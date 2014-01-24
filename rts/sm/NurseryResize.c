#include "PosixSource.h"
#include "Rts.h"
#include "HsFFI.h"

#include "Stats.h"

#include "Evac.h"
#include "GC.h"
#include "GCThread.h"
#include "GCTDecl.h"
#include "NurseryResize.h"
#include "Storage.h"

static int debug = 0;
static int graph = 0;

static W_ dynamicPN (Time last_time, W_ copied, double P, double I_, int times);
static W_ dynamicPNRateOld (Time last_time, W_ copied, double P, double I_, int times);
static W_ dynamicPNNew (Time last_time, W_ copied, double P, double I_, int times);
static W_ dynamicPNRate (Time last_time, W_ copied, double P, double I_, int times);
static W_ copiedRate (int pctn, W_ copied);
static W_ copiedRateNew (int pctn, W_ copied, double I);
//static W_ copiedRateFixed (Time last_time, double P, int times);
static W_ staticNursery(W_ blocks, W_ copied);

W_
dynamicResize (int algorithm)
{
    W_ blocks = 0;

    if (N == 1) {
        blocks = nursery_size;
    } else {
        W_ g0_words = genLiveWords(&generations[0])
                        - generations[0].n_large_words;
        W_ copied = g0_words + promoted_words;
        switch (algorithm) {
        case 1:
            blocks = dynamicPN(gct->gc_start_cpu, copied, 0.1, 1.25, 3);
            break;
        case 2:
            blocks = dynamicPN(gc_end_cpu, copied, 0.1, 1.25, 3);
            break;
        case 3:
            blocks = dynamicPNRateOld(gc_end_cpu, copied, 0.1, 1.25, 3);
            break;
        case 4:
            blocks = dynamicPNRate(gc_end_cpu, copied, 0.1, 1.25, 3);
            break;
        case 5:
            blocks = staticNursery(RtsFlags.GcFlags.minAllocAreaSize * n_capabilities, copied);
            break;
        //case 6:
        //    blocks = copiedRateNew(25, copied_, 0.5);
        //    break;
        case 7:
            blocks = copiedRate(25, copied);
            break;
        //case 8:
        //    blocks = copiedRate(25, g0_words);
        //    break;
        //case 9:
        //    blocks = copiedRate(25, copied_ - mut_list_size);
        //    break;
        //case 10:
        //    blocks = copiedRate(25, copied_);
        //    break;
        default:
            barf("Unknown nursery resize algorithm %d", algorithm);
        }
        if (graph > 0) {
            fprintf(stderr, "%" FMT_Word "\n", blocks * BLOCK_SIZE);
        }
    }

    nursery_size = blocks;
    if (debug > 0) {
        fprintf(stderr, "Nursery size: %.2fMiB\n", (double)blocks * BLOCK_SIZE / (1024 * 1024));
    }
    return blocks;
}

static double
reverseI(double I)
{
    if (I > 1) {
        if (I <= 1.1) return 1/1.1;
        I = 1 / (I * 0.9);
    } else {
        if (I >= 1/1.1) return 1.1;
        I = 1/I * 0.9;
    }
    return I;
}

static W_
dynamicPN (Time last_time, W_ copied, double P, double I_, int n0_tot_times)
{
    static nat mode = 0;
      // 0 -> first adjust
      // 1 -> fast adjust
      // 2 -> fine-adjust middle-bottom
      // 3 -> fine-adjust top-middle

    static double last_time_rate = 0;
    static double last2_time_rate = 0;
    static double middle_time_rate = 0;
    static double bottom_time_rate = 0;
    static double top_time_rate = 0;

    static W_ last_nursery_size = 0;
    static W_ last2_nursery_size = 0;
    static W_ middle_nursery_size = 0;
    static W_ bottom_nursery_size = 0;
    static W_ top_nursery_size = 0;
    
    double time_rate, rate;
    Time now;

    now = getProcessCPUTime();
    time_rate = (double)(now - last_time) / nursery_alloc;

    if (graph > 0) {
        fprintf(stderr, "%f ", time_rate);
    }

    rate = (double)nursery_alloc / copied;

    static int n0_times = 0;
    static double tot_rate = 0, tot_time_rate = 0;

    n0_times++;
    tot_rate += rate;
    tot_time_rate += time_rate;

    if (n0_times < n0_tot_times) {
        return nursery_size;
    }

    rate = tot_rate / n0_times;
    time_rate = tot_time_rate / n0_times;
    n0_times = 0;
    tot_rate = tot_time_rate = 0;

    static double I = 2;
    switch (mode) {
    case 0:
        if (fabs(last_time_rate - time_rate) < P * last_time_rate) {
            I = I_;

            if (last_time_rate == 0) barf("last_time_rate");
            //if (nursery_size != last_nursery_size) {
              if (debug) {
                fprintf(stderr, "\tFound optimum = %6" FMT_Word " rate = %f\n",
                        nursery_size, rate);
              }
            //}
            break;
        }
        if (debug) {
            fprintf(stderr, "\tStart in %6" FMT_Word " rate = %f\n",
                    nursery_size, rate);
        }

        // init
        last_time_rate = time_rate;
        last_nursery_size = nursery_size;

        last2_time_rate = 0;

        nursery_size = lround((double)nursery_size * I);
        mode++;
        break;
    case 1:
        // adjust direction if wrong
        if (last2_time_rate == 0 && time_rate > last_time_rate) {
            I = 1/I;

            last2_time_rate = time_rate;
            last2_nursery_size = nursery_size;

            nursery_size = lround((double)last_nursery_size * I);
            //fprintf(stderr, " wrong, now %" FMT_Word "\n", nursery_size);
            break;
        }

        // increase/decrease nursery size if performance keeps increasing
        if (time_rate < last_time_rate) {
            last2_time_rate = last_time_rate;
            last2_nursery_size = last_nursery_size;

            last_time_rate = time_rate;
            last_nursery_size = nursery_size;

            nursery_size = lround((double)nursery_size * I);
        } else {
            ASSERT(last2_time_rate != 0);
            ASSERT(last_time_rate < time_rate); // delete, use <= in general

            top_time_rate = last2_time_rate;
            top_nursery_size = last2_nursery_size;

            middle_time_rate = last_time_rate;
            middle_nursery_size = last_nursery_size;

            bottom_time_rate = time_rate;
            bottom_nursery_size = nursery_size;

            // invert check => for same time can be very different
            // nursery size, not otherwise
            if (fabs(top_time_rate - bottom_time_rate) < P * top_time_rate) {
                // last_time_rate == middle_time_rate
                nursery_size = middle_nursery_size;
                if (debug) {
                    fprintf(stderr, "\tFound optimum = %6" FMT_Word " rate = %f\n",
                            nursery_size, rate);
                }
                I = I_;
                mode = 0;
                break;
            } else {
                ASSERT(fabs(top_nursery_size - bottom_nursery_size)
                         > P * top_nursery_size);
            }

            ASSERT(lround(((double)(middle_nursery_size + bottom_nursery_size) / 2) * 2) == middle_nursery_size + bottom_nursery_size);
            nursery_size = lround((double)(middle_nursery_size + bottom_nursery_size) / 2);
            //fprintf(stderr, "\tTry middle-bottom = %" FMT_Word "\n", nursery_size);
            mode++;
        }
        break;
    case 2:
        ASSERT(middle_time_rate < bottom_time_rate);
        ASSERT(middle_time_rate < top_time_rate);

        // adjust between middle and bottom (last two runs)
        // if last adjustment worked, continue using it as new middle
        if (time_rate < middle_time_rate) {
            top_time_rate = middle_time_rate;
            top_nursery_size = middle_nursery_size;

            middle_time_rate = time_rate;
            middle_nursery_size = nursery_size;

            if (fabs(top_time_rate - bottom_time_rate) < P * top_time_rate) {
                last_time_rate = middle_time_rate;
                nursery_size = last_nursery_size = middle_nursery_size;
                if (debug) {
                    fprintf(stderr, "\tFound optimum = %6" FMT_Word " rate = %f\n",
                            nursery_size, rate);
                }
                I = I_;
                mode = 0;
                break;
            } else {
                ASSERT(fabs(top_nursery_size - bottom_nursery_size)
                         > P * top_nursery_size);
            }

            ASSERT(lround(((double)(middle_nursery_size + bottom_nursery_size) / 2) * 2) == middle_nursery_size + bottom_nursery_size);
            nursery_size = lround((double)(middle_nursery_size + bottom_nursery_size) / 2);
        } else {
            ASSERT(time_rate < bottom_time_rate);

            last_time_rate = time_rate;
            last_nursery_size = nursery_size;

            ASSERT(lround(((double)(top_nursery_size + middle_nursery_size) / 2) * 2) == top_nursery_size + middle_nursery_size);
            nursery_size = lround((double)(top_nursery_size + middle_nursery_size) / 2);
            //fprintf(stderr, "\tTry top-middle= %" FMT_Word "\n", nursery_size);
            mode++;
        }
        break;
    case 3:
        ASSERT(middle_time_rate < bottom_time_rate); // delete
        ASSERT(middle_time_rate < top_time_rate); // delete

        // adjust between top and middle
        // if last adjustment worked, use it as new middle and come
        // back to 2
        if (time_rate < middle_time_rate) {
            bottom_time_rate = middle_time_rate;
            bottom_nursery_size = middle_nursery_size;

            middle_time_rate = time_rate;
            middle_nursery_size = nursery_size;

        // use x and y as new top and bottom
        } else {
            ASSERT(time_rate < top_time_rate);

            top_time_rate = time_rate;
            top_nursery_size = nursery_size;

            bottom_time_rate = last_time_rate;
            bottom_nursery_size = last_nursery_size;
        }

        if (fabs(top_time_rate - bottom_time_rate) < P * top_time_rate) {
            //ASSERT(fabs(top_nursery_size - bottom_nursery_size)
            //         < P * top_nursery_size);
            last_time_rate = middle_time_rate;
            nursery_size = last_nursery_size = middle_nursery_size;
            if (debug) {
                fprintf(stderr, "\tFound optimum = %6" FMT_Word " rate = %f\n",
                        nursery_size, rate);
            }
            I = I_;
            mode = 0;
            break;
        } else {
            ASSERT(fabs(top_nursery_size - bottom_nursery_size)
                     > P * top_nursery_size);
        }

        ASSERT(lround(((double)(middle_nursery_size + bottom_nursery_size) / 2) * 2) == middle_nursery_size + bottom_nursery_size);
        nursery_size = lround((double)(middle_nursery_size + bottom_nursery_size) / 2);
        mode = 2;
        break;
    default:
        barf("nursery resize mode unknown: %d", mode);
    }

    return nursery_size;
}

static W_
dynamicPNRateOld (Time last_time, W_ copied, double P, double I_, int n0_tot_times)
{
    static nat mode = 0;
      // 0 -> first adjust
      // 1 -> fast adjust
      // 2 -> fine-adjust middle-bottom
      // 3 -> fine-adjust top-middle

    static double last_time_rate = 0;
    static double last2_time_rate = 0;
    static double middle_time_rate = 0;
    static double bottom_time_rate = 0;
    static double top_time_rate = 0;

    static double last_rate = 0;
    static double last2_rate = 0;
    static double middle_rate = 0;
    static double bottom_rate = 0;
    static double top_rate = 0;

    W_ blocks, blocks_copied;

    static double rate = 0;
    double time_rate, real_rate;
    Time now;

    blocks_copied = lround((double)copied / BLOCK_SIZE_W);

    now = getProcessCPUTime();
    time_rate = (double)(now - last_time) / nursery_alloc;

    time_rate = (double)(now - last_time) / nursery_alloc;
    real_rate = (double)nursery_alloc / copied;

    if (rate == 0) {
        rate = (double)100 / 35;
    }

    static int n0_times = 0;
    static double tot_rate = 0, tot_time_rate = 0;

    n0_times++;
    tot_rate += real_rate;
    tot_time_rate += time_rate;

    if (n0_times < n0_tot_times) {
        blocks = lround(blocks_copied * rate);
        return blocks;
    }

    real_rate = tot_rate / n0_times;
    time_rate = tot_time_rate / n0_times;

    n0_times = 0;
    tot_rate = 0;
    tot_time_rate = 0;

    static double I = 2;
    switch (mode) {
    case 0:
        if (fabs(last_time_rate - time_rate) < P * last_time_rate) {
            I = I_;

            if (last_time_rate == 0) barf("last_time_rate");
            rate = last_rate;

            //if (nursery_size != last_nursery_size) {
              if (debug) {
                fprintf(stderr, "\tFound optimum = %6" FMT_Word " rate = %f\n",
                        nursery_size, rate);
              }
            //}
            break;
        }
        if (debug) {
            fprintf(stderr, "\tStart in %6" FMT_Word " rate = %f\n",
                    nursery_size, rate);
        }

        // init
        last_time_rate = time_rate;
        last_rate = rate;

        last2_time_rate = 0;
        //if ((int)I != 2 && I != I_) {
        //    fprintf(stderr, "I = %f\nI_ = %f\n", I, I_);
        //    barf("I");
        //}
        rate *= I;
        mode = 1;
        break;
    case 1:
        // adjust direction if wrong
        if (last2_time_rate == 0 && time_rate > last_time_rate) {
            I = 1/I;

            last2_time_rate = time_rate;
            last2_rate = rate;

            rate = last_rate * I;
            break;
        }

        // increase/decrease nursery size if performance keeps increasing
        if (time_rate < last_time_rate) {
            last2_time_rate = last_time_rate;
            last2_rate = last_rate;

            last_time_rate = time_rate;
            last_rate = rate;

            rate *= I;
        } else {
            ASSERT(last2_time_rate != 0);
            ASSERT(last_time_rate < time_rate); // delete, use <= in general

            top_time_rate = last2_time_rate;
            top_rate = last2_rate;

            middle_time_rate = last_time_rate;
            middle_rate = last_rate;

            bottom_time_rate = time_rate;
            bottom_rate = rate;

            // invert check => for same time can be very different
            // nursery size, not otherwise
            if (fabs(top_time_rate - bottom_time_rate) < P * top_time_rate) {
                // last_time_rate == middle_time_rate
                rate = middle_rate;
                if (debug) {
                    fprintf(stderr, "\tFound optimum = %6" FMT_Word " rate = %f\n",
                            nursery_size, rate);
                }
                I = I_;
                mode = 0;
                break;
            }

            rate = lround((double)(middle_rate + bottom_rate) / 2);
            //fprintf(stderr, "\tTry middle-bottom = %" FMT_Word "\n", nursery_size);
            mode++;
        }
        break;
    case 2:
        ASSERT(middle_time_rate < bottom_time_rate);
        ASSERT(middle_time_rate < top_time_rate);

        // adjust between middle and bottom (last two runs)
        // if last adjustment worked, continue using it as new middle
        if (time_rate < middle_time_rate) {
            top_time_rate = middle_time_rate;
            top_rate = middle_rate;

            middle_time_rate = time_rate;
            middle_rate = rate;

            if (fabs(top_time_rate - bottom_time_rate) < P * top_time_rate) {
                last_time_rate = middle_time_rate;
                rate = last_rate = middle_rate;
                if (debug) {
                    fprintf(stderr, "\tFound optimum = %6" FMT_Word " rate = %f\n",
                            nursery_size, rate);
                }
                I = I_;
                mode = 0;
                break;
            }

            rate = lround((double)(middle_rate + bottom_rate) / 2);
        } else {
            ASSERT(time_rate < bottom_time_rate);

            last_time_rate = time_rate;
            last_rate = rate;

            rate = lround((double)(top_rate + middle_rate) / 2);
            //fprintf(stderr, "\tTry top-middle= %" FMT_Word "\n", nursery_size);
            mode++;
        }
        break;
    case 3:
        ASSERT(middle_time_rate < bottom_time_rate); // delete
        ASSERT(middle_time_rate < top_time_rate); // delete

        // adjust between top and middle
        // if last adjustment worked, use it as new middle and come
        // back to 2
        if (time_rate < middle_time_rate) {
            bottom_time_rate = middle_time_rate;
            bottom_rate = middle_rate;

            middle_time_rate = time_rate;
            middle_rate = rate;

        // use x and y as new top and bottom
        } else {
            ASSERT(time_rate < top_time_rate);

            top_time_rate = time_rate;
            top_rate = rate;

            bottom_time_rate = last_time_rate;
            bottom_rate = last_rate;
        }

        if (fabs(top_time_rate - bottom_time_rate) < P * top_time_rate) {
            last_time_rate = middle_time_rate;
            rate = last_rate = middle_rate;
            if (debug) {
                fprintf(stderr, "\tFound optimum = %6" FMT_Word " rate = %f\n",
                        nursery_size, rate);
            }
            I = I_;
            mode = 0;
            break;
        }

        rate = lround((double)(middle_rate + bottom_rate) / 2);
        mode = 2;
        break;
    default:
        barf("nursery resize mode unknown: %d", mode);
    }

    blocks = lround(blocks_copied * last_rate);
    return blocks;
}

static W_
dynamicPNNew (Time last_time, W_ copied, double P, double I_, int n0_tot_times)
{
    static nat mode = 0;

    static double last_time_rate = 0;

    static rtsBool rightDir = rtsFalse;

    static W_ last_nursery_size = 0;
    
    W_ blocks;
    double time_rate, rate;
    Time now;

    now = getProcessCPUTime();
    time_rate = (double)(now - last_time) / nursery_alloc;

    rate = (double)nursery_alloc / copied;

    static int n0_times = 0;
    static double tot_rate = 0, tot_time_rate = 0;

    n0_times++;
    tot_rate += rate;
    tot_time_rate += time_rate;

    if (n0_times < n0_tot_times) {
        return nursery_size;
    }

    rate = tot_rate / n0_times;
    time_rate = tot_time_rate / n0_times;
    n0_times = 0;
    tot_rate = tot_time_rate = 0;

    static double I = 2;

    switch (mode) {
    case 0:
        if (fabs(last_time_rate - time_rate) < P * last_time_rate) {
            ASSERT(last_time_rate != 0);
            //ASSERT(fabs(last_nursery_size - nursery_size)
            //         < P * last_nursery_size);
            //if (last_time_rate < time_rate) {
            //    nursery_size = last_nursery_size;
            //} else {
            //    //last_time_rate = time_rate;
            //}
            I = I_;

            //if (nursery_size != last_nursery_size) {
              if (debug) {
                fprintf(stderr, "\tFound optimum = %6" FMT_Word " rate = %f\n",
                        nursery_size, rate);
              }
            //}
            blocks = nursery_size;
            break;
        }

        ASSERT(fabs(last_nursery_size - nursery_size) > P * last_nursery_size);

        if (debug) {
            fprintf(stderr, "\tStart in %6" FMT_Word " rate = %f\n",
                    nursery_size, rate);
        }

        // init
        last_time_rate = time_rate;
        last_nursery_size = nursery_size;

        rightDir = rtsFalse;

        blocks = lround((double)nursery_size * I);
        mode = 1;
        break;
    case 1:
        if (fabs(last_time_rate - time_rate) < P * last_time_rate) {
            //ASSERT(fabs(last_nursery_size - nursery_size)
            //         < P * last_nursery_size);
            //if (last_time_rate < time_rate) {
            //    nursery_size = last_nursery_size;
            //} else {
            //    //last_time_rate = time_rate;
            //}
            I = I_;

            //if (nursery_size != last_nursery_size) {
              if (debug) {
                fprintf(stderr, "\tFound optimum = %6" FMT_Word " rate = %f\n",
                        nursery_size, rate);
              }
            //}
            blocks = nursery_size;
            mode = 0;
            break;
        }

        // first time, just adjust direction if wrong
        if (rightDir == rtsFalse && time_rate > last_time_rate) {
            I = 1/I;

            rightDir = rtsTrue;

            blocks = lround((double)last_nursery_size * I);
            //fprintf(stderr, " wrong, now %" FMT_Word "\n", nursery_size);
            break;
        }

        rightDir = rtsTrue;

        last_time_rate = time_rate;
        last_nursery_size = nursery_size;

        // increase/decrease nursery size if performance keeps increasing
        if (time_rate > last_time_rate) {
            I = reverseI(I);
        }
        blocks = lround((double)nursery_size * I);
        break;
    default:
        barf("Unknown dynamicPNNew mode");
    }

    return blocks;
}

// TODO
// In case min_nursery is used:
//  1. do not update rate?
//  2. use real rate and start over?
static W_
dynamicPNRate (Time last_time, W_ copied, double P, double I_, int n0_tot_times)
{
    static nat mode = 0;
      // 0 init
      // 1 first adjustment if direction is wrong
      // 2 normal operation

    static double rate = 0;
    static double last_rate = 0;
    static double last_time_rate = 0;
    static int dir = 0;
      // -1 left
      // 0  no direction
      // 1  right

    double time_rate, real_rate;

    W_ blocks, blocks_copied;
    Time now;

    blocks_copied = lround((double)copied / BLOCK_SIZE_W);

    now = getProcessCPUTime();

    time_rate = (double)(now - last_time) / nursery_alloc;
    real_rate = (double)nursery_alloc / copied;

    if (graph > 0) {
        fprintf(stderr, "%f %f ", time_rate, real_rate);
    }


    if (rate == 0) {
        rate = (double)100 / 35;
    }

    static int n0_times = 0;
    static double tot_rate = 0;
    static double tot_time_rate = 0;

    n0_times++;
    tot_rate += real_rate;
    tot_time_rate += time_rate;

    if (n0_times < n0_tot_times) {
        blocks = lround(blocks_copied * rate);
        return blocks;
    }

    real_rate = tot_rate / n0_times;
    time_rate = tot_time_rate / n0_times;

    n0_times = 0;
    tot_rate = 0;
    tot_time_rate = 0;

    static double I = 2;
    switch (mode) {
    case 0:
        if (fabs(last_time_rate - time_rate) < P * last_time_rate) {
            ASSERT(last_time_rate != 0);
            //if (last_time_rate < time_rate) {
            //    nursery_size = last_nursery_size;
            //} else {
            //    //last_time_rate = time_rate;
            //}
            I = I_;
            if (last_rate == 0) barf("last_rate");
            rate = last_rate;

            blocks = lround(blocks_copied * last_rate);
            if (debug) {
                fprintf(stderr, "[0] Found optimum = %.2fMiB rate = %f time_rate = %f\n",
                        (double)blocks * BLOCK_SIZE / (1024 * 1024), rate, time_rate);
            }
            break;
        }

        if (debug) {
            fprintf(stderr, "Start with nursery = %.2fMiB rate = %f time_rate = %f\n",
                    (double)nursery_size * BLOCK_SIZE / (1024 * 1024), rate, time_rate);
        }

        // init
        last_time_rate = time_rate;
        last_rate = rate;

        dir = 1;
        //if ((int)I != 2 && I != I_) {
        //    fprintf(stderr, "I = %f\nI_ = %f\n", I, I_);
        //    barf("I");
        //}
        rate *= I;

        blocks = lround(blocks_copied * rate);
        mode = 1;

        if (debug) {
            fprintf(stderr, "\tTry nursery = %.2fMiB rate = %f\n",
                    (double)blocks * BLOCK_SIZE / (1024 * 1024), rate);
        }

        break;
    case 1:
    case 2:
        if (fabs(last_time_rate - time_rate) < P * last_time_rate) {
            //if (last_time_rate < time_rate) {
            //    nursery_size = last_nursery_size;
            //} else {
            //    //last_time_rate = time_rate;
            //}
            dir = 0 - dir; // TODO: check if this is worthy
            //I = I_; 
            if (pow(I_, -1) != 1 / I_) barf("pow");
            I = pow(I_, dir);

            rate = last_rate;

            blocks = lround(blocks_copied * last_rate);
            mode = 0;

            if (debug) {
                fprintf(stderr, "[1/2] Found optimum = %.2fMiB rate = %f time_rate = %f\n",
                        (double)blocks * BLOCK_SIZE / (1024 * 1024), rate, time_rate);
            }
            break;
        }

        if (dir == 0) barf("dir");

        // first time, just adjust direction if wrong
        if (mode == 1) {
            mode = 2;
            if (time_rate > last_time_rate) {
                I = 1/I;
                rate = last_rate * I;

                blocks = lround(blocks_copied * rate);

                if (debug) {
                    fprintf(stderr, "Wrong dir (%.2f > %.2f)\n", time_rate, last_time_rate);
                    fprintf(stderr, "Now nursery = %.2fMiB rate = %f time_rate = %f\n",
                            (double)blocks * BLOCK_SIZE / (1024 * 1024), rate, time_rate);
                }
                break;
            }
        }

        // increase/decrease nursery size if performance keeps increasing
        if (time_rate > last_time_rate) {
            double I0 = I;
            I = reverseI(I);
            if (debug) {
                fprintf(stderr, "Reverse dir, (%f => %f)\n", I0, I);
            }
        }
        rate *= I;

        blocks = lround(blocks_copied * rate);
        //fprintf(stderr, "blocks = %ld\n", blocks);
        //fprintf(stderr, "blocks_copied = %ld\n", blocks_copied);
        //fprintf(stderr, "rate = %f\n", rate);

        last_time_rate = time_rate;
        last_rate = rate;

        if (debug) {
            fprintf(stderr, "Continue dir, now = %.2fMiB rate = %f time_rate = %f\n",
                    (double)blocks * BLOCK_SIZE / (1024 * 1024), rate, time_rate);
        }
        break;
    default:
        barf("Unknown dynamicPNRate mode");
    }

    if (rate >= 1 && (W_)lround(blocks / rate) != blocks_copied) {
        barf("blocks_copied = %ld\nblocks = %ld\nrate = %f\n", blocks_copied, blocks, rate);
    }
    return blocks;
}

static W_
staticNursery(W_ blocks, W_ copied)
{
    double time_rate, real_rate;

    Time now;

    now = getProcessCPUTime();

    time_rate = (double)(now - gc_end_cpu) / nursery_alloc;
    real_rate = (double)nursery_alloc / copied;

    if (graph > 0) {
        fprintf(stderr, "%f %f ", time_rate, real_rate);
    }

    return blocks;
}

W_
copiedRate (int pcnt, W_ copied)
{
    //static double initial_nursery_resize_rate = 0.5;
    //double STG_UNUSED nursery_resize_rate = 0.5;
    //double STG_UNUSED nursery_rate_growth = 0;
    //int nursery_rate_sign = 0;
    
    W_ blocks, blocks_copied;

    //blocks = countNurseryBlocks();

    blocks_copied = lround((double)copied / BLOCK_SIZE_W);
    blocks = lround((double)blocks_copied * 100 / pcnt);
    //blocks += (ideal-blocks) * nursery_resize_rate;
    if (debug) {
        double rate = (double)nursery_alloc / copied;
        fprintf(stderr, "\tUsing = %6" FMT_Word " rate = %f\n",
                blocks, rate);
    }

    //// modify nursery_resize_rate
    //if (nursery_resize_rate < 1) {
    //    if (hf_sign(ideal-blocks) == nursery_rate_sign) {
    //        nursery_resize_rate += nursery_resize_rate * nursery_rate_growth;
    //    } else {
    //        nursery_rate_sign = hf_sign(ideal-blocks);
    //        nursery_resize_rate = initial_nursery_resize_rate;
    //    }
    //    if (nursery_resize_rate > 1) {
    //        nursery_resize_rate = 1;
    //    }
    //}
    // FIXME: blocks / n_capabilities

    return blocks;
}

W_
copiedRateNew (int pcnt, W_ copied, double I)
{
    //static double initial_nursery_resize_rate = 0.5;
    //double STG_UNUSED nursery_resize_rate = 0.5;
    //double STG_UNUSED nursery_rate_growth = 0;
    //int nursery_rate_sign = 0;
    
    W_ blocks, blocks_copied;
    double target;

    blocks = countNurseryBlocks();

    blocks_copied = (double)copied / BLOCK_SIZE_W;
    target = (double)blocks_copied * 100 / pcnt;
    blocks += (target-blocks) * I;
    if (debug) {
        double rate = (double)nursery_alloc / copied;
        fprintf(stderr, "\tUsing = %6" FMT_Word " rate = %f\n",
                blocks, rate);
    }

    //// modify nursery_resize_rate
    //if (nursery_resize_rate < 1) {
    //    if (hf_sign(ideal-blocks) == nursery_rate_sign) {
    //        nursery_resize_rate += nursery_resize_rate * nursery_rate_growth;
    //    } else {
    //        nursery_rate_sign = hf_sign(ideal-blocks);
    //        nursery_resize_rate = initial_nursery_resize_rate;
    //    }
    //    if (nursery_resize_rate > 1) {
    //        nursery_resize_rate = 1;
    //    }
    //}
    // FIXME: blocks / n_capabilities

    return blocks;
}

//W_ copiedRateFixed (Time last_time, double P, int n0_tot_times)
//{
//    W_ blocks, g0_words;
//    double blocks_copied, last_time_rate, time_rate = 0, current_time_rate;
//    Time now;
//    static int n0_times = 0;
//    static double tot_time_rate = 0;
//    int rates[] = { 10, 15, 20, 25 };
//    static int last_rate, rate = 10;
//
//    now = getProcessCPUTime();
//    current_time_rate = (double)(now - last_time) / nursery_alloc;
//
//    n0_times++;
//    tot_time_rate += current_time_rate;
//
//    if (n0_times >= n0_tot_times) {
//        last_time_rate = time_rate;
//        time_rate = tot_time_rate / n0_times;
//        n0_times = 0;
//        tot_time_rate = 0;
//
//        if (fabs(last_time_rate - time_rate) < P * last_time_rate) {
//        }
//    }
//
//    g0_words = genLiveWords(&generations[0])
//                 - generations[0].n_large_words;
//
//    blocks_copied = lround((double)(g0_words + promoted_words) / BLOCK_SIZE_W);
//    blocks = lround(blocks_copied * 100 / rate);
//
//    if (debug) {
//        double rate = (double)nursery_alloc
//                        / (double)(g0_words + promoted_words);
//        fprintf(stderr, "\tUsing = %6" FMT_Word " rate = %f\n",
//                blocks, rate);
//    }
//
//    return blocks;
//}

void
checkGcInvariants (void)
{
    ASSERT(nursery_size != 0);
    ASSERT(nursery_alloc <= nursery_size * BLOCK_SIZE_W);
    //if (nursery_alloc < 0.95 * nursery_size * BLOCK_SIZE_W) {
    //    barf("\nCollection %d [%d]\nnursery_alloc = %" FMT_Word
    //         "\nnursery_size = %" FMT_Word,
    //         generations[0].collections + generations[1].collections, N,
    //         nursery_alloc, nursery_size * BLOCK_SIZE_W);
    //}

#ifdef DEBUG
    W_ g0_words, g1_words;
    static W_ g0_old_words = 0, g1_old_words = 0;

    g0_words = genLiveWords(&generations[0]) - generations[0].n_large_words;
    ASSERT(g0_words + promoted_words <= nursery_alloc);

    g1_words = genLiveWords(&generations[1]) - generations[1].n_large_words;

    ASSERT(countOccupied(gc_threads[0]->gens[0].scavd_list) == 0);
    ASSERT(countOccupied(gc_threads[0]->gens[1].scavd_list) == 0);
    if (N == 0) {
        ASSERT(promoted_words <= g1_words - g1_old_words);
        ASSERT(g1_words - g1_old_words <= g0_old_words); // + promoted_words);
        ASSERT(copied - mut_list_size
                 == g0_words + (g1_words - g1_old_words));
    } else {
        ASSERT(copied - mut_list_size == calcLiveWords()
                 - (generations[0].n_large_words +
                    generations[1].n_large_words));
    }

    g0_old_words = g0_words;
    g1_old_words = g1_words;

    promoted_objects = 0;
    promoted_words = 0;
#endif
}


