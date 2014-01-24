#ifndef SM_NURSERY_RESIZE_H
#define SM_NURSERY_RESIZE_H

#include "BeginPrivate.h"

void checkGcInvariants (void);

W_ dynamicResize (int algorithm);

#include "EndPrivate.h"

#endif /* SM_NURSERY_RESIZE_H */
