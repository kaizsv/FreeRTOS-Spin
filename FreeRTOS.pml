/* include the platform and the porting files */

#include "PROMELA.pml"
#include "portable.h.pml"

#ifndef _INC_FREERTOS_H_
#define _INC_FREERTOS_H_

#ifndef portPRIVILEGE_BIT
    #define portPRIVILEGE_BIT 0
#endif

#ifndef portYIELD_WITHIN_API
    #define portYIELD_WITHIN_API portYIELD
#endif

#endif
