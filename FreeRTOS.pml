/* include the platform and the porting files */

#include "platform/stm32p103_FreeRTOSConfig.pml"
#include "FreeRTOS/portable/GCC_ARM_CM3/port.pml"
#include "FreeRTOS/portable/GCC_ARM_CM3/portmacro.pml"

#ifndef _INC_FREERTOS_H_
#define _INC_FREERTOS_H_

#ifndef portPRIVILEGE_BIT
    #define portPRIVILEGE_BIT 0
#endif

#ifndef portYIELD_WITHIN_API
    #define portYIELD_WITHIN_API portYIELD
#endif

#endif
