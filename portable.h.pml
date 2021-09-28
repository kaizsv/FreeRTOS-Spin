#ifndef PORTABLE_H
#define PORTABLE_H

#if !defined(ARMV7M)

    #warning Please specify an architecture.
    #define ARMV7M

#endif

#if defined(ARMV7M)

    #include "platform/stm32p103_FreeRTOSConfig.pml"
    #include "FreeRTOS/portable/GCC_ARM_CM3/port.pml"

#endif

#endif
