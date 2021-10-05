#!/bin/bash

export FreeRTOSConfig_PLAN=" \
    -DconfigUSE_PREEMPTION=0 \
    -DconfigUSE_TIME_SLICING=1 \
    "
