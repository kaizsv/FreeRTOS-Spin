#!/bin/bash

export FreeRTOSConfig_PLAN=" \
    -DconfigUSE_PREEMPTION=1 \
    -DconfigUSE_TIME_SLICING=1 \
    "
