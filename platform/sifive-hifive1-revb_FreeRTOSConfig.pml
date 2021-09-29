#ifndef _FreeRTOS_CONFIG_
#define _FreeRTOS_CONFIG_

/** Default configurations: modification has no effects in the model **
configUSE_16_BIT_TICKS                      0
tskSTATIC_AND_DYNAMIC_ALLOCATION_POSSIBLE
configSUPPORT_DYNAMIC_ALLOCATION            1
configSUPPORT_STATIC_ALLOCATION             0
configUSE_TRACE_FACILITY                    0
configUSE_APPLICATION_TASK_TAG              0
configGENERATE_RUN_TIME_STATS               0
configUSE_TRACE_FACILITY                    0
configUSE_IDLE_HOOK                         0
configUSE_TIMERS                            0
INCLUDE_xTaskGetSchedulerState              0
configINCLUDE_FREERTOS_TASK_C_ADDITIONS_H   0
configUSE_TICKLESS_IDLE                     0
configUSE_POSIX_ERRNO                       0
configUSE_NEWLIB_REENTRANT                  0
configUSE_CO_ROUTINES                       0
configUSE_LIST_DATA_INTEGRITY_CHECK_BYTES   0
INCLUDE_xTaskAbortDelay                     0
configUSE_TASK_NOTIFICATIONS                0
INCLUDE_VTaskDelete                         0
**********************************************************************/

#define configTickType_t                    byte
#define configINITIAL_TICK_COUNT            0

// TODO: CLINT_CTRL_ADDR
// TODO: configUSE_PORT_OPTIMISED_TASK_SELECTION

#define configUSE_PREEMPTION                1
#define configUSE_TIME_SLICING              1
#define configIDLE_SHOULD_YIELD             0
#define configUSE_PORT_OPTIMISED_TASK_SELECTION 1
#ifndef configMAX_PRIORITIES
    #define configMAX_PRIORITIES            3
#endif
#ifndef configUSE_TICK_HOOK
    #define configUSE_TICK_HOOK             0
#endif
#define configUSE_MUTEXES                   1
#define configUSE_RECURSIVE_MUTEXES         1
#define configUSE_QUEUE_SETS                0 // TODO
#define configUSE_COUNTING_SEMAPHORES       1

#ifndef INCLUDE_vTaskSuspend
    #define INCLUDE_vTaskSuspend            1
#endif
#define INCLUDE_vTaskDelay                  1
#define INCLUDE_uxTaskPriorityGet           1
#define INCLUDE_vTaskPrioritySet            1

/* Configurations Limitations */

#if (promela_EXP_NUMBER > 7)
#error Increase the size of exp_inactive_yet in the file of v7m ghost variables.
#endif

#if (configMAX_PRIORITIES > 10)
#error Increase the size of the Container in the ListItem_t.
#endif

#if (configMAX_PRIORITIES >= 8)
#error Increase the size of the Value in the ListItem_t.
#endif

#endif
