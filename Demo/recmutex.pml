/* FreeRTOS/Demo/Common/Minimal/recmutex.c */

#define promela_TASK_NUMBER     3
#define promela_QUEUE_NUMBER    1

#define FIRST_TASK              promela_EXP_NUMBER
#define IDLE_TASK_ID            (FIRST_TASK + promela_TASK_NUMBER)

#define RUN_ALL_TASKS(stmts) \
    atomic {                \
        stmts;              \
        run Rec1();         \
        run Rec2();         \
        run Rec3();         \
    }

#ifdef CORRECTION
    #define CLEAR_configIDLE_SHOULD_YIELD_IF_USE_PREEMPTION_AND_TIME_SLICING
#endif

#include "../FreeRTOS.pml"
#include "../FreeRTOS/tasks.pml"
#include "../FreeRTOS/semphr.h.pml"

#ifdef LTL
    #include "property/recmutex.ltl"
#endif

#ifndef recmuCONTROLLING_TASK_PRIORITY
    #define recmuCONTROLLING_TASK_PRIORITY  (tskIDLE_PRIORITY + 2)
#endif
#define recmuBLOCKING_TASK_PRIORITY (tskIDLE_PRIORITY + 1)
#define recmuPOLLING_TASK_PRIORITY  (tskIDLE_PRIORITY + 0)

#define recmuMAX_COUNT      2 /* Origin is 10 */

#define recmuSHORT_DELAY    20
#define recmuNO_DELAY       0
#define recmu15ms_DELAY     15

SemaphoreDeclarator(1, byte);
SemaphoreHandle_t(xMutex, 1, byte);

#define INC_AND_WRAP_AROUND(val)    ((val + 1) % 8)

byte uxControllingCycles = 0, uxBlockingCycles = 0;

bool xControllingIsSuspended = false, xBlockingIsSuspended = false;

#define xControllingTaskHandle  (FIRST_TASK + 0)
#define xBlockingTaskHandle     (FIRST_TASK + 1)

proctype Rec1()
{
    byte ux = 0;
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bool local_bit = false, local_xReturn = false;
    assert(_PID == xControllingTaskHandle);
do
::  xSemaphoreGiveRecursive(_PID, xMutex, local_xReturn, local_var1, local_var2);
    /* Should not be able to 'give' the mutex, as we have not yet 'taken' it */
    AWAIT(_PID, assert(local_xReturn == false));

    do
    :: SELE(_PID, ux < recmuMAX_COUNT, ux = ux + 1);
        xSemaphoreTakeRecursive(_PID, xMutex, recmu15ms_DELAY, local_xReturn, local_bit, local_var1, local_var2);
        AWAIT(_PID, assert(local_xReturn == true); local_xReturn = false);
        vTaskDelay(_PID, recmuSHORT_DELAY, local_var1, local_var2);
    :: ELSE(_PID, ux < recmuMAX_COUNT, ux = 0); atomic { (_PID == EP); break }
    od;

    do
    :: SELE(_PID, ux < recmuMAX_COUNT, ux = ux + 1);
        vTaskDelay(_PID, recmuSHORT_DELAY, local_var1, local_var2);
        xSemaphoreGiveRecursive(_PID, xMutex, local_xReturn, local_var1, local_var2);
        AWAIT(_PID, assert(local_xReturn == true); local_xReturn = false);

        #if (configUSE_PREEMPTION == 0)
        taskYIELD(_PID);
        #endif
    :: ELSE(_PID, ux < recmuMAX_COUNT, ux = 0); atomic { (_PID == EP); break }
    od;

    xSemaphoreGiveRecursive(_PID, xMutex, local_xReturn, local_var1, local_var2);
    AWAIT(_PID, assert(local_xReturn == false));

running:
    AWAIT(_PID, uxControllingCycles = INC_AND_WRAP_AROUND(uxControllingCycles));

    AWAIT(_PID, xControllingIsSuspended = true);
    vTaskSuspend(_PID, NULL_byte, local_var1);
    AWAIT(_PID, xControllingIsSuspended = false);
od
}

proctype Rec2()
{
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bool local_bit = false, local_xReturn = false;
    assert(_PID == xBlockingTaskHandle);
do
::  xSemaphoreTakeRecursive(_PID, xMutex, 254, local_xReturn, local_bit, local_var1, local_var2);
    AWAIT(_PID, assert(local_xReturn == true); local_xReturn = false);
        AWAIT(_PID, assert(xControllingIsSuspended == true));
            xSemaphoreGiveRecursive(_PID, xMutex, local_xReturn, local_var1, local_var2);
            AWAIT(_PID, assert(local_xReturn == true); local_xReturn = false);

            AWAIT(_PID, xBlockingIsSuspended = true);
            vTaskSuspend(_PID, NULL_byte, local_var1);
            AWAIT(_PID, xBlockingIsSuspended = false);

    AWAIT(_PID, assert(uxControllingCycles == INC_AND_WRAP_AROUND(uxBlockingCycles)));
running:
    AWAIT(_PID, uxBlockingCycles = INC_AND_WRAP_AROUND(uxBlockingCycles));
od
}

proctype Rec3()
{
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bool local_bit = false, local_xReturn = false;
    assert(_PID == FIRST_TASK + 2);
do
::  xSemaphoreTakeRecursive(_PID, xMutex, recmuNO_DELAY, local_xReturn, local_bit, local_var1, local_var2);
    if
    :: SELE(_PID, local_xReturn == true, local_xReturn = false);
        AWAIT(_PID, assert(xBlockingIsSuspended && xControllingIsSuspended));

running:
        vTaskResume(_PID, xBlockingTaskHandle, local_var1);
        #if (configUSE_PREEMPTION == 0)
        taskYIELD(_PID);
        #endif

        vTaskResume(_PID, xControllingTaskHandle, local_var1);
        #if (configUSE_PREEMPTION == 0)
        taskYIELD(_PID);
        #endif

        AWAIT(_PID, assert(!xBlockingIsSuspended && !xControllingIsSuspended));

        #if (INCLUDE_uxTaskPriorityGet == 1)
        AWAIT(_PID, assert(uxTaskPriorityGet(NULL_byte) == recmuCONTROLLING_TASK_PRIORITY));
        #endif

        xSemaphoreGiveRecursive(_PID, xMutex, local_xReturn, local_var1, local_var2);
        AWAIT(_PID, assert(local_xReturn == true); local_xReturn = false);

        #if (INCLUDE_uxTaskPriorityGet == 1)
        AWAIT(_PID, assert(uxTaskPriorityGet(NULL_byte) == recmuPOLLING_TASK_PRIORITY));
        #endif
    :: ELSE(_PID, local_xReturn == true)
    fi;

    #if (configUSE_PREEMPTION == 0)
    taskYIELD(_PID);
    #endif
od
}

init
{
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;

    xSemaphoreCreateRecursiveMutex(xMutex, 0, local_var1, local_var2, EP);
    skip;

    d_step {
        prvInitialiseTaskLists();

        xTaskCreate_fixed(xControllingTaskHandle, recmuCONTROLLING_TASK_PRIORITY);
        xTaskCreate_fixed(xBlockingTaskHandle, recmuBLOCKING_TASK_PRIORITY);
        xTaskCreate_fixed(FIRST_TASK + 2, recmuPOLLING_TASK_PRIORITY);
    };

    vTaskStartScheduler(EP);

    /* Start the IDLE TASK */
    vTaskIDLE_TASK_BODY(IDLE_TASK_ID)
}
