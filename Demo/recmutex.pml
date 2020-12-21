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

#include "../FreeRTOS.pml"
#include "../FreeRTOS/tasks.pml"
#include "../FreeRTOS/semphr.h.pml"

#ifdef LTL
    #include "../property/recmutex.ltl"
#endif

#ifndef recmuCONTROLLING_TASK_PRIORITY
    #define recmuCONTROLLING_TASK_PRIORITY  (tskIDLE_PRIORITY + 2)
#endif
#define recmuBLOCKING_TASK_PRIORITY (tskIDLE_PRIORITY + 1)
#define recmuPOLLING_TASK_PRIORITY  (tskIDLE_PRIORITY + 0)

#define recmuMAX_COUNT      10

#define recmuSHORT_DELAY    20
#define recmuNO_DELAY       0
#define recmu15ms_DELAY     15

QueueDeclarator(1, byte);
SemaphoreHandle_t(xMutex, 1, byte);

#define INC_AND_WRAP_AROUND(val)    ((val + 1) % 8)

byte uxControllingCycles = 0, uxBlockingCycles = 0;

bool xControllingIsSuspended = false, xBlockingIsSuspended = false;

#define xControllingTaskHandle  (FIRST_TASK + 0)
#define xBlockingTaskHandle     (FIRST_TASK + 1)

proctype Rec1()
{
    byte idx, ux = 0;
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bool local_bit = false, local_xReturn = false, local_xIsTimeOut = false;
    assert(_PID == xControllingTaskHandle);
do
::  xSemaphoreGiveRecursive(_PID, xMutex, local_xReturn, local_xIsTimeOut, local_var1, local_var2);
    /* Should not be able to 'give' the mutex, as we have not yet 'taken' it */
    AWAIT(_PID, assert(local_xReturn == false));

    do
    :: SELE3(_PID, ux < recmuMAX_COUNT, ux = ux + 1);
        xSemaphoreTakeRecursive(_PID, xMutex, recmu15ms_DELAY, local_xReturn, local_bit, local_xIsTimeOut, local_var1, local_var2);
        AWAIT(_PID, assert(local_xReturn == true); local_xReturn = false);
        vTaskDelay(_PID, recmuSHORT_DELAY, local_bit, local_var1, local_var2);
    :: ELSE3(_PID, ux < recmuMAX_COUNT, ux = 0; break)
    od;

    do
    :: SELE3(_PID, ux < recmuMAX_COUNT, ux = ux + 1);
        vTaskDelay(_PID, recmuSHORT_DELAY, local_bit, local_var1, local_var2);
        xSemaphoreGiveRecursive(_PID, xMutex, local_xReturn, local_xIsTimeOut, local_var1, local_var2);
        AWAIT(_PID, assert(local_xReturn == true); local_xReturn = false);

        #if (configUSE_PREEMPTION == 0)
        taskYIELD(_PID, local_var1);
        #endif
    :: ELSE3(_PID, ux < recmuMAX_COUNT, ux = 0; break)
    od;

    xSemaphoreGiveRecursive(_PID, xMutex, local_xReturn, local_xIsTimeOut, local_var1, local_var2);
    AWAIT(_PID, assert(local_xReturn == false));

running:
    AWAIT(_PID, uxControllingCycles = INC_AND_WRAP_AROUND(uxControllingCycles));

    AWAIT(_PID, xControllingIsSuspended = true);
    vTaskSuspend(_PID, NULL_byte, local_var1, local_var2);
    AWAIT(_PID, xControllingIsSuspended = false);
od
}

proctype Rec2()
{
    byte idx;
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bool local_bit = false, local_xReturn = false, local_xIsTimeOut = false;
    assert(_PID == xBlockingTaskHandle);
do
::  xSemaphoreTakeRecursive(_PID, xMutex, 254, local_xReturn, local_bit, local_xIsTimeOut, local_var1, local_var2);
    AWAIT(_PID, assert(local_xReturn == true); local_xReturn = false);
        AWAIT(_PID, assert(xControllingIsSuspended == true));
            xSemaphoreGiveRecursive(_PID, xMutex, local_xReturn, local_xIsTimeOut, local_var1, local_var2);
            AWAIT(_PID, assert(local_xReturn == true); local_xReturn = false);

            AWAIT(_PID, xBlockingIsSuspended = true);
            vTaskSuspend(_PID, NULL_byte, local_var1, local_var2);
            AWAIT(_PID, xBlockingIsSuspended = false);

    AWAIT(_PID, assert(uxControllingCycles == INC_AND_WRAP_AROUND(uxBlockingCycles)));
running:
    AWAIT(_PID, uxBlockingCycles = INC_AND_WRAP_AROUND(uxBlockingCycles));
od
}

proctype Rec3()
{
    byte idx;
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bool local_bit = false, local_xReturn = false, local_xIsTimeOut = false;
    assert(_PID == FIRST_TASK + 2);
do
::  xSemaphoreTakeRecursive(_PID, xMutex, recmuNO_DELAY, local_xReturn, local_bit, local_xIsTimeOut, local_var1, local_var2);
    if
    :: SELE3(_PID, local_xReturn == true, local_xReturn = false);
        AWAIT(_PID, assert(xBlockingIsSuspended && xControllingIsSuspended));

running:
        vTaskResume(_PID, xBlockingTaskHandle, local_bit, local_var1);
        #if (configUSE_PREEMPTION == 0)
        taskYIELD(_PID, local_var1);
        #endif

        vTaskResume(_PID, xControllingTaskHandle, local_bit, local_var1);
        #if (configUSE_PREEMPTION == 0)
        taskYIELD(_PID, local_var1);
        #endif

        AWAIT(_PID, assert(!xBlockingIsSuspended && !xControllingIsSuspended));

        #if (INCLUDE_uxTaskPriorityGet == 1)
        AWAIT(_PID, assert(uxTaskPriorityGet(NULL_byte) == recmuCONTROLLING_TASK_PRIORITY));
        #endif

        xSemaphoreGiveRecursive(_PID, xMutex, local_xReturn, local_xIsTimeOut, local_var1, local_var2);
        AWAIT(_PID, assert(local_xReturn == true); local_xReturn = false);

        #if (INCLUDE_uxTaskPriorityGet == 1)
        AWAIT(_PID, assert(uxTaskPriorityGet(NULL_byte) == recmuPOLLING_TASK_PRIORITY));
        #endif
    :: ELSE2(_PID, local_xReturn == true)
    fi;

    #if (configUSE_PREEMPTION == 0)
    taskYIELD(_PID, local_var1);
    #endif
od
}

init
{
    byte idx;
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bool local_xIsTimeOut = false;

    xSemaphoreCreateRecursiveMutex(xMutex, 0, local_xIsTimeOut, local_var1, local_var2, EP);
    skip;

    d_step {
        prvInitialiseTaskLists(local_var1);

        xTaskCreate_fixed(xControllingTaskHandle, recmuCONTROLLING_TASK_PRIORITY);
        xTaskCreate_fixed(xBlockingTaskHandle, recmuBLOCKING_TASK_PRIORITY);
        xTaskCreate_fixed(FIRST_TASK + 2, recmuPOLLING_TASK_PRIORITY);
    };

    vTaskStartScheduler(EP, local_var1);

    /* Start the IDLE TASK */
    vTaskIDLE_TASK_BODY(IDLE_TASK_ID, local_var1)
}
