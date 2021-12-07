/* FreeRTOS/Demo/Common/Minimal/semtest.c */
#include "config/semtest.config"

#define promela_TASK_NUMBER     4
#define promela_QUEUE_NUMBER    2

#define FIRST_TASK              promela_EXP_NUMBER
#define IDLE_TASK_ID            (FIRST_TASK + promela_TASK_NUMBER)

#define RUN_ALL_TASKS(stmts)     \
    atomic {                     \
        stmts;                   \
        run prvSemaphoreTest1(); \
        run prvSemaphoreTest2(); \
        run prvSemaphoreTest3(); \
        run prvSemaphoreTest4(); \
    }

/* After applying the correction, the verification is still disproved.
 * The error is polling the binary semaphore.
 */
#ifdef CORRECTION
    #define CLEAR_configIDLE_SHOULD_YIELD_IF_USE_PREEMPTION_AND_TIME_SLICING
#endif

#include "../FreeRTOS.pml"
#include "../FreeRTOS/tasks.pml"
#include "../FreeRTOS/semphr.h.pml"

#ifdef LTL
    #include "property/semtest.ltl"
#endif

SemaphoreDeclarator(1, byte);

SemaphoreHandle_t(pxFirstSemaphore_xSemaphore, 1, byte);
bit pxFirstSemaphore_pulSharedVariable = 0;
#define pxFirstSemaphore_xBlockTime 0

SemaphoreHandle_t(pxSecondSemaphore_xSemaphore, 1, byte);
bit pxSecondSemaphore_pulSharedVariable = 0;
#define pxSecondSemaphore_xBlockTime 10

#define xDelay  100

proctype prvSemaphoreTest1()
{
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bit local_xReturn = false, local_bit = false;
    assert(FIRST_TASK == _PID);
do
::  xSemaphoreTake_NB(pxFirstSemaphore_xSemaphore, pxFirstSemaphore_xBlockTime, local_xReturn, local_bit, local_var1, local_var2, _PID);
    if
    :: SELE(_PID, local_xReturn == true, local_xReturn = false);
        /* Ensure the variable is increased once. Would expect a context switch
        between the two following AWAIT statements */
        AWAIT(_PID, assert(pxFirstSemaphore_pulSharedVariable == 0); pxFirstSemaphore_pulSharedVariable = 1);
        AWAIT(_PID, assert(pxFirstSemaphore_pulSharedVariable == 1); pxFirstSemaphore_pulSharedVariable = 0);

        xSemaphoreGive(pxFirstSemaphore_xSemaphore, local_xReturn, local_bit, local_var1, local_var2, _PID);
running:
        AWAIT(_PID, assert(local_xReturn); local_xReturn = false);

        /* xBlockTime is zero. Need not to delay. */
#ifdef CORRECTION
    #if (configUSE_PREEMPTION == 0) || (configUSE_TIME_SLICING == 0)
        taskYIELD(_PID);
    #endif
#endif
    :: ELSE(_PID, local_xReturn == true);
        /* xBlockTime is zero. Yield. */
        taskYIELD(_PID)
    fi;

#ifdef CORRECTION
    #if (configUSE_PREEMPTION == 1) && (configUSE_TIME_SLICING == 1)
        vTaskDelay(_PID, 5, local_var1);
    #endif
#endif
od
}

proctype prvSemaphoreTest2()
{
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bit local_xReturn = false, local_bit = false;
    assert(FIRST_TASK <= _PID && _PID < IDLE_TASK_ID);
do
::  xSemaphoreTake_NB(pxFirstSemaphore_xSemaphore, pxFirstSemaphore_xBlockTime, local_xReturn, local_bit, local_var1, local_var2, _PID);
    if
    :: SELE(_PID, local_xReturn == true, local_xReturn = false);
        /* Ensure the variable is increased once. Would expect a context switch
        between the two following AWAIT statements */
        AWAIT(_PID, assert(pxFirstSemaphore_pulSharedVariable == 0); pxFirstSemaphore_pulSharedVariable = 1);
        AWAIT(_PID, assert(pxFirstSemaphore_pulSharedVariable == 1); pxFirstSemaphore_pulSharedVariable = 0);

        xSemaphoreGive(pxFirstSemaphore_xSemaphore, local_xReturn, local_bit, local_var1, local_var2, _PID);
running:
        AWAIT(_PID, assert(local_xReturn); local_xReturn = false);

        /* xBlockTime is zero. Need not to delay. */
#ifdef CORRECTION
    #if (configUSE_PREEMPTION == 0) || (configUSE_TIME_SLICING == 0)
        taskYIELD(_PID);
    #endif
#endif
    :: ELSE(_PID, local_xReturn == true);
        /* xBlockTime is zero. Yield. */
        taskYIELD(_PID)
    fi;

#ifdef CORRECTION
    #if (configUSE_PREEMPTION == 1) && (configUSE_TIME_SLICING == 1)
        vTaskDelay(_PID, 5, local_var1);
    #endif
#endif
od
}

proctype prvSemaphoreTest3()
{
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bit local_xReturn = false, local_bit = false;
    assert(FIRST_TASK <= _PID && _PID < IDLE_TASK_ID);
do
::  xSemaphoreTake(pxSecondSemaphore_xSemaphore, pxSecondSemaphore_xBlockTime, local_xReturn, local_bit, local_var1, local_var2, _PID);
    if
    :: SELE(_PID, local_xReturn == true, local_xReturn = false);
        /* Ensure the variable is increased once. Would expect a context switch
        between the two following AWAIT statements */
        AWAIT(_PID, assert(pxSecondSemaphore_pulSharedVariable == 0); pxSecondSemaphore_pulSharedVariable = 1);
        AWAIT(_PID, assert(pxSecondSemaphore_pulSharedVariable == 1); pxSecondSemaphore_pulSharedVariable = 0);

        xSemaphoreGive(pxSecondSemaphore_xSemaphore, local_xReturn, local_bit, local_var1, local_var2, _PID);
        AWAIT(_PID, assert(local_xReturn); local_xReturn = false);

running:
        vTaskDelay(_PID, xDelay, local_var1)
    :: ELSE(_PID, local_xReturn == true)
    fi
od
}

proctype prvSemaphoreTest4()
{
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bit local_xReturn = false, local_bit = false;
    assert(FIRST_TASK <= _PID && _PID < IDLE_TASK_ID);
do
::  xSemaphoreTake(pxSecondSemaphore_xSemaphore, pxSecondSemaphore_xBlockTime, local_xReturn, local_bit, local_var1, local_var2, _PID);
    if
    :: SELE(_PID, local_xReturn == true, local_xReturn = false);
        /* Ensure the variable is increased once. Would expect a context switch
        between the two following AWAIT statements */
        AWAIT(_PID, assert(pxSecondSemaphore_pulSharedVariable == 0); pxSecondSemaphore_pulSharedVariable = 1);
        AWAIT(_PID, assert(pxSecondSemaphore_pulSharedVariable == 1); pxSecondSemaphore_pulSharedVariable = 0);

        xSemaphoreGive(pxSecondSemaphore_xSemaphore, local_xReturn, local_bit, local_var1, local_var2, _PID);
        AWAIT(_PID, assert(local_xReturn); local_xReturn = false);

running:
        vTaskDelay(_PID, xDelay, local_var1)
    :: ELSE(_PID, local_xReturn == true)
    fi
od
}

init {
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bit local_xReturn = false, local_xIsTimeOut = false;

    xSemaphoreCreateBinary(pxFirstSemaphore_xSemaphore, 0);
    xSemaphoreGive(pxFirstSemaphore_xSemaphore, local_xReturn, local_xIsTimeOut, local_var1, local_var2, EP);

    xSemaphoreCreateBinary(pxSecondSemaphore_xSemaphore, 1);
    xSemaphoreGive(pxSecondSemaphore_xSemaphore, local_xReturn, local_xIsTimeOut, local_var1, local_var2, EP);
    skip; /* prevent Spin Error: jump into d_step sequence */

    d_step {
        prvInitialiseTaskLists();
        xTaskCreate_fixed(FIRST_TASK, tskIDLE_PRIORITY);
        xTaskCreate_fixed(FIRST_TASK + 1, tskIDLE_PRIORITY);
        xTaskCreate_fixed(FIRST_TASK + 2, 1);
        xTaskCreate_fixed(FIRST_TASK + 3, 1)
    };
    vTaskStartScheduler(EP);

    /* Start the IDLE TASK */
    vTaskIDLE_TASK_BODY(IDLE_TASK_ID)
}
