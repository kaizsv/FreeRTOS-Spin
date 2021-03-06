/* FreeRTOS/Demo/Common/Minimal/BlockQ.c */

#define promela_TASK_NUMBER     6
#define promela_QUEUE_NUMBER    3

#define FIRST_TASK              promela_EXP_NUMBER
#define IDLE_TASK_ID            (FIRST_TASK + promela_TASK_NUMBER)

#define RUN_ALL_TASKS(stmts) \
    atomic {                \
        stmts;              \
        run QConsB1();      \
        run QProdB2();      \
        run QConsB3();      \
        run QProdB4();      \
        run QProdB5();      \
        run QConsB6();      \
    }

#define QUEUE_SEND_EXIT_CRITICAL
#define QUEUE_RECEIVE_EXIT_CRITICAL

#include "../FreeRTOS.pml"
#include "../FreeRTOS/tasks.pml"
#include "../FreeRTOS/queue.h.pml"

#ifdef LTL
    #include "../property/BlockQ.ltl"
#endif

#define xBlockTime  100
#define xDontBlock  0

QueueDeclarator(1, byte);
QueueDeclarator(2, byte); /* In source code, size is 5 */

QueueHandle_t(pxQueueParameters1_xQueue, 1, byte);
#define pxQueueParameters1_xBlockTime       xBlockTime

#define pxQueueParameters2_xQueue           pxQueueParameters1_xQueue
#define pxQueueParameters2_xBlockTime       xDontBlock

QueueHandle_t(pxQueueParameters3_xQueue, 1, byte);
#define pxQueueParameters3_xBlockTime       xDontBlock

#define pxQueueParameters4_xQueue           pxQueueParameters3_xQueue
#define pxQueueParameters4_xBlockTime       xBlockTime

QueueHandle_t(pxQueueParameters5_xQueue, 2, byte);
#define pxQueueParameters5_xBlockTime       xBlockTime

#define pxQueueParameters6_xQueue           pxQueueParameters5_xQueue
#define pxQueueParameters6_xBlockTime       xBlockTime

#define INCREASE_VAR_AND_INTOVERFLOW_3(var) \
    AWAIT(_PID, var = var + 1; var = var % 3)

#define INCREASE_VAR_AND_INTOVERFLOW_2(var) \
    AWAIT(_PID, var = var + 1; var = var % 2)

proctype QConsB1()
{
    byte idx;
    byte usData, usExpectedValue = 0;
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bit local_xReturn = false;
    bit local_xIsTimeOut = false;
    assert(_PID == FIRST_TASK);
do
::  xQueueReceive(pxQueueParameters1_xQueue, usData, pxQueueParameters1_xBlockTime, local_xReturn, local_xIsTimeOut, local_var1, local_var2, _PID);
    if
    :: SELE(_PID, local_xReturn == true, local_xReturn = false);
        AWAIT(_PID, assert(usData == usExpectedValue));
        /* Catch-up */
running:
        INCREASE_VAR_AND_INTOVERFLOW_2(usExpectedValue);

        #if (configUSE_PREEMPTION == 0)
        // pxQueueParameters1_xBlockTime is not zero
        #endif
    :: ELSE(_PID, local_xReturn == true)
    fi
od
}

proctype QProdB2()
{
    byte idx;
    byte usValue = 0;
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bit local_xReturn = false, local_xIsTimeOut = false;
    assert(_PID == FIRST_TASK + 1);
do
::  xQueueSend(pxQueueParameters2_xQueue, usValue, pxQueueParameters2_xBlockTime, local_xReturn, local_xIsTimeOut, local_var1, local_var2, _PID);
    AWAIT(_PID, assert(local_xReturn == true); local_xReturn = false);
running:
    INCREASE_VAR_AND_INTOVERFLOW_2(usValue);

    #if (configUSE_PREEMPTION == 0)
    taskYIELD(_PID, local_var1);
    #endif
od
}

proctype QConsB3()
{
    byte idx;
    byte usData, usExpectedValue = 0;
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bit local_xReturn = false;
    bit local_xIsTimeOut = false;
    assert(_PID == FIRST_TASK + 2);
do
::  xQueueReceive(pxQueueParameters3_xQueue, usData, pxQueueParameters3_xBlockTime, local_xReturn, local_xIsTimeOut, local_var1, local_var2, _PID);
    if
    :: SELE(_PID, local_xReturn == true, local_xReturn = false);
        AWAIT(_PID, assert(usData == usExpectedValue));
        /* Catch-up */
running:
        INCREASE_VAR_AND_INTOVERFLOW_2(usExpectedValue);

        #if (configUSE_PREEMPTION == 0)
        // pxQueueParameters3_xBlockTime is zero
        taskYIELD(_PID, local_var1);
        #endif
    :: ELSE(_PID, local_xReturn == true)
    fi
od
}

proctype QProdB4()
{
    byte idx;
    byte usValue = 0;
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bit local_xReturn = false, local_xIsTimeOut = false;
    assert(_PID == FIRST_TASK + 3);
do
::  xQueueSend(pxQueueParameters4_xQueue, usValue, pxQueueParameters4_xBlockTime, local_xReturn, local_xIsTimeOut, local_var1, local_var2, _PID);
    AWAIT(_PID, assert(local_xReturn == true); local_xReturn = false);
running:
    INCREASE_VAR_AND_INTOVERFLOW_2(usValue);

    #if (configUSE_PREEMPTION == 0)
    taskYIELD(_PID, local_var1);
    #endif
od
}

proctype QProdB5()
{
    byte idx;
    byte usValue = 0;
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bit local_xReturn = false, local_xIsTimeOut = false;
    assert(_PID == FIRST_TASK + 4);
do
::  xQueueSend(pxQueueParameters5_xQueue, usValue, pxQueueParameters5_xBlockTime, local_xReturn, local_xIsTimeOut, local_var1, local_var2, _PID);
    AWAIT(_PID, assert(local_xReturn == true); local_xReturn = false);
running:
    INCREASE_VAR_AND_INTOVERFLOW_3(usValue);

    #if (configUSE_PREEMPTION == 0)
    taskYIELD(_PID, local_var1);
    #endif
od
}

proctype QConsB6()
{
    byte idx;
    byte usData, usExpectedValue = 0;
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bit local_xReturn = false;
    bit local_xIsTimeOut = false;
    assert(_PID == FIRST_TASK + 5);
do
::  xQueueReceive(pxQueueParameters6_xQueue, usData, pxQueueParameters6_xBlockTime, local_xReturn, local_xIsTimeOut, local_var1, local_var2, _PID);
    if
    :: SELE(_PID, local_xReturn == true, local_xReturn = false);
        AWAIT(_PID, assert(usData == usExpectedValue));
        /* Catch-up */
running:
        INCREASE_VAR_AND_INTOVERFLOW_3(usExpectedValue);

        #if (configUSE_PREEMPTION == 0)
        // pxQueueParameters6_xBlockTime is not zero
        #endif
    :: ELSE(_PID, local_xReturn == true)
    fi
od
}

init {
    byte idx;
    byte local_var1 = NULL_byte;

    d_step {
        xQueueCreate(pxQueueParameters1_xQueue, 0, 1);
        xQueueCreate(pxQueueParameters3_xQueue, 1, 1);
        xQueueCreate(pxQueueParameters5_xQueue, 2, 2);

        prvInitialiseTaskLists(local_var1);

        xTaskCreate_fixed(FIRST_TASK + 0, 1);
        xTaskCreate_fixed(FIRST_TASK + 1, tskIDLE_PRIORITY);

        xTaskCreate_fixed(FIRST_TASK + 2, tskIDLE_PRIORITY);
        xTaskCreate_fixed(FIRST_TASK + 3, 1);

        xTaskCreate_fixed(FIRST_TASK + 4, tskIDLE_PRIORITY);
        xTaskCreate_fixed(FIRST_TASK + 5, tskIDLE_PRIORITY);
    };

    vTaskStartScheduler(EP, local_var1);

    /* Start the IDLE TASK */
    vTaskIDLE_TASK_BODY(IDLE_TASK_ID, local_var1)
}
