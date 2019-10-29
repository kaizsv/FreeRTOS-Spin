/* FreeRTOS/Demo/Common/Full/PollQ.c */
/* NOTE: the delayed time of xQueueSendToBack needs to be portMAX_DELAY, or
         the verification will be failed due to the fine grain time-slicing */

#define promela_TASK_NUMBER     2
#define promela_QUEUE_NUMBER    1

#define FIRST_TASK              promela_EXP_NUMBER
#define IDLE_TASK_ID            (FIRST_TASK + promela_TASK_NUMBER)

#define RUN_ALL_TASKS()     \
    atomic {                \
        run QConsNB();      \
        run QProdNB();      \
                            \
        run IDLE_TASK();    \
    }

#define QUEUE_SEND_EXIT_CRITICAL
//#define QUEUE_RECEIVE_EXIT_CRITICAL

#include "../FreeRTOS.pml"
#include "../FreeRTOS/tasks.pml"
#include "../FreeRTOS/queue.h.pml"

#define usNumToProduce 3

QueueDeclarator(10, byte);
QueueHandle_t(xPolledQueue, 10, byte);

#define INCREASE_VAR_AND_INTOVERFLOW(var)   \
    AWAIT_D(_PID, var = var + 1;            \
        if                                  \
        :: var == 253 -> var = 0            \
        :: else                             \
        fi                                  \
    )                                       \

proctype QConsNB()
{
    byte idx;
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bit local_xReturn = false, local_bit = false;
    bit local_xIsNDTimeOut = false;

    byte usData, usExpectedValue = 0;
    assert(_PID == FIRST_TASK + 0);
loop:
    do
    :: SELE(_PID, uxQueueMessagesWaiting(xPolledQueue)) ->
        xQueueReceive(xPolledQueue, usData, 0, local_xReturn, local_xIsNDTimeOut, local_var1, local_var2, _PID);
        if
        :: SELE(_PID, local_xReturn == true) ->
            AWAIT_D(_PID, assert(usData == usExpectedValue));
            INCREASE_VAR_AND_INTOVERFLOW(usExpectedValue)
        :: ELSE(_PID, local_xReturn == true)
        fi
    :: ELSE(_PID, uxQueueMessagesWaiting(xPolledQueue)) ->
        AWAIT_A(_PID, break)
    od;
    vTaskDelay(_PID, 1, local_bit, local_var1, local_var2);
    AWAIT_A(_PID, goto loop)
}

proctype QProdNB()
{
    byte idx;
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bit local_xReturn = false, local_bit = false;
    bit local_xIsNDTimeOut = false;

    byte usValue = 0, usLoop;
    assert(_PID == FIRST_TASK + 1);
loop:
    do
    :: atomic { SELE(_PID, usLoop < usNumToProduce) -> usLoop = usLoop + 1 };
        xQueueSendToBack(xPolledQueue, usValue, portMAX_DELAY, local_xReturn, local_bit, local_xIsNDTimeOut, local_var1, local_var2, _PID);
        if
        :: SELE(_PID, local_xReturn != true) ->
            assert(false)
        :: ELSE(_PID, local_xReturn != true) ->
            INCREASE_VAR_AND_INTOVERFLOW(usValue)
        fi
    :: atomic { ELSE(_PID, usLoop < usNumToProduce) -> usLoop = 0; break }
    od;
    vTaskDelay(_PID, 1, local_bit, local_var1, local_var2);
    AWAIT_A(_PID, goto loop)
}

init {
    byte idx;
    byte local_var1 = NULL_byte;

    xQueueCreate(xPolledQueue, 0, 10);

    prvInitialiseTaskLists(local_var1);

    xTaskCreate(EP, FIRST_TASK + 0, 1, local_var1);
    xTaskCreate(EP, FIRST_TASK + 1, 1, local_var1);

    vTaskStartScheduler(EP, local_var1)
}