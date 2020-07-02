/* FreeRTOS/Demo/Common/Minimal/PollQ.c */

#define promela_TASK_NUMBER     2
#define promela_QUEUE_NUMBER    1

#define FIRST_TASK              promela_EXP_NUMBER
#define IDLE_TASK_ID            (FIRST_TASK + promela_TASK_NUMBER)

#define RUN_ALL_TASKS(stmts) \
    atomic {                \
        stmts;              \
        run QConsNB();      \
        run QProdNB();      \
    }

#if 0
#define QUEUE_SEND_EXIT_CRITICAL
#define QUEUE_RECEIVE_EXIT_CRITICAL
#endif

#include "../FreeRTOS.pml"
#include "../FreeRTOS/tasks.pml"
#include "../FreeRTOS/queue.h.pml"

#define usNumToProduce 3

QueueDeclarator(10, byte);
QueueHandle_t(xPolledQueue, 10, byte);

#define INCREASE_VAR_AND_INTOVERFLOW(var)   \
    AWAIT_D(_PID, var = var + 1; var = var % (usNumToProduce + 1))

#define pollqPRODUCER_DELAY 50
#define pollqCONSUMER_DELAY 40
#define pollqNO_DELAY   0

proctype QConsNB()
{
    byte idx;
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bit local_xReturn = false, local_bit = false;
    bit local_xIsTimeOut = false;

    byte usData, usExpectedValue = 0;
    assert(_PID == FIRST_TASK + 0);
do
::  do
    :: SELE2(_PID, uxQueueMessagesWaiting(xPolledQueue));
        xQueueReceive(xPolledQueue, usData, 0, local_xReturn, local_xIsTimeOut, local_var1, local_var2, _PID);
        if
        :: SELE3(_PID, local_xReturn == true, local_xReturn = false);
            AWAIT_D(_PID, assert(usData == usExpectedValue));
            INCREASE_VAR_AND_INTOVERFLOW(usExpectedValue)
        :: ELSE2(_PID, local_xReturn == true)
        fi
    :: ELSE3(_PID, uxQueueMessagesWaiting(xPolledQueue), break)
    od;
    vTaskDelay(_PID, pollqCONSUMER_DELAY, local_bit, local_var1, local_var2);
od
}

proctype QProdNB()
{
    byte idx;
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bit local_xReturn = false, local_bit = false;
    bit local_xIsTimeOut = false;

    byte usValue = 0, usLoop = 0;
    assert(_PID == FIRST_TASK + 1);
do
::  do
    :: SELE3(_PID, usLoop < usNumToProduce, usLoop = usLoop + 1);
        xQueueSend(xPolledQueue, usValue, pollqNO_DELAY, local_xReturn, local_bit, local_xIsTimeOut, local_var1, local_var2, _PID);
        AWAIT_A(_PID, assert(local_xReturn == true); local_xReturn = false);
        INCREASE_VAR_AND_INTOVERFLOW(usValue)
    :: ELSE3(_PID, usLoop < usNumToProduce, usLoop = 0; break)
    od;
    vTaskDelay(_PID, pollqPRODUCER_DELAY, local_bit, local_var1, local_var2);
od
}

init {
    byte idx;
    byte local_var1 = NULL_byte;

    d_step {
        xQueueCreate(xPolledQueue, 0, 10);

        prvInitialiseTaskLists(local_var1);

        xTaskCreate_fixed(FIRST_TASK + 0, 1);
        xTaskCreate_fixed(FIRST_TASK + 1, 1)
    };

    vTaskStartScheduler(EP, local_var1);

    /* Start the IDLE TASK */
    vTaskIDLE_TASK_BODY(IDLE_TASK_ID, local_var1)
}
