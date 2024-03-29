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

#include "../FreeRTOS.pml"
#include "../FreeRTOS/tasks.pml"
#include "../FreeRTOS/queue.h.pml"

#ifdef LTL
    #include "property/PollQ.ltl"
#endif

#define usNumToProduce 3

#define INCREASE_VAR_AND_INTOVERFLOW(var)   \
    AWAIT(_PID, var = var + 1; var = var % (usNumToProduce + 1))

#define pollqQUEUE_SIZE 10
#define pollqPRODUCER_DELAY 50
#define pollqCONSUMER_DELAY 40
#define pollqNO_DELAY   0

QueueDeclarator(pollqQUEUE_SIZE, byte);
QueueHandle_t(xPolledQueue, pollqQUEUE_SIZE, byte);

proctype QConsNB()
{
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bit local_xReturn = false;

    byte usData, usExpectedValue = 0;
    assert(_PID == FIRST_TASK + 0);
do
::  do
    :: SELE(_PID, uxQueueMessagesWaiting(xPolledQueue));
        xQueueReceive_NB(xPolledQueue, usData, pollqNO_DELAY, local_xReturn, local_var1, local_var2, _PID);
        if
        :: SELE(_PID, local_xReturn == true, local_xReturn = false);
            AWAIT(_PID, assert(usData == usExpectedValue));
running:
            INCREASE_VAR_AND_INTOVERFLOW(usExpectedValue)
        :: ELSE(_PID, local_xReturn == true)
        fi
    :: ELSE(_PID, uxQueueMessagesWaiting(xPolledQueue)); atomic { (_PID == EP); break }
    od;
    vTaskDelay(_PID, pollqCONSUMER_DELAY, local_var1, local_var2);
od
}

proctype QProdNB()
{
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bit local_xReturn = false;

    byte usValue = 0, usLoop = 0;
    assert(_PID == FIRST_TASK + 1);
do
::  do
    :: SELE(_PID, usLoop < usNumToProduce, usLoop = usLoop + 1);
        xQueueSendToBack_NB(xPolledQueue, usValue, pollqNO_DELAY, local_xReturn, local_var1, local_var2, _PID);
        AWAIT(_PID, assert(local_xReturn == true); local_xReturn = false);
running:
        INCREASE_VAR_AND_INTOVERFLOW(usValue)
    :: ELSE(_PID, usLoop < usNumToProduce, usLoop = 0); atomic { (_PID == EP); break }
    od;
    vTaskDelay(_PID, pollqPRODUCER_DELAY, local_var1, local_var2);
od
}

init {
    d_step {
        xQueueCreate(xPolledQueue, 0, pollqQUEUE_SIZE);

        prvInitialiseTaskLists();

        xTaskCreate_fixed(FIRST_TASK + 0, 1);
        xTaskCreate_fixed(FIRST_TASK + 1, 1)
    };

    vTaskStartScheduler(EP);

    /* Start the IDLE TASK */
    vTaskIDLE_TASK_BODY(IDLE_TASK_ID)
}
