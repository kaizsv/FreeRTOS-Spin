/* FreeRTOS/Demo/Common/Minimal/dynamic.c */
#include "config/dynamic.config"

#define promela_TASK_NUMBER     5
#define promela_QUEUE_NUMBER    1

#define FIRST_TASK              promela_EXP_NUMBER
#define IDLE_TASK_ID            (FIRST_TASK + promela_TASK_NUMBER)

#define RUN_ALL_TASKS(stmts) \
    atomic {                \
        stmts;              \
        run CONT_INC();     \
        run LIM_INC();      \
        run C_CTRL();       \
        run SUSP_SEND();    \
        run SUSP_RECV();    \
    }

#define QUEUE_SEND_EXIT_CRITICAL
#define QUEUE_RECEIVE_EXIT_CRITICAL

#include "../FreeRTOS.pml"
#include "../FreeRTOS/tasks.pml"
#include "../FreeRTOS/queue.h.pml"

#ifdef LTL
    #include "property/dynamic.ltl"
#endif

#define xContinousIncrementHandle   FIRST_TASK + 0
#define xLimitedIncrementHandle     FIRST_TASK + 1

#define xQueueSendWhenSuspendedHandler      FIRST_TASK + 3
#define xQueueReceiveWhenSuspendedHandler   FIRST_TASK + 4

#define ULCOUNTER_IS_ACCESSED_BY(id, var)   \
    AWAIT(_PID, var = id)

#define priSLEEP_TIME   80
#define priLOOPS        5
#define priMAX_COUNT    3
#define priNO_BLOCK     0
#define priSUSPENDED_QUEUE_LENGTH 1
byte ulCounter;

QueueDeclarator(priSUSPENDED_QUEUE_LENGTH, byte);
QueueHandle_t(xSuspendedTestQueue, priSUSPENDED_QUEUE_LENGTH, byte);

proctype CONT_INC()
{
    byte idx;
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bit local_bit = false;

#define uxOurPriority tskIDLE_PRIORITY
    assert(_PID == xContinousIncrementHandle);
do
::  vTaskPrioritySet(_PID, NULL_byte, uxOurPriority + 1, local_var1, local_bit, local_var2);
    ULCOUNTER_IS_ACCESSED_BY(xContinousIncrementHandle, ulCounter);
    vTaskPrioritySet(_PID, NULL_byte, uxOurPriority, local_var1, local_bit, local_var2);

    #if (configUSE_PREEMPTION == 0)
    taskYIELD(_PID, local_var1);
    #endif
od
}

proctype LIM_INC()
{
    byte idx;
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;

    assert(_PID == xLimitedIncrementHandle);
    vTaskSuspend(_PID, NULL_byte, local_var1, local_var2);
do
::  ULCOUNTER_IS_ACCESSED_BY(xLimitedIncrementHandle, ulCounter);
        vTaskSuspend(_PID, NULL_byte, local_var1, local_var2);
od
}

proctype C_CTRL()
{
    byte idx;
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bit local_bit = false;

    assert(_PID == FIRST_TASK + 2);
do
::  /* Remove sLoops to simplify verification */
        vTaskSuspend(_PID, xContinousIncrementHandle, local_var1, local_var2);
            ULCOUNTER_IS_ACCESSED_BY(_PID, ulCounter);
        vTaskResume(_PID, xContinousIncrementHandle, local_bit, local_var1);

        #if (configUSE_PREEMPTION == 0)
        taskYIELD(_PID, local_var1);
        #endif

        vTaskDelay(_PID, priSLEEP_TIME, local_bit, local_var1, local_var2);

        vTaskSuspendAll(_PID);
            AWAIT(_PID, assert(ulCounter == xContinousIncrementHandle));
        xTaskResumeAll(_PID, local_var1, _, local_var2);

    vTaskSuspend(_PID, xContinousIncrementHandle, local_var1, local_var2);

    AWAIT(_PID, ulCounter = 0);

    vTaskResume(_PID, xLimitedIncrementHandle, local_bit, local_var1);

    #if (configUSE_PREEMPTION == 0)
    taskYIELD(_PID, local_var1);
    #endif

running:
    AWAIT(_PID, assert(ulCounter == xLimitedIncrementHandle));

    vTaskResume(_PID, xContinousIncrementHandle, local_bit, local_var1);

    #if (configUSE_PREEMPTION == 0)
    taskYIELD(_PID, local_var1);
    #endif
od
}

#define ulValueToSend   xQueueSendWhenSuspendedHandler
#define ulExpectedValue xQueueSendWhenSuspendedHandler

proctype SUSP_SEND()
{
    byte idx;
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bit local_bit = false, local_xReturn = false;
    assert(_PID == xQueueSendWhenSuspendedHandler);
do
::  vTaskSuspendAll(_PID);
    xQueueSendToBack_NB(xSuspendedTestQueue, ulValueToSend, priNO_BLOCK, local_xReturn, local_bit, local_var1, local_var2, _PID);
    AWAIT(_PID, assert(local_xReturn == true); local_xReturn = false);
    xTaskResumeAll(_PID, local_var1, _, local_var2);
    vTaskDelay(_PID, priSLEEP_TIME, local_bit, local_var1, local_var2);
od
}

proctype SUSP_RECV()
{
    byte idx;
    byte local_var1 = NULL_byte, local_var2 = NULL_byte, ulReceivedValue = 0;
    bit local_xIsTimeOut = false, xGotValue = false;
    assert(_PID == xQueueReceiveWhenSuspendedHandler);
do
::  do
    :: SELE(_PID, xGotValue == false);
        /* Remove pointless vTaskSuspendAll and xTaskResumeAll */
        xQueueReceive(xSuspendedTestQueue, ulReceivedValue, priNO_BLOCK, xGotValue, local_xIsTimeOut, local_var1, local_var2, _PID);
    :: ELSE(_PID, xGotValue == false, xGotValue = false; break)
    od;
running:
    AWAIT(_PID, assert(ulReceivedValue == ulExpectedValue); ulReceivedValue = 0);
od
}

init {
    byte idx;
    byte local_var = NULL_byte;

    d_step {
        xQueueCreate(xSuspendedTestQueue, 0, priSUSPENDED_QUEUE_LENGTH);

        prvInitialiseTaskLists(local_var);

        xTaskCreate_fixed(xContinousIncrementHandle, tskIDLE_PRIORITY);
        xTaskCreate_fixed(xLimitedIncrementHandle, tskIDLE_PRIORITY + 1);
        xTaskCreate_fixed(FIRST_TASK + 2, tskIDLE_PRIORITY);
        xTaskCreate_fixed(xQueueSendWhenSuspendedHandler, tskIDLE_PRIORITY);
        xTaskCreate_fixed(xQueueReceiveWhenSuspendedHandler, tskIDLE_PRIORITY);
    };

    vTaskStartScheduler(EP, local_var);

    /* Start the IDLE TASK */
    vTaskIDLE_TASK_BODY(IDLE_TASK_ID, local_var)
}
