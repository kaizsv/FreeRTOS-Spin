/* FreeRTOS/Demo/Common/Minimal/QPeek.c */
#include "config/QPeek.config"

#define promela_TASK_NUMBER     4
#define promela_QUEUE_NUMBER    1

#define FIRST_TASK              promela_EXP_NUMBER
#define IDLE_TASK_ID            (FIRST_TASK + promela_TASK_NUMBER)

#define RUN_ALL_TASKS(stmts) \
    atomic {            \
        stmts;          \
        run PeekL();    \
        run PeekM();    \
        run PeekH1();   \
        run PeekH2();   \
    }

#ifdef CORRECTION
    #define CLEAR_configIDLE_SHOULD_YIELD_IF_USE_PREEMPTION_AND_TIME_SLICING
#endif

#include "../FreeRTOS.pml"
#include "../FreeRTOS/tasks.pml"
#include "../FreeRTOS/semphr.h.pml"

#ifdef LTL
    #include "property/QPeek.ltl"
#endif

#define qpeekQUEUE_LENGTH   5
#define qpeekNO_BLOCK       0
#define qpeekSHORT_DELAY    10

#define qpeekLOW_PRIORITY       (tskIDLE_PRIORITY)
#define qpeekMED_PRIORITY       (tskIDLE_PRIORITY + 1)
#define qpeekHIGH_PRIORITY      (tskIDLE_PRIORITY + 2)
#define qpeekHIGHEST_PRIORITY   (tskIDLE_PRIORITY + 3)

#define xMediumPriorityTask     (FIRST_TASK + 1)
#define xHighPriorityTask       (FIRST_TASK + 2)
#define xHighestPriorityTask    (FIRST_TASK + 3)

#define MAGIC_VAL1  123 /* identification of 0x11223344 in the source code */
#define MAGIC_VAL2  213 /* identification of 0x01234567 in the source code */
#define MAGIC_VAL3  231 /* identification of 0xaabbaabb in the source code */

QueueDeclarator(qpeekQUEUE_LENGTH, byte);
QueueHandle_t(xQUEUE, qpeekQUEUE_LENGTH, byte);

proctype PeekL()
{
    byte local_var1 = NULL_byte, local_var2 = NULL_byte, ulValue = 0;
    bool local_xReturn = false;
    assert(_PID == FIRST_TASK);
do
::  AWAIT(_PID, ulValue = MAGIC_VAL1);
    xQueueSendToBack_NB(xQUEUE, ulValue, qpeekNO_BLOCK, local_xReturn, local_var1, local_var2, _PID);
    AWAIT(_PID, ulValue = 0; assert(local_xReturn == true); local_xReturn = false);

    #if (configUSE_PREEMPTION == 0)
        taskYIELD(_PID);
    #endif

    AWAIT(_PID, assert(uxQueueMessagesWaiting(xQUEUE) == 0);
        ulValue = MAGIC_VAL2);

    xQueueSendToBack_NB(xQUEUE, ulValue, qpeekNO_BLOCK, local_xReturn, local_var1, local_var2, _PID);
    AWAIT(_PID, ulValue = 0; assert(local_xReturn == true); local_xReturn = false);

    #if (configUSE_PREEMPTION == 0)
        taskYIELD(_PID);
    #endif

    xQueueReceive_NB(xQUEUE, ulValue, qpeekNO_BLOCK, local_xReturn, local_var1, local_var2, _PID);
    AWAIT(_PID,
        assert(local_xReturn == true); local_xReturn = false;
        assert(ulValue == MAGIC_VAL2); ulValue = 0
    );

    vTaskDelay(_PID, qpeekSHORT_DELAY, local_var1, local_var2);

    vTaskResume(_PID, xMediumPriorityTask, local_var1);
    vTaskResume(_PID, xHighPriorityTask, local_var1);
    vTaskResume(_PID, xHighestPriorityTask, local_var1);

    #if (configUSE_PREEMPTION == 0)
        taskYIELD(_PID);
    #endif

    AWAIT(_PID, ulValue = MAGIC_VAL3);
    xQueueSendToFront_NB(xQUEUE, ulValue, qpeekNO_BLOCK, local_xReturn, local_var1, local_var2, _PID);
    AWAIT(_PID, ulValue = 0; assert(local_xReturn == true); local_xReturn = false);

    #if (configUSE_PREEMPTION == 0)
        taskYIELD(_PID);
    #endif

    /* The queue should be empty */
    xQueuePeek_NB(_PID, xQUEUE, ulValue, qpeekNO_BLOCK, local_xReturn, local_var1, local_var2);
    AWAIT(_PID, assert(local_xReturn == false));

    vTaskResume(_PID, xHighPriorityTask, local_var1);
    vTaskResume(_PID, xHighestPriorityTask, local_var1);

    vTaskDelay(_PID, qpeekSHORT_DELAY, local_var1, local_var2);
od
}

proctype PeekM()
{
    byte local_var1 = NULL_byte, local_var2 = NULL_byte, ulValue = 0;
    bool local_xReturn = false;
    assert(_PID == xMediumPriorityTask);
do
::  xQueuePeek_PR(_PID, xQUEUE, ulValue, portMAX_DELAY, local_xReturn, local_var1, local_var2);
    AWAIT(_PID,
        assert(local_xReturn == true); local_xReturn = false;
        assert(ulValue == MAGIC_VAL2); ulValue = 0
    );

    AWAIT(_PID, assert(uxQueueMessagesWaiting(xQUEUE) == 1));

running:
    vTaskSuspend(_PID, NULL_byte, local_var1);
od
}

proctype PeekH1()
{
    byte local_var1 = NULL_byte, local_var2 = NULL_byte, ulValue = 0;
    bool local_xReturn = false;
    assert(_PID == xHighPriorityTask);
do
::  xQueuePeek_PR(_PID, xQUEUE, ulValue, portMAX_DELAY, local_xReturn, local_var1, local_var2);
    AWAIT(_PID,
        assert(local_xReturn == true); local_xReturn = false;
        assert(ulValue == MAGIC_VAL2); ulValue = 0
    );

    AWAIT(_PID, assert(uxQueueMessagesWaiting(xQUEUE) == 1));

    vTaskSuspend(_PID, NULL_byte, local_var1);

    xQueueReceive(xQUEUE, ulValue, portMAX_DELAY, local_xReturn, local_var1, local_var2, _PID);
    AWAIT(_PID,
        assert(local_xReturn == true); local_xReturn = false;
        assert(ulValue == MAGIC_VAL3); ulValue = 0
    );

    vTaskSuspend(_PID, NULL_byte, local_var1);
od
}

proctype PeekH2()
{
    byte local_var1 = NULL_byte, local_var2 = NULL_byte, ulValue = 0;
    bool local_xReturn = false;
    assert(_PID == xHighestPriorityTask);
do
::  xQueuePeek_PR(_PID, xQUEUE, ulValue, portMAX_DELAY, local_xReturn, local_var1, local_var2);
    AWAIT(_PID,
        assert(local_xReturn == true); local_xReturn = false;
        assert(ulValue == MAGIC_VAL1); ulValue = 0
    );

    AWAIT(_PID, assert(uxQueueMessagesWaiting(xQUEUE) == 1));

    xQueueReceive_NB(xQUEUE, ulValue, qpeekNO_BLOCK, local_xReturn, local_var1, local_var2, _PID);
    AWAIT(_PID,
        assert(local_xReturn == true); local_xReturn = false;
        assert(ulValue == MAGIC_VAL1); ulValue = 0
    );

    /* Block again */
    xQueuePeek_PR(_PID, xQUEUE, ulValue, portMAX_DELAY, local_xReturn, local_var1, local_var2);
    AWAIT(_PID,
        assert(local_xReturn == true); local_xReturn = false;
        assert(ulValue == MAGIC_VAL2); ulValue = 0
    );

    AWAIT(_PID, assert(uxQueueMessagesWaiting(xQUEUE) == 1));

    /* Only peeked the data */
    vTaskSuspend(_PID, NULL_byte, local_var1);

    xQueuePeek_PR(_PID, xQUEUE, ulValue, portMAX_DELAY, local_xReturn, local_var1, local_var2);
    AWAIT(_PID,
        assert(local_xReturn == true); local_xReturn = false;
        assert(ulValue == MAGIC_VAL3); ulValue = 0
    );

    vTaskSuspend(_PID, NULL_byte, local_var1);
od
}

init
{
    d_step {
        xQueueCreate(xQUEUE, 0, qpeekQUEUE_LENGTH);

        prvInitialiseTaskLists();

        xTaskCreate_fixed(FIRST_TASK, qpeekLOW_PRIORITY);
        xTaskCreate_fixed(xMediumPriorityTask, qpeekMED_PRIORITY);
        xTaskCreate_fixed(xHighPriorityTask, qpeekHIGH_PRIORITY);
        xTaskCreate_fixed(xHighestPriorityTask, qpeekHIGHEST_PRIORITY)
    };

    vTaskStartScheduler(EP);

    /* Start the IDLE TASK */
    vTaskIDLE_TASK_BODY(IDLE_TASK_ID)
}
