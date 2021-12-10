/* FreeRTOS/Demo/Common/Minimal/QPeek.c */
#include "config/QPeek.config"

#define promela_TASK_NUMBER     5
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
        run prvCheckTask(); \
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
    bool local_xReturn = false, local_bit = false;
    assert(_PID == FIRST_TASK);
do
::  AWAIT(_PID, ulValue = MAGIC_VAL1);
    xQueueSendToBack_NB(xQUEUE, ulValue, qpeekNO_BLOCK, local_xReturn, local_bit, local_var1, local_var2, _PID);
    AWAIT(_PID, ulValue = 0; assert(local_xReturn == true); local_xReturn = false);

    #if (configUSE_PREEMPTION == 0)
        taskYIELD(_PID);
    #endif

    AWAIT(_PID, assert(uxQueueMessagesWaiting(xQUEUE) == 0);
        ulValue = MAGIC_VAL2);

    xQueueSendToBack_NB(xQUEUE, ulValue, qpeekNO_BLOCK, local_xReturn, local_bit, local_var1, local_var2, _PID);
    AWAIT(_PID, ulValue = 0; assert(local_xReturn == true); local_xReturn = false);

    #if (configUSE_PREEMPTION == 0)
        taskYIELD(_PID);
    #endif

    xQueueReceive_NB(xQUEUE, ulValue, qpeekNO_BLOCK, local_xReturn, local_var1, local_var2, _PID);
    AWAIT(_PID,
        assert(local_xReturn == true); local_xReturn = false;
        assert(ulValue == MAGIC_VAL2); ulValue = 0
    );

    vTaskDelay(_PID, qpeekSHORT_DELAY, local_var1);

    vTaskResume(_PID, xMediumPriorityTask, local_bit);
    vTaskResume(_PID, xHighPriorityTask, local_bit);
    vTaskResume(_PID, xHighestPriorityTask, local_bit);

    #if (configUSE_PREEMPTION == 0)
        taskYIELD(_PID);
    #endif

    AWAIT(_PID, ulValue = MAGIC_VAL3);
    xQueueSendToFront_NB(xQUEUE, ulValue, qpeekNO_BLOCK, local_xReturn, local_bit, local_var1, local_var2, _PID);
    AWAIT(_PID, ulValue = 0; assert(local_xReturn == true); local_xReturn = false);

    #if (configUSE_PREEMPTION == 0)
        taskYIELD(_PID);
    #endif

    /* The queue should be empty */
    xQueuePeek_NB(_PID, xQUEUE, ulValue, qpeekNO_BLOCK, local_xReturn, local_var1, local_var2);
    AWAIT(_PID, assert(local_xReturn == false));

    vTaskResume(_PID, xHighPriorityTask, local_bit);
    vTaskResume(_PID, xHighestPriorityTask, local_bit);

    vTaskDelay(_PID, qpeekSHORT_DELAY, local_var1);
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

proctype prvCheckTask()
{
    byte local_var = NULL_byte;
    assert(_PID == FIRST_TASK + 4);
do
::  { // vTaskDelay
        AWAIT(_PID,
            assert(uxSchedulerSuspended == 0);
            uxSchedulerSuspended = uxSchedulerSuspended + 1; // vTaskSuspendAll(_PID);
        );
        { // prvAddCurrentTaskToDelayedList(_PID, local_var, false);
            AWAIT(_PID, d_step {
                assert(listLIST_ITEM_CONTAINER(TCB(pxCurrentTCB).xStateListItem) == CID_READY_LISTS + TCB(pxCurrentTCB).uxPriority);
                uxListRemove_pxIndex(pxReadyTasksLists[TCB(pxCurrentTCB).uxPriority], RLIST_SIZE, pxCurrentTCB, TCB(pxCurrentTCB).xStateListItem)
            });
            if
            :: SELE(_PID, listLIST_IS_EMPTY(pxReadyTasksLists[TCB(pxCurrentTCB).uxPriority]));
                AWAIT(_PID, portRESET_READY_PRIORITY(TCB(pxCurrentTCB).uxPriority, uxTopReadyPriority))
            :: ELSE(_PID, listLIST_IS_EMPTY(pxReadyTasksLists[TCB(pxCurrentTCB).uxPriority]))
            fi;
            AWAIT(_PID, d_step {
                if
                :: listLIST_IS_EMPTY(pxDelayedTaskList) ->
                    local_var = 10
                :: else ->
                    assert(hidden_var == NULL_byte);
                    for (hidden_idx: 0 .. (DLIST_SIZE - 1)) {
                        if
                        :: !listPOINTER_IS_NULL(pxDelayedTaskList.ps[hidden_idx]) ->
                            hidden_var = listGET_LIST_ITEM_VALUE(pxOrdinalStateListItem(pxDelayedTaskList, hidden_idx));
                        :: else -> break
                        fi
                    }
                    assert(hidden_var != NULL_byte && hidden_var > xTickCount);
                    local_var = hidden_var - xTickCount + 1;
                    hidden_idx = NULL_byte; hidden_var = NULL_byte;
                fi;
                assert(local_var < 256 && listGET_LIST_ITEM_VALUE(TCB(pxCurrentTCB).xStateListItem) == 0);
                listSET_LIST_ITEM_VALUE(TCB(pxCurrentTCB).xStateListItem, local_var)
            });
            AWAIT(_PID, d_step {
                if
                :: !listLIST_IS_EMPTY(pxDelayedTaskList) ->
                    update_xTickCount();
                :: else
                fi;
                assert(xTickCount == 0);
                vListInsert_sortStateListItem(pxDelayedTaskList, DLIST_SIZE, CID_DELAYED_TASK, pxCurrentTCB, TCB(pxCurrentTCB).xStateListItem)
            });
            if
            :: SELE(_PID, local_var < xNextTaskUnblockTicks);
                AWAIT(_PID, xNextTaskUnblockTicks = local_var; local_var = NULL_byte)
            :: ELSE(_PID, local_var < xNextTaskUnblockTicks, local_var = NULL_byte);
            fi;
        }; // End of prvAddCurrentTaskToDelayedList(_PID, local_var, false);
        xTaskResumeAll(_PID, local_var, true);
        if
        :: SELE(_PID, local_var == NULL_byte); // not yielded
            portYIELD_WITHIN_API(_PID)
        :: ELSE(_PID, local_var == NULL_byte, local_var = NULL_byte) // yielded
        fi
    }
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
        xTaskCreate_fixed(xHighestPriorityTask, qpeekHIGHEST_PRIORITY);
        xTaskCreate_fixed(FIRST_TASK + 4, configMAX_PRIORITIES - 1);
    };

    vTaskStartScheduler(EP);

    /* Start the IDLE TASK */
    vTaskIDLE_TASK_BODY(IDLE_TASK_ID)
}
