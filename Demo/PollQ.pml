/* FreeRTOS/Demo/Common/Minimal/PollQ.c */

#define promela_TASK_NUMBER     3
#define promela_QUEUE_NUMBER    1

#define FIRST_TASK              promela_EXP_NUMBER
#define IDLE_TASK_ID            (FIRST_TASK + promela_TASK_NUMBER)

#define RUN_ALL_TASKS(stmts) \
    atomic {                \
        stmts;              \
        run QConsNB();      \
        run QProdNB();      \
        run prvCheckTask(); \
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
    :: ELSE(_PID, uxQueueMessagesWaiting(xPolledQueue), break)
    od;
    vTaskDelay(_PID, pollqCONSUMER_DELAY, local_var1);
od
}

proctype QProdNB()
{
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bit local_xReturn = false, local_bit = false;

    byte usValue = 0, usLoop = 0;
    assert(_PID == FIRST_TASK + 1);
do
::  do
    :: SELE(_PID, usLoop < usNumToProduce, usLoop = usLoop + 1);
        xQueueSendToBack_NB(xPolledQueue, usValue, pollqNO_DELAY, local_xReturn, local_bit, local_var1, local_var2, _PID);
        AWAIT(_PID, assert(local_xReturn == true); local_xReturn = false);
running:
        INCREASE_VAR_AND_INTOVERFLOW(usValue)
    :: ELSE(_PID, usLoop < usNumToProduce, usLoop = 0; break)
    od;
    vTaskDelay(_PID, pollqPRODUCER_DELAY, local_var1);
od
}

proctype prvCheckTask()
{
    byte local_var = NULL_byte;
    assert(_PID == FIRST_TASK + 2);
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

init {
    d_step {
        xQueueCreate(xPolledQueue, 0, pollqQUEUE_SIZE);

        prvInitialiseTaskLists();

        xTaskCreate_fixed(FIRST_TASK + 0, 1);
        xTaskCreate_fixed(FIRST_TASK + 1, 1);
        xTaskCreate_fixed(FIRST_TASK + 2, configMAX_PRIORITIES - 1);
    };

    vTaskStartScheduler(EP);

    /* Start the IDLE TASK */
    vTaskIDLE_TASK_BODY(IDLE_TASK_ID)
}
