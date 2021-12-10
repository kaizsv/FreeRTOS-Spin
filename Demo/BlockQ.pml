/* FreeRTOS/Demo/Common/Minimal/BlockQ.c */
#include "config/BlockQ.config"

#define promela_TASK_NUMBER     7
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
        run prvCheckTask(); \
    }

#define QUEUE_SEND_EXIT_CRITICAL
#define QUEUE_RECEIVE_EXIT_CRITICAL

/* This correction requires memory more than 512GB. */
#ifdef CORRECTION
    #define CLEAR_configIDLE_SHOULD_YIELD_IF_USE_PREEMPTION_AND_TIME_SLICING
#endif

#include "../FreeRTOS.pml"
#include "../FreeRTOS/tasks.pml"
#include "../FreeRTOS/queue.h.pml"

#ifdef LTL
    #include "property/BlockQ.ltl"
#endif

#define xBlockTime  100
#define xDontBlock  0

#define uxQueueSize1    1
#define uxQueueSize2    2 /* Size is 5 in the source */

QueueDeclarator(uxQueueSize1, byte);
QueueDeclarator(uxQueueSize2, byte);

QueueHandle_t(pxQueueParameters1_xQueue, uxQueueSize1, byte);
#define pxQueueParameters1_xBlockTime       xBlockTime

#define pxQueueParameters2_xQueue           pxQueueParameters1_xQueue
#define pxQueueParameters2_xBlockTime       xDontBlock

QueueHandle_t(pxQueueParameters3_xQueue, uxQueueSize1, byte);
#define pxQueueParameters3_xBlockTime       xDontBlock

#define pxQueueParameters4_xQueue           pxQueueParameters3_xQueue
#define pxQueueParameters4_xBlockTime       xBlockTime

QueueHandle_t(pxQueueParameters5_xQueue, uxQueueSize2, byte);
#define pxQueueParameters5_xBlockTime       xBlockTime

#define pxQueueParameters6_xQueue           pxQueueParameters5_xQueue
#define pxQueueParameters6_xBlockTime       xBlockTime

#define INCREASE_VAR_AND_INTOVERFLOW_2(var) \
    AWAIT(_PID, var = (var == 0 -> 1 : 0))

#define G1  10
#define G2  20

proctype QConsB1()
{
#define G1usExpectedValue   G1
    byte usData;
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bit local_xReturn = false;
    assert(_PID == FIRST_TASK);
do
::  xQueueReceive(pxQueueParameters1_xQueue, usData, pxQueueParameters1_xBlockTime, local_xReturn, local_var1, local_var2, _PID);
    if
    :: SELE(_PID, local_xReturn == true, local_xReturn = false);
running:
        AWAIT(_PID, assert(usData == G1usExpectedValue); usData = 0);

        #if (configUSE_PREEMPTION == 0)
        // pxQueueParameters1_xBlockTime is not zero
        #endif
    :: ELSE(_PID, local_xReturn == true)
    fi
od
}

proctype QProdB2()
{
#define G1usValue   G1
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bit local_xReturn = false, local_xIsTimeOut = false;
    assert(_PID == FIRST_TASK + 1);
do
::  xQueueSend(pxQueueParameters2_xQueue, G1usValue, pxQueueParameters2_xBlockTime, local_xReturn, local_xIsTimeOut, local_var1, local_var2, _PID);
running:
    AWAIT(_PID, assert(local_xReturn == true); local_xReturn = false);

    #if (configUSE_PREEMPTION == 0)
    taskYIELD(_PID);
    #endif

#ifdef CORRECTION
    #if (configUSE_PREEMPTION == 1) && (configUSE_TIME_SLICING == 1)
        vTaskDelay(_PID, 30, local_var1);
    #endif
#endif
od
}

proctype QConsB3()
{
#define G2usExpectedValue   G2
    byte usData;
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bit local_xReturn = false;
    assert(_PID == FIRST_TASK + 2);
do
::  xQueueReceive(pxQueueParameters3_xQueue, usData, pxQueueParameters3_xBlockTime, local_xReturn, local_var1, local_var2, _PID);
    if
    :: SELE(_PID, local_xReturn == true, local_xReturn = false);
running:
        AWAIT(_PID, assert(usData == G2usExpectedValue); usData = 0);

        #if (configUSE_PREEMPTION == 0)
        // pxQueueParameters3_xBlockTime is zero
        taskYIELD(_PID);
        #endif
    :: ELSE(_PID, local_xReturn == true)
    fi
od
}

proctype QProdB4()
{
#define G2usValue   G2
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bit local_xReturn = false, local_xIsTimeOut = false;
    assert(_PID == FIRST_TASK + 3);
do
::  xQueueSend(pxQueueParameters4_xQueue, G2usValue, pxQueueParameters4_xBlockTime, local_xReturn, local_xIsTimeOut, local_var1, local_var2, _PID);
running:
    AWAIT(_PID, assert(local_xReturn == true); local_xReturn = false);

    #if (configUSE_PREEMPTION == 0)
    taskYIELD(_PID);
    #endif

#ifdef CORRECTION
    #if (configUSE_PREEMPTION == 1) && (configUSE_TIME_SLICING == 1)
        vTaskDelay(_PID, 30, local_var1);
    #endif
#endif
od
}

proctype QProdB5()
{
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bit usValue = 0;
    bit local_xReturn = false, local_xIsTimeOut = false;
    assert(_PID == FIRST_TASK + 4);
do
::  xQueueSend(pxQueueParameters5_xQueue, usValue, pxQueueParameters5_xBlockTime, local_xReturn, local_xIsTimeOut, local_var1, local_var2, _PID);
    AWAIT(_PID, assert(local_xReturn == true); local_xReturn = false);
running:
    INCREASE_VAR_AND_INTOVERFLOW_2(usValue);

    #if (configUSE_PREEMPTION == 0)
    taskYIELD(_PID);
    #endif
od
}

proctype QConsB6()
{
    byte usData;
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bit usExpectedValue = 0;
    bit local_xReturn = false;
    assert(_PID == FIRST_TASK + 5);
do
::  xQueueReceive(pxQueueParameters6_xQueue, usData, pxQueueParameters6_xBlockTime, local_xReturn, local_var1, local_var2, _PID);
    if
    :: SELE(_PID, local_xReturn == true, local_xReturn = false);
        AWAIT(_PID, assert(usData == usExpectedValue); usData = 0);
        /* Catch-up */
running:
        INCREASE_VAR_AND_INTOVERFLOW_2(usExpectedValue);

        #if (configUSE_PREEMPTION == 0)
        // pxQueueParameters6_xBlockTime is not zero
        #endif
    :: ELSE(_PID, local_xReturn == true)
    fi
od
}

proctype prvCheckTask()
{
    byte local_var = NULL_byte;
    assert(_PID == FIRST_TASK + 6);
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
        xQueueCreate(pxQueueParameters1_xQueue, 0, uxQueueSize1);
        xQueueCreate(pxQueueParameters3_xQueue, 1, uxQueueSize1);
        xQueueCreate(pxQueueParameters5_xQueue, 2, uxQueueSize2);

        prvInitialiseTaskLists();

        xTaskCreate_fixed(FIRST_TASK + 0, 1);
        xTaskCreate_fixed(FIRST_TASK + 1, tskIDLE_PRIORITY);

        xTaskCreate_fixed(FIRST_TASK + 2, tskIDLE_PRIORITY);
        xTaskCreate_fixed(FIRST_TASK + 3, 1);

        xTaskCreate_fixed(FIRST_TASK + 4, tskIDLE_PRIORITY);
        xTaskCreate_fixed(FIRST_TASK + 5, tskIDLE_PRIORITY);

        xTaskCreate_fixed(FIRST_TASK + 6, configMAX_PRIORITIES - 1);
    };

    vTaskStartScheduler(EP);

    /* Start the IDLE TASK */
    vTaskIDLE_TASK_BODY(IDLE_TASK_ID)
}
