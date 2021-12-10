/* FreeRTOS/Demo/Common/Minimal/GenQTest.c */
/* INCLUDE_xTaskAbortDelay is not defined */
#include "config/GenQTest.config"

#define promela_TASK_NUMBER     5
#define promela_QUEUE_NUMBER    3

#define FIRST_TASK              promela_EXP_NUMBER
#define IDLE_TASK_ID            (FIRST_TASK + promela_TASK_NUMBER)

#define RUN_ALL_TASKS(stmts)    \
    atomic {            \
        stmts;          \
        run GenQ();     \
        run MuLow();    \
        run MuMed();    \
        run MuHigh();   \
        run prvCheckTask(); \
    }

#ifdef CORRECTION
    #define CLEAR_configIDLE_SHOULD_YIELD_IF_USE_PREEMPTION_AND_TIME_SLICING
#endif

#include "../FreeRTOS.pml"
#include "../FreeRTOS/tasks.pml"
#include "../FreeRTOS/semphr.h.pml"

#ifdef LTL
    #include "property/GenQTest.ltl"
#endif

#define genqQUEUE_LENGTH    5
#define intsemNO_BLOCK      0
#define genqSHORT_BLOCK     2

#define genqMUTEX_LOW_PRIORITY  tskIDLE_PRIORITY
#define genqMUTEX_TEST_PRIORITY tskIDLE_PRIORITY + 1
#define genqMUTEX_MED_PRIORITY  tskIDLE_PRIORITY + 2
#define genqMUTEX_HIGH_PRIORITY tskIDLE_PRIORITY + 3

#define xMediumPriorityMutexTask    (FIRST_TASK + 2)
#define xHighPriorityMutexTask      (FIRST_TASK + 3)

SemaphoreDeclarator(1, byte);
QueueDeclarator(genqQUEUE_LENGTH, byte);

QueueHandle_t(xQUEUE, genqQUEUE_LENGTH, byte);
SemaphoreHandle_t(xMUTEX, 1, byte);
SemaphoreHandle_t(xLOCALMUTEX, 1, byte);

byte ulLoopCounter = 0;
byte ulGuardedVariable = 0;

#define INC_VAR_AND_WRAP_AROUND(var)    (var + 1) % 6

proctype GenQ()
{
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bool local_xReturn = false, local_xIsTimeOut = false;

    byte ulLoopCounterSnapshot = 0, ulData = 0, ulData2 = 0;
    assert(_PID == FIRST_TASK);
do
::  AWAIT(_PID, ulLoopCounterSnapshot = ulLoopCounter);
    xQueueSendToFront_NB(xQUEUE, ulLoopCounterSnapshot, intsemNO_BLOCK, _, local_xIsTimeOut, local_var1, local_var2, _PID);

    AWAIT(_PID, ulLoopCounterSnapshot = 0; assert(uxQueueMessagesWaiting(xQUEUE) == 1));

    xQueueReceive_NB(xQUEUE, ulData, intsemNO_BLOCK, local_xReturn, local_var1, local_var2, _PID);
    AWAIT(_PID, assert(local_xReturn == true); local_xReturn = false);

    AWAIT(_PID, assert(ulLoopCounter == ulData && uxQueueMessagesWaiting(xQUEUE) == 0);
        ulData = 0);

    AWAIT(_PID, ulLoopCounterSnapshot = ulLoopCounter);
    xQueueSendToBack_NB(xQUEUE, ulLoopCounterSnapshot, intsemNO_BLOCK, _, local_xIsTimeOut, local_var1, local_var2, _PID);

    AWAIT(_PID, ulLoopCounterSnapshot = 0; assert(uxQueueMessagesWaiting(xQUEUE) == 1));

    xQueueReceive_NB(xQUEUE, ulData, intsemNO_BLOCK, local_xReturn, local_var1, local_var2, _PID);
    AWAIT(_PID, assert(local_xReturn == true); local_xReturn = false);

    AWAIT(_PID, assert(uxQueueMessagesWaiting(xQUEUE) == 0 && ulLoopCounter == ulData);
        ulData = 0);

    #if (configUSE_PREEMPTION == 0)
    taskYIELD(_PID);
    #endif

    for (ulData: 2 .. 4) {
        xQueueSendToBack_NB(xQUEUE, ulData, intsemNO_BLOCK, _, local_xIsTimeOut, local_var1, local_var2, _PID);
    }

    AWAIT(_PID, ulData = 0; assert(uxQueueMessagesWaiting(xQUEUE) == 3));

    xQueueSendToFront_NB(xQUEUE, 1, intsemNO_BLOCK, _, local_xIsTimeOut, local_var1, local_var2, _PID);
    xQueueSendToFront_NB(xQUEUE, 0, intsemNO_BLOCK, _, local_xIsTimeOut, local_var1, local_var2, _PID);

    AWAIT(_PID, assert(uxQueueMessagesWaiting(xQUEUE) == 5));

    xQueueSendToFront_NB(xQUEUE, 0, intsemNO_BLOCK, local_xReturn, local_xIsTimeOut, local_var1, local_var2, _PID);
    AWAIT(_PID, assert(local_xReturn == false));

    xQueueSendToBack_NB(xQUEUE, 0, intsemNO_BLOCK, local_xReturn, local_xIsTimeOut, local_var1, local_var2, _PID);
    AWAIT(_PID, assert(local_xReturn == false));

    #if (configUSE_PREEMPTION == 0)
    taskYIELD(_PID);
    #endif

    for (ulData: 0 .. (genqQUEUE_LENGTH - 1)) {
        xQueuePeek_NB(_PID, xQUEUE, ulData2, intsemNO_BLOCK, local_xReturn, local_var1, local_var2);
        AWAIT(_PID, assert(local_xReturn == true); local_xReturn = false;
            assert(ulData == ulData2); ulData2 = 0);

        xQueueReceive_NB(xQUEUE, ulData2, intsemNO_BLOCK, local_xReturn, local_var1, local_var2, _PID);
        AWAIT(_PID, assert(local_xReturn == true); local_xReturn = false;
            assert(ulData == ulData2); ulData2 = 0);
    }

    AWAIT(_PID, ulData = 0; assert(uxQueueMessagesWaiting(xQUEUE) == 0));

    #if (configUSE_PREEMPTION == 0)
    taskYIELD(_PID);
    #endif

    for (ulData: 10 .. 11) {
        xQueueSendToBack_NB(xQUEUE, ulData, intsemNO_BLOCK, local_xReturn, local_xIsTimeOut, local_var1, local_var2, _PID);
        AWAIT(_PID, assert(local_xReturn == true); local_xReturn = false);
    }

    AWAIT(_PID, assert(uxQueueMessagesWaiting(xQUEUE) == 2));

    for (ulData: 0 .. 2) {
        xQueueSendToFront_NB(xQUEUE, 9 - ulData, intsemNO_BLOCK, local_xReturn, local_xIsTimeOut, local_var1, local_var2, _PID);
        AWAIT(_PID, assert(local_xReturn == true); local_xReturn = false);
    }

    AWAIT(_PID, ulData = 0; assert(uxQueueMessagesWaiting(xQUEUE) == 5));

    xQueueSendToFront_NB(xQUEUE, 0, intsemNO_BLOCK, local_xReturn, local_xIsTimeOut, local_var1, local_var2, _PID);
    AWAIT(_PID, assert(local_xReturn == false));

    xQueueSendToBack_NB(xQUEUE, 0, intsemNO_BLOCK, local_xReturn, local_xIsTimeOut, local_var1, local_var2, _PID);
    AWAIT(_PID, assert(local_xReturn == false));

    for (ulData: 7 .. (6 + genqQUEUE_LENGTH)) {
        xQueueReceive_NB(xQUEUE, ulData2, intsemNO_BLOCK, local_xReturn, local_var1, local_var2, _PID);
        AWAIT(_PID, assert(local_xReturn == true); local_xReturn = false;
            assert(ulData == ulData2); ulData2 = 0);
    }

    AWAIT(_PID, ulData = 0; assert(uxQueueMessagesWaiting(xQUEUE) == 0));

running:
    AWAIT(_PID, ulLoopCounter = INC_VAR_AND_WRAP_AROUND(ulLoopCounter));

#ifdef CORRECTION
    #if (configUSE_PREEMPTION == 1) && (configUSE_TIME_SLICING == 0)
        taskYIELD(_PID);
    #endif
#endif
od
}

inline prvTakeTwoMutexesReturnInDifferentOrder(_id, xMutex, xLocalMutex, xReturn, temp_bool, temp_var1, temp_var2)
{
    xSemaphoreTake(xMutex, intsemNO_BLOCK, xReturn, temp_bool, temp_var1, temp_var2, _id);
    AWAIT(_id, assert(xReturn == true); xReturn = false);

    AWAIT(_id, ulGuardedVariable = 0);

    AWAIT(_id, assert(uxTaskPriorityGet(NULL_byte) == genqMUTEX_LOW_PRIORITY));

    vTaskResume(_id, xHighPriorityMutexTask, temp_bool);

    #if (configUSE_PREEMPTION == 0)
    taskYIELD(_id);
    #endif

    AWAIT(_id, assert(uxTaskPriorityGet(NULL_byte) == genqMUTEX_HIGH_PRIORITY));

    vTaskPrioritySet(_id, NULL_byte, genqMUTEX_TEST_PRIORITY, temp_var1, temp_bool, temp_var2);
    AWAIT(_id, assert(uxTaskPriorityGet(NULL_byte) == genqMUTEX_HIGH_PRIORITY));

    vTaskResume(_id, xMediumPriorityMutexTask, temp_bool);

    AWAIT(_id, assert(ulGuardedVariable == 0));

    xSemaphoreTake(xLocalMutex, intsemNO_BLOCK, xReturn, temp_bool, temp_var1, temp_var2, _id);
    AWAIT(_id, assert(xReturn == true); xReturn = false);

    xSemaphoreGive(xMutex, xReturn, temp_bool, temp_var1, temp_var2, _id);
    AWAIT(_id, assert(xReturn == true); xReturn = false);

    #if (configUSE_PREEMPTION == 0)
    taskYIELD(_id);
    #endif

    AWAIT(_id, assert(ulGuardedVariable == 0));

    AWAIT(_id, assert(uxTaskPriorityGet(NULL_byte) == genqMUTEX_HIGH_PRIORITY));

    xSemaphoreGive(xLocalMutex, xReturn, temp_bool, temp_var1, temp_var2, _id);
    AWAIT(_id, assert(xReturn == true); xReturn = false);

    #if (configUSE_PREEMPTION == 0)
    taskYIELD(_id);
    #endif

    AWAIT(_id, assert(ulGuardedVariable == 1));

    AWAIT(_id, assert(uxTaskPriorityGet(NULL_byte) == genqMUTEX_TEST_PRIORITY));

    vTaskPrioritySet(_id, NULL_byte, genqMUTEX_LOW_PRIORITY, temp_var1, temp_bool, temp_var2);
#ifdef CORRECTION
    #if (configUSE_PREEMPTION == 1) && (configUSE_TIME_SLICING == 1)
        vTaskDelay(_PID, 5, temp_var1);
    #endif
#endif
}

inline prvTakeTwoMutexesReturnInSameOrder(_id, xMutex, xLocalMutex, xReturn, temp_bool, temp_var1, temp_var2)
{
    xSemaphoreTake(xMutex, intsemNO_BLOCK, xReturn, temp_bool, temp_var1, temp_var2, _id);
    AWAIT(_id, assert(xReturn == true); xReturn = false);

    AWAIT(_id, ulGuardedVariable = 0);

    AWAIT(_id, assert(uxTaskPriorityGet(NULL_byte) == genqMUTEX_LOW_PRIORITY));

    vTaskResume(_id, xHighPriorityMutexTask, temp_bool);

    #if (configUSE_PREEMPTION == 0)
    taskYIELD(_id);
    #endif

    AWAIT(_id, assert(uxTaskPriorityGet(NULL_byte) == genqMUTEX_HIGH_PRIORITY));

    vTaskResume(_id, xMediumPriorityMutexTask, temp_bool);

    AWAIT(_id, assert(ulGuardedVariable == 0));

    xSemaphoreTake(xLocalMutex, intsemNO_BLOCK, xReturn, temp_bool, temp_var1, temp_var2, _id);
    AWAIT(_id, assert(xReturn == true); xReturn = false);

    xSemaphoreGive(xLocalMutex, xReturn, temp_bool, temp_var1, temp_var2, _id);
    AWAIT(_id, assert(xReturn == true); xReturn = false);

    #if (configUSE_PREEMPTION == 0)
    taskYIELD(_id);
    #endif

    AWAIT(_id, assert(ulGuardedVariable == 0));

    AWAIT(_id, assert(uxTaskPriorityGet(NULL_byte) == genqMUTEX_HIGH_PRIORITY));

    xSemaphoreGive(xMutex, xReturn, temp_bool, temp_var1, temp_var2, _id);
    AWAIT(_id, assert(xReturn == true); xReturn = false);

    #if (configUSE_PREEMPTION == 0)
    taskYIELD(_id);
    #endif

    AWAIT(_id, assert(ulGuardedVariable == 1));

    AWAIT(_id, assert(uxTaskPriorityGet(NULL_byte) == genqMUTEX_LOW_PRIORITY));
}

proctype MuLow()
{
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bool local_bit = false, local_xReturn = false;
    assert(_PID == (FIRST_TASK + 1));
do
::  prvTakeTwoMutexesReturnInDifferentOrder(_PID, xMUTEX, xLOCALMUTEX, local_xReturn, local_bit, local_var1, local_var2);

running:
    #if (configUSE_PREEMPTION == 0)
    taskYIELD(_PID);
    #endif

    prvTakeTwoMutexesReturnInSameOrder(_PID, xMUTEX, xLOCALMUTEX, local_xReturn, local_bit, local_var1, local_var2);

    #if (configUSE_PREEMPTION == 0)
    taskYIELD(_PID);
    #endif
od
}

proctype MuMed()
{
    byte local_var1 = NULL_byte;
    assert(_PID == xMediumPriorityMutexTask);
do
::  vTaskSuspend(_PID, NULL_byte, local_var1);
    AWAIT(_PID, ulGuardedVariable = INC_VAR_AND_WRAP_AROUND(ulGuardedVariable));
od
}

proctype MuHigh()
{
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bool local_bit = false, local_xReturn = false;
    assert(_PID == xHighPriorityMutexTask);
do
::  vTaskSuspend(_PID, NULL_byte, local_var1);
    xSemaphoreTake(xMUTEX, portMAX_DELAY, local_xReturn, local_bit, local_var1, local_var2, _PID);
    AWAIT(_PID, assert(local_xReturn == true); local_xReturn = false);

    xSemaphoreGive(xMUTEX, local_xReturn, local_bit, local_var1, local_var2, _PID);
    AWAIT(_PID, assert(local_xReturn == true); local_xReturn = false);
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
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bool local_xIsTimeOut = false;

    d_step {
        xQueueCreate(xQUEUE, 0, genqQUEUE_LENGTH);
    };

    xSemaphoreCreateMutex(xMUTEX, 1, local_xIsTimeOut, local_var1, local_var2, EP);
    xSemaphoreCreateMutex(xLOCALMUTEX, 2, local_xIsTimeOut, local_var1, local_var2, EP);
    skip;

    d_step {
        prvInitialiseTaskLists();

        xTaskCreate_fixed(FIRST_TASK, tskIDLE_PRIORITY);
        xTaskCreate_fixed(FIRST_TASK + 1, genqMUTEX_LOW_PRIORITY);
        xTaskCreate_fixed(xMediumPriorityMutexTask, genqMUTEX_MED_PRIORITY);
        xTaskCreate_fixed(xHighPriorityMutexTask, genqMUTEX_HIGH_PRIORITY);
        xTaskCreate_fixed(FIRST_TASK + 4, configMAX_PRIORITIES - 1);
    };

    vTaskStartScheduler(EP);

    /* Start the IDLE TASK */
    vTaskIDLE_TASK_BODY(IDLE_TASK_ID)
}
