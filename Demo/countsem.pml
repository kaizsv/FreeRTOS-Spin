/* FreeRTOS/Demo/Common/Minimal/countsem.c */

#define promela_TASK_NUMBER     3
#define promela_QUEUE_NUMBER    2

#define FIRST_TASK              promela_EXP_NUMBER
#define IDLE_TASK_ID            (FIRST_TASK + promela_TASK_NUMBER)

#define RUN_ALL_TASKS(stmts) \
    atomic {        \
        stmts;      \
        run CNT1(); \
        run CNT2(); \
        run prvCheckTask(); \
    }

#ifdef CORRECTION
    #define CLEAR_configIDLE_SHOULD_YIELD_IF_USE_PREEMPTION_AND_TIME_SLICING
#endif

#include "../FreeRTOS.pml"
#include "../FreeRTOS/tasks.pml"
#include "../FreeRTOS/semphr.h.pml"

#ifdef LTL
    #include "property/countsem.ltl"
#endif

#define countMAX_COUNT_VALUE    10

#define countSTART_AT_MAX_COUNT 170 /* 0xaa */
#define countSTART_AT_ZERO      85  /* 0x55 */

#define countNUM_TEST_TASKS 2
#define countDONT_BLOCK     0

SemaphoreDeclarator(countMAX_COUNT_VALUE, byte);

SemaphoreHandle_t(xP1_xSemaphore, countMAX_COUNT_VALUE, byte);
SemaphoreHandle_t(xP2_xSemaphore, countMAX_COUNT_VALUE, byte);

inline prvDecrementSemaphoreCount(_id, ux, xSemaphore, xReturn, temp_bool, temp_var1, temp_var2)
{
    xSemaphoreGive(xSemaphore, xReturn, temp_bool, temp_var1, temp_var2, _id);
    AWAIT(_id, assert(xReturn == false));

    for (ux: 0 .. (countMAX_COUNT_VALUE - 1)) {
        AWAIT(_id, assert(uxSemaphoreGetCount(xSemaphore) == (countMAX_COUNT_VALUE - (ux))));

        xSemaphoreTake_NB(xSemaphore, countDONT_BLOCK, xReturn, temp_bool, temp_var1, temp_var2, _id);
        AWAIT(_id, assert(xReturn == true); xReturn = false);
runningDec:
        AWAIT(_id, skip)
    }

#if (configUSE_PREEMPTION == 0)
    taskYIELD(_id);
#endif

    AWAIT(_id, ux = 0; assert(uxSemaphoreGetCount(xSemaphore) == 0));
    xSemaphoreTake_NB(xSemaphore, countDONT_BLOCK, xReturn, temp_bool, temp_var1, temp_var2, _id);
    AWAIT(_id, assert(xReturn == false))
}

inline prvIncrementSemaphoreCount(_id, ux, xSemaphore, xReturn, temp_bool, temp_var1, temp_var2)
{
    xSemaphoreTake_NB(xSemaphore, countDONT_BLOCK, xReturn, temp_bool, temp_var1, temp_var2, _id);
    AWAIT(_id, assert(xReturn == false));

    for (ux: 0 .. (countMAX_COUNT_VALUE - 1)) {
        AWAIT(_id, assert(uxSemaphoreGetCount(xSemaphore) == ux));

        xSemaphoreGive(xSemaphore, xReturn, temp_bool, temp_var1, temp_var2, _id);
        AWAIT(_id, assert(xReturn == true); xReturn = false);
runningInc:
        AWAIT(_id, skip)
    }

#if (configUSE_PREEMPTION == 0)
    taskYIELD(_id);
#endif

    xSemaphoreGive(xSemaphore, xReturn, temp_bool, temp_var1, temp_var2, _id);
    AWAIT(_id, ux = 0; assert(xReturn == false));
}

proctype CNT1()
{
    byte local_var1 = NULL_byte, local_var2 = NULL_byte, ux = 0;
    bool local_xReturn = false, local_bit = false;
    assert(_PID == FIRST_TASK);
    // pxParameter->uxExpectedStartCount == countSTART_AT_MAX_COUNT
    // prvDecrementSemaphoreCount: remove the running label
    xSemaphoreGive(xP1_xSemaphore, local_xReturn, local_bit, local_var1, local_var2, _PID);
    AWAIT(_PID, assert(local_xReturn == false));
    for (ux: 0 .. (countMAX_COUNT_VALUE - 1)) {
        AWAIT(_PID, assert(uxSemaphoreGetCount(xP1_xSemaphore) == (countMAX_COUNT_VALUE - (ux))));
        xSemaphoreTake_NB(xP1_xSemaphore, countDONT_BLOCK, local_xReturn, local_bit, local_var1, local_var2, _PID);
        AWAIT(_PID, assert(local_xReturn == true); local_xReturn = false);
    }
#if (configUSE_PREEMPTION == 0)
    taskYIELD(_PID);
#endif
    AWAIT(_PID, ux = 0; assert(uxSemaphoreGetCount(xP1_xSemaphore) == 0));
    xSemaphoreTake_NB(xP1_xSemaphore, countDONT_BLOCK, local_xReturn, local_bit, local_var1, local_var2, _PID);
    AWAIT(_PID, assert(local_xReturn == false))
    // end prvDecrementSemaphoreCount //////////////////////////////

    xSemaphoreTake_NB(xP1_xSemaphore, 0, local_xReturn, local_bit, local_var1, local_var2, _PID);
    AWAIT(_PID, assert(local_xReturn == false));
do
::  prvIncrementSemaphoreCount(_PID, ux, xP1_xSemaphore, local_xReturn, local_bit, local_var1, local_var2);
    prvDecrementSemaphoreCount(_PID, ux, xP1_xSemaphore, local_xReturn, local_bit, local_var1, local_var2);

#ifdef CORRECTION
    #if (configUSE_PREEMPTION == 1) && (configUSE_TIME_SLICING == 0)
        taskYIELD(_PID);
    #endif
#endif
od
}

proctype CNT2()
{
    byte local_var1 = NULL_byte, local_var2 = NULL_byte, ux = 0;
    bool local_xReturn = false, local_bit = false;
    assert(_PID == (FIRST_TASK + 1));

    xSemaphoreTake_NB(xP2_xSemaphore, 0, local_xReturn, local_bit, local_var1, local_var2, _PID);
    AWAIT(_PID, assert(local_xReturn == false));
do
::  prvIncrementSemaphoreCount(_PID, ux, xP2_xSemaphore, local_xReturn, local_bit, local_var1, local_var2);
    prvDecrementSemaphoreCount(_PID, ux, xP2_xSemaphore, local_xReturn, local_bit, local_var1, local_var2);

#ifdef CORRECTION
    #if (configUSE_PREEMPTION == 1) && (configUSE_TIME_SLICING == 0)
        taskYIELD(_PID);
    #endif
#endif
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

init
{
    d_step {
        xSemaphoreCreateCounting_fixed(xP1_xSemaphore, 0, countMAX_COUNT_VALUE, countMAX_COUNT_VALUE);
        xSemaphoreCreateCounting_fixed(xP2_xSemaphore, 1, countMAX_COUNT_VALUE, 0);

        prvInitialiseTaskLists();

        xTaskCreate_fixed(FIRST_TASK + 0, tskIDLE_PRIORITY);
        xTaskCreate_fixed(FIRST_TASK + 1, tskIDLE_PRIORITY);
        xTaskCreate_fixed(FIRST_TASK + 2, configMAX_PRIORITIES - 1);
    };

    vTaskStartScheduler(EP);

    /* Start the IDLE TASK */
    vTaskIDLE_TASK_BODY(IDLE_TASK_ID)
}
