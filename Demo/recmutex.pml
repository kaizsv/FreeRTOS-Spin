/* FreeRTOS/Demo/Common/Minimal/recmutex.c */

#define promela_TASK_NUMBER     4
#define promela_QUEUE_NUMBER    1

#define FIRST_TASK              promela_EXP_NUMBER
#define IDLE_TASK_ID            (FIRST_TASK + promela_TASK_NUMBER)

#define RUN_ALL_TASKS(stmts) \
    atomic {                \
        stmts;              \
        run Rec1();         \
        run Rec2();         \
        run Rec3();         \
        run prvCheckTask(); \
    }

#ifdef CORRECTION
    #define CLEAR_configIDLE_SHOULD_YIELD_IF_USE_PREEMPTION_AND_TIME_SLICING
#endif

#include "../FreeRTOS.pml"
#include "../FreeRTOS/tasks.pml"
#include "../FreeRTOS/semphr.h.pml"

#ifdef LTL
    #include "property/recmutex.ltl"
#endif

#ifndef recmuCONTROLLING_TASK_PRIORITY
    #define recmuCONTROLLING_TASK_PRIORITY  (tskIDLE_PRIORITY + 2)
#endif
#define recmuBLOCKING_TASK_PRIORITY (tskIDLE_PRIORITY + 1)
#define recmuPOLLING_TASK_PRIORITY  (tskIDLE_PRIORITY + 0)

#define recmuMAX_COUNT      2 /* Origin is 10 */

#define recmuSHORT_DELAY    20
#define recmuNO_DELAY       0
#define recmu15ms_DELAY     15

SemaphoreDeclarator(1, byte);
SemaphoreHandle_t(xMutex, 1, byte);

#define INC_AND_WRAP_AROUND(val)    ((val + 1) % 8)

byte uxControllingCycles = 0, uxBlockingCycles = 0;

bool xControllingIsSuspended = false, xBlockingIsSuspended = false;

#define xControllingTaskHandle  (FIRST_TASK + 0)
#define xBlockingTaskHandle     (FIRST_TASK + 1)

proctype Rec1()
{
    byte ux = 0;
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bool local_bit = false, local_xReturn = false;
    assert(_PID == xControllingTaskHandle);
do
::  xSemaphoreGiveRecursive(_PID, xMutex, local_xReturn, local_bit, local_var1, local_var2);
    /* Should not be able to 'give' the mutex, as we have not yet 'taken' it */
    AWAIT(_PID, assert(local_xReturn == false));

    do
    :: SELE(_PID, ux < recmuMAX_COUNT, ux = ux + 1);
        xSemaphoreTakeRecursive(_PID, xMutex, recmu15ms_DELAY, local_xReturn, local_bit, local_var1, local_var2);
        AWAIT(_PID, assert(local_xReturn == true); local_xReturn = false);
        vTaskDelay(_PID, recmuSHORT_DELAY, local_var1);
    :: ELSE(_PID, ux < recmuMAX_COUNT, ux = 0; break)
    od;

    do
    :: SELE(_PID, ux < recmuMAX_COUNT, ux = ux + 1);
        vTaskDelay(_PID, recmuSHORT_DELAY, local_var1);
        xSemaphoreGiveRecursive(_PID, xMutex, local_xReturn, local_bit, local_var1, local_var2);
        AWAIT(_PID, assert(local_xReturn == true); local_xReturn = false);

        #if (configUSE_PREEMPTION == 0)
        taskYIELD(_PID);
        #endif
    :: ELSE(_PID, ux < recmuMAX_COUNT, ux = 0; break)
    od;

    xSemaphoreGiveRecursive(_PID, xMutex, local_xReturn, local_bit, local_var1, local_var2);
    AWAIT(_PID, assert(local_xReturn == false));

running:
    AWAIT(_PID, uxControllingCycles = INC_AND_WRAP_AROUND(uxControllingCycles));

    AWAIT(_PID, xControllingIsSuspended = true);
    vTaskSuspend(_PID, NULL_byte, local_var1);
    AWAIT(_PID, xControllingIsSuspended = false);
od
}

proctype Rec2()
{
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bool local_bit = false, local_xReturn = false;
    assert(_PID == xBlockingTaskHandle);
do
::  xSemaphoreTakeRecursive(_PID, xMutex, 254, local_xReturn, local_bit, local_var1, local_var2);
    AWAIT(_PID, assert(local_xReturn == true); local_xReturn = false);
        AWAIT(_PID, assert(xControllingIsSuspended == true));
            xSemaphoreGiveRecursive(_PID, xMutex, local_xReturn, local_bit, local_var1, local_var2);
            AWAIT(_PID, assert(local_xReturn == true); local_xReturn = false);

            AWAIT(_PID, xBlockingIsSuspended = true);
            vTaskSuspend(_PID, NULL_byte, local_var1);
            AWAIT(_PID, xBlockingIsSuspended = false);

    AWAIT(_PID, assert(uxControllingCycles == INC_AND_WRAP_AROUND(uxBlockingCycles)));
running:
    AWAIT(_PID, uxBlockingCycles = INC_AND_WRAP_AROUND(uxBlockingCycles));
od
}

proctype Rec3()
{
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bool local_bit = false, local_xReturn = false;
    assert(_PID == FIRST_TASK + 2);
do
::  xSemaphoreTakeRecursive(_PID, xMutex, recmuNO_DELAY, local_xReturn, local_bit, local_var1, local_var2);
    if
    :: SELE(_PID, local_xReturn == true, local_xReturn = false);
        AWAIT(_PID, assert(xBlockingIsSuspended && xControllingIsSuspended));

running:
        vTaskResume(_PID, xBlockingTaskHandle, local_bit);
        #if (configUSE_PREEMPTION == 0)
        taskYIELD(_PID);
        #endif

        vTaskResume(_PID, xControllingTaskHandle, local_bit);
        #if (configUSE_PREEMPTION == 0)
        taskYIELD(_PID);
        #endif

        AWAIT(_PID, assert(!xBlockingIsSuspended && !xControllingIsSuspended));

        #if (INCLUDE_uxTaskPriorityGet == 1)
        AWAIT(_PID, assert(uxTaskPriorityGet(NULL_byte) == recmuCONTROLLING_TASK_PRIORITY));
        #endif

        xSemaphoreGiveRecursive(_PID, xMutex, local_xReturn, local_bit, local_var1, local_var2);
        AWAIT(_PID, assert(local_xReturn == true); local_xReturn = false);

        #if (INCLUDE_uxTaskPriorityGet == 1)
        AWAIT(_PID, assert(uxTaskPriorityGet(NULL_byte) == recmuPOLLING_TASK_PRIORITY));
        #endif
    :: ELSE(_PID, local_xReturn == true)
    fi;

    #if (configUSE_PREEMPTION == 0)
    taskYIELD(_PID);
    #endif
od
}

proctype prvCheckTask()
{
    byte local_var = NULL_byte;
    assert(_PID == FIRST_TASK + 3);
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

    xSemaphoreCreateRecursiveMutex(xMutex, 0, local_xIsTimeOut, local_var1, local_var2, EP);
    skip;

    d_step {
        prvInitialiseTaskLists();

        xTaskCreate_fixed(xControllingTaskHandle, recmuCONTROLLING_TASK_PRIORITY);
        xTaskCreate_fixed(xBlockingTaskHandle, recmuBLOCKING_TASK_PRIORITY);
        xTaskCreate_fixed(FIRST_TASK + 2, recmuPOLLING_TASK_PRIORITY);
        xTaskCreate_fixed(FIRST_TASK + 3, configMAX_PRIORITIES - 1);
    };

    vTaskStartScheduler(EP);

    /* Start the IDLE TASK */
    vTaskIDLE_TASK_BODY(IDLE_TASK_ID)
}
