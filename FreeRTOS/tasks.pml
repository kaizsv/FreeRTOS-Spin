#ifndef _TASKS_
#define _TASKS_

#include "../FreeRTOS.pml"
#include "list.pml"

#define tskIDLE_PRIORITY        0
#define taskYIELD(_id, temp_var)     portYIELD(_id, temp_var)

#define taskENTER_CRITICAL(_id, temp_var)    portENTER_CRITICAL(_id, temp_var)
#define taskEXIT_CRITICAL(_id, temp_var)     portEXIT_CRITICAL(_id, temp_var)

#if (configUSE_PREEMPTION == 0)
    #define taskYIELD_IF_USING_PREEMPTION()
#else
    #define taskYIELD_IF_USING_PREEMPTION(_id, temp_var) portYIELD_WITHIN_API(_id, temp_var)
#endif

#define taskEVENT_LIST_ITEM_VALUE_IN_USE 8 /* 0b1000 */

#define xState  0
#define xEvent  1
typedef TCB_t {
    ListItem_t ListItems[2];

    byte uxPriority;

#if (configUSE_MUTEXES == 1)
    byte uxBasePriority;
    byte uxMutexesHeld;
#endif
};

#define TCB(index) TCBs[__OWNER_OF(index)]
TCB_t TCBs[promela_TASK_NUMBER + 1];

byte pxCurrentTCB = NULL_byte;

/* Declarator all lists. */
#include "include/Tasks_Lists_Declarator.pml"

#if (configUSE_PORT_OPTIMISED_TASK_SELECTION == 0)

inline taskRECORD_READY_PRIORITY(_id, Priority)
{
    if
    :: SELE(_id, Priority > uxTopReadyPriority) ->
        AWAIT_D(_id, uxTopReadyPriority = Priority)
    :: ELSE(_id, Priority > uxTopReadyPriority)
    fi
}

inline taskSELECT_HIGHEST_PRIORITY_TASK(_id)
{
    for (idx: 0 .. uxTopReadyPriority) {
        if
        :: SELE(_id, !listLIST_IS_EMPTY(pxReadyTasksLists[uxTopReadyPriority - idx])) ->
            AWAIT_A(_id, uxTopReadyPriority = uxTopReadyPriority - idx; break);
        :: ELSE(_id, !listLIST_IS_EMPTY(pxReadyTasksLists[uxTopReadyPriority - idx]))
        fi
    }
    AWAIT_A(_id, idx = 0);

    listGET_OWNER_OF_NEXT_ENTRY(_id, pxCurrentTCB, pxReadyTasksLists[uxTopReadyPriority], RLIST_SIZE)
}

    #define taskRESET_READY_PRIORITY(_id, uxPriority)
    #define portRESET_READY_PRIORITY(_id, uxPriority, uxTopReadyPriority)
#else
// TODO: configUSE_PORT_OPTIMISED_TASK_SELECTION
#endif

byte uxTopReadyPriority = tskIDLE_PRIORITY;
bool xSchedulerRunning = false;
bool xYieldPending = false;
byte uxSchedulerSuspended = 0;

bit xPendedTick = 0;
byte xTickCount = 0;
bool is_xTickCount_active = false;

#define xNextTaskUnblockTicks   \
    listGET_LIST_ITEM_VALUE(TCB(listGET_OWNER_OF_HEAD_ENTRY(pxDelayedTaskList)).ListItems[xState])

#define reset_xTickCount()  \
    is_xTickCount_active = false; xTickCount = 0

#define update_xTickCount() \
    for (idx: 0 .. (DLIST_SIZE - 1)) { \
        if \
        :: !listPOINTER_IS_NULL(pxDelayedTaskList.ps[idx]) -> \
            assert(listGET_LIST_ITEM_VALUE(pxOrdinalListItem(pxDelayedTaskList, idx)) > xTickCount); \
            listSET_LIST_ITEM_VALUE(pxOrdinalListItem(pxDelayedTaskList, idx), \
                listGET_LIST_ITEM_VALUE(pxOrdinalListItem(pxDelayedTaskList, idx)) - xTickCount) \
        :: else -> break \
        fi \
    } \
    idx = 0; \
    assert(xNextTaskUnblockTicks > 0); \
    xTickCount = 0

#define uxCurrentNumberOfTasks promela_TASK_NUMBER + 1 /* user and the idle tasks */

inline prvAddTaskToReadyList(_id, pxTCB)
{
    taskRECORD_READY_PRIORITY(_id, TCB(pxTCB).uxPriority);
    AWAIT_D(_id, vListInsertEnd(pxReadyTasksLists[TCB(pxTCB).uxPriority], RLIST_SIZE, CID_READY_LISTS + TCB(pxTCB).uxPriority, pxTCB, xState))
}

inline prvAddTaskToReadyList_fixed(pxTCB)
{
    uxTopReadyPriority = (TCB(pxTCB).uxPriority > uxTopReadyPriority -> TCB(pxTCB).uxPriority : uxTopReadyPriority);
    vListInsertEnd(pxReadyTasksLists[TCB(pxTCB).uxPriority], RLIST_SIZE, CID_READY_LISTS + TCB(pxTCB).uxPriority, pxTCB, xState)
}

#define prvGetTCBFromHandle(pxHandle) (pxHandle == NULL_byte -> pxCurrentTCB : pxHandle)

inline prvInitialiseTaskLists(idx2)
{
#if (promela_QUEUE_NUMBER > 0)
    /* check the Queue Lists are initialized */
    for (idx: 0 .. (promela_QUEUE_NUMBER - 1)) {
        assert(listPOINTER_IS_NULL(QLISTs[idx * 2].ps[0])); /* xTasksWaitingToSend */
        assert(listPOINTER_IS_NULL(QLISTs[idx*2+1].ps[0])); /* xTasksWaitingToReceive */
    }
    idx = 0;
#endif

    /* idx2: prevent double assignment from vListInitialise */
    for (idx2: 0 .. (configMAX_PRIORITIES - 1)) {
        vListInitialise(pxReadyTasksLists[idx2], RLIST_SIZE);
    }
    idx2 = NULL_byte;

    vListInitialise(xDelayedTaskList1, DLIST_SIZE);
    vListInitialise(xPendingReadyList, PLIST_SIZE);

#if (INCLUDE_vTaskSuspend == 1)
    vListInitialise(xSuspendedTaskList, SLIST_SIZE);
#endif
}

inline xTaskCreate_fixed(pcName, Priority)
{
    /* prvInitialiseNewTask */
    TCB(pcName).uxPriority = (Priority >= configMAX_PRIORITIES -> configMAX_PRIORITIES - 1 : Priority);
#if (configUSE_MUTEXES == 1)
    TCB(pcName).uxBasePriority = Priority;
    TCB(pcName).uxMutexesHeld = 0;
#endif
    vListInitialiseItem(TCB(pcName).ListItems[xState]);
    vListInitialiseItem(TCB(pcName).ListItems[xEvent]);
    listSET_LIST_ITEM_VALUE(TCB(pcName).ListItems[xEvent], configMAX_PRIORITIES - Priority);

    /* prvAddNewTaskToReadyList */
    if
    :: pxCurrentTCB == NULL_byte ->
        pxCurrentTCB = pcName
        /* ensure the list is initialized */
        assert(listLIST_IS_EMPTY(pxReadyTasksLists[0]));
    :: else ->
        pxCurrentTCB = (
            (xSchedulerRunning == false) &&
            (TCB(pxCurrentTCB).uxPriority <= TCB(pcName).uxPriority) ->
                pcName : pxCurrentTCB)
    fi;

    prvAddTaskToReadyList_fixed(pcName);

    /* yield the task if the assertion violated. */
    assert(!((xSchedulerRunning != false) && (TCB(pxCurrentTCB).uxPriority < TCB(pcName).uxPriority)))
}

#if (INCLUDE_vTaskDelay == 1)

inline vTaskDelay(_id, xTicksToDelay, xAlreadyYielded, temp_var, temp_var2)
{
    if
    :: atomic { SELE(_id, xTicksToDelay > 0) -> assert(uxSchedulerSuspended == 0 && xAlreadyYielded == false) };
        vTaskSuspendAll(_id);
        prvAddCurrentTaskToDelayedList(_id, xTicksToDelay, false, temp_var);
        xTaskResumeAll(_id, temp_var, xAlreadyYielded, temp_var2)
    :: atomic { ELSE(_id, xTicksToDelay > 0) -> assert(xAlreadyYielded == false) }
    fi;

    if
    :: atomic { SELE(_id, xAlreadyYielded == false) -> assert(xAlreadyYielded == false) };
        portYIELD_WITHIN_API(_id, temp_var)
    :: atomic { ELSE(_id, xAlreadyYielded == false) -> xAlreadyYielded = false }
    fi
}

#endif

#if (INCLUDE_uxTaskPriorityGet == 1)

#define uxTaskPriorityGet(xTask) TCB(prvGetTCBFromHandle(xTask)).uxPriority

#endif /* INCLUDE_uxTaskPriorityGet */

#if (INCLUDE_vTaskPrioritySet == 1)

inline vTaskPrioritySet(_id, xTask, uxNewPriority, pxTCB, xYieldRequired, temp_var, temp_Priority)
{
    AWAIT_D(_id, assert(uxNewPriority < configMAX_PRIORITIES && xYieldRequired == false));

    taskENTER_CRITICAL(_id, temp_var);
    AWAIT_D(_id, assert(pxTCB == NULL_byte); pxTCB = prvGetTCBFromHandle(xTask));

#if (configUSE_MUTEXES == 1)
    AWAIT_D(_id, assert(temp_Priority == NULL_byte); temp_Priority /* uxCurrentBasePriority */ = TCB(pxTCB).uxBasePriority);
#else
    AWAIT_D(_id, assert(temp_Priority == NULL_byte); temp_Priority /* uxCurrentBasePriority */ = TCB(pxTCB).uxPriority);
#endif

    if
    :: atomic { SELE(_id, temp_Priority /* uxCurrentBasePriority */ != uxNewPriority) -> assert(temp_var == NULL_byte) };
        if
        :: SELE(_id, uxNewPriority > temp_Priority /* uxCurrentBasePriority */) ->
            if
            :: SELE(_id, pxTCB != pxCurrentTCB && uxNewPriority >= TCB(pxCurrentTCB).uxPriority) ->
                AWAIT_D(_id, xYieldRequired = true)
            :: ELSE(_id, pxTCB != pxCurrentTCB && uxNewPriority >= TCB(pxCurrentTCB).uxPriority)
            fi
        :: ELSE(_id, uxNewPriority > temp_Priority /* uxCurrentBasePriority */) ->
            if
            :: SELE(_id, pxTCB == pxCurrentTCB) ->
                AWAIT_D(_id, xYieldRequired = true)
            :: ELSE(_id, pxTCB == pxCurrentTCB) ->
            fi
        fi;

        AWAIT_D(_id, temp_Priority /* uxPriorityUsedOnEntry */ = TCB(pxTCB).uxPriority);

#if (configUSE_MUTEXES == 1)
        if
        :: SELE(_id, TCB(pxTCB).uxBasePriority == TCB(pxTCB).uxPriority) ->
            AWAIT_D(_id, TCB(pxTCB).uxPriority = uxNewPriority)
        :: ELSE(_id, TCB(pxTCB).uxBasePriority == TCB(pxTCB).uxPriority)
        fi;
        AWAIT_D(_id, TCB(pxTCB).uxBasePriority = uxNewPriority);
#else
        AWAIT_D(_id, TCB(pxTCB).uxPriority = uxNewPriority);
#endif
        if
        :: SELE(_id, (listGET_LIST_ITEM_VALUE(TCB(pxTCB).ListItems[xEvent]) & taskEVENT_LIST_ITEM_VALUE_IN_USE) == 0) ->
            AWAIT_D(_id, listSET_LIST_ITEM_VALUE(TCB(pxTCB).ListItems[xEvent], configMAX_PRIORITIES - uxNewPriority))
        :: ELSE(_id, (listGET_LIST_ITEM_VALUE(TCB(pxTCB).ListItems[xEvent]) & taskEVENT_LIST_ITEM_VALUE_IN_USE) == 0)
        fi;

        if
        :: SELE(_id, listIS_CONTAINED_WITHIN(CID_READY_LISTS + temp_Priority /* uxPriorityUsedOnEntry */, TCB(pxTCB).ListItems[xState]) != false) ->
            AWAIT_D(_id, uxListRemove(pxReadyTasksLists[temp_Priority], RLIST_SIZE, pxTCB, xState, temp_var));
            if
            :: atomic { SELE(_id, temp_var == 0) -> temp_var = NULL_byte};
                portRESET_READY_PRIORITY(_id, temp_Priority /* uxPriorityUsedOnEntry */, uxTopReadyPriority)
            :: atomic { ELSE(_id, temp_var == 0) -> temp_var = NULL_byte}
            fi;
            prvAddTaskToReadyList(_id, pxTCB)
        :: ELSE(_id, listIS_CONTAINED_WITHIN(CID_READY_LISTS + temp_Priority /* uxPriorityUsedOnEntry */, TCB(pxTCB).ListItems[xState]) != false)
        fi;

        if
        :: atomic { SELE(_id, xYieldRequired != false) -> xYieldRequired = false; pxTCB = NULL_byte; temp_Priority = NULL_byte };
            taskYIELD_IF_USING_PREEMPTION(_id, temp_var)
        :: atomic { ELSE(_id, xYieldRequired != false) -> assert(xYieldRequired == false); pxTCB = NULL_byte; temp_Priority = NULL_byte }
        fi
    :: atomic { ELSE(_id, temp_Priority /* uxCurrentBasePriority */ != uxNewPriority) -> pxTCB = NULL_byte; temp_Priority = NULL_byte }
    fi;
    taskEXIT_CRITICAL(_id, temp_var)
}

#endif /* INCLUDE_vTaskPrioritySet */

#if (INCLUDE_vTaskSuspend == 1)

inline vTaskSuspend(_id, xTaskToSuspend, pxTCB, temp_var)
{
    taskENTER_CRITICAL(_id, temp_var);
    AWAIT_D(_id, assert(pxTCB == NULL_byte); pxTCB = prvGetTCBFromHandle(xTaskToSuspend));

    AWAIT_D(_id,
        assert(listLIST_ITEM_CONTAINER(TCB(pxTCB).ListItems[xState]) == CID_READY_LISTS + TCB(pxTCB).uxPriority);
        uxListRemove(pxReadyTasksLists[TCB(pxTCB).uxPriority], RLIST_SIZE, pxTCB, xState, temp_var));
    if
    :: atomic { SELE(_id, temp_var == 0) -> temp_var = NULL_byte };
        taskRESET_READY_PRIORITY(_id, TCB(pxTCB).uxPriority)
    :: atomic { ELSE(_id, temp_var == 0) -> temp_var = NULL_byte }
    fi;

#if (promela_QUEUE_NUMBER > 0)
    if
    :: SELE(_id, listLIST_ITEM_CONTAINER(TCB(pxTCB).ListItems[xEvent]) != NULL_byte) ->
        AWAIT_D(_id, uxListRemove(QLISTs[listLIST_ITEM_CONTAINER(TCB(pxTCB).ListItems[xEvent])], QLIST_SIZE, pxTCB, xEvent, _))
    :: ELSE(_id, listLIST_ITEM_CONTAINER(TCB(pxTCB).ListItems[xEvent]) != NULL_byte)
    fi;
#endif

    AWAIT_D(_id, vListInsertEnd(xSuspendedTaskList, SLIST_SIZE, CID_SUSPENDED_TASK, pxTCB, xState));

    /* Reset the unblock tick in case it referred to the task that is now in
     * the Suspended state */
    prvResetNextTaskUnblockTicks(_id);

    taskEXIT_CRITICAL(_id, temp_var);

    if
    :: atomic { SELE(_id, pxTCB == pxCurrentTCB) -> pxTCB = NULL_byte };
        /* The scheduler is always running */
        AWAIT_D(_id, assert(xSchedulerRunning != false && uxSchedulerSuspended == 0));
        portYIELD_WITHIN_API(_id, temp_var)
    :: atomic { ELSE(_id, pxTCB == pxCurrentTCB) -> pxTCB = NULL_byte }
    fi
}

inline prvTaskIsTaskSuspended(_id, xTask, xReturn)
{
    if
    :: atomic { SELE(_id, listIS_CONTAINED_WITHIN(CID_SUSPENDED_TASK, TCB(xTask).ListItems[xState]) != false) -> assert(xReturn == false) };
        if
        :: SELE(_id, listIS_CONTAINED_WITHIN(CID_PENDING_READY, TCB(xTask).ListItems[xEvent]) == false) ->
            if
            :: SELE(_id, listIS_CONTAINED_WITHIN(NULL_byte, TCB(xTask).ListItems[xEvent]) != false) ->
                AWAIT_D(_id, xReturn = true)
            :: ELSE(_id, listIS_CONTAINED_WITHIN(NULL_byte, TCB(xTask).ListItems[xEvent]) != false)
            fi
        :: ELSE(_id, listIS_CONTAINED_WITHIN(CID_PENDING_READY, TCB(xTask).ListItems[xEvent]) == false)
        fi
    :: atomic { ELSE(_id, listIS_CONTAINED_WITHIN(CID_SUSPENDED_TASK, TCB(xTask).ListItems[xState]) != false) -> assert(xReturn == false) }
    fi
}

inline vTaskResume(_id, xTaskToResume, temp_xReturn, temp_var)
{
    if
    :: SELE(_id, xTaskToResume != pxCurrentTCB && xTaskToResume != NULL_byte) ->
        taskENTER_CRITICAL(_id, temp_var);

        prvTaskIsTaskSuspended(_id, xTaskToResume, temp_xReturn);
        if
        :: atomic { SELE(_id, temp_xReturn != false) -> temp_xReturn = false };
            AWAIT_D(_id, uxListRemove(xSuspendedTaskList, SLIST_SIZE, xTaskToResume, xState, _));
            prvAddTaskToReadyList(_id, xTaskToResume);

            if
            :: SELE(_id, TCB(xTaskToResume).uxPriority >= TCB(pxCurrentTCB).uxPriority) ->
                taskYIELD_IF_USING_PREEMPTION(_id, temp_var)
            :: ELSE(_id, TCB(xTaskToResume).uxPriority >= TCB(pxCurrentTCB).uxPriority)
            fi
        :: atomic { ELSE(_id, temp_xReturn != false) -> assert(temp_xReturn == false) }
        fi;

        taskEXIT_CRITICAL(_id, temp_var)
    :: ELSE(_id, xTaskToResume != pxCurrentTCB && xTaskToResume != NULL_byte)
    fi
}

#endif /* INCLUDE_vTaskSuspend == 1 */

inline vTaskStartScheduler(_id, temp_var)
{
    xTaskCreate_fixed(IDLE_TASK_ID, (tskIDLE_PRIORITY | portPRIVILEGE_BIT));

    portDISABLE_INTERRUPTS(_id, temp_var);
    reset_xTickCount();
    xSchedulerRunning = true;

    xPortStartScheduler()
}

inline vTaskSuspendAll(_id)
{
    AWAIT_D(_id, uxSchedulerSuspended = uxSchedulerSuspended + 1);
}

inline xTaskResumeAll(_id, pxTCB, xAlreadyYielded, temp_var)
{
    AWAIT_D(_id, xAlreadyYielded = false;
        assert(pxTCB == NULL_byte && uxSchedulerSuspended));

    taskENTER_CRITICAL(_id, temp_var);
    AWAIT_D(_id, uxSchedulerSuspended = uxSchedulerSuspended - 1);
    if
    :: SELE(_id, uxSchedulerSuspended == 0) ->
        /* Because no task is delete, uxCurrentNumberOfTasks is greater than zero */
        do
        :: SELE(_id, !listLIST_IS_EMPTY(xPendingReadyList)) ->
            AWAIT_D(_id, pxTCB = listGET_OWNER_OF_HEAD_ENTRY(xPendingReadyList));
            AWAIT_D(_id,
                assert(listLIST_ITEM_CONTAINER(TCB(pxTCB).ListItems[xEvent]) == CID_PENDING_READY);
                uxListRemove(xPendingReadyList, PLIST_SIZE, pxTCB, xEvent, _));
            AWAIT_D(_id,
                assert(listLIST_ITEM_CONTAINER(TCB(pxTCB).ListItems[xState]) == CID_DELAYED_TASK);
                uxListRemove(pxDelayedTaskList, DLIST_SIZE, pxTCB, xState, _));
            prvAddTaskToReadyList(_id, pxTCB);

            if
            :: SELE(_id, TCB(pxTCB).uxPriority >= TCB(pxCurrentTCB).uxPriority) ->
                AWAIT_D(_id, xYieldPending = true)
            :: ELSE(_id, TCB(pxTCB).uxPriority >= TCB(pxCurrentTCB).uxPriority)
            fi
        :: ELSE(_id, !listLIST_IS_EMPTY(xPendingReadyList)) ->
            AWAIT_A(_id, break)
        od;

        if
        :: atomic { SELE(_id, pxTCB != NULL_byte) -> pxTCB = NULL_byte };
            prvResetNextTaskUnblockTicks(_id)
        :: atomic { ELSE(_id, pxTCB != NULL_byte) }
        fi;

        if
        :: atomic { SELE(_id, xPendedTick) -> temp_var = false };
            xTaskIncrementTick(_id, temp_var, pxTCB);
            if
            :: atomic { SELE(_id, temp_var != false) -> temp_var = NULL_byte };
                AWAIT_D(_id, xYieldPending = true)
            :: atomic { ELSE(_id, temp_var != false) -> temp_var = NULL_byte }
            fi;
            AWAIT_D(_id, xPendedTick = 0)
        :: atomic { ELSE(_id, xPendedTick) }
        fi;

        if
        :: SELE(_id, xYieldPending != false) ->
            #if (configUSE_PREEMPTION != 0)
            AWAIT_D(_id, xAlreadyYielded = true);
            #endif
            taskYIELD_IF_USING_PREEMPTION(_id, temp_var)
        :: ELSE(_id, xYieldPending != false)
        fi
    :: ELSE(_id, uxSchedulerSuspended == 0)
    fi;

    taskEXIT_CRITICAL(_id, temp_var)
}

inline xTaskIncrementTick(_id, xSwitchRequired, pxTCB)
{
    AWAIT_A(_id, assert(xSwitchRequired == false && pxTCB == NULL_byte));
    if
    :: SELE(_id, uxSchedulerSuspended == 0) ->
        AWAIT_D(_id, assert(xTickCount < 256);
            xTickCount = (is_xTickCount_active -> xTickCount + 1 : 0)
        );
        if
        :: SELE(_id, is_xTickCount_active && xTickCount >= xNextTaskUnblockTicks) ->
            do
            :: SELE(_id, listLIST_IS_EMPTY(pxDelayedTaskList) == false) ->
                /* The delayed list is not empty. */
                AWAIT_D(_id, pxTCB = listGET_OWNER_OF_HEAD_ENTRY(pxDelayedTaskList));

                if
                :: SELE(_id, xTickCount < listGET_LIST_ITEM_VALUE(TCB(pxTCB).ListItems[xState])) ->
                    /* It is not time to unblock this item yet. Record the item
                     * value in xNextTaskUnblockTicks and clear it. */
                    AWAIT_D(_id, update_xTickCount(); pxTCB = NULL_byte);
                    AWAIT_A(_id, break)
                :: ELSE(_id, xTickCount < listGET_LIST_ITEM_VALUE(TCB(pxTCB).ListItems[xState]))
                fi;

                AWAIT_D(_id,
                    uxListRemove(pxDelayedTaskList, DLIST_SIZE, pxTCB, xState, _);
                    listSET_LIST_ITEM_VALUE(TCB(pxTCB).ListItems[xState], 0)
                );

#if (promela_QUEUE_NUMBER > 0)
                if
                :: SELE(_id, listLIST_ITEM_CONTAINER(TCB(pxTCB).ListItems[xEvent]) != NULL_byte) ->
                    AWAIT_D(_id, uxListRemove(QLISTs[listLIST_ITEM_CONTAINER(TCB(pxTCB).ListItems[xEvent])], QLIST_SIZE, pxTCB, xEvent, _));
                :: ELSE(_id, listLIST_ITEM_CONTAINER(TCB(pxTCB).ListItems[xEvent]) != NULL_byte)
                fi;
#endif

                prvAddTaskToReadyList(_id, pxTCB);

                #if (configUSE_PREEMPTION == 1)
                if
                :: SELE(_id, TCB(pxTCB).uxPriority >= TCB(pxCurrentTCB).uxPriority) ->
                    AWAIT_D(_id, xSwitchRequired = true)
                :: ELSE(_id, TCB(pxTCB).uxPriority >= TCB(pxCurrentTCB).uxPriority)
                fi
                #endif
            :: ELSE(_id, listLIST_IS_EMPTY(pxDelayedTaskList) == false) ->
                /* The delayed list is empty */
                AWAIT_A(_id, reset_xTickCount(); pxTCB = NULL_byte; break)
            od
        :: ELSE(_id, is_xTickCount_active && xTickCount >= xNextTaskUnblockTicks)
        fi;

        #if ((configUSE_PREEMPTION == 1) && (configUSE_TIME_SLICING == 1))
        if
        :: SELE(_id, listLENGTH_IS_EXCEEDING_1(pxReadyTasksLists[TCB(pxCurrentTCB).uxPriority])) ->
            AWAIT_D(_id, xSwitchRequired = true)
        :: ELSE(_id, listLENGTH_IS_EXCEEDING_1(pxReadyTasksLists[TCB(pxCurrentTCB).uxPriority]))
        fi;
        #endif

        #if (configUSE_PREEMPTION == 1)
        if
        :: SELE(_id, xYieldPending != false) ->
            AWAIT_D(_id, xSwitchRequired = true)
        :: ELSE(_id, xYieldPending != false)
        fi
        #endif
    :: ELSE(_id, uxSchedulerSuspended == 0) ->
        AWAIT_D(_id, xPendedTick = 1)
    fi
}

inline vTaskSwitchContext(_id)
{
    if
    :: SELE(_id, uxSchedulerSuspended != 0) ->
        AWAIT_D(_id, xYieldPending = true)
    :: ELSE(_id, uxSchedulerSuspended != 0) ->
        AWAIT_D(_id, xYieldPending = false);
        /* configGENERATE_RUN_TIME_STATS == 0 */
        taskSELECT_HIGHEST_PRIORITY_TASK(_id)
    fi
}

inline vTaskPlaceOnEventList(_id, pxEventList, EventListContainer, xTicksToWait, temp_var)
{
    AWAIT_D(_id, vListInsert(pxEventList, QLIST_SIZE, EventListContainer, pxCurrentTCB, xEvent, temp_var));
    prvAddCurrentTaskToDelayedList(_id, xTicksToWait, true, temp_var)
}

inline xTaskRemoveFromEventList(_id, pxUnblockedTCB, pxEventList, xReturn)
{
    AWAIT_D(_id, assert(pxUnblockedTCB == NULL_byte);
        pxUnblockedTCB = listGET_OWNER_OF_HEAD_ENTRY(pxEventList); assert(pxUnblockedTCB != NULL_byte));
    AWAIT_D(_id, uxListRemove(pxEventList, QLIST_SIZE, pxUnblockedTCB, xEvent, _));

    if
    :: SELE(_id, uxSchedulerSuspended == 0) ->
        AWAIT_D(_id,
            /* Reset xTickCount and xState of pxUnblockedTCB as soon as possible */
            listSET_LIST_ITEM_VALUE(TCB(pxUnblockedTCB).ListItems[xState], 0);
            assert(listLIST_ITEM_CONTAINER(TCB(pxUnblockedTCB).ListItems[xState]) == CID_DELAYED_TASK);
            uxListRemove(pxDelayedTaskList, DLIST_SIZE, pxUnblockedTCB, xState, _);
            if
            :: listLIST_IS_EMPTY(pxDelayedTaskList) ->
                reset_xTickCount()
            :: else
            fi
        );
        prvAddTaskToReadyList(_id, pxUnblockedTCB)
    :: ELSE(_id, uxSchedulerSuspended == 0) ->
        AWAIT_D(_id, vListInsertEnd(xPendingReadyList, PLIST_SIZE, CID_PENDING_READY, pxUnblockedTCB, xEvent))
    fi;

    if
    :: atomic { SELE(_id, TCB(pxUnblockedTCB).uxPriority > TCB(pxCurrentTCB).uxPriority) -> pxUnblockedTCB = NULL_byte };
        AWAIT_D(_id, xReturn = true);
        AWAIT_D(_id, xYieldPending = true)
    :: atomic { ELSE(_id, TCB(pxUnblockedTCB).uxPriority > TCB(pxCurrentTCB).uxPriority) -> pxUnblockedTCB = NULL_byte }
        AWAIT_D(_id, xReturn = false)
    fi
}

inline vTaskMissedYield(_id)
{
    AWAIT_D(_id, xYieldPending = true)
}

inline vTaskIDLE_TASK_BODY(_id, temp_var)
{
    assert(_id == IDLE_TASK_ID);
do
::
    #if (configUSE_PREEMPTION == 0)
        taskYIELD(_id, temp_var);
    #endif

    #if ((configUSE_PREEMPTION == 1) && (configIDLE_SHOULD_YIELD == 1))
        if
        :: SELE(_id, listLENGTH_IS_EXCEEDING_1(pxReadyTasksLists[tskIDLE_PRIORITY])) ->
            taskYIELD(_id, temp_var)
        :: ELSE(_id, listLENGTH_IS_EXCEEDING_1(pxReadyTasksLists[tskIDLE_PRIORITY])) ->
            AWAIT_A(_id, skip) // TODO: redesign SELE and ELSE to set syst_count
        fi;
    #endif
od
}

inline prvResetNextTaskUnblockTicks(_id)
{
    if
    :: SELE(_id, listLIST_IS_EMPTY(pxDelayedTaskList)) ->
        AWAIT_D(_id, reset_xTickCount())
    :: ELSE(_id, listLIST_IS_EMPTY(pxDelayedTaskList)) ->
        AWAIT_D(_id, update_xTickCount())
    fi
}

#if (configUSE_MUTEXES == 1)

inline xTaskPriorityInherit(_id, pxMutexHolder, xReturn, temp_var)
{
    AWAIT_A(_id, assert(xReturn == false && temp_var == NULL_byte));
    if
    :: SELE(_id, pxMutexHolder != NULL_byte) ->
        if
        :: SELE(_id, TCB(pxMutexHolder).uxPriority < TCB(pxCurrentTCB).uxPriority) ->
            if
            :: SELE(_id, (listGET_LIST_ITEM_VALUE(TCB(pxMutexHolder).ListItems[xEvent]) & taskEVENT_LIST_ITEM_VALUE_IN_USE) == 0) ->
                AWAIT_D(_id, listSET_LIST_ITEM_VALUE(TCB(pxMutexHolder).ListItems[xEvent], configMAX_PRIORITIES - TCB(pxCurrentTCB).uxPriority))
            :: ELSE(_id, (listGET_LIST_ITEM_VALUE(TCB(pxMutexHolder).ListItems[xEvent]) & taskEVENT_LIST_ITEM_VALUE_IN_USE) == 0)
            fi;

            if
            :: SELE(_id, listIS_CONTAINED_WITHIN(CID_READY_LISTS + TCB(pxMutexHolder).uxPriority, TCB(pxMutexHolder).ListItems[xState]) != false) ->
                AWAIT_D(_id, uxListRemove(pxReadyTasksLists[TCB(pxMutexHolder).uxPriority], RLIST_SIZE, pxMutexHolder, xState, temp_var));
                if
                :: atomic { SELE(_id, temp_var == 0) -> temp_var = NULL_byte };
                    taskRESET_READY_PRIORITY(_id, TCB(pxMutexHolder).uxPriority)
                :: atomic { ELSE(_id, temp_var == 0) -> temp_var = NULL_byte }
                fi;

                AWAIT_D(_id, TCB(pxMutexHolder).uxPriority = TCB(pxCurrentTCB).uxPriority);
                prvAddTaskToReadyList(_id, pxMutexHolder)
            :: ELSE(_id, listIS_CONTAINED_WITHIN(CID_READY_LISTS + TCB(pxMutexHolder).uxPriority, TCB(pxMutexHolder).ListItems[xState]) != false) ->
                AWAIT_D(_id, TCB(pxMutexHolder).uxPriority = TCB(pxCurrentTCB).uxPriority)
            fi;

            AWAIT_D(_id, xReturn = true)
        :: ELSE(_id, TCB(pxMutexHolder).uxPriority < TCB(pxCurrentTCB).uxPriority) ->
            if
            :: SELE(_id, TCB(pxMutexHolder).uxBasePriority < TCB(pxCurrentTCB).uxPriority) ->
                AWAIT_D(_id, xReturn = true)
            :: ELSE(_id, TCB(pxMutexHolder).uxBasePriority < TCB(pxCurrentTCB).uxPriority)
            fi
        fi
    :: ELSE(_id, pxMutexHolder != NULL_byte)
    fi
}

inline xTaskPriorityDisinherit(_id, pxMutexHolder, xReturn, temp_var)
{
    if
    :: atomic { SELE(_id, pxMutexHolder != NULL_byte) -> assert(xReturn == false) };
        AWAIT_D(_id, assert(pxMutexHolder == pxCurrentTCB && TCB(pxMutexHolder).uxMutexesHeld != NULL_byte);
            TCB(pxMutexHolder).uxMutexesHeld = TCB(pxMutexHolder).uxMutexesHeld - 1);

        if
        :: SELE(_id, TCB(pxMutexHolder).uxPriority != TCB(pxMutexHolder).uxBasePriority) ->
            if
            :: SELE(_id, TCB(pxMutexHolder).uxMutexesHeld == 0) ->
                AWAIT_D(_id,
                    assert(listLIST_ITEM_CONTAINER(TCB(pxMutexHolder).ListItems[xState]) == CID_READY_LISTS + TCB(pxMutexHolder).uxPriority);
                    uxListRemove(pxReadyTasksLists[TCB(pxMutexHolder).uxPriority], RLIST_SIZE, pxMutexHolder, xState, temp_var));
                if
                :: atomic { SELE(_id, temp_var == 0) -> temp_var = NULL_byte };
                    taskRESET_READY_PRIORITY(_id, TCB(pxMutexHolder).uxPriority)
                :: atomic { ELSE(_id, temp_var == 0) -> temp_var = NULL_byte }
                fi;

                AWAIT_D(_id, TCB(pxMutexHolder).uxPriority = TCB(pxMutexHolder).uxBasePriority);

                AWAIT_D(_id, listSET_LIST_ITEM_VALUE(TCB(pxMutexHolder).ListItems[xEvent], configMAX_PRIORITIES - TCB(pxMutexHolder).uxPriority));
                prvAddTaskToReadyList(_id, pxMutexHolder);

                AWAIT_D(_id, xReturn = true)
            :: ELSE(_id, TCB(pxMutexHolder).uxMutexesHeld == 0)
            fi
        :: ELSE(_id, TCB(pxMutexHolder).uxPriority != TCB(pxMutexHolder).uxBasePriority)
        fi
    :: atomic { ELSE(_id, pxMutexHolder != NULL_byte) -> assert(xReturn == false) }
    fi
}

inline pvTaskIncrementMutexHeldCount(_id, pxMutexHolder)
{
    if
    :: SELE(_id, pxCurrentTCB != NULL_byte) ->
        AWAIT_D(_id, TCB(pxCurrentTCB).uxMutexesHeld = TCB(pxCurrentTCB).uxMutexesHeld + 1)
    :: ELSE(_id, pxCurrentTCB != NULL_byte)
    fi;

    AWAIT_D(_id, pxMutexHolder = pxCurrentTCB)
}

inline vTaskPriorityDisinheritAfterTimeout(_id, pxMutexHolder, uxHighestPriorityWaitingTask, uxPriorityUsedOnEntry)
{
    if
    :: SELE(_id, pxMutexHolder != NULL_byte) ->
        AWAIT_A(_id, assert(TCB(pxMutexHolder).uxMutexesHeld != NULL_byte));
        /* The variable uxHighestPriorityWaitingTask will not be referenced at
         * the following of the next statement. To reduce the usage of temporary
         * variables, we reassign the uxHighestPriorityWaitingTask variable. */
        if
        :: SELE(_id, TCB(pxMutexHolder).uxBasePriority < uxHighestPriorityWaitingTask) ->
            AWAIT_D(_id, uxHighestPriorityWaitingTask /* uxPriorityToUse */ = uxHighestPriorityWaitingTask)
        :: ELSE(_id, TCB(pxMutexHolder).uxBasePriority < uxHighestPriorityWaitingTask) ->
            AWAIT_D(_id, uxHighestPriorityWaitingTask /* uxPriorityToUse */ = TCB(pxMutexHolder).uxBasePriority)
        fi;

        if
        :: atomic { SELE(_id, TCB(pxMutexHolder).uxPriority != uxHighestPriorityWaitingTask /* uxPriorityToUse */) -> assert(uxHighestPriorityWaitingTask != NULL_byte) };
            if
            :: SELE(_id, TCB(pxMutexHolder).uxMutexesHeld == 1 /* uxOnlyOneMutexHeld */) ->
                AWAIT_D(_id, assert(pxMutexHolder != pxCurrentTCB && uxPriorityUsedOnEntry == NULL_byte);
                    uxPriorityUsedOnEntry = TCB(pxMutexHolder).uxPriority);
                AWAIT_D(_id, TCB(pxMutexHolder).uxPriority = uxHighestPriorityWaitingTask /* uxPriorityToUse */);

                if
                :: SELE(_id, (listGET_LIST_ITEM_VALUE(TCB(pxMutexHolder).ListItems[xEvent]) & taskEVENT_LIST_ITEM_VALUE_IN_USE) == 0) ->
                    AWAIT_D(_id, listSET_LIST_ITEM_VALUE(TCB(pxMutexHolder).ListItems[xEvent], configMAX_PRIORITIES - uxHighestPriorityWaitingTask/* uxPriorityToUse */);
                        uxHighestPriorityWaitingTask = NULL_byte /* reset variable */)
                :: ELSE(_id, (listGET_LIST_ITEM_VALUE(TCB(pxMutexHolder).ListItems[xEvent]) & taskEVENT_LIST_ITEM_VALUE_IN_USE) == 0)
                fi;

                if
                :: atomic { SELE(_id, listIS_CONTAINED_WITHIN(CID_READY_LISTS + uxPriorityUsedOnEntry, TCB(pxMutexHolder).ListItems[xState])) ->
                    assert(uxPriorityUsedOnEntry != NULL_byte) };
                    AWAIT_D(_id, uxListRemove(pxReadyTasksLists[uxPriorityUsedOnEntry], RLIST_SIZE, pxMutexHolder, xState, _));
                    if
                    :: atomic { SELE(_id, listLIST_IS_EMPTY(pxReadyTasksLists[uxPriorityUsedOnEntry])) -> uxPriorityUsedOnEntry = NULL_byte };
                        taskRECORD_READY_PRIORITY(_id, TCB(pxMutexHolder).uxPriority)
                    :: atomic { ELSE(_id, listLIST_IS_EMPTY(pxReadyTasksLists[uxPriorityUsedOnEntry])) -> uxPriorityUsedOnEntry = NULL_byte }
                    fi;

                    prvAddTaskToReadyList(_id, pxMutexHolder)
                :: atomic { ELSE(_id, listIS_CONTAINED_WITHIN(CID_READY_LISTS + uxPriorityUsedOnEntry, TCB(pxMutexHolder).ListItems[xState])) ->
                    uxPriorityUsedOnEntry = NULL_byte }
                fi
            :: ELSE(_id, TCB(pxMutexHolder).uxMutexesHeld == 1 /* uxOnlyOneMutexHeld */)
            fi
        :: atomic { ELSE(_id, TCB(pxMutexHolder).uxPriority != uxHighestPriorityWaitingTask /* uxPriorityToUse */) -> uxHighestPriorityWaitingTask = NULL_byte }
        fi
    :: ELSE(_id, pxMutexHolder != NULL_byte)
    fi
}

#endif /* configUSE_MUTEXES */

inline prvAddCurrentTaskToDelayedList(_id, xTicksToWait, xCanBlockIndefinitely, temp_var)
{
    AWAIT_D(_id,
        assert(listLIST_ITEM_CONTAINER(TCB(pxCurrentTCB).ListItems[xState]) == CID_READY_LISTS + TCB(pxCurrentTCB).uxPriority);
        uxListRemove(pxReadyTasksLists[TCB(pxCurrentTCB).uxPriority], RLIST_SIZE, pxCurrentTCB, xState, temp_var));
    if
    :: atomic { SELE(_id, temp_var == 0) -> temp_var = NULL_byte };
        portRESET_READY_PRIORITY(_id, TCB(now.pxCurrentTCB).uxPriority, uxTopReadyPriority)
    :: atomic { ELSE(_id, temp_var == 0) -> temp_var = NULL_byte }
    fi;

#if (INCLUDE_vTaskSuspend == 1)
    if
    :: SELE(_id, xTicksToWait == portMAX_DELAY && xCanBlockIndefinitely != false) ->
        AWAIT_D(_id, vListInsertEnd(xSuspendedTaskList, SLIST_SIZE, CID_SUSPENDED_TASK, pxCurrentTCB, xState))
    :: ELSE(_id, xTicksToWait == portMAX_DELAY && xCanBlockIndefinitely != false) ->
        AWAIT_D(_id,
            assert(xTicksToWait < 256 && listGET_LIST_ITEM_VALUE(TCB(pxCurrentTCB).ListItems[xState]) == 0);
            listSET_LIST_ITEM_VALUE(TCB(pxCurrentTCB).ListItems[xState], xTicksToWait));
        AWAIT_D(_id,
            if
            :: is_xTickCount_active ->
                assert(!listLIST_IS_EMPTY(pxDelayedTaskList));
                update_xTickCount()
            :: else ->
                assert(listLIST_IS_EMPTY(pxDelayedTaskList));
                is_xTickCount_active = true
            fi;
            vListInsert(pxDelayedTaskList, DLIST_SIZE, CID_DELAYED_TASK, pxCurrentTCB, xState, temp_var))
    fi;
#else
    AWAIT_D(_id,
        assert(xTicksToWait < 256 && listGET_LIST_ITEM_VALUE(TCB(pxCurrentTCB).ListItems[xState]) == 0);
        listSET_LIST_ITEM_VALUE(TCB(pxCurrentTCB).ListItems[xState], xTicksToWait));
    AWAIT_D(_id,
        if
        :: is_xTickCount_active ->
            assert(!listLIST_IS_EMPTY(pxDelayedTaskList));
            update_xTickCount();
        :: else ->
            assert(listLIST_IS_EMPTY(pxDelayedTaskList));
            is_xTickCount_active = true
        fi;
        vListInsert(pxDelayedTaskList, DLIST_SIZE, CID_DELAYED_TASK, pxCurrentTCB, xState, temp_var));
#endif
}

#endif
