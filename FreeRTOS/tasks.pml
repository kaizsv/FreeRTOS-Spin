#ifndef _TASKS_
#define _TASKS_

#include "../FreeRTOS.pml"
#include "list.pml"

#define tskIDLE_PRIORITY        0
#define taskYIELD(_id, temp_var)     portYIELD(_id, temp_var)

#define taskENTER_CRITICAL(_id, temp_var)    portENTER_CRITICAL(_id, temp_var)
#define taskEXIT_CRITICAL(_id, temp_var)     portEXIT_CRITICAL(_id, temp_var)

#if (configUSE_PREEMPTION == 0)
    #define taskYIELD_IF_USING_PREEMPTION(_id, temp_var)
#else
    // portYIELD_WITHIN_API(_id, temp_var)
    #define taskYIELD_IF_USING_PREEMPTION(_id, temp_var) portYIELD_DETERMINISTIC(_id, temp_var)
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
    :: SELE2_AS(_id, Priority > uxTopReadyPriority);
        AWAIT_DS(_id, uxTopReadyPriority = Priority)
    :: ELSE2_AS(_id, Priority > uxTopReadyPriority)
    fi
}

inline taskSELECT_HIGHEST_PRIORITY_TASK(_id)
{
    AWAIT_DS(_id, idx = uxTopReadyPriority);
    do
    :: SELE2_AS(_id, listLIST_IS_EMPTY(pxReadyTasksLists[idx]));
        AWAIT_DS(_id, assert(idx > 0); idx = idx - 1)
    :: ELSE3_AS(_id, listLIST_IS_EMPTY(pxReadyTasksLists[idx]), break);
    od;

    listGET_OWNER_OF_NEXT_ENTRY(_id, pxCurrentTCB, pxReadyTasksLists[idx], RLIST_SIZE);
    AWAIT_DS(_id, uxTopReadyPriority = idx; idx = 0)
}

    #define taskRESET_READY_PRIORITY(_id, uxPriority)
    #define portRESET_READY_PRIORITY(_id, uxPriority, uxTopReadyPriority)
#else
// TODO: configUSE_PORT_OPTIMISED_TASK_SELECTION
#endif

#if 0
    Because vTaskEndScheduler is not established, xSchedulerRunning
    is always true after starting the scheduler. To check whether
    the scheduler is started, the variable EP is a sound judgment.
#endif

#define xIsSchedulerRunning (EP != NULL_byte)

byte uxTopReadyPriority = tskIDLE_PRIORITY;
bit xPendedTicks = 0;
bool xYieldPending = false;
byte uxSchedulerSuspended = 0;

byte xTickCount = 0;
bool is_xTickCount_active = false;

#define xNextTaskUnblockTicks   \
    listGET_LIST_ITEM_VALUE(TCB(listGET_OWNER_OF_HEAD_ENTRY(pxDelayedTaskList)).ListItems[xState])

#define reset_xTickCount()  \
    is_xTickCount_active = false; xTickCount = 0

/* 255 delayed ticks represents the task will in Delayed or Suspended List
permanently. 254 delayed ticks ensures the task is reported as Delayed state
rather than the Suspended. Both delayed tick count are free from decreas. */
#define update_xTickCount() \
    for (idx: 0 .. (DLIST_SIZE - 1)) { \
        if \
        :: !listPOINTER_IS_NULL(pxDelayedTaskList.ps[idx]) && \
           (listGET_LIST_ITEM_VALUE(pxOrdinalListItem(pxDelayedTaskList, idx)) < 254) -> \
            assert(listGET_LIST_ITEM_VALUE(pxOrdinalListItem(pxDelayedTaskList, idx)) > xTickCount); \
            listSET_LIST_ITEM_VALUE(pxOrdinalListItem(pxDelayedTaskList, idx), \
                listGET_LIST_ITEM_VALUE(pxOrdinalListItem(pxDelayedTaskList, idx)) - xTickCount) \
        :: else -> break \
        fi \
    } \
    idx = 0; \
    assert(xNextTaskUnblockTicks > 0); \
    xTickCount = 0

#define uxCurrentNumberOfTasks promela_TASK_NUMBER + 1 /* user tasks and the idle */

inline prvAddTaskToReadyList(_id, pxTCB)
{
    taskRECORD_READY_PRIORITY(_id, TCB(pxTCB).uxPriority);
    AWAIT_DS(_id, vListInsertEnd_pxIndex(pxReadyTasksLists[TCB(pxTCB).uxPriority], RLIST_SIZE, CID_READY_LISTS + TCB(pxTCB).uxPriority, pxTCB, xState))
}

inline prvAddTaskToReadyList_fixed(pxTCB)
{
    uxTopReadyPriority = (TCB(pxTCB).uxPriority > uxTopReadyPriority -> TCB(pxTCB).uxPriority : uxTopReadyPriority);
    vListInsertEnd_pxIndex(pxReadyTasksLists[TCB(pxTCB).uxPriority], RLIST_SIZE, CID_READY_LISTS + TCB(pxTCB).uxPriority, pxTCB, xState)
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
        vListInitialise_pxIndex(pxReadyTasksLists[idx2], RLIST_SIZE);
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
    listSET_LIST_ITEM_VALUE(TCB(pcName).ListItems[xEvent], configMAX_PRIORITIES - (Priority));

    /* prvAddNewTaskToReadyList */
    if
    :: pxCurrentTCB == NULL_byte ->
        pxCurrentTCB = pcName
        /* ensure the list is initialized */
        assert(listLIST_IS_EMPTY(pxReadyTasksLists[0]));
    :: else ->
        pxCurrentTCB = (
            (!xIsSchedulerRunning) &&
            (TCB(pxCurrentTCB).uxPriority <= TCB(pcName).uxPriority) ->
                pcName : pxCurrentTCB)
    fi;

    prvAddTaskToReadyList_fixed(pcName);

    /* yield the task if the assertion violated. */
    assert(!((xIsSchedulerRunning) && (TCB(pxCurrentTCB).uxPriority < TCB(pcName).uxPriority)))
}

#if (INCLUDE_vTaskDelay == 1)

inline vTaskDelay(_id, xTicksToDelay, xAlreadyYielded, temp_var, temp_var2)
{
    if
    :: SELE3(_id, xTicksToDelay > 0, assert(uxSchedulerSuspended == 0));
        vTaskSuspendAll(_id);
        prvAddCurrentTaskToDelayedList(_id, xTicksToDelay, false, temp_var);
        xTaskResumeAll(_id, temp_var, xAlreadyYielded, temp_var2)
    :: ELSE3(_id, xTicksToDelay > 0, assert(xAlreadyYielded == false))
    fi;

    if
    :: SELE2(_id, xAlreadyYielded == false);
        portYIELD_WITHIN_API(_id, temp_var)
    :: ELSE3(_id, xAlreadyYielded == false, xAlreadyYielded = false)
    fi
}

#endif

#if (INCLUDE_uxTaskPriorityGet == 1)

#define uxTaskPriorityGet(xTask) TCB(prvGetTCBFromHandle(xTask)).uxPriority

#endif /* INCLUDE_uxTaskPriorityGet */

#if (INCLUDE_vTaskPrioritySet == 1)

#define uxCurrentBasePriority   temp_Priority
#define uxPriorityUsedOnEntry   temp_Priority

inline vTaskPrioritySet(_id, xTask, uxNewPriority, pxTCB, xYieldRequired, temp_var, temp_Priority)
{
    AWAIT(_id, assert(uxNewPriority < configMAX_PRIORITIES && xYieldRequired == false && temp_var == NULL_byte));

    taskENTER_CRITICAL(_id, temp_var);
    AWAIT_DS(_id, assert(pxTCB == NULL_byte); pxTCB = prvGetTCBFromHandle(xTask));

#if (configUSE_MUTEXES == 1)
    AWAIT_DS(_id, assert(uxCurrentBasePriority == NULL_byte); uxCurrentBasePriority = TCB(pxTCB).uxBasePriority);
#else
    AWAIT_DS(_id, assert(uxCurrentBasePriority == NULL_byte); uxCurrentBasePriority = TCB(pxTCB).uxPriority);
#endif

    if
    :: SELE2_AS(_id, uxCurrentBasePriority != uxNewPriority);
        if
        :: SELE2_AS(_id, uxNewPriority > uxCurrentBasePriority);
            if
            :: SELE2_AS(_id, pxTCB != pxCurrentTCB && uxNewPriority >= TCB(pxCurrentTCB).uxPriority);
                AWAIT_DS(_id, xYieldRequired = true)
            :: ELSE2_AS(_id, pxTCB != pxCurrentTCB && uxNewPriority >= TCB(pxCurrentTCB).uxPriority)
            fi
        :: ELSE2_AS(_id, uxNewPriority > uxCurrentBasePriority);
            if
            :: SELE2_AS(_id, pxTCB == pxCurrentTCB);
                AWAIT_DS(_id, xYieldRequired = true)
            :: ELSE2_AS(_id, pxTCB == pxCurrentTCB)
            fi
        fi;

        AWAIT_DS(_id, uxPriorityUsedOnEntry = TCB(pxTCB).uxPriority);

#if (configUSE_MUTEXES == 1)
        if
        :: SELE2_AS(_id, TCB(pxTCB).uxBasePriority == TCB(pxTCB).uxPriority);
            AWAIT_DS(_id, TCB(pxTCB).uxPriority = uxNewPriority)
        :: ELSE2_AS(_id, TCB(pxTCB).uxBasePriority == TCB(pxTCB).uxPriority)
        fi;
        AWAIT_DS(_id, TCB(pxTCB).uxBasePriority = uxNewPriority);
#else
        AWAIT_DS(_id, TCB(pxTCB).uxPriority = uxNewPriority);
#endif
        if
        :: SELE2_AS(_id, (listGET_LIST_ITEM_VALUE(TCB(pxTCB).ListItems[xEvent]) & taskEVENT_LIST_ITEM_VALUE_IN_USE) == 0);
            AWAIT_DS(_id, listSET_LIST_ITEM_VALUE(TCB(pxTCB).ListItems[xEvent], configMAX_PRIORITIES - (uxNewPriority)))
        :: ELSE2_AS(_id, (listGET_LIST_ITEM_VALUE(TCB(pxTCB).ListItems[xEvent]) & taskEVENT_LIST_ITEM_VALUE_IN_USE) == 0)
        fi;

        if
        :: SELE2_AS(_id, listIS_CONTAINED_WITHIN(CID_READY_LISTS + uxPriorityUsedOnEntry, TCB(pxTCB).ListItems[xState]) != false);
            AWAIT_DS(_id, uxListRemove_pxIndex(pxReadyTasksLists[uxPriorityUsedOnEntry], RLIST_SIZE, pxTCB, xState));
            if
            :: SELE2_AS(_id, listLIST_IS_EMPTY(pxReadyTasksLists[uxPriorityUsedOnEntry]));
                portRESET_READY_PRIORITY(_id, uxPriorityUsedOnEntry, uxTopReadyPriority)
            :: ELSE2_AS(_id, listLIST_IS_EMPTY(pxReadyTasksLists[uxPriorityUsedOnEntry]))
            fi;
            prvAddTaskToReadyList(_id, pxTCB)
        :: ELSE2_AS(_id, listIS_CONTAINED_WITHIN(CID_READY_LISTS + uxPriorityUsedOnEntry, TCB(pxTCB).ListItems[xState]) != false)
        fi;

        if
        :: SELE3_AS(_id, xYieldRequired != false, xYieldRequired = false; pxTCB = NULL_byte; temp_Priority = NULL_byte);
            taskYIELD_IF_USING_PREEMPTION(_id, temp_var)
        :: ELSE3_AS(_id, xYieldRequired != false, pxTCB = NULL_byte; temp_Priority = NULL_byte)
        fi
    :: ELSE3_AS(_id, uxCurrentBasePriority != uxNewPriority, pxTCB = NULL_byte; temp_Priority = NULL_byte)
    fi;
    taskEXIT_CRITICAL(_id, temp_var)
}

#endif /* INCLUDE_vTaskPrioritySet */

#if (INCLUDE_vTaskSuspend == 1)

inline vTaskSuspend(_id, xTaskToSuspend, pxTCB, temp_var)
{
    taskENTER_CRITICAL(_id, temp_var);
    AWAIT_DS(_id, assert(pxTCB == NULL_byte); pxTCB = prvGetTCBFromHandle(xTaskToSuspend));

    AWAIT_DS(_id,
        assert(listLIST_ITEM_CONTAINER(TCB(pxTCB).ListItems[xState]) == CID_READY_LISTS + TCB(pxTCB).uxPriority);
        uxListRemove_pxIndex(pxReadyTasksLists[TCB(pxTCB).uxPriority], RLIST_SIZE, pxTCB, xState));
    if
    :: SELE2_AS(_id, listLIST_IS_EMPTY(pxReadyTasksLists[TCB(pxTCB).uxPriority]));
        taskRESET_READY_PRIORITY(_id, TCB(pxTCB).uxPriority)
    :: ELSE2_AS(_id, listLIST_IS_EMPTY(pxReadyTasksLists[TCB(pxTCB).uxPriority]))
    fi;

#if (promela_QUEUE_NUMBER > 0)
    if
    :: SELE2_AS(_id, listLIST_ITEM_CONTAINER(TCB(pxTCB).ListItems[xEvent]) != NULL_byte);
        AWAIT_DS(_id, uxListRemove(QLISTs[listLIST_ITEM_CONTAINER(TCB(pxTCB).ListItems[xEvent])], QLIST_SIZE, pxTCB, xEvent))
    :: ELSE2_AS(_id, listLIST_ITEM_CONTAINER(TCB(pxTCB).ListItems[xEvent]) != NULL_byte)
    fi;
#endif

    AWAIT_DS(_id, vListInsertEnd(xSuspendedTaskList, SLIST_SIZE, CID_SUSPENDED_TASK, pxTCB, xState));

    taskEXIT_CRITICAL(_id, temp_var);

    taskENTER_CRITICAL(_id, temp_var);
    /* Reset the unblock tick in case it referred to the task that is now in
     * the Suspended state */
    prvResetNextTaskUnblockTicks(_id);
    taskEXIT_CRITICAL(_id, temp_var);

    if
    :: SELE3(_id, pxTCB == pxCurrentTCB, pxTCB = NULL_byte);
        /* The scheduler is always running */
        AWAIT(_id, assert(xIsSchedulerRunning && uxSchedulerSuspended == 0));
        portYIELD_WITHIN_API(_id, temp_var)
    :: ELSE3(_id, pxTCB == pxCurrentTCB, pxTCB = NULL_byte)
    fi
}

inline prvTaskIsTaskSuspended(_id, xTask, xReturn)
{
    if
    :: SELE2_AS(_id, listIS_CONTAINED_WITHIN(CID_SUSPENDED_TASK, TCB(xTask).ListItems[xState]) != false);
        if
        :: SELE2_AS(_id, listIS_CONTAINED_WITHIN(CID_PENDING_READY, TCB(xTask).ListItems[xEvent]) == false);
            if
            :: SELE2_AS(_id, listIS_CONTAINED_WITHIN(NULL_byte, TCB(xTask).ListItems[xEvent]) != false);
                AWAIT_DS(_id, assert(xReturn == false); xReturn = true)
            :: ELSE2_AS(_id, listIS_CONTAINED_WITHIN(NULL_byte, TCB(xTask).ListItems[xEvent]) != false)
            fi
        :: ELSE2_AS(_id, listIS_CONTAINED_WITHIN(CID_PENDING_READY, TCB(xTask).ListItems[xEvent]) == false)
        fi
    :: ELSE3_AS(_id, listIS_CONTAINED_WITHIN(CID_SUSPENDED_TASK, TCB(xTask).ListItems[xState]) != false, assert(xReturn == false))
    fi
}

inline vTaskResume(_id, xTaskToResume, temp_xReturn, temp_var)
{
    if
    :: SELE2(_id, xTaskToResume != pxCurrentTCB && xTaskToResume != NULL_byte);
        taskENTER_CRITICAL(_id, temp_var);

        prvTaskIsTaskSuspended(_id, xTaskToResume, temp_xReturn);
        if
        :: SELE3_AS(_id, temp_xReturn != false, temp_xReturn = false);
            AWAIT_DS(_id, uxListRemove(xSuspendedTaskList, SLIST_SIZE, xTaskToResume, xState));
            prvAddTaskToReadyList(_id, xTaskToResume);

            if
            :: SELE2_AS(_id, TCB(xTaskToResume).uxPriority >= TCB(pxCurrentTCB).uxPriority);
                taskYIELD_IF_USING_PREEMPTION(_id, temp_var)
            :: ELSE2_AS(_id, TCB(xTaskToResume).uxPriority >= TCB(pxCurrentTCB).uxPriority)
            fi
        :: ELSE2_AS(_id, temp_xReturn != false)
        fi;

        taskEXIT_CRITICAL(_id, temp_var)
    :: ELSE2(_id, xTaskToResume != pxCurrentTCB && xTaskToResume != NULL_byte)
    fi
}

#endif /* INCLUDE_vTaskSuspend == 1 */

inline vTaskStartScheduler(_id, temp_var)
{
    xTaskCreate_fixed(IDLE_TASK_ID, (tskIDLE_PRIORITY | portPRIVILEGE_BIT));

    portDISABLE_INTERRUPTS(_id, temp_var);
    reset_xTickCount();

    xPortStartScheduler()
}

inline vTaskSuspendAll(_id)
{
    AWAIT(_id, uxSchedulerSuspended = uxSchedulerSuspended + 1);
}

inline xTaskResumeAll(_id, pxTCB, xAlreadyYielded, temp_var)
{
    AWAIT(_id, xAlreadyYielded = false;
        assert(pxTCB == NULL_byte && uxSchedulerSuspended));

    taskENTER_CRITICAL(_id, temp_var);
    AWAIT_DS(_id, uxSchedulerSuspended = uxSchedulerSuspended - 1);
    if
    :: SELE2_AS(_id, uxSchedulerSuspended == 0);
        /* Because no task is delete, uxCurrentNumberOfTasks is greater than zero */
        do
        :: SELE2_AS(_id, !listLIST_IS_EMPTY(xPendingReadyList));
            AWAIT_DS(_id, pxTCB = listGET_OWNER_OF_HEAD_ENTRY(xPendingReadyList));
            AWAIT_DS(_id,
                assert(listLIST_ITEM_CONTAINER(TCB(pxTCB).ListItems[xEvent]) == CID_PENDING_READY);
                uxListRemove(xPendingReadyList, PLIST_SIZE, pxTCB, xEvent));
            AWAIT_DS(_id,
                assert(listLIST_ITEM_CONTAINER(TCB(pxTCB).ListItems[xState]) == CID_DELAYED_TASK);
                uxListRemove(pxDelayedTaskList, DLIST_SIZE, pxTCB, xState));
            prvAddTaskToReadyList(_id, pxTCB);

            if
            :: SELE2_AS(_id, TCB(pxTCB).uxPriority >= TCB(pxCurrentTCB).uxPriority);
                AWAIT_DS(_id, xYieldPending = true)
            :: ELSE2_AS(_id, TCB(pxTCB).uxPriority >= TCB(pxCurrentTCB).uxPriority)
            fi
        :: ELSE3_AS(_id, !listLIST_IS_EMPTY(xPendingReadyList), break)
        od;

        if
        :: SELE3_AS(_id, pxTCB != NULL_byte, pxTCB = NULL_byte);
            prvResetNextTaskUnblockTicks(_id)
        :: ELSE2_AS(_id, pxTCB != NULL_byte)
        fi;

        if
        :: SELE2_AS(_id, xPendedTicks);
            // xTaskIncrementTick
            if
            :: SELE3_AS(_id, uxSchedulerSuspended == 0, assert(pxTCB == NULL_byte));
                AWAIT_DS(_id, assert(xTickCount < 254);
                    xTickCount = (is_xTickCount_active -> xTickCount + 1 : 0));
                if
                :: SELE2_AS(_id, is_xTickCount_active && xTickCount >= xNextTaskUnblockTicks);
                    do
                    :: SELE2_AS(_id, listLIST_IS_EMPTY(pxDelayedTaskList) == false);
                        AWAIT_DS(_id, pxTCB = listGET_OWNER_OF_HEAD_ENTRY(pxDelayedTaskList));
                        if
                        :: SELE2_AS(_id, xTickCount < listGET_LIST_ITEM_VALUE(TCB(pxTCB).ListItems[xState]));
                            AWAIT_DS(_id, update_xTickCount(); pxTCB = NULL_byte);
                            AWAIT_AS(_id, break)
                        :: ELSE2_AS(_id, xTickCount < listGET_LIST_ITEM_VALUE(TCB(pxTCB).ListItems[xState]))
                        fi;
                        AWAIT_DS(_id,
                            uxListRemove(pxDelayedTaskList, DLIST_SIZE, pxTCB, xState);
                            listSET_LIST_ITEM_VALUE(TCB(pxTCB).ListItems[xState], 0));
#if (promela_QUEUE_NUMBER > 0)
                        if
                        :: SELE2_AS(_id, listLIST_ITEM_CONTAINER(TCB(pxTCB).ListItems[xEvent]) != NULL_byte);
                            AWAIT_DS(_id, uxListRemove(QLISTs[listLIST_ITEM_CONTAINER(TCB(pxTCB).ListItems[xEvent])], QLIST_SIZE, pxTCB, xEvent));
                        :: ELSE2_AS(_id, listLIST_ITEM_CONTAINER(TCB(pxTCB).ListItems[xEvent]) != NULL_byte)
                        fi;
#endif
                        prvAddTaskToReadyList(_id, pxTCB);
                        #if (configUSE_PREEMPTION == 1)
                        if
                        :: SELE2_AS(_id, TCB(pxTCB).uxPriority >= TCB(pxCurrentTCB).uxPriority);
                            AWAIT_DS(_id, xYieldPending = true)
                        :: ELSE2_AS(_id, TCB(pxTCB).uxPriority >= TCB(pxCurrentTCB).uxPriority)
                        fi
                        #endif
                    :: ELSE2_AS(_id, listLIST_IS_EMPTY(pxDelayedTaskList) == false);
                        AWAIT_AS(_id, reset_xTickCount(); pxTCB = NULL_byte; break)
                    od;
                :: ELSE2_AS(_id, is_xTickCount_active && xTickCount >= xNextTaskUnblockTicks);
                fi;
                #if ((configUSE_PREEMPTION == 1) && (configUSE_TIME_SLICING == 1))
                if
                :: SELE2_AS(_id, listLENGTH_IS_EXCEEDING_1(pxReadyTasksLists[TCB(pxCurrentTCB).uxPriority]));
                    AWAIT_DS(_id, xYieldPending = true)
                :: ELSE2_AS(_id, listLENGTH_IS_EXCEEDING_1(pxReadyTasksLists[TCB(pxCurrentTCB).uxPriority]))
                fi;
                #endif
                /* Because xPendedTicks is still positive, vApplicationTickHook
                 * is not executed. */
            :: ELSE2_AS(_id, uxSchedulerSuspended == 0)
            fi;
            // end xTaskIncrementTick
            AWAIT_AS(_id, xPendedTicks = 0)
        :: ELSE2_AS(_id, xPendedTicks)
        fi;

        if
        :: SELE2_AS(_id, xYieldPending != false);
            #if (configUSE_PREEMPTION != 0)
            AWAIT_DS(_id, xAlreadyYielded = true);
            #endif
            taskYIELD_IF_USING_PREEMPTION(_id, temp_var)
        :: ELSE2(_id, xYieldPending != false)
        fi
    :: ELSE2_AS(_id, uxSchedulerSuspended == 0)
    fi;

    taskEXIT_CRITICAL(_id, temp_var)
}

inline xTaskIncrementTick(_id, xSwitchRequired, pxTCB)
{
    if
    :: SELE3_AS(_id, uxSchedulerSuspended == 0, assert(xSwitchRequired == false && pxTCB == NULL_byte));
        AWAIT_DS(_id, assert(xTickCount < 254);
            xTickCount = (is_xTickCount_active -> xTickCount + 1 : 0)
        );
        if
        :: SELE2_AS(_id, is_xTickCount_active && xTickCount >= xNextTaskUnblockTicks);
            do
            :: SELE2_AS(_id, listLIST_IS_EMPTY(pxDelayedTaskList) == false);
                /* The delayed list is not empty. */
                AWAIT_DS(_id, pxTCB = listGET_OWNER_OF_HEAD_ENTRY(pxDelayedTaskList));

                if
                :: SELE2_AS(_id, xTickCount < listGET_LIST_ITEM_VALUE(TCB(pxTCB).ListItems[xState]));
                    /* It is not time to unblock this item yet. Record the item
                     * value in xNextTaskUnblockTicks and clear it. */
                    AWAIT_DS(_id, update_xTickCount(); pxTCB = NULL_byte);
                    AWAIT_AS(_id, break)
                :: ELSE2_AS(_id, xTickCount < listGET_LIST_ITEM_VALUE(TCB(pxTCB).ListItems[xState]))
                fi;

                AWAIT_DS(_id,
                    uxListRemove(pxDelayedTaskList, DLIST_SIZE, pxTCB, xState);
                    listSET_LIST_ITEM_VALUE(TCB(pxTCB).ListItems[xState], 0)
                );

#if (promela_QUEUE_NUMBER > 0)
                if
                :: SELE2_AS(_id, listLIST_ITEM_CONTAINER(TCB(pxTCB).ListItems[xEvent]) != NULL_byte);
                    AWAIT_DS(_id, uxListRemove(QLISTs[listLIST_ITEM_CONTAINER(TCB(pxTCB).ListItems[xEvent])], QLIST_SIZE, pxTCB, xEvent));
                :: ELSE2_AS(_id, listLIST_ITEM_CONTAINER(TCB(pxTCB).ListItems[xEvent]) != NULL_byte)
                fi;
#endif

                prvAddTaskToReadyList(_id, pxTCB);

                #if (configUSE_PREEMPTION == 1)
                if
                :: SELE2_AS(_id, TCB(pxTCB).uxPriority >= TCB(pxCurrentTCB).uxPriority);
                    AWAIT_DS(_id, xSwitchRequired = true)
                :: ELSE2_AS(_id, TCB(pxTCB).uxPriority >= TCB(pxCurrentTCB).uxPriority)
                fi
                #endif
            :: ELSE2_AS(_id, listLIST_IS_EMPTY(pxDelayedTaskList) == false);
                /* The delayed list is empty */
                AWAIT_AS(_id, reset_xTickCount(); pxTCB = NULL_byte; break)
            od
        :: ELSE2_AS(_id, is_xTickCount_active && xTickCount >= xNextTaskUnblockTicks)
        fi;

        #if ((configUSE_PREEMPTION == 1) && (configUSE_TIME_SLICING == 1))
        if
        :: SELE2_AS(_id, listLENGTH_IS_EXCEEDING_1(pxReadyTasksLists[TCB(pxCurrentTCB).uxPriority]));
            AWAIT_DS(_id, xSwitchRequired = true)
        :: ELSE2_AS(_id, listLENGTH_IS_EXCEEDING_1(pxReadyTasksLists[TCB(pxCurrentTCB).uxPriority]))
        fi;
        #endif

        #if (configUSE_TICK_HOOK == 1)
            if
            :: SELE2_AS(_id, xPendedTicks == 0);
                vApplicationTickHook();
            :: ELSE2_AS(_id, xPendedTicks == 0);
            fi;
        #endif

        #if (configUSE_PREEMPTION == 1)
        if
        :: SELE2_AS(_id, xYieldPending != false);
            AWAIT_DS(_id, xSwitchRequired = true)
        :: ELSE2_AS(_id, xYieldPending != false)
        fi
        #endif
    :: ELSE3_AS(_id, uxSchedulerSuspended == 0, assert(xSwitchRequired == false && pxTCB == NULL_byte));
        AWAIT_DS(_id, xPendedTicks = 1);
    fi
}

inline vTaskSwitchContext(_id)
{
    if
    :: SELE2_AS(_id, uxSchedulerSuspended != 0);
        AWAIT_DS(_id, xYieldPending = true)
    :: ELSE2_AS(_id, uxSchedulerSuspended != 0);
        AWAIT_DS(_id, xYieldPending = false);
        /* configGENERATE_RUN_TIME_STATS == 0 */
        taskSELECT_HIGHEST_PRIORITY_TASK(_id)
    fi
}

// TODO: check again
inline vTaskPlaceOnEventList(_id, pxEventList, EventListContainer, xTicksToWait, temp_var)
{
    AWAIT(_id, vListInsert(pxEventList, QLIST_SIZE, EventListContainer, pxCurrentTCB, xEvent, temp_var));
    prvAddCurrentTaskToDelayedList(_id, xTicksToWait, true, temp_var)
}

inline xTaskRemoveFromEventList(_id, pxUnblockedTCB, pxEventList, xReturn)
{
    AWAIT_DS(_id, xReturn = false; assert(pxUnblockedTCB == NULL_byte);
        pxUnblockedTCB = listGET_OWNER_OF_HEAD_ENTRY(pxEventList); assert(pxUnblockedTCB != NULL_byte));
    AWAIT_DS(_id, uxListRemove(pxEventList, QLIST_SIZE, pxUnblockedTCB, xEvent));

    if
    :: SELE2_AS(_id, uxSchedulerSuspended == 0);
        AWAIT_DS(_id,
            /* Reset xTickCount and xState of pxUnblockedTCB as soon as possible */
            listSET_LIST_ITEM_VALUE(TCB(pxUnblockedTCB).ListItems[xState], 0);
            if
            :: listLIST_ITEM_CONTAINER(TCB(pxUnblockedTCB).ListItems[xState]) == CID_DELAYED_TASK ->
                uxListRemove(pxDelayedTaskList, DLIST_SIZE, pxUnblockedTCB, xState);
                if
                :: listLIST_IS_EMPTY(pxDelayedTaskList) -> reset_xTickCount()
                :: else
                fi
#if (INCLUDE_vTaskSuspend == 1)
            :: listLIST_ITEM_CONTAINER(TCB(pxUnblockedTCB).ListItems[xState]) == CID_SUSPENDED_TASK ->
                uxListRemove(xSuspendedTaskList, SLIST_SIZE, pxUnblockedTCB, xState);
#endif
            :: else -> assert(false)
            fi
        );
        prvAddTaskToReadyList(_id, pxUnblockedTCB)
    :: ELSE2_AS(_id, uxSchedulerSuspended == 0);
        AWAIT_DS(_id, vListInsertEnd(xPendingReadyList, PLIST_SIZE, CID_PENDING_READY, pxUnblockedTCB, xEvent))
    fi;

    if
    :: SELE3_AS(_id, TCB(pxUnblockedTCB).uxPriority > TCB(pxCurrentTCB).uxPriority, pxUnblockedTCB = NULL_byte);
        AWAIT_DS(_id, xReturn = true; xYieldPending = true)
    :: ELSE3_AS(_id, TCB(pxUnblockedTCB).uxPriority > TCB(pxCurrentTCB).uxPriority, pxUnblockedTCB = NULL_byte);
        AWAIT_DS(_id, xReturn = false)
    fi
}

#if (INCLUDE_vTaskSuspend == 1)
    #define xTaskCheckForTimeOut(pxTimeOut, pxTicksToWait)  (!pxTimeOut || pxTicksToWait == NULL_byte)
#else
    #define xTaskCheckForTimeOut(pxTimeOut, pxTicksToWait)  (!pxTimeOut)
#endif

inline vTaskMissedYield(_id)
{
    AWAIT_DS(_id, xYieldPending = true)
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
        :: SELE2(_id, listLENGTH_IS_EXCEEDING_1(pxReadyTasksLists[tskIDLE_PRIORITY]));
            taskYIELD(_id, temp_var)
        :: ELSE2(_id, listLENGTH_IS_EXCEEDING_1(pxReadyTasksLists[tskIDLE_PRIORITY]))
        fi;
    #endif

    #if ((configUSE_PREEMPTION == 1) && (configIDLE_SHOULD_YIELD == 0))
        /* If the loop is empty, the SysTick flag will never be set */
        AWAIT(_id, skip)
    #endif
od
}

inline prvResetNextTaskUnblockTicks(_id)
{
    if
    :: SELE2_AS(_id, listLIST_IS_EMPTY(pxDelayedTaskList));
        AWAIT_DS(_id, reset_xTickCount())
    :: ELSE2_AS(_id, listLIST_IS_EMPTY(pxDelayedTaskList));
        AWAIT_DS(_id, update_xTickCount())
    fi
}

#if (configUSE_MUTEXES == 1)

inline xTaskPriorityInherit(_id, pxMutexHolder, xReturn)
{
    if
    :: SELE3_AS(_id, FIRST_TASK <= pxMutexHolder && pxMutexHolder < NULL_byte, assert(!xReturn));
        if
        :: SELE2_AS(_id, TCB(pxMutexHolder).uxPriority < TCB(pxCurrentTCB).uxPriority);
            if
            :: SELE2_AS(_id, (listGET_LIST_ITEM_VALUE(TCB(pxMutexHolder).ListItems[xEvent]) & taskEVENT_LIST_ITEM_VALUE_IN_USE) == 0);
                AWAIT_DS(_id, listSET_LIST_ITEM_VALUE(TCB(pxMutexHolder).ListItems[xEvent], configMAX_PRIORITIES - TCB(pxCurrentTCB).uxPriority))
            :: ELSE2_AS(_id, (listGET_LIST_ITEM_VALUE(TCB(pxMutexHolder).ListItems[xEvent]) & taskEVENT_LIST_ITEM_VALUE_IN_USE) == 0)
            fi;

            if
            :: SELE2_AS(_id, listIS_CONTAINED_WITHIN(CID_READY_LISTS + TCB(pxMutexHolder).uxPriority, TCB(pxMutexHolder).ListItems[xState]) != false);
                AWAIT_DS(_id, uxListRemove_pxIndex(pxReadyTasksLists[TCB(pxMutexHolder).uxPriority], RLIST_SIZE, pxMutexHolder, xState));
                if
                :: SELE2_AS(_id, listLIST_IS_EMPTY(pxReadyTasksLists[TCB(pxMutexHolder).uxPriority]));
                    taskRESET_READY_PRIORITY(_id, TCB(pxMutexHolder).uxPriority)
                :: ELSE2_AS(_id, listLIST_IS_EMPTY(pxReadyTasksLists[TCB(pxMutexHolder).uxPriority]))
                fi;

                AWAIT_DS(_id, TCB(pxMutexHolder).uxPriority = TCB(pxCurrentTCB).uxPriority);
                prvAddTaskToReadyList(_id, pxMutexHolder)
            :: ELSE2_AS(_id, listIS_CONTAINED_WITHIN(CID_READY_LISTS + TCB(pxMutexHolder).uxPriority, TCB(pxMutexHolder).ListItems[xState]) != false);
                AWAIT_DS(_id, TCB(pxMutexHolder).uxPriority = TCB(pxCurrentTCB).uxPriority)
            fi;

            AWAIT_DS(_id, xReturn = true)
        :: ELSE2_AS(_id, TCB(pxMutexHolder).uxPriority < TCB(pxCurrentTCB).uxPriority);
            if
            :: SELE2_AS(_id, TCB(pxMutexHolder).uxBasePriority < TCB(pxCurrentTCB).uxPriority);
                AWAIT_DS(_id, xReturn = true)
            :: ELSE2_AS(_id, TCB(pxMutexHolder).uxBasePriority < TCB(pxCurrentTCB).uxPriority)
            fi
        fi
    :: ELSE3_AS(_id, FIRST_TASK <= pxMutexHolder && pxMutexHolder < NULL_byte, assert(!xReturn))
    fi
}

inline xTaskPriorityDisinherit(_id, pxMutexHolder, xReturn)
{
    if
    :: SELE2_AS(_id, FIRST_TASK <= pxMutexHolder && pxMutexHolder < NULL_byte);
        AWAIT_DS(_id, assert(pxMutexHolder == pxCurrentTCB && TCB(pxMutexHolder).uxMutexesHeld != NULL_byte);
            TCB(pxMutexHolder).uxMutexesHeld = TCB(pxMutexHolder).uxMutexesHeld - 1);

        if
        :: SELE2_AS(_id, TCB(pxMutexHolder).uxPriority != TCB(pxMutexHolder).uxBasePriority);
            if
            :: SELE2_AS(_id, TCB(pxMutexHolder).uxMutexesHeld == 0);
                AWAIT_DS(_id,
                    assert(listLIST_ITEM_CONTAINER(TCB(pxMutexHolder).ListItems[xState]) == CID_READY_LISTS + TCB(pxMutexHolder).uxPriority);
                    uxListRemove_pxIndex(pxReadyTasksLists[TCB(pxMutexHolder).uxPriority], RLIST_SIZE, pxMutexHolder, xState))
                if
                :: SELE2_AS(_id, listLIST_IS_EMPTY(pxReadyTasksLists[TCB(pxMutexHolder).uxPriority]));
                    taskRESET_READY_PRIORITY(_id, TCB(pxMutexHolder).uxPriority)
                :: ELSE2_AS(_id, listLIST_IS_EMPTY(pxReadyTasksLists[TCB(pxMutexHolder).uxPriority]))
                fi;

                AWAIT_DS(_id, TCB(pxMutexHolder).uxPriority = TCB(pxMutexHolder).uxBasePriority);

                AWAIT_DS(_id, listSET_LIST_ITEM_VALUE(TCB(pxMutexHolder).ListItems[xEvent], configMAX_PRIORITIES - TCB(pxMutexHolder).uxPriority));
                prvAddTaskToReadyList(_id, pxMutexHolder);

                AWAIT_DS(_id, assert(xReturn == false); xReturn = true)
            :: ELSE2_AS(_id, TCB(pxMutexHolder).uxMutexesHeld == 0)
            fi
        :: ELSE2_AS(_id, TCB(pxMutexHolder).uxPriority != TCB(pxMutexHolder).uxBasePriority)
        fi
    :: ELSE3_AS(_id, FIRST_TASK <= pxMutexHolder && pxMutexHolder < NULL_byte, assert(xReturn == false))
    fi
}

inline pvTaskIncrementMutexHeldCount(_id, pxMutexHolder)
{
    if
    :: SELE2_AS(_id, pxCurrentTCB != NULL_byte);
        AWAIT_DS(_id, TCB(pxCurrentTCB).uxMutexesHeld = TCB(pxCurrentTCB).uxMutexesHeld + 1)
    :: ELSE2_AS(_id, pxCurrentTCB != NULL_byte)
    fi;

    AWAIT_DS(_id, pxMutexHolder = pxCurrentTCB)
}

#if 0
    The variable uxHighestPriorityWaitingTask will not be referenced at
    the following of the next statement. To reduce the usage of temporary
    variables, we reassign the uxHighestPriorityWaitingTask variable.
#endif

#define uxPriorityToUse     uxHighestPriorityWaitingTask
#define uxOnlyOneMutexHeld  1

inline vTaskPriorityDisinheritAfterTimeout(_id, pxMutexHolder, uxHighestPriorityWaitingTask, uxPriorityUsedOnEntry)
{
    if
    :: SELE2_AS(_id, pxMutexHolder != NULL_byte);
        AWAIT_DS(_id, assert(TCB(pxMutexHolder).uxMutexesHeld != NULL_byte));
        if
        :: SELE2_AS(_id, TCB(pxMutexHolder).uxBasePriority < uxHighestPriorityWaitingTask);
            AWAIT_DS(_id, uxPriorityToUse = uxHighestPriorityWaitingTask)
        :: ELSE2_AS(_id, TCB(pxMutexHolder).uxBasePriority < uxHighestPriorityWaitingTask);
            AWAIT_DS(_id, uxPriorityToUse = TCB(pxMutexHolder).uxBasePriority)
        fi;

        if
        :: SELE2_AS(_id, TCB(pxMutexHolder).uxPriority != uxPriorityToUse);
            if
            :: SELE2_AS(_id, TCB(pxMutexHolder).uxMutexesHeld == uxOnlyOneMutexHeld);
                AWAIT_DS(_id, assert(pxMutexHolder != pxCurrentTCB && uxPriorityUsedOnEntry == NULL_byte);
                    uxPriorityUsedOnEntry = TCB(pxMutexHolder).uxPriority);
                AWAIT_DS(_id, TCB(pxMutexHolder).uxPriority = uxPriorityToUse);

                if
                :: SELE2_AS(_id, (listGET_LIST_ITEM_VALUE(TCB(pxMutexHolder).ListItems[xEvent]) & taskEVENT_LIST_ITEM_VALUE_IN_USE) == 0);
                    AWAIT_DS(_id,
                        listSET_LIST_ITEM_VALUE(TCB(pxMutexHolder).ListItems[xEvent], configMAX_PRIORITIES - (uxPriorityToUse));
                        uxPriorityToUse = NULL_byte /* reset variable */)
                :: ELSE2_AS(_id, (listGET_LIST_ITEM_VALUE(TCB(pxMutexHolder).ListItems[xEvent]) & taskEVENT_LIST_ITEM_VALUE_IN_USE) == 0)
                fi;

                if
                :: SELE2_AS(_id, listIS_CONTAINED_WITHIN(CID_READY_LISTS + uxPriorityUsedOnEntry, TCB(pxMutexHolder).ListItems[xState]));
                    AWAIT_DS(_id, uxListRemove_pxIndex(pxReadyTasksLists[uxPriorityUsedOnEntry], RLIST_SIZE, pxMutexHolder, xState));
                    if
                    :: SELE3_AS(_id, listLIST_IS_EMPTY(pxReadyTasksLists[uxPriorityUsedOnEntry]), uxPriorityUsedOnEntry = NULL_byte);
                        portRESET_READY_PRIORITY(_id, TCB(pxMutexHolder).uxPriority, uxTopReadyPriority)
                    :: ELSE3_AS(_id, listLIST_IS_EMPTY(pxReadyTasksLists[uxPriorityUsedOnEntry]), uxPriorityUsedOnEntry = NULL_byte)
                    fi;

                    prvAddTaskToReadyList(_id, pxMutexHolder)
                :: ELSE3_AS(_id, listIS_CONTAINED_WITHIN(CID_READY_LISTS + uxPriorityUsedOnEntry, TCB(pxMutexHolder).ListItems[xState]), uxPriorityUsedOnEntry = NULL_byte)
                fi
            :: ELSE2_AS(_id, TCB(pxMutexHolder).uxMutexesHeld == uxOnlyOneMutexHeld)
            fi
        :: ELSE3_AS(_id, TCB(pxMutexHolder).uxPriority != uxPriorityToUse, uxPriorityToUse = NULL_byte)
        fi
    :: ELSE2_AS(_id, pxMutexHolder != NULL_byte)
    fi
}

#endif /* configUSE_MUTEXES */

// TODO check again
inline prvAddCurrentTaskToDelayedList(_id, xTicksToWait, xCanBlockIndefinitely, temp_var)
{
    AWAIT(_id,
        assert(listLIST_ITEM_CONTAINER(TCB(pxCurrentTCB).ListItems[xState]) == CID_READY_LISTS + TCB(pxCurrentTCB).uxPriority);
        uxListRemove_pxIndex(pxReadyTasksLists[TCB(pxCurrentTCB).uxPriority], RLIST_SIZE, pxCurrentTCB, xState));
    if
    :: SELE2(_id, listLIST_IS_EMPTY(pxReadyTasksLists[TCB(pxCurrentTCB).uxPriority]));
        portRESET_READY_PRIORITY(_id, TCB(now.pxCurrentTCB).uxPriority, uxTopReadyPriority)
    :: ELSE2(_id, listLIST_IS_EMPTY(pxReadyTasksLists[TCB(pxCurrentTCB).uxPriority]))
    fi;

#if (INCLUDE_vTaskSuspend == 1)
    if
    :: SELE2(_id, xTicksToWait == portMAX_DELAY && xCanBlockIndefinitely != false);
        AWAIT(_id, vListInsertEnd(xSuspendedTaskList, SLIST_SIZE, CID_SUSPENDED_TASK, pxCurrentTCB, xState))
    :: ELSE2(_id, xTicksToWait == portMAX_DELAY && xCanBlockIndefinitely != false);
        AWAIT(_id,
            assert(xTicksToWait < 256 && listGET_LIST_ITEM_VALUE(TCB(pxCurrentTCB).ListItems[xState]) == 0);
            listSET_LIST_ITEM_VALUE(TCB(pxCurrentTCB).ListItems[xState], xTicksToWait));
        AWAIT(_id,
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
    AWAIT(_id,
        assert(xTicksToWait < 256 && listGET_LIST_ITEM_VALUE(TCB(pxCurrentTCB).ListItems[xState]) == 0);
        listSET_LIST_ITEM_VALUE(TCB(pxCurrentTCB).ListItems[xState], xTicksToWait));
    AWAIT(_id,
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
