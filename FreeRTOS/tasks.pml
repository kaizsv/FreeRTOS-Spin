#ifndef _TASKS_
#define _TASKS_

#include "../FreeRTOS.pml"
#include "list.pml"

#define tskIDLE_PRIORITY        0
#define taskYIELD(_id)          portYIELD(_id)

#define taskENTER_CRITICAL(_id) portENTER_CRITICAL(_id)
#define taskEXIT_CRITICAL(_id)  portEXIT_CRITICAL(_id)

#if (configUSE_PREEMPTION == 0)
    #define taskYIELD_IF_USING_PREEMPTION(_id)
#else
    #define taskYIELD_IF_USING_PREEMPTION(_id)  portYIELD_WITHIN_API(_id)
#endif

#define taskEVENT_LIST_ITEM_VALUE_IN_USE 8 /* 0b1000 */

#define xState  0
#define xEvent  1
typedef TCB_t {
    ListItem_t ListItems[2];
    byte uxPriority;
    // Move uxBasePriority and uxMutexesHeld to another sturcture.
#if ( portCRITICAL_NESTING_IN_TCB == 1 )
    byte uxCriticalNesting;
#endif
};

#define TCB(index) TCBs[__OWNER_OF(index)]
TCB_t TCBs[promela_TASK_NUMBER + 1]; // include IDLE task

#if (configUSE_MUTEXES == 1)

typedef TCB_MUTEXES_t {
    byte uxBasePriority;
    byte uxMutexesHeld;
};

#define TCB_uxBasePriority(index)   TCBs_MUTEXES[__OWNER_OF(index)].uxBasePriority
#define TCB_uxMutexesHeld(index)    TCBs_MUTEXES[__OWNER_OF(index)].uxMutexesHeld
TCB_MUTEXES_t TCBs_MUTEXES[promela_TASK_NUMBER]; // exclude idle task

#endif

byte pxCurrentTCB = NULL_byte;

/* Declarator all lists. */
#include "include/Tasks_Lists_Declarator.pml"

#if (configUSE_PORT_OPTIMISED_TASK_SELECTION == 0)

inline taskRECORD_READY_PRIORITY(_id, Priority)
{
    if
    :: SELE_SAFE(_id, Priority > uxTopReadyPriority);
        AWAIT_SAFE(_id, uxTopReadyPriority = Priority)
    :: ELSE_SAFE(_id, Priority > uxTopReadyPriority)
    fi
}

inline taskRECORD_READY_PRIORITY_fixed(Priority)
{
    if
    :: Priority > uxTopReadyPriority ->
        uxTopReadyPriority = Priority
    :: else
    fi
}

inline taskSELECT_HIGHEST_PRIORITY_TASK(_id, local_idx)
{
    AWAIT_SAFE(_id, assert(local_idx == NULL_byte);
        local_idx = uxTopReadyPriority);
    do
    :: SELE_SAFE(_id, listLIST_IS_EMPTY(pxReadyTasksLists[local_idx]));
        AWAIT_SAFE(_id, assert(local_idx > 0); local_idx = local_idx - 1)
    :: ELSE_SAFE(_id, listLIST_IS_EMPTY(pxReadyTasksLists[local_idx]));
        atomic { (_id == EP); break }
    od;

    listGET_OWNER_OF_NEXT_ENTRY(_id, pxCurrentTCB, pxReadyTasksLists[local_idx], RLIST_SIZE);
    AWAIT_SAFE(_id, uxTopReadyPriority = local_idx; local_idx = NULL_byte)
}

    #define taskRESET_READY_PRIORITY(_id, uxPriority)
    #define portRESET_READY_PRIORITY(uxPriority, uxTopReadyPriority)
    #define EMPTY_RESET_PRIORITY_MACROS
#else

#define taskRECORD_READY_PRIORITY(_id, Priority) \
    AWAIT_SAFE(_id, portRECORD_READY_PRIORITY(Priority, uxTopReadyPriority))

#define taskRECORD_READY_PRIORITY_fixed(Priority) \
    portRECORD_READY_PRIORITY(Priority, uxTopReadyPriority)

inline taskSELECT_HIGHEST_PRIORITY_TASK(_id, local_idx)
{
    AWAIT_SAFE(_id,
        portGET_HIGHEST_PRIORITY(local_idx, uxTopReadyPriority);
        assert(listLIST_IS_EMPTY(pxReadyTasksLists[local_idx]) == false)
    );
    listGET_OWNER_OF_NEXT_ENTRY(_id, pxCurrentTCB, pxReadyTasksLists[local_idx], RLIST_SIZE);
    AWAIT_SAFE(_id, local_idx = NULL_byte);
}

inline taskRESET_READY_PRIORITY(_id, Priority)
{
    if
    :: SELE_SAFE(_id, listLIST_IS_EMPTY(pxReadyTasksLists[Priority]));
        AWAIT_SAFE(_id, portRESET_READY_PRIORITY(Priority, uxTopReadyPriority));
    :: ELSE_SAFE(_id, listLIST_IS_EMPTY(pxReadyTasksLists[Priority]));
    fi
}

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
byte xNextTaskUnblockTicks = portMAX_DELAY;

#define reset_xTickCount() xTickCount = 0

#define update_xTickCount(idx) \
    for (idx: 0 .. (DLIST_SIZE - 1)) { \
        if \
        :: !listPOINTER_IS_NULL(pxDelayedTaskList.ps[idx]) -> \
            assert(listGET_LIST_ITEM_VALUE(pxOrdinalListItem(pxDelayedTaskList, idx)) > xTickCount); \
            listSET_LIST_ITEM_VALUE(pxOrdinalListItem(pxDelayedTaskList, idx), \
                listGET_LIST_ITEM_VALUE(pxOrdinalListItem(pxDelayedTaskList, idx)) - xTickCount) \
        :: else -> break \
        fi \
    } \
    idx = NULL_byte; \
    xNextTaskUnblockTicks = listGET_ITEM_VALUE_OF_HEAD_ENTRY(pxDelayedTaskList); \
    reset_xTickCount()

#define uxCurrentNumberOfTasks promela_TASK_NUMBER + 1 /* user tasks and the idle */

inline prvAddTaskToReadyList(_id, pxTCB)
{
    taskRECORD_READY_PRIORITY(_id, TCB(pxTCB).uxPriority);
    AWAIT_SAFE_D(_id, vListInsertEnd_pxIndex(pxReadyTasksLists[TCB(pxTCB).uxPriority], RLIST_SIZE, CID_READY_LISTS + TCB(pxTCB).uxPriority, pxTCB, xState, hidden_idx))
}

inline prvAddTaskToReadyList_fixed(pxTCB)
{
    taskRECORD_READY_PRIORITY_fixed(TCB(pxTCB).uxPriority);
    vListInsertEnd_pxIndex(pxReadyTasksLists[TCB(pxTCB).uxPriority], RLIST_SIZE, CID_READY_LISTS + TCB(pxTCB).uxPriority, pxTCB, xState, hidden_idx)
}

#define prvGetTCBFromHandle(pxHandle) (pxHandle == NULL_byte -> pxCurrentTCB : pxHandle)

inline prvInitialiseTaskLists()
{
#if (promela_QUEUE_NUMBER > 0)
    /* check the Queue Lists are initialized */
    for (hidden_idx: 0 .. (promela_QUEUE_NUMBER - 1)) {
        assert(listPOINTER_IS_NULL(QLISTs[hidden_idx * 2].ps[0])); /* xTasksWaitingToSend */
        assert(listPOINTER_IS_NULL(QLISTs[hidden_idx*2+1].ps[0])); /* xTasksWaitingToReceive */
    }
    hidden_idx = NULL_byte;
#endif

    /* idx2: prevent double assignment from vListInitialise */
    for (hidden_idx2: 0 .. (configMAX_PRIORITIES - 1)) {
        vListInitialise_pxIndex(pxReadyTasksLists[hidden_idx2], RLIST_SIZE);
    }
    hidden_idx2 = NULL_byte;

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
    if
    :: pcName != IDLE_TASK_ID ->
        TCB_uxBasePriority(pcName) = Priority;
        TCB_uxMutexesHeld(pcName) = 0;
    :: else
    fi;
#endif
    vListInitialiseItem(TCB(pcName).ListItems[xState]);
    vListInitialiseItem(TCB(pcName).ListItems[xEvent]);
    listSET_LIST_ITEM_VALUE(TCB(pcName).ListItems[xEvent], configMAX_PRIORITIES - (Priority));

#if (portCRITICAL_NESTING_IN_TCB == 1 )
    TCB(pcName).uxCriticalNesting = 0;
#endif

    pxPortInitialiseStack(pcName);

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

inline vTaskDelay(_id, xTicksToDelay, xAlreadyYielded, temp_var)
{
    if
    :: SELE(_id, xTicksToDelay > 0, assert(uxSchedulerSuspended == 0));
        vTaskSuspendAll(_id);
        prvAddCurrentTaskToDelayedList(_id, xTicksToDelay, false);
        xTaskResumeAll(_id, temp_var, xAlreadyYielded)
    :: ELSE(_id, xTicksToDelay > 0, assert(xAlreadyYielded == NULL_byte))
    fi;

    if
    :: SELE(_id, xAlreadyYielded == false, xAlreadyYielded = NULL_byte);
        portYIELD_WITHIN_API(_id)
    :: ELSE(_id, xAlreadyYielded == false, xAlreadyYielded = NULL_byte)
    fi
}

#endif

#if (INCLUDE_uxTaskPriorityGet == 1)

#define uxTaskPriorityGet(xTask) TCB(prvGetTCBFromHandle(xTask)).uxPriority

#endif /* INCLUDE_uxTaskPriorityGet */

#if (INCLUDE_vTaskPrioritySet == 1)

#define uxCurrentBasePriority       temp_var
#define uxPriorityUsedOnEntry_pset  temp_var

inline vTaskPrioritySet(_id, xTask, uxNewPriority, pxTCB, xYieldRequired, temp_var)
{
    AWAIT(_id, assert(uxNewPriority < configMAX_PRIORITIES && xYieldRequired == false && temp_var == NULL_byte));

    taskENTER_CRITICAL(_id);
    AWAIT_SAFE(_id, assert(pxTCB == NULL_byte); pxTCB = prvGetTCBFromHandle(xTask));

#if (configUSE_MUTEXES == 1)
    AWAIT_SAFE(_id, assert(uxCurrentBasePriority == NULL_byte); uxCurrentBasePriority = TCB_uxBasePriority(pxTCB));
#else
    AWAIT_SAFE(_id, assert(uxCurrentBasePriority == NULL_byte); uxCurrentBasePriority = TCB(pxTCB).uxPriority);
#endif

    if
    :: SELE_SAFE(_id, uxCurrentBasePriority != uxNewPriority);
        if
        :: SELE_SAFE(_id, uxNewPriority > uxCurrentBasePriority, uxCurrentBasePriority = NULL_byte);
            if
            :: SELE_SAFE(_id, pxTCB != pxCurrentTCB && uxNewPriority >= TCB(pxCurrentTCB).uxPriority);
                AWAIT_SAFE(_id, xYieldRequired = true)
            :: ELSE_SAFE(_id, pxTCB != pxCurrentTCB && uxNewPriority >= TCB(pxCurrentTCB).uxPriority)
            fi
        :: ELSE_SAFE(_id, uxNewPriority > uxCurrentBasePriority, uxCurrentBasePriority = NULL_byte);
            if
            :: SELE_SAFE(_id, pxTCB == pxCurrentTCB);
                AWAIT_SAFE(_id, xYieldRequired = true)
            :: ELSE_SAFE(_id, pxTCB == pxCurrentTCB)
            fi
        fi;

        AWAIT_SAFE(_id, uxPriorityUsedOnEntry_pset = TCB(pxTCB).uxPriority);

#if (configUSE_MUTEXES == 1)
        if
        :: SELE_SAFE(_id, TCB_uxBasePriority(pxTCB) == TCB(pxTCB).uxPriority);
            AWAIT_SAFE(_id, TCB(pxTCB).uxPriority = uxNewPriority)
        :: ELSE_SAFE(_id, TCB_uxBasePriority(pxTCB) == TCB(pxTCB).uxPriority)
        fi;
        AWAIT_SAFE(_id, TCB_uxBasePriority(pxTCB) = uxNewPriority);
#else
        AWAIT_SAFE(_id, TCB(pxTCB).uxPriority = uxNewPriority);
#endif
        if
        :: SELE_SAFE(_id, (listGET_LIST_ITEM_VALUE(TCB(pxTCB).ListItems[xEvent]) & taskEVENT_LIST_ITEM_VALUE_IN_USE) == 0);
            AWAIT_SAFE(_id, listSET_LIST_ITEM_VALUE(TCB(pxTCB).ListItems[xEvent], configMAX_PRIORITIES - (uxNewPriority)))
        :: ELSE_SAFE(_id, (listGET_LIST_ITEM_VALUE(TCB(pxTCB).ListItems[xEvent]) & taskEVENT_LIST_ITEM_VALUE_IN_USE) == 0)
        fi;

        if
        :: SELE_SAFE(_id, listIS_CONTAINED_WITHIN(CID_READY_LISTS + uxPriorityUsedOnEntry_pset, TCB(pxTCB).ListItems[xState]) != false);
            AWAIT_SAFE_D(_id, uxListRemove_pxIndex(pxReadyTasksLists[uxPriorityUsedOnEntry_pset], RLIST_SIZE, pxTCB, xState, hidden_idx));
#ifndef EMPTY_RESET_PRIORITY_MACROS
            if
            :: SELE_SAFE(_id, listLIST_IS_EMPTY(pxReadyTasksLists[uxPriorityUsedOnEntry_pset]));
                AWAIT_SAFE(_id, portRESET_READY_PRIORITY(uxPriorityUsedOnEntry_pset, uxTopReadyPriority));
            :: ELSE_SAFE(_id, listLIST_IS_EMPTY(pxReadyTasksLists[uxPriorityUsedOnEntry_pset]))
            fi;
#endif
            prvAddTaskToReadyList(_id, pxTCB)
        :: ELSE_SAFE(_id, listIS_CONTAINED_WITHIN(CID_READY_LISTS + uxPriorityUsedOnEntry_pset, TCB(pxTCB).ListItems[xState]) != false)
        fi;

        if
        :: SELE_SAFE(_id, xYieldRequired != false, xYieldRequired = false; pxTCB = NULL_byte; uxPriorityUsedOnEntry_pset = NULL_byte);
            taskYIELD_IF_USING_PREEMPTION(_id)
        :: ELSE_SAFE(_id, xYieldRequired != false, pxTCB = NULL_byte; uxPriorityUsedOnEntry_pset = NULL_byte)
        fi
    :: ELSE_SAFE(_id, uxCurrentBasePriority != uxNewPriority, pxTCB = NULL_byte; uxCurrentBasePriority = NULL_byte)
    fi;
    taskEXIT_CRITICAL(_id)
}

#endif /* INCLUDE_vTaskPrioritySet */

#if (INCLUDE_vTaskSuspend == 1)

inline vTaskSuspend(_id, xTaskToSuspend, pxTCB)
{
    taskENTER_CRITICAL(_id);
    AWAIT_SAFE(_id, assert(pxTCB == NULL_byte); pxTCB = prvGetTCBFromHandle(xTaskToSuspend));

    AWAIT_SAFE_D(_id, assert(listLIST_ITEM_CONTAINER(TCB(pxTCB).ListItems[xState]) == CID_DELAYED_TASK ||
            listLIST_ITEM_CONTAINER(TCB(pxTCB).ListItems[xState]) == CID_READY_LISTS + TCB(pxTCB).uxPriority);
        if
        :: listLIST_ITEM_CONTAINER(TCB(pxTCB).ListItems[xState]) == CID_READY_LISTS + TCB(pxTCB).uxPriority ->
            uxListRemove_pxIndex(pxReadyTasksLists[TCB(pxTCB).uxPriority], RLIST_SIZE, pxTCB, xState, hidden_idx);
        :: listLIST_ITEM_CONTAINER(TCB(pxTCB).ListItems[xState]) == CID_DELAYED_TASK ->
            uxListRemove(pxDelayedTaskList, DLIST_SIZE, pxTCB, xState, hidden_idx);
            listSET_LIST_ITEM_VALUE(TCB(pxTCB).ListItems[xState], 0);
        fi
    );
#ifndef EMPTY_RESET_PRIORITY_MACROS
    if
    :: SELE_SAFE(_id, listLIST_IS_EMPTY(pxReadyTasksLists[TCB(pxTCB).uxPriority]));
        taskRESET_READY_PRIORITY(_id, TCB(pxTCB).uxPriority)
    :: ELSE_SAFE(_id, listLIST_IS_EMPTY(pxReadyTasksLists[TCB(pxTCB).uxPriority]))
    fi;
#endif

#if (promela_QUEUE_NUMBER > 0)
    if
    :: SELE_SAFE(_id, listLIST_ITEM_CONTAINER(TCB(pxTCB).ListItems[xEvent]) != NULL_byte);
        AWAIT_SAFE_D(_id, uxListRemove(QLISTs[listLIST_ITEM_CONTAINER(TCB(pxTCB).ListItems[xEvent])], QLIST_SIZE, pxTCB, xEvent, hidden_idx))
    :: ELSE_SAFE(_id, listLIST_ITEM_CONTAINER(TCB(pxTCB).ListItems[xEvent]) != NULL_byte)
    fi;
#endif

    AWAIT_SAFE_D(_id, vListInsertEnd(xSuspendedTaskList, SLIST_SIZE, CID_SUSPENDED_TASK, pxTCB, xState, hidden_idx));

    taskEXIT_CRITICAL(_id);

    taskENTER_CRITICAL(_id);
    /* Reset the unblock tick in case it referred to the task that is now in
     * the Suspended state */
    prvResetNextTaskUnblockTicks(_id);
    taskEXIT_CRITICAL(_id);

    if
    :: SELE(_id, pxTCB == pxCurrentTCB, pxTCB = NULL_byte);
        /* The scheduler is always running */
        AWAIT(_id, assert(xIsSchedulerRunning && uxSchedulerSuspended == 0));
        portYIELD_WITHIN_API(_id)
    :: ELSE(_id, pxTCB == pxCurrentTCB, pxTCB = NULL_byte)
    fi
}

inline prvTaskIsTaskSuspended(_id, xTask, xReturn)
{
    if
    :: SELE_SAFE(_id, listIS_CONTAINED_WITHIN(CID_SUSPENDED_TASK, TCB(xTask).ListItems[xState]) != false);
        if
        :: SELE_SAFE(_id, listIS_CONTAINED_WITHIN(CID_PENDING_READY, TCB(xTask).ListItems[xEvent]) == false);
            if
            :: SELE_SAFE(_id, listIS_CONTAINED_WITHIN(NULL_byte, TCB(xTask).ListItems[xEvent]) != false);
                AWAIT_SAFE(_id, xReturn = true)
            :: ELSE_SAFE(_id, listIS_CONTAINED_WITHIN(NULL_byte, TCB(xTask).ListItems[xEvent]) != false)
            fi
        :: ELSE_SAFE(_id, listIS_CONTAINED_WITHIN(CID_PENDING_READY, TCB(xTask).ListItems[xEvent]) == false)
        fi
    :: ELSE_SAFE(_id, listIS_CONTAINED_WITHIN(CID_SUSPENDED_TASK, TCB(xTask).ListItems[xState]) != false)
    fi
}

inline vTaskResume(_id, xTaskToResume, temp_var)
{
    if
    :: SELE(_id, xTaskToResume != pxCurrentTCB && xTaskToResume != NULL_byte);
        taskENTER_CRITICAL(_id);

        prvTaskIsTaskSuspended(_id, xTaskToResume, temp_var);
        if
        :: SELE_SAFE(_id, temp_var == true, temp_var = NULL_byte);
            AWAIT_SAFE_D(_id, uxListRemove(xSuspendedTaskList, SLIST_SIZE, xTaskToResume, xState, hidden_idx));
            prvAddTaskToReadyList(_id, xTaskToResume);

            if
            :: SELE_SAFE(_id, TCB(xTaskToResume).uxPriority >= TCB(pxCurrentTCB).uxPriority);
                taskYIELD_IF_USING_PREEMPTION(_id)
            :: ELSE_SAFE(_id, TCB(xTaskToResume).uxPriority >= TCB(pxCurrentTCB).uxPriority)
            fi
        :: ELSE_SAFE(_id, temp_var == true, assert(temp_var == NULL_byte))
        fi;

        taskEXIT_CRITICAL(_id)
    :: ELSE(_id, xTaskToResume != pxCurrentTCB && xTaskToResume != NULL_byte)
    fi
}

#endif /* INCLUDE_vTaskSuspend == 1 */

inline vTaskStartScheduler(_id)
{
    d_step {
        xTaskCreate_fixed(IDLE_TASK_ID, (tskIDLE_PRIORITY | portPRIVILEGE_BIT));
    };

    portDISABLE_INTERRUPTS(_id);
    xNextTaskUnblockTicks = portMAX_DELAY;
    reset_xTickCount();

    xPortStartScheduler()
}

inline vTaskSuspendAll(_id)
{
    AWAIT(_id, uxSchedulerSuspended = uxSchedulerSuspended + 1);
}

inline xTaskResumeAll(_id, pxTCB, xAlreadyYielded)
{
#define reuse_pxTCB pxTCB
    AWAIT(_id, xAlreadyYielded = false;
        assert(pxTCB == NULL_byte && uxSchedulerSuspended));

    taskENTER_CRITICAL(_id);
    AWAIT_SAFE(_id, uxSchedulerSuspended = uxSchedulerSuspended - 1);
    if
    :: SELE_SAFE(_id, uxSchedulerSuspended == 0);
        /* Because no task is delete, uxCurrentNumberOfTasks is greater than zero */
        do
        :: SELE_SAFE(_id, !listLIST_IS_EMPTY(xPendingReadyList));
            AWAIT_SAFE(_id, pxTCB = listGET_OWNER_OF_HEAD_ENTRY(xPendingReadyList));
            AWAIT_SAFE_D(_id,
                assert(listLIST_ITEM_CONTAINER(TCB(pxTCB).ListItems[xEvent]) == CID_PENDING_READY);
                uxListRemove(xPendingReadyList, PLIST_SIZE, pxTCB, xEvent, hidden_idx));
            AWAIT_SAFE_D(_id,
#if (INCLUDE_vTaskSuspend == 1)
                assert(listLIST_ITEM_CONTAINER(TCB(pxTCB).ListItems[xState]) == CID_DELAYED_TASK ||
                    listLIST_ITEM_CONTAINER(TCB(pxTCB).ListItems[xState]) == CID_SUSPENDED_TASK);
#else
                assert(listLIST_ITEM_CONTAINER(TCB(pxTCB).ListItems[xState]) == CID_DELAYED_TASK);
#endif
                if
                :: listLIST_ITEM_CONTAINER(TCB(pxTCB).ListItems[xState]) == CID_DELAYED_TASK ->
                    uxListRemove(pxDelayedTaskList, DLIST_SIZE, pxTCB, xState, hidden_idx);
                    listSET_LIST_ITEM_VALUE(TCB(pxTCB).ListItems[xState], 0);
#if (INCLUDE_vTaskSuspend == 1)
                :: listLIST_ITEM_CONTAINER(TCB(pxTCB).ListItems[xState]) == CID_SUSPENDED_TASK ->
                    uxListRemove(xSuspendedTaskList, SLIST_SIZE, pxTCB, xState, hidden_idx);
#endif
                fi
            );
            prvAddTaskToReadyList(_id, pxTCB);

            if
            :: SELE_SAFE(_id, TCB(pxTCB).uxPriority >= TCB(pxCurrentTCB).uxPriority);
                AWAIT_SAFE(_id, xYieldPending = true)
            :: ELSE_SAFE(_id, TCB(pxTCB).uxPriority >= TCB(pxCurrentTCB).uxPriority)
            fi
        :: ELSE_SAFE(_id, !listLIST_IS_EMPTY(xPendingReadyList)); atomic { (_id == EP); break }
        od;

        if
        :: SELE_SAFE(_id, pxTCB != NULL_byte, pxTCB = NULL_byte);
            prvResetNextTaskUnblockTicks(_id)
        :: ELSE_SAFE(_id, pxTCB != NULL_byte)
        fi;

        if
        :: SELE_SAFE(_id, xPendedTicks);
            // xTaskIncrementTick
            if
            :: SELE_SAFE(_id, uxSchedulerSuspended == 0, assert(pxTCB == NULL_byte));
                AWAIT_SAFE(_id,
                    if
                    :: !listLIST_IS_EMPTY(pxDelayedTaskList) ->
                        assert(xTickCount < 254); xTickCount = xTickCount + 1
                    :: else
                    fi
                );
                if
                :: SELE_SAFE(_id, xTickCount >= xNextTaskUnblockTicks);
                    do
                    :: SELE_SAFE(_id, listLIST_IS_EMPTY(pxDelayedTaskList) == false);
                        AWAIT_SAFE(_id, pxTCB = listGET_OWNER_OF_HEAD_ENTRY(pxDelayedTaskList));
                        if
                        :: SELE_SAFE(_id, xTickCount < listGET_LIST_ITEM_VALUE(TCB(pxTCB).ListItems[xState]));
                            AWAIT_SAFE(_id,
                                xNextTaskUnblockTicks = listGET_LIST_ITEM_VALUE(TCB(pxTCB).ListItems[xState]);
                                pxTCB = NULL_byte);
                            atomic { (_id == EP); break }
                        :: ELSE_SAFE(_id, xTickCount < listGET_LIST_ITEM_VALUE(TCB(pxTCB).ListItems[xState]))
                        fi;
                        AWAIT_SAFE_D(_id,
                            uxListRemove(pxDelayedTaskList, DLIST_SIZE, pxTCB, xState, hidden_idx);
                            listSET_LIST_ITEM_VALUE(TCB(pxTCB).ListItems[xState], 0));
#if (promela_QUEUE_NUMBER > 0)
                        if
                        :: SELE_SAFE(_id, listLIST_ITEM_CONTAINER(TCB(pxTCB).ListItems[xEvent]) != NULL_byte);
                            AWAIT_SAFE_D(_id, uxListRemove(QLISTs[listLIST_ITEM_CONTAINER(TCB(pxTCB).ListItems[xEvent])], QLIST_SIZE, pxTCB, xEvent, hidden_idx));
                        :: ELSE_SAFE(_id, listLIST_ITEM_CONTAINER(TCB(pxTCB).ListItems[xEvent]) != NULL_byte)
                        fi;
#endif
                        prvAddTaskToReadyList(_id, pxTCB);
                        #if (configUSE_PREEMPTION == 1)
                        if
                        :: SELE_SAFE(_id, TCB(pxTCB).uxPriority >= TCB(pxCurrentTCB).uxPriority);
                            AWAIT_SAFE(_id, xYieldPending = true)
                        :: ELSE_SAFE(_id, TCB(pxTCB).uxPriority >= TCB(pxCurrentTCB).uxPriority)
                        fi
                        #endif
                    :: ELSE_SAFE(_id, listLIST_IS_EMPTY(pxDelayedTaskList) == false);
                        AWAIT_SAFE(_id,
                            reset_xTickCount();
                            xNextTaskUnblockTicks = portMAX_DELAY;
                            pxTCB = NULL_byte);
                        atomic { (_id == EP); break }
                    od;
                :: ELSE_SAFE(_id, xTickCount >= xNextTaskUnblockTicks);
                fi;
                #if ((configUSE_PREEMPTION == 1) && (configUSE_TIME_SLICING == 1))
                if
                :: SELE_SAFE(_id, listLENGTH_IS_EXCEEDING_1(pxReadyTasksLists[TCB(pxCurrentTCB).uxPriority]));
                    AWAIT_SAFE(_id, xYieldPending = true)
                :: ELSE_SAFE(_id, listLENGTH_IS_EXCEEDING_1(pxReadyTasksLists[TCB(pxCurrentTCB).uxPriority]))
                fi;
                #endif
                /* Because xPendedTicks is still positive, vApplicationTickHook
                 * is not executed. */
            :: ELSE_SAFE(_id, uxSchedulerSuspended == 0)
            fi;
            // end xTaskIncrementTick
            AWAIT_SAFE(_id, xPendedTicks = 0)
        :: ELSE_SAFE(_id, xPendedTicks)
        fi;

        if
        :: SELE_SAFE(_id, xYieldPending != false);
            #if (configUSE_PREEMPTION != 0)
            AWAIT_SAFE(_id, xAlreadyYielded = true);
            #endif
            taskYIELD_IF_USING_PREEMPTION(_id)
        :: ELSE_SAFE(_id, xYieldPending != false)
        fi
    :: ELSE_SAFE(_id, uxSchedulerSuspended == 0)
    fi;

    taskEXIT_CRITICAL(_id)
}

// TODO: merge xTaskIncrementTick in xTaskResumeAll
// TODO: model SysTick cycle counts as hidden variable
inline xTaskIncrementTick(_id, xSwitchRequired, pxTCB)
{
    if
    :: SELE_SAFE(_id, uxSchedulerSuspended == 0, assert(xSwitchRequired == false && pxTCB == NULL_byte));
        AWAIT_SAFE(_id,
            if
            :: !listLIST_IS_EMPTY(pxDelayedTaskList) ->
                assert(xTickCount < 254); xTickCount = xTickCount + 1
            :: else
            fi
        );
        if
        :: SELE_SAFE(_id, xTickCount >= xNextTaskUnblockTicks);
            do
            :: SELE_SAFE(_id, listLIST_IS_EMPTY(pxDelayedTaskList) == false);
                /* The delayed list is not empty. */
                AWAIT_SAFE(_id, pxTCB = listGET_OWNER_OF_HEAD_ENTRY(pxDelayedTaskList));

                if
                :: SELE_SAFE(_id, xTickCount < listGET_LIST_ITEM_VALUE(TCB(pxTCB).ListItems[xState]));
                    /* It is not time to unblock this item yet. Record the item
                     * value in xNextTaskUnblockTicks and clear it. */
                    AWAIT_SAFE(_id,
                        xNextTaskUnblockTicks = listGET_LIST_ITEM_VALUE(TCB(pxTCB).ListItems[xState]);
                        pxTCB = NULL_byte);
                    atomic { (_id == EP); break }
                :: ELSE_SAFE(_id, xTickCount < listGET_LIST_ITEM_VALUE(TCB(pxTCB).ListItems[xState]))
                fi;

                AWAIT_SAFE_D(_id,
                    uxListRemove(pxDelayedTaskList, DLIST_SIZE, pxTCB, xState, hidden_idx);
                    listSET_LIST_ITEM_VALUE(TCB(pxTCB).ListItems[xState], 0)
                );

#if (promela_QUEUE_NUMBER > 0)
                if
                :: SELE_SAFE(_id, listLIST_ITEM_CONTAINER(TCB(pxTCB).ListItems[xEvent]) != NULL_byte);
                    AWAIT_SAFE_D(_id, uxListRemove(QLISTs[listLIST_ITEM_CONTAINER(TCB(pxTCB).ListItems[xEvent])], QLIST_SIZE, pxTCB, xEvent, hidden_idx));
                :: ELSE_SAFE(_id, listLIST_ITEM_CONTAINER(TCB(pxTCB).ListItems[xEvent]) != NULL_byte)
                fi;
#endif

                prvAddTaskToReadyList(_id, pxTCB);

                #if (configUSE_PREEMPTION == 1)
                if
                :: SELE_SAFE(_id, TCB(pxTCB).uxPriority >= TCB(pxCurrentTCB).uxPriority);
                    AWAIT_SAFE(_id, xSwitchRequired = true)
                :: ELSE_SAFE(_id, TCB(pxTCB).uxPriority >= TCB(pxCurrentTCB).uxPriority)
                fi
                #endif
            :: ELSE_SAFE(_id, listLIST_IS_EMPTY(pxDelayedTaskList) == false);
                /* The delayed list is empty */
                AWAIT_SAFE(_id,
                    reset_xTickCount();
                    xNextTaskUnblockTicks = portMAX_DELAY;
                    pxTCB = NULL_byte);
                atomic { (_id == EP); break }
            od
        :: ELSE_SAFE(_id, xTickCount >= xNextTaskUnblockTicks)
        fi;

        #if ((configUSE_PREEMPTION == 1) && (configUSE_TIME_SLICING == 1))
        if
        :: SELE_SAFE(_id, listLENGTH_IS_EXCEEDING_1(pxReadyTasksLists[TCB(pxCurrentTCB).uxPriority]));
            AWAIT_SAFE(_id, xSwitchRequired = true)
        :: ELSE_SAFE(_id, listLENGTH_IS_EXCEEDING_1(pxReadyTasksLists[TCB(pxCurrentTCB).uxPriority]))
        fi;
        #endif

        #if (configUSE_TICK_HOOK == 1)
            if
            :: SELE_SAFE(_id, xPendedTicks == 0);
                vApplicationTickHook();
            :: ELSE_SAFE(_id, xPendedTicks == 0);
            fi;
        #endif

        #if (configUSE_PREEMPTION == 1)
        if
        :: SELE_SAFE(_id, xYieldPending != false);
            AWAIT_SAFE(_id, xSwitchRequired = true)
        :: ELSE_SAFE(_id, xYieldPending != false)
        fi
        #endif
    :: ELSE_SAFE(_id, uxSchedulerSuspended == 0, assert(xSwitchRequired == false && pxTCB == NULL_byte));
        AWAIT_SAFE(_id, xPendedTicks = 1);
#if (configUSE_TICK_HOOK == 1)
        vApplicationTickHook();
#endif
    fi
}

inline vTaskSwitchContext(_id, local_idx)
{
    if
    :: SELE_SAFE(_id, uxSchedulerSuspended != 0);
        AWAIT_SAFE(_id, xYieldPending = true)
    :: ELSE_SAFE(_id, uxSchedulerSuspended != 0);
        AWAIT_SAFE(_id, xYieldPending = false);
        /* configGENERATE_RUN_TIME_STATS == 0 */
        taskSELECT_HIGHEST_PRIORITY_TASK(_id, local_idx)
    fi
}

// TODO: check again
inline vTaskPlaceOnEventList(_id, pxEventList, EventListContainer, xTicksToWait)
{
    AWAIT(_id, d_step {
        vListInsert(pxEventList, QLIST_SIZE, EventListContainer, pxCurrentTCB, xEvent, hidden_idx);
    });
    prvAddCurrentTaskToDelayedList(_id, xTicksToWait, true)
}

inline xTaskRemoveFromEventList(_id, pxUnblockedTCB, pxEventList)
{
    AWAIT_SAFE(_id, assert(pxUnblockedTCB == NULL_byte && !listLIST_IS_EMPTY(pxEventList));
        pxUnblockedTCB = listGET_OWNER_OF_HEAD_ENTRY(pxEventList));
    AWAIT_SAFE_D(_id, uxListRemove(pxEventList, QLIST_SIZE, pxUnblockedTCB, xEvent, hidden_idx));

    if
    :: SELE_SAFE(_id, uxSchedulerSuspended == 0);
        AWAIT_SAFE_D(_id,
            /* Reset xTickCount and xState of pxUnblockedTCB as soon as possible */
            listSET_LIST_ITEM_VALUE(TCB(pxUnblockedTCB).ListItems[xState], 0);
#if (INCLUDE_vTaskSuspend == 1)
            assert(listLIST_ITEM_CONTAINER(TCB(pxUnblockedTCB).ListItems[xState]) == CID_DELAYED_TASK ||
                listLIST_ITEM_CONTAINER(TCB(pxUnblockedTCB).ListItems[xState]) == CID_SUSPENDED_TASK);
#else
            assert(listLIST_ITEM_CONTAINER(TCB(pxUnblockedTCB).ListItems[xState]) == CID_DELAYED_TASK);
#endif
            if
            :: listLIST_ITEM_CONTAINER(TCB(pxUnblockedTCB).ListItems[xState]) == CID_DELAYED_TASK ->
                uxListRemove(pxDelayedTaskList, DLIST_SIZE, pxUnblockedTCB, xState, hidden_idx);
#if (INCLUDE_vTaskSuspend == 1)
            :: listLIST_ITEM_CONTAINER(TCB(pxUnblockedTCB).ListItems[xState]) == CID_SUSPENDED_TASK ->
                uxListRemove(xSuspendedTaskList, SLIST_SIZE, pxUnblockedTCB, xState, hidden_idx);
#endif
            fi
        );
        prvAddTaskToReadyList(_id, pxUnblockedTCB);
        /* Because xTickCount will not monotonically increase, we have to
         * reset xNextTaskUnblockTicks here. */
        prvResetNextTaskUnblockTicks(_id);
    :: ELSE_SAFE(_id, uxSchedulerSuspended == 0);
        AWAIT_SAFE_D(_id, vListInsertEnd(xPendingReadyList, PLIST_SIZE, CID_PENDING_READY, pxUnblockedTCB, xEvent, hidden_idx))
    fi;

    if
    :: SELE_SAFE(_id, TCB(pxUnblockedTCB).uxPriority > TCB(pxCurrentTCB).uxPriority);
        AWAIT_SAFE(_id, pxUnblockedTCB = true; xYieldPending = true)
    :: ELSE_SAFE(_id, TCB(pxUnblockedTCB).uxPriority > TCB(pxCurrentTCB).uxPriority);
        AWAIT_SAFE(_id, pxUnblockedTCB = false)
    fi
}

#if (INCLUDE_vTaskSuspend == 1)
    #define xTaskCheckForTimeOut(pxTimeOut, pxTicksToWait)  (!pxTimeOut || pxTicksToWait == NULL_byte)
#else
    #define xTaskCheckForTimeOut(pxTimeOut, pxTicksToWait)  (!pxTimeOut)
#endif

inline vTaskMissedYield(_id)
{
    AWAIT_SAFE(_id, xYieldPending = true)
}

inline vTaskIDLE_TASK_BODY(_id)
{
    assert(_id == IDLE_TASK_ID);
do
::
    #if (configUSE_PREEMPTION == 0)
        taskYIELD(_id);
    #endif

    #if ((configUSE_PREEMPTION == 1) && (configIDLE_SHOULD_YIELD == 1))
        if
        :: SELE(_id, listLENGTH_IS_EXCEEDING_1(pxReadyTasksLists[tskIDLE_PRIORITY]));
            taskYIELD(_id)
        :: ELSE(_id, listLENGTH_IS_EXCEEDING_1(pxReadyTasksLists[tskIDLE_PRIORITY]))
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
    :: SELE_SAFE(_id, listLIST_IS_EMPTY(pxDelayedTaskList));
        AWAIT_SAFE(_id, reset_xTickCount(); xNextTaskUnblockTicks = portMAX_DELAY)
    :: ELSE_SAFE(_id, listLIST_IS_EMPTY(pxDelayedTaskList));
        AWAIT_SAFE(_id, xNextTaskUnblockTicks = listGET_ITEM_VALUE_OF_HEAD_ENTRY(pxDelayedTaskList))
    fi
}

#if (configUSE_MUTEXES == 1)

inline xTaskPriorityInherit(_id, pxMutexHolder, xReturn)
{
    if
    :: SELE_SAFE(_id, FIRST_TASK <= pxMutexHolder && pxMutexHolder < NULL_byte, assert(!xReturn));
        if
        :: SELE_SAFE(_id, TCB(pxMutexHolder).uxPriority < TCB(pxCurrentTCB).uxPriority);
            if
            :: SELE_SAFE(_id, (listGET_LIST_ITEM_VALUE(TCB(pxMutexHolder).ListItems[xEvent]) & taskEVENT_LIST_ITEM_VALUE_IN_USE) == 0);
                AWAIT_SAFE(_id, listSET_LIST_ITEM_VALUE(TCB(pxMutexHolder).ListItems[xEvent], configMAX_PRIORITIES - TCB(pxCurrentTCB).uxPriority))
            :: ELSE_SAFE(_id, (listGET_LIST_ITEM_VALUE(TCB(pxMutexHolder).ListItems[xEvent]) & taskEVENT_LIST_ITEM_VALUE_IN_USE) == 0)
            fi;

            if
            :: SELE_SAFE(_id, listIS_CONTAINED_WITHIN(CID_READY_LISTS + TCB(pxMutexHolder).uxPriority, TCB(pxMutexHolder).ListItems[xState]) != false);
                AWAIT_SAFE_D(_id, uxListRemove_pxIndex(pxReadyTasksLists[TCB(pxMutexHolder).uxPriority], RLIST_SIZE, pxMutexHolder, xState, hidden_idx));
#ifndef EMPTY_RESET_PRIORITY_MACROS
                if
                :: SELE_SAFE(_id, listLIST_IS_EMPTY(pxReadyTasksLists[TCB(pxMutexHolder).uxPriority]));
                    taskRESET_READY_PRIORITY(_id, TCB(pxMutexHolder).uxPriority)
                :: ELSE_SAFE(_id, listLIST_IS_EMPTY(pxReadyTasksLists[TCB(pxMutexHolder).uxPriority]))
                fi;
#endif

                AWAIT_SAFE(_id, TCB(pxMutexHolder).uxPriority = TCB(pxCurrentTCB).uxPriority);
                prvAddTaskToReadyList(_id, pxMutexHolder)
            :: ELSE_SAFE(_id, listIS_CONTAINED_WITHIN(CID_READY_LISTS + TCB(pxMutexHolder).uxPriority, TCB(pxMutexHolder).ListItems[xState]) != false);
                AWAIT_SAFE(_id, TCB(pxMutexHolder).uxPriority = TCB(pxCurrentTCB).uxPriority)
            fi;

            AWAIT_SAFE(_id, xReturn = true)
        :: ELSE_SAFE(_id, TCB(pxMutexHolder).uxPriority < TCB(pxCurrentTCB).uxPriority);
            if
            :: SELE_SAFE(_id, TCB_uxBasePriority(pxMutexHolder) < TCB(pxCurrentTCB).uxPriority);
                AWAIT_SAFE(_id, xReturn = true)
            :: ELSE_SAFE(_id, TCB_uxBasePriority(pxMutexHolder) < TCB(pxCurrentTCB).uxPriority)
            fi
        fi
    :: ELSE_SAFE(_id, FIRST_TASK <= pxMutexHolder && pxMutexHolder < NULL_byte, assert(!xReturn))
    fi
}

inline xTaskPriorityDisinherit(_id, pxMutexHolder, xReturn)
{
    if
    :: SELE_SAFE(_id, FIRST_TASK <= pxMutexHolder && pxMutexHolder < NULL_byte);
        AWAIT_SAFE(_id, assert(pxMutexHolder == pxCurrentTCB && TCB_uxMutexesHeld(pxMutexHolder) != NULL_byte);
            TCB_uxMutexesHeld(pxMutexHolder) = TCB_uxMutexesHeld(pxMutexHolder) - 1);

        if
        :: SELE_SAFE(_id, TCB(pxMutexHolder).uxPriority != TCB_uxBasePriority(pxMutexHolder));
            if
            :: SELE_SAFE(_id, TCB_uxMutexesHeld(pxMutexHolder) == 0);
                AWAIT_SAFE_D(_id,
                    assert(listLIST_ITEM_CONTAINER(TCB(pxMutexHolder).ListItems[xState]) == CID_READY_LISTS + TCB(pxMutexHolder).uxPriority);
                    uxListRemove_pxIndex(pxReadyTasksLists[TCB(pxMutexHolder).uxPriority], RLIST_SIZE, pxMutexHolder, xState, hidden_idx))
#ifndef EMPTY_RESET_PRIORITY_MACROS
                if
                :: SELE_SAFE(_id, listLIST_IS_EMPTY(pxReadyTasksLists[TCB(pxMutexHolder).uxPriority]));
                    taskRESET_READY_PRIORITY(_id, TCB(pxMutexHolder).uxPriority)
                :: ELSE_SAFE(_id, listLIST_IS_EMPTY(pxReadyTasksLists[TCB(pxMutexHolder).uxPriority]))
                fi;
#endif

                AWAIT_SAFE(_id, TCB(pxMutexHolder).uxPriority = TCB_uxBasePriority(pxMutexHolder));

                AWAIT_SAFE(_id, listSET_LIST_ITEM_VALUE(TCB(pxMutexHolder).ListItems[xEvent], configMAX_PRIORITIES - TCB(pxMutexHolder).uxPriority));
                prvAddTaskToReadyList(_id, pxMutexHolder);

                AWAIT_SAFE(_id, xReturn = true)
            :: ELSE_SAFE(_id, TCB_uxMutexesHeld(pxMutexHolder) == 0)
            fi
        :: ELSE_SAFE(_id, TCB(pxMutexHolder).uxPriority != TCB_uxBasePriority(pxMutexHolder))
        fi
    :: ELSE_SAFE(_id, FIRST_TASK <= pxMutexHolder && pxMutexHolder < NULL_byte)
    fi
}

inline pvTaskIncrementMutexHeldCount(_id, pxMutexHolder)
{
    if
    :: SELE_SAFE(_id, pxCurrentTCB != NULL_byte);
        AWAIT_SAFE(_id, TCB_uxMutexesHeld(pxCurrentTCB) = TCB_uxMutexesHeld(pxCurrentTCB) + 1)
    :: ELSE_SAFE(_id, pxCurrentTCB != NULL_byte)
    fi;

    AWAIT_SAFE(_id, pxMutexHolder = pxCurrentTCB)
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
    :: SELE_SAFE(_id, pxMutexHolder != NULL_byte);
        AWAIT_SAFE(_id, assert(TCB_uxMutexesHeld(pxMutexHolder) != NULL_byte));
        if
        :: SELE_SAFE(_id, TCB_uxBasePriority(pxMutexHolder) < uxHighestPriorityWaitingTask);
            AWAIT_SAFE(_id, uxPriorityToUse = uxHighestPriorityWaitingTask)
        :: ELSE_SAFE(_id, TCB_uxBasePriority(pxMutexHolder) < uxHighestPriorityWaitingTask);
            AWAIT_SAFE(_id, uxPriorityToUse = TCB_uxBasePriority(pxMutexHolder))
        fi;

        if
        :: SELE_SAFE(_id, TCB(pxMutexHolder).uxPriority != uxPriorityToUse);
            if
            :: SELE_SAFE(_id, TCB_uxMutexesHeld(pxMutexHolder) == uxOnlyOneMutexHeld);
                AWAIT_SAFE(_id, assert(pxMutexHolder != pxCurrentTCB && uxPriorityUsedOnEntry == NULL_byte);
                    uxPriorityUsedOnEntry = TCB(pxMutexHolder).uxPriority);
                AWAIT_SAFE(_id, TCB(pxMutexHolder).uxPriority = uxPriorityToUse);

                if
                :: SELE_SAFE(_id, (listGET_LIST_ITEM_VALUE(TCB(pxMutexHolder).ListItems[xEvent]) & taskEVENT_LIST_ITEM_VALUE_IN_USE) == 0);
                    AWAIT_SAFE(_id,
                        listSET_LIST_ITEM_VALUE(TCB(pxMutexHolder).ListItems[xEvent], configMAX_PRIORITIES - (uxPriorityToUse));
                        uxPriorityToUse = NULL_byte /* reset variable */)
                :: ELSE_SAFE(_id, (listGET_LIST_ITEM_VALUE(TCB(pxMutexHolder).ListItems[xEvent]) & taskEVENT_LIST_ITEM_VALUE_IN_USE) == 0)
                fi;

                if
                :: SELE_SAFE(_id, listIS_CONTAINED_WITHIN(CID_READY_LISTS + uxPriorityUsedOnEntry, TCB(pxMutexHolder).ListItems[xState]));
                    AWAIT_SAFE_D(_id, uxListRemove_pxIndex(pxReadyTasksLists[uxPriorityUsedOnEntry], RLIST_SIZE, pxMutexHolder, xState, hidden_idx));
#ifndef EMPTY_RESET_PRIORITY_MACROS
                    if
                    :: SELE_SAFE(_id, listLIST_IS_EMPTY(pxReadyTasksLists[uxPriorityUsedOnEntry]), uxPriorityUsedOnEntry = NULL_byte);
                        AWAIT_SAFE(_id, portRESET_READY_PRIORITY(TCB(pxMutexHolder).uxPriority, uxTopReadyPriority));
                    :: ELSE_SAFE(_id, listLIST_IS_EMPTY(pxReadyTasksLists[uxPriorityUsedOnEntry]), uxPriorityUsedOnEntry = NULL_byte)
                    fi;
#endif

                    prvAddTaskToReadyList(_id, pxMutexHolder)
                :: ELSE_SAFE(_id, listIS_CONTAINED_WITHIN(CID_READY_LISTS + uxPriorityUsedOnEntry, TCB(pxMutexHolder).ListItems[xState]), uxPriorityUsedOnEntry = NULL_byte)
                fi
            :: ELSE_SAFE(_id, TCB_uxMutexesHeld(pxMutexHolder) == uxOnlyOneMutexHeld)
            fi
        :: ELSE_SAFE(_id, TCB(pxMutexHolder).uxPriority != uxPriorityToUse, uxPriorityToUse = NULL_byte)
        fi
    :: ELSE_SAFE(_id, pxMutexHolder != NULL_byte)
    fi
}

#endif /* configUSE_MUTEXES */

#if ( portCRITICAL_NESTING_IN_TCB == 1 )

inline vTaskEnterCritical(_id)
{
    portDISABLE_INTERRUPTS(_id);
    if
    :: SELE_SAFE(_id, xIsSchedulerRunning);
        AWAIT_SAFE(_id, TCB(pxCurrentTCB).uxCriticalNesting =
            TCB(pxCurrentTCB).uxCriticalNesting + 1);
        // portASSERT_IF_IN_ISR()
    :: ELSE_SAFE(_id, xIsSchedulerRunning);
    fi;
}

inline vTaskExitCritical(_id)
{
    if
    :: SELE(_id, xIsSchedulerRunning && TCB(pxCurrentTCB).uxCriticalNesting > 0);
        AWAIT_SAFE(_id, TCB(pxCurrentTCB).uxCriticalNesting =
            TCB(pxCurrentTCB).uxCriticalNesting - 1);
        if
        :: SELE_SAFE(_id, TCB(pxCurrentTCB).uxCriticalNesting == 0);
            portENABLE_INTERRUPTS(_id);
        :: ELSE_SAFE(_id, TCB(pxCurrentTCB).uxCriticalNesting == 0);
        fi
    :: ELSE(_id, xIsSchedulerRunning && TCB(pxCurrentTCB).uxCriticalNesting > 0);
    fi
}

#endif

// TODO check again
inline prvAddCurrentTaskToDelayedList(_id, xTicksToWait, xCanBlockIndefinitely)
{
    AWAIT(_id, d_step {
        assert(listLIST_ITEM_CONTAINER(TCB(pxCurrentTCB).ListItems[xState]) == CID_READY_LISTS + TCB(pxCurrentTCB).uxPriority);
        uxListRemove_pxIndex(pxReadyTasksLists[TCB(pxCurrentTCB).uxPriority], RLIST_SIZE, pxCurrentTCB, xState, hidden_idx);
    });
#ifndef EMPTY_RESET_PRIORITY_MACROS
    if
    :: SELE(_id, listLIST_IS_EMPTY(pxReadyTasksLists[TCB(pxCurrentTCB).uxPriority]));
        AWAIT(_id, portRESET_READY_PRIORITY(TCB(pxCurrentTCB).uxPriority, uxTopReadyPriority))
    :: ELSE(_id, listLIST_IS_EMPTY(pxReadyTasksLists[TCB(pxCurrentTCB).uxPriority]))
    fi;
#endif

#if (INCLUDE_vTaskSuspend == 1)
    if
    :: SELE(_id, xTicksToWait == portMAX_DELAY && xCanBlockIndefinitely != false);
        AWAIT(_id, d_step {
            vListInsertEnd(xSuspendedTaskList, SLIST_SIZE, CID_SUSPENDED_TASK, pxCurrentTCB, xState, hidden_idx);
        })
    :: ELSE(_id, xTicksToWait == portMAX_DELAY && xCanBlockIndefinitely != false);
        AWAIT(_id,
            assert(xTicksToWait < 255 && listGET_LIST_ITEM_VALUE(TCB(pxCurrentTCB).ListItems[xState]) == 0);
            listSET_LIST_ITEM_VALUE(TCB(pxCurrentTCB).ListItems[xState], xTicksToWait));
        AWAIT(_id, d_step {
            if
            :: !listLIST_IS_EMPTY(pxDelayedTaskList) ->
                update_xTickCount(hidden_idx);
            :: else ->
                reset_xTickCount();
            fi;
            assert(xTickCount == 0);
            vListInsert(pxDelayedTaskList, DLIST_SIZE, CID_DELAYED_TASK, pxCurrentTCB, xState, hidden_idx);
        });
        if
        :: SELE(_id, xTicksToWait < xNextTaskUnblockTicks);
            AWAIT(_id, xNextTaskUnblockTicks = xTicksToWait)
        :: ELSE(_id, xTicksToWait < xNextTaskUnblockTicks);
        fi;
    fi;
#else
    AWAIT(_id,
        assert(xTicksToWait < 256 && listGET_LIST_ITEM_VALUE(TCB(pxCurrentTCB).ListItems[xState]) == 0);
        listSET_LIST_ITEM_VALUE(TCB(pxCurrentTCB).ListItems[xState], xTicksToWait));
    AWAIT(_id, d_step {
        if
        :: !listLIST_IS_EMPTY(pxDelayedTaskList) ->
            update_xTickCount(hidden_idx);
        :: else ->
            reset_xTickCount();
        fi;
        vListInsert(pxDelayedTaskList, DLIST_SIZE, CID_DELAYED_TASK, pxCurrentTCB, xState, hidden_idx);
    });
    if
    :: SELE(_id, xTicksToWait < xNextTaskUnblockTicks);
        AWAIT(_id, xNextTaskUnblockTicks = xTicksToWait)
    :: ELSE(_id, xTicksToWait < xNextTaskUnblockTicks);
    fi;
#endif
}

#endif
