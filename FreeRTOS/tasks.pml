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

#define IDX_TCB(index)  index - FIRST_TASK
#define TCB(index) TCBs[IDX_TCB(index)]
TCB_t TCBs[promela_TASK_NUMBER + 1]; // TODO: check if the idle task uses the TCB

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
        :: SELE(_id, !listLIST_IS_EMPTY(LISTs[pxReadyTasksLists + uxTopReadyPriority - idx])) ->
            AWAIT_A(_id, uxTopReadyPriority = uxTopReadyPriority - idx; break);
        :: ELSE(_id, !listLIST_IS_EMPTY(LISTs[pxReadyTasksLists + uxTopReadyPriority - idx]))
        fi
    }
    AWAIT_A(_id, idx = 0);

    listGET_OWNER_OF_NEXT_ENTRY(_id, pxCurrentTCB, LISTs[pxReadyTasksLists + uxTopReadyPriority])
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

#define uxCurrentNumberOfTasks promela_TASK_NUMBER + 1 /* user and the idle tasks */

inline prvAddTaskToReadyList(_id, pxTCB)
{
    taskRECORD_READY_PRIORITY(_id, TCB(pxTCB).uxPriority);
    AWAIT_D(_id, vListInsertEnd(LISTs[pxReadyTasksLists + TCB(pxTCB).uxPriority], pxReadyTasksLists + TCB(pxTCB).uxPriority, IDX_TCB(pxTCB), xState))
}

#define prvGetTCBFromHandle(pxHandle) (pxHandle == NULL_byte -> pxCurrentTCB : pxHandle)

inline prvInitialiseTaskLists(idx2)
{
    /* check the lists in Queue structures are initialized. */
    for (idx: 0 .. (promela_QUEUE_NUMBER - 1)) {
        /* The Queues are uninitialized if the assertions failed.
         * Please check the QueueIDs are set correctly. */
        assert(listPOINTER_IS_NULL(LISTs[idx * 2].ps[0])); /* xTasksWaitingToSend */
        assert(listPOINTER_IS_NULL(LISTs[idx*2+1].ps[0])); /* xTasksWaitingToReceive */
    }
    idx = 0;

    /* idx2: prevent double assignment from vListInitialise */
    for (idx2: 0 .. (configMAX_PRIORITIES - 1)) {
        vListInitialise(LISTs[pxReadyTasksLists + idx2]);
    }
    idx2 = NULL_byte;

    vListInitialise(LISTs[xDelayedTaskList1]);
    vListInitialise(LISTs[xPendingReadyList]);

#if (INCLUDE_vTaskSuspend == 1)
    vListInitialise(LISTs[xSuspendedTaskList]);
#endif
}

inline xTaskCreate(_id, pcName, Priority, temp_var)
{
    /* prvInitialiseNewTask */
    if
    :: Priority >= configMAX_PRIORITIES ->
        TCB(pcName).uxPriority = configMAX_PRIORITIES - 1
    :: else ->
        TCB(pcName).uxPriority = Priority;
    fi;
#if (configUSE_MUTEXES == 1)
    TCB(pcName).uxBasePriority = Priority;
    TCB(pcName).uxMutexesHeld = 0;
#endif
    vListInitialiseItem(TCB(pcName).ListItems[xState]);
    vListInitialiseItem(TCB(pcName).ListItems[xEvent]);
    listSET_LIST_ITEM_VALUE(TCB(pcName).ListItems[xEvent], configMAX_PRIORITIES - Priority);

    /* prvAddNewTaskToReadyList */
    taskENTER_CRITICAL(_id, temp_var);
    if
    :: pxCurrentTCB == NULL_byte ->
        /* list initialization check */
        assert(listLIST_IS_EMPTY(LISTs[pxReadyTasksLists]));
        pxCurrentTCB = pcName
    :: else ->
        if
        :: (xSchedulerRunning == false) &&
           (TCB(pxCurrentTCB).uxPriority <= TCB(pcName).uxPriority) ->
            pxCurrentTCB = pcName
        :: else
        fi
    fi;

    prvAddTaskToReadyList(_id, pcName);
    /* TODO: portSETUP_TCB */
    taskEXIT_CRITICAL(_id, temp_var)

    if
    :: (xSchedulerRunning != false) && (TCB(pxCurrentTCB).uxPriority < TCB(pcName).uxPriority) ->
        taskYIELD_IF_USING_PREEMPTION(_id, temp_var)
    :: else
    fi
}

#if (INCLUDE_vTaskDelay == 1)

inline vTaskDelay(_id, xTicksToDelay, xAlreadyYielded, temp_var, temp_var2)
{
    if
    :: atomic { SELE(_id, xTicksToDelay > 0) -> assert(xAlreadyYielded == false) };
        AWAIT_A(_id, assert(uxSchedulerSuspended == 0));
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
        :: SELE(_id, listIS_CONTAINED_WITHIN(pxReadyTasksLists + temp_Priority /* uxPriorityUsedOnEntry */, TCB(pxTCB).ListItems[xState]) != false) ->
            AWAIT_D(_id, uxListRemove(LISTs[listLIST_ITEM_CONTAINER(TCB(pxTCB).ListItems[xState])], IDX_TCB(pxTCB), xState, temp_var));
            if
            :: atomic { SELE(_id, temp_var == 0) -> temp_var = NULL_byte};
                portRESET_READY_PRIORITY(_id, temp_Priority /* uxPriorityUsedOnEntry */, uxTopReadyPriority)
            :: atomic { ELSE(_id, temp_var == 0) -> temp_var = NULL_byte}
            fi;
            prvAddTaskToReadyList(_id, pxTCB)
        :: ELSE(_id, listIS_CONTAINED_WITHIN(pxReadyTasksLists + temp_Priority /* uxPriorityUsedOnEntry */, TCB(pxTCB).ListItems[xState]) != false)
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

    AWAIT_D(_id, uxListRemove(LISTs[listLIST_ITEM_CONTAINER(TCB(pxTCB).ListItems[xState])], IDX_TCB(pxTCB), xState, temp_var));
    if
    :: atomic { SELE(_id, temp_var == 0) -> temp_var = NULL_byte };
        taskRESET_READY_PRIORITY(_id, TCB(pxTCB).uxPriority)
    :: atomic { ELSE(_id, temp_var == 0) -> temp_var = NULL_byte }
    fi;

    if
    :: SELE(_id, listLIST_ITEM_CONTAINER(TCB(pxTCB).ListItems[xEvent]) != NULL_byte) ->
        AWAIT_D(_id, uxListRemove(LISTs[listLIST_ITEM_CONTAINER(TCB(pxTCB).ListItems[xEvent])], IDX_TCB(pxTCB), xEvent, _))
    :: ELSE(_id, listLIST_ITEM_CONTAINER(TCB(pxTCB).ListItems[xEvent]) != NULL_byte)
    fi;

    AWAIT_D(_id, vListInsertEnd(LISTs[xSuspendedTaskList], xSuspendedTaskList, IDX_TCB(pxTCB), xState));

    // TODO: configUSE_TASK_NOTIFICATIONS
    taskEXIT_CRITICAL(_id, temp_var);

    if
    :: atomic { SELE(_id, pxTCB == pxCurrentTCB) -> pxTCB = NULL_byte };
        if
        :: SELE(_id, xSchedulerRunning != false) ->
            AWAIT_A(_id, assert(uxSchedulerSuspended == 0));
            portYIELD_WITHIN_API(_id, temp_var)
        :: ELSE(_id, xSchedulerRunning != false) ->
            if
            :: SELE(_id, listLIST_LENGTH_EQ_CURRENTNUMBEROFTASKS(LISTs[xSuspendedTaskList])) ->
                AWAIT_D(_id, pxCurrentTCB = NULL_byte)
            :: ELSE(_id, listLIST_LENGTH_EQ_CURRENTNUMBEROFTASKS(LISTs[xSuspendedTaskList])) ->
                vTaskSwitchContext(_id);
            fi
        fi
    :: atomic { ELSE(_id, pxTCB == pxCurrentTCB) -> pxTCB = NULL_byte }
    fi
}

inline prvTaskIsTaskSuspended(_id, xTask, xReturn)
{
    if
    :: atomic { SELE(_id, listIS_CONTAINED_WITHIN(xSuspendedTaskList, TCB(xTask).ListItems[xState]) != false) -> assert(xReturn == false) };
        if
        :: SELE(_id, listIS_CONTAINED_WITHIN(xPendingReadyList, TCB(xTask).ListItems[xEvent]) == false) ->
            if
            :: SELE(_id, listIS_CONTAINED_WITHIN(NULL_byte, TCB(xTask).ListItems[xEvent]) != false) ->
                AWAIT_D(_id, xReturn = true)
            :: ELSE(_id, listIS_CONTAINED_WITHIN(NULL_byte, TCB(xTask).ListItems[xEvent]) != false)
            fi
        :: ELSE(_id, listIS_CONTAINED_WITHIN(xPendingReadyList, TCB(xTask).ListItems[xEvent]) == false)
        fi
    :: atomic { ELSE(_id, listIS_CONTAINED_WITHIN(xSuspendedTaskList, TCB(xTask).ListItems[xState]) != false) -> assert(xReturn == false) }
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
            AWAIT_D(_id, uxListRemove(LISTs[listLIST_ITEM_CONTAINER(TCB(xTaskToResume).ListItems[xState])], IDX_TCB(xTaskToResume), xState, _));
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
    xTaskCreate(_id, IDLE_TASK_ID, (tskIDLE_PRIORITY | portPRIVILEGE_BIT), temp_var);

    portDISABLE_INTERRUPTS(_id, temp_var);
    xSchedulerRunning = true;

    xPortStartScheduler()
}

inline vTaskSuspendAll(_id)
{
    AWAIT_D(_id, uxSchedulerSuspended = uxSchedulerSuspended + 1);
    // portMEMORY_BARRIER(); (optimization barrier)
}

inline xTaskResumeAll(_id, pxTCB, xAlreadyYielded, temp_var)
{
    AWAIT_D(_id, xAlreadyYielded = false;
        assert(pxTCB == NULL_byte);
        assert(uxSchedulerSuspended));

    taskENTER_CRITICAL(_id, temp_var);
    AWAIT_D(_id, uxSchedulerSuspended = uxSchedulerSuspended - 1);
    if
    :: SELE(_id, uxSchedulerSuspended == 0) ->
        // FIXME: uxCurrentNumberOfTasks must greater than zero if no task is deleted.
        do
        :: SELE(_id, !listLIST_IS_EMPTY(LISTs[xPendingReadyList])) ->
            AWAIT_D(_id, pxTCB = listGET_OWNER_OF_HEAD_ENTRY(LISTs[xPendingReadyList]));
            AWAIT_D(_id, uxListRemove(LISTs[listLIST_ITEM_CONTAINER(TCB(pxTCB).ListItems[xEvent])], IDX_TCB(pxTCB), xEvent, _));
            AWAIT_D(_id, uxListRemove(LISTs[listLIST_ITEM_CONTAINER(TCB(pxTCB).ListItems[xState])], IDX_TCB(pxTCB), xState, _));
            prvAddTaskToReadyList(_id, pxTCB);

            if
            :: SELE(_id, TCB(pxTCB).uxPriority >= TCB(pxCurrentTCB).uxPriority) ->
                AWAIT_D(_id, xYieldPending = true)
            :: ELSE(_id, TCB(pxTCB).uxPriority >= TCB(pxCurrentTCB).uxPriority)
            fi
        :: ELSE(_id, !listLIST_IS_EMPTY(LISTs[xPendingReadyList])) ->
            AWAIT_A(_id, break)
        od;
        AWAIT_A(_id, assert(pxTCB == NULL_byte || listLIST_IS_EMPTY(LISTs[pxDelayedTaskList]));
            pxTCB = NULL_byte /* reset variable as soon as possible */);

        // FIXME: uxPendedCounts

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
    AWAIT_A(_id, assert(xSwitchRequired == false && local_var == NULL_byte));
    if
    :: SELE(_id, uxSchedulerSuspended == 0) ->
        /* There is only one delayed task list. */

        do
        :: SELE(_id, listLIST_IS_EMPTY(LISTs[pxDelayedTaskList]) == false) ->
            /* FIXME: timed out */
            /* The delayed list is not empty. We ignore the effect of time in
             * the model. Thus, the delayed tasks are added back to the ready
             * list as soon as possible. */
            AWAIT_D(_id, pxTCB = listGET_OWNER_OF_HEAD_ENTRY(LISTs[pxDelayedTaskList]));
            /* FIXME: do not need to compare the item value here */

//            if
//            :: SELE(_PID, listGET_LIST_ITEM_VALUE(TCB(pxTCB).ListItems[xState]) > 0) ->
//                AWAIT_D(_id, listSET_LIST_ITEM_VALUE(TCB(pxTCB).ListItems[xState], listGET_LIST_ITEM_VALUE(TCB(pxTCB).ListItems[xState]) - 1));
//                AWAIT_A(_id, pxTCB = NULL_byte; break)
//            :: ELSE(_PID, listGET_LIST_ITEM_VALUE(TCB(pxTCB).ListItems[xState]) > 0)
//            fi;

            AWAIT_D(_id, uxListRemove(LISTs[listLIST_ITEM_CONTAINER(TCB(pxTCB).ListItems[xState])], IDX_TCB(pxTCB), xState, _));

            if
            :: SELE(_id, listLIST_ITEM_CONTAINER(TCB(pxTCB).ListItems[xEvent]) != NULL_byte) ->
                AWAIT_D(_id, uxListRemove(LISTs[listLIST_ITEM_CONTAINER(TCB(pxTCB).ListItems[xEvent])], IDX_TCB(pxTCB), xEvent, _));
            :: ELSE(_id, listLIST_ITEM_CONTAINER(TCB(pxTCB).ListItems[xEvent]) != NULL_byte)
            fi;

            prvAddTaskToReadyList(_id, pxTCB);

            #if (configUSE_PREEMPTION == 1)
            if
            :: SELE(_id, TCB(pxTCB).uxPriority >= TCB(pxCurrentTCB).uxPriority) ->
                AWAIT_D(_id, xSwitchRequired = true)
            :: ELSE(_id, TCB(pxTCB).uxPriority >= TCB(pxCurrentTCB).uxPriority)
            fi
            #endif
        :: ELSE(_id, listLIST_IS_EMPTY(LISTs[pxDelayedTaskList]) == false) ->
            /* The delayed list is empty. */
            AWAIT_A(_id, pxTCB = NULL_byte; break)
        od;

        #if ((configUSE_PREEMPTION == 1) && (configUSE_TIME_SLICING == 1))
        if
        :: SELE(_id, listLIST_LENGTH_IS_EXCEEDING_ONE(LISTs[pxReadyTasksLists + TCB(pxCurrentTCB).uxPriority])) ->
            AWAIT_D(_id, xSwitchRequired = true)
        :: ELSE(_id, listLIST_LENGTH_IS_EXCEEDING_ONE(LISTs[pxReadyTasksLists + TCB(pxCurrentTCB).uxPriority]))
        fi;
        #endif
    :: ELSE(_id, uxSchedulerSuspended == 0) /* TODO: pended ticks */
    fi;

    #if (configUSE_PREEMPTION == 1)
    if
    :: SELE(_id, xYieldPending != false) ->
        AWAIT_D(_id, xSwitchRequired = true)
    :: ELSE(_id, xYieldPending != false)
    fi
    #endif
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
    AWAIT_D(_id, vListInsert(pxEventList, EventListContainer, IDX_TCB(pxCurrentTCB), xEvent, temp_var));
    prvAddCurrentTaskToDelayedList(_id, xTicksToWait, true, temp_var)
}

inline xTaskRemoveFromEventList(_id, pxUnblockedTCB, pxEventList, xReturn)
{
    AWAIT_D(_id, pxUnblockedTCB = listGET_OWNER_OF_HEAD_ENTRY(pxEventList); assert(pxUnblockedTCB != NULL_byte));
    AWAIT_D(_id, uxListRemove(pxEventList, IDX_TCB(pxUnblockedTCB), xEvent, _));

    if
    :: SELE(_id, uxSchedulerSuspended == 0) ->
        AWAIT_D(_id, uxListRemove(LISTs[listLIST_ITEM_CONTAINER(TCB(pxUnblockedTCB).ListItems[xState])], IDX_TCB(pxUnblockedTCB), xState, _));
        prvAddTaskToReadyList(_id, pxUnblockedTCB)
    :: ELSE(_id, uxSchedulerSuspended == 0) ->
        AWAIT_D(_id, vListInsertEnd(LISTs[xPendingReadyList], xPendingReadyList, IDX_TCB(pxUnblockedTCB), xEvent))
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

// TODO: is the modeling of the idle task necessary?
portTASK_FUNCTION(IDLE_TASK)
{
    byte idx;
    byte local_var = NULL_byte;
    assert(_PID == IDLE_TASK_ID);
loop:
    // FIXME: ifdef INCLUDE_vTaskDelete then prvCheckTasksWaitingTermination

    #if (configUSE_PREEMPTION == 0)
        taskYIELD(_PID, local_var);
    #endif

    #if ((configUSE_PREEMPTION == 1) && (configIDLE_SHOULD_YIELD == 1))
        if
        :: SELE(_PID, listLIST_LENGTH_IS_EXCEEDING_ONE(LISTs[pxReadyTasksLists + tskIDLE_PRIORITY])) ->
            taskYIELD(_PID, local_var)
        :: ELSE(_PID, listLIST_LENGTH_IS_EXCEEDING_ONE(LISTs[pxReadyTasksLists + tskIDLE_PRIORITY]))
        fi;
    #endif

    // TODO: configUSE_TICKLESS_IDLE != 0

    AWAIT_A(_PID, goto loop)
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
            :: SELE(_id, listIS_CONTAINED_WITHIN(pxReadyTasksLists + TCB(pxMutexHolder).uxPriority, TCB(pxMutexHolder).ListItems[xState]) != false) ->
                AWAIT_D(_id, uxListRemove(LISTs[listLIST_ITEM_CONTAINER(TCB(pxMutexHolder).ListItems[xState])], IDX_TCB(pxMutexHolder), xState, temp_var));
                if
                :: atomic { SELE(_id, temp_var == 0) -> temp_var = NULL_byte };
                    taskRESET_READY_PRIORITY(_id, TCB(pxMutexHolder).uxPriority)
                :: atomic { ELSE(_id, temp_var == 0) -> temp_var = NULL_byte }
                fi;

                AWAIT_D(_id, TCB(pxMutexHolder).uxPriority = TCB(pxCurrentTCB).uxPriority);
                prvAddTaskToReadyList(_id, pxMutexHolder)
            :: ELSE(_id, listIS_CONTAINED_WITHIN(pxReadyTasksLists + TCB(pxMutexHolder).uxPriority, TCB(pxMutexHolder).ListItems[xState]) != false) ->
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
                AWAIT_D(_id, uxListRemove(LISTs[listLIST_ITEM_CONTAINER(TCB(pxMutexHolder).ListItems[xState])], IDX_TCB(pxMutexHolder), xState, temp_var));
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
                :: atomic { SELE(_id, listIS_CONTAINED_WITHIN(pxReadyTasksLists + uxPriorityUsedOnEntry, TCB(pxMutexHolder).ListItems[xState])) ->
                    assert(uxPriorityUsedOnEntry != NULL_byte) };
                    AWAIT_D(_id, uxListRemove(LISTs[listLIST_ITEM_CONTAINER(TCB(pxMutexHolder).ListItems[xState])], IDX_TCB(pxMutexHolder), xState, _));
                    if
                    :: atomic { SELE(_id, listLIST_IS_EMPTY(LISTs[pxReadyTasksLists + uxPriorityUsedOnEntry])) -> uxPriorityUsedOnEntry = NULL_byte };
                        taskRECORD_READY_PRIORITY(_id, TCB(pxMutexHolder).uxPriority)
                    :: atomic { ELSE(_id, listLIST_IS_EMPTY(LISTs[pxReadyTasksLists + uxPriorityUsedOnEntry])) -> uxPriorityUsedOnEntry = NULL_byte }
                    fi;

                    prvAddTaskToReadyList(_id, pxMutexHolder)
                :: atomic { ELSE(_id, listIS_CONTAINED_WITHIN(pxReadyTasksLists + uxPriorityUsedOnEntry, TCB(pxMutexHolder).ListItems[xState])) ->
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
    AWAIT_D(_id, uxListRemove(LISTs[listLIST_ITEM_CONTAINER(TCB(pxCurrentTCB).ListItems[xState])], IDX_TCB(pxCurrentTCB), xState, temp_var));
    if
    :: atomic { SELE(_id, temp_var == 0) -> temp_var = NULL_byte };
        portRESET_READY_PRIORITY(_id, TCB(now.pxCurrentTCB).uxPriority, uxTopReadyPriority)
    :: atomic { ELSE(_id, temp_var == 0) -> temp_var = NULL_byte }
    fi;

#if (INCLUDE_vTaskSuspend == 1)
    if
    :: SELE(_id, xTicksToWait == portMAX_DELAY && xCanBlockIndefinitely != false) ->
        AWAIT_D(_id, vListInsertEnd(LISTs[xSuspendedTaskList], xSuspendedTaskList, IDX_TCB(pxCurrentTCB), xState))
    :: ELSE(_id, xTicksToWait == portMAX_DELAY && xCanBlockIndefinitely != false) ->
        //AWAIT_D(_id, listSET_LIST_ITEM_VALUE(TCB(pxCurrentTCB).ListItems[xState], xTicksToWait))
        AWAIT_D(_id, vListInsert(LISTs[pxDelayedTaskList], pxDelayedTaskList, IDX_TCB(pxCurrentTCB), xState, temp_var))
    fi;
#else
    //AWAIT_D(_id, listSET_LIST_ITEM_VALUE(TCB(pxCurrentTCB).ListItems[xState], xTicksToWait))
    AWAIT_D(_id, vListInsert(LISTs[pxDelayedTaskList], pxDelayedTaskList, IDX_TCB(pxCurrentTCB), xState, temp_var));
#endif
}

#endif
