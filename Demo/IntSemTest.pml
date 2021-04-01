/* FreeRTOS/Demo/Common/Minimal/IntSemTest.c */

#define promela_TASK_NUMBER     3
#define promela_QUEUE_NUMBER    3

#define FIRST_TASK              promela_EXP_NUMBER
#define IDLE_TASK_ID            (FIRST_TASK + promela_TASK_NUMBER)

#define RUN_ALL_TASKS(stmts)    \
    atomic {            \
        stmts;          \
        run IntMuS();   \
        run IntMuM();   \
        run IntCnt();   \
    }

#include "../FreeRTOS/include/Queue_Declarator.pml"

SemaphoreDeclarator(1, byte);
SemaphoreDeclarator(3, byte);

SemaphoreHandle_t(xISRMutex, 1, byte);
SemaphoreHandle_t(xISRCountingSemaphore, 3, byte);
SemaphoreHandle_t(xMasterSlaveMutex, 1, byte);
bool xOkToGiveMutex = false, xOkToGiveCountingSemaphore = false;

#include "../FreeRTOS/queueFromISR.pml"

local byte xTimeNow = 0; /* Only for SysTick_Handler */
#define intsemINTERRUPT_MUTEX_GIVE_PERIOD   20
#define intsemINTERRUPT_MUTEX_GIVE_PERIOD_D 40  /* Double */
#define intsemINTERRUPT_MUTEX_GIVE_PERIOD_Q 80  /* Quardruple (intsemMAX_COUNT + 1) */

#define configUSE_TICK_HOOK 1
#define vApplicationTickHook() /* vInterruptSemaphorePeriodicTest */ \
    AWAIT_DS(_PID, xTimeNow = ((xOkToGiveMutex || xOkToGiveCountingSemaphore) -> xTimeNow + 1 : 0)); \
    if \
    :: SELE_AS(_PID, xTimeNow >= intsemINTERRUPT_MUTEX_GIVE_PERIOD, xTimeNow = 0); \
        if \
        :: SELE_AS(_PID, xOkToGiveMutex != false); \
            xQueueGiveFromISR(_PID, xISRMutex, pxTCB); \
        :: ELSE_AS(_PID, xOkToGiveMutex != false); \
        fi; \
        if \
        :: SELE_AS(_PID, xOkToGiveCountingSemaphore != false); \
            xQueueGiveFromISR(_PID, xISRCountingSemaphore, pxTCB); \
        :: ELSE_AS(_PID, xOkToGiveCountingSemaphore != false); \
        fi; \
    :: ELSE_AS(_PID, xTimeNow >= intsemINTERRUPT_MUTEX_GIVE_PERIOD); \
    fi

#include "../FreeRTOS.pml"
#include "../FreeRTOS/tasks.pml"
#include "../FreeRTOS/semphr.h.pml"

#define intsemMASTER_PRIORITY   (tskIDLE_PRIORITY)
#define intsemSLAVE_PRIORITY    (tskIDLE_PRIORITY + 1)

#define intsemNO_BLOCK  0
#define intsemMAX_COUNT 3

#define xSlaveHandle    (FIRST_TASK)

proctype IntMuS()
{
    byte idx;
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bool local_bit = false, local_xReturn = false, local_xIsTimeOut = false;
    assert(_PID == xSlaveHandle);
do
::  vTaskSuspend(_PID, NULL_byte, local_var1, local_var2);

    xSemaphoreTake(xMasterSlaveMutex, portMAX_DELAY, local_xReturn, local_bit, local_xIsTimeOut, local_var1, local_var2, _PID);
    AWAIT(_PID, assert(local_xReturn == true); local_xReturn = false);

    xSemaphoreGive(xMasterSlaveMutex, local_xReturn, local_xIsTimeOut, local_var1, local_var2, _PID);
    AWAIT(_PID, assert(local_xReturn == true); local_xReturn = false);
od
}

#define eTaskGetState_eBlocked(pxTCB) \
    (listLIST_ITEM_CONTAINER(TCB(pxTCB).ListItems[xState]) == CID_DELAYED_TASK) || \
    (listLIST_ITEM_CONTAINER(TCB(pxTCB).ListItems[xState]) == CID_SUSPENDED_TASK && listLIST_ITEM_CONTAINER(TCB(pxTCB).ListItems[xEvent]) != NULL_byte)

inline prvTakeAndGiveInTheSameOrder(_id, xReturn, temp_bit, temp_xIsTimeOut, temp_var1, temp_var2)
{
    AWAIT(_id,
        assert(listLIST_ITEM_CONTAINER(TCB(xSlaveHandle).ListItems[xState]) == CID_SUSPENDED_TASK);
        assert(uxTaskPriorityGet(NULL_byte) == intsemMASTER_PRIORITY)
    );

    xSemaphoreTake_NB(xMasterSlaveMutex, intsemNO_BLOCK, xReturn, temp_bit, temp_xIsTimeOut, temp_var1, temp_var2, _id);
    AWAIT(_id, assert(xReturn == true); xReturn = false);

    vTaskResume(_id, xSlaveHandle, temp_bit, temp_var1);

    AWAIT(_id,
        assert(eTaskGetState_eBlocked(xSlaveHandle));
        assert(uxTaskPriorityGet(NULL_byte) == intsemSLAVE_PRIORITY)
    );

    AWAIT(_id, xOkToGiveMutex = true);
    xSemaphoreTake(xISRMutex, intsemINTERRUPT_MUTEX_GIVE_PERIOD_D, xReturn, temp_bit, temp_xIsTimeOut, temp_var1, temp_var2, _id);
    AWAIT(_id, assert(xReturn == true); xReturn = false);
    AWAIT(_id, xOkToGiveMutex = false);

    xSemaphoreTake_NB(xISRMutex, intsemNO_BLOCK, xReturn, temp_bit, temp_xIsTimeOut, temp_var1, temp_var2, _id);
    AWAIT(_id, assert(xReturn == false));

    AWAIT(_id, assert(uxTaskPriorityGet(NULL_byte) == intsemSLAVE_PRIORITY));

    xSemaphoreGive(xISRMutex, xReturn, temp_xIsTimeOut, temp_var1, temp_var2, _id);
    AWAIT(_id, assert(xReturn == true); xReturn = false);

    AWAIT(_id, assert(uxTaskPriorityGet(NULL_byte) == intsemSLAVE_PRIORITY));

    xSemaphoreGive(xMasterSlaveMutex, xReturn, temp_xIsTimeOut, temp_var1, temp_var2, _id);
    AWAIT(_id, assert(xReturn == true); xReturn = false);

    AWAIT(_id,
        assert(uxTaskPriorityGet(NULL_byte) == intsemMASTER_PRIORITY);
        assert(listLIST_ITEM_CONTAINER(TCB(xSlaveHandle).ListItems[xState]) == CID_SUSPENDED_TASK)
    );

    xQueueGenericReset(_id, xISRMutex, temp_var1, temp_bit)
}

inline prvTakeAndGiveInTheOppositeOrder(_id, xReturn, temp_bit, temp_xIsTimeOut, temp_var1, temp_var2)
{
    AWAIT(_id,
        assert(listLIST_ITEM_CONTAINER(TCB(xSlaveHandle).ListItems[xState]) == CID_SUSPENDED_TASK);
        assert(uxTaskPriorityGet(NULL_byte) == intsemMASTER_PRIORITY)
    );

    xSemaphoreTake_NB(xMasterSlaveMutex, intsemNO_BLOCK, xReturn, temp_bit, temp_xIsTimeOut, temp_var1, temp_var2, _id);
    AWAIT(_id, assert(xReturn == true); xReturn = false);

    vTaskResume(_id, xSlaveHandle, temp_bit, temp_var1);

    AWAIT(_id,
        assert(eTaskGetState_eBlocked(xSlaveHandle));
        assert(uxTaskPriorityGet(NULL_byte) == intsemSLAVE_PRIORITY)
    );

    AWAIT(_id, xOkToGiveMutex = true);
    xSemaphoreTake(xISRMutex, intsemINTERRUPT_MUTEX_GIVE_PERIOD_D, xReturn, temp_bit, temp_xIsTimeOut, temp_var1, temp_var2, _id);
    AWAIT(_id, assert(xReturn == true); xReturn = false);
    AWAIT(_id, xOkToGiveMutex = false);

    xSemaphoreTake_NB(xISRMutex, intsemNO_BLOCK, xReturn, temp_bit, temp_xIsTimeOut, temp_var1, temp_var2, _id);
    AWAIT(_id, assert(xReturn == false));

    AWAIT(_id, assert(uxTaskPriorityGet(NULL_byte) == intsemSLAVE_PRIORITY));

    xSemaphoreGive(xMasterSlaveMutex, xReturn, temp_xIsTimeOut, temp_var1, temp_var2, _id);
    AWAIT(_id, assert(xReturn == true); xReturn = false);

    AWAIT(_id, assert(uxTaskPriorityGet(NULL_byte) == intsemSLAVE_PRIORITY));

    xSemaphoreGive(xISRMutex, xReturn, temp_xIsTimeOut, temp_var1, temp_var2, _id);
    AWAIT(_id, assert(xReturn == true); xReturn = false);

    AWAIT(_id, assert(uxTaskPriorityGet(NULL_byte) == intsemMASTER_PRIORITY));

    xQueueGenericReset(_id, xISRMutex, temp_var1, temp_bit)
}

proctype IntMuM()
{
    byte idx;
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bool local_xReturn = false, local_bit = false, local_xIsTimeOut = false;
    assert(_PID == (FIRST_TASK + 1));
do
::  prvTakeAndGiveInTheSameOrder(_PID, local_xReturn, local_bit, local_xIsTimeOut, local_var1, local_var2);

    vTaskDelay(_PID, intsemINTERRUPT_MUTEX_GIVE_PERIOD, local_bit, local_var1, local_var2);

    prvTakeAndGiveInTheOppositeOrder(_PID, local_xReturn, local_bit, local_xIsTimeOut, local_var1, local_var2);

    vTaskDelay(_PID, intsemINTERRUPT_MUTEX_GIVE_PERIOD, local_bit, local_var1, local_var2);
od
}

proctype IntCnt()
{
    byte idx;
    byte local_var1 = NULL_byte, local_var2 = NULL_byte, local_var3 = NULL_byte;
    bool local_xReturn = false, local_bit = false, local_xIsTimeOut = false;

    byte xCount = 0;
    assert(_PID == (FIRST_TASK + 2));
do
::  AWAIT(_PID, assert(uxQueueMessagesWaiting(xISRCountingSemaphore) == 0));

    AWAIT(_PID, xOkToGiveCountingSemaphore = true);
    vTaskDelay(_PID, intsemINTERRUPT_MUTEX_GIVE_PERIOD_Q, local_bit, local_var1, local_var2);
    AWAIT(_PID, xOkToGiveCountingSemaphore = false);

    AWAIT(_PID,
        assert(uxQueueMessagesWaiting(xISRCountingSemaphore) == intsemMAX_COUNT);
        /* uxQueueSpacesAvailable(xISRCountingSemaphore) == 0 */
        assert((xISRCountingSemaphore.uxLength - xISRCountingSemaphore.uxMessagesWaiting) == 0)
    );

    do
    :: xSemaphoreTake_NB(xISRCountingSemaphore, 0, local_xReturn, local_bit, local_xIsTimeOut, local_var1, local_var2, _PID);
       AWAIT(_PID,
        if
        :: local_xReturn == true -> local_xReturn = false; xCount = xCount + 1
        :: else -> break
        fi
       )
    od;

    AWAIT(_PID, assert(xCount == intsemMAX_COUNT); xCount = 0);

    vTaskPrioritySet(_PID, NULL_byte, configMAX_PRIORITIES - 1, local_var1, local_bit, local_var2, local_var3);

    AWAIT(_PID, xOkToGiveCountingSemaphore = true);
    xSemaphoreTake(xISRCountingSemaphore, portMAX_DELAY, local_xReturn, local_bit, local_xIsTimeOut, local_var1, local_var2, _PID);
    xSemaphoreTake(xISRCountingSemaphore, portMAX_DELAY, local_xReturn, local_bit, local_xIsTimeOut, local_var1, local_var2, _PID);
    AWAIT(_PID, xOkToGiveCountingSemaphore = false);

    vTaskPrioritySet(_PID, NULL_byte, tskIDLE_PRIORITY, local_var1, local_bit, local_var2, local_var3);
od
}

init
{
    byte idx;
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bool local_xIsTimeOut = false;

    xSemaphoreCreateMutex(xISRMutex, 0, local_xIsTimeOut, local_var1, local_var2, EP);
    skip;

    d_step {
        xSemaphoreCreateCounting_fixed(xISRCountingSemaphore, 1, intsemMAX_COUNT, 0);
    };

    xSemaphoreCreateMutex(xMasterSlaveMutex, 2, local_xIsTimeOut, local_var1, local_var2, EP);
    skip;

    d_step {
        prvInitialiseTaskLists(local_var1);

        xTaskCreate_fixed(xSlaveHandle, intsemSLAVE_PRIORITY);
        xTaskCreate_fixed(FIRST_TASK + 1, intsemMASTER_PRIORITY);
        xTaskCreate_fixed(FIRST_TASK + 2, tskIDLE_PRIORITY);
    };

    vTaskStartScheduler(EP, local_var1);

    /* Start the IDLE TASK */
    vTaskIDLE_TASK_BODY(IDLE_TASK_ID, local_var1)
}
