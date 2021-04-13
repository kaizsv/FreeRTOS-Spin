/* FreeRTOS/Demo/Common/Minimal/GenQTest.c */
/* INCLUDE_xTaskAbortDelay is not defined */

#define APP_DEFINED_PRIORITY
#define configMAX_PRIORITIES    4

#define promela_TASK_NUMBER     4
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
    }

#include "../FreeRTOS.pml"
#include "../FreeRTOS/tasks.pml"
#include "../FreeRTOS/semphr.h.pml"

#ifdef LTL
    #include "../property/GenQTest.ltl"
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
QueueDeclarator(5, byte);

QueueHandle_t(xQUEUE, 5, byte);
SemaphoreHandle_t(xMUTEX, 1, byte);
SemaphoreHandle_t(xLOCALMUTEX, 1, byte);

byte ulLoopCounter = 0;
byte ulGuardedVariable = 0;

#define INC_VAR_AND_WRAP_AROUND(var)    (var + 1) % 6

proctype GenQ()
{
    byte idx;
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bool local_xReturn = false, local_xIsTimeOut = false;

    byte ulLoopCounterSnapshot = 0, ulData = 0, ulData2 = 0;
    assert(_PID == FIRST_TASK);
do
::  AWAIT(_PID, ulLoopCounterSnapshot = ulLoopCounter);
    xQueueSendToFront_NB(xQUEUE, ulLoopCounterSnapshot, intsemNO_BLOCK, _, local_xIsTimeOut, local_var1, local_var2, _PID);

    AWAIT(_PID, ulLoopCounterSnapshot = 0; assert(uxQueueMessagesWaiting(xQUEUE) == 1));

    xQueueReceive_NB(xQUEUE, ulData, intsemNO_BLOCK, local_xReturn, local_xIsTimeOut, local_var1, local_var2, _PID);
    AWAIT(_PID, assert(local_xReturn == true); local_xReturn = false);

    AWAIT(_PID, assert(ulLoopCounter == ulData && uxQueueMessagesWaiting(xQUEUE) == 0);
        ulData = 0);

    AWAIT(_PID, ulLoopCounterSnapshot = ulLoopCounter);
    xQueueSendToBack_NB(xQUEUE, ulLoopCounterSnapshot, intsemNO_BLOCK, _, local_xIsTimeOut, local_var1, local_var2, _PID);

    AWAIT(_PID, ulLoopCounterSnapshot = 0; assert(uxQueueMessagesWaiting(xQUEUE) == 1));

    xQueueReceive_NB(xQUEUE, ulData, intsemNO_BLOCK, local_xReturn, local_xIsTimeOut, local_var1, local_var2, _PID);
    AWAIT(_PID, assert(local_xReturn == true); local_xReturn = false);

    AWAIT(_PID, assert(uxQueueMessagesWaiting(xQUEUE) == 0 && ulLoopCounter == ulData);
        ulData = 0);

    #if (configUSE_PREEMPTION == 0)
    taskYIELD(_PID, local_var1);
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
    taskYIELD(_PID, local_var1);
    #endif

    for (ulData: 0 .. (genqQUEUE_LENGTH - 1)) {
        xQueuePeek_NB(_PID, xQUEUE, ulData2, intsemNO_BLOCK, local_xReturn, local_xIsTimeOut, local_var1, local_var2);
        AWAIT(_PID, assert(local_xReturn == true); local_xReturn = false;
            assert(ulData == ulData2); ulData2 = 0);

        xQueueReceive_NB(xQUEUE, ulData2, intsemNO_BLOCK, local_xReturn, local_xIsTimeOut, local_var1, local_var2, _PID);
        AWAIT(_PID, assert(local_xReturn == true); local_xReturn = false;
            assert(ulData == ulData2); ulData2 = 0);
    }

    AWAIT(_PID, ulData = 0; assert(uxQueueMessagesWaiting(xQUEUE) == 0));

    #if (configUSE_PREEMPTION == 0)
    taskYIELD(_PID, local_var1);
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
        xQueueReceive_NB(xQUEUE, ulData2, intsemNO_BLOCK, local_xReturn, local_xIsTimeOut, local_var1, local_var2, _PID);
        AWAIT(_PID, assert(local_xReturn == true); local_xReturn = false;
            assert(ulData == ulData2); ulData2 = 0);
    }

    AWAIT(_PID, ulData = 0; assert(uxQueueMessagesWaiting(xQUEUE) == 0));

running:
    AWAIT(_PID, ulLoopCounter = INC_VAR_AND_WRAP_AROUND(ulLoopCounter));
od
}

inline prvTakeTwoMutexesReturnInDifferentOrder(_id, xMutex, xLocalMutex, xReturn, temp_bool, temp_xIsTimeOut, temp_var1, temp_var2)
{
    xSemaphoreTake(xMutex, intsemNO_BLOCK, xReturn, temp_bool, temp_xIsTimeOut, temp_var1, temp_var2, _id);
    AWAIT(_id, assert(xReturn == true); xReturn = false);

    AWAIT(_id, ulGuardedVariable = 0);

    AWAIT(_id, assert(uxTaskPriorityGet(NULL_byte) == genqMUTEX_LOW_PRIORITY));

    vTaskResume(_id, xHighPriorityMutexTask, temp_bool, temp_var1);

    #if (configUSE_PREEMPTION == 0)
    taskYIELD(_id, local_var1);
    #endif

    AWAIT(_id, assert(uxTaskPriorityGet(NULL_byte) == genqMUTEX_HIGH_PRIORITY));

    vTaskPrioritySet(_id, NULL_byte, genqMUTEX_TEST_PRIORITY, temp_var1, temp_bool, temp_var2);
    AWAIT(_id, assert(uxTaskPriorityGet(NULL_byte) == genqMUTEX_HIGH_PRIORITY));

    vTaskResume(_id, xMediumPriorityMutexTask, temp_bool, temp_var1);

    AWAIT(_id, assert(ulGuardedVariable == 0));

    xSemaphoreTake(xLocalMutex, intsemNO_BLOCK, xReturn, temp_bool, temp_xIsTimeOut, temp_var1, temp_var2, _id);
    AWAIT(_id, assert(xReturn == true); xReturn = false);

    xSemaphoreGive(xMutex, xReturn, temp_bool, temp_var1, temp_var2, _id);
    AWAIT(_id, assert(xReturn == true); xReturn = false);

    #if (configUSE_PREEMPTION == 0)
    taskYIELD(_id, local_var1);
    #endif

    AWAIT(_id, assert(ulGuardedVariable == 0));

    AWAIT(_id, assert(uxTaskPriorityGet(NULL_byte) == genqMUTEX_HIGH_PRIORITY));

    xSemaphoreGive(xLocalMutex, xReturn, temp_bool, temp_var1, temp_var2, _id);
    AWAIT(_id, assert(xReturn == true); xReturn = false);

    #if (configUSE_PREEMPTION == 0)
    taskYIELD(_id, local_var1);
    #endif

    AWAIT(_id, assert(ulGuardedVariable == 1));

    AWAIT(_id, assert(uxTaskPriorityGet(NULL_byte) == genqMUTEX_TEST_PRIORITY));

    vTaskPrioritySet(_id, NULL_byte, genqMUTEX_LOW_PRIORITY, temp_var1, temp_bool, temp_var2);
}

inline prvTakeTwoMutexesReturnInSameOrder(_id, xMutex, xLocalMutex, xReturn, temp_bool, temp_xIsTimeOut, temp_var1, temp_var2)
{
    xSemaphoreTake(xMutex, intsemNO_BLOCK, xReturn, temp_bool, temp_xIsTimeOut, temp_var1, temp_var2, _id);
    AWAIT(_id, assert(xReturn == true); xReturn = false);

    AWAIT(_id, ulGuardedVariable = 0);

    AWAIT(_id, assert(uxTaskPriorityGet(NULL_byte) == genqMUTEX_LOW_PRIORITY));

    vTaskResume(_id, xHighPriorityMutexTask, temp_bool, temp_var1);

    #if (configUSE_PREEMPTION == 0)
    taskYIELD(_id, local_var1);
    #endif

    AWAIT(_id, assert(uxTaskPriorityGet(NULL_byte) == genqMUTEX_HIGH_PRIORITY));

    vTaskResume(_id, xMediumPriorityMutexTask, temp_bool, temp_var1);

    AWAIT(_id, assert(ulGuardedVariable == 0));

    xSemaphoreTake(xLocalMutex, intsemNO_BLOCK, xReturn, temp_bool, temp_xIsTimeOut, temp_var1, temp_var2, _id);
    AWAIT(_id, assert(xReturn == true); xReturn = false);

    xSemaphoreGive(xLocalMutex, xReturn, temp_bool, temp_var1, temp_var2, _id);
    AWAIT(_id, assert(xReturn == true); xReturn = false);

    #if (configUSE_PREEMPTION == 0)
    taskYIELD(_id, local_var1);
    #endif

    AWAIT(_id, assert(ulGuardedVariable == 0));

    AWAIT(_id, assert(uxTaskPriorityGet(NULL_byte) == genqMUTEX_HIGH_PRIORITY));

    xSemaphoreGive(xMutex, xReturn, temp_bool, temp_var1, temp_var2, _id);
    AWAIT(_id, assert(xReturn == true); xReturn = false);

    #if (configUSE_PREEMPTION == 0)
    taskYIELD(_id, local_var1);
    #endif

    AWAIT(_id, assert(ulGuardedVariable == 1));

    AWAIT(_id, assert(uxTaskPriorityGet(NULL_byte) == genqMUTEX_LOW_PRIORITY));
}

proctype MuLow()
{
    byte idx;
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bool local_bit = false, local_xReturn = false, local_xIsTimeOut = false;
    assert(_PID == (FIRST_TASK + 1));
do
::  prvTakeTwoMutexesReturnInDifferentOrder(_PID, xMUTEX, xLOCALMUTEX, local_xReturn, local_bit, local_xIsTimeOut, local_var1, local_var2);

running:
    #if (configUSE_PREEMPTION == 0)
    taskYIELD(_PID, local_var1);
    #endif

    prvTakeTwoMutexesReturnInSameOrder(_PID, xMUTEX, xLOCALMUTEX, local_xReturn, local_bit, local_xIsTimeOut, local_var1, local_var2);

    #if (configUSE_PREEMPTION == 0)
    taskYIELD(_PID, local_var1);
    #endif
od
}

proctype MuMed()
{
    byte idx;
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    assert(_PID == xMediumPriorityMutexTask);
do
::  vTaskSuspend(_PID, NULL_byte, local_var1, local_var2);
    AWAIT(_PID, ulGuardedVariable = INC_VAR_AND_WRAP_AROUND(ulGuardedVariable));
od
}

proctype MuHigh()
{
    byte idx;
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bool local_bit = false, local_xReturn = false, local_xIsTimeOut = false;
    assert(_PID == xHighPriorityMutexTask);
do
::  vTaskSuspend(_PID, NULL_byte, local_var1, local_var2);
    xSemaphoreTake(xMUTEX, portMAX_DELAY, local_xReturn, local_bit, local_xIsTimeOut, local_var1, local_var2, _PID);
    AWAIT(_PID, assert(local_xReturn == true); local_xReturn = false);

    xSemaphoreGive(xMUTEX, local_xReturn, local_xIsTimeOut, local_var1, local_var2, _PID);
    AWAIT(_PID, assert(local_xReturn == true); local_xReturn = false);
od
}

init
{
    byte idx;
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bool local_xIsTimeOut = false;

    d_step {
        xQueueCreate(xQUEUE, 0, 5);
    };

    xSemaphoreCreateMutex(xMUTEX, 1, local_xIsTimeOut, local_var1, local_var2, EP);
    xSemaphoreCreateMutex(xLOCALMUTEX, 2, local_xIsTimeOut, local_var1, local_var2, EP);
    skip;

    d_step {
        prvInitialiseTaskLists(local_var1);

        xTaskCreate_fixed(FIRST_TASK, tskIDLE_PRIORITY);
        xTaskCreate_fixed(FIRST_TASK + 1, genqMUTEX_LOW_PRIORITY);
        xTaskCreate_fixed(xMediumPriorityMutexTask, genqMUTEX_MED_PRIORITY);
        xTaskCreate_fixed(xHighPriorityMutexTask, genqMUTEX_HIGH_PRIORITY);
    };

    vTaskStartScheduler(EP, local_var1);

    /* Start the IDLE TASK */
    vTaskIDLE_TASK_BODY(IDLE_TASK_ID, local_var1)
}
