/* FreeRTOS/Demo/Common/Minimal/countsem.c */

#define promela_TASK_NUMBER     2
#define promela_QUEUE_NUMBER    2

#define FIRST_TASK              promela_EXP_NUMBER
#define IDLE_TASK_ID            (FIRST_TASK + promela_TASK_NUMBER)

#define RUN_ALL_TASKS(stmts) \
    atomic {        \
        stmts;      \
        run CNT1(); \
        run CNT2(); \
    }

#ifdef CORRECTION
#include "../platform/stm32p103_FreeRTOSConfig.pml"
    #if (configUSE_PREEMPTION == 1) && (configUSE_TIME_SLICING == 1)
        #undef configIDLE_SHOULD_YIELD
        #define configIDLE_SHOULD_YIELD 0
    #endif
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

inline prvDecrementSemaphoreCount(_id, ux, xSemaphore, xReturn, temp_bool, temp_xIsTimeOut, temp_var1, temp_var2)
{
    xSemaphoreGive(xSemaphore, xReturn, temp_xIsTimeOut, temp_var1, temp_var2, _id);
    AWAIT(_id, assert(xReturn == false));

    for (ux: 0 .. (countMAX_COUNT_VALUE - 1)) {
        AWAIT(_id, assert(uxSemaphoreGetCount(xSemaphore) == (countMAX_COUNT_VALUE - (ux))));

        xSemaphoreTake_NB(xSemaphore, countDONT_BLOCK, xReturn, temp_bool, temp_xIsTimeOut, temp_var1, temp_var2, _id);
        AWAIT(_id, assert(xReturn == true); xReturn = false);
runningDec:
        AWAIT(_id, skip)
    }

#if (configUSE_PREEMPTION == 0)
    taskYIELD(_PID, temp_var1);
#endif

    AWAIT(_id, ux = 0; assert(uxSemaphoreGetCount(xSemaphore) == 0));
    xSemaphoreTake_NB(xSemaphore, countDONT_BLOCK, xReturn, temp_bool, temp_xIsTimeOut, temp_var1, temp_var2, _id);
    AWAIT(_id, assert(xReturn == false))
}

inline prvIncrementSemaphoreCount(_id, ux, xSemaphore, xReturn, temp_bool, temp_xIsTimeOut, temp_var1, temp_var2)
{
    xSemaphoreTake_NB(xSemaphore, countDONT_BLOCK, xReturn, temp_bool, temp_xIsTimeOut, temp_var1, temp_var2, _id);
    AWAIT(_id, assert(xReturn == false));

    for (ux: 0 .. (countMAX_COUNT_VALUE - 1)) {
        AWAIT(_id, assert(uxSemaphoreGetCount(xSemaphore) == ux));

        xSemaphoreGive(xSemaphore, xReturn, temp_xIsTimeOut, temp_var1, temp_var2, _id);
        AWAIT(_id, assert(xReturn == true); xReturn = false);
runningInc:
        AWAIT(_id, skip)
    }

#if (configUSE_PREEMPTION == 0)
    taskYIELD(_PID, temp_var1);
#endif

    xSemaphoreGive(xSemaphore, xReturn, temp_xIsTimeOut, temp_var1, temp_var2, _id);
    AWAIT(_id, ux = 0; assert(xReturn == false));
}

proctype CNT1()
{
    byte local_var1 = NULL_byte, local_var2 = NULL_byte, ux = 0;
    bool local_xReturn = false, local_bit = false, local_xIsTimeOut = false;
    assert(_PID == FIRST_TASK);
    // pxParameter->uxExpectedStartCount == countSTART_AT_MAX_COUNT
    // prvDecrementSemaphoreCount: remove the running label
    xSemaphoreGive(xP1_xSemaphore, local_xReturn, local_xIsTimeOut, local_var1, local_var2, _PID);
    AWAIT(_PID, assert(local_xReturn == false));
    for (ux: 0 .. (countMAX_COUNT_VALUE - 1)) {
        AWAIT(_PID, assert(uxSemaphoreGetCount(xP1_xSemaphore) == (countMAX_COUNT_VALUE - (ux))));
        xSemaphoreTake_NB(xP1_xSemaphore, countDONT_BLOCK, local_xReturn, local_bit, local_xIsTimeOut, local_var1, local_var2, _PID);
        AWAIT(_PID, assert(local_xReturn == true); local_xReturn = false);
    }
#if (configUSE_PREEMPTION == 0)
    taskYIELD(_PID, local_var1);
#endif
    AWAIT(_PID, ux = 0; assert(uxSemaphoreGetCount(xP1_xSemaphore) == 0));
    xSemaphoreTake_NB(xP1_xSemaphore, countDONT_BLOCK, local_xReturn, local_bit, local_xIsTimeOut, local_var1, local_var2, _PID);
    AWAIT(_PID, assert(local_xReturn == false))
    // end prvDecrementSemaphoreCount //////////////////////////////

    xSemaphoreTake_NB(xP1_xSemaphore, 0, local_xReturn, local_bit, local_xIsTimeOut, local_var1, local_var2, _PID);
    AWAIT(_PID, assert(local_xReturn == false));
do
::  prvIncrementSemaphoreCount(_PID, ux, xP1_xSemaphore, local_xReturn, local_bit, local_xIsTimeOut, local_var1, local_var2);
    prvDecrementSemaphoreCount(_PID, ux, xP1_xSemaphore, local_xReturn, local_bit, local_xIsTimeOut, local_var1, local_var2);

#ifdef CORRECTION
    #if (configUSE_PREEMPTION == 1) && (configUSE_TIME_SLICING == 0)
        taskYIELD(_PID, local_var1);
    #endif
#endif
od
}

proctype CNT2()
{
    byte local_var1 = NULL_byte, local_var2 = NULL_byte, ux = 0;
    bool local_xReturn = false, local_bit = false, local_xIsTimeOut = false;
    assert(_PID == (FIRST_TASK + 1));

    xSemaphoreTake_NB(xP2_xSemaphore, 0, local_xReturn, local_bit, local_xIsTimeOut, local_var1, local_var2, _PID);
    AWAIT(_PID, assert(local_xReturn == false));
do
::  prvIncrementSemaphoreCount(_PID, ux, xP2_xSemaphore, local_xReturn, local_bit, local_xIsTimeOut, local_var1, local_var2);
    prvDecrementSemaphoreCount(_PID, ux, xP2_xSemaphore, local_xReturn, local_bit, local_xIsTimeOut, local_var1, local_var2);

#ifdef CORRECTION
    #if (configUSE_PREEMPTION == 1) && (configUSE_TIME_SLICING == 0)
        taskYIELD(_PID, local_var1);
    #endif
#endif
od
}

init
{
    byte local_var1 = NULL_byte;

    d_step {
        xSemaphoreCreateCounting_fixed(xP1_xSemaphore, 0, countMAX_COUNT_VALUE, countMAX_COUNT_VALUE);
        xSemaphoreCreateCounting_fixed(xP2_xSemaphore, 1, countMAX_COUNT_VALUE, 0);

        prvInitialiseTaskLists(local_var1);

        xTaskCreate_fixed(FIRST_TASK + 0, tskIDLE_PRIORITY);
        xTaskCreate_fixed(FIRST_TASK + 1, tskIDLE_PRIORITY)
    };

    vTaskStartScheduler(EP, local_var1);

    /* Start the IDLE TASK */
    vTaskIDLE_TASK_BODY(IDLE_TASK_ID, local_var1)
}
