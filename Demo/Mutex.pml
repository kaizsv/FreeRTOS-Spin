
#define promela_TASK_NUMBER     2
#define promela_QUEUE_NUMBER    1

#define FIRST_TASK              promela_EXP_NUMBER
#define IDLE_TASK_ID            (FIRST_TASK + promela_TASK_NUMBER)

#define RUN_ALL_TASKS(stmts) \
    atomic {                \
        stmts;              \
        run MY_TASK();      \
        run SEC_TASK();     \
    }

#define QUEUE_TAKE_EXIT_CRITICAL

#include "../FreeRTOS.pml"
#include "../FreeRTOS/tasks.pml"
#include "../FreeRTOS/semphr.h.pml"

QueueDeclarator(1, byte);
SemaphoreHandle_t(mysemaphore, 1, byte);

byte mutex = 0;

proctype MY_TASK()
{
    byte idx;
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bit local_xReturn = false, local_bit = false;
    bit local_xIsTimeOut = false;
    assert(FIRST_TASK == _PID);
do
::  xSemaphoreTake(mysemaphore, portMAX_DELAY, local_xReturn, local_bit, local_xIsTimeOut, local_var1, local_var2, _PID);
    AWAIT_D(_PID, assert(local_xReturn == true); assert(mutex == 0); mutex = mutex + 1);
    AWAIT_D(_PID, assert(mutex == 1); mutex = mutex - 1);
    xSemaphoreGive(mysemaphore, local_xReturn, local_bit, local_xIsTimeOut, local_var1, local_var2, _PID);
od
}

proctype SEC_TASK()
{
    byte idx;
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bit local_xReturn = false, local_bit = false;
    bit local_xIsTimeOut = false;
    assert(FIRST_TASK <= _PID && _PID < IDLE_TASK_ID);
do
::  xSemaphoreTake(mysemaphore, portMAX_DELAY, local_xReturn, local_bit, local_xIsTimeOut, local_var1, local_var2, _PID);
    AWAIT_D(_PID, assert(local_xReturn == true); assert(mutex == 0); mutex = mutex + 1);
    AWAIT_D(_PID, assert(mutex == 1); mutex = mutex - 1);
    xSemaphoreGive(mysemaphore, local_xReturn, local_bit, local_xIsTimeOut, local_var1, local_var2, _PID);
od
}

init {
    byte idx;
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bit local_xReturn = false, local_bit = false;
    bit local_xIsTimeOut = false;

    xSemaphoreCreateMutex(mysemaphore, 0, local_xReturn, local_bit, local_xIsTimeOut, local_var1, local_var2, EP);

    d_step {
        prvInitialiseTaskLists(local_var1);
        xTaskCreate_fixed(FIRST_TASK, 1);
        xTaskCreate_fixed(FIRST_TASK + 1, 1)
    };
    vTaskStartScheduler(EP, local_var1);

    /* Start the IDLE TASK */
    vTaskIDLE_TASK_BODY(IDLE_TASK_ID, local_var1)
}
