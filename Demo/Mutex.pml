
#define promela_TASK_NUMBER     2
#define promela_QUEUE_NUMBER    1

#define FIRST_TASK              promela_EXP_NUMBER
#define IDLE_TASK_ID            (FIRST_TASK + promela_TASK_NUMBER)

#define RUN_ALL_TASKS()     \
    atomic {                \
        run MY_TASK();      \
        run SEC_TASK();     \
        run IDLE_TASK();    \
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
    bit local_xIsNDTimeOut = false;
    assert(FIRST_TASK == _PID);
loop:
    xSemaphoreTake(mysemaphore, portMAX_DELAY, local_xReturn, local_bit, local_xIsNDTimeOut, local_var1, local_var2, _PID);
    AWAIT_D(_PID, assert(local_xReturn == true); assert(mutex == 0); mutex = mutex + 1);
    AWAIT_D(_PID, assert(mutex == 1); mutex = mutex - 1);
    xSemaphoreGive(mysemaphore, local_xReturn, local_bit, local_xIsNDTimeOut, local_var1, local_var2, _PID);
    AWAIT_A(_PID, goto loop)
}

proctype SEC_TASK()
{
    byte idx;
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bit local_xReturn = false, local_bit = false;
    bit local_xIsNDTimeOut = false;
    assert(FIRST_TASK <= _PID && _PID < IDLE_TASK_ID);
loop:
    xSemaphoreTake(mysemaphore, portMAX_DELAY, local_xReturn, local_bit, local_xIsNDTimeOut, local_var1, local_var2, _PID);
    AWAIT_D(_PID, assert(local_xReturn == true); assert(mutex == 0); mutex = mutex + 1);
    AWAIT_D(_PID, assert(mutex == 1); mutex = mutex - 1);
    xSemaphoreGive(mysemaphore, local_xReturn, local_bit, local_xIsNDTimeOut, local_var1, local_var2, _PID);
    AWAIT_A(_PID, goto loop)
}

init {
    byte idx;
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bit local_xReturn = false, local_bit = false;
    bit local_xIsNDTimeOut = false;

    xSemaphoreCreateMutex(mysemaphore, 0, local_xReturn, local_bit, local_xIsNDTimeOut, local_var1, local_var2, EP);

    prvInitialiseTaskLists(local_var1);
    xTaskCreate(EP, FIRST_TASK, 1, local_var1);
    xTaskCreate(EP, FIRST_TASK + 1, 1, local_var1);
    vTaskStartScheduler(EP, local_var1)
}
