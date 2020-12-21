
#define promela_TASK_NUMBER     3
#define promela_QUEUE_NUMBER    0

#define FIRST_TASK              promela_EXP_NUMBER
#define IDLE_TASK_ID            (FIRST_TASK + promela_TASK_NUMBER)

#define RUN_ALL_TASKS(stmts) \
    atomic {                \
        stmts;              \
        run MY_TASK();      \
        run SEC_TASK();     \
        run THIRD_TASK();   \
    }

#include "../FreeRTOS.pml"
#include "../FreeRTOS/tasks.pml"

#ifdef LTL
    #include "../property/Demo.ltl"
#endif

// TODO: verify List, Queue; using embedded C code
// TODO: vPortSetInterruptHandler
// TODO: TODO: heap.c; embedded C code               
// TODO: change bit to byte
// TODO: check if the waiting statement is blocked in v7m.pml by using ltl

proctype MY_TASK()
{
    byte idx;
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bit local_bit = false, local_xIsNDTimeOut = false;
    assert(FIRST_TASK == _PID);
do
::  AWAIT(_PID, printf("Task1 %d\n", _PID));
    vTaskDelay(_PID, 50, local_bit, local_var1, local_var2);
od
}

proctype SEC_TASK()
{
    byte idx;
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bit local_bit = false, local_xIsNDTimeOut = false;
    assert(FIRST_TASK <= _PID && _PID < IDLE_TASK_ID);
do
::  AWAIT(_PID, printf("Task2 %d\n", _PID));
    vTaskDelay(_PID, 50, local_bit, local_var1, local_var2);
od
}

proctype THIRD_TASK()
{
    assert(FIRST_TASK <= _PID && _PID < IDLE_TASK_ID);
do
::  AWAIT(_PID, printf("Task3 %d low priority\n", _PID));
od
}

init {
    byte idx;
    byte local_var = NULL_byte;

    d_step {
        prvInitialiseTaskLists(local_var);
        xTaskCreate_fixed(FIRST_TASK + 0, 1);
        xTaskCreate_fixed(FIRST_TASK + 1, 1);
        xTaskCreate_fixed(FIRST_TASK + 2, tskIDLE_PRIORITY)
    };
    vTaskStartScheduler(EP, local_var);

    /* Start the IDLE TASK */
    vTaskIDLE_TASK_BODY(IDLE_TASK_ID, local_var)
}
