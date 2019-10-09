
#define promela_TASK_NUMBER     3
#define promela_QUEUE_NUMBER    0

#define FIRST_TASK              promela_EXP_NUMBER
#define IDLE_TASK_ID            (FIRST_TASK + promela_TASK_NUMBER)

#define RUN_ALL_TASKS()     \
    atomic {                \
        run MY_TASK();      \
        run SEC_TASK();     \
        run THIRD_TASK();   \
        run IDLE_TASK();    \
    }

#include "../FreeRTOS.pml"
#include "../FreeRTOS/tasks.pml"

/* Found a trace that the lowest priority task (THIRD_TASK) loops forever. */
ltl { <>[](_last != 5) }

// TODO: verify List, Queue
// TODO: vTaskDelay
// TODO: vPortSetInterruptHandler
// TODO: TODO: heap.c; embedded C code               
// TODO: change bit to byte

proctype MY_TASK()
{
    byte idx;
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bit local_bit = false, local_xIsNDTimeOut = false;
    assert(FIRST_TASK == _PID);
loop:
    AWAIT_A(_PID, assert(!HAS_PENDING_EXPS); printf("Task1 %d\n", _PID));
    vTaskDelay(_PID, 1, local_bit, local_var1, local_var2);
    AWAIT_A(_PID, goto loop)
}

proctype SEC_TASK()
{
    byte idx;
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bit local_bit = false, local_xIsNDTimeOut = false;
    assert(FIRST_TASK <= _PID && _PID < IDLE_TASK_ID);
loop:
    AWAIT_A(_PID, assert(!HAS_PENDING_EXPS); printf("Task2 %d\n", _PID));
    vTaskDelay(_PID, 1, local_bit, local_var1, local_var2);
    AWAIT_A(_PID, goto loop)
}

proctype THIRD_TASK()
{
    assert(FIRST_TASK <= _PID && _PID < IDLE_TASK_ID);
loop:
    AWAIT_A(_PID, assert(!HAS_PENDING_EXPS); printf("Task3 %d low priority\n", _PID));
    AWAIT_A(_PID, goto loop)
}

init {
    byte idx;
    byte local_var = NULL_byte;

    prvInitialiseTaskLists(local_var);
    xTaskCreate(EP, FIRST_TASK + 0, 1, local_var);
    xTaskCreate(EP, FIRST_TASK + 1, 1, local_var);
    xTaskCreate(EP, FIRST_TASK + 2, tskIDLE_PRIORITY, local_var);
    vTaskStartScheduler(EP, local_var)
}
