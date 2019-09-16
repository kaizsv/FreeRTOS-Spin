
#define promela_TASK_NUMBER     2
#define promela_QUEUE_NUMBER    0

#define FIRST_TASK              promela_EXP_NUMBER
#define IDLE_TASK_ID            (FIRST_TASK + promela_TASK_NUMBER)

#define RUN_ALL_TASKS()     \
    atomic {                \
        run MY_TASK();      \
        run SEC_TASK();     \
        run IDLE_TASK();    \
    }

#include "../FreeRTOS.pml"
#include "../FreeRTOS/tasks.pml"

// TODO: verify List, Queue
// TODO: vTaskDelay
// TODO: vPortSetInterruptHandler
// TODO: TODO: heap.c; embedded C code               
// TODO: change bit to byte

proctype MY_TASK()
{
    assert(FIRST_TASK == _PID);
loop:
    AWAIT_A(_PID, assert(!HAS_PENDING_EXPS); printf("Task1 %d\n", _PID));
    AWAIT_A(_PID, goto loop)
}

proctype SEC_TASK()
{
    assert(FIRST_TASK <= _PID && _PID < IDLE_TASK_ID);
loop:
    AWAIT_A(_PID, assert(!HAS_PENDING_EXPS); printf("Task2 %d\n", _PID));
    AWAIT_A(_PID, goto loop)
}

init {
    byte idx;
    byte local_var = NULL_byte;

    prvInitialiseTaskLists(local_var);
    xTaskCreate(EP, FIRST_TASK, 1, local_var);
    xTaskCreate(EP, FIRST_TASK + 1, 1, local_var);
    vTaskStartScheduler(EP, local_var)
}
