/* FreeRTOS/Demo/Common/Full/dynamic.c */

#define promela_TASK_NUMBER     3
#define promela_QUEUE_NUMBER    1

#define FIRST_TASK              promela_EXP_NUMBER
#define IDLE_TASK_ID            (FIRST_TASK + promela_TASK_NUMBER)

#define RUN_ALL_TASKS(stmts) \
    atomic {                \
        stmts;              \
        run CONT_INC();     \
        run LIM_INC();      \
        run C_CTRL();       \
    }

#define QUEUE_SEND_EXIT_CRITICAL
#define QUEUE_RECEIVE_EXIT_CRITICAL

#include "../FreeRTOS.pml"
#include "../FreeRTOS/tasks.pml"
#include "../FreeRTOS/queue.h.pml"

#define xContinousIncrementHandle   FIRST_TASK + 0
#define xLimitedIncrementHandle     FIRST_TASK + 1

QueueDeclarator(1, byte);
QueueHandle_t(xSuspendedTestQueue, 1, byte);

#define ULCOUNTER_IS_ACCESSED_BY(id, var)   \
    AWAIT_A(_PID, var = id)

#define priSLEEP_TIME   50
#define priLOOPS        5
#define priMAX_COUNT    3
#define priNO_BLOCK     0
#define priSUSPENDED_QUEUE_LENGTH 1
byte ulCounter;

proctype CONT_INC()
{
    byte idx;
    byte local_var1 = NULL_byte, local_var2 = NULL_byte, local_var3 = NULL_byte;
    bit local_bit = false;

    byte uxOurPriority;
    assert(_PID == xContinousIncrementHandle);
    AWAIT_D(_PID, uxOurPriority = uxTaskPriorityGet(NULL_byte));
loop:
    vTaskPrioritySet(_PID, NULL_byte, uxOurPriority + 1, local_var1, local_bit, local_var2, local_var3);
    ULCOUNTER_IS_ACCESSED_BY(xContinousIncrementHandle, ulCounter);
    vTaskPrioritySet(_PID, NULL_byte, uxOurPriority, local_var1, local_bit, local_var2, local_var3);
    AWAIT_A(_PID, goto loop)
}

proctype LIM_INC()
{
    byte idx;
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;

    assert(_PID == xLimitedIncrementHandle);
    vTaskSuspend(_PID, NULL_byte, local_var1, local_var2);
loop:
    AWAIT_A(_PID, assert(ulCounter == 0));
    ULCOUNTER_IS_ACCESSED_BY(xLimitedIncrementHandle, ulCounter);
        vTaskSuspend(_PID, NULL_byte, local_var1, local_var2);
    AWAIT_A(_PID, goto loop)
}

proctype C_CTRL()
{
    byte idx;
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bit local_bit = false;

    byte sLoops;
    assert(_PID == FIRST_TASK + 2);
loop:
    AWAIT_A(_PID, ulCounter = 0);

    for (sLoops: 0 .. (priLOOPS - 1)) {
        vTaskSuspend(_PID, xContinousIncrementHandle, local_var1, local_var2);
        ULCOUNTER_IS_ACCESSED_BY(_PID, ulCounter);
        vTaskResume(_PID, xContinousIncrementHandle, local_bit, local_var1);

        vTaskDelay(_PID, priSLEEP_TIME, local_bit, local_var1, local_var2);

        vTaskSuspendAll(_PID);
        AWAIT_D(_PID, assert(ulCounter == xContinousIncrementHandle));
        xTaskResumeAll(_PID, local_var1, _, local_var2);
    }

    vTaskSuspend(_PID, xContinousIncrementHandle, local_var1, local_var2);

    AWAIT_D(_PID, ulCounter = 0);

    vTaskSuspendAll(_PID);
        vTaskResume(_PID, xLimitedIncrementHandle, local_bit, local_var1);
    xTaskResumeAll(_PID, local_var1, _, local_var2);

    AWAIT_D(_PID, assert(ulCounter == xLimitedIncrementHandle));

#if (configUSE_PREEMPTION == 0)
    taskYIELD(_PID, local_var1);
#endif

    vTaskResume(_PID, xContinousIncrementHandle, local_bit, local_var1);
    AWAIT_A(_PID, goto loop)
}

init {
    byte idx;
    byte local_var = NULL_byte;

    d_step {
        xQueueCreate(xSuspendedTestQueue, 0, priSUSPENDED_QUEUE_LENGTH);

        prvInitialiseTaskLists(local_var);

        xTaskCreate_fixed(xContinousIncrementHandle, tskIDLE_PRIORITY);
        xTaskCreate_fixed(xLimitedIncrementHandle, tskIDLE_PRIORITY + 1);
        xTaskCreate_fixed(FIRST_TASK + 2, tskIDLE_PRIORITY)
    };

    vTaskStartScheduler(EP, local_var);

    /* Start the IDLE TASK */
    vTaskIDLE_TASK_BODY(IDLE_TASK_ID, local_var)
}
