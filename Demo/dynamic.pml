/* FreeRTOS/Demo/Common/Full/dynamic.c */

#define promela_TASK_NUMBER     3
#define promela_QUEUE_NUMBER    1

#define FIRST_TASK              promela_EXP_NUMBER
#define IDLE_TASK_ID            (FIRST_TASK + promela_TASK_NUMBER)

#define RUN_ALL_TASKS()     \
    atomic {                \
        run CONT_INC();     \
        run LIM_INC();      \
        run C_CTRL();       \
                            \
        run IDLE_TASK();    \
    }

#define QUEUE_SEND_EXIT_CRITICAL
#define QUEUE_RECEIVE_EXIT_CRITICAL

#include "../FreeRTOS.pml"
#include "../FreeRTOS/tasks.pml"
#include "../FreeRTOS/queue.h.pml"

#define xContinousIncrementHandle   FIRST_TASK + 0
#define xLimitedIncrementHandle     FIRST_TASK + 1

#define usNumToProduce 1

QueueDeclarator(1, byte);
QueueHandle_t(xSuspendedTestQueue, 1, byte);

#define INCREASE_VAR_AND_INT_OVERFLOW(var)  \
    AWAIT_A(_PID,                           \
        if                                  \
        :: var < 8 -> var = var + 1         \
        :: else                             \
        fi                                  \
    )

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
    vTaskPrioritySet(_PID, NULL_byte, uxOurPriority + 1, local_var1, local_bit, local_var2, local_var3)
    INCREASE_VAR_AND_INT_OVERFLOW(ulCounter);
    vTaskPrioritySet(_PID, NULL_byte, uxOurPriority, local_var1, local_bit, local_var2, local_var3)
    AWAIT_A(_PID, goto loop)
}

proctype LIM_INC()
{
    byte idx;
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;

    assert(_PID == xLimitedIncrementHandle);
    vTaskSuspend(_PID, NULL_byte, local_var1, local_var2);
loop:
    INCREASE_VAR_AND_INT_OVERFLOW(ulCounter);
    if
    :: SELE(_PID, ulCounter >= priMAX_COUNT) ->
        vTaskSuspend(_PID, NULL_byte, local_var1, local_var2)
    :: ELSE(_PID, ulCounter >= priMAX_COUNT)
    fi;
    AWAIT_A(_PID, goto loop)
}

proctype C_CTRL()
{
    byte idx;
    byte local_var1 = NULL_byte, local_var2 = NULL_byte;
    bit local_bit = false;

    byte sLoops, ulLastCounter = NULL_byte;
    assert(_PID == FIRST_TASK + 2)
loop:
    AWAIT_A(_PID, ulCounter = 0);

    for (sLoops: 0 .. (priLOOPS - 1)) {
        vTaskSuspend(_PID, xContinousIncrementHandle, local_var1, local_var2);
        AWAIT_D(_PID, ulLastCounter = ulCounter);
        vTaskResume(_PID, xContinousIncrementHandle, local_bit, local_var1);

        vTaskDelay(_PID, priSLEEP_TIME, local_bit, local_var1, local_var2);

        vTaskSuspendAll(_PID);
        AWAIT_D(_PID, assert(ulLastCounter != ulCounter); ulLastCounter = 0);
        xTaskResumeAll(_PID, local_var1, _, local_var2);
    }

    vTaskSuspend(_PID, xContinousIncrementHandle, local_var1, local_var2);

    AWAIT_D(_PID, ulCounter = 0);

    vTaskSuspendAll(_PID);
        vTaskResume(_PID, xLimitedIncrementHandle, local_bit, local_var1);
    xTaskResumeAll(_PID, local_var1, _, local_var2);

    AWAIT_D(_PID, assert(ulCounter == priMAX_COUNT));

#if (configUSE_PREEMPTION == 0)
    taskYIELD(_PID, local_var1);
#endif

    vTaskResume(_PID, xContinousIncrementHandle, local_bit, local_var1);
    AWAIT_A(_PID, goto loop)
}

init {
    byte idx;
    byte local_var1 = NULL_byte;

    xQueueCreate(xSuspendedTestQueue, 0, priSUSPENDED_QUEUE_LENGTH);

    prvInitialiseTaskLists(local_var1);

    xTaskCreate(EP, xContinousIncrementHandle, tskIDLE_PRIORITY, local_var1);
    xTaskCreate(EP, xLimitedIncrementHandle, tskIDLE_PRIORITY + 1, local_var1);
    xTaskCreate(EP, FIRST_TASK + 2, tskIDLE_PRIORITY, local_var1);

    vTaskStartScheduler(EP, local_var1)
}
