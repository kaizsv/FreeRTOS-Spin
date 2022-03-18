#ifndef _PROMELA_
#define _PROMELA_

#define NULL_byte       255 /* 0xff */

/* for indexing in d_step command */
hidden byte hidden_idx = NULL_byte;
hidden byte hidden_idx2 = NULL_byte;

/** Executing process
*
*      init PendSV SysTick <<exp handlers>>  FIRST_TASK  SEC_TASK  <<user tasks>>
* _pid  0     1      2          ... (incremental numbers)
* _PID        0      1          ... (incremental numbers)
*
* _pid is a read-only variable assignend by Spin to identify the executing
* processes. However, the "init" process, only starting the other processes, is
* not an executing process in the model. We shift the value of _pid by 1 to skip
* the "init" process.
*/
#define _PID (_pid - 1)
byte EP = NULL_byte; /* Executing Process */

#define ND_TIMER_INT(_id) \
    if \
    :: FIRST_TASK <= _id && _id <= IDLE_TASK_ID -> TIMER_INT_IRQ; \
    :: true \
    fi

#define AWAIT_DS(id, stmnt) d_step { assert(id == EP && INT_SAFE); stmnt }
#define AWAIT_AS(id, stmnt) atomic { assert(id == EP && INT_SAFE); stmnt }
#define AWAIT(id, stmnt)    atomic { (id == EP) -> stmnt; ND_TIMER_INT(id); D_TAKEN_INT(id) }
#define SELE2(id, cond) atomic { ((id == EP) && (cond)) -> ND_TIMER_INT(id); D_TAKEN_INT(id) }
#define ELSE2(id, cond) atomic { ((id == EP) && !(cond)) -> ND_TIMER_INT(id); D_TAKEN_INT(id) }
#define SELE3(id, cond, stmnt)  \
    atomic { ((id == EP) && (cond)) -> stmnt; ND_TIMER_INT(id); D_TAKEN_INT(id) }
#define ELSE3(id, cond, stmnt)  \
    atomic { ((id == EP) && !(cond)) -> stmnt; ND_TIMER_INT(id); D_TAKEN_INT(id) }

#define SELE2_AS(id, cond) atomic { (cond) -> assert(id == EP && INT_SAFE) }
#define ELSE2_AS(id, cond) atomic { !(cond) -> assert(id == EP && INT_SAFE) }
#define SELE3_AS(id, cond, stmnt) atomic { (cond) -> assert(id == EP && INT_SAFE); stmnt }
#define ELSE3_AS(id, cond, stmnt) atomic { !(cond) -> assert(id == EP && INT_SAFE); stmnt }

#define __SELECT23__(_1, _2, _3, NAME, ...) NAME

#define SELE(...)       __SELECT23__(__VA_ARGS__, SELE3, SELE2)(__VA_ARGS__)
#define ELSE(...)       __SELECT23__(__VA_ARGS__, ELSE3, ELSE2)(__VA_ARGS__)
#define SELE_AS(...)    __SELECT23__(__VA_ARGS__, SELE3_AS, SELE2_AS)(__VA_ARGS__)
#define ELSE_AS(...)    __SELECT23__(__VA_ARGS__, ELSE3_AS, ELSE2_AS)(__VA_ARGS__)

#endif
