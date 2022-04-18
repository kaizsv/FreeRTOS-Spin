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

#define AWAIT(id, stmt) atomic { (id == EP) -> stmt; ND_TIMER_INT(id); D_TAKEN_INT() }
#define SELE2(id, cond) atomic { ((id == EP) && (cond)) -> ND_TIMER_INT(id); D_TAKEN_INT() }
#define ELSE2(id, cond) atomic { ((id == EP) && !(cond)) -> ND_TIMER_INT(id); D_TAKEN_INT() }
#define SELE3(id, cond, stmt)  \
    atomic { ((id == EP) && (cond)) -> stmt; ND_TIMER_INT(id); D_TAKEN_INT() }
#define ELSE3(id, cond, stmt)  \
    atomic { ((id == EP) && !(cond)) -> stmt; ND_TIMER_INT(id); D_TAKEN_INT() }

#define AWAIT_SAFE(id, stmt) atomic { (id == EP) -> stmt; assert(INT_SAFE); }
#define SELE2_SAFE(id, cond) atomic { ((id == EP) && (cond)) -> assert(INT_SAFE) }
#define ELSE2_SAFE(id, cond) atomic { ((id == EP) && !(cond)) -> assert(INT_SAFE) }
#define SELE3_SAFE(id, cond, stmt) atomic { ((id == EP) && (cond)) -> stmt; assert(INT_SAFE) }
#define ELSE3_SAFE(id, cond, stmt) atomic { ((id == EP) && !(cond)) -> stmt; assert(INT_SAFE) }

#define __SELECT23__(_1, _2, _3, NAME, ...) NAME

#define SELE(...)       __SELECT23__(__VA_ARGS__, SELE3, SELE2)(__VA_ARGS__)
#define ELSE(...)       __SELECT23__(__VA_ARGS__, ELSE3, ELSE2)(__VA_ARGS__)
#define SELE_SAFE(...)  __SELECT23__(__VA_ARGS__, SELE3_SAFE, SELE2_SAFE)(__VA_ARGS__)
#define ELSE_SAFE(...)  __SELECT23__(__VA_ARGS__, ELSE3_SAFE, ELSE2_SAFE)(__VA_ARGS__)

#define AWAIT_SAFE_D(id, stmt) d_step { assert(id == EP); stmt; assert(INT_SAFE) }

#endif
