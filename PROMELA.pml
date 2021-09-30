#ifndef _PROMELA_
#define _PROMELA_

#define NULL_byte       255 /* 0xff */

/* for indexing in d_step command */
hidden byte hidden_idx = NULL_byte;

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
#define AWAIT_DS(id, stmnt) d_step { assert(id == EP); stmnt }
#define AWAIT_AS(id, stmnt) atomic { assert(id == EP); stmnt }
#define AWAIT(id, stmnt)    atomic { if :: (id == EP) && (FIRST_TASK <= id && id <= IDLE_TASK_ID) -> SET_SYST_FLAG() :: (id == EP) fi; stmnt }
#define SELE2(id, cond) atomic { ((id == EP) && (cond)) -> if :: FIRST_TASK <= id && id <= IDLE_TASK_ID -> SET_SYST_FLAG() :: true fi }
#define ELSE2(id, cond) atomic { ((id == EP) && !(cond)) -> if :: FIRST_TASK <= id && id <= IDLE_TASK_ID -> SET_SYST_FLAG() :: true fi }
#define SELE3(id, cond, stmnt)  \
    atomic { ((id == EP) && (cond)) -> if :: FIRST_TASK <= id && id <= IDLE_TASK_ID -> SET_SYST_FLAG() :: true fi; stmnt }
#define ELSE3(id, cond, stmnt)  \
    atomic { ((id == EP) && !(cond)) -> if :: FIRST_TASK <= id && id <= IDLE_TASK_ID -> SET_SYST_FLAG() :: true fi; stmnt }

#define SELE2_AS(id, cond) atomic { (cond) -> assert(id == EP) }
#define ELSE2_AS(id, cond) atomic { !(cond) -> assert(id == EP) }
#define SELE3_AS(id, cond, stmnt) atomic { (cond) -> assert(id == EP); stmnt }
#define ELSE3_AS(id, cond, stmnt) atomic { !(cond) -> assert(id == EP); stmnt }

#define __SELECT23__(_1, _2, _3, NAME, ...) NAME

#define SELE(...)       __SELECT23__(__VA_ARGS__, SELE3, SELE2)(__VA_ARGS__)
#define ELSE(...)       __SELECT23__(__VA_ARGS__, ELSE3, ELSE2)(__VA_ARGS__)
#define SELE_AS(...)    __SELECT23__(__VA_ARGS__, SELE3_AS, SELE2_AS)(__VA_ARGS__)
#define ELSE_AS(...)    __SELECT23__(__VA_ARGS__, ELSE3_AS, ELSE2_AS)(__VA_ARGS__)

#endif
