#define LIVENESS(a, b)  ([]((a) -> <>(b)))

ltl { []<>(_last != 1 && _last != 2) -> (LIVENESS(prvSemaphoreTest1@loop, prvSemaphoreTest1@liveness) && LIVENESS(prvSemaphoreTest2@loop, prvSemaphoreTest2@liveness) && LIVENESS(prvSemaphoreTest3@loop, prvSemaphoreTest3@liveness) && LIVENESS(prvSemaphoreTest4@loop, prvSemaphoreTest4@liveness)) }
