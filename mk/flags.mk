CFLAGS = -w -O2
SPINFLAGS = -a
COMPILETIME_FLAGS = -DXUSAFE -DCOLLAPSE -DNOFAIR
RUNTIME_FLAGS = -m$(MAX_DEPTH)
TRAIL_FLAGS = -p -v -k $(notdir $(TARGET)).trail

# minimized DFA encoding
ifdef MA
	COMPILETIME_FLAGS += -DMA=$(MA)
endif

# verify the selection property
ifdef LTL
	RUNTIME_FLAGS += -N $(LTL)
endif

# start printing trace after the Nth step
ifdef J
	TRAIL_FLAGS += -j$(J)
endif

# stop the simulation at the Nth step
ifdef U
	TRAIL_FLAGS += -u$(U)
endif

# weak fairness
ifdef WF
	COMPILETIME_FLAGS := $(filter-out -DNOFAIR, $(COMPILETIME_FLAGS))
	COMPILETIME_FLAGS += -DNFAIR=$(WF)
	RUNTIME_FLAGS += -f
endif

.PHONY: .safety .bfs .ltl .np
.safety:
	$(eval COMPILETIME_FLAGS += -DSAFETY -DNOCLAIM)

.bfs:
	$(eval COMPILETIME_FLAGS += -DBFS)

.ltl:
	$(eval SPINFLAGS += -DLTL)
	$(eval RUNTIME_FLAGS += -a)

.np:
	$(eval COMPILETIME_FLAGS += -DNP)
	$(eval RUNTIME_FLAGS += -l)
