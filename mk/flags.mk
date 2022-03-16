CFLAGS = -w -O2
SPINFLAGS = -a -D$(ARCH) $(PLAN)
COMPILETIME_FLAGS = -DXUSAFE -DCOLLAPSE -DNOFAIR
RUNTIME_FLAGS = -m$(MAX_DEPTH)
TRAIL_FLAGS = -p -v -k $(notdir $(TARGET)).trail -D$(ARCH)

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

# hash-compact
ifdef HC
	COMPILETIME_FLAGS := $(filter-out -DCOLLAPSE, $(COMPILETIME_FLAGS))
	COMPILETIME_FLAGS += -DHC$(HC)
endif

ifdef BITSTATE
	COMPILETIME_FLAGS := $(filter-out -DCOLLAPSE, $(COMPILETIME_FLAGS))
	COMPILETIME_FLAGS += -DBITSTATE
	RUNTIME_FLAGS := -V \# Usage: ./pan $(MAX_DEPTH) -k -w
endif

ifdef CORRECTION
	SPINFLAGS += -DCORRECTION
	TRAIL_FLAGS += -DCORRECTION
endif

.PHONY: .safety .bfs .ltl .np .trail.full .trail.ltl
.safety:
	$(eval COMPILETIME_FLAGS += -DSAFETY -DNOCLAIM)

.bfs:
	$(eval COMPILETIME_FLAGS += -DBFS)
	$(eval undefine RUNTIME_FLAGS)

.ltl:
	$(eval SPINFLAGS += -DLTL)
	$(eval RUNTIME_FLAGS += -a)

.np:
	$(eval COMPILETIME_FLAGS += -DNP)
	$(eval RUNTIME_FLAGS += -l)

.trail.full:
	$(eval TRAIL_FLAGS := -l -g $(TRAIL_FLAGS))

.trail.ltl:
	$(eval TRAIL_FLAGS := -DLTL $(TRAIL_FLAGS))
