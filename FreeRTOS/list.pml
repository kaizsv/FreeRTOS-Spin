#ifndef _LIST_
#define _LIST_

#include "../FreeRTOS.pml"

typedef ListItem_t {
    byte xItemValue;
    byte Container;
};

#define listGET_LIST_ITEM_VALUE(pxListItem) pxListItem.xItemValue
inline listSET_LIST_ITEM_VALUE(pxListItem, uxValue)
{
    assert(0 <= (uxValue) && (uxValue) < 256);
    pxListItem.xItemValue = uxValue
}

#define listLIST_ITEM_CONTAINER(pxListItem) pxListItem.Container
inline listSET_LIST_ITEM_CONTAINER(pxListItem, uxContainer)
{
    assert(0 <= (uxContainer) && (uxContainer) < 256);
    pxListItem.Container = uxContainer
}

typedef List_t {
    byte p_tcb;
};

#define listPOINTER_IS_NULL(pxListPointer) (pxListPointer.p_tcb == NULL_byte)

inline listPOINTER_RESET(pxListPointer)
{
    pxListPointer.p_tcb = NULL_byte
}

inline listPOINTER_SET(pxListPointer, tcb)
{
    assert(tcb < 254); // prevent p_tcb becoming NULL_byte or xListEnd
    pxListPointer.p_tcb = tcb
}

#define LIST_SIZE1  1
#define LIST_SIZE2  2
#define LIST_SIZE3  3
#define LIST_SIZE4  4
#define LIST_SIZE5  5

#if 0
    In the model, only pxReadyTasksLists may have a changed pxIndex
    because co-routine is not established and
    configUSE_TRACE_FACILITY and INCLUDE_xTaskGetHandle are undefined.

    |-- LIST_SIZE --|
    0 -> 1 -> 2 -> ... -> xListEnd
                             /\
                             ||
                           pxIndex
#endif

#if defined(configUSE_CO_ROUTINES) && defined(configUSE_TRACE_FACILITY)
    #error Redesign pxIndex, vListInsert, and the macros for referencing HEAD_ENTRY
#endif

#if defined(INCLUDE_xTaskGetHandle)
    #error Redesign pxIndex, vListInsert, and the macros for referencing HEAD_ENTRY
#endif

#define xListEnd    254

#define __TYPEDEF_List_t(__SIZE, WITH_PXINDEX) \
    typedef List ## __SIZE ## WITH_PXINDEX ## t { \
        List_t ps[LIST_SIZE ## __SIZE];

#define __ENDEF }

#define TYPEDEF_List_t(__SIZE) \
    __TYPEDEF_List_t(__SIZE, _) \
    __ENDEF

#define TYPEDEF_List_t_WITH_PXINDEX(__SIZE) \
    __TYPEDEF_List_t(__SIZE, _pxIndex_) \
        byte pxIndex; \
    __ENDEF

#define __OWNER_OF(tcb)                 (tcb) - FIRST_TASK
#define __GET_LIST_ITEM(tcb, xListItem) TCBs[__OWNER_OF(tcb)].xListItem
#define _GET_LIST_ITEM(tcb, xListItem)  TCBs_others[__OWNER_OF(tcb)].xListItem

#define pxOrdinalStateListItem(pxList, ord) __GET_LIST_ITEM(pxList.ps[ord].p_tcb, xStateListItem)
#define pxOrdinalEventListItem(pxList, ord) _GET_LIST_ITEM(pxList.ps[ord].p_tcb, xEventListItem)

#define listGET_STATE_ITEM_VALUE_OF_HEAD_ENTRY(pxList) \
    listGET_LIST_ITEM_VALUE(pxOrdinalStateListItem(pxList, 0))
#define listGET_EVENT_ITEM_VALUE_OF_HEAD_ENTRY(pxList) \
    listGET_LIST_ITEM_VALUE(pxOrdinalEventListItem(pxList, 0))

#define listLIST_IS_EMPTY(pxList)           listPOINTER_IS_NULL(pxList.ps[0])
#define listLIST_IS_NOT_FULL(pxList, SIZE)  listPOINTER_IS_NULL(pxList.ps[SIZE - 1])
#define listLENGTH_IS_EXCEEDING_0(pxList)   (!listPOINTER_IS_NULL(pxList.ps[0]))
#define listLENGTH_IS_EXCEEDING_1(pxList)   (!listPOINTER_IS_NULL(pxList.ps[1]))

inline listGET_OWNER_OF_NEXT_ENTRY(_id, pxTCB, pxList, SIZE)
{
    /* Increment the index to the next item and return the item, ensuring */
    /* we don't return the marker used at the end of the list */
    AWAIT_DS(_id,
        pxList.pxIndex = (
            (pxList.pxIndex < (SIZE - 1) && !listPOINTER_IS_NULL(pxList.ps[pxList.pxIndex + 1])) ->
                pxList.pxIndex + 1 : xListEnd
    )   );
    AWAIT_DS(_id, pxList.pxIndex = (pxList.pxIndex == xListEnd -> 0 : pxList.pxIndex));
    AWAIT_DS(_id,
        assert(pxTCB == NULL_byte || pxTCB == pxCurrentTCB);
        pxTCB = pxList.ps[pxList.pxIndex].p_tcb
    )
}

#define listGET_OWNER_OF_HEAD_ENTRY(pxList) pxList.ps[0].p_tcb

#define listIS_CONTAINED_WITHIN(xCID, pxListItem) (listLIST_ITEM_CONTAINER(pxListItem) == (xCID))

inline vListInitialiseItem(pxItem)
{
    listSET_LIST_ITEM_CONTAINER(pxItem, NULL_byte)
}

#define vListInitialisePointer listPOINTER_RESET

inline vListInitialise(pxList, SIZE)
{
    for (hidden_idx: 0 .. (SIZE - 1)) {
        vListInitialisePointer(pxList.ps[hidden_idx])
    }
    hidden_idx = NULL_byte
}

inline vListInitialise_pxIndex(pxList, SIZE)
{
    pxList.pxIndex = xListEnd;
    for (hidden_idx: 0 .. (SIZE - 1)) {
        vListInitialisePointer(pxList.ps[hidden_idx])
    }
    hidden_idx = NULL_byte
}

inline swapListPointers(aListPointer, bListPointer)
{
    aListPointer.p_tcb = aListPointer.p_tcb ^ bListPointer.p_tcb;
    bListPointer.p_tcb = bListPointer.p_tcb ^ aListPointer.p_tcb;
    aListPointer.p_tcb = aListPointer.p_tcb ^ bListPointer.p_tcb;
}

inline vListInsertEnd(pxList, SIZE, xCID, pxNewListItemTCB, pxNewListItem)
{
    assert(listLIST_IS_NOT_FULL(pxList, SIZE));

    for (hidden_idx: 0 .. (SIZE - 1)) {
        if
        :: listPOINTER_IS_NULL(pxList.ps[hidden_idx]) ->
            listSET_LIST_ITEM_CONTAINER(pxNewListItem, xCID);
            listPOINTER_SET(pxList.ps[hidden_idx], pxNewListItemTCB);
            break
        :: else
        fi
    }
    hidden_idx = NULL_byte
}

inline vListInsertEnd_pxIndex(pxList, SIZE, xCID, pxNewListItemTCB, pxNewListItem)
{
    assert(listLIST_IS_NOT_FULL(pxList, SIZE));

    /* Find the next null item */
    for (hidden_idx: 0 .. (SIZE - 1)) {
        if
        :: listPOINTER_IS_NULL(pxList.ps[hidden_idx]) -> break
        :: else
        fi
    }

    if
    :: pxList.pxIndex ^ xListEnd ->
        assert(pxList.pxIndex < hidden_idx);
        do
        :: pxList.pxIndex < hidden_idx ->
            swapListPointers(pxList.ps[hidden_idx - 1], pxList.ps[hidden_idx]);
            hidden_idx = hidden_idx - 1
        :: else ->
            assert(pxList.pxIndex == hidden_idx);
            pxList.pxIndex = pxList.pxIndex + 1;
            break
        od
    :: else
    fi;

    assert(listPOINTER_IS_NULL(pxList.ps[hidden_idx]));
    listSET_LIST_ITEM_CONTAINER(pxNewListItem, xCID);
    listPOINTER_SET(pxList.ps[hidden_idx], pxNewListItemTCB);
    hidden_idx = NULL_byte
}

inline vListInsert_sortStateListItem(pxList, SIZE, xCID, pxNewListItemTCB, pxNewListItem)
{
    assert(listLIST_IS_NOT_FULL(pxList, SIZE) && hidden_idx == NULL_byte && hidden_var == NULL_byte);
    for (hidden_idx: 0 .. (SIZE - 1)) {
        /* Find the next null item */
        if
        :: listPOINTER_IS_NULL(pxList.ps[hidden_idx]) -> break;
        :: else
        fi;
        /* Find the first place to insert the new item */
        if
        :: (hidden_var == NULL_byte) &&
           (listGET_LIST_ITEM_VALUE(pxOrdinalStateListItem(pxList, hidden_idx)) > listGET_LIST_ITEM_VALUE(pxNewListItem)) ->
            hidden_var = hidden_idx
        :: else
        fi
    }
    if
    :: hidden_var ^ NULL_byte ->
        /* replace the item at the hidden_var by the last null item */
        assert(hidden_var < hidden_idx);
        do
        :: hidden_var < hidden_idx ->
            swapListPointers(pxList.ps[hidden_idx - 1], pxList.ps[hidden_idx]);
            hidden_idx = hidden_idx - 1
        :: else ->
            assert(hidden_var == hidden_idx);
            hidden_var = NULL_byte;
            break
        od
    :: else
    fi;
    /* place pxNewListItem at the index position of pxList */
    assert(listPOINTER_IS_NULL(pxList.ps[hidden_idx]));
    listSET_LIST_ITEM_CONTAINER(pxNewListItem, xCID);
    listPOINTER_SET(pxList.ps[hidden_idx], pxNewListItemTCB);
    hidden_idx = NULL_byte
}

inline vListInsert_sortEventListItem(pxList, SIZE, xCID, pxNewListItemTCB, pxNewListItem)
{
    assert(listLIST_IS_NOT_FULL(pxList, SIZE) && hidden_idx == NULL_byte && hidden_var == NULL_byte);
    for (hidden_idx: 0 .. (SIZE - 1)) {
        /* Find the next null item */
        if
        :: listPOINTER_IS_NULL(pxList.ps[hidden_idx]) -> break;
        :: else
        fi;
        /* Find the first place to insert the new item */
        if
        :: (hidden_var == NULL_byte) &&
           (listGET_LIST_ITEM_VALUE(pxOrdinalEventListItem(pxList, hidden_idx)) > listGET_LIST_ITEM_VALUE(pxNewListItem)) ->
            hidden_var = hidden_idx
        :: else
        fi
    }
    if
    :: hidden_var ^ NULL_byte ->
        /* replace the item at the hidden_var by the last null item */
        assert(hidden_var < hidden_idx);
        do
        :: hidden_var < hidden_idx ->
            swapListPointers(pxList.ps[hidden_idx - 1], pxList.ps[hidden_idx]);
            hidden_idx = hidden_idx - 1
        :: else ->
            assert(hidden_var == hidden_idx);
            hidden_var = NULL_byte;
            break
        od
    :: else
    fi;
    /* place pxNewListItem at the index position of pxList */
    assert(listPOINTER_IS_NULL(pxList.ps[hidden_idx]));
    listSET_LIST_ITEM_CONTAINER(pxNewListItem, xCID);
    listPOINTER_SET(pxList.ps[hidden_idx], pxNewListItemTCB);
    hidden_idx = NULL_byte
}

#if 0
    In FreeRTOS, the return value of uxListRemove only compares with zero.
    In the model, the comparison can be establishtd by listLIST_IS_EMPTY
    macro since pxList is known.
#endif

inline uxListRemove(pxList, SIZE, pxItemToRemoveTCB, pxItemToRemove)
{
    /* find the index of pxItemToRemove in pxList */
    for (hidden_idx: 0 .. (SIZE - 1)) {
        if
        :: pxList.ps[hidden_idx].p_tcb == pxItemToRemoveTCB ->
            vListInitialisePointer(pxList.ps[hidden_idx]);
            break
        :: else -> assert(hidden_idx < (SIZE - 1)) /* check reliability */
        fi
    }

    if
    :: hidden_idx < (SIZE - 1) ->
        /* move items behind the index position of pxList forward */
        for (hidden_idx: (hidden_idx + 1) .. (SIZE - 1)) {
            if
            :: !listPOINTER_IS_NULL(pxList.ps[hidden_idx]) ->
                assert(pxList.ps[hidden_idx].p_tcb != pxItemToRemoveTCB);
                swapListPointers(pxList.ps[hidden_idx - 1], pxList.ps[hidden_idx])
            :: else -> break
            fi
        }
    :: else
    fi;
    hidden_idx = NULL_byte;
    vListInitialiseItem(pxItemToRemove)
}

inline uxListRemove_pxIndex(pxList, SIZE, pxItemToRemoveTCB, pxItemToRemove)
{
    /* find the index of pxItemToRemove in pxList */
    for (hidden_idx: 0 .. (SIZE - 1)) {
        if
        :: pxList.ps[hidden_idx].p_tcb == pxItemToRemoveTCB ->
            vListInitialisePointer(pxList.ps[hidden_idx]);
            break
        :: else -> assert(hidden_idx < (SIZE - 1)) /* check reliability */
        fi
    }

    /* Make sure the index is left pointing to a valid item */
    if
    :: (pxList.pxIndex >= hidden_idx) && (pxList.pxIndex ^ xListEnd) ->
        pxList.pxIndex = ((pxList.pxIndex ^ 0) -> pxList.pxIndex - 1 : xListEnd)
    :: else
    fi;

    if
    :: hidden_idx < (SIZE - 1) ->
        /* move items behind the index position of pxList forward */
        for (hidden_idx: (hidden_idx + 1) .. (SIZE - 1)) {
            if
            :: !listPOINTER_IS_NULL(pxList.ps[hidden_idx]) ->
                assert(pxList.ps[hidden_idx].p_tcb != pxItemToRemoveTCB);
                swapListPointers(pxList.ps[hidden_idx - 1], pxList.ps[hidden_idx])
            :: else -> break
            fi
        }
    :: else
    fi;
    hidden_idx = NULL_byte;
    vListInitialiseItem(pxItemToRemove)
}

#endif
