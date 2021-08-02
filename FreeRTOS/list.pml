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
    byte p_tcb_item;
};

#define listPOINTER_IS_NULL(pxListPointer) (pxListPointer.p_tcb_item == NULL_byte)

inline listPOINTER_RESET(pxListPointer)
{
    pxListPointer.p_tcb_item = NULL_byte
}

inline listPOINTER_SET(pxListPointer, tcb, item)
{
    /* prevent p_tcb_item becoming NULL_byte or xListEnd */
    assert(tcb < 127 && item < 2);
    pxListPointer.p_tcb_item = (tcb << 1) | item
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
#define __GET_LIST_ITEM(tcb, item)      TCBs[__OWNER_OF(tcb)].ListItems[item]
#define GET_LIST_ITEM_FROM_POINTER(p)   __GET_LIST_ITEM(p >> 1, p & 1)

#define pxNewListItem                   __GET_LIST_ITEM(pxNewListItemTCB, xStateORxEvent)
#define pxItemToRemove                  __GET_LIST_ITEM(pxItemToRemoveTCB, xStateORxEvent)
#define pxOrdinalListItem(pxList, ord)  GET_LIST_ITEM_FROM_POINTER(pxList.ps[ord].p_tcb_item)
#define pxFirstListItem(pxList)         pxOrdinalListItem(pxList, 0)

#define listGET_ITEM_VALUE_OF_HEAD_ENTRY(pxList) \
    listGET_LIST_ITEM_VALUE(pxFirstListItem(pxList))

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
        pxTCB = pxList.ps[pxList.pxIndex].p_tcb_item >> 1
    )
}

#define listGET_OWNER_OF_HEAD_ENTRY(pxList) (pxList.ps[0].p_tcb_item >> 1)

#define listIS_CONTAINED_WITHIN(xCID, pxListItem) (listLIST_ITEM_CONTAINER(pxListItem) == (xCID))

inline vListInitialiseItem(pxItem)
{
    listSET_LIST_ITEM_CONTAINER(pxItem, NULL_byte)
}

#define vListInitialisePointer listPOINTER_RESET

inline vListInitialise(pxList, SIZE)
{
    for (idx: 0 .. (SIZE - 1)) {
        vListInitialisePointer(pxList.ps[idx])
    }
    idx = 0
}

inline vListInitialise_pxIndex(pxList, SIZE)
{
    pxList.pxIndex = xListEnd;
    for (idx: 0 .. (SIZE - 1)) {
        vListInitialisePointer(pxList.ps[idx])
    }
    idx = 0
}

inline swapListPointers(aListPointer, bListPointer)
{
    aListPointer.p_tcb_item = aListPointer.p_tcb_item ^ bListPointer.p_tcb_item;
    bListPointer.p_tcb_item = bListPointer.p_tcb_item ^ aListPointer.p_tcb_item;
    aListPointer.p_tcb_item = aListPointer.p_tcb_item ^ bListPointer.p_tcb_item;
}

inline vListInsertEnd(pxList, SIZE, xCID, pxNewListItemTCB, xStateORxEvent)
{
    assert(listLIST_IS_NOT_FULL(pxList, SIZE));

    for (idx: 0 .. (SIZE - 1)) {
        if
        :: listPOINTER_IS_NULL(pxList.ps[idx]) ->
            listSET_LIST_ITEM_CONTAINER(pxNewListItem, xCID);
            listPOINTER_SET(pxList.ps[idx], pxNewListItemTCB, xStateORxEvent);
            break
        :: else
        fi
    }
    idx = 0
}

inline vListInsertEnd_pxIndex(pxList, SIZE, xCID, pxNewListItemTCB, xStateORxEvent)
{
    assert(listLIST_IS_NOT_FULL(pxList, SIZE));

    /* Find the next null item */
    for (idx: 0 .. (SIZE - 1)) {
        if
        :: listPOINTER_IS_NULL(pxList.ps[idx]) -> break
        :: else
        fi
    }

    if
    :: pxList.pxIndex ^ xListEnd ->
        assert(pxList.pxIndex < idx);
        do
        :: pxList.pxIndex < idx ->
            swapListPointers(pxList.ps[idx - 1], pxList.ps[idx]);
            idx = idx - 1
        :: else ->
            assert(pxList.pxIndex == idx);
            pxList.pxIndex = pxList.pxIndex + 1;
            break
        od
    :: else
    fi;

    assert(listPOINTER_IS_NULL(pxList.ps[idx]));
    listSET_LIST_ITEM_CONTAINER(pxNewListItem, xCID);
    listPOINTER_SET(pxList.ps[idx], pxNewListItemTCB, xStateORxEvent);
    idx = 0
}

inline vListInsert(pxList, SIZE, xCID, pxNewListItemTCB, xStateORxEvent, temp_var)
{
    assert(listLIST_IS_NOT_FULL(pxList, SIZE) && temp_var == NULL_byte);

    for (idx: 0 .. (SIZE - 1)) {
        /* Find the next null item */
        if
        :: listPOINTER_IS_NULL(pxList.ps[idx]) -> break;
        :: else
        fi;
        /* Find the first place to insert the new item */
        if
        :: (temp_var == NULL_byte) &&
           (listGET_LIST_ITEM_VALUE(pxOrdinalListItem(pxList, idx)) > listGET_LIST_ITEM_VALUE(pxNewListItem)) ->
            temp_var = idx
        :: else
        fi
    }

    if
    :: temp_var ^ NULL_byte ->
        /* replace the item at the temp_var by the last null item */
        assert(temp_var < idx);
        do
        :: temp_var < idx ->
            swapListPointers(pxList.ps[idx - 1], pxList.ps[idx]);
            idx = idx - 1
        :: else ->
            assert(temp_var == idx);
            temp_var = NULL_byte;
            break
        od
    :: else
    fi;

    /* place pxNewListItem at the index position of pxList */
    assert(listPOINTER_IS_NULL(pxList.ps[idx]));
    listSET_LIST_ITEM_CONTAINER(pxNewListItem, xCID);
    listPOINTER_SET(pxList.ps[idx], pxNewListItemTCB, xStateORxEvent);
    idx = 0
}

#if 0
    In FreeRTOS, the return value of uxListRemove only compares with zero.
    In the model, the comparison can be establishtd by listLIST_IS_EMPTY
    macro since pxList is known.
#endif

inline uxListRemove(pxList, SIZE, pxItemToRemoveTCB, xStateORxEvent)
{
    /* find the index of pxItemToRemove in pxList */
    for (idx: 0 .. (SIZE - 1)) {
        if
        :: (pxList.ps[idx].p_tcb_item >> 1) == pxItemToRemoveTCB ->
            assert((pxList.ps[idx].p_tcb_item & 1) == xStateORxEvent);
            vListInitialisePointer(pxList.ps[idx]);
            break
        :: else -> assert(idx < (SIZE - 1)) /* check reliability */
        fi
    }

    if
    :: idx < (SIZE - 1) ->
        /* move items behind the index position of pxList forward */
        for (idx: (idx + 1) .. (SIZE - 1)) {
            if
            :: !listPOINTER_IS_NULL(pxList.ps[idx]) ->
                swapListPointers(pxList.ps[idx - 1], pxList.ps[idx])
            :: else -> break
            fi
        }
    :: else
    fi;
    idx = 0;
    vListInitialiseItem(pxItemToRemove)
}

inline uxListRemove_pxIndex(pxList, SIZE, pxItemToRemoveTCB, xStateORxEvent)
{
    /* find the index of pxItemToRemove in pxList */
    for (idx: 0 .. (SIZE - 1)) {
        if
        :: (pxList.ps[idx].p_tcb_item >> 1) == pxItemToRemoveTCB ->
            assert((pxList.ps[idx].p_tcb_item & 1) == xStateORxEvent);
            vListInitialisePointer(pxList.ps[idx]);
            break
        :: else -> assert(idx < (SIZE - 1)) /* check reliability */
        fi
    }

    /* Make sure the index is left pointing to a valid item */
    if
    :: (pxList.pxIndex >= idx) && (pxList.pxIndex ^ xListEnd) ->
        pxList.pxIndex = ((pxList.pxIndex ^ 0) -> pxList.pxIndex - 1 : xListEnd)
    :: else
    fi;

    if
    :: idx < (SIZE - 1) ->
        /* move items behind the index position of pxList forward */
        for (idx: (idx + 1) .. (SIZE - 1)) {
            if
            :: !listPOINTER_IS_NULL(pxList.ps[idx]) ->
                swapListPointers(pxList.ps[idx - 1], pxList.ps[idx])
            :: else -> break
            fi
        }
    :: else
    fi;
    idx = 0;
    vListInitialiseItem(pxItemToRemove)
}

#endif
