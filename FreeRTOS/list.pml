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

/* The model needs to arrange a fix memory at the compile time, we use an array
 * to simulate a linked list. */
#define LIST_SIZE   5
#if (LIST_SIZE < 2)
#error LIST_SIZE must greater than 1
#endif

typedef List_p {
    byte tcb_item;
};

#define listPOINTER_IS_NULL(pxListPointer) (pxListPointer.tcb_item == NULL_byte)

inline listPOINTER_RESET(pxListPointer)
{
    pxListPointer.tcb_item = NULL_byte
}

inline listPOINTER_SET(pxListPointer, tcb, item)
{
    /* tcb must less than 127 to prevent tcb_item becoming NULL_byte. */
    assert(tcb < 127 && item < 2);
    pxListPointer.tcb_item = (tcb << 1) | item
}

typedef List_t {
    List_p ps[LIST_SIZE];
};

#define pxFirstListItem(pxList) TCBs[pxList.ps[0].tcb_item >> 1].ListItems[pxList.ps[0].tcb_item & 1]
#define pxNewListItem   TCBs[pxNewListItemIdx].ListItems[xStateORxEvent]
#define pxIterListItem  TCBs[pxList.ps[idx].tcb_item >> 1].ListItems[pxList.ps[idx].tcb_item & 1]
#define pxItemToRemove  TCBs[pxItemToRemoveIdx].ListItems[xStateORxEvent]

#define listGET_ITEM_VALUE_OF_HEAD_ENTRY(pxList) listGET_LIST_ITEM_VALUE(pxFirstListItem(pxList))

#define listLIST_IS_EMPTY(pxList)                   listPOINTER_IS_NULL(pxList.ps[0])
#define listLIST_LENGTH_IS_EXCEEDING_ZERO(pxList)   (!listPOINTER_IS_NULL(pxList.ps[0]))
#define listLIST_LENGTH_IS_EXCEEDING_ONE(pxList)    (!listPOINTER_IS_NULL(pxList.ps[1]))
#define listLIST_LENGTH_EQ_CURRENTNUMBEROFTASKS(pxList) \
    ((LIST_SIZE >= uxCurrentNumberOfTasks && !listPOINTER_IS_NULL(pxList.ps[uxCurrentNumberOfTasks - 1])) \
    && (LIST_SIZE <= uxCurrentNumberOfTasks || listPOINTER_IS_NULL(pxList.ps[uxCurrentNumberOfTasks])))

inline listGET_OWNER_OF_NEXT_ENTRY(_id, pxTCB, pxList)
{
    AWAIT_A(_id,
        assert(pxTCB == NULL_byte || pxTCB == pxCurrentTCB);
        assert(!listPOINTER_IS_NULL(pxList.ps[0]));
        for (idx: 1 .. (LIST_SIZE - 1)) {
            if
            :: !listPOINTER_IS_NULL(pxList.ps[idx]) ->
                swapListPointers(pxList.ps[idx - 1], pxList.ps[idx])
            :: else ->
                break
            fi
        }
        idx = 0 );

    AWAIT_D(_id, pxTCB = (pxList.ps[0].tcb_item >> 1) + promela_EXP_NUMBER)
}

#define listGET_OWNER_OF_HEAD_ENTRY(pxList) ((pxList.ps[0].tcb_item >> 1) + promela_EXP_NUMBER)

#define listIS_CONTAINED_WITHIN(pxListIdx, pxListItem) (listLIST_ITEM_CONTAINER(pxListItem) == (pxListIdx))

inline vListInitialiseItem(pxItem)
{
    listSET_LIST_ITEM_CONTAINER(pxItem, NULL_byte)
}

#define vListInitialisePointer listPOINTER_RESET

inline vListInitialise(pxList)
{
    for (idx: 0 .. (LIST_SIZE - 1)) {
        vListInitialisePointer(pxList.ps[idx])
    }
    idx = 0
}

/* swap two list pointers in-place */
inline swapListPointers(aListPointer, bListPointer)
{
    aListPointer.tcb_item = aListPointer.tcb_item ^ bListPointer.tcb_item;
    bListPointer.tcb_item = bListPointer.tcb_item ^ aListPointer.tcb_item;
    aListPointer.tcb_item = aListPointer.tcb_item ^ bListPointer.tcb_item;
}

inline vListInsertEnd(pxList, uxContainer, pxNewListItemIdx, xStateORxEvent)
{
    for (idx: 0 .. (LIST_SIZE - 1)) {
        if
        :: listPOINTER_IS_NULL(pxList.ps[idx]) ->
            listSET_LIST_ITEM_CONTAINER(pxNewListItem, uxContainer);
            listPOINTER_SET(pxList.ps[idx], pxNewListItemIdx, xStateORxEvent);
            break
        :: else ->
            assert(idx < (LIST_SIZE - 1)) /* fullness check */
        fi
    }
    idx = 0
}

inline vListInsert(pxList, uxContainer, pxNewListItemIdx, xStateORxEvent, temp_var)
{
    assert(temp_var == NULL_byte);
    /* find the index of the insertion */
    for (idx: 0 .. (LIST_SIZE - 1)) {
        if
        :: listPOINTER_IS_NULL(pxList.ps[idx]) ||
           (listGET_LIST_ITEM_VALUE(pxIterListItem) > listGET_LIST_ITEM_VALUE(pxNewListItem)) ->
            listSET_LIST_ITEM_CONTAINER(pxNewListItem, uxContainer);
            break
        :: else ->
            assert(idx < (LIST_SIZE - 1)) /* fullness check */
        fi
    }

    /* put pxNewListItem at the index of pxList */
    assert(listPOINTER_IS_NULL(pxList.ps[LIST_SIZE - 1])); /* fullness check */
    listPOINTER_SET(pxList.ps[LIST_SIZE - 1], pxNewListItemIdx, xStateORxEvent);
    if
    :: idx < (LIST_SIZE - 1) ->
        temp_var = idx;
        for (idx: 1 .. (LIST_SIZE - temp_var - 1)) {
            swapListPointers(pxList.ps[LIST_SIZE - idx], pxList.ps[LIST_SIZE - idx - 1])
        }
        temp_var = NULL_byte
    :: else
    fi;
    idx = 0
}

inline uxListRemove(pxList, pxItemToRemoveIdx, xStateORxEvent, uReturn)
{
    /* find the index of the insertion */
    for (idx: 0 .. (LIST_SIZE - 1)) {
        if
        :: (pxList.ps[idx].tcb_item >> 1) == pxItemToRemoveIdx ->
            assert((pxList.ps[idx].tcb_item & 1) == xStateORxEvent);
            vListInitialisePointer(pxList.ps[idx]);
            break
        :: else ->
            assert(idx < (LIST_SIZE - 1)) /* fullness check */
        fi
    }

    if
    :: idx == 0 ->
        /* make sure the index (position 0) is left pointing to a valid item. */
        for (idx: 1 .. (LIST_SIZE - 1)) {
            if
            :: !listPOINTER_IS_NULL(pxList.ps[LIST_SIZE - idx]) ->
                uReturn = LIST_SIZE - idx;
                swapListPointers(pxList.ps[0], pxList.ps[LIST_SIZE - idx]);
                break
            :: else ->
                uReturn = 0 /* Last value: LIST_SIZE - idx(LIST_SIZE - 1) - 1 */
            fi
        }
    :: idx == (LIST_SIZE - 1) ->
        uReturn = idx
    :: else ->
        /* Move the items behind the index forward */
        for (idx: (idx + 1) .. (LIST_SIZE - 1)) {
            if
            :: listPOINTER_IS_NULL(pxList.ps[idx]) ->
                uReturn = idx - 1;
                break
            :: else ->
                swapListPointers(pxList.ps[idx - 1], pxList.ps[idx]);
                uReturn = (LIST_SIZE - 1) /* Last value: idx (LIST_SIZE - 1) */
            fi
        }
    fi;
    idx = 0;
    vListInitialiseItem(pxItemToRemove)
}

#endif
