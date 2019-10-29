#ifndef _LIST_
#define _LIST_

#include "../FreeRTOS.pml"

typedef ListItem_t {
    byte Value_Owner;
    byte RESERVED_Container; /* The upper 4 bits are reserved. */
};

#define listGET_LIST_ITEM_OWNER(pxListItem) get_lower_byte(pxListItem.Value_Owner)
inline listSET_LIST_ITEM_OWNER(pxListItem, uxOwner)
{
    assert(0 <= (uxOwner) && (uxOwner) < 16);
    set_lower_byte(pxListItem.Value_Owner, uxOwner)
}

#define listGET_LIST_ITEM_VALUE(pxListItem) get_upper_byte(pxListItem.Value_Owner)
inline listSET_LIST_ITEM_VALUE(pxListItem, uxValue)
{
    assert(0 <= (uxValue) && (uxValue) < 16);
    set_upper_byte(pxListItem.Value_Owner, uxValue)
}

#define listLIST_ITEM_CONTAINER(pxListItem) get_lower_byte(pxListItem.RESERVED_Container)
inline listSET_LIST_ITEM_CONTAINER(pxListItem, uxContainer)
{
    assert(0 <= (uxContainer) && (uxContainer) < 16);
    set_lower_byte(pxListItem.RESERVED_Container, uxContainer)
}

/* The model needs to arrange a fix memory at the compile time, we use an array
 * to simulate a linked list. */
#define LIST_SIZE   5
#if (LIST_SIZE < 2)
#error LIST_SIZE must greater than 1
#endif

typedef List_t {
    ListItem_t indices[LIST_SIZE];
};

#define listGET_ITEM_VALUE_OF_HEAD_ENTRY(pxList) listGET_LIST_ITEM_VALUE(pxList.indices[0])

#define listLIST_IS_EMPTY(pxList) (listLIST_ITEM_CONTAINER(pxList.indices[0]) == NULL_nibble)
#define listLIST_LENGTH_IS_EXCEEDING_ZERO(pxList)   (listLIST_ITEM_CONTAINER(pxList.indices[0]) != NULL_nibble)
#define listLIST_LENGTH_IS_EXCEEDING_ONE(pxList)    (listLIST_ITEM_CONTAINER(pxList.indices[1]) != NULL_nibble)
#define listLIST_LENGTH_EQUALS_CURRENTNUMBEROFTASKS(pxList) (listLIST_ITEM_CONTAINER(pxList.indices[uxCurrentNumberOfTasks - 1]) != NULL_nibble)

inline listGET_OWNER_OF_NEXT_ENTRY(_id, pxTCB, pxList)
{
    AWAIT_A(_id,
        assert(pxTCB == NULL_byte || pxTCB == pxCurrentTCB);
        assert(listLIST_ITEM_CONTAINER(pxList.indices[0]) != NULL_nibble);
        for (idx: 1 .. (LIST_SIZE - 1)) {
            if
            :: listLIST_ITEM_CONTAINER(pxList.indices[idx]) != NULL_nibble ->
                swapListItems(pxList.indices[idx - 1], pxList.indices[idx])
            :: else ->
                break
            fi
        }
        idx = 0 );

    AWAIT_D(_id, pxTCB = listGET_LIST_ITEM_OWNER(pxList.indices[0]))
}

#define listGET_OWNER_OF_HEAD_ENTRY(pxList) listGET_LIST_ITEM_OWNER(pxList.indices[0])

#define listIS_CONTAINED_WITHIN(pxListIdx, pxListItem) (listLIST_ITEM_CONTAINER(pxListItem) == (pxListIdx))

inline vListInitialiseItem(pxItem)
{
    listSET_LIST_ITEM_CONTAINER(pxItem, NULL_nibble)
}

inline vListInitialise(pxList)
{
    for (idx: 0 .. (LIST_SIZE - 1)) {
        vListInitialiseItem(pxList.indices[idx])
    }
    idx = 0
}

/* deep copy list item */
inline dcListItem(varListItem, valListItem)
{
    varListItem.Value_Owner = valListItem.Value_Owner;
    varListItem.RESERVED_Container = valListItem.RESERVED_Container
}

/* swap two list items in-place */
inline swapListItems(aListItem, bListItem)
{
    aListItem.Value_Owner = aListItem.Value_Owner ^ bListItem.Value_Owner;
    bListItem.Value_Owner = bListItem.Value_Owner ^ aListItem.Value_Owner;
    aListItem.Value_Owner = aListItem.Value_Owner ^ bListItem.Value_Owner;
    aListItem.RESERVED_Container = aListItem.RESERVED_Container ^ bListItem.RESERVED_Container;
    bListItem.RESERVED_Container = bListItem.RESERVED_Container ^ aListItem.RESERVED_Container;
    aListItem.RESERVED_Container = aListItem.RESERVED_Container ^ bListItem.RESERVED_Container
}

inline vListInsertEnd(pxList, uxContainer, pxNewListItem)
{
    for (idx: 0 .. (LIST_SIZE - 1)) {
        if
        :: listLIST_ITEM_CONTAINER(pxList.indices[idx]) == NULL_nibble ->
            listSET_LIST_ITEM_CONTAINER(pxNewListItem, uxContainer);
            dcListItem(pxList.indices[idx], pxNewListItem);
            break
        :: else ->
            assert(idx < (LIST_SIZE - 1)) /* fullness check */
        fi
    }
    idx = 0
}

inline vListInsert(pxList, uxContainer, pxNewListItem, temp_var)
{
    assert(temp_var == NULL_byte);
    /* find the index of the insertion */
    for (idx: 0 .. (LIST_SIZE - 1)) {
        if
        :: (listLIST_ITEM_CONTAINER(pxList.indices[idx]) != NULL_nibble && listGET_LIST_ITEM_VALUE(pxList.indices[idx]) > listGET_LIST_ITEM_VALUE(pxNewListItem)) ||
           (listLIST_ITEM_CONTAINER(pxList.indices[idx]) == NULL_nibble) ->
           listSET_LIST_ITEM_CONTAINER(pxNewListItem, uxContainer);
           break
        :: else ->
            assert(idx < (LIST_SIZE - 1)) /* fullness check */
        fi
    }

    /* put pxNewListItem at the index of pxList */
    if
    :: listLIST_ITEM_CONTAINER(pxList.indices[idx]) == NULL_nibble ->
        /* as same as vListInsertEnd */
        dcListItem(pxList.indices[idx], pxNewListItem)
    :: else ->
        /* Move the items behind the index one slot later */
        assert(listLIST_ITEM_CONTAINER(pxList.indices[LIST_SIZE - 1]) == NULL_nibble); /* fullness check */
        temp_var = idx;
        for (idx: temp_var .. (LIST_SIZE - 1)) {
            swapListItems(pxNewListItem, pxList.indices[idx]);
            if
            :: listLIST_ITEM_CONTAINER(pxNewListItem) == NULL_nibble ->
                /* recover the last item */
                dcListItem(pxNewListItem, pxList.indices[temp_var]);
                break
            :: else
            fi
        }
        temp_var = NULL_byte
    fi;
    idx = 0
}

// TODO: double insertion
inline uxListRemove(pxList, pxItemToRemove, uReturn)
{
    /* find the index of the insertion */
    for (idx: 0 .. (LIST_SIZE - 1)) {
        if
        :: listGET_LIST_ITEM_OWNER(pxList.indices[idx]) == listGET_LIST_ITEM_OWNER(pxItemToRemove) ->
            // TODO: equal macro
            assert(listGET_LIST_ITEM_VALUE(pxList.indices[idx]) == listGET_LIST_ITEM_VALUE(pxItemToRemove));
            assert(listLIST_ITEM_CONTAINER(pxList.indices[idx]) == listLIST_ITEM_CONTAINER(pxItemToRemove));
            pxList.indices[idx].Value_Owner = 0; // FIXME
            vListInitialiseItem(pxList.indices[idx]);
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
            :: listLIST_ITEM_CONTAINER(pxList.indices[LIST_SIZE - idx]) != NULL_nibble ->
                uReturn = LIST_SIZE - idx;
                swapListItems(pxList.indices[0], pxList.indices[LIST_SIZE - idx]);
                break
            :: else ->
                uReturn = LIST_SIZE - idx - 1
            fi
        }
    :: idx == (LIST_SIZE - 1) ->
        uReturn = idx
    :: else ->
        /* Move the items behind the index forward */
        for (idx: (idx + 1) .. (LIST_SIZE - 1)) {
            if
            :: listLIST_ITEM_CONTAINER(pxList.indices[idx]) == NULL_nibble ->
                uReturn = idx - 1;
                break
            :: else ->
                swapListItems(pxList.indices[idx - 1], pxList.indices[idx]);
                uReturn = idx
            fi
        }
    fi;
    idx = 0;
    vListInitialiseItem(pxItemToRemove);
}

#endif
