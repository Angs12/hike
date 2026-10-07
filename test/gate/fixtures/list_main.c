#include "ADTList.h"
#include <assert.h>
#include <stdio.h>

static int destroyed;

static int compare(void *a, void *b) {
    int x = *(int *)a, y = *(int *)b;
    return (x > y) - (x < y);
}

static void destroy(void *value) {
    destroyed += *(int *)value;
}

int main(void) {
    int a = 3, b = 5, c = 7, missing = 11;
    List list = list_create(0);
    assert(list_size(list) == 0);
    assert(list_first(list) == LIST_BOF && list_last(list) == LIST_EOF);
    list_insert_next(list, LIST_BOF, &a);
    list_insert_next(list, list_last(list), &b);
    list_insert_next(list, list_first(list), &c);
    assert(list_size(list) == 3);
    int sum = 0;
    for (ListNode node = list_first(list); node != LIST_EOF;
         node = list_next(list, node))
        sum += *(int *)list_node_value(list, node);
    assert(sum == 15);
    assert(list_find(list, &b, compare) == &b);
    assert(list_find_node(list, &b, compare) == list_last(list));
    assert(list_find(list, &missing, compare) == 0);
    assert(list_set_destroy_value(list, destroy) == 0);
    list_remove_next(list, list_first(list));
    assert(list_size(list) == 2 && destroyed == 7);
    list_remove_next(list, list_first(list));
    assert(list_last(list) == list_first(list) && destroyed == 12);
    list_remove_next(list, LIST_BOF);
    assert(list_size(list) == 0 && list_last(list) == LIST_EOF);
    list_insert_next(list, LIST_BOF, &b);
    list_destroy(list);
    assert(destroyed == 20);
    printf("list: sum=%d destroyed=%d\n", sum, destroyed);
    return 0;
}
