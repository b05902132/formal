#include "merge_sort.h"

// Two buffers are needed to prevent aliasing problems.
// See static_buffer1.c and its proof script for IMPOSSIBLE for details.

int buf1[BUF_SIZE];
size_t buf1_used;
int buf2[BUF_SIZE];
size_t buf2_used;

void merge_sort(int *arr, size_t len)
{
    if (len < 2) {
        return;
    }
    if (len == 2) {
        if (arr[0] > arr[1]) {
            int tmp = arr[0];
            arr[0] = arr[1];
            arr[1] = tmp;
            //@ assert array_elem_swapped{Pre, Here}(arr, 2, 0, 1);
        }
        //@ assert permutation{Pre, Here}(arr, arr, len);
        //@ assert sorted(arr, len);
        return;
    }

    /* The following aux definitions help provers realize that the type of len/2 is size_t. */
    int *const left_arr = arr;
    int *const right_arr = arr + len/2;
    const size_t left_len = len / 2;
    const size_t right_len = len - len / 2;
    /* End aux definitions */

    //@ assert same_array{Pre, Here}(left_arr, arr, len/2);
    //@ assert same_array{Pre, Here}(right_arr, arr + len/2, len - len/2);

    //@ ghost before_arrcpy: ;
    int *const local_buf_left = buf1 + buf1_used;
    buf1_used += left_len;
    arrcpy(local_buf_left, arr, left_len);
    int *const local_buf_right = buf2 + buf2_used;
    buf2_used += right_len;
    arrcpy(local_buf_right, right_arr, right_len);


    //@ assert same_array{Here, Here}(left_arr, local_buf_left, left_len);
    //@ assert double_shift : same_array{Here, Here}(right_arr, local_buf_right, right_len);
    //@ assert permutation{before_arrcpy, Here}(left_arr, local_buf_left, left_len);
    //@ assert permutation{before_arrcpy, Here}(right_arr, local_buf_right, right_len);


    //@ ghost before_recursion1: ;
    merge_sort(local_buf_left, left_len);
    //@ assert permutation{before_recursion1, Here}(left_arr, local_buf_left, left_len);
    //@ assert permutation{before_recursion1, Here}(right_arr, local_buf_right, right_len);
    //@ ghost before_recursion2: ;
    merge_sort(local_buf_right, right_len);
    //@ assert sorted(local_buf_left, left_len);
    //@ assert sorted(local_buf_right, right_len);


    //@ assert same_array{before_recursion2, Here}(local_buf_left, local_buf_left, left_len);
    //@ assert permutation{before_recursion2, Here}(local_buf_left, local_buf_left, left_len);
    //@ assert permutation{before_recursion2, Here}(local_buf_right, local_buf_right, right_len);

    //@ assert permutation{before_recursion1, Here}(local_buf_left, local_buf_left, left_len);
    //@ assert permutation{before_recursion1, Here}(local_buf_right, local_buf_right, right_len);

    //@ assert permutation{before_recursion1, Here}(left_arr, local_buf_left, left_len);
    //@ assert permutation{before_recursion1, Here}(right_arr, local_buf_right, right_len);

    //@ assert permutation{Pre, Here}(arr, local_buf_left, len/2);
    //@ assert permutation{Pre, Here}(arr + len/2 , local_buf_right, len - len/2);

    //@ assert count_combine{Pre}(arr, len/2, arr + len/2, len - len/2, arr);

    //TODO : Use preceding three assersions to prove the following assertion.

    //@ assert count_combine(local_buf_left, left_len, local_buf_right, right_len, arr);

    merge(local_buf_left, left_len, local_buf_right, right_len, arr);

    //@ assert count_combine(local_buf_left, left_len, local_buf_right, right_len, arr);
    //TODO Use count_combine to prove the following:
    //@ assert permutation{Pre, Here}(arr, arr, len);

    buf1_used -= len/2;
    buf2_used -= len - len/2;
}
