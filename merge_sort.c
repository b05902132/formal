#include "merge_sort.h"

// Two buffers are needed to prevent aliasing problems.
// See static_buffer1.c and its proof script for IMPOSSIBLE for details.

int buf1[BUF_SIZE];
size_t buf1_used;
int buf2[BUF_SIZE];
size_t buf2_used;

/*@
  lemma permutation_count_combine{L1, L2}:
    \forall int *a1, *b1, *out1, *a2, *b2, *out2, integer len_a, len_b;
     permutation{L1, L2}(a1, a2, len_a) && permutation{L1, L2}(b1, b2, len_b)
     && permutation{L1, L2}(out1, out2, len_a + len_b) && count_combine{L1}(a1, len_a, b1, len_b, out1)
     ==> count_combine{L2}(a2, len_a, b2, len_b, out2);
*/

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
            //@ assert permutation{Pre, Here}(arr, arr, 2);
        }
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

    //@ assert same_array{before_recursion1, Here}(local_buf_left, arr, left_len);
    //@ assert same_array{before_recursion1, Here}(local_buf_right, arr + left_len, right_len);

    //@ assert count_combine(arr, left_len, arr + left_len, right_len, arr);

    //@ assert count_combine(local_buf_left, left_len, local_buf_right, right_len, arr);

    //@ ghost before_merge: ;
    merge(local_buf_left, left_len, local_buf_right, right_len, arr);

    //@ assert same_array{before_merge,Here}(local_buf_left, local_buf_left, left_len);
    //@ assert same_array{before_merge,Here}(local_buf_right, local_buf_right, right_len);
    //@ assert count_combine(local_buf_left, left_len, local_buf_right, right_len, arr);

    /* TODO: clear the redundent assertions */
    /*@ assert \forall int elem;
        count_elem{before_merge}(elem, arr, len)
        ==
        count_elem{before_merge}(elem, local_buf_left, left_len)
        + count_elem{before_merge}(elem, local_buf_right, right_len);
    */
    /*@ assert \forall int elem;
        count_elem{before_merge}(elem, local_buf_left, left_len)
        + count_elem{before_merge}(elem, local_buf_right, right_len)
        ==
        count_elem(elem, local_buf_left, left_len)
        + count_elem(elem, local_buf_right, right_len);
    */
    /*@
       assert \forall int elem;
        count_elem(elem, local_buf_left, left_len)
        + count_elem(elem, local_buf_right, right_len)
        == count_elem(elem, arr, len);
    */
    /*@ assert YUNOPROVETHIS: \forall int elem;
        count_elem{before_merge}(elem, arr, len)
        == count_elem(elem, arr, len);
    */
    //@ assert permutation{before_merge, Here}(arr, arr, len);
    //@ assert same_array{Pre, before_merge}(arr, arr, len);

    buf1_used -= len/2;
    buf2_used -= len - len/2;
}
