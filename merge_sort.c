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
        }
        //@ assert permutation{Pre, Here}(arr, arr, 0, len);
        //@ assert sorted(arr, len);
    }
    int *const local_buf1 = buf1 + buf1_used;
    buf1_used += len/2;
    arrcpy(local_buf1, arr, len/2);
    int *const local_buf2 = buf2 + buf2_used;
    buf2_used += (len - len/2);
    arrcpy(local_buf2, arr + len/2, len - len/2);

    //@ assert \forall integer i; 0 <= i < len/2 ==> arr[i] == local_buf1[i];
    //@ assert \forall integer i; 0 <= i < len - len/2 ==> arr[len/2 + i] == local_buf2[i];

    //@ ghost before_recursion: ;

    merge_sort(local_buf1, len/2);
    //@ assert sorted(local_buf1, len/2);
    //@ assert count_unchanged{before_recursion, Here}(local_buf1, 0, len/2);
    merge_sort(local_buf2, len - len/2);
    //@ assert sorted(local_buf2, len - len/2);
    //@ assert count_unchanged{before_recursion, Here}(local_buf2, 0, len - len/2);

    merge(local_buf1, len/2, local_buf2, len - len/2, arr);

    buf1_used -= len/2;
    buf2_used -= len - len/2;
}
