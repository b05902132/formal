#include <stdint.h>
#include <stddef.h>
#define LEN 10000
#define BUF_SIZE LEN * 3
static int buf[BUF_SIZE];

size_t buf_used;


/*@
  requires \valid(arr + (0 .. len - 1));
  requires \separated(arr + (0.. len - 1), (buf + (buf_used .. buf_used + 3 * len - 1)));
  requires buf_used + 3 * len <= BUF_SIZE;
  assigns buf[buf_used .. buf_used + 3 * len - 1];
  assigns buf_used;
  assigns arr[0 .. (len - 1)];
  ensures \forall integer i; 0 <= i < len ==> arr[i] == \at(arr[i], Pre);
  ensures \at(buf_used, Post) == \at(buf_used, Pre);
*/
void recur(int *arr, size_t len)
{
    if (len < 2) {
        return;
    }
    int * const local_buf = buf + buf_used;
    buf_used += len;
    /*@
      loop invariant 0 <= i <= len;
      loop invariant \forall integer j; 0 <= j < i ==> local_buf[j] == arr[j];
      loop assigns i, local_buf[0 .. (len - 1)];
      loop variant len - i;
    */
    for(int i = 0; i < len; i++) {
        local_buf[i] = arr[i];
    }
    //@ assert \forall integer i; 0 <= i < len ==> arr[i] == \at(arr[i], Pre);
    recur(local_buf, len/2);
before_recur2:
    recur(local_buf + len/2, len - len/2);
    //@ assert \forall integer j; 0 <= j < len/2 ==> local_buf[j] == \at(local_buf[j], before_recur2);
    //@ assert IMPOSSIBLE: \forall integer j; len/2 <= j < len ==> local_buf[j] == \at(local_buf[j], before_recur2);
    buf_used -= len;
}
