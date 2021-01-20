#include <stdint.h>
#include <stddef.h>
#define LEN 10000
#define BUF_SIZE LEN * 3
static int buf1[BUF_SIZE];
size_t buf1_used;
static int buf2[BUF_SIZE];
size_t buf2_used;

/*@
  requires \valid(out + (0 .. len-1));
  requires \valid_read(in + (0 .. len-1));
  requires \separated(in + (0 .. len-1), out + (0 .. len-1));
  assigns out[0..len-1];
  ensures \forall integer i; 0 <= i < len ==> in[i] == out[i];
*/
void arrcpy(int *out, const int *in, size_t len)
{
    /*@
      loop invariant 0 <= i <= len;
      loop invariant \forall integer j; 0 <= j < i ==> out[j] == in[j];
      loop assigns i, out[0..len-1];
      loop variant len - i;
    */
    for(size_t i = 0; i < len; i++){
        out[i] = in[i];
    }
}


/*@
  requires \valid(arr + (0 .. len - 1));
  requires \separated(arr + (0.. len - 1), (buf1 + (buf1_used .. buf1_used + len - 1)));
  requires \separated(arr + (0.. len - 1), (buf2 + (buf2_used .. buf2_used + len * 2- 1)));
  requires buf1_used + len <= BUF_SIZE;
  requires buf2_used + len * 2<= BUF_SIZE;
  assigns buf1[buf1_used .. buf1_used + len - 1];
  assigns buf2[buf2_used .. buf2_used + len * 2 - 1];
  assigns buf1_used;
  assigns buf2_used;
  assigns arr[0 .. (len - 1)];
  ensures \forall integer i; 0 <= i < len ==> arr[i] == \at(arr[i], Pre);
  ensures \at(buf1_used, Post) == \at(buf1_used, Pre);
  ensures \at(buf2_used, Post) == \at(buf2_used, Pre);
*/
void recur(int *arr, size_t len)
{
    if (len < 2) {
        return;
    }
    int *const local_buf1 = buf1 + buf1_used;
    buf1_used += len/2;
    arrcpy(local_buf1, arr, len/2);
    int *const local_buf2 = buf2 + buf2_used;
    buf2_used += (len - len/2);
    arrcpy(local_buf2, arr + len/2, len - len/2);

    //@ assert \forall integer i; 0 <= i < len/2 ==> arr[i] == local_buf1[i];
    //@ assert \forall integer i; 0 <= i < len - len/2 ==> arr[len/2 + i] == local_buf2[i];

    recur(local_buf1, len/2);
    recur(local_buf2, len - len/2);

    arrcpy(arr, local_buf1, len/2);
    arrcpy(arr + len/2, local_buf2, len - len/2);

    buf1_used -= len/2;
    buf2_used -= len - len/2;
}
