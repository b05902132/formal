#include <limits.h>
#include <stddef.h>
#include <stdint.h>
#define MAX_LENGTH 2000
#define BUFFER_SIZE  MAX_LENGTH * 3

/*@
  axiomatic count_elem_axiom{
    logic integer count_elem{L}(int elem, int *arr, integer b, integer e) reads arr[b..e-1];
    axiom empty : \forall int elem, int *arr, integer b, e; b >= e ==> count_elem(elem, arr, b, e) == 0;
    axiom append_eq : \forall int elem, int *arr, integer b, e;
        arr[e] == elem ==> count_elem(elem, arr, b, e+1) == count_elem(elem, arr, b, e) + 1;
    axiom append_neq : \forall int elem, int *arr, integer b, e;
        arr[e] != elem ==> count_elem(elem, arr, b, e+1) == count_elem(elem, arr, b, e);
  }

  predicate permutation{L1, L2}(int *arr1, int *arr2, integer b, integer e) =
    \forall int v; count_elem{L1}(v, arr1, b, e) == count_elem{L2}(v, arr2, b, e);

  lemma perm_eq{L1, L2}: \forall int *arr1, int *arr2, integer b, integer e;
      (\forall integer i; b <= i < e ==> \at(arr1[i], L1) == \at(arr2[i], L2))
        ==> permutation{L1, L2}(arr1, arr2, b, e);

  predicate sorted(int *arr, integer len) = \forall integer i; 0 <= i < len-1  ==> arr[i] <= arr[i+1];

  lemma sorted_append: \forall int *arr, integer len;
    sorted(arr, len) && arr[len] >= arr[len - 1] ==> sorted(arr, len + 1);

  lemma sorted_all: \forall int *arr, integer len;
    sorted(arr, len) ==> \forall integer i, j; 0 <= i <= j < len ==> arr[i] <= arr[j];
*/

static unsigned int BUFFER[BUFFER_SIZE];

static unsigned int *buf = BUFFER;

static unsigned int * const buf_end = BUFFER + BUFFER_SIZE;


/*@
  predicate count_combine(int* a1, integer size1, int* a2, integer size2, int *out) =
    \forall int v; count_elem(v, a1, 0, size1) + count_elem(v, a2, 0, size2)
        == count_elem(v, out, 0, size1 + size2);
  axiomatic merge_len_axiom{
    logic integer merge_len(int *arr1, integer len1, int *arr2, integer len2) reads arr1[0..len1-1], arr2[0..len2-1];
    axiom merge_empty : \forall int *arr1, *arr2, integer len; merge_len(arr1, 0, arr2, 0) == 0;
    axiom left : \forall int *arr1, *arr2, integer len1, len2;
        arr1[len1] > arr2[len2] ==>
            merge_len(arr1, len1 + 1, arr2, len2) == merge_len(arr1, len1, arr2, len2) + 1;
    axiom right : \forall int *arr1, *arr2, integer len1, len2;
        arr1[len1] <= arr2[len2] ==>
            merge_len(arr1, len1, arr2, len2 + 1) == merge_len(arr1, len1, arr2, len2) + 1;

  }
*/

//@ logic int min(int a, int b) = a <= b ? a : b;

/*@
  requires \valid_read(arr1 + (0..len1-1));
  requires \valid_read(arr2 + (0..len2-1));
  requires \separated(out + (0 .. len1 + len2 - 1), arr1 + (0 .. len1 - 1));
  requires \separated(out + (0 .. len1 + len2 - 1), arr2 + (0 .. len2 - 1));
  requires len1 + len2 <= SIZE_MAX;
  requires sorted(arr1, len1);
  requires sorted(arr2, len2);
  requires \valid(out + (0..len1 + len2 - 1));
  assigns out[0..len1 + len2 - 1];
  ensures sorted(out, len1 + len2);
  ensures count_combine(arr1, len1, arr2, len2, out);
*/
void merge(int *arr1, size_t len1, int *arr2, size_t len2, int *out)
{
    size_t i1 = 0;
    size_t i2 = 0;
    /*@
      loop invariant 0 <= i1 <= len1;
      loop invariant 0 <= i2 <= len2;
      loop invariant i1 <= len1 ==>
        \forall integer i; 0 <= i < i1 + i2 ==> out[i] <= arr1[i1];
      loop invariant i2 <= len2 ==>
        \forall integer i; 0 <= i < i1 + i2 ==> out[i] <= arr2[i2];
      loop invariant sorted(out, i1 + i2);
      loop invariant count_combine(arr1, i1, arr2, i2, out);
      loop assigns out[0..len1 + len2 - 1], i1, i2;
      loop variant len1 + len2 - i1 - i2;
    */
    while (i1 < len1 && i2 < len2) {
        if (arr1[i1] > arr2[i2]) {
            out[i1 + i2] = arr2[i2];
            i2 += 1;
            //@ assert i1 <len1 ==> out[i1 + i2 - 1] <= arr1[i1];
            //@ assert i2 <len2 ==> out[i1 + i2 - 1] <= arr2[i2];
        } else {
            out[i1 + i2] = arr1[i1];
            i1 += 1;
        }
        //@ assert out[i1 + i2 - 1] == \at(min(arr1[i1], arr2[i2]), LoopCurrent);
        //@ assert i1 <len1 && i2 <len2 ==> out[i1 + i2 - 1] <= min(arr1[i1], arr2[i2]);
        //@ assert i1 <len1 && i2 <len2 ==> \at(min(arr1[i1], arr2[i2]), LoopCurrent) <= min(arr1[i1], arr2[i2]);
    }
}

/*@
  requires \valid(arr + (0..len-1));
  requires \valid(buf + (0..buf_end - buf -1));
  requires len <= MAX_LENGTH;
  requires buf + len <= buf_end;
  requires \separated ( (arr + (0..len-1)),
                        (buf + (0..len-1)) );
*/
void merge_aux(unsigned int *arr, size_t len)
{
    unsigned int * const aux_buf = buf;
    buf += len / 2;
    merge_aux(aux_buf, len/2);
    buf -= len/2;

}
