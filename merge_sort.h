#include <limits.h>
#include <stdint.h>
#include <stddef.h>
#include "arrcpy.h"
#define LEN 10000
#define BUF_SIZE LEN * 3

extern int buf1[BUF_SIZE];
extern size_t buf1_used;
extern int buf2[BUF_SIZE];
extern size_t buf2_used;

/*@
  predicate swapped{L1, L2}(int *p, int *q) =
    \at(*p, L1) == \at(*q, L2) && \at(*p, L2) == \at(*q, L1);

  predicate array_elem_swapped{L1, L2}(int *arr, integer len, integer p, integer q) =
      0 <= p < len && 0 <= q < len && p != q && swapped{L1, L2}(arr + p, arr + q) &&
      \forall integer i; 0 <= i < len && i != p && i != q ==> \at(arr[p], L1) == \at(arr[i], L2);
*/

/*@
  axiomatic count_elem_axiom{
    logic integer count_elem{L}(int elem, int *arr, integer e) reads arr[0..e-1];
    axiom empty : \forall int elem, int *arr, integer e; e <= 0 ==> count_elem(elem, arr, e) == 0;
    axiom append_eq : \forall int elem, int *arr, integer e;
        e >= 0 && arr[e] == elem ==> count_elem(elem, arr, e+1) == count_elem(elem, arr, e) + 1;
    axiom append_neq : \forall int elem, int *arr, integer e;
        e >= 0 && arr[e] != elem ==> count_elem(elem, arr, e+1) == count_elem(elem, arr, e);
  }

  predicate permutation{L1, L2}(int *arr1, int *arr2, integer e) =
    \forall int v; count_elem{L1}(v, arr1, e) == count_elem{L2}(v, arr2, e);

  predicate same_array{L1, L2}(int *arr1, int *arr2, integer e) =
    \forall integer i; 0 <= i < e ==> \at(arr1[i], L1) == \at(arr2[i], L2);

  lemma perm_eq{L1, L2}: \forall int *arr1, int *arr2, integer e;
    same_array{L1, L2}(arr1, arr2, e) ==> permutation{L1, L2}(arr1, arr2, e);

  lemma perm_swap{L1, L2}: \forall int *arr1, integer e, p, q;
    array_elem_swapped{L1, L2}(arr1, e, p, q) ==> permutation{L1, L2}(arr1, arr1, e);

  lemma perm_trans{L1, L2, L3} : \forall int *arr1, int *arr2, int *arr3, integer e;
    permutation{L1, L2}(arr1, arr2, e) && permutation{L2, L3}(arr2, arr3, e)
    ==> permutation{L1, L3}(arr1, arr3, e);
*/



/*@
  predicate sorted(int *arr, integer len) =
    \forall integer i, j; 0 <= i <= j < len  ==> arr[i] <= arr[j];
*/



/*@
  predicate count_combine(int* a1, integer size1, int* a2, integer size2, int *out) =
    \forall int v; count_elem(v, a1, size1) + count_elem(v, a2, size2)
        == count_elem(v, out, size1 + size2);

  lemma count_combine_id:
    \forall int *a1, integer len1, len2; count_combine(a1, len1, a1 + len1, len2, a1);
*/


/*@
  requires \valid_read(arr1 + (0..len1-1));
  requires \valid_read(arr2 + (0..len2-1));
  requires \separated(out + (0 .. len1 + len2 - 1), arr1 + (0 .. len1 - 1));
  requires \separated(out + (0 .. len1 + len2 - 1), arr2 + (0 .. len2 - 1));
  requires len1 + len2 <= SIZE_MAX;
  requires arr1_sorted: sorted(arr1, len1);
  requires arr2_sorted: sorted(arr2, len2);
  requires \valid(out + (0..len1 + len2 - 1));
  assigns out[0..len1 + len2 - 1];
  ensures sorted(out, len1 + len2);
  ensures count_combine(arr1, len1, arr2, len2, out);
*/
void merge(const int *arr1, size_t len1, const int *arr2, size_t len2, int *out);

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
  ensures permutation{Pre, Post}(arr, arr, len);
  ensures sorted(arr, len);
  ensures \at(buf1_used, Post) == \at(buf1_used, Pre);
  ensures \at(buf2_used, Post) == \at(buf2_used, Pre);
*/
void merge_sort(int *arr, size_t len);
