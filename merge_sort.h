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
  axiomatic count_elem_axiom{
    logic integer count_elem{L}(int elem, int *arr, integer b, integer e) reads arr[b..e-1];
    axiom empty :
        \forall int elem, int *arr, integer b, e; b >= e ==> count_elem(elem, arr, b, e) == 0;
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

  predicate unchanged{L1, L2}(int *arr, integer b, integer e) =
    \forall integer i; b <= i < e ==> \at(arr[i], L1) == \at(arr[i], L2);

  predicate count_unchanged{L1, L2}(int *arr, integer b, integer e) =
    \forall int elem; count_elem{L1}(elem, arr, b, e) == count_elem{L2}(elem, arr, b, e);

  lemma unchanged_same_count{L1, L2} :
    \forall int *arr, integer b, e;
      unchanged{L1, L2}(arr, b, e) ==> count_unchanged{L1, L2}(arr, b, e);


  predicate sorted{L}(int *arr, integer len) =
    \forall integer i, j; 0 <= i <= j < len  ==> arr[i] <= arr[j];

  lemma unchange_sorted{L1, L2}:
    \forall int *arr, integer len;
      unchanged{L1, L2}(arr, 0, len) && sorted{L1}(arr, len)
      ==> sorted{L2}(arr, len);


  lemma sorted_append: \forall int *arr, integer len;
    sorted(arr, len) && arr[len] >= arr[len - 1] ==> sorted(arr, len + 1);

  lemma sorted_all: \forall int *arr, integer len;
    sorted(arr, len) ==> \forall integer i, j; 0 <= i <= j < len ==> arr[i] <= arr[j];
*/



/*@
  predicate count_combine(int* a1, integer size1, int* a2, integer size2, int *out) =
    \forall int v; count_elem(v, a1, 0, size1) + count_elem(v, a2, 0, size2)
        == count_elem(v, out, 0, size1 + size2);
  lemma count_combine_append_1:
    \forall int *a1, *a2, *out, integer size1, size2;
        count_combine(a1, size1, a2, size2, out) && a1[size1] == out[size1 + size2]
            ==> count_combine(a1, size1+1, a2, size2, out);
  lemma count_combine_append_2:
    \forall int *a1, *a2, *out, integer size1, size2;
        count_combine(a1, size1, a2, size2, out) && a2[size2] == out[size1 + size2]
            ==> count_combine(a1, size1, a2, size2+1, out);
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
void merge(int *arr1, size_t len1, int *arr2, size_t len2, int *out);

/*@
  requires \valid(out + (0 .. len-1));
  requires \valid_read(in + (0 .. len-1));
  requires \separated(in + (0 .. len-1), out + (0 .. len-1));
  assigns out[0..len-1];
  ensures \forall integer i; 0 <= i < len ==> in[i] == out[i];
*/
void arrcpy(int *out, const int *in, size_t len);

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
  ensures permutation{Pre, Post}(arr, arr, 0, len);
  ensures sorted(arr, len);
  ensures \at(buf1_used, Post) == \at(buf1_used, Pre);
  ensures \at(buf2_used, Post) == \at(buf2_used, Pre);
*/
void merge_sort(int *arr, size_t len);
