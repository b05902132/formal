#include "merge_sort.h"

/*@
  lemma adj_sorted: \forall int *arr, integer i, len;
    (0 < i < len ==> arr[i-1] <= arr[i]) ==> sorted(arr, len);

  lemma count_combine_append_1:
    \forall int *a1, *a2, *out, integer size1, size2;
        count_combine(a1, size1, a2, size2, out) && a1[size1] == out[size1 + size2]
            ==> count_combine(a1, size1+1, a2, size2, out);
  lemma count_combine_append_2:
    \forall int *a1, *a2, *out, integer size1, size2;
        count_combine(a1, size1, a2, size2, out) && a2[size2] == out[size1 + size2]
            ==> count_combine(a1, size1, a2, size2+1, out);
*/
void merge(const int *arr1, size_t len1, const int *arr2, size_t len2, int *out)
{
    size_t i_1 = 0;
    size_t i_2 = 0;
    size_t i_out = 0; // this variable aids theorem prover.
    /*@
      loop invariant 0 <= i_1 <= len1;
      loop invariant 0 <= i_2 <= len2;
      loop invariant i_out == i_1 + i_2;
      loop invariant out_bounded_arr1:
        i_1 < len1 ==> \forall integer i; 0 <= i < i_1 + i_2 ==> out[i] <= arr1[i_1];
      loop invariant out_bounded_arr2:
        i_2 < len2 ==> \forall integer i; 0 <= i < i_1 + i_2 ==> out[i] <= arr2[i_2];
      loop invariant sorted(out, i_out);
      loop invariant count_combine(arr1, i_1, arr2, i_2, out);
      loop assigns out[0..i_out - 1], i_1, i_2, i_out;
      loop variant len1 + len2 - i_out;
    */
    while (i_1 < len1 && i_2 < len2) {
        if (arr1[i_1] > arr2[i_2]) {
            out[i_out] = arr2[i_2];
            /* The auto prover are not smart enough to prove loop1_append_i2;
             * they require some aid to prove that the counts are not affected by this assignment,
             * hence the assertions about count_unchanged.
             * However, they cannot be autoproved without the first 3 assertions...
             */
            //@ assert same_array{LoopCurrent, Here}(arr1, arr1, i_1);
            //@ assert same_array{LoopCurrent, Here}(arr2, arr2, i_2);
            //@ assert same_array{LoopCurrent, Here}(out, out, i_1 + i_2);
            //@ assert permutation{LoopCurrent, Here}(arr1, arr1, i_1);
            //@ assert permutation{LoopCurrent, Here}(arr2, arr2, i_2);
            //@ assert permutation{LoopCurrent, Here}(out, out, i_out);
            //@ assert loop1_append_i2: count_combine(arr1, i_1, arr2, i_2+1, out);
            i_2 += 1;
            i_out += 1;
            //@ assert bound_aid_arr2: i_2 < len2 ==> out[i_1 + i_2 - 1] <= arr2[i_2];
            //@ assert sorted(out, i_1 + i_2 - 1);
        } else {
            out[i_out] = arr1[i_1];
            //@ assert same_array{LoopCurrent, Here}(arr1, arr1, i_1);
            //@ assert same_array{LoopCurrent, Here}(arr2, arr2, i_2);
            //@ assert same_array{LoopCurrent, Here}(out, out, i_1 + i_2);
            //@ assert permutation{LoopCurrent, Here}(arr1, arr1, i_1);
            //@ assert permutation{LoopCurrent, Here}(arr2, arr2, i_2);
            //@ assert permutation{LoopCurrent, Here}(out, out, i_out);
            //@ assert loop1_append_i1: count_combine(arr1, i_1+1, arr2, i_2, out);
            i_1 += 1;
            i_out += 1;
            //@ assert bound_aid_arr1: i_1 < len1 ==> out[i_1 + i_2 - 1] <= arr1[i_1];
            //@ assert sorted(out, i_1 + i_2 - 1);
        }
        //@ assert i_1 + i_2 >= 2 ==> out[i_1 + i_2 - 2] <= out[i_1 + i_2 - 1];
    }
}
