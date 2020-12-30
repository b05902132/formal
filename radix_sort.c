#include <limits.h>
#include <stddef.h>


/*@
  logic integer power(integer base, integer pow) = (pow <= 0) ? 1 : base * power(base, pow-1);
  lemma two_power_x_is_one_shift_x :
    \forall integer x;
        x >= 0 ==> (1 << x) == power(2, x);
*/

/*@
  requires radix < 8 * sizeof(unsigned int);
  assigns \nothing;
*/
int radix_sort_cmp(unsigned int lhs, unsigned int rhs, size_t radix)
{
    unsigned int mask = (unsigned int) 1<<radix;
    return (int) lhs & mask - (int) rhs & mask;
}

/*@
  requires \valid(lhs);
  requires \valid(rhs);
  assigns *lhs, *rhs;
  ensures \at(*lhs, Pre) == *rhs && \at(*rhs, Pre) == *lhs;
*/
void swap(unsigned int *lhs, unsigned int *rhs){
    unsigned int temp = *lhs;
    *lhs = *rhs;
    *rhs = temp;
}

void radix_sort_merge(unsigned int *arr, size_t beg, size_t end, size_t radix)
{
    if (end - beg <= 1) {
        return;
    }
    if (end - beg == 2) {
        if (radix_sort_cmp(arr[beg], arr[end], radix) < 0) {
            swap(&arr[beg], &arr[end]);
        }
        return;
    }
    size_t mid = beg + (end - beg) / 2;
}

void radix_sort_aux(unsigned int *arr, size_t beg, size_t end, size_t radix)
{
}

void radix_sort(unsigned int* arr, size_t beg, size_t end)
{
}
