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
    unsigned int mask = 1<<radix;
    return (int) lhs & mask - (int) rhs & mask;
}

void radix_sort_aux(unsigned int *arr, unsigned int beg, unsigned int end, size_t radix)
{
}

void radix_sort(unsigned int* arr, unsigned int beg, unsigned int end)
{
}
