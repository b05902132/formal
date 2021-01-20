#include "arrcpy.h"
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
