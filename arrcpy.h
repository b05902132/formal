#include <stddef.h>
/*@
  requires \valid(out + (0 .. len-1));
  requires \valid_read(in + (0 .. len-1));
  requires \separated(in + (0 .. len-1), out + (0 .. len-1));
  assigns out[0..len-1];
  ensures \forall integer i; 0 <= i < len ==> in[i] == out[i];
*/
void arrcpy(int *out, const int *in, size_t len);
