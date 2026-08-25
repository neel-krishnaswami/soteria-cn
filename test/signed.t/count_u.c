// The unsigned counter loop: body guard and spec invariant must agree on
// unsigned comparison semantics.
unsigned int count_up(unsigned int n)
/*@ requires n < 1000u32;
    ensures return == n; @*/
{
  unsigned int i = 0;
  while (i < n)
  /*@ inv i <= n; n < 1000u32; {n} unchanged; @*/
  {
    i = i + 1;
  }
  return i;
}
