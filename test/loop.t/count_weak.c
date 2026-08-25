// The invariant forgets the upper bound, so the postcondition cannot be
// proved after the loop.
int count_weak(int n)
/*@ requires 0i32 <= n; n < 1000i32;
    ensures return == n; @*/
{
  int i = 0;
  while (i < n)
  /*@ inv 0i32 <= i; n < 1000i32; {n} unchanged; @*/
  {
    i = i + 1;
  }
  return i;
}
