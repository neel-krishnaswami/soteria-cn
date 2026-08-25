// Wrong invariant: it is not preserved by the loop body, so consuming it at
// the back-edge must fail.
int count_bad(int n)
/*@ requires 0i32 <= n; n < 1000i32;
    ensures return == n; @*/
{
  int i = 0;
  while (i < n)
  /*@ inv 0i32 <= i; i == 0i32; n < 1000i32; {n} unchanged; @*/
  {
    i = i + 1;
  }
  return i;
}
