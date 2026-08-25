// A counter loop: the invariant pins the counter's range and the bound,
// letting the postcondition follow from the negated guard.
int count_up(int n)
/*@ requires 0i32 <= n; n < 1000i32;
    ensures return == n; @*/
{
  int i = 0;
  while (i < n)
  /*@ inv 0i32 <= i; i <= n; n < 1000i32; {n} unchanged; @*/
  {
    i = i + 1;
  }
  return i;
}
