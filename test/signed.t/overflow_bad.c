// Signed overflow is UB: x + 1 is not provably in range for int.
int inc(int x)
/*@ ensures true; @*/
{
  return x + 1;
}
