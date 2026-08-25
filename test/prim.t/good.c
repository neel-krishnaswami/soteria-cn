// good<ct> is CN's value-check, reused directly (so semantics match CN
// exactly — e.g. CN's range for _Bool is its storage byte, making both
// asserts below provable).
int good_ok(int x)
/*@ ensures return == x; @*/
{
  /*@ assert (good<int>(x)); @*/
  return x;
}

int good_bool(int x)
/*@ ensures return == x; @*/
{
  /*@ assert (good<_Bool>(2u8)); @*/
  return x;
}
