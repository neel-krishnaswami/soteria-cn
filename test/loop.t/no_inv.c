// A loop with no user invariant: CN still builds one (ownership of locals),
// which is enough when the postcondition does not depend on loop state.
int zero(void)
/*@ ensures return == 0i32; @*/
{
  int i = 5;
  while (i > 0) { i = i - 1; }
  return 0;
}

// Here the postcondition depends on the loop's result, so the auto-generated
// invariant is too weak.
int needs_inv(void)
/*@ ensures return == 0i32; @*/
{
  int i = 5;
  while (i > 0) { i = i - 1; }
  return i;
}
