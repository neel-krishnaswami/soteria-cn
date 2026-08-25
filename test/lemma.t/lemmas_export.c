/*@
function (u32) triple (u32 x) {
  3u32 * x
}

lemma triple_linear (u32 a, u32 b)
  requires
      true;
  ensures
      triple(a + b) == triple(a) + triple(b);
@*/

void uses_lemma(unsigned int a, unsigned int b)
/*@ requires a < 1000u32; b < 1000u32;
    ensures triple(a + b) == triple(a) + triple(b);
@*/
{
  /*@ apply triple_linear(a, b); @*/
}
