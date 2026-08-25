  $ soteria-cn verify lemmas.c
  Verifying function push_with_lemma...
  Successfully verified push_with_lemma
  Verifying function push_with_pure_lemma...
  Successfully verified push_with_pure_lemma
  $ soteria-cn verify lemmas_bad.c
  Verifying function push_no_lemma...
  error: `Lfail ((length(Seq_Cons(V|4|, V|1|)) == (0x00000001 + length(V|4|)))) in push_no_lemma
      --> lemmas_bad.c:38:13
   34 |    
   35 | /  struct sll *push_no_lemma(unsigned int x, struct sll *l)
   36 | |  /*@ requires take L = SLLseq(l);
   37 | |      ensures take L_post = SLLseq(return);
   38 | |              length(L_post) == 1u32 + length(L);
      | |              ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ Could not prove this holds
      . |  
   44 | |    return n;
   45 | |  }
      | \--' 1: Verifying function
   46 |    
  $ soteria-cn verify lemmas_export.c --lemmata obligations.v
  converting pure lemma type: triple_linear
  Verifying function uses_lemma...
  Successfully verified uses_lemma
  $ grep -c "Definition triple_linear_type" obligations.v > /dev/null && echo "obligation generated"
  obligation generated
Resource lemmas and lemmas mentioning recursive functions cannot be exported
(same limitation as upstream CN, which crashes; we fail cleanly):
  $ soteria-cn verify lemmas.c --lemmata unsupported.v -f push_with_lemma
  converting pure lemma type: length_cons_pure
  lemmas.c:22:1: error: rec-def not yet handled:
  length
  function [rec] (u32) length (datatype seq l) {
  ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ 
  lemmas.c:22:1: error: rec-def not yet handled:
  length
  function [rec] (u32) length (datatype seq l) {
  ^~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ 
  converting coerced lemma type: length_cons_fact
  [1]
