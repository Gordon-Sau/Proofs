open bossLib;

Theorem surj_imp_epic:
  (!y. ?x. f x = y) ==>
  (!g h. g o f = h o f ==> g = h)
Proof
  gvs[combinTheory.o_DEF,FUN_EQ_THM] >>
  rw[] >>
  last_x_assum $ qspec_then `x` assume_tac >>
  fs[] >>
  first_x_assum $ qspec_then `x'` assume_tac >>
  gvs[]
QED

Theorem epic_imp_surj:
  (?a b. (a: 'a) <> (b: 'a)) /\
  (!g h. (g: 'b -> 'a) o f = h o f ==> g = h) ==>
  (!y. ?z. f z = y)
Proof
  gvs[combinTheory.o_DEF,FUN_EQ_THM] >>
  rw[] >>
  gvs[PULL_FORALL] >>
  first_x_assum $ qspecl_then [
    `\z. if ?x. f x = z then a else b`,`\z. a`,`y`]
    assume_tac >>
  fs[] >>
  first_x_assum mp_tac >>
  impl_tac
  >- (
    rw[] >>
    first_x_assum mp_tac >>
    simp[] >>
    qexists `x` >>
    simp[]
  ) >>
  rw[]
QED

Theorem epic_imp_surj_bool:
  (!g h. (g: 'b -> bool) o f = h o f ==> g = h) ==>
  (!y. ?z. f z = y)
Proof
  gvs[combinTheory.o_DEF,FUN_EQ_THM] >>
  rw[] >>
  gvs[PULL_FORALL] >>
  first_x_assum $ qspecl_then [
    `\z. ?x. f x = z`,`\z. T`,`y`]
    assume_tac >>
  fs[] >>
  first_x_assum irule >>
  strip_tac >>
  qexists `x` >>
  simp[]
QED

