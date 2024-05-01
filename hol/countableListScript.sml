open HolKernel boolLib bossLib BasicProvers dep_rewrite;
open pred_setTheory relationTheory listTheory pairTheory;
open arithmeticTheory rich_listTheory;

val _ = new_theory "countableList";

Theorem UNIV_list_BIGUNION:
  (UNIV:'a list set) = BIGUNION (IMAGE (λk. {l | LENGTH l = k}) UNIV)
Proof
  rw[EXTENSION,EQ_IMP_THM] >>
  qexists `{l | LENGTH l = LENGTH x}` >>
  simp[] >>
  metis_tac[]
QED

Theorem set_SUC_LENGTH:
  {l | LENGTH l = SUC k} = IMAGE (UNCURRY CONS) (UNIV × {l | LENGTH l = k})
Proof
  rw[EXTENSION] >>
  Cases_on `x` >>
  gvs[ELIM_UNCURRY] >>
  rw[EQ_IMP_THM,LAMBDA_PROD,GSYM PEXISTS_THM]
QED

Theorem countable_list:
  countable (UNIV:'a set) ⇒
  countable (UNIV:'a list set)
Proof
  rw[UNIV_list_BIGUNION] >>
  irule bigunion_countable >>
  rw[IN_DEF]
  Induct_on `k` >>
  simp[set_SUC_LENGTH] >>
  metis_tac[cross_countable,image_countable]
QED

val _ = export_theory();
