open HolKernel boolLib bossLib BasicProvers pairTheory;
open pred_setTheory relationTheory combinTheory;

val _ = new_theory "restrict";

Definition restrict_def:
  restrict d f = λx. if d x then f x else ARB
End

Theorem restrict_thm:
  d x ⇒
  restrict d f x = f x
Proof
  simp[restrict_def]
QED

Theorem restrict_eq_thm:
  (∀x. d x ⇒ f x = g x) ⇔
  restrict d f = restrict d g
Proof
  rw[restrict_def,FUN_EQ_THM,EQ_IMP_THM] >>
  last_x_assum $ qspec_then `x` assume_tac >>
  rfs[]
QED

Theorem restrict_restrict:
  restrict d1 (restrict d2 f) = restrict (d1 ∩ d2) f
Proof
  rw[restrict_def,IN_DEF,FUN_EQ_THM] >>
  IF_CASES_TAC >> fs[]
QED

Theorem restrict_UNIV:
  restrict UNIV f = f
Proof
  rw[restrict_thm,FUN_EQ_THM]
QED

Theorem restrict_IDEM:
  restrict d (restrict d f) = restrict d f
Proof
  simp[restrict_restrict]
QED

Theorem restrict_exists_unique:
  ∃!f. f = restrict d f ∧ f = restrict d g
Proof
  simp[EXISTS_UNIQUE_THM,restrict_IDEM]
QED

Definition restricted_def:
  restricted d f ⇔ (restrict d f = f)
End

Theorem restricted_unique:
  ∀d f g. restricted d f ∧ restricted d g ∧
  (∀x. d x ⇒ f x = g x) ⇒
  f = g
Proof
  rw[restricted_def,FUN_EQ_THM] >>
  fs[restrict_def]
QED

Theorem restricted_eq_thm:
  ∀d f g. restricted d f ∧ restricted d g ⇒
  ((f = g) ⇔ (∀x. d x ⇒ f x = g x))
Proof
  rw[EQ_IMP_THM] >>
  metis_tac[restricted_unique]
QED

Theorem restricted_restrict_thm:
  restricted d (restrict d f)
Proof
  simp[restricted_def,restrict_restrict]
QED

val _ = export_theory ();
