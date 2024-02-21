open HolKernel boolLib bossLib BasicProvers;
open pred_setTheory relationTheory combinTheory;

open myPairTheory;

val _ = new_theory "mySum";

(*
* Church encoding could not work as we introduce a new
* type variable c
  a + b = (a -> c) -> (b -> c) -> c
  Inl = λx. λf g. f x
  InR = λy. λf g. g y
*)


(*
* bool * (a option * b option)
*)

Triviality mySum_inhabited:
  ∃s. (λs.
  (∃a. s = cons T (cons a ARB)) ∨
  (∃b. s = cons F (cons ARB b))) s
Proof
  simp[PULL_EXISTS,LEFT_OR_EXISTS_THM,RIGHT_OR_EXISTS_THM] >>
  metis_tac[]
QED

val mySum_tydef = new_type_definition ("mySum", mySum_inhabited);

val repabs_fns = define_new_type_bijections {
  name = "mySum_absrep",
  ABS = "mySum_abs",
  REP = "mySum_rep",
  tyax = mySum_tydef};

val mySum_absrep = CONJUNCT1 repabs_fns
val mySum_repabs = CONJUNCT2 repabs_fns

Triviality mySum_rep_11:
  (mySum_rep t1 = mySum_rep t2) = (t1 = t2)
Proof
  SRW_TAC [][EQ_IMP_THM] THEN
  POP_ASSUM (MP_TAC o AP_TERM ``mySum_abs``) THEN SRW_TAC [][mySum_absrep]
QED

Triviality mySum_rep_abs':
  (mySum_rep (mySum_abs (cons T (cons l ARB)))) =
    cons T (cons l ARB) ∧
  (mySum_rep (mySum_abs (cons F (cons ARB r)))) =
    cons F (cons ARB r)
Proof
  rw[] >>
  irule $ iffLR mySum_repabs >>
  metis_tac[]
QED

Triviality mySum_rep_thm:
  (∃l. mySum_rep s = cons T (cons l ARB)) ∨
  (∃r. mySum_rep s = cons F (cons ARB r))
Proof
  qspec_then `mySum_rep s` assume_tac $
    SRULE[] $ iffRL mySum_repabs >>
  fs[mySum_absrep] >>
  metis_tac[]
QED

Definition INL_def:
  INL l = mySum_abs $ cons T (cons l ARB)
End

Definition INR_def:
  INR r = mySum_abs $ cons F (cons ARB r)
End

Definition either_def:
  either f g e =
    if fst (mySum_rep e)
    then f $ fst (snd $ mySum_rep e)
    else g $ snd (snd $ mySum_rep e)
End

Theorem mySum_nchotomy:
  ∀s. (∃l. s = INL l) ∨ (∃r. s = INR r)
Proof
  rw[INL_def,INR_def] >>
  `(∃l. mySum_rep s = mySum_rep (mySum_abs (cons T (cons l ARB)))) ∨
  ∃r. mySum_rep s = mySum_rep (mySum_abs (cons F (cons ARB r)))` by
  simp[mySum_rep_abs',mySum_rep_thm] >>
  fs[mySum_rep_11] >>
  metis_tac[]
QED

Theorem mySum_distinct:
  ∀l r. INL l ≠ INR r
Proof
  simp[INL_def,INR_def] >>
  rpt strip_tac >>
  pop_assum $ assume_tac o Q.AP_TERM `mySum_rep` >>
  fs[mySum_rep_abs',cons_cong_thm]
QED

Theorem either_INL:
  either f g (INL l) = f l
Proof
  simp[either_def,INL_def] >>
  simp[mySum_rep_abs',fst_cons,snd_cons]
QED

Theorem either_INR:
  either f g (INR r) = g r
Proof
  simp[either_def,INR_def] >>
  simp[mySum_rep_abs',fst_cons,snd_cons]
QED

Theorem INL_eq:
  INL l1 = INL l2 ⇒ l1 = l2
Proof
  rw[INL_def] >>
  pop_assum $ assume_tac o Q.AP_TERM `mySum_rep` >>
  fs[mySum_rep_abs',cons_cong_thm]
QED

Theorem INR_eq:
  INR l1 = INR l2 ⇒ l1 = l2
Proof
  rw[INR_def] >>
  pop_assum $ assume_tac o Q.AP_TERM `mySum_rep` >>
  fs[mySum_rep_abs',cons_cong_thm]
QED

val _ = export_theory();
