open HolKernel boolLib bossLib BasicProvers;
open pred_setTheory relationTheory combinTheory;

val _ = new_theory "myPair";

Triviality myPair_inhabited:
  ?f. ( \ f. ?a b. f = ( \x y. x = a /\ y = b)) f
Proof
  simp[]
QED

val myPair_tydef = new_type_definition ("myPair", myPair_inhabited);

val repabs_fns = define_new_type_bijections {
  name = "myPair_absrep",
  ABS = "myPair_abs",
  REP = "myPair_rep",
  tyax = myPair_tydef};

val myPair_absrep = CONJUNCT1 repabs_fns
val myPair_repabs = CONJUNCT2 repabs_fns

Triviality myPair_rep_11:
  (myPair_rep t1 = myPair_rep t2) = (t1 = t2)
Proof
  SRW_TAC [][EQ_IMP_THM] THEN
  POP_ASSUM (MP_TAC o AP_TERM ``myPair_abs``) THEN SRW_TAC [][myPair_absrep]
QED

Triviality myPair_abs_11:
  f1 = (λx y. x = a1 ∧ y = b1) ∧
  f2 = (λx y. x = a2 ∧ y = b2) ⇒
  (myPair_abs f1 = myPair_abs f2 ⇔ f1 = f2)
Proof
  simp[] >>
  disch_then kall_tac >>
  rw[EQ_IMP_THM] >>
  ONCE_REWRITE_TAC[GSYM $ SRULE[PULL_EXISTS] $ iffLR myPair_repabs] >>
  simp[]
QED

val myPair_abs_11' =
  SRULE[PULL_EXISTS] $ iffLR myPair_repabs;

Triviality myPair_rep_thm:
  ∃a b. myPair_rep t = (λx y. x = a ∧ y = b)
Proof
  irule $ iffLR $ SRULE[] $ GSYM myPair_repabs >>
  simp[myPair_absrep]
QED

Definition fst_def:
  fst p = @a. ∃b. myPair_rep p a b
End

Definition snd_def:
  snd p = @b. ∃a. myPair_rep p a b
End

Definition cons_def:
  cons a b = myPair_abs (λx y. x = a ∧ y = b)
End

Theorem Pair_nchotomy:
  ∀p. ∃a b. p = cons a b
Proof
  gen_tac >>
  irule_at (Pos hd) $ iffLR myPair_rep_11 >>
  assume_tac $ Q.SPEC`p` $ GEN_ALL myPair_rep_thm >>
  fs[cons_def,myPair_abs_11'] >>
  metis_tac[]
QED

Theorem fst_cons:
  fst (cons x y) = x
Proof
  simp[cons_def,fst_def,myPair_abs_11']
QED

Theorem snd_cons:
  snd (cons x y) = y
Proof
  simp[cons_def,snd_def,myPair_abs_11']
QED

Theorem Pair_CASE:
  ∀P. (∀a b. P (cons a b)) ⇒ ∀p. P p
Proof
  metis_tac[Pair_nchotomy]
QED

Definition bimap_def:
  bimap f g p = cons (f $ fst p) (g $ snd p)
End

Theorem fst_bimap:
  fst (bimap f g p) = f (fst p)
Proof
  simp[bimap_def,fst_cons]
QED

Theorem snd_bimap:
  snd (bimap f g p) = g (snd p)
Proof
  simp[bimap_def,snd_cons]
QED

Theorem bimap_cons:
  bimap f g (cons a b) = cons (f a) (g b)
Proof
  simp[bimap_def,fst_cons,snd_cons]
QED

Theorem cons_cong_thm:
  cons l1 r1 = cons l2 r2 ⇔ l1 = l2 ∧ r1 = r2
Proof
  rw[EQ_IMP_THM]
  >- (
    pop_assum $ assume_tac o Q.AP_TERM `fst` >>
    fs[fst_cons]) >>
  pop_assum $ assume_tac o Q.AP_TERM `snd` >>
  fs[snd_cons]
QED

val _ = export_theory ();
