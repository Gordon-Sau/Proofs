open BasicProvers dep_rewrite bossLib arithmeticTheory numLib;
open optionTheory whileTheory relationTheory listTheory llistTheory rich_listTheory;

Definition bisimulation_def:
  bisimulation step R ⇔ (∀P Q. R P Q ⇒
    (!a P'. step a P P' ⇒ ?Q'. step a Q Q' ∧ R P' Q') ∧
    (!a Q'. step a Q Q' ⇒ ∃P'. step a P P' ∧ R P' Q'))
End

Definition bisimilar_def:
  bisimilar step P Q ⇔ ?R. bisimulation step R ∧ R P Q
End

Definition compose_r_def:
  compose_r R R' <=> \x z. ?y. R x y ∧ R' y z
End

Theorem compose_r_assoc:
  compose_r (compose_r R R') R'' = compose_r R (compose_r R' R'')
Proof
  simp[compose_r_def] >>
  metis_tac[]
QED

Theorem union_bisimulation:
  bisimulation step R ∧ bisimulation step R' ⇒
  bisimulation step (\x y. R x y \/ R' x y)
Proof
  rw[bisimulation_def] >>
  metis_tac[]
QED

Theorem bisimilar_bisimulation:
  bisimulation step (\P Q. bisimilar step P Q)
Proof
  rw[bisimulation_def,bisimilar_def] >>
  metis_tac[]
QED

Theorem bisimilar_refl:
  bisimilar step P P
Proof
  rw[bisimilar_def,bisimulation_def] >>
  qexists `\x y. x = y` >>
  gvs[]
QED

Theorem bisimilar_sym:
  bisimilar step P Q ⇒ bisimilar step Q P
Proof
  rw[] >>
  fs[bisimilar_def] >>
  qexists `\x y. R y x` >>
  gvs[bisimulation_def] >>
  rw[] >>
  metis_tac[]
QED

Theorem bisimilar_trans:
  bisimilar step P Q ∧ bisimilar step Q R ⇒ bisimilar step P R
Proof
  rw[] >>
  fs[bisimilar_def] >>
  qexists `\x y. ?z. R' x z ∧ R'' z y` >>
  gvs[bisimulation_def] >>
  rw[] >>
  metis_tac[]
QED

Inductive steps:
[~Nil]
  (∀ P. steps step [] P P)
[~Cons]
  (∀ P P' Q h t. step h P P' ∧ steps step t P' Q ⇒
  steps step (h::t) P Q)
End

Theorem steps_preserve_lemma:
  (!a P P' Q. R P Q ∧ step a P P' ⇒
    ∃ Q'. step' a Q Q' ∧ R P' Q') ⇒
  !s P P'. steps step s P P' ⇒
  !Q. R P Q ==> ∃Q'. steps step' s Q Q' ∧ R P' Q'
Proof
  strip_tac >>
  ho_match_mp_tac steps_ind >>
  rw[]
  >- (
    qexists `Q` >>
    simp[steps_rules]) >>
  last_x_assum $ drule_all_then strip_assume_tac >>
  irule_at (Pos hd) $ cj 2 steps_rules >>
  metis_tac[]
QED

Theorem steps_preserve = SRULE[PULL_FORALL,AND_IMP_INTRO]
steps_preserve_lemma

Theorem steps_single:
  steps step [x] P Q = step x P Q
Proof
  iff_tac
  >- (
    rw[] >>
    pop_assum $ strip_assume_tac o SRULE[Once steps_cases] >>
    pop_assum $ strip_assume_tac o SRULE[Once steps_cases] >>
    gvs[]
  ) >>
  rw[] >>
  irule $ cj 2 steps_rules >>
  first_assum $ irule_at (Pos hd) >>
  simp[steps_rules]
QED

Theorem steps_preserve_flip =
  SRULE[] o Q.SPECL [`step`,`step'`,`\x y. R y x`] $
  GEN_ALL steps_preserve

Theorem bisimulation_steps:
  bisimulation step R ⇔ ( ∀ P Q. R P Q ⇒
  ( ∀ P' s. steps step s P P' ⇒ ∃ Q'. steps step s Q Q' ∧ R P' Q') ∧
  ( ∀ Q' s. steps step s Q Q' ⇒ ∃ P'. steps step s P P' ∧ R P' Q'))
Proof
  iff_tac
  >- (
    simp[bisimulation_def] >>
    strip_tac >>
    pop_assum $ strip_assume_tac o SRULE[IMP_CONJ_THM] >>
    pop_assum $ strip_assume_tac o SRULE[FORALL_AND_THM] >>
    rpt gen_tac >>
    strip_tac >>
    rw[] >>
    metis_tac[steps_preserve,steps_preserve_flip]
  ) >>
  rw[bisimulation_def] >>
  metis_tac[steps_single]
QED

Definition simulation_def:
  simulation step R ⇔ (∀P Q a P'.
    R P Q /\ step a P P' ⇒ ∃ Q'. step a Q Q' ∧ R P' Q')
End

Definition similarity_def:
  similarity step P Q ⇔ ?R. simulation step R ∧ R P Q
End

Definition simulation_equiv_def:
  simulation_equiv step P Q ⇔ similarity step P Q ∧ similarity step Q P
End

Theorem bisimulation_simulation_thm:
  bisimulation step R ⇔
    simulation step R ∧
    simulation step (\x y. R y x)
Proof
  simp[bisimulation_def,simulation_def] >>
  iff_tac >>
  rw[] >>
  metis_tac[]
QED

Theorem no_trans_similar:
  (∀ a P'. step a P P' ⇒ F) ⇒ similarity step P Q
Proof
  rw[similarity_def] >>
  qexists `\x y. x = P` >>
  rw[simulation_def] >>
  metis_tac[]
QED

Theorem similarity_refl:
  similarity step P P
Proof
  rw[similarity_def,simulation_def] >>
  qexists `\x y. x = y` >>
  gvs[]
QED

Theorem similarity_trans:
  similarity step P Q ∧ similarity step Q R ⇒
  similarity step P R
Proof
  rw[similarity_def,simulation_def] >>
  qexists `\x y. ?z. R' x z ∧ R'' z y` >>
  gvs[] >>
  rw[] >>
  metis_tac[]
QED

Theorem bisimilar_IMP_simulatoin_equiv:
  bisimilar step P Q ==> simulation_equiv step P Q
Proof
  rw[bisimilar_def,simulation_equiv_def,similarity_def]
  >- metis_tac[bisimulation_simulation_thm] >>
  drule $ iffLR bisimulation_simulation_thm >>
  rw[] >>
  first_assum $ irule_at (Pos hd) >>
  simp[]
QED

Definition traces_def:
  traces step P s ⇔ ∃P'. steps step s P P'
End

Definition trace_equiv_def:
  trace_equiv step P Q ⇔ traces step P = traces step Q
End

Theorem simulation_IMP_traces_inclusion:
  (∀P Q a P'. R P Q ∧ step a P P' ⇒
    ∃Q'. step a Q Q' ∧ R P' Q') ⇒
  ∀a P P'. steps step a P P' ⇒ ∀ Q. R P Q ⇒ ∃Q'. steps step a Q Q'
Proof
  strip_tac >>
  ho_match_mp_tac steps_ind >>
  rw[]
  >- metis_tac[steps_Nil]
  >- metis_tac[steps_Cons]
QED

Theorem simulation_equiv_IMP_trace_equiv:
  simulation_equiv step P Q ⇒ trace_equiv step P Q
Proof
  rw[simulation_equiv_def] >>
  fs[similarity_def,simulation_def] >>
  simp[trace_equiv_def,pred_setTheory.EXTENSION,IN_DEF] >>
  rw[traces_def] >>
  iff_tac >>
  simp[PULL_EXISTS] >>
  rw[] >>
  irule $ SRULE[PULL_FORALL, AND_IMP_INTRO]
    simulation_IMP_traces_inclusion >>
  metis_tac[]
QED

Definition brb_def:
  brb step R = compose_r (bisimilar step)
    (compose_r R (bisimilar step))
End

Theorem brb_simp = SRULE[compose_r_def] brb_def

Definition bisimulation_up_to_def:
  bisimulation_up_to f step R ⇔
  ((∀P Q a P'. R P Q ∧ step a P P' ⇒ ?Q'. step a Q Q' ∧
    f R P' Q') ∧
  (∀P Q a Q'. R P Q ∧ step a Q Q' ⇒ ?P'. step a P P' ∧
    f R P' Q'))
End

Theorem bisimulation_up_to_brb_IMP_bisimulation:
  bisimulation_up_to (brb step) step R ==>
  bisimulation step (brb step R)
Proof
  rw[bisimulation_up_to_def] >>
  simp[Once $ bisimulation_def] >>
  ntac 3 strip_tac >>
  fs[brb_simp] >>
  drule $
    SRULE[bisimulation_def] bisimilar_bisimulation >>
  rev_drule $
    SRULE[bisimulation_def] bisimilar_bisimulation >>
  rw[] >>
  first_assum drule >>
  strip_tac >>
  last_x_assum $ drule_all_then strip_assume_tac >>
  last_x_assum $ drule_all_then strip_assume_tac >>
  imp_res_tac bisimilar_trans >>
  metis_tac[]
QED

Inductive equiv_closure:
[~base]
  (!x y. R x y ⇒ equiv_closure R x y)
[~refl]
  (!x. equiv_closure R x x)
[~sym]
  (!x y. equiv_closure R x y ⇒ equiv_closure R y x)
[~trans]
  (!x y z. equiv_closure R x y ∧ equiv_closure R y z ⇒
    equiv_closure R x z)
End

Theorem bisimulation_up_to_equiv_closure_IMP_bisimulation':
  bisimulation_up_to equiv_closure step R ⇒
  bisimulation step (equiv_closure R)
Proof
  simp[bisimulation_up_to_def] >>
  strip_tac >>
  simp[Once bisimulation_def] >>
  ho_match_mp_tac equiv_closure_ind >>
  rw[]
  >- metis_tac[equiv_closure_base]
  >- metis_tac[equiv_closure_base]
  >- metis_tac[equiv_closure_refl]
  >- metis_tac[equiv_closure_refl]
  >- metis_tac[equiv_closure_sym]
  >- metis_tac[equiv_closure_sym]
  >- metis_tac[equiv_closure_trans]
  >- metis_tac[equiv_closure_trans]
QED

