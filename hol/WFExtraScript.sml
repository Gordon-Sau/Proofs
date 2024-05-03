open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open pred_setTheory pairTheory relationTheory prim_recTheory;
open numTheory combinTheory arithmeticTheory;
open markerLib;
open llistTheory;
open whileTheory;

Theorem WF_ext:
  WF R /\ WF R'' ∧
  (!x y. R' x y ==> (R'' LEX R) (m x,f x) (m y,f y)) ⇒
  WF R'
Proof
  rpt strip_tac >>
  irule WF_SUBSET >>
  qexists `inv_image (R'' LEX R) (\y. (m y,f y))` >>
  simp[] >>
  irule WF_inv_image >>
  metis_tac[WF_LEX]
QED

Theorem WF_measure_ext:
  WF R /\
  (!x y. R' x y ==> (R x y /\ m x <= (m y):num) \/ m x < (m y):num) ==>
  WF R'
Proof
  rpt strip_tac >>
  drule_then irule $ INST_TYPE [``:'b`` |-> ``:num``] WF_ext >>
  qexistsl [`$<`,`I`,`m`] >>
  conj_tac >>
  rw[inv_image_def,LEX_DEF_THM] >>
  reverse $ first_x_assum $ drule_then strip_assume_tac
  >- rw[] >>
  Cases_on `m x = m y` >>
  rw[]
QED

Theorem WF_TC_SUBSET:
  WF R ∧
  (∀x y. R' x y ⇒ TC R x y) ⇒
  WF R'
Proof
  rw[] >>
  drule_at_then (Pos $ el 2) irule WF_SUBSET >>
  simp[WF_TC]
QED

CoInductive closed_LINFINITE:
  closed_LINFINITE R (h:::t) ∧ R h h' ⇒ closed_LINFINITE R (h':::h:::t)
End

Theorem WF_LFINITE_llist:
  (¬WF R) ⇔ ∃l. closed_LINFINITE R l
Proof
  rw[EQ_IMP_THM,WF_IFF_WELLFOUNDED,wellfounded_def]
  >- (
    qexists `LUNFOLD (\x. SOME (SUC x,f x)) 0` >>
    irule closed_LINFINITE_coind >>
    qexists `\l. ∃n. l = LUNFOLD (\x. SOME (SUC x,f x)) n` >>
    rw[] >- metis_tac[] >>
    ntac 2 $ simp[Once LUNFOLD] >>
    qexists `SUC n` >>
    irule EQ_SYM >>
    simp[Once LUNFOLD]
  ) >>
  qexists `\n. THE (LNTH n l)` >>
  pop_assum mp_tac >>
  simp[PULL_FORALL] >>
  qid_spec_tac `l` >>
  Induct_on `n`
  >- (
    PURE_REWRITE_TAC[LNTH] >>
    rw[Once closed_LINFINITE_cases] >>
    simp[]
  ) >>
  rw[LNTH] >>
  fs[Once closed_LINFINITE_cases] >>
  last_x_assum $ qspec_then `h:::t` mp_tac >>
  qpat_x_assum `closed_LINFINITE _ _` $ strip_assume_tac o
    SRULE[Once closed_LINFINITE_cases] >>
  simp[]
QED

Definition gen_inf_desc_chain_def:
  (gen_inf_desc_chain r f 0 = 0) ∧
  gen_inf_desc_chain r f (SUC n) =
    let gn = gen_inf_desc_chain r f n in
      $LEAST (\m. gn < m ∧ r (f m) (f gn))
End

Theorem WF_decompose:
  WF R ∧
  (∀f. (∀n. R' (f (SUC n)) (f n)) ⇒  ∃n. 0 < n ∧ R (f n) (f 0)) ⇒
  WF R'
Proof
  rw[WF_IFF_WELLFOUNDED,wellfounded_def,PULL_EXISTS] >>
  spose_not_then strip_assume_tac >>
  last_x_assum mp_tac >>
  simp[] >>
  qexists `f o gen_inf_desc_chain R f` >>
  rw[Once gen_inf_desc_chain_def] >>
  qpat_abbrev_tac `gsn = gen_inf_desc_chain _ _ n` >>
  `(\x. R (f x) (f gsn)) ($LEAST (\m. gsn < m ∧ R (f m) (f gsn)))`
      suffices_by simp[] >>
  irule LEAST_ELIM >>
  rw[] >>
  last_x_assum $ qspecl_then [`\n. f (n + gsn)`] mp_tac >>
  rw[] >>
  pop_assum mp_tac >>
  impl_tac
  >- (
    rw[] >>
    last_x_assum $ qspec_then `gsn + n'` mp_tac >>
    simp[arithmeticTheory.ADD1]
  ) >>
  rw[] >>
  first_x_assum $ irule_at (Pos last) >>
  DECIDE_TAC
QED

Definition the_measure_def:
  the_measure R x =
  if WF R ∧ FINITE {y | R y x}
  then
    MAX_SET (IMAGE (the_measure R) {y | R y x}) + 1
  else 0
Termination
  qexists `\y x. FST y = FST x ∧ WF (FST x) ∧ (FST x) (SND y) (SND x)` >>
  simp[] >>
  qspecl_then [`WF`,`FST`,`I`,`SND`] irule WF_PULL >>
  rw[]
End

Theorem the_measure_positive:
  WF R ∧ (∀x. FINITE {y | R y x}) ⇒ ∀x. 0 < the_measure R x
Proof
  strip_tac >>
  `!R' x. R' = R ==> 0 < the_measure R x` suffices_by rw[] >>
  ho_match_mp_tac the_measure_ind >>
  rw[] >>
  gvs[] >>
  simp[Once the_measure_def]
QED

Theorem the_measure_LT:
  WF R ∧ FINITE {y | R y x} ==> R y x ⇒ the_measure R y < the_measure R x
Proof
  rw[] >>
  PURE_REWRITE_TAC[GSYM arithmeticTheory.GREATER_DEF] >>
  simp[Once the_measure_def] >>
  simp[arithmeticTheory.GREATER_DEF,GSYM LE_LT1] >>
  irule in_max_set >>
  simp[]
QED

Theorem FINITE_UB_EXISTS:
  FINITE s ⇒ ∃n. ∀x. x ∈ s ⇒ x ≤ n
Proof
  rw[] >>
  qexists `MAX_SET s` >>
  rw[] >>
  irule in_max_set >>
  simp[]
QED

Theorem MAX_SET_LEAST_UB:
  FINITE s ⇒
    MAX_SET s = LEAST n. (∀x. x ∈ s ⇒ x ≤ n)
Proof
  rw[] >>
  irule LEAST_ELIM >>
  reverse $ rw[]
  >- metis_tac[FINITE_UB_EXISTS] >>
  irule LESS_EQUAL_ANTISYM >>
  conj_tac
  >- (
    Cases_on `n` >> simp[] >>
    irule in_max_set >>
    simp[] >>
    last_x_assum $ qspec_then `n'` mp_tac >>
    rw[] >>
    `SUC n' ≤ x` by DECIDE_TAC >>
    last_x_assum drule >>
    metis_tac[LESS_EQUAL_ANTISYM]
  ) >>
  drule MAX_SET_DEF >>
  Cases_on `s = EMPTY` >>
  rw[]
QED

(*
* implement the_measure with LEAST instead of MAX_SET
Definition the_other_measure_def:
  the_other_measure R x =
  if WF R
  then if ∃n. (∀y. R y x ⇒ the_other_measure R y < n) then
    LEAST n. ∀y. R y x ⇒ the_other_measure R y < n
    else 0
  else 0
Termination
  qexists `\y x. FST y = FST x ∧ WF (FST x) ∧ (FST x) (SND y) (SND x)` >>
  simp[] >>
  qspecl_then [`WF`,`FST`,`I`,`SND`] irule WF_PULL >>
  rw[]
End

Theorem the_other_measure_LT:
  WF R ∧ ARB ==>
    R y x ⇒ the_other_measure R y < the_other_measure R x
Proof
  cheat
QED
*)

