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

Theorem TC_RTC_IMP_TC:
  TC R x y ∧ RTC R y z ⇒ TC R x z
Proof
  rpt strip_tac >>
  gvs[RTC_CASES_TC] >>
  irule $ cj 2 TC_RULES >>
  metis_tac[]
QED

Definition gen_inf_desc_chain_def:
  (gen_inf_desc_chain r f 0 = 0) ∧ 
  gen_inf_desc_chain r f (SUC n) =
    let gn = gen_inf_desc_chain r f n in
      $LEAST (\m. gn < m ∧ r (f m) (f gn))
End

Theorem WF_TC_decompose:
  WF (R:'a -> 'a -> bool) ∧
  (∀n. TC R x y  ==>
  WF (R':'a -> 'a -> bool)
Proof
  rw[WF_IFF_WELLFOUNDED,wellfounded_def] >>
  spose_not_then strip_assume_tac >>
  last_x_assum mp_tac >>
  simp[] >>
  qexists `f o gen_inf_desc_chain R f` >>
  Induct_on `n` >>
  >- (
    rw[gen_inf_desc_chain_def] >>
    `(\x. R (f x) (f 0)) ($LEAST (\m. 0 < m ∧ R (f m) (f 0)))`
      suffices_by simp[] >>
    irule LEAST_ELIM >>
    rw[] >>
    cheat
  ) >>
  simp[Once gen_inf_desc_chain_def] >>
  fs[] >>
  qpat_abbrev_tac `gsn = gen_inf_desc_chain _ _ (SUC n)` >>
  `(\x. R (f x) (f gsn)) ($LEAST (\m. gsn < m ∧ R (f m) (f gsn)))`
      suffices_by simp[] >>
  irule LEAST_ELIM >>
  rw[] >>
QED
