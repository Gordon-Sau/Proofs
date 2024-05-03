open HolKernel boolLib bossLib BasicProvers dep_rewrite;
open pred_setTheory relationTheory combinTheory pairTheory;
open arithmeticTheory prim_recTheory;
open listTheory rich_listTheory sortingTheory;

Definition group_def:
  group [] = [] ∧
  group (x::xs) = let yzs = SPLITP ( λy. x ≠ y) xs in
    ((x,LENGTH (FST yzs) + 1) :: group (SND yzs))
Termination
  WF_REL_TAC `measure LENGTH` >>
  rw[] >>
  qspecl_then [`\y. x ≠ y`,`xs`] assume_tac
    (GEN_ALL SPLITP_LENGTH) >>
  last_x_assum $ assume_tac o GSYM >>
  fs[]
End

(* non-empty group *)
Theorem group_positve:
  ∀l. ∀g. MEM g (group l) ⇒ 0 < SND g
Proof
  ho_match_mp_tac group_ind >> rw[group_def] >>
  rw[group_def]
QED

(* every element in the two nearby group are different *)
Theorem group_different:
  ∀l. ∀n. n + 1 < LENGTH (group l) ⇒
    FST (EL n (group l)) ≠ FST (EL (n + 1) (group l))
Proof
  ho_match_mp_tac group_ind >> rw[group_def] >>
  Cases_on `SPLITP (λy. x ≠ y) xs` >>
  gvs[GSYM ADD1] >>
  reverse $ Cases_on `n` >>
  simp[] >>
  drule SPLITP_IMP >>
  rw[EVERY_MEM,o_DEF] >>
  Cases_on `r` >>
  gvs[group_def]
QED

Theorem FLAT_group:
  ∀l. FLAT (MAP (UNCURRY (flip REPLICATE)) $ group l) = l
Proof
  ho_match_mp_tac group_ind >>
  rw[group_def] >>
  Cases_on `SPLITP (λy. x ≠ y) xs` >>
  gvs[] >>
  drule SPLITP_IMP >>
  rw[o_DEF,EVERY_MEM] >>
  drule SPLITP_JOIN >>
  rw[REPLICATE,GSYM ADD1] >>
  irule LIST_EQ >>
  rw[LENGTH_REPLICATE,EL_REPLICATE] >>
  metis_tac[MEM_EL]
QED

Theorem SORTED_group_gt:
  SORTED $<= l ⇒
  ∀i j. i < j ∧ j < LENGTH (group l) ⇒
  FST (EL i (group l)) < FST (EL j (group l))
Proof
  simp[SORTED_EL_LESS,transitive_LE] >>
  qid_spec_tac `l` >>
  ho_match_mp_tac group_ind >>
  rw[group_def] >>
  Cases_on `SPLITP (λy. x ≠ y) xs` >>
  gvs[] >>
  last_x_assum mp_tac >>
  impl_tac
  >- (
    drule SPLITP_JOIN >>
    rw[] >>
    last_x_assum $ qspecl_then [`LENGTH (x::q) + m`,`LENGTH (x::q) + n`] mp_tac >>
    simp[GSYM ADD_SUC,EL_APPEND_EQN]) >>
  rw[] >>
  Cases_on `j` >>
  Cases_on `i` >>
  gvs[] >>
  pop_assum $ qspecl_then [`0`,`n`] mp_tac >>
    suffices_by (Cases_on `n` >> gvs[]) >>
  pop_assum kall_tac >>
  drule SPLITP_IMP >>
  Cases_on `r` >>
  gvs[group_def] >>
  drule SPLITP_JOIN >>
  rw[] >>
  last_x_assum $ qspecl_then [`0`,`LENGTH $ q ++ [h]`] mp_tac >>
  gvs[] >>
  simp[GSYM ADD1] >>
  PURE_REWRITE_TAC[Once $ GSYM APPEND_ASSOC] >>
  DEP_REWRITE_TAC[EL_LENGTH_APPEND] >>
  simp[]
QED

Theorem FILTER_REPLICATE:
  FILTER (λx. x = q) (REPLICATE n x) =
    if x = q then REPLICATE n x else []
Proof
  Induct_on `n` >> simp[]
QED

Triviality cong2:
  x = x' ∧ y = y' ⇒ f x y = f x' y'
Proof
  simp[]
QED

Theorem SORTED_group_ELEM:
  SORTED $<= l ∧ i < LENGTH (group l) ⇒
    SND (EL i (group l)) =
      LENGTH (FILTER (λx. x = FST (EL i (group l))) l)
Proof
  strip_tac >>
  Cases_on `EL i (group l)` >> simp[] >>
  qspec_then `l` mp_tac (GSYM FLAT_group) >>
  disch_then (fn t => simp[Once t]) >>
  simp[FILTER_FLAT,MAP_MAP_o,LENGTH_FLAT,FILTER_REPLICATE,
    ELIM_UNCURRY,o_DEF,COND_RAND] >>
  `∀j. j < LENGTH (group l) ∧ i ≠ j ⇒ FST (EL j (group l)) ≠ q` by (
    rw[] >>
    Cases_on `i < j`
    >- (drule_then drule SORTED_group_gt >> simp[]) >>
    `j < i` by fs[] >>
    drule_then drule SORTED_group_gt >> simp[]) >>
  `group l = TAKE i (group l) ++ [(q,r)] ++ DROP (i + 1) (group l)` by (
    irule EQ_TRANS >>
    irule_at (Pos hd) (GSYM TAKE_DROP) >>
    PURE_REWRITE_TAC[GSYM APPEND_ASSOC] >>
    irule_at (Pos hd) cong2 >>
    irule_at (Pos hd) EQ_REFL >>
    irule LIST_EQ >>
    rw[EL_DROP] >>
    Cases_on `x` >>
    simp[EL_DROP,ADD1]
  ) >>
  pop_assum (fn t => simp[Once t]) >>
  PURE_REWRITE_TAC[MAP_APPEND,SUM_APPEND] >>
  irule EQ_SYM >>
  simp[SUM_eq_0,MEM_MAP,PULL_EXISTS,MEM_DROP] >>
  simp[MEM_EL,EL_TAKE,PULL_EXISTS]
QED

