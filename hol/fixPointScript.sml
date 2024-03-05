open bossLib pred_setTheory optionTheory

Definition lfp_def:
  lfp f <=> (some x. f x = x /\ (!z. f z = z ==> x SUBSET z))
End

Definition gfp_def:
  gfp f <=> (some x. f x = x /\ (!z. f z = z ==> z SUBSET x))
End

Theorem lfp_IMP:
  lfp f = SOME ls ==>
  (f ls = ls /\ !z. f z = z ==> ls SUBSET z)
Proof
  gvs[lfp_def,some_def] >>
  rpt strip_tac
  >- metis_tac[] >>
  gvs[] >>
  SELECT_ELIM_TAC >>
  rpt strip_tac >>
  metis_tac[]
QED

Theorem gfp_IMP:
  gfp f = SOME gs ==>
  (f gs = gs /\ !z. f z = z ==> z SUBSET gs)
Proof
  gvs[gfp_def,some_def] >>
  rpt strip_tac
  >- metis_tac[] >>
  gvs[] >>
  SELECT_ELIM_TAC >>
  rpt strip_tac >>
  metis_tac[]
QED

Theorem gfp_unique:
  gfp f = SOME gs /\
  f gs' = gs' /\
  (!z. f z = z ==> z SUBSET gs') ==>
  gs = gs'
Proof
  gvs[gfp_def,some_def] >>
  rpt strip_tac >>
  gvs[] >>
  SELECT_ELIM_TAC >>
  rpt strip_tac
  >- metis_tac[] >>
  gvs[EXTENSION,SUBSET_DEF] >>
  rw[] >>
  eq_tac >>
  rpt strip_tac >>
  first_x_assum $ irule >>
  metis_tac[]
QED

Theorem IMP_gfp:
  (f gs = gs /\ !z. f z = z ==> z SUBSET gs) ==>
  gfp f = SOME gs
Proof
  Cases_on `gfp f`
  >- gvs[gfp_def,some_def] >>
  simp[gfp_def,some_def] >>
  rpt strip_tac >>
  metis_tac[gfp_unique]
QED

Theorem lfp_unique:
  lfp f = SOME ls /\
  f ls' = ls' /\
  (!z. f z = z ==> ls' SUBSET z) ==>
  ls = ls'
Proof
  gvs[lfp_def,some_def] >>
  rpt strip_tac >>
  gvs[] >>
  SELECT_ELIM_TAC >>
  rpt strip_tac
  >- metis_tac[] >>
  gvs[EXTENSION,SUBSET_DEF] >>
  rw[] >>
  eq_tac >>
  rpt strip_tac >>
  first_x_assum $ irule >>
  metis_tac[]
QED

Theorem IMP_lfp:
  (f ls = ls /\ !z. f z = z ==> ls SUBSET z) ==>
  lfp f = SOME ls
Proof
  Cases_on `lfp f`
  >- gvs[lfp_def,some_def] >>
  simp[lfp_def,some_def] >>
  rpt strip_tac >>
  metis_tac[lfp_unique]
QED

Theorem COMPL_SUBSET:
  (COMPL z) SUBSET (COMPL s) <=> s SUBSET z
Proof
  eq_tac >>
  gvs[SUBSET_DEF] >>
  rpt strip_tac >>
  metis_tac[]
QED

Theorem COMPL_cong:
  COMPL a = COMPL b <=>
  a = b
Proof
  eq_tac >>
  gvs[EXTENSION]
QED

Theorem exists_lfp_IMP_gfp:
  lfp (COMPL o f o COMPL) = SOME ls ==>
  gfp f = SOME (COMPL ls)
Proof
  rpt strip_tac >>
  irule IMP_gfp >>
  drule lfp_IMP >> 
  rpt strip_tac
  >- (irule $ iffLR COMPL_SUBSET >> simp[]) >>
  irule $ iffLR COMPL_cong >> gvs[]
QED

Theorem exists_gfp_IMP_lfp:
  gfp f = SOME gs ==>
  lfp (COMPL o f o COMPL) = SOME (COMPL gs)
Proof
  rpt strip_tac >>
  irule IMP_lfp >>
  drule gfp_IMP >>
  rpt strip_tac
  >- (
    irule $ iffLR COMPL_SUBSET >> simp[] >>
    first_x_assum irule >>
    gvs[] >>
    irule $ iffLR COMPL_cong >>
    simp[]
  ) >>
  simp[]
QED

Theorem COMPL_gfp_lfp:
  gfp f = OPTION_MAP COMPL $ lfp (COMPL o f o COMPL)
Proof
  Cases_on `gfp f` >>
  gvs[]
  >- (
    spose_not_then assume_tac >>
    last_x_assum mp_tac >>
    Cases_on `lfp (COMPL o f o COMPL)` >>
    gvs[] >>
    drule exists_lfp_IMP_gfp >>
    gvs[]
  ) >>
  drule exists_gfp_IMP_lfp >>
  gvs[]
QED

Theorem COMPL_lfp_gfp:
  lfp f = OPTION_MAP COMPL $ gfp (COMPL o f o COMPL)
Proof
  qspec_then `COMPL o f o COMPL` assume_tac $ GEN_ALL COMPL_gfp_lfp >>
  gvs[OPTION_MAP_COMPOSE,combinTheory.o_DEF] >>
  metis_tac[]
QED

Definition monotone_def:
  monotone f <=>
  (!X Y. X SUBSET Y ==> f X SUBSET f Y)
End

Theorem monotone_SUBSET_BIGINTER:
  monotone f /\
  y IN (\x. f x SUBSET x) ==>
  f y IN (\x. f x SUBSET x)
Proof
  gvs[monotone_def]
QED

Theorem IN_SUBSET_BIGINTER:
  X IN P ==>
  BIGINTER P SUBSET X
Proof
  metis_tac[SUBSET_REFL,BIGINTER_SUBSET]
QED

Theorem lfp_BIGINTER:
  monotone f ==>
  lfp f = SOME $ BIGINTER (\x. f x SUBSET x)
Proof
  rpt strip_tac >>
  irule IMP_lfp >>
  rw[]
  >- (
    qspec_then `z` assume_tac SUBSET_REFL >>
    irule BIGINTER_SUBSET >>
    first_x_assum $ irule_at Any >>
    gvs[]) >>
  `f (BIGINTER (λx. f x ⊆ x)) ⊆ BIGINTER (λx. f x ⊆ x)`
  by (
    qspec_then `BIGINTER (\x. f x SUBSET x)` assume_tac SUBSET_REFL >>
    gvs[SUBSET_BIGINTER] >>
    rpt strip_tac >>
    fs[monotone_def] >>
    first_x_assum $ drule_then assume_tac >>
    first_x_assum $ drule_then assume_tac >>
    metis_tac[SUBSET_TRANS]
  ) >>
  irule $ iffRL SET_EQ_SUBSET >>
  rpt strip_tac >>
  simp[] >>
  irule IN_SUBSET_BIGINTER >>
  drule_then irule monotone_SUBSET_BIGINTER >>
  gvs[]
QED

Theorem COMPL_COMPL_monotone:
  monotone f ==>
  monotone (COMPL o f o COMPL)
Proof
  simp[monotone_def] >>
  rpt strip_tac >>
  simp[COMPL_SUBSET]
QED

Theorem COMPL_BIGINTER_BIGUNION:
  COMPL (BIGINTER p) = BIGUNION {COMPL s| s IN p}
Proof
  simp[COMPL_DEF,DIFF_BIGINTER1,
    IMAGE_DEF,combinTheory.o_DEF]
QED

Theorem gfp_BIGUNION:
  monotone f ==>
  gfp f = SOME $ BIGUNION (\x. x SUBSET f x)
Proof
  rpt strip_tac >>
  simp[COMPL_gfp_lfp] >>
  drule COMPL_COMPL_monotone >>
  rpt strip_tac >> 
  drule lfp_BIGINTER >>
  rpt strip_tac >>
  simp[COMPL_BIGINTER_BIGUNION] >>
  AP_TERM_TAC >>
  simp[EXTENSION] >>
  rpt strip_tac >>
  eq_tac >>
  rpt strip_tac
  >- (
    qexists `COMPL x` >>
    gvs[SUBSET_DEF] >>
    metis_tac[] ) >>
  rpt strip_tac >>
  fs[SUBSET_DEF] >>
  rpt strip_tac >>
  `x = COMPL s` by
    gvs[COMPL_DEF,DIFF_DEF,EXTENSION] >>
  gvs[] >>
  metis_tac[]
QED

