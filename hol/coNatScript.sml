open bossLib arithmeticTheory optionTheory whileTheory numLib BasicProvers dep_rewrite
open llistTheory;

Theorem type_inhabited[local]:
  ?f:num. (\x.T) f
Proof Q.EXISTS_TAC `0` >> simp[]
QED

val coNat_tydef = new_type_definition ("coNat", type_inhabited);

val repabs_fns = define_new_type_bijections {
  name = "coNat_absrep",
  ABS = "coNat_abs",
  REP = "coNat_rep",
  tyax = coNat_tydef};

val coNat_absrep = CONJUNCT1 repabs_fns
val coNat_repabs = CONJUNCT2 repabs_fns

Theorem coNat_abs_11[local]:
  (coNat_abs r1 = coNat_abs r2) = (r1 = r2)
Proof
  `(\x. T) r1` by EVAL_TAC >>
  `(\x. T) r2` by EVAL_TAC >>
  gvs[coNat_repabs, EQ_IMP_THM] >>
  metis_tac[]
QED

Theorem coNat_rep_11[local]:
  (coNat_rep t1 = coNat_rep t2) = (t1 = t2)
Proof
  SRW_TAC [][EQ_IMP_THM] THEN
  POP_ASSUM (MP_TAC o AP_TERM ``coNat_abs``) THEN SRW_TAC [][coNat_absrep]
QED

val coNat_repabs' = SIMP_RULE(srw_ss())[] $ #1 (EQ_IMP_RULE (SPEC_ALL coNat_repabs))

Theorem coNat_if_rep_abs[local]: (f = coNat_rep a) ==> (a = coNat_abs f)
Proof DISCH_TAC THEN ASM_REWRITE_TAC [repabs_fns]
QED

val coZero = new_definition("coZero", ``coZero = coNat_abs 1``);
val coSuc = new_definition(
  "coSuc",
  ``coSuc n = if coNat_rep n = 0 then coNat_abs 0 else coNat_abs (SUC $ coNat_rep n)``
);

val coPrev = new_definition("coPrev", ``coPrev x =
  case coNat_rep x of
  | 0 => SOME x
  | SUC 0 => NONE
  | SUC n => SOME $ coNat_abs n``);

Theorem coPrev_coZero:
  coPrev coZero = NONE
Proof
  gvs[coPrev,coZero,coNat_repabs']
QED

Theorem coPrev_coSuc:
  coPrev (coSuc x) = SOME x
Proof
  gvs[coPrev,coSuc] >>
  Cases_on `coNat_rep x` >>
  gvs[coNat_repabs',GSYM coNat_abs_11,coNat_absrep]
QED

Theorem forall_coNat[local]:
  (!x. P x) = (!y. P (coNat_abs y))
Proof
  rpt strip_tac >>
  eq_tac >>
  rpt strip_tac
  >- metis_tac[] >>
  PURE_REWRITE_TAC[Once $ GSYM coNat_absrep] >>
  simp[]
QED

Theorem coNat_CASES:
  !x. (x = coZero) \/ (?n. x = coSuc n)
Proof
  simp[forall_coNat] >>
  gvs[coZero,coSuc] >>
  rpt strip_tac >>
  simp[coNat_abs_11] >>
  Cases_on `y` >>
  gvs[AllCaseEqs()] >>
  metis_tac[coNat_repabs']
QED

fun coNat_CASE_TAC tm = STRUCT_CASES_TAC (ISPEC tm coNat_CASES) ;

Theorem coSuc_NOT_coZero[simp]:
  !n. ~(coSuc n = coZero) /\ ~(coZero = coSuc n)
Proof
  gvs[coSuc,coZero] >>
  rw[coNat_abs_11]
QED

Theorem coNat_rep_to_coNat_abs[local]:
  !n x. coNat_rep n = x <=> n = coNat_abs x
Proof
  rpt strip_tac >> 
  eq_tac >>
  metis_tac[coNat_repabs',coNat_rep_11]
QED

Theorem coSuc_11[simp]:
  !n m. (coSuc n = coSuc m) <=> (n = m)
Proof
  gvs[coSuc] >>
  rpt strip_tac >>
  eq_tac >>
  rpt strip_tac >>
  gvs[AllCaseEqs(),coNat_rep_to_coNat_abs] >>
  gvs[coNat_abs_11,coNat_rep_11]
QED

Theorem coPrev_11[simp]:
  !n m. coPrev n = coPrev m <=> (n = m)
Proof
  gvs[coPrev] >>
  rpt strip_tac >>
  eq_tac
  >- (
    gvs[AllCaseEqs()] >>
    rpt strip_tac >>
    gvs[coNat_rep_11,coNat_abs_11,coNat_rep_to_coNat_abs]) >>
  gvs[AllCaseEqs()] >>
  rpt strip_tac >>
  Cases_on `coNat_rep m` >>
  gvs[coNat_abs_11,coNat_rep_to_coNat_abs] >>
  Cases_on `n'` >>
  gvs[]
QED

Theorem coPrev_NONE_coZero[simp]:
  !n. coPrev n = NONE ==> n = coZero
Proof
  simp[forall_coNat] >>
  rpt strip_tac >>
  gvs[coPrev,AllCaseEqs(),coZero] >>
  gvs[coNat_rep_to_coNat_abs]
QED

Theorem coPrev_SOME_coSUC[simp]:
  !n m. coPrev n = SOME m ==> n = coSuc m
Proof
  simp[forall_coNat] >>
  rpt strip_tac >>
  gvs[coPrev] >>
  fs[AllCaseEqs()] >>
  fs[coSuc] >>
  gvs[coNat_abs_11,coNat_repabs']
QED

(* coNat_unfold :: ('a -> 'a option) -> 'a -> coNat *)
val coNat_unfold_def = zDefine `coNat_unfold f z = coNat_abs $
  if ?n. FUNPOW (flip OPTION_BIND f) n (f z) = NONE
  then SUC $ LEAST n. FUNPOW (flip OPTION_BIND f) n (f z) = NONE 
  else 0`;

Theorem FUNPOW_SOME_EQ_NONE:
  FUNPOW f n (SOME x) = NONE ==>
  ?m. n = SUC m
Proof
  Cases_on `n` >>
  gvs[FUNPOW]
QED

Theorem FUNPOW_SUC:
  FUNPOW (flip OPTION_BIND f) n (f x') = FUNPOW (flip OPTION_BIND f) (SUC n) (SOME x')
Proof
  gvs[FUNPOW]
QED

Theorem contrapositive:
  !A B. (A ==> ~B) <=> (B ==> ~A)
Proof
  metis_tac[]
QED

Theorem LEAST_SUC:
  (?n. P n) /\
  (LEAST y. P y) = SUC n ==>
  (LEAST y. P (SUC y)) = n
Proof
  rpt strip_tac >>
  rev_drule $ PURE_REWRITE_RULE[PULL_EXISTS] $ iffLR LEAST_EXISTS >>
  gvs[] >>
  rpt strip_tac >>
  simp[] >>
  `$LEAST P = (LEAST y. P y)` by metis_tac[] >>
  `$LEAST (P o SUC) = (LEAST y. P (SUC y))` by metis_tac[] >>
  irule EQ_TRANS >>
  first_x_assum $ irule_at (Pos $ el 1) o GSYM >>
  gvs[] >>
  qpat_x_assum `(LEAST y. P y) = _` kall_tac >>
  LEAST_ELIM_TAC >>
  gvs[] >>
  conj_tac >- metis_tac[] >>
  rpt strip_tac >>
  gvs[contrapositive] >>
  last_x_assum drule >>
  gvs[] >>
  rpt strip_tac >>
  qpat_x_assum `!m. _ ==> ~ _` $ assume_tac o PURE_REWRITE_RULE[Once contrapositive] >>
  last_x_assum kall_tac >>
  first_x_assum rev_drule >>
  gvs[]
QED

Theorem f_FUNPOW:
!n x.
  P (FUNPOW P n x) = FUNPOW P (SUC n) x
Proof
  Induct >-
  gvs[] >>
  first_x_assum $ assume_tac o SIMP_RULE(srw_ss())[FUNPOW] >>
  simp[FUNPOW]
QED

Theorem FUNPOW_n_m:
  !n m x.
  FUNPOW P n (FUNPOW P m x) = FUNPOW P (n+m) x
Proof
  Induct >>
  gvs[FUNPOW] >>
  rpt strip_tac >>
  simp[f_FUNPOW] >>
  gvs[ADD_CLAUSES]
QED

Theorem coNat_unfold:
  !f x. coNat_unfold f x =
  case f x of
  | NONE => coZero
  | SOME y => coSuc (coNat_unfold f y)
Proof
  rpt strip_tac >>
  Cases_on `f x`
  >- (
    simp[coNat_unfold_def,coZero,coNat_abs_11,AllCaseEqs()] >>
    `FUNPOW (flip OPTION_BIND f) 0 NONE = NONE` by simp[] >>
    conj_tac >- metis_tac[] >>
    EVAL_TAC
  ) >>
  Cases_on `?n. FUNPOW (flip OPTION_BIND f) n (SOME x') = NONE` >>
  gvs[coNat_unfold_def,coSuc,coNat_abs_11,AllCaseEqs(),coNat_repabs']
  >- (
    disj2_tac >>
    drule_then assume_tac FUNPOW_SOME_EQ_NONE >>
    conj_tac >- (
      gvs[FUNPOW] >> metis_tac[]
    ) >>
    conj_tac >- metis_tac[] >>
    gvs[] >>
    `(\y. FUNPOW (flip OPTION_BIND f) y (SOME x') = NONE) (SUC m)` by simp[BETA_THM] >>
    drule $ SIMP_RULE(srw_ss())[PULL_EXISTS] $ iffLR LEAST_EXISTS >>
    first_x_assum kall_tac >>
    gvs[] >>
    rpt strip_tac >>
    qmatch_asmsub_abbrev_tac `FUNPOW _ l (SOME x')` >>
    Cases_on `l` >>
    gvs[] >>
    last_x_assum $ kall_tac >>
    last_x_assum $ kall_tac >>
    gvs[FUNPOW] >>
    irule EQ_SYM >>
    gvs[FUNPOW_SUC] >>
    ho_match_mp_tac $ GEN_ALL LEAST_SUC >>
    gvs[] >>
    metis_tac[]
  ) >>
  gvs[FUNPOW_SUC]
QED

val from_nat_def = zDefine`
  from_nat n = coNat_unfold (\n. case n of
    | 0 => NONE
    | SUC v => SOME v) n`;

Theorem from_nat:
  (from_nat (SUC n) = coSuc (from_nat n)) /\
  (from_nat 0 = coZero)
Proof
  gvs[from_nat_def] >>
  PURE_REWRITE_TAC[Once coNat_unfold] >>
  gvs[] >>
  PURE_REWRITE_TAC[Once coNat_unfold] >>
  gvs[]
QED

Theorem coSuc_SUC:
  coSuc (coNat_abs (SUC l)) = coNat_abs (SUC (SUC l))
Proof
  gvs[coSuc] >>
  IF_CASES_TAC >>
  gvs[coNat_repabs']
QED

Theorem coSuc_0:
  coSuc (coNat_abs 0) = coNat_abs 0
Proof
  gvs[coSuc,coNat_repabs']
QED

Theorem unfold_ue_coSuc_inf:
  (!x. x IN R ==> f x = NONE \/ ?n. f x = SOME n /\ n IN R) /\
  (!x. x IN R ==> g x =
    case f x of
    | NONE => coZero
    | SOME v => coSuc (g v)) /\
  (!n. FUNPOW (flip OPTION_BIND f) n (f z) <> NONE) /\
  z IN R ==>
  g z = coNat_abs 0
Proof
  strip_tac >>
  last_x_assum $ markerLib.ASSUME_NAMED_TAC "C" >>
  last_x_assum $ markerLib.ASSUME_NAMED_TAC "L" >>
  spose_not_then assume_tac >>
  `?a. g z = coNat_abs (SUC a)`
  by (
    Cases_on `coNat_rep $ g z` >>
    metis_tac[coNat_abs_11,coNat_absrep]
  ) >>
  last_x_assum mp_tac >>
  simp[] >>
  `?n. !y. FUNPOW (flip OPTION_BIND f) n (f z) <> SOME y` suffices_by (
    rpt strip_tac >>
    qexists_tac `n` >>
    metis_tac[option_CASES]
  ) >>
  first_x_assum mp_tac >>
  last_x_assum mp_tac >>
  qid_spec_tac `z` >>
  Induct_on `a` >>
  rpt strip_tac >>
  gvs[]
  >- (
    markerLib.LABEL_ASSUM "L" $ qspec_then `z'` assume_tac >>
    markerLib.LABEL_ASSUM "C" $ qspec_then `z'` assume_tac >>
    Cases_on `f z'` >>
    gvs[coZero,coNat_abs_11]
    >- (
      qexists_tac `0` >>
      simp[FUNPOW]
    ) >>
    gvs[coZero,coNat_abs_11,coSuc,AllCaseEqs()]
  ) >>
  markerLib.LABEL_ASSUM "L" $ qspec_then `z'` assume_tac >>
  Cases_on `f z'`
  >- (
    qexists_tac `0` >>
    simp[FUNPOW]
  ) >>
  markerLib.LABEL_ASSUM "C" $ qspec_then `z'` assume_tac >>
  gvs[GSYM coSuc_SUC] >>
  res_tac >>
  qexists_tac `SUC n` >>
  simp[FUNPOW]
QED

Theorem unfold_ue_coSuc_fin:
!z.
 (!x. x IN R ==> f x = NONE \/ ?n. f x = SOME n /\ n IN R) /\
 ((!x. x IN R ==> g x =
    case f x of
    | NONE => coZero
    | SOME v => coSuc (g v)) /\
  FUNPOW (flip OPTION_BIND f) n (f z) = NONE /\
  (!m. m < n ==> ?x. FUNPOW (flip OPTION_BIND f) m (f z) = SOME x)) /\
  z IN R ==>
  g z = coNat_abs $ SUC n
Proof
  Induct_on `n` >>
  rpt strip_tac
  >- (
    last_x_assum $ markerLib.ASSUME_NAMED_TAC "C" >>
    last_x_assum $ markerLib.ASSUME_NAMED_TAC "L" >>
    markerLib.LABEL_ASSUM "L" $ qspec_then `z` assume_tac >>
    gvs[coZero]
  ) >>
  qpat_x_assum `!x. x IN R ==> g x = _` $ markerLib.ASSUME_NAMED_TAC "L" >>
  last_x_assum $ markerLib.ASSUME_NAMED_TAC "I" >>
  last_x_assum $ markerLib.ASSUME_NAMED_TAC "C" >>
  gvs[GSYM f_FUNPOW]
  >- (
    gvs[coNat_abs_11] >>
    first_x_assum $ qspec_then `n` assume_tac >>
    gvs[]
  ) >>
  markerLib.LABEL_ASSUM "L" $ qspec_then `z` assume_tac >>
  simp[GSYM coSuc_SUC,AllCaseEqs()] >>
  Cases_on `f z`
  >- (
    gvs[] >>
    first_x_assum $ qspec_then `0` assume_tac >>
    gvs[]
  ) >>
  irule_at (Pos hd) EQ_REFL >>
  markerLib.LABEL_ASSUM "I" irule >>
  conj_tac
  >- (
    rpt strip_tac >>
    markerLib.LABEL_ASSUM "L" irule >>
    simp[]
  ) >>
  conj_tac
  >- (
    rpt strip_tac >>
    markerLib.LABEL_X_ASSUM "C" irule >>
    simp[]
  ) >>
  conj_tac
  >- (
    rpt strip_tac >>
    PURE_REWRITE_TAC[FUNPOW_SUC] >>
    last_x_assum irule >>
    simp[] 
  ) >>
  conj_tac
  >- (
    PURE_REWRITE_TAC[FUNPOW_SUC] >>
    simp[GSYM f_FUNPOW]
  ) >>
  markerLib.LABEL_X_ASSUM "C" drule >>
  simp[]
QED

Theorem coNat_unfold_ue:
  (!x. x IN R ==> f x = NONE \/ ?n. f x = SOME n /\ n IN R) /\
  (!x. x IN R ==> g x =
    case f x of
    | NONE => coZero
    | SOME v => coSuc (g v)) ==>
  (!y. y IN R ==> g y = coNat_unfold f y)
Proof
  rpt strip_tac >>
  last_x_assum $ markerLib.ASSUME_NAMED_TAC "C" >>
  last_x_assum $ markerLib.ASSUME_NAMED_TAC "L" >>
  simp[coNat_unfold_def] >>
  Cases_on `(!n. FUNPOW (flip OPTION_BIND f) n (f y) <> NONE)`
  >- (
    IF_CASES_TAC >>
    simp[] >>
    rpt strip_tac >>
    markerLib.LABEL_X_ASSUM "L" assume_tac >>
    markerLib.LABEL_X_ASSUM "C" assume_tac >>
    metis_tac[unfold_ue_coSuc_inf]
  ) >>
  gvs[] >>
  `(\x.FUNPOW (flip OPTION_BIND f) x (f y) = NONE) n` by simp[] >>
  drule $ PURE_REWRITE_RULE[PULL_EXISTS] LEAST_EXISTS_IMP >>
  simp[] >>
  ntac 2 (first_x_assum kall_tac) >>
  rpt strip_tac >>
  qabbrev_tac `l = (LEAST x. FUNPOW (flip OPTION_BIND f) x (f y) = NONE)` >>
  IF_CASES_TAC >>
  gvs[] >>
  first_x_assum kall_tac >>
  markerLib.LABEL_X_ASSUM "L" assume_tac >>
  markerLib.LABEL_X_ASSUM "C" assume_tac >>
  drule_then irule unfold_ue_coSuc_fin>>
  first_x_assum $ irule_at Any >>
  first_x_assum kall_tac >>
  metis_tac[option_CASES]
QED

Theorem coNat_Axiom_ue:
  !f. (!x. x IN R ==> f x = NONE \/ ?n. f x = SOME n /\ n IN R) ==>
  (?g. (!x. x IN R ==>
    g x = case f x of NONE => coZero | SOME v => coSuc (g v))) /\
  (!g h.
    (!x. x IN R ==>
      g x = case f x of NONE => coZero | SOME v => coSuc (g v)) /\
    (!x. x IN R ==>
      h x = case f x of NONE => coZero | SOME v => coSuc (h v)) ==> 
    (!x. x IN R ==> g x = h x))
Proof
  rpt strip_tac
  >- (
    qexists `coNat_unfold f` >>
    metis_tac[coNat_unfold] ) >>
  irule EQ_TRANS >>
  qexists `coNat_unfold f x` >>
  drule_all_then (irule_at (Pos hd)) coNat_unfold_ue >>
  irule EQ_SYM >>
  drule_all_then irule coNat_unfold_ue
QED

Theorem coNat_Axiom_ue':
  !f. ?!g. !x. g x = case f x of NONE => coZero | SOME v => coSuc (g v)
Proof
  strip_tac >>
  simp[EXISTS_UNIQUE_THM] >>
  rpt strip_tac
  >- (
    qspecl_then [`UNIV`,`f`] (irule o SIMP_RULE (srw_ss())[PULL_FORALL]) $ cj 1 $ GEN_ALL coNat_Axiom_ue >>
    metis_tac[option_CASES]
  ) >>
  PURE_REWRITE_TAC[FUN_EQ_THM] >>
  rpt strip_tac >>
  qspecl_then [`UNIV`,`f`] assume_tac $ cj 2 $ GEN_ALL coNat_Axiom_ue >>
  first_x_assum mp_tac >>
  impl_tac
  >- (simp[] >> metis_tac[option_CASES]) >>
  disch_then irule >>
  reverse (rpt strip_tac)
  >- simp[] >>
  first_x_assum irule
QED

Theorem coNat_bisimulation_lemma:
!R f x.
  (!x. x IN R ==>
    (f x = NONE \/ THE (f x) IN R) /\
    (OPTION_MAP FST o f) x = (coPrev o FST) x /\
    (OPTION_MAP SND o f) x = (coPrev o SND) x) /\
  x IN R ==> FST x = SND x
Proof
  rpt strip_tac >>
  irule EQ_TRANS >>
  qexists `coNat_unfold f x` >>
  drule_at_then Any (irule_at (Pos hd)) coNat_unfold_ue >>
  conj_tac
  >- (
    rpt strip_tac >>
    first_x_assum $ drule_then assume_tac >>
    Cases_on `f x'` >>
    rw[] ) >>
  conj_tac
  >- (
    rpt strip_tac >>
    first_x_assum $ drule_then assume_tac >>
    gvs[combinTheory.o_DEF,DefnBase.one_line_ify NONE OPTION_MAP_DEF] >>
    Cases_on `f x'` >>
    gvs[] ) >>
  irule EQ_SYM >>
  drule_at_then Any irule coNat_unfold_ue >>
  conj_tac
  >- (
    rpt strip_tac >>
    first_x_assum $ drule_then assume_tac >>
    Cases_on `f x'` >>
    gvs[combinTheory.o_DEF,DefnBase.one_line_ify NONE OPTION_MAP_DEF] >>
    rw[] ) >>
  rpt strip_tac >>
  first_x_assum $ drule_then assume_tac >>
  Cases_on `f x'` >>
  rw[]
QED

Theorem coNat_bisimulation:
  (n = m) <=>
  ?R. R n m /\
    (!n m. R n m ==>
      (n = coZero /\ m = coZero) \/
      (?x y. n = coSuc x /\ m = coSuc y /\ R x y))
Proof
  eq_tac >>
  rpt strip_tac
  >- (
    qexists `\x y. x = y` >>
    simp[] >>
    rpt strip_tac >>
    qspec_then `n'` assume_tac coNat_CASES >>
    metis_tac[]
  ) >>
  qspecl_then [`\(n,m). R n m`,`\(n,m). if n = coZero /\ m = coZero then NONE else SOME (THE (coPrev n), THE (coPrev m))`,`(n,m)`] assume_tac coNat_bisimulation_lemma >>
  gvs[] >>
  first_x_assum irule >>
  rpt strip_tac >>
  Cases_on `x` >>
  gvs[] >>
  first_x_assum $ drule_then assume_tac >>
  gvs[coPrev_coSuc,coPrev_coZero]
QED

Theorem exists_inf:
  ?w. w = coSuc w
Proof
  qexists `coNat_unfold (\k. SOME ()) ()` >>
  ONCE_REWRITE_TAC[Once coNat_unfold] >>
  simp[]
QED

Theorem inf_coSuc_unfold:
  inf = coSuc inf ==>
  inf = coNat_unfold (\k. SOME ()) ()
Proof
  `inf = (\k. inf) ()` by simp[] >>
  rpt strip_tac >>
  irule EQ_TRANS >>
  last_x_assum $ irule_at Any >>
  irule coNat_unfold_ue >>
  rpt strip_tac >>
  simp[] >>
  metis_tac[EVAL``() IN {()}``]
QED

Theorem inf_unique:
  inf = coSuc inf /\
  w = coSuc w ==>
  inf = w
Proof
  rpt strip_tac >>
  imp_res_tac inf_coSuc_unfold >> 
  simp[]
QED

Theorem from_nat_not_infinite:
!x y.
  from_nat x = y ==>
  y <> coSuc y
Proof
  Induct_on `x` >>
  rpt strip_tac >>
  fs[from_nat_def,Once coNat_unfold] >>
  fs[AllCaseEqs()] >>
  gvs[coSuc_NOT_coZero]
QED

