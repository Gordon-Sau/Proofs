open HolKernel boolLib BasicProvers pairTheory;
open pred_setTheory relationTheory combinTheory;

Theorem type_inhabited[local]:
  ?(p:('a # 'b)set). (λs. ∀x y y2. (x,y) ∈ s ∧ (x,y2) ∈ s ⇒  y = y2) p
Proof 
  Q.EXISTS_TAC `{}` >> simp[]
QED

val pfunc_tydef = new_type_definition ("pfunc", type_inhabited);

val repabs_fns = define_new_type_bijections {
  name = "pfunc_absrep",
  ABS = "pfunc_abs",
  REP = "pfunc_rep",
  tyax = pfunc_tydef};

val pfunc_absrep = CONJUNCT1 repabs_fns;
val pfunc_repabs = SRULE[] $ CONJUNCT2 repabs_fns;

Triviality pfunc_rep_11:
  (pfunc_rep t1 = pfunc_rep t2) = (t1 = t2)
Proof
  rw[EQ_IMP_THM] >>
  metis_tac[pfunc_absrep]
QED

Triviality forall_pfunc:
  (!x. P x) = (!y. P (pfunc_abs y))
Proof
  rpt strip_tac >>
  eq_tac >>
  rpt strip_tac
  >- metis_tac[] >>
  PURE_REWRITE_TAC[Once $ GSYM pfunc_absrep] >>
  simp[]
QED

Triviality pfunc_rep_IMP_unique:
  ∀x y y2. (x,y) ∈ pfunc_rep pf ∧ (x,y2) ∈ pfunc_rep pf ⇒
  y = y2
Proof
  rpt strip_tac >>
  irule $ iffRL pfunc_repabs >>
  ntac 2 $ first_x_assum $ irule_at (Pos last) >>
  simp[pfunc_absrep]
QED

Triviality forall_pfunc_rep:
  (!x. P (pfunc_rep x)) = (!s. (∀x y y2. (x,y) ∈ s ∧ (x,y2) ∈ s ⇒ y = y2) ⇒ P s)
Proof
  rpt strip_tac >>
  eq_tac >>
  rpt strip_tac
  >- (
    drule $ iffLR pfunc_repabs >>
    metis_tac[]) >>
  last_x_assum irule >>
  metis_tac[pfunc_rep_IMP_unique]
QED

Definition domain_def:
  domain pf = {x | ∃y. (x,y) ∈ pfunc_rep pf}
End

Definition func_to_pfunc_def:
  func_to_pfunc f = pfunc_abs (λ(x,y). y = f x)
End

Triviality pfunc_rep_func_to_pfunc:
  pfunc_rep (func_to_pfunc f) = (λ(x,y). y = f x)
Proof
  simp[func_to_pfunc_def] >>
  qmatch_goalsub_abbrev_tac `pfunc_abs R` >>
  `(∀x y y2. (x,y) ∈ R ∧ (x,y2) ∈ R ⇒ y = y2)`
    by rw[IN_DEF,Abbr`R`] >>
  drule_then irule $ iffLR pfunc_repabs
QED

Theorem domain_func_to_pfunc:
  domain (func_to_pfunc f) = UNIV
Proof
  rw[domain_def,pfunc_rep_func_to_pfunc]
QED

Definition ap_def:
  ap pf x =
    if x ∈ domain pf
    then @y. pfunc_rep pf (x,y)
    else ARB pf x
End

Theorem ap_func_to_pfunc:
  ap (func_to_pfunc f) x = f x
Proof
  simp[ap_def,domain_func_to_pfunc,pfunc_rep_func_to_pfunc]
QED

Definition restrict_def:
  restrict d pf = pfunc_abs (λ(x,y). d x ∧ pfunc_rep pf (x,y))
End

Triviality pfunc_rep_abs_pf:
  pfunc_rep (pfunc_abs (λ(x,y). d x ∧ pfunc_rep pf (x,y))) =
   (λ(x,y). d x ∧ pfunc_rep pf (x,y))
Proof
  irule $ iffLR pfunc_repabs >>
  rw[] >>
  metis_tac[SRULE[IN_DEF]pfunc_rep_IMP_unique]
QED

Theorem domain_restrict:
  domain (restrict d pf) = d ∩ domain pf
Proof
  rw[domain_def,restrict_def,EXTENSION,IN_DEF,
    EQ_IMP_THM,pfunc_rep_abs_pf] >>
  metis_tac[]
QED

Theorem restrict_ap_thm:
  d x ∧ domain pf1 x ⇒
  ap (restrict d pf1) x = ap pf1 x
Proof
  simp[ap_def,domain_restrict,IN_DEF] >>
  rw[restrict_def,pfunc_rep_abs_pf]
QED

Triviality pfunc_rep_SELECT:
  domain pf x ⇒
  (y = @y. pfunc_rep pf (x,y)) = pfunc_rep pf (x,y)
Proof
  strip_tac >>
  SELECT_ELIM_TAC >>
  rw[]
  >- (fs[domain_def,IN_DEF] >> metis_tac[]) >>
  metis_tac[SRULE[IN_DEF]pfunc_rep_IMP_unique]
QED

Theorem pfunc_restrict:
  ∃f. pf = restrict (domain pf) (func_to_pfunc f)
Proof
  qexists `\x. @y. pfunc_rep pf (x,y)` >>
  simp[restrict_def,pfunc_rep_func_to_pfunc] >>
  qmatch_goalsub_abbrev_tac `pfunc_abs f` >> 
  `f = λ(x,y). domain pf x ∧ pfunc_rep pf (x,y)`
    by (
      rw[Abbr`f`,FUN_EQ_THM,EQ_IMP_THM,pfunc_rep_SELECT] >>
      SELECT_ELIM_TAC >>
      fs[domain_def,IN_DEF] >>
      metis_tac[]
    ) >>
  rw[Once $ GSYM pfunc_rep_11,pfunc_rep_abs_pf,
    FUN_EQ_THM,EQ_IMP_THM] >>
  pairarg_tac >>
  fs[domain_def,IN_DEF] >>
  metis_tac[]
QED

Theorem pfunc_case:
  ∀pf. ∃d f. pf = restrict d (func_to_pfunc f)
Proof
  metis_tac[pfunc_restrict]
QED

fun pfunc_Case tm = STRUCT_CASES_TAC (Q.SPEC tm pfunc_case);

Theorem restrict_func_to_pfunc_eq_thm:
  (restrict d1 (func_to_pfunc f1) =
  restrict d2 (func_to_pfunc f2)) ⇔
  (d1 = d2 ∧ ∀x. d2 x ⇒ f1 x = f2 x)
Proof
  simp[EQ_IMP_THM] >>
  conj_tac
  >- (
    `domain (restrict d1 (func_to_pfunc f1)) = d1`
      by simp[domain_restrict,domain_func_to_pfunc] >>
    `domain (restrict d2 (func_to_pfunc f2)) = d2`
      by simp[domain_restrict,domain_func_to_pfunc] >>
    strip_tac >>
    conj_asm1_tac
    >- metis_tac[] >>
    rpt strip_tac >>
    `ap (restrict d1 (func_to_pfunc f1)) x = f1 x`
      by (
        irule EQ_TRANS >>
        irule_at (Pos hd) restrict_ap_thm >>
        simp[domain_func_to_pfunc] >>
        simp[ap_func_to_pfunc]) >>
    `ap (restrict d2 (func_to_pfunc f2)) x = f2 x`
      by (
        irule EQ_TRANS >>
        irule_at (Pos hd) restrict_ap_thm >>
        simp[domain_func_to_pfunc] >>
        simp[ap_func_to_pfunc]) >>
    metis_tac[]
  ) >>
  rpt strip_tac >>
  simp[restrict_def,pfunc_rep_func_to_pfunc] >>
  AP_TERM_TAC >>
  rw[FUN_EQ_THM,EQ_IMP_THM]
QED

Theorem pfunc_cong_thm:
  (domain pf1 = domain pf2 ∧
  ∀x. domain pf2 x ⇒ ap pf1 x = ap pf2 x) ⇒
  pf1 = pf2
Proof
  pfunc_Case `pf1` >>
  pfunc_Case `pf2` >>
  simp[domain_restrict,domain_func_to_pfunc,IN_DEF] >>
  rw[restrict_func_to_pfunc_eq_thm] >>
  gvs[restrict_ap_thm,domain_func_to_pfunc,
    ap_func_to_pfunc]
QED

Theorem restrict_restrict:
  restrict d1 (restrict d2 pf1) = restrict (d1 ∩ d2) pf1
Proof
  irule pfunc_cong_thm >>
  simp[domain_restrict,restrict_ap_thm,IN_DEF] >>
  metis_tac[INTER_COMM,INTER_ASSOC]
QED

Theorem restrict_eq:
  d ∩ domain f = d' ∩ domain f' ∧
  (∀x. d' x ∧ domain f' x ⇒ ap f x = ap f' x) ⇒
  restrict d f = restrict d' f'
Proof
  pfunc_Case `f` >>
  pfunc_Case `f'` >>
  rpt strip_tac >>
  rw[restrict_restrict,restrict_func_to_pfunc_eq_thm] >>
  fs[domain_restrict,domain_func_to_pfunc,
    restrict_ap_thm,ap_func_to_pfunc,IN_DEF] >>
  last_x_assum drule_all >>
  `d'' x` by (
    fs[INTER_DEF,FUN_EQ_THM,IN_DEF] >>
    metis_tac[]) >>
  simp[domain_restrict,domain_func_to_pfunc,
    restrict_ap_thm,ap_func_to_pfunc,IN_DEF]
QED

Definition safe_ap_def:
  safe_ap pf = λx. if domain pf x then SOME $ ap pf x else NONE
End

Theorem safe_ap_restrict:
  safe_ap (restrict d pf) x =
    if d x then safe_ap pf x else NONE
Proof
  simp[domain_restrict,safe_ap_def,restrict_ap_thm,IN_DEF] >>
  IF_CASES_TAC >>
  metis_tac[]
QED

Theorem safe_ap_restrict_ap:
  safe_ap (restrict d pf) x =
    if d x ∧ domain pf x then SOME $ ap pf x else NONE
Proof
  simp[domain_restrict,safe_ap_def,restrict_ap_thm,IN_DEF]
QED

Theorem safe_ap_func_to_pfunc:
  safe_ap (func_to_pfunc f) x = SOME $ f x
Proof
  simp[domain_func_to_pfunc,safe_ap_def,ap_func_to_pfunc]
QED

Theorem safe_ap_thm:
  safe_ap (restrict d (func_to_pfunc f)) x =
    if d x then SOME $ f x else NONE
Proof
  simp[safe_ap_restrict,safe_ap_func_to_pfunc]
QED

