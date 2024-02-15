open bossLib boolLib BasicProvers dep_rewrite pred_setTheory optionTheory pairTheory combinTheory listTheory 

(*
F(X) = 1 + A * X

F(X) -> F(Y)
|[[];uncurry ::]|[e;f]
v       v
X  ->   Y
  foldr f e
*)

Definition LF_CONSTRUCT_def:
  LF_CONSTRUCT z = option_CASE z [] (\(x,y). x::y)
End

Theorem LF_CONSTRUCT_simp[simp]:
  LF_CONSTRUCT NONE = [] /\
  !x y. LF_CONSTRUCT (SOME (x,y)) = x::y
Proof
  simp[LF_CONSTRUCT_def]
QED

Theorem LF_CONSTRUCT_SOME:
  !x. LF_CONSTRUCT (SOME x) = FST x::SND x
Proof
  rpt strip_tac >>
  Cases_on `x` >>
  simp[LF_CONSTRUCT_def]
QED

Definition FOLD_def:
  FOLD f = FOLDR (\x y. f $ SOME (x,y)) (f NONE)
End

Theorem FOLD_simp:
  (!f. FOLD f [] = f NONE) /\
  (!f x xs. FOLD f (x::xs) = f $ SOME (x,FOLD f xs))
Proof
  simp[FOLD_def]
QED

Definition LF_MAP_def:
  LF_MAP f = OPTION_MAP (I ## f)
End

Theorem PAIR_MAP_I:
  I ## I = I
Proof
  rw[FUN_EQ_THM] >>
  Cases_on `x` >>
  simp[]
QED

Theorem LF_MAP_I:
  LF_MAP I = I
Proof
  simp[LF_MAP_def,PAIR_MAP_I,FUN_EQ_THM] 
QED

Theorem PAIR_MAP_COMPOSE:
  (h ## f) o (h' ## g) = (h o h' ## f o g)
Proof
  rw[FUN_EQ_THM] >>
  Cases_on `x` >>
  simp[]
QED

Theorem OPTION_MAP_COMPOSE2:
  OPTION_MAP f o OPTION_MAP g = OPTION_MAP (f o g)
Proof
  rw[FUN_EQ_THM,OPTION_MAP_COMPOSE]
QED

Theorem LF_MAP_COMPOSE:
  (LF_MAP f) o (LF_MAP g) = LF_MAP (f o g)
Proof
  simp[LF_MAP_def,OPTION_MAP_COMPOSE2] >>
  AP_TERM_TAC >>
  simp[PAIR_MAP_COMPOSE]
QED

Theorem LF_MAP_compute_NONE[simp]:
  !x. LF_MAP x NONE = NONE
Proof
  simp[LF_MAP_def]
QED

Theorem LF_MAP_compute_SOME[simp]:
  !f x y. LF_MAP f (SOME (x,y)) = SOME $ (x, f y)
Proof
  simp[LF_MAP_def]
QED

Theorem LF_MAP_SOME:
  !f x. LF_MAP f (SOME x) = SOME $ (FST x, f $ SND x)
Proof
  rpt strip_tac >>
  Cases_on `x` >>
  gvs[]
QED

Theorem FOLD_commute:
  (FOLD f) o LF_CONSTRUCT =
  f o LF_MAP (FOLD f)
Proof
  gvs[o_DEF,FUN_EQ_THM] >>
  rpt strip_tac >>
  Cases_on `x` >>
  gvs[FOLD_simp,LF_MAP_SOME,LF_CONSTRUCT_SOME]
QED

Theorem FOLD_unique:
  g o LF_CONSTRUCT =
  f o (LF_MAP g) ==>
  g = FOLD f
Proof
  rpt strip_tac >>
  fs[FUN_EQ_THM] >>
  rpt strip_tac >>
  Induct_on `x` >>
  rpt strip_tac >>
  simp[]
  >- (
    first_x_assum $ qspec_then `NONE` assume_tac >>
    gvs[FOLD_simp]
  ) >>
  first_x_assum $ qspec_then `SOME (h,x)` assume_tac >>
  gvs[FOLD_simp]
QED

Theorem FOLD_unique_strong:
!R f g.
  (!x. ((x = NONE) \/ (SND (THE x) IN R)) ==> f x IN R) ==>
  g o LF_CONSTRUCT =
  f o (LF_MAP g) ==>
  g = FOLD f /\ !x. g x IN R
Proof
  ntac 4 strip_tac >>
  fs[FUN_EQ_THM] >>
  rpt strip_tac >>
  simp[] >>
  Induct_on `x` >>
  rpt strip_tac >>
  simp[]
  >>~- ([`[]`],
    first_x_assum $ qspec_then `NONE` assume_tac >>
    gvs[FOLD_simp]
  ) >>
  first_x_assum $ qspec_then `SOME (h,x)` assume_tac >>
  gvs[FOLD_simp]
QED

Theorem FOLD_unique:
  g o LF_CONSTRUCT =
  f o (LF_MAP g) ==>
  g = FOLD f
Proof
  rpt strip_tac >>
  qspec_then `UNIV` irule (cj 1 FOLD_unique_strong) >>
  simp[]
QED

(* Proof congruence and induction without using induction (only using FOLD_unique)*)
Theorem FOLD_I:
  FOLD LF_CONSTRUCT = I
Proof
  irule EQ_SYM >>
  irule FOLD_unique >>
  simp[LF_MAP_I]
QED

Theorem FOLD_I_unique:
  g o LF_CONSTRUCT =
  LF_CONSTRUCT o LF_MAP g ==>
  g = I
Proof
  rpt strip_tac >>
  irule EQ_TRANS >>
  irule_at (Pos hd) FOLD_unique >>
  first_x_assum $ irule_at (Pos hd) >>
  irule FOLD_I
QED

Definition list_cong_def:
  list_cong R f g <=>
    (!x. ((x = NONE) \/ (SND (THE x) IN R)) ==>
      f x IN R /\
      (FST o f) x = (g o LF_MAP FST) x /\
      (SND o f) x = (g o LF_MAP SND) x)
End

Theorem FOLD_IN_R:
  (!x. (x = NONE \/ SND (THE x) IN R) ==> f x IN R) ==>
  !x. FOLD f x IN R
Proof
  rpt strip_tac >>
  drule_then irule (cj 2 FOLD_unique_strong) >>
  irule FOLD_commute
QED

Theorem list_cong_lem:
  list_cong R f LF_CONSTRUCT ==>
  FST o (FOLD f) = I /\
  SND o (FOLD f) = I
Proof
  rw[list_cong_def] >>
  irule FOLD_I_unique >>
  gvs[o_DEF,FUN_EQ_THM] >>
  rpt strip_tac >>
  Cases_on `x` >>
  gvs[ELIM_UNCURRY,FOLD_simp] >>
  Cases_on `x'` >>
  gvs[FOLD_simp] >>
  irule EQ_TRANS >>
  TRY $ first_assum $ irule_at (Pos hd) o cj 2 >>
  TRY $ first_assum $ irule_at (Pos hd) o cj 3 >>
  simp[] >>
  irule FOLD_IN_R >>
  metis_tac[]
QED

Theorem list_cong_thm:
  list_cong R f LF_CONSTRUCT ==>
  !x. (x,x) IN R
Proof
  rpt strip_tac >>
  drule list_cong_lem >>
  rw[] >>
  `FOLD f x = (x,x)`
    by gvs[FUN_EQ_THM,PAIR_FST_SND_EQ] >>
  first_x_assum $ assume_tac o GSYM >>
  simp[] >>
  irule FOLD_IN_R >>
  metis_tac[list_cong_def]
QED

Theorem list_induction_lemma:
  (P [] ∧ (∀t. P t ⇒ ∀h. P (h::t))) ==>
  list_cong (\(x,y). P x /\ P y) (\x.
    case x of
    | NONE => ([],[])
    | SOME (x,xs,ys) => (x::xs,x::ys)) LF_CONSTRUCT
Proof
  rw[list_cong_def] >>
  gvs[] >>
  rpt (TOP_CASE_TAC >> gvs[])
QED

Theorem list_induction_from_fold_unique:
  P [] ∧ (∀t. P t ⇒ ∀h. P (h::t)) ⇒ ∀l. P l
Proof
  rpt strip_tac >>
  drule_all_then assume_tac list_induction_lemma >>
  drule list_cong_thm >>
  simp[]
QED

