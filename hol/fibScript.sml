open bossLib whileTheory pred_setTheory relationTheory combinTheory optionTheory;
open listTheory;
open arithmeticTheory numLib BasicProvers dep_rewrite;

Definition MPOWER_def:
  MPOWER f 0 x = x /\
  MPOWER f (SUC n) x =
    if EVEN n then
      let m = MPOWER f (n DIV 2) x in
        f m m
    else
      let m = MPOWER f (n DIV 2) x in
        f m (f x m)
Termination
  WF_REL_TAC `measure $ FST o SND` >>
  rw[] >>
  Cases_on `n` >>
  simp[] >>
  irule LESS_TRANS >>
  qexists `SUC n'` >>
  simp[]
End

Definition assoc_def:
  assoc s f <=> !x y z. x IN s /\ y IN s /\ z IN s ==>
    f (f x y) z = f x (f y z)
End

Definition closed_def:
  closed s f <=> !x. x IN s ==> f x IN s
End

Theorem FUNPOW_closed:
  closed s f ==>
    closed s (FUNPOW f n)
Proof
  strip_tac >>
  Induct_on `n` >>
  fs[closed_def,FUNPOW]
QED

Theorem ASSOC_FUNPOW_ADD:
  assoc s f /\ closed s (f x) /\ x IN s  ==>
  f (FUNPOW (f x) n x) (FUNPOW (f x) m x) =
    f x (FUNPOW (f x) (n + m) x)
Proof
  strip_tac >>
  Induct_on `n` >>
  gvs[assoc_def,FUNPOW_SUC] >>
  irule EQ_TRANS >>
  last_x_assum $ irule_at (Pos hd) >>
  drule FUNPOW_closed >>
  simp[closed_def,FUNPOW_SUC,
    DECIDE``m + SUC n = SUC (m + n)``]
QED

Theorem MPOWER_FUNPOW:
  !f n x.
  assoc s f /\ closed s (f x) /\ x IN s ==>
    MPOWER f n x = FUNPOW (f x) n x
Proof
  recInduct MPOWER_ind >>
  rw[] >>
  gvs[MPOWER_def] >>
  drule_all ASSOC_FUNPOW_ADD >>
  simp[GSYM FUNPOW_SUC] >>
  disch_then kall_tac >>
  rw[FUNPOW_SUC] >>
  qspec_then `2` (qspec_then `n` assume_tac o GSYM o SRULE[]) DIVISION >>
  gvs[MOD_2,ADD1]
QED

Theorem SUM_DISTRIB_LEFT:
  a * SUM l = SUM (MAP (\x. a * x) l)
Proof
  Induct_on `l` >>
  simp[]
QED

Theorem SUM_DISTRIB_RIGHT:
  SUM l * a = SUM (MAP (\x. a * x) l)
Proof
  Induct_on `l` >>
  simp[]
QED

Theorem SUM_ADD:
  SUM (GENLIST f j) + SUM (GENLIST g j) = SUM (GENLIST (\x. f x + g x) j)
Proof
  Induct_on `j` >>
  simp[GENLIST,SUM_SNOC]
QED

Theorem SUM_COMM:
  SUM (GENLIST (\i'. SUM (GENLIST (\j'. g i' j') j)) i)  =
  SUM (GENLIST (\j'. SUM (GENLIST (\i'. g i' j') i)) j)
Proof
  Induct_on `i`
  >- (
    Induct_on `j` >>
    fs[GENLIST,SUM_SNOC]) >>
  fs[GENLIST,SUM_SNOC,SUM_ADD]
QED

(* a : l * m, b : m * n  = l * n *)
Definition matrix_MUL_def:
  matrix_MUL a b l m n =
    GENLIST (\i.
      GENLIST (\j.
        SUM $ GENLIST (\k. EL k (EL i a) * EL j (EL k b)) m) n) l
End

Theorem matrix_MUL_EL:
  i < l /\ j < n ==>
  EL j (EL i $ matrix_MUL a b l m n) = SUM $ GENLIST (\k. EL k (EL i a) * EL j (EL k b)) m
Proof
  rw[] >>
  imp_res_tac EL_GENLIST >>
  qmatch_goalsub_abbrev_tac`EL j x` >>
  `x =GENLIST (λj'.
      SUM (GENLIST (λk. EL j' (EL k b) * EL k (EL i a)) m)) n` by gvs[EL_GENLIST,matrix_MUL_def,markerTheory.Abbrev_def] >>
  gvs[]
QED

Theorem matrix_MUL_LENGTH:
  LENGTH (matrix_MUL a b l m n) = l /\
  (i < l ==>
    LENGTH (EL i $ matrix_MUL a b l m n) = n)
Proof
  simp[matrix_MUL_def]
QED

Theorem matrix_MUL_CONG:
  (!i j k. i < l /\ j < n /\ k < m ==>
    EL j (EL k b) * EL k (EL i a) =
      EL j (EL k b') * EL k (EL i a')) /\
  l = l' /\ m = m' /\ n = n' ==>
  matrix_MUL a b l m n = matrix_MUL a' b' l' m' n'
Proof
  rw[matrix_MUL_def] >>
  irule GENLIST_CONG >>
  rw[] >>
  irule GENLIST_CONG >>
  rw[] >>
  AP_TERM_TAC >>
  irule GENLIST_CONG >>
  rw[]
QED

Theorem matrix_MUL_assoc_lem1:
  x < l ==>
  GENLIST (\k. EL k (EL x (matrix_MUL a b l m n)) * EL x' (EL k c)) n =
    GENLIST (\k. SUM (GENLIST (\k'.
        EL k' (EL x a) *
        EL k (EL k' b) *
        EL x' (EL k c)) m)) n
Proof
  strip_tac >>
  irule GENLIST_CONG >>
  rw[matrix_MUL_EL,SUM_DISTRIB_RIGHT,
    MAP_GENLIST,o_DEF]
QED

Theorem matrix_MUL_assoc_lem2:
  x' < r ==>
  GENLIST (λk. EL k (EL x a) * EL x' (EL k 
    (matrix_MUL b c m n r))) m =
  GENLIST (\k. EL k (EL x a) * SUM (GENLIST
    (\y. EL y (EL k b) * EL x' (EL y c)) n)) m
Proof
  strip_tac >>
  irule GENLIST_CONG >>
  rw[matrix_MUL_EL,SUM_DISTRIB_LEFT,
    MAP_GENLIST,o_DEF] >>
  AP_TERM_TAC >>
  irule GENLIST_CONG >>
  rw[]
QED

Theorem matrix_MUL_assoc:
  matrix_MUL (matrix_MUL a b l m n) c l n r =
    matrix_MUL a (matrix_MUL b c m n r) l m r
Proof
  rw[LIST_EQ_REWRITE,
    matrix_MUL_LENGTH,matrix_MUL_EL] >>
  last_x_assum assume_tac >>
  drule matrix_MUL_assoc_lem1 >>
  simp[] >>
  disch_then kall_tac >>
  rev_drule matrix_MUL_assoc_lem2 >>
  simp[] >>
  disch_then kall_tac >>
  simp[SUM_COMM] >>
  AP_TERM_TAC >>
  irule GENLIST_CONG >>
  rw[SUM_DISTRIB_RIGHT,MAP_GENLIST,o_DEF] >>
  AP_TERM_TAC >>
  irule GENLIST_CONG >>
  rw[]
QED

Definition fib_def:
  fib 0 = 1 /\
  fib (SUC 0) = 1 /\
  fib (SUC (SUC n)) = fib (SUC n) + fib n
End


Definition fib_mat_def:
  fib_mat = [[1;1];[1;0]]
End

Definition mul222_def:
  mul222 x y = matrix_MUL x y 2 2 2
End

Theorem fib_matrix:
  EL 0 (EL 0 $ FUNPOW (mul222 fib_mat) n fib_mat) = fib (SUC n) /\
  EL 0  (EL 1 $ FUNPOW (mul222 fib_mat) n fib_mat) = fib n /\
  EL 1  (EL 0 $ FUNPOW (mul222 fib_mat) n fib_mat) = fib n /\
  EL 1 (EL 1 $ FUNPOW (mul222 fib_mat) n fib_mat) =
    (if n = 0 then 0 else fib (n - 1))
Proof
  Induct_on `n` >>
  rw[fib_def,fib_mat_def,FUNPOW_SUC] >>
  EVAL_TAC >>
  rw[] >>
  simp[fib_def] >>
  simp[SRULE [GSYM ONE] $ cj 2 fib_def] >>
  Cases_on `n` >>
  simp[fib_def]
QED

Theorem log_fib:
  HD $ HD $ MPOWER mul222 n fib_mat = fib (SUC n)
Proof
  irule EQ_TRANS >>
  assume_tac $ cj 1 fib_matrix >>
  first_x_assum $ irule_at (Pos last) >>
  simp[] >>
  ntac 2 AP_TERM_TAC >>
  irule MPOWER_FUNPOW >>
  qexists `UNIV` >>
  simp[closed_def,assoc_def,mul222_def] >>
  irule matrix_MUL_assoc
QED

