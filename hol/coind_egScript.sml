open bossLib whileTheory pred_setTheory relationTheory optionTheory;
open llistTheory;
open arithmeticTheory numLib BasicProvers dep_rewrite;

CoInductive not_mem:
  (!x. not_mem x [||]) /\
  (!x y xs. not_mem x xs /\ y <> x ==> not_mem x (y:::xs))
End

Datatype:
  A= A' (bool -> A) | B
End

Datatype:
  A = L A | R A | B
End

Definition ones_def:
  ones = LUNFOLD (\x. SOME ((),1)) ()
End

Theorem ones:
  1:::ones = ones
Proof
  simp[ones_def] >>
  CONV_TAC $ RHS_CONV $ SCONV[Once LUNFOLD] >>
  simp[]
QED

Triviality two_not_mem_ones:
  not_mem 2 ones
Proof
  irule not_mem_coind >>
  qexists `\x y. y = ones /\ x = 2` >>
  simp[] >>
  disj2_tac >>
  irule_at (Pos hd) ones >>
  simp[]
QED

Triviality one_not_mem_ones:
  ~(not_mem 1 ones)
Proof
  strip_tac >>
  drule $ iffLR not_mem_cases >>
  simp[Once $ GSYM ones] >>
  simp[Once $ GSYM ones]
QED

Theorem not_mem_LNTH:
  not_mem x l <=> !n. LNTH n l <> SOME x
Proof
  eq_tac
  >- (
    simp[PULL_FORALL] >>
    qid_spec_tac `l` >>
    qid_spec_tac `x` >>
    Induct_on `n` >>
    Cases_on `l` >>
    rw[LNTH_THM] >>
    drule $ iffLR not_mem_cases >>
    simp[]
  ) >>
  strip_tac >>
  irule not_mem_coind >>
  qexists `\x l. !n. LNTH n l <> SOME x` >>
  rw[] >>
  Cases_on `a1` >>
  rw[]
  >- (
    first_x_assum $ qspec_then `SUC n` mp_tac >>
    simp[LNTH_THM]
  ) >>
  first_x_assum $ qspec_then `0` mp_tac >>
  simp[LNTH_THM]
QED

CoInductive comem:
(* only correct for finite llist.
* Every pair with an infinite list would satisfy mem *)
  (!x xs. comem x (x:::xs)) /\
  (!x y xs. comem x xs ==> comem x (y:::xs))
End

Theorem inf_imp_comem:
  !x l. ~(LFINITE l) ==> comem x l
Proof
  rw[] >>
  irule comem_coind >>
  qexists `\x l. ~(LFINITE l)` >>
  rw[] >>
  disj2_tac >>
  last_x_assum kall_tac >>
  fs[LFINITE_LNTH_NONE] >>
  Cases_on `a1`
  >- (
    first_x_assum $ qspec_then `0` mp_tac >>
    simp[]
  ) >>
  irule_at (Pos hd) EQ_REFL >>
  rw[] >>
  metis_tac[LNTH_THM]
QED

Inductive mem:
  (!x xs. mem x (x:::xs)) /\
  (!x y xs. mem x xs ==> mem x (y:::xs))
End

Theorem mem_not_mem:
  mem x l <=> ~(not_mem x l)
Proof
  eq_tac
  >- (
    qid_spec_tac `l` >>
    qid_spec_tac `x` >>
    ho_match_mp_tac mem_ind >>
    rw[]
    >- (
      strip_tac >>
      drule $ iffLR not_mem_cases >>
      simp[]
    ) >>
    strip_tac >>
    drule $ iffLR not_mem_cases >>
    simp[]
  ) >>
  CONV_TAC CONTRAPOS_CONV >>
  rw[] >>
  irule not_mem_coind >>
  qexists `\x l. ~(mem x l)` >>
  rw[] >>
  last_x_assum kall_tac >>
  Cases_on `a1` >>
  simp[] >>
  rpt strip_tac
  >- (
    last_x_assum mp_tac >>
    simp[] >>
    irule $ cj 2 mem_rules >>
    simp[]) >>
  last_x_assum mp_tac >>
  simp[] >>
  irule $ cj 1 mem_rules
QED

Triviality not_not_mem_single:
  ~(not_mem x [|x|])
Proof
  strip_tac >>
  drule $ iffLR not_mem_cases >>
  simp[]
QED

CoInductive allOdd:
  (!s x. allOdd s /\ ODD x ==> allOdd (x:::s)) /\
  allOdd [||]
End

Theorem allOddSingle:
  ODD x ==> allOdd [|x|]
Proof
  rw[] >>
  irule $ cj 1 allOdd_rules >>
  simp[] >>
  irule $ cj 2 allOdd_rules
QED

Theorem allOddAllOnes:
  allOdd ones
Proof
  irule allOdd_coind >>
  qexists `{ones}` >>
  simp[] >>
  disj1_tac >>
  irule_at (Pos hd) ones >>
  simp[]
QED

Definition inf_odds_def:
  inf_odds = LUNFOLD (\x. SOME (x + 2,x)) 1
End

Theorem allOdd_inf_odds:
  allOdd inf_odds
Proof
  irule allOdd_coind >>
  qexists `\x. ?y. ODD y /\ x = LUNFOLD (\x. SOME (x+2,x)) y` >>
  simp[inf_odds_def] >>
  conj_tac
  >- (
    irule_at (Pos last) EQ_REFL >>
    simp[]
  ) >>
  rw[] >>
  disj1_tac >>
  simp[Once $ LUNFOLD] >>
  irule_at (Pos last) EQ_REFL >>
  pop_assum mp_tac >>
  PURE_REWRITE_TAC[Once $ DECIDE``2 = SUC(SUC 0)``] >>
  PURE_REWRITE_TAC[GSYM $ ADD_SUC] >>
  PURE_REWRITE_TAC[ODD] >>
  simp[]
QED

