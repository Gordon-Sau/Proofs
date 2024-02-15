open bossLib pred_setTheory relationTheory combinTheory optionTheory;
open arithmeticTheory;

Definition Least_def:
  Least P = @n. (P n /\ (!m. m < n ==> ~P m))
End

Definition WhileNot_def:
  WhileNot P g x = if ?n. P (FUNPOW g n x)
                then FUNPOW g (Least (\n. P (FUNPOW g n x))) x
                else ARB
End

Triviality P_FUNPOW_0:
  P x <=> P (FUNPOW g 0 x)
Proof
  simp[FUNPOW]
QED

Triviality P_FUNPOW_SUC:
  P (FUNPOW g (SUC n) x) <=> P (FUNPOW g n (g x))
Proof
  simp[FUNPOW]
QED

Theorem exists_Least_lem:
  !x. (?n. P n /\ (!m. m < n ==> ~P m)) \/ (!n. n <= x ==> ~P n)
Proof
  Induct_on `x` >>
  rw[]
  >- (
    Cases_on `P 0` >> rw[] >>
    qexists `0` >>
    simp[]
  )
  >- (
    disj1_tac >>
    metis_tac[]
  ) >>
  Cases_on `P (SUC x)`
  >- (
    disj1_tac >>
    metis_tac[LT_SUC_LE]
  ) >>
  disj2_tac >>
  rw[] >>
  Cases_on `n = SUC x` >>
  simp[]
QED

Theorem exists_Least:
  P n ==> ?x. P x /\ (!m. m < x ==> ~P m)
Proof
  rw[] >>
  assume_tac exists_Least_lem >>
  first_x_assum $ qspec_then `n` assume_tac >>
  gvs[] >>
  metis_tac[]
QED

Theorem Least_unique:
  P n /\ P m /\ (!x. x < n ==> ~P x) /\ (!x. x < m ==> ~P x) ==>
  n = m
Proof
  Cases_on `n < m`
  >- metis_tac[] >>
  Cases_on `n = m`
  >- metis_tac[] >>
  `m < n` by DECIDE_TAC >>
  metis_tac[]
QED

Theorem WhileNot:
  WhileNot P g x = if P x then x else WhileNot P g (g x)
Proof
  simp[WhileNot_def]
  \\ reverse IF_CASES_TAC
  >- metis_tac[FUNPOW]
  \\ reverse IF_CASES_TAC
  >- (
    reverse IF_CASES_TAC
    >- (
      spose_not_then kall_tac >>
      first_x_assum mp_tac >>
      rw[] >>
      Cases_on `n` >>
      fs[FUNPOW] >>
      metis_tac[]
    )
    \\ `Least (\n. P (FUNPOW g n x)) =
        SUC (Least (\n. P (FUNPOW g n (g x))))`
      suffices_by simp[FUNPOW]
    \\ rw[Least_def]
    \\ SELECT_ELIM_TAC
    \\ rw[]
    >- (
      ho_match_mp_tac (GEN_ALL exists_Least) >>
      metis_tac[]
    ) >>
    Cases_on `x'` >>
    gvs[FUNPOW] >>
    SELECT_ELIM_TAC >>
    rw[]
    >- (
      ho_match_mp_tac (GEN_ALL exists_Least) >>
      metis_tac[]
    ) >>
    `SUC n'' = SUC x'` suffices_by simp[] >>
    irule Least_unique >>
    qexists `\n. P (FUNPOW g n x)` >>
    rw[FUNPOW] >>
    Cases_on `x''` >>
    gvs[FUNPOW]
  )
  \\ `Least (\n. P (FUNPOW g n x)) = 0`
  by (
    simp[Least_def]
    \\ SELECT_ELIM_TAC
    \\ rw[]
    >- (qexists `0` >> simp[FUNPOW])
    \\ Cases_on `x'`
    \\ simp[]
    \\ first_x_assum $ qspec_then `0` assume_tac
    \\ fs[FUNPOW])
  \\ simp[]
QED

Theorem WF_INDUCTION_THM:
  WF R ==>
    !P. (!x. (!y. R y x ==> P y) ==> P x) ==> !z. P z
Proof
  rw[WF_DEF] >>
  first_x_assum $ qspec_then `\x. ~(P x)` assume_tac >>
  fs[PULL_EXISTS] >>
  Cases_on `P z` >>
  simp[] >>
  first_x_assum drule >>
  rw[] >>
  Cases_on `P min` >>
  simp[] >>
  spose_not_then assume_tac >>
  first_x_assum drule >>
  simp[]
QED

Theorem While_Induction:
  WF R /\ (!s. B s ==> R (c s) s)
    ==> !P. (!s. (B s ==> P (c s)) ==> P s) ==> !v. P v
Proof
  rw[] >>
  dxrule_then irule WF_INDUCTION_THM >>
  rpt strip_tac >>
  last_x_assum irule >>
  strip_tac >>
  first_x_assum irule >>
  first_x_assum irule >>
  first_x_assum irule
QED
