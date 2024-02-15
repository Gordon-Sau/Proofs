open bossLib;

Theorem strong_induction:
  !P. ((!n. (!m. m < n ==> P m) ==> P n) ==> !n. P n)
Proof
  strip_tac >>
  qspec_then `\n. (!m. m < n ==> P m)` assume_tac numTheory.INDUCTION >>
  rpt strip_tac >>
  gvs[] >>
  first_x_assum irule >>
  rpt strip_tac >>
  first_x_assum drule >>
  simp[]
QED

Theorem least_exists_lemma:
  (!n. n < m ==> ~(P n)) \/ (?n. n < m /\ P n)
Proof
  Induct_on `m` >>
  gvs[]
  >- (
    Cases_on `P m`
    >- (
      disj2_tac >>
      qexists `m` >>
      gvs[]
    ) >>
    disj1_tac >>
    rpt strip_tac >>
    first_x_assum mp_tac >>
    simp[] >>
    Cases_on `n < m`
    >- (
      first_assum irule >>
      simp[] ) >>
    `n = m` by decide_tac >>
    gvs[]
  ) >>
  disj2_tac >>
  qexists `n` >>
  gvs[]
QED

Theorem least_exists:
  (?m. P m) ==>
  (?n. P n /\ !m. m < n ==> ~(P m))
Proof
  rpt strip_tac >>
  completeInduct_on `m` >>
  qspecl_then [`m`,`P`] assume_tac $ GEN_ALL least_exists_lemma >>
  rpt strip_tac >>
  gvs[]
  >- metis_tac[] >>
  first_x_assum drule >>
  gvs[]
QED

