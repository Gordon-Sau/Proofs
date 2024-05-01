open HolKernel boolLib bossLib BasicProvers dep_rewrite;
open pred_setTheory relationTheory listTheory pairTheory;
open arithmeticTheory rich_listTheory;

val _ = new_theory "countableList";

Theorem EVERY_k_BIGUNION:
  EVERY P = BIGUNION (IMAGE (λk. {l | EVERY P l ∧ LENGTH l = k}) UNIV)
Proof
  rw[EXTENSION,EQ_IMP_THM,IN_DEF] >>
  gvs[] >>
  qexists `{l | EVERY P l ∧ LENGTH l = LENGTH x}` >>
  gvs[] >>
  qexists `LENGTH x` >> fs[]
QED

Theorem EVERY_SUC_k:
  {l | EVERY P l ∧ LENGTH l = SUC k} =
    IMAGE (UNCURRY CONS) (P × {l | EVERY P l ∧ LENGTH l = k})
Proof
  rw[EXTENSION] >>
  Cases_on `x` >>
  gvs[ELIM_UNCURRY] >>
  rw[EQ_IMP_THM,LAMBDA_PROD,GSYM PEXISTS_THM,IN_DEF]
QED

Theorem countable_EVERY:
  countable P ⇒
    countable (EVERY P)
Proof
  rw[Once EVERY_k_BIGUNION] >>
  irule bigunion_countable >>
  rw[IN_DEF] >>
  Induct_on `k`
  >- (
    irule subset_countable >>
    qexists `{[]}` >>
    simp[SUBSET_DEF] ) >>
  simp[EVERY_SUC_k]  >>
  metis_tac[cross_countable,image_countable]
QED

Theorem EVERY_T:
  EVERY (λx. T) = λl. T
Proof
  rw[FUN_EQ_THM]
QED

Theorem countable_list:
  countable (UNIV:'a set) ⇒
  countable (UNIV:'a list set)
Proof
  strip_tac >>
  drule countable_EVERY >>
  simp[UNIV_DEF,EVERY_T]
QED

Datatype:
  Rose = Node 'a (Rose list)
End

Theorem Rose_size_def = fetch "-" "Rose_size_def";

Definition rose_depth_def:
  rose_depth (Node _ rs) = 1 + FOLDR MAX 0 (MAP rose_depth rs)
Termination
  WF_REL_TAC `measure (Rose_size (K 0))`
End

Theorem UNIV_rose_BIGUNION:
  (UNIV:'a Rose set) = BIGUNION (IMAGE (λk. {r | rose_depth r = k}) UNIV)
Proof
  rw[EXTENSION,EQ_IMP_THM] >>
  qexists `{r | rose_depth r = rose_depth x}` >>
  simp[] >>
  metis_tac[]
QED

Theorem rose_depth_0:
  rose_depth r = 0 ⇔ F
Proof
  Cases_on `r` >> simp[rose_depth_def]
QED

Definition every_rose_def:
  every_rose P (Node x rs) = (P x ∧ EVERY (every_rose P) rs)
Termination
  WF_REL_TAC `measure (Rose_size (K 0) o SND)`
End

Theorem every_rose_k_BIGUNION:
  every_rose P = BIGUNION (IMAGE (λk. {r | every_rose P r ∧ rose_depth r ≤ k}) UNIV)
Proof
  rw[EXTENSION,EQ_IMP_THM,IN_DEF] >> gvs[] >>
  qexists `{r | every_rose P r ∧ rose_depth r ≤ rose_depth x}` >>
  gvs[] >>
  qexists `rose_depth x` >> fs[]
QED

Theorem FOLDR_MAX_MEM:
  ∀x xs. MEM x xs ⇒
    x ≤ FOLDR MAX 0 xs
Proof
  Induct_on `xs` >> rw[] >>
  rw[arithmeticTheory.LESS_EQ_REFL]
QED

Theorem FOLDR_MAX_LE:
  (∀x. MEM x xs ⇒ x ≤ k) ⇒
  FOLDR MAX 0 xs ≤ k
Proof
  Induct_on `xs` >> rw[]
QED

Theorem every_rose_SUC_k:
  {r | every_rose P r ∧ rose_depth r ≤ SUC k} =
    IMAGE (UNCURRY Node)
      (P × {l | EVERY (λr. every_rose P r ∧ rose_depth r ≤ k) l})
Proof
  rw[EXTENSION] >>
  qid_spec_tac `k` >>
  qid_spec_tac `x` >>
  ho_match_mp_tac rose_depth_ind >>
  rw[every_rose_def,rose_depth_def] >>
  rw[EQ_IMP_THM]
  >- (
    simp[LAMBDA_PROD,GSYM PEXISTS_THM,IN_DEF] >>
    simp[EVERY_MEM] >>
    rpt gen_tac >> strip_tac >>
    last_x_assum $ qspec_then `r` (strip_assume_tac o iffRL) >>
    gvs[PULL_EXISTS,ELIM_UNCURRY] >>
    gvs[LAMBDA_PROD,GSYM PFORALL_THM,arithmeticTheory.ADD1] >>
    gvs[EVERY_MEM] >>
    irule arithmeticTheory.LESS_EQ_TRANS >>
    last_assum $ irule_at (Pos last) >>
    irule FOLDR_MAX_MEM >>
    simp[MEM_MAP] >>
    metis_tac[]
  )
  >- (Cases_on `x'` >> gvs[IN_DEF])
  >- (
    Cases_on `x'` >>
    gvs[] >>
    drule_at_then Any irule MONO_EVERY >>
    rw[]
  )
  >- (
    Cases_on `x'` >>
    gvs[] >>
    simp[arithmeticTheory.ADD1] >>
    irule FOLDR_MAX_LE >>
    rw[MEM_MAP] >>
    gvs[EVERY_MEM]
  )
QED

Theorem countable_every_rose:
  countable P ⇒
  countable (every_rose P)
Proof
  rw[Once every_rose_k_BIGUNION] >>
  irule bigunion_countable >>
  rw[IN_DEF] >>
  Induct_on `k` >>
  simp[rose_depth_0,every_rose_SUC_k] >>
  DEP_REWRITE_TAC[cross_countable,image_countable] >>
  drule countable_EVERY >>
  simp[GSPEC_ETA] >>
  metis_tac[ETA_AX]
QED

Theorem every_rose_T:
  every_rose (λx. T) = λr. T
Proof
  simp[FUN_EQ_THM] >>
  `!P x. P = (λx. T) ⇒ every_rose P x` suffices_by gvs[] >>
  ho_match_mp_tac every_rose_ind >>
  rw[every_rose_def,EVERY_MEM]
QED

Theorem countable_rose:
  countable (UNIV:'a set) ⇒
  countable (UNIV:'a Rose set)
Proof
  strip_tac >>
  drule countable_every_rose >>
  simp[UNIV_DEF,every_rose_T]
QED

val _ = export_theory();
