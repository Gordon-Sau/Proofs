open HolKernel boolLib bossLib BasicProvers dep_rewrite;
open pred_setTheory relationTheory combinTheory pairTheory;
open arithmeticTheory prim_recTheory;
open listTheory rich_listTheory sortingTheory;

val _ = new_theory "hydra";

(* part of the ideas are inspired by
* "Hydra Battles in Coq" by Pierre Castéran
* https://www.labri.fr/perso/casteran/hydras.pdf *)

Datatype:
  Rose = Node (Rose list)
End

Overload Leaf = ``Node []``;

Inductive RemoveLeaf:
[~head:]
  RemoveLeaf (Leaf::rs) rs

[~next:]
  RemoveLeaf rs rs' ⇒ RemoveLeaf (r::rs) (r::rs')
End

Inductive RemoveChildLeaf:
  RemoveLeaf rs rs' ⇒
    RemoveChildLeaf (Node rs) (Node rs')
End

Theorem RemoveLeaf_append:
  RemoveLeaf (xs  ++ Leaf::rs) (xs ++ rs)
Proof
  Induct_on `xs` >> rw[] >>
  metis_tac[RemoveLeaf_rules]
QED

Theorem RemoveLeaf_exists_append:
  ∀rs rs'. RemoveLeaf rs rs' ⇒
  ∃xs y ys. rs = (xs  ++ Leaf::ys) ∧ rs' = (xs ++ ys)
Proof
  ho_match_mp_tac RemoveLeaf_ind >>
  rw[]
  >- (irule_at (Pos last) (GSYM $ cj 1 APPEND) >> simp[]) >>
  irule_at (Pos last) (GSYM $ cj 2 APPEND) >> simp[]
QED

(* KP hydra game (the real hydra game) *)
Inductive Spawn:
[~head:]
  RemoveChildLeaf t t' ⇒
    Spawn (t::ts) (t'::(ts ++ REPLICATE n t'))
[~next:]
  Spawn ts ts' ⇒ Spawn (t::ts) (t::ts')
End

(* a generic spwan relation that we can plug different spawn
* relation to it *)
Inductive GenericSpawnNode:
[~base:]
  spawn ts ts' ⇒
    GenericSpawnNode spawn (Node ts) (Node ts')

[~head:]
  GenericSpawnNode spawn t t' ⇒
    GenericSpawnNode_l spawn (t::ts) (t'::ts)

[~next:]
  GenericSpawnNode_l spawn ts ts' ⇒
    GenericSpawnNode_l spawn (t::ts) (t::ts')

[~node:]
  GenericSpawnNode_l spawn ts ts' ⇒
    GenericSpawnNode spawn (Node ts) (Node ts')
End

(* spawn function for the simple hydra game *)
Inductive SimpleSpawn:
[~head:]
  RemoveChildLeaf t t' ⇒
    SimpleSpawn (t::ts) (t'::(ts ++ REPLICATE n Leaf))
[~next:]
  SimpleSpawn ts ts' ⇒ SimpleSpawn (t::ts) (t::ts')
End

Theorem Rose_size_def = fetch "-" "Rose_size_def";

Theorem LLEX_REPLICATE:
  ∀n'' n'. LLEX $< (REPLICATE n'' m) (REPLICATE n' m) ⇒ n'' < n'
Proof
  Induct_on `n'` >>
  rw[] >>
  Cases_on `n''` >>
  fs[]
QED

Theorem forall_not_MEM:
  (!x. ¬MEM x l) ⇔ (l = [])
Proof
  rw[EQ_IMP_THM] >>
  Cases_on `l` >>
  gvs[] >>
  metis_tac[]
QED

Theorem SORTED_DROP:
  ∀cmp l n. SORTED cmp l ⇒ SORTED cmp (DROP n l)
Proof
  ho_match_mp_tac SORTED_IND >>
  rw[] >>
  Cases_on `n` >> simp[]
QED

Theorem transitive_flip:
  transitive (flip r) ⇒ transitive r
Proof
  simp[transitive_def] >>
  metis_tac[]
QED

Theorem LLEX_TAKE:
  LLEX R (TAKE n l) (TAKE n l') ⇒ LLEX R l l'
Proof
  once_rewrite_tac[LLEX_EL_THM] >>
  rw[] >>
  qexists `n'` >>
  gvs[LIST_EQ_REWRITE,LENGTH_TAKE_EQ,EL_TAKE]
QED

Theorem LLEX_DROP:
  TAKE n l = TAKE n l' ∧ LLEX R (DROP n l) (DROP n l') ⇒
  LLEX R l l'
Proof
  once_rewrite_tac[LLEX_EL_THM] >>
  rw[] >>
  qexists `n + n'` >>
  reverse $ gvs[LIST_EQ_REWRITE,EL_DROP,EL_TAKE,
    SUB_LEFT_LESS,SUB_LEFT_LESS_EQ]
  >- gvs[LENGTH_TAKE_EQ] >>
  rw[] >>
  Cases_on `n' = 0` >>
  gvs[] >>
  first_assum $ qspec_then `x - n` mp_tac >>
  PURE_REWRITE_TAC[SUB_LEFT_ADD] >>
  simp[] >>
  IF_CASES_TAC >>
  gvs[LESS_OR_EQ]
QED

Theorem LLEX_TAKE_DROP:
  ∀l'. LLEX R l l' ⇒
  (!n. n ≤ LENGTH l' ⇒  LLEX R (TAKE n l) (TAKE n l') ∨
    (TAKE n l = TAKE n l' ∧ LLEX R (DROP n l) (DROP n l')))
Proof
  Induct_on `l` >>
  rw[LLEX_def] >>
  Cases_on `l'` >> gvs[]
  >- (
    Cases_on `n = 0` >> simp[] >>
    disj1_tac >>
    simp[LLEX_EL_THM] >>
    qexists `0` >>
    simp[EL_TAKE]
  ) >>
  Cases_on `n` >>
  fs[] >>
  metis_tac[]
QED

Theorem LLEX_irreflexive:
  ∀l. (∀x. ¬R x x) ⇒ ¬LLEX R l l
Proof
  Induct_on `l` >>
  rw[]
QED

Theorem LLEX_LT_not_refl:
  ¬ LLEX $< x x
Proof
  irule LLEX_irreflexive >>
  simp[]
QED

Theorem transitive_GE:
  transitive $>=
Proof
  irule transitive_flip >>
  simp[C_DEF,GREATER_EQ] >>
  assume_tac transitive_LE >>
  pop_assum mp_tac >>
  ho_match_mp_tac $ cj 1 $ iffLR EQ_IMP_THM >>
  AP_TERM_TAC >>
  rw[FUN_EQ_THM]
QED

(* For simple hydra game, we compare a list of depths of the leaves using LLEX *)
(* while LLEX is proven to be not WF,
* LLEX on a sorted list in descending order should be WF.
* By induction on the integer that is in the head of a list 
* and is the least of all head?
*)
Theorem LLEX_BOUNDED_WF:
  ∀B.
    (∃w. B w) ∧
    (∀l. B l ⇒ SORTED $>= l) ∧
    (∀x l. B l ∧ MEM x l ⇒ x ≤ n) ⇒
      ∃l'. B l' ∧ ∀l. B l ⇒ ¬LLEX $< l l'
Proof
  Induct_on `n` >> rw[]
  >- (
    `∀l. B l ⇒ ∃n. l = REPLICATE n 0` by (
      rpt strip_tac >>
      irule_at (Pos hd) LIST_EQ >>
      simp[EL_REPLICATE] >>
      metis_tac[MEM_EL]) >>
    `∃m. (λm. ∃l'. B l' ∧ l' = REPLICATE m 0) m`
      by metis_tac[] >>
    dxrule_then (strip_assume_tac o
      SRULE[NOT_LESS,GSYM IMP_DISJ_THM]) $ 
      SRULE[PULL_EXISTS] whileTheory.LEAST_EXISTS_IMP >>
    metis_tac[LLEX_REPLICATE]) >>
  `∃m. (λm. ∃l'. B l' ∧ ∀x. MEM x (DROP m l') ⇒ x ≤ n) m`   
  by (
    simp[] >>
    last_x_assum $ irule_at (Pos hd) >>
    qexists `LENGTH w` >>
    simp[]) >>
  dxrule_then (strip_assume_tac o
      SRULE[NOT_LESS,GSYM IMP_DISJ_THM]) $ 
    SRULE[PULL_EXISTS] whileTheory.LEAST_EXISTS_IMP >>
  qmatch_asmsub_abbrev_tac `DROP least_m l'` >>
  first_x_assum $ qspec_then
    `(IMAGE (DROP least_m) B) ∩ (\l. ∀x. MEM x l ⇒ x ≤ n)`
    mp_tac >>
  simp[] >>
  impl_tac
  >- (
    conj_tac
    >- metis_tac[IN_DEF,LESS_IMP_LESS_OR_EQ] >>
    rw[PULL_EXISTS] >>
    metis_tac[SORTED_DROP,IN_DEF]) >>
  qpat_x_assum `B l'` kall_tac >>
  qpat_x_assum `!x. MEM x (DROP _ l') ⇒ _` kall_tac >>
  rw[PULL_EXISTS] >>
  qpat_x_assum `x ∈ B` $ assume_tac o SRULE[IN_DEF] >>
  qpat_x_assum `!x'. x' ∈ B ∧ _ ⇒ ~LLEX _ _ _` $
    assume_tac o SRULE[Once IN_DEF] >>
  `!l x. B l ∧ MEM x (TAKE least_m l) ⇒ n < x`
  by (
    rw[MEM_EL,PULL_EXISTS] >>
    fs[EL_TAKE,LENGTH_TAKE_EQ] >>
    `n' < least_m` by fs[] >>
    qpat_x_assum`!n'. n' < least_m ⇒ _` drule >>
    disch_then $ qspec_then `l` mp_tac >>
    rw[MEM_EL,PULL_EXISTS,NOT_LESS_EQUAL,SUB_LEFT_LESS] >>
    pop_assum mp_tac >>
    simp[EL_DROP] >>
    strip_tac >>
    drule_then irule LESS_LESS_EQ_TRANS >>
    last_x_assum drule >> 
    DEP_REWRITE_TAC[SORTED_EL_LESS] >>
    conj_tac
    >- simp[transitive_GE] >>
    Cases_on `n'' = 0` >>
    rw[GREATER_EQ]) >>
  first_assum $ irule_at (Pos hd) >>
  rw[] >>
  strip_tac >>
  drule_then strip_assume_tac LLEX_TAKE_DROP >>
  `least_m ≤ LENGTH x` by (
    irule $ iffLR NOT_LESS >>
    strip_tac >>
    qpat_x_assum `!n. n < least_m ⇒ _` drule >>
    rw[] >>
    qexists `x` >>
    rw[]) >>
  first_assum drule >>
  rw[]
  >- (
    simp[LLEX_EL_THM] >>
    simp[GSYM IMP_DISJ_THM,TAKE_TAKE,LENGTH_TAKE] >>
    rpt gen_tac  >>
    ntac 3 strip_tac >>
    conj_asm1_tac
    >- (
      qpat_x_assum `n' ≤ LENGTH (TAKE _ _)` $
        strip_assume_tac o SRULE[LESS_OR_EQ] >>
      gvs[LENGTH_TAKE_EQ] >>
      pop_assum mp_tac >>
      IF_CASES_TAC >>
      fs[NOT_LESS_EQUAL] >>
      qpat_x_assum `!n. n < least_m ⇒ _` $ drule_then drule >>
      rw[]) >>
    simp[EL_TAKE] >>
    strip_tac >>
    gvs[TAKE_TAKE] >>
    qpat_x_assum `!n. n < least_m ⇒ _` $ drule_then drule >>
    rw[NOT_LESS_EQUAL,GSYM IMP_DISJ_THM,MEM_EL,SUB_LEFT_LESS] >>
    simp[EL_DROP] >>
    last_x_assum drule >>
    last_x_assum $ qspecl_then [`EL n' x`,`x`] mp_tac >>
    simp[MEM_EL,EL_DROP,PULL_EXISTS] >>
    disch_then $ qspec_then `n'` mp_tac >>
    simp[] >>
    DEP_REWRITE_TAC[SORTED_EL_LESS] >>
    rw[GREATER_EQ,transitive_GE] >>
    irule LESS_EQ_TRANS >>
    `EL n' l ≤ n` by fs[] >>
    first_assum $ irule_at (Pos last) >>
    Cases_on `n'' = 0` >> simp[]
  ) >>
  first_assum irule >>
  rw[MEM_EL,SUB_LEFT_LESS] >>
  rw[EL_DROP] >>
  first_x_assum drule >>
  rw[LLEX_LT_not_refl] >>
  pop_assum mp_tac >>
  reverse $ rw[LLEX_EL_THM,SUB_LEFT_LESS,SUB_LEFT_LESS_EQ,
    EL_DROP]
  >- (
    fs[] >>
    pop_assum mp_tac >>
    impl_tac >> fs[] >>
    qpat_x_assum `!x'. MEM x' (DROP least_m x) ⇒ _` $
      qspec_then `HD (DROP least_m x)` mp_tac >>
    simp[MEM_EL,SUB_LEFT_LESS,PULL_EXISTS] >>
    disch_then $ qspec_then `0` mp_tac >>
    simp[] >>
    rpt strip_tac >>
    irule LESS_EQ_TRANS >>
    first_assum $ irule_at (Pos last) >>
    irule LESS_IMP_LESS_OR_EQ >>
    irule LESS_EQ_LESS_TRANS >>
    first_assum $ irule_at (Pos hd) >>
    qpat_x_assum `!l. _ ⇒ SORTED $>= l` $
      qspec_then `l` mp_tac >>
    simp[] >>
    DEP_REWRITE_TAC[SORTED_EL_LESS] >>
    simp[GREATER_EQ,transitive_GE] >>
    Cases_on `n'` >> simp[] >>
    disch_then irule >>
    simp[]
  ) >>
  qpat_x_assum `least_m + n'' ≤ LENGTH l` $ 
    strip_assume_tac o SRULE[LESS_OR_EQ]
  >- (
    fs[LIST_EQ_REWRITE,EL_TAKE,EL_DROP] >>
    Cases_on `n' < n''`
    >- (
      first_assum drule >>
      simp[EL_DROP] >>
      last_assum irule >>
      simp[MEM_EL,SUB_LEFT_LESS] >>
      qexists `n'` >>
      simp[EL_DROP]) >>
    Cases_on `n' = n''`
    >- (
      gvs[EL_DROP] >>
      irule LESS_IMP_LESS_OR_EQ >>
      irule LESS_LESS_EQ_TRANS >>
      last_assum $ irule_at (Pos last) >>
      first_assum $ irule_at (Pos last) >>
      simp[MEM_EL,SUB_LEFT_LESS] >>
      qexists `n'` >>
      simp[EL_DROP]) >>
    `n'' < n'` by fs[] >>
    gvs[EL_DROP] >>
    irule LESS_IMP_LESS_OR_EQ >>
    irule LESS_LESS_EQ_TRANS >>
    last_assum $ irule_at (Pos last) >>
    simp[MEM_EL,PULL_EXISTS,SUB_LEFT_LESS] >>
    irule_at (Pos last) LESS_EQ_LESS_TRANS >>
    first_assum $ irule_at (Pos last) >>
    simp[EL_DROP] >>
    first_assum $ irule_at (Pos last) >>
    qpat_x_assum `!l. B l ⇒ SORTED _ _` $ qspec_then `l` mp_tac >>
    simp[] >>
    DEP_REWRITE_TAC[SORTED_EL_LESS,transitive_GE] >>
    simp[GREATER_EQ]
  ) >>
  gvs[LIST_EQ_REWRITE,EL_TAKE,EL_DROP] >>
  last_assum $ irule_at (Pos last) >>
  simp[MEM_EL,SUB_LEFT_LESS] >>
  irule_at (Pos hd) LESS_TRANS >>
  first_assum $ irule_at (Pos $ el 2) >>
  first_assum $ irule_at (Pos hd) >>
  simp[EL_DROP]
QED

(* This can probably be generalized *)
Theorem LLEX_SORTED_WF:
  WF (λl l'. SORTED $>= l ∧ SORTED $>= l' ∧ LLEX $< l l')
Proof
  rw[WF_DEF,PULL_EXISTS] >>
  Cases_on `∃l. B l ∧ ¬SORTED $>= l`
  >- (rw[] >> qexists `l` >> simp[]) >>
  pop_assum mp_tac >> rw[GSYM IMP_DISJ_THM] >>
  `∃l'. B l' ∧ ∀l. B l ⇒ ¬LLEX $< l l'` suffices_by (
    rw[] >>
    first_assum $ irule_at (Pos hd) >> rw[] >>
    metis_tac[]) >>
  Cases_on `B []`
  >- (first_assum $ irule_at (Pos hd) >> simp[]) >>
  `!l. B l ⇒ ?x xs. l = x::xs` by (
    rw[] >>
    Cases_on `l` >> fs[]) >>
  `?h. (λh. ∃tl. B (h::tl)) h` by (simp[] >> metis_tac[]) >>
  dxrule_then (strip_assume_tac o
    SRULE[NOT_LESS,GSYM IMP_DISJ_THM]) $ 
    SRULE[PULL_EXISTS] whileTheory.LEAST_EXISTS_IMP >>
  qmatch_asmsub_abbrev_tac `B (least_h::tl)` >>
  qspecl_then [`least_h`,`B ∩ (λl. ∃tl. l = least_h::tl )`]
    mp_tac $ GEN_ALL LLEX_BOUNDED_WF >>
  impl_tac
  >- (
    conj_tac
    >- (rw[IN_DEF] >> metis_tac[]) >>
    conj_tac
    >- rw[IN_DEF] >>
    rw[Once IN_DEF] >>
    last_x_assum drule >>
    DEP_REWRITE_TAC[SORTED_EL_LESS] >>
    rw[transitive_GE,GREATER_EQ] >>
    fs[MEM_EL] >>
    first_x_assum $ qspecl_then [`0`,`SUC n`] mp_tac >>
    simp[]
  ) >>
  rw[] >>
  qpat_x_assum `_ ∈ B` $ assume_tac o SRULE[IN_DEF] >>
  qpat_x_assum `!l. l ∈ B /\ _ ⇒ _` $
    strip_assume_tac o SRULE[IN_DEF,PULL_EXISTS] >>
  first_assum $ irule_at (Pos hd) >>
  rw[] >>
  qpat_x_assum `!l. B l ⇒ ?x xs. l = x::xs` $
    drule_then strip_assume_tac >>
  fs[] >>
  reverse $ rw[] >- metis_tac[] >>
  strip_tac >>
  metis_tac[]
QED

Definition Rose_depths_def:
  Rose_depths_l ts = FLAT (MAP Rose_depths ts) ∧

  Rose_depths (Node []) = [1n] ∧
  Rose_depths (Node ts) =
    MAP ($+ 1) $ Rose_depths_l ts
Termination
  WF_REL_TAC `measure 
    (λt. case t of
    | INL ts => Rose1_size ts
    | INR n => Rose_size n)`
End

Triviality flip_flip:
  flip (flip R) = R
Proof
  rw[FUN_EQ_THM]
QED

(*
(* not used *)
Triviality flip_TC_lem:
  ∀x x'. (flip R)⁺ x x' ⇒ R⁺ x' x
Proof
  ho_match_mp_tac TC_INDUCT >>
  rw[]
  >- metis_tac[cj 1 TC_RULES]
  >- metis_tac[cj 2 TC_RULES]
QED

Theorem flip_TC:
  flip (TC R) = TC (flip R)
Proof
  rw[FUN_EQ_THM,EQ_IMP_THM,flip_TC_lem] >>
  irule flip_TC_lem >>
  simp[flip_flip]
QED
*)

Theorem QSORT_SORTED_GE:
  SORTED $>= (QSORT $>= l)
Proof
  irule QSORT_SORTED >>
  simp[transitive_GE,total_def]
QED

Theorem SimpleSpawnNode_Rose_depths:
  (∀ys xs.
    GenericSpawnNode_l SimpleSpawn ys xs ⇒
      _ (Rose_depths_l xs) (Rose_depths_l ys)) ∧
  (∀y x.
    GenericSpawnNode SimpleSpawn y x ⇒
      _ (Rose_depths x) (Rose_depths y))
Proof
  ho_match_mp_tac GenericSpawnNode_ind >>
  rw[Rose_depths_LEX_LT] >>
  cheat
QED

(* https://en.wikipedia.org/wiki/Hydra_game#Introduction
* The proof described in wiki is do an induction on the depth
* but it should be possible to do it without the induction
* by passing a list of depths and define the WF order on it *)
Theorem WF_Simple_Hydra:
  WF (flip $ GenericSpawnNode SimpleSpawn ∪ᵣRemoveChildLeaf)
Proof
  irule WF_SUBSET >>
  qexists `inv_image
    (λl l'. SORTED $>= l ∧ SORTED $>= l' ∧ LLEX $< l l')
    ((QSORT $>=) o Rose_depths)` >>
  reverse conj_tac
  >- (
    irule WF_inv_image >>
    irule LLEX_SORTED_WF) >>
  CONV_TAC SWAP_FORALL_CONV >>
  simp[RUNION,DISJ_IMP_THM,FORALL_AND_THM,QSORT_SORTED_GE] >>
  cheat
QED

(* The standard way to prove termination is to map each 
* hydra to an ordinal, and show that the ordinal decreases *)
(* Instead, I am trying to prove that 
* the hydra game relation is a subset of `Rose_cmp`,
* and prove that `Rose_cmp` is WF *)
(* Rose_cmp l r compares two rose trees,
* if r is greater (taller) then l, then it returns T *)
(* TODO *)
Definition Rose_cmp_def:
  Rose_cmp (Node []) (Node []) = F ∧
  Rose_cmp (Node []) (Node (t::ts)) = T ∧
  Rose_cmp (Node (t::ts)) (Node (t'::ts')) =
  (* use the `LLEX on sorted list` idea *)
  LLEX Rose_cmp
    (QSORT (λx y. Rose_cmp y x ∨ x = y) (t::ts))
    (QSORT (λx y. Rose_cmp y x ∨ x = y) (t'::ts'))
Termination
  cheat
End

Theorem WF_Rose_cmp:
  WF Rose_cmp
Proof
  cheat
QED

Theorem WF_Hydra:
  WF (flip $ GenericSpawnNode Spawn ∪ᵣRemoveChildLeaf)
Proof
  cheat
QED

(* not useful, but having this means that 
* once we have proven a WF (flip Rose_cmp),
* we can use `the_measure` next time to get a measure, 
* which is easy to think about *)
Definition the_measure_def:
  the_measure R x =
  if WF R ∧ FINITE {y | R y x}
  then
    MAX_SET (IMAGE (the_measure R) {y | R y x}) + 1
  else 0
Termination
  qexists `\y x. FST y = FST x ∧ WF (FST x) ∧ (FST x) (SND y) (SND x)` >>
  simp[] >>
  qspecl_then [`WF`,`FST`,`I`,`SND`] irule WF_PULL >>
  rw[]
End

Theorem the_measure_positive:
  WF R ∧ (∀x. FINITE {y | R y x}) ⇒ ∀x. 0 < the_measure R x
Proof
  strip_tac >>
  `!R' x. R' = R ==> 0 < the_measure R x` suffices_by rw[] >>
  ho_match_mp_tac the_measure_ind >>
  rw[] >>
  gvs[] >>
  simp[Once the_measure_def]
QED

Theorem the_measure_LT:
  WF R ∧ FINITE {y | R y x} ==> R y x ⇒ the_measure R y < the_measure R x
Proof
  rw[] >>
  PURE_REWRITE_TAC[GSYM arithmeticTheory.GREATER_DEF] >>
  simp[Once the_measure_def] >>
  simp[arithmeticTheory.GREATER_DEF,GSYM LE_LT1] >>
  irule in_max_set >>
  simp[]
QED

val _ = export_theory();
