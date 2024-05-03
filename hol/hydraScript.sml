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

Inductive Spawn:
[~head:]
  RemoveChildLeaf t t' ⇒
    Spawn (t::ts) (t'::(ts ++ REPLICATE n t'))
[~next:]
  Spawn ts ts' ⇒ Spawn (t::ts) (t::ts')
End

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

Inductive SimpleSpawn:
[~head:]
  RemoveChildLeaf t t' ⇒
    SimpleSpawn (t::ts) (t'::(ts ++ REPLICATE n Leaf))
[~next:]
  SimpleSpawn ts ts' ⇒ SimpleSpawn (t::ts) (t::ts')
End

Theorem Rose_size_def = fetch "-" "Rose_size_def";

(* while LLEX is not WF, I think LLEX on a sorted list should be WF *)
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
  cheat
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
* but I think it should be possible to do it without the induction
* by passing a list of depths and define the WF order on it *)
Theorem WF_Simple_Hydra:
  WF (flip $ GenericSpawnNode SimpleSpawn ∪ᵣRemoveChildLeaf)
Proof
  simp[flip_TC,WF_TC_EQN] >>
  irule WF_SUBSET >>
  qexists `inv_image (λl l'. SORTED $>= l ∧ SORTED $>= l' ∧ LLEX $< l l') Rose_depths` >>
  reverse conj_tac
  >- (
    irule WF_inv_image >>
    ntac 2 $ irule_at (Pos hd) WF_LEX >>
    simp[]) >>
  CONV_TAC SWAP_FORALL_CONV >>
  simp[RUNION,DISJ_IMP_THM,FORALL_AND_THM] >>
  cheat
QED

Theorem WF_Hydra:
  WF (flip $ GenericSpawnNode Spawn ∪ᵣRemoveChildLeaf)
Proof
  
QED

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
