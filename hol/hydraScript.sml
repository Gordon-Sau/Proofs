open HolKernel boolLib bossLib BasicProvers dep_rewrite;
open pred_setTheory relationTheory listTheory pairTheory;
open rich_listTheory;

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

Inductive RemoveRootLeaf:
  RemoveLeaf rs rs' ⇒
    RemoveRootLeaf (Node rs) (Node rs')
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
  RemoveRootLeaf t t' ⇒
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
  RemoveRootLeaf t t' ⇒
    SimpleSpawn (t::ts) (t'::(ts ++ REPLICATE n Leaf))
[~next:]
  SimpleSpawn ts ts' ⇒ SimpleSpawn (t::ts) (t::ts')
End

Theorem Rose_size_def = fetch "-" "Rose_size_def";

Definition default_EL_def:
  default_EL d n l = if n < LENGTH l then EL n l else d
End

Overload EL0 = ``default_EL 0``;

Definition LEX_LIST_def:
  LEX_LIST cmp z (x::xs) (y::ys) =
    (cmp x y ∨ (x = y ∧ LEX_LIST cmp z xs ys)) ∧
  LEX_LIST cmp z [] (y::ys) = cmp z y ∧
  LEX_LIST cmp z (x::xs) [] = cmp x z ∧
  LEX_LIST cmp z _ _ = F
End

Definition Rose_depth_count_def:
  Rose_depth_count_l ts = FLAT (MAP Rose_depth_count ts) ∧

  Rose_depth_count (Node []) = [1n] ∧
  Rose_depth_count (Node ts) =
    MAP ($+ 1) $ Rose_depth_count_l ts
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

Theorem Rose_depth_count_positive:
  (∀(ts:Rose list). EVERY (λx. 0 < x) (Rose_depth_count_l ts)) ∧ 
  (∀(t:Rose). EVERY (λx. 0 < x) (Rose_depth_count t))
Proof
  ho_match_mp_tac Rose_depth_count_ind >>
  rw[Rose_depth_count_def] >>
  simp[EVERY_FLAT,EVERY_MAP,EVERY_MEM]
QED

Theorem LEX_FST_SND:
  (f LEX g) p q ⇔ f (FST p) (FST q) ∨ (FST p = FST q ∧ g (SND p) (SND q))
Proof
  Cases_on `p` >>
  Cases_on `q` >>
  simp[LEX_DEF]
QED


Theorem SimpleSpawnNode_Rose_depth_count:
  (∀ys xs.
    GenericSpawnNode_l SimpleSpawn ys xs ⇒
      _ (Rose_depth_count_l xs) (Rose_depth_count_l ys)) ∧
  (∀y x.
    GenericSpawnNode SimpleSpawn y x ⇒
      _ (Rose_depth_count x) (Rose_depth_count y))
Proof
  ho_match_mp_tac GenericSpawnNode_ind >>
  rw[Rose_depth_count_LEX_LT] >>
  >- cheat
  simp[
QED

Theorem WF_Simple_Hydra:
  WF (flip $ GenericSpawnNode SimpleSpawn ∪ᵣRemoveRootLeaf)
Proof
  simp[flip_TC,WF_TC_EQN] >>
  irule WF_SUBSET >>
  qexists `inv_image _ Rose_depth_count` >>
  reverse conj_tac
  >- (
    irule WF_inv_image >>
    ntac 2 $ irule_at (Pos hd) WF_LEX >>
    simp[]) >>
  CONV_TAC SWAP_FORALL_CONV >>
  simp[RUNION,DISJ_IMP_THM,FORALL_AND_THM] >>
  conj_tac
QED


val _ = export_theory();
