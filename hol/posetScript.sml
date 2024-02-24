(* ========================================================================= *)
(* Create "posetTheory" for reasoning about arbitrary partial orders.        *)
(* Originally created by Joe Hurd to support the pGCL formalization.         *)
(* ========================================================================= *)

open HolKernel Parse boolLib bossLib BasicProvers dep_rewrite;
open pairTheory pred_setTheory combinTheory;

val _ = new_theory "proset";

(* ------------------------------------------------------------------------- *)
(* Helpful proof tools                                                       *)
(* ------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------- *)
(* Functions from one predicate to another                                   *)
(* NOTE: this is actually pred_setTheory.FUNSET                              *)
(* ------------------------------------------------------------------------- *)

val function_def = new_definition
  ("function_def",
   ``function a b (f : 'a -> 'b) = !x. a x ==> b (f x)``);

(* ------------------------------------------------------------------------- *)
(* A HOL type of partial orders                                              *)
(* ------------------------------------------------------------------------- *)
Type proset[pp] = “:('a -> bool) # ('a -> 'a -> bool)”

(* ------------------------------------------------------------------------- *)
(* Definition of partially-ordered sets                                      *)
(* ------------------------------------------------------------------------- *)
Definition refl_def:
  refl (s,r) ⇔ (∀x. s x ⇒ r x x)
End

Definition trans_def:
  trans (s,r) ⇔
  (∀x y z. s x ∧ s y ∧ s z ∧ r x y ∧ r y z ⇒ r x z)
End

Definition proset_def:
  proset (s,r) ⇔ refl (s,r) ∧ trans (s,r)
End

val carrier_def = new_definition
  ("carrier_def",
   ``carrier ((s,r) : 'a proset) = s``);

val relation_def = new_definition
  ("relation_def",
   ``relation ((s,r) : 'a proset) = r``);

val _ = export_rewrites ["carrier_def", "relation_def"];

Definition weq_def:
  weq (s,r) x y ⇔ (s x ∧ s y ∧ r x y ∧ r y x)
End

Definition sym_def:
  sym (s,r) ⇔ (∀x y. s x ∧ s y ∧ r x y ⇒ r y x)
End

Theorem weq_sym:
  sym (s,weq (s,r))
Proof
  rw[weq_def,sym_def]
QED

Theorem weq_equiv:
  proset (s,r) ⇒
  refl (s,weq (s,r)) ∧
  sym (s,weq (s,r)) ∧
  trans (s,weq (s,r))
Proof
  rw[refl_def,weq_def,weq_sym,trans_def,proset_def] >>
  metis_tac[]
QED

Theorem refl_SUBSET:
  refl (p,r) ∧
  s SUBSET p ⇒
  refl (s,r)
Proof
  simp[refl_def,SRULE[IN_DEF]SUBSET_DEF]
QED

Theorem weq_SUBSET:
  weq (s,r) x y ∧
  s ⊆ p ==>
  weq (p,r) x y
Proof
  simp[weq_def,SRULE[IN_DEF]SUBSET_DEF]
QED

Theorem trans_SUBSET:
  trans (p,r) ∧ s ⊆ p ⇒
  trans (s,r)
Proof
  rw[trans_def,SRULE[IN_DEF]SUBSET_DEF] >>
  metis_tac[]
QED

Theorem proset_SUBSET:
  proset (p,r) ∧ s ⊆ p ⇒
  proset (s,r)
Proof
  metis_tac[proset_def,trans_SUBSET,refl_SUBSET]
QED

Definition greatest_def:
  greatest s r x ⇔ s x ∧ (!y. s y ⇒ r y x)
End

Definition glb_def:
  glb (p,r) s x ⇔ greatest (\z. p z ∧ !y. p y ∧ s y ⇒ r z y) r x
End

Theorem glb_simp = SRULE[greatest_def] glb_def

Theorem greatest_weq:
  greatest s r x ∧ greatest s r y ⇒
  weq (s,r) x y
Proof
  rw[greatest_def] >>
  `r x y` by metis_tac[] >>
  `r y x` by metis_tac[] >>
  fs[weq_def]
QED

Theorem glb_weq:
  glb p s x ∧ glb p s y ⇒
  weq p x y
Proof
  simp[oneline glb_def] >>
  CASE_TAC >>
  strip_tac >>
  rev_drule_then drule greatest_weq >>
  simp[weq_def]
QED

Definition least_DEF:
  least s r x ⇔ greatest s (flip r) x
End

Theorem least_def = SRULE[greatest_def,C_DEF] least_DEF

Theorem least_alt = least_DEF

Theorem flip_flip[simp]:
  flip (flip r) = r
Proof
  simp[C_DEF] >>
  metis_tac[]
QED

Theorem greatest_alt:
  !s r x. greatest s r x ⇔ least s (flip r) x
Proof
  rw[least_DEF]
QED

Definition lub_def:
  lub (p,r) s x ⇔ least (\z. p z ∧ !y. p y ∧ s y ⇒ r y z) r x
End

Theorem lub_alt:
  lub (p,r) = glb (p,flip r)
Proof
  simp[FUN_EQ_THM,glb_def,lub_def,least_alt]
QED

Theorem lub_simp = SRULE[glb_simp,FUN_EQ_THM] lub_alt

Theorem lub_IN:
  lub (p,r) s l ⇒ p l
Proof
  simp[lub_simp]
QED

Theorem leq_lub:
  lub (p,r) s l ∧ p y ∧ s y ⇒
  r y l
Proof
  simp[lub_simp]
QED

Theorem leq_trans_lub:
  lub (p,r) s l ∧ trans (p,r) ∧
  p y ∧ p z ∧ s z ∧ r y z ⇒
  r y l
Proof
  rw[trans_def] >>
  last_x_assum irule >>
  drule lub_IN >>
  rw[] >>
  first_x_assum $ irule_at (Pos $ el 2) >>
  metis_tac[leq_lub]
QED

Theorem lub_leq:
  lub (p,r) s l ∧ p y ∧ (∀x. p x ∧ s x ⇒ r x y) ⇒ r l y
Proof
  simp[lub_simp]
QED

Theorem lub_leq_simp:
  lub (p,r) s l ∧ trans (p,r) ∧ p z ⇒
  (r l z ⇔ (∀x. p x ∧ s x ⇒ r x z))
Proof
  rw[EQ_IMP_THM]
  >- (
    drule_then assume_tac lub_IN >>
    drule_all_then assume_tac leq_lub >>
    drule_then irule $ iffLR trans_def >>
    metis_tac[]
  ) >>
  metis_tac[lub_leq]
QED

Theorem lub_leq_def:
  proset (p,r) ==>
  (lub (p,r) s l ⇔ (p l ∧ ∀z. p z ⇒ (r l z ⇔ (∀y. p y ∧ s y ⇒ r y z))))
Proof
  rw[EQ_IMP_THM,proset_def]
  >- metis_tac[lub_IN]
  >- (
    drule_then irule $ iffLR trans_def >>
    simp[] >>
    first_assum $ irule_at (Pos last) >>
    simp[] >>
    conj_tac >- fs[lub_simp] >>
    metis_tac[leq_lub])
  >- (drule_then irule lub_leq >> rw[]) >>
  rw[lub_simp] >>
  last_x_assum $ rev_drule_then $ assume_tac o cj 1 >>
  metis_tac[refl_def]
QED

Theorem refl_flip:
  refl (p,r) ⇒
  refl (p,flip r)
Proof
  simp[refl_def]
QED

Theorem forall_flip:
  (!r. P (flip r)) <=> (!r. P r)
Proof
  iff_tac >>
  rw[] >>
  metis_tac[flip_flip]
QED

Theorem weq_flip:
  weq (p,flip r) = weq (p,r)
Proof
  rw[weq_def,EQ_IMP_THM,FUN_EQ_THM]
QED

Theorem trans_flip:
  trans (p,r) ⇒
  trans (p,flip r)
Proof
  simp[trans_def] >>
  metis_tac[]
QED

Theorem IMP_proset_flip:
  proset (p,r) ⇒
  proset (p,flip r)
Proof
  metis_tac[proset_def,refl_flip,trans_flip]
QED

Theorem proset_flip:
  proset (p,flip r) ⇔ proset (p,r)
Proof
  metis_tac[IMP_proset_flip,flip_flip]
QED

Theorem least_weq:
  least s r x ∧ least s r y ⇒
  weq (s,r) x y
Proof
  rw[least_alt] >>
  metis_tac[greatest_weq,weq_flip]
QED

Theorem lub_weq:
  lub p s x ∧ lub p s y ⇒
  weq p x y
Proof
  Cases_on`p` >>
  rw[lub_alt] >>
  metis_tac[glb_weq,weq_flip]
QED

Theorem glb_alt:
  glb (p,r) = lub (p,flip r)
Proof
  simp[lub_alt]
QED

Theorem greatest_IFF_upper_bound:
  s ⊆ p ⇒
  (greatest s r x ⇔ s x ∧ (!y. s y ⇒ r y x))
Proof
  rw[greatest_def,SUBSET_DEF,IN_DEF] >>
  metis_tac[]
QED

Theorem greatest_IMP_lub:
  greatest s r x ∧
  s ⊆ p ⇒
  lub (p,r) s x
Proof
  strip_tac >>
  last_x_assum mp_tac >>
  drule_then (fn t => rw[t,lub_simp]) 
    greatest_IFF_upper_bound >>
  fs[SUBSET_DEF,IN_DEF]
QED

Theorem least_IFF_lower_bound:
  s ⊆ p ⇒
  (least s r x ⇔ s x ∧ (!y. s y ⇒ r x y))
Proof
  qid_spec_tac `r` >>
  simp[Once $ GSYM forall_flip] >>
  rw[GSYM greatest_alt] >>
  drule_then irule greatest_IFF_upper_bound
QED

Theorem least_IMP_glb:
  least s r x ∧ s SUBSET p ⇒
  glb (p,r) s x
Proof
  strip_tac >>
  last_x_assum mp_tac >>
  drule_then (fn t => rw[t,glb_simp])
    least_IFF_lower_bound >>
  fs[SUBSET_DEF,IN_DEF]
QED

Theorem lub_EQ_glb_lower_bound:
  lub (p,r) s =
    glb (p,r) (\z. p z ∧ !y. p y ∧ s y ⇒ r y z)
Proof
  rw[FUN_EQ_THM,EQ_IMP_THM] >>
  fs[lub_def,least_alt,glb_def,greatest_def]
QED

Theorem glb_EQ_lub_upper_bound:
  glb (p,r) s =
    lub (p,r) (\z. p z ∧ ∀y. p y ∧ s y ⇒ r z y)
Proof
  simp[lub_alt] >>
  simp[Once glb_alt] >>
  simp[Once lub_EQ_glb_lower_bound]
QED

Definition complete_def:
  complete (p : 'a proset) =
    ∀c. (∃x. lub p c x) ∧ (∃x. glb p c x) 
End

Theorem complete:
  complete p = ∀c. ∃x. lub p c x
Proof
  rw[complete_def,EQ_IMP_THM] >>
  simp[oneline glb_EQ_lub_upper_bound] >>
  CASE_TAC >>
  metis_tac[]
QED

Definition weak_complete_def:
  weak_complete (s,r) =
    ∀c. c ⊆ s ⇒ (∃x. lub (s,r) c x) ∧ (∃x. glb (s,r) c x) 
End

Theorem weak_complete:
  weak_complete (s,r) ⇔ (∀c. c ⊆ s ⇒ ∃x. lub (s,r) c x)
Proof
  rw[weak_complete_def,EQ_IMP_THM] >>
  simp[glb_EQ_lub_upper_bound] >>
  last_x_assum ho_match_mp_tac >>
  fs[SUBSET_DEF,IN_DEF]
QED

Definition complete_lattice_def:
  complete_lattice p ⇔ proset p ∧ complete p
End

Theorem complete_IMP_weak_complete:
  complete (s,r) ⇒ weak_complete (s,r)
Proof
  simp[weak_complete,complete]
QED

Theorem weak_complete_IMP_complete:
  weak_complete (s,r) ⇒ complete (s,r)
Proof
  rw[weak_complete,complete] >>
  first_assum $ qspec_then `c INTER s` assume_tac o SRULE[] >>
  fs[lub_simp,SUBSET_DEF,IN_DEF] >>
  qexists `x` >>
  rw[]
QED

Definition top_def:
   top (s,r) x <=> s x /\ !y. s y ==> r y x
End

Definition bot_def:
  bot (s,r) x <=> s x /\ !y. s y ==> r x y
End

Theorem top_glb:
  top (s,r) x ⇔ glb (s,r) EMPTY x
Proof
  simp[glb_simp,top_def]
QED

Theorem top_lub:
  top (s,r) x ⇔ lub (s,r) s x
Proof
  simp[lub_simp,top_def] >>
  iff_tac >>
  simp[]
QED

Theorem bot_top:
  bot (s,r) x ⇔ top (s,flip r) x
Proof
  simp[bot_def,top_def]
QED

Theorem top_bot:
  top (s,r) x ⇔ bot (s,flip r) x
Proof
  simp[bot_def,top_def]
QED

Theorem bot_glb:
  bot (s,r) x ⇔ glb (s,r) s x
Proof
  simp[bot_top,top_lub,lub_alt]
QED

Theorem bot_lub:
  bot (s,r) x ⇔ lub (s,r) EMPTY x
Proof
  simp[bot_top,top_glb,lub_alt]
QED

Theorem lub_pred:
   !s r p x. lub (s,r) (s INTER p) x = lub (s,r) p x
Proof
  rw[lub_def,least_def,IN_DEF,EQ_IMP_THM]
QED

Theorem glb_pred:
  !s r p x. glb (s,r) (\j. s j /\ p j) x = glb (s,r) p x
Proof
  rw[glb_def,greatest_def,IN_DEF,EQ_IMP_THM]
QED

Theorem complete_lub:
  !p c. complete p ==> ?x. lub p c x
Proof
  metis_tac[complete_def]
QED

Theorem complete_glb:
  !p c. complete p ==> ?x. glb p c x
Proof
  metis_tac[complete_def]
QED

Theorem complete_lattice_top:
  complete_lattice (p,r) ⇒ ?x. top (p,r) x 
Proof
  rw[complete_lattice_def,complete_def,top_glb]
QED

Theorem complete_lattice_bot:
  complete_lattice (p,r) ⇒ ?x. bot (p,r) x 
Proof
  simp[complete_lattice_def,complete_def,bot_lub]
QED

Theorem complete_flip:
  complete (p,flip r) ⇔ complete (p,r)
Proof
  rw[complete_def,EQ_IMP_THM,GSYM lub_alt,GSYM glb_alt]
QED

Definition chain_def:
  chain ((s,r):'a proset) c ⇔
    !x y. s x /\ s y /\ c x /\ c y ==> r x y \/ r y x
End

(* ------------------------------------------------------------------------- *)
(* Pointwise lifting of prosets                                               *)
(* ------------------------------------------------------------------------- *)

Definition pointwise_rel_def:
  pointwise_rel (t : 'a -> bool) (r: 'b -> 'b -> bool) =
    λf g. ∀x. t x ⇒ r (f x) (g x)
End

Definition pointwise_lift_def:
  pointwise_lift (t : 'a -> bool) ((s,r) : 'b proset) =
    (function t s, pointwise_rel t r)
End

Theorem lub_pointwise_lift:
  (∀y. t y ⇒ lub (q,r) {f y | (∀x. t x ⇒ q (f x)) ∧ c f} (l y)) ⇒
  lub (pointwise_lift t (q,r)) c l
Proof
  rw[pointwise_lift_def,pointwise_rel_def,function_def,lub_simp] >>
  metis_tac[]
QED

Theorem complete_pointwise_lift:
  complete p ⇒ complete (pointwise_lift t p)
Proof
  Cases_on `p` >>
  rw[complete] >>
  irule_at (Pos hd) lub_pointwise_lift >>
  `!y.
     t y ==>
     ?l. lub (q,r) {f y | (∀x. t x ⇒ q (f x)) ∧ c f} l` by
     rw[] >>
  pop_assum
    (MP_TAC o CONV_RULE
      (QUANT_CONV RIGHT_IMP_EXISTS_CONV THENC SKOLEM_CONV)) >>
  simp[]
QED

Theorem proset_pointwise_lift:
  proset p ⇒ proset (pointwise_lift t p)
Proof
  Cases_on `p` >>
  simp[pointwise_lift_def,pointwise_rel_def,proset_def] >>
  rw[function_def,refl_def,trans_def] >>
  metis_tac[]
QED

Theorem complete_lattice_pointwise_lift:
  complete_lattice p ⇒ complete_lattice (pointwise_lift t p)
Proof
  simp[complete_lattice_def,complete_pointwise_lift,
    proset_pointwise_lift]
QED

Theorem proset_pred_set:
  proset (p,$SUBSET)
Proof
  rw[proset_def,trans_def,refl_def] >>
  metis_tac[SUBSET_TRANS]
QED

Theorem lub_pred_set:
  BIGUNION s ∈ X ∧ s ⊆ X ⇒
  lub (X,$SUBSET) s (BIGUNION s)
Proof
  rw[lub_simp,BIGUNION,IN_DEF,SUBSET_DEF] >>
  metis_tac[]
QED

Theorem complete_pred_set:
  (∀s. s ⊆ X ⇒ BIGUNION s ∈ X) ⇒
  complete (X,$SUBSET)
Proof
  rpt strip_tac >>
  irule weak_complete_IMP_complete >>
  rw[weak_complete] >>
  irule_at (Pos hd) lub_pred_set >>
  metis_tac[]
QED

Theorem complete_lattice_pred_set:
  complete_lattice (UNIV,$SUBSET )
Proof
  simp[complete_lattice_def,proset_pred_set] >>
  irule complete_pred_set >>
  simp[]
QED

(* ------------------------------------------------------------------------- *)
(* Functions acting on prosets.                                               *)
(* ------------------------------------------------------------------------- *)

Definition monotonic_def:
  monotonic ((s,r) : 'a proset) f =
    !x y. s x /\ s y /\ r x y ==> r (f x) (f y)
End

Definition up_continuous_def:
  up_continuous ((s,r) : 'a proset) f =
  !c x.
    chain (s,r) c /\ lub (s,r) c x ==>
    lub (s,r) (\y. ?z. (s z /\ c z) /\ (y = f z)) (f x)
End

Definition down_continuous_def:
  down_continuous ((s,r) : 'a proset) f =
  !c x.
    chain (s,r) c /\ glb (s,r) c x ==>
    glb (s,r) (\y. ?z. (s z /\ c z) /\ (y = f z)) (f x)
End

Definition continuous_def:
  continuous (p : 'a proset) f <=> up_continuous p f /\ down_continuous p f
End

Definition monotonic_lift:
  monotonic_lift ((s,r) : 'a proset) =
    (monotonic (s,r) ∩ function s s, pointwise_rel s r)
End

Definition monotone_def:
  monotone (s,r) r' f ⇔ ∀x y. s x ∧ s y ∧ r x y ⇒ r' (f x) (f y)
End

Theorem monotone_weq:
  monotone (s,r) r' f ∧ function s s' f ∧ weq (s,r) x y ⇒ weq (s',r') (f x) (f y)
Proof
  rw[function_def,monotone_def,weq_def]
QED

Theorem monotonic_eq_monotone:
  monotonic (s,r) = monotone (s,r) r
Proof
  rw[FUN_EQ_THM,monotone_def,monotonic_def]
QED

Theorem monotonic_weq:
  monotonic (s,r) f ∧ function s s' f ∧ weq (s,r) x y ⇒
  weq (s',r) (f x) (f y)
Proof
  simp[monotonic_eq_monotone] >>
  metis_tac[monotone_weq]
QED

Theorem monotonic_alt:
  monotonic (s,r) = {f | ∀x y. s x ∧ s y ∧ r x y ⇒ r (f x) (f y)}
Proof
  rw[FUN_EQ_THM,monotonic_def,EQ_IMP_THM] >>
  metis_tac[]
QED

Theorem monotonic_I:
  monotonic (s,r) I
Proof
  simp[monotonic_def]
QED

Theorem monotonic_o:
  monotonic (s,r) f ∧ monotonic (s,r) g ∧ function s s g ⇒
  monotonic (s,r) (f o g)
Proof
  simp[monotonic_def,function_def]
QED

Theorem lub_monotonic_lift:
  proset (q,r) ⇒
  (∀y. q y ⇒
    lub (q,r)
      {f y | function q q f ∧ monotonic (q,r) f ∧ c f} (l y)) ⇒
   lub (monotonic_lift (q,r)) c l
Proof
  rw[monotonic_lift,pointwise_rel_def,INTER_DEF,IN_DEF,
    proset_def] >>
  rw[lub_simp]
  >- (
    rw[monotonic_def] >>
    irule lub_leq >>
    first_assum $ drule_then $ irule_at (Pos last) >>
    conj_tac >- metis_tac[lub_IN] >>
    rw[] >>
    irule leq_trans_lub >>
    last_x_assum $ irule_at (Pos last) >>
    drule_then (irule_at (Pos last)) $ iffLR monotonic_def >>
    qexists `y` >> 
    fs[function_def] >>
    metis_tac[])
  >- metis_tac[function_def,lub_IN]
  >- (
    irule leq_lub >>
    last_x_assum $ drule_then (irule_at (Pos last)) >>
    fs[function_def] >>
    metis_tac[]) >>
  last_x_assum $ drule_then assume_tac >>
  drule_then irule lub_leq >>
  fs[function_def] >>
  metis_tac[]
QED

Theorem proset_monotonic_lift:
  proset p ⇒ proset (monotonic_lift p)
Proof
  Cases_on `p` >>
  rw[monotonic_lift,proset_def,pointwise_rel_def,IN_DEF,
    refl_def,trans_def,function_def] >>
  metis_tac[]
QED

Theorem complete_lattice_monotonic_lift:
  complete_lattice p ⇒ complete_lattice (monotonic_lift p)
Proof
  Cases_on `p` >>
  rw[complete,complete_lattice_def]
  >- metis_tac[proset_monotonic_lift] >>
  irule_at (Pos hd) lub_monotonic_lift >>
  simp[] >>
  `!y. q y ⇒
    ∃l. lub (q,r)
      {f y | function q q f ∧ monotonic (q,r) f ∧ c f} l`
    by rw[] >>
  pop_assum
    (MP_TAC o CONV_RULE
      (QUANT_CONV RIGHT_IMP_EXISTS_CONV THENC SKOLEM_CONV)) >>
  simp[]
QED

Theorem lub_lub:
  complete_lattice (p,r) ∧
  (!y. s y ⇒ y SUBSET p) ∧
  lub (p,r) {x | ?y. s y ∧ lub (p,r) y x} l ==>
  lub (p,r) (BIGUNION s) l
Proof
  strip_tac >>
  rw[lub_simp]
  >- metis_tac[lub_IN]
  >- (
    drule_then irule leq_trans_lub >>
    simp[] >>
    conj_tac >- fs[complete_lattice_def,proset_def] >>
    fs[complete_lattice_def,complete,IN_DEF,SUBSET_DEF] >>
    first_assum $ irule_at Any >>
    metis_tac[lub_IN,leq_lub]) >>
  drule_then irule lub_leq >>
  rw[] >>
  drule_then irule lub_leq >>
  rw[] >>
  metis_tac[IN_DEF]
QED

(* ------------------------------------------------------------------------- *)
(* Least and greatest fixed points.                                          *)
(* ------------------------------------------------------------------------- *)
Definition post_fixpoint_def:
  post_fixpoint (p,r) f x ⇔ p x ∧ r x (f x)
End

Definition pre_fixpoint_def:
  pre_fixpoint (p,r) f x ⇔ p x ∧ r (f x) x
End

Definition fixpoint_def:
  fixpoint eq f x ⇔ eq x (f x)
End

Theorem pre_fixpoint_alt:
  pre_fixpoint (p,r) = post_fixpoint (p,flip r)
Proof
  rw[pre_fixpoint_def,post_fixpoint_def,FUN_EQ_THM]
QED

Theorem post_fixpoint_alt:
  post_fixpoint (p,r) = pre_fixpoint (p,flip r)
Proof
  rw[pre_fixpoint_def,post_fixpoint_def,FUN_EQ_THM]
QED

Definition gfp_def:
  gfp (p,r) f x ⇔ greatest (p ∩ fixpoint (weq (p,r)) f) r x
End

Definition lfp_def:
  lfp (p,r) f x ⇔ least (p ∩ fixpoint (weq (p,r)) f) r x
End

Theorem gfp_simp = SRULE[fixpoint_def,greatest_def,IN_DEF] gfp_def

Theorem lfp_simp = SRULE[fixpoint_def,least_def,IN_DEF] lfp_def

Theorem knaster_tarski_gfp_lub:
  proset (p,r) ∧
  monotonic (p,r) f ∧
  function p p f ∧
  lub (p,r) (post_fixpoint (p,r) f) x ==>
  gfp (p,r) f x
Proof
  strip_tac >>
  `p x` by metis_tac[lub_IN] >>
  rw[gfp_simp]
  >- (
    `p (f x)` by metis_tac[function_def] >>
    simp[weq_def] >>
    conj_asm1_tac
    >- (
      drule_then irule lub_leq >>
      rw[post_fixpoint_def] >>
      fs[proset_def] >>
      drule_then irule $ iffLR trans_def >>
      simp[] >>
      first_assum (irule_at (Pos $ el 2)) >>
      conj_tac >- fs[function_def] >>
      drule_then irule $ iffLR monotonic_def >>
      simp[] >>
      drule_then irule leq_lub >>
      simp[post_fixpoint_def]
    ) >>
    drule_then irule leq_lub >>
    fs[monotonic_def,post_fixpoint_def]
  ) >>
  drule_then irule leq_lub >>
  simp[post_fixpoint_def] >>
  fs[weq_def]
QED

Theorem post_fixpoint_SUBSET:
  post_fixpoint (p,r) f ⊆ p
Proof
  gvs[SUBSET_DEF,IN_DEF,post_fixpoint_def]
QED

Theorem knaster_tarski_gfp_lub_thm:
  complete_lattice (p,r) ∧
  monotonic (p,r) f ∧ function p p f ==>
  ∃l.
    lub (p,r) (post_fixpoint (p,r) f) l ∧
    gfp (p,r) f l
Proof
  rw[complete_lattice_def,complete] >>
  first_assum $ qspec_then `post_fixpoint (p,r) f`
    strip_assume_tac >>
  first_assum $ irule_at (Pos hd) >>
  drule_all_then (irule_at (Pos hd)) knaster_tarski_gfp_lub
QED

Theorem knaster_tarski_gfp_thm:
  complete_lattice (p,r) ∧
  monotonic (p,r) f ∧ function p p f ⇒
  ?x. gfp (p,r) f x
Proof
  rpt strip_tac >>
  metis_tac[knaster_tarski_gfp_lub_thm]
QED

Theorem gfp_alt:
  gfp (p,r) = lfp (p,flip r)
Proof
  rw[gfp_def,lfp_def,FUN_EQ_THM,weq_flip] >>
  metis_tac[greatest_alt]
QED

Theorem lfp_alt:
  lfp (p,r) = gfp (p,flip r)
Proof
  simp[gfp_alt]
QED

Theorem monotonic_flip:
  monotonic (p,flip r) f ⇔ monotonic (p,r) f
Proof
  rw[monotonic_def,EQ_IMP_THM]
QED

Theorem knaster_tarski_lfp_glb:
  proset (p,r) ∧
  monotonic (p,r) f ∧
  function p p f ∧
  glb (p,r) (pre_fixpoint (p,r) f) x ==>
  lfp (p,r) f x
Proof
  qspec_then `flip r` assume_tac $
    Q.GEN `r` knaster_tarski_gfp_lub >>
  rw[pre_fixpoint_alt,glb_alt,lfp_alt,proset_flip,monotonic_flip]
QED

Theorem pre_fixpoint_SUBSET:
  pre_fixpoint (p,r) f ⊆ p
Proof
  simp[pre_fixpoint_def,SUBSET_DEF,IN_DEF]
QED

Theorem knaster_tarski_lfp_thm:
  complete_lattice (p,r) ∧
  monotonic (p,r) f ∧ function p p f ⇒
  ?x. lfp (p,r) f x
Proof
  qspec_then `flip r` assume_tac $
    Q.GEN `r` knaster_tarski_gfp_thm >>
  rw[pre_fixpoint_alt,glb_alt,lfp_alt,complete_lattice_def,
    complete_flip,proset_flip,monotonic_flip]
QED

Theorem gfp_weq:
  gfp (s,r) f x ∧ gfp (s,r) f y ⇒ weq (s,r) x y
Proof
  rw[gfp_simp] >>
  simp[weq_def]
QED

Theorem lfp_weq:
  lfp (s,r) f x ∧ lfp (s,r) f y ⇒ weq (s,r) x y
Proof
  rw[lfp_simp] >> simp[weq_def]
QED

Theorem gfp:
  complete_lattice (s,r) ∧
  function s s f ∧ monotonic (s,r) f ==>
  (gfp ((s,r) : 'a proset) f x =
    (s x /\ (weq (s,r) x (f x)) /\
      (!y. s y /\ r y (f y) ==> r y x)))
Proof
  rpt strip_tac >>
  drule_all knaster_tarski_gfp_lub_thm >>
  rw[] >>
  drule_then assume_tac gfp_weq >>
  rw[EQ_IMP_THM] >>
  fs[gfp_simp]
  >- (
    `weq (s,r) l x` by metis_tac[] >>
    `r y l` by (
      drule_then irule leq_lub >>
      simp[post_fixpoint_def]
    ) >>
    fs[complete_lattice_def,proset_def] >>
    drule_then irule $ iffLR trans_def >>
    simp[] >>
    metis_tac[weq_def]
  ) >>
  rw[weq_def]
QED

Definition closed_interval_def:
  closed_interval (p,r) a b ⇔ {x | p x ∧ r a x ∧ r x b}
End

Theorem closed_interval_SUBSET_p:
  closed_interval (p,r) a b ⊆ p
Proof
  simp[closed_interval_def,SUBSET_DEF,IN_DEF]
QED

Theorem closed_interval_lub:
  proset (p,r) ∧
  s ⊆ closed_interval (p,r) a b ∧
  p a ∧ p b ∧
  s x ∧ 
  lub (p,r) s l ⇒
  lub (closed_interval (p,r) a b,r) s l
Proof
  rw[SUBSET_DEF,IN_DEF,closed_interval_def] >>
  gvs[lub_simp] >>
  last_x_assum drule >>
  rw[] >>
  `r x l` by fs[] >>
  fs[proset_def,trans_def] >>
  metis_tac[]
QED

Theorem complete_lattice_closed_interval:
  complete_lattice (p,r) ∧ p a ∧ p b ∧ r a b ⇒
  complete_lattice (closed_interval (p,r) a b,r)
Proof
  rw[complete_lattice_def]
  >- metis_tac[proset_SUBSET,closed_interval_SUBSET_p] >>
  irule weak_complete_IMP_complete >>
  fs[complete,weak_complete] >>
  rw[] >>
  last_x_assum $ qspec_then `c` strip_assume_tac >>
  Cases_on `?x. c x` >>
  gvs[]
  >- metis_tac[closed_interval_lub] >>
  qexists `a` >>
  rw[closed_interval_def,lub_simp] >>
  fs[proset_def,refl_def]
QED

Theorem least_closed_interval_lub_thm:
  trans (p,r) ∧
  s ⊆ p ∧
  w SUBSET s ∧
  lub (p,r) w a ∧
  top (p,r) b ∧
  least (closed_interval (p,r) a b ∩ s) r x ⇒
  lub (s,r) w x
Proof
  rw[least_def,closed_interval_def,IN_DEF] >>
  rw[lub_simp]
  >- (
    `p y` by fs[SUBSET_DEF,IN_DEF] >>
    `p a` by metis_tac[lub_IN] >>
    `r y a` suffices_by (
      strip_tac >>
      drule_then irule $ iffLR trans_def >>
      metis_tac[]) >>
    drule_then irule leq_lub >>
    simp[]) >>
  last_x_assum irule >>
  fs[SUBSET_DEF,IN_DEF,top_def] >>
  drule_then irule lub_leq >>
  simp[]
QED

Theorem closed_interval_INTER:
  closed_interval (p,r) a b ∩ p = closed_interval (p,r) a b
Proof
  rw[closed_interval_def,SUBSET_DEF,EXTENSION,IN_DEF,
    EQ_IMP_THM]
QED

Theorem closed_interval_monotonic_IN:
  proset (p,r) ∧
  monotonic (p,r) f ∧
  function p p f ∧
  w ⊆ fixpoint (weq (p,r)) f ∧
  lub (p,r) w a ∧
  top (p,r) b ∧
  closed_interval (p,r) a b x ⇒
  closed_interval (p,r) a b (f x)
Proof
  simp[closed_interval_def,proset_def] >>
  strip_tac >>
  conj_asm1_tac
  >- gvs[function_def] >>
  reverse $ conj_tac
  >- gvs[top_def] >>
  `p a` by metis_tac[lub_IN] >>
  `r (f a) (f x)` by fs[monotonic_def] >>
  `p (f a)` by fs[function_def] >>
  drule_then irule $ iffLR trans_def >>
  simp[] >>
  first_x_assum $ irule_at (Pos last) >>
  simp[] >>
  drule_then irule lub_leq >>
  rw[] >>
  drule_then irule $ iffLR trans_def >>
  fs[SUBSET_DEF,fixpoint_def,weq_def,IN_DEF] >>
  last_x_assum $ drule_then strip_assume_tac >>
  first_assum $ irule_at (Pos $ el 2) >>
  simp[] >>
  drule_then irule $ iffLR monotonic_def >>
  simp[] >>
  drule_all_then irule leq_lub
QED

Theorem closed_interval_INTER_fixpoint_EQ:
  trans (p,r) ∧ p x ∧ p x' ⇒
  (closed_interval (p,r) x x' ∩
    fixpoint (weq (closed_interval (p,r) x x',r)) f) =
  (closed_interval (p,r) x x' ∩ fixpoint (weq (p,r)) f)
Proof
  rw[closed_interval_def,fixpoint_def,EXTENSION,
    INTER_DEF,IN_DEF,EQ_IMP_THM,weq_def] >>
  drule_then irule $ iffLR trans_def >>
  simp[] >>
  metis_tac[]
QED

Theorem complete_lattice_fixpoint:
  complete_lattice (p,r) ∧
  monotonic (p,r) f ∧ function p p f ==>
  complete_lattice (p ∩ fixpoint (weq (p,r)) f,r)
Proof
  rpt strip_tac >>
  fs[complete_lattice_def] >>
  conj_tac
  >- (drule_then irule proset_SUBSET >> simp[]) >>
  irule weak_complete_IMP_complete >>
  fs[complete,weak_complete] >>
  rw[] >>
  irule_at (Pos hd) least_closed_interval_lub_thm >>
  fs[proset_def] >>
  last_assum $ irule_at (Pos hd) >>
  simp[INTER_SUBSET,Once $ GSYM INTER_ASSOC,top_lub] >>
  last_assum $ qspec_then `c` strip_assume_tac >>
  last_assum $ qspec_then `p` strip_assume_tac >>
  first_assum $ irule_at (Pos hd) >>
  first_assum $ irule_at (Pos hd) >>
  simp[INTER_ASSOC,closed_interval_INTER] >>
  `p x` by metis_tac[lub_IN] >>
  `p x'` by metis_tac[lub_IN] >>
  drule_then (rev_drule_then drule) $
    GSYM closed_interval_INTER_fixpoint_EQ >>
  simp[] >>
  disch_then kall_tac >>
  simp[GSYM lfp_def] >>
  irule knaster_tarski_lfp_thm >>
  conj_tac
  >- (
    irule complete_lattice_closed_interval >>
    simp[complete_lattice_def,complete,proset_def] >>
    drule_then irule leq_lub >>
    simp[]) >>
  rw[function_def,monotonic_def]
  >- (
    fs[monotonic_def] >>
    metis_tac[closed_interval_SUBSET_p,SUBSET_DEF,IN_DEF]) >>
  irule closed_interval_monotonic_IN >>
  simp[top_lub,proset_def] >>
  metis_tac[]
QED

(* coinduction all the way *)
Definition compatible_def:
  compatible (p,r) b f = pointwise_rel p r (f o b) (b o f)
End

Theorem compatible_I:
  refl (s,r) ∧ function s s b ⇒
  compatible (s,r) b I
Proof
  rw[refl_def,compatible_def,pointwise_rel_def,function_def]
QED

Theorem function_o:
  function s' s'' f ∧ function s s' g ==>
  function s s'' (f o g)
Proof
  simp[function_def]
QED

Theorem monotonic_o:
  function s s' g ∧
  monotonic (s',r) f ∧ monotonic (s,r) g ⇒
  monotonic (s,r) (f o g)
Proof
  simp[function_def,monotonic_def]
QED

Theorem compatible_o:
  trans (s,r) ∧ monotonic (s,r) f ∧
  function s s b ∧ function s s f ∧ function s s g ∧
  compatible (s,r) b f ∧ compatible (s,r) b g ⇒
  compatible (s,r) b (f o g)
Proof
  rw[function_def,o_DEF,compatible_def,pointwise_rel_def] >>
  dxrule_then irule $ iffLR trans_def >>
  simp[] >>
  last_assum $ irule_at (Pos last) >>
  simp[] >>
  dxrule_then irule $ iffLR monotonic_def >>
  simp[]
QED

Theorem compatible_K:
  r x (b x) ⇒
  compatible (s,r) b (K x)
Proof
  rw[compatible_def,function_def,pointwise_rel_def]
QED

Theorem compatible_b:
  refl (s,r) ∧ function s s b ⇒
  compatible (s,r) b b
Proof
  rw[compatible_def,pointwise_rel_def,refl_def,function_def]
QED

Theorem least_respect_weq:
  trans (s,r) ∧
  least s r l ∧ weq (s,r) l l' ⇒ least s r l'
Proof
  rw[least_def,weq_def] >>
  drule_then irule $ iffLR trans_def >>
  metis_tac[]
QED

Theorem lub_respect_weq:
  lub p c l ∧ weq p l l' ∧ trans p ⇒ lub p c l'
Proof
  Cases_on `p` >>
  rw[lub_def] >>
  irule least_respect_weq >>
  conj_tac
  >- (
    drule_then irule trans_SUBSET >>
    fs[SUBSET_DEF,IN_DEF]) >>
  first_assum $ irule_at (Pos hd) >>
  fs[weq_def,least_def] >>
  rpt strip_tac >>
  drule_then irule $ iffLR trans_def >>
  metis_tac[]
QED

Theorem lub_monotonic_lift_monotonic:
  lub (monotonic_lift (s,r)) c l ⇒
  monotonic (s,r) l ∧ function s s l
Proof
  rw[monotonic_lift] >>
  drule lub_IN >>
  simp[INTER_DEF,IN_DEF]
QED

Theorem pointwise_rel_IMP:
  pointwise_rel s r l l' ∧ s y ==> r (l y) (l' y)
Proof
  fs[IN_DEF,monotonic_lift,function_def,pointwise_rel_def]
QED

Theorem weq_monotonic_lift:
  weq (monotonic_lift (s,r)) l l' ∧ s y ⇒
  weq (s,r) (l y) (l' y)
Proof
  rw[monotonic_lift,weq_def,IN_DEF] >>
  metis_tac[function_def,pointwise_rel_IMP]
QED

Theorem lub_monotonic_lift_EQ:
  complete_lattice (s,r) ⇒
  lub (monotonic_lift (s,r)) c l =
  (∀y. s y ⇒
    lub (s,r)
      {f y | function s s f ∧ monotonic (s,r) f ∧ c f} (l y))
Proof
  rw[complete_lattice_def,complete,EQ_IMP_THM]
  >- (
    `!y. s y ⇒
      ∃l. lub (s,r)
        {f y | function s s f ∧ monotonic (s,r) f ∧ c f} l`
      by rw[] >>
    pop_assum
     (strip_assume_tac o CONV_RULE
       (QUANT_CONV RIGHT_IMP_EXISTS_CONV THENC SKOLEM_CONV)) >>
    drule_all_then assume_tac lub_monotonic_lift >>
    drule_then (rev_drule_then assume_tac) lub_weq >>
    drule_all_then assume_tac weq_monotonic_lift >>
    last_x_assum (drule_then assume_tac) >>
    fs[proset_def] >>
    metis_tac[lub_respect_weq]) >>
  metis_tac[lub_monotonic_lift]
QED

Theorem compatible_lub:
  complete_lattice (s,r) ∧
  function s s b ∧ monotonic (s,r) b ∧
  w ⊆ compatible (s,r) b ∧
  lub (monotonic_lift (s,r)) w l ⇒
  compatible (s,r) b l
Proof
  rw[compatible_def,pointwise_rel_def] >>
  drule_then strip_assume_tac lub_monotonic_lift_monotonic >>
  drule_then (drule_then assume_tac) $
    iffLR lub_monotonic_lift_EQ >>
  pop_assum $ markerLib.ASSUME_NAMED_TAC "pointwise_lub" >>
  `s (b x)` by fs[function_def] >>
  markerLib.LABEL_ASSUM "pointwise_lub" $
    drule_then assume_tac >>
  `s (b (l x))` by fs[function_def] >>
  fs[complete_lattice_def,proset_def] >>
  drule_all lub_leq_simp >>
  simp[] >>
  disch_then kall_tac >>
  rw[] >>
  `r (f (b x)) (b (f x))` by (
    fs[compatible_def,SUBSET_DEF,IN_DEF,pointwise_rel_def]) >>
  drule_then irule $ iffLR trans_def >>
  ntac 2 (conj_tac >- fs[function_def]) >>
  first_x_assum $ irule_at (Pos $ el 2) >>
  conj_tac >- fs[function_def] >>
  drule_then irule $ iffLR monotonic_def >>
  ntac 2 (conj_tac >- fs[function_def]) >>
  markerLib.LABEL_ASSUM "pointwise_lub" $
    qspec_then `x` mp_tac >>
  rw[] >>
  dxrule_then irule leq_lub >>
  fs[function_def] >>
  metis_tac[]
QED

Definition companion_def:
  companion p b = lub (monotonic_lift p) (compatible p b)
End

Theorem companion_monotonic:
  companion (s,r) b t ⇒
  monotonic (s,r) t ∧ function s s t
Proof
  rw[companion_def,monotonic_lift] >>
  drule lub_IN >>
  fs[SUBSET_DEF,IN_DEF]
QED

Theorem companion_weq:
  companion p b x ∧ companion p b y ⇒
  weq (monotonic_lift p) x y
Proof
  rw[companion_def] >>
  metis_tac[lub_weq]
QED

Theorem exists_companion:
  complete_lattice p ⇒
  ∃t. companion p b t
Proof
  strip_tac >>
  drule complete_lattice_monotonic_lift >>
  simp[complete_lattice_def,complete,companion_def]
QED

Definition the_companion_def:
  the_companion p b = @t. companion p b t
End

Theorem compatible_companion:
  companion (s,r) b t ∧
  monotonic (s,r) b ∧ function s s b ∧
  complete_lattice (s,r) ==>
  compatible (s,r) b t
Proof
  rw[companion_def] >>
  irule compatible_lub >>
  rw[] >>
  last_x_assum $ irule_at (Pos last) >>
  simp[]
QED

Theorem leq_companion:
  companion (s,r) b t ∧
  compatible (s,r) b f ∧
  monotonic (s,r) f ∧ function s s f ⇒
  pointwise_rel s r f t
Proof
  rw[companion_def,monotonic_lift] >>
  drule_then irule leq_lub >>
  simp[SUBSET_DEF,IN_DEF]
QED

Theorem companion_bot_post_fixpoint:
  companion (s,r) b t ∧
  bot (s,r) bottom ∧
  complete_lattice (s,r) ∧
  function s s b ∧ monotonic (s,r) b ⇒
  post_fixpoint (s,r) b (t bottom)
Proof
  strip_tac >>
  drule_all compatible_companion >>
  fs[companion_def,bot_def,post_fixpoint_def] >>
  drule lub_monotonic_lift_monotonic >>
  fs[function_def,monotonic_def,
    complete_lattice_def,proset_def] >>
  rw[] >>
  drule_then irule $ iffLR trans_def >>
  simp[] >>
  qexists `t (b bottom)` >>
  fs[compatible_def,pointwise_rel_def]
QED

Theorem leq_companion_bot:
  companion (s,r) b t ∧
  bot (s,r) bottom ∧
  complete_lattice (s,r) ∧
  function s s b ∧ monotonic (s,r) b ⇒
  ∀y. s y ∧ r y (b y) ⇒ r y (t bottom)
Proof
  fs[companion_def] >>
  rw[] >>
  fs[lub_monotonic_lift_EQ] >>
  last_assum $ qspec_then `bottom` mp_tac >>
  impl_tac
  >- (
    fs[bot_lub] >>
    metis_tac[lub_IN]) >>
  rw[] >>
  drule_then irule leq_lub >>
  simp[] >>
  drule_then (irule_at (Pos last)) compatible_K >>
  rw[function_def,monotonic_def] >>
  fs[complete_lattice_def,proset_def,refl_def]
QED

Theorem companion_bot_fixpoint:
  companion (s,r) b t ∧
  bot (s,r) bottom ∧
  complete_lattice (s,r) ∧
  function s s b ∧ monotonic (s,r) b ⇒
  weq (s,r) (t bottom) (b (t bottom))
Proof
  simp[weq_def] >>
  strip_tac >>
  `s (t bottom) ∧ s (b (t (bottom))) ∧ s bottom` by (
    fs[companion_def] >>
    drule lub_monotonic_lift_monotonic >>
    metis_tac[bot_lub,lub_IN,function_def]) >>
  simp[] >>
  conj_asm1_tac
  >- (
    irule $ cj 2 $ SRULE[post_fixpoint_def] $
      companion_bot_post_fixpoint >>
    metis_tac[]) >>
  drule_then irule leq_companion_bot >>
  simp[] >>
  drule_then irule $ iffLR monotonic_def >>
  simp[]
QED

Theorem companion_o_idem:
  companion (s,r) b t ∧
  complete_lattice (s,r) ∧
  function s s b ∧ monotonic (s,r) b ⇒
  weq (monotonic_lift (s,r)) (t o t) t
Proof
  strip_tac >>
  drule_then strip_assume_tac companion_monotonic >>
  `monotonic (s,r) (t o t) ∧ function s s (t o t)` by
    metis_tac[monotonic_o,function_o] >>
  rw[monotonic_lift,weq_def,IN_DEF] 
  >- (
    drule_then irule leq_companion >>
    simp[] >>
    irule compatible_o >>
    rw[]
    >- fs[complete_lattice_def,proset_def] >>
    irule compatible_companion >>
    simp[]) >>
  rw[pointwise_rel_def] >>
  drule_then irule $ iffLR monotonic_def >>
  fs[function_def] >>
  drule $ SRULE[pointwise_rel_def] leq_companion >>
  disch_then $ qspec_then `I` mp_tac >>
  simp[monotonic_def,function_def] >>
  disch_then irule >>
  simp[] >>
  irule compatible_I >>
  fs[function_def,complete_lattice_def,proset_def]
QED

val _ = export_theory();
