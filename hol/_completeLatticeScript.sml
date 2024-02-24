open HolKernel boolLib bossLib BasicProvers dep_rewrite pairTheory;
open pred_setTheory relationTheory combinTheory;

open restrictTheory;
(* open partial_functionTheory; *)

val _ = new_theory "completeLattice";

Definition refl_set_def:
  refl_set s R ⇔ ∀ x. s x ⇒ R x x
End

Definition antisym_set_def:
  antisym_set s R ⇔ ∀ x y. s x ∧ s y /\
    R x y ∧ R y x ⇒ (x = y)
End

Definition trans_set_def:
  trans_set s r ⇔ ∀ x y z. s x ∧ s y ∧ s z ∧
    r x y ∧ r y z ⇒ r x z
End

Triviality refl_set_SUBSET:
  refl_set p r ∧
  s SUBSET p ⇒
  refl_set s r
Proof
  simp[refl_set_def,SRULE[IN_DEF]SUBSET_DEF]
QED

Triviality antisym_set_SUBSET:
  antisym_set p r ∧
  s ⊆ p ==>
  antisym_set s r
Proof
  simp[antisym_set_def,SRULE[IN_DEF]SUBSET_DEF]
QED

Triviality trans_set_SUBSET:
  trans_set p r ∧ s ⊆ p ⇒
  trans_set s r
Proof
  rw[trans_set_def,SRULE[IN_DEF]SUBSET_DEF] >>
  metis_tac[]
QED

Definition poset_def:
  poset (p,r) ⇔
    refl_set p r ∧
    antisym_set p r ∧
    trans_set p r
End

Theorem poset_simp =
  SRULE[refl_set_def,antisym_set_def,trans_set_def]
    poset_def

Theorem poset_SUBSET:
  poset (p,r) ∧ s SUBSET p ⇒
  poset (s,r)
Proof
  rw[poset_def] >>
  metis_tac[refl_set_SUBSET,
    antisym_set_SUBSET,
    trans_set_SUBSET]
QED

Definition greatest_def:
  greatest s r x ⇔ s x ∧ (!y. s y ⇒ r y x)
End

Definition glb_def:
  glb (p,r) s x ⇔ greatest (\z. p z ∧ !y. p y ∧ s y ⇒ r z y) r x
End

Theorem glb_simp = SRULE[greatest_def] glb_def

Theorem greatest_unique:
  antisym_set s r ∧
  greatest s r x ∧ greatest s r y ⇒
  x = y
Proof
  rw[greatest_def] >>
  `r x y` by metis_tac[] >>
  `r y x` by metis_tac[] >>
  fs[antisym_set_def]
QED

Theorem glb_unique:
  antisym_set p r ∧
  glb (p,r) s x ∧ glb (p,r) s y ⇒
  x = y
Proof
  rw[glb_def] >>
  drule_at_then (Pos last)
    (drule_at_then (Pos last) irule)
      greatest_unique >>
  drule_then irule antisym_set_SUBSET >>
  gvs[IN_DEF,SUBSET_DEF]
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

Theorem refl_set_flip:
  refl_set p r ⇒
  refl_set p (flip r)
Proof
  simp[refl_set_def]
QED

Theorem forall_flip:
  (!r. P (flip r)) <=> (!r. P r)
Proof
  iff_tac >>
  rw[] >>
  metis_tac[flip_flip]
QED

Theorem antisym_set_flip:
  antisym_set p r ⇒
  antisym_set p (flip r)
Proof
  simp[antisym_set_def]
QED

Theorem trans_set_flip:
  trans_set p r ⇒
  trans_set p (flip r)
Proof
  simp[trans_set_def] >>
  metis_tac[]
QED

Theorem poset_flip:
  poset (p,r) ⇒
  poset (p,flip r)
Proof
  metis_tac[poset_def,
    refl_set_flip,antisym_set_flip,trans_set_flip]
QED

Theorem lub_unique:
  antisym_set p r ∧
  lub (p,r) s x ∧ lub (p,r) s y ⇒
  x = y
Proof
  rw[lub_alt] >>
  metis_tac[antisym_set_flip,glb_unique]
QED

Theorem glb_alt:
  glb (p,r) = lub (p,flip r)
Proof
  simp[lub_alt]
QED

Theorem greatest_IFF_upper_bound:
  s ⊆ p ⇒
  (greatest s r x ⇔ s x ∧ p x ∧ (!y. p y ∧ s y ⇒ r y x))
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
    greatest_IFF_upper_bound
QED

Theorem least_IFF_lower_bound:
  s ⊆ p ⇒
  (least s r x ⇔ s x ∧ p x ∧ (!y. p y ∧ s y ⇒ r x y))
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
    least_IFF_lower_bound
QED

Theorem lub_EQ_glb_lower_bound:
  lub (p,r) s =
    glb (p,r) (\z. p z ∧ !y. p y ∧ s y ⇒ r y z)
Proof
  irule EQ_EXT >>
  gen_tac >>
  iff_tac >>
  simp[lub_def,least_alt,glb_def,greatest_def]
QED

Theorem glb_lower_bound_IMP_lub =
  iffRL $ AP_THM lub_EQ_glb_lower_bound ``x``

Theorem exists_all_glb_IMP_exists_all_lub:
  (!s. s ⊆ p ⇒ ?g. glb (p,r) s g) ⇒
  (!s'. s' ⊆ p ⇒ ?l. lub (p,r) s l)
Proof
  rw[] >>
  irule_at (Pos hd) glb_lower_bound_IMP_lub >>
  last_x_assum ho_match_mp_tac >>
  simp[SUBSET_DEF,IN_DEF]
QED

Theorem exists_all_lub_IMP_exists_all_glb:
  (!s. s ⊆ p ⇒ ?g. lub (p,r) s g) ⇒
  (!s'. s' ⊆ p ⇒ ?l. glb (p,r) s l)
Proof
  disch_then $ strip_assume_tac o SRULE[lub_alt] >>
  simp[glb_alt] >>
  metis_tac[exists_all_glb_IMP_exists_all_lub]
QED

Definition complete_lattice_def:
  complete_lattice (p,r) ⇔ poset (p,r) ∧
    (!s. s ⊆ p ⇒ ?g. lub (p,r) s g)
End

Theorem complete_lattice:
  complete_lattice (p,r) ⇔ poset (p,r) ∧
    (!s. s ⊆ p ⇒ ?l. lub (p,r) s l) ∧
    (!s. s ⊆ p ⇒ ?g. glb (p,r) s g)
Proof
  simp[complete_lattice_def,EQ_IMP_THM] >>
  metis_tac[exists_all_lub_IMP_exists_all_glb]
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

Theorem EMPTY_bot:
  EMPTY ∈ s ==> bot (s,\x y. x SUBSET y) EMPTY
Proof
  gvs[bot_def,SUBSET_DEF,IN_DEF]
QED

Theorem complete_lattice_bot:
  complete_lattice (p,r) ⇒ ?x. bot (p,r) x 
Proof
  simp[complete_lattice] >>
  metis_tac[bot_lub,EMPTY_SUBSET]
QED

Theorem complete_lattice_bot:
  complete_lattice (p,r) ⇒ ?x. top (p,r) x 
Proof
  simp[complete_lattice] >>
  metis_tac[top_glb,EMPTY_SUBSET]
QED

Theorem complete_lattice_bot:
  complete_lattice (p,r) ⇒ ?x. bot (p,r) x 
Proof
  simp[complete_lattice] >>
  metis_tac[bot_lub,EMPTY_SUBSET]
QED

Theorem complete_lattice_flip:
  complete_lattice (p,r) ⇒
  complete_lattice (p,flip r)
Proof
  strip_tac >>
  simp[complete_lattice_def] >>
  gvs[complete_lattice] >>
  rw[]
  >- metis_tac[poset_flip] >>
  simp[lub_alt]
QED

Triviality lub_IN:
  lub (p,r) s x ⇒ p x
Proof
  simp[lub_simp]
QED

Triviality glb_IN:
  glb (p,r) s x ⇒ p x
Proof
  simp[glb_simp]
QED

Definition monotone_def:
  monotone (p,r) f ⇔ (∀ x y. p x ∧ p y ∧ r x y ⇒
    p (f x) ∧ p (f y) ∧ r (f x) (f y))
End

Definition ord_pointwise_def:
  ord_pointwise (p,r) f g ⇔ (∀x. p x ⇒ r (f x) (g x))
End

Definition monotone_restricted_def:
  monotone_restricted (p,r) f ⇔
    restricted p f ∧ monotone (p,r) f
End

Definition monotone_lift_def:
  monotone_lift (p,r) ⇔
    (monotone_restricted (p,r),ord_pointwise (p,r)) 
End

Theorem monotone_closed:
  refl_set p r ∧
  monotone (p,r) f ∧ p x ⇒
  p (f x)
Proof
  rw[monotone_def,refl_set_def] >>
  last_x_assum $ drule_then strip_assume_tac >>
  last_x_assum drule_all >>
  simp[]
QED

Theorem monotone_flip:
  monotone (p,r) f ∧ (!x. p x ⇒ p (f x)) ⇒ monotone (p,flip r) f
Proof
  rw[monotone_def]
QED

Theorem monotone_lift_poset:
  poset (p,r) ⇒ poset (monotone_lift (p,r))
Proof
  rw[monotone_lift_def] >>
  fs[poset_def] >>
  rw[]
  >- (
    fs[monotone_restricted_def,monotone_def,refl_set_def] >>
    rw[ord_pointwise_def]
  )
  >- (
    fs[antisym_set_def,ord_pointwise_def] >>
    fs[monotone_restricted_def] >>
    rw[] >>
    drule_then (drule_then irule) restricted_unique >>
    rw[] >>
    first_x_assum $ drule_then assume_tac >>
    first_x_assum $ drule_then assume_tac >>
    last_x_assum irule >>
    simp[] >>
    metis_tac[monotone_closed]
  )
  >- (
    fs[trans_set_def,ord_pointwise_def,
      monotone_restricted_def] >>
    rw[] >>
    metis_tac[monotone_closed]
  )
QED

Definition UNION_func_def:
  UNION_func s x ⇔ {f x| s f}
End

Theorem UNION_func_applied =
  SRULE[EXTENSION,IN_DEF] UNION_func_def;

Theorem UNION_rel_EMPTY:
  (¬ ∃ f. s f) ==>
  (UNION_func s x = EMPTY)
Proof
  rw[FUN_EQ_THM,UNION_func_def]
QED

Theorem lub_monotone_lem:
  trans_set p r ∧
  (!x. p x ∧ X x ⇒ ?y. p y ∧ Y y ∧ r x y) ∧
  lub (p,r) Y y' ∧
  lub (p,r) X x' ⇒
  r x' y'
Proof
  rw[lub_simp] >>
  first_assum irule >>
  rw[] >>
  last_assum drule_all >>
  strip_tac >>
  `r y'' y'` by metis_tac[] >>
  fs[trans_set_def] >>
  last_assum irule >>
  simp[] >>
  metis_tac[]
QED

Theorem lub_UNION_func_mono_lem:
  trans_set p r ∧
  (!x. s x ⇒ monotone (p,r) x) ∧
  p x ∧ p y ∧ r x y ∧
  lub (p,r) (UNION_func s y) y' ∧
  lub (p,r) (UNION_func s x) x' ∧
  p x' ∧ p y' ⇒
  r x' y'
Proof
  rw[] >>
  drule_then (drule_at_then (Pos last) irule)
    lub_monotone_lem >>
  first_assum $ irule_at (Pos last) >>
  rw[UNION_func_def] >>
  last_x_assum drule >>
  rw[monotone_def] >>
  first_x_assum $ drule_all >>
  rw[] >>
  metis_tac[]
QED

Theorem UNION_rel_SUBSET:
  s ⊆ monotone (p,r) ∧
  refl_set p r ∧
  p x ⇒
  UNION_func s x ⊆ p
Proof
  rw[SUBSET_DEF,IN_DEF,UNION_func_def] >>
  last_x_assum $ drule_then assume_tac >>
  drule_all monotone_closed >>
  fs[monotone_def]
QED

val drule_last_then = drule_at_then (Pos last);

Theorem monotone_restrict:
  monotone (p,r) (restrict p f) ⇔ monotone (p,r) f
Proof
  rw[monotone_def,restrict_def]
QED

Theorem SELECT_lub:
  complete_lattice (p,r) ∧
  lub (p,r) s l ⇒
  ((@l. lub (p,r) s l) = l)
Proof
  rw[complete_lattice_def,poset_def] >>
  SELECT_ELIM_TAC >>
  conj_asm1_tac >>
  rw[] >>
  metis_tac[lub_unique]
QED

Theorem lub_UNION_func_monotone:
  complete_lattice (p,r) ∧
  s ⊆ monotone (p,r) ==> 
  monotone (p,r)
    (λx. @l. lub (p,r) (UNION_func s x) l)
Proof
  strip_tac >>
  simp[monotone_def] >>
  rpt gen_tac >> strip_tac >>
  `∃y. lub (p,r) (UNION_func s x) y`
  by (
    drule_then irule $
      cj 2 $ iffLR complete_lattice_def >>
    drule_then irule UNION_rel_SUBSET >>
    fs[poset_def,complete_lattice_def]) >>
  `∃y. lub (p,r) (UNION_func s x') y`
  by (
    drule_then irule $
      cj 2 $ iffLR complete_lattice_def >>
    drule_then irule UNION_rel_SUBSET >>
    fs[poset_def,complete_lattice_def]) >>
  drule_then imp_res_tac SELECT_lub >>
  simp[] >>
  conj_asm1_tac >- metis_tac[lub_IN] >>
  conj_asm1_tac >- metis_tac[lub_IN] >>
  (drule_last_then $ drule_last_then $ 
   drule_last_then $ drule_last_then irule)
    lub_UNION_func_mono_lem >>
  fs[complete_lattice_def,poset_def,SUBSET_DEF,IN_DEF]
QED

Theorem lub_UNION_rel_geq:
  p (f x) ∧
  s f ∧ p x ∧
  lub (p,r) (UNION_func s x) l ⇒
  r (f x) l
Proof
  rw[] >>
  gvs[lub_simp] >>
  first_x_assum irule >>
  fs[UNION_func_def] >>
  metis_tac[]
QED

Theorem exists_lub_UNION_func:
  complete_lattice (p,r) ∧
  (∀x. s x ⇒ monotone (p,r) x) ∧
  p x ⇒
  ∃y. lub (p,r) (UNION_func s x) y
Proof
  rw[complete_lattice_def] >>
  last_x_assum irule >>
  irule UNION_rel_SUBSET >>
  fs[poset_def,SUBSET_DEF,IN_DEF] >>
  metis_tac[]
QED

Theorem monotone_lift_lub:
  complete_lattice (p,r) ∧
  s ⊆ monotone_restricted (p,r) ==>
  lub (monotone_lift (p,r)) s
    (restrict p (\x. @l. lub (p,r) (UNION_func s x) l))
Proof
  rw[monotone_lift_def] >>
  simp[Once lub_simp] >>
  fs[SUBSET_DEF,IN_DEF,monotone_restricted_def] >>
  fs[restricted_restrict_thm,monotone_restrict] >>
  conj_asm1_tac
  >- (
    rw[ord_pointwise_def]
    >- (
      irule lub_UNION_func_monotone >>
      simp[SUBSET_DEF,IN_DEF]) >>
    DEP_REWRITE_TAC[restrict_thm] >>
    simp[] >>
    SELECT_ELIM_TAC >>
    rw[]
    >- metis_tac[exists_lub_UNION_func] >>
    drule_last_then irule lub_UNION_rel_geq >>
    simp[] >>
    irule monotone_closed >>
    fs[complete_lattice_def,poset_def] >>
    metis_tac[]
  ) >>
  rw[] >>
  gvs[ord_pointwise_def,restricted_restrict_thm,
    monotone_restrict] >>
  rw[] >>
  qpat_abbrev_tac `f =
    (λx. @l. lub (p,r) (UNION_func s x) l)` >>
  `lub (p,r) (UNION_func s x) (f x)`
  by (
    fs[Abbr`f`] >>
    SELECT_ELIM_TAC >>
    rw[] >>
    metis_tac[exists_lub_UNION_func]) >>
  qpat_x_assum `Abbrev _` kall_tac >>
  fs[lub_simp,UNION_func_def,restrict_thm] >>
  first_assum irule >>
  conj_asm1_tac >- (
    irule monotone_closed >>
    metis_tac[complete_lattice_def,poset_def]) >>
  rw[] >> fs[]
QED

Theorem monotone_lift_complete_lattice:
  complete_lattice (p,r) ⇒
  complete_lattice (monotone_lift (p,r))
Proof
  rw[complete_lattice_def,monotone_lift_def] >>
  metis_tac[complete_lattice_def,monotone_lift_def,
    monotone_lift_poset,monotone_lift_lub]
QED

Theorem monotone_I:
  monotone (d,r) I
Proof
  simp[monotone_def]
QED

Theorem monotone_o:
  monotone (d,r) f ∧ monotone (d,r) g ⇒
  monotone (d,r) (f o g)
Proof
  rw[monotone_def] >>
  metis_tac[]
QED

Definition post_fixpoint_def:
  post_fixpoint (p,r) f x ⇔ p x ∧ r x (f x)
End

Definition fixpoint_def:
  fixpoint f x ⇔ f x = x
End

Theorem fixpoint_restrict:
  d x ⇒
  (fixpoint (restrict d f) x ⇔ fixpoint f x)
Proof
  rw[fixpoint_def,restrict_thm]
QED

Definition gfp_def:
  gfp (p,r) f x ⇔ greatest (p ∩ fixpoint f) r x
End

Definition lfp_def:
  lfp (p,r) f x ⇔ least (p ∩ fixpoint f) r x
End

Theorem gfp_simp = SRULE[fixpoint_def,greatest_def,IN_DEF] gfp_def

Theorem lfp_simp = SRULE[fixpoint_def,least_def,IN_DEF] lfp_def

Theorem lub_SUBSET:
  BIGUNION s ∈ X ∧ s ⊆ X ⇒
  lub (X,$SUBSET) s (BIGUNION s)
Proof
  fs[lub_simp,BIGUNION,SUBSET_DEF,IN_DEF] >>
  metis_tac[]
QED

Theorem glb_SUBSET:
  BIGINTER s ∈ X ∧ s ⊆ X ⇒
  glb (X,$SUBSET) s (BIGINTER s)
Proof
  fs[glb_simp,BIGINTER,SUBSET_DEF,IN_DEF]
QED

Theorem complete_lattice_SUBSET:
  (∀s. s ⊆ X ⇒ BIGUNION s ∈ X) ⇒
  complete_lattice (X,$SUBSET)
Proof
  rw[complete_lattice_def]
  >- (
   rw[poset_simp]
   >- metis_tac[SUBSET_ANTISYM] >>
   metis_tac[SUBSET_TRANS]) >>
  irule_at (Pos hd) lub_SUBSET >>
  metis_tac[]
QED

Theorem lub_lub:
  complete_lattice (p,r) /\
  (!y. s y ⇒ y SUBSET p) ∧
  lub (p,r) {x | ?y. s y ∧ lub (p,r) y x} l ==>
  lub (p,r) (BIGUNION s) l
Proof
  strip_tac >>
  rw[lub_simp]
  >- metis_tac[lub_IN]
  >- (
    `s' SUBSET p` by metis_tac[SUBSET_DEF,IN_DEF] >>
    gvs[complete_lattice_def] >>
    last_assum $ drule_then strip_assume_tac >>
    qpat_x_assum `lub (p,r) _ l` $
      strip_assume_tac o SRULE[Once lub_simp] >>
    fs[poset_def,trans_set_def] >>
    last_x_assum irule >>
    simp[] >>
    `p g ∧ r y g` by (
      gvs[lub_simp] >> metis_tac[IN_DEF])>>
    first_assum $ irule_at (Pos hd) >>
    simp[] >>
    last_x_assum irule >>
    metis_tac[IN_DEF]) >>
  qpat_x_assum `lub (p,r) _ l` $
    strip_assume_tac o SRULE[Once lub_simp] >>
  first_x_assum irule >>
  rw[] >>
  pop_assum $ strip_assume_tac o SRULE[Once lub_simp] >>
  first_x_assum irule >>
  rw[] >>
  last_x_assum irule >>
  metis_tac[IN_DEF]
QED

Theorem glb_glb:
  complete_lattice (p,r) /\
  (!y. s y ⇒ y SUBSET p) ∧
  glb (p,r) {x | ?y. s y ∧ glb (p,r) y x} l ==>
  glb (p,r) (BIGUNION s) l
Proof
  simp[glb_alt] >>
  rw[] >>
  irule lub_lub >>
  simp[] >>
  metis_tac[complete_lattice_flip]
QED

Theorem knaster_tarski_gfp_lub:
  poset (p,r) ∧
  monotone (p,r) f ∧
  lub (p,r) (post_fixpoint (p,r) f) x ==>
  gfp (p,r) f x
Proof
  strip_tac >>
  `p x` by metis_tac[lub_IN] >>
  rw[gfp_simp]
  >- (
    gvs[lub_simp,post_fixpoint_def] >>
    `p (f x)` by
      metis_tac[monotone_closed,poset_def] >>
    `r x (f x)` by (
      last_x_assum irule >>
      rw[] >>
      last_x_assum $ drule_all_then assume_tac >>
      fs[monotone_def] >>
      `r (f y) (f x)` by metis_tac[] >>
      fs[poset_def,trans_set_def] >>
      metis_tac[]
    ) >>
    `r (f x) x` by (
      last_x_assum irule >>
      fs[monotone_def]
    ) >>
    fs[poset_def,antisym_set_def]
  ) >>
  gvs[lub_simp,post_fixpoint_def] >>
  last_x_assum irule >>
  fs[poset_def,refl_set_def]
QED

Theorem post_fixpoint_SUBSET:
  post_fixpoint (p,r) f ⊆ p
Proof
  gvs[SUBSET_DEF,IN_DEF,post_fixpoint_def]
QED

Theorem knaster_tarski_gfp_lub_thm:
  complete_lattice (p,r) ∧
  monotone (p,r) f ==> 
  gfp (p,r) f = lub (p,r) (post_fixpoint (p,r) f)
Proof
  rw[complete_lattice_def] >>
  `post_fixpoint (p,r) f ⊆ p`
    by irule post_fixpoint_SUBSET >>
  rw[EQ_IMP_THM,FUN_EQ_THM]
  >- (
    last_assum $ drule_then strip_assume_tac >>
    drule_all_then assume_tac knaster_tarski_gfp_lub >>
    `g = x` by (
      fs[gfp_def,poset_def] >>
      drule_last_then irule greatest_unique >>
      simp[] >>
      irule antisym_set_SUBSET >>
      last_assum $ irule_at (Pos last) >>
      metis_tac[INTER_SUBSET]) >>
    fs[]) >>
  metis_tac[knaster_tarski_gfp_lub]
QED

Theorem knaster_tarski_gfp_thm:
  complete_lattice (p,r) ∧
  monotone (p,r) f ⇒
  ?x. gfp (p,r) f x
Proof
  simp[knaster_tarski_gfp_lub_thm] >>
  rw[complete_lattice_def] >>
  last_assum irule >>
  metis_tac[post_fixpoint_SUBSET]
QED

Definition pre_fixpoint_def:
  pre_fixpoint (p,r) f x ⇔ p x ∧ r (f x) x
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

Theorem gfp_alt:
  gfp (p,r) = lfp (p,flip r)
Proof
  rw[gfp_def,lfp_def,FUN_EQ_THM] >>
  metis_tac[greatest_alt]
QED

Theorem lfp_alt:
  lfp (p,r) = gfp (p,flip r)
Proof
  simp[gfp_alt]
QED

Theorem knaster_tarski_lfp_glb:
  poset (p,r) ∧
  monotone (p,r) f ∧
  glb (p,r) (pre_fixpoint (p,r) f) x ==>
  lfp (p,r) f x
Proof
  qspec_then `flip r` assume_tac $
    Q.GEN `r` knaster_tarski_gfp_lub >>
  (* metis_tac[pre_fixpoint_alt,glb_alt,
  * lfp_alt,poset_flip,monotone_flip,
  * poset_def,monotone_closed] *)
  rw[pre_fixpoint_alt,glb_alt,lfp_alt] >>
  last_x_assum irule >>
  simp[] >>
  conj_tac >- drule_then irule poset_flip >>
  irule monotone_flip >>
  fs[poset_def] >>
  drule_then drule monotone_closed >>
  rw[]
QED

Theorem knaster_tarski_lfp_glb_thm:
  complete_lattice (p,r) ∧
  monotone (p,r) f ==> 
  lfp (p,r) f = glb (p,r) (pre_fixpoint (p,r) f)
Proof
  qspec_then `flip r` assume_tac $
    Q.GEN `r` knaster_tarski_gfp_lub_thm >>
  rw[lfp_alt,glb_alt,pre_fixpoint_alt] >>
  last_x_assum irule >>
  conj_tac >- metis_tac[complete_lattice_flip] >>
  irule monotone_flip >>
  metis_tac[monotone_def,complete_lattice_def,poset_def,
    monotone_closed]
QED

Theorem pre_fixpoint_SUBSET:
  pre_fixpoint (p,r) f ⊆ p
Proof
  simp[pre_fixpoint_def,SUBSET_DEF,IN_DEF]
QED

Theorem knaster_tarski_lfp_thm:
  complete_lattice (p,r) ∧
  monotone (p,r) f ⇒
  ?x. lfp (p,r) f x
Proof
  simp[knaster_tarski_lfp_glb_thm] >>
  rw[complete_lattice] >>
  last_assum irule >>
  metis_tac[pre_fixpoint_SUBSET]
(*
  qspec_then `flip r` assume_tac $
    Q.GEN `r` knaster_tarski_gfp_thm >>
  rw[glb_alt,lfp_alt] >>
  last_x_assum irule >>
  conj_tac >- drule_then irule complete_lattice_flip >>
  irule monotone_flip >>
  metis_tac[complete_lattice_def,poset_def,
    monotone_closed]
*)
QED

Theorem lfp_induction:
  complete_lattice (p,r) ∧
  monotone (p,r) f ∧
  lfp (p,r) f y ==>
  !x. p x ∧ r (f x) x ==> r y x
Proof
  rw[] >>
  drule_all_then (fn t => gvs[t]) $
    knaster_tarski_lfp_glb_thm >>
  gvs[glb_simp,pre_fixpoint_def]
QED

Theorem gfp_coinduction:
  complete_lattice (p,r) ∧
  monotone (p,r) f ∧
  gfp (p,r) f y ⇒
  !x. p x ∧ r x (f x) ⇒ r x y
Proof
  rw[] >>
  drule_all_then (fn t => gvs[t]) $
    knaster_tarski_gfp_lub_thm >>
  gvs[lub_simp,post_fixpoint_def]
QED

Theorem lfp_strong_induction:
  complete_lattice (p,r) ∧
  monotone (p,r) f ∧
  lfp (p,r) f y ∧
  glb (p,r) {f x;y} z /\
  p x ∧ r z x ==> r y x
Proof
  rw[] >>
  (drule_then $ drule_then $
    drule_then strip_assume_tac) lfp_induction >>
  `p z` by gvs[glb_simp] >>
  `p y` by (
    drule_all_then assume_tac
      knaster_tarski_lfp_glb_thm >>
    gvs[glb_simp]) >>
  `r y z` suffices_by (
    gvs[complete_lattice_def,poset_def,trans_set_def] >>
    metis_tac[]) >>
  first_assum irule >>
  gvs[glb_simp] >>
  last_x_assum irule >>
  conj_asm1_tac
  >- metis_tac[monotone_closed,
    complete_lattice_def,poset_def] >>
  rw[]
  >- fs[monotone_def] >>
  gvs[lfp_simp] >>
  `r z y` by metis_tac[] >>
  `r (f z) (f y)` by fs[monotone_def] >>
  gvs[]
QED

Theorem gfp_strong_coinduction:
  complete_lattice (p,r) ∧
  monotone (p,r) f ∧
  gfp (p,r) f y ∧
  lub (p,r) {f x;y} z /\
  p x ∧ r x z ==> r x y
Proof
  rw[gfp_alt,lub_alt] >>
  `refl_set p r` by fs[complete_lattice_def,poset_def] >>
  dxrule complete_lattice_flip >>
  drule monotone_flip >>
  rw[] >>
  drule lfp_strong_induction >>
  simp[] >>
  metis_tac[monotone_closed]
QED

Definition closed_interval_def:
  closed_interval (p,r) a b ⇔ \x. p x ∧ r a x ∧ r x b
End

Theorem closed_interval_lub:
  poset (p,r) ∧
  s ⊆ closed_interval (p,r) a b ∧
  p a ∧ p b ∧
  s x ∧ 
  lub (p,r) s l ⇒
  closed_interval (p,r) a b l
Proof
  rw[SUBSET_DEF,IN_DEF,closed_interval_def] >>
  gvs[lub_simp] >>
  last_x_assum drule >>
  rw[] >>
  `r x l` by fs[] >>
  fs[poset_def,trans_set_def] >>
  metis_tac[]
QED

Theorem complete_lattice_closed_interval:
  complete_lattice (p,r) ∧ p a ∧ p b ∧ r a b ⇒
  complete_lattice (closed_interval (p,r) a b,r)
Proof
  rw[complete_lattice_def] >>
  `closed_interval (p,r) a b ⊆ p` by
      rw[closed_interval_def,SUBSET_DEF,IN_DEF]
  >- metis_tac[poset_SUBSET] >>
  `s ⊆ p` by metis_tac[SUBSET_TRANS] >>
  last_assum drule >>
  rpt strip_tac >>
  Cases_on `?x. s x` >>
  gvs[]
  >- (
    qexists `g` >>
    rw[lub_simp]
    >- metis_tac[closed_interval_lub] >>
    gvs[lub_simp,SUBSET_DEF,IN_DEF]
  ) >>
  qexists `a` >>
  rw[closed_interval_def,lub_simp] >>
  metis_tac[poset_def,refl_set_def]
QED

Theorem closed_interval_monotone_SUBSET:
  poset (p,r) ∧
  monotone (p,r) f ∧
  w ⊆ fixpoint f ∧
  lub (p,r) w a ∧
  top (p,r) b ∧
  closed_interval (p,r) a b x ⇒
  closed_interval (p,r) a b (f x)
Proof
  simp[closed_interval_def] >>
  strip_tac >>
  conj_asm1_tac
  >- (
    gvs[monotone_def,poset_def,refl_set_def] >>
    metis_tac[]) >>
  gvs[fixpoint_def,SUBSET_DEF,lub_simp,IN_DEF] >>
  reverse $ conj_tac
  >- gvs[top_def] >>
  `p b` by gvs[top_def] >>
  `r (f a) (f x) ∧ p (f a)` by
    (fs[monotone_def] >> metis_tac[]) >>
  `r a (f a)` suffices_by (
    fs[poset_def,trans_set_def] >>
    metis_tac[]) >>
  last_x_assum irule >>
  rw[] >>
  `r y a` by metis_tac[] >>
  fs[monotone_def] >>
  last_x_assum drule_all >>
  strip_tac >>
  last_x_assum $ drule_then assume_tac >>
  fs[]
QED

Theorem gfp_lub_fixpoint:
  gfp (p,r) f x ⇒ lub (fixpoint f,r) p x
Proof
  rw[gfp_simp,lub_simp,IN_DEF,fixpoint_def]
QED

Theorem lfp_glb_fixpoint:
  lfp (p,r) f x ⇒ glb (fixpoint f,r) p x
Proof
  rw[lfp_simp,glb_simp,IN_DEF,fixpoint_def]
QED

Theorem least_closed_interval_lub_thm:
  trans_set p r ∧
  w ⊆ s ∧
  s ⊆ p ∧
  lub (p,r) w a ∧
  top (p,r) b ∧
  least (closed_interval (p,r) a b ∩ s) r x ⇒
  lub (s,r) w x
Proof
  rw[lub_simp,least_def,IN_DEF,closed_interval_def]
  >- (
    fs[trans_set_def] >>
    last_x_assum irule >>
    simp[] >>
    conj_asm1_tac
    >- (gvs[SUBSET_DEF,IN_DEF] >> metis_tac[]) >>
    qexists`a` >>
    metis_tac[]) >>
  last_x_assum irule >>
  gvs[SUBSET_DEF,IN_DEF,top_def]
QED

Theorem lfp_restrict:
  lfp (p,r) (restrict p f) x ⇔
  lfp (p,r) f x
Proof
  rw[lfp_simp,EQ_IMP_THM] >>
  gvs[restrict_def]
QED

Triviality closed_interval_INTER:
  closed_interval (p,r) a b ∩ p = closed_interval (p,r) a b
Proof
  rw[closed_interval_def,SUBSET_DEF,EXTENSION,IN_DEF,
    EQ_IMP_THM]
QED

Theorem knaster_tarski_thm:
  complete_lattice (p,r) ∧
  monotone (p,r) f ⇒
  complete_lattice (p ∩ fixpoint f,r)
Proof
  simp[complete_lattice_def] >>
  strip_tac >>
  `(p ∩ fixpoint f) ⊆ p` by simp[INTER_SUBSET] >>
  conj_asm1_tac
  >- drule_all_then irule poset_SUBSET >>
  rw[] >>
  irule_at (Pos hd) least_closed_interval_lub_thm >>
  simp[] >>
  first_assum $ irule_at (Pos $ el 2) >>
  rw[GSYM PULL_EXISTS] >- fs[poset_def] >>
  simp[GSYM lfp_def,top_lub,INTER_ASSOC] >>
  `p ⊆ p` by simp[] >>
  last_assum $ dxrule_then strip_assume_tac >>
  `s ⊆ p` by metis_tac[SUBSET_TRANS] >>
  last_assum $ dxrule_then strip_assume_tac >>
  ntac 2 $ first_assum (irule_at (Pos hd)) >>
  irule knaster_tarski_lfp_thm >>
  simp[closed_interval_INTER] >>
  conj_tac
  >- (
    irule complete_lattice_closed_interval >>
    fs[lub_simp,complete_lattice_def]) >>
  `closed_interval (p,r) g' g ⊆ p` by
    simp[closed_interval_def,SUBSET_DEF,IN_DEF] >>
  simp[monotone_def] >>
  rpt gen_tac >>
  strip_tac >>
  rev_drule_then (drule_then drule) $
    closed_interval_monotone_SUBSET >>
  simp[top_lub] >>
  disch_then kall_tac >>
  fs[closed_interval_def,monotone_def]
QED

Theorem gfp_coinduction_alt:
  complete_lattice (p,r) ∧ monotone (p,r) f ∧ gfp (p,r) f v ⇒ 
  ∀x y. p x ∧ p y ∧ r x y ∧ r y (f y) ⇒ r x v
Proof
  rw[] >>
  drule_all_then assume_tac gfp_coinduction >>
  gvs[complete_lattice_def,poset_def,trans_set_def] >>
  last_x_assum $ drule_last_then irule >>
  fs[gfp_def,greatest_def,IN_DEF]
QED

Definition compatible_def:
  compatible (p,r) b f ⇔
    monotone_restricted (p,r) f ∧
    ord_pointwise (p,r) (f o b) (b o f) 
End

Definition companion_def:
  companion (p,r) b =
  @l. lub (monotone_lift (p,r)) (compatible (p,r) b) l
End

Theorem compatible_I:
  complete_lattice (p,r) ∧ monotone_restricted (p,r) b ⇒
  compatible (p,r) b (restrict p I)
Proof
  rw[complete_lattice_def,poset_def,refl_set_def,
    monotone_restricted_def,restricted_restrict_thm,
    monotone_restrict,restrict_thm,
    compatible_def,monotone_I,ord_pointwise_def] >>
  `p (b x)` by metis_tac[monotone_closed,refl_set_def] >>
  simp[restrict_thm]
QED

Theorem compatible_b:
  complete_lattice (p,r) ∧ monotone_restricted (p,r) b ⇒
  compatible (p,r) b b
Proof
  rw[complete_lattice_def,poset_def,refl_set_def,
    compatible_def,monotone_I,ord_pointwise_def] >>
  metis_tac[monotone_closed,refl_set_def]
QED

Theorem compatible_o:
  complete_lattice (p,r) ∧ monotone (p,r) b ∧
  compatible (p,r) b f ∧ compatible (p,r) b g ⇒
  compatible (p,r) b (f o g)
Proof
  simp[complete_lattice_def,poset_def,
    compatible_def,ord_pointwise_def,monotone_o] >>
  rpt strip_tac >>
  qpat_x_assum `trans_set _ _` $
    markerLib.ASSUME_NAMED_TAC "trans" o
    SRULE[trans_set_def] >>
  markerLib.LABEL_ASSUM "trans" irule >>
  `p (g x)` by metis_tac[monotone_closed] >>
  first_assum $ drule_then $ irule_at (Pos last) >>
  `p (b x)` by metis_tac[monotone_closed] >>
  `r (g (b x)) (b (g x))`
    by (first_x_assum $ rev_drule_then irule) >>
  `p (g (b x))` by metis_tac[monotone_closed] >>
  `p (b (g x))` by metis_tac[monotone_closed] >>
  qpat_assum `monotone (p,r) f` $
    drule_all_then assume_tac o SRULE[monotone_def] >>
  simp[] >>
  ntac 5 $ pop_assum kall_tac >>
  `p (f (g x))` by metis_tac[monotone_closed] >>
  metis_tac[monotone_closed]
QED

Theorem compatible_lub:
  complete_lattice (p,r) ∧ monotone_restricted (p,r) b ∧
  s ⊆ compatible (p,r) b ∧
  lub (monotone_lift (p,r)) s l ⇒
  compatible (p,r) b l
Proof
  rw[compatible_def] >>
  fs[monotone_lift_def,lub_simp,monotone_restricted_def] >>
  fs[ord_pointwise_def,SUBSET_DEF,IN_DEF] >>
  rw[] >>
  fs[complete_lattice_def,poset_def] >>
  qpat_x_assum `trans_set _ _` $
    markerLib.ASSUME_NAMED_TAC "trans" o
    SRULE[trans_set_def] >>
  markerLib.LABEL_ASSUM "trans" irule >>
  conj_tac >- metis_tac[monotone_closed] >>
  conj_tac >- metis_tac[monotone_closed] >>
monotone_lift_lub
QED

Theorem monotone_companion:
Proof
QED

Theorem lub_unique:
  poset (p,r) ∧
  lub (p,r) s x ∧ lub (p,r) s y ⇒
  x = y
Proof
  rw[lub_def] >>
  drule_then irule poset_antisym >>
  simp[]
QED

val _ = export_theory ();
