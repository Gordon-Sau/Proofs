(* preorder set *)
open HolKernel boolLib bossLib BasicProvers dep_rewrite;
open pred_setTheory relationTheory;

val _ = new_theory "proset";

Definition refl_def:
  refl s r ⇔ (∀x. s x ⇒ r x x)
End

Definition trans_def:
  trans s r ⇔
    (∀x y z. s x ∧ s y ∧ s z ∧ r x y ∧ r y z ⇒ r x z)
End

Definition sym_def:
  sym s r ⇔ (∀x y. s x ∧ s y ⇒ (r x y ⇔ r y x))
End

Theorem equiv_on_refl_trans_sym:
  r equiv_on s ⇔ (refl s r ∧ trans s r ∧ sym s r)
Proof
  rw[equiv_on_def,EQ_IMP_THM,IN_DEF]
  >- metis_tac[refl_def]
  >- (
    PURE_REWRITE_TAC[trans_def] >>
    rpt strip_tac >>
    metis_tac[])
  >- metis_tac[sym_def]
  >- metis_tac[refl_def]
  >- metis_tac[sym_def]
  >- metis_tac[sym_def]
  >- (
    fs[trans_def] >>
    metis_tac[])
QED

Definition preorder_def:
  preorder s le = (refl s le ∧ trans s le)
End

Definition weq_def:
  weq le x y = (le x y ∧ le y x)
End

Theorem preorder_weq_refl:
  preorder s le ⇒
  refl s (weq le)
Proof
  simp[weq_def,preorder_def,refl_def]
QED

Theorem preorder_weq_sym:
  preorder s le ⇒
    sym s (weq le)
Proof
  rw[weq_def,preorder_def,sym_def] >>
  DECIDE_TAC
QED

Theorem preorder_flip:
  preorder s le ⇒
  preorder s (flip le)
Proof
  simp[preorder_def,refl_def,trans_def] >>
  metis_tac[]
QED

Theorem flip_flip:
  flip (flip f) = f
Proof
  simp[combinTheory.C_DEF] >>
  metis_tac[FUN_EQ_THM]
QED

Theorem preorder_unflip:
  preorder s (flip le) ⇒
  preorder s le
Proof
  strip_tac >>
  drule preorder_flip >>
  simp[flip_flip]
QED

Theorem preorder_weq_trans:
  preorder s le ⇒
    trans s (weq le)
Proof
  rw[weq_def,preorder_def,trans_def] >>
  metis_tac[]
QED

Theorem preorder_weq_equiv_on:
  preorder s le ⇒
  (weq le) equiv_on s
Proof
  strip_tac >>
  irule $ iffRL equiv_on_refl_trans_sym >>
  metis_tac[preorder_weq_refl,preorder_weq_sym,preorder_weq_trans]
QED

Definition indirect_eq_def:
  indirect_eq s le x y = (∀e. s e ⇒ (le e x ⇔ le e y))
End

Theorem indirect_eq_weq:
  preorder s le ∧ s x ∧ s y ⇒
  (indirect_eq s le x y ⇔ weq le x y)
Proof
  rw[EQ_IMP_THM,indirect_eq_def,weq_def] >>
  fs[IMP_CONJ_THM,FORALL_AND_THM] >>
  fs[preorder_def,refl_def] >>
  fs[trans_def] >>
  metis_tac[]
QED

Definition function_def:
   function a b (f : 'a -> 'b) = (∀x. a x ⇒ b (f x))
End

Definition pointwise_def:
  pointwise s r f g ⇔ (∀x. s x ⇒ r (f x) (g x))
End

Theorem preorder_pointwise:
  preorder s le ∧
  s' ⊆ function t s ⇒
  preorder s' (pointwise t le)
Proof
  rw[preorder_def,refl_def,pointwise_def,function_def,
    SUBSET_DEF,IN_DEF] >>
  rw[trans_def,pointwise_def,IN_DEF] >>
  drule_then irule $ iffLR trans_def >>
  conj_tac >- metis_tac[function_def] >>
  conj_tac >- metis_tac[function_def] >>
  first_x_assum $ drule_then (irule_at $ Pos last) >>
  metis_tac[function_def]
QED

Definition monotone_def:
  monotone s r f r' =
    ∀x y. s x ∧ s y ∧ r x y ==> r' (f x) (f y)
End

Theorem monotone_weq:
  monotone s r f r' ∧ function f s s' ∧
  s x ∧ s y ∧ weq r x y ⇒
    weq r' (f x) (f y)
Proof
  rw[weq_def] >>
  fs[monotone_def,function_def]
QED

Theorem monotone_flip:
  monotone s (flip r) f (flip r') ⇔
  monotone s r f r'
Proof
  simp[monotone_def] >>
  metis_tac[]
QED

val _ = export_theory();
