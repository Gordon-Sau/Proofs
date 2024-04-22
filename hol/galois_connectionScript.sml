open HolKernel boolLib bossLib BasicProvers dep_rewrite;
open pred_setTheory relationTheory;
open prosetTheory;

val _ = new_theory "galois_connection";

Definition galois_conn_def:
  galois_conn (s,r) (s',r') f g = (
    function s' s f ∧
    function s s' g ∧
    preorder s r ∧
    preorder s' r' ∧
    (∀x y. s' x ∧ s y ⇒ (r (f x) y ⇔ r' x (g y)))
  )
End

Theorem galois_conn_flip:
  galois_conn (s,r) (s',r') f g ⇔
    galois_conn (s',flip r') (s,flip r) g f
Proof
  rw[galois_conn_def,EQ_IMP_THM] >>
  metis_tac[preorder_flip,preorder_unflip]
QED

Theorem galois_conn_I:
  preorder s r ⇒
  galois_conn (s,r) (s,r) I I
Proof
  simp[galois_conn_def] >> simp[function_def]
QED

Theorem cancelGF:
  galois_conn (s,r) (s',r') f g ∧ s' x ⇒
  r' x (g (f x))
Proof
  rw[galois_conn_def] >>
  first_x_assum $ irule o iffLR >>
  fs[function_def,preorder_def,refl_def]
QED

Theorem cancelFG:
  galois_conn (s,r) (s',r') f g ∧ s y ⇒
  r (f (g y)) y
Proof
  rw[galois_conn_def,function_def,preorder_def,refl_def]
QED

Theorem galois_IMP_monotone_f:
  galois_conn (s,r) (s',r') f g ⇒ monotone s' r' f r
Proof
  rw[monotone_def] >>
  `s (f y)` by fs[galois_conn_def,function_def] >>
  drule_then strip_assume_tac $ iffLR galois_conn_def >>
  fs[preorder_def] >>
  drule_then irule (iffLR trans_def) >>
  fs[function_def] >>
  metis_tac[cancelGF]
QED

Theorem galois_IMP_monotone_g:
  galois_conn (s,r) (s',r') f g ⇒ monotone s r g r'
Proof
  strip_tac >>
  dxrule_then strip_assume_tac $ iffLR galois_conn_flip >>
  drule galois_IMP_monotone_f >>
  simp[monotone_flip]
QED

Theorem galois_conn_ore's_def:
  galois_conn (s,r) (s',r') f g ⇔ (
    function s' s f ∧
    function s s' g ∧
    preorder s r ∧
    preorder s' r' ∧
    monotone s' r' f r ∧
    monotone s r g r' ∧
    (∀x. s' x ⇒ r' x (g (f x))) ∧
    (∀y. s y ⇒ r (f (g y)) y)
  )
Proof
  iff_tac
  >- (
    strip_tac >>
    reverse $ rw[]
    >- metis_tac[cancelFG]
    >- metis_tac[cancelGF]
    >- metis_tac[galois_IMP_monotone_g]
    >- metis_tac[galois_IMP_monotone_f] >>
    metis_tac[galois_conn_def]
  ) >>
  rw[galois_conn_def] >>
  iff_tac
  >- (
    strip_tac >>
    fs[preorder_def] >>
    drule_then irule $ iffLR trans_def >>
    simp[] >>
    conj_tac >- metis_tac[function_def] >>
    first_x_assum $ drule_then (irule_at $ Pos $ el 2) >>
    conj_tac >- metis_tac[function_def] >>
    drule_then irule $ iffLR monotone_def >>
    simp[] >>
    metis_tac[function_def]
  ) >>
  strip_tac >>
  fs[preorder_def] >>
  drule_then irule $ iffLR trans_def >>
  simp[] >>
  conj_tac >- metis_tac[function_def] >>
  first_x_assum $ drule_then (irule_at $ Pos $ last) >>
  conj_tac >- metis_tac[function_def] >>
  drule_then irule $ iffLR monotone_def >>
  simp[] >>
  metis_tac[function_def]
QED

val _ = export_theory();
