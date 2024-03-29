open bossLib whileTheory pred_setTheory relationTheory optionTheory;
open arithmeticTheory numLib BasicProvers dep_rewrite;
open listTheory llistTheory itreeTauTheory;

(* 3 ways to think about Inductive sets.
* 1. the least fixed point such that X=F(X)
* 2. the smallest set that is closed forward (F(X) ⊆ X) (by Knaster-Tarski Thm)
* 3. the limit of keep applying F to {} (by Kleene fixed point thm)
* (keep adding elements to {} until it is closed)
* *)

Inductive even_list:
[~empty]
  even_list []
[~cons]
  (∀x xs. EVEN x ∧ even_list xs ⇒ even_list (x::xs))
End
even_list_rules;
even_list_cases;
even_list_ind;

(* F(X) = {[]} ∪ {y | y = x:: xs ∧ EVEN x ∧ xs ∈ X} *)
(* F(X) ⊆ X = {[]} ∪ {y | y = x:: xs ∧ EVEN x ∧ xs ∈ X} ⊆ X *)
(* = [] ∈ X ∧ (!y x xs. y = x::xs ∧ EVEN x ∧ xs ∈ X ⇒ y ∈ X *)
(* X ⊆ F(X) = X ⊆ ({[]} ∪ {x | x = y::ys ∧ EVEN y ∧ ys ∈ X}) *)
(* = ∀x. x ∈ X  ⇒ x = [] ∨ ∃y ys. x = y::ys ∧ EVEN y ∧ ys ∈ X *)

(* The smallest set S that satifies F(S) ⊆ S *)
(* ∀X. F(X) ⊆ X ⇒ S ⊆ X *) (* This is the induction principle *)
(* ∀X. [] ∈ X ∧ (!y x xs. y = x::xs ∧ EVEN x ∧ xs ∈ X ⇒ y ∈ X) ⇒
* (∀x. x ∈ S ⇒ x ∈ X) *)

Theorem even_list_example:
  even_list [0;2;4;6;8]
Proof
  rpt $ irule_at Any even_list_cons >>
  simp[] >>
  irule even_list_empty
QED

(* lets use llist (coinductiv/lazy list) instead *)
Inductive even_llist:
[~empty]
  even_llist [||] (* empty llist *)
[~cons]
  (∀x xs. EVEN x ∧ even_llist xs ⇒ even_llist (x:::xs))
  (* ::: is the cons for llist *)
End

(* should be similar to even_list as the predicate is essentially the same *)
Theorem even_llist_example:
  even_llist [|0;2;4;6;8|]
Proof
  rpt $ irule_at Any even_llist_cons >>
  simp[] >>
  irule even_llist_empty
QED

(* LUNFOLD is a way to create corecursive function.
* It is essentially unfold in Haskell.
* The second argument can be treated as the initial state.
* The first argument is applied on the initial state and
* return the next state, and the head of the list.
* We keep applying the function until we gets to NONE.
* This allows the list to be infinite as the function 
* may never return NONE *)
LUNFOLD;

Definition twos_def:
  twos = LUNFOLD (λu. SOME ((),2)) ()
End

Theorem twos:
  2:::twos = twos
Proof
  simp[twos_def] >>
  irule EQ_SYM >>
  simp[Once LUNFOLD]
QED

(* Try to prove this first *)
Theorem even_llist_twos:
  even_llist twos
Proof
  cheat
QED
(* It turns out that you cannot prove it. Why? *)

(* In fact, we can use induction to prove that `twos` 
* is not a even_llist *)
Theorem not_even_llist_twos:
  ¬even_llist twos 
Proof
  `∀l. even_llist l ⇒ l ≠ twos`
    suffices_by simp[] >>
  ho_match_mp_tac even_llist_ind >>
  simp[Once $ GSYM twos] >>
  rw[] >>
  simp[Once $ GSYM twos]
QED

(* so how should define even_llist? *)
CoInductive even_llist:
[~empty]
  even_llist [||]
[~cons]
  (∀x xs. EVEN x ∧ even_llist xs ⇒ even_llist (x:::xs))
End
even_llist_rules;
even_llist_cases;
even_llist_coind;
(* What theorems does this gives you?
* How is this different from the inductive version? *)

(* 3 ways to think about CoInductive sets.
* 1. the greatest fixed point such that X=F(X)
* 2. the largest set that is closed backward (X ⊆ F(X)) (by Knaster-Tarski Thm)
* 3. keep removing elements that does not satisfy the rule from UNIV
* until it is closed *)

(* The largest set S that satifies S ⊆ F(S) *)
(* ∀X. X ⊆ F(X) ⇒ X ⊆ S *) (* This is the coinduction principle *)
(* ∀X. (∀x. x ∈ X ⇒ x = [||] ∨ ∃y ys. x = y:::ys ∧ EVEN y ∧ ys ∈ X) ⇒
* (∀x. x ∈ X ⇒ x ∈ S) *)
(* A coinductive proof is essentially finding an X such that
* the thing you are proving is in X such and
* ∀x. x ∈ X ⇒ x = [||] ∨ ∃y ys. x = y:::ys ∧ EVEN y ∧ ys ∈ X *)
Theorem even_llist_example:
  even_llist [|0;2;4;6;8|]
Proof
  rpt $ irule_at Any even_llist_cons >>
  simp[] >>
  irule even_llist_empty
QED

(* hint: use even_llist_coind *)
(* Which set that is closed-backward should we choose? *)
Theorem even_llist_twos:
  even_llist twos
Proof
  irule even_llist_coind >>
  qexists `{twos}` >>
  simp[] >>
  `EVEN 2` by simp[] >>
  metis_tac[twos]
QED

Definition inc2_def:
  inc2 n = LUNFOLD (λn. SOME (n+2,n)) n 
End

Theorem inc2:
  n:::(inc2 $ n+2) = inc2 n
Proof
  simp[inc2_def] >>
  irule EQ_SYM >>
  simp[Once LUNFOLD]
QED

(* which set should we use? Is {inc2 0} closed-backward *)
Theorem even_llist_inc2:
  even_llist (inc2 0)
Proof
  irule even_llist_coind >>
  qexists `λl. ∃n. EVEN n ∧ l = inc2 n` >>
  rw[]
  >- (qexists`0` >> simp[]) >>
  disj2_tac >>
  simp[Once $ GSYM inc2] >>
  qexists `n+2` >>
  fs[EVEN_MOD2]
QED

Definition even_llist_prefix_def:
  even_llist_prefix 0 l = T ∧
  even_llist_prefix (SUC k) l =
    case l of
    | [||] => T
    | (h:::t) => EVEN h ∧ even_llist_prefix k t
End

Theorem even_llist_prefix_EQ_even_llist:
  even_llist l ⇔ ∀k. even_llist_prefix k l
Proof
  simp[EQ_IMP_THM] >>
  conj_tac
  >- (
    simp[PULL_FORALL] >>
    qid_spec_tac`l` >>
    Induct_on `k` >>
    rw[even_llist_prefix_def] >>
    CASE_TAC >>
    first_x_assum $ strip_assume_tac o
      SRULE[Once even_llist_cases] >>
    metis_tac[]
  ) >>
  qid_spec_tac `l` >>
  ho_match_mp_tac even_llist_coind >>
  rw[] >>
  Cases_on `l` >>
  rw[] >>
  pop_assum $ qspec_then `SUC k` assume_tac >>
  fs[even_llist_prefix_def]
QED

Theorem even_llist_prefix_inc2:
  ∀n. EVEN n ⇒ even_llist (inc2 n)
Proof
  simp[even_llist_prefix_EQ_even_llist,PULL_FORALL] >>
  Induct_on `k` >>
  rw[even_llist_prefix_def] >>
  simp[Once $ GSYM inc2] >>
  last_x_assum irule >>
  fs[EVEN_MOD2]
QED

Theorem even_llist_prefix_SUC:
  ∀n l. even_llist_prefix (SUC n) l ⇒ even_llist_prefix n l
Proof
  Induct_on `n` >>
  rw[even_llist_prefix_def] >>
  CASE_TAC >>
  gvs[even_llist_prefix_def]
QED

Theorem even_llist_prefix_complete:
  ∀n m l. even_llist_prefix n l ⇒ m < n ⇒ even_llist_prefix m l
Proof
  completeInduct_on `n` >>
  rw[] >>
  Cases_on `n` >- fs[] >>
  drule even_llist_prefix_SUC >>
  Cases_on `m = n'` >- rw[] >>
  `m < n'` by DECIDE_TAC >>
  last_x_assum $ qspec_then `n'` assume_tac >>
  fs[]
QED

(* This is essentially MEM, but in a predicate form *)
Inductive mem:
[~hd]
  (!x xs. mem x (x:::xs))
[~rest]
  (!x y xs. mem x xs ==> mem x (y:::xs))
End

(* What is the coinductive version of mem? *)
CoInductive comem:
[~hd]
  (!x xs. comem x (x:::xs))
[~rest]
  (!x y xs. comem x xs ==> comem x (y:::xs))
End

comem_coind;
(* we get the coinduction principle:
* (x,ys) ∈ S ⇒
* (∃xs. ys = x:::xs) ∨
* (∃y xs. ys = y:::xs ∧ (x,xs) ∈ S) *)

Theorem comem_inc2:
  comem x (inc2 n)
Proof
  irule comem_coind >>
  qexists `\x l. ?n. l = inc2 n` >>
  reverse $ rw[] >- metis_tac[] >>
  disj2_tac >>
  simp[Once $ GSYM inc2] >>
  metis_tac[]
QED

(* what happend when the second argument is not finite *)
Theorem inf_imp_comem:
  !x l. ~(LFINITE l) ==> comem x l
Proof
  rw[] >>
  irule comem_coind >>
  qexists `\x l. ~(LFINITE l)` >>
  rw[] >>
  disj2_tac >>
  last_x_assum kall_tac >>
  fs[LFINITE_LNTH_NONE] >>
  Cases_on `a1`
  >- (
    first_x_assum $ qspec_then `0` mp_tac >>
    simp[]
  ) >>
  irule_at (Pos hd) EQ_REFL >>
  rw[] >>
  metis_tac[LNTH_THM]
QED

CoInductive not_mem:
  (!x. not_mem x [||]) /\
  (!x y xs. not_mem x xs /\ y <> x ==> not_mem x (y:::xs))
End

not_mem_coind;

Theorem not_mem_LNTH:
  not_mem x l <=> !n. LNTH n l <> SOME x
Proof
  eq_tac
  >- (
    simp[PULL_FORALL] >>
    qid_spec_tac `l` >>
    qid_spec_tac `x` >>
    Induct_on `n` >>
    Cases_on `l` >>
    rw[LNTH_THM] >>
    drule $ iffLR not_mem_cases >>
    simp[]
  ) >>
  strip_tac >>
  irule not_mem_coind >>
  qexists `\x l. !n. LNTH n l <> SOME x` >>
  rw[] >>
  Cases_on `a1` >>
  rw[]
  >- (
    first_x_assum $ qspec_then `SUC n` mp_tac >>
    simp[LNTH_THM]
  ) >>
  first_x_assum $ qspec_then `0` mp_tac >>
  simp[LNTH_THM]
QED

(* Is this a coincidence that
* you can define the negation of inductive predicate
* as a coinductive predicate? *)
Theorem mem_not_mem:
  mem x l <=> ~(not_mem x l)
Proof
  eq_tac
  >- (
    qid_spec_tac `l` >>
    qid_spec_tac `x` >>
    ho_match_mp_tac mem_ind >>
    rw[]
    >- (
      strip_tac >>
      drule $ iffLR not_mem_cases >>
      simp[]
    ) >>
    strip_tac >>
    drule $ iffLR not_mem_cases >>
    simp[]
  ) >>
  CONV_TAC CONTRAPOS_CONV >>
  rw[] >>
  irule not_mem_coind >>
  qexists `\x l. ~(mem x l)` >>
  rw[] >>
  last_x_assum kall_tac >>
  Cases_on `a1` >>
  simp[] >>
  rpt strip_tac
  >- (
    last_x_assum mp_tac >>
    simp[] >>
    irule $ cj 2 mem_rules >>
    simp[]) >>
  last_x_assum mp_tac >>
  simp[] >>
  irule $ cj 1 mem_rules
QED

(* Prove this with coinduction *)
Theorem not_mem_inc2:
  ∀n. ¬EVEN n ⇒ not_mem n (inc2 0)
Proof
  rw[] >>
  irule not_mem_coind >>
  qexists `λk l. k = n ∧ ∃m. EVEN m ∧ l = inc2 m` >>
  rw[]
  >- (
    disj2_tac >>
    simp[Once $ GSYM inc2] >>
    conj_tac
    >- (
      qexists `m+2` >>
      fs[EVEN_MOD2]
    ) >>
    strip_tac >>
    fs[]
  ) >>
  qexists `0` >>
  simp[]
QED

(* Can you use induction to prove this using mem_not_mem? *)
Theorem not_mem_inc2:
  ∀n. ¬EVEN n ⇒ not_mem n (inc2 0)
Proof
  rw[] >>
  irule $ SRULE[] $ CONTRAPOS $ iffRL mem_not_mem >>
  `!n l. mem n l ⇒ (¬ EVEN n ∧ (∃m. EVEN m ∧ l = inc2 m)) ⇒ F`
    suffices_by (
      rpt strip_tac >>
      `EVEN 0` by simp[] >>
      metis_tac[]
    ) >>
  pop_assum kall_tac >>
  ho_match_mp_tac mem_ind >>
  rw[]
  >- (
    Cases_on `EVEN n` >>
    rw[] >>
    fs[Once $ GSYM inc2])
  >- simp[] >>
  disj2_tac >>
  rw[] >>
  pop_assum $ strip_assume_tac o SRULE[Once $ GSYM inc2] >>
  strip_tac >>
  last_x_assum drule >>
  fs[EVEN_MOD2]
QED

(* bisimilarity *)
Definition odds_def:
  odds l = LUNFOLD
    (λol. OPTION_BIND ol
      (λl. OPTION_MAP
        (\v. (LDROP 2 l,v)) $
        LHD l))
    (SOME l)
End

Definition evens_def:
  evens l =
    case LTL l of
      | NONE => [||]
      | SOME tl => odds tl
End

Definition merge_def:
  merge l l' = LUNFOLD (λp.
    case p of
      | ([||],[||]) => NONE
      | ([||],x:::xs) => SOME (([||],xs),x)
      | (x:::xs,ys) => SOME ((ys,xs),x)) (l,l')
End

Theorem odds:
  (odds [||] = [||]) ∧
  (∀x. odds [|x|] = [|x|]) ∧
  (∀x y zs. odds (x:::y:::zs) = x:::odds zs)
Proof
  rw[] >>
  simp[odds_def,Once LUNFOLD]
  >- (
    irule $ cj 1 LUNFOLD_THM >>
    simp[] >>
    disj1_tac >>
    PURE_REWRITE_TAC[DECIDE``2=SUC 1``,LDROP] >>
    simp[] >>
    PURE_REWRITE_TAC[DECIDE``1=SUC 0``,LDROP] >>
    simp[]
  ) >>
  AP_TERM_TAC >>
  PURE_REWRITE_TAC[DECIDE``2=SUC 1``,LDROP] >>
  simp[]
QED

Theorem odds_example:
  odds [|1;2;3;4;5|] = [|1;3;5|] ∧
  odds [|0;1;2;3;4;5|] = [|0;2;4|]
Proof
  simp[odds]
QED

Theorem evens_to_odds:
  (evens [||] = [||]) ∧
  (∀x ys. evens (x:::ys) = odds ys)
Proof
  rw[] >>
  simp[evens_def]
QED

Theorem evens:
  (evens [||] = [||]) ∧
  (∀x. evens [|x|] = [||]) ∧
  (!x y zs. evens (x:::y:::zs) = y:::evens zs)
Proof
  simp[evens_to_odds,odds] >>
  Cases_on `zs` >>
  simp[evens_to_odds,odds]
QED

Theorem merge:
  (!(l:'a llist) t. merge [||] l = l) ∧
  (!(lh:'a) lt r. merge (lh:::lt) r = lh:::merge r lt)
Proof
  conj_tac
  >- (
    rw[Once LLIST_BISIMULATION] >>
    qexists `\m l. m = merge [||] l` >>
    rw[] >>
    Cases_on `ll4` >>
    fs[] >>
    simp[merge_def,Once LUNFOLD]) >>
  fs[merge_def] >>
  simp[Once LUNFOLD]
QED

Theorem merge_odds_evens:
  merge (odds l) (evens l) = l
Proof
  simp[Once LLIST_BISIMULATION0] >>
  qexists `\x y. x = merge (odds y) (evens y)` >>
  rw[] >>
  Cases_on `ll4` >>
  simp[odds,evens,merge] >>
  Cases_on `t` >>
  simp[odds,merge,evens_to_odds]
QED

Theorem merge_odds_evens_LTAKE:
  merge (odds l) (evens l) = l
Proof
  irule $ iffRL LTAKE_EQ >>
  qid_spec_tac `l` >>
  completeInduct_on `n` >>
  rw[] >>
  Cases_on `l` >>
  simp[odds,evens,merge] >>
  Cases_on `t` >>
  simp[odds,evens,merge] >>
  Cases_on `n` >>
  simp[] >>
  Cases_on `n'` >>
  simp[]
QED

(* LAPPEND is similarly to itree_bind *)
LAPPEND;

Theorem even_llist_LAPPEND:
  even_llist l ∧ even_llist r ⇒
  even_llist (LAPPEND l r)
Proof
  rw[] >>
  irule even_llist_coind >>
  qexists `\l. ∃l' r. l = LAPPEND l' r ∧ even_llist l' ∧ even_llist r` >>
  rw[]
  >- metis_tac[] >>
  ntac 2 $ last_x_assum kall_tac >>
  Cases_on `l'`
  >- (
    fs[Once $ even_llist_cases] >>
    qexistsl[`[||]`,`xs`] >>
    simp[]) >>
  last_x_assum $
    assume_tac o SRULE[Once even_llist_cases] >>
  simp[] >>
  metis_tac[]
QED

Theorem mem_LAPPEND:
  ∀x l. mem x l ⇒ mem x (LAPPEND l r)
Proof
  Induct_on `mem` >>
  rw[mem_rules]
QED

Theorem mem_LAPPEND_1_LFINITE:
  ∀x l. LFINITE l ∧ mem x r ⇒ mem x (LAPPEND l r)
Proof
  Induct_on `LFINITE` >>
  rw[mem_rules]
QED

Theorem LAPPEND_INFINITE:
  ¬LFINITE l ⇒ LAPPEND l x = l
Proof
  rw[Once LLIST_BISIMULATION0] >>
  qexists `\x y. ¬LFINITE y ∧ ?z. x = LAPPEND y z` >>
  rw[]
  >- metis_tac[] >>
  last_x_assum kall_tac >>
  Cases_on `ll4` >>
  fs[] >>
  metis_tac[]
QED

Theorem mem_LAPPEND_IMP:
  ∀x l r. mem x (LAPPEND l r) ⇒ mem x l ∨ (LFINITE l ∧ mem x r)
Proof
  rw[] >>
  Cases_on `mem x l` >>
  simp[] >>
  reverse $ Cases_on `LFINITE l`
  >- metis_tac[LAPPEND_INFINITE] >>
  simp[] >>
  rpt $ pop_assum mp_tac >>
  Induct_on `LFINITE` >>
  rw[] >>
  `h ≠ x` by fs[Once mem_cases] >>
  `mem x (LAPPEND l r)` by fs[Once mem_cases] >>
  metis_tac[mem_cases]
QED

(* remove NONE finitely many times.
* Note that head on the left hand side cannot be NONE *)
Inductive strip_NONE:
[~some]
  strip_NONE (SOME x:::l) (SOME x:::l)
[~nil]
  strip_NONE [||] [||]
[~strip]
  strip_NONE l l' ⇒ strip_NONE (NONE:::l) l'
End

(* To make life easier. You can use
* ``Cases_on `blah` using optoin_list_CASES``
* to get all the three cases at once *)
Theorem option_list_CASES:
  ∀ol. (∃h l. ol = SOME h:::l) ∨ (∃l. ol = NONE:::l) ∨ ol = [||]
Proof
  gen_tac >>
  Cases_on `ol` >>
  simp[] >>
  Cases_on `h` >>
  simp[]
QED

(* weak bisimilar for llist *)
(* We can ignore finitely many taus. But if there
* are infinite taus, we want to keep it as it represents
* divergent process *)
CoInductive llist_wbisim:
[~tau]
  llist_wbisim l l' ⇒ llist_wbisim (NONE:::l) (NONE:::l')
[~nil]
  strip_NONE t [||] ∧ strip_NONE t' [||] ⇒ 
  llist_wbisim t t'
[~cons]
  llist_wbisim l l' ∧
  strip_NONE xl (SOME x:::l) ∧
  strip_NONE xl' (SOME x:::l') ⇒
  llist_wbisim xl xl'
End

Theorem strip_NONE_NONE[simp]:
  ∀l l'. strip_NONE (NONE:::l) l' <=> strip_NONE l l'
Proof
  rw[EQ_IMP_THM]
  >- last_x_assum $ strip_assume_tac o
    SRULE[Once strip_NONE_cases] >>
  metis_tac[strip_NONE_rules]
QED

Theorem llist_wbisim_refl:
  llist_wbisim l l
Proof
  irule llist_wbisim_coind >>
  qexists `\l l'. l = l'` >>
  rw[] >>
  Cases_on `a0` using option_list_CASES >>
  metis_tac[strip_NONE_rules]
QED

Theorem llist_wbisim_sym:
  ∀l' l. llist_wbisim l l' ⇒ llist_wbisim l' l
Proof
  ho_match_mp_tac llist_wbisim_coind >>
  rw[] >>
  last_x_assum $ strip_assume_tac o
    SRULE[Once $ llist_wbisim_cases] >>
  metis_tac[]
QED

Theorem llist_wbisim_NONE_eq:
  llist_wbisim (NONE:::l) l
Proof
  irule llist_wbisim_coind >>
  qexists `\l l'. l = l' ∨ l = NONE:::l'` >>
  rw[]
  >- (
    Cases_on `a0` using option_list_CASES >>
    metis_tac[llist_wbisim_rules,strip_NONE_rules,llist_wbisim_refl]) >>
  Cases_on `a1` using option_list_CASES >>
  metis_tac[llist_wbisim_rules,strip_NONE_rules,llist_wbisim_refl]
QED

Theorem IMP_llist_wbisim_NONE:
  llist_wbisim l l' ⇒ llist_wbisim l (NONE:::l')
Proof
  rw[] >>
  irule llist_wbisim_coind >>
  qexists `\l l'. llist_wbisim l l' ∨ (∃l''. llist_wbisim l l'' ∧ l'=NONE:::l'')` >>
  rw[] >>
  last_x_assum kall_tac >>
  simp[PULL_EXISTS]
  >- (
    Cases_on `a1` using option_list_CASES >>
    pop_assum $ strip_assume_tac o
        SRULE[Once llist_wbisim_cases] >>
    metis_tac[strip_NONE_strip]) >>
  Cases_on `l''` using option_list_CASES >>
  pop_assum $ strip_assume_tac o
    SRULE[Once llist_wbisim_cases] >>
  metis_tac[strip_NONE_strip]
QED

Theorem llist_wbisim_NONE[simp]:
  (∀(l:'a option llist) l'. llist_wbisim (NONE:::l) l' <=> llist_wbisim l l') ∧
  (∀(l:'a option llist) l'. llist_wbisim l (NONE:::l') ⇔ llist_wbisim l l')
Proof
  conj_asm1_tac
  >- (
    rw[EQ_IMP_THM]
    >- (
      last_x_assum $ strip_assume_tac o
        SRULE[Once llist_wbisim_cases]
      >- metis_tac[IMP_llist_wbisim_NONE] >>
      metis_tac[llist_wbisim_rules,strip_NONE_NONE]
    ) >>
    metis_tac[IMP_llist_wbisim_NONE,llist_wbisim_sym]) >>
  metis_tac[llist_wbisim_sym]
QED

Theorem strip_NONE_unique:
  ∀l l' l''. strip_NONE l l' ∧ strip_NONE l l'' ⇒ l' = l''
Proof
  Induct_on `strip_NONE` >>
  rw[] >>
  fs[Once strip_NONE_cases]
QED

Theorem llist_wbisim_strip_NONE:
  !t t' t''. llist_wbisim t t' /\ strip_NONE t t'' ==> llist_wbisim t'' t'
Proof
  Induct_on `strip_NONE` >>
  rw[]
QED

Theorem llist_wbisim_strip_NONE_2:
  !t t' t''. llist_wbisim t t' /\ strip_NONE t' t'' ==> llist_wbisim t t''
Proof
  Induct_on `strip_NONE` >>
  rw[]
QED

Theorem llist_wbisim_strip_NONE_nil:
  ∀t t'. llist_wbisim t t' ∧ strip_NONE t [||] ⇒
  strip_NONE t' [||]
Proof
  Induct_on `strip_NONE` >> rw[] >>
  fs[Once llist_wbisim_cases] >>
  fs[Once strip_NONE_cases]
QED

Theorem llist_wbisim_strip_NONE_cons_SOME:
  ∀t t'. llist_wbisim t t' ∧ strip_NONE t (SOME h:::l) ⇒
  ∃l'. strip_NONE t' (SOME h:::l') ∧ llist_wbisim l l'
Proof
  Induct_on `strip_NONE` >> rw[] >>
  imp_res_tac $ cj 1 llist_wbisim_NONE >>
  gvs[Once llist_wbisim_cases] >>
  fs[Once strip_NONE_cases] >>
  metis_tac[]
QED

(* There are quite a lot of cases in this proof *)
Theorem llist_wbisim_trans:
  llist_wbisim l l' ∧ llist_wbisim l' l'' ⇒
  llist_wbisim l l''
Proof
  rw[] >>
  irule llist_wbisim_coind >>
  qexists `\l l''. ∃l'.
    llist_wbisim l l' ∧ llist_wbisim l' l''` >>
  reverse $ rw[]
  >- metis_tac[] >>
  ntac 2 $ last_x_assum kall_tac >>
  Cases_on `a0` using option_list_CASES >>
  rw[]
  >- (
    last_x_assum $ strip_assume_tac o
      SRULE[Once $ llist_wbisim_cases] >>
    gvs[strip_NONE_NONE]
    >- metis_tac[llist_wbisim_strip_NONE_nil]
    >- metis_tac[llist_wbisim_strip_NONE_cons_SOME])
  >- (
    gvs[llist_wbisim_NONE_eq] >>
    last_x_assum $ strip_assume_tac o
      SRULE[Once $ llist_wbisim_cases] >>
    last_x_assum $ strip_assume_tac o
      SRULE[Once llist_wbisim_cases] >>
    gvs[strip_NONE_NONE]
    >- metis_tac[]
    >- metis_tac[llist_wbisim_sym,llist_wbisim_strip_NONE_nil]
    >- (
      disj2_tac >> disj2_tac >>
      metis_tac[llist_wbisim_sym,llist_wbisim_strip_NONE_cons_SOME])
    >- metis_tac[llist_wbisim_strip_NONE_nil]
    >- metis_tac[strip_NONE_unique,LLIST_DISTINCT]
    >- metis_tac[llist_wbisim_strip_NONE_cons_SOME]
    >- metis_tac[strip_NONE_unique,LLIST_DISTINCT]
    >- metis_tac[strip_NONE_unique,LCONS_11,
      llist_wbisim_strip_NONE_cons_SOME]
  )
  >- (
    last_x_assum $ strip_assume_tac o
      SRULE[Once $ llist_wbisim_cases]
    >- metis_tac[llist_wbisim_strip_NONE_nil]
    >- fs[Once strip_NONE_cases]
  )
QED

Theorem strip_NONE_LAPPEND_SOME_strip_NONE:
  ∀a x l b. strip_NONE a (SOME x:::l) ⇒
    strip_NONE (LAPPEND a b) (SOME x ::: LAPPEND l b) 
Proof
  Induct_on `strip_NONE` >>
  rw[strip_NONE_rules]
QED

Theorem strip_NONE_LAPPEND_nil_strip_NONE:
  ∀a. strip_NONE a [||] ∧ strip_NONE b b' ⇒
  strip_NONE (LAPPEND a b) b'
Proof
  Induct_on `strip_NONE` >>
  rw[strip_NONE_NONE]
QED

Theorem strip_NONE_nil_LAPPEND_NONE:
  ∀a l. strip_NONE a [||] ⇒
    ∃l'. LAPPEND a (NONE:::l) = NONE:::l' ∧ 
    llist_wbisim l' l
Proof
  Induct_on `strip_NONE` >>
  rw[llist_wbisim_refl] >>
  pop_assum $ qspec_then `l` strip_assume_tac >>
  simp[]
QED

Theorem LAPPEND_llist_wbisim:
  llist_wbisim l l' ∧ llist_wbisim r r' ⇒
  llist_wbisim (LAPPEND l r) (LAPPEND l' r')
Proof
  strip_tac >>
  irule llist_wbisim_coind >>
  qexists `\l l'. (∃a b a' b'.
    l = LAPPEND a b ∧ l' = LAPPEND a' b' ∧
    llist_wbisim a a' ∧ llist_wbisim b b') ∨
    llist_wbisim l l'` >>
  reverse $ rw[]
  >- metis_tac[] >>
  ntac 2 $ last_x_assum kall_tac
  >- (
    last_x_assum $ strip_assume_tac o
      SRULE[Once llist_wbisim_cases] >>
    metis_tac[]
  ) >>
  last_x_assum $ strip_assume_tac o
    SRULE[Once llist_wbisim_cases]
  >- metis_tac[LAPPEND]
  >- (
    last_x_assum $ strip_assume_tac o
      SRULE[Once llist_wbisim_cases]
    >- (
      disj1_tac >>
      simp[] >>
      rev_drule_then (qspec_then `l` strip_assume_tac)
        strip_NONE_nil_LAPPEND_NONE >>
      drule_then (qspec_then `l'` strip_assume_tac)
        strip_NONE_nil_LAPPEND_NONE >>
      simp[] >>
      metis_tac[llist_wbisim_trans,llist_wbisim_sym]
    ) >>
    metis_tac[strip_NONE_LAPPEND_nil_strip_NONE]
  ) >>
  metis_tac[strip_NONE_LAPPEND_SOME_strip_NONE]
QED

CoInductive even_ollist:
[~empty]
  even_ollist [||]
[~cons]
  (∀x xs. EVEN x ∧ even_ollist xs ⇒ even_ollist (SOME x:::xs))
[~none]
  (∀xs. even_ollist xs ⇒ even_ollist (NONE:::xs))
End

Theorem even_ollist_NONE[simp]:
  even_ollist (NONE:::xs) = even_ollist xs
Proof
  rw[EQ_IMP_THM,even_ollist_rules] >>
  pop_assum $ strip_assume_tac o
    SRULE[Once even_ollist_cases]
QED

Theorem even_ollist_strip_NONE:
  ∀l l'. strip_NONE l l' ∧ even_ollist l' ⇒ even_ollist l
Proof
  Induct_on `strip_NONE` >>
  rw[]
QED

Theorem even_ollist_strip_NONE_2:
  ∀l l'. strip_NONE l l' ∧ even_ollist l ⇒ even_ollist l'
Proof
  Induct_on `strip_NONE` >>
  rw[]
QED

(* you may need some lemmas about even_ollist and strip_NONE *)
Theorem wbisim_imp_even_ollist:
  ∀l' l. even_ollist l ∧ llist_wbisim l l' ⇒ even_ollist l'
Proof
  `∀l'. (?l. even_ollist l ∧ llist_wbisim l l') ⇒ even_ollist l'`
    suffices_by metis_tac[] >>
  ho_match_mp_tac even_ollist_coind >>
  rw[] >>
  fs[Once even_llist_cases,Once llist_wbisim_cases]
  >- metis_tac[llist_wbisim_NONE]
  >- (
    fs[Once strip_NONE_cases] >>
    fs[] >>
    metis_tac[llist_wbisim_refl,
      even_ollist_strip_NONE,even_ollist_rules]) >>
  Cases_on `l'` using option_list_CASES >>
  simp[]
  >- (
    pop_assum $ strip_assume_tac o
      SRULE[Once strip_NONE_cases] >>
    fs[] >>
    drule_all even_ollist_strip_NONE_2 >>
    rw[Once even_ollist_cases] >>
    qexists `l''` >>
    qpat_x_assum `llist_wbisim _ _` $ strip_assume_tac o
      SRULE[Once llist_wbisim_cases] >>
    simp[] >>
    metis_tac[]
  )
  >- (
    `llist_wbisim (SOME x:::l'') (SOME x:::l''')` by
      metis_tac[llist_wbisim_rules,strip_NONE_rules] >>
    first_assum $ irule_at (Pos hd) >>
    irule llist_wbisim_trans >>
    irule_at (Pos hd) llist_wbisim_strip_NONE_2 >>
    irule_at (Pos hd) llist_wbisim_refl >>
    first_assum $ irule_at (Pos hd) >>
    irule llist_wbisim_trans >>
    first_assum $ irule_at (Pos hd) >>
    irule llist_wbisim_strip_NONE >>
    fs[] >>
    metis_tac[llist_wbisim_refl]
  )
QED

Theorem even_ollist_LAPPEND:
  even_ollist l ∧ even_ollist l' ⇒
  even_ollist (LAPPEND l l')
Proof
  rpt strip_tac >>
  irule even_ollist_coind >>
  qexists `\ll. ?l l'. ll = LAPPEND l l' ∧ even_ollist l ∧ even_ollist l'` >>
  rw[]
  >- metis_tac[] >>
  ntac 2 $ last_x_assum kall_tac >>
  last_x_assum $ strip_assume_tac o
    SRULE[Once even_ollist_cases] >>
  fs[]
  >- (
    last_x_assum $ strip_assume_tac o
      SRULE[Once even_ollist_cases] >>
    simp[] >>
    qexistsl [`[||]`,`xs`] >>
    simp[even_ollist_rules]
  ) >>
  metis_tac[]  
QED

Theorem LAPPEND_ASSOC:
  LAPPEND (LAPPEND x y) z = LAPPEND x (LAPPEND y z)
Proof
  simp[Once LLIST_STRONG_BISIMULATION] >>
  qexists `\l1 l2. ?x y z.
      l1 = LAPPEND (LAPPEND x y) z ∧
      l2 = LAPPEND x (LAPPEND y z)` >>
  rw[]
  >- metis_tac[] >>
  Cases_on `x` >>
  simp[] >>
  metis_tac[]
QED

Theorem LFINITE_LAPPEND_LLENGTH:
  ∀x y n m. LFINITE x ∧ LFINITE y ∧
  LLENGTH x = SOME n ∧ LLENGTH y = SOME m ⇒
  LLENGTH (LAPPEND x y) = SOME (n + m)
Proof
  Induct_on `LFINITE` >>
  rw[] >>
  last_x_assum $ drule_all_then strip_assume_tac >>
  simp[]
QED

Theorem LLENGTH_LAPPEND:
  LLENGTH (LAPPEND x y) = OPTION_MAP2 $+ (LLENGTH x) (LLENGTH y)
Proof
  reverse $ Cases_on `LFINITE x`
  >- (
    drule_then (fn t => simp[t]) LAPPEND_INFINITE >>
    simp[LLENGTH]
  ) >>
  reverse $ Cases_on `LFINITE y` >>
  imp_res_tac LFINITE_HAS_LENGTH
  >- simp[LLENGTH] >>
  simp[] >>
  metis_tac[LFINITE_LAPPEND_LLENGTH,ADD_COMM]
QED

open pairTheory llistTheory;

Theorem LUNFOLD_Fusion:
  g o f = OPTION_MAP (f ## I) o h ⇒
  LUNFOLD g o f = LUNFOLD h
Proof
  rw[PULL_FORALL,FUN_EQ_THM] >>
  irule $ iffRL LUNFOLD_BISIMULATION >>
  qexists `\fx x. fx = f x` >>
  rw[] >>
  Cases_on `h y2` >>
  rw[] >>
  Cases_on `x` >>
  simp[]
QED

Theorem LUNFOLD_Fusion:
  g o f = OPTION_MAP (f ## I) o h ⇒
  LUNFOLD g o f = LUNFOLD h
Proof
  rw[PULL_FORALL,FUN_EQ_THM] >>
  irule $ iffRL LLIST_BISIMULATION >>
  qexists `\gl hl. ∃x. gl = LUNFOLD g (f x) ∧ hl = LUNFOLD h x` >>
  rw[combinTheory.o_DEF]
  >- metis_tac[] >>
  Cases_on `LUNFOLD g (f x)` >>
  rw[]
  >- (
    pop_assum $ strip_assume_tac o SRULE[Once LUNFOLD] >>
    gvs[AllCaseEqs()] >>
    simp[LUNFOLD_THM]
  )
  >- (
    pop_assum $ strip_assume_tac o SRULE[Once LUNFOLD] >>
    gvs[AllCaseEqs()] >>
    Cases_on `z` >>  
    fs[PAIR_MAP_THM]
  ) >>
  Cases_on `h x` >>
  simp[combinTheory.o_DEF]
  >- (
    qpat_x_assum `LUNFOLD g (f x) = _` $ strip_assume_tac o
      SRULE[Once LUNFOLD] >>
    gvs[AllCaseEqs()]
  ) >>
  Cases_on `x'` >>
  simp[] >>
  qpat_x_assum `LUNFOLD g (f x) = _` $ strip_assume_tac o
    SRULE[Once LUNFOLD] >>
  gvs[AllCaseEqs()] >>
  metis_tac[]
QED

Theorem LUNFOLD_I:
  LUNFOLD
  (\l. case l of
       | [||] => NONE
       | (h:::t) => SOME (t,h)) = I
Proof
  rw[FUN_EQ_THM] >>
  irule $ iffRL LLIST_BISIMULATION >>
  qexists `\lx x. lx = LUNFOLD
  (\l. case l of
       | [||] => NONE
       | (h:::t) => SOME (t,h)) x` >>
  rw[] >>
  CASE_TAC >>
  gvs[] >>
  simp[Once LUNFOLD]
QED

Theorem o_I_LUNFOLD:
  f o g = I ⇒
  LUNFOLD h o f = LUNFOLD (OPTION_MAP (g ## I) o h o f) 
Proof
  rw[FUN_EQ_THM] >>
  irule $ iffRL LUNFOLD_BISIMULATION >>
  qexists `\fx x. fx = f x` >>
  rw[] >>
  Cases_on `h (f y2)` >>
  simp[] >>
  Cases_on `x` >>
  simp[]
QED

Theorem SURJ_LUNFOLD:
  f o g = I ⇒
  f = LUNFOLD (OPTION_MAP (g ## I) o
        (\l. case l of
             | [||] => NONE
             | (h:::t) => SOME (t,h)) o f)
Proof
  rw[] >>
  irule EQ_TRANS >>
  irule_at (Pos last) o_I_LUNFOLD >>
  simp[LUNFOLD_I]
QED

