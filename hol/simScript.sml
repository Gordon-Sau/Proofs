open BasicProvers dep_rewrite bossLib arithmeticTheory numLib;
open optionTheory whileTheory numLib listTheory llistTheory;

Inductive steps':
  (!a s t. step a s t ⇒ steps' step a s t) ∧
  (!a s t t'. steps' step a s t ∧ step NONE t t' ⇒ steps' step a s t') ∧
  (!a s t t'. step NONE s t ∧ steps' step a t t' ⇒ steps' step a s t')
End

Definition steps_def:
  steps step = \x. steps' step (SOME x)
End

Theorem steps_rules:
  (!a s t. step (SOME a) s t ⇒ steps step a s t) ∧
  (!a s t t'. steps step a s t ∧ step NONE t t' ⇒ steps step a s t') ∧
  (!a s t t'. step NONE s t ∧ steps step a t t' ⇒ steps step a s t')
Proof
  rw[steps_def,steps'_rules] >>
  metis_tac[steps'_rules]
QED

Triviality steps_ind':
  ∀step P.
    (∀a s t. step (SOME a) s t ⇒ P a s t) ∧
    (∀a s t t'. P a s t ∧ step NONE t t' ⇒ P a s t') ∧
    (∀a s t t'. step NONE s t ∧ P a t t' ⇒ P a s t') ⇒
    ∀a0 a1 a2. steps' step a0 a1 a2 ⇒ !x. a0 = SOME x ⇒ P x a1 a2
Proof
  ntac 3 strip_tac >>
  ho_match_mp_tac steps'_ind >>
  rw[] >>
  metis_tac[]
QED

Theorem steps_ind:
  ∀step P.
    (∀a s t. step (SOME a) s t ⇒ P a s t) ∧
    (∀a s t t'. P a s t ∧ step NONE t t' ⇒ P a s t') ∧
    (∀a s t t'. step NONE s t ∧ P a t t' ⇒ P a s t') ⇒
    ∀a0 a1 a2. steps step a0 a1 a2 ⇒ P a0 a1 a2
Proof
  simp[steps_def] >>
  ntac 3 strip_tac >>
  qspecl_then [`step`,`P`] drule steps_ind' >>
  rpt $ strip_tac >>
  first_assum irule >>
  conj_tac >>
  rpt strip_tac >>
  metis_tac[]
QED

Theorem steps_strongind:
  !step P.
  (∀a s t. step (SOME a) s t ⇒ P a s t) ∧
  (∀a s t t'.
     steps step a s t ∧ P a s t ∧ step NONE t t' ⇒
     P a s t') ∧
  (∀a s t t'.
     step NONE s t ∧ steps step a t t' ∧ P a t t' ⇒
     P a s t') ⇒
  ∀a0 a1 a2. steps step a0 a1 a2 ⇒ P a0 a1 a2
Proof
  rpt gen_tac >>
  qspecl_then [`step`,`\a s t. steps step a s t ∧ P a s t`]
    (strip_assume_tac o SRULE[]) steps_ind >>
  rpt strip_tac >>
  last_x_assum irule >>
  rpt strip_tac >>
  simp[] >>
  metis_tac[steps_rules]
QED

Theorem steps_cases:
  !step a0 a1 a2.
    steps step a0 a1 a2 ⇔
    step (SOME a0) a1 a2 ∨
    (∃t. steps step a0 a1 t ∧ step NONE t a2) ∨
    ∃t. step NONE a1 t ∧ steps step a0 t a2
Proof
  rpt gen_tac >>
  iff_tac
  >- (
    foldr (fn (x,y) => y >> qid_spec_tac x) all_tac [`a0`,`a1`,`a2`] >>
    ho_match_mp_tac steps_ind >>
    rpt strip_tac >>
    metis_tac[steps_rules]
  ) >>
  metis_tac[steps_rules]
QED

Inductive steps_NONE:
  (!s. steps_NONE step s s) ∧
  (!s t t'. step NONE s t ∧ steps_NONE step t t' ⇒ steps_NONE step s t')
End

Triviality steps_NONE_rev':
  !t t'. steps_NONE step t t' ⇒
  !t''. step NONE t' t'' ⇒ steps_NONE step t t''
Proof
  ho_match_mp_tac steps_NONE_ind >>
  rw[]
  >- (
    drule_then irule $ cj 2 steps_NONE_rules >>
    simp[steps_NONE_rules]) >>
  last_x_assum $ drule_then assume_tac >>
  irule $ cj 2 steps_NONE_rules >>
  metis_tac[]
QED

Theorem steps_NONE_rev:
  !t t' t''. steps_NONE step t t' ∧ step NONE t' t'' ⇒
  steps_NONE step t t''
Proof
  metis_tac[steps_NONE_rev']
QED

Theorem steps_NONE_steps_left:
  !s s'. steps_NONE step s s' ⇒ steps step a s' t ⇒ steps step a s t
Proof
  ho_match_mp_tac steps_NONE_ind >>
  rw[steps_rules] >>
  irule $ cj 3 steps_rules >>
  last_x_assum $ irule_at (Pos hd) >>
  metis_tac[]
QED

Theorem steps_NONE_steps_right:
  !t t'. steps_NONE step t t' ⇒ steps step a s t ⇒ steps step a s t'
Proof
  ho_match_mp_tac steps_NONE_ind >>
  rw[steps_rules] >>
  last_x_assum irule >>
  irule $ cj 2 steps_rules >>
  metis_tac[]
QED

Theorem steps_skip_NONE_lemma:
  steps step a s t ⇔
    (?s' t'. steps_NONE step s s' ∧
      step (SOME a) s' t' ∧
      steps_NONE step t' t)
Proof
  iff_tac
  >- (
    qid_spec_tac `t` >>
    qid_spec_tac `s` >>
    qid_spec_tac `a` >>
    ho_match_mp_tac steps_ind >>
    rw[] >>
    first_assum $ irule_at (Pos $ el 2) >>
    metis_tac[steps_NONE_rev,steps_NONE_rules]
  ) >>
  simp[PULL_EXISTS] >>
  `!s s'. steps_NONE step s s' ==>
    !t' t. step (SOME a) s' t' ∧
      steps_NONE step t' t ⇒
      steps step a s t` suffices_by metis_tac[] >>
  ho_match_mp_tac steps_NONE_ind >>
  rw[]
  >- (
    drule_then irule steps_NONE_steps_right >>
    simp[steps_rules])
  >- (
    irule $ cj 3 steps_rules >>
    last_assum $ irule_at (Pos hd) >>
    metis_tac[])
QED

Definition reachable_def:
  reachable inits step ⇔ BIGUNION (IMAGE (RTC (\s t. ?a. step a s t)) inits)
End

Definition no_step_def:
  no_step step s = ¬(?a s'. step a s s')
End

Definition deterministic_def:
  deterministic inits step done ⇔
    (?i. inits = {i}) ∧ 
    (!s a t a2 t2. reachable inits step s ∧
      step a s t ∧ step a2 s t2 ⇒
      a = a2 ∧ t = t2) ∧
    (!s r r2. reachable inits step s ∧
      done s r ∧ done s r2 ⇒
      no_step step s ∧ r = r2)
End

Inductive fin_trace:
[~done]
  ( ∀ s r. done r s ⇒ fin_trace done step s [] r)
[~step]
  (∀a s s' t r. step a s s' ∧ fin_trace done step s' t r ⇒ fin_trace done step s (a::t) r)
End

CoInductive diverge:
  ∀ s s' a t. step a s s'∧ diverge step s' t ⇒ diverge step s (a:::t)
End

Triviality LFINITE_NOT_diverge:
  ∀t. LFINITE t ⇒ ∀s. ¬diverge step s t
Proof
  ho_match_mp_tac LFINITE_ind >>
  conj_tac
  >- fs[Once $ diverge_cases] >>
  rw[] >>
  spose_not_then assume_tac >>
  last_x_assum mp_tac >>
  simp[] >>
  pop_assum $ assume_tac o SRULE[Once $ diverge_cases] >>
  metis_tac[]
QED

Theorem diverge_NOT_LFINITE:
  diverge step s t ⇒ ¬ LFINITE t
Proof
  rw[] >>
  spose_not_then assume_tac >>
  qspec_then `step` drule $ GEN_ALL LFINITE_NOT_diverge >>
  simp[] >>
  metis_tac[]
QED

Definition trace_def:
  (trace done step inits t NONE = ?i t'. i ∈ inits ∧
    diverge step i t' ∧
    LFILTER (\x. x ≠ NONE) t' = t) ∧
  (trace done step inits t (SOME r) = ?i t'. i ∈ inits ∧
    fin_trace done step i t' r ∧
    fromList (FILTER (\x. x ≠ NONE) t') = t)
End

Inductive strip_NONE:
[~NONE]
  ! t t'. strip_NONE t t' ⇒ strip_NONE (NONE:::t) t'
[~SOME]
  !a t. strip_NONE (SOME a:::t) (SOME a:::t)
[~Nil]
  strip_NONE [||] [||]
End

CoInductive TRACE_WEAK_BISIMULATION:
[~NONE]
  ∀ l l'. TRACE_WEAK_BISIMULATION l l' ⇒
    TRACE_WEAK_BISIMULATION (NONE:::l) (NONE:::l')
[~SOME]
  ∀ t t' l l' a.
  strip_NONE t (SOME a:::l) ∧ strip_NONE t' (SOME a:::l') ∧
  TRACE_WEAK_BISIMULATION l l' ⇒
  TRACE_WEAK_BISIMULATION t t'
[~Nil]
  ∀ t t'.
  strip_NONE t [||] ∧ strip_NONE t' [||] ⇒
  TRACE_WEAK_BISIMULATION t t'
End

Theorem exists_LEAST_LNTH:
  !l. exists P l ⇒
  ?n x. LNTH n l = SOME x ∧ P x ∧
    (!m a. m < n /\ LNTH m l = SOME a ⇒ ¬ P a)
Proof
  ho_match_mp_tac exists_ind >>
  rw[]
  >- (qexists `0` >>gvs[]) >>
  Cases_on `P h`
  >- (qexists `0` >> gvs[]) >>
  qexists`SUC n` >>
  gvs[] >>
  rw[] >>
  Cases_on `m` >>
  gvs[] >>
  metis_tac[]
QED

Definition least_SOME_index_def:
  least_SOME_index l ⇔ @n. (?y. LNTH n l = SOME (SOME y) ∧
    (!m. m < n ⇒ THE (LNTH m l) = NONE))
End

(*
Theorem LFINITIE_LFILTER_strip_NONE:
  !t. LFINITE t ⇒ LFILTER (\x. x ≠ NONE) t = [||] ⇒
  strip_NONE t [||]
Proof
  ho_match_mp_tac LFINITE_ind >>
  simp[strip_NONE_rules] >>
  rw[] >>
  metis_tac[strip_NONE_rules]
QED

Theorem TRACE_WEAK_BISIMULATION_REFL:
  TRACE_WEAK_BISIMULATION l l
Proof
  irule TRACE_WEAK_BISIMULATION_coind >>
  qexists `$=` >>
  rw[] >>
  Cases_on `a0` >>
  gvs[strip_NONE_rules] >>
  Cases_on `h` >>
  gvs[] >>
  metis_tac[strip_NONE_rules]
QED

Theorem TRACE_WEAK_BISIMULATION_test:
  TRACE_WEAK_BISIMULATION (LUNFOLD (\x. SOME (SUC x,SOME x)) 0)
    (LUNFOLD (\x.
      case x of
         | INL y => SOME (INR y,NONE)
         | INR y => SOME (INL $ SUC y,SOME y)) (INL 0))
Proof
  irule TRACE_WEAK_BISIMULATION_coind >>
  qexists `\l l'. ?n. l = LUNFOLD (\x. SOME (SUC x, SOME x)) n ∧
    l' = LUNFOLD (λx.
               case x of
                 INL y => SOME (INR y,NONE)
               | INR y' => SOME (INL (SUC y'),SOME y')) (INL n)` >>
  simp[] >>
  reverse $ conj_tac >- metis_tac[] >>
  rw[] >>
  disj2_tac >>
  disj1_tac >>
  qexistsl [`LUNFOLD (\x. SOME (SUC x,SOME x)) (SUC n)`,
    `LUNFOLD (λx.
       case x of
         INL y => SOME (INR y,NONE)
       | INR y' => SOME (INL (SUC y'),SOME y')) (INL $ SUC n)`,
    `n`] >>
  conj_tac
  >- (simp[Once $ LUNFOLD] >> simp[strip_NONE_rules]) >>
  conj_tac
  >- (
    simp[Once $ LUNFOLD] >>
    simp[Once $ LUNFOLD] >>
    simp[strip_NONE_rules]
  ) >>
  metis_tac[]
QED

Theorem TRACE_WEAK_BISIMULATION_SYM:
  !l' l. TRACE_WEAK_BISIMULATION l l' ⇒ TRACE_WEAK_BISIMULATION l' l
Proof
  ho_match_mp_tac TRACE_WEAK_BISIMULATION_coind >>
  rw[] >>
  gvs[Once $ TRACE_WEAK_BISIMULATION_cases] >>
  metis_tac[]
QED

(*
Theorem TRACE_WEAK_BISIMULATION_TRANS:
  !l l''. (?l'.TRACE_WEAK_BISIMULATION l l' ∧ TRACE_WEAK_BISIMULATION l' l'') ⇒
  TRACE_WEAK_BISIMULATION l l''
Proof
  ho_match_mp_tac TRACE_WEAK_BISIMULATION_coind >>
  rw[] >>
  last_x_assum $ assume_tac o
    SRULE[Once $ TRACE_WEAK_BISIMULATION_cases] >>
  last_x_assum $ assume_tac o
    SRULE[Once $ TRACE_WEAK_BISIMULATION_cases] >>
  gvs[]
  >- metis_tac[]
  >- (
    disj2_tac >>
    disj1_tac >> 
    qexistsl [`l'5'`,`l'6'`,`a`] >>
    reverse $ conj_tac
    >- (
      simp[] >>
      qexists`l'5'` >>
      simp[TRACE_WEAK_BISIMULATION_REFL])
    >- (
      irule $ cj 1 strip_NONE_rules >>
      pop_assum kall_tac >>
      pop_assum kall_tac >>
      pop_assum $ assume_tac o SRULE[Once $ strip_NONE_cases] >>
      last_x_assum mp_tac >>
      last_x_assum 
    )
  )
QED
*)

Theorem LFINITE_ALL_NONE:
  ∀ l. LFINITE l ==>
  (!n x. LNTH n l = SOME x ⇒ x = NONE) ⇒
  strip_NONE l [||]
Proof
  ho_match_mp_tac LFINITE_ind >>
  rw[strip_NONE_rules] >>
  last_assum $ qspec_then `0` assume_tac >>
  fs[] >>
  irule strip_NONE_NONE >>
  last_x_assum irule >>
  rw[] >>
  last_x_assum irule >>
  qexists `SUC n` >>
  simp[]
QED

Theorem LFINITE_TRACE_WEAK_BISIMULATION:
  !a0. LFINITE a0 ==> !a1. LFINITE a1 ∧
  (!n x. LNTH n a0 = SOME x ⇒ x = NONE) ∧
  TRACE_WEAK_BISIMULATION a0 a1 ⇒
  strip_NONE a1 [||]
Proof
  ho_match_mp_tac LFINITE_strongind >>
  rw[]
  >- (
    fs[Once $ TRACE_WEAK_BISIMULATION_cases] >>
    fs[Once $ strip_NONE_cases]
  ) >>
  last_assum $ qspec_then `0` assume_tac >>
  fs[] >>
  first_x_assum irule >>
  rw[]
  >- (
    last_x_assum irule >>
    qexists `SUC n` >>
    gvs[]
  ) >>
  irule $ TRACE_WEAK_BISIMULATION_coind >>
  qexists `\x y. LFINITE x ∧ LFINITE y ∧ strip_NONE x a0 ∧ strip_NONE y [||]` >>
  gvs[] >>
  conj_tac
  >- (
    pop_assum kall_tac >>
    rw[] >>
  )
QED

Triviality strip_NONE_LFINITE':
  !t l. strip_NONE t l ⇒  l = [||] ⇒ LFINITE t
Proof
  ho_match_mp_tac strip_NONE_ind >>
  gvs[]
QED

Theorem strip_NONE_LFINITE:
  strip_NONE t [||] ⇒ LFINITE t
Proof
  metis_tac[strip_NONE_LFINITE']
QED

Theorem strip_NONE_LFINITE_EQ:
  !t l. strip_NONE t l ⇒ (LFINITE l = LFINITE t)
Proof
  ho_match_mp_tac strip_NONE_ind >>
  gvs[]
QED

Theorem strip_NONE_NIL_every_NONE:
  !l t.
    strip_NONE l t ⇒ t = [||] ⇒ every (\x. x = NONE) l
Proof
  ho_match_mp_tac strip_NONE_ind >>
  gvs[]
QED

Triviality strip_NONE_NOT_NONE':
  !l l'. strip_NONE l l' ⇒ !t. l' = NONE:::t ⇒ F
Proof
  ho_match_mp_tac strip_NONE_ind >>
  gvs[]
QED

Theorem strip_NONE_NOT_NONE:
  strip_NONE l (NONE:::l') ⇒ F
Proof
  metis_tac[strip_NONE_NOT_NONE']
QED

Theorem strip_NONE_every_NONE':
  !l t.
    strip_NONE l t ⇒
    !a l'. t = SOME a:::l' ∧
    every (\x. x = NONE) l ⇒
    F
Proof
  ho_match_mp_tac strip_NONE_ind >>
  gvs[]
QED

Theorem strip_NONE_every_NONE:
  strip_NONE l (SOME a:::l') ∧ every (\x. x = NONE) l ==> F
Proof
  metis_tac[strip_NONE_every_NONE']
QED


Triviality TRACE_WEAK_BISIMULATION_IMP_LFINITE:
  !l. LFINITE l ⇒
  !l'. TRACE_WEAK_BISIMULATION l l' ⇒
  LFINITE l'
Proof
  ho_match_mp_tac LFINITE_strongind >>
  rw[]
  >- (
    fs[Once $ TRACE_WEAK_BISIMULATION_cases] >>
    gvs[Once $ strip_NONE_cases] >>
    metis_tac[strip_NONE_LFINITE]
  ) >>
  Cases_on `h` >>
  pop_assum $ assume_tac o  
    SRULE[Once TRACE_WEAK_BISIMULATION_cases] >>
  gvs[]
  >- (
    qpat_x_assum `strip_NONE (NONE:::l) _` $
      assume_tac o SRULE[Once $ strip_NONE_cases] >>
    last_x_assum irule >>
    irule $ cj 2 TRACE_WEAK_BISIMULATION_rules >>
    metis_tac[]
  )
  >- metis_tac[strip_NONE_LFINITE]
  >- (
    qpat_x_assum `strip_NONE (SOME _:::_) (SOME _:::_)` $
      assume_tac o SRULE[Once $ strip_NONE_cases] >>
    gvs[] >>
    drule strip_NONE_LFINITE_EQ >>
    simp[]) >>
  metis_tac[strip_NONE_LFINITE]
QED

Theorem TRACE_WEAK_BISIMULATION_IMP_LFINITE_EQ:
  TRACE_WEAK_BISIMULATION l l' ⇒ LFINITE l = LFINITE l'
Proof
  rw[] >>
  iff_tac >>
  metis_tac[TRACE_WEAK_BISIMULATION_IMP_LFINITE,
    TRACE_WEAK_BISIMULATION_SYM]
QED

Theorem LFILTER_every_IMP:
  LFINITE l = LFINITE l' ∧
  LFILTER (\x. x ≠ NONE) l = LFILTER (\x. x ≠ NONE) l' ∧
  every (\x. x = NONE) l ⇒ 
  every (\x. x = NONE) l'
Proof
  rw[] >>
  irule every_coind >>
  qexists `\l. every (\x. x = NONE) l ∧
    (LFINITE l = LFINITE l')` >>
  qspec_then `\x. x <> NONE` assume_tac o
    SRULE[combinTheory.o_DEF] o GEN_ALL $
    GSYM LFILTER_EQ_NIL >>
  gvs[] >>
  rw[]
QED

Theorem LFILTER_EQ_TRACE_WEAK_BISIMULATION:
  (LFINITE l = LFINITE l' ∧
    LFILTER (\x. x≠ NONE) l = LFILTER (\x. x≠ NONE) l') ⇔ 
  TRACE_WEAK_BISIMULATION l l'
Proof
  Cases_on `every (\x. x = NONE) l`
  >- (
    iff_tac
    >- (
      rw[] >>
      drule_all LFILTER_every_IMP >>
      rw[] >>
      irule TRACE_WEAK_BISIMULATION_coind >>
      qexists `\l l'. (LFINITE l ⇔ LFINITE l') ∧ every (\x. x = NONE) l ∧
        every (\x. x = NONE) l'` >>
      gvs[every_LNTH] >>
      reverse conj_tac >- metis_tac[] >>
      rpt $ pop_assum kall_tac >>
      rpt strip_tac >>
      Cases_on `LFINITE a0`
      >- metis_tac[LFINITE_ALL_NONE] >>
      gvs[] >>
      disj1_tac >>
      Cases_on `a0` >>
      gvs[] >>
      Cases_on `a1` >>
      gvs[] >>
      last_assum $ qspec_then `0` assume_tac >>
      first_assum $ qspec_then `0` assume_tac >>
      fs[] >>
      rw[]
      >- (last_x_assum $ qspec_then `SUC n` assume_tac >> fs[])
      >- (first_x_assum $ qspec_then `SUC n` assume_tac >> fs[])
    ) >>
    strip_tac
    >> conj_asm1_tac
    >- metis_tac[TRACE_WEAK_BISIMULATION_IMP_LFINITE_EQ] >>
    `every (\x. x = NONE) l'` suffices_by (
      `¬ exists (\x. x ≠ NONE) l` by
        gvs[every_def,combinTheory.o_DEF] >>
      rw[] >>
      `¬ exists (\x. x ≠ NONE) l'` by
        gvs[every_def,combinTheory.o_DEF] >>
      simp[Once $ LFILTER] >>
      simp[Once $ LFILTER]) >>
    irule every_coind >>
    qexists `\x. LFINITE l = LFINITE x ∧
      TRACE_WEAK_BISIMULATION l x` >>
    conj_tac >- simp[] >>
    ntac 2 $ pop_assum kall_tac >>
    rpt gen_tac >>
    simp[] >>
    strip_tac >>
    qpat_x_assum `TRACE_WEAK_BISIMULATION _ _` $ assume_tac o
      SRULE[Once $ TRACE_WEAK_BISIMULATION_cases] >>
    rw[]
    >- metis_tac[strip_NONE_every_NONE]
    >- (drule strip_NONE_NIL_every_NONE >> simp[])
    >- (
      Cases_on `LFINITE t` >>
      gvs[]
      >- (
        irule TRACE_WEAK_BISIMULATION_coind >>
        qexists `\l l'. every (\x. x = NONE) l /\ LFINITE l ∧
          LFINITE l' ∧ TRACE_WEAK_BISIMULATION l' l` >>
        gvs[] >>
        rpt $ pop_assum kall_tac >>
        rw[] >>
        disj2_tac >>
        disj2_tac >>
        fs[every_LNTH] >>
        conj_tac >- metis_tac[LFINITE_ALL_NONE] >>
        Cases_on `a0`
        >- (
          gvs[Once $ TRACE_WEAK_BISIMULATION_cases] >>
          fs[Once $ strip_NONE_cases]) >>

      )
    )
    >- metis_tac[strip_NONE_every_NONE]
    >- (
      first_x_assum $ strip_assume_tac o
        SRULE[Once $ strip_NONE_cases] >>
      metis_tac[cj 3 TRACE_WEAK_BISIMULATION_rules]
    )
  )
QED
*)

Definition refine_def:
  refine (inits,step,done) (inits',step',done') ⇔
    (!l. trace done step inits l NONE ⇒
      trace done' step' inits' l NONE) ∧
    (!l r. trace done step inits l (SOME r) ⇒
      trace done' step' inits' l (SOME r))
End

Triviality fin_trace_steps_NONE':
  ∀ i t.
  steps_NONE step i t ⇒ !l r. fin_trace done step t l r ⇒
  ?ns. fin_trace done step i (ns ++ l) r ∧
    EVERY (\x. x = NONE) ns
Proof
  ho_match_mp_tac steps_NONE_ind >>
  rw[]
  >- (qexists `[]` >> simp[]) >>
  res_tac >>
  qexists `NONE::ns` >>
  gvs[] >>
  irule $ cj 2 fin_trace_rules >>
  metis_tac[]
QED

Theorem fin_trace_steps_NONE =
  SRULE[AND_IMP_INTRO,PULL_FORALL] fin_trace_steps_NONE';

Theorem fin_trace_steps_SOME:
  steps step a i t /\ fin_trace done step t l r ⇒
  ?ns ms. fin_trace done step i (ns ++ SOME a::(ms ++ l)) r ∧
    EVERY (\x. x = NONE) ns ∧
    EVERY (\x. x = NONE) ms
Proof
  simp[steps_skip_NONE_lemma] >>
  rw[] >>
  drule_all_then assume_tac fin_trace_steps_NONE >>
  rw[] >>
  drule_at_then (Pos $ el 2) drule $ cj 2 fin_trace_rules >>
  rw[] >>
  drule_all_then assume_tac fin_trace_steps_NONE >>
  rw[] >>
  drule_at_then (Pos $ el 2) rev_drule $ fin_trace_steps_NONE >>
  rw[] >>
  first_x_assum $ irule_at (Pos hd) >>
  simp[]
QED

Theorem fin_trace_refine:
  (!s' t' s. step' NONE s' t' ∧ R s s' ⇒
      ?t. steps_NONE step s t ∧ R t t') ∧
  (!a s' t' s. step' (SOME a) s' t' ∧ R s s' ⇒
      ?t. steps step a s t ∧ R t t') ∧
  (!r t' t. done' r t' ∧ R t t' ⇒
    ?t''. steps_NONE step t t'' ∧ done r t'') ==>
  !i' t' r. fin_trace done' step' i' t' r ⇒
  ∀ i. R i i' ⇒
  ?t. fin_trace done step i t r ∧ 
  FILTER (\x. x ≠ NONE) t = FILTER (λx. x ≠ NONE) t'
Proof
  strip_tac >>
  ho_match_mp_tac fin_trace_ind >>
  rw[]
  >- (
    first_x_assum $ drule_all_then strip_assume_tac >>
    `fin_trace done step t'' [] r` by (
      irule_at (Pos hd) $ cj 1 fin_trace_rules >>
      simp[]) >>
    drule_at_then (Pos $ el 2) drule $ fin_trace_steps_NONE >>
    rw[] >>
    first_x_assum $ irule_at (Pos hd) >>
    simp[FILTER_EQ_NIL]
  )
  >- (
    Cases_on `a` >>
    gvs[] >>
    first_x_assum $ drule_all_then strip_assume_tac >>
    last_x_assum $ qspec_then `t` $ assume_tac >>
    gvs[] >>
    drule_at_then (Pos $ el 2) drule fin_trace_steps_SOME >>
    rw[] >>
    first_assum $ irule_at (Pos hd) >>
    simp[FILTER_APPEND_DISTRIB] >>
    qspecl_then [`\x. x <> NONE`,`ns`] assume_tac $
      GSYM FILTER_EQ_NIL >>
    qspecl_then [`\x. x <> NONE`,`ms`] assume_tac $
      GSYM FILTER_EQ_NIL >>
    gvs[]
  )
  >- (
    first_x_assum $ drule_all_then strip_assume_tac >>
    last_x_assum $ qspec_then `t` $ assume_tac >>
    gvs[] >>
    drule_at_then (Pos $ el 2) drule fin_trace_steps_NONE >>
    rw[] >>
    first_assum $ irule_at (Pos hd) >>
    simp[FILTER_APPEND_DISTRIB] >>
    simp[FILTER_EQ_NIL]
  )
QED

Theorem diverge_steps_NONE:
  !s s'.
  steps_NONE step s s' ==> diverge step s' t ⇒
  ?ns. diverge step s (LAPPEND (fromList ns) t) ∧ EVERY (\x. x = NONE) ns
Proof
  ho_match_mp_tac steps_NONE_ind >>
  rw[]
  >- (
    qexists `[]` >>
    simp[]
  ) >>
  res_tac >>
  qexists `NONE::ns` >>
  simp[] >>
  irule_at (Pos hd) diverge_rules >>
  metis_tac[]
QED

Theorem diverge_steps_NONE:
  !s s'.
  steps_NONE step s s' ==> diverge step s' t ⇒
  ?ns. diverge step s (LAPPEND (fromList ns) t) ∧ EVERY (\x. x = NONE) ns
Proof
  ho_match_mp_tac steps_NONE_ind >>
  rw[]
  >- (
    qexists `[]` >>
    simp[]
  ) >>
  res_tac >>
  qexists `NONE::ns` >>
  simp[] >>
  irule_at (Pos hd) diverge_rules >>
  metis_tac[]
QED

Triviality LCONS_LAPPEND:
  h:::t = LAPPEND [|h|] t
Proof
  simp[]
QED

Theorem diverge_steps_SOME:
  !a s s'.
  steps step a s s' ==> !t. diverge step s' t ⇒
  ?ns ms. diverge step s (LAPPEND (fromList $ ns ++ (SOME a::ms)) t) ∧
    EVERY (\x. x = NONE) ns ∧
    EVERY (\x. x = NONE) ms
Proof
  ho_match_mp_tac steps_ind >>
  rw[]
  >- (
    qexistsl [`[]`,`[]`] >>
    simp[] >>
    metis_tac[diverge_rules]
  )
  >- (
    `diverge step s' (NONE:::t)` by metis_tac[diverge_rules] >>
    last_x_assum drule >>
    rw[] >>
    qexistsl [`ns`,`ms ++ [NONE]`] >>
    gvs[] >>
    ntac 3 $ last_x_assum kall_tac >>
    last_x_assum $ assume_tac o
      PURE_REWRITE_RULE[Once LCONS_LAPPEND] >>
    first_x_assum $ mp_tac o
      PURE_REWRITE_RULE[GSYM LAPPEND_ASSOC] >>
    `[|NONE|] = fromList [NONE]` by EVAL_TAC >>
    pop_assum (fn t => PURE_REWRITE_TAC[t]) >>
    PURE_REWRITE_TAC[LAPPEND_fromList] >>
    PURE_REWRITE_TAC[Once rich_listTheory.CONS_APPEND] >>
    strip_tac >>
    PURE_REWRITE_TAC[Once rich_listTheory.CONS_APPEND] >>
    metis_tac[APPEND_ASSOC]
  )
  >- (
    last_x_assum drule >>
    rw[] >>
    qexistsl [`NONE::ns`,`ms`] >>
    gvs[] >>
    irule diverge_rules >>
    metis_tac[]
  )
QED

Theorem imp_diverge_refine:
  (!a s s' t'. step' a s' t' ∧ R s s' ⇒
    ?t. step a s t ∧ R t t') ==>
  !i i' l. R i i' ∧ diverge step' i' l ⇒
  diverge step i l
Proof
  rw[] >>
  irule_at (Pos hd) diverge_coind >>
  qexists `\x y. ?x'. R x x' ∧ diverge step' x' y` >>
  simp[] >>
  conj_tac
  >- (
    ntac 2 $ pop_assum kall_tac >>
    rw[] >>
    pop_assum $ assume_tac o SRULE[Once $ diverge_cases] >>
    gvs[] >>
    last_assum $ drule_all_then strip_assume_tac >>
    first_assum $ irule_at (Pos hd) >>
    first_assum $ irule_at (Pos hd) >>
    simp[]
  ) >>
  metis_tac[]
QED

Theorem imp_diverge_refine:
  (!a s s' t'. step' a s' t' ∧ R s s' ⇒
    ?t. step a s t ∧ R t t') ==>
  !i i' l. R i i' ∧ diverge step' i' l ⇒
  diverge step i l
Proof
  rw[] >>
  irule diverge_coind >>
  qexists `\x y. ?x'. R x x' ∧ diverge step' x' y` >>
  simp[] >>
  conj_tac
  >- (
    ntac 2 $ pop_assum kall_tac >>
    rw[] >>
    pop_assum $ assume_tac o SRULE[Once $ diverge_cases] >>
    gvs[] >>
    last_assum $ drule_all_then strip_assume_tac >>
    first_assum $ irule_at (Pos hd) >>
    first_assum $ irule_at (Pos hd) >>
    simp[]
  ) >>
  metis_tac[]
QED

Theorem diverge_steps_NONE_refine:
  (!a s s' t'. step' a s' t' ∧ R s s' ⇒
    ?t. steps step a s t ∧ R t t') ∧
  (!a s s' t'. step' a s' t' ∧ R s s' ⇒
    ?t. steps step a s t ∧ R t t') ∧
  ==>
  !i i' l. R i i' ∧ diverge step' i' l ⇒
  diverge step i l
Proof
  rw[] >>
  irule_at (Pos hd) diverge_coind >>
  qexists `\x y. ?x'. R x x' ∧ diverge step' x' y` >>
  simp[] >>
  conj_tac
  >- (
    ntac 2 $ pop_assum kall_tac >>
    rw[] >>
    pop_assum $ assume_tac o SRULE[Once $ diverge_cases] >>
    gvs[] >>
    last_assum $ drule_all_then strip_assume_tac >>
    first_assum $ irule_at (Pos hd) >>
    first_assum $ irule_at (Pos hd) >>
    simp[]
  ) >>
  metis_tac[]
QED

CoInductive inf_trace:
[~done]
  ( ∀ s r. done r s ⇒ inf_trace done step s [||] r)
[~step]
  (∀a s s' t r. step a s s' ∧ inf_trace done step s' t r ⇒ inf_trace done step s (a:::t) r)
End

Theorem inf_trace_finite_thm:
  !t. LFINITE t ⇒ !s s' r. inf_trace done step s t r ⇒ fin_trace done step s t r
Proof
  ho_match_mp_tac LFINITE_ind >>
  rw[]
  >- (
    gvs[Once $ inf_trace_cases] >>
    simp[fin_trace_rules]) >>
  pop_assum $ assume_tac o SRULE[Once $ inf_trace_cases] >>
  irule fin_trace_step >>
  gvs[] >>
  metis_tac[]
QED

Theorem fin_trace_imp_inf_trace:
  ∀ s t r. fin_trace done step s t r ⇒ inf_trace done step s t r
Proof
  ho_match_mp_tac fin_trace_ind >>
  rw[inf_trace_done] >>
  irule inf_trace_step >>
  metis_tac[]
QED

Theorem inf_trace_diverge:
  !s t. inf_trace done step s t r /\ ¬ LFINITE t ==>
  diverge step s t
Proof
  ho_match_mp_tac diverge_coind >>
  rw[] >>
  gvs[Once $ inf_trace_cases] >>
  metis_tac[]
QED

Triviality LFINITE_NOT_diverge:
  ∀t. LFINITE t ⇒ ∀s. ¬diverge step s t
Proof
  ho_match_mp_tac LFINITE_ind >>
  conj_tac
  >- fs[Once $ diverge_cases] >>
  rw[] >>
  spose_not_then assume_tac >>
  last_x_assum mp_tac >>
  simp[] >>
  pop_assum $ assume_tac o SRULE[Once $ diverge_cases] >>
  metis_tac[]
QED

Theorem diverge_NOT_LFINITE:
  diverge step s t ⇒ ¬ LFINITE t
Proof
  rw[] >>
  spose_not_then assume_tac >>
  qspec_then `step` drule $ GEN_ALL LFINITE_NOT_diverge >>
  simp[] >>
  metis_tac[]
QED

Theorem diverge_inf_trace:
  !s t r. diverge step s t ⇒ inf_trace done step s t r
Proof
  ho_match_mp_tac inf_trace_coind >>
  rw[] >>
  disj2_tac >>
  pop_assum $ assume_tac o SRULE[Once $ diverge_cases] >>
  metis_tac[]
QED


