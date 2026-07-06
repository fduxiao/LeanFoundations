/-
Copyright (c) 2026 Xiao Tan. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Xiao Tan
-/

import LeanFoundations._MyTactics

/-!
# Propositional Logic
Now, let's see how to study logic within _the logic of Lean_.
-/

namespace PropLogic

inductive Proposition : Type where
  | var (name: String): Proposition
  | top : Proposition
  | and (p q : Proposition) : Proposition
  | imp (p q : Proposition) : Proposition
  | bot : Proposition
  | or (p q : Proposition) : Proposition


abbrev Proposition.not (p : Proposition) : Proposition := p.imp .bot


abbrev Context := List Proposition
abbrev Context.add (p : Proposition) (Γ : Context) : Context := p :: Γ


/-!
## Classical Logic
-/

/-!
### Semantics
-/
def Eval := String -> Bool


def Eval.eval (e: Eval): Proposition -> Bool
  | .var x => e x
  | .top => true
  | .and p q => (e.eval p).and (e.eval q)
  | .imp p q => (e.eval p).not.or (e.eval q)
  | .bot => false
  | .or p q => (e.eval p).or (e.eval q)


def Eval.satisfies (e: Eval) (Γ: Context) := forall p: Proposition, p ∈ Γ -> e.eval p = true


@[simp]
theorem Eval.satisfies.empty {e: Eval}:
  e.satisfies []
:= by
  intro p I
  simp at I


theorem Eval.satisfies.add {e: Eval} {Γ: Context} {p: Proposition}:
  e.satisfies Γ ->  e.eval p = true -> e.satisfies (Γ.add p)
:= by
  intro S H
  intro c I
  simp [Context.add] at I
  cases I with
  | inl =>
    simp_all
  | _ =>
    apply S
    assumption


theorem Eval.satisfies.split_add {e: Eval} {Γ: Context} {p: Proposition}:
  e.satisfies (Γ.add p) -> e.satisfies Γ ∧ e.eval p = true
:= by
  intro S
  and_intros
  . intro c I
    apply S
    simp_all
  . apply S
    simp


def Context.entailsC (Γ: Context) (p: Proposition): Prop := forall e: Eval, e.satisfies Γ -> e.eval p = true


theorem entailsC_imp_iff {Γ: Context} {p q: Proposition}:
  (Γ.add p).entailsC q <-> Γ.entailsC (p.imp q)
:= by
  apply Iff.intro
  . intro H
    intro e S
    simp [Eval.eval]
    cases E: e.eval p with
    | false =>
      left
      eq_refl
    | true =>
      right
      apply H
      apply Eval.satisfies.add
      . exact S
      . exact E
  . intro H
    intro e S
    rcases S.split_add with ⟨S, K⟩
    specialize H e S
    simp [Eval.eval] at H
    simp_all

/-!
### Syntax
-/

/--
Classical provability relation.
-/
inductive Context.provesC: Context -> Proposition -> Prop where
  | ax {Γ: Context} {p} : p ∈ Γ -> Γ.provesC p
  | topI {Γ: Context}: Γ.provesC .top
  | andI {Γ: Context} {p q} : Γ.provesC p -> Γ.provesC q -> Γ.provesC (Proposition.and p q)
  | andE1 {Γ: Context} {p q} : Γ.provesC (Proposition.and p q) -> Γ.provesC p
  | andE2 {Γ: Context} {p q} : Γ.provesC (Proposition.and p q) -> Γ.provesC q
  | impI {Γ: Context} {p q} : (Γ.add p).provesC q -> Γ.provesC (Proposition.imp p q)
  | impE {Γ: Context} {p q: Proposition}: Γ.provesC (p.imp q) -> Γ.provesC p -> Γ.provesC q
  | botE {Γ: Context} {p} : Γ.provesC Proposition.bot -> Γ.provesC p
  | orI1 {Γ: Context} {p q} : Γ.provesC p -> Γ.provesC (Proposition.or p q)
  | orI2 {Γ: Context} {p q} : Γ.provesC q -> Γ.provesC (Proposition.or p q)
  | orE {Γ: Context} {p q r} : Γ.provesC (Proposition.or p q) -> (Γ.add p).provesC r -> (Γ.add q).provesC r -> Γ.provesC r
  | em {Γ: Context} {p: Proposition} : Γ.provesC (p.or p.not)


@[simp]
theorem Context.provesC.add {Γ: Context} {c}:
  (Γ.add c).provesC c
:= by
  apply Context.provesC.ax
  simp [Context.add]


theorem Context.provesC.permute {Γ Γ': Context} {p}:
  Context.provesC Γ p ->
  List.Perm Γ Γ' ->
  Context.provesC Γ' p
:= by
  intro H P
  induction H generalizing Γ' <;> try grind [Context.provesC]
  case impI Γ p q H IH =>
    apply Context.provesC.impI
    simp [Context.add] at *
    apply IH
    simp
    exact P
  case orE Γ p q r H H1 H2 IH IH1 IH2 =>
    apply Context.provesC.orE
    . apply IH P
    . apply IH1
      simp
      exact P
    . apply IH2
      simp
      exact P


theorem Context.provesC.weaken {Γ Δ: Context} {p}:
  Γ.provesC p -> Context.provesC (Δ ++ Γ) p
:= by
  intro H
  induction H <;> try grind [Context.provesC]
  case impI Γ p q H IH =>
    apply Context.provesC.impI
    simp [Context.add] at *
    apply IH.permute
    simp
  case orE Γ p q r H H1 H2 IH IH1 IH2 =>
    apply IH.orE
    . apply IH1.permute
      simp
    . apply IH2.permute
      simp


theorem Context.provesC.weaken_add {Γ: Context} c {p}:
  Γ.provesC p -> (Γ.add c).provesC p
:= by
  intro H
  replace H := H.weaken (Δ := [c])
  exact H


theorem Context.provesC.weaken' {Γ Δ: Context} {p}:
  Γ.provesC p -> Context.provesC (Γ ++ Δ) p
:= by
  intro H
  replace H := H.weaken (Δ := Δ)
  apply H.permute
  apply List.perm_append_comm


theorem Context.provesC.weaken_add' {Γ: Context} c {p}:
  Context.provesC [c] p -> (Γ.add c).provesC p
:= by
  intro H
  replace H := H.weaken' (Δ := Γ)
  exact H


def Proposition.leC (p q: Proposition): Prop := Context.provesC [p] q


@[simp]
theorem Proposition.leC.refl {p: Proposition}:
  Proposition.leC p p
:= by
  apply Context.provesC.ax
  simp


theorem Proposition.leC.trans {p q r: Proposition}:
  Proposition.leC p q -> Proposition.leC q r -> Proposition.leC p r
:= by
  intro H1 H2
  replace H2 := H2.impI
  replace H2 := H2.weaken_add p
  simp [Context.add] at H2
  apply Context.provesC.impE
  . exact H2
  . exact H1


@[simp]
theorem Proposition.leC.top {p: Proposition}:
  p.leC .top
:= by
  apply Context.provesC.topI


@[simp]
theorem Proposition.leC.bot {p: Proposition}:
  Proposition.bot.leC p
:= by
  apply Context.provesC.botE
  apply Context.provesC.ax
  simp


def Proposition.eqC (p q: Proposition): Prop := Proposition.leC p q ∧ Proposition.leC q p


@[simp]
theorem Proposition.eqC.refl {p: Proposition}:
  p.eqC p
:= by
  simp [eqC]


theorem Proposition.eqC.symm {p q: Proposition}:
  p.eqC q -> q.eqC p
:= by
  intros
  simp_all [eqC]


theorem Proposition.eqC.trans {p q r: Proposition}:
  p.eqC q -> q.eqC r -> p.eqC r
:= by
  intros
  grind [leC.trans, eqC]



theorem Proposition.eqC.imp_not_or {p q: Proposition}:
  (p.imp q).eqC (p.not.or q)
:= by
  simp [eqC, leC]
  and_intros
  . apply Context.provesC.orE
    . apply Context.provesC.em (p := p)
    . apply Context.provesC.orI2
      apply Context.provesC.impE (p := p)
      . apply Context.provesC.ax
        simp
      . apply Context.provesC.ax
        simp
    . apply Context.provesC.orI1
      apply Context.provesC.ax
      simp
  . apply Context.provesC.orE (p := p.not) (q := q)
    . apply Context.provesC.ax
      simp
    . apply Context.provesC.impI
      simp [Context.add]
      apply Context.provesC.botE
      apply Context.provesC.impE (p := p)
      . apply Context.provesC.ax
        simp
      . apply Context.provesC.ax
        simp
    . apply Context.provesC.impI
      apply Context.provesC.ax
      simp


theorem Proposition.eqC.dne {p: Proposition}:
  p.eqC p.not.not
:= by
  simp [eqC, leC]
  and_intros
  . apply Context.provesC.impI
    simp [Context.add]
    apply Context.provesC.impE (p := p)
    . apply Context.provesC.ax
      simp
    . apply Context.provesC.ax
      simp
  . apply Context.provesC.orE
    . apply Context.provesC.em (p := p)
    . apply Context.provesC.ax
      simp
    . apply Context.provesC.botE
      apply Context.provesC.impE (p := p.not)
      . apply Context.provesC.ax
        simp
      . apply Context.provesC.ax
        simp


theorem Proposition.eqC.provesC {Γ: Context} {p p': Proposition}:
  p.eqC p' -> Context.provesC Γ p -> Context.provesC Γ p'
:= by
  intro E H
  apply Context.provesC.impE (p := p)
  . have K: Context.provesC [] (p.imp p') := by
      apply Context.provesC.impI
      apply E.left
    replace K := K.weaken (Δ := Γ)
    simp at K
    exact K
  . exact H


theorem Proposition.eqC.or {p p' q q': Proposition}:
  p.eqC p' -> q.eqC q' -> (p.or q).eqC (p'.or q')
:= by
  intros Hp Hq
  simp [eqC, leC]
  and_intros
  . apply Context.provesC.orE
    . apply Context.provesC.ax (p := p.or q)
      simp
    . apply Context.provesC.orI1
      apply Context.provesC.weaken_add'
      exact Hp.left
    . apply Context.provesC.orI2
      apply Context.provesC.weaken_add'
      exact Hq.left
  . apply Context.provesC.orE
    . apply Context.provesC.ax (p := p'.or q')
      simp
    . apply Context.provesC.orI1
      apply Context.provesC.weaken_add'
      exact Hp.right
    . apply Context.provesC.orI2
      apply Context.provesC.weaken_add'
      exact Hq.right


theorem Proposition.eqC.or1 {p p' q: Proposition}:
  p.eqC p' -> (p.or q).eqC (p'.or q)
:= by
  intro H
  apply Proposition.eqC.or
  . exact H
  . apply Proposition.eqC.refl


theorem Proposition.eqC.or2 {p q q': Proposition}:
  q.eqC q' -> (p.or q).eqC (p.or q')
:= by
  intro H
  apply Proposition.eqC.or
  . apply Proposition.eqC.refl
  . exact H


theorem Proposition.eqC.and {p p' q q': Proposition}:
  p.eqC p' -> q.eqC q' -> (p.and q).eqC (p'.and q')
:= by
  intros Hp Hq
  simp [eqC, leC]
  and_intros
  . apply Context.provesC.andI
    . apply Hp.provesC
      apply Context.provesC.andE1 (q := q)
      simp
    . apply Hq.provesC
      apply Context.provesC.andE2 (p := p)
      simp
  . apply Context.provesC.andI
    . apply Hp.symm.provesC
      apply Context.provesC.andE1 (q := q')
      simp
    . apply Hq.symm.provesC
      apply Context.provesC.andE2 (p := p')
      simp


theorem Proposition.eqC.imp {p p' q q': Proposition}:
  p.eqC p' -> q.eqC q' -> (p.imp q).eqC (p'.imp q')
:= by
  intros Hp Hq
  simp [eqC, leC]
  and_intros
  . apply Context.provesC.impI
    apply Hq.provesC
    apply Context.provesC.impE (p := p) (q := q)
    . apply Context.provesC.ax
      simp [Context.add]
    . apply Hp.symm.provesC
      apply Context.provesC.ax
      simp [Context.add]
  . apply Context.provesC.impI
    apply Hq.symm.provesC
    apply Context.provesC.impE (p := p') (q := q')
    . apply Context.provesC.ax
      simp [Context.add]
    . apply Hp.provesC
      apply Context.provesC.ax
      simp [Context.add]


theorem Proposition.eqC.not {p p': Proposition}:
  p.eqC p' -> p.not.eqC p'.not
:= by
  intro Hp
  apply Proposition.eqC.imp
  . exact Hp
  . simp


inductive Context.eqC: Context -> Context -> Prop where
  | nil: Context.eqC [] []
  | cons {p p': Proposition} {Γ Γ': Context}:
    p.eqC p' -> Context.eqC Γ Γ' -> Context.eqC (Γ.add p) (Γ'.add p')


theorem Context.provesC.eqC {Γ Γ': Context} {p: Proposition}:
  Context.provesC Γ p -> Context.eqC Γ Γ' -> Γ'.provesC p
:= by
  intro H E
  induction Γ generalizing Γ' p
  case nil =>
    cases E
    exact H
  case cons x xs IH =>
    cases E; case cons y ys E1 E2 =>
    replace H := H.impI
    specialize IH H E2
    solution[[
      apply Context.provesC.impE
      . apply Context.provesC.weaken_add
        apply Proposition.eqC.provesC
        . apply E1.imp
          apply Proposition.eqC.refl
        . exact IH
      . simp
    ]]


theorem Proposition.eqC.and_idempotent {p: Proposition}:
  (p.and p).eqC p
:= by
  simp [eqC, leC]
  and_intros
  . apply Context.provesC.andE1 (q := p)
    apply Context.provesC.ax
    simp
  . apply Context.provesC.andI
    . apply Context.provesC.ax
      simp
    . apply Context.provesC.ax
      simp


theorem Proposition.eqC.or_comm {p q: Proposition}:
  (p.or q).eqC (q.or p)
:= by
  and_intros
  . apply Context.provesC.orE (p := p) (q := q)
    . apply Context.provesC.ax
      simp
    . apply Context.provesC.orI2
      apply Context.provesC.ax
      simp
    . apply Context.provesC.orI1
      apply Context.provesC.ax
      simp
  . apply Context.provesC.orE (p := q) (q := p)
    . apply Context.provesC.ax
      simp
    . apply Context.provesC.orI2
      apply Context.provesC.ax
      simp
    . apply Context.provesC.orI1
      apply Context.provesC.ax
      simp


theorem Proposition.eqC.or_bot {p: Proposition}:
  (p.or .bot).eqC p
:= by
  and_intros
  . apply Context.provesC.orE (p := p) (q := .bot)
    . apply Context.provesC.ax
      simp
    . apply Context.provesC.ax
      simp
    . apply Context.provesC.botE
      apply Context.provesC.ax
      simp
  . apply Context.provesC.orI1
    simp


theorem Proposition.eqC.bot_or {p: Proposition}:
  (Proposition.bot.or p).eqC p
:= by
  apply Proposition.eqC.trans
  . apply Proposition.eqC.or_comm
  apply Proposition.eqC.or_bot


theorem Proposition.eqC.or_top {p: Proposition}:
  (p.or .top).eqC .top
:= by
  and_intros
  . apply Context.provesC.topI
  . apply Context.provesC.orI2
    apply Context.provesC.topI


theorem Proposition.eqC.top_or {p: Proposition}:
  (Proposition.top.or p).eqC .top
:= by
  apply Proposition.eqC.trans
  . apply Proposition.eqC.or_comm
  apply Proposition.eqC.or_top


theorem Proposition.eqC.or_assoc {p q r: Proposition}:
  (p.or (q.or r)).eqC ((p.or q).or r)
:= by
  and_intros
  . apply Context.provesC.orE (p := p) (q := q.or r)
    . simp
    . apply Context.provesC.orI1
      apply Context.provesC.orI1
      apply Context.provesC.ax
      simp
    . apply Context.provesC.orE (p := q) (q := r)
      . simp
      . apply Context.provesC.orI1
        apply Context.provesC.orI2
        apply Context.provesC.ax
        simp
      . apply Context.provesC.orI2
        apply Context.provesC.ax
        simp
  . unfold leC
    apply Context.provesC.orE (p := p.or q) (q := r)
    . simp
    . apply Context.provesC.orE (p := p) (q := q)
      . simp
      . apply Context.provesC.orI1
        apply Context.provesC.ax
        simp
      . apply Context.provesC.orI2
        apply Context.provesC.orI1
        apply Context.provesC.ax
        simp
    . apply Context.provesC.orI2
      apply Context.provesC.orI2
      apply Context.provesC.ax
      simp


theorem Proposition.eqC.or_and_distrib {p q r: Proposition}:
  (p.or (q.and r)).eqC ((p.or q).and (p.or r))
:= by
  simp [eqC, leC]
  and_intros
  . solution[[
      apply Context.provesC.orE (p := p) (q := q.and r)
      . simp
      . apply Context.provesC.andI
        . apply Context.provesC.orI1
          simp
        . apply Context.provesC.orI1
          simp
      . apply Context.provesC.andI
        . apply Context.provesC.orI2
          apply Context.provesC.andE1 (q := r)
          simp
        . apply Context.provesC.orI2
          apply Context.provesC.andE2 (p := q)
          simp
      ]]
  . apply Context.provesC.orE (p := p) (q := q)
    . apply Context.provesC.andE1 (q := p.or r)
      simp
    . apply Context.provesC.orI1
      simp
    . apply Context.provesC.orE (p := p) (q := r) <;> simp [Context.add]
      . apply Context.provesC.andE2 (p := p.or q)
        apply Context.provesC.ax
        simp
      . apply Context.provesC.orI1
        simp
      . apply Context.provesC.orI2
        apply Context.provesC.andI
        . apply Context.provesC.ax
          simp
        . apply Context.provesC.ax
          simp


theorem Proposition.eqC.or_and_distrib' {p q r: Proposition}:
  ((p.and q).or r).eqC ((p.or r).and (q.or r))
:= by
  apply Proposition.eqC.trans
  . apply Proposition.eqC.or_comm
  -- Target is changed to `(r.or (p.and q)).eqC ((p.or r).and (q.or r))`.
  -- We can then trigger the previous theorem.
  apply Proposition.eqC.trans
  . apply Proposition.eqC.or_and_distrib
  -- Now, it is `((r.or p).and (r.or q)).eqC ((p.or r).and (q.or r))`
  apply Proposition.eqC.and
  . solution[[
      apply Proposition.eqC.or_comm
    ]]
  . solution[[
      apply Proposition.eqC.or_comm
    ]]


theorem Proposition.eqC.not_top:
  Proposition.top.not.eqC Proposition.bot
:= by
  and_intros
  . apply Context.provesC.impE (p := .top)
    . simp
    . apply Context.provesC.topI
  . apply Context.provesC.botE
    simp


theorem Proposition.eqC.not_bot:
  Proposition.bot.not.eqC Proposition.top
:= by
  and_intros
  . apply Context.provesC.topI
  . apply Context.provesC.impI
    apply Context.provesC.ax
    simp


theorem Proposition.eqC.em {p: Proposition}:
  (p.or p.not).eqC .top
:= by
  and_intros
  . apply Context.provesC.topI
  . apply Context.provesC.em


theorem Proposition.eqC.em' {p: Proposition}:
  (p.not.or p).eqC .top
:= by
  apply Proposition.eqC.trans
  . apply Proposition.eqC.or_comm
  . apply Proposition.eqC.em


theorem Proposition.eqC.deMorgan_or {p q: Proposition}:
  (p.or q).not.eqC (p.not.and q.not)
:= by
  and_intros
  . apply Context.provesC.andI
    . apply Context.provesC.impI
      apply Context.provesC.impE (p := p.or q)
      . apply Context.provesC.ax
        simp
      . apply Context.provesC.orI1
        simp
    . solution[[
        apply Context.provesC.impI
        apply Context.provesC.impE (p := p.or q)
        . apply Context.provesC.ax
          simp
        . apply Context.provesC.orI2
          simp
      ]]
  . apply Context.provesC.impI
    apply Context.provesC.orE (p := p) (q := q)
    . simp
    . apply Context.provesC.impE (p := p)
      . apply Context.provesC.andE1 (q := q.not)
        apply Context.provesC.ax
        simp
      . simp
    . apply Context.provesC.impE (p := q)
      . apply Context.provesC.andE2 (p := p.not)
        apply Context.provesC.ax
        simp
      . simp


theorem Proposition.eqC.deMorgan_and {p q: Proposition}:
  (p.and q).not.eqC (p.not.or q.not)
:= by
  and_intros
  . apply Proposition.eqC.provesC
    . apply Proposition.eqC.imp_not_or
    . apply Context.provesC.impI
      apply Context.provesC.impI
      simp [Context.add]
      solution[[
        apply Context.provesC.impE (p := p.and q)
        . apply Context.provesC.ax
          simp
        . apply Context.provesC.andI
          . apply Context.provesC.ax
            simp
          . apply Context.provesC.ax
            simp
      ]]
  . apply Context.provesC.impI
    simp [Context.add]
    apply Context.provesC.orE (p := p.not) (q := q.not)
    . apply Context.provesC.ax
      simp
    . apply Context.provesC.impE (p := p)
      . apply Context.provesC.ax
        simp
      . apply Context.provesC.andE1 (q := q)
        apply Context.provesC.ax
        simp
    . apply Context.provesC.impE (p := q)
      . apply Context.provesC.ax
        simp
      . apply Context.provesC.andE2 (p := p)
        apply Context.provesC.ax
        simp


/-!
### Soundness
-/

theorem soundnessC {Γ: Context} {p}:
  Γ.provesC p -> Γ.entailsC p
:= by
  intro H
  intro e S
  induction H generalizing e
    <;> try grind [Eval.eval]
  case ax I =>
    apply S
    exact I
  case impI | orE =>
    grind [Eval.eval, Eval.satisfies.add]


theorem weakSoundnessC {p}:
  Context.provesC [] p -> Context.entailsC [] p
:= by
  apply soundnessC


theorem Proposition.leC.eval {p q: Proposition}:
  p.leC q -> forall e: Eval, e.eval (p.imp q) = true
:= by
  unfold Proposition.leC
  intro H e
  replace H := H.impI
  replace H := weakSoundnessC H
  specialize H e
  simp at H
  exact H


theorem Proposition.eqC.eval {p q: Proposition}:
  p.eqC q -> forall e: Eval, e.eval p = e.eval q
:= by
  rintro ⟨H1, H2⟩ e
  replace H1 := H1.eval e
  replace H2 := H2.eval e
  simp [Eval.eval] at H1 H2
  cases H1
  . cases H2
    . simp_all
    . simp_all
  . cases H2
    . simp_all
    . simp_all


/-!
### Completeness via Conjunctive Normal Form
-/


namespace DNF


inductive Literal: Proposition -> Prop where
  | var (x: String): Literal (.var x)
  | not (x: String): Literal (Proposition.var x).not


inductive Disj: Proposition -> Prop where
  | bot: Disj .bot
  | single {p: Proposition}: Literal p -> Disj p
  | or {p q: Proposition}: Disj p -> Disj q -> Disj (p.or q)


inductive Conj: Proposition -> Prop where
  | top: Conj .top
  | single {p: Proposition}: Disj p -> Conj p
  | and {p q: Proposition}: Conj p -> Conj q -> Conj (p.and q)


/--
When `Disj p` and `Disj q1`, `Disj q2`, `Disj q3`,
p ∨ (q1 ∧ (q2 ∧ q3))
= (p ∨ q1) ∧ (p ∨ (q2 ∧ q3))
= (p ∨ q1) ∧ ((p ∨ q2) ∧ (p ∨ q3)),
so the result will be a `Conj`.
-/
def disj_or_conj (p q: Proposition): Proposition :=
  match q with
  | .and q1 q2 => (disj_or_conj p q1).and (disj_or_conj p q2)
  | .top => .top
  | _ => p.or q


theorem disj_or_conj_eqC {p q: Proposition}:
  (disj_or_conj p q).eqC (p.or q)
:= by
  induction q <;> try simp [disj_or_conj]
  case and q1 q2 IH1 IH2 =>
    apply Proposition.eqC.trans
    . apply Proposition.eqC.and
      . exact IH1
      . exact IH2
    . exact Proposition.eqC.or_and_distrib.symm
  case top =>
    simp [Proposition.eqC, Proposition.leC]
    and_intros
    . apply Context.provesC.orI2
      apply Context.provesC.topI
    . apply Context.provesC.topI


theorem disj_or_conj_conj {p q: Proposition}:
  Disj p -> Conj q -> Conj (disj_or_conj p q)
:= by
  intro Hp Hq
  induction Hq
  case top =>
    simp [disj_or_conj]
    apply Conj.top
  case single q Hq =>
    unfold disj_or_conj
    split
    . cases Hq
      contradiction
    . apply Conj.top
    . apply Conj.single
      apply Disj.or
      . exact Hp
      . exact Hq
  case and q1 q2 H1 H2 IH1 IH2 =>
    simp [disj_or_conj]
    apply Conj.and
    . exact IH1
    . exact IH2


/--
When `Disj p1`, `Disj p2` and `Disj q1`, `Disj q2`, `Disj q3`,
(p1 ∧ p2) ∨ (q1 ∧ (q2 ∧ q3))
= (p1 ∨ (q1 ∧ (q2 ∧ q3))) ∧ (p2 ∨ (q1 ∧ (q2 ∧ q3)));
we then apply the previous theorem to get a `Conj`.
-/
def conj_or_conj (p q: Proposition): Proposition :=
  match p with
  | .and p1 p2 => (conj_or_conj p1 q).and (conj_or_conj p2 q)
  | .top => .top
  | p => disj_or_conj p q


theorem conj_or_conj_eqC {p q: Proposition}:
  (conj_or_conj p q).eqC (p.or q)
:= by
  induction p <;> try (simp [conj_or_conj]; apply disj_or_conj_eqC)
  case and p1 p2 IH1 IH2=>
    simp [conj_or_conj]
    apply Proposition.eqC.trans
    . apply Proposition.eqC.and
      . exact IH1
      . exact IH2
    . exact Proposition.eqC.or_and_distrib'.symm
  case top =>
    simp [conj_or_conj]
    and_intros
    . apply Context.provesC.orI1
      simp
    . apply Context.provesC.topI


theorem conj_or_conj_conj {p q: Proposition}:
  Conj p -> Conj q -> Conj (conj_or_conj p q)
:= by
  intro Hp Hq
  induction Hp
  case top =>
    simp [conj_or_conj]
    apply Conj.top
  case single p Hp =>
    unfold conj_or_conj
    split
    . cases Hp
      contradiction
    . apply Conj.top
    . apply disj_or_conj_conj
      . exact Hp
      . exact Hq
  case and p1 p2 H1 H2 IH1 IH2 =>
    simp [conj_or_conj]
    apply Conj.and
    . exact IH1
    . exact IH2


/--
¬ (p1 ∧ p2) = (¬ p1) ∨ (¬ p2)
-/
def conj_not: Proposition -> Proposition
  | .var x => (Proposition.var x).not
  | .not (.var x) => .var x
  | .and p1 p2 => conj_or_conj (conj_not p1) (conj_not p2)
  | .or p1 p2 => (conj_not p1).and (conj_not p2)
  | .top => .bot
  | .bot => .top
  | p => p.not


def conj_not_eqC {p: Proposition}:
  (conj_not p).eqC p.not
:= by
  induction p
  case var x =>
    simp [conj_not]
  case top =>
    simp [conj_not]
    exact Proposition.eqC.not_top.symm
  case bot =>
    simp [conj_not]
    exact Proposition.eqC.not_bot.symm
  case imp p1 p2 IH1 IH2 =>
    unfold conj_not
    split <;> try simp_all  -- contradiction or reflexivity
    -- the only case is some `¬¬x`, which is proved by `Proposition.eqC.dne`
    apply Proposition.eqC.dne
  case and p1 p2 IH1 IH2 =>
    simp [conj_not]
    apply Proposition.eqC.trans
    . apply conj_or_conj_eqC
    apply Proposition.eqC.trans
    . apply Proposition.eqC.or
      . exact IH1
      . exact IH2
    exact Proposition.eqC.deMorgan_and.symm
  case or p1 p2 IH1 IH2 =>
    simp [conj_not]
    apply Proposition.eqC.trans
    . apply Proposition.eqC.and
      . exact IH1
      . exact IH2
    exact Proposition.eqC.deMorgan_or.symm


theorem conj_not_disj_conj {p: Proposition}:
  Disj p -> Conj (conj_not p)
:= by
  intro H
  induction H
  case bot =>
    simp [conj_not]
    apply Conj.top
  case single p H =>
    cases H <;>
    . simp [conj_not]
      apply Conj.single
      apply Disj.single
      constructor
  case or p1 p2 H1 H2 IH1 IH2 =>
    simp [conj_not]
    apply Conj.and
    . exact IH1
    . exact IH2


theorem conj_not_conj_conj {p: Proposition}:
  Conj p -> Conj (conj_not p)
:= by
  intro H
  induction H
  case top =>
    simp [conj_not]
    apply Conj.single
    apply Disj.bot
  case single p H =>
    apply conj_not_disj_conj
    exact H
  case and p1 p2 H1 H2 IH1 IH2 =>
    simp [conj_not]
    apply conj_or_conj_conj
    . exact IH1
    . exact IH2


theorem CNF_exists (p: Proposition):
  exists q: Proposition, Conj q ∧ p.eqC q
:= by
  induction p
  case var x =>
    exists .var x
    and_intros
    . apply Conj.single
      apply Disj.single
      apply Literal.var
    . simp
    . simp
  case bot =>
    exists .bot
    and_intros
    . apply Conj.single
      apply Disj.bot
    . simp
    . simp
  case top =>
    exists .top
    and_intros
    . apply Conj.top
    . simp
    . simp
  case and p1 p2 IH1 IH2 =>
    rcases IH1 with ⟨q1, IH1, E1⟩
    rcases IH2 with ⟨q2, IH2, E2⟩
    exists (q1.and q2)
    apply And.intro
    . apply Conj.and
      . exact IH1
      . exact IH2
    . apply Proposition.eqC.and
      . exact E1
      . exact E2
  case or p1 p2 IH1 IH2 =>
    rcases IH1 with ⟨q1, H1, E1⟩
    rcases IH2 with ⟨q2, H2, E2⟩
    exists (conj_or_conj q1 q2)
    apply And.intro
    . apply conj_or_conj_conj
      . exact H1
      . exact H2
    . apply Proposition.eqC.trans
      . apply Proposition.eqC.or
        . exact E1
        . exact E2
      exact conj_or_conj_eqC.symm
  case imp p1 p2 IH1 IH2 =>
    rcases IH1 with ⟨q1, H1, E1⟩
    rcases IH2 with ⟨q2, H2, E2⟩
    exists conj_or_conj (conj_not q1) q2
    apply And.intro
    . apply conj_or_conj_conj
      . apply conj_not_conj_conj
        exact H1
      . exact H2
    . solution[[
        apply Proposition.eqC.trans
        . apply Proposition.eqC.imp_not_or
        apply Proposition.eqC.trans
        . apply Proposition.eqC.or
          . apply E1.not
          . exact E2
        apply Proposition.eqC.symm
        apply Proposition.eqC.trans
        . apply conj_or_conj_eqC
        apply Proposition.eqC.or
        . apply conj_not_eqC
        . simp
      ]]


def disj_split: Proposition -> List (String × Bool)
  | .var x => [(x, true)]
  | .not (.var x) => [(x, false)]
  | .or p q => disj_split p ++ disj_split q
  | _ => []


def disj_join: List (String × Bool) -> Proposition
  | [] => .bot
  | (x, b)::xs =>
    let p := if b then Proposition.var x else (Proposition.var x).not
    p.or (disj_join xs)


theorem disj_join_append {xs ys: List (String × Bool)}:
  (disj_join (xs ++ ys)).eqC ((disj_join xs).or (disj_join ys))
:= by
  induction xs
  case nil =>
    simp [disj_join]
    apply Proposition.eqC.bot_or.symm
  case cons x xs IH =>
    simp [disj_join]
    split <;>
    . apply Proposition.eqC.trans
      . apply IH.or2
      . apply Proposition.eqC.or_assoc


theorem disj_join_split {p: Proposition}:
  Disj p -> (disj_join (disj_split p)).eqC p
:= by
  intro H
  induction H
  case bot =>
    simp [disj_split, disj_join]
  case single p H =>
    cases H <;>
    . simp [disj_split, disj_join]
      apply Proposition.eqC.or_bot
  case or p1 p2 H1 H2 IH1 IH2 =>
    simp [disj_split]
    apply Proposition.eqC.trans
    . apply disj_join_append
    apply Proposition.eqC.or
    . exact IH1
    . exact IH2


theorem disj_join_perm {l1 l2: List (String × Bool)}:
   l1.Perm l2 -> (disj_join l1).eqC (disj_join l2)
:= by
  intro H
  induction H
  case nil =>
    simp [disj_join]
  case cons x xs ys H IH =>
    simp [disj_join]
    split <;>
    . apply Proposition.eqC.or2
      exact IH
  case swap x y l =>
    simp [disj_join]
    split <;>
    . split <;>
      . apply Proposition.eqC.or_assoc.trans
        apply Proposition.eqC.symm
        apply Proposition.eqC.or_assoc.trans
        apply Proposition.eqC.or1
        apply Proposition.eqC.or_comm
  case trans l1 l2 l3 P12 P23 IH12 IH23 =>
    apply Proposition.eqC.trans
    . exact IH12
    . exact IH23


def disj_eval (l: List (String × Bool)) (e: Eval): Bool :=
  match l with
  | [] => false
  | (x, b) :: xs =>
    let v := e x
    if b then v || disj_eval xs e else (!v) || disj_eval xs e


theorem disj_eval_perm {l1 l2: List (String × Bool)}:
  l1.Perm l2 ->
  forall e: Eval, disj_eval l1 e = disj_eval l2 e
:= by
  intro H e
  induction H
  case nil =>
    simp [disj_eval]
  case cons x xs ys H IH =>
    simp [disj_eval]
    simp [IH]
  case swap x y l =>
    simp [disj_eval]
    grind
  case trans l1 l2 l3 P12 P23 IH12 IH23 =>
    simp_all


theorem disj_eval_join_eq {l: List (String × Bool)}:
  forall e: Eval, disj_eval l e = e.eval (disj_join l)
:= by
  intro e
  induction l
  case nil =>
    simp [disj_join, disj_eval, Eval.eval]
  case cons x xs IH =>
    simp [disj_join, disj_eval, Eval.eval]
    rewrite [IH]
    rcases x with ⟨x, b⟩
    split
    . simp [Eval.eval]
    . simp [Eval.eval]


def split_at (l: List (String × Bool)) (x: String) (b: Bool):
  Option (List (String × Bool) × List (String × Bool))
:= match l with
  | [] => none
  | (y, c) :: ys =>
    if x == y && b == c then some ([], ys)
    else
      match split_at ys x b with
      | none => none
      | some (l1, l2) => some ((y, c) :: l1, l2)


theorem split_at_some {l l1 l2: List (String × Bool)} {x: String} {b: Bool}:
  split_at l x b = some (l1, l2) -> l = l1 ++ (x, b) :: l2
:= by
  intro H
  induction l generalizing l1 l2
  case nil =>
    simp [split_at] at H
  case cons y ys IH =>
    simp [split_at] at H
    split at H
    . cases H
      simp_all
    . split at H
      . -- none
        cases H
      . cases H
        simp
        apply IH
        assumption


theorem split_at_none {l: List (String × Bool)} {x: String} {b: Bool}:
  split_at l x b = none ->
  split_at l x (!b) = none ->
  forall b' e, disj_eval l e = disj_eval l (fun y => if y == x then b' else e y)
:= by
  intro H1 H2 b' e
  induction l
  case nil =>
    simp [disj_eval]
  case cons y ys IH =>
    simp [split_at] at H1 H2
    split at H1 <;> try contradiction
    split at H1 <;> try contradiction
    rename_i E1
    split at H2 <;> try contradiction
    split at H2 <;> try contradiction
    rename_i E2
    specialize IH E1 E2
    simp [disj_eval]
    simp [IH]
    grind


theorem disj_split_tautology {l: List (String × Bool)}:
  (forall e: Eval, disj_eval l e = true) -> (disj_join l).eqC .top
:= by
  intro H
  induction l
  case nil =>
    specialize H (fun _ => false)
    simp only [disj_eval] at H
    cases H
  case cons x xs IH =>
    rcases x with ⟨x, b⟩
    cases E: split_at xs x (!b)
    case some l =>
      rcases l with ⟨l1, l2⟩
      replace E := split_at_some E
      let xs' := (x, !b) :: (l1 ++ l2)
      have P: List.Perm ((x, b)::xs) ((x, b)::xs') := by
        grind
      apply (disj_join_perm P).trans
      simp [disj_join, xs']
      split <;>
      . simp_all
        apply Proposition.eqC.trans
        . apply Proposition.eqC.or_assoc
        apply Proposition.eqC.trans
        . apply Proposition.eqC.or1
          first | apply Proposition.eqC.em | apply Proposition.eqC.em'
        apply Proposition.eqC.top_or
    case none =>
      -- We must have `disj_eval xs e = true` for all `e`.
      have H: forall e: Eval, disj_eval xs e = true := by
        intro e
        cases I: disj_eval xs e
        case true =>
          eq_refl
        case false =>
          let e' := fun y => if y == x then !b else e y
          have I': disj_eval xs e' = false := by
            rewrite [<-I]
            symm
            apply split_at_none _ E
            cases E': split_at xs x b
            case none =>
              eq_refl
            case some l =>
              specialize H e
              simp [disj_eval, I] at H
              rcases l with ⟨l1, l2⟩
              replace E' := split_at_some E'
              let xs' := (x, b) :: (l1 ++ l2)
              have P: List.Perm xs xs' := by grind
              rewrite [disj_eval_perm P] at I
              simp [disj_eval, xs'] at I
              split at H
              . simp_all
              . simp_all
          let H' := H e'
          simp only [disj_eval] at H'
          simp [I'] at H'
          -- note that we choose `e' x = !b`
          simp [e'] at H'
      specialize IH H
      simp [disj_join]
      apply Proposition.eqC.trans
      . apply Proposition.eqC.or2
        exact IH
      . apply Proposition.eqC.or_top


theorem tautology_disj_top {p: Proposition}:
  Context.entailsC [] p -> Disj p -> p.eqC .top
:= by
  intro T D
  let l := disj_split p
  have E: (disj_join l).eqC p := disj_join_split D
  apply E.symm.trans
  apply disj_split_tautology
  intro e
  rewrite [disj_eval_join_eq]
  rewrite [E.eval]
  apply T
  simp


theorem tautology_conj_top {p: Proposition}:
  Context.entailsC [] p -> Conj p -> p.eqC .top
:= by
  intro H C
  induction C
  case top =>
    simp
  case and p1 p2 C1 C2 IH1 IH2 =>
    have H1: Context.entailsC [] p1 := by
        intro e S
        specialize H e S
        simp_all [Eval.eval]
    have H2: Context.entailsC [] p2 := by
      intro e S
      specialize H e S
      simp_all [Eval.eval]
    specialize IH1 H1
    specialize IH2 H2
    have H: (p1.and p2).eqC (Proposition.top.and .top) := by
      apply Proposition.eqC.and
      . exact IH1
      . exact IH2
    apply H.trans
    apply Proposition.eqC.and_idempotent
  case single p D =>
    cases D
    case bot =>
      specialize H (fun _ => false)
      simp [Eval.eval] at H
    case single L =>
      cases L with
      | var x =>
        specialize H (fun _ => false)
        simp [Eval.eval] at H
      | not x =>
        specialize H (fun _ => true)
        simp [Eval.eval] at H
    case or p1 p2 D1 D2 =>
      apply tautology_disj_top
      . exact H
      . apply Disj.or
        . exact D1
        . exact D2


theorem tautology_eqC_top {p: Proposition}:
  Context.entailsC [] p -> p.eqC .top
:= by
  intro H
  rcases CNF_exists p with ⟨q, C, E⟩
  have H: Context.entailsC [] q := by
    intro e S
    rewrite [<-E.eval]
    apply H
    exact S
  replace H := tautology_conj_top H C
  apply E.trans
  exact H


end DNF


theorem weakCompletenessC {p: Proposition}:
  Context.entailsC [] p -> Context.provesC [] p
:= by
  intro H
  replace H := DNF.tautology_eqC_top H
  apply H.symm.provesC
  apply Context.provesC.topI


theorem completenessC {Γ: Context} {p}:
  Γ.entailsC p -> Γ.provesC p
:= by
  induction Γ generalizing p
  case nil =>
    apply weakCompletenessC
  case cons x xs IH =>
    intros H
    replace H := entailsC_imp_iff.mp H
    specialize IH H
    apply Context.provesC.impE
    . apply IH.weaken_add
    . simp


/-!
## Intuitionistic Logic

### Syntax
-/

/--
Intuitionistic provability relation.
-/
inductive Context.proves: Context -> Proposition -> Prop where
  | ax {Γ: Context} {p} : p ∈ Γ -> Γ.proves p
  | topI {Γ: Context}: Γ.proves .top
  | andI {Γ: Context} {p q} : Γ.proves p -> Γ.proves q -> Γ.proves (Proposition.and p q)
  | andE1 {Γ: Context} {p q} : Γ.proves (Proposition.and p q) -> Γ.proves p
  | andE2 {Γ: Context} {p q} : Γ.proves (Proposition.and p q) -> Γ.proves q
  | impI {Γ: Context} {p q} : (Γ.add p).proves q -> Γ.proves (Proposition.imp p q)
  | impE {Γ: Context} {p q: Proposition}: Γ.proves (p.imp q) -> Γ.proves p -> Γ.proves q
  | botE {Γ: Context} {p} : Γ.proves Proposition.bot -> Γ.proves p
  | orI1 {Γ: Context} {p q} : Γ.proves p -> Γ.proves (Proposition.or p q)
  | orI2 {Γ: Context} {p q} : Γ.proves q -> Γ.proves (Proposition.or p q)
  | orE {Γ: Context} {p q r} : Γ.proves (Proposition.or p q) -> (Γ.add p).proves r -> (Γ.add q).proves r -> Γ.proves r


theorem Context.proves.permute {Γ Γ': Context} {p}:
  Γ.proves p ->
  Γ.Perm Γ' ->
  Context.proves Γ' p
:= by
  intro H P
  induction H generalizing Γ'
    <;> try grind [Context.proves]
  case impI Γ p q H IH =>
    apply Context.proves.impI
    simp [Context.add] at *
    apply IH
    simp
    exact P
  case orE Γ p q r H H1 H2 IH IH1 IH2 =>
    apply Context.proves.orE
    . apply IH P
    . apply IH1
      simp
      exact P
    . apply IH2
      simp
      exact P


theorem Context.proves.weaken {Γ Γ': Context} {p}:
  Γ.proves p ->
  Γ.Sublist Γ' ->
  Context.proves (Γ') p
:= by
  intro H R
  induction H generalizing Γ'
    <;> grind [Context.proves]


/-!
### Semantics
We use _Kripke models_ for semantics of intuitionistic logic. In classical logic, we use the type `Bool`,
which is a special case of _Boolean algebra_. Readers familiar with logic may expect _Heyting algebra_
as the semantic model for intuitionistic logic. It turns out that Kripke models are just special cases
of Heyting algebra in some [presheaves category][maclane2012sheaves].
-/


structure Kripke where
  W: Type
  R: W -> W -> Prop
  R_refl: forall {w: W}, R w w
  R_trans: forall {w1 w2 w3: W}, R w1 w2 -> R w2 w3 -> R w1 w3

  Cover: List W -> W -> Prop
  Cover_nonempty: forall {w}, ¬ Cover [] w
  Cover_R: forall {C: List W} {w: W}, Cover C w -> forall (w': W), w' ∈ C -> R w w'
  Cover_self: forall {w: W}, Cover [w] w
  /-
  Stability as in Mac Lane's _Sheaves in Geometry and Logic_.
  -/
  Cover_pullback: forall {C w u},
    Cover C w ->
    R w u ->
    exists D, Cover D u ∧ (forall u', u' ∈ D -> exists w', w' ∈ C ∧ R w' u')
  Cover_trans: forall {C w} {P: W -> Prop},
    Cover C w ->
    (f: forall w', w' ∈ C -> exists D, Cover D w' ∧ forall w'', w'' ∈ D -> P w'') ->
    exists D, Cover D w ∧ (forall w'', w'' ∈ D -> P w'')

  F: W -> String -> Prop
  F_monotone: forall {w1 w2 x}, R w1 w2 -> F w1 x -> F w2 x
  F_cover: forall {C w x}, Cover C w -> (forall w', w' ∈ C -> F w' x) -> F w x


def Kripke.forces (K: Kripke) (w: K.W) (p: Proposition): Prop :=
  match p with
  | .var x => K.F w x
  | .top => True
  | .bot => False
  | .and p q => K.forces w p ∧ K.forces w q
  | .or p q => exists C: List K.W, K.Cover C w ∧ (forall w', w' ∈ C -> K.forces w' p ∨ K.forces w' q)
  | .imp p q => forall w', K.R w w' -> K.forces w' p -> K.forces w' q


theorem Kripke.forces_weak {K: Kripke} {w1 w2: K.W} {p: Proposition}:
  K.R w1 w2 -> K.forces w1 p -> K.forces w2 p
:= by
  intro R F
  induction p generalizing w1 w2
  case var x =>
    apply K.F_monotone
    . exact R
    . exact F
  case top =>
    simp [Kripke.forces]
  case bot =>
    simp [Kripke.forces] at F
  case and p1 p2 IH1 IH2 =>
    simp [Kripke.forces] at *
    grind
  case imp p1 p2 IH1 IH2 =>
    intro w2' R' F'
    have R'': K.R w1 w2' := K.R_trans R R'
    apply F
    . apply K.R_trans R R'
    . exact F'
  case or p1 p2 IH1 IH2 =>
    simp [Kripke.forces] at F
    rcases F with ⟨C, HC, H⟩
    rcases K.Cover_pullback HC R with ⟨D, HD, S⟩
    exists D
    and_intros
    . exact HD
    . intro w' I
      rcases S w' I with ⟨w'', I'', R'⟩
      specialize H w'' I''
      cases H with
      | inl H =>
        left
        apply IH1 R'
        exact H
      | inr H =>
        right
        apply IH2 R'
        exact H


theorem Kripke.forces_cover {K: Kripke} {C: List K.W} {w: K.W} {p: Proposition}:
  K.Cover C w -> (forall w', w' ∈ C -> K.forces w' p) -> K.forces w p
:= by
  intro HC H
  induction p generalizing C w
  case var x =>
    apply K.F_cover HC
    exact H
  case top =>
    simp [Kripke.forces]
  case bot =>
    cases C
    case nil =>
      exfalso
      apply K.Cover_nonempty HC
    case cons w' C =>
      specialize H w' (by simp)
      simp [Kripke.forces] at H
  case and p1 p2 IH1 IH2 =>
    simp [Kripke.forces] at *
    solution[[
      grind
    ]]
  case imp p1 p2 IH1 IH2 =>
    intro w' R F
    rcases K.Cover_pullback HC R with ⟨D, HD, S⟩
    apply IH2 HD
    intro w'' I
    rcases S w'' I with ⟨w''', I', R'⟩
    specialize H w''' I'
    apply H
    . exact R'
    . apply Kripke.forces_weak _ F
      apply K.Cover_R
      . exact HD
      . exact I
  case or p1 p2 IH1 IH2 =>
    let P := fun w: K.W => K.forces w p1 ∨ K.forces w p2
    have f: ∀ (w' : K.W), w' ∈ C → ∃ D, K.Cover D w' ∧ forall w'', w'' ∈ D -> P w'' := by
      intro w' I
      simp [P]
      specialize H w' I
      rcases H with ⟨D, HD, H⟩
      exists D
    rcases K.Cover_trans HC f with ⟨D, HD, T⟩
    exists D


def Context.entails (Γ: Context) (p: Proposition): Prop :=
  forall K: Kripke, forall w: K.W, (forall q, q ∈ Γ -> K.forces w q) -> K.forces w p

/-!
### Soundness
-/

theorem soundness {Γ: Context} {p}:
  Γ.proves p -> Γ.entails p
:= by
  intro H K w S
  induction H generalizing K w
  case ax I =>
    apply S
    exact I
  case topI =>
    simp [Kripke.forces]
  case botE Γ p H IH =>
    specialize IH K w S
    simp [Kripke.forces] at IH
  case andI Γ p q H1 H2 IH1 IH2 =>
    simp [Kripke.forces]
    and_intros
    . apply IH1
      exact S
    . apply IH2
      exact S
  case andE1 Γ p q H IH | andE2 Γ p q H IH =>
    specialize IH K w S
    simp [Kripke.forces] at IH
    simp_all
  case impI Γ p q H IH =>
    simp [Kripke.forces]
    intro w' R F
    apply IH
    intro r I
    simp at I
    cases I with
    | inl I =>
      simp_all
    | inr I =>
      apply Kripke.forces_weak R
      apply S
      exact I
  case impE Γ p q H1 H2 IH1 IH2 =>
    specialize IH1 K w S w
    apply IH1
    . apply K.R_refl
    . apply IH2
      exact S
  case orI1 Γ p q H IH | orI2 Γ p q H IH =>
    simp [Kripke.forces]
    specialize IH K w S
    exists [w]
    and_intros
    . apply K.Cover_self
    . intro w' I
      simp_all
  case orE Γ p q r H1 H2 H3 IH1 IH2 IH3 =>
    specialize IH1 K w S
    simp [Kripke.forces] at IH1
    rcases IH1 with ⟨C, HC, H⟩
    apply Kripke.forces_cover HC
    intro w' I
    specialize H w' I
    have R: K.R w w' := K.Cover_R HC _ I
    cases H with
    | inl H =>
      apply IH2
      intro a I'
      simp at I'
      cases I' with
      | inl I' =>
        simp_all
      | inr I' =>
        apply Kripke.forces_weak R
        apply S
        exact I'
    | inr H =>
      apply IH3
      intro a I'
      simp at I'
      cases I' with
      | inl I' =>
        simp_all
      | inr I' =>
        apply Kripke.forces_weak R
        apply S
        exact I'


/-!
### Completeness
-/

axiom Context.decide (Γ: Context) p: Decidable (Γ.proves p)

namespace UniversalModel


def World: Type := {Γ: Context // ¬ Γ.proves .bot}

def Cover (C: List World) (w: World): Prop :=
  (¬ C = []) ∧
  (forall w', w' ∈ C -> w.val.Sublist w'.val) ∧
  forall {p}, (forall w, w ∈ C -> w.val.proves p) -> w.val.proves p


theorem Cover.exists {C: List World} {w: World}:
  Cover C w ->
  exists w', w' ∈ C ∧ w.val.Sublist w'.val
:= by
  intro HC
  cases C
  case nil =>
    simp [Cover] at HC
  case cons w' C =>
    exists w'
    simp_all [Cover]


theorem Cover.sub {C: List World} {w: World}:
  Cover C w ->
  forall w', w' ∈ C -> w.val.Sublist w'.val
:= by
  simp_all [Cover]


theorem Cover.proves {C: List World} {w: World}:
  Cover C w ->
  forall {p}, (forall w, w ∈ C -> w.val.proves p) -> w.val.proves p
:= by
  simp_all [Cover]


def mapWithIn {A B} (l: List A) (f: (x: A) -> (x ∈ l) -> B): List B :=
  match l with
  | [] => []
  | x :: xs =>
    let b := f x (by simp)
    let bs := mapWithIn xs (fun y I => f y (by simp [I]))
    b :: bs


theorem mapWithIn_spec {A B} {l: List A} {f: (x: A) -> (x ∈ l) -> B}:
  forall {y}, y ∈ mapWithIn l f <-> exists x, exists I: x ∈ l, y = f x I
:= by
  induction l
  case nil =>
    simp [mapWithIn]
  case cons x xs IH =>
    simp [mapWithIn]
    grind


def multiImp (Γ: Context) (p: Proposition): Proposition :=
  match Γ with
  | [] => p
  | q :: qs => q.imp (multiImp qs p)


theorem multiImp_iff {Δ Γ: Context} {p: Proposition}:
  (Δ ++ Γ).proves p <-> Γ.proves (multiImp Δ p)
:= by
  induction Δ generalizing Γ p
  case nil =>
    simp [multiImp]
  case cons q Δ IH =>
    simp [multiImp]
    apply Iff.intro
    . intro H
      apply Context.proves.impI
      apply IH.mp
      apply H.permute
      simp [Context.add]
      apply List.perm_comm.mp
      simp
    . intro H
      replace H: Context.proves (q :: Γ) (multiImp Δ p) := by
        apply Context.proves.impE
        . apply H.weaken
          simp
        . apply Context.proves.ax
          simp
      replace H := IH.mpr H
      apply H.permute
      simp


theorem weak_append {Γ Γ': Context} {p}:
  Γ.Sublist Γ' ->
  Context.proves (Γ' ++ Γ) p ->
  Γ'.proves p
:= by
  intro R H
  replace H: (Γ ++ Γ').proves p := by
    apply H.permute
    apply List.perm_append_comm
  induction Γ generalizing Γ' p
  case nil =>
    simp_all
  case cons q Γ IH =>
    replace H := H.impI
    specialize IH (by grind) H
    apply IH.impE
    apply Context.proves.ax
    grind


def Model: Kripke where
  W := World
  R := fun w1 w2 => w1.val.Sublist w2.val
  R_refl := by simp
  R_trans := by
    intro w1 w2 w3
    apply List.Sublist.trans

  Cover := Cover
  Cover_nonempty := by
    simp [Cover]
  Cover_R := by
    intro C w HC
    simp [Cover] at HC
    replace HC := HC.right.left
    apply HC
  Cover_self := by
    intro w
    unfold Cover
    grind
  Cover_pullback := by
    intro C w u HC R
    have H: exists L1 L2: List Context,
      (forall w', w' ∈ C <-> w'.val ∈ L1 ∨ w'.val ∈ L2) ∧
      (forall Γ: Context, Γ ∈ L1 -> ¬ (u.val ++ Γ).proves .bot) ∧
      (forall Γ: Context, Γ ∈ L2 -> (u.val ++ Γ).proves .bot)
    := by
      clear HC
      induction C
      case nil =>
        exists [], []
        simp
      case cons w' C IH =>
        rcases IH with ⟨L1, L2, I, H1, H2⟩
        cases (u.val ++ w'.val).decide .bot
        case isTrue =>
          exists L1, (w'.val :: L2)
          grind [Subtype.ext]
        case isFalse =>
          exists (w'.val :: L1), L2
          grind [Subtype.ext]
    rcases H with ⟨L1, L2, I, H1, H2⟩
    rcases HC with ⟨NE, S, HC⟩
    let f: (x: Context) -> (x ∈ L1) -> World := (fun Γ I => ⟨u.val ++ Γ, H1 Γ I⟩)
    let D: List World := mapWithIn L1 f
    exists D
    and_intros
    . intro E
      -- Since `D = []`, we must also have `L1 = []`.
      cases L1
      case cons => -- This case is impossible, since `D` is forced non-empty.
        simp [D, mapWithIn] at E
      -- Now, forall `w'`, `w' ∈ C` iff `w'.val ∈ L2`.
      simp at I  -- We get that simply by `simp` at `I`.
      -- This means `u.val ++ w'.val` is inconsistent, i.e. `w'.val ⊢ ¬ u.val`.
      have H: forall w', w' ∈ C -> w'.val.proves (multiImp u.val .bot) := by
        intro w' I'
        apply multiImp_iff.mp
        apply H2
        apply (I w').mp
        exact I'
      -- Since `C` covers `w`, we can conclude that `w ⊢ ¬ u.val`,
      specialize HC H
      -- which makes `u.val ++ w.val` inconsistent,
      replace HC := multiImp_iff.mpr HC
      -- which further implies `u` is inconsistent -- a contradiction.
      replace HC := weak_append R HC
      apply u.property
      exact HC
    . intro u' H
      replace H := mapWithIn_spec.mp H
      grind
    . intro p HD
      apply weak_append R
      apply multiImp_iff.mpr
      apply HC
      intro w'' I'
      replace I' := (I w'').mp I'
      rcases I' with I' | I'
      . let y: World := ⟨u.val ++ w''.val, H1 w''.val I'⟩
        replace I': y ∈ D := by
          apply mapWithIn_spec.mpr
          exists w''.val, I'
        specialize HD y I'
        simp [y] at HD
        apply multiImp_iff.mp
        exact HD
      . apply multiImp_iff.mp
        specialize H2 _ I'
        apply H2.botE
    . intro u' H
      replace H := mapWithIn_spec.mp H
      rcases H with ⟨Γ, I', E⟩
      have _: ¬ Γ.proves .bot := by
        intro contra
        apply H1 _ I'
        apply contra.weaken
        simp
      let w': World := ⟨Γ, by assumption⟩
      exists w'
      simp_all [w', f]
  Cover_trans := by
    intro C w P HC f
    have HD: exists D: List World,
      forall x,
        x ∈ D <->
        exists w', exists (I: w' ∈ C),
          x ∈ (f w' I).choose
    := by
      clear HC
      induction C
      case nil =>
        exists []
        -- `x ∈ []` is impossilbe, while `I: w' ∈ []` is also impossible.
        simp
      case cons w' ws' IH =>
        -- We first get the cover `D` of `w`.
        have I': w' ∈ w' :: ws' := by simp
        let T := f w' I'
        let D := T.choose
        -- Then, we get the accumulated result `D'` of `ws'` from `IH`.
        have f': ∀ (w' : World),
            w' ∈ ws' →
            ∃ D, Cover D w' ∧ ∀ (w'' : World), w'' ∈ D → P w''
        := by
          intros w' I'
          apply f
          simp_all
        rcases IH f' with ⟨D', HD'⟩
        exists (D ++ D')
        intro x
        apply Iff.intro
        . grind
        . rintro ⟨w'', I'', H''⟩
          simp at I''
          rcases I'' with E | I''
          . let F := f w'' I''
            simp only [E] at H''
            replace H'': x ∈ D := by
              apply H''
            simp [H'']
          . grind
    rcases HD with ⟨D, HD⟩
    exists D
    and_intros
    . intro E
      rcases HC.exists with ⟨w', I', _⟩
      -- `C` is not `[]`
      let T := f w' I'
      let C' := T.choose
      let HC' := T.choose_spec.left
      rcases HC'.exists with ⟨w'', I'', _⟩
      replace HD := (HD w'').mpr ⟨w', I', I''⟩
      simp [E] at HD
    . intro w' I'
      replace HD := (HD w').mp I'
      rcases HD with ⟨w'', I'', HD⟩
      let H := (f w'' I'').choose_spec.left
      apply List.Sublist.trans
      . apply HC.sub
        exact I''
      . apply H.sub
        exact HD
    . intro p H
      apply HC.proves
      intro w' I'
      let T := f w' I'
      let C' := T.choose
      let HC' := T.choose_spec.left
      apply HC'.proves
      intro w'' I''
      apply H
      apply (HD w'').mpr
      exists w', I'
    . intro w'' I''
      -- can be proved by `grind`
      replace HD := (HD w'').mp I''
      rcases HD with ⟨w', I', HD⟩
      let C' := (f w' I').choose
      let HC' := (f w' I').choose_spec.right
      apply HC'
      exact HD
  F w x := w.val.proves (Proposition.var x)
  F_monotone := by
    intro w1 w2 x
    intro R H
    apply H.weaken R
  F_cover {C w x} := by
    intro HC P
    apply HC.right.right
    exact P


theorem forces_iff_proves {w: World} {p: Proposition}:
  Model.forces w p <-> w.val.proves p
:= by
  induction p generalizing w
  case var x =>
    simp [Kripke.forces, Model]
  case top =>
    simp [Kripke.forces]
    apply Context.proves.topI
  case bot =>
    simp [Kripke.forces]
    exact w.property
  case and p1 p2 IH1 IH2 =>
    simp [Kripke.forces]
    apply Iff.intro
    . intro H
      rcases H with ⟨H1, H2⟩
      replace IH1 := IH1.mp H1
      replace IH2 := IH2.mp H2
      exact Context.proves.andI IH1 IH2
    . intro H
      have H1 := Context.proves.andE1 H
      have H2 := Context.proves.andE2 H
      replace IH1 := IH1.mpr H1
      replace IH2 := IH2.mpr H2
      exact ⟨IH1, IH2⟩
  case or p1 p2 IH1 IH2 =>
    apply Iff.intro
    . intro H
      rcases H with ⟨C, HC, H⟩
      simp [Model] at HC
      rcases HC with ⟨N, S, P⟩
      apply P
      intro w I
      specialize H w I
      rcases H with H | H
      . replace IH1 := IH1.mp H
        exact IH1.orI1
      . replace IH2 := IH2.mp H
        exact IH2.orI2
    . intro H
      rcases w with ⟨Γ, C⟩
      simp at H
      let Γ1 := Γ.add p1
      let Γ2 := Γ.add p2
      rcases Γ1.decide .bot with C1 | I1
      case isTrue => -- If p1 :: Γ is inconsistent, then Γ ⊢ p1.
        replace H: Γ.proves p2 := by
          apply H.orE
          . apply I1.botE
          . apply Context.proves.ax
            simp
        -- Since Γ covers itself, we can conclude that Γ ⊩ p1 ∨ p2.
        exists [⟨Γ, C⟩]
        simp [Model.Cover_self]
        right
        apply IH2.mpr
        exact H
      -- Now we have Γ1 is consistent.
      -- similarly, we discuss whether p2 :: Γ is inconsistent.
      rcases Γ2.decide .bot with C2 | I2
      case isTrue => -- We simply prove it by a `grind`.
        exists [⟨Γ, C⟩]
        grind [Model.Cover_self, Context.proves]
      -- Now that both p1 :: Γ and p2 :: Γ are consistent, we can construct a cover.
      let w1: World := ⟨Γ1, C1⟩
      let w2: World := ⟨Γ2, C2⟩
      exists [w1, w2]
      have K: forall {w}, w ∈ [w1, w2] -> w = w1 ∨ w = w2 := by
        grind
      and_intros
      . simp
      . intro w I
        rcases K I with I | I
        . simp_all [w1, Γ1]
        . simp_all [w2, Γ2]
      . intro p HC
        apply H.orE
        . apply HC w1
          apply List.Mem.head
        . apply HC w2
          apply List.Mem.tail
          apply List.Mem.head
      . intro w' I
        rcases K I with I | I
        . simp_all [w1, Γ1]
          left
          apply Context.proves.ax
          simp
        . simp_all [w2, Γ2]
          right
          apply Context.proves.ax
          simp
  case imp p1 p2 IH1 IH2 =>
    apply Iff.intro
    . intro H
      let Γ := w.val.add p1
      rcases Γ.decide .bot with C | I
      case isTrue =>
        apply Context.proves.impI
        apply I.botE
      case isFalse =>
        let w': World := ⟨Γ, C⟩
        have F: Model.forces w' p1 := by
          apply IH1.mpr
          simp [w', Γ]
          apply Context.proves.ax
          simp
        specialize H w' (by simp [Model, w', Γ]) F
        replace IH2 := IH2.mp H
        apply Context.proves.impI
        exact IH2
    . intro H
      simp [Kripke.forces]
      intro w' R F
      replace H: w'.val.proves (p1.imp p2) := by
        simp [Model] at R
        apply H.weaken
        exact R
      apply IH2.mpr
      apply Context.proves.impE
      . exact H
      . apply IH1.mp
        exact F


end UniversalModel

theorem completeness {Γ: Context} {p}:
  Γ.entails p -> Γ.proves p
:= by
  intro H
  rcases Γ.decide .bot with C | I
  case isTrue => -- If Γ is inconsistent, this is obvious.
    apply I.botE
  -- We then use the universal model for the consistent case.
  have K: forall p, p ∈ Γ -> UniversalModel.Model.forces ⟨Γ, C⟩ p := by
    intro p I
    apply UniversalModel.forces_iff_proves.mpr
    apply Context.proves.ax
    exact I
  specialize H UniversalModel.Model ⟨Γ, C⟩ K
  replace H := UniversalModel.forces_iff_proves.mp H
  exact H

/-!
## λ-Calculus and Curry-Howard Correspondence
-/

/-!
### Glivenko's theorem
-/

end PropLogic
