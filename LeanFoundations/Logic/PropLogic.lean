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
  solution[[
    . apply Proposition.eqC.or_comm
    . apply Proposition.eqC.or_comm
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
    cases H
    all_goals
      simp [conj_not]
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


theorem tautology_disj_top {p: Proposition}:
  Context.entailsC [] p -> Disj p -> p.eqC .top
:= by
  admit


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



/-!
### Semantics
We use _Kripke models_ for semantics of intuitionistic logic. In classical logic, we use the type `Bool`,
which is a special case of _Boolean algebra_. Readers familiar with logic may expect _Heyting algebra_
as the semantic model for intuitionistic logic. It turns out that Kripke models are just special cases
of Heyting algebra in some [presheaves category][maclane2012sheaves].
-/

/-!
### Soundness and Completeness
-/

/-!
## Glivenko's theorem
-/

/-!
## λ-Calculus and Curry-Howard Correspondence
-/

end PropLogic
