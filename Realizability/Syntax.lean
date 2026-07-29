/-
# Syntax: terms, formulas, and derivations for the fragment

The fragment of the project brief: intuitionistic propositional logic
(`∧, ∨, →`, with `¬φ` as `φ → ⊥`) over atomic equations between
`0`/`succ`-terms with variables, one quantifier rule pair (`∀`-intro /
`∀`-elim over `ℕ`), three arithmetic axiom schemas: decidable
equality (`s = t ∨ ¬ s = t`), `succ s ≠ 0`, and injectivity of `succ` —
and, since the Phase-2 extension, the **arithmetic induction rule**
`ind`: from `φ(0)` and `∀x (φ(x) → φ(succ x))`, conclude `∀x φ(x)`
(see STATUS.md for its realizer, the primitive-recursion combinator).

Natural deduction is an inductive family `Deriv Γ φ` in `Type`, so the
extraction function of `Extraction.lean` can recurse on it.  Hypotheses
are managed structurally (`ax` reads the head of the context, `wk`
weakens), which matches the curried-context extraction discipline.

Substitution bookkeeping is kept minimal: `∀`-elim carries the side
condition that the substituted term's variables are not bound in the
formula (no capture), `∀`-intro the usual freshness condition for
the context, and `ind` the same no-capture condition as `∀`-elim for
`succ x` — the term its step case substitutes.
-/
import Mathlib.Logic.Function.Basic

namespace Realizability

/-- Terms: variables (named by numbers), zero, successor. -/
inductive Term : Type where
  | var : ℕ → Term
  | zero : Term
  | succ : Term → Term
deriving DecidableEq, Repr

namespace Term

/-- Evaluation in an environment. -/
def eval (ρ : ℕ → ℕ) : Term → ℕ
  | var i => ρ i
  | zero => 0
  | succ t => t.eval ρ + 1

/-- The variables occurring in a term. -/
def vars : Term → List ℕ
  | var i => [i]
  | zero => []
  | succ t => t.vars

/-- Substitution of a term for a variable. -/
def subst (x : ℕ) (u : Term) : Term → Term
  | var i => if i = x then u else var i
  | zero => zero
  | succ t => succ (subst x u t)

/-- Evaluation after substitution is evaluation in the updated
environment. -/
theorem eval_subst (ρ : ℕ → ℕ) (x : ℕ) (u : Term) :
    ∀ t : Term, (subst x u t).eval ρ
      = t.eval (Function.update ρ x (u.eval ρ)) := by
  intro t
  induction t with
  | var i =>
    by_cases h : i = x
    · subst h
      simp [subst, eval, Function.update]
    · simp [subst, eval, h, Function.update]
  | zero => rfl
  | succ t ih => simp [subst, eval, ih]

/-- Evaluation only depends on the values of the occurring variables. -/
theorem eval_congr {ρ ρ' : ℕ → ℕ} :
    ∀ {t : Term}, (∀ y ∈ t.vars, ρ y = ρ' y) → t.eval ρ = t.eval ρ' := by
  intro t
  induction t with
  | var i => intro h; exact h i (by simp [vars])
  | zero => intro _; rfl
  | succ t ih => intro h; simp only [eval]; rw [ih h]

end Term

/-- Formulas of the fragment. -/
inductive Formula : Type where
  | bot : Formula
  | eq : Term → Term → Formula
  | and : Formula → Formula → Formula
  | or : Formula → Formula → Formula
  | imp : Formula → Formula → Formula
  | all : ℕ → Formula → Formula
deriving DecidableEq, Repr

namespace Formula

/-- Negation is implication into absurdity. -/
def neg (φ : Formula) : Formula := φ.imp bot

/-- Free occurrence of a variable. -/
def FreeIn (x : ℕ) : Formula → Prop
  | bot => False
  | eq s t => x ∈ s.vars ∨ x ∈ t.vars
  | and φ ψ => FreeIn x φ ∨ FreeIn x ψ
  | or φ ψ => FreeIn x φ ∨ FreeIn x ψ
  | imp φ ψ => FreeIn x φ ∨ FreeIn x ψ
  | all y φ => x ≠ y ∧ FreeIn x φ

/-- The variables bound somewhere in a formula. -/
def binders : Formula → List ℕ
  | bot => []
  | eq _ _ => []
  | and φ ψ => φ.binders ++ ψ.binders
  | or φ ψ => φ.binders ++ ψ.binders
  | imp φ ψ => φ.binders ++ ψ.binders
  | all y φ => y :: φ.binders

/-- Substitution of a term for a variable (stops at a rebinding of the
same variable; capture is excluded by the `SubstOK` side condition). -/
def subst (x : ℕ) (u : Term) : Formula → Formula
  | bot => bot
  | eq s t => eq (Term.subst x u s) (Term.subst x u t)
  | and φ ψ => and (subst x u φ) (subst x u ψ)
  | or φ ψ => or (subst x u φ) (subst x u ψ)
  | imp φ ψ => imp (subst x u φ) (subst x u ψ)
  | all y φ => if y = x then all y φ else all y (subst x u φ)

/-- Side condition for `∀`-elimination: no variable of the substituted
term is bound in the formula. -/
def SubstOK (u : Term) (φ : Formula) : Prop :=
  ∀ y ∈ u.vars, y ∉ φ.binders

end Formula

/-- A variable is fresh for a context when it is free in none of its
formulas. -/
def FreshIn (x : ℕ) (Γ : List Formula) : Prop :=
  ∀ φ ∈ Γ, ¬ φ.FreeIn x

open Formula in
/-- **Natural deduction for the fragment.**  Contexts are lists (head =
most recent hypothesis); `Type`-valued so extraction can recurse. -/
inductive Deriv : List Formula → Formula → Type where
  | ax {Γ : List Formula} {φ : Formula} : Deriv (φ :: Γ) φ
  | wk {Γ : List Formula} {φ ψ : Formula} : Deriv Γ φ → Deriv (ψ :: Γ) φ
  | andI {Γ : List Formula} {φ ψ : Formula} :
      Deriv Γ φ → Deriv Γ ψ → Deriv Γ (φ.and ψ)
  | andE₁ {Γ : List Formula} {φ ψ : Formula} : Deriv Γ (φ.and ψ) → Deriv Γ φ
  | andE₂ {Γ : List Formula} {φ ψ : Formula} : Deriv Γ (φ.and ψ) → Deriv Γ ψ
  | orI₁ {Γ : List Formula} {φ ψ : Formula} : Deriv Γ φ → Deriv Γ (φ.or ψ)
  | orI₂ {Γ : List Formula} {φ ψ : Formula} : Deriv Γ ψ → Deriv Γ (φ.or ψ)
  | orE {Γ : List Formula} {φ ψ χ : Formula} : Deriv Γ (φ.or ψ) →
      Deriv (φ :: Γ) χ → Deriv (ψ :: Γ) χ → Deriv Γ χ
  | impI {Γ : List Formula} {φ ψ : Formula} :
      Deriv (φ :: Γ) ψ → Deriv Γ (φ.imp ψ)
  | impE {Γ : List Formula} {φ ψ : Formula} :
      Deriv Γ (φ.imp ψ) → Deriv Γ φ → Deriv Γ ψ
  | botE {Γ : List Formula} {φ : Formula} : Deriv Γ .bot → Deriv Γ φ
  | allI {Γ : List Formula} {x : ℕ} {φ : Formula} :
      Deriv Γ φ → FreshIn x Γ → Deriv Γ (.all x φ)
  | allE {Γ : List Formula} {x : ℕ} {φ : Formula} (u : Term) :
      Deriv Γ (.all x φ) → Formula.SubstOK u φ → Deriv Γ (φ.subst x u)
  | ind {Γ : List Formula} {x : ℕ} {φ : Formula} :
      Deriv Γ (φ.subst x .zero) →
      Deriv Γ (.all x (φ.imp (φ.subst x (.succ (.var x))))) →
      Formula.SubstOK (.succ (.var x)) φ →
      Deriv Γ (.all x φ)
  | eqDec {Γ : List Formula} (s t : Term) :
      Deriv Γ ((eq s t).or (eq s t).neg)
  | succNeZero {Γ : List Formula} (s : Term) :
      Deriv Γ (eq (.succ s) .zero).neg
  | succInj {Γ : List Formula} (s t : Term) :
      Deriv Γ ((eq (.succ s) (.succ t)).imp (eq s t))

end Realizability
