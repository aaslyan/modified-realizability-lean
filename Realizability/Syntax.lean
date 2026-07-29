/-
# Syntax: terms, formulas, and derivations for the fragment

The fragment of the project brief: intuitionistic propositional logic
(`∧, ∨, →`, with `¬φ` as `φ → ⊥`) over atomic equations between
`0`/`succ`/`+`/`×`-terms with variables, one quantifier rule pair
(`∀`-intro / `∀`-elim over `ℕ`), three arithmetic axiom schemas:
decidable equality (`s = t ∨ ¬ s = t`), `succ s ≠ 0`, and injectivity
of `succ` — and, since the Phase-2 extension, the **arithmetic
induction rule** `ind`: from `φ(0)` and `∀x (φ(x) → φ(succ x))`,
conclude `∀x φ(x)` (see STATUS.md for its realizer, the
primitive-recursion combinator).

Since the Phase-A extension the signature includes `+` and `×` as
genuine function symbols, with two further schema groups (all with
contentless realizers, like the successor axioms): the
**equational-logic kit** (reflexivity, and symmetry / transitivity /
congruence as implication schemas, one congruence per function symbol),
and the **recursion equations defining `+` and `×`** — recursing on the
*first* argument (`0 + t = t`, `succ s + t = succ (s + t)`,
`0 × t = 0`, `succ s × t = (s × t) + t`), so that the classical
second-argument equations (`x + 0 = x`, …) are genuine theorems proved
by `ind` in `Arithmetic.lean`.

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

/-- Terms: variables (named by numbers), zero, successor, and — since
the Phase-A extension — sum and product. -/
inductive Term : Type where
  | var : ℕ → Term
  | zero : Term
  | succ : Term → Term
  | plus : Term → Term → Term
  | times : Term → Term → Term
deriving DecidableEq, Repr

namespace Term

/-- Evaluation in an environment. -/
def eval (ρ : ℕ → ℕ) : Term → ℕ
  | var i => ρ i
  | zero => 0
  | succ t => t.eval ρ + 1
  | plus s t => s.eval ρ + t.eval ρ
  | times s t => s.eval ρ * t.eval ρ

/-- The variables occurring in a term. -/
def vars : Term → List ℕ
  | var i => [i]
  | zero => []
  | succ t => t.vars
  | plus s t => s.vars ++ t.vars
  | times s t => s.vars ++ t.vars

/-- Substitution of a term for a variable. -/
def subst (x : ℕ) (u : Term) : Term → Term
  | var i => if i = x then u else var i
  | zero => zero
  | succ t => succ (subst x u t)
  | plus s t => plus (subst x u s) (subst x u t)
  | times s t => times (subst x u s) (subst x u t)

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
  | plus s t ihs iht => simp [subst, eval, ihs, iht]
  | times s t ihs iht => simp [subst, eval, ihs, iht]

/-- Evaluation only depends on the values of the occurring variables. -/
theorem eval_congr {ρ ρ' : ℕ → ℕ} :
    ∀ {t : Term}, (∀ y ∈ t.vars, ρ y = ρ' y) → t.eval ρ = t.eval ρ' := by
  intro t
  induction t with
  | var i => intro h; exact h i (by simp [vars])
  | zero => intro _; rfl
  | succ t ih => intro h; simp only [eval]; rw [ih h]
  | plus s t ihs iht =>
    intro h
    simp only [eval]
    rw [ihs fun y hy => h y (List.mem_append.mpr (Or.inl hy)),
      iht fun y hy => h y (List.mem_append.mpr (Or.inr hy))]
  | times s t ihs iht =>
    intro h
    simp only [eval]
    rw [ihs fun y hy => h y (List.mem_append.mpr (Or.inl hy)),
      iht fun y hy => h y (List.mem_append.mpr (Or.inr hy))]

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
  -- Phase A: the equational-logic kit for the signature `{0, succ, +, ×}`,
  -- as implication schemas in the style of `succInj` (all contentless).
  | eqRefl {Γ : List Formula} (t : Term) :
      Deriv Γ (eq t t)
  | eqSymm {Γ : List Formula} (s t : Term) :
      Deriv Γ ((eq s t).imp (eq t s))
  | eqTrans {Γ : List Formula} (s t u : Term) :
      Deriv Γ ((eq s t).imp ((eq t u).imp (eq s u)))
  | eqCongSucc {Γ : List Formula} (s t : Term) :
      Deriv Γ ((eq s t).imp (eq (.succ s) (.succ t)))
  | eqCongPlus {Γ : List Formula} (s₁ t₁ s₂ t₂ : Term) :
      Deriv Γ ((eq s₁ t₁).imp ((eq s₂ t₂).imp
        (eq (.plus s₁ s₂) (.plus t₁ t₂))))
  | eqCongTimes {Γ : List Formula} (s₁ t₁ s₂ t₂ : Term) :
      Deriv Γ ((eq s₁ t₁).imp ((eq s₂ t₂).imp
        (eq (.times s₁ s₂) (.times t₁ t₂))))
  -- Phase A: the recursion equations *defining* `+` and `×`, recursing on
  -- the **first** argument (the mirror of the briefed equations, which are
  -- thereby genuine `ind` theorems — see `Arithmetic.lean` and STATUS.md).
  | zeroPlus {Γ : List Formula} (t : Term) :
      Deriv Γ (eq (.plus .zero t) t)
  | succPlus {Γ : List Formula} (s t : Term) :
      Deriv Γ (eq (.plus (.succ s) t) (.succ (.plus s t)))
  | zeroTimes {Γ : List Formula} (t : Term) :
      Deriv Γ (eq (.times .zero t) .zero)
  | succTimes {Γ : List Formula} (s t : Term) :
      Deriv Γ (eq (.times (.succ s) t) (.plus (.times s t) t))

end Realizability
