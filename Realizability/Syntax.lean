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

Since the Phase-B extension the signature further includes `pred`,
`exp`, hereditary base change `bump`, and the Goodstein sequence
`good`, with their recursion-equation schemas, the numeral graph of
`bump` (see the rule comment and STATUS.md for why `bump` alone enters
by its graph), and the matching congruence schemas.  The hereditary
base-`k` *representation* itself lives in `Goodstein.lean` as a term of
this very syntax in one distinguished base variable.

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
import Realizability.Epsilon0

namespace Realizability

/-! ## The value-level Goodstein functions (Phase B)

The semantics of the Phase-B function symbols `bump` and `good`, as
plain `ℕ`-functions defined *before* `Term` so `Term.eval` can consume
them.  All recursions are **fuel-structural** (fuel `= n` is adequate,
`Goodstein.lean` proves it) rather than well-founded: `WellFounded.fix`
does not reduce in the kernel, and the certifying derivations of
`Goodstein.lean` need concrete Goodstein values to compute by
`rfl`/`decide`.  For the same reason the base-`b` logarithm is a local
fueled definition rather than Mathlib's well-founded `Nat.log`. -/

/-- Fueled base-`b` logarithm: the number of times `b` divides into `n`
(zero when `b ≤ 1` or `n < b`).  Structural in the fuel. -/
def hlogAux (b : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, n => if 1 < b ∧ b ≤ n then hlogAux b fuel (n / b) + 1 else 0

/-- The base-`b` logarithm, self-fueled: `hlog b n` is the largest `e`
with `b ^ e ≤ n` (for `1 < b ≤ n`; zero in the degenerate cases) —
`Goodstein.lean` proves the two facts used (`hlog_lt`,
`pow_hlog_le`). -/
def hlog (b n : ℕ) : ℕ :=
  hlogAux b n n

/-- **Hereditary base change, value level** (fueled): `bumpNAux k fuel n`
peels the leading base-`k` digit `n = k^e·c + r` (`e = hlog k n`,
`c = n / k^e`, `r = n % k^e`) and rewrites it at base `k + 1` with the
exponent *itself* hereditarily rewritten:
`(k+1)^(bump e)·c + bump r`.  Corresponds to
`WilliamAngus/Goodstein`'s `(HBase.f k · (k+1)).eval ∘ HBase.ofNat k`
(the structural base-replacement `f` on the `ofNat` representation);
checked concretely: `bumpN 2 4 = 3 ^ 3 ^ 3 ^ 0 = 27`, both here and
there (`4 = 2^2^2^0`).  Degenerate bases are the identity
(`bumpN 0 n = bumpN 1 n = n`), so no `2 ≤ k` side condition is ever
needed for soundness. -/
def bumpNAux (k : ℕ) : ℕ → ℕ → ℕ
  | _, 0 => 0
  | 0, _ + 1 => 0
  | fuel + 1, n + 1 =>
      (k + 1) ^ bumpNAux k fuel (hlog k (n + 1)) * ((n + 1) / k ^ hlog k (n + 1))
        + bumpNAux k fuel ((n + 1) % k ^ hlog k (n + 1))

/-- Hereditary base change at the adequate fuel (`Goodstein.lean`,
`hrep_eval_bump`, connects it to the syntactic representation read at
base `k + 1`). -/
def bumpN (k n : ℕ) : ℕ :=
  bumpNAux k n n

/-- **The Goodstein sequence, value level**: `goodN m 0 = m`, and one
step bumps the base `s + 2` hereditarily and subtracts one.  This is
`WilliamAngus/Goodstein`'s `goodsteinSequence start h n i` at
`start = 2`: their step `i → i + 1` applies the base-change `G` at base
`start + i = 2 + i`, exactly this `bumpN (s + 2)` at `i = s` (indexing
convention checked against their `g`/`G`; values checked:
`goodN 4 = 4, 26, 41, 60, …`, `goodN 3 = 3, 3, 3, 2, 1, 0, 0, …`). -/
def goodN (m : ℕ) : ℕ → ℕ
  | 0 => m
  | s + 1 => bumpN (s + 2) (goodN m s) - 1

/-- Terms: variables (named by numbers), zero, successor; since the
Phase-A extension, sum and product; since the Phase-B extension,
predecessor, exponentiation, hereditary base change (`bump`), and the
Goodstein sequence (`good`). -/
inductive Term : Type where
  | var : ℕ → Term
  | zero : Term
  | succ : Term → Term
  | plus : Term → Term → Term
  | times : Term → Term → Term
  | pred : Term → Term
  | exp : Term → Term → Term
  | bump : Term → Term → Term
  | good : Term → Term → Term
  | prec : Term → Term → Term
deriving DecidableEq, Repr

namespace Term

/-- Evaluation in an environment.  The Phase-B symbols evaluate by the
value-level functions above (`pred` is truncated predecessor, `exp` is
`^`, `bump` is `bumpN`, `good` is `goodN`). -/
def eval (ρ : ℕ → ℕ) : Term → ℕ
  | var i => ρ i
  | zero => 0
  | succ t => t.eval ρ + 1
  | plus s t => s.eval ρ + t.eval ρ
  | times s t => s.eval ρ * t.eval ρ
  | pred t => t.eval ρ - 1
  | exp s t => s.eval ρ ^ t.eval ρ
  | bump s t => bumpN (s.eval ρ) (t.eval ρ)
  | good s t => goodN (s.eval ρ) (t.eval ρ)
  | prec s t => oltN (s.eval ρ) (t.eval ρ)

/-- The variables occurring in a term. -/
def vars : Term → List ℕ
  | var i => [i]
  | zero => []
  | succ t => t.vars
  | plus s t => s.vars ++ t.vars
  | times s t => s.vars ++ t.vars
  | pred t => t.vars
  | exp s t => s.vars ++ t.vars
  | bump s t => s.vars ++ t.vars
  | good s t => s.vars ++ t.vars
  | prec s t => s.vars ++ t.vars

/-- Substitution of a term for a variable. -/
def subst (x : ℕ) (u : Term) : Term → Term
  | var i => if i = x then u else var i
  | zero => zero
  | succ t => succ (subst x u t)
  | plus s t => plus (subst x u s) (subst x u t)
  | times s t => times (subst x u s) (subst x u t)
  | pred t => pred (subst x u t)
  | exp s t => exp (subst x u s) (subst x u t)
  | bump s t => bump (subst x u s) (subst x u t)
  | good s t => good (subst x u s) (subst x u t)
  | prec s t => prec (subst x u s) (subst x u t)

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
  | pred t ih => simp [subst, eval, ih]
  | exp s t ihs iht => simp [subst, eval, ihs, iht]
  | bump s t ihs iht => simp [subst, eval, ihs, iht]
  | good s t ihs iht => simp [subst, eval, ihs, iht]
  | prec s t ihs iht => simp [subst, eval, ihs, iht]

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
  | pred t ih => intro h; simp only [eval]; rw [ih h]
  | exp s t ihs iht =>
    intro h
    simp only [eval]
    rw [ihs fun y hy => h y (List.mem_append.mpr (Or.inl hy)),
      iht fun y hy => h y (List.mem_append.mpr (Or.inr hy))]
  | bump s t ihs iht =>
    intro h
    simp only [eval]
    rw [ihs fun y hy => h y (List.mem_append.mpr (Or.inl hy)),
      iht fun y hy => h y (List.mem_append.mpr (Or.inr hy))]
  | good s t ihs iht =>
    intro h
    simp only [eval]
    rw [ihs fun y hy => h y (List.mem_append.mpr (Or.inl hy)),
      iht fun y hy => h y (List.mem_append.mpr (Or.inr hy))]
  | prec s t ihs iht =>
    intro h
    simp only [eval]
    rw [ihs fun y hy => h y (List.mem_append.mpr (Or.inl hy)),
      iht fun y hy => h y (List.mem_append.mpr (Or.inr hy))]

end Term

/-- The numeral for `n`: an `n`-fold `succ` of `zero`. -/
def numeral : ℕ → Term
  | 0 => .zero
  | n + 1 => .succ (numeral n)

/-- Numerals evaluate to their number, in every environment. -/
@[simp] theorem numeral_eval (ρ : ℕ → ℕ) : ∀ n : ℕ, (numeral n).eval ρ = n
  | 0 => rfl
  | n + 1 => by simp only [numeral, Term.eval, numeral_eval ρ n]

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
  -- Phase B: recursion equations for predecessor and exponentiation
  -- (honest first-order schemas, like the Phase-A group) …
  | predZero {Γ : List Formula} :
      Deriv Γ (eq (.pred .zero) .zero)
  | predSucc {Γ : List Formula} (s : Term) :
      Deriv Γ (eq (.pred (.succ s)) s)
  | expZero {Γ : List Formula} (s : Term) :
      Deriv Γ (eq (.exp s .zero) (.succ .zero))
  | expSucc {Γ : List Formula} (s t : Term) :
      Deriv Γ (eq (.exp s (.succ t)) (.times (.exp s t) s))
  -- … the two axioms for hereditary base change: absorption at zero
  -- (a term schema) and the numeral graph (an `ℕ`-parameterized schema —
  -- `bump`'s course-of-values recursion through the hereditary exponent
  -- structure is not a first-order equation schema; the semantic
  -- characterization "`bump` is the representation read at the next
  -- base" is *derived*, per numeral instance, in `Goodstein.lean`) …
  | bumpZero {Γ : List Formula} (s : Term) :
      Deriv Γ (eq (.bump s .zero) .zero)
  | bumpNum {Γ : List Formula} (k n : ℕ) :
      Deriv Γ (eq (.bump (numeral k) (numeral n)) (numeral (bumpN k n)))
  -- … the Goodstein sequence's own defining recursion (genuine
  -- first-order schemas again: one step bumps the base `t + 2` and
  -- takes the predecessor) …
  | goodZero {Γ : List Formula} (s : Term) :
      Deriv Γ (eq (.good s .zero) s)
  | goodSucc {Γ : List Formula} (s t : Term) :
      Deriv Γ (eq (.good s (.succ t))
        (.pred (.bump (.succ (.succ t)) (.good s t))))
  -- … and the congruence schemas completing the equational-logic kit
  -- for the extended signature.
  | eqCongPred {Γ : List Formula} (s t : Term) :
      Deriv Γ ((eq s t).imp (eq (.pred s) (.pred t)))
  | eqCongExp {Γ : List Formula} (s₁ t₁ s₂ t₂ : Term) :
      Deriv Γ ((eq s₁ t₁).imp ((eq s₂ t₂).imp
        (eq (.exp s₁ s₂) (.exp t₁ t₂))))
  | eqCongBump {Γ : List Formula} (s₁ t₁ s₂ t₂ : Term) :
      Deriv Γ ((eq s₁ t₁).imp ((eq s₂ t₂).imp
        (eq (.bump s₁ s₂) (.bump t₁ t₂))))
  | eqCongGood {Γ : List Formula} (s₁ t₁ s₂ t₂ : Term) :
      Deriv Γ ((eq s₁ t₁).imp ((eq s₂ t₂).imp
        (eq (.good s₁ s₂) (.good t₁ t₂))))
  -- Phase C: **transfinite induction along the ordinal notations below
  -- `ε₀`** (`tiEps0`), the one rule of the fragment that is not a
  -- consequence of its own resources — this is the content of
  -- Gentzen/Kirby–Paris.  Variables range over `ℕ`, read as notation
  -- *codes* (`Epsilon0.lean`), and `y ≺ x` is the atomic formula
  -- `prec y x = 1`, so the rule stays inside the fragment's
  -- equations-only formula language.  Progressiveness of `φ` yields
  -- `∀x φ(x)`; its realizer is the recursor `tiRecC`, whose defining
  -- recursion runs along `≺` rather than along `succ` (contrast `ind`).
  --
  -- Side conditions, all three needed by the soundness proof: the two
  -- variables are distinct (so that `x`'s value survives the inner
  -- binder), the substituted variable does not get captured, and `y` is
  -- not free in `φ` (so that `φ(y)` under the inner environment is
  -- `φ` under `x ↦ y`'s value).
  | tiEps0 {Γ : List Formula} {x y : ℕ} {φ : Formula} :
      Deriv Γ (Formula.all x
        ((Formula.all y ((eq (.prec (.var y) (.var x)) (.succ .zero)).imp
          (φ.subst x (.var y)))).imp φ)) →
      x ≠ y →
      Formula.SubstOK (.var y) φ →
      ¬ φ.FreeIn y →
      Deriv Γ (.all x φ)
  -- Phase C: the numeral graph of the order (`prec` is a *decidable*
  -- comparison of codes, so the fragment computes it on numerals — the
  -- same device as Phase B's `bumpNum`, and for the same reason: the
  -- recursion is course-of-values through the notation structure, not a
  -- first-order equation schema) …
  | precNum {Γ : List Formula} (a b : ℕ) :
      Deriv Γ (eq (.prec (numeral a) (numeral b)) (numeral (oltN a b)))
  -- … and its congruence schema, completing the equational kit.
  | eqCongPrec {Γ : List Formula} (s₁ t₁ s₂ t₂ : Term) :
      Deriv Γ ((eq s₁ t₁).imp ((eq s₂ t₂).imp
        (eq (.prec s₁ s₂) (.prec t₁ t₂))))

end Realizability
