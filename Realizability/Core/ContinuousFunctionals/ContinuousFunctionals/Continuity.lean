/-
# Continuity for type-2 functionals

A functional `F : (ℕ → ℕ) → ℕ` is continuous — with respect to the product
topology on Baire space `ℕ → ℕ` and the discrete topology on `ℕ` — exactly
when its value at any point `α` depends only on a finite initial segment of
`α`.  This file states that condition in the elementary "modulus at a point"
form `Continuous2`, plus the equivalent phrasing through initial segments
that is convenient against `IsAssociate`.

Deliberately *not* here: any import of Mathlib's topology library.  The
product-topology formulation is a definitional unwinding away, and keeping
the project at the level of finite information avoids a dependency the
mathematics does not need.
-/
import ContinuousFunctionals.Sequences

namespace ContinuousFunctionals

/-- **Continuity for type-2 functionals** (pointwise modulus form): at every
point `α` there is a stage `n` such that the value `F α` depends only on
`α 0, …, α (n-1)` — any `β` agreeing with `α` below `n` gets the same value.

This is the standard "any finite piece of information about the output is
determined by a finite piece of information about the input" condition of
Kleene (1959) and Kreisel (1959) specialized to type 2, where the output is
a single natural number; see Longley–Normann 2015, Ch. 8, and Longley,
*Notions of computability at higher types I*, §3.3.1.  It is precisely
continuity of `F` for the product topology on `ℕ → ℕ` (basic open sets =
sets of sequences with a prescribed initial segment) and the discrete
topology on `ℕ`. -/
def Continuous2 (F : (ℕ → ℕ) → ℕ) : Prop :=
  ∀ α : ℕ → ℕ, ∃ n : ℕ, ∀ β : ℕ → ℕ, (∀ i < n, α i = β i) → F α = F β

/-- Continuity rephrased through initial segments: `F` is continuous iff at
every `α` some initial segment `initSeg α n` already forces the value.  Same
content as `Continuous2`, in the vocabulary an associate consumes. -/
theorem continuous2_iff_initSeg {F : (ℕ → ℕ) → ℕ} :
    Continuous2 F ↔ ∀ α : ℕ → ℕ, ∃ n : ℕ, ∀ β : ℕ → ℕ,
      initSeg β n = initSeg α n → F β = F α := by
  constructor
  · intro h α
    obtain ⟨n, hn⟩ := h α
    exact ⟨n, fun β hβ =>
      (hn β (fun i hi => (initSeg_eq_iff.mp hβ i hi).symm)).symm⟩
  · intro h α
    obtain ⟨n, hn⟩ := h α
    exact ⟨n, fun β hβ =>
      (hn β (initSeg_eq_iff.mpr (fun i hi => (hβ i hi).symm))).symm⟩

end ContinuousFunctionals
