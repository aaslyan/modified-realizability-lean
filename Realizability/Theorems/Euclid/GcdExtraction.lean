/-
# Phase E2 (Euclid), the extracted gcd

`gcdTheorem` is a closed derivation of

    ∀a ∀b. ∃g. g ∣ a ∧ g ∣ b ∧ ∀d. (d ∣ a → d ∣ b → d ∣ g)

so modified realizability turns it into a program: the realizer of the
existential carries its witness, and the witness *is* a greatest common
divisor.  The three certifications of every extraction phase — soundness
at the theorem, continuity, and a class in `CtQ 2` — plus the witness
function itself and the value-level facts read off it.

## Why there is no `#eval` here

Goodstein (`#eval` at ambient 12) and Hanoi (26) run; this realizer sits
at ambient **41** — the gcd derivation is the deepest in the repository —
and every `pairPT`/`up`/`down` at that level is a functional nested 40
deep, so even `gcdWitness 0 0` does not return.  The realizer is a
certified program (soundness holds at *every* input, below), but running
it is walled by the level, exactly as `hanoiSolution 5`'s encoding and the
Hydra code-2 battle are walled elsewhere.  The value-level facts are
therefore read off the *realized specification*, not off evaluation.
-/
import Realizability.Theorems.Euclid.GcdTheorem
import Realizability.Core.CollapseDemo

namespace Realizability

open ContinuousFunctionals

/-! **The statement, spelled out** — checked at every build so what is
proved cannot drift behind a definition: `⊢ ∀a ∀b. ∃g. g ∣ a ∧ g ∣ b ∧
∀d. (d ∣ a → d ∣ b → d ∣ g)`, with each `∣` the fragment's `∃`-over-`×`. -/
#check (gcdTheorem :
  Deriv [] (Formula.all 6 (Formula.all 7 (Formula.ex 10
    (gcdSpecT (Term.var 6) (Term.var 7) (Term.var 10))))))

/- The bound above which the extracted family realizes the theorem.
(`maxRecDepth` raised: the gcd derivation is the repository's deepest, so
computing its bound by `rfl` recurses further than the default allows.) -/
set_option maxRecDepth 4000 in
theorem gcd_derivBound : derivBound gcdTheorem = 41 := rfl

/-- **Soundness at the gcd theorem**, at every ambient from 41 up. -/
theorem gcd_realized' (ρ : ℕ → ℕ) {n : ℕ} (hn : 41 ≤ n) :
    MR ρ (.all 6 (.all 7 (.ex 10 (gcdSpecT (.var 6) (.var 7) (.var 10))))) n
      (extract gcdTheorem ρ [] n) :=
  soundness gcdTheorem ρ [] trivial n (by rw [gcd_derivBound]; exact hn)

/-- **The extracted gcd function.**  Apply the realizer to `a` and `b`,
then read the witness component of the existential.  Ambient 41 is the
derivation's own bound, so this is the realizer at the level where it is
certified. -/
def gcdWitness (a b : ℕ) : ℕ :=
  fstPT (app₁ (app₁ (extract gcdTheorem (fun _ => 0) [] 41) (natPT 41 a)) (natPT 40 b))
    (defaultPT 39)

/-- **The extracted number is a common divisor of `a` and `b`** — read
off the first two conjuncts of the realized specification, at every
input, from `soundness` (not from computation, so it holds where
evaluation cannot reach).  That it is the *greatest* common divisor is the
third conjunct of `gcd_realized'`; it, and the witnessing quotients, are
carried by the same realizer. -/
theorem gcdWitness_dvd (a b : ℕ) : gcdWitness a b ∣ a ∧ gcdWitness a b ∣ b := by
  have h := gcd_realized' (fun _ => 0) (n := 41) (le_refl 41)
  exact ⟨⟨_, (h a b).1⟩, ⟨_, (h a b).2.1⟩⟩

/-- Generic continuity applies with no modification: `extract_continuous`
covers the whole subtractive-Euclid recursion with no per-derivation work. -/
theorem gcd_extract_continuous' (ρ : ℕ → ℕ) :
    Continuous2 (extract gcdTheorem ρ [] 1) :=
  extract_continuous gcdTheorem ρ

/-- The theorem's program as an element of `CtQ 2` — the class of its
extracted type-2 realizer in the extensional collapse. -/
noncomputable def gcdRealizesCtQ (ρ : ℕ → ℕ) : CtQ 2 :=
  RealizesCtQ gcdTheorem ρ

#print axioms gcd_realized'
#print axioms gcdWitness_dvd
#print axioms gcd_extract_continuous'

end Realizability
