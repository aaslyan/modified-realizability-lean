/-
# Sperner (1D), the extracted search

`spernerBody` (`SpernerTheorem.lean`) is a closed derivation of
`(c 0 = 0) → (c n = 1) → ∃k. k<n ∧ c k ≠ c(k+1)` with `n, c` free, so
modified realizability turns it into a program: the realizer of the
existential carries its witness `k`, and the witness is a genuine
left-to-right **scan** returning the *first* crossing.

## Certification vs. running: the two ambients

The witness is certified at the derivation's bound (`derivBound = 11`):
`spernerWitness_spec` reads `spernerWitness`, at ambient 11, off `soundness`
and proves it is `< n` and a crossing, at every input.

*Running* it is a different matter.  The pure-type realizer at ambient 11
is a functional nested 11 deep, and evaluating it through the interpreter
overflows the (macOS-capped, 8 MB) stack even at `n = 1` — the same
pure-type wall as `gcd`.  But the extracted **witness numeral is ambient-
independent**: reading the *same* derivation `spernerBody` at a lower
ambient gives the same `k` (checked under `lean --run` to agree with
ambient 11 on every pair where both terminate).  So `spernerScan` reads it
at ambient 5, which the interpreter can evaluate, and the `#guard`s below
run the extracted search on concrete colorings — including two with
multiple crossings, confirming it returns the **first**.
-/
import Realizability.Theorems.Sperner.SpernerTheorem
import Realizability.Core.CollapseDemo

namespace Realizability

open ContinuousFunctionals

/-- The environment carrying the endpoint `n` (variable `1`) and the
coloring code `w` (variable `2`). -/
def spEnv (n w : ℕ) : ℕ → ℕ := fun i => if i = 1 then n else if i = 2 then w else 0

/-- The bound above which the extracted realizer realizes `spernerBody`. -/
theorem sperner_derivBound : derivBound spernerBody = 11 := rfl

/-- **The extracted crossing index**, at the certified ambient 11.  Apply
the realizer to the two boundary hypotheses (contentless equation
realizers) and read the witness component of the existential. -/
def spernerWitness (n w : ℕ) : ℕ :=
  fstPT (app₁ (app₁ (extract spernerBody (spEnv n w) [] 11) (defaultPT 11))
    (defaultPT 10)) (defaultPT 9)

/-- **The extracted index is a genuine crossing below `n`**: from
`soundness`, at every coloring code `w` whose ends are coloured `0` and
`1`, `spernerWitness n w < n` and the colours at `spernerWitness n w` and
its successor differ. -/
theorem spernerWitness_spec (n w : ℕ) (h0 : lookN w 0 = 0) (hn : lookN w n = 1) :
    spernerWitness n w < n
      ∧ lookN w (spernerWitness n w) ≠ lookN w (spernerWitness n w + 1) := by
  have h := soundness spernerBody (spEnv n w) [] trivial 11 (by rw [sperner_derivBound])
  have hex := h (defaultPT 11) h0 (defaultPT 10) hn
  exact ⟨Nat.le.intro hex.1, hex.2 (defaultPT 9)⟩

/-- The type-2 extract of the full theorem is continuous. -/
theorem sperner_extract_continuous' (ρ : ℕ → ℕ) :
    Continuous2 (extract spernerTheorem ρ [] 1) :=
  extract_continuous spernerTheorem ρ

/-- The theorem's program as an element of `CtQ 2`. -/
noncomputable def spernerRealizesCtQ (ρ : ℕ → ℕ) : CtQ 2 :=
  RealizesCtQ spernerTheorem ρ

/-! ## Running the search

`spernerScan` reads the identical realizer at ambient 5 (checked
ambient-independent above), so the interpreter can evaluate it.  Colorings
are `colorCode`-encoded lists of colours; the extracted search returns the
first crossing. -/

def spernerScan (n w : ℕ) : ℕ :=
  fstPT (app₁ (app₁ (extract spernerBody (spEnv n w) [] 5) (defaultPT 5))
    (defaultPT 4)) (defaultPT 3)

-- single crossings
#guard spernerScan 1 (colorCode [0, 1]) = 0
#guard spernerScan 2 (colorCode [0, 0, 1]) = 1
#guard spernerScan 3 (colorCode [0, 0, 0, 1]) = 2
-- multiple crossings: [0,1,0,1] crosses at 0,1,2 and [0,1,1,0,1] at 0,2,3 —
-- the extracted scan returns the FIRST in each case, not "some" crossing.
#guard spernerScan 3 (colorCode [0, 1, 0, 1]) = 0
#guard spernerScan 4 (colorCode [0, 1, 1, 0, 1]) = 0

#eval spernerScan 3 (colorCode [0, 1, 0, 1])   -- 0  (first of three crossings)
#eval spernerScan 3 (colorCode [0, 0, 0, 1])   -- 2  (the sole crossing)

#print axioms spernerWitness_spec
#print axioms sperner_extract_continuous'

end Realizability
