/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import Realizability.Common.Arithmetic

/-!
# Fibonacci by a paired invariant — the on-ramp example

The most recognizable recursive function there is, extracted from a
constructive proof by the pipeline **unchanged** — no new extraction
machinery, no new realizability clause.  It is the easy case that shows
the mechanism working before anything ordinal-flavored (Goodstein,
Hydra) appears.

## The design

`fib (n+2)` needs *both* `fib (n+1)` and `fib n`, not just the immediate
predecessor — the course-of-values snag.  It is dodged not with strong
induction but with a **paired invariant**, proved by *ordinary* `ind`:

    ∀n. (∃y. fib n = y) ∧ (∃z. fib (n+1) = z)

Step case: given `(y, z)` with `fib n = y` and `fib (n+1) = z`, the pair
`(z, y + z)` witnesses `fib (n+1) = z` and `fib (n+2) = y + z` — the last
directly from `fibSucc` (`fib (n+2) = fib n + fib (n+1)`) rewritten by
the two hypotheses.  No case analysis, no strong induction: the shift
*is* the step, and the extracted realizer is exactly that iteration,
computing `fib` by `+` alone.

## Why this shape, not `∃y ∃z. …`

The paired invariant is written as a **conjunction of two existentials**,
not a nested `∃y ∃z`.  Both are `lvl 0`; but with nested `∃y ∃z (A ∧ B)`
the step's outer `exI` supplies `z`, which is the *inner* binder's
variable, and naive substitution captures it — the Goodstein/Hanoi
renaming dance.  With `(∃y. A) ∧ (∃z. B)` each existential body is
atomic, so the witnesses `(z, y+z)` drop into binder-free formulas and
nothing captures.  `lvl` is unchanged: `∧`/`∃` over equations is `0`,
the outer `∀` makes it `1` — the same level as every other theorem here,
landing at `PureType 2` / `CtQ 2`.
-/

namespace Realizability

/-- The paired invariant's body at a term `n`: `(∃y. fib n = y) ∧
(∃z. fib (n+1) = z)`, with `y = var 3`, `z = var 4`.  Left free in `n`
(here always `var 0`, the `ind` variable) so `ind` can substitute. -/
def fibBody (n : Term) : Formula :=
  Formula.and (.ex 3 (.eq (.fib n) (.var 3)))
    (.ex 4 (.eq (.fib (.succ n)) (.var 4)))

/-- **`∀n. (∃y. fib n = y) ∧ (∃z. fib (n+1) = z)`**, by ordinary `ind` on
`n`.  The witness pair is built by the recursion — base `(0, 1)`, step
`(y, z) ↦ (z, y + z)` — so the extracted realizer computes Fibonacci,
even though `fib` is also a symbol (the symbol is only the spec, and the
step's `fibSucc` justification; the *witness* comes out of `ind`). -/
def fibPairedTheorem : Deriv [] (.all 0 (fibBody (.var 0))) := by
  refine Deriv.ind ?base ?step ?ok
  -- Base `(fib 0 = 0) , (fib 1 = 1)`: the two seed equations `fibZero`,
  -- `fibOne`, each supplied as an `∃`-witness.
  case base =>
    refine Deriv.andI ?ba ?bb
    · exact Deriv.exI .zero Deriv.fibZero (substOK_of_forall (by decide))
    · exact Deriv.exI (.succ .zero) Deriv.fibOne (substOK_of_forall (by decide))
  -- Step: name `y = var 3`, `z = var 4` from the two hypotheses, then
  -- witness `(z, y + z)`.
  case step =>
    refine Deriv.allI (Deriv.impI ?body) (freshIn_nil 0)
    -- Peel `y` (`var 3`) off the first conjunct, `z` (`var 4`) off the
    -- second; contexts grow `[fibA, φ]` then `[fibB, fibA, φ]`.
    refine Deriv.exE (Deriv.andE₁ Deriv.ax) ?d2 (by decide +kernel) (by decide +kernel)
    refine Deriv.exE (Deriv.andE₂ (Deriv.wk Deriv.ax)) ?d3 (by decide +kernel)
      (by decide +kernel)
    refine Deriv.andI ?left ?right
    -- First conjunct `∃y. fib (n+1) = y`: witness `z = var 4`, which is
    -- exactly the hypothesis `fib (n+1) = var 4` at the context head.
    · exact Deriv.exI (.var 4) Deriv.ax (substOK_of_forall (by decide))
    -- Second conjunct `∃z. fib (n+2) = z`: witness `y + z = var 3 + var 4`;
    -- `fibSucc` gives `fib (n+2) = fib n + fib (n+1)`, rewritten by the two
    -- hypotheses `fib n = var 3` and `fib (n+1) = var 4`.
    · refine Deriv.exI (.plus (.var 3) (.var 4)) ?w ?wok
      · exact (Deriv.fibSucc (.var 0)).transE
          (Deriv.congPlusE (Deriv.wk Deriv.ax) Deriv.ax)
      · exact substOK_of_forall (by decide)
  case ok => exact substOK_of_forall (by decide)

/-- The theorem's formula is `lvl 1` — the same level as every headline
theorem in the repository (`∀` costs `+1`, the paired `∃ ∧ ∃` over
equations costs nothing), so its realizers live in `PureType 2`. -/
theorem fib_lvl : lvl (.all 0 (fibBody (.var 0))) = 1 := rfl

end Realizability
