/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import Realizability.Common.Exists

/-!
# Phase E3: the Tower of Hanoi, inside the fragment

    ⊢ ∀n ∀f ∀t ∀v. ∃k. Solves(n, f, t, v, k) ∧ MoveCount k = 2^n − 1

as a closed derivation, by **ordinary induction** — `ind`, the Phase-2
rule — with no `tiEps0` and no ordinal anywhere.  That is the point of
the phase: Hanoi is an ordinary theorem of PA, so it exercises the
pipeline on infrastructure strictly simpler than Goodstein's or Hydra's,
while having a recursion that *branches* where theirs were linear.

## Correctness and optimality together

The induction carries both conjuncts at once — the decision the brief
asked to be recorded.  Separately would mean proving existence first and
then re-running the same induction to count the witness it produced,
which needs that witness named, i.e. a second existential elimination
inside a second induction.  Carried together, the step case gets both
facts about each sub-solution from the same `∃`-elimination, and costs
one `andI`.

The count is carried subtraction-free, as

    succ (MoveCount k) = 2^n

because the fragment has `pred` but no order relation, so `2^n − 1`
cannot be manipulated directly.  The brief's form is recovered at the end
by `predSucc`: see `hanoiTheorem`.

## The one place naive substitution bites — differently from D2

Hanoi's recursion **permutes its pegs**: solving `f → t via v` needs
`f → v via t` and `v → t via f`.  So the induction hypothesis
`∀f ∀t ∀v. …` must be instantiated at a permutation of the very
variables the goal has just bound — and with naive substitution *every*
such instantiation captures, because to instantiate the second binder at
the third variable, the third is still bound.  Both permutations the
recursion needs hit it, and no ordering of the binders avoids it.

The fix is cheaper than D2's naming trick: **α-rename the induction
hypothesis first**.  Instantiating `∀f∀t∀v` at three *fresh* variables is
capture-free, and re-generalizing them gives the same statement over
binders disjoint from the goal's; instantiating *that* at the permutation
is capture-free in turn.  `ihRenamed` is those six lines, and the device
is reusable for any recursion that permutes its parameters.

A second, smaller instance of the same issue: both sub-solutions must be
in scope at once, so the second existential's witness variable is renamed
from `5` to `9` before elimination (`ihSecond`).
-/

namespace Realizability

open ContinuousFunctionals

/-! ## The formulas

Variable convention: `1` is the disk count `n`, `2`/`3`/`4` the pegs
`from`/`to`/`via`, `5` the existential witness, `6`/`7`/`8` the fresh
variables the induction hypothesis is renamed through, `9` the second
witness (and the bound variable of the doubling lemma, which never meets
it). -/

/-- The numeral `2`, as a term. -/
abbrev twoT : Term := .succ (.succ .zero)

/-- The `∃`-body: `k` (variable `w`) solves the `n`-disk problem moving
`a → b` via `c`, and its move count is `2^n − 1` in subtraction-free
form. -/
abbrev hanoiBodyK (a b c w : ℕ) : Formula :=
  (Formula.eq (.solves (.var 1) (.var a) (.var b) (.var c) (.var w))
    (.succ .zero)).and
    (Formula.eq (.succ (.mvcount (.var w))) (.exp twoT (.var 1)))

/-- The induction formula: for all pegs, a solution exists, of the right
length. -/
abbrev hanoiSpec : Formula :=
  .all 2 (.all 3 (.all 4 (.ex 5 (hanoiBodyK 2 3 4 5))))

/-! ## The arithmetic the step needs: `2^x + 2^x = 2^(x+1)`

No induction of its own — `expSucc` plus Phase A's `×` theorems (which
are themselves `ind` theorems, in `Arithmetic.lean`). -/

/-- **`∀x. 2^x + 2^x = 2^(succ x)`**, via `y × 2 = y + y`. -/
def expDoubleDeriv :
    Deriv [] (.all 9 (.eq (.plus (.exp twoT (.var 9)) (.exp twoT (.var 9)))
      (.exp twoT (.succ (.var 9))))) := by
  refine Deriv.allI ?_ (freshIn_nil 9)
  have d1 : Deriv [] (Formula.eq (.times (.exp twoT (.var 9)) twoT)
      (.plus (.times (.exp twoT (.var 9)) (.succ .zero)) (.exp twoT (.var 9)))) :=
    Deriv.allE (.succ .zero)
      (Deriv.allE (.exp twoT (.var 9)) timesSuccDeriv
        (substOK_of_forall (by decide)))
      (substOK_of_forall (by decide))
  have d2 : Deriv [] (Formula.eq (.times (.exp twoT (.var 9)) (.succ .zero))
      (.plus (.times (.exp twoT (.var 9)) .zero) (.exp twoT (.var 9)))) :=
    Deriv.allE .zero
      (Deriv.allE (.exp twoT (.var 9)) timesSuccDeriv
        (substOK_of_forall (by decide)))
      (substOK_of_forall (by decide))
  have d3 : Deriv [] (Formula.eq (.times (.exp twoT (.var 9)) .zero) .zero) :=
    Deriv.allE (.exp twoT (.var 9)) timesZeroDeriv
      (substOK_of_forall (by decide))
  have d6 : Deriv [] (Formula.eq (.times (.exp twoT (.var 9)) (.succ .zero))
      (.exp twoT (.var 9))) :=
    d2.transE ((Deriv.congPlusE d3 (.eqRefl _)).transE
      (Deriv.zeroPlus (.exp twoT (.var 9))))
  have d8 : Deriv [] (Formula.eq (.times (.exp twoT (.var 9)) twoT)
      (.plus (.exp twoT (.var 9)) (.exp twoT (.var 9)))) :=
    d1.transE (Deriv.congPlusE d6 (.eqRefl _))
  exact Deriv.symmE ((Deriv.expSucc twoT (.var 9)).transE d8)

/-! ## The base case -/

/-- `φ(0)`: the empty sequence solves the 0-disk problem, and
`succ (MoveCount 0) = 1 = 2^0`. -/
def hanoiBase : Deriv [] (hanoiSpec.subst 1 .zero) := by
  refine Deriv.allI (Deriv.allI (Deriv.allI ?_ (by decide +kernel))
    (by decide +kernel)) (by decide +kernel)
  refine Deriv.exI .zero (Deriv.andI (.solvesZero (.var 2) (.var 3) (.var 4)) ?_)
    (by decide +kernel)
  exact (Deriv.congSuccE Deriv.mvcountNil).transE
    (Deriv.symmE (Deriv.expZero twoT))

/-! ## The step case -/

/-- **α-renaming the induction hypothesis.**  Instantiating `∀2∀3∀4` at
the fresh `6, 7, 8` is capture-free, and re-generalizing gives the same
statement over binders disjoint from the goal's — which is what makes the
*permuted* instantiations below capture-free in turn. -/
def ihRenamed : Deriv [hanoiSpec]
    (.all 6 (.all 7 (.all 8 (.ex 5 (hanoiBodyK 6 7 8 5))))) := by
  refine Deriv.allI (Deriv.allI (Deriv.allI ?_ (by decide +kernel))
    (by decide +kernel)) (by decide +kernel)
  have h0 : Deriv [hanoiSpec] hanoiSpec := Deriv.ax
  have h1 : Deriv [hanoiSpec] (.all 3 (.all 4 (.ex 5 (hanoiBodyK 6 3 4 5)))) :=
    Deriv.allE (.var 6) h0 (by decide +kernel)
  have h2 : Deriv [hanoiSpec] (.all 4 (.ex 5 (hanoiBodyK 6 7 4 5))) :=
    Deriv.allE (.var 7) h1 (by decide +kernel)
  exact Deriv.allE (.var 8) h2 (by decide +kernel)

/-- The hypothesis at the first sub-problem: `f → v` via `t`. -/
def ihFirst : Deriv [hanoiSpec] (.ex 5 (hanoiBodyK 2 4 3 5)) := by
  have h1 : Deriv [hanoiSpec] (.all 7 (.all 8 (.ex 5 (hanoiBodyK 2 7 8 5)))) :=
    Deriv.allE (.var 2) ihRenamed (by decide +kernel)
  have h2 : Deriv [hanoiSpec] (.all 8 (.ex 5 (hanoiBodyK 2 4 8 5))) :=
    Deriv.allE (.var 4) h1 (by decide +kernel)
  exact Deriv.allE (.var 3) h2 (by decide +kernel)

/-- The hypothesis at the second sub-problem: `v → t` via `f`, with its
witness variable renamed to `9` so that both witnesses can be in scope at
once. -/
def ihSecond : Deriv [hanoiSpec] (.ex 9 (hanoiBodyK 4 3 2 9)) := by
  have h1 : Deriv [hanoiSpec] (.all 7 (.all 8 (.ex 5 (hanoiBodyK 4 7 8 5)))) :=
    Deriv.allE (.var 4) ihRenamed (by decide +kernel)
  have h2 : Deriv [hanoiSpec] (.all 8 (.ex 5 (hanoiBodyK 4 3 8 5))) :=
    Deriv.allE (.var 3) h1 (by decide +kernel)
  have h3 : Deriv [hanoiSpec] (.ex 5 (hanoiBodyK 4 3 2 5)) :=
    Deriv.allE (.var 2) h2 (by decide +kernel)
  exact Deriv.exE h3
    (Deriv.exI (.var 5) Deriv.ax (by decide +kernel))
    (by decide +kernel) (by decide +kernel)

/-- The witness for `n + 1`: the first sub-solution, the big move
`f → t`, then the second sub-solution.  A move is the term `f × 3 + t` —
no symbol of its own. -/
abbrev hanoiWitness : Term :=
  .happ (.var 5) (.hcons (.plus (.times (.var 2) (numeral 3)) (.var 3)) (.var 9))

/-- The context inside the two existential eliminations. -/
abbrev stepCtx : List Formula :=
  [hanoiBodyK 4 3 2 9, hanoiBodyK 2 4 3 5, hanoiSpec]

/-- **The step's core**: with both sub-solutions in scope, the joined
sequence solves one disk more and has the right length.  The first
conjunct is `solvesSucc` applied to the two hypotheses; the second is
`mvcountApp` followed by the doubling lemma. -/
def stepCore : Deriv stepCtx
    ((Formula.eq (.solves (.succ (.var 1)) (.var 2) (.var 3) (.var 4)
        hanoiWitness) (.succ .zero)).and
      (Formula.eq (.succ (.mvcount hanoiWitness))
        (.exp twoT (.succ (.var 1))))) := by
  have hyp₂ : Deriv stepCtx (hanoiBodyK 4 3 2 9) := Deriv.ax
  have hyp₁ : Deriv stepCtx (hanoiBodyK 2 4 3 5) := Deriv.wk Deriv.ax
  refine Deriv.andI ?_ ?_
  · exact Deriv.impE
      (Deriv.impE
        (Deriv.solvesSucc (.var 1) (.var 2) (.var 3) (.var 4) (.var 5) (.var 9))
        (Deriv.andE₁ hyp₁))
      (Deriv.andE₁ hyp₂)
  · have hdouble : Deriv stepCtx
        (Formula.eq (.plus (.exp twoT (.var 1)) (.exp twoT (.var 1)))
          (.exp twoT (.succ (.var 1)))) :=
      Deriv.allE (.var 1) (Deriv.wk (Deriv.wk (Deriv.wk expDoubleDeriv)))
        (substOK_of_forall (by decide))
    exact (Deriv.mvcountApp (.var 5)
        (.plus (.times (.var 2) (numeral 3)) (.var 3)) (.var 9)).transE
      ((Deriv.congPlusE (Deriv.andE₂ hyp₁) (Deriv.andE₂ hyp₂)).transE hdouble)

/-- **Progressiveness**: `∀n. φ(n) → φ(n+1)`, the premise of `ind`. -/
def hanoiStep :
    Deriv [] (.all 1 (hanoiSpec.imp (hanoiSpec.subst 1 (.succ (.var 1))))) := by
  refine Deriv.allI (Deriv.impI ?_) (freshIn_nil 1)
  refine Deriv.allI (Deriv.allI (Deriv.allI ?_ (by decide +kernel))
    (by decide +kernel)) (by decide +kernel)
  refine Deriv.exE ihFirst ?_ (by decide +kernel) (by decide +kernel)
  refine Deriv.exE (Deriv.wk ihSecond) ?_ (by decide +kernel) (by decide +kernel)
  exact Deriv.exI hanoiWitness stepCore (by decide +kernel)

/-! ## The theorem -/

/-- **The Tower of Hanoi, in subtraction-free form**:
`⊢ ∀n ∀f ∀t ∀v ∃k. Solves(n,f,t,v,k) ∧ succ (MoveCount k) = 2^n`. -/
def hanoiSolvable : Deriv [] (.all 1 hanoiSpec) :=
  .ind hanoiBase hanoiStep (substOK_of_forall (by decide))

/-- The specification in the brief's own form, with the count as
`2^n − 1`: from `succ (MoveCount k) = 2^n`, `predSucc` gives
`MoveCount k = pred (2^n)`. -/
abbrev hanoiBodyPred : Formula :=
  (Formula.eq (.solves (.var 1) (.var 2) (.var 3) (.var 4) (.var 5))
    (.succ .zero)).and
    (Formula.eq (.mvcount (.var 5)) (.pred (.exp twoT (.var 1))))

/-- **The Tower of Hanoi, as the brief states it**:

    ⊢ ∀n ∀f ∀t ∀v. ∃k. Solves(n, f, t, v, k) ∧ MoveCount k = 2^n − 1

Correctness *and* optimality: the witness is a valid solution, and its
length is exactly `2^n − 1`, which is the minimum. -/
def hanoiTheorem :
    Deriv [] (.all 1 (.all 2 (.all 3 (.all 4 (.ex 5 hanoiBodyPred))))) := by
  refine Deriv.allI (Deriv.allI (Deriv.allI (Deriv.allI ?_ (by decide +kernel))
    (by decide +kernel)) (by decide +kernel)) (freshIn_nil 1)
  have g1 : Deriv [] hanoiSpec :=
    Deriv.allE (.var 1) hanoiSolvable (by decide +kernel)
  have g2 : Deriv [] (.all 3 (.all 4 (.ex 5 (hanoiBodyK 2 3 4 5)))) :=
    Deriv.allE (.var 2) g1 (by decide +kernel)
  have g3 : Deriv [] (.all 4 (.ex 5 (hanoiBodyK 2 3 4 5))) :=
    Deriv.allE (.var 3) g2 (by decide +kernel)
  have hspec : Deriv [] (.ex 5 (hanoiBodyK 2 3 4 5)) :=
    Deriv.allE (.var 4) g3 (by decide +kernel)
  refine Deriv.exE hspec ?_ (by decide +kernel) (by decide +kernel)
  refine Deriv.exI (.var 5) (Deriv.andI (Deriv.andE₁ Deriv.ax) ?_)
    (by decide +kernel)
  -- `MoveCount k = pred (succ (MoveCount k)) = pred (2^n)`
  exact (Deriv.symmE (Deriv.predSucc (.mvcount (.var 5)))).transE
    (Deriv.congPredE (Deriv.andE₂ Deriv.ax))

end Realizability
