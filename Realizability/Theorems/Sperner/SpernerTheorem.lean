/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import Realizability.Common.StrongInduction

/-!
# Sperner's Lemma (1D) / the discrete intermediate value theorem

    ⊢ ∀n ∀c. (c 0 = 0) → (c n = 1) → ∃k. k < n ∧ c k ≠ c (k+1)

a closed derivation of the fragment: colour the points `0,…,n` of a line,
with the ends coloured `0` and `1`; then somewhere adjacent colours
differ — the coloring must "cross".  This is the 1-dimensional Sperner
lemma, the discrete ancestor of the intermediate value theorem; the *2D*
version (the standard constructive route to Brouwer's fixed point
theorem) needs a genuine triangulation object and is out of scope.

## The coloring, and the one new symbol

The fragment has no function variables, so the arbitrary coloring `c` is
carried as a single `ℕ` **code** `w` (variable `2`), and `c k` is the new
`look` symbol (`Coloring.lean`), `look w k = lookN w k` decoding the
`k`-th colour of the cons-list coded by `w`.  This is the one place the
"no new symbols" discipline genuinely forces a symbol: `c k` for a *bound*
`k` is data access — a decode recursion — not a relation, so unlike order
(`∃d. …`) it cannot be encoded away.  Everything else reuses existing
kit: `k < n` is `ltT` (the E1 order layer), `c k ≠ c(k+1)` is the negated
equation, and `eqDec`/`succNeZero` drive the case analysis.

Proved for **arbitrary `ℕ`-valued** colorings — the `{0,1}` restriction is
never used, so the theorem is the general discrete IVT and the binary
Sperner statement is its special case.

## The argument (a forward scan)

Ordinary induction on the point index, on the invariant

    P(m)  :=  (c m = 0)  ∨  ∃k. k < m ∧ c k ≠ c(k+1)

— "either we are still at the starting colour `0`, or a crossing has
already happened."  `P(0)` is the boundary `c 0 = 0`; the step, at each
new point, compares `c(m+1)` to `0` (`eqDec`) and either stays on the left
disjunct or reports the crossing at `m`.  At the end `c n = 1 ≠ 0` kills
the left disjunct, forcing a crossing.  The extracted witness is a genuine
left-to-right scan returning the **first** crossing (see
`SpernerExtraction.lean`).
-/

namespace Realizability

open ContinuousFunctionals

/-! ## The formulas

Variable convention: `2 = w` (the coloring code), `0 = m` (the induction /
point index), `1 = n` (the endpoint), `3 = k` (the crossing witness),
`4` the order-difference variable of `k < …`. -/

/-- `c k`, i.e. `look w k` with `w = var 2`. -/
abbrev colorH (k : Term) : Term := .look (.var 2) k

/-- `c k ≠ c (k+1)`. -/
abbrev crossH (k : Term) : Formula :=
  (Formula.eq (colorH k) (colorH (.succ k))).neg

/-- `∃k. k < m ∧ c k ≠ c(k+1)`. -/
abbrev existsCrossH (m : Term) : Formula :=
  .ex 3 ((ltT 4 (.var 3) m).and (crossH (.var 3)))

/-- The induction invariant `P(m) := (c m = 0) ∨ ∃k<m. c k ≠ c(k+1)`, at
`m = var 0`. -/
abbrev invP : Formula :=
  (Formula.eq (colorH (.var 0)) .zero).or (existsCrossH (.var 0))

/-! ## Order weakening: `k < m → k < m+1` -/

/-- From `k < m`, conclude `k < succ m` — bump the difference by one. -/
def ltWeakSucc {Γ : List Formula} (h4 : FreshIn 4 Γ)
    (D : Deriv Γ (ltT 4 (.var 3) (.var 0))) : Deriv Γ (ltT 4 (.var 3) (.succ (.var 0))) := by
  refine Deriv.exE D ?_ h4 (by decide)
  refine Deriv.exI (.succ (.var 4)) ?_ (substOK_of_forall (by decide))
  -- goal: succ (var 3) + succ (var 4) = succ (var 0)
  exact (Deriv.allE (.var 4) (Deriv.allE (.succ (.var 3)) (Deriv.wkNil _ plusSuccDeriv)
    (substOK_of_forall (by decide))) (substOK_of_forall (by decide))).transE
    (Deriv.congSuccE Deriv.ax)

/-! ## The induction -/

/-- **`∀m. P(m)`, by ordinary induction on the point index** — the forward
scan.  Proven in the context of the boundary hypothesis `c 0 = 0`. -/
def spernerInduction :
    Deriv [Formula.eq (colorH (.var 1)) (.succ .zero), Formula.eq (colorH .zero) .zero]
      (.all 0 invP) := by
  refine Deriv.ind ?base ?step (substOK_of_forall (by decide))
  · -- base `P(0) = (c 0 = 0) ∨ …`: the boundary
    exact Deriv.orI₁ (Deriv.wk Deriv.ax)
  · -- step `∀m. P(m) → P(m+1)`
    refine Deriv.allI (Deriv.impI ?_) (by decide +kernel)
    -- context [ hP : P(m) , cn=1 , c0=0 ]
    refine Deriv.orE Deriv.ax ?caseLeft ?caseRight
    · -- still at 0: compare c(m+1) to 0
      refine Deriv.orE (Deriv.eqDec (colorH (.succ (.var 0))) .zero) ?stay ?cross
      · -- c(m+1) = 0 : stay on the left disjunct
        exact Deriv.orI₁ Deriv.ax
      · -- c(m+1) ≠ 0 : crossing at m, witness k := m
        refine Deriv.orI₂ (Deriv.exI (.var 0)
          (Deriv.andI (ltSuccSelfV 4 0 (by decide)) ?_) (substOK_of_forall (by decide)))
        -- crossH (var 0): c m = 0 and c(m+1) ≠ 0 give c m ≠ c(m+1)
        refine Deriv.impI (Deriv.impE (Deriv.wk Deriv.ax) ?_)
        -- context [ heq : c m = c(m+1) , hne : c(m+1)≠0 , hcL : c m = 0 , … ]; goal c(m+1) = 0
        exact (Deriv.symmE Deriv.ax).transE (Deriv.wk (Deriv.wk Deriv.ax))
    · -- a crossing already happened: weaken its bound past m+1
      refine Deriv.orI₂ ?_
      refine Deriv.exE Deriv.ax ?_ (by decide +kernel) (by decide +kernel)
      -- context [ hand : (k<m) ∧ (c k ≠ c(k+1)) , hcR , … ]
      exact Deriv.exI (.var 3)
        (Deriv.andI (ltWeakSucc (by decide) (Deriv.andE₁ Deriv.ax)) (Deriv.andE₂ Deriv.ax))
        (substOK_of_forall (by decide))

/-! ## The theorem -/

/-- The body of the theorem with `n = var 1` and the code `w = var 2` left
**free** (not yet `∀`-bound): `⊢ (c 0 = 0) → (c n = 1) → ∃k. k<n ∧ c k ≠
c(k+1)`.  Extraction reads the witness off *this* (instantiating `n, w`
through the environment), which keeps the realizer shallow enough to run —
the two `∀`s would otherwise add two `app₁` layers of pure-type plumbing.
-/
def spernerBody :
    Deriv [] ((Formula.eq (colorH .zero) .zero).imp
      ((Formula.eq (colorH (.var 1)) (.succ .zero)).imp (existsCrossH (.var 1)))) := by
  refine Deriv.impI (Deriv.impI ?_)
  -- context [ cn=1 , c0=0 ]; goal `∃k. k < n ∧ c k ≠ c(k+1)`
  have hPn : Deriv [Formula.eq (colorH (.var 1)) (.succ .zero), Formula.eq (colorH .zero) .zero]
      (invP.subst 0 (.var 1)) :=
    Deriv.allE (.var 1) spernerInduction (substOK_of_forall (by decide))
  refine Deriv.orE hPn ?atEnd ?found
  · -- left disjunct `c n = 0` contradicts `c n = 1`
    refine Deriv.botE (Deriv.impE (Deriv.succNeZero .zero) ?_)
    -- succ 0 = c n = 0
    exact (Deriv.symmE (Deriv.wk Deriv.ax)).transE Deriv.ax
  · -- right disjunct is exactly the goal
    exact Deriv.ax

/-- **Sperner's Lemma, 1D / the discrete IVT**:
`⊢ ∀n ∀c. (c 0 = 0) → (c n = 1) → ∃k. k < n ∧ c k ≠ c(k+1)`.

`c` is the coloring coded by variable `2`; `look` reads its colours.
Proved for arbitrary `ℕ`-valued colorings; the `∀n ∀c` is `spernerBody`
generalised. -/
def spernerTheorem :
    Deriv [] (.all 1 (.all 2
      ((Formula.eq (colorH .zero) .zero).imp
        ((Formula.eq (colorH (.var 1)) (.succ .zero)).imp (existsCrossH (.var 1)))))) :=
  Deriv.allI (Deriv.allI spernerBody (freshIn_nil 2)) (freshIn_nil 1)

/-! ## Certification -/

/-- The extracted realizer of Sperner's lemma realizes it. -/
theorem sperner_realized (ρ : ℕ → ℕ) {n : ℕ} (hn : derivBound spernerTheorem ≤ n) :
    MR ρ (.all 1 (.all 2
      ((Formula.eq (colorH .zero) .zero).imp
        ((Formula.eq (colorH (.var 1)) (.succ .zero)).imp (existsCrossH (.var 1)))))) n
      (extract spernerTheorem ρ [] n) :=
  soundness spernerTheorem ρ [] trivial n hn

/-- Its type-2 extract is continuous. -/
theorem sperner_extract_continuous (ρ : ℕ → ℕ) :
    Continuous2 (extract spernerTheorem ρ [] 1) :=
  extract_continuous spernerTheorem ρ

#print axioms sperner_realized
#print axioms sperner_extract_continuous

end Realizability
