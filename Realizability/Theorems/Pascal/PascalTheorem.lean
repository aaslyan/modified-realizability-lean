/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import Realizability.Theorems.Goodstein.Goodstein

/-!
# Phase F3: Pascal's triangle mod 2, inside the fragment

Four theorems, all by **ordinary induction** — no `TI(ε₀)`, no ordinals,
and no `∃`: the statements are decidable equations and a disjunction, so
this is the lightest infrastructure in the development.

| theorem | says |
|---|---|
| `pasZeroCol` | `∀n. pas(n,0) = 1` — the left edge |
| `pasAbove` | `∀n ∀j. pas(n, n+j+1) = 0` — everything above the diagonal vanishes |
| `pasDiag` | `∀n. pas(n,n) = 1` — the right edge |
| **`pasTotal`** | `∀n ∀k. pas(n,k) = 1 ∨ pas(n,k) = 0` — every entry is a bit |

Only the first is nearly immediate.  `pasAbove` is the real induction:
it needs its hypothesis at *two* arguments (`j` and `j+1`), which is what
makes the `∀j` inside the induction formula necessary rather than
decorative, and it consumes Phase A's `x + succ y = succ (x + y)` to line
the indices up.  `pasDiag` then reads the diagonal off `pasAbove` at
`j = 0`, and `pasTotal` is a **nested** induction — outer on the row,
inner on the column.

## Why the inner induction exists at all

The fragment has no case-analysis axiom "every number is `0` or a
successor", and no order relation, so a variable cannot be split into
`0`/`succ k` by any rule.  Where an informal proof would say "case on
`k`", the derivations below run `ind` on `k` and *discard the induction
hypothesis*: the base and step cases of an induction are exactly the two
cases of a `0`/`succ` split.  That is the fragment's only way to do it,
and it is worth naming because it recurs three times here.

## What is imported, and what is not

The import is exactly `pasN`'s four structural equations (Phase F2) plus
`xor`'s numeral graph.  The two clauses the brief lists as
characteristic — `pas(n,n) = 1`, and vanishing above the diagonal — are
**derived here**, not assumed.  `Nat.choose` appears nowhere in this file
or in the fragment; it is used only in `PascalExtraction.lean`, as an
independent reference for cross-checking, exactly the role
`WilliamAngus/Goodstein` played in Phase B.
-/

namespace Realizability

open ContinuousFunctionals

/-! ## Congruence, as derivation-formers -/

/-- Congruence of `xor`. -/
def Deriv.congXorE {Γ : List Formula} {s₁ t₁ s₂ t₂ : Term}
    (D₁ : Deriv Γ (.eq s₁ t₁)) (D₂ : Deriv Γ (.eq s₂ t₂)) :
    Deriv Γ (.eq (.xor s₁ s₂) (.xor t₁ t₂)) :=
  .impE (.impE (.eqCongXor s₁ t₁ s₂ t₂) D₁) D₂

/-- Congruence of `pas`. -/
def Deriv.congPasE {Γ : List Formula} {s₁ t₁ s₂ t₂ : Term}
    (D₁ : Deriv Γ (.eq s₁ t₁)) (D₂ : Deriv Γ (.eq s₂ t₂)) :
    Deriv Γ (.eq (.pas s₁ s₂) (.pas t₁ t₂)) :=
  .impE (.impE (.eqCongPas s₁ t₁ s₂ t₂) D₁) D₂

/-! ## The left edge -/

/-- **`∀n. pas(n,0) = 1`.**  Induction on `n` used purely as a `0`/`succ`
split: both cases are axioms and the hypothesis is discarded. -/
def pasZeroCol : Deriv [] (.all 1 (.eq (.pas (.var 1) .zero) (.succ .zero))) :=
  .ind Deriv.pasZeroZero
    (.allI (.impI (Deriv.pasSuccZero (.var 1))) (freshIn_nil 1))
    (substOK_of_forall (by decide))

/-! ## Above the diagonal -/

/-- **`∀n ∀j. pas(n, succ (n + j)) = 0`.**

The one induction of the phase that genuinely needs its hypothesis twice:
the step's two recursive entries are at `j` and at `j + 1`, and lining the
second up costs Phase A's `plusSuccDeriv`. -/
def pasAbove : Deriv []
    (.all 1 (.all 2 (.eq (.pas (.var 1) (.succ (.plus (.var 1) (.var 2)))) .zero))) := by
  refine .ind ?_ ?_ (substOK_of_forall (by decide))
  · -- base: `pas(0, succ (0 + j)) = 0`
    refine Deriv.allI ?_ (freshIn_nil 2)
    exact (Deriv.congPasE (.eqRefl .zero)
        (Deriv.congSuccE (Deriv.zeroPlus (.var 2)))).transE
      (Deriv.pasZeroSucc (.var 2))
  · -- step
    refine Deriv.allI (Deriv.impI (Deriv.allI ?_ (by decide +kernel)))
      (freshIn_nil 1)
    -- context: the induction hypothesis `∀j. pas(n, succ (n + j)) = 0`
    have ih : Deriv [.all 2 (.eq (.pas (.var 1) (.succ (.plus (.var 1) (.var 2)))) .zero)]
        (.all 2 (.eq (.pas (.var 1) (.succ (.plus (.var 1) (.var 2)))) .zero)) := .ax
    have ihj : Deriv [.all 2 (.eq (.pas (.var 1) (.succ (.plus (.var 1) (.var 2)))) .zero)]
        (.eq (.pas (.var 1) (.succ (.plus (.var 1) (.var 2)))) .zero) :=
      Deriv.allE (.var 2) ih (by decide +kernel)
    have ihsj : Deriv [.all 2 (.eq (.pas (.var 1) (.succ (.plus (.var 1) (.var 2)))) .zero)]
        (.eq (.pas (.var 1) (.succ (.plus (.var 1) (.succ (.var 2))))) .zero) :=
      Deriv.allE (.succ (.var 2)) ih (by decide +kernel)
    -- `n + succ j = succ (n + j)`, from Phase A
    have hps : Deriv [.all 2 (.eq (.pas (.var 1) (.succ (.plus (.var 1) (.var 2)))) .zero)]
        (.eq (.plus (.var 1) (.succ (.var 2))) (.succ (.plus (.var 1) (.var 2)))) :=
      Deriv.allE (.var 2)
        (Deriv.allE (.var 1) (Deriv.wk plusSuccDeriv') (substOK_of_forall (by decide)))
        (substOK_of_forall (by decide))
    have ihsj' : Deriv [.all 2 (.eq (.pas (.var 1) (.succ (.plus (.var 1) (.var 2)))) .zero)]
        (.eq (.pas (.var 1) (.succ (.succ (.plus (.var 1) (.var 2))))) .zero) :=
      (Deriv.congPasE (.eqRefl (.var 1))
        (Deriv.congSuccE (Deriv.symmE hps))).transE ihsj
    -- the goal's index: `succ n + j = succ (n + j)`
    have hidx : Deriv [.all 2 (.eq (.pas (.var 1) (.succ (.plus (.var 1) (.var 2)))) .zero)]
        (.eq (.pas (.succ (.var 1)) (.succ (.plus (.succ (.var 1)) (.var 2))))
          (.pas (.succ (.var 1)) (.succ (.succ (.plus (.var 1) (.var 2)))))) :=
      Deriv.congPasE (.eqRefl _)
        (Deriv.congSuccE (Deriv.succPlus (.var 1) (.var 2)))
    refine hidx.transE ((Deriv.pasSuccSucc (.var 1)
      (.succ (.plus (.var 1) (.var 2)))).transE ?_)
    -- `xor(0, 0) = 0`
    exact (Deriv.congXorE ihj ihsj').transE (Deriv.xorNum 0 0)

/-! ## The diagonal -/

/-- **`∀n. pas(n,n) = 1`** — the clause the brief lists as characteristic,
derived rather than assumed.  The step reads `pas(n, succ n) = 0` off
`pasAbove` at `j = 0`. -/
def pasDiag : Deriv [] (.all 1 (.eq (.pas (.var 1) (.var 1)) (.succ .zero))) := by
  refine .ind Deriv.pasZeroZero ?_ (substOK_of_forall (by decide))
  refine Deriv.allI (Deriv.impI ?_) (freshIn_nil 1)
  have ih : Deriv [.eq (.pas (.var 1) (.var 1)) (.succ .zero)]
      (.eq (.pas (.var 1) (.var 1)) (.succ .zero)) := .ax
  -- `pas(n, succ n) = 0`, from `pasAbove` at `j = 0` and `n + 0 = n`
  have hab : Deriv [.eq (.pas (.var 1) (.var 1)) (.succ .zero)]
      (.eq (.pas (.var 1) (.succ (.plus (.var 1) .zero))) .zero) :=
    Deriv.allE .zero
      (Deriv.allE (.var 1) (Deriv.wk pasAbove) (by decide +kernel))
      (by decide +kernel)
  have hz : Deriv [.eq (.pas (.var 1) (.var 1)) (.succ .zero)]
      (.eq (.plus (.var 1) .zero) (.var 1)) :=
    Deriv.allE (.var 1) (Deriv.wk plusZeroDeriv) (substOK_of_forall (by decide))
  have habove : Deriv [.eq (.pas (.var 1) (.var 1)) (.succ .zero)]
      (.eq (.pas (.var 1) (.succ (.var 1))) .zero) :=
    (Deriv.congPasE (.eqRefl (.var 1))
      (Deriv.congSuccE (Deriv.symmE hz))).transE hab
  refine (Deriv.pasSuccSucc (.var 1) (.var 1)).transE ?_
  exact (Deriv.congXorE ih habove).transE (Deriv.xorNum 1 0)

/-! ## Totality

The nested induction: outer on the row, inner on the column, with the
inner hypothesis discarded — the fragment's only way to case-split a
variable into `0`/`succ`. -/

/-- The body of the totality statement, at a given row term. -/
abbrev pasBit (row : Term) : Formula :=
  (Formula.eq (.pas row (.var 2)) (.succ .zero)).or
    (Formula.eq (.pas row (.var 2)) .zero)

/-- **`∀n ∀k. pas(n,k) = 1 ∨ pas(n,k) = 0`** — every entry is a bit, and
the disjunction's *tag* is the extracted decider. -/
def pasTotal : Deriv [] (.all 1 (.all 2 (pasBit (.var 1)))) := by
  refine .ind ?_ ?_ (substOK_of_forall (by decide))
  · -- base row: `pas(0,k)` is `1` at `k = 0` and `0` after
    refine .ind (Deriv.orI₁ Deriv.pasZeroZero) ?_ (substOK_of_forall (by decide))
    exact Deriv.allI (Deriv.impI (Deriv.orI₂ (Deriv.pasZeroSucc (.var 2))))
      (freshIn_nil 2)
  · -- step row
    refine Deriv.allI (Deriv.impI ?_) (freshIn_nil 1)
    refine .ind (Deriv.orI₁ (Deriv.pasSuccZero (.var 1))) ?_
      (substOK_of_forall (by decide))
    refine Deriv.allI (Deriv.impI ?_) (by decide +kernel)
    -- context: [inner IH at k, outer IH `∀k. pas(n,k) ∈ {0,1}`]
    have outer : Deriv [pasBit (.succ (.var 1)), .all 2 (pasBit (.var 1))]
        (.all 2 (pasBit (.var 1))) := .wk .ax
    have hk : Deriv [pasBit (.succ (.var 1)), .all 2 (pasBit (.var 1))]
        (pasBit (.var 1)) := Deriv.allE (.var 2) outer (by decide +kernel)
    have hsk : Deriv [pasBit (.succ (.var 1)), .all 2 (pasBit (.var 1))]
        ((Formula.eq (.pas (.var 1) (.succ (.var 2))) (.succ .zero)).or
          (Formula.eq (.pas (.var 1) (.succ (.var 2))) .zero)) :=
      Deriv.allE (.succ (.var 2)) outer (by decide +kernel)
    -- the recursion equation, then the four value cases
    refine Deriv.orE hk ?_ ?_ <;>
      refine Deriv.orE (Deriv.wk hsk) ?_ ?_
    · -- 1, 1 → 0
      exact Deriv.orI₂ ((Deriv.pasSuccSucc (.var 1) (.var 2)).transE
        ((Deriv.congXorE (Deriv.wk .ax) .ax).transE (Deriv.xorNum 1 1)))
    · -- 1, 0 → 1
      exact Deriv.orI₁ ((Deriv.pasSuccSucc (.var 1) (.var 2)).transE
        ((Deriv.congXorE (Deriv.wk .ax) .ax).transE (Deriv.xorNum 1 0)))
    · -- 0, 1 → 1
      exact Deriv.orI₁ ((Deriv.pasSuccSucc (.var 1) (.var 2)).transE
        ((Deriv.congXorE (Deriv.wk .ax) .ax).transE (Deriv.xorNum 0 1)))
    · -- 0, 0 → 0
      exact Deriv.orI₂ ((Deriv.pasSuccSucc (.var 1) (.var 2)).transE
        ((Deriv.congXorE (Deriv.wk .ax) .ax).transE (Deriv.xorNum 0 0)))

end Realizability
