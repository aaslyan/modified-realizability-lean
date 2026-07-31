/-
# Phase E2 (Euclid): the divisibility foundation

The Euclid roadmap's E2 proves the full greatest-common-divisor
characterisation.  This file starts it with the reusable algebra that
characterisation rests on, all in the fragment with **no new symbols**:

- **distributivity** `d·(x+y) = d·x + d·y`, one more `ind` theorem;
- the **`Divides` predicate**, `d ∣ a := ∃q. a = d·q` (just `∃` and `×`),
  and its basic laws — reflexivity, `d ∣ 0`, and `d ∣ x → d ∣ y →
  d ∣ (x+y)` (the payoff of distributivity).

`gcd` itself is deferred: it will be stated **existentially**
(`∃g. g ∣ a ∧ g ∣ b ∧ ∀d. d ∣ a → d ∣ b → d ∣ g`), so the extracted
realizer *is* the gcd and no `gcd` symbol is needed — the same
witness-carrying design as Goodstein and Hanoi.
-/
import Realizability.StrongInduction

namespace Realizability

open ContinuousFunctionals

/-! ## Congruence of `×` (the `+` versions are in `Arithmetic.lean`) -/

/-- Congruence of `×` in the right argument. -/
def Deriv.congTimesR {Γ : List Formula} {s t : Term} (u : Term)
    (D : Deriv Γ (.eq s t)) : Deriv Γ (.eq (.times u s) (.times u t)) :=
  .impE (.impE (.eqCongTimes u u s t) (.eqRefl u)) D

/-! ## Distributivity -/

/-- `d·(x+y) = d·x + d·y`, free variables `0 = d`, `1 = x`, `2 = y`. -/
private abbrev distribEq : Formula :=
  .eq (.times (.var 0) (.plus (.var 1) (.var 2)))
    (.plus (.times (.var 0) (.var 1)) (.times (.var 0) (.var 2)))

/-- **`∀d ∀x ∀y. d·(x+y) = d·x + d·y`**, by `ind` on `y` (carrying
`∀d ∀x`).  Base: `x+0 = x` and `d·0 = 0`.  Step: `d·(x+succ y)` unfolds by
`plusSucc`/`timesSucc` to `d·(x+y) + d`, the IH rewrites it to
`(d·x + d·y) + d`, and `plusAssoc` + `timesSucc` reassemble the goal. -/
def distribDeriv : Deriv [] (.all 0 (.all 1 (.all 2 distribEq))) := by
  refine Deriv.allI (Deriv.allI (Deriv.ind ?_ ?_ (substOK_of_forall (by decide)))
    (freshIn_nil 1)) (freshIn_nil 0)
  · -- base: `d·(x+0) = d·x + d·0`
    have lhs : Deriv [] (.eq (.times (.var 0) (.plus (.var 1) .zero))
        (.times (.var 0) (.var 1))) :=
      Deriv.congTimesR (.var 0)
        (Deriv.allE (.var 1) plusZeroDeriv (substOK_of_forall (by decide)))
    have rhs : Deriv [] (.eq (.plus (.times (.var 0) (.var 1)) (.times (.var 0) .zero))
        (.times (.var 0) (.var 1))) :=
      (Deriv.congPlusR (.times (.var 0) (.var 1))
          (Deriv.allE (.var 0) timesZeroDeriv (substOK_of_forall (by decide)))).transE
        (Deriv.allE (.times (.var 0) (.var 1)) plusZeroDeriv (substOK_of_forall (by decide)))
    exact lhs.transE (Deriv.symmE rhs)
  · -- step
    refine Deriv.allI (Deriv.impI ?_) (freshIn_nil 2)
    -- context [distribEq]; goal `d·(x+succ y) = d·x + d·(succ y)`
    have ih : Deriv [distribEq] distribEq := Deriv.ax
    have e1 : Deriv [distribEq]
        (.eq (.times (.var 0) (.plus (.var 1) (.succ (.var 2))))
          (.times (.var 0) (.succ (.plus (.var 1) (.var 2))))) :=
      Deriv.congTimesR (.var 0)
        (Deriv.allE (.var 2) (Deriv.allE (.var 1) (Deriv.wkNil _ plusSuccDeriv')
          (substOK_of_forall (by decide))) (substOK_of_forall (by decide)))
    have e2 : Deriv [distribEq]
        (.eq (.times (.var 0) (.succ (.plus (.var 1) (.var 2))))
          (.plus (.times (.var 0) (.plus (.var 1) (.var 2))) (.var 0))) :=
      Deriv.allE (.plus (.var 1) (.var 2))
        (Deriv.allE (.var 0) (Deriv.wkNil _ timesSuccDeriv)
          (substOK_of_forall (by decide))) (substOK_of_forall (by decide))
    have e3 : Deriv [distribEq]
        (.eq (.plus (.times (.var 0) (.plus (.var 1) (.var 2))) (.var 0))
          (.plus (.plus (.times (.var 0) (.var 1)) (.times (.var 0) (.var 2))) (.var 0))) :=
      Deriv.congPlusL (.var 0) ih
    have e4 : Deriv [distribEq]
        (.eq (.plus (.plus (.times (.var 0) (.var 1)) (.times (.var 0) (.var 2))) (.var 0))
          (.plus (.times (.var 0) (.var 1))
            (.plus (.times (.var 0) (.var 2)) (.var 0)))) :=
      Deriv.allE (.var 0) (Deriv.allE (.times (.var 0) (.var 2))
        (Deriv.allE (.times (.var 0) (.var 1)) (Deriv.wkNil _ plusAssocDeriv')
          (substOK_of_forall (by decide))) (substOK_of_forall (by decide)))
        (substOK_of_forall (by decide))
    have e5 : Deriv [distribEq]
        (.eq (.plus (.times (.var 0) (.var 2)) (.var 0)) (.times (.var 0) (.succ (.var 2)))) :=
      Deriv.symmE (Deriv.allE (.var 2) (Deriv.allE (.var 0) (Deriv.wkNil _ timesSuccDeriv)
        (substOK_of_forall (by decide))) (substOK_of_forall (by decide)))
    exact (((e1.transE e2).transE e3).transE e4).transE
      (Deriv.congPlusR (.times (.var 0) (.var 1)) e5)

/-! ## The `Divides` predicate and its laws -/

/-- `d ∣ a`, witnessed by quotient variable `q`: `∃q. a = d · q`. -/
def dvdT (q : ℕ) (d a : Term) : Formula :=
  .ex q (.eq a (.times d (.var q)))

/-- **`∀d. d ∣ d`** — quotient `1`.  (`d · 1 = d · 0 + d = d`.) -/
def dvdReflDeriv : Deriv [] (.all 0 (dvdT 1 (.var 0) (.var 0))) := by
  refine Deriv.allI (Deriv.exI (.succ .zero) ?_ (substOK_numeral 1 _)) (freshIn_nil 0)
  have hd : Deriv [] (.eq (.times (.var 0) (.succ .zero)) (.var 0)) :=
    ((Deriv.allE .zero (Deriv.allE (.var 0) timesSuccDeriv
        (substOK_of_forall (by decide))) (substOK_of_forall (by decide))).transE
      (Deriv.congPlusL (.var 0)
        (Deriv.allE (.var 0) timesZeroDeriv (substOK_of_forall (by decide))))).transE
      (Deriv.zeroPlus (.var 0))
  simpa only [dvdT, Formula.subst, Term.subst] using Deriv.symmE hd

/-- **`∀d. d ∣ 0`** — quotient `0`. -/
def dvdZeroDeriv : Deriv [] (.all 0 (dvdT 1 (.var 0) .zero)) := by
  refine Deriv.allI (Deriv.exI .zero ?_ (substOK_numeral 0 _)) (freshIn_nil 0)
  simpa only [dvdT, Formula.subst, Term.subst] using
    Deriv.symmE (Deriv.allE (.var 0) timesZeroDeriv (substOK_of_forall (by decide)))

/-- **`∀d ∀a ∀b. d ∣ a → d ∣ b → d ∣ (a+b)`** — the payoff of
distributivity: `a = d·qₐ`, `b = d·q_b`, so `a+b = d·(qₐ+q_b)`. -/
def dvdAddDeriv : Deriv [] (.all 0 (.all 1 (.all 2
    ((dvdT 3 (.var 0) (.var 1)).imp ((dvdT 4 (.var 0) (.var 2)).imp
      (dvdT 5 (.var 0) (.plus (.var 1) (.var 2)))))))) := by
  refine Deriv.allI (Deriv.allI (Deriv.allI (Deriv.impI (Deriv.impI ?_))
    (freshIn_nil 2)) (freshIn_nil 1)) (freshIn_nil 0)
  -- context [ d∣b , d∣a ];  eliminate d∣a (∃q₃), then d∣b (∃q₄)
  refine Deriv.exE (Deriv.wk Deriv.ax) ?_ (by decide) (by decide)
  refine Deriv.exE (Deriv.wk Deriv.ax) ?_ (by decide) (by decide)
  -- context [ hb : b = d·q₄ , ha : a = d·q₃ , d∣b , d∣a ]  (q₄ = var 4, q₃ = var 3)
  set Γ : List Formula :=
    [Formula.eq (.var 2) (.times (.var 0) (.var 4)),
     Formula.eq (.var 1) (.times (.var 0) (.var 3)),
     dvdT 4 (.var 0) (.var 2), dvdT 3 (.var 0) (.var 1)] with hΓ
  have hb : Deriv Γ (Formula.eq (.var 2) (.times (.var 0) (.var 4))) := .ax
  have ha : Deriv Γ (Formula.eq (.var 1) (.times (.var 0) (.var 3))) := .wk .ax
  have hdist : Deriv Γ (.eq (.times (.var 0) (.plus (.var 3) (.var 4)))
      (.plus (.times (.var 0) (.var 3)) (.times (.var 0) (.var 4)))) :=
    Deriv.allE (.var 4) (Deriv.allE (.var 3) (Deriv.allE (.var 0)
      (Deriv.wkNil _ distribDeriv) (substOK_of_forall (by decide)))
      (substOK_of_forall (by decide))) (substOK_of_forall (by decide))
  refine Deriv.exI (.plus (.var 3) (.var 4)) ?_ (substOK_of_forall (by decide))
  -- goal: a + b = d·(q₃+q₄)
  simpa only [dvdT, Formula.subst, Term.subst] using
    (Deriv.congPlusE ha hb).transE (Deriv.symmE hdist)

/-! ## Left cancellation and the subtractive divisibility law

The "greatest" half of the gcd characterisation needs `d ∣ a → d ∣ b →
d ∣ (b − a)`, i.e. `d ∣ a → d ∣ (a+c) → d ∣ c`.  Deriving it needs
left-cancellation of `+`. -/

/-- The cancellation equation `a + x = a + y → x = y`, variables
`0 = a`, `1 = x`, `2 = y`. -/
private abbrev cancelEq : Formula :=
  (Formula.eq (.plus (.var 0) (.var 1)) (.plus (.var 0) (.var 2))).imp
    (.eq (.var 1) (.var 2))

/-- **`∀a ∀x ∀y. a + x = a + y → x = y`** — left cancellation, by `ind`
on `a` (base by `zeroPlus`, step by `succPlus` + `succInj`). -/
def cancelAddDeriv : Deriv [] (.all 0 (.all 1 (.all 2 cancelEq))) := by
  refine Deriv.ind ?_ ?_ (substOK_of_forall (by decide))
  · refine Deriv.allI (Deriv.allI (Deriv.impI ?_) (freshIn_nil 2)) (freshIn_nil 1)
    exact (Deriv.symmE (Deriv.zeroPlus (.var 1))).transE
      (Deriv.ax.transE (Deriv.zeroPlus (.var 2)))
  · refine Deriv.allI (Deriv.impI (Deriv.allI (Deriv.allI (Deriv.impI ?_)
      (by decide +kernel)) (by decide +kernel))) (freshIn_nil 0)
    -- context [ h : succ a + x = succ a + y , IH ]
    set Γ : List Formula :=
      [Formula.eq (.plus (.succ (.var 0)) (.var 1)) (.plus (.succ (.var 0)) (.var 2)),
       .all 1 (.all 2 cancelEq)] with hΓ
    have hs : Deriv Γ (Formula.eq (.succ (.plus (.var 0) (.var 1)))
        (.succ (.plus (.var 0) (.var 2)))) :=
      ((Deriv.symmE (Deriv.succPlus (.var 0) (.var 1))).transE Deriv.ax).transE
        (Deriv.succPlus (.var 0) (.var 2))
    have hinner : Deriv Γ (Formula.eq (.plus (.var 0) (.var 1)) (.plus (.var 0) (.var 2))) :=
      Deriv.impE (Deriv.succInj _ _) hs
    have ih0 : Deriv Γ (.all 1 (.all 2 cancelEq)) := Deriv.wk Deriv.ax
    have ih1 : Deriv Γ (.all 2 cancelEq) :=
      Deriv.allE (.var 1) ih0 (substOK_of_forall (by decide))
    have ihinst : Deriv Γ cancelEq :=
      Deriv.allE (.var 2) ih1 (substOK_of_forall (by decide))
    exact Deriv.impE ihinst hinner

/-- `∀x ∀c. x + c = 0 → c = 0` — a summand of `0` is `0`.  `caseNat` on
`c`; a successor makes `x + c` a successor, contradicting `succNeZero`. -/
def addEqZeroDeriv :
    Deriv [] (.all 0 (.all 1 ((Formula.eq (.plus (.var 0) (.var 1)) .zero).imp
      (.eq (.var 1) .zero)))) := by
  refine Deriv.allI (Deriv.allI (Deriv.impI ?_) (freshIn_nil 1)) (freshIn_nil 0)
  -- context [ h : x + c = 0 ]
  refine Deriv.orE (Deriv.allE (.var 1) (Deriv.wkNil _ caseNatDeriv)
    (substOK_of_forall (by decide))) ?c0 ?cS
  · exact Deriv.ax
  · -- c = succ m : x + succ m = succ (x + m) = 0, impossible
    refine Deriv.exE Deriv.ax ?_ (by decide) (by decide)
    -- context [ hm : c = succ m , (∃5 …) , h : x + c = 0 ]
    have hm : Deriv [Formula.eq (.var 1) (.succ (.var 5)),
        .ex 5 (Formula.eq (.var 1) (.succ (.var 5))),
        Formula.eq (.plus (.var 0) (.var 1)) .zero]
        (Formula.eq (.var 1) (.succ (.var 5))) := .ax
    have hsum : Deriv [Formula.eq (.var 1) (.succ (.var 5)),
        .ex 5 (Formula.eq (.var 1) (.succ (.var 5))),
        Formula.eq (.plus (.var 0) (.var 1)) .zero]
        (Formula.eq (.succ (.plus (.var 0) (.var 5))) .zero) :=
      ((Deriv.symmE (Deriv.allE (.var 5) (Deriv.allE (.var 0)
          (Deriv.wkNil _ plusSuccDeriv') (substOK_of_forall (by decide)))
          (substOK_of_forall (by decide)))).transE
        (Deriv.congPlusR (.var 0) (Deriv.symmE hm))).transE (Deriv.wk (Deriv.wk Deriv.ax))
    exact Deriv.botE (Deriv.impE (Deriv.succNeZero (.plus (.var 0) (.var 5))) hsum)

/-- **`∀d ∀a ∀c. d ∣ a → d ∣ (a+c) → d ∣ c`** — the subtractive law.
`a = d·q₅`, `a+c = d·q₆`, so `d·q₅ + c = d·q₆`.  Trichotomy on `q₅,q₆`:
either `q₆ = q₅ + r` (cancel `d·q₅` to get `c = d·r`) or `q₅ = succ q₆ + s`
(then `d·q₆ + (d + (d·s + c)) = d·q₆`, cancelling and peeling forces
`c = 0`, and `d ∣ 0`).  Variables `0 = d`, `1 = a`, `4 = c`; quotients
`5,6`; trichotomy's own difference variables `2,3` stay clear. -/
def dvdSubDeriv : Deriv [] (.all 0 (.all 1 (.all 4
    ((dvdT 5 (.var 0) (.var 1)).imp ((dvdT 6 (.var 0) (.plus (.var 1) (.var 4))).imp
      (dvdT 7 (.var 0) (.var 4))))))) := by
  refine Deriv.allI (Deriv.allI (Deriv.allI (Deriv.impI (Deriv.impI ?_))
    (freshIn_nil 4)) (freshIn_nil 1)) (freshIn_nil 0)
  -- context [ d∣(a+c) , d∣a ];  eliminate d∣a (q₅) then d∣(a+c) (q₆)
  refine Deriv.exE (Deriv.wk Deriv.ax) ?_ (by decide) (by decide)
  refine Deriv.exE (Deriv.wk Deriv.ax) ?_ (by decide) (by decide)
  set Γ0 : List Formula :=
    [Formula.eq (.plus (.var 1) (.var 4)) (.times (.var 0) (.var 6)),
     Formula.eq (.var 1) (.times (.var 0) (.var 5)),
     dvdT 6 (.var 0) (.plus (.var 1) (.var 4)), dvdT 5 (.var 0) (.var 1)] with hΓ0
  have hq : Deriv Γ0 (Formula.eq (.plus (.var 1) (.var 4)) (.times (.var 0) (.var 6))) := .ax
  have ha : Deriv Γ0 (Formula.eq (.var 1) (.times (.var 0) (.var 5))) := .wk .ax
  have hkey : Deriv Γ0 (Formula.eq (.plus (.times (.var 0) (.var 5)) (.var 4))
      (.times (.var 0) (.var 6))) :=
    (Deriv.congPlusL (.var 4) (Deriv.symmE ha)).transE hq
  refine Deriv.orE (Deriv.allE (.var 6) (Deriv.allE (.var 5)
    (Deriv.wkNil _ trichotomyDeriv) (substOK_of_forall (by decide)))
    (substOK_of_forall (by decide))) ?le ?lt
  · -- q₅ ≤ q₆ : `q₆ = q₅ + r`  (r = var 2)
    refine Deriv.exE Deriv.ax ?_ (by decide) (by decide)
    set Δ : List Formula :=
      (Formula.eq (.plus (.var 5) (.var 2)) (.var 6)) :: leT 2 (.var 5) (.var 6) :: Γ0 with hΔ
    have hr : Deriv Δ (Formula.eq (.plus (.var 5) (.var 2)) (.var 6)) := .ax
    have hkeyΔ : Deriv Δ (Formula.eq (.plus (.times (.var 0) (.var 5)) (.var 4))
        (.times (.var 0) (.var 6))) := .wk (.wk hkey)
    have hdq6 : Deriv Δ (Formula.eq (.times (.var 0) (.var 6))
        (.plus (.times (.var 0) (.var 5)) (.times (.var 0) (.var 2)))) :=
      (Deriv.congTimesR (.var 0) (Deriv.symmE hr)).transE
        (Deriv.allE (.var 2) (Deriv.allE (.var 5) (Deriv.allE (.var 0)
          (Deriv.wkNil _ distribDeriv) (substOK_of_forall (by decide)))
          (substOK_of_forall (by decide))) (substOK_of_forall (by decide)))
    have hc : Deriv Δ (Formula.eq (.var 4) (.times (.var 0) (.var 2))) :=
      Deriv.impE (Deriv.allE (.times (.var 0) (.var 2)) (Deriv.allE (.var 4)
        (Deriv.allE (.times (.var 0) (.var 5)) (Deriv.wkNil _ cancelAddDeriv)
          (substOK_of_forall (by decide))) (substOK_of_forall (by decide)))
        (substOK_of_forall (by decide))) (hkeyΔ.transE hdq6)
    exact Deriv.exI (.var 2) (by simpa only [dvdT, Formula.subst, Term.subst] using hc)
      (substOK_of_forall (by decide))
  · -- q₆ < q₅ : `q₅ = succ q₆ + s`  (s = var 3), forcing c = 0
    refine Deriv.exE Deriv.ax ?_ (by decide) (by decide)
    set Δ : List Formula :=
      (Formula.eq (.plus (.succ (.var 6)) (.var 3)) (.var 5)) :: ltT 3 (.var 6) (.var 5) :: Γ0
      with hΔ
    have hs : Deriv Δ (Formula.eq (.plus (.succ (.var 6)) (.var 3)) (.var 5)) := .ax
    have hkeyΔ : Deriv Δ (Formula.eq (.plus (.times (.var 0) (.var 5)) (.var 4))
        (.times (.var 0) (.var 6))) := .wk (.wk hkey)
    -- d·q₅ = (d·q₆ + d) + d·s
    have hq5 : Deriv Δ (Formula.eq (.times (.var 0) (.var 5))
        (.plus (.plus (.times (.var 0) (.var 6)) (.var 0)) (.times (.var 0) (.var 3)))) :=
      ((Deriv.congTimesR (.var 0) (Deriv.symmE hs)).transE
        (Deriv.allE (.var 3) (Deriv.allE (.succ (.var 6)) (Deriv.allE (.var 0)
          (Deriv.wkNil _ distribDeriv) (substOK_of_forall (by decide)))
          (substOK_of_forall (by decide))) (substOK_of_forall (by decide)))).transE
        (Deriv.congPlusL (.times (.var 0) (.var 3))
          (Deriv.allE (.var 6) (Deriv.allE (.var 0) (Deriv.wkNil _ timesSuccDeriv)
            (substOK_of_forall (by decide))) (substOK_of_forall (by decide))))
    -- `((d·q₆ + d) + d·s) + c = d·q₆`
    have heq : Deriv Δ (Formula.eq
        (.plus (.plus (.plus (.times (.var 0) (.var 6)) (.var 0)) (.times (.var 0) (.var 3)))
          (.var 4)) (.times (.var 0) (.var 6))) :=
      (Deriv.symmE (Deriv.congPlusL (.var 4) hq5)).transE hkeyΔ
    -- reassociate to `d·q₆ + (d + (d·s + c)) = d·q₆`
    have hass1 : Deriv Δ (Formula.eq
        (.plus (.plus (.plus (.times (.var 0) (.var 6)) (.var 0)) (.times (.var 0) (.var 3)))
          (.var 4))
        (.plus (.plus (.times (.var 0) (.var 6)) (.var 0))
          (.plus (.times (.var 0) (.var 3)) (.var 4)))) :=
      Deriv.allE (.var 4) (Deriv.allE (.times (.var 0) (.var 3))
        (Deriv.allE (.plus (.times (.var 0) (.var 6)) (.var 0))
          (Deriv.wkNil _ plusAssocDeriv') (substOK_of_forall (by decide)))
        (substOK_of_forall (by decide))) (substOK_of_forall (by decide))
    have hass2 : Deriv Δ (Formula.eq
        (.plus (.plus (.times (.var 0) (.var 6)) (.var 0))
          (.plus (.times (.var 0) (.var 3)) (.var 4)))
        (.plus (.times (.var 0) (.var 6))
          (.plus (.var 0) (.plus (.times (.var 0) (.var 3)) (.var 4))))) :=
      Deriv.allE (.plus (.times (.var 0) (.var 3)) (.var 4)) (Deriv.allE (.var 0)
        (Deriv.allE (.times (.var 0) (.var 6)) (Deriv.wkNil _ plusAssocDeriv')
          (substOK_of_forall (by decide))) (substOK_of_forall (by decide)))
        (substOK_of_forall (by decide))
    -- `d·q₆ + X = d·q₆ + 0`, cancel to `X = 0`, then peel `d`, then `d·s`
    have hform : Deriv Δ (Formula.eq
        (.plus (.times (.var 0) (.var 6))
          (.plus (.var 0) (.plus (.times (.var 0) (.var 3)) (.var 4))))
        (.times (.var 0) (.var 6))) :=
      (Deriv.symmE (hass1.transE hass2)).transE heq
    have hX0 : Deriv Δ (Formula.eq
        (.plus (.var 0) (.plus (.times (.var 0) (.var 3)) (.var 4))) .zero) :=
      Deriv.impE (Deriv.allE .zero (Deriv.allE
        (.plus (.var 0) (.plus (.times (.var 0) (.var 3)) (.var 4)))
        (Deriv.allE (.times (.var 0) (.var 6)) (Deriv.wkNil _ cancelAddDeriv)
          (substOK_of_forall (by decide))) (substOK_of_forall (by decide)))
        (substOK_of_forall (by decide)))
        (hform.transE (Deriv.symmE (Deriv.allE (.times (.var 0) (.var 6))
          (Deriv.wkNil _ plusZeroDeriv) (substOK_of_forall (by decide)))))
    have hcs0 : Deriv Δ (Formula.eq (.plus (.times (.var 0) (.var 3)) (.var 4)) .zero) :=
      Deriv.impE (Deriv.allE (.plus (.times (.var 0) (.var 3)) (.var 4))
        (Deriv.allE (.var 0) (Deriv.wkNil _ addEqZeroDeriv)
          (substOK_of_forall (by decide))) (substOK_of_forall (by decide))) hX0
    have hc0 : Deriv Δ (Formula.eq (.var 4) .zero) :=
      Deriv.impE (Deriv.allE (.var 4) (Deriv.allE (.times (.var 0) (.var 3))
        (Deriv.wkNil _ addEqZeroDeriv) (substOK_of_forall (by decide)))
        (substOK_of_forall (by decide))) hcs0
    refine Deriv.exI .zero ?_ (substOK_numeral 0 _)
    exact (by simpa only [dvdT, Formula.subst, Term.subst] using
      hc0.transE (Deriv.symmE (Deriv.allE (.var 0) (Deriv.wkNil _ timesZeroDeriv)
        (substOK_of_forall (by decide)))))

/-! ## Certification -/

theorem distrib_realized (ρ : ℕ → ℕ) {n : ℕ} (hn : derivBound distribDeriv ≤ n) :
    MR ρ (.all 0 (.all 1 (.all 2 distribEq))) n (extract distribDeriv ρ [] n) :=
  soundness distribDeriv ρ [] trivial n hn

theorem dvdAdd_realized (ρ : ℕ → ℕ) {n : ℕ} (hn : derivBound dvdAddDeriv ≤ n) :
    MR ρ (.all 0 (.all 1 (.all 2
      ((dvdT 3 (.var 0) (.var 1)).imp ((dvdT 4 (.var 0) (.var 2)).imp
        (dvdT 5 (.var 0) (.plus (.var 1) (.var 2)))))))) n
      (extract dvdAddDeriv ρ [] n) :=
  soundness dvdAddDeriv ρ [] trivial n hn

theorem dvdSub_realized (ρ : ℕ → ℕ) {n : ℕ} (hn : derivBound dvdSubDeriv ≤ n) :
    MR ρ (.all 0 (.all 1 (.all 4
      ((dvdT 5 (.var 0) (.var 1)).imp ((dvdT 6 (.var 0) (.plus (.var 1) (.var 4))).imp
        (dvdT 7 (.var 0) (.var 4))))))) n (extract dvdSubDeriv ρ [] n) :=
  soundness dvdSubDeriv ρ [] trivial n hn

theorem distrib_extract_continuous (ρ : ℕ → ℕ) :
    Continuous2 (extract distribDeriv ρ [] 1) :=
  extract_continuous distribDeriv ρ

theorem dvdSub_extract_continuous (ρ : ℕ → ℕ) :
    Continuous2 (extract dvdSubDeriv ρ [] 1) :=
  extract_continuous dvdSubDeriv ρ

theorem dvdAdd_extract_continuous (ρ : ℕ → ℕ) :
    Continuous2 (extract dvdAddDeriv ρ [] 1) :=
  extract_continuous dvdAddDeriv ρ

#print axioms distrib_realized
#print axioms dvdAdd_realized
#print axioms dvdSub_realized
#print axioms distrib_extract_continuous
#print axioms dvdAdd_extract_continuous
#print axioms dvdSub_extract_continuous

end Realizability
