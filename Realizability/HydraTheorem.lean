/-
# Phase H5: Hercules wins, inside the fragment

    ⊢ ∀h. ∃t. hydra(h, t) = 0

as a closed derivation of the fragment — every hydra dies, for every
starting tree, with no bound on the number of moves and no restriction on
the shape of the tree.  This is the Kirby–Paris theorem, in the same
sense that Phase D2's result is Goodstein's theorem: the statement is the
fragment's own, the reasoning is the fragment's own, and one property of
the ordinal assignment is imported (Phase H4's `hordCutLt`).

## The argument

Transfinite induction (`tiEps0`) along `≺`, on the formula

    φ(x)  :=  ∀s. hord(hydra(h, s)) = x  →  ∃t. hydra(h, t) = 0

with `h` a *parameter*, universally quantified only at the very end.
Read φ(x) as "every state of the battle from `h` whose ordinal is `x`
eventually reaches the dead hydra".  Progressiveness: fix `x`, assume
φ(y) for every `y ≺ x`, and let `s` be a state with ordinal `x`.  Either
`hydra(h,s) = 0` — the hydra is already dead and `t := s` witnesses the
conclusion — or it is not, and then the *next* state's ordinal
`hord(hydra(h,s+1))` is `≺ x`, so the induction hypothesis at that
ordinal, instantiated at the state `s+1`, supplies the witness.  The
conclusion `∀x φ(x)` is instantiated at the ordinal of the initial state,
whose hypothesis is reflexivity.

Structurally this is `GoodsteinTheorem.lean` line for line, including the
**naming** step that works around naive substitution (`namedIHDeriv`
there, `hydraNamedIHDeriv` here): the induction hypothesis cannot be
instantiated directly at `hord(hydra(h, s+1))`, because that term mentions
`s`, which φ binds.  So the derivation proves `∀z. z = hord(hydra(h,s+1))
→ …` first, instantiating the hypothesis at the *variable* `z`, and only
then instantiates that at the term.

The one Hydra-specific difference is where the descent comes from.  In
Goodstein it was assembled from three schemas about `ord`, `bump` and
`pred`; here it is `hordCutLt` glued to the battle's recursion equation
`hydraSucc` by congruence of `hord` — the fragment's own three-line
`hydraDescentDeriv`.  Nothing about the *number of regrown copies* is
ever used: the schema quantifies over it, so the derivation never
inspects how far the hydra grew.  That is the whole point of the game,
and it is visible in the proof term.

## What this does and does not claim

**Does**: the fragment derives termination of the Kirby–Paris battle from
transfinite induction up to `ε₀`, with the move, the battle and the
ordinal assignment all as its own symbols evaluated by H1–H3's verified
functions, and with `= 0` meaning "the tree is a bare head" by the
bijection of H1.

**Does not**: prove that Peano arithmetic *cannot* derive it — the
independence half of Kirby–Paris is not formalized here, and no claim
about it is made.  Nor is `hordCutLt` internalized; see
`HydraFragment.lean` for that accounting.
-/
import Realizability.HydraFragment

namespace Realizability

open ContinuousFunctionals

/-! ## The formulas

Variable convention (identical to `GoodsteinTheorem.lean`): `1` is the
ordinal `x`, `2` the starting hydra `h`, `3` the move counter `s`, `4` the
existential witness `t`, `5` both the transfinite-induction binder `y` and
the naming variable `z`. -/

/-- The induction formula `φ(x)`: every state of the battle whose ordinal
is `x` reaches the dead hydra. -/
abbrev hydraIndFormula : Formula :=
  .all 3
    ((Formula.eq (.hord (.hydra (.var 2) (.var 3))) (.var 1)).imp hydraTerminates)

/-- The ordinal of the *next* state — the term the induction hypothesis is
applied at. -/
abbrev hordNext : Term := .hord (.hydra (.var 2) (.succ (.var 3)))

/-- The progressiveness hypothesis `∀y. y ≺ x → φ(y)`. -/
abbrev hydraHypH : Formula :=
  .all 5 ((Formula.eq (.prec (.var 5) (.var 1)) (.succ .zero)).imp
    (hydraIndFormula.subst 1 (.var 5)))

/-- The state hypothesis `hord(hydra(h,s)) = x`. -/
abbrev hydraHypE : Formula :=
  .eq (.hord (.hydra (.var 2) (.var 3))) (.var 1)

/-- The case hypothesis `hydra(h,s) ≠ 0` — the hydra is still alive. -/
abbrev hydraHypNE : Formula :=
  (Formula.eq (.hydra (.var 2) (.var 3)) .zero).neg

/-! ## The step: the ordinal really descends

`hordCutLt` gives the descent for `hcut(s+1, hydra(h,s))`; `hydraSucc`
says that term *is* `hydra(h,s+1)`; and the state hypothesis rewrites the
right-hand side to `x`.  Gluing those is the fragment's own work. -/

/-- Inside the fragment: from `hydra(h,s) ≠ 0` and `hord(hydra(h,s)) = x`,
the next state's ordinal is `≺ x`. -/
def hydraDescentDeriv : Deriv [hydraHypNE, hydraHypE, hydraHypH]
    (Formula.eq (.prec hordNext (.var 1)) (.succ .zero)) := by
  -- the imported descent, at this move and this state
  have d1 : Deriv [hydraHypNE, hydraHypE, hydraHypH]
      (Formula.eq (.prec
        (.hord (.hcut (.succ (.var 3)) (.hydra (.var 2) (.var 3))))
        (.hord (.hydra (.var 2) (.var 3))))
        (.succ .zero)) :=
    .impE (.hordCutLt (.succ (.var 3)) (.hydra (.var 2) (.var 3)))
      (show Deriv [hydraHypNE, hydraHypE, hydraHypH] hydraHypNE from .ax)
  -- the battle's recursion equation, read backwards
  have d2 : Deriv [hydraHypNE, hydraHypE, hydraHypH]
      (Formula.eq (.hcut (.succ (.var 3)) (.hydra (.var 2) (.var 3)))
        (.hydra (.var 2) (.succ (.var 3)))) :=
    Deriv.symmE (.hydraSucc (.var 2) (.var 3))
  have d3 : Deriv [hydraHypNE, hydraHypE, hydraHypH]
      (Formula.eq (.hord (.hcut (.succ (.var 3)) (.hydra (.var 2) (.var 3))))
        hordNext) :=
    Deriv.congHordE d2
  have hE : Deriv [hydraHypNE, hydraHypE, hydraHypH] hydraHypE := .wk .ax
  have d4 : Deriv [hydraHypNE, hydraHypE, hydraHypH]
      (Formula.eq (.prec
          (.hord (.hcut (.succ (.var 3)) (.hydra (.var 2) (.var 3))))
          (.hord (.hydra (.var 2) (.var 3))))
        (.prec hordNext (.var 1))) :=
    Deriv.congPrecE d3 hE
  exact (Deriv.symmE d4).transE d1

/-- The **naming** step: the induction hypothesis, applied at a variable
standing for the next state's ordinal.  Instantiating `∀y` at `var 5`
cannot capture, and the equation `var 5 = hordNext` is what transfers the
descent. -/
def hydraNamedIHDeriv : Deriv [hydraHypNE, hydraHypE, hydraHypH]
    (Formula.all 5 ((Formula.eq (.var 5) hordNext).imp hydraTerminates)) := by
  refine Deriv.allI (Deriv.impI ?_) (by decide +kernel)
  -- context: [z = hordNext, hydra alive, state hypothesis, IH]
  have hH : Deriv [Formula.eq (.var 5) hordNext, hydraHypNE, hydraHypE,
      hydraHypH] hydraHypH := .wk (.wk (.wk .ax))
  have hHN : Deriv [Formula.eq (.var 5) hordNext, hydraHypNE, hydraHypE,
      hydraHypH] (Formula.eq (.var 5) hordNext) := .ax
  -- the descent, transported along the naming equation
  have hdesc : Deriv [Formula.eq (.var 5) hordNext, hydraHypNE, hydraHypE,
      hydraHypH] (Formula.eq (.prec hordNext (.var 1)) (.succ .zero)) :=
    .wk hydraDescentDeriv
  have hprec : Deriv [Formula.eq (.var 5) hordNext, hydraHypNE, hydraHypE,
      hydraHypH] (Formula.eq (.prec (.var 5) (.var 1)) (.succ .zero)) :=
    (Deriv.congPrecE hHN (.eqRefl (.var 1))).transE hdesc
  -- the induction hypothesis at `var 5`
  have hinst : Deriv [Formula.eq (.var 5) hordNext, hydraHypNE, hydraHypE,
      hydraHypH]
      ((Formula.eq (.prec (.var 5) (.var 1)) (.succ .zero)).imp
        (hydraIndFormula.subst 1 (.var 5))) :=
    Deriv.allE (.var 5) hH (by decide +kernel)
  have hphi : Deriv [Formula.eq (.var 5) hordNext, hydraHypNE, hydraHypE,
      hydraHypH] (hydraIndFormula.subst 1 (.var 5)) := .impE hinst hprec
  -- instantiate it at the *next* state `s + 1`
  have hstate : Deriv [Formula.eq (.var 5) hordNext, hydraHypNE, hydraHypE,
      hydraHypH] ((Formula.eq hordNext (.var 5)).imp hydraTerminates) :=
    Deriv.allE (.succ (.var 3)) hphi (by decide +kernel)
  exact .impE hstate (Deriv.symmE hHN)

/-- The step case: the hydra is still alive, so the induction hypothesis
at the next state's ordinal supplies the witness. -/
def hydraStepBranch : Deriv [hydraHypNE, hydraHypE, hydraHypH] hydraTerminates :=
  .impE (Deriv.allE hordNext hydraNamedIHDeriv (by decide +kernel))
    (.eqRefl hordNext)

/-- **Progressiveness of φ** — the premise of `tiEps0`. -/
def hydraProgressive :
    Deriv [] (Formula.all 1
      ((Formula.all 5 ((Formula.eq (.prec (.var 5) (.var 1)) (.succ .zero)).imp
        (hydraIndFormula.subst 1 (.var 5)))).imp hydraIndFormula)) := by
  refine Deriv.allI (Deriv.impI (Deriv.allI (Deriv.impI ?_) (by decide +kernel)))
    (by decide +kernel)
  -- context: [state hypothesis, IH]; goal: `∃t. hydra(h,t) = 0`
  refine Deriv.orE (Deriv.eqDec (.hydra (.var 2) (.var 3)) .zero) ?_ ?_
  · -- the hydra is already dead: the witness is `s` itself
    exact Deriv.exI (.var 3) .ax (by decide +kernel)
  · exact hydraStepBranch

/-- **Termination of the battle, for the parameter `h`**:
`∃t. hydra(h,t) = 0`, by transfinite induction along `≺` instantiated at
the ordinal of the initial hydra. -/
def hydraTerminatesDeriv : Deriv [] hydraTerminates := by
  have hall : Deriv [] (Formula.all 1 hydraIndFormula) :=
    Deriv.tiEps0 (x := 1) (y := 5) hydraProgressive (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
  have hinst : Deriv []
      (hydraIndFormula.subst 1 (.hord (.hydra (.var 2) .zero))) :=
    Deriv.allE _ hall (by decide +kernel)
  have hstate : Deriv []
      ((Formula.eq (.hord (.hydra (.var 2) .zero))
        (.hord (.hydra (.var 2) .zero))).imp hydraTerminates) :=
    Deriv.allE .zero hinst (by decide +kernel)
  exact .impE hstate (.eqRefl _)

/-- **Hercules wins**: `⊢ ∀h. ∃t. hydra(h, t) = 0`.

Every hydra dies.  The quantifier is over *all* natural numbers, which by
H1's bijection is all finite rooted trees; the witness is unbounded; the
number of heads regrown at each move is whatever the move symbol's
argument says, and the derivation never looks at it. -/
def hydraTheorem : Deriv [] hydraGoal :=
  Deriv.allI hydraTerminatesDeriv (by decide +kernel)

/-! ## Certification

The theorem is a closed derivation, so soundness and generic continuity
apply with no new argument. -/

/-- The theorem realizes what it says. -/
theorem hydra_theorem_realized (ρ : ℕ → ℕ) {m : ℕ}
    (hm : derivBound hydraTheorem ≤ m) :
    MR ρ hydraGoal m (extract hydraTheorem ρ [] m) :=
  soundness hydraTheorem ρ [] trivial m hm

/-- And its type-2 extract is continuous. -/
theorem hydra_theorem_extract_continuous (ρ : ℕ → ℕ) :
    Continuous2 (extract hydraTheorem ρ [] 1) :=
  extract_continuous hydraTheorem ρ

#print axioms hydraTheorem
#print axioms hydra_theorem_realized
#print axioms hydra_theorem_extract_continuous

end Realizability
