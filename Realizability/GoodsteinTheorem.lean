/-
# Phase D2: Goodstein's theorem, inside the fragment

    ⊢ ∀m. ∃t. good(m, t) = 0

as a closed derivation of the fragment — the genuine universally
quantified statement, not an instance schema and not a bounded version.

## The argument

Transfinite induction (`tiEps0`) along `≺`, on the formula

    φ(x)  :=  ∀s. ord(s+2, good(m, s)) = x  →  ∃t. good(m, t) = 0

with `m` a *parameter* (universally quantified only at the very end).
Read φ(x) as "every state of the sequence from `m` whose ordinal is `x`
eventually reaches `0`".  Progressiveness: fix `x`, assume φ(y) for every
`y ≺ x`, and let `s` be a state with ordinal `x`.  Either `good(m,s) = 0`
— and `t := s` witnesses the conclusion — or it is not, and then the
step's ordinal `ord(s+3, good(m,s+1))` is `≺ x`, so the induction
hypothesis at that ordinal, instantiated at the state `s+1`, gives the
witness.  The conclusion `∀x. φ(x)` is then instantiated at the ordinal
of the *initial* state, whose hypothesis is `ord(2, good(m,0)) = itself`,
i.e. reflexivity.

## The one place substitution bites (a design point worth flagging)

The fragment's substitution is naive, with `SubstOK` forbidding capture
outright rather than renaming.  The step above wants to instantiate the
induction hypothesis `∀y. y ≺ x → φ(y)` at the term
`ord(s+3, good(m,s+1))`, which mentions `s` — and `s` is bound in φ.
That is a *genuine* capture, not a spurious side condition: the
substituted occurrence sits inside φ's own `∀s`.

The standard fix is capture-avoiding substitution (α-renaming).  Instead,
this derivation **names the ordinal**: it proves

    ∀z. (z = ord(s+3, good(m,s+1))) → ∃t. good(m,t) = 0

— where the induction hypothesis is instantiated at the *variable* `z`,
which captures nothing — and then instantiates that at the term itself,
with `eqRefl`.  The instantiation of a `∀` at a term happens where the
term's variables are free, and the instantiation at a variable happens
where capture cannot occur.  This is a general technique for
naive-substitution calculi, and it costs one extra `∀` in the derivation
and nothing in the extract's structure.

## What is imported rather than derived

The descent used below — bump the base, subtract one, and the ordinal
strictly decreases — was an imported axiom schema in D2 and is **derived**
since D5 (`OrdinalDescent.lean`), from three separate properties of the
ordinal assignment.  What the fragment still imports is those three, none
of which mentions the Goodstein sequence; see that module's header for the
exact accounting of what remains metatheoretic.  Everything here — the
case split, the gluing of `goodSucc` with the descent, the induction
itself, and the extraction of the witness — is the fragment's own.
-/
import Realizability.Exists
import Realizability.OrdinalDescent

namespace Realizability

open ContinuousFunctionals

/-! ## The formulas

Variable convention: `1` is the ordinal `x`, `2` the start value `m`, `3`
the step counter `s`, `4` the existential witness `t`, `5` both the
transfinite-induction binder `y` and the naming variable `z` (they never
occur together, and reusing the name is what keeps the `allE` at `var 5`
capture-free). -/

/-- The conclusion, for the parameter `m`: `∃t. good(m, t) = 0`. -/
abbrev goodTerminates : Formula :=
  .ex 4 (Formula.eq (.good (.var 2) (.var 4)) .zero)

/-- The induction formula `φ(x)`: every state of the sequence whose
ordinal is `x` terminates. -/
abbrev goodIndFormula : Formula :=
  .all 3
    ((Formula.eq (.ord (.succ (.succ (.var 3))) (.good (.var 2) (.var 3)))
      (.var 1)).imp goodTerminates)

/-- The ordinal of the *next* state — the term the induction hypothesis is
applied at. -/
abbrev ordNext : Term :=
  .ord (.succ (.succ (.succ (.var 3)))) (.good (.var 2) (.succ (.var 3)))

/-- The progressiveness hypothesis `∀y. y ≺ x → φ(y)`. -/
abbrev hypH : Formula :=
  .all 5 ((Formula.eq (.prec (.var 5) (.var 1)) (.succ .zero)).imp
    (goodIndFormula.subst 1 (.var 5)))

/-- The state hypothesis `ord(s+2, good(m,s)) = x`. -/
abbrev hypE : Formula :=
  .eq (.ord (.succ (.succ (.var 3))) (.good (.var 2) (.var 3))) (.var 1)

/-- The case hypothesis `good(m,s) ≠ 0`. -/
abbrev hypNE : Formula := (Formula.eq (.good (.var 2) (.var 3)) .zero).neg

/-! ## The step: the ordinal really descends

`ordDescent` gives the descent for `pred (bump (s+2) (good m s))`;
`goodSucc` says that term *is* `good m (s+1)`; and the state hypothesis
`E` rewrites the right-hand side to `x`.  Gluing those is the fragment's
own work. -/

/-- Inside the fragment: from `good(m,s) ≠ 0` and `ord(s+2,good(m,s)) = x`,
the next state's ordinal is `≺ x`. -/
def descentDeriv : Deriv [hypNE, hypE, hypH]
    (Formula.eq (.prec ordNext (.var 1)) (.succ .zero)) := by
  have d1 : Deriv [hypNE, hypE, hypH]
      (Formula.eq (.prec
        (.ord (.succ (.succ (.succ (.var 3))))
          (.pred (.bump (.succ (.succ (.var 3))) (.good (.var 2) (.var 3)))))
        (.ord (.succ (.succ (.var 3))) (.good (.var 2) (.var 3))))
        (.succ .zero)) :=
    .impE (.ordDescent (.var 3) (.good (.var 2) (.var 3)))
      (show Deriv [hypNE, hypE, hypH] hypNE from .ax)
  have d2 : Deriv [hypNE, hypE, hypH]
      (Formula.eq (.pred (.bump (.succ (.succ (.var 3))) (.good (.var 2) (.var 3))))
        (.good (.var 2) (.succ (.var 3)))) :=
    Deriv.symmE (.goodSucc (.var 2) (.var 3))
  have d3 : Deriv [hypNE, hypE, hypH]
      (Formula.eq (.ord (.succ (.succ (.succ (.var 3))))
          (.pred (.bump (.succ (.succ (.var 3))) (.good (.var 2) (.var 3)))))
        ordNext) :=
    Deriv.congOrdE (.eqRefl _) d2
  have hE : Deriv [hypNE, hypE, hypH] hypE := .wk .ax
  have d4 : Deriv [hypNE, hypE, hypH]
      (Formula.eq (.prec
          (.ord (.succ (.succ (.succ (.var 3))))
            (.pred (.bump (.succ (.succ (.var 3))) (.good (.var 2) (.var 3)))))
          (.ord (.succ (.succ (.var 3))) (.good (.var 2) (.var 3))))
        (.prec ordNext (.var 1))) :=
    Deriv.congPrecE d3 hE
  exact (Deriv.symmE d4).transE d1

/-- The **naming** step: the induction hypothesis, applied at a variable
standing for the next state's ordinal.  This is the derivation described
in the header — instantiating `∀y` at `var 5` cannot capture, and the
equation `var 5 = ordNext` is what transfers the descent. -/
def namedIHDeriv : Deriv [hypNE, hypE, hypH]
    (Formula.all 5 ((Formula.eq (.var 5) ordNext).imp goodTerminates)) := by
  refine Deriv.allI (Deriv.impI ?_) (by decide +kernel)
  -- context: [z = ordNext, good m s ≠ 0, state hypothesis, IH]
  have hH : Deriv [Formula.eq (.var 5) ordNext, hypNE, hypE, hypH] hypH :=
    .wk (.wk (.wk .ax))
  have hHN : Deriv [Formula.eq (.var 5) ordNext, hypNE, hypE, hypH]
      (Formula.eq (.var 5) ordNext) := .ax
  -- the descent, transported along the naming equation
  have hdesc : Deriv [Formula.eq (.var 5) ordNext, hypNE, hypE, hypH]
      (Formula.eq (.prec ordNext (.var 1)) (.succ .zero)) := .wk descentDeriv
  have hprec : Deriv [Formula.eq (.var 5) ordNext, hypNE, hypE, hypH]
      (Formula.eq (.prec (.var 5) (.var 1)) (.succ .zero)) :=
    (Deriv.congPrecE hHN (.eqRefl (.var 1))).transE hdesc
  -- the induction hypothesis at `var 5`
  have hinst : Deriv [Formula.eq (.var 5) ordNext, hypNE, hypE, hypH]
      ((Formula.eq (.prec (.var 5) (.var 1)) (.succ .zero)).imp
        (goodIndFormula.subst 1 (.var 5))) :=
    Deriv.allE (.var 5) hH (by decide +kernel)
  have hphi : Deriv [Formula.eq (.var 5) ordNext, hypNE, hypE, hypH]
      (goodIndFormula.subst 1 (.var 5)) := .impE hinst hprec
  -- instantiate it at the *next* state `s + 1`
  have hstate : Deriv [Formula.eq (.var 5) ordNext, hypNE, hypE, hypH]
      ((Formula.eq ordNext (.var 5)).imp goodTerminates) :=
    Deriv.allE (.succ (.var 3)) hphi (by decide +kernel)
  exact .impE hstate (Deriv.symmE hHN)

/-- The step case: if the sequence has not yet reached `0`, the induction
hypothesis at the next state's ordinal supplies the witness. -/
def stepBranch : Deriv [hypNE, hypE, hypH] goodTerminates :=
  .impE (Deriv.allE ordNext namedIHDeriv (by decide +kernel)) (.eqRefl ordNext)

/-- **Progressiveness of φ** — the premise of `tiEps0`. -/
def goodProgressive :
    Deriv [] (Formula.all 1
      ((Formula.all 5 ((Formula.eq (.prec (.var 5) (.var 1)) (.succ .zero)).imp
        (goodIndFormula.subst 1 (.var 5)))).imp goodIndFormula)) := by
  refine Deriv.allI (Deriv.impI (Deriv.allI (Deriv.impI ?_) (by decide +kernel)))
    (by decide +kernel)
  -- context: [state hypothesis, IH]; goal: `∃t. good(m,t) = 0`
  refine Deriv.orE (Deriv.eqDec (.good (.var 2) (.var 3)) .zero) ?_ ?_
  · -- the sequence is already at `0`: the witness is `s` itself
    exact Deriv.exI (.var 3) .ax (by decide +kernel)
  · exact stepBranch

/-- **Goodstein's theorem, for the parameter `m`**: `∃t. good(m,t) = 0`,
by transfinite induction along `≺` instantiated at the ordinal of the
initial state. -/
def goodTerminatesDeriv : Deriv [] goodTerminates := by
  have hall : Deriv [] (Formula.all 1 goodIndFormula) :=
    Deriv.tiEps0 (x := 1) (y := 5) goodProgressive (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  have hinst : Deriv [] (goodIndFormula.subst 1
      (.ord (.succ (.succ .zero)) (.good (.var 2) .zero))) :=
    Deriv.allE _ hall (by decide +kernel)
  have hstate : Deriv []
      ((Formula.eq (.ord (.succ (.succ .zero)) (.good (.var 2) .zero))
        (.ord (.succ (.succ .zero)) (.good (.var 2) .zero))).imp
        goodTerminates) :=
    Deriv.allE .zero hinst (by decide +kernel)
  exact .impE hstate (.eqRefl _)

/-- **Goodstein's theorem**: `⊢ ∀m. ∃t. good(m, t) = 0`.

The genuine statement — universally quantified over the start value,
existentially over the number of steps, with no bound on either.  Every
`good`, `bump`, `pred`, `ord` and `prec` in it is the fragment's own
symbol, evaluated by the value-level functions cross-checked against
`WilliamAngus/Goodstein` in Phase B. -/
def goodsteinTheorem : Deriv [] (Formula.all 2 goodTerminates) :=
  Deriv.allI goodTerminatesDeriv (by decide +kernel)

end Realizability
