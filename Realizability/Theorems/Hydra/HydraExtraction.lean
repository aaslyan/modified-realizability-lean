/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import Realizability.Theorems.Hydra.HydraTheorem
import Realizability.Core.CollapseDemo

/-!
# Phase H6: the extracted Hydra program

`hydraTheorem` (Phase H5) is a closed derivation of `∀h ∃t. hydra(h,t) = 0`,
and modified realizability turns it into a program, because the realizer
of an existential **carries its witness**.  This module reads that witness
off and certifies it three ways, exactly as Phase D3 did for Goodstein:

* `hydraBattleLength_spec` — the extracted number really is a battle
  length: `hydraSeqN h (hydraBattleLength h) = 0`, for **every** hydra
  code `h`.  Proved from `soundness`, not by computation, so it holds at
  trees no evaluator will ever reach;
* `hydra_extract_continuous` — the extract is `Continuous2`, by the
  generic continuity theorem, with no per-derivation certificate;
* `hydraRealizesCtQ` — hence it has a class in `CtQ 2`, the extensional
  collapse of the Kleene–Kreisel development.

And it runs, at the small trees: see the `#eval`s at the end.

## The performance limit, stated as in D3/D4 and for the same reason

`hydraBattleLength 2` does not finish (no output at 600 s).  The answer is
not astronomical — it is `3`, and `hydraSeqN` computes the battle
`2 → 3 → 1 → 0` instantly — so this is a limitation of *evaluating the
extract*, not of the mathematics.  The cause is the one Phase D4
diagnosed and did not fix: every recursive value in `tiRecC`'s output is
wrapped in two `dropR` transports, and `app₁`/`abs₁` duplicate their
argument at each application, so the realizer re-evaluates its own
recursive calls exponentially often in the number of moves.  Nothing
memoizes.  The Hydra layer inherits that unchanged; it adds no new
bottleneck of its own.

The certified content is unaffected: `hydraBattleLength_spec` holds at
every `h`, including the ones evaluation cannot reach.
-/

namespace Realizability

open ContinuousFunctionals

/-! **The statement, spelled out** — no abbreviations, checked at every
build, so that what is proved cannot drift behind a definition:
`⊢ ∀h ∃t. hydra(h, t) = 0`. -/
#check (hydraTheorem :
  Deriv [] (Formula.all 2 (Formula.ex 4
    (Formula.eq (Term.hydra (Term.var 2) (Term.var 4)) Term.zero))))

/-- The bound above which the extracted family realizes the theorem — the
same `12` as Goodstein's, since the derivations have the same shape. -/
theorem hydra_derivBound : derivBound hydraTheorem = 12 := rfl

/-- **Soundness at the Hydra theorem**: the extracted family realizes
`∀h ∃t. hydra(h,t) = 0` at every ambient level from 12 up. -/
theorem hydra_realized (ρ : ℕ → ℕ) {n : ℕ} (hn : 12 ≤ n) :
    MR ρ hydraGoal n (extract hydraTheorem ρ [] n) :=
  soundness hydraTheorem ρ [] trivial n (by rw [hydra_derivBound]; exact hn)

/-- **The extracted battle-length function.**  Apply the realizer to the
hydra's code and read the witness component of the existential — the first
component at the canonical point, which is exactly where `exIC` puts it.
Ambient 12 is the derivation's own bound, so this is the realizer *at the
level where it is certified*. -/
def hydraBattleLength (h : ℕ) : ℕ :=
  fstPT (app₁ (extract hydraTheorem (fun _ ↦ 0) [] 12) (natPT 12 h))
    (defaultPT 11)

/-- **The extracted function is correct**, at every hydra: the battle from
the tree coded `h` has reached the bare head after `hydraBattleLength h`
moves.  This is soundness instantiated at the theorem — the realizer's
witness clause *is* this statement — so it needs no computation and holds
far beyond where evaluation could reach. -/
theorem hydraBattleLength_spec (h : ℕ) :
    hydraSeqN h (hydraBattleLength h) = 0 := by
  have hr := hydra_realized (fun _ ↦ 0) (n := 12) (Nat.le_refl 12) h
  have h2 : Term.eval
      (Function.update (Function.update (fun _ ↦ 0) 2 h) 4
        (fstPT (app₁ (extract hydraTheorem (fun _ ↦ 0) [] 12)
          (natPT 12 h)) (defaultPT 11)))
      (.hydra (.var 2) (.var 4))
      = Term.eval
      (Function.update (Function.update (fun _ ↦ 0) 2 h) 4
        (fstPT (app₁ (extract hydraTheorem (fun _ ↦ 0) [] 12)
          (natPT 12 h)) (defaultPT 11))) .zero := hr
  simpa [Term.eval, Function.update, hydraBattleLength] using h2

/-- Generic continuity applies to the theorem's extract with no
modification: `extract_continuous` covers the Hydra schemas like every
other rule. -/
theorem hydra_extract_continuous (ρ : ℕ → ℕ) :
    Continuous2 (extract hydraTheorem ρ [] 1) :=
  extract_continuous hydraTheorem ρ

/-- **The theorem's program, as an element of `CtQ 2`** — the class of its
extracted type-2 realizer in the extensional collapse. -/
noncomputable def hydraRealizesCtQ (ρ : ℕ → ℕ) : CtQ 2 :=
  RealizesCtQ hydraTheorem ρ

/-! ## Running it

The two smallest battles, with the value level as the cross-check:

    code 0  — the bare head, already dead        → 0 moves
    code 1  — a root with one head               → 1 move

Both `#eval`s below return in a few seconds.  Code `2` (the two-deep
chain, whose battle is `2 → 3 → 1 → 0`) does not finish; see the header. -/

/-- The value-level battle agrees with the extracted witness at code `1`
(kernel-checked, independent of the evaluator). -/
theorem hydraSeqN_one_at_one : hydraSeqN 1 1 = 0 := rfl

/-- And the dead hydra is already dead at step `0`. -/
theorem hydraSeqN_zero_at_zero : hydraSeqN 0 0 = 0 := rfl

#eval hydraBattleLength 0
#eval hydraBattleLength 1

#print axioms hydra_realized
#print axioms hydraBattleLength_spec
#print axioms hydra_extract_continuous

end Realizability
