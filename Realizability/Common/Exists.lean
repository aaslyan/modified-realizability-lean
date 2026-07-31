/-
# Phase D0: the existential quantifier

Goodstein's theorem is `∀m ∃s. good(m, s) = 0`.  Before this phase the
fragment could not *state* it: `Formula` had `∧ ∨ → ⊥` over equations and
a single `∀` binder, and no `∃` at all.  This module is D0's checkpoint —
the machinery lives in the files it belongs to (one case each in
`Formula`, `MR`, both transports, the tracking relation, `extract`,
`derivBound`, `soundness`, `extract_tracked`), and what is here is the
first genuinely existential theorem of the fragment, with its realizer
certified.

## The design decision (D0's flagged question)

**`∃` needed two new rules but no new devices.**  Its realizability
clause is

    MR ρ (∃y φ) n x  ↔  MR ρ[y ↦ fstPT x (defaultPT n)] φ n (sndPT x)

— the first component, read at the canonical point, *is* the witness, and
the second realizes `φ` there.  That is literally the `∨` clause with the
two-valued tag generalized to a numeral, so:

* extraction reuses `pairPT`/`fstPT`/`sndPT`: `exIC` is `orI₁C` with the
  witness numeral in place of the constant tag `0`, and `exEC` is `orEC`
  with the tag *split* replaced by passing the witness into the
  environment.  No second pairing mechanism was introduced, as the brief
  required;
* the transports get one case each, shaped like `∨`'s (`liftR_ex`,
  `dropR_ex`), and tracking gets `exIC_tracked`/`exEC_tracked`, which are
  `orI₁C_tracked`/`orEC_tracked` with the case split deleted;
* **`∃` costs no ambient level**: `lvl (∃y φ) = lvl φ`, unlike `→` and
  `∀`.  The reason is worth recording because it is the invariant behind
  the whole level discipline: binders that *consume* realizers cost a
  level, binders that merely *package* them do not.  So no `derivBound`
  in the development grew.

The one place `∃` is not just `∨` is elimination's side conditions: the
witness must not escape its scope, so `exE` carries `FreshIn x Γ` and
`¬ ψ.FreeIn x`.  In the soundness proof these are exactly what let
`CtxR_congr` carry the context across the environment update (the witness
is written into the environment at `x`) and `MR_congr` carry the
conclusion back.
-/
import Realizability.Theorems.Goodstein.TransfiniteInduction

namespace Realizability

open ContinuousFunctionals

/-- Numerals are closed. -/
@[simp] theorem numeral_vars : ∀ n : ℕ, (numeral n).vars = []
  | 0 => rfl
  | n + 1 => numeral_vars n

/-- Substituting into a formula whose substituted term is closed is
always capture-safe. -/
theorem substOK_numeral (n : ℕ) (φ : Formula) :
    Formula.SubstOK (numeral n) φ := by
  intro y hy
  rw [numeral_vars] at hy
  exact absurd hy List.not_mem_nil

/-! ## The first existential theorem of the fragment

`G(3)` reaches `0` at step `5` (Phase B: `3, 3, 3, 2, 1, 0`), so the
fragment can prove `∃s. good(3, s) = 0` outright — by `exI` at the
witness `5̂`, over Phase B's numeral computation `goodComputeDeriv`.  This
is the concrete `∃` that D2 has to produce *uniformly in the start
value*, and it is worth having both to exercise the new rule and to make
the difference visible: here the witness is supplied by hand, there it
comes out of the transfinite recursion. -/

/-- `⊢ ∃s. good(3, s) = 0` — witness `5`. -/
def goodThreeExDeriv :
    Deriv [] (.ex 1 (.eq (.good (numeral 3) (.var 1)) .zero)) := by
  refine Deriv.exI (numeral 5) ?_ (substOK_numeral 5 _)
  show Deriv []
    (.eq (.good (Term.subst 1 (numeral 5) (numeral 3)) (numeral 5)) .zero)
  rw [numeral_subst]
  exact goodComputeDeriv 3 5

/-- And `∃`-elimination is usable: from `∃s. good(3,s) = 0` the fragment
re-derives the same statement (a round trip through `exE`, so that the
elimination rule is exercised too — its side conditions are the freshness
of the bound variable in the empty context and its non-occurrence in the
conclusion). -/
def goodThreeExRoundTrip :
    Deriv [] (.ex 1 (.eq (.good (numeral 3) (.var 1)) .zero)) :=
  .exE goodThreeExDeriv (.exI (.var 1) .ax (by
      intro y hy
      simp only [Term.vars, List.mem_singleton] at hy
      subst hy
      simp [Formula.binders]))
    (fun _ h => absurd h List.not_mem_nil)
    (by simp [Formula.FreeIn, Term.vars, numeral_vars])

/-! ## Certification -/

/-- The extracted realizer of `∃s. good(3,s) = 0` realizes it: the pair
`⟨witness, payload⟩` at every ambient above the bound. -/
theorem good_three_ex_realized (ρ : ℕ → ℕ) {n : ℕ}
    (hn : derivBound goodThreeExDeriv ≤ n) :
    MR ρ (.ex 1 (.eq (.good (numeral 3) (.var 1)) .zero)) n
      (extract goodThreeExDeriv ρ [] n) :=
  soundness goodThreeExDeriv ρ [] trivial n hn

/-- The `exE` round trip realizes it too — the elimination rule's
soundness case, exercised. -/
theorem good_three_ex_round_trip_realized (ρ : ℕ → ℕ) {n : ℕ}
    (hn : derivBound goodThreeExRoundTrip ≤ n) :
    MR ρ (.ex 1 (.eq (.good (numeral 3) (.var 1)) .zero)) n
      (extract goodThreeExRoundTrip ρ [] n) :=
  soundness goodThreeExRoundTrip ρ [] trivial n hn

/-- Generic continuity covers the two new rules with no modification. -/
theorem good_three_ex_extract_continuous (ρ : ℕ → ℕ) :
    Continuous2 (extract goodThreeExDeriv ρ [] 1) :=
  extract_continuous goodThreeExDeriv ρ

theorem good_three_ex_round_trip_extract_continuous (ρ : ℕ → ℕ) :
    Continuous2 (extract goodThreeExRoundTrip ρ [] 1) :=
  extract_continuous goodThreeExRoundTrip ρ

/-- The witness is *readable off* the realizer: the first component at the
canonical point is the numeral `5`.  This is what makes modified
realizability of `∃` worth having — the realizer carries the witness, so
extraction yields the stopping time and not merely a proof that one
exists.  (Here it is the witness supplied by hand; in
`GoodsteinTheorem.lean` it is the one the recursor computes.) -/
theorem good_three_ex_witness (ρ : ℕ → ℕ) (n : ℕ) :
    fstPT (extract goodThreeExDeriv ρ [] n) (defaultPT n) = 5 := by
  rw [show (5 : ℕ) = (numeral 5).eval ρ from (numeral_eval ρ 5).symm]
  exact exIC_witness _ _ n

#print axioms good_three_ex_realized
#print axioms good_three_ex_round_trip_realized
#print axioms good_three_ex_extract_continuous
#print axioms good_three_ex_round_trip_extract_continuous
#print axioms good_three_ex_witness

end Realizability
