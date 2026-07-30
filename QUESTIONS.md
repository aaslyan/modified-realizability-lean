# Open questions and pending decisions

A running record of decision points I have raised, with options and my
recommendations.  Items get moved to "Resolved" when you answer them.

## Resolved

1. **Which not-yet-proved piece to attack next?**
   *Asked 2026-07-27; answered: "Generic continuity."*
   *Reopened 2026-07-27 after design analysis (sizing concern:
   continuity seemed to need hereditary countability at every ambient —
   the full countability chapter).*
   ***Closed 2026-07-28: generic continuity is proved***
   (`extract_continuous` in `GenericContinuity.lean`), per the brief's
   direction to thread a compositional logical relation through the
   derivation.  The sizing concern dissolved: the invariant is the
   oracle-parameterized continuity relation (`Tracked`), under which
   abstraction closure holds by β-reduction — no associates are
   constructed, so the countability chapter is not needed for this
   theorem.  The finding's residue that *does* stand: associate-level
   abstraction closure remains open and remains the hard core of the
   parent repo's finite-types chapter.  Bonus: the brief's `lvl φ ≤ 1`
   hypothesis proved unnecessary — every closed derivation's extract is
   continuous, so `RealizesCtQ` is now total on closed derivations.

2. **Push `Realizability` to GitHub?**
   *Answered 2026-07-27: pushed to
   `github.com/aaslyan/modified-realizability-lean`.*

3. **Rename the local `ContinuousFunctionals` directory?**
   *Done 2026-07-27: now `/home/aaslyan/kleene-kreisel-lean`; the
   Realizability path dependency and manifest updated, both repos
   rebuilt green.*

6. **Induction axiom (long-term plan).**  *Closed: delivered as Phase 2
   (see STATUS.md), and now exercised on new content by Phase A — the
   four `+`/`×` defining equations are `ind` theorems (five inductions,
   `Arithmetic.lean`).*

7. **Phase A: Option 1 vs Option 2 for `+`/`×`** (the brief delegated
   the choice, to be recorded with rationale).  *Resolved 2026-07-29:
   Option 2, in "mirror recursion" form* — the defining axioms recurse
   on the **first** argument, so all four briefed (second-argument)
   equations are genuine `ind` theorems; the brief's own Option-2
   sketch (second-argument axioms) would have collapsed into Option 1
   with `ind` never firing, and a term-level recursion binder was the
   "deeper syntactic machinery" wall the brief itself flagged.  Full
   rationale in STATUS.md's Phase-A section.  Also settled there: the
   equational-logic kit as per-symbol implication schemas rather than
   a single Leibniz replacement rule.

8. **Phase B: encoding of hereditary base-`k` representations** (the
   brief named this the single most consequential design decision and
   delegated it).  *Resolved 2026-07-29: a representation is a term of
   the fragment's own syntax in one distinguished free variable (the
   base, variable `0`)* — so bumping the base is evaluating the same
   term at `k + 1` (the reference repo's base-replacement `f` made
   definitional), existence is a *derivable* fragment equation
   produced by a certifying evaluator (no axiom about `hrep` exists),
   and uniqueness/canonicity is deferred with an explicit safety
   argument.  One compromise flagged: `bump` enters the fragment by
   its numeral graph (`bumpNum`), since its course-of-values recursion
   through the exponent structure is not a first-order schema.  Full
   rationale in STATUS.md's Phase-B section.

9. **Phase C: how `tiEps0`'s quantifiers range, and whether canonicity
   of notations is load-bearing** (the brief delegated the first and
   demanded a direct answer to the second).  *Resolved 2026-07-29.*
   Quantifiers range over **natural-number codes** of Cantor-normal-form
   trees — forced, since the fragment has one sort and only equations, so
   `y ≺ x` is the equation `prec y x = 1` for a new function symbol.  The
   tempting reuse of Phase B's hereditary base-2 representation as the
   coding was rejected because it *trivializes* the rule (that coding is
   order-isomorphic to `(ℕ, <)`, so `tiEps0` would follow from `ind`).
   And canonicity **is** load-bearing, decisively: on arbitrary notations
   the comparison has an infinite descending chain
   `ω ≻ 1 + ω ≻ 1 + (1 + ω) ≻ …` of terms all denoting `ω`, so the order
   is the comparison conjoined with a normal-form predicate — Phase B's
   deferred `NF` layer, now built.  Full rationale, with the
   machine-checked witnesses, in STATUS.md's Phase-C section.

10. **Phase C: does the recursor need a well-foundedness theorem?**  The
   brief said no (structural recursion on the notation's subterms) and
   asked that the finding be recorded either way.  *Resolved
   2026-07-29: it does* — `≺`-descent is not subterm descent (from `ω^ω`
   one descends to the larger tree `ω^2·2 + ω·2 + 2`), so `Epsilon0.lean`
   proves `oLt_wf` and `tiRecC` is `WellFounded.fix` on it.  The brief's
   philosophical point survives in sharper form: that proof is
   elementary and `Classical`-free (`[propext, Quot.sound]`, strictly
   less than the realization theorems' budget).  Recorded in STATUS.md,
   together with the two things this forced — a hand-rolled pairing
   (Mathlib's `Nat.pair` theory is choice-dependent) and a ban on
   `by_cases` in that module.

11. **The fragment has no `∃`** (item 3½, raised in Phase B, deferred by
   Phase C).  *Resolved 2026-07-29 as Phase D0*: added, and it needed no
   new machinery — its realizability clause is `∨`'s with the tag
   generalized to a numeral, so `exIC`/`exEC` reuse the existing pairing
   devices and `lvl (∃y φ) = lvl φ`.  Goodstein's theorem is now stated
   and proved (`goodsteinTheorem`).  The original item is preserved
   below for the record.

## Open

*(nothing blocking; the roadmap's phases are all delivered.  The
remaining item is engineering, not mathematics.)*

12. **The extracted program is correct but not efficient.**  *Diagnosed
   2026-07-29 in Phase D4 and left unfixed, deliberately.*  The profile:
   at `m = 1` the recursor's body is entered 2377 times at only **two**
   distinct notation codes — 2376 of them at the same code — so the cost
   is re-evaluation of an identical recursive call, ≈ 2400× per Goodstein
   step, independent of the ambient level.  `WellFounded.fix` is *not* to
   blame: the compiled code contains no `Acc` references at all (proofs
   are erased for `#eval`, unlike for kernel reduction, which is what
   Phase B was avoiding).  Three proof-backed `@[csimp]` sharing variants
   were written, compiled and measured: **exactly zero effect**.  The
   reason no `csimp` can help is structural — it changes what a function
   computes, not how often the surrounding term calls it — and the fix
   that would work (memoization keyed by the code) is not expressible as
   a provably-equal pure function.  Full evidence in STATUS.md's Phase-D4
   section.  Recommendation unchanged: leave it; the correctness theorem
   carries the content at every input.  Original entry: `goodsteinStopTime` evaluates at `m = 0, 1`
   in under a second and does not finish at `m = 2`, because every
   recursive value passes through two `dropR` transports and `app₁`/
   `abs₁` duplicate their argument, so recursive calls are re-evaluated
   exponentially often in the number of Goodstein steps.  Nothing is
   memoized.  Options if this is ever worth pursuing: sharing in the
   combinators, a transport-free realizer for this derivation shape, or
   a compiled evaluator for `PureType`.  Recommendation: leave it —
   `goodsteinStopTime_spec` carries the mathematical content at every
   input, and efficiency was never a roadmap goal.  Flagged rather than
   fixed.

### Historical record of item 3½

3½. **The fragment has no `∃` — now a Phase-D blocker.**  Flagged during
   Phase B (2026-07-29); *Phase C deliberately did not fold it in*
   (2026-07-29): the transfinite-induction work turned out to be
   self-contained, while `∃` touches `Formula`, `MR`, both transports and
   the tracking relation — a phase-sized change of its own that would
   have been entangled with the notation/well-foundedness work for no
   benefit.  It is now the **first** thing Phase D needs, before any
   descent argument, since without it the target cannot be stated.  The
   original analysis stands:
   the target `∀m ∃s. G(m, s) = 0` is Π₂, and the fragment's formulas
   have only `∀` (plus `∧∨→⊥` over equations).  Phase B is unaffected
   (its deliverables are equations and their certifications), but
   Phase D cannot even state termination without either (a) an `∃`
   clause added to `Formula`/`MR` — the natural choice for this
   project, since modified realizability of `∃` carries the witness,
   and *extracting the Goodstein stopping-time function is presumably
   the point of the roadmap* — or (b) a negative translation, which
   would gut the extraction payoff.  Recommendation, updated for the
   post-Phase-C state: make `∃` **Phase D's first deliverable**, before
   the descent argument (its `MR` clause is the `orI` pattern — pair a
   witness numeral with a realizer — and it needs a `liftR`/`dropR` case,
   a `Tracked` case, and intro/elim rules with their four machinery
   cases each).

4. **Next chapter in `kleene-kreisel-lean`.**  Per the stated pipeline:
   Kreisel's density theorem is next (completing the Kleene-tree pairing
   into both machine-checked halves of "restriction costs everything /
   nothing"), awaiting its brief.  Standing alternatives: the
   countability / arbitrary-finite-types chapter (its associate-level
   abstraction closure is still the hard core there, though it is no
   longer needed for `RealizesCtQ` — see item 1); Mathlib upstreaming
   of the type-2 core.

5. **The draft paper (`paper/main.pdf`) awaits your read-through.**  It
   predates the Kleene tree module and this realizability project; when
   the dust settles, decide whether to extend it, write a separate note,
   or leave it as the type-2/collapse snapshot.

