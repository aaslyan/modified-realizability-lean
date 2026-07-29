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

## Open

3½. **The fragment has no `∃` — Phase C must decide how Goodstein's
   theorem will be *stated*.**  Flagged during Phase B (2026-07-29):
   the target `∀m ∃s. G(m, s) = 0` is Π₂, and the fragment's formulas
   have only `∀` (plus `∧∨→⊥` over equations).  Phase B is unaffected
   (its deliverables are equations and their certifications), but
   Phase D cannot even state termination without either (a) an `∃`
   clause added to `Formula`/`MR` — the natural choice for this
   project, since modified realizability of `∃` carries the witness,
   and *extracting the Goodstein stopping-time function is presumably
   the point of the roadmap* — or (b) a negative translation, which
   would gut the extraction payoff.  Recommendation: fold `∃` into
   Phase C alongside `TI(ε₀)` (its `MR` clause is the `orI` pattern:
   pair a witness numeral with a realizer), rather than discovering
   the gap mid-Phase-D.

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

