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

## Open

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

