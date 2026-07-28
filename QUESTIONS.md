# Open questions and pending decisions

A running record of decision points I have raised, with options and my
recommendations.  Items get moved to "Resolved" when you answer them.

## Resolved

1. **Which not-yet-proved piece to attack next?**
   *Asked 2026-07-27; answered: "Generic continuity."*
   ***Reopened 2026-07-27 after design analysis — my "tractable,
   ~200–300 lines" sizing was wrong.***  The finding: a level-≤1
   *conclusion* does not bound the ambient levels the extract consults.
   The application combinators climb (`impEC` and `allEC` read the major
   premise's extract one ambient up), and derivations may detour through
   arbitrarily high-level cut formulas (`impE` with any `χ → φ`).  So
   continuity of the ambient-1 functional rests on hereditary
   continuity of ambient-`k` extracts for unbounded `k` — the honest
   invariant is "the extract is hereditarily countable (has an
   associate) at every ambient," and proving *that* requires
   associate-level closure of every combinator, including abstraction —
   i.e. options (a) and (b) below are the same theorem.  The genuinely
   distinct choices now:
   - **(i) proceed to the density-theorem brief** as planned, leaving
     `RealizesCtQ` certificate-per-derivation (certificates are
     mechanical by the demo's method: compute the value, exhibit the
     modulus) — *my recommendation, matching the stated pipeline*;
   - (ii) brief the countability chapter properly as its own pass — it
     subsumes both this gap and the parent repo's deferred finite-types
     chapter, so it pays double, but it is weeks-scale, not
     lemma-scale;
   - (iii) a syntactically restricted generic theorem (introduction-only
     derivations, no `impE`/`allE`) is provable cheaply but excludes
     modus ponens — low value; I recommend against pretending it is the
     theorem.

2. **Push `Realizability` to GitHub?**
   *Answered 2026-07-27: pushed to
   `github.com/aaslyan/modified-realizability-lean`.*

3. **Rename the local `ContinuousFunctionals` directory?**
   *Done 2026-07-27: now `/home/aaslyan/kleene-kreisel-lean`; the
   Realizability path dependency and manifest updated, both repos
   rebuilt green.*

2. **Push `Realizability` to GitHub?**
   *Answered 2026-07-27: pushed to
   `github.com/aaslyan/modified-realizability-lean`.*

## Open

4. **Next chapter in `kleene-kreisel-lean`.**  Per the stated pipeline:
   Kreisel's density theorem is next (completing the Kleene-tree pairing
   into both machine-checked halves of "restriction costs everything /
   nothing"), awaiting its brief.  Standing alternatives: the
   countability / arbitrary-finite-types chapter (see item 1's finding —
   it would also discharge the `RealizesCtQ` certificate gap); Mathlib
   upstreaming of the type-2 core.

5. **The draft paper (`paper/main.pdf`) awaits your read-through.**  It
   predates the Kleene tree module and this realizability project; when
   the dust settles, decide whether to extend it, write a separate note,
   or leave it as the type-2/collapse snapshot.

6. **Induction axiom (long-term plan).**  STATUS.md specifies the single
   missing theorem (closure of `MR` under primitive recursion at every
   ambient level).  Green-light it as its own brief when ready — it
   should not be folded into smaller work.
