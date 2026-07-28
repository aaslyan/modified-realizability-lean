# Open questions and pending decisions

A running record of decision points I have raised, with options and my
recommendations.  Items get moved to "Resolved" when you answer them.

## Resolved

1. **Which not-yet-proved piece to attack next?**
   *Asked 2026-07-27; answered: "Generic continuity."*
   - **(a) Generic continuity** *(my recommendation — selected)*: prove
     that extracted type-2 realizers are always continuous, for closed
     derivations of level-≤1 formulas, so `RealizesCtQ` applies to every
     such derivation without a per-derivation certificate.  Tractable:
     an induction over derivations threading a compositional continuity
     invariant through context realizers (a small logical relation),
     estimated ~200–300 lines.
   - (b) Full general `CtQ` landing: every extracted functional at every
     level has an associate — the parent project's deferred
     finite-types/countability chapter; a large undertaking.
   - (c) Something else (the original message was garbled).

2. **Push `Realizability` to GitHub?**
   *Answered 2026-07-27: pushed to
   `github.com/aaslyan/modified-realizability-lean`.*

## Open

3. **Rename the local `ContinuousFunctionals` directory to
   `kleene-kreisel-lean`?**  Cosmetic consistency with the GitHub name;
   one `mv` plus updating the `Realizability` lakefile's path dependency
   and my memory notes.

4. **Next chapter in `kleene-kreisel-lean`, when this milestone rests.**
   Standing options, unchanged: arbitrary finite types / combinatory
   structure (now partially motivated by the transports built here);
   Kreisel's density theorem (the deep end); Mathlib upstreaming of the
   type-2 core.

5. **The draft paper (`paper/main.pdf`) awaits your read-through.**  It
   predates the Kleene tree module and this realizability project; when
   the dust settles, decide whether to extend it, write a separate note,
   or leave it as the type-2/collapse snapshot.

6. **Induction axiom (long-term plan).**  STATUS.md specifies the single
   missing theorem (closure of `MR` under primitive recursion at every
   ambient level).  Green-light it as its own brief when ready — it
   should not be folded into smaller work.
