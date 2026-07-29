# Status: milestone COMPLETE, generic continuity COMPLETE, induction (Phase 2) COMPLETE

`lake build` succeeds, zero `sorry`/`admit`.  `#print axioms` on the
soundness theorem (now covering the `ind` rule), the recursor's
preservation theorem, the generic-continuity theorem, and the
collapse-demo theorem reports:

```
'Realizability.soundness' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'Realizability.MR_indRecC' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'Realizability.extract_continuous' depends on axioms:
  [propext, Quot.sound]
'Realizability.collapse_demo' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

(likewise `MR_liftR_dropR`, `FR_famOf`, `indC_tracked` —
`[propext, Quot.sound]` — `demo_extract_eq`, and
`demo_extract_continuous`, the latter a one-line corollary of
`extract_continuous`).

## What is delivered

- `Syntax.lean` — terms, the fragment's formulas, capture-safe
  substitution, and the 17-rule natural-deduction family — since the
  Phase-2 extension including the arithmetic induction rule `ind`
  (from `φ(0)` and `∀x (φ(x) → φ(succ x))`, conclude `∀x φ(x)`; side
  condition: no variable capture for the substituted `succ x`, same
  shape as `∀`-elim's).
- `ModifiedRealizes.lean` — the pure-type devices (`up`/`down`,
  `pairPT`/`fstPT`/`sndPT`, `app₁`/`abs₁` with beta) and the
  **flexible-ambient** modified-realizability relation `MR ρ φ n x`
  with realizers in `PureType (n+1)`, plus environment-congruence
  (`MR_congr`) and the substitution lemma (`MR_subst`).
- `Transport.lean` — the formula-indexed level transports
  `liftR`/`dropR` with the mutual preservation induction
  (`MR_liftR_dropR`), iterated versions, and the family generator
  `famOf` with `FR_famOf`.  This is the pure-type "finite types as
  retracts" machinery, reusable by the parent project's deferred
  arbitrary-finite-types chapter.
- `Extraction.lean` — the extraction function, dispatching to one named
  combinator per rule (full list below), and the ambient bound
  `derivBound`.
- `Soundness.lean` — `CtxR_congr` and **`soundness`**: for every
  derivation, environment, and realizing context assignment, the
  extracted family realizes the conclusion at every ambient level above
  `derivBound`.
- `GenericContinuity.lean` — the **generic continuity theorem**
  (`extract_continuous`): the extracted type-2 realizer of *every*
  closed derivation is continuous.  Proved by induction on the
  derivation, threading the oracle-parameterized continuity relation
  `Tracked` (a Kripke-style logical relation on Baire-space-indexed
  families of pure-type objects), with one named preservation lemma per
  extraction combinator (full list below) and tracking preservation for
  every pure-type device and transport (`up`/`down`, the pairing
  devices, `app₁`/`abs₁`, `liftR`/`dropR`, `famOf`).
- `CollapseDemo.lean` — `RealizesCtQ` (the class of a closed
  derivation's extracted type-2 realizer in `CtQ 2`, via the parent
  project's capstone equivalence `ctQTwoEquiv`) — now **total on closed
  derivations**, the continuity obligation discharged uniformly by
  `extract_continuous` — and the named demo: `demoDeriv₁`/`demoDeriv₂`,
  two different derivations of `A ∧ B → B ∧ A` whose extracted terms
  are proved equal as functionals (`demo_extract_eq`) and hence denote
  the same element of `CtQ 2` (**`collapse_demo`**).  The demo's
  continuity certificates are one-line corollaries of
  `extract_continuous`; the concrete value computation
  (`demo_extract_apply`) is kept as the worked illustration of the
  modulus.

## The per-rule extraction combinators (all in `Extraction.lean`)

1. `axC` — hypothesis projection (rule `ax`);
2. tail recursion on the context (rule `wk`);
3. `andIC` — pointwise pairing (`andI`);
4. `andE₁C` — pointwise first projection (`andE₁`);
5. `andE₂C` — pointwise second projection (`andE₂`);
6. `orI₁C` — tag 0 (`orI₁`);
7. `orI₂C` — tag 1 (`orI₂`);
8. `orEC` — pointwise tag split, rebuilding the branch hypothesis's
   family from the payload at each ambient (`orE`);
9. `impIC` — abstraction over the bound realizer's transport-generated
   family (`impI`);
10. `impEC` — application, major premise one ambient up (`impE`);
11. `botEC` — vacuous (`botE`);
12. `allIC` — abstraction reading the numeral off the argument
    (`allI`);
13. `allEC` — application at the numeral of the term's value (`allE`);
14. `eqDecC` — decidable-equality tag (`eqDec`);
15. `axiomC` — contentless realizer for `succNeZero`;
16. `axiomC` — contentless realizer for `succInj` (vacuous or
    true-equation implication clauses);
17. `indC` — **the induction recursor** (rule `ind`): the type-indexed
    primitive recursion `indRecC` — `indRecC a b 0 = a`,
    `indRecC a b (k+1) = app₁ (app₁ b (natPT _ k)) (indRecC a b k)` —
    at the realizer's own type `PureType (m + 1)`, uniformly in the
    ambient `m`, packaged into the concluded `∀x. φ(x)` by the existing
    `allIC` device.  The one combinator that *iterates*: the number of
    `app₁` steps performed is the numeral being realized.  Correctness
    is `MR_indRecC` (`Soundness.lean`), closure of `MR` under primitive
    recursion at every ambient level, stated once and instantiated —
    no level-by-level instances exist.

## The per-combinator continuity preservation lemmas (all in `GenericContinuity.lean`)

One per combinator, same order as the list above; each says the
combinator sends tracked inputs to tracked outputs:

1. `axC_tracked` (rule `ax`);
2. `wk_tracked` — the tail of a tracked context is tracked (rule `wk`);
3. `andIC_tracked` (`andI`);
4. `andE₁C_tracked` (`andE₁`);
5. `andE₂C_tracked` (`andE₂`);
6. `orI₁C_tracked` (`orI₁`);
7. `orI₂C_tracked` (`orI₂`);
8. `orEC_tracked` (`orE`) — continuous tag read, tracked `famOf`
   payload families, pointwise case split;
9. `impIC_tracked` (`impI`) — abstraction closure **by β-reduction**
   under the tracking relation (see below);
10. `impEC_tracked` (`impE`) — application, major premise one ambient
    up;
11. `botEC_tracked` (`botE`);
12. `allIC_tracked` (`allI`) — the bound numeral is a continuous read
    off the tracked argument;
13. `allEC_tracked` (`allE`) — application at the numeral of a
    continuously computed term value;
14. `eqDecC_tracked` (`eqDec`) — case split on the equality of two
    continuously computed values;
15. `axiomC_succNeZero_tracked` (`succNeZero`);
16. `axiomC_succInj_tracked` (`succInj`);
17. `indC_tracked` (`ind`) — per fixed iteration count the recursor is
    tracked by a small induction on the numeral (each step is `app₁` of
    tracked pieces, existing closure lemmas only); the *actual* count,
    read continuously off the abstraction's argument, is absorbed by
    the one new closure fact `tracked_apply_nat` (with its base form
    `continuous2_apply_nat`): consulting a family of tracked families
    at a continuously computed numeral preserves tracking, because near
    any oracle the numeral is locally constant — the countably-branching
    generalization of the binary case split `ite_tracked`.

The capstone `extract_continuous` is the induction on `Deriv`
(`extract_tracked`) invoking one preservation lemma per case — the same
shape as `soundness` — instantiated at the constant environment, empty
context, and the tracked identity family of Baire space.

## Design decisions and deviations (flagged)

- **Flexible ambient level.**  `MR ρ φ n x` is defined at every ambient
  `n`, all clauses at one level with binders stepping down — no level
  coercion occurs in the definition.  The coercions concentrate in the
  transports, which extraction alone needs.
- **`Realizes` in `CtQ`, uniformly.**  `RealizesCtQ` lands in `CtQ 2`
  via `ctQTwoEquiv`, for **every** closed derivation: the continuity
  obligation is discharged once by `extract_continuous`
  (`GenericContinuity.lean`), with no per-derivation certificate and no
  level hypothesis.  The brief's `lvl φ ≤ 1` restriction turned out to
  be unnecessary — continuity of the extract is a property of the
  extraction combinators alone; the formula's level matters only for
  *realization* (`soundness`), not for continuity.

  *How the 2026-07-27 sizing finding was resolved (superseded
  2026-07-28):* the earlier analysis was right that the ambient-1
  extract consults extracts at every ambient (`impEC`/`allEC` climb,
  cut formulas are unbounded), and right that "every extract **has an
  associate** at every ambient" is countability-chapter-sized (its hard
  core is associate-level abstraction closure).  It was wrong to
  conclude those are the only invariant choices.  The compositional
  invariant that works is the **oracle-parameterized continuity
  relation** (`Tracked`): a Baire-indexed *family* of pure-type objects
  is tracked iff its pointwise application to every tracked argument
  family is a continuous function of the oracle — the classical
  relative-continuity logical relation.  Tracking constrains only how
  numbers are read out of a family through continuously supplied
  arguments, never a single functional in isolation, so **abstraction
  closure holds by β-reduction** (`abs₁_tracked`): applying `abs₁ G` to
  a tracked argument computes `G`, and no associate is ever
  constructed.  The capstone then reads the extract off along the
  tracked identity family `α ↦ α`.  The associate-level closure theorem
  remains genuinely open — but it is needed for the parent project's
  finite-types chapter, not for this theorem.
- The `→` clause of `MR` is the `Assoc`/`CtPer` clause *shape* at the
  level of pure functionals; the literal `Assoc`-instance reading enters
  through the `CtQ` packaging, not as a redundant re-proof.

## The induction rule (Phase 2): COMPLETE

The specification recorded here since the first milestone ("exactly one
new theorem is required: closure of `MR` under primitive recursion at
every ambient level") is now discharged.  What was added, per file:

- `Syntax.lean` — the rule `ind`: from `Deriv Γ (φ.subst x zero)` and
  `Deriv Γ (all x (φ.imp (φ.subst x (succ (var x)))))`, conclude
  `Deriv Γ (all x φ)`, with the no-capture side condition
  `SubstOK (succ (var x)) φ` (same shape as `∀`-elim's).
- `Extraction.lean` — combinator 17 (`indRecC`/`indC`, listed above);
  `derivBound (ind D₁ D₂ _) = max (derivBound D₁) (derivBound D₂) + 1`.
- `Soundness.lean` — **`MR_indRecC`**, the actual new theorem: if `a`
  realizes `φ(0)` at ambient `m` and `b` realizes
  `∀x (φ(x) → φ(succ x))` at ambient `m + 2`, then `indRecC a b k`
  realizes `φ` under `ρ[x ↦ k]` at ambient `m`, for every `k` — proved
  **uniformly in the ambient level `m`** (one statement, no
  level-by-level instances), by ordinary natural-number induction on
  the numeral `k`.  The two inductions are kept explicitly distinct:
  `MR_indRecC` is the "small" induction (on the numeral, at a fixed
  ambient), invoked exactly once by the `ind` case of the "big"
  induction over `Deriv` in `soundness`, which only unfolds the `allIC`
  packaging and dispatches.

One structural point deserves flagging, because it is *why* the small
induction stays level-uniform rather than needing the transports: the
flexible-ambient design makes `MR`'s `→` clause consume and produce
realizers at the *same* level, so the iterate never crosses ambient
levels at all — the step realizer, consumed through the `∀` clause at
`m + 2` and the `→` clause at `m + 1`, maps ambient-`m` realizers of
`φ(k)` to ambient-`m` realizers of `φ(succ k)`.  The first milestone's
specification predicted the iterate would cross implication levels and
lean on the transports; in the event the transports are needed only
where they always were (the binder cases of extraction), and the
recursion is genuinely primitive recursion at the fixed type
`PureType (m + 1)`, uniformly in `m`.  The substitution lemma
(`MR_subst`) does the conversion between `φ(0)`/`φ(succ x)` under `ρ`
and `φ` under the updated environment at both ends of each step.

**Generic continuity against the new combinator — answered
explicitly.**  The generic continuity theorem does *not* cover `ind`
for free: `extract_tracked` is an induction over `Deriv`, so the new
rule adds a case, and `indC_tracked` is its per-combinator preservation
lemma (item 17 above).  But the *invariant* needed no strengthening,
and only one genuinely new closure fact was required:
`tracked_apply_nat` — the iteration count is read off the oracle
through the `allIC` abstraction, and a count that is a continuous
function of the oracle is locally constant, so the recursor (tracked at
each fixed count by the existing `app₁`-closure lemmas) stays tracked
at the oracle-dependent count.  `extract_continuous`, `RealizesCtQ`,
and `collapse_demo` then cover `ind`-derivations with no further
change — `CollapseDemo.lean` was not touched.

## Citation (checked as far as the primary text allows)

The construction follows the standard realizer of the induction axiom
in modified realizability: Gödel's primitive-recursor constants
applied to the base and step realizers, iterating application along
the numeral — A.S. Troelstra (ed.), *Metamathematical Investigation of
Intuitionistic Arithmetic and Analysis*, Springer LNM 344, 1973:
**Ch. III, §3.4** (modified realizability and its soundness theorem)
for the interpretation, with the recursor constants of the underlying
system **N-HAω from Ch. I, §1.6**.

Granularity, stated plainly per the house discipline: the primary text
was **not accessible** in this environment (Springer's per-chapter
PDFs are paywalled; no scan exists in the ILLC eprints repository, the
Troelstra Archive index, or the Internet Archive — all checked
directly).  The section-level attribution above was cross-checked
against a primary-adjacent source, Troelstra's own corrections report
*Corrections to some Publications* (ILLC X-2018-02, December 2018,
`eprints.illc.uva.nl/id/eprint/1650`), which confirms directly: §3.4
of LNM 344 is the modified-realizability section (its corrections
reference items "3.4.7" and "3.4.14" on pp. 215–222, and the relation
`y mr A`), and §1.6.15 defines the system there called `HAω` with its
combinator/equality axioms.  The item-level clause number for the
induction case inside §3.4's soundness proof is deliberately **not**
cited, rather than guessed — refining to definition granularity
requires the book itself and remains a documentation-only follow-up,
exactly as recorded for Longley–Normann chapter-level citations in the
parent project's STATUS.md.

## Out of scope (per the brief)

Full first-order quantification with unbounded nesting beyond the one
`∀`-pair; Dialectica; any claim of soundness for HA.
