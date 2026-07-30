# Status: COMPLETE through Phase D5 — Goodstein's theorem is proved inside the fragment and its stopping-time function extracted, certified, and executed

Phases: milestone (modified realizability + extraction + soundness),
generic continuity, induction (2), arithmetic (A), hereditary base-`k`
and the Goodstein sequence (B), transfinite induction to `ε₀` (C), and
Phase D in four checkpoints — `∃` (D0), the ordinal-assignment
obligations (D1), Goodstein's theorem (D2), the extracted function
(D3).

`lake build` succeeds, zero `sorry`/`admit`.  `#print axioms` on the
soundness theorem (now covering the `ind` rule and the Phase-A rules),
the recursor's preservation theorem, the generic-continuity theorem, and
the collapse-demo theorem reports:

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

and on the four Phase-A equation theorems (`#print axioms` commands are
in `Arithmetic.lean` itself, so this is checked at every build):

```
'Realizability.plus_zero_realized'   … [propext, Classical.choice, Quot.sound]
'Realizability.plus_succ_realized'   … [propext, Classical.choice, Quot.sound]
'Realizability.times_zero_realized'  … [propext, Classical.choice, Quot.sound]
'Realizability.times_succ_realized'  … [propext, Classical.choice, Quot.sound]
'Realizability.plus_zero_extract_continuous'   … [propext, Quot.sound]
'Realizability.plus_succ_extract_continuous'   … [propext, Quot.sound]
'Realizability.times_zero_extract_continuous'  … [propext, Quot.sound]
'Realizability.times_succ_extract_continuous'  … [propext, Quot.sound]
```

and on the Phase-C theorems (`#print axioms` in
`TransfiniteInduction.lean`, checked at every build — note the first
line, which is the well-foundedness of the notation order that the
transfinite recursor is defined by, and which is deliberately
`Classical`-free so the continuity budget survives):

```
'Realizability.oLt_wf'                     … [propext, Quot.sound]
'Realizability.MR_tiRecC'                  … [propext, Classical.choice, Quot.sound]
'Realizability.ti_demo_realized'           … [propext, Classical.choice, Quot.sound]
'Realizability.prec_one_omega_realized'    … [propext, Classical.choice, Quot.sound]
'Realizability.ti_demo_extract_continuous' … [propext, Quot.sound]
'Realizability.ordOf_goodstein_three_descends' … does not depend on any axioms
```

and on the Phase-B certification theorems (`#print axioms` in
`Goodstein.lean`, likewise checked at every build):

```
'Realizability.hrep_self_realized'    … [propext, Classical.choice, Quot.sound]
'Realizability.good_compute_realized' … [propext, Classical.choice, Quot.sound]
'Realizability.hrep_self_extract_continuous'    … [propext, Quot.sound]
'Realizability.good_compute_extract_continuous' … [propext, Quot.sound]
```

(likewise `MR_liftR_dropR`, `FR_famOf`, `indC_tracked` —
`[propext, Quot.sound]` — `demo_extract_eq`, and
`demo_extract_continuous`, the latter a one-line corollary of
`extract_continuous`).

## What is delivered

- `Syntax.lean` — terms (since Phase A over `{0, succ, +, ×}`, since
  Phase B additionally `pred`/`exp`/`bump`/`good`, with the
  fuel-structural value-level functions `hlog`/`bumpN`/`goodN` and the
  `numeral` embedding), the fragment's formulas, capture-safe
  substitution, and the 39-rule natural-deduction family — since the
  Phase-2 extension including the arithmetic induction rule `ind`
  (from `φ(0)` and `∀x (φ(x) → φ(succ x))`, conclude `∀x φ(x)`; side
  condition: no variable capture for the substituted `succ x`, same
  shape as `∀`-elim's); since the Phase-A extension the
  equational-logic kit (`eqRefl`, and `eqSymm`/`eqTrans`/`eqCongSucc`/
  `eqCongPlus`/`eqCongTimes` as implication schemas, `succInj`-style)
  plus the four first-argument recursion equations defining `+`/`×`
  (`zeroPlus`, `succPlus`, `zeroTimes`, `succTimes`); and since the
  Phase-B extension the recursion schemas for `pred`/`exp`/`good`
  (`predZero`, `predSucc`, `expZero`, `expSucc`, `goodZero`,
  `goodSucc`), the two `bump` axioms (`bumpZero`, and the numeral
  graph `bumpNum` — see the Phase-B section), and the four matching
  congruence schemas (`eqCongPred`, `eqCongExp`, `eqCongBump`,
  `eqCongGood`).
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
- `Arithmetic.lean` (Phase A) — the four defining equations of `+`/`×`
  as closed `ind` theorems with extracted, certified realizers; see the
  Phase-A section below.
- `Goodstein.lean` (Phase B) — hereditary base-`k` representation **as
  a term of the fragment's own syntax in one distinguished base
  variable**, the bump-and-decrement step, and the Goodstein sequence,
  with fragment-internal certification (`hrepSelfDeriv`,
  `bumpHrepDeriv`, `goodComputeDeriv`) and kernel-verified value
  cross-checks against `WilliamAngus/Goodstein`; see the Phase-B
  section below.  Goodstein's theorem itself is **not** proved and not
  claimed — Phases C/D.
- `Epsilon0.lean` (Phase C, and the only module *before* `Syntax.lean`)
  — the ordinal notations below `ε₀` as natural-number codes, their
  Cantor-normal-form order `≺`, the normal-form predicate that makes it
  well-founded, and **`oLt_wf`**; plus a hand-rolled choice-free,
  kernel-computable triangular pairing (Mathlib's `Nat.pair` could not be
  used — see the Phase-C section).
- `TransfiniteInduction.lean` (Phase C) — the identification of the
  notations with Phase B's `HTerm` grammar (`ordTerm`), the Goodstein
  ordinal assignment `ordOf` with kernel-verified descent instances, the
  rule exercised end to end, and the `#print axioms` block.
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
    no level-by-level instances exist;
18. –27. `axiomC` — contentless realizers for the ten Phase-A schemas
    (`eqRefl`, `eqSymm`, `eqTrans`, `eqCongSucc`, `eqCongPlus`,
    `eqCongTimes`, `zeroPlus`, `succPlus`, `zeroTimes`, `succTimes`):
    atomic conclusions carry no computational content, so each
    soundness case is just the equation's truth from its premises'
    truths (`derivBound`: 0 for the bare-equation schemas, 1/2 for the
    single/nested implication schemas);
28. –39. `axiomC` — contentless realizers for the twelve Phase-B
    schemas (`predZero`, `predSucc`, `expZero`, `expSucc`, `bumpZero`,
    `bumpNum`, `goodZero`, `goodSucc`, `eqCongPred`, `eqCongExp`,
    `eqCongBump`, `eqCongGood`), same discipline and bounds as the
    Phase-A group;
40. `tiC` — **the transfinite recursor** (rule `tiEps0`): `tiRecC`,
    defined by `WellFounded.fix` along the notation order `≺`, packaged
    by `allIC` exactly as `indC` is.  The second combinator that
    recurses, and the only one whose recursion is not along `ℕ`'s
    successor structure.  Correctness is `MR_tiRecC` (`Soundness.lean`);
    `tiRecC_eq` is the non-dependent unfolding both the soundness and
    the continuity proof use;
41. –42. `axiomC` — contentless realizers for the two remaining Phase-C
    schemas (`precNum`, the numeral graph of the order, and
    `eqCongPrec`).

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
    generalization of the binary case split `ite_tracked`;
18. –27. `axiomC_eqRefl_tracked` … `axiomC_succTimes_tracked` — one per
    Phase-A schema, all the tracked junk family.  The one place Phase A
    genuinely touches the continuity module is *not* per-rule:
    `termEval_continuous` gains the `plus`/`times` cases (a binary
    composition of two continuous reads, `continuous2_comp₂`, already
    in the closure kit) — the `allE` case reads term values off tracked
    environments, so evaluation over the extended signature had to stay
    continuous.  No case of `extract_tracked` is left silent;
28. –39. `axiomC_predZero_tracked` … `axiomC_eqCongGood_tracked` — one
    per Phase-B schema, all the tracked junk family; and
    `termEval_continuous` gains the `pred`/`exp`/`bump`/`good` cases —
    `bump`/`good` are *arbitrary* functions of two continuously
    computed values, so `continuous2_comp₂` again covers them with no
    new closure fact.  No case of `extract_tracked` is left silent.

40. `tiC_tracked` (`tiEps0`) — the recursor is tracked at each *fixed*
    notation by well-founded induction along `≺` (`tiRecC_tracked`), and
    the oracle-dependent notation code is absorbed by the same
    `tracked_apply_nat` that rule `ind` needed — no new closure fact was
    required.  The case split on `j' ≺ j` inside the recursor does not
    depend on the oracle, so it is discharged index by index rather than
    by `ite_tracked`.  `termEval_continuous` gains the `prec` case
    (`continuous2_comp₂ oltN`);
41. –42. `axiomC_precNum_tracked`, `axiomC_eqCongPrec_tracked`.

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

## Phase A (arithmetic): COMPLETE — Option 2, "mirror recursion" form

The brief posed Option 1 (the four briefed equations as bare axiom
rules) against Option 2 (the equations *proved* using `ind`), and asked
for the choice and its rationale to be recorded here.

**Option 2 was taken, in the following form.**  `Term` gains `plus` and
`times`; the axiom rules *defining* them (`Syntax.lean`) are the
primitive-recursion equations **on the first argument** —

```
0 + t = t          succ s + t = succ (s + t)
0 × t = 0          succ s × t = (s × t) + t
```

— while the four briefed equations recurse on the *second* argument,
and are therefore genuine theorems, each proved by `ind` on its first
argument (`Arithmetic.lean`): even `∀x. x + 0 = x` is an induction,
exactly as `0 + n = n` is in Lean itself (where `Nat.add` recurses on
the second argument — the same mirror, reflected).

**Why this form, stated plainly.**  The brief's own Option-2 sketch
("`x + 0 = x` is then the base case of a recursion on the second
argument") harbors a collapse: had the defining axiom schemas been the
briefed equations themselves, each deliverable would have been one
`allI` away from an axiom citation, `ind` would never fire, and Option
2 would have been Option 1 with different labels.  The alternative that
keeps the axioms second-argument *and* the theorems non-trivial is a
term-level recursion binder — exactly the "deeper syntactic machinery"
wall the brief anticipated (a binding term former, substitution through
it, new capture conditions).  First-argument axiomatization dissolves
the dilemma: the definition stays four schema rules with contentless
realizers (the `succNeZero`/`succInj` pattern, nothing new in the
machinery), and all four deliverables genuinely exercise Phase 2's
induction — five `ind` derivations in total, including the auxiliary
`(z + x) + y = (z + y) + x` (`plusRightCommDeriv`) that the
multiplication step needs, plus theorem-to-theorem reuse
(`timesZeroDeriv` and `timesSuccDeriv` instantiate `plusZeroDeriv`,
`plusSuccDeriv`, and the auxiliary inside their step cases).

**The equational-logic kit had to be added regardless.**  Before Phase
A the fragment could not derive *any* equation outright — no rule
produced an atomic conclusion (`eqDec` yields a disjunction; `succInj`
an implication; the `orE` escape from the negative branch is circular).
The kit is the standard first-order-with-equality apparatus for the
signature `{0, succ, +, ×}`: `eqRefl`, plus symmetry, transitivity and
one congruence per function symbol as implication schemas in the
`succInj` style, all with contentless realizers (`axiomC`), soundness
cases one line each.  A single Leibniz replacement rule was considered
and rejected: it subsumes the kit but drags a formula parameter and two
`SubstOK` side conditions into every use site, and its soundness case
needs `MR_subst` gymnastics; the per-symbol kit keeps both the
machinery cases and the derivations trivial.

**Bound-variable discipline** (`Arithmetic.lean`): `∀`-elimination's
no-capture condition forbids instantiating `∀x∀y. φ` at terms
containing `y`, so the two-variable lemmas exist in α-variant form
where needed — `plusSuccDeriv'` (bound variables 2, 3) is derived from
the deliverable `plusSuccDeriv` by instantiate-and-regeneralize (allE
twice at fresh variables, allI twice), not re-proved; the auxiliary
binds 2, 3, 4 outright.

**Machinery cases added, none silent**: `extract`/`derivBound` (ten
`axiomC` dispatches; bounds 0/1/2 by implication depth), `soundness`
(ten one-line truth cases), `extract_tracked` (ten junk-family cases),
and — the one substantive continuity touch — `termEval_continuous`
gains `plus`/`times` via the pre-existing `continuous2_comp₂`, keeping
`allE`'s term-value reads continuous over the extended signature.
`extract_continuous` therefore covers every new rule; the eight
`#print axioms` checks live in `Arithmetic.lean` and run at every
build (outputs quoted at the top of this file).

**Out of scope, per the brief**: hereditary base-`k` notation and
anything Goodstein-specific (Phase B); `TI(ε₀)` (Phase C); any
strength claim beyond the two operations and their four equations.

## Phase B (hereditary base-k and the Goodstein sequence): COMPLETE

**Scope, stated plainly per the brief**: this phase makes Goodstein's
theorem *expressible* and certifies the definitions; it does **not**
prove Goodstein's theorem, does not touch `TI(ε₀)` or ordinal
notations, and no such claim is made anywhere.  Those are Phases C/D.

### The encoding decision (the load-bearing choice)

**A hereditary base-`k` representation is a term of the fragment's own
syntax, in one distinguished free variable — variable `0`, "the
base".**  `hrep k n` (`Goodstein.lean`) is the term
`x^(hrep k e)·c + hrep k r` over `{0, succ, +, ×, exp}`, exponents
hereditarily in the same shape.  Justification:

- *Bumping the base is not an operation at all* under this encoding —
  it is evaluating the **same term** at base `k + 1`
  (`hrep_eval_bump`), which is the mathematical essence of a Goodstein
  step.  The reference repository's base-change `f` does exactly this
  (it maps `HBase base h → HBase (base+1) _` leaving the tree
  untouched); our encoding makes that structural fact definitional.
- *Existence is a derivable equation, not an axiom*: the certifying
  evaluator `hrepSubstDeriv` proves, inside the fragment,
  `(hrep k n)[base := b̂] = (value)̂` for every base numeral, from the
  recursion axioms of `+`/`×`/`exp` alone; `hrepSelfDeriv` is its
  existence instance `(hrep k n)[base := k̂] = n̂`.  No axiom about
  `hrep` exists.
- The alternative encodings the brief anticipated (Gödel-coded digit
  sequences via pairing arithmetic, or `pairPT`-level realizer
  structure) would put the representation *outside* the term language
  or demand a coding apparatus (`div`/`mod`/β-function) far heavier
  than Phase D needs.  The fragment's own terms already *are* finite
  trees over exactly the right signature.

The grammar of representations is `HTerm` (`Prop`-valued: base
variable, `zero`, `succ`, `+`, `×`, `exp` — nothing else), with
`hrep_hterm` and `HTerm.vars_eq_zero` the well-formedness facts.

### The `bump` compromise, flagged

`bump`'s recursion is course-of-values *through the hereditary
exponent structure* — not a first-order equation schema over open
terms.  It therefore enters the fragment by its **numeral graph**
(`bumpNum : ⊢ bump k̂ n̂ = (bumpN k n)̂`) plus zero-absorption
(`bumpZero`, a genuine term schema).  The semantic characterization
"`bump` is the representation read at the next base" is **derived**,
per numeral instance, as `bumpHrepDeriv` — proved from `bumpNum` and
the certifying evaluator, not axiomatized.  Open-term decomposition
axioms for `bump` (for `ind` proofs *about* `bump` in Phase D, if the
descent argument needs them fragment-side) are deliberately deferred;
what Phase D certainly needs value-side is already here.  `pred`,
`exp`, and `good` need no such compromise: their defining equations
are honest first-order schemas (`good`'s recursion `goodZero`/
`goodSucc` is exactly the sequence's definition, and the fragment
*computes* the sequence from it: `goodComputeDeriv`, e.g. the closed
theorem `⊢ good 4̂ 1̂ = 26̂`).

### Uniqueness: deferred, and why that is safe

Existence is proved (meta: `hrep_eval_self`; fragment:
`hrepSelfDeriv`, both unconditional in `k` — degenerate bases `k ≤ 1`
yield the one-digit representation and the identity bump, so no
`k ≥ 2` side condition contaminates the statements).  Uniqueness —
canonicity of digit bounds (`c < k`) and exponent ordering, the
reference's `NFBelow`/`NF` layer — is **deferred**: every object Phase
D consumes factors through the *deterministic function* `hrep`; no
statement in this development quantifies over "some representation of
`n`", so canonicity is never load-bearing here.  It becomes Phase-D
work exactly if the ordinal assignment is defined on arbitrary
`HTerm`s rather than on `hrep`'s image.

### Implementation note: fuel, not well-founded recursion

`hlog`/`bumpN`/`hrep` recurse structurally on fuel `= n` (adequacy:
`hlog_lt`, `pow_hlog_le`) instead of well-founded recursion or
Mathlib's `Nat.log`, because `WellFounded.fix` does not reduce in the
kernel: the concrete cross-checks (`goodN_four` etc.) are `rfl`, and
`goodFourOneDeriv`'s type `numeral (goodN 4 1) = numeral 26` checks by
kernel computation.  Division, modulus and powers are
kernel-accelerated, so only the logarithm needed the treatment.

### Cross-check against `WilliamAngus/Goodstein` (reference only)

Checked against `Goodstein/HBase.lean` and `Goodstein/Goodstein.lean`
of that repository (classical Mathlib development; no code imported —
their machinery proves facts about `ℕ`/ordinals directly, ours must
live inside the derivation system):

- `hrep` ↔ `HBase.ofNat`; term shape `x^e·c + r` ↔ constructor
  `hadd i aᵢ rest ↦ base^(eval i)·aᵢ + eval rest`; checked at
  `n = 4, k = 2`: both produce `2^(2^(2^0))` (theirs as a tree, ours
  as the term with base variable), value `4`.
- `bumpN` ↔ `eval ∘ f` (their base replacement): `bumpN 2 4 = 27 =
  3^(3^(3^0))`, kernel-verified (`bumpN_two_four`).
- `Term.gstep`/`pred (bump …)` ↔ their `G = (f …).pred`; value at
  `(2, 4)` is `26` both ways.
- `goodN`/`good` ↔ `goodsteinSequence start h n i` at `start = 2`:
  their step `i → i+1` applies `G` at base `start + i = 2 + i`; ours
  bumps base `s + 2` at step `s → s+1` — the same convention, no
  off-by-one (the brief's explicit worry).  Values kernel-verified:
  `goodN 4 = 4, 26, 41, 60, …` (`goodN_four`) and
  `goodN 3 = 3, 3, 3, 2, 1, 0, 0` (`goodN_three`), the classical
  sequences.
- Their `HBase.pred` ↔ our `pred` symbol (truncated predecessor);
  their `NFBelow`/`NF` ↔ our deferred canonicity layer (above).

### File placement

`Syntax.lean` holds only what must live with `Term`/`eval`/`Deriv`:
the value-level functions (`hlog`, `bumpN`, `goodN`), `numeral`, the
four constructors, and the twelve rules.  Everything else — `hrep`,
the grammar, the meta theorems, the derivation-formers, the certifying
evaluator, the certification block — is the new `Goodstein.lean`
(importing `Arithmetic.lean`).  Machinery cases added with no silent
gaps: `extract`/`derivBound`/`soundness`/`extract_tracked` (twelve
each) and `termEval_continuous` (`pred`/`exp`/`bump`/`good` via the
existing `continuous2_comp₂`); `extract_continuous` covers every new
rule, and the four `#print axioms` checks in `Goodstein.lean` run at
every build (outputs quoted at the top of this file).

## Phase C (transfinite induction up to `ε₀`): COMPLETE

**Scope, stated plainly per the brief**: this phase adds the rule
`tiEps0`, extracts and certifies its realizer, and proves that realizer
continuous.  It does **not** prove Goodstein's theorem (Phase D), makes
**no** conservativity/consistency/strength claim about the extended
fragment, does not claim (and does not prove) that the fragment fails to
derive the rule — that is standard metatheory for PA, invoked only as
framing — and does not generalize beyond `ε₀`.

```
∀x. (∀y. y ≺ x → φ(y)) → φ(x)
─────────────────────────────  (tiEps0)
          ∀x. φ(x)
```

### The representation decision: notations are natural-number codes

The fragment has **one sort** — its variables range over `ℕ` and its
atomic formulas are equations — so `tiEps0`'s `∀x`/`∀y` cannot range over
a separate type of notations, and `y ≺ x` cannot be a new atomic
predicate.  Both are therefore *coded*: `x`, `y` are natural numbers read
as Cantor-normal-form trees, and `y ≺ x` is the equation
`prec y x = succ zero`, `prec` being a new function symbol whose value
semantics is the characteristic function of the order (`oltN`).  The
coding (`Epsilon0.lean`) is

```
code 0                      ↦ the ordinal 0
mkO e c r = ⟪e, ⟪c, r⟫⟫ + 1  ↦ ω^(e)·(c+1) + (r)
```

and it is a **bijection** `ℕ ≅ {CNF trees}` (`mkO_oE_oC_oR`): the rule's
`∀x` ranges over exactly the notations, with no undecodable codes.

*One tempting alternative is a trap, and is worth recording.*  Since
Phase B already represents `n` hereditarily in base `k`, one could code a
notation by the natural number whose hereditary base-2 representation it
is — no new coding at all.  That collapses the phase: the map
`n ↦ ord₂(n)` is *order-preserving*, so `≺` becomes `<` on `ℕ`, and
`tiEps0` becomes ordinary course-of-values induction, derivable from
Phase 2's `ind`.  (Hereditary base-2 reaches only ordinals whose Cantor
normal form has all coefficients `1`, an initial segment of order type
`ω` — which is exactly why it is order-isomorphic to `ℕ` and exactly why
it is useless here.)  The coding above avoids this: it is not
order-preserving, and the kernel-verified Goodstein instance in
`TransfiniteInduction.lean` shows the descent `9 ≻ 2 ≻ 10 ≻ 3 ≻ 1 ≻ 0`
*increasing* numerically at its second step.

### Canonicity: load-bearing here — the Phase-B flag, closed

Phase B deferred canonicity of hereditary representations and flagged
that it becomes load-bearing "exactly if the ordinal assignment is
defined on arbitrary `HTerm`s".  This phase quantifies over arbitrary
notations, so the question was checked directly, as the brief required.
**The answer is that canonicity is not optional, and the failure is not
subtle.**  On arbitrary CNF trees the comparison admits an infinite
descending chain:

```
ω  ≻  1 + ω  ≻  1 + (1 + ω)  ≻  1 + (1 + (1 + ω))  ≻  …
```

Every step wins by comparing head exponents (`0 ≺ 1`), and every term in
the chain denotes the *same* ordinal `ω`, since `1 + ω = ω`.  Two
representations of one ordinal, ranked strictly — precisely the ambiguity
Phase B could defer.  Machine-checked witnesses:
`precB_onePlus_omega`, `precB_onePlus_onePlus_omega`,
`nfB_onePlus_omega`.

Resolution, per the brief's first option: the order the rule uses
(`oltB`) is the comparison **conjoined with the normal-form predicate**
`nfB` — hereditarily, the remainder's head exponent strictly below the
head exponent.  This is the `NFBelow`/`NF` layer Phase B deferred, now
built.  Two consequences worth being explicit about:

* the rule's *conclusion* is still unrestricted (`∀x φ(x)` for every
  natural number, not only for normal codes): a non-normal code has no
  `≺`-predecessors, so progressiveness proves `φ` of it outright.  No
  side condition of `tiEps0` mentions normality;
* nothing in the phase quantifies over "some representation of an
  ordinal" — the assignment `ordOf` is again a deterministic function,
  as `hrep` was.

### What Lean needed — the brief's prediction, corrected

The brief predicted that no well-foundedness theorem would be needed:
the recursor was to be built by structural recursion on the notation's
subterms, and Lean's acceptance of that recursion was to be the formal
counterpart of Gentzen's "direct inspection of a concretely presented
notation system".  **The prediction does not hold, and the reason is
structural, not technical**: `≺`-descent is not subterm descent.  From
`ω^ω` one descends to `ω^2·2 + ω·2 + 2`, a *larger* tree — Phase B's own
numbers exhibit it (`hrep 2 4` is `ω^ω`; one Goodstein step lands on the
three-summand notation for `26`).  A recursion that only reaches
subterms cannot reach the predecessors the rule quantifies over, so no
amount of care with the recursion's shape avoids the issue.

So `Epsilon0.lean` proves **`oLt_wf`**, well-foundedness of `≺` on normal
forms, and `tiRecC` is `WellFounded.fix` on it.  The brief's *point*
survives intact, and in a sharper form than the structural version would
have given:

> The proof needs no ordinals, no `Classical`, and nothing beyond what
> Lean's own inductive types provide: three nested inductions —
> accessibility of the head exponent (outer), the coefficient (middle,
> ordinary strong induction on `ℕ`), accessibility of the remainder
> (inner, itself supplied by the outer hypothesis, since a normal form's
> remainder has a smaller head exponent) — matching the three ways one
> notation can precede another.  Gentzen's answer to Hilbert's programme
> was that inspecting an explicitly presented notation system convinces
> us it is well-ordered, and that this conviction is not reducible to the
> arithmetic it justifies.  Here that inspection is a short induction the
> kernel checks, and its cost is visible in the build: `oLt_wf` needs
> `[propext, Quot.sound]`, strictly less than the
> `[propext, Classical.choice, Quot.sound]` of the realization theorems
> it underwrites.  (The other half of Gentzen's point — that the
> *arithmetic* cannot return the favour — is standard metatheory for PA,
> not something proved here for this fragment; see the citation note.)

### `Classical.choice` had to be kept out of the *definition* — and that forced a hand-rolled pairing

A constraint that shaped the module and is worth recording because it is
easy to trip over: `tiRecC`'s **definition** mentions `oLt_wf`, so every
axiom of the well-foundedness proof is inherited by `extract`, hence by
`extract_continuous`, whose budget is `[propext, Quot.sound]`.  Two
things had to be dealt with:

* **Mathlib's `Nat.pair`/`Nat.unpair` cannot be used.**  Its inverse goes
  through `Nat.sqrt`, and *every* Mathlib lemma about that pairing
  (`Nat.pair_unpair`, `Nat.unpair_left_le`, …) depends on
  `Classical.choice` — measured, not assumed.  `Epsilon0.lean` therefore
  builds the triangular (Cantor) pairing from scratch: `tri` structurally,
  the inverse by a fueled downward search, arithmetic-only proofs.  Bonus:
  it also *reduces in the kernel*, which Mathlib's does not, so the
  Phase-B practice of kernel-verified cross-checks survives into this
  phase (`ordOf_goodstein_three` is `rfl`; the descent instances are
  `decide`).
* **The `by_cases` tactic can fall back on `Classical.byCases`.**  It did,
  inside the strong-induction helper, and quietly cost `Classical.choice`
  for the whole module.  Every case split in `Epsilon0.lean` now goes
  through the explicit decidable split `decEm`, and the file's strong
  induction is proved locally rather than imported.  This is a standing
  invariant of that module, not a one-off cleanup.

### The realizer, and the level bookkeeping the rule costs

`tiRecC φ b k = app₁ (app₁ b k̂) ⟨progressiveness argument at k⟩`, the
argument returning the recursive value at `j` when handed `j` and any
realizer of `j ≺ k`.  Two structural points:

* **The order premise carries no computational content.**  `y ≺ x` is an
  *equation* of the fragment, so realizing it *is* the fact
  `oltN j k = 1`, i.e. `OLt j k` — exactly the descent the well-founded
  recursion needs.  All of the rule's content is in the recursion; none
  is in the premise.  (This is the `succNeZero`/`axiomC` design decision
  paying off in a place where it matters: had `≺` been given
  computational content, the recursor would have had to *check* the
  descent instead of receiving it.)
* **Two `dropR φ` transports are forced by levels.**  Contrast `ind`,
  whose step formula `∀x (φ(x) → φ(succ x))` let the iterate stay at one
  ambient level (recorded in the Phase-2 section as the pleasant
  surprise that the transports were not needed).  Here the antecedent is
  *itself* a `∀→` pair, so it consumes realizers of `φ(y)` two ambient
  levels below the level at which the recursion produces them.  Hence
  `MR_tiRecC`'s hypothesis `lvl φ ≤ m₂` and `derivBound`'s
  `max (derivBound D) (lvl φ + 2) + 1`.  So Phase C is the first rule
  whose realizer genuinely needs `Transport.lean` in its *recursion*, not
  only at its binders.

`MR_tiRecC` is the phase's new theorem — the counterpart of
`MR_indRecC` one level of recursion up — proved by well-founded induction
in Lean along `≺`, the "small" induction, invoked exactly once by the
`tiEps0` case of the big induction over `Deriv`.  Its three side
conditions are each used exactly once: `x ≠ y` to read `x`'s value
through the inner binder, `SubstOK (var y) φ` for `MR_subst`, and
`¬ φ.FreeIn y` for the `MR_congr` step that discards the inner binder's
assignment.

### Generic continuity against the new combinator — answered explicitly

As with `ind`, generic continuity does not come for free (`extract_tracked`
is an induction over `Deriv`, so the rule adds a case), but the invariant
needed **no strengthening and no new closure fact**.  `tiRecC_tracked`
mirrors `MR_tiRecC`: well-founded induction along `≺` gives tracking at
each *fixed* notation, and the oracle-dependent notation code is absorbed
by `tracked_apply_nat` — the same lemma rule `ind` introduced for its
iteration count.  One simplification is worth noting: the recursor's
internal case split (`j' ≺ j`) does **not** depend on the oracle, so it
is discharged index by index and `ite_tracked` is not needed.  The two
`dropR`s are covered by `liftR_dropR_tracked`.  `CollapseDemo.lean` was
not touched, and `RealizesCtQ`/`collapse_demo` cover `tiEps0`-derivations
unchanged.

### Machinery cases added, none silent

Rule count 39 → **42**: `tiEps0`, plus `precNum` (the numeral graph of
the order) and `eqCongPrec` (its congruence schema, completing the
equational kit).  `prec` joins the signature, so `Term.eval`/`vars`/
`subst`/`eval_subst`/`eval_congr` each gain a case, as does
`termEval_continuous` (`continuous2_comp₂ oltN`).  Per-rule discipline:
`extract` + `derivBound` (three cases), `soundness` (three), and
`extract_tracked` (three).  `precNum` follows the flagged Phase-B
`bumpNum` pattern for the same reason — the comparison's recursion is
course-of-values through the notation structure, not a first-order
equation schema — and, as there, the general facts about it are proved,
not axiomatized (`Epsilon0.lean`'s order constructors).

### The bridge to Phase B, and what Phase D still owes

`ordTerm` decodes a notation code into a term of Phase B's grammar
(`ordTerm_hterm : HTerm (ordTerm c)`): the notations of this phase *are*
Phase B's hereditary representations, with the base variable read as `ω`
instead of as a numeral — no second encoding, per the brief.  `ordOf k n`
is the ordinal assignment for the Goodstein sequence, clause for clause
the mirror of `hrepAux` with `mkO` for the term constructors.  Verified
in the kernel (`TransfiniteInduction.lean`): the ordinals along `G(3)`
are `ω+1, ω, 3, 2, 1, 0` (codes `9, 2, 10, 3, 1, 0`), all normal, each
strictly `≺` its predecessor, and `ordOf 3 (bumpN 2 3) = ordOf 2 3` — the
base change leaving the ordinal fixed.

Phase D's remaining obligations are stated in that module rather than
implied: (1) `nfB (ordOf k n) = true` for `2 ≤ k` (Phase B's deferred
digit-bound/exponent-ordering facts, i.e. real `hlog` theory); (2)
`ordOf (k+1) (bumpN k n) = ordOf k n` in general (the fuels differ on the
two sides, unlike Phase B's `hrepAux_eval_bump`, so a fuel-adequacy lemma
for `ordOfAux` comes first); (3) the descent
`OLt (ordOf (k+1) (bumpN k n - 1)) (ordOf k n)`.  Only (3) uses
`tiEps0`; (1) and (2) are ordinary Phase-B-style work.

**And the gap that is not ours to close here**: the fragment still has no
`∃`, so `∀m ∃s. good m s = 0` cannot be *stated*, let alone proved (open
item 3½ in QUESTIONS.md, raised during Phase B and deliberately not
folded into this phase — the transfinite-induction work turned out to be
self-contained, and `∃` touches `Formula`, `MR`, the transports and the
tracking relation, which is a phase-sized change of its own).

### Citation (checked as far as the primary text allows)

The construction is the standard one for functionals defined by
transfinite recursion on a primitive-recursive ordering: W. W. Tait,
*Functionals defined by transfinite recursion*, **Journal of Symbolic
Logic 30(2) (June 1965), 155–174**, DOI 10.2307/2270132 (Zbl
0133.25202).  Its companion is *The substitution method*, JSL 30(2)
(1965), 175–192, DOI 10.2307/2270133; the similarly-dated *Infinitely
long terms of transfinite type* (in Crossley–Dummett, eds., *Formal
Systems and Recursive Functions*, North-Holland 1965, 176–185, DOI
10.1016/S0049-237X(08)71689-6) is a **different** paper and is not the
source for this construction.

Granularity, stated plainly per the house discipline — the brief asked
for this explicitly, and Phase B's Troelstra citation is the template.
**The primary text was not accessible**; this citation is at *abstract*
granularity.  Checked directly: Cambridge Core (abstract and reference
list free, body paywalled), JSTOR (403 to this environment), Project
Euclid (the legacy URL now redirects to the homepage; JSL is no longer
hosted there), Unpaywall / OpenAlex / Semantic Scholar (all report the
DOI closed with no repository copy), the Internet Archive (no item; the
1965 conference volume is present but lending-restricted with
search-inside disabled), Google Books (nothing), zbMATH Open (metadata
and reference list, no review text), and Tait's own former homepage at
`home.uchicago.edu/~wwtx/` (now 404; its 2024-10-05 Wayback snapshot
posts 20 papers, none earlier than 1981).  Both JSL reviews — Vesley,
JSL 31(3) (1966), 509–510, and López-Escobar, JSL 40(4) (1975), 623–624 —
are likewise paywalled, the former offering only a first-page image.

What the author's abstract (free, and byte-identical to Crossref's
record) *does* verify, and all that is claimed on its authority: the
paper treats quantifier-free second-order systems of primitive recursive
arithmetic extended by rules that "have the form of definition by
transfinite recursion up to some ordinal ξ (where ξ is represented by a
primitive recursive (p.r.) ordering)"; the systems are described in
**§2**, elementary closure properties in **§3**, less elementary ones in
**§§5–7**, and "the key lemma (**Theorem 1**) needed for the reduction of
these equations to transfinite recursion is simply a sharpening of the
Brouwer-Kleene idea".  No section or theorem beyond §2, §3, §§5–7 and
Theorem 1 is cited, and **the abstract does not single out `ε₀`** — it
states the recursion for a general ordinal given by a p.r. ordering — so
no `ε₀`-specific claim is made on its authority.  (The distributed
abstract also has a lacuna after "The main results of this paper are of
two sorts:" and prints subscripts inconsistent with its own gloss; both
are the publisher's transcription, not ours.)

For the `ε₀` scheme specifically the granularity available was Tait's own
later restatement, read in full: W. W. Tait, *The substitution method
revisited*, in Feferman et al. (eds.), *Proofs, Categories and
Computations: Essays in Honor of Grigori Mints*, Tributes 13, College
Publications 2010, 231–241 (Zbl 1225.03076), obtained from the archived
copy of his homepage.  There he works in "the quantifier-free system
PRA²_{ε₀} … with definition by recursion on each ordinal α < ε₀", with
"the order type ε₀ … represented in some standard way by a primitive
recursive ordering ≺ of ω with least element 0" — the setup this phase
formalizes — and attributes to the 1965 paper by number both a
conservativity result ("Tait 1965a, Theorem 4") and a bound on the
ordinals needed ("Tait 1965a, §5").  **Those numbers are Tait's own
citations, verified in the 2010 text and not checked against the 1965
text.**  Two further pointers found in the literature — a "Theorem 3" and
a page reference "p. 163" — rest on OCR and on a paywalled paper
respectively, and are therefore *not* recorded as verified.

Kirby–Paris and Gentzen are cited here only for the *framing* (that the
fragment cannot derive the rule), which this development does not prove
and does not claim.

## Phase D (Goodstein's theorem and its extracted function): COMPLETE

Four checkpoints, each built and axiom-checked separately, as the brief
required.  The results, in order.

### D0 — `∃` added to the fragment: COMPLETE

**The flagged design question, answered: `∃` needed two new rules but no
new devices.**  Its realizability clause is

    MR ρ (∃y φ) n x  ↔  MR ρ[y ↦ fstPT x (defaultPT n)] φ n (sndPT x)

— the first component read at the canonical point *is* the witness — so
it is literally the `∨` clause with the two-valued tag generalized to a
numeral.  Consequences, all of them reuse rather than new machinery:

* `exIC` is `orI₁C` with the witness numeral in place of the constant
  tag; `exEC` is `orEC` with the tag split replaced by passing the
  witness into the environment.  The same `pairPT`/`fstPT`/`sndPT` — no
  second pairing mechanism, as the brief required;
* the transports gain one case each (`liftR_ex`/`dropR_ex`), shaped like
  `∨`'s; tracking gains `exIC_tracked`/`exEC_tracked`, which are
  `orI₁C_tracked`/`orEC_tracked` with the case split deleted;
* **`∃` costs no ambient level**: `lvl (∃y φ) = lvl φ`.  Worth recording
  as the invariant behind the level discipline: binders that *consume*
  realizers (`→`, `∀`) cost a level, binders that merely *package* them
  do not.  No `derivBound` anywhere grew.

The one place `∃` is not just `∨`: elimination's side conditions
(`FreshIn x Γ`, `¬ ψ.FreeIn x`) keep the witness from escaping its
scope.  In the soundness proof they are exactly what let `CtxR_congr`
carry the context across the environment update and `MR_congr` carry the
conclusion back.

Checkpoint (`Exists.lean`, run at every build): the fragment's first
existential theorem, `⊢ ∃s. good(3,s) = 0` with witness `5`, together
with an `exE` round trip so the elimination rule is exercised too.

```
'Realizability.good_three_ex_realized'                    … [propext, Classical.choice, Quot.sound]
'Realizability.good_three_ex_round_trip_realized'         … [propext, Classical.choice, Quot.sound]
'Realizability.good_three_ex_extract_continuous'          … [propext, Quot.sound]
'Realizability.good_three_ex_round_trip_extract_continuous' … [propext, Quot.sound]
```

`extract_continuous`'s induction gained both new cases — confirmed, not
skipped: they are `exIC_tracked` and `exEC_tracked`, and the `exE` case
threads `trackedEnv_update` because the witness enters the *environment*.

### D1 — the three named obligations: COMPLETE

All three proved (`OrdinalAssignment.lean`), and the brief's question
"did (1) and (2) turn out to be ordinary work as predicted?" is answered
**no — they were the substantial part of Phase D**:

1. `nfB_ordOf` (normality of the assignment) needed logarithm theory
   Phase B never built.  Phase B used exactly two facts about `hlog`
   (`hlog_lt`, `pow_hlog_le`); canonicity needs the *maximality* half —
   `lt_pow_hlog_succ` — and from it the digit bounds (`one_le_digit`,
   `digit_lt`), the exponent ordering (`hlog_rem_lt`), monotonicity
   (`hlog_le_hlog`), and a uniqueness lemma (`hlog_of_digits`).  It also
   needed the assignment's **monotonicity** (`precB_ordOf_of_lt`), which
   is a three-case digit comparison mirroring the three order
   constructors of Phase C.
2. `ordOf_bumpN` (base change preserves the ordinal) needed, as Phase C
   predicted, a fuel-adequacy lemma first — in fact three
   (`hlogAux_eq_of_le`, `bumpNAux_eq_of_le`, `ordOfAux_eq_of_le`), each
   with its own `_succ_eq` step, since all three recursions are fueled.
   It also needed **`bumpN` to be a well-behaved function**, which Phase
   B never established: `bumpN_mono_bound` proves strict monotonicity and
   the digit bound `r < k^e → bump r < (k+1)^(bump e)` *together*, by one
   strong induction, because each case of either half consumes the other
   at a smaller argument.  That lemma is the largest single proof in the
   phase.
3. `ordOf_descent` (the Goodstein step descends) was, as predicted, short
   — given 2, it is monotonicity applied to `bumpN k n - 1 < bumpN k n`.

**A correction to Phase C's prediction, which the brief asked to be
checked rather than assumed**: Phase C guessed that (3) would be "the one
that actually uses `tiEps0`'s machinery".  It does not.  All three
obligations are value-level arithmetic about `ℕ`, with no reference to
`Deriv`, `MR`, or the recursor; `tiEps0` enters only in D2, where the
*induction* is performed.  What (3) actually needs is (2) plus
monotonicity — and monotonicity is the same digit-comparison work as
(1), so (1) and (3) share their hard core rather than being independent.

One hypothesis had to be added: obligations 2 and 3 hold for `2 ≤ k`
only.  At `k = 1` base change is not ordinal-preserving (`bumpN 1 4 = 4`,
whose base-2 ordinal is `ω^ω` but whose base-1 ordinal is the finite
`4`).  Harmless — Goodstein bases are `s + 2` — but it is a real side
condition, unlike Phase B's unconditional statements.

```
'Realizability.nfB_ordOf'         … [propext, Quot.sound]
'Realizability.ordOf_bumpN'       … [propext, Classical.choice, Quot.sound]
'Realizability.ordOf_descent'     … [propext, Classical.choice, Quot.sound]
'Realizability.bumpN_mono_bound'  … [propext, Classical.choice, Quot.sound]
```

**File placement changed** (a structural move, no content change,
reported because it touches Phase-B and Phase-C files): `hlog`, `bumpN`,
`goodN` moved out of `Syntax.lean`, their Phase-B facts out of
`Goodstein.lean`, and `ordOf` out of `TransfiniteInduction.lean`, all
into the new `OrdinalAssignment.lean`, which sits *before* `Syntax.lean`.
Forced: `Term.eval` must consume `ordOf` (Phase D adds the `ord` symbol),
and `Soundness.lean` must consume D1's theorems (the `ordDescent` case).

### D2 — Goodstein's theorem: COMPLETE

```
goodsteinTheorem : Deriv [] (Formula.all 2 (Formula.ex 4
  (Formula.eq (Term.good (Term.var 2) (Term.var 4)) Term.zero)))
```

`⊢ ∀m ∃t. good(m,t) = 0` — the genuine statement, universally quantified
over the start value and existentially over the number of steps, with no
restriction to concrete values and no bound on either quantifier.  The
`#check` of that exact type runs at every build.

The proof is the classical ordinal descent, on the induction formula

    φ(x) := ∀s. ord(s+2, good(m,s)) = x → ∃t. good(m,t) = 0

with `m` a parameter, generalized only at the end.  Progressiveness
splits on `good(m,s) = 0` (`eqDec`): if it holds, `s` is the witness; if
not, `goodSucc` rewrites the next state into `pred (bump (s+2) …)`, the
`ordDescent` axiom gives that its ordinal is `≺ x`, and the induction
hypothesis at that ordinal — instantiated at the state `s+1` — returns
the witness.

**Two things about this derivation deserve a reviewer's attention.**

*First, the one imported fact.*  `ordDescent` is an axiom schema of the
fragment whose truth is D1's `ordOf_descent`, discharged in the
`ordDescent` case of `soundness`.  This follows the precedent of Phase
B's `bumpNum` and Phase C's `precNum`, and for the same reason: the
content is course-of-values recursion through the hereditary structure,
which is not a first-order equation schema over the fragment's terms.
What the fragment *derives* is everything else — the case split, the
gluing of `goodSucc` with the descent, the transfinite induction, and the
witness.  Stated plainly: the arithmetic of the ordinal assignment is
metatheory (proved in Lean, D1); the logic is the fragment's.

*Second, a substitution obstacle and the technique that resolves it.*
The fragment's substitution is naive, with `SubstOK` forbidding capture
outright rather than renaming.  The step wants to instantiate the
induction hypothesis `∀y. y ≺ x → φ(y)` at `ord(s+3, good(m,s+1))`,
which mentions `s` — and `s` is bound in φ.  That is a **genuine**
capture, not a spurious side condition: the substituted occurrence sits
inside φ's own `∀s`.  The derivation therefore **names the ordinal**: it
proves `∀z. (z = ord(s+3,good(m,s+1))) → ∃t. good(m,t) = 0`, instantiating
the induction hypothesis at the *variable* `z` (which captures nothing),
and then instantiates *that* at the term, with `eqRefl`.  One extra `∀`
in the derivation, nothing in the extract's structure.  This is the
general technique for naive-substitution calculi, and it is the reason
the fragment never needed α-renaming machinery.

```
'Realizability.goodstein_realized' … [propext, Classical.choice, Quot.sound]
```

The standard three, as expected — `oLt_wf`'s reduced set does *not*
propagate here, because realization goes through `soundness`, which uses
`Classical.choice` in many earlier cases.  (Continuity does keep the
reduced set; see D3.)

### D3 — the extracted function: COMPLETE, with one honest limitation

1. **Continuity applies with no modification.**
   `goodstein_extract_continuous` is a one-line corollary of
   `extract_continuous`; the generic-continuity discipline covered
   `tiEps0`, `exI`/`exE` and `ordDescent` without a per-derivation
   certificate, exactly as designed.  `[propext, Quot.sound]` — the
   reduced set survives all of Phase D.
2. **`RealizesCtQ` gives a genuine class**: `goodsteinRealizesCtQ`, the
   theorem's program as an element of `CtQ 2`.
3. **The extracted function is correct and it runs.**
   `goodsteinStopTime m` reads the witness off the realizer at ambient
   12 (the derivation's own bound).  Two separate claims, deliberately
   kept apart:

   * `goodsteinStopTime_spec : ∀ m, goodN m (goodsteinStopTime m) = 0` —
     proved from `soundness`, **for every** `m`.  This is the real
     payoff: the extracted number is a stopping time at values no
     evaluator will ever reach.
   * The evaluator's output, verbatim from the build log of
     `GoodsteinExtraction.lean`:

     ```
     info: Realizability/GoodsteinExtraction.lean:99:0: 0
     info: Realizability/GoodsteinExtraction.lean:100:0: 1
     ```

     i.e. `#eval goodsteinStopTime 0` prints `0` and
     `#eval goodsteinStopTime 1` prints `1`, both correct
     (`goodN 1 1 = 0`, kernel-checked as `goodN_one_at_one`).  Each takes
     under a second.

**The limitation, reported rather than papered over.**  `m = 2` did not
finish.  Measured, all on this machine (24 cores, single-threaded
evaluation): 110 s at the certified ambient 12 — terminated, no output;
110 s at ambient 3 (uncertified — see the Phase-D4 correction below,
this run was not a scaled-down version of the same computation); 900 s at ambient 12
— terminated, no output, with the evaluator's resident memory past
1.7 GB and still climbing.  So the failure is not a slow constant, it is
the space and time of an exponentially branching re-evaluation.  `m = 3`
was not attempted.  For contrast, the *value-level* sequence is trivial
here: `G(2) = 2, 2, 1, 0` (`#eval` returns instantly), so the stopping
time being computed is `3`.  The cause is not the Goodstein numbers, which are tiny here
(`G(2) = 2, 2, 1, 0`), but the *extract's* shape: every recursive value
is wrapped in two `dropR` transports, and `app₁`/`abs₁` duplicate their
argument at each application, so the realizer re-evaluates its own
recursive calls exponentially often in the number of Goodstein steps.
Nothing memoizes.  So the honest summary is: the extraction pipeline is
**executable, and executes correctly at 0 and 1**, but is not an
efficient program — the certified correctness statement
(`goodsteinStopTime_spec`) is what carries the content at larger inputs.
Making the extract efficient (sharing, or a transport-free realizer for
this derivation shape) is a genuine open engineering problem and is not
claimed to be solved here.

**One change to earlier phases was needed for D3**, and is flagged:
`noncomputable` was removed from the transports (`Transport.lean`) and
the extraction combinators (`Extraction.lean`).  Those markers were
defensive, not necessary — Lean compiles all of them, `PureType` values
included — and without the change `#eval` on the extract is impossible
("no executable code").  No definition's content changed; only the
modifier was deleted.

## Phase D4 (making the extracted function fast): DIAGNOSED, NOT FIXED

The brief asked for a profile first and a `@[csimp]`-based fix second.
The profile came out clean and decisive; the fix does not exist under the
brief's own constraint that every replacement be proof-backed.  Both
halves are below, with the measurements that support them.

**No Lean file changed in this phase.**  `goodsteinStopTime_spec`, its
statement and its proof, `soundness`, and the extraction algorithm are
byte-for-byte as they were at the end of D3 — `git diff` for D4 touches
only this file and QUESTIONS.md.

### The measurements

All at ambient 12 (the derivation's own bound, i.e. the level at which
the extract is certified), on this machine, by attaching tracing
implementations to the primitives with `@[csimp]` lemmas proved by `rfl`
(`dbg_trace` is definitionally transparent, so the traced pipeline is the
same function).

| | `m = 0` | `m = 1` |
|---|---|---|
| Goodstein steps to `0` | 0 | 1 |
| `tiRecC` fix-body entries | 1 | **2377** |
| distinct codes entered at | 1 | **2** |
| entries at code `0` | — | **2376** |
| `app₁` calls | 6 | **346 437** |

Two further measurements:

* **Ambient-independence.**  The same count at ambient 13: 2376 entries
  at code `0`, identical.  So the multiplier is *not* the pure-type
  transport towers, whose depth grows with the ambient level.
* **Per-entry cost is constant**: 346 437 / 2377 ≈ 146 `app₁` calls per
  entry.  Total work is therefore (entries) × (a constant), and the
  entry count is the entire story.

### Cause 1 (`WellFounded.fix`) — ruled out, with evidence

The brief asked whether evaluating `tiRecC` re-derives accessibility
proofs at every recursive call.  **It does not.**  In the generated C
(`.lake/build/ir/Realizability/Extraction.c`) the recursion is compiled
to a direct self-recursive function,
`l_WellFounded_fixC___at___00Realizability_tiRecC_spec__0`, whose body
calls itself, `l_Realizability_natPT`, `l_Realizability_app_u2081` and
`l_Realizability_oltB` — and

```
grep -cE "lean_Acc|Acc_rec|WellFounded_apply" .lake/build/ir/Realizability/Extraction.c
0
```

`Acc` is a `Prop`, so the accessibility argument is erased before code
generation; the decidable test `oltB` is all that survives of it.

Worth stating because it looks like a contradiction with Phase B: that
phase avoided `WellFounded.fix` for `hlog`/`bumpN`/`goodN` for a
*different* evaluator.  Kernel reduction (`rfl`, `decide`) does not erase
proofs, so `WellFounded.fix` genuinely blocks there.  Compiled evaluation
(`#eval`) does erase them.  Both statements are true; they are about
different machines.

### Cause 2 (unshared duplication) — confirmed, but not where the brief expected

The blowup is re-evaluation of an **identical** recursive call: 2376 of
the 2377 entries are at the same code `0`, requested over and over.  The
per-step multiplier ≈ 2400 is the number of points at which the
surrounding extract applies the recursor's abstraction — the extracted
derivation consults its induction hypothesis that many times per
Goodstein step.  Extrapolating: ≈ 1.4 × 10¹⁰ entries at `m = 2` (three
steps) and ≈ 5 × 10¹⁶ at `m = 3` (five steps).

But it is *not* redundant substitution inside a primitive, which is the
form the brief anticipated and the form `csimp` could repair.  Three
sharing variants were written and proved, then measured:

* `orECFast` — reads the major premise's `d n` once instead of twice
  (once for the tag, once for the payload);
* `exECFast` — the same duplication in `∃`-elimination;
* `tiRecCFast` — reads the notation code `ζ (defaultPT _)` once instead
  of twice (once to decide `≺`, once to recurse), and binds the
  recursive value before the inner abstraction so it is not rebuilt per
  application point.

All three are `let`-rebindings, hence definitionally equal, so
`@[csimp] theorem … := rfl` type-checks for each; all three were
compiled into the pipeline.  **Measured effect: none.**  `tiRecC`
entries 2377 → 2377; `app₁` calls 346 437 → 346 437, exactly.  Lean's
compiler was already sharing those subexpressions.  They were reverted
rather than shipped: a `csimp` that changes nothing, documented as an
optimization, would misrepresent the state of the code.

### Why no proof-backed `csimp` can fix this

The duplicated work is not *inside* any primitive; it is *how many times
the surrounding term calls it*.  `csimp` replaces what a function
computes, never how often its caller calls it — so no replacement of
`app₁`, `abs₁`, `dropR` or `tiRecC`, however clever, can collapse 2376
identical calls into one.

Collapsing them requires memoization keyed by the notation code, i.e.
state that survives across *independent evaluations of the same
expression*.  In pure Lean that is not available as a function provably
equal to the original: `Thunk` memoizes a single value, not a
`ℕ`-indexed family of function values; a lazily-expanded infinite trie of
`Thunk`s would need coinduction; and a `HashMap`/`IO.Ref` cache can only
be attached with `@[implemented_by]`, which carries **no** proof
obligation and would make every `#eval` in this development depend on
unverified code.  Since the brief requires each replacement to be backed
by a checked equality proof, that route was not taken.

What *would* fix it, recorded and out of scope: reduce how often the
extracted derivation consults its induction hypothesis (a change to the
derivation), lower `derivBound` so fewer transports are built (likewise),
or give `Fam` a memoizing representation (a change to the extraction
algorithm).  All three change the extract itself, which this brief
explicitly excludes.

### `m = 2` and `m = 3`: a performance limit, not an astronomical answer

The brief asks that these not be conflated.  They are not the same here,
and the distinction is unambiguous: **the answers are tiny.**
`G(2) = 2, 2, 1, 0`, so the stopping time is `3`; `G(3) = 3, 3, 3, 2, 1,
0`, so it is `5`.  Both are computed instantly at the value level
(`goodN`, kernel-verified in Phase B).  What is astronomical is only the
*extract's re-evaluation count* at those inputs.  So this is entirely a
performance limitation of the extracted term's evaluation, and the true
answers are small and known.

`#eval goodsteinStopTime 2` therefore still produces no output (measured
again after the sharing variants: no output at 200 s).  `m = 3` was not
attempted.  The certified content is unaffected:
`goodsteinStopTime_spec` proves `goodN m (goodsteinStopTime m) = 0` for
every `m`, including 2 and 3, and it needs no evaluation.

### Correction to a Phase-D3 measurement

D3 reported a 110 s run "at ambient 3 (uncertified, diagnostic only)" as
if it were a smaller instance of the same computation.  **It is not**,
and the D3 text has been amended.  Below the derivation's bound the
extract's reads produce junk codes, and `oltB` on a junk code runs
`unTri`'s linear search over a huge number — that run was measuring
garbage arithmetic, not a scaled-down version of the certified
computation.  The valid scaling evidence is the ambient-independence
measurement above (12 versus 13, identical counts).

## Phase D5 (closing the `ordDescent` gap): the composite is now DERIVED

D2 proved Goodstein's theorem in the fragment but imported its core step
— *bump the base, subtract one, the ordinal strictly decreases* — as a
single axiom schema.  That was the honest weak point: the fragment proved
the theorem relative to the very fact that makes it true.  This phase
removes that import.

### What changed

The schema `ordDescent` is **deleted**.  In its place the fragment has
three schemas, each a property of one function symbol, and each
corresponding to exactly one Phase-D1 theorem:

| schema | says | discharged by |
|---|---|---|
| `ordBump` | base change leaves the ordinal alone | `ordOf_bumpN` |
| `ordPredLt` | the assignment strictly decreases at `pred` | `olt_ordOf_of_lt` |
| `bumpNeZero` | bumping a nonzero number gives a nonzero number | `bumpN_ne_zero` |

and the composite is **derived inside the fragment**
(`OrdinalDescent.lean`, `Deriv.ordDescent`): from `n ≠ 0`, `bumpNeZero`
gives that the bumped value is nonzero, `ordPredLt` at the bumped base
gives the strict decrease, and `ordBump` rewrites the right-hand side
back to the original base — the rewriting step being congruence of
`prec`.  D1's obligation 3, `ordOf_descent`, is no longer assumed
anywhere; it survives in `OrdinalAssignment.lean` as the semantic twin of
what the fragment now proves.

Rule count 46 → 48 (one removed, three added).

### The derivation is not vacuous, and that is checked

`ord_descent_via_fragment` reads the *derived* descent back through
`soundness` and recovers the semantic statement

    2 ≤ k → n ≠ 0 → OLt (ordOf (k+1) (bumpN k n - 1)) (ordOf k n)

using only the three component schemas — not `ordOf_descent`, which is
proved independently.  Fragment-side derivation and metatheorem now agree
without either being defined in terms of the other, which is the check
that the syntactic proof has real content.

```
'Realizability.ord_descent_realized'           … [propext, Classical.choice, Quot.sound]
'Realizability.ord_descent_via_fragment'       … [propext, Classical.choice, Quot.sound]
'Realizability.ord_descent_extract_continuous' … [propext, Quot.sound]
```

`goodsteinTheorem` is **untouched**: the derived former has the same name
and signature as the deleted constructor, so `GoodsteinTheorem.lean`'s
derivation text is unchanged, the theorem's type is unchanged (the
spelled-out `#check` still runs at every build), and
`goodsteinStopTime`'s `#eval` still prints `0` and `1`.

### What this does *not* achieve — stated plainly

The three schemas remain **axioms of the fragment**, justified by
theorems proved in Lean rather than by derivations in the object theory.
The metatheoretic dependence is the same size as before in logical
strength; what changed is its *shape*: no imported fact is now about the
Goodstein sequence, or about a step of anything.  Each is one general
property of the ordinal assignment or of `bump`, and the Goodstein
reasoning — the case split, the descent's composition, the transfinite
induction, the witness — is entirely the fragment's own.

So: the gap is narrowed from "the theorem's core lemma is assumed" to
"three general properties of the assignment are assumed".  It is not
eliminated, and this file does not claim it is.

### What full internalization would take (scoped, not attempted)

To derive the three schemas *inside* the fragment rather than import
them, the fragment would need to become a usable arithmetic theory:

1. **New symbols with recursion equations**: `hlog`, `div`, `mod` — the
   digit decomposition is not expressible without them.
2. **An order relation.**  The fragment's atomic formulas are equations
   only.  Since D0 there is `∃`, so `m ≤ n` can be encoded as
   `∃c. m + c = n`, but every arithmetic law about it (transitivity,
   antisymmetry, compatibility with `+`/`×`/`exp`) then has to be derived.
3. **Course-of-values induction**, derived from `ind` by the standard
   bounded-quantifier trick — which needs 2 first.
4. **Phase D1 redone syntactically**: `lt_pow_hlog_succ`, the digit
   bounds, `hlog_of_digits`, `bumpN_mono_bound` (a nested strong
   induction over powers and division), `ordOf_bumpN`, monotonicity.

That is a research-scale project — building a working fragment of
elementary number theory inside the object theory — not a phase, and it
would roughly double the size of the development.  Recorded here so the
decision is informed rather than implicit.

## Hydra project, Phase H1 (tree encoding) and H2 (the move): COMPLETE

A new mathematical layer on top of the finished Goodstein work, reusing
the existing `TI(ε₀)` machinery and the realizability pipeline unchanged.
This entry covers H1 and H2 only; H3 (the ordinal assignment and its
descent proof) is the hard part and has not been started.

### H1 — finite rooted trees as natural numbers

`Hydra.lean`.  A hydra is a mutual pair of inductives — `Hydra` (a node
carrying a `Forest`) and `Forest` (a list of hydras) — rather than the
nested `Hydra := List Hydra`, because the encode/decode proofs are mutual
structural recursions and nested inductives make those fight the
recursor.  The coding is the standard list coding through **Phase C's
existing pairing**:

    ⌜nil⌝ = 0,   ⌜cons h f⌝ = ⟪⌜h⌝, ⌜f⌝⟫ + 1,   ⌜node f⌝ = ⌜f⌝

No new coding primitive was introduced.  That matters for the reason
Phase C recorded: Mathlib's `Nat.pair`/`Nat.unpair` are unusable in this
development (every lemma about them carries `Classical.choice`, and
`Nat.unpair` does not reduce in the kernel), so `Epsilon0.lean`'s
hand-rolled triangular pairing is what everything is built on.

**Both round trips are proved**, which is what makes "the fragment's `∀x`
ranges over exactly the hydras" exact rather than approximate:

* `encodeF_forestOf : encodeF (forestOf n) = n` — every natural number is
  a code;
* `hydraOf_encodeH : hydraOf (encodeH h) = h` — every tree is recovered
  from its code.

```
'Realizability.encodeF_decodeF' … [propext, Quot.sound]
'Realizability.decodeF_encodeF' … [propext, Quot.sound]
'Realizability.hydraOf_encodeH' … [propext, Quot.sound]
'Realizability.encodeF_forestOf' … [propext, Quot.sound]
```

Choice-free, as the constraint requires.  Decoding is fueled with
`pr1`/`pr2` decreasing the code, exactly as everything else in this
development.  The four smallest codes are kernel-checked
(`hydraOf_small`): `0` a bare head, `1` a root with one head, `2` the
two-deep chain, `3` a root with two heads.

### H2 — the cutting-and-regrowth step

**The rule implemented, stated precisely** (its citation is being
verified separately; see the note below):

* a **head** is a leaf — a node with no children;
* Hercules chops one head.  Let `p` be the head's parent;
* if `p` is the **root**, the head is removed and nothing grows;
* otherwise let `g` be `p`'s parent.  After the head is removed from `p`,
  the hydra grows `n` extra copies of the resulting subtree at `p`, all
  attached to `g`; the modified `p` stays where it is.

Two parameters are deliberately left open, so that the eventual theorems
quantify over them rather than baking in one reading: **which** head is
chopped, and **how many** copies grow.  `cutH n : Hydra → Hydra × Bool`
returns the new subtree together with the one bit the caller needs —
"the head I chopped was a direct child of me" — which is exactly what
tells a node whether it is the grandparent and must grow the copies.  At
the root that bit is discarded, which *is* the "parent is the root,
nothing grows" clause.

`hydraStepN : ℕ → ℕ → ℕ` is the move on codes (decode, step, re-encode) —
the value-level function a fragment symbol will evaluate by in H4 — and
`hydraSeqN start s` is the battle with `s + 1` copies grown at step `s`.

**Worked examples, kernel-verified by `rfl`** (`hydraSeq_two_heads`,
`hydraSeq_chain`, `hydraSeq_one`):

| start | battle (codes) | reading |
|---|---|---|
| `1` | `1, 0` | one head at the root: chopped, nothing grows |
| `3` | `3, 1, 0` | two heads at the root: chopped one at a time |
| `2` | `2, 3, 1, 0` | **the hydra grows**: emptying the child makes the root grow a copy of it, so one child with one head becomes two heads |

The third row is the phenomenon in miniature, and the reason H3's ordinal
assignment is needed at all: the node count goes *up* at that step, so
nothing about the tree's size is decreasing — only the assigned ordinal
is.

### The citation, now checked — and two corrections it forced

A dedicated research pass closed the item flagged below.  Three findings
change what this section originally said.

**The rule implemented is Kirby–Paris, and the battle lengths confirm
it.**  There are two *different* games in circulation and they are widely
conflated.  Wikipedia introduces a "simple hydra game" first — copies are
**bare leaves attached to the parent** — whose path-hydra battle lengths
are `1, 3, 11, 1114111`.  Kirby–Paris is the grandparent rule with the
whole post-cut subtree copied, and its lengths are `1, 3, 37, >` Graham's
number.  `37` is therefore the discriminating number: a wrong attachment
point or copy count would not land on it.  (Googology Wiki hosts a
38-state bracket trace of that 37-step battle on the 4-node path,
`File:Hydra3.svg`.)

**Verified in-session.**  Running our own `hydraStep` on the path hydras
gives

```
path 1 (2 nodes) → 1      path 2 (3 nodes) → 3      path 3 (4 nodes) → 37
```

— the published Kirby–Paris values, `37` included.  Paths 1 and 2 are
`rfl`-checked at build time (`battleLen_small`); path 3 takes ≈ 98 s, so
it is run out of band (`#eval battleLen 200 1 (encodeH (path 3))`, output
`37`) and recorded here rather than on every build.  The research pass
independently reports the same 37 under the *rightmost* strategy with
different intermediate states, which is a further check: our strategy is
leftmost, and the length is strategy-independent.

Getting there needed both halves of the pairing made fast, and both are
proved rather than assumed:

* `tri` gained a constant-time closed form (`tri_eq_triFast`, via
  `2 * tri n = n * (n + 1)`, so no division enters the induction);
* `unTri` gained an `O(log n)` **binary search** (`unTriBin`), proved
  correct by maintaining exactly the invariant `tri lo ≤ n < tri (hi + 1)`
  and closing with `unTri_unique` — those two inequalities characterise
  the answer, and Phase C had already proved them for `unTri`
  (`tri_unTri_le`, `lt_tri_unTri_succ`).

Both are attached with `@[csimp]`, so the definitions and every proof
about them are untouched; only compiled evaluation changes.  Both proofs
are `Classical`-free, preserving the module invariant that
`Epsilon0.lean` must stay at `[propext, Quot.sound]`.

**Correction on attribution — this one matters for the theorem we will
state.**  Kirby and Paris proved termination for the replication factor
equal to the round number.  Our `cutH` deliberately takes the copy count
as a parameter, so what this development will prove is the **free**
battle (arbitrary, adversarial replication).  That generalization must
**not** be attributed to Kirby–Paris 1982; it belongs to the later
literature and to Castéran's development.  Relatedly, Dershowitz and
Moser ("The Hydra Battle Revisited") record explicitly that they shift
the factor by one relative to the original — so the convention has to be
pinned rather than assumed.  Ours: `hydraSeqN` grows `s + 1` copies at
step `s`, i.e. round numbering from 1.

**Sources.**  Kirby & Paris, *Accessible independence results for Peano
arithmetic*, Bull. LMS 14 (1982), 285–293; a scan with a text layer is at
`cs.tau.ac.il/~nachumd/term/Kirbyparis.pdf`.  Castéran's Coq development
is at `rocq-community.org/hydra-battles/` (the `coq-community` URL times
out); its §2.0.1 states the rule as "`h′` is replaced by `n + 1` copies of
`h′` which share the same root", with the replication factor equal to the
round index — the same rule as ours.

**Not verified, and not claimed**: `Hydra(4) > Graham's number` and the
`f_α` growth-rate bounds (asserted by the wikis, unchecked here); and a
numeric instance of Castéran's `l_std` formula, which did not obviously
reproduce the small cases and may be an indexing offset — deliberately
left alone rather than quoted.

### One thing still flagged

**The original citation note (now superseded, kept for the record).**  The brief requires the exact regrowth
rule to be stated and cited before implementing, since the literature has
inequivalent-looking variants (copies at the grandparent versus the
parent; `n` copies at stage `n` versus adversarially many; heads as
leaves versus as edges).  The rule above is stated precisely and is the
standard Kirby–Paris one to the best of my knowledge, but the primary
text (Kirby & Paris, *Accessible independence results for Peano
arithmetic*, Bull. LMS 14 (1982), 285–293) has **not** yet been checked
directly, and no claim is made here that it has.  The worked examples
above are therefore *hand-computed from the rule as stated*, not
cross-checked against a literature source — unlike Phase B's Goodstein
values, which were checked against `WilliamAngus/Goodstein`.  This must
be closed before H3 is built on top of it.

**Evaluation blows up quickly, and that is expected.**  Hydra codes grow
explosively (regrowth multiplies subtrees, and the pairing is
quadratic), and `Epsilon0.lean`'s `tri`/`unTri` are unary/linear — fine
for the notation codes Phase C needed, too slow for hydra codes beyond
the tiny battles above, where the interpreter's stack overflows.  A
closed-form `tri` via `@[csimp]` was tried and set aside (the equality
proof needs division-free arithmetic plumbing that this light-import
module does not have).  Per the brief, evaluation efficiency is out of
scope for H1–H5; recorded here as the known first obstacle for the
visualization phase, which will need bigger battles than these.

### H3, part one: the assignment exists and descends on the worked battle

Added since the entry above.  `insertExp e c` is the Cantor normal form
of `ω^e ⊕ c` — equal exponents merge into the coefficient, a larger one
is prepended, a smaller one recurses into the remainder — fueled on
`oR c < c`, with the usual adequacy pair (`insertExpAux_succ_eq`,
`insertExpAux_eq_of_le`) and its defining equation `insertExp_pos`.  This
is the ordinal arithmetic the development previously lacked.  On top of
it, `ordOfHydra`/`ordOfForest` are a plain structural recursion needing
no fuel, and `ordOfHydraN` is the assignment on codes.

Kernel-checked (`ordOfHydraN_small`): the four smallest hydras get
ordinals `0`, `1`, `ω`, `2` — note the two-deep chain gets `ω` while two
heads get `2`.

And the point of the whole construction, also kernel-checked
(`ordOfHydraN_descends_two`, `ordOfHydraN_descends_rest`): along the
battle `2 → 3 → 1 → 0`, the assigned ordinals are `ω ≻ 2 ≻ 1 ≻ 0`.  The
first step is the one where the **tree grows** — one child with one head
becomes two heads — and it is exactly there that `ω` drops to `2`.  The
node count went up; the measure came down.

### H3 chain, steps 1–3: DONE

* **1. Totality of `≺` on normal forms** (`precB_trichotomy`,
  `precB_total`, and the form insertion needs,
  `precB_of_ne_of_not_precB`).  Phase C proved the order well-founded and
  irreflexive but never *total* — its descent always related notations
  built to be related.  The Hydra layer needs totality, and the proof is
  the same three-way induction as the comparison itself: head exponents,
  then coefficients, then remainders, the recursive calls shrinking the
  sum.
* **2. `nfB_insertExp` — insertion preserves normal form.**  Three cases
  are the normal-form destructors read back; the fourth, recursing into
  the remainder, is exactly where totality is consumed: an exponent
  neither equal to nor above the head must sit below it, which is what
  keeps the new remainder under the old head.  `oE_insertExp` and
  `insertExp_ne_zero` are the two small facts it needs.
* **3. `nfB_ordOfHydra` / `nfB_ordOfForest` — the assignment lands in
  normal form**, by mutual induction over the tree.  This is the
  precondition for *any* descent statement, since `OLt` requires
  normality on both sides.

**Step 4, first half, and a simplification.**
`precB_insertExp_self : c ≺ ω^e ⊕ c` — inserting strictly increases the
ordinal, by the same four-case recursion (bigger coefficient, bigger head
exponent, bigger remainder, then recurse).  At `e = 0` this *is* the
descent's base case, and it is recorded in that form:
`ordOfForest_cons_leaf_descends` — a node loses a head hanging off it and
its ordinal drops, which is the Kirby–Paris clause where nothing regrows.

The other half of step 4 turned out to be **already available**: the
inequality that makes arbitrarily many copies harmless — `ω^a·(m+1) ≺ ω^b`
whenever `a ≺ b` — is exactly Phase C's `precB_mkO_exp`, which says a
smaller head exponent wins *regardless of coefficient and remainder*.  No
new lemma is needed; the replication factor never appears in the
comparison.

Remaining: monotonicity of `insertExp` in each argument (replacing a
child by one of smaller ordinal lowers the parent's), and then the general
descent by induction over `cutH`'s recursion.

**Monotonicity: attempted once, reverted, and what it will take.**  The
statement is `c₁ ≺ c₂ → ω^e ⊕ c₁ ≺ ω^e ⊕ c₂` (for normal forms).  The
proof is *not* a simple recursion: the case analysis is a square, because
insertion branches on how `e` compares with the head of its accumulator,
and the two accumulators may branch differently.  So the cases are
`(branch taken for c₁) × (branch taken for c₂)` — nine, of which some are
impossible and must be excluded by totality and irreflexivity — and only
the both-recursed corner is an induction step.  A first attempt got four
of them wrong and was reverted rather than left half-proved.  Worth doing
next with the square written out explicitly before any Lean is typed;
the `precB_cases`/`precB_of_ne_of_not_precB` pair is what settles each
corner.

### The original note, superseded by step 1 above

Worth recording because it would otherwise be found mid-proof.  Before
any *general* descent theorem can even be stated, the assignment must be
shown to land in normal form (`OLt` requires normality of both sides), and
that reduces to: `insertExp` preserves `nfB`.  Three of its four cases go
through directly from `nfB_exp`/`nfB_rem`/`nfB_below`.  The fourth — where
the inserted exponent recurses into the remainder — needs to know that if
`e ≠ oE c` and `oE c ⊀ e` then `e ≺ oE c`.

That is **trichotomy of `precB` on normal forms**, and `Epsilon0.lean`
does not have it: Phase C proved irreflexivity and the three
constructors, but never needed the comparison to be *total*.  So the
dependency order for the rest of H3 is:

1. `precB` is trichotomous on normal forms (a new `Epsilon0.lean` lemma,
   by the same strong induction that `precB_ordOf_of_lt` used —
   compare head exponents, then coefficients, then remainders);
2. `insertExp` preserves normal form (needs 1);
3. `nfB (ordOfHydra h)` (mutual induction over the tree, needs 2);
4. monotonicity of `insertExp` in the inserted exponent, and
   `ω^a·(m+1) ≺ ω^b` for `a ≺ b` — the fact that makes arbitrarily many
   copies harmless;
5. the general descent theorem, by induction over `cutH`'s recursion.

`oE_insertExp` (the head of an insertion is either the inserted exponent
or the old head) is proved and is what step 2 will consume.

### What the rest of H3 needs (scoped, not started)

The assignment sends a hydra to a `≺`-notation: `ord(node [c₁,…,cₖ])` is
the Cantor normal form of `ω^{ord c₁} ⊕ … ⊕ ω^{ord cₖ}`.  Building it on
Phase C's codes means implementing, and proving monotone, the CNF *sum*
of a multiset of exponents — sorting the children's codes, collecting
equal exponents into coefficients — which is ordinal arithmetic on codes
that this development does not yet have.  The descent then needs three
facts: removing a leaf child strictly decreases a node's ordinal;
`ω^a·(m+1) < ω^b` whenever `a < b` (this is what makes arbitrarily many
copies harmless); and monotonicity of the parent's ordinal in each
child's.  D1's retrospective on the analogous Goodstein assignment called
that work the substantial part of the phase, and this one is strictly
harder because it must see the whole tree shape rather than read off a
linear hereditary notation.
