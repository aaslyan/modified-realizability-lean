# Status: milestone COMPLETE, generic continuity COMPLETE, induction (Phase 2) COMPLETE, arithmetic (Phase A) COMPLETE, hereditary base-k / Goodstein sequence (Phase B) COMPLETE

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
    Phase-A group.

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
