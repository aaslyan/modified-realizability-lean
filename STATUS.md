# Status: milestone COMPLETE

`lake build` succeeds, zero `sorry`/`admit`.  `#print axioms` on the
soundness theorem and the collapse-demo theorem reports:

```
'Realizability.soundness' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'Realizability.collapse_demo' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

(likewise `MR_liftR_dropR`, `FR_famOf`, `demo_extract_eq`,
`demo_extract_continuous`).

## What is delivered

- `Syntax.lean` — terms, the fragment's formulas, capture-safe
  substitution, and the 16-rule natural-deduction family.
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
- `CollapseDemo.lean` — `RealizesCtQ` (the class of a closed
  derivation's extracted type-2 realizer in `CtQ 2`, via the parent
  project's capstone equivalence `ctQTwoEquiv`), and the named demo:
  `demoDeriv₁`/`demoDeriv₂`, two different derivations of
  `A ∧ B → B ∧ A` whose extracted terms are proved equal as functionals
  (`demo_extract_eq`) and hence denote the same element of `CtQ 2`
  (**`collapse_demo`**), with the continuity certificate proved
  concretely (`demo_extract_apply`, `demo_extract_continuous`).

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
    true-equation implication clauses).

## Design decisions and deviations (flagged)

- **Flexible ambient level.**  `MR ρ φ n x` is defined at every ambient
  `n`, all clauses at one level with binders stepping down — no level
  coercion occurs in the definition.  The coercions concentrate in the
  transports, which extraction alone needs.
- **`Realizes` in `CtQ`, at the demo's level.**  `RealizesCtQ` lands in
  `CtQ 2` via `ctQTwoEquiv`, for closed derivations whose extracted
  type-2 realizer is continuous — certified concretely for the demo.
  The brief's fully general `CtQ`-valued soundness (every derivation at
  every level) additionally needs a *generic* continuity/countability
  theorem for extracted functionals (each combinator preserves having
  associates) — identified, not attempted: it is precisely the
  associate-level closure layer of the parent project's deferred
  finite-types chapter.  No partial credit is claimed.
- The `→` clause of `MR` is the `Assoc`/`CtPer` clause *shape* at the
  level of pure functionals; the literal `Assoc`-instance reading enters
  through the `CtQ` packaging, not as a redundant re-proof.

## Why induction is excluded (specification for the long-term plan)

The induction axiom's realizer is the recursor: from realizers of
`φ(0)` and `∀x (φ(x) → φ(succ x))`, iterate application `n` times to
realize `φ(n)`.  With the transports now in place, exactly one new
theorem is required: closure of `MR` under primitive recursion at every
ambient level — the pure-type counterpart of Kleene's S1–S8
primitive-recursion clauses.  The iterate crosses implication levels,
which is what the transports were built for; the statement is closable,
not open-ended.  Everything else induction needs (families at binders,
substitution, environment congruence) already exists.

## Out of scope (per the brief)

Full first-order quantification with unbounded nesting beyond the one
`∀`-pair; Dialectica; any claim of soundness for HA.
