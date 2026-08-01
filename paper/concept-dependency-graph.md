# Concept dependency graph — *How a Proof Becomes a Program*

Built **before** drafting, per the plan. Each concept is a node. An arrow
`A → B` means *B uses A*, so a correct ordering has **every arrow pointing
forward** (A introduced before B). Nodes are grouped by the Act that
introduces them; the check at the bottom confirms no arrow points
backward, at a finer grain than the Act boundaries.

Every node is annotated with where its facts come from (dossier Fact ID,
or `src:` for direct source where the dossier predates the code — the
Fibonacci material).

---

## Nodes, in introduction order

### Act I — the hook
- **N1 Goodstein's theorem (stated)** — the sequence `good(m,·)` climbs
  astronomically yet always reaches 0. Stated, not explained. [GOOD-025, GOOD-021]
- **N2 The surprise** — proving it needs strictly more than ordinary
  arithmetic induction, yet a runnable program falls out. [ORD-017, GOOD-029/030]

### Act II — one real example, end to end
- **N3 The fragment (a small formal system we prove *inside*)** — a fixed
  object theory with its own terms, formulas, proof rules. [CORE-001/007/011]
- **N4 Formula** — the specific one: `∃s. good(3,s) = 0`. [CORE-007, GOOD-010]
- **N5 Derivation (a proof object)** — `goodThreeExDeriv`, built by `exI`
  at the witness 5 over a numeral computation. [GOOD-010, CORE-021]
- **N6 Realizer** — the computational content a proof of a formula carries. [CORE-030]
- **N7 The `∃` realizability clause** — a realizer of `∃y φ` is a pair:
  a witness, and a certificate that `φ` holds at it. [CORE-030, CORE-037]
- **N8 Witness / canonical read-off** — the first component read at the
  canonical point *is* the witness. [EXT-009, GOOD-012]
- **N9 Contentless realizer** — an equation carries no content, so its
  certificate is trivial (any object, once the equation holds). [CORE-030, EXT-008]
- **N10 `extract`** — the function turning a derivation into a realizer;
  here applied to *this* proof. [EXT-001]
- **N11 Running it** — evaluate the extracted realizer, read 5 back. [GOOD-012, GOOD-032]

### Act III — the theory, in the order Act II needed it
- **N12 Formula-indexed realizability, all connectives** — the `∃` clause's
  shape, now for `⊥,=,∧,∨,→,∀,∃` (∨ = numeric tag; → and ∀ *consume* a
  realizer; ∧ = a pair; ∃ = the pair just seen). [CORE-030]
- **N13 `lvl` (level accounting)** — `∀`/`→` cost a level, `∃` and `∧`/`∨`
  do not; *why*: consuming vs. packaging. [CORE-029, CORE-037]
- **N14 `PureType`** — the hierarchy a realizer lives in; a realizer of `φ`
  sits at `PureType (lvl-based n + 1)`. [KK-001, CORE-034]
- **N15 `CtQ` / `ctQTwoEquiv`** — the extensional collapse; the single
  *program* a closed statement denotes. [KK-002, EXT-035]
- **N16 `soundness`** — for *every* proof, the extract realizes the
  formula (Act II's one instance, made universal). [EXT-018]
- **N17 Generic continuity (stated)** — every extract is a *continuous*
  type-2 functional; deeper reason deferred. [EXT-024, EXT-025]

### Act IV — the same machine on harder proofs
- **N18 `ind` → recursion (`indRecC`)** — the fragment's ordinary
  induction; its extract is a genuine recursive program. [CORE-013, EXT-003]
- **N19 Structured witness (Hanoi)** — the witness is a move *sequence*. [HP-013, HP-020]
- **N20 Decision procedure (Pascal)** — a `∨`-tag becomes a runnable
  classifier; tabulated, it draws Sierpiński. [HP-033, HP-034]
- **N21 Strengthened induction hypothesis (Fibonacci)** — the naive
  statement fails ordinary induction; a paired invariant `(fib n, fib(n+1))`
  succeeds, the step a shift. [src: FibonacciTheorem.lean, FibonacciExtraction.lean]
- **N22 Order as `∃`, strong induction derived** — `<` is `∃d. succ s + d = t`
  (no new symbol); strong induction is *derived* from `ind`. [ES-001, ES-007]
- **N23 Capture and its two dodges (gcd)** — naive substitution captures;
  naming (fresh `∀`) and α-renaming, first used *together*. [GOOD-027, HP-017, ES-019]
- **N24 Arbitrary-ℕ Sperner** — the discrete IVT, for *any* ℕ-coloring, not
  just `{0,1}`. [ES-028, ES-029, ES-036]
- **N25 ε₀ notations + `≺` well-founded** — ordinal notations as numbers,
  their order proved well-founded by elementary means. [ORD-001, ORD-013]
- **N26 `tiEps0` → transfinite recursion (`tiRecC`)** — induction along `≺`;
  the one rule beyond ordinary logic + induction; Act II's `∃`-example now
  gets its witness *uniformly* by ordinal recursion (Goodstein). [CORE-014, EXT-004, GOOD-025/026, GOOD-032]
- **N27 No function variables → fragment/metatheorem split (Hydra)** — the
  fragment proves one encoded battle terminates but cannot *state* "for
  every strategy"; that is a separate metatheorem. [HYD-025, HYD-033, HYD-034, CORE-044]

### Act V — the constructivity audit (climax)
- **N28 `Classical.choice`, `propext`, `Quot.sound`, `#print axioms`** — the
  kernel's own trust ledger. [CONST-001..005]
- **N29 TCB verdict** — every extracted program's trusted base is
  `{kernel, propext, Quot.sound}`; the one classical axiom is confined to
  two named Mathlib lemmas *inside correctness proofs*, never in anything
  that runs. [CONST-003, CONST-006]

### Act VI — what Lean forced us to discover
- **N30 Why `lvl` has its shape** (revisit N13 as a discovery). [CORE-037]
- **N31 Why the Hydra split was forced** (revisit N27 as a discovery). [HYD-034, CORE-044]
- **N32 Why ε₀ was hand-rolled, not `Nat.pair`** — Mathlib's pairing is
  choice-dependent; reusing it would have broken N29 before it was
  provable. [ORD-003, CONST-005]
- **N33 The memoization null result** — a fully verified memo of the
  transfinite recursor changes nothing; the recursor value is `O(1)`, the
  cost is in *applications*. Measured, not guessed. [EXT-013, EXT-014]
- **N34 Descent: assumed → derived** — an imported axiom schema early on,
  later derived from three single-symbol schemas that never mention
  Goodstein. [ORD-031, ORD-032, GOOD-034]
- ~~N35 "continuity became obvious only after generalization"~~ — **CUT**:
  not substantiated in the dossier (EXT-038 supports only that continuity
  is a property of the combinators, not a claim about *when* it became
  clear).

### Act VII — closing
- **N36 The thesis** — not "one pipeline"; rather *how little machinery it
  took*: different mathematics, the same handful of moving parts. [SC5, synthesis]

---

## Forward-only check (the arrows that could have gone backward)

Each row: a *use*, the node it needs, and confirmation the need is earlier.

| Used in | Needs | Earlier? |
|---|---|---|
| N7 `∃` clause | N6 realizer, N4 formula | ✓ (N6,N4 < N7) |
| N8 witness read-off | N7 `∃` clause | ✓ |
| N10 `extract` (on this proof) | N5 derivation, N6 realizer | ✓ |
| N11 running it | N10 extract, N8 witness | ✓ |
| N12 general realizability | N7 `∃` clause (generalize the shape) | ✓ (II before III) |
| N13 `lvl` | N12 (which clauses consume) | ✓ |
| N14 `PureType` | N6 realizer, N13 `lvl` | ✓ (both earlier) |
| N15 `CtQ` | N14 `PureType`, N17 continuity | **⚠ see note** |
| N16 `soundness` | N10 extract, N12 realizability | ✓ |
| N17 continuity (stated) | N10 extract, N14 `PureType` | ✓ |
| N18 `ind`→recursion | N10 extract | ✓ (IV after III) |
| N19 Hanoi | N18 `ind`, N8 witness, N7 `∃` | ✓ |
| N20 Pascal | N12 (`∨`-tag), N10 extract | ✓ |
| N21 Fibonacci | N18 `ind`, N7 `∃`, N12 (`∧`) | ✓ |
| N23 gcd | N22 order/strong-ind, capture (N4/N5 substitution) | ✓ (N22 < N23) |
| N24 Sperner | N22 order (`<`), N18 `ind`, N7 `∃` | ✓ |
| N26 Goodstein/`tiEps0` | N25 ε₀, N18 `ind`, N7 `∃`, N2 (the promise) | ✓ |
| N27 Hydra | N26 `tiEps0`, N27's own limitation | ✓ |
| N29 TCB verdict | N28 axioms, and all of Act IV's programs | ✓ |
| N30–N34 discoveries | their Act III–V originals | ✓ (VI last) |

**The one arrow to manage carefully — N15 `CtQ` needs N17 continuity.**
Inside Act III, `CtQ` is introduced as item 3 and continuity as item 5, so
naively `CtQ → continuity` points *backward*. Resolution (adopted in the
draft): at III-3 introduce `PureType` and state only that the *program* of
a closed statement is a single extensional object, **naming** `CtQ` and
noting it needs one further property — continuity — which III-5 then
supplies. So III-3 raises the question ("what makes this collapse
well-defined?") that III-5 answers. This matches the governing principle
(each definition answers a prior question) and keeps the arrow forward: the
reader meets `CtQ` as a promissory note, redeemed two definitions later. No
full use of `CtQ` (i.e. `RealizesCtQ`) occurs before continuity is in hand.

**`ind` placement.** `ind` (N18) is first *used* in Act IV, not Act II or
III — Act II's example is witness-by-hand (`exI`, no induction), and Act III
is semantics, not proof rules. So N18 opens Act IV, before Hanoi. Forward.

**`tiEps0` / ε₀ placement.** First *used* at Goodstein (N26). Act I (N2)
plants the question "more than ordinary arithmetic"; N25/N26 answer it.
Forward: a promise in Act I, paid at Act IV-6 — not a backward reference.

**Constructivity foreshadowing.** The choice-freeness of ε₀ (N32) is *not*
front-loaded into N25/N26; the suspicion that resolves it is raised only in
Act V (N28). So `Classical.choice` is fully introduced at N28 and the ε₀
discovery sits at N34-adjacent in Act VI, after N29. No backward arrow.

**Conclusion:** with the two placements above (`CtQ` as a named promise
before continuity; `ind`/`tiEps0`/choice introduced at first use), every
arrow points forward. Drafting may proceed.
