# Status: IN PROGRESS — semantic core complete, extraction blocked on a
# real (and now precisely identified) infrastructure need

## What is built and green (`lake build`, zero `sorry`)

- `Syntax.lean` — terms (`var`/`zero`/`succ`), formulas of the fragment
  (`⊥`, `≐`, `∧`, `∨`, `→`, one `∀`; `¬φ := φ → ⊥`), substitution with
  capture side conditions, and the natural-deduction family `Deriv` with
  all 16 rules of the fragment (ax, wk, andI, andE₁, andE₂, orI₁, orI₂,
  orE, impI, impE, botE, allI, allE, eqDec, succNeZero, succInj).
- `ModifiedRealizes.lean` — the pure-type device layer (`up`/`down`
  section-retraction, pointwise pairing `pairPT`/`fstPT`/`sndPT`,
  application/abstraction `app₁`/`abs₁` with the beta law), the level
  function `lvl`, and the **flexible-ambient** realizability relation
  `MR ρ φ n x` with realizers `x : PureType (n+1)` — plus the two
  stability lemmas the quantifier rules need: `MR_congr` (environment
  congruence on free variables) and `MR_subst` (the substitution lemma).

Design vindicated so far: the flexible ambient level eliminates the
entire level-padding layer from the *definition* of realizability — all
clauses stay at one ambient, binders step down by one, and no coercion
between mismatched levels ever occurs in `MR`.

## The finding that blocks extraction (and what it will take)

Extraction hits a precise obstruction: **binders provide realizers at
one ambient level, bodies consume them at several.**  An `impI`
abstraction binds its hypothesis-realizer `x` at a single ambient `m`
(that is what the `MR` implication clause supplies), but the body's
recursive extraction uses hypotheses at shifted ambients whenever it
applies them (`impE` consumes its major premise one ambient up).  Every
architectural variant tried — curried contexts with under-binder
transformations, family-valued realizers, ambient-local semantic
extraction — reduces to the same gap.

The gap is closed by exactly one thing: **formula-indexed level
transports** `liftR φ : PT (m+1) → PT (m+2)` and `dropR φ` with
`MR`-preservation both ways, defined by mutual recursion on the formula
(the generic `up`/`down` provably do *not* preserve `MR` at implication
— the computation is in the design notes).  This is not an artifact of
this project: it is the standard "every finite type is a retract of a
pure type" machinery, forced by the brief's (correct) insistence on
reusing the pure-type hierarchy rather than introducing product/arrow
types.  It is the same infrastructure the parent project's deferred
"arbitrary finite types" chapter needs — building it here pays that
debt.

Estimated remaining work: transports with preservation (~200 lines),
per-rule extraction combinators (~300), soundness induction (~200),
`CtQ`-landing and the collapse demo (~200).

## Not yet delivered (relative to the brief)

Extraction, soundness, `Realizes` in `CtQ`, the collapse demo, and the
per-rule combinator list.  No claim is made for them; nothing partial is
committed as if finished.

## Why induction is excluded (specification for the long-term plan)

The induction axiom's realizer is the recursor: given realizers of
`φ(0)` and of `∀x (φ(x) → φ(succ x))`, iterate application `n` times to
realize `φ(n)`.  Formalizing it needs (a) the level transports above
(the iterate crosses implication levels), and (b) a closure theorem for
`MR` under primitive recursion at every ambient level — the pure-type
counterpart of Kleene's S1–S8 primitive-recursion clauses, which the
parent project deliberately does not yet have.  With the transports in
place, (b) is the single genuinely new theorem induction requires; it is
a well-posed, closable target, not an open-ended one.
