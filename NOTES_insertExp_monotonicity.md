# Working notes: monotonicity of `insertExp`

Two attempts, neither landed, both worth keeping — the first because its
failure mode is specific and repeatable, the second because it found the
actual blocker.  Nothing here is committed Lean; the tree has never held
a half-proved version of this lemma.

## The statement

In `Realizability/Hydra.lean`, `insertExp e c` is the Cantor normal form
of `ω^e ⊕ c`.  The needed lemma is monotonicity in the accumulator:

```lean
theorem precB_insertExp_mono {e : ℕ} (he : nfB e = true) :
    ∀ c₂ c₁ : ℕ, nfB c₁ = true → nfB c₂ = true → precB c₁ c₂ = true →
      precB (insertExp e c₁) (insertExp e c₂) = true
```

Why it is needed: `ordOfForest` folds `insertExp` over a node's children,
so "replacing a child by one of smaller ordinal lowers the parent's
ordinal" — the inductive step of the Hydra descent — is exactly this.

Recall the four branches of `insertExp e c`, writing `E = oE c`:

| tag | condition | value |
|---|---|---|
| **Z** | `c = 0` | `mkO e 0 0` |
| **A** | `e = E` | `mkO E (oC c + 1) (oR c)` (merge into the coefficient) |
| **B** | `e ≠ E`, `E ≺ e` | `mkO e 0 c` (prepend; `e` becomes the head) |
| **C** | `e ≠ E`, `¬(E ≺ e)` | `mkO E (oC c) (insertExp e (oR c))` (recurse) |

## Attempt 1 — Lean first (reverted)

Structure written: `nat_strong_ind` on `c₂`, then `rcases decEm (c₁ = 0)`,
then `rcases precB_cases hc₁ hc₂ h12` into "`c₁` has the strictly smaller
head exponent" versus "equal head exponents", and inside each, a
`decEm`-cascade on `c₂`'s branch with a nested cascade on `c₁`'s branch in
some arms but not others.

Lean rejected four corners.  The messages, and what each actually meant:

1. `precB_mkO_exp … hp₁` — *argument has type `precB (oE c₁) e = true`,
   expected `precB e e = true`*.  The constructor was applied with the
   wrong pairing of head exponents: I had `c₁` in branch **B** (head `e`)
   and `c₂` in branch **A** (head `oE c₂ = e`), so both heads are `e` and
   the *exponent* constructor does not apply at all — that corner is a
   coefficient comparison.
2. `precB_mkO_rem … h12` — *got `precB (mkO _ _ c₁) (mkO _ _ c₂)`,
   expected `precB (insertExp e c₁) (mkO e 0 c₂)`*.  I had reduced the
   right-hand accumulator to its branch but left the left-hand one as an
   unreduced `insertExp`.
3. `rw [← insertExp_pos hc₁]` — *pattern not found*.  Same mistake in the
   other direction: trying to re-fold a branch that was never unfolded.
4. `precB_mkO_coeff … hcc` — *expected the goal's right side to be an
   `mkO`, found an `if`*.  Again one side unreduced.

**Diagnosis, which is the useful part.**  Three of the four are the same
error: the proof must case-split on **both** accumulators' branches
*before* applying any order constructor, so that both sides of the goal
are in `mkO` form simultaneously.  My cascade split on `c₂` first and on
`c₁` only inside some arms, so several corners reached a constructor with
one side still an `if`.  The fix is not a patch — it is to enumerate the
grid up front.

## Attempt 2 — the grid on paper first

Enumerating `(branch for c₁) × (branch for c₂)`:

**Row Z (`c₁ = 0`).**  All three settle immediately, with no induction:

| `c₂` | goal | settled by |
|---|---|---|
| A | `mkO e 0 0 ≺ mkO e (oC c₂ + 1) (oR c₂)` | `precB_mkO_coeff`, `0 < oC c₂ + 1` |
| B | `mkO e 0 0 ≺ mkO e 0 c₂` | `precB_mkO_rem`, `precB_zero_left` |
| C | `mkO e 0 0 ≺ mkO (oE c₂) (oC c₂) …` | `precB_mkO_exp`, `e ≺ oE c₂` |

**Rows with `oE c₁ = oE c₂` (from `precB_cases`, second disjunct).**  Both
accumulators compare `e` against the *same* head, so they take the *same*
branch — the grid collapses to its diagonal:

| branch | goal | settled by |
|---|---|---|
| A | coefficients `oC c₁ + 1 < oC c₂ + 1`, or equal with `oR c₁ ≺ oR c₂` | `precB_mkO_coeff` / `precB_mkO_rem` |
| B | `mkO e 0 c₁ ≺ mkO e 0 c₂` | `precB_mkO_rem`, hypothesis `c₁ ≺ c₂` |
| C | same head and coefficient, remainders recursed | `precB_mkO_rem` + **induction hypothesis** at `oR c₂` |

This is the only place the induction is used.

**Rows with `oE c₁ ≺ oE c₂` (first disjunct).  This is where it breaks.**
To know which branch `c₁` takes, one must chain the branch condition on
`c₂` with `oE c₁ ≺ oE c₂`:

* `c₂` in **B** means `oE c₂ ≺ e`; to place `c₁` one needs
  `oE c₁ ≺ e` — that is **transitivity**;
* corners like "`c₁` in **A**, `c₂` in **B**" (so `e = oE c₁` and
  `oE c₂ ≺ e`, i.e. `oE c₂ ≺ oE c₁`) must be excluded against
  `oE c₁ ≺ oE c₂` — that is **asymmetry**.

## Conclusion: a missing prerequisite, and it is not Hydra-specific

`Epsilon0.lean` proves `≺` well-founded (`oLt_wf`) and irreflexive
(`precB_irrefl`), and the Hydra work added totality
(`precB_trichotomy`).  It has **never** proved transitivity or asymmetry,
because nothing before now compared three notations at once: Goodstein's
descent only ever related two notations built to be related.

So the order of work is:

0. **`precB` transitive on normal forms** — same nested induction as
   trichotomy (head exponents, then coefficients, then remainders),
   comparable size.  Asymmetry then follows from transitivity plus
   `precB_irrefl`.
1. monotonicity, via the grid above — with rows Z and "equal heads"
   already worked out here, and the "smaller head" rows becoming routine
   once 0 is available.
2. the general Hydra descent, whose root case is already proved
   (`ordOfForest_cons_leaf_descends`) and whose deeper case is 1 plus
   `precB_mkO_exp`.

Once 0 lands, `≺` is a full strict linear order on normal forms and there
should be no further order property left to discover — this is the third
time a "mechanical" step turned out to rest on an unproved structural
fact (canonicity in Phase C, then totality, now transitivity), and the
pattern has a natural end point.
