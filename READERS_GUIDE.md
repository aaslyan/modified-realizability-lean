# Reader's guide

For a full manual read-through of the proof, start to finish.  This is a
map, not a substitute: every claim below is checkable against the Lean
source, and §4 reproduces every "done means" claim from scratch.

The one-sentence version of what is proved: **the fragment derives
`∀m ∃t. good(m,t) = 0`, and modified realizability turns that derivation
into a program that computes the Goodstein stopping time, certified
correct at every input and continuous as a type-2 functional.**

---

## 1. Dependency-ordered theorem map

Read in this order.  Each entry is `declaration` — file — what it
establishes.  The order is logical, not chronological: phase labels are
noted only where they help.

### 1.1 The notation system and its order (read first — everything else consumes it)

| # | Declaration | File | What it gives you |
|---|---|---|---|
| 1 | `tri`, `pr`, `pr1`, `pr2`, `pr_pr1_pr2` | `Epsilon0.lean` | A hand-rolled triangular pairing `ℕ ≅ ℕ²`, choice-free and kernel-computable.  Read `pr_pr1_pr2` (surjectivity) and move on. |
| 2 | `mkO`, `oE`, `oC`, `oR`, `mkO_oE_oC_oR` | `Epsilon0.lean` | Ordinal notations below `ε₀` **as natural numbers**: `mkO e c r` codes `ω^e·(c+1) + r`, and the destructors invert it exactly.  The coding is a bijection, so the fragment's `∀x` ranges over exactly the notations. |
| 3 | `precAux`, `precB`, `precB_pos` | `Epsilon0.lean` | Cantor-normal-form comparison, fueled.  `precB_pos` is the characterization you will use everywhere. |
| 4 | `nfB`, `nfB_pos`, `nfB_mkO` | `Epsilon0.lean` | The normal-form predicate (strictly decreasing exponents, hereditarily). |
| 5 | `precB_onePlus_omega`, `nfB_onePlus_omega`, `not_olt_onePlus_omega` | `Epsilon0.lean` | **Why normal forms are not optional**: `ω ≻ 1+ω ≻ 1+(1+ω) ≻ …` is an infinite descent in the bare comparison, through terms all denoting `ω`.  Machine-checked. |
| 6 | `oltB`, `OLt`, `oltN` | `Epsilon0.lean` | The order the rule actually uses: comparison **conjoined with** normality.  `oltN` is its characteristic function, the semantics of the `prec` symbol. |
| 7 | `acc_zero`, `acc_mkO`, `acc_of_nf`, **`oLt_wf`** | `Epsilon0.lean` | **Well-foundedness.**  `acc_mkO` is the heart: three nested inductions (head exponent's accessibility, coefficient, remainder's accessibility) matching the three ways one notation can precede another.  No ordinals, no `Classical`. |

### 1.2 The value-level Goodstein functions and the ordinal assignment

| # | Declaration | File | What it gives you |
|---|---|---|---|
| 8 | `hlog`, `bumpN`, `goodN` | `OrdinalAssignment.lean` | The functions the fragment's symbols evaluate by (Phase B; moved here in Phase D).  All fueled, all kernel-computable. |
| 9 | `lt_pow_hlog_succ`, `one_le_digit`, `digit_lt`, `hlog_rem_lt`, `hlog_of_digits` | `OrdinalAssignment.lean` | Logarithm theory: maximality, the digit bounds, the exponent ordering, and uniqueness of a digit decomposition.  Phase B needed none of this; canonicity needs all of it. |
| 10 | `bumpN_pos_eq`, **`bumpN_mono_bound`** | `OrdinalAssignment.lean` | `bumpN` as a *function*: strictly monotone, and respecting the digit bound.  Proved together by one strong induction — the largest single proof in Phase D.  Read the docstring first. |
| 11 | `ordOf`, `ordOf_pos` | `OrdinalAssignment.lean` | **The ordinal assignment**: `ordOf k n` is the code of the ordinal of `n`'s hereditary base-`k` representation read at base `ω`. |
| 12 | `precB_ordOf_of_lt`, **`nfB_ordOf`**, `olt_ordOf_of_lt` | `OrdinalAssignment.lean` | D1 obligation 1: the assignment is monotone and lands in normal form. |
| 13 | **`ordOf_bumpN`** | `OrdinalAssignment.lean` | D1 obligation 2: bumping the base does not change the ordinal. |
| 14 | **`ordOf_descent`** | `OrdinalAssignment.lean` | D1 obligation 3: one Goodstein step strictly decreases the ordinal.  This is the mathematical content of the whole development. |

### 1.3 The fragment

| # | Declaration | File | What it gives you |
|---|---|---|---|
| 15 | `Term`, `Term.eval`, `numeral` | `Syntax.lean` | Terms over `{0, succ, +, ×, pred, exp, bump, good, prec, ord}`. |
| 16 | `Formula`, `FreeIn`, `subst`, `SubstOK`, `FreshIn` | `Syntax.lean` | Formulas (`∧∨→⊥`, `∀`, and since D0 `∃`) and the substitution bookkeeping. |
| 17 | **`Deriv`** | `Syntax.lean` | The 46-rule natural-deduction family (39 before Phase C; `tiEps0`, `precNum`, `eqCongPrec`, then `ordDescent`, `eqCongOrd`, `exI`, `exE`).  Read the constructor list in order; the comments mark which phase added what. |

### 1.4 Realizability, extraction, soundness

| # | Declaration | File | What it gives you |
|---|---|---|---|
| 18 | `PureType` (parent project), `up`/`down`, `pairPT`/`fstPT`/`sndPT`, `app₁`/`abs₁`, `app₁_abs₁` | `ModifiedRealizes.lean` | The pure-type devices.  Everything else is built from these five. |
| 19 | `lvl`, **`MR`** | `ModifiedRealizes.lean` | The flexible-ambient realizability relation.  Read the `∃` clause against the `∨` clause — they are the same shape. |
| 20 | `MR_congr`, `MR_subst` | `ModifiedRealizes.lean` | Environment congruence and the substitution lemma. |
| 21 | `liftR`, `dropR`, **`MR_liftR_dropR`**, `famOf`, `FR_famOf` | `Transport.lean` | The level transports and the family generator: how a binder's one-ambient realizer serves a body that uses it at many ambients. |
| 22 | `extract` (and its combinators), `derivBound` | `Extraction.lean` | One named combinator per rule.  The two that *recurse* are `indRecC` (along `succ`) and **`tiRecC`** (along `≺`) — read `tiRecC` and `tiRecC_eq` carefully; they are where the transfinite content lives. |
| 23 | `MR_indRecC`, **`MR_tiRecC`** | `Soundness.lean` | The two "small" inductions: closure of `MR` under primitive recursion, and under transfinite recursion along `≺`. |
| 24 | **`soundness`** | `Soundness.lean` | The big induction: every derivation's extract realizes its conclusion. |

### 1.5 Continuity

| # | Declaration | File | What it gives you |
|---|---|---|---|
| 25 | `Tracked`, `abs₁_tracked`, `tracked_apply_nat` | `GenericContinuity.lean` | The oracle-parameterized logical relation, abstraction closure by β-reduction, and the closure fact both recursors need. |
| 26 | `tiRecC_tracked`, `tiC_tracked`, `exIC_tracked`, `exEC_tracked` | `GenericContinuity.lean` | The Phase-C and Phase-D preservation lemmas. |
| 27 | `extract_tracked`, **`extract_continuous`** | `GenericContinuity.lean` | Every closed derivation's extract is `Continuous2`. |
| 28 | `RealizesCtQ`, `collapse_demo` | `CollapseDemo.lean` | The extract's class in `CtQ 2`, total on closed derivations. |

### 1.6 What the fragment proves

| # | Declaration | File | What it gives you |
|---|---|---|---|
| 29 | `plusZeroDeriv` … `timesSuccDeriv` | `Arithmetic.lean` | The four `+`/`×` equations as genuine `ind` theorems (Phase A). |
| 30 | `hrep`, `hrep_eval_self`, `hrep_eval_bump`, `goodComputeDeriv`, `goodN_four`, `goodN_three` | `Goodstein.lean` | Hereditary representations as terms of the fragment; the sequence computed inside the fragment; the cross-checks against `WilliamAngus/Goodstein`. |
| 31 | `ordTerm_hterm`, `ordOf_goodstein_three`, `ordOf_goodstein_three_descends` | `TransfiniteInduction.lean` | The notations *are* Phase B's `HTerm` grammar read at base `ω`; and the kernel-verified descent `9 ≻ 2 ≻ 10 ≻ 3 ≻ 1 ≻ 0` along `G(3)` — note it is not numerically decreasing. |
| 32 | `tiDemoDeriv` | `TransfiniteInduction.lean` | `tiEps0` exercised end to end. |
| 33 | `goodThreeExDeriv`, `good_three_ex_witness` | `Exists.lean` | The fragment's first existential theorem, and the witness read off its realizer. |
| 34 | `descentDeriv`, `namedIHDeriv`, `stepBranch`, `goodProgressive` | `GoodsteinTheorem.lean` | The four pieces of the induction step.  `namedIHDeriv` is the substitution trick — read its docstring. |
| 35 | **`goodsteinTheorem`** | `GoodsteinTheorem.lean` | `⊢ ∀m ∃t. good(m,t) = 0`. |
| 36 | `goodsteinStopTime`, **`goodsteinStopTime_spec`**, `goodstein_extract_continuous`, `goodsteinRealizesCtQ` | `GoodsteinExtraction.lean` | The extracted function, its correctness at every input, its continuity, and its class in `CtQ 2`. |

---

## 2. The four sub-phases in plain language

**D0 — the existential quantifier.**  The fragment had no `∃`, so
Goodstein's theorem could not even be stated.  Adding it was cheap
because modified realizability treats `∃y φ` almost exactly like a
disjunction: a realizer is a pair whose first component is the witness
and whose second realizes `φ` there, so the existing pairing devices did
all the work and no new ambient level was needed.  The two new rules are
the standard introduction and elimination, with elimination carrying the
usual freshness conditions that stop the witness escaping its scope.

**D1 — the three obligations.**  These are facts about numbers, not
about derivations: that the ordinal assignment always produces a *normal*
notation, that bumping the base leaves the ordinal unchanged, and that
one Goodstein step strictly decreases it.  The first two turned out to be
the substantial work of Phase D — they need real logarithm theory (that
`hlog` is maximal, hence that digits are bounded and exponents strictly
decrease) and a proof that `bumpN` is strictly monotone and bound-
respecting, which Phase B had never needed.  The third is then short: given
base-change invariance, the descent is just monotonicity applied to
"subtract one".

**D2 — Goodstein's theorem.**  Transfinite induction along `≺` on the
formula "every state of the sequence whose ordinal is `x` eventually
reaches `0`", with the start value as a parameter.  If the current value
is `0` we are done and the step count is the witness; otherwise the next
state's ordinal is strictly smaller, so the induction hypothesis applies
to it and hands back a witness.  The only fact imported from the
metatheory is D1's descent, which enters as the axiom schema
`ordDescent`; the case analysis, the gluing with `goodSucc`, the
induction and the witness are all the fragment's own work.

**D3 — the extracted function.**  Because the realizer of an existential
carries its witness, the derivation *is* a program: apply the extracted
realizer to a start value and read the first component.  That function is
proved correct for every input by instantiating soundness — no
computation involved — and it is continuous by the generic continuity
theorem with no new argument.  It also literally runs, though only for
the smallest inputs: the extract re-evaluates its own recursive calls
through the transport towers, so cost explodes with the number of
Goodstein steps.

---

## 3. Design decisions made in this brief (apply extra scrutiny here)

These were *not* dictated by the brief.  Each is a place where a
reviewer should check that the choice is sound and that nothing was
quietly weakened.

1. **`∃` reuses `∨`'s machinery rather than getting its own** (the
   expected example).  `exIC`/`exEC` are built from `pairPT`/`fstPT`/
   `sndPT`, and `lvl (∃y φ) = lvl φ`.  Check: is the `MR` clause for `∃`
   the standard one, and does the level assignment make `derivBound`
   sound?  (`Exists.lean` header; `ModifiedRealizes.lean` `MR`.)
2. **`∃`-elimination's side conditions.**  I chose `FreshIn x Γ` and
   `¬ ψ.FreeIn x` — the standard pair.  Check they are strong enough in
   the soundness case (`Soundness.lean`, `exE`).
3. **The `ord` symbol was added to the signature.**  Phase D2 needs to
   *speak* about the ordinal of a state, and the fragment has only
   equations between terms, so the assignment had to become a function
   symbol.  Check: does anything in the theorem depend on `ord` having
   properties beyond the one axiom below?
4. **`ordDescent` as an axiom schema, and only that one.**  I considered
   splitting it into `ordBump` + `ordPredLt` + `bumpNeZero` and deriving
   the composite, which would have been more granular; I kept one schema
   because it is exactly D1's theorem, so the soundness case is a single
   application with nothing hidden in the gluing.  Check: is the schema
   *true* as stated (base `≥ 2` is built into its shape), and is its
   soundness case really `ordOf_descent`?
5. **The "name the ordinal" trick** instead of adding α-renaming to the
   fragment.  This is the subtlest choice in Phase D.  Check that the
   capture it avoids is genuine (it is: the substituted term mentions `s`,
   which φ binds) and that the extra `∀z` does not weaken the theorem.
   (`GoodsteinTheorem.lean`, `namedIHDeriv`.)
6. **`2 ≤ k` on D1 obligations 2 and 3.**  Not in the brief; forced,
   because base change is not ordinal-preserving at `k = 1`.  Check that
   every use site supplies a base of the form `s + 2`.
7. **Moving `hlog`/`bumpN`/`goodN`/`ordOf` into `OrdinalAssignment.lean`.**
   A structural move with no content change, forced by the module order
   (`Soundness.lean` needs D1's theorems).  Check that nothing was
   silently altered in transit.
8. **Removing `noncomputable` from the transports and the extraction
   combinators.**  Required for D3 to run at all.  Check that the
   definitions are otherwise untouched.
9. **Formula abbreviations in `GoodsteinTheorem.lean` are `abbrev`, not
   `def`.**  Needed so `decide` can discharge the side conditions.  A
   reviewer should confirm the side conditions really are being *proved*
   (they are — by `decide +kernel` on decidable predicates), not assumed.
10. **Reusing variable `5` for both the transfinite-induction binder and
    the naming variable.**  Deliberate: it is what keeps the `allE` at
    `var 5` capture-free.  Check the variable convention table at the top
    of `GoodsteinTheorem.lean`.

Carried over from earlier phases, restated because they bear on Phase D:
`bumpNum`/`precNum` are numeral-graph axioms (Phases B/C), and Phase C's
order is only well-founded on normal forms.

---

## 4. Reproducing every claim from a fresh clone

```bash
# 1. Both repositories, side by side (the path dependency is hard-coded).
git clone https://github.com/aaslyan/kleene-kreisel-lean.git
git clone https://github.com/aaslyan/modified-realizability-lean.git Realizability
cd Realizability

# 2. Build everything.  Toolchain (leanprover/lean4:v4.26.0) is pinned in
#    lean-toolchain; elan fetches it automatically.
lake build

# 3. Zero placeholders.
grep -rn "sorry\|admit" Realizability/*.lean            # expect: no matches
```

`lake build` already prints every `#print axioms` result and every
`#eval` in the development.  To check the Phase-D claims individually:

```bash
cat > /tmp/check.lean <<'EOF'
import Realizability.GoodsteinExtraction
namespace Realizability

-- D2: the theorem, at exactly the claimed type
#check (goodsteinTheorem :
  Deriv [] (Formula.all 2 (Formula.ex 4
    (Formula.eq (Term.good (Term.var 2) (Term.var 4)) Term.zero))))

-- D1: the three obligations
#print axioms nfB_ordOf
#print axioms ordOf_bumpN
#print axioms ordOf_descent

-- D0/D2/D3: realization, continuity, extraction
#print axioms good_three_ex_realized          -- D0
#print axioms goodstein_realized              -- D2
#print axioms goodsteinStopTime_spec          -- D3, correctness at every input
#print axioms goodstein_extract_continuous    -- D3, continuity
#print axioms extract_continuous              -- the generic theorem
#print axioms soundness

-- D3: the extracted function, running
#eval goodsteinStopTime 0                     -- 0    (<1 s)
#eval goodsteinStopTime 1                     -- 1    (<1 s)
-- #eval goodsteinStopTime 2                  -- does NOT finish; see STATUS.md
end Realizability
EOF
lake env lean /tmp/check.lean
```

Expected output, in order: the `#check` echoing
`goodsteinTheorem : Deriv [] (Formula.all 2 goodTerminates)` — note Lean
*displays* the abbreviation `goodTerminates`, but the ascription in the
`#check` is the spelled-out `Formula.ex 4 (Formula.eq …)`, so what was
checked is the unfolded type;
`nfB_ordOf … [propext, Quot.sound]`; the other two obligations and every
`_realized` at `[propext, Classical.choice, Quot.sound]`; both
`_continuous` at `[propext, Quot.sound]`; then `0` and `1`.

The build itself is the strongest check: it fails if any `#print axioms`
line disagrees only in the sense that a reviewer reading the log will see
it, so read the log rather than trusting this file.
