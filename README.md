# Modified realizability for a minimal fragment of arithmetic

A Lean 4 formalization of modified realizability: a small first-order
fragment, an extraction function turning each of its derivations into a
pure-type realizer, a soundness theorem, and a **generic continuity
theorem** covering every extracted realizer at once.

Then four theorems proved *inside* that fragment, each with its realizer
extracted, certified, and run:

| | statement | phase |
|---|---|---|
| **Goodstein** | `⊢ ∀m ∃t. good(m,t) = 0` | D2 |
| **Kirby–Paris (Hydra)** | `⊢ ∀h ∃t. hydra(h,t) = 0` | H5 |
| **Tower of Hanoi** | `⊢ ∀n∀f∀t∀v ∃k. Solves(n,f,t,v,k) ∧ MoveCount k = 2ⁿ − 1` | E3 |
| **Pascal mod 2** | `⊢ ∀n∀k. pas(n,k) = 1 ∨ pas(n,k) = 0` | F3 |

Zero `sorry`/`admit`.  `lake build` is the whole test suite: every
correctness claim is a theorem, and every axiom-budget and evaluation
claim is an embedded `#print axioms`, `#eval` or `#guard` that runs on
each build.

## What is actually delivered

**The pipeline.**  `MR` (the realizability relation, flexible in the
ambient level), `extract` (one named combinator per derivation rule),
`soundness`, and `extract_continuous` — the last saying that *every*
closed derivation's extracted type-2 realizer is continuous, with no
per-derivation certificate.  The realizers live in the pure-type
hierarchy of a companion Kleene–Kreisel development, so each has a class
in `CtQ 2`.

**Programs, not just proofs.**  Because a realizer of `∃` carries its
witness, each theorem above yields a runnable function, certified at
*every* input by soundness rather than by testing:

* `goodsteinStopTime` — Goodstein's stopping time;
* `hydraBattleLength` — the Kirby–Paris battle length;
* `hanoiSolution` / `hanoiMoves` — the actual move sequence, decoded to
  `(from, to)` pairs: `[(0,1), (0,2), (1,2)]` for two disks, the classical
  optimum;
* `pasDecide` — a decision procedure whose output, drawn as a triangle,
  is the Sierpiński gasket.

## Two things this repository is careful about

**The axiom budget is a checked invariant, not a claim.**  Realization
theorems report exactly `[propext, Classical.choice, Quot.sound]`;
continuity theorems report only `[propext, Quot.sound]`.  That forced
real design decisions — Mathlib's `Nat.pair` is unusable here because its
lemma set is choice-dependent, so the pairing is hand-rolled, and
`Epsilon0.lean` must stay `Classical`-free because its well-foundedness
proof sits inside `extract`.

**What is imported is stated exactly.**  Each headline theorem rests on a
small number of axiom schemas about single function symbols, each
discharged by exactly one Lean theorem, and each phase's section in
`STATUS.md` says which.  Where a result is proved *about* the fragment
rather than *inside* it — `hercules_wins`, Kummer/Lucas — that is said
plainly, with the obstruction named.

## Where to start

* **`READERS_GUIDE.md`** — a dependency-ordered map of every declaration
  worth reading, with §4 reproducing every claim from a clean build.
* **`HYDRA.md`** — the Hydra project (H1–H9) as one self-contained
  document.
* **`STATUS.md`** — the authoritative record: per-phase deliverables,
  design decisions *with rationale*, flagged deviations, measured
  numbers, and quoted `#print axioms` output.
* **`QUESTIONS.md`** — decision points raised and how they were settled.

If you would rather see a theorem than read one, build the project and
look at the tail of the log: `PascalExtraction.lean` prints the
Sierpiński triangle its extracted decider computes, and
`HydraDisplay.lean` prints a Kirby–Paris battle with each state's ordinal
beside it — the tree growing while the ordinal falls.

## Building

```bash
git clone <this repo> Realizability
git clone https://github.com/aaslyan/kleene-kreisel-lean   # sibling checkout, required
cd Realizability && lake build
```

The toolchain is pinned in `lean-toolchain`; elan fetches it.  The build
requires the sibling Kleene–Kreisel checkout at `../kleene-kreisel-lean`,
declared in `lakefile.lean` — it supplies `PureType`, `Assoc`, `CtQ` and
the capstone equivalence.

## Scope, stated once

Independence results are **not** formalized.  Goodstein's theorem and
Kirby–Paris are proved here in the sense of "the sequence terminates";
that Peano arithmetic cannot prove them is a different theorem, needing
machinery this development does not have, and it is claimed nowhere.
Likewise the Hanoi result is optimality *for the recursive solution
relation it defines*, not classical minimality over arbitrary legal move
sequences.  Each phase's section says what it does and does not establish.
