/-
# Phase H1: finite rooted trees as natural numbers

The Kirby–Paris Hydra game needs the fragment to quantify over *trees*,
and the fragment has one sort: `ℕ`.  So hydras are coded as naturals,
the same way Phase C coded ordinal notations — and, as there, the coding
is built from scratch rather than taken from Mathlib.

## Why from scratch again

Phase C's experience is the reason, and it is worth restating because it
is the constraint that shapes this file.  Mathlib's `Nat.pair`/
`Nat.unpair` were unusable there for two independent reasons: *every*
lemma about them depends on `Classical.choice` (measured, not assumed),
which would propagate into `extract` and break the continuity theorems'
`[propext, Quot.sound]` budget; and `Nat.unpair` goes through `Nat.sqrt`,
which does not reduce in the kernel, which would cost every `rfl`
cross-check.  `Epsilon0.lean` therefore has a hand-rolled triangular
pairing that is choice-free and kernel-computable, with `pr`/`pr1`/`pr2`
and the bijection lemmas.  **This file reuses that pairing**; it adds no
new coding primitive, only the list-of-children layer on top.

## The trees, and the coding

A hydra is a finite rooted tree: a node together with a finite, possibly
empty, list of child hydras.  Written as a mutual pair of inductives —
`Hydra` and `Forest` — rather than as `Hydra := List Hydra`, because
mutual structural recursion over the pair is what the encode/decode
proofs need, and nested inductives make those proofs fight the recursor.

Codes follow the standard list coding through the pairing:

    ⌜nil⌝            = 0
    ⌜cons h f⌝       = ⟪⌜h⌝, ⌜f⌝⟫ + 1
    ⌜node f⌝         = ⌜f⌝

A hydra's code *is* its forest's code, since a node carries no data
beyond its children.  Because `pr` is a bijection and the `+1` separates
the empty forest from the nonempty ones, the coding is a bijection
between `ℕ` and hydras — both round trips are proved below
(`decode_encode`, `encode_decode`), which is what makes "the fragment's
`∀x` ranges over exactly the hydras" true rather than approximate.

Decoding is fueled, like every other recursion in this development: the
components `pr1 n` and `pr2 n` are `≤ n` (`pr1_le`, `pr2_le`), so fuel
`= n` is adequate (`decodeF_eq_of_le`).
-/
import Realizability.Epsilon0

namespace Realizability

/-! ## The trees -/

mutual

/-- A hydra: a rooted node with a finite list of child hydras. -/
inductive Hydra : Type where
  | node : Forest → Hydra

/-- A finite list of hydras — the children of a node. -/
inductive Forest : Type where
  | nil : Forest
  | cons : Hydra → Forest → Forest

end

/-- The one-node hydra (a bare head). -/
def Hydra.leaf : Hydra := .node .nil

/-! ## Encoding -/

mutual

/-- The code of a hydra: the code of its children. -/
def encodeH : Hydra → ℕ
  | .node f => encodeF f

/-- The code of a forest: the standard list coding through the pairing. -/
def encodeF : Forest → ℕ
  | .nil => 0
  | .cons h f => pr (encodeH h) (encodeF f) + 1

end

@[simp] theorem encodeH_node (f : Forest) : encodeH (.node f) = encodeF f := rfl

@[simp] theorem encodeF_nil : encodeF .nil = 0 := rfl

@[simp] theorem encodeF_cons (h : Hydra) (f : Forest) :
    encodeF (.cons h f) = pr (encodeH h) (encodeF f) + 1 := rfl

/-! ## Decoding -/

/-- Decode a code into a forest (fueled; `pr1`/`pr2` strictly decrease the
code, so fuel `= n` is adequate). -/
def decodeF : ℕ → ℕ → Forest
  | 0, _ => .nil
  | _ + 1, 0 => .nil
  | fuel + 1, n + 1 =>
      .cons (.node (decodeF fuel (pr1 n))) (decodeF fuel (pr2 n))

/-- Decode a code into a hydra. -/
def decodeH (fuel n : ℕ) : Hydra := .node (decodeF fuel n)

theorem decodeF_succ_eq : ∀ (fuel n : ℕ), n ≤ fuel →
    decodeF (fuel + 1) n = decodeF fuel n
  | 0, n, h => by
    have hn : n = 0 := by omega
    subst hn
    rfl
  | fuel + 1, n, h => by
    cases n with
    | zero => rfl
    | succ m =>
      have h1 : pr1 m ≤ fuel := by
        have := pr1_le m
        omega
      have h2 : pr2 m ≤ fuel := by
        have := pr2_le m
        omega
      show Forest.cons (.node (decodeF (fuel + 1) (pr1 m)))
          (decodeF (fuel + 1) (pr2 m)) = _
      rw [decodeF_succ_eq fuel _ h1, decodeF_succ_eq fuel _ h2]
      rfl

theorem decodeF_eq_of_le : ∀ (fuel n : ℕ), n ≤ fuel →
    decodeF fuel n = decodeF n n
  | 0, n, h => by
    have hn : n = 0 := by omega
    subst hn
    rfl
  | fuel + 1, n, h => by
    rcases decEm (n = fuel + 1) with he | he
    · rw [he]
    · have hf : n ≤ fuel := by omega
      rw [decodeF_succ_eq fuel n hf, decodeF_eq_of_le fuel n hf]

/-- **The hydra with code `n`**, at the adequate fuel. -/
def hydraOf (n : ℕ) : Hydra := decodeH n n

/-- **The forest with code `n`**, at the adequate fuel. -/
def forestOf (n : ℕ) : Forest := decodeF n n

theorem forestOf_zero : forestOf 0 = .nil := rfl

/-- The decoding recursion, at the adequate fuel. -/
theorem forestOf_succ (n : ℕ) :
    forestOf (n + 1) = .cons (.node (forestOf (pr1 n))) (forestOf (pr2 n)) := by
  show decodeF (n + 1) (n + 1) = _
  show Forest.cons (.node (decodeF n (pr1 n))) (decodeF n (pr2 n)) = _
  rw [decodeF_eq_of_le n _ (pr1_le n), decodeF_eq_of_le n _ (pr2_le n)]
  rfl

/-! ## The coding is a bijection

Both round trips, as the brief requires: decoding a code and re-encoding
returns the code, and encoding a tree and decoding returns the tree. -/

/-- Round trip one: every natural number *is* a code. -/
theorem encodeF_decodeF : ∀ (fuel n : ℕ), n ≤ fuel →
    encodeF (decodeF fuel n) = n
  | 0, n, h => by
    have hn : n = 0 := by omega
    subst hn
    rfl
  | fuel + 1, n, h => by
    cases n with
    | zero => rfl
    | succ m =>
      have h1 : pr1 m ≤ fuel := by
        have := pr1_le m
        omega
      have h2 : pr2 m ≤ fuel := by
        have := pr2_le m
        omega
      show pr (encodeH (.node (decodeF fuel (pr1 m)))) (encodeF (decodeF fuel (pr2 m)))
        + 1 = m + 1
      rw [encodeH_node, encodeF_decodeF fuel _ h1, encodeF_decodeF fuel _ h2,
        pr_pr1_pr2]

/-- Round trip one, at the adequate fuel: `⌜forestOf n⌝ = n`. -/
theorem encodeF_forestOf (n : ℕ) : encodeF (forestOf n) = n :=
  encodeF_decodeF n n (Nat.le_refl n)

/-- Hence also for hydras. -/
theorem encodeH_hydraOf (n : ℕ) : encodeH (hydraOf n) = n :=
  encodeF_forestOf n

mutual

/-- Round trip two, hydras: decoding a tree's own code returns the tree. -/
theorem decodeH_encodeH : ∀ (h : Hydra) (fuel : ℕ), encodeH h ≤ fuel →
    decodeH fuel (encodeH h) = h
  | .node f, fuel, hf => by
    show Hydra.node (decodeF fuel (encodeF f)) = Hydra.node f
    rw [decodeF_encodeF f fuel hf]

/-- Round trip two, forests. -/
theorem decodeF_encodeF : ∀ (f : Forest) (fuel : ℕ), encodeF f ≤ fuel →
    decodeF fuel (encodeF f) = f
  | .nil, fuel, _ => by
    cases fuel with
    | zero => rfl
    | succ g => rfl
  | .cons h f, fuel, hf => by
    cases fuel with
    | zero =>
      exact absurd hf (by simp [encodeF])
    | succ g =>
      have hb : pr (encodeH h) (encodeF f) ≤ g := by
        simp only [encodeF] at hf
        omega
      have h1 : encodeH h ≤ g := by
        have := pr1_le (pr (encodeH h) (encodeF f))
        rw [pr1_pr] at this
        omega
      have h2 : encodeF f ≤ g := by
        have := pr2_le (pr (encodeH h) (encodeF f))
        rw [pr2_pr] at this
        omega
      show Forest.cons (.node (decodeF g (pr1 (pr (encodeH h) (encodeF f)))))
          (decodeF g (pr2 (pr (encodeH h) (encodeF f)))) = _
      rw [pr1_pr, pr2_pr, decodeF_encodeF f g h2]
      have hh : decodeH g (encodeH h) = h := decodeH_encodeH h g h1
      show Forest.cons (decodeH g (encodeH h)) f = _
      rw [hh]

end

/-- Round trip two, at the adequate fuel. -/
theorem hydraOf_encodeH (h : Hydra) : hydraOf (encodeH h) = h :=
  decodeH_encodeH h (encodeH h) (Nat.le_refl _)

theorem forestOf_encodeF (f : Forest) : forestOf (encodeF f) = f :=
  decodeF_encodeF f (encodeF f) (Nat.le_refl _)

/-! ## Small codes, kernel-checked

The coding is computable in the kernel (that is what the hand-rolled
pairing buys), so the smallest hydras can be read off by `rfl`. -/

/-- The empty forest — a bare root with no children — is code `0`. -/
theorem encodeH_leaf : encodeH Hydra.leaf = 0 := rfl

/-- A root with one leaf child is code `1`. -/
theorem encodeH_one : encodeH (.node (.cons Hydra.leaf .nil)) = 1 := rfl

/-- A root with one child which itself has one leaf child — a chain of
depth two — is code `2`. -/
theorem encodeH_two :
    encodeH (.node (.cons (.node (.cons Hydra.leaf .nil)) .nil)) = 2 := rfl

/-- A root with two leaf children is code `3`. -/
theorem encodeH_three :
    encodeH (.node (.cons Hydra.leaf (.cons Hydra.leaf .nil))) = 3 := rfl

/-- And the decoder inverts all of them, in the kernel. -/
theorem hydraOf_small :
    (hydraOf 0, hydraOf 1, hydraOf 2, hydraOf 3)
      = (Hydra.leaf,
         .node (.cons Hydra.leaf .nil),
         .node (.cons (.node (.cons Hydra.leaf .nil)) .nil),
         .node (.cons Hydra.leaf (.cons Hydra.leaf .nil))) := rfl

/-! ## Phase H2: the cutting-and-regrowth step

The rule implemented here (see STATUS.md for the citation and for the
variants that exist in the literature):

* a **head** is a leaf — a node with no children;
* Hercules chops one head off.  Let `p` be the head's parent;
* if `p` is the **root**, the head is simply removed and nothing grows;
* otherwise let `g` be `p`'s parent.  After the head is removed from `p`,
  the hydra grows `n` extra copies of the resulting subtree at `p`, all
  attached to `g`.  The modified `p` itself stays where it was.

Two parameters are left open and fixed by the caller, deliberately:
**which** head is chopped (here: the leftmost, per H4's canonical-strategy
decision) and **how many** copies grow (`n`, so the theorems quantify over
it and cover both the "n at stage n" and the adversarial readings).

`cutH` returns the new subtree together with a flag saying "the head I
chopped was a *direct child* of me", which is exactly the information the
caller needs to decide whether it is the grandparent and must therefore
grow the copies.  At the root the flag is discarded — which is precisely
the "parent is the root, nothing grows" clause. -/

/-- Concatenation of forests. -/
def Forest.append : Forest → Forest → Forest
  | .nil, g => g
  | .cons h f, g => .cons h (Forest.append f g)

/-- `n` copies of a hydra, as a forest. -/
def Forest.replicate : ℕ → Hydra → Forest
  | 0, _ => .nil
  | n + 1, h => .cons h (Forest.replicate n h)

/-- Is this hydra a bare head (a node with no children)? -/
def Hydra.isLeaf : Hydra → Bool
  | .node .nil => true
  | .node (.cons _ _) => false

/-- **One Hydra move**: chop the leftmost head, growing `n` copies at the
grandparent.  The `Bool` reports whether the chopped head was a direct
child of this node, i.e. whether *this node's parent* is the grandparent
that must grow the copies. -/
def cutH (n : ℕ) : Hydra → Hydra × Bool
  | .node .nil => (.node .nil, false)
  | .node (.cons (.node .nil) rest) => (.node rest, true)
  | .node (.cons (.node (.cons c₀ cs)) rest) =>
      let child : Hydra := .node (.cons c₀ cs)
      let r := cutH n child
      if r.2 then
        -- the head was a child of `child`, so this node is the grandparent
        (.node (.cons r.1 (Forest.append (Forest.replicate n r.1) rest)), false)
      else
        (.node (.cons r.1 rest), false)

/-- The move, forgetting the flag: at the root there is no grandparent, so
a head chopped from the root simply disappears. -/
def hydraStep (n : ℕ) (h : Hydra) : Hydra := (cutH n h).1

/-- The move on **codes** — the value-level function the fragment's symbol
will evaluate by.  Decoding and re-encoding are both kernel-computable, so
this computes. -/
def hydraStepN (n code : ℕ) : ℕ := encodeH (hydraStep n (hydraOf code))

/-- The battle: `hydraSeq n s` is the state after `s` moves from the hydra
coded `n`, with the number of copies at step `s` taken to be `s + 1`. -/
def hydraSeqN (start : ℕ) : ℕ → ℕ
  | 0 => start
  | s + 1 => hydraStepN (s + 1) (hydraSeqN start s)

/-! ### Small battles, kernel-checked

Codes from the table above: `0` is a bare head, `1` a root with one head,
`2` the two-deep chain, `3` a root with two heads. -/

/-- A root with two heads loses them one at a time and nothing grows —
both heads hang off the root, so the regrowth clause never fires. -/
theorem hydraSeq_two_heads :
    (hydraSeqN 3 0, hydraSeqN 3 1, hydraSeqN 3 2) = (3, 1, 0) := rfl

/-- The two-deep chain, where regrowth actually fires. -/
theorem hydraSeq_chain :
    (hydraSeqN 2 0, hydraSeqN 2 1, hydraSeqN 2 2, hydraSeqN 2 3) = (2, 3, 1, 0) := rfl

/-- Worth reading off: the middle step **grew** the hydra.  Code `2` is a
root with one child carrying one head; chopping that head empties the
child, and the root — the grandparent — grows a copy of it, leaving code
`3`, a root with *two* heads.  The tree got wider before it died.  This is
the phenomenon in miniature, and the reason the assigned ordinal, not the
node count, is what decreases (Phase H3). -/
theorem hydraSeq_one : (hydraSeqN 1 0, hydraSeqN 1 1) = (1, 0) := rfl

#print axioms encodeF_decodeF
#print axioms decodeF_encodeF
#print axioms hydraOf_encodeH
#print axioms encodeF_forestOf

end Realizability
