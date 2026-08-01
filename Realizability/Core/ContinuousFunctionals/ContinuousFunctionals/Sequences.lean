/-
# Finite sequences, codes, and initial segments

The finite pieces of information about a point `α : ℕ → ℕ` of Baire space
are its finite initial segments `[α 0, …, α (n-1)] : List ℕ`.  An associate
(`ContinuousFunctionals.IsAssociate`) consumes such segments through a fixed
numerical coding.  This file provides:

* `initSeg α n` — the initial segment of length `n` (the standard notation
  `ᾱ(n)` of the literature), and its basic calculus: `initSeg_eq_iff` is the
  bridge between "agreement below `n`" and equality of segments, and
  `initSeg_take` says the prefixes of a segment are the shorter segments;
* `code` / `decodeList` — a fixed bijective coding of `List ℕ` by `ℕ`,
  borrowed from Mathlib's `Denumerable (List ℕ)` instance;
* `extendZero σ` — the canonical infinite extension of a finite sequence,
  used to pick a definite point of Baire space inside each basic open set.

Everything here is elementary bookkeeping; the mathematical content of the
project starts in `Associate.lean` and `Continuity.lean`.
-/
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Pairing
import Mathlib.Logic.Equiv.List

namespace ContinuousFunctionals

/-- `initSeg α n` is the initial segment `[α 0, α 1, …, α (n - 1)]` of the
sequence `α : ℕ → ℕ`: the finite piece of information about `α` visible at
stage `n`.  This is the Lean rendering of the sequence-number notation
`ᾱ(n)` used throughout the literature on the countable functionals
(Kleene 1959; Longley–Normann 2015, Ch. 8). -/
def initSeg (α : ℕ → ℕ) (n : ℕ) : List ℕ :=
  (List.range n).map α

@[simp] theorem initSeg_zero (α : ℕ → ℕ) : initSeg α 0 = [] := rfl

@[simp] theorem initSeg_length (α : ℕ → ℕ) (n : ℕ) :
    (initSeg α n).length = n := by
  simp [initSeg]

/-- Passing from stage `n` to stage `n + 1` appends the single value `α n`. -/
theorem initSeg_succ (α : ℕ → ℕ) (n : ℕ) :
    initSeg α (n + 1) = initSeg α n ++ [α n] := by
  simp [initSeg, List.range_succ]

/-- Two sequences have the same initial segment of length `n` iff they agree
at every index below `n`.  This is the bridge between the "modulus of
continuity" view (`Continuous2`) and the "neighborhood" view
(`IsAssociate`) of finite information. -/
theorem initSeg_eq_iff {α β : ℕ → ℕ} {n : ℕ} :
    initSeg α n = initSeg β n ↔ ∀ i < n, α i = β i := by
  simp [initSeg]

/-- Truncating an initial segment yields the shorter initial segment: the
prefixes of `initSeg α n` are exactly the `initSeg α m` for `m ≤ n`. -/
theorem initSeg_take (α : ℕ → ℕ) {m n : ℕ} (h : m ≤ n) :
    (initSeg α n).take m = initSeg α m := by
  simp [initSeg, ← List.map_take, List.take_range, Nat.min_eq_left h]

/-- The fixed numerical code of a finite sequence, via Mathlib's
`Denumerable (List ℕ)` instance.  Associates consume codes rather than raw
lists so that an associate is literally a function `ℕ → ℕ`, i.e. itself a
type-1 object — the point of Kleene's construction (Longley–Normann 2015,
Ch. 8: type-1 objects encode type-2 objects). -/
def code (σ : List ℕ) : ℕ :=
  Encodable.encode σ

/-- Decoding of finite sequences, inverse to `code`. -/
def decodeList (k : ℕ) : List ℕ :=
  Denumerable.ofNat (List ℕ) k

@[simp] theorem decodeList_code (σ : List ℕ) : decodeList (code σ) = σ :=
  Denumerable.ofNat_encode σ

theorem code_injective : Function.Injective code := by
  intro σ τ h
  have h' := congrArg decodeList h
  simpa using h'

/-- Reading an entry of an initial segment below its length recovers the
sequence: `initSeg` is a faithful record of the first `n` values. -/
theorem initSeg_getD (α : ℕ → ℕ) {i n : ℕ} (h : i < n) :
    (initSeg α n).getD i 0 = α i := by
  have hlen : i < (initSeg α n).length := by simpa using h
  rw [List.getD_eq_getElem _ _ hlen]
  simp [initSeg]

/-- `extendZero σ` extends the finite sequence `σ` to a point of Baire space
by padding with `0`.  It is the canonical point inside the basic open set of
all sequences beginning with `σ`. -/
def extendZero (σ : List ℕ) : ℕ → ℕ :=
  fun i => σ.getD i 0

@[simp] theorem initSeg_extendZero (σ : List ℕ) :
    initSeg (extendZero σ) σ.length = σ := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp [initSeg, extendZero, h₂]

/-- The coding is honest about size: the code of a finite sequence bounds
its length.  (Each `cons` step passes through `Nat.pair`, which dominates
its second argument.)  This is what lets a search over stages `r` with
"position `code (initSeg γ r)` visible in a prefix of length `n`" be
implicitly bounded by `n`. -/
theorem length_le_code (σ : List ℕ) : σ.length ≤ code σ := by
  induction σ with
  | nil => exact Nat.zero_le _
  | cons a l ih =>
    have h1 : code l + 1 ≤ code (a :: l) := by
      unfold code
      rw [Encodable.encode_list_cons]
      exact Nat.succ_le_succ (Nat.right_le_pair _ _)
    simp only [List.length_cons]
    omega

/-- Interleaving two sequences into one point of Baire space through the
pairing bijection: the standard type-changing device by which a pair of
type-1 objects is a single type-1 object. -/
def pairSeq (b g : ℕ → ℕ) : ℕ → ℕ := fun i => Nat.pair (b i) (g i)

/-- First components of a finite sequence of coded pairs. -/
def fstList (ρ : List ℕ) : List ℕ := ρ.map fun z => z.unpair.1

/-- Second components of a finite sequence of coded pairs. -/
def sndList (ρ : List ℕ) : List ℕ := ρ.map fun z => z.unpair.2

@[simp] theorem fstList_length (ρ : List ℕ) : (fstList ρ).length = ρ.length := by
  simp [fstList]

@[simp] theorem sndList_length (ρ : List ℕ) : (sndList ρ).length = ρ.length := by
  simp [sndList]

/-- A prefix of an interleaved pair determines the prefix of the first
component. -/
theorem fstList_initSeg_pairSeq (b g : ℕ → ℕ) (n : ℕ) :
    fstList (initSeg (pairSeq b g) n) = initSeg b n := by
  unfold fstList initSeg pairSeq
  rw [List.map_map]
  apply List.map_congr_left
  intro i _
  simp [Nat.unpair_pair]

/-- A prefix of an interleaved pair determines the prefix of the second
component. -/
theorem sndList_initSeg_pairSeq (b g : ℕ → ℕ) (n : ℕ) :
    sndList (initSeg (pairSeq b g) n) = initSeg g n := by
  unfold sndList initSeg pairSeq
  rw [List.map_map]
  apply List.map_congr_left
  intro i _
  simp [Nat.unpair_pair]

end ContinuousFunctionals
