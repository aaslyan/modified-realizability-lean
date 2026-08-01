/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import Realizability.Signature.Pascal

/-!
# Phase G1: Kummer/Lucas at `p = 2`

The stretch goal of the Pascal brief, and unlike Phase F's theorems this
one is *not* an internal consistency check of `pas`'s own definition: it
is the classical characterisation

    C(n,k) is odd  ⟺  the binary digits of k are a submask of those of n

(Kummer 1852 / Lucas 1878, at `p = 2`), and it is what makes the
Sierpiński picture inevitable rather than merely observed.

## The route

Everything goes through the **binary step identities**, proved from
Pascal's recursion alone by one simultaneous induction:

    pas(2n,   2k)   = pas(n,k)      pas(2n,   2k+1) = 0
    pas(2n+1, 2k)   = pas(n,k)      pas(2n+1, 2k+1) = pas(n,k)

Their proof is the interesting part.  The two `2n+1` clauses follow from
the two `2n` clauses *at the same `n`*, and the two `2n` clauses at `n+1`
follow from the `2n+1` clauses at `n` — so the induction alternates
between the even and odd rows, which is exactly the alternation the
Sierpiński gasket's self-similarity expresses.

Read together they say: `pas(n,k) = pas(n/2, k/2)` when `k`'s low bit is
below `n`'s, and `0` otherwise (`pasN_lucas_step`).  Iterating that down
the bits is the theorem.

## Digits, without a new mechanism

The brief asked that digit extraction reuse existing machinery rather
than introduce a second scheme.  It needs none at all: the `i`-th binary
digit of `m` is `(m / 2^i) % 2`, which is arithmetic already present, and
the submask condition is `∀ i, digit k i ≤ digit n i`.  No hereditary
representation is required, because unlike Phase B's `bump` this
recursion never has to look at a digit's *own* structure — only at its
value, which is `0` or `1`.

The `&&&` form is proved too (`pasN_eq_one_iff_land`), since that is how
the theorem is usually quoted.
-/

namespace Realizability

/-! ## Small facts the induction leans on -/

/-- The left column is all ones. -/
theorem pasN_col_zero : ∀ n : ℕ, pasN n 0 = 1
  | 0 => rfl
  | _ + 1 => rfl

theorem xorN_zero_left {a : ℕ} (h : a = 1 ∨ a = 0) : xorN 0 a = a := by
  rcases h with h | h <;> rw [h] <;> rfl

theorem xorN_zero_right {a : ℕ} (h : a = 1 ∨ a = 0) : xorN a 0 = a := by
  rcases h with h | h <;> rw [h] <;> rfl

theorem xorN_self {a : ℕ} (h : a = 1 ∨ a = 0) : xorN a a = 0 := by
  rcases h with h | h <;> rw [h] <;> rfl

/-! ## The binary step identities -/

/-- The two even-row identities, and — since the odd rows are derived
from the even ones at the same `n` — all four, by one induction on `n`.

`pasEven n` is the statement at row `2n`; the odd row `2n+1` is
`pasOdd`, immediately below. -/
theorem pasN_even : ∀ (n k : ℕ),
    pasN (2 * n) (2 * k) = pasN n k ∧ pasN (2 * n) (2 * k + 1) = 0 := by
  intro n
  induction n with
  | zero =>
    intro k
    constructor
    · cases k with
      | zero => rfl
      | succ j =>
        have h : 2 * (j + 1) = (2 * j + 1) + 1 := by omega
        rw [h]
        rfl
    · show pasN 0 (2 * k + 1) = 0
      rfl
  | succ n ih =>
    -- first the odd row `2n+1`, from the even row `2n`
    have hodd : ∀ k : ℕ, pasN (2 * n + 1) (2 * k) = pasN n k
        ∧ pasN (2 * n + 1) (2 * k + 1) = pasN n k := by
      intro k
      constructor
      · cases k with
        | zero => exact (pasN_col_zero n).symm
        | succ j =>
          have h : 2 * (j + 1) = (2 * j + 1) + 1 := by omega
          rw [h]
          show xorN (pasN (2 * n) (2 * j + 1)) (pasN (2 * n) (2 * j + 1 + 1)) = _
          have h₁ := (ih j).2
          have h₂ : pasN (2 * n) (2 * j + 1 + 1) = pasN n (j + 1) := by
            have he : 2 * j + 1 + 1 = 2 * (j + 1) := by omega
            rw [he]
            exact (ih (j + 1)).1
          rw [h₁, h₂]
          exact xorN_zero_left (pasN_total n (j + 1))
      · show xorN (pasN (2 * n) (2 * k)) (pasN (2 * n) (2 * k + 1)) = pasN n k
        rw [(ih k).1, (ih k).2]
        exact xorN_zero_right (pasN_total n k)
    intro k
    constructor
    · -- `pas(2(n+1), 2k) = pas(n+1, k)`
      cases k with
      | zero =>
        show pasN (2 * (n + 1)) 0 = pasN (n + 1) 0
        rw [pasN_col_zero, pasN_col_zero]
      | succ j =>
        have hn : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
        have hk : 2 * (j + 1) = (2 * j + 1) + 1 := by omega
        rw [hn, hk]
        show xorN (pasN (2 * n + 1) (2 * j + 1))
          (pasN (2 * n + 1) (2 * j + 1 + 1)) = _
        have h₁ := (hodd j).2
        have h₂ : pasN (2 * n + 1) (2 * j + 1 + 1) = pasN n (j + 1) := by
          have he : 2 * j + 1 + 1 = 2 * (j + 1) := by omega
          rw [he]
          exact (hodd (j + 1)).1
        rw [h₁, h₂]
        rfl
    · -- `pas(2(n+1), 2k+1) = 0`
      have hn : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
      rw [hn]
      show xorN (pasN (2 * n + 1) (2 * k)) (pasN (2 * n + 1) (2 * k + 1)) = 0
      rw [(hodd k).1, (hodd k).2]
      exact xorN_self (pasN_total n k)

/-- The two odd-row identities. -/
theorem pasN_odd (n k : ℕ) :
    pasN (2 * n + 1) (2 * k) = pasN n k
    ∧ pasN (2 * n + 1) (2 * k + 1) = pasN n k := by
  constructor
  · cases k with
    | zero => exact (pasN_col_zero n).symm
    | succ j =>
      have h : 2 * (j + 1) = (2 * j + 1) + 1 := by omega
      rw [h]
      show xorN (pasN (2 * n) (2 * j + 1)) (pasN (2 * n) (2 * j + 1 + 1)) = _
      have h₁ := (pasN_even n j).2
      have h₂ : pasN (2 * n) (2 * j + 1 + 1) = pasN n (j + 1) := by
        have he : 2 * j + 1 + 1 = 2 * (j + 1) := by omega
        rw [he]
        exact (pasN_even n (j + 1)).1
      rw [h₁, h₂]
      exact xorN_zero_left (pasN_total n (j + 1))
  · show xorN (pasN (2 * n) (2 * k)) (pasN (2 * n) (2 * k + 1)) = pasN n k
    rw [(pasN_even n k).1, (pasN_even n k).2]
    exact xorN_zero_right (pasN_total n k)

/-- **The Lucas step**: one binary digit at a time.  `pas(n,k)` is
`pas(n/2, k/2)` when `k`'s low bit is at most `n`'s, and `0` otherwise. -/
theorem pasN_lucas_step (n k : ℕ) :
    pasN n k = if k % 2 ≤ n % 2 then pasN (n / 2) (k / 2) else 0 := by
  obtain ⟨m, hm⟩ : ∃ m, n / 2 = m := ⟨_, rfl⟩
  obtain ⟨j, hj⟩ : ∃ j, k / 2 = j := ⟨_, rfl⟩
  have hb : n % 2 = 0 ∨ n % 2 = 1 := by omega
  have hc : k % 2 = 0 ∨ k % 2 = 1 := by omega
  rw [hm, hj]
  rcases hb with hb | hb <;> rcases hc with hc | hc
  · have hn2 : n = 2 * m := by omega
    have hk2 : k = 2 * j := by omega
    rw [if_pos (by omega), hn2, hk2]
    exact (pasN_even m j).1
  · have hn2 : n = 2 * m := by omega
    have hk2 : k = 2 * j + 1 := by omega
    rw [if_neg (by omega), hn2, hk2]
    exact (pasN_even m j).2
  · have hn2 : n = 2 * m + 1 := by omega
    have hk2 : k = 2 * j := by omega
    rw [if_pos (by omega), hn2, hk2]
    exact (pasN_odd m j).1
  · have hn2 : n = 2 * m + 1 := by omega
    have hk2 : k = 2 * j + 1 := by omega
    rw [if_pos (by omega), hn2, hk2]
    exact (pasN_odd m j).2

/-! ## Binary digits

The `i`-th binary digit of `m` is `(m / 2^i) % 2` — no new mechanism, and
in particular no hereditary representation: unlike Phase B's `bump`, this
recursion never inspects a digit's own structure, only its value. -/

/-- The `i`-th binary digit. -/
def digit (m i : ℕ) : ℕ := (m / 2 ^ i) % 2

theorem digit_zero (m : ℕ) : digit m 0 = m % 2 := by
  show (m / 2 ^ 0) % 2 = m % 2
  simp

theorem digit_succ (m i : ℕ) : digit m (i + 1) = digit (m / 2) i := by
  show (m / 2 ^ (i + 1)) % 2 = ((m / 2) / 2 ^ i) % 2
  rw [Nat.div_div_eq_div_mul]
  have h : 2 ^ (i + 1) = 2 * 2 ^ i := by
    rw [Nat.pow_succ]
    omega
  rw [h]

theorem digit_of_zero (i : ℕ) : digit 0 i = 0 := by
  show (0 / 2 ^ i) % 2 = 0
  simp

/-- A number all of whose binary digits vanish is `0`. -/
theorem eq_zero_of_digits : ∀ k : ℕ, (∀ i, digit k i = 0) → k = 0 := by
  refine nat_strong_ind (fun k ih ↦ ?_)
  intro h
  rcases Nat.eq_zero_or_pos k with h0 | h0
  · exact h0
  · have hk2 : k % 2 = 0 := by
      have := h 0
      rwa [digit_zero] at this
    have hd : ∀ i, digit (k / 2) i = 0 := by
      intro i
      have := h (i + 1)
      rwa [digit_succ] at this
    have hlt : k / 2 < k := by omega
    have := ih (k / 2) hlt hd
    omega

/-! ## The theorem -/

/-- **Kummer/Lucas at `p = 2`.**  `C(n,k)` is odd exactly when every
binary digit of `k` is at most the corresponding digit of `n` — that is,
when `k`'s bits are a submask of `n`'s.

Strong induction on `n`, one binary digit per step: `pasN_lucas_step`
peels the low bit off both arguments, and `digit_succ` shifts the digit
condition to match. -/
theorem pasN_eq_one_iff :
    ∀ (n k : ℕ), pasN n k = 1 ↔ ∀ i, digit k i ≤ digit n i := by
  refine nat_strong_ind (fun n ih ↦ ?_)
  intro k
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0
    constructor
    · intro h1 i
      have hk : k = 0 := by
        cases k with
        | zero => rfl
        | succ j => exact absurd h1 (by rw [pasN_zero_succ]; simp)
      subst hk
      exact Nat.le_refl _
    · intro h
      have hd : ∀ i, digit k i = 0 := by
        intro i
        have h₁ := h i
        have h₂ := digit_of_zero i
        omega
      rw [eq_zero_of_digits k hd]
      rfl
  · have hlt : n / 2 < n := by omega
    rw [pasN_lucas_step]
    constructor
    · intro h1
      by_cases hcond : k % 2 ≤ n % 2
      · rw [if_pos hcond] at h1
        have hrec := (ih (n / 2) hlt (k / 2)).mp h1
        intro i
        cases i with
        | zero => rw [digit_zero, digit_zero]; exact hcond
        | succ i => rw [digit_succ, digit_succ]; exact hrec i
      · rw [if_neg hcond] at h1
        exact absurd h1 (by simp)
    · intro h
      have h₀ := h 0
      rw [digit_zero, digit_zero] at h₀
      rw [if_pos h₀]
      refine (ih (n / 2) hlt (k / 2)).mpr ?_
      intro i
      have := h (i + 1)
      rwa [digit_succ, digit_succ] at this

/-- The same, as the parity statement it decides: the entry is `0`
exactly when some digit of `k` exceeds the corresponding digit of `n`. -/
theorem pasN_eq_zero_iff (n k : ℕ) :
    pasN n k = 0 ↔ ¬ (∀ i, digit k i ≤ digit n i) := by
  rcases pasN_total n k with h | h
  · rw [h]
    simp only [Nat.one_ne_zero, false_iff, not_not]
    exact (pasN_eq_one_iff n k).mp h
  · rw [h]
    simp only [true_iff]
    intro hall
    have := (pasN_eq_one_iff n k).mpr hall
    omega

/-! ## The bitwise form

`k AND n = k` — how the theorem is usually quoted.  Digits and `testBit`
are the same thing, so this is a repackaging of `pasN_eq_one_iff`, not a
second proof. -/

theorem testBit_eq_digit (m : ℕ) : ∀ i, m.testBit i = decide (digit m i = 1)
  | 0 => by rw [Nat.testBit_zero, digit_zero]
  | i + 1 => by
    rw [Nat.testBit_succ, testBit_eq_digit (m / 2) i, digit_succ]

theorem digit_le_one (m i : ℕ) : digit m i = 0 ∨ digit m i = 1 := by
  show (m / 2 ^ i) % 2 = 0 ∨ (m / 2 ^ i) % 2 = 1
  omega

theorem land_eq_self_iff (n k : ℕ) :
    k &&& n = k ↔ ∀ i, digit k i ≤ digit n i := by
  have hbit : ∀ m i, (m.testBit i = true) ↔ digit m i = 1 := by
    intro m i
    rw [testBit_eq_digit]
    simp
  constructor
  · intro h i
    have ht : (k.testBit i && n.testBit i) = k.testBit i := by
      rw [← Nat.testBit_and, h]
    rcases digit_le_one k i with hk2 | hk2
    · omega
    · have hkt : k.testBit i = true := (hbit k i).mpr hk2
      rw [hkt, Bool.true_and] at ht
      have hn := (hbit n i).mp ht
      omega
  · intro h
    refine Nat.eq_of_testBit_eq fun i ↦ ?_
    rw [Nat.testBit_and]
    cases hkt : k.testBit i with
    | false => simp
    | true =>
      have hk1 : digit k i = 1 := (hbit k i).mp hkt
      have hi := h i
      rcases digit_le_one n i with hn0 | hn1
      · omega
      · rw [(hbit n i).mpr hn1]
        simp

/-- **Kummer/Lucas at `p = 2`, in its usual form**:

    C(n,k) is odd  ⟺  k AND n = k. -/
theorem pasN_eq_one_iff_land (n k : ℕ) : pasN n k = 1 ↔ k &&& n = k :=
  (pasN_eq_one_iff n k).trans (land_eq_self_iff n k).symm

/-! ## Cross-checks

The theorem is proved, so this checks that the *statement* is the famous
one, over as much of the triangle as `pasN` can be run: it is the
unmemoised Pascal recursion, so a cell in row `n` costs about `C(n,k)`
calls, and 16 rows is what fits comfortably in a build.  The digit form
needs no separate check — it *is* `pasN_eq_one_iff`. -/

#guard (List.range 17).all fun n ↦
  (List.range (n + 1)).all fun k ↦ (pasN n k == 1) == (k &&& n == k)

/-! Two named instances: row 8 is `1 0 0 0 0 0 0 0 1` because the only
submasks of `1000₂` are `0` and itself; row 7 is all ones because
`111₂` contains every mask below it. -/

#guard (List.range 9).map (pasN 8) == [1, 0, 0, 0, 0, 0, 0, 0, 1]
#guard (List.range 8).map (pasN 7) == [1, 1, 1, 1, 1, 1, 1, 1]

#print axioms pasN_even
#print axioms pasN_lucas_step
#print axioms pasN_eq_one_iff
#print axioms pasN_eq_one_iff_land

end Realizability
