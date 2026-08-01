/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import Realizability.Signature.Hanoi

/-!
# Sperner (1D) value layer: colorings as cons-list codes

The 1-dimensional Sperner / discrete-IVT theorem quantifies over an
*arbitrary* coloring `c : {0,…,n} → ℕ`.  The fragment has no function
variables (the same wall as the Hydra battle), so a coloring is carried
as a single `ℕ` **code**, and reading `c k` is a new symbol `look`,
evaluated by `lookN` here.

`lookN w k` is the `k`-th element of the coloring coded by `w`, using the
**same cons-list encoding as `Hanoi.lean`** (`hconsN`/`hhead`/`htail` over
Phase C's hand-rolled, `Classical`-free pairing `pr`).  It is structural
in the index, hence kernel-computable and choice-free — it feeds
`Term.eval`, so it must be, exactly like `hydraStepN`/`goodN`.

No new *object* is constructed (colorings reuse the existing sequence
coding); the only genuinely new thing is the `look` accessor symbol —
statability-forced, since `c k` for a bound `k` cannot be written as a
term over the existing signature.
-/

namespace Realizability

/-- The color at index `k` of the coloring coded by `w`.  Structural in the
index; out of the encoded range it reads `hhead hnil`. -/
def lookN : ℕ → ℕ → ℕ
  | w, 0 => hhead w
  | w, i + 1 => lookN (htail w) i

@[simp] theorem lookN_zero (w : ℕ) : lookN w 0 = hhead w := rfl

@[simp] theorem lookN_succ (w i : ℕ) : lookN w (i + 1) = lookN (htail w) i := rfl

/-- Encode an explicit coloring (a list of colors, index `0` first) as a
cons-list code — the inverse of `lookN` on the encoded range. -/
def colorCode : List ℕ → ℕ
  | [] => hnil
  | c :: cs => hconsN c (colorCode cs)

/-- `lookN` reads back exactly what `colorCode` stored, within range. -/
theorem lookN_colorCode :
    ∀ (cs : List ℕ) (k : ℕ) (h : k < cs.length), lookN (colorCode cs) k = cs.get ⟨k, h⟩
  | c :: cs, 0, _ => by
      simp [lookN, colorCode, hhead_hcons]
  | c :: cs, k + 1, h => by
      have h' : k < cs.length := Nat.lt_of_succ_lt_succ h
      simp only [lookN, colorCode, htail_hcons, List.get]
      exact lookN_colorCode cs k h'

end Realizability
