/-
# Type-3 sanity checks: associate-independence is a real constraint

The distinctive requirement of `IsAssociate3` is the quantifier over *all*
associates of the argument functional: a type-3 associate may use only
information about the functional, never about the particular associate
presenting it.  This file shows the requirement bites:

* `projAssociateAt v` — a family of associates of the projection
  `F α = α 0`, all agreeing on the segments the first-fire discipline ever
  consults, but differing (value `v`) at a position that is only read
  *after* the fire;
* `peekAssociate` — a type-1 function that reads its argument sequence at
  exactly such a position; it is a perfectly good neighborhood function,
  but `no_isAssociate3_peekAssociate` shows it is an associate of *no*
  type-3 functional: fed two associates of the same `F`, it fires with two
  different values.

Together with `isAssociate3_const` and `isAssociate3_evalAssociate` this
confirms `IsAssociate3` is neither vacuous nor universally true.
`Hierarchy.lean` proves the corresponding non-example at every pure type
above 3.
-/
import ContinuousFunctionals.Evaluation

namespace ContinuousFunctionals

/-- A family of associates of the projection `F α = α 0`, indexed by the
value `v` they carry at every position coding a sequence of length ≥ 2 —
positions the first-fire discipline never consults, since the fire happens
at length 1. -/
def projAssociateAt (v : ℕ) : ℕ → ℕ := fun k =>
  match decodeList k with
  | [] => 0
  | [x] => x + 1
  | _ :: _ :: _ => v

/-- Every member of the family is an associate of the projection: silent
on the empty segment, firing with `α 0 + 1` at length 1 — the tail value
`v` is invisible to the associate condition. -/
theorem isAssociate_projAssociateAt (v : ℕ) :
    IsAssociate (projAssociateAt v) (fun α => α 0) := by
  intro α
  refine ⟨1, ?_, ?_⟩
  · have h1 : initSeg α 1 = [α 0] := by
      simp [initSeg, List.range_succ]
    rw [h1]
    simp [projAssociateAt]
  · intro m hm
    have hm0 : m = 0 := by omega
    rw [hm0]
    simp [projAssociateAt]

/-- The "peek" function: reads its argument sequence at the fixed position
`p` (plus one, in the neighborhood convention), as soon as the prefix is
long enough.  A legitimate type-1 function — but it reads the *associate*,
not the functional. -/
def peekAssociate (p : ℕ) : ℕ → ℕ := fun k =>
  if p < (decodeList k).length then (decodeList k).getD p 0 + 1 else 0

/-- Along a genuine prefix chain, `peekAssociate p` is silent until the
position `p` is visible and then fires with `a p + 1`. -/
theorem peekAssociate_code_initSeg (p : ℕ) (a : ℕ → ℕ) (n : ℕ) :
    peekAssociate p (code (initSeg a n)) = if p < n then a p + 1 else 0 := by
  unfold peekAssociate
  rw [decodeList_code]
  by_cases h : p < n
  · rw [if_pos (by simpa using h), if_pos h, initSeg_getD a h]
  · rw [if_neg (by simpa using h), if_neg h]

/-- **Associate-independence bites**: `peekAssociate (code [0, 0])` is an
associate of no type-3 functional.  Fed the associates
`projAssociateAt 0` and `projAssociateAt 1` of the *same* projection
functional, it fires with values `0 + 1` and `1 + 1` respectively, so no
single value `Φ (fun α => α 0)` can satisfy `IsAssociate3`.  (The position
`code [0, 0]` codes a length-2 sequence, exactly where the family
disagrees.) -/
theorem no_isAssociate3_peekAssociate :
    ¬ ∃ Φ : ((ℕ → ℕ) → ℕ) → ℕ,
      IsAssociate3 (peekAssociate (code [0, 0])) Φ := by
  rintro ⟨Φ, hΦ⟩
  have key : ∀ v : ℕ, Φ (fun α => α 0) = v := by
    intro v
    obtain ⟨n, hv, -⟩ :=
      hΦ (fun α => α 0) (projAssociateAt v) (isAssociate_projAssociateAt v)
    rw [peekAssociate_code_initSeg] at hv
    by_cases hn : code [0, 0] < n
    · rw [if_pos hn] at hv
      have ha : projAssociateAt v (code [0, 0]) = v := by
        simp [projAssociateAt]
      rw [ha] at hv
      omega
    · rw [if_neg hn] at hv
      omega
  have h0 := key 0
  have h1 := key 1
  omega

end ContinuousFunctionals
