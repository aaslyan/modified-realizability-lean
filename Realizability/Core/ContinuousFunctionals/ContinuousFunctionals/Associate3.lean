/-
# Associates at pure type 3

`IsAssociate3 b Φ`: the type-1 function `b` is an associate of the type-3
functional `Φ` — along the prefix chain of *any associate `a` of any
continuous type-2 functional `F`*, `b` runs silently and then fires with
value `Φ F + 1`.

Correspondence with the literature: this is the clause `n = 2` of Kleene's
inductive definition (Longley, *Notions of computability at higher types
I*, §3.3.1, Definition 3.13): "`f ∈ C1` is an associate for
`F : Cₙ → ℕ` iff whenever `g` is an associate for `G ∈ Cₙ` we have
`f | g = F(G)`", with `C2` = the type-2 functionals having associates —
by `continuous_iff_hasAssociate` (and `continuous2_iff_continuous`)
exactly the continuous ones.  The type-3 functionals of the countable
hierarchy, `Ct(3)`, are those `Φ` with an associate.  `Hierarchy.lean`
states the definition uniformly at every pure type and proves this file's
definition is its level-3 instance.

Two modeling notes, both consequences of staying with total Lean
functions:

* `Φ` is total on all of `((ℕ → ℕ) → ℕ) → ℕ`, but `IsAssociate3`
  constrains it only on the continuous fragment — its values on
  discontinuous functionals are irrelevant, mirroring how `Ct(3)` is
  properly a set of functions *on* `Ct(2)` (the extensional-collapse view;
  Longley §3.3.1).
* The quantifier over *all* associates `a` of the same `F` is the genuine
  content at this level: `b` may only use information about `F`, not about
  the particular way an associate presents `F`.  `SanityChecks3.lean`
  exhibits a `b` that fails exactly this requirement.
-/
import ContinuousFunctionals.Application

namespace ContinuousFunctionals

/-- **Kleene's associates at pure type 3.**  `b` is an associate of `Φ`
iff for every continuous type-2 functional — presented as `F` with an
associate `a`, by the main theorem — `b` fires along the prefix chain of
`a` with value `Φ F + 1`, having read `0` on all shorter prefixes.
Equivalently (`isAssociate3_iff_kleeneApply`) `b | a = Φ F` for every
associate `a` of every continuous `F` (Longley §3.3.1, Definition 3.13,
clause `n = 2`). -/
def IsAssociate3 (b : ℕ → ℕ) (Φ : ((ℕ → ℕ) → ℕ) → ℕ) : Prop :=
  ∀ (F : (ℕ → ℕ) → ℕ) (a : ℕ → ℕ), IsAssociate a F →
    ∃ n : ℕ, b (code (initSeg a n)) = Φ F + 1 ∧
      ∀ m < n, b (code (initSeg a m)) = 0

/-- `IsAssociate3` unfolded through Kleene application: `b | a` is defined
and equals `Φ F` whenever `a` is an associate of `F`.  The textbook form
of the definition. -/
theorem isAssociate3_iff_kleeneApply {b : ℕ → ℕ}
    {Φ : ((ℕ → ℕ) → ℕ) → ℕ} :
    IsAssociate3 b Φ ↔
      ∀ (F : (ℕ → ℕ) → ℕ) (a : ℕ → ℕ), IsAssociate a F →
        ApplyDefined b a ∧ kleeneApply b a = Φ F := by
  constructor
  · intro hb F a ha
    obtain ⟨n, hv, hz⟩ := hb F a ha
    refine ⟨⟨n, by rw [hv]; exact Nat.succ_ne_zero _⟩, ?_⟩
    exact kleeneApply_eq_of_fire hv hz
  · intro h F a ha
    obtain ⟨hd, hval⟩ := h F a ha
    obtain ⟨n, v, hv, hz⟩ := hd.exists_fire
    have hveq : v = Φ F := by
      rw [← hval]
      exact (kleeneApply_eq_of_fire hv hz).symm
    exact ⟨n, by rw [hv, hveq], hz⟩

/-- The constant type-3 functional has the constant associate, firing on
the empty prefix of any argument associate: `IsAssociate3` is not vacuous. -/
theorem isAssociate3_const (c : ℕ) :
    IsAssociate3 (fun _ => c + 1) (fun _ => c) :=
  fun _ _ _ => ⟨0, rfl, fun m hm => absurd hm (Nat.not_lt_zero m)⟩

end ContinuousFunctionals
