/-
# The main theorem: continuity ↔ having an associate

Both directions of the required deliverable:

* `hasAssociate_of_continuous` — every continuous functional has an
  associate.  The associate is built *uniformly* as `canonicalAssociate F`:
  on (the code of) a finite sequence `σ` it classically asks whether `σ`
  already determines the value of `F` on the whole basic open set of
  sequences extending `σ`, and if so answers that value (plus one).
  Continuity guarantees that along the prefix chain of any `α` this
  condition is eventually reached, and the first-fire discipline of
  `IsAssociate` is then verified at the *least* such stage.
* `continuous_of_hasAssociate` — every associate genuinely defines a
  continuous functional: the firing stage at `α` is a modulus of
  continuity at `α`.

Packaged together as `continuous_iff_hasAssociate`.  This equivalence is
the type-2 kernel of Kleene's construction of the countable functionals
(Kleene 1959; Longley, *Notions of computability at higher types I*,
§3.3.1; Longley–Normann 2015, Ch. 8).
-/
import ContinuousFunctionals.Associate
import ContinuousFunctionals.Continuity

namespace ContinuousFunctionals

/-- `Determines F σ`: the finite sequence `σ` already determines the value
of `F`, in the sense that every point of Baire space beginning with `σ` is
sent to the same value — namely the value at the canonical such point
`extendZero σ`.  These are exactly the "neighborhoods on which `F` is
constant"; the canonical associate answers on precisely these. -/
def Determines (F : (ℕ → ℕ) → ℕ) (σ : List ℕ) : Prop :=
  ∀ β : ℕ → ℕ, initSeg β σ.length = σ → F β = F (extendZero σ)

/-- **The canonical associate** of a functional `F`.  On the code of a
finite sequence `σ` it answers `F (extendZero σ) + 1` if `σ` determines the
value of `F` (`Determines F σ`), and `0` ("not enough information yet")
otherwise.  The definition is classical — no decision procedure for
`Determines` is claimed — which is all the notion of associate requires.

This is verbatim the function `f_F` with which Longley (*Notions of
computability at higher types I*, §3.3.1, displayed before Definition 3.13)
introduces Kleene's associates: `f_F ⟨n₀,…,n_{r−1}⟩ = m + 1` if `F g = m`
for all `g` extending the sequence, and `0` if no such `m` exists. -/
noncomputable def canonicalAssociate (F : (ℕ → ℕ) → ℕ) : ℕ → ℕ := fun k =>
  @ite _ (Determines F (decodeList k)) (Classical.propDecidable _)
    (F (extendZero (decodeList k)) + 1) 0

/-- Unfolding of `canonicalAssociate` on the code of a sequence: the coding
round-trips, so the associate genuinely tests `Determines F σ`. -/
theorem canonicalAssociate_code (F : (ℕ → ℕ) → ℕ) (σ : List ℕ) :
    canonicalAssociate F (code σ) =
      @ite _ (Determines F σ) (Classical.propDecidable _)
        (F (extendZero σ) + 1) 0 := by
  unfold canonicalAssociate
  rw [decodeList_code]

theorem canonicalAssociate_of_determines {F : (ℕ → ℕ) → ℕ} {σ : List ℕ}
    (h : Determines F σ) :
    canonicalAssociate F (code σ) = F (extendZero σ) + 1 := by
  rw [canonicalAssociate_code]
  exact if_pos h

theorem canonicalAssociate_of_not_determines {F : (ℕ → ℕ) → ℕ} {σ : List ℕ}
    (h : ¬ Determines F σ) :
    canonicalAssociate F (code σ) = 0 := by
  rw [canonicalAssociate_code]
  exact if_neg h

theorem determines_of_canonicalAssociate_ne_zero {F : (ℕ → ℕ) → ℕ}
    {σ : List ℕ} (h : canonicalAssociate F (code σ) ≠ 0) :
    Determines F σ := by
  by_contra hcon
  exact h (canonicalAssociate_of_not_determines hcon)

/-- **Every continuous functional has an associate** — the harder direction
of the main theorem.  The modulus of continuity at `α` produces a stage `N`
with `Determines F (initSeg α N)`, so the canonical associate fires at `N`;
the associate condition is then verified at the *least* firing stage along
`α`, where the value is again forced to be `F α + 1` because `α` itself
extends the determining segment. -/
theorem hasAssociate_of_continuous {F : (ℕ → ℕ) → ℕ} (hF : Continuous2 F) :
    ∃ a : ℕ → ℕ, IsAssociate a F := by
  classical
  refine ⟨canonicalAssociate F, fun α => ?_⟩
  -- The modulus of continuity at `α` yields a determining segment.
  obtain ⟨N, hN⟩ := hF α
  have hdet : Determines F (initSeg α N) := by
    intro β hβ
    rw [initSeg_length] at hβ
    have hβα : F α = F β := hN β (fun i hi => (initSeg_eq_iff.mp hβ i hi).symm)
    have hzα : F α = F (extendZero (initSeg α N)) := by
      apply hN
      intro i hi
      have h0 : initSeg (extendZero (initSeg α N)) N = initSeg α N := by
        have h1 := initSeg_extendZero (initSeg α N)
        rwa [initSeg_length] at h1
      exact (initSeg_eq_iff.mp h0 i hi).symm
    rw [← hβα]
    exact hzα
  -- Hence the canonical associate fires somewhere along `α`; take the
  -- least firing stage.
  have hfire : canonicalAssociate F (code (initSeg α N)) ≠ 0 := by
    rw [canonicalAssociate_of_determines hdet]
    exact Nat.succ_ne_zero _
  have hex : ∃ n, canonicalAssociate F (code (initSeg α n)) ≠ 0 := ⟨N, hfire⟩
  refine ⟨Nat.find hex, ?_, fun m hm => ?_⟩
  · -- At the least firing stage the value is forced to be `F α + 1`,
    -- because `α` extends its own determining segment.
    have hdet₀ : Determines F (initSeg α (Nat.find hex)) :=
      determines_of_canonicalAssociate_ne_zero (Nat.find_spec hex)
    have hα : F α = F (extendZero (initSeg α (Nat.find hex))) := by
      apply hdet₀
      rw [initSeg_length]
    rw [canonicalAssociate_of_determines hdet₀, ← hα]
  · -- Below the least firing stage the associate reads `0`.
    by_contra hne
    exact Nat.find_min hex hm hne

/-- **Every associate genuinely defines a continuous functional** — the
firing stage of the associate at `α` is a modulus of continuity at `α`.
If `β` agrees with `α` up to that stage then the associate runs identically
on both prefix chains up to it, so by the first-fire principle it computes
`F β + 1` and `F α + 1` at the same segment, forcing `F α = F β`. -/
theorem continuous_of_hasAssociate {a : ℕ → ℕ} {F : (ℕ → ℕ) → ℕ}
    (ha : IsAssociate a F) : Continuous2 F := by
  intro α
  obtain ⟨n, hv, hz⟩ := ha α
  refine ⟨n, fun β hβ => ?_⟩
  have hseg : ∀ m ≤ n, initSeg α m = initSeg β m := fun m hm =>
    initSeg_eq_iff.mpr (fun i hi => hβ i (lt_of_lt_of_le hi hm))
  have hv' : a (code (initSeg β n)) = F α + 1 := by
    rw [← hseg n le_rfl]
    exact hv
  have hz' : ∀ m < n, a (code (initSeg β m)) = 0 := fun m hm => by
    rw [← hseg m (le_of_lt hm)]
    exact hz m hm
  have hβval : a (code (initSeg β n)) = F β + 1 :=
    ha.firstFire_eq (by rw [hv']; exact Nat.succ_ne_zero _) hz'
  rw [hv'] at hβval
  omega

/-- **Kleene's characterization**: a type-2 functional is continuous iff it
has an associate (Kleene 1959; Longley–Normann 2015, Ch. 8). -/
theorem continuous_iff_hasAssociate {F : (ℕ → ℕ) → ℕ} :
    Continuous2 F ↔ ∃ a : ℕ → ℕ, IsAssociate a F :=
  ⟨hasAssociate_of_continuous, fun ⟨_, ha⟩ => continuous_of_hasAssociate ha⟩

end ContinuousFunctionals
