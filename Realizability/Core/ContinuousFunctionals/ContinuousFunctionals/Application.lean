/-
# Kleene application of type-1 functions

Kleene's partial application operation `f | g` is the engine of the
associates presentation of the countable functionals: `f | g ≃ f(ḡ(r)) − 1`
where `r` is *least* with `f(ḡ(r)) > 0` (Longley, *Notions of computability
at higher types I*, §3.3.1, displayed before Definition 3.13).  At type 2 it
is implicit in `IsAssociate`; at type 3 it is how an associate consumes an
associate, so it needs a name of its own.

This file defines `kleeneApply b a` (with junk value `0` off the domain —
all theorems require `ApplyDefined`), and proves the interface the rest of
the development uses:

* `fire_value_unique` — the first-fire value along a fixed sequence is
  unique, so `kleeneApply` is characterized by any first-fire witness
  (`kleeneApply_eq_of_fire`);
* `isAssociate_iff_kleeneApply` — `IsAssociate a F` says exactly
  `a | α = F α` (defined and equal) for every `α`, turning the docstring
  equation of `IsAssociate` into a theorem;
* `IsAssociate.determines` — an associate determines its functional, the
  right-uniqueness half of the associate relation.
-/
import ContinuousFunctionals.Associate

namespace ContinuousFunctionals

/-- `ApplyDefined b a`: the Kleene application `b | a` is defined — `b`
answers on some finite prefix of the sequence `a`. -/
def ApplyDefined (b a : ℕ → ℕ) : Prop :=
  ∃ r, b (code (initSeg a r)) ≠ 0

/-- **First-fire values are unique.**  If `b` fires on the prefix chain of
`a` at stage `n` with value `v` (zeros strictly below), and also at stage
`n'` with value `v'`, then `v = v'` (and in fact `n = n'`): the two
witnesses collide by trichotomy, since each declares zeros below itself. -/
theorem fire_value_unique {b a : ℕ → ℕ} {n n' v v' : ℕ}
    (hv : b (code (initSeg a n)) = v + 1)
    (hz : ∀ m < n, b (code (initSeg a m)) = 0)
    (hv' : b (code (initSeg a n')) = v' + 1)
    (hz' : ∀ m < n', b (code (initSeg a m)) = 0) :
    v = v' := by
  rcases lt_trichotomy n n' with h | h | h
  · have h0 := hz' n h
    rw [hv] at h0
    omega
  · subst h
    rw [hv] at hv'
    omega
  · have h0 := hz n' h
    rw [hv'] at h0
    omega

/-- **Kleene application** `b | a`: the value `v` such that `b`, run along
the coded prefix chain of `a`, first answers `v + 1`.  Defined via
`Classical.epsilon`, which by `fire_value_unique` picks *the* first-fire
value whenever `ApplyDefined b a` holds; off the domain the value is
unspecified junk and no theorem below mentions it.  This is the operation
`f | g ≃ f(ḡ(r)) − 1`, `r` least with `f(ḡ(r)) > 0`, of Longley §3.3.1. -/
noncomputable def kleeneApply (b a : ℕ → ℕ) : ℕ :=
  Classical.epsilon fun v =>
    ∃ n, b (code (initSeg a n)) = v + 1 ∧ ∀ m < n, b (code (initSeg a m)) = 0

/-- Any first-fire witness computes `kleeneApply`. -/
theorem kleeneApply_eq_of_fire {b a : ℕ → ℕ} {n v : ℕ}
    (hv : b (code (initSeg a n)) = v + 1)
    (hz : ∀ m < n, b (code (initSeg a m)) = 0) :
    kleeneApply b a = v := by
  have hspec := Classical.epsilon_spec
    (p := fun v => ∃ n, b (code (initSeg a n)) = v + 1 ∧
      ∀ m < n, b (code (initSeg a m)) = 0) ⟨v, n, hv, hz⟩
  obtain ⟨n', hv', hz'⟩ := hspec
  exact fire_value_unique hv' hz' hv hz

/-- A defined application has a first-fire witness: take the least stage
with a nonzero answer. -/
theorem ApplyDefined.exists_fire {b a : ℕ → ℕ} (h : ApplyDefined b a) :
    ∃ n v, b (code (initSeg a n)) = v + 1 ∧
      ∀ m < n, b (code (initSeg a m)) = 0 := by
  classical
  have hex : ∃ r, b (code (initSeg a r)) ≠ 0 := h
  refine ⟨Nat.find hex, b (code (initSeg a (Nat.find hex))) - 1, ?_,
    fun m hm => ?_⟩
  · have h1 := Nat.find_spec hex
    omega
  · by_contra hne
    exact Nat.find_min hex hm hne

/-- An associate applies to every point: the application is defined. -/
theorem IsAssociate.applyDefined {a : ℕ → ℕ} {F : (ℕ → ℕ) → ℕ}
    (ha : IsAssociate a F) (α : ℕ → ℕ) : ApplyDefined a α := by
  obtain ⟨n, hv, _⟩ := ha α
  exact ⟨n, by rw [hv]; exact Nat.succ_ne_zero _⟩

/-- An associate computes its functional through Kleene application:
`a | α = F α`. -/
theorem IsAssociate.kleeneApply_eq {a : ℕ → ℕ} {F : (ℕ → ℕ) → ℕ}
    (ha : IsAssociate a F) (α : ℕ → ℕ) :
    kleeneApply a α = F α := by
  obtain ⟨n, hv, hz⟩ := ha α
  exact kleeneApply_eq_of_fire hv hz

/-- **`IsAssociate` is Kleene application, verbatim**: `a` is an associate
of `F` iff `a | α` is defined and equals `F α` at every `α`.  (Definedness
cannot be dropped: off its domain `kleeneApply` returns junk `0`, which
could accidentally agree with `F`.)  This is the type-2 clause of Longley
§3.3.1, Definition 3.13, as a theorem about our `IsAssociate`. -/
theorem isAssociate_iff_kleeneApply {a : ℕ → ℕ} {F : (ℕ → ℕ) → ℕ} :
    IsAssociate a F ↔ ∀ α, ApplyDefined a α ∧ kleeneApply a α = F α := by
  constructor
  · intro ha α
    exact ⟨ha.applyDefined α, ha.kleeneApply_eq α⟩
  · intro h α
    obtain ⟨hd, hval⟩ := h α
    obtain ⟨n, v, hv, hz⟩ := hd.exists_fire
    have hveq : v = F α := by
      rw [← hval]
      exact (kleeneApply_eq_of_fire hv hz).symm
    exact ⟨n, by rw [hv, hveq], hz⟩

/-- **An associate determines its functional**: the associate relation is
right-unique.  This is why quantifying over "all associates of `F`" in the
type-3 definition is coherent — a single sequence can code at most one
type-2 functional. -/
theorem IsAssociate.determines {a : ℕ → ℕ} {F F' : (ℕ → ℕ) → ℕ}
    (h : IsAssociate a F) (h' : IsAssociate a F') : F = F' := by
  funext α
  rw [← h.kleeneApply_eq α, ← h'.kleeneApply_eq α]

end ContinuousFunctionals
