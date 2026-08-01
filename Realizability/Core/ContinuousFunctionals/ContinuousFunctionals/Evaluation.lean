/-
# Evaluation functionals have explicit associates

The canonical inhabitants of the higher types beyond constants: evaluation
at a fixed argument.  The construction here is *level-free*: `evalAssociate
γ` computes, from a prefix of a sequence `a`, the first-fire value of `a`
along the prefix chain of the fixed sequence `γ` — and this is where the
graph-reading subtlety of the higher types appears: a prefix of `a` of
length `m` reveals the values `a 0, …, a (m-1)`, i.e. `a`'s answers on
exactly those coded segments whose *code* is below `m`.  So `evalAssociate`
reads a prefix `ρ` of `a` and searches for a stage `r` such that

* every probe position `code (initSeg γ r')` for `r' ≤ r` falls inside `ρ`
  (the prefix is long enough to *see* `a`'s answers on the first `r + 1`
  segments of `γ`), and
* those answers are `0` strictly below `r` and nonzero at `r` — i.e. `ρ`
  witnesses `a`'s first fire on the prefix chain of `γ`.

The core theorem `evalAssociate_fire_of_fire` mentions no types at all:
if `a` first-fires along `γ` with value `v`, then `evalAssociate γ`
first-fires along `a` with the same `v`.  Instantiated at type 3
(`isAssociate3_evalAssociate`): for a point `α₀` of Baire space, the
functional `Φ F = F α₀` is in `Ct(3)`.  `Hierarchy.lean` instantiates the
same core lemma at every pure type.

Readiness is unique per prefix (`EvalReady.unique`), so the definition
needs no search bound — a `Classical.epsilon` picks the witness stage.
-/
import ContinuousFunctionals.Composition
import ContinuousFunctionals.Associate3

namespace ContinuousFunctionals

/-- The probe position for stage `r`: where an associate records its
answer on the length-`r` initial segment of `γ`. -/
def probe (γ : ℕ → ℕ) (r : ℕ) : ℕ :=
  code (initSeg γ r)

/-- `EvalReady γ ρ r`: the finite prefix `ρ` (of some intended sequence)
is long enough to see the probe positions of `γ` up to stage `r`, and its
entries there witness a first fire at `r`: zeros strictly below, nonzero
at `r`. -/
def EvalReady (γ : ℕ → ℕ) (ρ : List ℕ) (r : ℕ) : Prop :=
  (∀ r' ≤ r, probe γ r' < ρ.length) ∧
    (∀ r' < r, ρ.getD (probe γ r') 0 = 0) ∧
    ρ.getD (probe γ r) 0 ≠ 0

instance (γ : ℕ → ℕ) (ρ : List ℕ) (r : ℕ) : Decidable (EvalReady γ ρ r) := by
  unfold EvalReady
  infer_instance

/-- At most one stage is ready on a given prefix: two ready stages would
each declare the other's fire position zero. -/
theorem EvalReady.unique {γ : ℕ → ℕ} {ρ : List ℕ} {r r' : ℕ}
    (h : EvalReady γ ρ r) (h' : EvalReady γ ρ r') : r = r' := by
  unfold EvalReady at h h'
  obtain ⟨-, hz, hnz⟩ := h
  obtain ⟨-, hz', hnz'⟩ := h'
  rcases lt_trichotomy r r' with hlt | heq | hgt
  · exact absurd (hz' r hlt) hnz
  · exact heq
  · exact absurd (hz r' hgt) hnz'

/-- On a genuine prefix of a sequence `a`, readiness says exactly: all
probes up to `r` are visible, and `a` itself first fires on the prefix
chain of `γ` at stage `r`. -/
theorem evalReady_initSeg_iff {γ a : ℕ → ℕ} {n r : ℕ} :
    EvalReady γ (initSeg a n) r ↔
      ((∀ r' ≤ r, probe γ r' < n) ∧ (∀ r' < r, a (probe γ r') = 0) ∧
        a (probe γ r) ≠ 0) := by
  unfold EvalReady
  rw [initSeg_length]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, fun r' hr' => ?_, ?_⟩
    · rw [← initSeg_getD a (h1 r' (le_of_lt hr'))]
      exact h2 r' hr'
    · rw [← initSeg_getD a (h1 r le_rfl)]
      exact h3
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, fun r' hr' => ?_, ?_⟩
    · rw [initSeg_getD a (h1 r' (le_of_lt hr'))]
      exact h2 r' hr'
    · rw [initSeg_getD a (h1 r le_rfl)]
      exact h3

/-- The value `evalAssociate` reads off a finite prefix `ρ`: the entry at
the unique ready stage's probe position, or `0` if no stage is ready. -/
noncomputable def evalOnList (γ : ℕ → ℕ) (ρ : List ℕ) : ℕ :=
  if EvalReady γ ρ (Classical.epsilon (EvalReady γ ρ)) then
    ρ.getD (probe γ (Classical.epsilon (EvalReady γ ρ))) 0
  else 0

theorem evalOnList_of_ready {γ : ℕ → ℕ} {ρ : List ℕ} {r : ℕ}
    (h : EvalReady γ ρ r) :
    evalOnList γ ρ = ρ.getD (probe γ r) 0 := by
  have heps : EvalReady γ ρ (Classical.epsilon (EvalReady γ ρ)) :=
    Classical.epsilon_spec (p := EvalReady γ ρ) ⟨r, h⟩
  unfold evalOnList
  rw [if_pos heps, EvalReady.unique heps h]

theorem evalOnList_of_not_ready {γ : ℕ → ℕ} {ρ : List ℕ}
    (h : ∀ r, ¬ EvalReady γ ρ r) :
    evalOnList γ ρ = 0 := by
  unfold evalOnList
  rw [if_neg (h _)]

/-- **The evaluation associate** for the sequence `γ`: on (the code of) a
prefix `ρ` of an argument sequence, answer `evalOnList γ ρ`. -/
noncomputable def evalAssociate (γ : ℕ → ℕ) : ℕ → ℕ := fun k =>
  evalOnList γ (decodeList k)

theorem evalAssociate_code (γ : ℕ → ℕ) (σ : List ℕ) :
    evalAssociate γ (code σ) = evalOnList γ σ := by
  unfold evalAssociate
  rw [decodeList_code]

/-- **The level-free core**: if `a` first-fires along the prefix chain of
`γ` with value `v`, then `evalAssociate γ` first-fires along the prefix
chain of `a` with the same value `v` — namely at the least stage of `a` at
which all probe positions of `γ` up to `a`'s fire stage are visible.
Before that stage no stage is ready and `evalAssociate γ` is silent. -/
theorem evalAssociate_fire_of_fire {γ a : ℕ → ℕ} {v rs : ℕ}
    (hval : a (code (initSeg γ rs)) = v + 1)
    (hzero : ∀ m < rs, a (code (initSeg γ m)) = 0) :
    ∃ n, evalAssociate γ (code (initSeg a n)) = v + 1 ∧
      ∀ m < n, evalAssociate γ (code (initSeg a m)) = 0 := by
  classical
  -- Readiness on genuine prefixes of `a` happens exactly at stage `rs`,
  -- as soon as all probes up to `rs` are visible.
  have hchar : ∀ n r, EvalReady γ (initSeg a n) r ↔
      ((∀ r' ≤ rs, probe γ r' < n) ∧ r = rs) := by
    intro n r
    rw [evalReady_initSeg_iff]
    constructor
    · rintro ⟨h1, h2, h3⟩
      have hr : r = rs := by
        rcases lt_trichotomy r rs with hlt | heq | hgt
        · exact absurd (hzero r hlt) h3
        · exact heq
        · refine absurd (h2 rs hgt) ?_
          rw [show probe γ rs = code (initSeg γ rs) from rfl, hval]
          exact Nat.succ_ne_zero _
      subst hr
      exact ⟨h1, rfl⟩
    · rintro ⟨h1, rfl⟩
      refine ⟨h1, fun r' hr' => hzero r' hr', ?_⟩
      rw [show probe γ r = code (initSeg γ r) from rfl, hval]
      exact Nat.succ_ne_zero _
  -- Some prefix of `a` sees all probes up to `rs`; take the least such.
  obtain ⟨M, hM⟩ := exists_bound (fun r' => probe γ r') (rs + 1)
  have hex : ∃ n, ∀ r' ≤ rs, probe γ r' < n :=
    ⟨M + 1, fun r' hr' => Nat.lt_succ_of_le (hM r' (Nat.lt_succ_of_le hr'))⟩
  refine ⟨Nat.find hex, ?_, fun m hm => ?_⟩
  · -- At the least visible stage: ready at `rs`, and the entry read there
    -- is `a`'s fire value `v + 1`.
    have hvis := Nat.find_spec hex
    have hready : EvalReady γ (initSeg a (Nat.find hex)) rs :=
      (hchar _ rs).mpr ⟨hvis, rfl⟩
    rw [evalAssociate_code, evalOnList_of_ready hready,
      initSeg_getD a (hvis rs le_rfl)]
    exact hval
  · -- Below it: no stage is ready, so the associate is silent.
    rw [evalAssociate_code]
    apply evalOnList_of_not_ready
    intro r hr
    exact Nat.find_min hex hm ((hchar m r).mp hr).1

/-- **Evaluation at a point is in `Ct(3)`**: for a fixed point `α₀` of
Baire space, `evalAssociate α₀` is a type-3 associate of `Φ F = F α₀`.
Instance of the level-free core: any associate `a` of `F` first-fires
along `α₀` with value `F α₀` by definition. -/
theorem isAssociate3_evalAssociate (α₀ : ℕ → ℕ) :
    IsAssociate3 (evalAssociate α₀) (fun F => F α₀) := by
  intro F a ha
  obtain ⟨rs, hval, hzero⟩ := ha α₀
  exact evalAssociate_fire_of_fire hval hzero

end ContinuousFunctionals
