/-
# The extensional collapse: hereditary total-extensionality on `K₂`

The other, textbook-canonical way to build the countable functionals:
instead of total Lean functionals witnessed by associates, work *inside*
the type-1 functions and Kleene application.  Define, by recursion on the
level, a partial equivalence relation

* `CtPer 0 g g'` — equality of type-1 functions;
* `CtPer (n+1) b b'` — for all `g ≈ₙ g'`, both `b | g` and `b' | g'` are
  defined and equal;

and take the countable functionals of level `n + 1` to be the equivalence
classes of self-related elements (`CtQ` in `CtQ.lean`).  This is the
extensional collapse of Kleene's second algebra `K₂` (Longley, *Notions
of computability at higher types I*, §3.3.1 — "this is essentially an
extensional collapse construction", with the general notion in his
Definition 1.2 and §5.1; Longley–Normann 2015, Ch. 8).

The theorem of this file is the **master bridge** `ctPer_iff_assoc`:

`CtPer n b b'  ↔  ∃ x : PureType (n+1), Assoc n b x ∧ Assoc n b' x`

— two type-1 functions are collapse-equivalent iff they are associates of
a common functional.  So the PER presentation and the `Assoc` presentation
of the hierarchy describe the same objects: self-relatedness is "is an
associate of something" (`Assoc.ctPer_self` and the converse), and the
class of `b` is the set of associates of the functional `b` computes.
The forward direction manufactures the common functional classically —
its value at `x` is `b | (some associate of x)`, well defined up to the
PER by exactly the associate-independence isolated at type 3.

Everything runs on the `Application.lean` interface (`kleeneApply`,
`ApplyDefined`, first-fire lemmas); no new computation machinery is
needed.
-/
import ContinuousFunctionals.Hierarchy

namespace ContinuousFunctionals

/-- **The collapse PER**: hereditary totality-and-extensionality on
type-1 functions.  `CtPer 0` is equality (every point of Baire space
denotes itself); `CtPer (n+1) b b'` says that on arguments related at the
level below, `b` and `b'` are defined and agree — they compute the same
level-`(n+2)` functional.  Partial equivalence relation: symmetric and
transitive (`CtPer.symm`, `CtPer.trans`) but reflexive only on the
"hereditarily total extensional" elements, which is the point. -/
def CtPer : ℕ → (ℕ → ℕ) → (ℕ → ℕ) → Prop
  | 0, g, g' => g = g'
  | n + 1, b, b' => ∀ g g' : ℕ → ℕ, CtPer n g g' →
      ApplyDefined b g ∧ ApplyDefined b' g' ∧
        kleeneApply b g = kleeneApply b' g'

theorem CtPer.symm : ∀ {n : ℕ} {b b' : ℕ → ℕ}, CtPer n b b' → CtPer n b' b := by
  intro n
  induction n with
  | zero =>
    intro b b' h
    exact Eq.symm h
  | succ m ih =>
    intro b b' h g g' hgg'
    obtain ⟨h1, h2, h3⟩ := h g' g (ih hgg')
    exact ⟨h2, h1, h3.symm⟩

theorem CtPer.trans : ∀ {n : ℕ} {b b' b'' : ℕ → ℕ},
    CtPer n b b' → CtPer n b' b'' → CtPer n b b'' := by
  intro n
  induction n with
  | zero =>
    intro b b' b'' h h'
    exact Eq.trans h h'
  | succ m ih =>
    intro b b' b'' h h' g g' hgg'
    have hgg : CtPer m g g := ih hgg' (CtPer.symm hgg')
    obtain ⟨h1, h2, h3⟩ := h g g hgg
    obtain ⟨h4, h5, h6⟩ := h' g g' hgg'
    exact ⟨h1, h5, h3.trans h6⟩

/-- **The master bridge**: the collapse PER and the associate relation
present the same hierarchy.  Two type-1 functions are related at level
`n` iff they are associates of a common functional of pure type `n + 1`.

Backward: associates of a common `x` are defined and agree on all
related arguments, because related arguments are themselves co-associates
of a common lower-level object (induction) and `Assoc` forces the value
`x`-side by the first-fire discipline.  Forward: the common functional is
built classically — at an argument `x` with an associate, answer
`b | (chosen associate of x)`; associate-independence (the PER clause,
via `b ≈ b` from `b ≈ b'`) makes the choice immaterial. -/
theorem ctPer_iff_assoc : ∀ (n : ℕ) (b b' : ℕ → ℕ),
    CtPer n b b' ↔ ∃ x : PureType (n + 1), Assoc n b x ∧ Assoc n b' x := by
  intro n
  induction n with
  | zero =>
    intro b b'
    constructor
    · intro h
      exact ⟨b', h, rfl⟩
    · rintro ⟨x, hb, hb'⟩
      have h1 : b = x := hb
      have h2 : b' = x := hb'
      show b = b'
      rw [h1, h2]
  | succ m ih =>
    intro b b'
    constructor
    · intro h
      classical
      have hbb : CtPer (m + 1) b b := CtPer.trans h (CtPer.symm h)
      set Φ : PureType (m + 2) := fun x =>
        if hx : ∃ g, Assoc m g x then kleeneApply b hx.choose else 0
        with hΦdef
      have key : ∀ c : ℕ → ℕ, CtPer (m + 1) b c → Assoc (m + 1) c Φ := by
        intro c hc x g hg
        have hx : ∃ g', Assoc m g' x := ⟨g, hg⟩
        have hgg₀ : CtPer m g hx.choose :=
          (ih g hx.choose).mpr ⟨x, hg, hx.choose_spec⟩
        obtain ⟨hdb, hdc, heq⟩ := hc hx.choose g (CtPer.symm hgg₀)
        obtain ⟨k, v, hv, hz⟩ := hdc.exists_fire
        refine ⟨k, ?_, hz⟩
        have hval : kleeneApply c g = v := kleeneApply_eq_of_fire hv hz
        have hΦx : Φ x = kleeneApply b hx.choose := by
          simp only [hΦdef]
          exact dif_pos hx
        rw [hv, hΦx, heq, hval]
      exact ⟨Φ, key b hbb, key b' h⟩
    · rintro ⟨x, hb, hb'⟩
      intro g g' hgg'
      obtain ⟨y, hg, hg'⟩ := (ih g g').mp hgg'
      obtain ⟨k, hv, hz⟩ := hb y g hg
      obtain ⟨k', hv', hz'⟩ := hb' y g' hg'
      refine ⟨⟨k, ?_⟩, ⟨k', ?_⟩, ?_⟩
      · rw [hv]
        exact Nat.succ_ne_zero _
      · rw [hv']
        exact Nat.succ_ne_zero _
      · rw [kleeneApply_eq_of_fire hv hz, kleeneApply_eq_of_fire hv' hz']

/-- Every associate is self-related: having something to compute is
hereditary total-extensionality. -/
theorem Assoc.ctPer_self {n : ℕ} {b : ℕ → ℕ} {x : PureType (n + 1)}
    (h : Assoc n b x) : CtPer n b b :=
  (ctPer_iff_assoc n b b).mpr ⟨x, h, h⟩

/-- The bridge at level 1, in the type-2 vocabulary: collapse-equivalence
is "associates of a common continuous functional". -/
theorem ctPer_one_iff {b b' : ℕ → ℕ} :
    CtPer 1 b b' ↔ ∃ F : (ℕ → ℕ) → ℕ, IsAssociate b F ∧ IsAssociate b' F := by
  rw [ctPer_iff_assoc 1 b b']
  constructor
  · rintro ⟨F, h1, h2⟩
    exact ⟨F, assoc_one_iff.mp h1, assoc_one_iff.mp h2⟩
  · rintro ⟨F, h1, h2⟩
    exact ⟨F, assoc_one_iff.mpr h1, assoc_one_iff.mpr h2⟩

/-- The bridge at level 2, in the type-3 vocabulary: self-relatedness is
"is an associate of some type-3 functional". -/
theorem ctPer_two_self_iff {b : ℕ → ℕ} :
    CtPer 2 b b ↔ ∃ Φ : ((ℕ → ℕ) → ℕ) → ℕ, IsAssociate3 b Φ := by
  rw [ctPer_iff_assoc 2 b b]
  constructor
  · rintro ⟨Φ, h1, -⟩
    exact ⟨Φ, assoc_two_iff.mp h1⟩
  · rintro ⟨Φ, h1⟩
    exact ⟨Φ, assoc_two_iff.mpr h1, assoc_two_iff.mpr h1⟩

end ContinuousFunctionals
