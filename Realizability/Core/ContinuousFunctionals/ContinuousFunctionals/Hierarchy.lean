/-
# The full hierarchy: associates at every pure finite type

Kleene's inductive definition of the countable functionals, uniformly in
the type level (Longley, *Notions of computability at higher types I*,
§3.3.1, Definition 3.13; Kleene 1959; Longley–Normann 2015, Ch. 8):

* `C₀ = ℕ`, `C₁ = ℕ → ℕ`, and each `f ∈ C₁` is an associate of itself;
* for `n ≥ 1`, `f ∈ C₁` is an associate of `F : Cₙ → ℕ` iff whenever `g`
  is an associate of `G ∈ Cₙ`, `f | g = F(G)`; and `Cₙ₊₁` is the set of
  functions with an associate.

Formalized as: `PureType` (the pure finite types over `ℕ`), the associate
relation `Assoc n a x` for `x : PureType (n+1)` (a single structural
recursion — no separate `Ct` is needed inside it, since "`G` has an
associate at the lower level" is self-contained), and `Ct n` — the
countable = Kleene–Kreisel functionals of pure type `n`.

The level-by-level developments are the sanity anchor for the uniform
definition and become its instances: `Assoc 0` is definitional equality of
type-1 functions, `Assoc 1` is `IsAssociate` (`assoc_one_iff`), and
`Assoc 2` is `IsAssociate3` (`assoc_two_iff`).  In particular membership
in `Ct 2` is topological continuity (`mem_ct_two_iff_continuous2` with
`continuous2_iff_continuous`).  The machinery built at those levels was
already level-free (first-fire, `kleeneApply`, `evalAssociate`), so the
uniform theorems below — constants, evaluation, agreement of co-associated
functionals on `Ct`, and the peek non-example — are direct instantiations,
not new arguments.

Modeling note (as at type 3): functionals are total Lean functions on
`PureType n`, constrained by `Assoc` only on the continuous fragment.
Accordingly right-uniqueness holds *on `Ct`* (`Assoc.eq_on_ct`), not as
equality of total functions.  Packaging `Ct` as an honest extensional
collapse is deliberately deferred (density-theorem territory).
-/
import ContinuousFunctionals.SanityChecks3
import ContinuousFunctionals.MainTheorem

namespace ContinuousFunctionals

/-- The pure finite types over `ℕ`: type `0` is `ℕ`, and type `n + 1` is
the type of functions from type `n` to `ℕ`. -/
def PureType : ℕ → Type
  | 0 => ℕ
  | n + 1 => PureType n → ℕ

/-- **Kleene's associate relation at every pure type** (Longley §3.3.1,
Definition 3.13).  `Assoc n a x` says the type-1 function `a` is an
associate of `x : PureType (n + 1)`:

* at the base (`n = 0`), every type-1 function is an associate of itself;
* at level `n + 1`, `b` is an associate of `F` iff along the prefix chain
  of any associate `g` of any `G` of the level below, `b` is silent and
  then fires with value `F G + 1` — that is, `b | g = F G` in Kleene's
  application.

Objects of type `0` (numbers) need no associates; the recursion runs over
the function types only, which is why the index is shifted by one. -/
def Assoc : (n : ℕ) → (ℕ → ℕ) → PureType (n + 1) → Prop
  | 0, a, f => a = f
  | n + 1, b, F => ∀ (G : PureType (n + 1)) (g : ℕ → ℕ), Assoc n g G →
      ∃ m, b (code (initSeg g m)) = F G + 1 ∧
        ∀ k < m, b (code (initSeg g k)) = 0

/-- **The countable (Kleene–Kreisel) functionals** of each pure type: all
numbers at type `0`, and at function types the objects having an
associate.  `Ct 1` is all of Baire space (`ct_one_eq_univ`), and `Ct 2`
is the continuous type-2 functionals (`mem_ct_two_iff_continuous2`). -/
def Ct : (n : ℕ) → Set (PureType n)
  | 0 => Set.univ
  | n + 1 => {x | ∃ a, Assoc n a x}

@[simp] theorem assoc_zero_iff {a : ℕ → ℕ} {f : PureType 1} :
    Assoc 0 a f ↔ a = f :=
  Iff.rfl

/-- At level 1 the uniform definition is exactly `IsAssociate`: the
quantification over associates of type-1 objects collapses, since each is
its own unique associate. -/
theorem assoc_one_iff {b : ℕ → ℕ} {F : PureType 2} :
    Assoc 1 b F ↔ IsAssociate b F := by
  constructor
  · intro h α
    exact h α α rfl
  · intro h G g hg
    subst hg
    exact h g

/-- At level 2 the uniform definition is exactly `IsAssociate3`. -/
theorem assoc_two_iff {b : ℕ → ℕ} {Φ : PureType 3} :
    Assoc 2 b Φ ↔ IsAssociate3 b Φ := by
  constructor
  · intro h F a ha
    exact h F a (assoc_one_iff.mpr ha)
  · intro h G g hg
    exact h G g (assoc_one_iff.mp hg)

/-- Every point of Baire space is countable: `Ct 1` is everything. -/
theorem ct_one_eq_univ : Ct 1 = Set.univ := by
  ext f
  simp only [Set.mem_univ, iff_true]
  exact ⟨f, rfl⟩

/-- Membership in `Ct 2` is continuity: the uniform hierarchy restricts at
type 2 to the main theorem of this project.  (Via
`continuous2_iff_continuous`, equivalently topological continuity.) -/
theorem mem_ct_two_iff_continuous2 {F : PureType 2} :
    F ∈ Ct 2 ↔ Continuous2 F := by
  rw [continuous_iff_hasAssociate]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, assoc_one_iff.mp ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, assoc_one_iff.mpr ha⟩

/-- Constant functionals are countable at every level, with the constant
associate firing on the empty prefix. -/
theorem assoc_const (n c : ℕ) :
    Assoc (n + 1) (fun _ => c + 1) (fun _ => c : PureType (n + 2)) :=
  fun _ _ _ => ⟨0, rfl, fun m hm => absurd hm (Nat.not_lt_zero m)⟩

/-- **Evaluation is countable at every level**: for a fixed `x₀` of pure
type `n + 1` with associate `g₀`, the evaluation functional `F ↦ F x₀` —
of pure type `n + 3`, consuming the type-`(n + 2)` functionals that take
`x₀` as argument — has the explicit associate `evalAssociate g₀`.  Direct
instantiation of the level-free core `evalAssociate_fire_of_fire`: any
associate of `F` first-fires along `g₀` with value `F x₀`, by definition
of `Assoc`.  At `n = 0` this is `isAssociate3_evalAssociate`. -/
theorem assoc_eval {n : ℕ} (x₀ : PureType (n + 1)) (g₀ : ℕ → ℕ)
    (hg₀ : Assoc n g₀ x₀) :
    Assoc (n + 2) (evalAssociate g₀) (fun F => F x₀ : PureType (n + 3)) := by
  intro F a ha
  obtain ⟨rs, hval, hzero⟩ := ha x₀ g₀ hg₀
  exact evalAssociate_fire_of_fire hval hzero

/-- **Composition at every level.**  Given `Φ : PureType (n + 2)` with
associate `b`, and a map `h` of Baire space into level `n + 1` tracked
continuously — for each `α` the sequence `U α` is an associate of `h α`,
and `U` is itself produced coordinatewise by associates `u k` — the
composite `α ↦ Φ (h α)` is a continuous type-2 functional with the
explicit associate `compAssociate b u`: composing any countable
functional with a trackable argument map lands back in the worked type-2
theory, by the very construction built there.  Instance of the level-free
core `compAssociate_fire_of_fires`: the definition of `Assoc` says `b`
first-fires along `U α` with value `Φ (h α)`.  At `n = 0` the tracking
condition `Assoc 0 (U α) (h α)` collapses to `U α = h α` and this is
`isAssociate_compAssociate` verbatim. -/
theorem assoc_comp {n : ℕ} {Φ : PureType (n + 2)}
    {h : (ℕ → ℕ) → PureType (n + 1)} {b : ℕ → ℕ}
    {U : (ℕ → ℕ) → ℕ → ℕ} {u : ℕ → ℕ → ℕ}
    (hb : Assoc (n + 1) b Φ)
    (hU : ∀ α, Assoc n (U α) (h α))
    (hu : ∀ k, IsAssociate (u k) (fun α => U α k)) :
    IsAssociate (compAssociate b u) (fun α => Φ (h α)) := fun α =>
  compAssociate_fire_of_fires (fun k => hu k α) (hb (h α) (U α) (hU α))

/-- The purely qualitative corollary: composing a countable functional of
any level with a continuously tracked argument map yields a continuous
type-2 functional. -/
theorem continuous2_comp_assoc {n : ℕ} {Φ : PureType (n + 2)}
    {h : (ℕ → ℕ) → PureType (n + 1)}
    (hΦ : Φ ∈ Ct (n + 2))
    (htrack : ∃ U : (ℕ → ℕ) → ℕ → ℕ, (∀ α, Assoc n (U α) (h α)) ∧
      ∀ k, Continuous2 (fun α => U α k)) :
    Continuous2 (fun α => Φ (h α)) := by
  obtain ⟨b, hb⟩ := hΦ
  obtain ⟨U, hU, hUc⟩ := htrack
  choose u hu using fun k => hasAssociate_of_continuous (hUc k)
  exact continuous_of_hasAssociate (assoc_comp hb hU hu)

/-- **Co-associated functionals agree on the countable fragment**: a
single associate pins down a functional's values at every countable
argument.  (Equality of the total Lean functions is not available — and
not meaningful — off `Ct`; cf. the modeling note in the header.) -/
theorem Assoc.eq_on_ct {n : ℕ} {b : ℕ → ℕ} {Φ Φ' : PureType (n + 2)}
    (h : Assoc (n + 1) b Φ) (h' : Assoc (n + 1) b Φ') :
    ∀ x ∈ Ct (n + 1), Φ x = Φ' x := by
  rintro x ⟨g, hg⟩
  obtain ⟨m, hv, hz⟩ := h x g hg
  obtain ⟨m', hv', hz'⟩ := h' x g hg
  exact fire_value_unique hv hz hv' hz'

/-- An associate of the constant functional carrying an arbitrary value
`v` at every position coding a nonempty sequence — positions never
consulted, since the fire happens already on the empty prefix. -/
def constAssociateAt (c v : ℕ) : ℕ → ℕ := fun k =>
  if decodeList k = [] then c + 1 else v

theorem assoc_constAssociateAt (n c v : ℕ) :
    Assoc (n + 1) (constAssociateAt c v) (fun _ => c : PureType (n + 2)) :=
  fun _ g _ =>
    ⟨0, by simp [constAssociateAt], fun m hm => absurd hm (Nat.not_lt_zero m)⟩

/-- **Associate-independence bites at every level above 2**: the function
peeking at position `code [0]` of its argument sequence is an associate of
no functional of any level `n + 3`.  Fed the associates
`constAssociateAt 0 0` and `constAssociateAt 0 1` of the *same* constant
functional of level `n + 2`, it fires with two different values.  (At
level 2 there is no such phenomenon: type-1 objects have unique
associates, which is why `Assoc 1` collapses to `IsAssociate`.) -/
theorem not_exists_assoc_peekAssociate (n : ℕ) :
    ¬ ∃ Φ : PureType (n + 3), Assoc (n + 2) (peekAssociate (code [0])) Φ := by
  rintro ⟨Φ, hΦ⟩
  have key : ∀ v : ℕ, Φ (fun _ => 0) = v := by
    intro v
    obtain ⟨m, hv, -⟩ :=
      hΦ (fun _ => 0) (constAssociateAt 0 v) (assoc_constAssociateAt n 0 v)
    rw [peekAssociate_code_initSeg] at hv
    by_cases hm : code [0] < m
    · rw [if_pos hm] at hv
      have ha : constAssociateAt 0 v (code [0]) = v := by
        simp [constAssociateAt]
      rw [ha] at hv
      omega
    · rw [if_neg hm] at hv
      omega
  have h0 := key 0
  have h1 := key 1
  omega

end ContinuousFunctionals
