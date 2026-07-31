/-
# Modified realizability over the pure-type hierarchy

Realizers are drawn from the Kleene–Kreisel development's `PureType`
hierarchy.  The central design decision is the **flexible ambient
level**: `MR ρ φ n x` says the object `x : PureType (n+1)` realizes `φ`
at ambient level `n`.  All clauses stay at one ambient level —
conjunction and disjunction read components by pointwise unpairing at
the same level, and implication/universal quantification consume
arguments one level down (`n-1`), pairing the argument into the
functional's input.  This eliminates level-coercion bookkeeping
entirely: no padding between mismatched levels ever occurs, because
levels never mismatch.  The formula-level function `lvl` records the
minimal adequate ambient level; `MR` itself is defined for every `n`
(instances below `lvl φ` are degenerate and never used by extraction).

The implication clause is the `Assoc`/`CtPer` clause shape — "for every
realizer of the antecedent, the application realizes the consequent" —
at the level of the pure functionals themselves; the associate-level
counterpart enters in `Soundness.lean` when classes in `CtQ` are formed.

Devices (all small, all level-uniform):

* `up`/`down` — the standard pure-type section/retraction pair;
* `pairPT`/`fstPT`/`sndPT` — pointwise pairing at every level ≥ 1;
* `app₁`/`abs₁` — application and abstraction through pairing, with the
  beta law `app₁_abs₁`;
* `natPT` — numerals at every level (for the `∀` clause).
-/
import ContinuousFunctionals.Hierarchy
import Realizability.Core.Syntax

namespace Realizability

open ContinuousFunctionals

/-! ## Pure-type devices -/

/-- The canonical element of each pure type. -/
def defaultPT : (n : ℕ) → PureType n
  | 0 => (0 : ℕ)
  | _ + 1 => fun _ => (0 : ℕ)

/-- A numeral at every level: the hereditarily constant functional. -/
def natPT : (n : ℕ) → ℕ → PureType n
  | 0, k => k
  | _ + 1, k => fun _ => k

mutual
  /-- The standard embedding of a pure type into the next level. -/
  def up : (n : ℕ) → PureType n → PureType (n + 1)
    | 0, k => fun _ => k
    | n + 1, F => fun G => F (down n G)
  /-- The standard projection of a pure type from the next level. -/
  def down : (n : ℕ) → PureType (n + 1) → PureType n
    | 0, f => f (0 : ℕ)
    | n + 1, H => fun x => H (up n x)
end

/-- `down` retracts `up`: the embedding is a section. -/
theorem down_up : ∀ (n : ℕ) (x : PureType n), down n (up n x) = x
  | 0, _ => rfl
  | n + 1, F => funext fun x => by
      show F (down n (up n x)) = F x
      rw [down_up n x]

/-- Pointwise pairing of two objects of the same level `n + 1`. -/
def pairPT {n : ℕ} (x y : PureType (n + 1)) : PureType (n + 1) :=
  fun z => Nat.pair (x z) (y z)

/-- First component of a pointwise pair. -/
def fstPT {n : ℕ} (x : PureType (n + 1)) : PureType (n + 1) :=
  fun z => (x z).unpair.1

/-- Second component of a pointwise pair. -/
def sndPT {n : ℕ} (x : PureType (n + 1)) : PureType (n + 1) :=
  fun z => (x z).unpair.2

@[simp] theorem fstPT_pairPT {n : ℕ} (x y : PureType (n + 1)) :
    fstPT (pairPT x y) = x := by
  funext z
  simp [fstPT, pairPT]

@[simp] theorem sndPT_pairPT {n : ℕ} (x y : PureType (n + 1)) :
    sndPT (pairPT x y) = y := by
  funext z
  simp [sndPT, pairPT]

/-- Application through pairing: a functional `F` of level `n + 2`
applied to an argument `x` of level `n + 1`, yielding a level-`(n + 1)`
result.  The result's own argument is embedded by `up` and paired with
`x` for `F` to consume. -/
def app₁ {n : ℕ} (F : PureType (n + 2)) (x : PureType (n + 1)) :
    PureType (n + 1) :=
  fun w => F (pairPT x (up n w))

/-- Abstraction through pairing: the inverse device to `app₁`. -/
def abs₁ {n : ℕ} (G : PureType (n + 1) → PureType (n + 1)) :
    PureType (n + 2) :=
  fun z => G (fstPT z) (down n (sndPT z))

/-- **Beta.**  `app₁ (abs₁ G) x = G x`. -/
theorem app₁_abs₁ {n : ℕ} (G : PureType (n + 1) → PureType (n + 1))
    (x : PureType (n + 1)) :
    app₁ (abs₁ G) x = G x := by
  funext w
  show G (fstPT (pairPT x (up n w))) (down n (sndPT (pairPT x (up n w)))) = _
  rw [fstPT_pairPT, sndPT_pairPT, down_up]

/-! ## The level function and the realizability relation -/

/-- The minimal adequate ambient level of a formula. -/
def lvl : Formula → ℕ
  | .bot => 0
  | .eq _ _ => 0
  | .and φ ψ => max (lvl φ) (lvl ψ)
  | .or φ ψ => max (lvl φ) (lvl ψ)
  | .imp φ ψ => max (lvl φ) (lvl ψ) + 1
  | .all _ φ => lvl φ + 1
  | .ex _ φ => lvl φ

/-- **Modified realizability at ambient level `n`** (Kreisel's modified
realizability, transposed to the pure-type hierarchy of the
Kleene–Kreisel development).  `MR ρ φ n x`:

* `⊥` is realized by nothing;
* `s ≐ t` is realized by anything, provided the equation holds — atomic
  formulas carry no computational content;
* `φ ∧ ψ`: both pointwise-unpaired components realize;
* `φ ∨ ψ`: a numeric tag (the first component, read at the canonical
  point) selects the disjunct the second component realizes;
* `φ → ψ`: every realizer of `φ` one level down is sent by `app₁` to a
  realizer of `ψ` — the `Assoc`-clause shape at functional level;
* `∀ y φ`: every numeral instance is realized (`app₁` at the numeral),
  with the environment updated;
* `∃ y φ`: the first component, read at the canonical point, is the
  **witness**, and the second realizes `φ` there — the standard
  existential clause, and structurally the `∨` clause with a numeral in
  place of a two-valued tag.  So it needs no new device and no new
  ambient level (`lvl (∃y φ) = lvl φ`): binders that *consume* realizers
  (`→`, `∀`) cost a level, binders that *package* them do not. -/
def MR (ρ : ℕ → ℕ) : (φ : Formula) → (n : ℕ) → PureType (n + 1) → Prop
  | .bot, _, _ => False
  | .eq s t, _, _ => s.eval ρ = t.eval ρ
  | .and φ ψ, n, x => MR ρ φ n (fstPT x) ∧ MR ρ ψ n (sndPT x)
  | .or φ ψ, n, x =>
      (fstPT x (defaultPT n) = 0 ∧ MR ρ φ n (sndPT x)) ∨
      (fstPT x (defaultPT n) ≠ 0 ∧ MR ρ ψ n (sndPT x))
  | .imp φ ψ, n, F =>
      match n with
      | 0 => False
      | m + 1 => ∀ x : PureType (m + 1), MR ρ φ m x → MR ρ ψ m (app₁ F x)
  | .all y φ, n, F =>
      match n with
      | 0 => False
      | m + 1 => ∀ k : ℕ, MR (Function.update ρ y k) φ m (app₁ F (natPT (m + 1) k))
  | .ex y φ, n, x =>
      MR (Function.update ρ y (fstPT x (defaultPT n))) φ n (sndPT x)

/-! ## Stability lemmas -/

/-- Realizability depends only on the environment's values at free
variables. -/
theorem MR_congr :
    ∀ (φ : Formula) {ρ ρ' : ℕ → ℕ} (n : ℕ) (x : PureType (n + 1)),
      (∀ y, φ.FreeIn y → ρ y = ρ' y) → (MR ρ φ n x ↔ MR ρ' φ n x) := by
  intro φ
  induction φ with
  | bot => intro ρ ρ' n x _; rfl
  | eq s t =>
    intro ρ ρ' n x h
    show s.eval ρ = t.eval ρ ↔ s.eval ρ' = t.eval ρ'
    rw [Term.eval_congr fun y hy => h y (Or.inl hy),
      Term.eval_congr fun y hy => h y (Or.inr hy)]
  | and φ ψ ihφ ihψ =>
    intro ρ ρ' n x h
    show MR ρ φ n _ ∧ MR ρ ψ n _ ↔ MR ρ' φ n _ ∧ MR ρ' ψ n _
    rw [ihφ n _ fun y hy => h y (Or.inl hy), ihψ n _ fun y hy => h y (Or.inr hy)]
  | or φ ψ ihφ ihψ =>
    intro ρ ρ' n x h
    show (_ ∧ MR ρ φ n _) ∨ (_ ∧ MR ρ ψ n _) ↔ (_ ∧ MR ρ' φ n _) ∨ (_ ∧ MR ρ' ψ n _)
    rw [ihφ n _ fun y hy => h y (Or.inl hy), ihψ n _ fun y hy => h y (Or.inr hy)]
  | imp φ ψ ihφ ihψ =>
    intro ρ ρ' n x h
    cases n with
    | zero => rfl
    | succ m =>
      show (∀ z, MR ρ φ m z → MR ρ ψ m _) ↔ ∀ z, MR ρ' φ m z → MR ρ' ψ m _
      constructor
      · intro hF z hz
        rw [← ihψ m _ fun y hy => h y (Or.inr hy)]
        exact hF z ((ihφ m z fun y hy => h y (Or.inl hy)).mpr hz)
      · intro hF z hz
        rw [ihψ m _ fun y hy => h y (Or.inr hy)]
        exact hF z ((ihφ m z fun y hy => h y (Or.inl hy)).mp hz)
  | all y φ ih =>
    intro ρ ρ' n x h
    cases n with
    | zero => rfl
    | succ m =>
      show (∀ k, MR (Function.update ρ y k) φ m _) ↔
        ∀ k, MR (Function.update ρ' y k) φ m _
      have hupd : ∀ k z, φ.FreeIn z →
          Function.update ρ y k z = Function.update ρ' y k z := by
        intro k z hz
        by_cases hzy : z = y
        · subst hzy; simp [Function.update]
        · simp only [Function.update, dif_neg hzy]
          exact h z ⟨hzy, hz⟩
      constructor
      · intro hF k
        exact (ih m _ (hupd k)).mp (hF k)
      · intro hF k
        exact (ih m _ (hupd k)).mpr (hF k)
  | ex y φ ih =>
    intro ρ ρ' n x h
    show MR (Function.update ρ y (fstPT x (defaultPT n))) φ n (sndPT x) ↔
      MR (Function.update ρ' y (fstPT x (defaultPT n))) φ n (sndPT x)
    refine ih n _ (fun z hz => ?_)
    by_cases hzy : z = y
    · subst hzy; simp [Function.update]
    · simp only [Function.update, dif_neg hzy]
      exact h z ⟨hzy, hz⟩

/-- **The substitution lemma**: realizing a substituted formula is
realizing the formula in the updated environment (no capture, per
`SubstOK`). -/
theorem MR_subst {x : ℕ} {u : Term} :
    ∀ (φ : Formula), Formula.SubstOK u φ → ∀ (ρ : ℕ → ℕ) (n : ℕ)
      (a : PureType (n + 1)),
      (MR ρ (φ.subst x u) n a ↔
        MR (Function.update ρ x (u.eval ρ)) φ n a) := by
  intro φ
  induction φ with
  | bot => intro _ ρ n a; rfl
  | eq s t =>
    intro _ ρ n a
    show (Term.subst x u s).eval ρ = (Term.subst x u t).eval ρ ↔ _
    rw [Term.eval_subst, Term.eval_subst]
    rfl
  | and φ ψ ihφ ihψ =>
    intro hok ρ n a
    have hφ : Formula.SubstOK u φ := fun y hy hb =>
      hok y hy (List.mem_append.mpr (Or.inl hb))
    have hψ : Formula.SubstOK u ψ := fun y hy hb =>
      hok y hy (List.mem_append.mpr (Or.inr hb))
    show MR ρ ((φ.subst x u).and (ψ.subst x u)) n a ↔ _
    show MR ρ (φ.subst x u) n _ ∧ MR ρ (ψ.subst x u) n _ ↔ _
    rw [ihφ hφ, ihψ hψ]
    rfl
  | or φ ψ ihφ ihψ =>
    intro hok ρ n a
    have hφ : Formula.SubstOK u φ := fun y hy hb =>
      hok y hy (List.mem_append.mpr (Or.inl hb))
    have hψ : Formula.SubstOK u ψ := fun y hy hb =>
      hok y hy (List.mem_append.mpr (Or.inr hb))
    show (_ ∧ MR ρ (φ.subst x u) n _) ∨ (_ ∧ MR ρ (ψ.subst x u) n _) ↔ _
    rw [ihφ hφ, ihψ hψ]
    rfl
  | imp φ ψ ihφ ihψ =>
    intro hok ρ n a
    have hφ : Formula.SubstOK u φ := fun y hy hb =>
      hok y hy (List.mem_append.mpr (Or.inl hb))
    have hψ : Formula.SubstOK u ψ := fun y hy hb =>
      hok y hy (List.mem_append.mpr (Or.inr hb))
    cases n with
    | zero => rfl
    | succ m =>
      show (∀ z, MR ρ (φ.subst x u) m z → MR ρ (ψ.subst x u) m _) ↔ _
      constructor
      · intro hF z hz
        rw [← ihψ hψ ρ m _]
        exact hF z ((ihφ hφ ρ m z).mpr hz)
      · intro hF z hz
        rw [ihψ hψ ρ m _]
        exact hF z ((ihφ hφ ρ m z).mp hz)
  | ex y φ ih =>
    intro hok ρ n a
    by_cases hyx : y = x
    · subst hyx
      rw [show Formula.subst y u (.ex y φ) = .ex y φ from by
        simp [Formula.subst]]
      show MR (Function.update ρ y _) φ n _ ↔
        MR (Function.update (Function.update ρ y (u.eval ρ)) y _) φ n _
      rw [Function.update_idem]
    · have hok' : Formula.SubstOK u φ := fun z hz hb =>
        hok z hz (List.mem_cons_of_mem _ hb)
      have hyu : y ∉ u.vars := fun hy =>
        hok y hy (List.mem_cons_self ..)
      rw [show Formula.subst x u (.ex y φ) = .ex y (φ.subst x u) from by
        simp [Formula.subst, hyx]]
      show MR (Function.update ρ y _) (φ.subst x u) n _ ↔
        MR (Function.update (Function.update ρ x (u.eval ρ)) y _) φ n _
      rw [ih hok' (Function.update ρ y (fstPT a (defaultPT n))) n (sndPT a)]
      have h1 : u.eval (Function.update ρ y (fstPT a (defaultPT n)))
          = u.eval ρ :=
        Term.eval_congr fun z hz => by
          have : z ≠ y := fun h => hyu (h ▸ hz)
          simp [Function.update, this]
      rw [h1, Function.update_comm (fun h => hyx h.symm)]
  | all y φ ih =>
    intro hok ρ n a
    by_cases hyx : y = x
    · subst hyx
      rw [show Formula.subst y u (.all y φ) = .all y φ from by
        simp [Formula.subst]]
      cases n with
      | zero => rfl
      | succ m =>
        show (∀ k, MR (Function.update ρ y k) φ m _) ↔
          ∀ k, MR (Function.update (Function.update ρ y (u.eval ρ)) y k) φ m _
        have hupd : ∀ k, Function.update (Function.update ρ y (u.eval ρ)) y k
            = Function.update ρ y k := fun k => Function.update_idem ..
        constructor
        · intro h k; rw [hupd k]; exact h k
        · intro h k; have := h k; rwa [hupd k] at this
    · have hok' : Formula.SubstOK u φ := fun z hz hb =>
        hok z hz (List.mem_cons_of_mem _ hb)
      have hyu : y ∉ u.vars := fun hy =>
        hok y hy (List.mem_cons_self ..)
      rw [show Formula.subst x u (.all y φ) = .all y (φ.subst x u) from by
        simp [Formula.subst, hyx]]
      cases n with
      | zero => rfl
      | succ m =>
        show (∀ k, MR (Function.update ρ y k) (φ.subst x u) m _) ↔
          ∀ k, MR (Function.update (Function.update ρ x (u.eval ρ)) y k) φ m _
        have key : ∀ k (b : PureType (m + 1)),
            MR (Function.update ρ y k) (φ.subst x u) m b ↔
            MR (Function.update (Function.update ρ x (u.eval ρ)) y k) φ m b := by
          intro k b
          rw [ih hok' (Function.update ρ y k) m b]
          have h1 : u.eval (Function.update ρ y k) = u.eval ρ :=
            Term.eval_congr fun z hz => by
              have : z ≠ y := fun h => hyu (h ▸ hz)
              simp [Function.update, this]
          rw [h1, Function.update_comm (fun h => hyx h.symm)]
        constructor
        · intro h k; exact (key k _).mp (h k)
        · intro h k; exact (key k _).mpr (h k)

end Realizability
