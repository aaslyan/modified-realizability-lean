/-
# The countable functionals as honest quotient types

Packaging of the extensional collapse (`Collapse.lean`): the countable
functionals of pure type `n + 1` as the quotient `CtQ (n + 1)` of the
hereditarily total-extensional type-1 functions (`CtDom n`, the
self-related elements of `CtPer n`) by collapse-equivalence.  This is
`Ct = EC(K₂)` as an actual type, not a predicate on total Lean functions
(Longley–Normann 2015, Ch. 8; Longley, §3.3.1 and §5.1).

* `CtQ.app` — application `CtQ (n+2) → CtQ (n+1) → ℕ` descends from
  Kleene application: well-definedness on classes *is* the PER clause,
  i.e. exactly the associate-independence isolated at type 3.
  `CtQ.app_mk` computes it against the `Assoc` presentation.
* `ctQOneEquiv` — at level 1 the collapse is Baire space itself.
* `ctQTwoEquiv` — **the capstone**: the collapse at level 2 is precisely
  the continuous type-2 functionals, `CtQ 2 ≃ {F // Continuous2 F}`.
  A class is sent to the functional it computes (`ctQTwoToFun`),
  continuous by the main theorem; bijectivity says a collapse class is
  exactly the set of associates of one continuous functional
  (injectivity via `ctPer_one_iff`, surjectivity by choosing an
  associate via `hasAssociate_of_continuous`).

Off the countable fragment nothing is modeled at all here — the quotient
carries only the hereditarily total-extensional content, which is why no
"agreement on `Ct` only" caveats appear in this file.
-/
import ContinuousFunctionals.Collapse

namespace ContinuousFunctionals

/-- The hereditarily total-extensional type-1 functions at level `n`:
the domain of the collapse PER. -/
def CtDom (n : ℕ) : Type :=
  {b : ℕ → ℕ // CtPer n b b}

instance ctSetoid (n : ℕ) : Setoid (CtDom n) where
  r b b' := CtPer n b.1 b'.1
  iseqv := ⟨fun b => b.2, fun h => CtPer.symm h, fun h1 h2 => CtPer.trans h1 h2⟩

/-- **The countable functionals of pure type `n`**, as a quotient type:
numbers at type 0, and at type `n + 1` the collapse classes of level-`n`
hereditarily total-extensional elements.  `CtQ 1 ≃ ℕ → ℕ`
(`ctQOneEquiv`) and `CtQ 2 ≃` the continuous functionals
(`ctQTwoEquiv`). -/
def CtQ : ℕ → Type
  | 0 => ℕ
  | n + 1 => Quotient (ctSetoid n)

/-- **Application descends to the quotient**: `CtQ (n+2) → CtQ (n+1) → ℕ`
induced by Kleene application.  Well-definedness on classes is literally
the PER clause. -/
noncomputable def CtQ.app {n : ℕ} : CtQ (n + 2) → CtQ (n + 1) → ℕ :=
  Quotient.lift₂ (fun b g : _ => kleeneApply b.1 g.1)
    (fun _ g _ g' hb hg => (hb g.1 g'.1 hg).2.2)

/-- `CtQ.app` computes the `Assoc` presentation: on the classes of an
associate of `Φ` and an associate of `x`, the descended application
returns `Φ x`. -/
theorem CtQ.app_mk {n : ℕ} {Φ : PureType (n + 2)} {x : PureType (n + 1)}
    {b g : ℕ → ℕ} (hb : Assoc (n + 1) b Φ) (hg : Assoc n g x) :
    CtQ.app (Quotient.mk (ctSetoid (n + 1)) ⟨b, hb.ctPer_self⟩)
      (Quotient.mk (ctSetoid n) ⟨g, hg.ctPer_self⟩) = Φ x := by
  obtain ⟨k, hv, hz⟩ := hb x g hg
  exact kleeneApply_eq_of_fire hv hz

/-- At level 1 the collapse is Baire space itself: the PER is equality,
so classes are points. -/
def ctQOneEquiv : CtQ 1 ≃ (ℕ → ℕ) where
  toFun := Quotient.lift (fun b : CtDom 0 => b.1) (fun _ _ h => h)
  invFun g := Quotient.mk (ctSetoid 0) ⟨g, rfl⟩
  left_inv := by
    intro q
    induction q using Quotient.ind with
    | _ b => exact Quotient.sound rfl
  right_inv g := rfl

/-- A self-related element computes a functional: `α ↦ b | α` is
witnessed by `b` itself. -/
theorem isAssociate_kleeneApply_self {b : ℕ → ℕ} (hb : CtPer 1 b b) :
    IsAssociate b (fun α => kleeneApply b α) :=
  isAssociate_iff_kleeneApply.mpr fun α => ⟨(hb α α rfl).1, rfl⟩

/-- The functional computed by a level-2 collapse class: `α ↦ b | α`,
continuous by the main theorem. -/
noncomputable def ctQTwoToFun : CtQ 2 → {F : (ℕ → ℕ) → ℕ // Continuous2 F} :=
  Quotient.lift
    (fun b : CtDom 1 =>
      (⟨fun α => kleeneApply b.1 α,
        continuous_of_hasAssociate (isAssociate_kleeneApply_self b.2)⟩ :
        {F : (ℕ → ℕ) → ℕ // Continuous2 F}))
    (fun _ _ h => Subtype.ext (funext fun α => (h α α rfl).2.2))

/-- `ctQTwoToFun` is a bijection: a collapse class is exactly the set of
associates of the one continuous functional it computes. -/
theorem ctQTwoToFun_bijective : Function.Bijective ctQTwoToFun := by
  constructor
  · intro q q' himg
    induction q using Quotient.ind with
    | _ b =>
      induction q' using Quotient.ind with
      | _ b' =>
        apply Quotient.sound
        have hfun : (fun α => kleeneApply b.1 α) = fun α => kleeneApply b'.1 α :=
          congrArg Subtype.val himg
        refine ctPer_one_iff.mpr ⟨fun α => kleeneApply b.1 α,
          isAssociate_kleeneApply_self b.2, ?_⟩
        rw [hfun]
        exact isAssociate_kleeneApply_self b'.2
  · intro F
    refine ⟨Quotient.mk (ctSetoid 1)
      ⟨(hasAssociate_of_continuous F.2).choose,
        Assoc.ctPer_self (n := 1)
          (assoc_one_iff.mpr (hasAssociate_of_continuous F.2).choose_spec)⟩, ?_⟩
    apply Subtype.ext
    funext α
    show kleeneApply (hasAssociate_of_continuous F.2).choose α = F.1 α
    exact ((hasAssociate_of_continuous F.2).choose_spec).kleeneApply_eq α

/-- **The capstone: the collapse at level 2 is the continuous type-2
functionals.**  The quotient construction (`Ct = EC(K₂)`) and the
associate characterization of continuity (`continuous_iff_hasAssociate`)
present the same mathematical objects. -/
noncomputable def ctQTwoEquiv : CtQ 2 ≃ {F : (ℕ → ℕ) → ℕ // Continuous2 F} :=
  Equiv.ofBijective ctQTwoToFun ctQTwoToFun_bijective

end ContinuousFunctionals
