/-
# The collapse payoff: two derivations, one program

`RealizesCtQ` sends a closed derivation to the class of its extracted
type-2 realizer in `CtQ 2` — the extensional collapse of the
Kleene–Kreisel development, reached through the capstone equivalence
`ctQTwoEquiv`.  "The program" a derivation denotes is this class, not
the raw extracted term.  It applies to **every** closed derivation
uniformly: the continuity obligation is discharged once and for all by
`extract_continuous` (`GenericContinuity.lean`), not by a
per-derivation certificate.

The named demo: two *different* derivations of commutativity of `∧`
under `→`,

* `demoDeriv₁ = impI (andI (andE₂ ax) (andE₁ ax))` — the direct swap;
* `demoDeriv₂ = impI (andE₁ (andI (andI (andE₂ ax) (andE₁ ax)) ax))` —
  the swap re-paired with the hypothesis and immediately projected;

whose extracted terms differ syntactically but compute the same
functional (`demo_extract_eq`, by the pairing retraction), hence have
the same class (`collapse_demo`).  The demo's continuity certificates
(`demo_extract_continuous`, `demo_extract_continuous₂`) are one-line
corollaries of the general theorem; the concrete value computation
(`demo_extract_apply`) is kept as the worked illustration of *why* the
functional is continuous: it reads its argument at position `0` and at
one further position determined by the answer.
-/
import ContinuousFunctionals.CtQ
import Realizability.Soundness
import Realizability.GenericContinuity

namespace Realizability

open ContinuousFunctionals

/-- **The `CtQ`-valued meaning of a closed derivation**: the class of
its extracted type-2 realizer in the extensional collapse, through the
capstone equivalence of the Kleene–Kreisel development.  Total on
closed derivations — continuity is supplied by `extract_continuous`. -/
noncomputable def RealizesCtQ {φ : Formula} (D : Deriv [] φ)
    (ρ : ℕ → ℕ) : CtQ 2 :=
  ctQTwoEquiv.symm ⟨extract D ρ [] 1, extract_continuous D ρ⟩

/-- The demo's atomic formulas (any atoms would do). -/
def demoA : Formula := .eq (.var 0) (.var 1)
def demoB : Formula := .eq (.var 2) (.var 3)

/-- The direct derivation of `A ∧ B → B ∧ A`. -/
def demoDeriv₁ : Deriv [] ((demoA.and demoB).imp (demoB.and demoA)) :=
  .impI (.andI (.andE₂ .ax) (.andE₁ .ax))

/-- A detour derivation of the same formula: swap, re-pair with the
hypothesis, project. -/
def demoDeriv₂ : Deriv [] ((demoA.and demoB).imp (demoB.and demoA)) :=
  .impI (.andE₁ (.andI (.andI (.andE₂ .ax) (.andE₁ .ax)) .ax))

/-- At the base of a family, `famOf` returns the generating realizer. -/
theorem famOf_self (φ : Formula) (x : PureType 1) :
    famOf φ (m := 0) x 0 = x := by
  unfold famOf
  rw [dif_pos (Nat.le_refl 0)]
  rfl

/-- **The two extracted terms compute the same family**: the detour's
extra pair-and-project cancels by the pairing retraction. -/
theorem demo_extract_eq (ρ : ℕ → ℕ) (env : List Fam) :
    extract demoDeriv₂ ρ env = extract demoDeriv₁ ρ env := by
  unfold demoDeriv₁ demoDeriv₂
  funext n
  cases n with
  | zero => rfl
  | succ m =>
    simp only [extract, impIC]
    congr 1
    funext x
    simp only [andE₁C, andIC]
    rw [fstPT_pairPT]

/-- The computed value of the shared extracted functional: read the
argument at `0`, decode a position from it, read there, and swap the
components. -/
theorem demo_extract_apply (ρ : ℕ → ℕ) (z : PureType 1) :
    extract demoDeriv₁ ρ [] 1 z =
      Nat.pair ((z ((z (0 : ℕ)).unpair.2)).unpair.1.unpair.2)
        ((z ((z (0 : ℕ)).unpair.2)).unpair.1.unpair.1) := by
  unfold demoDeriv₁
  simp only [extract, impIC, andIC, andE₁C, andE₂C, axC, List.headD]
  show (abs₁ fun x =>
    pairPT (sndPT (famOf (demoA.and demoB) x 0))
      (fstPT (famOf (demoA.and demoB) x 0))) z = _
  show pairPT (sndPT (famOf (demoA.and demoB) (fstPT z) 0))
      (fstPT (famOf (demoA.and demoB) (fstPT z) 0))
      (down 0 (sndPT z)) = _
  rw [famOf_self]
  rfl

/-- **Continuity of the shared extracted functional** — a one-line
corollary of the general theorem `extract_continuous`.  (The concrete
modulus is still visible in `demo_extract_apply`: the value at `α`
depends only on `α 0` and one further position computed from it.) -/
theorem demo_extract_continuous (ρ : ℕ → ℕ) :
    Continuous2 (extract demoDeriv₁ ρ [] 1) :=
  extract_continuous demoDeriv₁ ρ

/-- Continuity of the detour's extract — the same one-line corollary
(no appeal to the term equality `demo_extract_eq` needed). -/
theorem demo_extract_continuous₂ (ρ : ℕ → ℕ) :
    Continuous2 (extract demoDeriv₂ ρ [] 1) :=
  extract_continuous demoDeriv₂ ρ

/-- **The collapse demo** (the brief's named instance): the two
derivations denote the *same element of `CtQ 2`* — quotient equality of
the extensional collapse, applied directly to the two extracted
programs. -/
theorem collapse_demo (ρ : ℕ → ℕ) :
    RealizesCtQ demoDeriv₂ ρ = RealizesCtQ demoDeriv₁ ρ := by
  unfold RealizesCtQ
  apply congrArg ctQTwoEquiv.symm
  apply Subtype.ext
  exact congrFun (demo_extract_eq ρ []) 1

end Realizability
