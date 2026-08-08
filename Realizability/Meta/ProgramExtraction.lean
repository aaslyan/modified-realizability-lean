/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import Realizability.Core.CollapseDemo

/-!
# Program-extraction API for common theorem shapes

This module is deliberately small.  The uniform extraction theorem in this
repository is:

*input*: a derivation object `D : Deriv [] φ` in the object fragment;
*output*: the extracted family `extract D`, its soundness certificate, and for
closed type-2 extracts its `CtQ 2` class.

It is **not** a compiler from arbitrary Lean theorems to programs.  Lean
theorems about ordinary Lean propositions must first be represented as
object-language formulas and proved as `Deriv` trees.  Once that is done, the
functions below factor the repeated "apply the realizer to numerals and read
the witness/tag" boilerplate used by the case-study extraction files.

The caller supplies the ambient `bound`; in the certified examples this is
usually `derivBound D`, recorded as a theorem such as `goodstein_derivBound`.
Each universal quantifier consumes one ambient level.
-/

namespace Realizability

open ContinuousFunctionals

/-! ## The uniform core -/

/-- The raw extracted family of a closed derivation at the zero environment. -/
def extractedFamily {φ : Formula} (D : Deriv [] φ) : Fam :=
  extract D (fun _ ↦ 0) []

/-- The raw extracted realizer of a closed derivation at ambient `n`. -/
def extractedAt {φ : Formula} (D : Deriv [] φ) (n : ℕ) : PureType (n + 1) :=
  extractedFamily D n

/-- The `CtQ 2` program denoted by a closed derivation.  This is the
proof-independent continuous-functional meaning, when the theorem is read at
type 2. -/
noncomputable def extractedCtQ {φ : Formula} (D : Deriv [] φ)
    (ρ : ℕ → ℕ := fun _ ↦ 0) : CtQ 2 :=
  RealizesCtQ D ρ

/-! ## Applying universal quantifiers -/

/-- Apply the extracted realizer of a `∀` theorem to one numeral.

The parameter `m` is the ambient level *after* the application.  The theorem
itself is evaluated one level higher, at `m + 1`. -/
def apply₁ {x : ℕ} {φ : Formula}
    (D : Deriv [] (.all x φ)) (m a : ℕ) : PureType (m + 1) :=
  app₁ (extractedAt D (m + 1)) (natPT (m + 1) a)

/-- Apply the extracted realizer of a `∀∀` theorem to two numerals.

The parameter `m` is the ambient level after both applications. -/
def apply₂ {x y : ℕ} {φ : Formula}
    (D : Deriv [] (.all x (.all y φ))) (m a b : ℕ) : PureType (m + 1) :=
  app₁ (app₁ (extractedAt D (m + 2)) (natPT (m + 2) a))
    (natPT (m + 1) b)

/-- Apply the extracted realizer of a `∀∀∀` theorem to three numerals.

The parameter `m` is the ambient level after all three applications. -/
def apply₃ {x y z : ℕ} {φ : Formula}
    (D : Deriv [] (.all x (.all y (.all z φ)))) (m a b c : ℕ) :
    PureType (m + 1) :=
  app₁ (app₁ (app₁ (extractedAt D (m + 3)) (natPT (m + 3) a))
      (natPT (m + 2) b))
    (natPT (m + 1) c)

/-- Apply the extracted realizer of a `∀∀∀∀` theorem to four numerals.

The parameter `m` is the ambient level after all four applications. -/
def apply₄ {w x y z : ℕ} {φ : Formula}
    (D : Deriv [] (.all w (.all x (.all y (.all z φ))))) (m a b c d : ℕ) :
    PureType (m + 1) :=
  app₁ (app₁ (app₁ (app₁ (extractedAt D (m + 4)) (natPT (m + 4) a))
        (natPT (m + 3) b))
      (natPT (m + 2) c))
    (natPT (m + 1) d)

/-! ASCII aliases for paper snippets and terminal use. -/

def apply1 {x : ℕ} {φ : Formula}
    (D : Deriv [] (.all x φ)) (m a : ℕ) : PureType (m + 1) :=
  apply₁ D m a

def apply2 {x y : ℕ} {φ : Formula}
    (D : Deriv [] (.all x (.all y φ))) (m a b : ℕ) : PureType (m + 1) :=
  apply₂ D m a b

def apply3 {x y z : ℕ} {φ : Formula}
    (D : Deriv [] (.all x (.all y (.all z φ)))) (m a b c : ℕ) :
    PureType (m + 1) :=
  apply₃ D m a b c

def apply4 {w x y z : ℕ} {φ : Formula}
    (D : Deriv [] (.all w (.all x (.all y (.all z φ))))) (m a b c d : ℕ) :
    PureType (m + 1) :=
  apply₄ D m a b c d

/-! ## Reading computational content -/

/-- Read the witness from a theorem of shape `∀x. ∃y. φ`. -/
def witness₁ {x y : ℕ} {φ : Formula}
    (D : Deriv [] (.all x (.ex y φ))) (m a : ℕ) : ℕ :=
  fstPT (apply₁ D m a) (defaultPT m)

/-- Read the witness from a theorem of shape `∀x. ∀y. ∃z. φ`. -/
def witness₂ {x y z : ℕ} {φ : Formula}
    (D : Deriv [] (.all x (.all y (.ex z φ)))) (m a b : ℕ) : ℕ :=
  fstPT (apply₂ D m a b) (defaultPT m)

/-- Read the witness from a theorem of shape `∀w. ∀x. ∀y. ∃z. φ`. -/
def witness₃ {w x y z : ℕ} {φ : Formula}
    (D : Deriv [] (.all w (.all x (.all y (.ex z φ))))) (m a b c : ℕ) : ℕ :=
  fstPT (apply₃ D m a b c) (defaultPT m)

/-- Read the witness from a theorem of shape `∀v. ∀w. ∀x. ∀y. ∃z. φ`. -/
def witness₄ {v w x y z : ℕ} {φ : Formula}
    (D : Deriv [] (.all v (.all w (.all x (.all y (.ex z φ)))))) (m a b c d : ℕ) :
    ℕ :=
  fstPT (apply₄ D m a b c d) (defaultPT m)

/-- Read the disjunction tag from a theorem of shape `∀x. ∀y. φ ∨ ψ`.
By convention `0` means the left branch and `1` means the right branch. -/
def tag₂ {x y : ℕ} {φ ψ : Formula}
    (D : Deriv [] (.all x (.all y (.or φ ψ)))) (m a b : ℕ) : ℕ :=
  fstPT (apply₂ D m a b) (defaultPT m)

def witness1 {x y : ℕ} {φ : Formula}
    (D : Deriv [] (.all x (.ex y φ))) (m a : ℕ) : ℕ :=
  witness₁ D m a

def witness2 {x y z : ℕ} {φ : Formula}
    (D : Deriv [] (.all x (.all y (.ex z φ)))) (m a b : ℕ) : ℕ :=
  witness₂ D m a b

def witness3 {w x y z : ℕ} {φ : Formula}
    (D : Deriv [] (.all w (.all x (.all y (.ex z φ))))) (m a b c : ℕ) : ℕ :=
  witness₃ D m a b c

def witness4 {v w x y z : ℕ} {φ : Formula}
    (D : Deriv [] (.all v (.all w (.all x (.all y (.ex z φ)))))) (m a b c d : ℕ) :
    ℕ :=
  witness₄ D m a b c d

def tag2 {x y : ℕ} {φ ψ : Formula}
    (D : Deriv [] (.all x (.all y (.or φ ψ)))) (m a b : ℕ) : ℕ :=
  tag₂ D m a b

#print axioms extractedFamily
#print axioms extractedAt
#print axioms witness₁
#print axioms witness₄
#print axioms tag₂
#print axioms witness1
#print axioms tag2

end Realizability
