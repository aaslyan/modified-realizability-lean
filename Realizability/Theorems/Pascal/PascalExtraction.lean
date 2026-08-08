/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import Realizability.Theorems.Pascal.PascalTheorem
import Realizability.Meta.ProgramExtraction
import Mathlib.Data.Nat.Choose.Basic

/-!
# Phase F4: the extracted Sierpiński decider

`pasTotal` is a closed derivation of

    ∀n ∀k. pas(n,k) = 1 ∨ pas(n,k) = 0

and its realizer, unlike Goodstein's or Hanoi's, carries no witness —
what it carries is the **tag of the disjunction**, which says *which*
side holds.  So the extract of this theorem is a genuine decision
function: `pasTag n k` is `0` when the fragment's proof took the left
branch (`pas(n,k) = 1`) and nonzero when it took the right.

`pasDecide_eq` proves, from `soundness`, that the tag decides correctly
at every `(n,k)`.  Drawn as a triangle, what the tags print is the
Sierpiński gasket — and there is no gap between the picture and the
theorem: every cell is one instance of the proved disjunction, resolved
by the extracted realizer itself.

## The reference computation

`Nat.choose` appears only in this module, only in `#guard`s, and never in
the fragment or in any proof: it is an *independent* reference against
which the extracted decider is cross-checked, exactly the role
`WilliamAngus/Goodstein` played for Phase B's Goodstein values.
-/

namespace Realizability

open ContinuousFunctionals

/-! **The statement, spelled out**, checked at every build. -/
#check (pasTotal :
  Deriv [] (Formula.all 1 (Formula.all 2
    ((Formula.eq (Term.pas (Term.var 1) (Term.var 2)) (Term.succ Term.zero)).or
      (Formula.eq (Term.pas (Term.var 1) (Term.var 2)) Term.zero)))))

/-- The bound above which the extract realizes the theorem. -/
theorem pas_derivBound : derivBound pasTotal = 8 := rfl

/-- **Soundness at the totality theorem.** -/
theorem pas_realized (ρ : ℕ → ℕ) {m : ℕ} (hm : 8 ≤ m) :
    MR ρ (.all 1 (.all 2 (pasBit (.var 1)))) m (extract pasTotal ρ [] m) :=
  soundness pasTotal ρ [] trivial m (by rw [pas_derivBound]; exact hm)

/-- **The extracted decider's tag.**  `0` means the derivation proved the
left disjunct, `pas(n,k) = 1`. -/
def pasTag (n k : ℕ) : ℕ :=
  tag₂ pasTotal 6 n k

/-- The decider, as a bit. -/
def pasDecide (n k : ℕ) : ℕ := if pasTag n k = 0 then 1 else 0

/-- **The extracted decider is correct**, at every `(n,k)`: its bit is
Pascal's triangle mod 2.  From `soundness` — the disjunction's tag is
sound by construction, which is exactly what makes the realizer a
decision procedure. -/
theorem pasDecide_eq (n k : ℕ) : pasDecide n k = pasN n k := by
  have h := pas_realized (fun _ ↦ 0) (m := 8) (Nat.le_refl 8) n k
  rcases h with ⟨htag, heq⟩ | ⟨htag, heq⟩
  · have h1 : pasTag n k = 0 := htag
    have h2 : pasN n k = 1 := by simpa [Term.eval, Function.update] using heq
    show (if pasTag n k = 0 then 1 else 0) = pasN n k
    rw [if_pos h1, h2]
  · have h1 : ¬ (pasTag n k = 0) := htag
    have h2 : pasN n k = 0 := by simpa [Term.eval, Function.update] using heq
    show (if pasTag n k = 0 then 1 else 0) = pasN n k
    rw [if_neg h1, h2]

/-- Generic continuity applies with no modification. -/
theorem pas_extract_continuous (ρ : ℕ → ℕ) :
    Continuous2 (extract pasTotal ρ [] 1) :=
  extract_continuous pasTotal ρ

/-- The decider's class in `CtQ 2`. -/
noncomputable def pasRealizesCtQ (ρ : ℕ → ℕ) : CtQ 2 :=
  RealizesCtQ pasTotal ρ

/-! ## What the fragment's own symbol computes

`pasFragment n k` evaluates the *term* `pas(n̂, k̂)` — the fragment's
decider as opposed to its realizer.  `pasDecide_eq` says the two agree
at every `(n,k)`, which matters below: the extracted realizer is far too
slow to draw a large triangle, but the theorem covers exactly the gap
that evaluation cannot. -/

/-- `pasN n k` computed through the fragment's `pas` symbol at numerals. -/
def pasFragment (n k : ℕ) : ℕ :=
  Term.eval (fun _ ↦ 0) (.pas (numeral n) (numeral k))

theorem pasFragment_eq (n k : ℕ) : pasFragment n k = pasN n k := by
  show pasN ((numeral n).eval (fun _ ↦ 0)) ((numeral k).eval (fun _ ↦ 0)) = _
  rw [numeral_eval, numeral_eval]

/-! ## Cross-checks against an independent reference

`Nat.choose` is Mathlib's binomial coefficient, used here and nowhere
else — not in the fragment, not in any proof.  The first block checks the
**extracted decider** (kept small: see the timings below); the second
checks the fragment's symbol over the whole triangle that gets recorded. -/

#guard (List.range 9).all fun n ↦
  (List.range (n + 1)).all fun k ↦ pasDecide n k == Nat.choose n k % 2

#guard (List.range 17).all fun n ↦
  (List.range (n + 1)).all fun k ↦ pasFragment n k == Nat.choose n k % 2

/-! A handful of named instances of the **extracted** decider, recorded
explicitly. -/

#guard pasDecide 4 2 == 0    -- C(4,2) = 6, even
#guard pasDecide 5 2 == 0    -- C(5,2) = 10, even
#guard pasDecide 6 3 == 0    -- C(6,3) = 20, even
#guard pasDecide 7 3 == 1    -- C(7,3) = 35, odd
#guard pasDecide 8 4 == 0    -- C(8,4) = 70, even

/-! And the same cells from the fragment's symbol, further out than the
realizer can be run. -/

#guard pasFragment 16 8 == 0    -- C(16,8) = 12870, even
#guard pasFragment 15 5 == 1    -- C(15,5) = 3003, odd
#guard pasFragment 20 4 == 1    -- C(20,4) = 4845, odd

/-! ## The triangle

Rows 0–7 are drawn by the **extracted realizer**; the recorded grid and
the larger picture come from the fragment's symbol, which
`pasDecide_eq` proves computes the same bits. -/

/-- One row of raw bits, from the extracted realizer. -/
def pasRowExtract (n : ℕ) : List ℕ := (List.range (n + 1)).map (pasDecide n)

/-- One row of raw bits, from the fragment's symbol. -/
def pasRow (n : ℕ) : List ℕ := (List.range (n + 1)).map (pasFragment n)

/-- One row, centred, for the picture. -/
def pasRowStr (rows n : ℕ) : String :=
  String.ofList (List.replicate (rows - n) ' ') ++
    String.intercalate " "
      ((List.range (n + 1)).map fun k ↦ if pasFragment n k = 1 then "#" else ".")

/-- The triangle, as a string. -/
def pasTriangle (rows : ℕ) : String :=
  String.intercalate "\n" ((List.range rows).map (pasRowStr rows))

/-! The first eight rows, straight from the extracted realizer. -/

#eval (List.range 8).map pasRowExtract

/-! The raw grid — this is what a visualization consumes. -/

#eval (List.range 16).map pasRow

/-! And the picture. -/

#eval IO.println (pasTriangle 16)

#print axioms pas_realized
#print axioms pasDecide_eq
#print axioms pas_extract_continuous

end Realizability
