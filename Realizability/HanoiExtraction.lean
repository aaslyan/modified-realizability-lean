/-
# Phase E4: the extracted Hanoi solver

`hanoiTheorem` is a closed derivation of

    ∀n ∀f ∀t ∀v. ∃k. Solves(n,f,t,v,k) ∧ MoveCount k = 2^n − 1

so modified realizability turns it into a program: the realizer of the
existential carries its witness, and the witness *is the solution* — the
actual move sequence, not merely a proof that one exists.

Three certifications, as in every prior extraction phase, plus the
decoded artifact the visualization needs.
-/
import Realizability.HanoiTheorem
import Realizability.CollapseDemo

namespace Realizability

open ContinuousFunctionals

/-! **The statement, spelled out** — checked at every build so that what
is proved cannot drift behind a definition. -/
#check (hanoiTheorem :
  Deriv [] (Formula.all 1 (Formula.all 2 (Formula.all 3 (Formula.all 4
    (Formula.ex 5
      ((Formula.eq (Term.solves (Term.var 1) (Term.var 2) (Term.var 3)
          (Term.var 4) (Term.var 5)) (Term.succ Term.zero)).and
        (Formula.eq (Term.mvcount (Term.var 5))
          (Term.pred (Term.exp twoT (Term.var 1)))))))))))

/-- The bound above which the extracted family realizes the theorem. -/
theorem hanoi_derivBound : derivBound hanoiTheorem = 26 := rfl

/-- **Soundness at the Hanoi theorem.** -/
theorem hanoi_realized (ρ : ℕ → ℕ) {m : ℕ} (hm : 26 ≤ m) :
    MR ρ (.all 1 (.all 2 (.all 3 (.all 4 (.ex 5 hanoiBodyPred))))) m
      (extract hanoiTheorem ρ [] m) :=
  soundness hanoiTheorem ρ [] trivial m (by rw [hanoi_derivBound]; exact hm)

/-- **The extracted solver.**  Apply the realizer to the disk count and
the three pegs, then read the witness component of the existential.
Ambient 26 is the derivation's own bound, so this is the realizer at the
level where it is certified. -/
def hanoiSolution (n f t v : ℕ) : ℕ :=
  fstPT (app₁ (app₁ (app₁ (app₁ (extract hanoiTheorem (fun _ => 0) [] 26)
    (natPT 26 n)) (natPT 25 f)) (natPT 24 t)) (natPT 23 v)) (defaultPT 22)

/-! ## Reading the solution back

A move is `src * 3 + dst`, so decoding is division and remainder; the
sequence is the cons coding of `Hanoi.lean`.  This is the artifact a
visualization consumes. -/

/-- Decode an encoded move sequence into readable `(src, dst)` pairs. -/
def decodeMoves : ℕ → ℕ → List (ℕ × ℕ)
  | 0, _ => []
  | fuel + 1, k =>
      if k = 0 then []
      else (hhead k / 3, hhead k % 3) :: decodeMoves fuel (htail k)

/-- The extracted solution, decoded. -/
def hanoiMoves (n : ℕ) : List (ℕ × ℕ) :=
  decodeMoves (n + 32) (hanoiSolution n 0 2 1)

/-! ## The solutions, run and decoded

Peg `0` is the source, `2` the target, `1` the spare. -/

#eval hanoiMoves 1
#eval hanoiMoves 2
#eval hanoiMoves 3
#eval hanoiMoves 4

/-! And the move counts are `2^n − 1`, read off the extracted witness
itself rather than from the theorem. -/

#guard (hanoiMoves 0).length == 0
#guard (hanoiMoves 1).length == 1
#guard (hanoiMoves 2).length == 3
#guard (hanoiMoves 3).length == 7
#guard (hanoiMoves 4).length == 15

/-! The extracted witness is the same sequence the value-level solver
produces — so the derivation's program and `Hanoi.lean`'s function agree,
which is not something soundness by itself says. -/

#guard hanoiSolution 0 0 2 1 == hanoiN 0 0 2 1
#guard hanoiSolution 1 0 2 1 == hanoiN 1 0 2 1
#guard hanoiSolution 2 0 2 1 == hanoiN 2 0 2 1
#guard hanoiSolution 3 0 2 1 == hanoiN 3 0 2 1
#guard hanoiSolution 4 0 2 1 == hanoiN 4 0 2 1

/-- **The extracted solver is correct and optimal**, at every disk count
and every arrangement of pegs: the sequence it returns is a valid
solution, and its length is exactly `2^n − 1`.  From `soundness`, not
from computation, so it holds far beyond where evaluation reaches. -/
theorem hanoiSolution_spec (n f t v : ℕ) :
    solvesN n f t v (hanoiSolution n f t v) = 1
    ∧ hlen (hanoiSolution n f t v) = 2 ^ n - 1 := by
  have h := hanoi_realized (fun _ => 0) (m := 26) (Nat.le_refl 26)
  have h4 := h n f t v
  obtain ⟨h1, h2⟩ := h4
  constructor
  · simpa [Term.eval, Function.update, hanoiSolution] using h1
  · simpa [Term.eval, Function.update, hanoiSolution] using h2

/-- Generic continuity applies with no modification. -/
theorem hanoi_extract_continuous (ρ : ℕ → ℕ) :
    Continuous2 (extract hanoiTheorem ρ [] 1) :=
  extract_continuous hanoiTheorem ρ

/-- The theorem's program as an element of `CtQ 2`. -/
noncomputable def hanoiRealizesCtQ (ρ : ℕ → ℕ) : CtQ 2 :=
  RealizesCtQ hanoiTheorem ρ

#print axioms hanoi_realized
#print axioms hanoiSolution_spec
#print axioms hanoi_extract_continuous

end Realizability
