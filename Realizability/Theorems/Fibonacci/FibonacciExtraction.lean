/-
# Fibonacci: the extracted function

`fibPairedTheorem` is a closed derivation of
`∀n. (∃y. fib n = y) ∧ (∃z. fib (n+1) = z)`; modified realizability turns
it into a program, because the realizer of the paired invariant carries
its two witnesses.  Reading the **first** existential's witness off — the
`(∃y. fib n = y)` component — gives `fibonacci : ℕ → ℕ`, and it is
certified three ways, exactly as Goodstein/Hanoi/gcd/Sperner are:

* `fibonacci_spec` — the extracted number really is the `n`-th Fibonacci
  value: `fibonacci n = fibN n`, for **every** `n`, from `soundness` (the
  realizer's witness clause *is* this equation), not by computation;
* `fib_extract_continuous` — the extract is `Continuous2`, by the generic
  theorem, no modification;
* `fibRealizesCtQ` — hence a class in `CtQ 2`.

`derivBound fibPairedTheorem = 5`, so the extract runs at its own certified
ambient — but its evaluation cost is **exponential in `n`** (≈ ×4 per step:
the step realizer forces the accumulated pair without sharing, the D4/D6
re-evaluation wall that memoization was measured not to fix, and the reason
Goodstein's `m = 4` and gcd are certified-not-run).  So the extract itself
is `#guard`ed only at the small `n` it reaches (0–3), and the headline
`fibonacci 10 = 55` is delivered as the **certified equation**
`fibonacci_ten` — `fibonacci_spec` rewrites it to the kernel-checked
`fibN 10 = 55` (`Signature/Fibonacci.lean`), so it is *proved*, not
evaluated.  The `#print axioms fibonacci` line confirms the extracted
function's own footprint is `[propext, Quot.sound]` — traced, not assumed
to transfer from the pipeline.
-/
import Realizability.Theorems.Fibonacci.FibonacciTheorem
import Realizability.Core.CollapseDemo

namespace Realizability

open ContinuousFunctionals

/-! **The statement, spelled out** — checked at every build so what is
proved cannot drift behind `fibBody`:
`⊢ ∀n. (∃y. fib n = y) ∧ (∃z. fib (n+1) = z)`. -/
#check (fibPairedTheorem :
  Deriv [] (Formula.all 0 (Formula.and
    (Formula.ex 3 (Formula.eq (Term.fib (Term.var 0)) (Term.var 3)))
    (Formula.ex 4 (Formula.eq (Term.fib (Term.succ (Term.var 0))) (Term.var 4))))))

/-- The bound above which the extracted family realizes the theorem. -/
theorem fib_derivBound : derivBound fibPairedTheorem = 5 := rfl

/-- **Soundness at the paired invariant**: the extracted family realizes
`∀n. (∃y. fib n = y) ∧ (∃z. fib (n+1) = z)` at every ambient from 5 up. -/
theorem fib_realized (ρ : ℕ → ℕ) {m : ℕ} (hm : 5 ≤ m) :
    MR ρ (.all 0 (fibBody (.var 0))) m (extract fibPairedTheorem ρ [] m) :=
  soundness fibPairedTheorem ρ [] trivial m (by rw [fib_derivBound]; exact hm)

/-- **The extracted Fibonacci function.**  Apply the realizer to `n`, take
the first component of the paired invariant (the `∃y. fib n = y`
conjunct), and read its witness — the first component at the canonical
point, where `exIC` puts it.  Ambient 5 is the derivation's own bound, so
this is the realizer at the level where it is certified. -/
def fibonacci (n : ℕ) : ℕ :=
  fstPT (fstPT (app₁ (extract fibPairedTheorem (fun _ => 0) [] 5) (natPT 5 n)))
    (defaultPT 4)

/-- **The extracted function is correct**, at every input: it computes the
`n`-th Fibonacci number.  This is soundness instantiated at the theorem —
the first existential's witness clause *is* `fib n = fibonacci n` — so it
needs no computation and holds far beyond where evaluation reaches. -/
theorem fibonacci_spec (n : ℕ) : fibonacci n = fibN n := by
  have h := fib_realized (fun _ => 0) (m := 5) (Nat.le_refl 5) n
  have h2 : Term.eval
      (Function.update (Function.update (fun _ => 0) 0 n) 3
        (fstPT (fstPT (app₁ (extract fibPairedTheorem (fun _ => 0) [] 5)
          (natPT 5 n))) (defaultPT 4)))
      (.fib (.var 0))
    = Term.eval
      (Function.update (Function.update (fun _ => 0) 0 n) 3
        (fstPT (fstPT (app₁ (extract fibPairedTheorem (fun _ => 0) [] 5)
          (natPT 5 n))) (defaultPT 4)))
      (.var 3) := h.1
  simpa [Term.eval, Function.update, fibonacci] using h2.symm

/-- **The extract carries the iterative loop's `(a, b)` state.**  The theorem
has *two* existentials; `fibonacci` reads the first (`fib n`), and `fibNext`
reads the second — the `sndPT` half of the `∧`-pair — which is `fib (n+1)`.
Together they are the exact pair the two-line iterative Fibonacci threads,
`(a, b) ↦ (b, a+b)`. -/
def fibNext (n : ℕ) : ℕ :=
  fstPT (sndPT (app₁ (extract fibPairedTheorem (fun _ => 0) [] 5) (natPT 5 n)))
    (defaultPT 4)

/-- `fibNext` is the *next* Fibonacci number, read from the second conjunct
of soundness — the mirror of `fibonacci_spec`. -/
theorem fibNext_spec (n : ℕ) : fibNext n = fibN (n + 1) := by
  have h := fib_realized (fun _ => 0) (m := 5) (Nat.le_refl 5) n
  have h2 : Term.eval
      (Function.update (Function.update (fun _ => 0) 0 n) 4
        (fstPT (sndPT (app₁ (extract fibPairedTheorem (fun _ => 0) [] 5)
          (natPT 5 n))) (defaultPT 4)))
      (.fib (.succ (.var 0)))
    = Term.eval
      (Function.update (Function.update (fun _ => 0) 0 n) 4
        (fstPT (sndPT (app₁ (extract fibPairedTheorem (fun _ => 0) [] 5)
          (natPT 5 n))) (defaultPT 4)))
      (.var 4) := h.2
  simpa [Term.eval, Function.update, fibNext] using h2.symm

/-- **The extraction made tangible.**  Reading *both* witnesses gives the
iterative loop's running state `(fib n, fib (n+1))` — the same pair a
programmer carries in two variables — tumbling out of a proof that never
mentions a loop.  Certified for every `n` from the two `_spec`s; the
`#guard` below runs it. -/
theorem fib_pair_spec (n : ℕ) :
    (fibonacci n, fibNext n) = (fibN n, fibN (n + 1)) := by
  rw [fibonacci_spec, fibNext_spec]

/-- Generic continuity applies to the theorem's extract with no
modification. -/
theorem fib_extract_continuous (ρ : ℕ → ℕ) :
    Continuous2 (extract fibPairedTheorem ρ [] 1) :=
  extract_continuous fibPairedTheorem ρ

/-- **The theorem's program, as an element of `CtQ 2`.** -/
noncomputable def fibRealizesCtQ (ρ : ℕ → ℕ) : CtQ 2 :=
  RealizesCtQ fibPairedTheorem ρ

/-- **`fibonacci 10 = 55`**, the headline value — *proved*, via
`fibonacci_spec`, so it needs no evaluation of the extract (whose cost at
`n = 10` is astronomical).  `rw` rewrites to `fibN 10 = 55`, closed by
`rfl` on the kernel-computable value function. -/
theorem fibonacci_ten : fibonacci 10 = 55 := by rw [fibonacci_spec]; rfl

/-- And `fibonacci 5 = 5`, likewise certified. -/
theorem fibonacci_five : fibonacci 5 = 5 := by rw [fibonacci_spec]; rfl

/-! ## Running it

This `#guard` **runs the extracted realizer** and reads *both* witnesses at
`n = 0…3`, checking the pair-state it carries against the iterative loop's:

    (0,1) → (1,1) → (1,2) → (2,3)

— a build-time self-check that the pipeline computes Fibonacci, not merely
that a proof exists.  It stops at `n = 3` because evaluation is exponential
(see the header); the larger values are the certified
`fibonacci_five`/`fibonacci_ten`. -/

#guard (List.range 4).map (fun k => (fibonacci k, fibNext k))
  == [(0, 1), (1, 1), (1, 2), (2, 3)]

#eval (List.range 4).map (fun k => (fibonacci k, fibNext k))

#print axioms fib_realized
#print axioms fibonacci_spec
#print axioms fibNext_spec
#print axioms fib_extract_continuous
#print axioms fibonacci

end Realizability
