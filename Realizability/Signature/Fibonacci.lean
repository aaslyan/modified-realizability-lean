/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import Mathlib.Logic.Function.Basic

/-!
# Fibonacci value layer

The value-level function the `fib` symbol evaluates by.  Fibonacci is a
genuine recursively-defined value — the same category as the Hanoi
solver or the Pascal parity, and unlike order/divisibility it is not an
`∃`-definable relation over the existing signature — so it enters as its
own symbol, evaluated here by `fibN`.

The course-of-values snag (`fib (n+2)` needs *both* `fib (n+1)` and
`fib n`) is handled the same way at the value level as the fragment
handles it in `FibonacciTheorem.lean`: a **paired** recursion carrying
the two consecutive values.  `fibPair n = (fib n, fib (n+1))`, stepping
`(a, b) ↦ (b, a + b)`; this is *single* structural recursion on `n`, so
it reduces in the kernel (the concrete `#guard` below is by
computation), and it is choice-free — it feeds `Term.eval`, so it must
be, exactly like `goodN`/`hydraStepN`/`lookN`.

The step order `a + b = fib n + fib (n+1)` is chosen so that the
defining equation the fragment imports,

    fib (n+2) = fib n + fib (n+1)          (`Deriv.fibSucc`),

holds here by `rfl` — `fibN_succ_succ` below — matching the paired
invariant's step `(y, z) ↦ (z, y + z)` in the derivation.
-/

namespace Realizability

/-- `fibPair n = (fib n, fib (n+1))`, by single structural recursion on
`n` (so it reduces in the kernel).  The step keeps the two consecutive
values and shifts, which is the value-level image of the fragment's
paired invariant. -/
def fibPair : ℕ → ℕ × ℕ
  | 0 => (0, 1)
  | n + 1 => ((fibPair n).2, (fibPair n).1 + (fibPair n).2)

/-- The `n`-th Fibonacci number: the first component of `fibPair`. -/
def fibN (n : ℕ) : ℕ := (fibPair n).1

@[simp] theorem fibN_zero : fibN 0 = 0 := rfl

@[simp] theorem fibN_one : fibN 1 = 1 := rfl

/-- The recurrence, definitionally — this is exactly the equation
`Deriv.fibSucc` imports, and its `rfl` proof is what makes the
`fibSucc` soundness case `rfl`. -/
theorem fibN_succ_succ (n : ℕ) : fibN (n + 2) = fibN n + fibN (n + 1) := rfl

/-- Rows 0–10 of the sequence, kernel-checked: `fib 10 = 55`. -/
theorem fib_small :
    (fibN 0, fibN 1, fibN 2, fibN 3, fibN 4, fibN 5,
     fibN 6, fibN 7, fibN 8, fibN 9, fibN 10)
      = (0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55) := rfl

#guard fibN 10 = 55
#guard fibN 15 = 610

end Realizability
