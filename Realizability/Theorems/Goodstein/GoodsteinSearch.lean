/-
Copyright (c) 2026 Ara Aslyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ara Aslyan
-/
import Realizability.Theorems.Goodstein.GoodsteinExtraction

/-!
# One function, two programs: search versus ordinal descent

The Goodstein stopping time `m ↦ s` (the first step at which `goodN m` reaches
`0`) can be computed two ways, and the contrast between them is the point of
this module.

**By minimization (a `while` loop / the μ-operator).** Compute the sequence,
test for zero, return the first hit:

    stopBySearch m = μ s. (goodN m s = 0).

This is the natural program, and it is easy. But it is `partial`: Lean's kernel
*refuses to certify that it terminates*, because nothing in the definition
bounds the search. Its totality is precisely Goodstein's theorem, and the
`partial` keyword is exactly that missing certificate, sitting in the source.
If Goodstein's theorem were false — if some sequence never reached `0` — this
loop would silently run forever, and the definition could not tell you which.

**By ordinal descent (the extracted realizer).** `goodsteinStopTime`
(`GoodsteinExtraction`) is extracted from the proof, which recurses along the
ordinals below `ε₀`. It is a *total* `def` — no `partial` — because its
termination is carried by the well-foundedness of `≺`, intrinsically, however
astronomically large the intermediate values become. The proof is the program;
the program halts by construction.

**Making the dependency machine-checked.** The gap is visible in one keyword,
but we can make it a *proof*. `Nat.find` — Lean's constructive minimization —
is total only when handed an existence proof `∃ s, goodN m s = 0`. The only
such proof available is `goodReachesZero`, which *is* the extracted
ordinal-descent theorem (`goodsteinStopTime_spec`). So `minStop` below is the
same μ-search as `stopBySearch`, but total — and it is total *because it
literally consumes Goodstein's theorem* as its termination argument. The
dependency "search halts ⟺ the theorem holds" is no longer prose; it is the
type of `Nat.find`.

At runtime the existence proof is erased, so `minStop` *evaluates* by the cheap
`goodN` search (not by the expensive ambient-12 realizer): the theorem is spent
at type-checking time to license totality, and the computation is the fast loop.
Consequently `minStop 4` is as unreachable as the real sequence
(`4, 26, 41, 60, …`), exactly like the naive loop — the certificate buys
termination, not speed.

This is a demonstration, not part of the certified extraction pipeline:
`stopBySearch` is deliberately `partial`, and `minStop` is metatheory that
inherits `Classical.choice` through `soundness` (its `#print axioms` is checked
below and is *not* the extracted-program budget). Nothing here changes any
extracted realizer or its axioms.

## Reference

The contrast is the classical one between *unbounded ( μ-) recursion*, whose
termination is a separate theorem, and *structural / well-founded recursion*,
whose termination is intrinsic. Independence of Goodstein's theorem from Peano
arithmetic is **not** used and **not** claimed here — the contrast needs only
"an unbounded search halts iff a zero exists," which is elementary.
-/

namespace Realizability

open Realizability

/-! ## Program 1 — minimization (the naive `while` loop) -/

/-- The Goodstein stopping time by **unbounded search**: the least `s` with
`goodN m s = 0`. Lean requires `partial`: there is no termination proof for the
search other than Goodstein's theorem itself, so the kernel does not certify
that this returns. The `partial` keyword is that missing certificate. -/
partial def stopBySearch (m : ℕ) : ℕ :=
  let rec go (s : ℕ) : ℕ := if goodN m s = 0 then s else go (s + 1)
  go 0

/-! ## Program 2 — the same minimization, made total by the theorem -/

/-- **The existence proof is the extracted ordinal-descent theorem.**
`goodsteinStopTime m` is a step at which the sequence is `0`
(`goodsteinStopTime_spec`), so a zero exists. This lemma is the *only* reason
the minimization below is total. -/
def goodReachesZero (m : ℕ) : ∃ s, goodN m s = 0 :=
  ⟨goodsteinStopTime m, goodsteinStopTime_spec m⟩

/-- The Goodstein stopping time by **constructive minimization**, `Nat.find` —
the same μ-search as `stopBySearch`, but a *total* `def`. It type-checks only
because `goodReachesZero` (the extracted theorem) supplies the termination
argument that `stopBySearch` lacks: the μ-operator here literally consumes
Goodstein's theorem. -/
def minStop (m : ℕ) : ℕ := Nat.find (goodReachesZero m)

/-- `minStop` returns a genuine stop: the sequence really is `0` there. -/
theorem goodN_minStop (m : ℕ) : goodN m (minStop m) = 0 :=
  Nat.find_spec (goodReachesZero m)

/-- The certified minimum never exceeds the extracted witness: the least stop
time is at most the one the ordinal-descent program returns (`Nat.find` gives
the least `s`, and `goodsteinStopTime m` is one such `s`). -/
theorem minStop_le (m : ℕ) : minStop m ≤ goodsteinStopTime m :=
  Nat.find_min' (goodReachesZero m) (goodsteinStopTime_spec m)

/-! ## The two programs agree, where evaluation reaches -/

-- `minStop` evaluates by the fast search (the erased proof does not run):
-- the published stopping times `0, 1, 3, 5` for `m = 0, 1, 2, 3`.
#guard [minStop 0, minStop 1, minStop 2, minStop 3] == [0, 1, 3, 5]
-- the naive `partial` loop computes the identical column …
#guard [stopBySearch 0, stopBySearch 1, stopBySearch 2, stopBySearch 3] == [0, 1, 3, 5]
-- … and both agree with the ordinal-descent extract where it evaluates (m = 0, 1;
-- past that the extract hits the ambient-12 wall, and `m = 4`'s stop time is
-- astronomically large for either search — the certificate buys termination,
-- not speed).
#guard [goodsteinStopTime 0, goodsteinStopTime 1] == [minStop 0, minStop 1]

-- Transparency: `minStop` is metatheory, inheriting `Classical.choice` through
-- `soundness` (via `goodsteinStopTime_spec`). This is *not* the extracted-program
-- axiom budget — the extracted realizers stay `[propext, Quot.sound]`; `minStop`
-- merely reasons *about* one. Reported as `[propext, Classical.choice, Quot.sound]`.
#print axioms minStop

end Realizability
