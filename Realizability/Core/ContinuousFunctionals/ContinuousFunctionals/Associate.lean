/-
# Associates (Kleene's neighborhood functions) for type-2 functionals

An associate makes the finite-information dependence of a type-2 functional
explicit: it is a single type-1 function on codes of finite sequences that
"searches" along the initial segments of its argument for the first stage at
which enough information has appeared, using the standard neighborhood-
function convention (`0` = "not enough information yet", `k + 1` =
"converged with value `k`").

This file contains the definition `IsAssociate` — the load-bearing
definition of the whole project — together with the *first-fire principle*
`IsAssociate.firstFire_eq`, the one lemma about the definition that
everything downstream (the equivalence with continuity in
`MainTheorem.lean`, and composition in `Composition.lean`) actually uses.
-/
import ContinuousFunctionals.Sequences

namespace ContinuousFunctionals

/-- **Kleene's associates, restricted to pure type 2.**  `IsAssociate a F`
says that the type-1 function `a : ℕ → ℕ` is an associate of the type-2
functional `F : (ℕ → ℕ) → ℕ`: along the chain of coded initial segments of
any `α`, the function `a` returns `0` ("not enough information yet") until,
at some finite stage `n`, it returns `F α + 1` ("converged, with value
`F α`").

Correspondence with the literature.  Kleene's partial application operation
on type-1 functions is `f | g ≃ f(ḡ(r)) − 1` where `r` is *least* with
`f(ḡ(r)) > 0`, and `f` is an associate of `F : ℕ^ℕ → ℕ` iff `f | g = F g`
for every `g`; unfolding `|` at the least `r` yields verbatim the statement
below (with `code (initSeg α n)` for `ḡ(r)` and the `+ 1` shift making
"value `F α`" and "converged" one condition).  See:

* S. C. Kleene, *Countable functionals*, in: Constructivity in Mathematics
  (1959) — the original definition;
* J. R. Longley, *Notions of computability at higher types I*, §3.3.1,
  Definition 3.13 (associates for the countable functionals; the
  application `f | g` is defined immediately before it) — the type-2 case
  of that definition is exactly this one;
* J. Longley and D. Normann, *Higher-Order Computability* (2015), Ch. 8
  (the total continuous functionals); D. Normann, *Recursion on the
  Countable Functionals* (1980) — the standard book treatments of the same
  notion.

The "least such stage" is phrased here as "nonzero at `n`, zero strictly
below `n`", which avoids a separate well-founded search each time the
witness is used. -/
def IsAssociate (a : ℕ → ℕ) (F : (ℕ → ℕ) → ℕ) : Prop :=
  ∀ α : ℕ → ℕ, ∃ n : ℕ,
    a (code (initSeg α n)) = F α + 1 ∧
    ∀ m < n, a (code (initSeg α m)) = 0

/-- Fire-data form of the first-fire principle: it needs only one known
first-fire of `a` along `γ` (at stage `p`, with value `v + 1`), not the
full associate property.  If `a` is also zero strictly below `n` and
nonzero at `n`, its value at `n` is forced to be the same `v + 1` — two
first-fires along one sequence collide by trichotomy, since each declares
zeros below itself. -/
theorem firstFire_eq_of_fire {a γ : ℕ → ℕ} {v p : ℕ}
    (hv : a (code (initSeg γ p)) = v + 1)
    (hz : ∀ m < p, a (code (initSeg γ m)) = 0)
    {n : ℕ} (hn : a (code (initSeg γ n)) ≠ 0)
    (hzn : ∀ m < n, a (code (initSeg γ m)) = 0) :
    a (code (initSeg γ n)) = v + 1 := by
  rcases lt_trichotomy n p with h | h | h
  · exact absurd (hz n h) hn
  · rw [h]
    exact hv
  · have h0 := hzn p h
    rw [hv] at h0
    exact absurd h0 (Nat.succ_ne_zero _)

/-- **The first-fire principle.**  If an associate of `F` is zero on all
initial segments of `α` shorter than `n` and nonzero on the segment of
length `n`, then its value there is forced: it must be `F α + 1`.  In other
words, the *first* nonzero value along the prefix chain of `α` is always the
correct one — there is no way to "fire early" with a wrong value, because
the definitional witness stage would then contradict either the zeros below
it or the zeros below `n`.

This is the only fact about `IsAssociate` the rest of the project needs:
the backward direction of the main theorem and the composition theorem are
both corollaries. -/
theorem IsAssociate.firstFire_eq {a : ℕ → ℕ} {F : (ℕ → ℕ) → ℕ}
    (ha : IsAssociate a F) {α : ℕ → ℕ} {n : ℕ}
    (hn : a (code (initSeg α n)) ≠ 0)
    (hz : ∀ m < n, a (code (initSeg α m)) = 0) :
    a (code (initSeg α n)) = F α + 1 := by
  obtain ⟨n₀, hv₀, hz₀⟩ := ha α
  exact firstFire_eq_of_fire hv₀ hz₀ hn hz

end ContinuousFunctionals
