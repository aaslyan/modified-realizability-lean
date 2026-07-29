/-
# Soundness: every derivation extracts a realizer

The main theorem of the milestone's logical half: for every derivation
`D : Deriv Γ φ`, environment `ρ`, and context assignment `env` realizing
`Γ` (`CtxR`), the extracted family realizes `φ` at every ambient level
above `derivBound D`.  Proof by induction on the derivation; each case
invokes the corresponding named combinator's behavior, with the
transports supplying hypothesis families at binders (`FR_famOf`), the
substitution lemma at `∀`-elimination, and environment congruence at
`∀`-introduction.
-/
import Realizability.Extraction

namespace Realizability

open ContinuousFunctionals

/-- Context realization is stable under environment changes away from
the context's free variables. -/
theorem CtxR_congr {ρ ρ' : ℕ → ℕ} :
    ∀ (Γ : List Formula) (env : List Fam),
      (∀ ψ ∈ Γ, ∀ z, ψ.FreeIn z → ρ z = ρ' z) →
      CtxR ρ Γ env → CtxR ρ' Γ env := by
  intro Γ
  induction Γ with
  | nil => intro env _ _; trivial
  | cons ψ Γ ih =>
    intro env h hc
    refine ⟨?_, ih env.tail (fun χ hχ => h χ (List.mem_cons_of_mem _ hχ)) hc.2⟩
    intro n hn
    exact (MR_congr ψ n _ (h ψ (List.mem_cons_self ..))).mp (hc.1 n hn)

/-- **Closure of `MR` under primitive recursion, uniformly in the
ambient level** — the new theorem of the induction extension: the
pure-type counterpart of the recursor's realizing clause in the
soundness of modified realizability for induction (Troelstra 1973; see
STATUS.md for the exact citation).  Stated once for every ambient `m`,
per the level-free-core discipline; no level-by-level instances exist.

This is the **"small" induction**: ordinary natural-number induction on
the numeral `k` being realized, at a fixed ambient `m`, strictly nested
inside the "big" induction over `Deriv` that `soundness` performs
(which invokes this lemma exactly once, in its `ind` case).  The
iteration never changes ambient level: `MR`'s `→` clause consumes and
produces realizers at the same level, so the step realizer `b` —
consumed through the `∀` clause at ambient `m + 2` and the `→` clause
at `m + 1` — sends ambient-`m` realizers of `φ(k)` to ambient-`m`
realizers of `φ(succ k)`.  The substitution lemma converts between
`φ(0)` / `φ(succ x)` under `ρ` and `φ` under the updated environment at
both ends of each step. -/
theorem MR_indRecC {ρ : ℕ → ℕ} {x : ℕ} {φ : Formula}
    (hok : Formula.SubstOK (.succ (.var x)) φ) {m : ℕ}
    {a : PureType (m + 1)} {b : PureType (m + 3)}
    (ha : MR ρ (φ.subst x .zero) m a)
    (hb : MR ρ (.all x (φ.imp (φ.subst x (.succ (.var x))))) (m + 2) b) :
    ∀ k : ℕ, MR (Function.update ρ x k) φ m (indRecC a b k) := by
  intro k
  -- The small induction: on the numeral, at the fixed ambient `m`.
  induction k with
  | zero =>
    have h0 : Formula.SubstOK Term.zero φ := fun y hy => by
      simp [Term.vars] at hy
    exact (MR_subst φ h0 ρ m a).mp ha
  | succ k ih =>
    -- One step: the `∀` clause of `hb` at the numeral `k`, then the
    -- `→` clause at the induction hypothesis.
    have hstep := hb k (indRecC a b k) ih
    have hconv := (MR_subst φ hok (Function.update ρ x k) m _).mp hstep
    have heval : Term.eval (Function.update ρ x k) (.succ (.var x))
        = k + 1 := by
      show Function.update ρ x k x + 1 = k + 1
      simp [Function.update]
    rw [heval, Function.update_idem] at hconv
    exact hconv

/-- **Soundness of extraction** for the fragment: derivable formulas are
realized by their extracted families, above the derivation's bound. -/
theorem soundness {Γ : List Formula} {φ : Formula} (D : Deriv Γ φ) :
    ∀ (ρ : ℕ → ℕ) (env : List Fam), CtxR ρ Γ env →
      ∀ n, derivBound D ≤ n → MR ρ φ n (extract D ρ env n) := by
  induction D with
  | ax =>
    intro ρ env henv n hn
    exact henv.1 n hn
  | wk D ih =>
    intro ρ env henv n hn
    exact ih ρ env.tail henv.2 n hn
  | @andI Γ φ ψ D₁ D₂ ih₁ ih₂ =>
    intro ρ env henv n hn
    have hb : max (derivBound D₁) (derivBound D₂) ≤ n := hn
    refine ⟨?_, ?_⟩
    · show MR ρ φ n (fstPT (pairPT (extract D₁ ρ env n) (extract D₂ ρ env n)))
      rw [fstPT_pairPT]
      exact ih₁ ρ env henv n (by omega)
    · show MR ρ ψ n (sndPT (pairPT (extract D₁ ρ env n) (extract D₂ ρ env n)))
      rw [sndPT_pairPT]
      exact ih₂ ρ env henv n (by omega)
  | andE₁ D ih =>
    intro ρ env henv n hn
    exact (ih ρ env henv n hn).1
  | andE₂ D ih =>
    intro ρ env henv n hn
    exact (ih ρ env henv n hn).2
  | @orI₁ Γ φ ψ D ih =>
    intro ρ env henv n hn
    left
    refine ⟨?_, ?_⟩
    · show fstPT (pairPT (fun _ => (0 : ℕ)) (extract D ρ env n))
        (defaultPT n) = 0
      rw [fstPT_pairPT]
    · show MR ρ φ n (sndPT (pairPT (fun _ => (0 : ℕ)) (extract D ρ env n)))
      rw [sndPT_pairPT]
      exact ih ρ env henv n hn
  | @orI₂ Γ φ ψ D ih =>
    intro ρ env henv n hn
    right
    refine ⟨?_, ?_⟩
    · show fstPT (pairPT (fun _ => (1 : ℕ)) (extract D ρ env n))
        (defaultPT n) ≠ 0
      rw [fstPT_pairPT]
      exact one_ne_zero
    · show MR ρ ψ n (sndPT (pairPT (fun _ => (1 : ℕ)) (extract D ρ env n)))
      rw [sndPT_pairPT]
      exact ih ρ env henv n hn
  | @orE Γ φ ψ χ D D₁ D₂ ih ih₁ ih₂ =>
    intro ρ env henv n hn
    have hb : max (max (derivBound D) (max (lvl φ) (lvl ψ)))
        (max (derivBound D₁) (derivBound D₂)) ≤ n := hn
    have hmaj := ih ρ env henv n (by omega)
    show MR ρ χ n
      (if fstPT (extract D ρ env n) (defaultPT n) = 0 then
        extract D₁ ρ (famOf φ (sndPT (extract D ρ env n)) :: env) n
      else
        extract D₂ ρ (famOf ψ (sndPT (extract D ρ env n)) :: env) n)
    by_cases htag : fstPT (extract D ρ env n) (defaultPT n) = 0
    · rw [if_pos htag]
      rcases hmaj with ⟨-, hp⟩ | ⟨hne, -⟩
      · exact ih₁ ρ (famOf φ (sndPT (extract D ρ env n)) :: env)
          ⟨FR_famOf φ ρ (by omega) _ hp, henv⟩ n (by omega)
      · exact absurd htag hne
    · rw [if_neg htag]
      rcases hmaj with ⟨heq, -⟩ | ⟨-, hp⟩
      · exact absurd heq htag
      · exact ih₂ ρ (famOf ψ (sndPT (extract D ρ env n)) :: env)
          ⟨FR_famOf ψ ρ (by omega) _ hp, henv⟩ n (by omega)
  | @impI Γ φ ψ D ih =>
    intro ρ env henv n hn
    have hb : max (derivBound D) (lvl φ) + 1 ≤ n := hn
    cases n with
    | zero => omega
    | succ m =>
      intro x hx
      show MR ρ ψ m
        (app₁ (abs₁ fun z => extract D ρ (famOf φ z :: env) m) x)
      rw [app₁_abs₁]
      exact ih ρ (famOf φ x :: env)
        ⟨FR_famOf φ ρ (by omega) x hx, henv⟩ m (by omega)
  | impE D₁ D₂ ih₁ ih₂ =>
    intro ρ env henv n hn
    have hb : max (derivBound D₁) (derivBound D₂) ≤ n := hn
    exact ih₁ ρ env henv (n + 1) (by omega) _ (ih₂ ρ env henv n (by omega))
  | botE D ih =>
    intro ρ env henv n hn
    exact (ih ρ env henv n hn).elim
  | @allI Γ y φ D hfresh ih =>
    intro ρ env henv n hn
    have hb : derivBound D + 1 ≤ n := hn
    cases n with
    | zero => omega
    | succ m =>
      intro k
      show MR (Function.update ρ y k) φ m
        (app₁ (abs₁ fun z =>
          extract D (Function.update ρ y (z (defaultPT m))) env m)
          (natPT (m + 1) k))
      rw [app₁_abs₁]
      show MR (Function.update ρ y k) φ m
        (extract D (Function.update ρ y (natPT (m + 1) k (defaultPT m)))
          env m)
      rw [show natPT (m + 1) k (defaultPT m) = k from rfl]
      refine ih (Function.update ρ y k) env
        (CtxR_congr Γ env (fun ψ hψ z hz => ?_) henv) m (by omega)
      by_cases hzy : z = y
      · exact absurd (hzy ▸ hz) (hfresh ψ hψ)
      · simp [Function.update, hzy]
  | @allE Γ y φ u D hok ih =>
    intro ρ env henv n hn
    rw [MR_subst φ hok ρ n _]
    exact ih ρ env henv (n + 1) (by
      have hb : derivBound D ≤ n := hn
      omega) (u.eval ρ)
  | @ind Γ x φ D₁ D₂ hok ih₁ ih₂ =>
    -- The "big"-induction case: unfold the `allIC` packaging, then hand
    -- everything to the "small" induction `MR_indRecC`, instantiated at
    -- the premises' extracted families (base at ambient `m`, step at
    -- ambient `m + 2`).
    intro ρ env henv n hn
    have hb : max (derivBound D₁) (derivBound D₂) + 1 ≤ n := hn
    cases n with
    | zero => omega
    | succ m =>
      intro k
      show MR (Function.update ρ x k) φ m
        (app₁ (abs₁ fun z =>
          indRecC (extract D₁ ρ env m) (extract D₂ ρ env (m + 2))
            (z (defaultPT m)))
          (natPT (m + 1) k))
      rw [app₁_abs₁]
      show MR (Function.update ρ x k) φ m
        (indRecC (extract D₁ ρ env m) (extract D₂ ρ env (m + 2))
          (natPT (m + 1) k (defaultPT m)))
      rw [show natPT (m + 1) k (defaultPT m) = k from rfl]
      exact MR_indRecC hok (ih₁ ρ env henv m (by omega))
        (ih₂ ρ env henv (m + 2) (by omega)) k
  | eqDec s t =>
    intro ρ env henv n hn
    have hb : (1 : ℕ) ≤ n := hn
    cases n with
    | zero => omega
    | succ m =>
      cases hdec : decide (s.eval ρ = t.eval ρ) with
      | true =>
        have heq : Term.eval ρ s = Term.eval ρ t := of_decide_eq_true hdec
        show MR ρ _ (m + 1) (eqDecC (decide (s.eval ρ = t.eval ρ)) (m + 1))
        rw [hdec]
        left
        refine ⟨?_, heq⟩
        show fstPT (pairPT (fun _ => (0 : ℕ)) (defaultPT (m + 2)))
          (defaultPT (m + 1)) = 0
        rw [fstPT_pairPT]
      | false =>
        have hne : ¬ (Term.eval ρ s = Term.eval ρ t) :=
          of_decide_eq_false hdec
        show MR ρ _ (m + 1) (eqDecC (decide (s.eval ρ = t.eval ρ)) (m + 1))
        rw [hdec]
        right
        refine ⟨?_, ?_⟩
        · show fstPT (pairPT (fun _ => (1 : ℕ)) (defaultPT (m + 2)))
            (defaultPT (m + 1)) ≠ 0
          rw [fstPT_pairPT]
          exact one_ne_zero
        · intro x hx
          exact absurd (hx : Term.eval ρ s = Term.eval ρ t) hne
  | succNeZero s =>
    intro ρ env henv n hn
    have hb : (1 : ℕ) ≤ n := hn
    cases n with
    | zero => omega
    | succ m =>
      intro x hx
      exact absurd hx (Nat.succ_ne_zero _)
  | succInj s t =>
    intro ρ env henv n hn
    have hb : (1 : ℕ) ≤ n := hn
    cases n with
    | zero => omega
    | succ m =>
      intro x hx
      show (Term.eval ρ s) = (Term.eval ρ t)
      have hx' : Term.eval ρ s + 1 = Term.eval ρ t + 1 := hx
      omega
  -- Phase A: the equational-logic kit — atomic conclusions carry no
  -- content, so each case is the equation's truth from its premises'.
  | eqRefl t =>
    intro ρ env henv n hn
    show Term.eval ρ t = Term.eval ρ t
    rfl
  | eqSymm s t =>
    intro ρ env henv n hn
    have hb : (1 : ℕ) ≤ n := hn
    cases n with
    | zero => omega
    | succ m =>
      intro x hx
      show Term.eval ρ t = Term.eval ρ s
      exact (hx : Term.eval ρ s = Term.eval ρ t).symm
  | eqTrans s t u =>
    intro ρ env henv n hn
    have hb : (2 : ℕ) ≤ n := hn
    cases n with
    | zero => omega
    | succ m =>
      cases m with
      | zero => omega
      | succ m' =>
        intro x hx y hy
        show Term.eval ρ s = Term.eval ρ u
        exact (hx : Term.eval ρ s = Term.eval ρ t).trans
          (hy : Term.eval ρ t = Term.eval ρ u)
  | eqCongSucc s t =>
    intro ρ env henv n hn
    have hb : (1 : ℕ) ≤ n := hn
    cases n with
    | zero => omega
    | succ m =>
      intro x hx
      show Term.eval ρ s + 1 = Term.eval ρ t + 1
      have hx' : Term.eval ρ s = Term.eval ρ t := hx
      omega
  | eqCongPlus s₁ t₁ s₂ t₂ =>
    intro ρ env henv n hn
    have hb : (2 : ℕ) ≤ n := hn
    cases n with
    | zero => omega
    | succ m =>
      cases m with
      | zero => omega
      | succ m' =>
        intro x hx y hy
        show Term.eval ρ s₁ + Term.eval ρ s₂
          = Term.eval ρ t₁ + Term.eval ρ t₂
        rw [(hx : Term.eval ρ s₁ = Term.eval ρ t₁),
          (hy : Term.eval ρ s₂ = Term.eval ρ t₂)]
  | eqCongTimes s₁ t₁ s₂ t₂ =>
    intro ρ env henv n hn
    have hb : (2 : ℕ) ≤ n := hn
    cases n with
    | zero => omega
    | succ m =>
      cases m with
      | zero => omega
      | succ m' =>
        intro x hx y hy
        show Term.eval ρ s₁ * Term.eval ρ s₂
          = Term.eval ρ t₁ * Term.eval ρ t₂
        rw [(hx : Term.eval ρ s₁ = Term.eval ρ t₁),
          (hy : Term.eval ρ s₂ = Term.eval ρ t₂)]
  -- Phase A: the first-argument recursion equations, true in `ℕ`.
  | zeroPlus t =>
    intro ρ env henv n hn
    show 0 + Term.eval ρ t = Term.eval ρ t
    omega
  | succPlus s t =>
    intro ρ env henv n hn
    show Term.eval ρ s + 1 + Term.eval ρ t = Term.eval ρ s + Term.eval ρ t + 1
    omega
  | zeroTimes t =>
    intro ρ env henv n hn
    show 0 * Term.eval ρ t = 0
    exact Nat.zero_mul _
  | succTimes s t =>
    intro ρ env henv n hn
    show (Term.eval ρ s + 1) * Term.eval ρ t
      = Term.eval ρ s * Term.eval ρ t + Term.eval ρ t
    exact Nat.succ_mul _ _
  -- Phase B: the recursion equations for `pred`/`exp`, true in `ℕ` …
  | predZero =>
    intro ρ env henv n hn
    show 0 - 1 = 0
    rfl
  | predSucc s =>
    intro ρ env henv n hn
    show Term.eval ρ s + 1 - 1 = Term.eval ρ s
    omega
  | expZero s =>
    intro ρ env henv n hn
    show Term.eval ρ s ^ 0 = 0 + 1
    exact Nat.pow_zero _
  | expSucc s t =>
    intro ρ env henv n hn
    show Term.eval ρ s ^ (Term.eval ρ t + 1)
      = Term.eval ρ s ^ Term.eval ρ t * Term.eval ρ s
    exact Nat.pow_succ ..
  -- … the two `bump` axioms (absorption at zero is the fueled
  -- function's base case; the numeral graph is its own graph) …
  | bumpZero s =>
    intro ρ env henv n hn
    show bumpN (Term.eval ρ s) 0 = 0
    rfl
  | bumpNum k n' =>
    intro ρ env henv n hn
    show bumpN ((numeral k).eval ρ) ((numeral n').eval ρ)
      = (numeral (bumpN k n')).eval ρ
    rw [numeral_eval, numeral_eval, numeral_eval]
  -- … the Goodstein recursion, which is `goodN`'s own definition …
  | goodZero s =>
    intro ρ env henv n hn
    show goodN (Term.eval ρ s) 0 = Term.eval ρ s
    rfl
  | goodSucc s t =>
    intro ρ env henv n hn
    show goodN (Term.eval ρ s) (Term.eval ρ t + 1)
      = bumpN (Term.eval ρ t + 1 + 1) (goodN (Term.eval ρ s) (Term.eval ρ t)) - 1
    rfl
  -- … and the congruence schemas.
  | eqCongPred s t =>
    intro ρ env henv n hn
    have hb : (1 : ℕ) ≤ n := hn
    cases n with
    | zero => omega
    | succ m =>
      intro x hx
      show Term.eval ρ s - 1 = Term.eval ρ t - 1
      rw [(hx : Term.eval ρ s = Term.eval ρ t)]
  | eqCongExp s₁ t₁ s₂ t₂ =>
    intro ρ env henv n hn
    have hb : (2 : ℕ) ≤ n := hn
    cases n with
    | zero => omega
    | succ m =>
      cases m with
      | zero => omega
      | succ m' =>
        intro x hx y hy
        show Term.eval ρ s₁ ^ Term.eval ρ s₂
          = Term.eval ρ t₁ ^ Term.eval ρ t₂
        rw [(hx : Term.eval ρ s₁ = Term.eval ρ t₁),
          (hy : Term.eval ρ s₂ = Term.eval ρ t₂)]
  | eqCongBump s₁ t₁ s₂ t₂ =>
    intro ρ env henv n hn
    have hb : (2 : ℕ) ≤ n := hn
    cases n with
    | zero => omega
    | succ m =>
      cases m with
      | zero => omega
      | succ m' =>
        intro x hx y hy
        show bumpN (Term.eval ρ s₁) (Term.eval ρ s₂)
          = bumpN (Term.eval ρ t₁) (Term.eval ρ t₂)
        rw [(hx : Term.eval ρ s₁ = Term.eval ρ t₁),
          (hy : Term.eval ρ s₂ = Term.eval ρ t₂)]
  | eqCongGood s₁ t₁ s₂ t₂ =>
    intro ρ env henv n hn
    have hb : (2 : ℕ) ≤ n := hn
    cases n with
    | zero => omega
    | succ m =>
      cases m with
      | zero => omega
      | succ m' =>
        intro x hx y hy
        show goodN (Term.eval ρ s₁) (Term.eval ρ s₂)
          = goodN (Term.eval ρ t₁) (Term.eval ρ t₂)
        rw [(hx : Term.eval ρ s₁ = Term.eval ρ t₁),
          (hy : Term.eval ρ s₂ = Term.eval ρ t₂)]

end Realizability
