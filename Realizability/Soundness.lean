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

end Realizability
