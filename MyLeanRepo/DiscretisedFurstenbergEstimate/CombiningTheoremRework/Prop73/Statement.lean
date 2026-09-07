module

/-
  Prop73 Statement — Genuine Combining Induction

  Contains the core type abbreviations and helper lemmas for
  Proposition 7.3 (Combining Theorem) genuine induction.

  Key property: C and C' are λ-INDEPENDENT — existentially quantified
  outside the ∀ lam binder, depending only on n,s,τ,C_P.

  Whiteprint node: combining_theorem_genuine / statement
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FormatConversionLemmas
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.B1Integration
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DiscretisedFurstenbergEstimate.CombiningTheorem
open DiscretisedFurstenbergEstimate.DyadicConversion
open DirecretisedFurstenbergEstimate.FormatConversion.M2

/-- Genuine combining induction statement for n scale blocks.

    C and C' are existentially quantified OUTSIDE the lam binder,
    ensuring they depend only on n,s,τ,C_P (not on lam).
    δ₀ may depend on lam (absorbs "λ sufficiently small" condition). -/
abbrev CombiningInductionGenuine (s t τ ε_G η ε_N C_P : ℝ) (n : ℕ) : Prop :=
  ∃ (C C' : ℝ), 0 < C ∧ 0 < C' ∧
    ∀ (lam : ℝ), 0 < lam →
      ∃ (δ₀ : ℝ), 0 < δ₀ ∧
        ∀ (k : ℕ), dyadicDelta k ≤ δ₀ →
          ∀ (M : ℕ)
            (config : CTNiceConfiguration k s (Real.rpow (dyadicDelta k) (-lam)) M)
            (Δ : Fin (n + 1) → ℝ)
            (scaleClass : Fin n → ScaleClass)
            (N : Fin n → ℕ)
            (C_between : Fin n → ℝ),
            CombiningConfig s t τ n ε_G η lam ε_N C_P C_between k M config Δ scaleClass N →
            B1BridgeHypotheses k config →
            (config.T₀.card : ENNReal) ≥
              ENNReal.ofReal (combiningLowerBound (dyadicDelta k) (M : ℝ) C C' lam s ε_N η n Δ scaleClass)

/-! ### Helper lemmas -/

/-- Telescoping product over natural numbers with positive terms. -/
lemma prod_telescoping_nat {m : ℕ} {f : ℕ → ℝ} (hpos : ∀ k ≤ m, 0 < f k) :
    ∏ k ∈ Finset.range m, f (k + 1) / f k = f m / f 0 := by
  induction m with
  | zero =>
    have hf0 : 0 < f 0 := hpos 0 (by norm_num)
    simp [hf0.ne']
  | succ m ih =>
    have hpos' : ∀ k ≤ m, 0 < f k := fun k hk => hpos k (by omega)
    rw [Finset.prod_range_succ, ih hpos']
    have hfm : 0 < f m := hpos m (by omega)
    have hf0 : 0 < f 0 := hpos 0 (by omega)
    field_simp [hfm.ne', hf0.ne'] <;> ring

/-- Quotient of two dyadic scales is dyadic when numerator ≤ denominator. -/
lemma dyadic_quotient {x y : ℝ} (hx : x ∈ dyadicScales) (hy : y ∈ dyadicScales)
    (hxy : x ≤ y) (hx_pos : 0 < x) : x / y ∈ dyadicScales := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  have h1 : (2 : ℝ)^(-(a : ℤ)) ≤ (2 : ℝ)^(-(b : ℤ)) := hxy
  have h2 : a ≥ b := by
    by_contra h3
    have h4 : a < b := by omega
    have h5 : (2 : ℝ)^(-(a : ℤ)) > (2 : ℝ)^(-(b : ℤ)) := by
      have h6 : (-(a : ℤ)) > (-(b : ℤ)) := by omega
      have h7 : 1 < (2 : ℝ) := by norm_num
      exact zpow_lt_zpow_right₀ h7 h6
    linarith
  refine ⟨a - b, ?_⟩
  have h3 : (a : ℤ) - (b : ℤ) = ↑(a - b) := by
    simp [h2] <;> omega
  have h4 : (2 : ℝ)^(-(a : ℤ)) / (2 : ℝ)^(-(b : ℤ)) =
      (2 : ℝ)^(-((a - b : ℕ) : ℤ)) := by
    have h5 : (2 : ℝ)^(-(a : ℤ)) / (2 : ℝ)^(-(b : ℤ)) =
        (2 : ℝ)^(-(a : ℤ) - (-(b : ℤ))) := by
      rw [← zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
    rw [h5]
    have h6 : -(a : ℤ) - (-(b : ℤ)) = -((a - b : ℕ) : ℤ) := by
      have h7 : -(a : ℤ) - (-(b : ℤ)) = -((a : ℤ) - (b : ℤ)) := by ring
      rw [h7]
      have h8 : (a : ℤ) - (b : ℤ) = ↑(a - b) := by
        simp [h2] <;> omega
      rw [h8] <;> rfl
    rw [h6]
  exact h4

/-! ### Extra hypotheses structure -/

/-- Extra hypotheses needed by the genuine combining theorem but not present
    in CombiningConfig or B1BridgeHypotheses.

    These are supplied by the outer B1 bridge assembly / Appendix A chain. -/
structure CombiningExtraHypotheses
    (s t ε_G η ε_N C_P : ℝ) (n : ℕ) (lam : ℝ) (k M : ℕ)
    (config : CTNiceConfiguration k s (Real.rpow (dyadicDelta k) (-lam)) M)
    (Δ : Fin (n + 1) → ℝ) (scaleClass : Fin n → ScaleClass) : Prop where
  /-- Square set is an S-set at exponent s (needed by prop5). -/
  hP_set : IsFinsetDeltaSSet (dyadicDelta k) s C_P
      (finsetDyadicToDSquare config.P₀)
  /-- Slope bound for all tubes (derivable from B1BridgeHypotheses.h_tubes_strip). -/
  h_slope : ∀ T ∈ config.T₀, |T.slope| ≤ 1
  /-- For good scales, square set is also an S-set at exponent min(t_j,1). -/
  hP_set_tj : ∀ (j : Fin n) (t_j : ℝ),
    scaleClass j = ScaleClass.good t_j →
      IsFinsetDeltaSSet (dyadicDelta k) (min t_j 1) C_P
        (finsetDyadicToDSquare config.P₀)
  /-- t ≤ t_j for good scales (OS line 1012). -/
  h_tj_ge_t : ∀ (j : Fin n) (t_j : ℝ),
    scaleClass j = ScaleClass.good t_j → t ≤ t_j
  /-- Improved incidence bound for good scales (from Appendix A chain). -/
  h_improved_incidence : (config.T₀.card : ENNReal) ≥
      ENNReal.ofReal (Real.rpow (dyadicDelta k) (-(2 * s + ε_G)))
  /-- Exponent condition for good scale base case.
      Uses denominator min(t,1)-s because the good-base proof uses
      exponent u = min(t,1). -/
  h_exp_condition : (η + 2 * ε_G) * (1 - s) / (min t 1 - s) ≤ ε_G + lam + ε_N - η

/-- Genuine combining induction with explicit extra hypotheses.

    C,C' are lam-independent (existential outside ∀ lam binder).
    δ₀ may depend on lam.
    The extra hypotheses are supplied by the outer B1 bridge assembly. -/
abbrev CombiningInductionGenuine_with_data
    (s t τ ε_G η ε_N C_P : ℝ) (n : ℕ) : Prop :=
  ∃ (C C' : ℝ), 0 < C ∧ 0 < C' ∧
    ∀ (lam : ℝ), 0 < lam →
      ∃ (δ₀ : ℝ), 0 < δ₀ ∧
        ∀ (k : ℕ), dyadicDelta k ≤ δ₀ →
          ∀ (M : ℕ)
            (config : CTNiceConfiguration k s (Real.rpow (dyadicDelta k) (-lam)) M)
            (Δ : Fin (n + 1) → ℝ)
            (scaleClass : Fin n → ScaleClass)
            (N : Fin n → ℕ)
            (C_between : Fin n → ℝ),
            CombiningConfig s t τ n ε_G η lam ε_N C_P C_between k M config Δ scaleClass N →
            B1BridgeHypotheses k config →
            CombiningExtraHypotheses s t ε_G η ε_N C_P n lam k M config Δ scaleClass →
            (config.T₀.card : ENNReal) ≥
              ENNReal.ofReal (combiningLowerBound (dyadicDelta k) (M : ℝ) C C' lam s ε_N η n Δ scaleClass)

/-! ### Explicit C'(n,τ) constant -/

/-- Explicit C'(n,τ) constant from OS Proposition 7.3.

    Recurrence: C'(1,τ) = 2, C'(n+1,τ) = 2 + (2/τ)·C'(n,τ).
    Closed form: C'(n,τ) = 2·Σ_{i=0}^{n-1} (2/τ)^i.

    Depends only on n and τ, not on s, λ, ε_N, η, or C_P.
    Used to choose a uniform λ before calling the combining theorem. -/
def combiningCprime (n : ℕ) (τ : ℝ) : ℝ :=
  2 * ∑ i ∈ Finset.range n, (2 / τ) ^ i

lemma combiningCprime_pos {n : ℕ} {τ : ℝ} (hn : 0 < n) (hτ : 0 < τ) :
    0 < combiningCprime n τ := by
  have hne : (Finset.range n).Nonempty := by
    have h2 : 0 ∈ Finset.range n := by
      simp only [Finset.mem_range]
      <;> omega
    exact ⟨0, h2⟩
  have h1 : 0 < ∑ i ∈ Finset.range n, (2 / τ) ^ i :=
    Finset.sum_pos (fun i _ => by positivity) hne
  dsimp only [combiningCprime]
  positivity

lemma combiningCprime_monotone {m n : ℕ} {τ : ℝ} (h : m ≤ n) (hτ : 0 < τ) :
    combiningCprime m τ ≤ combiningCprime n τ := by
  have h1 : Finset.range m ⊆ Finset.range n := by
    intro x hx
    simp only [Finset.mem_range] at hx ⊢ <;> omega
  have h2 : ∑ i ∈ Finset.range m, (2 / τ) ^ i ≤ ∑ i ∈ Finset.range n, (2 / τ) ^ i := by
    apply Finset.sum_le_sum_of_subset_of_nonneg h1
    intro i _ _; positivity
  dsimp only [combiningCprime]
  gcongr

lemma combiningCprime_succ (n : ℕ) (τ : ℝ) (hτ : 0 < τ) :
    combiningCprime (n + 1) τ = 2 + (2 / τ) * combiningCprime n τ := by
  let r : ℝ := 2 / τ
  have h_ind : ∀ m : ℕ, ∑ i ∈ Finset.range (m + 1), r ^ i = 1 + r * ∑ i ∈ Finset.range m, r ^ i := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      calc
        ∑ i ∈ Finset.range (m + 2), r ^ i
          = (∑ i ∈ Finset.range (m + 1), r ^ i) + r ^ (m + 1) := by
            rw [Finset.sum_range_succ] <;> ring
        _ = (1 + r * ∑ i ∈ Finset.range m, r ^ i) + r ^ (m + 1) := by rw [ih]
        _ = 1 + r * ((∑ i ∈ Finset.range m, r ^ i) + r ^ m) := by
            simp [pow_succ] <;> ring
        _ = 1 + r * ∑ i ∈ Finset.range (m + 1), r ^ i := by
            have hsum2 : ∑ i ∈ Finset.range (m + 1), r ^ i =
                (∑ i ∈ Finset.range m, r ^ i) + r ^ m :=
              Finset.sum_range_succ (fun i => r ^ i) m
            rw [hsum2] <;> ring
  have h := h_ind n
  dsimp only [combiningCprime]
  rw [h]
  <;> ring

end DiscretisedFurstenbergEstimate.CombiningTheoremRework
