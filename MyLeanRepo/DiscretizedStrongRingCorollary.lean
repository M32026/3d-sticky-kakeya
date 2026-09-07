module

/-
# Discretized Strong Ring Corollary

Bridges the application-facing covering-number interface to the corrected
Strong Ring theorem's Lebesgue-volume interface.

Given application exponent `s_app`, choose `σ = (1 + s_app)/2 > s_app` and
convert:
- `K·δ^{-ε_app}` delta-set constant → `δ^{-ε_strong}`
- `K·δ^{-(s_app+ε_app)}` covering bound → `δ^{-σ}`
- `volume(A) ≤ δ·Nδ(A) ≤ K·δ^{1-s_app-ε_app} ≤ δ^{1-σ}`
-/

public import MyLeanRepo.StrongRingTheoremCorrected
public import MyLeanRepo.CoveringMeasureTranslation
public import MyLeanRepo.OSWPrelude

@[expose] public section

open MeasureTheory ENNReal Set Classical BigOperators
open scoped BigOperators Pointwise

namespace WeakTwoEndsSumProduct

/-- Monotonicity of `IsRealDeltaSet` in the constant parameter: if `C1 ≤ C2`,
    then a `(δ, s, C1)`-set is also a `(δ, s, C2)`-set. -/
lemma IsRealDeltaSet.mono_const' {δ s C1 C2 : ℝ} {A : Set ℝ}
    (h : IsRealDeltaSet δ s C1 A) (hC : C1 ≤ C2) :
    IsRealDeltaSet δ s C2 A := by
  dsimp only [IsRealDeltaSet, IsDeltaSCSet] at h ⊢
  rcases h with ⟨h_bdd, h_nonempty, h_d, h_dyadic, hδ_pos, hs_nonneg, hs_le, hC1_pos, h_main⟩
  have hC2_pos : 0 < C2 := by linarith
  refine ⟨h_bdd, h_nonempty, h_d, h_dyadic, hδ_pos, hs_nonneg, hs_le, hC2_pos, ?_⟩
  intro r Q hr hQ hδr hr1
  have h10 := h_main hr hQ hδr hr1
  have h11 : ENNReal.ofReal C1 ≤ ENNReal.ofReal C2 := ENNReal.ofReal_le_ofReal hC
  calc ENat.toENNReal (dyadicCoveringNumber (d := 1) δ (realLineCopy A ∩ Q))
    ≤ ENNReal.ofReal C1 * ENat.toENNReal (dyadicCoveringNumber (d := 1) δ (realLineCopy A)) * ENNReal.ofReal (r ^ s) := h10
    _ ≤ ENNReal.ofReal C2 * ENat.toENNReal (dyadicCoveringNumber (d := 1) δ (realLineCopy A)) * ENNReal.ofReal (r ^ s) := by
      gcongr
      <;> exact h11

/-- **Discretized Strong Ring Corollary**.

    Application-facing interface: accepts a `(δ, κ, K·δ^{-ε_app})`-set A with
    covering number `Nδ(A) ≤ K·δ^{-(s_app+ε_app)}`, and produces the Ring
    expansion using `strong_ring_theorem_corrected` at exponent
    `σ = (1 + s_app)/2 > s_app`. -/
theorem discretized_strong_ring_corollary
    (s_app κ : ℝ) (hs_app_pos : 0 < s_app) (hs_app_lt_one : s_app < 1)
    (hκ_pos : 0 < κ) (hκ_le_s_app : κ ≤ s_app) :
    ∃ (c ε_app : ℝ), 0 < c ∧ 0 < ε_app ∧
      ∀ (K C₀ : ℝ), 1 ≤ K → 0 < C₀ → C₀ ≤ (2 : ℝ) ^ κ →
        ∃ (δ₀ : ℝ), 0 < δ₀ ∧
          ∀ {δ : ℝ}, δ ∈ dyadicScales → 0 < δ → δ ≤ δ₀ →
            ∀ (A : Set ℝ) (μ : Measure ℝ) (t : ℝ),
              A ⊆ Set.Icc 1 2 →
              IsRealDeltaSet δ κ (K * δ ^ (-ε_app)) A →
              Nreal δ A ≤ ENNReal.ofReal (K * δ ^ (-(s_app + ε_app))) →
              IsAllScaleFrostman κ C₀ μ →
              μ.support ⊆ Set.Icc 0 1 →
              δ ^ c ≤ t → t ≤ 1 →
              ∃ x ∈ μ.support,
                ENNReal.ofReal (δ ^ (-c)) * Nreal δ (scaleSet t⁻¹ A) ≤
                  Nreal δ (Set.image2 (fun a b => a + x * b) (scaleSet t⁻¹ A) A) := by
  let σ : ℝ := (1 + s_app) / 2
  have hσ_pos : 0 < σ := by dsimp only [σ]; linarith
  have hσ_lt_one : σ < 1 := by dsimp only [σ]; linarith
  have hκ_le_σ : κ ≤ σ := by dsimp only [σ]; linarith [hκ_le_s_app]
  have hσ_gt_s_app : s_app < σ := by dsimp only [σ]; linarith
  have hσ_minus_s_app_pos : 0 < σ - s_app := by dsimp only [σ]; linarith
  have h1_minus_σ_pos : 0 < 1 - σ := by dsimp only [σ]; linarith
  -- Obtain strong theorem constants at exponent σ
  rcases strong_ring_theorem_corrected σ κ hσ_pos hσ_lt_one hκ_pos hκ_le_σ with
    ⟨c_strong, ε_strong, hc_strong_pos, hε_strong_pos, h_main⟩
  -- Choose ε_app strictly smaller than all relevant gaps
  let gap : ℝ := min (min ε_strong (σ - s_app)) (1 - σ) / 2
  have hgap_pos : 0 < gap := by
    dsimp only [gap]
    have h1 : 0 < ε_strong := hε_strong_pos
    have h2 : 0 < σ - s_app := hσ_minus_s_app_pos
    have h3 : 0 < 1 - σ := h1_minus_σ_pos
    positivity
  let ε_app : ℝ := gap
  have hε_app_pos : 0 < ε_app := hgap_pos
  have hε_app_lt_ε_strong : ε_app < ε_strong := by
    dsimp only [ε_app, gap]
    have h : min (min ε_strong (σ - s_app)) (1 - σ) ≤ ε_strong := by
      exact le_trans (min_le_left _ _) (min_le_left _ _)
    linarith
  have hε_app_lt_gap1 : ε_app < σ - s_app := by
    dsimp only [ε_app, gap]
    have h : min (min ε_strong (σ - s_app)) (1 - σ) ≤ σ - s_app := by
      exact le_trans (min_le_left _ _) (min_le_right _ _)
    linarith
  have hε_app_lt_gap2 : ε_app < 1 - σ := by
    dsimp only [ε_app, gap]
    have h : min (min ε_strong (σ - s_app)) (1 - σ) ≤ 1 - σ := min_le_right _ _
    linarith
  refine ⟨c_strong, ε_app, hc_strong_pos, hε_app_pos, ?_⟩
  intro K C₀ hK_one hC₀_pos hC₀_le
  rcases h_main C₀ hC₀_pos hC₀_le with ⟨δ₀_strong, hδ₀_strong_pos, h_strong⟩
  -- Choose δ₀ small enough for both conversions
  let exp1 : ℝ := ε_strong - ε_app
  let exp2 : ℝ := σ - s_app - ε_app
  have hexp1_pos : 0 < exp1 := by linarith
  have hexp2_pos : 0 < exp2 := by linarith
  let δ₀_K : ℝ := K ^ (-(1 / exp1))
  let δ₀_K2 : ℝ := K ^ (-(1 / exp2))
  let δ₀ : ℝ := min δ₀_strong (min δ₀_K δ₀_K2)
  have hδ₀_pos : 0 < δ₀ := by positivity
  refine ⟨δ₀, hδ₀_pos, ?_⟩
  intro δ hδ_dyadic hδ_pos hδle A μ t hA_sub hA_delta hN_bound hFrost hμ_supp htc ht_le_one
  have hδ_le_δ₀K : δ ≤ δ₀_K := by
    have h1 : δ ≤ δ₀ := hδle
    have h2 : δ₀ ≤ min δ₀_K δ₀_K2 := min_le_right _ _
    have h3 : min δ₀_K δ₀_K2 ≤ δ₀_K := min_le_left _ _
    exact le_trans (le_trans h1 h2) h3
  have hδ_le_δ₀K2 : δ ≤ δ₀_K2 := by
    have h1 : δ ≤ δ₀ := hδle
    have h2 : δ₀ ≤ min δ₀_K δ₀_K2 := min_le_right _ _
    have h3 : min δ₀_K δ₀_K2 ≤ δ₀_K2 := min_le_right _ _
    exact le_trans (le_trans h1 h2) h3
  have hδ_le_strong : δ ≤ δ₀_strong := by
    have h1 : δ ≤ δ₀ := hδle
    have h2 : δ₀ ≤ δ₀_strong := min_le_left _ _
    exact le_trans h1 h2
  have hK_pos : 0 < K := by linarith
  -- Conversion 1: K·δ^{-ε_app} ≤ δ^{-ε_strong}
  have hK_leδ_neg_exp1 : K ≤ δ ^ (-exp1) := by
    have h1 : δ ≤ K ^ (-(1 / exp1)) := hδ_le_δ₀K
    have h2 : δ ^ exp1 ≤ K ^ (-1 : ℝ) := by
      calc δ ^ exp1
        ≤ (K ^ (-(1 / exp1))) ^ exp1 := by gcongr
      _ = K ^ (-1 : ℝ) := by
        rw [← Real.rpow_mul (by positivity)]
        have h_exp : (-(1 / exp1)) * exp1 = -1 := by
          field_simp [hexp1_pos.ne'] <;> ring
        rw [h_exp]
    have h3 : 0 < δ ^ exp1 := by positivity
    have h4 : K ≤ (δ ^ exp1)⁻¹ := by
      have h5 : (δ ^ exp1)⁻¹ ≥ K := by
        calc (δ ^ exp1)⁻¹
          ≥ (K ^ (-1 : ℝ))⁻¹ := by gcongr
        _ = K := by
          have h6 : (K ^ (-1 : ℝ))⁻¹ = K := by
            rw [Real.rpow_neg_one, inv_inv]
          exact h6
      exact h5
    have h7 : (δ ^ exp1)⁻¹ = δ ^ (-exp1) := by
      rw [← Real.rpow_neg hδ_pos.le]
      <;> ring
    rw [h7] at h4
    exact h4
  have h_conv1 : K * δ ^ (-ε_app) ≤ δ ^ (-ε_strong) := by
    have h_rpow : δ ^ (-exp1) * δ ^ (-ε_app) = δ ^ (-exp1 + (-ε_app)) :=
      Eq.symm (Real.rpow_add hδ_pos (-exp1) (-ε_app))
    have h_sum : -exp1 + (-ε_app) = -ε_strong := by
      dsimp only [exp1] <;> ring
    calc K * δ ^ (-ε_app)
      ≤ δ ^ (-exp1) * δ ^ (-ε_app) := by gcongr
    _ = δ ^ (-exp1 + (-ε_app)) := h_rpow
    _ = δ ^ (-ε_strong) := by rw [h_sum]
  -- Conversion 2: K·δ^{-(s_app+ε_app)} ≤ δ^{-σ}
  have hK_leδ_neg_exp2 : K ≤ δ ^ (-exp2) := by
    have h1 : δ ≤ K ^ (-(1 / exp2)) := hδ_le_δ₀K2
    have h2 : δ ^ exp2 ≤ K ^ (-1 : ℝ) := by
      calc δ ^ exp2
        ≤ (K ^ (-(1 / exp2))) ^ exp2 := by gcongr
      _ = K ^ (-1 : ℝ) := by
        rw [← Real.rpow_mul (by positivity)]
        have h_exp : (-(1 / exp2)) * exp2 = -1 := by
          field_simp [hexp2_pos.ne'] <;> ring
        rw [h_exp]
    have h3 : 0 < δ ^ exp2 := by positivity
    have h4 : K ≤ (δ ^ exp2)⁻¹ := by
      have h5 : (δ ^ exp2)⁻¹ ≥ K := by
        calc (δ ^ exp2)⁻¹
          ≥ (K ^ (-1 : ℝ))⁻¹ := by gcongr
        _ = K := by
          have h6 : (K ^ (-1 : ℝ))⁻¹ = K := by
            rw [Real.rpow_neg_one, inv_inv]
          exact h6
      exact h5
    have h7 : (δ ^ exp2)⁻¹ = δ ^ (-exp2) := by
      rw [← Real.rpow_neg hδ_pos.le] <;> ring
    rw [h7] at h4
    exact h4
  have h_conv2 : K * δ ^ (-(s_app + ε_app)) ≤ δ ^ (-σ) := by
    have h_rpow : δ ^ (-exp2) * δ ^ (-(s_app + ε_app)) = δ ^ (-exp2 + (-(s_app + ε_app))) :=
      Eq.symm (Real.rpow_add hδ_pos (-exp2) (-(s_app + ε_app)))
    have h_sum : -exp2 + (-(s_app + ε_app)) = -σ := by
      dsimp only [exp2] <;> ring
    calc K * δ ^ (-(s_app + ε_app))
      ≤ δ ^ (-exp2) * δ ^ (-(s_app + ε_app)) := by gcongr
    _ = δ ^ (-exp2 + (-(s_app + ε_app))) := h_rpow
    _ = δ ^ (-σ) := by rw [h_sum]
  -- Delta-set constant upgrade
  have hA_delta_strong : IsRealDeltaSet δ κ (δ ^ (-ε_strong)) A :=
    IsRealDeltaSet.mono_const' hA_delta h_conv1
  -- Covering number upgrade
  have hN_strong : Nreal δ A ≤ ENNReal.ofReal (δ ^ (-σ)) := by
    calc Nreal δ A
      ≤ ENNReal.ofReal (K * δ ^ (-(s_app + ε_app))) := hN_bound
    _ ≤ ENNReal.ofReal (δ ^ (-σ)) := ENNReal.ofReal_le_ofReal h_conv2
  -- Volume bound: volume(A) ≤ δ·Nδ(A) ≤ K·δ^{1-s_app-ε_app} ≤ δ^{1-σ}
  have hA_bdd : Bornology.IsBounded A :=
    (Metric.isBounded_Icc (1 : ℝ) 2).subset hA_sub
  have hvol1 : volume A ≤ ENNReal.ofReal δ * Nreal δ A :=
    covering_number_ge_measure_div_delta hδ_pos hA_bdd
  have h6 : δ * δ ^ (-σ) = δ ^ (1 - σ) := by
    have h_rpow : δ ^ (1 : ℝ) * δ ^ (-σ) = δ ^ (1 + (-σ)) :=
      Eq.symm (Real.rpow_add hδ_pos 1 (-σ))
    have h_simp : δ ^ (1 : ℝ) = δ := by simp
    have h_sum : 1 + (-σ) = 1 - σ := by ring
    rw [h_simp] at h_rpow
    rw [h_sum] at h_rpow
    exact h_rpow
  have hvol2 : volume A ≤ ENNReal.ofReal (δ ^ (1 - σ)) := by
    calc volume A
      ≤ ENNReal.ofReal δ * Nreal δ A := hvol1
    _ ≤ ENNReal.ofReal δ * ENNReal.ofReal (K * δ ^ (-(s_app + ε_app))) := by gcongr
    _ = ENNReal.ofReal (δ * (K * δ ^ (-(s_app + ε_app)))) := by
        rw [← ENNReal.ofReal_mul (by positivity)] <;> ring
    _ ≤ ENNReal.ofReal (δ * δ ^ (-σ)) := by
        apply ENNReal.ofReal_le_ofReal
        gcongr <;> exact h_conv2
    _ = ENNReal.ofReal (δ ^ (1 - σ)) := by rw [h6]
  -- Apply corrected strong ring theorem
  exact h_strong hδ_dyadic hδ_pos hδ_le_strong A μ t hA_sub
    hA_delta_strong hvol2 hN_strong hFrost hμ_supp htc ht_le_one

end WeakTwoEndsSumProduct
