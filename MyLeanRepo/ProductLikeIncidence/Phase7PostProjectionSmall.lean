module

/-
# Phase 7 Post-Projection Smallness Lemma (Route B / Factor 6)

Extracted from Phase7FullIntegrationV2. Uses interval thickening containment
instead of exact equality for S_pre, giving factor 6 = 3 (thickening) × 2 (scalar).

## Proof chain

Given `S_pre y ⊆ intervalThicken(raw_proj, ε)` where `ε = δ*(1+|x y|)/2`:

1. `post_proj ⊆ scaleSet(c_i, S_pre y) ⊆ intervalThicken(scaleSet(c_i, raw_proj), δ)`
   because `|c_i| * ε ≤ δ` (sector-specific bound)
2. `N(intervalThicken δ X) ≤ 3 * N(X)` (ThickeningCovering)
3. `N(scaleSet(chartFullLambda, A_y)) ≤ 2 * N(A_y)` (scalar covering, |chartFullLambda|≤1)
4. Total: `N(post_proj) ≤ 3 * 2 * N(A_y) = 6 * N(A_y)`

## Dependencies

- `MyLeanRepo.ProductLikeIncidence.ThickeningCovering` — intervalThicken helpers
- `MyLeanRepo.RoundingWrapper` — Nreal_mono_local
-/

public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.ProductLikeBasic
public import MyLeanRepo.Compat
public import MyLeanRepo.RoundingWrapper
public import MyLeanRepo.SetDiscretizationBridge
public import MyLeanRepo.ProductLikeIncidence.ThickeningCovering
public import MyLeanRepo.ProductLikeIncidence.FourSectorChart
public import MyLeanRepo.ProductLikeIncidence.ChartFullLambda
public import MyLeanRepo.ProductLikeIncidence.Phase7ScaledProjections
public import MyLeanRepo.ProductLikeIncidence.DirectionFailureCompositionV8
public import MyLeanRepo.FourSectorSelection
public import MyLeanRepo.OSWPrelude

@[expose] public section

open Set ENNReal Bornology Classical

noncomputable section

namespace ProductLikeIncidence.ProductReduction

/-- Post-projection smallness for a single y in the selected sector (Route B, factor 6). -/
lemma phase7_post_projection_small_routeB
    {δ s η εgain L_exp C_raw C_Pbar c_proj K_BSG : ℝ}
    {q_graph_total q_diff q_size ζ_dir η_proj : ℝ}
    {Y : Set ℝ}
    {θ1 θ2 θ3 : ℝ}
    {x : ℝ → ℝ}
    {F_graph : Set (EuclideanSpace ℝ (Fin 2))}
    {S_pre : ℝ → Set ℝ}
    {T_y_points : ℝ → Set (EuclideanSpace ℝ (Fin 2))}
    {Pbar_param : Set (EuclideanSpace ℝ (Fin 2))}
    {B1 B2 : Set ℝ}
    (hδ_pos : 0 < δ)
    (hδ_lt_one : δ < 1)
    (h_budget : εgain > q_graph_total + 2 * q_diff + q_size + η + ζ_dir + η_proj)
    (h_proj_budget : (L_exp - 1 / 2 : ℝ) * η < ζ_dir + η_proj)
    (h_factor_absorb : 6 * C_raw * Real.sqrt C_Pbar *
        δ ^ (ζ_dir + η_proj - (L_exp - 1 / 2 : ℝ) * η) < 1)
    (hC_raw_pos : 0 < C_raw)
    (hC_Pbar_pos : 0 < C_Pbar)
    (hc_proj_pos : 0 < c_proj)
    (hK_BSG_pos : 0 < K_BSG)
    (hεgain_pos : 0 < εgain)
    (hK_BSG_le : K_BSG ≤ δ ^ (-q_diff))
    (hc_proj_ge : c_proj ≥ δ ^ q_graph_total)
    (h_delta_small : δ ^ (εgain - (q_graph_total + 2 * q_diff + q_size + η + ζ_dir + η_proj)) ≤ 1 / 64)
    (i : Fin 4)
    (y : ℝ)
    (Θ_sec : Set ℝ)
    (hy : y ∈ Θ_sec)
    (hy_ne_theta2 : y ≠ θ2)
    (hΘ_sec_sub_Y : Θ_sec ⊆ Y)
    (h_sector : sectorPredicate i x y)
    (hx_formula : ∀ y, x y = ((θ2 - θ3) * (y - θ1)) / ((θ3 - θ1) * (θ2 - y)))
    (hT_sub : ∀ y ∈ Y, T_y_points y ⊆ Pbar_param)
    (hS_pre_thick : ∀ y ∈ Y, y ≠ θ2 → S_pre y ⊆
      intervalThicken (δ * (1 + |x y|) / 2) (phase7ScaledProjection y θ2 θ3 (T_y_points y)))
    (hPbar_bdd : IsBounded Pbar_param)
    (hPbar_small : ENat.toENNReal (dyadicCoveringNumber δ Pbar_param) <
        ENNReal.ofReal (C_Pbar * δ ^ (-(2 * s + η))))
    (h_raw_proj_bound : ∀ y ∈ Y,
      Nreal δ (Set.image (fun q : EuclideanSpace ℝ (Fin 2) => q 0 * y + q 1) (T_y_points y)) ≤
      ENNReal.ofReal C_raw *
      ENNReal.ofReal (δ ^ (-(L_exp * η))) *
      ENNReal.ofReal (Real.sqrt ((ENat.toENNReal (dyadicCoveringNumber δ Pbar_param)).toReal)))
    (h_chartFullLambda_bound : ∀ (i : Fin 4) (y : ℝ), sectorPredicate i x y →
      |chartFullLambda i y θ1 θ3 θ2 x| ≤ 1)
    (hB1_lower : Nreal δ B1 ≥ ENNReal.ofReal (δ ^ (-s + q_size)))
    (hB2_lower : Nreal δ B2 ≥ ENNReal.ofReal (δ ^ (-s + q_size)))
    :
    ENat.toENNReal (dyadicCoveringNumber δ
      (projectionSet1D (sectorTMap i (x y))
        (FourSectorChart.chartSectorCoordPoint i ''
          (F_graph ∩ {p | p 0 * x y + p 1 ∈ S_pre y})))) <
    (1 / 2 : ENNReal) * ENNReal.ofReal (c_proj / (16 * K_BSG^2)) *
      ENNReal.ofReal (δ ^ (-εgain)) *
      Nreal δ (sectorCoordSet i B2 B1) := by
  let G_y := F_graph ∩ {p | p 0 * x y + p 1 ∈ S_pre y}
  let A_y := Set.image (fun q : EuclideanSpace ℝ (Fin 2) => q 0 * y + q 1) (T_y_points y)
  let B2_sec := sectorCoordSet i B2 B1
  let c_i := FourSectorChart.chartSectorScalar i (x y)
  let lam_y := (θ2 - θ3) / (θ2 - y)
  let raw_proj : Set ℝ := phase7ScaledProjection y θ2 θ3 (T_y_points y)
  let ε_y := δ * (1 + |x y|) / 2

  have h_y_in_Y : y ∈ Y := hΘ_sec_sub_Y hy
  have h_chart_pred : FourSectorChart.chartSectorPred i (x y) := by
    have h_sp : sectorPredicate i x y := h_sector
    fin_cases i <;> simp [sectorPredicate, FourSectorChart.chartSectorPred,
      Set.mem_Icc, Set.mem_Ioi, Set.mem_Ico, Set.mem_Iio] at h_sp ⊢ <;> tauto

  let post_proj_real : Set ℝ := projectionSet (sectorTMap i (x y))
      (FourSectorChart.chartSectorCoordPoint i '' G_y)

  -- Step 1: post_proj = scaleSet c_i (affineProjection x(y) G_y)
  have h1 : post_proj_real = scaleSet c_i (affineProjection (x y) G_y) :=
    FourSectorChart.chart_sector_projection_set i (x y) h_chart_pred G_y

  -- Step 2: affineProjection x(y) G_y ⊆ S_pre y
  have h2 : affineProjection (x y) G_y ⊆ S_pre y := by
    intro z hz
    rcases hz with ⟨p, hp, rfl⟩
    exact hp.2

  -- Step 3: S_pre y ⊆ intervalThicken ε_y raw_proj
  have h3 : S_pre y ⊆ intervalThicken ε_y raw_proj :=
    hS_pre_thick y h_y_in_Y hy_ne_theta2

  -- Step 4: post_proj ⊆ scaleSet c_i (intervalThicken ε_y raw_proj)
  have h4 : post_proj_real ⊆ scaleSet c_i (intervalThicken ε_y raw_proj) := by
    rw [h1]
    have h5 : scaleSet c_i (affineProjection (x y) G_y) ⊆ scaleSet c_i (S_pre y) := by
      intro z hz
      rcases hz with ⟨w, hw, rfl⟩
      exact ⟨w, h2 hw, rfl⟩
    have h6 : scaleSet c_i (S_pre y) ⊆ scaleSet c_i (intervalThicken ε_y raw_proj) := by
      intro z hz
      rcases hz with ⟨w, hw, rfl⟩
      exact ⟨w, h3 hw, rfl⟩
    exact subset_trans h5 h6

  have h_eps_y_nonneg : 0 ≤ ε_y := by
    dsimp only [ε_y]; positivity

  -- Step 5: scaleSet c_i (intervalThicken ε_y raw_proj)
  --         = intervalThicken (|c_i| * ε_y) (scaleSet c_i raw_proj)
  have h5 : scaleSet c_i (intervalThicken ε_y raw_proj) =
      intervalThicken (|c_i| * ε_y) (scaleSet c_i raw_proj) :=
    scaleSet_intervalThicken c_i ε_y raw_proj h_eps_y_nonneg

  -- Step 6: Sector error bound |c_i| * ε_y ≤ δ
  have h6_sector_error : |c_i| * ε_y ≤ δ := by
    have h_main : |c_i| * (1 + |x y|) / 2 ≤ 1 := by
      fin_cases i
      · -- Sector 0: 0 ≤ x y ≤ 1, scalar = 1
        have h1 : 0 ≤ x y ∧ x y ≤ 1 := by simpa [sectorPredicate, Set.mem_Icc] using h_sector
        have h2 : |x y| ≤ 1 := by rw [abs_le] <;> constructor <;> linarith
        have h_scalar : |c_i| = 1 := by
          simp [c_i, FourSectorChart.chartSectorScalar] <;> norm_num
        rw [h_scalar]; linarith
      · -- Sector 1: x y > 1, scalar = 1/(x y)
        have h1 : 1 < x y := by simpa [sectorPredicate, Set.mem_Ioi] using h_sector
        have h2 : 0 < x y := by linarith
        have h3 : |x y| = x y := abs_of_pos h2
        have h_scalar : |c_i| = 1 / (x y) := by
          simp [c_i, FourSectorChart.chartSectorScalar, h3] <;> field_simp [h2.ne'] <;> ring
        rw [h_scalar, h3]
        field_simp [h2.ne'] <;> linarith
      · -- Sector 2: -1 ≤ x y < 0, scalar = 1
        have h1 : -1 ≤ x y ∧ x y < 0 := by simpa [sectorPredicate, Set.mem_Ico] using h_sector
        have h2 : |x y| ≤ 1 := by rw [abs_le] <;> constructor <;> linarith
        have h_scalar : |c_i| = 1 := by
          simp [c_i, FourSectorChart.chartSectorScalar] <;> norm_num
        rw [h_scalar]; linarith
      · -- Sector 3: x y < -1, scalar = 1/(x y)
        have h1 : x y < -1 := by simpa [sectorPredicate, Set.mem_Iio] using h_sector
        have h2 : 0 < |x y| := abs_pos.mpr (show x y ≠ 0 from by linarith)
        have h3 : 1 < |x y| := by
          have h4 : |x y| = -(x y) := by rw [abs_of_neg] <;> linarith
          rw [h4] <;> linarith
        have h_scalar : |c_i| = 1 / |x y| := by
          simp [c_i, FourSectorChart.chartSectorScalar] <;> field_simp [h2.ne'] <;> ring
        rw [h_scalar]
        have h5 : (1 / |x y|) * (1 + |x y|) / 2 ≤ 1 := by
          have h6 : 0 < |x y| := h2
          have h7 : 1 ≤ |x y| := by linarith
          field_simp [h6.ne'] <;> linarith
        exact h5
    have h_eps : ε_y = δ * ((1 + |x y|) / 2) := by dsimp only [ε_y] <;> ring
    rw [h_eps]
    have h : |c_i| * (δ * ((1 + |x y|) / 2)) = δ * (|c_i| * (1 + |x y|) / 2) := by ring
    rw [h]
    have h_final : δ * (|c_i| * (1 + |x y|) / 2) ≤ δ := by
      have h := mul_le_mul_of_nonneg_left h_main hδ_pos.le
      simpa using h
    exact h_final

  -- Step 7: post_proj ⊆ intervalThicken δ (scaleSet c_i raw_proj)
  have h7 : post_proj_real ⊆ intervalThicken δ (scaleSet c_i raw_proj) := by
    intro z hz
    have hz' : z ∈ scaleSet c_i (intervalThicken ε_y raw_proj) := h4 hz
    rw [h5] at hz'
    rcases hz' with ⟨a, ha, hza⟩
    exact ⟨a, ha, le_trans hza h6_sector_error⟩

  -- Step 8: scaleSet c_i raw_proj = scaleSet chartFullLambda A_y
  have h_lambda_eq : chartFullLambda i y θ1 θ3 θ2 x = c_i * lam_y := by
    fin_cases i <;> simp [chartFullLambda, FourSectorChart.chartSectorScalar, c_i, lam_y] <;> ring
  have h9 : scaleSet c_i raw_proj = scaleSet (chartFullLambda i y θ1 θ3 θ2 x) A_y := by
    have h10 : raw_proj = scaleSet lam_y A_y := by rfl
    rw [h10]
    ext z
    simp only [scaleSet, Set.mem_image]
    constructor
    · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨u, hu, by rw [h_lambda_eq] <;> ring⟩
    · rintro ⟨u, hu, rfl⟩
      refine ⟨lam_y * u, ⟨u, hu, rfl⟩, ?_⟩
      rw [h_lambda_eq] <;> ring

  -- Step 9: Fiber bounded
  let f_proj : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ :=
    { toFun := fun q => q 0 * y + q 1
      map_add' := by intro a b; simp [add_mul]; ring
      map_smul' := by intro c a; simp [smul_eq_mul]; ring }
  have h_fiber_bdd : IsBounded A_y := by
    have h1 : A_y ⊆ f_proj '' Pbar_param := by
      intro z hz
      rcases hz with ⟨w, hw, rfl⟩
      exact ⟨w, hT_sub y h_y_in_Y hw, rfl⟩
    have h_img_bdd : IsBounded (f_proj '' Pbar_param) := hPbar_bdd.image f_proj
    exact IsBounded.subset h_img_bdd h1

  let X := scaleSet (chartFullLambda i y θ1 θ3 θ2 x) A_y
  have hX_bdd : IsBounded X := WeakTwoEndsSumProduct.scaleSet_bounded h_fiber_bdd
  have h_coeff_abs : |chartFullLambda i y θ1 θ3 θ2 x| ≤ 1 :=
    h_chartFullLambda_bound i y h_sector

  -- Step 10: N(post_proj) ≤ 3 * N(X) ≤ 3 * 2 * N(A_y) = 6 * N(A_y)
  have h_sub' : post_proj_real ⊆ intervalThicken δ X := by
    calc post_proj_real
      ⊆ intervalThicken δ (scaleSet c_i raw_proj) := h7
    _ = intervalThicken δ X := by rw [h9]

  have h10 : Nreal δ post_proj_real ≤ Nreal δ (intervalThicken δ X) :=
    robust_projection_main.Nreal_mono_local h_sub'

  have h11 : Nreal δ (intervalThicken δ X) ≤ 3 * Nreal δ X :=
    intervalThicken_covering_bound hδ_pos hX_bdd

  have h12 : Nreal δ X ≤ 2 * Nreal δ A_y := by
    have h := FourSectorChart.scalar_covering_upper hδ_pos (by norm_num) h_fiber_bdd h_coeff_abs
    have h_const : (Nat.ceil (1 : ℝ) + 1 : ENNReal) = (2 : ENNReal) := by norm_num
    rw [h_const] at h
    exact h

  have h13 : Nreal δ post_proj_real ≤ 6 * Nreal δ A_y := by
    calc Nreal δ post_proj_real
      ≤ Nreal δ (intervalThicken δ X) := h10
    _ ≤ 3 * Nreal δ X := h11
    _ ≤ 3 * (2 * Nreal δ A_y) := by gcongr
    _ = 6 * Nreal δ A_y := by ring

  -- Step 11: Bound N(A_y) using h_raw_proj_bound + hPbar_small
  have hN_ne_top : ENat.toENNReal (dyadicCoveringNumber δ Pbar_param) ≠ ⊤ := by
    intro h
    rw [h] at hPbar_small
    simp at hPbar_small <;> exact hPbar_small

  have h14 : (ENat.toENNReal (dyadicCoveringNumber δ Pbar_param)).toReal <
      C_Pbar * δ ^ (-(2 * s + η)) := by
    have h_iff : (ENat.toENNReal (dyadicCoveringNumber δ Pbar_param)).toReal <
        (ENNReal.ofReal (C_Pbar * δ ^ (-(2 * s + η)))).toReal :=
      ENNReal.toReal_lt_toReal hN_ne_top ENNReal.ofReal_ne_top |>.mpr hPbar_small
    have h3 : (ENNReal.ofReal (C_Pbar * δ ^ (-(2 * s + η)))).toReal =
        C_Pbar * δ ^ (-(2 * s + η)) := by
      rw [ENNReal.toReal_ofReal] <;> positivity
    rw [h3] at h_iff <;> exact h_iff

  have h15 : Real.sqrt ((ENat.toENNReal (dyadicCoveringNumber δ Pbar_param)).toReal) <
      Real.sqrt C_Pbar * δ ^ (-(s + η / 2)) := by
    have h16 : Real.sqrt ((ENat.toENNReal (dyadicCoveringNumber δ Pbar_param)).toReal) <
        Real.sqrt (C_Pbar * δ ^ (-(2 * s + η))) := Real.sqrt_lt_sqrt (by positivity) h14
    have h17 : Real.sqrt (C_Pbar * δ ^ (-(2 * s + η))) =
        Real.sqrt C_Pbar * δ ^ (-(s + η / 2)) := by
      have h_pos1 : 0 ≤ C_Pbar := by positivity
      have h_pos2 : 0 ≤ δ ^ (-(2 * s + η)) := by positivity
      rw [Real.sqrt_mul h_pos1]
      have h_sqrt : Real.sqrt (δ ^ (-(2 * s + η))) = (δ ^ (-(2 * s + η))) ^ (1 / 2 : ℝ) := by
        rw [Real.sqrt_eq_rpow]
      rw [h_sqrt, ← Real.rpow_mul hδ_pos.le] <;> ring_nf
    rw [h17] at h16 <;> exact h16

  have h18 : Nreal δ A_y ≤
      ENNReal.ofReal C_raw *
      ENNReal.ofReal (δ ^ (-(L_exp * η))) *
      ENNReal.ofReal (Real.sqrt ((ENat.toENNReal (dyadicCoveringNumber δ Pbar_param)).toReal)) :=
    h_raw_proj_bound y h_y_in_Y

  have h19 : Nreal δ A_y ≤
      ENNReal.ofReal (C_raw * Real.sqrt C_Pbar * δ ^ (-(s + (L_exp + 1 / 2 : ℝ) * η))) := by
    calc Nreal δ A_y
      ≤ ENNReal.ofReal C_raw *
          ENNReal.ofReal (δ ^ (-(L_exp * η))) *
          ENNReal.ofReal (Real.sqrt ((ENat.toENNReal (dyadicCoveringNumber δ Pbar_param)).toReal)) := h18
    _ ≤ ENNReal.ofReal C_raw *
        ENNReal.ofReal (δ ^ (-(L_exp * η))) *
        ENNReal.ofReal (Real.sqrt C_Pbar * δ ^ (-(s + η / 2))) := by
          have h15' : ENNReal.ofReal (Real.sqrt ((ENat.toENNReal (dyadicCoveringNumber δ Pbar_param)).toReal)) ≤
              ENNReal.ofReal (Real.sqrt C_Pbar * δ ^ (-(s + η / 2))) :=
            ENNReal.ofReal_le_ofReal (le_of_lt h15)
          gcongr
    _ = ENNReal.ofReal (C_raw * Real.sqrt C_Pbar * δ ^ (-(s + (L_exp + 1 / 2 : ℝ) * η))) := by
          have h_exp : δ ^ (-(L_exp * η)) * δ ^ (-(s + η / 2)) =
              δ ^ (-(s + (L_exp + 1 / 2 : ℝ) * η)) := by
            have h_sum : (-(L_exp * η)) + (-(s + η / 2)) = -(s + (L_exp + 1 / 2 : ℝ) * η) := by ring
            have h : δ ^ (-(L_exp * η)) * δ ^ (-(s + η / 2)) = δ ^ ((-(L_exp * η)) + (-(s + η / 2))) := by
              exact Eq.symm (Real.rpow_add hδ_pos (-(L_exp * η)) (-(s + η / 2)))
            rw [h, h_sum]
          have h_mul : C_raw * (δ ^ (-(L_exp * η))) * (Real.sqrt C_Pbar * δ ^ (-(s + η / 2))) =
              C_raw * Real.sqrt C_Pbar * δ ^ (-(s + (L_exp + 1 / 2 : ℝ) * η)) := by
            calc C_raw * (δ ^ (-(L_exp * η))) * (Real.sqrt C_Pbar * δ ^ (-(s + η / 2)))
                = C_raw * Real.sqrt C_Pbar * (δ ^ (-(L_exp * η)) * δ ^ (-(s + η / 2))) := by ring
              _ = C_raw * Real.sqrt C_Pbar * δ ^ (-(s + (L_exp + 1 / 2 : ℝ) * η)) := by rw [h_exp]
          have h_pos1 : 0 ≤ C_raw * δ ^ (-(L_exp * η)) := by positivity
          have h_pos2 : 0 ≤ Real.sqrt C_Pbar * δ ^ (-(s + η / 2)) := by positivity
          have h1a : ENNReal.ofReal C_raw * ENNReal.ofReal (δ ^ (-(L_exp * η))) =
              ENNReal.ofReal (C_raw * δ ^ (-(L_exp * η))) := by
            rw [← ENNReal.ofReal_mul (by positivity)]
          have h2a : ENNReal.ofReal (C_raw * δ ^ (-(L_exp * η))) * ENNReal.ofReal (Real.sqrt C_Pbar * δ ^ (-(s + η / 2))) =
              ENNReal.ofReal ((C_raw * δ ^ (-(L_exp * η))) * (Real.sqrt C_Pbar * δ ^ (-(s + η / 2)))) := by
            exact Eq.symm (ENNReal.ofReal_mul (hp := h_pos1))
          have h2 : (ENNReal.ofReal C_raw * ENNReal.ofReal (δ ^ (-(L_exp * η)))) *
              ENNReal.ofReal (Real.sqrt C_Pbar * δ ^ (-(s + η / 2))) =
              ENNReal.ofReal ((C_raw * δ ^ (-(L_exp * η))) * (Real.sqrt C_Pbar * δ ^ (-(s + η / 2)))) := by
            rw [h1a] <;> exact h2a
          have h_final : ENNReal.ofReal ((C_raw * δ ^ (-(L_exp * η))) * (Real.sqrt C_Pbar * δ ^ (-(s + η / 2)))) =
              ENNReal.ofReal (C_raw * Real.sqrt C_Pbar * δ ^ (-(s + (L_exp + 1 / 2 : ℝ) * η))) := by
            apply congr_arg ENNReal.ofReal
            exact h_mul
          rw [h2, h_final]

  have h20 : Nreal δ post_proj_real ≤
      ENNReal.ofReal (6 * C_raw * Real.sqrt C_Pbar * δ ^ (-(s + (L_exp + 1 / 2 : ℝ) * η))) := by
    set Yval := C_raw * Real.sqrt C_Pbar * δ ^ (-(s + (L_exp + 1 / 2 : ℝ) * η)) with hYval
    have h19' : Nreal δ A_y ≤ ENNReal.ofReal Yval := by simpa [Yval] using h19
    have h6_eq : (6 : ENNReal) = ENNReal.ofReal (6 : ℝ) := by norm_cast
    have h_mul_eq : (6 : ENNReal) * ENNReal.ofReal Yval = ENNReal.ofReal (6 * Yval) := by
      rw [h6_eq]
      have h7 : ENNReal.ofReal (6 : ℝ) * ENNReal.ofReal Yval = ENNReal.ofReal ((6 : ℝ) * Yval) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
      rw [h7]
      <;> congr 1 <;> norm_cast
    calc Nreal δ post_proj_real
      ≤ (6 : ENNReal) * Nreal δ A_y := h13
    _ ≤ (6 : ENNReal) * ENNReal.ofReal Yval := by
        have h : (6 : ENNReal) * Nreal δ A_y ≤ (6 : ENNReal) * ENNReal.ofReal Yval := by
          exact mul_le_mul_of_nonneg_left h19' (by positivity)
        exact h
    _ = ENNReal.ofReal (6 * Yval) := h_mul_eq
    _ = ENNReal.ofReal (6 * C_raw * Real.sqrt C_Pbar * δ ^ (-(s + (L_exp + 1 / 2 : ℝ) * η))) := by
      congr 1
      simp [hYval] <;> ring

  -- Step 12: Factor absorption
  have h_eps_gap_pos : 0 < ζ_dir + η_proj - (L_exp - 1 / 2 : ℝ) * η := by linarith [h_proj_budget]

  have h21 : 6 * C_raw * Real.sqrt C_Pbar * δ ^ (-(s + (L_exp + 1 / 2 : ℝ) * η)) <
      δ ^ (-(s + η + ζ_dir + η_proj)) := by
    have h22 : δ ^ (-(s + (L_exp + 1 / 2 : ℝ) * η)) =
        δ ^ (-(s + η + ζ_dir + η_proj)) * δ ^ (ζ_dir + η_proj - (L_exp - 1 / 2 : ℝ) * η) := by
      rw [← Real.rpow_add hδ_pos] <;> ring_nf
    rw [h22]
    have h23 : 6 * C_raw * Real.sqrt C_Pbar * δ ^ (ζ_dir + η_proj - (L_exp - 1 / 2 : ℝ) * η) < 1 :=
      h_factor_absorb
    have h24 : 0 < δ ^ (-(s + η + ζ_dir + η_proj)) := by positivity
    have h25 : δ ^ (-(s + η + ζ_dir + η_proj)) *
        (6 * C_raw * Real.sqrt C_Pbar * δ ^ (ζ_dir + η_proj - (L_exp - 1 / 2 : ℝ) * η)) <
        δ ^ (-(s + η + ζ_dir + η_proj)) := by
      have h25' := mul_lt_mul_of_pos_left h23 h24
      simpa using h25'
    have h26 : 6 * C_raw * Real.sqrt C_Pbar * (δ ^ (-(s + η + ζ_dir + η_proj)) * δ ^ (ζ_dir + η_proj - (L_exp - 1 / 2 : ℝ) * η)) =
        δ ^ (-(s + η + ζ_dir + η_proj)) * (6 * C_raw * Real.sqrt C_Pbar * δ ^ (ζ_dir + η_proj - (L_exp - 1 / 2 : ℝ) * η)) := by ring
    rw [h26]
    exact h25

  -- Step 13: Target bound
  have hB2_lower' : Nreal δ B2_sec ≥ ENNReal.ofReal (δ ^ (-s + q_size)) := by
    fin_cases i <;> simp [B2_sec, sectorCoordSet] <;>
      (try { exact hB2_lower }) <;> (try { exact hB1_lower })

  let factor_real : ℝ := match i with
    | 0 => 1 / 2 | 1 => 1 / 4 | 2 => 1 / 2 | 3 => 1 / 4
  have h_factor_ge : factor_real ≥ 1 / 4 := by
    dsimp only [factor_real]; fin_cases i <;> norm_num
  have h_factor_le : factor_real ≤ 1 / 2 := by
    dsimp only [factor_real]; fin_cases i <;> norm_num

  have h_real_ineq : factor_real * (c_proj / (16 * K_BSG ^ 2)) * δ ^ (-εgain) * δ ^ (-s + q_size) ≥
      δ ^ (-(s + η + ζ_dir + η_proj)) :=
    direction_budget_absorption
      (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one)
      (h_factor_ge := h_factor_ge)
      (hc_proj_ge := hc_proj_ge)
      (hK_BSG_pos := hK_BSG_pos) (hK_BSG_le := hK_BSG_le)
      (hD_pos := by linarith [h_budget]) (h_delta_small := h_delta_small)

  have h_real_ineq2 : (1 / 2 : ℝ) * (c_proj / (16 * K_BSG ^ 2)) * δ ^ (-εgain) * δ ^ (-s + q_size) ≥
      δ ^ (-(s + η + ζ_dir + η_proj)) := by
    set K := (c_proj / (16 * K_BSG ^ 2)) * δ ^ (-εgain) * δ ^ (-s + q_size) with hK
    have hK_nonneg : 0 ≤ K := by positivity
    have h4 : factor_real * K ≤ (1 / 2 : ℝ) * K :=
      mul_le_mul_of_nonneg_right h_factor_le hK_nonneg
    have h5 : (1 / 2 : ℝ) * (c_proj / (16 * K_BSG ^ 2)) * δ ^ (-εgain) * δ ^ (-s + q_size) = (1 / 2 : ℝ) * K := by ring
    have h_real_ineq' : δ ^ (-(s + η + ζ_dir + η_proj)) ≤ factor_real * K := by
      convert h_real_ineq using 1
      simp [hK] <;> ring
    rw [h5]
    exact le_trans h_real_ineq' h4

  have h_target_ge : (1 / 2 : ENNReal) * ENNReal.ofReal (c_proj / (16 * K_BSG^2)) *
      ENNReal.ofReal (δ ^ (-εgain)) * Nreal δ B2_sec ≥
      ENNReal.ofReal (δ ^ (-(s + η + ζ_dir + η_proj))) := by
    have h_real3 : δ ^ (-(s + η + ζ_dir + η_proj)) ≤
        (1 / 2 : ℝ) * (c_proj / (16 * K_BSG ^ 2)) * δ ^ (-εgain) * δ ^ (-s + q_size) :=
      h_real_ineq2
    have h_half : (1 / 2 : ENNReal) = ENNReal.ofReal (1 / 2 : ℝ) := by
      simp
    have h_combine : (1 / 2 : ENNReal) * ENNReal.ofReal (c_proj / (16 * K_BSG^2)) *
        ENNReal.ofReal (δ ^ (-εgain)) * ENNReal.ofReal (δ ^ (-s + q_size)) =
        ENNReal.ofReal ((1 / 2 : ℝ) * (c_proj / (16 * K_BSG ^ 2)) * δ ^ (-εgain) * δ ^ (-s + q_size)) := by
      rw [h_half]
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      <;> ring
    have h5 : Nreal δ B2_sec ≥ ENNReal.ofReal (δ ^ (-s + q_size)) := hB2_lower'
    have h6 : 0 ≤ (1 / 2 : ENNReal) * ENNReal.ofReal (c_proj / (16 * K_BSG^2)) * ENNReal.ofReal (δ ^ (-εgain)) := by positivity
    have h4 : (1 / 2 : ENNReal) * ENNReal.ofReal (c_proj / (16 * K_BSG^2)) *
        ENNReal.ofReal (δ ^ (-εgain)) * Nreal δ B2_sec ≥
        (1 / 2 : ENNReal) * ENNReal.ofReal (c_proj / (16 * K_BSG^2)) *
        ENNReal.ofReal (δ ^ (-εgain)) * ENNReal.ofReal (δ ^ (-s + q_size)) := by
      exact mul_le_mul_of_nonneg_left h5 h6
    have h3 : (1 / 2 : ENNReal) * ENNReal.ofReal (c_proj / (16 * K_BSG^2)) *
        ENNReal.ofReal (δ ^ (-εgain)) * ENNReal.ofReal (δ ^ (-s + q_size)) ≥
        ENNReal.ofReal (δ ^ (-(s + η + ζ_dir + η_proj))) := by
      rw [h_combine]
      exact ENNReal.ofReal_le_ofReal h_real3
    exact le_trans h3 h4

  -- Convert to conclusion type
  have h_conv : Nreal δ post_proj_real =
      ENat.toENNReal (dyadicCoveringNumber δ
        (projectionSet1D (sectorTMap i (x y))
          (FourSectorChart.chartSectorCoordPoint i '' G_y))) := by rfl

  have h_main : Nreal δ post_proj_real <
      (1 / 2 : ENNReal) * ENNReal.ofReal (c_proj / (16 * K_BSG^2)) *
        ENNReal.ofReal (δ ^ (-εgain)) * Nreal δ B2_sec := by
    calc Nreal δ post_proj_real
      ≤ ENNReal.ofReal (6 * C_raw * Real.sqrt C_Pbar * δ ^ (-(s + (L_exp + 1 / 2 : ℝ) * η))) := h20
    _ < ENNReal.ofReal (δ ^ (-(s + η + ζ_dir + η_proj))) := by
        exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr h21
    _ ≤ (1 / 2 : ENNReal) * ENNReal.ofReal (c_proj / (16 * K_BSG^2)) *
          ENNReal.ofReal (δ ^ (-εgain)) * Nreal δ B2_sec := h_target_ge

  simpa [h_conv] using h_main

end ProductLikeIncidence.ProductReduction
