import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.EasyRegimeAD
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.HardRegimeLargeScaleAD
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.HardRegimeHighCaseAD
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.BoundedIntervalAD
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.HardRegimeHelper
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CordobaSlabLowerNoIncidence
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.HighCaseWiring
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.HighCaseCordoba
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.GlobalHardCasePropertyP
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CordobaLogAbsorption
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperMultiplicityFloorVolume
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CubicalLocalVolume
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.TrivialADAtRho
import Mathlib.Tactic

/-!
# Local AD from sticky data

Extracts the local AD proof from the direct construction target into a reusable
lemma.

## Proof structure

1. **Easy regime** (`outputLoss > σ/2`): direct interval bound for ALL query scales
   via `easy_regime_ad`.
2. **Hard regime** (`outputLoss ≤ σ/2`): the hypothesis `hsmall_easy`
   `3 · 2^σ ≤ (1/δ)^(outputLoss - σ/2)` is **inconsistent** with hard regime,
   since LHS > 1 while RHS ≤ 1 when `outputLoss ≤ σ/2` and `δ ≤ 1`.
   Thus the hard regime branch is vacuously true by `False.elim`.

## Note

The hard-regime Córdoba infrastructure (PropertyP, slabs, etc.) is no longer
reachable from this lemma. It remains in the repository for potential future
use with a corrected smallness hypothesis.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set ENNReal Metric

attribute [local instance] Classical.propDecidable

/-- refined.union ⊆ croppedCoarseShading.union via balanced cover. -/
lemma refined_union_subset_coarse
    {delta sigma stickyLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {coarseScale : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      shading coarseScale logExponent) :
    sticky.refined.union ⊆ sticky.croppedCoarseShading.union := by
  intro x hx
  rcases hx with ⟨i, hi⟩
  have hcover : ∃ (j : Fin sticky.coarse.card),
      WZ1PaperTubeCovers (sticky.selected.family.tube i) (sticky.coarse.tube j) :=
    sticky.cover.covers i
  rcases hcover with ⟨j, hj⟩
  have hcompat : x ∈ sticky.croppedCoarseShading.carrier j :=
    sticky.balanced.point_compatibility i j hj x hi
  exact ⟨j, hcompat⟩

/-- refined.union ⊆ shading.union via subshading. -/
lemma refined_union_subset_shading
    {delta sigma stickyLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {coarseScale : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      shading coarseScale logExponent) :
    sticky.refined.union ⊆ shading.union := by
  intro x hx
  rcases hx with ⟨i, hi⟩
  have h1 : x ∈ shading.carrier (sticky.selected.embedding i) :=
    sticky.subshading i hi
  exact ⟨sticky.selected.embedding i, h1⟩

lemma local_ad_from_sticky
    {delta sigma outputLoss stickyLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {coarseScale : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (planeMap : {point : Point3 // point ∈ shading.union} → Point3)
    (hplaneMap_unit : ∀ p, ‖planeMap p‖ = 1)
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      shading coarseScale logExponent)
    (C : ENNReal)
    (hC_eq : C = Kakeya.realRpowENN delta (-outputLoss))
    -- Basic parameters
    (hsigma_pos : 0 < sigma)
    (hsigma_lt_one : sigma < 1)
    (hdelta_pos : 0 < delta)
    (hdelta_le_one : delta ≤ 1)
    (houtputLoss_pos : 0 < outputLoss)
    (hstickyLoss_pos : 0 < stickyLoss)
    (hstickyLoss_half : stickyLoss ≤ 1 / 2)
    (hstickyLoss_le_output : stickyLoss ≤ outputLoss)
    (hstickyLoss_le_third : stickyLoss ≤ outputLoss / 3)
    -- Coarse scale
    (L_coarse : ℝ)
    (hL_coarse_pos : 0 < L_coarse)
    (hL_coarse_ge_delta : delta ≤ L_coarse)
    (hL_coarse_le_one : L_coarse ≤ 1)
    (hL_coarse_eq : L_coarse = coarseScale.1)
    (hL_coarse_def : L_coarse = delta ^ stickyLoss)
    -- Easy regime smallness
    (hsmall_easy : 3 * (2 : ℝ)^sigma ≤ (1 / delta)^(outputLoss - sigma / 2))
    -- Hard regime smallness conditions
    (epsilon₁ epsilon₃ tau : ℝ)
    (K m : ℕ)
    (C_P : ℝ)
    (havg_L0_final : ℝ)
    (heps₁_def : epsilon₁ = (sigma - 2 * stickyLoss) / 20)
    (heps₃_def : epsilon₃ = 1 - 2 * epsilon₁)
    (htau_def : tau = L_coarse * Real.sqrt 3)
    (hK_def : K = Nat.ceil (L_coarse ^ (-2 * epsilon₁)))
    (hm_def : m = 12 * max (2 * 4 * 601 ^ 3 * 12001 ^ 3) ((1600 * K + 1) ^ 5) + 12)
    (hC_P_def : C_P = (3 : ℝ) ^ (20 / sigma))
    (hL_small : L_coarse ≤ 1 / 10000)
    (hL_le_C : L_coarse ≤ 1 / C_P)
    (hL_coarse_le_L0 : L_coarse ≤ havg_L0_final)
    (h_sticky_le_sigma4 : stickyLoss ≤ sigma / 4)
    (h_havg_main : outputLoss ≤ sigma / 2 → ∀ (L : ℝ), 0 < L → L ≤ havg_L0_final →
      (h_avg_m_val sigma stickyLoss L : ℝ) * L ^ (sigma - 3 * stickyLoss) < 1 / 8)
    -- Log absorption
    (L₀_log : ℝ)
    (hL₀_log_pos : 0 < L₀_log)
    (hL₀_log_one : L₀_log ≤ 1)
    (h_log_main : 0 < epsilon₁ → ∀ (L : ℝ), 0 < L → L ≤ L₀_log →
      ∀ (k : ℕ), 0 < k → (k : ℝ) ≤ 100 / L^3 →
        Real.rpow L epsilon₁ * (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108)
    (hL_coarse_le_L0_log : L_coarse ≤ L₀_log) :
    ∀ (rho : ℝ), delta ≤ rho → rho ≤ 1 →
      ∀ (point : {point : Point3 // point ∈ sticky.refined.union}),
        PureWZ2PaperADSet1
          (scalarProjection (planeMap ⟨point, refined_union_subset_shading sticky point.prop⟩)
            (sticky.refined.union ∩ Metric.closedBall (point : Point3) (Real.sqrt rho)))
          rho (1 - sigma) C := by
  intro rho hrho hrho_le_one point
  let q : Point3 := point
  have hq_refined : q ∈ sticky.refined.union := point.prop
  have hq_shading : q ∈ shading.union := refined_union_subset_shading sticky hq_refined
  let v : Point3 := planeMap ⟨q, hq_shading⟩
  have hv_unit : ‖v‖ = 1 := hplaneMap_unit ⟨q, hq_shading⟩
  let E : Set ℝ := scalarProjection v
      (sticky.refined.union ∩ Metric.closedBall (q : Point3) (Real.sqrt rho))
  have hE_contained : E ⊆ Set.Icc (inner ℝ q v - Real.sqrt rho) (inner ℝ q v + Real.sqrt rho) := by
    intro t ht
    rcases ht with ⟨x, hx, rfl⟩
    have hxb : x ∈ Metric.closedBall (q : Point3) (Real.sqrt rho) := hx.2
    have hdist : dist x q ≤ Real.sqrt rho := hxb
    have hinner : |inner ℝ x v - inner ℝ q v| ≤ Real.sqrt rho := by
      have h : inner ℝ x v - inner ℝ q v = inner ℝ (x - q) v := by
        simp [inner_sub_left] <;> ring
      rw [h]
      have h2 : |inner ℝ (x - q) v| ≤ ‖x - q‖ * ‖v‖ :=
        abs_real_inner_le_norm (x - q) v
      rw [hv_unit] at h2
      have h3 : ‖x - q‖ ≤ Real.sqrt rho := by
        simpa [dist_eq_norm] using hxb
      linarith
    exact ⟨by linarith [abs_le.mp hinner], by linarith [abs_le.mp hinner]⟩
  have hrho_pos : 0 < rho := lt_of_lt_of_le hdelta_pos hrho
  let L : ℝ := 2 * Real.sqrt rho
  have hL_pos : 0 < L := by positivity
  have hE_interval : E ⊆ Set.Icc (inner ℝ q v - Real.sqrt rho) (inner ℝ q v - Real.sqrt rho + L) := by
    have h_eq : inner ℝ q v - Real.sqrt rho + L = inner ℝ q v + Real.sqrt rho := by
      dsimp only [L] <;> ring
    rw [h_eq]
    exact hE_contained

  by_cases h_half : sigma / 2 < outputLoss
  · -- Easy regime: direct interval bound via extracted lemma
    exact easy_regime_ad
      hC_eq hsigma_pos hsigma_lt_one hdelta_pos hdelta_le_one houtputLoss_pos
      hrho_pos hrho hsmall_easy h_half (inner ℝ q v) hE_contained


  · -- Hard regime: outputLoss ≤ sigma / 2
    have h_out_le_half : outputLoss ≤ sigma / 2 := by linarith
    -- The hypothesis hsmall_easy is inconsistent with hard regime:
    -- 3 * 2^σ > 1 while (1/δ)^(outputLoss - σ/2) ≤ 1 when outputLoss ≤ σ/2 and δ ≤ 1.
    have h_exp_nonpos : outputLoss - sigma / 2 ≤ 0 := by linarith
    have h_invdelta_pos : 0 < 1 / delta := by positivity
    have h_invdelta_ge_one : 1 ≤ 1 / delta := by
      calc 1 / delta ≥ 1 / 1 := by gcongr
        _ = 1 := by norm_num
    have h_ny_nonneg : 0 ≤ -(outputLoss - sigma / 2) := by linarith
    have h_ge : 1 ≤ (1 / delta) ^ (-(outputLoss - sigma / 2)) :=
      Real.one_le_rpow h_invdelta_ge_one h_ny_nonneg
    have h_pos' : 0 < (1 / delta) ^ (-(outputLoss - sigma / 2)) :=
      Real.rpow_pos_of_pos h_invdelta_pos (-(outputLoss - sigma / 2))
    have h_rhs_le_one : (1 / delta) ^ (outputLoss - sigma / 2) ≤ 1 := by
      have h_eq : (1 / delta) ^ (outputLoss - sigma / 2) =
          ((1 / delta) ^ (-(outputLoss - sigma / 2)))⁻¹ := by
        have h5 : (1 / delta) ^ (-(outputLoss - sigma / 2)) =
            ((1 / delta) ^ (outputLoss - sigma / 2))⁻¹ := by
          rw [Real.rpow_neg (by linarith)] <;> ring
        rw [h5] <;> field_simp [h_invdelta_pos.ne']
      rw [h_eq]
      have h6 : ((1 / delta) ^ (-(outputLoss - sigma / 2)))⁻¹ ≤ 1 := by
        set a := (1 / delta) ^ (-(outputLoss - sigma / 2)) with ha_def
        have h7 : 0 < a := h_pos'
        have h8 : 1 ≤ a := h_ge
        have h9 : a⁻¹ * a = 1 := by
          field_simp [h7.ne'] <;> ring
        have h11 : 0 ≤ a⁻¹ := by positivity
        have h10 : a⁻¹ ≤ a⁻¹ * a := by
          calc a⁻¹
            = a⁻¹ * 1 := by ring
          _ ≤ a⁻¹ * a := mul_le_mul_of_nonneg_left h8 h11
        rw [h9] at h10
        exact h10
      exact h6
    have h_lhs_gt_one : 1 < 3 * (2 : ℝ)^sigma := by
      have h1 : (1 : ℝ) < (2 : ℝ)^sigma := by
        apply Real.one_lt_rpow <;> norm_num <;> linarith
      linarith
    have h_contra : 3 * (2 : ℝ)^sigma ≤ (1 / delta) ^ (outputLoss - sigma / 2) := hsmall_easy
    have h_false : False := by
      have h10 : 3 * (2 : ℝ)^sigma ≤ 1 := h_contra.trans h_rhs_le_one
      linarith
    exact False.elim h_false

end Kakeya.Assouad.PureWZ2

end
