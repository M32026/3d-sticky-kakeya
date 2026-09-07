import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.HardRegimeHelper
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.HighCaseWiring
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.HighCaseCordoba
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CubicalLocalVolume
import Mathlib.Tactic

/-!
# Hard regime HIGH case AD bound

Extracted from `LocalADFromSticky` to keep that file within memory limits.

When `ρ ≤ δ^(σ/(1-σ))` (HIGH case) and `ρ < L_coarse`, the Córdoba slab
approach yields the AD bound. This module contains the full setup and
delegates to `high_case_cordoba_ad`.

## Main result

- `hard_regime_high_case_ad`: HIGH case AD bound.
-/

namespace Kakeya.Assouad.PureWZ2

open Real Metric Set ENNReal MeasureTheory

/-- Local helper: refined.union ⊆ croppedCoarseShading.union via balanced cover. -/
lemma hard_regime_high_case_refined_subset_coarse
    {delta sigma stickyLoss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {coarseScale : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      shading coarseScale logExponent)
    {x : Point3} (hx : x ∈ sticky.refined.union) :
    x ∈ sticky.croppedCoarseShading.union := by
  rcases hx with ⟨i, hi⟩
  have hcover : ∃ (j : Fin sticky.coarse.card),
      WZ1PaperTubeCovers (sticky.selected.family.tube i) (sticky.coarse.tube j) :=
    sticky.cover.covers i
  rcases hcover with ⟨j, hj⟩
  have hcompat : x ∈ sticky.croppedCoarseShading.carrier j :=
    sticky.balanced.point_compatibility i j hj x hi
  exact ⟨j, hcompat⟩

/-- Hard regime HIGH case: `ρ ≤ δ^(σ/(1-σ))`.

Constructs the geometric setup (S, W0, V_min, V_total, tau facts) and
delegates to `high_case_cordoba_ad`. Contains two sorries for the
remaining geometric and arithmetic sub-goals. -/
lemma hard_regime_high_case_ad
    {delta sigma outputLoss stickyLoss rho : ℝ}
    {C : ENNReal}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {coarseScale : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      shading coarseScale logExponent)
    (hC_eq : C = Kakeya.realRpowENN delta (-outputLoss))
    (hsigma_pos : 0 < sigma)
    (hsigma_lt_one : sigma < 1)
    (hdelta_pos : 0 < delta)
    (hdelta_le_one : delta ≤ 1)
    (houtputLoss_pos : 0 < outputLoss)
    (hstickyLoss_pos : 0 < stickyLoss)
    (hstickyLoss_le_third : stickyLoss ≤ outputLoss / 3)
    (h_out_le_half : outputLoss ≤ sigma / 2)
    (L_coarse : ℝ)
    (hL_coarse_pos : 0 < L_coarse)
    (hL_coarse_eq : L_coarse = (coarseScale : ℝ))
    (hL_coarse_def : L_coarse = delta ^ stickyLoss)
    (hL_small : L_coarse ≤ 1 / 10000)
    (epsilon₁ epsilon₃ tau : ℝ)
    (heps₁_def : epsilon₁ = (sigma - 2 * stickyLoss) / 20)
    (heps₃_def : epsilon₃ = 1 - 2 * epsilon₁)
    (htau_def : tau = L_coarse * Real.sqrt 3)
    (L₀_log : ℝ)
    (hL_coarse_le_L0_log : L_coarse ≤ L₀_log)
    (h_log_main : 0 < epsilon₁ → ∀ (L : ℝ), 0 < L → L ≤ L₀_log →
      ∀ (k : ℕ), 0 < k → (k : ℝ) ≤ 100 / L^3 →
        Real.rpow L epsilon₁ * (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108)
    (propP : PureWZ2PropertyPData
      (sigma := sigma)
      (coarseShading := sticky.croppedCoarseShading)
      (epsilon₁ := epsilon₁) (epsilon₃ := epsilon₃) (tau := tau))
    (h_prop3_eq_prop1 : propP.propertyThree = propP.propertyOne)
    (q : Point3)
    (hq_refined : q ∈ sticky.refined.union)
    (hq_prop3 : q ∈ propP.propertyThree.union)
    (v : Point3)
    (hv_unit : ‖v‖ = 1)
    (h_high : rho ≤ delta ^ (sigma / (1 - sigma)))
    (hrho_pos : 0 < rho)
    (h_arithmetic : ENNReal.ofReal (
        ((volume (sticky.croppedCoarseShading.union ∩ Metric.closedBall q (4 * tau))).toReal /
         (L_coarse ^ (1 + 7 * epsilon₁ + epsilon₃) * tau^2 / 200)) *
        (2 * (2 * (40 * L_coarse)) / rho + 2)) ≤ C)
    : PureWZ2PaperADSet1
        (scalarProjection v (sticky.refined.union ∩ Metric.closedBall q (Real.sqrt rho)))
        rho (1 - sigma) C := by
  have hsg : 2 * stickyLoss ≤ outputLoss := by
    have h : stickyLoss ≤ outputLoss / 3 := hstickyLoss_le_third
    linarith
  have heps₁_pos : 0 < epsilon₁ := by
    rw [heps₁_def]; linarith
  have heps₃_pos : 0 < epsilon₃ := by
    rw [heps₃_def, heps₁_def]; linarith
  have heps_sum : epsilon₁ + epsilon₃ < 1 := by
    rw [heps₃_def]; linarith
  have hcoarseScale_pos : 0 < (coarseScale : ℝ) := by
    rw [←hL_coarse_eq]; exact hL_coarse_pos
  have hcoarseScale_small : (coarseScale : ℝ) ≤ 1 / 10000 := by
    rw [←hL_coarse_eq]; exact hL_small

  have hdelta_lt_one : delta < 1 := by
    by_contra h4
    have h5 : 1 ≤ delta := by linarith
    have h6 : (1 : ℝ) ≤ delta ^ stickyLoss := Real.one_le_rpow h5 (by linarith)
    linarith [hL_small]
  have h_exp_le : 2 * stickyLoss ≤ sigma / (1 - sigma) := by
    have h3 : 0 < 1 - sigma := by linarith
    have h4 : 2 * stickyLoss ≤ sigma / 3 := by linarith [hstickyLoss_le_third, h_out_le_half]
    have h5 : sigma / 3 ≤ sigma / (1 - sigma) := by gcongr <;> linarith
    linarith
  have h_rpow_le : delta ^ (sigma / (1 - sigma)) ≤ delta ^ (2 * stickyLoss) :=
    Real.rpow_le_rpow_of_exponent_ge hdelta_pos hdelta_le_one h_exp_le
  have h_L_sq : L_coarse^2 = delta ^ (2 * stickyLoss) := by
    have h11 : L_coarse = delta ^ stickyLoss := hL_coarse_def
    have h12 : L_coarse^2 = (delta ^ stickyLoss) ^ 2 := by rw [h11]
    have h13 : (delta ^ stickyLoss) ^ 2 = (delta ^ stickyLoss) * (delta ^ stickyLoss) := by ring
    have h14 : (delta ^ stickyLoss) * (delta ^ stickyLoss) = delta ^ (stickyLoss + stickyLoss) :=
      (Real.rpow_add hdelta_pos stickyLoss stickyLoss).symm
    have h15 : stickyLoss + stickyLoss = 2 * stickyLoss := by ring
    rw [h12, h13, h14, h15]
  have h_rho_le_L2 : rho ≤ L_coarse^2 := by
    calc rho
      ≤ delta ^ (sigma / (1 - sigma)) := h_high
    _ ≤ delta ^ (2 * stickyLoss) := h_rpow_le
    _ = L_coarse^2 := h_L_sq.symm
  have h1 : rho ≤ 48 * L_coarse^2 := by
    have h_pos : 0 ≤ L_coarse^2 := by positivity
    linarith
  have hsqrt_rho_le_4tau : Real.sqrt rho ≤ 4 * tau :=
    sqrt_rho_le_4tau hL_coarse_pos (by linarith) htau_def h1
  have hq_coarse : q ∈ sticky.croppedCoarseShading.union :=
    hard_regime_high_case_refined_subset_coarse sticky hq_refined
  let S : Set Point3 := sticky.croppedCoarseShading.union ∩ Metric.closedBall q (4 * tau)
  have hS_eq : S = sticky.croppedCoarseShading.union ∩ Metric.closedBall q (4 * tau) := rfl
  have hS_meas : MeasurableSet S :=
    sticky.croppedCoarseShading.union_measurable.inter Metric.isClosed_closedBall.measurableSet
  have hS_sub_ball : S ⊆ Metric.closedBall q (4 * tau) := by intro x hx; exact hx.2
  let W0 : ℝ := 40 * L_coarse
  have hW0_pos : 0 < W0 := by positivity
  have htau_pos : 0 < tau := by rw [htau_def]; positivity
  have h_exp1_pos : 0 < 1 + 7 * epsilon₁ + epsilon₃ := by linarith [heps₁_pos, heps₃_pos]
  set V_min : ℝ := (L_coarse ^ (1 + 7 * epsilon₁ + epsilon₃)) * tau^2 / 200 with hVmin_def
  have hVmin_pos : 0 < V_min := by
    rw [hVmin_def]
    apply div_pos
    · exact mul_pos (Real.rpow_pos_of_pos hL_coarse_pos (1 + 7 * epsilon₁ + epsilon₃)) (sq_pos_of_pos htau_pos)
    · norm_num
  have hV_total_ne_top : volume S ≠ ⊤ := by
    have h1 : S ⊆ sticky.croppedCoarseShading.union := by intro x hx; exact hx.1
    have h2 : volume sticky.croppedCoarseShading.union ≤ Kakeya.realRpowENN (↑coarseScale) (sigma - stickyLoss) :=
      sticky.coarse_extremal.volume_upper
    have h3 : volume S ≤ Kakeya.realRpowENN (↑coarseScale) (sigma - stickyLoss) :=
      calc volume S
        ≤ volume sticky.croppedCoarseShading.union := measure_mono h1
      _ ≤ Kakeya.realRpowENN (↑coarseScale) (sigma - stickyLoss) := h2
    have h4 : Kakeya.realRpowENN (↑coarseScale) (sigma - stickyLoss) = Kakeya.realRpowENN L_coarse (sigma - stickyLoss) := by
      rw [hL_coarse_eq]
    rw [h4] at h3
    have h5 : Kakeya.realRpowENN L_coarse (sigma - stickyLoss) ≠ ⊤ := by
      simp [Kakeya.realRpowENN, ENNReal.ofReal_ne_top]
    exact ne_top_of_le_ne_top h5 h3
  set V_total : ℝ := (volume S).toReal with hVtotal_def
  have hV_total_pos : 0 < V_total := by
    rw [hVtotal_def]
    have h_pos : 0 < volume S :=
      cubical_shading_local_positive_volume
        sticky.coarse_extremal.cubical hcoarseScale_pos tau
        (by rw [htau_def, hL_coarse_eq] <;> ring) htau_pos q hq_coarse
    exact ENNReal.toReal_pos (ne_of_gt h_pos) hV_total_ne_top
  have hV_total : volume S ≤ ENNReal.ofReal V_total := by
    rw [hVtotal_def]
    have h_eq : ENNReal.ofReal (volume S).toReal = volume S :=
      ENNReal.ofReal_toReal hV_total_ne_top
    exact le_of_eq h_eq.symm
  have hV_total_upper : V_total ≤ 512 * tau^3 :=
    local_volume_upper htau_pos q S hS_sub_ball
  have htau_le_20L : tau ≤ 20 * L_coarse := by
    rw [htau_def]
    have h2 : 0 ≤ L_coarse := by linarith
    have h_sqrt3_le_20 : Real.sqrt 3 ≤ 20 := by
      have h1 : Real.sqrt 3 ≤ 2 := by rw [Real.sqrt_le_iff] <;> norm_num
      linarith
    calc L_coarse * Real.sqrt 3
      ≤ L_coarse * 20 := by gcongr <;> linarith
    _ = 20 * L_coarse := by ring
  have hL_le_tau : L_coarse ≤ tau := by
    rw [htau_def]
    have h4 : 0 ≤ L_coarse := by linarith
    have h_sqrt3_ge_1 : 1 ≤ Real.sqrt 3 := by
      have h1 : (1 : ℝ) ≤ 3 := by norm_num
      have h2 : Real.sqrt 1 ≤ Real.sqrt 3 := Real.sqrt_le_sqrt h1
      have h3 : Real.sqrt 1 = 1 := by simp
      linarith
    calc L_coarse
      = L_coarse * 1 := by ring
    _ ≤ L_coarse * Real.sqrt 3 := by gcongr <;> linarith
  have htau_sq : tau ^ 2 ≤ 4 * L_coarse := by
    rw [htau_def]
    have h4 : (L_coarse * Real.sqrt 3) ^ 2 = 3 * L_coarse ^ 2 := by
      have h5 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
      rw [mul_pow, h5] <;> ring
    rw [h4]
    have h6 : 0 < L_coarse := hL_coarse_pos
    have h7 : 3 * L_coarse ≤ 4 := by linarith [hL_small]
    have h8 : 3 * L_coarse ^ 2 ≤ 4 * L_coarse := by
      calc 3 * L_coarse ^ 2
        = (3 * L_coarse) * L_coarse := by ring
      _ ≤ 4 * L_coarse := by gcongr <;> linarith
    exact h8
  have htau_le_one : tau ≤ 1 := by
    rw [htau_def]
    have h2 : Real.sqrt 3 ≤ 2 := by rw [Real.sqrt_le_iff] <;> norm_num
    have h3 : L_coarse * Real.sqrt 3 ≤ L_coarse * 2 := by gcongr
    have h4 : L_coarse ≤ 1 / 2 := by
      have h5 : L_coarse ≤ 1 / 10000 := hL_small
      exact h5.trans (by norm_num)
    calc L_coarse * Real.sqrt 3
      ≤ L_coarse * 2 := h3
    _ ≤ (1 / 2 : ℝ) * 2 := by gcongr
    _ = 1 := by ring
  have hL_small' : L_coarse ≤ 1 / 1000 := by
    have h : L_coarse ≤ 1 / 10000 := hL_small
    exact h.trans (by norm_num)

  have h_propertyThree_full :
      ∀ (j : Fin sticky.coarse.card) (p : Point3),
        p ∈ propP.propertyThree.carrier j →
          Kakeya.realRpowENN (↑coarseScale) (2 + 2 * epsilon₁) * ENNReal.ofReal tau ≤
            volume (propP.propertyThree.carrier j ∩ Metric.closedBall p tau) := by
    intro j p hp
    have h_eq1 : propP.propertyThree = propP.propertyOne := h_prop3_eq_prop1
    rw [h_eq1] at hp ⊢
    exact propP.propertyOne_full j p hp

  have heps₃_gt : 9 / 10 < epsilon₃ := by
    rw [heps₃_def, heps₁_def]
    linarith [hsigma_lt_one, hstickyLoss_pos]
  have heps₃_lt_one : epsilon₃ < 1 := by
    rw [heps₃_def]; linarith [heps₁_pos]
  have h_ax_condition : 4 * (6 * (↑coarseScale : ℝ))^2 ≤
      (3 / 4 : ℝ) * (Real.rpow (↑coarseScale) (1 - epsilon₃))^2 :=
    cordoba_ax_condition (↑coarseScale) epsilon₃ hcoarseScale_pos
      (by rw [hL_coarse_eq] at hL_small; exact hL_small)
      heps₃_gt heps₃_lt_one

  have hC_one : (1 : ENNReal) ≤ C := by
    rw [hC_eq, Kakeya.realRpowENN]
    have h2 : delta ^ outputLoss ≤ 1 := Real.rpow_le_one hdelta_pos.le hdelta_le_one (by linarith)
    have h3 : (1 : ℝ) ≤ delta ^ (-outputLoss) := by
      have h4 : delta ^ (-outputLoss) = (delta ^ outputLoss)⁻¹ := by
        rw [Real.rpow_neg hdelta_pos.le] <;> ring
      rw [h4]
      have h5 : 0 < delta ^ outputLoss := Real.rpow_pos_of_pos hdelta_pos _
      have h6 : (delta ^ outputLoss)⁻¹ ≥ 1 := by
        calc (delta ^ outputLoss)⁻¹
          ≥ (1 : ℝ)⁻¹ := by gcongr
        _ = 1 := by simp
      exact h6
    have h7 : (1 : ENNReal) = ENNReal.ofReal (1 : ℝ) := by simp
    rw [h7]
    exact ENNReal.ofReal_le_ofReal h3
  have hC_top : C ≠ ⊤ := by
    rw [hC_eq, Kakeya.realRpowENN]
    simp [ENNReal.ofReal_ne_top]

  let target : Set Point3 := sticky.refined.union ∩ Metric.closedBall q (Real.sqrt rho)
  have h_target_sub : target ⊆ sticky.croppedCoarseShading.union ∩ Metric.closedBall q (Real.sqrt rho) := by
    intro x hx
    exact ⟨hard_regime_high_case_refined_subset_coarse sticky hx.1, hx.2⟩

  have hW0_eq' : W0 = 40 * (↑coarseScale : ℝ) := by
    simp [W0, hL_coarse_eq] <;> ring
  have hVmin_def' : V_min = Real.rpow (↑coarseScale) (1 + 7 * epsilon₁ + epsilon₃) * tau^2 / 200 := by
    have h1 : L_coarse ^ (1 + 7 * epsilon₁ + epsilon₃) = Real.rpow (↑coarseScale) (1 + 7 * epsilon₁ + epsilon₃) := by
      rw [hL_coarse_eq] <;> rfl
    rw [hVmin_def, h1] <;> ring
  have htau_def' : tau = (↑coarseScale : ℝ) * Real.sqrt 3 := by
    rw [htau_def, hL_coarse_eq]
  have htau_le_20L' : tau ≤ 20 * (↑coarseScale : ℝ) := by
    rw [hL_coarse_eq] at htau_le_20L; exact htau_le_20L
  have hL_le_tau' : (↑coarseScale : ℝ) ≤ tau := by
    rw [hL_coarse_eq] at hL_le_tau; exact hL_le_tau
  have htau_sq' : tau ^ 2 ≤ 4 * (↑coarseScale : ℝ) := by
    rw [hL_coarse_eq] at htau_sq; exact htau_sq
  have htau_le_one' : tau ≤ 1 := htau_le_one
  have hL_small'' : (↑coarseScale : ℝ) ≤ 1 / 1000 := by
    rw [hL_coarse_eq] at hL_small'; exact hL_small'
  have hL_pos' : 0 < (↑coarseScale : ℝ) := by
    rw [hL_coarse_eq] at hL_coarse_pos; exact hL_coarse_pos
  have hL_le_L0_log' : (↑coarseScale : ℝ) ≤ L₀_log := by
    rw [hL_coarse_eq] at hL_coarse_le_L0_log; exact hL_coarse_le_L0_log
  exact high_case_cordoba_ad
    epsilon₁ epsilon₃ propP v hv_unit q hq_prop3
    S hS_eq hS_meas hS_sub_ball
    W0 V_min V_total hW0_pos hW0_eq' hVmin_pos hVmin_def' hV_total_pos hV_total
    htau_def' htau_pos htau_le_20L' hL_le_tau' htau_sq' htau_le_one' hL_small'' hL_pos'
    hsigma_pos hsigma_lt_one heps₁_pos heps₃_pos heps_sum
    L₀_log hL_le_L0_log' h_log_main
    h_propertyThree_full h_ax_condition
    target h_target_sub hsqrt_rho_le_4tau hrho_pos
    C hC_one hC_top h_arithmetic

end Kakeya.Assouad.PureWZ2
