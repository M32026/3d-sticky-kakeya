import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SmallDiameterAD
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.OneScaleLocalGrain
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.ADBridge
import Mathlib.Tactic

/-!
# Local AD from the diameter of a query ball

For a query ball of radius `sqrt rho`, every unit scalar projection has
diameter at most `2 * sqrt rho`.  The lemma below packages the exact endpoint
power inequality needed by `small_diameter_ad`.  Unlike the historical easy
regime, it does not require `sigma / 2 < outputLoss`; that inequality was only
one sufficient way to establish the endpoint uniformly down to `rho = delta`.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open Metric Set ENNReal

/-- A diameter-`2 sqrt rho` set has local AD once the endpoint power is
absorbed by the target constant. -/
lemma small_diameter_ad_of_endpoint_power
    {delta rho outputLoss sigma : ℝ}
    {E : Set ℝ}
    (hdelta_pos : 0 < delta)
    (hdelta_le_one : delta ≤ 1)
    (hrho_pos : 0 < rho)
    (hrho_le_one : rho ≤ 1)
    (houtputLoss_pos : 0 < outputLoss)
    (hsigma_pos : 0 < sigma)
    (hsigma_lt_one : sigma < 1)
    (hE_diam : ∀ x y, x ∈ E → y ∈ E →
      |x - y| ≤ 2 * Real.sqrt rho)
    (hendpoint :
      3 * (2 / Real.sqrt rho) ^ sigma ≤ delta ^ (-outputLoss)) :
    PureWZ2PaperADSet1 E rho (1 - sigma)
      (Kakeya.realRpowENN delta (-outputLoss)) := by
  let x : ℝ := 2 / Real.sqrt rho
  have hsqrt_pos : 0 < Real.sqrt rho := Real.sqrt_pos.mpr hrho_pos
  have hsqrt_le_one : Real.sqrt rho ≤ 1 := by
    rw [Real.sqrt_le_one]
    linarith
  have hx_one : 1 ≤ x := by
    dsimp only [x]
    calc
      1 = Real.sqrt rho / Real.sqrt rho := by
        field_simp [hsqrt_pos.ne']
      _ ≤ 2 / Real.sqrt rho := by gcongr <;> linarith
  have hx_pos : 0 < x := lt_of_lt_of_le (by norm_num) hx_one
  have hx_sigma_one : 1 ≤ x ^ sigma :=
    Real.one_le_rpow hx_one hsigma_pos.le
  have hC_real : (3 : ℝ) ≤ delta ^ (-outputLoss) := by
    have hthree : (3 : ℝ) ≤ 3 * x ^ sigma := by nlinarith
    exact hthree.trans (by simpa [x] using hendpoint)
  have hC_ge : (3 : ENNReal) ≤
      Kakeya.realRpowENN delta (-outputLoss) := by
    simpa [Kakeya.realRpowENN] using
      ENNReal.ofReal_le_ofReal hC_real
  have hpower_product :
      x ^ sigma * x ^ (1 - sigma) = x := by
    calc
      x ^ sigma * x ^ (1 - sigma) =
          x ^ (sigma + (1 - sigma)) := by
            rw [← Real.rpow_add hx_pos]
      _ = x := by simp
  have htarget :
      3 * x ≤ delta ^ (-outputLoss) * x ^ (1 - sigma) := by
    have hmul := mul_le_mul_of_nonneg_right
      (show 3 * x ^ sigma ≤ delta ^ (-outputLoss) by
        simpa [x] using hendpoint)
      (Real.rpow_nonneg hx_pos.le (1 - sigma))
    calc
      3 * x = (3 * x ^ sigma) * x ^ (1 - sigma) := by
        rw [mul_assoc, hpower_product]
      _ ≤ delta ^ (-outputLoss) * x ^ (1 - sigma) := hmul
  have hsum : x + 2 ≤ 3 * x := by linarith
  have hendpoint_real :
      2 / Real.sqrt rho + 2 ≤
        delta ^ (-outputLoss) *
          (2 / Real.sqrt rho) ^ (1 - sigma) := by
    simpa [x] using hsum.trans htarget
  have hendpoint_enn :
      ENNReal.ofReal (2 / Real.sqrt rho + 2) ≤
        Kakeya.realRpowENN delta (-outputLoss) *
          Kakeya.realRpowENN (2 / Real.sqrt rho) (1 - sigma) := by
    have hdelta_nonneg : 0 ≤ delta ^ (-outputLoss) := by positivity
    have hpow_nonneg :
        0 ≤ (2 / Real.sqrt rho) ^ (1 - sigma) := by positivity
    have hmul :
        Kakeya.realRpowENN delta (-outputLoss) *
            Kakeya.realRpowENN (2 / Real.sqrt rho) (1 - sigma) =
          ENNReal.ofReal
            (delta ^ (-outputLoss) *
              (2 / Real.sqrt rho) ^ (1 - sigma)) := by
      simp only [Kakeya.realRpowENN]
      exact (ENNReal.ofReal_mul hdelta_nonneg).symm
    rw [hmul]
    exact ENNReal.ofReal_le_ofReal hendpoint_real
  exact small_diameter_ad hdelta_pos hdelta_le_one hrho_pos hrho_le_one
    houtputLoss_pos hsigma_pos hsigma_lt_one hE_diam
    (Kakeya.realRpowENN delta (-outputLoss)) rfl hC_ge hendpoint_enn
    pure_wz2_paper_ad_bridge

/-- Apply the endpoint-power criterion to the scalar projection of an arbitrary
subset of one query ball. -/
lemma ball_projection_large_scale_ad
    {delta rho outputLoss sigma : ℝ}
    {v q : Point3} {S : Set Point3}
    (hdelta_pos : 0 < delta)
    (hdelta_le_one : delta ≤ 1)
    (hrho_pos : 0 < rho)
    (hrho_le_one : rho ≤ 1)
    (houtputLoss_pos : 0 < outputLoss)
    (hsigma_pos : 0 < sigma)
    (hsigma_lt_one : sigma < 1)
    (hv_unit : ‖v‖ = 1)
    (hS : S ⊆ Metric.closedBall q (Real.sqrt rho))
    (hendpoint :
      3 * (2 / Real.sqrt rho) ^ sigma ≤ delta ^ (-outputLoss)) :
    PureWZ2PaperADSet1 (scalarProjection v S) rho (1 - sigma)
      (Kakeya.realRpowENN delta (-outputLoss)) := by
  exact small_diameter_ad_of_endpoint_power
    hdelta_pos hdelta_le_one hrho_pos hrho_le_one
    houtputLoss_pos hsigma_pos hsigma_lt_one
    (projection_diameter_bound hrho_pos hv_unit hS) hendpoint

end Kakeya.Assouad.PureWZ2

end
