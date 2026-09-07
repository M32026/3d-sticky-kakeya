import MyLeanRepo.Kakeya.Assouad.LargeSlope.GlobalADVolumeBound

/-!
# Local AD measure bound for WZ1 Lemma 23 Step 1

The full-grain slice in Lemma 23 projects into one interval.  Its projection
is a subset of the exact-slice global AD set, so the local covering clause
gives a quantitative one-dimensional measure upper bound.
-/

namespace Kakeya.Assouad

open MeasureTheory

/--
A subset of one radius-`r` window in an AD set has measure at most its local
covering number times the diameter `2 * rho` of one covering ball.
-/
theorem IsADSet1.volume_subset_closedBall_le
    {A P : Set ℝ} {rho alpha : ℝ} {C : ENNReal}
    (hAD : IsADSet1 A rho alpha C)
    (hC : C ≠ ⊤)
    {center radius : ℝ}
    (hrho_radius : rho ≤ radius)
    (hradius_one : radius ≤ 1)
    (hP : P ⊆ A ∩ Metric.closedBall center radius) :
    volume P ≤
      (C * Kakeya.realRpowENN (radius / rho) alpha) *
        ENNReal.ofReal (2 * rho) := by
  have hrho : 0 < rho := hAD.1
  have hrho_one : rho ≤ 1 :=
    hrho_radius.trans hradius_one
  have hcoverAD :
      (↑(Metric.externalCoveringNumber
        ⟨rho, hrho.le⟩
        (A ∩ Metric.closedBall center radius)) : ENNReal) ≤
          C * Kakeya.realRpowENN (radius / rho) alpha :=
    hAD.2.2.2.2.2 rho hrho.le le_rfl hrho_one
      center radius hrho_radius hradius_one
  have hcoverMono :
      Metric.externalCoveringNumber
          ⟨rho, hrho.le⟩ P ≤
        Metric.externalCoveringNumber
          ⟨rho, hrho.le⟩
          (A ∩ Metric.closedBall center radius) :=
    Metric.externalCoveringNumber_mono_set hP
  have hcover :
      (↑(Metric.externalCoveringNumber
        ⟨rho, hrho.le⟩ P) : ENNReal) ≤
          C * Kakeya.realRpowENN (radius / rho) alpha := by
    have hcoverMonoENN :
        (↑(Metric.externalCoveringNumber
          ⟨rho, hrho.le⟩ P) : ENNReal) ≤
        (↑(Metric.externalCoveringNumber
          ⟨rho, hrho.le⟩
          (A ∩ Metric.closedBall center radius)) : ENNReal) := by
      exact_mod_cast hcoverMono
    exact hcoverMonoENN.trans hcoverAD
  have hboundFinite :
      C * Kakeya.realRpowENN (radius / rho) alpha ≠ ⊤ :=
    ENNReal.mul_ne_top hC
      (by simp [Kakeya.realRpowENN, ENNReal.ofReal_ne_top])
  exact
    volume_le_externalCoveringNumber_mul_two_delta
      hrho hboundFinite hcover

/--
If the projected full-grain slice occupies a fixed fraction of its carrier
interval, that fullness is bounded by the exact local AD estimate.
-/
theorem wz1_lemma23_projection_fullness_ad_bound
    {A P : Set ℝ} {rho sigma : ℝ} {C density : ENNReal}
    (hAD : IsADSet1 A rho (1 - sigma) C)
    (hC : C ≠ ⊤)
    {center radius : ℝ}
    (hrho_radius : rho ≤ radius)
    (hradius_one : radius ≤ 1)
    (hP : P ⊆ A ∩ Metric.closedBall center radius)
    (hfull :
      density * ENNReal.ofReal (2 * radius) ≤ volume P) :
    density * ENNReal.ofReal (2 * radius) ≤
      (C * Kakeya.realRpowENN
        (radius / rho) (1 - sigma)) *
          ENNReal.ofReal (2 * rho) := by
  exact hfull.trans
    (hAD.volume_subset_closedBall_le
      hC hrho_radius hradius_one hP)

end Kakeya.Assouad
