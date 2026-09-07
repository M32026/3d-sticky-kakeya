import MyLeanRepo.Kakeya.Cinematic.Section5.CoarseFiberCarrierContainmentInputs

/-!
# Interval helpers for coarse-fiber carrier containment
-/

noncomputable section

open Set

namespace Kakeya.Cinematic

lemma fine_interval_length_le_sqrt_shading_mul_coarse
    {delta t Delta C_R C_shading : ℝ}
    (hC_shading : 1 ≤ C_shading)
    (hC_R : 1 ≤ C_R)
    (hdelta : 0 < delta)
    (hdelta_le_Delta : delta ≤ Delta)
    (hDelta_le_t : Delta ≤ t)
    (U : CurvilinearRectangle
      (C_shading * delta) (C_R * t * Delta / delta))
    (parent : CurvilinearRectangle Delta (C_R * t)) :
    U.interval.length ≤
      Real.sqrt C_shading * parent.interval.length := by
  have hC_R_pos : 0 < C_R := by linarith
  have ht_pos : 0 < t := by linarith
  have hDelta_pos : 0 < Delta := by linarith
  have hC_shading_nonneg : 0 ≤ C_shading := by linarith
  have hparent_ratio_nonneg : 0 ≤ Delta / (C_R * t) := by positivity
  have hratio :
      C_shading * delta / (C_R * t * Delta / delta) ≤
        C_shading * (Delta / (C_R * t)) := by
    have hleft :
        C_shading * delta / (C_R * t * Delta / delta) =
          C_shading * (delta / Delta) ^ 2 *
            (Delta / (C_R * t)) := by
      field_simp [hdelta.ne', hDelta_pos.ne', hC_R_pos.ne', ht_pos.ne']
      <;> ring
    rw [hleft]
    have hdelta_ratio : delta / Delta ≤ 1 := by
      exact (div_le_one hDelta_pos).mpr hdelta_le_Delta
    have hdelta_ratio_nonneg : 0 ≤ delta / Delta := by positivity
    have hsquare : (delta / Delta) ^ 2 ≤ 1 := by nlinarith
    have hscaled :
        C_shading * (delta / Delta) ^ 2 ≤ C_shading := by
      nlinarith
    exact mul_le_mul_of_nonneg_right hscaled hparent_ratio_nonneg
  rw [U.interval_length, parent.interval_length]
  calc
    Real.sqrt
        (C_shading * delta / (C_R * t * Delta / delta))
        ≤ Real.sqrt (C_shading * (Delta / (C_R * t))) :=
      Real.sqrt_le_sqrt hratio
    _ = Real.sqrt C_shading *
        Real.sqrt (Delta / (C_R * t)) := by
      rw [Real.sqrt_mul hC_shading_nonneg]

lemma same_midpoint_shorter_interval_subset
    (I J : ParameterInterval)
    (hmid : I.midpoint = J.midpoint)
    (hlen : I.length ≤ J.length) :
    Set.Icc I.left I.right ⊆ Set.Icc J.left J.right := by
  intro x hx
  have hleft : J.left ≤ I.left := by
    have hI : I.left = I.midpoint - I.length / 2 := by
      simp [ParameterInterval.midpoint, ParameterInterval.length] <;> ring
    have hJ : J.left = J.midpoint - J.length / 2 := by
      simp [ParameterInterval.midpoint, ParameterInterval.length] <;> ring
    rw [hI, hJ, hmid]
    linarith
  have hright : I.right ≤ J.right := by
    have hI : I.right = I.midpoint + I.length / 2 := by
      simp [ParameterInterval.midpoint, ParameterInterval.length] <;> ring
    have hJ : J.right = J.midpoint + J.length / 2 := by
      simp [ParameterInterval.midpoint, ParameterInterval.length] <;> ring
    rw [hI, hJ, hmid]
    linarith
  exact ⟨hleft.trans hx.1, hx.2.trans hright⟩

end Kakeya.Cinematic
