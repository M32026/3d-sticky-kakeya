import MyLeanRepo.Kakeya.Streamlined.RhoTubeMultiplicity.DilatedExactInducedThickenedFiberMass
import MyLeanRepo.Kakeya.Streamlined.RhoTubeMultiplicity.RollingBodyHalo
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.DilatedTubeContainment
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

noncomputable section

open Metric MeasureTheory Kakeya

namespace Kakeya.Streamlined

private lemma isCompact_extendedSegment
    {rho A : ℝ} (T : Kakeya.DeltaTube rho) :
    IsCompact (GeometricLemmas.extendedSegment A T) := by
  apply IsCompact.image
  · apply IsCompact.image
    · exact isCompact_Icc
    · exact continuous_const.add (continuous_id.smul continuous_const)
  · fun_prop

private lemma nonempty_extendedSegment
    {rho A : ℝ} (hA : 0 ≤ A) (T : Kakeya.DeltaTube rho) :
    (GeometricLemmas.extendedSegment A T).Nonempty := by
  have hmid :=
    GeometricLemmas.mem_extendedSegment_of_abs_le (T := T) hA
      (show |(0 : ℝ)| ≤ A / 2 by simp; linarith)
  exact ⟨GeometricLemmas.tubeMidpoint T, by simpa using hmid⟩

lemma dilatedTube_innerBall
    {rho A : ℝ} (hrho : 0 < rho) (hA : 1 ≤ A)
    (T : Kakeya.DeltaTube rho) (x : Point3)
    (hx : x ∈ dilatedTubeCarrier A T) :
    ∃ y : Point3, dist x y ≤ rho / 2 ∧
      Metric.closedBall y (rho / 2) ⊆
        dilatedTubeCarrier A T ∩ Metric.closedBall x rho := by
  let E := GeometricLemmas.extendedSegment A T
  have hA_pos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hE_compact : IsCompact E := isCompact_extendedSegment T
  have hE_nonempty : E.Nonempty := nonempty_extendedSegment hA_pos.le T
  have hx' : x ∈ Metric.cthickening (A * rho) E := by
    rw [← GeometricLemmas.dilatedTubeCarrier_eq_cthickening
      hA_pos hrho.le T]
    exact hx
  have h_inf_ed : Metric.infEDist x E ≤ ENNReal.ofReal (A * rho) :=
    (Metric.mem_cthickening_iff (δ := A * rho) (s := E)).mp hx'
  have h_inf_ne_top : Metric.infEDist x E ≠ ⊤ :=
    Metric.infEDist_ne_top hE_nonempty
  have h_inf : Metric.infDist x E ≤ A * rho := by
    have h1 : Metric.infDist x E =
        ENNReal.toReal (Metric.infEDist x E) := by
      rfl
    rw [h1]
    have h2 :
        ENNReal.toReal (Metric.infEDist x E) ≤
          ENNReal.toReal (ENNReal.ofReal (A * rho)) :=
      (ENNReal.toReal_le_toReal h_inf_ne_top (by simp)).mpr h_inf_ed
    rw [ENNReal.toReal_ofReal (mul_nonneg hA_pos.le hrho.le)] at h2
    exact h2
  rcases hE_compact.exists_infDist_eq_dist hE_nonempty x with
    ⟨p, hp, h_eqdist⟩
  have h_dist_xp : dist x p ≤ A * rho := by
    rw [← h_eqdist]
    exact h_inf
  let c : ℝ := 1 - 1 / (2 * A)
  let y : Point3 := p + c • (x - p)
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    have hden : 2 ≤ 2 * A := by nlinarith
    have hfrac : 1 / (2 * A) ≤ 1 := by
      exact (div_le_one (by positivity)).mpr (by nlinarith)
    linarith
  have h_one_sub_c : 1 - c = 1 / (2 * A) := by
    dsimp [c]
    ring
  have h_x_y : x - y = (1 / (2 * A)) • (x - p) := by
    rw [show 1 / (2 * A) = 1 - c by exact h_one_sub_c.symm]
    dsimp [y]
    module
  have h_y_p : y - p = c • (x - p) := by
    dsimp [y]
    module
  have hcoeff_nonneg : 0 ≤ 1 / (2 * A) := by positivity
  have h_dist_xy :
      dist x y = (1 / (2 * A)) * dist x p := by
    rw [dist_eq_norm, dist_eq_norm, h_x_y, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg hcoeff_nonneg]
  have h_dist_yp : dist y p = c * dist x p := by
    rw [dist_eq_norm, dist_eq_norm, h_y_p, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg hc_nonneg]
  have h_xy_le : dist x y ≤ rho / 2 := by
    rw [h_dist_xy]
    calc
      (1 / (2 * A)) * dist x p
          ≤ (1 / (2 * A)) * (A * rho) := by
            exact mul_le_mul_of_nonneg_left h_dist_xp hcoeff_nonneg
      _ = rho / 2 := by
        field_simp [hA_pos.ne']
  have h_yp_le : dist y p ≤ (A - 1 / 2) * rho := by
    rw [h_dist_yp]
    calc
      c * dist x p ≤ c * (A * rho) :=
        mul_le_mul_of_nonneg_left h_dist_xp hc_nonneg
      _ = (A - 1 / 2) * rho := by
        dsimp [c]
        field_simp [hA_pos.ne']
  refine ⟨y, h_xy_le, ?_⟩
  intro z hz
  have h_dist_zy : dist z y ≤ rho / 2 := Metric.mem_closedBall.mp hz
  have h_dist_zx : dist z x ≤ rho := by
    calc
      dist z x ≤ dist z y + dist y x := dist_triangle _ _ _
      _ = dist z y + dist x y := by rw [dist_comm y x]
      _ ≤ rho / 2 + rho / 2 := add_le_add h_dist_zy h_xy_le
      _ = rho := by ring
  have h_dist_zp : dist z p ≤ A * rho := by
    calc
      dist z p ≤ dist z y + dist y p := dist_triangle _ _ _
      _ ≤ rho / 2 + (A - 1 / 2) * rho :=
        add_le_add h_dist_zy h_yp_le
      _ = A * rho := by ring
  have hz_carrier : z ∈ dilatedTubeCarrier A T := by
    rw [GeometricLemmas.dilatedTubeCarrier_eq_cthickening
      hA_pos hrho.le T]
    exact Metric.mem_cthickening_of_dist_le z p (A * rho) E hp h_dist_zp
  exact ⟨hz_carrier, Metric.mem_closedBall.mpr h_dist_zx⟩

lemma dilated_tube_halo_volume_bound
    {rho A : ℝ} (hrho : 0 < rho) (hA : 1 ≤ A)
    (T : Kakeya.DeltaTube rho) (S : Set Point3)
    (hS : S ⊆ dilatedTubeCarrier A T) :
    volume (Metric.cthickening rho S) ≤
      1728 * volume
        (dilatedTubeCarrier A T ∩ Metric.cthickening rho S) := by
  have hA_pos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hK_closed : IsClosed (dilatedTubeCarrier A T) := by
    rw [GeometricLemmas.dilatedTubeCarrier_eq_cthickening
      hA_pos hrho.le T]
    exact Metric.isClosed_cthickening
  exact rolling_body_halo_volume_bound hrho
    (dilatedTubeCarrier A T) S hK_closed hS
    (fun x hx => dilatedTube_innerBall hrho hA T x hx)

theorem dilated_exact_induced_thickened_fiber_mass :
    DilatedExactInducedThickenedFiberMassStatement := by
  intro A hA rho hrho fine coarse P Y Z h_parents h_exact
  have h_main : ∀ j : Fin coarse.card,
      volume (Metric.cthickening rho (P.fiberShadedUnion Y j)) ≤
        1728 * volume (Z.carrier j) := by
    intro j
    rcases h_parents j with ⟨T, hT_carrier⟩
    let S := P.fiberShadedUnion Y j
    have hS_sub : S ⊆ dilatedTubeCarrier A T := by
      intro x hx
      rcases hx with ⟨i, hpi, hxi⟩
      have hcontained :
          (fine.body i).carrier ⊆
            (coarse.body (P.parent i)).carrier :=
        P.contained i
      rw [hpi] at hcontained
      rw [hT_carrier] at hcontained
      exact hcontained (Y.subset_body i hxi)
    have hZ_eq : Z.carrier j =
        dilatedTubeCarrier A T ∩
          Metric.cthickening rho S := by
      have h := h_exact j
      rw [hT_carrier] at h
      exact h
    have h_bound :=
      dilated_tube_halo_volume_bound hrho hA T S hS_sub
    rw [hZ_eq]
    exact h_bound
  calc
    (∑ j : Fin coarse.card,
        volume (Metric.cthickening rho (P.fiberShadedUnion Y j)))
        ≤ ∑ j : Fin coarse.card, (1728 * volume (Z.carrier j)) := by
          apply Finset.sum_le_sum
          intro i _
          exact h_main i
    _ = 1728 * Z.mass := by
      rw [Shading.mass]
      exact (Finset.mul_sum Finset.univ
        (fun j : Fin coarse.card => volume (Z.carrier j)) 1728).symm
    _ ≤ 4096 * Z.mass := by
      gcongr <;> norm_num

/-- Direct specialization to the canonical actual dilated parent family. -/
theorem dilated_exact_induced_thickened_fiber_mass_bodyFamily
    {A rho : ℝ} (hA : 1 ≤ A) (hrho : 0 < rho)
    {fine : BodyFamily} {coarse : TubeFamily rho}
    (P : Factoring fine (dilatedTubeBodyFamily A coarse))
    (Y : Shading fine)
    (Z : Shading (dilatedTubeBodyFamily A coarse))
    (h_exact : P.IsExactInducedShading Y Z rho) :
    (∑ j : Fin coarse.card,
        volume
          (Metric.cthickening rho
            (P.fiberShadedUnion Y j))) ≤
      4096 * Z.mass := by
  exact dilated_exact_induced_thickened_fiber_mass hA hrho P Y Z
    (fun j => ⟨coarse.tube j, rfl⟩) h_exact

end Kakeya.Streamlined
