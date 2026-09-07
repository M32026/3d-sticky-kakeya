import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12

/-!
# Closest point in a centered dilated tube

Extract a point on the centered `B`-extended axis segment from membership in
the centered `B`-dilated ordinary carrier.  This isolated lemma keeps the
complete-incidence overlap proof independent of unrelated large geometric
modules.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric

/--
If `point` lies in the centered `B`-dilation of a `rho`-tube, then it lies
within `B * rho` of the correspondingly centered `B`-extended axis segment.
-/
theorem pureWZ2_general_dilation_closest_point
    {rho B : ℝ}
    (hrho : 0 ≤ rho)
    (hB : 0 < B)
    (tube : Kakeya.DeltaTube rho)
    (point : Point3)
    (hpoint :
      point ∈ wz2PaperCenteredDilatedCarrier B tube) :
    ∃ parameter : ℝ,
      parameter ∈
          Set.Icc (1 / 2 - B / 2) (1 / 2 + B / 2) ∧
        dist point
            (tube.base + parameter • tube.direction) ≤
          B * rho := by
  let midpoint :=
    tube.base + (1 / 2 : ℝ) • tube.direction
  let homothety : Point3 → Point3 :=
    AffineMap.homothety midpoint B
  let axis :=
    (fun parameter : ℝ =>
      tube.base + parameter • tube.direction) ''
        Set.Icc (0 : ℝ) 1
  rcases hpoint with ⟨sourcePoint, hsourcePoint, rfl⟩
  have haxisNonempty : axis.Nonempty :=
    ⟨tube.base, ⟨0, by norm_num, by simp⟩⟩
  have hsourceDistance :
      Metric.infDist sourcePoint axis ≤ rho := by
    have hedistance :
        Metric.infEDist sourcePoint axis ≤
          ENNReal.ofReal rho :=
      Metric.mem_cthickening_iff.mp hsourcePoint
    change
      ENNReal.toReal (Metric.infEDist sourcePoint axis) ≤ rho
    exact
      ENNReal.toReal_le_of_le_ofReal hrho hedistance
  have haxisCompact : IsCompact axis := by
    apply IsCompact.image isCompact_Icc
    exact
      continuous_const.add
        (continuous_id.smul continuous_const)
  rcases
      haxisCompact.exists_infDist_eq_dist
        haxisNonempty sourcePoint with
    ⟨axisPoint, haxisPoint, hdistance⟩
  have hsourceAxis :
      dist sourcePoint axisPoint ≤ rho := by
    rw [← hdistance]
    exact hsourceDistance
  rcases haxisPoint with
    ⟨parameter, hparameter, rfl⟩
  let targetParameter :=
    B * parameter - B / 2 + 1 / 2
  have htargetRange :
      targetParameter ∈
        Set.Icc (1 / 2 - B / 2) (1 / 2 + B / 2) := by
    dsimp only [targetParameter]
    constructor <;> nlinarith [hparameter.1, hparameter.2]
  have hhomothety :
      ∀ source : Point3,
        homothety source =
          B • (source - midpoint) + midpoint := by
    intro source
    simpa [homothety, vadd_eq_add, vsub_eq_sub] using
      AffineMap.homothety_apply midpoint B source
  have haxisImage :
      homothety
          (tube.base + parameter • tube.direction) =
        tube.base +
          targetParameter • tube.direction := by
    rw [hhomothety]
    have haxisDifference :
        tube.base + parameter • tube.direction - midpoint =
          (parameter - 1 / 2 : ℝ) • tube.direction := by
      dsimp only [midpoint]
      module
    rw [haxisDifference, smul_smul]
    dsimp only [targetParameter, midpoint]
    module
  have hdistanceScaled :
      dist
          (homothety sourcePoint)
          (homothety
            (tube.base + parameter • tube.direction)) =
        B *
          dist sourcePoint
            (tube.base + parameter • tube.direction) := by
    rw [dist_eq_norm, hhomothety, hhomothety]
    have hdifference :
        (B • (sourcePoint - midpoint) + midpoint) -
            (B •
                (tube.base + parameter • tube.direction - midpoint) +
              midpoint) =
          B •
            (sourcePoint -
              (tube.base + parameter • tube.direction)) := by
      module
    rw [hdifference, norm_smul, Real.norm_eq_abs,
      abs_of_pos hB, ← dist_eq_norm]
  refine ⟨targetParameter, htargetRange, ?_⟩
  have hmidpoint :
      midpoint = wz2PaperTubeMidpoint tube := by
    rfl
  change
    dist
        (homothety sourcePoint)
        (tube.base + targetParameter • tube.direction) ≤
      B * rho
  rw [← haxisImage, hdistanceScaled]
  exact mul_le_mul_of_nonneg_left hsourceAxis hB.le

end Kakeya.Assouad

end
