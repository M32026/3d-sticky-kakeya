import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.AlignedCoarseScale
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.LossGapAbsorption
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.MultiScaleLocalAD
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.WeakenLoss
import MyLeanRepo.Kakeya.Assouad.ExtremalHelpers

/-!
# Aligned one-scale output at an arbitrary finite-grid query

The one-scale Property-(P) argument naturally returns local AD at the
critical scale `48 * rho ^ 2`, where `rho` is an integer multiple of the
fine scale.  This module transports that output to the original query scale.
The shading and plane map are unchanged, and the fixed factor from the scale
comparison is paid by a strict loss gap.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open Set ENNReal

/-- Restrict a one-scale local-grain output to a smaller query scale, while
weakening its extremality and CWA loss.  The displayed constant is exactly
the cost of `IsADSet1.weaken_scale`. -/
noncomputable def PureWZ2OneScaleLocalGrainData.refineQueryScale
    {delta sigma sourceLoss targetLoss criticalScale queryScale : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {planeMap : {point : Point3 // point ∈ source.union} → Point3}
    (data : PureWZ2OneScaleLocalGrainData
      (sigma := sigma) (outputLoss := sourceLoss) (rho := criticalScale)
      (Y := source) planeMap)
    (hsourceTarget : sourceLoss ≤ targetLoss)
    (hqueryPos : 0 < queryScale)
    (hqueryCritical : queryScale ≤ criticalScale)
    (hcriticalOne : criticalScale ≤ 1)
    (hcost :
      Kakeya.realRpowENN delta (-sourceLoss) *
          ENNReal.ofReal (10 * criticalScale / queryScale) ≤
        Kakeya.realRpowENN delta (-targetLoss)) :
    PureWZ2OneScaleLocalGrainData
      (sigma := sigma) (outputLoss := targetLoss) (rho := queryScale)
      (Y := source) planeMap where
  shading := data.shading
  subshading := data.subshading
  extremal := data.extremal.mono_loss hsourceTarget
  cwa := by
    apply weaken_convex_wolff_bound data.cwa
    exact realRpowENN_antitone data.extremal.delta_pos
      data.extremal.delta_le_one (by linarith)
  local_ad := by
    intro point hpoint
    let criticalSet : Set ℝ := scalarProjection
      (planeMap ⟨point, data.subshading.union hpoint⟩)
      (data.shading.union ∩
        Metric.closedBall point (Real.sqrt criticalScale))
    let querySet : Set ℝ := scalarProjection
      (planeMap ⟨point, data.subshading.union hpoint⟩)
      (data.shading.union ∩
        Metric.closedBall point (Real.sqrt queryScale))
    have querySubset : querySet ⊆ criticalSet := by
      rintro value ⟨other, hother, rfl⟩
      exact ⟨other, ⟨hother.1, hother.2.trans
        (Real.sqrt_le_sqrt hqueryCritical)⟩, rfl⟩
    have restricted : IsADSet1 querySet criticalScale (1 - sigma)
        (Kakeya.realRpowENN delta (-sourceLoss)) :=
      (data.local_ad point hpoint).mono querySubset
    exact (restricted.weaken_scale hqueryPos hqueryCritical
      hcriticalOne).mono_constant hcost

/-- If the critical scale is less than four times the query scale, the
internal scale-refinement cost is at most `40`. -/
lemma internal_aligned_refinement_cost_le_forty
    {criticalScale queryScale : ℝ} {constant : ENNReal}
    (hqueryPos : 0 < queryScale)
    (hratio : criticalScale < 4 * queryScale) :
    constant * ENNReal.ofReal (10 * criticalScale / queryScale) ≤
      40 * constant := by
  have ratioBound : 10 * criticalScale / queryScale ≤ 40 := by
    apply (div_le_iff₀ hqueryPos).2
    linarith
  have ofRealBound :
      ENNReal.ofReal (10 * criticalScale / queryScale) ≤ 40 := by
    simpa using ENNReal.ofReal_le_ofReal ratioBound
  calc
    constant * ENNReal.ofReal (10 * criticalScale / queryScale) ≤
        constant * 40 := by gcongr
    _ = 40 * constant := by ring

/-- Loss-gap form of `refineQueryScale` for a factor-four aligned critical
scale. -/
noncomputable def PureWZ2OneScaleLocalGrainData.refineAlignedQueryScale
    {delta sigma sourceLoss targetLoss criticalScale queryScale : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {planeMap : {point : Point3 // point ∈ source.union} → Point3}
    (data : PureWZ2OneScaleLocalGrainData
      (sigma := sigma) (outputLoss := sourceLoss) (rho := criticalScale)
      (Y := source) planeMap)
    (hqueryPos : 0 < queryScale)
    (hqueryCritical : queryScale ≤ criticalScale)
    (hratio : criticalScale < 4 * queryScale)
    (hcriticalOne : criticalScale ≤ 1)
    (hloss : sourceLoss < targetLoss)
    (hsmall : delta ≤ Real.rpow (40 : ℝ)
      (-1 / (targetLoss - sourceLoss))) :
    PureWZ2OneScaleLocalGrainData
      (sigma := sigma) (outputLoss := targetLoss) (rho := queryScale)
      (Y := source) planeMap := by
  apply PureWZ2OneScaleLocalGrainData.refineQueryScale data hloss.le
    hqueryPos hqueryCritical hcriticalOne
  exact (internal_aligned_refinement_cost_le_forty hqueryPos hratio).trans
    (by
      simpa using realRpowENN_neg_loss_gap_absorb
        (factor := (40 : ℝ)) (delta := delta)
        (sourceLoss := sourceLoss) (targetLoss := targetLoss)
        (by norm_num) hloss data.extremal.delta_pos hsmall)

/-- Specialize the preceding transport to the canonical integer-aligned
coarse scale.  The only geometric assumption is the lower endpoint
`48 * delta^2 ≤ queryScale`; `queryScale ≤ 1/4` guarantees that the critical
scale remains at most one. -/
noncomputable def PureWZ2OneScaleLocalGrainData.atAlignedCoarseQuery
    {delta sigma sourceLoss targetLoss queryScale : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {planeMap : {point : Point3 // point ∈ source.union} → Point3}
    (data : PureWZ2OneScaleLocalGrainData
      (sigma := sigma) (outputLoss := sourceLoss)
      (rho := 48 * alignedCoarseScale delta queryScale ^ 2)
      (Y := source) planeMap)
    (hqueryPos : 0 < queryScale)
    (hquerySmall : queryScale ≤ 1 / 4)
    (hgridFloor : 48 * delta ^ 2 ≤ queryScale)
    (hloss : sourceLoss < targetLoss)
    (hsmall : delta ≤ Real.rpow (40 : ℝ)
      (-1 / (targetLoss - sourceLoss))) :
    PureWZ2OneScaleLocalGrainData
      (sigma := sigma) (outputLoss := targetLoss) (rho := queryScale)
      (Y := source) planeMap := by
  have criticalPos :
      0 < 48 * alignedCoarseScale delta queryScale ^ 2 := by
    have alignedPos := alignedCoarseScale_pos
      data.extremal.delta_pos hqueryPos
    positivity
  have queryCritical :
      queryScale ≤ 48 * alignedCoarseScale delta queryScale ^ 2 :=
    query_le_fortyEight_mul_alignedCoarseScale_sq
      data.extremal.delta_pos hqueryPos
  have criticalRatio :
      48 * alignedCoarseScale delta queryScale ^ 2 <
        4 * queryScale :=
    fortyEight_mul_alignedCoarseScale_sq_lt_four_mul_query
      data.extremal.delta_pos hqueryPos hgridFloor
  have criticalOne :
      48 * alignedCoarseScale delta queryScale ^ 2 ≤ 1 := by
    exact criticalRatio.le.trans (by linarith)
  exact PureWZ2OneScaleLocalGrainData.refineAlignedQueryScale data
    hqueryPos queryCritical criticalRatio criticalOne hloss hsmall

end Kakeya.Assouad.PureWZ2

end
