import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.SaturationPlaneMapExtension
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.PaperIsotropicLocalAD
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.CombinedAffineLocalAD

/-!
# Exact plane maps after the final isotropic normalization

The inverse-transpose normal of an isotropic dilation is a positive scalar
multiple of the old normal, so normalization leaves the unit normal unchanged.
Only the metric on its domain changes: dilating by `scale` divides the
Lipschitz constant by `scale`.  This is the precise normalization step needed
before extending an exact-image plane field to a cubical saturation.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

/-- The canonical preimage of a point in a positive isotropic image. -/
def pureWZ2IsotropicExactSourcePoint
    {exactImage : Set Point3} (center : Point3) {scale : ℝ}
    (hscale : 0 < scale)
    (target : {point : Point3 //
      point ∈ pureWZ2IsotropicMap center scale '' exactImage}) :
    {point : Point3 // point ∈ exactImage} :=
  ⟨pureWZ2IsotropicInverse center scale target, by
    rcases target.property with ⟨source, hsource, heq⟩
    have hinverse : pureWZ2IsotropicInverse center scale target = source := by
      rw [← heq, pureWZ2IsotropicInverse_map center hscale]
    rwa [hinverse]⟩

@[simp] theorem pureWZ2IsotropicMap_exactSourcePoint
    {exactImage : Set Point3} (center : Point3) {scale : ℝ}
    (hscale : 0 < scale)
    (target : {point : Point3 //
      point ∈ pureWZ2IsotropicMap center scale '' exactImage}) :
    pureWZ2IsotropicMap center scale
        (pureWZ2IsotropicExactSourcePoint center hscale target) = target := by
  exact pureWZ2IsotropicMap_inverse center hscale target

/-- Pullback distances under a positive isotropic dilation are divided by
the dilation factor. -/
theorem pureWZ2IsotropicExactSourcePoint_dist
    {exactImage : Set Point3} (center : Point3) {scale : ℝ}
    (hscale : 0 < scale)
    (first second : {point : Point3 //
      point ∈ pureWZ2IsotropicMap center scale '' exactImage}) :
    dist (pureWZ2IsotropicExactSourcePoint center hscale first)
        (pureWZ2IsotropicExactSourcePoint center hscale second) =
      dist (first : Point3) (second : Point3) / scale := by
  simp only [pureWZ2IsotropicExactSourcePoint, Subtype.dist_eq,
    pureWZ2IsotropicInverse, dist_eq_norm]
  have hdiff :
      center + scale⁻¹ • (first : Point3) -
          (center + scale⁻¹ • (second : Point3)) =
        scale⁻¹ • ((first : Point3) - (second : Point3)) := by
    rw [smul_sub]
    module
  rw [hdiff, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_pos hscale, div_eq_mul_inv]
  ring

/-- Pull a unit normal field forward through a positive isotropic dilation.
The values do not change; only their base points do. -/
def pureWZ2IsotropicExactPlaneMap
    {exactImage : Set Point3}
    (rawNormal : {point : Point3 // point ∈ exactImage} → Point3)
    (center : Point3) {scale : ℝ} (hscale : 0 < scale)
    (target : {point : Point3 //
      point ∈ pureWZ2IsotropicMap center scale '' exactImage}) : Point3 :=
  rawNormal (pureWZ2IsotropicExactSourcePoint center hscale target)

theorem pureWZ2IsotropicExactPlaneMap_unit
    {exactImage : Set Point3}
    (rawNormal : {point : Point3 // point ∈ exactImage} → Point3)
    (hrawUnit : ∀ point, ‖rawNormal point‖ = 1)
    (center : Point3) {scale : ℝ} (hscale : 0 < scale)
    (target : {point : Point3 //
      point ∈ pureWZ2IsotropicMap center scale '' exactImage}) :
    ‖pureWZ2IsotropicExactPlaneMap rawNormal center hscale target‖ = 1 := by
  exact hrawUnit (pureWZ2IsotropicExactSourcePoint center hscale target)

/-- A dilation by `scale` turns a `K`-Lipschitz exact normal into any
`targetK`-Lipschitz field satisfying `K ≤ targetK * scale`. -/
theorem pureWZ2IsotropicExactPlaneMap_lipschitz
    {exactImage : Set Point3}
    {rawNormal : {point : Point3 // point ∈ exactImage} → Point3}
    {K targetK : NNReal}
    (hrawLipschitz : LipschitzWith K rawNormal)
    (center : Point3) {scale : ℝ} (hscale : 0 < scale)
    (hK : (K : ℝ) ≤ (targetK : ℝ) * scale) :
    LipschitzWith targetK
      (pureWZ2IsotropicExactPlaneMap rawNormal center hscale) := by
  apply LipschitzWith.of_dist_le_mul
  intro first second
  have hsource := hrawLipschitz.dist_le_mul
    (pureWZ2IsotropicExactSourcePoint center hscale first)
    (pureWZ2IsotropicExactSourcePoint center hscale second)
  rw [pureWZ2IsotropicExactSourcePoint_dist center hscale] at hsource
  calc
    dist (pureWZ2IsotropicExactPlaneMap rawNormal center hscale first)
        (pureWZ2IsotropicExactPlaneMap rawNormal center hscale second)
        ≤ (K : ℝ) *
            (dist (first : Point3) (second : Point3) / scale) := hsource
    _ ≤ ((targetK : ℝ) * scale) *
          (dist (first : Point3) (second : Point3) / scale) := by
        gcongr
    _ = (targetK : ℝ) * dist first second := by
        rw [Subtype.dist_eq]
        field_simp [hscale.ne']

/-- The exact-image local AD estimate after the final isotropic dilation.
Unlike the older ball-only wrapper, the target subset may be any subset of
the displayed ball.  This is what the subsequent cubical saturation uses
with radius `sqrt targetRho + 2 * witnessRadius`. -/
theorem PureWZ2AnisotropicExactPlaneMapData.isotropicExact_local_ad
    {sourceDelta targetDelta c d m sigma : ℝ}
    {C : ENNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {anisotropicCenter : Point3}
    {hcd : c < d} {hm : 0 < m}
    {raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g anisotropicCenter hcd hm}
    {sourceLocal : PureWZ2LocalGrainData sourceShading sigma C}
    (exact : PureWZ2AnisotropicExactPlaneMapData raw sourceLocal)
    (isotropicCenter : Point3) {scale sourceRho finalRho radius : ℝ}
    (hscale : 0 < scale)
    (target : {point : Point3 //
      point ∈ pureWZ2IsotropicMap isotropicCenter scale ''
        raw.exactShading.union})
    (targetSet : Set Point3)
    (htargetImage : targetSet ⊆
      pureWZ2IsotropicMap isotropicCenter scale '' raw.exactShading.union)
    (htargetBall : targetSet ⊆
      Metric.closedBall (target : Point3) radius)
    (hsourceRho : sourceDelta ≤ sourceRho)
    (hsourceRhoOne : sourceRho ≤ 1)
    (hball :
      ‖(anisotropicRescalingLinearEquiv g c d m hcd hm).symm
          |>.toContinuousLinearEquiv.toContinuousLinearMap‖ *
          (radius / scale) ≤ Real.sqrt sourceRho)
    (hbase :
      (scale /
          ‖dPhiInvT g c d m
            (sourceLocal.planeMap
              (raw.exactSourcePoint
                (pureWZ2IsotropicExactSourcePoint
                  isotropicCenter hscale target)))‖) *
        sourceRho ≤ finalRho)
    (hfinalRho : 0 < finalRho) :
    PureWZ2PaperADSet1
      (scalarProjection
        (pureWZ2IsotropicExactPlaneMap exact.planeMap
          isotropicCenter hscale target) targetSet)
      finalRho (1 - sigma) C := by
  let exactPoint :=
    pureWZ2IsotropicExactSourcePoint isotropicCenter hscale target
  let sourcePoint := raw.exactSourcePoint exactPoint
  have htargetPoint : (target : Point3) =
      pureWZ2IsotropicMap isotropicCenter scale
        (anisotropicCenteredRescalingMap g c d m anisotropicCenter
          sourcePoint) := by
    rw [raw.map_exactSourcePoint exactPoint]
    exact (pureWZ2IsotropicMap_exactSourcePoint
      isotropicCenter hscale target).symm
  have hcombined := pureWZ2_combined_affine_isotropic_local_ad_of_image_in_ball
    (sourceRho := sourceRho) (targetRho := finalRho)
    (targetRadius := radius) sourceLocal g hcd hm
      anisotropicCenter isotropicCenter hscale
      sourcePoint (target : Point3) htargetPoint targetSet
  have htargetCombined : targetSet ⊆
      (fun source => pureWZ2IsotropicMap isotropicCenter scale
        (anisotropicCenteredRescalingMap g c d m anisotropicCenter source)) ''
          sourceShading.union := by
    intro point hpoint
    rcases htargetImage hpoint with ⟨exactSource, hexactSource, rfl⟩
    rw [raw.exactShading_union] at hexactSource
    rcases hexactSource with ⟨source, hsource, rfl⟩
    exact ⟨source, hsource, rfl⟩
  have hresult := hcombined htargetCombined htargetBall hsourceRho
    hsourceRhoOne hball hbase hfinalRho
  rw [pureWZ2IsotropicExactPlaneMap, exact.planeMap_eq]
  exact hresult

/-- Directly combine isotropic normalization of the exact normal with the
ambient extension-and-renormalization theorem used for the final cubical
saturation. -/
theorem pureWZ2_extend_isotropic_exact_plane_map_to_saturation
    {exactImage target : Set Point3}
    {rawNormal : {point : Point3 // point ∈ exactImage} → Point3}
    {sourceK targetK : NNReal}
    (hrawLipschitz : LipschitzWith sourceK rawNormal)
    (hrawUnit : ∀ point, ‖rawNormal point‖ = 1)
    (center : Point3) {scale witnessRadius : ℝ}
    (hscale : 0 < scale)
    (hK : (sourceK : ℝ) ≤ (targetK : ℝ) * scale)
    (hwitnessRadius : 0 ≤ witnessRadius)
    (targetWitness : ∀ point : {point : Point3 // point ∈ target},
      ∃ source : {point : Point3 //
          point ∈ pureWZ2IsotropicMap center scale '' exactImage},
        dist (point : Point3) (source : Point3) ≤ witnessRadius)
    (hsmall :
      ((lipschitzExtensionConstant Point3 * targetK : NNReal) : ℝ) *
          witnessRadius ≤ 1 / 2)
    (hone :
      4 * ((lipschitzExtensionConstant Point3 * targetK : NNReal) : ℝ) ≤ 1) :
    Nonempty (PureWZ2SaturationPlaneMapData
      (pureWZ2IsotropicMap center scale '' exactImage) target
      (pureWZ2IsotropicExactPlaneMap rawNormal center hscale)
      witnessRadius
      (4 * ((lipschitzExtensionConstant Point3 * targetK : NNReal) : ℝ) *
        witnessRadius)) := by
  apply pureWZ2_extend_plane_map_to_saturation
    (pureWZ2IsotropicExactPlaneMap_lipschitz
      hrawLipschitz center hscale hK)
    (fun point => pureWZ2IsotropicExactPlaneMap_unit
      rawNormal hrawUnit center hscale point)
    hwitnessRadius targetWitness hsmall hone

/-- Assemble the final local-grain record after the combined affine and
isotropic map and the final cubical saturation.  The source radius may depend
on both the requested target radius and its distinguished saturation point;
this is exactly the flexibility needed to pay for anisotropic ball distortion
without asserting a false same-radius transport statement. -/
def PureWZ2AnisotropicExactPlaneMapData.toIsotropicSaturationLocalGrains
    {sourceDelta targetDelta finalDelta c d m sigma : ℝ}
    {C : ENNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {g : SlopeFunction} {anisotropicCenter : Point3}
    {hcd : c < d} {hm : 0 < m}
    {raw : PureWZ2AnisotropicPaperRetubingData
      (targetDelta := targetDelta) sourceFamily sourceShading
        g anisotropicCenter hcd hm}
    {sourceLocal : PureWZ2LocalGrainData sourceShading sigma C}
    (exact : PureWZ2AnisotropicExactPlaneMapData raw sourceLocal)
    (isotropicCenter : Point3) {scale witnessRadius error pointBound : ℝ}
    (hscale : 0 < scale)
    {targetFamily : Kakeya.Streamlined.TubeFamily finalDelta}
    (targetShading : WZ1PaperTubeShading targetFamily)
    (hfinalDeltaPos : 0 < finalDelta)
    (saturation : PureWZ2SaturationPlaneMapData
      (pureWZ2IsotropicMap isotropicCenter scale ''
        raw.exactShading.union)
      targetShading.union
      (pureWZ2IsotropicExactPlaneMap exact.planeMap
        isotropicCenter hscale) witnessRadius error)
    (sourceIndex : Fin targetFamily.card →
      Fin (anisotropicPaperTargetFamily sourceFamily g c d m
        anisotropicCenter targetDelta hcd hm).card)
    (hdirection : ∀ index, (targetFamily.tube index).direction =
      ((anisotropicPaperTargetFamily sourceFamily g c d m
        anisotropicCenter targetDelta hcd hm).tube
          (sourceIndex index)).direction)
    (htubeWitness : ∀ index point,
      ∀ hpoint : point ∈ targetShading.carrier index,
        ∃ source : {point : Point3 //
            point ∈ pureWZ2IsotropicMap isotropicCenter scale ''
              raw.exactShading.union},
          dist point (source : Point3) ≤ witnessRadius ∧
          (pureWZ2IsotropicExactSourcePoint isotropicCenter hscale source :
              Point3) ∈ raw.exactShading.carrier (sourceIndex index))
    (hwitnessRadius : 0 ≤ witnessRadius) (herror : 0 ≤ error)
    (hpointBound : 0 ≤ pointBound)
    (hexactBound : ∀ source : {point : Point3 //
      point ∈ pureWZ2IsotropicMap isotropicCenter scale ''
        raw.exactShading.union}, ‖(source : Point3)‖ ≤ pointBound)
    (hincidenceBudget : 3 * sourceDelta + error ≤ finalDelta)
    (hprojectionBudget : witnessRadius + pointBound * error ≤ finalDelta)
    (sourceRho : ∀ rho : ℝ, finalDelta ≤ rho → rho ≤ 1 →
      {point : Point3 // point ∈ targetShading.union} → ℝ)
    (hsourceRhoLower : ∀ rho hrhoLower hrhoOne point,
      sourceDelta ≤ sourceRho rho hrhoLower hrhoOne point)
    (hsourceRhoOne : ∀ rho hrhoLower hrhoOne point,
      sourceRho rho hrhoLower hrhoOne point ≤ 1)
    (hball : ∀ rho hrhoLower hrhoOne point,
      ‖(anisotropicRescalingLinearEquiv g c d m hcd hm).symm
          |>.toContinuousLinearEquiv.toContinuousLinearMap‖ *
          ((Real.sqrt rho + 2 * witnessRadius) / scale) ≤
        Real.sqrt (sourceRho rho hrhoLower hrhoOne point))
    (hbase : ∀ rho hrhoLower hrhoOne point,
      (scale /
          ‖dPhiInvT g c d m
            (sourceLocal.planeMap
              (raw.exactSourcePoint
                (pureWZ2IsotropicExactSourcePoint isotropicCenter hscale
                  (saturation.sourcePoint point))))‖) *
        sourceRho rho hrhoLower hrhoOne point ≤ rho) :
    PureWZ2LocalGrainData targetShading sigma (6 * C) := by
  apply saturation.toLocalGrainData
    (sourceDelta := 3 * sourceDelta)
    hwitnessRadius herror hpointBound hexactBound
  · intro index point hpoint
    rcases htubeWitness index point hpoint with
      ⟨source, hdist, hsourceCarrier⟩
    refine ⟨source, hdist, ?_⟩
    rw [hdirection index]
    change
      |inner ℝ
          ((anisotropicPaperTargetFamily sourceFamily g c d m
            anisotropicCenter targetDelta hcd hm).tube
              (sourceIndex index)).direction
          (exact.planeMap
            (pureWZ2IsotropicExactSourcePoint isotropicCenter hscale source))|
        ≤ 3 * sourceDelta
    exact exact.planeMap_incidence_source (sourceIndex index)
      (pureWZ2IsotropicExactSourcePoint isotropicCenter hscale source)
      hsourceCarrier
  · exact hincidenceBudget
  · exact hprojectionBudget
  · intro rho hrhoLower hrhoOne point
    let targetSet :=
      (pureWZ2IsotropicMap isotropicCenter scale ''
          raw.exactShading.union) ∩
        Metric.closedBall (saturation.sourcePoint point : Point3)
          (Real.sqrt rho + 2 * witnessRadius)
    apply exact.isotropicExact_local_ad isotropicCenter hscale
      (saturation.sourcePoint point) targetSet
    · exact Set.inter_subset_left
    · exact Set.inter_subset_right
    · exact hsourceRhoLower rho hrhoLower hrhoOne point
    · exact hsourceRhoOne rho hrhoLower hrhoOne point
    · exact hball rho hrhoLower hrhoOne point
    · exact hbase rho hrhoLower hrhoOne point
    · exact hfinalDeltaPos.trans_le hrhoLower

end Kakeya.Assouad

end
