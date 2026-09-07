import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CommonSpatialPropertyThreePullback
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.ADBridge
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.ExtremalCWATransfer
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.MultiScaleLocalAD

/-!
# One-scale output on the honest Property-P fine pullback

This module packages the structural part of the HIGH one-scale argument.  The
output shading is the common-spatial ambient lift of the genuine Property-P
fine pullback.  Its union is exactly the geometric pullback union, while all
source tube memberships are restored at surviving points.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set ENNReal

/-- A paper subshading relation gives the corresponding union inclusion. -/
lemma paperSubshading_union
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {selected source : WZ1PaperTubeShading family}
    (hsub : PaperIsSubshading selected source) :
    selected.union ⊆ source.union := by
  rintro point ⟨index, hpoint⟩
  exact ⟨index, hsub index hpoint⟩

/-- Assemble one complete one-scale local-grain output once the analytic AD
estimate has been proved on the honest common-spatial pullback.  Every loss is
explicit: `massLoss` pays the shading refinement, and `hslack` absorbs it into
the target loss exponent. -/
theorem propertyThreeCommonHull_one_scale_output
    {delta sigma stickyDataLoss stickyLoss targetLoss queryScale tau epsilon₁ epsilon₃ : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (planeMap : {point : Point3 // point ∈ sourceShading.union} → Point3)
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyDataLoss)
      sourceShading rho logExponent)
    (propP : PureWZ2PropertyPData
      (sigma := sigma)
      (coarseShading := sticky.croppedCoarseShading)
      (tau := tau)
      epsilon₁ epsilon₃)
    (hsourceCubical : WZ1PaperIsCubicalShading sourceShading)
    (scaleFactor : ℕ) (hscaleFactor : 0 < scaleFactor)
    (hrhoAligned : rho.1 = (scaleFactor : ℝ) * delta)
    (sourceExtremal :
      WZ2PaperCroppedIsExtremal
        sigma stickyLoss family sourceShading)
    (sourceCWA :
      WZ2PaperConvexWolffBound family
        (Kakeya.realRpowENN delta (-stickyLoss)))
    (massLoss : ENNReal)
    (hmassLossPos : 0 < massLoss)
    (hmassLossFinite : massLoss ≠ ⊤)
    (hmass : massLoss⁻¹ * sourceShading.mass ≤
      (ambientPropertyThreeCommonHull sticky propP.propertyThree).mass)
    (hloss : stickyLoss ≤ targetLoss)
    (hslack : massLoss * Kakeya.realRpowENN delta targetLoss ≤
      Kakeya.realRpowENN delta stickyLoss)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (htargetLoss : 0 < targetLoss)
    (hlocalAD : ∀ point : Point3,
      ∀ hpoint : point ∈
          (ambientPropertyThreeCommonHull sticky propP.propertyThree).union,
        IsADSet1
          (scalarProjection
            (planeMap ⟨point, paperSubshading_union
              (ambientPropertyThreeCommonHull_subshading
                sticky propP.propertyThree) hpoint⟩)
            ((ambientPropertyThreeCommonHull
                sticky propP.propertyThree).union ∩
              Metric.closedBall point (Real.sqrt queryScale)))
          queryScale (1 - sigma)
          (Kakeya.realRpowENN delta (-targetLoss))) :
    ∃ data : PureWZ2OneScaleLocalGrainData
        (sigma := sigma) (outputLoss := targetLoss)
        (rho := queryScale) (Y := sourceShading) planeMap,
      data.shading =
        ambientPropertyThreeCommonHull sticky propP.propertyThree := by
  let target := ambientPropertyThreeCommonHull sticky propP.propertyThree
  have hpullbackCubical : WZ1PaperIsCubicalShading
      (propertyThreeFinePullbackShading
        sticky.cover sticky.refined propP.propertyThree) :=
    propertyThreeFinePullbackShading_cubical
      sticky.cover sticky.refined propP.propertyThree
      sticky.refined_cubical scaleFactor hscaleFactor hrhoAligned
  have htargetCubical : WZ1PaperIsCubicalShading target :=
    ambientPropertyThreeCommonHull_cubical sticky propP.propertyThree
      hsourceCubical hpullbackCubical
  have htargetExtremal :
      WZ2PaperCroppedIsExtremal sigma targetLoss family target :=
    transfer_cropped_extremal_to_subshading massLoss
      hmassLossPos hmassLossFinite sourceExtremal
      (ambientPropertyThreeCommonHull_subshading sticky propP.propertyThree)
      hmass htargetCubical hloss hslack hdelta hdeltaOne htargetLoss
  have htargetCWA : WZ2PaperConvexWolffBound family
      (Kakeya.realRpowENN delta (-targetLoss)) :=
    transfer_cwa_to_subshading
      (_shading1 := sourceShading) (_shading2 := target)
      sourceCWA hloss hdelta hdeltaOne
  exact ⟨{
    shading := target
    subshading :=
      ambientPropertyThreeCommonHull_subshading sticky propP.propertyThree
    extremal := htargetExtremal
    cwa := htargetCWA
    local_ad := by
      intro point hpoint
      simpa [target] using hlocalAD point hpoint
  }, rfl⟩

/-- Paper-AD version of the one-scale assembler.  The factor `10` from the
paper/internal bridge is exposed as `hconstant`; it is never hidden in the
target loss. -/
theorem propertyThreeCommonHull_one_scale_output_of_paperAD
    {delta sigma stickyDataLoss stickyLoss targetLoss queryScale tau epsilon₁ epsilon₃ : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading family}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (planeMap : {point : Point3 // point ∈ sourceShading.union} → Point3)
    (hplaneUnit : ∀ point, ‖planeMap point‖ = 1)
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyDataLoss)
      sourceShading rho logExponent)
    (propP : PureWZ2PropertyPData
      (sigma := sigma)
      (coarseShading := sticky.croppedCoarseShading)
      (tau := tau) epsilon₁ epsilon₃)
    (hsourceCubical : WZ1PaperIsCubicalShading sourceShading)
    (scaleFactor : ℕ) (hscaleFactor : 0 < scaleFactor)
    (hrhoAligned : rho.1 = (scaleFactor : ℝ) * delta)
    (sourceExtremal :
      WZ2PaperCroppedIsExtremal
        sigma stickyLoss family sourceShading)
    (sourceCWA :
      WZ2PaperConvexWolffBound family
        (Kakeya.realRpowENN delta (-stickyLoss)))
    (massLoss paperConstant : ENNReal)
    (hmassLossPos : 0 < massLoss)
    (hmassLossFinite : massLoss ≠ ⊤)
    (hmass : massLoss⁻¹ * sourceShading.mass ≤
      (ambientPropertyThreeCommonHull sticky propP.propertyThree).mass)
    (hloss : stickyLoss ≤ targetLoss)
    (hslack : massLoss * Kakeya.realRpowENN delta targetLoss ≤
      Kakeya.realRpowENN delta stickyLoss)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (htargetLoss : 0 < targetLoss)
    (hpaperAD : ∀ point : Point3,
      ∀ hpoint : point ∈
          (ambientPropertyThreeCommonHull sticky propP.propertyThree).union,
        PureWZ2PaperADSet1
          (scalarProjection
            (planeMap ⟨point, paperSubshading_union
              (ambientPropertyThreeCommonHull_subshading
                sticky propP.propertyThree) hpoint⟩)
            ((ambientPropertyThreeCommonHull
                sticky propP.propertyThree).union ∩
              Metric.closedBall point (Real.sqrt queryScale)))
          queryScale (1 - sigma) paperConstant)
    (hconstant : 10 * paperConstant ≤
      Kakeya.realRpowENN delta (-targetLoss)) :
    ∃ data : PureWZ2OneScaleLocalGrainData
        (sigma := sigma) (outputLoss := targetLoss)
        (rho := queryScale) (Y := sourceShading) planeMap,
      data.shading =
        ambientPropertyThreeCommonHull sticky propP.propertyThree := by
  apply propertyThreeCommonHull_one_scale_output planeMap sticky propP
    hsourceCubical scaleFactor hscaleFactor hrhoAligned
    sourceExtremal sourceCWA massLoss hmassLossPos hmassLossFinite
    hmass hloss hslack hdelta hdeltaOne htargetLoss
  intro point hpoint
  let sourcePoint : {point : Point3 // point ∈ sourceShading.union} :=
    ⟨point, paperSubshading_union
      (ambientPropertyThreeCommonHull_subshading
        sticky propP.propertyThree) hpoint⟩
  let targetSet : Set ℝ := scalarProjection (planeMap sourcePoint)
    ((ambientPropertyThreeCommonHull sticky propP.propertyThree).union ∩
      Metric.closedBall point (Real.sqrt queryScale))
  have htargetSubset : targetSet ⊆
      scalarProjection (planeMap sourcePoint) sourceShading.union := by
    rintro value ⟨other, hother, rfl⟩
    exact ⟨other, paperSubshading_union
      (ambientPropertyThreeCommonHull_subshading
        sticky propP.propertyThree) hother.1, rfl⟩
  have hbounded : targetSet ⊆ Set.Icc (-4 : ℝ) 4 :=
    scalarProjection_bounded (hplaneUnit sourcePoint) targetSet htargetSubset
  have hinternal : IsADSet1 targetSet queryScale (1 - sigma)
      (10 * paperConstant) :=
    pure_wz2_paper_ad_bridge.1 targetSet queryScale (1 - sigma)
      paperConstant hbounded (hpaperAD point hpoint)
  have htargetTop : Kakeya.realRpowENN delta (-targetLoss) ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  exact hinternal.mono_constant hconstant

end Kakeya.Assouad.PureWZ2

end
