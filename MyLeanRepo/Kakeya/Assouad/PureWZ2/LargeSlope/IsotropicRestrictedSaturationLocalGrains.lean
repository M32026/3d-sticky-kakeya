import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.IsotropicExactPlaneMap

/-!
# Local grains from a restricted exact image under isotropic saturation

This wrapper separates the geometric restriction of an exact normal field
from the subsequent Lipschitz extension to a cubically saturated target.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

/-- Restrict an exact unit normal field to a measurable/geometric subregion. -/
def pureWZ2RestrictedExactNormal
    {exactAmbient exactRestricted : Set Point3}
    (rawNormal : {point : Point3 // point ∈ exactAmbient} → Point3)
    (hsub : exactRestricted ⊆ exactAmbient) :
    {point : Point3 // point ∈ exactRestricted} → Point3 :=
  fun point => rawNormal ⟨point, hsub point.property⟩

theorem pureWZ2RestrictedExactNormal_lipschitz
    {exactAmbient exactRestricted : Set Point3}
    {rawNormal : {point : Point3 // point ∈ exactAmbient} → Point3}
    {K : NNReal}
    (hraw : LipschitzWith K rawNormal)
    (hsub : exactRestricted ⊆ exactAmbient) :
    LipschitzWith K (pureWZ2RestrictedExactNormal rawNormal hsub) := by
  intro first second
  simpa [pureWZ2RestrictedExactNormal, Subtype.edist_eq] using
    hraw ⟨first, hsub first.property⟩ ⟨second, hsub second.property⟩

theorem pureWZ2RestrictedExactNormal_unit
    {exactAmbient exactRestricted : Set Point3}
    {rawNormal : {point : Point3 // point ∈ exactAmbient} → Point3}
    (hraw : ∀ point, ‖rawNormal point‖ = 1)
    (hsub : exactRestricted ⊆ exactAmbient)
    (point : {point : Point3 // point ∈ exactRestricted}) :
    ‖pureWZ2RestrictedExactNormal rawNormal hsub point‖ = 1 :=
  hraw ⟨point, hsub point.property⟩

/-- Extend a restricted exact isotropic normal to a final cubical shading and
package the resulting one-Lipschitz local-grain field. -/
theorem pureWZ2_restricted_isotropic_saturation_local_grains
    {delta sourceIncidence sigma scale witnessRadius error pointBound : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    {exactAmbient exactRestricted : Set Point3}
    {rawNormal : {point : Point3 // point ∈ exactAmbient} → Point3}
    {K targetK : NNReal} {C : ENNReal}
    (hsub : exactRestricted ⊆ exactAmbient)
    (hrawLipschitz : LipschitzWith K rawNormal)
    (hrawUnit : ∀ point, ‖rawNormal point‖ = 1)
    (center : Point3) (hscale : 0 < scale)
    (hK : (K : ℝ) ≤ (targetK : ℝ) * scale)
    (hwitnessRadius : 0 ≤ witnessRadius)
    (htargetWitness : ∀ point : {point : Point3 // point ∈ shading.union},
      ∃ source : {point : Point3 //
          point ∈ pureWZ2IsotropicMap center scale '' exactRestricted},
        dist (point : Point3) (source : Point3) ≤ witnessRadius)
    (hsmall :
      ((lipschitzExtensionConstant Point3 * targetK : NNReal) : ℝ) *
        witnessRadius ≤ 1 / 2)
    (hone :
      4 * ((lipschitzExtensionConstant Point3 * targetK : NNReal) : ℝ) ≤ 1)
    (herrorEq : error =
      4 * ((lipschitzExtensionConstant Point3 * targetK : NNReal) : ℝ) *
        witnessRadius)
    (hpointBound : 0 ≤ pointBound)
    (hexactBound : ∀ source : {point : Point3 //
      point ∈ pureWZ2IsotropicMap center scale '' exactRestricted},
      ‖(source : Point3)‖ ≤ pointBound)
    (hincidence : ∀ index point,
      ∀ _hpoint : point ∈ shading.carrier index,
        ∃ source : {point : Point3 //
            point ∈ pureWZ2IsotropicMap center scale '' exactRestricted},
          dist point (source : Point3) ≤ witnessRadius ∧
          |inner ℝ (family.tube index).direction
            (pureWZ2IsotropicExactPlaneMap
              (pureWZ2RestrictedExactNormal rawNormal hsub) center hscale
                source)| ≤ sourceIncidence)
    (hincidenceBudget : sourceIncidence + error ≤ delta)
    (hprojectionBudget : witnessRadius + pointBound * error ≤ 2 * delta)
    (hexactAD : ∀ rho : ℝ, delta ≤ rho → rho ≤ 1 →
      ∀ source : {point : Point3 //
        point ∈ pureWZ2IsotropicMap center scale '' exactRestricted},
        PureWZ2PaperADSet1
          (scalarProjection
            (pureWZ2IsotropicExactPlaneMap
              (pureWZ2RestrictedExactNormal rawNormal hsub) center hscale
                source)
            ((pureWZ2IsotropicMap center scale '' exactRestricted) ∩
              Metric.closedBall
                (source : Point3)
                (Real.sqrt rho + 2 * witnessRadius)))
          rho (1 - sigma) C) :
    Nonempty (PureWZ2LocalGrainData shading sigma (15 * C)) := by
  let restrictedNormal := pureWZ2RestrictedExactNormal rawNormal hsub
  rcases pureWZ2_extend_isotropic_exact_plane_map_to_saturation
      (pureWZ2RestrictedExactNormal_lipschitz hrawLipschitz hsub)
      (pureWZ2RestrictedExactNormal_unit hrawUnit hsub) center hscale hK
      hwitnessRadius htargetWitness hsmall hone with
    ⟨saturation⟩
  refine ⟨saturation.toLocalGrainDataTwo hwitnessRadius ?_ hpointBound
    hexactBound hincidence ?_ ?_ ?_⟩
  · positivity
  · rw [← herrorEq]
    exact hincidenceBudget
  · rw [← herrorEq]
    exact hprojectionBudget
  · intro rho hrhoLower hrhoOne point
    exact hexactAD rho hrhoLower hrhoOne (saturation.sourcePoint point)

/-- Specialize the restricted saturation wrapper to an actual anisotropic
exact-plane-map package.  All local AD estimates come from the same
inverse-transpose normal used for incidence. -/
theorem PureWZ2AnisotropicExactPlaneMapData.toRestrictedIsotropicLocalGrains
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
    {exactRestricted : Set Point3}
    (hsub : exactRestricted ⊆ raw.exactShading.union)
    (isotropicCenter : Point3) {scale witnessRadius error pointBound : ℝ}
    (hscale : 0 < scale)
    {targetFamily : Kakeya.Streamlined.TubeFamily finalDelta}
    (targetShading : WZ1PaperTubeShading targetFamily)
    (hfinalDeltaPos : 0 < finalDelta)
    {targetK : NNReal}
    (hK : (exact.K : ℝ) ≤ (targetK : ℝ) * scale)
    (hwitnessRadius : 0 ≤ witnessRadius)
    (htargetWitness : ∀ point : {point : Point3 // point ∈ targetShading.union},
      ∃ source : {point : Point3 //
          point ∈ pureWZ2IsotropicMap isotropicCenter scale '' exactRestricted},
        dist (point : Point3) (source : Point3) ≤ witnessRadius)
    (hsmall :
      ((lipschitzExtensionConstant Point3 * targetK : NNReal) : ℝ) *
        witnessRadius ≤ 1 / 2)
    (hone :
      4 * ((lipschitzExtensionConstant Point3 * targetK : NNReal) : ℝ) ≤ 1)
    (herrorEq : error =
      4 * ((lipschitzExtensionConstant Point3 * targetK : NNReal) : ℝ) *
        witnessRadius)
    (hpointBound : 0 ≤ pointBound)
    (hexactBound : ∀ source : {point : Point3 //
      point ∈ pureWZ2IsotropicMap isotropicCenter scale '' exactRestricted},
      ‖(source : Point3)‖ ≤ pointBound)
    (sourceIndex : Fin targetFamily.card → Fin
      (anisotropicPaperTargetFamily sourceFamily g c d m
        anisotropicCenter targetDelta hcd hm).card)
    (hdirection : ∀ index, (targetFamily.tube index).direction =
      ((anisotropicPaperTargetFamily sourceFamily g c d m
        anisotropicCenter targetDelta hcd hm).tube
          (sourceIndex index)).direction)
    (htubeWitness : ∀ index point,
      ∀ hpoint : point ∈ targetShading.carrier index,
        ∃ source : {point : Point3 //
            point ∈ pureWZ2IsotropicMap isotropicCenter scale ''
              exactRestricted},
          dist point (source : Point3) ≤ witnessRadius ∧
          (pureWZ2IsotropicInverse isotropicCenter scale source : Point3) ∈
            raw.exactShading.carrier (sourceIndex index))
    (hincidenceBudget : 3 * sourceDelta + error ≤ finalDelta)
    (hprojectionBudget : witnessRadius + pointBound * error ≤ 2 * finalDelta)
    (sourceRho : ∀ rho : ℝ, finalDelta ≤ rho → rho ≤ 1 → ℝ)
    (hsourceRhoLower : ∀ rho hrhoLower hrhoOne,
      sourceDelta ≤ sourceRho rho hrhoLower hrhoOne)
    (hsourceRhoOne : ∀ rho hrhoLower hrhoOne,
      sourceRho rho hrhoLower hrhoOne ≤ 1)
    (hball : ∀ rho hrhoLower hrhoOne,
      ‖(anisotropicRescalingLinearEquiv g c d m hcd hm).symm
          |>.toContinuousLinearEquiv.toContinuousLinearMap‖ *
          ((Real.sqrt rho + 2 * witnessRadius) / scale) ≤
        Real.sqrt (sourceRho rho hrhoLower hrhoOne))
    (hbase : ∀ rho hrhoLower hrhoOne,
      ∀ exactPoint : {point : Point3 //
        point ∈ pureWZ2IsotropicMap isotropicCenter scale '' exactRestricted},
      (scale /
          ‖dPhiInvT g c d m
            (sourceLocal.planeMap
              (raw.exactSourcePoint
                (pureWZ2IsotropicExactSourcePoint isotropicCenter hscale
                  ⟨exactPoint, Set.image_mono hsub exactPoint.property⟩)))‖) *
        sourceRho rho hrhoLower hrhoOne ≤ rho) :
    Nonempty (PureWZ2LocalGrainData targetShading sigma (15 * C)) := by
  apply pureWZ2_restricted_isotropic_saturation_local_grains targetShading
    hsub exact.planeMap_lipschitz exact.planeMap_unit isotropicCenter hscale hK
    hwitnessRadius htargetWitness hsmall hone herrorEq hpointBound hexactBound
  · intro index point hpoint
    rcases htubeWitness index point hpoint with
      ⟨source, hdist, hsourceCarrier⟩
    refine ⟨source, hdist, ?_⟩
    rw [hdirection index]
    exact exact.planeMap_incidence_source (sourceIndex index)
      (pureWZ2IsotropicInverse isotropicCenter scale source) hsourceCarrier
  · exact hincidenceBudget
  · exact hprojectionBudget
  · intro rho hrhoLower hrhoOne target
    let targetSet :=
      (pureWZ2IsotropicMap isotropicCenter scale '' exactRestricted) ∩
        Metric.closedBall (target : Point3)
          (Real.sqrt rho + 2 * witnessRadius)
    let ambientTarget : {point : Point3 // point ∈
        pureWZ2IsotropicMap isotropicCenter scale '' raw.exactShading.union} :=
      ⟨target, Set.image_mono hsub target.property⟩
    apply exact.isotropicExact_local_ad isotropicCenter hscale ambientTarget
      targetSet
    · exact Set.inter_subset_left.trans (Set.image_mono hsub)
    · exact Set.inter_subset_right
    · exact hsourceRhoLower rho hrhoLower hrhoOne
    · exact hsourceRhoOne rho hrhoLower hrhoOne
    · exact hball rho hrhoLower hrhoOne
    · exact hbase rho hrhoLower hrhoOne target
    · exact hfinalDeltaPos.trans_le hrhoLower

end Kakeya.Assouad

end
