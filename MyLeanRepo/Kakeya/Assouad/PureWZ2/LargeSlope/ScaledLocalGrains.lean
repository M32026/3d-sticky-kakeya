import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.PaperIsotropicLocalAD

/-!
# Power-Lipschitz local grains before the final Lemma-8 normalization

The affine map in WZ2 Proposition 6.5 need not preserve the unit Lipschitz
constant of the source plane map.  The paper first carries the resulting
power-sized Lipschitz constant through the affine change of coordinates and
then removes it by a mass-popular isotropic rescaling.  This module provides
the missing type-level boundary between those two steps.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

/-- Local-grain data with an explicit Lipschitz constant.  This is an
internal Lemma-8 object; the public Node-6 output still uses
`PureWZ2LocalGrainData`, whose Lipschitz constant is exactly one. -/
structure PureWZ2ScaledLocalGrainData
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (sigma : ℝ) (C : ENNReal) (K : NNReal) where
  planeMap : {point : Point3 // point ∈ shading.union} → Point3
  planeMap_lipschitz : LipschitzWith K planeMap
  planeMap_unit : ∀ point, ‖planeMap point‖ = 1
  planeMap_incidence :
    ∀ index point,
      ∀ hpoint : point ∈ shading.carrier index,
        |inner ℝ (family.tube index).direction
            (planeMap ⟨point, ⟨index, hpoint⟩⟩)| ≤ delta

/-- A unit-Lipschitz local-grain record is the special case `K = 1`. -/
def PureWZ2LocalGrainData.toScaled
    {delta sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {C : ENNReal}
    (data : PureWZ2LocalGrainData shading sigma C) :
    PureWZ2ScaledLocalGrainData shading sigma C 1 where
  planeMap := data.planeMap
  planeMap_lipschitz := data.planeMap_lipschitz
  planeMap_unit := data.planeMap_unit
  planeMap_incidence := data.planeMap_incidence

/-- The final isotropic dilation in paper Lemma 8 turns an explicit
`K`-Lipschitz intermediate plane map into the unit-Lipschitz output.
Every target point retains an exact source preimage; cubical-thickening
stability is a separate preceding obligation. -/
theorem PureWZ2ScaledLocalGrainData.isotropicNormalize
    {sourceDelta sigma scale : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {C : ENNReal} {K : NNReal}
    (sourceLocal : PureWZ2ScaledLocalGrainData sourceShading sigma C K)
    (center : Point3)
    (hsourceDelta : 0 < sourceDelta)
    (hscale : 1 ≤ scale)
    (hK : (K : ℝ) ≤ scale)
    {targetFamily : Kakeya.Streamlined.TubeFamily (scale * sourceDelta)}
    (targetShading : WZ1PaperTubeShading targetFamily)
    (sourceParent : Fin targetFamily.card → Fin sourceFamily.card)
    (hdirection : ∀ index, (targetFamily.tube index).direction =
      (sourceFamily.tube (sourceParent index)).direction)
    (hcarrier : ∀ index, targetShading.carrier index ⊆
      pureWZ2IsotropicMap center scale ''
        sourceShading.carrier (sourceParent index))
    (htargetAD :
      ∀ rho : ℝ, scale * sourceDelta ≤ rho → rho ≤ 1 →
        ∀ point : {point : Point3 // point ∈ targetShading.union},
          PureWZ2PaperADSet1
            (scalarProjection
              (sourceLocal.planeMap
                ⟨pureWZ2IsotropicInverse center scale point, by
                  rcases point.property with ⟨index, hpoint⟩
                  rcases hcarrier index hpoint with
                    ⟨source, hsource, heq⟩
                  have hinverse :
                      pureWZ2IsotropicInverse center scale point = source := by
                    rw [← heq, pureWZ2IsotropicInverse_map center
                      (lt_of_lt_of_le (by norm_num) hscale)]
                  rw [hinverse]
                  exact ⟨sourceParent index, hsource⟩⟩)
              (targetShading.union ∩
                Metric.closedBall (point : Point3) (Real.sqrt rho)))
            rho (1 - sigma) C) :
    Nonempty (PureWZ2LocalGrainData targetShading sigma C) := by
  have hscalePos : 0 < scale := lt_of_lt_of_le (by norm_num) hscale
  let inverse :
      {point : Point3 // point ∈ targetShading.union} →
        {point : Point3 // point ∈ sourceShading.union} := fun target =>
    ⟨pureWZ2IsotropicInverse center scale target, by
      rcases target.property with ⟨index, hpoint⟩
      rcases hcarrier index hpoint with ⟨source, hsource, heq⟩
      have hinverse : pureWZ2IsotropicInverse center scale target = source := by
        rw [← heq, pureWZ2IsotropicInverse_map center hscalePos]
      rw [hinverse]
      exact ⟨sourceParent index, hsource⟩⟩
  let targetPlaneMap :
      {point : Point3 // point ∈ targetShading.union} → Point3 :=
    fun target => sourceLocal.planeMap (inverse target)
  have hinverseDistance : ∀ first second,
      dist (inverse first) (inverse second) =
        dist (first : Point3) (second : Point3) / scale := by
    intro first second
    simp only [inverse, Subtype.dist_eq, pureWZ2IsotropicInverse, dist_eq_norm]
    have hdiff :
        center + scale⁻¹ • (first : Point3) -
            (center + scale⁻¹ • (second : Point3)) =
          scale⁻¹ • ((first : Point3) - (second : Point3)) := by
      rw [smul_sub]
      module
    rw [hdiff, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos hscalePos]
    rw [div_eq_mul_inv]
    ring
  have htargetLipschitz : LipschitzWith 1 targetPlaneMap := by
    apply LipschitzWith.of_dist_le_mul
    intro first second
    have hsource := sourceLocal.planeMap_lipschitz.dist_le_mul
      (inverse first) (inverse second)
    rw [hinverseDistance] at hsource
    have hnonneg : 0 ≤ dist (first : Point3) (second : Point3) :=
      dist_nonneg
    have hratio : (K : ℝ) *
        (dist (first : Point3) (second : Point3) / scale) ≤
        dist (first : Point3) (second : Point3) := by
      calc
        (K : ℝ) * (dist (first : Point3) (second : Point3) / scale)
            ≤ scale *
                (dist (first : Point3) (second : Point3) / scale) := by
              gcongr
        _ = dist (first : Point3) (second : Point3) := by
              field_simp [hscalePos.ne']
    have hreal : dist (targetPlaneMap first) (targetPlaneMap second) ≤
        dist (first : Point3) (second : Point3) :=
      hsource.trans hratio
    simpa only [NNReal.coe_one, one_mul, Subtype.dist_eq] using hreal
  have htargetUnit : ∀ target, ‖targetPlaneMap target‖ = 1 :=
    fun target => sourceLocal.planeMap_unit (inverse target)
  have htargetIncidence : ∀ index point,
      ∀ hpoint : point ∈ targetShading.carrier index,
        |inner ℝ (targetFamily.tube index).direction
          (targetPlaneMap ⟨point, ⟨index, hpoint⟩⟩)| ≤
            scale * sourceDelta := by
    intro index point hpoint
    rcases hcarrier index hpoint with ⟨source, hsource, heq⟩
    have hinverseEq :
        inverse ⟨point, ⟨index, hpoint⟩⟩ =
          ⟨source, ⟨sourceParent index, hsource⟩⟩ := by
      apply Subtype.ext
      change pureWZ2IsotropicInverse center scale point = source
      rw [← heq, pureWZ2IsotropicInverse_map center hscalePos]
    rw [hdirection index]
    change |inner ℝ (sourceFamily.tube (sourceParent index)).direction
      (sourceLocal.planeMap
        (inverse ⟨point, ⟨index, hpoint⟩⟩))| ≤ _
    rw [hinverseEq]
    exact (sourceLocal.planeMap_incidence
      (sourceParent index) source hsource).trans <| by
        calc
          sourceDelta = 1 * sourceDelta := by ring
          _ ≤ scale * sourceDelta := by gcongr
  have htargetSubset : targetShading.union ⊆
      pureWZ2IsotropicMap center scale '' sourceShading.union := by
    rintro point ⟨index, hpoint⟩
    rcases hcarrier index hpoint with ⟨source, hsource, rfl⟩
    exact ⟨source, ⟨sourceParent index, hsource⟩, rfl⟩
  have htargetAD : ∀ rho, scale * sourceDelta ≤ rho → rho ≤ 1 →
      ∀ target : {point : Point3 // point ∈ targetShading.union},
        PureWZ2PaperADSet1
          (scalarProjection (targetPlaneMap target)
            (targetShading.union ∩
              Metric.closedBall (target : Point3) (Real.sqrt rho)))
          rho (1 - sigma) C := by
    intro rho hrhoLower hrhoOne target
    simpa only [targetPlaneMap, inverse] using
      htargetAD rho hrhoLower hrhoOne target
  exact ⟨{
    planeMap := targetPlaneMap
    planeMap_lipschitz := htargetLipschitz
    planeMap_unit := htargetUnit
    planeMap_incidence := htargetIncidence
    local_ad := htargetAD
  }⟩

end Kakeya.Assouad

end
