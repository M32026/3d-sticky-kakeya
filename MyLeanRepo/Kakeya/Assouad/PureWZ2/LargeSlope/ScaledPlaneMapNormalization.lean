import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicExactPopularBox
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.ScaledLocalGrains

/-!
# Unit-Lipschitz plane field after the final isotropic dilation

This is the metric part of the last normalization in paper Lemma 8.  Local AD
is supplied separately because it belongs to the combined affine transport,
not to the anisotropic intermediate object.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

/-- Turn a `K`-Lipschitz plane field into a unit-Lipschitz field through an
isotropic dilation by any scale at least `K`. -/
theorem pureWZ2_isotropic_normalize_plane_map
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
        sourceShading.carrier (sourceParent index)) :
    ∃ planeMap : {point : Point3 // point ∈ targetShading.union} → Point3,
      LipschitzWith 1 planeMap ∧
      (∀ point, ‖planeMap point‖ = 1) ∧
      (∀ index point,
        ∀ hpoint : point ∈ targetShading.carrier index,
          |inner ℝ (targetFamily.tube index).direction
              (planeMap ⟨point, ⟨index, hpoint⟩⟩)| ≤
            scale * sourceDelta) := by
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
  let planeMap := fun target => sourceLocal.planeMap (inverse target)
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
      abs_of_pos hscalePos, div_eq_mul_inv]
    ring
  have hlipschitz : LipschitzWith 1 planeMap := by
    apply LipschitzWith.of_dist_le_mul
    intro first second
    have hsource := sourceLocal.planeMap_lipschitz.dist_le_mul
      (inverse first) (inverse second)
    rw [hinverseDistance] at hsource
    have hratio : (K : ℝ) *
        (dist (first : Point3) (second : Point3) / scale) ≤
        dist (first : Point3) (second : Point3) := by
      calc
        (K : ℝ) * (dist (first : Point3) (second : Point3) / scale)
            ≤ scale * (dist (first : Point3) (second : Point3) / scale) := by
              gcongr
        _ = dist (first : Point3) (second : Point3) := by
              field_simp [hscalePos.ne']
    have hreal := hsource.trans hratio
    simpa only [NNReal.coe_one, one_mul, Subtype.dist_eq] using hreal
  refine ⟨planeMap, hlipschitz, ?_, ?_⟩
  · exact fun target => sourceLocal.planeMap_unit (inverse target)
  · intro index point hpoint
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

end Kakeya.Assouad

end
