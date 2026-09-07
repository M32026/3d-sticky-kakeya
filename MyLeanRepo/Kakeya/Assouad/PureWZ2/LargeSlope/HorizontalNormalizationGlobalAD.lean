import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.HorizontalNormalizationProjection
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.ADTransfer

/-!
# Exact-image global AD after horizontal normalization

This is the exact-set part of the final Proposition-6.5 global-grain
transport.  Cubical saturation is deliberately handled downstream, where its
nonzero projection error is visible.
-/

noncomputable section

namespace Kakeya.Assouad

open Set

/-- Source global AD transfers to the exact image of the triangular map
followed by a horizontal dilation.  The scalar projection is changed by the
positive affine multiplier `lambda`, and the target base scale may be any
larger scale. -/
theorem pureWZ2_horizontalNormalized_exact_global_ad
    {sourceDelta targetDelta sigma : ℝ} {C : ENNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    (sourceGlobal : PureWZ2C2GlobalGrainData sourceShading sigma C)
    (geometrySlope : SlopeFunction)
    {c d m lambda : ℝ}
    (hcd : c < d) (hm : 0 < m) (hlambda : 0 < lambda)
    (hinterval : Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1)
    (anisotropicCenter horizontalCenter : Point3)
    (hcenterHeight : horizontalCenter 2 = 0)
    (hbase : lambda * sourceDelta ≤ targetDelta)
    (htargetDelta : 0 < targetDelta) :
    ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (scalarProjection
          (globalGrainDirection
            (pureWZ2HorizontalNormalizedSlope geometrySlope sourceGlobal.slope
              c d m horizontalCenter t))
          (horizontalSlice
            (pureWZ2HorizontalNormalizedMap geometrySlope c d m
              anisotropicCenter horizontalCenter lambda ''
                sourceShading.union) t))
        targetDelta (1 - sigma) C := by
  intro t ht
  let sourceHeight := c + (d - c) / 2 * (t + 1)
  have hsourceHeight : sourceHeight ∈ Set.Icc c d := by
    dsimp only [sourceHeight]
    have hlength : 0 < d - c := sub_pos.mpr hcd
    constructor
    · have hnonnegative : 0 ≤ t + 1 := by linarith [ht.1]
      have : 0 ≤ (d - c) / 2 * (t + 1) := by positivity
      linarith
    · have htwo : t + 1 ≤ 2 := by linarith [ht.2]
      have hupper : (d - c) / 2 * (t + 1) ≤ d - c := by
        calc
          (d - c) / 2 * (t + 1) ≤ (d - c) / 2 * 2 := by gcongr
          _ = d - c := by ring
      linarith
  have hsource := sourceGlobal.global_ad_slope sourceHeight
    (hinterval hsourceHeight)
  have haffine := PureWZ2PaperADSet1.affine_transfer
    (b := pureWZ2HorizontalNormalizedProjectionOffset geometrySlope
      sourceGlobal.slope c d m anisotropicCenter horizontalCenter lambda t)
      hsource hlambda
  have hheight : c + (d - c) / 2 *
      (horizontalCenter 2 + t + 1) = sourceHeight := by
    rw [hcenterHeight]
    simp [sourceHeight]
  rw [pureWZ2HorizontalNormalized_projection_set geometrySlope
    sourceGlobal.slope hcd hm anisotropicCenter horizontalCenter
      sourceShading.union t,
    hheight]
  exact haffine.weaken_scale htargetDelta hbase

end Kakeya.Assouad

end
