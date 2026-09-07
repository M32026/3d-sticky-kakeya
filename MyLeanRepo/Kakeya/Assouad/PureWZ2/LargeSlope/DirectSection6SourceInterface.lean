import MyLeanRepo.Kakeya.Assouad.PureWZ2.IntervalSlopeRescaling

/-!
# Minimal direct Section-6 source interface

This file contains only the source record consumed by the direct affine
backend.  The historical universal Proposition 6.2 producer lives in
`DirectSection6SourceAssembly`; fixed-scale Node 6 constructions can reuse the
same backend without importing that producer or its obsolete balancing chain.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

/-- Absolute coefficient dominating both finite distortion terms used by the
final isotropic normalization. -/
def pureWZ2DirectFinalGeometryConstant : ℝ :=
  max 1 <| max
    (16 * (lipschitzExtensionConstant Point3 : ℝ) * 145440000)
    1818000000

/-- A fixed source-scale threshold leaving room for final isotropic
normalization after the exact triangular map. -/
def pureWZ2DirectFinalGeometryThreshold : ℝ :=
  1 / (3200000 * pureWZ2DirectFinalGeometryConstant)

theorem pureWZ2DirectFinalGeometryConstant_pos :
    0 < pureWZ2DirectFinalGeometryConstant := by
  unfold pureWZ2DirectFinalGeometryConstant
  exact zero_lt_one.trans_le (le_max_left _ _)

theorem pureWZ2DirectFinalGeometryThreshold_pos :
    0 < pureWZ2DirectFinalGeometryThreshold := by
  unfold pureWZ2DirectFinalGeometryThreshold
  exact one_div_pos.mpr
    (mul_pos (by norm_num) pureWZ2DirectFinalGeometryConstant_pos)

/-- Only the selected source interval, rather than all of the preliminary
Section-6 slab estimates, is consumed by the direct affine backend. -/
structure PureWZ2DirectSourceScaleData
    {delta : ℝ} (rho : WZ2PaperRequestedScale delta) where
  slabLeft : ℝ
  slabRight : ℝ
  slabLeft_mem : -1 ≤ slabLeft
  slab_ordered : slabLeft < slabRight
  slabRight_mem : slabRight ≤ 1
  slab_width : slabRight - slabLeft = rho.1

/-- The complete direct source package immediately before the horizontal
affine normalization. -/
structure PureWZ2DirectSection6SourceAssembly
    (logExponent : ℕ)
    (sigma epsilon delta : ℝ) where
  technicalLoss : ℝ
  technicalLoss_pos : 0 < technicalLoss
  technicalLoss_nonneg : 0 ≤ technicalLoss
  technicalLoss_le_two_epsilon : technicalLoss ≤ 2 * epsilon
  cfg : PureWZ2C2GrainConfiguration sigma technicalLoss delta
  globalSlope : SlopeFunction
  globalSlope_eq_source : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
    globalSlope z = cfg.globalGrains.slope z
  globalSlope_normalized : globalSlope.IsNormalized
  rho : WZ2PaperRequestedScale delta
  delta_small : delta ≤ 1 / 100
  rho_tiny : rho.1 ≤ 1 / 6400
  rho_final_tiny : rho.1 ≤ pureWZ2DirectFinalGeometryThreshold
  delta_le_rho_sq : delta ≤ rho.1 ^ 2
  delta_le_rho_eight : delta ≤ rho.1 ^ 8
  scaleData : PureWZ2DirectSourceScaleData rho
  horizontalSource : PureWZ2HorizontalSourceData cfg
  globalSlope_eq_horizontalSource :
    globalSlope = horizontalSource.globalSlope
  horizontalSource_scale : horizontalSource.source_length = rho.1

end Kakeya.Assouad

end
