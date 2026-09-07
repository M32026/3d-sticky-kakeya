import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetProjectiveNormal
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectAnisotropicRetubing
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.LineClassNormalizationPopularBox

/-!
# Exact preimages for the direct half-offset terminal

This module composes the exact triangular source map with the final
`diag(lambda,1,lambda)` line-class normalization.  It only concerns exact
images.  Cubical saturation is handled later by a nearest-witness argument.
-/

noncomputable section

namespace Kakeya.Assouad

open Set

namespace PureWZ2DirectCommonYSourceAssembly

variable
    {logExponent : ℕ}
    {sigma epsilon delta width lambda : ℝ}
    (commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta)
    (retubing : PureWZ2DirectAnisotropicRetubingData
      commonSource.halfOffsetAssembly)
    (box : PureWZ2LineClassPopularBoxData retubing.raw.exactShading width)

/-- The literal exact terminal set after the `(x,z)` restriction and final
line-class normalization. -/
def halfOffsetTerminalExactSet : Set Point3 :=
  pureWZ2LineClassNormalizationMap box.center lambda '' box.restricted.union

/-- Pull a terminal exact-image point back through the final diagonal map. -/
def halfOffsetTerminalRawPoint
    (hlambda : 0 < lambda)
    (target : {point : Point3 //
      point ∈ commonSource.halfOffsetTerminalExactSet retubing box
        (lambda := lambda)}) :
    {point : Point3 // point ∈ retubing.raw.exactShading.union} := by
  let equivalence :=
    pureWZ2LineClassNormalizationAffineEquiv box.center lambda hlambda
  let rawPoint : Point3 := equivalence.symm target
  refine ⟨rawPoint, ?_⟩
  rcases target.property with ⟨point, hpoint, heq⟩
  have htarget : (target : Point3) = equivalence point := by
    rw [pureWZ2LineClassNormalizationAffineEquiv_apply]
    exact heq.symm
  have hrawPoint : rawPoint = point := by
    dsimp only [rawPoint]
    rw [htarget, AffineEquiv.symm_apply_apply]
  rw [hrawPoint]
  exact paperSubshading_union_subset box.restricted_subshading hpoint

@[simp] theorem halfOffsetTerminal_map_rawPoint
    (hlambda : 0 < lambda)
    (target : {point : Point3 //
      point ∈ commonSource.halfOffsetTerminalExactSet retubing box
        (lambda := lambda)}) :
    pureWZ2LineClassNormalizationMap box.center lambda
        (commonSource.halfOffsetTerminalRawPoint retubing box hlambda target) =
      target := by
  rw [← pureWZ2LineClassNormalizationAffineEquiv_apply]
  exact AffineEquiv.apply_symm_apply _ _

/-- Pull a terminal exact-image point all the way back to the retained
half-offset source. -/
def halfOffsetTerminalSourcePoint
    (hlambda : 0 < lambda)
    (target : {point : Point3 //
      point ∈ commonSource.halfOffsetTerminalExactSet retubing box
        (lambda := lambda)}) :
    {point : Point3 //
      point ∈ commonSource.halfOffsetAssembly.horizontalSource.sourceShading.union} := by
  let rawPoint := commonSource.halfOffsetTerminalRawPoint retubing box
    hlambda target
  let sourcePoint := retubing.raw.exactSourcePoint rawPoint
  refine ⟨sourcePoint, ?_⟩
  rcases sourcePoint.property with ⟨index, hpoint⟩
  exact ⟨(wz2PaperNonemptyCarrierSubfamily
      retubing.popular.popular.restricted).embedding index,
    retubing.popular.source_subshading index hpoint.1⟩

/-- The inverse of the exact two-stage map has the scaled three-Lipschitz
bound needed by the fixed projective-normal theorem. -/
theorem halfOffsetTerminalSourcePoint_scaled_dist_le
    (hlambda : 1 ≤ lambda)
    (first second : {point : Point3 //
      point ∈ commonSource.halfOffsetTerminalExactSet retubing box
        (lambda := lambda)}) :
    let source := commonSource.halfOffsetAssembly.horizontalSource
    let b := source.m * (source.d - source.c) / 2
    b * dist
        (commonSource.halfOffsetTerminalSourcePoint retubing box
          (lt_of_lt_of_le (by norm_num) hlambda) first)
        (commonSource.halfOffsetTerminalSourcePoint retubing box
          (lt_of_lt_of_le (by norm_num) hlambda) second) ≤
      3 * dist first second := by
  let source := commonSource.halfOffsetAssembly.horizontalSource
  let g := pureWZ2DirectGeometrySlope source
  let c := source.c
  let d := source.d
  let m := source.m
  let b := m * (d - c) / 2
  let lambdaPos : 0 < lambda := lt_of_lt_of_le (by norm_num) hlambda
  let firstRaw := commonSource.halfOffsetTerminalRawPoint retubing box
    lambdaPos first
  let secondRaw := commonSource.halfOffsetTerminalRawPoint retubing box
    lambdaPos second
  have hcd : c < d := source.ordered
  have hm : 0 < m := source.slopeScale_pos
  have hmOne : m ≤ 1 := source.slopeScale_le_one
  have hdc : d - c ≤ 1 / 25 := by
    dsimp only [c, d]
    rw [source.length_eq, commonSource.halfOffsetAssembly.horizontalSource_scale]
    have hrho := commonSource.halfOffsetAssembly.rho_tiny
    nlinarith
  have hsub : Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1 := by
    intro z hz
    exact ⟨source.left_mem.trans hz.1, hz.2.trans source.right_mem⟩
  have hg : g.IsNormalized := by
    simpa [g, pureWZ2DirectGeometrySlope] using source.geometrySlope_normalized
  have hb : 0 < b := by
    dsimp only [b]
    exact div_pos (mul_pos source.slopeScale_pos (sub_pos.mpr source.ordered))
      (by norm_num)
  have hop := anisotropicRescalingLinearEquiv_symm_opNorm_le
    g c d m hcd hm hmOne hdc hg hsub
  have hinverse := retubing.raw.exactSourcePoint_lipschitz.dist_le_mul
    firstRaw secondRaw
  have hfirstStage : b * dist
      (retubing.raw.exactSourcePoint firstRaw)
      (retubing.raw.exactSourcePoint secondRaw) ≤
      3 * dist firstRaw secondRaw := by
    calc
      b * dist (retubing.raw.exactSourcePoint firstRaw)
          (retubing.raw.exactSourcePoint secondRaw) ≤
          b * (‖(anisotropicRescalingLinearEquiv g c d m hcd hm).symm
              |>.toContinuousLinearEquiv.toContinuousLinearMap‖ *
            dist firstRaw secondRaw) := by
              gcongr
              simpa only [NNReal.smul_def, coe_nnnorm] using hinverse
      _ ≤ Real.sqrt 6 * dist firstRaw secondRaw := by
        have hbop : b *
            ‖(anisotropicRescalingLinearEquiv g c d m hcd hm).symm
              |>.toContinuousLinearEquiv.toContinuousLinearMap‖ ≤
            Real.sqrt 6 := by
          calc
            b * ‖(anisotropicRescalingLinearEquiv g c d m hcd hm).symm
                |>.toContinuousLinearEquiv.toContinuousLinearMap‖ ≤
                b * (Real.sqrt 6 / b) := by gcongr
            _ = Real.sqrt 6 := by field_simp [hb.ne']
        calc
          b * (‖(anisotropicRescalingLinearEquiv g c d m hcd hm).symm
                |>.toContinuousLinearEquiv.toContinuousLinearMap‖ *
              dist firstRaw secondRaw) =
              (b * ‖(anisotropicRescalingLinearEquiv g c d m hcd hm).symm
                |>.toContinuousLinearEquiv.toContinuousLinearMap‖) *
                dist firstRaw secondRaw := by ring
          _ ≤ Real.sqrt 6 * dist firstRaw secondRaw := by gcongr
      _ ≤ 3 * dist firstRaw secondRaw := by
        have hsqrt : Real.sqrt 6 ≤ 3 := by
          nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6),
            Real.sqrt_nonneg 6]
        gcongr
  have hsecondStage : dist firstRaw secondRaw ≤ dist first second := by
    have hforward := pureWZ2LineClassNormalization_source_dist_le
      box.center hlambda (firstRaw : Point3) (secondRaw : Point3)
    simpa only [firstRaw, secondRaw,
      commonSource.halfOffsetTerminal_map_rawPoint retubing box lambdaPos,
      Subtype.dist_eq] using hforward
  exact hfirstStage.trans <| by gcongr

end PureWZ2DirectCommonYSourceAssembly

end Kakeya.Assouad

end
