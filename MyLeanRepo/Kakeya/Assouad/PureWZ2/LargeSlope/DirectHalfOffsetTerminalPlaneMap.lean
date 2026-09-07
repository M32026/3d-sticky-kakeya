import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalPreimage

/-!
# The direct half-offset terminal exact plane map

This is the source-specific specialization of the fixed projective-normal
transport to the literal `(x,z)` terminal exact image.
-/

noncomputable section

namespace Kakeya.Assouad

namespace PureWZ2DirectCommonYSourceAssembly

variable
    {logExponent : ℕ}
    {sigma epsilon delta width : ℝ}
    (commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta)

/-- The unit projective normal on the literal `(x,z)`-localized terminal
exact image. -/
def halfOffsetTerminalExactPlaneMap
    (firstRetubing : PureWZ2DirectAnisotropicRetubingData
      commonSource.halfOffsetAssembly)
    (terminalBox : PureWZ2LineClassPopularBoxData
      firstRetubing.raw.exactShading width) :
    {point : Point3 //
      point ∈ commonSource.halfOffsetTerminalExactSet
        firstRetubing terminalBox
          (lambda := pureWZ2FixedProjectiveNormalLambda)} → Point3 :=
  fun point =>
    let source := commonSource.halfOffsetAssembly.horizontalSource
    let b := source.m * (source.d - source.c) / 2
    let S := 2 / (source.d - source.c)
    pureWZ2OffsetProjectiveTotalNormalizedNormal b S
      pureWZ2FixedProjectiveNormalLambda
      (pureWZ2OffsetShearProjectiveNormal
        (PureWZ2HalfOffsetHorizontalSourceData.offset source)
        (source.sourceLocalGrains.planeMap
          (commonSource.halfOffsetTerminalSourcePoint
            firstRetubing terminalBox
              (lt_of_lt_of_le (by norm_num)
                pureWZ2FixedProjectiveNormalLambda_one_le) point)))

/-- The pointwise normal used by the terminal exact plane map is unit. -/
theorem halfOffsetTerminalExactPlaneMap_unit
    (firstRetubing : PureWZ2DirectAnisotropicRetubingData
      commonSource.halfOffsetAssembly)
    (terminalBox : PureWZ2LineClassPopularBoxData
      firstRetubing.raw.exactShading width)
    (point : {point : Point3 //
      point ∈ commonSource.halfOffsetTerminalExactSet
        firstRetubing terminalBox
          (lambda := pureWZ2FixedProjectiveNormalLambda)}) :
    ‖commonSource.halfOffsetTerminalExactPlaneMap
        firstRetubing terminalBox point‖ = 1 := by
  exact pureWZ2OffsetProjectiveTotalNormalizedNormal_unit _ _ _ _

/-- Before any tube reindexing, the normalized total image of a genuine
source direction has incidence at most the source radius with the fixed
projective normal. -/
theorem halfOffset_normalizedDirection_incidence
    (index : Fin commonSource.halfOffsetAssembly.cfg.family.card)
    (point : Point3)
    (hpoint : point ∈
      commonSource.halfOffsetAssembly.horizontalSource.sourceShading.carrier
        index) :
    let source := commonSource.halfOffsetAssembly.horizontalSource
    let a := PureWZ2HalfOffsetHorizontalSourceData.offset source
    let b := source.m * (source.d - source.c) / 2
    let S := 2 / (source.d - source.c)
    let direction := wz1PaperDirection
      (commonSource.halfOffsetAssembly.cfg.family.tube index)
    let normal := source.sourceLocalGrains.planeMap
      ⟨point, ⟨index, hpoint⟩⟩
    |inner ℝ
        ((‖pureWZ2OffsetProjectiveTotalLinear a b S
            pureWZ2FixedProjectiveNormalLambda direction‖⁻¹ : ℝ) •
          pureWZ2OffsetProjectiveTotalLinear a b S
            pureWZ2FixedProjectiveNormalLambda direction)
        (pureWZ2OffsetProjectiveTotalNormalizedNormal b S
          pureWZ2FixedProjectiveNormalLambda
          (pureWZ2OffsetShearProjectiveNormal a normal))| ≤ delta := by
  let source := commonSource.halfOffsetAssembly.horizontalSource
  let a := PureWZ2HalfOffsetHorizontalSourceData.offset source
  let b := source.m * (source.d - source.c) / 2
  let S := 2 / (source.d - source.c)
  let direction := wz1PaperDirection
    (commonSource.halfOffsetAssembly.cfg.family.tube index)
  let normal := source.sourceLocalGrains.planeMap ⟨point, ⟨index, hpoint⟩⟩
  have hlengthPos : 0 < source.d - source.c := sub_pos.mpr source.ordered
  have hlengthUpper : source.d - source.c ≤ 1 / 25 := by
    rw [source.length_eq, commonSource.halfOffsetAssembly.horizontalSource_scale]
    have hrho := commonSource.halfOffsetAssembly.rho_tiny
    nlinarith
  have hb : 0 < b := by
    dsimp only [b]
    exact div_pos (mul_pos source.slopeScale_pos hlengthPos) (by norm_num)
  have hbUpper : b ≤ 1 / 50 := by
    dsimp only [b]
    have hproduct := mul_le_mul_of_nonneg_right source.slopeScale_le_one
      hlengthPos.le
    nlinarith
  have hS : 1 ≤ S := by
    dsimp only [S]
    exact (le_div_iff₀ hlengthPos).2 (by nlinarith [hlengthUpper])
  have hlambdaPos : 0 < pureWZ2FixedProjectiveNormalLambda :=
    zero_lt_one.trans_le pureWZ2FixedProjectiveNormalLambda_one_le
  have hvertical : 1 / 2 ≤ |direction 2| := by
    dsimp only [direction]
    unfold wz1PaperDirection
    split_ifs with hsign
    · simpa using commonSource.halfOffsetAssembly.cfg.line_class index |>.vertical
    · simpa using commonSource.halfOffsetAssembly.cfg.line_class index |>.vertical
  have hscale : 1 ≤ pureWZ2FixedProjectiveNormalLambda * S / 2 := by
    have hlambdaTwo : (2 : ℝ) ≤ pureWZ2FixedProjectiveNormalLambda := by
      unfold pureWZ2FixedProjectiveNormalLambda
      norm_num
    have hprod : (2 : ℝ) ≤ pureWZ2FixedProjectiveNormalLambda * S := by
      calc
        (2 : ℝ) = 2 * 1 := by ring
        _ ≤ pureWZ2FixedProjectiveNormalLambda * S :=
          mul_le_mul hlambdaTwo hS (by norm_num) hlambdaPos.le
    nlinarith
  have hdirectionNorm : 1 ≤
      ‖pureWZ2OffsetProjectiveTotalLinear a b S
        pureWZ2FixedProjectiveNormalLambda direction‖ :=
    pureWZ2OffsetProjectiveTotalLinear_norm_lower_one
      (show 0 < S from zero_lt_one.trans_le hS) hlambdaPos hscale direction
        hvertical
  let sourcePoint : {point : Point3 //
      point ∈ source.sourceShading.union} := ⟨point, ⟨index, hpoint⟩⟩
  have hchart : (1 / 50 : ℝ) ≤
      |pureWZ2OffsetShearNormal a normal 1| :=
    PureWZ2HalfOffsetHorizontalSourceData.offsetShearNormal_coord_one_lower_restrict
      source commonSource.halfOffsetAssembly_compatibility sourcePoint
  have hchartNe : pureWZ2OffsetShearNormal a normal 1 ≠ 0 := by
    intro hzero
    rw [hzero, abs_zero] at hchart
    norm_num at hchart
  have hsource : |inner ℝ direction normal| ≤ delta := by
    have hraw := source.sourceLocalGrains.planeMap_incidence index point hpoint
    dsimp only [direction, normal]
    unfold wz1PaperDirection
    split_ifs with hsign
    · exact hraw
    · simpa [inner_neg_left, abs_neg] using hraw
  have hbudget : (b / (1 / 50 : ℝ)) * delta ≤ delta := by
    have hcoefficient : b / (1 / 50 : ℝ) ≤ 1 := by
      exact (div_le_one (by norm_num : (0 : ℝ) < 1 / 50)).2 hbUpper
    exact mul_le_of_le_one_left
      commonSource.halfOffsetAssembly.cfg.extremal.delta_pos.le hcoefficient
  exact pureWZ2OffsetProjectiveTotal_normalizedDirection_inner_abs_le
    hb (by norm_num) (ne_of_gt (zero_lt_one.trans_le hS)) hlambdaPos.ne'
    direction normal hchartNe hchart hsource hdirectionNorm hbudget

/-- On the literal `(x,z)`-localized terminal exact image, the projective
normal obtained from the genuine half-offset source is one-Lipschitz. -/
theorem halfOffsetTerminalExactPlaneMap_lipschitz
    (firstRetubing : PureWZ2DirectAnisotropicRetubingData
      commonSource.halfOffsetAssembly)
    (terminalBox : PureWZ2LineClassPopularBoxData
      firstRetubing.raw.exactShading width) :
    LipschitzWith 1
      (commonSource.halfOffsetTerminalExactPlaneMap
        firstRetubing terminalBox) := by
  let source := commonSource.halfOffsetAssembly.horizontalSource
  let b := source.m * (source.d - source.c) / 2
  let S := 2 / (source.d - source.c)
  have hlengthPos : 0 < source.d - source.c := sub_pos.mpr source.ordered
  have hlengthUpper : source.d - source.c ≤ 2 := by
    linarith [source.left_mem, source.right_mem]
  have hb : 0 < b := by
    dsimp only [b]
    exact div_pos (mul_pos source.slopeScale_pos hlengthPos) (by norm_num)
  have hbOne : b ≤ 1 := by
    dsimp only [b]
    have hproduct : source.m * (source.d - source.c) ≤ 2 := by
      calc
        source.m * (source.d - source.c) ≤
            1 * (source.d - source.c) := by
              exact mul_le_mul_of_nonneg_right source.slopeScale_le_one
                hlengthPos.le
        _ ≤ 2 := by simpa using hlengthUpper
    nlinarith
  have hS : 1 ≤ S := by
    dsimp only [S]
    exact (le_div_iff₀ hlengthPos).2 (by simpa using hlengthUpper)
  let terminalSet := commonSource.halfOffsetTerminalExactSet
    firstRetubing terminalBox
      (lambda := pureWZ2FixedProjectiveNormalLambda)
  let preimage : {point : Point3 // point ∈ terminalSet} →
      {point : Point3 // point ∈
        commonSource.halfOffsetAssembly.horizontalSource.sourceShading.union} :=
    commonSource.halfOffsetTerminalSourcePoint firstRetubing terminalBox
      (lt_of_lt_of_le (by norm_num)
        pureWZ2FixedProjectiveNormalLambda_one_le)
  have htransport :=
    commonSource.halfOffset_fixedLambdaProjectiveNormal_lipschitz
      (X := {point : Point3 // point ∈ terminalSet})
      (b := b) (S := S) (preimage := preimage) hb hbOne hS
      (commonSource.halfOffsetTerminalSourcePoint_scaled_dist_le
        firstRetubing terminalBox pureWZ2FixedProjectiveNormalLambda_one_le)
  change LipschitzWith 1 (fun point =>
    pureWZ2OffsetProjectiveTotalNormalizedNormal b S
      pureWZ2FixedProjectiveNormalLambda
      (pureWZ2OffsetShearProjectiveNormal
        (PureWZ2HalfOffsetHorizontalSourceData.offset source)
        (source.sourceLocalGrains.planeMap (preimage point))))
  exact htransport

end PureWZ2DirectCommonYSourceAssembly

end Kakeya.Assouad

end
