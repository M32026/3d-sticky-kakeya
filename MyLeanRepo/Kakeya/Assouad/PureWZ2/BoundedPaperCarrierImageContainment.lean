import MyLeanRepo.Kakeya.Assouad.PureWZ2.OrdinaryLineConflictPacking
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12OrdinaryRescaledTube
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperTubeCarrierGeometryHelpers

/-!
# Bounded cropped paper carriers inside the public ordinary rescaling

The normalized source tubes have bounded ordinary bases.  After the literal
`1 / 100` longitudinal compression, the entire cropped full-axis paper
carrier therefore fits in the midpoint-centered public ordinary target.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric

attribute [local instance] Classical.propDecidable

theorem wz2PaperLiteral_image_paperCarrier_subset_ordinary_of_boundedBase
    {delta rho : ℝ}
    (hdelta : 0 < delta)
    (source : Kakeya.DeltaTube delta)
    (anchor : Kakeya.DeltaTube rho)
    (hrho : 0 < rho)
    (hrhoOne : rho ≤ 1)
    (ratioSmall : delta / rho ≤ 1 / 24)
    (sourceLine : WZ1PaperTubeInLineClass source)
    (sourceBase : ‖source.base‖ ≤ 4)
    (covered : WZ1PaperTubeCovers source anchor) :
    wz2PaperLiteralUnitRescalingMap anchor hrho ''
        wz1PaperTubeCarrier source ⊆
      (wz2PaperLiteralOrdinaryRescaledTube
        source anchor hrho).carrier := by
  rintro imagePoint ⟨sourcePoint, sourcePointMem, rfl⟩
  have deltaLeRho : delta ≤ rho := by
    have ratioOne : delta / rho ≤ 1 :=
      ratioSmall.trans (by norm_num)
    exact (div_le_one hrho).mp ratioOne
  have deltaSmall : delta ≤ 1 / 24 := by
    calc
      delta ≤ rho / 24 := by
        have scaled := (div_le_iff₀ hrho).mp ratioSmall
        simpa [div_eq_mul_inv, mul_comm] using scaled
      _ ≤ 1 / 24 := by
        gcongr
  rcases
      exists_dist_le_of_mem_cthickening_closed
        (isClosed_tubeAxisLine source)
        (by positivity : 0 ≤ 6 * delta)
        sourcePointMem.1
    with ⟨axisPoint, axisPointMem, sourceAxisDistance⟩
  rcases wz1Paper_axis_exists_parameter sourceLine axisPointMem with
    ⟨axisParameter, axisPointEq⟩
  let midpointParameter :=
    pureWZ2OrdinaryAxialParameter source sourceLine
  have midpointEq :
      wz2PaperTubeMidpoint source =
        wz1TubeAxisZeroPoint source +
          midpointParameter • wz1PaperDirection source :=
    pureWZ2OrdinaryAxialParameter_spec source sourceLine
  have midpointParameterBound :
      |midpointParameter| ≤ 6 :=
    pureWZ2OrdinaryAxialParameter_abs_le_six
      sourceLine sourceBase
  let error := sourcePoint - axisPoint
  have errorNorm : ‖error‖ ≤ 6 * delta := by
    simpa [error, dist_eq_norm] using sourceAxisDistance
  have sourcePointHeight : |sourcePoint (2 : Fin 3)| ≤ 1 := by
    simpa [Kakeya.Streamlined.axisBox] using sourcePointMem.2 |>.2.2
  have zeroHeight :
      (wz1TubeAxisZeroPoint source) (2 : Fin 3) = 0 :=
    wz1TubeAxisZeroPoint_coord_two source sourceLine.vertical
  have directionHeight :
      (1 / 2 : ℝ) ≤
        (wz1PaperDirection source) (2 : Fin 3) :=
    sourceLine.1
  have directionHeightPos :
      0 < (wz1PaperDirection source) (2 : Fin 3) := by
    linarith
  have sourcePointDecomposition :
      sourcePoint =
        wz1TubeAxisZeroPoint source +
          axisParameter • wz1PaperDirection source + error := by
    dsimp only [error]
    rw [axisPointEq]
    abel
  have heightIdentity :
      sourcePoint (2 : Fin 3) =
        axisParameter *
            (wz1PaperDirection source) (2 : Fin 3) +
          error (2 : Fin 3) := by
    rw [sourcePointDecomposition]
    simp [zeroHeight, smul_eq_mul]
  have errorHeight : |error (2 : Fin 3)| ≤ 6 * delta := by
    exact
      (show |error (2 : Fin 3)| ≤ ‖error‖ by
        simpa [Real.norm_eq_abs] using
          PiLp.norm_apply_le error (2 : Fin 3)).trans errorNorm
  have axisParameterBound : |axisParameter| ≤ 5 / 2 := by
    have productBound :
        |axisParameter *
            (wz1PaperDirection source) (2 : Fin 3)| ≤
          1 + 6 * delta := by
      calc
        |axisParameter *
            (wz1PaperDirection source) (2 : Fin 3)| =
            |sourcePoint (2 : Fin 3) - error (2 : Fin 3)| := by
          congr 1
          linarith
        _ ≤ |sourcePoint (2 : Fin 3)| +
              |error (2 : Fin 3)| :=
          abs_sub _ _
        _ ≤ 1 + 6 * delta := by
          gcongr
    have productEq :
        |axisParameter *
            (wz1PaperDirection source) (2 : Fin 3)| =
          |axisParameter| *
            (wz1PaperDirection source) (2 : Fin 3) := by
      rw [abs_mul, abs_of_pos directionHeightPos]
    rw [productEq] at productBound
    have lower :
        |axisParameter| * (1 / 2 : ℝ) ≤
          |axisParameter| *
            (wz1PaperDirection source) (2 : Fin 3) := by
      gcongr
    nlinarith
  let imageDirection :=
    wz2PaperLiteralSourceImageDirection source anchor
  have imageDirectionNe : imageDirection ≠ 0 :=
    wz2PaperLiteralSourceImageDirection_ne_zero
      source anchor hrho
  have imageDirectionBound : ‖imageDirection‖ ≤ 3 / 200 := by
    dsimp only [imageDirection, wz2PaperLiteralSourceImageDirection]
    unfold wz1PaperDirection
    split_ifs
    · exact
        wz2PaperLiteralUnitRescalingLinear_sourceDirection_norm_le
          hrho hrhoOne covered
    · simpa using
        wz2PaperLiteralUnitRescalingLinear_sourceDirection_norm_le
          hrho hrhoOne covered
  have parameterDifference :
      |axisParameter - midpointParameter| ≤ 17 / 2 := by
    calc
      |axisParameter - midpointParameter| ≤
          |axisParameter| + |midpointParameter| :=
        abs_sub _ _
      _ ≤ 5 / 2 + 6 := by
        gcongr
      _ = 17 / 2 := by ring
  have imageParameterBound :
      |(axisParameter - midpointParameter) *
          ‖imageDirection‖| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_nonneg (norm_nonneg imageDirection)]
    calc
      |axisParameter - midpointParameter| *
            ‖imageDirection‖ ≤
          (17 / 2 : ℝ) * (3 / 200) := by
        gcongr
      _ ≤ 1 / 2 := by norm_num
  let targetParameter :=
    1 / 2 +
      (axisParameter - midpointParameter) * ‖imageDirection‖
  have targetParameterMem : targetParameter ∈ Set.Icc (0 : ℝ) 1 := by
    rw [Set.mem_Icc]
    dsimp only [targetParameter]
    rw [abs_le] at imageParameterBound
    constructor <;> linarith
  have axisDifference :
      axisPoint - wz2PaperTubeMidpoint source =
        (axisParameter - midpointParameter) •
          wz1PaperDirection source := by
    rw [axisPointEq, midpointEq]
    module
  have imageAxisPoint :
      wz2PaperLiteralUnitRescalingMap anchor hrho axisPoint ∈
        Kakeya.unitSegment
          (wz2PaperLiteralOrdinaryRescaledTube
            source anchor hrho).base
          (wz2PaperLiteralOrdinaryRescaledTube
            source anchor hrho).direction := by
    refine ⟨targetParameter, targetParameterMem, ?_⟩
    have mapDifference :
        wz2PaperLiteralUnitRescalingMap anchor hrho axisPoint =
          wz2PaperLiteralUnitRescalingMap anchor hrho
              (wz2PaperTubeMidpoint source) +
            (axisParameter - midpointParameter) • imageDirection := by
      have difference :=
        wz2PaperLiteralUnitRescalingMap_sub
          anchor hrho axisPoint (wz2PaperTubeMidpoint source)
      rw [axisDifference, map_smul] at difference
      change
        wz2PaperLiteralUnitRescalingMap anchor hrho axisPoint -
            wz2PaperLiteralUnitRescalingMap anchor hrho
              (wz2PaperTubeMidpoint source) =
          (axisParameter - midpointParameter) • imageDirection
        at difference
      rw [← difference]
      abel
    rw [mapDifference]
    change
      (wz2PaperLiteralUnitRescalingMap anchor hrho
          (wz2PaperTubeMidpoint source) -
        (1 / 2 : ℝ) • NormedSpace.normalize imageDirection) +
          targetParameter • NormedSpace.normalize imageDirection =
        wz2PaperLiteralUnitRescalingMap anchor hrho
            (wz2PaperTubeMidpoint source) +
          (axisParameter - midpointParameter) • imageDirection
    dsimp only [targetParameter]
    have recover' :
        ‖imageDirection‖ •
            NormedSpace.normalize imageDirection =
          imageDirection :=
      NormedSpace.norm_smul_normalize imageDirection
    have scaledRecover :
        ((axisParameter - midpointParameter) * ‖imageDirection‖) •
            NormedSpace.normalize imageDirection =
          (axisParameter - midpointParameter) • imageDirection := by
      rw [mul_smul, recover']
    rw [add_smul, scaledRecover]
    module
  have imageDistance :
      dist
          (wz2PaperLiteralUnitRescalingMap anchor hrho sourcePoint)
          (wz2PaperLiteralUnitRescalingMap anchor hrho axisPoint) ≤
        delta / rho := by
    rw [dist_eq_norm, wz2PaperLiteralUnitRescalingMap_sub]
    calc
      ‖wz2PaperLiteralUnitRescalingLinear anchor
          (sourcePoint - axisPoint)‖ ≤
          ‖sourcePoint - axisPoint‖ / (100 * rho) :=
        wz2PaperLiteralUnitRescalingLinear_norm_le
          anchor hrho hrhoOne _
      _ ≤ (6 * delta) / (100 * rho) := by
        gcongr
      _ ≤ delta / rho := by
        apply
          (div_le_iff₀
            (mul_pos (by norm_num) hrho)).mpr
        field_simp [hrho.ne']
        nlinarith
  exact
    Metric.mem_cthickening_of_dist_le
      (wz2PaperLiteralUnitRescalingMap anchor hrho sourcePoint)
      (wz2PaperLiteralUnitRescalingMap anchor hrho axisPoint)
      (delta / rho)
      (Kakeya.unitSegment
        (wz2PaperLiteralOrdinaryRescaledTube
          source anchor hrho).base
        (wz2PaperLiteralOrdinaryRescaledTube
          source anchor hrho).direction)
      imageAxisPoint imageDistance

end Kakeya.Assouad

end
