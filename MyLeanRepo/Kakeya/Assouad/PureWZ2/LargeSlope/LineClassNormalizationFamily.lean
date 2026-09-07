import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.LineClassSlopeCompatibleNormalization
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AffineDiagonalRawTube

/-!
# Exact family for the line-class-compatible final normalization

This file applies the single map `diag(lambda, 1, lambda)` to a complete
tube configuration.  The family and exact shading use the same affine
equivalence literally.  In particular, the exact mass multiplier is
`lambda^2`, matching the two expanded coordinates.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

/-- Unit direction obtained from `diag(lambda, 1, lambda)`. -/
def pureWZ2LineClassNormalizationDirection
    (lambda : ℝ) (hlambda : 0 < lambda) (direction : Point3) : Point3 :=
  let image := pureWZ2LineClassNormalizationLinearEquiv lambda hlambda direction
  (‖image‖⁻¹ : ℝ) • image

theorem pureWZ2LineClassNormalizationDirection_unit
    (lambda : ℝ) (hlambda : 0 < lambda)
    {direction : Point3} (hdirection : direction ≠ 0) :
    ‖pureWZ2LineClassNormalizationDirection lambda hlambda direction‖ = 1 := by
  let linear := pureWZ2LineClassNormalizationLinearEquiv lambda hlambda
  let image := linear direction
  have himage : image ≠ 0 := by
    intro hzero
    apply hdirection
    apply linear.injective
    simpa [image] using hzero
  have hnorm : 0 < ‖image‖ := norm_pos_iff.mpr himage
  change ‖(‖image‖⁻¹ : ℝ) • image‖ = 1
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  field_simp [hnorm.ne']

/-- A target tube whose supporting line is the exact normalized image of the
source supporting line.  Its radius is supplied by the later saturation. -/
def pureWZ2LineClassNormalizationTube
    (center : Point3) (lambda : ℝ) (hlambda : 0 < lambda)
    {sourceDelta targetDelta : ℝ}
    (source : Kakeya.DeltaTube sourceDelta) : Kakeya.DeltaTube targetDelta where
  base := pureWZ2LineClassNormalizationMap center lambda source.base
  direction := pureWZ2LineClassNormalizationDirection
    lambda hlambda source.direction
  direction_unit :=
    pureWZ2LineClassNormalizationDirection_unit lambda hlambda <| by
      intro hzero
      have hnorm := congrArg norm hzero
      rw [source.direction_unit, norm_zero] at hnorm
      norm_num at hnorm

/-- The line-class normalization is affine on parametrized lines. -/
theorem pureWZ2LineClassNormalizationMap_add_smul
    (center : Point3) (lambda : ℝ) (hlambda : 0 < lambda)
    (base direction : Point3) (scalar : ℝ) :
    pureWZ2LineClassNormalizationMap center lambda
        (base + scalar • direction) =
      pureWZ2LineClassNormalizationMap center lambda base +
        scalar •
          pureWZ2LineClassNormalizationLinearEquiv lambda hlambda
            direction := by
  let equivalence :=
    pureWZ2LineClassNormalizationAffineEquiv center lambda hlambda
  have hmap := equivalence.map_vadd base (scalar • direction)
  rw [map_smul] at hmap
  rw [← pureWZ2LineClassNormalizationAffineEquiv_apply
      center lambda hlambda (base + scalar • direction),
    ← pureWZ2LineClassNormalizationAffineEquiv_apply
      center lambda hlambda base]
  change equivalence (base + scalar • direction) =
    equivalence base + scalar • equivalence.linear direction
  simpa only [vadd_eq_add, add_comm] using hmap

/-- Exact supporting-line covariance for one normalized tube. -/
theorem pureWZ2LineClassNormalizationTube_axis
    (center : Point3) (lambda : ℝ) (hlambda : 0 < lambda)
    {sourceDelta targetDelta : ℝ}
    (source : Kakeya.DeltaTube sourceDelta) :
    tubeAxisLine
        (pureWZ2LineClassNormalizationTube center lambda hlambda source :
          Kakeya.DeltaTube targetDelta) =
      pureWZ2LineClassNormalizationMap center lambda '' tubeAxisLine source := by
  let imageDirection :=
    pureWZ2LineClassNormalizationLinearEquiv lambda hlambda source.direction
  have hsourceDirection : source.direction ≠ 0 := by
    intro hzero
    have hnorm := congrArg norm hzero
    rw [source.direction_unit, norm_zero] at hnorm
    norm_num at hnorm
  have himageDirection : imageDirection ≠ 0 := by
    intro hzero
    apply hsourceDirection
    apply (pureWZ2LineClassNormalizationLinearEquiv lambda hlambda).injective
    change imageDirection =
      (pureWZ2LineClassNormalizationLinearEquiv lambda hlambda) 0
    rw [hzero, map_zero]
  have himageNorm : 0 < ‖imageDirection‖ :=
    norm_pos_iff.mpr himageDirection
  ext target
  constructor
  · rintro ⟨parameter, rfl⟩
    refine ⟨source.base + (parameter / ‖imageDirection‖) • source.direction,
      ⟨parameter / ‖imageDirection‖, rfl⟩, ?_⟩
    rw [pureWZ2LineClassNormalizationMap_add_smul center lambda hlambda]
    change pureWZ2LineClassNormalizationMap center lambda source.base +
        (parameter / ‖imageDirection‖) • imageDirection = _
    change _ = pureWZ2LineClassNormalizationMap center lambda source.base +
        parameter • ((‖imageDirection‖⁻¹ : ℝ) • imageDirection)
    rw [smul_smul]
    congr 2
  · rintro ⟨sourcePoint, ⟨parameter, rfl⟩, rfl⟩
    refine ⟨parameter * ‖imageDirection‖, ?_⟩
    rw [pureWZ2LineClassNormalizationMap_add_smul center lambda hlambda]
    change pureWZ2LineClassNormalizationMap center lambda source.base +
        parameter • imageDirection = _
    change _ = pureWZ2LineClassNormalizationMap center lambda source.base +
        (parameter * ‖imageDirection‖) •
          ((‖imageDirection‖⁻¹ : ℝ) • imageDirection)
    rw [smul_smul]
    congr 2
    field_simp [himageNorm.ne']

/-- One-to-one target family for the line-class normalization. -/
def pureWZ2LineClassNormalizationFamily
    {sourceDelta targetDelta : ℝ}
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta)
    (center : Point3) (lambda : ℝ) (hlambda : 0 < lambda) :
    Kakeya.Streamlined.TubeFamily targetDelta where
  card := sourceFamily.card
  tube index := pureWZ2LineClassNormalizationTube
    center lambda hlambda (sourceFamily.tube index)

@[simp] theorem pureWZ2LineClassNormalizationFamily_tube
    {sourceDelta targetDelta : ℝ}
    (sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta)
    (center : Point3) (lambda : ℝ) (hlambda : 0 < lambda)
    (index : Fin sourceFamily.card) :
    (pureWZ2LineClassNormalizationFamily (targetDelta := targetDelta)
      sourceFamily center lambda hlambda).tube index =
      pureWZ2LineClassNormalizationTube center lambda hlambda
        (sourceFamily.tube index) :=
  rfl

/-- Literal exact-image shading on the normalized family. -/
def pureWZ2LineClassNormalizationExactShading
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (center : Point3) (lambda : ℝ) (hlambda : 0 < lambda)
    (hcarrier : ∀ index,
      pureWZ2LineClassNormalizationMap center lambda ''
          sourceShading.carrier index ⊆
        wz1PaperTubeCarrier
          ((pureWZ2LineClassNormalizationFamily
            (targetDelta := targetDelta) sourceFamily center lambda hlambda).tube
              index)) :
    WZ1PaperTubeShading
      (pureWZ2LineClassNormalizationFamily
        (targetDelta := targetDelta) sourceFamily center lambda hlambda) where
  carrier index := pureWZ2LineClassNormalizationMap center lambda ''
    sourceShading.carrier index
  measurable_carrier index := by
    let equivalence :=
      pureWZ2LineClassNormalizationAffineEquiv center lambda hlambda
    have heq :
        pureWZ2LineClassNormalizationMap center lambda ''
            sourceShading.carrier index =
          equivalence '' sourceShading.carrier index := by
      ext point
      simp only [Set.mem_image]
      constructor
      · rintro ⟨source, hsource, rfl⟩
        exact ⟨source, hsource,
          pureWZ2LineClassNormalizationAffineEquiv_apply
            center lambda hlambda source⟩
      · rintro ⟨source, hsource, rfl⟩
        exact ⟨source, hsource,
          (pureWZ2LineClassNormalizationAffineEquiv_apply
            center lambda hlambda source).symm⟩
    rw [heq]
    exact equivalence.toHomeomorphOfFiniteDimensional.toMeasurableEquiv
      |>.measurableSet_image.mpr (sourceShading.measurable_carrier index)
  subset_body index := hcarrier index

@[simp] theorem pureWZ2LineClassNormalizationExactShading_carrier
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (center : Point3) (lambda : ℝ) (hlambda : 0 < lambda)
    (hcarrier : ∀ index,
      pureWZ2LineClassNormalizationMap center lambda ''
          sourceShading.carrier index ⊆
        wz1PaperTubeCarrier
          ((pureWZ2LineClassNormalizationFamily
            (targetDelta := targetDelta) sourceFamily center lambda hlambda).tube
              index))
    (index : Fin sourceFamily.card) :
    (pureWZ2LineClassNormalizationExactShading sourceShading center
      lambda hlambda hcarrier).carrier index =
      pureWZ2LineClassNormalizationMap center lambda ''
        sourceShading.carrier index :=
  rfl

/-- The target union is the image of the source union under the same map. -/
theorem pureWZ2LineClassNormalizationExactShading_union
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (center : Point3) (lambda : ℝ) (hlambda : 0 < lambda)
    (hcarrier : ∀ index,
      pureWZ2LineClassNormalizationMap center lambda ''
          sourceShading.carrier index ⊆
        wz1PaperTubeCarrier
          ((pureWZ2LineClassNormalizationFamily
            (targetDelta := targetDelta) sourceFamily center lambda hlambda).tube
              index)) :
    (pureWZ2LineClassNormalizationExactShading sourceShading center
      lambda hlambda hcarrier).union =
      pureWZ2LineClassNormalizationMap center lambda ''
        sourceShading.union := by
  ext point
  constructor
  · rintro ⟨index, source, hsource, rfl⟩
    exact ⟨source, ⟨index, hsource⟩, rfl⟩
  · rintro ⟨source, ⟨index, hsource⟩, rfl⟩
    exact ⟨index, source, hsource, rfl⟩

/-- Package exact global AD on the literal target family and shading.  This
is the last zero-error step before any optional target-grid saturation. -/
theorem pureWZ2LineClassNormalizationExactShading_global_ad
    {sourceDelta targetDelta sigma : ℝ} {C : ENNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (sourceSlope : SlopeFunction)
    (hsourceAD : ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (scalarProjection (globalGrainDirection (sourceSlope t))
          (horizontalSlice sourceShading.union t))
        sourceDelta (1 - sigma) C)
    (center : Point3) {lambda : ℝ} (hlambda : 0 < lambda)
    (hcenterHeight : center 2 = 0)
    (hsourceHeight : ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      t / lambda ∈ Set.Icc (-1 : ℝ) 1)
    (hbase : lambda * sourceDelta ≤ targetDelta)
    (htargetDelta : 0 < targetDelta)
    (hcarrier : ∀ index,
      pureWZ2LineClassNormalizationMap center lambda ''
          sourceShading.carrier index ⊆
        wz1PaperTubeCarrier
          ((pureWZ2LineClassNormalizationFamily
            (targetDelta := targetDelta) sourceFamily center lambda hlambda).tube
              index)) :
    ∀ t ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (scalarProjection
          (globalGrainDirection
            (pureWZ2LineClassNormalizedSlope sourceSlope
              (center 2) lambda t))
          (horizontalSlice
            (pureWZ2LineClassNormalizationExactShading sourceShading center
              lambda hlambda hcarrier).union t))
        targetDelta (1 - sigma) C := by
  intro t ht
  rw [pureWZ2LineClassNormalizationExactShading_union]
  exact pureWZ2_lineClassNormalization_exact_global_ad_of_slope
    sourceSlope hsourceAD center hlambda hcenterHeight hsourceHeight hbase
      htargetDelta t ht

/-- Exact mass scaling of the synchronized target shading. -/
theorem pureWZ2LineClassNormalizationExactShading_mass
    {sourceDelta targetDelta : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceShading : WZ1PaperTubeShading sourceFamily)
    (center : Point3) (lambda : ℝ) (hlambda : 0 < lambda)
    (hcarrier : ∀ index,
      pureWZ2LineClassNormalizationMap center lambda ''
          sourceShading.carrier index ⊆
        wz1PaperTubeCarrier
          ((pureWZ2LineClassNormalizationFamily
            (targetDelta := targetDelta) sourceFamily center lambda hlambda).tube
              index)) :
    (pureWZ2LineClassNormalizationExactShading sourceShading center
      lambda hlambda hcarrier).mass =
      ENNReal.ofReal (lambda ^ 2) * sourceShading.mass := by
  change (∑ index, MeasureTheory.volume
      (pureWZ2LineClassNormalizationMap center lambda ''
        sourceShading.carrier index)) =
    ENNReal.ofReal (lambda ^ 2) *
      ∑ index, MeasureTheory.volume (sourceShading.carrier index)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro index _
  exact pureWZ2LineClassNormalizationMap_volume_image
    center lambda hlambda _

/-- The line-class normalization preserves the positive paper orientation. -/
theorem wz1PaperDirection_lineClassNormalizationTube
    (center : Point3) {lambda : ℝ} (hlambda : 1 ≤ lambda)
    {sourceDelta targetDelta : ℝ}
    (source : Kakeya.DeltaTube sourceDelta) :
    wz1PaperDirection
        (pureWZ2LineClassNormalizationTube center lambda
          (lt_of_lt_of_le (by norm_num) hlambda) source :
            Kakeya.DeltaTube targetDelta) =
      pureWZ2LineClassNormalizationDirection lambda
        (lt_of_lt_of_le (by norm_num) hlambda) (wz1PaperDirection source) := by
  let lambdaPos : 0 < lambda := lt_of_lt_of_le (by norm_num) hlambda
  have hsourceNonzero : source.direction ≠ 0 := by
    intro hzero
    have hnorm := congrArg norm hzero
    rw [source.direction_unit, norm_zero] at hnorm
    norm_num at hnorm
  unfold wz1PaperDirection
  change (if 0 ≤ pureWZ2LineClassNormalizationDirection lambda lambdaPos
          source.direction 2 then
        pureWZ2LineClassNormalizationDirection lambda lambdaPos
          source.direction
      else -pureWZ2LineClassNormalizationDirection lambda lambdaPos
        source.direction) = _
  have himageNonzero :
      pureWZ2LineClassNormalizationLinear lambda source.direction ≠ 0 := by
    intro hzero
    have heq : pureWZ2LineClassNormalizationLinearEquiv lambda lambdaPos
        source.direction = 0 := by
      simpa only [pureWZ2LineClassNormalizationLinearEquiv_apply] using hzero
    apply hsourceNonzero
    apply (pureWZ2LineClassNormalizationLinearEquiv lambda lambdaPos).injective
    rw [heq, map_zero]
  have hcoefficient : 0 <
      ‖pureWZ2LineClassNormalizationLinear lambda source.direction‖⁻¹ *
        lambda := by
    exact mul_pos (inv_pos.mpr (norm_pos_iff.mpr himageNonzero)) lambdaPos
  have hsign : 0 ≤ pureWZ2LineClassNormalizationDirection lambda lambdaPos
        source.direction 2 ↔ 0 ≤ source.direction 2 := by
    simp only [pureWZ2LineClassNormalizationDirection, PiLp.smul_apply,
      pureWZ2LineClassNormalizationLinearEquiv_apply,
      pureWZ2LineClassNormalizationLinear, point3_coord2]
    change 0 ≤
        ‖point3 (lambda * source.direction 0) (source.direction 1)
          (lambda * source.direction 2)‖⁻¹ *
            (lambda * source.direction 2) ↔ _
    have hnormEq :
        ‖point3 (lambda * source.direction 0) (source.direction 1)
          (lambda * source.direction 2)‖ =
        ‖pureWZ2LineClassNormalizationLinear lambda source.direction‖ := by
      rfl
    rw [hnormEq]
    rw [show ‖pureWZ2LineClassNormalizationLinear lambda
          source.direction‖⁻¹ * (lambda * source.direction 2) =
        (‖pureWZ2LineClassNormalizationLinear lambda
          source.direction‖⁻¹ * lambda) * source.direction 2 by ring]
    exact mul_nonneg_iff_of_pos_left hcoefficient
  by_cases hsourceSign : 0 ≤ source.direction 2
  · rw [if_pos hsourceSign, if_pos (hsign.mpr hsourceSign)]
  · rw [if_neg hsourceSign, if_neg (fun h => hsourceSign (hsign.mp h))]
    unfold pureWZ2LineClassNormalizationDirection
    simp only [map_neg, norm_neg, smul_neg, neg_smul]

/-- The canonical target zero-height axis point is the image of the source
axis point at the normalization center's height. -/
theorem wz1TubeAxisZeroPoint_lineClassNormalizationTube
    (center : Point3) {lambda : ℝ} (hlambda : 1 ≤ lambda)
    {sourceDelta targetDelta : ℝ}
    (source : Kakeya.DeltaTube sourceDelta)
    (hsourceVertical : (1 / 2 : ℝ) ≤ |source.direction 2|) :
    wz1TubeAxisZeroPoint
        (pureWZ2LineClassNormalizationTube center lambda
          (lt_of_lt_of_le (by norm_num) hlambda) source :
            Kakeya.DeltaTube targetDelta) =
      pureWZ2LineClassNormalizationMap center lambda
        (tubeAxisPointAtHeight source (center 2)) := by
  let lambdaPos : 0 < lambda := lt_of_lt_of_le (by norm_num) hlambda
  let target : Kakeya.DeltaTube targetDelta :=
    pureWZ2LineClassNormalizationTube center lambda lambdaPos source
  have htargetVertical : (1 / 2 : ℝ) ≤ |target.direction 2| := by
    change (1 / 2 : ℝ) ≤
      |pureWZ2LineClassNormalizationDirection lambda lambdaPos
        source.direction 2|
    have hratio := pureWZ2LineClassNormalization_vertical_ratio hlambda
      source.direction_unit hsourceVertical
    have heq :
        |pureWZ2LineClassNormalizationDirection lambda lambdaPos
            source.direction 2| =
          |pureWZ2LineClassNormalizationLinear lambda source.direction 2| /
            ‖pureWZ2LineClassNormalizationLinear lambda source.direction‖ := by
      simp only [pureWZ2LineClassNormalizationDirection,
        pureWZ2LineClassNormalizationLinearEquiv_apply, PiLp.smul_apply,
        smul_eq_mul, abs_mul, abs_inv, abs_norm]
      ring
    rw [heq]
    exact hratio
  apply wz1TubeAxisZeroPoint_eq_of_mem_axis_of_coord_two_eq_zero
    htargetVertical
  · rw [show tubeAxisLine target =
        pureWZ2LineClassNormalizationMap center lambda ''
          tubeAxisLine source by
      exact pureWZ2LineClassNormalizationTube_axis center lambda lambdaPos source]
    exact ⟨tubeAxisPointAtHeight source (center 2),
      tubeAxisPointAtHeight_mem source _, rfl⟩
  · have hsourceVerticalNe : source.direction 2 ≠ 0 := by
      intro hzero
      rw [hzero, abs_zero] at hsourceVertical
      norm_num at hsourceVertical
    have hsourceHeight : tubeAxisPointAtHeight source (center 2) 2 =
        center 2 := tubeAxisPointAtHeight_coord_two source hsourceVerticalNe _
    simp only [pureWZ2LineClassNormalizationMap, point3_coord2]
    rw [hsourceHeight, sub_self, mul_zero]

/-- A coordinatewise bound on the exact target zero point upgrades the
line-class normalization tube to the paper line class. -/
theorem lineClassNormalizationTube_in_lineClass
    (center : Point3) {lambda : ℝ} (hlambda : 1 ≤ lambda)
    {sourceDelta targetDelta : ℝ}
    (source : Kakeya.DeltaTube sourceDelta)
    (hsourceVertical : (1 / 2 : ℝ) ≤ |source.direction 2|)
    (hzeroX :
      |pureWZ2LineClassNormalizationMap center lambda
        (tubeAxisPointAtHeight source (center 2)) 0| ≤ 1 / 3)
    (hzeroY :
      |pureWZ2LineClassNormalizationMap center lambda
        (tubeAxisPointAtHeight source (center 2)) 1| ≤ 1 / 3) :
    WZ1PaperTubeInLineClass
      (pureWZ2LineClassNormalizationTube center lambda
        (lt_of_lt_of_le (by norm_num) hlambda) source :
          Kakeya.DeltaTube targetDelta) := by
  let lambdaPos : 0 < lambda := lt_of_lt_of_le (by norm_num) hlambda
  let target : Kakeya.DeltaTube targetDelta :=
    pureWZ2LineClassNormalizationTube center lambda lambdaPos source
  have hpaperDirection := wz1PaperDirection_lineClassNormalizationTube
    (targetDelta := targetDelta) center hlambda source
  have hvertical : (1 / 2 : ℝ) ≤
      wz1PaperDirection target 2 := by
    rw [hpaperDirection]
    have hratio := pureWZ2LineClassNormalization_vertical_ratio hlambda
      (wz1PaperDirection_norm source) <| by
        have habs : |wz1PaperDirection source 2| =
            |source.direction 2| := by
          unfold wz1PaperDirection
          split_ifs <;> simp
        rw [habs]
        exact hsourceVertical
    have hsourceDirectionTwo : 0 ≤ wz1PaperDirection source 2 := by
      unfold wz1PaperDirection
      split_ifs with hsign
      · exact hsign
      · exact neg_nonneg.mpr (le_of_not_ge hsign)
    have htargetDirectionTwo : 0 ≤
        pureWZ2LineClassNormalizationLinear lambda
          (wz1PaperDirection source) 2 := by
      simp only [pureWZ2LineClassNormalizationLinear, point3_coord2]
      exact mul_nonneg lambdaPos.le hsourceDirectionTwo
    rw [abs_of_nonneg htargetDirectionTwo] at hratio
    have heq :
        pureWZ2LineClassNormalizationDirection lambda lambdaPos
            (wz1PaperDirection source) 2 =
          pureWZ2LineClassNormalizationLinear lambda
              (wz1PaperDirection source) 2 /
            ‖pureWZ2LineClassNormalizationLinear lambda
              (wz1PaperDirection source)‖ := by
      simp only [pureWZ2LineClassNormalizationDirection,
        pureWZ2LineClassNormalizationLinearEquiv_apply, PiLp.smul_apply]
      ring
    change (1 / 2 : ℝ) ≤
      pureWZ2LineClassNormalizationDirection lambda lambdaPos
        (wz1PaperDirection source) 2
    rw [heq]
    exact hratio
  have hzero := wz1TubeAxisZeroPoint_lineClassNormalizationTube
    (targetDelta := targetDelta) center hlambda source hsourceVertical
  exact ⟨hvertical, by rw [hzero]; exact hzeroX,
    by rw [hzero]; exact hzeroY⟩

end Kakeya.Assouad

end
