import MyLeanRepo.Kakeya.Assouad.PureWZ2.CompleteFiberExtremal
import MyLeanRepo.Kakeya.Assouad.PureWZ2.NormalizationRigidCropGeometryProducer
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12OrdinaryNestedCover
import MyLeanRepo.Kakeya.Assouad.WZ1.DirectionInnerProductBound

/-!
# Canonical orientation of one complete strict fiber

Independently reverse the stored parametrization of each tube toward one
common parent direction.  Ordinary carriers and midpoints are unchanged.
The oriented family supplies the common rigid-frame geometry, and the
resulting crop certificate pulls back to the original complete fiber.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- Orient one tube toward a fixed reference direction without changing it. -/
def pureWZ2OrientTubeToward
    {delta rho : ℝ}
    (reference : Kakeya.DeltaTube rho)
    (tube : Kakeya.DeltaTube delta) :
    Kakeya.DeltaTube delta :=
  if 0 ≤ inner ℝ reference.direction tube.direction then
    tube
  else
    reverseTube tube

@[simp] theorem pureWZ2OrientTubeToward_carrier
    {delta rho : ℝ}
    (reference : Kakeya.DeltaTube rho)
    (tube : Kakeya.DeltaTube delta) :
    (pureWZ2OrientTubeToward reference tube).carrier =
      tube.carrier := by
  unfold pureWZ2OrientTubeToward
  split_ifs
  · rfl
  · exact reverseTube_carrier tube

@[simp] theorem pureWZ2OrientTubeToward_midpoint
    {delta rho : ℝ}
    (reference : Kakeya.DeltaTube rho)
    (tube : Kakeya.DeltaTube delta) :
    wz2PaperTubeMidpoint
        (pureWZ2OrientTubeToward reference tube) =
      wz2PaperTubeMidpoint tube := by
  unfold pureWZ2OrientTubeToward
  split_ifs
  · rfl
  · exact wz2PaperTubeMidpoint_reverse tube

/-- Orient every member of an indexed family toward the same parent. -/
def pureWZ2OrientFamilyToward
    {delta rho : ℝ}
    (reference : Kakeya.DeltaTube rho)
    (family : Kakeya.Streamlined.TubeFamily delta) :
    Kakeya.Streamlined.TubeFamily delta where
  card := family.card
  tube index :=
    pureWZ2OrientTubeToward reference (family.tube index)

@[simp] theorem pureWZ2OrientFamilyToward_card
    {delta rho : ℝ}
    (reference : Kakeya.DeltaTube rho)
    (family : Kakeya.Streamlined.TubeFamily delta) :
    (pureWZ2OrientFamilyToward reference family).card =
      family.card :=
  rfl

@[simp] theorem pureWZ2OrientFamilyToward_carrier
    {delta rho : ℝ}
    (reference : Kakeya.DeltaTube rho)
    (family : Kakeya.Streamlined.TubeFamily delta)
    (index : Fin family.card) :
    ((pureWZ2OrientFamilyToward reference family).tube index).carrier =
      (family.tube index).carrier :=
  pureWZ2OrientTubeToward_carrier reference (family.tube index)

@[simp] theorem wz1TubeAxisZeroPoint_reverse
    {delta : ℝ}
    {tube : Kakeya.DeltaTube delta}
    (vertical : tube.direction (2 : Fin 3) ≠ 0) :
    wz1TubeAxisZeroPoint (reverseTube tube) =
      wz1TubeAxisZeroPoint tube := by
  unfold wz1TubeAxisZeroPoint reverseTube
  apply PiLp.ext
  intro coordinate
  simp only [PiLp.add_apply, PiLp.neg_apply, PiLp.sub_apply,
    PiLp.smul_apply, smul_eq_mul]
  field_simp [vertical]
  ring

@[simp] theorem wz1PaperDirection_reverse
    {delta : ℝ}
    {tube : Kakeya.DeltaTube delta}
    (vertical : tube.direction (2 : Fin 3) ≠ 0) :
    wz1PaperDirection (reverseTube tube) =
      wz1PaperDirection tube := by
  unfold wz1PaperDirection reverseTube
  by_cases nonnegative : 0 ≤ tube.direction (2 : Fin 3)
  · have positive : 0 < tube.direction (2 : Fin 3) := by
      exact lt_of_le_of_ne nonnegative (Ne.symm vertical)
    rw [if_pos nonnegative]
    have negativeReverse :
        ¬ 0 ≤ (-tube.direction) (2 : Fin 3) := by
      simp only [PiLp.neg_apply]
      linarith
    rw [if_neg negativeReverse]
    simp
  · rw [if_neg nonnegative]
    have positiveReverse :
        0 ≤ (-tube.direction) (2 : Fin 3) := by
      simp only [PiLp.neg_apply]
      linarith
    rw [if_pos positiveReverse]

theorem WZ1PaperTubeInLineClass.reverse_iff
    {delta : ℝ}
    (tube : Kakeya.DeltaTube delta) :
    WZ1PaperTubeInLineClass (reverseTube tube) ↔
      WZ1PaperTubeInLineClass tube := by
  constructor
  · intro reversed
    have originalVertical :
        tube.direction (2 : Fin 3) ≠ 0 := by
      intro zero
      have vertical := reversed.vertical
      simp [reverseTube, zero] at vertical
      norm_num at vertical
    unfold WZ1PaperTubeInLineClass at reversed ⊢
    rw [← wz1PaperDirection_reverse originalVertical,
      ← wz1TubeAxisZeroPoint_reverse originalVertical]
    exact reversed
  · intro original
    have vertical :
        tube.direction (2 : Fin 3) ≠ 0 := by
      intro zero
      have bound := original.vertical
      rw [zero, abs_zero] at bound
      norm_num at bound
    unfold WZ1PaperTubeInLineClass at original ⊢
    rw [wz1PaperDirection_reverse vertical,
      wz1TubeAxisZeroPoint_reverse vertical]
    exact original

@[simp] theorem pureWZ2RigidImageTube_reverse
    (frame : Point3 ≃ᵃⁱ[ℝ] Point3)
    {delta : ℝ}
    (tube : Kakeya.DeltaTube delta) :
    pureWZ2RigidImageTube frame (reverseTube tube) =
      reverseTube (pureWZ2RigidImageTube frame tube) := by
  rw [Kakeya.DeltaTube.mk.injEq]
  constructor
  · change
      frame (tube.base + tube.direction) =
        frame tube.base +
          frame.linearIsometryEquiv tube.direction
    simpa [vadd_eq_add, add_comm] using
      frame.map_vadd tube.base tube.direction
  · simp [pureWZ2RigidImageTube, reverseTube]

theorem pureWZ2_orientTubeToward_inner_ge_half
    {delta rho : ℝ}
    (deltaNonnegative : 0 ≤ delta)
    (rhoNonnegative : 0 ≤ rho)
    (rhoQuarter : rho ≤ 1 / 4)
    (reference : Kakeya.DeltaTube rho)
    (tube : Kakeya.DeltaTube delta)
    (contained : tube.carrier ⊆ reference.carrier) :
    1 / 2 ≤
      inner ℝ reference.direction
        (pureWZ2OrientTubeToward reference tube).direction := by
  rcases
      direction_inner_product_bound
        deltaNonnegative tube reference contained
        rhoNonnegative rhoQuarter
    with
    ⟨sign, signCases, lower⟩
  have productNonnegative :
      0 ≤ rho * (1 / 4 - rho) :=
    mul_nonneg rhoNonnegative (sub_nonneg.mpr rhoQuarter)
  have radicandLower :
      (3 / 4 : ℝ) ≤ 1 - 4 * rho ^ 2 := by
    nlinarith
  have radicandNonnegative :
      0 ≤ 1 - 4 * rho ^ 2 :=
    radicandLower.trans' (by norm_num)
  have rootSquare :
      (Real.sqrt (1 - 4 * rho ^ 2)) ^ 2 =
        1 - 4 * rho ^ 2 :=
    Real.sq_sqrt radicandNonnegative
  have rootNonnegative :
      0 ≤ Real.sqrt (1 - 4 * rho ^ 2) :=
    Real.sqrt_nonneg _
  have rootHalf :
      (1 / 2 : ℝ) ≤ Real.sqrt (1 - 4 * rho ^ 2) := by
    nlinarith
  have lowerHalf :
      (1 / 2 : ℝ) ≤
        inner ℝ tube.direction (sign • reference.direction) :=
    rootHalf.trans lower
  unfold pureWZ2OrientTubeToward
  by_cases aligned :
      0 ≤ inner ℝ reference.direction tube.direction
  · rw [if_pos aligned]
    rcases signCases with rfl | rfl
    · simpa [real_inner_comm] using lowerHalf
    · simp only [neg_one_smul, inner_neg_right] at lowerHalf
      have opposite :
          (1 / 2 : ℝ) ≤
            -inner ℝ reference.direction tube.direction := by
        simpa [real_inner_comm] using lowerHalf
      linarith
  · rw [if_neg aligned]
    rcases signCases with rfl | rfl
    · simp only [one_smul] at lowerHalf
      have same :
          (1 / 2 : ℝ) ≤
            inner ℝ reference.direction tube.direction := by
        simpa [real_inner_comm] using lowerHalf
      exact False.elim (aligned (by linarith))
    · simpa [reverseTube, real_inner_comm] using lowerHalf

/--
One strict parent fiber, canonically oriented toward its parent, supplies the
whole-family rigid-crop frame geometry without any finite selection.
-/
def pureWZ2RigidCropFrameInput_of_parent_containment
    {delta rho : ℝ}
    (deltaPositive : 0 < delta)
    (rhoPositive : 0 < rho)
    (rhoQuarter : rho ≤ 1 / 4)
    (family : Kakeya.Streamlined.TubeFamily delta)
    (parent : Kakeya.DeltaTube rho)
    (contained :
      ∀ index, (family.tube index).carrier ⊆ parent.carrier)
    (midpointBudget :
      5 * rho ≤ Real.sqrt 3 / 32 + delta) :
    PureWZ2RigidCropFrameInput
      (pureWZ2OrientFamilyToward parent family) where
  centerDirection := parent.direction
  centerDirection_unit := parent.direction_unit
  commonPoint := wz2PaperTubeMidpoint parent
  halfStart := 0
  halfStart_cases := Or.inl rfl
  direction_cone index :=
    pureWZ2_orientTubeToward_inner_ge_half
      deltaPositive.le rhoPositive.le rhoQuarter
      parent (family.tube index) (contained index)
  segment_near index := by
    refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
    have midpointDistance :=
      wz2PaperSourceMidpoint_dist_le_five_mul_of_carrier_subset
        deltaPositive rhoPositive
        (family.tube index) parent (contained index)
    change
      ‖wz2PaperTubeMidpoint
            (pureWZ2OrientTubeToward parent (family.tube index)) -
          wz2PaperTubeMidpoint parent‖ ≤
        Real.sqrt 3 / 32 + delta
    rw [pureWZ2OrientTubeToward_midpoint]
    have midpointDistance' :
        ‖wz2PaperTubeMidpoint (family.tube index) -
            wz2PaperTubeMidpoint parent‖ ≤
          5 * rho := by
      simpa [dist_eq_norm] using midpointDistance
    exact midpointDistance'.trans midpointBudget

/--
An exact-index rigid crop certificate.  Unlike the generic finite-selection
certificate, its cropped family is definitionally the common rigid image of
the supplied family.
-/
structure PureWZ2ExactRigidCropFrameCertificate
    {delta : ℝ}
    (family : Kakeya.Streamlined.TubeFamily delta) where
  frame : Point3 ≃ᵃⁱ[ℝ] Point3
  carrier_margin :
    ∀ index point,
      point ∈
          ((pureWZ2RigidImageFamily frame family).tube index).carrier →
        |point 0| ≤ 1 - delta ∧
          |point 1| ≤ 1 - delta ∧
          |point 2| ≤ 1 - delta
  axisBox :
    ∀ index,
      ((pureWZ2RigidImageFamily frame family).tube index).carrier ⊆
        Kakeya.Streamlined.axisBox 2 2 2
  line_class :
    WZ1PaperIsLineClass
      (pureWZ2RigidImageFamily frame family)

namespace PureWZ2ExactRigidCropFrameCertificate

/-- Every later pure subfamily inherits the same exact common rigid frame. -/
def subfamily
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (certificate :
      PureWZ2ExactRigidCropFrameCertificate family)
    (selected : WZ2PaperPureTubeSubfamily family) :
    PureWZ2ExactRigidCropFrameCertificate selected.family where
  frame := certificate.frame
  carrier_margin index point pointMem := by
    have sourceMem :
        point ∈
          ((pureWZ2RigidImageFamily
            certificate.frame family).tube
            (selected.embedding index)).carrier := by
      change
        point ∈
          (pureWZ2RigidImageTube certificate.frame
            (selected.family.tube index)).carrier at pointMem
      change
        point ∈
          (pureWZ2RigidImageTube certificate.frame
            (family.tube (selected.embedding index))).carrier
      rw [← selected.tube_eq index]
      exact pointMem
    exact
      certificate.carrier_margin
        (selected.embedding index) point sourceMem
  axisBox index point pointMem := by
    have sourceMem :
        point ∈
          ((pureWZ2RigidImageFamily
            certificate.frame family).tube
            (selected.embedding index)).carrier := by
      change
        point ∈
          (pureWZ2RigidImageTube certificate.frame
            (selected.family.tube index)).carrier at pointMem
      change
        point ∈
          (pureWZ2RigidImageTube certificate.frame
            (family.tube (selected.embedding index))).carrier
      rw [← selected.tube_eq index]
      exact pointMem
    exact
      certificate.axisBox
        (selected.embedding index) sourceMem
  line_class index := by
    have sourceLine :=
      certificate.line_class (selected.embedding index)
    change
      WZ1PaperTubeInLineClass
        (pureWZ2RigidImageTube certificate.frame
          (selected.family.tube index))
    rw [selected.tube_eq index]
    exact sourceLine

end PureWZ2ExactRigidCropFrameCertificate

namespace PureWZ2CompleteFiberLocalizationData

/--
At a sufficiently small source scale, the scale-choice upper bound already
puts the actual parent radius inside the rigid-frame regime.
-/
theorem rho_quarter_of_source_power_small
    {sigma sourceLoss inputLoss delta : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {localized :
      PureWZ2ExtremalConfiguration sigma inputLoss delta}
    (data :
      PureWZ2CompleteFiberLocalizationData source localized)
    (sourcePowerSmall :
      Real.rpow delta sourceLoss ≤ 1 / 1000) :
    data.nearby.rho ≤ 1 / 4 := by
  exact data.rho_upper.le.trans (sourcePowerSmall.trans (by norm_num))

/--
The same source-scale bound makes all complete-fiber midpoints fit in the
fixed common-frame window.
-/
theorem midpoint_budget_of_source_power_small
    {sigma sourceLoss inputLoss delta : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {localized :
      PureWZ2ExtremalConfiguration sigma inputLoss delta}
    (data :
      PureWZ2CompleteFiberLocalizationData source localized)
    (sourcePowerSmall :
      Real.rpow delta sourceLoss ≤ 1 / 1000) :
    5 * data.nearby.rho ≤
      Real.sqrt 3 / 32 + delta := by
  have rhoSmall :
      data.nearby.rho ≤ 1 / 1000 :=
    data.rho_upper.le.trans sourcePowerSmall
  have sqrtLower : (1 : ℝ) ≤ Real.sqrt 3 :=
    Real.le_sqrt_of_sq_le (by norm_num)
  have deltaNonnegative : 0 ≤ delta :=
    localized.extremal.delta_pos.le
  nlinarith

/-- Canonically oriented common-frame geometry for the complete fiber. -/
def rigidCropFrameInput
    {sigma sourceLoss inputLoss delta : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {localized :
      PureWZ2ExtremalConfiguration sigma inputLoss delta}
    (data :
      PureWZ2CompleteFiberLocalizationData source localized)
    (rhoQuarter : data.nearby.rho ≤ 1 / 4)
    (midpointBudget :
      5 * data.nearby.rho ≤
        Real.sqrt 3 / 32 + delta) :
    PureWZ2RigidCropFrameInput
      (pureWZ2OrientFamilyToward
        (data.nearby.scaleData.coarse.tube data.parent)
        localized.family) :=
  pureWZ2RigidCropFrameInput_of_parent_containment
    localized.extremal.delta_pos
    data.nearby.scaleData.rho_pos
    rhoQuarter localized.family
    (data.nearby.scaleData.coarse.tube data.parent)
    data.parent_containment midpointBudget

/--
The rigid crop constructed on the oriented complete fiber is a certificate
for the original localized family because all indexed carriers agree.
-/
theorem exists_rigidCropFrameCertificate
    {sigma sourceLoss inputLoss delta : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {localized :
      PureWZ2ExtremalConfiguration sigma inputLoss delta}
    (data :
      PureWZ2CompleteFiberLocalizationData source localized)
    (deltaSmall :
      delta ≤ pureWZ2RigidCropGeometryDeltaThreshold)
    (rhoQuarter : data.nearby.rho ≤ 1 / 4)
    (midpointBudget :
      5 * data.nearby.rho ≤
        Real.sqrt 3 / 32 + delta) :
    Nonempty
      (PureWZ2ExactRigidCropFrameCertificate localized.family) := by
  let oriented :=
    pureWZ2OrientFamilyToward
      (data.nearby.scaleData.coarse.tube data.parent)
      localized.family
  let input : PureWZ2RigidCropFrameInput oriented :=
    data.rigidCropFrameInput rhoQuarter midpointBudget
  rcases
      exists_pureWZ2RigidCropFrameCertificate
        input localized.extremal.delta_pos deltaSmall
    with
    ⟨certificate⟩
  let croppedFamily :=
    pureWZ2RigidImageFamily certificate.frame localized.family
  have orientedCarrierEq :
      ∀ index,
        (certificate.croppedFamily.tube
            (certificate.indexEquiv index)).carrier =
          (croppedFamily.tube index).carrier := by
    intro index
    rw [certificate.ordinary_carrier_image_eq index,
      pureWZ2RigidImageFamily_carrier]
    congr 1
    exact
      pureWZ2OrientTubeToward_carrier
        (data.nearby.scaleData.coarse.tube data.parent)
        (localized.family.tube index)
  have margin :
      ∀ index point,
        point ∈ (croppedFamily.tube index).carrier →
          |point 0| ≤ 1 - delta ∧
            |point 1| ≤ 1 - delta ∧
            |point 2| ≤ 1 - delta := by
    intro index point pointMem
    apply
      certificate.carrier_margin
        (certificate.indexEquiv index) point
    rw [orientedCarrierEq index]
    exact pointMem
  have box :
      ∀ index,
        (croppedFamily.tube index).carrier ⊆
          Kakeya.Streamlined.axisBox 2 2 2 := by
    intro index point pointMem
    apply certificate.axisBox (certificate.indexEquiv index)
    rw [orientedCarrierEq index]
    exact pointMem
  have line : WZ1PaperIsLineClass croppedFamily := by
    intro index
    have orientedLine :=
      certificate.line_class (certificate.indexEquiv index)
    rw [certificate.cropped_tube_eq index] at orientedLine
    change
      WZ1PaperTubeInLineClass
        (pureWZ2RigidImageTube certificate.frame
          (localized.family.tube index))
    dsimp only [oriented, pureWZ2OrientFamilyToward] at orientedLine
    unfold pureWZ2OrientTubeToward at orientedLine
    split at orientedLine
    · exact orientedLine
    · rw [pureWZ2RigidImageTube_reverse] at orientedLine
      exact
        (WZ1PaperTubeInLineClass.reverse_iff
          (pureWZ2RigidImageTube certificate.frame
            (localized.family.tube index))).mp orientedLine
  refine
    ⟨{
      frame := certificate.frame
      carrier_margin := margin
      axisBox := box
      line_class := line
    }⟩

/--
Small-scale complete-fiber normalization with no direction, spatial-cell, or
half-segment pigeonhole.
-/
theorem exists_rigidCropFrameCertificate_of_source_power_small
    {sigma sourceLoss inputLoss delta : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {localized :
      PureWZ2ExtremalConfiguration sigma inputLoss delta}
    (data :
      PureWZ2CompleteFiberLocalizationData source localized)
    (deltaSmall :
      delta ≤ pureWZ2RigidCropGeometryDeltaThreshold)
    (sourcePowerSmall :
      Real.rpow delta sourceLoss ≤ 1 / 1000) :
    Nonempty
      (PureWZ2ExactRigidCropFrameCertificate localized.family) :=
  data.exists_rigidCropFrameCertificate
    deltaSmall
    (data.rho_quarter_of_source_power_small sourcePowerSmall)
    (data.midpoint_budget_of_source_power_small sourcePowerSmall)

end PureWZ2CompleteFiberLocalizationData

end Kakeya.Assouad

end
