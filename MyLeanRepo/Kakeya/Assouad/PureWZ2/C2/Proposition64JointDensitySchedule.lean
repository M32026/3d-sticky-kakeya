import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64JointPaperEDDensity
import MyLeanRepo.Kakeya.Assouad.ConstantAbsorption

/-!
# P0-uniform joint-density schedule for Proposition 6.4

The paper chooses the hierarchy depth and losses before the runtime tube
family.  This file chooses one source-scale cutoff in that order and then
constructs the runtime joint-density scalar receipt from the defining
normalization, half-height, and final-scale identities.
-/

noncomputable section

namespace Kakeya.Assouad

/-- The fixed part of the pre-ED mass coefficient after the exact
`halfHeight` cancellation. -/
noncomputable def pureWZ2Proposition64JointDensityFixedMassCoefficient :
    ENNReal :=
  ENNReal.ofReal (pureWZ2Proposition64Lemma35Scale ^ 3) *
    (ENNReal.ofReal (pureWZ2Proposition64Lemma35Width ^ 3 / 27) *
      (ENNReal.ofReal
          (2 / pureWZ2Proposition64NormalizationConstant) *
        ENNReal.ofReal (1 / 6)))

/-- The fixed target coefficient after writing
`finalDelta = (45 * scale) * sourceDelta`. -/
noncomputable def pureWZ2Proposition64JointDensityTargetCoefficient
    (structuralLoss : ℝ) : ENNReal :=
  294 *
    (55296 * Kakeya.deltaTubeVolume 1) *
    Kakeya.realRpowENN
      (45 * pureWZ2Proposition64Lemma35Scale)
      (structuralLoss + 2)

theorem pureWZ2Proposition64JointDensityFixedMassCoefficient_pos :
    0 < pureWZ2Proposition64JointDensityFixedMassCoefficient := by
  have hscale :
      0 < ENNReal.ofReal (pureWZ2Proposition64Lemma35Scale ^ 3) :=
    ENNReal.ofReal_pos.mpr <|
      pow_pos pureWZ2Proposition64Lemma35Scale_pos 3
  have hwidthReal : 0 < pureWZ2Proposition64Lemma35Width := by
    unfold pureWZ2Proposition64Lemma35Width
    exact one_div_pos.mpr <|
      mul_pos (by norm_num) pureWZ2Proposition64Lemma35Scale_pos
  have hwidth :
      0 < ENNReal.ofReal
        (pureWZ2Proposition64Lemma35Width ^ 3 / 27) :=
    ENNReal.ofReal_pos.mpr <|
      div_pos (pow_pos hwidthReal 3) (by norm_num)
  have hnormalization :
      0 < ENNReal.ofReal
        (2 / pureWZ2Proposition64NormalizationConstant) :=
    ENNReal.ofReal_pos.mpr <|
      div_pos (by norm_num)
        pureWZ2Proposition64NormalizationConstant_pos
  have hsixth : 0 < ENNReal.ofReal (1 / 6) := by norm_num
  have hlast :
      0 < ENNReal.ofReal
          (2 / pureWZ2Proposition64NormalizationConstant) *
        ENNReal.ofReal (1 / 6) :=
    ENNReal.mul_pos hnormalization.ne' hsixth.ne'
  have hrest :
      0 < ENNReal.ofReal
          (pureWZ2Proposition64Lemma35Width ^ 3 / 27) *
        (ENNReal.ofReal
            (2 / pureWZ2Proposition64NormalizationConstant) *
          ENNReal.ofReal (1 / 6)) :=
    ENNReal.mul_pos hwidth.ne' hlast.ne'
  unfold pureWZ2Proposition64JointDensityFixedMassCoefficient
  exact ENNReal.mul_pos hscale.ne' hrest.ne'

theorem pureWZ2Proposition64JointDensityFixedMassCoefficient_ne_top :
    pureWZ2Proposition64JointDensityFixedMassCoefficient ≠ ⊤ := by
  unfold pureWZ2Proposition64JointDensityFixedMassCoefficient
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top <|
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top <|
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top

theorem pureWZ2Proposition64JointDensityTargetCoefficient_ne_top
    (structuralLoss : ℝ) :
    pureWZ2Proposition64JointDensityTargetCoefficient structuralLoss ≠ ⊤ := by
  unfold pureWZ2Proposition64JointDensityTargetCoefficient
  exact ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (by norm_num) <|
      ENNReal.mul_ne_top (by norm_num) deltaTubeVolume_one_ne_top) <|
        by simp [Kakeya.realRpowENN]

/-- Exact cancellation of the short-slab height in the affine Jacobian. -/
theorem pureWZ2Proposition64_jointDensityMassCoefficient_eq
    {sourceDelta densityLoss halfHeight : ℝ}
    (hhalfHeight : 0 < halfHeight) :
    pureWZ2Proposition64JointDensityMassCoefficient
        sourceDelta densityLoss
        pureWZ2Proposition64NormalizationConstant halfHeight =
      pureWZ2Proposition64JointDensityFixedMassCoefficient *
        Kakeya.realRpowENN sourceDelta densityLoss := by
  have hnormalization :
      0 < pureWZ2Proposition64NormalizationConstant :=
    pureWZ2Proposition64NormalizationConstant_pos
  have hjacobian :
      ENNReal.ofReal
          (1 /
            (pureWZ2Proposition64NormalizationConstant * halfHeight)) *
          ENNReal.ofReal (2 * halfHeight) =
        ENNReal.ofReal
          (2 / pureWZ2Proposition64NormalizationConstant) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp [hnormalization.ne', hhalfHeight.ne']
  unfold pureWZ2Proposition64JointDensityMassCoefficient
    pureWZ2Proposition64JointDensityFixedMassCoefficient
  calc
    _ = ENNReal.ofReal (pureWZ2Proposition64Lemma35Scale ^ 3) *
        (ENNReal.ofReal (pureWZ2Proposition64Lemma35Width ^ 3 / 27) *
          ((ENNReal.ofReal
              (1 /
                (pureWZ2Proposition64NormalizationConstant * halfHeight)) *
            ENNReal.ofReal (2 * halfHeight)) *
            (ENNReal.ofReal (1 / 6) *
              Kakeya.realRpowENN sourceDelta densityLoss))) := by ring
    _ = _ := by rw [hjacobian]; ring

/-- Exact fixed-multiple expansion of the final-scale target power. -/
theorem pureWZ2Proposition64_jointDensityTarget_eq
    {sourceDelta structuralLoss : ℝ}
    (hsourceDelta : 0 < sourceDelta) :
    294 *
        (Kakeya.realRpowENN
            (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
              structuralLoss *
          ((55296 * Kakeya.deltaTubeVolume 1) *
            Kakeya.realRpowENN
              (pureWZ2Proposition64Lemma35FinalDelta sourceDelta) 2)) =
      pureWZ2Proposition64JointDensityTargetCoefficient structuralLoss *
        Kakeya.realRpowENN sourceDelta (structuralLoss + 2) := by
  let scale : ℝ := 45 * pureWZ2Proposition64Lemma35Scale
  have hscale : 0 < scale := by
    dsimp only [scale]
    exact mul_pos (by norm_num)
      pureWZ2Proposition64Lemma35Scale_pos
  have hmul : ∀ exponent : ℝ,
      Kakeya.realRpowENN (scale * sourceDelta) exponent =
        Kakeya.realRpowENN scale exponent *
          Kakeya.realRpowENN sourceDelta exponent := by
    intro exponent
    simp only [Kakeya.realRpowENN]
    calc
      ENNReal.ofReal ((scale * sourceDelta).rpow exponent) =
          ENNReal.ofReal
            (scale.rpow exponent * sourceDelta.rpow exponent) := by
              exact congrArg ENNReal.ofReal
                (Real.mul_rpow hscale.le hsourceDelta.le)
      _ = _ := ENNReal.ofReal_mul
        (Real.rpow_nonneg hscale.le exponent)
  unfold pureWZ2Proposition64Lemma35FinalDelta
  change 294 *
      (Kakeya.realRpowENN (scale * sourceDelta) structuralLoss *
        ((55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN (scale * sourceDelta) 2)) = _
  rw [hmul structuralLoss, hmul 2]
  unfold pureWZ2Proposition64JointDensityTargetCoefficient
  change _ =
    294 * (55296 * Kakeya.deltaTubeVolume 1) *
      Kakeya.realRpowENN scale (structuralLoss + 2) *
      Kakeya.realRpowENN sourceDelta (structuralLoss + 2)
  rw [realRpowENN_add hscale, realRpowENN_add hsourceDelta]
  ring

/--
P0 schedule selected before every runtime family.

The strict gap `densityLoss < structuralLoss` is necessary: the critical
floor API supplies no positive lower bound for an arbitrary later
`structuralLoss`, while fixed numerical constants require a positive power
gap for absorption.
-/
structure PureWZ2Proposition64JointDensitySchedule
    (levelCount : ℕ) (densityLoss structuralLoss targetDelta₀ : ℝ) where
  levelCount_ge_two : 2 ≤ levelCount
  densityLoss_pos : 0 < densityLoss
  loss_gap : densityLoss < structuralLoss
  targetDelta₀_pos : 0 < targetDelta₀
  sourceDelta₀ : ℝ
  sourceDelta₀_pos : 0 < sourceDelta₀
  sourceDelta₀_le_one : sourceDelta₀ ≤ 1
  finalDelta_le_target :
    ∀ {sourceDelta : ℝ}, 0 < sourceDelta →
      sourceDelta ≤ sourceDelta₀ →
      pureWZ2Proposition64Lemma35FinalDelta sourceDelta ≤ targetDelta₀
  average_absorption :
    ∀ {sourceDelta halfHeight : ℝ}, 0 < sourceDelta →
      sourceDelta ≤ sourceDelta₀ → 0 < halfHeight →
      294 *
          (Kakeya.realRpowENN
              (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
                structuralLoss *
            ((55296 * Kakeya.deltaTubeVolume 1) *
              Kakeya.realRpowENN
                (pureWZ2Proposition64Lemma35FinalDelta sourceDelta) 2)) ≤
        pureWZ2Proposition64JointDensityMassCoefficient
            sourceDelta densityLoss
            pureWZ2Proposition64NormalizationConstant halfHeight *
          Kakeya.realRpowENN sourceDelta 2

/-- Choose the complete joint-density source cutoff before runtime data. -/
theorem exists_pureWZ2Proposition64JointDensitySchedule
    {levelCount : ℕ} {densityLoss structuralLoss targetDelta₀ : ℝ}
    (hlevelCount : 2 ≤ levelCount)
    (hdensityLoss : 0 < densityLoss)
    (hlossGap : densityLoss < structuralLoss)
    (htargetDelta₀ : 0 < targetDelta₀) :
    Nonempty (PureWZ2Proposition64JointDensitySchedule
      levelCount densityLoss structuralLoss targetDelta₀) := by
  let fixedMass :=
    pureWZ2Proposition64JointDensityFixedMassCoefficient
  let targetCoefficient :=
    pureWZ2Proposition64JointDensityTargetCoefficient structuralLoss
  let ratio := targetCoefficient * fixedMass⁻¹
  have hratioTop : ratio ≠ ⊤ := by
    exact ENNReal.mul_ne_top
      (pureWZ2Proposition64JointDensityTargetCoefficient_ne_top
        structuralLoss)
      (ENNReal.inv_ne_top.mpr
        pureWZ2Proposition64JointDensityFixedMassCoefficient_pos.ne')
  let gap := structuralLoss - densityLoss
  have hgap : 0 < gap := by
    dsimp only [gap]
    linarith
  rcases exists_delta_realRpowENN_bound ratio hratioTop hgap with
    ⟨absorptionDelta₀, habsorptionDelta₀, habsorptionDelta₀One,
      habsorption⟩
  let targetSourceDelta₀ :=
    targetDelta₀ / (45 * pureWZ2Proposition64Lemma35Scale)
  have htargetSourceDelta₀ : 0 < targetSourceDelta₀ := by
    dsimp only [targetSourceDelta₀]
    exact div_pos htargetDelta₀ <|
      mul_pos (by norm_num) pureWZ2Proposition64Lemma35Scale_pos
  let sourceDelta₀ := min absorptionDelta₀ targetSourceDelta₀
  refine ⟨{
    levelCount_ge_two := hlevelCount
    densityLoss_pos := hdensityLoss
    loss_gap := hlossGap
    targetDelta₀_pos := htargetDelta₀
    sourceDelta₀ := sourceDelta₀
    sourceDelta₀_pos := lt_min habsorptionDelta₀ htargetSourceDelta₀
    sourceDelta₀_le_one :=
      (min_le_left _ _).trans habsorptionDelta₀One
    finalDelta_le_target := ?_
    average_absorption := ?_ }⟩
  · intro sourceDelta hsourceDelta hsourceSmall
    have htarget :
        sourceDelta ≤ targetSourceDelta₀ :=
      hsourceSmall.trans (min_le_right _ _)
    unfold pureWZ2Proposition64Lemma35FinalDelta
    dsimp only [targetSourceDelta₀] at htarget
    apply (le_div_iff₀
      (mul_pos (by norm_num)
        pureWZ2Proposition64Lemma35Scale_pos)).mp at htarget
    nlinarith
  · intro sourceDelta halfHeight hsourceDelta hsourceSmall hhalfHeight
    have hratio :
        ratio ≤ Kakeya.realRpowENN sourceDelta (-gap) :=
      habsorption sourceDelta hsourceDelta
        (hsourceSmall.trans (min_le_left _ _))
    have hmassZero : fixedMass ≠ 0 :=
      pureWZ2Proposition64JointDensityFixedMassCoefficient_pos.ne'
    have hmassTop : fixedMass ≠ ⊤ :=
      pureWZ2Proposition64JointDensityFixedMassCoefficient_ne_top
    have hratioCancel : ratio * fixedMass = targetCoefficient := by
      dsimp only [ratio]
      rw [mul_assoc, ENNReal.inv_mul_cancel hmassZero hmassTop, mul_one]
    rw [pureWZ2Proposition64_jointDensityTarget_eq hsourceDelta]
    rw [pureWZ2Proposition64_jointDensityMassCoefficient_eq hhalfHeight]
    change targetCoefficient *
        Kakeya.realRpowENN sourceDelta (structuralLoss + 2) ≤
      fixedMass * Kakeya.realRpowENN sourceDelta densityLoss *
        Kakeya.realRpowENN sourceDelta 2
    have hmain :
        targetCoefficient *
            Kakeya.realRpowENN sourceDelta (structuralLoss + 2) ≤
          fixedMass *
            Kakeya.realRpowENN sourceDelta (densityLoss + 2) := by
      calc
        targetCoefficient *
            Kakeya.realRpowENN sourceDelta (structuralLoss + 2) =
          (ratio * fixedMass) *
            Kakeya.realRpowENN sourceDelta (structuralLoss + 2) := by
              rw [hratioCancel]
        _ ≤ Kakeya.realRpowENN sourceDelta (-gap) * fixedMass *
            Kakeya.realRpowENN sourceDelta (structuralLoss + 2) := by
              gcongr
        _ = fixedMass *
            (Kakeya.realRpowENN sourceDelta (-gap) *
              Kakeya.realRpowENN sourceDelta (structuralLoss + 2)) := by ring
        _ = fixedMass *
            Kakeya.realRpowENN sourceDelta (densityLoss + 2) := by
              rw [← realRpowENN_add hsourceDelta]
              congr 2
              dsimp only [gap]
              ring
    calc
      targetCoefficient *
          Kakeya.realRpowENN sourceDelta (structuralLoss + 2) ≤
        fixedMass *
          Kakeya.realRpowENN sourceDelta (densityLoss + 2) := hmain
      _ = fixedMass * Kakeya.realRpowENN sourceDelta densityLoss *
          Kakeya.realRpowENN sourceDelta 2 := by
            rw [realRpowENN_add hsourceDelta]
            ring

namespace PureWZ2Proposition64JointDensitySchedule

/-- Instantiate the density schedule at its own preselected structural loss.
This is the production P7 interface and carries no critical-floor token. -/
theorem runtime_receipt_exact
    {levelCount : ℕ}
    {densityLoss structuralLoss targetDelta₀ : ℝ}
    (schedule : PureWZ2Proposition64JointDensitySchedule
      levelCount densityLoss structuralLoss targetDelta₀)
    {sigma workLoss sourceDelta runtimeTargetDelta₀ : ℝ}
    (hsourceDelta : 0 < sourceDelta)
    (hsourceCutoff : sourceDelta ≤ schedule.sourceDelta₀)
    (quantitativeOutput : PureWZ2QuantitativeNormalizedHierarchyOutput
      sigma workLoss sourceDelta)
    {hsourceSmall : sourceDelta ≤
      pureWZ2Proposition64Lemma35SourceCeiling runtimeTargetDelta₀}
    (_geometry :
      PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData
        quantitativeOutput.normalized hsourceSmall)
    (hlevelCount :
      quantitativeOutput.normalized.hierarchy.hierarchy.levelCount =
        levelCount)
    (hdensityLoss : quantitativeOutput.densityLoss = densityLoss) :
    PureWZ2Proposition64JointDensityScalarReceipt
      sourceDelta
      (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
      quantitativeOutput.densityLoss
      quantitativeOutput.normalized.prepared.normalization
      quantitativeOutput.normalized.prepared.slab.halfHeight
      structuralLoss targetDelta₀ := by
  have hhalfHeight_eq :
      quantitativeOutput.normalized.prepared.slab.halfHeight =
        pureWZ2Proposition64HalfHeight sourceDelta levelCount := by
    rw [quantitativeOutput.normalized.prepared.slab.halfHeight_eq,
      hlevelCount]
  have hhalfHeight :
      0 < quantitativeOutput.normalized.prepared.slab.halfHeight :=
    hhalfHeight_eq.symm ▸
      pureWZ2Proposition64HalfHeight_pos hsourceDelta
  have hscheduled := schedule.average_absorption
    hsourceDelta hsourceCutoff hhalfHeight
  rw [← hdensityLoss] at hscheduled
  rw [← quantitativeOutput.normalized.normalization_eq] at hscheduled
  exact {
    finalDelta_le_floor :=
      schedule.finalDelta_le_target hsourceDelta hsourceCutoff
    average_absorption := hscheduled }

/-- Instantiate the pre-runtime schedule on one runtime hierarchy and floor.
Normalization and half-height facts are projected from the output itself. -/
theorem runtime_receipt
    {levelCount : ℕ}
    {densityLoss structuralLoss targetDelta₀ : ℝ}
    (schedule : PureWZ2Proposition64JointDensitySchedule
      levelCount densityLoss structuralLoss targetDelta₀)
    {sigma workLoss sourceDelta runtimeTargetDelta₀ outputLoss : ℝ}
    (hsourceDelta : 0 < sourceDelta)
    (hsourceCutoff : sourceDelta ≤ schedule.sourceDelta₀)
    (quantitativeOutput : PureWZ2QuantitativeNormalizedHierarchyOutput
      sigma workLoss sourceDelta)
    {hsourceSmall : sourceDelta ≤
      pureWZ2Proposition64Lemma35SourceCeiling runtimeTargetDelta₀}
    (_geometry : PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData
      quantitativeOutput.normalized hsourceSmall)
    (floor : PureWZ2CroppedCriticalFloorSelectionData
      sigma outputLoss outputLoss)
    (hlevelCount :
      quantitativeOutput.normalized.hierarchy.hierarchy.levelCount =
        levelCount)
    (hdensityLoss : quantitativeOutput.densityLoss = densityLoss)
    (hfloorLoss : structuralLoss ≤ floor.structuralLoss)
    (htargetFloor : targetDelta₀ ≤ floor.delta₀) :
    PureWZ2Proposition64JointDensityScalarReceipt
      sourceDelta
      (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
      quantitativeOutput.densityLoss
      quantitativeOutput.normalized.prepared.normalization
      quantitativeOutput.normalized.prepared.slab.halfHeight
      floor.structuralLoss floor.delta₀ := by
  have hfinalTarget :=
    schedule.finalDelta_le_target hsourceDelta hsourceCutoff
  have hfinalOne :
      pureWZ2Proposition64Lemma35FinalDelta sourceDelta ≤ 1 := by
    exact hfinalTarget.trans
      (htargetFloor.trans floor.delta₀_le_one)
  have hhalfHeight_eq :
      quantitativeOutput.normalized.prepared.slab.halfHeight =
        pureWZ2Proposition64HalfHeight sourceDelta levelCount := by
    rw [quantitativeOutput.normalized.prepared.slab.halfHeight_eq,
      hlevelCount]
  have hhalfHeight :
      0 < quantitativeOutput.normalized.prepared.slab.halfHeight :=
    hhalfHeight_eq.symm ▸
      pureWZ2Proposition64HalfHeight_pos hsourceDelta
  have hscheduled := schedule.average_absorption
    hsourceDelta hsourceCutoff hhalfHeight
  rw [← hdensityLoss] at hscheduled
  rw [← quantitativeOutput.normalized.normalization_eq] at hscheduled
  refine {
    finalDelta_le_floor := hfinalTarget.trans htargetFloor
    average_absorption := ?_ }
  calc
    294 *
        (Kakeya.realRpowENN
            (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
              floor.structuralLoss *
          ((55296 * Kakeya.deltaTubeVolume 1) *
            Kakeya.realRpowENN
              (pureWZ2Proposition64Lemma35FinalDelta sourceDelta) 2)) ≤
      294 *
        (Kakeya.realRpowENN
            (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
              structuralLoss *
          ((55296 * Kakeya.deltaTubeVolume 1) *
            Kakeya.realRpowENN
              (pureWZ2Proposition64Lemma35FinalDelta sourceDelta) 2)) := by
      gcongr
      simp only [Kakeya.realRpowENN]
      apply ENNReal.ofReal_mono
      exact Real.rpow_le_rpow_of_exponent_ge
        (by
          unfold pureWZ2Proposition64Lemma35FinalDelta
          exact mul_pos
            (mul_pos (by norm_num)
              pureWZ2Proposition64Lemma35Scale_pos)
            hsourceDelta)
        hfinalOne hfloorLoss
    _ ≤ _ := hscheduled

/-- Direct adapter to the canonical joint-ED density constructor. -/
theorem exists_jointPaperED_with_density
    {levelCount : ℕ}
    {densityLoss structuralLoss targetDelta₀ : ℝ}
    (schedule : PureWZ2Proposition64JointDensitySchedule
      levelCount densityLoss structuralLoss targetDelta₀)
    {sigma workLoss sourceDelta runtimeTargetDelta₀ outputLoss : ℝ}
    (hsourceDelta : 0 < sourceDelta)
    (hsourceCutoff : sourceDelta ≤ schedule.sourceDelta₀)
    (quantitativeOutput : PureWZ2QuantitativeNormalizedHierarchyOutput
      sigma workLoss sourceDelta)
    {hsourceSmall : sourceDelta ≤
      pureWZ2Proposition64Lemma35SourceCeiling runtimeTargetDelta₀}
    (geometry :
      PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData
        quantitativeOutput.normalized hsourceSmall)
    (frostman :
      PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData.SelectedSourceFrostmanReceipt
        geometry)
    (floor : PureWZ2CroppedCriticalFloorSelectionData
      sigma outputLoss outputLoss)
    (hlevelCount :
      quantitativeOutput.normalized.hierarchy.hierarchy.levelCount =
        levelCount)
    (hdensityLoss : quantitativeOutput.densityLoss = densityLoss)
    (hfloorLoss : structuralLoss ≤ floor.structuralLoss)
    (htargetFloor : targetDelta₀ ≤ floor.delta₀) :
    let K := pureWZ2Proposition64PaperConflictPackingDegree sourceDelta
      quantitativeOutput.normalized.prepared.normalization
      (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
      quantitativeOutput.normalized.prepared.slab.halfHeight
    ∃ joint : PureWZ2Proposition64JointPaperEDSelectionData
        geometry.cleanup.finalShading K,
      joint.finalShading.IsLambdaDense
        (Kakeya.realRpowENN
          (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
            floor.structuralLoss) := by
  let receipt := schedule.runtime_receipt hsourceDelta hsourceCutoff
    quantitativeOutput geometry floor hlevelCount hdensityLoss
      hfloorLoss htargetFloor
  exact geometry.exists_jointPaperED_with_density
    quantitativeOutput frostman floor receipt

end PureWZ2Proposition64JointDensitySchedule

end Kakeya.Assouad

end
