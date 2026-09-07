import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64SelectedSourceFrostman
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64JointPaperEDDensity
import MyLeanRepo.Kakeya.Assouad.PureWZ2.FinitePureNearbyAssembly

/-!
# Quantitative Proposition 6.4 vertical assembly from exact receipts

This module fixes the paper-ED output by choosing it from one supplied
`SelectedSourceFrostmanReceipt`.  All later receipts are indexed by that exact
choice, the same quantitative hierarchy output, the same geometric prefix,
and the same cropped critical floor.

The scalar receipt contains only family-free inequalities.  The nearby
channel is represented by finitely many actual scale covers on the canonical
final family together with one rounding relation; the target nearby-CWA
receipt is constructed from those data inside this module.
-/

noncomputable section

namespace Kakeya.Assouad

namespace PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData

variable
    {sigma workLoss sourceDelta targetDelta₀ outputLoss : ℝ}
    {hsourceSmall : sourceDelta ≤
      pureWZ2Proposition64Lemma35SourceCeiling targetDelta₀}
    (quantitativeOutput : PureWZ2QuantitativeNormalizedHierarchyOutput
      sigma workLoss sourceDelta)
    (geometry : PureWZ2Proposition64Lemma35GeometricData
      quantitativeOutput.normalized hsourceSmall)
    (frostman : SelectedSourceFrostmanReceipt geometry)
    (floor : PureWZ2CroppedCriticalFloorSelectionData
      sigma outputLoss outputLoss)

/-- Raw conflict degree used by the joint paper-ED selector. -/
noncomputable def quantitativeVerticalJointPaperEDConflictLoss : ENNReal :=
  let _ := geometry
  pureWZ2Proposition64PaperConflictPackingDegree sourceDelta
    quantitativeOutput.normalized.prepared.normalization
    (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
    quantitativeOutput.normalized.prepared.slab.halfHeight

/-- The cleanup-interface loss after the joint selector's simultaneous
weight regularization. -/
noncomputable def quantitativeVerticalPaperEDLoss : ENNReal :=
  pureWZ2Proposition64JointCleanupLoss geometry.cleanup.finalShading
    (quantitativeVerticalJointPaperEDConflictLoss quantitativeOutput geometry)

/-- The canonical joint paper-ED witness.  It retains the average-carrier and
weight-band receipts needed by the downstream combined selection. -/
noncomputable abbrev quantitativeVerticalJointPaperED :
    PureWZ2Proposition64JointPaperEDSelectionData
      geometry.cleanup.finalShading
      (quantitativeVerticalJointPaperEDConflictLoss quantitativeOutput geometry) :=
  Classical.choice
    (geometry.exists_jointPaperED_of_selectedSourceReceipt
      quantitativeOutput frostman)

/-- The canonical cleanup witness is definitionally the same joint ED after
forgetting only its additional quantitative fields. -/
noncomputable abbrev quantitativeVerticalPaperED :
    PureWZ2Proposition64PaperEDCleanupData
      geometry.cleanup.finalShading
      (quantitativeVerticalPaperEDLoss quantitativeOutput geometry) :=
  (quantitativeVerticalJointPaperED quantitativeOutput geometry frostman
    ).toPaperEDCleanupData

/-- The same canonical joint ED exposes the ambient-average carrier floor
from any family-free density scalar receipt; no critical-floor object is
needed to state this interface. -/
theorem quantitativeVerticalJointPaperED_haverage
    {structuralLoss structuralDelta₀ : ℝ}
    (scalars : PureWZ2Proposition64JointDensityScalarReceipt
      sourceDelta
      (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
      quantitativeOutput.densityLoss
      quantitativeOutput.normalized.prepared.normalization
      quantitativeOutput.normalized.prepared.slab.halfHeight
      structuralLoss structuralDelta₀) :
    Kakeya.realRpowENN
          (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
            structuralLoss *
        ((55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN
            (pureWZ2Proposition64Lemma35FinalDelta sourceDelta) 2) ≤
      geometry.cleanup.finalShading.mass /
        (2 *
          (paperPositiveMassSubfamily
            geometry.cleanup.finalShading).family.card : ENNReal) :=
  geometry.jointPaperED_haverage quantitativeOutput scalars

/-- The canonical paper-ED loss is finite. -/
theorem quantitativeVerticalPaperEDLoss_ne_top :
    quantitativeVerticalPaperEDLoss quantitativeOutput geometry ≠ ⊤ := by
  unfold quantitativeVerticalPaperEDLoss
    pureWZ2Proposition64JointCleanupLoss
  apply ENNReal.mul_ne_top
  · unfold pureWZ2Proposition64JointWeightRegularizationLoss
    apply ENNReal.mul_ne_top
    · norm_num
    apply ENNReal.pow_ne_top
    apply ENNReal.add_ne_top.mpr
    constructor <;> simp
  apply ENNReal.add_ne_top.mpr
  constructor
  · unfold quantitativeVerticalJointPaperEDConflictLoss
      pureWZ2Proposition64PaperConflictPackingDegree
    exact ENNReal.natCast_ne_top _
  · simp

/-- The genuinely family-free scalar tail of quantitative vertical
rediscretization.  Every field is evaluated on the same output, geometry,
canonical ED loss, and cropped critical floor. -/
structure QuantitativeVerticalScalarReceipt : Prop where
  finalDelta_le_floor :
    pureWZ2Proposition64Lemma35FinalDelta sourceDelta ≤ floor.delta₀
  density_absorption :
    (147 *
        (quantitativeVerticalPaperEDLoss quantitativeOutput geometry + 1)) *
          (Kakeya.realRpowENN
              (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
                floor.structuralLoss *
            (55296 * Kakeya.deltaTubeVolume 1 *
              Kakeya.realRpowENN
                (pureWZ2Proposition64Lemma35FinalDelta sourceDelta) 2)) ≤
      pureWZ2Proposition64QuantitativeMassCoefficient quantitativeOutput *
        Kakeya.realRpowENN sourceDelta 2
  cwa_absorption :
    4 * Kakeya.realRpowENN
        (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
          (-floor.structuralLoss) ≤
      Kakeya.realRpowENN
        (pureWZ2Proposition64Lemma35FinalDelta sourceDelta) (-outputLoss)
  volume_absorption :
    pureWZ2Proposition64VolumeCoefficient quantitativeOutput.normalized *
        Kakeya.realRpowENN sourceDelta
          (sigma - quantitativeOutput.normalized.inputLoss) ≤
      Kakeya.realRpowENN
        (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
          (sigma - outputLoss)
  local_constant_absorption :
    192 * Kakeya.realRpowENN sourceDelta (-workLoss) ≤
      Kakeya.realRpowENN
        (pureWZ2Proposition64Lemma35FinalDelta sourceDelta) (-outputLoss)
  global_constant_absorption :
    7077888 * (24000 * Kakeya.realRpowENN sourceDelta (-workLoss)) ≤
      Kakeya.realRpowENN
        (pureWZ2Proposition64Lemma35FinalDelta sourceDelta) (-outputLoss)

/-- The sole non-scalar receipt still required by the final critical-floor
assembly, on the canonical ED family fixed above. -/
structure QuantitativeVerticalNearbyReceipt : Prop where
  nearby :
    WZ2PaperPureCWAAtNearbyScales
      (quantitativeVerticalPaperED
        quantitativeOutput geometry frostman).subfamily.family
      (Kakeya.realRpowENN
        (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
          (-floor.structuralLoss))

/-- Finite same-family scale-cover data sufficient to construct the canonical
ED family's nearby CWA.

Unlike `QuantitativeVerticalNearbyReceipt`, this does not store the target
proposition.  It stores finitely many actual Definition-2.12 scale covers and
the rounding relation that makes them cover every requested scale.  Every
scale witness is indexed by the one canonical paper-ED family above. -/
structure QuantitativeVerticalNearbyScheduleReceipt where
  coordinateCount : ℕ
  coordinateCount_pos : 0 < coordinateCount
  scaleWitness :
    ∀ _coordinate : Fin coordinateCount,
      Σ actualScale : ℝ,
        WZ2PaperPureScaleCoverData
          (quantitativeVerticalPaperED
            quantitativeOutput geometry frostman).subfamily.family
          actualScale
          (Kakeya.realRpowENN
            (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
              (-floor.structuralLoss))
  rounding :
    ∀ requested : WZ2PaperRequestedScale
        (pureWZ2Proposition64Lemma35FinalDelta sourceDelta),
      ∃ coordinate : Fin coordinateCount,
        requested.1 ≤ (scaleWitness coordinate).1 ∧
          ENNReal.ofReal (scaleWitness coordinate).1 <
            Kakeya.realRpowENN
                (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
                (-floor.structuralLoss) *
              ENNReal.ofReal requested.1

/-- Build the exact nearby receipt from a finite rounded schedule on the same
canonical ED family. -/
theorem quantitativeVerticalNearbyReceipt_of_schedule
    (schedule : QuantitativeVerticalNearbyScheduleReceipt
      quantitativeOutput geometry frostman floor) :
    QuantitativeVerticalNearbyReceipt
      quantitativeOutput geometry frostman floor := by
  refine ⟨pureWZ2_nearby_from_finite_witnesses
    geometry.scales.finalDelta_pos ?_ ?_
    (quantitativeVerticalPaperED
      quantitativeOutput geometry frostman).essentially_distinct
    schedule.coordinateCount schedule.coordinateCount_pos
    schedule.scaleWitness schedule.rounding⟩
  · rw [Kakeya.realRpowENN, ENNReal.one_le_ofReal]
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos
      geometry.scales.finalDelta_pos
      (geometry.scales.finalDelta_le_one_ninety_six.trans (by norm_num))
      (by linarith [floor.structuralLoss_pos])
  · simp [Kakeya.realRpowENN]

/-- Assemble the quantitative vertical rediscretization from one exact
hierarchy, its literal geometric prefix and selected-source receipt, one
cropped critical floor, the family-free scalar tail, and a finite same-family
nearby schedule. -/
theorem pureWZ2_quantitativeVerticalRediscretization_of_receipts
    (scalars : QuantitativeVerticalScalarReceipt
      quantitativeOutput geometry floor)
    (nearbySchedule : QuantitativeVerticalNearbyScheduleReceipt
      quantitativeOutput geometry frostman floor) :
    Nonempty (PureWZ2VerticalRediscretizationData
      quantitativeOutput.normalized.prepared.normalized
      (pureWZ2Proposition64Lemma35FinalDelta sourceDelta) outputLoss) := by
  let ed := quantitativeVerticalPaperED quantitativeOutput geometry frostman
  let nearby := quantitativeVerticalNearbyReceipt_of_schedule
    quantitativeOutput geometry frostman floor nearbySchedule
  apply geometry.assembleVerticalRediscretizationOfCriticalFloor
    quantitativeOutput ed floor
  exact {
    nearby := nearby.nearby
    finalDelta_le_floor := scalars.finalDelta_le_floor
    ed_loss_ne_top :=
      quantitativeVerticalPaperEDLoss_ne_top quantitativeOutput geometry
    density_absorption := scalars.density_absorption
    cwa_absorption := scalars.cwa_absorption
    volume_absorption := scalars.volume_absorption
    local_constant_absorption := scalars.local_constant_absorption
    global_constant_absorption := scalars.global_constant_absorption
  }

end PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData

end Kakeya.Assouad

end
