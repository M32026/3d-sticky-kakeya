import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64QuantitativeVerticalOfReceipts
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64GeometricTopLevelCWA
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64TopLevelToFiberCWA

/-!
# Quantitative Proposition 6.4 finite nearby schedule

The quantitative R4 ledger already gives top-level CWA on the exact canonical
paper-ED family.  Therefore the remaining multiscale input is not another CWA
assumption: it is a finite family of literal partitioning covers whose complete
fibers are degree-uniform, together with the scale rounding and parent-count
bounds.  The actual-John fiber CWA is constructed below from those data.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

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

/-- The top-level CWA constant already proved for the exact canonical ED
family from the quantitative hierarchy ledger. -/
noncomputable def quantitativeVerticalPaperEDTopConstant : ENNReal :=
  ENNReal.ofReal
        (quantitativeOutput.normalized.prepared.normalization *
          quantitativeOutput.normalized.prepared.slab.halfHeight /
            pureWZ2Proposition64Lemma35Scale ^ 3) *
    ENNReal.ofReal
        (27 *
          (2 * pureWZ2Proposition64TopCarrierFactor
            (quantitativeOutput := quantitativeOutput) - 1) ^ 3) *
    ((pureWZ2Proposition64TopWeight
          (quantitativeOutput := quantitativeOutput))⁻¹ *
        pureWZ2Proposition64TopRetention
          (sourceDelta := sourceDelta)
          (quantitativeVerticalPaperEDLoss quantitativeOutput geometry)) *
      Kakeya.realRpowENN sourceDelta
        (-quantitativeOutput.normalized.inputLoss)

/-- The only genuinely multiscale receipt still required on the canonical
paper-ED family.

For each member of a finite scale net it stores a literal strict
Definition-2.12 partitioning cover, uniformity of all nonempty complete
fibers, and the scale-cancelling coarse-parent count.  It stores neither
nearby CWA nor any arbitrary-family callback. -/
structure QuantitativeVerticalMultiscaleDegreeUniformityReceipt where
  coordinateCount : ℕ
  coordinateCount_pos : 0 < coordinateCount
  actualScale : Fin coordinateCount → ℝ
  actualScale_pos : ∀ coordinate, 0 < actualScale coordinate
  coarse :
    ∀ coordinate,
      Kakeya.Streamlined.TubeFamily (actualScale coordinate)
  cover :
    ∀ coordinate,
      WZ2PaperPurePartitioningCover
        (quantitativeVerticalPaperED
          quantitativeOutput geometry frostman).subfamily.family
        (coarse coordinate)
  degreeConstant : Fin coordinateCount → ENNReal
  fullFiberUniform :
    ∀ coordinate,
      WZ2PaperPureFullFibersAreCUniform
        (quantitativeVerticalPaperED
          quantitativeOutput geometry frostman).subfamily.family
        (coarse coordinate)
        (degreeConstant coordinate)
  parentCountConstant : Fin coordinateCount → ENNReal
  parentCount :
    ∀ coordinate,
      (coarse coordinate).enncard ≤
        parentCountConstant coordinate *
          (Kakeya.realRpowENN (actualScale coordinate) 2)⁻¹
  scaleAbsorption :
    ∀ coordinate,
      let bodyConstant :=
        degreeConstant coordinate *
          parentCountConstant coordinate *
          (108 * ENNReal.ofReal
            (1 + 2 * actualScale coordinate)) *
          212776173 *
          quantitativeVerticalPaperEDTopConstant
            quantitativeOutput geometry
      max (degreeConstant coordinate) bodyConstant ≤
        Kakeya.realRpowENN
          (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
          (-floor.structuralLoss)
  rounding :
    ∀ requested : WZ2PaperRequestedScale
        (pureWZ2Proposition64Lemma35FinalDelta sourceDelta),
      ∃ coordinate : Fin coordinateCount,
        requested.1 ≤ actualScale coordinate ∧
          ENNReal.ofReal (actualScale coordinate) <
            Kakeya.realRpowENN
                (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
                (-floor.structuralLoss) *
              ENNReal.ofReal requested.1

/-- Construct every actual Definition-2.12 scale witness once the already
proved canonical top-level CWA and the finite degree-uniform cover receipt
are supplied.  The separate argument avoids storing a deterministic theorem
inside the genuinely multiscale receipt. -/
noncomputable def quantitativeVerticalNearbySchedule_of_degreeUniformityAndTopLevel
    (topLevel :
      WZ2PaperConvexWolffBound
        (quantitativeVerticalPaperED
          quantitativeOutput geometry frostman).subfamily.family
        (quantitativeVerticalPaperEDTopConstant quantitativeOutput geometry))
    (receipt : QuantitativeVerticalMultiscaleDegreeUniformityReceipt
      quantitativeOutput geometry frostman floor) :
    QuantitativeVerticalNearbyScheduleReceipt
      quantitativeOutput geometry frostman floor := by
  let ed := quantitativeVerticalPaperED quantitativeOutput geometry frostman
  let outputConstant :=
    Kakeya.realRpowENN
      (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
      (-floor.structuralLoss)
  let topConstant :=
    quantitativeVerticalPaperEDTopConstant quantitativeOutput geometry
  have finalLine : WZ1PaperIsLineClass ed.subfamily.family :=
    geometry.paperED_lineClass ed
  have finalLocal :
      ∀ index, ‖wz2PaperTubeMidpoint
        (ed.subfamily.family.tube index)‖ ≤ 3 := by
    intro index
    have hcentered :
        wz2PaperTubeMidpoint (ed.subfamily.family.tube index) =
          wz1TubeAxisZeroPoint (ed.subfamily.family.tube index) := by
      have hvertical := (finalLine index).vertical
      rw [ed.tube_provenance index] at hvertical
      rw [ed.tube_provenance index]
      apply pureWZ2Proposition64IsotropicRebasedPaperTube_midpoint
      simpa [pureWZ2Proposition64IsotropicPaperFamily,
        pureWZ2Proposition64IsotropicRebasedPaperTube,
        pureWZ2Proposition64IsotropicPaperTube] using hvertical
    rw [hcentered]
    have hzeroTwo :
        wz1TubeAxisZeroPoint (ed.subfamily.family.tube index) (2 : Fin 3) = 0 :=
      wz1TubeAxisZeroPoint_coord_two _ (finalLine index).vertical
    rw [EuclideanSpace.norm_eq, Real.sqrt_le_iff]
    constructor
    · positivity
    · simp only [Real.norm_eq_abs, sq_abs, Fin.sum_univ_three, hzeroTwo]
      have hzero := sq_le_sq₀
        (abs_nonneg (wz1TubeAxisZeroPoint
          (ed.subfamily.family.tube index) 0))
        (by norm_num : 0 ≤ (1 / 3 : ℝ)) |>.2 (finalLine index).2.1
      have hone := sq_le_sq₀
        (abs_nonneg (wz1TubeAxisZeroPoint
          (ed.subfamily.family.tube index) 1))
        (by norm_num : 0 ≤ (1 / 3 : ℝ)) |>.2 (finalLine index).2.2
      rw [sq_abs] at hzero hone
      nlinarith
  refine {
    coordinateCount := receipt.coordinateCount
    coordinateCount_pos := receipt.coordinateCount_pos
    scaleWitness := fun coordinate => ⟨receipt.actualScale coordinate, ?_⟩
    rounding := receipt.rounding
  }
  let rho := receipt.actualScale coordinate
  let coarse := receipt.coarse coordinate
  let cover := receipt.cover coordinate
  let degreeConstant := receipt.degreeConstant coordinate
  let parentCountConstant := receipt.parentCountConstant coordinate
  let bodyConstant :=
    degreeConstant * parentCountConstant *
      (108 * ENNReal.ofReal (1 + 2 * rho)) *
      212776173 * topConstant
  have absorption := receipt.scaleAbsorption coordinate
  have degreeLe : degreeConstant ≤ outputConstant :=
    (le_max_left degreeConstant bodyConstant).trans absorption
  have bodyLe : bodyConstant ≤ outputConstant :=
    (le_max_right degreeConstant bodyConstant).trans absorption
  refine {
    delta_pos := geometry.scales.finalDelta_pos
    rho_pos := receipt.actualScale_pos coordinate
    coarse := coarse
    cover := cover
    full_fiber_uniform := fun first second =>
      (receipt.fullFiberUniform coordinate first second).trans (by
        gcongr)
    rescaledFiber := ?_
  }
  intro parent
  apply pureWZ2Proposition64_pure_fullFiber_cwa_of_topLevel
    cover (geometry.paperED_family_nonempty ed)
    (receipt.actualScale_pos coordinate)
    topLevel (receipt.fullFiberUniform coordinate)
    (receipt.parentCount coordinate)
    (fun coarseParent targetSet => by
      simpa [rho, mul_assoc, mul_left_comm, mul_comm] using
        pureWZ2Proposition64_outerJohn_inverse_volume_le_general
          (receipt.actualScale_pos coordinate)
          (coarse.tube coarseParent)
          (WZ2PaperAssouadUnitRescalingData.ofTube
            (coarse.tube coarseParent)
            (receipt.actualScale_pos coordinate))
          targetSet)
    (fun _coarseParent sourceSet hsourceConvex => by
      rcases pureWZ2Proposition64_localized_common_cropped_envelope
          geometry.scales.finalDelta_pos
          (geometry.scales.finalDelta_le_one_ninety_six.trans (by norm_num))
          finalLine finalLocal sourceSet hsourceConvex with
        ⟨paperSet, hpaperConvex, hpaperVolume, hpaperCarrier⟩
      exact ⟨paperSet, hpaperConvex, hpaperVolume,
        fun source _hsource hcarrier => hpaperCarrier source hcarrier⟩)
    bodyLe parent

/-- The quantitative hierarchy's R4 ledger supplies the deterministic
top-level input; only the finite degree-uniform cover receipt remains open. -/
theorem exists_quantitativeVerticalNearbySchedule_of_degreeUniformity
    (receipt : QuantitativeVerticalMultiscaleDegreeUniformityReceipt
      quantitativeOutput geometry frostman floor) :
    Nonempty (QuantitativeVerticalNearbyScheduleReceipt
      quantitativeOutput geometry frostman floor) := by
  let ed := quantitativeVerticalPaperED quantitativeOutput geometry frostman
  have topLevel :
      WZ2PaperConvexWolffBound ed.subfamily.family
        (quantitativeVerticalPaperEDTopConstant
          quantitativeOutput geometry) := by
    simpa [quantitativeVerticalPaperEDTopConstant, mul_assoc] using
      (paperED_topLevelCWA
        (quantitativeOutput := quantitativeOutput) geometry ed)
  exact ⟨quantitativeVerticalNearbySchedule_of_degreeUniformityAndTopLevel
    quantitativeOutput geometry frostman floor topLevel receipt⟩

/-- Quantitative vertical rediscretization now consumes only the family-free
scalar tail and the canonical finite degree-uniform cover receipt. -/
theorem pureWZ2_quantitativeVerticalRediscretization_of_degreeUniformity
    (scalars : QuantitativeVerticalScalarReceipt
      quantitativeOutput geometry floor)
    (receipt : QuantitativeVerticalMultiscaleDegreeUniformityReceipt
      quantitativeOutput geometry frostman floor) :
    Nonempty (PureWZ2VerticalRediscretizationData
      quantitativeOutput.normalized.prepared.normalized
      (pureWZ2Proposition64Lemma35FinalDelta sourceDelta) outputLoss) := by
  rcases exists_quantitativeVerticalNearbySchedule_of_degreeUniformity
      quantitativeOutput geometry frostman floor receipt with
    ⟨nearbySchedule⟩
  exact pureWZ2_quantitativeVerticalRediscretization_of_receipts
    quantitativeOutput geometry frostman floor scalars
    nearbySchedule

end PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData

end Kakeya.Assouad

end
