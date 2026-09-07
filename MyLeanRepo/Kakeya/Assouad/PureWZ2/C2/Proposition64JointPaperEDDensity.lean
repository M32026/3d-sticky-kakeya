import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64JointPaperEDSelection
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64SelectedSourceFrostman

/-!
# Proposition 6.4 joint paper-ED density

This module closes the same-witness density ledger required by the mild
rescaling step of `wz2_64.tex`.  The pre-ED saturated shading mass and its
positive source-indexed cardinality remain in one inequality.  Only after
that cancellation is established do we invoke the joint paper-ED selector.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

/-- The mass coefficient stripped of every runtime family and shading. -/
noncomputable def pureWZ2Proposition64JointDensityMassCoefficient
    (sourceDelta densityLoss normalization halfHeight : ℝ) : ENNReal :=
  ENNReal.ofReal (pureWZ2Proposition64Lemma35Scale ^ 3) *
    (ENNReal.ofReal (pureWZ2Proposition64Lemma35Width ^ 3 / 27) *
      (ENNReal.ofReal (1 / (normalization * halfHeight)) *
        (ENNReal.ofReal (2 * halfHeight) *
          (ENNReal.ofReal (1 / 6) *
            Kakeya.realRpowENN sourceDelta densityLoss))))

/--
Runtime scalar receipt for the same-witness average-mass estimate.

It contains no family-valued object, but it is indexed by the actual
`sourceDelta`, `finalDelta`, normalization, and slab height.  Thus it is not
itself a P0 cutoff: the production schedule must later prove that its
pre-runtime source cutoff constructs this receipt uniformly.
-/
structure PureWZ2Proposition64JointDensityScalarReceipt
    (sourceDelta finalDelta densityLoss normalization halfHeight
      structuralLoss floorDelta₀ : ℝ) : Prop where
  finalDelta_le_floor : finalDelta ≤ floorDelta₀
  average_absorption :
    294 *
        (Kakeya.realRpowENN finalDelta structuralLoss *
          ((55296 * Kakeya.deltaTubeVolume 1) *
            Kakeya.realRpowENN finalDelta 2)) ≤
      pureWZ2Proposition64JointDensityMassCoefficient
          sourceDelta densityLoss normalization halfHeight *
        Kakeya.realRpowENN sourceDelta 2

namespace PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData

variable
    {sigma workLoss sourceDelta targetDelta₀ outputLoss : ℝ}
    {hsourceSmall : sourceDelta ≤
      pureWZ2Proposition64Lemma35SourceCeiling targetDelta₀}
    (quantitativeOutput : PureWZ2QuantitativeNormalizedHierarchyOutput
      sigma workLoss sourceDelta)
    (geometry : PureWZ2Proposition64Lemma35GeometricData
      quantitativeOutput.normalized hsourceSmall)

/-- The positive part of the pre-ED saturated family still injects into the
original normalized source family through the literal selected-source map. -/
theorem positiveFinal_enncard_le_source :
    (paperPositiveMassSubfamily
      geometry.cleanup.finalShading).family.enncard ≤
        quantitativeOutput.normalized.source.family.enncard := by
  let positive :=
    paperPositiveMassSubfamily geometry.cleanup.finalShading
  have hpositive :
      positive.family.card ≤ geometry.selectedSource.family.card := by
    have hraw := Fintype.card_le_of_injective positive.embedding
      positive.embedding.injective
    simp only [Fintype.card_fin] at hraw
    change positive.family.card ≤ geometry.selectedSource.family.card at hraw
    exact hraw
  have hselected :
      geometry.selectedSource.family.card ≤
        quantitativeOutput.normalized.source.family.card := by
    simpa only [Fintype.card_fin] using
      Fintype.card_le_of_injective geometry.selectedSource.embedding
        geometry.selectedSource.embedding.injective
  change (positive.family.card : ENNReal) ≤
    (quantitativeOutput.normalized.source.family.card : ENNReal)
  exact_mod_cast hpositive.trans hselected

/-- The complete slab/common-window/exact/popular/isotropic mass chain before
ED selection.  No conflict degree occurs in this inequality. -/
theorem quantitative_preED_mass_ledger :
    pureWZ2Proposition64QuantitativeMassCoefficient quantitativeOutput *
        (wz1PaperBodyFamily
          quantitativeOutput.normalized.source.family).mass ≤
      147 * geometry.cleanup.finalShading.mass := by
  unfold pureWZ2Proposition64QuantitativeMassCoefficient
  have hgroup :
      (ENNReal.ofReal
          (2 * quantitativeOutput.normalized.prepared.slab.halfHeight) *
        (ENNReal.ofReal (1 / 6) *
          Kakeya.realRpowENN sourceDelta quantitativeOutput.densityLoss)) *
          (wz1PaperBodyFamily
            quantitativeOutput.normalized.source.family).mass =
      ENNReal.ofReal
          (2 * quantitativeOutput.normalized.prepared.slab.halfHeight) *
        (ENNReal.ofReal (1 / 6) *
          (Kakeya.realRpowENN sourceDelta quantitativeOutput.densityLoss *
            (wz1PaperBodyFamily
              quantitativeOutput.normalized.source.family).mass)) := by
    ring
  have hselected :
      ENNReal.ofReal
          (2 * quantitativeOutput.normalized.prepared.slab.halfHeight) *
        quantitativeOutput.normalized.hierarchy.shading.mass ≤
      147 * geometry.selectedShading.mass := by
    calc
      ENNReal.ofReal
          (2 * quantitativeOutput.normalized.prepared.slab.halfHeight) *
          quantitativeOutput.normalized.hierarchy.shading.mass ≤
        3 * quantitativeOutput.normalized.prepared.slab.shading.mass :=
          quantitativeOutput.normalized.prepared.slab.mass_fraction
      _ ≤ 3 * (49 * geometry.selectedShading.mass) := by
        gcongr
        rw [geometry.selectedShading_mass]
        exact geometry.common.retained_mass
      _ = 147 * geometry.selectedShading.mass := by ring
  have hexact :
      ENNReal.ofReal
          (1 /
            (quantitativeOutput.normalized.prepared.normalization *
              quantitativeOutput.normalized.prepared.slab.halfHeight)) *
        (ENNReal.ofReal
            (2 * quantitativeOutput.normalized.prepared.slab.halfHeight) *
          quantitativeOutput.normalized.hierarchy.shading.mass) ≤
      147 * geometry.exactShading.mass := by
    calc
      _ ≤ ENNReal.ofReal
          (1 /
            (quantitativeOutput.normalized.prepared.normalization *
              quantitativeOutput.normalized.prepared.slab.halfHeight)) *
          (147 * geometry.selectedShading.mass) := by gcongr
      _ = 147 *
          (ENNReal.ofReal
            (1 /
              (quantitativeOutput.normalized.prepared.normalization *
                quantitativeOutput.normalized.prepared.slab.halfHeight)) *
            geometry.selectedShading.mass) := by ring
      _ = 147 * geometry.exactShading.mass := by
        rw [geometry.exactShading_mass]
  have hpopular :
      ENNReal.ofReal
          (pureWZ2Proposition64Lemma35Width ^ 3 / 27) *
        (ENNReal.ofReal
            (1 /
              (quantitativeOutput.normalized.prepared.normalization *
                quantitativeOutput.normalized.prepared.slab.halfHeight)) *
          (ENNReal.ofReal
              (2 *
                quantitativeOutput.normalized.prepared.slab.halfHeight) *
            quantitativeOutput.normalized.hierarchy.shading.mass)) ≤
      147 * geometry.cleanup.popular.restricted.mass := by
    calc
      _ ≤ ENNReal.ofReal
          (pureWZ2Proposition64Lemma35Width ^ 3 / 27) *
          (147 * geometry.exactShading.mass) := by gcongr
      _ = 147 *
          (ENNReal.ofReal
            (pureWZ2Proposition64Lemma35Width ^ 3 / 27) *
            geometry.exactShading.mass) := by ring
      _ ≤ 147 * geometry.cleanup.popular.restricted.mass := by
        gcongr
        exact geometry.cleanup.popular.mass_lower
  calc
    ENNReal.ofReal (pureWZ2Proposition64Lemma35Scale ^ 3) *
          (ENNReal.ofReal
              (pureWZ2Proposition64Lemma35Width ^ 3 / 27) *
            (ENNReal.ofReal
                (1 /
                  (quantitativeOutput.normalized.prepared.normalization *
                    quantitativeOutput.normalized.prepared.slab.halfHeight)) *
              (ENNReal.ofReal
                  (2 *
                    quantitativeOutput.normalized.prepared.slab.halfHeight) *
                (ENNReal.ofReal (1 / 6) *
                  Kakeya.realRpowENN sourceDelta
                    quantitativeOutput.densityLoss)))) *
        (wz1PaperBodyFamily
          quantitativeOutput.normalized.source.family).mass =
      ENNReal.ofReal (pureWZ2Proposition64Lemma35Scale ^ 3) *
          (ENNReal.ofReal
              (pureWZ2Proposition64Lemma35Width ^ 3 / 27) *
            (ENNReal.ofReal
                (1 /
                  (quantitativeOutput.normalized.prepared.normalization *
                    quantitativeOutput.normalized.prepared.slab.halfHeight)) *
              (ENNReal.ofReal
                  (2 *
                    quantitativeOutput.normalized.prepared.slab.halfHeight) *
                (ENNReal.ofReal (1 / 6) *
                  (Kakeya.realRpowENN sourceDelta
                      quantitativeOutput.densityLoss *
                    (wz1PaperBodyFamily
                      quantitativeOutput.normalized.source.family).mass))))) := by
        rw [← hgroup]
        ring
    _ ≤ ENNReal.ofReal (pureWZ2Proposition64Lemma35Scale ^ 3) *
        (ENNReal.ofReal
            (pureWZ2Proposition64Lemma35Width ^ 3 / 27) *
          (ENNReal.ofReal
              (1 /
                (quantitativeOutput.normalized.prepared.normalization *
                  quantitativeOutput.normalized.prepared.slab.halfHeight)) *
            (ENNReal.ofReal
                (2 *
                  quantitativeOutput.normalized.prepared.slab.halfHeight) *
              quantitativeOutput.normalized.hierarchy.shading.mass))) := by
      gcongr
      exact quantitativeOutput.normalized_mass_retention
    _ ≤ ENNReal.ofReal (pureWZ2Proposition64Lemma35Scale ^ 3) *
        (147 * geometry.cleanup.popular.restricted.mass) := by
      gcongr
    _ = 147 *
        (ENNReal.ofReal (pureWZ2Proposition64Lemma35Scale ^ 3) *
          geometry.cleanup.popular.restricted.mass) := by ring
    _ ≤ 147 * geometry.cleanup.finalShading.mass := by
      gcongr
      exact geometry.cleanup_finalShading_mass_lower

/-- Source paper-body mass and the two literal embeddings keep the positive
pre-ED cardinality in the same mass inequality. -/
theorem quantitative_preED_cardinality_mass_ledger :
    pureWZ2Proposition64QuantitativeMassCoefficient quantitativeOutput *
        (Kakeya.realRpowENN sourceDelta 2 *
          (paperPositiveMassSubfamily
            geometry.cleanup.finalShading).family.enncard) ≤
      147 * geometry.cleanup.finalShading.mass := by
  have hsourceDeltaSmall : sourceDelta ≤ 1 / 24 := by
    nlinarith [geometry.scales.sourceDelta_small]
  have hsourceBody :
      quantitativeOutput.normalized.source.family.enncard *
          Kakeya.realRpowENN sourceDelta 2 ≤
        (wz1PaperBodyFamily
          quantitativeOutput.normalized.source.family).mass :=
    pureWZ2_paperBody_mass_lower
      quantitativeOutput.normalized.source.extremal.delta_pos
      (hsourceDeltaSmall.trans (by norm_num))
      quantitativeOutput.normalized.source.line_class
  calc
    pureWZ2Proposition64QuantitativeMassCoefficient quantitativeOutput *
        (Kakeya.realRpowENN sourceDelta 2 *
          (paperPositiveMassSubfamily
            geometry.cleanup.finalShading).family.enncard) ≤
      pureWZ2Proposition64QuantitativeMassCoefficient quantitativeOutput *
        (Kakeya.realRpowENN sourceDelta 2 *
          quantitativeOutput.normalized.source.family.enncard) := by
      gcongr
      exact geometry.positiveFinal_enncard_le_source quantitativeOutput
    _ = pureWZ2Proposition64QuantitativeMassCoefficient quantitativeOutput *
        (quantitativeOutput.normalized.source.family.enncard *
          Kakeya.realRpowENN sourceDelta 2) := by ring
    _ ≤ pureWZ2Proposition64QuantitativeMassCoefficient quantitativeOutput *
        (wz1PaperBodyFamily
          quantitativeOutput.normalized.source.family).mass := by
      gcongr
    _ ≤ 147 * geometry.cleanup.finalShading.mass :=
      geometry.quantitative_preED_mass_ledger quantitativeOutput

/-- The pre-ED saturated shading has a nonempty positive-mass subfamily. -/
theorem positiveFinal_family_nonempty :
    (paperPositiveMassSubfamily
      geometry.cleanup.finalShading).family.Nonempty := by
  let positive :=
    paperPositiveMassSubfamily geometry.cleanup.finalShading
  let positiveShading :=
    restrictPaperShading positive geometry.cleanup.finalShading
  by_contra hempty
  have hcard : positive.family.card = 0 := by
    simpa [Kakeya.Streamlined.TubeFamily.Nonempty] using hempty
  have hpositiveMassZero : positiveShading.mass = 0 := by
    change (∑ index : Fin positive.family.card,
      volume (positiveShading.carrier index)) = 0
    apply Finset.sum_eq_zero
    intro index _
    exact Fin.elim0 (Fin.cast hcard index)
  have hmassEq :
      positiveShading.mass = geometry.cleanup.finalShading.mass :=
    restrictPaperShading_positiveMass_mass geometry.cleanup.finalShading
  have hsourceMassZero : geometry.cleanup.finalShading.mass = 0 := by
    rw [← hmassEq, hpositiveMassZero]
  have hmassPos := geometry.cleanup_finalShading_mass_pos
  rw [hsourceMassZero] at hmassPos
  exact (lt_irrefl 0 hmassPos)

/-- Derive the exact average-per-positive-tube inequality consumed by the
joint selector.  The positive cardinality is multiplied through the whole
proof and cancelled only at the final division. -/
theorem jointPaperED_haverage
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
            geometry.cleanup.finalShading).family.card : ENNReal) := by
  let positive :=
    paperPositiveMassSubfamily geometry.cleanup.finalShading
  let targetCost :=
    Kakeya.realRpowENN
        (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
          structuralLoss *
      ((55296 * Kakeya.deltaTubeVolume 1) *
        Kakeya.realRpowENN
          (pureWZ2Proposition64Lemma35FinalDelta sourceDelta) 2)
  have hcardZero : (positive.family.card : ENNReal) ≠ 0 := by
    exact_mod_cast
      (Nat.ne_of_gt
        (geometry.positiveFinal_family_nonempty quantitativeOutput))
  have hdenominatorZero :
      (2 * positive.family.card : ENNReal) ≠ 0 :=
    mul_ne_zero (by norm_num) hcardZero
  have hdenominatorTop :
      (2 * positive.family.card : ENNReal) ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) (by simp)
  apply (ENNReal.le_div_iff_mul_le
    (Or.inl hdenominatorZero) (Or.inl hdenominatorTop)).2
  apply (ENNReal.mul_le_mul_iff_left
    (by norm_num : (147 : ENNReal) ≠ 0)
    (by norm_num : (147 : ENNReal) ≠ ⊤)).mp
  calc
    (targetCost * (2 * (positive.family.card : ENNReal))) * 147 =
        (294 * targetCost) * positive.family.enncard := by
      simp [Kakeya.Streamlined.TubeFamily.enncard]
      ring
    _ ≤
        (pureWZ2Proposition64QuantitativeMassCoefficient quantitativeOutput *
          Kakeya.realRpowENN sourceDelta 2) *
            positive.family.enncard := by
      exact mul_le_mul_left
        (by
          simpa only [targetCost,
            pureWZ2Proposition64JointDensityMassCoefficient,
            pureWZ2Proposition64QuantitativeMassCoefficient] using
              scalars.average_absorption)
        positive.family.enncard
    _ = pureWZ2Proposition64QuantitativeMassCoefficient quantitativeOutput *
        (Kakeya.realRpowENN sourceDelta 2 *
          positive.family.enncard) := by ring
    _ ≤ 147 * geometry.cleanup.finalShading.mass := by
      simpa only [positive] using
        geometry.quantitative_preED_cardinality_mass_ledger
          quantitativeOutput
    _ = geometry.cleanup.finalShading.mass * 147 := by ring

/-- Construct the canonical joint selector from the selected-source Frostman
receipt, without invoking the older generic paper-ED choice. -/
theorem exists_jointPaperED_of_selectedSourceReceipt
    (frostman : SelectedSourceFrostmanReceipt geometry) :
    let K := pureWZ2Proposition64PaperConflictPackingDegree sourceDelta
      quantitativeOutput.normalized.prepared.normalization
      (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
      quantitativeOutput.normalized.prepared.slab.halfHeight
    Nonempty (PureWZ2Proposition64JointPaperEDSelectionData
      geometry.cleanup.finalShading K) := by
  dsimp only
  refine pureWZ2Proposition64_exactJointPaperEDSelectionPacking
    quantitativeOutput.normalized.prepared.restrictedRaw.slope
    quantitativeOutput.normalized.prepared.slab.center
    quantitativeOutput.normalized.prepared.slab.anchorHeight
    quantitativeOutput.normalized.prepared.slab.halfHeight
    quantitativeOutput.normalized.prepared.normalization
    geometry.common.translation geometry.selectedSource.family
    quantitativeOutput.normalized.source.extremal.delta_pos
    geometry.common.translation_height
    quantitativeOutput.normalized.prepared.slab.halfHeight_pos
    quantitativeOutput.normalized.prepared.slab.halfHeight_le_one
    quantitativeOutput.normalized.normalization_nine
    quantitativeOutput.normalized.prepared.normalized.anchor_value_bound ?_
    (quantitativeOutput.normalized.source.line_class.subfamily
      geometry.selectedSource)
    (by
      intro first second hne
      have hambientNe :
          geometry.selectedSource.embedding first ≠
            geometry.selectedSource.embedding second :=
        geometry.selectedSource.embedding.injective.ne hne
      simpa only [Kakeya.Streamlined.TubeSubfamily.tube_eq] using
        quantitativeOutput.normalized.source.extremal.cwa_nearby_scales.2.2.1
          (geometry.selectedSource.embedding first)
          (geometry.selectedSource.embedding second) hambientNe)
    (fun source => frostman.source_bounded_base
      (geometry.selectedSource.embedding source))
    geometry.imageData.line_class geometry.exactShading
    geometry.cleanup.popular geometry.scales.width_pos
    geometry.scales.imageDelta_pos geometry.scales.finalDelta_pos
    geometry.scales.finalDelta_le_one_ninety_six geometry.scales.scale_one
    geometry.scales.retube_radius geometry.scales.box_scale
  · have hcenter :=
      quantitativeOutput.normalized.prepared.slab.source_window 0 (by norm_num)
    rw [mul_zero, add_zero] at hcenter
    exact abs_le.mpr hcenter

/-- Final canonical construction: one joint ED family together with lambda
density derived internally from the quantitative hierarchy and scalar cutoff. -/
theorem exists_jointPaperED_with_density
    (frostman : SelectedSourceFrostmanReceipt geometry)
    (floor : PureWZ2CroppedCriticalFloorSelectionData
      sigma outputLoss outputLoss)
    (scalars : PureWZ2Proposition64JointDensityScalarReceipt
      sourceDelta
      (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
      quantitativeOutput.densityLoss
      quantitativeOutput.normalized.prepared.normalization
      quantitativeOutput.normalized.prepared.slab.halfHeight
      floor.structuralLoss floor.delta₀) :
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
  dsimp only
  rcases geometry.exists_jointPaperED_of_selectedSourceReceipt
      quantitativeOutput frostman with ⟨joint⟩
  refine ⟨joint, joint.dense_of_average_body_cost ?_⟩
  exact geometry.jointPaperED_haverage quantitativeOutput scalars

end PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData

end Kakeya.Assouad

end
