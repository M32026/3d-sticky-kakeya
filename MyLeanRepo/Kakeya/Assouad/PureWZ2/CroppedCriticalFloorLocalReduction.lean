import MyLeanRepo.Kakeya.Assouad.PureWZ2.CroppedCriticalFloorBridge
import MyLeanRepo.Kakeya.Assouad.PureWZ2.NormalizationFinalOrdinaryTrace
import MyLeanRepo.Kakeya.Assouad.PureWZ2.PureCriticalFloorSelection
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCarrierVolumeLower

/-!
# Local cropped-to-ordinary critical-floor reduction

Finite positive density alone does not repair the unrestricted global
reduction: a cropped paper carrier can miss the crop box, and longitudinally
shifted ordinary representatives need not retain the cropped shading.

The minimum local interface is a same-family ordinary trace with three facts:
the ordinary indexed body mass is bounded by the cropped indexed body mass,
the trace retains a fixed fraction of cropped shaded mass, and its union is
contained in the cropped union. Pure nearby-scale CWA is then preserved by
using the same ordinary family and only weakening its constant.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

/-- The exact local mass and support data needed for cropped-floor reduction. -/
structure PureWZ2CroppedFloorLocalTraceData
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (croppedShading : WZ1PaperTubeShading family)
    (lossConstant : ENNReal) where
  ordinaryShading : Kakeya.Streamlined.TubeShading family
  ordinary_body_mass_le :
    family.toBodyFamily.mass ≤ (wz1PaperBodyFamily family).mass
  trace_mass_retention :
    lossConstant⁻¹ * croppedShading.mass ≤ ordinaryShading.mass
  ordinary_union_subset :
    ordinaryShading.union ⊆ croppedShading.union

namespace PureWZ2CroppedFloorLocalTraceData

/-- Assemble the public reduction data from the minimal local trace input. -/
theorem toReductionData
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (familyNonempty : family.Nonempty)
    (croppedShading : WZ1PaperTubeShading family)
    (lossConstant cwaConstant densityConstant : ENNReal)
    (lossConstantOne : 1 ≤ lossConstant)
    (lossConstantTop : lossConstant ≠ ⊤)
    (pureCWA : WZ2PaperPureCWAAtNearbyScales family cwaConstant)
    (croppedDense : croppedShading.IsLambdaDense densityConstant)
    (localTrace :
      PureWZ2CroppedFloorLocalTraceData
        croppedShading lossConstant) :
    Nonempty
      (PureWZ2CroppedFloorReductionData
        family croppedShading lossConstant
          cwaConstant densityConstant) := by
  have cwaConstantLe :
      cwaConstant ≤ lossConstant * cwaConstant := by
    calc
      cwaConstant = 1 * cwaConstant := by simp
      _ ≤ lossConstant * cwaConstant := by gcongr
  have ordinaryCWA :
      WZ2PaperPureCWAAtNearbyScales
        family (lossConstant * cwaConstant) :=
    pureCWA.mono cwaConstantLe
      (ENNReal.mul_ne_top lossConstantTop pureCWA.2.1.2)
  have ordinaryDense :
      localTrace.ordinaryShading.IsLambdaDense
        (lossConstant⁻¹ * densityConstant) := by
    change
      (lossConstant⁻¹ * densityConstant) *
          family.toBodyFamily.mass ≤
        localTrace.ordinaryShading.mass
    calc
      (lossConstant⁻¹ * densityConstant) *
            family.toBodyFamily.mass ≤
          (lossConstant⁻¹ * densityConstant) *
            (wz1PaperBodyFamily family).mass :=
        mul_le_mul_right localTrace.ordinary_body_mass_le _
      _ = lossConstant⁻¹ *
            (densityConstant *
              (wz1PaperBodyFamily family).mass) := by
        ring
      _ ≤ lossConstant⁻¹ * croppedShading.mass := by
        gcongr
        exact croppedDense
      _ ≤ localTrace.ordinaryShading.mass :=
        localTrace.trace_mass_retention
  exact
    ⟨{
      ordinaryFamily := family
      ordinaryShading := localTrace.ordinaryShading
      ordinary_nonempty := familyNonempty
      ordinary_cwa := ordinaryCWA
      ordinary_dense := ordinaryDense
      ordinary_union_volume_le :=
        measure_mono localTrace.ordinary_union_subset
    }⟩

end PureWZ2CroppedFloorLocalTraceData

/--
For a line-class family at scale at most `1/12`, the canonical inner ordinary
tube in each paper carrier gives the required indexed body-mass comparison.
-/
theorem pureWZ2_ordinary_body_mass_le_cropped_body_mass
    {delta : ℝ}
    (deltaPos : 0 < delta)
    (deltaSmall : delta ≤ 1 / 12)
    (family : Kakeya.Streamlined.TubeFamily delta)
    (lineClass : WZ1PaperIsLineClass family) :
    family.toBodyFamily.mass ≤ (wz1PaperBodyFamily family).mass := by
  change
    (∑ index : Fin family.card,
      volume (family.tube index).carrier) ≤
    ∑ index : Fin family.card,
      volume (wz1PaperTubeCarrier (family.tube index))
  apply Finset.sum_le_sum
  intro index _
  calc
    volume (family.tube index).carrier =
        volume (wz2PaperInnerTube (family.tube index)).carrier := by
      change
        (family.tube index).volume =
          (wz2PaperInnerTube (family.tube index)).volume
      exact
        Kakeya.Streamlined.tube_volume_eq
          (family.tube index)
          (wz2PaperInnerTube (family.tube index))
    _ ≤ volume (wz1PaperTubeCarrier (family.tube index)) :=
      measure_mono
        (wz2PaperInnerTube_carrier_subset
          deltaPos deltaSmall
          (family.tube index) (lineClass index))

/--
Specialization to the canonical ordinary trace carried by a completed
normalization. The scalar absorption is the only extra quantitative input:
it says that the fixed loss allowed by the critical-floor bridge pays the
per-tube ordinary density and the `1/100` cubical trace loss.
-/
theorem PureWZ2CroppedCriticalNormalizationData.croppedFloorReduction_of_trace
    {sigma inputLoss normalizationLoss delta : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    (normalized :
      PureWZ2CroppedCriticalNormalizationData
        (outputLoss := normalizationLoss)
        source normalizationExponent)
    (selected :
      Kakeya.Streamlined.TubeSubfamily normalized.croppedFamily)
    (finalShading : WZ1PaperTubeShading selected.family)
    (selectedNonempty : selected.family.Nonempty)
    (finalCubical : WZ1PaperIsCubicalShading finalShading)
    (finalSubset :
      ∀ index,
        finalShading.carrier index ⊆
          normalized.croppedRefined.carrier
            (selected.embedding index))
    (ordinaryDensity : ENNReal)
    (ordinaryPerTube :
      ∀ index : Fin selected.family.card,
        ordinaryDensity *
            volume
              (normalized.croppedFamily.tube
                (selected.embedding index)).carrier ≤
          volume
            (normalized.frame ''
              normalized.ordinaryRefined.carrier
                (normalized.ordinaryIndex selected index)))
    (lossConstant cwaConstant densityConstant : ENNReal)
    (lossConstantOne : 1 ≤ lossConstant)
    (lossConstantTop : lossConstant ≠ ⊤)
    (lossAbsorption :
      lossConstant⁻¹ ≤ (100 : ENNReal)⁻¹ * ordinaryDensity)
    (selectedCWA :
      WZ2PaperPureCWAAtNearbyScales selected.family cwaConstant)
    (croppedDense : finalShading.IsLambdaDense densityConstant)
    (deltaSmall : delta ≤ 1 / 12) :
    Nonempty
      (PureWZ2CroppedFloorReductionData
        selected.family finalShading lossConstant
          cwaConstant densityConstant) := by
  let ordinaryShading :=
    normalized.finalOrdinaryTrace selected finalShading
  have selectedLine : WZ1PaperIsLineClass selected.family := by
    intro index
    rw [selected.tube_eq index]
    exact normalized.line_class (selected.embedding index)
  have traceLower :
      (100 : ENNReal)⁻¹ * ordinaryDensity * finalShading.mass ≤
        ordinaryShading.mass := by
    exact
      normalized.finalOrdinaryTrace_mass_lower
        selected finalShading normalized.final_extremal.delta_pos
        finalCubical finalSubset ordinaryDensity ordinaryPerTube
  have traceRetention :
      lossConstant⁻¹ * finalShading.mass ≤ ordinaryShading.mass := by
    calc
      lossConstant⁻¹ * finalShading.mass ≤
          ((100 : ENNReal)⁻¹ * ordinaryDensity) *
            finalShading.mass :=
        mul_le_mul_left lossAbsorption _
      _ ≤ ordinaryShading.mass := traceLower
  have unionSubset : ordinaryShading.union ⊆ finalShading.union := by
    rintro point ⟨index, pointMem⟩
    exact ⟨index, pointMem.2⟩
  apply
    PureWZ2CroppedFloorLocalTraceData.toReductionData
      selectedNonempty finalShading
      lossConstant cwaConstant densityConstant
      lossConstantOne lossConstantTop selectedCWA croppedDense
  exact
    {
      ordinaryShading := ordinaryShading
      ordinary_body_mass_le :=
        pureWZ2_ordinary_body_mass_le_cropped_body_mass
          normalized.final_extremal.delta_pos deltaSmall
          selected.family selectedLine
      trace_mass_retention := traceRetention
      ordinary_union_subset := unionSubset
    }

/-- Apply Node 2's ordinary critical floor to one exact cropped subshading
through the normalization's canonical ordinary trace.  This is deliberately
source-local: it does not assert a reduction for arbitrary cropped families. -/
theorem PureWZ2CroppedCriticalNormalizationData.volume_lower_of_trace_and_pure_floor
    {sigma inputLoss normalizationLoss delta floorLoss structuralBudget
      densityLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    (normalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent)
    (selected : Kakeya.Streamlined.TubeSubfamily normalized.croppedFamily)
    (finalShading : WZ1PaperTubeShading selected.family)
    (selectedNonempty : selected.family.Nonempty)
    (finalCubical : WZ1PaperIsCubicalShading finalShading)
    (finalSubset : ∀ index,
      finalShading.carrier index ⊆
        normalized.croppedRefined.carrier (selected.embedding index))
    (ordinaryDensity lossConstant : ENNReal)
    (ordinaryPerTube : ∀ index : Fin selected.family.card,
      ordinaryDensity *
          volume (normalized.croppedFamily.tube
            (selected.embedding index)).carrier ≤
        volume (normalized.frame ''
          normalized.ordinaryRefined.carrier
            (normalized.ordinaryIndex selected index)))
    (criticalFloor : PureWZ2CriticalFloorSelectionData
      sigma floorLoss structuralBudget)
    (lossConstantOne : 1 ≤ lossConstant)
    (lossConstantTop : lossConstant ≠ ⊤)
    (traceAbsorption :
      lossConstant⁻¹ ≤ (100 : ENNReal)⁻¹ * ordinaryDensity)
    (selectedCWA : WZ2PaperPureCWAAtNearbyScales selected.family
      (Kakeya.realRpowENN delta (-densityLoss)))
    (croppedDense : finalShading.IsLambdaDense
      (Kakeya.realRpowENN delta densityLoss))
    (cwaAbsorption :
      lossConstant * Kakeya.realRpowENN delta (-densityLoss) ≤
        Kakeya.realRpowENN delta (-criticalFloor.structuralLoss))
    (densityAbsorption :
      Kakeya.realRpowENN delta criticalFloor.structuralLoss ≤
        lossConstant⁻¹ * Kakeya.realRpowENN delta densityLoss)
    (deltaSmall : delta ≤ 1 / 12)
    (deltaCutoff : delta ≤ criticalFloor.delta₀) :
    Kakeya.realRpowENN delta (sigma + floorLoss) ≤
      volume finalShading.union := by
  rcases normalized.croppedFloorReduction_of_trace selected finalShading
      selectedNonempty finalCubical finalSubset ordinaryDensity ordinaryPerTube
      lossConstant (Kakeya.realRpowENN delta (-densityLoss))
      (Kakeya.realRpowENN delta densityLoss) lossConstantOne lossConstantTop
      traceAbsorption selectedCWA croppedDense deltaSmall with ⟨reduced⟩
  have ordinaryCWA : WZ2PaperPureCWAAtNearbyScales
      reduced.ordinaryFamily
      (Kakeya.realRpowENN delta (-criticalFloor.structuralLoss)) :=
    reduced.ordinary_cwa.mono cwaAbsorption
      (by simp [Kakeya.realRpowENN])
  have ordinaryDense : reduced.ordinaryShading.IsLambdaDense
      (Kakeya.realRpowENN delta criticalFloor.structuralLoss) := by
    exact
      (mul_le_mul_left densityAbsorption
        reduced.ordinaryFamily.toBodyFamily.mass).trans
        reduced.ordinary_dense
  exact
    (criticalFloor.volume_floor delta normalized.final_extremal.delta_pos
      deltaCutoff reduced.ordinaryFamily reduced.ordinary_nonempty
      reduced.ordinaryShading ordinaryCWA ordinaryDense).trans
        reduced.ordinary_union_volume_le

end Kakeya.Assouad

end
