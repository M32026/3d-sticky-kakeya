import MyLeanRepo.Kakeya.Assouad.PureWZ2.PureCriticalFloorSelection
import MyLeanRepo.Kakeya.Assouad.PureWZ2.CroppedCriticalFloorLocalReduction
import MyLeanRepo.Kakeya.Assouad.ConstantAbsorption

/-!
# Ordinary pure critical floor for the Proposition 6.3 tail

This file packages the local ordinary trace needed by one concrete final
cropped shading.  It does not assert a global cropped critical-floor axiom.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

private def proposition63CriticalTailIdentitySubfamily
    {delta : ℝ} (family : Kakeya.Streamlined.TubeFamily delta) :
    Kakeya.Streamlined.TubeSubfamily family where
  family := family
  embedding := Function.Embedding.refl _
  tube_eq _ := rfl

/-- The exact evidence needed to transfer an ordinary critical floor to one
particular cropped tail shading. -/
structure PureWZ2CriticalTailOrdinaryTrace
    {delta structuralLoss : ℝ}
    {croppedFamily : Kakeya.Streamlined.TubeFamily delta}
    (croppedShading : WZ1PaperTubeShading croppedFamily) where
  ordinaryFamily : Kakeya.Streamlined.TubeFamily delta
  ordinaryShading : Kakeya.Streamlined.TubeShading ordinaryFamily
  ordinary_nonempty : ordinaryFamily.Nonempty
  ordinary_cwa : WZ2PaperPureCWAAtNearbyScales ordinaryFamily
    (Kakeya.realRpowENN delta (-structuralLoss))
  ordinary_dense : ordinaryShading.IsLambdaDense
    (Kakeya.realRpowENN delta structuralLoss)
  ordinary_union_subset : ordinaryShading.union ⊆ croppedShading.union

/-- The family-free scalar receipt required by the trace constructor.  The
upstream loss schedule can obtain this uniformly from a positive gap
`structuralLoss - traceLoss - finalLoss`. -/
structure Proposition63PureCriticalTailTraceAbsorption
    (delta structuralLoss traceLoss finalLoss : ℝ) : Prop where
  absorb : Kakeya.realRpowENN delta structuralLoss ≤
    (100 : ENNReal)⁻¹ * Kakeya.realRpowENN delta traceLoss *
      Kakeya.realRpowENN delta finalLoss

/-- A scale cutoff producing the trace absorption uniformly, with no family
or shading parameters. -/
structure Proposition63PureCriticalTailTraceAbsorptionSchedule
    (structuralLoss traceLoss finalLoss : ℝ) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  absorb : ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
    Proposition63PureCriticalTailTraceAbsorption
      delta structuralLoss traceLoss finalLoss

/-- A positive exponent gap absorbs the fixed trace constant `100`. -/
theorem proposition63_pureCriticalTailTraceAbsorptionSchedule
    {structuralLoss traceLoss finalLoss : ℝ}
    (gapPos : traceLoss + finalLoss < structuralLoss) :
    Nonempty (Proposition63PureCriticalTailTraceAbsorptionSchedule
      structuralLoss traceLoss finalLoss) := by
  let gap := structuralLoss - traceLoss - finalLoss
  have gap_pos : 0 < gap := by
    dsimp only [gap]
    linarith
  rcases exists_delta_realRpowENN_bound (100 : ENNReal) (by norm_num)
      gap_pos with ⟨delta₀, delta₀Pos, delta₀One, bound⟩
  refine ⟨{
    delta₀ := delta₀
    delta₀_pos := delta₀Pos
    delta₀_le_one := delta₀One
    absorb := ?_
  }⟩
  intro delta deltaPos deltaLe
  have hbound := bound delta deltaPos deltaLe
  refine ⟨?_⟩
  calc
    Kakeya.realRpowENN delta structuralLoss =
        (100 : ENNReal)⁻¹ *
          (Kakeya.realRpowENN delta structuralLoss * 100) := by
      rw [mul_comm (Kakeya.realRpowENN delta structuralLoss) 100,
        ← mul_assoc, ENNReal.inv_mul_cancel]
      · simp
      · norm_num
      · norm_num
    _ ≤ (100 : ENNReal)⁻¹ *
        (Kakeya.realRpowENN delta structuralLoss *
          Kakeya.realRpowENN delta (-gap)) := by gcongr
    _ = (100 : ENNReal)⁻¹ *
        Kakeya.realRpowENN delta (traceLoss + finalLoss) := by
      rw [← realRpowENN_add deltaPos]
      congr 2
      dsimp only [gap]
      ring
    _ = (100 : ENNReal)⁻¹ * Kakeya.realRpowENN delta traceLoss *
        Kakeya.realRpowENN delta finalLoss := by
      rw [realRpowENN_add deltaPos]
      ring

/-- Build the local ordinary witness on the identity subfamily of a completed
normalization.  The final trace pays exactly the fixed `1/100` loss and the
caller-specified per-tube trace exponent. -/
noncomputable def PureWZ2CroppedCriticalNormalizationData.criticalTailOrdinaryTrace_identity
    {sigma inputLoss normalizationLoss delta structuralLoss traceLoss
      finalLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma inputLoss delta}
    {normalizationExponent : ℕ}
    (normalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent)
    (finalShading : WZ1PaperTubeShading normalized.croppedFamily)
    (finalCubical : WZ1PaperIsCubicalShading finalShading)
    (finalSubset : ∀ index, finalShading.carrier index ⊆
      normalized.croppedRefined.carrier index)
    (ordinaryPerTube :
      ∀ index : Fin normalized.croppedFamily.card,
        Kakeya.realRpowENN delta traceLoss *
            volume (normalized.croppedFamily.tube index).carrier ≤
          volume (normalized.frame ''
            normalized.ordinaryRefined.carrier
              (normalized.ordinaryIndex
                (proposition63CriticalTailIdentitySubfamily
                  normalized.croppedFamily) index)))
    (finalExtremal : WZ2PaperCroppedIsExtremal
      sigma finalLoss normalized.croppedFamily finalShading)
    (pureCWA : WZ2PaperPureCWAAtNearbyScales normalized.croppedFamily
      (Kakeya.realRpowENN delta (-structuralLoss)))
    (deltaSmall : delta ≤ 1 / 12)
    (absorption : Proposition63PureCriticalTailTraceAbsorption
      delta structuralLoss traceLoss finalLoss) :
    PureWZ2CriticalTailOrdinaryTrace
      (structuralLoss := structuralLoss) finalShading := by
  let selected :=
    proposition63CriticalTailIdentitySubfamily normalized.croppedFamily
  let trace := normalized.finalOrdinaryTrace selected finalShading
  have finalSubset' : ∀ index, finalShading.carrier index ⊆
      normalized.croppedRefined.carrier (selected.embedding index) := by
    intro index point pointMem
    exact finalSubset index pointMem
  have traceMass :
      (100 : ENNReal)⁻¹ * Kakeya.realRpowENN delta traceLoss *
          finalShading.mass ≤ trace.mass := by
    exact normalized.finalOrdinaryTrace_mass_lower selected finalShading
      finalExtremal.delta_pos finalCubical finalSubset'
      (Kakeya.realRpowENN delta traceLoss) ordinaryPerTube
  have bodyMass : normalized.croppedFamily.toBodyFamily.mass ≤
      (wz1PaperBodyFamily normalized.croppedFamily).mass :=
    pureWZ2_ordinary_body_mass_le_cropped_body_mass
      finalExtremal.delta_pos deltaSmall
      normalized.croppedFamily normalized.line_class
  have traceDense : trace.IsLambdaDense
      (Kakeya.realRpowENN delta structuralLoss) := by
    change Kakeya.realRpowENN delta structuralLoss *
        normalized.croppedFamily.toBodyFamily.mass ≤ trace.mass
    calc
      Kakeya.realRpowENN delta structuralLoss *
            normalized.croppedFamily.toBodyFamily.mass ≤
          Kakeya.realRpowENN delta structuralLoss *
            (wz1PaperBodyFamily normalized.croppedFamily).mass := by
        gcongr
      _ ≤ ((100 : ENNReal)⁻¹ * Kakeya.realRpowENN delta traceLoss *
            Kakeya.realRpowENN delta finalLoss) *
          (wz1PaperBodyFamily normalized.croppedFamily).mass := by
        gcongr
        exact absorption.absorb
      _ = (100 : ENNReal)⁻¹ * Kakeya.realRpowENN delta traceLoss *
          (Kakeya.realRpowENN delta finalLoss *
            (wz1PaperBodyFamily normalized.croppedFamily).mass) := by ring
      _ ≤ (100 : ENNReal)⁻¹ * Kakeya.realRpowENN delta traceLoss *
          finalShading.mass := by
        gcongr
        exact finalExtremal.dense
      _ ≤ trace.mass := traceMass
  exact {
    ordinaryFamily := normalized.croppedFamily
    ordinaryShading := trace
    ordinary_nonempty := finalExtremal.nonempty
    ordinary_cwa := pureCWA
    ordinary_dense := traceDense
    ordinary_union_subset := by
      rintro point ⟨index, pointMem⟩
      exact ⟨index, pointMem.2⟩
  }

/-- The critical-floor step used by the final cell-mass argument. -/
theorem PureWZ2CriticalFloorSelectionData.cropped_union_floor_of_trace
    {sigma floorLoss structuralBudget delta : ℝ}
    {croppedFamily : Kakeya.Streamlined.TubeFamily delta}
    {croppedShading : WZ1PaperTubeShading croppedFamily}
    (critical : PureWZ2CriticalFloorSelectionData
      sigma floorLoss structuralBudget)
    (deltaPos : 0 < delta)
    (deltaSmall : delta ≤ critical.delta₀)
    (trace : PureWZ2CriticalTailOrdinaryTrace
      (structuralLoss := critical.structuralLoss) croppedShading) :
    Kakeya.realRpowENN delta (sigma + floorLoss) ≤
      volume croppedShading.union := by
  exact (critical.volume_floor delta deltaPos deltaSmall
    trace.ordinaryFamily trace.ordinary_nonempty trace.ordinaryShading
    trace.ordinary_cwa trace.ordinary_dense).trans
      (measure_mono trace.ordinary_union_subset)

end Kakeya.Assouad

end
