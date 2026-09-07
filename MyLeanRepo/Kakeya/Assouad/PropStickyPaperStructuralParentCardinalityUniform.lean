import MyLeanRepo.Kakeya.Assouad.PropStickyPreparedParentwiseStructuralProducerStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperMergedTopLevelCWA

/-!
# Uniform cardinality of the structural parent fibers

The caller cover has uniformly comparable ambient full-fiber cardinalities.
Each one-parent structural selection has the same weighted cardinality
retention loss.  Combining these facts gives one common comparison between
the selected structural fibers over any two caller parents.

This is the formal counterpart of the additional parent pigeonholing used
before the final `mu_fine mu_coarse` comparison.
-/

noncomputable section

namespace Kakeya.Assouad

def wz2PaperStructuralParentCardinalityWeight
    (delta sourceLoss : ℝ) : ENNReal :=
  (1 / 2 : ENNReal) * Kakeya.realRpowENN delta sourceLoss

def wz2PaperStructuralParentCardinalityConstant
    {delta sourceLoss stableLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {preparationExponent : ℕ}
    (prepared :
      WZ2PaperCallerStrictPreparationData
        (sourceLoss := sourceLoss)
        (stableLoss := stableLoss)
        shading caller preparationExponent) : ENNReal :=
  prepared.structuralConstant *
    (wz2PaperPreparedOneParentFiniteLoss sourceLoss *
      (55296 * Kakeya.deltaTubeVolume 1))

theorem wz2_paper_structural_parent_cardinality_uniform
    {delta sourceLoss stableLoss sigma floorLoss strongLoss outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {preparationExponent : ℕ}
    (prepared :
      WZ2PaperCallerStrictPreparationData
        (sourceLoss := sourceLoss)
        (stableLoss := stableLoss)
        shading caller preparationExponent)
    (critical :
      WZ2PaperCriticalFloorSelectionData
        sigma floorLoss strongLoss)
    (structural :
      WZ2PaperPreparedParentwiseStructuralProducerData
        (outputLoss := outputLoss) prepared critical) :
    ∀ first second : Fin prepared.callerStrict.coarse.card,
      wz2PaperStructuralParentCardinalityWeight delta sourceLoss *
          ((structural.fiberProducer first).selection.refinement
            |>.selected.family.enncard) ≤
        wz2PaperStructuralParentCardinalityConstant
            (sourceLoss := sourceLoss) prepared *
          ((structural.fiberProducer second).selection.refinement
            |>.selected.family.enncard) := by
  intro first second
  let weight :=
    wz2PaperStructuralParentCardinalityWeight delta sourceLoss
  let finiteLoss :=
    wz2PaperPreparedOneParentFiniteLoss sourceLoss
  let geometry := 55296 * Kakeya.deltaTubeVolume 1
  let firstAmbient :=
    (wz2PaperPreparedOneParentFiber prepared first).family.enncard
  let secondAmbient :=
    (wz2PaperPreparedOneParentFiber prepared second).family.enncard
  let firstSelected :=
    (structural.fiberProducer first).selection.refinement
      |>.selected.family.enncard
  let secondSelected :=
    (structural.fiberProducer second).selection.refinement
      |>.selected.family.enncard
  have hFirstSelected : firstSelected ≤ firstAmbient := by
    let selected :=
      (structural.fiberProducer first).selection.refinement.selected
    change
      (selected.family.card : ENNReal) ≤
      ((wz2PaperPreparedOneParentFiber prepared first).family.card :
        ENNReal)
    have hCard :
        selected.family.card ≤
          (wz2PaperPreparedOneParentFiber prepared first).family.card := by
      simpa [Fintype.card_fin] using
        Fintype.card_le_of_injective
          selected.embedding selected.embedding.injective
    exact_mod_cast hCard
  have hAmbient :
      firstAmbient ≤ prepared.structuralConstant * secondAmbient := by
    exact prepared.callerStrict.full_fiber_uniform first second
  let quantitative :=
    (structural.fiberProducer second).quantitative
  have hMassConstant :
      quantitative.massRetentionConstant ≤ finiteLoss := by
    rw [quantitative.massRetentionConstant_eq]
    dsimp only [finiteLoss, wz2PaperPreparedOneParentFiniteLoss]
    have hDepth :
        wz2PaperPreparedOneParentFineScaleCount prepared second ≤
          wz2PaperPreparedOneParentDepth sourceLoss := by
      dsimp only [wz2PaperPreparedOneParentFineScaleCount,
        wz2PaperPreparedOneParentDepth]
      calc
        prepared.strictScaleCount - prepared.callerLevel.val ≤
            prepared.strictScaleCount := Nat.sub_le _ _
        _ ≤ prepared.levelCount + 1 :=
          prepared.strictScaleCount_le
        _ = Nat.ceil (1 / sourceLoss) + 2 := by
          rw [prepared.levelCount_eq]
    gcongr
    exact (by norm_num : (1 : ENNReal) ≤ 2)
  have hCardinalityConstant :
      quantitative.cardinalityRetentionConstant ≤ finiteLoss * geometry := by
    rw [quantitative.cardinalityRetentionConstant_eq]
    exact mul_le_mul_right' hMassConstant geometry
  have hRetention :
      weight * secondAmbient ≤
        (finiteLoss * geometry) * secondSelected := by
    calc
      weight * secondAmbient =
          quantitative.weight * secondAmbient := by
        rw [quantitative.weight_eq]
        rfl
      _ ≤
          quantitative.cardinalityRetentionConstant * secondSelected :=
        quantitative.global_retention
      _ ≤ (finiteLoss * geometry) * secondSelected := by
        gcongr
  calc
    weight * firstSelected ≤ weight * firstAmbient := by
      gcongr
    _ ≤ weight * (prepared.structuralConstant * secondAmbient) := by
      gcongr
    _ =
        prepared.structuralConstant * (weight * secondAmbient) := by
      ring
    _ ≤
        prepared.structuralConstant *
          ((finiteLoss * geometry) * secondSelected) := by
      gcongr
    _ =
        wz2PaperStructuralParentCardinalityConstant
            (sourceLoss := sourceLoss) prepared *
          secondSelected := by
      simp [wz2PaperStructuralParentCardinalityConstant,
        finiteLoss, geometry]
      ring

theorem wz2_paper_weighted_uniform_fiber_product
    {Parent : Type*} [Fintype Parent] [Nonempty Parent]
    (fiberCardinality : Parent → ENNReal)
    (weight constant total : ENNReal)
    (hUniform :
      ∀ first second,
        weight * fiberCardinality first ≤
          constant * fiberCardinality second)
    (hTotal :
      (∑ parent, fiberCardinality parent) = total) :
    ∀ parent,
      weight * fiberCardinality parent *
          (Fintype.card Parent : ENNReal) ≤
        constant * total := by
  intro parent
  calc
    weight * fiberCardinality parent *
          (Fintype.card Parent : ENNReal) =
        ∑ _other : Parent,
          weight * fiberCardinality parent := by
      simp [mul_comm]
    _ ≤
        ∑ other : Parent,
          constant * fiberCardinality other := by
      exact Finset.sum_le_sum fun other _ => hUniform parent other
    _ = constant * total := by
      rw [← Finset.mul_sum, hTotal]

end Kakeya.Assouad

end
