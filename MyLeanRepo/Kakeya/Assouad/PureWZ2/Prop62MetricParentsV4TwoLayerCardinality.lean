import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62TwoLayerCardinality
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62PaperAudit.StatementsV4

/-!
# Two-layer cardinality for the frozen metric-parent output

The frozen metric-parent output does not expose ordinary essential
distinctness or bounded-base geometry for its refined fine family.  The
rescaled full fibers nevertheless have exactly the local geometry needed for
the six-parameter packing argument: their canonical ordinary rescalings are
essentially distinct and all their midpoints lie in the radius-three ball.

This module records the resulting uniform bound for every full metric fiber
and sums those bounds over the coarse parent map.  The coarse factor is
controlled separately by the five-parameter packing theorem for
`WZ1PaperIsLineClass`; thus no global ordinary distinctness or bounded-base
hypothesis on the refined fine family is used.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/- The former mixed generic/frozen implementation is retained temporarily as
reference text but is no longer elaborated. -/
/-
/-- The six-dimensional packing count at the rescaled fiber scale. -/
def pureWZ2Prop62RescaledFiberPackingBound
    (delta rho : ℝ) : ℕ :=
  (2 * Nat.ceil (3 / ((delta / rho) / 64)) + 1) ^ 3 *
    (2 * Nat.ceil (1 / ((delta / rho) / 64)) + 1) ^ 3

/-- One grid base simultaneously dominating the coarse and rescaled-fiber
packing counts. -/
def pureWZ2Prop62TwoLayerGridBase (delta : ℝ) : ℕ :=
  2 * Nat.ceil (192 / delta) + 1

/-- Explicit coefficient for the logarithm of an eleven-dimensional grid
count. -/
def pureWZ2Prop62TwoLayerCardLogConstant : ℝ :=
  max
    (Real.log (2 * (387 : ℝ) ^ 11) / Real.log 2 + 1)
    (11 / Real.log 2)

theorem pureWZ2Prop62_rescaledFiberPackingBound_le_twoLayer
    {delta rho : ℝ}
    (deltaPos : 0 < delta)
    (rhoPos : 0 < rho)
    (rhoLeOne : rho ≤ 1) :
    pureWZ2Prop62RescaledFiberPackingBound delta rho ≤
      pureWZ2Prop62TwoLayerGridBase delta ^ 6 := by
  have firstArgument :
      3 / ((delta / rho) / 64) = 192 * rho / delta := by
    field_simp [deltaPos.ne', rhoPos.ne']
    ring
  have firstBound : 192 * rho / delta ≤ 192 / delta := by
    apply (div_le_div_iff_of_pos_right deltaPos).2
    nlinarith
  have secondArgument :
      1 / ((delta / rho) / 64) = 64 * rho / delta := by
    field_simp [deltaPos.ne', rhoPos.ne']
  have secondBound : 64 * rho / delta ≤ 192 / delta := by
    apply (div_le_div_iff_of_pos_right deltaPos).2
    nlinarith
  have firstCeil :
      Nat.ceil (3 / ((delta / rho) / 64)) ≤
        Nat.ceil (192 / delta) := by
    rw [firstArgument]
    exact Nat.ceil_mono firstBound
  have secondCeil :
      Nat.ceil (1 / ((delta / rho) / 64)) ≤
        Nat.ceil (192 / delta) := by
    rw [secondArgument]
    exact Nat.ceil_mono secondBound
  unfold pureWZ2Prop62RescaledFiberPackingBound
  unfold pureWZ2Prop62TwoLayerGridBase
  calc
    (2 * Nat.ceil (3 / ((delta / rho) / 64)) + 1) ^ 3 *
          (2 * Nat.ceil (1 / ((delta / rho) / 64)) + 1) ^ 3 ≤
        (2 * Nat.ceil (192 / delta) + 1) ^ 3 *
          (2 * Nat.ceil (192 / delta) + 1) ^ 3 := by
      gcongr
    _ = (2 * Nat.ceil (192 / delta) + 1) ^ 6 := by ring

theorem pureWZ2Prop62_rescaledFiber_source_card_le
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {parent : Fin coarse.card}
    {sourceConstant : ENNReal}
    (input :
      PureWZ2Prop62MetricFiberRescalingInput
        cover parent sourceConstant) :
    input.sourceFamily.card ≤
      pureWZ2Prop62RescaledFiberPackingBound delta rho := by
  let rescaled :=
    wz2PaperLiteralOrdinaryRescaledFamily
      input.sourceFamily (coarse.tube parent) input.rho_pos
  have rescaledDistinct :
      WZ2PaperOrdinaryIsEssentiallyDistinct rescaled :=
    wz2PaperOrdinaryRescaled_essentiallyDistinct_of_locality
      input.rho_pos input.rho_le_one input.delta_pos
      input.scale_separation input.source_line_class
      input.anchor_line_class input.source_covered
      input.source_strongly_separated input.target_locality
  have packed :=
    wz2PaperOrdinary_local_six_grid_card_bound
      (div_pos input.delta_pos input.rho_pos)
      (show (0 : ℝ) ≤ 3 by norm_num)
      rescaledDistinct Finset.univ (0 : Point3) <| by
        intro index _
        simpa [rescaled, dist_zero_right] using
          input.target_locality index
  have rescaledCard : rescaled.card = input.sourceFamily.card := rfl
  rw [rescaledCard] at packed
  simpa [
    pureWZ2Prop62RescaledFiberPackingBound,
    Finset.card_univ, Fintype.card_fin
  ] using packed

theorem pureWZ2Prop62_rescaledFiber_fullFiber_card_le
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {parent : Fin coarse.card}
    {sourceConstant : ENNReal}
    (input :
      PureWZ2Prop62MetricFiberRescalingInput
        cover parent sourceConstant) :
    (wz2PaperFullFiberIndices fine coarse parent).card ≤
      pureWZ2Prop62RescaledFiberPackingBound delta rho := by
  have cardEq :
      input.sourceFamily.card = input.sourceIndices.card := by
    simpa using Fintype.card_congr input.sourceEquiv
  rw [← input.sourceIndices_eq, ← cardEq]
  exact pureWZ2Prop62_rescaledFiber_source_card_le input

theorem pureWZ2Prop62_rescaledFiber_source_card_le_standard
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {parent : Fin coarse.card}
    {sourceConstant : ENNReal}
    (input :
      PureWZ2Prop62MetricFiberRescalingInput
        cover parent sourceConstant) :
    input.sourceFamily.card ≤
      (2 * Nat.ceil (320 / delta) + 1) ^ 6 := by
  let rescaled :=
    wz2PaperLiteralOrdinaryRescaledFamily
      input.sourceFamily (coarse.tube parent) input.rho_pos
  have rescaledDistinct :
      WZ2PaperOrdinaryIsEssentiallyDistinct rescaled :=
    wz2PaperOrdinaryRescaled_essentiallyDistinct_of_locality
      input.rho_pos input.rho_le_one input.delta_pos
      input.scale_separation input.source_line_class
      input.anchor_line_class input.source_covered
      input.source_strongly_separated input.target_locality
  have packed :=
    wz2PaperOrdinary_local_six_grid_card_bound
      (div_pos input.delta_pos input.rho_pos)
      (show (0 : ℝ) ≤ 3 by norm_num)
      rescaledDistinct Finset.univ (0 : Point3) <| by
        intro index _
        simpa [rescaled, dist_zero_right] using
          input.target_locality index
  have firstArgument :
      3 / ((delta / rho) / 64) = 192 * rho / delta := by
    field_simp [input.delta_pos.ne', input.rho_pos.ne']
    ring
  have firstBound : 192 * rho / delta ≤ 320 / delta := by
    apply (div_le_div_iff_of_pos_right input.delta_pos).2
    nlinarith [input.rho_le_one]
  have secondArgument :
      1 / ((delta / rho) / 64) = 64 * rho / delta := by
    field_simp [input.delta_pos.ne', input.rho_pos.ne']
  have secondBound : 64 * rho / delta ≤ 320 / delta := by
    apply (div_le_div_iff_of_pos_right input.delta_pos).2
    nlinarith [input.rho_le_one]
  have firstCeil :
      Nat.ceil (3 / ((delta / rho) / 64)) ≤
        Nat.ceil (320 / delta) := by
    rw [firstArgument]
    exact Nat.ceil_mono firstBound
  have secondCeil :
      Nat.ceil (1 / ((delta / rho) / 64)) ≤
        Nat.ceil (320 / delta) := by
    rw [secondArgument]
    exact Nat.ceil_mono secondBound
  have rescaledCard : rescaled.card = input.sourceFamily.card := rfl
  rw [rescaledCard] at packed
  simpa only [Finset.card_univ, Fintype.card_fin] using
    packed.trans (by
      calc
        (2 * Nat.ceil (3 / ((delta / rho) / 64)) + 1) ^ 3 *
              (2 * Nat.ceil (1 / ((delta / rho) / 64)) + 1) ^ 3 ≤
            (2 * Nat.ceil (320 / delta) + 1) ^ 3 *
              (2 * Nat.ceil (320 / delta) + 1) ^ 3 := by
          gcongr
        _ = (2 * Nat.ceil (320 / delta) + 1) ^ 6 := by ring)

theorem pureWZ2Prop62_rescaledFiber_source_log_le
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {parent : Fin coarse.card}
    {sourceConstant : ENNReal}
    (input :
      PureWZ2Prop62MetricFiberRescalingInput
        cover parent sourceConstant) :
    (Nat.log 2 (2 * input.sourceFamily.card) + 1 : ℝ) ≤
      pureWZ2Prop62OrdinaryCardLogConstant *
        (1 + Real.log delta⁻¹) := by
  have sourceNonempty : input.sourceFamily.Nonempty := by
    change 0 < input.sourceFamily.card
    have indicesPos : 0 < input.sourceIndices.card :=
      input.sourceIndices_nonempty.card_pos
    have cardEq :
        input.sourceFamily.card = input.sourceIndices.card := by
      simpa using Fintype.card_congr input.sourceEquiv
    rwa [cardEq]
  exact
    pureWZ2Prop62_ordinary_card_log_bound
      input.delta_pos
      (by nlinarith [input.scale_separation, input.rho_le_one])
      sourceNonempty
      (pureWZ2Prop62_rescaledFiber_source_card_le_standard input)

theorem pureWZ2Prop62_rescaledFiber_fullFiber_card_le_standard
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {parent : Fin coarse.card}
    {sourceConstant : ENNReal}
    (input :
      PureWZ2Prop62MetricFiberRescalingInput
        cover parent sourceConstant) :
    (wz2PaperFullFiberIndices fine coarse parent).card ≤
      (2 * Nat.ceil (320 / delta) + 1) ^ 6 := by
  have cardEq :
      input.sourceFamily.card = input.sourceIndices.card := by
    simpa using Fintype.card_congr input.sourceEquiv
  rw [← input.sourceIndices_eq, ← cardEq]
  exact pureWZ2Prop62_rescaledFiber_source_card_le_standard input

theorem pureWZ2Prop62_metricFiber_source_essentiallyDistinct
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {parent : Fin coarse.card}
    {sourceConstant : ENNReal}
    (input :
      PureWZ2Prop62MetricFiberRescalingInput
        cover parent sourceConstant) :
    WZ1PaperIsEssentiallyDistinct input.sourceFamily := by
  intro first second firstNeSecond
  have stronglySeparated :=
    input.source_strongly_separated first second firstNeSecond
  have deltaLtStrong :
      delta <
        wz2PaperLiteralSourceSeparationFactor * delta := by
    calc
      delta = 1 * delta := by ring
      _ <
          wz2PaperLiteralSourceSeparationFactor * delta := by
        apply mul_lt_mul_of_pos_right _ input.delta_pos
        norm_num [wz2PaperLiteralSourceSeparationFactor]
  exact deltaLtStrong.trans stronglySeparated

theorem pureWZ2Prop62_metricFiber_source_card_le_five
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {parent : Fin coarse.card}
    {sourceConstant : ENNReal}
    (input :
      PureWZ2Prop62MetricFiberRescalingInput
        cover parent sourceConstant) :
    input.sourceFamily.card ≤
      (2 * Nat.ceil (8 * rho / delta) + 1) ^ 5 := by
  let reference : Fin input.sourceFamily.card :=
    input.sourceEquiv.symm
      ⟨input.sourceIndices_nonempty.choose,
        input.sourceIndices_nonempty.choose_spec⟩
  have everySourceNearReference :
      ∀ index : Fin input.sourceFamily.card,
        wz1PaperLineDistance
            (input.sourceFamily.tube index)
            (input.sourceFamily.tube reference) ≤ rho := by
    intro index
    have indexCovered := input.source_covered index
    have referenceCovered := input.source_covered reference
    have triangle :=
      wz1PaperLineDistance_triangle
        (input.sourceFamily.tube index)
        (coarse.tube parent)
        (input.sourceFamily.tube reference)
    have symmetry :
        wz1PaperLineDistance
            (coarse.tube parent)
            (input.sourceFamily.tube reference) =
          wz1PaperLineDistance
            (input.sourceFamily.tube reference)
            (coarse.tube parent) :=
      wz1PaperLineDistance_symm _ _
    rw [symmetry] at triangle
    unfold WZ1PaperTubeCovers at indexCovered referenceCovered
    linarith
  have packed :=
    tube_packing_bound_general
      (pureWZ2Prop62_metricFiber_source_essentiallyDistinct input)
      input.source_line_class input.delta_pos rho input.rho_pos reference
  have allIndices :
      (Finset.univ.filter fun index : Fin input.sourceFamily.card =>
        wz1PaperLineDistance
            (input.sourceFamily.tube index)
            (input.sourceFamily.tube reference) ≤ rho) =
        Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro index
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact everySourceNearReference index
  rw [allIndices] at packed
  simpa only [Finset.card_univ, Fintype.card_fin] using packed

theorem pureWZ2Prop62_metricFiber_fullFiber_card_le_five
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {parent : Fin coarse.card}
    {sourceConstant : ENNReal}
    (input :
      PureWZ2Prop62MetricFiberRescalingInput
        cover parent sourceConstant) :
    (wz2PaperFullFiberIndices fine coarse parent).card ≤
      (2 * Nat.ceil (8 * rho / delta) + 1) ^ 5 := by
  have cardEq :
      input.sourceFamily.card = input.sourceIndices.card := by
    simpa using Fintype.card_congr input.sourceEquiv
  rw [← input.sourceIndices_eq, ← cardEq]
  exact pureWZ2Prop62_metricFiber_source_card_le_five input

theorem MetricParentsAtPrescribedScaleData.fullFiber_card_le
    {delta : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    {fineParentDistanceConstant : ℝ}
    {parentConstant fiberConstant : ENNReal}
    (metric :
      Prop62PaperAudit.V4.MetricParentsAtPrescribedScaleData
        sourceShading rho fineParentDistanceConstant
        parentConstant fiberConstant)
    (parent : Fin metric.scaleData.coarse.card) :
    (wz2PaperFullFiberIndices
        metric.refinement.selected.family
        metric.scaleData.coarse parent).card ≤
      pureWZ2Prop62RescaledFiberPackingBound delta rho.1 := by
  let fiberData :=
    Classical.choice (metric.scaleData.rescaledFiber parent)
  exact
    pureWZ2Prop62_rescaledFiber_fullFiber_card_le
      fiberData.rescalingInput

theorem MetricParentsAtPrescribedScaleData.fullFiber_card_le_five
    {delta : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    {fineParentDistanceConstant : ℝ}
    {parentConstant fiberConstant : ENNReal}
    (metric :
      Prop62PaperAudit.V4.MetricParentsAtPrescribedScaleData
        sourceShading rho fineParentDistanceConstant
        parentConstant fiberConstant)
    (parent : Fin metric.scaleData.coarse.card) :
    (wz2PaperFullFiberIndices
        metric.refinement.selected.family
        metric.scaleData.coarse parent).card ≤
      (2 * Nat.ceil (8 * rho.1 / delta) + 1) ^ 5 := by
  let fiberData :=
    Classical.choice (metric.scaleData.rescaledFiber parent)
  exact
    pureWZ2Prop62_metricFiber_fullFiber_card_le_five
      fiberData.rescalingInput

theorem MetricParentsAtPrescribedScaleData.fullFiber_card_le_standard
    {delta : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    {fineParentDistanceConstant : ℝ}
    {parentConstant fiberConstant : ENNReal}
    (metric :
      Prop62PaperAudit.V4.MetricParentsAtPrescribedScaleData
        sourceShading rho fineParentDistanceConstant
        parentConstant fiberConstant)
    (parent : Fin metric.scaleData.coarse.card) :
    (wz2PaperFullFiberIndices
        metric.refinement.selected.family
        metric.scaleData.coarse parent).card ≤
      (2 * Nat.ceil (320 / delta) + 1) ^ 6 := by
  let fiberData :=
    Classical.choice (metric.scaleData.rescaledFiber parent)
  exact
    pureWZ2Prop62_rescaledFiber_fullFiber_card_le_standard
      fiberData.rescalingInput

theorem MetricParentsAtPrescribedScaleData.fine_card_le_coarse_mul_fiberPacking
    {delta : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    {fineParentDistanceConstant : ℝ}
    {parentConstant fiberConstant : ENNReal}
    (metric :
      Prop62PaperAudit.V4.MetricParentsAtPrescribedScaleData
        sourceShading rho fineParentDistanceConstant
        parentConstant fiberConstant) :
    metric.refinement.selected.family.card ≤
      metric.scaleData.coarse.card *
        pureWZ2Prop62RescaledFiberPackingBound delta rho.1 := by
  let fine := metric.refinement.selected.family
  let coarse := metric.scaleData.coarse
  let parentMap := metric.scaleData.cover.parent
  have fiberEq :
      ∀ parent : Fin coarse.card,
        ((Finset.univ : Finset (Fin fine.card)).filter fun sourceIndex =>
            parentMap sourceIndex = parent) =
          wz2PaperFullFiberIndices fine coarse parent := by
    intro parent
    ext sourceIndex
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      mem_wz2PaperFullFiberIndices_iff]
    exact metric.metric_fiber sourceIndex parent
  have fiberSum :
      ∑ parent : Fin coarse.card,
          ((Finset.univ : Finset (Fin fine.card)).filter fun sourceIndex =>
            parentMap sourceIndex = parent).card =
        fine.card := by
    have partition :=
      Finset.sum_card_fiberwise_eq_card_filter
        (Finset.univ : Finset (Fin fine.card))
        (Finset.univ : Finset (Fin coarse.card))
        parentMap
    simpa only [Finset.mem_univ, Finset.filter_true,
      Finset.card_univ, Fintype.card_fin] using partition
  calc
    fine.card =
        ∑ parent : Fin coarse.card,
          ((Finset.univ : Finset (Fin fine.card)).filter fun sourceIndex =>
            parentMap sourceIndex = parent).card := fiberSum.symm
    _ =
        ∑ parent : Fin coarse.card,
          (wz2PaperFullFiberIndices fine coarse parent).card := by
      apply Finset.sum_congr rfl
      intro parent _
      rw [fiberEq parent]
    _ ≤
        ∑ _parent : Fin coarse.card,
          pureWZ2Prop62RescaledFiberPackingBound delta rho.1 := by
      apply Finset.sum_le_sum
      intro parent _
      exact
        MetricParentsAtPrescribedScaleData.fullFiber_card_le
          metric parent
    _ =
        coarse.card *
          pureWZ2Prop62RescaledFiberPackingBound delta rho.1 := by
      simp

theorem MetricParentsAtPrescribedScaleData.fine_card_le_coarse_mul_standard
    {delta : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    {fineParentDistanceConstant : ℝ}
    {parentConstant fiberConstant : ENNReal}
    (metric :
      Prop62PaperAudit.V4.MetricParentsAtPrescribedScaleData
        sourceShading rho fineParentDistanceConstant
        parentConstant fiberConstant) :
    metric.refinement.selected.family.card ≤
      metric.scaleData.coarse.card *
        (2 * Nat.ceil (320 / delta) + 1) ^ 6 := by
  let fine := metric.refinement.selected.family
  let coarse := metric.scaleData.coarse
  let parentMap := metric.scaleData.cover.parent
  have fiberEq :
      ∀ parent : Fin coarse.card,
        ((Finset.univ : Finset (Fin fine.card)).filter fun sourceIndex =>
            parentMap sourceIndex = parent) =
          wz2PaperFullFiberIndices fine coarse parent := by
    intro parent
    ext sourceIndex
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      mem_wz2PaperFullFiberIndices_iff]
    exact metric.metric_fiber sourceIndex parent
  have fiberSum :
      ∑ parent : Fin coarse.card,
          ((Finset.univ : Finset (Fin fine.card)).filter fun sourceIndex =>
            parentMap sourceIndex = parent).card =
        fine.card := by
    have partition :=
      Finset.sum_card_fiberwise_eq_card_filter
        (Finset.univ : Finset (Fin fine.card))
        (Finset.univ : Finset (Fin coarse.card))
        parentMap
    simpa only [Finset.mem_univ, Finset.filter_true,
      Finset.card_univ, Fintype.card_fin] using partition
  calc
    fine.card =
        ∑ parent : Fin coarse.card,
          ((Finset.univ : Finset (Fin fine.card)).filter fun sourceIndex =>
            parentMap sourceIndex = parent).card := fiberSum.symm
    _ =
        ∑ parent : Fin coarse.card,
          (wz2PaperFullFiberIndices fine coarse parent).card := by
      apply Finset.sum_congr rfl
      intro parent _
      rw [fiberEq parent]
    _ ≤
        ∑ _parent : Fin coarse.card,
          (2 * Nat.ceil (320 / delta) + 1) ^ 6 := by
      apply Finset.sum_le_sum
      intro parent _
      exact
        MetricParentsAtPrescribedScaleData.fullFiber_card_le_standard
          metric parent
    _ =
        coarse.card * (2 * Nat.ceil (320 / delta) + 1) ^ 6 := by
      simp

theorem MetricParentsAtPrescribedScaleData.fine_card_le_five_by_five
    {delta : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    {fineParentDistanceConstant : ℝ}
    {parentConstant fiberConstant : ENNReal}
    (metric :
      Prop62PaperAudit.V4.MetricParentsAtPrescribedScaleData
        sourceShading rho fineParentDistanceConstant
        parentConstant fiberConstant) :
    metric.refinement.selected.family.card ≤
      (2 * Nat.ceil (80 / rho.1) + 1) ^ 5 *
        (2 * Nat.ceil (8 * rho.1 / delta) + 1) ^ 5 := by
  let fine := metric.refinement.selected.family
  let coarse := metric.scaleData.coarse
  let parentMap := metric.scaleData.cover.parent
  have coarseBound :
      coarse.card ≤
        (2 * Nat.ceil (80 / rho.1) + 1) ^ 5 :=
    paper_essentially_distinct_card_bound_nat
      metric.scaleData.section6Cover.coarse_essentially_distinct
      metric.scaleData.section6Cover.coarse_line_class
      metric.rho_pos rho.2.2
  have fiberEq :
      ∀ parent : Fin coarse.card,
        ((Finset.univ : Finset (Fin fine.card)).filter fun sourceIndex =>
            parentMap sourceIndex = parent) =
          wz2PaperFullFiberIndices fine coarse parent := by
    intro parent
    ext sourceIndex
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      mem_wz2PaperFullFiberIndices_iff]
    exact metric.metric_fiber sourceIndex parent
  have fiberSum :
      ∑ parent : Fin coarse.card,
          ((Finset.univ : Finset (Fin fine.card)).filter fun sourceIndex =>
            parentMap sourceIndex = parent).card =
        fine.card := by
    have partition :=
      Finset.sum_card_fiberwise_eq_card_filter
        (Finset.univ : Finset (Fin fine.card))
        (Finset.univ : Finset (Fin coarse.card))
        parentMap
    simpa only [Finset.mem_univ, Finset.filter_true,
      Finset.card_univ, Fintype.card_fin] using partition
  calc
    fine.card =
        ∑ parent : Fin coarse.card,
          ((Finset.univ : Finset (Fin fine.card)).filter fun sourceIndex =>
            parentMap sourceIndex = parent).card := fiberSum.symm
    _ =
        ∑ parent : Fin coarse.card,
          (wz2PaperFullFiberIndices fine coarse parent).card := by
      apply Finset.sum_congr rfl
      intro parent _
      rw [fiberEq parent]
    _ ≤
        ∑ _parent : Fin coarse.card,
          (2 * Nat.ceil (8 * rho.1 / delta) + 1) ^ 5 := by
      apply Finset.sum_le_sum
      intro parent _
      exact
        MetricParentsAtPrescribedScaleData.fullFiber_card_le_five
          metric parent
    _ =
        coarse.card *
          (2 * Nat.ceil (8 * rho.1 / delta) + 1) ^ 5 := by
      simp
    _ ≤
        (2 * Nat.ceil (80 / rho.1) + 1) ^ 5 *
          (2 * Nat.ceil (8 * rho.1 / delta) + 1) ^ 5 := by
      gcongr

theorem MetricParentsAtPrescribedScaleData.delta_pos
    {delta : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    {fineParentDistanceConstant : ℝ}
    {parentConstant fiberConstant : ENNReal}
    (metric :
      Prop62PaperAudit.V4.MetricParentsAtPrescribedScaleData
        sourceShading rho fineParentDistanceConstant
        parentConstant fiberConstant) :
    0 < delta := by
  let sourceIndex : Fin metric.refinement.selected.family.card :=
    ⟨0, metric.refined_nonempty⟩
  let parent := metric.scaleData.cover.parent sourceIndex
  let fiberData :=
    Classical.choice (metric.scaleData.rescaledFiber parent)
  exact fiberData.rescalingInput.delta_pos

theorem pureWZ2Prop62_five_by_five_le_standard
    {delta rho : ℝ}
    (deltaPos : 0 < delta)
    (deltaLeRho : delta ≤ rho)
    (rhoLeOne : rho ≤ 1)
    (deltaLeOneHundred : delta ≤ 1 / 100) :
    (2 * Nat.ceil (80 / rho) + 1) ^ 5 *
        (2 * Nat.ceil (8 * rho / delta) + 1) ^ 5 ≤
      (2 * Nat.ceil (320 / delta) + 1) ^ 6 := by
  have rhoPos : 0 < rho := deltaPos.trans_le deltaLeRho
  have coarseCeilLt :
      (Nat.ceil (80 / rho) : ℝ) < 80 / rho + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have fiberCeilLt :
      (Nat.ceil (8 * rho / delta) : ℝ) <
        8 * rho / delta + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have coarseBase :
      ((2 * Nat.ceil (80 / rho) + 1 : ℕ) : ℝ) ≤
        163 / rho := by
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    have threeLe : (3 : ℝ) ≤ 3 / rho := by
      calc
        (3 : ℝ) = 3 / 1 := by norm_num
        _ ≤ 3 / rho := by gcongr
    calc
      2 * (Nat.ceil (80 / rho) : ℝ) + 1 ≤
          2 * (80 / rho + 1) + 1 := by
        gcongr
      _ = 160 / rho + 3 := by ring
      _ ≤ 160 / rho + 3 / rho := by gcongr
      _ = 163 / rho := by
        field_simp [rhoPos.ne']
        norm_num
  have fiberBase :
      ((2 * Nat.ceil (8 * rho / delta) + 1 : ℕ) : ℝ) ≤
        19 * rho / delta := by
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    have threeLe : (3 : ℝ) ≤ 3 * rho / delta := by
      calc
        (3 : ℝ) = 3 * delta / delta := by
          field_simp [deltaPos.ne']
        _ ≤ 3 * rho / delta := by gcongr
    calc
      2 * (Nat.ceil (8 * rho / delta) : ℝ) + 1 ≤
          2 * (8 * rho / delta + 1) + 1 := by
        gcongr
      _ = 16 * rho / delta + 3 := by ring
      _ ≤ 16 * rho / delta + 3 * rho / delta := by gcongr
      _ = 19 * rho / delta := by ring
  have productBase :
      (((2 * Nat.ceil (80 / rho) + 1) *
          (2 * Nat.ceil (8 * rho / delta) + 1) : ℕ) : ℝ) ≤
        3097 / delta := by
    norm_num only [Nat.cast_mul]
    calc
      ((2 * Nat.ceil (80 / rho) + 1 : ℕ) : ℝ) *
            ((2 * Nat.ceil (8 * rho / delta) + 1 : ℕ) : ℝ) ≤
          (163 / rho) * (19 * rho / delta) := by
        gcongr
      _ = 3097 / delta := by
        field_simp [rhoPos.ne', deltaPos.ne']
        norm_num
  have oldBaseLower :
      640 / delta ≤
        ((2 * Nat.ceil (320 / delta) + 1 : ℕ) : ℝ) := by
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    have ceilLower :
        320 / delta ≤ (Nat.ceil (320 / delta) : ℝ) :=
      Nat.le_ceil _
    calc
      640 / delta = 2 * (320 / delta) := by ring
      _ ≤ 2 * (Nat.ceil (320 / delta) : ℝ) := by gcongr
      _ ≤ 2 * (Nat.ceil (320 / delta) : ℝ) + 1 := by norm_num
  have absorb :
      (3097 / delta) ^ 5 ≤ (640 / delta) ^ 6 := by
    have constantBound :
        (3097 : ℝ) ^ 5 / 100 ≤ (640 : ℝ) ^ 6 := by
      norm_num
    have scaled :
        (3097 : ℝ) ^ 5 * delta ≤ (640 : ℝ) ^ 6 := by
      calc
        (3097 : ℝ) ^ 5 * delta ≤
            (3097 : ℝ) ^ 5 * (1 / 100) := by gcongr
        _ = (3097 : ℝ) ^ 5 / 100 := by ring
        _ ≤ (640 : ℝ) ^ 6 := constantBound
    calc
      (3097 / delta) ^ 5 =
          (3097 : ℝ) ^ 5 / delta ^ 5 := by rw [div_pow]
      _ ≤ (640 : ℝ) ^ 6 / delta ^ 6 := by
        apply
          (div_le_div_iff₀
            (pow_pos deltaPos 5) (pow_pos deltaPos 6)).2
        rw [show delta ^ 6 = delta ^ 5 * delta by ring]
        nlinarith [pow_pos deltaPos 5]
      _ = (640 / delta) ^ 6 := by rw [div_pow]
  have realBound :
      ((((2 * Nat.ceil (80 / rho) + 1) ^ 5 *
          (2 * Nat.ceil (8 * rho / delta) + 1) ^ 5 : ℕ) : ℝ)) ≤
        (((2 * Nat.ceil (320 / delta) + 1) ^ 6 : ℕ) : ℝ) := by
    calc
      ((((2 * Nat.ceil (80 / rho) + 1) ^ 5 *
          (2 * Nat.ceil (8 * rho / delta) + 1) ^ 5 : ℕ) : ℝ)) =
          ((((2 * Nat.ceil (80 / rho) + 1) *
            (2 * Nat.ceil (8 * rho / delta) + 1) : ℕ) : ℝ)) ^ 5 := by
        norm_num
        ring
      _ ≤ (3097 / delta) ^ 5 := by gcongr
      _ ≤ (640 / delta) ^ 6 := absorb
      _ ≤
          (((2 * Nat.ceil (320 / delta) + 1 : ℕ) : ℝ)) ^ 6 := by
        gcongr
      _ =
          (((2 * Nat.ceil (320 / delta) + 1) ^ 6 : ℕ) : ℝ) := by
        norm_num
  exact_mod_cast realBound

theorem MetricParentsAtPrescribedScaleData.fine_card_le_standard
    {delta : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    {fineParentDistanceConstant : ℝ}
    {parentConstant fiberConstant : ENNReal}
    (metric :
      Prop62PaperAudit.V4.MetricParentsAtPrescribedScaleData
        sourceShading rho fineParentDistanceConstant
        parentConstant fiberConstant)
    (deltaLeOneHundred : delta ≤ 1 / 100) :
    metric.refinement.selected.family.card ≤
      (2 * Nat.ceil (320 / delta) + 1) ^ 6 := by
  exact
    (MetricParentsAtPrescribedScaleData.fine_card_le_five_by_five
      metric).trans <|
      pureWZ2Prop62_five_by_five_le_standard
        (MetricParentsAtPrescribedScaleData.delta_pos metric)
        rho.2.1 rho.2.2 deltaLeOneHundred

theorem MetricParentsAtPrescribedScaleData.fineLog_le_prebalanceLog
    {delta : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    {fineParentDistanceConstant : ℝ}
    {parentConstant fiberConstant : ENNReal}
    (metric :
      Prop62PaperAudit.V4.MetricParentsAtPrescribedScaleData
        sourceShading rho fineParentDistanceConstant
        parentConstant fiberConstant)
    (deltaLeOneHundred : delta ≤ 1 / 100) :
    (Nat.log 2
          (2 * metric.refinement.selected.family.card) + 1 : ℝ) ≤
      pureWZ2Prop62OrdinaryCardLogConstant *
        (1 + Real.log delta⁻¹) := by
  exact
    pureWZ2Prop62_ordinary_card_log_bound
      (MetricParentsAtPrescribedScaleData.delta_pos metric)
      (deltaLeOneHundred.trans (by norm_num))
      metric.refined_nonempty
      (MetricParentsAtPrescribedScaleData.fine_card_le_standard
        metric deltaLeOneHundred)

theorem MetricParentsAtPrescribedScaleData.coarse_card_le_twoLayer
    {delta : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    {fineParentDistanceConstant : ℝ}
    {parentConstant fiberConstant : ENNReal}
    (metric :
      Prop62PaperAudit.V4.MetricParentsAtPrescribedScaleData
        sourceShading rho fineParentDistanceConstant
        parentConstant fiberConstant) :
    metric.scaleData.coarse.card ≤
      pureWZ2Prop62TwoLayerGridBase delta ^ 5 := by
  have raw :
      metric.scaleData.coarse.card ≤
        (2 * Nat.ceil (80 / rho.1) + 1) ^ 5 :=
    paper_essentially_distinct_card_bound_nat
      metric.scaleData.section6Cover.coarse_essentially_distinct
      metric.scaleData.section6Cover.coarse_line_class
      metric.rho_pos rho.2.2
  have deltaPos : 0 < delta :=
    MetricParentsAtPrescribedScaleData.delta_pos metric
  have inverseLe : 1 / rho.1 ≤ 1 / delta :=
    one_div_le_one_div_of_le
      deltaPos
      rho.2.1
  have argumentLe : 80 / rho.1 ≤ 192 / delta := by
    calc
      80 / rho.1 = 80 * (1 / rho.1) := by ring
      _ ≤ 80 * (1 / delta) := by gcongr
      _ ≤ 192 * (1 / delta) := by
        gcongr
        norm_num
      _ = 192 / delta := by ring
  exact raw.trans <| by
    unfold pureWZ2Prop62TwoLayerGridBase
    gcongr

theorem MetricParentsAtPrescribedScaleData.fine_card_le_twoLayer
    {delta : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    {fineParentDistanceConstant : ℝ}
    {parentConstant fiberConstant : ENNReal}
    (metric :
      Prop62PaperAudit.V4.MetricParentsAtPrescribedScaleData
        sourceShading rho fineParentDistanceConstant
        parentConstant fiberConstant) :
    metric.refinement.selected.family.card ≤
      pureWZ2Prop62TwoLayerGridBase delta ^ 11 := by
  have deltaPos : 0 < delta :=
    MetricParentsAtPrescribedScaleData.delta_pos metric
  calc
    metric.refinement.selected.family.card ≤
        metric.scaleData.coarse.card *
          pureWZ2Prop62RescaledFiberPackingBound delta rho.1 :=
      MetricParentsAtPrescribedScaleData.fine_card_le_coarse_mul_fiberPacking
        metric
    _ ≤
        pureWZ2Prop62TwoLayerGridBase delta ^ 5 *
          pureWZ2Prop62TwoLayerGridBase delta ^ 6 := by
      gcongr
      · exact
          MetricParentsAtPrescribedScaleData.coarse_card_le_twoLayer
            metric
      · exact
          pureWZ2Prop62_rescaledFiberPackingBound_le_twoLayer
            deltaPos metric.rho_pos rho.2.2
    _ = pureWZ2Prop62TwoLayerGridBase delta ^ 11 := by ring

theorem pureWZ2Prop62_twoLayer_card_log_bound
    {delta : ℝ}
    (deltaPos : 0 < delta)
    (deltaLeOne : delta ≤ 1)
    {cardinality : ℕ}
    (cardinalityPos : 0 < cardinality)
    (cardinalityBound :
      cardinality ≤
        pureWZ2Prop62TwoLayerGridBase delta ^ 11) :
    (Nat.log 2 (2 * cardinality) + 1 : ℝ) ≤
      pureWZ2Prop62TwoLayerCardLogConstant *
        (1 + Real.log delta⁻¹) := by
  have logTwoPos : 0 < Real.log 2 :=
    Real.log_pos (by norm_num)
  have logInvNonnegative : 0 ≤ Real.log delta⁻¹ := by
    apply Real.log_nonneg
    exact (one_le_inv₀ deltaPos).mpr deltaLeOne
  have constantFirst :
      Real.log (2 * (387 : ℝ) ^ 11) / Real.log 2 + 1 ≤
        pureWZ2Prop62TwoLayerCardLogConstant :=
    le_max_left _ _
  have constantSecond :
      11 / Real.log 2 ≤
        pureWZ2Prop62TwoLayerCardLogConstant :=
    le_max_right _ _
  have doubleCardinalityPos : 0 < 2 * cardinality := by
    positivity
  have ceilPositive : 0 < Nat.ceil (192 / delta) := by
    apply Nat.ceil_pos.mpr
    positivity
  have ceilLt :
      (Nat.ceil (192 / delta) : ℝ) <
        192 / delta + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have baseLe :
      (pureWZ2Prop62TwoLayerGridBase delta : ℝ) ≤
        387 / delta := by
    have threeLe : (3 : ℝ) ≤ 3 / delta := by
      calc
        (3 : ℝ) = 3 / 1 := by norm_num
        _ ≤ 3 / delta := by gcongr
    have middle :
        ((2 * Nat.ceil (192 / delta) + 1 : ℕ) : ℝ) <
          384 / delta + 3 := by
      norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      calc
        2 * (Nat.ceil (192 / delta) : ℝ) + 1 <
            2 * (192 / delta + 1) + 1 := by
          gcongr
        _ = 384 / delta + 3 := by ring
    unfold pureWZ2Prop62TwoLayerGridBase
    calc
      ((2 * Nat.ceil (192 / delta) + 1 : ℕ) : ℝ) ≤
          384 / delta + 3 := middle.le
      _ ≤ 384 / delta + 3 / delta := by gcongr
      _ = 387 / delta := by
        field_simp [deltaPos.ne']
        ring
  have cardinalityReal :
      (cardinality : ℝ) ≤
        (pureWZ2Prop62TwoLayerGridBase delta : ℝ) ^ 11 := by
    exact_mod_cast cardinalityBound
  have basePowerLe :
      (pureWZ2Prop62TwoLayerGridBase delta : ℝ) ^ 11 ≤
        (387 / delta) ^ 11 := by
    gcongr
  have quotientPower :
      (387 / delta) ^ 11 =
        (387 : ℝ) ^ 11 * delta ^ (-11 : ℝ) := by
    have inversePower :
        delta ^ (-11 : ℝ) = (delta ^ 11)⁻¹ := by
      rw [Real.rpow_neg deltaPos.le]
      norm_cast
    rw [inversePower]
    field_simp [deltaPos.ne']
  have polynomialCardinality :
      ((2 * cardinality : ℕ) : ℝ) ≤
        (2 * (387 : ℝ) ^ 11) *
          delta ^ (-11 : ℝ) := by
    calc
      ((2 * cardinality : ℕ) : ℝ) =
          2 * (cardinality : ℝ) := by norm_num
      _ ≤
          2 *
            (pureWZ2Prop62TwoLayerGridBase delta : ℝ) ^ 11 := by
        gcongr
      _ ≤ 2 * (387 / delta) ^ 11 := by
        gcongr
      _ =
          (2 * (387 : ℝ) ^ 11) *
            delta ^ (-11 : ℝ) := by
        rw [quotientPower]
        ring
  have natLog :
      (Nat.log 2 (2 * cardinality) : ℝ) ≤
        Real.log ((2 * cardinality : ℕ) : ℝ) /
          Real.log 2 := by
    have powerLe :
        (2 : ℕ) ^ Nat.log 2 (2 * cardinality) ≤
          2 * cardinality :=
      Nat.pow_log_le_self 2 doubleCardinalityPos.ne'
    have powerLeReal :
        (2 : ℝ) ^ Nat.log 2 (2 * cardinality) ≤
          ((2 * cardinality : ℕ) : ℝ) := by
      exact_mod_cast powerLe
    have logarithm :=
      Real.log_le_log (by positivity) powerLeReal
    rw [Real.log_pow] at logarithm
    exact (le_div_iff₀ logTwoPos).mpr (by simpa using logarithm)
  have cardLog :
      Real.log ((2 * cardinality : ℕ) : ℝ) ≤
        Real.log
          ((2 * (387 : ℝ) ^ 11) *
            delta ^ (-11 : ℝ)) :=
    Real.log_le_log (by exact_mod_cast doubleCardinalityPos)
      polynomialCardinality
  have productLog :
      Real.log
          ((2 * (387 : ℝ) ^ 11) *
            delta ^ (-11 : ℝ)) =
        Real.log (2 * (387 : ℝ) ^ 11) +
          11 * Real.log delta⁻¹ := by
    rw [Real.log_mul (by positivity) (by positivity),
      Real.log_rpow deltaPos (-11 : ℝ), Real.log_inv]
    ring
  calc
    (Nat.log 2 (2 * cardinality) + 1 : ℝ) ≤
        Real.log ((2 * cardinality : ℕ) : ℝ) /
            Real.log 2 + 1 := by
      linarith
    _ ≤
        Real.log
            ((2 * (387 : ℝ) ^ 11) *
              delta ^ (-11 : ℝ)) /
            Real.log 2 + 1 := by
      gcongr
    _ =
        (Real.log (2 * (387 : ℝ) ^ 11) /
            Real.log 2 + 1) +
          (11 / Real.log 2) * Real.log delta⁻¹ := by
      rw [productLog]
      field_simp [logTwoPos.ne']
      ring
    _ ≤
        pureWZ2Prop62TwoLayerCardLogConstant +
          pureWZ2Prop62TwoLayerCardLogConstant *
            Real.log delta⁻¹ := by
      gcongr
    _ =
        pureWZ2Prop62TwoLayerCardLogConstant *
          (1 + Real.log delta⁻¹) := by
      ring

-/

/-- Frozen V4 wrapper around the generic two-layer cardinality theorem. -/
theorem MetricParentsAtPrescribedScaleData.fineLog_le_twoLayer
    {delta : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    {fineParentDistanceConstant : ℝ}
    {parentConstant fiberConstant : ENNReal}
    (metric :
      Prop62PaperAudit.V4.MetricParentsAtPrescribedScaleData
        sourceShading rho fineParentDistanceConstant
        parentConstant fiberConstant) :
    (Nat.log 2
          (2 * metric.refinement.selected.family.card) + 1 : ℝ) ≤
      pureWZ2Prop62TwoLayerCardLogConstant *
        (1 + Real.log delta⁻¹) := by
  let fiberData :
      ∀ parent : Fin metric.scaleData.coarse.card,
        Prop62PaperAudit.V4.RescaledMetricFiberCWAData
          metric.scaleData.section6Cover parent metric.rho_pos
            fiberConstant :=
    fun parent => Classical.choice (metric.scaleData.rescaledFiber parent)
  let sourceConstant :
      Fin metric.scaleData.coarse.card → ENNReal :=
    fun parent => (fiberData parent).sourceConstant
  have rescaledFiber :
      ∀ parent,
        Nonempty
          (PureWZ2Prop62MetricFiberRescalingInput
            metric.scaleData.section6Cover parent
              (sourceConstant parent)) :=
    fun parent => ⟨(fiberData parent).rescalingInput⟩
  have deltaPos : 0 < delta := by
    let sourceIndex : Fin metric.refinement.selected.family.card :=
      ⟨0, metric.refined_nonempty⟩
    let parent := metric.scaleData.cover.parent sourceIndex
    exact (fiberData parent).rescalingInput.delta_pos
  exact
    pureWZ2Prop62_twoLayer_fineLog
      metric.scaleData.section6Cover deltaPos rho.2.1 rho.2.2
      metric.refined_nonempty
      sourceConstant rescaledFiber

end Kakeya.Assouad

end
