import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63TerminalParentPairRefinement
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63InitialLocalGrainReentry
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63RobustTransversality

/-!
# Two-rich-call close-count transport for Proposition 6.3

The robust Proposition 6.2 call and the target Proposition 6.2 call generally
live on different dependent tube subfamilies.  This module transports the
outer close-direction estimate through the actual current-shading re-entry
and the target selection.  The only remaining input is the scalar comparison
between the outer fiber multiplicity and the inner terminal total degree.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set Finset

attribute [local instance] Classical.propDecidable

/-- The terminal fiber multiplicity is no larger than the number of tubes in
the terminal fine family.  This elementary projection is used before the
quantitative cross-call cardinality cancellation. -/
lemma Proposition63TerminalMultiplicityCertificate.muFine_le_fine_card
    {delta rho sigma terminalLoss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (terminal : Proposition63TerminalMultiplicityCertificate
      (sigma := sigma) (terminalLoss := terminalLoss)
      cover fineShading coarseShading) :
    (terminal.muFine : ENNReal) ≤ fine.enncard := by
  let edge := Classical.choose terminal.packetCells_nonempty
  have edgeMem : edge ∈ terminal.packetCells :=
    Classical.choose_spec terminal.packetCells_nonempty
  have exactMultiplicity := terminal.exact_fine_multiplicity edge edgeMem
  let fiberCell : Finset (Fin fine.card) :=
    (wz2PaperFullFiberIndices fine coarse edge.1).filter fun sourceIndex =>
      wz1PaperGridCube delta edge.2 ⊆ fineShading.carrier sourceIndex
  have fiberCellLe : fiberCell.card ≤ fine.card := by
    exact (Finset.card_le_card <| Finset.filter_subset _ _).trans
      (by
        simpa using Finset.card_le_univ
          (s := wz2PaperFullFiberIndices fine coarse edge.1))
  change (terminal.muFine : ENNReal) ≤ (fine.card : ENNReal)
  exact_mod_cast exactMultiplicity.symm ▸ fiberCellLe

/-- Summing the terminal pointwise fiber cap over the genuine parent
partition controls `#coarse * muFine` by the standard fiber power times the
whole terminal fine family.  This is the sharp outer bound used in the
two-scale close-count comparison. -/
lemma Proposition63TerminalMultiplicityCertificate.coarse_card_mul_muFine_le
    {delta rho sigma terminalLoss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (terminal : Proposition63TerminalMultiplicityCertificate
      (sigma := sigma) (terminalLoss := terminalLoss)
      cover fineShading coarseShading) :
    coarse.enncard * (terminal.muFine : ENNReal) ≤
      Kakeya.realRpowENN (delta / rho)
          (2 - sigma - terminalLoss) * fine.enncard := by
  have summed :
      ∑ parent : Fin coarse.card, (terminal.muFine : ENNReal) ≤
        ∑ parent : Fin coarse.card,
          Kakeya.realRpowENN (delta / rho)
              (2 - sigma - terminalLoss) *
            ((wz2PaperFullFiberIndices fine coarse parent).card : ENNReal) :=
    Finset.sum_le_sum fun parent _ => terminal.fine_multiplicity_upper parent
  have fiberSum :
      (∑ parent : Fin coarse.card,
          ((wz2PaperFullFiberIndices fine coarse parent).card : ENNReal)) =
        fine.enncard := by
    let parentMap := cover.toWZ1PaperTubeCover.parent
    have fiberEq : ∀ parent : Fin coarse.card,
        wz2PaperFullFiberIndices fine coarse parent =
          (Finset.univ : Finset (Fin fine.card)).filter fun source =>
            parentMap source = parent := by
      intro parent
      ext source
      simp only [mem_wz2PaperFullFiberIndices_iff, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · intro covered
        exact (cover.toWZ1PaperTubeCover.parent_unique
          source parent covered).symm
      · intro parentEq
        rw [← parentEq]
        exact cover.toWZ1PaperTubeCover.parent_covers source
    have fiberSumNat :
        ∑ parent : Fin coarse.card,
            (wz2PaperFullFiberIndices fine coarse parent).card = fine.card := by
      calc
        (∑ parent : Fin coarse.card,
            (wz2PaperFullFiberIndices fine coarse parent).card) =
            ∑ parent : Fin coarse.card,
              ((Finset.univ : Finset (Fin fine.card)).filter fun source =>
                parentMap source = parent).card := by
          apply Finset.sum_congr rfl
          intro parent _
          rw [fiberEq parent]
        _ = fine.card := by
          simpa only [Finset.mem_univ, Finset.filter_true, Finset.card_univ,
            Fintype.card_fin] using
              Finset.sum_card_fiberwise_eq_card_filter
                (Finset.univ : Finset (Fin fine.card))
                (Finset.univ : Finset (Fin coarse.card)) parentMap
    rw [← Nat.cast_sum, fiberSumNat]
    rfl
  calc
    coarse.enncard * (terminal.muFine : ENNReal) =
        ∑ _parent : Fin coarse.card, (terminal.muFine : ENNReal) := by
      simp [Kakeya.Streamlined.TubeFamily.enncard, Finset.sum_const,
        nsmul_eq_mul, mul_comm]
    _ ≤ ∑ parent : Fin coarse.card,
          Kakeya.realRpowENN (delta / rho)
              (2 - sigma - terminalLoss) *
            ((wz2PaperFullFiberIndices fine coarse parent).card : ENNReal) :=
      summed
    _ = Kakeya.realRpowENN (delta / rho)
          (2 - sigma - terminalLoss) *
        (∑ parent : Fin coarse.card,
          ((wz2PaperFullFiberIndices fine coarse parent).card : ENNReal)) := by
      rw [Finset.mul_sum]
    _ = Kakeya.realRpowENN (delta / rho)
          (2 - sigma - terminalLoss) * fine.enncard := by rw [fiberSum]

/-- Cancel one weighted-cardinality retention inequality against a target
degree lower bound.  This is the scalar skeleton of the cross-call degree
comparison and avoids division by the normalization weight. -/
lemma proposition63_cross_call_cardinality_cancel
    {sourceCap sourceCard targetCard targetDegree normalizationWeight
      selectionCost densityPower closeBound : ENNReal}
    (hnormalizationWeightPos : 0 < normalizationWeight)
    (hnormalizationWeightTop : normalizationWeight ≠ ⊤)
    (hsourceCap : sourceCap ≤ sourceCard)
    (hretention : normalizationWeight * sourceCard ≤
      selectionCost * targetCard)
    (htargetDegree : densityPower * targetCard ≤ targetDegree)
    (hscalar : (2 * closeBound) * selectionCost ≤
      normalizationWeight * densityPower) :
    2 * closeBound * sourceCap ≤ targetDegree := by
  apply (ENNReal.mul_le_mul_iff_left
    hnormalizationWeightPos.ne' hnormalizationWeightTop).mp
  calc
    (2 * closeBound * sourceCap) * normalizationWeight ≤
        (2 * closeBound * sourceCard) * normalizationWeight := by gcongr
    _ = (2 * closeBound) *
          (normalizationWeight * sourceCard) := by ring
    _ ≤ (2 * closeBound) * (selectionCost * targetCard) := by gcongr
    _ = ((2 * closeBound) * selectionCost) * targetCard := by ring
    _ ≤ (normalizationWeight * densityPower) * targetCard := by gcongr
    _ = (densityPower * targetCard) * normalizationWeight := by ring
    _ ≤ targetDegree * normalizationWeight := by gcongr

/-- Sharp cross-call cancellation retaining the outer parent cardinality.
The outer terminal fiber cap is averaged over its full parent partition; the
target re-entry retains source cardinality; and the target terminal converts
that cardinality to total point degree. -/
lemma proposition63_cross_call_fiber_degree_cancel
    {sourceCap outerSelectedCard sourceCard targetCard targetDegree coarseCard
      outerFiberPower normalizationWeight selectionCost densityPower
      closeBound : ENNReal}
    (hcoarseCardPos : 0 < coarseCard)
    (hcoarseCardTop : coarseCard ≠ ⊤)
    (hnormalizationWeightPos : 0 < normalizationWeight)
    (hnormalizationWeightTop : normalizationWeight ≠ ⊤)
    (hsourceCap : coarseCard * sourceCap ≤
      outerFiberPower * outerSelectedCard)
    (hselectedCard : outerSelectedCard ≤ sourceCard)
    (hretention : normalizationWeight * sourceCard ≤
      selectionCost * targetCard)
    (htargetDegree : densityPower * targetCard ≤ targetDegree)
    (hscalar : (2 * closeBound) * outerFiberPower * selectionCost ≤
      coarseCard * normalizationWeight * densityPower) :
    2 * closeBound * sourceCap ≤ targetDegree := by
  let common : ENNReal := coarseCard * normalizationWeight
  have commonPos : 0 < common := by
    dsimp only [common]
    positivity
  have commonTop : common ≠ ⊤ := by
    dsimp only [common]
    exact ENNReal.mul_ne_top
      hcoarseCardTop hnormalizationWeightTop
  apply (ENNReal.mul_le_mul_iff_left commonPos.ne' commonTop).mp
  calc
    (2 * closeBound * sourceCap) * common =
        (2 * closeBound) * (coarseCard * sourceCap) *
          normalizationWeight := by
      dsimp only [common]
      ring
    _ ≤ (2 * closeBound) *
          (outerFiberPower * outerSelectedCard) *
          normalizationWeight := by gcongr
    _ ≤ (2 * closeBound) * (outerFiberPower * sourceCard) *
          normalizationWeight := by gcongr
    _ = (2 * closeBound) * outerFiberPower *
          (normalizationWeight * sourceCard) := by ring
    _ ≤ (2 * closeBound) * outerFiberPower *
          (selectionCost * targetCard) := by gcongr
    _ = ((2 * closeBound) * outerFiberPower * selectionCost) *
          targetCard := by ring
    _ ≤ (coarseCard * normalizationWeight * densityPower) *
          targetCard := by gcongr
    _ = common * (densityPower * targetCard) := by
      dsimp only [common]
      ring
    _ ≤ common * targetDegree := by gcongr
    _ = targetDegree * common := by ring

/-- The exact scalar input sufficient to dominate the robust terminal fiber
multiplicity by the target terminal total point degree.  All runtime factors
are fields of the two rich outputs and the genuine current re-entry. -/
theorem proposition63_two_rich_cross_degree_of_scalar
    {delta sigma outerLoss outerSourceLoss outerNormalizationLoss
      targetReentryLoss targetLoss : ℝ}
    {densityPower : ENNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {outerNormalizationExponent : ℕ}
    {outerReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) sourceShading outerNormalizationExponent
      outerSourceLoss outerNormalizationLoss}
    {robustScale : WZ2PaperRequestedScale delta}
    (outer : Proposition63RichTerminalStickyData
      (outputLoss := outerLoss) sourceShading outerReentry robustScale)
    {current : WZ1PaperTubeShading
      outerReentry.toNormalizationData.croppedFamily}
    (targetReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := targetReentryLoss) outerReentry.toNormalizationData
      current)
    (htargetReentryLoss : 0 < targetReentryLoss)
    {targetScale : WZ2PaperRequestedScale delta}
    (target : Proposition63RichTerminalStickyData
      (outputLoss := targetLoss) targetReentry.normalization.croppedRefined
      (targetReentry.normalization.toPropStickyReentryData
        htargetReentryLoss
        targetReentry.reentry_normalization_loss_pos) targetScale)
    (hdeltaSmall : delta ≤ 1 / 12)
    (hdensityScalar :
      densityPower *
          ((target.terminal.regularity : ENNReal) *
            Kakeya.realRpowENN delta
              (sigma - targetReentry.reentryNormalizationLoss)) ≤
        wz2PaperPureRefinementFraction delta 61 *
          Kakeya.realRpowENN delta
            (targetReentry.reentryNormalizationLoss + 2))
    (hscalar :
      (2 * stickyCoarseCloseCount) *
          (targetReentry.regularized.regularizationLoss *
            targetReentry.weightUpper) ≤
        targetReentry.normalizationWeight * densityPower) :
    2 * stickyCoarseCloseCount * (outer.terminal.muFine : ENNReal) ≤
      ((target.terminal.fineDegreeFloor * target.terminal.muFine : ℕ) :
        ENNReal) := by
  apply proposition63_cross_call_cardinality_cancel
      (normalizationWeight := targetReentry.normalizationWeight)
      (selectionCost :=
        targetReentry.regularized.regularizationLoss *
          targetReentry.weightUpper)
      (sourceCard := sourceFamily.enncard)
      (targetCard := targetReentry.normalization.croppedFamily.enncard)
      (densityPower := densityPower)
      (closeBound := stickyCoarseCloseCount)
  · exact bot_lt_iff_ne_bot.mpr targetReentry.normalization_weight_ne_zero
  · exact targetReentry.normalization_weight_ne_top
  · exact outer.terminal.muFine_le_fine_card.trans
      (tubeSubfamily_enncard_le outer.data.selected)
  · change targetReentry.normalizationWeight * sourceFamily.enncard ≤
      (targetReentry.regularized.regularizationLoss *
        targetReentry.weightUpper) *
          targetReentry.regularized.selected.family.enncard
    exact targetReentry.regularized.cardinality_retention
  · exact target.fineMultiplicity_density_of_source_cardinality
      densityPower hdeltaSmall hdensityScalar
  · exact hscalar

/-- Sharp specialization retaining the outer terminal coarse cardinality.
This is the quantitative WZ2 analogue of WZ1's `hAbsorbFinal`: the outer
fiber power, the current re-entry selection cost, and the target density
power are compared before any runtime cardinality is cancelled. -/
theorem proposition63_two_rich_cross_degree_of_sharp_scalar
    {delta sigma outerLoss outerSourceLoss outerNormalizationLoss
      targetReentryLoss targetLoss : ℝ}
    {densityPower : ENNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {outerNormalizationExponent : ℕ}
    {outerReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) sourceShading outerNormalizationExponent
      outerSourceLoss outerNormalizationLoss}
    {robustScale : WZ2PaperRequestedScale delta}
    (outer : Proposition63RichTerminalStickyData
      (outputLoss := outerLoss) sourceShading outerReentry robustScale)
    {current : WZ1PaperTubeShading
      outerReentry.toNormalizationData.croppedFamily}
    (targetReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := targetReentryLoss) outerReentry.toNormalizationData
      current)
    (htargetReentryLoss : 0 < targetReentryLoss)
    {targetScale : WZ2PaperRequestedScale delta}
    (target : Proposition63RichTerminalStickyData
      (outputLoss := targetLoss) targetReentry.normalization.croppedRefined
      (targetReentry.normalization.toPropStickyReentryData
        htargetReentryLoss
        targetReentry.reentry_normalization_loss_pos) targetScale)
    (hdeltaSmall : delta ≤ 1 / 12)
    (hdensityScalar :
      densityPower *
          ((target.terminal.regularity : ENNReal) *
            Kakeya.realRpowENN delta
              (sigma - targetReentry.reentryNormalizationLoss)) ≤
        wz2PaperPureRefinementFraction delta 61 *
          Kakeya.realRpowENN delta
            (targetReentry.reentryNormalizationLoss + 2))
    (hscalar :
      (2 * stickyCoarseCloseCount) *
          Kakeya.realRpowENN (delta / robustScale.1)
            (2 - sigma - outer.terminalLoss) *
          (targetReentry.regularized.regularizationLoss *
            targetReentry.weightUpper) ≤
        outer.data.coarse.enncard *
          targetReentry.normalizationWeight * densityPower) :
    2 * stickyCoarseCloseCount * (outer.terminal.muFine : ENNReal) ≤
      ((target.terminal.fineDegreeFloor * target.terminal.muFine : ℕ) :
        ENNReal) := by
  apply proposition63_cross_call_fiber_degree_cancel
      (outerSelectedCard := outer.data.selected.family.enncard)
      (sourceCard := sourceFamily.enncard)
      (targetCard := targetReentry.normalization.croppedFamily.enncard)
      (coarseCard := outer.data.coarse.enncard)
      (outerFiberPower := Kakeya.realRpowENN
        (delta / robustScale.1) (2 - sigma - outer.terminalLoss))
      (normalizationWeight := targetReentry.normalizationWeight)
      (selectionCost := targetReentry.regularized.regularizationLoss *
        targetReentry.weightUpper)
      (densityPower := densityPower)
      (closeBound := stickyCoarseCloseCount)
  · change (0 : ENNReal) < (outer.data.coarse.card : ENNReal)
    exact_mod_cast outer.data.coarse_extremal.nonempty
  · exact ENNReal.coe_ne_top
  · exact bot_lt_iff_ne_bot.mpr targetReentry.normalization_weight_ne_zero
  · exact targetReentry.normalization_weight_ne_top
  · exact outer.terminal.coarse_card_mul_muFine_le
  · exact tubeSubfamily_enncard_le outer.data.selected
  · change targetReentry.normalizationWeight * sourceFamily.enncard ≤
      (targetReentry.regularized.regularizationLoss *
        targetReentry.weightUpper) *
          targetReentry.regularized.selected.family.enncard
    exact targetReentry.regularized.cardinality_retention
  · exact target.fineMultiplicity_density_of_source_cardinality
      densityPower hdeltaSmall hdensityScalar
  · exact hscalar

/-- Use the outer coarse CWA cardinality floor to remove the last runtime
family cardinality from the sharp two-call scalar inequality. -/
theorem proposition63_two_rich_cross_degree_of_uniform_scalar
    {delta sigma outerLoss outerSourceLoss outerNormalizationLoss
      targetReentryLoss targetLoss : ℝ}
    {densityPower : ENNReal}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {outerNormalizationExponent : ℕ}
    {outerReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) sourceShading outerNormalizationExponent
      outerSourceLoss outerNormalizationLoss}
    {robustScale : WZ2PaperRequestedScale delta}
    (outer : Proposition63RichTerminalStickyData
      (outputLoss := outerLoss) sourceShading outerReentry robustScale)
    {current : WZ1PaperTubeShading
      outerReentry.toNormalizationData.croppedFamily}
    (targetReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := targetReentryLoss) outerReentry.toNormalizationData
      current)
    (htargetReentryLoss : 0 < targetReentryLoss)
    {targetScale : WZ2PaperRequestedScale delta}
    (target : Proposition63RichTerminalStickyData
      (outputLoss := targetLoss) targetReentry.normalization.croppedRefined
      (targetReentry.normalization.toPropStickyReentryData
        htargetReentryLoss
        targetReentry.reentry_normalization_loss_pos) targetScale)
    (hdeltaSmall : delta ≤ 1 / 12)
    (hrobustSmall : robustScale.1 ≤ 1 / 10000)
    (hdensityScalar :
      densityPower *
          ((target.terminal.regularity : ENNReal) *
            Kakeya.realRpowENN delta
              (sigma - targetReentry.reentryNormalizationLoss)) ≤
        wz2PaperPureRefinementFraction delta 61 *
          Kakeya.realRpowENN delta
            (targetReentry.reentryNormalizationLoss + 2))
    (hscalar :
      ((2 * stickyCoarseCloseCount) *
          Kakeya.realRpowENN (delta / robustScale.1)
            (2 - sigma - outer.terminalLoss) *
          (targetReentry.regularized.regularizationLoss *
            targetReentry.weightUpper)) *
          ((12 : ENNReal) * ENNReal.ofReal Real.pi) *
          Kakeya.realRpowENN robustScale.1 (2 - outerLoss) ≤
        targetReentry.normalizationWeight * densityPower) :
    2 * stickyCoarseCloseCount * (outer.terminal.muFine : ENNReal) ≤
      ((target.terminal.fineDegreeFloor * target.terminal.muFine : ℕ) :
        ENNReal) := by
  have coarseFloor :
      1 ≤ ((12 : ENNReal) * ENNReal.ofReal Real.pi) *
        (Kakeya.realRpowENN robustScale.1 (2 - outerLoss) *
          outer.data.coarse.enncard) :=
    cwa_cardinality_weight_floor outer.data.coarse_extremal
      (hrobustSmall.trans <| by norm_num)
  have sharpScalar :
      (2 * stickyCoarseCloseCount) *
          Kakeya.realRpowENN (delta / robustScale.1)
            (2 - sigma - outer.terminalLoss) *
          (targetReentry.regularized.regularizationLoss *
            targetReentry.weightUpper) ≤
        outer.data.coarse.enncard *
          targetReentry.normalizationWeight * densityPower := by
    let left : ENNReal :=
      (2 * stickyCoarseCloseCount) *
        Kakeya.realRpowENN (delta / robustScale.1)
          (2 - sigma - outer.terminalLoss) *
        (targetReentry.regularized.regularizationLoss *
          targetReentry.weightUpper)
    calc
      left = left * 1 := by simp
      _ ≤ left * (((12 : ENNReal) * ENNReal.ofReal Real.pi) *
          (Kakeya.realRpowENN robustScale.1 (2 - outerLoss) *
            outer.data.coarse.enncard)) := by gcongr
      _ = outer.data.coarse.enncard *
          (left * ((12 : ENNReal) * ENNReal.ofReal Real.pi) *
            Kakeya.realRpowENN robustScale.1 (2 - outerLoss)) := by ring
      _ ≤ outer.data.coarse.enncard *
          (targetReentry.normalizationWeight * densityPower) := by
        gcongr
      _ = outer.data.coarse.enncard *
          targetReentry.normalizationWeight * densityPower := by ring
  exact proposition63_two_rich_cross_degree_of_sharp_scalar outer
    targetReentry htargetReentryLoss target hdeltaSmall hdensityScalar
    sharpScalar

/-- Scaled two-call cross-degree criterion with no auxiliary runtime density
parameter.  The explicit natural factor is carried through the same
cardinality cancellation; robust point-cover pruning uses the factor four
instance while the plane-map route retains its factor two instance. -/
theorem proposition63_two_rich_cross_degree_of_terminal_scalar_scaled
    {delta sigma outerLoss outerSourceLoss outerNormalizationLoss
      targetReentryLoss targetLoss : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {outerNormalizationExponent : ℕ}
    {outerReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) sourceShading outerNormalizationExponent
      outerSourceLoss outerNormalizationLoss}
    {robustScale : WZ2PaperRequestedScale delta}
    (outer : Proposition63RichTerminalStickyData
      (outputLoss := outerLoss) sourceShading outerReentry robustScale)
    {current : WZ1PaperTubeShading
      outerReentry.toNormalizationData.croppedFamily}
    (targetReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := targetReentryLoss) outerReentry.toNormalizationData
      current)
    (htargetReentryLoss : 0 < targetReentryLoss)
    {targetScale : WZ2PaperRequestedScale delta}
    (target : Proposition63RichTerminalStickyData
      (outputLoss := targetLoss) targetReentry.normalization.croppedRefined
      (targetReentry.normalization.toPropStickyReentryData
        htargetReentryLoss
        targetReentry.reentry_normalization_loss_pos) targetScale)
    (hdeltaSmall : delta ≤ 1 / 12)
    (hrobustSmall : robustScale.1 ≤ 1 / 10000)
    (factor : ℕ)
    (hscalar :
      ((((factor : ENNReal) * stickyCoarseCloseCount) *
          Kakeya.realRpowENN (delta / robustScale.1)
            (2 - sigma - outer.terminalLoss) *
          (targetReentry.regularized.regularizationLoss *
            targetReentry.weightUpper)) *
          ((12 : ENNReal) * ENNReal.ofReal Real.pi) *
          Kakeya.realRpowENN robustScale.1 (2 - outerLoss)) *
          ((target.terminal.regularity : ENNReal) *
            Kakeya.realRpowENN delta
              (sigma - targetReentry.reentryNormalizationLoss)) ≤
        targetReentry.normalizationWeight *
          (wz2PaperPureRefinementFraction delta 61 *
            Kakeya.realRpowENN delta
              (targetReentry.reentryNormalizationLoss + 2))) :
    (factor : ENNReal) * stickyCoarseCloseCount *
        (outer.terminal.muFine : ENNReal) ≤
      ((target.terminal.fineDegreeFloor * target.terminal.muFine : ℕ) :
        ENNReal) := by
  let outerFiberPower : ENNReal :=
    Kakeya.realRpowENN (delta / robustScale.1)
      (2 - sigma - outer.terminalLoss)
  let coarseWeight : ENNReal :=
    ((12 : ENNReal) * ENNReal.ofReal Real.pi) *
      Kakeya.realRpowENN robustScale.1 (2 - outerLoss)
  let selectionCost : ENNReal :=
    targetReentry.regularized.regularizationLoss *
      targetReentry.weightUpper
  let targetScaleFactor : ENNReal :=
    (target.terminal.regularity : ENNReal) *
      Kakeya.realRpowENN delta
        (sigma - targetReentry.reentryNormalizationLoss)
  let targetSourcePower : ENNReal :=
    wz2PaperPureRefinementFraction delta 61 *
      Kakeya.realRpowENN delta
        (targetReentry.reentryNormalizationLoss + 2)
  let targetDegree : ENNReal :=
    ((target.terminal.fineDegreeFloor * target.terminal.muFine : ℕ) :
      ENNReal)
  have deltaStrict : delta < 1 :=
    hdeltaSmall.trans_lt (by norm_num)
  have fractionPos : 0 < wz2PaperPureRefinementFraction delta 61 := by
    unfold wz2PaperPureRefinementFraction
    exact ENNReal.pow_pos
      (ENNReal.inv_pos.mpr ENNReal.ofReal_ne_top) 61
  have fractionTop : wz2PaperPureRefinementFraction delta 61 ≠ ⊤ := by
    change (ENNReal.ofReal (Real.log (1 / delta)))⁻¹ ^ 61 ≠ ⊤
    apply ENNReal.pow_ne_top
    apply ENNReal.inv_ne_top.mpr
    exact (ENNReal.ofReal_pos.mpr <| Real.log_pos <|
      one_lt_one_div targetReentry.reentry_extremal.delta_pos
        deltaStrict).ne'
  have targetSourcePowerPos : 0 < targetSourcePower := by
    dsimp only [targetSourcePower]
    apply ENNReal.mul_pos fractionPos.ne'
    exact (ENNReal.ofReal_pos.mpr <| Real.rpow_pos_of_pos
      targetReentry.reentry_extremal.delta_pos _).ne'
  have targetSourcePowerTop : targetSourcePower ≠ ⊤ := by
    dsimp only [targetSourcePower]
    exact ENNReal.mul_ne_top fractionTop ENNReal.ofReal_ne_top
  have normalizationWeightPos : 0 < targetReentry.normalizationWeight :=
    bot_lt_iff_ne_bot.mpr targetReentry.normalization_weight_ne_zero
  have normalizationWeightTop : targetReentry.normalizationWeight ≠ ⊤ :=
    targetReentry.normalization_weight_ne_top
  have coarseCardPos : 0 < outer.data.coarse.enncard := by
    change (0 : ENNReal) < (outer.data.coarse.card : ENNReal)
    exact_mod_cast outer.data.coarse_extremal.nonempty
  have coarseCardTop : outer.data.coarse.enncard ≠ ⊤ := ENNReal.coe_ne_top
  let common := outer.data.coarse.enncard *
    targetReentry.normalizationWeight * targetSourcePower
  have commonPos : 0 < common := by
    dsimp only [common]
    positivity
  have commonTop : common ≠ ⊤ := by
    dsimp only [common]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top coarseCardTop normalizationWeightTop)
      targetSourcePowerTop
  have coarseFloor : 1 ≤ coarseWeight * outer.data.coarse.enncard := by
    dsimp only [coarseWeight]
    simpa only [mul_assoc] using
      cwa_cardinality_weight_floor outer.data.coarse_extremal
        (hrobustSmall.trans <| by norm_num)
  have outerFiber := outer.terminal.coarse_card_mul_muFine_le
  have selectedCard := tubeSubfamily_enncard_le outer.data.selected
  have reentryCardinality :
      targetReentry.normalizationWeight * sourceFamily.enncard ≤
        selectionCost * targetReentry.normalization.croppedFamily.enncard := by
    dsimp only [selectionCost]
    change targetReentry.normalizationWeight * sourceFamily.enncard ≤
      (targetReentry.regularized.regularizationLoss *
        targetReentry.weightUpper) *
          targetReentry.regularized.selected.family.enncard
    exact targetReentry.regularized.cardinality_retention
  have sourceDegree : targetSourcePower *
      targetReentry.normalization.croppedFamily.enncard ≤
        targetScaleFactor * targetDegree := by
    simpa only [targetSourcePower, targetScaleFactor, targetDegree,
      mul_assoc] using
        target.fineMultiplicity_source_cardinality_ledger hdeltaSmall
  let coefficient : ENNReal :=
    ((factor : ENNReal) * stickyCoarseCloseCount) * outerFiberPower *
      selectionCost *
      targetScaleFactor
  have coefficientCoarseBound : coefficient * coarseWeight ≤
      targetReentry.normalizationWeight * targetSourcePower := by
    simpa only [coefficient, outerFiberPower, selectionCost, coarseWeight,
      targetScaleFactor, targetSourcePower, mul_assoc, mul_left_comm,
      mul_comm] using hscalar
  have coefficientBound : coefficient ≤
      outer.data.coarse.enncard * targetReentry.normalizationWeight *
        targetSourcePower := by
    calc
      coefficient = coefficient * 1 := by simp
      _ ≤ coefficient * (coarseWeight * outer.data.coarse.enncard) := by
        gcongr
      _ = outer.data.coarse.enncard *
          (coefficient * coarseWeight) := by ring
      _ ≤ outer.data.coarse.enncard *
          (targetReentry.normalizationWeight * targetSourcePower) := by
        exact mul_le_mul_left' coefficientCoarseBound _
      _ = outer.data.coarse.enncard *
          targetReentry.normalizationWeight * targetSourcePower := by ring
  apply (ENNReal.mul_le_mul_iff_left commonPos.ne' commonTop).mp
  calc
    ((factor : ENNReal) * stickyCoarseCloseCount *
          (outer.terminal.muFine : ENNReal)) * common =
        ((factor : ENNReal) * stickyCoarseCloseCount) *
          (outer.data.coarse.enncard *
            (outer.terminal.muFine : ENNReal)) *
          targetReentry.normalizationWeight * targetSourcePower := by
      dsimp only [common]
      ring
    _ ≤ ((factor : ENNReal) * stickyCoarseCloseCount) *
          (outerFiberPower * outer.data.selected.family.enncard) *
          targetReentry.normalizationWeight * targetSourcePower := by
      have scaled := mul_le_mul_right'
        (mul_le_mul_left' outerFiber
          ((factor : ENNReal) * stickyCoarseCloseCount))
        (targetReentry.normalizationWeight * targetSourcePower)
      simpa only [outerFiberPower, mul_assoc] using scaled
    _ ≤ ((factor : ENNReal) * stickyCoarseCloseCount) *
          (outerFiberPower * sourceFamily.enncard) *
          targetReentry.normalizationWeight * targetSourcePower := by gcongr
    _ = ((factor : ENNReal) * stickyCoarseCloseCount) * outerFiberPower *
          targetSourcePower *
            (targetReentry.normalizationWeight * sourceFamily.enncard) := by
      ring
    _ ≤ ((factor : ENNReal) * stickyCoarseCloseCount) * outerFiberPower *
          targetSourcePower *
            (selectionCost *
              targetReentry.normalization.croppedFamily.enncard) := by gcongr
    _ = ((factor : ENNReal) * stickyCoarseCloseCount) * outerFiberPower *
          selectionCost *
          (targetSourcePower *
            targetReentry.normalization.croppedFamily.enncard) := by ring
    _ ≤ ((factor : ENNReal) * stickyCoarseCloseCount) * outerFiberPower *
          selectionCost *
          (targetScaleFactor * targetDegree) := by gcongr
    _ = coefficient * targetDegree := by
      dsimp only [coefficient]
      ring
    _ ≤ (outer.data.coarse.enncard *
          targetReentry.normalizationWeight * targetSourcePower) *
          targetDegree := by
      exact mul_le_mul_right' coefficientBound targetDegree
    _ = targetDegree * common := by
      dsimp only [common, targetDegree]
      ring

/-- Factor-two compatibility specialization used by the one-scale plane-map
route. -/
theorem proposition63_two_rich_cross_degree_of_terminal_scalar
    {delta sigma outerLoss outerSourceLoss outerNormalizationLoss
      targetReentryLoss targetLoss : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {outerNormalizationExponent : ℕ}
    {outerReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) sourceShading outerNormalizationExponent
      outerSourceLoss outerNormalizationLoss}
    {robustScale : WZ2PaperRequestedScale delta}
    (outer : Proposition63RichTerminalStickyData
      (outputLoss := outerLoss) sourceShading outerReentry robustScale)
    (targetReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := targetReentryLoss) outerReentry.toNormalizationData
      (extendShading outer.data.selected outer.data.refined))
    (htargetReentryLoss : 0 < targetReentryLoss)
    {targetScale : WZ2PaperRequestedScale delta}
    (target : Proposition63RichTerminalStickyData
      (outputLoss := targetLoss) targetReentry.normalization.croppedRefined
      (targetReentry.normalization.toPropStickyReentryData
        htargetReentryLoss
        targetReentry.reentry_normalization_loss_pos) targetScale)
    (hdeltaSmall : delta ≤ 1 / 12)
    (hrobustSmall : robustScale.1 ≤ 1 / 10000)
    (hscalar :
      (((2 * stickyCoarseCloseCount) *
          Kakeya.realRpowENN (delta / robustScale.1)
            (2 - sigma - outer.terminalLoss) *
          (targetReentry.regularized.regularizationLoss *
            targetReentry.weightUpper)) *
          ((12 : ENNReal) * ENNReal.ofReal Real.pi) *
          Kakeya.realRpowENN robustScale.1 (2 - outerLoss)) *
          ((target.terminal.regularity : ENNReal) *
            Kakeya.realRpowENN delta
              (sigma - targetReentry.reentryNormalizationLoss)) ≤
        targetReentry.normalizationWeight *
          (wz2PaperPureRefinementFraction delta 61 *
            Kakeya.realRpowENN delta
              (targetReentry.reentryNormalizationLoss + 2))) :
    2 * stickyCoarseCloseCount * (outer.terminal.muFine : ENNReal) ≤
      ((target.terminal.fineDegreeFloor * target.terminal.muFine : ℕ) :
        ENNReal) := by
  exact proposition63_two_rich_cross_degree_of_terminal_scalar_scaled
    outer targetReentry htargetReentryLoss target hdeltaSmall hrobustSmall 2
    hscalar

/-- The target terminal close count is controlled by the robust terminal
after transporting through both genuine dependent subfamily embeddings.
The explicit factor is kept in the statement so later multiplicity
extractions can reserve a larger fixed margin when needed. -/
theorem proposition63_two_rich_close_count_scaled_absorbed
    {delta sigma outerLoss outerSourceLoss outerNormalizationLoss
      targetReentryLoss targetLoss kappa : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {outerNormalizationExponent : ℕ}
    {outerReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) sourceShading outerNormalizationExponent
      outerSourceLoss outerNormalizationLoss}
    {robustScale : WZ2PaperRequestedScale delta}
    (outer : Proposition63RichTerminalStickyData
      (outputLoss := outerLoss) sourceShading outerReentry robustScale)
    {current : WZ1PaperTubeShading
      outerReentry.toNormalizationData.croppedFamily}
    (targetReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := targetReentryLoss) outerReentry.toNormalizationData
      current)
    (hcurrentSubOuter : PaperIsSubshading current
      (extendShading outer.data.selected outer.data.refined))
    (htargetReentryLoss : 0 < targetReentryLoss)
    {targetScale : WZ2PaperRequestedScale delta}
    (target : Proposition63RichTerminalStickyData
      (outputLoss := targetLoss) targetReentry.normalization.croppedRefined
      (targetReentry.normalization.toPropStickyReentryData
        htargetReentryLoss
        targetReentry.reentry_normalization_loss_pos) targetScale)
    (hrobustSmall : robustScale.1 ≤ 1 / 10000)
    (factor : ℕ)
    (hcrossCall :
      (factor : ENNReal) *
          (stickyCoarseCloseCount * (outer.terminal.muFine : ENNReal)) ≤
        ((target.terminal.fineDegreeFloor * target.terminal.muFine : ℕ) :
          ENNReal)) :
    ∀ point ∈ target.data.refined.union, ∀ index,
      point ∈ target.data.refined.carrier index →
        factor * paperCloseDirectionCount target.data.refined point index
            robustScale.1 ≤
          target.terminal.fineDegreeFloor * target.terminal.muFine := by
  let nestedSub : Kakeya.Streamlined.TubeSubfamily sourceFamily :=
    targetReentry.regularized.selected.comp target.data.selected
  have nestedSubshading : ∀ index,
      target.data.refined.carrier index ⊆
        (extendShading outer.data.selected outer.data.refined).carrier
          (nestedSub.embedding index) := by
    intro index point pointMem
    have targetSourceMem : point ∈
        targetReentry.normalization.croppedRefined.carrier
          (target.data.selected.embedding index) :=
      target.data.subshading index pointMem
    have restrictedMem : point ∈
        (restrictPaperShading targetReentry.regularized.selected
          current).carrier
            (target.data.selected.embedding index) := by
      exact targetReentry.denseSubshading
        (target.data.selected.embedding index) targetSourceMem
    change point ∈
      (extendShading outer.data.selected outer.data.refined).carrier
        ((target.data.selected.embedding.trans
          targetReentry.regularized.selected.embedding) index)
    rw [Function.Embedding.trans_apply]
    exact hcurrentSubOuter _ restrictedMem
  intro point pointMem index pointIndex
  have transported :
      (paperCloseDirectionCount target.data.refined point index
          robustScale.1 : ENNReal) ≤
        paperCloseDirectionCount
          (extendShading outer.data.selected outer.data.refined) point
          (nestedSub.embedding index) robustScale.1 := by
    exact_mod_cast paperCloseDirectionCount_le_of_tubeSubfamily
      nestedSub nestedSubshading point index
  have ambientCenterMem : point ∈
      (extendShading outer.data.selected outer.data.refined).carrier
        (nestedSub.embedding index) :=
    nestedSubshading index pointIndex
  have outerIndexExists : ∃ outerIndex,
      outer.data.selected.embedding outerIndex = nestedSub.embedding index := by
    by_contra noOuterIndex
    rw [extendShading_carrier_empty noOuterIndex] at ambientCenterMem
    exact ambientCenterMem
  rcases outerIndexExists with ⟨outerIndex, outerIndexEq⟩
  have outerPointMem : point ∈ outer.data.refined.carrier outerIndex := by
    rw [← extendShading_carrier_mem
      (sub := outer.data.selected) (refined := outer.data.refined)]
    rw [outerIndexEq]
    exact ambientCenterMem
  have outerPointUnion : point ∈ outer.data.refined.union :=
    ⟨outerIndex, outerPointMem⟩
  have outerBound :
      (paperCloseDirectionCount outer.data.refined point outerIndex
          robustScale.1 : ENNReal) ≤
        stickyCoarseCloseCount * (outer.terminal.muFine : ENNReal) :=
    outer.terminal.robust_close_count
      outer.data.coarse_extremal.delta_pos hrobustSmall point
      outerPointUnion outerIndex outerPointMem
  have extendedEq :
      paperCloseDirectionCount
          (extendShading outer.data.selected outer.data.refined) point
          (nestedSub.embedding index) robustScale.1 =
        paperCloseDirectionCount outer.data.refined point outerIndex
          robustScale.1 := by
    rw [← outerIndexEq]
    exact paperCloseDirectionCount_extendShading
      outer.data.selected outer.data.refined point outerIndex
  have resultENN :
      (factor * paperCloseDirectionCount target.data.refined point index
          robustScale.1 : ℕ) ≤
        target.terminal.fineDegreeFloor * target.terminal.muFine := by
    exact_mod_cast
      (calc
        (factor : ENNReal) *
              (paperCloseDirectionCount target.data.refined point index
                robustScale.1 : ENNReal) ≤
            factor *
              (paperCloseDirectionCount
                (extendShading outer.data.selected outer.data.refined) point
                (nestedSub.embedding index) robustScale.1 : ENNReal) := by
          gcongr
        _ = factor *
              (paperCloseDirectionCount outer.data.refined point outerIndex
                robustScale.1 : ENNReal) := by rw [extendedEq]
        _ ≤ factor *
              (stickyCoarseCloseCount *
                (outer.terminal.muFine : ENNReal)) := by gcongr
        _ ≤ ((target.terminal.fineDegreeFloor *
              target.terminal.muFine : ℕ) : ENNReal) := hcrossCall)
  exact resultENN

/-- Factor-two specialization used by the one-scale plane-map route. -/
theorem proposition63_two_rich_close_count_absorbed
    {delta sigma outerLoss outerSourceLoss outerNormalizationLoss
      targetReentryLoss targetLoss kappa : ℝ}
    {sourceFamily : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading sourceFamily}
    {outerNormalizationExponent : ℕ}
    {outerReentry : PureWZ2PropStickyReentryData
      (sigma := sigma) sourceShading outerNormalizationExponent
      outerSourceLoss outerNormalizationLoss}
    {robustScale : WZ2PaperRequestedScale delta}
    (outer : Proposition63RichTerminalStickyData
      (outputLoss := outerLoss) sourceShading outerReentry robustScale)
    (targetReentry : Proposition63CurrentShadingReentryData
      (reentryLoss := targetReentryLoss) outerReentry.toNormalizationData
      (extendShading outer.data.selected outer.data.refined))
    (htargetReentryLoss : 0 < targetReentryLoss)
    {targetScale : WZ2PaperRequestedScale delta}
    (target : Proposition63RichTerminalStickyData
      (outputLoss := targetLoss) targetReentry.normalization.croppedRefined
      (targetReentry.normalization.toPropStickyReentryData
        htargetReentryLoss
        targetReentry.reentry_normalization_loss_pos) targetScale)
    (hrobustSmall : robustScale.1 ≤ 1 / 10000)
    (hcrossCall :
      2 * (stickyCoarseCloseCount * (outer.terminal.muFine : ENNReal)) ≤
        ((target.terminal.fineDegreeFloor * target.terminal.muFine : ℕ) :
          ENNReal)) :
    ∀ point ∈ target.data.refined.union, ∀ index,
      point ∈ target.data.refined.carrier index →
        2 * paperCloseDirectionCount target.data.refined point index
            robustScale.1 ≤
          target.terminal.fineDegreeFloor * target.terminal.muFine := by
  exact proposition63_two_rich_close_count_scaled_absorbed outer
    targetReentry (fun _ => Set.Subset.rfl) htargetReentryLoss target
    (kappa := kappa) hrobustSmall 2 hcrossCall

end Kakeya.Assouad.PureWZ2

end
