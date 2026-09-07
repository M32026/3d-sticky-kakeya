import MyLeanRepo.Kakeya.Assouad.PureWZ2.CallerCenterEnvelopeConflictDegree
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62CanonicalMassBudget
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Section6CoverParentMap
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLinePackingCardinality

/-!
# Proposition 6.2 two-layer cardinality

This module contains the statement-independent two-layer packing argument.
The coarse family is controlled by five line parameters.  Each complete
metric fiber is controlled after literal rescaling by six parameters.  The
resulting eleven-dimensional bound gives the logarithmic cardinality estimate
needed by the four-degree construction.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- The six-dimensional packing count at the rescaled fiber scale. -/
def pureWZ2Prop62RescaledFiberPackingBound
    (delta rho : ℝ) : ℕ :=
  (2 * Nat.ceil (3 / ((delta / rho) / 64)) + 1) ^ 3 *
    (2 * Nat.ceil (1 / ((delta / rho) / 64)) + 1) ^ 3

/-- One grid base simultaneously dominating coarse and rescaled-fiber counts. -/
def pureWZ2Prop62TwoLayerGridBase (delta : ℝ) : ℕ :=
  2 * Nat.ceil (192 / delta) + 1

/-- Explicit coefficient for the logarithm of the eleven-dimensional grid. -/
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

theorem pureWZ2Prop62_coarse_card_le_twoLayer
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : PureWZ2Section6Cover fine coarse)
    (deltaPos : 0 < delta)
    (deltaLeRho : delta ≤ rho)
    (rhoLeOne : rho ≤ 1) :
    coarse.card ≤ pureWZ2Prop62TwoLayerGridBase delta ^ 5 := by
  have rhoPos : 0 < rho := deltaPos.trans_le deltaLeRho
  have raw :
      coarse.card ≤
        (2 * Nat.ceil (80 / rho) + 1) ^ 5 :=
    paper_essentially_distinct_card_bound_nat
      cover.coarse_essentially_distinct cover.coarse_line_class
      rhoPos rhoLeOne
  have inverseLe : 1 / rho ≤ 1 / delta :=
    one_div_le_one_div_of_le deltaPos deltaLeRho
  have argumentLe : 80 / rho ≤ 192 / delta := by
    calc
      80 / rho = 80 * (1 / rho) := by ring
      _ ≤ 80 * (1 / delta) := by gcongr
      _ ≤ 192 * (1 / delta) := by
        gcongr
        norm_num
      _ = 192 / delta := by ring
  exact raw.trans <| by
    unfold pureWZ2Prop62TwoLayerGridBase
    gcongr

theorem pureWZ2Prop62_fine_card_le_coarse_mul_fiberPacking
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : PureWZ2Section6Cover fine coarse)
    (sourceConstant : Fin coarse.card → ENNReal)
    (rescaledFiber :
      ∀ parent,
        Nonempty
          (PureWZ2Prop62MetricFiberRescalingInput
            cover parent (sourceConstant parent))) :
    fine.card ≤
      coarse.card * pureWZ2Prop62RescaledFiberPackingBound delta rho := by
  let parentMap := cover.toWZ1PaperTubeCover.parent
  have fiberEq :
      ∀ parent : Fin coarse.card,
        ((Finset.univ : Finset (Fin fine.card)).filter fun source =>
          parentMap source = parent) =
          wz2PaperFullFiberIndices fine coarse parent := by
    intro parent
    ext source
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      mem_wz2PaperFullFiberIndices_iff]
    constructor
    · intro parentEq
      rw [← parentEq]
      exact cover.toWZ1PaperTubeCover.parent_covers source
    · intro sourceCovered
      exact
        (cover.toWZ1PaperTubeCover.parent_unique
          source parent sourceCovered).symm
  have fiberSum :
      ∑ parent : Fin coarse.card,
          ((Finset.univ : Finset (Fin fine.card)).filter fun source =>
            parentMap source = parent).card =
        fine.card := by
    simpa only [Finset.mem_univ, Finset.filter_true,
      Finset.card_univ, Fintype.card_fin] using
      Finset.sum_card_fiberwise_eq_card_filter
        (Finset.univ : Finset (Fin fine.card))
        (Finset.univ : Finset (Fin coarse.card))
        parentMap
  calc
    fine.card =
        ∑ parent : Fin coarse.card,
          ((Finset.univ : Finset (Fin fine.card)).filter fun source =>
            parentMap source = parent).card := fiberSum.symm
    _ =
        ∑ parent : Fin coarse.card,
          (wz2PaperFullFiberIndices fine coarse parent).card := by
      apply Finset.sum_congr rfl
      intro parent _
      rw [fiberEq parent]
    _ ≤
        ∑ _parent : Fin coarse.card,
          pureWZ2Prop62RescaledFiberPackingBound delta rho := by
      exact Finset.sum_le_sum fun parent _ =>
        pureWZ2Prop62_rescaledFiber_fullFiber_card_le
          (Classical.choice (rescaledFiber parent))
    _ =
        coarse.card *
          pureWZ2Prop62RescaledFiberPackingBound delta rho := by
      simp

theorem pureWZ2Prop62_fine_card_le_twoLayer
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : PureWZ2Section6Cover fine coarse)
    (deltaPos : 0 < delta)
    (deltaLeRho : delta ≤ rho)
    (rhoLeOne : rho ≤ 1)
    (sourceConstant : Fin coarse.card → ENNReal)
    (rescaledFiber :
      ∀ parent,
        Nonempty
          (PureWZ2Prop62MetricFiberRescalingInput
            cover parent (sourceConstant parent))) :
    fine.card ≤ pureWZ2Prop62TwoLayerGridBase delta ^ 11 := by
  calc
    fine.card ≤
        coarse.card *
          pureWZ2Prop62RescaledFiberPackingBound delta rho :=
      pureWZ2Prop62_fine_card_le_coarse_mul_fiberPacking
        cover sourceConstant rescaledFiber
    _ ≤
        pureWZ2Prop62TwoLayerGridBase delta ^ 5 *
          pureWZ2Prop62TwoLayerGridBase delta ^ 6 := by
      gcongr
      · exact
          pureWZ2Prop62_coarse_card_le_twoLayer
            cover deltaPos deltaLeRho rhoLeOne
      · exact
          pureWZ2Prop62_rescaledFiberPackingBound_le_twoLayer
            deltaPos (deltaPos.trans_le deltaLeRho) rhoLeOne
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

/--
The reusable two-layer conclusion from explicit metric fields.  No frozen V4
record or statement module is involved.
-/
theorem pureWZ2Prop62_twoLayer_fineLog
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : PureWZ2Section6Cover fine coarse)
    (deltaPos : 0 < delta)
    (deltaLeRho : delta ≤ rho)
    (rhoLeOne : rho ≤ 1)
    (fineNonempty : fine.Nonempty)
    (sourceConstant : Fin coarse.card → ENNReal)
    (rescaledFiber :
      ∀ parent,
        Nonempty
          (PureWZ2Prop62MetricFiberRescalingInput
            cover parent (sourceConstant parent))) :
    (Nat.log 2 (2 * fine.card) + 1 : ℝ) ≤
      pureWZ2Prop62TwoLayerCardLogConstant *
        (1 + Real.log delta⁻¹) := by
  exact
    pureWZ2Prop62_twoLayer_card_log_bound
      deltaPos (deltaLeRho.trans rhoLeOne) fineNonempty
      (pureWZ2Prop62_fine_card_le_twoLayer
        cover deltaPos deltaLeRho rhoLeOne sourceConstant rescaledFiber)

end Kakeya.Assouad

end
