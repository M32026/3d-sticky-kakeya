import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.Node6FixedHeightSelection
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.Node6SpatialCover
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.Node6FixedC2ZeroExtension
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.Section6Absorption

/-!
# Scalar budgets for the fixed-scale Node-6 selector

This module deliberately stays below the historical `PropSticky` interface.
The only logarithmic loss in the fixed-scale packet is the recorded
`cellIndexedMassRatio`; the first lemma below pays that loss together with
the literal refinement fraction before any runtime fixed-scale datum is
introduced.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

/-- The direction-level count is bounded by the standard logarithmic
envelope.  This local formulation is kept public because Node 6 needs the
bound independently of the Proposition-6.2 producer. -/
theorem node6_fixed_directionLevelCount_le_logEnvelope
    {delta : ℝ} (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1) :
    (pureWZ2Prop62DirectionLevelCount delta : ENNReal) ≤
      2 * ENNReal.ofReal (1 + Real.log delta⁻¹) := by
  have hlogNonneg : 0 ≤ Real.log delta⁻¹ :=
    Real.log_nonneg ((one_le_inv₀ hdelta).mpr hdeltaOne)
  have hquotientNonneg :
      0 ≤ Real.log delta⁻¹ / Real.log 2 := by positivity
  have hfloor :
      (Nat.floor (Real.log delta⁻¹ / Real.log 2) : ℝ) ≤
        Real.log delta⁻¹ / Real.log 2 :=
    Nat.floor_le hquotientNonneg
  have hlogTwoHalf : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have hbound : Real.log (1 / 2 : ℝ) ≤ (1 / 2 : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos (by norm_num)
    have hrewrite : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
      rw [Real.log_div (by norm_num) (by norm_num)]
      simp
    rw [hrewrite] at hbound
    linarith
  have hquotient :
      Real.log delta⁻¹ / Real.log 2 ≤ 2 * Real.log delta⁻¹ := by
    rw [div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
    nlinarith
  have hreal :
      (pureWZ2Prop62DirectionLevelCount delta : ℝ) ≤
        2 * (1 + Real.log delta⁻¹) := by
    change
      ((Nat.floor (Real.log (1 / delta) / Real.log 2) + 1 : ℕ) : ℝ) ≤
        2 * (1 + Real.log delta⁻¹)
    rw [show 1 / delta = delta⁻¹ by simp]
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith
  have hconverted := ENNReal.ofReal_mono hreal
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)] at hconverted
  norm_num at hconverted ⊢
  simpa using hconverted

/-- Before runtime fixed-scale data is selected, a strict source-to-slab gap
absorbs both the Node-6 polylogarithmic cell ratio and the refinement loss.
This is uniform in all later packet data. -/
theorem exists_delta_node6_fixed_ratio_refinement_absorption
    (sourceLoss slabLoss : ℝ)
    (hsourceSlab : sourceLoss < slabLoss)
    (logExponent : ℕ) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
        (pureWZ2Prop62DirectionLevelCount delta : ENNReal) ^ 10 *
            Kakeya.realRpowENN delta slabLoss ≤
          wz2PaperPureRefinementFraction delta logExponent *
            Kakeya.realRpowENN delta sourceLoss := by
  let middleLoss : ℝ := (sourceLoss + slabLoss) / 2
  have hsourceMiddle : sourceLoss < middleLoss := by
    dsimp [middleLoss]
    linarith
  have hmiddleSlab : middleLoss < slabLoss := by
    dsimp [middleLoss]
    linarith
  rcases exists_delta_pure_refinement_fraction_absorbs
      sourceLoss middleLoss hsourceMiddle logExponent with
    ⟨refinementScale, hrefinementPos, hrefinementOne, hrefinement⟩
  rcases exists_delta_C_pow_log_absorbed_ennreal
      (1 : ENNReal) (by norm_num) 2 (by norm_num)
      (sub_pos.mpr hmiddleSlab) (by norm_num : 0 < (10 : ℕ)) with
    ⟨ratioScale, hratioPos, hratioOne, hratio⟩
  let delta₀ : ℝ := min refinementScale ratioScale
  refine ⟨delta₀, lt_min hrefinementPos hratioPos,
    (min_le_left _ _).trans hrefinementOne, ?_⟩
  intro delta hdelta hdeltaBound
  have hdeltaOne : delta ≤ 1 :=
    hdeltaBound.trans ((min_le_left _ _).trans hrefinementOne)
  have hdeltaRefinement : delta ≤ refinementScale :=
    hdeltaBound.trans (min_le_left _ _)
  have hdeltaRatio : delta ≤ ratioScale :=
    hdeltaBound.trans (min_le_right _ _)
  have hcount := node6_fixed_directionLevelCount_le_logEnvelope hdelta hdeltaOne
  have hcountPow :
      (pureWZ2Prop62DirectionLevelCount delta : ENNReal) ^ 10 ≤
        (2 * ENNReal.ofReal (1 + Real.log delta⁻¹)) ^ 10 :=
    pow_le_pow_left' hcount 10
  have hratioPower :
      (2 * ENNReal.ofReal (1 + Real.log delta⁻¹)) ^ 10 ≤
        Kakeya.realRpowENN delta (-(slabLoss - middleLoss)) := by
    simpa [mul_comm] using hratio delta hdelta hdeltaRatio
  have hratioBound :
      (pureWZ2Prop62DirectionLevelCount delta : ENNReal) ^ 10 ≤
        Kakeya.realRpowENN delta (-(slabLoss - middleLoss)) :=
    hcountPow.trans hratioPower
  have hratioFinal :
      (pureWZ2Prop62DirectionLevelCount delta : ENNReal) ^ 10 *
          Kakeya.realRpowENN delta slabLoss ≤
        Kakeya.realRpowENN delta middleLoss := by
    calc
      (pureWZ2Prop62DirectionLevelCount delta : ENNReal) ^ 10 *
          Kakeya.realRpowENN delta slabLoss ≤
        Kakeya.realRpowENN delta (-(slabLoss - middleLoss)) *
          Kakeya.realRpowENN delta slabLoss := by gcongr
      _ = Kakeya.realRpowENN delta middleLoss := by
        rw [← realRpowENN_add hdelta]
        congr 2
        ring
  exact hratioFinal.trans (hrefinement hdelta hdeltaRefinement)

/-- Convert the two scalar inequalities natural for the fixed-scale packet
into the exact hypotheses consumed by `Node6FixedHeightSelection`.  The
selection scalar is deliberately stated before division by the cell mass;
the proof performs that cancellation only after recording the required
nonzero and finite factors. -/
theorem PureWZ2Node6FixedScaleOutput.fixed_height_budgets_of_scalars
    {delta sigma sourceLoss fixedLoss slabLoss power : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (cfg : PureWZ2C2GrainConfiguration sigma sourceLoss delta)
    (data : PureWZ2Node6FixedScaleOutput
      (sigma := sigma) (outputLoss := fixedLoss)
      cfg.shading rho logExponent)
    (hrho : rho.1 = Real.rpow delta power)
    (hdeltaSmall : delta ≤ 1 / 12)
    (hsigma : sigma < 2)
    (hsourceFixed : sourceLoss ≤ fixedLoss)
    (hfixedSlab : fixedLoss ≤ slabLoss)
    (targetMass coverBudget : ENNReal)
    (htargetMass : targetMass =
      ENNReal.ofReal (Real.pi / 4) *
        Kakeya.realRpowENN delta (slabLoss + 2) *
        cfg.family.enncard * ENNReal.ofReal rho.1)
    (hglobalScalar :
      4 * data.cellIndexedMassRatio * targetMass ≤
        ENNReal.ofReal rho.1 *
          (wz2PaperPureRefinementFraction delta logExponent *
            (Kakeya.realRpowENN delta sourceLoss *
              cfg.family.enncard * Kakeya.realRpowENN delta 2)))
    (hactive : data.balanced.activeCells.Nonempty)
    (hselectionScalar :
      targetMass *
          ((data.balanced.activeCells.card : ENNReal) *
            data.cellIndexedMassRatio) ≤
        (coverBudget / 16) *
          ((data.balanced.activeCells.card : ENNReal) *
            data.cellIndexedMassRatio * data.cellIndexedMassBase))
    (hcoverScalar : (1 : ENNReal) ≤ coverBudget / 16) :
    (4 * data.cellIndexedMassRatio * targetMass ≤
        ENNReal.ofReal rho.1 * data.refined.mass) ∧
      (targetMass / data.cellIndexedMassBase + 1 ≤ coverBudget / 8) := by
  have hsourceMass :
      Kakeya.realRpowENN delta sourceLoss * cfg.family.enncard *
          Kakeya.realRpowENN delta 2 ≤ cfg.shading.mass :=
    calc
      Kakeya.realRpowENN delta sourceLoss * cfg.family.enncard *
          Kakeya.realRpowENN delta 2 =
        Kakeya.realRpowENN delta sourceLoss *
          (cfg.family.enncard * Kakeya.realRpowENN delta 2) := by ring
      _ ≤ Kakeya.realRpowENN delta sourceLoss *
          (wz1PaperBodyFamily cfg.family).mass := by
        gcongr
        exact pureWZ2_prop62_paper_body_mass_lower
          cfg.extremal.delta_pos hdeltaSmall cfg.line_class
      _ ≤ cfg.shading.mass := cfg.extremal.dense
  have hrefinedMass :
      wz2PaperPureRefinementFraction delta logExponent *
          (Kakeya.realRpowENN delta sourceLoss * cfg.family.enncard *
            Kakeya.realRpowENN delta 2) ≤ data.refined.mass := by
    calc
      wz2PaperPureRefinementFraction delta logExponent *
          (Kakeya.realRpowENN delta sourceLoss * cfg.family.enncard *
            Kakeya.realRpowENN delta 2) ≤
          wz2PaperPureRefinementFraction delta logExponent *
            cfg.shading.mass := by gcongr
      _ ≤ data.refined.mass := data.retained_mass
  have hglobalMassBudget :
      4 * data.cellIndexedMassRatio * targetMass ≤
        ENNReal.ofReal rho.1 * data.refined.mass :=
    hglobalScalar.trans (by gcongr)
  have hcardPos : 0 < (data.balanced.activeCells.card : ENNReal) := by
    exact_mod_cast hactive.card_pos
  let factor : ENNReal :=
    (data.balanced.activeCells.card : ENNReal) * data.cellIndexedMassRatio
  have hfactorZero : factor ≠ 0 := by
    dsimp [factor]
    exact mul_ne_zero hcardPos.ne' data.cellIndexedMassRatio_pos.ne'
  have hfactorTop : factor ≠ ⊤ := by
    dsimp [factor]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top
      data.cellIndexedMassRatio_ne_top
  have hselectionScaled :
      targetMass * factor ≤
        (coverBudget / 16) * (factor * data.cellIndexedMassBase) := by
    simpa [factor, mul_assoc, mul_left_comm, mul_comm] using hselectionScalar
  have hselectionRaw :
      targetMass ≤ (coverBudget / 16) * data.cellIndexedMassBase := by
    apply (ENNReal.mul_le_mul_iff_left hfactorZero hfactorTop).mp
    simpa [factor, mul_assoc, mul_left_comm, mul_comm] using hselectionScaled
  have hbaseZero : data.cellIndexedMassBase ≠ 0 :=
    data.cellIndexedMassBase_pos.ne'
  have hselectionSixteen :
      targetMass / data.cellIndexedMassBase ≤ coverBudget / 16 := by
    apply (ENNReal.div_le_iff hbaseZero data.cellIndexedMassBase_ne_top).mpr
    simpa [mul_comm, mul_left_comm, mul_assoc] using hselectionRaw
  refine ⟨hglobalMassBudget, ?_⟩
  calc
    targetMass / data.cellIndexedMassBase + 1 ≤
        coverBudget / 16 + coverBudget / 16 := by
      exact add_le_add hselectionSixteen hcoverScalar
    _ = coverBudget / 8 := by
      rw [ENNReal.div_add_div_same]
      rw [show coverBudget + coverBudget = 2 * coverBudget by ring,
        show (16 : ENNReal) = 2 * 8 by norm_num]
      exact ENNReal.mul_div_mul_left coverBudget 8
        (by norm_num) (by norm_num)

/-- The scalar bridge can be consumed immediately by the fixed-height
selector.  In particular the zero extension is used only to form the final
selected shading, never in either numerical budget. -/
theorem PureWZ2Node6FixedScaleOutput.fixed_height_selection_of_scalars
    {delta sigma sourceLoss fixedLoss slabLoss power : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (cfg : PureWZ2C2GrainConfiguration sigma sourceLoss delta)
    (data : PureWZ2Node6FixedScaleOutput
      (sigma := sigma) (outputLoss := fixedLoss)
      cfg.shading rho logExponent)
    (zeroExtension :
      WZ2PaperSubfamilyZeroExtensionData data.selected data.refined)
    (hrho : rho.1 = Real.rpow delta power)
    (hdeltaSmall : delta ≤ 1 / 12)
    (hsigma : sigma < 2)
    (hsourceFixed : sourceLoss ≤ fixedLoss)
    (hfixedSlab : fixedLoss ≤ slabLoss)
    (targetMass coverBudget : ENNReal)
    (htargetMass : targetMass =
      ENNReal.ofReal (Real.pi / 4) *
        Kakeya.realRpowENN delta (slabLoss + 2) *
        cfg.family.enncard * ENNReal.ofReal rho.1)
    (hcoverBudget : coverBudget =
      Kakeya.realRpowENN delta (-slabLoss) *
        Kakeya.realRpowENN rho.1 (-2 + sigma))
    (hglobalScalar :
      4 * data.cellIndexedMassRatio * targetMass ≤
        ENNReal.ofReal rho.1 *
          (wz2PaperPureRefinementFraction delta logExponent *
            (Kakeya.realRpowENN delta sourceLoss *
              cfg.family.enncard * Kakeya.realRpowENN delta 2)))
    (hactive : data.balanced.activeCells.Nonempty)
    (hselectionScalar :
      targetMass *
          ((data.balanced.activeCells.card : ENNReal) *
            data.cellIndexedMassRatio) ≤
        (coverBudget / 16) *
          ((data.balanced.activeCells.card : ENNReal) *
            data.cellIndexedMassRatio * data.cellIndexedMassBase))
    (hcoverScalar : (1 : ENNReal) ≤ coverBudget / 16) :
    Nonempty (PureWZ2Node6FixedHeightSelectionProvenance
      (slabLoss := slabLoss) data zeroExtension targetMass coverBudget) := by
  rcases data.fixed_height_budgets_of_scalars (source := cfg.family) cfg hrho hdeltaSmall hsigma
      hsourceFixed hfixedSlab targetMass coverBudget htargetMass hglobalScalar
      hactive hselectionScalar hcoverScalar with ⟨hglobal, hselection⟩
  exact data.section6ScaleProvenance_of_global_indexed_mass_budget
    zeroExtension slabLoss hfixedSlab targetMass coverBudget htargetMass
    hcoverBudget hglobal hselection

end Kakeya.Assouad

end
