import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalChainNumericSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalPopularOuterHeightSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalPairGoodBlocks
import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers

/-!
# Pre-runtime terminal schedule for an ordinary hierarchy step

This schedule runs the terminal paper-order geometry on the exact intermediate
grain source produced by the ordinary two-call owner.  The popular geometry is
charged at `richLoss`; no density or final one-scale loss is selected here.
-/

noncomputable section

namespace Kakeya.Assouad

structure PureWZ2OrdinaryWeightedTerminalSchedule
    (sigma middleLoss stickyLoss richLoss eta : ℝ) where
  globalLoss : ℝ := 2 * middleLoss
  globalLoss_eq : globalLoss = 2 * middleLoss
  projection : PureWZ2TerminalExactProjectionThreshold sigma richLoss
  volumeLoss : ℝ := projection.theoremEta / 64
  volumeLoss_eq : volumeLoss = projection.theoremEta / 64
  constantLoss : ℝ := projection.theoremEta / 64
  constantLoss_eq : constantLoss = projection.theoremEta / 64
  extraLoss : ℝ := projection.theoremEta / 64
  extraLoss_eq : extraLoss = projection.theoremEta / 64
  numeric : PureWZ2TerminalChainNumericThreshold sigma globalLoss stickyLoss eta
    projection.theoremEta richLoss volumeLoss constantLoss extraLoss
  globalLoss_le_projection : globalLoss ≤ projection.sourceLossCeiling
  localMassLoss : ℝ := 3 * richLoss / 4
  localMassLoss_eq : localMassLoss = 3 * richLoss / 4
  localMassLoss_pos : 0 < localMassLoss
  output_theorem : richLoss + projection.theoremEta ≤ 1
  rho₀ : ℝ
  rho₀_pos : 0 < rho₀
  rho₀_le_one : rho₀ ≤ 1
  rho₀_le_projection : rho₀ ≤ projection.delta₀
  rho₀_le_numeric : rho₀ ≤ numeric.delta₀
  normal_transfer : ∀ rho, 0 < rho → rho ≤ rho₀ →
    1000 * Real.sqrt rho ≤ 1
  outer_height : ∀ {rho inputLoss : ℝ} {logExponent : ℕ}
      {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss rho}
      {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
      {terminalSource : PureWZ2TerminalPreparedSource source terminal}
      {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
      {window : PureWZ2TerminalWindow prepared}
      (data : PureWZ2TerminalWindowHeightPopularData window),
    0 < rho → rho ≤ rho₀ →
      16 * Kakeya.realRpowENN rho localMassLoss *
          (data.popular.bins : ENNReal) *
          (data.popular.heightIndices.card : ENNReal) ≤
        pureWZ2TerminalPopularRichFloor rho richLoss
  popular_extra : ∀ {rho inputLoss : ℝ} {logExponent : ℕ}
      {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss rho}
      {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
      {terminalSource : PureWZ2TerminalPreparedSource source terminal}
      {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
      {window : PureWZ2TerminalWindow prepared}
      {heightData : PureWZ2TerminalWindowHeightPopularData window}
      {carrier : PureWZ2TerminalPopularSourceCarrierData heightData}
      {weightClass : PureWZ2TerminalPopularParentWeightClassData carrier}
      {restricted : PureWZ2TerminalPopularParentRestrictionData weightClass}
      {restrictedPrepared :
        PureWZ2TerminalPopularParentRestrictedPreparedData restricted}
      {line : PureWZ2HorizontalFixedBinCore
        restrictedPrepared.windowed source.globalGrains.slope}
      {parents : PureWZ2TerminalPopularRestrictedFixedBinParentData line}
      {selection : PureWZ2TerminalPopularRestrictedParentSelectionData parents}
      {selectedCarrier :
        PureWZ2TerminalPopularSelectedParentCarrierData selection}
      {sources : PureWZ2TerminalPopularCoarseSourceFamily selection}
      {localized : PureWZ2TerminalPopularLocalizedPieceData
        (selectedCarrier := selectedCarrier) sources}
      {prep : PureWZ2TerminalPopularGraphPreparation localized}
      {graphParents : PureWZ2TerminalPopularGraphParentData prep}
      {localCells : PureWZ2TerminalPopularLocalCellData
        (eta := eta) graphParents}
      (data : PureWZ2TerminalPopularPreparedGraphData localCells),
    0 < rho → rho ≤ rho₀ →
      (data.graph.residue.extraCost : ℝ) ≤ Real.rpow rho (-extraLoss)
  popular_c : ∀ rho, 0 < rho → rho ≤ rho₀ →
    (pureWZ2TerminalPopularGraphConstant rho globalLoss).toReal ≤
      Real.rpow rho (-constantLoss)
  weighted_slice : ∀ rho, 0 < rho → rho ≤ rho₀ →
    pureWZ2TerminalPairWeightedSliceLogCost rho *
        Kakeya.realRpowENN rho (1 + sigma / 2 + volumeLoss) *
        pureWZ2TerminalExactVolumeCost rho sigma globalLoss ≤
      (16 : ENNReal)⁻¹ * Kakeya.realRpowENN rho
        (2 + 3 * sigma / 2 + 5 * stickyLoss / 2)
  pair_mass : ∀ rho, 0 < rho → rho ≤ rho₀ →
    2 * pureWZ2TerminalPairSourceMassLogCost rho *
        Kakeya.realRpowENN rho (sigma + richLoss) ≤
      Kakeya.realRpowENN rho localMassLoss *
        Kakeya.realRpowENN rho (sigma + stickyLoss)
  global_conversion : ∀ rho, 0 < rho → rho ≤ rho₀ →
    100 * Kakeya.realRpowENN rho (-middleLoss) ≤
      Kakeya.realRpowENN rho (-globalLoss)
  final_length : ∀ rho, 0 < rho → rho ≤ rho₀ →
    Real.rpow (pureWZ2SourceHorizontalFinalScale rho)
        (1 / 2 + richLoss) ≤ Real.sqrt rho

theorem pureWZ2_ordinaryWeightedTerminal_schedule
    {sigma middleLoss stickyLoss richLoss eta : ℝ}
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hmiddle : 0 < middleLoss)
    (hsticky : 0 < stickyLoss)
    (hstickyMiddle : stickyLoss ≤ middleLoss / 2)
    (heta : 0 < eta) (hetaSigma : 8 * eta < sigma)
    (hmiddleEta : 2 * middleLoss < eta)
    (hrich : 0 < richLoss) (hrichOne : richLoss < 1)
    (hrichSigma : richLoss / 2 < sigma)
    (projection : PureWZ2TerminalExactProjectionThreshold sigma richLoss)
    (hglobalProjection : 2 * middleLoss ≤ projection.sourceLossCeiling)
    (hglobalConstant : 2 * middleLoss < projection.theoremEta / 64)
    (hvolumeGap :
      2 * middleLoss + 5 * stickyLoss / 2 < projection.theoremEta / 64)
    (hpairGap : stickyLoss + 3 * richLoss / 4 < richLoss)
    (houtputTheorem : richLoss + projection.theoremEta ≤ 1) :
    Nonempty (PureWZ2OrdinaryWeightedTerminalSchedule
      sigma middleLoss stickyLoss richLoss eta) := by
  let globalLoss := 2 * middleLoss
  let volumeLoss := projection.theoremEta / 64
  let constantLoss := projection.theoremEta / 64
  let extraLoss := projection.theoremEta / 64
  have hglobal : 0 < globalLoss := by dsimp only [globalLoss]; linarith
  have hglobalEta : globalLoss < eta := by
    dsimp only [globalLoss]
    exact hmiddleEta
  have hglobalProjection' : globalLoss ≤ projection.sourceLossCeiling := by
    simpa only [globalLoss] using hglobalProjection
  have hglobalConstant' : globalLoss < constantLoss := by
    simpa only [globalLoss, constantLoss] using hglobalConstant
  have hvolume : 0 < volumeLoss := by
    dsimp only [volumeLoss]
    exact div_pos projection.theoremEta_pos (by norm_num)
  have hconstant : 0 < constantLoss := by
    dsimp only [constantLoss]
    positivity
  have hextra : 0 < extraLoss := by
    dsimp only [extraLoss]
    positivity
  have hstickyEta : 3 * stickyLoss / 2 < eta := by
    linarith
  have hvolumeGap' : globalLoss + 5 * stickyLoss / 2 < volumeLoss := by
    simpa only [globalLoss, volumeLoss] using hvolumeGap
  have hedge : 8 * ((volumeLoss + extraLoss) + constantLoss) <
      projection.theoremEta / 2 := by
    dsimp only [volumeLoss, extraLoss, constantLoss]
    linarith [projection.theoremEta_pos]
  rcases pureWZ2_terminal_chain_numeric_threshold hsigma hsigmaOne hglobal
      hsticky heta (by linarith [hetaSigma]) hetaSigma hglobalEta
      hglobalConstant' hvolume
      hconstant hextra hstickyEta hvolumeGap' projection.theoremEta_pos
      (projection.theoremEta_small.trans (by norm_num)) hrich hrichOne
      hrichSigma hedge with ⟨numeric⟩
  let localMassLoss := 3 * richLoss / 4
  have hlocalMass : 0 < localMassLoss := by
    dsimp only [localMassLoss]
    linarith
  have hhalfLocal : richLoss / 2 < localMassLoss := by
    dsimp only [localMassLoss]
    linarith
  have hpairGap' : stickyLoss + localMassLoss < richLoss := by
    simpa only [localMassLoss] using hpairGap
  rcases exists_delta_rpow_le_single (1 / 2 : ℝ) (1 / 1000)
      (by norm_num) (by norm_num) (by norm_num) with
    ⟨normalRho₀, hnormalRho₀, hnormalRho₀One, hnormal⟩
  rcases pureWZ2_terminalPopular_outerHeight_schedule hrichOne hhalfLocal with
    ⟨heightRho₀, hheightRho₀, hheightRho₀One, hheight⟩
  rcases pureWZ2_terminalPopular_extraCost_schedule hextra with
    ⟨extraRho₀, hextraRho₀, hextraRho₀One, hextraBound⟩
  rcases pureWZ2_terminalPair_weightedSlice_budget_schedule hvolumeGap with
    ⟨weightedRho₀, hweightedRho₀, hweightedRho₀One, hweighted⟩
  rcases pureWZ2_terminalPair_doubleSourceMass_budget_schedule hpairGap' with
    ⟨pairRho₀, hpairRho₀, hpairRho₀One, hpair⟩
  rcases exists_scale_absorb_constant (100 : ENNReal) (by norm_num)
      hmiddle.le (by linarith : middleLoss < globalLoss) with
    ⟨conversionRho₀, hconversionRho₀, hconversionRho₀One, hconversion⟩
  rcases exists_scale_absorb_constant (40000 : ENNReal) (by norm_num)
      hglobal.le hglobalConstant' with
    ⟨popularCRho₀, hpopularCRho₀, hpopularCRho₀One, hpopularC⟩
  rcases exists_delta_rpow_le_single (1 - richLoss) (1 / 1280)
      (by linarith) (by norm_num) (by norm_num) with
    ⟨lengthScaleRho₀, hlengthScaleRho₀, hlengthScaleRho₀One, hlengthScale⟩
  rcases exists_delta_rpow_le_single (richLoss ^ 2) (1 / 36)
      (sq_pos_of_pos hrich) (by norm_num) (by norm_num) with
    ⟨lengthPowerRho₀, hlengthPowerRho₀, hlengthPowerRho₀One, hlengthPower⟩
  let rho₀ := min projection.delta₀
    (min numeric.delta₀ (min normalRho₀
      (min heightRho₀ (min extraRho₀ (min weightedRho₀
        (min pairRho₀ (min conversionRho₀
          (min popularCRho₀ (min lengthScaleRho₀ lengthPowerRho₀)))))))))
  have hrho₀ : 0 < rho₀ := by
    dsimp only [rho₀]
    exact lt_min projection.delta₀_pos <|
      lt_min numeric.delta₀_pos <| lt_min hnormalRho₀ <|
        lt_min hheightRho₀ <| lt_min hextraRho₀ <|
          lt_min hweightedRho₀ <| lt_min hpairRho₀ <|
            lt_min hconversionRho₀ <| lt_min hpopularCRho₀ <|
              lt_min hlengthScaleRho₀ hlengthPowerRho₀
  refine ⟨{
    globalLoss := globalLoss
    globalLoss_eq := rfl
    projection := projection
    volumeLoss := volumeLoss
    volumeLoss_eq := rfl
    constantLoss := constantLoss
    constantLoss_eq := rfl
    extraLoss := extraLoss
    extraLoss_eq := rfl
    numeric := numeric
    globalLoss_le_projection := hglobalProjection'
    localMassLoss := localMassLoss
    localMassLoss_eq := rfl
    localMassLoss_pos := hlocalMass
    output_theorem := houtputTheorem
    rho₀ := rho₀
    rho₀_pos := hrho₀
    rho₀_le_one := (min_le_left _ _).trans projection.delta₀_le_one
    rho₀_le_projection := min_le_left _ _
    rho₀_le_numeric := (min_le_right _ _).trans (min_le_left _ _)
    normal_transfer := ?_
    outer_height := ?_
    popular_extra := ?_
    popular_c := ?_
    weighted_slice := ?_
    pair_mass := ?_
    global_conversion := ?_
    final_length := ?_
  }⟩
  · intro rho hrho hrhoSmall
    have hsmall : rho ≤ normalRho₀ := hrhoSmall.trans <|
      (min_le_right _ _).trans <| (min_le_right _ _).trans (min_le_left _ _)
    have hp := hnormal rho hrho hsmall
    rw [show Real.rpow rho (1 / 2 : ℝ) = Real.sqrt rho by
      exact (Real.sqrt_eq_rpow rho).symm] at hp
    nlinarith
  · intro rho inputLoss logExponent source terminal terminalSource prepared
      window data hrho hrhoSmall
    exact hheight data hrho <| hrhoSmall.trans <|
      (min_le_right _ _).trans <| (min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_left _ _)
  · intro rho inputLoss logExponent source terminal terminalSource prepared
      window heightData carrier weightClass restricted restrictedPrepared line
      parents selection selectedCarrier sources localized prep graphParents
      localCells data hrho hrhoSmall
    exact hextraBound data hrho <| hrhoSmall.trans <|
      (min_le_right _ _).trans <| (min_le_right _ _).trans <|
        (min_le_right _ _).trans <| (min_le_right _ _).trans (min_le_left _ _)
  · intro rho hrho hrhoSmall
    have hsmall : rho ≤ popularCRho₀ :=
      hrhoSmall.trans (by simp [rho₀])
    have hENN := hpopularC rho hrho hsmall
    have htop : Kakeya.realRpowENN rho (-constantLoss) ≠ ⊤ := by
      simp [Kakeya.realRpowENN]
    have hreal := ENNReal.toReal_mono htop hENN
    simpa [pureWZ2TerminalPopularGraphConstant, Kakeya.realRpowENN,
      ENNReal.toReal_ofReal (Real.rpow_nonneg hrho.le _)] using hreal
  · intro rho hrho hrhoSmall
    exact hweighted (sigma := sigma) hrho <| hrhoSmall.trans <|
      (min_le_right _ _).trans <| (min_le_right _ _).trans <|
        (min_le_right _ _).trans <| (min_le_right _ _).trans <|
          (min_le_right _ _).trans (min_le_left _ _)
  · intro rho hrho hrhoSmall
    exact hpair (sigma := sigma) hrho <| hrhoSmall.trans <|
      (min_le_right _ _).trans <| (min_le_right _ _).trans <|
        (min_le_right _ _).trans <| (min_le_right _ _).trans <|
          (min_le_right _ _).trans <| (min_le_right _ _).trans (min_le_left _ _)
  · intro rho hrho hrhoSmall
    exact hconversion rho hrho <| hrhoSmall.trans <|
      (min_le_right _ _).trans <| (min_le_right _ _).trans <|
        (min_le_right _ _).trans <| (min_le_right _ _).trans <|
          (min_le_right _ _).trans <| (min_le_right _ _).trans <|
            (min_le_right _ _).trans (min_le_left _ _)
  · intro rho hrho hrhoSmall
    have hscaleSmall : rho ≤ lengthScaleRho₀ :=
      hrhoSmall.trans (by simp [rho₀])
    have hpowerSmall : rho ≤ lengthPowerRho₀ :=
      hrhoSmall.trans (by simp [rho₀])
    have hscale := hlengthScale rho hrho hscaleSmall
    have hfactor : 1280 * Real.rpow rho (1 - richLoss) ≤ 1 := by
      nlinarith
    have htargetUpper : pureWZ2SourceHorizontalFinalScale rho ≤
        Real.rpow rho richLoss := by
      unfold pureWZ2SourceHorizontalFinalScale
      calc
        1280 * rho = 1280 * Real.rpow rho 1 :=
          congrArg (fun x : ℝ => 1280 * x) (Real.rpow_one rho).symm
        _ = 1280 * Real.rpow rho ((1 - richLoss) + richLoss) := by ring_nf
        _ = 1280 * (Real.rpow rho (1 - richLoss) *
              Real.rpow rho richLoss) :=
          congrArg (fun x : ℝ => 1280 * x)
            (Real.rpow_add hrho (1 - richLoss) richLoss)
        _ = (1280 * Real.rpow rho (1 - richLoss)) *
              Real.rpow rho richLoss := by ring
        _ ≤ 1 * Real.rpow rho richLoss := by
          gcongr
          exact Real.rpow_nonneg hrho.le richLoss
        _ = Real.rpow rho richLoss := by simp
    have hlength := pureWZ2_sourceHorizontal_length_lower hrho hrich
      (by unfold pureWZ2SourceHorizontalFinalScale; positivity)
      htargetUpper (hlengthPower rho hrho hpowerSmall)
    have hinternal : pureWZ2SourceHorizontalInternalScale
        (pureWZ2SourceHorizontalFinalScale rho) = rho := by
      unfold pureWZ2SourceHorizontalInternalScale
        pureWZ2SourceHorizontalFinalScale
      ring
    rw [hinternal] at hlength
    exact hlength

end Kakeya.Assouad

end
