import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalScaleExactRefinedReadyGraph
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalScaleExactProjection
import MyLeanRepo.Kakeya.Assouad.WZ1.VerticalRescalingADProof

/-!
# Projection dichotomy for the twice-normalized exact terminal graph

The second common `/5` homothety divides dot differences by `25`.  The
source dot-AD certificate therefore transports exactly to one fifth of the
new Theorem-22 scale.  The closed long-branch contradiction can then be
applied without identifying the auxiliary graph with the paper carrier.
-/

noncomputable section

namespace Kakeya.Assouad

theorem PureWZ2TerminalExactRefinedReadyGraph.dot_difference_ad
    {sigma inputLoss delta stickyLoss eta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {line : PureWZ2HorizontalFixedLineCore
      window.windowed source.globalGrains.slope}
    {parents : PureWZ2TerminalFixedLineParentData line}
    {selection : PureWZ2TerminalParentYSelection parents}
    {residue : PureWZ2TerminalParentYResidueData selection}
    {retained : PureWZ2TerminalRetainedShadingData residue}
    {sources : PureWZ2TerminalSourceFamily retained}
    {band : PureWZ2TerminalFixedBandSelection sources}
    {phase : PureWZ2TerminalHeightPhaseSelection band}
    {anchored : PureWZ2TerminalAnchoredPieceData phase}
    {prep : PureWZ2TerminalExactGraphPreparation anchored}
    {graphParents : PureWZ2TerminalExactGraphParentData prep}
    {localCells : PureWZ2TerminalExactLocalCellData (eta := eta) graphParents}
    {preparedGraph : PureWZ2TerminalExactPreparedGraphData localCells}
    {sharp : PureWZ2TerminalExactSharpGeometry preparedGraph}
    {first : PureWZ2TerminalExactReadyGraph
      (theoremEta := theoremEta) sharp}
    (data : PureWZ2TerminalExactRefinedReadyGraph first)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1) :
    IsADSet1 (wz1DotDifferenceSet data.common.H)
      (data.ready.deltaGraph / 5) (1 - sigma)
      (10 * ((16200 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) *
        (10 * Kakeya.realRpowENN delta (-inputLoss)))) := by
  let C : ENNReal := (16200 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) *
    (10 * Kakeya.realRpowENN delta (-inputLoss))
  have hfirst : IsADSet1 (wz1DotDifferenceSet first.common.H)
      (Real.sqrt delta / (25 * Real.sqrt 3)) (1 - sigma) C := by
    simpa [C] using first.dot_difference_ad hsigma hsigmaOne
  have hADScalePos : 0 < Real.sqrt delta / (25 * Real.sqrt 3) := by
    exact div_pos (Real.sqrt_pos.mpr source.extremal.delta_pos) (by positivity)
  have himage := hfirst.image_div_sq
    (delta := Real.sqrt delta / (25 * Real.sqrt 3))
    (M := 5) (by norm_num) hADScalePos hsigma hsigmaOne
  have hscale :
      (Real.sqrt delta / (25 * Real.sqrt 3)) / 5 ^ 2 =
        data.ready.deltaGraph / 5 := by
    rw [data.deltaGraph_eq, first.ready.deltaGraph_eq,
      wz1Lemma23Theorem22Scale]
    ring
  have himageSet :
      (fun value : ℝ => value / (5 : ℝ) ^ 2) ''
          wz1DotDifferenceSet first.common.H =
        (fun value : ℝ => value / 25) ''
          wz1DotDifferenceSet first.common.H := by
    congr 1
    funext value
    norm_num
  rw [data.common.dot_image]
  rw [himageSet, hscale] at himage
  simpa [C] using himage

/-- The twice-normalized exact graph satisfies Alternative A once the closed
common-endpoint reduction is supplied.  The one extra factor ten in the AD
constant is kept visible in the final long-branch absorption premise. -/
theorem PureWZ2TerminalExactRefinedReadyGraph.projection_alternative_a
    {sigma inputLoss delta stickyLoss eta theoremEta outputLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {line : PureWZ2HorizontalFixedLineCore
      window.windowed source.globalGrains.slope}
    {parents : PureWZ2TerminalFixedLineParentData line}
    {selection : PureWZ2TerminalParentYSelection parents}
    {residue : PureWZ2TerminalParentYResidueData selection}
    {retained : PureWZ2TerminalRetainedShadingData residue}
    {sources : PureWZ2TerminalSourceFamily retained}
    {band : PureWZ2TerminalFixedBandSelection sources}
    {phase : PureWZ2TerminalHeightPhaseSelection band}
    {anchored : PureWZ2TerminalAnchoredPieceData phase}
    {prep : PureWZ2TerminalExactGraphPreparation anchored}
    {graphParents : PureWZ2TerminalExactGraphParentData prep}
    {localCells : PureWZ2TerminalExactLocalCellData (eta := eta) graphParents}
    {preparedGraph : PureWZ2TerminalExactPreparedGraphData localCells}
    {sharp : PureWZ2TerminalExactSharpGeometry preparedGraph}
    {first : PureWZ2TerminalExactReadyGraph
      (theoremEta := theoremEta) sharp}
    (data : PureWZ2TerminalExactRefinedReadyGraph first)
    (hepsilon : 0 < outputLoss)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hepsilonSigma : outputLoss / 2 < sigma)
    {budgetFactor projectionEta reductionDelta₀ : ℝ}
    (hreduction :
      ∀ {rho' : ℝ} {sourceF' sourceG₁' sourceG₂' : DiscreteSet 2}
        {sourceH' : Finset (Point2 × Point2 × Point2)}
        {unitBall' : WZ1Lemma23UnitBallGraph
          rho' sourceF' sourceG₁' sourceG₂' sourceH'}
        (ready' : WZ1Lemma23Theorem22ReadyGraph rho' theoremEta unitBall'),
        ready'.deltaGraph ≤ reductionDelta₀ →
        unitBall'.G₂ = unitBall'.G₁ →
          WZ1Proposition8_9AlternativeAUnion ready'.deltaGraph outputLoss
              unitBall'.F unitBall'.G₁ unitBall'.G₁ ∨
            Nonempty (PureWZ2CommonEndpointProjectionLongData
              (epsilon := outputLoss) ready' budgetFactor projectionEta))
    (hdeltaSmall : data.ready.deltaGraph ≤ reductionDelta₀)
    (htheoremEta : 0 ≤ theoremEta)
    (htheoremEtaSmall : theoremEta ≤ 1 / 100)
    (hconstant : ∀ strongLong : PureWZ2CommonEndpointProjectionLongData
        (epsilon := outputLoss) data.ready budgetFactor projectionEta,
      let C : ENNReal := 10 *
        ((16200 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) *
          (10 * Kakeya.realRpowENN delta (-inputLoss)))
      ((5 * C) * ENNReal.ofReal
            (max 1 (10 * (strongLong.long.affine.dotScale *
              (data.ready.deltaGraph / 5)) /
                (data.ready.deltaGraph / 2)))) * 100 *
          Kakeya.realRpowENN (data.ready.deltaGraph / 2)
            (strongLong.long.projectionEta *
              (sigma - outputLoss / 2)) < 1) :
    WZ1Proposition8_9AlternativeAUnion data.ready.deltaGraph outputLoss
      data.common.F data.common.G₁ data.common.G₁ := by
  have hcommon : data.common.G₂ = data.common.G₁ := by
    rw [data.common.G₂_eq, data.common.G₁_eq]
  rcases hreduction data.ready hdeltaSmall hcommon with hA | hB
  · exact hA
  · rcases hB with ⟨strongLong⟩
    exfalso
    let C : ENNReal := 10 *
      ((16200 : ENNReal) * ENNReal.ofReal (Real.sqrt 3) *
        (10 * Kakeya.realRpowENN delta (-inputLoss)))
    have hAD : IsADSet1 (wz1DotDifferenceSet data.common.H)
        (data.ready.deltaGraph / 5) (1 - sigma) C := by
      simpa [C] using data.dot_difference_ad hsigma hsigmaOne
    have hCtop : C ≠ ⊤ := by
      dsimp only [C]
      exact ENNReal.mul_ne_top (by norm_num)
        (ENNReal.mul_ne_top
          (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
          (ENNReal.mul_ne_top (by norm_num)
            (by simp [Kakeya.realRpowENN])))
    have hdeltaGraphOne : data.ready.deltaGraph ≤ 1 := by
      rw [data.ready.deltaGraph_eq, wz1Lemma23Theorem22Scale]
      have hrefinedOne : delta / 625 ≤ 1 := by
        apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 625)).2
        nlinarith [source.extremal.delta_le_one]
      have hsqrt : Real.sqrt (delta / 625) ≤ 1 :=
        Real.sqrt_le_one.mpr hrefinedOne
      have hdenom : 1 ≤ 5 * Real.sqrt 3 := by
        have hsqrt3 : 1 ≤ Real.sqrt 3 :=
          (Real.one_le_sqrt).2 (by norm_num)
        nlinarith
      exact (div_le_self (Real.sqrt_nonneg (delta / 625)) hdenom).trans hsqrt
    have hdeltaGraphStrict : data.ready.deltaGraph < 1 := by
      have hdenom : 1 < 5 * Real.sqrt 3 := by
        have hsqrt3 : 1 ≤ Real.sqrt 3 :=
          (Real.one_le_sqrt).2 (by norm_num)
        nlinarith
      rw [data.ready.deltaGraph_eq, wz1Lemma23Theorem22Scale]
      have hrefinedPos : 0 < delta / 625 := by
        exact div_pos source.extremal.delta_pos (by norm_num)
      have hrootPos : 0 < Real.sqrt (delta / 625) :=
        Real.sqrt_pos.mpr hrefinedPos
      exact (div_lt_self hrootPos hdenom).trans_le
        (Real.sqrt_le_one.mpr (by
          apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 625)).2
          nlinarith [source.extremal.delta_le_one]))
    have hscaledOne : strongLong.long.affine.dotScale *
        (data.ready.deltaGraph / 5) ≤ 1 :=
      strongLong.scaled_dotAD_le_one rfl htheoremEta
        htheoremEtaSmall hdeltaGraphOne
    have htargetPos : 0 < data.ready.deltaGraph / 2 :=
      div_pos data.ready.deltaGraph_pos (by norm_num)
    have htargetOne : data.ready.deltaGraph / 2 ≤ 1 :=
      (div_le_self data.ready.deltaGraph_pos.le (by norm_num)).trans
        hdeltaGraphOne
    have htargetStrict : data.ready.deltaGraph / 2 < 1 := by
      calc
        data.ready.deltaGraph / 2 < data.ready.deltaGraph := by
          linarith [data.ready.deltaGraph_pos]
        _ < 1 := hdeltaGraphStrict
    exact strongLong.long.false_of_dot_ad hAD hCtop hsigma hsigmaOne
      (by positivity) hepsilonSigma hscaledOne htargetPos htargetOne
      htargetStrict (by simpa [C] using hconstant strongLong)

end Kakeya.Assouad
