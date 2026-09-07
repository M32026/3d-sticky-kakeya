import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalPopularLocalCells
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23GeometricInput

/-!
# Generalized Lemma-23 input for the terminal outer-popular carrier

The graph volume lower bound is conditional on the one fixed localized-piece
cost being bounded by the selected parent-count/weight-floor supply.  The
final constructor follows the coordinate-cropped WZ1 graph path, so it does
not replace the paper axis box by a false unit-ball containment.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

theorem PureWZ2TerminalPopularGraphPreparation.power_volume_lower
    {sigma inputLoss delta stickyLoss volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
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
    (prep : PureWZ2TerminalPopularGraphPreparation localized)
    (hbudget :
      pureWZ2TerminalPopularLocalizedPieceCost *
          Kakeya.realRpowENN delta (1 + sigma / 2 + volumeLoss) ≤
        (localized.selectedParents.card : ENNReal) *
          weightClass.weightFloor) :
    Kakeya.realRpowENN delta (1 + sigma / 2 + volumeLoss) ≤
      volume prep.shadow.union := by
  have hcostPos : 0 < pureWZ2TerminalPopularLocalizedPieceCost := by
    norm_num [pureWZ2TerminalPopularLocalizedPieceCost]
  have hcostTop : pureWZ2TerminalPopularLocalizedPieceCost ≠ ⊤ := by
    norm_num [pureWZ2TerminalPopularLocalizedPieceCost]
  apply (ENNReal.mul_le_mul_iff_left hcostPos.ne' hcostTop).mp
  simpa [mul_comm] using hbudget.trans prep.volume_floor

/-- Repackage the popular terminal preparation as the official generalized
WZ1 Lemma-23 geometric input. -/
def PureWZ2TerminalPopularLocalCellData.toGeometricInput
    {sigma inputLoss delta stickyLoss eta volumeLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
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
    (localCells : PureWZ2TerminalPopularLocalCellData
      (eta := eta) graphParents)
    (family : WZ1Lemma23LocalCellFamilyGeneralized
      (rho := delta) (sigma := sigma) (eta := eta) prep.shadow
      (pureWZ2TerminalPopularGraphConstant delta inputLoss)
      prep.windowed.global.sourceSlope prep.windowed.global.cells prep.localGrains)
    (hvolume : Kakeya.realRpowENN delta
        (1 + sigma / 2 + volumeLoss) ≤ volume prep.shadow.union) :
    WZ1Lemma23GeometricInputGeneralized
      (eta := eta) (volumeLoss := volumeLoss)
      prep.windowed prep.localGrains where
  window_volume := hvolume
  global_localization := prep.localization
  local_cell_family := family

/-- Coordinate-cropped version of the generalized WZ1 graph constructor.
The ordinary paper carrier lies in the coordinate cube, hence in a radius-2
ball rather than the unit ball used by the legacy convenience wrapper. -/
theorem PureWZ2TerminalPopularLocalCellData.toTheorem22ReadyOutput
    {sigma inputLoss delta stickyLoss eta volumeLoss constantLoss theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
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
    (localCells : PureWZ2TerminalPopularLocalCellData
      (eta := eta) graphParents)
    (hvolume : Kakeya.realRpowENN delta
        (1 + sigma / 2 + volumeLoss) ≤ volume prep.shadow.union)
    (absorption : WZ1Lemma23Theorem22Absorption
      delta theoremEta volumeLoss constantLoss)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (heta : 0 < eta) (hetaSigma : 4 * eta < sigma)
    (hCOne : (1 : ENNReal) ≤
      pureWZ2TerminalPopularGraphConstant delta inputLoss)
    (hCpower :
      (pureWZ2TerminalPopularGraphConstant delta inputLoss).toReal ≤
        Real.rpow delta (-constantLoss)) :
    Nonempty (WZ1Lemma23Theorem22ReadyOutput
      prep.windowed theoremEta) := by
  let C := pureWZ2TerminalPopularGraphConstant delta inputLoss
  have hCtop : C ≠ ⊤ := by
    dsimp only [C, pureWZ2TerminalPopularGraphConstant]
    exact ENNReal.mul_ne_top (by norm_num)
      (by simp [Kakeya.realRpowENN])
  have hcoord : ∀ point ∈ prep.shadow.union, ∀ coordinate : Fin 3,
      |point coordinate| ≤ 1 := by
    intro point hpoint coordinate
    have hsource := prep.shadow_source hpoint
    have hbox := shading_union_subset_axisBox hsource
    simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq] at hbox
    norm_num at hbox
    fin_cases coordinate <;> tauto
  rcases wz1_lemma23_localized_global_bin_package_of_coord_of_exact
      prep.windowed.global source.extremal.delta_le_one hcoord
      prep.exactAD hCtop prep.localization.center
      prep.localization.localization with ⟨localizedGlobal, _⟩
  rcases wz1_lemma23_y_residue_package prep.windowed.global
      source.extremal.delta_le_one with ⟨residue, _hresidueCells, hresidueExtra⟩
  rcases wz1_lemma23_localized_prepared_package prep.windowed
      localizedGlobal residue localCells.localBins with ⟨preparedGraph⟩
  rcases wz1_lemma23_localized_prepared_geometry_of_coord
      source.extremal.delta_le_one hcoord preparedGraph with ⟨geometry⟩
  have hpower := preparedGraph.power_edge_bound_of_coord
    source.extremal.delta_le_one hsigma hsigmaOne hcoord hCOne hCtop
    volumeLoss constantLoss 0 hvolume hCpower (by simp [hresidueExtra])
  have hedgeReal : Real.rpow (wz1Lemma23Theorem22Scale delta)
      (theoremEta - 3) ≤ (preparedGraph.normalized.H.card : ℝ) := by
    apply absorption.edge.trans
    simpa using hpower
  have hedgeENN : Kakeya.realRpowENN
      (wz1Lemma23Theorem22Scale delta) (theoremEta - 3) ≤
        (preparedGraph.normalized.H.card : ENNReal) := by
    rw [Kakeya.realRpowENN]
    have hcast : (preparedGraph.normalized.H.card : ENNReal) =
        ENNReal.ofReal (preparedGraph.normalized.H.card : ℝ) := by norm_cast
    rw [hcast]
    exact ENNReal.ofReal_le_ofReal hedgeReal
  have hedgeUnit : Kakeya.realRpowENN
      (wz1Lemma23Theorem22Scale delta) (theoremEta - 3) ≤
        (geometry.unitBall.H.card : ENNReal) := by
    rw [geometry.unitBall.edge_card]
    exact hedgeENN
  rcases geometry.toTheorem22ReadyGraph theoremEta hedgeUnit
      absorption.katzTao with ⟨ready⟩
  exact ⟨{
    localized := localizedGlobal
    residue := residue
    localBins := localCells.localBins
    prepared := preparedGraph
    geometry := geometry
    ready := ready
  }⟩

end Kakeya.Assouad

end
