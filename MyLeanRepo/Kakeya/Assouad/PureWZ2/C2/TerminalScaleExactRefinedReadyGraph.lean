import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalScaleExactReadyGraph

/-!
# A second common homothety for the exact terminal graph

The first unit-ball normalization divides every planar vertex by `5`.  For
the exact terminal trapezoid we apply the same common homothety once more,
but run Theorem 22 at the genuinely smaller graph parameter `delta / 625`.
Consequently the new Theorem-22 scale is the old scale divided by `25`.
After pulling the strip back through both homotheties this leaves the needed
physical strip width `delta / (5 * sqrt 3)`.

The stronger edge threshold and Katz--Tao power absorption are explicit
inputs.  In particular, neither is inferred from the first ready graph.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

private lemma pureWZ2_exact_refined_sqrt
    {delta : ℝ} (hdelta : 0 ≤ delta) :
    Real.sqrt (delta / 625) = Real.sqrt delta / 25 := by
  rw [Real.sqrt_div hdelta]
  norm_num

private lemma pureWZ2_exact_refined_target_le_fifth
    {delta : ℝ} (hdelta : 0 ≤ delta) :
    Real.sqrt (delta / 625) / Real.sqrt 3 ≤
      (Real.sqrt delta / Real.sqrt 3) / 5 := by
  rw [pureWZ2_exact_refined_sqrt hdelta]
  have hsqrt : 0 ≤ Real.sqrt delta := Real.sqrt_nonneg delta
  have hsqrtThree : 0 < Real.sqrt 3 := by positivity
  calc
    Real.sqrt delta / 25 / Real.sqrt 3 ≤
        (Real.sqrt delta / 5) / Real.sqrt 3 := by
      gcongr
      nlinarith
    _ = Real.sqrt delta / Real.sqrt 3 / 5 := by ring

private lemma pureWZ2_unitBallPoint_coord_diff
    (first second : Point2) (coordinate : Fin 2) :
    |(wz1Lemma23UnitBallPoint first) coordinate -
        (wz1Lemma23UnitBallPoint second) coordinate| =
      |first coordinate - second coordinate| / 5 := by
  simp [wz1Lemma23UnitBallPoint]
  rw [show (5 : ℝ)⁻¹ * first coordinate -
      (5 : ℝ)⁻¹ * second coordinate =
        (first coordinate - second coordinate) / 5 by ring]
  rw [abs_div]
  norm_num

/-- The exact terminal graph after a second common `/5` homothety. -/
structure PureWZ2TerminalExactRefinedReadyGraph
    {sigma inputLoss delta stickyLoss eta theoremEta : ℝ} {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {line : PureWZ2HorizontalFixedBinCore window.windowed source.globalGrains.slope}
    {parents : PureWZ2TerminalFixedBinParentData line}
    {selection : PureWZ2TerminalBinParentYSelection parents}
    {residue : PureWZ2TerminalBinParentYResidueData selection}
    {retained : PureWZ2TerminalBinRetainedShadingData residue}
    {sources : PureWZ2TerminalBinSourceFamily retained}
    {band : PureWZ2TerminalBinFixedBandSelection sources}
    {phase : PureWZ2TerminalBinHeightPhaseSelection band}
    {anchored : PureWZ2TerminalBinAnchoredPieceData phase}
    {prep : PureWZ2TerminalBinExactGraphPreparation anchored}
    {graphParents : PureWZ2TerminalExactGraphParentData prep}
    {localCells : PureWZ2TerminalExactLocalCellData (eta := eta) graphParents}
    {preparedGraph : PureWZ2TerminalExactPreparedGraphData localCells}
    {sharp : PureWZ2TerminalExactSharpGeometry preparedGraph}
    (first : PureWZ2TerminalExactReadyGraph
      (theoremEta := theoremEta) sharp) where
  common : WZ1Lemma23UnitBallGraph (delta / 625)
    first.common.F first.common.G₁ first.common.G₁ first.common.H
  ready : WZ1Lemma23Theorem22ReadyGraph
    (delta / 625) theoremEta common
  deltaGraph_eq : ready.deltaGraph = first.ready.deltaGraph / 25
  heightFiberCost_eq : preparedGraph.graph.residue.heightFiberCost = 2

theorem PureWZ2TerminalExactReadyGraph.refineForExactTrapezoid
    {sigma inputLoss delta stickyLoss eta theoremEta : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    {line : PureWZ2HorizontalFixedBinCore
      window.windowed source.globalGrains.slope}
    {parents : PureWZ2TerminalFixedBinParentData line}
    {selection : PureWZ2TerminalBinParentYSelection parents}
    {residue : PureWZ2TerminalBinParentYResidueData selection}
    {retained : PureWZ2TerminalBinRetainedShadingData residue}
    {sources : PureWZ2TerminalBinSourceFamily retained}
    {band : PureWZ2TerminalBinFixedBandSelection sources}
    {phase : PureWZ2TerminalBinHeightPhaseSelection band}
    {anchored : PureWZ2TerminalBinAnchoredPieceData phase}
    {prep : PureWZ2TerminalBinExactGraphPreparation anchored}
    {graphParents : PureWZ2TerminalExactGraphParentData prep}
    {localCells : PureWZ2TerminalExactLocalCellData (eta := eta) graphParents}
    {preparedGraph : PureWZ2TerminalExactPreparedGraphData localCells}
    {sharp : PureWZ2TerminalExactSharpGeometry preparedGraph}
    (first : PureWZ2TerminalExactReadyGraph
      (theoremEta := theoremEta) sharp)
    (hedge :
      Kakeya.realRpowENN
          (wz1Lemma23Theorem22Scale (delta / 625))
          (theoremEta - 3) ≤
        (first.common.H.card : ENNReal))
    (hKatzTao : (4 : ENNReal) ≤
      Kakeya.realRpowENN
        (wz1Lemma23Theorem22Scale (delta / 625)) (-theoremEta)) :
    Nonempty (PureWZ2TerminalExactRefinedReadyGraph first) := by
  have hdelta : 0 < delta := source.extremal.delta_pos
  have hrefined : 0 < delta / 625 := by positivity
  have hcommonEndpoints : first.common.G₂ = first.common.G₁ := by
    rw [first.common.G₂_eq, first.common.G₁_eq]
  have hsupport : ∀ edge ∈ first.common.H,
      edge.1 ∈ first.common.F ∧
        edge.2.1 ∈ first.common.G₁ ∧
          edge.2.2 ∈ first.common.G₁ := by
    intro edge hedgeMem
    have hs := first.common.edge_support edge hedgeMem
    rw [hcommonEndpoints] at hs
    exact hs
  have hFbound : ∀ point ∈ first.common.F, dist point 0 ≤ 2 := by
    intro point hpoint
    exact (first.common.F_unit point hpoint).trans (by norm_num)
  have hGbound : ∀ point ∈ first.common.G₁, dist point 0 ≤ 5 := by
    intro point hpoint
    exact (first.common.G₁_unit point hpoint).trans (by norm_num)
  have htarget := pureWZ2_exact_refined_target_le_fifth hdelta.le
  have hFcoord : ∀ firstPoint ∈ first.common.F,
      ∀ secondPoint ∈ first.common.F, firstPoint ≠ secondPoint →
        Real.sqrt (delta / 625) / Real.sqrt 3 ≤
          |firstPoint 0 - secondPoint 0| := by
    intro firstPoint hfirst secondPoint hsecond hne
    rw [first.common.F_eq] at hfirst hsecond
    rcases Finset.mem_image.mp hfirst with
      ⟨firstSource, hfirstSource, rfl⟩
    rcases Finset.mem_image.mp hsecond with
      ⟨secondSource, hsecondSource, rfl⟩
    have hsourceNe : firstSource ≠ secondSource := by
      intro heq
      exact hne (congr_arg wz1Lemma23UnitBallPoint heq)
    have hsource := sharp.geometry.coordinate_separation.1
      firstSource hfirstSource secondSource hsecondSource hsourceNe
    rw [pureWZ2_unitBallPoint_coord_diff]
    exact htarget.trans
      (div_le_div_of_nonneg_right hsource (by norm_num))
  have hGcoord : ∀ firstPoint ∈ first.common.G₁,
      ∀ secondPoint ∈ first.common.G₁, firstPoint ≠ secondPoint →
        Real.sqrt (delta / 625) / Real.sqrt 3 ≤
          |firstPoint 1 - secondPoint 1| := by
    intro firstPoint hfirst secondPoint hsecond hne
    rw [first.common.G₁_eq] at hfirst hsecond
    rcases Finset.mem_image.mp hfirst with
      ⟨firstSource, hfirstSource, rfl⟩
    rcases Finset.mem_image.mp hsecond with
      ⟨secondSource, hsecondSource, rfl⟩
    have hsourceNe : firstSource ≠ secondSource := by
      intro heq
      exact hne (congr_arg wz1Lemma23UnitBallPoint heq)
    rw [wz1Lemma23CommonLocalVertices] at hfirstSource hsecondSource
    rcases Finset.mem_image.mp hfirstSource with
      ⟨firstCell, hfirstCell, rfl⟩
    rcases Finset.mem_image.mp hsecondSource with
      ⟨secondCell, hsecondCell, rfl⟩
    have hsource := wz1Lemma23_local_points_coordinate_separated
      sharp.sharp.selectedLocal.g preparedGraph.graph.residue.y_separated
      hfirstCell hsecondCell hsourceNe
    rw [pureWZ2_unitBallPoint_coord_diff]
    exact htarget.trans
      (div_le_div_of_nonneg_right
        ((div_le_self (Real.sqrt_nonneg delta)
          ((Real.one_le_sqrt).2 (by norm_num))).trans hsource)
        (by norm_num))
  rcases wz1_lemma23_unit_ball_graph hrefined hsupport
      hFbound hGbound hGbound hFcoord hGcoord hGcoord with ⟨common⟩
  have hedgeCommon : Kakeya.realRpowENN
      (wz1Lemma23Theorem22Scale (delta / 625)) (theoremEta - 3) ≤
        (common.H.card : ENNReal) := by
    rw [common.edge_card]
    exact hedge
  let deltaGraph := wz1Lemma23Theorem22Scale (delta / 625)
  have hdeltaGraph : 0 < deltaGraph := by
    dsimp only [deltaGraph, wz1Lemma23Theorem22Scale]
    positivity
  have hthresholdPos :
      0 < Kakeya.realRpowENN deltaGraph (theoremEta - 3) := by
    apply ENNReal.ofReal_pos.mpr
    exact Real.rpow_pos_of_pos hdeltaGraph _
  have hHcardPos : 0 < (common.H.card : ENNReal) :=
    hthresholdPos.trans_le hedgeCommon
  have hHnonempty : common.H.Nonempty := by
    apply Finset.card_pos.mp
    exact_mod_cast hHcardPos
  rcases hHnonempty with ⟨edge, hedgeMem⟩
  have hs := common.edge_support edge hedgeMem
  let ready : WZ1Lemma23Theorem22ReadyGraph
      (delta / 625) theoremEta common :=
    { deltaGraph := deltaGraph
      deltaGraph_eq := rfl
      deltaGraph_pos := hdeltaGraph
      F_nonempty := ⟨edge.1, hs.1⟩
      G₁_nonempty := ⟨edge.2.1, hs.2.1⟩
      G₂_nonempty := ⟨edge.2.2, hs.2.2⟩
      H_nonempty := ⟨edge, hedgeMem⟩
      F_katzTao := common.F_katzTao.mono_const hKatzTao
      G₁_katzTao := common.G₁_katzTao.mono_const hKatzTao
      G₂_katzTao := common.G₂_katzTao.mono_const hKatzTao
      edge_threshold := hedgeCommon }
  have hscale : ready.deltaGraph = first.ready.deltaGraph / 25 := by
    rw [show ready.deltaGraph = wz1Lemma23Theorem22Scale (delta / 625) by rfl,
      first.ready.deltaGraph_eq]
    simp only [wz1Lemma23Theorem22Scale,
      pureWZ2_exact_refined_sqrt hdelta.le]
    ring
  exact ⟨{
    common := common
    ready := ready
    deltaGraph_eq := hscale
    heightFiberCost_eq := first.heightFiberCost_eq }⟩

end Kakeya.Assouad
