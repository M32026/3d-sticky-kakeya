import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalPopularReadyGraph

/-!
# Second common normalization for the terminal outer-popular graph

The reusable core below depends only on a common-endpoint unit-ball graph,
its ready certificate, and coordinate separation of its two vertex classes.
The terminal specialization derives those coordinate bounds from the actual
volume-popular residue and retains the complete graph provenance separately.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

private lemma pureWZ2_popular_refined_sqrt
    {rho : ℝ} (hrho : 0 ≤ rho) :
    Real.sqrt (rho / 625) = Real.sqrt rho / 25 := by
  rw [Real.sqrt_div hrho]
  norm_num

private lemma pureWZ2_popular_refined_target_le
    {rho : ℝ} (hrho : 0 ≤ rho) :
    Real.sqrt (rho / 625) / Real.sqrt 3 ≤
      Real.sqrt rho / (5 * Real.sqrt 3) := by
  rw [pureWZ2_popular_refined_sqrt hrho]
  have hsqrt : 0 ≤ Real.sqrt rho := Real.sqrt_nonneg rho
  have hsqrtThree : 0 < Real.sqrt 3 := by positivity
  calc
    Real.sqrt rho / 25 / Real.sqrt 3 ≤
        (Real.sqrt rho / 5) / Real.sqrt 3 := by
      gcongr
      nlinarith
    _ = Real.sqrt rho / (5 * Real.sqrt 3) := by ring

/-- A second common `/5` normalization of an already common-endpoint ready
graph.  The edge set is unchanged up to the common injective homothety. -/
structure PureWZ2CommonRefinedReadyGraph
    (rho theoremEta : ℝ)
    {sourceF sourceG : DiscreteSet 2}
    {sourceH : Finset (Point2 × Point2 × Point2)}
    (first : WZ1Lemma23UnitBallGraph
      rho sourceF sourceG sourceG sourceH)
    (firstReady : WZ1Lemma23Theorem22ReadyGraph
      rho theoremEta first) where
  common : WZ1Lemma23UnitBallGraph (rho / 625)
    first.F first.G₁ first.G₁ first.H
  ready : WZ1Lemma23Theorem22ReadyGraph
    (rho / 625) theoremEta common
  deltaGraph_eq : ready.deltaGraph = firstReady.deltaGraph / 25

theorem pureWZ2_refine_common_ready_graph
    {rho theoremEta : ℝ}
    {sourceF sourceG : DiscreteSet 2}
    {sourceH : Finset (Point2 × Point2 × Point2)}
    (first : WZ1Lemma23UnitBallGraph
      rho sourceF sourceG sourceG sourceH)
    (firstReady : WZ1Lemma23Theorem22ReadyGraph
      rho theoremEta first)
    (hrho : 0 < rho)
    (hFcoord : ∀ firstPoint ∈ first.F,
      ∀ secondPoint ∈ first.F, firstPoint ≠ secondPoint →
        Real.sqrt rho / (5 * Real.sqrt 3) ≤
          |firstPoint 0 - secondPoint 0|)
    (hGcoord : ∀ firstPoint ∈ first.G₁,
      ∀ secondPoint ∈ first.G₁, firstPoint ≠ secondPoint →
        Real.sqrt rho / (5 * Real.sqrt 3) ≤
          |firstPoint 1 - secondPoint 1|)
    (hedge : Kakeya.realRpowENN
        (wz1Lemma23Theorem22Scale (rho / 625))
        (theoremEta - 3) ≤ (first.H.card : ENNReal))
    (hKatzTao : (4 : ENNReal) ≤
      Kakeya.realRpowENN
        (wz1Lemma23Theorem22Scale (rho / 625)) (-theoremEta)) :
    Nonempty (PureWZ2CommonRefinedReadyGraph
      rho theoremEta first firstReady) := by
  have hrefined : 0 < rho / 625 := by positivity
  have hsupport : ∀ edge ∈ first.H,
      edge.1 ∈ first.F ∧ edge.2.1 ∈ first.G₁ ∧ edge.2.2 ∈ first.G₁ :=
    by
      intro edge hedgeMem
      have hs := first.edge_support edge hedgeMem
      rw [first.G₂_eq, first.G₁_eq] at hs
      simpa only [first.G₁_eq] using hs
  have hFbound : ∀ point ∈ first.F, dist point 0 ≤ 2 := by
    intro point hpoint
    exact (first.F_unit point hpoint).trans (by norm_num)
  have hGbound : ∀ point ∈ first.G₁, dist point 0 ≤ 5 := by
    intro point hpoint
    exact (first.G₁_unit point hpoint).trans (by norm_num)
  have htarget := pureWZ2_popular_refined_target_le hrho.le
  rcases wz1_lemma23_unit_ball_graph hrefined hsupport hFbound hGbound
      hGbound
      (fun firstPoint hfirst secondPoint hsecond hne =>
        htarget.trans (hFcoord firstPoint hfirst secondPoint hsecond hne))
      (fun firstPoint hfirst secondPoint hsecond hne =>
        htarget.trans (hGcoord firstPoint hfirst secondPoint hsecond hne))
      (fun firstPoint hfirst secondPoint hsecond hne =>
        htarget.trans (hGcoord firstPoint hfirst secondPoint hsecond hne)) with
    ⟨common⟩
  have hedgeCommon : Kakeya.realRpowENN
      (wz1Lemma23Theorem22Scale (rho / 625)) (theoremEta - 3) ≤
        (common.H.card : ENNReal) := by
    rw [common.edge_card]
    exact hedge
  let deltaGraph := wz1Lemma23Theorem22Scale (rho / 625)
  have hdeltaGraph : 0 < deltaGraph := by
    dsimp only [deltaGraph, wz1Lemma23Theorem22Scale]
    positivity
  have hthresholdPos :
      0 < Kakeya.realRpowENN deltaGraph (theoremEta - 3) := by
    apply ENNReal.ofReal_pos.mpr
    exact Real.rpow_pos_of_pos hdeltaGraph _
  have hHnonempty : common.H.Nonempty := by
    apply Finset.card_pos.mp
    exact_mod_cast hthresholdPos.trans_le hedgeCommon
  rcases hHnonempty with ⟨edge, hedgeMem⟩
  have hs := common.edge_support edge hedgeMem
  let ready : WZ1Lemma23Theorem22ReadyGraph
      (rho / 625) theoremEta common := {
    deltaGraph := deltaGraph
    deltaGraph_eq := rfl
    deltaGraph_pos := hdeltaGraph
    F_nonempty := ⟨edge.1, hs.1⟩
    G₁_nonempty := ⟨edge.2.1, hs.2.1⟩
    G₂_nonempty := ⟨edge.2.2, hs.2.2⟩
    H_nonempty := ⟨edge, hedgeMem⟩
    F_katzTao := common.F_katzTao.mono_const hKatzTao
    G₁_katzTao := common.G₁_katzTao.mono_const hKatzTao
    G₂_katzTao := common.G₂_katzTao.mono_const hKatzTao
    edge_threshold := hedgeCommon
  }
  have hscale : ready.deltaGraph = firstReady.deltaGraph / 25 := by
    rw [show ready.deltaGraph = wz1Lemma23Theorem22Scale (rho / 625) by rfl,
      firstReady.deltaGraph_eq]
    simp only [wz1Lemma23Theorem22Scale,
      pureWZ2_popular_refined_sqrt hrho.le]
    ring
  exact ⟨{ common := common, ready := ready, deltaGraph_eq := hscale }⟩

private lemma pureWZ2_popular_unitBallPoint_coord_diff
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

theorem PureWZ2TerminalPopularReadyGraph.refineForExactTrapezoid
    {sigma inputLoss delta stickyLoss eta theoremEta : ℝ}
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
    {localCells : PureWZ2TerminalPopularLocalCellData
      (eta := eta) graphParents}
    {preparedGraph : PureWZ2TerminalPopularPreparedGraphData localCells}
    {sharp : PureWZ2TerminalPopularSharpGeometry preparedGraph}
    (first : PureWZ2TerminalPopularReadyGraph
      (theoremEta := theoremEta) sharp)
    (hedge : Kakeya.realRpowENN
        (wz1Lemma23Theorem22Scale (delta / 625))
        (theoremEta - 3) ≤ (first.common.H.card : ENNReal))
    (hKatzTao : (4 : ENNReal) ≤
      Kakeya.realRpowENN
        (wz1Lemma23Theorem22Scale (delta / 625)) (-theoremEta)) :
    Nonempty (PureWZ2CommonRefinedReadyGraph
      delta theoremEta first.common first.ready) := by
  have hFcoord : ∀ firstPoint ∈ first.common.F,
      ∀ secondPoint ∈ first.common.F, firstPoint ≠ secondPoint →
        Real.sqrt delta / (5 * Real.sqrt 3) ≤
          |firstPoint 0 - secondPoint 0| := by
    intro firstPoint hfirst secondPoint hsecond hne
    rw [first.common.F_eq] at hfirst hsecond
    rcases Finset.mem_image.mp hfirst with ⟨firstSource, hfirstSource, rfl⟩
    rcases Finset.mem_image.mp hsecond with ⟨secondSource, hsecondSource, rfl⟩
    have hsourceNe : firstSource ≠ secondSource := by
      intro heq
      exact hne (congr_arg wz1Lemma23UnitBallPoint heq)
    rw [pureWZ2_popular_unitBallPoint_coord_diff]
    rw [show Real.sqrt delta / (5 * Real.sqrt 3) =
        (Real.sqrt delta / Real.sqrt 3) / 5 by ring]
    exact div_le_div_of_nonneg_right
      (sharp.geometry.coordinate_separation.1
        firstSource hfirstSource secondSource hsecondSource hsourceNe)
      (by norm_num : (0 : ℝ) ≤ 5)
  have hGcoord : ∀ firstPoint ∈ first.common.G₁,
      ∀ secondPoint ∈ first.common.G₁, firstPoint ≠ secondPoint →
        Real.sqrt delta / (5 * Real.sqrt 3) ≤
          |firstPoint 1 - secondPoint 1| := by
    intro firstPoint hfirst secondPoint hsecond hne
    rw [first.common.G₁_eq] at hfirst hsecond
    rcases Finset.mem_image.mp hfirst with ⟨firstSource, hfirstSource, rfl⟩
    rcases Finset.mem_image.mp hsecond with ⟨secondSource, hsecondSource, rfl⟩
    have hsourceNe : firstSource ≠ secondSource := by
      intro heq
      exact hne (congr_arg wz1Lemma23UnitBallPoint heq)
    rw [wz1Lemma23CommonLocalVertices] at hfirstSource hsecondSource
    rcases Finset.mem_image.mp hfirstSource with
      ⟨firstCell, hfirstCell, rfl⟩
    rcases Finset.mem_image.mp hsecondSource with
      ⟨secondCell, hsecondCell, rfl⟩
    rw [pureWZ2_popular_unitBallPoint_coord_diff]
    rw [show Real.sqrt delta / (5 * Real.sqrt 3) =
        (Real.sqrt delta / Real.sqrt 3) / 5 by ring]
    exact div_le_div_of_nonneg_right
      ((div_le_self (Real.sqrt_nonneg delta)
        ((Real.one_le_sqrt).2 (by norm_num : (1 : ℝ) ≤ 3))).trans
          (wz1Lemma23_local_points_coordinate_separated
            sharp.sharp.selectedLocal.g
            preparedGraph.graph.residue.y_separated
            hfirstCell hsecondCell hsourceNe))
      (by norm_num : (0 : ℝ) ≤ 5)
  exact pureWZ2_refine_common_ready_graph first.common first.ready
    source.extremal.delta_pos hFcoord hGcoord hedge hKatzTao

end Kakeya.Assouad
