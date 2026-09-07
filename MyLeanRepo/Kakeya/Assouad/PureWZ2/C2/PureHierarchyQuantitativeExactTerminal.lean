import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PureHierarchyExactTerminalAssembly

/-!
# Quantitative exact-terminal hierarchy data

The mixed exact-terminal route previously retained the terminal geometry but
forgot the constant-multiplicity and indexed-mass receipts before the
Corollary-5.6 popularity step.  This file adds parallel wrappers around the
existing compatibility records.  The underlying exact-terminal and mixed
records are unchanged.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

/-- An exact terminal level together with the two quantitative facts used by
the later popularity argument.  The density exponent is kept explicit because
it is chosen by the outer terminal schedule. -/
structure PureWZ2QuantitativeExactTerminalLevelData
    {sigma inputLoss delta : ℝ}
    (source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta)
    (outputLoss densityLoss : ℝ) where
  terminal : PureWZ2ExactTerminalLevelData source outputLoss
  multiplicity : ℕ
  multiplicity_pos : 0 < multiplicity
  constant_multiplicity :
    terminal.shading.HasConstantMultiplicity multiplicity (2 * multiplicity)
  mass_lower :
    Kakeya.realRpowENN delta densityLoss *
        (wz1PaperBodyFamily source.family).mass ≤
      terminal.shading.mass

/-- The concrete exact-rich terminal output supplies the quantitative wrapper
once the already scheduled height-layer mass lower bound has been paid. -/
theorem PureWZ2TerminalExactRichSetTrapezoid.toQuantitativeExactTerminalLevel
    {sigma inputLoss delta stickyLoss eta theoremEta outputLoss densityLoss : ℝ}
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
    {first : PureWZ2TerminalExactReadyGraph
      (theoremEta := theoremEta) sharp}
    {ready : PureWZ2TerminalExactRefinedReadyGraph first}
    {rich : PureWZ2TerminalExactAlternativeAHeightData ready outputLoss}
    {weighted : PureWZ2TerminalExactRichHeightCellData rich}
    (data : PureWZ2TerminalExactRichSetTrapezoid weighted)
    (hinputOutput : inputLoss ≤ outputLoss)
    (hvolume : Kakeya.realRpowENN delta (sigma + outputLoss) ≤
      (rich.heightIndices.card : ENNReal) *
        preparedGraph.heightPopular.layerMass)
    (hmass : Kakeya.realRpowENN delta densityLoss *
        (wz1PaperBodyFamily source.family).mass ≤
      (rich.heightIndices.card : ENNReal) *
        preparedGraph.heightPopular.layerMass) :
    Nonempty (PureWZ2QuantitativeExactTerminalLevelData
      source outputLoss densityLoss) := by
  have hsubSource : PureWZ2PaperIsSubshading data.shading source.shading :=
    fun index => (data.subshading index).trans (retained.subshading index)
  have hconstant : Kakeya.realRpowENN delta (-inputLoss) ≤
      Kakeya.realRpowENN delta (-outputLoss) :=
    pureWZ2_grain_constant_mono source.extremal.delta_pos
      source.extremal.delta_le_one hinputOutput
  have hconstantTop : Kakeya.realRpowENN delta (-outputLoss) ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  let localGrains := source.localGrains.restrictWithConstant
    hsubSource hconstant hconstantTop
  let globalGrains := source.globalGrains.restrict
    hsubSource hconstant hconstantTop
  let trapezoids : Finset WZ1VerticalTrapezoid := {data.trapezoid}
  let terminalLevel : PureWZ2ExactTerminalLevelData source outputLoss := {
    shading := data.shading
    subshading := hsubSource
    volume_lower := hvolume.trans data.volume_lower
    localGrains := localGrains
    planeMap_vertical_bound := by
      intro point
      exact source.planeMap_vertical_bound
        ⟨point, hsubSource.union_subset point.property⟩
    sourceGlobalGrains := globalGrains
    source_slope_eq := rfl
    trapezoids := trapezoids
    trapezoids_nonempty := by simp [trapezoids]
    height_eq := by
      intro candidate hcandidate
      simp only [trapezoids, Finset.mem_singleton] at hcandidate
      subst candidate
      exact data.height_eq
    slope_bound := by
      intro candidate hcandidate
      simp only [trapezoids, Finset.mem_singleton] at hcandidate
      subst candidate
      exact data.slope_bound
    length_bounds := by
      intro candidate hcandidate
      simp only [trapezoids, Finset.mem_singleton] at hcandidate
      subst candidate
      exact data.length_bounds
    separated_cores := by
      intro firstCandidate hfirst secondCandidate hsecond hne
      simp only [trapezoids, Finset.mem_singleton] at hfirst hsecond
      exact False.elim (hne (hfirst.trans hsecond.symm))
    slope_approximation := by
      intro candidate hcandidate z hz hslice
      simp only [trapezoids, Finset.mem_singleton] at hcandidate
      subst candidate
      exact data.slope_approximation z hz hslice
    active_height_coverage := by
      intro z _hz hslice
      exact ⟨data.trapezoid, by simp [trapezoids],
        data.active_height_coverage z hslice⟩ }
  have honeMultiplicity : (1 : ENNReal) ≤ terminalSource.multiplicity := by
    exact_mod_cast terminalSource.multiplicity_pos
  have hvolumeMass : volume data.shading.union ≤ data.shading.mass := by
    calc
      volume data.shading.union = 1 * volume data.shading.union := by simp
      _ ≤ (terminalSource.multiplicity : ENNReal) *
          volume data.shading.union := by gcongr
      _ ≤ data.shading.mass := data.multiplicity_mass_lower
  exact ⟨{
    terminal := terminalLevel
    multiplicity := terminalSource.multiplicity
    multiplicity_pos := terminalSource.multiplicity_pos
    constant_multiplicity := by
      change data.shading.HasConstantMultiplicity
        terminalSource.multiplicity (2 * terminalSource.multiplicity)
      exact data.constant_multiplicity
    mass_lower := by
      change Kakeya.realRpowENN delta densityLoss *
          (wz1PaperBodyFamily source.family).mass ≤ data.shading.mass
      exact hmass.trans (data.volume_lower.trans hvolumeMass) }⟩

/-- The raw mixed hierarchy together with the exact terminal quantitative
receipts.  Geometry stays in the original compatibility record. -/
structure PureWZ2QuantitativeMixedRawHierarchyData
    {sigma inputLoss delta : ℝ}
    (source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta)
    (finalLoss hierarchyLoss densityLoss : ℝ) where
  mixed : PureWZ2MixedRawHierarchyData source finalLoss hierarchyLoss
  multiplicity : ℕ
  multiplicity_pos : 0 < multiplicity
  constant_multiplicity :
    mixed.shading.HasConstantMultiplicity multiplicity (2 * multiplicity)
  mass_lower :
    Kakeya.realRpowENN delta densityLoss *
        (wz1PaperBodyFamily source.family).mass ≤ mixed.shading.mass

/-- Append one quantitative exact terminal level without changing the ordinary
prefix or its dependent hierarchy-depth equality. -/
theorem PureWZ2OrdinaryHierarchyPrefixData.appendQuantitativeExactTerminalWithLevelCount
    {sigma inputLoss delta finalLoss hierarchyLoss densityLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {N : ℕ}
    (ordinary : PureWZ2OrdinaryHierarchyPrefixData source hierarchyLoss N)
    (terminal : PureWZ2QuantitativeExactTerminalLevelData
      source finalLoss densityLoss)
    (hfinalHierarchy : finalLoss ≤ hierarchyLoss) :
    Nonempty { mixed : PureWZ2QuantitativeMixedRawHierarchyData
        source finalLoss hierarchyLoss densityLoss //
      mixed.mixed.levelCount = N } := by
  rcases ordinary.appendExactTerminalWithLevelCountAndShading terminal.terminal
      hfinalHierarchy with ⟨mixed⟩
  exact ⟨⟨{
    mixed := mixed.1
    multiplicity := terminal.multiplicity
    multiplicity_pos := terminal.multiplicity_pos
    constant_multiplicity := by
      rw [mixed.2.2]
      exact terminal.constant_multiplicity
    mass_lower := by
      rw [mixed.2.2]
      exact terminal.mass_lower }, mixed.2.1⟩⟩

end Kakeya.Assouad

end
