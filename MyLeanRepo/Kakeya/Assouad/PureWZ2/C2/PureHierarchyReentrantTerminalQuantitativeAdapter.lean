import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PureHierarchyQuantitativeExactTerminal
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PureHierarchyReentrantTerminalPaperOrderProducer
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05V4RichEndpointTerminalCore

/-!
# Same-witness quantitative adapter for the reentrant terminal

The paper-order producer already selects one concrete mod-16 residue by the
indexed mass of its completed source-height block shadings.  The quantitative
receipt below is deliberately indexed by that concrete residue: its
multiplicity band and source-body indexed-mass lower bound therefore concern
the same `PureWZ2TerminalPopularBlockResidueData.finalShading`.

The fixed-runtime package is to be filled immediately after
`buildGoodBlockFamily` and `selectResidue` in the actual invocation.  It is not
a producer for an arbitrary terminal and it does not permit a second terminal
or residue choice.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

namespace PureWZ2TerminalPopularBlockResidueData

variable
    {sigma inputLoss delta stickyLoss eta theoremEta outputLoss localMassLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {good : PureWZ2TerminalPopularGoodBlockFamilyData
      (eta := eta) (theoremEta := theoremEta)
      (outputLoss := outputLoss) (localMassLoss := localMassLoss) prepared}

/-- The zero-extension preserves the constant-multiplicity band on the exact
final shading chosen by the residue. -/
theorem finalShading_constant_multiplicity
    (data : PureWZ2TerminalPopularBlockResidueData good) :
    data.finalShading.HasConstantMultiplicity
      terminalSource.multiplicity (2 * terminalSource.multiplicity) :=
  data.zeroExtension.constantMultiplicity
    data.selectedShading_constant_multiplicity

/-- The two quantitative facts saved at the concrete residue-construction
point.  Both fields are definitionally about `data.finalShading`. -/
structure QuantitativeSameWitnessReceipt
    (data : PureWZ2TerminalPopularBlockResidueData good)
    (densityLoss : ℝ) where
  constant_multiplicity :
    data.finalShading.HasConstantMultiplicity
      terminalSource.multiplicity (2 * terminalSource.multiplicity)
  source_body_mass_lower :
    Kakeya.realRpowENN delta densityLoss *
        (wz1PaperBodyFamily source.family).mass ≤
      data.finalShading.mass

/-- Save the indexed-mass leaf together with the canonical multiplicity band
as soon as the concrete mass-selected residue has been constructed. -/
theorem quantitativeSameWitnessReceipt
    (data : PureWZ2TerminalPopularBlockResidueData good)
    (densityLoss : ℝ)
    (hmass :
      Kakeya.realRpowENN delta densityLoss *
          (wz1PaperBodyFamily source.family).mass ≤
        data.finalShading.mass) :
    QuantitativeSameWitnessReceipt data densityLoss where
  constant_multiplicity := data.finalShading_constant_multiplicity
  source_body_mass_lower := hmass

/-- Repackage the concrete paper-order residue as a quantitative exact
terminal.  The exact geometry and both quantitative fields use the same
`data.finalShading`. -/
theorem toQuantitativeExactTerminalLevel
    (data : PureWZ2TerminalPopularBlockResidueData good)
    {densityLoss : ℝ}
    (quantitative : QuantitativeSameWitnessReceipt data densityLoss)
    (hinputOutput : inputLoss ≤ outputLoss)
    (hscalar :
      32 * good.sourceMassCost *
          Kakeya.realRpowENN delta (sigma + outputLoss) ≤
        Kakeya.realRpowENN delta localMassLoss *
          Kakeya.realRpowENN delta (sigma + stickyLoss)) :
    Nonempty (PureWZ2QuantitativeExactTerminalLevelData
      source outputLoss densityLoss) := by
  have hsub := data.finalShading_subshading
  have hvolume := data.finalShading_volume_lower hscalar
  have hconstant : Kakeya.realRpowENN delta (-inputLoss) ≤
      Kakeya.realRpowENN delta (-outputLoss) :=
    pureWZ2_grain_constant_mono source.extremal.delta_pos
      source.extremal.delta_le_one hinputOutput
  have hconstantTop : Kakeya.realRpowENN delta (-outputLoss) ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  let localGrains :=
    source.localGrains.restrictWithConstant hsub hconstant hconstantTop
  let globalGrains :=
    source.globalGrains.restrict hsub hconstant hconstantTop
  letI := Classical.decEq WZ1VerticalTrapezoid
  let trapezoids : Finset WZ1VerticalTrapezoid :=
    data.selected.image fun index =>
      (good.output index).exactTrapezoid.trapezoid
  let terminalLevel : PureWZ2ExactTerminalLevelData source outputLoss := {
    shading := data.finalShading
    subshading := hsub
    volume_lower := hvolume
    localGrains := localGrains
    planeMap_vertical_bound := by
      intro point
      exact source.planeMap_vertical_bound
        ⟨point, hsub.union_subset point.property⟩
    sourceGlobalGrains := globalGrains
    source_slope_eq := rfl
    trapezoids := trapezoids
    trapezoids_nonempty := data.selected_nonempty.image _
    height_eq := by
      intro trapezoid htrapezoid
      rcases Finset.mem_image.mp htrapezoid with
        ⟨index, _hindex, rfl⟩
      exact (good.output index).exactTrapezoid.height_eq
    slope_bound := by
      intro trapezoid htrapezoid
      rcases Finset.mem_image.mp htrapezoid with
        ⟨index, _hindex, rfl⟩
      exact (good.output index).exactTrapezoid.slope_bound
    length_bounds := by
      intro trapezoid htrapezoid
      rcases Finset.mem_image.mp htrapezoid with
        ⟨index, _hindex, rfl⟩
      exact (good.output index).exactTrapezoid.length_bounds
    separated_cores := by
      intro trapezoid htrapezoid other hother hne
      rcases Finset.mem_image.mp htrapezoid with
        ⟨first, hfirst, rfl⟩
      rcases Finset.mem_image.mp hother with
        ⟨second, hsecond, rfl⟩
      have hindexNe : first ≠ second := by
        intro heq
        subst second
        exact hne rfl
      exact data.separated_cores first second hfirst hsecond hindexNe
    slope_approximation := by
      intro trapezoid htrapezoid z hz hslice
      rcases Finset.mem_image.mp htrapezoid with
        ⟨target, htarget, rfl⟩
      rw [data.finalShading_union_eq] at hslice
      rcases Set.nonempty_iff_ne_empty.mpr hslice with ⟨point, hpoint⟩
      rcases (data.mem_selectedShading_union_iff point).mp hpoint.1 with
        ⟨sourceIndex, hsourceIndex, selectedIndex, hlocal⟩
      have hlocal' := hlocal
      rw [(good.output sourceIndex).chain.outerHeightLift.carrier_eq] at hlocal'
      rcases hlocal' with ⟨_hsource, _hregion⟩
      have hsourceSlice : horizontalSlice
          (good.blockShading sourceIndex).union z ≠ ∅ :=
        Set.nonempty_iff_ne_empty.mp
          ⟨point, ⟨selectedIndex, hlocal⟩, hpoint.2⟩
      have hsourceCore :=
        (good.output sourceIndex).exactTrapezoid.active_height_coverage
          z hsourceSlice
      by_cases heq :
          (good.output target).exactTrapezoid.trapezoid =
            (good.output sourceIndex).exactTrapezoid.trapezoid
      · rw [heq]
        change |source.globalGrains.slope z -
          (good.output sourceIndex).exactTrapezoid.trapezoid.affine z| ≤ delta
        exact
          (good.output sourceIndex).exactTrapezoid.slope_approximation
            z hsourceCore hsourceSlice
      · have hindexNe : target ≠ sourceIndex := by
          intro hindex
          subst sourceIndex
          exact heq rfl
        have hsep := data.separated_cores target sourceIndex
          htarget hsourceIndex hindexNe z hz z hsourceCore
        exact False.elim ((not_le_of_gt
          (Real.sqrt_pos.mpr source.extremal.delta_pos)) (by simpa using hsep))
    active_height_coverage := by
      intro z _hz hslice
      rw [data.finalShading_union_eq] at hslice
      rcases Set.nonempty_iff_ne_empty.mpr hslice with ⟨point, hpoint⟩
      rcases (data.mem_selectedShading_union_iff point).mp hpoint.1 with
        ⟨index, hindex, selectedIndex, hlocal⟩
      have hlocalSlice : horizontalSlice
          (good.blockShading index).union z ≠ ∅ :=
        Set.nonempty_iff_ne_empty.mp
          ⟨point, ⟨selectedIndex, hlocal⟩, hpoint.2⟩
      exact ⟨(good.output index).exactTrapezoid.trapezoid,
        Finset.mem_image.mpr ⟨index, hindex, rfl⟩,
        (good.output index).exactTrapezoid.active_height_coverage
          z hlocalSlice⟩ }
  exact ⟨{
    terminal := terminalLevel
    multiplicity := terminalSource.multiplicity
    multiplicity_pos := terminalSource.multiplicity_pos
    constant_multiplicity := quantitative.constant_multiplicity
    mass_lower := quantitative.source_body_mass_lower }⟩

end PureWZ2TerminalPopularBlockResidueData

namespace PureWZ2QuantitativeExactTerminalLevelData

/-- Weakening the terminal loss leaves the exact shading and both quantitative
receipts unchanged. -/
noncomputable def mono_loss
    {sigma inputLoss delta firstLoss secondLoss densityLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    (data : PureWZ2QuantitativeExactTerminalLevelData
      source firstLoss densityLoss)
    (hloss : firstLoss ≤ secondLoss) :
    PureWZ2QuantitativeExactTerminalLevelData
      source secondLoss densityLoss where
  terminal := data.terminal.mono_loss hloss
  multiplicity := data.multiplicity
  multiplicity_pos := data.multiplicity_pos
  constant_multiplicity := by
    simpa using data.constant_multiplicity
  mass_lower := by
    simpa using data.mass_lower

end PureWZ2QuantitativeExactTerminalLevelData

namespace PureWZ2QuantitativeNormalizedHierarchyOutput

/-- Weaken only the quantitative density exponent on one already normalized
hierarchy.  The source, hierarchy, selected shading, multiplicity, and
normalization witnesses are definitionally unchanged. -/
noncomputable def mono_densityLoss
    {sigma workLoss sourceDelta : ℝ}
    (data : PureWZ2QuantitativeNormalizedHierarchyOutput
      sigma workLoss sourceDelta)
    (nextDensityLoss : ℝ)
    (hloss : data.densityLoss ≤ nextDensityLoss) :
    PureWZ2QuantitativeNormalizedHierarchyOutput
      sigma workLoss sourceDelta where
  densityLoss := nextDensityLoss
  quantitativeInputLoss := data.quantitativeInputLoss
  inputLoss_le_workLoss := data.inputLoss_le_workLoss
  quantitativeSource := data.quantitativeSource
  quantitativeHierarchyLoss := data.quantitativeHierarchyLoss
  hierarchyLoss_pos := data.hierarchyLoss_pos
  quantitative := {
    hierarchy := data.quantitative.hierarchy
    multiplicity := data.quantitative.multiplicity
    multiplicity_pos := data.quantitative.multiplicity_pos
    pointMultiplicity_upper := data.quantitative.pointMultiplicity_upper
    mass_retention := by
      calc
        ENNReal.ofReal (1 / 6) *
              (Kakeya.realRpowENN sourceDelta nextDensityLoss *
                (wz1PaperBodyFamily data.quantitativeSource.family).mass) ≤
            ENNReal.ofReal (1 / 6) *
              (Kakeya.realRpowENN sourceDelta data.densityLoss *
                (wz1PaperBodyFamily data.quantitativeSource.family).mass) := by
          gcongr
          exact realRpowENN_antitone
            data.quantitativeSource.extremal.delta_pos
            data.quantitativeSource.extremal.delta_le_one hloss
        _ ≤ data.quantitative.hierarchy.shading.mass :=
          data.quantitative.mass_retention }
  hierarchyLoss_upper := data.hierarchyLoss_upper
  normalized := data.normalized
  inputLoss_eq := data.inputLoss_eq
  source_eq := data.source_eq
  hierarchyLoss_eq := data.hierarchyLoss_eq
  hierarchy_eq := data.hierarchy_eq
  normalized_mass_retention := by
    calc
      ENNReal.ofReal (1 / 6) *
            (Kakeya.realRpowENN sourceDelta nextDensityLoss *
              (wz1PaperBodyFamily data.normalized.source.family).mass) ≤
          ENNReal.ofReal (1 / 6) *
            (Kakeya.realRpowENN sourceDelta data.densityLoss *
              (wz1PaperBodyFamily data.normalized.source.family).mass) := by
        gcongr
        exact realRpowENN_antitone data.normalized.source.extremal.delta_pos
          data.normalized.source.extremal.delta_le_one hloss
      _ ≤ data.normalized.hierarchy.shading.mass :=
        data.normalized_mass_retention

@[simp] theorem mono_densityLoss_densityLoss
    {sigma workLoss sourceDelta : ℝ}
    (data : PureWZ2QuantitativeNormalizedHierarchyOutput
      sigma workLoss sourceDelta)
    (nextDensityLoss : ℝ)
    (hloss : data.densityLoss ≤ nextDensityLoss) :
    (data.mono_densityLoss nextDensityLoss hloss).densityLoss =
      nextDensityLoss := rfl

end PureWZ2QuantitativeNormalizedHierarchyOutput

namespace PureWZ2QuantitativeMixedRawHierarchyData

/-- The quantitative normalization theorem with the density exponent retained
as an explicit result equality.  This prevents downstream P6 scheduling from
having to recover an implementation detail of the existential output. -/
theorem toQuantitativeNormalizedHierarchyOutputWithDensityEq
    {sigma inputLoss sourceDelta finalLoss hierarchyLoss workLoss densityLoss : ℝ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss sourceDelta}
    (data : PureWZ2QuantitativeMixedRawHierarchyData
      source finalLoss hierarchyLoss densityLoss)
    (hinputHierarchy : inputLoss ≤ hierarchyLoss)
    (hhierarchyWork : hierarchyLoss ≤ workLoss)
    (hbridge : PureWZ2PaperADBridgeStatement)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hhierarchyLoss : 0 < hierarchyLoss)
    (hfinalHierarchy : finalLoss ≤ hierarchyLoss)
    (hfinalLevelZero : finalLoss ≤
      hierarchyLoss / (4 * (data.mixed.levelCount : ℝ)))
    (hdeltaStrict : sourceDelta < 1)
    (hgeometric : Real.rpow sourceDelta
      (hierarchyLoss / (data.mixed.levelCount : ℝ)) < 1 / 9)
    (hlevelZero :
      pureWZ2HierarchySlabConstant sourceDelta sigma finalLoss *
          ENNReal.ofReal (12 * Real.rpow sourceDelta
            (hierarchyLoss / (data.mixed.levelCount : ℝ))) <
        Kakeya.realRpowENN sourceDelta
          (sigma + hierarchyLoss / (4 * (data.mixed.levelCount : ℝ))))
    (hremoved :
      pureWZ2HierarchySlabConstant sourceDelta sigma finalLoss *
          ENNReal.ofReal
            (12 * ∑ level : Fin data.mixed.levelCount,
              Real.rpow
                (wz1Corollary26Scale sourceDelta
                  data.mixed.levelCount level) hierarchyLoss) ≤
        ENNReal.ofReal (1 / 3) *
          MeasureTheory.volume data.mixed.shading.union)
    (hfinalVolume :
      Kakeya.realRpowENN sourceDelta (sigma + hierarchyLoss) <
        ENNReal.ofReal (2 / 3) *
          Kakeya.realRpowENN sourceDelta (sigma + finalLoss))
    (hhierarchyLossUpper :
      hierarchyLoss ≤ 1 / (data.mixed.levelCount : ℝ))
    (hcostAbsorb :
      (data.mixed.levelCount : ℝ) * 136 ≤
        Real.rpow sourceDelta (-hierarchyLoss))
    (threshold : PureWZ2Proposition64HierarchyScaleThreshold
      data.mixed.levelCount)
    (hsourceSmall : sourceDelta ≤ threshold.delta₀) :
    Nonempty { output : PureWZ2QuantitativeNormalizedHierarchyOutput
        sigma workLoss sourceDelta //
      output.densityLoss = densityLoss ∧
        output.normalized.inputLoss = inputLoss ∧
          output.normalized.source.family = source.family ∧
          output.normalized.hierarchy.hierarchy.levelCount =
            data.mixed.levelCount } := by
  rcases data.toQuantitativeLocallyLinearHierarchyWithLevelCount
      hbridge hsigma hsigmaOne hhierarchyLoss hfinalHierarchy
      hfinalLevelZero hdeltaStrict hgeometric hlevelZero hremoved
      hfinalVolume with ⟨quantitativeRaw⟩
  let hierarchy := quantitativeRaw.1.hierarchy.mono_finalLoss hhierarchyWork
  have hshading : hierarchy.shading =
      quantitativeRaw.1.hierarchy.shading := rfl
  let quantitative : PureWZ2QuantitativeLocallyLinearHierarchyData
      source workLoss hierarchyLoss densityLoss := {
    hierarchy := hierarchy
    multiplicity := quantitativeRaw.1.multiplicity
    multiplicity_pos := quantitativeRaw.1.multiplicity_pos
    pointMultiplicity_upper := by
      rw [hshading]
      exact quantitativeRaw.1.pointMultiplicity_upper
    mass_retention := by
      rw [hshading]
      exact quantitativeRaw.1.mass_retention }
  have hlevelCount : quantitative.hierarchy.hierarchy.levelCount =
      data.mixed.levelCount := by
    change quantitativeRaw.1.hierarchy.hierarchy.levelCount =
      data.mixed.levelCount
    exact quantitativeRaw.2
  rcases quantitative.hierarchy.toNormalizedHierarchyOutputWithEq
      (hinputHierarchy.trans hhierarchyWork) hbridge hhierarchyLoss.le
      (by rw [hlevelCount]; exact hhierarchyLossUpper)
      (by rw [hlevelCount]; exact hcostAbsorb)
      (by
        rw [hlevelCount]
        exact threshold.halfHeight_slab_ad
          source.extremal.delta_pos hsourceSmall)
      (by
        rw [hlevelCount]
        exact threshold.parameter_window
          source.extremal.delta_pos hsourceSmall) with ⟨output⟩
  let normalized : PureWZ2QuantitativeNormalizedHierarchyOutput
      sigma workLoss sourceDelta := {
    densityLoss := densityLoss
    quantitativeInputLoss := inputLoss
    inputLoss_le_workLoss := hinputHierarchy.trans hhierarchyWork
    quantitativeSource := source
    quantitativeHierarchyLoss := hierarchyLoss
    hierarchyLoss_pos := hhierarchyLoss
    quantitative := quantitative
    hierarchyLoss_upper := by
      rw [hlevelCount]
      exact hhierarchyLossUpper
    normalized := output.1
    inputLoss_eq := output.2.1
    source_eq := output.2.2.1
    hierarchyLoss_eq := output.2.2.2.2.1
    hierarchy_eq := output.2.2.2.2.2.1
    normalized_mass_retention := by
      rw [output.2.2.2.2.2.2.2.2, output.2.2.2.2.2.2.2.1]
      exact quantitative.mass_retention }
  have hnormalizedLevel :
      output.1.hierarchy.hierarchy.levelCount =
        quantitative.hierarchy.hierarchy.levelCount :=
    output.2.2.2.2.2.2.1
  exact ⟨⟨normalized, rfl, output.2.1, output.2.2.2.1,
    hnormalizedLevel.trans hlevelCount⟩⟩

end PureWZ2QuantitativeMixedRawHierarchyData

/-- Quantitative runtime data indexed directly by an already constructed
terminal datum.  This is the owner-free counterpart of the legacy invocation
wrapper below. -/
structure PureWZ2TerminalQuantitativeRuntimeData
    {sigma inputLoss delta outputLoss densityLoss : ℝ}
    {capability : PureWZ2PropStickyCapability}
    {schedule : PureWZ2ReentrantTerminalPaperOrderSchedule
      capability sigma outputLoss}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {logExponent : ℕ}
    {terminal : PureWZ2TerminalScaleStickyData
      source schedule.kernel.terminal.stickyLoss logExponent}
    (runtime : PureWZ2TerminalPaperOrderRuntimeData
      (schedule := schedule) terminal) where
  quantitative :
    PureWZ2TerminalPopularBlockResidueData.QuantitativeSameWitnessReceipt
      runtime.residue densityLoss

namespace PureWZ2TerminalQuantitativeRuntimeData

/-- Build the quantitative wrapper from the explicit pre-runtime scalar bound
for the concrete residue retained by `runtime`. -/
theorem ofScalar
    {sigma inputLoss delta outputLoss densityLoss : ℝ}
    {capability : PureWZ2PropStickyCapability}
    {schedule : PureWZ2ReentrantTerminalPaperOrderSchedule
      capability sigma outputLoss}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {logExponent : ℕ}
    {terminal : PureWZ2TerminalScaleStickyData
      source schedule.kernel.terminal.stickyLoss logExponent}
    (runtime : PureWZ2TerminalPaperOrderRuntimeData
      (schedule := schedule) terminal)
    (hscalar :
      32 * runtime.good.sourceMassCost *
          Kakeya.realRpowENN delta densityLoss ≤
        Kakeya.realRpowENN delta schedule.localMassLoss *
          wz2PaperPureRefinementFraction delta logExponent *
          Kakeya.realRpowENN delta inputLoss) :
    PureWZ2TerminalQuantitativeRuntimeData
      (densityLoss := densityLoss) runtime where
  quantitative := runtime.residue.quantitativeSameWitnessReceipt densityLoss
    (runtime.finalShading_source_body_mass_lower hscalar)

/-- Use the family-independent endpoint mass schedule after bounding the
concrete residue cost by the terminal logarithmic envelope. -/
theorem ofAbsorption
    {sigma inputLoss delta outputLoss densityLoss : ℝ}
    {capability : PureWZ2PropStickyCapability}
    {schedule : PureWZ2ReentrantTerminalPaperOrderSchedule
      capability sigma outputLoss}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData
      source schedule.kernel.terminal.stickyLoss 72}
    (runtime : PureWZ2TerminalPaperOrderRuntimeData
      (schedule := schedule) terminal)
    (absorption : PureWZ2RichEndpointQuantitativeMassAbsorption
      schedule.sourceLossCeiling schedule.localMassLoss densityLoss)
    (hinputCeiling : inputLoss ≤ schedule.sourceLossCeiling)
    (hdelta : 0 < delta) (hdeltaSmall : delta ≤ absorption.delta₀) :
    PureWZ2TerminalQuantitativeRuntimeData
      (densityLoss := densityLoss) runtime := by
  apply PureWZ2TerminalQuantitativeRuntimeData.ofScalar runtime
  have hcost : 32 * runtime.good.sourceMassCost ≤
      pureWZ2TerminalPairSourceMassLogCost delta := by
    rw [runtime.sourceMassCost_eq]
    calc
      32 * (8 * (runtime.pairClass.bins : ENNReal)) =
          256 * (runtime.pairClass.bins : ENNReal) := by ring
      _ ≤ pureWZ2TerminalPairSourceMassLogCost delta :=
        runtime.pairClass.sourceMassCost_le
  have hscheduled := absorption.absorb_actual_cost hdelta hdeltaSmall hcost
  exact hscheduled.trans <| by
    gcongr
    exact realRpowENN_antitone hdelta source.extremal.delta_le_one
      hinputCeiling

/-- Convert the retained concrete residue to the quantitative exact terminal
without reselecting either the terminal data or the residue. -/
theorem toQuantitativeExactTerminal
    {sigma inputLoss delta outputLoss densityLoss : ℝ}
    {capability : PureWZ2PropStickyCapability}
    {schedule : PureWZ2ReentrantTerminalPaperOrderSchedule
      capability sigma outputLoss}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {logExponent : ℕ}
    {terminal : PureWZ2TerminalScaleStickyData
      source schedule.kernel.terminal.stickyLoss logExponent}
    {runtime : PureWZ2TerminalPaperOrderRuntimeData
      (schedule := schedule) terminal}
    (data : PureWZ2TerminalQuantitativeRuntimeData
      (densityLoss := densityLoss) runtime) :
    Nonempty (PureWZ2QuantitativeExactTerminalLevelData
      source outputLoss densityLoss) := by
  rcases runtime.residue.toQuantitativeExactTerminalLevel
      data.quantitative runtime.inputLoss_le_working
      runtime.terminal_volume_scalar with ⟨workingTerminal⟩
  exact ⟨workingTerminal.mono_loss
    schedule.kernel.terminal.workingLoss_le_output⟩

/-- Append the direct terminal runtime to its literal ordinary prefix. -/
theorem appendToOrdinaryWithLevelCount
    {sigma inputLoss delta outputLoss densityLoss hierarchyLoss : ℝ}
    {capability : PureWZ2PropStickyCapability}
    {schedule : PureWZ2ReentrantTerminalPaperOrderSchedule
      capability sigma outputLoss}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {logExponent : ℕ}
    {terminal : PureWZ2TerminalScaleStickyData
      source schedule.kernel.terminal.stickyLoss logExponent}
    {runtime : PureWZ2TerminalPaperOrderRuntimeData
      (schedule := schedule) terminal}
    {N : ℕ}
    (ordinary : PureWZ2OrdinaryHierarchyPrefixData source hierarchyLoss N)
    (houtputHierarchy : outputLoss ≤ hierarchyLoss)
    (data : PureWZ2TerminalQuantitativeRuntimeData
      (densityLoss := densityLoss) runtime) :
    Nonempty { mixed : PureWZ2QuantitativeMixedRawHierarchyData
        source outputLoss hierarchyLoss densityLoss //
      mixed.mixed.levelCount = N } := by
  rcases data.toQuantitativeExactTerminal with ⟨terminalLevel⟩
  exact ordinary.appendQuantitativeExactTerminalWithLevelCount
    terminalLevel houtputHierarchy

end PureWZ2TerminalQuantitativeRuntimeData

/-- The exact fixed-runtime output that must be saved after the actual
paper-order good-block family and its mass-selected residue are constructed.
The package is indexed by one genuine invocation and contains no universal
producer for unrelated terminals. -/
structure PureWZ2ReentrantTerminalQuantitativeFixedRuntimeReceipts
    {sigma inputLoss delta outputLoss densityLoss : ℝ}
    {capability : PureWZ2PropStickyCapability}
    {schedule : PureWZ2ReentrantTerminalPaperOrderSchedule
      capability sigma outputLoss}
    {current : PureWZ2ReentrantGrainSource sigma inputLoss delta
      capability.normalizationExponent}
    (invocation : PureWZ2ReentrantTerminalKernelInvocation
      (schedule := schedule.kernel) current) where
  paperOrder : PureWZ2ReentrantTerminalPaperOrderReceipts invocation
  terminalSource : PureWZ2TerminalPreparedSource current.grain
    paperOrder.owner.toOwner.toTerminalScaleStickyData
  prepared : PureWZ2TerminalLemma23Prepared terminalSource
  good : PureWZ2TerminalPopularGoodBlockFamilyData
    (eta := schedule.kernel.terminal.eta)
    (theoremEta := schedule.kernel.terminal.theoremEta)
    (outputLoss := schedule.kernel.terminal.workingLoss)
    (localMassLoss := schedule.localMassLoss) prepared
  residue : PureWZ2TerminalPopularBlockResidueData good
  quantitative :
    PureWZ2TerminalPopularBlockResidueData.QuantitativeSameWitnessReceipt
      residue densityLoss
  terminal_volume_scalar :
    32 * good.sourceMassCost *
          Kakeya.realRpowENN delta
            (sigma + schedule.kernel.terminal.workingLoss) ≤
      Kakeya.realRpowENN delta schedule.localMassLoss *
        Kakeya.realRpowENN delta
          (sigma + schedule.kernel.terminal.stickyLoss)

namespace PureWZ2ReentrantTerminalQuantitativeFixedRuntimeReceipts

/-- Convert one actual fixed-runtime paper-order package to quantitative exact
terminal data without reselecting a terminal or residue. -/
theorem toQuantitativeExactTerminal
    {sigma inputLoss delta outputLoss densityLoss : ℝ}
    {capability : PureWZ2PropStickyCapability}
    {schedule : PureWZ2ReentrantTerminalPaperOrderSchedule
      capability sigma outputLoss}
    {current : PureWZ2ReentrantGrainSource sigma inputLoss delta
      capability.normalizationExponent}
    {invocation : PureWZ2ReentrantTerminalKernelInvocation
      (schedule := schedule.kernel) current}
    (hinputCeiling : inputLoss ≤ schedule.sourceLossCeiling)
    (receipts :
      PureWZ2ReentrantTerminalQuantitativeFixedRuntimeReceipts
        (densityLoss := densityLoss) invocation) :
    Nonempty (PureWZ2QuantitativeExactTerminalLevelData
      current.grain outputLoss densityLoss) := by
  have hinputWorking : inputLoss ≤ schedule.kernel.terminal.workingLoss :=
    hinputCeiling.trans schedule.sourceLossCeiling_kernel |>.trans <|
      schedule.kernel.sourceLossCeiling_terminal.trans <|
        schedule.kernel.terminal.sourceLossCeiling_working.trans <|
          div_le_self schedule.kernel.terminal.workingLoss_pos.le (by norm_num)
  rcases receipts.residue.toQuantitativeExactTerminalLevel
      receipts.quantitative hinputWorking receipts.terminal_volume_scalar with
    ⟨workingTerminal⟩
  exact ⟨workingTerminal.mono_loss
    schedule.kernel.terminal.workingLoss_le_output⟩

/-- Append the fixed-runtime quantitative terminal only after its same-witness
receipt has been checked. -/
theorem appendToOrdinaryWithLevelCount
    {sigma inputLoss delta outputLoss densityLoss hierarchyLoss : ℝ}
    {capability : PureWZ2PropStickyCapability}
    {schedule : PureWZ2ReentrantTerminalPaperOrderSchedule
      capability sigma outputLoss}
    {current : PureWZ2ReentrantGrainSource sigma inputLoss delta
      capability.normalizationExponent}
    {invocation : PureWZ2ReentrantTerminalKernelInvocation
      (schedule := schedule.kernel) current}
    {N : ℕ}
    (ordinary :
      PureWZ2OrdinaryHierarchyPrefixData current.grain hierarchyLoss N)
    (hinputCeiling : inputLoss ≤ schedule.sourceLossCeiling)
    (houtputHierarchy : outputLoss ≤ hierarchyLoss)
    (receipts :
      PureWZ2ReentrantTerminalQuantitativeFixedRuntimeReceipts
        (densityLoss := densityLoss) invocation) :
    Nonempty { mixed : PureWZ2QuantitativeMixedRawHierarchyData
        current.grain outputLoss hierarchyLoss densityLoss //
      mixed.mixed.levelCount = N } := by
  rcases receipts.toQuantitativeExactTerminal hinputCeiling with
    ⟨terminalLevel⟩
  exact ordinary.appendQuantitativeExactTerminalWithLevelCount
    terminalLevel houtputHierarchy

end PureWZ2ReentrantTerminalQuantitativeFixedRuntimeReceipts

end Kakeya.Assouad

end
