import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.FixedLineCore
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalScaleParentResidue
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalScaleRetainedShading
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalScaleSourceFamily
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalScaleFixedBandSelection
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalScaleAnchoredPieces
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.TerminalScaleExactGraphParents

/-!
# All global-bin fibres on one terminal slice

The terminal use of WZ Lemma 24 must retain the contribution of every
global AD bin.  Selecting one largest bin introduces a fixed power loss at
the exact endpoint.  This module records the finite partition before any
parent or local-grain choices are made.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- Explicit parent projection for callers that consume the non-maximal
fixed-bin interface. -/
def PureWZ2HorizontalFixedLineCore.toFixedBinCore
    {delta rho sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : Kakeya.Streamlined.TubeShading family}
    {C : ENNReal}
    {windowed : WZ1Lemma23WindowedGlobalSlicePackage
      (delta := delta) (rho := rho) (sigma := sigma) shading C}
    {slope : ℝ → ℝ}
    (line : PureWZ2HorizontalFixedLineCore windowed slope) :
    PureWZ2HorizontalFixedBinCore windowed slope :=
  line.toPureWZ2HorizontalFixedBinCore

/-- The global-bin label used on the fixed Fubini slice. -/
def pureWZ2HorizontalGlobalBinLabel
    {delta rho sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : Kakeya.Streamlined.TubeShading family}
    {C : ENNReal}
    {windowed : WZ1Lemma23WindowedGlobalSlicePackage
      (delta := delta) (rho := rho) (sigma := sigma) shading C}
    {slope : ℝ → ℝ}
    (line : PureWZ2HorizontalFixedLineCore windowed slope)
    (cell : ℤ × ℤ × ℤ) : ℤ :=
  Int.floor
    (wz1Lemma23GlobalCoordinate windowed.global.extendedSlope
      (wz1Lemma23CellCenter rho cell) / rho)

/-- Cells of the common Fubini slice carrying one prescribed global-bin
label. -/
def pureWZ2HorizontalGlobalBinCells
    {delta rho sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : Kakeya.Streamlined.TubeShading family}
    {C : ENNReal}
    {windowed : WZ1Lemma23WindowedGlobalSlicePackage
      (delta := delta) (rho := rho) (sigma := sigma) shading C}
    {slope : ℝ → ℝ}
    (line : PureWZ2HorizontalFixedLineCore windowed slope)
    (bin : ℤ) : Finset (ℤ × ℤ × ℤ) :=
  line.sliceCells.filter fun cell =>
    pureWZ2HorizontalGlobalBinLabel line cell = bin

theorem pureWZ2HorizontalGlobalBinCells_subset
    {delta rho sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : Kakeya.Streamlined.TubeShading family}
    {C : ENNReal}
    {windowed : WZ1Lemma23WindowedGlobalSlicePackage
      (delta := delta) (rho := rho) (sigma := sigma) shading C}
    {slope : ℝ → ℝ}
    (line : PureWZ2HorizontalFixedLineCore windowed slope)
    (bin : ℤ) :
    pureWZ2HorizontalGlobalBinCells line bin ⊆ line.sliceCells :=
  Finset.filter_subset _ _

/-- Every listed global bin has a nonempty cell fibre. -/
theorem pureWZ2HorizontalGlobalBinCells_nonempty
    {delta rho sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : Kakeya.Streamlined.TubeShading family}
    {C : ENNReal}
    {windowed : WZ1Lemma23WindowedGlobalSlicePackage
      (delta := delta) (rho := rho) (sigma := sigma) shading C}
    {slope : ℝ → ℝ}
    (line : PureWZ2HorizontalFixedLineCore windowed slope)
    {bin : ℤ} (hbin : bin ∈ line.globalBins) :
    (pureWZ2HorizontalGlobalBinCells line bin).Nonempty := by
  rw [line.globalBins_eq] at hbin
  rcases Finset.mem_image.mp hbin with ⟨cell, hcell, hlabel⟩
  refine ⟨cell, Finset.mem_filter.mpr ⟨hcell, ?_⟩⟩
  simpa [pureWZ2HorizontalGlobalBinLabel] using hlabel

/-- The maximal-bin `heavyCells` are one member of the all-bin family. -/
theorem pureWZ2HorizontalGlobalBinCells_lineBin
    {delta rho sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : Kakeya.Streamlined.TubeShading family}
    {C : ENNReal}
    {windowed : WZ1Lemma23WindowedGlobalSlicePackage
      (delta := delta) (rho := rho) (sigma := sigma) shading C}
    {slope : ℝ → ℝ}
    (line : PureWZ2HorizontalFixedLineCore windowed slope) :
    pureWZ2HorizontalGlobalBinCells line line.lineBin = line.heavyCells := by
  rw [line.heavyCells_eq]
  rfl

/-- The slice cells are the disjoint fibres of their global-bin label.  This
is the exact counting identity needed before summing per-bin terminal
outputs; no `globalBins.card` loss occurs. -/
theorem PureWZ2HorizontalFixedLineCore.card_eq_sum_globalBinCells
    {delta rho sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : Kakeya.Streamlined.TubeShading family}
    {C : ENNReal}
    {windowed : WZ1Lemma23WindowedGlobalSlicePackage
      (delta := delta) (rho := rho) (sigma := sigma) shading C}
    {slope : ℝ → ℝ}
    (line : PureWZ2HorizontalFixedLineCore windowed slope) :
    line.sliceCells.card =
      ∑ bin ∈ line.globalBins,
        (pureWZ2HorizontalGlobalBinCells line bin).card := by
  let label : (ℤ × ℤ × ℤ) → ℤ :=
    pureWZ2HorizontalGlobalBinLabel line
  have hmaps : Set.MapsTo label
      (line.sliceCells : Set (ℤ × ℤ × ℤ))
      (line.globalBins : Set ℤ) := by
    intro cell hcell
    rw [line.globalBins_eq]
    exact Finset.mem_image.mpr ⟨cell, hcell, by
      rfl⟩
  simpa [label, pureWZ2HorizontalGlobalBinCells] using
    Finset.card_eq_sum_card_fiberwise hmaps

/-- The corresponding identity after coercion to `ENNReal`. -/
theorem PureWZ2HorizontalFixedLineCore.enncard_eq_sum_globalBinCells
    {delta rho sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : Kakeya.Streamlined.TubeShading family}
    {C : ENNReal}
    {windowed : WZ1Lemma23WindowedGlobalSlicePackage
      (delta := delta) (rho := rho) (sigma := sigma) shading C}
    {slope : ℝ → ℝ}
    (line : PureWZ2HorizontalFixedLineCore windowed slope) :
    (line.sliceCells.card : ENNReal) =
      ∑ bin ∈ line.globalBins,
        ((pureWZ2HorizontalGlobalBinCells line bin).card : ENNReal) := by
  exact_mod_cast line.card_eq_sum_globalBinCells

/-- Repackage any actual global-bin fibre of the selected Fubini slice as a
fixed-bin core.  All geometric estimates are inherited from the common slice;
only the largest-fibre cardinality inequality is intentionally absent. -/
theorem PureWZ2HorizontalFixedLineCore.coreAtGlobalBin
    {delta rho sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : Kakeya.Streamlined.TubeShading family}
    {C : ENNReal}
    {windowed : WZ1Lemma23WindowedGlobalSlicePackage
      (delta := delta) (rho := rho) (sigma := sigma) shading C}
    {slope : ℝ → ℝ}
    (line : PureWZ2HorizontalFixedLineCore windowed slope)
    (bin : ℤ) (hbin : bin ∈ line.globalBins) :
    ∃ core : PureWZ2HorizontalFixedBinCore windowed slope,
      core.lineBin = bin ∧
        core.heavyCells = pureWZ2HorizontalGlobalBinCells line bin := by
  let heavyCells := pureWZ2HorizontalGlobalBinCells line bin
  have hheavyNonempty : heavyCells.Nonempty :=
    pureWZ2HorizontalGlobalBinCells_nonempty line hbin
  have hheavySubset : heavyCells ⊆ line.sliceCells :=
    pureWZ2HorizontalGlobalBinCells_subset line bin
  let lineCell := Classical.choose hheavyNonempty
  have hlineCell : lineCell ∈ heavyCells :=
    Classical.choose_spec hheavyNonempty
  let representative (cell : ℤ × ℤ × ℤ) : Point3 :=
    if hcell : cell ∈ heavyCells then
      wz1Lemma23LiftSlicePoint line.lineHeight
        (wz1Lemma23ExactSliceRepresentative shading line.rho_pos
          line.lineHeight ⟨cell, by
            simpa [line.sliceCells_eq] using hheavySubset hcell⟩)
    else 0
  have hrepEq : ∀ cell (hcell : cell ∈ heavyCells),
      representative cell =
        wz1Lemma23LiftSlicePoint line.lineHeight
          (wz1Lemma23ExactSliceRepresentative shading line.rho_pos
            line.lineHeight ⟨cell, by
              simpa [line.sliceCells_eq] using hheavySubset hcell⟩) := by
    intro cell hcell
    simp [representative, hcell]
  have hrepMem : ∀ cell (hcell : cell ∈ heavyCells),
      representative cell ∈ shading.union := by
    intro cell hcell
    rw [hrepEq cell hcell]
    exact wz1Lemma23ExactSliceRepresentative_mem_union shading line.rho_pos
      line.lineHeight _
  have hrepHeight : ∀ cell (hcell : cell ∈ heavyCells),
      representative cell (2 : Fin 3) = line.lineHeight := by
    intro cell hcell
    rw [hrepEq cell hcell]
    simp [wz1Lemma23LiftSlicePoint, point3]
  have hrepIndex : ∀ cell (hcell : cell ∈ heavyCells),
      wz1Lemma23CellIndex rho (representative cell) = cell := by
    intro cell hcell
    rw [hrepEq cell hcell]
    exact wz1Lemma23ExactSliceRepresentative_index shading line.rho_pos
      line.lineHeight _
  let lineAnchor := representative lineCell
  let lineLevel := inner ℝ lineAnchor
    (globalGrainDirection (slope line.lineHeight))
  have hextendedEq : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      windowed.global.extendedSlope z = slope z := by
    intro z hz
    rw [windowed.global.extendedSlope_eq z hz, line.sourceSlope_eq]
  have hnear : ∀ cell (hcell : cell ∈ heavyCells),
      |inner ℝ (representative cell)
          (globalGrainDirection (slope line.lineHeight)) - lineLevel| ≤
        9 * rho := by
    intro cell hcell
    let coordinate : Point3 → ℝ := fun point =>
      wz1Lemma23GlobalCoordinate windowed.global.extendedSlope point
    have hpHeight := hrepHeight cell hcell
    have haHeight := hrepHeight lineCell hlineCell
    have hpIndex := hrepIndex cell hcell
    have haIndex := hrepIndex lineCell hlineCell
    have hpSnap := wz1Lemma23_globalCoordinate_snap_of_coord_bound
      line.rho_pos line.rho_le_one
      windowed.global.extendedSlope windowed.global.extendedSlope_lipschitz
      windowed.global.extendedSlope_bounded (representative cell)
      (line.coordinate_bound _ (hrepMem cell hcell))
    have haSnap := wz1Lemma23_globalCoordinate_snap_of_coord_bound
      line.rho_pos line.rho_le_one
      windowed.global.extendedSlope windowed.global.extendedSlope_lipschitz
      windowed.global.extendedSlope_bounded lineAnchor
      (line.coordinate_bound _ (hrepMem lineCell hlineCell))
    have hcenter : |coordinate (wz1Lemma23CellCenter rho cell) -
        coordinate (wz1Lemma23CellCenter rho lineCell)| < rho := by
      apply wz1Lemma23_abs_sub_lt_of_floor_div_eq line.rho_pos
      have hcellBin := (Finset.mem_filter.mp hcell).2
      have hlineBin := (Finset.mem_filter.mp hlineCell).2
      simpa [heavyCells, pureWZ2HorizontalGlobalBinCells,
        pureWZ2HorizontalGlobalBinLabel, coordinate] using
        hcellBin.trans hlineBin.symm
    have hpCoord : coordinate (representative cell) =
        inner ℝ (representative cell)
          (globalGrainDirection (slope line.lineHeight)) := by
      simp only [coordinate, wz1Lemma23GlobalCoordinate]
      rw [hpHeight, hextendedEq line.lineHeight line.lineHeight_mem]
      simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
    have haCoord : coordinate lineAnchor = lineLevel := by
      dsimp only [lineAnchor, lineLevel]
      simp only [coordinate, wz1Lemma23GlobalCoordinate]
      rw [haHeight, hextendedEq line.lineHeight line.lineHeight_mem]
      simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
    have hpSnapEq : wz1Lemma23Snap rho (representative cell) =
        wz1Lemma23CellCenter rho cell := by
      simp [wz1Lemma23Snap, hpIndex]
    have haSnapEq : wz1Lemma23Snap rho lineAnchor =
        wz1Lemma23CellCenter rho lineCell := by
      dsimp only [lineAnchor]
      simp [wz1Lemma23Snap, haIndex]
    rw [hpSnapEq] at hpSnap
    rw [haSnapEq] at haSnap
    rw [← hpCoord, ← haCoord]
    have htriangle := abs_sub_le (coordinate (representative cell))
      (coordinate (wz1Lemma23CellCenter rho cell)) (coordinate lineAnchor)
    have htriangle2 := abs_sub_le
      (coordinate (wz1Lemma23CellCenter rho cell))
      (coordinate (wz1Lemma23CellCenter rho lineCell)) (coordinate lineAnchor)
    have hpointBound :
        |coordinate (representative cell) -
          coordinate (wz1Lemma23CellCenter rho cell)| ≤ 4 * rho := by
      simpa [coordinate] using hpSnap
    have hanchorBound :
        |coordinate (wz1Lemma23CellCenter rho lineCell) -
          coordinate lineAnchor| ≤ 4 * rho := by
      simpa [coordinate, abs_sub_comm] using haSnap
    exact htriangle.trans (by
      linarith [htriangle2, hpointBound, hanchorBound, hcenter.le])
  refine ⟨{
    rho_pos := line.rho_pos
    rho_le_one := line.rho_le_one
    sourceSlope_eq := line.sourceSlope_eq
    coordinate_bound := line.coordinate_bound
    lineHeight := line.lineHeight
    lineHeight_mem := line.lineHeight_mem
    sliceCells := line.sliceCells
    sliceCells_eq := line.sliceCells_eq
    slice_area_lower := line.slice_area_lower
    sliceCells_nonempty := line.sliceCells_nonempty
    globalBins := line.globalBins
    globalBins_eq := line.globalBins_eq
    global_bin_count := line.global_bin_count
    lineBin := bin
    lineBin_mem := hbin
    heavyCells := heavyCells
    heavyCells_eq := rfl
    heavyCells_subset := hheavySubset
    heavyCells_nonempty := hheavyNonempty
    representative := representative
    representative_eq := hrepEq
    representative_mem := hrepMem
    representative_height := hrepHeight
    representative_index := hrepIndex
    lineCell := lineCell
    lineCell_mem := hlineCell
    lineAnchor := lineAnchor
    lineAnchor_eq := rfl
    lineAnchor_mem := hrepMem lineCell hlineCell
    lineAnchor_height := hrepHeight lineCell hlineCell
    lineLevel := lineLevel
    lineLevel_eq := rfl
    heavy_representative_near_line := hnear }, rfl, rfl⟩

/-- All nonempty global-bin fibres of one Fubini slice, together with their
genuine terminal parent geometry. This is the lossless input for the weighted
terminal aggregation: the cell fibres partition the common slice before any
largest-bin pigeonhole is applied. -/
structure PureWZ2TerminalGlobalBinParentFamily
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    (line : PureWZ2HorizontalFixedLineCore
      window.windowed source.globalGrains.slope) where
  core : ∀ bin : {bin // bin ∈ line.globalBins},
    PureWZ2HorizontalFixedBinCore
      window.windowed source.globalGrains.slope
  lineBin_eq : ∀ bin, (core bin).lineBin = bin.1
  heavyCells_eq : ∀ bin, (core bin).heavyCells =
    pureWZ2HorizontalGlobalBinCells line bin.1
  parents : ∀ bin, PureWZ2TerminalFixedBinParentData (core bin)
  selection : ∀ bin, PureWZ2TerminalBinParentYSelection (parents bin)
  residue : ∀ bin, PureWZ2TerminalBinParentYResidueData (selection bin)
  retained : ∀ bin, PureWZ2TerminalBinRetainedShadingData (residue bin)
  sources : ∀ bin, PureWZ2TerminalBinSourceFamily (retained bin)
  band : ∀ bin, PureWZ2TerminalBinFixedBandSelection (sources bin)
  phase : ∀ bin, PureWZ2TerminalBinHeightPhaseSelection (band bin)
  anchored : ∀ bin, PureWZ2TerminalBinAnchoredPieceData (phase bin)
  preparedGraphCarrier : ∀ bin,
    PureWZ2TerminalBinExactGraphPreparation (anchored bin)
  graphParents : ∀ bin,
    PureWZ2TerminalExactGraphParentData (preparedGraphCarrier bin)
  slice_card : line.sliceCells.card =
    ∑ bin : {bin // bin ∈ line.globalBins}, (core bin).heavyCells.card

/-- Construct the parent package independently on every global-bin fibre. -/
theorem PureWZ2HorizontalFixedLineCore.toTerminalGlobalBinParents
    {sigma inputLoss delta stickyLoss : ℝ}
    {logExponent : ℕ}
    {source : PureWZ2QuantitativeGrainConfiguration sigma inputLoss delta}
    {terminal : PureWZ2TerminalScaleStickyData source stickyLoss logExponent}
    {terminalSource : PureWZ2TerminalPreparedSource source terminal}
    {prepared : PureWZ2TerminalLemma23Prepared terminalSource}
    {window : PureWZ2TerminalWindow prepared}
    (line : PureWZ2HorizontalFixedLineCore
      window.windowed source.globalGrains.slope)
    (hbridge : PureWZ2PaperADBridgeStatement) :
    Nonempty (PureWZ2TerminalGlobalBinParentFamily line) := by
  let core : ∀ bin : {bin // bin ∈ line.globalBins},
      PureWZ2HorizontalFixedBinCore
        window.windowed source.globalGrains.slope := fun bin =>
    Classical.choose (line.coreAtGlobalBin bin.1 bin.2)
  let parents : ∀ bin, PureWZ2TerminalFixedBinParentData (core bin) :=
    fun bin => Classical.choice ((core bin).toTerminalBinParents)
  let selection : ∀ bin, PureWZ2TerminalBinParentYSelection (parents bin) :=
    fun bin => Classical.choice ((parents bin).selectOnePerYBin)
  let residue : ∀ bin,
      PureWZ2TerminalBinParentYResidueData (selection bin) :=
    fun bin => Classical.choice ((selection bin).selectResidueBin)
  let retained : ∀ bin,
      PureWZ2TerminalBinRetainedShadingData (residue bin) :=
    fun bin => Classical.choice ((residue bin).retainSourceShadingBin)
  let sources : ∀ bin, PureWZ2TerminalBinSourceFamily (retained bin) :=
    fun bin => Classical.choice ((retained bin).sourcesBin)
  let band : ∀ bin, PureWZ2TerminalBinFixedBandSelection (sources bin) :=
    fun bin => Classical.choice ((sources bin).selectFixedBandBin)
  let phase : ∀ bin, PureWZ2TerminalBinHeightPhaseSelection (band bin) :=
    fun bin => Classical.choice ((band bin).selectHeightPhaseBin)
  let anchored : ∀ bin, PureWZ2TerminalBinAnchoredPieceData (phase bin) :=
    fun bin => Classical.choice ((phase bin).anchorPiecesBin)
  let preparedGraphCarrier : ∀ bin,
      PureWZ2TerminalBinExactGraphPreparation (anchored bin) :=
    fun bin => Classical.choice ((anchored bin).prepareExactGraphBin hbridge)
  let graphParents : ∀ bin,
      PureWZ2TerminalExactGraphParentData (preparedGraphCarrier bin) :=
    fun bin => Classical.choice ((preparedGraphCarrier bin).graphParents)
  have hlineBin : ∀ bin, (core bin).lineBin = bin.1 := by
    intro bin
    exact (Classical.choose_spec
      (line.coreAtGlobalBin bin.1 bin.2)).1
  have hheavy : ∀ bin, (core bin).heavyCells =
      pureWZ2HorizontalGlobalBinCells line bin.1 := by
    intro bin
    exact (Classical.choose_spec
      (line.coreAtGlobalBin bin.1 bin.2)).2
  have hslice : line.sliceCells.card =
      ∑ bin : {bin // bin ∈ line.globalBins}, (core bin).heavyCells.card := by
    calc
      line.sliceCells.card =
          ∑ bin ∈ line.globalBins,
            (pureWZ2HorizontalGlobalBinCells line bin).card :=
        line.card_eq_sum_globalBinCells
      _ = ∑ bin : {bin // bin ∈ line.globalBins},
          (pureWZ2HorizontalGlobalBinCells line bin.1).card := by
        exact Finset.sum_subtype line.globalBins (fun _ => Iff.rfl) _
      _ = ∑ bin : {bin // bin ∈ line.globalBins},
          (core bin).heavyCells.card := by
        apply Finset.sum_congr rfl
        intro bin _hbin
        rw [hheavy bin]
  exact ⟨{
    core := core
    lineBin_eq := hlineBin
    heavyCells_eq := hheavy
    parents := parents
    selection := selection
    residue := residue
    retained := retained
    sources := sources
    band := band
    phase := phase
    anchored := anchored
    preparedGraphCarrier := preparedGraphCarrier
    graphParents := graphParents
    slice_card := hslice
  }⟩

end Kakeya.Assouad
