import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62FourDegreeIncidence
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Section6CoverParentMap
import MyLeanRepo.Kakeya.Assouad.PropStickyExactCellBalancingHelpers

/-!
# Proposition 6.2: exact fine multiplicity on packet-cell edges

This is the first step of the paper's four-degree lemma.  The tube families
and the genuine Section 6 metric fibers are fixed.  For a metric parent `P`
and a fixed fine cell `q`, `packetCellMultiplicity P q` is the number of
members of the complete metric fiber over `P` whose shading contains the
whole cell `q`.

One global dyadic pigeonhole selects a common multiplicity scale
`muFine = 2^level`.  This module stops at that multiplicity class.  The
paper's exact choice of `muFine` tube incidences is intentionally deferred
until after the parent-weight selection and reference-tree cleanup.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

structure PureWZ2Prop62PacketCellInput
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : PureWZ2Section6Cover fine coarse)
    (shading : WZ1PaperTubeShading fine) where
  delta_pos : 0 < delta
  rho_pos : 0 < rho
  cubical : WZ1PaperIsCubicalShading shading
  fineCells : Finset WZ2PaperCellIndex
  fineCells_eq :
    fineCells = wz1PaperActiveCells shading delta_pos
  fineCells_nonempty : fineCells.Nonempty
  coarseCellOf : WZ2PaperCellIndex → WZ2PaperCellIndex
  fine_cell_containment :
    ∀ cell ∈ fineCells,
      wz1PaperGridCube delta cell ⊆
        wz1PaperGridCube rho (coarseCellOf cell)
  parent_cell_containment :
    ∀ parent cell source,
      cell ∈ fineCells →
      source ∈ wz2PaperFullFiberIndices fine coarse parent →
      wz1PaperGridCube delta cell ⊆ shading.carrier source →
        wz1PaperGridCube rho (coarseCellOf cell) ⊆
          wz1PaperTubeCarrier (coarse.tube parent)

namespace PureWZ2Prop62PacketCellInput

variable
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {shading : WZ1PaperTubeShading fine}
    (input : PureWZ2Prop62PacketCellInput cover shading)

/-- Fine sources in the genuine metric fiber over `parent` whose shading
contains the whole fixed cell. -/
def packetCellSources
    (parent : Fin coarse.card)
    (cell : WZ2PaperCellIndex) :
    Finset (Fin fine.card) :=
  if cell ∈ input.fineCells then
    (wz2PaperFullFiberIndices fine coarse parent).filter fun source =>
      wz1PaperGridCube delta cell ⊆ shading.carrier source
  else
    ∅

/-- The paper's `m(P,q)`. -/
def packetCellMultiplicity
    (pair : Fin coarse.card × WZ2PaperCellIndex) : ℕ :=
  (input.packetCellSources pair.1 pair.2).card

/-- All parent-cell pairs with positive multiplicity. -/
def positivePairs :
    Finset (Fin coarse.card × WZ2PaperCellIndex) :=
  (Finset.univ ×ˢ input.fineCells).filter fun pair =>
    0 < input.packetCellMultiplicity pair

@[simp]
theorem mem_packetCellSources_iff
    (parent : Fin coarse.card)
    (cell : WZ2PaperCellIndex)
    (source : Fin fine.card) :
    source ∈ input.packetCellSources parent cell ↔
      cell ∈ input.fineCells ∧
        source ∈ wz2PaperFullFiberIndices fine coarse parent ∧
        wz1PaperGridCube delta cell ⊆
          shading.carrier source := by
  by_cases cellMem : cell ∈ input.fineCells
  · simp [packetCellSources, cellMem]
  · simp [packetCellSources, cellMem]

@[simp]
theorem mem_positivePairs_iff
    (pair : Fin coarse.card × WZ2PaperCellIndex) :
    pair ∈ input.positivePairs ↔
      pair.2 ∈ input.fineCells ∧
        0 < input.packetCellMultiplicity pair := by
  simp [positivePairs]

theorem positivePairs_nonempty :
    input.positivePairs.Nonempty := by
  rcases input.fineCells_nonempty with ⟨cell, cellMem⟩
  have cellActive :
      cell ∈ wz1PaperActiveCells shading input.delta_pos := by
    rw [← input.fineCells_eq]
    exact cellMem
  rcases
      ((mem_wz1PaperActiveCells
        shading input.delta_pos cell).mp cellActive).2
    with
    ⟨point, pointUnion, pointCell⟩
  rcases pointUnion with ⟨source, pointCarrier⟩
  change Fin fine.card at source
  change point ∈ shading.carrier source at pointCarrier
  let parent :=
    cover.toWZ1PaperTubeCover.parent source
  have sourceFiber :
      source ∈ wz2PaperFullFiberIndices fine coarse parent := by
    exact
      (mem_wz2PaperFullFiberIndices_iff parent source).mpr
        (cover.toWZ1PaperTubeCover.parent_covers source)
  have cellCarrier :
      wz1PaperGridCube delta cell ⊆
        shading.carrier source := by
    have pointIndex :
        wz1PaperGridIndex delta point = cell :=
      (mem_wz1PaperGridCube delta cell point).mp pointCell
    simpa [pointIndex] using
      input.cubical source point pointCarrier
  have sourceMem :
      source ∈ input.packetCellSources parent cell := by
    exact
      (input.mem_packetCellSources_iff parent cell source).mpr
        ⟨cellMem, sourceFiber, cellCarrier⟩
  have multiplicityPos :
      0 < input.packetCellMultiplicity (parent, cell) := by
    exact Finset.card_pos.mpr ⟨source, sourceMem⟩
  exact
    ⟨(parent, cell),
      (input.mem_positivePairs_iff (parent, cell)).mpr
        ⟨cellMem, multiplicityPos⟩⟩

theorem positivePair_multiplicity_pos :
    ∀ pair ∈ input.positivePairs,
      0 < input.packetCellMultiplicity pair := by
  intro pair pairMem
  exact (input.mem_positivePairs_iff pair).mp pairMem |>.2

structure FineMultiplicityClassData where
  level : ℕ
  muFine : ℕ
  muFine_eq : muFine = 2 ^ level
  muFine_pos : 0 < muFine
  selectedPairs :
    Finset (Fin coarse.card × WZ2PaperCellIndex)
  selectedPairs_nonempty : selectedPairs.Nonempty
  selectedPairs_subset :
    selectedPairs ⊆ input.positivePairs
  multiplicity_band :
    ∀ pair ∈ selectedPairs,
      muFine ≤ input.packetCellMultiplicity pair ∧
        input.packetCellMultiplicity pair < 2 * muFine
  binCount : ℕ
  binCount_eq :
    binCount =
      Nat.log 2
        (∑ pair ∈ input.positivePairs,
          input.packetCellMultiplicity pair) + 1
  class_retention :
    (∑ pair ∈ input.positivePairs,
        input.packetCellMultiplicity pair) ≤
      binCount *
        ∑ pair ∈ selectedPairs,
          input.packetCellMultiplicity pair

namespace FineMultiplicityClassData

variable
    (data : input.FineMultiplicityClassData)

theorem source_mem_fullFiber
    (pair : {pair // pair ∈ data.selectedPairs})
    {source : Fin fine.card}
    (sourceMem :
      source ∈
        input.packetCellSources pair.1.1 pair.1.2) :
    source ∈
      wz2PaperFullFiberIndices fine coarse pair.1.1 := by
  exact
    (input.mem_packetCellSources_iff
      pair.1.1 pair.1.2 source).mp
        sourceMem |>.2.1

theorem cell_subset_carrier
    (pair : {pair // pair ∈ data.selectedPairs})
    {source : Fin fine.card}
    (sourceMem :
      source ∈
        input.packetCellSources pair.1.1 pair.1.2) :
    wz1PaperGridCube delta pair.1.2 ⊆
      shading.carrier source := by
  exact
    (input.mem_packetCellSources_iff
      pair.1.1 pair.1.2 source).mp
        sourceMem |>.2.2

theorem coarseCell_subset_parentCarrier
    (pair : {pair // pair ∈ data.selectedPairs})
    {source : Fin fine.card}
    (sourceMem :
      source ∈
        input.packetCellSources pair.1.1 pair.1.2) :
    wz1PaperGridCube rho (input.coarseCellOf pair.1.2) ⊆
      wz1PaperTubeCarrier (coarse.tube pair.1.1) := by
  have pairPositive :=
    data.selectedPairs_subset pair.2
  have cellMem :
      pair.1.2 ∈ input.fineCells :=
    (input.mem_positivePairs_iff pair.1).mp pairPositive |>.1
  exact
    input.parent_cell_containment
      pair.1.1 pair.1.2 source cellMem
      (FineMultiplicityClassData.source_mem_fullFiber
        input data pair sourceMem)
      (FineMultiplicityClassData.cell_subset_carrier
        input data pair sourceMem)

end FineMultiplicityClassData

theorem pureWZ2_prop62_packet_cell_fine_multiplicity_class :
    Nonempty input.FineMultiplicityClassData := by
  let totalMultiplicity : ℕ :=
    ∑ pair ∈ input.positivePairs,
      input.packetCellMultiplicity pair
  rcases
      dyadic_band_pigeonhole
        input.positivePairs input.packetCellMultiplicity
        input.positivePairs_nonempty
        input.positivePair_multiplicity_pos
    with
    ⟨level, selectedPairs, selectedPairsNonempty,
      selectedPairsSubset, multiplicityBand, retention⟩
  let muFine : ℕ := 2 ^ level
  have muFinePos : 0 < muFine := by
    positivity
  let binCount : ℕ :=
    Nat.log 2 totalMultiplicity + 1
  have classRetention :
      totalMultiplicity ≤
        binCount *
          ∑ pair ∈ selectedPairs,
            input.packetCellMultiplicity pair := by
    simpa [totalMultiplicity, binCount,
      Nat.mul_comm] using retention
  exact
    ⟨{
      level := level
      muFine := muFine
      muFine_eq := rfl
      muFine_pos := muFinePos
      selectedPairs := selectedPairs
      selectedPairs_nonempty := selectedPairsNonempty
      selectedPairs_subset := selectedPairsSubset
      multiplicity_band := by
        intro pair pairMem
        have band := multiplicityBand pair pairMem
        simpa [muFine, pow_succ, Nat.mul_comm] using band
      binCount := binCount
      binCount_eq := rfl
      class_retention := classRetention
    }⟩

end PureWZ2Prop62PacketCellInput

end Kakeya.Assouad

end
