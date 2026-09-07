import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4DirectUniversal
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4FixedGridBoundaryRemoval
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4OnePassTreeCleanup
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63PowerScale
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63CrossDegreeAbsorption
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SourceWitnessCoarseShading
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9TerminalFiberSupport
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4NormalizedFineUnionCriticalLower

/-!
# Rich Proposition 6.2 kernel for Proposition 6.3

The public Node 3 kernel intentionally forgets the exact ordinary
normalization of its output coarse pair.  Proposition 6.3 needs that
certificate for its dependent second call.  This Node 4-owned wrapper keeps
the rich result of the already-proved V4 kernel without changing the public
Node 3 interface.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory

attribute [local instance] Classical.propDecidable

/-- Reinterpret the paper-facing balanced cover in the four-degree output as
the Section 6 balanced cover used by the Node 4 source-witness construction. -/
noncomputable def proposition63TerminalBalancedCoverOfFourDegree
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {ambientCover : PureWZ2Section6Cover fine coarse}
    {shading : WZ1PaperTubeShading fine}
    (input : PureWZ2Prop62PacketCellInput ambientCover shading)
    {densityConstant outputParentConstant sourceFiberConstant : ENNReal}
    (certificate : PureWZ2Prop62FourDegreeOutputCertificate input
      densityConstant outputParentConstant sourceFiberConstant) :
    PureWZ2BalancedCoverData certificate.cover
      certificate.refinement.refined certificate.coarseShading where
  point_compatibility := by
    intro sourceIndex parent covered point point_mem
    have parent_eq :
        certificate.cover.toWZ1PaperTubeCover.parent sourceIndex = parent :=
      certificate.cover.toWZ1PaperTubeCover.parent_unique
        sourceIndex parent covered |>.symm
    rw [← parent_eq]
    exact certificate.balanced.point_compatibility sourceIndex point point_mem
  coarse_cubical := certificate.balanced.coarse_cubical
  activeCells := certificate.balanced.activeCells
  coarse_union_eq := certificate.balanced.coarse_union_eq
  cellMass := certificate.balanced.cellMass
  cellMass_pos := certificate.balanced.cellMass_pos
  cellMass_ne_top := certificate.balanced.cellMass_ne_top
  fine_cell_mass := certificate.balanced.fine_cell_mass

/-- The canonical selected-incidence shading of the four-degree output is
exactly any source-witness reconstruction from the same terminal balanced
cover.  In particular, this identifies the Node 3 density theorem with the
Node 4 parent-specific witness construction. -/
theorem proposition63SourceWitnessShading_carrier_eq_selectedIncidence
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {ambientCover : PureWZ2Section6Cover fine coarse}
    {shading : WZ1PaperTubeShading fine}
    (input : PureWZ2Prop62PacketCellInput ambientCover shading)
    {densityConstant outputParentConstant sourceFiberConstant : ENNReal}
    (certificate : PureWZ2Prop62FourDegreeOutputCertificate input
      densityConstant outputParentConstant sourceFiberConstant)
    (sourceWitness : PureWZ2SourceWitnessCoarseShadingData
      (proposition63TerminalBalancedCoverOfFourDegree input certificate)) :
    ∀ parent : Fin certificate.coarse.family.card,
      sourceWitness.shading.carrier parent =
      certificate.selectedIncidenceCoarseShading.carrier parent := by
  intro parent
  have parentCellsEq : sourceWitness.parentCells parent =
      certificate.selectedParentCells parent := by
    rw [sourceWitness.parentCells_eq]
    apply Finset.ext
    intro cell
    unfold sourceWitnessParentCells
      PureWZ2Prop62FourDegreeOutputCertificate.selectedParentCells
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨cellActive, source, parentEq, point, pointFine, pointCell⟩
      refine ⟨cellActive, point, ?_, pointCell⟩
      let indices := wz2PaperFullFiberIndices
        certificate.refinement.selected.family certificate.coarse.family parent
      have sourceFiber : source ∈ indices := by
        dsimp only [indices]
        rw [certificate.cover.fullFiberIndices_eq parent]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ source, parentEq⟩
      let fiber := wz2PaperFullFiberSubfamily
        certificate.refinement.selected.family certificate.coarse.family parent
      let fiberIndex : Fin fiber.family.card :=
        (indices.orderIsoOfFin rfl).symm ⟨source, sourceFiber⟩
      have embeddingEq : fiber.embedding fiberIndex = source :=
        congrArg Subtype.val <|
          (indices.orderIsoOfFin rfl).apply_symm_apply ⟨source, sourceFiber⟩
      refine ⟨fiberIndex, ?_⟩
      simpa only [PureWZ2Prop62FourDegreeOutputCertificate.windowedFullFiberShading,
        restrictPaperShading, fiber, embeddingEq] using pointFine
    · rintro ⟨cellActive, point, pointFiber, pointCell⟩
      rcases pointFiber with ⟨fiberIndex, pointFine⟩
      let fiber := wz2PaperFullFiberSubfamily
        certificate.refinement.selected.family certificate.coarse.family parent
      let source := fiber.embedding fiberIndex
      change Fin (wz2PaperFullFiberIndices
        certificate.refinement.selected.family certificate.coarse.family
          parent).card at fiberIndex
      have sourceFiber :
          source ∈ wz2PaperFullFiberIndices
            certificate.refinement.selected.family certificate.coarse.family
              parent :=
        Finset.orderEmbOfFin_mem _ rfl fiberIndex
      have parentEq :
          certificate.cover.toPaperTubeCover.parent source = parent := by
        exact (certificate.cover.toPaperTubeCover.parent_unique source parent
          ((mem_wz2PaperFullFiberIndices_iff parent source).mp sourceFiber)).symm
      refine ⟨cellActive, source, parentEq, point, ?_, pointCell⟩
      simpa only [PureWZ2Prop62FourDegreeOutputCertificate.windowedFullFiberShading,
        restrictPaperShading, fiber, source] using pointFine
  rw [sourceWitness.shading_carrier_eq,
    certificate.selectedIncidenceCoarseShading_carrier, parentCellsEq]

/-- Carrierwise identification also preserves the indexed shading mass. -/
theorem proposition63SourceWitnessShading_mass_eq_selectedIncidence
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {ambientCover : PureWZ2Section6Cover fine coarse}
    {shading : WZ1PaperTubeShading fine}
    (input : PureWZ2Prop62PacketCellInput ambientCover shading)
    {densityConstant outputParentConstant sourceFiberConstant : ENNReal}
    (certificate : PureWZ2Prop62FourDegreeOutputCertificate input
      densityConstant outputParentConstant sourceFiberConstant)
    (sourceWitness : PureWZ2SourceWitnessCoarseShadingData
      (proposition63TerminalBalancedCoverOfFourDegree input certificate)) :
    sourceWitness.shading.mass =
      certificate.selectedIncidenceCoarseShading.mass := by
  unfold Kakeya.Streamlined.Shading.mass
  apply Finset.sum_congr rfl
  intro parent _
  exact congrArg volume <|
    proposition63SourceWitnessShading_carrier_eq_selectedIncidence
      input certificate sourceWitness parent

/-- The part of Node 3's terminal four-degree certificate which Node 4 uses
for the sharp Lemma 4.7 mass account.  The record deliberately retains the
same terminal fine shading, coarse shading, and Section 6 cover: the
multiplicity bands below are not interchangeable with bounds proved on an
independently selected family. -/
structure Proposition63TerminalMultiplicityCertificate
    {delta rho sigma terminalLoss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : PureWZ2Section6Cover fine coarse)
    (fineShading : WZ1PaperTubeShading fine)
    (coarseShading : WZ1PaperTubeShading coarse) where
  delta_pos : 0 < delta
  fine_cubical : WZ1PaperIsCubicalShading fineShading
  balanced : PureWZ2BalancedCoverData cover fineShading coarseShading
  fine_cell_nested :
    ∀ source point,
      point ∈ fineShading.carrier source →
        ∃ cell ∈ balanced.activeCells,
          wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆
            wz1PaperGridCube rho cell
  sourceWitness : PureWZ2SourceWitnessCoarseShadingData balanced
  sourceWitness_dense :
    sourceWitness.shading.IsLambdaDense
      (Kakeya.realRpowENN rho terminalLoss)
  muFine : ℕ
  muCoarse : ℕ
  W : ℕ
  fiberFloor : ℕ
  regularity : ℕ
  muFine_pos : 0 < muFine
  muCoarse_pos : 0 < muCoarse
  W_pos : 0 < W
  fiberFloor_pos : 0 < fiberFloor
  regularity_pos : 0 < regularity
  packetCells : Finset (Fin coarse.card × WZ2PaperCellIndex)
  packetCells_nonempty : packetCells.Nonempty
  packetCells_eq :
    packetCells =
      ((Finset.univ : Finset (Fin coarse.card)).product
        (wz1PaperActiveCells fineShading delta_pos)).filter
          fun edge =>
            ((wz2PaperFullFiberIndices fine coarse edge.1).filter
              fun sourceIndex =>
                wz1PaperGridCube delta edge.2 ⊆
                  fineShading.carrier sourceIndex).Nonempty
  exact_fine_multiplicity :
    ∀ edge ∈ packetCells,
      ((wz2PaperFullFiberIndices fine coarse edge.1).filter
        fun sourceIndex =>
          wz1PaperGridCube delta edge.2 ⊆
            fineShading.carrier sourceIndex).card =
        muFine
  fineDegreeFloor : ℕ
  fineDegreeFloor_pos : 0 < fineDegreeFloor
  fine_degree_floor :
    ∀ cell ∈ packetCells.image Prod.snd,
      fineDegreeFloor ≤
        (packetCells.filter fun edge => edge.2 = cell).card
  fine_degree_upper :
    ∀ cell ∈ packetCells.image Prod.snd,
      (packetCells.filter fun edge => edge.2 = cell).card ≤
        regularity * fineDegreeFloor
  balanced_cell_mass :
    balanced.cellMass =
      W * volume (wz1PaperGridCube delta (0, 0, 0))
  coarse_multiplicity :
    ∀ cell ∈ balanced.activeCells,
      muCoarse ≤
          (Finset.univ.filter fun parent =>
            wz1PaperGridCube rho cell ⊆
              coarseShading.carrier parent).card ∧
        (Finset.univ.filter fun parent =>
          wz1PaperGridCube rho cell ⊆
            coarseShading.carrier parent).card ≤
          regularity * muCoarse
  fiber_cardinality :
    ∀ parent,
      (fiberFloor : ENNReal) ≤
          wz2PaperFullFiberCount fine coarse parent ∧
        wz2PaperFullFiberCount fine coarse parent <
          2 * (fiberFloor : ENNReal)
  fine_multiplicity_floor :
    ∀ parent,
      ((55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN (delta / rho)
            (2 - sigma + terminalLoss)) *
        (wz2PaperFullFiberCount fine coarse parent : ENNReal) ≤
      (muFine : ENNReal)
  coarse_multiplicity_floor :
    (55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN rho (2 - sigma + terminalLoss) *
        coarse.enncard ≤
      (muCoarse : ENNReal)
  coarse_multiplicity_upper :
    (regularity * muCoarse : ℕ) ≤
      Kakeya.realRpowENN rho (2 - sigma - terminalLoss) *
        coarse.enncard
  fine_multiplicity_upper : ∀ parent,
    (muFine : ENNReal) ≤
      Kakeya.realRpowENN (delta / rho)
          (2 - sigma - terminalLoss) *
        ((wz2PaperFullFiberIndices fine coarse parent).card : ENNReal)

/-- Forget the producer-specific packet input while retaining every terminal
multiplicity fact on the exact output families. -/
noncomputable def proposition63TerminalMultiplicityCertificateOfFourDegree
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {ambientCover : PureWZ2Section6Cover fine coarse}
    {shading : WZ1PaperTubeShading fine}
    (input : PureWZ2Prop62PacketCellInput ambientCover shading)
    {densityConstant outputParentConstant sourceFiberConstant : ENNReal}
    {sigma terminalLoss : ℝ}
    (certificate : PureWZ2Prop62FourDegreeOutputCertificate input
      densityConstant outputParentConstant sourceFiberConstant)
    (fine_multiplicity_floor :
      ∀ parent,
        ((55296 * Kakeya.deltaTubeVolume 1) *
            Kakeya.realRpowENN (delta / rho)
              (2 - sigma + terminalLoss)) *
          (wz2PaperFullFiberCount
            certificate.refinement.selected.family
            certificate.coarse.family parent : ENNReal) ≤
        (certificate.muFine : ENNReal))
    (coarse_multiplicity_floor :
      (55296 * Kakeya.deltaTubeVolume 1) *
            Kakeya.realRpowENN rho (2 - sigma + terminalLoss) *
          certificate.coarse.family.enncard ≤
        (certificate.muCoarse : ENNReal))
    (coarse_multiplicity_upper :
      (certificate.regularity * certificate.muCoarse : ℕ) ≤
        Kakeya.realRpowENN rho (2 - sigma - terminalLoss) *
          certificate.coarse.family.enncard)
    (fine_multiplicity_upper : ∀ parent,
      (certificate.muFine : ENNReal) ≤
        Kakeya.realRpowENN (delta / rho)
            (2 - sigma - terminalLoss) *
          ((wz2PaperFullFiberIndices
            certificate.refinement.selected.family
            certificate.coarse.family parent).card : ENNReal))
    (fineDegreeFloor : ℕ)
    (fineDegreeFloor_pos : 0 < fineDegreeFloor)
    (fine_degree_floor :
      ∀ cell ∈ certificate.packetCells.image Prod.snd,
        fineDegreeFloor ≤
          (certificate.packetCells.filter fun edge => edge.2 = cell).card)
    (fine_degree_upper :
      ∀ cell ∈ certificate.packetCells.image Prod.snd,
        (certificate.packetCells.filter fun edge => edge.2 = cell).card ≤
          certificate.regularity * fineDegreeFloor)
    (selectedIncidence_dense :
      certificate.selectedIncidenceCoarseShading.IsLambdaDense
        (Kakeya.realRpowENN rho terminalLoss)) :
    Proposition63TerminalMultiplicityCertificate certificate.cover
      (sigma := sigma) (terminalLoss := terminalLoss)
      certificate.refinement.refined certificate.coarseShading := by
  let terminalBalanced :=
    proposition63TerminalBalancedCoverOfFourDegree input certificate
  let sourceWitness := Classical.choice <|
    source_witness_coarse_shading terminalBalanced
  have sourceWitnessDense :
      sourceWitness.shading.IsLambdaDense
        (Kakeya.realRpowENN rho terminalLoss) := by
    rw [Kakeya.Streamlined.Shading.IsLambdaDense] at selectedIncidence_dense
    rw [Kakeya.Streamlined.Shading.IsLambdaDense]
    rw [proposition63SourceWitnessShading_mass_eq_selectedIncidence
      input certificate sourceWitness]
    exact selectedIncidence_dense
  exact {
    delta_pos := input.delta_pos
    fine_cubical := certificate.refined_cubical
    balanced := terminalBalanced
    fine_cell_nested := certificate.fine_cell_nested
    sourceWitness := sourceWitness
    sourceWitness_dense := sourceWitnessDense
    muFine := certificate.muFine
    muCoarse := certificate.muCoarse
    W := certificate.W
    fiberFloor := certificate.fiberFloor
    regularity := certificate.regularity
    muFine_pos := certificate.muFine_pos
    muCoarse_pos := certificate.muCoarse_pos
    W_pos := certificate.W_pos
    fiberFloor_pos := certificate.fiberFloor_pos
    regularity_pos := certificate.regularity_pos
    packetCells := certificate.packetCells
    packetCells_nonempty := certificate.packetCells_nonempty
    packetCells_eq := certificate.packetCells_eq
    exact_fine_multiplicity := certificate.exact_fine_multiplicity
    fineDegreeFloor := fineDegreeFloor
    fineDegreeFloor_pos := fineDegreeFloor_pos
    fine_degree_floor := fine_degree_floor
    fine_degree_upper := fine_degree_upper
    balanced_cell_mass := certificate.balanced_cell_mass
    coarse_multiplicity := by
      intro cell cell_mem
      apply certificate.coarse_multiplicity cell
      rw [certificate.active_coarse_cells_eq]
      exact cell_mem
    fiber_cardinality := certificate.fiber_cardinality
    fine_multiplicity_floor := fine_multiplicity_floor
    coarse_multiplicity_floor := coarse_multiplicity_floor
    coarse_multiplicity_upper := coarse_multiplicity_upper
    fine_multiplicity_upper := fine_multiplicity_upper
  }

namespace Proposition63TerminalMultiplicityCertificate

variable
    {delta rho sigma terminalLoss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (certificate : Proposition63TerminalMultiplicityCertificate
      (sigma := sigma) (terminalLoss := terminalLoss)
      cover fineShading coarseShading)

/-- The exact terminal coarse multiplicity band, stated pointwise on the
coarse shading consumed by Node 4. -/
theorem coarse_pointMultiplicity_band
    {point : Point3} (point_mem : point ∈ coarseShading.union) :
    (certificate.muCoarse : ENNReal) ≤
        coarseShading.pointMultiplicity point ∧
      (coarseShading.pointMultiplicity point : ENNReal) ≤
        (certificate.regularity * certificate.muCoarse : ℕ) := by
  rw [certificate.balanced.coarse_union_eq] at point_mem
  rcases Set.mem_iUnion₂.mp point_mem with
    ⟨cell, cell_mem, point_cell⟩
  have count_eq :
      coarseShading.pointMultiplicity point =
        (Finset.univ.filter fun parent =>
          wz1PaperGridCube rho cell ⊆
            coarseShading.carrier parent).card := by
    change
      (Finset.univ.filter fun parent =>
        point ∈ coarseShading.carrier parent).card = _
    congr 1
    ext parent
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro parent_point
      have point_index : wz1PaperGridIndex rho point = cell :=
        (mem_wz1PaperGridCube rho cell point).mp point_cell
      simpa only [point_index] using
        certificate.balanced.coarse_cubical parent point parent_point
    · intro whole_cell
      exact whole_cell point_cell
  rw [count_eq]
  constructor
  · exact_mod_cast (certificate.coarse_multiplicity cell cell_mem).1
  · exact_mod_cast (certificate.coarse_multiplicity cell cell_mem).2

/-- The strict geometric fiber of a Section 6 cover is exactly the fiber of
its unique parent map. -/
private theorem fullFiberIndices_eq
    (parent : Fin coarse.card) :
    wz2PaperFullFiberIndices fine coarse parent =
      cover.toWZ1PaperTubeCover.fiberIndices parent := by
  ext source
  simp only [wz2PaperFullFiberIndices, WZ1PaperTubeCover.fiberIndices,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro covered
    exact (cover.toWZ1PaperTubeCover.parent_unique
      source parent covered).symm
  · intro parent_eq
    rw [← parent_eq]
    exact cover.toWZ1PaperTubeCover.parent_covers source

/-- At every point where one terminal parent fiber is present, its
multiplicity is exactly the terminal packet multiplicity `muFine`. -/
theorem fiber_pointMultiplicity_eq_muFine_of_pos
    (parent : Fin coarse.card) (point : Point3)
    (positive : 0 < cover.toWZ1PaperTubeCover.fiberPointMultiplicity
      fineShading parent point) :
    cover.toWZ1PaperTubeCover.fiberPointMultiplicity
        fineShading parent point = certificate.muFine := by
  let cell := wz1PaperGridIndex delta point
  let fiberSources :=
    (cover.toWZ1PaperTubeCover.fiberIndices parent).filter
      fun sourceIndex => point ∈ fineShading.carrier sourceIndex
  have fiber_nonempty : fiberSources.Nonempty := by
    change 0 < fiberSources.card at positive
    exact Finset.card_pos.mp positive
  rcases fiber_nonempty with ⟨sourceIndex, source_mem⟩
  have source_data := Finset.mem_filter.mp source_mem
  have source_fiber :
      sourceIndex ∈ wz2PaperFullFiberIndices fine coarse parent := by
    rw [fullFiberIndices_eq (cover := cover) parent]
    exact source_data.1
  have whole_cell :
      wz1PaperGridCube delta cell ⊆
        fineShading.carrier sourceIndex :=
    certificate.fine_cubical sourceIndex point source_data.2
  have cell_active :
      cell ∈ wz1PaperActiveCells fineShading certificate.delta_pos := by
    rw [mem_wz1PaperActiveCells]
    refine ⟨?_, ⟨point, ⟨sourceIndex, source_data.2⟩, ?_⟩⟩
    · exact paper_point_gridIndex_in_window certificate.delta_pos
        (fineShading.subset_body sourceIndex source_data.2).2
    · exact (mem_wz1PaperGridCube delta cell point).mpr rfl
  have packet_mem : (parent, cell) ∈ certificate.packetCells := by
    rw [certificate.packetCells_eq]
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_product.mpr ⟨Finset.mem_univ parent, cell_active⟩,
      ⟨sourceIndex, Finset.mem_filter.mpr ⟨source_fiber, whole_cell⟩⟩⟩
  have active_fiber_eq :
      fiberSources =
        (wz2PaperFullFiberIndices fine coarse parent).filter
          fun candidate =>
            wz1PaperGridCube delta cell ⊆
              fineShading.carrier candidate := by
    dsimp only [fiberSources]
    rw [← fullFiberIndices_eq (cover := cover) parent]
    apply Finset.filter_congr
    intro candidate _candidate_fiber
    constructor
    · intro candidate_point
      exact certificate.fine_cubical
        candidate point candidate_point
    · intro candidate_cell
      exact candidate_cell
        ((mem_wz1PaperGridCube delta cell point).mpr rfl)
  change fiberSources.card = certificate.muFine
  rw [active_fiber_eq]
  exact certificate.exact_fine_multiplicity (parent, cell) packet_mem

/-- Uniform upper bound for every terminal fiber point multiplicity. -/
theorem fiber_pointMultiplicity_le
    (parent : Fin coarse.card) (point : Point3) :
    (cover.toWZ1PaperTubeCover.fiberPointMultiplicity
        fineShading parent point : ENNReal) ≤ certificate.muFine := by
  by_cases positive : 0 < cover.toWZ1PaperTubeCover.fiberPointMultiplicity
      fineShading parent point
  · rw [certificate.fiber_pointMultiplicity_eq_muFine_of_pos
      parent point positive]
  · have zero : cover.toWZ1PaperTubeCover.fiberPointMultiplicity
        fineShading parent point = 0 := Nat.eq_zero_of_not_pos positive
    rw [zero]
    simp

/-- The terminal fine point multiplicity is the sum of the multiplicities in
its disjoint complete parent fibers. -/
private theorem fine_pointMultiplicity_eq_sum_fibers
    (point : Point3) :
    fineShading.pointMultiplicity point =
      ∑ parent : Fin coarse.card,
        cover.toWZ1PaperTubeCover.fiberPointMultiplicity
          fineShading parent point := by
  let fineAtPoint : Finset (Fin fine.card) :=
    Finset.univ.filter fun source => point ∈ fineShading.carrier source
  have mapsTo :
      Set.MapsTo cover.toWZ1PaperTubeCover.parent
        (fineAtPoint : Set (Fin fine.card))
        (Finset.univ : Finset (Fin coarse.card)) := by
    intro source _sourceMem
    exact Finset.mem_univ _
  have fiberCard : ∀ parent,
      (fineAtPoint.filter fun source =>
          cover.toWZ1PaperTubeCover.parent source = parent).card =
        cover.toWZ1PaperTubeCover.fiberPointMultiplicity
          fineShading parent point := by
    intro parent
    congr 1
    ext source
    simp only [fineAtPoint, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨source_point, source_parent⟩
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ source, source_parent⟩,
          source_point⟩
    · intro source_mem
      have source_data := Finset.mem_filter.mp source_mem
      exact
        ⟨source_data.2,
          (Finset.mem_filter.mp source_data.1).2⟩
  change fineAtPoint.card = _
  rw [Finset.card_eq_sum_card_fiberwise mapsTo]
  exact Finset.sum_congr rfl fun parent _ => fiberCard parent

/-- Bound the fine point multiplicity directly from a public packet-degree
bound and a uniform complete-fiber multiplicity cap.  This producer-level
form is used while the terminal certificate itself is being assembled. -/
theorem fourDegree_fine_pointMultiplicity_le_of_packet_degree
    {ambientFine : Kakeya.Streamlined.TubeFamily delta}
    {ambientCoarse : Kakeya.Streamlined.TubeFamily rho}
    {ambientCover : PureWZ2Section6Cover ambientFine ambientCoarse}
    {ambientShading : WZ1PaperTubeShading ambientFine}
    {input : PureWZ2Prop62PacketCellInput ambientCover ambientShading}
    {densityConstant outputParentConstant sourceFiberConstant : ENNReal}
    (output : PureWZ2Prop62FourDegreeOutputCertificate input
      densityConstant outputParentConstant sourceFiberConstant)
    (fineDegree : ℕ)
    (fine_degree_upper :
      ∀ cell ∈ output.packetCells.image Prod.snd,
        (output.packetCells.filter fun edge => edge.2 = cell).card ≤
          output.regularity * fineDegree)
    (fiber_upper : ∀ parent point,
      (output.cover.toWZ1PaperTubeCover.fiberPointMultiplicity
          output.refinement.refined parent point : ENNReal) ≤ output.muFine)
    (point : Point3) :
    output.refinement.refined.pointMultiplicity point ≤
      (output.regularity * fineDegree) * output.muFine := by
  by_cases point_mem : point ∈ output.refinement.refined.union
  · let cell := wz1PaperGridIndex delta point
    let activeParents : Finset (Fin output.coarse.family.card) :=
      Finset.univ.filter fun parent =>
        0 < output.cover.toWZ1PaperTubeCover.fiberPointMultiplicity
          output.refinement.refined parent point
    let packetsAt := output.packetCells.filter fun edge => edge.2 = cell
    have point_cell : point ∈ wz1PaperGridCube delta cell :=
      (mem_wz1PaperGridCube delta cell point).mpr rfl
    have cell_active :
        cell ∈ wz1PaperActiveCells output.refinement.refined input.delta_pos := by
      rw [mem_wz1PaperActiveCells]
      refine ⟨?_, ⟨point, point_mem, point_cell⟩⟩
      rcases point_mem with ⟨source, source_point⟩
      exact paper_point_gridIndex_in_window input.delta_pos
        (output.refinement.refined.subset_body source source_point).2
    have active_to_packet : ∀ parent ∈ activeParents,
        (parent, cell) ∈ packetsAt := by
      intro parent parent_mem
      have positive := (Finset.mem_filter.mp parent_mem).2
      rcases Finset.card_pos.mp positive with ⟨source, source_mem⟩
      have source_data := Finset.mem_filter.mp source_mem
      have source_fiber : source ∈ wz2PaperFullFiberIndices
          output.refinement.selected.family output.coarse.family parent := by
        rw [fullFiberIndices_eq (cover := output.cover) parent]
        exact source_data.1
      have whole_cell : wz1PaperGridCube delta cell ⊆
          output.refinement.refined.carrier source :=
        output.refined_cubical source point source_data.2
      exact Finset.mem_filter.mpr ⟨by
        rw [output.packetCells_eq]
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨Finset.mem_univ parent, cell_active⟩,
            ⟨source, Finset.mem_filter.mpr ⟨source_fiber, whole_cell⟩⟩⟩,
        rfl⟩
    have active_card_le : activeParents.card ≤ packetsAt.card := by
      apply Finset.card_le_card_of_injective
        (f := fun parent : {parent // parent ∈ activeParents} =>
          ⟨(parent.1, cell), active_to_packet parent.1 parent.2⟩)
      intro first second equality
      apply Subtype.ext
      exact congrArg Prod.fst (congrArg Subtype.val equality)
    have cell_mem : cell ∈ output.packetCells.image Prod.snd := by
      rcases point_mem with ⟨source, source_point⟩
      let parent := output.cover.toWZ1PaperTubeCover.parent source
      have source_fiber : source ∈ wz2PaperFullFiberIndices
          output.refinement.selected.family output.coarse.family parent := by
        rw [fullFiberIndices_eq (cover := output.cover) parent]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ source, rfl⟩
      have whole_cell : wz1PaperGridCube delta cell ⊆
          output.refinement.refined.carrier source :=
        output.refined_cubical source point source_point
      have pair_mem : (parent, cell) ∈ output.packetCells := by
        rw [output.packetCells_eq]
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨Finset.mem_univ parent, cell_active⟩,
            ⟨source, Finset.mem_filter.mpr ⟨source_fiber, whole_cell⟩⟩⟩
      exact Finset.mem_image.mpr ⟨(parent, cell), pair_mem, rfl⟩
    have sum_active :
        (∑ parent : Fin output.coarse.family.card,
            output.cover.toWZ1PaperTubeCover.fiberPointMultiplicity
              output.refinement.refined parent point) =
          ∑ parent ∈ activeParents,
            output.cover.toWZ1PaperTubeCover.fiberPointMultiplicity
              output.refinement.refined parent point := by
      rw [Finset.sum_subset (Finset.subset_univ activeParents)]
      intro parent _ parent_not_active
      have not_positive : ¬0 <
          output.cover.toWZ1PaperTubeCover.fiberPointMultiplicity
            output.refinement.refined parent point := by
        intro positive
        exact parent_not_active <| Finset.mem_filter.mpr
          ⟨Finset.mem_univ parent, positive⟩
      exact Nat.eq_zero_of_not_pos not_positive
    rw [fine_pointMultiplicity_eq_sum_fibers
      (cover := output.cover) (fineShading := output.refinement.refined) point,
      sum_active]
    calc
      (∑ parent ∈ activeParents,
          output.cover.toWZ1PaperTubeCover.fiberPointMultiplicity
            output.refinement.refined parent point) ≤
          ∑ _parent ∈ activeParents, output.muFine := by
        exact Finset.sum_le_sum fun parent _ => by
          exact_mod_cast fiber_upper parent point
      _ = activeParents.card * output.muFine := by simp
      _ ≤ packetsAt.card * output.muFine :=
        Nat.mul_le_mul_right output.muFine active_card_le
      _ ≤ (output.regularity * fineDegree) * output.muFine :=
        Nat.mul_le_mul_right output.muFine <|
          fine_degree_upper cell cell_mem
  · have point_zero : output.refinement.refined.pointMultiplicity point = 0 := by
      simp only [Kakeya.Streamlined.Shading.pointMultiplicity]
      apply Finset.card_eq_zero.mpr
      rw [Finset.filter_eq_empty_iff]
      intro source _ source_point
      exact point_mem ⟨source, source_point⟩
    rw [point_zero]
    simp

/-- Every selected fine cell contributes one exact `muFine` packet for each
of its incident terminal parents.  Consequently the total fine multiplicity
through any point of that cell is at least the terminal fine-degree floor
times `muFine`. -/
theorem fine_pointMultiplicity_lower
    (cell : WZ2PaperCellIndex)
    (cell_mem : cell ∈ certificate.packetCells.image Prod.snd)
    (point : Point3)
    (point_mem : point ∈ wz1PaperGridCube delta cell) :
    (certificate.fineDegreeFloor * certificate.muFine : ℕ) ≤
      fineShading.pointMultiplicity point := by
  let packetsAt :=
    certificate.packetCells.filter fun edge => edge.2 = cell
  let parents := packetsAt.image Prod.fst
  have parents_card : parents.card = packetsAt.card := by
    apply Finset.card_image_iff.mpr
    intro first first_mem second second_mem parent_eq
    have first_cell : first.2 = cell :=
      (Finset.mem_filter.mp first_mem).2
    have second_cell : second.2 = cell :=
      (Finset.mem_filter.mp second_mem).2
    exact Prod.ext parent_eq (first_cell.trans second_cell.symm)
  have fiber_eq : ∀ parent ∈ parents,
      cover.toWZ1PaperTubeCover.fiberPointMultiplicity
          fineShading parent point = certificate.muFine := by
    intro parent parent_mem
    rcases Finset.mem_image.mp parent_mem with
      ⟨edge, edge_mem, edge_parent⟩
    have packet_mem : edge ∈ certificate.packetCells :=
      (Finset.mem_filter.mp edge_mem).1
    have edge_cell : edge.2 = cell :=
      (Finset.mem_filter.mp edge_mem).2
    have point_index : wz1PaperGridIndex delta point = cell :=
      (mem_wz1PaperGridCube delta cell point).mp point_mem
    have active_fiber_eq :
        (cover.toWZ1PaperTubeCover.fiberIndices parent).filter
            (fun source => point ∈ fineShading.carrier source) =
          (wz2PaperFullFiberIndices fine coarse edge.1).filter
            (fun source =>
              wz1PaperGridCube delta edge.2 ⊆
                fineShading.carrier source) := by
      rw [← edge_parent]
      rw [← fullFiberIndices_eq (cover := cover) edge.1]
      apply Finset.filter_congr
      intro source _source_fiber
      constructor
      · intro source_point
        have whole := certificate.fine_cubical source point source_point
        simpa [point_index, edge_cell] using whole
      · intro whole
        exact whole (by simpa [edge_cell] using point_mem)
    change
      ((cover.toWZ1PaperTubeCover.fiberIndices parent).filter
        fun source => point ∈ fineShading.carrier source).card =
          certificate.muFine
    rw [active_fiber_eq]
    exact certificate.exact_fine_multiplicity edge packet_mem
  have parents_sum :
      ∑ parent ∈ parents,
          cover.toWZ1PaperTubeCover.fiberPointMultiplicity
            fineShading parent point =
        parents.card * certificate.muFine := by
    calc
      (∑ parent ∈ parents,
          cover.toWZ1PaperTubeCover.fiberPointMultiplicity
            fineShading parent point) =
          ∑ _parent ∈ parents, certificate.muFine := by
        exact Finset.sum_congr rfl fiber_eq
      _ = parents.card * certificate.muFine := by simp
  calc
    certificate.fineDegreeFloor * certificate.muFine ≤
        packetsAt.card * certificate.muFine :=
      Nat.mul_le_mul_right certificate.muFine
        (certificate.fine_degree_floor cell cell_mem)
    _ = parents.card * certificate.muFine := by rw [parents_card]
    _ = ∑ parent ∈ parents,
          cover.toWZ1PaperTubeCover.fiberPointMultiplicity
            fineShading parent point := parents_sum.symm
    _ ≤ ∑ parent : Fin coarse.card,
          cover.toWZ1PaperTubeCover.fiberPointMultiplicity
            fineShading parent point := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro parent _parent_univ _parent_not_mem
      exact Nat.zero_le _
    _ = fineShading.pointMultiplicity point :=
      (fine_pointMultiplicity_eq_sum_fibers
        (cover := cover) (fineShading := fineShading) point).symm

/-- At a point of the terminal fine shading, the total point multiplicity is
exactly the number of terminal parents incident to its fine cell times the
common exact fiber multiplicity. -/
theorem fine_pointMultiplicity_eq_packetDegree_mul
    {point : Point3} (point_mem : point ∈ fineShading.union) :
    fineShading.pointMultiplicity point =
      (certificate.packetCells.filter fun edge =>
          edge.2 = wz1PaperGridIndex delta point).card * certificate.muFine := by
  let cell := wz1PaperGridIndex delta point
  let activeParents : Finset (Fin coarse.card) :=
    Finset.univ.filter fun parent =>
      0 < cover.toWZ1PaperTubeCover.fiberPointMultiplicity
        fineShading parent point
  let packetsAt := certificate.packetCells.filter fun edge => edge.2 = cell
  have point_cell : point ∈ wz1PaperGridCube delta cell :=
    (mem_wz1PaperGridCube delta cell point).mpr rfl
  have cell_active :
      cell ∈ wz1PaperActiveCells fineShading certificate.delta_pos := by
    rw [mem_wz1PaperActiveCells]
    refine ⟨?_, ⟨point, point_mem, point_cell⟩⟩
    rcases point_mem with ⟨source, source_point⟩
    exact paper_point_gridIndex_in_window certificate.delta_pos
      (fineShading.subset_body source source_point).2
  have active_iff_packet : ∀ parent, parent ∈ activeParents ↔
      (parent, cell) ∈ packetsAt := by
    intro parent
    simp only [activeParents, packetsAt, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · intro positive
      refine ⟨?_, trivial⟩
      rw [certificate.packetCells_eq]
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr
        ⟨Finset.mem_univ parent, cell_active⟩, ?_⟩
      rcases Finset.card_pos.mp positive with ⟨source, source_mem⟩
      have source_data := Finset.mem_filter.mp source_mem
      have source_fiber : source ∈
          wz2PaperFullFiberIndices fine coarse parent := by
        rw [fullFiberIndices_eq (cover := cover) parent]
        exact source_data.1
      exact ⟨source, Finset.mem_filter.mpr ⟨source_fiber,
        certificate.fine_cubical source point source_data.2⟩⟩
    · rintro ⟨packet_mem, _⟩
      rw [certificate.packetCells_eq] at packet_mem
      rcases (Finset.mem_filter.mp packet_mem).2 with ⟨source, source_mem⟩
      apply Finset.card_pos.mpr
      have source_parent : cover.toWZ1PaperTubeCover.parent source = parent := by
        exact (cover.toWZ1PaperTubeCover.parent_unique source parent
          ((mem_wz2PaperFullFiberIndices_iff parent source).mp
            (Finset.mem_filter.mp source_mem).1)).symm
      exact ⟨source, Finset.mem_filter.mpr ⟨
        Finset.mem_filter.mpr ⟨Finset.mem_univ source, source_parent⟩,
        (Finset.mem_filter.mp source_mem).2 point_cell⟩⟩
  have active_card : activeParents.card = packetsAt.card := by
    apply Finset.card_bij (fun parent _ => (parent, cell))
    · intro parent parent_mem
      exact (active_iff_packet parent).mp parent_mem
    · intro first first_mem second second_mem pair_eq
      exact congrArg Prod.fst pair_eq
    · intro edge edge_mem
      obtain ⟨parent, edgeCell⟩ := edge
      have edge_cell : edgeCell = cell := (Finset.mem_filter.mp edge_mem).2
      subst edgeCell
      exact ⟨parent, (active_iff_packet parent).mpr edge_mem, rfl⟩
  have sum_active :
      (∑ parent : Fin coarse.card,
          cover.toWZ1PaperTubeCover.fiberPointMultiplicity
            fineShading parent point) =
        ∑ parent ∈ activeParents,
          cover.toWZ1PaperTubeCover.fiberPointMultiplicity
            fineShading parent point := by
    rw [Finset.sum_subset (Finset.subset_univ activeParents)]
    intro parent _ parent_not_active
    have not_positive : ¬0 <
        cover.toWZ1PaperTubeCover.fiberPointMultiplicity
          fineShading parent point := by
      intro positive
      exact parent_not_active <| Finset.mem_filter.mpr
        ⟨Finset.mem_univ parent, positive⟩
    exact Nat.eq_zero_of_not_pos not_positive
  rw [fine_pointMultiplicity_eq_sum_fibers
    (cover := cover) (fineShading := fineShading) point, sum_active]
  calc
    (∑ parent ∈ activeParents,
        cover.toWZ1PaperTubeCover.fiberPointMultiplicity
          fineShading parent point) =
        ∑ _parent ∈ activeParents, certificate.muFine := by
      apply Finset.sum_congr rfl
      intro parent parent_mem
      exact certificate.fiber_pointMultiplicity_eq_muFine_of_pos parent point
        ((Finset.mem_filter.mp parent_mem).2)
    _ = activeParents.card * certificate.muFine := by simp
    _ = packetsAt.card * certificate.muFine := by rw [active_card]
    _ = (certificate.packetCells.filter fun edge =>
          edge.2 = wz1PaperGridIndex delta point).card *
        certificate.muFine := rfl

/-- The terminal fine shading inherits the upper end of the same fine-degree
dyadic class used for its lower point-multiplicity bound. -/
theorem fine_pointMultiplicity_upper
    (point : Point3) :
    (fineShading.pointMultiplicity point : ENNReal) ≤
      ((certificate.regularity * certificate.fineDegreeFloor : ℕ) : ENNReal) *
        certificate.muFine := by
  by_cases point_mem : point ∈ fineShading.union
  · have packet_mem : wz1PaperGridIndex delta point ∈
        certificate.packetCells.image Prod.snd := by
      rcases point_mem with ⟨source, source_point⟩
      let parent := cover.toWZ1PaperTubeCover.parent source
      let cell := wz1PaperGridIndex delta point
      have source_fiber : source ∈
          wz2PaperFullFiberIndices fine coarse parent := by
        rw [fullFiberIndices_eq (cover := cover) parent]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ source, rfl⟩
      have whole_cell : wz1PaperGridCube delta cell ⊆
          fineShading.carrier source :=
        certificate.fine_cubical source point source_point
      have cell_active : cell ∈
          wz1PaperActiveCells fineShading certificate.delta_pos := by
        rw [mem_wz1PaperActiveCells]
        refine ⟨?_, ⟨point, ⟨source, source_point⟩,
          (mem_wz1PaperGridCube delta cell point).mpr rfl⟩⟩
        exact paper_point_gridIndex_in_window certificate.delta_pos
          (fineShading.subset_body source source_point).2
      have pair_mem : (parent, cell) ∈ certificate.packetCells := by
        rw [certificate.packetCells_eq]
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨Finset.mem_univ parent, cell_active⟩,
            ⟨source, Finset.mem_filter.mpr ⟨source_fiber, whole_cell⟩⟩⟩
      exact Finset.mem_image.mpr ⟨(parent, cell), pair_mem, rfl⟩
    rw [certificate.fine_pointMultiplicity_eq_packetDegree_mul point_mem]
    exact_mod_cast Nat.mul_le_mul_right certificate.muFine
      (certificate.fine_degree_upper _ packet_mem)
  · have point_zero : fineShading.pointMultiplicity point = 0 := by
      simp only [Kakeya.Streamlined.Shading.pointMultiplicity]
      apply Finset.card_eq_zero.mpr
      rw [Finset.filter_eq_empty_iff]
      intro source _ source_point
      exact point_mem ⟨source, source_point⟩
    rw [point_zero]
    simp

/-- Integrating the exact pointwise fine-degree upper bound. -/
theorem fine_mass_le_degree_mul_volume :
    fineShading.mass ≤
      (((certificate.regularity * certificate.fineDegreeFloor : ℕ) :
          ENNReal) * certificate.muFine) *
        volume fineShading.union := by
  apply mass_le_of_pointMultiplicity_le
  intro point _point_mem
  exact certificate.fine_pointMultiplicity_upper point

/-- Every point of the exact terminal fine shading lies in a selected packet
cell, so the preceding packet count gives a uniform total multiplicity
floor on the whole terminal shaded union. -/
theorem fine_pointMultiplicity_floor_on_union
    {point : Point3} (point_mem : point ∈ fineShading.union) :
    (certificate.fineDegreeFloor * certificate.muFine : ℕ) ≤
      fineShading.pointMultiplicity point := by
  rcases point_mem with ⟨source, source_point⟩
  let parent := cover.toWZ1PaperTubeCover.parent source
  let cell := wz1PaperGridIndex delta point
  have source_fiber : source ∈ wz2PaperFullFiberIndices fine coarse parent := by
    rw [fullFiberIndices_eq (cover := cover) parent]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ source, rfl⟩
  have whole_cell :
      wz1PaperGridCube delta cell ⊆ fineShading.carrier source :=
    certificate.fine_cubical source point source_point
  have cell_active :
      cell ∈ wz1PaperActiveCells fineShading certificate.delta_pos := by
    rw [mem_wz1PaperActiveCells]
    refine ⟨?_, ⟨point, ⟨source, source_point⟩, ?_⟩⟩
    · exact paper_point_gridIndex_in_window certificate.delta_pos
        (fineShading.subset_body source source_point).2
    · exact (mem_wz1PaperGridCube delta cell point).mpr rfl
  have packet_mem : (parent, cell) ∈ certificate.packetCells := by
    rw [certificate.packetCells_eq]
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr
          ⟨Finset.mem_univ parent, cell_active⟩,
        ⟨source, Finset.mem_filter.mpr ⟨source_fiber, whole_cell⟩⟩⟩
  have cell_mem : cell ∈ certificate.packetCells.image Prod.snd :=
    Finset.mem_image.mpr ⟨(parent, cell), packet_mem, rfl⟩
  exact certificate.fine_pointMultiplicity_lower
    cell cell_mem point ((mem_wz1PaperGridCube delta cell point).mpr rfl)

end Proposition63TerminalMultiplicityCertificate

/-- Forget one coarse-scale cell of strict axial slack.  This is kept as a
separate helper because the ordinary re-entry record itself stores only the
weaker reusable quarter-height window. -/
theorem proposition63_reentry_axial_window_of_margin
    {delta sigma sourceLoss normalizationLoss : ℝ}
    {croppedFamily : Kakeya.Streamlined.TubeFamily delta}
    {croppedShading : WZ1PaperTubeShading croppedFamily}
    {normalizationExponent : ℕ}
    (reentry : PureWZ2PropStickyReentryData
      (sigma := sigma) croppedShading normalizationExponent
        sourceLoss normalizationLoss)
    (rho : WZ2PaperRequestedScale delta)
    (margin : ∀ index point,
      point ∈ reentry.geometry.frame ''
          reentry.geometry.ordinaryRefined.carrier index →
        |point (2 : Fin 3)| + rho.1 ≤ 1 / 8) :
    ∀ index point,
      point ∈ reentry.geometry.frame ''
          reentry.geometry.ordinaryRefined.carrier index →
        |point (2 : Fin 3)| ≤ 1 / 8 := by
  intro index point pointMem
  have rhoNonnegative : 0 ≤ rho.1 :=
    reentry.ordinarySource.extremal.delta_pos.le.trans rho.2.1
  exact (le_add_of_nonneg_right rhoNonnegative).trans
    (margin index point pointMem)

/-- Convert a source-scale packet-density lower bound into the target-scale
power used by Node 4's first complete-fiber regularization. -/
theorem proposition63_terminal_fiber_mass_lower_of_source_power
    {delta rho outputLoss packetLoss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : PureWZ2Section6Cover fine coarse)
    (fineShading : WZ1PaperTubeShading fine)
    (fiberFloor : ℕ)
    (deltaPos : 0 < delta) (deltaOne : delta ≤ 1)
    (rhoPos : 0 < rho)
    (rhoUpper : rho ≤ Real.rpow delta outputLoss)
    (outputLossNonnegative : 0 ≤ outputLoss)
    (packetLossBudget : packetLoss ≤ outputLoss * outputLoss)
    (packetLower : ∀ parent : Fin coarse.card,
      Kakeya.realRpowENN delta packetLoss * (fiberFloor : ENNReal) *
          Kakeya.realRpowENN delta 2 ≤
        (restrictPaperShading
          (wz2PaperFullFiberSubfamily fine coarse parent) fineShading).mass) :
    ∀ parent : Fin coarse.card,
      Kakeya.realRpowENN rho outputLoss * (fiberFloor : ENNReal) *
          Kakeya.realRpowENN delta 2 ≤
        cover.toPaperTubeCover.fiberShadedMass fineShading parent := by
  intro parent
  have rhoPower : Kakeya.realRpowENN rho outputLoss ≤
      Kakeya.realRpowENN delta (outputLoss * outputLoss) :=
    pure_wz2_target_power_upper deltaPos rhoPos.le rhoUpper
      outputLossNonnegative
  have deltaPower : Kakeya.realRpowENN delta
        (outputLoss * outputLoss) ≤ Kakeya.realRpowENN delta packetLoss :=
    pure_wz2_rpowENN_antitone deltaPos deltaOne packetLossBudget
  have massEq :
      (restrictPaperShading (wz2PaperFullFiberSubfamily fine coarse parent)
        fineShading).mass =
        cover.toPaperTubeCover.fiberShadedMass fineShading parent := by
    calc
      _ = ∑ source ∈ wz2PaperFullFiberIndices fine coarse parent,
          volume (fineShading.carrier source) := by
        simpa only [wz2PaperFullFiberSubfamily] using
          restrictPaperShading_fromFinset_mass fineShading
            (wz2PaperFullFiberIndices fine coarse parent)
      _ = _ := by
        rw [cover.fullFiberIndices_eq parent]
        rfl
  rw [← massEq]
  exact (mul_le_mul_right' (mul_le_mul_right'
    (rhoPower.trans deltaPower) _) _).trans <| by
      exact packetLower parent

/-- One Node 4 call result before the public projection forgets the terminal
multiplicity bands.  Both fields are generated from the same canonical
four-degree producer; this prevents a downstream cancellation argument from
pairing public sticky data with an unrelated balancing certificate. -/
structure Proposition63RichTerminalStickyData
    {delta sigma outputLoss sourceLoss normalizationLoss : ℝ}
    {croppedFamily : Kakeya.Streamlined.TubeFamily delta}
    {normalizationExponent : ℕ}
    (croppedShading : WZ1PaperTubeShading croppedFamily)
    (reentry : PureWZ2PropStickyReentryData
      (sigma := sigma) croppedShading normalizationExponent
      sourceLoss normalizationLoss)
    (rho : WZ2PaperRequestedScale delta) where
  data : PureWZ2PropStickyData
    (sigma := sigma) (outputLoss := outputLoss) croppedShading rho 61
  coarse_midpoint_local : ∀ parent,
    ‖wz2PaperTubeMidpoint (data.coarse.tube parent)‖ ≤ 3
  coarseSourceLoss : ℝ
  coarseNormalizationLoss : ℝ
  coarseSourceLoss_pos : 0 < coarseSourceLoss
  coarseNormalizationLoss_pos : 0 < coarseNormalizationLoss
  coarseSourceLoss_budget : 3 * coarseSourceLoss ≤ outputLoss
  coarseNormalizationLoss_eq :
    coarseNormalizationLoss = (7 / 2 : ℝ) * coarseSourceLoss
  coarseReentry :
    (∀ index point,
      point ∈ reentry.geometry.frame ''
          reentry.geometry.ordinaryRefined.carrier index →
        |point (2 : Fin 3)| ≤ 1 / 8) →
      PureWZ2PropStickyReentryData
        (sigma := sigma) data.croppedCoarseShading 0
        coarseSourceLoss coarseNormalizationLoss
  coarse_reentry_axial_window_of_margin :
    ∀ rootAxialMargin : ∀ index point,
      point ∈ reentry.geometry.frame ''
          reentry.geometry.ordinaryRefined.carrier index →
        |point (2 : Fin 3)| + rho.1 ≤ 1 / 8,
      ∀ index point,
        point ∈
            (coarseReentry
              (proposition63_reentry_axial_window_of_margin reentry rho
                rootAxialMargin)).geometry.frame ''
              (coarseReentry
                (proposition63_reentry_axial_window_of_margin reentry rho
                  rootAxialMargin)).geometry.ordinaryRefined.carrier
                index →
          |point (2 : Fin 3)| ≤ 1 / 8
  terminalLoss : ℝ
  terminalLoss_pos : 0 < terminalLoss
  terminalLoss_le_output : terminalLoss ≤ outputLoss
  terminal : Proposition63TerminalMultiplicityCertificate
    (sigma := sigma) (terminalLoss := terminalLoss)
    data.cover data.refined data.croppedCoarseShading
  canonical_rescaled_fiber : ∀ parent,
    WZ2PaperPureRescaledFullFiberOutput
        (sigma := sigma) (loss := outputLoss)
        (restrictPaperShading
          (Kakeya.Streamlined.TubeSubfamily.fromFinset
            data.selected.family
            (wz2PaperFullFiberIndices
              data.selected.family data.coarse parent))
          data.refined)
        (data.coarse.tube parent) data.coarse_extremal.delta_pos
  canonical_rescaled_fiber_unit_ball : ∀ parent,
    (canonical_rescaled_fiber parent).rescalingCertificate.publicFamily.IsInUnitBall
  terminal_fiber_mass_lower : ∀ parent,
    Kakeya.realRpowENN rho.1 outputLoss *
          (terminal.fiberFloor : ENNReal) *
          Kakeya.realRpowENN delta 2 ≤
      data.cover.toPaperTubeCover.fiberShadedMass data.refined parent
  terminal_regularity_bound :
    (terminal.regularity : ENNReal) ≤
      Prop62PaperAudit.V4.logarithmicLoss delta ^ 10
  terminal_cellMass_power_lower :
    Kakeya.realRpowENN rho.1 3 *
          Kakeya.realRpowENN (delta / rho.1)
            (sigma + 2 * terminalLoss) ≤
      terminal.balanced.cellMass
  cross_degree :
    Kakeya.realRpowENN rho.1 outputLoss *
          (terminal.regularity * terminal.muCoarse : ℕ) ≤
      terminal.fineDegreeFloor
  total_mass_retention :
    wz2PaperPureRefinementFraction delta 61 * croppedShading.mass ≤
      data.refined.mass

namespace Proposition63RichTerminalStickyData

/-- The exact coarse re-entry projection used by the existing dependent
Node 4 iteration. -/
noncomputable def toReentrant
    {delta sigma outputLoss sourceLoss normalizationLoss : ℝ}
    {croppedFamily : Kakeya.Streamlined.TubeFamily delta}
    {normalizationExponent : ℕ}
    {croppedShading : WZ1PaperTubeShading croppedFamily}
    {reentry : PureWZ2PropStickyReentryData
      (sigma := sigma) croppedShading normalizationExponent
      sourceLoss normalizationLoss}
    {rho : WZ2PaperRequestedScale delta}
    (data : Proposition63RichTerminalStickyData
      (outputLoss := outputLoss) croppedShading reentry rho)
    (rootAxialWindow :
      ∀ index point,
        point ∈ reentry.geometry.frame ''
            reentry.geometry.ordinaryRefined.carrier index →
          |point (2 : Fin 3)| ≤ 1 / 8) :
    PureWZ2ReentrantPropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      croppedShading rho 0 61 where
  data := data.data
  coarseSourceLoss := data.coarseSourceLoss
  coarseNormalizationLoss := data.coarseNormalizationLoss
  coarseSourceLoss_pos := data.coarseSourceLoss_pos
  coarseNormalizationLoss_pos := data.coarseNormalizationLoss_pos
  coarseSourceLoss_budget := data.coarseSourceLoss_budget
  coarseNormalizationLoss_eq := data.coarseNormalizationLoss_eq
  coarseReentry := data.coarseReentry rootAxialWindow

end Proposition63RichTerminalStickyData

end Kakeya.Assouad.PureWZ2

namespace Kakeya.Assouad.Prop62PaperAudit.V4

open Kakeya.Assouad
open MeasureTheory

/--
The reusable V4 kernel on an exact re-entry pair.

The scalar schedule and uniform threshold are selected before `delta`, the
exact cropped pair, and `rho`.  At runtime the kernel converts the supplied
re-entry object back to the existing normalization input without changing its
cropped family or shading.
-/
theorem pureWZ2_prop_sticky_reentry_v4_rich_terminal_exact_source
    (hFixedGrid : FixedGridBoundaryRemovalStatement)
    (hTreeCleanup : OnePassTreeCleanupStatement)
    (sigma : ℝ)
    (critical : PureWZ2CriticalPackage sigma)
    (outputLoss : ℝ)
    (outputLossPos : 0 < outputLoss)
    (outputLossLeOne : outputLoss ≤ 1) :
    ∃ normalizationLoss delta₀ : ℝ,
      0 < pureWZ2CompleteNormalizationFinalLoss normalizationLoss ∧
      0 < normalizationLoss ∧
      pureWZ2CompleteNormalizationFinalLoss normalizationLoss ≤
        normalizationLoss / 2 ∧
      normalizationLoss < outputLoss ∧
      0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        ∀ (croppedFamily : Kakeya.Streamlined.TubeFamily delta)
          (croppedShading : WZ1PaperTubeShading croppedFamily)
          {normalizationExponent : ℕ}
          (reentry :
                PureWZ2PropStickyReentryData
                  (sigma := sigma)
                  croppedShading normalizationExponent
                  (pureWZ2CompleteNormalizationFinalLoss
                    normalizationLoss)
                  normalizationLoss),
          ∀ rho : WZ2PaperRequestedScale delta,
            Real.rpow delta (1 - outputLoss) ≤ rho.1 →
            rho.1 ≤ Real.rpow delta outputLoss →
              Nonempty
                (PureWZ2.Proposition63RichTerminalStickyData
                  (outputLoss := outputLoss)
                  croppedShading reentry rho) := by
  rcases
      Kakeya.Assouad.Prop62PaperAudit.V4.PureWZ2CriticalPackage.prop62V4_pure_scalar_routing
        critical
        10 8 2 51 outputLossPos outputLossLeOne
    with
    ⟨scalarRouting⟩
  let routing := scalarRouting.routing
  let scalar := scalarRouting.scalar
  rcases
      prop62V4_three_loss_routing routing outputLossLeOne
    with
    ⟨three⟩
  rcases three with
    ⟨sourceLoss, normalizationLoss, workingEta,
      sourceLossEq, normalizationLossEq, workingEtaEq,
      sourceLossPos, normalizationLossPos, workingEtaPos,
      sourceLossLeEighth, sourceLossLeHalf, sourceLossLeHierarchy,
      normalizationLossWorking, normalizationLossOutput⟩
  subst workingEta
  subst sourceLoss
  let three : Prop62V4ThreeLossRoutingData routing :=
    {
      sourceLoss :=
        pureWZ2CompleteNormalizationFinalLoss normalizationLoss
      normalizationLoss := normalizationLoss
      workingEta := routing.numerics.hierarchy.stableLoss
      sourceLoss_eq := rfl
      normalizationLoss_eq := normalizationLossEq
      workingEta_eq := rfl
      sourceLoss_pos := sourceLossPos
      normalizationLoss_pos := normalizationLossPos
      workingEta_pos := workingEtaPos
      sourceLoss_le_eighth := sourceLossLeEighth
      sourceLoss_le_half := sourceLossLeHalf
      sourceLoss_le_hierarchy := sourceLossLeHierarchy
      normalizationLoss_lt_workingEta := normalizationLossWorking
      normalizationLoss_output_budget := normalizationLossOutput
    }
  let cleanupOracle : PureWZ2Prop62CleanupOracle :=
    onePassTreeCleanupStatement_to_pureWZ2Prop62CleanupOracle
      hTreeCleanup
  rcases
      prop62V4_normalized_rich_producer
        three hFixedGrid cleanupOracle
    with
    ⟨richReceipt⟩
  rcases
      prop62V4_normalized_ledger_routing routing three
    with
    ⟨ledgerReceipt⟩
  rcases
      prop62V4_selected_incidence_pure_scalar_extension
        10 8 2 51 sigma outputLoss outputLossPos routing scalar
    with
    ⟨incidenceScalar⟩
  rcases
      PureWZ2.proposition63_cross_degree_absorption
        routing.numerics.hierarchy.sourceLoss
        routing.numerics.hierarchy.capLoss outputLoss outputLossPos
        (by
          rw [routing.numerics.hierarchy.sourceLoss_eq,
            routing.numerics.hierarchy.capLoss_eq]
          dsimp only [wz2PaperFinalSourceLoss, wz2PaperFinalCapLoss]
          have structuralLe :
              routing.critical.structuralLoss ≤ outputLoss ^ 2 / 1000 :=
            routing.critical.structuralLoss_le.trans (min_le_left _ _)
          have outputSquarePos : 0 < outputLoss ^ 2 := sq_pos_of_pos outputLossPos
          have outputSquareLeOne : outputLoss ^ 2 ≤ 1 := by nlinarith
          have structuralLeOne : routing.critical.structuralLoss ≤ 1 :=
            structuralLe.trans <| by nlinarith
          have structuralSquareLe :
              routing.critical.structuralLoss ^ 2 ≤
                routing.critical.structuralLoss := by
            nlinarith [routing.critical.structuralLoss_pos]
          nlinarith)
    with ⟨crossDegreeAbsorption⟩
  let coarseSourceLoss :=
    routing.numerics.hierarchy.finalStrongLoss
  let coarseNormalizationLoss :=
    (7 / 2 : ℝ) * coarseSourceLoss
  rcases
      wz2PaperPureNearby_topLevelPaperCWA_eventually
        (loss := coarseSourceLoss)
        (outputLoss := coarseNormalizationLoss)
        routing.numerics.hierarchy.finalStrongLoss_pos
        (by
          nlinarith [
            routing.numerics.hierarchy.final_output_budget,
            outputLossLeOne])
        (by
          change
            3 * routing.numerics.hierarchy.finalStrongLoss <
              (7 / 2 : ℝ) *
                routing.numerics.hierarchy.finalStrongLoss
          nlinarith [routing.numerics.hierarchy.finalStrongLoss_pos])
    with
    ⟨coarseTopDelta, coarseTopDeltaPos, _coarseTopDeltaOne,
      recoverCoarseTopCWA⟩
  rcases
      pure_wz2_exists_delta₀_rpow_le
        coarseTopDeltaPos
        outputLossPos
    with
    ⟨topScaleDelta, topScaleDeltaPos, _topScaleDeltaOne,
      topScaleSmall⟩
  let delta₀ :=
    min richReceipt.delta₀
      (min ledgerReceipt.delta₀
        (min incidenceScalar.delta₀
          (min crossDegreeAbsorption.delta₀ topScaleDelta)))
  have delta₀Pos : 0 < delta₀ := by
    exact
      lt_min richReceipt.delta₀_pos <|
        lt_min ledgerReceipt.delta₀_pos <|
          lt_min incidenceScalar.delta₀_pos <|
            lt_min crossDegreeAbsorption.delta₀_pos topScaleDeltaPos
  have delta₀LeOne : delta₀ ≤ 1 := by
    exact
      (min_le_left _ _).trans <|
        richReceipt.delta₀_le_one_hundred.trans (by norm_num)
  refine
    ⟨three.normalizationLoss, delta₀,
      three.sourceLoss_pos, three.normalizationLoss_pos,
      three.sourceLoss_le_half,
      by
        nlinarith [three.normalizationLoss_output_budget],
      delta₀Pos, delta₀LeOne, ?_⟩
  intro delta deltaPos deltaLe croppedFamily croppedShading
    normalizationExponent reentry rho rhoLower rhoUpper
  let normalized := reentry.toNormalizationData
  have deltaRich : delta ≤ richReceipt.delta₀ :=
    deltaLe.trans (min_le_left _ _)
  have deltaLedger : delta ≤ ledgerReceipt.delta₀ :=
    deltaLe.trans <|
      (min_le_right _ _).trans (min_le_left _ _)
  have deltaIncidence : delta ≤ incidenceScalar.delta₀ :=
    deltaLe.trans <|
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_left _ _)
  have deltaTopScale : delta ≤ topScaleDelta :=
    deltaLe.trans <|
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans <|
          (min_le_right _ _).trans (min_le_right _ _)
  have deltaCrossDegree : delta ≤ crossDegreeAbsorption.delta₀ :=
    deltaLe.trans <|
      (min_le_right _ _).trans <|
        (min_le_right _ _).trans <|
          (min_le_right _ _).trans (min_le_left _ _)
  have deltaScalar : delta ≤ scalar.delta₀ :=
    deltaIncidence.trans incidenceScalar.delta₀_le_scalar
  rcases
      richReceipt.produce
        deltaPos deltaRich normalized rho rhoLower rhoUpper
    with
    ⟨produced⟩
  let rich := produced.rich
  rcases
      ledgerReceipt.route deltaPos deltaLedger normalized
    with
    ⟨ledger⟩
  have sourceLedger :=
    rich.fixedGridMetric_hierarchySourceMassVolumeLedger
      (deltaLedger.trans ledgerReceipt.delta₀_le_one_twelfth)
      ledger
  let coarseWitness :
      Prop62V4FinalCoarseCriticalWitness
        rich.outputCertificate routing.critical.structuralLoss :=
    rich.finalCoarseCriticalWitness_of_selectedIncidence
      routing.critical incidenceScalar.overlap
      (deltaIncidence.trans incidenceScalar.delta₀_le_overlap)
      rhoUpper
      (scalar.rho_small deltaPos deltaScalar rhoUpper)
      (scalar.ratio_small
        deltaPos deltaScalar produced.metricCertificate.rho_pos rhoLower)
      (by
        simpa [three.workingEta_eq] using
          incidenceScalar.reduced_coarse_density
            deltaPos deltaIncidence
            produced.metricCertificate.rho_pos rhoUpper)
      (by
        simpa [three.workingEta_eq] using
          scalar.parent_cwa
            deltaPos deltaScalar
            produced.metricCertificate.rho_pos rhoUpper)
  let criticalInputs :=
    rich.criticalMultiplicityInputs
      scalar deltaScalar rhoLower rhoUpper
      three.sourceLoss_le_hierarchy three.workingEta_eq coarseWitness
  let productInputs :=
    scalar.productMultiplicityInputs
      rich.packetInput rich.multiplicity rich.parentClass rich.treeCleanup
      rich.exactification rich.parentDegree rich.core rich.good
      rich.families (output := rich.canonicalOutput)
      deltaScalar rhoLower rhoUpper rich.regularity_bound
      sourceLedger.1 sourceLedger.2
  let componentInputs :=
    scalar.componentMultiplicityFloorInputs
      rich.packetInput rich.multiplicity rich.parentClass rich.treeCleanup
      rich.exactification rich.parentDegree rich.core rich.good
      rich.families (output := rich.canonicalOutput)
      deltaScalar rhoLower rhoUpper rich.regularity_bound
  let volumeAbsorption :=
    scalar.extremalVolumeAbsorption
      deltaScalar deltaPos produced.metricCertificate.rho_pos
  let sourceFiberConstant : ENNReal :=
    Kakeya.realRpowENN delta (-8 * three.workingEta) / 81000000
  let finalInputs :=
    scalar.finalAssemblyInputs
      rich.packetInput rich.multiplicity rich.parentClass rich.treeCleanup
      rich.exactification rich.parentDegree rich.core rich.good
      rich.families (output := rich.canonicalOutput)
      deltaScalar rho.2.1 rho.2.2 rhoLower rhoUpper
      rich.regularity_bound
      (by
        simpa [three.workingEta_eq] using rich.parent_constant_bound)
      criticalInputs productInputs componentInputs volumeAbsorption
      sourceFiberConstant rich.terminalRescaling
      (by
        simpa [sourceFiberConstant, three.workingEta_eq] using
          rich.terminal_fiber_constant_bound)
  let assembled :
      PureWZ2PropStickyData
        (sigma := sigma)
        (outputLoss := routing.numerics.hierarchy.finalStrongLoss)
        normalized.croppedRefined rho 61 :=
    rich.assemblePurePropStickySixtyOne
      (Prop62V4CriticalInputsAssembly.criticalForCap
        (routing := routing))
      criticalInputs productInputs componentInputs volumeAbsorption
      finalInputs.toFinalAssemblyInputsData
  let outputData :=
    PureWZ2PropStickyData.mono_loss
      (firstLoss := routing.numerics.hierarchy.finalStrongLoss)
      (secondLoss := outputLoss) assembled <| by
      linarith [
        routing.numerics.hierarchy.final_output_budget,
        routing.numerics.hierarchy.finalStrongLoss_pos]
  let terminalCertificate :
      PureWZ2.Proposition63TerminalMultiplicityCertificate
        rich.outputCertificate.cover
        rich.outputCertificate.refinement.refined
        rich.outputCertificate.coarseShading :=
    PureWZ2.proposition63TerminalMultiplicityCertificateOfFourDegree
      rich.packetInput rich.outputCertificate
      (by
        intro parent
        change
          ((55296 * Kakeya.deltaTubeVolume 1) *
                Kakeya.realRpowENN (delta / rho.1)
                  (2 - sigma + routing.numerics.hierarchy.finalStrongLoss)) *
              (rich.families.terminalFiber rich.packetInput rich.multiplicity
                rich.parentClass rich.treeCleanup rich.exactification
                rich.parentDegree rich.core parent).family.enncard ≤
            (rich.canonicalOutput.muFine : ENNReal)
        exact rich.canonicalOutput.fine_multiplicity_lower
          rich.packetInput rich.multiplicity rich.parentClass rich.treeCleanup
          rich.exactification rich.parentDegree rich.core rich.good
          rich.families
          (Prop62V4CriticalInputsAssembly.criticalForCap
            (routing := routing)) criticalInputs productInputs
          componentInputs parent)
      (by
        change
          (55296 * Kakeya.deltaTubeVolume 1) *
                Kakeya.realRpowENN rho.1
                  (2 - sigma + routing.numerics.hierarchy.finalStrongLoss) *
              rich.families.restriction.coarseSelected.family.enncard ≤
            (rich.canonicalOutput.muCoarse : ENNReal)
        exact rich.canonicalOutput.coarse_multiplicity_lower
          rich.packetInput rich.multiplicity rich.parentClass rich.treeCleanup
          rich.exactification rich.parentDegree rich.core rich.good
          rich.families
          (Prop62V4CriticalInputsAssembly.criticalForCap
            (routing := routing)) criticalInputs productInputs
          componentInputs)
      (by
        have cap :=
          rich.canonicalOutput.coarse_multiplicity_upper_of_critical_inputs
            rich.packetInput rich.multiplicity rich.parentClass
            rich.treeCleanup rich.exactification rich.parentDegree rich.core
            rich.good rich.families
            (Prop62V4CriticalInputsAssembly.criticalForCap
              (routing := routing)) criticalInputs
        calc
          ((rich.canonicalOutput.coarseLoss *
                rich.canonicalOutput.muCoarse : ℕ) : ENNReal) =
              (rich.canonicalOutput.coarseLoss : ENNReal) *
                (rich.canonicalOutput.muCoarse : ENNReal) := by simp
          _ ≤ (rich.canonicalOutput.coarseLoss : ENNReal) *
                (Kakeya.realRpowENN rho.1
                    (2 - sigma - routing.numerics.hierarchy.capLoss) *
                  rich.families.restriction.coarseSelected.family.enncard) :=
            mul_le_mul_left' cap _
          _ = ((rich.canonicalOutput.coarseLoss : ENNReal) *
                Kakeya.realRpowENN rho.1
                  (2 - sigma - routing.numerics.hierarchy.capLoss)) *
                rich.families.restriction.coarseSelected.family.enncard := by
            ring
          _ ≤ Kakeya.realRpowENN rho.1
                  (2 - sigma - routing.numerics.hierarchy.finalStrongLoss) *
                rich.families.restriction.coarseSelected.family.enncard :=
            mul_le_mul_right'
              finalInputs.public_multiplicity_absorption.coarse_scalar _
          _ = Kakeya.realRpowENN rho.1
                  (2 - sigma - routing.numerics.hierarchy.finalStrongLoss) *
                rich.outputCertificate.coarse.family.enncard := rfl)
      (by
        intro parent
        have cap :=
          rich.canonicalOutput.fine_multiplicity_upper_of_critical_inputs
            rich.packetInput rich.multiplicity rich.parentClass
            rich.treeCleanup rich.exactification rich.parentDegree rich.core
            rich.good rich.families
            (Prop62V4CriticalInputsAssembly.criticalForCap
              (routing := routing)) criticalInputs parent
        exact cap.trans <| by
          calc
            Kakeya.realRpowENN (delta / rho.1)
                  (2 - sigma - routing.numerics.hierarchy.capLoss) *
                (rich.families.terminalFiber rich.packetInput
                  rich.multiplicity rich.parentClass rich.treeCleanup
                  rich.exactification rich.parentDegree rich.core
                  parent).family.enncard ≤
              Kakeya.realRpowENN (delta / rho.1)
                  (2 - sigma -
                    routing.numerics.hierarchy.finalStrongLoss) *
                (rich.families.terminalFiber rich.packetInput
                  rich.multiplicity rich.parentClass rich.treeCleanup
                  rich.exactification rich.parentDegree rich.core
                  parent).family.enncard := by
              gcongr
              exact finalInputs.public_multiplicity_absorption.fine_scalar
            _ =
              Kakeya.realRpowENN (delta / rho.1)
                  (2 - sigma -
                    routing.numerics.hierarchy.finalStrongLoss) *
                ((wz2PaperFullFiberIndices
                  rich.outputCertificate.refinement.selected.family
                  rich.outputCertificate.coarse.family parent).card :
                    ENNReal) := rfl)
      (rich.packetInput.fineCellThreshold rich.multiplicity rich.parentClass
        rich.treeCleanup rich.exactification rich.producer.initial.bins
        (rich.packetInput.canonicalPeelingA0 rich.multiplicity
          rich.parentClass rich.treeCleanup rich.exactification
          rich.producer.initial.bins))
      (by
        have numeratorPos :
            0 < 2 ^ rich.producer.initial.bins.fineCellBin.level :=
          pow_pos (by norm_num) _
        have denominatorPos :=
          rich.packetInput.canonicalPeelingA0_pos rich.multiplicity
            rich.parentClass rich.treeCleanup rich.exactification
            rich.producer.initial.bins
        rw [PureWZ2Prop62PacketCellInput.fineCellThreshold,
          Nat.ceilDiv_eq_add_pred_div]
        apply Nat.div_pos
        · omega
        · exact denominatorPos)
      (rich.packetInput.packetCells_fine_degree_lower
        rich.schedule rich.producer)
      (rich.packetInput.packetCells_fine_degree_upper_canonical
        rich.schedule rich.producer)
      (by
        let lambda := Kakeya.realRpowENN rho.1
          (routing.critical.structuralLoss / 2)
        have rhoSmall : rho.1 ≤ 1 / 24 :=
          scalar.rho_small deltaPos deltaScalar rhoUpper
        have densityScalar :
            PureWZ2Prop62FourDegreeOutputCertificate.SelectedIncidenceDensityScalar
              (densityConstant :=
                Kakeya.realRpowENN delta (2 * three.workingEta))
              lambda := by
          change
            (576 * (55296 * Kakeya.deltaTubeVolume 1) : ENNReal) *
                lambda ≤
              Kakeya.realRpowENN delta (2 * three.workingEta)
          simpa [lambda, three.workingEta_eq] using
            incidenceScalar.reduced_coarse_density deltaPos deltaIncidence
              produced.metricCertificate.rho_pos rhoUpper
        have halfDense :=
          rich.outputCertificate.selectedIncidenceCoarseShading_dense
            deltaPos produced.metricCertificate.rho_pos rhoSmall
            lambda densityScalar
        have terminalPowerLe :
            Kakeya.realRpowENN rho.1
                routing.numerics.hierarchy.finalStrongLoss ≤ lambda := by
          dsimp only [lambda]
          apply pure_wz2_rpowENN_antitone
            produced.metricCertificate.rho_pos rho.2.2
          nlinarith [routing.critical.structuralLoss_pos,
            scalar.structural_to_final]
        rw [Kakeya.Streamlined.Shading.IsLambdaDense] at halfDense ⊢
        exact (mul_le_mul_right' terminalPowerLe
          (wz1PaperBodyFamily
            rich.outputCertificate.coarse.family).mass).trans halfDense)
  refine
    ⟨{
      data := outputData
      coarse_midpoint_local := by
        intro parent
        change ‖wz2PaperTubeMidpoint
          (rich.outputCertificate.coarse.family.tube parent)‖ ≤ 3
        have centered := rich.finalParentsCentered parent
        rw [← centered]
        exact (wz2PaperCenteredLineTube_midpoint_norm_le_one
          (rich.outputCertificate.cover.coarse_line_class parent)).trans
            (by norm_num)
      coarseSourceLoss := coarseSourceLoss
      coarseNormalizationLoss := coarseNormalizationLoss
      coarseSourceLoss_pos :=
        routing.numerics.hierarchy.finalStrongLoss_pos
      coarseNormalizationLoss_pos := by
        dsimp only [coarseNormalizationLoss, coarseSourceLoss]
        nlinarith [routing.numerics.hierarchy.finalStrongLoss_pos]
      coarseSourceLoss_budget := by
        dsimp only [coarseSourceLoss]
        exact routing.numerics.hierarchy.final_output_budget
      coarseNormalizationLoss_eq := rfl
      coarseReentry := ?_
      coarse_reentry_axial_window_of_margin := ?_
      terminalLoss := routing.numerics.hierarchy.finalStrongLoss
      terminalLoss_pos := routing.numerics.hierarchy.finalStrongLoss_pos
      terminalLoss_le_output := by
        linarith [routing.numerics.hierarchy.final_output_budget,
          routing.numerics.hierarchy.finalStrongLoss_pos]
      terminal := terminalCertificate
      canonical_rescaled_fiber := fun parent =>
        (rich.canonicalOutput.terminalFiberRescaledOutput
            rich.packetInput rich.multiplicity rich.parentClass
            rich.treeCleanup rich.exactification rich.parentDegree rich.core
            rich.good rich.families
            (Prop62V4CriticalInputsAssembly.criticalForCap
              (routing := routing)) criticalInputs productInputs
            componentInputs volumeAbsorption
            finalInputs.toFinalAssemblyInputsData parent).mono_loss (by
              linarith [
                routing.numerics.hierarchy.final_output_budget,
                routing.numerics.hierarchy.finalStrongLoss_pos])
      canonical_rescaled_fiber_unit_ball := by
        intro parent
        let sourceFamily :=
          (rich.families.terminalFiber rich.packetInput rich.multiplicity
            rich.parentClass rich.treeCleanup rich.exactification
            rich.parentDegree rich.core parent).family
        have sourceBounded : HasBoundedBase sourceFamily 4 := by
          intro source
          rw [(rich.families.terminalFiber rich.packetInput
            rich.multiplicity rich.parentClass rich.treeCleanup
            rich.exactification rich.parentDegree rich.core parent).tube_eq]
          change ‖rich.fixedGridComposedSelected.family.tube
            ((rich.families.terminalFiber rich.packetInput
              rich.multiplicity rich.parentClass rich.treeCleanup
              rich.exactification rich.parentDegree rich.core parent
              ).embedding source) |>.base‖ ≤ 4
          rw [rich.fixedGridComposedSelected.tube_eq]
          exact normalized.ordinary_bounded_base
            (rich.fixedGridComposedSelected.embedding
              ((rich.families.terminalFiber rich.packetInput
                rich.multiplicity rich.parentClass rich.treeCleanup
                rich.exactification rich.parentDegree rich.core parent
                ).embedding source))
        exact rich.canonicalOutput.terminalFiberCertificate_publicFamily_isInUnitBall
          rich.packetInput rich.multiplicity rich.parentClass
          rich.treeCleanup rich.exactification rich.parentDegree rich.core
          rich.good rich.families finalInputs.rho_le_one
          criticalInputs.ratio_small parent sourceBounded
      terminal_fiber_mass_lower := by
        apply PureWZ2.proposition63_terminal_fiber_mass_lower_of_source_power
          rich.outputCertificate.cover
          rich.outputCertificate.refinement.refined
          rich.outputCertificate.fiberFloor deltaPos
          (deltaLe.trans delta₀LeOne) produced.metricCertificate.rho_pos
          rhoUpper outputLossPos.le
        · have packetGap := routing.numerics.packet_critical_gap
          have finalStrongLeOutput :
              routing.numerics.hierarchy.finalStrongLoss ≤ outputLoss := by
            rw [routing.numerics.hierarchy.finalStrongLoss_eq]
            unfold wz2PaperFinalStrongLoss
            linarith
          have structuralLeOutput :
              routing.critical.structuralLoss ≤ outputLoss :=
            routing.numerics.structural_final.le.trans finalStrongLeOutput
          exact packetGap.le.trans <|
            mul_le_mul_of_nonneg_left structuralLeOutput outputLossPos.le
        · intro parent
          simpa only [three.workingEta_eq, Nat.cast_ofNat, mul_assoc]
            using rich.outputCertificate.packet_density parent
      terminal_regularity_bound := by
        change
          (rich.outputCertificate.regularity : ENNReal) ≤
            Prop62PaperAudit.V4.logarithmicLoss delta ^ 10
        change
          (rich.canonicalOutput.coarseLoss : ENNReal) ≤
            Prop62PaperAudit.V4.logarithmicLoss delta ^ 10
        exact rich.regularity_bound
      terminal_cellMass_power_lower := by
        have hfloor :=
          _root_.Kakeya.Assouad.Prop62PaperAudit.V4.Prop62V4RichCertificateCompanionData.FixedGridPureScalar.balanced_cellMass_power_lower
            rich scalar deltaScalar rhoLower
            three.sourceLoss_le_hierarchy three.workingEta_eq
            rhoUpper
            (rich.outputCertificate.cover.toWZ1PaperTubeCover.parent
              ⟨0, rich.outputCertificate.refined_nonempty⟩)
        have hbalanced :
            terminalCertificate.balanced.cellMass =
              rich.outputCertificate.balanced.cellMass := rfl
        exact hbalanced.symm ▸ hfloor
      cross_degree := ?_
      total_mass_retention := ?_
    }⟩
  · intro rootAxialWindow
    let lambda :=
      Kakeya.realRpowENN rho.1
        (routing.critical.structuralLoss / 2)
    have lambdaPos : 0 < lambda := by
      simp [lambda, Kakeya.realRpowENN,
        Real.rpow_pos_of_pos produced.metricCertificate.rho_pos]
    have rhoSmall : rho.1 ≤ 1 / 24 :=
      scalar.rho_small deltaPos deltaScalar rhoUpper
    have ratioSmall : delta / rho.1 ≤ 1 / 24 :=
      scalar.ratio_small
        deltaPos deltaScalar produced.metricCertificate.rho_pos rhoLower
    have rhoTopScale : rho.1 ≤ coarseTopDelta :=
      rhoUpper.trans (topScaleSmall delta deltaPos deltaTopScale)
    have densityScalar :
        PureWZ2Prop62FourDegreeOutputCertificate.SelectedIncidenceDensityScalar
          (densityConstant :=
            Kakeya.realRpowENN delta (2 * three.workingEta))
          lambda := by
      change
        (576 * (55296 * Kakeya.deltaTubeVolume 1) : ENNReal) *
            lambda ≤
          Kakeya.realRpowENN delta (2 * three.workingEta)
      simpa [lambda, three.workingEta_eq] using
        incidenceScalar.reduced_coarse_density
          deltaPos deltaIncidence
          produced.metricCertificate.rho_pos rhoUpper
    have densityBudget :
        Kakeya.realRpowENN rho.1 coarseSourceLoss / 2 ≤
          (100 : ENNReal)⁻¹ * lambda := by
      have finalLeStructural :
          Kakeya.realRpowENN rho.1 coarseSourceLoss ≤
            Kakeya.realRpowENN rho.1 routing.critical.structuralLoss := by
        apply pure_wz2_rpowENN_antitone
          produced.metricCertificate.rho_pos rho.2.2
        exact scalar.structural_to_final
      have absorbed :=
        incidenceScalar.overlap.overlap_absorption
          deltaPos
          (deltaIncidence.trans incidenceScalar.delta₀_le_overlap)
          produced.metricCertificate.rho_pos rhoUpper
      have structuralLeHalf :
          Kakeya.realRpowENN rho.1 routing.critical.structuralLoss ≤
            (100000 : ENNReal)⁻¹ * lambda := by
        have divided :=
          (ENNReal.mul_le_iff_le_inv
            (by norm_num : (100000 : ENNReal) ≠ 0)
            (by norm_num : (100000 : ENNReal) ≠ ⊤)).mp absorbed
        simpa [lambda] using divided
      calc
        Kakeya.realRpowENN rho.1 coarseSourceLoss / 2 ≤
            Kakeya.realRpowENN rho.1 coarseSourceLoss :=
          by
            rw [ENNReal.div_eq_inv_mul]
            calc
              (2 : ENNReal)⁻¹ *
                    Kakeya.realRpowENN rho.1 coarseSourceLoss ≤
                  1 *
                    Kakeya.realRpowENN rho.1 coarseSourceLoss := by
                gcongr
                norm_num
              _ = Kakeya.realRpowENN rho.1 coarseSourceLoss := by simp
        _ ≤
            Kakeya.realRpowENN rho.1 routing.critical.structuralLoss :=
          finalLeStructural
        _ ≤ (100000 : ENNReal)⁻¹ * lambda := structuralLeHalf
        _ ≤ (100 : ENNReal)⁻¹ * lambda := by
          gcongr
          norm_num
    let ordinaryExtremal :
        WZ2PaperPureIsExtremal
          sigma coarseSourceLoss
          rich.outputCertificate.coarse.family
          rich.outputCertificate.finalCoarseOrdinaryTrace :=
      {
        delta_pos := produced.metricCertificate.rho_pos
        delta_le_one := rho.2.2
        nonempty := assembled.coarse_extremal.nonempty
        cwa_nearby_scales := assembled.coarse_extremal.cwa_nearby_scales
        dense := by
          have densityPower :
              Kakeya.realRpowENN rho.1 coarseSourceLoss ≤
                Kakeya.realRpowENN rho.1
                  routing.critical.structuralLoss := by
            apply pure_wz2_rpowENN_antitone
              produced.metricCertificate.rho_pos rho.2.2
            exact scalar.structural_to_final
          have dense :=
            rich.finalCoarseOrdinaryTrace_dense_of_selectedIncidence
              routing.critical incidenceScalar.overlap
              (deltaIncidence.trans incidenceScalar.delta₀_le_overlap)
              rhoUpper rhoSmall ratioSmall
              (by
                simpa [three.workingEta_eq] using
                  incidenceScalar.reduced_coarse_density
                    deltaPos deltaIncidence
                    produced.metricCertificate.rho_pos rhoUpper)
          rw [Kakeya.Streamlined.Shading.IsLambdaDense] at dense ⊢
          calc
            Kakeya.realRpowENN rho.1 coarseSourceLoss *
                  rich.outputCertificate.coarse.family.toBodyFamily.mass ≤
                Kakeya.realRpowENN rho.1
                    routing.critical.structuralLoss *
                  rich.outputCertificate.coarse.family.toBodyFamily.mass := by
              gcongr
            _ ≤
                rich.outputCertificate.finalCoarseOrdinaryTrace.mass :=
              dense
        volume_upper := by
          calc
            volume
                rich.outputCertificate.finalCoarseOrdinaryTrace.union ≤
              volume rich.outputCertificate.coarseShading.union :=
                measure_mono
                  rich.outputCertificate.finalCoarseOrdinaryTrace_union_subset
            _ ≤
                Kakeya.realRpowENN rho.1 (sigma - coarseSourceLoss) := by
              have assembledVolume :=
                assembled.coarse_extremal.volume_upper
              change
                volume rich.outputCertificate.coarseShading.union ≤
                  Kakeya.realRpowENN rho.1
                    (sigma -
                      routing.numerics.hierarchy.finalStrongLoss)
                at assembledVolume
              simpa [coarseSourceLoss] using assembledVolume
      }
    have ordinaryAxialWindow :
        ∀ parent point,
          point ∈
              rich.outputCertificate.finalCoarseOrdinaryTrace.carrier parent →
            |point (2 : Fin 3)| ≤ 1 / 4 :=
      rich.finalCoarseOrdinaryTrace_axial_window
        rootAxialWindow rhoSmall
    have finalLeNormalization :
        coarseSourceLoss ≤ coarseNormalizationLoss := by
      dsimp only [coarseNormalizationLoss]
      nlinarith [routing.numerics.hierarchy.finalStrongLoss_pos]
    have topNormalization :
        WZ2PaperConvexWolffBound
          rich.outputCertificate.coarse.family
          (Kakeya.realRpowENN rho.1 (-coarseNormalizationLoss)) := by
      exact
        recoverCoarseTopCWA
          rho.1 produced.metricCertificate.rho_pos rhoTopScale
          rich.outputCertificate.coarse.family
          assembled.coarse_extremal.cwa_nearby_scales
          (rich.finalCoarse_fullOrdinaryCarrier_subset_paper
            rhoSmall)
    let croppedExtremal :=
      assembled.coarse_extremal.mono_loss finalLeNormalization
    exact
      rich.exactCoarseReentryData
        (by rfl) ratioSmall rhoSmall lambda lambdaPos densityScalar
        coarseSourceLoss coarseNormalizationLoss
        routing.numerics.hierarchy.finalStrongLoss_pos
        (by
          dsimp only [coarseNormalizationLoss, coarseSourceLoss]
          nlinarith [routing.numerics.hierarchy.finalStrongLoss_pos])
        (by
          dsimp only [coarseNormalizationLoss, coarseSourceLoss]
          nlinarith [routing.numerics.hierarchy.finalStrongLoss_pos])
        densityBudget ordinaryExtremal ordinaryAxialWindow
        topNormalization croppedExtremal
  · intro rootAxialMargin parent point pointMem
    change point ∈ (AffineIsometryEquiv.refl ℝ Point3) ''
        rich.outputCertificate.finalCoarseOrdinaryTrace.carrier parent
      at pointMem
    rcases pointMem with ⟨sourcePoint, sourcePointMem, rfl⟩
    simpa using rich.finalCoarseOrdinaryTrace_axial_window_of_margin
      rootAxialMargin parent sourcePoint sourcePointMem

  ·
    change Kakeya.realRpowENN rho.1 outputLoss *
          (terminalCertificate.regularity * terminalCertificate.muCoarse : ℕ) ≤
        terminalCertificate.fineDegreeFloor
    change Kakeya.realRpowENN rho.1 outputLoss *
          (rich.outputCertificate.regularity *
            rich.outputCertificate.muCoarse : ℕ) ≤
        (rich.packetInput.fineCellThreshold rich.multiplicity
          rich.parentClass rich.treeCleanup rich.exactification
          rich.producer.initial.bins
          (rich.packetInput.canonicalPeelingA0 rich.multiplicity
            rich.parentClass rich.treeCleanup rich.exactification
            rich.producer.initial.bins))
    let fineDegree :=
      rich.packetInput.fineCellThreshold rich.multiplicity
        rich.parentClass rich.treeCleanup rich.exactification
        rich.producer.initial.bins
        (rich.packetInput.canonicalPeelingA0 rich.multiplicity
          rich.parentClass rich.treeCleanup rich.exactification
          rich.producer.initial.bins)
    have massLower :
        wz2PaperPureRefinementFraction delta 61 *
              Kakeya.realRpowENN delta
                routing.numerics.hierarchy.sourceLoss *
              rich.outputCertificate.refinement.selected.family.enncard *
              Kakeya.realRpowENN delta 2 ≤
            rich.outputCertificate.refinement.refined.mass := by
      calc
        wz2PaperPureRefinementFraction delta 61 *
              Kakeya.realRpowENN delta
                routing.numerics.hierarchy.sourceLoss *
              rich.outputCertificate.refinement.selected.family.enncard *
              Kakeya.realRpowENN delta 2 =
            wz2PaperPureRefinementFraction delta 50 *
              (wz1PaperRefinementFraction delta 11 *
                Kakeya.realRpowENN delta
                  routing.numerics.hierarchy.sourceLoss *
                rich.outputCertificate.refinement.selected.family.enncard *
                Kakeya.realRpowENN delta 2) := by
          simp only [wz2PaperPureRefinementFraction,
            wz1PaperRefinementFraction]
          rw [show 61 = 50 + 11 by norm_num, pow_add]
          ring
        _ ≤ wz2PaperPureRefinementFraction delta 50 *
              (Prop62PaperAudit.V4.prop62V4FixedGridMetricCompanionOfCertificate
                normalized produced.fixedGrid.preparation
                produced.metricCertificate).metric.refinement.refined.mass := by
          exact mul_le_mul_left' sourceLedger.1 _
        _ ≤ rich.outputCertificate.refinement.refined.mass :=
          rich.outputCertificate.total_mass_retention
    have fineVolumeUpper :
        volume rich.outputCertificate.refinement.refined.union ≤
          Kakeya.realRpowENN delta
            (sigma - routing.numerics.hierarchy.sourceLoss) := by
      apply (measure_mono ?_).trans sourceLedger.2
      intro point point_mem
      rcases point_mem with ⟨source, source_mem⟩
      exact ⟨rich.outputCertificate.refinement.selected.embedding source,
        rich.outputCertificate.refinement.subshading source source_mem⟩
    have massUpper :
        rich.outputCertificate.refinement.refined.mass ≤
          ((rich.outputCertificate.regularity : ENNReal) * fineDegree) *
            rich.outputCertificate.muFine *
            volume rich.outputCertificate.refinement.refined.union := by
      apply mass_le_of_pointMultiplicity_le
      intro point _point_mem
      have pointwise := terminalCertificate.fine_pointMultiplicity_upper point
      change
        (rich.outputCertificate.refinement.refined.pointMultiplicity point :
            ENNReal) ≤
          (((rich.outputCertificate.regularity * fineDegree : ℕ) : ENNReal) *
            rich.outputCertificate.muFine) at pointwise
      simpa only [Nat.cast_mul] using pointwise
    have fiberCardinality :
        (rich.outputCertificate.fiberFloor : ENNReal) *
            rich.outputCertificate.coarse.family.enncard ≤
          rich.outputCertificate.refinement.selected.family.enncard := by
      exact
        PureWZ2Prop62PacketCellInput.FourDegreeLemmaOutputData.fiberFloor_mul_coarse_enncard_le_fine_enncard
          rich.packetInput rich.multiplicity rich.parentClass rich.treeCleanup
          rich.exactification rich.parentDegree rich.core rich.good
          rich.families rich.canonicalOutput
    have fineCap :
        (rich.outputCertificate.muFine : ENNReal) ≤
          Kakeya.realRpowENN (delta / rho.1)
              (2 - sigma - routing.numerics.hierarchy.capLoss) *
            (2 : ENNReal) * rich.outputCertificate.fiberFloor := by
      let parent : Fin rich.outputCertificate.coarse.family.card :=
        ⟨0,
          PureWZ2Prop62PacketCellInput.FourDegreeLemmaOutputData.finalCoarse_card_pos
            rich.packetInput rich.multiplicity rich.parentClass
            rich.treeCleanup rich.exactification rich.parentDegree
            rich.core rich.families⟩
      have cap :=
        rich.canonicalOutput.fine_multiplicity_upper_of_critical_inputs
          rich.packetInput rich.multiplicity rich.parentClass
          rich.treeCleanup rich.exactification rich.parentDegree rich.core
          rich.good rich.families
          (Prop62V4CriticalInputsAssembly.criticalForCap
            (routing := routing)) criticalInputs parent
      calc
        (rich.outputCertificate.muFine : ENNReal) ≤
            Kakeya.realRpowENN (delta / rho.1)
                (2 - sigma - routing.numerics.hierarchy.capLoss) *
              (rich.families.terminalFiber rich.packetInput
                rich.multiplicity rich.parentClass rich.treeCleanup
                rich.exactification rich.parentDegree rich.core
                parent).family.enncard := cap
        _ ≤
            Kakeya.realRpowENN (delta / rho.1)
                (2 - sigma - routing.numerics.hierarchy.capLoss) *
              ((2 : ENNReal) * rich.outputCertificate.fiberFloor) := by
          gcongr
          exact
            PureWZ2Prop62PacketCellInput.FourDegreeLemmaOutputData.terminalFiber_enncard_le_two_mul_fiberFloor
              rich.packetInput rich.multiplicity rich.parentClass
              rich.treeCleanup rich.exactification rich.parentDegree rich.core
              rich.good rich.families rich.canonicalOutput parent
        _ = _ := by ring
    have coarseCap :
        (rich.outputCertificate.muCoarse : ENNReal) ≤
          Kakeya.realRpowENN rho.1
              (2 - sigma - routing.numerics.hierarchy.capLoss) *
            rich.outputCertificate.coarse.family.enncard :=
      rich.canonicalOutput.coarse_multiplicity_upper_of_critical_inputs
        rich.packetInput rich.multiplicity rich.parentClass
        rich.treeCleanup rich.exactification rich.parentDegree rich.core
        rich.good rich.families
        (Prop62V4CriticalInputsAssembly.criticalForCap
          (routing := routing)) criticalInputs
    have scalarCross := crossDegreeAbsorption.absorb deltaPos
      deltaCrossDegree produced.metricCertificate.rho_pos rhoUpper
      rich.regularity_bound
    have rawCross := PureWZ2.proposition63_cross_degree_of_mass_ledger
      (sourceLoss := routing.numerics.hierarchy.sourceLoss)
      (capLoss := routing.numerics.hierarchy.capLoss)
      (outputLoss := outputLoss)
      deltaPos produced.metricCertificate.rho_pos
      (wz2PaperPureRefinementFraction delta 61)
      rich.outputCertificate.regularity fineDegree
      rich.outputCertificate.muFine rich.outputCertificate.muCoarse
      rich.outputCertificate.fiberFloor
      rich.outputCertificate.refinement.selected.family.enncard
      rich.outputCertificate.coarse.family.enncard
      rich.outputCertificate.refinement.refined.mass
      (volume rich.outputCertificate.refinement.refined.union)
      (by
        unfold wz2PaperPureRefinementFraction
        apply ENNReal.pow_pos
        apply ENNReal.inv_pos.mpr
        exact ENNReal.ofReal_ne_top)
      (by
        unfold wz2PaperPureRefinementFraction
        apply ENNReal.pow_ne_top
        apply ENNReal.inv_ne_top.mpr
        apply (ENNReal.ofReal_pos.mpr ?_).ne'
        apply Real.log_pos
        apply one_lt_one_div deltaPos
        exact deltaCrossDegree.trans_lt
          crossDegreeAbsorption.delta₀_lt_one)
      (by exact_mod_cast rich.outputCertificate.fiberFloor_pos)
      (ENNReal.natCast_ne_top _) massLower massUpper fineVolumeUpper
      fiberCardinality (by simpa [mul_assoc] using fineCap)
      coarseCap scalarCross
    change Kakeya.realRpowENN rho.1 outputLoss *
          ((rich.outputCertificate.regularity *
            rich.outputCertificate.muCoarse : ℕ) : ENNReal) ≤
        (fineDegree : ENNReal)
    rw [Nat.cast_mul]
    exact rawCross
  · exact outputData.retained_mass

end Kakeya.Assouad.Prop62PaperAudit.V4

namespace Kakeya.Assouad.PureWZ2

/-- A pre-runtime loss schedule whose runtime call returns both the ordinary
sticky output and the exact re-entry certificate for its coarse pair. -/
structure Proposition63RichStickyKernelScheduleData
    (sigma outputLoss : ℝ) where
  sourceLoss : ℝ
  normalizationLoss : ℝ
  sourceLoss_eq :
    sourceLoss = pureWZ2CompleteNormalizationFinalLoss normalizationLoss
  delta₀ : ℝ
  sourceLoss_pos : 0 < sourceLoss
  normalizationLoss_pos : 0 < normalizationLoss
  sourceLoss_le_half : sourceLoss ≤ normalizationLoss / 2
  normalizationLoss_lt_output : normalizationLoss < outputLoss
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  runTerminal :
    ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
      ∀ (croppedFamily : Kakeya.Streamlined.TubeFamily delta)
        (croppedShading : WZ1PaperTubeShading croppedFamily)
        {normalizationExponent : ℕ}
        (reentry : PureWZ2PropStickyReentryData
            (sigma := sigma) croppedShading normalizationExponent
            sourceLoss normalizationLoss),
        ∀ rho : WZ2PaperRequestedScale delta,
          Real.rpow delta (1 - outputLoss) ≤ rho.1 →
          rho.1 ≤ Real.rpow delta outputLoss →
            Nonempty (Proposition63RichTerminalStickyData
              (outputLoss := outputLoss) croppedShading reentry rho)
  runPlain :
    ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
      ∀ (croppedFamily : Kakeya.Streamlined.TubeFamily delta)
        (croppedShading : WZ1PaperTubeShading croppedFamily)
        {normalizationExponent : ℕ}
        (reentry : PureWZ2PropStickyReentryData
            (sigma := sigma) croppedShading normalizationExponent
            sourceLoss normalizationLoss),
        ∀ rho : WZ2PaperRequestedScale delta,
          Real.rpow delta (1 - outputLoss) ≤ rho.1 →
          rho.1 ≤ Real.rpow delta outputLoss →
            Nonempty (PureWZ2PropStickyData
              (sigma := sigma) (outputLoss := outputLoss)
              croppedShading rho 61)
  run :
    ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
      ∀ (croppedFamily : Kakeya.Streamlined.TubeFamily delta)
        (croppedShading : WZ1PaperTubeShading croppedFamily)
        {normalizationExponent : ℕ}
        (reentry : PureWZ2PropStickyReentryData
            (sigma := sigma) croppedShading normalizationExponent
            sourceLoss normalizationLoss),
        (∀ index point,
          point ∈ reentry.geometry.frame ''
              reentry.geometry.ordinaryRefined.carrier index →
            |point (2 : Fin 3)| ≤ 1 / 8) →
        ∀ rho : WZ2PaperRequestedScale delta,
          Real.rpow delta (1 - outputLoss) ≤ rho.1 →
          rho.1 ≤ Real.rpow delta outputLoss →
            Nonempty (PureWZ2ReentrantPropStickyData
              (sigma := sigma) (outputLoss := outputLoss)
              croppedShading rho 0 61)

/-- Preserve the rich output of the closed V4 kernel for Node 4. -/
theorem proposition63_rich_sticky_kernel
    (sigma : ℝ)
    (critical : PureWZ2CriticalPackage sigma)
    (outputLoss : ℝ)
    (outputLoss_pos : 0 < outputLoss)
    (outputLoss_le_one : outputLoss ≤ 1) :
    Nonempty (Proposition63RichStickyKernelScheduleData
      sigma outputLoss) := by
  rcases
      Prop62PaperAudit.V4.pureWZ2_prop_sticky_reentry_v4_rich_terminal_exact_source
        Prop62PaperAudit.V4.fixed_grid_boundary_removal
        Prop62PaperAudit.V4.one_pass_tree_cleanup
        sigma critical outputLoss outputLoss_pos outputLoss_le_one
    with
    ⟨normalizationLoss, delta₀, sourceLoss_pos, normalizationLoss_pos,
      sourceLoss_le_half, normalizationLoss_lt_output, delta₀_pos,
      delta₀_le_one, produce⟩
  refine ⟨{
    sourceLoss := pureWZ2CompleteNormalizationFinalLoss normalizationLoss
    normalizationLoss := normalizationLoss
    sourceLoss_eq := rfl
    delta₀ := delta₀
    sourceLoss_pos := sourceLoss_pos
    normalizationLoss_pos := normalizationLoss_pos
    sourceLoss_le_half := sourceLoss_le_half
    normalizationLoss_lt_output := normalizationLoss_lt_output
    delta₀_pos := delta₀_pos
    delta₀_le_one := delta₀_le_one
    runTerminal := produce
    runPlain := ?_
    run := ?_
  }⟩
  · intro delta delta_pos delta_le croppedFamily croppedShading
      normalizationExponent reentry rho rho_lower rho_upper
    rcases produce delta delta_pos delta_le croppedFamily croppedShading
        reentry rho rho_lower rho_upper with ⟨rich⟩
    exact ⟨rich.data⟩
  intro delta delta_pos delta_le croppedFamily croppedShading
    normalizationExponent reentry axial_window rho rho_lower rho_upper
  rcases produce delta delta_pos delta_le croppedFamily croppedShading
      reentry rho rho_lower rho_upper with ⟨rich⟩
  exact ⟨rich.toReentrant axial_window⟩

/-- Two rich Proposition 6.2 schedules in the paper's dependency order.
The second schedule is chosen first; its source loss is then the exact output
loss budget for the first call.  The factor `1 / 16` leaves room for the
ordinary-density, current-extremality, and two ambient-CWA losses paid by the
genuine current-shading re-entry between the calls. -/
structure Proposition63RichTwoCallScheduleData
    (sigma outputLoss : ℝ) where
  second : Proposition63RichStickyKernelScheduleData sigma outputLoss
  firstOutputLoss : ℝ
  firstOutputLoss_eq : firstOutputLoss = second.sourceLoss / 16
  firstOutputLoss_pos : 0 < firstOutputLoss
  firstOutputLoss_lt_secondSource : firstOutputLoss < second.sourceLoss
  first : Proposition63RichStickyKernelScheduleData sigma firstOutputLoss

/-- Preselect both rich kernel schedules before either runtime scale or
configuration is chosen. -/
theorem proposition63_rich_two_call_schedule
    (sigma : ℝ)
    (critical : PureWZ2CriticalPackage sigma)
    (outputLoss : ℝ)
    (outputLoss_pos : 0 < outputLoss)
    (outputLoss_le_one : outputLoss ≤ 1) :
    Nonempty (Proposition63RichTwoCallScheduleData sigma outputLoss) := by
  rcases proposition63_rich_sticky_kernel sigma critical outputLoss
      outputLoss_pos outputLoss_le_one with ⟨second⟩
  let firstOutputLoss : ℝ := second.sourceLoss / 16
  have firstOutputLoss_pos : 0 < firstOutputLoss := by
    dsimp only [firstOutputLoss]
    linarith [second.sourceLoss_pos]
  have firstOutputLoss_lt_secondSource :
      firstOutputLoss < second.sourceLoss := by
    dsimp only [firstOutputLoss]
    linarith [second.sourceLoss_pos]
  have firstOutputLoss_le_one : firstOutputLoss ≤ 1 := by
    linarith [second.sourceLoss_le_half,
      second.normalizationLoss_lt_output]
  rcases proposition63_rich_sticky_kernel sigma critical firstOutputLoss
      firstOutputLoss_pos firstOutputLoss_le_one with ⟨first⟩
  exact ⟨{
    second := second
    firstOutputLoss := firstOutputLoss
    firstOutputLoss_eq := rfl
    firstOutputLoss_pos := firstOutputLoss_pos
    firstOutputLoss_lt_secondSource := firstOutputLoss_lt_secondSource
    first := first
  }⟩

namespace Proposition63RichTwoCallScheduleData

variable {sigma outputLoss : ℝ}
    (schedule : Proposition63RichTwoCallScheduleData sigma outputLoss)

/-- A root-scale ceiling which makes the exact Proposition 6.3 power scale
small enough for the second kernel as well as the root scale small enough for
the first kernel. -/
noncomputable def rootScaleCeiling : ℝ :=
  min schedule.first.delta₀
    (Real.rpow schedule.second.delta₀ ((2 + sigma) / sigma))

theorem rootScaleCeiling_pos
    (hsigma : 0 < sigma) :
    0 < schedule.rootScaleCeiling := by
  apply lt_min schedule.first.delta₀_pos
  exact Real.rpow_pos_of_pos schedule.second.delta₀_pos _

theorem rootScaleCeiling_le_first :
    schedule.rootScaleCeiling ≤ schedule.first.delta₀ :=
  min_le_left _ _

/-- Below the preselected root ceiling, the exact power scale for the first
call lies below the second kernel's threshold. -/
theorem powerScale_le_second
    (hsigma : 0 < sigma)
    {delta : ℝ}
    (hdelta : 0 < delta)
    (hdeltaRoot : delta ≤ schedule.rootScaleCeiling)
    (power : Proposition63PowerScale delta sigma) :
    power.Delta ≤ schedule.second.delta₀ := by
  have exponent_pos : 0 < sigma / (2 + sigma) := by positivity
  have delta_le_power : delta ≤
      Real.rpow schedule.second.delta₀ ((2 + sigma) / sigma) :=
    hdeltaRoot.trans (min_le_right _ _)
  rw [power.Delta_eq]
  calc
    Real.rpow delta (sigma / (2 + sigma)) ≤
        Real.rpow
          (Real.rpow schedule.second.delta₀ ((2 + sigma) / sigma))
          (sigma / (2 + sigma)) :=
      Real.rpow_le_rpow hdelta.le delta_le_power exponent_pos.le
    _ = Real.rpow schedule.second.delta₀
          (((2 + sigma) / sigma) * (sigma / (2 + sigma))) :=
      (Real.rpow_mul schedule.second.delta₀_pos.le _ _).symm
    _ = schedule.second.delta₀ := by
      have denominator_ne : 2 + sigma ≠ 0 := by positivity
      have sigma_ne : sigma ≠ 0 := hsigma.ne'
      rw [show ((2 + sigma) / sigma) * (sigma / (2 + sigma)) = 1 by
        field_simp [sigma_ne, denominator_ne]]
      exact Real.rpow_one _

/-- Retarget the exact coarse re-entry produced by the first rich call to the
losses selected in advance by the second kernel. -/
noncomputable def reentryForSecond
    {delta : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    (firstOutput : PureWZ2ReentrantPropStickyData
      (sigma := sigma) (outputLoss := schedule.firstOutputLoss)
      sourceShading rho 0 61) :
    PureWZ2PropStickyReentryData
      (sigma := sigma) firstOutput.data.croppedCoarseShading 0
      schedule.second.sourceLoss schedule.second.normalizationLoss :=
  firstOutput.coarseReentry.mono_losses
    (by
      have budget := firstOutput.coarseSourceLoss_budget
      linarith [budget,
        firstOutput.coarseSourceLoss_pos,
        schedule.firstOutputLoss_eq,
        schedule.firstOutputLoss_lt_secondSource])
    (by
      rw [firstOutput.coarseNormalizationLoss_eq]
      have budget := firstOutput.coarseSourceLoss_budget
      linarith [budget,
        schedule.firstOutputLoss_eq,
        schedule.firstOutputLoss_lt_secondSource,
        schedule.second.sourceLoss_le_half,
        firstOutput.coarseSourceLoss_pos,
        schedule.second.normalizationLoss_pos])
    schedule.second.sourceLoss_pos
    schedule.second.normalizationLoss_pos
    schedule.second.sourceLoss_le_half

/-- Execute the second call on the exact first coarse pair.  Only its ordinary
sticky output is needed by Node 4, so no stronger axial-window premise is
introduced at this boundary. -/
theorem runSecond
    {delta : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    (firstOutput : PureWZ2ReentrantPropStickyData
      (sigma := sigma) (outputLoss := schedule.firstOutputLoss)
      sourceShading rho 0 61)
    (hrhoBound : rho.1 ≤ schedule.second.delta₀)
    (tau : WZ2PaperRequestedScale rho.1)
    (tau_lower : Real.rpow rho.1 (1 - outputLoss) ≤ tau.1)
    (tau_upper : tau.1 ≤ Real.rpow rho.1 outputLoss) :
    Nonempty (PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      firstOutput.data.croppedCoarseShading tau 61) :=
  schedule.second.runPlain rho.1 firstOutput.data.coarse_extremal.delta_pos
    hrhoBound firstOutput.data.coarse firstOutput.data.croppedCoarseShading
    (schedule.reentryForSecond firstOutput) tau tau_lower tau_upper

end Proposition63RichTwoCallScheduleData

/-- Three rich Proposition 6.2 schedules in the exact dependency order used
by the paper's Lemma 4.11 interval step: the first call reaches the outer
`rho` family, the second is the arbitrary `tau` one-scale call, and the third
is the separate `sqrt rho` one-scale call made after the `tau` refinement.
The later whole-cell balancing used for full-grain selection is a distinct
step.  All three schedules are chosen before runtime scales and
configurations. -/
structure Proposition63RichThreeCallScheduleData
    (sigma outputLoss : ℝ) where
  third : Proposition63RichStickyKernelScheduleData sigma outputLoss
  secondOutputLoss : ℝ
  secondOutputLoss_eq : secondOutputLoss = third.sourceLoss / 16
  secondOutputLoss_pos : 0 < secondOutputLoss
  secondOutputLoss_lt_thirdSource : secondOutputLoss < third.sourceLoss
  second : Proposition63RichStickyKernelScheduleData sigma secondOutputLoss
  firstOutputLoss : ℝ
  firstOutputLoss_eq : firstOutputLoss = second.sourceLoss / 16
  firstOutputLoss_pos : 0 < firstOutputLoss
  firstOutputLoss_lt_secondSource : firstOutputLoss < second.sourceLoss
  first : Proposition63RichStickyKernelScheduleData sigma firstOutputLoss

/-- Preselect all three rich kernels before any runtime scale or shading is
known. -/
theorem proposition63_rich_three_call_schedule
    (sigma : ℝ)
    (critical : PureWZ2CriticalPackage sigma)
    (outputLoss : ℝ)
    (outputLoss_pos : 0 < outputLoss)
    (outputLoss_le_one : outputLoss ≤ 1) :
    Nonempty (Proposition63RichThreeCallScheduleData sigma outputLoss) := by
  rcases proposition63_rich_sticky_kernel sigma critical outputLoss
      outputLoss_pos outputLoss_le_one with ⟨third⟩
  let secondOutputLoss : ℝ := third.sourceLoss / 16
  have hsecondPos : 0 < secondOutputLoss := by
    dsimp only [secondOutputLoss]
    linarith [third.sourceLoss_pos]
  have hsecondLt : secondOutputLoss < third.sourceLoss := by
    dsimp only [secondOutputLoss]
    linarith [third.sourceLoss_pos]
  have hsecondOne : secondOutputLoss ≤ 1 := by
    linarith [third.sourceLoss_le_half, third.normalizationLoss_lt_output]
  rcases proposition63_rich_sticky_kernel sigma critical secondOutputLoss
      hsecondPos hsecondOne with ⟨second⟩
  let firstOutputLoss : ℝ := second.sourceLoss / 16
  have hfirstPos : 0 < firstOutputLoss := by
    dsimp only [firstOutputLoss]
    linarith [second.sourceLoss_pos]
  have hfirstLt : firstOutputLoss < second.sourceLoss := by
    dsimp only [firstOutputLoss]
    linarith [second.sourceLoss_pos]
  have hfirstOne : firstOutputLoss ≤ 1 := by
    linarith [second.sourceLoss_le_half,
      second.normalizationLoss_lt_output]
  rcases proposition63_rich_sticky_kernel sigma critical firstOutputLoss
      hfirstPos hfirstOne with ⟨first⟩
  exact ⟨{
    third := third
    secondOutputLoss := secondOutputLoss
    secondOutputLoss_eq := rfl
    secondOutputLoss_pos := hsecondPos
    secondOutputLoss_lt_thirdSource := hsecondLt
    second := second
    firstOutputLoss := firstOutputLoss
    firstOutputLoss_eq := rfl
    firstOutputLoss_pos := hfirstPos
    firstOutputLoss_lt_secondSource := hfirstLt
    first := first
  }⟩

namespace Proposition63RichThreeCallScheduleData

variable {sigma outputLoss : ℝ}
    (schedule : Proposition63RichThreeCallScheduleData sigma outputLoss)

/-- Forget the final square-root call and expose the first two calls through
the existing dependent-cover API. -/
noncomputable def firstTwo :
    Proposition63RichTwoCallScheduleData sigma schedule.secondOutputLoss where
  second := schedule.second
  firstOutputLoss := schedule.firstOutputLoss
  firstOutputLoss_eq := schedule.firstOutputLoss_eq
  firstOutputLoss_pos := schedule.firstOutputLoss_pos
  firstOutputLoss_lt_secondSource := schedule.firstOutputLoss_lt_secondSource
  first := schedule.first

end Proposition63RichThreeCallScheduleData

/-- Four rich Proposition 6.2 schedules in the dependency order required by
two robust Lemma 17 localizations.  The first call reaches the outer `rho`
family.  At the `rho` level, the second/third calls form the outer/target pair
for the arbitrary `tau` localization.  Its point cover is restored on the
third call's exact zero-extension, so that terminal is the outer witness for
the fourth, square-root target call. -/
structure Proposition63RichFourCallScheduleData
    (sigma outputLoss : ℝ) where
  fourth : Proposition63RichStickyKernelScheduleData sigma outputLoss
  thirdOutputLoss : ℝ
  thirdOutputLoss_eq : thirdOutputLoss = fourth.sourceLoss / 16
  thirdOutputLoss_pos : 0 < thirdOutputLoss
  thirdOutputLoss_lt_fourthSource : thirdOutputLoss < fourth.sourceLoss
  third : Proposition63RichStickyKernelScheduleData sigma thirdOutputLoss
  secondOutputLoss : ℝ
  secondOutputLoss_eq : secondOutputLoss = third.sourceLoss / 16
  secondOutputLoss_pos : 0 < secondOutputLoss
  secondOutputLoss_lt_thirdSource : secondOutputLoss < third.sourceLoss
  second : Proposition63RichStickyKernelScheduleData sigma secondOutputLoss
  firstOutputLoss : ℝ
  firstOutputLoss_eq : firstOutputLoss = second.sourceLoss / 16
  firstOutputLoss_pos : 0 < firstOutputLoss
  firstOutputLoss_lt_secondSource : firstOutputLoss < second.sourceLoss
  first : Proposition63RichStickyKernelScheduleData sigma firstOutputLoss

/-- Preselect the four rich kernels needed by two robust localizations before
any runtime scale, family, or shading is known. -/
theorem proposition63_rich_four_call_schedule
    (sigma : ℝ)
    (critical : PureWZ2CriticalPackage sigma)
    (outputLoss : ℝ)
    (outputLoss_pos : 0 < outputLoss)
    (outputLoss_le_one : outputLoss ≤ 1) :
    Nonempty (Proposition63RichFourCallScheduleData sigma outputLoss) := by
  rcases proposition63_rich_sticky_kernel sigma critical outputLoss
      outputLoss_pos outputLoss_le_one with ⟨fourth⟩
  let thirdOutputLoss : ℝ := fourth.sourceLoss / 16
  have hthirdPos : 0 < thirdOutputLoss := by
    dsimp only [thirdOutputLoss]
    linarith [fourth.sourceLoss_pos]
  have hthirdLt : thirdOutputLoss < fourth.sourceLoss := by
    dsimp only [thirdOutputLoss]
    linarith [fourth.sourceLoss_pos]
  have hthirdOne : thirdOutputLoss ≤ 1 := by
    dsimp only [thirdOutputLoss]
    linarith [fourth.sourceLoss_le_half,
      fourth.normalizationLoss_lt_output]
  rcases proposition63_rich_sticky_kernel sigma critical thirdOutputLoss
      hthirdPos hthirdOne with ⟨third⟩
  let secondOutputLoss : ℝ := third.sourceLoss / 16
  have hsecondPos : 0 < secondOutputLoss := by
    dsimp only [secondOutputLoss]
    linarith [third.sourceLoss_pos]
  have hsecondLt : secondOutputLoss < third.sourceLoss := by
    dsimp only [secondOutputLoss]
    linarith [third.sourceLoss_pos]
  have hsecondOne : secondOutputLoss ≤ 1 := by
    dsimp only [secondOutputLoss]
    linarith [third.sourceLoss_le_half, third.normalizationLoss_lt_output]
  rcases proposition63_rich_sticky_kernel sigma critical secondOutputLoss
      hsecondPos hsecondOne with ⟨second⟩
  let firstOutputLoss : ℝ := second.sourceLoss / 16
  have hfirstPos : 0 < firstOutputLoss := by
    dsimp only [firstOutputLoss]
    linarith [second.sourceLoss_pos]
  have hfirstLt : firstOutputLoss < second.sourceLoss := by
    dsimp only [firstOutputLoss]
    linarith [second.sourceLoss_pos]
  have hfirstOne : firstOutputLoss ≤ 1 := by
    dsimp only [firstOutputLoss]
    linarith [second.sourceLoss_le_half, second.normalizationLoss_lt_output]
  rcases proposition63_rich_sticky_kernel sigma critical firstOutputLoss
      hfirstPos hfirstOne with ⟨first⟩
  exact ⟨{
    fourth := fourth
    thirdOutputLoss := thirdOutputLoss
    thirdOutputLoss_eq := rfl
    thirdOutputLoss_pos := hthirdPos
    thirdOutputLoss_lt_fourthSource := hthirdLt
    third := third
    secondOutputLoss := secondOutputLoss
    secondOutputLoss_eq := rfl
    secondOutputLoss_pos := hsecondPos
    secondOutputLoss_lt_thirdSource := hsecondLt
    second := second
    firstOutputLoss := firstOutputLoss
    firstOutputLoss_eq := rfl
    firstOutputLoss_pos := hfirstPos
    firstOutputLoss_lt_secondSource := hfirstLt
    first := first
  }⟩

namespace Proposition63RichFourCallScheduleData

variable {sigma outputLoss : ℝ}
    (schedule : Proposition63RichFourCallScheduleData sigma outputLoss)

/-- The first three calls: fine to `rho`, followed by the outer and target
rich calls for the arbitrary `tau` robust localization. -/
noncomputable def firstThree :
    Proposition63RichThreeCallScheduleData sigma schedule.thirdOutputLoss where
  third := schedule.third
  secondOutputLoss := schedule.secondOutputLoss
  secondOutputLoss_eq := schedule.secondOutputLoss_eq
  secondOutputLoss_pos := schedule.secondOutputLoss_pos
  secondOutputLoss_lt_thirdSource := schedule.secondOutputLoss_lt_thirdSource
  second := schedule.second
  firstOutputLoss := schedule.firstOutputLoss
  firstOutputLoss_eq := schedule.firstOutputLoss_eq
  firstOutputLoss_pos := schedule.firstOutputLoss_pos
  firstOutputLoss_lt_secondSource := schedule.firstOutputLoss_lt_secondSource
  first := schedule.first

/-- The last three calls at the `rho` level: the first robust outer, the first
target (which remains the second robust outer), and the square-root target. -/
noncomputable def lastThree :
    Proposition63RichThreeCallScheduleData sigma outputLoss where
  third := schedule.fourth
  secondOutputLoss := schedule.thirdOutputLoss
  secondOutputLoss_eq := schedule.thirdOutputLoss_eq
  secondOutputLoss_pos := schedule.thirdOutputLoss_pos
  secondOutputLoss_lt_thirdSource := schedule.thirdOutputLoss_lt_fourthSource
  second := schedule.third
  firstOutputLoss := schedule.secondOutputLoss
  firstOutputLoss_eq := schedule.secondOutputLoss_eq
  firstOutputLoss_pos := schedule.secondOutputLoss_pos
  firstOutputLoss_lt_secondSource := schedule.secondOutputLoss_lt_thirdSource
  first := schedule.second

end Proposition63RichFourCallScheduleData

end Kakeya.Assouad.PureWZ2

end
