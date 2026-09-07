import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05IndexedIncidenceExactification
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalFineExactBalancingHelpers

/-!
# Finite value bound for cubical indexed incidence mass

Inside a retained coarse cell, an exactly balanced cubical shading is a finite
union of selected literal fine cells.  Counting the fine cells separately for
each indexed tube expresses the actual indexed incidence mass as an integer
multiple of one fine-cell volume.
-/

noncomputable section

open MeasureTheory Set

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- Selected fine cells in one coarse cell which belong to one indexed tube. -/
def pureWZ2Node05TubeFineCells
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading fine}
    {coarseCells : Finset WZ2PaperCellIndex}
    {availableFineCells : WZ2PaperCellIndex → Finset WZ2PaperCellIndex}
    (balancing : WZ2PaperExactCellBalancingData
      (delta := delta) (rho := rho) shading coarseCells availableFineCells)
    (cell : WZ2PaperCellIndex) (source : Fin fine.card) :
    Finset WZ2PaperCellIndex :=
  (balancing.selectedFineCells cell).filter fun fineCell =>
    wz1PaperGridCube delta fineCell ⊆ balancing.refined.carrier source

/-- The tube--fine-cell incidence count in one retained coarse cell. -/
def pureWZ2Node05CubicalIncidenceCount
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading fine}
    {coarseCells : Finset WZ2PaperCellIndex}
    {availableFineCells : WZ2PaperCellIndex → Finset WZ2PaperCellIndex}
    (balancing : WZ2PaperExactCellBalancingData
      (delta := delta) (rho := rho) shading coarseCells availableFineCells)
    (cell : WZ2PaperCellIndex) : ℕ :=
  ∑ source : Fin fine.card,
    (pureWZ2Node05TubeFineCells balancing cell source).card

theorem pureWZ2Node05_refinedCarrier_inter_coarseCell
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading fine}
    {coarseCells : Finset WZ2PaperCellIndex}
    {availableFineCells : WZ2PaperCellIndex → Finset WZ2PaperCellIndex}
    (balancing : WZ2PaperExactCellBalancingData
      (delta := delta) (rho := rho) shading coarseCells availableFineCells)
    {cell : WZ2PaperCellIndex}
    (hcell : cell ∈ balancing.retainedCoarseCells)
    (source : Fin fine.card) :
    balancing.refined.carrier source ∩ wz1PaperGridCube rho cell =
      ⋃ fineCell ∈ pureWZ2Node05TubeFineCells balancing cell source,
        wz1PaperGridCube delta fineCell := by
  have hunion :
      balancing.refined.union ∩ wz1PaperGridCube rho cell =
        ⋃ fineCell ∈ balancing.selectedFineCells cell,
          wz1PaperGridCube delta fineCell := by
    rw [balancing.refined_union_eq]
    exact wz2RefinedUnion_inter_coarseCube
      balancing.retainedFineCells_eq balancing.fine_cell_containment hcell
  ext point
  constructor
  · rintro ⟨hcarrier, hcoarse⟩
    have hunionPoint : point ∈
        balancing.refined.union ∩ wz1PaperGridCube rho cell :=
      ⟨⟨source, hcarrier⟩, hcoarse⟩
    rw [hunion] at hunionPoint
    rcases Set.mem_iUnion₂.mp hunionPoint with
      ⟨fineCell, hfineCell, hpointFine⟩
    have hindex : wz1PaperGridIndex delta point = fineCell :=
      (mem_wz1PaperGridCube delta fineCell point).mp hpointFine
    have hcube :
        wz1PaperGridCube delta fineCell ⊆ balancing.refined.carrier source := by
      simpa only [hindex] using
        balancing.refined_cubical source point hcarrier
    exact Set.mem_iUnion₂.mpr
      ⟨fineCell, Finset.mem_filter.mpr ⟨hfineCell, hcube⟩, hpointFine⟩
  · intro hpoint
    rcases Set.mem_iUnion₂.mp hpoint with
      ⟨fineCell, hfineCell, hpointFine⟩
    have hfineData := (Finset.mem_filter.mp hfineCell).2
    exact
      ⟨hfineData hpointFine,
        balancing.fine_cell_containment cell hcell fineCell
          (Finset.mem_filter.mp hfineCell).1 hpointFine⟩

theorem pureWZ2Node05_refinedCarrier_inter_coarseCell_volume
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading fine}
    {coarseCells : Finset WZ2PaperCellIndex}
    {availableFineCells : WZ2PaperCellIndex → Finset WZ2PaperCellIndex}
    (balancing : WZ2PaperExactCellBalancingData
      (delta := delta) (rho := rho) shading coarseCells availableFineCells)
    (hdelta : 0 < delta)
    {cell : WZ2PaperCellIndex}
    (hcell : cell ∈ balancing.retainedCoarseCells)
    (source : Fin fine.card) :
    volume (balancing.refined.carrier source ∩ wz1PaperGridCube rho cell) =
      ((pureWZ2Node05TubeFineCells balancing cell source).card : ENNReal) *
        volume (wz1PaperGridCube delta (0, 0, 0)) := by
  rw [pureWZ2Node05_refinedCarrier_inter_coarseCell balancing hcell source]
  exact wz1PaperGridCube_volume_biUnion hdelta _

theorem pureWZ2Node05_cellIncidenceMass_eq_count_mul
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading fine}
    {coarseCells : Finset WZ2PaperCellIndex}
    {availableFineCells : WZ2PaperCellIndex → Finset WZ2PaperCellIndex}
    (balancing : WZ2PaperExactCellBalancingData
      (delta := delta) (rho := rho) shading coarseCells availableFineCells)
    (hdelta : 0 < delta)
    {cell : WZ2PaperCellIndex}
    (hcell : cell ∈ balancing.retainedCoarseCells) :
    wz2PaperCellIncidenceMass (rho := rho) balancing.refined cell =
      (pureWZ2Node05CubicalIncidenceCount balancing cell : ENNReal) *
        volume (wz1PaperGridCube delta (0, 0, 0)) := by
  unfold wz2PaperCellIncidenceMass pureWZ2Node05CubicalIncidenceCount
  simp_rw [pureWZ2Node05_refinedCarrier_inter_coarseCell_volume
    balancing hdelta hcell]
  rw [← Finset.sum_mul, Nat.cast_sum]

theorem pureWZ2Node05_cubicalIncidenceCount_le
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading fine}
    {coarseCells : Finset WZ2PaperCellIndex}
    {availableFineCells : WZ2PaperCellIndex → Finset WZ2PaperCellIndex}
    (balancing : WZ2PaperExactCellBalancingData
      (delta := delta) (rho := rho) shading coarseCells availableFineCells)
    {cell : WZ2PaperCellIndex}
    (hcell : cell ∈ balancing.retainedCoarseCells) :
    pureWZ2Node05CubicalIncidenceCount balancing cell ≤
      (2 ^ balancing.level) * fine.card := by
  unfold pureWZ2Node05CubicalIncidenceCount
  calc
    (∑ source : Fin fine.card,
        (pureWZ2Node05TubeFineCells balancing cell source).card) ≤
        ∑ _source : Fin fine.card, (balancing.selectedFineCells cell).card := by
      apply Finset.sum_le_sum
      intro source _
      exact Finset.card_le_card (Finset.filter_subset _ _)
    _ = fine.card * (balancing.selectedFineCells cell).card := by simp
    _ = (2 ^ balancing.level) * fine.card := by
      rw [balancing.selectedFineCells_card cell hcell]
      exact Nat.mul_comm _ _

/-- The actual indexed incidence mass realizes at most one value for every
possible tube--fine-cell incidence count. -/
theorem pureWZ2Node05_cubicalIncidence_valueCard_le
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading fine}
    {coarseCells : Finset WZ2PaperCellIndex}
    {availableFineCells : WZ2PaperCellIndex → Finset WZ2PaperCellIndex}
    (balancing : WZ2PaperExactCellBalancingData
      (delta := delta) (rho := rho) shading coarseCells availableFineCells)
    (hdelta : 0 < delta) :
    (balancing.retainedCoarseCells.image fun cell =>
        wz2PaperCellIncidenceMass (rho := rho) balancing.refined cell).card ≤
      (2 ^ balancing.level) * fine.card + 1 := by
  let bound := (2 ^ balancing.level) * fine.card
  let values : Finset ENNReal :=
    (Finset.range (bound + 1)).image fun count : ℕ =>
      (count : ENNReal) *
        volume (wz1PaperGridCube delta (0, 0, 0))
  have himageSubset :
      (balancing.retainedCoarseCells.image fun cell =>
          wz2PaperCellIncidenceMass (rho := rho) balancing.refined cell) ⊆
        values := by
    intro value hvalue
    rcases Finset.mem_image.mp hvalue with ⟨cell, hcell, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨pureWZ2Node05CubicalIncidenceCount balancing cell, ?_, ?_⟩
    · rw [Finset.mem_range]
      exact Nat.lt_succ_of_le
        (pureWZ2Node05_cubicalIncidenceCount_le balancing hcell)
    · exact (pureWZ2Node05_cellIncidenceMass_eq_count_mul
        balancing hdelta hcell).symm
  calc
    (balancing.retainedCoarseCells.image fun cell =>
        wz2PaperCellIncidenceMass (rho := rho) balancing.refined cell).card ≤
        values.card := Finset.card_le_card himageSubset
    _ ≤ (Finset.range (bound + 1)).card := Finset.card_image_le
    _ = (2 ^ balancing.level) * fine.card + 1 := by simp [bound]

/-! ## Generic V4-facing version

The declarations below do not mention exact balancing data.  They use only
the cubical fine shading and the retained fine-cell nesting certificate which
survives in the V4 output.
-/

/-- Delta cells of one indexed fine carrier which lie inside one rho-cell. -/
def pureWZ2Node05GenericSourceCellsAt
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (hdelta : 0 < delta)
    (fineShading : WZ1PaperTubeShading fine)
    (source : Fin fine.card) (cell : WZ2PaperCellIndex) :
    Finset WZ2PaperCellIndex :=
  (wz1PaperGridIndicesInWindow delta hdelta).filter fun fineCell =>
    wz1PaperGridCube delta fineCell ⊆ fineShading.carrier source ∧
      wz1PaperGridCube delta fineCell ⊆ wz1PaperGridCube rho cell

/-- Integer coefficient of the actual indexed incidence mass, without any
balancing-data dependency. -/
def pureWZ2Node05GenericIncidenceCoefficient
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (hdelta : 0 < delta)
    (fineShading : WZ1PaperTubeShading fine)
    (cell : WZ2PaperCellIndex) : ℕ :=
  ∑ source : Fin fine.card,
    (pureWZ2Node05GenericSourceCellsAt (rho := rho)
      hdelta fineShading source cell).card

theorem pureWZ2Node05_genericSourceCarrierInter_eq_cellsUnion
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (hdelta : 0 < delta)
    {fineShading : WZ1PaperTubeShading fine}
    (hcubical : WZ1PaperIsCubicalShading fineShading)
    {activeCells : Finset WZ2PaperCellIndex}
    (hfineCellNested :
      ∀ source point, point ∈ fineShading.carrier source →
        ∃ cell ∈ activeCells,
          wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆
            wz1PaperGridCube rho cell)
    (source : Fin fine.card) (cell : WZ2PaperCellIndex) :
    fineShading.carrier source ∩ wz1PaperGridCube rho cell =
      ⋃ fineCell ∈ pureWZ2Node05GenericSourceCellsAt (rho := rho)
          hdelta fineShading source cell,
        wz1PaperGridCube delta fineCell := by
  ext point
  constructor
  · rintro ⟨hcarrier, hcell⟩
    let fineCell := wz1PaperGridIndex delta point
    have hpointFine : point ∈ wz1PaperGridCube delta fineCell :=
      (mem_wz1PaperGridCube delta fineCell point).mpr rfl
    have hwindow : fineCell ∈ wz1PaperGridIndicesInWindow delta hdelta := by
      apply paper_point_gridIndex_in_window hdelta
      exact (fineShading.subset_body source hcarrier).2
    have hcarrierCube :
        wz1PaperGridCube delta fineCell ⊆ fineShading.carrier source :=
      hcubical source point hcarrier
    rcases hfineCellNested source point hcarrier with
      ⟨nestedCell, _hnestedActive, hnested⟩
    have hpointNested := hnested hpointFine
    have hcellsEq : nestedCell = cell :=
      ((mem_wz1PaperGridCube rho nestedCell point).mp hpointNested).symm.trans
        ((mem_wz1PaperGridCube rho cell point).mp hcell)
    have hrhoCube :
        wz1PaperGridCube delta fineCell ⊆ wz1PaperGridCube rho cell := by
      simpa only [hcellsEq] using hnested
    exact Set.mem_iUnion₂.mpr
      ⟨fineCell, Finset.mem_filter.mpr
        ⟨hwindow, hcarrierCube, hrhoCube⟩, hpointFine⟩
  · intro hpoint
    rcases Set.mem_iUnion₂.mp hpoint with
      ⟨fineCell, hfineCell, hpointFine⟩
    have hdata := (Finset.mem_filter.mp hfineCell).2
    exact ⟨hdata.1 hpointFine, hdata.2 hpointFine⟩

theorem pureWZ2Node05_genericSourceCarrierInter_volume
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (hdelta : 0 < delta)
    {fineShading : WZ1PaperTubeShading fine}
    (hcubical : WZ1PaperIsCubicalShading fineShading)
    {activeCells : Finset WZ2PaperCellIndex}
    (hfineCellNested :
      ∀ source point, point ∈ fineShading.carrier source →
        ∃ cell ∈ activeCells,
          wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆
            wz1PaperGridCube rho cell)
    (source : Fin fine.card) (cell : WZ2PaperCellIndex) :
    volume (fineShading.carrier source ∩ wz1PaperGridCube rho cell) =
      ((pureWZ2Node05GenericSourceCellsAt (rho := rho)
          hdelta fineShading source cell).card : ENNReal) *
        volume (wz1PaperGridCube delta (0, 0, 0)) := by
  rw [pureWZ2Node05_genericSourceCarrierInter_eq_cellsUnion
    hdelta hcubical hfineCellNested source cell]
  exact wz1PaperGridCube_volume_biUnion hdelta _

theorem pureWZ2Node05_genericIncidenceMass_eq_coefficient_mul
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (hdelta : 0 < delta)
    {fineShading : WZ1PaperTubeShading fine}
    (hcubical : WZ1PaperIsCubicalShading fineShading)
    {activeCells : Finset WZ2PaperCellIndex}
    (hfineCellNested :
      ∀ source point, point ∈ fineShading.carrier source →
        ∃ cell ∈ activeCells,
          wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆
            wz1PaperGridCube rho cell)
    (cell : WZ2PaperCellIndex) :
    wz2PaperCellIncidenceMass (rho := rho) fineShading cell =
      (pureWZ2Node05GenericIncidenceCoefficient (rho := rho)
          hdelta fineShading cell : ENNReal) *
        volume (wz1PaperGridCube delta (0, 0, 0)) := by
  unfold wz2PaperCellIncidenceMass
    pureWZ2Node05GenericIncidenceCoefficient
  simp_rw [pureWZ2Node05_genericSourceCarrierInter_volume
    hdelta hcubical hfineCellNested]
  rw [← Finset.sum_mul, Nat.cast_sum]

theorem pureWZ2Node05_genericIncidenceCoefficient_le
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (hdelta : 0 < delta)
    (fineShading : WZ1PaperTubeShading fine)
    (cell : WZ2PaperCellIndex) :
    pureWZ2Node05GenericIncidenceCoefficient (rho := rho)
        hdelta fineShading cell ≤
      fine.card * (wz1PaperGridIndicesInWindow delta hdelta).card := by
  unfold pureWZ2Node05GenericIncidenceCoefficient
  calc
    (∑ source : Fin fine.card,
        (pureWZ2Node05GenericSourceCellsAt (rho := rho)
          hdelta fineShading source cell).card) ≤
        ∑ _source : Fin fine.card,
          (wz1PaperGridIndicesInWindow delta hdelta).card := by
      apply Finset.sum_le_sum
      intro source _
      exact Finset.card_le_card (Finset.filter_subset _ _)
    _ = fine.card * (wz1PaperGridIndicesInWindow delta hdelta).card := by
      simp

/-- Generic realized-value bound suitable for the V4 output certificate. -/
theorem pureWZ2Node05_genericCubicalIncidence_valueCard_le
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (hdelta : 0 < delta)
    {fineShading : WZ1PaperTubeShading fine}
    (hcubical : WZ1PaperIsCubicalShading fineShading)
    (activeCells : Finset WZ2PaperCellIndex)
    (hfineCellNested :
      ∀ source point, point ∈ fineShading.carrier source →
        ∃ cell ∈ activeCells,
          wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆
            wz1PaperGridCube rho cell) :
    (activeCells.image fun cell =>
        wz2PaperCellIncidenceMass (rho := rho) fineShading cell).card ≤
      fine.card * (wz1PaperGridIndicesInWindow delta hdelta).card + 1 := by
  let bound := fine.card * (wz1PaperGridIndicesInWindow delta hdelta).card
  let values : Finset ENNReal :=
    (Finset.range (bound + 1)).image fun coefficient : ℕ =>
      (coefficient : ENNReal) *
        volume (wz1PaperGridCube delta (0, 0, 0))
  have himageSubset :
      (activeCells.image fun cell =>
          wz2PaperCellIncidenceMass (rho := rho) fineShading cell) ⊆ values := by
    intro value hvalue
    rcases Finset.mem_image.mp hvalue with ⟨cell, hcell, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨pureWZ2Node05GenericIncidenceCoefficient (rho := rho)
      hdelta fineShading cell, ?_, ?_⟩
    · rw [Finset.mem_range]
      exact Nat.lt_succ_of_le
        (pureWZ2Node05_genericIncidenceCoefficient_le
          hdelta fineShading cell)
    · exact (pureWZ2Node05_genericIncidenceMass_eq_coefficient_mul
        hdelta hcubical hfineCellNested cell).symm
  calc
    (activeCells.image fun cell =>
        wz2PaperCellIncidenceMass (rho := rho) fineShading cell).card ≤
        values.card := Finset.card_le_card himageSubset
    _ ≤ (Finset.range (bound + 1)).card := Finset.card_image_le
    _ = fine.card * (wz1PaperGridIndicesInWindow delta hdelta).card + 1 := by
      simp [bound]

end Kakeya.Assouad

end
