import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63OneScaleFullGrainCell
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CellMassConversion
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CardinalityFix
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalFineExactBalancingHelpers

/-!
# Globalization of the one-scale full-grain cells

This module makes the finite choice of one full-grain/Fubini certificate in
every active square-root cell.  Their good regions are disjoint because each
stays inside its actual grid cell.  Consequently their union retains at least
half of the one-scale union volume.  Conversion of this volume statement into
shading mass is kept separate and uses genuine pointwise multiplicity bounds.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set ENNReal Metric

attribute [local instance] Classical.propDecidable

/-- One compatible full-grain/Fubini certificate for every active balanced
square-root cell. -/
structure Proposition63OneScaleFullGrainCellsData
    {delta sigma outputLoss queryScale sqrtScale : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    (planeMap : Point3 → Point3)
    (oneScale : PureWZ2OneScaleLocalGrainData
      (sigma := sigma) (outputLoss := outputLoss)
      (rho := queryScale) (Y := source) (fun point => planeMap point))
    (cells : Proposition63BalancedCellData (scale := sqrtScale)
      oneScale.shading)
    (lineVolume : ℝ) (coverBudget : ℕ) where
  cellData :
    ∀ cell : {cell // cell ∈ cells.activeCells},
      Proposition63FullGrainFubiniCellData
        (oneScale.shading.union ∩
          wz1PaperGridCube sqrtScale cell.1)
        (planeMap (cells.cellRep cell.1 cell.2))
        queryScale (2 * sqrtScale) lineVolume
        (cells.cellMass / 2)
        ((cells.cellMass / 2) /
          (2 * (coverBudget : ENNReal)))

/-- Apply the one-cell construction simultaneously to every active cell. -/
theorem proposition63_oneScale_fullGrainFubiniCells
    {delta sigma outputLoss queryScale sqrtScale K lineVolume : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    (planeMap : Point3 → Point3)
    (oneScale : PureWZ2OneScaleLocalGrainData
      (sigma := sigma) (outputLoss := outputLoss)
      (rho := queryScale) (Y := source) (fun point => planeMap point))
    (cells : Proposition63BalancedCellData (scale := sqrtScale)
      oneScale.shading)
    (hqueryOne : queryScale ≤ 1)
    (hsqrtScale : sqrtScale = Real.sqrt queryScale)
    (hplaneUnit : ∀ point ∈ oneScale.shading.union,
      ‖planeMap point‖ = 1)
    (hK : 1 ≤ K)
    (hplaneLipschitz : ∀ first ∈ oneScale.shading.union,
      ∀ second ∈ oneScale.shading.union,
        dist (planeMap first) (planeMap second) ≤
          K * dist first second)
    (coverBudget : ℕ) (hcoverBudgetPos : 0 < coverBudget)
    (hcoverBudget :
      (512 : ENNReal) *
          ((2 * Nat.ceil (2 * K) + 2 : ENNReal) *
            (9 * Kakeya.realRpowENN delta (-outputLoss) *
              Kakeya.realRpowENN (1 / queryScale) (1 - sigma))) ≤
        (coverBudget : ENNReal))
    (hlineVolume : 0 < lineVolume)
    (hlineFloor : ENNReal.ofReal lineVolume ≤ cells.cellMass / 2) :
    Nonempty
      (Proposition63OneScaleFullGrainCellsData planeMap oneScale cells
        lineVolume coverBudget) := by
  let selected := fun cell : {cell // cell ∈ cells.activeCells} =>
    Classical.choice
      (proposition63_oneScale_fullGrainFubiniCell_of_cells planeMap oneScale cells
        cell.1 cell.2 hqueryOne hsqrtScale hplaneUnit hK
        hplaneLipschitz coverBudget hcoverBudgetPos hcoverBudget
        hlineVolume hlineFloor)
  exact ⟨{ cellData := selected }⟩

namespace Proposition63OneScaleFullGrainCellsData

variable
    {delta sigma outputLoss queryScale sqrtScale : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {planeMap : Point3 → Point3}
    {oneScale : PureWZ2OneScaleLocalGrainData
      (sigma := sigma) (outputLoss := outputLoss)
      (rho := queryScale) (Y := source) (fun point => planeMap point)}
    {cells : Proposition63BalancedCellData (scale := sqrtScale)
      oneScale.shading}
    {lineVolume : ℝ} {coverBudget : ℕ}

/-- The selected good region in one cell, extended by the empty set away from
the active-cell index set. -/
def cellGood
    (data : Proposition63OneScaleFullGrainCellsData planeMap oneScale
      cells lineVolume coverBudget)
    (cell : ℤ × ℤ × ℤ) : Set Point3 :=
  if hcell : cell ∈ cells.activeCells then
    (data.cellData ⟨cell, hcell⟩).good
  else ∅

lemma cellGood_eq
    (data : Proposition63OneScaleFullGrainCellsData planeMap oneScale
      cells lineVolume coverBudget)
    (cell : ℤ × ℤ × ℤ) (hcell : cell ∈ cells.activeCells) :
    data.cellGood cell = (data.cellData ⟨cell, hcell⟩).good := by
  simp [cellGood, hcell]

/-- The common measurable restriction selected across all active cells. -/
def goodRegion
    (data : Proposition63OneScaleFullGrainCellsData planeMap oneScale
      cells lineVolume coverBudget) : Set Point3 :=
  ⋃ cell ∈ cells.activeCells, data.cellGood cell

theorem goodRegion_measurable
    (data : Proposition63OneScaleFullGrainCellsData planeMap oneScale
      cells lineVolume coverBudget) :
    MeasurableSet data.goodRegion := by
  apply MeasurableSet.biUnion
    (Finset.finite_toSet cells.activeCells).countable
  intro cell hcell
  rw [data.cellGood_eq cell hcell]
  exact (data.cellData ⟨cell, hcell⟩).good_measurable

theorem cellGood_subset_cell
    (data : Proposition63OneScaleFullGrainCellsData planeMap oneScale
      cells lineVolume coverBudget)
    (cell : ℤ × ℤ × ℤ) (hcell : cell ∈ cells.activeCells) :
    data.cellGood cell ⊆ wz1PaperGridCube sqrtScale cell := by
  rw [data.cellGood_eq cell hcell]
  exact (data.cellData ⟨cell, hcell⟩).good_subset.trans
    Set.inter_subset_right

theorem goodRegion_subset
    (data : Proposition63OneScaleFullGrainCellsData planeMap oneScale
      cells lineVolume coverBudget) :
    data.goodRegion ⊆ oneScale.shading.union := by
  intro point hpoint
  rcases Set.mem_iUnion₂.mp hpoint with ⟨cell, hcell, hpointGood⟩
  rw [data.cellGood_eq cell hcell] at hpointGood
  exact (data.cellData ⟨cell, hcell⟩).good_subset hpointGood |>.1

/-- The finite union of the chosen cellwise good regions retains at least half
of the one-scale union volume. -/
theorem goodRegion_half_volume
    (data : Proposition63OneScaleFullGrainCellsData planeMap oneScale
      cells lineVolume coverBudget)
    (hsqrtScale : 0 < sqrtScale) :
    volume oneScale.shading.union ≤ 2 * volume data.goodRegion := by
  have hdisjoint : Set.PairwiseDisjoint (↑cells.activeCells)
      data.cellGood := by
    intro first _ second _ hne
    exact (wz1PaperGridCube_disjoint hne).mono
      (data.cellGood_subset_cell first ‹first ∈ cells.activeCells›)
      (data.cellGood_subset_cell second ‹second ∈ cells.activeCells›)
  have hmeasurable : ∀ cell ∈ cells.activeCells,
      MeasurableSet (data.cellGood cell) := by
    intro cell hcell
    rw [data.cellGood_eq cell hcell]
    exact (data.cellData ⟨cell, hcell⟩).good_measurable
  have hsum :
      (cells.activeCells.card : ENNReal) * (cells.cellMass / 2) ≤
        ∑ cell ∈ cells.activeCells, volume (data.cellGood cell) := by
    calc
      (cells.activeCells.card : ENNReal) *
            (cells.cellMass / 2) =
          ∑ cell ∈ cells.activeCells, cells.cellMass / 2 := by
            simp [Finset.sum_const]
      _ ≤ ∑ cell ∈ cells.activeCells, volume (data.cellGood cell) :=
        Finset.sum_le_sum fun cell hcell => by
          rw [data.cellGood_eq cell hcell]
          exact (data.cellData ⟨cell, hcell⟩).good_volume
  have hunion :
      volume data.goodRegion =
        ∑ cell ∈ cells.activeCells, volume (data.cellGood cell) := by
    exact MeasureTheory.measure_biUnion_finset hdisjoint hmeasurable
  rw [cells.fine_union_volume, hunion]
  have hhalf : 2 * (cells.cellMass / 2) = cells.cellMass :=
    ENNReal.mul_div_cancel (by norm_num) (by norm_num)
  calc
    (cells.activeCells.card : ENNReal) * cells.cellMass
        = (cells.activeCells.card : ENNReal) *
            (2 * (cells.cellMass / 2)) := by rw [hhalf]
    _ = 2 * ((cells.activeCells.card : ENNReal) *
          (cells.cellMass / 2)) := by ac_rfl
    _ ≤ 2 * ∑ cell ∈ cells.activeCells, volume (data.cellGood cell) :=
      mul_le_mul_left' hsum 2

/-- Restrict the one-scale shading to the common finite union of the selected
cellwise good regions. -/
def retainedShading
    (data : Proposition63OneScaleFullGrainCellsData planeMap oneScale
      cells lineVolume coverBudget) :
    WZ1PaperTubeShading family :=
  paperRestrictShadingToSet oneScale.shading data.goodRegion
    data.goodRegion_measurable

theorem retainedShading_subshading
    (data : Proposition63OneScaleFullGrainCellsData planeMap oneScale
      cells lineVolume coverBudget) :
    PaperIsSubshading' data.retainedShading oneScale.shading := by
  intro index point hpoint
  exact hpoint.1

theorem retainedShading_union
    (data : Proposition63OneScaleFullGrainCellsData planeMap oneScale
      cells lineVolume coverBudget) :
    data.retainedShading.union = data.goodRegion := by
  ext point
  constructor
  · rintro ⟨index, hpoint⟩
    exact hpoint.2
  · intro hpoint
    rcases data.goodRegion_subset hpoint with ⟨index, hindex⟩
    exact ⟨index, hindex, hpoint⟩

/-- If the one-scale shading already has point multiplicity in the genuine
band `[multiplicity, 2 * multiplicity)`, the common full-grain restriction
retains at least one quarter of its shading mass. -/
theorem retainedShading_quarter_mass
    (data : Proposition63OneScaleFullGrainCellsData planeMap oneScale
      cells lineVolume coverBudget)
    (hsqrtScale : 0 < sqrtScale)
    (multiplicity : ENNReal) (hmultiplicityTop : multiplicity ≠ ⊤)
    (hmultiplicityLower : ∀ point ∈ oneScale.shading.union,
      multiplicity ≤
        (oneScale.shading.pointMultiplicity point : ENNReal))
    (hmultiplicityUpper : ∀ point ∈ oneScale.shading.union,
      (oneScale.shading.pointMultiplicity point : ENNReal) <
        2 * multiplicity) :
    oneScale.shading.mass ≤ 4 * data.retainedShading.mass := by
  have htwoMultiplicityTop : 2 * multiplicity ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) hmultiplicityTop
  have hsourceUpper : oneScale.shading.mass ≤
      (2 * multiplicity) * volume oneScale.shading.union :=
    Kakeya.Assouad.mass_le_multiplicity_vol htwoMultiplicityTop
      hmultiplicityUpper
  have hretainedLower : multiplicity * volume data.goodRegion ≤
      data.retainedShading.mass := by
    rw [← data.retainedShading_union]
    apply Kakeya.Assouad.multiplicity_floor_le_mass
    intro point hpoint
    have hpointGood : point ∈ data.goodRegion := by
      rw [← data.retainedShading_union]
      exact hpoint
    change multiplicity ≤
      (paperRestrictShadingToSet oneScale.shading data.goodRegion
        data.goodRegion_measurable).pointMultiplicity point
    rw [paperPmRestrictShadingToSet data.goodRegion_measurable hpointGood]
    exact hmultiplicityLower point (data.goodRegion_subset hpointGood)
  calc
    oneScale.shading.mass
        ≤ (2 * multiplicity) * volume oneScale.shading.union := hsourceUpper
    _ ≤ (2 * multiplicity) * (2 * volume data.goodRegion) :=
      mul_le_mul_left' (data.goodRegion_half_volume hsqrtScale)
        (2 * multiplicity)
    _ = 4 * (multiplicity * volume data.goodRegion) := by ring
    _ ≤ 4 * data.retainedShading.mass := mul_le_mul_left' hretainedLower 4

/-- Fine `delta`-cells of the original cubical shading that meet the selected
good region. -/
def retainedFineCells
    (data : Proposition63OneScaleFullGrainCellsData planeMap oneScale
      cells lineVolume coverBudget)
    (hdelta : 0 < delta) : Finset (ℤ × ℤ × ℤ) :=
  (wz1PaperGridIndicesInWindow delta hdelta).filter fun cell =>
    (data.goodRegion ∩ wz1PaperGridCube delta cell).Nonempty

/-- The actual cubical output: retain every original fine cell that meets the
selected good region. -/
def cubicalRetainedShading
    (data : Proposition63OneScaleFullGrainCellsData planeMap oneScale
      cells lineVolume coverBudget)
    (hdelta : 0 < delta) : WZ1PaperTubeShading family :=
  wz2RefinedShading oneScale.shading (data.retainedFineCells hdelta)

theorem cubicalRetainedShading_subshading
    (data : Proposition63OneScaleFullGrainCellsData planeMap oneScale
      cells lineVolume coverBudget)
    (hdelta : 0 < delta) :
    PaperIsSubshading' (data.cubicalRetainedShading hdelta)
      oneScale.shading :=
  wz2RefinedShading_subshading

theorem cubicalRetainedShading_cubical
    (data : Proposition63OneScaleFullGrainCellsData planeMap oneScale
      cells lineVolume coverBudget)
    (hdelta : 0 < delta) :
    WZ1PaperIsCubicalShading (data.cubicalRetainedShading hdelta) :=
  wz2RefinedShading_cubical oneScale.extremal.cubical

theorem goodRegion_subset_cubicalRetained_union
    (data : Proposition63OneScaleFullGrainCellsData planeMap oneScale
      cells lineVolume coverBudget)
    (hdelta : 0 < delta) :
    data.goodRegion ⊆ (data.cubicalRetainedShading hdelta).union := by
  intro point hpoint
  have hpointSource : point ∈ oneScale.shading.union :=
    data.goodRegion_subset hpoint
  have hpointBox : point ∈ Kakeya.Streamlined.axisBox 2 2 2 := by
    rcases hpointSource with ⟨index, hindex⟩
    exact (oneScale.shading.subset_body index hindex).2
  have hwindow : wz1PaperGridIndex delta point ∈
      wz1PaperGridIndicesInWindow delta hdelta :=
    Kakeya.Assouad.paper_point_gridIndex_in_window hdelta hpointBox
  have hpointCell : point ∈
      wz1PaperGridCube delta (wz1PaperGridIndex delta point) := by
    rw [mem_wz1PaperGridCube]
  have hselected : wz1PaperGridIndex delta point ∈
      data.retainedFineCells hdelta := by
    rw [retainedFineCells, Finset.mem_filter]
    exact ⟨hwindow, ⟨point, hpoint, hpointCell⟩⟩
  rw [cubicalRetainedShading, wz2RefinedShading_union_inter]
  refine ⟨hpointSource, ?_⟩
  exact Set.mem_iUnion₂.mpr
    ⟨wz1PaperGridIndex delta point, hselected, hpointCell⟩

theorem retainedShading_mass_le_cubicalRetainedShading_mass
    (data : Proposition63OneScaleFullGrainCellsData planeMap oneScale
      cells lineVolume coverBudget)
    (hdelta : 0 < delta) :
    data.retainedShading.mass ≤
      (data.cubicalRetainedShading hdelta).mass := by
  apply Finset.sum_le_sum
  intro index _
  apply measure_mono
  intro point hpoint
  refine ⟨hpoint.1, ?_⟩
  have hpointHull :=
    data.goodRegion_subset_cubicalRetained_union hdelta hpoint.2
  rw [cubicalRetainedShading, wz2RefinedShading_union_inter] at hpointHull
  exact hpointHull.2

/-- Cubical form of the multiplicity-aware mass ledger.  It keeps the exact
good regions as witnesses but returns a genuine union-of-fine-cells shading
suitable for the next extremality/re-entry step. -/
theorem cubicalRetainedShading_quarter_mass
    (data : Proposition63OneScaleFullGrainCellsData planeMap oneScale
      cells lineVolume coverBudget)
    (hdelta : 0 < delta) (hsqrtScale : 0 < sqrtScale)
    (multiplicity : ENNReal) (hmultiplicityTop : multiplicity ≠ ⊤)
    (hmultiplicityLower : ∀ point ∈ oneScale.shading.union,
      multiplicity ≤
        (oneScale.shading.pointMultiplicity point : ENNReal))
    (hmultiplicityUpper : ∀ point ∈ oneScale.shading.union,
      (oneScale.shading.pointMultiplicity point : ENNReal) <
        2 * multiplicity) :
    oneScale.shading.mass ≤
      4 * (data.cubicalRetainedShading hdelta).mass :=
  (data.retainedShading_quarter_mass hsqrtScale multiplicity
      hmultiplicityTop hmultiplicityLower hmultiplicityUpper).trans
    (mul_le_mul_left'
      (data.retainedShading_mass_le_cubicalRetainedShading_mass hdelta) 4)

end Proposition63OneScaleFullGrainCellsData

end Kakeya.Assouad.PureWZ2

end
