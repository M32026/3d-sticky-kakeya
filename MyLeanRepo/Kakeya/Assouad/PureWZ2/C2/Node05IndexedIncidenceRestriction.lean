import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05IndexedIncidenceExactification
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.StickyRefinementData
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.GenericHierarchyAlgorithms

/-!
# Synchronized restriction to exact-incidence coarse cells

The fine and coarse shadings are intersected with the same union of retained
`rho`-cells.  Their families, the Section 6 cover, and hence its parent map
are unchanged.  Indexed incidence mass is never replaced by union volume.
-/

noncomputable section

open MeasureTheory Set

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- The spatial region represented by a finite set of paper grid cells. -/
def pureWZ2Node05RetainedCellRegion
    (rho : ℝ) (cells : Finset WZ2PaperCellIndex) : Set Point3 :=
  ⋃ cell ∈ cells, wz1PaperGridCube rho cell

lemma pureWZ2Node05RetainedCellRegion_measurable
    (rho : ℝ) (cells : Finset WZ2PaperCellIndex) :
    MeasurableSet (pureWZ2Node05RetainedCellRegion rho cells) := by
  exact MeasurableSet.biUnion cells.finite_toSet.countable
    (fun cell _ => wz1PaperGridCube_measurable cell)

/-- Intersect every carrier with one common retained-cell region. -/
def pureWZ2Node05RestrictToCells
    {scale rho : ℝ}
    {family : Kakeya.Streamlined.TubeFamily scale}
    (shading : WZ1PaperTubeShading family)
    (cells : Finset WZ2PaperCellIndex) : WZ1PaperTubeShading family where
  carrier index :=
    shading.carrier index ∩ pureWZ2Node05RetainedCellRegion rho cells
  measurable_carrier index :=
    (shading.measurable_carrier index).inter
      (pureWZ2Node05RetainedCellRegion_measurable rho cells)
  subset_body index := Set.inter_subset_left.trans (shading.subset_body index)

@[simp] lemma pureWZ2Node05RestrictToCells_carrier
    {scale rho : ℝ}
    {family : Kakeya.Streamlined.TubeFamily scale}
    (shading : WZ1PaperTubeShading family)
    (cells : Finset WZ2PaperCellIndex) (index : Fin family.card) :
    (pureWZ2Node05RestrictToCells (rho := rho) shading cells).carrier index =
      shading.carrier index ∩ pureWZ2Node05RetainedCellRegion rho cells := rfl

lemma pureWZ2Node05RestrictToCells_union
    {scale rho : ℝ}
    {family : Kakeya.Streamlined.TubeFamily scale}
    (shading : WZ1PaperTubeShading family)
    (cells : Finset WZ2PaperCellIndex) :
    (pureWZ2Node05RestrictToCells (rho := rho) shading cells).union =
      shading.union ∩ pureWZ2Node05RetainedCellRegion rho cells := by
  ext point
  constructor
  · rintro ⟨index, hsource, hregion⟩
    exact ⟨⟨index, hsource⟩, hregion⟩
  · rintro ⟨⟨index, hsource⟩, hregion⟩
    exact ⟨index, hsource, hregion⟩

lemma wz1PaperGridCube_subset_retainedCellRegion
    {rho : ℝ} {cells : Finset WZ2PaperCellIndex}
    {cell : WZ2PaperCellIndex} (hcell : cell ∈ cells) :
    wz1PaperGridCube rho cell ⊆
      pureWZ2Node05RetainedCellRegion rho cells := by
  intro point hpoint
  exact Set.mem_iUnion₂.mpr ⟨cell, hcell, hpoint⟩

lemma pureWZ2Node05RestrictToCells_inter_gridCube
    {scale rho : ℝ}
    {family : Kakeya.Streamlined.TubeFamily scale}
    (shading : WZ1PaperTubeShading family)
    (cells : Finset WZ2PaperCellIndex)
    {cell : WZ2PaperCellIndex} (hcell : cell ∈ cells)
    (index : Fin family.card) :
    (pureWZ2Node05RestrictToCells (rho := rho) shading cells).carrier index ∩
        wz1PaperGridCube rho cell =
      shading.carrier index ∩ wz1PaperGridCube rho cell := by
  ext point
  simp only [pureWZ2Node05RestrictToCells_carrier, Set.mem_inter_iff]
  constructor
  · exact fun h => ⟨h.1.1, h.2⟩
  · intro h
    exact ⟨⟨h.1, wz1PaperGridCube_subset_retainedCellRegion hcell h.2⟩, h.2⟩

lemma pureWZ2Node05RestrictToCells_constantMultiplicity
    {scale rho : ℝ}
    {family : Kakeya.Streamlined.TubeFamily scale}
    {shading : WZ1PaperTubeShading family}
    {cells : Finset WZ2PaperCellIndex}
    {lower upper : ℕ}
    (hconstant : shading.HasConstantMultiplicity lower upper) :
    (pureWZ2Node05RestrictToCells (rho := rho) shading cells).HasConstantMultiplicity
      lower upper := by
  intro point hpoint
  rw [pureWZ2Node05RestrictToCells_union] at hpoint
  have hpointMultiplicity :
      (pureWZ2Node05RestrictToCells (rho := rho) shading cells).pointMultiplicity
          point = shading.pointMultiplicity point := by
    unfold Kakeya.Streamlined.Shading.pointMultiplicity
    congr 1
    apply Finset.filter_congr
    intro index _
    simp only [pureWZ2Node05RestrictToCells_carrier, Set.mem_inter_iff]
    exact ⟨fun h => h.1, fun h => ⟨h, hpoint.2⟩⟩
  rw [hpointMultiplicity]
  exact hconstant point hpoint.1

/-- Both shadings restricted to the same retained spatial cells, with the
original families and exact Section 6 cover retained definitionally. -/
structure PureWZ2Node05IndexedIncidenceRestrictionData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {cover : PureWZ2Section6Cover fine coarse}
    (base : PureWZ2BalancedCoverData cover fineShading coarseShading)
    (fineCellNested :
      ∀ source point, point ∈ fineShading.carrier source →
        ∃ cell ∈ base.activeCells,
          wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆
            wz1PaperGridCube rho cell)
    {valueCount : ℕ}
    (exactified : PureWZ2Node05IndexedIncidenceExactificationData
      (rho := rho) fineShading base.activeCells valueCount) where
  fineRestricted : WZ1PaperTubeShading fine
  coarseRestricted : WZ1PaperTubeShading coarse
  fineRestricted_eq :
    fineRestricted =
      pureWZ2Node05RestrictToCells (rho := rho) fineShading
        exactified.retainedCells
  coarseRestricted_eq :
    coarseRestricted =
      pureWZ2Node05RestrictToCells (rho := rho) coarseShading
        exactified.retainedCells
  restrictedBase :
    PureWZ2BalancedCoverData cover fineRestricted coarseRestricted
  restrictedBase_activeCells :
    restrictedBase.activeCells = exactified.retainedCells
  restrictedBalanced : PureWZ2Node5BalancedCoverData restrictedBase
  restrictedBalanced_incidenceMass :
    restrictedBalanced.incidenceMass = exactified.incidenceMass
  indexed_mass_retention :
    (∑ cell ∈ base.activeCells,
        wz2PaperCellIncidenceMass (rho := rho) fineShading cell) ≤
      (valueCount : ENNReal) *
        ∑ cell ∈ restrictedBase.activeCells,
          wz2PaperCellIncidenceMass
            (rho := rho) fineRestricted cell

/-- Perform the synchronized whole-cell spatial restriction. -/
noncomputable def pureWZ2Node05_indexedIncidenceRestriction
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {cover : PureWZ2Section6Cover fine coarse}
    (base : PureWZ2BalancedCoverData cover fineShading coarseShading)
    (fineCellNested :
      ∀ source point, point ∈ fineShading.carrier source →
        ∃ cell ∈ base.activeCells,
          wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆
            wz1PaperGridCube rho cell)
    {valueCount : ℕ}
    (exactified : PureWZ2Node05IndexedIncidenceExactificationData
      (rho := rho) fineShading base.activeCells valueCount) :
    PureWZ2Node05IndexedIncidenceRestrictionData
      base fineCellNested exactified := by
  let cells := exactified.retainedCells
  let fineRestricted :=
    pureWZ2Node05RestrictToCells (rho := rho) fineShading cells
  let coarseRestricted :=
    pureWZ2Node05RestrictToCells (rho := rho) coarseShading cells
  have hcoarseUnion :
      coarseRestricted.union = pureWZ2Node05RetainedCellRegion rho cells := by
    rw [pureWZ2Node05RestrictToCells_union]
    apply Set.inter_eq_right.mpr
    intro point hpoint
    rcases Set.mem_iUnion₂.mp hpoint with ⟨cell, hcell, hpointCell⟩
    rw [base.coarse_union_eq]
    exact Set.mem_iUnion₂.mpr
      ⟨cell, exactified.retainedCells_subset hcell, hpointCell⟩
  have hcoarseCubical : WZ1PaperIsCubicalShading coarseRestricted := by
    intro index point hpoint other hother
    have hsourceOther := base.coarse_cubical index point hpoint.1 hother
    rcases Set.mem_iUnion₂.mp hpoint.2 with ⟨cell, hcell, hpointCell⟩
    have hindex : wz1PaperGridIndex rho point = cell :=
      (mem_wz1PaperGridCube rho cell point).mp hpointCell
    have hotherCell : other ∈ wz1PaperGridCube rho cell :=
      (mem_wz1PaperGridCube rho cell other).mpr <| by
        simpa [hindex] using hother
    exact ⟨hsourceOther, Set.mem_iUnion₂.mpr ⟨cell, hcell, hotherCell⟩⟩
  have hpointCompatibility :
      ∀ source parent,
        WZ1PaperTubeCovers (fine.tube source) (coarse.tube parent) →
          ∀ point, point ∈ fineRestricted.carrier source →
            point ∈ coarseRestricted.carrier parent := by
    intro source parent hcovers point hpoint
    exact ⟨base.point_compatibility source parent hcovers point hpoint.1, hpoint.2⟩
  have hfineUnionInter :
      ∀ cell ∈ cells,
        fineRestricted.union ∩ wz1PaperGridCube rho cell =
          fineShading.union ∩ wz1PaperGridCube rho cell := by
    intro cell hcell
    rw [pureWZ2Node05RestrictToCells_union]
    ext point
    simp only [Set.mem_inter_iff]
    constructor
    · exact fun h => ⟨h.1.1, h.2⟩
    · intro h
      exact ⟨⟨h.1, wz1PaperGridCube_subset_retainedCellRegion hcell h.2⟩, h.2⟩
  let restrictedBase :
      PureWZ2BalancedCoverData cover fineRestricted coarseRestricted := {
    point_compatibility := hpointCompatibility
    coarse_cubical := hcoarseCubical
    activeCells := cells
    coarse_union_eq := hcoarseUnion
    cellMass := base.cellMass
    cellMass_pos := base.cellMass_pos
    cellMass_ne_top := base.cellMass_ne_top
    fine_cell_mass := by
      intro cell hcell
      rw [hfineUnionInter cell hcell]
      exact base.fine_cell_mass cell
        (exactified.retainedCells_subset hcell) }
  have hindexed :
      ∀ cell ∈ cells,
        wz2PaperCellIncidenceMass (rho := rho) fineRestricted cell =
          exactified.incidenceMass := by
    intro cell hcell
    unfold wz2PaperCellIncidenceMass
    rw [Finset.sum_congr rfl]
    · exact exactified.incidenceMass_eq cell hcell
    · intro source _
      rw [pureWZ2Node05RestrictToCells_inter_gridCube
        fineShading cells hcell source]
  have hnested :
      ∀ source point, point ∈ fineRestricted.carrier source →
        ∃ cell ∈ restrictedBase.activeCells,
          wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆
            wz1PaperGridCube rho cell := by
    intro source point hpoint
    rcases Set.mem_iUnion₂.mp hpoint.2 with
      ⟨retainedCell, hretainedCell, hpointRetained⟩
    rcases fineCellNested source point hpoint.1 with
      ⟨oldCell, holdCell, hnestedOld⟩
    have hpointFine :
        point ∈ wz1PaperGridCube delta (wz1PaperGridIndex delta point) :=
      (mem_wz1PaperGridCube delta _ point).mpr rfl
    have hpointOld := hnestedOld hpointFine
    have heq : oldCell = retainedCell :=
      ((mem_wz1PaperGridCube rho oldCell point).mp hpointOld).symm.trans
        ((mem_wz1PaperGridCube rho retainedCell point).mp hpointRetained)
    exact ⟨retainedCell, hretainedCell, by simpa only [heq] using hnestedOld⟩
  let restrictedBalanced : PureWZ2Node5BalancedCoverData restrictedBase := {
    incidenceMass := exactified.incidenceMass
    incidenceMass_pos := exactified.incidenceMass_pos
    incidenceMass_ne_top := exactified.incidenceMass_ne_top
    fine_cell_incidence_mass := hindexed
    fine_cell_nested := hnested }
  refine {
    fineRestricted := fineRestricted
    coarseRestricted := coarseRestricted
    fineRestricted_eq := rfl
    coarseRestricted_eq := rfl
    restrictedBase := restrictedBase
    restrictedBase_activeCells := rfl
    restrictedBalanced := restrictedBalanced
    restrictedBalanced_incidenceMass := rfl
    indexed_mass_retention := ?_ }
  rw [show restrictedBase.activeCells = cells from rfl]
  have hrestrictedSum :
      (∑ cell ∈ cells,
          wz2PaperCellIncidenceMass (rho := rho) fineRestricted cell) =
        ∑ cell ∈ cells,
          wz2PaperCellIncidenceMass (rho := rho) fineShading cell := by
    apply Finset.sum_congr rfl
    intro cell hcell
    unfold wz2PaperCellIncidenceMass
    apply Finset.sum_congr rfl
    intro source _
    rw [pureWZ2Node05RestrictToCells_inter_gridCube
      fineShading cells hcell source]
  rw [hrestrictedSum]
  exact exactified.indexed_mass_retention

end Kakeya.Assouad

end
