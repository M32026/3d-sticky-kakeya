import MyLeanRepo.Kakeya.Assouad.PropStickyPaperBalancedActiveParentCellsStatements
import MyLeanRepo.Kakeya.Assouad.PureWZ2.PaperShadingMassFinite
import MyLeanRepo.Kakeya.Assouad.PureWZ2.PropSticky
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max

/-!
# Exactification of indexed coarse-cell incidence mass

This finite leaf selects a largest fiber of the actual indexed function
`wz2PaperCellIncidenceMass`.  A cardinality bound on its realized range is an
explicit input: finiteness of the active cell set alone gives no useful
retention cost.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory
open Finset

attribute [local instance] Classical.propDecidable

/-- A nonempty collection of active coarse cells on which the actual indexed
incidence mass is exactly constant.  The final field records the entire cost
of exactification. -/
structure PureWZ2Node05IndexedIncidenceExactificationData
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (fineShading : WZ1PaperTubeShading fine)
    (activeCells : Finset WZ2PaperCellIndex)
    (valueCount : ℕ) where
  retainedCells : Finset WZ2PaperCellIndex
  retainedCells_subset : retainedCells ⊆ activeCells
  retainedCells_nonempty : retainedCells.Nonempty
  incidenceMass : ENNReal
  incidenceMass_pos : 0 < incidenceMass
  incidenceMass_ne_top : incidenceMass ≠ ⊤
  incidenceMass_eq :
    ∀ cell ∈ retainedCells,
      wz2PaperCellIncidenceMass (rho := rho) fineShading cell = incidenceMass
  indexed_mass_retention :
    (∑ cell ∈ activeCells,
        wz2PaperCellIncidenceMass (rho := rho) fineShading cell) ≤
      (valueCount : ENNReal) *
        ∑ cell ∈ retainedCells,
          wz2PaperCellIncidenceMass (rho := rho) fineShading cell

/-- A positive balanced union mass forces positive indexed incidence mass in
each active cell.  This is only the elementary union-versus-sum inequality;
the two masses are not identified. -/
theorem PureWZ2BalancedCoverData.cellIncidenceMass_pos
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {cover : PureWZ2Section6Cover fine coarse}
    (base : PureWZ2BalancedCoverData cover fineShading coarseShading)
    (cell : WZ2PaperCellIndex) (hcell : cell ∈ base.activeCells) :
    0 < wz2PaperCellIncidenceMass (rho := rho) fineShading cell := by
  have hunion :
      fineShading.union ∩ wz1PaperGridCube rho cell =
        ⋃ source : Fin fine.card,
          fineShading.carrier source ∩ wz1PaperGridCube rho cell := by
    ext point
    simp only [Kakeya.Streamlined.Shading.union, Set.mem_inter_iff,
      Set.mem_iUnion]
    constructor
    · rintro ⟨⟨source, hsource⟩, hcellPoint⟩
      exact ⟨source, hsource, hcellPoint⟩
    · rintro ⟨source, hsource, hcellPoint⟩
      exact ⟨⟨source, hsource⟩, hcellPoint⟩
  have hle :
      volume (fineShading.union ∩ wz1PaperGridCube rho cell) ≤
        wz2PaperCellIncidenceMass (rho := rho) fineShading cell := by
    rw [hunion, wz2PaperCellIncidenceMass]
    simpa using MeasureTheory.measure_biUnion_finset_le
      (Finset.univ : Finset (Fin fine.card))
      (fun source =>
        fineShading.carrier source ∩ wz1PaperGridCube rho cell)
  have hpositive :
      0 < volume (fineShading.union ∩ wz1PaperGridCube rho cell) := by
    rw [base.fine_cell_mass cell hcell]
    exact base.cellMass_pos
  exact hpositive.trans_le hle

/-- Indexed incidence in one cell is finite because it is bounded by the
total indexed shading mass. -/
theorem PureWZ2BalancedCoverData.cellIncidenceMass_ne_top
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {cover : PureWZ2Section6Cover fine coarse}
    (_base : PureWZ2BalancedCoverData cover fineShading coarseShading)
    (cell : WZ2PaperCellIndex) :
    wz2PaperCellIncidenceMass (rho := rho) fineShading cell ≠ ⊤ := by
  apply ne_top_of_le_ne_top (wz1PaperTubeShading_mass_ne_top fineShading)
  unfold wz2PaperCellIncidenceMass Kakeya.Streamlined.Shading.mass
  exact Finset.sum_le_sum fun source _ =>
    MeasureTheory.measure_mono Set.inter_subset_left

/-- Finite pigeonholing for the genuine indexed incidence mass.  The caller
must supply a bound on the number of mass values actually realized on the
active set, as well as positivity and finiteness on every active cell.  The
chosen class maximizes total indexed mass, not merely its cardinality. -/
noncomputable def pureWZ2Node05_indexedIncidenceExactification
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (fineShading : WZ1PaperTubeShading fine)
    (activeCells : Finset WZ2PaperCellIndex)
    (valueCount : ℕ)
    (hactive : activeCells.Nonempty)
    (hvalueCount :
      (activeCells.image fun cell =>
        wz2PaperCellIncidenceMass (rho := rho) fineShading cell).card ≤
          valueCount)
    (hmass_pos :
      ∀ cell ∈ activeCells,
        0 < wz2PaperCellIncidenceMass (rho := rho) fineShading cell)
    (hmass_ne_top :
      ∀ cell ∈ activeCells,
        wz2PaperCellIncidenceMass (rho := rho) fineShading cell ≠ ⊤) :
    PureWZ2Node05IndexedIncidenceExactificationData
      (rho := rho) fineShading activeCells valueCount := by
  let mass : WZ2PaperCellIndex → ENNReal := fun cell =>
    wz2PaperCellIncidenceMass (rho := rho) fineShading cell
  let values : Finset ENNReal := activeCells.image mass
  let fiberMass : ENNReal → ENNReal := fun value =>
    ∑ cell ∈ activeCells with mass cell = value, mass cell
  have hvalues_nonempty : values.Nonempty := hactive.image mass
  have hexists := Finset.exists_max_image values
      fiberMass hvalues_nonempty
  let incidenceMass : ENNReal := Classical.choose hexists
  have hincidenceMass_spec := Classical.choose_spec hexists
  have hincidenceMass_mem : incidenceMass ∈ values :=
    hincidenceMass_spec.1
  have hmax :
      ∀ value ∈ values,
        fiberMass value ≤ fiberMass incidenceMass :=
    hincidenceMass_spec.2
  let retainedCells : Finset WZ2PaperCellIndex :=
    activeCells.filter fun cell => mass cell = incidenceMass
  have hrepresentative_exists := Finset.mem_image.mp hincidenceMass_mem
  let representative : WZ2PaperCellIndex :=
    Classical.choose hrepresentative_exists
  have hrepresentative_spec := Classical.choose_spec hrepresentative_exists
  have hrepresentative_active : representative ∈ activeCells :=
    hrepresentative_spec.1
  have hrepresentative_mass : mass representative = incidenceMass :=
    hrepresentative_spec.2
  have hrepresentative_retained : representative ∈ retainedCells := by
    simp only [retainedCells, Finset.mem_filter]
    exact ⟨hrepresentative_active, hrepresentative_mass⟩
  have hmass_sum :
      (∑ cell ∈ activeCells, mass cell) =
        ∑ value ∈ values,
          ∑ cell ∈ activeCells with mass cell = value, mass cell := by
    have hfilter :
        activeCells.filter (fun cell => mass cell ∈ values) = activeCells := by
      ext cell
      simp only [Finset.mem_filter]
      constructor
      · exact fun h => h.1
      · intro hcell
        exact ⟨hcell, Finset.mem_image.mpr ⟨cell, hcell, rfl⟩⟩
    have hfiber :=
      Finset.sum_fiberwise_eq_sum_filter activeCells values mass mass
    rw [hfilter] at hfiber
    exact hfiber.symm
  have hmax_mass_fibers :
      ∀ value ∈ values,
        (∑ cell ∈ activeCells with mass cell = value, mass cell) ≤
          ∑ cell ∈ retainedCells, mass cell := by
    intro value hvalue
    simpa only [fiberMass, retainedCells] using hmax value hvalue
  have hretention_mass_values :
      (∑ cell ∈ activeCells, mass cell) ≤
        (values.card : ENNReal) *
          ∑ cell ∈ retainedCells, mass cell := by
    rw [hmass_sum]
    simpa only [nsmul_eq_mul] using
      Finset.sum_le_card_nsmul values _
        (∑ cell ∈ retainedCells, mass cell) hmax_mass_fibers
  refine {
    retainedCells := retainedCells
    retainedCells_subset := Finset.filter_subset _ _
    retainedCells_nonempty := ⟨representative, hrepresentative_retained⟩
    incidenceMass := incidenceMass
    incidenceMass_pos := ?_
    incidenceMass_ne_top := ?_
    incidenceMass_eq := ?_
    indexed_mass_retention := ?_ }
  · rw [← hrepresentative_mass]
    exact hmass_pos representative hrepresentative_active
  · rw [← hrepresentative_mass]
    exact hmass_ne_top representative hrepresentative_active
  · intro cell hcell
    exact (Finset.mem_filter.mp hcell).2
  · exact hretention_mass_values.trans <| by
      exact mul_le_mul_left (by exact_mod_cast hvalueCount) _

/-- Exactify the active cells of an ordinary balanced cover.  Positivity and
finiteness of the actual indexed mass are consequences of the cover data, so
the only extra quantitative input is the realized-value count. -/
noncomputable def PureWZ2BalancedCoverData.indexedIncidenceExactification
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {cover : PureWZ2Section6Cover fine coarse}
    (base : PureWZ2BalancedCoverData cover fineShading coarseShading)
    (valueCount : ℕ)
    (hactive : base.activeCells.Nonempty)
    (hvalueCount :
      (base.activeCells.image fun cell =>
        wz2PaperCellIncidenceMass (rho := rho) fineShading cell).card ≤
          valueCount) :
    PureWZ2Node05IndexedIncidenceExactificationData
      (rho := rho) fineShading base.activeCells valueCount :=
  pureWZ2Node05_indexedIncidenceExactification
    fineShading base.activeCells valueCount
    hactive
    hvalueCount
    base.cellIncidenceMass_pos
    (fun cell _ => base.cellIncidenceMass_ne_top cell)

end Kakeya.Assouad

end
