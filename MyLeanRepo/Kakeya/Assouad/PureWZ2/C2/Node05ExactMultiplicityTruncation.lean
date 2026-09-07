import MyLeanRepo.Kakeya.Assouad.PropStickyExactCellBalancingHelpers
import MyLeanRepo.Kakeya.Assouad.PropStickyBoundaryCellPruningGeometry
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalFineExactBalancingHelpers
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperRelativeMultiplicityHelpers
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperMultiplicityFloorVolume
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05IndexedIncidenceExactification
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.StickyRefinementData

/-!
# Exact multiplicity truncation on literal fine cells

For every active literal `delta`-cell, choose exactly `m` of the genuine
sources whose old cubical carrier contains that entire cell.  The resulting
shading keeps the original family and assigns to each source the finite union
of the whole cells on which that source was chosen.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Finset

attribute [local instance] Classical.propDecidable

/-- The genuine source fiber over a literal fine cell. -/
def pureWZ2Node05CellSourceFiber
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (Y : WZ1PaperTubeShading fine)
    (cell : WZ2PaperCellIndex) : Finset (Fin fine.card) :=
  Finset.univ.filter fun source =>
    wz1PaperGridCube delta cell ⊆ Y.carrier source

lemma pureWZ2Node05CellSourceFiber_eq_pointMultiplicity
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {Y : WZ1PaperTubeShading fine}
    (hcubical : WZ1PaperIsCubicalShading Y)
    {cell : WZ2PaperCellIndex} {point : Point3}
    (hpoint : point ∈ wz1PaperGridCube delta cell) :
    (pureWZ2Node05CellSourceFiber Y cell).card =
      Y.pointMultiplicity point := by
  unfold pureWZ2Node05CellSourceFiber
    Kakeya.Streamlined.Shading.pointMultiplicity
  congr 1
  apply Finset.filter_congr
  intro source _
  constructor
  · exact fun hsource => hsource hpoint
  · intro hsource
    have hindex : wz1PaperGridIndex delta point = cell :=
      (mem_wz1PaperGridCube delta cell point).mp hpoint
    simpa only [hindex] using hcubical source point hsource

lemma pureWZ2Node05CellSourceFiber_card_lower
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {Y : WZ1PaperTubeShading fine}
    {m : ℕ}
    (hdelta : 0 < delta)
    (hcubical : WZ1PaperIsCubicalShading Y)
    (hconstant : Y.HasConstantMultiplicity m (2 * m))
    {cell : WZ2PaperCellIndex}
    (hcell : cell ∈ wz1PaperActiveCells Y hdelta) :
    m ≤ (pureWZ2Node05CellSourceFiber Y cell).card := by
  rcases ((mem_wz1PaperActiveCells Y hdelta cell).mp hcell).2 with
    ⟨point, hpointUnion, hpointCell⟩
  rw [pureWZ2Node05CellSourceFiber_eq_pointMultiplicity
    hcubical hpointCell]
  exact (hconstant point hpointUnion).1

/-- Reassemble a same-family shading from a cellwise source selection. -/
def pureWZ2Node05SelectedCellShading
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (Y : WZ1PaperTubeShading fine)
    (hdelta : 0 < delta)
    (selectedSources : WZ2PaperCellIndex → Finset (Fin fine.card))
    (hselected_subset :
      ∀ cell, cell ∈ wz1PaperActiveCells Y hdelta →
        selectedSources cell ⊆
          pureWZ2Node05CellSourceFiber Y cell) :
    WZ1PaperTubeShading fine where
  carrier source :=
    wz2RetainedCellsUnion delta <|
      (wz1PaperActiveCells Y hdelta).filter fun cell =>
        source ∈ selectedSources cell
  measurable_carrier source := wz2RetainedCellsUnion_measurable
  subset_body source := by
    intro point hpoint
    rcases Set.mem_iUnion₂.mp hpoint with ⟨cell, hcell, hpointCell⟩
    have hactive : cell ∈ wz1PaperActiveCells Y hdelta :=
      (Finset.mem_filter.mp hcell).1
    have hselected : source ∈ selectedSources cell :=
      (Finset.mem_filter.mp hcell).2
    have hsourceMem :
        source ∈ pureWZ2Node05CellSourceFiber Y cell :=
      hselected_subset cell hactive hselected
    have hsource :
        wz1PaperGridCube delta cell ⊆ Y.carrier source := by
      exact (Finset.mem_filter.mp hsourceMem).2
    exact Y.subset_body source (hsource hpointCell)

lemma mem_pureWZ2Node05SelectedCellShading_carrier
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (Y : WZ1PaperTubeShading fine)
    (hdelta : 0 < delta)
    (selectedSources : WZ2PaperCellIndex → Finset (Fin fine.card))
    (hselected_subset :
      ∀ cell, cell ∈ wz1PaperActiveCells Y hdelta →
        selectedSources cell ⊆ pureWZ2Node05CellSourceFiber Y cell)
    (source : Fin fine.card) (point : Point3) :
    point ∈ (pureWZ2Node05SelectedCellShading
        Y hdelta selectedSources hselected_subset).carrier source ↔
      wz1PaperGridIndex delta point ∈ wz1PaperActiveCells Y hdelta ∧
        source ∈ selectedSources (wz1PaperGridIndex delta point) := by
  constructor
  · intro hpoint
    rcases Set.mem_iUnion₂.mp hpoint with ⟨cell, hcell, hpointCell⟩
    have hindex : wz1PaperGridIndex delta point = cell :=
      (mem_wz1PaperGridCube delta cell point).mp hpointCell
    rw [hindex]
    exact Finset.mem_filter.mp hcell
  · rintro ⟨hactive, hselected⟩
    exact Set.mem_iUnion₂.mpr
      ⟨wz1PaperGridIndex delta point,
        Finset.mem_filter.mpr ⟨hactive, hselected⟩,
        (mem_wz1PaperGridCube delta
          (wz1PaperGridIndex delta point) point).mpr rfl⟩

lemma pureWZ2Node05SelectedCellShading_subshading
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (Y : WZ1PaperTubeShading fine)
    (hdelta : 0 < delta)
    (selectedSources : WZ2PaperCellIndex → Finset (Fin fine.card))
    (hselected_subset :
      ∀ cell, cell ∈ wz1PaperActiveCells Y hdelta →
        selectedSources cell ⊆ pureWZ2Node05CellSourceFiber Y cell) :
    ∀ source,
      (pureWZ2Node05SelectedCellShading
        Y hdelta selectedSources hselected_subset).carrier source ⊆
          Y.carrier source := by
  intro source point hpoint
  have hmem := (mem_pureWZ2Node05SelectedCellShading_carrier
    Y hdelta selectedSources hselected_subset source point).mp hpoint
  have hsourceFiber := hselected_subset _ hmem.1 hmem.2
  have hcellSubset := (Finset.mem_filter.mp hsourceFiber).2
  exact hcellSubset <|
    (mem_wz1PaperGridCube delta
      (wz1PaperGridIndex delta point) point).mpr rfl

lemma pureWZ2Node05SelectedCellShading_cubical
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (Y : WZ1PaperTubeShading fine)
    (hdelta : 0 < delta)
    (selectedSources : WZ2PaperCellIndex → Finset (Fin fine.card))
    (hselected_subset :
      ∀ cell, cell ∈ wz1PaperActiveCells Y hdelta →
        selectedSources cell ⊆ pureWZ2Node05CellSourceFiber Y cell) :
    WZ1PaperIsCubicalShading
      (pureWZ2Node05SelectedCellShading
        Y hdelta selectedSources hselected_subset) := by
  intro source point hpoint other hother
  have hmem := (mem_pureWZ2Node05SelectedCellShading_carrier
    Y hdelta selectedSources hselected_subset source point).mp hpoint
  have hindex : wz1PaperGridIndex delta other =
      wz1PaperGridIndex delta point :=
    (mem_wz1PaperGridCube delta
      (wz1PaperGridIndex delta point) other).mp hother
  apply (mem_pureWZ2Node05SelectedCellShading_carrier
    Y hdelta selectedSources hselected_subset source other).mpr
  simpa only [hindex] using hmem

lemma wz1PaperGridIndex_mem_activeCells_of_mem_union
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {Y : WZ1PaperTubeShading fine}
    (hdelta : 0 < delta) {point : Point3}
    (hpoint : point ∈ Y.union) :
    wz1PaperGridIndex delta point ∈ wz1PaperActiveCells Y hdelta := by
  rw [mem_wz1PaperActiveCells]
  refine ⟨?_, ⟨point, hpoint, ?_⟩⟩
  · exact paper_point_gridIndex_in_window hdelta
      (shading_union_subset_axisBox hpoint)
  · exact (mem_wz1PaperGridCube delta
      (wz1PaperGridIndex delta point) point).mpr rfl

lemma pureWZ2Node05SelectedCellShading_union_eq
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (Y : WZ1PaperTubeShading fine)
    (hdelta : 0 < delta)
    (selectedSources : WZ2PaperCellIndex → Finset (Fin fine.card))
    (hselected_subset :
      ∀ cell, cell ∈ wz1PaperActiveCells Y hdelta →
        selectedSources cell ⊆ pureWZ2Node05CellSourceFiber Y cell)
    (hselected_nonempty :
      ∀ cell, cell ∈ wz1PaperActiveCells Y hdelta →
        (selectedSources cell).Nonempty) :
    (pureWZ2Node05SelectedCellShading
        Y hdelta selectedSources hselected_subset).union = Y.union := by
  apply Set.Subset.antisymm
  · rintro point ⟨source, hpoint⟩
    exact ⟨source, pureWZ2Node05SelectedCellShading_subshading
      Y hdelta selectedSources hselected_subset source hpoint⟩
  · intro point hpoint
    have hactive := wz1PaperGridIndex_mem_activeCells_of_mem_union
      hdelta hpoint
    rcases hselected_nonempty _ hactive with ⟨source, hsource⟩
    exact ⟨source,
      (mem_pureWZ2Node05SelectedCellShading_carrier
        Y hdelta selectedSources hselected_subset source point).mpr
          ⟨hactive, hsource⟩⟩

lemma pureWZ2Node05SelectedCellShading_pointMultiplicity
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (Y : WZ1PaperTubeShading fine)
    (hdelta : 0 < delta)
    (selectedSources : WZ2PaperCellIndex → Finset (Fin fine.card))
    (hselected_subset :
      ∀ cell, cell ∈ wz1PaperActiveCells Y hdelta →
        selectedSources cell ⊆ pureWZ2Node05CellSourceFiber Y cell)
    {point : Point3}
    (hactive :
      wz1PaperGridIndex delta point ∈ wz1PaperActiveCells Y hdelta) :
    (pureWZ2Node05SelectedCellShading
        Y hdelta selectedSources hselected_subset).pointMultiplicity point =
      (selectedSources (wz1PaperGridIndex delta point)).card := by
  unfold Kakeya.Streamlined.Shading.pointMultiplicity
  congr 1
  ext source
  rw [Finset.mem_filter,
    mem_pureWZ2Node05SelectedCellShading_carrier]
  simp only [Finset.mem_univ, true_and, hactive]
  rfl

lemma pureWZ2Node05SelectedCellShading_constantMultiplicity
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (Y : WZ1PaperTubeShading fine)
    (hdelta : 0 < delta)
    (selectedSources : WZ2PaperCellIndex → Finset (Fin fine.card))
    (hselected_subset :
      ∀ cell, cell ∈ wz1PaperActiveCells Y hdelta →
        selectedSources cell ⊆ pureWZ2Node05CellSourceFiber Y cell)
    {m : ℕ}
    (hselected_card :
      ∀ cell, cell ∈ wz1PaperActiveCells Y hdelta →
        (selectedSources cell).card = m) :
    (pureWZ2Node05SelectedCellShading
        Y hdelta selectedSources hselected_subset).HasConstantMultiplicity m m := by
  intro point hpoint
  have hpointY : point ∈ Y.union := by
    rcases hpoint with ⟨source, hsource⟩
    exact ⟨source, pureWZ2Node05SelectedCellShading_subshading
      Y hdelta selectedSources hselected_subset source hsource⟩
  have hactive := wz1PaperGridIndex_mem_activeCells_of_mem_union
    hdelta hpointY
  rw [pureWZ2Node05SelectedCellShading_pointMultiplicity
    Y hdelta selectedSources hselected_subset hactive,
    hselected_card _ hactive]
  exact ⟨le_rfl, le_rfl⟩

/-- Exact cellwise source truncation, with its same-family geometric and mass
certificates. -/
structure PureWZ2Node05ExactMultiplicityTruncationData
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (Y : WZ1PaperTubeShading fine)
    (hdelta : 0 < delta)
    (m : ℕ) where
  selectedSources : WZ2PaperCellIndex → Finset (Fin fine.card)
  selectedSources_subset :
    ∀ cell, cell ∈ wz1PaperActiveCells Y hdelta →
      selectedSources cell ⊆ pureWZ2Node05CellSourceFiber Y cell
  selectedSources_card :
    ∀ cell, cell ∈ wz1PaperActiveCells Y hdelta →
      (selectedSources cell).card = m
  truncated : WZ1PaperTubeShading fine
  truncated_eq :
    truncated = pureWZ2Node05SelectedCellShading
      Y hdelta selectedSources selectedSources_subset
  subshading : ∀ source, truncated.carrier source ⊆ Y.carrier source
  cubical : WZ1PaperIsCubicalShading truncated
  union_eq : truncated.union = Y.union
  exact_multiplicity : truncated.HasConstantMultiplicity m m
  pointMultiplicity_eq : ∀ point ∈ truncated.union,
    truncated.pointMultiplicity point = m
  mass_retention : Y.mass ≤ 2 * truncated.mass

/-- Exact literal-cell truncation from a pointwise lower multiplicity floor.
Unlike `PureWZ2Node05ExactMultiplicityTruncationData`, this core does not
build in a factor-two upper bound for the source shading.  It is therefore
the appropriate same-witness interface for a rich Proposition-6.2 output,
whose upper band is controlled by its terminal regularity. -/
structure PureWZ2Node05LowerFloorExactTruncationData
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (Y : WZ1PaperTubeShading fine)
    (hdelta : 0 < delta)
    (m : ℕ) where
  selectedSources : WZ2PaperCellIndex → Finset (Fin fine.card)
  selectedSources_subset :
    ∀ cell, cell ∈ wz1PaperActiveCells Y hdelta →
      selectedSources cell ⊆ pureWZ2Node05CellSourceFiber Y cell
  selectedSources_card :
    ∀ cell, cell ∈ wz1PaperActiveCells Y hdelta →
      (selectedSources cell).card = m
  truncated : WZ1PaperTubeShading fine
  truncated_eq :
    truncated = pureWZ2Node05SelectedCellShading
      Y hdelta selectedSources selectedSources_subset
  subshading : ∀ source, truncated.carrier source ⊆ Y.carrier source
  cubical : WZ1PaperIsCubicalShading truncated
  union_eq : truncated.union = Y.union
  exact_multiplicity : truncated.HasConstantMultiplicity m m

/-- Choose exactly the prescribed lower-floor number of genuine sources on
each active literal cell. -/
noncomputable def pureWZ2Node05_lowerFloorExactTruncation
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (Y : WZ1PaperTubeShading fine)
    (hdelta : 0 < delta)
    (hcubical : WZ1PaperIsCubicalShading Y)
    (m : ℕ) (hm : 0 < m)
    (hlower : ∀ point ∈ Y.union, m ≤ Y.pointMultiplicity point) :
    PureWZ2Node05LowerFloorExactTruncationData Y hdelta m := by
  have hexists : ∀ cell, cell ∈ wz1PaperActiveCells Y hdelta →
      ∃ selected : Finset (Fin fine.card),
        selected ⊆ pureWZ2Node05CellSourceFiber Y cell ∧
          selected.card = m := by
    intro cell hcell
    rcases ((mem_wz1PaperActiveCells Y hdelta cell).mp hcell).2 with
      ⟨point, hpointUnion, hpointCell⟩
    apply Finset.exists_subset_card_eq
    rw [pureWZ2Node05CellSourceFiber_eq_pointMultiplicity
      hcubical hpointCell]
    exact hlower point hpointUnion
  choose activeSelection hactiveSubset hactiveCard using hexists
  let selectedSources : WZ2PaperCellIndex → Finset (Fin fine.card) :=
    fun cell => if hcell : cell ∈ wz1PaperActiveCells Y hdelta then
      activeSelection cell hcell else ∅
  have hsubset : ∀ cell, cell ∈ wz1PaperActiveCells Y hdelta →
      selectedSources cell ⊆ pureWZ2Node05CellSourceFiber Y cell := by
    intro cell hcell
    simpa only [selectedSources, dif_pos hcell] using
      hactiveSubset cell hcell
  have hcard : ∀ cell, cell ∈ wz1PaperActiveCells Y hdelta →
      (selectedSources cell).card = m := by
    intro cell hcell
    simpa only [selectedSources, dif_pos hcell] using
      hactiveCard cell hcell
  let truncated := pureWZ2Node05SelectedCellShading
    Y hdelta selectedSources hsubset
  have hnonempty : ∀ cell, cell ∈ wz1PaperActiveCells Y hdelta →
      (selectedSources cell).Nonempty := by
    intro cell hcell
    rw [← Finset.card_pos, hcard cell hcell]
    exact hm
  exact {
    selectedSources := selectedSources
    selectedSources_subset := hsubset
    selectedSources_card := hcard
    truncated := truncated
    truncated_eq := rfl
    subshading := pureWZ2Node05SelectedCellShading_subshading
      Y hdelta selectedSources hsubset
    cubical := pureWZ2Node05SelectedCellShading_cubical
      Y hdelta selectedSources hsubset
    union_eq := pureWZ2Node05SelectedCellShading_union_eq
      Y hdelta selectedSources hsubset hnonempty
    exact_multiplicity :=
      pureWZ2Node05SelectedCellShading_constantMultiplicity
        Y hdelta selectedSources hsubset hcard }

/-- A lower-floor exact truncation loses at most the supplied pointwise upper
factor.  Both sides are indexed masses on the same literal family. -/
theorem PureWZ2Node05LowerFloorExactTruncationData.mass_retention_of_upper
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {Y : WZ1PaperTubeShading fine}
    {hdelta : 0 < delta} {m : ℕ}
    (truncation : PureWZ2Node05LowerFloorExactTruncationData Y hdelta m)
    (regularity : ℕ)
    (hupper : ∀ point, Y.pointMultiplicity point ≤ regularity * m) :
    Y.mass ≤ (regularity : ENNReal) * truncation.truncated.mass := by
  have hsource : Y.mass ≤
      ((regularity : ENNReal) * (m : ENNReal)) * volume Y.union := by
    apply mass_le_of_pointMultiplicity_le
    intro point _
    exact_mod_cast hupper point
  have htarget : (m : ENNReal) * volume truncation.truncated.union ≤
      truncation.truncated.mass := by
    exact (constant_multiplicity_mass_volume_generic <| by
      intro point hpoint
      have hexact := truncation.exact_multiplicity point hpoint
      exact ⟨hexact.1, hexact.2.trans (by omega)⟩).1
  calc
    Y.mass ≤ ((regularity : ENNReal) * (m : ENNReal)) *
        volume Y.union := hsource
    _ = (regularity : ENNReal) *
        ((m : ENNReal) * volume truncation.truncated.union) := by
      rw [truncation.union_eq]
      ring
    _ ≤ (regularity : ENNReal) * truncation.truncated.mass := by gcongr

/-- Preserve a balanced cover after a lower-floor exact truncation. -/
noncomputable def
    PureWZ2Node05LowerFloorExactTruncationData.toBalancedBase
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {Y : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {cover : PureWZ2Section6Cover fine coarse}
    {hdelta : 0 < delta} {m : ℕ}
    (truncation : PureWZ2Node05LowerFloorExactTruncationData Y hdelta m)
    (base : PureWZ2BalancedCoverData cover Y coarseShading) :
    PureWZ2BalancedCoverData cover truncation.truncated coarseShading where
  point_compatibility := by
    intro source parent hcovers point hpoint
    exact base.point_compatibility source parent hcovers point
      (truncation.subshading source hpoint)
  coarse_cubical := base.coarse_cubical
  activeCells := base.activeCells
  coarse_union_eq := base.coarse_union_eq
  cellMass := base.cellMass
  cellMass_pos := base.cellMass_pos
  cellMass_ne_top := base.cellMass_ne_top
  fine_cell_mass := by
    intro cell hcell
    rw [truncation.union_eq]
    exact base.fine_cell_mass cell hcell

/-- Upgrade the preserved balanced cover with its exact indexed incidence
mass and literal-cell nesting. -/
noncomputable def
    PureWZ2Node05LowerFloorExactTruncationData.toNode5Balanced
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {Y : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {cover : PureWZ2Section6Cover fine coarse}
    {hdelta : 0 < delta} {m : ℕ}
    (truncation : PureWZ2Node05LowerFloorExactTruncationData Y hdelta m)
    (base : PureWZ2BalancedCoverData cover Y coarseShading)
    (hm : 0 < m)
    (fineCellNested :
      ∀ source point, point ∈ Y.carrier source →
        ∃ cell ∈ base.activeCells,
          wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆
            wz1PaperGridCube rho cell) :
    let truncatedBase := truncation.toBalancedBase base
    PureWZ2Node5BalancedCoverData truncatedBase := by
  let truncatedBase := truncation.toBalancedBase base
  exact {
    incidenceMass := (m : ENNReal) * base.cellMass
    incidenceMass_pos :=
      ENNReal.mul_pos (by simp [Nat.ne_of_gt hm]) base.cellMass_pos.ne'
    incidenceMass_ne_top :=
      ENNReal.mul_ne_top (by simp) base.cellMass_ne_top
    fine_cell_incidence_mass := by
      intro cell hcell
      have hFubini :=
        sum_volume_inter_eq_setLIntegral_pointMultiplicity
          truncation.truncated
            (S := wz1PaperGridCube rho cell)
            (wz1PaperGridCube_measurable cell)
      change (∑ source : Fin (wz1PaperBodyFamily fine).card,
          volume (truncation.truncated.carrier source ∩
            wz1PaperGridCube rho cell)) = (m : ENNReal) * base.cellMass
      rw [hFubini]
      have hpointwise : ∀ point ∈ wz1PaperGridCube rho cell,
          (truncation.truncated.pointMultiplicity point : ENNReal) =
            (truncation.truncated.union).indicator
              (fun _ : Point3 => (m : ENNReal)) point := by
        intro point _
        by_cases hpointUnion : point ∈ truncation.truncated.union
        · simp only [Set.indicator_of_mem hpointUnion]
          exact_mod_cast (le_antisymm
            (truncation.exact_multiplicity point hpointUnion).2
            (truncation.exact_multiplicity point hpointUnion).1)
        · simp only [Set.indicator_apply, hpointUnion, ↓reduceIte]
          have hnone : ∀ source : Fin fine.card,
              point ∉ truncation.truncated.carrier source := by
            intro source hsource
            exact hpointUnion ⟨source, hsource⟩
          simp [Kakeya.Streamlined.Shading.pointMultiplicity, hnone]
      calc
        (∫⁻ point in wz1PaperGridCube rho cell,
            (truncation.truncated.pointMultiplicity point : ENNReal)) =
            ∫⁻ point in wz1PaperGridCube rho cell,
              (truncation.truncated.union).indicator
                (fun _ : Point3 => (m : ENNReal)) point := by
              apply MeasureTheory.setLIntegral_congr_fun
                (wz1PaperGridCube_measurable cell)
              exact hpointwise
        _ = ∫⁻ point in
              truncation.truncated.union ∩ wz1PaperGridCube rho cell,
                (m : ENNReal) := by
              rw [MeasureTheory.setLIntegral_indicator
                (measurableSet_shading_union truncation.truncated)]
        _ = (m : ENNReal) * volume
              (truncation.truncated.union ∩ wz1PaperGridCube rho cell) := by
              rw [MeasureTheory.setLIntegral_const]
        _ = (m : ENNReal) * base.cellMass := by
              rw [truncation.union_eq, base.fine_cell_mass cell hcell]
    fine_cell_nested := by
      intro source point hpoint
      exact fineCellNested source point (truncation.subshading source hpoint) }

/-- Choose exactly `m` genuine sources independently on every active literal
fine cell and reassemble their whole-cell carriers. -/
noncomputable def pureWZ2Node05_exactMultiplicityTruncation
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (Y : WZ1PaperTubeShading fine)
    (hdelta : 0 < delta)
    (hcubical : WZ1PaperIsCubicalShading Y)
    (m : ℕ) (hm : 0 < m)
    (hconstant : Y.HasConstantMultiplicity m (2 * m)) :
    PureWZ2Node05ExactMultiplicityTruncationData Y hdelta m := by
  have hexists : ∀ cell, cell ∈ wz1PaperActiveCells Y hdelta →
      ∃ selected : Finset (Fin fine.card),
        selected ⊆ pureWZ2Node05CellSourceFiber Y cell ∧
          selected.card = m := by
    intro cell hcell
    exact Finset.exists_subset_card_eq
      (pureWZ2Node05CellSourceFiber_card_lower
        hdelta hcubical hconstant hcell)
  choose activeSelection hactiveSubset hactiveCard using hexists
  let selectedSources : WZ2PaperCellIndex → Finset (Fin fine.card) :=
    fun cell => if hcell : cell ∈ wz1PaperActiveCells Y hdelta then
      activeSelection cell hcell else ∅
  have hsubset : ∀ cell, cell ∈ wz1PaperActiveCells Y hdelta →
      selectedSources cell ⊆ pureWZ2Node05CellSourceFiber Y cell := by
    intro cell hcell
    simpa only [selectedSources, dif_pos hcell] using
      hactiveSubset cell hcell
  have hcard : ∀ cell, cell ∈ wz1PaperActiveCells Y hdelta →
      (selectedSources cell).card = m := by
    intro cell hcell
    simpa only [selectedSources, dif_pos hcell] using
      hactiveCard cell hcell
  let truncated := pureWZ2Node05SelectedCellShading
    Y hdelta selectedSources hsubset
  have hsub : ∀ source, truncated.carrier source ⊆ Y.carrier source :=
    pureWZ2Node05SelectedCellShading_subshading
      Y hdelta selectedSources hsubset
  have hcub : WZ1PaperIsCubicalShading truncated :=
    pureWZ2Node05SelectedCellShading_cubical
      Y hdelta selectedSources hsubset
  have hnonempty : ∀ cell, cell ∈ wz1PaperActiveCells Y hdelta →
      (selectedSources cell).Nonempty := by
    intro cell hcell
    rw [← Finset.card_pos, hcard cell hcell]
    exact hm
  have hunion : truncated.union = Y.union :=
    pureWZ2Node05SelectedCellShading_union_eq
      Y hdelta selectedSources hsubset hnonempty
  have hexact : truncated.HasConstantMultiplicity m m :=
    pureWZ2Node05SelectedCellShading_constantMultiplicity
      Y hdelta selectedSources hsubset hcard
  have hband : truncated.HasConstantMultiplicity m (2 * m) := by
    intro point hpoint
    have h := hexact point hpoint
    exact ⟨h.1, h.2.trans (by omega)⟩
  have hmass : Y.mass ≤ 2 * truncated.mass := by
    have hle := constant_multiplicity_mass_le_of_union_volume_le
      hconstant hband 1 (by simp [hunion])
    simpa using hle
  exact {
    selectedSources := selectedSources
    selectedSources_subset := hsubset
    selectedSources_card := hcard
    truncated := truncated
    truncated_eq := rfl
    subshading := hsub
    cubical := hcub
    union_eq := hunion
    exact_multiplicity := hexact
    pointMultiplicity_eq := fun point hpoint =>
      le_antisymm (hexact point hpoint).2 (hexact point hpoint).1
    mass_retention := hmass }

/-- The original balanced cover is preserved verbatim after truncation: no
coarse cell is deleted, and the fine union mass in each active cell is
unchanged. -/
noncomputable def PureWZ2Node05ExactMultiplicityTruncationData.toBalancedBase
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {Y : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {cover : PureWZ2Section6Cover fine coarse}
    {hdelta : 0 < delta} {m : ℕ}
    (truncation : PureWZ2Node05ExactMultiplicityTruncationData Y hdelta m)
    (base : PureWZ2BalancedCoverData cover Y coarseShading) :
    PureWZ2BalancedCoverData cover truncation.truncated coarseShading where
  point_compatibility := by
    intro source parent hcovers point hpoint
    exact base.point_compatibility source parent hcovers point
      (truncation.subshading source hpoint)
  coarse_cubical := base.coarse_cubical
  activeCells := base.activeCells
  coarse_union_eq := base.coarse_union_eq
  cellMass := base.cellMass
  cellMass_pos := base.cellMass_pos
  cellMass_ne_top := base.cellMass_ne_top
  fine_cell_mass := by
    intro cell hcell
    rw [truncation.union_eq]
    exact base.fine_cell_mass cell hcell

noncomputable def PureWZ2BalancedCoverData.exactMultiplicityTruncation
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {Y : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {cover : PureWZ2Section6Cover fine coarse}
    (base : PureWZ2BalancedCoverData cover Y coarseShading)
    (hdelta : 0 < delta)
    (hcubical : WZ1PaperIsCubicalShading Y)
    (m : ℕ) (hm : 0 < m)
    (hconstant : Y.HasConstantMultiplicity m (2 * m)) :
    let truncation := pureWZ2Node05_exactMultiplicityTruncation
      Y hdelta hcubical m hm hconstant
    PureWZ2BalancedCoverData
      cover truncation.truncated coarseShading := by
  let truncation := pureWZ2Node05_exactMultiplicityTruncation
    Y hdelta hcubical m hm hconstant
  exact truncation.toBalancedBase base

/-- On every retained balanced coarse cell, the actual indexed incidence mass
of the truncated shading is exactly `m` times the original union cell mass. -/
theorem PureWZ2Node05ExactMultiplicityTruncationData.cellIncidenceMass_eq
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {Y : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {cover : PureWZ2Section6Cover fine coarse}
    {hdelta : 0 < delta} {m : ℕ}
    (truncation : PureWZ2Node05ExactMultiplicityTruncationData Y hdelta m)
    (base : PureWZ2BalancedCoverData cover Y coarseShading)
    (cell : WZ2PaperCellIndex) (hcell : cell ∈ base.activeCells) :
    wz2PaperCellIncidenceMass (rho := rho) truncation.truncated cell =
      (m : ENNReal) * base.cellMass := by
  have hFubini :=
    sum_volume_inter_eq_setLIntegral_pointMultiplicity
      truncation.truncated
        (S := wz1PaperGridCube rho cell)
        (wz1PaperGridCube_measurable cell)
  unfold wz2PaperCellIncidenceMass
  change (∑ source : Fin (wz1PaperBodyFamily fine).card,
      volume (truncation.truncated.carrier source ∩
        wz1PaperGridCube rho cell)) = (m : ENNReal) * base.cellMass
  rw [hFubini]
  have hpointwise : ∀ point ∈ wz1PaperGridCube rho cell,
      (truncation.truncated.pointMultiplicity point : ENNReal) =
        (truncation.truncated.union).indicator
          (fun _ : Point3 => (m : ENNReal)) point := by
    intro point hpointCell
    by_cases hpointUnion : point ∈ truncation.truncated.union
    · simp only [Set.indicator_of_mem hpointUnion]
      exact_mod_cast truncation.pointMultiplicity_eq point hpointUnion
    · simp only [Set.indicator_apply, hpointUnion, ↓reduceIte]
      have hnone : ∀ source : Fin fine.card,
          point ∉ truncation.truncated.carrier source := by
        intro source hsource
        exact hpointUnion ⟨source, hsource⟩
      simp [Kakeya.Streamlined.Shading.pointMultiplicity, hnone]
  calc
    (∫⁻ point in wz1PaperGridCube rho cell,
        (truncation.truncated.pointMultiplicity point : ENNReal))
        = ∫⁻ point in wz1PaperGridCube rho cell,
            (truncation.truncated.union).indicator
              (fun _ : Point3 => (m : ENNReal)) point := by
          apply MeasureTheory.setLIntegral_congr_fun
            (wz1PaperGridCube_measurable cell)
          exact hpointwise
    _ = ∫⁻ point in
          truncation.truncated.union ∩ wz1PaperGridCube rho cell,
            (m : ENNReal) := by
          rw [MeasureTheory.setLIntegral_indicator
            (measurableSet_shading_union truncation.truncated)]
    _ = (m : ENNReal) * volume
          (truncation.truncated.union ∩ wz1PaperGridCube rho cell) := by
          rw [MeasureTheory.setLIntegral_const]
    _ = (m : ENNReal) * base.cellMass := by
          rw [truncation.union_eq, base.fine_cell_mass cell hcell]

/-- The exact indexed incidence mass is positive and finite. -/
theorem PureWZ2Node05ExactMultiplicityTruncationData.cellIncidenceMass_pos
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {Y : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {cover : PureWZ2Section6Cover fine coarse}
    {hdelta : 0 < delta} {m : ℕ}
    (truncation : PureWZ2Node05ExactMultiplicityTruncationData Y hdelta m)
    (base : PureWZ2BalancedCoverData cover Y coarseShading)
    (hm : 0 < m) (cell : WZ2PaperCellIndex)
    (hcell : cell ∈ base.activeCells) :
    0 < wz2PaperCellIncidenceMass (rho := rho) truncation.truncated cell := by
  rw [truncation.cellIncidenceMass_eq base cell hcell]
  exact ENNReal.mul_pos (by simp [Nat.ne_of_gt hm]) base.cellMass_pos.ne'

theorem PureWZ2Node05ExactMultiplicityTruncationData.cellIncidenceMass_ne_top
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {Y : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {cover : PureWZ2Section6Cover fine coarse}
    {hdelta : 0 < delta} {m : ℕ}
    (truncation : PureWZ2Node05ExactMultiplicityTruncationData Y hdelta m)
    (base : PureWZ2BalancedCoverData cover Y coarseShading)
    (cell : WZ2PaperCellIndex) (hcell : cell ∈ base.activeCells) :
    wz2PaperCellIncidenceMass (rho := rho) truncation.truncated cell ≠ ⊤ := by
  rw [truncation.cellIncidenceMass_eq base cell hcell]
  exact ENNReal.mul_ne_top (by simp) base.cellMass_ne_top

/-- Package the exact multiplicity truncation as the Node-5 balanced cover.
The active coarse cells, coarse shading, cover, and parent map are unchanged. -/
noncomputable def PureWZ2Node05ExactMultiplicityTruncationData.toNode5Balanced
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {Y : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {cover : PureWZ2Section6Cover fine coarse}
    {hdelta : 0 < delta} {m : ℕ}
    (truncation : PureWZ2Node05ExactMultiplicityTruncationData Y hdelta m)
    (base : PureWZ2BalancedCoverData cover Y coarseShading)
    (hm : 0 < m)
    (fineCellNested :
      ∀ source point, point ∈ Y.carrier source →
        ∃ cell ∈ base.activeCells,
          wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆
            wz1PaperGridCube rho cell) :
    let truncatedBase := truncation.toBalancedBase base
    PureWZ2Node5BalancedCoverData truncatedBase := by
  let truncatedBase := truncation.toBalancedBase base
  exact {
    incidenceMass := (m : ENNReal) * base.cellMass
    incidenceMass_pos :=
      ENNReal.mul_pos (by simp [Nat.ne_of_gt hm]) base.cellMass_pos.ne'
    incidenceMass_ne_top :=
      ENNReal.mul_ne_top (by simp) base.cellMass_ne_top
    fine_cell_incidence_mass := by
      intro cell hcell
      exact truncation.cellIncidenceMass_eq base cell hcell
    fine_cell_nested := by
      intro source point hpoint
      exact fineCellNested source point (truncation.subshading source hpoint) }

end Kakeya.Assouad

end
