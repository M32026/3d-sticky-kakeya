import MyLeanRepo.Kakeya.Assouad.PropStickyBoundaryCellPruningStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyBoundaryCellPruningGeometry

/-!
# Boundary-cell pruning for WZ2 `prop: sticky`
-/

open MeasureTheory

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

theorem wz2_paper_boundary_cell_pruning_of_crossing_mass
    {delta rho : ℝ}
    (hdelta : 0 < delta)
    (hdelta_le_rho : delta ≤ rho)
    (hrho : 0 < rho)
    (hrho_le_one : rho ≤ 1)
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading fine)
    (hcubical : WZ1PaperIsCubicalShading shading)
    (multiplicityCap : ENNReal)
    (hcap :
      ∀ point,
        (shading.pointMultiplicity point : ENNReal) ≤
          multiplicityCap)
    (hcrossingMass :
      (∑ index : Fin fine.card,
          volume
            (shading.carrier index ∩
              wz2PaperBoundaryCrossingRegion
                (rho := rho) shading hdelta)) <
        shading.mass) :
    Nonempty
      (WZ2PaperBoundaryCellPruningData
        (rho := rho) shading hdelta multiplicityCap) := by
  classical
  let coarseParent := fun cell =>
    wz1PaperGridIndex rho (cellCorner delta cell)
  let activeCells := wz1PaperActiveCells shading hdelta
  let safeFineCells :=
    activeCells.filter fun cell =>
      wz1PaperGridCube delta cell ⊆
        wz1PaperGridCube rho (coarseParent cell)
  let crossingFineCells := activeCells \ safeFineCells
  let crossingRegion : Set Point3 :=
    ⋃ cell ∈ crossingFineCells, wz1PaperGridCube delta cell
  let safeUnion : Set Point3 :=
    ⋃ cell ∈ safeFineCells, wz1PaperGridCube delta cell
  have h_safe_cnt :
      Set.Countable (↑safeFineCells : Set (ℤ × ℤ × ℤ)) :=
    Finset.countable_toSet safeFineCells
  have h_cross_cnt :
      Set.Countable (↑crossingFineCells : Set (ℤ × ℤ × ℤ)) :=
    Finset.countable_toSet crossingFineCells
  have h_safeUnion_measurable : MeasurableSet safeUnion :=
    MeasurableSet.biUnion h_safe_cnt fun i _ =>
      wz1PaperGridCube_measurable i
  have h_crossingRegion_measurable :
      MeasurableSet crossingRegion :=
    MeasurableSet.biUnion h_cross_cnt fun i _ =>
      wz1PaperGridCube_measurable i
  let pruned : WZ1PaperTubeShading fine :=
    { carrier := fun i => shading.carrier i ∩ safeUnion
      measurable_carrier := fun i =>
        (shading.measurable_carrier i).inter
          h_safeUnion_measurable
      subset_body := fun i =>
        Set.inter_subset_left.trans (shading.subset_body i) }
  let coarseCells := safeFineCells.image coarseParent
  let availableFineCells := fun coarseCell =>
    safeFineCells.filter fun fineCell =>
      coarseParent fineCell = coarseCell
  have h_gridCubes_disjoint :
      ∀ c1 c2 : WZ2PaperCellIndex, c1 ≠ c2 →
        Disjoint
          (wz1PaperGridCube delta c1)
          (wz1PaperGridCube delta c2) := by
    intro c1 c2 hne
    rw [Set.disjoint_left]
    intro point hfirst hsecond
    have h1 : wz1PaperGridIndex delta point = c1 :=
      (mem_wz1PaperGridCube _ _ _).mp hfirst
    have h2 : wz1PaperGridIndex delta point = c2 :=
      (mem_wz1PaperGridCube _ _ _).mp hsecond
    exact hne (h1.symm.trans h2)
  have h_disjoint : Disjoint safeUnion crossingRegion := by
    rw [Set.disjoint_left]
    intro point hsafe hcross
    rcases Set.mem_iUnion₂.mp hsafe with
      ⟨first, hfirst, hpointFirst⟩
    rcases Set.mem_iUnion₂.mp hcross with
      ⟨second, hsecond, hpointSecond⟩
    have hne : first ≠ second := by
      intro heq
      have hsecondSafe : second ∈ safeFineCells := by
        rw [← heq]
        exact hfirst
      exact (Finset.mem_sdiff.mp hsecond).2 hsecondSafe
    exact
      Set.disjoint_left.mp
        (h_gridCubes_disjoint first second hne)
        hpointFirst hpointSecond
  have h_window :
      ∀ point : Point3,
        point ∈ Kakeya.Streamlined.axisBox 2 2 2 →
          wz1PaperGridIndex delta point ∈
            wz1PaperGridIndicesInWindow delta hdelta := by
    intro point hpoint
    let bound : ℤ := ⌈1 / delta⌉ + 1
    have habs : ∀ coordinate : Fin 3, |point coordinate| ≤ 1 := by
      have hbox :
          |point 0| ≤ 1 ∧ |point 1| ≤ 1 ∧ |point 2| ≤ 1 := by
        simpa [Kakeya.Streamlined.axisBox] using hpoint
      intro coordinate
      fin_cases coordinate <;> tauto
    have hb :
        ∀ coordinate : Fin 3,
          -bound ≤ ⌊point coordinate / delta⌋ ∧
            ⌊point coordinate / delta⌋ ≤ bound := by
      intro coordinate
      have habsCoordinate := habs coordinate
      have hupper :
          point coordinate / delta ≤ 1 / delta := by
        gcongr
        exact (abs_le.mp habsCoordinate).2
      have hlower :
          -(1 / delta) ≤ point coordinate / delta := by
        have h :
            (-1 : ℝ) / delta ≤ point coordinate / delta := by
          gcongr
          exact (abs_le.mp habsCoordinate).1
        have h2 :
            -(1 / delta) = (-1 : ℝ) / delta := by
          ring
        rw [h2]
        exact h
      constructor
      · have hfloor :
            ⌊-(1 / delta)⌋ ≤
              ⌊point coordinate / delta⌋ :=
          Int.floor_mono hlower
        rw [Int.floor_neg] at hfloor
        linarith
      · have hfloor :
            ⌊point coordinate / delta⌋ ≤
              ⌊1 / delta⌋ :=
          Int.floor_mono hupper
        exact
          hfloor.trans
            (Int.floor_le_ceil (1 / delta) |>.trans
              (by omega))
    have h0 :
        ⌊point 0 / delta⌋ ∈ Finset.Icc (-bound) bound := by
      exact Finset.mem_Icc.mpr ⟨(hb 0).1, (hb 0).2⟩
    have h1 :
        ⌊point 1 / delta⌋ ∈ Finset.Icc (-bound) bound := by
      exact Finset.mem_Icc.mpr ⟨(hb 1).1, (hb 1).2⟩
    have h2 :
        ⌊point 2 / delta⌋ ∈ Finset.Icc (-bound) bound := by
      exact Finset.mem_Icc.mpr ⟨(hb 2).1, (hb 2).2⟩
    exact
      Finset.mem_product.mpr
        ⟨h0, Finset.mem_product.mpr ⟨h1, h2⟩⟩
  have h_shading_union_subset_activeUnion :
      shading.union ⊆
        ⋃ cell ∈ activeCells,
          wz1PaperGridCube delta cell := by
    intro point hpoint
    rcases hpoint with ⟨index, hpoint⟩
    let cell := wz1PaperGridIndex delta point
    have hbody :
        point ∈ wz1PaperTubeCarrier (fine.tube index) :=
      shading.subset_body index hpoint
    have hcellWindow :
        cell ∈ wz1PaperGridIndicesInWindow delta hdelta :=
      h_window point hbody.2
    have hcellActive : cell ∈ activeCells := by
      rw [mem_wz1PaperActiveCells]
      exact
        ⟨hcellWindow,
          ⟨point, ⟨index, hpoint⟩,
            (mem_wz1PaperGridCube _ _ _).mpr rfl⟩⟩
    exact
      Set.mem_iUnion₂.mpr
        ⟨cell, hcellActive,
          (mem_wz1PaperGridCube _ _ _).mpr rfl⟩
  have h_activeUnion_subset_shading_union :
      (⋃ cell ∈ activeCells,
          wz1PaperGridCube delta cell) ⊆
        shading.union := by
    intro point hpoint
    rcases Set.mem_iUnion₂.mp hpoint with
      ⟨cell, hcell, hpointCell⟩
    have h :
        shading.union ∩ wz1PaperGridCube delta cell =
          wz1PaperGridCube delta cell :=
      hcubical.inter_activeCell_eq hdelta hcell
    have hpoint' :
        point ∈
          shading.union ∩ wz1PaperGridCube delta cell := by
      rw [h]
      exact hpointCell
    exact hpoint'.1
  have h_shading_union_eq :
      shading.union =
        ⋃ cell ∈ activeCells,
          wz1PaperGridCube delta cell :=
    Set.Subset.antisymm
      h_shading_union_subset_activeUnion
      h_activeUnion_subset_shading_union
  have h_safe_crossing_union :
      safeUnion ∪ crossingRegion =
        ⋃ cell ∈ activeCells,
          wz1PaperGridCube delta cell := by
    have hpartition :
        activeCells = safeFineCells ∪ crossingFineCells := by
      rw [
        Finset.union_sdiff_of_subset
          (Finset.filter_subset _ _)]
    rw [hpartition]
    ext point
    simp [safeUnion, crossingRegion]
  have h_carrier_cover :
      ∀ index,
        shading.carrier index ⊆
          safeUnion ∪ crossingRegion := by
    intro index point hpoint
    have hpointUnion : point ∈ shading.union := ⟨index, hpoint⟩
    rw [h_shading_union_eq, ← h_safe_crossing_union] at hpointUnion
    exact hpointUnion
  have h_volume_add :
      ∀ index,
        volume (shading.carrier index) =
          volume (shading.carrier index ∩ safeUnion) +
            volume
              (shading.carrier index ∩ crossingRegion) := by
    intro index
    have heq :
        shading.carrier index =
          (shading.carrier index ∩ safeUnion) ∪
            (shading.carrier index ∩ crossingRegion) := by
      ext point
      constructor
      · intro hpoint
        rcases h_carrier_cover index hpoint with hsafe | hcross
        · exact Or.inl ⟨hpoint, hsafe⟩
        · exact Or.inr ⟨hpoint, hcross⟩
      · rintro (hpoint | hpoint)
        · exact hpoint.1
        · exact hpoint.1
    have h1 :
        volume (shading.carrier index) =
          volume
            ((shading.carrier index ∩ safeUnion) ∪
              (shading.carrier index ∩ crossingRegion)) :=
      congrArg volume heq
    rw [h1]
    exact
      MeasureTheory.measure_union
        (h_disjoint.mono
          Set.inter_subset_right Set.inter_subset_right)
        ((shading.measurable_carrier index).inter
          h_crossingRegion_measurable)
  have h_mass_eq :
      shading.mass =
        pruned.mass +
          ∑ index : Fin fine.card,
            volume
              (shading.carrier index ∩ crossingRegion) := by
    simp only [Kakeya.Streamlined.Shading.mass, pruned]
    rw [
      Finset.sum_congr rfl fun index _ => h_volume_add index,
      Finset.sum_add_distrib]
    rfl
  have h_fubini :
      (∑ index : Fin fine.card,
          volume
            (shading.carrier index ∩ crossingRegion)) =
        ∫⁻ point in crossingRegion,
          (shading.pointMultiplicity point : ENNReal) :=
    sum_volume_inter_eq_setLIntegral_pointMultiplicity
      shading h_crossingRegion_measurable
  have h_integral_le :
      (∫⁻ point in crossingRegion,
          (shading.pointMultiplicity point : ENNReal)) ≤
        multiplicityCap * volume crossingRegion := by
    calc
      (∫⁻ point in crossingRegion,
          (shading.pointMultiplicity point : ENNReal))
          ≤ ∫⁻ _point in crossingRegion, multiplicityCap := by
            apply MeasureTheory.setLIntegral_mono'
              h_crossingRegion_measurable
            intro point _
            exact hcap point
      _ = multiplicityCap * volume crossingRegion := by
        rw [MeasureTheory.setLIntegral_const]
  have h_mass_le :
      shading.mass ≤
        pruned.mass +
          multiplicityCap * volume crossingRegion := by
    rw [h_mass_eq, h_fubini]
    exact add_le_add_right h_integral_le pruned.mass
  have h_crossing_subset :
      crossingFineCells ⊆ activeCells := by
    intro cell hcell
    exact (Finset.mem_sdiff.mp hcell).1
  have h_crossing_def :
      ∀ cell ∈ crossingFineCells,
        ¬ (wz1PaperGridCube delta cell ⊆
          wz1PaperGridCube rho (coarseParent cell)) := by
    intro cell hcell
    have hactive := (Finset.mem_sdiff.mp hcell).1
    have hnotsafe := (Finset.mem_sdiff.mp hcell).2
    rw [Finset.mem_filter] at hnotsafe
    intro hcontain
    exact hnotsafe ⟨hactive, hcontain⟩
  have h_crossing_volume :
      volume crossingRegion ≤
        ENNReal.ofReal (1000 * delta / rho) :=
    wz2_boundary_cell_pruning_volume_bound
      hcubical hdelta hdelta_le_rho hrho hrho_le_one
      crossingFineCells h_crossing_subset h_crossing_def
  have h_mass_le_explicit :
      shading.mass ≤
        pruned.mass +
          multiplicityCap *
            ENNReal.ofReal (1000 * delta / rho) := by
    have hmul :
        multiplicityCap * volume crossingRegion ≤
          multiplicityCap *
            ENNReal.ofReal (1000 * delta / rho) :=
      mul_le_mul_left' h_crossing_volume multiplicityCap
    exact h_mass_le.trans (add_le_add_right hmul pruned.mass)
  have h_mass_pos : 0 < pruned.mass := by
    by_contra hzero
    have hpruned : pruned.mass = 0 := by simpa using hzero
    have hcrossingEq :
        (∑ index : Fin fine.card,
            volume
              (shading.carrier index ∩ crossingRegion)) =
          shading.mass := by
      simpa [hpruned] using h_mass_eq.symm
    change
      (∑ index : Fin fine.card,
          volume
            (shading.carrier index ∩ crossingRegion)) <
        shading.mass at hcrossingMass
    rw [hcrossingEq] at hcrossingMass
    exact (lt_irrefl shading.mass) hcrossingMass
  have h_safe_nonempty : safeFineCells.Nonempty := by
    by_contra hempty
    have hsafes : safeFineCells = ∅ := by simpa using hempty
    have hsafeUnion : safeUnion = ∅ := by
      simp [safeUnion, hsafes]
    have hpruned : pruned.mass = 0 := by
      simp [pruned, hsafeUnion, Kakeya.Streamlined.Shading.mass]
    rw [hpruned] at h_mass_pos
    exact (lt_irrefl 0) h_mass_pos
  have h_pruned_cubical :
      WZ1PaperIsCubicalShading pruned := by
    intro index point hpoint
    have hsource : point ∈ shading.carrier index := hpoint.1
    rcases Set.mem_iUnion₂.mp hpoint.2 with
      ⟨cell, hcell, hpointCell⟩
    have hindex : wz1PaperGridIndex delta point = cell :=
      (mem_wz1PaperGridCube _ _ _).mp hpointCell
    have hcarrier :
        wz1PaperGridCube delta
            (wz1PaperGridIndex delta point) ⊆
          shading.carrier index :=
      hcubical index point hsource
    intro other hother
    refine ⟨hcarrier hother, ?_⟩
    exact
      Set.mem_iUnion₂.mpr
        ⟨cell, hcell, by rwa [← hindex]⟩
  have h_pruned_union_eq : pruned.union = safeUnion := by
    ext point
    constructor
    · rintro ⟨index, hpoint⟩
      exact hpoint.2
    · intro hpoint
      rcases Set.mem_iUnion₂.mp hpoint with
        ⟨cell, hcell, hpointCell⟩
      have hactive : cell ∈ activeCells :=
        (Finset.mem_filter.mp hcell).1
      have hcube :
          wz1PaperGridCube delta cell ⊆ shading.union :=
        Set.inter_eq_right.mp
          (hcubical.inter_activeCell_eq hdelta hactive)
      rcases hcube hpointCell with ⟨index, hsource⟩
      exact ⟨index, hsource, hpoint⟩
  have h_coarse_nonempty : coarseCells.Nonempty :=
    h_safe_nonempty.image coarseParent
  have h_available_nonempty :
      ∀ coarseCell ∈ coarseCells,
        (availableFineCells coarseCell).Nonempty := by
    intro coarseCell hcoarse
    rcases Finset.mem_image.mp hcoarse with
      ⟨fineCell, hfineCell, rfl⟩
    exact
      ⟨fineCell,
        Finset.mem_filter.mpr ⟨hfineCell, rfl⟩⟩
  have h_ready :
      ∀ coarseCell ∈ coarseCells,
        ∀ fineCell ∈ availableFineCells coarseCell,
          fineCell ∈ wz1PaperActiveCells pruned hdelta ∧
            wz1PaperGridCube delta fineCell ⊆
              wz1PaperGridCube rho coarseCell := by
    intro coarseCell _ fineCell hfineCell
    have hsafe : fineCell ∈ safeFineCells :=
      (Finset.mem_filter.mp hfineCell).1
    have hparent : coarseParent fineCell = coarseCell :=
      (Finset.mem_filter.mp hfineCell).2
    have hcontain :
        wz1PaperGridCube delta fineCell ⊆
          wz1PaperGridCube rho coarseCell := by
      simpa [hparent] using (Finset.mem_filter.mp hsafe).2
    have hactive : fineCell ∈ activeCells :=
      (Finset.mem_filter.mp hsafe).1
    have hwindow :
        fineCell ∈ wz1PaperGridIndicesInWindow delta hdelta :=
      (mem_wz1PaperActiveCells shading hdelta fineCell).mp
        hactive |>.1
    have hcellNonempty :
        (wz1PaperGridCube delta fineCell).Nonempty :=
      ⟨cellCorner delta fineCell,
        cellCorner_mem_gridCube hdelta fineCell⟩
    have hcellSubset :
        wz1PaperGridCube delta fineCell ⊆ pruned.union := by
      rw [h_pruned_union_eq]
      intro point hpoint
      exact Set.mem_iUnion₂.mpr ⟨fineCell, hsafe, hpoint⟩
    have hinter :
        (pruned.union ∩
          wz1PaperGridCube delta fineCell).Nonempty := by
      rcases hcellNonempty with ⟨point, hpoint⟩
      exact ⟨point, hcellSubset hpoint, hpoint⟩
    exact
      ⟨(mem_wz1PaperActiveCells pruned hdelta fineCell).mpr
          ⟨hwindow, hinter⟩,
        hcontain⟩
  have h_safe_contained :
      ∀ fineCell ∈ safeFineCells,
        wz1PaperGridCube delta fineCell ⊆
          wz1PaperGridCube rho (coarseParent fineCell) := by
    intro fineCell hfineCell
    exact (Finset.mem_filter.mp hfineCell).2
  exact
    ⟨{
      safeFineCells := safeFineCells
      crossingFineCells := crossingFineCells
      safeFineCells_subset := Finset.filter_subset _ _
      crossingFineCells_eq := rfl
      activeCells_partition := by
        rw [
          Finset.union_sdiff_of_subset
            (Finset.filter_subset _ _)]
      crossingRegion := crossingRegion
      crossingRegion_eq := rfl
      crossingRegion_eq_source := rfl
      crossingRegion_measurable := h_crossingRegion_measurable
      crossingRegion_volume := h_crossing_volume
      pruned := pruned
      pruned_carrier_eq := fun _ => rfl
      pruned_subshading := fun _ => Set.inter_subset_left
      pruned_cubical := h_pruned_cubical
      pruned_union_eq := h_pruned_union_eq
      source_mass_le := h_mass_le
      source_mass_eq_crossing := h_mass_eq
      source_mass_le_explicit := h_mass_le_explicit
      pruned_mass_pos := h_mass_pos
      safeFineCells_nonempty := h_safe_nonempty
      coarseParent := coarseParent
      safeFineCell_contained := h_safe_contained
      coarseCells := coarseCells
      coarseCells_eq := rfl
      coarseCells_nonempty := h_coarse_nonempty
      availableFineCells := availableFineCells
      availableFineCells_eq := fun _ => rfl
      availableFineCells_nonempty := h_available_nonempty
      availableFineCells_ready := h_ready
    }⟩

theorem wz2_paper_boundary_crossing_mass_le_of_multiplicity_cap
    {delta rho : ℝ}
    (hdelta : 0 < delta)
    (hdelta_le_rho : delta ≤ rho)
    (hrho : 0 < rho)
    (hrho_le_one : rho ≤ 1)
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading fine)
    (hcubical : WZ1PaperIsCubicalShading shading)
    (multiplicityCap : ENNReal)
    (hcap :
      ∀ point,
        (shading.pointMultiplicity point : ENNReal) ≤
          multiplicityCap) :
    (∑ index : Fin fine.card,
        volume
          (shading.carrier index ∩
            wz2PaperBoundaryCrossingRegion
              (rho := rho) shading hdelta)) ≤
      multiplicityCap *
        ENNReal.ofReal (1000 * delta / rho) := by
  let crossingFineCells :=
    wz2PaperBoundaryCrossingFineCells
      (rho := rho) shading hdelta
  let crossingRegion :=
    wz2PaperBoundaryCrossingRegion
      (rho := rho) shading hdelta
  have hcountable :
      Set.Countable
        (↑crossingFineCells : Set WZ2PaperCellIndex) :=
    Finset.countable_toSet crossingFineCells
  have hmeasurable : MeasurableSet crossingRegion := by
    exact MeasurableSet.biUnion hcountable fun cell _ =>
      wz1PaperGridCube_measurable cell
  have hcrossingSubset :
      crossingFineCells ⊆
        wz1PaperActiveCells shading hdelta := by
    intro cell hcell
    exact (Finset.mem_sdiff.mp hcell).1
  have hcrossingDef :
      ∀ cell ∈ crossingFineCells,
        ¬ (wz1PaperGridCube delta cell ⊆
          wz1PaperGridCube rho
            (wz2PaperBoundaryCoarseParent delta rho cell)) := by
    intro cell hcell
    have hactive := (Finset.mem_sdiff.mp hcell).1
    have hnotsafe := (Finset.mem_sdiff.mp hcell).2
    rw [wz2PaperBoundarySafeFineCells, Finset.mem_filter] at hnotsafe
    intro hcontain
    exact hnotsafe ⟨hactive, hcontain⟩
  have hvolume :
      volume crossingRegion ≤
        ENNReal.ofReal (1000 * delta / rho) := by
    exact
      wz2_boundary_cell_pruning_volume_bound
        hcubical hdelta hdelta_le_rho hrho hrho_le_one
        crossingFineCells hcrossingSubset hcrossingDef
  have hintegral :
      (∫⁻ point in crossingRegion,
          (shading.pointMultiplicity point : ENNReal)) ≤
        multiplicityCap * volume crossingRegion := by
    calc
      (∫⁻ point in crossingRegion,
          (shading.pointMultiplicity point : ENNReal))
          ≤ ∫⁻ _point in crossingRegion, multiplicityCap := by
            apply MeasureTheory.setLIntegral_mono' hmeasurable
            intro point _
            exact hcap point
      _ = multiplicityCap * volume crossingRegion := by
        rw [MeasureTheory.setLIntegral_const]
  change
    (∑ index : Fin fine.card,
        volume (shading.carrier index ∩ crossingRegion)) ≤ _
  calc
    (∑ index : Fin fine.card,
        volume (shading.carrier index ∩ crossingRegion))
        =
      ∫⁻ point in crossingRegion,
        (shading.pointMultiplicity point : ENNReal) :=
      sum_volume_inter_eq_setLIntegral_pointMultiplicity
        shading hmeasurable
    _ ≤ multiplicityCap * volume crossingRegion := hintegral
    _ ≤
      multiplicityCap *
        ENNReal.ofReal (1000 * delta / rho) :=
      mul_le_mul_left' hvolume multiplicityCap

theorem wz2_prop_sticky_boundary_cell_pruning :
    WZ2PropStickyBoundaryCellPruningStatement := by
  intro delta rho hdelta hdelta_le_rho hrho hrho_le_one fine shading
    hcubical multiplicityCap hcap hsmall
  have hcrossingMass :
      (∑ index : Fin fine.card,
          volume
            (shading.carrier index ∩
              wz2PaperBoundaryCrossingRegion
                (rho := rho) shading hdelta)) <
        shading.mass :=
    (wz2_paper_boundary_crossing_mass_le_of_multiplicity_cap
      hdelta hdelta_le_rho hrho hrho_le_one
      shading hcubical multiplicityCap hcap).trans_lt hsmall
  exact
    wz2_paper_boundary_cell_pruning_of_crossing_mass
      hdelta hdelta_le_rho hrho hrho_le_one
      shading hcubical multiplicityCap hcap hcrossingMass

end Kakeya.Assouad

end
