import MyLeanRepo.Kakeya.Assouad.PropStickyExactCellBalancingHelpers
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperRelativeMultiplicityHelpers
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperRefinementHelpers
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperMultiplicityHelpers

/-!
# Helper lemmas for final fine exact balancing

Provides the mass-retention bridge from cell-count retention to shaded-mass
retention for cubical paper shadings sharing a dyadic multiplicity band.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Finset

attribute [local instance] Classical.propDecidable

/-- Any point in the paper axis box has its grid index in the finite window. -/
lemma paper_point_gridIndex_in_window
    {delta : ℝ}
    (hdelta : 0 < delta) {point : Point3}
    (hpoint : point ∈ Kakeya.Streamlined.axisBox 2 2 2) :
    wz1PaperGridIndex delta point ∈
      wz1PaperGridIndicesInWindow delta hdelta := by
  let bound : ℤ := ⌈1 / delta⌉ + 1
  have habs : ∀ coordinate : Fin 3, |point coordinate| ≤ 1 := by
    have hbox : |point 0| ≤ 1 ∧ |point 1| ≤ 1 ∧ |point 2| ≤ 1 := by
      simpa [Kakeya.Streamlined.axisBox] using hpoint
    intro coordinate
    fin_cases coordinate <;> tauto
  have hb : ∀ coordinate : Fin 3,
      -bound ≤ ⌊point coordinate / delta⌋ ∧
        ⌊point coordinate / delta⌋ ≤ bound := by
    intro coordinate
    have habsCoordinate := habs coordinate
    have hupper : point coordinate / delta ≤ 1 / delta := by
      gcongr
      exact (abs_le.mp habsCoordinate).2
    have hlower : -(1 / delta) ≤ point coordinate / delta := by
      have h : (-1 : ℝ) / delta ≤ point coordinate / delta := by
        gcongr
        exact (abs_le.mp habsCoordinate).1
      have h2 : -(1 / delta) = (-1 : ℝ) / delta := by ring
      rw [h2]
      exact h
    constructor
    · have hfloor : ⌊-(1 / delta)⌋ ≤ ⌊point coordinate / delta⌋ :=
        Int.floor_mono hlower
      rw [Int.floor_neg] at hfloor
      linarith
    · have hfloor : ⌊point coordinate / delta⌋ ≤ ⌊1 / delta⌋ :=
        Int.floor_mono hupper
      exact hfloor.trans (Int.floor_le_ceil (1 / delta) |>.trans (by omega))
  have h0 : ⌊point 0 / delta⌋ ∈ Finset.Icc (-bound) bound :=
    Finset.mem_Icc.mpr ⟨(hb 0).1, (hb 0).2⟩
  have h1 : ⌊point 1 / delta⌋ ∈ Finset.Icc (-bound) bound :=
    Finset.mem_Icc.mpr ⟨(hb 1).1, (hb 1).2⟩
  have h2 : ⌊point 2 / delta⌋ ∈ Finset.Icc (-bound) bound :=
    Finset.mem_Icc.mpr ⟨(hb 2).1, (hb 2).2⟩
  exact Finset.mem_product.mpr ⟨h0, Finset.mem_product.mpr ⟨h1, h2⟩⟩

/-- For a cubical paper shading, the union equals the union of its active grid cubes. -/
theorem WZ1PaperIsCubicalShading.union_eq_activeCells
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading fine}
    (hcubical : WZ1PaperIsCubicalShading shading)
    (hdelta : 0 < delta) :
    shading.union =
      ⋃ cell ∈ wz1PaperActiveCells shading hdelta,
        wz1PaperGridCube delta cell := by
  let activeCells := wz1PaperActiveCells shading hdelta
  apply Set.Subset.antisymm
  · intro point hpoint
    rcases hpoint with ⟨index, hcarrier⟩
    let cell := wz1PaperGridIndex delta point
    have hbody : point ∈ wz1PaperTubeCarrier (fine.tube index) :=
      shading.subset_body index hcarrier
    have hcellWindow : cell ∈ wz1PaperGridIndicesInWindow delta hdelta :=
      paper_point_gridIndex_in_window (delta := delta) hdelta hbody.2
    have hpointCell : point ∈ wz1PaperGridCube delta cell :=
      (mem_wz1PaperGridCube delta cell point).mpr rfl
    have hcellActive : cell ∈ activeCells := by
      rw [mem_wz1PaperActiveCells shading hdelta cell]
      exact ⟨hcellWindow, ⟨point, ⟨index, hcarrier⟩, hpointCell⟩⟩
    exact Set.mem_iUnion₂.mpr ⟨cell, hcellActive, hpointCell⟩
  · intro point hpoint
    rcases Set.mem_iUnion₂.mp hpoint with ⟨cell, hcell, hpointCell⟩
    have h : shading.union ∩ wz1PaperGridCube delta cell =
        wz1PaperGridCube delta cell :=
      hcubical.inter_activeCell_eq hdelta hcell
    have h' : point ∈ shading.union ∩ wz1PaperGridCube delta cell := by
      rw [h]
      exact hpointCell
    exact h'.1

/--
Mass retention from cell-count retention for cubical paper shadings in a common
dyadic multiplicity band.
-/
theorem cubical_mass_retention_from_cell_count
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (S T : WZ1PaperTubeShading fine)
    (hS_cubical : WZ1PaperIsCubicalShading S)
    (hT_cubical : WZ1PaperIsCubicalShading T)
    (hdelta : 0 < delta)
    (m : ℕ)
    (hS_mult : S.HasConstantMultiplicity m (2 * m))
    (hT_mult : T.HasConstantMultiplicity m (2 * m))
    (K : ENNReal)
    (h_count :
      (wz1PaperActiveCells S hdelta).card ≤
        K * (wz1PaperActiveCells T hdelta).card) :
    S.mass ≤ 2 * K * T.mass := by
  let activeS := wz1PaperActiveCells S hdelta
  let activeT := wz1PaperActiveCells T hdelta
  let cv : ENNReal := volume (wz1PaperGridCube delta (0, 0, 0))
  have hcv_ne_top : cv ≠ ⊤ :=
    wz1PaperGridCube_volume_ne_top hdelta (0, 0, 0)
  have hS_union_eq : S.union =
      ⋃ cell ∈ activeS, wz1PaperGridCube delta cell :=
    hS_cubical.union_eq_activeCells hdelta
  have hT_union_eq : T.union =
      ⋃ cell ∈ activeT, wz1PaperGridCube delta cell :=
    hT_cubical.union_eq_activeCells hdelta
  have hvolS : volume S.union = (activeS.card : ENNReal) * cv := by
    rw [hS_union_eq]
    exact wz1PaperGridCube_volume_biUnion hdelta activeS
  have hvolT : volume T.union = (activeT.card : ENNReal) * cv := by
    rw [hT_union_eq]
    exact wz1PaperGridCube_volume_biUnion hdelta activeT
  have hS_mass := (constant_multiplicity_mass_volume_generic hS_mult).2
  have hT_mass := (constant_multiplicity_mass_volume_generic hT_mult).1
  calc
    S.mass ≤ (2 * m : ENNReal) * volume S.union := hS_mass
    _ = (2 * m : ENNReal) * ((activeS.card : ENNReal) * cv) := by rw [hvolS]
    _ ≤ (2 * m : ENNReal) * (K * (activeT.card : ENNReal) * cv) := by gcongr
    _ = 2 * K * ((m : ENNReal) * ((activeT.card : ENNReal) * cv)) := by ring
    _ = 2 * K * ((m : ENNReal) * volume T.union) := by rw [hvolT]
    _ ≤ 2 * K * T.mass := by gcongr

lemma wholeCellRestriction_pointMultiplicity_eq
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {S T : WZ1PaperTubeShading fine}
    {U : Set Point3}
    (hcarrier : ∀ i, T.carrier i = S.carrier i ∩ U)
    {p : Point3}
    (hp : p ∈ T.union) :
    T.pointMultiplicity p = S.pointMultiplicity p := by
  have hU : p ∈ U := by
    rcases hp with ⟨i, hi⟩
    rw [hcarrier i] at hi
    exact hi.2
  simp only [Kakeya.Streamlined.Shading.pointMultiplicity]
  congr 1
  apply Finset.filter_congr
  intro i _
  rw [hcarrier i]
  exact ⟨fun h => h.1, fun h => ⟨h, hU⟩⟩

lemma wholeCellRestriction_fiberPointMultiplicity_eq
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {S T : WZ1PaperTubeShading fine}
    {U : Set Point3}
    (hcarrier : ∀ i, T.carrier i = S.carrier i ∩ U)
    (selected : Kakeya.Streamlined.TubeSubfamily fine)
    {p : Point3}
    (hp : p ∈ (restrictPaperShading selected T).union) :
    (restrictPaperShading selected T).pointMultiplicity p =
      (restrictPaperShading selected S).pointMultiplicity p := by
  have hU : p ∈ U := by
    rcases hp with ⟨i, hi⟩
    have h : p ∈ T.carrier (selected.embedding i) := hi
    rw [hcarrier (selected.embedding i)] at h
    exact h.2
  simp only [Kakeya.Streamlined.Shading.pointMultiplicity]
  congr 1
  apply Finset.filter_congr
  intro i _
  simp only [restrictPaperShading]
  rw [hcarrier (selected.embedding i)]
  exact ⟨fun h => h.1, fun h => ⟨h, hU⟩⟩

lemma dyadicBandSubshading_pointMultiplicity_eq
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading fine}
    {level : ℕ}
    {p : Point3}
    (hp : p ∈ (wz1PaperDyadicBandSubshading S level).union) :
    (wz1PaperDyadicBandSubshading S level).pointMultiplicity p =
      S.pointMultiplicity p := by
  have hband : p ∈ wz1PaperDyadicMultiplicityBand S level := by
    rcases hp with ⟨i, hi⟩
    exact hi.2
  simp only [Kakeya.Streamlined.Shading.pointMultiplicity]
  congr 1
  apply Finset.filter_congr
  intro i _
  change
    (p ∈ S.carrier i ∧ p ∈ wz1PaperDyadicMultiplicityBand S level) ↔
      p ∈ S.carrier i
  exact and_iff_left hband

lemma dyadicBandSubshading_fiberPointMultiplicity_eq
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading fine}
    {level : ℕ}
    (selected : Kakeya.Streamlined.TubeSubfamily fine)
    {p : Point3}
    (hp : p ∈ (restrictPaperShading selected
        (wz1PaperDyadicBandSubshading S level)).union) :
    (restrictPaperShading selected
        (wz1PaperDyadicBandSubshading S level)).pointMultiplicity p =
      (restrictPaperShading selected S).pointMultiplicity p := by
  have hband : p ∈ wz1PaperDyadicMultiplicityBand S level := by
    rcases hp with ⟨i, hi⟩
    exact hi.2
  simp only [Kakeya.Streamlined.Shading.pointMultiplicity]
  congr 1
  apply Finset.filter_congr
  intro i _
  simp only [restrictPaperShading]
  change
    (p ∈ S.carrier (selected.embedding i) ∧
        p ∈ wz1PaperDyadicMultiplicityBand S level) ↔
      p ∈ S.carrier (selected.embedding i)
  exact and_iff_left hband

lemma activeCell_subset_retainedFineCells
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading fine}
    {coarseCells : Finset WZ2PaperCellIndex}
    {availableFineCells : WZ2PaperCellIndex → Finset WZ2PaperCellIndex}
    {balancing : WZ2PaperExactCellBalancingData
        (delta := delta) (rho := rho) (fine := fine)
        shading coarseCells availableFineCells}
    {S : WZ1PaperTubeShading fine}
    (hS_union_subset : S.union ⊆ balancing.refined.union)
    (hdelta : 0 < delta)
    {fineCell : WZ2PaperCellIndex}
    (hfine : fineCell ∈ wz1PaperActiveCells S hdelta) :
    fineCell ∈ balancing.retainedFineCells := by
  have h1 : fineCell ∈ wz1PaperGridIndicesInWindow delta hdelta :=
    (mem_wz1PaperActiveCells S hdelta fineCell).mp hfine |>.1
  have h2 : (S.union ∩ wz1PaperGridCube delta fineCell).Nonempty :=
    (mem_wz1PaperActiveCells S hdelta fineCell).mp hfine |>.2
  have h3 : (balancing.refined.union ∩
      wz1PaperGridCube delta fineCell).Nonempty :=
    h2.mono (fun x hx => ⟨hS_union_subset hx.1, hx.2⟩)
  have h4 : fineCell ∈ wz1PaperActiveCells balancing.refined hdelta := by
    rw [mem_wz1PaperActiveCells balancing.refined hdelta]
    exact ⟨h1, h3⟩
  have h5 : balancing.refined.union ∩ wz1PaperGridCube delta fineCell =
        wz1PaperGridCube delta fineCell :=
    balancing.refined_cubical.inter_activeCell_eq hdelta h4
  have h6 : wz1PaperGridCube delta fineCell ⊆ balancing.refined.union := by
    have h : (balancing.refined.union ∩ wz1PaperGridCube delta fineCell) ⊆
        balancing.refined.union := Set.inter_subset_left
    rw [h5] at h
    exact h
  have h7 : balancing.refined.union =
        ⋃ f ∈ balancing.retainedFineCells, wz1PaperGridCube delta f :=
    balancing.refined_union_eq
  have h6' : wz1PaperGridCube delta fineCell ⊆
        ⋃ f ∈ balancing.retainedFineCells, wz1PaperGridCube delta f := by
    rw [h7] at h6
    exact h6
  have hvol_pos : 0 < volume (wz1PaperGridCube delta fineCell) :=
    wz1PaperGridCube_volume_pos hdelta fineCell
  have hnonempty : (wz1PaperGridCube delta fineCell).Nonempty := by
    by_contra h
    have h_empty : wz1PaperGridCube delta fineCell = ∅ := by
      simpa [Set.not_nonempty_iff_eq_empty] using h
    rw [h_empty] at hvol_pos
    simp at hvol_pos
  rcases hnonempty with ⟨p, hp⟩
  have h8 : p ∈ ⋃ f ∈ balancing.retainedFineCells,
      wz1PaperGridCube delta f := h6' hp
  have h8' : ∃ (g : WZ2PaperCellIndex),
      g ∈ balancing.retainedFineCells ∧
        p ∈ wz1PaperGridCube delta g := by
    simpa [Finset.mem_biUnion] using h8
  rcases h8' with ⟨g, hg, hpg⟩
  have h11 : fineCell = g := by
    by_contra hne
    have hdisj : Disjoint (wz1PaperGridCube delta fineCell)
        (wz1PaperGridCube delta g) :=
      wz1PaperGridCube_disjoint hne
    exact Set.disjoint_left.mp hdisj hp hpg
  exact h11 ▸ hg

lemma unique_coarseParent_of_retainedFineCell
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading fine}
    {coarseCells : Finset WZ2PaperCellIndex}
    {availableFineCells : WZ2PaperCellIndex → Finset WZ2PaperCellIndex}
    {balancing : WZ2PaperExactCellBalancingData
        (delta := delta) (rho := rho) (fine := fine)
        shading coarseCells availableFineCells}
    (hdelta : 0 < delta)
    {fineCell : WZ2PaperCellIndex}
    (hfine : fineCell ∈ balancing.retainedFineCells) :
    ∃! (coarseCell : WZ2PaperCellIndex),
      coarseCell ∈ balancing.retainedCoarseCells ∧
        fineCell ∈ balancing.selectedFineCells coarseCell := by
  have hex : ∃ (coarseCell : WZ2PaperCellIndex),
      coarseCell ∈ balancing.retainedCoarseCells ∧
        fineCell ∈ balancing.selectedFineCells coarseCell := by
    rw [balancing.retainedFineCells_eq] at hfine
    rcases Finset.mem_biUnion.mp hfine with ⟨coarseCell, hcoarse, hsel⟩
    exact ⟨coarseCell, hcoarse, hsel⟩
  rcases hex with ⟨coarseCell, hcoarse, hsel⟩
  refine ⟨coarseCell, ⟨hcoarse, hsel⟩, ?_⟩
  intro other hother
  have hcont1 : wz1PaperGridCube delta fineCell ⊆
        wz1PaperGridCube rho coarseCell :=
    balancing.fine_cell_containment coarseCell hcoarse fineCell hsel
  have hcont2 : wz1PaperGridCube delta fineCell ⊆
        wz1PaperGridCube rho other :=
    balancing.fine_cell_containment other hother.1 fineCell hother.2
  have hvol_pos : 0 < volume (wz1PaperGridCube delta fineCell) :=
    wz1PaperGridCube_volume_pos hdelta fineCell
  have hnonempty : (wz1PaperGridCube delta fineCell).Nonempty := by
    by_contra h
    have h_empty : wz1PaperGridCube delta fineCell = ∅ := by
      simpa [Set.not_nonempty_iff_eq_empty] using h
    rw [h_empty] at hvol_pos
    simp at hvol_pos
  rcases hnonempty with ⟨p, hp⟩
  have h_in1 : p ∈ wz1PaperGridCube rho coarseCell := hcont1 hp
  have h_in2 : p ∈ wz1PaperGridCube rho other := hcont2 hp
  have h_eq : coarseCell = other := by
    have hi : wz1PaperGridIndex rho p = coarseCell :=
      (mem_wz1PaperGridCube rho coarseCell p).mp h_in1
    have hj : wz1PaperGridIndex rho p = other :=
      (mem_wz1PaperGridCube rho other p).mp h_in2
    exact hi.symm.trans hj
  exact h_eq.symm

end Kakeya.Assouad

end
