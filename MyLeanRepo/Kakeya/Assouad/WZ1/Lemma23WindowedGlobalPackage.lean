import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23NormalizedVertexBounds
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23YResidueVertexSeparation
import MyLeanRepo.Kakeya.Assouad.WZ1.LocallyLinearOneScale.ShadingRestriction

/-!
# The paper height-window input for the actual WZ1 Lemma 23 cells

WZ1 Lemma 23 starts with a union of `rho`-cubes whose centers have heights in
one interval of length `sqrt rho`.  This is stronger than merely restricting
the shaded points to that interval: a boundary-intersecting cell can have its
center outside the pointwise support interval.

This module records the literal cell-center condition and transports it
through the global-slice, y-residue, actual-tripartite, and normalized
packages.
-/

namespace Kakeya.Assouad

noncomputable section

/--
All active actual `rho`-cell centers lie in one paper height window.
-/
def WZ1Lemma23ActiveCellHeightWindow
    {delta rho : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (hrho : 0 < rho) : Prop :=
  ∃ left : ℝ,
    ∀ idx ∈ wz1Lemma23ActiveCells Y rho hrho,
      (wz1Lemma23SnappedPoint rho idx) (2 : Fin 3) ∈
        Set.Icc left (left + Real.sqrt rho)

/-- Bounded spatial cells whose canonical centers lie in one height window. -/
def wz1Lemma23CellHeightWindow
    (rho : ℝ) (hrho : 0 < rho) (left : ℝ) :
    Finset (ℤ × ℤ × ℤ) :=
  (wz1Lemma23BoundedCells rho hrho).filter fun idx =>
    (wz1Lemma23SnappedPoint rho idx) (2 : Fin 3) ∈
      Set.Icc left (left + Real.sqrt rho)

/-- The measurable union of all bounded cells retained by one height window. -/
def wz1Lemma23CellHeightWindowSet
    (rho : ℝ) (hrho : 0 < rho) (left : ℝ) : Set Point3 :=
  ⋃ idx ∈ wz1Lemma23CellHeightWindow rho hrho left,
    wz1Lemma23Cell rho idx

/-- The finite cell-center window is measurable. -/
lemma wz1Lemma23CellHeightWindowSet_measurable
    (rho : ℝ) (hrho : 0 < rho) (left : ℝ) :
    MeasurableSet (wz1Lemma23CellHeightWindowSet rho hrho left) := by
  exact
    Set.Finite.measurableSet_biUnion
      (wz1Lemma23CellHeightWindow rho hrho left).finite_toSet
      (fun idx _ => wz1Lemma23Cell_measurable hrho idx)

/--
Restrict a shading to complete actual `rho`-cells whose centers lie in one
height window.
-/
def wz1Lemma23RestrictShadingToCellHeightWindow
    {delta rho : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (hrho : 0 < rho) (left : ℝ) :
    Kakeya.Streamlined.TubeShading F :=
  let windowSet :=
    wz1Lemma23CellHeightWindowSet rho hrho left
  { carrier := fun i => Y.carrier i ∩ windowSet
    measurable_carrier := fun i =>
      (Y.measurable_carrier i).inter
        (wz1Lemma23CellHeightWindowSet_measurable
          rho hrho left)
    subset_body := fun i =>
      Set.inter_subset_left.trans (Y.subset_body i) }

/-- The complete-cell height restriction is a subshading. -/
lemma wz1Lemma23RestrictShadingToCellHeightWindow_subshading
    {delta rho : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (hrho : 0 < rho) (left : ℝ) :
    IsSubshading
      (wz1Lemma23RestrictShadingToCellHeightWindow
        Y hrho left)
      Y := by
  intro i
  exact Set.inter_subset_left

/-- Every active restricted cell center lies in the chosen height window. -/
lemma wz1Lemma23RestrictShadingToCellHeightWindow_active_window
    {delta rho : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (hrho : 0 < rho) (left : ℝ) :
    WZ1Lemma23ActiveCellHeightWindow
      (wz1Lemma23RestrictShadingToCellHeightWindow
        Y hrho left)
      hrho := by
  refine ⟨left, ?_⟩
  intro idx hidx
  have hactive :=
    (wz1Lemma23_mem_active_iff
      (wz1Lemma23RestrictShadingToCellHeightWindow
        Y hrho left)
      hrho idx).mp hidx
  rcases hactive.2 with ⟨point, hpoint, hpointCell⟩
  rcases hpoint with ⟨tubeIndex, hpointTube⟩
  have hpointWindow :
      point ∈ wz1Lemma23CellHeightWindowSet rho hrho left :=
    hpointTube.2
  rcases Set.mem_iUnion₂.mp hpointWindow with
    ⟨windowIndex, hwindowIndex, hpointWindowCell⟩
  have hindexEq : windowIndex = idx := by
    have hfirst :
        wz1Lemma23CellIndex rho point = windowIndex :=
      hpointWindowCell
    have hsecond :
        wz1Lemma23CellIndex rho point = idx :=
      hpointCell
    exact hfirst.symm.trans hsecond
  simpa [hindexEq] using
    (Finset.mem_filter.mp hwindowIndex).2

/-- Local grains restrict to the complete-cell height window. -/
def wz1Lemma23RestrictLocalGrainsToCellHeightWindow
    {delta rho sigma : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C : ENNReal}
    (hrho : 0 < rho) (left : ℝ)
    (localGrains : WZ1LocalGrainData Y sigma C) :
    WZ1LocalGrainData
      (wz1Lemma23RestrictShadingToCellHeightWindow
        Y hrho left)
      sigma C :=
  restrictAndWeakenLocalGrains
    (wz1Lemma23RestrictShadingToCellHeightWindow_subshading
      Y hrho left)
    (by rfl)
    localGrains

/-- Global slab AD restricts to the complete-cell height window. -/
lemma wz1Lemma23RestrictGlobalSlabADToCellHeightWindow
    {delta rho sigma : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C : ENNReal} {slope : ℝ → ℝ}
    (hrho : 0 < rho) (left : ℝ)
    (hglobal : HasGlobalSlabAD Y slope sigma C) :
    HasGlobalSlabAD
      (wz1Lemma23RestrictShadingToCellHeightWindow
        Y hrho left)
      slope sigma C :=
  restrictAndWeakenGlobalSlabAD
    (wz1Lemma23RestrictShadingToCellHeightWindow_subshading
      Y hrho left)
    (by rfl)
    hglobal

/-- Any actual-cell subset inherits the source cell-center height window. -/
lemma WZ1Lemma23ActiveCellHeightWindow.subset
    {delta rho : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {hrho : 0 < rho}
    (hwindow : WZ1Lemma23ActiveCellHeightWindow Y hrho)
    {cells : Finset (ℤ × ℤ × ℤ)}
    (hactive :
      cells ⊆ wz1Lemma23ActiveCells Y rho hrho) :
    WZ1Lemma23SingleHeightWindow rho cells := by
  rcases hwindow with ⟨left, hwindow⟩
  exact ⟨left, fun idx hidx => hwindow idx (hactive hidx)⟩

/--
A global-slice package equipped with the literal paper height-window input.
-/
structure WZ1Lemma23WindowedGlobalSlicePackage
    {delta rho sigma : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (C : ENNReal) where
  global :
    WZ1Lemma23GlobalSlicePackage
      (delta := delta) (rho := rho) (sigma := sigma) Y C
  active_height_window :
    WZ1Lemma23ActiveCellHeightWindow Y global.rho_pos

/--
Paper-window constructor from exact-slice global AD.  This is the cropped
counterpart of the historical unit-ball/slab wrapper below.
-/
theorem wz1_lemma23_windowed_global_slice_package_of_exact_paper_window
    {delta rho sigma : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (hrho : 0 < rho)
    (hdelta_rho : delta ≤ rho)
    (hrho_one : rho ≤ 1)
    (hball : Y.union ⊆ Metric.closedBall (0 : Point3) 2)
    (hcoord : ∀ point ∈ Y.union, ∀ coordinate : Fin 3,
      |point coordinate| ≤ 1)
    (sourceSlope : ℝ → ℝ)
    (hsourceLipschitz :
      LipschitzOnWith 1 sourceSlope (Set.Icc (-1 : ℝ) 1))
    (hsourceBounded :
      ∀ z ∈ Set.Icc (-1 : ℝ) 1, |sourceSlope z| ≤ 3)
    (C : ENNReal) (hC : C ≠ ⊤)
    (hglobal : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      IsADSet1
        (scalarProjection (globalGrainDirection (sourceSlope z))
          (horizontalSlice Y.union z))
        delta (1 - sigma) C)
    (left : ℝ) :
    ∃ windowedShading : Kakeya.Streamlined.TubeShading F,
      ∃ package :
          WZ1Lemma23WindowedGlobalSlicePackage
            (delta := delta) (rho := rho) (sigma := sigma)
            windowedShading C,
        windowedShading =
            wz1Lemma23RestrictShadingToCellHeightWindow Y hrho left ∧
          IsSubshading windowedShading Y ∧
          package.global.sourceSlope = sourceSlope := by
  let windowedShading :=
    wz1Lemma23RestrictShadingToCellHeightWindow Y hrho left
  have hsub : IsSubshading windowedShading Y :=
    wz1Lemma23RestrictShadingToCellHeightWindow_subshading Y hrho left
  have hunionSub : windowedShading.union ⊆ Y.union := by
    rintro point ⟨index, hpoint⟩
    exact ⟨index, hsub index hpoint⟩
  have hwindowBall :
      windowedShading.union ⊆ Metric.closedBall (0 : Point3) 2 :=
    hunionSub.trans hball
  have hwindowCoord :
      ∀ point ∈ windowedShading.union, ∀ coordinate : Fin 3,
        |point coordinate| ≤ 1 := by
    intro point hpoint coordinate
    exact hcoord point (hunionSub hpoint) coordinate
  have hwindowGlobal : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      IsADSet1
        (scalarProjection (globalGrainDirection (sourceSlope z))
          (horizontalSlice windowedShading.union z))
        delta (1 - sigma) C := by
    intro z hz
    apply (hglobal z hz).mono
    rintro value ⟨point, hpoint, rfl⟩
    exact ⟨point, ⟨hunionSub hpoint.1, hpoint.2⟩, rfl⟩
  rcases
      wz1_lemma23_global_slice_package_of_exact_paper_window
        windowedShading hrho hdelta_rho hrho_one
        hwindowBall hwindowCoord sourceSlope
        hsourceLipschitz hsourceBounded C hC hwindowGlobal with
    ⟨globalPackage, hsourceEq⟩
  let package :
      WZ1Lemma23WindowedGlobalSlicePackage
        (delta := delta) (rho := rho) (sigma := sigma)
        windowedShading C :=
    { global := globalPackage
      active_height_window :=
        wz1Lemma23RestrictShadingToCellHeightWindow_active_window
          Y hrho left }
  exact ⟨windowedShading, package, rfl, hsub,
    by simpa [package] using hsourceEq⟩

/--
Construct the actual windowed global-slice package from a source shading by
retaining complete `rho`-cells whose centers lie in the prescribed paper
height window.
-/
theorem wz1_lemma23_windowed_global_slice_package
    {delta rho sigma : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (hrho : 0 < rho)
    (hdelta_rho : delta ≤ rho)
    (hrho_one : rho ≤ 1)
    (hball : Y.union ⊆ Metric.closedBall (0 : Point3) 1)
    (sourceSlope : ℝ → ℝ)
    (hsourceLipschitz :
      LipschitzOnWith 1 sourceSlope (Set.Icc (-1 : ℝ) 1))
    (hsourceBounded :
      ∀ z ∈ Set.Icc (-1 : ℝ) 1, |sourceSlope z| ≤ 3)
    (C : ENNReal) (hC : C ≠ ⊤)
    (hglobal : HasGlobalSlabAD Y sourceSlope sigma C)
    (left : ℝ) :
    ∃ windowedShading :
        Kakeya.Streamlined.TubeShading F,
      ∃ package :
          WZ1Lemma23WindowedGlobalSlicePackage
            (delta := delta) (rho := rho) (sigma := sigma)
            windowedShading C,
        windowedShading =
            wz1Lemma23RestrictShadingToCellHeightWindow
              Y hrho left ∧
          IsSubshading windowedShading Y ∧
          package.global.sourceSlope = sourceSlope := by
  let windowedShading :=
    wz1Lemma23RestrictShadingToCellHeightWindow
      Y hrho left
  have hsub : IsSubshading windowedShading Y :=
    wz1Lemma23RestrictShadingToCellHeightWindow_subshading
      Y hrho left
  have hwindowBall :
      windowedShading.union ⊆
        Metric.closedBall (0 : Point3) 1 :=
    (by
      rintro point ⟨tubeIndex, hpoint⟩
      exact hball ⟨tubeIndex, hsub tubeIndex hpoint⟩)
  have hwindowGlobal :
      HasGlobalSlabAD
        windowedShading sourceSlope sigma C :=
    wz1Lemma23RestrictGlobalSlabADToCellHeightWindow
      hrho left hglobal
  rcases
      wz1_lemma23_global_slice_package
        windowedShading hrho hdelta_rho hrho_one
        hwindowBall sourceSlope hsourceLipschitz
        hsourceBounded C hC hwindowGlobal with
    ⟨globalPackage, hsourceEq⟩
  let package :
      WZ1Lemma23WindowedGlobalSlicePackage
        (delta := delta) (rho := rho) (sigma := sigma)
        windowedShading C :=
    { global := globalPackage
      active_height_window :=
        wz1Lemma23RestrictShadingToCellHeightWindow_active_window
          Y hrho left }
  exact
    ⟨windowedShading, package, rfl, hsub,
      by simpa [package] using hsourceEq⟩

namespace WZ1Lemma23WindowedGlobalSlicePackage

/-- The genuine global-slice cells lie in the paper height window. -/
lemma global_cells_window
    {delta rho sigma : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C : ENNReal}
    (package :
      WZ1Lemma23WindowedGlobalSlicePackage
        (delta := delta) (rho := rho) (sigma := sigma) Y C) :
    WZ1Lemma23SingleHeightWindow rho package.global.cells :=
  package.active_height_window.subset package.global.cells_active

/-- Every y-residue subset lies in the same paper height window. -/
lemma residue_cells_window
    {delta rho sigma : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C : ENNReal}
    (package :
      WZ1Lemma23WindowedGlobalSlicePackage
        (delta := delta) (rho := rho) (sigma := sigma) Y C)
    (residuePackage :
      WZ1Lemma23YResiduePackage package.global) :
    WZ1Lemma23SingleHeightWindow rho residuePackage.cells :=
  package.active_height_window.subset residuePackage.cells_active

end WZ1Lemma23WindowedGlobalSlicePackage

/--
The actual normalized graph on windowed y-residue cells has fixed vertex
bounds.  These are the direct boundedness conclusions before the final common
rescaling to the unit ball.
-/
theorem WZ1Lemma23YResiduePreparedPackage.vertex_bounds
    {delta rho sigma : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C : ENNReal}
    (hrho_one : rho ≤ 1)
    (hball : Y.union ⊆ Metric.closedBall (0 : Point3) 1)
    {windowed :
      WZ1Lemma23WindowedGlobalSlicePackage
        (delta := delta) (rho := rho) (sigma := sigma) Y C}
    {residuePackage :
      WZ1Lemma23YResiduePackage windowed.global}
    {localPackage :
      WZ1Lemma23LocalBinPackage
        (rho := rho) (sigma := sigma) C windowed.global.cells}
    (package :
      WZ1Lemma23YResiduePreparedPackage
        windowed.global residuePackage localPackage) :
    (∀ point ∈ package.prepared.normalized.F,
        dist point 0 ≤ 2) ∧
      (∀ point ∈ package.prepared.normalized.G₁,
        dist point 0 ≤ 5) ∧
      ∀ point ∈ package.prepared.normalized.G₂,
        dist point 0 ≤ 5 := by
  have h :=
    package.prepared.actual.vertex_bounds
      windowed.global.rho_pos hrho_one hball
      windowed.global.extendedSlope_lipschitz
      package.selectedLocal.g_bounded
      residuePackage.cells_active
      (windowed.residue_cells_window residuePackage)
  rw [package.prepared.normalized.F_eq,
    package.prepared.normalized.G₁_eq,
    package.prepared.normalized.G₂_eq,
    package.prepared.normalized_sourceF,
    package.prepared.normalized_sourceG₁,
    package.prepared.normalized_sourceG₂]
  exact h

/-- Paper-crop variant of the normalized vertex bounds. -/
theorem WZ1Lemma23YResiduePreparedPackage.vertex_bounds_of_coord
    {delta rho sigma : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C : ENNReal}
    (hrho_one : rho ≤ 1)
    (hcoord : ∀ point ∈ Y.union, ∀ i : Fin 3, |point i| ≤ 1)
    {windowed :
      WZ1Lemma23WindowedGlobalSlicePackage
        (delta := delta) (rho := rho) (sigma := sigma) Y C}
    {residuePackage :
      WZ1Lemma23YResiduePackage windowed.global}
    {localPackage :
      WZ1Lemma23LocalBinPackage
        (rho := rho) (sigma := sigma) C windowed.global.cells}
    (package :
      WZ1Lemma23YResiduePreparedPackage
        windowed.global residuePackage localPackage) :
    (∀ point ∈ package.prepared.normalized.F, dist point 0 ≤ 2) ∧
      (∀ point ∈ package.prepared.normalized.G₁, dist point 0 ≤ 5) ∧
      ∀ point ∈ package.prepared.normalized.G₂, dist point 0 ≤ 5 := by
  have h :=
    package.prepared.actual.vertex_bounds_of_coord
      windowed.global.rho_pos hrho_one hcoord
      windowed.global.extendedSlope_lipschitz
      package.selectedLocal.g_bounded
      residuePackage.cells_active
      (windowed.residue_cells_window residuePackage)
  rw [package.prepared.normalized.F_eq,
    package.prepared.normalized.G₁_eq,
    package.prepared.normalized.G₂_eq,
    package.prepared.normalized_sourceF,
    package.prepared.normalized_sourceG₁,
    package.prepared.normalized_sourceG₂]
  exact h

end

end Kakeya.Assouad
