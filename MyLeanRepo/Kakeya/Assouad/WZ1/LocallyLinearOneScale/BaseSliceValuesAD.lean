import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23GlobalSlicePackage
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23ExactSliceGlobalBins
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23ActualEdgeDotContainmentStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.GeneralizedThickening
import MyLeanRepo.Kakeya.Assouad.WZ1.TransportNormalizeAD

/-!
# AD bound for snapped base-slice values

The snapped base-slice values at one height are within `4 * rho` of the
exact-slice scalar projection, which has AD from the global slab certificate.
Thickening transfer then gives AD for the base-slice values.
-/

namespace Kakeya.Assouad

open Metric Set

/--
AD for the untranslated snapped base-slice values (intersected with [-4,4]).

Proof outline:
1. Let z = selectedHeight baseHeightIndex
2. E = scalar projection of horizontal slice at z has IsADSet1 from global slab AD
3. Coarsen E from scale delta to rho
4. Each base value (global coord of cell center) is within 4*rho of some point in E
   (snapped cell geometry + exact slice representative)
5. Therefore baseValues ⊆ cthickening (4*rho) E
6. Apply generalized_thickening: IsADSet1 (baseValues ∩ [-4,4]) rho (1-sigma) (100*C)
-/
lemma base_slice_values_AD_of_coord
    {delta rho sigma : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C : ENNReal}
    (globalPackage : WZ1Lemma23GlobalSlicePackage
      (delta := delta) (rho := rho) (sigma := sigma) Y C)
    (hglobal : HasGlobalSlabAD Y globalPackage.sourceSlope sigma C)
    (cells : Finset (ℤ × ℤ × ℤ))
    (hcells : cells ⊆ globalPackage.cells)
    (baseHeightIndex : ℤ)
    (hcoord : ∀ point ∈ Y.union, ∀ coordinate : Fin 3,
      |point coordinate| ≤ 1)
    (hdelta_rho : delta ≤ rho)
    (hrho_pos : 0 < rho)
    (hrho_one : rho ≤ 1)
    (hbaseHeightIndex : baseHeightIndex ∈ wz1Lemma23SnappedHeights cells) :
    IsADSet1
      (((cells.filter fun idx => wz1Lemma23SnappedHeight idx = baseHeightIndex).image
          fun idx => wz1Lemma23GlobalCoordinate globalPackage.extendedSlope
            (wz1Lemma23SnappedPoint rho idx) : Set ℝ) ∩
        Set.Icc (-4 : ℝ) 4)
      rho (1 - sigma) (100 * C) := by
  classical
  let z : ℝ := globalPackage.selectedHeight baseHeightIndex
  -- Step 1: z ∈ [-1,1] (needed for exactSlice)
  have hz_mem : z ∈ Set.Icc (-1 : ℝ) 1 := by
    rcases Finset.mem_image.mp hbaseHeightIndex with ⟨idx, hidx, h_idx_height⟩
    have hidx_global : idx ∈ globalPackage.cells := hcells hidx
    have h_in_bunion : idx ∈ Finset.biUnion globalPackage.heightIndices globalPackage.layerCells := by
      rw [globalPackage.cells_eq] at hidx_global; exact hidx_global
    rcases Finset.mem_biUnion.mp h_in_bunion with ⟨h, hh, hidxLayer⟩
    have hheight : idx.2.2 = h := globalPackage.layer_height h hh idx hidxLayer
    have h_eq : h = baseHeightIndex := by
      have h1 : idx.2.2 = baseHeightIndex := by
        simpa [wz1Lemma23SnappedHeight] using h_idx_height
      linarith
    have h_idx_in_layer : idx ∈ globalPackage.layerCells baseHeightIndex := by
      rw [h_eq] at hidxLayer; exact hidxLayer
    have h_idx_exact : idx ∈ wz1Lemma23ExactSliceCells Y rho hrho_pos z := by
      rw [globalPackage.layerCells_eq] at h_idx_in_layer; exact h_idx_in_layer
    let cell : WZ1Lemma23ExactSliceCell Y rho hrho_pos z := ⟨idx, h_idx_exact⟩
    let rep2 := wz1Lemma23ExactSliceRepresentative Y hrho_pos z cell
    let rep : Point3 := wz1Lemma23LiftSlicePoint z rep2
    have hrep_union : rep ∈ Y.union :=
      wz1Lemma23ExactSliceRepresentative_mem_union Y hrho_pos z cell
    have hrep_z : rep (2 : Fin 3) = z := by
      simp [rep, rep2, wz1Lemma23LiftSlicePoint, point3]
    have h : |rep (2 : Fin 3)| ≤ 1 :=
      hcoord rep hrep_union (2 : Fin 3)
    rw [hrep_z] at h
    have h' : -1 ≤ z ∧ z ≤ 1 := abs_le.mp h
    exact ⟨h'.1, h'.2⟩
  -- Step 2: E has AD at scale delta
  let E : Set ℝ :=
    scalarProjection
      (globalGrainDirection (globalPackage.sourceSlope z))
      (horizontalSlice Y.union z)
  have hAD_delta : IsADSet1 E delta (1 - sigma) C :=
    hglobal.exactSlice z hz_mem
  -- Step 3: Coarsen to scale rho
  have hAD_rho : IsADSet1 E rho (1 - sigma) C :=
    hAD_delta.coarsen_scale hrho_pos hdelta_rho hrho_one
  let filteredCells : Finset (ℤ × ℤ × ℤ) :=
    cells.filter fun idx => wz1Lemma23SnappedHeight idx = baseHeightIndex
  let baseValues : Finset ℝ :=
    filteredCells.image fun idx =>
      wz1Lemma23GlobalCoordinate globalPackage.extendedSlope
        (wz1Lemma23SnappedPoint rho idx)
  -- Step 4: Each base value is within 4*rho of E
  -- This uses snapped cell geometry: |globalCoord(cellCenter) - globalCoord(rep)| ≤ 4*rho
  -- and globalCoord(rep) = inner rep (globalGrainDirection (sourceSlope z)) ∈ E
  have hclose :
      ∀ value ∈ baseValues, ∃ sourceValue ∈ E, |value - sourceValue| ≤ 4 * rho := by
    intro value hvalue
    rcases Finset.mem_image.mp hvalue with ⟨idx, hidx, rfl⟩
    have h_idx_in_layer : idx ∈ globalPackage.layerCells baseHeightIndex := by
      have h_idx_in_cells : idx ∈ cells := (Finset.mem_filter.mp hidx).1
      have h_idx_height : wz1Lemma23SnappedHeight idx = baseHeightIndex :=
        (Finset.mem_filter.mp hidx).2
      have h_idx_global : idx ∈ globalPackage.cells := hcells h_idx_in_cells
      have h_in_bunion : idx ∈ Finset.biUnion globalPackage.heightIndices globalPackage.layerCells := by
        rw [globalPackage.cells_eq] at h_idx_global; exact h_idx_global
      rcases Finset.mem_biUnion.mp h_in_bunion with ⟨h, hh, hidxLayer⟩
      have hheight : idx.2.2 = h := globalPackage.layer_height h hh idx hidxLayer
      have h1 : idx.2.2 = baseHeightIndex := by
        simpa [wz1Lemma23SnappedHeight] using h_idx_height
      have h_eq : h = baseHeightIndex := hheight.symm.trans h1
      rw [h_eq] at hidxLayer
      exact hidxLayer
    let cell : WZ1Lemma23ExactSliceCell Y rho hrho_pos z :=
      ⟨idx, by rw [globalPackage.layerCells_eq] at h_idx_in_layer; exact h_idx_in_layer⟩
    let sourceRepresentative :=
      wz1Lemma23ExactSliceRepresentative Y hrho_pos z cell
    let sourcePoint :=
      wz1Lemma23LiftSlicePoint z sourceRepresentative
    have hsourcePointUnion : sourcePoint ∈ Y.union :=
      wz1Lemma23ExactSliceRepresentative_mem_union Y hrho_pos z cell
    let sourceValue :=
      inner ℝ sourcePoint
        (globalGrainDirection (globalPackage.sourceSlope z))
    have hsourcePointHeight : sourcePoint (2 : Fin 3) = z := by
      simp [sourcePoint, wz1Lemma23LiftSlicePoint, point3]
    have hsourceHorizontal : sourcePoint ∈ horizontalSlice Y.union z :=
      ⟨hsourcePointUnion, hsourcePointHeight⟩
    have hsourceValueMem : sourceValue ∈ E :=
      ⟨sourcePoint, hsourceHorizontal, rfl⟩
    have hsnap :=
      wz1Lemma23_globalCoordinate_snap_of_coord_bound
        hrho_pos hrho_one globalPackage.extendedSlope
        globalPackage.extendedSlope_lipschitz
        globalPackage.extendedSlope_bounded sourcePoint
        (hcoord sourcePoint hsourcePointUnion)
    have hsourceIndex :
        wz1Lemma23CellIndex rho sourcePoint = idx :=
      wz1Lemma23ExactSliceRepresentative_index Y hrho_pos z cell
    have hsnapEq :
        wz1Lemma23Snap rho sourcePoint = wz1Lemma23CellCenter rho idx := by
      simp [wz1Lemma23Snap, hsourceIndex]
    have hsourceCoord :
        wz1Lemma23GlobalCoordinate globalPackage.extendedSlope sourcePoint =
          sourceValue := by
      calc
        wz1Lemma23GlobalCoordinate globalPackage.extendedSlope sourcePoint
          = inner ℝ sourcePoint
              (globalGrainDirection (globalPackage.extendedSlope z)) := by
          simp [wz1Lemma23GlobalCoordinate, sourcePoint, sourceRepresentative,
            wz1Lemma23LiftSlicePoint, globalGrainDirection, point3,
            PiLp.inner_apply, Fin.sum_univ_succ]
        _ = sourceValue := by
          have heq : globalPackage.extendedSlope z = globalPackage.sourceSlope z :=
            globalPackage.extendedSlope_eq z hz_mem
          rw [heq]
    refine ⟨sourceValue, hsourceValueMem, ?_⟩
    have h_snap_point : wz1Lemma23SnappedPoint rho idx = wz1Lemma23CellCenter rho idx := by
      rfl
    rw [h_snap_point, ← hsnapEq, ← hsourceCoord]
    simpa [abs_sub_comm] using hsnap
  -- Step 5: baseValues ⊆ cthickening (4*rho) E
  have hthick : (baseValues : Set ℝ) ⊆ Metric.cthickening (4 * rho) E := by
    intro value hvalue
    rcases hclose value hvalue with ⟨sourceValue, hsourceMem, hdist⟩
    have h1 : infEDist value E ≤ edist value sourceValue :=
      Metric.infEDist_le_edist_of_mem hsourceMem
    have h2 : edist value sourceValue = ENNReal.ofReal (|value - sourceValue|) := by
      simp [edist_dist, Real.dist_eq]
    have h3 : infEDist value E ≤ ENNReal.ofReal (4 * rho) := by
      rw [h2] at h1
      have h4 : ENNReal.ofReal (|value - sourceValue|) ≤ ENNReal.ofReal (4 * rho) :=
        ENNReal.ofReal_le_ofReal hdist
      exact h1.trans h4
    exact h3
  let B : Set ℝ := (baseValues : Set ℝ) ∩ Set.Icc (-4 : ℝ) 4
  have hB_bounded : B ⊆ Set.Icc (-4 : ℝ) 4 := by
    intro x hx; exact hx.2
  have hB_thick : B ⊆ Metric.cthickening (4 * rho) E := by
    intro x hx; exact hthick hx.1
  have h4rho_pos : 0 < 4 * rho := by positivity
  -- Step 6: Thickening transfer gives AD for B
  have h_const_eq :
      (2 * (Nat.ceil ((4 * rho) / rho) + 1) : ENNReal) ^ 2 * C = (100 : ENNReal) * C := by
    have h1 : (4 * rho) / rho = 4 := by
      field_simp [hrho_pos.ne']
    rw [h1]
    have h2 : Nat.ceil (4 : ℝ) = 4 := by
      rw [Nat.ceil_eq_iff] <;> norm_num
    rw [h2]
    <;> norm_cast
  have hAD_B : IsADSet1 B rho (1 - sigma) (100 * C) := by
    rw [← h_const_eq]
    exact hAD_rho.generalized_thickening hB_thick hB_bounded hrho_pos h4rho_pos
  exact hAD_B

/-- Historical unit-ball wrapper for the coordinate-crop base-value AD bound. -/
lemma base_slice_values_AD
    {delta rho sigma : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C : ENNReal}
    (globalPackage : WZ1Lemma23GlobalSlicePackage
      (delta := delta) (rho := rho) (sigma := sigma) Y C)
    (hglobal : HasGlobalSlabAD Y globalPackage.sourceSlope sigma C)
    (cells : Finset (ℤ × ℤ × ℤ))
    (hcells : cells ⊆ globalPackage.cells)
    (baseHeightIndex : ℤ)
    (hball : Y.union ⊆ Metric.closedBall (0 : Point3) 1)
    (hdelta_rho : delta ≤ rho)
    (hrho_pos : 0 < rho)
    (hrho_one : rho ≤ 1)
    (hbaseHeightIndex : baseHeightIndex ∈ wz1Lemma23SnappedHeights cells) :
    IsADSet1
      (((cells.filter fun idx => wz1Lemma23SnappedHeight idx = baseHeightIndex).image
          fun idx => wz1Lemma23GlobalCoordinate globalPackage.extendedSlope
            (wz1Lemma23SnappedPoint rho idx) : Set ℝ) ∩
        Set.Icc (-4 : ℝ) 4)
      rho (1 - sigma) (100 * C) := by
  apply base_slice_values_AD_of_coord globalPackage hglobal cells hcells
    baseHeightIndex _ hdelta_rho hrho_pos hrho_one hbaseHeightIndex
  intro point hpoint coordinate
  have hnorm : ‖point‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hball hpoint
  exact (PiLp.norm_apply_le point coordinate).trans hnorm

/--
Containment: snapped base-slice values lie within `4*rho` of the exact-slice
scalar projection `E`.

This is the geometric core of `base_slice_values_AD`, exposed separately for
downstream consumers that need to combine it with different AD transfers.
-/
lemma base_slice_values_containment_of_coord
    {delta rho sigma : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C : ENNReal}
    (globalPackage : WZ1Lemma23GlobalSlicePackage
      (delta := delta) (rho := rho) (sigma := sigma) Y C)
    (cells : Finset (ℤ × ℤ × ℤ))
    (hcells : cells ⊆ globalPackage.cells)
    (baseHeightIndex : ℤ)
    (hcoord : ∀ point ∈ Y.union, ∀ coordinate : Fin 3,
      |point coordinate| ≤ 1)
    (hrho_pos : 0 < rho)
    (hrho_one : rho ≤ 1)
    (hbaseHeightIndex : baseHeightIndex ∈ wz1Lemma23SnappedHeights cells) :
    (let z : ℝ := globalPackage.selectedHeight baseHeightIndex
     let E : Set ℝ :=
       scalarProjection
         (globalGrainDirection (globalPackage.sourceSlope z))
         (horizontalSlice Y.union z)
     let baseValues : Finset ℝ :=
       (cells.filter fun idx => wz1Lemma23SnappedHeight idx = baseHeightIndex).image
         fun idx => wz1Lemma23GlobalCoordinate globalPackage.extendedSlope
           (wz1Lemma23SnappedPoint rho idx)
     (baseValues : Set ℝ) ⊆ Metric.cthickening (4 * rho) E) := by
  dsimp only
  let z : ℝ := globalPackage.selectedHeight baseHeightIndex
  let E : Set ℝ :=
    scalarProjection
      (globalGrainDirection (globalPackage.sourceSlope z))
      (horizontalSlice Y.union z)
  let filteredCells : Finset (ℤ × ℤ × ℤ) :=
    cells.filter fun idx => wz1Lemma23SnappedHeight idx = baseHeightIndex
  let baseValues : Finset ℝ :=
    filteredCells.image fun idx =>
      wz1Lemma23GlobalCoordinate globalPackage.extendedSlope
        (wz1Lemma23SnappedPoint rho idx)
  have hz_mem : z ∈ Set.Icc (-1 : ℝ) 1 := by
    rcases Finset.mem_image.mp hbaseHeightIndex with ⟨idx, hidx, h_idx_height⟩
    have hidx_global : idx ∈ globalPackage.cells := hcells hidx
    have h_in_bunion : idx ∈ Finset.biUnion globalPackage.heightIndices globalPackage.layerCells := by
      rw [globalPackage.cells_eq] at hidx_global; exact hidx_global
    rcases Finset.mem_biUnion.mp h_in_bunion with ⟨h, hh, hidxLayer⟩
    have hheight : idx.2.2 = h := globalPackage.layer_height h hh idx hidxLayer
    have h_eq : h = baseHeightIndex := by
      have h1 : idx.2.2 = baseHeightIndex := by
        simpa [wz1Lemma23SnappedHeight] using h_idx_height
      linarith
    have h_idx_in_layer : idx ∈ globalPackage.layerCells baseHeightIndex := by
      rw [h_eq] at hidxLayer; exact hidxLayer
    have h_idx_exact : idx ∈ wz1Lemma23ExactSliceCells Y rho hrho_pos z := by
      rw [globalPackage.layerCells_eq] at h_idx_in_layer; exact h_idx_in_layer
    let cell : WZ1Lemma23ExactSliceCell Y rho hrho_pos z := ⟨idx, h_idx_exact⟩
    let rep2 := wz1Lemma23ExactSliceRepresentative Y hrho_pos z cell
    let rep : Point3 := wz1Lemma23LiftSlicePoint z rep2
    have hrep_union : rep ∈ Y.union :=
      wz1Lemma23ExactSliceRepresentative_mem_union Y hrho_pos z cell
    have hrep_z : rep (2 : Fin 3) = z := by
      simp [rep, rep2, wz1Lemma23LiftSlicePoint, point3]
    have h : |rep (2 : Fin 3)| ≤ 1 :=
      hcoord rep hrep_union (2 : Fin 3)
    rw [hrep_z] at h
    have h' : -1 ≤ z ∧ z ≤ 1 := abs_le.mp h
    exact ⟨h'.1, h'.2⟩
  have hclose :
      ∀ value ∈ baseValues, ∃ sourceValue ∈ E, |value - sourceValue| ≤ 4 * rho := by
    intro value hvalue
    rcases Finset.mem_image.mp hvalue with ⟨idx, hidx, rfl⟩
    have h_idx_in_layer : idx ∈ globalPackage.layerCells baseHeightIndex := by
      have h_idx_in_cells : idx ∈ cells := (Finset.mem_filter.mp hidx).1
      have h_idx_height : wz1Lemma23SnappedHeight idx = baseHeightIndex :=
        (Finset.mem_filter.mp hidx).2
      have h_idx_global : idx ∈ globalPackage.cells := hcells h_idx_in_cells
      have h_in_bunion : idx ∈ Finset.biUnion globalPackage.heightIndices globalPackage.layerCells := by
        rw [globalPackage.cells_eq] at h_idx_global; exact h_idx_global
      rcases Finset.mem_biUnion.mp h_in_bunion with ⟨h, hh, hidxLayer⟩
      have hheight : idx.2.2 = h := globalPackage.layer_height h hh idx hidxLayer
      have h1 : idx.2.2 = baseHeightIndex := by
        simpa [wz1Lemma23SnappedHeight] using h_idx_height
      have h_eq : h = baseHeightIndex := hheight.symm.trans h1
      rw [h_eq] at hidxLayer
      exact hidxLayer
    let cell : WZ1Lemma23ExactSliceCell Y rho hrho_pos z :=
      ⟨idx, by rw [globalPackage.layerCells_eq] at h_idx_in_layer; exact h_idx_in_layer⟩
    let sourceRepresentative :=
      wz1Lemma23ExactSliceRepresentative Y hrho_pos z cell
    let sourcePoint :=
      wz1Lemma23LiftSlicePoint z sourceRepresentative
    have hsourcePointUnion : sourcePoint ∈ Y.union :=
      wz1Lemma23ExactSliceRepresentative_mem_union Y hrho_pos z cell
    let sourceValue :=
      inner ℝ sourcePoint
        (globalGrainDirection (globalPackage.sourceSlope z))
    have hsourcePointHeight : sourcePoint (2 : Fin 3) = z := by
      simp [sourcePoint, wz1Lemma23LiftSlicePoint, point3]
    have hsourceHorizontal : sourcePoint ∈ horizontalSlice Y.union z :=
      ⟨hsourcePointUnion, hsourcePointHeight⟩
    have hsourceValueMem : sourceValue ∈ E :=
      ⟨sourcePoint, hsourceHorizontal, rfl⟩
    have hsnap :=
      wz1Lemma23_globalCoordinate_snap_of_coord_bound
        hrho_pos hrho_one globalPackage.extendedSlope
        globalPackage.extendedSlope_lipschitz
        globalPackage.extendedSlope_bounded sourcePoint
        (hcoord sourcePoint hsourcePointUnion)
    have hsourceIndex :
        wz1Lemma23CellIndex rho sourcePoint = idx :=
      wz1Lemma23ExactSliceRepresentative_index Y hrho_pos z cell
    have hsnapEq :
        wz1Lemma23Snap rho sourcePoint = wz1Lemma23CellCenter rho idx := by
      simp [wz1Lemma23Snap, hsourceIndex]
    have hsourceCoord :
        wz1Lemma23GlobalCoordinate globalPackage.extendedSlope sourcePoint =
          sourceValue := by
      calc
        wz1Lemma23GlobalCoordinate globalPackage.extendedSlope sourcePoint
          = inner ℝ sourcePoint
              (globalGrainDirection (globalPackage.extendedSlope z)) := by
          simp [wz1Lemma23GlobalCoordinate, sourcePoint, sourceRepresentative,
            wz1Lemma23LiftSlicePoint, globalGrainDirection, point3,
            PiLp.inner_apply, Fin.sum_univ_succ]
        _ = sourceValue := by
          have heq : globalPackage.extendedSlope z = globalPackage.sourceSlope z :=
            globalPackage.extendedSlope_eq z hz_mem
          rw [heq]
    refine ⟨sourceValue, hsourceValueMem, ?_⟩
    have h_snap_point : wz1Lemma23SnappedPoint rho idx = wz1Lemma23CellCenter rho idx := by rfl
    rw [h_snap_point, ← hsnapEq, ← hsourceCoord]
    simpa [abs_sub_comm] using hsnap
  intro value hvalue
  rcases hclose value hvalue with ⟨sourceValue, hsourceMem, hdist⟩
  have h1 : infEDist value E ≤ edist value sourceValue :=
    Metric.infEDist_le_edist_of_mem hsourceMem
  have h2 : edist value sourceValue = ENNReal.ofReal (|value - sourceValue|) := by
    simp [edist_dist, Real.dist_eq]
  have h3 : infEDist value E ≤ ENNReal.ofReal (4 * rho) := by
    rw [h2] at h1
    have h4 : ENNReal.ofReal (|value - sourceValue|) ≤ ENNReal.ofReal (4 * rho) :=
      ENNReal.ofReal_le_ofReal hdist
    exact h1.trans h4
  exact h3

/-- Historical unit-ball wrapper for base-slice containment. -/
lemma base_slice_values_containment
    {delta rho sigma : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C : ENNReal}
    (globalPackage : WZ1Lemma23GlobalSlicePackage
      (delta := delta) (rho := rho) (sigma := sigma) Y C)
    (cells : Finset (ℤ × ℤ × ℤ))
    (hcells : cells ⊆ globalPackage.cells)
    (baseHeightIndex : ℤ)
    (hball : Y.union ⊆ Metric.closedBall (0 : Point3) 1)
    (hrho_pos : 0 < rho)
    (hrho_one : rho ≤ 1)
    (hbaseHeightIndex : baseHeightIndex ∈ wz1Lemma23SnappedHeights cells) :
    (let z : ℝ := globalPackage.selectedHeight baseHeightIndex
     let E : Set ℝ :=
       scalarProjection
         (globalGrainDirection (globalPackage.sourceSlope z))
         (horizontalSlice Y.union z)
     let baseValues : Finset ℝ :=
       (cells.filter fun idx => wz1Lemma23SnappedHeight idx = baseHeightIndex).image
         fun idx => wz1Lemma23GlobalCoordinate globalPackage.extendedSlope
           (wz1Lemma23SnappedPoint rho idx)
     (baseValues : Set ℝ) ⊆ Metric.cthickening (4 * rho) E) := by
  apply base_slice_values_containment_of_coord globalPackage cells hcells
    baseHeightIndex _ hrho_pos hrho_one hbaseHeightIndex
  intro point hpoint coordinate
  have hnorm : ‖point‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hball hpoint
  exact (PiLp.norm_apply_le point coordinate).trans hnorm

end Kakeya.Assouad
