import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23ExactSliceGlobalBins

/-!
# Global-slice package for the actual WZ1 Lemma 23 cell graph

This module combines:

* genuine per-height slice popularity;
* a globally bounded one-Lipschitz slope extension;
* the exact-slice global AD certificate; and
* the perturbed snapped-bin count.

The result is the actual multi-height cell family together with the uniform
natural-number global-bin bound consumed by the closed four-cycle theorem.
-/

namespace Kakeya.Assouad

noncomputable section

open MeasureTheory

private lemma wz1Lemma23_nat_le_ceil_add_one
    {n : ℕ} {X : ENNReal} (hX : X ≠ ⊤)
    (hn : (n : ENNReal) ≤ X) :
    n ≤ Nat.ceil X.toReal + 1 := by
  have hreal : (n : ℝ) ≤ X.toReal := by
    rw [← ENNReal.toReal_natCast n]
    exact
      (ENNReal.toReal_le_toReal
        (ENNReal.natCast_ne_top n) hX).mpr hn
  have hceil :
      n ≤ Nat.ceil X.toReal := by
    exact_mod_cast hreal.trans (Nat.le_ceil X.toReal)
  omega

/--
The actual cell family prepared for the global half of Lemma 23 Step 3.
-/
structure WZ1Lemma23GlobalSlicePackage
    {delta rho sigma : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (C : ENNReal) where
  rho_pos : 0 < rho
  sourceSlope : ℝ → ℝ
  extendedSlope : ℝ → ℝ
  extendedSlope_lipschitz :
    LipschitzOnWith 1 extendedSlope Set.univ
  extendedSlope_bounded :
    ∀ z, |extendedSlope z| ≤ 3
  extendedSlope_eq :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      extendedSlope z = sourceSlope z
  selectedHeight : ℤ → ℝ
  heightIndices : Finset ℤ
  cells : Finset (ℤ × ℤ × ℤ)
  layerCells : ℤ → Finset (ℤ × ℤ × ℤ)
  heightIndices_eq :
    heightIndices =
      wz1Lemma23BoundedHeightIndices rho rho_pos
  layerCells_eq :
    ∀ heightIndex,
      layerCells heightIndex =
        wz1Lemma23ExactSliceCells
          Y rho rho_pos (selectedHeight heightIndex)
  cells_eq :
    cells = heightIndices.biUnion layerCells
  selectedHeight_mem :
    ∀ heightIndex ∈ heightIndices,
      selectedHeight heightIndex ∈
        wz1Lemma23HeightInterval rho heightIndex
  layer_volume_bound :
    ∀ heightIndex ∈ heightIndices,
      volume (Y.union ∩
          wz1Lemma23HeightSlab rho heightIndex) /
            ENNReal.ofReal (gridSide (rho / 2)) ≤
        volume
          (wz1Lemma23PlanarSlice Y.union
            (selectedHeight heightIndex))
  cells_active :
    cells ⊆ wz1Lemma23ActiveCells Y rho rho_pos
  volume_cell_bound :
    volume Y.union ≤
      (cells.card : ENNReal) *
        ENNReal.ofReal (gridSide (rho / 2)) *
        (ENNReal.ofReal rho ^ 2 * ENNReal.ofReal Real.pi)
  layer_height :
    ∀ heightIndex ∈ heightIndices,
      ∀ idx ∈ layerCells heightIndex,
        idx.2.2 = heightIndex
  globalBinBound : ℕ
  globalBinBound_eq :
    globalBinBound =
      Nat.ceil
        (132 * C *
          Kakeya.realRpowENN (1 / rho) (1 - sigma)).toReal + 1
  global_bins :
    ∀ heightIndex ∈ wz1Lemma23SnappedHeights cells,
      (wz1Lemma23SnappedGlobalBinsAt
        rho extendedSlope cells heightIndex).card ≤
          globalBinBound

/--
Construct the actual global-slice package from the final Proposition 9
shading and its exact-slice global AD certificate.
-/
theorem wz1_lemma23_global_slice_package_of_exact_paper_window
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
        delta (1 - sigma) C) :
    ∃ package :
      WZ1Lemma23GlobalSlicePackage
        (delta := delta) (rho := rho) (sigma := sigma) Y C,
      package.sourceSlope = sourceSlope := by
  rcases
      wz1_lemma23_global_slope_extension
        sourceSlope hsourceLipschitz hsourceBounded with
    ⟨extendedSlope, hextendedLipschitz,
      hextendedBounded, hextendedEq⟩
  have hfinite : volume Y.union ≠ ⊤ := by
    have hballFinite :
        volume (Metric.closedBall (0 : Point3) 2) < ⊤ :=
      Metric.isBounded_closedBall.measure_lt_top
    exact ((measure_mono hball).trans_lt hballFinite).ne
  rcases
      wz1_lemma23_slice_popularity_cell_abundance_two
        Y hrho hball with
    ⟨selectedHeight, hcellsActive, hvolume,
      hselected, hlayerHeight⟩
  let heightIndices :=
    wz1Lemma23BoundedHeightIndices rho hrho
  let layerCells := fun heightIndex =>
    wz1Lemma23ExactSliceCells
      Y rho hrho (selectedHeight heightIndex)
  let cells := heightIndices.biUnion layerCells
  let X : ENNReal :=
    132 * C *
      Kakeya.realRpowENN (1 / rho) (1 - sigma)
  have hX : X ≠ ⊤ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num) hC)
      (by simp [Kakeya.realRpowENN, ENNReal.ofReal_ne_top])
  let globalBinBound : ℕ :=
    Nat.ceil X.toReal + 1
  have hheightIndex_mem :
      ∀ heightIndex ∈ wz1Lemma23SnappedHeights cells,
        heightIndex ∈ heightIndices := by
    intro heightIndex hheightIndex
    rcases Finset.mem_image.mp hheightIndex with
      ⟨idx, hidx, rfl⟩
    rcases Finset.mem_biUnion.mp hidx with
      ⟨sourceHeight, hsourceHeight, hidxLayer⟩
    have hheight :=
      hlayerHeight sourceHeight hsourceHeight idx hidxLayer
    simpa [hheight] using hsourceHeight
  have hglobalBins :
      ∀ heightIndex ∈ wz1Lemma23SnappedHeights cells,
        (wz1Lemma23SnappedGlobalBinsAt
          rho extendedSlope cells heightIndex).card ≤
            globalBinBound := by
    intro heightIndex hheightIndex
    have hheightMem :=
      hheightIndex_mem heightIndex hheightIndex
    have hbins :=
      wz1_lemma23_exactSlice_global_bin_count_of_exact_paper_window
        Y hrho hdelta_rho hrho_one hcoord
        sourceSlope extendedSlope
        hextendedLipschitz hextendedBounded
        hextendedEq hglobal
        (selectedHeight heightIndex)
    have hbinsEq :=
      wz1Lemma23_slicePopularity_globalBins_eq
        Y hrho heightIndices selectedHeight
        (fun index hindex => (hselected index hindex).1)
        extendedSlope hheightMem
    have hbinsENN :
        ((wz1Lemma23SnappedGlobalBinsAt
          rho extendedSlope cells heightIndex).card : ENNReal) ≤ X := by
      rw [hbinsEq]
      exact hbins
    exact
      wz1Lemma23_nat_le_ceil_add_one hX hbinsENN
  let package :
      WZ1Lemma23GlobalSlicePackage
        (delta := delta) (rho := rho) (sigma := sigma) Y C :=
    { extendedSlope := extendedSlope
      rho_pos := hrho
      sourceSlope := sourceSlope
      extendedSlope_lipschitz := hextendedLipschitz
      extendedSlope_bounded := hextendedBounded
      extendedSlope_eq := hextendedEq
      selectedHeight := selectedHeight
      heightIndices := heightIndices
      cells := cells
      layerCells := layerCells
      heightIndices_eq := rfl
      layerCells_eq := fun _ => rfl
      cells_eq := rfl
      selectedHeight_mem := fun heightIndex hheight =>
        (hselected heightIndex hheight).1
      layer_volume_bound := fun heightIndex hheight =>
        (hselected heightIndex hheight).2
      cells_active := hcellsActive
      volume_cell_bound := hvolume
      layer_height := hlayerHeight
      globalBinBound := globalBinBound
      globalBinBound_eq := rfl
      global_bins := hglobalBins }
  exact ⟨package, rfl⟩

/-- Unit-ball compatibility wrapper from an exact-slice AD certificate. -/
theorem wz1_lemma23_global_slice_package_of_exact
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
    (hglobal : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      IsADSet1
        (scalarProjection (globalGrainDirection (sourceSlope z))
          (horizontalSlice Y.union z))
        delta (1 - sigma) C) :
    ∃ package :
      WZ1Lemma23GlobalSlicePackage
        (delta := delta) (rho := rho) (sigma := sigma) Y C,
      package.sourceSlope = sourceSlope := by
  apply wz1_lemma23_global_slice_package_of_exact_paper_window
    Y hrho hdelta_rho hrho_one
  · intro point hpoint
    have h := hball hpoint
    simp only [Metric.mem_closedBall, dist_zero_right] at h ⊢
    linarith
  · intro point hpoint coordinate
    have hnorm : ‖point‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hball hpoint
    simpa [Real.norm_eq_abs] using
      (PiLp.norm_apply_le point coordinate).trans hnorm
  · exact hsourceLipschitz
  · exact hsourceBounded
  · exact hC
  · exact hglobal

/-- Compatibility wrapper from the historical slab certificate. -/
theorem wz1_lemma23_global_slice_package
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
    (hglobal : HasGlobalSlabAD Y sourceSlope sigma C) :
    ∃ package :
      WZ1Lemma23GlobalSlicePackage
        (delta := delta) (rho := rho) (sigma := sigma) Y C,
      package.sourceSlope = sourceSlope := by
  exact wz1_lemma23_global_slice_package_of_exact
    Y hrho hdelta_rho hrho_one hball sourceSlope
    hsourceLipschitz hsourceBounded C hC
    (fun z hz => hglobal.exactSlice z hz)

end

end Kakeya.Assouad
