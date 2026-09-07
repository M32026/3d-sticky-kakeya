import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23GlobalSlicePackage
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23LocalizedExactSliceGlobalBins
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23YResiduePackage

/-!
# Localized global-bin package for WZ1 Lemma 23

The ordinary global-slice package uses the whole bounded exact-slice AD set
and therefore gives a scale-`1` bin bound.  Lemma 23 instead starts inside
the `sqrt rho` neighborhood of one global grain.  This package records that
slice-by-slice localization and replaces the global-bin bound by the sharp
Step 3 scale

`33 * C * (sqrt rho / rho)^(1 - sigma)`.
-/

namespace Kakeya.Assouad

noncomputable section

private lemma wz1Lemma23_localized_nat_le_ceil_add_one
    {n : ℕ} {X : ENNReal} (hX : X ≠ ⊤)
    (hn : (n : ENNReal) ≤ X) :
    n ≤ Nat.ceil X.toReal + 1 := by
  have hreal : (n : ℝ) ≤ X.toReal := by
    rw [← ENNReal.toReal_natCast n]
    exact
      (ENNReal.toReal_le_toReal
        (ENNReal.natCast_ne_top n) hX).mpr hn
  have hceil : n ≤ Nat.ceil X.toReal := by
    exact_mod_cast hreal.trans (Nat.le_ceil X.toReal)
  omega

/--
The original exact-slice cells equipped with the paper's localized
global-grain scalar support and sharp global-bin bound.
-/
structure WZ1Lemma23LocalizedGlobalBinPackage
    {delta rho sigma : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C : ENNReal}
    (globalPackage :
      WZ1Lemma23GlobalSlicePackage
        (delta := delta) (rho := rho) (sigma := sigma) Y C) where
  center : ℤ → ℝ
  localization :
    ∀ heightIndex ∈ globalPackage.heightIndices,
      scalarProjection
          (globalGrainDirection
            (globalPackage.sourceSlope
              (globalPackage.selectedHeight heightIndex)))
          (horizontalSlice Y.union
            (globalPackage.selectedHeight heightIndex)) ⊆
        Metric.closedBall (center heightIndex) (Real.sqrt rho)
  globalBinBound : ℕ
  globalBinBound_eq :
    globalBinBound =
      Nat.ceil
        (33 * C *
          Kakeya.realRpowENN
            (Real.sqrt rho / rho) (1 - sigma)).toReal + 1
  global_bins :
    ∀ heightIndex ∈
        wz1Lemma23SnappedHeights globalPackage.cells,
      (wz1Lemma23SnappedGlobalBinsAt
        rho globalPackage.extendedSlope
        globalPackage.cells heightIndex).card ≤
          globalBinBound

/--
Construct the sharp global-bin package from the paper's slice-by-slice
global-grain localization.
-/
theorem wz1_lemma23_localized_global_bin_package_of_coord_of_exact
    {delta rho sigma : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C : ENNReal}
    (globalPackage :
      WZ1Lemma23GlobalSlicePackage
        (delta := delta) (rho := rho) (sigma := sigma) Y C)
    (hrho_one : rho ≤ 1)
    (hcoord : ∀ point ∈ Y.union, ∀ coordinate : Fin 3,
      |point coordinate| ≤ 1)
    (hexact : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      IsADSet1
        (scalarProjection (globalGrainDirection (globalPackage.sourceSlope z))
          (horizontalSlice Y.union z)) rho (1 - sigma) C)
    (hC : C ≠ ⊤)
    (center : ℤ → ℝ)
    (hlocalized :
      ∀ heightIndex ∈ globalPackage.heightIndices,
        scalarProjection
            (globalGrainDirection
              (globalPackage.sourceSlope
                (globalPackage.selectedHeight heightIndex)))
            (horizontalSlice Y.union
              (globalPackage.selectedHeight heightIndex)) ⊆
          Metric.closedBall
            (center heightIndex) (Real.sqrt rho)) :
    ∃ package :
      WZ1Lemma23LocalizedGlobalBinPackage globalPackage,
      package.globalBinBound =
        Nat.ceil
          (33 * C *
            Kakeya.realRpowENN
              (Real.sqrt rho / rho) (1 - sigma)).toReal + 1 := by
  let X : ENNReal :=
    33 * C *
      Kakeya.realRpowENN
        (Real.sqrt rho / rho) (1 - sigma)
  have hX : X ≠ ⊤ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num) hC)
      (by simp [Kakeya.realRpowENN, ENNReal.ofReal_ne_top])
  let globalBinBound : ℕ :=
    Nat.ceil X.toReal + 1
  have hheightIndexMem :
      ∀ heightIndex ∈
          wz1Lemma23SnappedHeights globalPackage.cells,
        heightIndex ∈ globalPackage.heightIndices := by
    intro heightIndex hheightIndex
    rcases Finset.mem_image.mp hheightIndex with
      ⟨idx, hidx, rfl⟩
    rw [globalPackage.cells_eq] at hidx
    rcases Finset.mem_biUnion.mp hidx with
      ⟨sourceHeight, hsourceHeight, hidxLayer⟩
    have hheight :=
      globalPackage.layer_height
        sourceHeight hsourceHeight idx hidxLayer
    simpa [hheight] using hsourceHeight
  have hglobalBins :
      ∀ heightIndex ∈
          wz1Lemma23SnappedHeights globalPackage.cells,
        (wz1Lemma23SnappedGlobalBinsAt
          rho globalPackage.extendedSlope
          globalPackage.cells heightIndex).card ≤
            globalBinBound := by
    intro heightIndex hheightIndex
    have hheightMem :=
      hheightIndexMem heightIndex hheightIndex
    have hbins :=
      wz1_lemma23_exactSlice_localized_global_bin_count_of_coord_of_exact
        Y globalPackage.rho_pos hrho_one hcoord
        globalPackage.sourceSlope globalPackage.extendedSlope
        globalPackage.extendedSlope_lipschitz
        globalPackage.extendedSlope_bounded
        globalPackage.extendedSlope_eq hexact
        (globalPackage.selectedHeight heightIndex)
        (center heightIndex)
        (hlocalized heightIndex hheightMem)
    have hbinsEq :=
      wz1Lemma23_slicePopularity_globalBins_eq
        Y globalPackage.rho_pos
        globalPackage.heightIndices
        globalPackage.selectedHeight
        globalPackage.selectedHeight_mem
        globalPackage.extendedSlope hheightMem
    have hlayerCellsEq :
        globalPackage.layerCells =
          fun index =>
            wz1Lemma23ExactSliceCells
              Y rho globalPackage.rho_pos
              (globalPackage.selectedHeight index) := by
      funext index
      exact globalPackage.layerCells_eq index
    have hbinsENN :
        ((wz1Lemma23SnappedGlobalBinsAt
          rho globalPackage.extendedSlope
          globalPackage.cells heightIndex).card : ENNReal) ≤ X := by
      rw [globalPackage.cells_eq, hlayerCellsEq]
      rw [hbinsEq]
      simpa [X] using hbins
    exact
      wz1Lemma23_localized_nat_le_ceil_add_one
        hX hbinsENN
  let package :
      WZ1Lemma23LocalizedGlobalBinPackage globalPackage :=
    { center := center
      localization := hlocalized
      globalBinBound := globalBinBound
      globalBinBound_eq := rfl
      global_bins := hglobalBins }
  exact ⟨package, rfl⟩

/-- Adapt historical slab AD to the exact-slice coordinate-crop core. -/
theorem wz1_lemma23_localized_global_bin_package_of_coord
    {delta rho sigma : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C : ENNReal}
    (globalPackage : WZ1Lemma23GlobalSlicePackage
      (delta := delta) (rho := rho) (sigma := sigma) Y C)
    (hdelta_rho : delta ≤ rho) (hrho_one : rho ≤ 1)
    (hcoord : ∀ point ∈ Y.union, ∀ coordinate : Fin 3, |point coordinate| ≤ 1)
    (hglobal : HasGlobalSlabAD Y globalPackage.sourceSlope sigma C)
    (hC : C ≠ ⊤) (center : ℤ → ℝ)
    (hlocalized : ∀ heightIndex ∈ globalPackage.heightIndices,
      scalarProjection
          (globalGrainDirection (globalPackage.sourceSlope
            (globalPackage.selectedHeight heightIndex)))
          (horizontalSlice Y.union (globalPackage.selectedHeight heightIndex)) ⊆
        Metric.closedBall (center heightIndex) (Real.sqrt rho)) :
    ∃ package : WZ1Lemma23LocalizedGlobalBinPackage globalPackage,
      package.globalBinBound = Nat.ceil
        (33 * C * Kakeya.realRpowENN (Real.sqrt rho / rho) (1 - sigma)).toReal + 1 := by
  apply wz1_lemma23_localized_global_bin_package_of_coord_of_exact
    globalPackage hrho_one hcoord _ hC center hlocalized
  intro z hz
  exact (hglobal.exactSlice z hz).coarsen_scale
    globalPackage.rho_pos hdelta_rho hrho_one

/-- Historical unit-ball wrapper for the coordinate-crop package. -/
theorem wz1_lemma23_localized_global_bin_package
    {delta rho sigma : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C : ENNReal}
    (globalPackage :
      WZ1Lemma23GlobalSlicePackage
        (delta := delta) (rho := rho) (sigma := sigma) Y C)
    (hdelta_rho : delta ≤ rho)
    (hrho_one : rho ≤ 1)
    (hball : Y.union ⊆ Metric.closedBall (0 : Point3) 1)
    (hglobal : HasGlobalSlabAD Y globalPackage.sourceSlope sigma C)
    (hC : C ≠ ⊤)
    (center : ℤ → ℝ)
    (hlocalized :
      ∀ heightIndex ∈ globalPackage.heightIndices,
        scalarProjection
            (globalGrainDirection
              (globalPackage.sourceSlope
                (globalPackage.selectedHeight heightIndex)))
            (horizontalSlice Y.union
              (globalPackage.selectedHeight heightIndex)) ⊆
          Metric.closedBall (center heightIndex) (Real.sqrt rho)) :
    ∃ package : WZ1Lemma23LocalizedGlobalBinPackage globalPackage,
      package.globalBinBound =
        Nat.ceil
          (33 * C *
            Kakeya.realRpowENN
              (Real.sqrt rho / rho) (1 - sigma)).toReal + 1 := by
  apply wz1_lemma23_localized_global_bin_package_of_coord
    globalPackage hdelta_rho hrho_one _ hglobal hC center hlocalized
  intro point hpoint coordinate
  have hnorm : ‖point‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hball hpoint
  exact (PiLp.norm_apply_le point coordinate).trans hnorm

/-- The sharp global-bin bound restricts to any actual-cell subset. -/
lemma WZ1Lemma23LocalizedGlobalBinPackage.global_bins_mono
    {delta rho sigma : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C : ENNReal}
    {globalPackage :
      WZ1Lemma23GlobalSlicePackage
        (delta := delta) (rho := rho) (sigma := sigma) Y C}
    (package :
      WZ1Lemma23LocalizedGlobalBinPackage globalPackage)
    {cells : Finset (ℤ × ℤ × ℤ)}
    (hcells : cells ⊆ globalPackage.cells) :
    ∀ heightIndex ∈ wz1Lemma23SnappedHeights cells,
      (wz1Lemma23SnappedGlobalBinsAt
        rho globalPackage.extendedSlope cells heightIndex).card ≤
          package.globalBinBound := by
  intro heightIndex hheight
  have hheightGlobal :
      heightIndex ∈
        wz1Lemma23SnappedHeights globalPackage.cells :=
    wz1Lemma23_snappedHeights_mono hcells hheight
  exact
    (Finset.card_le_card
        (wz1Lemma23_snappedGlobalBinsAt_mono
          rho globalPackage.extendedSlope
          heightIndex hcells)).trans
      (package.global_bins heightIndex hheightGlobal)

end

end Kakeya.Assouad
