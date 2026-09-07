import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23ActualLocalBins
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23LocalGraphFromFullGrains
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23PlanarProjectionFullness

/-!
# Local-bin package for the actual WZ1 Lemma 23 cell graph

This module joins the two outputs attached to the same separated coarse cubes:

* an almost-full local grain proves that the anchor normal has large first
  component and hence defines the bounded Lipschitz graph `g`; and
* the Proposition 9 local AD certificate in the radius-`sqrt rho` anchor ball
  bounds the actual snapped local-coordinate bins on that y-layer.

The cell incidence is the paper's genuine `Q(y)` relation.  No auxiliary
graph, diagonal graph, or injectivity surrogate is introduced.
-/

namespace Kakeya.Assouad

noncomputable section

/--
Actual cells and their full local-grain anchors.

Every occupied snapped y-layer is represented in `sample`.  Its anchor is an
actual shaded point, all cells on the layer have genuine representatives in
the anchor's radius-`sqrt rho` ball, and the full-grain normal agrees with the
Proposition 9 plane map at that anchor.
-/
structure WZ1Lemma23LocalCellFamily
    {delta rho sigma eta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (C : ENNReal) (slope : ℝ → ℝ)
    (cells : Finset (ℤ × ℤ × ℤ))
    (localGrains : WZ1LocalGrainData Y sigma C)
    extends WZ1Lemma23FullGrainAnchorFamily
      rho sigma eta C slope where
  rho_pos : 0 < rho
  cells_active :
    cells ⊆ wz1Lemma23ActiveCells Y rho rho_pos
  y_mem :
    ∀ y ∈ wz1Lemma23SnappedYLayers cells,
      wz1Lemma23SnappedYValue rho y ∈ sample
  anchor_mem :
    ∀ y ∈ wz1Lemma23SnappedYLayers cells,
      anchor (wz1Lemma23SnappedYValue rho y) ∈ Y.union
  local_normal :
    ∀ y ∈ wz1Lemma23SnappedYLayers cells,
      normal (anchor (wz1Lemma23SnappedYValue rho y)) =
        localGrains.planeMap
          (anchor (wz1Lemma23SnappedYValue rho y))
  grain_in_source :
    ∀ y (hy : y ∈ wz1Lemma23SnappedYLayers cells),
      (grainInput
        (wz1Lemma23SnappedYValue rho y)
        (y_mem y hy)).grain ⊆
          Y.union
  grain_in_anchor_ball :
    ∀ y (hy : y ∈ wz1Lemma23SnappedYLayers cells),
      (grainInput
        (wz1Lemma23SnappedYValue rho y)
        (y_mem y hy)).grain ⊆
          Metric.closedBall
            (anchor (wz1Lemma23SnappedYValue rho y))
            (Real.sqrt rho)
  layer_ball :
    ∀ y (hy : y ∈ wz1Lemma23SnappedYLayers cells),
      ∀ idx (hidx : idx ∈ cells), idx.2.1 = y →
        dist
            (wz1Lemma23CellRepresentative Y rho_pos
              ⟨idx, cells_active hidx⟩)
            (anchor (wz1Lemma23SnappedYValue rho y)) ≤
          Real.sqrt rho

/-- Actual cells carrying the generalized full-grain anchor family. -/
structure WZ1Lemma23LocalCellFamilyGeneralized
    {delta rho sigma eta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (C : ENNReal) (slope : ℝ → ℝ)
    (cells : Finset (ℤ × ℤ × ℤ))
    (localGrains : WZ1LocalGrainData Y sigma C)
    extends WZ1Lemma23FullGrainAnchorFamilyGeneralized
      rho sigma eta C slope where
  rho_pos : 0 < rho
  cells_active :
    cells ⊆ wz1Lemma23ActiveCells Y rho rho_pos
  y_mem :
    ∀ y ∈ wz1Lemma23SnappedYLayers cells,
      wz1Lemma23SnappedYValue rho y ∈ sample
  anchor_mem :
    ∀ y ∈ wz1Lemma23SnappedYLayers cells,
      anchor (wz1Lemma23SnappedYValue rho y) ∈ Y.union
  local_normal :
    ∀ y ∈ wz1Lemma23SnappedYLayers cells,
      normal (anchor (wz1Lemma23SnappedYValue rho y)) =
        localGrains.planeMap
          (anchor (wz1Lemma23SnappedYValue rho y))
  grain_center :
    ∀ y (hy : y ∈ wz1Lemma23SnappedYLayers cells),
      (grainInput
        (wz1Lemma23SnappedYValue rho y)
        (y_mem y hy)).center =
          anchor (wz1Lemma23SnappedYValue rho y)
  coarseSource :
    ∀ y ∈ sample, Set Point3
  coarse_source_measurable :
    ∀ y (hy : y ∈ sample), MeasurableSet (coarseSource y hy)
  coarse_source_nonempty :
    ∀ y (hy : y ∈ sample), (coarseSource y hy).Nonempty
  coarse_source_subset :
    ∀ y (hy : y ∈ sample),
      coarseSource y hy ⊆
        Y.union ∩ Metric.closedBall (anchor y) (Real.sqrt rho)
  coarse_source_volume :
    ∀ y (hy : y ∈ sample),
      Kakeya.realRpowENN rho
          (3 / 2 + sigma / 2 + eta) ≤
        MeasureTheory.volume (coarseSource y hy)
  grain_in_coarse_source :
    ∀ y (hy : y ∈ wz1Lemma23SnappedYLayers cells),
      (grainInput
        (wz1Lemma23SnappedYValue rho y)
        (y_mem y hy)).grain ⊆
          coarseSource
            (wz1Lemma23SnappedYValue rho y)
            (y_mem y hy)
  grain_in_source :
    ∀ y (hy : y ∈ wz1Lemma23SnappedYLayers cells),
      (grainInput
        (wz1Lemma23SnappedYValue rho y)
        (y_mem y hy)).grain ⊆
          Y.union
  grain_in_anchor_ball :
    ∀ y (hy : y ∈ wz1Lemma23SnappedYLayers cells),
      (grainInput
        (wz1Lemma23SnappedYValue rho y)
        (y_mem y hy)).grain ⊆
          Metric.closedBall
            (anchor (wz1Lemma23SnappedYValue rho y))
            (Real.sqrt rho)
  projected_eq :
    ∀ y (hy : y ∈ wz1Lemma23SnappedYLayers cells),
      ∀ z ∈
          Set.Ico
            (grainInput
              (wz1Lemma23SnappedYValue rho y)
              (y_mem y hy)).heightLeft
            ((grainInput
              (wz1Lemma23SnappedYValue rho y)
              (y_mem y hy)).heightLeft + Real.sqrt rho),
        (grainInput
          (wz1Lemma23SnappedYValue rho y)
          (y_mem y hy)).projected z =
            scalarProjection
              (globalGrainDirection (slope z))
              (horizontalSlice Y.union z)
  layer_ball :
    ∀ y (hy : y ∈ wz1Lemma23SnappedYLayers cells),
      ∀ idx (hidx : idx ∈ cells), idx.2.1 = y →
        dist
            (wz1Lemma23CellRepresentative Y rho_pos
              ⟨idx, cells_active hidx⟩)
            (anchor (wz1Lemma23SnappedYValue rho y)) ≤
          Real.sqrt rho

/--
The actual local graph and one uniform natural-number bound for all occupied
y-layers.
-/
structure WZ1Lemma23LocalBinPackage
    {rho sigma : ℝ}
    (C : ENNReal) (cells : Finset (ℤ × ℤ × ℤ)) where
  g : ℝ → ℝ
  g_lipschitz : LipschitzOnWith 64 g Set.univ
  g_bounded : ∀ y, |g y| ≤ 2
  localBinBound : ℕ
  localBinBound_eq :
    localBinBound =
      Nat.ceil
        (19 * C *
          Kakeya.realRpowENN
            (Real.sqrt rho / rho) (1 - sigma)).toReal + 1
  local_bins :
    ∀ y ∈ wz1Lemma23SnappedYLayers cells,
      (wz1Lemma23SnappedLocalBinsAt
        rho g cells y).card ≤ localBinBound

private lemma wz1Lemma23_local_nat_le_ceil_add_one
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
Construct the local-bin package from the faithful full-grain and coarse-cube
incidence data.
-/
theorem wz1_lemma23_local_bin_package
    {delta rho sigma eta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (C : ENNReal) (slope : ℝ → ℝ)
    (cells : Finset (ℤ × ℤ × ℤ))
    (localGrains : WZ1LocalGrainData Y sigma C)
    (hdelta_rho : delta ≤ rho)
    (hrho_one : rho ≤ 1)
    (hsigma : 0 < sigma) (hsigma_one : sigma < 1)
    (heta : 0 < eta) (heta_sigma : 4 * eta < sigma)
    (hC : C ≠ ⊤)
    (hCpower : C ≤ Kakeya.realRpowENN rho (-eta))
    (hPlanarSmall : 32 * Real.rpow rho eta ≤ 1)
    (hrootSmall : 12 * Real.sqrt rho ≤ 1)
    (habsorb :
      Real.rpow rho (1 - 4 * eta / sigma) ≤
        Real.sqrt rho / 10)
    (family :
      WZ1Lemma23LocalCellFamily
        (rho := rho) (sigma := sigma) (eta := eta)
        Y C slope cells localGrains) :
    ∃ package :
        WZ1Lemma23LocalBinPackage
          (rho := rho) (sigma := sigma) C cells,
      package.localBinBound =
        Nat.ceil
          (19 * C *
            Kakeya.realRpowENN
              (Real.sqrt rho / rho) (1 - sigma)).toReal + 1 := by
  let baseFamily :
      WZ1Lemma23FullGrainAnchorFamily
        rho sigma eta C slope :=
    family.toWZ1Lemma23FullGrainAnchorFamily
  rcases
      wz1_lemma23_local_graph_from_full_grains
        wz1_lemma23_planar_projection_fullness
        rho sigma eta C slope
        family.rho_pos hrho_one hsigma hsigma_one
        heta heta_sigma hC hCpower
        hPlanarSmall hrootSmall habsorb baseFamily with
    ⟨g, hgLipschitz, hgBounded, hgAnchor⟩
  have hfirst :
      ∀ y ∈ wz1Lemma23SnappedYLayers cells,
        1 / 4 ≤
          |localGrains.planeMap
            (family.anchor
              (wz1Lemma23SnappedYValue rho y)) (0 : Fin 3)| := by
    intro y hy
    let sampleY := wz1Lemma23SnappedYValue rho y
    have hsample : sampleY ∈ family.sample :=
      family.y_mem y hy
    have hgrain :=
      wz1_lemma23_full_grain_normal_first_component
        wz1_lemma23_planar_projection_fullness
        rho sigma eta C slope
        family.rho_pos hrho_one hsigma hsigma_one
        heta heta_sigma hC hCpower
        hPlanarSmall hrootSmall habsorb
        (family.grainInput sampleY hsample)
    rw [family.grain_normal sampleY hsample,
      family.local_normal y hy] at hgrain
    exact hgrain
  have hvertical :
      ∀ y ∈ wz1Lemma23SnappedYLayers cells,
        |localGrains.planeMap
          (family.anchor
            (wz1Lemma23SnappedYValue rho y)) (2 : Fin 3)| ≤
          1 / 2 := by
    intro y hy
    have hsample := family.y_mem y hy
    rw [← family.local_normal y hy]
    exact family.normal_vertical
      (wz1Lemma23SnappedYValue rho y) hsample
  have hgraph :
      ∀ y ∈ wz1Lemma23SnappedYLayers cells,
        g (wz1Lemma23SnappedYValue rho y) =
          localGrains.planeMap
              (family.anchor
                (wz1Lemma23SnappedYValue rho y)) (2 : Fin 3) /
            localGrains.planeMap
              (family.anchor
                (wz1Lemma23SnappedYValue rho y)) (0 : Fin 3) := by
    intro y hy
    have hsample := family.y_mem y hy
    rw [← family.local_normal y hy]
    exact hgAnchor
      (wz1Lemma23SnappedYValue rho y) hsample
  let X : ENNReal :=
    19 * C *
      Kakeya.realRpowENN
        (Real.sqrt rho / rho) (1 - sigma)
  have hX : X ≠ ⊤ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num) hC)
      (by simp [Kakeya.realRpowENN, ENNReal.ofReal_ne_top])
  let localBinBound : ℕ := Nat.ceil X.toReal + 1
  have hlocalBins :
      ∀ y ∈ wz1Lemma23SnappedYLayers cells,
        (wz1Lemma23SnappedLocalBinsAt
          rho g cells y).card ≤ localBinBound := by
    intro y hy
    have hbins :=
      wz1_lemma23_actual_local_bins_at
        Y C localGrains cells g
        (fun y =>
          family.anchor (wz1Lemma23SnappedYValue rho y))
        family.rho_pos hdelta_rho hrho_one
        family.cells_active family.anchor_mem
        hvertical hfirst hgraph family.layer_ball y hy
    exact
      wz1Lemma23_local_nat_le_ceil_add_one hX
        (by simpa [X] using hbins)
  exact
    ⟨{ g := g
       g_lipschitz := hgLipschitz
       g_bounded := hgBounded
       localBinBound := localBinBound
       localBinBound_eq := rfl
       local_bins := hlocalBins },
      rfl⟩

/-- Construct the local-bin package from the generalized full-grain data. -/
theorem wz1_lemma23_local_bin_package_generalized
    {delta rho sigma eta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (C : ENNReal) (slope : ℝ → ℝ)
    (cells : Finset (ℤ × ℤ × ℤ))
    (localGrains : WZ1LocalGrainData Y sigma C)
    (hdelta_rho : delta ≤ rho)
    (hrho_one : rho ≤ 1)
    (hsigma : 0 < sigma) (hsigma_one : sigma < 1)
    (heta : 0 < eta) (heta_sigma : 4 * eta < sigma)
    (hC : C ≠ ⊤)
    (hCpower : C ≤ Kakeya.realRpowENN rho (-eta))
    (hPlanarSmall : 32 * Real.rpow rho eta ≤ 1)
    (hrootSmall20 : 20 * Real.sqrt rho ≤ 1)
    (habsorb :
      Real.rpow rho (1 - 4 * eta / sigma) ≤
        Real.sqrt rho / 14)
    (family :
      WZ1Lemma23LocalCellFamilyGeneralized
        (rho := rho) (sigma := sigma) (eta := eta)
        Y C slope cells localGrains) :
    ∃ package :
        WZ1Lemma23LocalBinPackage
          (rho := rho) (sigma := sigma) C cells,
      package.localBinBound =
        Nat.ceil
          (19 * C *
            Kakeya.realRpowENN
              (Real.sqrt rho / rho) (1 - sigma)).toReal + 1 := by
  let baseFamily :
      WZ1Lemma23FullGrainAnchorFamilyGeneralized
        rho sigma eta C slope :=
    family.toWZ1Lemma23FullGrainAnchorFamilyGeneralized
  rcases
      wz1_lemma23_local_graph_from_full_grains_generalized
        rho sigma eta C slope
        family.rho_pos hrho_one hsigma hsigma_one
        heta heta_sigma hC hCpower
        hPlanarSmall hrootSmall20 habsorb baseFamily with
    ⟨g, hgLipschitz, hgBounded, hgAnchor⟩
  have hfirst :
      ∀ y ∈ wz1Lemma23SnappedYLayers cells,
        1 / 4 ≤
          |localGrains.planeMap
            (family.anchor
              (wz1Lemma23SnappedYValue rho y)) (0 : Fin 3)| := by
    intro y hy
    let sampleY := wz1Lemma23SnappedYValue rho y
    have hsample : sampleY ∈ family.sample :=
      family.y_mem y hy
    have hgrain :=
      wz1_lemma23_full_grain_normal_first_component_generalized
        rho sigma eta C slope
        family.rho_pos hrho_one hsigma hsigma_one
        heta heta_sigma hC hCpower
        hPlanarSmall hrootSmall20 habsorb
        (family.grainInput sampleY hsample)
    rw [family.grain_normal sampleY hsample,
      family.local_normal y hy] at hgrain
    exact hgrain
  have hvertical :
      ∀ y ∈ wz1Lemma23SnappedYLayers cells,
        |localGrains.planeMap
          (family.anchor
            (wz1Lemma23SnappedYValue rho y)) (2 : Fin 3)| ≤
          1 / 2 := by
    intro y hy
    have hsample := family.y_mem y hy
    rw [← family.local_normal y hy]
    exact family.normal_vertical
      (wz1Lemma23SnappedYValue rho y) hsample
  have hgraph :
      ∀ y ∈ wz1Lemma23SnappedYLayers cells,
        g (wz1Lemma23SnappedYValue rho y) =
          localGrains.planeMap
              (family.anchor
                (wz1Lemma23SnappedYValue rho y)) (2 : Fin 3) /
            localGrains.planeMap
              (family.anchor
                (wz1Lemma23SnappedYValue rho y)) (0 : Fin 3) := by
    intro y hy
    have hsample := family.y_mem y hy
    rw [← family.local_normal y hy]
    exact hgAnchor
      (wz1Lemma23SnappedYValue rho y) hsample
  let X : ENNReal :=
    19 * C *
      Kakeya.realRpowENN
        (Real.sqrt rho / rho) (1 - sigma)
  have hX : X ≠ ⊤ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num) hC)
      (by simp [Kakeya.realRpowENN, ENNReal.ofReal_ne_top])
  let localBinBound : ℕ := Nat.ceil X.toReal + 1
  have hlocalBins :
      ∀ y ∈ wz1Lemma23SnappedYLayers cells,
        (wz1Lemma23SnappedLocalBinsAt
          rho g cells y).card ≤ localBinBound := by
    intro y hy
    have hbins :=
      wz1_lemma23_actual_local_bins_at
        Y C localGrains cells g
        (fun y =>
          family.anchor (wz1Lemma23SnappedYValue rho y))
        family.rho_pos hdelta_rho hrho_one
        family.cells_active family.anchor_mem
        hvertical hfirst hgraph family.layer_ball y hy
    exact
      wz1Lemma23_local_nat_le_ceil_add_one hX
        (by simpa [X] using hbins)
  exact
    ⟨{ g := g
       g_lipschitz := hgLipschitz
       g_bounded := hgBounded
       localBinBound := localBinBound
       localBinBound_eq := rfl
       local_bins := hlocalBins },
      rfl⟩

end

end Kakeya.Assouad
