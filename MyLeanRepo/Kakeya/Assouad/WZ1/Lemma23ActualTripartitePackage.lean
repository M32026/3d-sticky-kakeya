import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23ActualEdgeDotContainment
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23SnappedTripartiteAbundance
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23TripartiteEncoding

/-!
# Actual tripartite package produced by WZ1 Lemma 23

This module packages the already-closed finite Steps 3--5 into the exact
objects consumed by WZ1 Theorem 22.  It does not assert Katz--Tao control,
separation, boundedness, or the final exponent absorption; those remain the
geometric and parameter inputs of the next producer.
-/

namespace Kakeya.Assouad

noncomputable section

/-- The actual Theorem 22 graph after fixing the Step 4 base key. -/
structure WZ1Lemma23ActualTripartitePackage
    (rho : ℝ) (f g : ℝ → ℝ)
    (cells : Finset (ℤ × ℤ × ℤ))
    (baseHeightIndex baseGlobalBin : ℤ) where
  cycles :
    Finset
      ((ℤ × ℤ × ℤ) ×
        (ℤ × ℤ × ℤ) ×
        (ℤ × ℤ × ℤ) ×
        (ℤ × ℤ × ℤ)) :=
    wz1Lemma23SnappedBaseCycles
      rho f g cells baseHeightIndex baseGlobalBin
  cycles_eq :
    cycles =
      wz1Lemma23SnappedBaseCycles
        rho f g cells baseHeightIndex baseGlobalBin
  F : DiscreteSet 2 :=
    wz1Lemma23HeightVertices cycles
      (wz1Lemma23SnappedHeightPoint
        rho f baseHeightIndex)
  G₁ : DiscreteSet 2 :=
    wz1Lemma23FirstLocalVertices cycles
      (wz1Lemma23SnappedLocalPoint rho g)
  G₂ : DiscreteSet 2 :=
    wz1Lemma23ThirdLocalVertices cycles
      (wz1Lemma23SnappedLocalPoint rho g)
  H : Finset (Point2 × Point2 × Point2) :=
    wz1Lemma23TripartiteEdges cycles
      (wz1Lemma23SnappedHeightPoint
        rho f baseHeightIndex)
      (wz1Lemma23SnappedLocalPoint rho g)
  F_eq :
    F =
      wz1Lemma23HeightVertices cycles
        (wz1Lemma23SnappedHeightPoint
          rho f baseHeightIndex)
  G₁_eq :
    G₁ =
      wz1Lemma23FirstLocalVertices cycles
        (wz1Lemma23SnappedLocalPoint rho g)
  G₂_eq :
    G₂ =
      wz1Lemma23ThirdLocalVertices cycles
        (wz1Lemma23SnappedLocalPoint rho g)
  H_eq :
    H =
      wz1Lemma23TripartiteEdges cycles
        (wz1Lemma23SnappedHeightPoint
          rho f baseHeightIndex)
        (wz1Lemma23SnappedLocalPoint rho g)
  edge_support :
    ∀ edge ∈ H,
      edge.1 ∈ F ∧ edge.2.1 ∈ G₁ ∧ edge.2.2 ∈ G₂
  cycle_to_edge :
    cycles.card ≤ 16 * H.card
  dot_containment :
    wz1DotDifferenceSet H ⊆
      Metric.cthickening (4 * rho)
        (wz1Lemma23SnappedBaseSliceValues
          rho f cells baseHeightIndex baseGlobalBin : Set ℝ)

/--
Construct the actual package from the fixed base key, retaining the complete
cell-to-edge cardinality lower chain.
-/
theorem wz1_lemma23_actual_tripartite_package
    (rho : ℝ) (f g : ℝ → ℝ)
    (cells : Finset (ℤ × ℤ × ℤ))
    (localBinBound globalBinBound : ℕ)
    (hrho : 0 < rho)
    (hlocalBins :
      ∀ y ∈ wz1Lemma23SnappedYLayers cells,
        (wz1Lemma23SnappedLocalBinsAt
          rho g cells y).card ≤ localBinBound)
    (hglobalBins :
      ∀ z ∈ wz1Lemma23SnappedHeights cells,
        (wz1Lemma23SnappedGlobalBinsAt
          rho f cells z).card ≤ globalBinBound) :
    ∃ baseHeightIndex baseGlobalBin : ℤ,
      ∃ package :
          WZ1Lemma23ActualTripartitePackage
            rho f g cells baseHeightIndex baseGlobalBin,
        cells.card ^ 4 ≤
          ((wz1Lemma23SnappedYLayers cells).card *
            localBinBound) ^ 2 *
          ((wz1Lemma23SnappedHeights cells).card ^ 2 *
            globalBinBound) *
          ((wz1Lemma23SnappedHeights cells).card *
            globalBinBound) *
          16 * package.H.card := by
  rcases
      wz1_lemma23_snapped_tripartite_abundance
        rho f g cells localBinBound globalBinBound
        hrho hlocalBins hglobalBins with
    ⟨baseHeightIndex, baseGlobalBin, habundance⟩
  let cycles :=
    wz1Lemma23SnappedBaseCycles
      rho f g cells baseHeightIndex baseGlobalBin
  let heightPoint :=
    wz1Lemma23SnappedHeightPoint
      rho f baseHeightIndex
  let localPoint :=
    wz1Lemma23SnappedLocalPoint rho g
  let F := wz1Lemma23HeightVertices cycles heightPoint
  let G₁ := wz1Lemma23FirstLocalVertices cycles localPoint
  let G₂ := wz1Lemma23ThirdLocalVertices cycles localPoint
  let H := wz1Lemma23TripartiteEdges cycles heightPoint localPoint
  have hedge_eq :
      wz1Lemma23SnappedTripartiteEdge
          rho f g baseHeightIndex =
        wz1Lemma23TripartiteEdge heightPoint localPoint := by
    funext path
    rfl
  have hsupport :
      ∀ edge ∈ H,
        edge.1 ∈ F ∧ edge.2.1 ∈ G₁ ∧ edge.2.2 ∈ G₂ := by
    intro edge hedge
    rcases Finset.mem_image.mp hedge with
      ⟨path, hpath, rfl⟩
    exact
      ⟨Finset.mem_image.mpr ⟨path, hpath, rfl⟩,
        Finset.mem_image.mpr ⟨path, hpath, rfl⟩,
        Finset.mem_image.mpr ⟨path, hpath, rfl⟩⟩
  have hcycle_to_edge :
      cycles.card ≤ 16 * H.card := by
    have h :=
      (wz1_lemma23_snapped_tripartite_fiber
        rho f g cells baseHeightIndex baseGlobalBin hrho).2
    change cycles.card ≤
      16 *
        (cycles.image
          (wz1Lemma23SnappedTripartiteEdge
            rho f g baseHeightIndex)).card at h
    change cycles.card ≤
      16 *
        (cycles.image
          (wz1Lemma23TripartiteEdge
            heightPoint localPoint)).card
    rw [← hedge_eq]
    exact h
  have hdot :
      wz1DotDifferenceSet H ⊆
        Metric.cthickening (4 * rho)
          (wz1Lemma23SnappedBaseSliceValues
            rho f cells baseHeightIndex baseGlobalBin : Set ℝ) := by
    have h :=
      wz1_lemma23_actual_edge_dot_containment
        rho f g cells baseHeightIndex baseGlobalBin hrho
    change
      wz1DotDifferenceSet
          (cycles.image
            (wz1Lemma23SnappedTripartiteEdge
              rho f g baseHeightIndex)) ⊆
        Metric.cthickening (4 * rho)
          (wz1Lemma23SnappedBaseSliceValues
            rho f cells baseHeightIndex baseGlobalBin : Set ℝ) at h
    change
      wz1DotDifferenceSet
          (cycles.image
            (wz1Lemma23TripartiteEdge
              heightPoint localPoint)) ⊆
        Metric.cthickening (4 * rho)
          (wz1Lemma23SnappedBaseSliceValues
            rho f cells baseHeightIndex baseGlobalBin : Set ℝ)
    rw [← hedge_eq]
    exact h
  let package :
      WZ1Lemma23ActualTripartitePackage
        rho f g cells baseHeightIndex baseGlobalBin :=
    { cycles := cycles
      cycles_eq := rfl
      F := F
      G₁ := G₁
      G₂ := G₂
      H := H
      F_eq := rfl
      G₁_eq := rfl
      G₂_eq := rfl
      H_eq := rfl
      edge_support := hsupport
      cycle_to_edge := hcycle_to_edge
      dot_containment := hdot }
  refine ⟨baseHeightIndex, baseGlobalBin, package, ?_⟩
  change cells.card ^ 4 ≤
    ((wz1Lemma23SnappedYLayers cells).card *
      localBinBound) ^ 2 *
    ((wz1Lemma23SnappedHeights cells).card ^ 2 *
      globalBinBound) *
    ((wz1Lemma23SnappedHeights cells).card *
      globalBinBound) *
    16 *
    (cycles.image
      (wz1Lemma23TripartiteEdge
        heightPoint localPoint)).card
  rw [← hedge_eq]
  simpa [cycles] using habundance

end

end Kakeya.Assouad
