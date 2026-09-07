import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23GlobalSlopeExtension
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23PerturbedADBinCount
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23SlicePopularity
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23SnappedCellGeometry
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23SnappedFourCycleAbundanceStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.TransportNormalizeAD

/-!
# Global scalar-bin bounds on genuine WZ1 Lemma 23 slices

Every cell in an exact-slice layer carries a genuine source point at one real
height.  The source global scalar values therefore lie in the exact-slice AD
set.  Snapping changes those values by at most `4 * rho`, so the perturbed
AD-bin theorem bounds the actual snapped scalar bins.
-/

namespace Kakeya.Assouad

noncomputable section

/-- Snapped global scalar values on one genuine exact-slice cell family. -/
def wz1Lemma23ExactSliceGlobalValues
    {delta rho : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (hrho : 0 < rho) (z : ℝ)
    (slope : ℝ → ℝ) : Finset ℝ :=
  (wz1Lemma23ExactSliceCells Y rho hrho z).image fun idx =>
    wz1Lemma23GlobalCoordinate slope
      (wz1Lemma23CellCenter rho idx)

private lemma wz1Lemma23_globalCoordinate_eq_projection
    (slope : ℝ → ℝ) (z : ℝ) (point : Point2) :
    wz1Lemma23GlobalCoordinate slope
        (wz1Lemma23LiftSlicePoint z point) =
      inner ℝ (wz1Lemma23LiftSlicePoint z point)
        (globalGrainDirection (slope z)) := by
  simp [wz1Lemma23GlobalCoordinate, wz1Lemma23LiftSlicePoint,
    globalGrainDirection, point3, PiLp.inner_apply,
    Fin.sum_univ_succ]

/--
The actual snapped global values from one genuine exact slice occupy at most
`132 * C * rho^(-(1-sigma))` scalar bins.
-/
theorem wz1_lemma23_exactSlice_global_bin_count_of_exact_paper_window
    {delta rho sigma : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (hrho : 0 < rho) (hdelta_rho : delta ≤ rho)
    (hrho_one : rho ≤ 1)
    (hcoord : ∀ point ∈ Y.union, ∀ coordinate : Fin 3,
      |point coordinate| ≤ 1)
    (sourceSlope extendedSlope : ℝ → ℝ)
    (hextendedLipschitz :
      LipschitzOnWith 1 extendedSlope Set.univ)
    (hextendedBounded : ∀ z, |extendedSlope z| ≤ 3)
    (hextendedEq :
      ∀ z ∈ Set.Icc (-1 : ℝ) 1,
        extendedSlope z = sourceSlope z)
    {C : ENNReal}
    (hglobal : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      IsADSet1
        (scalarProjection (globalGrainDirection (sourceSlope z))
          (horizontalSlice Y.union z))
        delta (1 - sigma) C)
    (z : ℝ) :
    ((wz1Lemma23ScalarBins rho
      (wz1Lemma23ExactSliceGlobalValues
        Y hrho z extendedSlope)).card : ENNReal) ≤
      132 * C *
        Kakeya.realRpowENN (1 / rho) (1 - sigma) := by
  classical
  let cells := wz1Lemma23ExactSliceCells Y rho hrho z
  let values :=
    wz1Lemma23ExactSliceGlobalValues
      Y hrho z extendedSlope
  by_cases hcells : cells = ∅
  · have hvalues : values = ∅ := by
      simp [values, cells, wz1Lemma23ExactSliceGlobalValues, hcells]
    simpa [values, hvalues]
  · have hcellsNonempty : cells.Nonempty := by
      simpa [Finset.nonempty_iff_ne_empty] using hcells
    rcases hcellsNonempty with ⟨idx, hidx⟩
    let cell : WZ1Lemma23ExactSliceCell Y rho hrho z :=
      ⟨idx, hidx⟩
    let representative :=
      wz1Lemma23ExactSliceRepresentative Y hrho z cell
    let point := wz1Lemma23LiftSlicePoint z representative
    have hpointUnion : point ∈ Y.union := by
      exact
        wz1Lemma23ExactSliceRepresentative_mem_union
          Y hrho z cell
    have hzCoord : point (2 : Fin 3) = z := by
      simp [point, wz1Lemma23LiftSlicePoint, point3]
    have hzAbs : |z| ≤ 1 := by
      rw [← hzCoord]
      simpa [hzCoord] using hcoord point hpointUnion (2 : Fin 3)
    have hz : z ∈ Set.Icc (-1 : ℝ) 1 :=
      abs_le.mp hzAbs
    let E :=
      scalarProjection
        (globalGrainDirection (sourceSlope z))
        (horizontalSlice Y.union z)
    have hADSource :
        IsADSet1 E delta (1 - sigma) C := by
      exact hglobal z hz
    have hADRho :
        IsADSet1 E rho (1 - sigma) C :=
      hADSource.coarsen_scale hrho hdelta_rho hrho_one
    have hzeroLipschitz :
        LipschitzOnWith 4
          (fun _ : ℝ => (0 : ℝ)) Set.univ := by
      exact
        ((LipschitzWith.const (0 : ℝ)).weaken
          (by norm_num)).lipschitzOnWith
    have hclose :
        ∀ value ∈ values,
          ∃ sourceValue ∈ E,
            |value - sourceValue| ≤ 4 * rho := by
      intro value hvalue
      rcases Finset.mem_image.mp hvalue with
        ⟨sourceIdx, hsourceIdx, rfl⟩
      let sourceCell :
          WZ1Lemma23ExactSliceCell Y rho hrho z :=
        ⟨sourceIdx, hsourceIdx⟩
      let sourceRepresentative :=
        wz1Lemma23ExactSliceRepresentative
          Y hrho z sourceCell
      let sourcePoint :=
        wz1Lemma23LiftSlicePoint z sourceRepresentative
      have hsourcePointUnion : sourcePoint ∈ Y.union :=
        wz1Lemma23ExactSliceRepresentative_mem_union
          Y hrho z sourceCell
      let sourceValue :=
        inner ℝ sourcePoint
          (globalGrainDirection (sourceSlope z))
      have hsourcePointHeight :
          sourcePoint (2 : Fin 3) = z := by
        simp [sourcePoint, wz1Lemma23LiftSlicePoint, point3]
      have hsourceHorizontal :
          sourcePoint ∈ horizontalSlice Y.union z := by
        exact ⟨hsourcePointUnion, hsourcePointHeight⟩
      have hsourceValueMem : sourceValue ∈ E :=
        ⟨sourcePoint, hsourceHorizontal, rfl⟩
      have hsnap :=
        wz1Lemma23_globalCoordinate_snap_of_coord_bound
          hrho hrho_one extendedSlope
          hextendedLipschitz hextendedBounded sourcePoint
          (hcoord sourcePoint hsourcePointUnion)
      have hsourceIndex :
          wz1Lemma23CellIndex rho sourcePoint = sourceIdx :=
        wz1Lemma23ExactSliceRepresentative_index
          Y hrho z sourceCell
      have hsnapEq :
          wz1Lemma23Snap rho sourcePoint =
            wz1Lemma23CellCenter rho sourceIdx := by
        simp [wz1Lemma23Snap, hsourceIndex]
      have hsourceCoord :
          wz1Lemma23GlobalCoordinate
              extendedSlope sourcePoint =
            sourceValue := by
        calc
          wz1Lemma23GlobalCoordinate
              extendedSlope sourcePoint =
              inner ℝ sourcePoint
                (globalGrainDirection (extendedSlope z)) := by
            simpa [sourcePoint, sourceRepresentative] using
              wz1Lemma23_globalCoordinate_eq_projection
                extendedSlope z sourceRepresentative
          _ = sourceValue := by
            rw [hextendedEq z hz]
      refine ⟨sourceValue, hsourceValueMem, ?_⟩
      rw [← hsnapEq, ← hsourceCoord]
      simpa [abs_sub_comm] using hsnap
    exact
      wz1_lemma23_perturbed_ad_bin_count
        rho (1 - sigma) C E values
        hADRho hrho_one hclose

/-- Unit-ball compatibility wrapper for the exact-slice global bin count. -/
theorem wz1_lemma23_exactSlice_global_bin_count_of_exact
    {delta rho sigma : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (hrho : 0 < rho) (hdelta_rho : delta ≤ rho)
    (hrho_one : rho ≤ 1)
    (hball : Y.union ⊆ Metric.closedBall (0 : Point3) 1)
    (sourceSlope extendedSlope : ℝ → ℝ)
    (hextendedLipschitz :
      LipschitzOnWith 1 extendedSlope Set.univ)
    (hextendedBounded : ∀ z, |extendedSlope z| ≤ 3)
    (hextendedEq :
      ∀ z ∈ Set.Icc (-1 : ℝ) 1,
        extendedSlope z = sourceSlope z)
    {C : ENNReal}
    (hglobal : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      IsADSet1
        (scalarProjection (globalGrainDirection (sourceSlope z))
          (horizontalSlice Y.union z))
        delta (1 - sigma) C)
    (z : ℝ) :
    ((wz1Lemma23ScalarBins rho
      (wz1Lemma23ExactSliceGlobalValues
        Y hrho z extendedSlope)).card : ENNReal) ≤
      132 * C *
        Kakeya.realRpowENN (1 / rho) (1 - sigma) := by
  refine wz1_lemma23_exactSlice_global_bin_count_of_exact_paper_window
    Y hrho hdelta_rho hrho_one ?_ sourceSlope extendedSlope
    hextendedLipschitz hextendedBounded hextendedEq hglobal z
  intro point hpoint coordinate
  have hnorm : ‖point‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hball hpoint
  simpa [Real.norm_eq_abs] using
    (PiLp.norm_apply_le point coordinate).trans hnorm

/-- Compatibility wrapper from the historical slab certificate. -/
theorem wz1_lemma23_exactSlice_global_bin_count
    {delta rho sigma : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (hrho : 0 < rho) (hdelta_rho : delta ≤ rho)
    (hrho_one : rho ≤ 1)
    (hball : Y.union ⊆ Metric.closedBall (0 : Point3) 1)
    (sourceSlope extendedSlope : ℝ → ℝ)
    (hextendedLipschitz :
      LipschitzOnWith 1 extendedSlope Set.univ)
    (hextendedBounded : ∀ z, |extendedSlope z| ≤ 3)
    (hextendedEq :
      ∀ z ∈ Set.Icc (-1 : ℝ) 1,
        extendedSlope z = sourceSlope z)
    {C : ENNReal}
    (hglobal : HasGlobalSlabAD Y sourceSlope sigma C)
    (z : ℝ) :
    ((wz1Lemma23ScalarBins rho
      (wz1Lemma23ExactSliceGlobalValues
        Y hrho z extendedSlope)).card : ENNReal) ≤
      132 * C *
        Kakeya.realRpowENN (1 / rho) (1 - sigma) := by
  exact wz1_lemma23_exactSlice_global_bin_count_of_exact
    Y hrho hdelta_rho hrho_one hball
    sourceSlope extendedSlope hextendedLipschitz
    hextendedBounded hextendedEq
    (fun height hheight => hglobal.exactSlice height hheight) z

/--
For a disjoint union of exact-slice layers, filtering by one occupied snapped
height recovers exactly that layer's cells.
-/
lemma wz1Lemma23_slicePopularity_filter_height
    {delta rho : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (hrho : 0 < rho)
    (heightIndices : Finset ℤ)
    (selectedHeight : ℤ → ℝ)
    (hselected :
      ∀ heightIndex ∈ heightIndices,
        selectedHeight heightIndex ∈
          wz1Lemma23HeightInterval rho heightIndex)
    {heightIndex : ℤ} (hheightIndex : heightIndex ∈ heightIndices) :
    let layerCells := fun index =>
      wz1Lemma23ExactSliceCells
        Y rho hrho (selectedHeight index)
    let cells := heightIndices.biUnion layerCells
    cells.filter (fun idx => idx.2.2 = heightIndex) =
      layerCells heightIndex := by
  classical
  dsimp only
  ext idx
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hidx, hidxHeight⟩
    rcases Finset.mem_biUnion.mp hidx with
      ⟨sourceHeight, hsourceHeight, hidxSource⟩
    have hsourceEq :
        idx.2.2 = sourceHeight :=
      wz1Lemma23_exactSliceCells_height_eq
        Y hrho (hselected sourceHeight hsourceHeight)
        hidxSource
    have hheightEq : sourceHeight = heightIndex := by
      omega
    simpa [hheightEq] using hidxSource
  · intro hidx
    have hidxHeight :
        idx.2.2 = heightIndex :=
      wz1Lemma23_exactSliceCells_height_eq
        Y hrho (hselected heightIndex hheightIndex)
        hidx
    exact
      ⟨Finset.mem_biUnion.mpr
          ⟨heightIndex, hheightIndex, hidx⟩,
        hidxHeight⟩

/--
The `SnappedGlobalBinsAt` set consumed by the actual four-cycle count is the
scalar-bin image of the corresponding exact-slice values.
-/
lemma wz1Lemma23_slicePopularity_globalBins_eq
    {delta rho : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (hrho : 0 < rho)
    (heightIndices : Finset ℤ)
    (selectedHeight : ℤ → ℝ)
    (hselected :
      ∀ heightIndex ∈ heightIndices,
        selectedHeight heightIndex ∈
          wz1Lemma23HeightInterval rho heightIndex)
    (slope : ℝ → ℝ)
    {heightIndex : ℤ} (hheightIndex : heightIndex ∈ heightIndices) :
    let layerCells := fun index =>
      wz1Lemma23ExactSliceCells
        Y rho hrho (selectedHeight index)
    let cells := heightIndices.biUnion layerCells
    wz1Lemma23SnappedGlobalBinsAt
        rho slope cells heightIndex =
      wz1Lemma23ScalarBins rho
        (wz1Lemma23ExactSliceGlobalValues
          Y hrho (selectedHeight heightIndex) slope) := by
  classical
  dsimp only
  rw [wz1Lemma23SnappedGlobalBinsAt,
    wz1Lemma23_slicePopularity_filter_height
      Y hrho heightIndices selectedHeight hselected hheightIndex]
  simp [wz1Lemma23SnappedGlobalBin,
    wz1Lemma23ScalarBins,
    wz1Lemma23ExactSliceGlobalValues,
    wz1Lemma23SnappedPoint, Finset.image_image,
    Function.comp_def]

end

end Kakeya.Assouad
