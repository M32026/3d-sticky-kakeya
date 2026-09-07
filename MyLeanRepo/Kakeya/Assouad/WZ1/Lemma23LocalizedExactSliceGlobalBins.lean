import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23ExactSliceGlobalBins
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23LocalizedPerturbedADBinCount

/-!
# Localized exact-slice global bins for WZ1 Lemma 23

The paper restricts `E` to the `sqrt rho` neighborhood of one global grain
before the four-cycle count.  On every exact height slice, the genuine global
scalar values therefore lie in one radius-`sqrt rho` portion of the global
AD set.  Combining this localization with the actual cell-center snapping
error gives the sharp Step 3 global-bin scale

`33 * C * (sqrt rho / rho)^(1 - sigma)`.
-/

namespace Kakeya.Assouad

noncomputable section

private lemma wz1Lemma23_localized_globalCoordinate_eq_projection
    (slope : ℝ → ℝ) (z : ℝ) (point : Point2) :
    wz1Lemma23GlobalCoordinate slope
        (wz1Lemma23LiftSlicePoint z point) =
      inner ℝ (wz1Lemma23LiftSlicePoint z point)
        (globalGrainDirection (slope z)) := by
  simp [wz1Lemma23GlobalCoordinate, wz1Lemma23LiftSlicePoint,
    globalGrainDirection, point3, PiLp.inner_apply,
    Fin.sum_univ_succ]

/--
The snapped exact-slice values are within `4 * rho` of genuine source
projection values.
-/
lemma wz1Lemma23_exactSlice_snapped_values_close_of_coord
    {delta rho : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (hrho : 0 < rho) (hrho_one : rho ≤ 1)
    (hcoord : ∀ point ∈ Y.union, ∀ coordinate : Fin 3,
      |point coordinate| ≤ 1)
    (sourceSlope extendedSlope : ℝ → ℝ)
    (hextendedLipschitz :
      LipschitzOnWith 1 extendedSlope Set.univ)
    (hextendedBounded : ∀ z, |extendedSlope z| ≤ 3)
    (hextendedEq :
      ∀ z ∈ Set.Icc (-1 : ℝ) 1,
        extendedSlope z = sourceSlope z)
    (z : ℝ)
    (hz : z ∈ Set.Icc (-1 : ℝ) 1) :
    let E :=
      scalarProjection
        (globalGrainDirection (sourceSlope z))
        (horizontalSlice Y.union z)
    let values :=
      wz1Lemma23ExactSliceGlobalValues
        Y hrho z extendedSlope
    ∀ value ∈ values,
      ∃ sourceValue ∈ E,
        |value - sourceValue| ≤ 4 * rho := by
  dsimp only
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
  have hsourceValueMem :
      sourceValue ∈
        scalarProjection
          (globalGrainDirection (sourceSlope z))
          (horizontalSlice Y.union z) :=
    ⟨sourcePoint, hsourceHorizontal, rfl⟩
  have hsnap :=
    wz1Lemma23_globalCoordinate_snap_of_coord_bound
      hrho hrho_one extendedSlope hextendedLipschitz
      hextendedBounded sourcePoint
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
          wz1Lemma23_localized_globalCoordinate_eq_projection
            extendedSlope z sourceRepresentative
      _ = sourceValue := by
        rw [hextendedEq z hz]
  refine ⟨sourceValue, hsourceValueMem, ?_⟩
  rw [← hsnapEq, ← hsourceCoord]
  simpa [abs_sub_comm] using hsnap

/-- Historical unit-ball wrapper for the coordinate-crop snapping bound. -/
lemma wz1Lemma23_exactSlice_snapped_values_close
    {delta rho : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (hrho : 0 < rho) (hrho_one : rho ≤ 1)
    (hball : Y.union ⊆ Metric.closedBall (0 : Point3) 1)
    (sourceSlope extendedSlope : ℝ → ℝ)
    (hextendedLipschitz :
      LipschitzOnWith 1 extendedSlope Set.univ)
    (hextendedBounded : ∀ z, |extendedSlope z| ≤ 3)
    (hextendedEq :
      ∀ z ∈ Set.Icc (-1 : ℝ) 1,
        extendedSlope z = sourceSlope z)
    (z : ℝ)
    (hz : z ∈ Set.Icc (-1 : ℝ) 1) :
    let E :=
      scalarProjection
        (globalGrainDirection (sourceSlope z))
        (horizontalSlice Y.union z)
    let values :=
      wz1Lemma23ExactSliceGlobalValues
        Y hrho z extendedSlope
    ∀ value ∈ values,
      ∃ sourceValue ∈ E,
        |value - sourceValue| ≤ 4 * rho := by
  apply wz1Lemma23_exactSlice_snapped_values_close_of_coord
    Y hrho hrho_one _ sourceSlope extendedSlope
    hextendedLipschitz hextendedBounded hextendedEq z hz
  intro point hpoint coordinate
  have hnorm : ‖point‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hball hpoint
  exact (PiLp.norm_apply_le point coordinate).trans hnorm

/--
Localized exact-slice global-bin count at an arbitrary admissible radius
`R`.  This is the quantitative form used after the paper has selected a
global-grain neighbourhood whose width is only specified up to an absolute
constant.
-/
theorem wz1_lemma23_exactSlice_localized_global_bin_count_of_coord_of_exact_radius
    {delta rho sigma : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (hrho : 0 < rho)
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
    (hexact : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      IsADSet1
        (scalarProjection (globalGrainDirection (sourceSlope z))
          (horizontalSlice Y.union z))
        rho (1 - sigma) C)
    (z center R : ℝ)
    (hrho_R : rho ≤ R)
    (hR_one : R ≤ 1)
    (hlocalized :
      scalarProjection
          (globalGrainDirection (sourceSlope z))
          (horizontalSlice Y.union z) ⊆
        Metric.closedBall center R) :
    ((wz1Lemma23ScalarBins rho
      (wz1Lemma23ExactSliceGlobalValues
        Y hrho z extendedSlope)).card : ENNReal) ≤
      33 * C *
        Kakeya.realRpowENN
          (R / rho) (1 - sigma) := by
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
    have hpointUnion : point ∈ Y.union :=
      wz1Lemma23ExactSliceRepresentative_mem_union
        Y hrho z cell
    have hzCoord : point (2 : Fin 3) = z := by
      simp [point, wz1Lemma23LiftSlicePoint, point3]
    have hzAbs : |z| ≤ 1 := by
      rw [← hzCoord]
      exact hcoord point hpointUnion 2
    have hz : z ∈ Set.Icc (-1 : ℝ) 1 :=
      abs_le.mp hzAbs
    let E :=
      scalarProjection
        (globalGrainDirection (sourceSlope z))
        (horizontalSlice Y.union z)
    have hADRho : IsADSet1 E rho (1 - sigma) C :=
      hexact z hz
    have hcloseSource :=
      wz1Lemma23_exactSlice_snapped_values_close_of_coord
        Y hrho hrho_one hcoord
        sourceSlope extendedSlope
        hextendedLipschitz hextendedBounded
        hextendedEq z hz
    have hcloseLocalized :
        ∀ value ∈ values,
          ∃ sourceValue ∈
              E ∩ Metric.closedBall center R,
            |value - sourceValue| ≤ 4 * rho := by
      intro value hvalue
      rcases hcloseSource value hvalue with
        ⟨sourceValue, hsourceValue, hclose⟩
      exact
        ⟨sourceValue,
          ⟨hsourceValue, hlocalized hsourceValue⟩,
          hclose⟩
    simpa [E, values] using
      wz1_lemma23_localized_perturbed_ad_bin_count_direct
        rho R (1 - sigma) C
        E values center hADRho
        hrho_R hR_one hcloseLocalized

/--
Localized exact-slice global-bin count at the paper's radius `sqrt rho`.
-/
theorem wz1_lemma23_exactSlice_localized_global_bin_count_of_coord_of_exact
    {delta rho sigma : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (hrho : 0 < rho)
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
    (hexact : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      IsADSet1
        (scalarProjection (globalGrainDirection (sourceSlope z))
          (horizontalSlice Y.union z))
        rho (1 - sigma) C)
    (z center : ℝ)
    (hlocalized :
      scalarProjection
          (globalGrainDirection (sourceSlope z))
          (horizontalSlice Y.union z) ⊆
        Metric.closedBall center (Real.sqrt rho)) :
    ((wz1Lemma23ScalarBins rho
      (wz1Lemma23ExactSliceGlobalValues
        Y hrho z extendedSlope)).card : ENNReal) ≤
      33 * C *
        Kakeya.realRpowENN
          (Real.sqrt rho / rho) (1 - sigma) := by
  have hrhoSqrt : rho ≤ Real.sqrt rho := by
    have hsqrtNonneg : 0 ≤ Real.sqrt rho :=
      Real.sqrt_nonneg rho
    have hsqrtSq : Real.sqrt rho ^ 2 = rho :=
      Real.sq_sqrt hrho.le
    nlinarith
  have hsqrtOne : Real.sqrt rho ≤ 1 :=
    Real.sqrt_le_one.mpr hrho_one
  exact wz1_lemma23_exactSlice_localized_global_bin_count_of_coord_of_exact_radius
    Y hrho hrho_one hcoord sourceSlope extendedSlope
    hextendedLipschitz hextendedBounded hextendedEq hexact
    z center (Real.sqrt rho) hrhoSqrt hsqrtOne hlocalized

/-- Convert the historical slab-AD input to the exact-slice core. -/
theorem wz1_lemma23_exactSlice_localized_global_bin_count_of_coord
    {delta rho sigma : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (hrho : 0 < rho) (hdelta_rho : delta ≤ rho)
    (hrho_one : rho ≤ 1)
    (hcoord : ∀ point ∈ Y.union, ∀ coordinate : Fin 3,
      |point coordinate| ≤ 1)
    (sourceSlope extendedSlope : ℝ → ℝ)
    (hextendedLipschitz : LipschitzOnWith 1 extendedSlope Set.univ)
    (hextendedBounded : ∀ z, |extendedSlope z| ≤ 3)
    (hextendedEq : ∀ z ∈ Set.Icc (-1 : ℝ) 1, extendedSlope z = sourceSlope z)
    {C : ENNReal}
    (hglobal : HasGlobalSlabAD Y sourceSlope sigma C)
    (z center : ℝ)
    (hlocalized :
      scalarProjection (globalGrainDirection (sourceSlope z))
          (horizontalSlice Y.union z) ⊆
        Metric.closedBall center (Real.sqrt rho)) :
    ((wz1Lemma23ScalarBins rho
      (wz1Lemma23ExactSliceGlobalValues Y hrho z extendedSlope)).card : ENNReal) ≤
      33 * C * Kakeya.realRpowENN (Real.sqrt rho / rho) (1 - sigma) := by
  apply wz1_lemma23_exactSlice_localized_global_bin_count_of_coord_of_exact
    Y hrho hrho_one hcoord sourceSlope extendedSlope
    hextendedLipschitz hextendedBounded hextendedEq _ z center hlocalized
  intro sourceZ hsourceZ
  exact (hglobal.exactSlice sourceZ hsourceZ).coarsen_scale
    hrho hdelta_rho hrho_one

/-- Historical unit-ball wrapper for the paper-coordinate-crop theorem. -/
theorem wz1_lemma23_exactSlice_localized_global_bin_count
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
    (z center : ℝ)
    (hlocalized :
      scalarProjection
          (globalGrainDirection (sourceSlope z))
          (horizontalSlice Y.union z) ⊆
        Metric.closedBall center (Real.sqrt rho)) :
    ((wz1Lemma23ScalarBins rho
      (wz1Lemma23ExactSliceGlobalValues
        Y hrho z extendedSlope)).card : ENNReal) ≤
      33 * C *
        Kakeya.realRpowENN
          (Real.sqrt rho / rho) (1 - sigma) := by
  apply wz1_lemma23_exactSlice_localized_global_bin_count_of_coord
    Y hrho hdelta_rho hrho_one _ sourceSlope extendedSlope
    hextendedLipschitz hextendedBounded hextendedEq
    hglobal z center hlocalized
  intro point hpoint coordinate
  have hnorm : ‖point‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hball hpoint
  exact (PiLp.norm_apply_le point coordinate).trans hnorm

end

end Kakeya.Assouad
