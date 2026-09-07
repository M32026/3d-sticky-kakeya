import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23LocalizedPerturbedADBinCount
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23SnappedCellGeometry
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23SnappedFourCycleAbundanceStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23SpatialGrid

/-!
# Actual per-y local-bin bounds for WZ1 Lemma 23

For one retained snapped y-layer, choose the genuine shaded anchor of the
paper's unique separated `sqrt rho` cube `Q(y)`.  The Proposition 9 local
grain certificate controls the normal projection of the shading in the
`sqrt rho` ball around that anchor.

The local graph value at the snapped y-coordinate is the quotient
`V_z / V_x`.  Consequently the snapped local coordinate is an affine image
of the normal projection, up to the spatial-cell snapping error.  This module
feeds that relation into the localized affine perturbed AD-bin theorem.
-/

namespace Kakeya.Assouad

noncomputable section

/-- Real y-coordinate of a snapped cell with integer y-index `y`. -/
def wz1Lemma23SnappedYValue (rho : ℝ) (y : ℤ) : ℝ :=
  (wz1Lemma23CellCenter rho ((0 : ℤ), y, (0 : ℤ))) (1 : Fin 3)

private lemma wz1Lemma23_cellCenter_y_eq
    (rho : ℝ) (idx : ℤ × ℤ × ℤ) :
    (wz1Lemma23CellCenter rho idx) (1 : Fin 3) =
      wz1Lemma23SnappedYValue rho idx.2.1 := by
  simp [wz1Lemma23SnappedYValue, wz1Lemma23CellCenter, point3]

/--
The actual local scalar bins on one snapped y-layer obey the localized
Proposition 9 AD bound.

`hlayerBall` is precisely the paper's separated-coarse-cube incidence:
all retained cells on this y-layer have genuine shaded representatives in the
single radius-`sqrt rho` ball centered at `anchor`.
-/
theorem wz1_lemma23_actual_local_bins_at
    {delta rho sigma : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (C : ENNReal)
    (localGrains : WZ1LocalGrainData Y sigma C)
    (cells : Finset (ℤ × ℤ × ℤ))
    (g : ℝ → ℝ) (anchor : ℤ → Point3)
    (hrho : 0 < rho)
    (hdelta_rho : delta ≤ rho)
    (hrho_one : rho ≤ 1)
    (hactive :
      cells ⊆ wz1Lemma23ActiveCells Y rho hrho)
    (hanchor :
      ∀ y ∈ wz1Lemma23SnappedYLayers cells,
        anchor y ∈ Y.union)
    (hvertical :
      ∀ y ∈ wz1Lemma23SnappedYLayers cells,
        |localGrains.planeMap (anchor y) (2 : Fin 3)| ≤ 1 / 2)
    (hfirst :
      ∀ y ∈ wz1Lemma23SnappedYLayers cells,
        1 / 4 ≤
          |localGrains.planeMap (anchor y) (0 : Fin 3)|)
    (hgraph :
      ∀ y ∈ wz1Lemma23SnappedYLayers cells,
        g (wz1Lemma23SnappedYValue rho y) =
          localGrains.planeMap (anchor y) (2 : Fin 3) /
            localGrains.planeMap (anchor y) (0 : Fin 3))
    (hlayerBall :
      ∀ y (hy : y ∈ wz1Lemma23SnappedYLayers cells),
        ∀ idx (hidx : idx ∈ cells), idx.2.1 = y →
          dist
              (wz1Lemma23CellRepresentative Y hrho
                ⟨idx, hactive hidx⟩)
              (anchor y) ≤
            Real.sqrt rho)
    (y : ℤ) (hy : y ∈ wz1Lemma23SnappedYLayers cells) :
    ((wz1Lemma23SnappedLocalBinsAt
        rho g cells y).card : ENNReal) ≤
      19 * C *
        Kakeya.realRpowENN
          (Real.sqrt rho / rho) (1 - sigma) := by
  classical
  let normal := localGrains.planeMap (anchor y)
  let a : ℝ := 1 / normal 0
  let b : ℝ :=
    -(normal 1 / normal 0) *
      wz1Lemma23SnappedYValue rho y
  let targetValues : Finset ℝ :=
    (cells.filter fun idx => idx.2.1 = y).image fun idx =>
      wz1Lemma23LocalCoordinate g
        (wz1Lemma23SnappedPoint rho idx)
  have hnormalUnit : ‖normal‖ = 1 :=
    localGrains.unit (anchor y) (hanchor y hy)
  have hnx : 1 / 4 ≤ |normal 0| := hfirst y hy
  have hnxPos : 0 < |normal 0| := by linarith
  have hnxNe : normal 0 ≠ 0 :=
    abs_ne_zero.mp hnxPos.ne'
  have hcoord0 : |normal 0| ≤ 1 := by
    have h := PiLp.norm_apply_le normal (0 : Fin 3)
    simpa [Real.norm_eq_abs, hnormalUnit] using h
  have hcoord1 : |normal 1| ≤ 1 := by
    have h := PiLp.norm_apply_le normal (1 : Fin 3)
    simpa [Real.norm_eq_abs, hnormalUnit] using h
  have ha : |a| ≤ 4 := by
    rw [abs_div, abs_one]
    have h :
        (1 : ℝ) / |normal 0| ≤
          1 / (1 / 4 : ℝ) := by
      gcongr
    norm_num at h ⊢
    exact h
  have hyRatio : |normal 1 / normal 0| ≤ 4 := by
    rw [abs_div]
    calc
      |normal 1| / |normal 0|
          ≤ 1 / |normal 0| := by gcongr
      _ ≤ 1 / (1 / 4 : ℝ) := by gcongr
      _ = 4 := by norm_num
  have hzRatio : |normal 2 / normal 0| ≤ 2 := by
    rw [abs_div]
    calc
      |normal 2| / |normal 0|
          ≤ (1 / 2 : ℝ) / |normal 0| := by
            gcongr
            exact hvertical y hy
      _ ≤ (1 / 2 : ℝ) / (1 / 4 : ℝ) := by gcongr
      _ = 2 := by norm_num
  have hrhoSqrt : rho ≤ Real.sqrt rho := by
    have hsquare := Real.sq_sqrt hrho.le
    nlinarith [Real.sqrt_nonneg rho, hrho_one]
  have hsqrtOne : Real.sqrt rho ≤ 1 := by
    have hsquare := Real.sq_sqrt hrho.le
    nlinarith [Real.sqrt_nonneg rho, hrho_one]
  have hAD :
      IsADSet1
        (scalarProjection normal
          (Y.union ∩
            Metric.closedBall (anchor y) (Real.sqrt rho)))
        rho (1 - sigma) C := by
    simpa [normal] using
      localGrains.local_ad rho hdelta_rho hrho_one
        (anchor y) (hanchor y hy)
  have hclose :
      ∀ value ∈ targetValues,
        ∃ sourceValue ∈
            scalarProjection normal
                (Y.union ∩
                  Metric.closedBall (anchor y) (Real.sqrt rho)) ∩
              Metric.closedBall
                (inner ℝ (anchor y) normal)
                (Real.sqrt rho),
          |value - (a * sourceValue + b)| ≤ 4 * rho := by
    intro value hvalue
    rcases Finset.mem_image.mp hvalue with
      ⟨idx, hidxFilter, rfl⟩
    have hidx : idx ∈ cells := (Finset.mem_filter.mp hidxFilter).1
    have hidxY : idx.2.1 = y :=
      (Finset.mem_filter.mp hidxFilter).2
    let cell : WZ1Lemma23ActiveCell Y rho hrho :=
      ⟨idx, hactive hidx⟩
    let point := wz1Lemma23CellRepresentative Y hrho cell
    let snapped := wz1Lemma23SnappedPoint rho idx
    let sourceValue := inner ℝ point normal
    have hpointUnion : point ∈ Y.union :=
      wz1Lemma23CellRepresentative_mem_union Y hrho cell
    have hpointBall :
        point ∈ Metric.closedBall (anchor y) (Real.sqrt rho) := by
      rw [Metric.mem_closedBall]
      exact hlayerBall y hy idx hidx hidxY
    have hsourceProjection :
        sourceValue ∈
          scalarProjection normal
            (Y.union ∩
              Metric.closedBall (anchor y) (Real.sqrt rho)) :=
      ⟨point, ⟨hpointUnion, hpointBall⟩, rfl⟩
    have hsourceWindow :
        sourceValue ∈
          Metric.closedBall
            (inner ℝ (anchor y) normal)
            (Real.sqrt rho) := by
      rw [Metric.mem_closedBall, Real.dist_eq]
      have hinner :
          |inner ℝ (point - anchor y) normal| ≤
            ‖point - anchor y‖ * ‖normal‖ :=
        abs_real_inner_le_norm (point - anchor y) normal
      have hdist :
          ‖point - anchor y‖ ≤ Real.sqrt rho := by
        simpa [dist_eq_norm] using
          hlayerBall y hy idx hidx hidxY
      have heq :
          sourceValue - inner ℝ (anchor y) normal =
            inner ℝ (point - anchor y) normal := by
        simp [sourceValue, inner_sub_left]
      rw [heq]
      exact hinner.trans (by
        rw [hnormalUnit, mul_one]
        exact hdist)
    have hpointIndex :
        wz1Lemma23CellIndex rho point = idx :=
      wz1Lemma23CellRepresentative_index Y hrho cell
    have hgeometry :=
      wz1_lemma23_snapped_cell_geometry rho hrho hrho_one
    have hcoord :
        ∀ i : Fin 3,
          |point i - (wz1Lemma23CellCenter rho idx) i| ≤
            rho / 2 :=
      (hgeometry.2.1 idx point hpointIndex).1
    have hsnappedY :
        snapped 1 = wz1Lemma23SnappedYValue rho y := by
      simpa [snapped, wz1Lemma23SnappedPoint, hidxY] using
        wz1Lemma23_cellCenter_y_eq rho idx
    have hgraphY :
        g (snapped 1) = normal 2 / normal 0 := by
      rw [hsnappedY]
      simpa [normal] using hgraph y hy
    have hsourceFormula :
        a * sourceValue + b =
          point 0 +
            (normal 1 / normal 0) *
                (point 1 -
                  wz1Lemma23SnappedYValue rho y) +
            (normal 2 / normal 0) * point 2 := by
      simp only [a, b, sourceValue, scalarProjection]
      simp [PiLp.inner_apply, Fin.sum_univ_succ]
      field_simp [hnxNe]
      ring
    have hpointY :
        |point 1 - wz1Lemma23SnappedYValue rho y| ≤
          rho / 2 := by
      rw [← hsnappedY]
      simpa [snapped, wz1Lemma23SnappedPoint] using hcoord 1
    have hmain :
        |wz1Lemma23LocalCoordinate g snapped -
            (a * sourceValue + b)| ≤
          rho / 2 + 2 * (rho / 2) + 4 * (rho / 2) := by
      rw [hsourceFormula]
      simp only [wz1Lemma23LocalCoordinate, hgraphY]
      have heq :
          snapped 0 +
                (normal 2 / normal 0) * snapped 2 -
              (point 0 +
                  (normal 1 / normal 0) *
                      (point 1 -
                        wz1Lemma23SnappedYValue rho y) +
                  (normal 2 / normal 0) * point 2) =
            (snapped 0 - point 0) +
              (normal 2 / normal 0) * (snapped 2 - point 2) -
              (normal 1 / normal 0) *
                (point 1 -
                  wz1Lemma23SnappedYValue rho y) := by
        ring
      rw [heq]
      calc
        |(snapped 0 - point 0) +
              (normal 2 / normal 0) * (snapped 2 - point 2) -
              (normal 1 / normal 0) *
                (point 1 -
                  wz1Lemma23SnappedYValue rho y)|
            ≤ |snapped 0 - point 0| +
                |normal 2 / normal 0| *
                  |snapped 2 - point 2| +
                |normal 1 / normal 0| *
                  |point 1 -
                    wz1Lemma23SnappedYValue rho y| := by
              calc
                |(snapped 0 - point 0) +
                      (normal 2 / normal 0) *
                        (snapped 2 - point 2) -
                      (normal 1 / normal 0) *
                        (point 1 -
                          wz1Lemma23SnappedYValue rho y)|
                    ≤ |(snapped 0 - point 0) +
                        (normal 2 / normal 0) *
                          (snapped 2 - point 2)| +
                        |(normal 1 / normal 0) *
                          (point 1 -
                            wz1Lemma23SnappedYValue rho y)| :=
                      abs_sub _ _
                _ ≤
                      |snapped 0 - point 0| +
                        |(normal 2 / normal 0) *
                          (snapped 2 - point 2)| +
                        |(normal 1 / normal 0) *
                          (point 1 -
                            wz1Lemma23SnappedYValue rho y)| := by
                      gcongr
                      exact abs_add_le _ _
                _ =
                      |snapped 0 - point 0| +
                        |normal 2 / normal 0| *
                          |snapped 2 - point 2| +
                        |normal 1 / normal 0| *
                          |point 1 -
                            wz1Lemma23SnappedYValue rho y| := by
                      rw [abs_mul, abs_mul]
        _ ≤ rho / 2 + 2 * (rho / 2) + 4 * (rho / 2) := by
          have h0 :
              |snapped 0 - point 0| ≤ rho / 2 := by
            rw [abs_sub_comm]
            simpa [snapped, wz1Lemma23SnappedPoint] using hcoord 0
          have h2 :
              |snapped 2 - point 2| ≤ rho / 2 := by
            rw [abs_sub_comm]
            simpa [snapped, wz1Lemma23SnappedPoint] using hcoord 2
          gcongr
    have hfour :
        rho / 2 + 2 * (rho / 2) + 4 * (rho / 2) ≤
          4 * rho := by
      linarith
    exact
      ⟨sourceValue, ⟨hsourceProjection, hsourceWindow⟩,
        hmain.trans hfour⟩
  have hbins :=
    wz1_lemma23_localized_affine_perturbed_ad_bin_count
      rho (Real.sqrt rho) (1 - sigma) a b C
      (scalarProjection normal
        (Y.union ∩
          Metric.closedBall (anchor y) (Real.sqrt rho)))
      targetValues
      (inner ℝ (anchor y) normal)
      hAD hrhoSqrt hsqrtOne ha hclose
  have htargetBins :
      wz1Lemma23ScalarBins rho targetValues =
        wz1Lemma23SnappedLocalBinsAt rho g cells y := by
    simp [targetValues, wz1Lemma23ScalarBins,
      wz1Lemma23SnappedLocalBinsAt, Finset.image_image,
      Function.comp_def]
  rw [← htargetBins]
  exact hbins

end

end Kakeya.Assouad
