import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.PaperCubeSliceArea
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCommonBinPopularHalfMass
import MyLeanRepo.Kakeya.Assouad.WZ1.GeneralizedThickening

/-!
# Same-height horizontal saturation

This file supplies the carrier missing in the written transition from WZ
Lemma 5.4 to Lemma 5.3.  Inside one side-`rho` paper cube, retain precisely
the heights at which a measurable source has positive planar slice area and
fill the horizontal square only at those heights.  Thus every saturated point
has a genuine source point at the same height, while Fubini and a uniform
source-slice cap give a sharp volume lower bound for the saturation.

The construction is an internal measurable set.  It is not asserted to be a
tube shading, to inherit CWA, or to be a union of side-`rho` cubes.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set Metric

attribute [local instance] Classical.propDecidable

/-- Heights at which a measurable three-dimensional set has positive planar
slice area. -/
def wz1Lemma23PositiveSliceHeights (E : Set Point3) : Set ℝ :=
  {z | 0 < volume (wz1Lemma23PlanarSlice E z)}

theorem measurableSet_wz1Lemma23PositiveSliceHeights
    (E : Set Point3) (hE : MeasurableSet E) :
    MeasurableSet (wz1Lemma23PositiveSliceHeights E) := by
  exact measurableSet_lt measurable_const
    (measurable_volume_wz1Lemma23PlanarSlice E hE)

/-- A uniform slice-area cap bounds the total volume by the cap times the
measure of the positive-height support. -/
theorem volume_le_sliceCap_mul_positiveSliceHeights
    (E : Set Point3) (hE : MeasurableSet E) (A : ENNReal)
    (hslice : ∀ z ∈ wz1Lemma23PositiveSliceHeights E,
      volume (wz1Lemma23PlanarSlice E z) ≤ A) :
    volume E ≤ A * volume (wz1Lemma23PositiveSliceHeights E) := by
  rw [wz1_lemma23_volume_eq_lintegral_planarSlice E hE]
  let H := wz1Lemma23PositiveSliceHeights E
  have hH : MeasurableSet H :=
    measurableSet_wz1Lemma23PositiveSliceHeights E hE
  calc
    (∫⁻ z : ℝ, volume (wz1Lemma23PlanarSlice E z)) ≤
        ∫⁻ z : ℝ, H.indicator (fun _ => A) z := by
      apply lintegral_mono
      intro z
      by_cases hz : z ∈ H
      · rw [Set.indicator_of_mem hz]
        exact hslice z hz
      · simp only [Set.indicator, hz, if_false]
        have hzero : volume (wz1Lemma23PlanarSlice E z) = 0 := by
          apply bot_unique
          exact le_of_not_gt hz
        rw [hzero]
    _ = ∫⁻ _z in H, A := by
      rw [lintegral_indicator hH]
    _ = A * volume H :=
      MeasureTheory.setLIntegral_const H A

/-- Fill the horizontal base of one paper cube, but only at heights where the
source part of that cube has positive planar slice area. -/
def wz1PaperGridCubeSameHeightSaturation
    (rho : ℝ) (cell : WZ2PaperCellIndex) (source : Set Point3) : Set Point3 :=
  wz1PaperGridCube rho cell ∩
    {point | point 2 ∈ wz1Lemma23PositiveSliceHeights source}

theorem measurableSet_wz1PaperGridCubeSameHeightSaturation
    (rho : ℝ) (cell : WZ2PaperCellIndex)
    (source : Set Point3) (hsource : MeasurableSet source) :
    MeasurableSet
      (wz1PaperGridCubeSameHeightSaturation rho cell source) := by
  exact (wz1PaperGridCube_measurable cell).inter <|
    (measurableSet_wz1Lemma23PositiveSliceHeights source hsource).preimage
      (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 2).measurable

theorem wz1PaperGridCubeSameHeightSaturation_subset_cube
    (rho : ℝ) (cell : WZ2PaperCellIndex) (source : Set Point3) :
    wz1PaperGridCubeSameHeightSaturation rho cell source ⊆
      wz1PaperGridCube rho cell :=
  Set.inter_subset_left

/-- Positive source slice area supplies an actual source point at that exact
height. -/
theorem wz1Lemma23PositiveSliceHeights_exists_point
    {E : Set Point3} {z : ℝ}
    (hz : z ∈ wz1Lemma23PositiveSliceHeights E) :
    ∃ point : Point2, point ∈ wz1Lemma23PlanarSlice E z := by
  by_contra hempty
  have hset : wz1Lemma23PlanarSlice E z = ∅ :=
    Set.not_nonempty_iff_eq_empty.mp hempty
  rw [wz1Lemma23PositiveSliceHeights, Set.mem_setOf_eq, hset] at hz
  simpa using hz

/-- Every saturated point has a genuine source point at the same height. -/
theorem wz1PaperGridCubeSameHeightSaturation_exists_source_same_height
    {rho : ℝ} {cell : WZ2PaperCellIndex} {source : Set Point3}
    (hsource : source ⊆ wz1PaperGridCube rho cell)
    {point : Point3}
    (hpoint : point ∈
      wz1PaperGridCubeSameHeightSaturation rho cell source) :
    ∃ sourcePoint ∈ source ∩ wz1PaperGridCube rho cell,
      sourcePoint 2 = point 2 := by
  rcases wz1Lemma23PositiveSliceHeights_exists_point hpoint.2 with
    ⟨planar, hplanar⟩
  have hlift := wz1Lemma23_mem_planarSlice_iff.mp hplanar
  refine ⟨point3 (planar 0) (planar 1) (point 2), ?_, by simp [point3]⟩
  exact ⟨hlift, hsource hlift⟩

/-- A positive slice of a source contained in one cube can occur only inside
that cube's vertical interval. -/
theorem wz1Lemma23PositiveSliceHeights_subset_cubeHeight
    {rho : ℝ} (hrho : 0 < rho) (cell : WZ2PaperCellIndex)
    {source : Set Point3}
    (hsource : source ⊆ wz1PaperGridCube rho cell) :
    wz1Lemma23PositiveSliceHeights source ⊆
      Set.Ico ((cell.2.2 : ℝ) * rho) (((cell.2.2 : ℝ) + 1) * rho) := by
  intro z hz
  rcases wz1Lemma23PositiveSliceHeights_exists_point hz with ⟨point, hpoint⟩
  have hlift := hsource (wz1Lemma23_mem_planarSlice_iff.mp hpoint)
  rw [wz1PaperGridCube_eq_Ico hrho cell] at hlift
  have hz0 : (point3 (point 0) (point 1) z) 2 = z := by simp [point3]
  have hlower : (cell.2.2 : ℝ) * rho ≤ z := by
    rw [← hz0]
    exact hlift.2.2.2.2.1
  have hupper : z < ((cell.2.2 : ℝ) + 1) * rho := by
    rw [← hz0]
    exact hlift.2.2.2.2.2
  exact ⟨hlower, hupper⟩

/-- The saturation has the full horizontal square as its slice at every
positive source height, and is empty at all other heights. -/
theorem wz1PaperGridCubeSameHeightSaturation_planarSlice
    (rho : ℝ) (cell : WZ2PaperCellIndex) (source : Set Point3) (z : ℝ) :
    wz1Lemma23PlanarSlice
        (wz1PaperGridCubeSameHeightSaturation rho cell source) z =
      if z ∈ wz1Lemma23PositiveSliceHeights source then
        wz1Lemma23PlanarSlice (wz1PaperGridCube rho cell) z
      else ∅ := by
  ext point
  rw [wz1Lemma23_mem_planarSlice_iff]
  change
    (point3 (point 0) (point 1) z ∈ wz1PaperGridCube rho cell ∧
      (point3 (point 0) (point 1) z) 2 ∈
        wz1Lemma23PositiveSliceHeights source) ↔ _
  have hzcoord : (point3 (point 0) (point 1) z) 2 = z := by simp [point3]
  rw [hzcoord]
  by_cases hz : z ∈ wz1Lemma23PositiveSliceHeights source
  · rw [if_pos hz, wz1Lemma23_mem_planarSlice_iff]
    simp only [hz, and_true]
  · rw [if_neg hz]
    simp only [Set.mem_empty_iff_false, iff_false]
    exact fun hpoint => hz hpoint.2

/-- Exact volume of the same-height saturation. -/
theorem wz1PaperGridCubeSameHeightSaturation_volume
    {rho : ℝ} (hrho : 0 < rho) (cell : WZ2PaperCellIndex)
    (source : Set Point3) (hsourceMeasurable : MeasurableSet source)
    (hsource : source ⊆ wz1PaperGridCube rho cell) :
    volume (wz1PaperGridCubeSameHeightSaturation rho cell source) =
      ENNReal.ofReal (rho ^ 2) *
        volume (wz1Lemma23PositiveSliceHeights source) := by
  let saturation := wz1PaperGridCubeSameHeightSaturation rho cell source
  let H := wz1Lemma23PositiveSliceHeights source
  have hsaturationMeas : MeasurableSet saturation :=
    measurableSet_wz1PaperGridCubeSameHeightSaturation
      rho cell source hsourceMeasurable
  have hH : MeasurableSet H :=
    measurableSet_wz1Lemma23PositiveSliceHeights source hsourceMeasurable
  have hheight : H ⊆
      Set.Ico ((cell.2.2 : ℝ) * rho)
        (((cell.2.2 : ℝ) + 1) * rho) :=
    wz1Lemma23PositiveSliceHeights_subset_cubeHeight hrho cell hsource
  rw [wz1_lemma23_volume_eq_lintegral_planarSlice saturation hsaturationMeas]
  calc
    (∫⁻ z : ℝ, volume (wz1Lemma23PlanarSlice saturation z)) =
        ∫⁻ z : ℝ, H.indicator (fun _ => ENNReal.ofReal (rho ^ 2)) z := by
      congr with z
      by_cases hz : z ∈ H
      · rw [Set.indicator_of_mem hz]
        rw [wz1PaperGridCubeSameHeightSaturation_planarSlice, if_pos hz]
        exact _root_.Kakeya.Assouad.wz1PaperGridCube_planarSlice_volume_exact
          hrho cell z
          (hheight hz)
      · simp only [Set.indicator, hz, if_false]
        rw [wz1PaperGridCubeSameHeightSaturation_planarSlice, if_neg hz]
        simp
    _ = ∫⁻ _z in H, ENNReal.ofReal (rho ^ 2) := by
      rw [lintegral_indicator hH]
    _ = ENNReal.ofReal (rho ^ 2) * volume H :=
      MeasureTheory.setLIntegral_const H _

/-- Horizontal saturation gains the ratio between the horizontal square area
and any uniform source slice-area cap.  This division-free form is convenient
for the later exact power cancellation. -/
theorem source_volume_mul_square_le_sliceCap_mul_saturation_volume
    {rho : ℝ} (hrho : 0 < rho) (cell : WZ2PaperCellIndex)
    (source : Set Point3) (hsourceMeasurable : MeasurableSet source)
    (hsource : source ⊆ wz1PaperGridCube rho cell)
    (A : ENNReal)
    (hslice : ∀ z ∈ wz1Lemma23PositiveSliceHeights source,
      volume (wz1Lemma23PlanarSlice source z) ≤ A) :
    volume source * ENNReal.ofReal (rho ^ 2) ≤
      A * volume (wz1PaperGridCubeSameHeightSaturation rho cell source) := by
  calc
    volume source * ENNReal.ofReal (rho ^ 2) ≤
        (A * volume (wz1Lemma23PositiveSliceHeights source)) *
          ENNReal.ofReal (rho ^ 2) := by
      gcongr
      exact volume_le_sliceCap_mul_positiveSliceHeights
        source hsourceMeasurable A hslice
    _ = A * volume
        (wz1PaperGridCubeSameHeightSaturation rho cell source) := by
      rw [wz1PaperGridCubeSameHeightSaturation_volume
        hrho cell source hsourceMeasurable hsource]
      ring

/-- At one saturated height, the global projection lies in a `4*rho`
thickening of the original source projection at the same height. -/
theorem sameHeightSaturation_projection_subset_source_thickening
    {rho slope z : ℝ} (hrho : 0 < rho)
    (cell : WZ2PaperCellIndex) (source : Set Point3)
    (hsource : source ⊆ wz1PaperGridCube rho cell)
    (hslope : |slope| ≤ 3) :
    (fun point : Point2 => point 0 + slope * point 1) ''
        wz1Lemma23PlanarSlice
          (wz1PaperGridCubeSameHeightSaturation rho cell source) z ⊆
      Metric.cthickening (4 * rho)
        ((fun point : Point2 => point 0 + slope * point 1) ''
          wz1Lemma23PlanarSlice source z) := by
  rintro value ⟨point, hpoint, rfl⟩
  have hlift := wz1Lemma23_mem_planarSlice_iff.mp hpoint
  rcases wz1PaperGridCubeSameHeightSaturation_exists_source_same_height
      hsource hlift with
    ⟨sourcePoint, hsourcePoint, hsourceHeight⟩
  let sourcePlanar : Point2 :=
    WithLp.toLp 2 ![sourcePoint 0, sourcePoint 1]
  have hsourcePlanar : sourcePlanar ∈ wz1Lemma23PlanarSlice source z := by
    rw [wz1Lemma23_mem_planarSlice_iff]
    have hheight : sourcePoint 2 = z := by
      calc
        sourcePoint 2 = (point3 (point 0) (point 1) z) 2 := hsourceHeight
        _ = z := by simp [point3]
    have heq : point3 (sourcePlanar 0) (sourcePlanar 1) z = sourcePoint := by
      ext coordinate
      fin_cases coordinate <;> simp [sourcePlanar, point3, hheight]
    rw [heq]
    exact hsourcePoint.1
  have hpointCube : point3 (point 0) (point 1) z ∈
      wz1PaperGridCube rho cell := hlift.1
  have hsourceCube : sourcePoint ∈ wz1PaperGridCube rho cell := hsourcePoint.2
  rw [wz1PaperGridCube_eq_Ico hrho cell] at hpointCube hsourceCube
  have hp0l : (cell.1 : ℝ) * rho ≤ point 0 := by
    simpa [point3] using hpointCube.1
  have hp0u : point 0 < ((cell.1 : ℝ) + 1) * rho := by
    simpa [point3] using hpointCube.2.1
  have hq0l : (cell.1 : ℝ) * rho ≤ sourcePoint 0 := hsourceCube.1
  have hq0u : sourcePoint 0 < ((cell.1 : ℝ) + 1) * rho := hsourceCube.2.1
  have hp1l : (cell.2.1 : ℝ) * rho ≤ point 1 := by
    simpa [point3] using hpointCube.2.2.1
  have hp1u : point 1 < ((cell.2.1 : ℝ) + 1) * rho := by
    simpa [point3] using hpointCube.2.2.2.1
  have hq1l : (cell.2.1 : ℝ) * rho ≤ sourcePoint 1 := hsourceCube.2.2.1
  have hq1u : sourcePoint 1 < ((cell.2.1 : ℝ) + 1) * rho :=
    hsourceCube.2.2.2.1
  have hx : |point 0 - sourcePoint 0| ≤ rho := by
    rw [abs_sub_le_iff]
    constructor <;> linarith
  have hy : |point 1 - sourcePoint 1| ≤ rho := by
    rw [abs_sub_le_iff]
    constructor <;> linarith
  have hdist :
      dist (point 0 + slope * point 1)
          (sourcePlanar 0 + slope * sourcePlanar 1) ≤ 4 * rho := by
    rw [Real.dist_eq]
    have hsplit :
        point 0 + slope * point 1 -
            (sourcePlanar 0 + slope * sourcePlanar 1) =
          (point 0 - sourcePoint 0) +
            slope * (point 1 - sourcePoint 1) := by
      have hs0 : sourcePlanar 0 = sourcePoint 0 := by simp [sourcePlanar]
      have hs1 : sourcePlanar 1 = sourcePoint 1 := by simp [sourcePlanar]
      rw [hs0, hs1]
      ring
    rw [hsplit]
    calc
      |(point 0 - sourcePoint 0) + slope *
          (point 1 - sourcePoint 1)| ≤
          |point 0 - sourcePoint 0| +
            |slope| * |point 1 - sourcePoint 1| := by
              simpa [abs_mul] using
                (abs_add_le (point 0 - sourcePoint 0)
                  (slope * (point 1 - sourcePoint 1)))
      _ ≤ rho + 3 * rho := by gcongr
      _ = 4 * rho := by ring
  exact Metric.mem_cthickening_of_dist_le
    (point 0 + slope * point 1)
    (sourcePlanar 0 + slope * sourcePlanar 1)
    (4 * rho) _
    ⟨sourcePlanar, hsourcePlanar, rfl⟩ hdist

end Kakeya.Assouad

end
