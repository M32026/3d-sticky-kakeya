import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63ExactSlice
import MyLeanRepo.Kakeya.Assouad.WZ1.HorizontalChartNormalization
import MyLeanRepo.Kakeya.Assouad.PureWZ2.NormalizationCWATransport

/-!
# Horizontal-chart normalization for Proposition 6.3

The chart selected in the slab argument is global: it is either the identity
or the swap of the first two coordinates.  This file transports the actual
cropped paper family and shading through that one isometry.  In particular,
the second chart is not discharged by changing the slope alone.
-/

noncomputable section

namespace Kakeya.Assouad

open Kakeya.Streamlined MeasureTheory Set Metric

namespace WZ1HorizontalChart

/-- The induced permutation of paper-grid indices. -/
def mapGridIndex : WZ1HorizontalChart → (ℤ × ℤ × ℤ) → (ℤ × ℤ × ℤ)
  | .first, index => index
  | .second, index => (index.2.1, index.1, index.2.2)

/-- Regard the linear chart as the origin-fixing affine isometry consumed by
the pure-CWA transport theorem. -/
def affineIsometry (chart : WZ1HorizontalChart) :
    Point3 ≃ᵃⁱ[ℝ] Point3 := chart.isometry.toAffineIsometryEquiv

@[simp] lemma affineIsometry_apply
    (chart : WZ1HorizontalChart) (point : Point3) :
    chart.affineIsometry point = chart.isometry point := by
  rfl

@[simp] lemma mapGridIndex_involutive
    (chart : WZ1HorizontalChart) (index : ℤ × ℤ × ℤ) :
    chart.mapGridIndex (chart.mapGridIndex index) = index := by
  cases chart <;> rcases index with ⟨first, second, third⟩ <;> rfl

/-- A horizontal chart carries a tube axis to the axis of the transported
tube. -/
lemma image_tubeAxisLine
    (chart : WZ1HorizontalChart) {delta : ℝ}
    (tube : Kakeya.DeltaTube delta) :
    chart.isometry '' tubeAxisLine tube =
      tubeAxisLine (transportTube chart.isometry tube) := by
  ext point
  constructor
  · rintro ⟨source, ⟨parameter, rfl⟩, rfl⟩
    refine ⟨parameter, ?_⟩
    simp [transportTube, map_add, map_smul]
  · rintro ⟨parameter, rfl⟩
    refine ⟨tube.base + parameter • tube.direction, ⟨parameter, rfl⟩, ?_⟩
    simp [transportTube, map_add, map_smul]

/-- The symmetric paper crop is invariant under either horizontal chart. -/
lemma image_paper_axisBox (chart : WZ1HorizontalChart) :
    chart.isometry '' Kakeya.Streamlined.axisBox 2 2 2 =
      Kakeya.Streamlined.axisBox 2 2 2 := by
  cases chart with
  | first =>
      simp [isometry]
  | second =>
      ext point
      constructor
      · rintro ⟨source, hsource, rfl⟩
        norm_num [Kakeya.Streamlined.axisBox] at hsource ⊢
        simpa [Kakeya.Streamlined.axisBox, isometry, wz1Swap01_apply, point3]
          using ⟨hsource.2.1, hsource.1, hsource.2.2⟩
      · intro hpoint
        refine ⟨wz1Swap01 point, ?_, wz1Swap01_involutive point⟩
        norm_num [Kakeya.Streamlined.axisBox] at hpoint ⊢
        simpa [Kakeya.Streamlined.axisBox, isometry, wz1Swap01_apply, point3]
          using ⟨hpoint.2.1, hpoint.1, hpoint.2.2⟩

@[simp] lemma paperGridIndex_isometry
    (chart : WZ1HorizontalChart) (scale : ℝ) (point : Point3) :
    wz1PaperGridIndex scale (chart.isometry point) =
      chart.mapGridIndex (wz1PaperGridIndex scale point) := by
  cases chart <;>
    simp [WZ1HorizontalChart.isometry, mapGridIndex, wz1PaperGridIndex,
      gridIndex, wz1Swap01_apply, point3]

/-- Horizontal coordinate permutation sends one paper grid cube exactly to
the correspondingly permuted cube. -/
lemma image_paperGridCube
    (chart : WZ1HorizontalChart) (scale : ℝ)
    (index : ℤ × ℤ × ℤ) :
    chart.isometry '' wz1PaperGridCube scale index =
      wz1PaperGridCube scale (chart.mapGridIndex index) := by
  ext point
  constructor
  · rintro ⟨source, hsource, rfl⟩
    rw [mem_wz1PaperGridCube, chart.paperGridIndex_isometry]
    exact congrArg chart.mapGridIndex
      ((mem_wz1PaperGridCube scale index source).mp hsource)
  · intro hpoint
    refine ⟨chart.isometry point, ?_, chart.isometry_involutive point⟩
    rw [mem_wz1PaperGridCube, chart.paperGridIndex_isometry]
    have hindex := congrArg chart.mapGridIndex
      ((mem_wz1PaperGridCube scale
        (chart.mapGridIndex index) point).mp hpoint)
    simpa using hindex

/-- The cropped full-line paper carrier commutes with a horizontal chart. -/
lemma image_paperTubeCarrier
    (chart : WZ1HorizontalChart) {delta : ℝ}
    (tube : Kakeya.DeltaTube delta) :
    chart.isometry '' wz1PaperTubeCarrier tube =
      wz1PaperTubeCarrier (transportTube chart.isometry tube) := by
  rw [wz1PaperTubeCarrier, wz1PaperTubeCarrier,
    Set.image_inter chart.isometry.injective,
    image_cthickening, chart.image_tubeAxisLine, chart.image_paper_axisBox]

/-- Transport a cropped paper shading through the selected chart. -/
def transportPaperShading
    (chart : WZ1HorizontalChart) {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family) :
    WZ1PaperTubeShading (transportFamily chart.isometry family) where
  carrier index := chart.isometry ''
    shading.carrier ⟨index.1, by
      simpa [wz1PaperBodyFamily, transportFamily] using index.2⟩
  measurable_carrier index := by
    let sourceIndex : Fin (wz1PaperBodyFamily family).card :=
      ⟨index.1, by
        simpa [wz1PaperBodyFamily, transportFamily] using index.2⟩
    have hsource := shading.measurable_carrier sourceIndex
    have himage : chart.isometry '' shading.carrier sourceIndex =
        chart.isometry.symm ⁻¹' shading.carrier sourceIndex := by
      ext point
      constructor
      · rintro ⟨source, hsource, rfl⟩
        simpa using hsource
      · intro hpoint
        exact ⟨chart.isometry.symm point, hpoint,
          chart.isometry.apply_symm_apply point⟩
    rw [himage]
    exact hsource.preimage chart.isometry.symm.continuous.measurable
  subset_body index := by
    let sourceIndex : Fin (wz1PaperBodyFamily family).card :=
      ⟨index.1, by
        simpa [wz1PaperBodyFamily, transportFamily] using index.2⟩
    change chart.isometry '' shading.carrier sourceIndex ⊆
      wz1PaperTubeCarrier
        ((transportFamily chart.isometry family).tube index)
    have htube :
        (transportFamily chart.isometry family).tube index =
          transportTube chart.isometry (family.tube sourceIndex) := by
      rfl
    rw [htube, ← chart.image_paperTubeCarrier (family.tube sourceIndex)]
    exact Set.image_mono (shading.subset_body sourceIndex)

@[simp] lemma transportPaperShading_carrier
    (chart : WZ1HorizontalChart) {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (index : Fin family.card) :
    (chart.transportPaperShading shading).carrier index =
      chart.isometry '' shading.carrier index := by
  rfl

lemma transportPaperShading_union
    (chart : WZ1HorizontalChart) {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family} :
    (chart.transportPaperShading shading).union =
      chart.isometry '' shading.union := by
  ext point
  simp only [Shading.union, transportPaperShading, Set.mem_iUnion,
    Set.mem_image]
  constructor
  · rintro ⟨index, source, hsource, rfl⟩
    exact ⟨source, ⟨index, hsource⟩, rfl⟩
  · rintro ⟨source, ⟨index, hsource⟩, rfl⟩
    exact ⟨index, source, hsource, rfl⟩

lemma transportPaperShading_mass
    (chart : WZ1HorizontalChart) {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family} :
    (chart.transportPaperShading shading).mass = shading.mass := by
  simp only [Shading.mass, transportPaperShading]
  apply Finset.sum_congr rfl
  intro index _
  exact volume_image chart.isometry (shading.carrier index)

lemma transportPaperBodyFamily_mass
    (chart : WZ1HorizontalChart) {delta : ℝ}
    (family : Kakeya.Streamlined.TubeFamily delta) :
    (wz1PaperBodyFamily (transportFamily chart.isometry family)).mass =
      (wz1PaperBodyFamily family).mass := by
  simp only [Kakeya.Streamlined.BodyFamily.mass, wz1PaperBodyFamily]
  apply Finset.sum_congr rfl
  intro index _
  rw [show wz1PaperTubeCarrier
      ((transportFamily chart.isometry family).tube index) =
        chart.isometry '' wz1PaperTubeCarrier (family.tube index) by
    exact (chart.image_paperTubeCarrier (family.tube index)).symm]
  exact volume_image chart.isometry _

/-- Paper cubicality is invariant under the horizontal chart. -/
lemma transportPaperShading_cubical
    (chart : WZ1HorizontalChart) {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (hcubical : WZ1PaperIsCubicalShading shading) :
    WZ1PaperIsCubicalShading (chart.transportPaperShading shading) := by
  intro index point hpoint
  let sourceIndex : Fin (wz1PaperBodyFamily family).card :=
    ⟨index.1, by
      simpa [wz1PaperBodyFamily, transportFamily] using index.2⟩
  change point ∈ chart.isometry '' shading.carrier sourceIndex at hpoint
  rcases hpoint with ⟨source, hsource, rfl⟩
  have hsourceCube := hcubical sourceIndex source hsource
  rw [chart.paperGridIndex_isometry,
    ← chart.image_paperGridCube delta (wz1PaperGridIndex delta source)]
  exact Set.image_mono hsourceCube

/-- The positive paper direction commutes with a horizontal chart. -/
lemma paperDirection_transportTube
    (chart : WZ1HorizontalChart) {delta : ℝ}
    (tube : Kakeya.DeltaTube delta) :
    wz1PaperDirection (transportTube chart.isometry tube) =
      chart.isometry (wz1PaperDirection tube) := by
  unfold wz1PaperDirection
  have hcoord :
      (transportTube chart.isometry tube).direction (2 : Fin 3) =
        tube.direction (2 : Fin 3) := by
    exact chart.isometry_preserves_coord2 tube.direction
  rw [hcoord]
  split_ifs
  · rfl
  · change -(chart.isometry tube.direction) =
      chart.isometry (-tube.direction)
    exact (chart.isometry.map_neg tube.direction).symm

/-- The height-zero axis point commutes with a horizontal chart. -/
lemma tubeAxisZeroPoint_transportTube
    (chart : WZ1HorizontalChart) {delta : ℝ}
    (tube : Kakeya.DeltaTube delta) :
    wz1TubeAxisZeroPoint (transportTube chart.isometry tube) =
      chart.isometry (wz1TubeAxisZeroPoint tube) := by
  unfold wz1TubeAxisZeroPoint
  change chart.isometry tube.base -
      ((chart.isometry tube.base) 2 /
        (chart.isometry tube.direction) 2) • chart.isometry tube.direction =
    chart.isometry
      (tube.base - (tube.base 2 / tube.direction 2) • tube.direction)
  rw [chart.isometry_preserves_coord2, chart.isometry_preserves_coord2]
  rw [chart.isometry.map_sub, chart.isometry.map_smul]

/-- The fixed paper line class is invariant under a horizontal coordinate
swap. -/
lemma transportFamily_lineClass
    (chart : WZ1HorizontalChart) {delta : ℝ}
    (family : Kakeya.Streamlined.TubeFamily delta)
    (hline : WZ1PaperIsLineClass family) :
    WZ1PaperIsLineClass (transportFamily chart.isometry family) := by
  intro index
  have hsource := hline index
  rcases hsource with ⟨hvertical, hzero, hone⟩
  constructor
  · change 1 / 2 ≤
      (wz1PaperDirection
        (transportTube chart.isometry (family.tube index))) 2
    rw [chart.paperDirection_transportTube,
      chart.isometry_preserves_coord2]
    exact hvertical
  · change
      |(wz1TubeAxisZeroPoint
        (transportTube chart.isometry (family.tube index))) 0| ≤ 1 / 3 ∧
      |(wz1TubeAxisZeroPoint
        (transportTube chart.isometry (family.tube index))) 1| ≤ 1 / 3
    rw [chart.tubeAxisZeroPoint_transportTube]
    cases chart with
    | first =>
        constructor
        · simpa [isometry] using hzero
        · simpa [isometry] using hone
    | second =>
        constructor
        · simpa [isometry, wz1Swap01_apply, point3] using hone
        · simpa [isometry, wz1Swap01_apply, point3] using hzero

/-- The generic affine-isometry image family is definitionally the same as
the linear transport used by the paper-shading layer. -/
lemma imageTubeFamily_eq_transportFamily
    (chart : WZ1HorizontalChart) {delta : ℝ}
    (family : Kakeya.Streamlined.TubeFamily delta) :
    imageTubeFamily chart.affineIsometry family =
      transportFamily chart.isometry family := by
  rfl

/-- Pure nearby-scale CWA is invariant under the horizontal chart. -/
lemma transportFamily_pureCWA
    (chart : WZ1HorizontalChart) {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    (hcwa : WZ2PaperPureCWAAtNearbyScales family C) :
    WZ2PaperPureCWAAtNearbyScales
      (transportFamily chart.isometry family) C := by
  rw [← chart.imageTubeFamily_eq_transportFamily family]
  exact pureCWAAtNearbyScales_image chart.affineIsometry hcwa

/-- Cropped Section 6 extremality is invariant under the global horizontal
chart. -/
lemma transportPaperCroppedExtremal
    (chart : WZ1HorizontalChart)
    {delta sigma loss : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (hextremal : WZ2PaperCroppedIsExtremal
      sigma loss family shading) :
    WZ2PaperCroppedIsExtremal sigma loss
      (transportFamily chart.isometry family)
      (chart.transportPaperShading shading) := by
  refine
    { delta_pos := hextremal.delta_pos
      delta_le_one := hextremal.delta_le_one
      nonempty := ?_
      cwa_nearby_scales := chart.transportFamily_pureCWA
        hextremal.cwa_nearby_scales
      cubical := chart.transportPaperShading_cubical hextremal.cubical
      dense := ?_
      volume_upper := ?_ }
  · change 0 < family.card
    exact hextremal.nonempty
  · change Kakeya.realRpowENN delta loss *
        (wz1PaperBodyFamily
          (transportFamily chart.isometry family)).mass ≤
      (chart.transportPaperShading shading).mass
    rw [chart.transportPaperBodyFamily_mass,
      chart.transportPaperShading_mass]
    exact hextremal.dense
  · rw [chart.transportPaperShading_union, volume_image]
    exact hextremal.volume_upper

/-- Horizontal slices commute with the chart because the height coordinate is
fixed. -/
lemma image_horizontalSlice
    (chart : WZ1HorizontalChart) (set : Set Point3) (height : ℝ) :
    chart.isometry '' horizontalSlice set height =
      horizontalSlice (chart.isometry '' set) height := by
  ext point
  constructor
  · rintro ⟨source, ⟨hsource, hheight⟩, rfl⟩
    exact ⟨⟨source, hsource, rfl⟩, by
      rw [chart.isometry_preserves_coord2]
      exact hheight⟩
  · rintro ⟨⟨source, hsource, hpoint⟩, hheight⟩
    subst point
    exact ⟨source, ⟨hsource, by
      rw [chart.isometry_preserves_coord2] at hheight
      exact hheight⟩, rfl⟩

/-- Scalar projection in the normalized chart is exactly the original
charted scalar projection. -/
lemma scalarProjection_image_chart
    (chart : WZ1HorizontalChart) (slope : ℝ) (set : Set Point3) :
    scalarProjection (globalGrainDirection slope)
        (chart.isometry '' set) =
      scalarProjection (chart.direction slope) set := by
  change globalGrainProjection (fun _ : ℝ => slope)
      (chart.isometry '' set) =
    wz1ChartedGlobalGrainProjection chart (fun _ : ℝ => slope) set
  exact transportProjection_eq chart (fun _ => slope) set

/-- The exact horizontal-slice projection after chart normalization. -/
lemma normalized_horizontalSlice_projection
    (chart : WZ1HorizontalChart) {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (slope height : ℝ) :
    scalarProjection (globalGrainDirection slope)
        (horizontalSlice (chart.transportPaperShading shading).union height) =
      scalarProjection (chart.direction slope)
        (horizontalSlice shading.union height) := by
  rw [chart.transportPaperShading_union, ← chart.image_horizontalSlice]
  exact chart.scalarProjection_image_chart slope _

end WZ1HorizontalChart

namespace PureWZ2.Proposition63ChartSelectionData

variable
    {delta rho Delta sigma stickyLoss localLoss targetLoss coefficient : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    {original : PureWZ2BalancedCoverData cover fineShading coarseShading}
    {initial : PropertyThreeSelectedInitialLocalData
      (sigma := sigma) (outputLoss := localLoss)
      (coefficient := coefficient) fineShading}
    {hdelta : 0 < delta}
    {rebalanced : Proposition63InitialRebalancedData original initial hdelta}
    {hrho : 0 < rho}
    {input : Proposition63MetricFiberInputData
      (stickyLoss := stickyLoss) rebalanced hrho}
    {sourceDensity : ENNReal}
    {data : Proposition63CommonSliceRescaledData
      (Delta := Delta) (targetLoss := targetLoss) input sourceDensity}
    {hDelta : 0 < Delta} {hDeltaSmall : Delta ≤ 1 / 200}
    {hdeltaDelta : delta ≤ Delta ^ 2}
    {hdeltaRatio : delta / Delta ≤ 1 / 4}

/-- The exact public-slice estimate in the standard `(1,m,0)` chart after
transporting the whole paper shading by the globally selected chart. -/
lemma normalized_public_horizontal_slice_ad
    (selection : Proposition63ChartSelectionData data
      hDelta hDeltaSmall hdeltaDelta hdeltaRatio)
    {outputLoss : ℝ}
    (rescaled : Proposition63ChartRescaledData selection outputLoss)
    (slopes : Proposition63SlopeData selection)
    (hrhoDelta : rho = Delta)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (height : ℝ) :
    PureWZ2PaperADSet1
      (scalarProjection
        (globalGrainDirection (slopes.slope (100 * height)))
        (horizontalSlice
          (selection.chartLabel.chart.transportPaperShading
            rescaled.publicShading).union height))
      Delta (1 - sigma)
      ((2 * (Nat.ceil
          (proposition63ExactSliceError delta rho Delta coefficient / Delta) +
        1) : ENNReal) ^ 2 *
          (204 * (1 + proposition63SlabADConstant delta localLoss))) := by
  rw [selection.chartLabel.chart.normalized_horizontalSlice_projection]
  exact selection.public_horizontal_slice_chart_ad
    rescaled slopes hrhoDelta hsigma hsigmaOne height

end PureWZ2.Proposition63ChartSelectionData

end Kakeya.Assouad

end
