import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12
import MyLeanRepo.Kakeya.Assouad.TubeAlignmentGeometry
import MyLeanRepo.Kakeya.Streamlined.TubeRefinement

/-!
# Canonical coaxial reanchoring

Recenter one ordinary unit-segment tube at the orthogonal projection of a
common spatial anchor onto its coaxial line.  Points of the original carrier
inside a sufficiently small anchor ball remain in the reanchored carrier.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric
open MeasureTheory

/-- Orthogonal projection of `center` onto the coaxial line of `tube`. -/
def pureWZ2ReanchoredMidpoint
    {delta : ℝ} (center : Point3) (tube : Kakeya.DeltaTube delta) :
    Point3 :=
  wz2PaperTubeMidpoint tube +
    inner ℝ (center - wz2PaperTubeMidpoint tube) tube.direction •
      tube.direction

/-- The canonical ordinary tube centered at the reanchored midpoint. -/
def pureWZ2ReanchoredTube
    {delta : ℝ} (center : Point3) (tube : Kakeya.DeltaTube delta) :
    Kakeya.DeltaTube delta where
  base :=
    pureWZ2ReanchoredMidpoint center tube -
      (1 / 2 : ℝ) • tube.direction
  direction := tube.direction
  direction_unit := tube.direction_unit

/-- Signed axial translation from the reanchored tube to the source tube. -/
def pureWZ2AxialShift
    {delta : ℝ} (center : Point3) (tube : Kakeya.DeltaTube delta) : ℝ :=
  inner ℝ (wz2PaperTubeMidpoint tube - center) tube.direction

@[simp] theorem pureWZ2ReanchoredTube_direction
    {delta : ℝ} (center : Point3) (tube : Kakeya.DeltaTube delta) :
    (pureWZ2ReanchoredTube center tube).direction = tube.direction :=
  rfl

theorem pureWZ2ReanchoredTube_midpoint
    {delta : ℝ} (center : Point3) (tube : Kakeya.DeltaTube delta) :
    wz2PaperTubeMidpoint (pureWZ2ReanchoredTube center tube) =
      pureWZ2ReanchoredMidpoint center tube := by
  simp [pureWZ2ReanchoredTube, wz2PaperTubeMidpoint]

/-- Exact same-direction axial translation provenance. -/
theorem pureWZ2ReanchoredTube_source_base
    {delta : ℝ} (center : Point3) (tube : Kakeya.DeltaTube delta) :
    tube.base =
      (pureWZ2ReanchoredTube center tube).base +
        pureWZ2AxialShift center tube •
          (pureWZ2ReanchoredTube center tube).direction := by
  have hmid :
      tube.base =
        wz2PaperTubeMidpoint tube -
          (1 / 2 : ℝ) • tube.direction := by
    simp [wz2PaperTubeMidpoint]
  rw [hmid]
  simp only [pureWZ2ReanchoredTube, pureWZ2AxialShift,
    pureWZ2ReanchoredMidpoint]
  have hinner :
      inner ℝ (wz2PaperTubeMidpoint tube - center) tube.direction =
        -inner ℝ (center - wz2PaperTubeMidpoint tube) tube.direction := by
    rw [show wz2PaperTubeMidpoint tube - center =
      -(center - wz2PaperTubeMidpoint tube) by abel, inner_neg_left]
  rw [hinner]
  module

/-- The source midpoint is the same axial translate of the reanchored midpoint. -/
theorem pureWZ2ReanchoredTube_source_midpoint
    {delta : ℝ} (center : Point3)
    (tube : Kakeya.DeltaTube delta) :
    wz2PaperTubeMidpoint tube =
      wz2PaperTubeMidpoint
          (pureWZ2ReanchoredTube center tube) +
        pureWZ2AxialShift center tube • tube.direction := by
  rw [pureWZ2ReanchoredTube_midpoint]
  simp only [pureWZ2ReanchoredMidpoint,
    pureWZ2AxialShift]
  have hinner :
      inner ℝ (wz2PaperTubeMidpoint tube - center)
          tube.direction =
        -inner ℝ
          (center - wz2PaperTubeMidpoint tube)
          tube.direction := by
    rw [show wz2PaperTubeMidpoint tube - center =
      -(center - wz2PaperTubeMidpoint tube) by abel,
      inner_neg_left]
  rw [hinner]
  module

private lemma pureWZ2_inner_abs_le_dist
    (first second direction : Point3)
    (hdirection : ‖direction‖ = 1) :
    |inner ℝ (first - second) direction| ≤ dist first second := by
  have h :=
    abs_real_inner_le_norm (first - second) direction
  rw [hdirection, mul_one, ← dist_eq_norm] at h
  exact h

/--
If the source tube meets the radius-`radius` anchor ball, then its required
axial reanchoring is at most `1/2 + delta + radius`.
-/
theorem pureWZ2AxialShift_abs_le
    {delta radius : ℝ}
    (hdelta : 0 ≤ delta)
    {center : Point3} {tube : Kakeya.DeltaTube delta}
    {point : Point3}
    (hpointTube : point ∈ tube.carrier)
    (hpointBall : point ∈ Metric.closedBall center radius) :
    |pureWZ2AxialShift center tube| ≤
      1 / 2 + delta + radius := by
  rcases exists_closest_on_axis hdelta tube point hpointTube with
    ⟨parameter, hparameter, hpointAxis⟩
  let axisPoint := tube.base + parameter • tube.direction
  have hdecomp :
      wz2PaperTubeMidpoint tube - center =
        (wz2PaperTubeMidpoint tube - axisPoint) +
          (axisPoint - point) + (point - center) := by
    abel
  have hmidAxis :
      |inner ℝ
          (wz2PaperTubeMidpoint tube - axisPoint)
          tube.direction| ≤
        1 / 2 := by
    have hvector :
        wz2PaperTubeMidpoint tube - axisPoint =
          (1 / 2 - parameter : ℝ) • tube.direction := by
      dsimp only [axisPoint]
      simp [wz2PaperTubeMidpoint]
      module
    have hinner :
        inner ℝ
            (wz2PaperTubeMidpoint tube - axisPoint)
            tube.direction =
          1 / 2 - parameter := by
      rw [hvector, inner_smul_left, real_inner_self_eq_norm_sq,
        tube.direction_unit]
      simp
    rw [hinner, abs_le]
    constructor <;> linarith [hparameter.1, hparameter.2]
  have haxisPoint :
      |inner ℝ (axisPoint - point) tube.direction| ≤ delta := by
    have hdist :
        dist axisPoint point ≤ delta := by
      rwa [dist_comm]
    exact
      (pureWZ2_inner_abs_le_dist axisPoint point tube.direction
        tube.direction_unit).trans hdist
  have hcenter :
      |inner ℝ (point - center) tube.direction| ≤ radius := by
    have hdist :
        dist point center ≤ radius := by
      simpa [Metric.mem_closedBall] using hpointBall
    exact
      (pureWZ2_inner_abs_le_dist point center tube.direction
        tube.direction_unit).trans hdist
  change
    |inner ℝ (wz2PaperTubeMidpoint tube - center) tube.direction| ≤ _
  rw [hdecomp, inner_add_left, inner_add_left]
  calc
    |inner ℝ
          (wz2PaperTubeMidpoint tube - axisPoint)
          tube.direction +
        inner ℝ (axisPoint - point) tube.direction +
        inner ℝ (point - center) tube.direction|
        ≤
      |inner ℝ
          (wz2PaperTubeMidpoint tube - axisPoint)
          tube.direction| +
        |inner ℝ (axisPoint - point) tube.direction| +
        |inner ℝ (point - center) tube.direction| := by
          exact abs_add_three _ _ _
    _ ≤ 1 / 2 + delta + radius := by gcongr

/--
Every source-carrier point in the small anchor ball belongs to the canonical
reanchored carrier.
-/
theorem pureWZ2_mem_reanchoredCarrier
    {delta radius : ℝ}
    (hdelta : 0 ≤ delta)
    (hradius : 0 ≤ radius)
    (hsmall : delta + radius ≤ 1 / 2)
    {center : Point3} {tube : Kakeya.DeltaTube delta}
    {point : Point3}
    (hpointTube : point ∈ tube.carrier)
    (hpointBall : point ∈ Metric.closedBall center radius) :
    point ∈ (pureWZ2ReanchoredTube center tube).carrier := by
  rcases exists_closest_on_axis hdelta tube point hpointTube with
    ⟨parameter, hparameter, hpointAxis⟩
  let axisPoint := tube.base + parameter • tube.direction
  let reanchored := pureWZ2ReanchoredTube center tube
  let reanchoredMidpoint := pureWZ2ReanchoredMidpoint center tube
  have horthogonal :
      inner ℝ (center - reanchoredMidpoint) tube.direction = 0 := by
    dsimp only [reanchoredMidpoint, pureWZ2ReanchoredMidpoint]
    rw [show center -
        (wz2PaperTubeMidpoint tube +
          inner ℝ (center - wz2PaperTubeMidpoint tube) tube.direction •
            tube.direction) =
      (center - wz2PaperTubeMidpoint tube) -
        inner ℝ (center - wz2PaperTubeMidpoint tube) tube.direction •
          tube.direction by abel,
      inner_sub_left, inner_smul_left, real_inner_self_eq_norm_sq,
      tube.direction_unit]
    simp
  let localParameter :=
    1 / 2 +
      inner ℝ (axisPoint - reanchoredMidpoint) tube.direction
  have hlocalBound :
      |inner ℝ (axisPoint - reanchoredMidpoint) tube.direction| ≤
        delta + radius := by
    have hdecomp :
        axisPoint - reanchoredMidpoint =
          (axisPoint - point) + (point - center) +
            (center - reanchoredMidpoint) := by
      abel
    have haxisPoint :
        |inner ℝ (axisPoint - point) tube.direction| ≤ delta := by
      have hdist :
          dist axisPoint point ≤ delta := by
        rwa [dist_comm]
      exact
        (pureWZ2_inner_abs_le_dist axisPoint point tube.direction
          tube.direction_unit).trans hdist
    have hcenter :
        |inner ℝ (point - center) tube.direction| ≤ radius := by
      have hdist :
          dist point center ≤ radius := by
        simpa [Metric.mem_closedBall] using hpointBall
      exact
        (pureWZ2_inner_abs_le_dist point center tube.direction
          tube.direction_unit).trans hdist
    rw [hdecomp, inner_add_left, inner_add_left, horthogonal, add_zero]
    calc
      |inner ℝ (axisPoint - point) tube.direction +
          inner ℝ (point - center) tube.direction|
          ≤
        |inner ℝ (axisPoint - point) tube.direction| +
          |inner ℝ (point - center) tube.direction| :=
            abs_add_le _ _
      _ ≤ delta + radius := add_le_add haxisPoint hcenter
  have hlocalParameter : localParameter ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp only [localParameter]
    have habs := abs_le.mp (hlocalBound.trans hsmall)
    constructor <;> linarith
  have haxisIn :
      axisPoint ∈
        Kakeya.unitSegment reanchored.base reanchored.direction := by
    refine ⟨localParameter, hlocalParameter, ?_⟩
    have hmid :
        wz2PaperTubeMidpoint reanchored = reanchoredMidpoint := by
      exact pureWZ2ReanchoredTube_midpoint center tube
    have hbase :
        reanchored.base =
          reanchoredMidpoint -
            (1 / 2 : ℝ) • tube.direction := by
      rfl
    have hparallel :
        axisPoint - reanchoredMidpoint =
          inner ℝ (axisPoint - reanchoredMidpoint) tube.direction •
            tube.direction := by
      have haxis :
          axisPoint - wz2PaperTubeMidpoint tube =
            (parameter - 1 / 2 : ℝ) • tube.direction := by
        dsimp only [axisPoint]
        simp [wz2PaperTubeMidpoint]
        module
      have hcenterProjection :
          reanchoredMidpoint - wz2PaperTubeMidpoint tube =
            inner ℝ (center - wz2PaperTubeMidpoint tube) tube.direction •
              tube.direction := by
        dsimp only [reanchoredMidpoint, pureWZ2ReanchoredMidpoint]
        abel
      have hvector :
          axisPoint - reanchoredMidpoint =
            ((parameter - 1 / 2) -
              inner ℝ (center - wz2PaperTubeMidpoint tube) tube.direction) •
                tube.direction := by
        rw [show axisPoint - reanchoredMidpoint =
          (axisPoint - wz2PaperTubeMidpoint tube) -
            (reanchoredMidpoint - wz2PaperTubeMidpoint tube) by abel,
          haxis, hcenterProjection]
        module
      rw [hvector, inner_smul_left, real_inner_self_eq_norm_sq,
        tube.direction_unit]
      simp
    rw [hbase]
    dsimp only [localParameter]
    rw [pureWZ2ReanchoredTube_direction]
    calc
      reanchoredMidpoint - (1 / 2 : ℝ) • tube.direction +
          (1 / 2 +
            inner ℝ (axisPoint - reanchoredMidpoint) tube.direction) •
            tube.direction =
        reanchoredMidpoint +
          inner ℝ (axisPoint - reanchoredMidpoint) tube.direction •
            tube.direction := by module
      _ = reanchoredMidpoint +
          (axisPoint - reanchoredMidpoint) := by rw [← hparallel]
      _ = axisPoint := by abel
  exact
    Metric.mem_cthickening_of_dist_le
      point axisPoint delta
      (Kakeya.unitSegment reanchored.base reanchored.direction)
      haxisIn hpointAxis

/-- Indexed localized reanchoring with exact source provenance. -/
structure PureWZ2LocalizedReanchoringData
    {delta : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    (sourceShading : Kakeya.Streamlined.TubeShading source)
    (selected : Kakeya.Streamlined.TubeSubfamily source)
    (center : Point3)
    (radius : ℝ) where
  family : Kakeya.Streamlined.TubeFamily delta
  sourceIndex : Fin family.card ↪ Fin source.card
  axialShift : Fin family.card → ℝ
  direction_eq :
    ∀ index,
      (family.tube index).direction =
        (source.tube (sourceIndex index)).direction
  source_base_eq :
    ∀ index,
      (source.tube (sourceIndex index)).base =
        (family.tube index).base +
          axialShift index • (family.tube index).direction
  axialShift_bound :
    ∀ index, |axialShift index| ≤ 1
  shading : Kakeya.Streamlined.TubeShading family
  shading_carrier :
    ∀ index,
      shading.carrier index =
        sourceShading.carrier (sourceIndex index) ∩
          Metric.closedBall center radius
  subshading :
    ∀ index,
      shading.carrier index ⊆
        sourceShading.carrier (sourceIndex index)
  mass_eq :
    shading.mass =
      ∑ index : Fin selected.family.card,
        volume
          (sourceShading.carrier (selected.embedding index) ∩
            Metric.closedBall center radius)

/--
Build the indexed reanchored family on any selected source indices whose
localized shading is nonempty.
-/
def pureWZ2LocalizedReanchoring
    {delta radius : ℝ}
    (hdelta : 0 ≤ delta)
    (hradius : 0 ≤ radius)
    (hsmall : delta + radius ≤ 1 / 2)
    {source : Kakeya.Streamlined.TubeFamily delta}
    (sourceShading : Kakeya.Streamlined.TubeShading source)
    (selected : Kakeya.Streamlined.TubeSubfamily source)
    (center : Point3)
    (hselected :
      ∀ index : Fin selected.family.card,
        (sourceShading.carrier (selected.embedding index) ∩
          Metric.closedBall center radius).Nonempty) :
    PureWZ2LocalizedReanchoringData
      sourceShading selected center radius := by
  let family : Kakeya.Streamlined.TubeFamily delta :=
    { card := selected.family.card
      tube := fun index =>
        pureWZ2ReanchoredTube center
          (source.tube (selected.embedding index)) }
  let shading : Kakeya.Streamlined.TubeShading family :=
    { carrier := fun index =>
        sourceShading.carrier (selected.embedding index) ∩
          Metric.closedBall center radius
      measurable_carrier := fun index =>
        (sourceShading.measurable_carrier
          (selected.embedding index)).inter
            measurableSet_closedBall
      subset_body := by
        intro index point hpoint
        exact
          pureWZ2_mem_reanchoredCarrier
            hdelta hradius hsmall
            (sourceShading.subset_body
              (selected.embedding index) hpoint.1)
            hpoint.2 }
  refine
    { family := family
      sourceIndex := selected.embedding
      axialShift := fun index =>
        pureWZ2AxialShift center
          (source.tube (selected.embedding index))
      direction_eq := ?_
      source_base_eq := ?_
      axialShift_bound := ?_
      shading := shading
      shading_carrier := ?_
      subshading := ?_
      mass_eq := ?_ }
  · intro index
    rfl
  · intro index
    exact
      pureWZ2ReanchoredTube_source_base center
        (source.tube (selected.embedding index))
  · intro index
    rcases hselected index with ⟨point, hpoint⟩
    exact
      (pureWZ2AxialShift_abs_le
        hdelta
        (sourceShading.subset_body
          (selected.embedding index) hpoint.1)
        hpoint.2).trans (by
          linarith)
  · intro index
    rfl
  · intro index point hpoint
    exact hpoint.1
  · rfl

end Kakeya.Assouad

end
