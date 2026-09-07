import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.CroppedConvexOverload
import MyLeanRepo.Kakeya.Assouad.Targets.TubeParameterPrismGeometry

/-!
# Paper-carrier parameter Frostman control

This is the cropped-paper analogue of the ordinary parameter-prism bridge.
It counts the literal full-line paper bodies in `wz1PaperBodyFamily`; no
ordinary `DeltaTube.carrier`, unit-ball containment, or tube-volume
normalization enters the argument.

A four-parameter cluster of width `r` lies in the parameter prism of radius
`20 * r`.  The constant absorbs the `6 * delta` paper thickness on both the
point and its axis projection, the vertical-chart slope bound, and the
parameter displacement on the height window `[-1, 1]`.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

/--
Every literal paper carrier in one four-parameter cluster lies in a common
affine parameter prism.
-/
lemma paper_parameter_cluster_prism_containment
    {delta r : ℝ}
    (hdelta : 0 < delta) (hdeltaR : delta ≤ r)
    (F : Kakeya.Streamlined.TubeFamily delta)
    (hline : WZ1PaperIsLineClass F)
    (indices : Finset (Fin F.card))
    (reference : Fin F.card)
    (hcluster :
      ∀ i ∈ indices,
        |(tubeParams i).a - (tubeParams reference).a| ≤ r ∧
        |(tubeParams i).b - (tubeParams reference).b| ≤ r ∧
        |(tubeParams i).c - (tubeParams reference).c| ≤ r ∧
        |(tubeParams i).d - (tubeParams reference).d| ≤ r) :
    ∀ i ∈ indices,
      wz1PaperTubeCarrier (F.tube i) ⊆
        tubeParameterPrism (tubeParams reference) (20 * r) := by
  intro i hi point hpoint
  let tube := F.tube i
  let sourceParams := tubeParams i
  let referenceParams := tubeParams reference
  let projection :=
    tube.base +
      inner ℝ (point - tube.base) tube.direction • tube.direction

  have hvertical : IsInVerticalChart F := hline.vertical
  have hpointHeightAbs : |point (2 : Fin 3)| ≤ 1 := by
    have hbox := hpoint.2
    simpa [Kakeya.Streamlined.axisBox] using hbox.2.2
  have hpointHeight : point (2 : Fin 3) ∈ Set.Icc (-1 : ℝ) 1 :=
    abs_le.mp hpointHeightAbs

  have hprojectionDistance : ‖point - projection‖ ≤ 6 * delta := by
    exact projection_dist_bound hdelta hpoint.1
  have hprojectionAxis : projection ∈ tubeAxisLine tube := by
    refine ⟨inner ℝ (point - tube.base) tube.direction, ?_⟩
    rfl
  have htubeVertical : tube.direction (2 : Fin 3) ≠ 0 := by
    have h := hvertical i
    intro hzero
    rw [hzero] at h
    norm_num at h

  have hprojectionZero :
      projection (0 : Fin 3) =
        sourceParams.a + sourceParams.c * projection (2 : Fin 3) :=
    tubeAxisLine_coord_zero tube htubeVertical hprojectionAxis
  have hprojectionOne :
      projection (1 : Fin 3) =
        sourceParams.b + sourceParams.d * projection (2 : Fin 3) :=
    tubeAxisLine_coord_one tube htubeVertical hprojectionAxis

  have hcoordinateDistance :
      ∀ coordinate : Fin 3,
        |point coordinate - projection coordinate| ≤ 6 * delta := by
    intro coordinate
    exact (PiLp.norm_apply_le (point - projection) coordinate).trans
      hprojectionDistance

  have hsourceSlope := tubeParams_cd_bounds hvertical i
  have hclusterI := hcluster i hi

  have hcoordinateBound :
      ∀ (coordinate : Fin 3)
        (sourceIntercept referenceIntercept sourceSlope referenceSlope : ℝ),
        projection coordinate =
          sourceIntercept + sourceSlope * projection (2 : Fin 3) →
        |sourceIntercept - referenceIntercept| ≤ r →
        |sourceSlope| ≤ 2 →
        |sourceSlope - referenceSlope| ≤ r →
        |point coordinate -
            (referenceIntercept + referenceSlope * point (2 : Fin 3))| ≤
          20 * r := by
    intro coordinate sourceIntercept referenceIntercept sourceSlope
      referenceSlope hprojectionCoordinate hintercept hslope hslopeDifference
    have hprojectionHeight :
        |projection (2 : Fin 3) - point (2 : Fin 3)| ≤ 6 * delta := by
      simpa [abs_sub_comm] using hcoordinateDistance (2 : Fin 3)
    have hrNonnegative : 0 ≤ r :=
      (le_of_lt hdelta).trans hdeltaR
    have hdecomposition :
        point coordinate -
            (referenceIntercept + referenceSlope * point (2 : Fin 3)) =
          (point coordinate - projection coordinate) +
            (sourceIntercept - referenceIntercept) +
              sourceSlope *
                (projection (2 : Fin 3) - point (2 : Fin 3)) +
                  (sourceSlope - referenceSlope) * point (2 : Fin 3) := by
      rw [hprojectionCoordinate]
      ring
    have hfirst :
        |point coordinate - projection coordinate| ≤ 6 * delta :=
      hcoordinateDistance coordinate
    have hthird :
        |sourceSlope| * |projection 2 - point 2| ≤ 2 * (6 * delta) := by
      exact mul_le_mul hslope hprojectionHeight (abs_nonneg _) (by norm_num)
    have hfourth :
        |sourceSlope - referenceSlope| * |point 2| ≤ r * 1 := by
      exact mul_le_mul hslopeDifference hpointHeightAbs (abs_nonneg _)
        hrNonnegative
    rw [hdecomposition]
    calc
      |(point coordinate - projection coordinate) +
          (sourceIntercept - referenceIntercept) +
            sourceSlope * (projection 2 - point 2) +
              (sourceSlope - referenceSlope) * point 2|
          ≤ |(point coordinate - projection coordinate) +
                (sourceIntercept - referenceIntercept) +
                  sourceSlope * (projection 2 - point 2)| +
              |(sourceSlope - referenceSlope) * point 2| :=
            abs_add_le _ _
      _ ≤ (|(point coordinate - projection coordinate) +
                (sourceIntercept - referenceIntercept)| +
              |sourceSlope * (projection 2 - point 2)|) +
            |(sourceSlope - referenceSlope) * point 2| := by
              gcongr
              exact abs_add_le _ _
      _ ≤ ((|point coordinate - projection coordinate| +
                |sourceIntercept - referenceIntercept|) +
              |sourceSlope * (projection 2 - point 2)|) +
            |(sourceSlope - referenceSlope) * point 2| := by
              gcongr
              exact abs_add_le _ _
      _ = |point coordinate - projection coordinate| +
              |sourceIntercept - referenceIntercept| +
                |sourceSlope| * |projection 2 - point 2| +
                  |sourceSlope - referenceSlope| * |point 2| := by
            rw [abs_mul, abs_mul]
      _ ≤ 6 * delta + r + 2 * (6 * delta) + r * 1 := by
            gcongr
      _ ≤ 20 * r := by linarith

  have hzero :
      |point (0 : Fin 3) -
          (referenceParams.a +
            referenceParams.c * point (2 : Fin 3))| ≤ 20 * r := by
    exact hcoordinateBound 0 sourceParams.a referenceParams.a
      sourceParams.c referenceParams.c hprojectionZero hclusterI.1
      hsourceSlope.1 hclusterI.2.2.1
  have hone :
      |point (1 : Fin 3) -
          (referenceParams.b +
            referenceParams.d * point (2 : Fin 3))| ≤ 20 * r := by
    exact hcoordinateBound 1 sourceParams.b referenceParams.b
      sourceParams.d referenceParams.d hprojectionOne hclusterI.2.1
      hsourceSlope.2 hclusterI.2.2.2
  exact ⟨hpointHeight, hzero, hone⟩

/--
The cropped paper Convex-Wolff bound implies indexed four-parameter
Frostman non-concentration.  The constant `3200 = 8 * 20^2` is the volume
constant of the common parameter prism.
-/
theorem paper_tubeParameterFrostmanBound_of_croppedConvexWolff
    {delta : ℝ} (hdelta : 0 < delta)
    (F : Kakeya.Streamlined.TubeFamily delta)
    (hline : WZ1PaperIsLineClass F)
    (C : ENNReal)
    (hcwa : WZ2PaperConvexWolffBound F C) :
    TubeParameterFrostmanBound F (3200 * C) := by
  classical
  intro r hdeltaR hrOne reference
  let indices : Finset (Fin F.card) :=
    Finset.univ.filter fun i =>
      |(tubeParams i).a - (tubeParams reference).a| ≤ r ∧
      |(tubeParams i).b - (tubeParams reference).b| ≤ r ∧
      |(tubeParams i).c - (tubeParams reference).c| ≤ r ∧
      |(tubeParams i).d - (tubeParams reference).d| ≤ r
  by_cases hr : 0 < r
  · have hcluster :
        ∀ i ∈ indices,
          |(tubeParams i).a - (tubeParams reference).a| ≤ r ∧
          |(tubeParams i).b - (tubeParams reference).b| ≤ r ∧
          |(tubeParams i).c - (tubeParams reference).c| ≤ r ∧
          |(tubeParams i).d - (tubeParams reference).d| ≤ r := by
      intro i hi
      exact (Finset.mem_filter.mp hi).2
    let prism := tubeParameterPrism (tubeParams reference) (20 * r)
    have hcontained :
        ∀ i ∈ indices, wz1PaperTubeCarrier (F.tube i) ⊆ prism := by
      exact paper_parameter_cluster_prism_containment hdelta hdeltaR F
        hline indices reference hcluster
    have hindicesSubset :
        indices ⊆
          (wz1PaperBodyFamily F).containedIndices prism := by
      intro i hi
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hcontained i hi⟩
    have hcard :
        (indices.card : ENNReal) ≤
          (wz1PaperBodyFamily F).containedCount prism := by
      change (indices.card : ENNReal) ≤
        ((wz1PaperBodyFamily F).containedIndices prism).card
      exact_mod_cast Finset.card_le_card hindicesSubset
    have hprism :=
      tube_parameter_prism_geometry
        (tubeParams reference) (20 * r) (by positivity)
    have hcount := hcwa prism hprism.1
    have hvolume :
        volume prism ≤ ENNReal.ofReal (3200 * r ^ 2) := by
      have h := hprism.2
      have heq : (8 : ℝ) * (20 * r) ^ 2 = 3200 * r ^ 2 := by ring
      simpa [prism, heq] using h
    have hmain :
        (indices.card : ENNReal) ≤
          C * ENNReal.ofReal (3200 * r ^ 2) * F.enncard := by
      calc
        (indices.card : ENNReal)
            ≤ (wz1PaperBodyFamily F).containedCount prism := hcard
        _ ≤ C * volume prism * F.enncard := hcount
        _ ≤ C * ENNReal.ofReal (3200 * r ^ 2) * F.enncard := by
          gcongr
    have hrpow :
        ENNReal.ofReal (3200 * r ^ 2) =
          3200 * Kakeya.realRpowENN r 2 := by
      have hrPow : Real.rpow r 2 = r ^ 2 := Real.rpow_two r
      simp only [Kakeya.realRpowENN, hrPow]
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3200)]
      norm_num
    rw [hrpow] at hmain
    simpa [indices, mul_assoc, mul_left_comm, mul_comm] using hmain
  · have hrNonpositive : r ≤ 0 := le_of_not_gt hr
    have hdeltaNonpositive : delta ≤ 0 := hdeltaR.trans hrNonpositive
    exact False.elim ((not_le_of_gt hdelta) hdeltaNonpositive)

/-- Parameter Frostman control for a genuine subfamily, normalized by the
ambient cardinality.  This is the form needed before public centered cleanup:
restricting the source indices does not incur an artificial ambient-to-source
cardinality ratio. -/
theorem paper_tubeParameterFrostmanBound_subfamily_ambient
    {delta : ℝ} (hdelta : 0 < delta)
    (ambient : Kakeya.Streamlined.TubeFamily delta)
    (hline : WZ1PaperIsLineClass ambient)
    (C : ENNReal)
    (hcwa : WZ2PaperConvexWolffBound ambient C)
    (source : Kakeya.Streamlined.TubeSubfamily ambient) :
    ∀ r : ℝ, delta ≤ r → r ≤ 1 →
      ∀ reference : Fin source.family.card,
        (((Finset.univ : Finset (Fin source.family.card)).filter fun i =>
          |(tubeParams (F := source.family) i).a -
              (tubeParams (F := source.family) reference).a| ≤ r ∧
          |(tubeParams (F := source.family) i).b -
              (tubeParams (F := source.family) reference).b| ≤ r ∧
          |(tubeParams (F := source.family) i).c -
              (tubeParams (F := source.family) reference).c| ≤ r ∧
          |(tubeParams (F := source.family) i).d -
              (tubeParams (F := source.family) reference).d| ≤ r).card :
            ENNReal) ≤
          (3200 * C) * Kakeya.realRpowENN r 2 * ambient.enncard := by
  intro r hdeltaR hrOne reference
  let sourceCluster : Finset (Fin source.family.card) :=
    (Finset.univ : Finset (Fin source.family.card)).filter fun i =>
      |(tubeParams (F := source.family) i).a -
          (tubeParams (F := source.family) reference).a| ≤ r ∧
      |(tubeParams (F := source.family) i).b -
          (tubeParams (F := source.family) reference).b| ≤ r ∧
      |(tubeParams (F := source.family) i).c -
          (tubeParams (F := source.family) reference).c| ≤ r ∧
      |(tubeParams (F := source.family) i).d -
          (tubeParams (F := source.family) reference).d| ≤ r
  let ambientCluster : Finset (Fin ambient.card) :=
    (Finset.univ : Finset (Fin ambient.card)).filter fun i =>
      |(tubeParams (F := ambient) i).a -
          (tubeParams (F := ambient) (source.embedding reference)).a| ≤ r ∧
      |(tubeParams (F := ambient) i).b -
          (tubeParams (F := ambient) (source.embedding reference)).b| ≤ r ∧
      |(tubeParams (F := ambient) i).c -
          (tubeParams (F := ambient) (source.embedding reference)).c| ≤ r ∧
      |(tubeParams (F := ambient) i).d -
          (tubeParams (F := ambient) (source.embedding reference)).d| ≤ r
  have hmap : sourceCluster.map source.embedding ⊆ ambientCluster := by
    intro ambientIndex hindex
    rcases Finset.mem_map.mp hindex with ⟨sourceIndex, hsourceIndex, rfl⟩
    have hcluster := (Finset.mem_filter.mp hsourceIndex).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa only [tubeParams, source.tube_eq] using hcluster
  have hcard : (sourceCluster.card : ENNReal) ≤
      (ambientCluster.card : ENNReal) := by
    rw [← Finset.card_map]
    exact_mod_cast Finset.card_le_card hmap
  have hambient :=
    paper_tubeParameterFrostmanBound_of_croppedConvexWolff
      hdelta ambient hline C hcwa r hdeltaR hrOne
        (source.embedding reference)
  exact hcard.trans <| by
    simpa [ambientCluster] using hambient

end Kakeya.Assouad
