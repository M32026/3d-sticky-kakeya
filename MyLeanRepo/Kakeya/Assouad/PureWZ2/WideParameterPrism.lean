import MyLeanRepo.Kakeya.Assouad.Targets.TubeParameterPrismGeometry
import MyLeanRepo.Kakeya.Assouad.AnisotropicRescaling.TubeParameters
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12RescalingBridge

/-!
# A bounded-base parameter prism for complete ordinary tubes
-/

noncomputable section

open MeasureTheory Set

namespace Kakeya.Assouad

def wideTubeParameterPrism (params : TubeParams) (radius : ℝ) : Set Point3 :=
  {point |
    point (2 : Fin 3) ∈ Set.Icc (-6 : ℝ) 6 ∧
      |point 0 - (params.a + params.c * point 2)| ≤ radius ∧
      |point 1 - (params.b + params.d * point 2)| ≤ radius}

private noncomputable def stretchVerticalSix : Point3 ≃ₗ[ℝ] Point3 where
  toFun point := point3 (point 0) (point 1) (6 * point 2)
  invFun point := point3 (point 0) (point 1) (point 2 / 6)
  left_inv point := by
    ext i
    fin_cases i <;> simp [point3] <;> ring
  right_inv point := by
    ext i
    fin_cases i <;> simp [point3] <;> ring
  map_add' first second := by
    ext i
    fin_cases i <;> simp [point3] <;> ring
  map_smul' scalar point := by
    ext i
    fin_cases i <;> simp [point3] <;> ring

private lemma stretchVerticalSix_apply
    (point : Point3) :
    stretchVerticalSix point = point3 (point 0) (point 1) (6 * point 2) :=
  rfl

private lemma stretchVerticalSix_det :
    LinearMap.det (stretchVerticalSix : Point3 →ₗ[ℝ] Point3) = 6 := by
  let diagonal : Fin 3 → ℝ := ![1, 1, 6]
  have heq : (stretchVerticalSix : Point3 →ₗ[ℝ] Point3) =
      Matrix.toLpLin 2 2 (Matrix.diagonal diagonal) := by
    ext point coordinate
    have hmatrix : WithLp.ofLp
        ((Matrix.toLpLin 2 2 (Matrix.diagonal diagonal)) point) =
        (Matrix.diagonal diagonal).mulVec (WithLp.ofLp point) :=
      Matrix.ofLp_toLpLin (p := (2 : ENNReal)) (q := (2 : ENNReal))
        (Matrix.diagonal diagonal) point
    have hcoord := congr_fun hmatrix coordinate
    rw [Matrix.mulVec_diagonal] at hcoord
    fin_cases coordinate <;>
      simp [stretchVerticalSix, point3, diagonal] at hcoord ⊢ <;>
      exact hcoord.symm
  rw [heq, LinearMap.det_toLpLin 2 (Matrix.diagonal diagonal),
    Matrix.det_diagonal]
  simp [diagonal, Fin.prod_univ_succ]

lemma wideTubeParameterPrism_geometry
    (params : TubeParams) (radius : ℝ) (hradius : 0 ≤ radius) :
    Convex ℝ (wideTubeParameterPrism params radius) ∧
      volume (wideTubeParameterPrism params radius) ≤
        ENNReal.ofReal (48 * radius ^ 2) := by
  let scaled : TubeParams :=
    { a := params.a, b := params.b, c := 6 * params.c, d := 6 * params.d }
  let standard := tubeParameterPrism scaled radius
  have himage : wideTubeParameterPrism params radius =
      stretchVerticalSix '' standard := by
    ext point
    constructor
    · intro hp
      let source := stretchVerticalSix.symm point
      refine ⟨source, ?_, stretchVerticalSix.apply_symm_apply point⟩
      have hs0 : source 0 = point 0 := by simp [source, stretchVerticalSix, point3]
      have hs1 : source 1 = point 1 := by simp [source, stretchVerticalSix, point3]
      have hs2 : source 2 = point 2 / 6 := by simp [source, stretchVerticalSix, point3]
      rcases hp with ⟨hz, hx, hy⟩
      constructor
      · rw [hs2]
        constructor <;> linarith [hz.1, hz.2]
      constructor
      · rw [hs0, hs2]
        convert hx using 1 <;> simp [scaled] <;> ring
      · rw [hs1, hs2]
        convert hy using 1 <;> simp [scaled] <;> ring
    · rintro ⟨source, hs, rfl⟩
      rcases hs with ⟨hz, hx, hy⟩
      have h0 : (stretchVerticalSix source) 0 = source 0 := by
        simp [stretchVerticalSix, point3]
      have h1 : (stretchVerticalSix source) 1 = source 1 := by
        simp [stretchVerticalSix, point3]
      have h2 : (stretchVerticalSix source) 2 = 6 * source 2 := by
        simp [stretchVerticalSix, point3]
      constructor
      · rw [h2]
        constructor <;> linarith [hz.1, hz.2]
      constructor
      · rw [h0, h2]
        convert hx using 1 <;> simp [scaled] <;> ring
      · rw [h1, h2]
        convert hy using 1 <;> simp [scaled] <;> ring
  have hstandard := tube_parameter_prism_geometry scaled radius hradius
  constructor
  · rw [himage]
    exact hstandard.1.linear_image stretchVerticalSix.toLinearMap
  · rw [himage]
    have hvolume : volume (stretchVerticalSix '' standard) =
        ENNReal.ofReal 6 * volume standard := by
      change volume ((stretchVerticalSix : Point3 →ₗ[ℝ] Point3) '' standard) = _
      rw [MeasureTheory.Measure.addHaar_image_linearMap volume
        (stretchVerticalSix : Point3 →ₗ[ℝ] Point3) standard,
        stretchVerticalSix_det]
      norm_num
    rw [hvolume]
    calc
      ENNReal.ofReal 6 * volume standard
          ≤ ENNReal.ofReal 6 * ENNReal.ofReal (8 * radius ^ 2) := by
            gcongr
            simpa [standard] using hstandard.2
      _ = ENNReal.ofReal (48 * radius ^ 2) := by
            rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 6)]
            congr 1
            ring

lemma parameter_cluster_carrier_subset_widePrism
    {delta r : ℝ} (hdelta : 0 < delta) (hdelta_r : delta ≤ r)
    (hr_one : r ≤ 1)
    {F : Kakeya.Streamlined.TubeFamily delta}
    (hbase : HasBoundedBase F 4)
    (hvertical : IsInVerticalChart F)
    (reference index : Fin F.card)
    (hcluster :
      |(tubeParams index).a - (tubeParams reference).a| ≤ r ∧
      |(tubeParams index).b - (tubeParams reference).b| ≤ r ∧
      |(tubeParams index).c - (tubeParams reference).c| ≤ r ∧
      |(tubeParams index).d - (tubeParams reference).d| ≤ r) :
    (F.tube index).carrier ⊆
      wideTubeParameterPrism (tubeParams reference) (10 * r) := by
  intro point hpoint
  let tube := F.tube index
  have hsegment : IsCompact
      (Kakeya.unitSegment tube.base tube.direction) := by
    apply IsCompact.image isCompact_Icc
    fun_prop
  change point ∈ Metric.cthickening delta
    (Kakeya.unitSegment tube.base tube.direction) at hpoint
  rw [hsegment.cthickening_eq_biUnion_closedBall hdelta.le] at hpoint
  rcases Set.mem_iUnion₂.mp hpoint with ⟨axisPoint, haxis, hpointAxis⟩
  rcases haxis with ⟨parameter, hparameter, haxisEq⟩
  have haxisLine : axisPoint ∈ tubeAxisLine tube :=
    ⟨parameter, haxisEq.symm⟩
  have hverticalNe : tube.direction 2 ≠ 0 := by
    intro hzero
    have h := hvertical index
    rw [hzero] at h
    norm_num at h
  have haxis0 := tubeAxisLine_coord_zero tube hverticalNe haxisLine
  have haxis1 := tubeAxisLine_coord_one tube hverticalNe haxisLine
  change axisPoint 0 = (tubeParams index).a +
    (tubeParams index).c * axisPoint 2 at haxis0
  change axisPoint 1 = (tubeParams index).b +
    (tubeParams index).d * axisPoint 2 at haxis1
  have hpointDist : dist point axisPoint ≤ delta := by
    simpa [Metric.mem_closedBall] using hpointAxis
  have hcoord : ∀ coordinate : Fin 3,
      |point coordinate - axisPoint coordinate| ≤ delta := by
    intro coordinate
    exact (PiLp.norm_apply_le (point - axisPoint) coordinate).trans
      (by simpa [dist_eq_norm] using hpointDist)
  have hpointZ : |point 2| ≤ 6 := by
    have hbaseZ : |tube.base 2| ≤ 4 :=
      (PiLp.norm_apply_le tube.base 2).trans (hbase index)
    have hdirZ : |tube.direction 2| ≤ 1 := by
      exact (PiLp.norm_apply_le tube.direction 2).trans_eq tube.direction_unit
    have haxisZ : |axisPoint 2| ≤ 5 := by
      rw [← haxisEq]
      have hp : |parameter| ≤ 1 := abs_le.mpr
        ⟨by linarith [hparameter.1], hparameter.2⟩
      calc
        |(tube.base + parameter • tube.direction) 2|
            ≤ |tube.base 2| + |parameter| * |tube.direction 2| := by
              simpa [abs_mul] using abs_add_le (tube.base 2)
                (parameter * tube.direction 2)
        _ ≤ 4 + 1 * 1 := by gcongr
        _ = 5 := by norm_num
    calc
      |point 2| ≤ |axisPoint 2| + |point 2 - axisPoint 2| := by
        have := abs_add_le (axisPoint 2) (point 2 - axisPoint 2)
        simpa [add_sub_cancel] using this
      _ ≤ 5 + delta := by
        exact add_le_add haxisZ (hcoord 2)
      _ ≤ 6 := by linarith [hdelta_r, hr_one]
  have hslope := tubeParams_cd_bounds hvertical index
  have hx : |point 0 -
      ((tubeParams reference).a + (tubeParams reference).c * point 2)| ≤
      10 * r := by
    have hdecomp : point 0 -
        ((tubeParams reference).a + (tubeParams reference).c * point 2) =
      (point 0 - axisPoint 0) +
        ((tubeParams index).a - (tubeParams reference).a) +
        (tubeParams index).c * (axisPoint 2 - point 2) +
        ((tubeParams index).c - (tubeParams reference).c) * point 2 := by
      rw [haxis0]
      ring
    rw [hdecomp]
    have habs :
        |(point 0 - axisPoint 0) +
            ((tubeParams index).a - (tubeParams reference).a) +
            (tubeParams index).c * (axisPoint 2 - point 2) +
            ((tubeParams index).c - (tubeParams reference).c) * point 2|
          ≤ |point 0 - axisPoint 0| +
              |(tubeParams index).a - (tubeParams reference).a| +
              |(tubeParams index).c| * |axisPoint 2 - point 2| +
              |(tubeParams index).c - (tubeParams reference).c| * |point 2| := by
      calc
        _ ≤ |(point 0 - axisPoint 0) +
              ((tubeParams index).a - (tubeParams reference).a) +
              (tubeParams index).c * (axisPoint 2 - point 2)| +
              |((tubeParams index).c - (tubeParams reference).c) * point 2| :=
                abs_add_le _ _
        _ ≤ (|(point 0 - axisPoint 0) +
              ((tubeParams index).a - (tubeParams reference).a)| +
              |(tubeParams index).c * (axisPoint 2 - point 2)|) +
              |((tubeParams index).c - (tubeParams reference).c) * point 2| := by
                gcongr
                exact abs_add_le _ _
        _ ≤ ((|point 0 - axisPoint 0| +
              |(tubeParams index).a - (tubeParams reference).a|) +
              |(tubeParams index).c * (axisPoint 2 - point 2)|) +
              |((tubeParams index).c - (tubeParams reference).c) * point 2| := by
                gcongr
                exact abs_add_le _ _
        _ = _ := by rw [abs_mul, abs_mul]
    calc
      |(point 0 - axisPoint 0) +
          ((tubeParams index).a - (tubeParams reference).a) +
          (tubeParams index).c * (axisPoint 2 - point 2) +
          ((tubeParams index).c - (tubeParams reference).c) * point 2|
        ≤ |point 0 - axisPoint 0| +
            |(tubeParams index).a - (tubeParams reference).a| +
            |(tubeParams index).c| * |axisPoint 2 - point 2| +
            |(tubeParams index).c - (tubeParams reference).c| * |point 2| := by
              exact habs
      _ ≤ delta + r + 2 * delta + r * 6 := by
            have haxisPoint : |axisPoint 2 - point 2| ≤ delta := by
              simpa [abs_sub_comm] using hcoord 2
            have hcoord0 := hcoord 0
            gcongr <;> linarith [hcluster.1, hcluster.2.2.1, hslope.1, hpointZ]
      _ ≤ 10 * r := by linarith
  have hy : |point 1 -
      ((tubeParams reference).b + (tubeParams reference).d * point 2)| ≤
      10 * r := by
    have hdecomp : point 1 -
        ((tubeParams reference).b + (tubeParams reference).d * point 2) =
      (point 1 - axisPoint 1) +
        ((tubeParams index).b - (tubeParams reference).b) +
        (tubeParams index).d * (axisPoint 2 - point 2) +
        ((tubeParams index).d - (tubeParams reference).d) * point 2 := by
      rw [haxis1]
      ring
    rw [hdecomp]
    have habs :
        |(point 1 - axisPoint 1) +
            ((tubeParams index).b - (tubeParams reference).b) +
            (tubeParams index).d * (axisPoint 2 - point 2) +
            ((tubeParams index).d - (tubeParams reference).d) * point 2|
          ≤ |point 1 - axisPoint 1| +
              |(tubeParams index).b - (tubeParams reference).b| +
              |(tubeParams index).d| * |axisPoint 2 - point 2| +
              |(tubeParams index).d - (tubeParams reference).d| * |point 2| := by
      calc
        _ ≤ |(point 1 - axisPoint 1) +
              ((tubeParams index).b - (tubeParams reference).b) +
              (tubeParams index).d * (axisPoint 2 - point 2)| +
              |((tubeParams index).d - (tubeParams reference).d) * point 2| :=
                abs_add_le _ _
        _ ≤ (|(point 1 - axisPoint 1) +
              ((tubeParams index).b - (tubeParams reference).b)| +
              |(tubeParams index).d * (axisPoint 2 - point 2)|) +
              |((tubeParams index).d - (tubeParams reference).d) * point 2| := by
                gcongr
                exact abs_add_le _ _
        _ ≤ ((|point 1 - axisPoint 1| +
              |(tubeParams index).b - (tubeParams reference).b|) +
              |(tubeParams index).d * (axisPoint 2 - point 2)|) +
              |((tubeParams index).d - (tubeParams reference).d) * point 2| := by
                gcongr
                exact abs_add_le _ _
        _ = _ := by rw [abs_mul, abs_mul]
    calc
      |(point 1 - axisPoint 1) +
          ((tubeParams index).b - (tubeParams reference).b) +
          (tubeParams index).d * (axisPoint 2 - point 2) +
          ((tubeParams index).d - (tubeParams reference).d) * point 2|
        ≤ |point 1 - axisPoint 1| +
            |(tubeParams index).b - (tubeParams reference).b| +
            |(tubeParams index).d| * |axisPoint 2 - point 2| +
            |(tubeParams index).d - (tubeParams reference).d| * |point 2| := by
              exact habs
      _ ≤ delta + r + 2 * delta + r * 6 := by
            have haxisPoint : |axisPoint 2 - point 2| ≤ delta := by
              simpa [abs_sub_comm] using hcoord 2
            have hcoord1 := hcoord 1
            gcongr <;> linarith [hcluster.2.1, hcluster.2.2.2, hslope.2, hpointZ]
      _ ≤ 10 * r := by linarith
  exact ⟨abs_le.mp hpointZ, hx, hy⟩

end Kakeya.Assouad

end
