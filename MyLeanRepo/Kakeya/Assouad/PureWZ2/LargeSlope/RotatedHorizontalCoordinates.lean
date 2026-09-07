import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.GlobalGrainWindowVolume
import MyLeanRepo.Kakeya.Assouad.WZ1.AnchoredRescalingGeometry
import MyLeanRepo.Kakeya.Assouad.LargeSlope.SlopeVariation
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Rotated horizontal coordinates for WZ2 Section 6

The paper rotates only the horizontal coordinates so that the global-grain
direction at the distinguished height becomes the first coordinate.  The
vertical coordinate is unchanged.  All common slices, xz-prisms, and
projected normals used below are expressed in this one coordinate frame.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

/-- Normalizing factor for the horizontal direction `(1,m,0)`. -/
def pureWZ2HorizontalNorm (m : ℝ) : ℝ := Real.sqrt (1 + m ^ 2)

lemma pureWZ2HorizontalNorm_pos (m : ℝ) : 0 < pureWZ2HorizontalNorm m := by
  apply Real.sqrt_pos.2
  nlinarith [sq_nonneg m]

lemma pureWZ2HorizontalNorm_sq (m : ℝ) :
    pureWZ2HorizontalNorm m ^ 2 = 1 + m ^ 2 := by
  exact Real.sq_sqrt (by nlinarith [sq_nonneg m])

/-- Rotate horizontal coordinates so `(1,m,0)` becomes the positive x-axis. -/
def pureWZ2HorizontalRotationLinear (m : ℝ) : Point3 →ₗ[ℝ] Point3 where
  toFun point := point3
    ((point 0 + m * point 1) / pureWZ2HorizontalNorm m)
    ((-m * point 0 + point 1) / pureWZ2HorizontalNorm m)
    (point 2)
  map_add' first second := by
    ext coordinate
    fin_cases coordinate <;> simp [point3] <;> ring
  map_smul' scalar point := by
    ext coordinate
    fin_cases coordinate <;> simp [point3] <;> ring

/-- Inverse of the horizontal rotation. -/
def pureWZ2HorizontalRotationInverseLinear (m : ℝ) : Point3 →ₗ[ℝ] Point3 where
  toFun point := point3
    ((point 0 - m * point 1) / pureWZ2HorizontalNorm m)
    ((m * point 0 + point 1) / pureWZ2HorizontalNorm m)
    (point 2)
  map_add' first second := by
    ext coordinate
    fin_cases coordinate <;> simp [point3] <;> ring
  map_smul' scalar point := by
    ext coordinate
    fin_cases coordinate <;> simp [point3] <;> ring

/-- The horizontal rotation as a linear equivalence. -/
def pureWZ2HorizontalRotationEquiv (m : ℝ) : Point3 ≃ₗ[ℝ] Point3 :=
  LinearEquiv.mk (pureWZ2HorizontalRotationLinear m)
    (pureWZ2HorizontalRotationInverseLinear m)
    (by
      intro point
      ext coordinate
      fin_cases coordinate
      · simp [pureWZ2HorizontalRotationLinear,
          pureWZ2HorizontalRotationInverseLinear, point3]
        have hs := pureWZ2HorizontalNorm_sq m
        field_simp [pureWZ2HorizontalNorm_pos m |>.ne']
        rw [hs]
        ring
      · simp [pureWZ2HorizontalRotationLinear,
          pureWZ2HorizontalRotationInverseLinear, point3]
        have hs := pureWZ2HorizontalNorm_sq m
        field_simp [pureWZ2HorizontalNorm_pos m |>.ne']
        rw [hs]
        ring
      · simp [pureWZ2HorizontalRotationLinear,
          pureWZ2HorizontalRotationInverseLinear, point3])
    (by
      intro point
      ext coordinate
      fin_cases coordinate
      · simp [pureWZ2HorizontalRotationLinear,
          pureWZ2HorizontalRotationInverseLinear, point3]
        have hs := pureWZ2HorizontalNorm_sq m
        field_simp [pureWZ2HorizontalNorm_pos m |>.ne']
        rw [hs]
        ring
      · simp [pureWZ2HorizontalRotationLinear,
          pureWZ2HorizontalRotationInverseLinear, point3]
        have hs := pureWZ2HorizontalNorm_sq m
        field_simp [pureWZ2HorizontalNorm_pos m |>.ne']
        rw [hs]
        ring
      · simp [pureWZ2HorizontalRotationLinear,
          pureWZ2HorizontalRotationInverseLinear, point3])

/-- The horizontal rotation is an isometry. -/
def pureWZ2HorizontalRotation (m : ℝ) : Point3 ≃ₗᵢ[ℝ] Point3 :=
  LinearIsometryEquiv.mk (pureWZ2HorizontalRotationEquiv m) (by
    intro point
    have hsource := point3_coord_norm_sq point
    have htarget :=
      point3_coord_norm_sq (pureWZ2HorizontalRotationEquiv m point)
    have hs := pureWZ2HorizontalNorm_sq m
    have hnorm :
        ‖pureWZ2HorizontalRotationEquiv m point‖ ^ 2 = ‖point‖ ^ 2 := by
      rw [hsource, htarget]
      simp [pureWZ2HorizontalRotationEquiv,
        pureWZ2HorizontalRotationLinear, point3]
      field_simp [pureWZ2HorizontalNorm_pos m |>.ne']
      nlinarith
    have hsourceNonneg : 0 ≤ ‖point‖ := norm_nonneg point
    have htargetNonneg :
        0 ≤ ‖pureWZ2HorizontalRotationEquiv m point‖ :=
      norm_nonneg _
    nlinarith)

@[simp] lemma pureWZ2HorizontalRotation_coord_zero (m : ℝ) (point : Point3) :
    pureWZ2HorizontalRotation m point 0 =
      (point 0 + m * point 1) / pureWZ2HorizontalNorm m := by
  simp [pureWZ2HorizontalRotation, pureWZ2HorizontalRotationEquiv,
    pureWZ2HorizontalRotationLinear, point3]

@[simp] lemma pureWZ2HorizontalRotation_coord_one (m : ℝ) (point : Point3) :
    pureWZ2HorizontalRotation m point 1 =
      (-m * point 0 + point 1) / pureWZ2HorizontalNorm m := by
  simp [pureWZ2HorizontalRotation, pureWZ2HorizontalRotationEquiv,
    pureWZ2HorizontalRotationLinear, point3]

@[simp] lemma pureWZ2HorizontalRotation_coord_two (m : ℝ) (point : Point3) :
    pureWZ2HorizontalRotation m point 2 = point 2 := by
  simp [pureWZ2HorizontalRotation, pureWZ2HorizontalRotationEquiv,
    pureWZ2HorizontalRotationLinear, point3]

/-- The rotated x-axis, expressed in the original coordinates. -/
def pureWZ2RotatedXAxis (m : ℝ) : Point3 :=
  (pureWZ2HorizontalRotation m).symm
    (EuclideanSpace.single (0 : Fin 3) (1 : ℝ))

/-- The rotated y-axis, expressed in the original coordinates. -/
def pureWZ2RotatedYAxis (m : ℝ) : Point3 :=
  (pureWZ2HorizontalRotation m).symm
    (EuclideanSpace.single (1 : Fin 3) (1 : ℝ))

lemma pureWZ2HorizontalRotation_inner_x (m : ℝ) (point : Point3) :
    inner ℝ point (pureWZ2RotatedXAxis m) =
      pureWZ2HorizontalRotation m point 0 := by
  rw [pureWZ2RotatedXAxis, ← (pureWZ2HorizontalRotation m).inner_map_map]
  simp [EuclideanSpace.inner_single_right]

lemma pureWZ2HorizontalRotation_inner_y (m : ℝ) (point : Point3) :
    inner ℝ point (pureWZ2RotatedYAxis m) =
      pureWZ2HorizontalRotation m point 1 := by
  rw [pureWZ2RotatedYAxis, ← (pureWZ2HorizontalRotation m).inner_map_map]
  simp [EuclideanSpace.inner_single_right]

lemma pureWZ2RotatedXAxis_unit (m : ℝ) :
    ‖pureWZ2RotatedXAxis m‖ = 1 := by
  rw [pureWZ2RotatedXAxis, (pureWZ2HorizontalRotation m).symm.norm_map]
  rw [PiLp.norm_single]
  norm_num

lemma pureWZ2RotatedYAxis_unit (m : ℝ) :
    ‖pureWZ2RotatedYAxis m‖ = 1 := by
  rw [pureWZ2RotatedYAxis, (pureWZ2HorizontalRotation m).symm.norm_map]
  rw [PiLp.norm_single]
  norm_num

lemma pureWZ2RotatedYAxis_vertical_zero (m : ℝ) :
    pureWZ2RotatedYAxis m 2 = 0 := by
  rw [← pureWZ2HorizontalRotation_coord_two m
    (pureWZ2RotatedYAxis m)]
  rw [pureWZ2RotatedYAxis,
    (pureWZ2HorizontalRotation m).apply_symm_apply]
  simp

/-- Genuine common slice in the rotated horizontal frame. -/
def pureWZ2RotatedYSlice (m : ℝ) (E : Set Point3) (y : ℝ) : Set Point2 :=
  pureWZ2YSlice (pureWZ2HorizontalRotation m '' E) y

/-- Spatial lift of a rotated y-coordinate window. -/
def pureWZ2RotatedYWindow (m : ℝ) (window : Set ℝ) : Set Point3 :=
  {point | pureWZ2HorizontalRotation m point 1 ∈ window}

theorem measurableSet_pureWZ2RotatedYWindow
    (m : ℝ) {window : Set ℝ} (hwindow : MeasurableSet window) :
    MeasurableSet (pureWZ2RotatedYWindow m window) := by
  exact hwindow.preimage (by fun_prop)

/-- The rotation preserves three-dimensional Lebesgue measure. -/
theorem pureWZ2HorizontalRotation_volume_image
    (m : ℝ) {E : Set Point3} (hE : MeasurableSet E) :
    volume (pureWZ2HorizontalRotation m '' E) = volume E := by
  let rotation := pureWZ2HorizontalRotation m
  have hpres : MeasurePreserving rotation volume volume :=
    LinearIsometryEquiv.measurePreserving rotation
  have himage : MeasurableSet (rotation '' E) :=
    rotation.toMeasurableEquiv.measurableSet_image.mpr hE
  have happly := Measure.map_apply (μ := volume)
    rotation.continuous.measurable himage
  rw [hpres.map_eq] at happly
  have hpre : rotation ⁻¹' (rotation '' E) = E := by
    ext point
    simp
  rw [hpre] at happly
  simpa [rotation] using happly

/-- The rotated y-coordinate of a point in the paper axis box lies in `[-2,2]`. -/
theorem pureWZ2HorizontalRotation_coord_one_mem_two
    (frameSlope : ℝ) {point : Point3}
    (hpoint : point ∈ Kakeya.Streamlined.axisBox 2 2 2) :
    pureWZ2HorizontalRotation frameSlope point 1 ∈ Set.Icc (-2 : ℝ) 2 := by
  have hcoord :
      |pureWZ2HorizontalRotation frameSlope point 1| ≤
        ‖pureWZ2HorizontalRotation frameSlope point‖ := by
    have h := PiLp.norm_apply_le
      (pureWZ2HorizontalRotation frameSlope point) (1 : Fin 3)
    exact h
  rw [(pureWZ2HorizontalRotation frameSlope).norm_map] at hcoord
  have hnormSq := point3_coord_norm_sq point
  have hx : |point 0| ≤ 1 := by
    simpa [Kakeya.Streamlined.axisBox] using hpoint.1
  have hy : |point 1| ≤ 1 := by
    simpa [Kakeya.Streamlined.axisBox] using hpoint.2.1
  have hz : |point 2| ≤ 1 := by
    simpa [Kakeya.Streamlined.axisBox] using hpoint.2.2
  have hnormSqLe : ‖point‖ ^ 2 ≤ 3 := by
    rw [hnormSq]
    have hxBounds := abs_le.mp hx
    have hyBounds := abs_le.mp hy
    have hzBounds := abs_le.mp hz
    have hxSq : (point 0) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (point 0)]
    have hySq : (point 1) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (point 1)]
    have hzSq : (point 2) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (point 2)]
    linarith
  have hnorm : ‖point‖ ≤ 2 := by
    nlinarith [norm_nonneg point]
  have habs : |pureWZ2HorizontalRotation frameSlope point 1| ≤ 2 :=
    hcoord.trans hnorm
  exact abs_le.mp habs

/-- Rotation sends a constant global grain into an axis-aligned xz-grain. -/
theorem pureWZ2HorizontalRotation_globalGrainWithConstant_subset
    (slope : SlopeFunction) {delta constant : ℝ}
    (hdelta : 0 ≤ delta) (hconstant : 0 ≤ constant)
    (anchor : Point3) :
    pureWZ2HorizontalRotation (slope (anchor 2)) ''
        pureWZ2GlobalGrainWithConstant constant slope delta anchor ⊆
      {point : Point3 |
        |point 2 - (pureWZ2HorizontalRotation
          (slope (anchor 2)) anchor) 2| ≤ constant * delta ∧
        |point 0 - (pureWZ2HorizontalRotation
          (slope (anchor 2)) anchor) 0| ≤ constant * delta} := by
  intro point hpoint
  rcases hpoint with ⟨source, hsource, rfl⟩
  let m := slope (anchor 2)
  have hnormOne : 1 ≤ pureWZ2HorizontalNorm m := by
    have hs := pureWZ2HorizontalNorm_sq m
    have hn := (pureWZ2HorizontalNorm_pos m).le
    nlinarith [sq_nonneg m]
  have hnormPos := pureWZ2HorizontalNorm_pos m
  constructor
  · simpa [m] using hsource.1
  · have hraw :
        |(source 0 + m * source 1) - (anchor 0 + m * anchor 1)| ≤
          constant * delta := by
      simpa [m, globalGrainDirection, PiLp.inner_apply,
        Fin.sum_univ_succ] using hsource.2
    have hnonneg : 0 ≤ constant * delta := mul_nonneg hconstant hdelta
    rw [pureWZ2HorizontalRotation_coord_zero,
      pureWZ2HorizontalRotation_coord_zero]
    have heq :
        (source 0 + m * source 1) / pureWZ2HorizontalNorm m -
            (anchor 0 + m * anchor 1) / pureWZ2HorizontalNorm m =
          ((source 0 + m * source 1) - (anchor 0 + m * anchor 1)) /
            pureWZ2HorizontalNorm m := by ring
    rw [heq, abs_div, abs_of_pos hnormPos]
    calc
      |(source 0 + m * source 1) - (anchor 0 + m * anchor 1)| /
          pureWZ2HorizontalNorm m
        ≤ (constant * delta) / pureWZ2HorizontalNorm m := by gcongr
      _ ≤ constant * delta := by
        exact div_le_self hnonneg hnormOne

/-- A rotated common slice of a constant global grain has area `O(delta^2)`. -/
theorem pureWZ2_rotatedYSlice_globalGrainWithConstant_volume_upper
    (slope : SlopeFunction) {delta constant : ℝ}
    (hdelta : 0 ≤ delta) (hconstant : 0 ≤ constant)
    (anchor : Point3) (y : ℝ) :
    volume (pureWZ2RotatedYSlice (slope (anchor 2))
        (pureWZ2GlobalGrainWithConstant constant slope delta anchor) y) ≤
      ENNReal.ofReal (4 * (constant * delta) ^ 2) := by
  let center := pureWZ2HorizontalRotation (slope (anchor 2)) anchor
  let rectangle : Set Point2 := {point |
    point 0 ∈ Set.Icc (center 0 - constant * delta)
      (center 0 + constant * delta) ∧
    point 1 ∈ Set.Icc (center 2 - constant * delta)
      (center 2 + constant * delta)}
  have hsubset : pureWZ2RotatedYSlice (slope (anchor 2))
      (pureWZ2GlobalGrainWithConstant constant slope delta anchor) y ⊆
      rectangle := by
    intro point hpoint
    have himage := pureWZ2_mem_ySlice_iff.mp hpoint
    have hbox := pureWZ2HorizontalRotation_globalGrainWithConstant_subset
      slope hdelta hconstant anchor himage
    dsimp only [rectangle, center]
    constructor
    · have hx : -(constant * delta) ≤
          point 0 - (pureWZ2HorizontalRotation
            (slope (anchor 2)) anchor) 0 ∧
          point 0 - (pureWZ2HorizontalRotation
            (slope (anchor 2)) anchor) 0 ≤ constant * delta := by
        exact abs_le.mp (by simpa [point3] using hbox.2)
      constructor <;> linarith
    · have hz : -(constant * delta) ≤
          point 1 - (pureWZ2HorizontalRotation
            (slope (anchor 2)) anchor) 2 ∧
          point 1 - (pureWZ2HorizontalRotation
            (slope (anchor 2)) anchor) 2 ≤ constant * delta := by
        exact abs_le.mp (by simpa [point3] using hbox.1)
      constructor <;> linarith
  have hrectangle : volume rectangle =
      ENNReal.ofReal (2 * (constant * delta)) *
        ENNReal.ofReal (2 * (constant * delta)) := by
    let lower : Fin 2 → ℝ := fun index =>
      if index = 0 then center 0 - constant * delta
      else center 2 - constant * delta
    let upper : Fin 2 → ℝ := fun index =>
      if index = 0 then center 0 + constant * delta
      else center 2 + constant * delta
    let point2Equiv : (Fin 2 → ℝ) ≃ᵐ Point2 :=
      { toFun := WithLp.toLp 2
        invFun := WithLp.ofLp
        left_inv := WithLp.ofLp_toLp (2 : ENNReal)
        right_inv := WithLp.toLp_ofLp (2 : ENNReal)
        measurable_toFun :=
          (PiLp.continuous_toLp
            (p := 2) (β := fun _ : Fin 2 => ℝ)).measurable
        measurable_invFun :=
          (PiLp.continuous_ofLp
            (p := 2) (β := fun _ : Fin 2 => ℝ)).measurable }
    have hrect : rectangle = point2Equiv '' Set.Icc lower upper := by
      ext point
      simp only [rectangle, Set.mem_setOf_eq, Set.mem_image, Set.mem_Icc]
      constructor
      · intro hp
        refine ⟨point.ofLp, ?_, ?_⟩
        constructor <;> intro index <;> fin_cases index
        · simpa [lower] using hp.1.1
        · simpa [lower] using hp.2.1
        · simpa [upper] using hp.1.2
        · simpa [upper] using hp.2.2
        · exact point2Equiv.right_inv point
      · rintro ⟨coordinates, hcoordinates, rfl⟩
        constructor
        · constructor
          · change center 0 - constant * delta ≤ coordinates 0
            simpa [lower] using hcoordinates.1 (0 : Fin 2)
          · change coordinates 0 ≤ center 0 + constant * delta
            simpa [upper] using hcoordinates.2 (0 : Fin 2)
        · constructor
          · change center 2 - constant * delta ≤ coordinates 1
            simpa [lower] using hcoordinates.1 (1 : Fin 2)
          · change coordinates 1 ≤ center 2 + constant * delta
            simpa [upper] using hcoordinates.2 (1 : Fin 2)
    rw [hrect]
    have hpres : MeasurePreserving point2Equiv volume volume :=
      PiLp.volume_preserving_toLp (ι := Fin 2)
    have hmeas : MeasurableSet (Set.Icc lower upper) := measurableSet_Icc
    have himage :
        volume (point2Equiv '' Set.Icc lower upper) =
          volume (Set.Icc lower upper) := by
      have happly := Measure.map_apply (μ := volume) hpres.measurable
        (point2Equiv.measurableSet_image.mpr hmeas)
      rw [hpres.map_eq] at happly
      have hpre : point2Equiv ⁻¹' (point2Equiv '' Set.Icc lower upper) =
          Set.Icc lower upper := by ext coordinates; simp
      rw [hpre] at happly
      exact happly
    rw [himage, Real.volume_Icc_pi, Fin.prod_univ_two]
    congr 2 <;> dsimp [lower, upper] <;> ring
  calc
    volume (pureWZ2RotatedYSlice (slope (anchor 2))
        (pureWZ2GlobalGrainWithConstant constant slope delta anchor) y)
      ≤ volume rectangle := measure_mono hsubset
    _ = ENNReal.ofReal (2 * (constant * delta)) *
        ENNReal.ofReal (2 * (constant * delta)) := hrectangle
    _ = ENNReal.ofReal (4 * (constant * delta) ^ 2) := by
      rw [← ENNReal.ofReal_mul (by positivity :
        0 ≤ 2 * (constant * delta))]
      congr 1
      ring

/-- The exceptional rotated-y window inside one constant-4 grain. -/
theorem pureWZ2_globalGrainWithConstant_four_rotated_window_volume_upper
    (slope : SlopeFunction) {delta : ℝ} (hdelta : 0 ≤ delta)
    (anchor : Point3) {window : Set ℝ} (hwindow : MeasurableSet window) :
    volume (pureWZ2GlobalGrainWithConstant 4 slope delta anchor ∩
        pureWZ2RotatedYWindow (slope (anchor 2)) window) ≤
      ENNReal.ofReal (64 * delta ^ 2) * volume window := by
  let rotation := pureWZ2HorizontalRotation (slope (anchor 2))
  let restricted := pureWZ2GlobalGrainWithConstant 4 slope delta anchor ∩
    pureWZ2RotatedYWindow (slope (anchor 2)) window
  let rotated := rotation '' restricted
  have hgrain : pureWZ2GlobalGrainWithConstant 4 slope delta anchor =
      pureWZ2GlobalGrain slope (4 * delta) anchor := by
    ext point
    simp [pureWZ2GlobalGrain, pureWZ2GlobalGrainWithConstant]
  have hrestricted : MeasurableSet restricted := by
    dsimp only [restricted]
    rw [hgrain]
    exact (measurableSet_pureWZ2GlobalGrain slope (4 * delta) anchor).inter
      (measurableSet_pureWZ2RotatedYWindow _ hwindow)
  have hrotated : MeasurableSet rotated :=
    rotation.toMeasurableEquiv.measurableSet_image.mpr hrestricted
  have hvolume : volume restricted = volume rotated :=
    (pureWZ2HorizontalRotation_volume_image _ hrestricted).symm
  have hslice : ∀ y, volume (pureWZ2YSlice rotated y) ≤
      ENNReal.ofReal (64 * delta ^ 2) := by
    intro y
    calc
      volume (pureWZ2YSlice rotated y)
        ≤ volume (pureWZ2RotatedYSlice (slope (anchor 2))
            (pureWZ2GlobalGrainWithConstant 4 slope delta anchor) y) := by
          apply measure_mono
          apply pureWZ2YSlice_mono
          exact Set.image_mono Set.inter_subset_left
      _ ≤ ENNReal.ofReal (4 * ((4 : ℝ) * delta) ^ 2) :=
        pureWZ2_rotatedYSlice_globalGrainWithConstant_volume_upper slope
          hdelta (by norm_num) anchor y
      _ = ENNReal.ofReal (64 * delta ^ 2) := by congr 1 <;> ring
  have houtside : ∀ y ∉ window, volume (pureWZ2YSlice rotated y) = 0 := by
    intro y hy
    have hempty : pureWZ2YSlice rotated y = ∅ := by
      ext point
      simp only [pureWZ2_mem_ySlice_iff, Set.notMem_empty, iff_false]
      rintro ⟨source, hsource, hsourceEq⟩
      apply hy
      have hcoordinate := hsource.2
      dsimp only [restricted, pureWZ2RotatedYWindow] at hcoordinate
      change rotation source 1 ∈ window at hcoordinate
      rw [hsourceEq] at hcoordinate
      simpa [point3, rotation] using hcoordinate
    rw [hempty, measure_empty]
  have hfull : (∫⁻ y : ℝ, volume (pureWZ2YSlice rotated y)) =
      ∫⁻ y in window, volume (pureWZ2YSlice rotated y) := by
    rw [← lintegral_indicator hwindow]
    apply lintegral_congr
    intro y
    by_cases hy : y ∈ window
    · simp [hy]
    · simp [hy, houtside y hy]
  rw [hvolume, pureWZ2_volume_eq_lintegral_ySlice rotated hrotated, hfull]
  calc
    (∫⁻ y in window, volume (pureWZ2YSlice rotated y))
      ≤ ∫⁻ _y in window, ENNReal.ofReal (64 * delta ^ 2) :=
        setLIntegral_mono' hwindow (fun y _ => hslice y)
    _ = ENNReal.ofReal (64 * delta ^ 2) * volume window := by
      rw [setLIntegral_const]

/-- The derivative of a normalized slope is one-Lipschitz on `[-1,1]`. -/
theorem pureWZ2_normalized_deriv_lipschitz
    {slope : SlopeFunction} (hnormalized : slope.IsNormalized) :
    LipschitzOnWith (1 : NNReal) (deriv slope) (Set.Icc (-1 : ℝ) 1) := by
  have hdifferentiable : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      DifferentiableAt ℝ (deriv slope) z := by
    intro z _
    have hC2 : ContDiff ℝ 2 (slope : ℝ → ℝ) := slope.contDiff
    have hC1 : ContDiff ℝ 1 (deriv slope) := hC2.deriv'
    exact (hC1.differentiable (by norm_num)).differentiableAt
  exact Convex.lipschitzOnWith_of_nnnorm_deriv_le
    hdifferentiable
    (fun z hz => by
      have hbound := (hnormalized z hz).2.2
      exact NNReal.coe_le_coe.mp (show
        (↑(‖deriv (deriv slope) z‖₊) : ℝ) ≤ 1 by
          simpa [Real.norm_eq_abs] using hbound))
    (convex_Icc (-1 : ℝ) 1)

/-- A small derivative at one slab point controls slope variation on the slab. -/
theorem pureWZ2_slope_close_to_small_derivative_anchor
    {slope : SlopeFunction} (hnormalized : slope.IsNormalized)
    {a b z0 z : ℝ}
    (ha : -1 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hz0 : z0 ∈ Set.Icc a b) (hz : z ∈ Set.Icc a b)
    (hsmall : |deriv slope z0| < b - a) :
    |slope z - slope z0| ≤ 2 * (b - a) ^ 2 := by
  have hz0Ambient : z0 ∈ Set.Icc (-1 : ℝ) 1 :=
    ⟨ha.trans hz0.1, hz0.2.trans hb⟩
  have hzAmbient : z ∈ Set.Icc (-1 : ℝ) 1 :=
    ⟨ha.trans hz.1, hz.2.trans hb⟩
  have hderivLip := pureWZ2_normalized_deriv_lipschitz hnormalized
  have hderivDistance := hderivLip.norm_sub_le hzAmbient hz0Ambient
  have hderivDiff : |deriv slope z - deriv slope z0| ≤ |z - z0| := by
    simpa [Real.norm_eq_abs, Real.dist_eq] using hderivDistance
  have hspan : |z - z0| ≤ b - a := by
    rw [abs_le]
    constructor <;> linarith [hz.1, hz.2, hz0.1, hz0.2]
  have hderiv : |deriv slope z| ≤ 2 * (b - a) := by
    calc
      |deriv slope z|
        ≤ |deriv slope z0| + |deriv slope z - deriv slope z0| := by
          calc
            |deriv slope z| =
                |deriv slope z0 + (deriv slope z - deriv slope z0)| := by
              congr 1
              ring
            _ ≤ _ := abs_add_le _ _
      _ ≤ (b - a) + (b - a) := by gcongr <;> linarith
      _ = 2 * (b - a) := by ring
  have hdifferentiable : Differentiable ℝ slope :=
    slope.contDiff.differentiable (by norm_num)
  have hslope := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := (slope : ℝ → ℝ))
    (fun point _ => hdifferentiable.differentiableAt)
    (fun point hpoint => by
      have hpointSlab : point ∈ Set.Icc a b := hpoint
      have hpointClose :=
        (pureWZ2_normalized_deriv_lipschitz hnormalized).norm_sub_le
          ⟨ha.trans hpoint.1, hpoint.2.trans hb⟩ hz0Ambient
      have hpointSpan : |point - z0| ≤ b - a := by
        rw [abs_le]
        constructor <;> linarith [hpoint.1, hpoint.2, hz0.1, hz0.2]
      have hpointDeriv : |deriv slope point| ≤ 2 * (b - a) := by
        have hdiff : |deriv slope point - deriv slope z0| ≤
            |point - z0| := by
          simpa [Real.norm_eq_abs, Real.dist_eq] using hpointClose
        calc
          |deriv slope point|
            ≤ |deriv slope z0| +
                |deriv slope point - deriv slope z0| := by
              calc
                |deriv slope point| =
                    |deriv slope z0 +
                      (deriv slope point - deriv slope z0)| := by
                  congr 1
                  ring
                _ ≤ _ := abs_add_le _ _
          _ ≤ (b - a) + (b - a) := by gcongr <;> linarith
          _ = 2 * (b - a) := by ring
      simpa [Real.norm_eq_abs] using hpointDeriv)
    (convex_Icc a b) hz0 hz
  have hdistance : |z - z0| ≤ b - a := hspan
  calc
    |slope z - slope z0| = ‖slope z - slope z0‖ := by
      simp [Real.norm_eq_abs]
    _ ≤ 2 * (b - a) * ‖z - z0‖ := hslope
    _ ≤ 2 * (b - a) * (b - a) := by
      simpa [Real.norm_eq_abs] using
        mul_le_mul_of_nonneg_left hdistance (by linarith)
    _ = 2 * (b - a) ^ 2 := by ring

/-- Fixed-rotation containment for a grain whose slope is close to the frame slope. -/
theorem pureWZ2HorizontalRotation_fixed_globalGrain_subset
    (slope : SlopeFunction) {delta : ℝ} (hdelta : 0 ≤ delta)
    {frameSlope : ℝ} (anchor : Point3)
    (hanchorBox : anchor ∈ Kakeya.Streamlined.axisBox 2 2 2)
    (hclose : |slope (anchor 2) - frameSlope| ≤ 2 * delta) :
    pureWZ2HorizontalRotation frameSlope ''
        (pureWZ2GlobalGrainWithConstant 4 slope delta anchor ∩
          Kakeya.Streamlined.axisBox 2 2 2) ⊆
      {point : Point3 |
        |point 2 - (pureWZ2HorizontalRotation frameSlope anchor) 2| ≤
            4 * delta ∧
        |point 0 - (pureWZ2HorizontalRotation frameSlope anchor) 0| ≤
            8 * delta} := by
  intro point hpoint
  rcases hpoint with ⟨source, hsource, rfl⟩
  have hnormOne : 1 ≤ pureWZ2HorizontalNorm frameSlope := by
    have hs := pureWZ2HorizontalNorm_sq frameSlope
    have hn := (pureWZ2HorizontalNorm_pos frameSlope).le
    nlinarith [sq_nonneg frameSlope]
  have hnormPos := pureWZ2HorizontalNorm_pos frameSlope
  have hsourceY : |source 1| ≤ 1 := by
    simpa [Kakeya.Streamlined.axisBox] using hsource.2.2.1
  have hanchorY : |anchor 1| ≤ 1 := by
    simpa [Kakeya.Streamlined.axisBox] using hanchorBox.2.1
  have hyDiff : |source 1 - anchor 1| ≤ 2 := by
    calc
      |source 1 - anchor 1| ≤ |source 1| + |anchor 1| := abs_sub _ _
      _ ≤ 1 + 1 := add_le_add hsourceY hanchorY
      _ = 2 := by norm_num
  constructor
  · simpa using hsource.1.1
  · let anchorSlope := slope (anchor 2)
    have hgrain :
        |(source 0 + anchorSlope * source 1) -
          (anchor 0 + anchorSlope * anchor 1)| ≤ 4 * delta := by
      simpa [anchorSlope, globalGrainDirection, PiLp.inner_apply,
        Fin.sum_univ_succ] using hsource.1.2
    have hslopeDiff : |frameSlope - anchorSlope| ≤ 2 * delta := by
      simpa [anchorSlope, abs_sub_comm] using hclose
    have hraw :
        |(source 0 + frameSlope * source 1) -
          (anchor 0 + frameSlope * anchor 1)| ≤ 8 * delta := by
      have hdecomp :
          (source 0 + frameSlope * source 1) -
              (anchor 0 + frameSlope * anchor 1) =
            ((source 0 + anchorSlope * source 1) -
              (anchor 0 + anchorSlope * anchor 1)) +
            (frameSlope - anchorSlope) * (source 1 - anchor 1) := by ring
      rw [hdecomp]
      calc
        |((source 0 + anchorSlope * source 1) -
              (anchor 0 + anchorSlope * anchor 1)) +
            (frameSlope - anchorSlope) * (source 1 - anchor 1)|
          ≤ |(source 0 + anchorSlope * source 1) -
              (anchor 0 + anchorSlope * anchor 1)| +
            |(frameSlope - anchorSlope) * (source 1 - anchor 1)| :=
              abs_add_le _ _
        _ = |(source 0 + anchorSlope * source 1) -
              (anchor 0 + anchorSlope * anchor 1)| +
            |frameSlope - anchorSlope| * |source 1 - anchor 1| := by
              rw [abs_mul]
        _ ≤ 4 * delta + (2 * delta) * 2 := by gcongr
        _ = 8 * delta := by ring
    rw [pureWZ2HorizontalRotation_coord_zero,
      pureWZ2HorizontalRotation_coord_zero]
    have heq :
        (source 0 + frameSlope * source 1) / pureWZ2HorizontalNorm frameSlope -
            (anchor 0 + frameSlope * anchor 1) / pureWZ2HorizontalNorm frameSlope =
          ((source 0 + frameSlope * source 1) -
            (anchor 0 + frameSlope * anchor 1)) /
              pureWZ2HorizontalNorm frameSlope := by ring
    rw [heq, abs_div, abs_of_pos hnormPos]
    calc
      |(source 0 + frameSlope * source 1) -
          (anchor 0 + frameSlope * anchor 1)| /
          pureWZ2HorizontalNorm frameSlope
        ≤ (8 * delta) / pureWZ2HorizontalNorm frameSlope := by gcongr
      _ ≤ 8 * delta := div_le_self (by positivity) hnormOne

/-- Pairwise fixed-frame diameter of one constant-4 global grain.  The
horizontal error is the literal grain thickness plus the frame-slope gap; no
`O(delta)` assumption on that gap is hidden in this statement. -/
theorem pureWZ2_fixedFrame_globalGrain_pair_diameter
    (slope : ℝ → ℝ) {delta gap frameSlope : ℝ}
    (hdelta : 0 ≤ delta) (hgap : 0 ≤ gap) (anchor : Point3)
    (hclose : |slope (anchor 2) - frameSlope| ≤ gap)
    {first second : Point3}
    (hfirst : first ∈ pureWZ2GlobalGrainWithConstant 4 slope delta anchor ∩
      Kakeya.Streamlined.axisBox 2 2 2)
    (hsecond : second ∈ pureWZ2GlobalGrainWithConstant 4 slope delta anchor ∩
      Kakeya.Streamlined.axisBox 2 2 2) :
    |pureWZ2HorizontalRotation frameSlope first 0 -
        pureWZ2HorizontalRotation frameSlope second 0| ≤
          8 * delta + 2 * gap ∧
      |first 2 - second 2| ≤ 8 * delta := by
  let anchorSlope := slope (anchor 2)
  have hnormOne : 1 ≤ pureWZ2HorizontalNorm frameSlope := by
    have hs := pureWZ2HorizontalNorm_sq frameSlope
    have hn := (pureWZ2HorizontalNorm_pos frameSlope).le
    nlinarith [sq_nonneg frameSlope]
  have hnormPos := pureWZ2HorizontalNorm_pos frameSlope
  have hyFirst : |first 1| ≤ 1 := by
    simpa [Kakeya.Streamlined.axisBox] using hfirst.2.2.1
  have hySecond : |second 1| ≤ 1 := by
    simpa [Kakeya.Streamlined.axisBox] using hsecond.2.2.1
  have hyDiff : |first 1 - second 1| ≤ 2 := by
    calc
      |first 1 - second 1| ≤ |first 1| + |second 1| := abs_sub _ _
      _ ≤ 1 + 1 := add_le_add hyFirst hySecond
      _ = 2 := by norm_num
  have hfirstProjection :
      |(first 0 + anchorSlope * first 1) -
        (anchor 0 + anchorSlope * anchor 1)| ≤ 4 * delta := by
    simpa [anchorSlope, globalGrainDirection, PiLp.inner_apply,
      Fin.sum_univ_succ] using hfirst.1.2
  have hsecondProjection :
      |(second 0 + anchorSlope * second 1) -
        (anchor 0 + anchorSlope * anchor 1)| ≤ 4 * delta := by
    simpa [anchorSlope, globalGrainDirection, PiLp.inner_apply,
      Fin.sum_univ_succ] using hsecond.1.2
  have hprojectionDiff :
      |(first 0 + anchorSlope * first 1) -
        (second 0 + anchorSlope * second 1)| ≤ 8 * delta := by
    calc
      |(first 0 + anchorSlope * first 1) -
          (second 0 + anchorSlope * second 1)| =
        |((first 0 + anchorSlope * first 1) -
            (anchor 0 + anchorSlope * anchor 1)) +
          ((anchor 0 + anchorSlope * anchor 1) -
            (second 0 + anchorSlope * second 1))| := by congr 1 <;> ring
      _ ≤ |(first 0 + anchorSlope * first 1) -
            (anchor 0 + anchorSlope * anchor 1)| +
          |(anchor 0 + anchorSlope * anchor 1) -
            (second 0 + anchorSlope * second 1)| := abs_add_le _ _
      _ ≤ 4 * delta + 4 * delta := by
        exact add_le_add hfirstProjection
          (by simpa [abs_sub_comm] using hsecondProjection)
      _ = 8 * delta := by ring
  have hslopeGap : |frameSlope - anchorSlope| ≤ gap := by
    simpa [anchorSlope, abs_sub_comm] using hclose
  constructor
  · rw [pureWZ2HorizontalRotation_coord_zero,
      pureWZ2HorizontalRotation_coord_zero]
    have heq :
        (first 0 + frameSlope * first 1) / pureWZ2HorizontalNorm frameSlope -
            (second 0 + frameSlope * second 1) /
              pureWZ2HorizontalNorm frameSlope =
          (((first 0 + anchorSlope * first 1) -
              (second 0 + anchorSlope * second 1)) +
            (frameSlope - anchorSlope) * (first 1 - second 1)) /
              pureWZ2HorizontalNorm frameSlope := by ring
    rw [heq, abs_div, abs_of_pos hnormPos]
    calc
      |((first 0 + anchorSlope * first 1) -
            (second 0 + anchorSlope * second 1)) +
          (frameSlope - anchorSlope) * (first 1 - second 1)| /
            pureWZ2HorizontalNorm frameSlope
        ≤ (8 * delta + gap * 2) /
            pureWZ2HorizontalNorm frameSlope := by
          apply div_le_div_of_nonneg_right _ hnormPos.le
          calc
            |((first 0 + anchorSlope * first 1) -
                  (second 0 + anchorSlope * second 1)) +
                (frameSlope - anchorSlope) * (first 1 - second 1)|
              ≤ |(first 0 + anchorSlope * first 1) -
                  (second 0 + anchorSlope * second 1)| +
                |(frameSlope - anchorSlope) * (first 1 - second 1)| :=
                  abs_add_le _ _
            _ = |(first 0 + anchorSlope * first 1) -
                  (second 0 + anchorSlope * second 1)| +
                |frameSlope - anchorSlope| * |first 1 - second 1| := by
                  rw [abs_mul]
            _ ≤ 8 * delta + gap * 2 := add_le_add hprojectionDiff
              (mul_le_mul hslopeGap hyDiff (abs_nonneg _) hgap)
      _ ≤ 8 * delta + gap * 2 :=
        div_le_self (by positivity) hnormOne
      _ = 8 * delta + 2 * gap := by ring
  · calc
      |first 2 - second 2| =
          |(first 2 - anchor 2) + (anchor 2 - second 2)| := by
            congr 1 <;> ring
      _ ≤ |first 2 - anchor 2| + |anchor 2 - second 2| := abs_add_le _ _
      _ ≤ 4 * delta + 4 * delta := by
        exact add_le_add hfirst.1.1 (by simpa [abs_sub_comm] using hsecond.1.1)
      _ = 8 * delta := by ring

/-- The rotated `x` coordinate of the central plane of one global grain,
restricted to the fixed rotated-`y` plane with coordinate `y`.  Unlike the
anchor's rotated `x` coordinate, this center follows the harmless horizontal
drift caused by using a nearby, but not `O(delta)`-near, fixed frame. -/
def pureWZ2FixedRotatedSliceCenterX
    (anchorSlope frameSlope : ℝ) (anchor : Point3) (y : ℝ) : ℝ :=
  (pureWZ2HorizontalNorm frameSlope *
      (anchor 0 + anchorSlope * anchor 1) -
    (anchorSlope - frameSlope) * y) /
      (1 + anchorSlope * frameSlope)

/-- Two-dimensional change-of-coordinates identity behind the fixed-frame
slice estimate. -/
lemma pureWZ2_fixed_rotated_slice_x_sub_center
    (anchorSlope frameSlope : ℝ) (anchor point : Point3) (y : ℝ)
    (hdenom : 1 + anchorSlope * frameSlope ≠ 0)
    (hy : pureWZ2HorizontalRotation frameSlope point 1 = y) :
    pureWZ2HorizontalRotation frameSlope point 0 -
        pureWZ2FixedRotatedSliceCenterX anchorSlope frameSlope anchor y =
      pureWZ2HorizontalNorm frameSlope *
          ((point 0 + anchorSlope * point 1) -
            (anchor 0 + anchorSlope * anchor 1)) /
        (1 + anchorSlope * frameSlope) := by
  have hnorm := pureWZ2HorizontalNorm_sq frameSlope
  have hnormNe := (pureWZ2HorizontalNorm_pos frameSlope).ne'
  have hdenom' : 1 + frameSlope * anchorSlope ≠ 0 := by
    simpa [mul_comm] using hdenom
  rw [pureWZ2HorizontalRotation_coord_zero]
  rw [pureWZ2HorizontalRotation_coord_one] at hy
  have hyRaw : -frameSlope * point 0 + point 1 =
      pureWZ2HorizontalNorm frameSlope * y := by
    simpa [mul_comm] using (div_eq_iff hnormNe).mp hy
  dsimp only [pureWZ2FixedRotatedSliceCenterX]
  field_simp [hnormNe, hdenom, hdenom']
  linear_combination
    (frameSlope - anchorSlope) * hyRaw -
      (point 0 + anchorSlope * point 1) * hnorm

/-- In a fixed horizontal frame whose slope is within `1/100` of the grain
slope, one exact rotated-`y` slice stays `O(delta)`-thin in rotated `x`. -/
theorem pureWZ2_fixed_rotatedYSlice_globalGrain_subset_rectangle
    (slope : ℝ → ℝ)
    {delta : ℝ} (hdelta : 0 ≤ delta)
    {frameSlope : ℝ} (anchor : Point3)
    (hanchorBox : anchor ∈ Kakeya.Streamlined.axisBox 2 2 2)
    (hanchorSlope : |slope (anchor 2)| ≤ 1)
    (hclose : |slope (anchor 2) - frameSlope| ≤ 1 / 100) (y : ℝ) :
    pureWZ2RotatedYSlice frameSlope
        (pureWZ2GlobalGrainWithConstant 4 slope delta anchor ∩
          Kakeya.Streamlined.axisBox 2 2 2) y ⊆
      {point : Point2 |
        point 0 ∈ Set.Icc
          (pureWZ2FixedRotatedSliceCenterX (slope (anchor 2))
            frameSlope anchor y - 8 * delta)
          (pureWZ2FixedRotatedSliceCenterX (slope (anchor 2))
            frameSlope anchor y + 8 * delta) ∧
        point 1 ∈ Set.Icc (anchor 2 - 4 * delta)
          (anchor 2 + 4 * delta)} := by
  intro slicePoint hslicePoint
  have himage := pureWZ2_mem_ySlice_iff.mp hslicePoint
  rcases himage with ⟨source, hsource, hsourceEq⟩
  have hsourceCoord := congr_arg (fun point : Point3 => point 1) hsourceEq
  have hy : pureWZ2HorizontalRotation frameSlope source 1 = y := by
    simpa [point3] using hsourceCoord
  let anchorSlope := slope (anchor 2)
  let denominator := 1 + anchorSlope * frameSlope
  have hanchorSlope' : |anchorSlope| ≤ 1 := by
    simpa [anchorSlope] using hanchorSlope
  have hslopeDiff : |frameSlope - anchorSlope| ≤ 1 / 100 := by
    simpa [anchorSlope, abs_sub_comm] using hclose
  have hperturbation : |anchorSlope * (frameSlope - anchorSlope)| ≤
      1 / 100 := by
    rw [abs_mul]
    nlinarith [abs_nonneg anchorSlope,
      abs_nonneg (frameSlope - anchorSlope)]
  have hdenomLower : (99 / 100 : ℝ) ≤ denominator := by
    have hperturbationLower : -(1 / 100 : ℝ) ≤
        anchorSlope * (frameSlope - anchorSlope) :=
      (abs_le.mp hperturbation).1
    dsimp only [denominator]
    nlinarith [sq_nonneg anchorSlope]
  have hdenomPos : 0 < denominator := by linarith
  have hframeSlope : |frameSlope| ≤ 101 / 100 := by
    calc
      |frameSlope| ≤ |anchorSlope| + |frameSlope - anchorSlope| := by
        have htriangle := abs_add_le anchorSlope (frameSlope - anchorSlope)
        simpa only [show anchorSlope + (frameSlope - anchorSlope) =
          frameSlope by ring] using htriangle
      _ ≤ 1 + 1 / 100 := add_le_add hanchorSlope' hslopeDiff
      _ = 101 / 100 := by norm_num
  have hnormUpper : pureWZ2HorizontalNorm frameSlope ≤ 3 / 2 := by
    have hnormSq := pureWZ2HorizontalNorm_sq frameSlope
    have hframeSq : frameSlope ^ 2 ≤ (101 / 100 : ℝ) ^ 2 := by
      nlinarith [sq_abs frameSlope, abs_nonneg frameSlope]
    nlinarith [pureWZ2HorizontalNorm_pos frameSlope]
  have hprojection :
      |(source 0 + anchorSlope * source 1) -
        (anchor 0 + anchorSlope * anchor 1)| ≤ 4 * delta := by
    simpa [anchorSlope, globalGrainDirection, PiLp.inner_apply,
      Fin.sum_univ_succ] using hsource.1.2
  have hxIdentity := pureWZ2_fixed_rotated_slice_x_sub_center
    anchorSlope frameSlope anchor source y hdenomPos.ne' hy
  have hxSource :
      |pureWZ2HorizontalRotation frameSlope source 0 -
        pureWZ2FixedRotatedSliceCenterX anchorSlope frameSlope anchor y| ≤
          8 * delta := by
    rw [hxIdentity, abs_div, abs_mul, abs_of_pos hdenomPos,
      abs_of_pos (pureWZ2HorizontalNorm_pos frameSlope)]
    rw [div_le_iff₀ hdenomPos]
    calc
      pureWZ2HorizontalNorm frameSlope *
          |(source 0 + anchorSlope * source 1) -
            (anchor 0 + anchorSlope * anchor 1)|
        ≤ (3 / 2 : ℝ) * (4 * delta) := by
          exact mul_le_mul hnormUpper hprojection (abs_nonneg _)
            (by positivity)
      _ ≤ (8 * delta) * denominator := by
        nlinarith
  have hx : |slicePoint 0 -
      pureWZ2FixedRotatedSliceCenterX anchorSlope frameSlope anchor y| ≤
        8 * delta := by
    have hcoord := congr_arg (fun point : Point3 => point 0) hsourceEq
    have hcoord' : pureWZ2HorizontalRotation frameSlope source 0 =
        slicePoint 0 := by simpa [point3] using hcoord
    rwa [hcoord'] at hxSource
  have hz : |slicePoint 1 - anchor 2| ≤ 4 * delta := by
    have hcoord := congr_arg (fun point : Point3 => point 2) hsourceEq
    have hcoord' : pureWZ2HorizontalRotation frameSlope source 2 =
        slicePoint 1 := by simpa [point3] using hcoord
    have hsourceCoord : source 2 = slicePoint 1 := by
      calc
        source 2 = pureWZ2HorizontalRotation frameSlope source 2 := by simp
        _ = slicePoint 1 := hcoord'
    have hsourceZ : |source 2 - anchor 2| ≤ 4 * delta := hsource.1.1
    rwa [hsourceCoord] at hsourceZ
  dsimp only [anchorSlope] at hx ⊢
  constructor
  · exact ⟨by linarith [(abs_le.mp hx).1],
      by linarith [(abs_le.mp hx).2]⟩
  · exact ⟨by linarith [(abs_le.mp hz).1],
      by linarith [(abs_le.mp hz).2]⟩

/-- A fixed rotated slice of a nearby-slope constant-4 grain has area `≤ 256δ²`. -/
theorem pureWZ2_fixed_rotatedYSlice_globalGrain_volume_upper
    (slope : ℝ → ℝ)
    {delta : ℝ} (hdelta : 0 ≤ delta)
    {frameSlope : ℝ} (anchor : Point3)
    (hanchorBox : anchor ∈ Kakeya.Streamlined.axisBox 2 2 2)
    (hanchorSlope : |slope (anchor 2)| ≤ 1)
    (hclose : |slope (anchor 2) - frameSlope| ≤ 1 / 100) (y : ℝ) :
    volume (pureWZ2RotatedYSlice frameSlope
      (pureWZ2GlobalGrainWithConstant 4 slope delta anchor ∩
        Kakeya.Streamlined.axisBox 2 2 2) y) ≤
      ENNReal.ofReal (128 * delta ^ 2) := by
  let centerX := pureWZ2FixedRotatedSliceCenterX
    (slope (anchor 2)) frameSlope anchor y
  let rectangle : Set Point2 := {point |
    point 0 ∈ Set.Icc (centerX - 8 * delta) (centerX + 8 * delta) ∧
    point 1 ∈ Set.Icc (anchor 2 - 4 * delta) (anchor 2 + 4 * delta)}
  have hsubset : pureWZ2RotatedYSlice frameSlope
      (pureWZ2GlobalGrainWithConstant 4 slope delta anchor ∩
        Kakeya.Streamlined.axisBox 2 2 2) y ⊆ rectangle := by
    simpa only [rectangle, centerX] using
      pureWZ2_fixed_rotatedYSlice_globalGrain_subset_rectangle slope
        hdelta anchor hanchorBox hanchorSlope hclose y
  let lower : Fin 2 → ℝ := fun index =>
    if index = 0 then centerX - 8 * delta else anchor 2 - 4 * delta
  let upper : Fin 2 → ℝ := fun index =>
    if index = 0 then centerX + 8 * delta else anchor 2 + 4 * delta
  let point2Equiv : (Fin 2 → ℝ) ≃ᵐ Point2 :=
    { toFun := WithLp.toLp 2
      invFun := WithLp.ofLp
      left_inv := WithLp.ofLp_toLp (2 : ENNReal)
      right_inv := WithLp.toLp_ofLp (2 : ENNReal)
      measurable_toFun :=
        (PiLp.continuous_toLp
          (p := 2) (β := fun _ : Fin 2 => ℝ)).measurable
      measurable_invFun :=
        (PiLp.continuous_ofLp
          (p := 2) (β := fun _ : Fin 2 => ℝ)).measurable }
  have hrectangle : rectangle = point2Equiv '' Set.Icc lower upper := by
    ext point
    simp only [rectangle, Set.mem_setOf_eq, Set.mem_image, Set.mem_Icc]
    constructor
    · intro hp
      refine ⟨point.ofLp, ?_, point2Equiv.right_inv point⟩
      constructor <;> intro index <;> fin_cases index
      · simpa [lower] using hp.1.1
      · simpa [lower] using hp.2.1
      · simpa [upper] using hp.1.2
      · simpa [upper] using hp.2.2
    · rintro ⟨coordinates, hcoordinates, rfl⟩
      constructor
      · constructor
        · change centerX - 8 * delta ≤ coordinates 0
          simpa [lower] using hcoordinates.1 (0 : Fin 2)
        · change coordinates 0 ≤ centerX + 8 * delta
          simpa [upper] using hcoordinates.2 (0 : Fin 2)
      · constructor
        · change anchor 2 - 4 * delta ≤ coordinates 1
          simpa [lower] using hcoordinates.1 (1 : Fin 2)
        · change coordinates 1 ≤ anchor 2 + 4 * delta
          simpa [upper] using hcoordinates.2 (1 : Fin 2)
  have hpres : MeasurePreserving point2Equiv volume volume :=
    PiLp.volume_preserving_toLp (ι := Fin 2)
  have himage : volume (point2Equiv '' Set.Icc lower upper) =
      volume (Set.Icc lower upper) := by
    have hmeas : MeasurableSet (Set.Icc lower upper) := measurableSet_Icc
    have happly := Measure.map_apply (μ := volume) hpres.measurable
      (point2Equiv.measurableSet_image.mpr hmeas)
    rw [hpres.map_eq] at happly
    have hpre : point2Equiv ⁻¹' (point2Equiv '' Set.Icc lower upper) =
        Set.Icc lower upper := by ext coordinates; simp
    rwa [hpre] at happly
  calc
    volume (pureWZ2RotatedYSlice frameSlope
      (pureWZ2GlobalGrainWithConstant 4 slope delta anchor ∩
        Kakeya.Streamlined.axisBox 2 2 2) y)
      ≤ volume rectangle := measure_mono hsubset
    _ = volume (point2Equiv '' Set.Icc lower upper) := by rw [hrectangle]
    _ = volume (Set.Icc lower upper) := himage
    _ = ENNReal.ofReal (16 * delta) * ENNReal.ofReal (8 * delta) := by
      rw [Real.volume_Icc_pi, Fin.prod_univ_two]
      congr 2 <;> dsimp [lower, upper] <;> ring
    _ = ENNReal.ofReal (128 * delta ^ 2) := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 16 * delta)]
      congr 1
      ring

/-- The nearby-slope constant-4 grain over a fixed rotated-y window. -/
theorem pureWZ2_globalGrain_fixed_rotated_window_volume_upper
    (slope : ℝ → ℝ)
    {delta : ℝ} (hdelta : 0 ≤ delta)
    {frameSlope : ℝ} (anchor : Point3)
    (hanchorBox : anchor ∈ Kakeya.Streamlined.axisBox 2 2 2)
    (hanchorSlope : |slope (anchor 2)| ≤ 1)
    (hclose : |slope (anchor 2) - frameSlope| ≤ 1 / 100)
    {window : Set ℝ} (hwindow : MeasurableSet window) :
    volume ((pureWZ2GlobalGrainWithConstant 4 slope delta anchor ∩
        Kakeya.Streamlined.axisBox 2 2 2) ∩
          pureWZ2RotatedYWindow frameSlope window) ≤
      ENNReal.ofReal (128 * delta ^ 2) * volume window := by
  let rotation := pureWZ2HorizontalRotation frameSlope
  let grainRegion := pureWZ2GlobalGrainWithConstant 4 slope delta anchor ∩
    Kakeya.Streamlined.axisBox 2 2 2
  let restricted := grainRegion ∩ pureWZ2RotatedYWindow frameSlope window
  let rotated := rotation '' restricted
  have haxis : MeasurableSet (Kakeya.Streamlined.axisBox 2 2 2) := by
    apply MeasurableSet.inter
    · exact (isClosed_Iic.preimage (by fun_prop : Continuous
        (fun point : Point3 => |point 0|))).measurableSet
    · apply MeasurableSet.inter
      · exact (isClosed_Iic.preimage (by fun_prop : Continuous
          (fun point : Point3 => |point 1|))).measurableSet
      · exact (isClosed_Iic.preimage (by fun_prop : Continuous
          (fun point : Point3 => |point 2|))).measurableSet
  have hgrain : pureWZ2GlobalGrainWithConstant 4 slope delta anchor =
      pureWZ2GlobalGrain slope (4 * delta) anchor := by
    ext point
    simp [pureWZ2GlobalGrain, pureWZ2GlobalGrainWithConstant]
  have hrestricted : MeasurableSet restricted := by
    dsimp only [restricted, grainRegion]
    rw [hgrain]
    exact ((measurableSet_pureWZ2GlobalGrain slope (4 * delta) anchor).inter
      haxis).inter (measurableSet_pureWZ2RotatedYWindow frameSlope hwindow)
  have hrotated : MeasurableSet rotated :=
    rotation.toMeasurableEquiv.measurableSet_image.mpr hrestricted
  have hvolume : volume restricted = volume rotated :=
    (pureWZ2HorizontalRotation_volume_image frameSlope hrestricted).symm
  have hslice : ∀ y, volume (pureWZ2YSlice rotated y) ≤
      ENNReal.ofReal (128 * delta ^ 2) := by
    intro y
    calc
      volume (pureWZ2YSlice rotated y)
        ≤ volume (pureWZ2RotatedYSlice frameSlope grainRegion y) := by
          apply measure_mono
          apply pureWZ2YSlice_mono
          exact Set.image_mono Set.inter_subset_left
      _ ≤ ENNReal.ofReal (128 * delta ^ 2) :=
        pureWZ2_fixed_rotatedYSlice_globalGrain_volume_upper slope
          hdelta anchor hanchorBox hanchorSlope hclose y
  have houtside : ∀ y ∉ window, volume (pureWZ2YSlice rotated y) = 0 := by
    intro y hy
    have hempty : pureWZ2YSlice rotated y = ∅ := by
      ext point
      simp only [pureWZ2_mem_ySlice_iff, Set.notMem_empty, iff_false]
      rintro ⟨source, hsource, hsourceEq⟩
      apply hy
      have hcoordinate := hsource.2
      dsimp only [restricted, pureWZ2RotatedYWindow] at hcoordinate
      change rotation source 1 ∈ window at hcoordinate
      rw [hsourceEq] at hcoordinate
      simpa [point3, rotation] using hcoordinate
    rw [hempty, measure_empty]
  have hfull : (∫⁻ y : ℝ, volume (pureWZ2YSlice rotated y)) =
      ∫⁻ y in window, volume (pureWZ2YSlice rotated y) := by
    rw [← lintegral_indicator hwindow]
    apply lintegral_congr
    intro y
    by_cases hy : y ∈ window
    · simp [hy]
    · simp [hy, houtside y hy]
  change volume restricted ≤ _
  rw [hvolume, pureWZ2_volume_eq_lintegral_ySlice rotated hrotated, hfull]
  calc
    (∫⁻ y in window, volume (pureWZ2YSlice rotated y))
      ≤ ∫⁻ _y in window, ENNReal.ofReal (128 * delta ^ 2) :=
        setLIntegral_mono' hwindow (fun y _ => hslice y)
    _ = ENNReal.ofReal (128 * delta ^ 2) * volume window := by
      rw [setLIntegral_const]

/-- Fubini averaging in a fixed rotated horizontal coordinate frame. -/
theorem pureWZ2_exists_rotatedYSlice_average_on
    (frameSlope : ℝ) {E : Set Point3} (hE : MeasurableSet E)
    (hEFinite : volume E ≠ ⊤)
    {good : Set ℝ} (hgood : MeasurableSet good)
    (hgoodZero : volume good ≠ 0)
    (hEGood : ∀ point ∈ E,
      pureWZ2HorizontalRotation frameSlope point 1 ∈ good) :
    ∃ y ∈ good, volume E / volume good ≤
      volume (pureWZ2RotatedYSlice frameSlope E y) := by
  let rotation := pureWZ2HorizontalRotation frameSlope
  let rotated := rotation '' E
  have hrotated : MeasurableSet rotated :=
    rotation.toMeasurableEquiv.measurableSet_image.mpr hE
  have hrotatedFinite : volume rotated ≠ ⊤ := by
    rw [pureWZ2HorizontalRotation_volume_image frameSlope hE]
    exact hEFinite
  have hsupport : ∀ point ∈ rotated, point 1 ∈ good := by
    intro point hpoint
    rcases hpoint with ⟨source, hsource, rfl⟩
    exact hEGood source hsource
  rcases pureWZ2_exists_ySlice_average_on hrotated hrotatedFinite
      hgood hgoodZero hsupport with ⟨y, hy, haverage⟩
  refine ⟨y, hy, ?_⟩
  rw [pureWZ2HorizontalRotation_volume_image frameSlope hE] at haverage
  exact haverage

end Kakeya.Assouad

end
