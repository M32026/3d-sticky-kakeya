import MyLeanRepo.Kakeya.Assouad.LargeSlope.ADSlabVolumeBound
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicADTransfer
import MyLeanRepo.Kakeya.Assouad.PropStickyBoundaryCellPruningGeometry
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23GoodHeights

/-!
# Volume upper bounds from paper exact-slice global AD

The paper-facing grain interface records exact horizontal-slice AD rather
than the older slab AD structure.  Fubini and the fixed cropped support turn
that exact-slice statement directly into the union-volume upper bound needed
by the terminal Proposition-6.5 configuration.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

/-- A coordinate-plane set in `[-1,1]^2` has area controlled by projection
along any vector whose first coordinate is one. -/
lemma paper_coordinate_area_le_four_projection
    {S : Set (Fin 2 → ℝ)}
    (hS : ∀ point ∈ S, |point 0| ≤ 1 ∧ |point 1| ≤ 1)
    (slope : ℝ) {M : ENNReal}
    (hprojection : volume
      ((fun point : Fin 2 → ℝ => point 0 + slope * point 1) '' S) ≤ M) :
    volume S ≤ 4 * M := by
  let raw : Fin 2 → ℝ := fun coordinate =>
    if coordinate = 0 then 1 else slope
  let rawNorm : ℝ := Real.sqrt (raw 0 ^ 2 + raw 1 ^ 2)
  let normal : Fin 2 → ℝ := fun coordinate => raw coordinate / rawNorm
  have hrawZero : raw 0 = 1 := by simp [raw]
  have hrawOne : raw 1 = slope := by simp [raw]
  have hnormSq : rawNorm ^ 2 = raw 0 ^ 2 + raw 1 ^ 2 := by
    rw [Real.sq_sqrt]
    exact add_nonneg (sq_nonneg (raw 0)) (sq_nonneg (raw 1))
  have hnormOne : 1 ≤ rawNorm := by
    have hsumOne : 1 ≤ raw 0 ^ 2 + raw 1 ^ 2 := by
      rw [hrawZero]
      nlinarith [sq_nonneg (raw 1)]
    have hnonnegative : 0 ≤ rawNorm :=
      Real.sqrt_nonneg (raw 0 ^ 2 + raw 1 ^ 2)
    nlinarith [hnormSq]
  have hnormPos : 0 < rawNorm := lt_of_lt_of_le (by norm_num) hnormOne
  have hnormalUnit : normal 0 ^ 2 + normal 1 ^ 2 = 1 := by
    dsimp only [normal]
    rw [div_pow, div_pow, ← add_div, ← hnormSq]
    field_simp [hnormPos.ne']
  let rawProjection : Set ℝ :=
    (fun point : Fin 2 → ℝ => point 0 + slope * point 1) '' S
  let normalizedProjection : Set ℝ :=
    (fun point : Fin 2 → ℝ =>
      point 0 * normal 0 + point 1 * normal 1) '' S
  have hnormalizedImage : normalizedProjection =
      (fun value : ℝ => value / rawNorm) '' rawProjection := by
    ext value
    simp only [normalizedProjection, rawProjection, Set.mem_image]
    constructor
    · rintro ⟨point, hpoint, rfl⟩
      refine ⟨point 0 + slope * point 1, ⟨point, hpoint, rfl⟩, ?_⟩
      dsimp only [normal]
      rw [hrawZero, hrawOne]
      ring
    · rintro ⟨projected, ⟨point, hpoint, rfl⟩, rfl⟩
      refine ⟨point, hpoint, ?_⟩
      dsimp only [normal]
      rw [hrawZero, hrawOne]
      ring
  have hnormalizedVolume : volume normalizedProjection =
      ENNReal.ofReal (1 / rawNorm) * volume rawProjection := by
    rw [hnormalizedImage]
    have himage : (fun value : ℝ => value / rawNorm) '' rawProjection =
        (fun value : ℝ => rawNorm * value) ⁻¹' rawProjection := by
      ext value
      constructor
      · rintro ⟨source, hsource, rfl⟩
        have hmul : rawNorm * (source / rawNorm) = source := by
          field_simp [hnormPos.ne']
        change rawNorm * (source / rawNorm) ∈ rawProjection
        rwa [hmul]
      · intro hvalue
        exact ⟨rawNorm * value, hvalue, by
          field_simp [hnormPos.ne']⟩
    rw [himage, Real.volume_preimage_mul_left hnormPos.ne' rawProjection]
    congr 1
    rw [abs_of_pos (inv_pos.mpr hnormPos)]
    field_simp [hnormPos.ne']
  have hnormalizedLe : volume normalizedProjection ≤ volume rawProjection := by
    rw [hnormalizedVolume]
    have hinverse : ENNReal.ofReal (1 / rawNorm) ≤ 1 := by
      rw [ENNReal.ofReal_le_one]
      exact (div_le_one hnormPos).2 hnormOne
    calc
      ENNReal.ofReal (1 / rawNorm) * volume rawProjection ≤
          1 * volume rawProjection := by gcongr
      _ = volume rawProjection := one_mul _
  have hball : ∀ point ∈ S,
      point 0 ^ 2 + point 1 ^ 2 ≤ (2 : ℝ) ^ 2 := by
    intro point hpoint
    have hzeroBound := abs_le.mp (hS point hpoint).1
    have honeBound := abs_le.mp (hS point hpoint).2
    nlinarith [sq_nonneg (point 0 - 1), sq_nonneg (point 0 + 1),
      sq_nonneg (point 1 - 1), sq_nonneg (point 1 + 1)]
  have harea := area_le_two_projection (S := S) (v := normal) (R := 2)
    hnormalUnit (show (0 : ℝ) ≤ 2 by norm_num) hball
  calc
    volume S ≤ ENNReal.ofReal (2 * (2 : ℝ)) *
        volume normalizedProjection := harea
    _ ≤ ENNReal.ofReal (2 * (2 : ℝ)) * volume rawProjection := by gcongr
    _ ≤ 4 * M := by
      rw [show ENNReal.ofReal (2 * (2 : ℝ)) = (4 : ENNReal) by norm_num]
      exact mul_le_mul_left' hprojection 4

/-- The interval-form paper AD condition controls the measure of its whole
set once an explicit symmetric projection bound is supplied. -/
lemma PureWZ2PaperADSet1.volume_le_of_subset_Icc
    {E : Set ℝ} {delta alpha : ℝ} {C : ENNReal}
    (hAD : PureWZ2PaperADSet1 E delta alpha C)
    {bound : ℝ} (hbound : 0 < bound)
    (hdeltaBound : delta ≤ 2 * bound)
    (hsubset : E ⊆ Set.Icc (-bound) bound) :
    volume E ≤
      (C * Kakeya.realRpowENN ((2 * bound) / delta) alpha) *
        ENNReal.ofReal (2 * delta) := by
  rcases hAD with ⟨hdelta, _halpha, _halphaOne, _hCOne, hCtop, hcover⟩
  have hintersection : E ∩ Set.Icc (-bound) (-bound + 2 * bound) = E := by
    rw [show -bound + 2 * bound = bound by ring]
    exact Set.inter_eq_left.mpr hsubset
  have hcover' := hcover delta hdelta.le le_rfl
    (-bound) (2 * bound) hdeltaBound
  rw [hintersection] at hcover'
  exact volume_le_externalCoveringNumber_mul_two_delta hdelta
    (ENNReal.mul_ne_top hCtop (by simp [Kakeya.realRpowENN])) hcover'

/-- Exact-slice paper AD bounds the volume of any paper shading.  The
explicit slope bound is retained because the public slope need not be
centered at zero. -/
theorem pureWZ2_paperShading_volume_le_of_global_ad
    {delta sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (slope : SlopeFunction) {C : ENNReal}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hCtop : C ≠ ⊤) {slopeBound : ℝ}
    (hslopeBound : 0 ≤ slopeBound)
    (hslope : ∀ z ∈ Set.Icc (-1 : ℝ) 1, |slope z| ≤ slopeBound)
    (hglobal : ∀ z : ℝ, ∀ hz : z ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (scalarProjection (globalGrainDirection (slope z))
          (horizontalSlice shading.union z))
        delta (1 - sigma) C) :
    volume shading.union ≤ 8 *
      (C * Kakeya.realRpowENN
          ((2 * (1 + slopeBound)) / delta) (1 - sigma) *
        ENNReal.ofReal (2 * delta)) := by
  let planarSlice : ℝ → Set Point2 := fun z =>
    wz1Lemma23PlanarSlice shading.union z
  let coordinateSlice : ℝ → Set (Fin 2 → ℝ) := fun z =>
    {point | point3 (point 0) (point 1) z ∈ shading.union}
  have hshadingMeasurable : MeasurableSet shading.union := by
    rw [show shading.union = ⋃ index : Fin family.card, shading.carrier index by
      ext point
      simp [Kakeya.Streamlined.Shading.union]
      rfl]
    exact MeasurableSet.iUnion fun index => shading.measurable_carrier index
  let coordinates : Point2 ≃ᵐ (Fin 2 → ℝ) :=
    { toFun := fun point => point.ofLp
      invFun := WithLp.toLp 2
      left_inv := WithLp.toLp_ofLp (2 : ENNReal)
      right_inv := WithLp.ofLp_toLp (2 : ENNReal)
      measurable_toFun :=
        (PiLp.continuous_ofLp
          (p := 2) (β := fun _ : Fin 2 => ℝ)).measurable
      measurable_invFun :=
        (PiLp.continuous_toLp
          (p := 2) (β := fun _ : Fin 2 => ℝ)).measurable }
  have hcoordinateSliceMeasurable : ∀ z, MeasurableSet (coordinateSlice z) := by
    intro z
    have hcontinuous : Continuous (fun coordinates : Fin 2 → ℝ =>
        point3 (coordinates 0) (coordinates 1) z) := by
      unfold point3
      fun_prop
    exact hshadingMeasurable.preimage hcontinuous.measurable
  have hsliceImage : ∀ z, coordinates '' planarSlice z = coordinateSlice z := by
    intro z
    ext point
    constructor
    · rintro ⟨source, hsource, rfl⟩
      exact wz1Lemma23_mem_planarSlice_iff.mp hsource
    · intro hpoint
      refine ⟨WithLp.toLp 2 point, ?_, by rfl⟩
      rw [wz1Lemma23_mem_planarSlice_iff]
      exact hpoint
  have hsliceVolume : ∀ z, volume (planarSlice z) =
      volume (coordinateSlice z) := by
    intro z
    have hpreserving : MeasurePreserving coordinates volume volume :=
      PiLp.volume_preserving_ofLp (ι := Fin 2)
    have hpreimage : coordinates ⁻¹' coordinateSlice z = planarSlice z := by
      rw [← hsliceImage z]
      exact Set.preimage_image_eq _ coordinates.injective
    have hvolume := hpreserving.measure_preimage_emb
      coordinates.measurableEmbedding (coordinateSlice z)
    rwa [hpreimage] at hvolume
  have hprojectionEq : ∀ z : ℝ,
      (fun point : Fin 2 → ℝ => point 0 + slope z * point 1) ''
          coordinateSlice z =
        scalarProjection (globalGrainDirection (slope z))
          (horizontalSlice shading.union z) := by
    intro z
    ext value
    simp only [Set.mem_image, coordinateSlice, scalarProjection,
      horizontalSlice, Set.mem_setOf_eq]
    constructor
    · rintro ⟨point, hpoint, rfl⟩
      refine ⟨point3 (point 0) (point 1) z,
        ⟨hpoint, by simp [point3]⟩, ?_⟩
      simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ, point3]
    · rintro ⟨point, ⟨hpoint, hheight⟩, rfl⟩
      let source : Fin 2 → ℝ := fun coordinate =>
        if coordinate = 0 then point 0 else point 1
      refine ⟨source, ?_, ?_⟩
      · change point3 (source 0) (source 1) z ∈ shading.union
        convert hpoint using 1
        ext coordinate
        fin_cases coordinate <;> simp [source, point3, hheight]
      · simp [source, globalGrainDirection, PiLp.inner_apply,
          Fin.sum_univ_succ]
  let projectionBound : ENNReal :=
    C * Kakeya.realRpowENN
        ((2 * (1 + slopeBound)) / delta) (1 - sigma) *
      ENNReal.ofReal (2 * delta)
  let bound : ENNReal := 4 * projectionBound
  have hslice : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      volume (planarSlice z) ≤ bound := by
    intro z hz
    have hprojectionSubset :
        scalarProjection (globalGrainDirection (slope z))
            (horizontalSlice shading.union z) ⊆
          Set.Icc (-(1 + slopeBound)) (1 + slopeBound) := by
      rintro value ⟨point, ⟨hpoint, _hheight⟩, rfl⟩
      have hambient := shading_union_subset_axisBox hpoint
      have hx : |point 0| ≤ 1 := by
        simpa [Kakeya.Streamlined.axisBox] using hambient.1
      have hy : |point 1| ≤ 1 := by
        simpa [Kakeya.Streamlined.axisBox] using hambient.2.1
      have hinner : inner ℝ point (globalGrainDirection (slope z)) =
          point 0 + slope z * point 1 := by
        simp [globalGrainDirection, PiLp.inner_apply, Fin.sum_univ_succ]
      change inner ℝ point (globalGrainDirection (slope z)) ∈ _
      rw [hinner]
      apply abs_le.mp
      calc
        |point 0 + slope z * point 1| ≤
            |point 0| + |slope z| * |point 1| := by
          simpa [abs_mul] using abs_add_le (point 0) (slope z * point 1)
        _ ≤ 1 + slopeBound * 1 := by
          gcongr
          exact hslope z hz
        _ = 1 + slopeBound := by ring
    have hdeltaProjection : delta ≤ 2 * (1 + slopeBound) := by
      nlinarith
    have hprojection : volume
        (scalarProjection (globalGrainDirection (slope z))
          (horizontalSlice shading.union z)) ≤ projectionBound := by
      simpa only [projectionBound] using
        (hglobal z hz).volume_le_of_subset_Icc
          (show 0 < 1 + slopeBound by linarith) hdeltaProjection
          hprojectionSubset
    have hsliceBox : ∀ point ∈ coordinateSlice z,
        |point 0| ≤ 1 ∧ |point 1| ≤ 1 := by
      intro point hpoint
      have hambient := shading_union_subset_axisBox hpoint
      simpa [Kakeya.Streamlined.axisBox, point3] using
        And.intro hambient.1 hambient.2.1
    rw [hsliceVolume z]
    exact paper_coordinate_area_le_four_projection hsliceBox (slope z) <| by
      rw [hprojectionEq z]
      exact hprojection
  have houtside : ∀ z ∉ Set.Icc (-1 : ℝ) 1, planarSlice z = ∅ := by
    intro z hz
    ext point
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hpoint
    have hambient := shading_union_subset_axisBox
      (wz1Lemma23_mem_planarSlice_iff.mp hpoint)
    apply hz
    have hzAbs : |z| ≤ 1 := by
      simpa [Kakeya.Streamlined.axisBox, point3] using hambient.2.2
    exact abs_le.mp hzAbs
  rw [wz1_lemma23_volume_eq_lintegral_planarSlice shading.union
    hshadingMeasurable]
  calc
    (∫⁻ z : ℝ, volume (planarSlice z)) ≤
        ∫⁻ z : ℝ, Set.indicator (Set.Icc (-1 : ℝ) 1)
          (fun _ => bound) z := by
      apply lintegral_mono
      intro z
      by_cases hz : z ∈ Set.Icc (-1 : ℝ) 1
      · simpa [hz] using hslice z hz
      · change volume (planarSlice z) ≤ _
        rw [houtside z hz]
        simp [hz]
    _ = bound * volume (Set.Icc (-1 : ℝ) 1) := by
      rw [lintegral_indicator measurableSet_Icc, setLIntegral_const]
    _ = 2 * bound := by
      rw [Real.volume_Icc]
      norm_num
      exact mul_comm _ _
    _ = 8 *
        (C * Kakeya.realRpowENN
            ((2 * (1 + slopeBound)) / delta) (1 - sigma) *
          ENNReal.ofReal (2 * delta)) := by
      dsimp only [bound, projectionBound]
      ring

end Kakeya.Assouad

end
