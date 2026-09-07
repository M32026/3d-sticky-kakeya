import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.SourceCarrierPreparation
import MyLeanRepo.Kakeya.Assouad.LargeSlope.ADSlabVolumeBound
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23GoodHeights

/-!
# Slab-volume upper bounds from Pure exact-slice global AD

The Pure paper crop lies in `[-1,1]^3`, not the ordinary unit ball.  Its
horizontal slices therefore lie in a radius-`sqrt 2` disk.  Exact-slice AD
still gives a uniform area bound, and the closed Lemma-23 Fubini identity
turns this into a horizontal slab-volume estimate.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

/-- Exact-slice AD bounds the area of every horizontal slice of a paper
shading. -/
theorem paper_exactSlice_area_le
    {delta sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : Kakeya.Streamlined.TubeShading family)
    (haxis : ∀ point ∈ shading.union, ∀ coordinate : Fin 3,
      |point coordinate| ≤ 1)
    (slope : ℝ → ℝ) (C : ENNReal)
    (hdelta : 0 < delta) (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hCtop : C ≠ ⊤)
    (hexact : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      IsADSet1
        (scalarProjection (globalGrainDirection (slope z))
          (horizontalSlice shading.union z))
        delta (1 - sigma) C)
    (z : ℝ) :
    MeasureTheory.volume (wz1Lemma23PlanarSlice shading.union z) ≤
      32 * C * Kakeya.realRpowENN delta sigma := by
  by_cases hz : z ∈ Set.Icc (-1 : ℝ) 1
  · let slice := wz1Lemma23PlanarSlice shading.union z
    let coordinates : Point2 ≃ᵐ (Fin 2 → ℝ) :=
      { toFun := WithLp.ofLp
        invFun := WithLp.toLp 2
        left_inv := WithLp.toLp_ofLp (2 : ENNReal)
        right_inv := WithLp.ofLp_toLp (2 : ENNReal)
        measurable_toFun :=
          (PiLp.continuous_ofLp
            (p := 2) (β := fun _ : Fin 2 => ℝ)).measurable
        measurable_invFun :=
          (PiLp.continuous_toLp
            (p := 2) (β := fun _ : Fin 2 => ℝ)).measurable }
    let coordinateSlice : Set (Fin 2 → ℝ) := coordinates '' slice
    have hvolumeEq : MeasureTheory.volume coordinateSlice =
        MeasureTheory.volume slice := by
      have hmp : MeasurePreserving coordinates volume volume :=
        PiLp.volume_preserving_ofLp (Fin 2)
      have hpre : coordinates ⁻¹' coordinateSlice = slice :=
        Set.preimage_image_eq slice coordinates.injective
      have hmeasure := hmp.measure_preimage_emb
        coordinates.measurableEmbedding coordinateSlice
      rw [hpre] at hmeasure
      exact hmeasure.symm
    have hprojEq :
        (fun point : Fin 2 → ℝ =>
          point 0 + slope z * point 1) '' coordinateSlice =
        scalarProjection (globalGrainDirection (slope z))
          (horizontalSlice shading.union z) := by
      ext value
      constructor
      · rintro ⟨point, ⟨planar, hplanar, rfl⟩, rfl⟩
        change _
        have hpoint : planar ∈ slice := hplanar
        have hpaper := wz1Lemma23_mem_planarSlice_iff.mp hpoint
        let point3d := point3 (planar 0) (planar 1) z
        refine ⟨point3d, ⟨hpaper, by simp [point3d, point3]⟩, ?_⟩
        change inner ℝ point3d (globalGrainDirection (slope z)) =
          planar 0 + slope z * planar 1
        simp [point3d, globalGrainDirection, PiLp.inner_apply,
          Fin.sum_univ_succ, point3]
      · rintro ⟨point, ⟨hpaper, hheight⟩, rfl⟩
        let planar : Point2 := WithLp.toLp 2 ![point 0, point 1]
        have hplanar : planar ∈ slice := by
          apply wz1Lemma23_mem_planarSlice_iff.mpr
          have heq : point3 (planar 0) (planar 1) z = point := by
            ext coordinate
            fin_cases coordinate <;> simp [planar, point3, hheight]
          rwa [heq]
        refine ⟨coordinates planar, ⟨planar, hplanar, rfl⟩, ?_⟩
        simp [coordinates, planar, globalGrainDirection, PiLp.inner_apply,
          Fin.sum_univ_succ, mul_comm]
    have hproj : MeasureTheory.volume
        ((fun point : Fin 2 → ℝ => point 0 + slope z * point 1) ''
          coordinateSlice) ≤
      8 * C * Kakeya.realRpowENN delta sigma := by
      rw [hprojEq]
      exact IsADSet1.volume_le hdelta hsigma hsigmaOne hCtop (hexact z hz)
    let w : Fin 2 → ℝ := fun coordinate =>
      match coordinate with
      | 0 => 1
      | 1 => slope z
    have hnorm : (1 : ℝ) ≤ w 0 ^ 2 + w 1 ^ 2 := by
      dsimp only [w]
      nlinarith [sq_nonneg (slope z)]
    have hbox : ∀ point ∈ coordinateSlice,
        point 0 ^ 2 + point 1 ^ 2 ≤ (Real.sqrt 2) ^ 2 := by
      rintro point ⟨planar, hplanar, rfl⟩
      have hpaper := wz1Lemma23_mem_planarSlice_iff.mp hplanar
      have hpoint0 : |planar 0| ≤ 1 := by
        simpa [point3] using haxis _ hpaper (0 : Fin 3)
      have hpoint1 : |planar 1| ≤ 1 := by
        simpa [point3] using haxis _ hpaper (1 : Fin 3)
      have h0 : planar 0 ^ 2 ≤ 1 := by
        nlinarith [sq_abs (planar 0), abs_nonneg (planar 0)]
      have h1 : planar 1 ^ 2 ≤ 1 := by
        nlinarith [sq_abs (planar 1), abs_nonneg (planar 1)]
      change planar 0 ^ 2 + planar 1 ^ 2 ≤ (Real.sqrt 2) ^ 2
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    have hproj' : MeasureTheory.volume
        ((fun point : Fin 2 → ℝ => point 0 * w 0 + point 1 * w 1) ''
          coordinateSlice) ≤
      8 * C * Kakeya.realRpowENN delta sigma := by
      simpa [w, mul_comm] using hproj
    have harea := area_le_projection_nonunit_radius
      (S := coordinateSlice) (R := Real.sqrt 2)
      (Real.sqrt_nonneg _) hbox hnorm hproj'
    calc
      MeasureTheory.volume slice = MeasureTheory.volume coordinateSlice :=
        hvolumeEq.symm
      _ ≤
          ENNReal.ofReal (2 * Real.sqrt 2) *
            (8 * C * Kakeya.realRpowENN delta sigma) := harea
      _ ≤ 4 * (8 * C * Kakeya.realRpowENN delta sigma) := by
        gcongr
        rw [show (4 : ENNReal) = ENNReal.ofReal (4 : ℝ) by norm_num]
        exact ENNReal.ofReal_le_ofReal (by
          nlinarith [Real.sqrt_nonneg 2,
            Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)])
      _ = 32 * C * Kakeya.realRpowENN delta sigma := by ring
  · have hempty : wz1Lemma23PlanarSlice shading.union z = ∅ := by
      ext point
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hpoint
      have hpaper := wz1Lemma23_mem_planarSlice_iff.mp hpoint
      have hzAbs : |z| ≤ 1 := by
        simpa [point3] using haxis _ hpaper (2 : Fin 3)
      exact hz (abs_le.mp hzAbs)
    rw [hempty]
    simp

/-- A uniform planar-slice cap gives a slab-volume cap by the closed
Lemma-23 Fubini identity. -/
theorem volume_inter_horizontalSlab_le_of_planarSlice
    {E : Set Point3} (hE : MeasurableSet E)
    {M : ENNReal}
    (hslice : ∀ z, MeasureTheory.volume (wz1Lemma23PlanarSlice E z) ≤ M)
    {a b : ℝ} (hab : a ≤ b) :
    MeasureTheory.volume (E ∩ horizontalSlab a b) ≤
      M * ENNReal.ofReal (b - a) := by
  let slab := E ∩ horizontalSlab a b
  have hslab : MeasurableSet slab :=
    hE.inter (measurableSet_horizontalSlab a b)
  rw [wz1_lemma23_volume_eq_lintegral_planarSlice slab hslab]
  let bound : ℝ → ENNReal := Set.indicator (Set.Icc a b) (fun _ => M)
  have hpointwise : ∀ z,
      MeasureTheory.volume (wz1Lemma23PlanarSlice slab z) ≤ bound z := by
    intro z
    by_cases hz : z ∈ Set.Icc a b
    · dsimp only [bound]
      simp only [Set.indicator_of_mem hz]
      exact (MeasureTheory.measure_mono (by
        intro point hpoint
        have hpoint3 := wz1Lemma23_mem_planarSlice_iff.mp hpoint
        exact wz1Lemma23_mem_planarSlice_iff.mpr hpoint3.1)).trans (hslice z)
    · dsimp only [bound]
      simp only [Set.indicator, hz, if_false]
      have hempty : wz1Lemma23PlanarSlice slab z = ∅ := by
        ext point
        simp only [Set.mem_empty_iff_false, iff_false]
        intro hpoint
        have hpoint3 := wz1Lemma23_mem_planarSlice_iff.mp hpoint
        apply hz
        simpa [horizontalSlab, point3] using hpoint3.2
      rw [hempty]
      simp
  calc
    (∫⁻ z : ℝ, MeasureTheory.volume (wz1Lemma23PlanarSlice slab z)) ≤
        ∫⁻ z : ℝ, bound z := MeasureTheory.lintegral_mono hpointwise
    _ = M * MeasureTheory.volume (Set.Icc a b) := by
      exact MeasureTheory.lintegral_indicator_const₀
        measurableSet_Icc.nullMeasurableSet M
    _ = M * ENNReal.ofReal (b - a) := by
      rw [Real.volume_Icc]

/-- Pure paper exact-slice AD implies the corresponding slab-volume cap. -/
theorem paper_exactSlice_slab_volume_le
    {delta sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : Kakeya.Streamlined.TubeShading family)
    (haxis : ∀ point ∈ shading.union, ∀ coordinate : Fin 3,
      |point coordinate| ≤ 1)
    (slope : ℝ → ℝ) (C : ENNReal)
    (hdelta : 0 < delta) (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hCtop : C ≠ ⊤)
    (hexact : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      IsADSet1
        (scalarProjection (globalGrainDirection (slope z))
          (horizontalSlice shading.union z))
        delta (1 - sigma) C)
    {a b : ℝ} (hab : a ≤ b) :
    MeasureTheory.volume (shading.union ∩ horizontalSlab a b) ≤
      (32 * C * Kakeya.realRpowENN delta sigma) *
        ENNReal.ofReal (b - a) := by
  exact volume_inter_horizontalSlab_le_of_planarSlice
    (measurableSet_shading_union shading)
    (paper_exactSlice_area_le shading haxis slope C hdelta hsigma hsigmaOne
      hCtop hexact) hab

end Kakeya.Assouad
