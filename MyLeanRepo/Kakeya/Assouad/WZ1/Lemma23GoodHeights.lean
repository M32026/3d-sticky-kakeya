import MyLeanRepo.Kakeya.Assouad.Definitions
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Fubini selection of a good height for WZ1 Lemma 23

This module is independent of the old Corollary 26 popularity implementation.
It gives only the measure-theoretic horizontal-slice identity and the
one-height pigeonhole needed in the geometric preparation of Lemma 23.
-/

noncomputable section

open MeasureTheory Set

namespace Kakeya.Assouad

/-- Measurable equivalence from `Point3` to its coordinate function. -/
private def lemma23Point3EquivPi : Point3 ≃ᵐ (Fin 3 → ℝ) :=
  { toFun := fun point => point.ofLp
    invFun := WithLp.toLp 2
    left_inv := WithLp.toLp_ofLp (2 : ENNReal)
    right_inv := WithLp.ofLp_toLp (2 : ENNReal)
    measurable_toFun :=
      (PiLp.continuous_ofLp
        (p := 2) (β := fun _ : Fin 3 => ℝ)).measurable
    measurable_invFun :=
      (PiLp.continuous_toLp
        (p := 2) (β := fun _ : Fin 3 => ℝ)).measurable }

/-- Measurable equivalence from `Point2` to its coordinate function. -/
private def lemma23Point2EquivPi : Point2 ≃ᵐ (Fin 2 → ℝ) :=
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

/-- Split the last coordinate from a three-dimensional coordinate function. -/
private def lemma23Split3Equiv :
    (Fin 3 → ℝ) ≃ᵐ (ℝ × (Fin 2 → ℝ)) :=
  MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2

/-- The planar realization of a horizontal slice. -/
def wz1Lemma23PlanarSlice (E : Set Point3) (z : ℝ) : Set Point2 :=
  lemma23Point2EquivPi.symm ''
    {p : Fin 2 → ℝ |
      lemma23Point3EquivPi.symm
          (lemma23Split3Equiv.symm (z, p)) ∈ E}

private lemma lemma23_split_point
    (z : ℝ) (coordinates : Fin 2 → ℝ) :
    lemma23Point3EquivPi.symm
        (lemma23Split3Equiv.symm (z, coordinates)) =
      point3 (coordinates 0) (coordinates 1) z := by
  ext i
  fin_cases i <;>
    simp [lemma23Point3EquivPi, lemma23Split3Equiv,
      Fin.insertNth_apply_below, point3]

/-- Coordinate description of the planar horizontal slice. -/
theorem wz1Lemma23_mem_planarSlice_iff
    {E : Set Point3} {z : ℝ} {point : Point2} :
    point ∈ wz1Lemma23PlanarSlice E z ↔
      point3 (point 0) (point 1) z ∈ E := by
  simp only [wz1Lemma23PlanarSlice, Set.mem_image,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨coordinates, hcoordinates, hpoint⟩
    rw [← hpoint]
    rw [lemma23_split_point] at hcoordinates
    simpa [lemma23Point2EquivPi] using hcoordinates
  · intro hpoint
    refine ⟨lemma23Point2EquivPi point, ?_, by simp⟩
    rw [lemma23_split_point]
    simpa [lemma23Point2EquivPi] using hpoint

private lemma lemma23Point3EquivPi_measurePreserving :
    MeasurePreserving lemma23Point3EquivPi volume volume := by
  have hsymm :
      MeasurePreserving lemma23Point3EquivPi.symm volume volume :=
    PiLp.volume_preserving_toLp (ι := Fin 3)
  have hmap :
      Measure.map lemma23Point3EquivPi.symm volume = volume :=
    hsymm.map_eq
  refine ⟨lemma23Point3EquivPi.measurable, ?_⟩
  calc
    Measure.map lemma23Point3EquivPi volume =
        Measure.map lemma23Point3EquivPi
          (Measure.map lemma23Point3EquivPi.symm volume) := by
      rw [hmap]
    _ = Measure.map
        (lemma23Point3EquivPi ∘ lemma23Point3EquivPi.symm)
        volume := by
      rw [Measure.map_map
        lemma23Point3EquivPi.measurable
        lemma23Point3EquivPi.symm.measurable]
    _ = volume := by
      have hcomp :
          lemma23Point3EquivPi ∘ lemma23Point3EquivPi.symm = id := by
        funext x
        simp
      rw [hcomp]
      simp

private lemma lemma23Point2EquivPi_measurePreserving :
    MeasurePreserving lemma23Point2EquivPi volume volume := by
  have hsymm :
      MeasurePreserving lemma23Point2EquivPi.symm volume volume :=
    PiLp.volume_preserving_toLp (ι := Fin 2)
  have hmap :
      Measure.map lemma23Point2EquivPi.symm volume = volume :=
    hsymm.map_eq
  refine ⟨lemma23Point2EquivPi.measurable, ?_⟩
  calc
    Measure.map lemma23Point2EquivPi volume =
        Measure.map lemma23Point2EquivPi
          (Measure.map lemma23Point2EquivPi.symm volume) := by
      rw [hmap]
    _ = Measure.map
        (lemma23Point2EquivPi ∘ lemma23Point2EquivPi.symm)
        volume := by
      rw [Measure.map_map
        lemma23Point2EquivPi.measurable
        lemma23Point2EquivPi.symm.measurable]
    _ = volume := by
      have hcomp :
          lemma23Point2EquivPi ∘ lemma23Point2EquivPi.symm = id := by
        funext x
        simp
      rw [hcomp]
      simp

private lemma lemma23_equiv_image_volume
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β}
    {S : Set α} (hS : MeasurableSet S)
    (e : α ≃ᵐ β) (hmp : MeasurePreserving e μ ν) :
    ν (e '' S) = μ S := by
  rw [← hmp.map_eq]
  rw [Measure.map_apply e.measurable
    (e.measurableSet_image.mpr hS)]
  rw [e.preimage_image]

/-- Three-dimensional volume is the integral of planar horizontal slices. -/
theorem wz1_lemma23_volume_eq_lintegral_planarSlice
    (E : Set Point3) (hE : MeasurableSet E) :
    volume E =
      ∫⁻ z : ℝ, volume (wz1Lemma23PlanarSlice E z) := by
  let E₃ : Set (Fin 3 → ℝ) := lemma23Point3EquivPi '' E
  have hE₃_meas : MeasurableSet E₃ :=
    lemma23Point3EquivPi.measurableSet_image.mpr hE
  have hvol₃ : volume E₃ = volume E :=
    lemma23_equiv_image_volume hE
      lemma23Point3EquivPi
      lemma23Point3EquivPi_measurePreserving
  let Eprod : Set (ℝ × (Fin 2 → ℝ)) :=
    lemma23Split3Equiv '' E₃
  have hEprod_meas : MeasurableSet Eprod :=
    lemma23Split3Equiv.measurableSet_image.mpr hE₃_meas
  have hsplit_mp :
      MeasurePreserving lemma23Split3Equiv volume volume :=
    MeasureTheory.volume_preserving_piFinSuccAbove
      (fun _ : Fin 3 => ℝ) 2
  have hvolprod : volume Eprod = volume E₃ :=
    lemma23_equiv_image_volume hE₃_meas
      lemma23Split3Equiv hsplit_mp
  have hfubini :
      volume Eprod =
        ∫⁻ z : ℝ, volume {p : Fin 2 → ℝ | (z, p) ∈ Eprod} := by
    rw [MeasureTheory.Measure.volume_eq_prod ℝ (Fin 2 → ℝ)]
    exact Measure.prod_apply hEprod_meas
  have hsection :
      ∀ z : ℝ,
        {p : Fin 2 → ℝ | (z, p) ∈ Eprod} =
          {p : Fin 2 → ℝ |
            lemma23Point3EquivPi.symm
              (lemma23Split3Equiv.symm (z, p)) ∈ E} := by
    intro z
    ext p
    simp only [Eprod, E₃, Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨x, ⟨point, hpoint, hpoint_x⟩, hx⟩
      have hx' : x = lemma23Split3Equiv.symm (z, p) := by
        rw [← hx]
        simp
      have hpoint' :
          point =
            lemma23Point3EquivPi.symm
              (lemma23Split3Equiv.symm (z, p)) := by
        apply lemma23Point3EquivPi.injective
        rw [hpoint_x, hx']
        simp
      rwa [hpoint'] at hpoint
    · intro hp
      let x : Fin 3 → ℝ := lemma23Split3Equiv.symm (z, p)
      let point : Point3 := lemma23Point3EquivPi.symm x
      exact
        ⟨x, ⟨point, hp, by simp [point, x]⟩,
          by simp [x]⟩
  have hslice :
      ∀ z : ℝ,
        volume {p : Fin 2 → ℝ | (z, p) ∈ Eprod} =
          volume (wz1Lemma23PlanarSlice E z) := by
    intro z
    rw [hsection z]
    let S : Set (Fin 2 → ℝ) :=
      {p |
        lemma23Point3EquivPi.symm
          (lemma23Split3Equiv.symm (z, p)) ∈ E}
    have hS_meas : MeasurableSet S := by
      have hmap :
          Measurable
            (fun p : Fin 2 → ℝ =>
              lemma23Point3EquivPi.symm
                (lemma23Split3Equiv.symm (z, p))) := by
        fun_prop
      exact hE.preimage hmap
    have himage :
        lemma23Point2EquivPi.symm '' S =
          wz1Lemma23PlanarSlice E z := by
      rfl
    rw [← himage]
    exact
      (lemma23_equiv_image_volume hS_meas
        lemma23Point2EquivPi.symm
        (PiLp.volume_preserving_toLp
          (ι := Fin 2))).symm
  calc
    volume E = volume E₃ := hvol₃.symm
    _ = volume Eprod := hvolprod.symm
    _ = ∫⁻ z : ℝ,
        volume {p : Fin 2 → ℝ | (z, p) ∈ Eprod} := hfubini
    _ = ∫⁻ z : ℝ, volume (wz1Lemma23PlanarSlice E z) := by
      congr with z
      exact hslice z

/--
If `E` lies in the unit ball and has volume at least `V`, one horizontal
height in `[-1,1]` has planar slice area at least `V / 2`.
-/
theorem wz1_lemma23_exists_good_height_slice
    {E : Set Point3} (hE : MeasurableSet E)
    (hE_ball : E ⊆ Metric.closedBall (0 : Point3) 1)
    {V : ENNReal} (hV : V ≤ volume E) :
    ∃ z ∈ Set.Icc (-1 : ℝ) 1,
      V / 2 ≤ volume (wz1Lemma23PlanarSlice E z) := by
  have hvol :
      volume E =
        ∫⁻ z : ℝ, volume (wz1Lemma23PlanarSlice E z) :=
    wz1_lemma23_volume_eq_lintegral_planarSlice E hE
  by_cases hV_zero : V = 0
  · exact ⟨0, by simp, by simp [hV_zero]⟩
  by_contra h
  push Not at h
  let μ : Measure ℝ :=
    volume.restrict (Set.Icc (-1 : ℝ) 1)
  let sliceArea : ℝ → ENNReal :=
    fun z => volume (wz1Lemma23PlanarSlice E z)
  have hout :
      ∀ z ∉ Set.Icc (-1 : ℝ) 1, sliceArea z = 0 := by
    intro z hz
    have hempty : wz1Lemma23PlanarSlice E z = ∅ := by
      ext p
      simp only [wz1Lemma23PlanarSlice, Set.mem_image,
        Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨q, hq, _⟩
      let point : Point3 :=
        lemma23Point3EquivPi.symm
          (lemma23Split3Equiv.symm (z, q))
      have hpoint : point ∈ E := hq
      have hnorm : ‖point‖ ≤ 1 := by
        simpa [Metric.mem_closedBall] using hE_ball hpoint
      have hzcoord : point 2 = z := by
        simp [point, lemma23Point3EquivPi,
          lemma23Split3Equiv]
      have hcoord : |z| ≤ ‖point‖ := by
        rw [← hzcoord]
        have hle : ‖point 2‖ ≤ ‖point‖ :=
          PiLp.norm_apply_le point 2
        simpa [Real.norm_eq_abs] using hle
      exact hz (abs_le.mp (hcoord.trans hnorm))
    simp [sliceArea, hempty]
  have hle :
      sliceArea ≤ᵐ[μ] fun _ => V / 2 := by
    filter_upwards with z
    by_cases hz : z ∈ Set.Icc (-1 : ℝ) 1
    · exact le_of_lt (h z hz)
    · simp [hout z hz]
  have hint_slice :
      ∫⁻ z, sliceArea z ∂μ = volume E := by
    have hrestrict :
        ∫⁻ z, sliceArea z ∂μ =
          ∫⁻ z in Set.Icc (-1 : ℝ) 1, sliceArea z := rfl
    rw [hrestrict]
    have hfull :
        ∫⁻ z : ℝ, sliceArea z =
          ∫⁻ z in Set.Icc (-1 : ℝ) 1, sliceArea z := by
      rw [← lintegral_indicator measurableSet_Icc]
      congr with z
      by_cases hz : z ∈ Set.Icc (-1 : ℝ) 1
      · simp [hz]
      · simp [hz, hout z hz]
    rw [← hfull, ← hvol]
  have hint_const :
      ∫⁻ _z, V / 2 ∂μ = V := by
    have hvolume :
        volume (Set.Icc (-1 : ℝ) 1) = 2 := by
      norm_num [Real.volume_Icc]
    calc
      ∫⁻ _z, V / 2 ∂μ =
          (V / 2) * volume (Set.Icc (-1 : ℝ) 1) := by
        simp [μ, lintegral_const]
      _ = (V / 2) * 2 := by rw [hvolume]
      _ = V :=
        ENNReal.div_mul_cancel (by norm_num) (by norm_num)
  have hcompare :
      ∫⁻ z, sliceArea z ∂μ ≤
        ∫⁻ _z, V / 2 ∂μ :=
    lintegral_mono_ae hle
  rw [hint_slice, hint_const] at hcompare
  have heq_integral :
      ∫⁻ z, sliceArea z ∂μ =
        ∫⁻ _z, V / 2 ∂μ := by
    rw [hint_slice, hint_const]
    exact le_antisymm hcompare hV
  have hE_lt_top :
      volume E < ⊤ := by
    have hball :
        volume (Metric.closedBall (0 : Point3) 1) < ⊤ :=
      Metric.isBounded_closedBall.measure_lt_top
    exact (measure_mono hE_ball).trans_lt hball
  have hfinite :
      ∫⁻ z, sliceArea z ∂μ ≠ ⊤ := by
    rw [hint_slice]
    exact hE_lt_top.ne
  have hae :
      sliceArea =ᵐ[μ] fun _ => V / 2 :=
    MeasureTheory.ae_eq_of_ae_le_of_lintegral_le
      hle hfinite measurable_const.aemeasurable
      heq_integral.ge
  have hneq :
      ∀ z, sliceArea z ≠ V / 2 := by
    intro z
    by_cases hz : z ∈ Set.Icc (-1 : ℝ) 1
    · exact ne_of_lt (h z hz)
    · rw [hout z hz]
      exact Ne.symm
        (ENNReal.div_ne_zero.mpr
          ⟨hV_zero, by norm_num⟩)
  have hnull :
      μ {z | sliceArea z ≠ V / 2} = 0 := by
    simpa [Filter.EventuallyEq, ae_iff] using hae
  have hall :
      {z | sliceArea z ≠ V / 2} = Set.univ := by
    ext z
    simp [hneq z]
  rw [hall] at hnull
  have hpositive : 0 < μ Set.univ := by
    simp [μ, Real.volume_Icc]
  exact hpositive.ne' hnull

/--
Paper-window variant of `wz1_lemma23_exists_good_height_slice`.  The proof
only needs the vertical support to lie in `[-1,1]`; horizontal unit-ball
containment is irrelevant to the Fubini selection.
-/
theorem wz1_lemma23_exists_good_height_slice_of_height_bound
    {E : Set Point3} (hE : MeasurableSet E)
    (hE_finite : volume E ≠ ⊤)
    (hheight : ∀ point ∈ E, |point (2 : Fin 3)| ≤ 1)
    {V : ENNReal} (hV : V ≤ volume E) :
    ∃ z ∈ Set.Icc (-1 : ℝ) 1,
      V / 2 ≤ volume (wz1Lemma23PlanarSlice E z) := by
  have hvol :
      volume E =
        ∫⁻ z : ℝ, volume (wz1Lemma23PlanarSlice E z) :=
    wz1_lemma23_volume_eq_lintegral_planarSlice E hE
  by_cases hV_zero : V = 0
  · exact ⟨0, by simp, by simp [hV_zero]⟩
  by_contra h
  push Not at h
  let μ : Measure ℝ :=
    volume.restrict (Set.Icc (-1 : ℝ) 1)
  let sliceArea : ℝ → ENNReal :=
    fun z => volume (wz1Lemma23PlanarSlice E z)
  have hout :
      ∀ z ∉ Set.Icc (-1 : ℝ) 1, sliceArea z = 0 := by
    intro z hz
    have hempty : wz1Lemma23PlanarSlice E z = ∅ := by
      ext p
      simp only [wz1Lemma23PlanarSlice, Set.mem_image,
        Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨q, hq, _⟩
      let point : Point3 :=
        lemma23Point3EquivPi.symm
          (lemma23Split3Equiv.symm (z, q))
      have hpoint : point ∈ E := hq
      have hzcoord : point 2 = z := by
        simp [point, lemma23Point3EquivPi,
          lemma23Split3Equiv]
      have hzabs : |z| ≤ 1 := by
        rw [← hzcoord]
        exact hheight point hpoint
      exact hz (abs_le.mp hzabs)
    simp [sliceArea, hempty]
  have hle :
      sliceArea ≤ᵐ[μ] fun _ => V / 2 := by
    filter_upwards with z
    by_cases hz : z ∈ Set.Icc (-1 : ℝ) 1
    · exact le_of_lt (h z hz)
    · simp [hout z hz]
  have hint_slice :
      ∫⁻ z, sliceArea z ∂μ = volume E := by
    have hrestrict :
        ∫⁻ z, sliceArea z ∂μ =
          ∫⁻ z in Set.Icc (-1 : ℝ) 1, sliceArea z := rfl
    rw [hrestrict]
    have hfull :
        ∫⁻ z : ℝ, sliceArea z =
          ∫⁻ z in Set.Icc (-1 : ℝ) 1, sliceArea z := by
      rw [← lintegral_indicator measurableSet_Icc]
      congr with z
      by_cases hz : z ∈ Set.Icc (-1 : ℝ) 1
      · simp [hz]
      · simp [hz, hout z hz]
    rw [← hfull, ← hvol]
  have hint_const :
      ∫⁻ _z, V / 2 ∂μ = V := by
    have hvolume :
        volume (Set.Icc (-1 : ℝ) 1) = 2 := by
      norm_num [Real.volume_Icc]
    calc
      ∫⁻ _z, V / 2 ∂μ =
          (V / 2) * volume (Set.Icc (-1 : ℝ) 1) := by
        simp [μ, lintegral_const]
      _ = (V / 2) * 2 := by rw [hvolume]
      _ = V :=
        ENNReal.div_mul_cancel (by norm_num) (by norm_num)
  have hcompare :
      ∫⁻ z, sliceArea z ∂μ ≤
        ∫⁻ _z, V / 2 ∂μ :=
    lintegral_mono_ae hle
  rw [hint_slice, hint_const] at hcompare
  have heq_integral :
      ∫⁻ z, sliceArea z ∂μ =
        ∫⁻ _z, V / 2 ∂μ := by
    rw [hint_slice, hint_const]
    exact le_antisymm hcompare hV
  have hfinite :
      ∫⁻ z, sliceArea z ∂μ ≠ ⊤ := by
    rw [hint_slice]
    exact hE_finite
  have hae :
      sliceArea =ᵐ[μ] fun _ => V / 2 :=
    MeasureTheory.ae_eq_of_ae_le_of_lintegral_le
      hle hfinite measurable_const.aemeasurable
      heq_integral.ge
  have hneq :
      ∀ z, sliceArea z ≠ V / 2 := by
    intro z
    by_cases hz : z ∈ Set.Icc (-1 : ℝ) 1
    · exact ne_of_lt (h z hz)
    · rw [hout z hz]
      exact Ne.symm
        (ENNReal.div_ne_zero.mpr
          ⟨hV_zero, by norm_num⟩)
  have hnull :
      μ {z | sliceArea z ≠ V / 2} = 0 := by
    simpa [Filter.EventuallyEq, ae_iff] using hae
  have hall :
      {z | sliceArea z ≠ V / 2} = Set.univ := by
    ext z
    simp [hneq z]
  rw [hall] at hnull
  have hpositive : 0 < μ Set.univ := by
    simp [μ, Real.volume_Icc]
  exact hpositive.ne' hnull

/--
On any nondegenerate height interval, one genuine slice has area at least the
average area of the part of `E` in that horizontal slab.
-/
theorem wz1_lemma23_exists_good_height_in_slab
    {E : Set Point3} (hE : MeasurableSet E)
    (hE_finite : volume E ≠ ⊤)
    {a b : ℝ} (hab : a < b) :
    ∃ z ∈ Set.Ico a b,
      volume (E ∩
          {point : Point3 | point (2 : Fin 3) ∈ Set.Ico a b}) /
          ENNReal.ofReal (b - a) ≤
        volume (wz1Lemma23PlanarSlice E z) := by
  let heightSlab : Set Point3 :=
    {point | point (2 : Fin 3) ∈ Set.Ico a b}
  let slab := E ∩ heightSlab
  have hheight_meas :
      MeasurableSet heightSlab := by
    change MeasurableSet
      ((fun point : Point3 => point (2 : Fin 3)) ⁻¹'
        Set.Ico a b)
    exact measurableSet_Ico.preimage
      (PiLp.continuous_apply 2
        (fun _ : Fin 3 => ℝ) (2 : Fin 3)).measurable
  have hslab_meas : MeasurableSet slab :=
    hE.inter hheight_meas
  have hslice_mem :
      ∀ z : ℝ,
        wz1Lemma23PlanarSlice slab z =
          if z ∈ Set.Ico a b then
            wz1Lemma23PlanarSlice E z
          else
            ∅ := by
    intro z
    ext point
    rw [wz1Lemma23_mem_planarSlice_iff]
    by_cases hz : z ∈ Set.Ico a b
    · simp only [hz, if_pos, wz1Lemma23_mem_planarSlice_iff]
      change
        point3 (point 0) (point 1) z ∈
            E ∩ heightSlab ↔
          point3 (point 0) (point 1) z ∈ E
      have hslab :
          point3 (point 0) (point 1) z ∈
            heightSlab := by
        simpa [heightSlab, point3] using hz
      constructor
      · intro hpoint
        exact hpoint.1
      · intro hpoint
        exact ⟨hpoint, hslab⟩
    · dsimp only [slab]
      rw [if_neg hz]
      simp only [Set.notMem_empty, iff_false]
      change
        ¬ point3 (point 0) (point 1) z ∈
          E ∩ heightSlab
      rintro ⟨_, hslab⟩
      apply hz
      simpa [heightSlab, point3] using hslab
  have hslab_volume :
      volume slab =
        ∫⁻ z in Set.Ico a b,
          volume (wz1Lemma23PlanarSlice E z) := by
    have hfubini :=
      wz1_lemma23_volume_eq_lintegral_planarSlice slab hslab_meas
    rw [hfubini]
    rw [← lintegral_indicator measurableSet_Ico]
    apply lintegral_congr
    intro z
    rw [hslice_mem z]
    by_cases hz : z ∈ Set.Ico a b
    · simp [hz]
    · simp [hz]
  have hinterval_ne_zero :
      volume (Set.Ico a b) ≠ 0 := by
    rw [Real.volume_Ico]
    exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne'
  have hslab_integral_finite :
      (∫⁻ z in Set.Ico a b,
          volume (wz1Lemma23PlanarSlice E z)) ≠ ⊤ := by
    rw [← hslab_volume]
    intro htop
    have hle : volume slab ≤ volume E :=
      measure_mono Set.inter_subset_left
    rw [htop] at hle
    exact hE_finite (top_unique hle)
  rcases
      exists_setLAverage_le
        (f := fun z : ℝ =>
          volume (wz1Lemma23PlanarSlice E z))
        hinterval_ne_zero measurableSet_Ico.nullMeasurableSet
        hslab_integral_finite with
    ⟨z, hz, havg⟩
  refine ⟨z, hz, ?_⟩
  rw [setLAverage_eq, Real.volume_Ico] at havg
  change volume slab / ENNReal.ofReal (b - a) ≤
    volume (wz1Lemma23PlanarSlice E z)
  rw [hslab_volume]
  exact havg

end Kakeya.Assouad
