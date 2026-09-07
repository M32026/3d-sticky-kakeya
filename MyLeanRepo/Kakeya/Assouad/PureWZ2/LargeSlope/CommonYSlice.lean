import MyLeanRepo.Kakeya.Assouad.Definitions
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.CroppedPopularGlobalGrains
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Genuine common y-slices for WZ2 Section 6

This module isolates the measure-theoretic coordinate split used by the
large-slope argument.  The slice is the actual plane `y = y₀`, represented in
the `(x,z)` coordinates.  In particular, no thick slab or arbitrary point is
substituted for the common slice.
-/

noncomputable section

open MeasureTheory Set

namespace Kakeya.Assouad

/-- Compatibility name for the unit-constant literal global grain. -/
abbrev pureWZ2GlobalGrain
    (slope : ℝ → ℝ) (delta : ℝ) (anchor : Point3) : Set Point3 :=
  pureWZ2GlobalGrainWithConstant 1 slope delta anchor

private def commonYSlicePoint3EquivPi : Point3 ≃ᵐ (Fin 3 → ℝ) :=
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

private def commonYSlicePoint2EquivPi : Point2 ≃ᵐ (Fin 2 → ℝ) :=
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

/-- Split the y-coordinate from a three-dimensional coordinate function. -/
private def commonYSliceSplit3Equiv :
    (Fin 3 → ℝ) ≃ᵐ (ℝ × (Fin 2 → ℝ)) :=
  MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 1

/-- The genuine `y = y₀` slice, represented in `(x,z)` coordinates. -/
def pureWZ2YSlice (E : Set Point3) (y : ℝ) : Set Point2 :=
  commonYSlicePoint2EquivPi.symm ''
    {coordinates : Fin 2 → ℝ |
      commonYSlicePoint3EquivPi.symm
          (commonYSliceSplit3Equiv.symm (y, coordinates)) ∈ E}

private lemma commonYSlice_split_point
    (y : ℝ) (coordinates : Fin 2 → ℝ) :
    commonYSlicePoint3EquivPi.symm
        (commonYSliceSplit3Equiv.symm (y, coordinates)) =
      point3 (coordinates 0) y (coordinates 1) := by
  ext index
  fin_cases index
  · simp [commonYSlicePoint3EquivPi, commonYSliceSplit3Equiv,
      Fin.insertNth_apply_below, point3]
  · simp [commonYSlicePoint3EquivPi, commonYSliceSplit3Equiv,
      Fin.insertNth_apply_same, point3]
  · simp [commonYSlicePoint3EquivPi, commonYSliceSplit3Equiv,
      Fin.insertNth, Fin.succAboveCases, point3]

/-- Coordinate description of a genuine common y-slice. -/
theorem pureWZ2_mem_ySlice_iff
    {E : Set Point3} {y : ℝ} {point : Point2} :
    point ∈ pureWZ2YSlice E y ↔
      point3 (point 0) y (point 1) ∈ E := by
  simp only [pureWZ2YSlice, Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨coordinates, hcoordinates, hpoint⟩
    rw [← hpoint]
    rw [commonYSlice_split_point] at hcoordinates
    simpa [commonYSlicePoint2EquivPi] using hcoordinates
  · intro hpoint
    refine ⟨commonYSlicePoint2EquivPi point, ?_, by simp⟩
    rw [commonYSlice_split_point]
    simpa [commonYSlicePoint2EquivPi] using hpoint

private def pureWZ2PlanarRectangle
    (left right bottom top : ℝ) : Set Point2 :=
  {point | point 0 ∈ Set.Icc left right ∧
    point 1 ∈ Set.Icc bottom top}

private lemma pureWZ2PlanarRectangle_volume
    (left right bottom top : ℝ) :
    volume (pureWZ2PlanarRectangle left right bottom top) =
      ENNReal.ofReal (right - left) * ENNReal.ofReal (top - bottom) := by
  let lower : Fin 2 → ℝ := fun index =>
    if index = 0 then left else bottom
  let upper : Fin 2 → ℝ := fun index =>
    if index = 0 then right else top
  have hrectangle :
      pureWZ2PlanarRectangle left right bottom top =
        commonYSlicePoint2EquivPi ⁻¹' Set.Icc lower upper := by
    ext point
    simp only [pureWZ2PlanarRectangle, Set.mem_setOf_eq,
      Set.mem_preimage, Set.mem_Icc]
    constructor
    · rintro ⟨hfirst, hsecond⟩
      constructor
      · intro index
        fin_cases index
        · simpa [lower, commonYSlicePoint2EquivPi] using hfirst.1
        · simpa [lower, commonYSlicePoint2EquivPi] using hsecond.1
      · intro index
        fin_cases index
        · simpa [upper, commonYSlicePoint2EquivPi] using hfirst.2
        · simpa [upper, commonYSlicePoint2EquivPi] using hsecond.2
    · rintro ⟨hlower, hupper⟩
      constructor
      · constructor
        · simpa [lower, commonYSlicePoint2EquivPi] using hlower (0 : Fin 2)
        · simpa [upper, commonYSlicePoint2EquivPi] using hupper (0 : Fin 2)
      · constructor
        · simpa [lower, commonYSlicePoint2EquivPi] using hlower (1 : Fin 2)
        · simpa [upper, commonYSlicePoint2EquivPi] using hupper (1 : Fin 2)
  rw [hrectangle]
  have hpreserving :
      MeasurePreserving commonYSlicePoint2EquivPi volume volume :=
    PiLp.volume_preserving_ofLp (ι := Fin 2)
  have hmeasure :=
    hpreserving.measure_preimage
      (isCompact_Icc.measurableSet.nullMeasurableSet :
        NullMeasurableSet (Set.Icc lower upper) volume)
  rw [hmeasure, Real.volume_Icc_pi, Fin.prod_univ_two]
  simp [lower, upper]

/-- A global grain has one `2 * delta` interval in each exact `(x,z)` slice. -/
theorem pureWZ2_ySlice_globalGrain_subset_rectangle
    (slope : ℝ → ℝ) (delta y : ℝ) (anchor : Point3) :
    pureWZ2YSlice (pureWZ2GlobalGrain slope delta anchor) y ⊆
      pureWZ2PlanarRectangle
          (anchor (0 : Fin 3) -
            slope (anchor (2 : Fin 3)) *
              (y - anchor (1 : Fin 3)) - delta)
          (anchor (0 : Fin 3) -
            slope (anchor (2 : Fin 3)) *
              (y - anchor (1 : Fin 3)) + delta)
          (anchor (2 : Fin 3) - delta)
          (anchor (2 : Fin 3) + delta) := by
  intro point hpoint
  have hgrain := pureWZ2_mem_ySlice_iff.mp hpoint
  rcases hgrain with ⟨hz, hprojection⟩
  have hprojection_raw :
      |point 0 + slope (anchor 2) * y -
          (anchor 0 + slope (anchor 2) * anchor 1)| ≤ delta := by
    simpa [globalGrainDirection, point3, Fin.sum_univ_succ,
      PiLp.inner_apply] using hprojection
  have hprojection' :
      |point 0 - anchor 0 +
          slope (anchor 2) * (y - anchor 1)| ≤ delta := by
    convert hprojection_raw using 1 <;> ring
  have hx := abs_le.mp hprojection'
  have hz_raw : |point 1 - anchor 2| ≤ delta := by
    simpa [point3] using hz
  have hz' := abs_le.mp hz_raw
  constructor
  · constructor <;> linarith
  · constructor <;> linarith

/-- Exact y-slices of one literal global grain have area at most `4 delta^2`. -/
theorem pureWZ2_ySlice_globalGrain_volume_upper
    (slope : ℝ → ℝ) {delta : ℝ} (hdelta : 0 ≤ delta)
    (y : ℝ) (anchor : Point3) :
    volume (pureWZ2YSlice
        (pureWZ2GlobalGrain slope delta anchor) y) ≤
      ENNReal.ofReal (4 * delta ^ 2) := by
  let left : ℝ := anchor 0 -
    slope (anchor 2) * (y - anchor 1) - delta
  let right : ℝ := anchor 0 -
    slope (anchor 2) * (y - anchor 1) + delta
  let bottom : ℝ := anchor 2 - delta
  let top : ℝ := anchor 2 + delta
  have hsubset :
      pureWZ2YSlice (pureWZ2GlobalGrain slope delta anchor) y ⊆
        pureWZ2PlanarRectangle left right bottom top := by
    simpa [left, right, bottom, top] using
      pureWZ2_ySlice_globalGrain_subset_rectangle slope delta y anchor
  calc
    volume (pureWZ2YSlice
        (pureWZ2GlobalGrain slope delta anchor) y)
        ≤ volume (pureWZ2PlanarRectangle left right bottom top) :=
      measure_mono hsubset
    _ = ENNReal.ofReal (2 * delta) * ENNReal.ofReal (2 * delta) := by
      rw [pureWZ2PlanarRectangle_volume]
      congr 2 <;> dsimp [left, right, bottom, top] <;> ring
    _ = ENNReal.ofReal (4 * delta ^ 2) := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * delta)]
      congr 1
      ring

private lemma commonYSlicePoint3EquivPi_measurePreserving :
    MeasurePreserving commonYSlicePoint3EquivPi volume volume := by
  have hsymm :
      MeasurePreserving commonYSlicePoint3EquivPi.symm volume volume :=
    PiLp.volume_preserving_toLp (ι := Fin 3)
  have hmap :
      Measure.map commonYSlicePoint3EquivPi.symm volume = volume :=
    hsymm.map_eq
  refine ⟨commonYSlicePoint3EquivPi.measurable, ?_⟩
  calc
    Measure.map commonYSlicePoint3EquivPi volume =
        Measure.map commonYSlicePoint3EquivPi
          (Measure.map commonYSlicePoint3EquivPi.symm volume) := by
      rw [hmap]
    _ = Measure.map
        (commonYSlicePoint3EquivPi ∘ commonYSlicePoint3EquivPi.symm)
        volume := by
      rw [Measure.map_map
        commonYSlicePoint3EquivPi.measurable
        commonYSlicePoint3EquivPi.symm.measurable]
    _ = volume := by
      have hcomp :
          commonYSlicePoint3EquivPi ∘ commonYSlicePoint3EquivPi.symm = id := by
        funext coordinates
        simp
      rw [hcomp]
      simp

private lemma commonYSlicePoint2EquivPi_measurePreserving :
    MeasurePreserving commonYSlicePoint2EquivPi volume volume := by
  have hsymm :
      MeasurePreserving commonYSlicePoint2EquivPi.symm volume volume :=
    PiLp.volume_preserving_toLp (ι := Fin 2)
  have hmap :
      Measure.map commonYSlicePoint2EquivPi.symm volume = volume :=
    hsymm.map_eq
  refine ⟨commonYSlicePoint2EquivPi.measurable, ?_⟩
  calc
    Measure.map commonYSlicePoint2EquivPi volume =
        Measure.map commonYSlicePoint2EquivPi
          (Measure.map commonYSlicePoint2EquivPi.symm volume) := by
      rw [hmap]
    _ = Measure.map
        (commonYSlicePoint2EquivPi ∘ commonYSlicePoint2EquivPi.symm)
        volume := by
      rw [Measure.map_map
        commonYSlicePoint2EquivPi.measurable
        commonYSlicePoint2EquivPi.symm.measurable]
    _ = volume := by
      have hcomp :
          commonYSlicePoint2EquivPi ∘ commonYSlicePoint2EquivPi.symm = id := by
        funext coordinates
        simp
      rw [hcomp]
      simp

private lemma commonYSlice_equiv_image_volume
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β}
    {S : Set α} (hS : MeasurableSet S)
    (equiv : α ≃ᵐ β) (hpreserving : MeasurePreserving equiv μ ν) :
    ν (equiv '' S) = μ S := by
  rw [← hpreserving.map_eq]
  rw [Measure.map_apply equiv.measurable
    (equiv.measurableSet_image.mpr hS)]
  rw [equiv.preimage_image]

/-- Three-dimensional volume is the integral of genuine y-slice areas. -/
theorem pureWZ2_volume_eq_lintegral_ySlice
    (E : Set Point3) (hE : MeasurableSet E) :
    volume E = ∫⁻ y : ℝ, volume (pureWZ2YSlice E y) := by
  let E₃ : Set (Fin 3 → ℝ) := commonYSlicePoint3EquivPi '' E
  have hE₃_meas : MeasurableSet E₃ :=
    commonYSlicePoint3EquivPi.measurableSet_image.mpr hE
  have hvol₃ : volume E₃ = volume E :=
    commonYSlice_equiv_image_volume hE
      commonYSlicePoint3EquivPi
      commonYSlicePoint3EquivPi_measurePreserving
  let Eprod : Set (ℝ × (Fin 2 → ℝ)) :=
    commonYSliceSplit3Equiv '' E₃
  have hEprod_meas : MeasurableSet Eprod :=
    commonYSliceSplit3Equiv.measurableSet_image.mpr hE₃_meas
  have hsplit_preserving :
      MeasurePreserving commonYSliceSplit3Equiv volume volume :=
    MeasureTheory.volume_preserving_piFinSuccAbove
      (fun _ : Fin 3 => ℝ) 1
  have hvolprod : volume Eprod = volume E₃ :=
    commonYSlice_equiv_image_volume hE₃_meas
      commonYSliceSplit3Equiv hsplit_preserving
  have hfubini :
      volume Eprod =
        ∫⁻ y : ℝ, volume {coordinates : Fin 2 → ℝ | (y, coordinates) ∈ Eprod} := by
    rw [MeasureTheory.Measure.volume_eq_prod ℝ (Fin 2 → ℝ)]
    exact Measure.prod_apply hEprod_meas
  have hsection :
      ∀ y : ℝ,
        {coordinates : Fin 2 → ℝ | (y, coordinates) ∈ Eprod} =
          {coordinates : Fin 2 → ℝ |
            commonYSlicePoint3EquivPi.symm
              (commonYSliceSplit3Equiv.symm (y, coordinates)) ∈ E} := by
    intro y
    ext coordinates
    simp only [Eprod, E₃, Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨source, ⟨point, hpoint, hpoint_source⟩, hsource⟩
      have hsource' :
          source = commonYSliceSplit3Equiv.symm (y, coordinates) := by
        rw [← hsource]
        simp
      have hpoint' :
          point = commonYSlicePoint3EquivPi.symm
            (commonYSliceSplit3Equiv.symm (y, coordinates)) := by
        apply commonYSlicePoint3EquivPi.injective
        rw [hpoint_source, hsource']
        simp
      rwa [hpoint'] at hpoint
    · intro hpoint
      let source : Fin 3 → ℝ :=
        commonYSliceSplit3Equiv.symm (y, coordinates)
      let point : Point3 := commonYSlicePoint3EquivPi.symm source
      exact
        ⟨source, ⟨point, hpoint, by simp [point, source]⟩,
          by simp [source]⟩
  have hslice :
      ∀ y : ℝ,
        volume {coordinates : Fin 2 → ℝ | (y, coordinates) ∈ Eprod} =
          volume (pureWZ2YSlice E y) := by
    intro y
    rw [hsection y]
    let source : Set (Fin 2 → ℝ) :=
      {coordinates |
        commonYSlicePoint3EquivPi.symm
          (commonYSliceSplit3Equiv.symm (y, coordinates)) ∈ E}
    have hsource_meas : MeasurableSet source := by
      have hmap :
          Measurable
            (fun coordinates : Fin 2 → ℝ =>
              commonYSlicePoint3EquivPi.symm
                (commonYSliceSplit3Equiv.symm (y, coordinates))) := by
        fun_prop
      exact hE.preimage hmap
    have himage :
        commonYSlicePoint2EquivPi.symm '' source = pureWZ2YSlice E y := by
      rfl
    rw [← himage]
    exact
      (commonYSlice_equiv_image_volume hsource_meas
        commonYSlicePoint2EquivPi.symm
        (PiLp.volume_preserving_toLp (ι := Fin 2))).symm
  calc
    volume E = volume E₃ := hvol₃.symm
    _ = volume Eprod := hvolprod.symm
    _ = ∫⁻ y : ℝ,
        volume {coordinates : Fin 2 → ℝ | (y, coordinates) ∈ Eprod} := hfubini
    _ = ∫⁻ y : ℝ, volume (pureWZ2YSlice E y) := by
      congr with y
      exact hslice y

/--
Fubini averaging on an arbitrary measurable set of admissible y-values.
The support hypothesis ensures that no mass is lost outside `good`.
-/
theorem pureWZ2_exists_ySlice_average_on
    {E : Set Point3} (hE : MeasurableSet E)
    (hE_finite : volume E ≠ ⊤)
    {good : Set ℝ} (hgood : MeasurableSet good)
    (hgood_ne_zero : volume good ≠ 0)
    (hE_good : ∀ point ∈ E, point (1 : Fin 3) ∈ good) :
    ∃ y ∈ good,
      volume E / volume good ≤ volume (pureWZ2YSlice E y) := by
  let sliceArea : ℝ → ENNReal :=
    fun y => volume (pureWZ2YSlice E y)
  have houtside :
      ∀ y ∉ good, sliceArea y = 0 := by
    intro y hy
    have hempty : pureWZ2YSlice E y = ∅ := by
      ext point
      simp only [pureWZ2_mem_ySlice_iff, Set.notMem_empty, iff_false]
      intro hpoint
      apply hy
      simpa [point3] using hE_good _ hpoint
    simp [sliceArea, hempty]
  have hfull :
      ∫⁻ y : ℝ, sliceArea y = ∫⁻ y in good, sliceArea y := by
    rw [← lintegral_indicator hgood]
    apply lintegral_congr
    intro y
    by_cases hy : y ∈ good
    · simp [hy]
    · simp [hy, houtside y hy]
  have hintegral :
      ∫⁻ y in good, sliceArea y = volume E := by
    rw [← hfull, ← pureWZ2_volume_eq_lintegral_ySlice E hE]
  have hintegral_finite :
      (∫⁻ y in good, sliceArea y) ≠ ⊤ := by
    rw [hintegral]
    exact hE_finite
  rcases
      exists_setLAverage_le
        (f := sliceArea) hgood_ne_zero hgood.nullMeasurableSet
        hintegral_finite with
    ⟨y, hy, havg⟩
  refine ⟨y, hy, ?_⟩
  rw [setLAverage_eq, hintegral] at havg
  exact havg

end Kakeya.Assouad

end
