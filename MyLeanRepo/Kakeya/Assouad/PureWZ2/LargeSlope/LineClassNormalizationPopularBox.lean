import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.HorizontalPopularBox

/-!
# Two-coordinate popular boxes for the line-class normalization

The terminal map `diag(lambda, 1, lambda)` expands the first and third
coordinates and leaves the second coordinate unchanged.  Its source
localization must therefore spend exactly two powers of the reciprocal
scale.  This file is the corresponding `(x,z)` pigeonhole; no restriction
is made in the `y` coordinate.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

/-- An `(x,z)` box clipped to the fixed paper window. -/
def pureWZ2LineClassSourceBox
    (center : Point3) (width : ℝ) : Set Point3 :=
  wz1AxisBox center (point3 (width / 2) 1 (width / 2)) ∩
    wz1MildRescalingSourceWindow

/-- Finite two-dimensional pigeonhole in the coordinates expanded by
`diag(lambda, 1, lambda)`. -/
theorem pureWZ2_lineClass_box_pigeonhole
    {delta : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    {width : ℝ} (hwidth : 0 < width) (hwidthOne : width ≤ 1) :
    ∃ center : Point3, center ∈ wz1MildRescalingSourceWindow ∧
      center 1 = 0 ∧
      ENNReal.ofReal (width ^ 2 / 9) * shading.mass ≤
        ∑ index, MeasureTheory.volume
          (shading.carrier index ∩
            pureWZ2LineClassSourceBox center width) := by
  let n : ℕ := Nat.floor (3 / width)
  have hquotientNonnegative : 0 ≤ 3 / width := by positivity
  have hthree : 3 ≤ 3 / width := by
    calc
      3 = 3 * width / width := by field_simp [hwidth.ne']
      _ ≤ 3 / width := by gcongr <;> linarith
  have hnThree : 3 ≤ n :=
    (Nat.le_floor_iff hquotientNonnegative).mpr hthree
  have hnUpper : (n : ℝ) ≤ 3 / width :=
    Nat.floor_le hquotientNonnegative
  have hnStrict : 3 / width < (n : ℝ) + 1 := by
    simpa [n] using Nat.lt_floor_add_one (3 / width)
  have hnWidth : 2 < (n : ℝ) * width := by
    have : 3 < ((n : ℝ) + 1) * width := by
      calc
        3 = (3 / width) * width := by field_simp [hwidth.ne']
        _ < ((n : ℝ) + 1) * width := by gcongr
    nlinarith
  let spacing : ℝ := (2 - width) / ((n : ℝ) - 1)
  have hdenominator : 0 < (n : ℝ) - 1 := by
    have hnOne : (1 : ℝ) < n := by
      exact_mod_cast (show 1 < n by omega)
    linarith
  have hspacingPos : 0 < spacing := by
    dsimp only [spacing]
    exact div_pos (by linarith) hdenominator
  have hspacingLe : spacing ≤ width := by
    dsimp only [spacing]
    apply (div_le_iff₀ hdenominator).2
    nlinarith
  let first : Fin n := ⟨0, by omega⟩
  let last : Fin n := ⟨n - 1, by omega⟩
  let coordinateCenter (index : Fin n) : ℝ :=
    -1 + width / 2 + (index : ℝ) * spacing
  have hfirst : coordinateCenter first = -1 + width / 2 := by
    simp [coordinateCenter, first]
  have hlast : coordinateCenter last = 1 - width / 2 := by
    have hlastValue : (last : ℝ) = (n : ℝ) - 1 := by
      have hlastNat : (last : ℕ) = n - 1 := by simp [last]
      rw [show (last : ℝ) = ↑(last : ℕ) by simp, hlastNat]
      rw [Nat.cast_sub (show 1 ≤ n by omega)]
      simp
    rw [show coordinateCenter last =
      -1 + width / 2 + (last : ℝ) * spacing by rfl, hlastValue]
    dsimp only [spacing]
    field_simp [hdenominator.ne']
    ring
  have hcenterMem : ∀ index : Fin n,
      coordinateCenter index ∈ Set.Icc (-1 : ℝ) 1 := by
    intro index
    have hindexNonnegative : 0 ≤ (index : ℝ) := by positivity
    have hindexUpper : (index : ℝ) ≤ (n : ℝ) - 1 := by
      have hnat : index.val + 1 ≤ n := by omega
      have hreal : (index.val : ℝ) + 1 ≤ n := by exact_mod_cast hnat
      norm_num at hreal ⊢
      linarith
    constructor
    · have : 0 ≤ (index : ℝ) * spacing := by positivity
      dsimp only [coordinateCenter]
      linarith
    · have hmul : (index : ℝ) * spacing ≤
          ((n : ℝ) - 1) * spacing := by gcongr
      have htotal : ((n : ℝ) - 1) * spacing = 2 - width := by
        dsimp only [spacing]
        field_simp [hdenominator.ne']
      rw [htotal] at hmul
      dsimp only [coordinateCenter]
      linarith
  have hcoverOne : ∀ value : ℝ, value ∈ Set.Icc (-1 : ℝ) 1 →
      ∃ index : Fin n, |value - coordinateCenter index| ≤ width / 2 := by
    intro value hvalue
    let candidates : Finset (Fin n) := Finset.univ.filter fun index =>
      value ≤ coordinateCenter index + width / 2
    have hcandidates : candidates.Nonempty := by
      refine ⟨last, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      rw [hlast]
      linarith [hvalue.2]
    let index : Fin n := candidates.min' hcandidates
    have hindexMem : index ∈ candidates := Finset.min'_mem _ _
    have hright : value ≤ coordinateCenter index + width / 2 :=
      (Finset.mem_filter.mp hindexMem).2
    by_cases hzero : index.val = 0
    · have heq : index = first := Fin.ext hzero
      refine ⟨index, abs_le.mpr ⟨?_, ?_⟩⟩
      · rw [heq, hfirst]
        linarith [hvalue.1]
      · linarith
    · let previous : Fin n := ⟨index.val - 1, by omega⟩
      have hpreviousLt : previous < index := by
        simp [previous, Fin.lt_def]
        omega
      have hpreviousNotMem : previous ∉ candidates := by
        intro hmem
        exact (not_le_of_gt hpreviousLt)
          (Finset.min'_le candidates previous hmem)
      have hpreviousRight :
          coordinateCenter previous + width / 2 < value := by
        have hnot : ¬value ≤ coordinateCenter previous + width / 2 := by
          intro hle
          exact hpreviousNotMem
            (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hle⟩)
        exact lt_of_not_ge hnot
      have hindexDifference : (index : ℝ) = (previous : ℝ) + 1 := by
        exact_mod_cast (show index.val = previous.val + 1 by
          simp [previous] <;> omega)
      have hstep : coordinateCenter index =
          coordinateCenter previous + spacing := by
        dsimp only [coordinateCenter]
        rw [hindexDifference]
        ring
      refine ⟨index, abs_le.mpr ⟨?_, ?_⟩⟩
      · rw [hstep]
        linarith
      · linarith
  let Index := Fin n × Fin n
  let center (index : Index) : Point3 :=
    point3 (coordinateCenter index.1) 0 (coordinateCenter index.2)
  let box (index : Index) : Set Point3 :=
    pureWZ2LineClassSourceBox (center index) width
  have hwindow : shading.union ⊆ wz1MildRescalingSourceWindow := by
    rintro point ⟨index, hpoint⟩ coordinate
    have hbox := (shading.subset_body index hpoint).2
    fin_cases coordinate
    · simpa [Kakeya.Streamlined.axisBox] using hbox.1
    · simpa [Kakeya.Streamlined.axisBox] using hbox.2.1
    · simpa [Kakeya.Streamlined.axisBox] using hbox.2.2
  have hcover : shading.union ⊆ ⋃ index : Index, box index := by
    intro point hpoint
    have hcoords : ∀ coordinate : Fin 3, |point coordinate| ≤ 1 :=
      hwindow hpoint
    rcases hcoverOne (point 0) (abs_le.mp (hcoords 0)) with ⟨ix, hx⟩
    rcases hcoverOne (point 2) (abs_le.mp (hcoords 2)) with ⟨iz, hz⟩
    refine Set.mem_iUnion.mpr ⟨(ix, iz), ?_⟩
    refine ⟨?_, hwindow hpoint⟩
    intro coordinate
    fin_cases coordinate
    · simpa [center, pureWZ2LineClassSourceBox, wz1AxisBox, point3] using hx
    · simpa [center, pureWZ2LineClassSourceBox, wz1AxisBox, point3] using
        hcoords 1
    · simpa [center, pureWZ2LineClassSourceBox, wz1AxisBox, point3] using hz
  have hmassCover : shading.mass ≤ ∑ index : Index,
      ∑ tube : Fin family.card, volume (shading.carrier tube ∩ box index) := by
    rw [show shading.mass = ∑ tube : Fin family.card,
        volume (shading.carrier tube) by rfl, Finset.sum_comm]
    apply Finset.sum_le_sum
    intro tube _
    apply measure_cover_le_sum
    intro point hpoint
    exact hcover ⟨tube, hpoint⟩
  let mass (index : Index) : ENNReal :=
    ∑ tube : Fin family.card, volume (shading.carrier tube ∩ box index)
  have hnonemptyIndex : Nonempty Index := ⟨first, first⟩
  letI : Nonempty Index := hnonemptyIndex
  obtain ⟨selected, _hselected, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset Index) mass
      Finset.univ_nonempty
  have hsumUpper : (∑ index : Index, mass index) ≤
      (n : ENNReal) ^ 2 * mass selected := by
    calc
      (∑ index : Index, mass index) ≤
          ∑ _index : Index, mass selected := by
        exact Finset.sum_le_sum fun index hindex =>
          hmax index (Finset.mem_univ index)
      _ = (Fintype.card Index : ENNReal) * mass selected := by
        simp [Finset.sum_const]
      _ = (n : ENNReal) ^ 2 * mass selected := by
        simp [Index, pow_two]
  have hcountFactor : (n : ENNReal) ^ 2 *
      ENNReal.ofReal (width ^ 2 / 9) ≤ 1 := by
    have hreal : (n : ℝ) ^ 2 * (width ^ 2 / 9) ≤ 1 := by
      have hsquare : (n : ℝ) ^ 2 ≤ (3 / width) ^ 2 := by gcongr
      calc
        (n : ℝ) ^ 2 * (width ^ 2 / 9) ≤
            (3 / width) ^ 2 * (width ^ 2 / 9) := by gcongr
        _ = 1 := by field_simp [hwidth.ne'] <;> ring
    rw [show (n : ENNReal) ^ 2 = ENNReal.ofReal ((n : ℝ) ^ 2) by simp]
    rw [← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_le_one]
    exact hreal
  have hselectedMass : ENNReal.ofReal (width ^ 2 / 9) * shading.mass ≤
      mass selected := by
    calc
      ENNReal.ofReal (width ^ 2 / 9) * shading.mass ≤
          ENNReal.ofReal (width ^ 2 / 9) *
            (∑ index : Index, mass index) := by gcongr
      _ ≤ ENNReal.ofReal (width ^ 2 / 9) *
          ((n : ENNReal) ^ 2 * mass selected) := by gcongr
      _ = ((n : ENNReal) ^ 2 *
          ENNReal.ofReal (width ^ 2 / 9)) * mass selected := by ring
      _ ≤ 1 * mass selected := by gcongr
      _ = mass selected := by simp
  refine ⟨center selected, ?_, ?_, ?_⟩
  · intro coordinate
    fin_cases coordinate
    · simpa [center, point3] using abs_le.mpr (hcenterMem selected.1)
    · simp [center, point3]
    · simpa [center, point3] using abs_le.mpr (hcenterMem selected.2)
  · simp [center, point3]
  · change ENNReal.ofReal (width ^ 2 / 9) * shading.mass ≤ mass selected
    exact hselectedMass

/-- The literal restriction to a mass-popular `(x,z)` box. -/
structure PureWZ2LineClassPopularBoxData
    {delta : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family) (width : ℝ) where
  center : Point3
  center_mem : center ∈ wz1MildRescalingSourceWindow
  center_y : center 1 = 0
  restricted : WZ1PaperTubeShading family
  restricted_carrier : ∀ index, restricted.carrier index =
    shading.carrier index ∩ pureWZ2LineClassSourceBox center width
  restricted_subshading : ∀ index, restricted.carrier index ⊆
    shading.carrier index
  mass_lower : ENNReal.ofReal (width ^ 2 / 9) * shading.mass ≤
    restricted.mass

/-- Select the source box used by the line-class-compatible normalization. -/
theorem pureWZ2_lineClass_popular_box
    {delta : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    {width : ℝ} (hwidth : 0 < width) (hwidthOne : width ≤ 1) :
    Nonempty (PureWZ2LineClassPopularBoxData shading width) := by
  rcases pureWZ2_lineClass_box_pigeonhole shading hwidth hwidthOne with
    ⟨center, hcenter, hcenterY, hmass⟩
  let sourceBox := pureWZ2LineClassSourceBox center width
  have hboxMeasurable : MeasurableSet sourceBox := by
    dsimp only [sourceBox, pureWZ2LineClassSourceBox, wz1AxisBox,
      wz1MildRescalingSourceWindow]
    apply MeasurableSet.inter
    · have hmeas : MeasurableSet (⋂ coordinate : Fin 3,
          {point : Point3 | |point coordinate - center coordinate| ≤
            (point3 (width / 2) 1 (width / 2)) coordinate}) :=
        MeasurableSet.iInter fun coordinate => measurableSet_le
          ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) coordinate).sub
            continuous_const |>.abs.measurable) measurable_const
      convert hmeas using 1 <;> ext point <;> simp
    · have hmeas : MeasurableSet (⋂ coordinate : Fin 3,
          {point : Point3 | |point coordinate| ≤ 1}) :=
        MeasurableSet.iInter fun coordinate => measurableSet_le
          ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) coordinate).abs.measurable)
          measurable_const
      convert hmeas using 1 <;> ext point <;> simp
  let restricted : WZ1PaperTubeShading family :=
    { carrier := fun index => shading.carrier index ∩ sourceBox
      measurable_carrier := fun index =>
        (shading.measurable_carrier index).inter hboxMeasurable
      subset_body := fun index => Set.inter_subset_left.trans
        (shading.subset_body index) }
  exact ⟨{
    center := center
    center_mem := hcenter
    center_y := hcenterY
    restricted := restricted
    restricted_carrier := fun _ => rfl
    restricted_subshading := fun _ => Set.inter_subset_left
    mass_lower := by
      change ENNReal.ofReal (width ^ 2 / 9) * shading.mass ≤
        ∑ index : Fin family.card,
          volume (shading.carrier index ∩ sourceBox)
      exact hmass
  }⟩

end Kakeya.Assouad

end
