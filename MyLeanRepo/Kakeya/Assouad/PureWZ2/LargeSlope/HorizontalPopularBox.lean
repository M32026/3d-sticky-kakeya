import MyLeanRepo.Kakeya.Assouad.WZ1.MildRescalingBoxPigeonholeHelpers
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.ConfigurationRestriction

/-!
# Mass-popular horizontal box for Proposition 6.5

This is the two-dimensional pigeonhole used before horizontal normalization.
It restricts only the first two coordinates and retains the entire paper
height window.  Consequently the mass loss is quadratic in the width, while
the selected center has height zero.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

/-- A horizontal box of side length `width`, clipped to the fixed paper
window.  Its vertical half-width is one, so a center of height zero retains
the whole paper height interval. -/
def pureWZ2HorizontalSourceBox (center : Point3) (width : ℝ) : Set Point3 :=
  wz1MildRescalingSourceBox center
    (point3 (width / 2) (width / 2) 1)

/-- Finite two-dimensional box pigeonhole.  Only the horizontal coordinates
are divided, giving the factor `width ^ 2 / 9`. -/
theorem pureWZ2_horizontal_box_pigeonhole
    {delta : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    {width : ℝ} (hwidth : 0 < width) (hwidthOne : width ≤ 1) :
    ∃ center : Point3,
      center ∈ wz1MildRescalingSourceWindow ∧
      center 2 = 0 ∧
      ENNReal.ofReal (width ^ 2 / 9) * shading.mass ≤
        ∑ index, MeasureTheory.volume
          (shading.carrier index ∩
            pureWZ2HorizontalSourceBox center width) := by
  let n : ℕ := Nat.floor (3 / width)
  have hnonneg : 0 ≤ 3 / width := by positivity
  have hthree : 3 ≤ 3 / width := by
    calc
      3 = 3 * width / width := by field_simp [hwidth.ne']
      _ ≤ 3 / width := by
        gcongr
        linarith
  have hn3 : n ≥ 3 :=
    (Nat.le_floor_iff hnonneg).mpr hthree
  have hn : (n : ℝ) ≤ 3 / width := Nat.floor_le hnonneg
  have hnUpper : 3 / width < (n : ℝ) + 1 := by
    simpa [n] using Nat.lt_floor_add_one (3 / width)
  have hnWidth : (n : ℝ) * width > 2 := by
    have hmul : 3 < ((n : ℝ) + 1) * width := by
      calc
        3 = (3 / width) * width := by field_simp [hwidth.ne']
        _ < ((n : ℝ) + 1) * width := by gcongr
    rw [show ((n : ℝ) + 1) * width = (n : ℝ) * width + width by ring]
      at hmul
    linarith
  set spacing : ℝ := (2 - width) / ((n : ℝ) - 1) with hspacing
  have hdenom : 0 < (n : ℝ) - 1 := by linarith
  have hspacingPos : 0 < spacing := by
    rw [hspacing]
    have : 0 < 2 - width := by linarith
    positivity
  have hspacingLe : spacing ≤ width := by
    rw [hspacing]
    have hnumerator : 2 - width ≤ ((n : ℝ) - 1) * width := by
      linarith
    calc
      (2 - width) / ((n : ℝ) - 1) ≤
          (((n : ℝ) - 1) * width) / ((n : ℝ) - 1) := by gcongr
      _ = width := by field_simp [hdenom.ne']
  let first : Fin n := ⟨0, by omega⟩
  let last : Fin n := ⟨n - 1, by omega⟩
  let coordinateCenter : Fin n → ℝ :=
    fun k => -1 + width / 2 + (k : ℝ) * spacing
  have hfirst : coordinateCenter first = -1 + width / 2 := by
    simp [coordinateCenter, first]
  have hlast : coordinateCenter last = 1 - width / 2 := by
    have hlastValue : (last : ℝ) = (n : ℝ) - 1 := by
      have hlastNat : (last : ℕ) = n - 1 := by simp [last]
      rw [show (last : ℝ) = ↑(last : ℕ) by simp, hlastNat]
      rw [Nat.cast_sub (show 1 ≤ n by omega)]
      simp
    rw [show coordinateCenter last =
      -1 + width / 2 + (last : ℝ) * spacing by rfl]
    rw [hlastValue, hspacing]
    field_simp [hdenom.ne']
    ring
  have hcenterMem :
      ∀ k : Fin n, coordinateCenter k ∈ Set.Icc (-1 : ℝ) 1 := by
    intro k
    have hkNonneg : 0 ≤ (k : ℝ) := by exact_mod_cast Nat.zero_le k.val
    have hkLe : (k : ℝ) ≤ (n : ℝ) - 1 := by
      have hk : k.val + 1 ≤ n := by omega
      have hk' : (k : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hk
      linarith
    constructor
    · have hproduct : 0 ≤ (k : ℝ) * spacing := by positivity
      change -1 ≤ -1 + width / 2 + (k : ℝ) * spacing
      linarith
    · have hproduct :
          (k : ℝ) * spacing ≤ ((n : ℝ) - 1) * spacing :=
        mul_le_mul_of_nonneg_right hkLe hspacingPos.le
      have htotal : ((n : ℝ) - 1) * spacing = 2 - width := by
        rw [hspacing]
        field_simp [hdenom.ne']
      rw [htotal] at hproduct
      change -1 + width / 2 + (k : ℝ) * spacing ≤ 1
      linarith
  have hcoverOne :
      ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 →
        ∃ k : Fin n, |x - coordinateCenter k| ≤ width / 2 := by
    intro x hx
    let candidates : Finset (Fin n) :=
      Finset.univ.filter (fun k => x ≤ coordinateCenter k + width / 2)
    have hcandidates : candidates.Nonempty := by
      have hxLast : x ≤ coordinateCenter last + width / 2 := by
        rw [hlast]
        linarith [hx.2]
      exact ⟨last, by simp [candidates, hxLast]⟩
    let k : Fin n := candidates.min' hcandidates
    have hkMem : k ∈ candidates := Finset.min'_mem candidates hcandidates
    have hkRight : x ≤ coordinateCenter k + width / 2 := by
      simpa [candidates, Finset.mem_filter] using hkMem
    by_cases hkZero : k.val = 0
    · have hkFirst : k = first := by
        apply Fin.ext
        simp [first, hkZero]
      refine ⟨first, ?_⟩
      rw [abs_le]
      have hleft : coordinateCenter first - width / 2 ≤ x := by
        rw [hfirst]
        linarith [hx.1]
      rw [hkFirst] at hkRight
      constructor <;> linarith
    · have hkPos : 0 < k.val := by omega
      let previous : Fin n := ⟨k.val - 1, by omega⟩
      have hpreviousLt : previous < k := by
        simp [previous, Fin.lt_def]
        omega
      have hpreviousNotMem : previous ∉ candidates := by
        intro hmem
        have hle : k ≤ previous := Finset.min'_le candidates previous hmem
        exact not_le.mpr hpreviousLt hle
      have hpreviousRight :
          coordinateCenter previous + width / 2 < x := by
        have hnot :
            ¬x ≤ coordinateCenter previous + width / 2 := by
          simpa [candidates, Finset.mem_filter] using hpreviousNotMem
        linarith
      have hkDifference : (k : ℝ) = (previous : ℝ) + 1 := by
        have hvalue : k.val = previous.val + 1 := by
          simp [previous]
          omega
        exact_mod_cast hvalue
      have hstep :
          coordinateCenter k = coordinateCenter previous + spacing := by
        change -1 + width / 2 + (k : ℝ) * spacing =
          (-1 + width / 2 + (previous : ℝ) * spacing) + spacing
        rw [hkDifference]
        ring
      have hleft : coordinateCenter k - width / 2 ≤ x := by
        rw [hstep]
        linarith [hspacingLe]
      refine ⟨k, ?_⟩
      rw [abs_le]
      constructor <;> linarith
  let Index := Fin n × Fin n
  let center : Index → Point3 :=
    fun p => point3 (coordinateCenter p.1) (coordinateCenter p.2) 0
  let box : Index → Set Point3 :=
    fun p => pureWZ2HorizontalSourceBox (center p) width
  have hwindowCover :
      wz1MildRescalingSourceWindow ⊆ ⋃ p : Index, box p := by
    intro point hpoint
    have hcoordinates : ∀ i : Fin 3, |point i| ≤ 1 := by
      simpa [wz1MildRescalingSourceWindow, Set.mem_setOf_eq] using hpoint
    obtain ⟨firstIndex, hfirstIndex⟩ :=
      hcoverOne (point 0) (abs_le.mp (hcoordinates 0))
    obtain ⟨secondIndex, hsecondIndex⟩ :=
      hcoverOne (point 1) (abs_le.mp (hcoordinates 1))
    let p : Index := (firstIndex, secondIndex)
    have haxis : point ∈ wz1AxisBox (center p)
        (point3 (width / 2) (width / 2) 1) := by
      simp only [wz1AxisBox, Set.mem_setOf_eq]
      intro i
      fin_cases i
      · simpa [center, point3_apply] using hfirstIndex
      · simpa [center, point3_apply] using hsecondIndex
      · simpa [center, point3_apply] using hcoordinates 2
    have hbox : point ∈ box p := by
      exact ⟨haxis, hpoint⟩
    exact Set.mem_iUnion.mpr ⟨p, hbox⟩
  have hshadingWindow : shading.union ⊆ wz1MildRescalingSourceWindow := by
    rintro point ⟨index, hpoint⟩ coordinate
    have hbody := (shading.subset_body index hpoint).2
    fin_cases coordinate
    · simpa [Kakeya.Streamlined.axisBox] using hbody.1
    · simpa [Kakeya.Streamlined.axisBox] using hbody.2.1
    · simpa [Kakeya.Streamlined.axisBox] using hbody.2.2
  have hcarrierCover :
      ∀ index : Fin family.card,
        shading.carrier index ⊆ ⋃ p : Index, box p := by
    intro index
    exact subset_trans
      (show shading.carrier index ⊆ shading.union from
        fun point hpoint => ⟨index, hpoint⟩)
      (subset_trans hshadingWindow hwindowCover)
  have hvolume :
      ∀ index : Fin family.card,
        volume (shading.carrier index) ≤
          ∑ p : Index, volume (shading.carrier index ∩ box p) := by
    intro index
    exact measure_cover_le_sum (hcarrierCover index)
  have hsum :
      shading.mass ≤
        ∑ p : Index,
          ∑ index : Fin family.card,
            volume (shading.carrier index ∩ box p) := by
    calc
      shading.mass = ∑ index : Fin family.card,
          volume (shading.carrier index) := by rfl
      _ ≤ ∑ index : Fin family.card,
          ∑ p : Index, volume (shading.carrier index ∩ box p) :=
        Finset.sum_le_sum (fun index _ => hvolume index)
      _ = ∑ p : Index,
          ∑ index : Fin family.card,
            volume (shading.carrier index ∩ box p) := by
        rw [Finset.sum_comm]
  let captured : Index → ENNReal :=
    fun p => ∑ index : Fin family.card,
      volume (shading.carrier index ∩ box p)
  let threshold : Index → ENNReal :=
    fun _ => ENNReal.ofReal (width ^ 2 / 9) * shading.mass
  have hIndexNonempty : Nonempty Index := ⟨(first, first)⟩
  have hcard : Fintype.card Index = n ^ 2 := by
    simp [Index, Fintype.card_prod]
    ring
  have hthresholdSum :
      ∑ p : Index, threshold p =
        (Fintype.card Index : ENNReal) *
          ENNReal.ofReal (width ^ 2 / 9) * shading.mass := by
    simp [threshold, Finset.sum_const, hcard]
    ring
  have hsquare :
      (n ^ 2 : ENNReal) * ENNReal.ofReal (width ^ 2 / 9) ≤ 1 := by
    have hreal : (n : ℝ) ^ 2 * (width ^ 2 / 9) ≤ 1 := by
      have hnSq : (n : ℝ) ^ 2 ≤ (3 / width) ^ 2 := by gcongr
      have hnormalize : (3 / width) ^ 2 * (width ^ 2 / 9) = 1 := by
        field_simp [hwidth.ne']
        ring
      calc
        (n : ℝ) ^ 2 * (width ^ 2 / 9) ≤
            (3 / width) ^ 2 * (width ^ 2 / 9) := by gcongr
        _ = 1 := hnormalize
    have heq :
        (n ^ 2 : ENNReal) * ENNReal.ofReal (width ^ 2 / 9) =
          ENNReal.ofReal ((n : ℝ) ^ 2 * (width ^ 2 / 9)) := by
      have hnCast : (n : ENNReal) = ENNReal.ofReal (n : ℝ) := by simp
      rw [hnCast, ← ENNReal.ofReal_pow (by positivity)]
      rw [← ENNReal.ofReal_mul (by positivity)]
    rw [heq, ENNReal.ofReal_le_one]
    exact hreal
  have hsumCompare :
      ∑ p : Index, threshold p ≤ ∑ p : Index, captured p := by
    rw [hthresholdSum, hcard]
    have hcast : (↑(n ^ 2) : ENNReal) = (↑n ^ 2 : ENNReal) := by
      rw [Nat.cast_pow]
    rw [hcast]
    exact (calc
      (↑n ^ 2 : ENNReal) * ENNReal.ofReal (width ^ 2 / 9) *
            shading.mass ≤ 1 * shading.mass := by gcongr
      _ = shading.mass := by ring
      _ ≤ ∑ p : Index, captured p := hsum)
  have hexists : ∃ p : Index, threshold p ≤ captured p := by
    simpa using ENNReal.exists_le_of_sum_le
      (Finset.univ_nonempty : (Finset.univ : Finset Index).Nonempty)
      hsumCompare
  rcases hexists with ⟨p, hp⟩
  have hselectedCenter : center p ∈ wz1MildRescalingSourceWindow := by
    have hcoords : ∀ i : Fin 3, |(center p) i| ≤ 1 := by
      intro i
      fin_cases i
      · simpa [center, point3_apply] using abs_le.mpr (hcenterMem p.1)
      · simpa [center, point3_apply] using abs_le.mpr (hcenterMem p.2)
      · simp [center, point3_apply]
    simpa [wz1MildRescalingSourceWindow, Set.mem_setOf_eq] using hcoords
  refine ⟨center p, hselectedCenter, ?_, ?_⟩
  · simp [center, point3_apply]
  · change ENNReal.ofReal (width ^ 2 / 9) * shading.mass ≤
      ∑ index : Fin family.card,
        volume (shading.carrier index ∩
          pureWZ2HorizontalSourceBox (center p) width)
    exact hp

/-- A literal restriction of a paper shading to a mass-popular horizontal
box.  The height coordinate is not pigeonholed. -/
structure PureWZ2HorizontalPopularBoxData
    {delta : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family) (width : ℝ) where
  center : Point3
  center_mem : center ∈ wz1MildRescalingSourceWindow
  center_height : center 2 = 0
  box : Set Point3
  box_eq : box = pureWZ2HorizontalSourceBox center width
  box_measurable : MeasurableSet box
  restricted : WZ1PaperTubeShading family
  restricted_carrier : ∀ index, restricted.carrier index =
    shading.carrier index ∩ box
  restricted_subshading : ∀ index,
    restricted.carrier index ⊆ shading.carrier index
  restricted_union : restricted.union = shading.union ∩ box
  mass_lower : ENNReal.ofReal (width ^ 2 / 9) * shading.mass ≤
    restricted.mass

/-- Select a mass-popular horizontal box, retaining the full height window. -/
theorem pureWZ2_horizontal_popular_box
    {delta : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    {width : ℝ} (hwidth : 0 < width) (hwidthOne : width ≤ 1) :
    Nonempty (PureWZ2HorizontalPopularBoxData shading width) := by
  rcases pureWZ2_horizontal_box_pigeonhole shading hwidth hwidthOne with
    ⟨center, hcenter, hcenterHeight, hmass⟩
  let box := pureWZ2HorizontalSourceBox center width
  have hboxMeasurable : MeasurableSet box := by
    dsimp only [box, pureWZ2HorizontalSourceBox,
      wz1MildRescalingSourceBox, wz1AxisBox,
      wz1MildRescalingSourceWindow]
    apply MeasurableSet.inter
    · have hmeas : MeasurableSet (⋂ coordinate : Fin 3,
          {point : Point3 |
            |point coordinate - center coordinate| ≤
              (point3 (width / 2) (width / 2) 1) coordinate}) :=
        MeasurableSet.iInter fun coordinate : Fin 3 =>
          measurableSet_le
            ((show Continuous (fun point : Point3 => point coordinate) from
                PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) coordinate).sub
              (show Continuous (fun _point : Point3 => center coordinate) from
                continuous_const)).abs.measurable
            (show Measurable (fun _point : Point3 =>
              (point3 (width / 2) (width / 2) 1) coordinate) from
                measurable_const)
      have hset : {point : Point3 | ∀ coordinate : Fin 3,
          |point coordinate - center coordinate| ≤
            (point3 (width / 2) (width / 2) 1) coordinate} =
          ⋂ coordinate : Fin 3, {point : Point3 |
            |point coordinate - center coordinate| ≤
              (point3 (width / 2) (width / 2) 1) coordinate} := by
        ext point
        simp
      rw [hset]
      exact hmeas
    · have hmeas : MeasurableSet (⋂ coordinate : Fin 3,
          {point : Point3 | |point coordinate| ≤ 1}) :=
        MeasurableSet.iInter fun coordinate : Fin 3 =>
          measurableSet_le ((show Continuous
            (fun point : Point3 => point coordinate) from
              PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ)
                coordinate).abs.measurable) measurable_const
      have hset : {point : Point3 | ∀ coordinate : Fin 3,
          |point coordinate| ≤ 1} =
          ⋂ coordinate : Fin 3,
            {point : Point3 | |point coordinate| ≤ 1} := by
        ext point
        simp
      rw [hset]
      exact hmeas
  let restricted : WZ1PaperTubeShading family :=
    { carrier := fun index => shading.carrier index ∩ box
      measurable_carrier := fun index =>
        (shading.measurable_carrier index).inter hboxMeasurable
      subset_body := fun index => Set.inter_subset_left.trans
        (shading.subset_body index) }
  have hunion : restricted.union = shading.union ∩ box := by
    ext point
    constructor
    · rintro ⟨index, hsource, hbox⟩
      exact ⟨⟨index, hsource⟩, hbox⟩
    · rintro ⟨⟨index, hsource⟩, hbox⟩
      exact ⟨index, hsource, hbox⟩
  exact ⟨{
    center := center
    center_mem := hcenter
    center_height := hcenterHeight
    box := box
    box_eq := rfl
    box_measurable := hboxMeasurable
    restricted := restricted
    restricted_carrier := fun _ => rfl
    restricted_subshading := fun _ => Set.inter_subset_left
    restricted_union := hunion
    mass_lower := by
      change ENNReal.ofReal (width ^ 2 / 9) * shading.mass ≤
        ∑ index, volume (shading.carrier index ∩ box)
      simpa [box] using hmass
  }⟩

end Kakeya.Assouad

end
