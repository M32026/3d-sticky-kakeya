import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.HorizontalPopularBox
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.PopularBoxLocalGrains

/-!
# An anisotropic popular box for the final normalization

The final normalization needs a wide horizontal box, of width comparable to
the inverse normalization scale, but only one pre-isotropic grid scale in the
vertical direction.  This two-stage pigeonhole keeps the corresponding
quadratic-times-linear mass factor.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- One-dimensional mass pigeonhole in the paper height window. -/
theorem pureWZ2_vertical_slab_pigeonhole
    {delta : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    {width : ℝ} (hwidth : 0 < width) (hwidthOne : width ≤ 1) :
    ∃ center : ℝ, center ∈ Set.Icc (-1 : ℝ) 1 ∧
      ENNReal.ofReal (width / 3) * shading.mass ≤
        shadedMassInSlab shading (center - width / 2)
          (center + width / 2) := by
  let count : ℕ := Nat.floor (3 / width)
  have hquotientNonnegative : 0 ≤ 3 / width := by positivity
  have hthree : 3 ≤ 3 / width := by
    calc
      3 = 3 * width / width := by field_simp [hwidth.ne']
      _ ≤ 3 / width := by gcongr <;> linarith
  have hcountThree : 3 ≤ count :=
    (Nat.le_floor_iff hquotientNonnegative).mpr hthree
  have hcountUpper : (count : ℝ) ≤ 3 / width :=
    Nat.floor_le hquotientNonnegative
  have hcountStrict : 3 / width < (count : ℝ) + 1 := by
    simpa [count] using Nat.lt_floor_add_one (3 / width)
  have hcountWidth : 2 < (count : ℝ) * width := by
    have : 3 < ((count : ℝ) + 1) * width := by
      calc
        3 = (3 / width) * width := by field_simp [hwidth.ne']
        _ < ((count : ℝ) + 1) * width := by gcongr
    nlinarith
  let spacing : ℝ := (2 - width) / ((count : ℝ) - 1)
  have hdenominator : 0 < (count : ℝ) - 1 := by
    have : (1 : ℝ) < count := by exact_mod_cast (show 1 < count by omega)
    linarith
  have hspacingPos : 0 < spacing := by
    dsimp only [spacing]
    exact div_pos (by linarith) hdenominator
  have hspacingLe : spacing ≤ width := by
    dsimp only [spacing]
    apply (div_le_iff₀ hdenominator).2
    nlinarith
  let first : Fin count := ⟨0, by omega⟩
  let last : Fin count := ⟨count - 1, by omega⟩
  let center (index : Fin count) : ℝ :=
    -1 + width / 2 + (index : ℝ) * spacing
  have hfirst : center first = -1 + width / 2 := by
    simp [center, first]
  have hlast : center last = 1 - width / 2 := by
    have hlastValue : (last : ℝ) = (count : ℝ) - 1 := by
      have hlastNat : (last : ℕ) = count - 1 := by simp [last]
      rw [show (last : ℝ) = ↑(last : ℕ) by simp, hlastNat]
      rw [Nat.cast_sub (show 1 ≤ count by omega)]
      simp
    rw [show center last =
      -1 + width / 2 + (last : ℝ) * spacing by rfl, hlastValue]
    dsimp only [spacing]
    field_simp [hdenominator.ne']
    ring
  have hcenterMem : ∀ index : Fin count,
      center index ∈ Set.Icc (-1 : ℝ) 1 := by
    intro index
    have hindexNonnegative : 0 ≤ (index : ℝ) := by positivity
    have hindexUpper : (index : ℝ) ≤ (count : ℝ) - 1 := by
      have : index.val + 1 ≤ count := by omega
      have hreal : (index.val : ℝ) + 1 ≤ count := by exact_mod_cast this
      norm_num at hreal ⊢
      linarith
    constructor
    · have : 0 ≤ (index : ℝ) * spacing := by positivity
      dsimp only [center]
      linarith
    · have hproduct : (index : ℝ) * spacing ≤
          ((count : ℝ) - 1) * spacing := by gcongr
      have htotal : ((count : ℝ) - 1) * spacing = 2 - width := by
        dsimp only [spacing]
        field_simp [hdenominator.ne']
      rw [htotal] at hproduct
      dsimp only [center]
      linarith
  have hcover : ∀ height : ℝ, height ∈ Set.Icc (-1 : ℝ) 1 →
      ∃ index : Fin count, |height - center index| ≤ width / 2 := by
    intro height hheight
    let candidates : Finset (Fin count) :=
      Finset.univ.filter (fun index => height ≤ center index + width / 2)
    have hcandidates : candidates.Nonempty := by
      refine ⟨last, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      rw [hlast]
      linarith [hheight.2]
    let index : Fin count := candidates.min' hcandidates
    have hindexMem : index ∈ candidates := Finset.min'_mem _ _
    have hright : height ≤ center index + width / 2 :=
      (Finset.mem_filter.mp hindexMem).2
    by_cases hzero : index.val = 0
    · have heq : index = first := Fin.ext hzero
      refine ⟨index, abs_le.mpr ⟨?_, ?_⟩⟩
      rw [heq, hfirst]
      linarith [hheight.1]
      linarith
    · let previous : Fin count := ⟨index.val - 1, by omega⟩
      have hpreviousLt : previous < index := by
        simp [previous, Fin.lt_def]
        omega
      have hpreviousNotMem : previous ∉ candidates := by
        intro hmem
        exact (not_le_of_gt hpreviousLt)
          (Finset.min'_le candidates previous hmem)
      have hpreviousRight : center previous + width / 2 < height := by
        have hnot : ¬height ≤ center previous + width / 2 := by
          intro hle
          exact hpreviousNotMem
            (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hle⟩)
        exact lt_of_not_ge hnot
      have hindexDifference : (index : ℝ) = (previous : ℝ) + 1 := by
        exact_mod_cast (show index.val = previous.val + 1 by
          simp [previous] <;> omega)
      have hstep : center index = center previous + spacing := by
        dsimp only [center]
        rw [hindexDifference]
        ring
      refine ⟨index, abs_le.mpr ⟨?_, ?_⟩⟩
      rw [hstep]
      linarith
      linarith
  have hcarrierCover : ∀ index : Fin family.card,
      shading.carrier index ⊆ ⋃ k : Fin count,
        horizontalSlab (center k - width / 2) (center k + width / 2) := by
    intro index point hpoint
    have hbody := (shading.subset_body index hpoint).2
    have hheight : point 2 ∈ Set.Icc (-1 : ℝ) 1 :=
      abs_le.mp (by simpa [Kakeya.Streamlined.axisBox] using hbody.2.2)
    rcases hcover (point 2) hheight with ⟨k, hk⟩
    exact Set.mem_iUnion.mpr ⟨k, by
      exact ⟨by linarith [(abs_le.mp hk).1],
        by linarith [(abs_le.mp hk).2]⟩⟩
  have hsum : shading.mass ≤ ∑ k : Fin count,
      shadedMassInSlab shading (center k - width / 2)
        (center k + width / 2) := by
    change (∑ index : Fin family.card, volume (shading.carrier index)) ≤ _
    change _ ≤ ∑ k : Fin count, ∑ index : Fin family.card,
      volume (shading.carrier index ∩
        horizontalSlab (center k - width / 2)
          (center k + width / 2))
    rw [show (∑ k : Fin count, ∑ index : Fin family.card,
        volume (shading.carrier index ∩
          horizontalSlab (center k - width / 2)
            (center k + width / 2))) =
      ∑ index : Fin family.card, ∑ k : Fin count,
        volume (shading.carrier index ∩
          horizontalSlab (center k - width / 2)
            (center k + width / 2)) by
      rw [Finset.sum_comm]]
    exact Finset.sum_le_sum fun index _ =>
      measure_cover_le_sum (hcarrierCover index)
  let mass (index : Fin count) : ENNReal :=
    shadedMassInSlab shading (center index - width / 2)
      (center index + width / 2)
  letI : Nonempty (Fin count) := ⟨first⟩
  obtain ⟨selected, _hselected, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin count)) mass
      Finset.univ_nonempty
  have hsumUpper : (∑ index : Fin count, mass index) ≤
      (count : ENNReal) * mass selected := by
    calc
      _ ≤ ∑ _index : Fin count, mass selected := by
        exact Finset.sum_le_sum fun index hindex =>
          hmax index (Finset.mem_univ index)
      _ = (count : ENNReal) * mass selected := by simp [Finset.sum_const]
  have hcountFactor : (count : ENNReal) * ENNReal.ofReal (width / 3) ≤ 1 := by
    have hreal : (count : ℝ) * (width / 3) ≤ 1 := by
      calc
        (count : ℝ) * (width / 3) ≤ (3 / width) * (width / 3) := by
          gcongr
        _ = 1 := by field_simp [hwidth.ne']
    have heq : (count : ENNReal) * ENNReal.ofReal (width / 3) =
        ENNReal.ofReal ((count : ℝ) * (width / 3)) := by
      rw [show (count : ENNReal) = ENNReal.ofReal (count : ℝ) by simp,
        ← ENNReal.ofReal_mul (by positivity)]
    rw [heq, ENNReal.ofReal_le_one]
    exact hreal
  refine ⟨center selected, hcenterMem selected, ?_⟩
  calc
    ENNReal.ofReal (width / 3) * shading.mass ≤
        ENNReal.ofReal (width / 3) *
          (∑ index : Fin count, mass index) := by gcongr
    _ ≤ ENNReal.ofReal (width / 3) *
        ((count : ENNReal) * mass selected) := by gcongr
    _ = ((count : ENNReal) * ENNReal.ofReal (width / 3)) *
        mass selected := by ring
    _ ≤ 1 * mass selected := by gcongr
    _ = mass selected := by simp
    _ = shadedMassInSlab shading (center selected - width / 2)
        (center selected + width / 2) := rfl

/-- A horizontal normalization box with an independently selected short
vertical window. -/
structure PureWZ2FinalAnisotropicPopularBoxData
    {delta : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (horizontalWidth heightWidth : ℝ) where
  center : Point3
  center_mem : center ∈ wz1MildRescalingSourceWindow
  restricted : WZ1PaperTubeShading family
  restricted_subshading : ∀ index,
    restricted.carrier index ⊆ shading.carrier index
  horizontal_close : ∀ point ∈ restricted.union,
    |point 0 - center 0| ≤ horizontalWidth / 2 ∧
      |point 1 - center 1| ≤ horizontalWidth / 2
  height_close : ∀ point ∈ restricted.union,
    |point 2 - center 2| ≤ heightWidth / 2
  mass_lower : ENNReal.ofReal (heightWidth / 3) *
      (ENNReal.ofReal (horizontalWidth ^ 2 / 9) * shading.mass) ≤
    restricted.mass

/-- Select the final anisotropic popular box by a horizontal pigeonhole and
then a vertical pigeonhole. -/
theorem pureWZ2_final_anisotropic_popular_box
    {delta : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    {horizontalWidth heightWidth : ℝ}
    (hhorizontal : 0 < horizontalWidth)
    (hhorizontalOne : horizontalWidth ≤ 1)
    (hheight : 0 < heightWidth) (hheightOne : heightWidth ≤ 1) :
    Nonempty (PureWZ2FinalAnisotropicPopularBoxData shading
      horizontalWidth heightWidth) := by
  rcases pureWZ2_horizontal_popular_box shading hhorizontal hhorizontalOne with
    ⟨horizontal⟩
  rcases pureWZ2_vertical_slab_pigeonhole horizontal.restricted
      hheight hheightOne with ⟨heightCenter, hheightCenter, hmass⟩
  let center := point3 (horizontal.center 0) (horizontal.center 1) heightCenter
  let restricted := pureWZ2PaperRestrictToSet horizontal.restricted
    (horizontalSlab (heightCenter - heightWidth / 2)
      (heightCenter + heightWidth / 2))
    (measurableSet_horizontalSlab _ _)
  refine ⟨{
    center := center
    center_mem := ?_
    restricted := restricted
    restricted_subshading := ?_
    horizontal_close := ?_
    height_close := ?_
    mass_lower := ?_
  }⟩
  · intro coordinate
    fin_cases coordinate
    · simpa [center, point3] using horizontal.center_mem (0 : Fin 3)
    · simpa [center, point3] using horizontal.center_mem (1 : Fin 3)
    · simpa [center, point3] using abs_le.mpr hheightCenter
  · intro index point hpoint
    exact horizontal.restricted_subshading index hpoint.1
  · rintro point ⟨index, hpoint⟩
    have hhorizontalPoint : point ∈ horizontal.restricted.union :=
      ⟨index, hpoint.1⟩
    rw [horizontal.restricted_union, horizontal.box_eq] at hhorizontalPoint
    have hbox := hhorizontalPoint.2.1
    constructor
    · simpa [center, pureWZ2HorizontalSourceBox,
        wz1MildRescalingSourceBox, wz1AxisBox, point3] using hbox (0 : Fin 3)
    · simpa [center, pureWZ2HorizontalSourceBox,
        wz1MildRescalingSourceBox, wz1AxisBox, point3] using hbox (1 : Fin 3)
  · rintro point ⟨index, hpoint⟩
    have hslab := hpoint.2
    change point 2 ∈ Set.Icc (heightCenter - heightWidth / 2)
      (heightCenter + heightWidth / 2) at hslab
    have hcenterTwo : center 2 = heightCenter := by simp [center, point3]
    rw [hcenterTwo]
    rw [abs_le]
    constructor <;> linarith [hslab.1, hslab.2]
  · calc
      ENNReal.ofReal (heightWidth / 3) *
          (ENNReal.ofReal (horizontalWidth ^ 2 / 9) * shading.mass) ≤
        ENNReal.ofReal (heightWidth / 3) * horizontal.restricted.mass := by
          gcongr
          exact horizontal.mass_lower
      _ ≤ restricted.mass := by
        change ENNReal.ofReal (heightWidth / 3) *
          horizontal.restricted.mass ≤ ∑ index : Fin family.card,
            volume (horizontal.restricted.carrier index ∩
              horizontalSlab (heightCenter - heightWidth / 2)
                (heightCenter + heightWidth / 2))
        exact hmass

namespace PureWZ2FinalAnisotropicPopularBoxData

/-- If the vertical width is no larger than the horizontal width, the
anisotropic box lies in the same circumscribed ball as the horizontal cube. -/
theorem restricted_union_subset_ball
    {delta horizontalWidth heightWidth : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (data : PureWZ2FinalAnisotropicPopularBoxData shading
      horizontalWidth heightWidth)
    (hhorizontal : 0 ≤ horizontalWidth)
    (hheight : heightWidth ≤ horizontalWidth) :
    data.restricted.union ⊆
      Metric.closedBall data.center (Real.sqrt 3 * (horizontalWidth / 2)) := by
  intro point hpoint
  have hxy := data.horizontal_close point hpoint
  have hz := data.height_close point hpoint
  have hwidthHalf : heightWidth / 2 ≤ horizontalWidth / 2 := by gcongr
  have hcoord : ∀ coordinate : Fin 3,
      |(point - data.center) coordinate| ≤ horizontalWidth / 2 := by
    intro coordinate
    fin_cases coordinate
    · simpa [PiLp.sub_apply] using hxy.1
    · simpa [PiLp.sub_apply] using hxy.2
    · simpa [PiLp.sub_apply] using hz.trans hwidthHalf
  rw [Metric.mem_closedBall, dist_eq_norm]
  have hradius : 0 ≤ horizontalWidth / 2 := by positivity
  have hsquare : ‖point - data.center‖ ^ 2 ≤
      3 * (horizontalWidth / 2) ^ 2 := by
    have h0 := (sq_le_sq₀
      (abs_nonneg ((point - data.center) 0)) hradius).2 (hcoord 0)
    have h1 := (sq_le_sq₀
      (abs_nonneg ((point - data.center) 1)) hradius).2 (hcoord 1)
    have h2 := (sq_le_sq₀
      (abs_nonneg ((point - data.center) 2)) hradius).2 (hcoord 2)
    rw [EuclideanSpace.real_norm_sq_eq]
    norm_num [Fin.sum_univ_succ]
    have h0' : (point 0 - data.center 0) ^ 2 ≤
        (horizontalWidth / 2) ^ 2 := by
      simpa [PiLp.sub_apply, sq_abs] using h0
    have h1' : (point 1 - data.center 1) ^ 2 ≤
        (horizontalWidth / 2) ^ 2 := by
      simpa [PiLp.sub_apply, sq_abs] using h1
    have h2' : (point 2 - data.center 2) ^ 2 ≤
        (horizontalWidth / 2) ^ 2 := by
      simpa [PiLp.sub_apply, sq_abs] using h2
    nlinarith
  have hsqrtSquare :
      (Real.sqrt 3 * (horizontalWidth / 2)) ^ 2 =
        3 * (horizontalWidth / 2) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg 3)
    hradius)).mp
  rwa [hsqrtSquare]

end PureWZ2FinalAnisotropicPopularBoxData

end Kakeya.Assouad

end
