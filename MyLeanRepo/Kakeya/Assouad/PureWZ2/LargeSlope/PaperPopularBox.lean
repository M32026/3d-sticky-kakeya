import MyLeanRepo.Kakeya.Assouad.WZ1.MildRescalingBoxPigeonhole
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.ConfigurationRestriction

/-!
# Mass-popular box for a pure paper shading

This specializes the closed WZ1 box pigeonhole to the cropped paper carrier.
The output is an ordinary measurable restriction; later literal cubical
saturation is performed only after the full affine map.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

structure PureWZ2PaperPopularBoxData
    {delta : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family) (width : ℝ) where
  center : Point3
  center_mem : center ∈ wz1MildRescalingSourceWindow
  box : Set Point3
  box_eq : box = wz1MildRescalingSourceBox center
    (point3 (width / 2) (width / 2) (width / 2))
  box_measurable : MeasurableSet box
  restricted : WZ1PaperTubeShading family
  restricted_carrier : ∀ index, restricted.carrier index =
    shading.carrier index ∩ box
  restricted_subshading : ∀ index,
    restricted.carrier index ⊆ shading.carrier index
  restricted_union : restricted.union = shading.union ∩ box
  mass_lower : ENNReal.ofReal (width ^ 3 / 27) * shading.mass ≤
    restricted.mass

/-- The literal restriction selected by the box pigeonhole lies in the
Euclidean ball circumscribing that box. -/
theorem PureWZ2PaperPopularBoxData.restricted_union_subset_ball
    {delta width : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (data : PureWZ2PaperPopularBoxData shading width)
    (hwidth : 0 ≤ width) :
    data.restricted.union ⊆
      Metric.closedBall data.center (Real.sqrt 3 * (width / 2)) := by
  rintro point hpoint
  rw [data.restricted_union, data.box_eq] at hpoint
  have haxis := hpoint.2.1
  rw [Metric.mem_closedBall, dist_eq_norm]
  let radius := width / 2
  have hradius : 0 ≤ radius := by
    dsimp only [radius]
    positivity
  have hcoord : ∀ coordinate : Fin 3,
      |(point - data.center) coordinate| ≤ radius := by
    intro coordinate
    fin_cases coordinate
    · simpa [radius, PiLp.sub_apply, point3, PiLp.single_apply] using
        haxis 0
    · simpa [radius, PiLp.sub_apply, point3, PiLp.single_apply] using
        haxis 1
    · simpa [radius, PiLp.sub_apply, point3, PiLp.single_apply] using
        haxis 2
  have hsquare : ‖point - data.center‖ ^ 2 ≤ 3 * radius ^ 2 := by
    have h0 := (sq_le_sq₀
      (abs_nonneg ((point - data.center) 0)) hradius).2 (hcoord 0)
    have h1 := (sq_le_sq₀
      (abs_nonneg ((point - data.center) 1)) hradius).2 (hcoord 1)
    have h2 := (sq_le_sq₀
      (abs_nonneg ((point - data.center) 2)) hradius).2 (hcoord 2)
    have h0' : ((point - data.center) 0) ^ 2 ≤ radius ^ 2 := by
      simpa only [sq_abs] using h0
    have h1' : ((point - data.center) 1) ^ 2 ≤ radius ^ 2 := by
      simpa only [sq_abs] using h1
    have h2' : ((point - data.center) 2) ^ 2 ≤ radius ^ 2 := by
      simpa only [sq_abs] using h2
    have h0'' : (point 0 - data.center 0) ^ 2 ≤ radius ^ 2 := by
      simpa only [PiLp.sub_apply] using h0'
    have h1'' : (point 1 - data.center 1) ^ 2 ≤ radius ^ 2 := by
      simpa only [PiLp.sub_apply] using h1'
    have h2'' : (point 2 - data.center 2) ^ 2 ≤ radius ^ 2 := by
      simpa only [PiLp.sub_apply] using h2'
    rw [EuclideanSpace.real_norm_sq_eq]
    norm_num [Fin.sum_univ_succ]
    nlinarith [h0'', h1'', h2'']
  have hsqrtSq : (Real.sqrt 3 * radius) ^ 2 = 3 * radius ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have hright : 0 ≤ Real.sqrt 3 * radius := by positivity
  change ‖point - data.center‖ ≤ Real.sqrt 3 * radius
  apply (sq_le_sq₀ (norm_nonneg _) hright).mp
  rw [hsqrtSq]
  exact hsquare

theorem pureWZ2_paper_popular_box
    {delta : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    {width : ℝ} (hwidth : 0 < width) (hwidthOne : width ≤ 1) :
    Nonempty (PureWZ2PaperPopularBoxData shading width) := by
  have hunionWindow : shading.union ⊆ wz1MildRescalingSourceWindow := by
    rintro point ⟨index, hpoint⟩ coordinate
    have hbox := (shading.subset_body index hpoint).2
    fin_cases coordinate
    · simpa [Kakeya.Streamlined.axisBox] using hbox.1
    · simpa [Kakeya.Streamlined.axisBox] using hbox.2.1
    · simpa [Kakeya.Streamlined.axisBox] using hbox.2.2
  rcases wz1_mild_rescaling_box_pigeonhole shading
      hunionWindow width
      hwidth hwidthOne with ⟨center, _hcenterMargin, hcenter, hmass⟩
  let halfWidth := point3 (width / 2) (width / 2) (width / 2)
  let box := wz1MildRescalingSourceBox center halfWidth
  have hboxMeasurable : MeasurableSet box := by
    dsimp only [box, wz1MildRescalingSourceBox, wz1AxisBox,
      wz1MildRescalingSourceWindow]
    apply MeasurableSet.inter
    · have hmeas : MeasurableSet (⋂ coordinate : Fin 3,
          {point : Point3 |
            |point coordinate - center coordinate| ≤ halfWidth coordinate}) :=
        MeasurableSet.iInter fun coordinate : Fin 3 =>
          measurableSet_le
            ((show Continuous (fun point : Point3 => point coordinate) from
                PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ)
                  coordinate).sub
              (show Continuous (fun _point : Point3 => center coordinate) from
                continuous_const)).abs.measurable
            (show Measurable (fun _point : Point3 => halfWidth coordinate) from
              measurable_const)
      have hset : {point : Point3 | ∀ coordinate : Fin 3,
          |point coordinate - center coordinate| ≤ halfWidth coordinate} =
          ⋂ coordinate : Fin 3,
            {point : Point3 |
              |point coordinate - center coordinate| ≤ halfWidth coordinate} := by
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
                coordinate).abs.measurable)
            (show Measurable (fun _point : Point3 => (1 : ℝ)) from
              measurable_const)
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
  have hmass' : ENNReal.ofReal (width ^ 3 / 27) * shading.mass ≤
      restricted.mass := by
    change ENNReal.ofReal (width ^ 3 / 27) * shading.mass ≤
      ∑ index : Fin (wz1PaperBodyFamily family).card,
        volume (shading.carrier index ∩ box)
    simpa [box, halfWidth] using hmass
  exact ⟨{
    center := center
    center_mem := hcenter
    box := box
    box_eq := rfl
    box_measurable := hboxMeasurable
    restricted := restricted
    restricted_carrier := fun _ => rfl
    restricted_subshading := fun _ => Set.inter_subset_left
    restricted_union := hunion
    mass_lower := hmass'
  }⟩

end Kakeya.Assouad

end
