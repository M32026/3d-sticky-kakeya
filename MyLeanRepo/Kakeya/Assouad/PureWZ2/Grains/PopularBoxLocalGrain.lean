import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PopularBox
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.LocalGrainRestriction
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.LocalAD
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CubicalSlabLower

/-!
# Popular grid-aligned box for strict local grains

The box restriction is common-spatial: every surviving point keeps all of its
tube memberships.  Hence strict local grains restrict directly, while the
grid alignment preserves cubicality.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Metric Set

attribute [local instance] Classical.propDecidable

/-- Select one mass-popular grid-aligned box on a paper shading. -/
theorem popular_box_shading
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    (hdelta : 0 < delta)
    (hcubical : WZ1PaperIsCubicalShading source)
    (K : ℕ) (hK : 0 < K) (hKeven : K % 2 = 0)
    (hKdelta : (K : ℝ) * delta ≤ 1) :
    ∃ (center : Point3)
      (selected : WZ1PaperTubeShading family),
      (∀ coordinate : Fin 3,
        ∃ index : ℤ, center coordinate = (index : ℝ) * delta) ∧
      PaperIsSubshading selected source ∧
      WZ1PaperIsCubicalShading selected ∧
      ENNReal.ofReal (((K : ℝ) * delta) ^ 3 / 8000) * source.mass ≤
        selected.mass ∧
      (∀ first second : Point3,
        first ∈ selected.union → second ∈ selected.union →
          dist first second ≤
            Real.sqrt 3 * ((K : ℝ) * delta + 2 * delta)) := by
  have hsourceWindow : source.union ⊆ pureWZ2SourceWindow := by
    rintro point ⟨index, hpoint⟩
    have hbox := (source.subset_body index hpoint).2
    intro coordinate
    fin_cases coordinate
    · have h : |point 0| ≤ 1 := by
        simpa [Kakeya.Streamlined.axisBox] using hbox.1
      simpa using h.trans (show (1 : ℝ) ≤ 2 by norm_num)
    · have h : |point 1| ≤ 1 := by
        simpa [Kakeya.Streamlined.axisBox] using hbox.2.1
      simpa using h.trans (show (1 : ℝ) ≤ 2 by norm_num)
    · have h : |point 2| ≤ 1 := by
        simpa [Kakeya.Streamlined.axisBox] using hbox.2.2
      simpa using h.trans (show (1 : ℝ) ≤ 2 by norm_num)
  rcases pureWZ2_grid_aligned_box_pigeonhole source hsourceWindow
      hdelta K hK hKeven hKdelta with
    ⟨center, hcenterGrid, _hcenterWindow, hmass⟩
  let halfWidth : Point3 :=
    point3 (((K : ℝ) * delta) / 2)
      (((K : ℝ) * delta) / 2) (((K : ℝ) * delta) / 2)
  let box : Set Point3 := pureWZ2SourceBox center halfWidth
  have hboxMeasurable : MeasurableSet box := by
    have haxisClosed : IsClosed (wz1AxisBox center halfWidth) := by
      have heq : wz1AxisBox center halfWidth =
          ⋂ coordinate : Fin 3,
            {point : Point3 |
              |point coordinate - center coordinate| ≤ halfWidth coordinate} := by
        ext point
        simp [wz1AxisBox]
      rw [heq]
      exact isClosed_iInter fun coordinate =>
        isClosed_le
          (continuous_abs.comp
            ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) coordinate).sub
              continuous_const)) continuous_const
    have hwindowClosed : IsClosed pureWZ2SourceWindow := by
      have heq : pureWZ2SourceWindow =
          ⋂ coordinate : Fin 3, {point : Point3 | |point coordinate| ≤ 2} := by
        ext point
        simp [pureWZ2SourceWindow]
      rw [heq]
      exact isClosed_iInter fun coordinate =>
        isClosed_le
          (continuous_abs.comp
            (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) coordinate))
          continuous_const
    exact (haxisClosed.inter hwindowClosed).measurableSet
  let activeCells : Set (ℤ × ℤ × ℤ) :=
    {cell | (wz1PaperGridCube delta cell ∩ box).Nonempty}
  let saturated : Set Point3 :=
    (wz1PaperGridIndex delta) ⁻¹' activeCells
  have hgridMeasurable : Measurable (wz1PaperGridIndex delta) := by
    have h : Measurable (fun point : Point3 =>
        (⌊point 0 / delta⌋, ⌊point 1 / delta⌋,
          ⌊point 2 / delta⌋)) := by
      fun_prop
    convert h using 1
    funext point
    simp [wz1PaperGridIndex, gridIndex]
  have hsaturatedMeasurable : MeasurableSet saturated := by
    exact hgridMeasurable
      (DiscreteMeasurableSpace.forall_measurableSet activeCells)
  have hboxSubset : box ⊆ saturated := by
    intro point hpoint
    change wz1PaperGridIndex delta point ∈ activeCells
    exact ⟨point,
      (mem_wz1PaperGridCube delta
        (wz1PaperGridIndex delta point) point).mpr rfl, hpoint⟩
  let selected :=
    paperRestrictShadingToSet source saturated hsaturatedMeasurable
  have hselectedSub : PaperIsSubshading selected source :=
    fun _ _ hpoint => hpoint.1
  have hwhole : ∀ point ∈ saturated,
      wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆
        saturated := by
    intro point hpoint other hother
    have hgrid : wz1PaperGridIndex delta other =
        wz1PaperGridIndex delta point :=
      (mem_wz1PaperGridCube delta
        (wz1PaperGridIndex delta point) other).mp hother
    change wz1PaperGridIndex delta other ∈ activeCells
    rw [hgrid]
    exact hpoint
  have hselectedCubical : WZ1PaperIsCubicalShading selected :=
    paperRestrictShadingToSet_cubical hsaturatedMeasurable hcubical hwhole
  have hselectedMass :
      ENNReal.ofReal (((K : ℝ) * delta) ^ 3 / 8000) * source.mass ≤
        selected.mass := by
    calc
      ENNReal.ofReal (((K : ℝ) * delta) ^ 3 / 8000) * source.mass
          ≤ ∑ index, volume (source.carrier index ∩ box) := by
            simpa [box, halfWidth] using hmass
      _ ≤ ∑ index, volume (source.carrier index ∩ saturated) := by
        apply Finset.sum_le_sum
        intro index _
        exact measure_mono (Set.inter_subset_inter_right _ hboxSubset)
      _ = selected.mass := rfl
  have hdiameter : ∀ first second : Point3,
      first ∈ selected.union → second ∈ selected.union →
        dist first second ≤
          Real.sqrt 3 * ((K : ℝ) * delta + 2 * delta) := by
    intro first second hfirst hsecond
    rcases hfirst with ⟨firstIndex, hfirst⟩
    rcases hsecond with ⟨secondIndex, hsecond⟩
    have hfirstSaturated : first ∈ saturated := hfirst.2
    have hsecondSaturated : second ∈ saturated := hsecond.2
    rcases hfirstSaturated with ⟨firstWitness, hfirstWitnessCell,
      hfirstWitnessBox⟩
    rcases hsecondSaturated with ⟨secondWitness, hsecondWitnessCell,
      hsecondWitnessBox⟩
    have hfirstCell : first ∈ wz1PaperGridCube delta
        (wz1PaperGridIndex delta firstWitness) := by
      rw [mem_wz1PaperGridCube]
      exact hfirstWitnessCell.symm
    have hsecondCell : second ∈ wz1PaperGridCube delta
        (wz1PaperGridIndex delta secondWitness) := by
      rw [mem_wz1PaperGridCube]
      exact hsecondWitnessCell.symm
    have hfirstNear : dist first firstWitness ≤ Real.sqrt 3 * delta := by
      simpa [mul_comm] using
        wz1PaperGridCube_diameter hdelta _ hfirstCell
          ((mem_wz1PaperGridCube delta _ firstWitness).mpr rfl)
    have hsecondNear : dist secondWitness second ≤ Real.sqrt 3 * delta := by
      rw [dist_comm]
      simpa [mul_comm] using
        wz1PaperGridCube_diameter hdelta _ hsecondCell
          ((mem_wz1PaperGridCube delta _ secondWitness).mpr rfl)
    have hwitnessCoordinates : ∀ coordinate : Fin 3,
        |firstWitness coordinate - secondWitness coordinate| ≤
          (K : ℝ) * delta := by
      intro coordinate
      have hfirstAxis := hfirstWitnessBox.1 coordinate
      have hsecondAxis := hsecondWitnessBox.1 coordinate
      have hhalf : halfWidth coordinate = ((K : ℝ) * delta) / 2 := by
        fin_cases coordinate <;> simp [halfWidth, point3]
      rw [hhalf] at hfirstAxis hsecondAxis
      rw [abs_le] at hfirstAxis hsecondAxis ⊢
      constructor <;> linarith
    have hwitnessDistance :
        dist firstWitness secondWitness ≤
          Real.sqrt 3 * ((K : ℝ) * delta) := by
      rw [dist_eq_norm]
      have hnormSquare : ‖firstWitness - secondWitness‖ ^ 2 =
          (firstWitness 0 - secondWitness 0) ^ 2 +
            (firstWitness 1 - secondWitness 1) ^ 2 +
              (firstWitness 2 - secondWitness 2) ^ 2 := by
        simpa [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] using
          EuclideanSpace.real_norm_sq_eq (firstWitness - secondWitness)
      have hboundSquare : ∀ coordinate : Fin 3,
          (firstWitness coordinate - secondWitness coordinate) ^ 2 ≤
            ((K : ℝ) * delta) ^ 2 := by
        intro coordinate
        nlinarith [abs_le.mp (hwitnessCoordinates coordinate)]
      have hsqrtSquare : (Real.sqrt 3 * ((K : ℝ) * delta)) ^ 2 =
          3 * ((K : ℝ) * delta) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by norm_num)]
      have hnonnegative : 0 ≤ Real.sqrt 3 * ((K : ℝ) * delta) := by
        positivity
      nlinarith [norm_nonneg (firstWitness - secondWitness),
        hboundSquare 0, hboundSquare 1, hboundSquare 2]
    calc
      dist first second ≤ dist first firstWitness +
          dist firstWitness secondWitness + dist secondWitness second := by
        linarith [dist_triangle first firstWitness second,
          dist_triangle firstWitness secondWitness second]
      _ ≤ Real.sqrt 3 * delta +
          Real.sqrt 3 * ((K : ℝ) * delta) +
            Real.sqrt 3 * delta := by gcongr
      _ = Real.sqrt 3 * ((K : ℝ) * delta + 2 * delta) := by ring
  exact ⟨center, selected, hcenterGrid, hselectedSub,
    hselectedCubical, hselectedMass, hdiameter⟩

/-- Select one mass-popular grid-aligned box and retain strict local grains
on the resulting genuine multi-tube restriction. -/
theorem popular_box_local_grain
    {delta sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {C : ENNReal}
    (localGrains : PureWZ2LocalGrainData source sigma C)
    (hdelta : 0 < delta)
    (hcubical : WZ1PaperIsCubicalShading source)
    (K : ℕ) (hK : 0 < K) (hKeven : K % 2 = 0)
    (hKdelta : (K : ℝ) * delta ≤ 1) :
    ∃ (center : Point3)
      (selected : WZ1PaperTubeShading family)
      (selectedLocal : PureWZ2LocalGrainData selected sigma C),
      (∀ coordinate : Fin 3,
        ∃ index : ℤ, center coordinate = (index : ℝ) * delta) ∧
      PaperIsSubshading selected source ∧
      WZ1PaperIsCubicalShading selected ∧
      ENNReal.ofReal (((K : ℝ) * delta) ^ 3 / 8000) * source.mass ≤
        selected.mass ∧
      (∀ first second : Point3,
        first ∈ selected.union → second ∈ selected.union →
          dist first second ≤
            Real.sqrt 3 * ((K : ℝ) * delta + 2 * delta)) := by
  rcases popular_box_shading hdelta hcubical K hK hKeven hKdelta with
    ⟨center, selected, hcenter, hselectedSub, hselectedCubical,
      hselectedMass, hdiameter⟩
  exact ⟨center, selected, localGrains.restrict hselectedSub,
    hcenter, hselectedSub, hselectedCubical, hselectedMass, hdiameter⟩

end Kakeya.Assouad.PureWZ2

end
