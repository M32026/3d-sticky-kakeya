import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63MildRescalingGeometry
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PopularBoxLocalGrain

/-!
# A mass-popular shifted grid core for mild rescaling

The generic popular-box theorem uses a saturated box.  Mild rescaling asks
instead for the smaller set of grid cells wholly contained in its geometric
normalization window.  We choose a slightly smaller grid-aligned source box;
every grid cell meeting that box is then contained in the mild-rescaling
window.  The numerical margin still retains the required
`1 / (2000000 * scale^3)` fraction of shaded mass.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- The shifted mild-rescaling core is measurable. -/
lemma measurableSet_pureWZ2ShiftedOriginGridCore
    (delta scale : ℝ) (center : Point3) :
    MeasurableSet
      (pureWZ2ShiftedOriginGridCore delta scale center) := by
  let window : Set Point3 :=
    {point | ∀ coordinate : Fin 3,
      |point coordinate - center coordinate| ≤
        1 / (9 * scale) - 6 * delta}
  have hindex : Measurable (wz1PaperGridIndex delta) := by
    have h : Measurable (fun point : Point3 =>
        (⌊point 0 / delta⌋, ⌊point 1 / delta⌋,
          ⌊point 2 / delta⌋)) := by
      fun_prop
    convert h using 1
    funext point
    simp [wz1PaperGridIndex, gridIndex]
  have heq :
      pureWZ2ShiftedOriginGridCore delta scale center =
        (wz1PaperGridIndex delta) ⁻¹'
          {index : ℤ × ℤ × ℤ |
            wz1PaperGridCube delta index ⊆ window} := by
    rfl
  rw [heq]
  exact hindex
    (DiscreteMeasurableSpace.forall_measurableSet _)

/-- The shifted core is a union of complete source grid cells. -/
lemma pureWZ2ShiftedOriginGridCore_whole_cell
    (delta scale : ℝ) (center : Point3) :
    ∀ point ∈ pureWZ2ShiftedOriginGridCore delta scale center,
      wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆
        pureWZ2ShiftedOriginGridCore delta scale center := by
  intro point hpoint other hother
  have hindex :
      wz1PaperGridIndex delta other =
        wz1PaperGridIndex delta point :=
    (mem_wz1PaperGridCube delta
      (wz1PaperGridIndex delta point) other).mp hother
  change
    wz1PaperGridCube delta (wz1PaperGridIndex delta other) ⊆ _
  rw [hindex]
  exact hpoint

/-- Select a grid center whose complete shifted core carries the mass fraction
required by `pureWZ2_grain_mild_rescale`. -/
theorem popular_shifted_grid_core_shading
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (source : WZ1PaperTubeShading family)
    (hdelta : 0 < delta)
    (hcubical : WZ1PaperIsCubicalShading source)
    (scale : ℝ)
    (hscale : 1 ≤ scale)
    (hsmall : scale * delta ≤ 1 / 1000) :
    ∃ (center : Point3)
      (selected : WZ1PaperTubeShading family),
      (∀ coordinate : Fin 3,
        ∃ index : ℤ,
          center coordinate = (index : ℝ) * delta) ∧
      center ∈ pureWZ2SourceWindow ∧
      PaperIsSubshading selected source ∧
      WZ1PaperIsCubicalShading selected ∧
      ENNReal.ofReal ((1 / 2000000 : ℝ) / scale ^ 3) *
          source.mass ≤
        selected.mass ∧
      (∀ index,
        selected.carrier index =
          source.carrier index ∩
            pureWZ2ShiftedOriginGridCore delta scale center) := by
  have hscalePos : 0 < scale := lt_of_lt_of_le (by norm_num) hscale
  have hdeltaScalePos : 0 < scale * delta := mul_pos hscalePos hdelta
  let n : ℕ := Nat.floor (1 / (10 * scale * delta))
  let K : ℕ := 2 * n
  have hxNonneg : 0 ≤ 1 / (10 * scale * delta) := by positivity
  have hxLarge : (100 : ℝ) ≤ 1 / (10 * scale * delta) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hnLarge : 100 ≤ n := by
    exact (Nat.le_floor_iff hxNonneg).mpr hxLarge
  have hnPos : 0 < n := by omega
  have hKPos : 0 < K := by
    dsimp only [K]
    omega
  have hKEven : K % 2 = 0 := by
    simp [K]
  have hnUpper : (n : ℝ) ≤ 1 / (10 * scale * delta) :=
    Nat.floor_le hxNonneg
  have hnLower :
      1 / (10 * scale * delta) - 1 < (n : ℝ) := by
    linarith [Nat.lt_floor_add_one (1 / (10 * scale * delta))]
  have hKdeltaUpper : (K : ℝ) * delta ≤ 1 / (5 * scale) := by
    dsimp only [K]
    push_cast
    calc
      (2 : ℝ) * n * delta ≤
          2 * (1 / (10 * scale * delta)) * delta := by
        gcongr
      _ = 1 / (5 * scale) := by
        field_simp [hscalePos.ne', hdelta.ne']
        norm_num
  have hKdeltaOne : (K : ℝ) * delta ≤ 1 := by
    calc
      (K : ℝ) * delta ≤ 1 / (5 * scale) := hKdeltaUpper
      _ ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith
  have hsourceWindow : source.union ⊆ pureWZ2SourceWindow := by
    rintro point ⟨index, hpoint⟩
    have hbox := (source.subset_body index hpoint).2
    intro coordinate
    have hcoordinate : |point coordinate| ≤ 1 := by
      fin_cases coordinate
      · simpa [Kakeya.Streamlined.axisBox] using hbox.1
      · simpa [Kakeya.Streamlined.axisBox] using hbox.2.1
      · simpa [Kakeya.Streamlined.axisBox] using hbox.2.2
    exact hcoordinate.trans (by norm_num)
  rcases
      pureWZ2_grid_aligned_box_pigeonhole
        source hsourceWindow hdelta K hKPos hKEven hKdeltaOne
    with ⟨center, hcenterGrid, hcenterWindow, hboxMass⟩
  let halfWidth : Point3 :=
    point3 (((K : ℝ) * delta) / 2)
      (((K : ℝ) * delta) / 2)
      (((K : ℝ) * delta) / 2)
  let sourceBox : Set Point3 :=
    pureWZ2SourceBox center halfWidth
  let core : Set Point3 :=
    pureWZ2ShiftedOriginGridCore delta scale center
  have hsourceBoxCore : sourceBox ⊆ core := by
    intro point hpoint
    change
      wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆
        {other | ∀ coordinate : Fin 3,
          |other coordinate - center coordinate| ≤
            1 / (9 * scale) - 6 * delta}
    intro other hother coordinate
    have hsameCell :
        wz1PaperGridIndex delta other =
          wz1PaperGridIndex delta point :=
      (mem_wz1PaperGridCube delta
        (wz1PaperGridIndex delta point) other).mp hother
    have hcoordinateDistance :
        |other coordinate - point coordinate| ≤ delta := by
      have hpointMem :
          point ∈ wz1PaperGridCube delta
            (wz1PaperGridIndex delta point) :=
        (mem_wz1PaperGridCube delta _ point).mpr rfl
      rw [wz1PaperGridCube_eq_Ico hdelta] at hother hpointMem
      fin_cases coordinate
      · change |other 0 - point 0| ≤ delta
        rw [abs_le]
        constructor <;>
          linarith [hother.1, hother.2.1,
            hpointMem.1, hpointMem.2.1]
      · change |other 1 - point 1| ≤ delta
        rw [abs_le]
        constructor <;>
          linarith [hother.2.2.1, hother.2.2.2.1,
            hpointMem.2.2.1, hpointMem.2.2.2.1]
      · change |other 2 - point 2| ≤ delta
        rw [abs_le]
        constructor <;>
          linarith [hother.2.2.2.2.1, hother.2.2.2.2.2,
            hpointMem.2.2.2.2.1, hpointMem.2.2.2.2.2]
    have hpointCenter :
        |point coordinate - center coordinate| ≤
          ((K : ℝ) * delta) / 2 := by
      have haxis := hpoint.1 coordinate
      have hhalf :
          halfWidth coordinate = ((K : ℝ) * delta) / 2 := by
        fin_cases coordinate <;> simp [halfWidth, point3]
      simpa [hhalf] using haxis
    have htriangle :
        |other coordinate - center coordinate| ≤
          |other coordinate - point coordinate| +
            |point coordinate - center coordinate| := by
      calc
        |other coordinate - center coordinate| =
            |(other coordinate - point coordinate) +
              (point coordinate - center coordinate)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    have hhalfUpper :
        ((K : ℝ) * delta) / 2 ≤ 1 / (10 * scale) := by
      calc
        ((K : ℝ) * delta) / 2 ≤
            (1 / (5 * scale)) / 2 := by gcongr
        _ = 1 / (10 * scale) := by ring
    have hdeltaMargin :
        delta + 1 / (10 * scale) ≤
          1 / (9 * scale) - 6 * delta := by
      have hscaled : scale * delta ≤ 1 / 1000 := hsmall
      have hscaleInvPos : 0 < 1 / scale := by positivity
      have hscaledDelta :
          delta ≤ (1 / 1000) * (1 / scale) := by
        have heq : delta = (scale * delta) * (1 / scale) := by
          field_simp [hscalePos.ne']
        rw [heq]
        gcongr
      calc
        delta + 1 / (10 * scale) ≤
            1 / (1000 * scale) + 1 / (10 * scale) := by
          have hdeltaUpper : delta ≤ 1 / (1000 * scale) := by
            rw [show (1 / (1000 * scale) : ℝ) =
              (1 / 1000) * (1 / scale) by ring]
            exact hscaledDelta
          gcongr
        _ ≤ 1 / (9 * scale) - 6 * delta := by
          rw [show (1 / (1000 * scale) + 1 / (10 * scale) : ℝ) =
              (101 / 1000) * (1 / scale) by field_simp [hscalePos.ne']; ring]
          rw [show (1 / (9 * scale) : ℝ) =
              (1 / 9) * (1 / scale) by ring]
          have hcoeff : (107 / 1000 : ℝ) ≤ 1 / 9 := by norm_num
          have hcoeffScaled :
              (107 / 1000 : ℝ) * (1 / scale) ≤
                (1 / 9) * (1 / scale) :=
            mul_le_mul_of_nonneg_right hcoeff hscaleInvPos.le
          nlinarith [hcoeffScaled, hscaledDelta]
    exact htriangle.trans <|
      calc
        |other coordinate - point coordinate| +
            |point coordinate - center coordinate| ≤
          delta + ((K : ℝ) * delta) / 2 := by gcongr
        _ ≤ delta + 1 / (10 * scale) := by gcongr
        _ ≤ 1 / (9 * scale) - 6 * delta := hdeltaMargin
  have hcoefficient :
      (1 / 2000000 : ℝ) / scale ^ 3 ≤
        ((K : ℝ) * delta) ^ 3 / 8000 := by
    have hKdeltaLower :
        (99 / 500 : ℝ) / scale ≤ (K : ℝ) * delta := by
      have hnLower' :
          1 / (10 * scale * delta) - 1 ≤ (n : ℝ) :=
        hnLower.le
      have hraw :
          1 / (5 * scale) - 2 * delta ≤
            (K : ℝ) * delta := by
        dsimp only [K]
        push_cast
        calc
          1 / (5 * scale) - 2 * delta =
              2 * (1 / (10 * scale * delta) - 1) * delta := by
            field_simp [hscalePos.ne', hdelta.ne'] <;> ring
          _ ≤ 2 * n * delta := by gcongr
      have hdeltaUpper : delta ≤ 1 / (1000 * scale) := by
        have heq : delta = (scale * delta) * (1 / scale) := by
          field_simp [hscalePos.ne']
        rw [heq, show (1 / (1000 * scale) : ℝ) =
          (1 / 1000) * (1 / scale) by ring]
        gcongr
      calc
        (99 / 500 : ℝ) / scale =
            1 / (5 * scale) - 2 / (1000 * scale) := by
          field_simp [hscalePos.ne']
          ring
        _ ≤ 1 / (5 * scale) - 2 * delta := by
          have htwo : 2 * delta ≤ 2 * (1 / (1000 * scale)) := by
            gcongr
          simpa [div_eq_mul_inv, mul_assoc] using
            (sub_le_sub_left htwo (1 / (5 * scale)))
        _ ≤ (K : ℝ) * delta := hraw
    have hpositive : 0 ≤ (99 / 500 : ℝ) / scale := by positivity
    have hcubed :
        ((99 / 500 : ℝ) / scale) ^ 3 ≤
          ((K : ℝ) * delta) ^ 3 := by gcongr
    have hnumeric :
        (1 / 2000000 : ℝ) ≤ ((99 / 500 : ℝ) ^ 3) / 8000 := by
      norm_num
    calc
      (1 / 2000000 : ℝ) / scale ^ 3 ≤
          (((99 / 500 : ℝ) ^ 3) / 8000) / scale ^ 3 := by
        exact div_le_div_of_nonneg_right hnumeric (by positivity)
      _ = (((99 / 500 : ℝ) / scale) ^ 3) / 8000 := by ring
      _ ≤ ((K : ℝ) * delta) ^ 3 / 8000 := by gcongr
  have hcoefficientENN :
      ENNReal.ofReal ((1 / 2000000 : ℝ) / scale ^ 3) ≤
        ENNReal.ofReal (((K : ℝ) * delta) ^ 3 / 8000) :=
    ENNReal.ofReal_mono hcoefficient
  have hcoreMass :
      ENNReal.ofReal ((1 / 2000000 : ℝ) / scale ^ 3) *
          source.mass ≤
        ∑ index, volume (source.carrier index ∩ core) := by
    calc
      ENNReal.ofReal ((1 / 2000000 : ℝ) / scale ^ 3) *
            source.mass ≤
          ENNReal.ofReal (((K : ℝ) * delta) ^ 3 / 8000) *
            source.mass := by gcongr
      _ ≤ ∑ index, volume (source.carrier index ∩ sourceBox) := by
        simpa [sourceBox, halfWidth] using hboxMass
      _ ≤ ∑ index, volume (source.carrier index ∩ core) := by
        apply Finset.sum_le_sum
        intro index _
        exact measure_mono
          (Set.inter_subset_inter_right _ hsourceBoxCore)
  have hcoreMeasurable : MeasurableSet core :=
    measurableSet_pureWZ2ShiftedOriginGridCore delta scale center
  let selected : WZ1PaperTubeShading family :=
    paperRestrictShadingToSet source core hcoreMeasurable
  have hselectedSub : PaperIsSubshading selected source :=
    fun _ _ hpoint => hpoint.1
  have hselectedCubical : WZ1PaperIsCubicalShading selected :=
    paperRestrictShadingToSet_cubical hcoreMeasurable hcubical
      (pureWZ2ShiftedOriginGridCore_whole_cell delta scale center)
  refine
    ⟨center, selected, hcenterGrid, hcenterWindow, hselectedSub,
      hselectedCubical, ?_, ?_⟩
  · change
      ENNReal.ofReal ((1 / 2000000 : ℝ) / scale ^ 3) *
          source.mass ≤
        ∑ index, volume (source.carrier index ∩ core)
    exact hcoreMass
  · intro index
    rfl

end Kakeya.Assouad.PureWZ2

end
