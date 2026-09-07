import MyLeanRepo.Kakeya.Assouad.WZ1.IsotropicTubeRediscretization
import MyLeanRepo.Kakeya.Assouad.WZ1.MildRescalingNormalizedGrainsStatements
import MyLeanRepo.Kakeya.Assouad.TranslationInfrastructure
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.CapsuleBounds

/-!
# Closed geometric helpers for Proposition 6.3 mild rescaling

These lemmas isolate the grid and carrier geometry used by the final
one-tube-per-source retubing.  In particular, this module does not import the
older mild-rescaling assembly, whose transitive closure still contains an
unrelated open local-AD target.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open Set

attribute [local instance] Classical.propDecidable

/-- The grid-aligned core of the mild-rescaling window around `center`.
A point belongs to the core exactly when its complete source grid cell stays
inside the coordinate window used by the isotropic rescaling. -/
def pureWZ2ShiftedOriginGridCore
    (delta scale : ℝ) (center : Point3) : Set Point3 :=
  let width : ℝ := 1 / (9 * scale) - 6 * delta
  {point |
    wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆
      {other | ∀ coordinate, |other coordinate - center coordinate| ≤ width}}

/-- Every coordinate of a point in `Point3` is bounded by its Euclidean norm. -/
lemma proposition63_point3_coord_abs_le_norm
    (point : Point3) (coordinate : Fin 3) :
    |point coordinate| ≤ ‖point‖ := by
  have hnorm :
      ‖point‖ ^ 2 = point 0 ^ 2 + point 1 ^ 2 + point 2 ^ 2 := by
    simp [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_succ]
    ring
  have hsquare : point coordinate ^ 2 ≤ ‖point‖ ^ 2 := by
    rw [hnorm]
    fin_cases coordinate <;> simp [add_assoc] <;> nlinarith
  have hnorm_nonneg : 0 ≤ ‖point‖ := norm_nonneg point
  calc
    |point coordinate| = Real.sqrt (point coordinate ^ 2) := by
      rw [Real.sqrt_sq_eq_abs]
    _ ≤ Real.sqrt (‖point‖ ^ 2) := Real.sqrt_le_sqrt hsquare
    _ = ‖point‖ := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hnorm_nonneg]

/-- If a unit-direction tube has a sufficiently vertical direction, then a
bounded point on its axis controls the height-zero point of that axis. -/
lemma zero_point_bound_from_axis_point
    {delta : ℝ} {tube : Kakeya.DeltaTube delta}
    (hdir : (1 / 2 : ℝ) ≤ |tube.direction (2 : Fin 3)|)
    (point : Point3) (hpointAxis : point ∈ tubeAxisLine tube)
    (bound : ℝ) (hboundNonneg : 0 ≤ bound)
    (hpointBound : ∀ coordinate : Fin 3, |point coordinate| ≤ bound) :
    ∀ coordinate : Fin 3,
      |wz1TubeAxisZeroPoint tube coordinate| ≤ 3 * bound := by
  have hpointParameter :
      ∃ parameter : ℝ, point = tube.base + parameter • tube.direction := by
    simpa [tubeAxisLine, Set.mem_setOf_eq] using hpointAxis
  rcases hpointParameter with ⟨parameter, hparameter⟩
  let zeroPoint := wz1TubeAxisZeroPoint tube
  set direction : Point3 := tube.direction with hdirection
  have hdirectionTwo : direction (2 : Fin 3) ≠ 0 := by
    by_contra hzero
    rw [hzero] at hdir
    norm_num at hdir
  have hpointTwo :
      point (2 : Fin 3) =
        tube.base (2 : Fin 3) + parameter * direction (2 : Fin 3) := by
    rw [hparameter]
    simp
  have hpointCoordinate : ∀ coordinate : Fin 3,
      point coordinate = tube.base coordinate + parameter * direction coordinate := by
    intro coordinate
    rw [hparameter]
    simp
  have hzeroPoint : ∀ coordinate : Fin 3,
      zeroPoint coordinate =
        point coordinate -
          (point (2 : Fin 3) / direction (2 : Fin 3)) *
            direction coordinate := by
    intro coordinate
    have hdefinition :
        zeroPoint coordinate =
          tube.base coordinate -
            (tube.base (2 : Fin 3) / direction (2 : Fin 3)) *
              direction coordinate := by
      simp [zeroPoint, wz1TubeAxisZeroPoint]
      ring
    rw [hdefinition, hpointCoordinate coordinate, hpointTwo]
    field_simp [hdirectionTwo]
    ring
  intro coordinate
  have htriangle :
      |zeroPoint coordinate| ≤
        |point coordinate| +
          |point (2 : Fin 3) / direction (2 : Fin 3)| *
            |direction coordinate| := by
    rw [hzeroPoint coordinate]
    have h := abs_sub (point coordinate)
      ((point (2 : Fin 3) / direction (2 : Fin 3)) *
        direction coordinate)
    simpa [abs_mul] using h
  have hdirectionBound : |direction coordinate| ≤ 1 := by
    have hunit : ‖direction‖ = 1 := tube.direction_unit
    have hcoordinate :=
      proposition63_point3_coord_abs_le_norm direction coordinate
    rw [hunit] at hcoordinate
    exact hcoordinate
  have hquotient :
      |point (2 : Fin 3) / direction (2 : Fin 3)| ≤ 2 * bound := by
    calc
      |point (2 : Fin 3) / direction (2 : Fin 3)| =
          |point (2 : Fin 3)| / |direction (2 : Fin 3)| := by
        rw [abs_div]
      _ ≤ bound / |direction (2 : Fin 3)| := by
        gcongr
        exact hpointBound 2
      _ ≤ bound / (1 / 2 : ℝ) := by gcongr
      _ = 2 * bound := by ring
  calc
    |zeroPoint coordinate| ≤
        |point coordinate| +
          |point (2 : Fin 3) / direction (2 : Fin 3)| *
            |direction coordinate| := htriangle
    _ ≤ bound + (2 * bound) * 1 := by
      apply add_le_add (hpointBound coordinate)
      calc
        |point (2 : Fin 3) / direction (2 : Fin 3)| *
              |direction coordinate| ≤
            (2 * bound) * |direction coordinate| :=
          mul_le_mul_of_nonneg_right hquotient (abs_nonneg _)
        _ ≤ (2 * bound) * 1 :=
          mul_le_mul_of_nonneg_left hdirectionBound (by linarith)
    _ = 3 * bound := by ring

/-- A similarity about a grid-aligned center preserves equality of fine grid
indices. -/
lemma proposition63_rescaling_same_grid_cell_iff
    {delta scale : ℝ} (hdelta : 0 < delta) (hscale : 0 < scale)
    (center : Point3)
    (hcenterGrid : ∀ coordinate : Fin 3,
      ∃ index : ℤ, center coordinate = (index : ℝ) * delta)
    (first second : Point3) :
    wz1PaperGridIndex (scale * delta)
        (wz1IsotropicRescalingMap center scale first) =
      wz1PaperGridIndex (scale * delta)
        (wz1IsotropicRescalingMap center scale second) ↔
    wz1PaperGridIndex delta first = wz1PaperGridIndex delta second := by
  rcases hcenterGrid 0 with ⟨n0, hn0⟩
  rcases hcenterGrid 1 with ⟨n1, hn1⟩
  rcases hcenterGrid 2 with ⟨n2, hn2⟩
  have hcoordinate : ∀ (point : Point3) (coordinate : Fin 3) (n : ℤ),
      center coordinate = (n : ℝ) * delta →
      ⌊(wz1IsotropicRescalingMap center scale point) coordinate /
          (scale * delta)⌋ = ⌊point coordinate / delta⌋ - n := by
    intro point coordinate n hn
    have hratio :
        (wz1IsotropicRescalingMap center scale point) coordinate /
            (scale * delta) = point coordinate / delta - (n : ℝ) := by
      change (scale * (point coordinate - center coordinate)) /
          (scale * delta) = point coordinate / delta - (n : ℝ)
      rw [hn]
      field_simp [hscale.ne', hdelta.ne']
    rw [hratio, Int.floor_sub_intCast]
  simp only [wz1PaperGridIndex, gridIndex]
  rw [hcoordinate first 0 n0 hn0, hcoordinate first 1 n1 hn1,
    hcoordinate first 2 n2 hn2, hcoordinate second 0 n0 hn0,
    hcoordinate second 1 n1 hn1, hcoordinate second 2 n2 hn2]
  constructor
  · intro h
    rcases Prod.mk.inj h with ⟨h0, h12⟩
    rcases Prod.mk.inj h12 with ⟨h1, h2⟩
    have h0' : ⌊first 0 / delta⌋ = ⌊second 0 / delta⌋ := by omega
    have h1' : ⌊first 1 / delta⌋ = ⌊second 1 / delta⌋ := by omega
    have h2' : ⌊first 2 / delta⌋ = ⌊second 2 / delta⌋ := by omega
    exact Prod.ext h0' (Prod.ext h1' h2')
  · intro h
    rcases Prod.mk.inj h with ⟨h0, h12⟩
    rcases Prod.mk.inj h12 with ⟨h1, h2⟩
    exact Prod.ext (congrArg (fun value => value - n0) h0)
      (Prod.ext (congrArg (fun value => value - n1) h1)
        (congrArg (fun value => value - n2) h2))

/-- A grid-aligned similarity carries a cubical set to a cubical set at the
enlarged scale. -/
lemma proposition63_cubical_set_rescaling
    {delta scale : ℝ} (hdelta : 0 < delta) (hscale : 0 < scale)
    (center : Point3)
    (hcenterGrid : ∀ coordinate : Fin 3,
      ∃ index : ℤ, center coordinate = (index : ℝ) * delta)
    (set : Set Point3)
    (hcubical : ∀ point ∈ set,
      wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆ set) :
    ∀ target ∈ wz1IsotropicRescalingMap center scale '' set,
      wz1PaperGridCube (scale * delta)
          (wz1PaperGridIndex (scale * delta) target) ⊆
        wz1IsotropicRescalingMap center scale '' set := by
  intro target htarget other hother
  rcases htarget with ⟨source, hsource, rfl⟩
  let sourceOther := wz1IsotropicRescalingInverse center scale other
  have hmapInverse :
      wz1IsotropicRescalingMap center scale sourceOther = other := by
    ext coordinate
    simp [sourceOther, wz1IsotropicRescalingMap,
      wz1IsotropicRescalingInverse]
    field_simp [hscale.ne']
  have htargetGrid :
      wz1PaperGridIndex (scale * delta) other =
        wz1PaperGridIndex (scale * delta)
          (wz1IsotropicRescalingMap center scale source) :=
    (mem_wz1PaperGridCube (scale * delta) _ other).mp hother
  have hsourceGrid :
      wz1PaperGridIndex delta sourceOther =
        wz1PaperGridIndex delta source := by
    apply (proposition63_rescaling_same_grid_cell_iff hdelta hscale center
      hcenterGrid sourceOther source).mp
    rwa [hmapInverse]
  have hsourceOther : sourceOther ∈ set :=
    hcubical source hsource <|
      (mem_wz1PaperGridCube delta _ sourceOther).mpr hsourceGrid
  exact ⟨sourceOther, hsourceOther, hmapInverse⟩

/-- The intersection of two cubical sets is cubical. -/
lemma proposition63_cubical_set_intersection
    {delta : ℝ} (first second : Set Point3)
    (hfirst : ∀ point ∈ first,
      wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆ first)
    (hsecond : ∀ point ∈ second,
      wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆ second) :
    ∀ point ∈ first ∩ second,
      wz1PaperGridCube delta (wz1PaperGridIndex delta point) ⊆
        first ∩ second := by
  intro point hpoint other hother
  exact ⟨hfirst point hpoint.1 hother, hsecond point hpoint.2 hother⟩

/-- A bounded source paper-carrier point is carried by a target tube whose
axis is the centered isotropic image of the source axis. -/
lemma proposition63_rescaled_point_in_paper_carrier
    {delta scale : ℝ} (hdelta : 0 < delta) (hscale : 0 < scale)
    (hscaleDeltaSmall : scale * delta < 1 / 54)
    (center : Point3)
    (width : ℝ) (hwidth : width = 1 / (9 * scale) - 6 * delta)
    {sourceTube : Kakeya.DeltaTube delta} {point : Point3}
    (hpoint : point ∈ wz1PaperTubeCarrier sourceTube)
    (hbox : ∀ coordinate, |point coordinate - center coordinate| ≤ width)
    {targetTube : Kakeya.DeltaTube (scale * delta)}
    (haxis : tubeAxisLine targetTube =
      wz1IsotropicRescalingMap center scale '' tubeAxisLine sourceTube) :
    wz1IsotropicRescalingMap center scale point ∈
      wz1PaperTubeCarrier targetTube := by
  let translate : Point3 → Point3 := fun source => source - center
  let translatedAxis : Set Point3 := translate '' tubeAxisLine sourceTube
  have htranslated : point - center ∈
      Metric.cthickening (6 * delta) translatedAxis := by
    have himage :
        Metric.cthickening (6 * delta) translatedAxis =
          translate '' Metric.cthickening (6 * delta)
            (tubeAxisLine sourceTube) := by
      simpa [translate, translatedAxis, sub_eq_add_neg] using
        TranslationInfrastructure.translate_cthickening
          (-center) (tubeAxisLine sourceTube)
    rw [himage]
    exact ⟨point, hpoint.1, by simp [translate]⟩
  have hscaled : scale • (point - center) ∈
      Metric.cthickening (6 * (scale * delta))
        ((fun source : Point3 => scale • source) '' translatedAxis) := by
    have hsimilarity :=
      Streamlined.GeometricLemmas.cthickening_smul_point3
        (L := scale) hscale
        (r := 6 * (scale * delta)) (s := translatedAxis)
    have hradius : 6 * (scale * delta) / scale = 6 * delta := by
      field_simp [hscale.ne']
    rw [hsimilarity, hradius]
    exact ⟨point - center, htranslated, rfl⟩
  have haxisImage :
      (fun source : Point3 => scale • source) '' translatedAxis =
        tubeAxisLine targetTube := by
    rw [haxis]
    ext target
    simp only [translatedAxis, translate, Set.mem_image]
    constructor
    · rintro ⟨translatedPoint, ⟨source, hsource, rfl⟩, rfl⟩
      exact ⟨source, hsource, by simp [wz1IsotropicRescalingMap]⟩
    · rintro ⟨source, hsource, rfl⟩
      exact ⟨source - center, ⟨source, hsource, rfl⟩, by
        simp [wz1IsotropicRescalingMap]⟩
  have hthickening : wz1IsotropicRescalingMap center scale point ∈
      Metric.cthickening (6 * (scale * delta))
        (tubeAxisLine targetTube) := by
    rw [← haxisImage]
    simpa [wz1IsotropicRescalingMap] using hscaled
  have htargetBox : wz1IsotropicRescalingMap center scale point ∈
      Kakeya.Streamlined.axisBox 2 2 2 := by
    have hcoordinate : ∀ coordinate : Fin 3,
        |(wz1IsotropicRescalingMap center scale point) coordinate| ≤ 1 := by
      intro coordinate
      have hvalue :
          (wz1IsotropicRescalingMap center scale point) coordinate =
            scale * (point coordinate - center coordinate) := by
        simp [wz1IsotropicRescalingMap]
      rw [hvalue, abs_mul, abs_of_pos hscale]
      calc
        scale * |point coordinate - center coordinate| ≤ scale * width := by
          exact mul_le_mul_of_nonneg_left (hbox coordinate) hscale.le
        _ = 1 / 9 - 6 * scale * delta := by
          rw [hwidth]
          field_simp [hscale.ne']
        _ ≤ 1 := by linarith [mul_pos hscale hdelta]
    simpa [Kakeya.Streamlined.axisBox] using
      And.intro (hcoordinate 0)
        (And.intro (hcoordinate 1) (hcoordinate 2))
  exact ⟨hthickening, htargetBox⟩

end Kakeya.Assouad.PureWZ2

end
