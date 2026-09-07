import MyLeanRepo.Kakeya.Assouad.PureWZ2.IntervalSlopeRescaling
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.ConfigurationRestriction
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.OffsetShearNormal
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.PopularBoxLocalGrains
import MyLeanRepo.Kakeya.Assouad.WZ1.AnchoredRescalingGeometry
import Mathlib.Tactic

/-!
# Fixed source-side shear chart selection

This file isolates the source-side measurable pigeonhole needed before the
old half-offset assembly.  It does not use
`PureWZ2LocalGlobalCompatibility`, `normal_first`, or `normal_tilt`.

The final source-level theorem uses only one actual source point, the source
tube containing it, the line-class vertical bound, the exact local incidence
bound, the unit-normal certificate, and the smallness hypothesis
`delta ≤ 1 / 100`.  This gives a quantitative horizontal lower bound for the
actual source normal, hence forces one of the two fixed shears `a = ±1/2` to
have denominator at least `1 / 50`.  Splitting the source carrier by these
two measurable shear charts, one chart retains at least half of the shaded
mass.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- The two fixed shears used before any projectivization. -/
inductive PureWZ2FixedShearChoice where
  | plus
  | minus
  deriving DecidableEq

namespace PureWZ2FixedShearChoice

/-- The actual horizontal shear parameter. -/
def shear : PureWZ2FixedShearChoice → ℝ
  | plus => 1 / 2
  | minus => -1 / 2

theorem shear_abs_le (choice : PureWZ2FixedShearChoice) :
    |choice.shear| ≤ 1 / 2 := by
  cases choice <;> norm_num [shear]

end PureWZ2FixedShearChoice

private lemma sourceShading_union_measurable
    {sigma inputLoss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma inputLoss delta}
    (source : PureWZ2HorizontalSourceData cfg) :
    MeasurableSet source.sourceShading.union := by
  let carrierUnion : Set Point3 :=
    ⋃ index : Fin cfg.family.card, source.sourceShading.carrier index
  have hEq : source.sourceShading.union = carrierUnion := by
    ext point
    constructor <;> intro h
    · rcases h with ⟨index, hindex⟩
      exact mem_iUnion.2 ⟨index, hindex⟩
    · rcases mem_iUnion.1 h with ⟨index, hindex⟩
      exact ⟨index, hindex⟩
  rw [hEq]
  exact MeasurableSet.iUnion fun index =>
    source.sourceShading.measurable_carrier index

/-- The fixed-shear chart coordinate on the actual source plane map. -/
def pureWZ2SourceShearCoordinate
    {sigma inputLoss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma inputLoss delta}
    (source : PureWZ2HorizontalSourceData cfg)
    (choice : PureWZ2FixedShearChoice)
    (point : {point : Point3 // point ∈ source.sourceShading.union}) : ℝ :=
  source.sourceLocalGrains.planeMap point 1 -
    choice.shear * source.sourceLocalGrains.planeMap point 0

theorem pureWZ2SourceShearCoordinate_eq
    {sigma inputLoss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma inputLoss delta}
    (source : PureWZ2HorizontalSourceData cfg)
    (choice : PureWZ2FixedShearChoice)
    (point : {point : Point3 // point ∈ source.sourceShading.union}) :
    pureWZ2SourceShearCoordinate source choice point =
      pureWZ2OffsetShearNormal choice.shear
        (source.sourceLocalGrains.planeMap point) 1 := by
  simp [pureWZ2SourceShearCoordinate, pureWZ2OffsetShearNormal_coord_one]

private lemma point3_inner_eq
    (first second : Point3) :
    inner ℝ first second =
      first 0 * second 0 + first 1 * second 1 + first 2 * second 2 := by
  rw [PiLp.inner_apply]
  simp [Fin.sum_univ_succ]
  ring

private lemma pureWZ2OffsetShearNormal_restrict_coord_one_eq
    {sigma inputLoss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma inputLoss delta}
    (source : PureWZ2HorizontalSourceData cfg)
    {target : WZ1PaperTubeShading cfg.family}
    (hsub : ∀ index, target.carrier index ⊆ source.sourceShading.carrier index)
    (choice : PureWZ2FixedShearChoice)
    (point : {point : Point3 // point ∈ target.union}) :
    pureWZ2OffsetShearNormal choice.shear
        ((source.sourceLocalGrains.restrict hsub).planeMap point) 1 =
      pureWZ2SourceShearCoordinate source choice
        ⟨point.1, paperSubshading_union_subset hsub point.property⟩ := by
  simp [pureWZ2SourceShearCoordinate, pureWZ2OffsetShearNormal_coord_one,
    PureWZ2LocalGrainData.restrict_planeMap]

private lemma pureWZ2SourceShearCoordinate_measurable
    {sigma inputLoss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma inputLoss delta}
    (source : PureWZ2HorizontalSourceData cfg)
    (choice : PureWZ2FixedShearChoice) :
    Measurable (pureWZ2SourceShearCoordinate source choice) := by
  have hplane : Measurable source.sourceLocalGrains.planeMap :=
    source.sourceLocalGrains.planeMap_lipschitz.continuous.measurable
  have hcoord0 : Measurable fun point : {point : Point3 // point ∈ source.sourceShading.union} =>
      source.sourceLocalGrains.planeMap point 0 :=
    (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 0).measurable.comp hplane
  have hcoord1 : Measurable fun point : {point : Point3 // point ∈ source.sourceShading.union} =>
      source.sourceLocalGrains.planeMap point 1 :=
    (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) 1).measurable.comp hplane
  exact hcoord1.sub (measurable_const.mul hcoord0)

/-- The source points where one fixed shear already has a uniform
denominator lower bound. -/
def pureWZ2SourceShearSet
    {sigma inputLoss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma inputLoss delta}
    (source : PureWZ2HorizontalSourceData cfg)
    (choice : PureWZ2FixedShearChoice) : Set Point3 :=
  {point | ∃ hpoint : point ∈ source.sourceShading.union,
      (1 / 50 : ℝ) ≤ |pureWZ2SourceShearCoordinate source choice
        ⟨point, hpoint⟩|}

private lemma pureWZ2SourceShearSet_measurable
    {sigma inputLoss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma inputLoss delta}
    (source : PureWZ2HorizontalSourceData cfg)
    (choice : PureWZ2FixedShearChoice) :
    MeasurableSet (pureWZ2SourceShearSet source choice) := by
  let subtypeSet : Set {point : Point3 // point ∈ source.sourceShading.union} :=
    {point |
      (1 / 50 : ℝ) ≤
        |pureWZ2SourceShearCoordinate source choice point|}
  have hsubMeas : MeasurableSet subtypeSet := by
    have hcoord :
        Measurable fun point : {point : Point3 // point ∈ source.sourceShading.union} =>
          |pureWZ2SourceShearCoordinate source choice point| :=
      continuous_abs.measurable.comp
        (pureWZ2SourceShearCoordinate_measurable source choice)
    exact hcoord measurableSet_Ici
  have hEq :
      pureWZ2SourceShearSet source choice =
        ((fun point : {point : Point3 // point ∈ source.sourceShading.union} =>
            (point : Point3)) '' subtypeSet) := by
    ext point
    constructor
    · rintro ⟨hpoint, hdenom⟩
      exact ⟨⟨point, hpoint⟩, hdenom, rfl⟩
    · rintro ⟨point, hpoint, rfl⟩
      exact ⟨point.property, hpoint⟩
  rw [hEq]
  exact (MeasurableEmbedding.subtype_coe
    (sourceShading_union_measurable source)).measurableSet_image.mpr hsubMeas

theorem mem_pureWZ2SourceShearSet_iff
    {sigma inputLoss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma inputLoss delta}
    (source : PureWZ2HorizontalSourceData cfg)
    (choice : PureWZ2FixedShearChoice)
    {point : Point3}
    (hpoint : point ∈ source.sourceShading.union) :
    point ∈ pureWZ2SourceShearSet source choice ↔
      (1 / 50 : ℝ) ≤
        |pureWZ2SourceShearCoordinate source choice
          ⟨point, hpoint⟩| := by
  constructor
  · rintro ⟨hpoint', hdenom⟩
    simpa using hdenom
  · intro hdenom
    exact ⟨hpoint, hdenom⟩

/-- A unit normal with small vertical coordinate belongs to at least one of
the two fixed shear charts. -/
theorem pureWZ2_fixedShear_mem
    {normal : Point3}
    (hunit : ‖normal‖ = 1)
    (hvertical : |normal 2| ≤ 1 / 2) :
    (1 / 4 : ℝ) ≤
        |pureWZ2OffsetShearNormal (1 / 2) normal 1| ∨
      (1 / 4 : ℝ) ≤
        |pureWZ2OffsetShearNormal (-1 / 2) normal 1| := by
  by_contra h
  push Not at h
  have hplus : |pureWZ2OffsetShearNormal (1 / 2) normal 1| < 1 / 4 := h.1
  have hminus : |pureWZ2OffsetShearNormal (-1 / 2) normal 1| < 1 / 4 := h.2
  have hyTwice :
      |2 * normal 1| < 1 / 2 := by
    have hsum :
        |pureWZ2OffsetShearNormal (1 / 2) normal 1 +
            pureWZ2OffsetShearNormal (-1 / 2) normal 1| <
          1 / 2 := by
      calc
        |pureWZ2OffsetShearNormal (1 / 2) normal 1 +
            pureWZ2OffsetShearNormal (-1 / 2) normal 1| ≤
            |pureWZ2OffsetShearNormal (1 / 2) normal 1| +
              |pureWZ2OffsetShearNormal (-1 / 2) normal 1| := abs_add_le _ _
        _ < 1 / 4 + 1 / 4 := add_lt_add hplus hminus
        _ = 1 / 2 := by norm_num
    have hsumEq :
        pureWZ2OffsetShearNormal (1 / 2) normal 1 +
            pureWZ2OffsetShearNormal (-1 / 2) normal 1 =
          2 * normal 1 := by
      rw [pureWZ2OffsetShearNormal_coord_one, pureWZ2OffsetShearNormal_coord_one]
      ring
    rw [hsumEq] at hsum
    exact hsum
  have hy : |normal 1| < 1 / 4 := by
    have habs : 2 * |normal 1| < 1 / 2 := by
      simpa [abs_mul] using hyTwice
    nlinarith
  have hx :
      |normal 0| < 1 / 2 := by
    have hdiff :
        |normal 0| <
          1 / 2 := by
      have htriangle :
          |pureWZ2OffsetShearNormal (-1 / 2) normal 1 +
              -(pureWZ2OffsetShearNormal (1 / 2) normal 1)| <
            1 / 2 := by
        calc
          |pureWZ2OffsetShearNormal (-1 / 2) normal 1 +
              -(pureWZ2OffsetShearNormal (1 / 2) normal 1)| ≤
              |pureWZ2OffsetShearNormal (-1 / 2) normal 1| +
                |-(pureWZ2OffsetShearNormal (1 / 2) normal 1)| := abs_add_le _ _
          _ = |pureWZ2OffsetShearNormal (-1 / 2) normal 1| +
                |pureWZ2OffsetShearNormal (1 / 2) normal 1| := by rw [abs_neg]
          _ < 1 / 4 + 1 / 4 := add_lt_add hminus hplus
          _ = 1 / 2 := by norm_num
      have hdiffEq :
          pureWZ2OffsetShearNormal (-1 / 2) normal 1 +
              -(pureWZ2OffsetShearNormal (1 / 2) normal 1) =
            normal 0 := by
        rw [pureWZ2OffsetShearNormal_coord_one, pureWZ2OffsetShearNormal_coord_one]
        ring
      rw [hdiffEq] at htriangle
      exact htriangle
    exact hdiff
  have hnormSq :
      normal 0 ^ 2 + normal 1 ^ 2 + normal 2 ^ 2 = 1 := by
    have hsq := point3_coord_norm_sq normal
    simpa [hunit] using hsq.symm
  have hzSq : normal 2 ^ 2 ≤ 1 / 4 := by
    nlinarith [abs_le.mp hvertical]
  have hxSq : normal 0 ^ 2 < 1 / 4 := by
    nlinarith [abs_lt.mp hx]
  have hySq : normal 1 ^ 2 < 1 / 16 := by
    nlinarith [abs_lt.mp hy]
  nlinarith

theorem pureWZ2_fixedShear_coord_one_lower
    {normal : Point3}
    (hunit : ‖normal‖ = 1)
    (hvertical : |normal 2| ≤ 1 / 2) :
    (1 / 50 : ℝ) <
        |pureWZ2OffsetShearNormal (1 / 2) normal 1| ∨
      (1 / 50 : ℝ) <
        |pureWZ2OffsetShearNormal (-1 / 2) normal 1| := by
  rcases pureWZ2_fixedShear_mem hunit hvertical with hplus | hminus
  · left
    linarith
  · right
    linarith

/-- If the horizontal part of a normal has squared norm at least `1 / 500`,
then one of the two fixed shears has denominator at least `1 / 50`. -/
theorem pureWZ2_fixedShear_mem_of_horizontal_sq_lower
    {normal : Point3}
    (hhorizontal :
      (1 / 500 : ℝ) ≤ normal 0 ^ 2 + normal 1 ^ 2) :
    (1 / 50 : ℝ) ≤
        |pureWZ2OffsetShearNormal (1 / 2) normal 1| ∨
      (1 / 50 : ℝ) ≤
        |pureWZ2OffsetShearNormal (-1 / 2) normal 1| := by
  by_contra h
  push Not at h
  have hplus : |pureWZ2OffsetShearNormal (1 / 2) normal 1| < 1 / 50 := h.1
  have hminus : |pureWZ2OffsetShearNormal (-1 / 2) normal 1| < 1 / 50 := h.2
  have hyTwice :
      |2 * normal 1| < 1 / 25 := by
    have hsum :
        |pureWZ2OffsetShearNormal (1 / 2) normal 1 +
            pureWZ2OffsetShearNormal (-1 / 2) normal 1| <
          1 / 25 := by
      calc
        |pureWZ2OffsetShearNormal (1 / 2) normal 1 +
            pureWZ2OffsetShearNormal (-1 / 2) normal 1| ≤
            |pureWZ2OffsetShearNormal (1 / 2) normal 1| +
              |pureWZ2OffsetShearNormal (-1 / 2) normal 1| := abs_add_le _ _
        _ < 1 / 50 + 1 / 50 := add_lt_add hplus hminus
        _ = 1 / 25 := by norm_num
    have hsumEq :
        pureWZ2OffsetShearNormal (1 / 2) normal 1 +
            pureWZ2OffsetShearNormal (-1 / 2) normal 1 =
          2 * normal 1 := by
      rw [pureWZ2OffsetShearNormal_coord_one, pureWZ2OffsetShearNormal_coord_one]
      ring
    rw [hsumEq] at hsum
    exact hsum
  have hy : |normal 1| < 1 / 50 := by
    have habs : 2 * |normal 1| < 1 / 25 := by
      simpa [abs_mul] using hyTwice
    nlinarith
  have hx :
      |normal 0| < 1 / 25 := by
    have htriangle :
        |pureWZ2OffsetShearNormal (-1 / 2) normal 1 +
            -(pureWZ2OffsetShearNormal (1 / 2) normal 1)| <
          1 / 25 := by
      calc
        |pureWZ2OffsetShearNormal (-1 / 2) normal 1 +
            -(pureWZ2OffsetShearNormal (1 / 2) normal 1)| ≤
            |pureWZ2OffsetShearNormal (-1 / 2) normal 1| +
              |-(pureWZ2OffsetShearNormal (1 / 2) normal 1)| := abs_add_le _ _
        _ = |pureWZ2OffsetShearNormal (-1 / 2) normal 1| +
              |pureWZ2OffsetShearNormal (1 / 2) normal 1| := by rw [abs_neg]
        _ < 1 / 50 + 1 / 50 := add_lt_add hminus hplus
        _ = 1 / 25 := by norm_num
    have hdiffEq :
        pureWZ2OffsetShearNormal (-1 / 2) normal 1 +
            -(pureWZ2OffsetShearNormal (1 / 2) normal 1) =
          normal 0 := by
      rw [pureWZ2OffsetShearNormal_coord_one, pureWZ2OffsetShearNormal_coord_one]
      ring
    rw [hdiffEq] at htriangle
    exact htriangle
  have hhorizontalLt : normal 0 ^ 2 + normal 1 ^ 2 < 1 / 500 := by
    nlinarith [abs_lt.mp hx, abs_lt.mp hy]
  linarith

/-- The actual source normal at every retained source point has horizontal
squared norm at least `1 / 500`, using only the containing tube, line-class
verticality, exact incidence, unit normality, and `delta ≤ 1 / 100`. -/
theorem pureWZ2Source_horizontal_sq_lower
    {sigma inputLoss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma inputLoss delta}
    (source : PureWZ2HorizontalSourceData cfg)
    (hdeltaSmall : delta ≤ 1 / 100)
    (point : {point : Point3 // point ∈ source.sourceShading.union}) :
    (1 / 500 : ℝ) ≤
      source.sourceLocalGrains.planeMap point 0 ^ 2 +
        source.sourceLocalGrains.planeMap point 1 ^ 2 := by
  rcases point.property with ⟨index, hpoint⟩
  let direction := (cfg.family.tube index).direction
  let normal := source.sourceLocalGrains.planeMap point
  have hinc : |inner ℝ direction normal| ≤ delta :=
    source.sourceLocalGrains.planeMap_incidence index point.1 hpoint
  have hsmall : |inner ℝ direction normal| ≤ 1 / 100 :=
    hinc.trans hdeltaSmall
  have hdirection2 : (1 / 2 : ℝ) ≤ |direction 2| :=
    (cfg.line_class index).vertical
  have hdirection0 : |direction 0| ≤ 1 := by
    have h := PiLp.norm_apply_le direction (0 : Fin 3)
    simpa [direction, Real.norm_eq_abs, (cfg.family.tube index).direction_unit] using h
  have hdirection1 : |direction 1| ≤ 1 := by
    have h := PiLp.norm_apply_le direction (1 : Fin 3)
    simpa [direction, Real.norm_eq_abs, (cfg.family.tube index).direction_unit] using h
  have hunit : ‖normal‖ = 1 := source.sourceLocalGrains.planeMap_unit point
  have hnormSq :
      normal 0 ^ 2 + normal 1 ^ 2 + normal 2 ^ 2 = 1 := by
    have hsq := point3_coord_norm_sq normal
    simpa [normal, hunit] using hsq.symm
  by_contra hhorizontal
  have hhorizontalLt : normal 0 ^ 2 + normal 1 ^ 2 < 1 / 500 :=
    lt_of_not_ge hhorizontal
  have hnormal0 : |normal 0| < 1 / 20 := by
    nlinarith [sq_abs (normal 0), hhorizontalLt]
  have hnormal1 : |normal 1| < 1 / 20 := by
    nlinarith [sq_abs (normal 1), hhorizontalLt]
  have hnormal2 : (9 / 10 : ℝ) ≤ |normal 2| := by
    have hnormal2sq : (normal 2) ^ 2 > 81 / 100 := by
      nlinarith [hnormSq, hhorizontalLt]
    by_contra h
    have habsLt : |normal 2| < 9 / 10 := lt_of_not_ge h
    have hnormal2sqLt : (normal 2) ^ 2 < 81 / 100 := by
      nlinarith [sq_abs (normal 2), habsLt, abs_nonneg (normal 2)]
    linarith
  have hverticalTerm : (9 / 20 : ℝ) ≤ |direction 2 * normal 2| := by
    rw [abs_mul]
    nlinarith [hdirection2, hnormal2, abs_nonneg (direction 2), abs_nonneg (normal 2)]
  have hhorizontal0Term : |direction 0 * normal 0| ≤ 1 / 20 := by
    rw [abs_mul]
    have hnormal0le : |normal 0| ≤ (20 : ℝ)⁻¹ := by
      simpa using hnormal0.le
    nlinarith [hdirection0, hnormal0le, abs_nonneg (direction 0), abs_nonneg (normal 0)]
  have hhorizontal1Term : |direction 1 * normal 1| ≤ 1 / 20 := by
    rw [abs_mul]
    have hnormal1le : |normal 1| ≤ (20 : ℝ)⁻¹ := by
      simpa using hnormal1.le
    nlinarith [hdirection1, hnormal1le, abs_nonneg (direction 1), abs_nonneg (normal 1)]
  have hpair :
      |direction 0 * normal 0 + direction 1 * normal 1| ≤ 1 / 10 := by
    calc
      |direction 0 * normal 0 + direction 1 * normal 1| ≤
          |direction 0 * normal 0| + |direction 1 * normal 1| := abs_add_le _ _
      _ ≤ 1 / 20 + 1 / 20 := by gcongr
      _ = 1 / 10 := by norm_num
  have hsplit :
      direction 2 * normal 2 =
        inner ℝ direction normal +
          -(direction 0 * normal 0 + direction 1 * normal 1) := by
    rw [point3_inner_eq]
    ring
  have hreverse :
      |direction 2 * normal 2| ≤
        |inner ℝ direction normal| +
          |direction 0 * normal 0 + direction 1 * normal 1| := by
    calc
      |direction 2 * normal 2| =
          |inner ℝ direction normal +
              -(direction 0 * normal 0 + direction 1 * normal 1)| := by
        rw [hsplit]
      _ ≤ |inner ℝ direction normal| +
          |-(direction 0 * normal 0 + direction 1 * normal 1)| := abs_add_le _ _
      _ = |inner ℝ direction normal| +
          |direction 0 * normal 0 + direction 1 * normal 1| := by
        rw [abs_neg]
  have hlarge : (39 / 100 : ℝ) ≤ |inner ℝ direction normal| := by
    linarith
  linarith

/-- Restrict the source shading to one fixed-shear chart. -/
def pureWZ2SourceShearRestrictedShading
    {sigma inputLoss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma inputLoss delta}
    (source : PureWZ2HorizontalSourceData cfg)
    (choice : PureWZ2FixedShearChoice) :
    WZ1PaperTubeShading cfg.family :=
  pureWZ2PaperRestrictToSet source.sourceShading
    (pureWZ2SourceShearSet source choice)
    (pureWZ2SourceShearSet_measurable source choice)

theorem pureWZ2SourceShearRestrictedShading_subshading
    {sigma inputLoss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma inputLoss delta}
    (source : PureWZ2HorizontalSourceData cfg)
    (choice : PureWZ2FixedShearChoice) :
    ∀ index,
      (pureWZ2SourceShearRestrictedShading source choice).carrier index ⊆
        source.sourceShading.carrier index := by
  intro index
  exact Set.inter_subset_left

/-- One fixed source shear retains at least half the shading mass. -/
structure PureWZ2FixedShearSourceSelection
    {sigma inputLoss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma inputLoss delta}
    (source : PureWZ2HorizontalSourceData cfg) where
  shear_choice : PureWZ2FixedShearChoice
  shear : ℝ
  shear_eq : shear = shear_choice.shear
  selectedShading : WZ1PaperTubeShading cfg.family
  selected_subshading :
    ∀ index, selectedShading.carrier index ⊆ source.sourceShading.carrier index
  selected_union :
    selectedShading.union =
      source.sourceShading.union ∩
        pureWZ2SourceShearSet source shear_choice
  selectedLocalGrains :
    PureWZ2LocalGrainData selectedShading sigma
      (Kakeya.realRpowENN delta (-inputLoss))
  selectedGlobalGrains :
    PureWZ2C2GlobalGrainData selectedShading sigma
      (Kakeya.realRpowENN delta (-inputLoss))
  half_mass :
    (1 / 2 : ENNReal) * source.sourceShading.mass ≤ selectedShading.mass
  denominator_lower :
    ∀ point : {point : Point3 // point ∈ selectedShading.union},
      (1 / 50 : ℝ) ≤
        |pureWZ2OffsetShearNormal shear
          (selectedLocalGrains.planeMap point) 1|

/-- A point in the source union lies in at least one fixed-shear chart,
provided the actual source plane map has small vertical coordinate there. -/
theorem pureWZ2Source_mem_fixedShear_union_of_hvertical
    {sigma inputLoss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma inputLoss delta}
    (source : PureWZ2HorizontalSourceData cfg)
    (hvertical : ∀ point : {point : Point3 // point ∈ source.sourceShading.union},
      |source.sourceLocalGrains.planeMap point 2| ≤ 1 / 2)
    (point : {point : Point3 // point ∈ source.sourceShading.union}) :
    point.1 ∈ pureWZ2SourceShearSet source .plus ∪
      pureWZ2SourceShearSet source .minus := by
  rcases pureWZ2_fixedShear_mem
      (source.sourceLocalGrains.planeMap_unit point)
      (hvertical point) with hplus | hminus
  · left
    have hplus' :
        (1 / 50 : ℝ) ≤
          |pureWZ2OffsetShearNormal (1 / 2)
              (source.sourceLocalGrains.planeMap point) 1| := by
      linarith [show (1 / 50 : ℝ) ≤ (1 / 4 : ℝ) by norm_num, hplus]
    exact (mem_pureWZ2SourceShearSet_iff source .plus point.property).2
      (by
        simpa [PureWZ2FixedShearChoice.shear, pureWZ2SourceShearCoordinate_eq]
          using hplus')
  · right
    have hminus' :
        (1 / 50 : ℝ) ≤
          |pureWZ2OffsetShearNormal (-1 / 2)
              (source.sourceLocalGrains.planeMap point) 1| := by
      linarith [show (1 / 50 : ℝ) ≤ (1 / 4 : ℝ) by norm_num, hminus]
    exact (mem_pureWZ2SourceShearSet_iff source .minus point.property).2
      (by
        simpa [PureWZ2FixedShearChoice.shear, pureWZ2SourceShearCoordinate_eq]
          using hminus')

/-- Source-level two-chart cover derived directly from one actual source tube,
the line-class vertical bound, exact incidence, unit normality, and
`delta ≤ 1 / 100`. -/
theorem pureWZ2Source_mem_fixedShear_union
    {sigma inputLoss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma inputLoss delta}
    (source : PureWZ2HorizontalSourceData cfg)
    (hdeltaSmall : delta ≤ 1 / 100)
    (point : {point : Point3 // point ∈ source.sourceShading.union}) :
    point.1 ∈ pureWZ2SourceShearSet source .plus ∪
      pureWZ2SourceShearSet source .minus := by
  have hhorizontal :
      (1 / 500 : ℝ) ≤
        source.sourceLocalGrains.planeMap point 0 ^ 2 +
          source.sourceLocalGrains.planeMap point 1 ^ 2 :=
    pureWZ2Source_horizontal_sq_lower source hdeltaSmall point
  rcases pureWZ2_fixedShear_mem_of_horizontal_sq_lower hhorizontal with hplus | hminus
  · left
    have hplus' :
        (1 / 50 : ℝ) ≤
          |pureWZ2SourceShearCoordinate source .plus point| := by
      simpa [PureWZ2FixedShearChoice.shear, pureWZ2SourceShearCoordinate_eq] using hplus
    exact (mem_pureWZ2SourceShearSet_iff source .plus point.property).2
      hplus'
  · right
    have hminus' :
        (1 / 50 : ℝ) ≤
          |pureWZ2SourceShearCoordinate source .minus point| := by
      simpa [PureWZ2FixedShearChoice.shear, pureWZ2SourceShearCoordinate_eq] using hminus
    exact (mem_pureWZ2SourceShearSet_iff source .minus point.property).2
      hminus'

/-- Measurable fixed-shear pigeonhole on one actual source shading. -/
theorem pureWZ2_fixedShear_source_selection
    {sigma inputLoss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma inputLoss delta}
    (source : PureWZ2HorizontalSourceData cfg)
    (hdeltaSmall : delta ≤ 1 / 100) :
    Nonempty (PureWZ2FixedShearSourceSelection source) := by
  let plusSet := pureWZ2SourceShearSet source .plus
  let minusSet := pureWZ2SourceShearSet source .minus
  let plusShading := pureWZ2SourceShearRestrictedShading source .plus
  let minusShading := pureWZ2SourceShearRestrictedShading source .minus
  have hsubPlus : ∀ index, plusShading.carrier index ⊆ source.sourceShading.carrier index :=
    pureWZ2SourceShearRestrictedShading_subshading source .plus
  have hsubMinus : ∀ index, minusShading.carrier index ⊆ source.sourceShading.carrier index :=
    pureWZ2SourceShearRestrictedShading_subshading source .minus
  have hcover :
      ∀ index, source.sourceShading.carrier index ⊆ plusSet ∪ minusSet := by
    intro index point hpoint
    exact pureWZ2Source_mem_fixedShear_union source hdeltaSmall
      ⟨point, ⟨index, hpoint⟩⟩
  have hMass :
      plusShading.mass + minusShading.mass ≥ source.sourceShading.mass := by
    have h :
        ∀ index,
          MeasureTheory.volume (source.sourceShading.carrier index) ≤
            MeasureTheory.volume (source.sourceShading.carrier index ∩ plusSet) +
              MeasureTheory.volume (source.sourceShading.carrier index ∩ minusSet) := by
      intro index
      have hcov :
          source.sourceShading.carrier index ⊆
            (source.sourceShading.carrier index ∩ plusSet) ∪
              (source.sourceShading.carrier index ∩ minusSet) := by
        intro point hpoint
        rcases hcover index hpoint with hplus | hminus
        · exact Or.inl ⟨hpoint, hplus⟩
        · exact Or.inr ⟨hpoint, hminus⟩
      exact (MeasureTheory.measure_mono hcov).trans
        (MeasureTheory.measure_union_le _ _)
    calc
      source.sourceShading.mass =
          ∑ index : Fin cfg.family.card,
            MeasureTheory.volume (source.sourceShading.carrier index) := by
        rfl
      _ ≤ ∑ index : Fin cfg.family.card,
          (MeasureTheory.volume (source.sourceShading.carrier index ∩ plusSet) +
            MeasureTheory.volume (source.sourceShading.carrier index ∩ minusSet)) := by
        exact Finset.sum_le_sum fun index _ => h index
      _ = plusShading.mass + minusShading.mass := by
        rw [Finset.sum_add_distrib]
        rfl
  by_cases hplus :
      (1 / 2 : ENNReal) * source.sourceShading.mass ≤ plusShading.mass
  · let selectedLocal := source.sourceLocalGrains.restrict hsubPlus
    let selectedGlobal :=
      source.sourceGlobalGrains.restrict_same_constant hsubPlus
    have hselectedUnion :
        plusShading.union =
          source.sourceShading.union ∩ plusSet :=
      pureWZ2PaperRestrictToSet_union source.sourceShading plusSet
        (pureWZ2SourceShearSet_measurable source .plus)
    refine ⟨{
      shear_choice := .plus
      shear := 1 / 2
      shear_eq := by rfl
      selectedShading := plusShading
      selected_subshading := hsubPlus
      selected_union := hselectedUnion
      selectedLocalGrains := selectedLocal
      selectedGlobalGrains := selectedGlobal
      half_mass := hplus
      denominator_lower := ?_
    }⟩
    intro point
    have hmem : point.1 ∈ source.sourceShading.union ∩ plusSet := by
      simpa [hselectedUnion] using point.property
    have hdenom :
        (1 / 50 : ℝ) ≤
          |pureWZ2SourceShearCoordinate source .plus
            ⟨point.1, hmem.1⟩| := by
      exact (mem_pureWZ2SourceShearSet_iff source .plus hmem.1).mp hmem.2
    let sourcePoint : {point : Point3 // point ∈ source.sourceShading.union} :=
      ⟨point.1, paperSubshading_union_subset hsubPlus point.property⟩
    have hsourcePoint : sourcePoint = ⟨point.1, hmem.1⟩ := by
      apply Subtype.ext
      rfl
    have hdenom' :
        (1 / 50 : ℝ) ≤
          |pureWZ2SourceShearCoordinate source .plus sourcePoint| := by
      rw [hsourcePoint]
      exact hdenom
    have hrestricted :
        (1 / 50 : ℝ) ≤
          |pureWZ2OffsetShearNormal (1 / 2)
              ((source.sourceLocalGrains.restrict hsubPlus).planeMap point) 1| := by
      have hEqAbs :
          |pureWZ2OffsetShearNormal (1 / 2)
              ((source.sourceLocalGrains.restrict hsubPlus).planeMap point) 1| =
            |pureWZ2SourceShearCoordinate source .plus sourcePoint| := by
        simpa [PureWZ2FixedShearChoice.shear, sourcePoint] using
          congrArg abs
            (pureWZ2OffsetShearNormal_restrict_coord_one_eq
              source hsubPlus .plus point)
      calc
        (1 / 50 : ℝ) ≤ |pureWZ2SourceShearCoordinate source .plus sourcePoint| := hdenom'
        _ = |pureWZ2OffsetShearNormal (1 / 2)
              ((source.sourceLocalGrains.restrict hsubPlus).planeMap point) 1| := by
            rw [hEqAbs]
    simpa [selectedLocal] using hrestricted
  · have hplusLt :
        plusShading.mass < (1 / 2 : ENNReal) * source.sourceShading.mass :=
      lt_of_not_ge hplus
    have hminusHalf :
        (1 / 2 : ENNReal) * source.sourceShading.mass ≤ minusShading.mass := by
      by_contra hminus
      have hminusLt :
          minusShading.mass < (1 / 2 : ENNReal) * source.sourceShading.mass :=
        lt_of_not_ge hminus
      have hsumLt :
          plusShading.mass + minusShading.mass <
            (1 / 2 : ENNReal) * source.sourceShading.mass +
              (1 / 2 : ENNReal) * source.sourceShading.mass :=
        ENNReal.add_lt_add hplusLt hminusLt
      have hHalfAdd : (1 / 2 : ENNReal) + (1 / 2 : ENNReal) = 1 := by
        have h1 : (1 / 2 : ENNReal) = ↑(1 / 2 : NNReal) := by simp
        rw [h1]
        have h2 :
            (↑(1 / 2 : NNReal) : ENNReal) + (↑(1 / 2 : NNReal) : ENNReal) =
              ↑((1 / 2 : NNReal) + (1 / 2 : NNReal)) := by
          rw [ENNReal.coe_add]
        rw [h2]
        have h3 : (1 / 2 : NNReal) + (1 / 2 : NNReal) = 1 := by
          apply Subtype.ext
          simp [NNReal.coe_add]
          norm_num
        rw [h3]
        simp
      have hsumEq :
          (1 / 2 : ENNReal) * source.sourceShading.mass +
              (1 / 2 : ENNReal) * source.sourceShading.mass =
            source.sourceShading.mass := by
        rw [← add_mul, hHalfAdd, one_mul]
      rw [hsumEq] at hsumLt
      exact (lt_irrefl (plusShading.mass + minusShading.mass))
        (hsumLt.trans_le hMass)
    let selectedLocal := source.sourceLocalGrains.restrict hsubMinus
    let selectedGlobal :=
      source.sourceGlobalGrains.restrict_same_constant hsubMinus
    have hselectedUnion :
        minusShading.union =
          source.sourceShading.union ∩ minusSet :=
      pureWZ2PaperRestrictToSet_union source.sourceShading minusSet
        (pureWZ2SourceShearSet_measurable source .minus)
    refine ⟨{
      shear_choice := .minus
      shear := -1 / 2
      shear_eq := by rfl
      selectedShading := minusShading
      selected_subshading := hsubMinus
      selected_union := hselectedUnion
      selectedLocalGrains := selectedLocal
      selectedGlobalGrains := selectedGlobal
      half_mass := hminusHalf
      denominator_lower := ?_
    }⟩
    intro point
    have hmem : point.1 ∈ source.sourceShading.union ∩ minusSet := by
      simpa [hselectedUnion] using point.property
    have hdenom :
        (1 / 50 : ℝ) ≤
          |pureWZ2SourceShearCoordinate source .minus
            ⟨point.1, hmem.1⟩| := by
      exact (mem_pureWZ2SourceShearSet_iff source .minus hmem.1).mp hmem.2
    let sourcePoint : {point : Point3 // point ∈ source.sourceShading.union} :=
      ⟨point.1, paperSubshading_union_subset hsubMinus point.property⟩
    have hsourcePoint : sourcePoint = ⟨point.1, hmem.1⟩ := by
      apply Subtype.ext
      rfl
    have hdenom' :
        (1 / 50 : ℝ) ≤
          |pureWZ2SourceShearCoordinate source .minus sourcePoint| := by
      rw [hsourcePoint]
      exact hdenom
    have hrestricted :
        (1 / 50 : ℝ) ≤
          |pureWZ2OffsetShearNormal (-1 / 2)
              ((source.sourceLocalGrains.restrict hsubMinus).planeMap point) 1| := by
      have hEqAbs :
          |pureWZ2OffsetShearNormal (-1 / 2)
              ((source.sourceLocalGrains.restrict hsubMinus).planeMap point) 1| =
            |pureWZ2SourceShearCoordinate source .minus sourcePoint| := by
        simpa [PureWZ2FixedShearChoice.shear, sourcePoint] using
          congrArg abs
            (pureWZ2OffsetShearNormal_restrict_coord_one_eq
              source hsubMinus .minus point)
      calc
        (1 / 50 : ℝ) ≤ |pureWZ2SourceShearCoordinate source .minus sourcePoint| := hdenom'
        _ = |pureWZ2OffsetShearNormal (-1 / 2)
              ((source.sourceLocalGrains.restrict hsubMinus).planeMap point) 1| := by
            rw [hEqAbs]
    simpa [selectedLocal] using hrestricted

end Kakeya.Assouad

end
