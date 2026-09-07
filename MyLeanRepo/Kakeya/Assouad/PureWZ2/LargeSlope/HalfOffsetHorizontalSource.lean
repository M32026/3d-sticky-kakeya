import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectSection6SourceInterface
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.OffsetShearProjectiveNormal
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.ExactDiagonalCubicalGlobalAD

/-!
# Fixed-shear projective source normal

This module records the source-side fixed-shear chart before any horizontal
rescaling.  The actual source shading and local plane map are preserved
verbatim; only the public shear witness used by the affine rescaling is
replaced by a chosen constant `a` with a compensating intercept shift.

The only source-side certificate retained here is the one genuinely consumed
by the terminal projective-normal estimates: a bound `|a| ≤ 1/2` and a
uniform denominator lower bound on the actual retained source points.
-/

noncomputable section

namespace Kakeya.Assouad

open Set

attribute [local instance] Classical.propDecidable

/-- Adding a constant to a paper-interval slope changes neither derivative
bound in the nonsingularity certificate. -/
theorem PureWZ2C2SlopeIsNonsingular.addConstant
    {f : PureWZ2C2SlopeFunction} (hf : PureWZ2C2SlopeIsNonsingular f)
    (k : ℝ) :
    PureWZ2C2SlopeIsNonsingular (fun t => f t + k) := by
  rcases hf with ⟨extension, hsmooth, hextension, hbounds⟩
  refine ⟨fun z => extension z + k, hsmooth.add contDiffOn_const, ?_, ?_⟩
  · intro t
    change extension t.1 + k = f t + k
    rw [hextension t]
  · intro t
    have h := hbounds t
    refine ⟨?_, ?_, ?_⟩
    · simpa only [deriv_add_const] using h.1
    · simpa only [deriv_add_const] using h.2.1
    · have hderiv : deriv (fun z => extension z + k) = deriv extension := by
        funext z
        exact deriv_add_const k
      rw [hderiv]
      exact h.2.2

namespace PureWZ2HalfOffsetHorizontalSourceData

variable {sigma delta : ℝ}

/-- The half-offset coefficient is chosen at the midpoint of the actual source
interval used by the affine map. -/
def anchorSlope
    {inputLoss : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma inputLoss delta}
    (source : PureWZ2HorizontalSourceData cfg) : ℝ :=
  cfg.globalGrains.slope (source.c + (source.d - source.c) / 2)

def canonicalHalfOffset
    {inputLoss : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma inputLoss delta}
    (source : PureWZ2HorizontalSourceData cfg) : ℝ :=
  pureWZ2HalfOffset (anchorSlope source)

/-- The actual stored affine shear witness carried by the source data.  This is
the quantity terminal constructions must use. -/
def offset
    {inputLoss : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma inputLoss delta}
    (source : PureWZ2HorizontalSourceData cfg) : ℝ :=
  source.geometrySlope (source.c + (source.d - source.c) / 2)

theorem anchorSlope_abs_le_one
    {inputLoss : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma inputLoss delta}
    (source : PureWZ2HorizontalSourceData cfg) :
    |anchorSlope source| ≤ 1 := by
  apply (cfg.globalGrains.slope_normalized _ ?_).1
  constructor
  · linarith [source.left_mem, source.ordered.le]
  · linarith [source.right_mem, source.ordered.le]

theorem canonicalHalfOffset_abs_le
    {inputLoss : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma inputLoss delta}
    (source : PureWZ2HorizontalSourceData cfg) :
    |canonicalHalfOffset source| ≤ 1 / 2 := by
  exact pureWZ2HalfOffset_abs_le (anchorSlope_abs_le_one source)

/-- The direct fixed-shear chart certificate actually consumed by the terminal
projective-normal estimates.  It only records the actual stored source shear
and the uniform denominator lower bound on the retained source normals. -/
structure FixedShearChart
    {inputLoss : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma inputLoss delta}
    (source : PureWZ2HorizontalSourceData cfg) where
  offset_abs_le : |offset source| ≤ 1 / 2
  denominator_lower : ∀ point : {point : Point3 // point ∈ source.sourceShading.union},
    (1 / 50 : ℝ) ≤
      |pureWZ2OffsetShearNormal (offset source)
          (source.sourceLocalGrains.planeMap point) 1|

/-- Replace the source's internal horizontal shear by an explicit fixed chart
parameter `a`.  The public interval slope is translated by the compensating
intercept change, so its derivative certificate is retained verbatim while the
actual source shading and grain records stay unchanged. -/
noncomputable def withFixedShear
    {sigma inputLoss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma inputLoss delta}
    (source : PureWZ2HorizontalSourceData cfg)
    (a : ℝ) (ha : |a| ≤ 1 / 2) :
    PureWZ2HorizontalSourceData cfg := by
  let midpoint : ℝ := source.c + (source.d - source.c) / 2
  let denominator : ℝ := source.m * (source.d - source.c) / 2
  let shift : ℝ := (source.geometrySlope midpoint - a) / denominator
  have hdenominator : denominator ≠ 0 := by
    dsimp only [denominator]
    have hlength : source.d - source.c ≠ 0 := sub_ne_zero.mpr source.ordered.ne'
    exact div_ne_zero (mul_ne_zero source.slopeScale_pos.ne' hlength) (by norm_num)
  refine {
    c := source.c
    d := source.d
    m := source.m
    left_mem := source.left_mem
    ordered := source.ordered
    right_mem := source.right_mem
    source_length := source.source_length
    length_eq := source.length_eq
    slopeScale_pos := source.slopeScale_pos
    slopeScale_lower := source.slopeScale_lower
    slopeScale_le_one := source.slopeScale_le_one
    globalSlope := source.globalSlope
    globalSlope_eq_on := source.globalSlope_eq_on
    globalSlope_normalized := source.globalSlope_normalized
    derivative_band := source.derivative_band
    sourceShading := source.sourceShading
    source_in_interval := source.source_in_interval
    source_mass_lower := source.source_mass_lower
    source_mass_card := source.source_mass_card
    sourceGlobalGrains := source.sourceGlobalGrains
    source_global_slope_eq := source.source_global_slope_eq
    sourceLocalGrains := source.sourceLocalGrains
    geometrySlope := { toFun := fun _ => a, contDiff := contDiff_const }
    geometrySlope_normalized := by
      intro z _
      refine ⟨ha.trans (by norm_num), ?_, ?_⟩
      · simp
      · simp
    f := fun t => source.f t + shift
    f_nonsingular := source.f_nonsingular.addConstant shift
    f_formula := ?_
  }
  intro t
  rw [source.f_formula]
  dsimp only [midpoint, denominator, shift]
  simp only [anisotropicRescaledSlopeWithShear]
  field_simp [hdenominator]
  ring

/-- The legacy midpoint half-offset chart, now exposed only as a wrapper around
the general fixed-shear replacement. -/
noncomputable def withHalfOffset
    {sigma inputLoss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma inputLoss delta}
    (source : PureWZ2HorizontalSourceData cfg) :
    PureWZ2HorizontalSourceData cfg := by
  have ha : |canonicalHalfOffset source| ≤ 1 / 2 := canonicalHalfOffset_abs_le source
  exact withFixedShear source (canonicalHalfOffset source) ha

@[simp] theorem withFixedShear_geometrySlope_apply
    {sigma inputLoss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma inputLoss delta}
    (source : PureWZ2HorizontalSourceData cfg)
    (a : ℝ) (ha : |a| ≤ 1 / 2) (z : ℝ) :
    (withFixedShear source a ha).geometrySlope z = a := by
  simp only [withFixedShear]

theorem withFixedShear_geometrySlope_midpoint
    {sigma inputLoss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma inputLoss delta}
    (source : PureWZ2HorizontalSourceData cfg)
    (a : ℝ) (ha : |a| ≤ 1 / 2) :
    (withFixedShear source a ha).geometrySlope
      (source.c + (source.d - source.c) / 2) = a := by
  simp

@[simp] theorem withFixedShear_sourceShading
    {sigma inputLoss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma inputLoss delta}
    (source : PureWZ2HorizontalSourceData cfg)
    (a : ℝ) (ha : |a| ≤ 1 / 2) :
    (withFixedShear source a ha).sourceShading = source.sourceShading := by
  simp only [withFixedShear]

@[simp] theorem withFixedShear_sourceLocalGrains
    {sigma inputLoss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma inputLoss delta}
    (source : PureWZ2HorizontalSourceData cfg)
    (a : ℝ) (ha : |a| ≤ 1 / 2) :
    (withFixedShear source a ha).sourceLocalGrains = source.sourceLocalGrains := by
  simp only [withFixedShear]

@[simp] theorem withFixedShear_sourceGlobalGrains
    {sigma inputLoss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma inputLoss delta}
    (source : PureWZ2HorizontalSourceData cfg)
    (a : ℝ) (ha : |a| ≤ 1 / 2) :
    (withFixedShear source a ha).sourceGlobalGrains = source.sourceGlobalGrains := by
  simp only [withFixedShear]

theorem withHalfOffset_geometrySlope_midpoint
    {inputLoss : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma inputLoss delta}
    (source : PureWZ2HorizontalSourceData cfg) :
    (withHalfOffset source).geometrySlope
      (source.c + (source.d - source.c) / 2) =
        canonicalHalfOffset source := by
  simp [withHalfOffset, canonicalHalfOffset]

@[simp] theorem withHalfOffset_sourceShading
    {sigma inputLoss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma inputLoss delta}
    (source : PureWZ2HorizontalSourceData cfg) :
    (withHalfOffset source).sourceShading = source.sourceShading := by
  simpa [withHalfOffset] using
    withFixedShear_sourceShading source (canonicalHalfOffset source)
      (canonicalHalfOffset_abs_le source)

@[simp] theorem withHalfOffset_sourceLocalGrains
    {sigma inputLoss delta : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma inputLoss delta}
    (source : PureWZ2HorizontalSourceData cfg) :
    (withHalfOffset source).sourceLocalGrains = source.sourceLocalGrains := by
  simpa [withHalfOffset] using
    withFixedShear_sourceLocalGrains source (canonicalHalfOffset source)
      (canonicalHalfOffset_abs_le source)

@[simp] theorem offset_withFixedShear
    {inputLoss : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma inputLoss delta}
    {source : PureWZ2HorizontalSourceData cfg}
    (a : ℝ) (ha : |a| ≤ 1 / 2) :
    offset (withFixedShear source a ha) = a := by
  simp [offset, withFixedShear]

@[simp] theorem offset_withHalfOffset
    {inputLoss : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma inputLoss delta}
    (source : PureWZ2HorizontalSourceData cfg) :
    offset (withHalfOffset source) = canonicalHalfOffset source := by
  simp [withHalfOffset, canonicalHalfOffset, offset_withFixedShear]

/-- Build the direct chart certificate on a source whose stored geometry shear
has been explicitly replaced by a fixed constant `a`. -/
theorem fixedShearChart_withFixedShear
    {inputLoss : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma inputLoss delta}
    (source : PureWZ2HorizontalSourceData cfg)
    (a : ℝ) (ha : |a| ≤ 1 / 2)
    (hdenom : ∀ point : {point : Point3 // point ∈ source.sourceShading.union},
      (1 / 50 : ℝ) ≤
        |pureWZ2OffsetShearNormal a
            (source.sourceLocalGrains.planeMap point) 1|) :
    FixedShearChart (withFixedShear source a ha) := by
  refine {
    offset_abs_le := by simpa [offset_withFixedShear] using ha
    denominator_lower := ?_
  }
  intro point
  have hpoint : point.1 ∈ source.sourceShading.union := by
    simpa using point.property
  have hptEq : (⟨point.1, hpoint⟩ : {point : Point3 // point ∈ source.sourceShading.union}) = point := by
    apply Subtype.ext
    rfl
  change (1 / 50 : ℝ) ≤
    |pureWZ2OffsetShearNormal a
        ((withFixedShear source a ha).sourceLocalGrains.planeMap point) 1|
  rw [← hptEq]
  simpa only [withFixedShear] using hdenom ⟨point.1, hpoint⟩

/-- Legacy helper for the canonical half-offset source. -/
theorem fixedShearChart_withHalfOffset
    {inputLoss : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma inputLoss delta}
    (source : PureWZ2HorizontalSourceData cfg)
    (hdenom : ∀ point : {point : Point3 // point ∈ source.sourceShading.union},
      (1 / 50 : ℝ) ≤
        |pureWZ2OffsetShearNormal (canonicalHalfOffset source)
            (source.sourceLocalGrains.planeMap point) 1|) :
    FixedShearChart (withHalfOffset source) := by
  have ha : |canonicalHalfOffset source| ≤ 1 / 2 := canonicalHalfOffset_abs_le source
  have hchart := fixedShearChart_withFixedShear source (canonicalHalfOffset source) ha hdenom
  change FixedShearChart (withFixedShear source (canonicalHalfOffset source) ha)
  exact hchart

theorem offset_abs_le
    {inputLoss : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma inputLoss delta}
    {source : PureWZ2HorizontalSourceData cfg}
    (chart : FixedShearChart source) :
    |offset source| ≤ 1 / 2 := chart.offset_abs_le

/-- The normalized global slope changes by at most `1/200` from the midpoint
of the actual source interval. -/
theorem source_slope_close_anchor
    {inputLoss : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma inputLoss delta}
    (source : PureWZ2HorizontalSourceData cfg)
    (point : {point : Point3 // point ∈ source.sourceShading.union}) :
    |cfg.globalGrains.slope (point.1 2) - anchorSlope source| ≤ 1 / 200 := by
  have hmid : source.c + (source.d - source.c) / 2 ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [source.left_mem, source.right_mem, source.ordered.le]
  rcases point.property with ⟨index, hcarrier⟩
  have hz := source.source_in_interval index hcarrier
  have hpoint : point.1 2 ∈ Set.Icc (-1 : ℝ) 1 := by
    exact ⟨source.left_mem.trans hz.1, hz.2.trans source.right_mem⟩
  have hlip := cfg.globalGrains.slope_lipschitzOn
  have hvariation := hlip.norm_sub_le hpoint hmid
  have hdistance : |point.1 2 -
      (source.c + (source.d - source.c) / 2)| ≤
      (source.d - source.c) / 2 := by
    rw [abs_le]
    constructor <;> linarith [hz.1, hz.2]
  have hwidth : (source.d - source.c) / 2 ≤ 1 / 200 := by
    rw [source.length_eq]
    calc
      source.source_length / 100 / 2 ≤ source.m / 200 := by
        nlinarith [source.slopeScale_lower]
      _ ≤ 1 / 200 := by nlinarith [source.slopeScale_le_one]
  have hresult :
      |cfg.globalGrains.slope (point.1 2) -
          cfg.globalGrains.slope
            (source.c + (source.d - source.c) / 2)| ≤
        1 / 200 := by
    have hvariation' :
        |cfg.globalGrains.slope (point.1 2) -
            cfg.globalGrains.slope
              (source.c + (source.d - source.c) / 2)| ≤
          |point.1 2 - (source.c + (source.d - source.c) / 2)| := by
      simpa [Real.dist_eq] using hvariation
    exact hvariation'.trans (hdistance.trans hwidth)
  simpa [anchorSlope] using hresult

theorem offsetShearNormal_coord_one_lower_restrict
    {inputLoss : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma inputLoss delta}
    (source : PureWZ2HorizontalSourceData cfg)
    (chart : FixedShearChart source)
    (point : {point : Point3 // point ∈ source.sourceShading.union}) :
    (1 / 50 : ℝ) ≤
      |pureWZ2OffsetShearNormal (offset source)
        (source.sourceLocalGrains.planeMap point) 1| :=
  chart.denominator_lower point

theorem projectiveNormal_lipschitz_restrict
    {inputLoss : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma inputLoss delta}
    (source : PureWZ2HorizontalSourceData cfg)
    (chart : FixedShearChart source) :
    LipschitzWith 10100
      (fun point => pureWZ2OffsetShearProjectiveNormal (offset source)
        (source.sourceLocalGrains.planeMap point)) := by
  have hraw : LipschitzWith 2
      (fun point => pureWZ2OffsetShearNormal (offset source)
        (source.sourceLocalGrains.planeMap point)) := by
    simpa using pureWZ2OffsetShearNormal_lipschitz chart.offset_abs_le
      source.sourceLocalGrains.planeMap_lipschitz
  have hnorm : ∀ point, ‖pureWZ2OffsetShearNormal (offset source)
      (source.sourceLocalGrains.planeMap point)‖ ≤ 2 := by
    intro point
    simpa [source.sourceLocalGrains.planeMap_unit point] using
      pureWZ2OffsetShearNormal_norm_le_two chart.offset_abs_le
        (source.sourceLocalGrains.planeMap point)
  have hcoord : ∀ point, ((1 / 50 : ℝ) : ℝ) ≤
      |pureWZ2OffsetShearNormal (offset source)
        (source.sourceLocalGrains.planeMap point) 1| := by
    intro point
    exact (offsetShearNormal_coord_one_lower_restrict
      source chart point)
  have hlip := pureWZ2OffsetShearProjectiveNormal_lipschitz
    (a := offset source) (B := (2 : NNReal)) (c := (1 / 50 : NNReal))
    (K := (2 : NNReal)) hraw (by norm_num) hnorm hcoord
  have hconstant : (((1 / 50 : NNReal)⁻¹ +
      (2 : NNReal) * (1 / 50 : NNReal)⁻¹ ^ 2) * 2) = 10100 := by
    norm_num
  rw [← hconstant]
  exact hlip

theorem projectiveNormal_coord_one_restrict
    {inputLoss : ℝ}
    {cfg : PureWZ2C2GrainConfiguration sigma inputLoss delta}
    (source : PureWZ2HorizontalSourceData cfg)
    (chart : FixedShearChart source)
    (point : {point : Point3 // point ∈ source.sourceShading.union}) :
    pureWZ2OffsetShearProjectiveNormal (offset source)
      (source.sourceLocalGrains.planeMap point) 1 = 1 := by
  apply pureWZ2OffsetShearProjectiveNormal_coord_one
  have hpositive := offsetShearNormal_coord_one_lower_restrict
    source chart point
  intro hzero
  rw [hzero, abs_zero] at hpositive
  norm_num at hpositive

end PureWZ2HalfOffsetHorizontalSourceData

end Kakeya.Assouad

end
