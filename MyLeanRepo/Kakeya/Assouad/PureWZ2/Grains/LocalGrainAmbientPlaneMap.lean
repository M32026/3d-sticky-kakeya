import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.LocalGrainRestriction
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.TransversePairPaper
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.FinestCellPlaneMap
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Ambient extension of a strict local-grain plane map

The strict paper interface stores its plane map on the shading union subtype.
For geometric refinements it is convenient to keep an ambient measurable
function.  Finite-dimensional Lipschitz extension gives such a function and
agrees exactly with the original map at every shaded point.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open Set

attribute [local instance] Classical.propDecidable

/-- Globally regular radial clipping.  It is the identity on the unit sphere
and becomes radial normalization as soon as the input norm is at least
`1/2`. -/
def pureWZ2ClippedRadialMap (point : Point3) : Point3 :=
  (max (1 / 2 : ℝ) ‖point‖)⁻¹ • point

theorem pureWZ2ClippedRadialMap_norm_of_half_le
    {point : Point3} (hpoint : (1 / 2 : ℝ) ≤ ‖point‖) :
    ‖pureWZ2ClippedRadialMap point‖ = 1 := by
  have hpointNe : point ≠ 0 := by
    intro hzero
    subst point
    norm_num at hpoint
  rw [pureWZ2ClippedRadialMap, max_eq_right hpoint]
  exact norm_smul_inv_norm hpointNe

theorem pureWZ2ClippedRadialMap_eq_self
    {point : Point3} (hpoint : ‖point‖ = 1) :
    pureWZ2ClippedRadialMap point = point := by
  rw [pureWZ2ClippedRadialMap, max_eq_right (by rw [hpoint]; norm_num),
    hpoint]
  simp

theorem pureWZ2ClippedRadialMap_measurable :
    Measurable pureWZ2ClippedRadialMap := by
  unfold pureWZ2ClippedRadialMap
  fun_prop

/-- The clipped radial map is globally four-Lipschitz. -/
theorem pureWZ2ClippedRadialMap_lipschitz :
    LipschitzWith 4 pureWZ2ClippedRadialMap := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro first second
  let firstScale : ℝ := max (1 / 2) ‖first‖
  let secondScale : ℝ := max (1 / 2) ‖second‖
  have hfirstScale : 0 < firstScale :=
    (by norm_num : (0 : ℝ) < 1 / 2).trans_le (le_max_left _ _)
  have hsecondScale : 0 < secondScale :=
    (by norm_num : (0 : ℝ) < 1 / 2).trans_le (le_max_left _ _)
  have hfirstNorm : ‖first‖ ≤ firstScale := le_max_right _ _
  have hsecondNorm : ‖second‖ ≤ secondScale := le_max_right _ _
  have hscaleDifference : |firstScale - secondScale| ≤ ‖first - second‖ := by
    calc
      |firstScale - secondScale| ≤
          max |(1 / 2 : ℝ) - 1 / 2| |‖first‖ - ‖second‖| := by
        exact abs_max_sub_max_le_max _ _ _ _
      _ = |‖first‖ - ‖second‖| := by simp
      _ ≤ ‖first - second‖ := abs_norm_sub_norm_le first second
  have hinverseDifference :
      |firstScale⁻¹ - secondScale⁻¹| =
        |firstScale - secondScale| / (firstScale * secondScale) := by
    rw [inv_sub_inv hfirstScale.ne' hsecondScale.ne']
    rw [abs_div, abs_mul, abs_of_pos hfirstScale, abs_of_pos hsecondScale]
    rw [abs_sub_comm]
  have hsecondTerm :
      |firstScale⁻¹ - secondScale⁻¹| * ‖second‖ ≤
        ‖first - second‖ / firstScale := by
    rw [hinverseDifference]
    have hscaleRatio : ‖second‖ / secondScale ≤ 1 :=
      (div_le_one hsecondScale).2 hsecondNorm
    have hdifferenceRatio :
        |firstScale - secondScale| / firstScale ≤
          ‖first - second‖ / firstScale := by gcongr
    calc
      |firstScale - secondScale| / (firstScale * secondScale) *
            ‖second‖ =
          (|firstScale - secondScale| / firstScale) *
            (‖second‖ / secondScale) := by
        field_simp [hfirstScale.ne', hsecondScale.ne']
      _ ≤ (‖first - second‖ / firstScale) * 1 := by
        exact mul_le_mul hdifferenceRatio hscaleRatio (by positivity)
          (by positivity)
      _ = ‖first - second‖ / firstScale := by ring
  have hdecompose :
      firstScale⁻¹ • first - secondScale⁻¹ • second =
        firstScale⁻¹ • (first - second) +
          (firstScale⁻¹ - secondScale⁻¹) • second := by
    simp [sub_smul, smul_sub]
  change ‖pureWZ2ClippedRadialMap first -
      pureWZ2ClippedRadialMap second‖ ≤ (4 : ℝ) * ‖first - second‖
  rw [pureWZ2ClippedRadialMap, pureWZ2ClippedRadialMap]
  change ‖firstScale⁻¹ • first - secondScale⁻¹ • second‖ ≤ _
  rw [hdecompose]
  calc
    ‖firstScale⁻¹ • (first - second) +
        (firstScale⁻¹ - secondScale⁻¹) • second‖ ≤
        ‖firstScale⁻¹ • (first - second)‖ +
          ‖(firstScale⁻¹ - secondScale⁻¹) • second‖ := norm_add_le _ _
    _ = ‖first - second‖ / firstScale +
        |firstScale⁻¹ - secondScale⁻¹| * ‖second‖ := by
      rw [norm_smul, norm_smul]
      simp only [Real.norm_eq_abs, abs_inv, abs_of_pos hfirstScale]
      ring
    _ ≤ ‖first - second‖ / firstScale +
        ‖first - second‖ / firstScale := by gcongr
    _ ≤ (4 : ℝ) * ‖first - second‖ := by
      have hhalf : (1 / 2 : ℝ) ≤ firstScale := le_max_left _ _
      have hterm : ‖first - second‖ / firstScale ≤
          2 * ‖first - second‖ := by
        calc
          ‖first - second‖ / firstScale ≤
              ‖first - second‖ / (1 / 2 : ℝ) := by gcongr
          _ = 2 * ‖first - second‖ := by ring
      linarith

/-- An ambient extension of a weak plane map which is already Lipschitz on
its shading union.  The extension agrees pointwise on the shading, so the
unit-normal and tube-incidence certificates are transported without any
change of constants. -/
structure PureWZ2AmbientWeakPlaneMapExtension
    {delta incidence : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (planeMap : PaperWZ1WeakPlaneMapData shading incidence)
    (coefficient : NNReal) where
  ambient : PaperWZ1WeakPlaneMapData shading incidence
  lipschitz : LipschitzWith
    (lipschitzExtensionConstant Point3 * coefficient) ambient.planeMap
  agrees : ∀ point : {point : Point3 // point ∈ shading.union},
    ambient.planeMap point = planeMap.planeMap point

/-- Extend a weak plane map from its actual shading union to all of
`Point3`.  This is the non-circular form needed before constructing any local
grain data. -/
theorem weak_plane_map_ambient_extension
    {delta incidence : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (planeMap : PaperWZ1WeakPlaneMapData shading incidence)
    (coefficient : NNReal)
    (hlipschitz : LipschitzWith coefficient
      (fun point : {point : Point3 // point ∈ shading.union} =>
        planeMap.planeMap point)) :
    Nonempty (PureWZ2AmbientWeakPlaneMapExtension planeMap coefficient) := by
  let sourceMap : Point3 → Point3 := fun point =>
    if hpoint : point ∈ shading.union then
      planeMap.planeMap point else 0
  have hsourceMap : LipschitzOnWith coefficient sourceMap shading.union := by
    intro first hfirst second hsecond
    simp only [sourceMap, hfirst, hsecond, dif_pos]
    exact hlipschitz ⟨first, hfirst⟩ ⟨second, hsecond⟩
  rcases hsourceMap.extend_finite_dimension with
    ⟨extended, hextended, heq⟩
  let ambient : PaperWZ1WeakPlaneMapData shading incidence :=
    { planeMap := extended
      measurable := hextended.continuous.measurable
      unit := by
        intro point hpoint
        rw [← heq hpoint]
        simp [sourceMap, hpoint, planeMap.unit]
      incidence := by
        intro index point hpoint
        have hpointUnion : point ∈ shading.union := ⟨index, hpoint⟩
        rw [← heq hpointUnion]
        simpa [sourceMap, hpointUnion] using
          planeMap.incidence index point hpoint }
  refine ⟨{
    ambient := ambient
    lipschitz := hextended
    agrees := ?_
  }⟩
  intro point
  change extended point = planeMap.planeMap point
  rw [← heq point.property]
  simp [sourceMap, point.property]

/-- A fixed ambient extension followed by globally regular radial clipping.
It agrees with the original unit map on the source shading. -/
structure PureWZ2UnitAmbientWeakPlaneMapExtension
    {delta incidence : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (planeMap : PaperWZ1WeakPlaneMapData shading incidence)
    (coefficient : NNReal) where
  raw : PureWZ2AmbientWeakPlaneMapExtension planeMap coefficient
  ambient : PaperWZ1WeakPlaneMapData shading incidence
  ambient_eq : ambient.planeMap =
    fun point => pureWZ2ClippedRadialMap (raw.ambient.planeMap point)
  lipschitz : LipschitzWith
    (4 * (lipschitzExtensionConstant Point3 * coefficient)) ambient.planeMap
  agrees : ∀ point : {point : Point3 // point ∈ shading.union},
    ambient.planeMap point = planeMap.planeMap point

namespace PureWZ2UnitAmbientWeakPlaneMapExtension

theorem lipschitzOn_of_raw_norm_half
    {delta incidence : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {planeMap : PaperWZ1WeakPlaneMapData shading incidence}
    {coefficient : NNReal}
    (extension : PureWZ2UnitAmbientWeakPlaneMapExtension planeMap coefficient)
    (target : Set Point3)
    (hlower : ∀ point ∈ target,
      (1 / 2 : ℝ) ≤ ‖extension.raw.ambient.planeMap point‖) :
    LipschitzOnWith
      (4 * (lipschitzExtensionConstant Point3 * coefficient))
      extension.ambient.planeMap target := by
  exact extension.lipschitz.lipschitzOnWith

theorem unitOn_of_raw_norm_half
    {delta incidence : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {planeMap : PaperWZ1WeakPlaneMapData shading incidence}
    {coefficient : NNReal}
    (extension : PureWZ2UnitAmbientWeakPlaneMapExtension planeMap coefficient)
    (target : Set Point3)
    (hlower : ∀ point ∈ target,
      (1 / 2 : ℝ) ≤ ‖extension.raw.ambient.planeMap point‖) :
    ∀ point ∈ target, ‖extension.ambient.planeMap point‖ = 1 := by
  intro point hpoint
  rw [extension.ambient_eq]
  exact pureWZ2ClippedRadialMap_norm_of_half_le (hlower point hpoint)

end PureWZ2UnitAmbientWeakPlaneMapExtension

/-- Construct the fixed unit-valued ambient map used throughout one finite
inner schedule.  Every pair-specific map is a restriction of this one
function. -/
theorem weak_plane_map_unit_ambient_extension
    {delta incidence : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (planeMap : PaperWZ1WeakPlaneMapData shading incidence)
    (coefficient : NNReal)
    (hlipschitz : LipschitzWith coefficient
      (fun point : {point : Point3 // point ∈ shading.union} =>
        planeMap.planeMap point)) :
    Nonempty (PureWZ2UnitAmbientWeakPlaneMapExtension planeMap coefficient) := by
  rcases weak_plane_map_ambient_extension planeMap coefficient hlipschitz with
    ⟨raw⟩
  let ambient : PaperWZ1WeakPlaneMapData shading incidence :=
    { planeMap := fun point =>
        pureWZ2ClippedRadialMap (raw.ambient.planeMap point)
      measurable := pureWZ2ClippedRadialMap_measurable.comp
        raw.ambient.measurable
      unit := by
        intro point hpoint
        have hagree : raw.ambient.planeMap point = planeMap.planeMap point :=
          raw.agrees ⟨point, hpoint⟩
        rw [show pureWZ2ClippedRadialMap (raw.ambient.planeMap point) =
            planeMap.planeMap point by
          rw [hagree]
          exact pureWZ2ClippedRadialMap_eq_self
            (planeMap.unit point hpoint)]
        exact planeMap.unit point hpoint
      incidence := by
        intro index point hpoint
        have hagree : raw.ambient.planeMap point = planeMap.planeMap point :=
          raw.agrees ⟨point, ⟨index, hpoint⟩⟩
        rw [show pureWZ2ClippedRadialMap (raw.ambient.planeMap point) =
            planeMap.planeMap point by
          rw [hagree]
          exact pureWZ2ClippedRadialMap_eq_self
            (planeMap.unit point ⟨index, hpoint⟩)]
        exact planeMap.incidence index point hpoint }
  refine ⟨{
    raw := raw
    ambient := ambient
    ambient_eq := rfl
    lipschitz := by
      simpa only [ambient, Function.comp_def] using
        pureWZ2ClippedRadialMap_lipschitz.comp raw.lipschitz
    agrees := ?_
  }⟩
  intro point
  change pureWZ2ClippedRadialMap (raw.ambient.planeMap point) =
    planeMap.planeMap point
  rw [raw.agrees point]
  exact pureWZ2ClippedRadialMap_eq_self (planeMap.unit point point.property)

/-- An ambient weak plane map which agrees with one strict local-grain plane
map at every shaded point. -/
structure PureWZ2AmbientPlaneMapExtension
    {delta sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {C : ENNReal}
    (localGrains : PureWZ2LocalGrainData shading sigma C) where
  ambient : PaperWZ1WeakPlaneMapData shading delta
  constant : NNReal
  lipschitz : LipschitzWith constant ambient.planeMap
  agrees : ∀ point : {point : Point3 // point ∈ shading.union},
    ambient.planeMap point = localGrains.planeMap point

/-- Extend the genuine strict local-grain plane map to all of `Point3`.  The
incidence scale and all unit values on the shading are unchanged. -/
theorem local_grain_ambient_plane_map
    {delta sigma : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {C : ENNReal}
    (localGrains : PureWZ2LocalGrainData shading sigma C) :
    Nonempty (PureWZ2AmbientPlaneMapExtension localGrains) := by
  let sourceMap : Point3 → Point3 := fun point =>
    if hpoint : point ∈ shading.union then
      localGrains.planeMap ⟨point, hpoint⟩ else 0
  have hsourceMap : LipschitzOnWith 1 sourceMap shading.union := by
    apply LipschitzOnWith.of_dist_le_mul
    intro first hfirst second hsecond
    simp only [sourceMap, hfirst, hsecond, dif_pos]
    have h := localGrains.planeMap_lipschitz.dist_le_mul
      ⟨first, hfirst⟩ ⟨second, hsecond⟩
    simpa [Subtype.dist_eq] using h
  rcases hsourceMap.extend_finite_dimension with
    ⟨extended, hextended, heq⟩
  let K : NNReal := lipschitzExtensionConstant Point3
  let ambient : PaperWZ1WeakPlaneMapData shading delta :=
    { planeMap := extended
      measurable := hextended.continuous.measurable
      unit := by
        intro point hpoint
        rw [← heq hpoint]
        simp [sourceMap, hpoint, localGrains.planeMap_unit]
      incidence := by
        intro index point hpoint
        have hpointUnion : point ∈ shading.union := ⟨index, hpoint⟩
        rw [← heq hpointUnion]
        simpa [sourceMap, hpointUnion] using
          localGrains.planeMap_incidence index point hpoint }
  refine ⟨{ ambient := ambient
            constant := K
            lipschitz := ?_
            agrees := ?_ }⟩
  · simpa [ambient, K] using hextended
  · intro point
    have hpoint := point.prop
    change extended point = localGrains.planeMap point
    rw [← heq hpoint]
    simp [sourceMap, hpoint]

end Kakeya.Assouad.PureWZ2

end
