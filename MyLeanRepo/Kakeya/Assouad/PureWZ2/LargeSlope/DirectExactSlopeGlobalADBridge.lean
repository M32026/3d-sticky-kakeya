import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectAnisotropicRetubing
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.HorizontalNormalizationGlobalAD
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.LineClassSlopeCompatibleNormalization

/-!
# Exact public slope and global AD for the direct Section-6 map

The direct route already carries the interval-domain nonsingular slope selected
from the actual Node-5 configuration.  This module records that the slope in
the exact triangular projection identity is literally that public slope.  No
affine tangent, slope approximation, or extra slope-error radius is used.
-/

noncomputable section

namespace Kakeya.Assouad

open Set

/-- The Node-6 global representative agrees with the paper slope on its
literal domain. -/
theorem PureWZ2DirectSection6SourceAssembly.globalSlope_eq_cfg
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    (assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta) :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      assembly.globalSlope z = assembly.cfg.globalGrains.slope z :=
  assembly.globalSlope_eq_source

/-- The Node-6 globalization of the interval slope supplies a smooth internal
witness for the arbitrary-shear rescaling.  It is obtained from the centered
witness by a constant value translation, so no derivative bound changes and
no zero-intercept condition is introduced. -/
theorem PureWZ2DirectSection6SourceAssembly.exists_exactGlobalSlope
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    (assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta) :
    ∃ slope : SlopeFunction,
      slope.IsNonsingular ∧ ∀ t : ℝ, slope t =
        anisotropicRescaledSlopeWithShear assembly.globalSlope
          assembly.horizontalSource.c assembly.horizontalSource.d
          assembly.horizontalSource.m
          (assembly.horizontalSource.geometrySlope
            (assembly.horizontalSource.c +
              (assembly.horizontalSource.d - assembly.horizontalSource.c) / 2))
          t := by
  rcases slope_rescaling_to_centered_nonsingular
    assembly.globalSlope
    assembly.globalSlope_normalized
    assembly.horizontalSource.ordered
    assembly.horizontalSource.slopeScale_pos
    (by
      intro z hz
      exact ⟨assembly.horizontalSource.left_mem.trans hz.1,
        hz.2.trans assembly.horizontalSource.right_mem⟩)
    (by
      intro z hz
      rw [assembly.globalSlope_eq_horizontalSource]
      exact assembly.horizontalSource.derivative_band z hz)
    (by
      calc
        assembly.horizontalSource.d - assembly.horizontalSource.c =
            assembly.horizontalSource.source_length / 100 :=
          assembly.horizontalSource.length_eq
        _ ≤ assembly.horizontalSource.m / 100 := by
          exact div_le_div_of_nonneg_right
            assembly.horizontalSource.slopeScale_lower (by norm_num)
        _ ≤ assembly.horizontalSource.m / 50 := by
          linarith [assembly.horizontalSource.slopeScale_pos]) with
    ⟨centeredSlope, hcenteredNonsingular, _hcenteredZero, hcenteredFormula⟩
  let center : ℝ := assembly.horizontalSource.c +
    (assembly.horizontalSource.d - assembly.horizontalSource.c) / 2
  let scale : ℝ := assembly.horizontalSource.m *
    (assembly.horizontalSource.d - assembly.horizontalSource.c) / 2
  let offset : ℝ :=
    (assembly.globalSlope center -
      assembly.horizontalSource.geometrySlope center) / scale
  let slope : SlopeFunction := centeredSlope.addConstant offset
  refine ⟨slope, SlopeFunction.addConstant_isNonsingular
    hcenteredNonsingular offset, ?_⟩
  intro t
  rw [show slope t = centeredSlope t + offset by rfl, hcenteredFormula]
  simp only [anisotropicRescaledSlope, anisotropicRescaledSlopeWithShear,
    center, scale, offset]
  ring

/-- The exact globally smooth slope used by the direct triangular map.  Its
restriction to `[-1,1]` is the already frozen public slope
`horizontalSource.f`. -/
noncomputable def PureWZ2DirectSection6SourceAssembly.exactGlobalSlope
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    (assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta) : SlopeFunction :=
  Classical.choose assembly.exists_exactGlobalSlope

theorem PureWZ2DirectSection6SourceAssembly.exactGlobalSlope_formula
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    (assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta) (t : ℝ) :
    assembly.exactGlobalSlope t =
      anisotropicRescaledSlopeWithShear assembly.globalSlope
        assembly.horizontalSource.c assembly.horizontalSource.d
        assembly.horizontalSource.m
        (assembly.horizontalSource.geometrySlope
          (assembly.horizontalSource.c +
            (assembly.horizontalSource.d - assembly.horizontalSource.c) / 2))
        t :=
  (Classical.choose_spec assembly.exists_exactGlobalSlope).2 t

/-- The new global representative agrees pointwise with the old public slope
on the paper interval.  The proof uses the single Node-6 globalized
representative throughout, so no second extension is selected here. -/
theorem PureWZ2DirectSection6SourceAssembly.exactGlobalSlope_onUnitInterval
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    (assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta)
    (t : PureWZ2UnitInterval) :
    assembly.exactGlobalSlope t.1 = assembly.horizontalSource.f t := by
  rw [assembly.exactGlobalSlope_formula]
  rw [assembly.globalSlope_eq_horizontalSource]
  exact assembly.horizontalSource.f_formula t |>.symm

/-- The exact global representative inherits the already proved public
nonsingularity certificate. -/
theorem PureWZ2DirectSection6SourceAssembly.exactGlobalSlope_nonsingular
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    (assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta) :
    assembly.exactGlobalSlope.IsNonsingular :=
  (Classical.choose_spec assembly.exists_exactGlobalSlope).1

/-- When the horizontal popular-box center has target height zero, the slope
transported by the combined triangular and horizontal map is exactly the
frozen global slope on all of `ℝ`.  This is stronger than the later
interval-domain identification with `horizontalSource.f`. -/
theorem PureWZ2DirectSection6SourceAssembly.horizontalNormalizedSlope_eq_exactGlobalSlope
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    (assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta)
    (horizontalCenter : Point3)
    (hcenterHeight : horizontalCenter 2 = 0) :
    ∀ t : ℝ,
      pureWZ2HorizontalNormalizedSlope assembly.horizontalSource.geometrySlope
          assembly.globalSlope
          assembly.horizontalSource.c assembly.horizontalSource.d
          assembly.horizontalSource.m horizontalCenter t =
        assembly.exactGlobalSlope t := by
  intro t
  rw [assembly.exactGlobalSlope_formula]
  simp [pureWZ2HorizontalNormalizedSlope, hcenterHeight]

/-- Function-level form of the preceding pointwise identity.  The combined
horizontal map therefore carries the very same global function used by the
frozen Node-6 output, rather than a separately chosen extension. -/
theorem PureWZ2DirectSection6SourceAssembly.horizontalNormalizedSlopeFunction_eq_exactGlobalSlope
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    (assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta)
    (horizontalCenter : Point3)
    (hcenterHeight : horizontalCenter 2 = 0) :
    (fun t : ℝ =>
      pureWZ2HorizontalNormalizedSlope assembly.horizontalSource.geometrySlope
        assembly.horizontalSource.globalSlope
        assembly.horizontalSource.c assembly.horizontalSource.d
        assembly.horizontalSource.m horizontalCenter t) =
      assembly.exactGlobalSlope := by
  funext t
  rw [← assembly.globalSlope_eq_horizontalSource]
  exact assembly.horizontalNormalizedSlope_eq_exactGlobalSlope
    horizontalCenter hcenterHeight t

/-- Horizontal normalization at scale one and center zero is the original
centered triangular map. -/
@[simp] theorem pureWZ2Direct_horizontalNormalizedMap_one_zero
    (g : SlopeFunction) (c d m : ℝ) (center point : Point3) :
    pureWZ2HorizontalNormalizedMap g c d m center 0 1 point =
      anisotropicCenteredRescalingMap g c d m center point := by
  ext coordinate
  fin_cases coordinate <;>
    simp [pureWZ2HorizontalNormalizedMap, point3]

/-- Restricting the direct source grains and removing the null top face do
not change their chosen ambient slope representative. -/
@[simp] theorem PureWZ2DirectAnisotropicRetubingData.openSourceSlope_eq
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    {assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta}
    (data : PureWZ2DirectAnisotropicRetubingData assembly) :
    data.popular.openSourceGlobalGrains.slope =
      assembly.cfg.globalGrains.slope := by
  exact data.popular.source_global_slope_eq

/-- The exact slope appearing in the direct projection identity is the
interval-domain public slope already supplied by the Node-5 source package. -/
theorem PureWZ2DirectAnisotropicRetubingData.exactSlope_eq_public
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    {assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta}
    (data : PureWZ2DirectAnisotropicRetubingData assembly)
    (t : PureWZ2UnitInterval) :
    anisotropicRescaledSlopeWithShear assembly.globalSlope
        assembly.horizontalSource.c assembly.horizontalSource.d
        assembly.horizontalSource.m
        (assembly.horizontalSource.geometrySlope
          (assembly.horizontalSource.c +
            (assembly.horizontalSource.d - assembly.horizontalSource.c) / 2))
        t.1 =
      assembly.horizontalSource.f t := by
  rw [assembly.globalSlope_eq_horizontalSource]
  simpa [pureWZ2HorizontalNormalizedSlope] using
    assembly.horizontalSource.horizontalNormalizedSlope_eq
      (0 : Point3) (by simp) t

/-- The original source radius is no larger than the reciprocal-grid radius
of the exact triangular target. -/
theorem PureWZ2DirectSection6SourceAssembly.delta_le_directTargetDelta
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    (assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta) :
    delta ≤ anisotropicPaperAlignedScale delta
      assembly.horizontalSource.c assembly.horizontalSource.d := by
  have hlengthPos : 0 < assembly.horizontalSource.d -
      assembly.horizontalSource.c :=
    sub_pos.mpr assembly.horizontalSource.ordered
  have hrawPos : 0 < anisotropicPaperRawScale delta
      assembly.horizontalSource.c assembly.horizontalSource.d := by
    unfold anisotropicPaperRawScale
    exact div_pos (mul_pos (by norm_num) assembly.cfg.extremal.delta_pos)
      hlengthPos
  have hrawHalf : anisotropicPaperRawScale delta
      assembly.horizontalSource.c assembly.horizontalSource.d ≤ 1 / 2 := by
    have hlength : assembly.horizontalSource.d -
        assembly.horizontalSource.c = assembly.rho.1 / 100 := by
      rw [assembly.horizontalSource.length_eq, assembly.horizontalSource_scale]
    have hrawEq : anisotropicPaperRawScale delta
        assembly.horizontalSource.c assembly.horizontalSource.d =
      1600 * delta / assembly.rho.1 := by
      unfold anisotropicPaperRawScale
      rw [hlength]
      field_simp [show assembly.rho.1 ≠ 0 by
        exact ne_of_gt (assembly.cfg.extremal.delta_pos.trans_le
          assembly.rho.2.1)]
      ring
    rw [hrawEq, div_le_iff₀
      (assembly.cfg.extremal.delta_pos.trans_le assembly.rho.2.1)]
    have hfactor : 0 ≤ (1 / 2 : ℝ) - 1600 * assembly.rho.1 := by
      linarith [assembly.rho_tiny]
    nlinarith [assembly.delta_le_rho_sq,
      mul_nonneg
        (assembly.cfg.extremal.delta_pos.trans_le assembly.rho.2.1).le
        hfactor]
  have hrawTarget := anisotropicPaperRawScale_le_aligned hrawPos hrawHalf
  calc
    delta ≤ 16 * delta /
        (assembly.horizontalSource.d - assembly.horizontalSource.c) := by
      rw [le_div_iff₀ hlengthPos]
      have hlengthOne : assembly.horizontalSource.d -
          assembly.horizontalSource.c ≤ 1 := by
        rw [assembly.horizontalSource.length_eq, assembly.horizontalSource_scale]
        linarith [assembly.rho_tiny]
      nlinarith [assembly.cfg.extremal.delta_pos]
    _ = anisotropicPaperRawScale delta assembly.horizontalSource.c
        assembly.horizontalSource.d := rfl
    _ ≤ anisotropicPaperAlignedScale delta assembly.horizontalSource.c
        assembly.horizontalSource.d := hrawTarget

/-- Source global AD transfers to the exact direct triangular image with the
frozen globally smooth slope.  The combined-map transported slope agrees with
this witness on all of `ℝ`, so this bridge does not pass through an
interval-only extension equality. -/
theorem PureWZ2DirectAnisotropicRetubingData.exact_global_ad
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    {assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta}
    (data : PureWZ2DirectAnisotropicRetubingData assembly) :
    ∀ t : ℝ, ∀ ht : t ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (scalarProjection
          (globalGrainDirection
            (assembly.exactGlobalSlope t))
          (horizontalSlice data.raw.exactShading.union t))
        (anisotropicPaperAlignedScale delta
          assembly.horizontalSource.c assembly.horizontalSource.d)
        (1 - sigma)
        (Kakeya.realRpowENN delta (-assembly.technicalLoss)) := by
  let targetDelta := anisotropicPaperAlignedScale delta
    assembly.horizontalSource.c assembly.horizontalSource.d
  have htargetPos : 0 < targetDelta := by
    apply anisotropicPaperAlignedScale_pos
    · unfold anisotropicPaperRawScale
      exact div_pos (mul_pos (by norm_num) assembly.cfg.extremal.delta_pos)
        (sub_pos.mpr assembly.horizontalSource.ordered)
    · have hlength : assembly.horizontalSource.d -
          assembly.horizontalSource.c = assembly.rho.1 / 100 := by
        rw [assembly.horizontalSource.length_eq, assembly.horizontalSource_scale]
      have hrawEq : anisotropicPaperRawScale delta
          assembly.horizontalSource.c assembly.horizontalSource.d =
        1600 * delta / assembly.rho.1 := by
        unfold anisotropicPaperRawScale
        rw [hlength]
        field_simp [show assembly.rho.1 ≠ 0 by
          exact ne_of_gt (assembly.cfg.extremal.delta_pos.trans_le
            assembly.rho.2.1)]
        ring
      rw [hrawEq, div_le_iff₀
        (assembly.cfg.extremal.delta_pos.trans_le assembly.rho.2.1)]
      have hfactor : 0 ≤ (1 / 2 : ℝ) - 1600 * assembly.rho.1 := by
        linarith [assembly.rho_tiny]
      nlinarith [assembly.delta_le_rho_sq,
        mul_nonneg
          (assembly.cfg.extremal.delta_pos.trans_le assembly.rho.2.1).le
          hfactor]
  have hexact := pureWZ2_horizontalNormalized_exact_global_ad
    data.popular.openSourceGlobalGrains
    (pureWZ2DirectGeometrySlope assembly.horizontalSource)
    (c := assembly.horizontalSource.c)
    (d := assembly.horizontalSource.d)
    (m := assembly.horizontalSource.m) (lambda := (1 : ℝ))
    assembly.horizontalSource.ordered
    assembly.horizontalSource.slopeScale_pos (by norm_num)
    data.interval_sub_unit
    (pureWZ2DirectAnisotropicCenter data.popular) (0 : Point3)
    (by simp)
    (by simpa [targetDelta] using assembly.delta_le_directTargetDelta)
    htargetPos
  intro t ht
  have h := hexact t ht
  rw [data.raw.exactShading_union]
  rw [data.openSourceSlope_eq] at h
  let sourceHeight : ℝ := assembly.horizontalSource.c +
    (assembly.horizontalSource.d - assembly.horizontalSource.c) / 2 * (t + 1)
  have hsourceHeight : sourceHeight ∈ Set.Icc
      assembly.horizontalSource.c assembly.horizontalSource.d := by
    dsimp only [sourceHeight]
    have hlength : 0 < assembly.horizontalSource.d -
        assembly.horizontalSource.c :=
      sub_pos.mpr assembly.horizontalSource.ordered
    constructor
    · have hnonnegative : 0 ≤ t + 1 := by linarith [ht.1]
      have : 0 ≤ (assembly.horizontalSource.d -
          assembly.horizontalSource.c) / 2 * (t + 1) := by positivity
      linarith
    · have htwo : t + 1 ≤ 2 := by linarith [ht.2]
      have hupper : (assembly.horizontalSource.d -
          assembly.horizontalSource.c) / 2 * (t + 1) ≤
          assembly.horizontalSource.d - assembly.horizontalSource.c := by
        calc
          _ ≤ (assembly.horizontalSource.d -
              assembly.horizontalSource.c) / 2 * 2 := by gcongr
          _ = assembly.horizontalSource.d -
              assembly.horizontalSource.c := by ring
      linarith
  have hsourceHeightUnit : sourceHeight ∈ Set.Icc (-1 : ℝ) 1 :=
    data.interval_sub_unit hsourceHeight
  have hslope :
      pureWZ2HorizontalNormalizedSlope
          (pureWZ2DirectGeometrySlope assembly.horizontalSource)
          assembly.cfg.globalGrains.slope assembly.horizontalSource.c
          assembly.horizontalSource.d assembly.horizontalSource.m
          (0 : Point3) t = assembly.exactGlobalSlope t := by
    calc
      _ = pureWZ2HorizontalNormalizedSlope
          (pureWZ2DirectGeometrySlope assembly.horizontalSource)
          assembly.globalSlope assembly.horizontalSource.c
          assembly.horizontalSource.d assembly.horizontalSource.m
          (0 : Point3) t := by
            unfold pureWZ2HorizontalNormalizedSlope
              anisotropicRescaledSlopeWithShear
            simp only [PiLp.zero_apply, zero_add]
            rw [← assembly.globalSlope_eq_source _ (by
              simpa only [sourceHeight] using hsourceHeightUnit)]
      _ = assembly.exactGlobalSlope t :=
        assembly.horizontalNormalizedSlope_eq_exactGlobalSlope
          (0 : Point3) (by simp) t
  rw [hslope] at h
  simpa only [targetDelta,
    pureWZ2Direct_horizontalNormalizedMap_one_zero, pureWZ2DirectGeometrySlope]
    using h

/-- Interval-domain compatibility form of `exact_global_ad`.  This is now a
corollary of the global frozen-slope statement rather than its source. -/
theorem PureWZ2DirectAnisotropicRetubingData.exact_public_global_ad
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    {assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta}
    (data : PureWZ2DirectAnisotropicRetubingData assembly) :
    ∀ t : ℝ, ∀ ht : t ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (scalarProjection
          (globalGrainDirection
            (assembly.horizontalSource.f ⟨t, ht⟩))
          (horizontalSlice data.raw.exactShading.union t))
        (anisotropicPaperAlignedScale delta
          assembly.horizontalSource.c assembly.horizontalSource.d)
        (1 - sigma)
        (Kakeya.realRpowENN delta (-assembly.technicalLoss)) := by
  intro t ht
  simpa only [assembly.exactGlobalSlope_onUnitInterval ⟨t, ht⟩] using
    data.exact_global_ad t ht

/-- Exact global AD survives any later tube-index restriction of the direct
exact image.  This is the form consumed by the synchronized joint family. -/
theorem PureWZ2DirectAnisotropicRetubingData.exact_public_global_ad_subfamily
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    {assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta}
    (data : PureWZ2DirectAnisotropicRetubingData assembly)
    (selected : Kakeya.Streamlined.TubeSubfamily
      (anisotropicPaperTargetFamily data.popular.family
        (pureWZ2DirectGeometrySlope assembly.horizontalSource)
        assembly.horizontalSource.c assembly.horizontalSource.d
        assembly.horizontalSource.m
        (pureWZ2DirectAnisotropicCenter data.popular)
        (anisotropicPaperAlignedScale delta assembly.horizontalSource.c
          assembly.horizontalSource.d)
        assembly.horizontalSource.ordered
        assembly.horizontalSource.slopeScale_pos)) :
    ∀ t : ℝ, ∀ ht : t ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (scalarProjection
          (globalGrainDirection
            (assembly.horizontalSource.f ⟨t, ht⟩))
          (horizontalSlice
            (restrictPaperShading selected data.raw.exactShading).union t))
        (anisotropicPaperAlignedScale delta
          assembly.horizontalSource.c assembly.horizontalSource.d)
        (1 - sigma)
        (Kakeya.realRpowENN delta (-assembly.technicalLoss)) := by
  intro t ht
  exact (data.exact_public_global_ad t ht).weaken_subset <| by
    apply Set.image_mono
    intro point hpoint
    exact ⟨restrictPaperShading_union_subset selected data.raw.exactShading
      hpoint.1, hpoint.2⟩

/-- The same restricted-family AD statement with the retained globally smooth
exact slope.  This is the source form needed before a final height-changing
dilation. -/
theorem PureWZ2DirectAnisotropicRetubingData.exact_global_ad_subfamily
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    {assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta}
    (data : PureWZ2DirectAnisotropicRetubingData assembly)
    (selected : Kakeya.Streamlined.TubeSubfamily
      (anisotropicPaperTargetFamily data.popular.family
        (pureWZ2DirectGeometrySlope assembly.horizontalSource)
        assembly.horizontalSource.c assembly.horizontalSource.d
        assembly.horizontalSource.m
        (pureWZ2DirectAnisotropicCenter data.popular)
        (anisotropicPaperAlignedScale delta assembly.horizontalSource.c
          assembly.horizontalSource.d)
        assembly.horizontalSource.ordered
        assembly.horizontalSource.slopeScale_pos)) :
    ∀ t : ℝ, ∀ ht : t ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (scalarProjection
          (globalGrainDirection (assembly.exactGlobalSlope t))
          (horizontalSlice
            (restrictPaperShading selected data.raw.exactShading).union t))
        (anisotropicPaperAlignedScale delta
          assembly.horizontalSource.c assembly.horizontalSource.d)
        (1 - sigma)
        (Kakeya.realRpowENN delta (-assembly.technicalLoss)) := by
  intro t ht
  exact (data.exact_global_ad t ht).weaken_subset <| by
    apply Set.image_mono
    intro point hpoint
    exact ⟨restrictPaperShading_union_subset selected data.raw.exactShading
      hpoint.1, hpoint.2⟩

/-- After the final line-class dilation, the exact transported slope remains
globally smooth and nonsingular.  No new extension or endpoint argument is
needed. -/
theorem PureWZ2DirectSection6SourceAssembly.finalExactSlope_nonsingular
    {logExponent : ℕ}
    {sigma epsilon delta lambda : ℝ}
    (assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta)
    (hlambda : 1 ≤ lambda) :
    (pureWZ2LineClassNormalizedSlope
      assembly.exactGlobalSlope 0 lambda).IsNonsingular :=
  pureWZ2LineClassNormalizedSlope_nonsingular
    assembly.exactGlobalSlope assembly.exactGlobalSlope_nonsingular hlambda

/-- Interval-domain corollary of the final exact nonsingularity result. -/
theorem PureWZ2DirectSection6SourceAssembly.finalExactPublicSlope_nonsingular
    {logExponent : ℕ}
    {sigma epsilon delta lambda : ℝ}
    (assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta)
    (hlambda : 1 ≤ lambda) :
    PureWZ2C2SlopeIsNonsingular
      (pureWZ2LineClassNormalizedSlope
        assembly.exactGlobalSlope 0 lambda).onUnitInterval :=
  SlopeFunction.nonsingular_onUnitInterval _
    (assembly.finalExactSlope_nonsingular hlambda)

/-- Exact global AD on the final line-class image of any synchronized direct
subfamily.  The slope in the conclusion is the same globally smooth exact
slope used for the nonsingularity proof above. -/
theorem PureWZ2DirectAnisotropicRetubingData.final_exact_global_ad_subfamily
    {logExponent : ℕ}
    {sigma epsilon delta targetDelta lambda : ℝ}
    {assembly : PureWZ2DirectSection6SourceAssembly
      logExponent sigma epsilon delta}
    (data : PureWZ2DirectAnisotropicRetubingData assembly)
    (selected : Kakeya.Streamlined.TubeSubfamily
      (anisotropicPaperTargetFamily data.popular.family
        (pureWZ2DirectGeometrySlope assembly.horizontalSource)
        assembly.horizontalSource.c assembly.horizontalSource.d
        assembly.horizontalSource.m
        (pureWZ2DirectAnisotropicCenter data.popular)
        (anisotropicPaperAlignedScale delta assembly.horizontalSource.c
          assembly.horizontalSource.d)
        assembly.horizontalSource.ordered
        assembly.horizontalSource.slopeScale_pos))
    (center : Point3) (hcenterHeight : center 2 = 0)
    (hlambda : 1 ≤ lambda)
    (hbase : lambda *
        anisotropicPaperAlignedScale delta assembly.horizontalSource.c
          assembly.horizontalSource.d ≤ targetDelta)
    (htargetDelta : 0 < targetDelta) :
    ∀ t : ℝ, ∀ ht : t ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (scalarProjection
          (globalGrainDirection
            (pureWZ2LineClassNormalizedSlope
              assembly.exactGlobalSlope (center 2) lambda t))
          (horizontalSlice
            (pureWZ2LineClassNormalizationMap center lambda ''
              (restrictPaperShading selected data.raw.exactShading).union) t))
        targetDelta (1 - sigma)
        (Kakeya.realRpowENN delta (-assembly.technicalLoss)) := by
  have hlambdaPos : 0 < lambda := lt_of_lt_of_le (by norm_num) hlambda
  apply pureWZ2_lineClassNormalization_exact_global_ad_of_slope
    assembly.exactGlobalSlope
    (data.exact_global_ad_subfamily selected) center hlambdaPos
    hcenterHeight
  · intro t ht
    constructor
    · apply (le_div_iff₀ hlambdaPos).2
      nlinarith [ht.1]
    · apply (div_le_iff₀ hlambdaPos).2
      nlinarith [ht.2]
  · exact hbase
  · exact htargetDelta

end Kakeya.Assouad

end
