/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Mathlib.Analysis.Trigonometric
public import Kakeya.Mathlib.MeasureTheory.Action
public import Kakeya.Mathlib.MeasureTheory.ProdBox
public import Kakeya.Mathlib.Topology.CoveringNumber
public import Kakeya.Mathlib.Topology.Metric
public import Kakeya.Tube.Basic
public import Kakeya.Tube.CardEssentiallyDistinct
public import Kakeya.Tube.IntersectionVolume

/-!
# Essentially distinct thin tubes inside the dilate of a fat tube

This file collects the geometry of the dilate `C · V` of a `ρ`-tube `V` and the packing count
that bounds the number of pairwise essentially distinct `C⁻¹ρ`-tubes it can contain.  The count
is the combinatorial input of `Tube.exists_comparableReplacement`
(`Kakeya/Tube/Rescale.lean`), and it splits into two regimes according to whether the dilate is
thin (`ρ ≤ 1 / (4 C_n)`) or fat.

## Blueprint correspondence

There are two blueprint sources.  Everything up to and including
`Tube.essDistinctTubesInFatDilate` comes from `GWZAdapted/section8_genkf.tex`; the plank-case
group in the final section of the file comes from `GWZAdapted/section8_rescaling.tex`.

* `Tube.x_mem_carrier`, `Tube.y_mem_carrier` ↔ `lem:tubeCoreEndpointsMem`;
* `Tube.x_eq_center_sub`, `Tube.y_eq_center_add` ↔ `lem:tubeCoreFromCentre`;
* `Metric.image_cthickening_homothety` ↔ `lem:cthickeningHomothety`;
* `Tube.dilate_carrier_eq_cthickening` ↔ `lem:tubeDilateCthickening`;
* `Tube.subset_dilate` ↔ `lem:tubeSubsetOwnDilate`;
* `Tube.abs_inner_and_perp_le_of_mem_dilate` ↔ `lem:dilatePointBoundsGeneral`;
* `Tube.norm_perp_direction_le_of_chord` ↔ `lem:chordAngleBound`;
* `Tube.dist_le_of_mem_dilate_of_mem_dilate` ↔ `lem:dilatePointsDist`;
* `Tube.norm_perp_sub_center_le_of_mem_dilate` ↔ `lem:dilatePointPerpDrift`;
* `Tube.abs_inner_sub_center_le_of_pinned` ↔ `lem:thinTubeInFatDilateLongitudinal`;
* `Tube.norm_perp_sub_center_le_of_pinned_of_le_one`
  ↔ `lem:thinTubeInFatDilateTransverseSmallAngle`;
* `Tube.norm_perp_sub_center_le_of_pinned_of_one_lt`
  ↔ `lem:thinTubeInFatDilateTransverseLargeAngle`;
* `Tube.norm_perp_sub_center_le_of_pinned` ↔ `lem:thinTubeInFatDilateTransverse`;
* `Tube.subset_dilate_of_norm_perp_direction_le` ↔ `lem:thinTubeInFatDilate`;
* `Tube.inner_and_perp_le_of_mem_dilate` ↔ `lem:dilatePointBounds`;
* `Tube.parameters_mem_of_subset_dilate` ↔ `lem:endpointRegionMem`;
* `Metric.cthickening_segment_subset_cthickening_segment` ↔ `lem:segmentEndpointCthickening`;
* `segment_homothety_subset_inter_translate` ↔ `lem:slideSegmentHomothety`;
* `Tube.cthickening_subset_of_subset_segment` ↔ `lem:tubeSlideCoreSubsetSelf`;
* `Tube.cthickening_subset_of_subset_translate_segment` ↔ `lem:tubeSlideCoreSubsetSlid`;
* `Tube.cthickening_slideCore_subset_inter` ↔ `lem:tubeSlideCommonCore`;
* `Tube.volume_cthickening_slideCore` ↔ `lem:tubeSlideCommonCoreVolume`;
* `Tube.volume_carrier_eq_volume_carrier` ↔ `lem:tubeVolumeIndependentOfPosition`;
* `Tube.volume_pos_and_lt_top` ↔ `lem:tubeVolumePosLtTop`;
* `Tube.sum_volume_carrier_eq_card_mul` ↔ `lem:tubeFamilySumVolume`;
* `Tube.mul_sum_volume_le_iff_mul_card_le` ↔ `lem:tubeShareVolumeCard`;
* `Tube.three_quarters_le_one_sub_cstar_pow` ↔ `lem:oneMinusQuarterPow`;
* `not_isEssentiallyDistinct_of_three_quarters_le` ↔ `lem:notEssDistinctOfThreeQuarters`;
* `Tube.not_essDistinct_of_axial_slide` ↔ `lem:tubeAxialSlideOverlap`;
* `Tube.axialSeparation.kappa` ↔ `def:essDistinctTubeAxialSeparationConstant`;
* `Tube.axialSeparation.coe_kappa` ↔ `lem:kappaValue`;
* `Tube.finrank_perpSpace` ↔ `lem:perpSpaceFinrank`;
* `Tube.volume_closedBall_perpSpace` ↔ `lem:perpSpaceBallVolume`;
* `Tube.parameterMap` ↔ `def:tubeParameterMap`;
* `Tube.card_le_of_separated_parameterSpace` ↔ `lem:parameterSpaceMeasure`;
* `Tube.abs_inner_sub_le_norm_perp_sub` ↔ `lem:tubeDirectionAxialComparison`;
* `Tube.axial_separation_of_essDistinct` ↔ `lem:essDistinctTubeAxialSeparation`;
* `Tube.parameterRegion.C` ↔ `def:endpointRegionMeasureConstant`;
* `Tube.parameterRegion.volume_formula_eq` ↔ `lem:endpointRegionConstantArith`;
* `Submodule.norm_orthogonalProjectionOnto_perp_span_singleton` ↔ `lem:perpProjectionNorm`;
* `Tube.parameterMap_mem_parameterRegion` ↔ `lem:parameterMapMemRegion`;
* `Tube.volume_parameterRegion` ↔ `lem:endpointRegionVolume`;
* `Tube.volume_parameterRegion_le` ↔ `lem:endpointRegionMeasure`;
* `Metric.volume_cthickening_box_le` ↔ `lem:boxThickeningVolume`;
* `Tube.exists_orientedFamily` ↔ `lem:tubeReverseOrientation`;
* `Tube.max_coord_dist_le_dist` and `Tube.lt_dist_parameterMap_of_max_lt`
  ↔ the two items (a), (b) of `lem:parameterSpaceMaxNormSeparation`;
* `Tube.essDistinctTubesInThinDilate` ↔ `lem:essDistinctTubesInThinDilate`;
* `Tube.essDistinctTubesInFatDilate` ↔ `lem:essDistinctTubesInFatDilate`.

`Tube.finrank_parameterSpace` has no blueprint counterpart of its own: it is step (4) of the
proof of `lem:essDistinctTubesInThinDilate`, made a declaration because the reduction to
`Tube.finrank_perpSpace` through the two nested `WithLp 2` products is not a `simp` call.

From `GWZAdapted/section8_rescaling.tex`, the plank-case group:

* `Kakeya.Tube.exists_axis_repr_of_mem_dilate` ↔ `lem:ml1bootDilateAxisRepr`;
* `Kakeya.Tube.exists_axis_repr_sub_midpoint_of_mem_dilate`
  ↔ `lem:ml1bootCentreRelativeAxisRepr`;
* `Kakeya.inner_sq_add_norm_transverse_sq_eq` ↔ `lem:unitVectorTiltPythagoras`;
* `Kakeya.Tube.norm_chord_transverse_le_of_endpoints_mem_dilate` and
  `Kakeya.Tube.one_sub_abs_inner_chord_le_of_endpoints_mem_dilate`
  ↔ the two conclusions of `lem:ml1bootUnitChordTilt`;
* `Kakeya.norm_smul_add_sub_smul_le` ↔ `lem:ml1bootSignedDisplacement`;
* `Kakeya.Tube.subset_dilate_rescale_of_subset_dilate`
  ↔ `lem:ml1bootEnlargementPlankCore`.

The centred box `Metric.prodBox` and its volume now live in
`Kakeya/Mathlib/MeasureTheory/ProdBox.lean`.

## Notation and conventions

Throughout, `C_n = Kakeya.Tube.tubeOverlapCoreClose.C n` is the *linear* dilation constant of
`Kakeya.Tube.tubeOverlapCoreClose`, `c_* = 1 / (4 n)` is the endpoint separation constant of
blueprint `def:essDistinctTubeEndpointSeparation_constant` (it has no Lean name of its own and
is written out at each occurrence), and for `d : E` the perpendicular component with respect to
a unit vector `e` is written `d - ⟪e, d⟫ • e`.

The file carries two namespaces, and both are needed.  The `section8_genkf.tex` material lives
in the root namespace `Tube` of the structure `Tube`, where the dilate has to be written out as
`Kakeya.Tube.dilate`; the `section8_rescaling.tex` group at the end lives in `Kakeya.Tube`,
beside `Kakeya.Tube.dilate` itself, where it is written simply `dilate`, with its two
vector-level members in `Kakeya`.  The perpendicular component is written with the unit vector
as the *first* argument of `inner` throughout, matching `d - inner ℝ e d • e` and
`InnerProductGeometry.norm_sub_inner_smul_eq_sin_angle`.

Two deliberate deviations from the blueprint wording are documented at the declarations
concerned: `Tube.card_le_of_separated_parameterSpace` is stated for an arbitrary
finite-dimensional real inner product space rather than for a chosen isometric copy of
`ℝ ^ (2n-1)`, and the blueprint's packing constant `C_{lem:separatedSetCardBound}(d) = 2^d/ω_d`
is written as the inverse of `Metric.coveringNumber_mul_pow_le_volume_cthickening.C d`, which
is the same number.
-/

@[expose] public section

open MeasureTheory Metric Set

namespace Tube

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {ρ : NNReal}

/-! ### The core of a tube -/

/-- **The starting endpoint of the core lies in the tube** (blueprint
`lem:tubeCoreEndpointsMem`).  A `δ`-tube is the union of the closed `δ`-balls centred at the
points of its core, and `T.x` is one of those centres.

Blueprint `note:tubeEndpointMembership` records why this one-line fact is a declaration of its
own: three separate arguments below need it. -/
theorem x_mem_carrier {δ : NNReal} (T : Tube δ E) : T.x ∈ T.carrier := by
  rw [T.carrier_eq]
  exact Set.mem_iUnion₂.mpr
    ⟨T.x, left_mem_segment ℝ T.x T.y, Metric.mem_closedBall_self δ.coe_nonneg⟩

/-- **The final endpoint of the core lies in the tube** (blueprint
`lem:tubeCoreEndpointsMem`). -/
theorem y_mem_carrier {δ : NNReal} (T : Tube δ E) : T.y ∈ T.carrier := by
  rw [T.carrier_eq]
  exact Set.mem_iUnion₂.mpr
    ⟨T.y, right_mem_segment ℝ T.x T.y, Metric.mem_closedBall_self δ.coe_nonneg⟩

/-- **The core of a tube, read off from its centre** (blueprint `lem:tubeCoreFromCentre`): the
core is the segment of length one centred at `T.center` in the direction `T.direction`.  This
is an identity in the vector space; `‖T.direction‖ = 1` is needed only for the word "length". -/
theorem x_eq_center_sub {δ : NNReal} (T : Tube δ E) :
    T.x = T.center - (1 / 2 : ℝ) • T.direction := by
  simp [Tube.center, Tube.direction, midpoint_eq_smul_add]
  module

/-- **The core of a tube, read off from its centre** (blueprint
`lem:tubeCoreFromCentre`). -/
theorem y_eq_center_add {δ : NNReal} (T : Tube δ E) :
    T.y = T.center + (1 / 2 : ℝ) • T.direction := by
  simp [Tube.center, Tube.direction, midpoint_eq_smul_add]
  module

/-! ### Dilates -/

/-- **A homothety carries a closed neighbourhood to a closed neighbourhood** (blueprint
`lem:cthickeningHomothety`).  The homothety of ratio `c > 0` scales all distances by `c`, hence
scales the radius of a closed neighbourhood by `c`. -/
theorem _root_.Metric.image_cthickening_homothety (m : E) {c : ℝ} (hc : 0 < c) {r : ℝ}
    (hr : 0 ≤ r) (A : Set E) :
    AffineMap.homothety m c '' cthickening r A
      = cthickening (c * r) (AffineMap.homothety m c '' A) := by
  let h : E → E := AffineMap.homothety m c
  change h '' cthickening r A = cthickening (c * r) (h '' A)
  have hcne : c ≠ 0 := ne_of_gt hc
  have hc0 : 0 ≤ c := le_of_lt hc
  have hci_pos : 0 < c⁻¹ := inv_pos.mpr hc
  have hcr0 : 0 ≤ c * r := mul_nonneg hc0 hr
  have hdist : ∀ {a : ℝ} (ha : 0 < a) (z w : E),
      dist (AffineMap.homothety m a z) (AffineMap.homothety m a w) = a * dist z w := by
    intro a ha z w
    rw [dist_eq_norm, dist_eq_norm]
    have hsub : AffineMap.homothety m a z - AffineMap.homothety m a w = a • (z - w) := by
      simp [AffineMap.homothety_apply, smul_sub]
    rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
  have hed : ∀ {a : ℝ} (ha : 0 < a) (z w : E),
      edist (AffineMap.homothety m a z) (AffineMap.homothety m a w)
        = ENNReal.ofReal a * edist z w := by
    intro a ha z w
    rw [edist_dist, edist_dist, hdist ha, ENNReal.ofReal_mul (le_of_lt ha)]
  have hinf : ∀ {a : ℝ} (ha : 0 < a) (B : Set E) (x : E),
      infEDist (AffineMap.homothety m a x) (AffineMap.homothety m a '' B)
        = ENNReal.ofReal a * infEDist x B := by
    intro a ha B x
    rw [infEDist, infEDist, iInf_image]
    calc
      (⨅ y ∈ B, edist (AffineMap.homothety m a x) (AffineMap.homothety m a y))
          = ⨅ y ∈ B, ENNReal.ofReal a * edist x y := by
            apply biInf_congr
            intro y hy
            exact hed ha x y
      _ = ENNReal.ofReal a * (⨅ y ∈ B, edist x y) := by
            simp_rw [ENNReal.mul_iInf_of_ne (ENNReal.ofReal_pos.mpr ha).ne' ENNReal.ofReal_ne_top]
  have hinv : ∀ y : E, h (AffineMap.homothety m (c⁻¹) y) = y := by
    intro y
    dsimp [h]
    rw [← AffineMap.homothety_mul_apply m c (c⁻¹) y, mul_inv_cancel₀ hcne]
    simp
  have hinv_on : ∀ a : E, AffineMap.homothety m (c⁻¹) (h a) = a := by
    intro a
    dsimp [h]
    rw [← AffineMap.homothety_mul_apply m (c⁻¹) c a, inv_mul_cancel₀ hcne]
    simp
  have himage_inv : AffineMap.homothety m (c⁻¹) '' (h '' A) = A := by
    ext z
    constructor
    · rintro ⟨w, ⟨a, ha, hw⟩, hz⟩
      rw [← hw] at hz
      rw [← hz]
      rw [hinv_on a]
      exact ha
    · intro hz
      refine ⟨h z, ?_, ?_⟩
      · exact ⟨z, hz, rfl⟩
      · exact hinv_on z
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Metric.mem_cthickening_iff]
    rw [hinf hc A x]
    calc
      ENNReal.ofReal c * infEDist x A ≤ ENNReal.ofReal c * ENNReal.ofReal r := by
        exact mul_le_mul_right (by simpa [Metric.mem_cthickening_iff] using hx) (ENNReal.ofReal c)
      _ = ENNReal.ofReal (c * r) := (ENNReal.ofReal_mul hc0).symm
  · intro hy
    refine ⟨AffineMap.homothety m (c⁻¹) y, ?_, hinv y⟩
    rw [Metric.mem_cthickening_iff]
    rw [← himage_inv]
    rw [hinf hci_pos (h '' A) y]
    calc
      ENNReal.ofReal (c⁻¹) * infEDist y (h '' A)
          ≤ ENNReal.ofReal (c⁻¹) * ENNReal.ofReal (c * r) := by
        exact mul_le_mul_right
          (by simpa [Metric.mem_cthickening_iff] using hy) (ENNReal.ofReal (c⁻¹))
      _ = ENNReal.ofReal (c⁻¹ * (c * r)) := (ENNReal.ofReal_mul (le_of_lt hci_pos)).symm
      _ = ENNReal.ofReal r := by
        congr 1
        rw [← mul_assoc, inv_mul_cancel₀ hcne, one_mul]

/-- **The dilate of a tube is a thickened long segment** (blueprint
`lem:tubeDilateCthickening`): `c · T` is the closed `c δ`-neighbourhood of the segment of length
`c` through the centre of `T` in the direction of `T`. -/
theorem dilate_carrier_eq_cthickening {δ : NNReal} (T : Tube δ E) {c : ℝ} (hc : 0 < c) :
    (Kakeya.Tube.dilate T c).carrier
      = cthickening (c * (δ : ℝ))
          (segment ℝ (T.center - (c / 2) • T.direction) (T.center + (c / 2) • T.direction)) := by
  have hcarrier :
      (Kakeya.Tube.dilate T c).carrier = (AffineMap.homothety T.center c) '' T.carrier := by
    rw [Kakeya.Tube.dilate]
    simp
  rw [hcarrier, T.carrier_eq_cthickening]
  rw [Metric.image_cthickening_homothety T.center hc (NNReal.coe_nonneg δ)]
  congr 1
  rw [image_segment]
  congr 1
  · rw [T.x_eq_center_sub, AffineMap.homothety_apply]
    simp only [vsub_eq_sub, vadd_eq_add]
    module
  · rw [T.y_eq_center_add, AffineMap.homothety_apply]
    simp only [vsub_eq_sub, vadd_eq_add]
    module

/-- **A tube lies in its own dilate** (blueprint `lem:tubeSubsetOwnDilate`). -/
theorem subset_dilate {δ : NNReal} (T : Tube δ E) {c : ℝ} (hc : 1 ≤ c) :
    T.carrier ⊆ (Kakeya.Tube.dilate T c).carrier := by
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hcne : c ≠ 0 := hc0.ne'
  rw [T.carrier_eq_cthickening, dilate_carrier_eq_cthickening T hc0]
  have hδ : (δ : ℝ) ≤ c * (δ : ℝ) := by
    simpa using mul_le_mul_of_nonneg_right hc (NNReal.coe_nonneg δ)
  have hseg : segment ℝ T.x T.y
      ⊆ segment ℝ (T.center - (c / 2) • T.direction) (T.center + (c / 2) • T.direction) := by
    refine Convex.segment_subset (convex_segment _ _) ?_ ?_
    · let t : ℝ := (c - 1) / (2 * c)
      have ht : t ∈ Icc (0 : ℝ) 1 := by
        constructor
        · dsimp [t]
          exact div_nonneg (sub_nonneg.mpr hc) (mul_pos (by norm_num) hc0).le
        · dsimp [t]
          rw [div_le_iff₀ (mul_pos (by norm_num) hc0)]
          nlinarith [hc]
      have hx : AffineMap.lineMap (T.center - (c / 2) • T.direction)
          (T.center + (c / 2) • T.direction) t = T.x := by
        rw [x_eq_center_sub T]
        set ctr : E := T.center with hctr
        set dir : E := T.direction with hdir
        rw [AffineMap.lineMap_apply_module]
        have hcombo : ∀ u : ℝ,
            (1 - u) • (ctr - (c / 2) • dir) + u • (ctr + (c / 2) • dir)
              = ctr + ((2 * u - 1) * (c / 2)) • dir := by
          intro u
          module
        rw [hcombo t]
        have hscalar : (2 * t - 1) * (c / 2) = -1 / 2 := by
          dsimp [t]
          field_simp [hcne]
          ring
        rw [hscalar]
        module
      rw [← hx]
      exact lineMap_mem_segment ℝ _ _ ht
    · let t : ℝ := (c + 1) / (2 * c)
      have ht : t ∈ Icc (0 : ℝ) 1 := by
        constructor
        · dsimp [t]
          exact div_nonneg (by linarith) (mul_pos (by norm_num) hc0).le
        · dsimp [t]
          rw [div_le_iff₀ (mul_pos (by norm_num) hc0)]
          nlinarith [hc]
      have hy : AffineMap.lineMap (T.center - (c / 2) • T.direction)
          (T.center + (c / 2) • T.direction) t = T.y := by
        rw [y_eq_center_add T]
        set ctr : E := T.center with hctr
        set dir : E := T.direction with hdir
        rw [AffineMap.lineMap_apply_module]
        have hcombo : ∀ u : ℝ,
            (1 - u) • (ctr - (c / 2) • dir) + u • (ctr + (c / 2) • dir)
              = ctr + ((2 * u - 1) * (c / 2)) • dir := by
          intro u
          module
        rw [hcombo t]
        have hscalar : (2 * t - 1) * (c / 2) = 1 / 2 := by
          dsimp [t]
          field_simp [hcne]
          ring
        rw [hscalar]
      rw [← hy]
      exact lineMap_mem_segment ℝ _ _ ht
  exact (Metric.cthickening_subset_of_subset (δ : ℝ) hseg).trans
    (Metric.cthickening_mono hδ _)

/-- **A tube is no bigger than any of its dilates** (blueprint
`lem:ml1bootTubeSubsetDilate`): the volume half of `Tube.subset_dilate`, obtained from it by
monotonicity of Lebesgue measure.

It is consumed at `c = 2` by `Kakeya.ml1Boot.volume_plankTube_le`, and the containment itself
is what the first half of `Kakeya.ml1Boot.exists_dilate_testBody` needs. -/
theorem volume_le_volume_dilate {δ : NNReal} (T : Tube δ E) {c : ℝ} (hc : 1 ≤ c) :
    volume T.carrier ≤ volume (Kakeya.Tube.dilate T c).carrier := by
  exact measure_mono (subset_dilate T hc)

/-- **A point of a dilate at an arbitrary ratio** (blueprint `lem:dilatePointBoundsGeneral`).

A point of `c · T` is within `c / 2 + c δ` of the centre of `T` along the axis of `T`, and
within `c δ` of it in the transverse directions, for every ratio `c > 0`.  The ratio is left
free because the consumers need it at `c = 1` and `c = 2`, where the `C_n`-specific
`Tube.inner_and_perp_le_of_mem_dilate` cannot be cited. -/
theorem abs_inner_and_perp_le_of_mem_dilate {δ : NNReal} (T : Tube δ E) {c : ℝ} (hc : 0 < c)
    {z : E} (hz : z ∈ (Kakeya.Tube.dilate T c).carrier) :
    |inner ℝ (z - T.center) T.direction| ≤ c / 2 + c * (δ : ℝ) ∧
      ‖z - T.center - inner ℝ T.direction (z - T.center) • T.direction‖ ≤ c * (δ : ℝ) := by
  have hcnonneg : 0 ≤ c := le_of_lt hc
  have hδ0 : 0 ≤ (δ : ℝ) := NNReal.coe_nonneg δ
  have hcr : 0 ≤ c * (δ : ℝ) := mul_nonneg hcnonneg hδ0
  have hz' : z ∈ cthickening (c * (δ : ℝ))
      (segment ℝ (T.center - (c / 2) • T.direction) (T.center + (c / 2) • T.direction)) := by
    rw [dilate_carrier_eq_cthickening T hc] at hz
    exact hz
  have hz'' : z ∈ ⋃ x ∈ segment ℝ (T.center - (c / 2) • T.direction)
      (T.center + (c / 2) • T.direction), closedBall x (c * (δ : ℝ)) := by
    rwa [← isClosed_segment.cthickening_eq_biUnion_closedBall hcr]
  rw [Set.mem_iUnion₂] at hz''
  rcases hz'' with ⟨w, hw, hzw⟩
  rw [Metric.mem_closedBall] at hzw
  rcases (segment_eq_image_lineMap ℝ (T.center - (c / 2) • T.direction)
      (T.center + (c / 2) • T.direction)).symm ▸ hw with ⟨s, hs, hw_eq⟩
  let t : ℝ := (2 * s - 1) * (c / 2)
  have hw_eq' : w = T.center + t • T.direction := by
    rw [← hw_eq]
    rw [AffineMap.lineMap_apply_module]
    dsimp [t]
    module
  have hs0 : 0 ≤ s := hs.1
  have hs1 : s ≤ 1 := hs.2
  have h2s : -1 ≤ 2 * s - 1 ∧ 2 * s - 1 ≤ 1 := by
    constructor <;> linarith
  have hc2 : 0 ≤ c / 2 := by positivity
  have ht : |t| ≤ c / 2 := by
    dsimp [t]
    calc
      |(2 * s - 1) * (c / 2)| = |2 * s - 1| * |c / 2| := abs_mul _ _
      _ = |2 * s - 1| * (c / 2) := by rw [abs_of_nonneg hc2]
      _ ≤ 1 * (c / 2) := mul_le_mul_of_nonneg_right (abs_le.mpr h2s) hc2
      _ = c / 2 := by ring
  have he : (inner ℝ T.direction T.direction : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, T.norm_direction]; norm_num
  have hz_sub : z - T.center = (z - w) + t • T.direction := by
    rw [hw_eq']
    abel
  have hz_inner : inner ℝ T.direction (z - T.center) = inner ℝ T.direction (z - w) + t := by
    rw [hz_sub]
    rw [inner_add_right, inner_smul_right, he]
    ring
  have hnorm_zw : ‖z - w‖ ≤ c * (δ : ℝ) := by
    simpa [dist_eq_norm] using hzw
  have hinner_zw : |inner ℝ T.direction (z - w)| ≤ c * (δ : ℝ) := by
    calc
      |inner ℝ T.direction (z - w)| ≤ ‖T.direction‖ * ‖z - w‖ :=
        abs_real_inner_le_norm T.direction (z - w)
      _ = ‖z - w‖ := by rw [T.norm_direction]; ring
      _ ≤ c * (δ : ℝ) := hnorm_zw
  have haxial : |inner ℝ (z - T.center) T.direction| ≤ c / 2 + c * (δ : ℝ) := by
    rw [real_inner_comm]
    rw [hz_inner]
    calc
      |inner ℝ T.direction (z - w) + t| ≤ |inner ℝ T.direction (z - w)| + |t| := abs_add_le _ _
      _ ≤ c * (δ : ℝ) + c / 2 := add_le_add hinner_zw ht
      _ = c / 2 + c * (δ : ℝ) := by ring
  have hnorm_perp : ∀ d : E, ‖d - (inner ℝ T.direction d) • T.direction‖ ≤ ‖d‖ := by
    intro d
    have hsq : ‖d - (inner ℝ T.direction d) • T.direction‖ ^ 2 ≤ ‖d‖ ^ 2 := by
      have hmain := norm_add_sq (𝕜 := ℝ) (x := (inner ℝ T.direction d) • T.direction)
        (y := d - (inner ℝ T.direction d) • T.direction)
      have hdecomp : d = (inner ℝ T.direction d) • T.direction +
          (d - (inner ℝ T.direction d) • T.direction) := by abel
      rw [← hdecomp] at hmain
      have hcross : inner ℝ ((inner ℝ T.direction d) • T.direction)
          (d - (inner ℝ T.direction d) • T.direction) = 0 := by
        have hsub : inner ℝ T.direction (d - (inner ℝ T.direction d) • T.direction) = 0 := by
          rw [inner_sub_right, inner_smul_right, he]
          ring
        simp [inner_smul_left, hsub]
      have hd : ‖d‖ ^ 2 = ‖(inner ℝ T.direction d) • T.direction‖ ^ 2 +
          ‖d - (inner ℝ T.direction d) • T.direction‖ ^ 2 := by
        rw [hmain, hcross]
        simp
      have hpe : ‖(inner ℝ T.direction d) • T.direction‖ ^ 2 = (inner ℝ T.direction d) ^ 2 := by
        rw [norm_smul, Real.norm_eq_abs, T.norm_direction, mul_one, sq_abs]
      nlinarith [hd, hpe, sq_nonneg (inner ℝ T.direction d)]
    have h := sq_le_sq.mp hsq
    simpa using h
  have hperp : z - T.center - inner ℝ T.direction (z - T.center) • T.direction
      = (z - w) - inner ℝ T.direction (z - w) • T.direction := by
    rw [hz_inner, hz_sub]
    module
  have htrans : ‖z - T.center - inner ℝ T.direction (z - T.center) • T.direction‖
      ≤ c * (δ : ℝ) := by
    rw [hperp]
    exact le_trans (hnorm_perp (z - w)) hnorm_zw
  exact ⟨haxial, htrans⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The component of `w` orthogonal to the unit vector `e` has norm at most `‖w‖`. -/
private lemma norm_perp_le_norm {e : E} (he : ‖e‖ = 1) (w : E) :
    ‖w - inner ℝ e w • e‖ ≤ ‖w‖ := by
  have hsq : ‖w - (inner ℝ e w) • e‖ ^ 2 ≤ ‖w‖ ^ 2 := by
    have hmain := norm_add_sq (𝕜 := ℝ) (x := (inner ℝ e w) • e) (y := w - (inner ℝ e w) • e)
    have hdecomp : w = (inner ℝ e w) • e + (w - (inner ℝ e w) • e) := by abel
    rw [← hdecomp] at hmain
    have hcross : inner ℝ ((inner ℝ e w) • e) (w - (inner ℝ e w) • e) = 0 := by
      have hsub : inner ℝ e (w - (inner ℝ e w) • e) = 0 := by
        rw [inner_sub_right, real_inner_smul_right]
        have hee : inner ℝ e e = 1 := by
          rw [real_inner_self_eq_norm_sq, he]
          norm_num
        rw [hee]
        ring
      simp [inner_smul_left, hsub]
    have hd : ‖w‖ ^ 2 = ‖(inner ℝ e w) • e‖ ^ 2 + ‖w - (inner ℝ e w) • e‖ ^ 2 := by
      rw [hmain, hcross]
      simp
    have hpe : ‖(inner ℝ e w) • e‖ ^ 2 = (inner ℝ e w) ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, he, mul_one, sq_abs]
    nlinarith [hd, hpe, sq_nonneg (inner ℝ e w)]
  simpa using (sq_le_sq.mp hsq)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The signed version of the chord-angle bound: unit vectors `e f g` with `⟪e, g⟫ ≥ 0` and
`⟪g, f⟫ ≥ 0`, whose perpendicular parts with respect to `e` and `f` are bounded by `A` and `B`
with `A + B < 1`, have the perpendicular part of `f` with respect to `e` bounded by `A + B`. -/
private lemma norm_perp_direction_le_of_aux {e f g : E} (he : ‖e‖ = 1) (hf : ‖f‖ = 1)
    (hg : ‖g‖ = 1) (hge : 0 ≤ inner ℝ e g) (hgf : 0 ≤ inner ℝ g f) {A B : ℝ}
    (hA : ‖g - inner ℝ e g • e‖ ≤ A) (hB : ‖g - inner ℝ f g • f‖ ≤ B) (hAB : A + B < 1) :
    ‖f - inner ℝ e f • e‖ ≤ A + B := by
  let α : ℝ := InnerProductGeometry.angle e g
  let β : ℝ := InnerProductGeometry.angle g f
  have hα0 : 0 ≤ α := by
    dsimp [α]
    exact InnerProductGeometry.angle_nonneg e g
  have hβ0 : 0 ≤ β := by
    dsimp [β]
    exact InnerProductGeometry.angle_nonneg g f
  have hα_le_pi : α ≤ Real.pi := by
    dsimp [α]
    exact InnerProductGeometry.angle_le_pi e g
  have hα_le : α ≤ Real.pi / 2 := by
    dsimp [α]
    rw [InnerProductGeometry.angle, Real.arccos_le_pi_div_two]
    exact div_nonneg hge (mul_pos (by (rw [he]; norm_num)) (by rw [hg]; norm_num)).le
  have hβ_le : β ≤ Real.pi / 2 := by
    dsimp [β]
    rw [InnerProductGeometry.angle, Real.arccos_le_pi_div_two]
    exact div_nonneg hgf (mul_pos (by rw [hg]; norm_num) (by rw [hf]; norm_num)).le
  have hsinα : Real.sin α = ‖g - inner ℝ e g • e‖ := by
    dsimp [α]
    exact (InnerProductGeometry.norm_sub_inner_smul_eq_sin_angle he hg).symm
  have hsinβ : Real.sin β = ‖g - inner ℝ f g • f‖ := by
    dsimp [β]
    rw [InnerProductGeometry.angle_comm]
    exact (InnerProductGeometry.norm_sub_inner_smul_eq_sin_angle hf hg).symm
  have hsinα_le_A : Real.sin α ≤ A := by rw [hsinα]; exact hA
  have hsinβ_le_B : Real.sin β ≤ B := by rw [hsinβ]; exact hB
  have hαβ_le : α + β ≤ Real.pi / 2 := by
    by_contra hnot
    have hgt : Real.pi / 2 < α + β := lt_of_not_ge hnot
    have hsub0 : 0 ≤ Real.pi / 2 - α := by linarith
    have hβgt : Real.pi / 2 - α < β := by linarith
    have hsin_gt : Real.cos α < Real.sin β := by
      have hlt := Real.sin_lt_sin_of_lt_of_le_pi_div_two
        (x := Real.pi / 2 - α) (y := β) (by linarith) hβ_le hβgt
      rwa [Real.sin_pi_div_two_sub] at hlt
    have hcosα0 : 0 ≤ Real.cos α := Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) hα_le
    have hsinα0 : 0 ≤ Real.sin α := by
      dsimp [α]
      exact InnerProductGeometry.sin_angle_nonneg e g
    have hsum1 : 1 ≤ Real.sin α + Real.cos α := by
      have hshow : (1 : ℝ) ^ 2 ≤ (Real.sin α + Real.cos α) ^ 2 := by
        have hsc : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
        nlinarith [sq_nonneg (Real.sin α), sq_nonneg (Real.cos α)]
      exact le_of_sq_le_sq hshow (add_nonneg hsinα0 hcosα0)
    nlinarith [hsinα_le_A, hsinβ_le_B, hsin_gt, hsum1, hAB]
  have hangle : InnerProductGeometry.angle e f ≤ α + β := by
    dsimp [α, β]
    exact InnerProductGeometry.angle_le_angle_add_angle e g f
  have hsin_ef_le : Real.sin (InnerProductGeometry.angle e f) ≤ Real.sin (α + β) := by
    have hx0 : 0 ≤ InnerProductGeometry.angle e f := InnerProductGeometry.angle_nonneg e f
    exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) hαβ_le hangle
  have hsin_add : Real.sin (α + β) ≤ Real.sin α + Real.sin β :=
    Real.sin_add_le_sin_add_sin hα0 hβ0 hαβ_le
  calc
    ‖f - inner ℝ e f • e‖ = Real.sin (InnerProductGeometry.angle e f) :=
      InnerProductGeometry.norm_sub_inner_smul_eq_sin_angle he hf
    _ ≤ Real.sin (α + β) := hsin_ef_le
    _ ≤ Real.sin α + Real.sin β := hsin_add
    _ ≤ A + B := add_le_add hsinα_le_A hsinβ_le_B

/-- **The chord-angle bound** (blueprint `lem:chordAngleBound`).

Two points at distance at least `d` lying both in the `ρ`-tube `Tρ` and in the `2`-dilate of the
`δ`-tube `Tb` pin the direction of `Tb` to that of `Tρ`: the transverse component of `Tb`'s
direction with respect to `Tρ`'s is at most `(2 ρ + 4 δ) / d`.  The conclusion is unconditional;
the regime where the right-hand side exceeds `1` is trivial because the left-hand side is the
norm of a component of a unit vector. -/
theorem norm_perp_direction_le_of_chord {δ : NNReal} (Tρ : Tube ρ E) (Tb : Tube δ E)
    {d : ℝ} (hd : 0 < d) {p q : E} (hpq : d ≤ dist p q)
    (hpρ : p ∈ Tρ.carrier) (hqρ : q ∈ Tρ.carrier)
    (hpb : p ∈ (Kakeya.Tube.dilate Tb 2).carrier)
    (hqb : q ∈ (Kakeya.Tube.dilate Tb 2).carrier) :
    ‖Tb.direction - inner ℝ Tρ.direction Tb.direction • Tρ.direction‖
      ≤ (2 * (ρ : ℝ) + 4 * (δ : ℝ)) / d := by
  let e : E := Tρ.direction
  let f : E := Tb.direction
  let g : E := (‖p - q‖)⁻¹ • (p - q)
  let A : ℝ := 2 * (ρ : ℝ) / d
  let B : ℝ := 4 * (δ : ℝ) / d
  have he : ‖e‖ = 1 := by
    dsimp [e]
    exact Tρ.norm_direction
  have hf : ‖f‖ = 1 := by
    dsimp [f]
    exact Tb.norm_direction
  have hpq_le : d ≤ ‖p - q‖ := by simpa [dist_eq_norm] using hpq
  have hpqn_pos : 0 < ‖p - q‖ := lt_of_lt_of_le hd hpq_le
  have hg : ‖g‖ = 1 := by
    dsimp [g]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpqn_pos)]
    exact inv_mul_cancel₀ (ne_of_gt hpqn_pos)
  -- Step 1: the chord `p - q` is nearly parallel to `e = Tρ.direction`
  have hp1 : p ∈ (Kakeya.Tube.dilate Tρ 1).carrier := subset_dilate Tρ (by norm_num) hpρ
  have hq1 : q ∈ (Kakeya.Tube.dilate Tρ 1).carrier := subset_dilate Tρ (by norm_num) hqρ
  have hppρ : ‖p - Tρ.center - inner ℝ e (p - Tρ.center) • e‖ ≤ (ρ : ℝ) := by
    have hz := (abs_inner_and_perp_le_of_mem_dilate Tρ (c := 1) (by norm_num) hp1).2
    simpa [e, one_mul] using hz
  have hqpρ : ‖q - Tρ.center - inner ℝ e (q - Tρ.center) • e‖ ≤ (ρ : ℝ) := by
    have hz := (abs_inner_and_perp_le_of_mem_dilate Tρ (c := 1) (by norm_num) hq1).2
    simpa [e, one_mul] using hz
  have hperp_e : ‖(p - q) - inner ℝ e (p - q) • e‖ ≤ 2 * (ρ : ℝ) := by
    have hid : (p - q) - inner ℝ e (p - q) • e
        = (p - Tρ.center - inner ℝ e (p - Tρ.center) • e) - (q - Tρ.center - inner ℝ e (q - Tρ.center) • e) := by
      rw [inner_sub_right, inner_sub_right, inner_sub_right]
      module
    calc
      ‖(p - q) - inner ℝ e (p - q) • e‖
          = ‖(p - Tρ.center - inner ℝ e (p - Tρ.center) • e) - (q - Tρ.center - inner ℝ e (q - Tρ.center) • e)‖ := by rw [hid]
      _ ≤ ‖p - Tρ.center - inner ℝ e (p - Tρ.center) • e‖ + ‖q - Tρ.center - inner ℝ e (q - Tρ.center) • e‖ := by
        exact norm_sub_le _ _
      _ ≤ (ρ : ℝ) + (ρ : ℝ) := by linarith
      _ = 2 * (ρ : ℝ) := by ring
  have hIdent_e : g - inner ℝ e g • e = (‖p - q‖)⁻¹ • ((p - q) - inner ℝ e (p - q) • e) := by
    dsimp [g]
    rw [real_inner_smul_right]
    rw [← smul_smul]
    rw [← smul_sub]
  have hgperp_e : ‖g - inner ℝ e g • e‖ ≤ A := by
    dsimp [A]
    rw [hIdent_e]
    rw [norm_smul]
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpqn_pos)]
    have hdiv : (‖p - q‖)⁻¹ * ‖(p - q) - inner ℝ e (p - q) • e‖
        = ‖(p - q) - inner ℝ e (p - q) • e‖ / ‖p - q‖ := by
      rw [div_eq_inv_mul]
    rw [hdiv]
    calc
      ‖(p - q) - inner ℝ e (p - q) • e‖ / ‖p - q‖
          ≤ ‖(p - q) - inner ℝ e (p - q) • e‖ / d := by
              exact div_le_div_of_nonneg_left (norm_nonneg _) hd hpq_le
      _ ≤ 2 * (ρ : ℝ) / d := div_le_div_of_nonneg_right hperp_e hd.le
  -- Step 2: the chord is nearly parallel to `f = Tb.direction`
  have hppδ : ‖p - Tb.center - inner ℝ f (p - Tb.center) • f‖ ≤ 2 * (δ : ℝ) := by
    have hz := (abs_inner_and_perp_le_of_mem_dilate Tb (c := 2) (by norm_num) hpb).2
    simpa [f] using hz
  have hqpδ : ‖q - Tb.center - inner ℝ f (q - Tb.center) • f‖ ≤ 2 * (δ : ℝ) := by
    have hz := (abs_inner_and_perp_le_of_mem_dilate Tb (c := 2) (by norm_num) hqb).2
    simpa [f] using hz
  have hperp_f : ‖(p - q) - inner ℝ f (p - q) • f‖ ≤ 4 * (δ : ℝ) := by
    have hid : (p - q) - inner ℝ f (p - q) • f
        = (p - Tb.center - inner ℝ f (p - Tb.center) • f) - (q - Tb.center - inner ℝ f (q - Tb.center) • f) := by
      rw [inner_sub_right, inner_sub_right, inner_sub_right]
      module
    rw [hid]
    exact (norm_sub_le _ _).trans (by linarith)
  have hIdent_f : g - inner ℝ f g • f = (‖p - q‖)⁻¹ • ((p - q) - inner ℝ f (p - q) • f) := by
    dsimp [g]
    rw [real_inner_smul_right]
    rw [← smul_smul]
    rw [← smul_sub]
  have hgperp_f : ‖g - inner ℝ f g • f‖ ≤ B := by
    dsimp [B]
    rw [hIdent_f]
    rw [norm_smul]
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpqn_pos)]
    have hdiv : (‖p - q‖)⁻¹ * ‖(p - q) - inner ℝ f (p - q) • f‖
        = ‖(p - q) - inner ℝ f (p - q) • f‖ / ‖p - q‖ := by
      rw [div_eq_inv_mul]
    rw [hdiv]
    calc
      ‖(p - q) - inner ℝ f (p - q) • f‖ / ‖p - q‖
          ≤ ‖(p - q) - inner ℝ f (p - q) • f‖ / d := by
              exact div_le_div_of_nonneg_left (norm_nonneg _) hd hpq_le
      _ ≤ 4 * (δ : ℝ) / d := div_le_div_of_nonneg_right hperp_f hd.le
  -- Step 3: combine the two near-parallelisms through the angle triangle inequality
  have hmain : ‖f - inner ℝ e f • e‖ ≤ A + B := by
    by_cases htriv : 1 ≤ A + B
    · exact le_trans (by simpa [hf] using norm_perp_le_norm he f) htriv
    · have hAB : A + B < 1 := by linarith
      by_cases hge : 0 ≤ inner ℝ e g
      · by_cases hgf : 0 ≤ inner ℝ g f
        · exact norm_perp_direction_le_of_aux he hf hg hge hgf hgperp_e hgperp_f hAB
        · have hgf' : 0 ≤ inner ℝ g (-f) := by
            rw [inner_neg_right]
            linarith [lt_of_not_ge hgf]
          have hB' : ‖g - inner ℝ (-f) g • (-f)‖ ≤ B := by
            have hid : g - inner ℝ (-f) g • (-f) = g - inner ℝ f g • f := by
              simp [inner_neg_left]
            rwa [hid]
          have hconc := norm_perp_direction_le_of_aux he (by simpa using hf) hg hge hgf'
            hgperp_e hB' hAB
          have hnorm : ‖(-f) - inner ℝ e (-f) • e‖ = ‖f - inner ℝ e f • e‖ := by
            calc
              ‖(-f) - inner ℝ e (-f) • e‖ = ‖-(f - inner ℝ e f • e)‖ := by
                congr 1
                simp [inner_neg_right]
                abel
              _ = ‖f - inner ℝ e f • e‖ := norm_neg (f - inner ℝ e f • e)
          rwa [← hnorm]
      · by_cases hgf : 0 ≤ inner ℝ g f
        · have hge' : 0 ≤ inner ℝ (-e) g := by
            rw [inner_neg_left]
            linarith [lt_of_not_ge hge]
          have hA' : ‖g - inner ℝ (-e) g • (-e)‖ ≤ A := by
            have hid : g - inner ℝ (-e) g • (-e) = g - inner ℝ e g • e := by
              simp [inner_neg_left]
            rwa [hid]
          have hconc := norm_perp_direction_le_of_aux (by simpa using he) hf hg hge' hgf
            hA' hgperp_f hAB
          simpa [inner_neg_left] using hconc
        · have hge' : 0 ≤ inner ℝ (-e) g := by
            rw [inner_neg_left]
            linarith [lt_of_not_ge hge]
          have hgf' : 0 ≤ inner ℝ g (-f) := by
            rw [inner_neg_right]
            linarith [lt_of_not_ge hgf]
          have hA' : ‖g - inner ℝ (-e) g • (-e)‖ ≤ A := by
            have hid : g - inner ℝ (-e) g • (-e) = g - inner ℝ e g • e := by
              simp [inner_neg_left]
            rwa [hid]
          have hB' : ‖g - inner ℝ (-f) g • (-f)‖ ≤ B := by
            have hid : g - inner ℝ (-f) g • (-f) = g - inner ℝ f g • f := by
              simp [inner_neg_left]
            rwa [hid]
          have hconc := norm_perp_direction_le_of_aux (by simpa using he) (by simpa using hf) hg
            hge' hgf' hA' hB' hAB
          have hnorm : ‖(-f) - inner ℝ (-e) (-f) • (-e)‖ = ‖f - inner ℝ e f • e‖ := by
            calc
              ‖(-f) - inner ℝ (-e) (-f) • (-e)‖ = ‖-(f - inner ℝ e f • e)‖ := by
                congr 1
                simp [inner_neg_left, inner_neg_right]
                abel
              _ = ‖f - inner ℝ e f • e‖ := norm_neg (f - inner ℝ e f • e)
          rwa [← hnorm]
  have hmain' : ‖f - inner ℝ e f • e‖ ≤ (2 * (ρ : ℝ) + 4 * (δ : ℝ)) / d := by
    dsimp [A, B] at hmain
    rw [add_div]
    exact hmain
  simpa [e, f] using hmain'

/-- **Two points of dilates of one tube are close** (blueprint `lem:dilatePointsDist`).

Both points are decomposed along the axis of `T`; the four bounds of
`Tube.abs_inner_and_perp_le_of_mem_dilate` add up to the stated one. -/
theorem dist_le_of_mem_dilate_of_mem_dilate {δ : NNReal} (T : Tube δ E) {c c' : ℝ}
    (hc : 0 < c) (hc' : 0 < c') {y z : E}
    (hy : y ∈ (Kakeya.Tube.dilate T c).carrier)
    (hz : z ∈ (Kakeya.Tube.dilate T c').carrier) :
    dist y z ≤ (c + c') / 2 + 2 * (c + c') * (δ : ℝ) := by
  let s_y : ℝ := inner ℝ (y - T.center) T.direction
  let s_z : ℝ := inner ℝ (z - T.center) T.direction
  let v_y : E := (y - T.center) - s_y • T.direction
  let v_z : E := (z - T.center) - s_z • T.direction
  have hwy := abs_inner_and_perp_le_of_mem_dilate (T := T) (c := c) hc hy
  have hwz := abs_inner_and_perp_le_of_mem_dilate (T := T) (c := c') hc' hz
  have hsy : |s_y| ≤ c / 2 + c * (δ : ℝ) := by
    simpa [s_y] using hwy.1
  have hsz : |s_z| ≤ c' / 2 + c' * (δ : ℝ) := by
    simpa [s_z] using hwz.1
  have hvy : ‖v_y‖ ≤ c * (δ : ℝ) := by
    simpa [v_y, s_y, real_inner_comm] using hwy.2
  have hvz : ‖v_z‖ ≤ c' * (δ : ℝ) := by
    simpa [v_z, s_z, real_inner_comm] using hwz.2
  have hydecomp : y - T.center = s_y • T.direction + v_y := by
    dsimp [v_y]
    module
  have hzdecomp : z - T.center = s_z • T.direction + v_z := by
    dsimp [v_z]
    module
  have hdiff : y - z = (s_y - s_z) • T.direction + (v_y - v_z) := by
    calc
      y - z = (y - T.center) - (z - T.center) := by abel
      _ = (s_y • T.direction + v_y) - (s_z • T.direction + v_z) := by rw [hydecomp, hzdecomp]
      _ = (s_y - s_z) • T.direction + (v_y - v_z) := by module
  have habs : |s_y - s_z| ≤ |s_y| + |s_z| := by
    simpa [sub_eq_add_neg] using (abs_add_le s_y (-s_z))
  rw [dist_eq_norm]
  rw [hdiff]
  calc
    ‖(s_y - s_z) • T.direction + (v_y - v_z)‖
        ≤ ‖(s_y - s_z) • T.direction‖ + ‖v_y - v_z‖ := norm_add_le _ _
    _ = |s_y - s_z| + ‖v_y - v_z‖ := by
        rw [norm_smul, T.norm_direction]
        simp
    _ ≤ (|s_y| + |s_z|) + (‖v_y‖ + ‖v_z‖) := add_le_add habs (norm_sub_le v_y v_z)
    _ ≤ (c / 2 + c * (δ : ℝ)) + (c' / 2 + c' * (δ : ℝ)) + (c * (δ : ℝ) + c' * (δ : ℝ)) := by
        linarith [hsy, hsz, hvy, hvz]
    _ = (c + c') / 2 + 2 * (c + c') * (δ : ℝ) := by ring

/-- **Transverse drift of a point of a dilate against a foreign direction** (blueprint
`lem:dilatePointPerpDrift`).

The transverse component is measured against a unit vector `e` foreign to `T`, so the axial
coordinate of `y` contributes through the tilt `S = ‖f - ⟪e, f⟫ • e‖` of `T`'s own direction. -/
theorem norm_perp_sub_center_le_of_mem_dilate {δ : NNReal} (T : Tube δ E) {c : ℝ} (hc : 0 < c)
    {e : E} (he : ‖e‖ = 1) {y : E} (hy : y ∈ (Kakeya.Tube.dilate T c).carrier) :
    ‖(y - T.center) - inner ℝ e (y - T.center) • e‖
      ≤ (c / 2 + c * (δ : ℝ)) * ‖T.direction - inner ℝ e T.direction • e‖ + c * (δ : ℝ) := by
  let s : ℝ := inner ℝ T.direction (y - T.center)
  let v : E := (y - T.center) - s • T.direction
  have hy_dec : y - T.center = s • T.direction + v := by
    dsimp [v]
    abel
  have hb := abs_inner_and_perp_le_of_mem_dilate T hc hy
  have hbs : |s| ≤ c / 2 + c * (δ : ℝ) := by
    dsimp [s]
    rw [real_inner_comm]
    exact hb.1
  have hbnp : ‖v‖ ≤ c * (δ : ℝ) := by
    dsimp [v, s]
    exact hb.2
  have hperp_exp : (y - T.center) - inner ℝ e (y - T.center) • e
      = s • (T.direction - inner ℝ e T.direction • e) + (v - inner ℝ e v • e) := by
    rw [hy_dec]
    rw [inner_add_right, real_inner_smul_right]
    rw [add_smul]
    rw [← smul_smul]
    module
  have hnorm : ‖(y - T.center) - inner ℝ e (y - T.center) • e‖
      ≤ |s| * ‖T.direction - inner ℝ e T.direction • e‖ + ‖v‖ := by
    rw [hperp_exp]
    calc
      ‖s • (T.direction - inner ℝ e T.direction • e) + (v - inner ℝ e v • e)‖
          ≤ ‖s • (T.direction - inner ℝ e T.direction • e)‖ + ‖v - inner ℝ e v • e‖ :=
            norm_add_le _ _
      _ = |s| * ‖T.direction - inner ℝ e T.direction • e‖ + ‖v - inner ℝ e v • e‖ := by
            rw [norm_smul, Real.norm_eq_abs]
      _ ≤ |s| * ‖T.direction - inner ℝ e T.direction • e‖ + ‖v‖ := by
            exact add_le_add
              (le_refl (|s| * ‖T.direction - inner ℝ e T.direction • e‖)) (norm_perp_le_norm he v)
  have hS : 0 ≤ ‖T.direction - inner ℝ e T.direction • e‖ := norm_nonneg _
  calc
    ‖(y - T.center) - inner ℝ e (y - T.center) • e‖
        ≤ |s| * ‖T.direction - inner ℝ e T.direction • e‖ + ‖v‖ := hnorm
    _ ≤ (c / 2 + c * (δ : ℝ)) * ‖T.direction - inner ℝ e T.direction • e‖ + c * (δ : ℝ) := by
        exact add_le_add (mul_le_mul_of_nonneg_right hbs hS) hbnp

/-- **A pinned thin tube is longitudinally confined** (blueprint
`lem:thinTubeInFatDilateLongitudinal`).

This bound is *not* a consequence of the dilation ratio being at least `1`: the core of `Tb` is
pinned to `Tρ` only through the single point `p`, so the centre of `Tb` is offset from that of
`Tρ` by `O(1)` and not by `O(ρ)`. -/
theorem abs_inner_sub_center_le_of_pinned {δ : NNReal} (Tρ : Tube ρ E) (Tb : Tube δ E)
    {K : ℝ} (hK : 1 ≤ K) (hρ1 : (ρ : ℝ) ≤ 1) (hδ : (δ : ℝ) ≤ K * (ρ : ℝ))
    {p : E} (hpρ : p ∈ Tρ.carrier) (hpb : p ∈ (Kakeya.Tube.dilate Tb 2).carrier)
    {x : E} (hx : x ∈ Tb.carrier) :
    |inner ℝ Tρ.direction (x - Tρ.center)| ≤ 16 * K := by
  -- x lies in the 1-dilate of Tb, so the chord estimate bounds `dist x p`
  have hx1 : x ∈ (Kakeya.Tube.dilate Tb 1).carrier := subset_dilate Tb (by norm_num) hx
  have hdist : dist x p ≤ 3 / 2 + 6 * (δ : ℝ) := by
    have hz := dist_le_of_mem_dilate_of_mem_dilate (T := Tb) (c := 1) (c' := 2)
      (by norm_num) (by norm_num) hx1 hpb
    nlinarith
  -- p lies in the 1-dilate of Tρ, pinning its axial coordinate with respect to Tρ
  have hp1 : p ∈ (Kakeya.Tube.dilate Tρ 1).carrier := subset_dilate Tρ (by norm_num) hpρ
  have hpax : |inner ℝ Tρ.direction (p - Tρ.center)| ≤ 1 / 2 + (ρ : ℝ) := by
    have hz := (abs_inner_and_perp_le_of_mem_dilate Tρ (c := 1) (by norm_num) hp1).1
    simpa [real_inner_comm] using hz
  -- Cauchy-Schwarz with `‖Tρ.direction‖ = 1`
  have hxp : |inner ℝ Tρ.direction (x - p)| ≤ dist x p := by
    calc
      |inner ℝ Tρ.direction (x - p)| ≤ ‖Tρ.direction‖ * ‖x - p‖ :=
        abs_real_inner_le_norm Tρ.direction (x - p)
      _ = ‖x - p‖ := by simp [Tρ.norm_direction]
      _ = dist x p := by rw [← dist_eq_norm]
  -- triangle inequality, then the two estimates, then the arithmetic
  calc
    |inner ℝ Tρ.direction (x - Tρ.center)|
        ≤ |inner ℝ Tρ.direction (p - Tρ.center)| + |inner ℝ Tρ.direction (x - p)| := by
          rw [show x - Tρ.center = (p - Tρ.center) + (x - p) by abel]
          rw [inner_add_right]
          exact abs_add_le _ _
    _ ≤ (1 / 2 + (ρ : ℝ)) + dist x p := add_le_add hpax hxp
    _ ≤ (1 / 2 + (ρ : ℝ)) + (3 / 2 + 6 * (δ : ℝ)) := by
          exact add_le_add (le_refl (1 / 2 + (ρ : ℝ))) hdist
    _ ≤ 16 * K := by
          have hρK : (ρ : ℝ) ≤ K := by linarith
          have hK0 : 0 ≤ K := by linarith
          have hKρ : K * (ρ : ℝ) ≤ K := by
            simpa [mul_comm] using mul_le_mul_of_nonneg_right hρ1 hK0
          nlinarith [hK, hδ, hρK, hKρ]

/-- **Transverse confinement of a pinned thin tube: the small-angle branch** (blueprint
`lem:thinTubeInFatDilateTransverseSmallAngle`).

The case hypothesis `15 K ρ ≤ 1` is what absorbs the quadratic term `45 K² ρ²` back into
`3 K ρ`. -/
theorem norm_perp_sub_center_le_of_pinned_of_le_one {δ : NNReal} (Tρ : Tube ρ E) (Tb : Tube δ E)
    {K : ℝ} (hK : 1 ≤ K) (hδ : (δ : ℝ) ≤ K * (ρ : ℝ))
    {p : E} (hpρ : p ∈ Tρ.carrier) (hpb : p ∈ (Kakeya.Tube.dilate Tb 2).carrier)
    (hS : ‖Tb.direction - inner ℝ Tρ.direction Tb.direction • Tρ.direction‖ ≤ 15 * K * (ρ : ℝ))
    (hsmall : 15 * K * (ρ : ℝ) ≤ 1) {x : E} (hx : x ∈ Tb.carrier) :
    ‖(x - Tρ.center) - inner ℝ Tρ.direction (x - Tρ.center) • Tρ.direction‖
      ≤ 59 / 2 * K * (ρ : ℝ) := by
  let e : E := Tρ.direction
  let S : ℝ := ‖Tb.direction - inner ℝ e Tb.direction • e‖
  have he : ‖e‖ = 1 := by
    simpa [e] using Tρ.norm_direction
  have hS' : S ≤ 15 * K * (ρ : ℝ) := by
    simpa [S, e] using hS
  have hS0 : 0 ≤ S := by
    dsimp [S]
    exact norm_nonneg _
  have hK0 : 0 ≤ K := by linarith
  have hρ0 : 0 ≤ (ρ : ℝ) := NNReal.coe_nonneg ρ
  have hδ0 : 0 ≤ (δ : ℝ) := NNReal.coe_nonneg δ
  have hp1 : p ∈ (Kakeya.Tube.dilate Tρ 1).carrier := subset_dilate Tρ (by norm_num) hpρ
  have hx1 : x ∈ (Kakeya.Tube.dilate Tb 1).carrier := subset_dilate Tb (by norm_num) hx
  have hpa : ‖(p - Tρ.center) - inner ℝ e (p - Tρ.center) • e‖ ≤ (ρ : ℝ) := by
    have hz := (abs_inner_and_perp_le_of_mem_dilate Tρ (c := 1) (by norm_num) hp1).2
    simpa [e, one_mul] using hz
  have hpbp : ‖(p - Tb.center) - inner ℝ e (p - Tb.center) • e‖
      ≤ (1 + 2 * (δ : ℝ)) * S + 2 * (δ : ℝ) := by
    have hz := norm_perp_sub_center_le_of_mem_dilate (T := Tb) (c := 2) (hc := by norm_num)
      (e := e) (he := he) (y := p) (hy := hpb)
    simpa [S, e, one_mul] using hz
  have hxb : ‖(x - Tb.center) - inner ℝ e (x - Tb.center) • e‖
      ≤ (1 / 2 + (δ : ℝ)) * S + (δ : ℝ) := by
    have hz := norm_perp_sub_center_le_of_mem_dilate (T := Tb) (c := 1) (hc := by norm_num)
      (e := e) (he := he) (y := x) (hy := hx1)
    simpa [S, e, one_mul] using hz
  have hid : (x - Tρ.center) - inner ℝ e (x - Tρ.center) • e
      = ((p - Tρ.center) - inner ℝ e (p - Tρ.center) • e)
        - ((p - Tb.center) - inner ℝ e (p - Tb.center) • e)
        + ((x - Tb.center) - inner ℝ e (x - Tb.center) • e) := by
    rw [show x - Tρ.center = (p - Tρ.center) - (p - Tb.center) + (x - Tb.center) by abel]
    rw [inner_add_right, inner_sub_right, inner_sub_right, inner_sub_right]
    module
  have htri : ‖(x - Tρ.center) - inner ℝ e (x - Tρ.center) • e‖
      ≤ ‖(p - Tρ.center) - inner ℝ e (p - Tρ.center) • e‖
        + (‖(p - Tb.center) - inner ℝ e (p - Tb.center) • e‖
          + ‖(x - Tb.center) - inner ℝ e (x - Tb.center) • e‖) := by
    let A : E := (p - Tρ.center) - inner ℝ e (p - Tρ.center) • e
    let B : E := (p - Tb.center) - inner ℝ e (p - Tb.center) • e
    let C : E := (x - Tb.center) - inner ℝ e (x - Tb.center) • e
    rw [hid]
    calc
      ‖A - B + C‖ ≤ ‖A - B‖ + ‖C‖ := norm_add_le (A - B) C
      _ ≤ (‖A‖ + ‖B‖) + ‖C‖ := add_le_add (norm_sub_le A B) le_rfl
      _ = ‖A‖ + (‖B‖ + ‖C‖) := by ring
  have hbound : ‖(x - Tρ.center) - inner ℝ e (x - Tρ.center) • e‖
      ≤ (ρ : ℝ) + (3 / 2 + 3 * (δ : ℝ)) * S + 3 * (δ : ℝ) := by
    nlinarith [htri, hpa, hpbp, hxb]
  have hK3 : 0 ≤ 3 * K := by nlinarith
  have hpos : 0 ≤ 3 * K * (ρ : ℝ) := mul_nonneg hK3 hρ0
  have hprod : 45 * K ^ 2 * (ρ : ℝ) ^ 2 ≤ 3 * K * (ρ : ℝ) := by
    rw [show 45 * K ^ 2 * (ρ : ℝ) ^ 2 = 3 * K * (ρ : ℝ) * (15 * K * (ρ : ℝ)) by ring]
    simpa using mul_le_mul_of_nonneg_left hsmall hpos
  calc
    ‖(x - Tρ.center) - inner ℝ e (x - Tρ.center) • e‖
        ≤ (ρ : ℝ) + (3 / 2 + 3 * (δ : ℝ)) * S + 3 * (δ : ℝ) := hbound
    _ ≤ 59 / 2 * K * (ρ : ℝ) := by
      nlinarith [hS', hS0, hδ, hδ0, hρ0, hK, hK0, hprod]

/-- **Transverse confinement of a pinned thin tube: the large-angle branch** (blueprint
`lem:thinTubeInFatDilateTransverseLargeAngle`).

This branch is angle-free.  It may *not* be disposed of by calling the conclusion trivial on the
ground that `32 K ρ > 2` exceeds the diameter of a unit ball: `Tb` is not confined to a unit ball
about the centre of `Tρ`, its points reaching distance up to `2 + 8 K ρ` from it. -/
theorem norm_perp_sub_center_le_of_pinned_of_one_lt {δ : NNReal} (Tρ : Tube ρ E) (Tb : Tube δ E)
    {K : ℝ} (hK : 1 ≤ K) (hδ : (δ : ℝ) ≤ K * (ρ : ℝ))
    {p : E} (hpρ : p ∈ Tρ.carrier) (hpb : p ∈ (Kakeya.Tube.dilate Tb 2).carrier)
    (hlarge : 1 < 15 * K * (ρ : ℝ)) {x : E} (hx : x ∈ Tb.carrier) :
    ‖(x - Tρ.center) - inner ℝ Tρ.direction (x - Tρ.center) • Tρ.direction‖
      ≤ 59 / 2 * K * (ρ : ℝ) := by
  let e : E := Tρ.direction
  let m : E := Tρ.center
  have he : ‖e‖ = 1 := by
    dsimp [e]
    exact Tρ.norm_direction
  have hρ0 : 0 ≤ (ρ : ℝ) := NNReal.coe_nonneg ρ
  -- `x` lies in the `1`-dilate of `Tb`, pinned with `p` in its `2`-dilate
  have hxp : ‖x - p‖ ≤ 3 / 2 + 6 * (K * (ρ : ℝ)) := by
    have hx1 : x ∈ (Kakeya.Tube.dilate Tb 1).carrier := subset_dilate Tb (by norm_num) hx
    have hd : dist x p ≤ 3 / 2 + 6 * (δ : ℝ) := by
      have hd0 := dist_le_of_mem_dilate_of_mem_dilate (T := Tb) (c := 1) (c' := 2)
        (by norm_num) (by norm_num) hx1 hpb
      norm_num at hd0
      exact hd0
    have hdx : ‖x - p‖ ≤ 3 / 2 + 6 * (δ : ℝ) := by
      simpa [dist_eq_norm] using hd
    linarith [hδ]
  -- `p` is within `ρ` of `m` in the transverse directions (the `1`-dilate bound)
  have hperp_p : ‖(p - m) - inner ℝ e (p - m) • e‖ ≤ (ρ : ℝ) := by
    have hp1 : p ∈ (Kakeya.Tube.dilate Tρ 1).carrier := subset_dilate Tρ (by norm_num) hpρ
    have hz := (abs_inner_and_perp_le_of_mem_dilate Tρ (c := 1) (by norm_num) hp1).2
    simpa [e, m, one_mul] using hz
  -- the perpendicular part is linear
  have hid : (x - m) - inner ℝ e (x - m) • e
      = ((p - m) - inner ℝ e (p - m) • e) + ((x - p) - inner ℝ e (x - p) • e) := by
    rw [show x - m = (p - m) + (x - p) by abel]
    rw [inner_add_right, add_smul]
    module
  have hperp_x : ‖(x - m) - inner ℝ e (x - m) • e‖
      ≤ (ρ : ℝ) + 3 / 2 + 6 * (K * (ρ : ℝ)) := by
    calc
      ‖(x - m) - inner ℝ e (x - m) • e‖
          ≤ ‖(p - m) - inner ℝ e (p - m) • e‖ + ‖(x - p) - inner ℝ e (x - p) • e‖ := by
            rw [hid]
            exact norm_add_le _ _
      _ ≤ (ρ : ℝ) + ‖x - p‖ := by
            exact add_le_add hperp_p (norm_perp_le_norm he (x - p))
      _ ≤ (ρ : ℝ) + 3 / 2 + 6 * (K * (ρ : ℝ)) := by
            linarith [hxp]
  -- numerical bookkeeping: `ρ ≤ Kρ` and `3/2 ≤ 45/2 Kρ`
  have hle1 : (ρ : ℝ) ≤ K * (ρ : ℝ) := by
    simpa using mul_le_mul_of_nonneg_right hK hρ0
  have hle2 : (3 / 2 : ℝ) ≤ 45 / 2 * (K * (ρ : ℝ)) := by
    have hl := mul_le_mul_of_nonneg_left (le_of_lt hlarge) (by norm_num : (0 : ℝ) ≤ 3 / 2)
    nlinarith
  calc
    ‖(x - Tρ.center) - inner ℝ Tρ.direction (x - Tρ.center) • Tρ.direction‖
        = ‖(x - m) - inner ℝ e (x - m) • e‖ := by simp [e, m]
    _ ≤ (ρ : ℝ) + 3 / 2 + 6 * (K * (ρ : ℝ)) := hperp_x
    _ ≤ 59 / 2 * K * (ρ : ℝ) := by nlinarith [hle1, hle2]

/-- **Transverse confinement of a pinned thin tube** (blueprint
`lem:thinTubeInFatDilateTransverse`).

Both branches of the split on `15 K ρ ≤ 1`, argued by quite different routes, land on the same
figure `29.5 K ρ`; that is what fixes `32 K` as the ratio in
`Tube.subset_dilate_of_norm_perp_direction_le`. -/
theorem norm_perp_sub_center_le_of_pinned {δ : NNReal} (Tρ : Tube ρ E) (Tb : Tube δ E)
    {K : ℝ} (hK : 1 ≤ K) (hδ : (δ : ℝ) ≤ K * (ρ : ℝ))
    {p : E} (hpρ : p ∈ Tρ.carrier) (hpb : p ∈ (Kakeya.Tube.dilate Tb 2).carrier)
    (hS : ‖Tb.direction - inner ℝ Tρ.direction Tb.direction • Tρ.direction‖ ≤ 15 * K * (ρ : ℝ))
    {x : E} (hx : x ∈ Tb.carrier) :
    ‖(x - Tρ.center) - inner ℝ Tρ.direction (x - Tρ.center) • Tρ.direction‖
      ≤ 32 * K * (ρ : ℝ) := by
  have hKρ : 0 ≤ K * (ρ : ℝ) := mul_nonneg (le_trans zero_le_one hK) (NNReal.coe_nonneg ρ)
  have hhalf : 59 / 2 * K * (ρ : ℝ) ≤ 32 * K * (ρ : ℝ) := by
    nlinarith [hKρ]
  rcases le_or_gt (15 * K * (ρ : ℝ)) 1 with hsmall | hlarge
  · exact le_trans (norm_perp_sub_center_le_of_pinned_of_le_one Tρ Tb hK hδ hpρ hpb hS hsmall hx)
      hhalf
  · exact le_trans (norm_perp_sub_center_le_of_pinned_of_one_lt Tρ Tb hK hδ hpρ hpb hlarge hx)
      hhalf

/-- **A thin tube whose direction is pinned lies in a bounded dilate of the fat one** (blueprint
`lem:thinTubeInFatDilate`).

If `Tb` has thickness at most `K ρ`, meets the `ρ`-tube `Tρ` in a point `p` that also lies in
`2 · Tb`, and its direction is transverse to that of `Tρ` by at most `15 K ρ`, then
`Tb ⊆ 32 K · Tρ`.

This is the geometric core of blueprint `lem:ml1bootPlankTubeInParentDilate`, whose value
`c' = 32 C_𝕎` is exactly the `32 K` here; the plank enters that lemma only by supplying `p`, a
second point at distance `≥ 2/5`, and hence the transverse hypothesis `hS` through
`Tube.norm_perp_direction_le_of_chord`.  See blueprint `note:thinTubeInFatDilate`. -/
theorem subset_dilate_of_norm_perp_direction_le {δ : NNReal} (Tρ : Tube ρ E) (Tb : Tube δ E)
    {K : ℝ} (hK : 1 ≤ K) (hρ1 : (ρ : ℝ) ≤ 1) (hδ : (δ : ℝ) ≤ K * (ρ : ℝ))
    {p : E} (hpρ : p ∈ Tρ.carrier) (hpb : p ∈ (Kakeya.Tube.dilate Tb 2).carrier)
    (hS : ‖Tb.direction - inner ℝ Tρ.direction Tb.direction • Tρ.direction‖ ≤ 15 * K * (ρ : ℝ)) :
    Tb.carrier ⊆ (Kakeya.Tube.dilate Tρ (32 * K)).carrier := by
  intro x hx
  let s : ℝ := inner ℝ Tρ.direction (x - Tρ.center)
  have hC : 0 < 32 * K := by linarith
  have hs : |s| ≤ (32 * K) / 2 := by
    have h := abs_inner_sub_center_le_of_pinned Tρ Tb hK hρ1 hδ hpρ hpb hx
    dsimp [s] at h ⊢
    nlinarith
  have hz : dist x (Tρ.center + s • Tρ.direction) ≤ 32 * K * (ρ : ℝ) := by
    have h := norm_perp_sub_center_le_of_pinned Tρ Tb hK hδ hpρ hpb hS hx
    rw [dist_eq_norm, sub_add_eq_sub_sub]
    dsimp [s] at h ⊢
    exact h
  exact Kakeya.Tube.mem_dilate_of_dist_axis_le Tρ hC hs hz

/-- **A point of a dilate, in axial and transverse coordinates** (blueprint
`lem:dilatePointBounds`).  A point of the thin dilate `C_n · V` is within `3 C_n / 2` of the
centre of `V` along the axis of `V`, and within `C_n ρ` of it in the transverse directions. -/
theorem inner_and_perp_le_of_mem_dilate (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (V : Tube ρ E) {z : E}
    (hz : z ∈ (Kakeya.Tube.dilate V
      (Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E))).carrier) :
    |inner ℝ (z - V.center) V.direction|
        ≤ 3 / 2 * Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) ∧
      ‖z - V.center - inner ℝ V.direction (z - V.center) • V.direction‖
        ≤ Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) * (ρ : ℝ) := by
  set Cn : ℝ := Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) with hCndef
  have hCpos : 0 < Cn := by
    dsimp [Cn]
    linarith [Kakeya.Tube.tubeOverlapCoreClose.one_lt_C (Module.finrank ℝ E)]
  have hCnonneg : 0 ≤ Cn := by linarith
  have hρ0' : 0 ≤ (ρ : ℝ) := by exact_mod_cast le_of_lt hρ0
  have hCr : 0 ≤ Cn * (ρ : ℝ) := mul_nonneg hCnonneg hρ0'
  have hz' : z ∈ cthickening (Cn * (ρ : ℝ))
      (segment ℝ (V.center - (Cn / 2) • V.direction) (V.center + (Cn / 2) • V.direction)) := by
    rw [dilate_carrier_eq_cthickening V hCpos] at hz
    exact hz
  have hz'' : z ∈ ⋃ x ∈ segment ℝ (V.center - (Cn / 2) • V.direction)
      (V.center + (Cn / 2) • V.direction), closedBall x (Cn * (ρ : ℝ)) := by
    rwa [← isClosed_segment.cthickening_eq_biUnion_closedBall hCr]
  rw [Set.mem_iUnion₂] at hz''
  rcases hz'' with ⟨w, hw, hzw⟩
  rw [Metric.mem_closedBall] at hzw
  rcases (segment_eq_image_lineMap ℝ (V.center - (Cn / 2) • V.direction)
      (V.center + (Cn / 2) • V.direction)).symm ▸ hw with ⟨s, hs, hw_eq⟩
  let t : ℝ := (2 * s - 1) * (Cn / 2)
  have hw_eq' : w = V.center + t • V.direction := by
    rw [← hw_eq]
    rw [AffineMap.lineMap_apply_module]
    dsimp [t]
    module
  have hs0 : 0 ≤ s := hs.1
  have hs1 : s ≤ 1 := hs.2
  have h2s : -1 ≤ 2 * s - 1 ∧ 2 * s - 1 ≤ 1 := by
    constructor <;> linarith
  have hCn2 : 0 ≤ Cn / 2 := by positivity
  have ht : |t| ≤ Cn / 2 := by
    dsimp [t]
    calc
      |(2 * s - 1) * (Cn / 2)| = |2 * s - 1| * |Cn / 2| := abs_mul _ _
      _ = |2 * s - 1| * (Cn / 2) := by rw [abs_of_nonneg hCn2]
      _ ≤ 1 * (Cn / 2) := mul_le_mul_of_nonneg_right (abs_le.mpr h2s) hCn2
      _ = Cn / 2 := by ring
  have he : (inner ℝ V.direction V.direction : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, V.norm_direction]; norm_num
  have hz_sub : z - V.center = (z - w) + t • V.direction := by
    rw [hw_eq']
    abel
  have hz_inner : inner ℝ V.direction (z - V.center) = inner ℝ V.direction (z - w) + t := by
    rw [hz_sub]
    rw [inner_add_right, inner_smul_right, he]
    ring
  have hnorm_zw : ‖z - w‖ ≤ Cn * (ρ : ℝ) := by
    simpa [dist_eq_norm] using hzw
  have hinner_zw : |inner ℝ V.direction (z - w)| ≤ Cn * (ρ : ℝ) := by
    calc
      |inner ℝ V.direction (z - w)| ≤ ‖V.direction‖ * ‖z - w‖ :=
        abs_real_inner_le_norm V.direction (z - w)
      _ = ‖z - w‖ := by rw [V.norm_direction]; ring
      _ ≤ Cn * (ρ : ℝ) := hnorm_zw
  have haxial : |inner ℝ (z - V.center) V.direction| ≤ 3 / 2 * Cn := by
    rw [real_inner_comm]
    rw [hz_inner]
    calc
      |inner ℝ V.direction (z - w) + t| ≤ |inner ℝ V.direction (z - w)| + |t| := abs_add_le _ _
      _ ≤ Cn * (ρ : ℝ) + Cn / 2 := add_le_add hinner_zw ht
      _ ≤ 3 / 2 * Cn := by
        have hρ1' : (ρ : ℝ) ≤ (1 : ℝ) := by exact_mod_cast hρ1
        have hrho : Cn * (ρ : ℝ) ≤ Cn := by
          simpa [mul_one] using mul_le_mul_of_nonneg_left hρ1' hCnonneg
        nlinarith
  have hnorm_perp : ∀ d : E, ‖d - (inner ℝ V.direction d) • V.direction‖ ≤ ‖d‖ := by
    intro d
    have hsq : ‖d - (inner ℝ V.direction d) • V.direction‖ ^ 2 ≤ ‖d‖ ^ 2 := by
      have hmain := norm_add_sq (𝕜 := ℝ) (x := (inner ℝ V.direction d) • V.direction)
        (y := d - (inner ℝ V.direction d) • V.direction)
      have hdecomp : d = (inner ℝ V.direction d) • V.direction +
          (d - (inner ℝ V.direction d) • V.direction) := by abel
      rw [← hdecomp] at hmain
      have hcross : inner ℝ ((inner ℝ V.direction d) • V.direction)
          (d - (inner ℝ V.direction d) • V.direction) = 0 := by
        have hsub : inner ℝ V.direction (d - (inner ℝ V.direction d) • V.direction) = 0 := by
          rw [inner_sub_right, inner_smul_right, he]
          ring
        simp [inner_smul_left, hsub]
      have hd : ‖d‖ ^ 2 = ‖(inner ℝ V.direction d) • V.direction‖ ^ 2 +
          ‖d - (inner ℝ V.direction d) • V.direction‖ ^ 2 := by
        rw [hmain, hcross]
        simp
      have hpe : ‖(inner ℝ V.direction d) • V.direction‖ ^ 2 = (inner ℝ V.direction d) ^ 2 := by
        rw [norm_smul, Real.norm_eq_abs, V.norm_direction, mul_one, sq_abs]
      nlinarith [hd, hpe, sq_nonneg (inner ℝ V.direction d)]
    have h := sq_le_sq.mp hsq
    simpa using h
  have hperp : z - V.center - inner ℝ V.direction (z - V.center) • V.direction
      = (z - w) - inner ℝ V.direction (z - w) • V.direction := by
    rw [hz_inner, hz_sub]
    module
  have htrans : ‖z - V.center - inner ℝ V.direction (z - V.center) • V.direction‖
      ≤ Cn * (ρ : ℝ) := by
    rw [hperp]
    exact le_trans (hnorm_perp (z - w)) hnorm_zw
  exact ⟨haxial, htrans⟩

/-- **Position and direction of a thin tube inside a thin dilate** (blueprint
`lem:endpointRegionMem`).

The three conclusions are the items (i)–(iii) of the blueprint lemma: the two core endpoints of
`U` have bounded axial coordinate, bounded transverse coordinate, and the direction of `U` is
within `2 C_n ρ` of the direction of `V`. -/
theorem parameters_mem_of_subset_dilate {σ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hσρ : σ ≤ ρ)
    (V : Tube ρ E) (U : Tube σ E)
    (hU : U.carrier ⊆ (Kakeya.Tube.dilate V
      (Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E))).carrier) :
    (|inner ℝ (U.x - V.center) V.direction|
          ≤ 3 / 2 * Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) ∧
        |inner ℝ (U.y - V.center) V.direction|
          ≤ 3 / 2 * Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E)) ∧
      (‖U.x - V.center - inner ℝ V.direction (U.x - V.center) • V.direction‖
          ≤ Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) * (ρ : ℝ) ∧
        ‖U.y - V.center - inner ℝ V.direction (U.y - V.center) • V.direction‖
          ≤ Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) * (ρ : ℝ)) ∧
      ‖U.direction - inner ℝ V.direction U.direction • V.direction‖
        ≤ 2 * Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) * (ρ : ℝ) := by
  have hxU : U.x ∈ U.carrier := x_mem_carrier U
  have hyU : U.y ∈ U.carrier := y_mem_carrier U
  have hx : U.x ∈ (Kakeya.Tube.dilate V
      (Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E))).carrier := hU hxU
  have hy : U.y ∈ (Kakeya.Tube.dilate V
      (Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E))).carrier := hU hyU
  have hxbl := inner_and_perp_le_of_mem_dilate hρ0 hρ1 V hx
  have hybl := inner_and_perp_le_of_mem_dilate hρ0 hρ1 V hy
  have hxax : |inner ℝ (U.x - V.center) V.direction|
      ≤ 3 / 2 * Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) := hxbl.1
  have hyax : |inner ℝ (U.y - V.center) V.direction|
      ≤ 3 / 2 * Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) := hybl.1
  have hxpn : ‖U.x - V.center - inner ℝ V.direction (U.x - V.center) • V.direction‖
      ≤ Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) * (ρ : ℝ) := hxbl.2
  have hypn : ‖U.y - V.center - inner ℝ V.direction (U.y - V.center) • V.direction‖
      ≤ Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) * (ρ : ℝ) := hybl.2
  have hdir : ‖U.direction - inner ℝ V.direction U.direction • V.direction‖
      ≤ 2 * Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) * (ρ : ℝ) := by
    calc
      ‖U.direction - inner ℝ V.direction U.direction • V.direction‖
          = ‖(U.y - V.center - (inner ℝ V.direction (U.y - V.center)) • V.direction) -
              (U.x - V.center - (inner ℝ V.direction (U.x - V.center)) • V.direction)‖ := by
            congr 1
            change (U.y - U.x) - inner ℝ V.direction (U.y - U.x) • V.direction = _
            rw [inner_sub_right, inner_sub_right, inner_sub_right]
            module
      _ ≤ ‖U.y - V.center - (inner ℝ V.direction (U.y - V.center)) • V.direction‖ +
          ‖U.x - V.center - (inner ℝ V.direction (U.x - V.center)) • V.direction‖ :=
            norm_sub_le _ _
      _ ≤ 2 * Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) * (ρ : ℝ) := by
            linarith
  exact ⟨⟨hxax, hyax⟩, ⟨hxpn, hypn⟩, hdir⟩

/-- **Position and direction of a thin tube inside a dilate at an arbitrary ratio**, the free-ratio
form of `Tube.parameters_mem_of_subset_dilate`.

Items (i)–(iii) of blueprint `lem:endpointRegionMem` with the fixed ratio `C_n` replaced by a free
`D > 0`, which is what the parameter-space count needs in order to run at the free ratio of
`Tube.essDistinctTubesInSelfDilate` rather than at `C_n`.  It is the first of the declarations of
the free-ratio group of `section8_genkf.tex`: the fixed-ratio statement cannot be cited at a free
ratio in either direction, since a smaller ratio weakens the containment hypothesis while a larger
one weakens the conclusion.

Two hypotheses of the fixed-ratio form are absent because they are not used: `ρ ≤ 1`, which there
converts `C_n / 2 + C_n ρ` into the displayed `3 C_n / 2`, and `σ ≤ ρ`.  Consequently this
statement implies the fixed-ratio one at `D = C_n` whenever `ρ ≤ 1`, and does not need the
`1 < C_n` of `Kakeya.Tube.tubeOverlapCoreClose`: the ratio enters only through
`Tube.abs_inner_and_perp_le_of_mem_dilate`, which is stated at a free ratio already. -/
theorem parameters_mem_of_subset_dilate_free {σ : NNReal} {D : ℝ} (hD : 0 < D)
    (V : Tube ρ E) (U : Tube σ E)
    (hU : U.carrier ⊆ (Kakeya.Tube.dilate V D).carrier) :
    (|inner ℝ (U.x - V.center) V.direction| ≤ D / 2 + D * (ρ : ℝ) ∧
        |inner ℝ (U.y - V.center) V.direction| ≤ D / 2 + D * (ρ : ℝ)) ∧
      (‖U.x - V.center - inner ℝ V.direction (U.x - V.center) • V.direction‖ ≤ D * (ρ : ℝ) ∧
        ‖U.y - V.center - inner ℝ V.direction (U.y - V.center) • V.direction‖ ≤ D * (ρ : ℝ)) ∧
      ‖U.direction - inner ℝ V.direction U.direction • V.direction‖ ≤ 2 * D * (ρ : ℝ) := by
  have hxU : U.x ∈ U.carrier := x_mem_carrier U
  have hyU : U.y ∈ U.carrier := y_mem_carrier U
  have hxbl := abs_inner_and_perp_le_of_mem_dilate (T := V) (c := D) hD (hU hxU)
  have hybl := abs_inner_and_perp_le_of_mem_dilate (T := V) (c := D) hD (hU hyU)
  have hdir : ‖U.direction - inner ℝ V.direction U.direction • V.direction‖
      ≤ 2 * D * (ρ : ℝ) := by
    calc
      ‖U.direction - inner ℝ V.direction U.direction • V.direction‖
          = ‖(U.y - V.center - (inner ℝ V.direction (U.y - V.center)) • V.direction) -
              (U.x - V.center - (inner ℝ V.direction (U.x - V.center)) • V.direction)‖ := by
            congr 1
            change (U.y - U.x) - inner ℝ V.direction (U.y - U.x) • V.direction = _
            rw [inner_sub_right, inner_sub_right, inner_sub_right]
            module
      _ ≤ ‖U.y - V.center - (inner ℝ V.direction (U.y - V.center)) • V.direction‖ +
          ‖U.x - V.center - (inner ℝ V.direction (U.x - V.center)) • V.direction‖ :=
            norm_sub_le _ _
      _ ≤ 2 * D * (ρ : ℝ) := by linarith [hxbl.2, hybl.2]
  exact ⟨⟨hxbl.1, hybl.1⟩, ⟨hxbl.2, hybl.2⟩, hdir⟩

/-! ### Axial slides -/

/-- **Comparing the neighbourhoods of two segments with close endpoints** (blueprint
`lem:segmentEndpointCthickening`). -/
theorem _root_.Metric.cthickening_segment_subset_cthickening_segment {p₁ q₁ p₂ q₂ : E}
    {ε r : ℝ} (hε : 0 ≤ ε) (hr : 0 ≤ r) (hp : dist p₁ p₂ ≤ ε) (hq : dist q₁ q₂ ≤ ε) :
    cthickening r (segment ℝ p₁ q₁) ⊆ cthickening (r + ε) (segment ℝ p₂ q₂) := by
  have hseg : segment ℝ p₁ q₁ ⊆ cthickening ε (segment ℝ p₂ q₂) := by
    rintro w hw
    rcases (segment_eq_image_lineMap ℝ p₁ q₁).symm ▸ hw with ⟨t, ht, rfl⟩
    have hw' : AffineMap.lineMap p₂ q₂ t ∈ segment ℝ p₂ q₂ :=
      lineMap_mem_segment ℝ p₂ q₂ ht
    have ht0 : 0 ≤ t := ht.1
    have ht1 : t ≤ 1 := ht.2
    have h1t0 : 0 ≤ 1 - t := by linarith
    have hdist : dist (AffineMap.lineMap p₁ q₁ t) (AffineMap.lineMap p₂ q₂ t) ≤ ε := by
      calc
        dist (AffineMap.lineMap p₁ q₁ t) (AffineMap.lineMap p₂ q₂ t)
            = ‖AffineMap.lineMap p₁ q₁ t - AffineMap.lineMap p₂ q₂ t‖ := dist_eq_norm _ _
        _ = ‖((1 - t) • p₁ + t • q₁) - ((1 - t) • p₂ + t • q₂)‖ := by
          simp [AffineMap.lineMap_apply_module]
        _ = ‖(1 - t) • (p₁ - p₂) + t • (q₁ - q₂)‖ := by
          congr 1
          rw [smul_sub, smul_sub]
          abel
        _ ≤ ‖(1 - t) • (p₁ - p₂)‖ + ‖t • (q₁ - q₂)‖ := norm_add_le _ _
        _ = |1 - t| * ‖p₁ - p₂‖ + |t| * ‖q₁ - q₂‖ := by simp [norm_smul]
        _ = (1 - t) * ‖p₁ - p₂‖ + t * ‖q₁ - q₂‖ := by
          simp [abs_of_nonneg ht0, abs_of_nonneg h1t0]
        _ = (1 - t) * dist p₁ p₂ + t * dist q₁ q₂ := by simp [dist_eq_norm]
        _ ≤ (1 - t) * ε + t * ε := by
          exact add_le_add (mul_le_mul_of_nonneg_left hp h1t0)
            (mul_le_mul_of_nonneg_left hq ht0)
        _ = ε := by ring
    exact mem_cthickening_of_dist_le (α := E) _ _ ε _ hw' hdist
  calc
    cthickening r (segment ℝ p₁ q₁) ⊆ cthickening r (cthickening ε (segment ℝ p₂ q₂)) :=
      Metric.cthickening_subset_of_subset r hseg
    _ ⊆ cthickening (r + ε) (segment ℝ p₂ q₂) :=
      Metric.cthickening_cthickening_subset hr hε (segment ℝ p₂ q₂)

/-- **A shrunken copy of a segment inside the segment and inside its axial translate**
(blueprint `lem:slideSegmentHomothety`).

The map `h z = p + α⁺ • (q - p) + lam • (z - p)` is affine with linear part `lam • id` — for
`lam < 1` it is the homothety of ratio `lam` centred at `p + (1 - lam)⁻¹ α⁺ • (q - p)` — and it
carries `[p, q]` into the intersection of `[p, q]` with its translate by `α • (q - p)`.  The
volume law `|h A| = lam ^ n |A|` is `MeasureTheory.Measure.addHaar_image_homothety` and is not
restated here. -/
theorem _root_.segment_homothety_subset_inter_translate {p q : E} (hpq : dist p q = 1) (α : ℝ)
    {lam : ℝ} (hlam : 0 < lam) (hlam' : lam ≤ 1 - |α|) :
    (fun z => p + max α 0 • (q - p) + lam • (z - p)) '' segment ℝ p q
      ⊆ segment ℝ p q ∩ (fun z => z + α • (q - p)) '' segment ℝ p q := by
  rw [segment_eq_image' ℝ p q]
  intro x hx
  rw [Set.mem_inter_iff]
  rcases hx with ⟨z, hz, hxt⟩
  rcases hz with ⟨t, ht, hzt⟩
  subst hzt
  set s : ℝ := max α 0 + lam * t
  have hx' : p + s • (q - p) = x := by
    rw [← hxt]
    dsimp [s]
    rw [show (p + t • (q - p)) - p = t • (q - p) by abel]
    rw [add_smul, smul_smul, add_assoc]
  constructor
  · refine ⟨s, ?_, hx'⟩
    constructor
    · dsimp [s]
      have hma : 0 ≤ max α 0 := le_max_right α 0
      have hmul : 0 ≤ lam * t := mul_nonneg (le_of_lt hlam) ht.1
      linarith
    · dsimp [s]
      have ho : max α 0 ≤ |α| := max_le (le_abs_self α) (abs_nonneg α)
      have hmt : lam * t ≤ lam := mul_le_of_le_one_right (le_of_lt hlam) ht.2
      linarith
  · rw [← Set.image_comp]
    refine ⟨s - α, ?_, ?_⟩
    · constructor
      · dsimp [s]
        have hA : α ≤ max α 0 := le_max_left α 0
        have hmul : 0 ≤ lam * t := mul_nonneg (le_of_lt hlam) ht.1
        linarith
      · dsimp [s]
        rcases lt_or_ge α 0 with hα | hα
        · have ha_eq : max α 0 = 0 := max_eq_right (le_of_lt hα)
          have hmt : lam * t ≤ lam := mul_le_of_le_one_right (le_of_lt hlam) ht.2
          rw [show |α| = -α by exact abs_of_neg hα] at hlam'
          ring_nf at hlam'
          linarith [ha_eq]
        · have ha_eq : max α 0 = α := max_eq_left hα
          have hmt : lam * t ≤ lam := mul_le_of_le_one_right (le_of_lt hlam) ht.2
          have habs : 0 ≤ |α| := abs_nonneg α
          linarith
    · rw [← hx']
      change (p + (s - α) • (q - p)) + α • (q - p) = p + s • (q - p)
      rw [add_assoc, ← add_smul, sub_add_cancel]

/-- **A thin neighbourhood of a piece of the core lies in the tube** (blueprint
`lem:tubeSlideCoreSubsetSelf`).  The radius `r` is free up to `σ`; the two monotonicities of
`Metric.cthickening` (in the set and in the radius) give the containment. -/
theorem cthickening_subset_of_subset_segment {σ : NNReal} (U : Tube σ E) {A : Set E}
    (hA : A ⊆ segment ℝ U.x U.y) {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ (σ : ℝ)) :
    cthickening r A ⊆ U.carrier := by
  rw [U.carrier_eq_cthickening]
  exact (Metric.cthickening_subset_of_subset r hA).trans
    (Metric.cthickening_mono hr (segment ℝ U.x U.y))

/-- **A thin neighbourhood of a piece of the slid core lies in the slid tube** (blueprint
`lem:tubeSlideCoreSubsetSlid`).

Here `c_* = 1 / (4 n)` and `λ = 1 - c_*`.  The budget balances exactly:
`λ σ + c_* σ = σ`, so the thickening lands on `U'` itself and not on a strictly larger
neighbourhood.  This is why the lemma is stated at the single radius `λ σ`. -/
theorem cthickening_subset_of_subset_translate_segment {σ : NNReal} (U' : Tube σ E) {A : Set E}
    {p q f : E} {α : ℝ}
    (hA : A ⊆ (fun z => z + α • f) '' segment ℝ p q)
    (hp : dist U'.x (p + α • f) ≤ 1 / (4 * (Module.finrank ℝ E : ℝ)) * (σ : ℝ))
    (hq : dist U'.y (q + α • f) ≤ 1 / (4 * (Module.finrank ℝ E : ℝ)) * (σ : ℝ)) :
    cthickening ((1 - 1 / (4 * (Module.finrank ℝ E : ℝ))) * (σ : ℝ)) A ⊆ U'.carrier := by
  let cstar : ℝ := 1 / (4 * (Module.finrank ℝ E : ℝ))
  let lam : ℝ := 1 - cstar
  have hnR0 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by
    exact_mod_cast Nat.zero_le (Module.finrank ℝ E)
  have hσ0 : 0 ≤ (σ : ℝ) := σ.property
  have hcstar0 : 0 ≤ cstar := by
    dsimp [cstar]
    exact div_nonneg (by norm_num) (mul_nonneg (by norm_num) hnR0)
  have hcstar_le_one : cstar ≤ 1 := by
    dsimp [cstar]
    by_cases hz : (Module.finrank ℝ E : ℝ) = 0
    · simp [hz]
    · have hnpos : (0 : ℝ) < (Module.finrank ℝ E : ℝ) := by
        exact lt_of_le_of_ne hnR0 (by simpa [eq_comm] using hz)
      have hnR : (1 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by
        have hn_nat : Module.finrank ℝ E ≠ 0 := by
          exact_mod_cast hz
        exact_mod_cast (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn_nat))
      rw [div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 4) hnpos)]
      nlinarith [hnR]
  have hlam0 : 0 ≤ lam := by dsimp [lam]; linarith
  have hlamσ : 0 ≤ lam * (σ : ℝ) := mul_nonneg hlam0 hσ0
  have hεσ : 0 ≤ cstar * (σ : ℝ) := mul_nonneg hcstar0 hσ0
  have hAseg : A ⊆ segment ℝ (p + α • f) (q + α • f) := by
    rw [← segment_add_right_image p q (α • f)]
    exact hA
  have h2 : cthickening (lam * (σ : ℝ)) A
      ⊆ cthickening (lam * (σ : ℝ) + cstar * (σ : ℝ)) (segment ℝ U'.x U'.y) := by
    exact (Metric.cthickening_subset_of_subset (lam * (σ : ℝ)) hAseg).trans
      (Metric.cthickening_segment_subset_cthickening_segment
        (p₁ := p + α • f) (q₁ := q + α • f) (p₂ := U'.x) (q₂ := U'.y)
        (ε := cstar * (σ : ℝ)) (r := lam * (σ : ℝ))
        hεσ hlamσ (by simpa [cstar, dist_comm] using hp)
          (by simpa [cstar, dist_comm] using hq))
  have hrad : lam * (σ : ℝ) + cstar * (σ : ℝ) = (σ : ℝ) := by dsimp [lam]; ring
  rw [hrad] at h2
  rwa [← U'.carrier_eq_cthickening] at h2

/-- **A shrunken core common to a tube and its axial slide** (blueprint
`lem:tubeSlideCommonCore`).

`S = h '' [p_U, q_U]` is the image of the core under the map
`h z = p_U + α⁺ • f_U + λ • (z - p_U)` of `segment_homothety_subset_inter_translate`, with
`λ = 1 - c_*` and `α⁺ = max α 0`.  Its `λ σ`-neighbourhood lies in both tubes:
`Tube.cthickening_subset_of_subset_segment` puts it in `U` and
`Tube.cthickening_subset_of_subset_translate_segment` puts it in `U'`. -/
theorem cthickening_slideCore_subset_inter {σ : NNReal} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1)
    (U U' : Tube σ E) {α : ℝ} (hα : |α| ≤ 1 / (4 * (Module.finrank ℝ E : ℝ)))
    (hp : dist U'.x (U.x + α • U.direction) ≤ 1 / (4 * (Module.finrank ℝ E : ℝ)) * (σ : ℝ))
    (hq : dist U'.y (U.y + α • U.direction) ≤ 1 / (4 * (Module.finrank ℝ E : ℝ)) * (σ : ℝ)) :
    cthickening ((1 - 1 / (4 * (Module.finrank ℝ E : ℝ))) * (σ : ℝ))
        ((fun z => U.x + max α 0 • (U.y - U.x)
            + (1 - 1 / (4 * (Module.finrank ℝ E : ℝ))) • (z - U.x)) '' segment ℝ U.x U.y)
      ⊆ U.carrier ∩ U'.carrier := by
  let lam : ℝ := 1 - 1 / (4 * (Module.finrank ℝ E : ℝ))
  let cstar : ℝ := 1 / (4 * (Module.finrank ℝ E : ℝ))
  change cthickening (lam * (σ : ℝ))
      ((fun z => U.x + max α 0 • (U.y - U.x) + lam • (z - U.x)) '' segment ℝ U.x U.y)
    ⊆ U.carrier ∩ U'.carrier
  set S : Set E := (fun z => U.x + max α 0 • (U.y - U.x) + lam • (z - U.x)) '' segment ℝ U.x U.y
  have hσ0' : 0 ≤ (σ : ℝ) := σ.property
  have hnR0 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by
    exact_mod_cast Nat.zero_le (Module.finrank ℝ E)
  have hcstar0 : 0 ≤ cstar := by
    dsimp [cstar]
    exact div_nonneg (by norm_num) (mul_nonneg (by norm_num) hnR0)
  have hcstar_lt_one : cstar < 1 := by
    dsimp [cstar]
    by_cases hz : (Module.finrank ℝ E : ℝ) = 0
    · simp [hz]
    · have hnpos : (0 : ℝ) < (Module.finrank ℝ E : ℝ) := by
        exact lt_of_le_of_ne hnR0 (by simpa [eq_comm] using hz)
      have hnR : (1 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by
        have hn_nat : Module.finrank ℝ E ≠ 0 := by
          exact_mod_cast hz
        exact_mod_cast (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn_nat))
      rw [div_lt_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 4) hnpos)]
      nlinarith [hnR]
  have hlam_pos : 0 < lam := by dsimp [lam]; linarith
  have hlam0 : 0 ≤ lam := le_of_lt hlam_pos
  have hlam_le_one : lam ≤ 1 := by dsimp [lam]; linarith
  have hlam' : lam ≤ 1 - |α| := by dsimp [lam]; linarith [hα]
  have hud : dist U.x U.y = 1 := U.dist_eq_one
  have hS_sub :
      S ⊆ segment ℝ U.x U.y ∩ (fun z => z + α • U.direction) '' segment ℝ U.x U.y := by
    have h1 := segment_homothety_subset_inter_translate (p := U.x) (q := U.y) (α := α)
      (lam := lam) hud hlam_pos hlam'
    simpa [S] using h1
  have hSl : S ⊆ segment ℝ U.x U.y := hS_sub.trans Set.inter_subset_left
  have hSr : S ⊆ (fun z => z + α • U.direction) '' segment ℝ U.x U.y :=
    hS_sub.trans Set.inter_subset_right
  have hrle : lam * (σ : ℝ) ≤ (σ : ℝ) := by nlinarith [hlam_le_one, hσ0']
  have hU1 : cthickening (lam * (σ : ℝ)) S ⊆ U.carrier := by
    exact (Metric.cthickening_subset_of_subset (lam * (σ : ℝ)) hSl).trans
      (cthickening_subset_of_subset_segment (U := U) (A := segment ℝ U.x U.y)
        (r := lam * (σ : ℝ)) Subset.rfl (mul_nonneg hlam0 hσ0') hrle)
  have hU2 : cthickening (lam * (σ : ℝ)) S ⊆ U'.carrier := by
    exact cthickening_subset_of_subset_translate_segment (U' := U') (p := U.x) (q := U.y)
      (f := U.direction) (α := α) hSr hp hq
  exact Set.subset_inter hU1 hU2

/-- **Volume of the common core** (blueprint `lem:tubeSlideCommonCoreVolume`).

The map `h` of `Tube.cthickening_slideCore_subset_inter` is the homothety of ratio
`λ = 1 - c_*` centred at `p_U + (1 - λ)⁻¹ α⁺ f_U` (`eq_homothety_of_smul_sub`), so
`Metric.image_cthickening_homothety` identifies `S ^ (λ σ)` with `h '' U` and
`MeasureTheory.Measure.addHaar_image_homothety` multiplies the volume by `λ ^ n`. -/
theorem volume_cthickening_slideCore [Nontrivial E] {σ : NNReal} (U : Tube σ E) (α : ℝ) :
    volume (cthickening ((1 - 1 / (4 * (Module.finrank ℝ E : ℝ))) * (σ : ℝ))
        ((fun z => U.x + max α 0 • (U.y - U.x)
            + (1 - 1 / (4 * (Module.finrank ℝ E : ℝ))) • (z - U.x)) '' segment ℝ U.x U.y))
      = ENNReal.ofReal ((1 - 1 / (4 * (Module.finrank ℝ E : ℝ))) ^ Module.finrank ℝ E)
        * volume U.carrier := by
  set lam : ℝ := 1 - 1 / (4 * (Module.finrank ℝ E : ℝ))
  have hn_pos : 0 < Module.finrank ℝ E := Module.finrank_pos (R := ℝ) (M := E)
  have hlam1 : lam < 1 := by
    dsimp [lam]
    have hpos : (0 : ℝ) < 1 / (4 * (Module.finrank ℝ E : ℝ)) := by positivity
    linarith
  have hlam : 0 < lam := by
    dsimp [lam]
    have hn1 : (1 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt hn_pos)
    have h4pos : 0 < 4 * (Module.finrank ℝ E : ℝ) := by positivity
    have hlt : 1 / (4 * (Module.finrank ℝ E : ℝ)) < 1 := by
      rw [div_lt_iff₀ h4pos]
      nlinarith
    linarith
  have hs0 : 0 ≤ (σ : ℝ) := NNReal.coe_nonneg σ
  have hfun : (fun z => U.x + max α 0 • (U.y - U.x) + lam • (z - U.x))
      = ⇑(AffineMap.homothety (U.x + (1 - lam)⁻¹ • (max α 0 • (U.y - U.x))) lam) := by
    exact eq_homothety_of_smul_sub U.x (max α 0 • (U.y - U.x)) hlam1
  have himg : (fun z => U.x + max α 0 • (U.y - U.x) + lam • (z - U.x))
          '' segment ℝ U.x U.y
      = AffineMap.homothety (U.x + (1 - lam)⁻¹ • (max α 0 • (U.y - U.x))) lam
          '' segment ℝ U.x U.y := by
    rw [hfun]
  calc
    volume (cthickening (lam * (σ : ℝ))
        ((fun z => U.x + max α 0 • (U.y - U.x) + lam • (z - U.x)) '' segment ℝ U.x U.y))
        = volume (cthickening (lam * (σ : ℝ))
            (AffineMap.homothety (U.x + (1 - lam)⁻¹ • (max α 0 • (U.y - U.x))) lam
              '' segment ℝ U.x U.y)) := by
            rw [himg]
    _ = volume (AffineMap.homothety (U.x + (1 - lam)⁻¹ • (max α 0 • (U.y - U.x))) lam
            '' cthickening (σ : ℝ) (segment ℝ U.x U.y)) := by
            rw [← Metric.image_cthickening_homothety
              (U.x + (1 - lam)⁻¹ • (max α 0 • (U.y - U.x))) hlam hs0 (segment ℝ U.x U.y)]
    _ = volume (AffineMap.homothety (U.x + (1 - lam)⁻¹ • (max α 0 • (U.y - U.x))) lam
            '' U.carrier) := by
            rw [U.carrier_eq_cthickening]
    _ = ENNReal.ofReal (abs (lam ^ Module.finrank ℝ E)) * volume U.carrier := by
            simp [MeasureTheory.Measure.addHaar_image_homothety]
    _ = ENNReal.ofReal (lam ^ Module.finrank ℝ E) * volume U.carrier := by
            congr 1
            exact congrArg ENNReal.ofReal (abs_of_nonneg (pow_nonneg hlam.le _))

/-- **Two tubes of the same scale have the same volume** (blueprint
`lem:tubeVolumeIndependentOfPosition`).

Both carriers are the `δ`-neighbourhoods of their cores, and both cores have length one
(`Tube.dist_eq_one`), so `exists_affineIsometryEquiv_image_segment_eq` supplies a rigid motion
carrying one core to the other; it commutes with `Metric.cthickening`
(`Metric.image_cthickening_isometryEquiv`) and preserves volume
(`AffineIsometryEquiv.measurePreserving`).

The repository has only the two crude one-sided bounds `Tube.le_volume` and
`Tube.volume_le`, whose ratio is far from `1`; they cannot replace this equality, which
is what lets `Tube.not_essDistinct_of_axial_slide` control the maximum in
`IsEssentiallyDistinct`. -/
theorem volume_carrier_eq_volume_carrier {δ : NNReal} (T T' : Tube δ E) :
    volume T.carrier = volume T'.carrier := by
  have hnorm : ‖T.y - T.x‖ = ‖T'.y - T'.x‖ := by
    rw [← dist_eq_norm, ← dist_eq_norm]
    rw [dist_comm, T.dist_eq_one, dist_comm, T'.dist_eq_one]
  obtain ⟨Φ, hpx, hpy, hseg⟩ :=
    exists_affineIsometryEquiv_image_segment_eq (p := T.x) (q := T.y) (p' := T'.x) (q' := T'.y)
      hnorm
  have hseg' : Φ.toIsometryEquiv '' segment ℝ T.x T.y = segment ℝ T'.x T'.y := by
    simpa using hseg
  have hcar : Φ.toIsometryEquiv '' T.carrier = T'.carrier := by
    rw [T.carrier_eq_cthickening, T'.carrier_eq_cthickening]
    rw [image_cthickening_isometryEquiv Φ.toIsometryEquiv (δ : ℝ) (segment ℝ T.x T.y)]
    exact congrArg (cthickening (δ : ℝ)) hseg'
  have hpre_eq : Φ ⁻¹' T'.carrier = T.carrier := by
    rw [← hcar]
    simpa using (Φ.toIsometryEquiv.toEquiv.injective.preimage_image T.carrier)
  have hvol' : volume (Φ ⁻¹' T'.carrier) = volume T'.carrier :=
    (AffineIsometryEquiv.measurePreserving Φ).measure_preimage
      (T'.isCompact.isClosed.measurableSet.nullMeasurableSet)
  rw [← hpre_eq]
  exact hvol'

/-- **A tube has positive finite volume** (blueprint `lem:tubeVolumePosLtTop`): positivity from
`Tube.le_volume`, finiteness because the carrier is compact.

**`hσ1 : σ ≤ 1` is dead and its deletion is owed.**  Neither input constrains the radius from
above: `Tube.le_volume` asks nothing of it at all, and finiteness is compactness.  The
binder is therefore a spurious demand that this lemma passes on to every consumer, and it has
already cost one downstream statement a dead hypothesis of its own — see the docstring of
`Tube.mul_sum_volume_le_iff_mul_card_le`, which for that reason reassembles the two facts
instead of citing this lemma.  Deleting it is a one-line edit here plus the `_hσ1` line of the
proof, with call sites to repair in this file (`Tube.not_essDistinct_of_axial_slide`) and in
`Kakeya/DimensionThree/MainLemma1/Rescaling/AnchorDenominator.lean`
(`Kakeya.ml1Boot.volume_testedBody_bracket`, whose surviving `Λθ ≤ 1` is still needed there by
`Tube.volume_le` and whose docstring claim that *finiteness* needs `0 < Λθ ≤ 1` must be
corrected in the same edit).  It is not performed here because it requires a build to confirm that
those are the only call sites. -/
theorem volume_pos_and_lt_top [Nontrivial E] {σ : NNReal} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1)
    (U : Tube σ E) : 0 < volume U.carrier ∧ volume U.carrier < ⊤ := by
  set n := Module.finrank ℝ E with hn_def
  -- `σ ≤ 1` is part of the API but not needed in the proof (`le_volume` and compactness
  -- alone already give positivity and finiteness).
  have _hσ1 : σ ≤ 1 := hσ1
  have hc0 : (le_volume.c n : ENNReal) ≠ 0 :=
    (ENNReal.coe_pos.mpr (le_volume.c_pos n)).ne'
  have hσe0 : (σ : ENNReal) ≠ 0 := (ENNReal.coe_pos.mpr hσ0).ne'
  have hpow0 : (σ : ENNReal) ^ (n - 1) ≠ 0 := pow_ne_zero (n - 1) hσe0
  have hpos : 0 < (le_volume.c n : ENNReal) * (σ : ENNReal) ^ (n - 1) :=
    lt_of_le_of_ne zero_le (Ne.symm (mul_ne_zero hc0 hpow0))
  constructor
  · exact lt_of_lt_of_le hpos (le_volume (E := E) (T := U) (δ := σ))
  · exact U.isCompact.measure_lt_top

/-- **The total volume of a family of equal-radius tubes** (blueprint
`lem:tubeFamilySumVolume`): the sum of the volumes of a finite family of `δ`-tubes is the
cardinality of the index set times the common volume, named by an arbitrary reference `δ`-tube.

Every summand equals `volume T₀.carrier` by `Tube.volume_carrier_eq_volume_carrier`, so this is
`Finset.sum_const`.

*Nothing at all is asked of `δ`*: at `δ = 0` both sides are the cardinality times the volume of
a unit segment, which vanishes in every ambient dimension `≥ 2`, and the identity is then the
vacuous one.  *And `T₀` is an arbitrary reference `δ`-tube, not required to be a member of the
family*: the volume of a `δ`-tube is a function of `δ` alone, so any `δ`-tube whatever may be
used to name the common value; supplying it is what lets the statement dispense with any
nonemptiness hypothesis on `s`.  Only `s` is asked to be finite; `ι` is arbitrary. -/
theorem sum_volume_carrier_eq_card_mul {δ : NNReal} {ι : Type*} (T : ι → Tube δ E)
    (T₀ : Tube δ E) (s : Finset ι) :
    ∑ i ∈ s, volume (T i).carrier = (s.card : ENNReal) * volume T₀.carrier := by
  rw [Finset.sum_eq_card_nsmul (fun i _ => volume_carrier_eq_volume_carrier (T i) T₀)]
  rw [nsmul_eq_mul]

/-- **For equal-radius tubes a volume share and a cardinality share hold at the same factor**
(blueprint `lem:tubeShareVolumeCard`).

Read at `c = κ`, `d = 1`, at `s` a family and at `r` a subfamily of it, the left-hand side is the
*volume* share `κ ∑_{i ∈ s} |T i| ≤ ∑_{i ∈ r} |T i|` and the right-hand side the *cardinality*
share `κ |s| ≤ |r|`: for tubes of one common radius the two hold **at the same** `κ`, with nothing
lost in the factor.  The statement is an equivalence, so either may be read off the other.

*Neither `r ⊆ s` nor any relation between the two index sets is asked*, and `ι` need not be
finite; only `s` and `r` are.  *The reference `δ`-tube `T₀` is a hypothesis and does not appear in
the conclusion*: exactly as in `Tube.sum_volume_carrier_eq_card_mul` its only office is to name
the common volume that is cancelled, and asking for it is what lets the statement dispense with
any nonemptiness hypothesis and the proof run without a case distinction.

*`0 < δ` is all that is asked of the radius, and `δ ≤ 1` is deliberately not asked.*  What is
cancelled is the common volume of `Tube.sum_volume_carrier_eq_card_mul`, and cancelling it needs
it positive and finite (`ENNReal.mul_le_mul_right`).  Finiteness is compactness of the carrier —
`ConvexSpaceBody.isCompact` and `IsCompact.measure_lt_top` — and asks nothing of the radius at all;
positivity is `Tube.le_volume`, which likewise constrains the radius only through
`0 < δ`.  So the intended proof takes those two facts directly rather than through
`Tube.volume_pos_and_lt_top`, which packages exactly them behind a spurious `δ ≤ 1` that
its own proof does not spend; relaxing that lemma is owed there, and after it this proof may cite
it instead of reassembling it.

*The one condition that is asked is not decorative.*  At `δ = 0` in an ambient dimension `≥ 2`
every `|T i|` vanishes, so the left-hand side reads `0 ≤ 0` at every `c` and `d` while the
right-hand side remains a genuine constraint on cardinalities: a consumer that deliberately
admits `δ = 0` cannot be restated with a volume share. -/
theorem mul_sum_volume_le_iff_mul_card_le [Nontrivial E] {δ : NNReal} (hδ0 : 0 < δ)
    {ι : Type*} (T : ι → Tube δ E) (T₀ : Tube δ E) {s r : Finset ι} {c d : ENNReal} :
    c * ∑ i ∈ s, volume (T i).carrier ≤ d * ∑ i ∈ r, volume (T i).carrier
      ↔ c * (s.card : ENNReal) ≤ d * (r.card : ENNReal) := by
  set n := Module.finrank ℝ E
  have hc0 : (le_volume.c n : ENNReal) ≠ 0 :=
    (ENNReal.coe_pos.mpr (le_volume.c_pos n)).ne'
  have hδ0' : (δ : ENNReal) ≠ 0 := (ENNReal.coe_pos.mpr hδ0).ne'
  have hpow0 : (δ : ENNReal) ^ (n - 1) ≠ 0 := pow_ne_zero (n - 1) hδ0'
  have hpos : (le_volume.c n : ENNReal) * (δ : ENNReal) ^ (n - 1) ≠ 0 :=
    mul_ne_zero hc0 hpow0
  have hVpos : 0 < volume T₀.carrier :=
    lt_of_lt_of_le (lt_of_le_of_ne zero_le (Ne.symm hpos))
      (le_volume (E := E) (T := T₀) (δ := δ))
  have hVne : volume T₀.carrier ≠ 0 := ne_of_gt hVpos
  have hVtop : volume T₀.carrier ≠ ⊤ := ne_of_lt T₀.isCompact.measure_lt_top
  have hsums : ∑ i ∈ s, volume (T i).carrier = (s.card : ENNReal) * volume T₀.carrier := by
    exact sum_volume_carrier_eq_card_mul T T₀ s
  have hsumr : ∑ i ∈ r, volume (T i).carrier = (r.card : ENNReal) * volume T₀.carrier := by
    exact sum_volume_carrier_eq_card_mul T T₀ r
  rw [hsums, hsumr]
  rw [← mul_assoc, ← mul_assoc]
  exact ENNReal.mul_le_mul_iff_left hVne hVtop

/-- **`(1 - 1 / (4 n)) ^ n ≥ 3 / 4`** (blueprint `lem:oneMinusQuarterPow`), the numerical claim
behind the endpoint separation constant `c_* = 1 / (4 n)`.  Mathlib states Bernoulli's
inequality only additively (`one_add_mul_le_pow`), so it is instantiated at `a = -1 / (4 n)`.

Blueprint `def:essDistinctTubeEndpointSeparation_constant` assigns this statement to
`Kakeya/Mathlib/Algebra/Div.lean`; that file is a `prelude` module importing only
`Init.Prelude`, so the lemma is stated here instead, next to its only two consumers. -/
theorem three_quarters_le_one_sub_cstar_pow {n : ℕ} (hn : 1 ≤ n) :
    (3 : ℝ) / 4 ≤ (1 - 1 / (4 * (n : ℝ))) ^ n := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnRpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le zero_lt_one hnR
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnRpos
  have hble : -2 ≤ -(1 / (4 * (n : ℝ))) := by
    rw [neg_le_neg_iff]
    have hm4pos : (0 : ℝ) < 4 * (n : ℝ) := mul_pos (by norm_num) hnRpos
    rw [div_le_iff₀ hm4pos]
    nlinarith [hnR]
  have hbern : 1 + (n : ℝ) * -(1 / (4 * (n : ℝ)))
      ≤ (1 + -(1 / (4 * (n : ℝ)))) ^ n :=
    one_add_mul_le_pow hble n
  have hsimpl : 1 + (n : ℝ) * -(1 / (4 * (n : ℝ))) = (3 : ℝ) / 4 := by
    field_simp [hn0]
    ring
  rwa [hsimpl] at hbern

/-- **A three-quarter overlap defeats essential distinctness** (blueprint
`lem:notEssDistinctOfThreeQuarters`).  This lemma carries the whole of the `[0, ∞]`-arithmetic:
the step `(1/2) |A| < (3/4) |A|` needs `|A| ≠ 0` and `|A| ≠ ∞` supplied explicitly. -/
theorem _root_.not_isEssentiallyDistinct_of_three_quarters_le {A A' : Set E}
    (hAA' : 3 / 4 * volume A ≤ volume (A ∩ A')) (hvol : volume A' = volume A)
    (hpos : 0 < volume A) (hfin : volume A < ⊤) :
    ¬ IsEssentiallyDistinct A A' := by
  intro hED
  have hmax : max (volume A) (volume A') = volume A := by
    rw [hvol, max_self]
  have hle : (3 / 4 : ENNReal) * volume A ≤ (1 / 2 : ENNReal) * volume A := by
    calc
      (3 / 4 : ENNReal) * volume A ≤ volume (A ∩ A') := hAA'
      _ ≤ (1 / 2 : ENNReal) * max (volume A) (volume A') := hED
      _ = (1 / 2 : ENNReal) * volume A := by rw [hmax]
  have hv0 : volume A ≠ 0 := ne_of_gt hpos
  have hvtop : volume A ≠ ⊤ := ne_of_lt hfin
  have h34r : ENNReal.ofReal (3 / 4 : ℝ) = (3 / 4 : ENNReal) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4)]
    simp
  have h12r : ENNReal.ofReal (1 / 2 : ℝ) = (1 / 2 : ENNReal) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    simp
  rw [ENNReal.mul_le_mul_iff_left hv0 hvtop] at hle
  have hbad : ¬ (3 / 4 : ENNReal) ≤ (1 / 2 : ENNReal) := by
    intro h
    rw [← h34r, ← h12r] at h
    have hℝ : (3 / 4 : ℝ) ≤ (1 / 2 : ℝ) :=
      (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 1 / 2)).mp h
    norm_num at hℝ
  exact False.elim (hbad hle)

/-- **An axial slide of a tube is not essentially distinct from it** (blueprint
`lem:tubeAxialSlideOverlap`).

If the core of `U'` is, up to an error `c_* σ`, the core of `U` slid along its own direction by
`α` with `|α| ≤ c_* = 1 / (4 n)`, then `|U ∩ U'| ≥ (1 - c_*) ^ n |U| ≥ (3/4) |U|`, which
contradicts essential distinctness.  Blueprint `note:tubeAxialSlideOverlapRepair` records why
the range of `α` cannot be enlarged to `|α| ≤ 1/3`. -/
theorem not_essDistinct_of_axial_slide [Nontrivial E] {σ : NNReal} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1)
    (U U' : Tube σ E) {α : ℝ} (hα : |α| ≤ 1 / (4 * (Module.finrank ℝ E : ℝ)))
    (hp : dist U'.x (U.x + α • U.direction) ≤ 1 / (4 * (Module.finrank ℝ E : ℝ)) * (σ : ℝ))
    (hq : dist U'.y (U.y + α • U.direction) ≤ 1 / (4 * (Module.finrank ℝ E : ℝ)) * (σ : ℝ)) :
    ¬ IsEssentiallyDistinct U.carrier U'.carrier := by
  set n := Module.finrank ℝ E with hn_def
  set lam : ℝ := 1 - 1 / (4 * (n : ℝ))
  let S : Set E := (fun z => U.x + max α 0 • (U.y - U.x) + lam • (z - U.x)) '' segment ℝ U.x U.y
  have hn_one : 1 ≤ n := by
    rw [hn_def]
    exact Module.finrank_pos (R := ℝ) (M := E)
  -- inclusion into the intersection
  have h_sub : cthickening (lam * (σ : ℝ)) S ⊆ U.carrier ∩ U'.carrier := by
    simpa [S, lam, hn_def] using (cthickening_slideCore_subset_inter hσ0 hσ1 U U' hα hp hq)
  have hvol_le : volume (cthickening (lam * (σ : ℝ)) S) ≤ volume (U.carrier ∩ U'.carrier) :=
    measure_mono h_sub
  -- volume of the shrunken core
  have hvol_core : volume (cthickening (lam * (σ : ℝ)) S)
      = ENNReal.ofReal (lam ^ n) * volume U.carrier := by
    simpa [S, lam, hn_def] using (volume_cthickening_slideCore (U := U) (α := α))
  -- numerical bound
  have h34r : ENNReal.ofReal (3 / 4 : ℝ) = (3 / 4 : ENNReal) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4)]
    simp
  have hlam_ge : (3 / 4 : ENNReal) ≤ ENNReal.ofReal (lam ^ n) := by
    have hR : (3 : ℝ) / 4 ≤ lam ^ n := by
      simpa [lam] using three_quarters_le_one_sub_cstar_pow hn_one
    rw [← h34r]
    exact ENNReal.ofReal_le_ofReal hR
  -- chain of inequalities
  have hAA' : (3 / 4 : ENNReal) * volume U.carrier ≤ volume (U.carrier ∩ U'.carrier) := by
    calc
      (3 / 4 : ENNReal) * volume U.carrier ≤ ENNReal.ofReal (lam ^ n) * volume U.carrier := by
        gcongr
      _ = volume (cthickening (lam * (σ : ℝ)) S) := hvol_core.symm
      _ ≤ volume (U.carrier ∩ U'.carrier) := hvol_le
  -- the three hypotheses of not_isEssentiallyDistinct_of_three_quarters_le
  have hvol : volume U'.carrier = volume U.carrier :=
    (volume_carrier_eq_volume_carrier U U').symm
  have hpos : 0 < volume U.carrier := (volume_pos_and_lt_top hσ0 hσ1 U).1
  have hfin : volume U.carrier < ⊤ := (volume_pos_and_lt_top hσ0 hσ1 U).2
  exact not_isEssentiallyDistinct_of_three_quarters_le hAA' hvol hpos hfin

/-! ### The rescaled parameter space -/

/-- **The axial resolution** `κ_{lem:essDistinctTubeAxialSeparation}(n, C) = c_* / (8 C C_n)
= 1 / (32 n C C_n)` (blueprint `def:essDistinctTubeAxialSeparationConstant`).

It depends only on the ambient dimension `n`, on the comparability constant `C` and on `C_n`,
and not on the scale `ρ`.  Since `C, C_n ≥ 1` it satisfies `κ ≤ c_* / 8`, so in particular
`κ / 4 ≤ c_*`, which is what `Tube.not_essDistinct_of_axial_slide` requires of the slide it is
applied to. -/
noncomputable abbrev axialSeparation.kappa (n : ℕ) (C : NNReal) : NNReal :=
  1 / (32 * (n : NNReal) * C * (Kakeya.Tube.tubeOverlapCoreClose.C n).toNNReal)

/-- **The real value of the axial resolution** (blueprint `lem:kappaValue`).

`Tube.axialSeparation.kappa` is an `NNReal` abbreviation containing a `Real.toNNReal`, so every
consumer needing its real value must discharge `max C_n 0 = C_n` and push the coercion through a
division.  This lemma does that once and for all; the two displayed forms are `c_* / (8 C C_n)`
and `1 / (32 n C C_n)`. -/
theorem axialSeparation.coe_kappa {n : ℕ} (hn : 1 ≤ n) {C : NNReal} (hC : 1 ≤ C) :
    (axialSeparation.kappa n C : ℝ)
        = 1 / (4 * (n : ℝ)) / (8 * (C : ℝ) * Kakeya.Tube.tubeOverlapCoreClose.C n) ∧
      (axialSeparation.kappa n C : ℝ)
        = 1 / (32 * (n : ℝ) * (C : ℝ) * Kakeya.Tube.tubeOverlapCoreClose.C n) ∧
      0 < (axialSeparation.kappa n C : ℝ) := by
  have hCn1 : 1 < Kakeya.Tube.tubeOverlapCoreClose.C n :=
    Kakeya.Tube.tubeOverlapCoreClose.one_lt_C n
  have hCn0 : 0 < Kakeya.Tube.tubeOverlapCoreClose.C n := lt_trans zero_lt_one hCn1
  have hCn_ne : Kakeya.Tube.tubeOverlapCoreClose.C n ≠ 0 := ne_of_gt hCn0
  have hC0 : (0 : NNReal) < C := lt_of_lt_of_le zero_lt_one hC
  have hC_ne : (C : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hC0
  have hC_posR : 0 < (C : ℝ) := by exact_mod_cast hC0
  have hn_pos : 0 < (n : ℝ) := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (by exact_mod_cast hn)
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
  have hmax : ((Kakeya.Tube.tubeOverlapCoreClose.C n).toNNReal : ℝ)
      = Kakeya.Tube.tubeOverlapCoreClose.C n :=
    Real.coe_toNNReal _ (le_of_lt hCn0)
  have hkn : (axialSeparation.kappa n C : ℝ)
      = 1 / (32 * (n : ℝ) * (C : ℝ) * Kakeya.Tube.tubeOverlapCoreClose.C n) := by
    simp [axialSeparation.kappa, hmax]
  constructor
  · calc
      (axialSeparation.kappa n C : ℝ)
          = 1 / (32 * (n : ℝ) * (C : ℝ) * Kakeya.Tube.tubeOverlapCoreClose.C n) := hkn
      _ = 1 / (4 * (n : ℝ)) / (8 * (C : ℝ) * Kakeya.Tube.tubeOverlapCoreClose.C n) := by
          field_simp [hn_ne, hC_ne, hCn_ne]
          ring
  constructor
  · exact hkn
  · rw [hkn]
    positivity

/-- The hyperplane `e^⊥` orthogonal to the core direction `e` of `V`, an inner product space of
dimension `n - 1`. -/
abbrev perpSpace (V : Tube ρ E) : Type _ := ↥((ℝ ∙ V.direction)ᗮ)

/-- **Dimension of the orthogonal complement of the core direction** (blueprint
`lem:perpSpaceFinrank`): `dim e^⊥ = n - 1`, since `‖e‖ = 1` gives `dim (ℝ ∙ e) = 1`.

Mathlib's `Submodule.finrank_orthogonal_span_singleton` states this under an instance hypothesis
`[Fact (finrank ℝ E = n + 1)]`, which would leak into every downstream statement quantifying
over `n`; the route through `finrank_span_singleton` and
`Submodule.finrank_add_finrank_orthogonal` avoids it. -/
theorem finrank_perpSpace (V : Tube ρ E) :
    Module.finrank ℝ (perpSpace V) = Module.finrank ℝ E - 1 := by
  have hVd : V.direction ≠ 0 := by
    exact norm_ne_zero_iff.mp (by rw [V.norm_direction]; norm_num)
  have hspan : Module.finrank ℝ (ℝ ∙ V.direction) = 1 :=
    finrank_span_singleton hVd
  have hadd : Module.finrank ℝ (ℝ ∙ V.direction) + Module.finrank ℝ ((ℝ ∙ V.direction)ᗮ)
      = Module.finrank ℝ E :=
    Submodule.finrank_add_finrank_orthogonal (ℝ ∙ V.direction)
  rw [hspan] at hadd
  change Module.finrank ℝ ((ℝ ∙ V.direction)ᗮ) = Module.finrank ℝ E - 1
  omega

/-- **Volume of a ball in the transverse space** (blueprint `lem:perpSpaceBallVolume`):
`|B̄_{e^⊥}(0, r)| = ofReal (ω_{n-1} r ^ (n-1))` with `ω_d = 2 ^ d · C_cov d`.

For `n ≥ 2` this is `Metric.volume_closedBall_eq_ccov_mul_pow` in `e^⊥`, which is then
nontrivial; for `n = 1` the space `e^⊥` is zero-dimensional and both sides equal `1`, by
`Metric.volume_closedBall_of_finrank_eq_zero` and `C_cov 0 = 1`. -/
theorem volume_closedBall_perpSpace (V : Tube ρ E) {r : ℝ} (hr : 0 ≤ r) :
    volume (Metric.closedBall (0 : perpSpace V) r)
      = ENNReal.ofReal ((2 : ℝ) ^ (Module.finrank ℝ E - 1)
          * (Metric.coveringNumber_mul_pow_le_volume_cthickening.C (Module.finrank ℝ E - 1) : ℝ)
          * r ^ (Module.finrank ℝ E - 1)) := by
  set n : ℕ := Module.finrank ℝ E with hn_def
  have hVne : V.direction ≠ 0 := by
    exact norm_ne_zero_iff.mp (by rw [V.norm_direction]; norm_num)
  haveI : Nontrivial E := ⟨0, V.direction, hVne.symm⟩
  have hn_pos : 0 < n := by
    rw [hn_def]
    exact Module.finrank_pos (R := ℝ) (M := E)
  have hperp : Module.finrank ℝ (perpSpace V) = n - 1 := by
    simpa [hn_def] using Tube.finrank_perpSpace V
  by_cases h2 : 2 ≤ n
  · have hperp_pos : 0 < Module.finrank ℝ (perpSpace V) := by
      rw [hperp]
      omega
    haveI : Nontrivial (perpSpace V) :=
      Module.nontrivial_of_finrank_pos (R := ℝ) (M := perpSpace V) hperp_pos
    have hvol := Metric.volume_closedBall_eq_ccov_mul_pow (E := perpSpace V) (r := r) hr
    simpa [hperp] using hvol
  · have h1 : n = 1 := by omega
    have hperp0 : Module.finrank ℝ (perpSpace V) = 0 := by
      omega
    have hv0 : volume (Metric.closedBall (0 : perpSpace V) r) = 1 :=
      Metric.volume_closedBall_of_finrank_eq_zero (G := perpSpace V) hperp0 hr
    have hC : (Metric.coveringNumber_mul_pow_le_volume_cthickening.C (n - 1) : ℝ) = 1 := by
      have hCnn :
          Metric.coveringNumber_mul_pow_le_volume_cthickening.C (n - 1) = (1 : NNReal) := by
        rw [h1]
        rw [Metric.coveringNumber_mul_pow_le_volume_cthickening.C]
        congr 1
        norm_num [Real.Gamma_one]
      exact_mod_cast hCnn
    have hpow2 : (2 : ℝ) ^ (n - 1) = 1 := by rw [h1]; norm_num
    have hpowr : r ^ (n - 1) = 1 := by rw [h1]; norm_num
    have hinside : (2 : ℝ) ^ (n - 1)
        * (Metric.coveringNumber_mul_pow_le_volume_cthickening.C (n - 1) : ℝ) * r ^ (n - 1)
        = 1 := by
      rw [hpow2, hC, hpowr]
      norm_num
    have hRHS : ENNReal.ofReal ((2 : ℝ) ^ (n - 1)
        * (Metric.coveringNumber_mul_pow_le_volume_cthickening.C (n - 1) : ℝ) * r ^ (n - 1))
        = (1 : ENNReal) := by
      rw [hinside, ENNReal.ofReal_one]
    rw [hv0, hRHS]

/-- **The parameter space** `F = ℝ × e^⊥ × e^⊥` of blueprint `def:tubeParameterMap`, carrying
the product inner product, so that `dim F = 2 n - 1` and
`‖(t, v, v')‖ = √(t² + ‖v‖² + ‖v'‖²) ≥ max {|t|, ‖v‖, ‖v'‖}`.  The `L²` product is spelt with
`WithLp 2`, which is the Mathlib carrier of the product inner product. -/
abbrev parameterSpace (V : Tube ρ E) : Type _ :=
  WithLp 2 (ℝ × WithLp 2 (perpSpace V × perpSpace V))

/-- **The rescaled parameter `Ψ`** of blueprint `def:tubeParameterMap`:
`Ψ(U) = ((c_* σ / κ) ⟪p_U - m, e⟫, (p_U - m)^⊥, (q_U - m)^⊥)`, with `m` the centre and `e` the
direction of `V`, `σ` the scale of `U`, `c_* = 1 / (4 n)` and
`κ = Tube.axialSeparation.kappa n C`.

The axial coordinate is rescaled so that its own resolution `κ` and the transverse resolution
`c_* σ` become the same number; blueprint `note:essDistinctTubesInDilateAxial` explains why the
`2n`-dimensional endpoint pair `(p_U, q_U)` cannot be used instead. -/
noncomputable def parameterMap {σ : NNReal} (V : Tube ρ E) (C : NNReal) (U : Tube σ E) :
    parameterSpace V :=
  WithLp.toLp 2
    (1 / (4 * (Module.finrank ℝ E : ℝ)) * (σ : ℝ)
        / (axialSeparation.kappa (Module.finrank ℝ E) C : ℝ)
        * inner ℝ (U.x - V.center) V.direction,
      WithLp.toLp 2 (((ℝ ∙ V.direction)ᗮ).orthogonalProjectionOnto (U.x - V.center),
        ((ℝ ∙ V.direction)ᗮ).orthogonalProjectionOnto (U.y - V.center)))

/-- **Counting in the parameter space** (blueprint `lem:parameterSpaceMeasure`).

A family `(Ψ i)_{i ∈ G}` of pairwise `r`-separated points of a set `A` in a finite-dimensional
real inner product space `F` has
`#G ≤ C_{lem:separatedSetCardBound}(dim F) · r ^ -dim F · |A^{(r)}|`, where the packing constant
`2 ^ d / ω_d` is the inverse of `Metric.coveringNumber_mul_pow_le_volume_cthickening.C d`.

Two deviations from the blueprint, both harmless.  The blueprint transports
`lem:separatedSetCardBound` from `ℝ ^ (2n-1)` to `F = ℝ × e^⊥ × e^⊥` along a chosen linear
isometry equivalence; here the statement is made directly for an arbitrary finite-dimensional
real inner product space, which is what
`Metric.packingNumber_mul_pow_le_volume_cthickening` already provides, so no isometry has to be
chosen.  And the thickening radius is `r` rather than `r / 2`, matching that lemma; the loss is
absorbed by `Metric.volume_cthickening_box_le`, whose hypothesis is only `s ≤ h_k`. -/
theorem card_le_of_separated_parameterSpace {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    [Nontrivial F] {ι : Type*} {G : Finset ι} {Ψ : ι → F} {A : Set F} {r : NNReal} (hr : 0 < r)
    (hGA : ∀ i ∈ G, Ψ i ∈ A)
    (hsep : (↑G : Set ι).Pairwise fun i j => (r : ℝ) < dist (Ψ i) (Ψ j)) :
    (G.card : ENNReal)
      ≤ (Metric.coveringNumber_mul_pow_le_volume_cthickening.C (Module.finrank ℝ F) : ENNReal)⁻¹
        * (r : ENNReal)⁻¹ ^ Module.finrank ℝ F * volume (cthickening (r : ℝ) A) := by
  set d := Module.finrank ℝ F
  set S : Set F := Ψ '' (↑G : Set ι) with hSdef
  have hr_nn : (0 : ℝ) ≤ (r : ℝ) := r.coe_nonneg
  have hΨinj : Set.InjOn Ψ (↑G : Set ι) := by
    intro i hi j hj hΨij
    by_contra hij
    have hlt : (r : ℝ) < dist (Ψ i) (Ψ j) := hsep hi hj hij
    rw [hΨij, dist_self] at hlt
    have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
    exact (lt_irrefl (0 : ℝ)) (lt_trans hrR hlt)
  have hSA : S ⊆ A := by
    rw [hSdef]
    rintro x ⟨i, hi, rfl⟩
    exact hGA i hi
  have hSsep : Metric.IsSeparated (r : ENNReal) S := by
    rw [Metric.IsSeparated, hSdef]
    rintro x ⟨i, hi, rfl⟩ y ⟨j, hj, rfl⟩ hxy
    have hij : i ≠ j := by
      rintro rfl
      exact hxy rfl
    rw [edist_dist]
    rw [← ENNReal.ofReal_coe_nnreal (p := r)]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hr_nn).mpr (hsep hi hj hij)
  have hcount : (G.card : ENNReal) ≤ (Metric.packingNumber r A : ENNReal) := by
    calc
      (G.card : ENNReal) = S.encard := by
        rw [hSdef, Set.InjOn.encard_image hΨinj, Set.encard_coe_eq_coe_finsetCard]
        norm_cast
      _ ≤ (Metric.packingNumber r A : ENNReal) := by
        exact_mod_cast (Metric.IsSeparated.encard_le_packingNumber hSA hSsep)
  have hvol := Metric.packingNumber_mul_pow_le_volume_cthickening (E := F) r A
  have hC0 : (Metric.coveringNumber_mul_pow_le_volume_cthickening.C d : ENNReal) ≠ 0 := by
    exact_mod_cast ne_of_gt (Metric.coveringNumber_mul_pow_le_volume_cthickening.C_pos d)
  have hr0 : (r : ENNReal) ≠ 0 := by
    exact_mod_cast ne_of_gt hr
  have hCtop : (Metric.coveringNumber_mul_pow_le_volume_cthickening.C d : ENNReal) ≠ ⊤ := by
    exact ENNReal.coe_ne_top
  have hrtop : (r : ENNReal) ≠ ⊤ := by
    exact ENNReal.coe_ne_top
  have hrd0 : (r : ENNReal) ^ d ≠ 0 := pow_ne_zero d hr0
  have hrdtop : (r : ENNReal) ^ d ≠ ⊤ := ENNReal.pow_ne_top hrtop
  have hB0 : (Metric.coveringNumber_mul_pow_le_volume_cthickening.C d : ENNReal)
        * (r : ENNReal) ^ d ≠ 0 := mul_ne_zero hC0 hrd0
  have hBtop : (Metric.coveringNumber_mul_pow_le_volume_cthickening.C d : ENNReal)
        * (r : ENNReal) ^ d ≠ ⊤ := ENNReal.mul_ne_top hCtop hrdtop
  have hpack : (Metric.packingNumber r A : ENNReal)
      ≤ (Metric.coveringNumber_mul_pow_le_volume_cthickening.C d : ENNReal)⁻¹
        * (r : ENNReal)⁻¹ ^ d * volume (cthickening (r : ℝ) A) := by
    let B : ENNReal := (Metric.coveringNumber_mul_pow_le_volume_cthickening.C d : ENNReal)
        * (r : ENNReal) ^ d
    have hdiv : (Metric.packingNumber r A : ENNReal)
        ≤ volume (cthickening (r : ℝ) A) / B := by
      rw [ENNReal.le_div_iff_mul_le (Or.inl hB0) (Or.inl hBtop)]
      rw [show (Metric.packingNumber r A : ENNReal) * B
          = (Metric.coveringNumber_mul_pow_le_volume_cthickening.C d : ENNReal)
            * (Metric.packingNumber r A : ENNReal) * (r : ENNReal) ^ d by
        dsimp [B]
        ac_rfl]
      exact hvol
    calc
      (Metric.packingNumber r A : ENNReal) ≤ volume (cthickening (r : ℝ) A) / B := hdiv
      _ = (Metric.coveringNumber_mul_pow_le_volume_cthickening.C d : ENNReal)⁻¹
          * (r : ENNReal)⁻¹ ^ d * volume (cthickening (r : ℝ) A) := by
        rw [ENNReal.div_eq_inv_mul]
        rw [show B⁻¹ = (Metric.coveringNumber_mul_pow_le_volume_cthickening.C d : ENNReal)⁻¹
            * (r : ENNReal)⁻¹ ^ d by
          dsimp [B]
          rw [ENNReal.mul_inv (Or.inl hC0) (Or.inr hrd0), ENNReal.inv_pow]]
  exact hcount.trans hpack

/-- **Comparing the axial components of two nearly axial unit vectors** (blueprint
`lem:tubeDirectionAxialComparison`).  For unit vectors `f, f'` making a nonnegative inner
product with the unit vector `e` and with transverse parts of norm at most `1/2`, the axial
components differ by at most the transverse parts do. -/
theorem abs_inner_sub_le_norm_perp_sub {e f f' : E} (he : ‖e‖ = 1) (hf : ‖f‖ = 1)
    (hf' : ‖f'‖ = 1) (hfe : 0 ≤ inner ℝ f e) (hf'e : 0 ≤ inner ℝ f' e)
    (hfp : ‖f - inner ℝ e f • e‖ ≤ 1 / 2) (hf'p : ‖f' - inner ℝ e f' • e‖ ≤ 1 / 2) :
    |inner ℝ (f - f') e| ≤ ‖(f - inner ℝ e f • e) - (f' - inner ℝ e f' • e)‖ := by
  set a : ℝ := inner ℝ e f
  set a' : ℝ := inner ℝ e f'
  set u : E := f - a • e
  set u' : E := f' - a' • e
  have ha : inner ℝ f e = a := by simp [a, real_inner_comm]
  have ha' : inner ℝ f' e = a' := by simp [a', real_inner_comm]
  have ha0 : 0 ≤ a := by simpa [a, real_inner_comm] using hfe
  have ha'0 : 0 ≤ a' := by simpa [a', real_inner_comm] using hf'e
  have hu_sq : ‖u‖ ^ 2 = 1 - a ^ 2 := by
    change ‖f - a • e‖ ^ 2 = 1 - a ^ 2
    rw [norm_sub_sq_real]
    simp [hf, he, ha, norm_smul, inner_smul_right]
    ring
  have hu'_sq : ‖u'‖ ^ 2 = 1 - a' ^ 2 := by
    change ‖f' - a' • e‖ ^ 2 = 1 - a' ^ 2
    rw [norm_sub_sq_real]
    simp [hf', he, ha', norm_smul, inner_smul_right]
    ring
  have ha_sq : a ^ 2 + ‖u‖ ^ 2 = 1 := by nlinarith [hu_sq]
  have ha'_sq : a' ^ 2 + ‖u'‖ ^ 2 = 1 := by nlinarith [hu'_sq]
  have hu0 : 0 ≤ ‖u‖ := norm_nonneg u
  have hu'0 : 0 ≤ ‖u'‖ := norm_nonneg u'
  have ha_half : 1 / 2 ≤ a := by
    have hsq : (1 / 2 : ℝ) ^ 2 ≤ a ^ 2 := by nlinarith [hu_sq, hfp, hu0]
    have habs : |(1 / 2 : ℝ)| ≤ |a| := sq_le_sq.mp hsq
    simpa [abs_of_nonneg ha0] using habs
  have ha'_half : 1 / 2 ≤ a' := by
    have hsq : (1 / 2 : ℝ) ^ 2 ≤ a' ^ 2 := by nlinarith [hu'_sq, hf'p, hu'0]
    have habs : |(1 / 2 : ℝ)| ≤ |a'| := sq_le_sq.mp hsq
    simpa [abs_of_nonneg ha'0] using habs
  have hapos : 0 < a + a' := by linarith [ha_half, ha'_half]
  have hap0 : 0 ≤ a + a' := le_of_lt hapos
  have hsum : ‖u‖ + ‖u'‖ ≤ a + a' := by linarith [ha_half, ha'_half, hfp, hf'p]
  have hin : inner ℝ (f - f') e = a - a' := by
    rw [inner_sub_left, ← ha, ← ha']
  have hprod : (a - a') * (a + a') = ‖u'‖ ^ 2 - ‖u‖ ^ 2 := by
    nlinarith [ha_sq, ha'_sq]
  have hrev : |‖u'‖ - ‖u‖| ≤ ‖u - u'‖ := by
    simpa [abs_sub_comm] using abs_norm_sub_norm_le u u'
  have hmain : |a - a'| * (a + a') ≤ ‖u - u'‖ * (a + a') := by
    calc
      |a - a'| * (a + a') = |(a - a') * (a + a')| := by
        rw [abs_mul, abs_of_nonneg hap0]
      _ = |‖u'‖ ^ 2 - ‖u‖ ^ 2| := by rw [hprod]
      _ = |‖u'‖ - ‖u‖| * (‖u'‖ + ‖u‖) := by
        rw [show ‖u'‖ ^ 2 - ‖u‖ ^ 2 = (‖u'‖ - ‖u‖) * (‖u'‖ + ‖u‖) by ring]
        rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ ‖u'‖ + ‖u‖)]
      _ ≤ ‖u - u'‖ * (‖u'‖ + ‖u‖) := by
        exact mul_le_mul_of_nonneg_right hrev (by positivity : 0 ≤ ‖u'‖ + ‖u‖)
      _ ≤ ‖u - u'‖ * (a + a') := by
        exact mul_le_mul_of_nonneg_left (by simpa [add_comm] using hsum) (norm_nonneg (u - u'))
  have hfinal : |a - a'| ≤ ‖u - u'‖ := by
    have hc : a + a' ≠ 0 := ne_of_gt hapos
    calc
      |a - a'| = (|a - a'| * (a + a')) / (a + a') := by field_simp [hc]
      _ ≤ (‖u - u'‖ * (a + a')) / (a + a') := div_le_div_of_nonneg_right hmain hap0
      _ = ‖u - u'‖ := by field_simp [hc]
  rwa [hin]

/-- **Mixed-scale separation of the tube parameters** (blueprint
`lem:essDistinctTubeAxialSeparation`).

In the thin regime `ρ ≤ 1 / (4 C_n)`, two essentially distinct `σ`-tubes `U, U'` inside
`C_n · V`, oriented so that both directions make a nonnegative inner product with the direction
of `V`, have parameters separated by more than `c_* σ / 4`: the maximum of the two transverse
endpoint differences and of the rescaled axial difference exceeds `c_* σ / 4`.

Since `(p_U - m)^⊥ - (p_{U'} - m)^⊥ = (p_U - p_{U'})^⊥` and likewise at `q`, the three
quantities are the coordinate differences of `Tube.parameterMap V C U` and
`Tube.parameterMap V C U'`, so this says that the two parameters are `c_* σ / 4`-separated. -/
theorem axial_separation_of_essDistinct [Nontrivial E] {C : NNReal} (hC : 1 ≤ C) (hρ0 : 0 < ρ)
    (hρ : (ρ : ℝ) ≤ 1 / (4 * Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E)))
    (V : Tube ρ E) (U U' : Tube (C⁻¹ * ρ) E)
    (hU : U.carrier ⊆ (Kakeya.Tube.dilate V
      (Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E))).carrier)
    (hU' : U'.carrier ⊆ (Kakeya.Tube.dilate V
      (Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E))).carrier)
    (hUo : 0 ≤ inner ℝ U.direction V.direction)
    (hU'o : 0 ≤ inner ℝ U'.direction V.direction)
    (hED : IsEssentiallyDistinct U.carrier U'.carrier) :
    1 / 4 * (1 / (4 * (Module.finrank ℝ E : ℝ))) * ((C : ℝ)⁻¹ * (ρ : ℝ))
      < max (max ‖U.x - U'.x - inner ℝ V.direction (U.x - U'.x) • V.direction‖
              ‖U.y - U'.y - inner ℝ V.direction (U.y - U'.y) • V.direction‖)
          (1 / (4 * (Module.finrank ℝ E : ℝ)) * ((C : ℝ)⁻¹ * (ρ : ℝ))
            / (axialSeparation.kappa (Module.finrank ℝ E) C : ℝ)
            * |inner ℝ (U.x - U'.x) V.direction|) := by
  classical
  set n : ℕ := Module.finrank ℝ E
  set cstar : ℝ := 1 / (4 * (n : ℝ))
  set σ : ℝ := (C : ℝ)⁻¹ * (ρ : ℝ)
  set Cn : ℝ := Kakeya.Tube.tubeOverlapCoreClose.C n
  set κ : ℝ := (axialSeparation.kappa n C : ℝ)
  set η : ℝ := 1 / 4 * cstar * σ
  set α0 : ℝ := inner ℝ (U.x - U'.x) V.direction
  set u : E := (U.x - U'.x) - α0 • V.direction
  set β0 : ℝ := inner ℝ (U.y - U'.y) V.direction
  set w : E := (U.y - U'.y) - β0 • V.direction
  set α : ℝ := -α0 * inner ℝ V.direction U.direction
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast Module.finrank_pos (R := ℝ) (M := E)
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hCn1 : 1 < Cn := by dsimp [Cn]; exact Kakeya.Tube.tubeOverlapCoreClose.one_lt_C n
  have hCnpos : 0 < Cn := lt_trans zero_lt_one hCn1
  have hCn0 : Cn ≠ 0 := ne_of_gt hCnpos
  have hC1r : 1 ≤ (C : ℝ) := by exact_mod_cast hC
  have hCp : (0 : NNReal) < C := lt_of_lt_of_le zero_lt_one hC
  have hCpr : 0 < (C : ℝ) := by exact_mod_cast hCp
  have hC0 : (C : ℝ) ≠ 0 := ne_of_gt hCpr
  have hCnz : (C : NNReal) ≠ 0 := ne_of_gt hCp
  have hρr : 0 < (ρ : ℝ) := by exact_mod_cast hρ0
  have hρnr : 0 ≤ (ρ : ℝ) := le_of_lt hρr
  have hρ1 : ρ ≤ 1 := by
    have hbig : (1 / (4 * Cn) : ℝ) ≤ 1 := by
      rw [div_le_one (by positivity : 0 < 4 * Cn)]
      nlinarith [hCn1]
    exact_mod_cast (hρ.trans hbig)
  have hσr : 0 < σ := by dsimp [σ]; exact mul_pos (inv_pos.mpr hCpr) hρr
  have hcs : 0 < cstar := by dsimp [cstar]; positivity
  have hη : 0 < η := by dsimp [η]; positivity
  have hcstar0 : cstar ≠ 0 := ne_of_gt hcs
  have hσ0r : σ ≠ 0 := ne_of_gt hσr
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hκ0 : κ ≠ 0 := ne_of_gt hκ
  have hCinvp : 0 < (C : NNReal)⁻¹ := inv_pos.mpr hCp
  have hσρpos : 0 < (C⁻¹ * ρ : NNReal) := mul_pos hCinvp hρ0
  have hCinvle1 : (C : NNReal)⁻¹ ≤ 1 := by
    exact (inv_le_one₀ (lt_of_lt_of_le zero_lt_one hC)).mpr hC
  have hσρleρ : (C⁻¹ * ρ : NNReal) ≤ ρ := by
    simpa [mul_comm] using mul_le_of_le_one_right (le_of_lt hρ0) hCinvle1
  have hσρle1 : (C⁻¹ * ρ : NNReal) ≤ 1 := le_trans hσρleρ hρ1
  have hρreal : (ρ : ℝ) ≤ 1 / (4 * Cn) := by simpa [Cn] using hρ
  have hUpar := parameters_mem_of_subset_dilate hρ0 hρ1 hσρleρ V U hU
  have hU'par := parameters_mem_of_subset_dilate hρ0 hρ1 hσρleρ V U' hU'
  have hdirU : ‖U.direction - inner ℝ V.direction U.direction • V.direction‖ ≤ 2 * Cn * (ρ : ℝ) := by
    exact hUpar.2.2
  have hdirU' : ‖U'.direction - inner ℝ V.direction U'.direction • V.direction‖ ≤ 2 * Cn * (ρ : ℝ) := by
    exact hU'par.2.2
  have h2Cnρ : 2 * Cn * (ρ : ℝ) ≤ 1 / 2 := by
    calc
      2 * Cn * (ρ : ℝ) ≤ 2 * Cn * (1 / (4 * Cn)) := by
        exact mul_le_mul_of_nonneg_left hρreal (by positivity : 0 ≤ 2 * Cn)
      _ = 1 / 2 := by
        field_simp [hCn0]
        norm_num
  have hdirU12 : ‖U.direction - inner ℝ V.direction U.direction • V.direction‖ ≤ 1 / 2 := hdirU.trans h2Cnρ
  have hdirU'12 : ‖U'.direction - inner ℝ V.direction U'.direction • V.direction‖ ≤ 1 / 2 := hdirU'.trans h2Cnρ
  have hdir : |inner ℝ (U.direction - U'.direction) V.direction| ≤
      ‖(U.direction - inner ℝ V.direction U.direction • V.direction) -
        (U'.direction - inner ℝ V.direction U'.direction • V.direction)‖ :=
    abs_inner_sub_le_norm_perp_sub (e := V.direction) (f := U.direction) (f' := U'.direction)
      V.norm_direction U.norm_direction U'.norm_direction hUo hU'o hdirU12 hdirU'12
  by_contra hnot
  have hle : max (max ‖U.x - U'.x - inner ℝ V.direction (U.x - U'.x) • V.direction‖
              ‖U.y - U'.y - inner ℝ V.direction (U.y - U'.y) • V.direction‖)
          (cstar * σ / κ * |inner ℝ (U.x - U'.x) V.direction|) ≤ η := by
    simpa [η] using le_of_not_gt hnot
  have hle1 : ‖U.x - U'.x - inner ℝ V.direction (U.x - U'.x) • V.direction‖ ≤ η := by
    exact (le_max_left _ _).trans ((le_max_left _ _).trans hle)
  have hle2 : ‖U.y - U'.y - inner ℝ V.direction (U.y - U'.y) • V.direction‖ ≤ η := by
    exact (le_max_right _ _).trans ((le_max_left _ _).trans hle)
  have hle3 : cstar * σ / κ * |α0| ≤ η := by
    exact (le_max_right _ _).trans hle
  have hηeq4 : η = cstar * σ / 4 := by dsimp [η]; ring
  have hα0 : |α0| ≤ κ / 4 := by
    have hmul : cstar * σ / κ * |α0| ≤ cstar * σ / 4 := by
      simpa [hηeq4] using hle3
    have hposM : 0 < cstar * σ / κ := by
      exact div_pos (mul_pos hcs hσr) hκ
    have hdiv : |α0| ≤ (cstar * σ / 4) / (cstar * σ / κ) :=
      (le_div_iff₀ hposM).mpr (by simpa [mul_comm] using hmul)
    have hid : (cstar * σ / 4) / (cstar * σ / κ) = κ / 4 := by
      field_simp [hcstar0, hσ0r, hκ0]
    rw [hid] at hdiv
    exact hdiv
  have hα0eqx : inner ℝ V.direction (U.x - U'.x) = α0 := by
    exact real_inner_comm (U.x - U'.x) V.direction
  have hu : ‖u‖ ≤ η := by
    dsimp [u]
    rw [← hα0eqx]
    exact hle1
  have hβ0eqy : inner ℝ V.direction (U.y - U'.y) = β0 := by
    exact real_inner_comm (U.y - U'.y) V.direction
  have hw : ‖w‖ ≤ η := by
    dsimp [w]
    rw [← hβ0eqy]
    exact hle2
  have hdecomp : U.x - U'.x = α0 • V.direction + u := by
    dsimp [u]; abel
  have hdecomp2 : U.y - U'.y = β0 • V.direction + w := by
    dsimp [w]; abel
  have h2 : (U.y - U'.y) - (U.x - U'.x) = U.direction - U'.direction := by
    rw [show U.direction = U.y - U.x by rfl, show U'.direction = U'.y - U'.x by rfl]
    module
  have hperpdiff : (U.direction - inner ℝ V.direction U.direction • V.direction) -
      (U'.direction - inner ℝ V.direction U'.direction • V.direction) = w - u := by
    have hsub : (U.direction - inner ℝ V.direction U.direction • V.direction) -
        (U'.direction - inner ℝ V.direction U'.direction • V.direction)
        = (U.direction - U'.direction) - (inner ℝ V.direction U.direction - inner ℝ V.direction U'.direction) • V.direction := by
      module
    have hsub' : (U.direction - inner ℝ V.direction U.direction • V.direction) -
        (U'.direction - inner ℝ V.direction U'.direction • V.direction)
        = (U.direction - U'.direction) - inner ℝ V.direction (U.direction - U'.direction) • V.direction := by
      rw [hsub]
      congr 1
      congr 1
      rw [← inner_sub_right]
    have hwsu : w - u = (U.direction - U'.direction) - inner ℝ V.direction (U.direction - U'.direction) • V.direction := by
      dsimp [w, u, α0, β0]
      have h1 : (U.y - U'.y) - inner ℝ (U.y - U'.y) V.direction • V.direction
          - ((U.x - U'.x) - inner ℝ (U.x - U'.x) V.direction • V.direction)
          = (U.y - U'.y - (U.x - U'.x)) - (inner ℝ (U.y - U'.y) V.direction - inner ℝ (U.x - U'.x) V.direction) • V.direction := by
        module
      rw [h1]
      rw [h2]
      congr 1
      congr 1
      rw [← inner_sub_left]
      rw [h2]
      exact (real_inner_comm (U.direction - U'.direction) V.direction).symm
    exact hsub'.trans hwsu.symm
  have hperp_norm : ‖(U.direction - inner ℝ V.direction U.direction • V.direction) -
      (U'.direction - inner ℝ V.direction U'.direction • V.direction)‖ ≤ 2 * η := by
    rw [hperpdiff]
    calc
      ‖w - u‖ ≤ ‖w‖ + ‖u‖ := norm_sub_le w u
      _ ≤ η + η := add_le_add hw hu
      _ = 2 * η := by ring
  have hβdiff : β0 - α0 = inner ℝ (U.direction - U'.direction) V.direction := by
    dsimp [β0, α0]
    rw [← inner_sub_left]
    rw [h2]
  have hβ0a : |β0 - α0| ≤ 2 * η := by
    rw [hβdiff]
    exact hdir.trans hperp_norm
  have hperp_swap : ‖V.direction - inner ℝ V.direction U.direction • U.direction‖
      = ‖U.direction - inner ℝ V.direction U.direction • V.direction‖ := by
    let t : ℝ := inner ℝ V.direction U.direction
    have htU : inner ℝ V.direction U.direction = t := rfl
    have htV : inner ℝ U.direction V.direction = t := by
      rw [← htU]
      exact real_inner_comm V.direction U.direction
    have hsq_a : ‖V.direction - t • U.direction‖ ^ 2 = 1 - t ^ 2 := by
      rw [norm_sub_sq_real]
      simp [V.norm_direction, U.norm_direction, norm_smul, inner_smul_right, htU]
      ring
    have hsq_b : ‖U.direction - t • V.direction‖ ^ 2 = 1 - t ^ 2 := by
      rw [norm_sub_sq_real]
      simp [V.norm_direction, U.norm_direction, norm_smul, inner_smul_right, htV]
      ring
    have hsq : ‖V.direction - t • U.direction‖ ^ 2 = ‖U.direction - t • V.direction‖ ^ 2 := by
      rw [hsq_a, hsq_b]
    have hmain : ‖V.direction - t • U.direction‖ = ‖U.direction - t • V.direction‖ := by
      have ha : 0 ≤ ‖V.direction - t • U.direction‖ := norm_nonneg _
      have hb : 0 ≤ ‖U.direction - t • V.direction‖ := norm_nonneg _
      exact le_antisymm (le_of_sq_le_sq hsq.le hb) (le_of_sq_le_sq hsq.symm.le ha)
    rw [show inner ℝ V.direction U.direction = t by rfl]
    exact hmain
  have hperp1 : ‖V.direction - inner ℝ V.direction U.direction • U.direction‖ ≤ 2 * Cn * (ρ : ℝ) := by
    calc
      ‖V.direction - inner ℝ V.direction U.direction • U.direction‖
          = ‖U.direction - inner ℝ V.direction U.direction • V.direction‖ := hperp_swap
      _ ≤ 2 * Cn * (ρ : ℝ) := hdirU
  have hslide : ‖-α0 • V.direction - α • U.direction‖ = |α0| * ‖V.direction - inner ℝ V.direction U.direction • U.direction‖ := by
    have hvid : -α0 • V.direction - α • U.direction = -α0 • (V.direction - inner ℝ V.direction U.direction • U.direction) := by
      dsimp [α]
      module
    rw [hvid]
    rw [norm_smul]
    rw [show ‖(-α0 : ℝ)‖ = |α0| by exact (Real.norm_eq_abs (-α0)).trans (abs_neg α0)]
  have hslide_le : ‖-α0 • V.direction - α • U.direction‖ ≤ (κ / 4) * (2 * Cn * (ρ : ℝ)) := by
    rw [hslide]
    exact mul_le_mul hα0 hperp1 (norm_nonneg _) (by positivity : 0 ≤ κ / 4)
  have hbU : |inner ℝ V.direction U.direction| ≤ 1 := by
    calc
      |inner ℝ V.direction U.direction| ≤ ‖V.direction‖ * ‖U.direction‖ := abs_real_inner_le_norm V.direction U.direction
      _ = 1 := by rw [V.norm_direction, U.norm_direction]; norm_num
  have hα4 : |α| ≤ κ / 4 := by
    dsimp [α]
    calc
      |-α0 * inner ℝ V.direction U.direction| = |α0| * |inner ℝ V.direction U.direction| := by
        rw [abs_mul, abs_neg]
      _ ≤ |α0| * 1 := by
        exact mul_le_mul_of_nonneg_left hbU (abs_nonneg α0)
      _ = |α0| := by ring
      _ ≤ κ / 4 := hα0
  have hκval : κ = 1 / (32 * (n : ℝ) * (C : ℝ) * Cn) := by
    dsimp [κ]
    have hmax : max (Kakeya.Tube.tubeOverlapCoreClose.C n) 0 = Cn := by
      rw [max_eq_left (le_trans zero_le_one (le_of_lt (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C n)))]
    simp [hmax]
  have hκcstar : κ / 4 ≤ cstar := by
    rw [hκval]
    dsimp [cstar]
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
    rw [div_le_iff₀ (by positivity : 0 < 32 * (n : ℝ) * (C : ℝ) * Cn)]
    have hide : (1 / (4 * (n : ℝ))) * 4 * (32 * (n : ℝ) * (C : ℝ) * Cn)
        = 32 * (C : ℝ) * Cn := by
      field_simp [hn0]
    rw [hide]
    nlinarith only [hC1r, hCn1]
  have hmain_eq : (κ / 4) * (2 * Cn * (ρ : ℝ)) = η / 4 := by
    rw [hκval]
    dsimp [η, σ, cstar]
    field_simp [hn0, hC0, hCn0]
    ring
  have hsliderr : (κ / 4) * (2 * Cn * (ρ : ℝ)) ≤ η := by
    calc
      (κ / 4) * (2 * Cn * (ρ : ℝ)) = η / 4 := hmain_eq
      _ ≤ η := div_le_self hη.le (by norm_num : (1 : ℝ) ≤ 4)
  have hp_id : U'.x - (U.x + α • U.direction) = (-α0 • V.direction - α • U.direction) - u := by
    dsimp [u]
    module
  have hpnorm : ‖U'.x - (U.x + α • U.direction)‖ ≤ cstar * σ := by
    rw [hp_id]
    calc
      ‖(-α0 • V.direction - α • U.direction) - u‖ ≤ ‖-α0 • V.direction - α • U.direction‖ + ‖u‖ := norm_sub_le _ _
      _ ≤ (κ / 4) * (2 * Cn * (ρ : ℝ)) + η := add_le_add hslide_le hu
      _ ≤ cstar * σ := by nlinarith only [hsliderr, hηeq4, hη]
  have hσreal : ((C⁻¹ * ρ : NNReal) : ℝ) = σ := by
    rw [NNReal.coe_mul, NNReal.coe_inv]
  have hp : dist U'.x (U.x + α • U.direction) ≤ 1 / (4 * (Module.finrank ℝ E : ℝ)) * ((C⁻¹ * ρ : NNReal) : ℝ) := by
    simpa [cstar, hσreal, dist_eq_norm] using hpnorm
  have hq_id : U'.y - (U.y + α • U.direction) = (-α0 • V.direction - α • U.direction) - (β0 - α0) • V.direction - w := by
    dsimp [w]
    module
  have hbq : ‖(β0 - α0) • V.direction‖ ≤ |β0 - α0| := by
    rw [norm_smul, Real.norm_eq_abs, V.norm_direction]
    simp
  have hqnorm : ‖U'.y - (U.y + α • U.direction)‖ ≤ cstar * σ := by
    rw [hq_id]
    calc
      ‖((-α0 • V.direction - α • U.direction) - (β0 - α0) • V.direction) - w‖
          ≤ ‖(-α0 • V.direction - α • U.direction) - (β0 - α0) • V.direction‖ + ‖w‖ := norm_sub_le _ _
      _ ≤ (‖-α0 • V.direction - α • U.direction‖ + ‖(β0 - α0) • V.direction‖) + ‖w‖ := by
            gcongr
            exact norm_sub_le (-α0 • V.direction - α • U.direction) ((β0 - α0) • V.direction)
      _ ≤ ‖-α0 • V.direction - α • U.direction‖ + |β0 - α0| + η := by
            nlinarith only [hbq, hw]
      _ ≤ (κ / 4) * (2 * Cn * (ρ : ℝ)) + 2 * η + η := by
            nlinarith only [hslide_le, hβ0a]
      _ ≤ cstar * σ := by nlinarith only [hsliderr, hηeq4, hη]
  have hq : dist U'.y (U.y + α • U.direction) ≤ 1 / (4 * (Module.finrank ℝ E : ℝ)) * ((C⁻¹ * ρ : NNReal) : ℝ) := by
    simpa [cstar, hσreal, dist_eq_norm] using hqnorm
  have hαcstar : |α| ≤ cstar := hα4.trans hκcstar
  have hslide_not_ed : ¬ IsEssentiallyDistinct U.carrier U'.carrier :=
    not_essDistinct_of_axial_slide (σ := C⁻¹ * ρ) hσρpos hσρle1 U U' (α := α) hαcstar hp hq
  exact hslide_not_ed hED

/-! ### The parameter region and its measure -/

/-- **The thickening of a centred box is at most the doubled box** (blueprint
`lem:boxThickeningVolume`).  Each of the three coordinate projections of the `L²` product is
`1`-Lipschitz, so a thickening by `s ≤ min {h₀, h₁, h₂}` at most doubles each half-side, and
the measure of a product of an interval and two balls multiplies by `2 ^ (1 + d₁ + d₂)`. -/
theorem _root_.Metric.volume_cthickening_box_le {F₁ F₂ : Type*} [NormedAddCommGroup F₁]
    [InnerProductSpace ℝ F₁] [FiniteDimensional ℝ F₁] [MeasurableSpace F₁] [BorelSpace F₁]
    [NormedAddCommGroup F₂] [InnerProductSpace ℝ F₂] [FiniteDimensional ℝ F₂]
    [MeasurableSpace F₂] [BorelSpace F₂] {h₀ h₁ h₂ s : ℝ} (hs : 0 < s) (hs₀ : s ≤ h₀)
    (hs₁ : s ≤ h₁) (hs₂ : s ≤ h₂) :
    cthickening s (Metric.prodBox (F₁ := F₁) (F₂ := F₂) h₀ h₁ h₂)
        ⊆ Metric.prodBox (F₁ := F₁) (F₂ := F₂) (2 * h₀) (2 * h₁) (2 * h₂) ∧
      volume (cthickening s (Metric.prodBox (F₁ := F₁) (F₂ := F₂) h₀ h₁ h₂))
        ≤ 2 ^ (1 + Module.finrank ℝ F₁ + Module.finrank ℝ F₂)
          * volume (Metric.prodBox (F₁ := F₁) (F₂ := F₂) h₀ h₁ h₂) := by
  set B : Set (WithLp 2 (ℝ × WithLp 2 (F₁ × F₂))) :=
    Metric.prodBox (F₁ := F₁) (F₂ := F₂) h₀ h₁ h₂
  set B' : Set (WithLp 2 (ℝ × WithLp 2 (F₁ × F₂))) :=
    Metric.prodBox (F₁ := F₁) (F₂ := F₂) (2 * h₀) (2 * h₁) (2 * h₂)
  have h0_nonneg : 0 ≤ h₀ := le_trans (le_of_lt hs) hs₀
  have h1_nonneg : 0 ≤ h₁ := le_trans (le_of_lt hs) hs₁
  have h2_nonneg : 0 ≤ h₂ := le_trans (le_of_lt hs) hs₂
  have hcthick : cthickening s B ⊆ B' := by
    intro z hz
    have hinf : infEDist z B ≤ ENNReal.ofReal s :=
      Metric.mem_cthickening_iff.mp hz
    let pz : WithLp 2 (F₁ × F₂) := (WithLp.ofLp z).2
    have hforall1 : ∀ ε : ℝ, 0 < ε → |(WithLp.ofLp z).1| ≤ h₀ + s + ε := by
      intro ε hε
      have hinf' : infEDist z B < ENNReal.ofReal (s + ε) := by
        refine lt_of_le_of_lt hinf ?_
        exact (ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < s + ε)).mpr (by linarith)
      rcases Metric.infEDist_lt_iff.mp hinf' with ⟨y, hyB, hyed⟩
      have hdy : dist z y < s + ε := by
        rw [edist_dist] at hyed
        exact (ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < s + ε)).mp hyed
      have hy1 : |(WithLp.ofLp y).1| ≤ h₀ := by
        simpa [B] using hyB.1
      have hdist1 : dist (WithLp.ofLp z).1 (WithLp.ofLp y).1 ≤ dist z y := by
        exact WithLp.dist_fst_le z y
      have htri : |(WithLp.ofLp z).1| ≤
          dist (WithLp.ofLp z).1 (WithLp.ofLp y).1 + |(WithLp.ofLp y).1| := by
        calc
          |(WithLp.ofLp z).1| = dist (WithLp.ofLp z).1 (0 : ℝ) := by
            simp [dist_eq_norm, Real.norm_eq_abs]
          _ ≤ dist (WithLp.ofLp z).1 (WithLp.ofLp y).1 + dist (WithLp.ofLp y).1 (0 : ℝ) :=
            dist_triangle _ _ _
          _ = dist (WithLp.ofLp z).1 (WithLp.ofLp y).1 + |(WithLp.ofLp y).1| := by
            simp [dist_eq_norm, Real.norm_eq_abs]
      nlinarith [hy1, hdist1, le_of_lt hdy, htri]
    have hforall2 : ∀ ε : ℝ, 0 < ε → ‖(WithLp.ofLp pz).1‖ ≤ h₁ + s + ε := by
      intro ε hε
      have hinf' : infEDist z B < ENNReal.ofReal (s + ε) := by
        refine lt_of_le_of_lt hinf ?_
        exact (ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < s + ε)).mpr (by linarith)
      rcases Metric.infEDist_lt_iff.mp hinf' with ⟨y, hyB, hyed⟩
      have hdy : dist z y < s + ε := by
        rw [edist_dist] at hyed
        exact (ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < s + ε)).mp hyed
      let py : WithLp 2 (F₁ × F₂) := (WithLp.ofLp y).2
      have hy2 : ‖(WithLp.ofLp py).1‖ ≤ h₁ := by
        change ‖(WithLp.ofLp (WithLp.ofLp y).2).1‖ ≤ h₁
        simpa [B] using hyB.2.1
      have hdist2 : dist (WithLp.ofLp pz).1 (WithLp.ofLp py).1 ≤ dist pz py := by
        exact WithLp.dist_fst_le pz py
      have hdist_outer : dist pz py ≤ dist z y := by
        exact WithLp.dist_snd_le z y
      have htri2 : ‖(WithLp.ofLp pz).1‖ ≤
          dist (WithLp.ofLp pz).1 (WithLp.ofLp py).1 + ‖(WithLp.ofLp py).1‖ := by
        calc
          ‖(WithLp.ofLp pz).1‖ =
              ‖((WithLp.ofLp pz).1 - (WithLp.ofLp py).1) + (WithLp.ofLp py).1‖ := by
            congr 1
            abel
          _ ≤ ‖(WithLp.ofLp pz).1 - (WithLp.ofLp py).1‖ + ‖(WithLp.ofLp py).1‖ :=
            norm_add_le _ _
          _ = dist (WithLp.ofLp pz).1 (WithLp.ofLp py).1 + ‖(WithLp.ofLp py).1‖ := by
            rw [dist_eq_norm]
      nlinarith [hy2, hdist2, hdist_outer, le_of_lt hdy, htri2]
    have hforall3 : ∀ ε : ℝ, 0 < ε → ‖(WithLp.ofLp pz).2‖ ≤ h₂ + s + ε := by
      intro ε hε
      have hinf' : infEDist z B < ENNReal.ofReal (s + ε) := by
        refine lt_of_le_of_lt hinf ?_
        exact (ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < s + ε)).mpr (by linarith)
      rcases Metric.infEDist_lt_iff.mp hinf' with ⟨y, hyB, hyed⟩
      have hdy : dist z y < s + ε := by
        rw [edist_dist] at hyed
        exact (ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < s + ε)).mp hyed
      let py : WithLp 2 (F₁ × F₂) := (WithLp.ofLp y).2
      have hy3 : ‖(WithLp.ofLp py).2‖ ≤ h₂ := by
        change ‖(WithLp.ofLp (WithLp.ofLp y).2).2‖ ≤ h₂
        simpa [B] using hyB.2.2
      have hdist3 : dist (WithLp.ofLp pz).2 (WithLp.ofLp py).2 ≤ dist pz py := by
        exact WithLp.dist_snd_le pz py
      have hdist_outer : dist pz py ≤ dist z y := by
        exact WithLp.dist_snd_le z y
      have htri3 : ‖(WithLp.ofLp pz).2‖ ≤
          dist (WithLp.ofLp pz).2 (WithLp.ofLp py).2 + ‖(WithLp.ofLp py).2‖ := by
        calc
          ‖(WithLp.ofLp pz).2‖ =
              ‖((WithLp.ofLp pz).2 - (WithLp.ofLp py).2) + (WithLp.ofLp py).2‖ := by
            congr 1
            abel
          _ ≤ ‖(WithLp.ofLp pz).2 - (WithLp.ofLp py).2‖ + ‖(WithLp.ofLp py).2‖ :=
            norm_add_le _ _
          _ = dist (WithLp.ofLp pz).2 (WithLp.ofLp py).2 + ‖(WithLp.ofLp py).2‖ := by
            rw [dist_eq_norm]
      nlinarith [hy3, hdist3, hdist_outer, le_of_lt hdy, htri3]
    have hz1 : |(WithLp.ofLp z).1| ≤ 2 * h₀ :=
      le_trans (le_of_forall_pos_le_add hforall1) (by linarith)
    have hz2 : ‖(WithLp.ofLp pz).1‖ ≤ 2 * h₁ :=
      le_trans (le_of_forall_pos_le_add hforall2) (by linarith)
    have hz3 : ‖(WithLp.ofLp pz).2‖ ≤ 2 * h₂ :=
      le_trans (le_of_forall_pos_le_add hforall3) (by linarith)
    dsimp [B', Metric.prodBox]
    exact ⟨hz1, by simpa [pz] using hz2, by simpa [pz] using hz3⟩
  constructor
  · exact hcthick
  · -- volume half
    let inner : Set (WithLp 2 (F₁ × F₂)) :=
      WithLp.ofLp ⁻¹' (Metric.closedBall (0 : F₁) h₁ ×ˢ Metric.closedBall (0 : F₂) h₂)
    let inner₂ : Set (WithLp 2 (F₁ × F₂)) :=
      WithLp.ofLp ⁻¹'
        (Metric.closedBall (0 : F₁) (2 * h₁) ×ˢ Metric.closedBall (0 : F₂) (2 * h₂))
    have hf : MeasurePreserving (@WithLp.ofLp 2 (ℝ × WithLp 2 (F₁ × F₂))) :=
      WithLp.volume_preserving_ofLp ℝ (WithLp 2 (F₁ × F₂))
    have hg : MeasurePreserving (@WithLp.ofLp 2 (F₁ × F₂)) :=
      WithLp.volume_preserving_ofLp F₁ F₂
    have hB_eq : B = (@WithLp.ofLp 2 (ℝ × WithLp 2 (F₁ × F₂))) ⁻¹'
        (Set.Icc (-h₀) h₀ ×ˢ inner) := by
      ext z
      simp [B, Metric.prodBox, inner, abs_le]
    have hB₂_eq : B' = (@WithLp.ofLp 2 (ℝ × WithLp 2 (F₁ × F₂))) ⁻¹'
        (Set.Icc (-(2 * h₀)) (2 * h₀) ×ˢ inner₂) := by
      ext z
      simp [B', Metric.prodBox, inner₂, abs_le]
    have hmeas_inner : MeasurableSet inner := by
      change MeasurableSet
        ((WithLp.ofLp : WithLp 2 (F₁ × F₂) → F₁ × F₂) ⁻¹'
          (Metric.closedBall (0 : F₁) h₁ ×ˢ Metric.closedBall (0 : F₂) h₂))
      exact hg.measurable (measurableSet_closedBall.prod measurableSet_closedBall)
    have hmeas_inner₂ : MeasurableSet inner₂ := by
      change MeasurableSet
        ((WithLp.ofLp : WithLp 2 (F₁ × F₂) → F₁ × F₂) ⁻¹'
          (Metric.closedBall (0 : F₁) (2 * h₁) ×ˢ Metric.closedBall (0 : F₂) (2 * h₂)))
      exact hg.measurable (measurableSet_closedBall.prod measurableSet_closedBall)
    have hvol_inner : volume inner = volume (Metric.closedBall (0 : F₁) h₁)
        * volume (Metric.closedBall (0 : F₂) h₂) := by
      change volume
        ((WithLp.ofLp : WithLp 2 (F₁ × F₂) → F₁ × F₂) ⁻¹'
          (Metric.closedBall (0 : F₁) h₁ ×ˢ Metric.closedBall (0 : F₂) h₂)) = _
      rw [hg.measure_preimage (measurableSet_closedBall.prod measurableSet_closedBall).nullMeasurableSet,
        MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod]
    have hvol_inner₂ : volume inner₂ = volume (Metric.closedBall (0 : F₁) (2 * h₁))
        * volume (Metric.closedBall (0 : F₂) (2 * h₂)) := by
      change volume
        ((WithLp.ofLp : WithLp 2 (F₁ × F₂) → F₁ × F₂) ⁻¹'
          (Metric.closedBall (0 : F₁) (2 * h₁) ×ˢ Metric.closedBall (0 : F₂) (2 * h₂))) = _
      rw [hg.measure_preimage (measurableSet_closedBall.prod measurableSet_closedBall).nullMeasurableSet,
        MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod]
    have hmeas : MeasurableSet (Set.Icc (-h₀) h₀ ×ˢ inner) :=
      measurableSet_Icc.prod hmeas_inner
    have hmeas₂ : MeasurableSet (Set.Icc (-(2 * h₀)) (2 * h₀) ×ˢ inner₂) :=
      measurableSet_Icc.prod hmeas_inner₂
    have hvolB : volume B = ENNReal.ofReal (2 * h₀)
        * volume (Metric.closedBall (0 : F₁) h₁) * volume (Metric.closedBall (0 : F₂) h₂) := by
      rw [hB_eq, hf.measure_preimage hmeas.nullMeasurableSet,
        MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod, hvol_inner,
        Real.volume_Icc]
      ring_nf
    have hvolB₂ : volume B' = ENNReal.ofReal (4 * h₀)
        * volume (Metric.closedBall (0 : F₁) (2 * h₁)) * volume (Metric.closedBall (0 : F₂) (2 * h₂)) := by
      rw [hB₂_eq, hf.measure_preimage hmeas₂.nullMeasurableSet,
        MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod, hvol_inner₂,
        Real.volume_Icc]
      ring_nf
    have hball₁ : volume (Metric.closedBall (0 : F₁) (2 * h₁))
        = (2 : ENNReal) ^ Module.finrank ℝ F₁ * volume (Metric.closedBall (0 : F₁) h₁) := by
      have h1 : volume (Metric.closedBall (0 : F₁) (2 * h₁)) =
          ENNReal.ofReal ((2 * h₁) ^ Module.finrank ℝ F₁) * volume (Metric.ball (0 : F₁) 1) := by
        exact MeasureTheory.Measure.addHaar_closedBall volume (0 : F₁) (by positivity : 0 ≤ 2 * h₁)
      have h2 : volume (Metric.closedBall (0 : F₁) h₁) =
          ENNReal.ofReal (h₁ ^ Module.finrank ℝ F₁) * volume (Metric.ball (0 : F₁) 1) := by
        exact MeasureTheory.Measure.addHaar_closedBall volume (0 : F₁) h1_nonneg
      rw [h1, h2]
      rw [mul_pow]
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (2 : ℝ) ^ Module.finrank ℝ F₁)]
      rw [ENNReal.ofReal_pow (by norm_num : 0 ≤ (2 : ℝ)) (Module.finrank ℝ F₁)]
      rw [ENNReal.ofReal_ofNat]
      ring
    have hball₂ : volume (Metric.closedBall (0 : F₂) (2 * h₂))
        = (2 : ENNReal) ^ Module.finrank ℝ F₂ * volume (Metric.closedBall (0 : F₂) h₂) := by
      have h1 : volume (Metric.closedBall (0 : F₂) (2 * h₂)) =
          ENNReal.ofReal ((2 * h₂) ^ Module.finrank ℝ F₂) * volume (Metric.ball (0 : F₂) 1) := by
        exact MeasureTheory.Measure.addHaar_closedBall volume (0 : F₂) (by positivity : 0 ≤ 2 * h₂)
      have h2 : volume (Metric.closedBall (0 : F₂) h₂) =
          ENNReal.ofReal (h₂ ^ Module.finrank ℝ F₂) * volume (Metric.ball (0 : F₂) 1) := by
        exact MeasureTheory.Measure.addHaar_closedBall volume (0 : F₂) h2_nonneg
      rw [h1, h2]
      rw [mul_pow]
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (2 : ℝ) ^ Module.finrank ℝ F₂)]
      rw [ENNReal.ofReal_pow (by norm_num : 0 ≤ (2 : ℝ)) (Module.finrank ℝ F₂)]
      rw [ENNReal.ofReal_ofNat]
      ring
    have hfac : ENNReal.ofReal (4 * h₀) = (2 : ENNReal) * ENNReal.ofReal (2 * h₀) := by
      rw [show 4 * h₀ = (2 : ℝ) * (2 * h₀) by ring]
      rw [ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ))]
      rw [ENNReal.ofReal_ofNat]
    have hpow : (2 : ENNReal) ^ (1 + Module.finrank ℝ F₁ + Module.finrank ℝ F₂)
        = 2 * (2 : ENNReal) ^ Module.finrank ℝ F₁ * (2 : ENNReal) ^ Module.finrank ℝ F₂ := by
      rw [pow_add, pow_add]
      norm_num
    have hvolB'eq : volume B' =
        (2 : ENNReal) ^ (1 + Module.finrank ℝ F₁ + Module.finrank ℝ F₂) * volume B := by
      rw [hvolB₂, hvolB, hball₁, hball₂, hfac, hpow]
      ring
    calc
      volume (cthickening s B) ≤ volume B' := measure_mono hcthick
      _ = (2 : ENNReal) ^ (1 + Module.finrank ℝ F₁ + Module.finrank ℝ F₂) * volume B := hvolB'eq

/-- **The parameter-region constant** `c_{lem:endpointRegionMeasure}(n) = 24 ω_{n-1}²`
(blueprint `def:endpointRegionMeasureConstant`), where `ω_d` is the volume of the unit ball of
`ℝ ^ d`.  It is written here as `24 (2 ^ (n-1) · C_cov(n-1)) ^ 2`, using
`ω_d = 2 ^ d · Metric.coveringNumber_mul_pow_le_volume_cthickening.C d`.

The factor `24 = 2 · 12` comes from the axial side length `24 C C_n² σ` of the box, and each
`ω_{n-1}` from one of the two transverse balls. -/
noncomputable abbrev parameterRegion.C (n : ℕ) : NNReal :=
  24 * (2 ^ (n - 1) * Metric.coveringNumber_mul_pow_le_volume_cthickening.C (n - 1)) ^ 2

/-- **The parameter region `𝓑`** of blueprint `lem:endpointRegionMeasure`: the centred box
`[-3 c_* σ C_n / (2κ), 3 c_* σ C_n / (2κ)] × B̄(0, C_n ρ) × B̄(0, C_n ρ)` inside
`Tube.parameterSpace V`, with `σ = C⁻¹ ρ`. -/
noncomputable def parameterRegion (V : Tube ρ E) (C : NNReal) : Set (parameterSpace V) :=
  Metric.prodBox
    (3 * (1 / (4 * (Module.finrank ℝ E : ℝ))) * ((C : ℝ)⁻¹ * (ρ : ℝ))
      * Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E)
      / (2 * (axialSeparation.kappa (Module.finrank ℝ E) C : ℝ)))
    (Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) * (ρ : ℝ))
    (Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) * (ρ : ℝ))

/-- **The constant of the parameter region** (blueprint `lem:endpointRegionConstantArith`), a
pure identity between real numbers.

Substituting `κ = c_* / (8 C C_n)` turns the axial side `2 h₀ = 3 c_* σ C_n / κ` into
`24 C C_n² σ`, and `2n - 2 = 2(n-1)` (truncated subtraction in `ℕ`, legitimate as `n ≥ 1`)
turns `(C_n ρ) ^ (2n-2)` into `C_n ^ (2n-2) ρ ^ (2n-2)`. -/
theorem parameterRegion.volume_formula_eq [Nontrivial E] {C : NNReal} (hC : 1 ≤ C)
    (hρ0 : 0 < ρ) :
    2 * (3 * (1 / (4 * (Module.finrank ℝ E : ℝ))) * ((C : ℝ)⁻¹ * (ρ : ℝ))
          * Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E)
          / (2 * (axialSeparation.kappa (Module.finrank ℝ E) C : ℝ)))
        * ((2 : ℝ) ^ (Module.finrank ℝ E - 1)
            * (Metric.coveringNumber_mul_pow_le_volume_cthickening.C
                (Module.finrank ℝ E - 1) : ℝ)) ^ 2
        * (Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) * (ρ : ℝ))
            ^ (2 * Module.finrank ℝ E - 2)
      = (parameterRegion.C (Module.finrank ℝ E) : ℝ) * (C : ℝ)
        * Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) ^ (2 * Module.finrank ℝ E)
        * ((C : ℝ)⁻¹ * (ρ : ℝ)) * (ρ : ℝ) ^ (2 * Module.finrank ℝ E - 2) := by
  classical
  set n : ℕ := Module.finrank ℝ E
  set Cn : ℝ := Kakeya.Tube.tubeOverlapCoreClose.C n
  set W : ℝ := (2 : ℝ) ^ (n - 1) *
    (Metric.coveringNumber_mul_pow_le_volume_cthickening.C (n - 1) : ℝ)
  set σ : ℝ := (C : ℝ)⁻¹ * (ρ : ℝ)
  set κ : ℝ := (axialSeparation.kappa n C : ℝ)
  set cstar : ℝ := 1 / (4 * (n : ℝ))
  -- nonzeroness / positivity
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast Module.finrank_pos (R := ℝ) (M := E)
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hn1 : 1 ≤ n := by
    have h : 0 < Module.finrank ℝ E := Module.finrank_pos (R := ℝ) (M := E)
    simpa [n] using (Nat.succ_le_iff.mpr h)
  have hCpos : 0 < (C : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hC)
  have hC0 : (C : ℝ) ≠ 0 := ne_of_gt hCpos
  have hCnpos : 0 < Cn := by
    dsimp [Cn]
    exact lt_trans zero_lt_one (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C n)
  have hCn0 : Cn ≠ 0 := ne_of_gt hCnpos
  have hκval : κ = 1 / (32 * (n : ℝ) * (C : ℝ) * Cn) := by
    dsimp [κ]
    have hmax : max (Kakeya.Tube.tubeOverlapCoreClose.C n) 0 = Cn := by
      rw [max_eq_left (le_trans zero_le_one (le_of_lt (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C n)))]
    simp [hmax]
  have hparamC : (parameterRegion.C n : ℝ) = 24 * W ^ 2 := by
    dsimp [parameterRegion.C, W]
  have hpow : Cn ^ 2 * (Cn * (ρ : ℝ)) ^ (2 * n - 2) =
      Cn ^ (2 * n) * (ρ : ℝ) ^ (2 * n - 2) := by
    rw [mul_pow]
    rw [← mul_assoc, ← pow_add]
    have hsum : 2 + (2 * n - 2) = 2 * n := by omega
    rw [hsum]
  have haxial : 2 * (3 * cstar * σ * Cn / (2 * κ)) = 24 * (C : ℝ) * Cn ^ 2 * σ := by
    dsimp [σ, cstar]
    rw [hκval]
    field_simp [hn0, hC0, hCn0]
    ring
  calc
    2 * (3 * (1 / (4 * (Module.finrank ℝ E : ℝ))) * ((C : ℝ)⁻¹ * (ρ : ℝ))
          * Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E)
          / (2 * (axialSeparation.kappa (Module.finrank ℝ E) C : ℝ)))
        * ((2 : ℝ) ^ (Module.finrank ℝ E - 1)
            * (Metric.coveringNumber_mul_pow_le_volume_cthickening.C
                (Module.finrank ℝ E - 1) : ℝ)) ^ 2
        * (Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) * (ρ : ℝ))
            ^ (2 * Module.finrank ℝ E - 2)
        = 2 * (3 * cstar * σ * Cn / (2 * κ)) * W ^ 2 * (Cn * (ρ : ℝ)) ^ (2 * n - 2) := by
          dsimp [n, Cn, W, κ, σ, cstar]
    _ = (24 * (C : ℝ) * Cn ^ 2 * σ) * W ^ 2 * (Cn * (ρ : ℝ)) ^ (2 * n - 2) := by
          rw [haxial]
    _ = 24 * (C : ℝ) * σ * W ^ 2 * (Cn ^ 2 * (Cn * (ρ : ℝ)) ^ (2 * n - 2)) := by
          ring
    _ = 24 * (C : ℝ) * σ * W ^ 2 * (Cn ^ (2 * n) * (ρ : ℝ) ^ (2 * n - 2)) := by
          rw [hpow]
    _ = 24 * W ^ 2 * (C : ℝ) * Cn ^ (2 * n) * σ * (ρ : ℝ) ^ (2 * n - 2) := by
          ring
    _ = (parameterRegion.C (Module.finrank ℝ E) : ℝ)
        * (C : ℝ) * Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E)
            ^ (2 * Module.finrank ℝ E)
        * ((C : ℝ)⁻¹ * (ρ : ℝ)) * (ρ : ℝ) ^ (2 * Module.finrank ℝ E - 2) := by
          rw [hparamC]

/-- **The projection onto the transverse space is the transverse part** (blueprint
`lem:perpProjectionNorm`).

`Tube.parameterMap` stores the transverse coordinates as elements of the subtype
`(ℝ ∙ e)ᗮ`, whereas `Tube.parameters_mem_of_subset_dilate` bounds the vector
`d - ⟪e, d⟫ • e` of `E`.  This lemma identifies the two, and is used at both transverse
coordinates of every parameter. -/
theorem _root_.Submodule.norm_orthogonalProjectionOnto_perp_span_singleton {e : E}
    (he : ‖e‖ = 1) (d : E) :
    ((((ℝ ∙ e)ᗮ).orthogonalProjectionOnto d : E) = d - inner ℝ e d • e) ∧
      ‖((ℝ ∙ e)ᗮ).orthogonalProjectionOnto d‖ = ‖d - inner ℝ e d • e‖ := by
  have hproj : (((ℝ ∙ e)ᗮ).orthogonalProjectionOnto d : E) = d - inner ℝ e d • e := by
    rw [Submodule.coe_orthogonalProjectionOnto_apply, Submodule.starProjection_orthogonal']
    change d - (ℝ ∙ e).starProjection d = d - inner ℝ e d • e
    rw [Submodule.starProjection_unit_singleton ℝ he d]
  constructor
  · exact hproj
  · rw [Submodule.coe_norm, hproj]

/-- **A thin tube in a thin dilate has its parameter in the region** (blueprint
`lem:parameterMapMemRegion`).

The three coordinate bounds cutting out `Tube.parameterRegion` are the three items of
`Tube.parameters_mem_of_subset_dilate`: the axial bound `3 C_n / 2` stretched by the
nonnegative rescaling factor `c_* σ / κ`, and the two transverse bounds `C_n ρ` read through
`Submodule.norm_orthogonalProjectionOnto_perp_span_singleton`. -/
theorem parameterMap_mem_parameterRegion {C : NNReal} (hC : 1 ≤ C) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (V : Tube ρ E) (U : Tube (C⁻¹ * ρ) E)
    (hU : U.carrier ⊆ (Kakeya.Tube.dilate V
      (Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E))).carrier) :
    parameterMap V C U ∈ parameterRegion V C := by
  classical
  let n : ℕ := Module.finrank ℝ E
  let cstar : ℝ := 1 / (4 * (n : ℝ))
  let sg : ℝ := (C : ℝ)⁻¹ * (ρ : ℝ)
  let Cn : ℝ := Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E)
  let κ : ℝ := (axialSeparation.kappa (Module.finrank ℝ E) C : ℝ)
  -- positivity of the constituents of the rescaling factor `c_* σ / κ`
  have hnR : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
  have hcstarn : 0 ≤ cstar := by
    dsimp [cstar]
    exact one_div_nonneg.mpr (mul_nonneg (by norm_num) hnR)
  have hCpos : (0 : NNReal) < C := lt_of_lt_of_le zero_lt_one hC
  have hsg0 : 0 ≤ sg := by
    dsimp [sg]
    exact mul_nonneg (inv_nonneg.mpr (le_of_lt (NNReal.coe_pos.mpr hCpos)))
      ((NNReal.coe_pos.mpr hρ0).le)
  have hκn : 0 ≤ κ := by
    dsimp [κ]
    positivity
  have hcoerce : ((C⁻¹ * ρ : NNReal) : ℝ) = (C : ℝ)⁻¹ * (ρ : ℝ) := by
    rw [NNReal.coe_mul, NNReal.coe_inv]
  -- `σ = C⁻¹ρ ≤ ρ` since `C ≥ 1`, so `parameters_mem_of_subset_dilate` applies
  have hσρ : (C⁻¹ * ρ : NNReal) ≤ ρ := by
    have hCinvle1 : (C : NNReal)⁻¹ ≤ 1 := by
      exact (inv_le_one₀ hCpos).mpr hC
    simpa [mul_comm] using mul_le_of_le_one_right (le_of_lt hρ0) hCinvle1
  have hP := parameters_mem_of_subset_dilate (σ := C⁻¹ * ρ) hρ0 hρ1 hσρ V U hU
  have hxax : |inner ℝ (U.x - V.center) V.direction| ≤ 3 / 2 * Cn := by
    simpa [Cn] using hP.1.1
  have hxpn : ‖U.x - V.center - inner ℝ V.direction (U.x - V.center) • V.direction‖
      ≤ Cn * (ρ : ℝ) := by
    simpa [Cn] using hP.2.1.1
  have hypn : ‖U.y - V.center - inner ℝ V.direction (U.y - V.center) • V.direction‖
      ≤ Cn * (ρ : ℝ) := by
    simpa [Cn] using hP.2.1.2
  -- the two transverse coordinates of `parameterMap` are the corresponding projections
  have hproj_x : ‖((ℝ ∙ V.direction)ᗮ).orthogonalProjectionOnto (U.x - V.center)‖
      ≤ Cn * (ρ : ℝ) := by
    have h := (Submodule.norm_orthogonalProjectionOnto_perp_span_singleton
      V.norm_direction (U.x - V.center)).2
    rw [h]
    exact hxpn
  have hproj_y : ‖((ℝ ∙ V.direction)ᗮ).orthogonalProjectionOnto (U.y - V.center)‖
      ≤ Cn * (ρ : ℝ) := by
    have h := (Submodule.norm_orthogonalProjectionOnto_perp_span_singleton
      V.norm_direction (U.y - V.center)).2
    rw [h]
    exact hypn
  -- axial coordinate, rescaled by the nonnegative factor `c_* σ / κ`
  have hfac0 : 0 ≤ cstar * sg / κ := by
    exact div_nonneg (mul_nonneg hcstarn hsg0) hκn
  have haxial : |cstar * sg / κ * inner ℝ (U.x - V.center) V.direction|
      ≤ 3 * cstar * sg * Cn / (2 * κ) := by
    calc
      |cstar * sg / κ * inner ℝ (U.x - V.center) V.direction|
          = |cstar * sg / κ| * |inner ℝ (U.x - V.center) V.direction| := by rw [abs_mul]
      _ = cstar * sg / κ * |inner ℝ (U.x - V.center) V.direction| := by
            rw [abs_of_nonneg hfac0]
      _ ≤ cstar * sg / κ * (3 / 2 * Cn) := by
            exact mul_le_mul_of_nonneg_left hxax hfac0
      _ = 3 * cstar * sg * Cn / (2 * κ) := by
            ring_nf
  -- the three half-sides of `Tube.parameterRegion`
  let H0 : ℝ := 3 * cstar * sg * Cn / (2 * κ)
  let H1 : ℝ := Cn * (ρ : ℝ)
  let H2 : ℝ := Cn * (ρ : ℝ)
  have hv0 : |cstar * sg / κ * inner ℝ (U.x - V.center) V.direction| ≤ H0 := by
    simpa [H0] using haxial
  have hv1 : ‖((ℝ ∙ V.direction)ᗮ).orthogonalProjectionOnto (U.x - V.center)‖ ≤ H1 := by
    simpa [H1] using hproj_x
  have hv2 : ‖((ℝ ∙ V.direction)ᗮ).orthogonalProjectionOnto (U.y - V.center)‖ ≤ H2 := by
    simpa [H2] using hproj_y
  -- membership in the box is the conjunction of the three coordinate bounds
  rw [parameterRegion]
  change parameterMap V C U ∈ Metric.prodBox H0 H1 H2
  dsimp [Metric.prodBox]
  constructor
  · have hfst : WithLp.fst (parameterMap V C U) =
        cstar * sg / κ * inner ℝ (U.x - V.center) V.direction := by
        simp [parameterMap, hcoerce, cstar, sg, κ, n]
    rw [hfst]
    exact hv0
  · constructor
    · have hf1 : (WithLp.snd (parameterMap V C U)).fst =
          ((ℝ ∙ V.direction)ᗮ).orthogonalProjectionOnto (U.x - V.center) := by
          simp [parameterMap]
      rw [hf1]
      exact hv1
    · have hf2 : (WithLp.snd (parameterMap V C U)).snd =
          ((ℝ ∙ V.direction)ᗮ).orthogonalProjectionOnto (U.y - V.center) := by
          simp [parameterMap]
      rw [hf2]
      exact hv2

/-- **Volume of the rescaled parameter region** (blueprint `lem:endpointRegionVolume`).

`Metric.volume_prodBox` at `F₁ = F₂ = e^⊥` splits the box into three factors, and
`Tube.volume_closedBall_perpSpace` evaluates each transverse ball; all three factors are
`ENNReal.ofReal`s of nonnegative reals, so they merge into a single one. -/
theorem volume_parameterRegion [Nontrivial E] {C : NNReal} (hC : 1 ≤ C) (hρ0 : 0 < ρ)
    (V : Tube ρ E) :
    volume (parameterRegion V C)
      = ENNReal.ofReal (2 * (3 * (1 / (4 * (Module.finrank ℝ E : ℝ))) * ((C : ℝ)⁻¹ * (ρ : ℝ))
            * Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E)
            / (2 * (axialSeparation.kappa (Module.finrank ℝ E) C : ℝ)))
          * ((2 : ℝ) ^ (Module.finrank ℝ E - 1)
              * (Metric.coveringNumber_mul_pow_le_volume_cthickening.C
                  (Module.finrank ℝ E - 1) : ℝ)) ^ 2
          * (Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) * (ρ : ℝ))
              ^ (2 * Module.finrank ℝ E - 2)) := by
  classical
  set n : ℕ := Module.finrank ℝ E
  set cstar : ℝ := 1 / (4 * (n : ℝ))
  set sg : ℝ := (C : ℝ)⁻¹ * (ρ : ℝ)
  set Cn : ℝ := Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E)
  set κ : ℝ := (axialSeparation.kappa (Module.finrank ℝ E) C : ℝ)
  let h0 : ℝ := 3 * cstar * sg * Cn / (2 * κ)
  let h1 : ℝ := Cn * (ρ : ℝ)
  let h2 : ℝ := Cn * (ρ : ℝ)
  let ω : ℝ := (2 : ℝ) ^ (n - 1) *
    (Metric.coveringNumber_mul_pow_le_volume_cthickening.C (n - 1) : ℝ)
  have hn : 1 ≤ n := by
    dsimp [n]
    exact Nat.succ_le_of_lt (Module.finrank_pos (R := ℝ) (M := E))
  have hκpos : 0 < κ := by
    dsimp [κ]
    exact (axialSeparation.coe_kappa (n := Module.finrank ℝ E) hn hC).2.2
  have hκnonneg : 0 ≤ κ := le_of_lt hκpos
  have hCpos : (0 : NNReal) < C := lt_of_lt_of_le zero_lt_one hC
  have hcstar_nonneg : 0 ≤ cstar := by
    dsimp [cstar]
    exact one_div_nonneg.mpr (mul_nonneg (by norm_num) (by exact_mod_cast (Nat.zero_le n)))
  have hsg_nonneg : 0 ≤ sg := by
    dsimp [sg]
    exact mul_nonneg (inv_nonneg.mpr (le_of_lt (NNReal.coe_pos.mpr hCpos)))
      ((NNReal.coe_pos.mpr hρ0).le)
  have hCn_pos : 0 < Cn := by
    dsimp [Cn]
    exact lt_trans zero_lt_one (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C (Module.finrank ℝ E))
  have hCn_nonneg : 0 ≤ Cn := le_of_lt hCn_pos
  have h1_nonneg : 0 ≤ h1 := by
    dsimp [h1]
    exact mul_nonneg hCn_nonneg ((NNReal.coe_pos.mpr hρ0).le)
  have h0_nonneg : 0 ≤ h0 := by
    dsimp [h0]
    positivity
  have hω_nonneg : 0 ≤ ω := by
    dsimp [ω]
    exact mul_nonneg (pow_nonneg (by norm_num) _) (NNReal.coe_nonneg _)
  have hB_nonneg : 0 ≤ ω * h1 ^ (n - 1) :=
    mul_nonneg hω_nonneg (pow_nonneg h1_nonneg _)
  have hA_nonneg : 0 ≤ 2 * h0 := mul_nonneg (by norm_num) h0_nonneg
  have h_nat : (n - 1) + (n - 1) = 2 * n - 2 := by omega
  rw [parameterRegion, Metric.volume_prodBox]
  rw [Tube.volume_closedBall_perpSpace V h1_nonneg]
  calc
    ENNReal.ofReal (2 * h0) * ENNReal.ofReal (ω * h1 ^ (n - 1))
        * ENNReal.ofReal (ω * h1 ^ (n - 1))
        = ENNReal.ofReal (2 * h0)
            * ENNReal.ofReal ((ω * h1 ^ (n - 1)) * (ω * h1 ^ (n - 1))) := by
            rw [mul_assoc]
            rw [← ENNReal.ofReal_mul hB_nonneg]
    _ = ENNReal.ofReal ((2 * h0) * ((ω * h1 ^ (n - 1)) * (ω * h1 ^ (n - 1)))) := by
            rw [← ENNReal.ofReal_mul hA_nonneg]
    _ = ENNReal.ofReal ((2 * h0) * ω ^ 2 * h1 ^ (2 * n - 2)) := by
            congr 1
            rw [show (ω * h1 ^ (n - 1)) * (ω * h1 ^ (n - 1)) = ω ^ 2 * h1 ^ (2 * n - 2) by
              calc
                (ω * h1 ^ (n - 1)) * (ω * h1 ^ (n - 1))
                    = ω * ω * (h1 ^ (n - 1) * h1 ^ (n - 1)) := by
                      ring
                _ = ω * ω * h1 ^ ((n - 1) + (n - 1)) := by
                      rw [← pow_add]
                _ = ω ^ 2 * h1 ^ (2 * n - 2) := by
                      rw [← pow_two ω, h_nat]]
            ring

/-- **Measure of the rescaled parameter region** (blueprint `lem:endpointRegionMeasure`).

Every `C⁻¹ρ`-tube inside the dilate `C_n · V` has its parameter in the region `𝓑`, and
`|𝓑| = 3 c_* σ C_n / κ · ω_{n-1}² (C_n ρ) ^ (2n-2)
= c_{lem:endpointRegionMeasure}(n) · C C_n^{2n} σ ρ^{2n-2}` after substituting
`κ = c_* / (8 C C_n)`.  Only the upper bound is recorded, which is what the count consumes. -/
theorem volume_parameterRegion_le [Nontrivial E] {C : NNReal} (hC : 1 ≤ C) (hρ0 : 0 < ρ)
    (hρ1 : ρ ≤ 1) (V : Tube ρ E) :
    (∀ U : Tube (C⁻¹ * ρ) E,
        U.carrier ⊆ (Kakeya.Tube.dilate V
          (Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E))).carrier →
        parameterMap V C U ∈ parameterRegion V C) ∧
      volume (parameterRegion V C)
        ≤ ENNReal.ofReal ((parameterRegion.C (Module.finrank ℝ E) : ℝ) * (C : ℝ)
            * Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E)
                ^ (2 * Module.finrank ℝ E)
            * ((C : ℝ)⁻¹ * (ρ : ℝ)) * (ρ : ℝ) ^ (2 * Module.finrank ℝ E - 2)) := by
  refine ⟨?_, ?_⟩
  · exact fun U hU => parameterMap_mem_parameterRegion hC hρ0 hρ1 V U hU
  · rw [volume_parameterRegion hC hρ0 V]
    rw [parameterRegion.volume_formula_eq hC hρ0]

/-! ### The thin regime -/

/-- **Orienting a family against a reference direction** (blueprint
`lem:tubeReverseOrientation`).

`Tube.reverse` exchanges the two core endpoints of a tube, hence flips its direction
(`Tube.reverse_direction`) and leaves its carrier untouched (`Tube.reverse_carrier`).  Choosing,
for each member of a family, between the tube and its reversal therefore produces a family with
the *same carriers* — so pairwise essential distinctness, containment in an arbitrary set and
the index set all transfer verbatim — every member of which has direction making a nonnegative
inner product with the reference vector `e`.

This is what supplies the two orientation hypotheses of
`Tube.axial_separation_of_essDistinct`, which are conditions on the *tubes* and not on their
carriers, to a family carrying no orientation assumption.  The blueprint fixes the choice
explicitly; here it is existentially quantified, the consumer using nothing about the new family
beyond the two stated properties. -/
theorem exists_orientedFamily {ι : Type*} {δ : NNReal} (U : ι → Tube δ E) (e : E) :
    ∃ U' : ι → Tube δ E,
      ∀ j, (U' j).carrier = (U j).carrier ∧ 0 ≤ inner ℝ (U' j).direction e := by
  classical
  refine ⟨(fun j => if 0 ≤ inner ℝ (U j).direction e then U j else (U j).reverse), ?_⟩
  intro j
  by_cases h : 0 ≤ inner ℝ (U j).direction e
  · dsimp
    rw [if_pos h]
    exact ⟨rfl, h⟩
  · dsimp
    rw [if_neg h]
    exact ⟨(U j).reverse_carrier, by
      rw [Tube.reverse_direction, inner_neg_left]
      exact neg_nonneg.mpr (le_of_not_ge h)⟩

/-- **Dimension of the parameter space**: `dim (ℝ × e^⊥ × e^⊥) = 1 + 2 (n - 1) = 2 n - 1`.

This is step (4) of the proof of blueprint `lem:essDistinctTubesInThinDilate` rather than a
blueprint lemma of its own; it is a declaration here because `Tube.parameterSpace` is a nested
`WithLp 2` product, so the reduction to `Tube.finrank_perpSpace` is not a `simp` call.  The
hypothesis `Nontrivial E` is what makes the truncated subtraction `2 n - 1` the true dimension:
at `n = 0` the left side is `1` and the right side is `0`. -/
theorem finrank_parameterSpace [Nontrivial E] (V : Tube ρ E) :
    Module.finrank ℝ (parameterSpace V) = 2 * Module.finrank ℝ E - 1 := by
  let A : Type _ := WithLp 2 (perpSpace V × perpSpace V)
  have hA : Module.finrank ℝ A = Module.finrank ℝ (perpSpace V) + Module.finrank ℝ (perpSpace V) := by
    calc
      Module.finrank ℝ A = Module.finrank ℝ (perpSpace V × perpSpace V) := by
        exact LinearEquiv.finrank_eq (WithLp.linearEquiv 2 ℝ (perpSpace V × perpSpace V))
      _ = Module.finrank ℝ (perpSpace V) + Module.finrank ℝ (perpSpace V) := Module.finrank_prod
  calc
    Module.finrank ℝ (parameterSpace V) = Module.finrank ℝ (ℝ × A) := by
      exact LinearEquiv.finrank_eq (WithLp.linearEquiv 2 ℝ (ℝ × A))
    _ = Module.finrank ℝ ℝ + Module.finrank ℝ A := Module.finrank_prod
    _ = 1 + Module.finrank ℝ A := by simp
    _ = 1 + Module.finrank ℝ (perpSpace V) + Module.finrank ℝ (perpSpace V) := by
      rw [hA]
      omega
    _ = 2 * Module.finrank ℝ E - 1 := by
      rw [Tube.finrank_perpSpace V]
      have hn : 1 ≤ Module.finrank ℝ E := Module.finrank_pos (R := ℝ) (M := E)
      omega

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Each coordinate of the parameter space is dominated by the distance** (blueprint
`lem:parameterSpaceMaxNormSeparation`, item (a)).

`Tube.parameterSpace` carries the `L²` norm `‖(t, v, v')‖ = √(t² + ‖v‖² + ‖v'‖²)`, so each of
the three coordinate distances is at most the distance, and hence so is their maximum. -/
theorem max_coord_dist_le_dist (V : Tube ρ E) (z z' : parameterSpace V) :
    max (max ‖WithLp.fst (WithLp.snd z) - WithLp.fst (WithLp.snd z')‖
            ‖WithLp.snd (WithLp.snd z) - WithLp.snd (WithLp.snd z')‖)
        (|WithLp.fst z - WithLp.fst z'|)
      ≤ dist z z' := by
  have hT1 : ‖WithLp.fst (WithLp.snd z) - WithLp.fst (WithLp.snd z')‖ ≤ dist z z' := by
    calc
      ‖WithLp.fst (WithLp.snd z) - WithLp.fst (WithLp.snd z')‖
          = dist (WithLp.fst (WithLp.snd z)) (WithLp.fst (WithLp.snd z')) := by rw [dist_eq_norm]
      _ ≤ dist (WithLp.snd z) (WithLp.snd z') :=
        WithLp.dist_fst_le (WithLp.snd z) (WithLp.snd z')
      _ ≤ dist z z' := WithLp.dist_snd_le z z'
  have hT2 : ‖WithLp.snd (WithLp.snd z) - WithLp.snd (WithLp.snd z')‖ ≤ dist z z' := by
    calc
      ‖WithLp.snd (WithLp.snd z) - WithLp.snd (WithLp.snd z')‖
          = dist (WithLp.snd (WithLp.snd z)) (WithLp.snd (WithLp.snd z')) := by rw [dist_eq_norm]
      _ ≤ dist (WithLp.snd z) (WithLp.snd z') :=
        WithLp.dist_snd_le (WithLp.snd z) (WithLp.snd z')
      _ ≤ dist z z' := WithLp.dist_snd_le z z'
  have hT3 : |WithLp.fst z - WithLp.fst z'| ≤ dist z z' := by
    calc
      |WithLp.fst z - WithLp.fst z'| = dist (WithLp.fst z) (WithLp.fst z') := by rw [Real.dist_eq]
      _ ≤ dist z z' := WithLp.dist_fst_le z z'
  exact max_le (max_le hT1 hT2) hT3

/-- **From coordinate separation to separation in the parameter space** (blueprint
`lem:parameterSpaceMaxNormSeparation`, item (b)).

The centre `m` of `V` cancels in each of the three coordinates of `Ψ(U) - Ψ(U')`, which are
therefore `(p_U - p_{U'})^⊥`, `(q_U - q_{U'})^⊥` and `(c_* σ / κ) ⟪p_U - p_{U'}, e⟫`; the claim
is then `Tube.max_coord_dist_le_dist` chained with the assumed strict inequality.  The
right-hand side of `hr` is exactly the maximum appearing in
`Tube.axial_separation_of_essDistinct`, which is applied at `r = c_* σ / 4`. -/
theorem lt_dist_parameterMap_of_max_lt {σ C : NNReal} (V : Tube ρ E) (U U' : Tube σ E) {r : ℝ}
    (hr : r < max (max ‖U.x - U'.x - inner ℝ V.direction (U.x - U'.x) • V.direction‖
                      ‖U.y - U'.y - inner ℝ V.direction (U.y - U'.y) • V.direction‖)
              (1 / (4 * (Module.finrank ℝ E : ℝ)) * (σ : ℝ)
                / (axialSeparation.kappa (Module.finrank ℝ E) C : ℝ)
                * |inner ℝ (U.x - U'.x) V.direction|)) :
    r < dist (parameterMap V C U) (parameterMap V C U') := by
  let P : parameterSpace V := parameterMap V C U
  let P' : parameterSpace V := parameterMap V C U'
  let cstar : ℝ := 1 / (4 * (Module.finrank ℝ E : ℝ)) * (σ : ℝ)
      / (axialSeparation.kappa (Module.finrank ℝ E) C : ℝ)
  have hcstar_nonneg : 0 ≤ cstar := by
    dsimp [cstar]
    exact div_nonneg
      (mul_nonneg
        (one_div_nonneg.mpr (mul_nonneg (by norm_num)
          (by exact_mod_cast Nat.zero_le (Module.finrank ℝ E))))
        (NNReal.coe_nonneg σ))
      (NNReal.coe_nonneg (axialSeparation.kappa (Module.finrank ℝ E) C))
  have hcanc_x : U.x - U'.x = (U.x - V.center) - (U'.x - V.center) := by abel
  have hcanc_y : U.y - U'.y = (U.y - V.center) - (U'.y - V.center) := by abel
  have hinner_ax : inner ℝ (U.x - V.center) V.direction - inner ℝ (U'.x - V.center) V.direction
      = inner ℝ (U.x - U'.x) V.direction := by
    rw [← inner_sub_left]
    rw [hcanc_x]
  have haxial : |WithLp.fst P - WithLp.fst P'| = cstar * |inner ℝ (U.x - U'.x) V.direction| := by
    have hin : WithLp.fst P - WithLp.fst P' = cstar * inner ℝ (U.x - U'.x) V.direction := by
      calc
        WithLp.fst P - WithLp.fst P'
            = cstar * inner ℝ (U.x - V.center) V.direction
                - cstar * inner ℝ (U'.x - V.center) V.direction := by
              simp [P, P', parameterMap, cstar]
        _ = cstar * (inner ℝ (U.x - V.center) V.direction - inner ℝ (U'.x - V.center) V.direction) := by
            rw [mul_sub]
        _ = cstar * inner ℝ (U.x - U'.x) V.direction := by rw [hinner_ax]
    rw [hin, abs_mul, abs_of_nonneg hcstar_nonneg]
  have hperp_x : ((ℝ ∙ V.direction)ᗮ).orthogonalProjectionOnto (U.x - U'.x)
      = ((ℝ ∙ V.direction)ᗮ).orthogonalProjectionOnto (U.x - V.center)
          - ((ℝ ∙ V.direction)ᗮ).orthogonalProjectionOnto (U'.x - V.center) := by
    rw [hcanc_x]
    exact map_sub ((ℝ ∙ V.direction)ᗮ).orthogonalProjectionOnto (U.x - V.center) (U'.x - V.center)
  have hperp_y : ((ℝ ∙ V.direction)ᗮ).orthogonalProjectionOnto (U.y - U'.y)
      = ((ℝ ∙ V.direction)ᗮ).orthogonalProjectionOnto (U.y - V.center)
          - ((ℝ ∙ V.direction)ᗮ).orthogonalProjectionOnto (U'.y - V.center) := by
    rw [hcanc_y]
    exact map_sub ((ℝ ∙ V.direction)ᗮ).orthogonalProjectionOnto (U.y - V.center) (U'.y - V.center)
  have hT1 : ‖WithLp.fst (WithLp.snd P) - WithLp.fst (WithLp.snd P')‖
      = ‖U.x - U'.x - inner ℝ V.direction (U.x - U'.x) • V.direction‖ := by
    rw [show WithLp.fst (WithLp.snd P) = ((ℝ ∙ V.direction)ᗮ).orthogonalProjectionOnto (U.x - V.center) by
        simp [P, parameterMap]]
    rw [show WithLp.fst (WithLp.snd P') = ((ℝ ∙ V.direction)ᗮ).orthogonalProjectionOnto (U'.x - V.center) by
        simp [P', parameterMap]]
    rw [← hperp_x]
    exact (Submodule.norm_orthogonalProjectionOnto_perp_span_singleton V.norm_direction (U.x - U'.x)).2
  have hT2 : ‖WithLp.snd (WithLp.snd P) - WithLp.snd (WithLp.snd P')‖
      = ‖U.y - U'.y - inner ℝ V.direction (U.y - U'.y) • V.direction‖ := by
    rw [show WithLp.snd (WithLp.snd P) = ((ℝ ∙ V.direction)ᗮ).orthogonalProjectionOnto (U.y - V.center) by
        simp [P, parameterMap]]
    rw [show WithLp.snd (WithLp.snd P') = ((ℝ ∙ V.direction)ᗮ).orthogonalProjectionOnto (U'.y - V.center) by
        simp [P', parameterMap]]
    rw [← hperp_y]
    exact (Submodule.norm_orthogonalProjectionOnto_perp_span_singleton V.norm_direction (U.y - U'.y)).2
  have hc : max (max ‖U.x - U'.x - inner ℝ V.direction (U.x - U'.x) • V.direction‖
                  ‖U.y - U'.y - inner ℝ V.direction (U.y - U'.y) • V.direction‖)
              (cstar * |inner ℝ (U.x - U'.x) V.direction|) ≤ dist P P' := by
    simpa [hT1, hT2, haxial, P, P'] using Tube.max_coord_dist_le_dist V P P'
  simpa [cstar, P, P'] using lt_of_lt_of_le hr hc

/-- **The thin regime: essentially distinct thin tubes in a bounded dilate** (blueprint
`lem:essDistinctTubesInThinDilate`).

When `ρ ≤ 1 / (4 C_n)` the count is a packing count in the `(2n-1)`-dimensional parameter space
of `Tube.parameterMap`: reorienting the family by `Tube.exists_orientedFamily`,
`Tube.axial_separation_of_essDistinct` and `Tube.lt_dist_parameterMap_of_max_lt` make the
parameters pairwise `r`-separated at the single resolution `r = c_* σ / 4 = σ / (16 n)`, they
all lie in the region `𝓑` of `Tube.volume_parameterRegion_le`, and
`Tube.card_le_of_separated_parameterSpace` together with `Metric.volume_cthickening_box_le`
(whose three side conditions hold at this `r`, which is the design reason for the axial
rescaling in `Tube.parameterMap`) turns that into the displayed bound.

This is the raw form the count produces: the third factor is the thickening loss and the fourth
is the bound on `|𝓑|`.  No simplification of the right-hand side is attempted here; absorbing it
into the selection constant is `Tube.essDistinctTubesInDilate.thin_absorbed`
(`Kakeya/Tube/Rescale.lean`), which is where that constant is defined.  The hypothesis
`ρ ≤ 1` of the ingredients is not assumed: it follows from `hρ` and `C_n > 1`. -/
theorem essDistinctTubesInThinDilate {ι : Type*} [Nontrivial E] {C : NNReal} (hC : 1 ≤ C)
    (hρ0 : 0 < ρ)
    (hρ : (ρ : ℝ) ≤ 1 / (4 * Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E)))
    (V : Tube ρ E) (a : Finset ι) (U : ι → Tube (C⁻¹ * ρ) E)
    (hUED : (↑a : Set ι).Pairwise fun i j => IsEssentiallyDistinct (U i).carrier (U j).carrier)
    (hUV : ∀ j ∈ a, (U j).carrier ⊆ (Kakeya.Tube.dilate V
      (Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E))).carrier) :
    (a.card : ENNReal)
      ≤ (Metric.coveringNumber_mul_pow_le_volume_cthickening.C
            (2 * Module.finrank ℝ E - 1) : ENNReal)⁻¹
        * (ENNReal.ofReal (1 / 4 * (1 / (4 * (Module.finrank ℝ E : ℝ)))
              * ((C : ℝ)⁻¹ * (ρ : ℝ))))⁻¹ ^ (2 * Module.finrank ℝ E - 1)
        * 2 ^ (2 * Module.finrank ℝ E - 1)
        * ENNReal.ofReal ((parameterRegion.C (Module.finrank ℝ E) : ℝ) * (C : ℝ)
            * Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E)
                ^ (2 * Module.finrank ℝ E)
            * ((C : ℝ)⁻¹ * (ρ : ℝ)) * (ρ : ℝ) ^ (2 * Module.finrank ℝ E - 2)) := by
  classical
  set n : ℕ := Module.finrank ℝ E with hndef
  set CnR := Kakeya.Tube.tubeOverlapCoreClose.C n with hCnR
  set σ : ℝ := (C : ℝ)⁻¹ * (ρ : ℝ) with hσ
  set cstar : ℝ := 1 / (4 * (n : ℝ)) with hcs
  set x : ℝ := 1 / 4 * cstar * σ with hx
  -- positivity / order lemmas
  have hnposR : 0 < (n : ℝ) := by exact_mod_cast Module.finrank_pos (R := ℝ) (M := E)
  have hn1 : 1 ≤ n := Nat.succ_le_iff.mpr (Module.finrank_pos (R := ℝ) (M := E))
  have hn1R : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hC0NN : (0 : NNReal) < C := lt_of_lt_of_le zero_lt_one hC
  have hCposR : 0 < (C : ℝ) := by exact_mod_cast hC0NN
  have hCge1R : (1 : ℝ) ≤ (C : ℝ) := by exact_mod_cast hC
  have hρposR : 0 < (ρ : ℝ) := by exact_mod_cast hρ0
  have hCn1 : 1 < CnR := by
    dsimp [CnR]
    exact_mod_cast (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C n)
  have hCnposR : 0 < CnR := lt_trans zero_lt_one hCn1
  have hCnge1R : (1 : ℝ) ≤ CnR := le_of_lt hCn1
  have hσpos : 0 < σ := by dsimp [σ]; exact mul_pos (inv_pos.mpr hCposR) hρposR
  have hcstarpos : 0 < cstar := by dsimp [cstar]; positivity
  have hcstarle4 : cstar ≤ 1 / 4 := by
    dsimp [cstar]
    field_simp [ne_of_gt hnposR]
    nlinarith
  have hxpos : 0 < x := by dsimp [x]; positivity
  have hx0 : 0 ≤ x := le_of_lt hxpos
  let r : NNReal := ⟨x, hx0⟩
  have hrℝ : (r : ℝ) = x := rfl
  have hr0 : 0 < r := by exact hxpos
  have hCinvle1NN : (C : NNReal)⁻¹ ≤ 1 := by
    exact (inv_le_one₀ (lt_of_lt_of_le zero_lt_one hC)).mpr hC
  have hCinvle1R : (C : ℝ)⁻¹ ≤ 1 := by exact_mod_cast hCinvle1NN
  have hσreal : (((C⁻¹ * ρ : NNReal) : ℝ)) = (C : ℝ)⁻¹ * (ρ : ℝ) := by
    rw [NNReal.coe_mul, NNReal.coe_inv]
  have hrEN : (r : ENNReal) = ENNReal.ofReal x := by
    rw [← hrℝ]
    exact (ENNReal.ofReal_eq_coe_nnreal (x := (r : ℝ)) (by positivity : 0 ≤ (r : ℝ))).symm
  have hρ1 : ρ ≤ 1 := by
    have hbig : (1 / (4 * (Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) : ℝ)) : ℝ) ≤ 1 := by
      rw [div_le_one (by positivity : 0 < (4 * (Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) : ℝ)))]
      nlinarith [Kakeya.Tube.tubeOverlapCoreClose.one_lt_C (Module.finrank ℝ E)]
    exact_mod_cast (hρ.trans hbig)
  -- Step 1: reorient against V.direction
  rcases exists_orientedFamily U V.direction with ⟨U', hU'⟩
  have hU'car : ∀ j, (U' j).carrier = (U j).carrier := fun j => (hU' j).1
  have hU'orient : ∀ j, 0 ≤ inner ℝ (U' j).direction V.direction := fun j => (hU' j).2
  have hUED' : (↑a : Set ι).Pairwise fun i j => IsEssentiallyDistinct (U' i).carrier (U' j).carrier := by
    intro i hi j hj hij
    rw [hU'car i, hU'car j]
    exact hUED (x := i) hi (y := j) hj hij
  have hUV' : ∀ j ∈ a,
      (U' j).carrier ⊆ (Kakeya.Tube.dilate V
        (Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E))).carrier := by
    intro j hj
    rw [hU'car j]
    exact hUV j hj
  -- Step 2: separation in parameterSpace
  have hsep : (↑a : Set ι).Pairwise (fun i j =>
      (r : ℝ) < dist (parameterMap V C (U' i)) (parameterMap V C (U' j))) := by
    intro i hi j hj hij
    have hd := axial_separation_of_essDistinct hC hρ0 hρ V (U' i) (U' j) (hUV' i hi) (hUV' j hj)
      (hU'orient i) (hU'orient j) (hUED' (x := i) hi (y := j) hj hij)
    have hxlt : x < max
          (max ‖(U' i).x - (U' j).x - inner ℝ V.direction ((U' i).x - (U' j).x) • V.direction‖
              ‖(U' i).y - (U' j).y - inner ℝ V.direction ((U' i).y - (U' j).y) • V.direction‖)
          (1 / (4 * (n : ℝ)) * ((C⁻¹ * ρ : NNReal) : ℝ) / (axialSeparation.kappa n C : ℝ)
            * |inner ℝ ((U' i).x - (U' j).x) V.direction|) := by
      rw [hσreal]
      simpa [x, σ, cstar] using hd
    exact lt_dist_parameterMap_of_max_lt (V := V) (C := C) (σ := C⁻¹ * ρ)
      (U := U' i) (U' := U' j) (by simpa [hrℝ] using hxlt)
  -- Step 3: membership and region measure
  have hGA : ∀ i ∈ a, parameterMap V C (U' i) ∈ parameterRegion V C := by
    intro i hi
    exact (volume_parameterRegion_le hC hρ0 hρ1 V).1 (U' i) (hUV' i hi)
  let boundary : ℝ := (parameterRegion.C n : ℝ) * (C : ℝ) * CnR ^ (2 * n) * σ * (ρ : ℝ) ^ (2 * n - 2)
  have hvolA : volume (parameterRegion V C) ≤ ENNReal.ofReal boundary := by
    simpa [n, CnR, σ, boundary] using (volume_parameterRegion_le hC hρ0 hρ1 V).2
  -- Step 5: the thickening
  let κ : ℝ := (axialSeparation.kappa n C : ℝ)
  let h0 : ℝ := 3 * (1 / (4 * (n : ℝ))) * σ * CnR / (2 * κ)
  let h1 : ℝ := CnR * (ρ : ℝ)
  have hκval : κ = 1 / (32 * (n : ℝ) * (C : ℝ) * (Kakeya.Tube.tubeOverlapCoreClose.C n : ℝ)) := by
    dsimp [κ, axialSeparation.kappa]
    have hmax : max (Kakeya.Tube.tubeOverlapCoreClose.C n) 0 = Kakeya.Tube.tubeOverlapCoreClose.C n := by
      rw [max_eq_left (le_trans zero_le_one (le_of_lt (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C n)))]
    simp [hmax]
  have h0_form : h0 = 12 * (C : ℝ) * CnR ^ 2 * σ := by
    dsimp [h0, σ, cstar]
    rw [hκval]
    field_simp [ne_of_gt hnposR, hCposR.ne', ne_of_gt hCnposR]
    ring
  have hs0 : (r : ℝ) ≤ h0 := by
    dsimp [r]
    rw [h0_form]
    dsimp [x]
    have hcstar_le_big : 1 / 4 * cstar ≤ 12 * (C : ℝ) * CnR ^ 2 := by
      nlinarith [hcstarle4, hCge1R, hCnge1R, hcstarpos]
    nlinarith [hcstar_le_big, hσpos]
  have hxleσ : x ≤ σ := by
    dsimp [x]
    nlinarith [hcstarle4, hcstarpos, hσpos]
  have hσleρ : σ ≤ (ρ : ℝ) := by
    dsimp [σ]
    nlinarith [hCinvle1R, hρposR]
  have hρleCnRρ : (ρ : ℝ) ≤ CnR * (ρ : ℝ) := by
    nlinarith [hCnge1R, hρposR]
  have hs1 : (r : ℝ) ≤ CnR * (ρ : ℝ) := by
    rw [hrℝ]
    exact le_trans hxleσ (le_trans hσleρ hρleCnRρ)
  have hs_gt0 : 0 < (r : ℝ) := by
    rw [hrℝ]
    exact hxpos
  have hbox := (Metric.volume_cthickening_box_le (F₁ := perpSpace V) (F₂ := perpSpace V)
      (h₀ := h0) (h₁ := h1) (h₂ := h1) (s := (r : ℝ)) hs_gt0 hs0 hs1 hs1).2
  have hbox' : volume (cthickening (r : ℝ) (parameterRegion V C))
        ≤ 2 ^ (1 + Module.finrank ℝ (perpSpace V) + Module.finrank ℝ (perpSpace V))
            * volume (parameterRegion V C) := by
    simpa [parameterRegion, n, CnR, σ, κ, h0, h1] using hbox
  have hfinp : Module.finrank ℝ (perpSpace V) = n - 1 := by
    simpa [← hndef] using Tube.finrank_perpSpace V
  have hfin1 : 1 + (n - 1) + (n - 1) = 2 * n - 1 := by omega
  have hcthick_bound : volume (cthickening (r : ℝ) (parameterRegion V C))
        ≤ 2 ^ (2 * n - 1) * volume (parameterRegion V C) := by
    simpa [hfin1, hfinp, n] using hbox'
  have hbigvol : volume (cthickening (r : ℝ) (parameterRegion V C))
        ≤ 2 ^ (2 * n - 1) * ENNReal.ofReal boundary := by
    calc
      volume (cthickening (r : ℝ) (parameterRegion V C))
          ≤ 2 ^ (2 * n - 1) * volume (parameterRegion V C) := hcthick_bound
      _ ≤ 2 ^ (2 * n - 1) * ENNReal.ofReal boundary := by
            exact mul_le_mul_of_nonneg_left hvolA (by positivity)
  -- Step 4: the count
  have dfin : Module.finrank ℝ (parameterSpace V) = 2 * n - 1 := by
    simpa [← hndef] using Tube.finrank_parameterSpace V
  have hcard := card_le_of_separated_parameterSpace
      (F := parameterSpace V) (G := a) (Ψ := fun i => parameterMap V C (U' i))
      (A := parameterRegion V C) (r := r) hr0 hGA hsep
  calc
    (a.card : ENNReal)
        ≤ (Metric.coveringNumber_mul_pow_le_volume_cthickening.C (Module.finrank ℝ (parameterSpace V)) : ENNReal)⁻¹
            * (r : ENNReal)⁻¹ ^ Module.finrank ℝ (parameterSpace V) * volume (cthickening (r : ℝ) (parameterRegion V C)) := hcard
    _ = (Metric.coveringNumber_mul_pow_le_volume_cthickening.C (2 * n - 1) : ENNReal)⁻¹
            * (r : ENNReal)⁻¹ ^ (2 * n - 1) * volume (cthickening (r : ℝ) (parameterRegion V C)) := by
          rw [dfin]
    _ = (Metric.coveringNumber_mul_pow_le_volume_cthickening.C (2 * n - 1) : ENNReal)⁻¹
            * (ENNReal.ofReal x)⁻¹ ^ (2 * n - 1) * volume (cthickening (r : ℝ) (parameterRegion V C)) := by
          rw [hrEN]
    _ ≤ (Metric.coveringNumber_mul_pow_le_volume_cthickening.C (2 * n - 1) : ENNReal)⁻¹
            * (ENNReal.ofReal x)⁻¹ ^ (2 * n - 1) * (2 ^ (2 * n - 1) * ENNReal.ofReal boundary) := by
          exact mul_le_mul_of_nonneg_left hbigvol (by positivity)
    _ = (Metric.coveringNumber_mul_pow_le_volume_cthickening.C (2 * Module.finrank ℝ E - 1) : ENNReal)⁻¹
            * (ENNReal.ofReal (1 / 4 * (1 / (4 * (Module.finrank ℝ E : ℝ)))
                  * ((C : ℝ)⁻¹ * (ρ : ℝ))))⁻¹ ^ (2 * Module.finrank ℝ E - 1)
            * 2 ^ (2 * Module.finrank ℝ E - 1)
            * ENNReal.ofReal ((parameterRegion.C (Module.finrank ℝ E) : ℝ) * (C : ℝ)
                * Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E)
                    ^ (2 * Module.finrank ℝ E)
                * ((C : ℝ)⁻¹ * (ρ : ℝ)) * (ρ : ℝ) ^ (2 * Module.finrank ℝ E - 2)) := by
          simp only [x, cstar, σ, CnR, boundary]
          rw [hndef]
          ac_rfl

/-! ### The fat regime -/

/-- **The fat regime: essentially distinct thin tubes in a bounded dilate** (blueprint
`lem:essDistinctTubesInFatDilate`).

When `ρ > 1 / (4 C_n)` the dilate `C_n · V` is comparable to a ball of radius `3 C_n / 2` while
the tube scale `σ = C⁻¹ρ` is bounded below by `C⁻¹ / (4 C_n)`, so the crude ball count
`Tube.card_le_of_EssDistinct` already gives a bound depending only on `n`, `C` and `C_n`.
Blueprint `note:essDistinctTubesInDilateRegimes` explains why the count splits here. -/
theorem essDistinctTubesInFatDilate {ι : Type*} [Nontrivial E] {C : NNReal} (hC : 1 ≤ C)
    (hρ : 1 / (4 * Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E)) < (ρ : ℝ))
    (hρ1 : ρ ≤ 1) (V : Tube ρ E) (a : Finset ι) (U : ι → Tube (C⁻¹ * ρ) E)
    (hUED : (↑a : Set ι).Pairwise fun i j => IsEssentiallyDistinct (U i).carrier (U j).carrier)
    (hUV : ∀ j ∈ a, (U j).carrier ⊆ (Kakeya.Tube.dilate V
      (Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E))).carrier) :
    (a.card : ℝ) ≤ card_le_of_EssDistinct.C (Module.finrank ℝ E)
      * (6 * (C : ℝ) * Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) ^ 2)
        ^ (2 * Module.finrank ℝ E) := by
  classical
  set n : ℕ := Module.finrank ℝ E
  set Cn : ℝ := Kakeya.Tube.tubeOverlapCoreClose.C n
  -- positivity of the constants
  have hCn0 : 0 < Cn := by
    dsimp [Cn]
    exact lt_trans zero_lt_one (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C n)
  have hfour : (0 : ℝ) < 4 * Cn := mul_pos (by norm_num) hCn0
  have hρ0R : 0 < (ρ : ℝ) := by
    have hpos : (0 : ℝ) < 1 / (4 * Cn) := one_div_pos.mpr hfour
    linarith
  have hρ0 : 0 < ρ := NNReal.coe_pos.mp hρ0R
  have hC0 : (0 : NNReal) < C := lt_of_lt_of_le zero_lt_one hC
  have hCposR : 0 < (C : ℝ) := by exact_mod_cast hC0
  have hδ : 0 < C⁻¹ * ρ := mul_pos (inv_pos.mpr hC0) hρ0
  have hσR0 : 0 < ((C⁻¹ * ρ : NNReal) : ℝ) := NNReal.coe_pos.mpr hδ
  have hσR : ((C⁻¹ * ρ : NNReal) : ℝ) = (C : ℝ)⁻¹ * (ρ : ℝ) := by
    rw [NNReal.coe_mul, NNReal.coe_inv]
  -- the dilate `Cn · V` sits inside the ball of radius `3 Cn / 2` about `V.center`
  have hseg_ball :
      segment ℝ (V.center - (Cn / 2) • V.direction) (V.center + (Cn / 2) • V.direction)
        ⊆ closedBall V.center (Cn / 2) := by
    refine (convex_closedBall V.center (Cn / 2)).segment_subset ?_ ?_
    · rw [Metric.mem_closedBall, dist_eq_norm]
      calc
        ‖(V.center - (Cn / 2) • V.direction) - V.center‖
            = ‖(Cn / 2) • V.direction‖ := by
              rw [← norm_neg]
              congr 1
              module
        _ = Cn / 2 := by
          rw [norm_smul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ Cn / 2),
              V.norm_direction, mul_one]
        _ ≤ Cn / 2 := le_rfl
    · rw [Metric.mem_closedBall, dist_eq_norm]
      calc
        ‖(V.center + (Cn / 2) • V.direction) - V.center‖
            = ‖(Cn / 2) • V.direction‖ := by
              congr 1
              module
        _ = Cn / 2 := by
          rw [norm_smul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ Cn / 2),
              V.norm_direction, mul_one]
        _ ≤ Cn / 2 := le_rfl
  have hct_sub :
      cthickening (Cn * (ρ : ℝ))
          (segment ℝ (V.center - (Cn / 2) • V.direction) (V.center + (Cn / 2) • V.direction))
        ⊆ closedBall V.center (Cn / 2 + Cn * (ρ : ℝ)) := by
    intro z hz
    rw [isCompact_segment.cthickening_eq_biUnion_closedBall
        (by positivity : (0 : ℝ) ≤ Cn * (ρ : ℝ))] at hz
    rw [Set.mem_iUnion₂] at hz
    obtain ⟨w, hwseg, hwz⟩ := hz
    rw [Metric.mem_closedBall] at hwz ⊢
    calc
      dist z V.center ≤ dist z w + dist w V.center := dist_triangle z w V.center
      _ ≤ Cn * (ρ : ℝ) + Cn / 2 := by
        exact add_le_add hwz (by
          have := hseg_ball hwseg
          rwa [Metric.mem_closedBall] at this)
      _ = Cn / 2 + Cn * (ρ : ℝ) := by ring
  have hdilate_ball : (Kakeya.Tube.dilate V Cn).carrier ⊆ closedBall V.center (3 * Cn / 2) := by
    rw [dilate_carrier_eq_cthickening V hCn0]
    refine hct_sub.trans ?_
    apply Metric.closedBall_subset_closedBall
    have hρR1 : (ρ : ℝ) ≤ 1 := by exact_mod_cast hρ1
    have hCnρ : Cn * (ρ : ℝ) ≤ Cn := mul_le_of_le_one_right hCn0.le hρR1
    nlinarith
  -- translate by `-V.center`: essential distinctness and the ball are preserved
  have hU'ball : ∀ i ∈ a, ((U i).vadd (-V.center)).carrier ⊆ closedBall (0 : E) (3 * Cn / 2) := by
    intro i hi z hz
    rw [Tube.vadd_carrier] at hz
    rcases hz with ⟨x, hx, rfl⟩
    have hx_mem : x ∈ closedBall V.center (3 * Cn / 2) := hdilate_ball (hUV i hi hx)
    rw [Metric.mem_closedBall] at hx_mem
    rw [Metric.mem_closedBall]
    rw [dist_comm]
    change dist 0 (-V.center +ᵥ x) ≤ 3 * Cn / 2
    rw [vadd_eq_add]
    calc
      dist 0 (-V.center + x) = ‖V.center - x‖ := by
        rw [dist_eq_norm]
        congr 1
        abel
      _ = dist x V.center := by
        rw [dist_eq_norm]
        rw [← norm_neg]
        congr 1
        abel
      _ ≤ 3 * Cn / 2 := hx_mem
  have hU'ED : (↑a : Set ι).Pairwise
      (fun i j => IsEssentiallyDistinct ((U i).vadd (-V.center)).carrier
        ((U j).vadd (-V.center)).carrier) := by
    intro i hi j hj hij
    rw [Tube.vadd_carrier]
    change IsEssentiallyDistinct ((fun x : E => -V.center +ᵥ x) '' (U i).carrier)
        ((fun x : E => -V.center +ᵥ x) '' (U j).carrier)
    simp only [vadd_eq_add]
    exact (Kakeya.isEssentiallyDistinct_translate (U i).carrier (U j).carrier (-V.center)).mpr
      (hUED hi hj hij)
  -- scale comparison: `r / σ ≤ 6 C Cn²`
  have hratio : (3 * Cn / 2) / ((C⁻¹ * ρ : NNReal) : ℝ) ≤ 6 * (C : ℝ) * Cn ^ 2 := by
    rw [hσR]
    have hden0 : 0 < (C : ℝ)⁻¹ * (ρ : ℝ) := mul_pos (inv_pos.mpr hCposR) hρ0R
    rw [div_le_iff₀ hden0]
    have hmul : 6 * Cn ^ 2 * (1 / (4 * Cn)) < 6 * Cn ^ 2 * (ρ : ℝ) :=
      mul_lt_mul_of_pos_left hρ (by positivity : (0 : ℝ) < 6 * Cn ^ 2)
    have hrho_ge : (3 * Cn / 2) ≤ 6 * Cn ^ 2 * (ρ : ℝ) := by
      have hcalc : 6 * Cn ^ 2 * (1 / (4 * Cn)) = 3 * Cn / 2 := by
        field_simp [hCn0.ne']
        ring
      linarith
    calc
      3 * Cn / 2 ≤ 6 * Cn ^ 2 * (ρ : ℝ) := hrho_ge
      _ = 6 * (C : ℝ) * Cn ^ 2 * ((C : ℝ)⁻¹ * (ρ : ℝ)) := by
        calc
          6 * Cn ^ 2 * (ρ : ℝ)
              = 6 * Cn ^ 2 * ((C : ℝ) * (C : ℝ)⁻¹) * (ρ : ℝ) := by
                rw [mul_inv_cancel₀ hCposR.ne']
                ring
          _ = 6 * (C : ℝ) * Cn ^ 2 * ((C : ℝ)⁻¹ * (ρ : ℝ)) := by
                ring
  -- assemble
  have hcard := Tube.card_le_of_EssDistinct (E := E) (δ := C⁻¹ * ρ) hδ (3 * Cn / 2) a
      (fun i => (U i).vadd (-V.center)) hU'ball hU'ED
  calc
    (a.card : ℝ)
        ≤ card_le_of_EssDistinct.C n
            * (((3 * Cn / 2) / ((C⁻¹ * ρ : NNReal) : ℝ)) ^ (2 * n)) := hcard
    _ ≤ card_le_of_EssDistinct.C n * ((6 * (C : ℝ) * Cn ^ 2) ^ (2 * n)) := by
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (div_nonneg (by positivity : (0 : ℝ) ≤ 3 * Cn / 2) hσR0.le)
          hratio (2 * n))
        (le_of_lt card_le_of_EssDistinct.C_pos)

end Tube

/-! ### The tube-level core of the plank case of the enlargement lemma

The seven statements below are the tube- and vector-level content of the *plank* half of GWZ's
Lemma 3.1, in the only shape that can be true in the conventions of this development: a
containment in `8 · (T₀^{(3δ)})`, a **homothety** of a **concentric rescaling**, and not in any
concentric rescaling `T₀^{(r)}` with `r = O(δ)`.  Blueprint
`note:ml1bootEnlargementTubeStatus` records the retraction of the concentric-rescaling form and
`def:ml1bootEnlargementPlankConstant` fixes the two constants `Λ = 8` and `C = 3`.

Unlike the rest of the file these live in `Kakeya.Tube` — beside `Kakeya.Tube.dilate`, which
they are all about — and their two vector-level members in `Kakeya`, so `dilate` needs no
qualification here.  The correspondence is listed again in the module docstring.

The plank-level consequence lives in `Kakeya/DimensionThree/MainLemma1/PlankEnlargement.lean`,
being the only one of the group that mentions a dimension and a thickness. -/

namespace Kakeya

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Pythagoras for the transverse part along a unit vector** (blueprint
`lem:unitVectorTiltPythagoras`).

For a unit vector `e` and any `z`, the orthogonal decomposition of `z` along `e` is a
Pythagorean one:
`⟪e, z⟫² + ‖z - ⟪e, z⟫ • e‖² = ‖z‖²`.

Both summands on the left are nonnegative, so this single identity delivers the three
consequences the group uses — `|⟪e, z⟫| ≤ ‖z‖`, `‖z - ⟪e, z⟫ • e‖ ≤ ‖z‖`, and, at `‖z‖ = 1`,
the linearization `1 - |⟪e, z⟫| ≤ (1 - |⟪e, z⟫|)(1 + |⟪e, z⟫|) = ‖z - ⟪e, z⟫ • e‖²`.  The
blueprint displays those consequences alongside the identity; they are not separate
declarations here because each is a one-step arithmetic rearrangement of it, and the linearity
of `z ↦ z - ⟪e, z⟫ • e` together with the vanishing at `e` that the blueprint also records are
supplied directly by `inner_add_right`, `real_inner_smul_right` and
`real_inner_self_eq_norm_sq`.

The unit vector is the *first* argument of `inner`, as it is in the transverse components
`d - inner ℝ T.direction d • T.direction` of the rest of this file and in
`InnerProductGeometry.norm_sub_inner_smul_eq_sin_angle`, so that no consumer has to insert a
`real_inner_comm`.

It is stated at a general `z` and not only at a unit one: the transverse estimate of
`Kakeya.Tube.norm_chord_transverse_le_of_endpoints_mem_dilate` applies it at a vector of
arbitrary norm. -/
theorem inner_sq_add_norm_transverse_sq_eq {e : E} (he : ‖e‖ = 1) (z : E) :
    inner ℝ e z ^ 2 + ‖z - inner ℝ e z • e‖ ^ 2 = ‖z‖ ^ 2 := by
  rw [norm_sub_sq_real]
  simp [he, norm_smul, inner_smul_right, real_inner_comm]
  ring

/-- **Displacement across a sign-corrected nearly-parallel direction** (blueprint
`lem:ml1bootSignedDisplacement`).

For unit vectors `e` and `f`, put `α = ⟪e, f⟫` and `w = f - α • e`.  A displacement `τ • e + g`
along `e` can be re-expressed along the *nearly parallel* direction `f` at the same
longitudinal parameter up to sign: there is `r` with `|r| = |τ|` and
`‖τ • e + g - r • f‖ ≤ |τ| (1 - |α|) + |τ| ‖w‖ + ‖g‖`.

This is the arithmetic core of `Kakeya.Tube.subset_dilate_rescale_of_subset_dilate` with
the tubes removed.  The blueprint fixes `r` explicitly, as `τ` when `α ≥ 0` and `-τ`
otherwise; it is existentially quantified here because the sign correction exists only to make
the estimate insensitive to the orientation of `f`, and the consumer uses nothing about `r`
beyond `|r| = |τ|`.  Nothing here mentions tubes, scales or a dimension, and no nonnegativity
is assumed of `τ`.

As in `Kakeya.inner_sq_add_norm_transverse_sq_eq`, the vector along which the transverse part
is taken is the first argument of `inner`. -/
theorem norm_smul_add_sub_smul_le {e f : E} (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (τ : ℝ) (g : E) :
    ∃ r : ℝ, |r| = |τ| ∧
      ‖τ • e + g - r • f‖
        ≤ |τ| * (1 - |inner ℝ e f|) + |τ| * ‖f - inner ℝ e f • e‖ + ‖g‖ := by
  set α : ℝ := inner ℝ e f with hα_def
  set w : E := f - α • e with hw_def
  have hf' : f = α • e + w := by
    rw [hw_def]
    abel
  have hαabs : |α| ≤ 1 := by
    rw [hα_def]
    calc
      |inner ℝ e f| ≤ ‖e‖ * ‖f‖ := abs_real_inner_le_norm e f
      _ = 1 := by rw [he, hf]; norm_num
  by_cases hαge : 0 ≤ α
  · -- case α ≥ 0 : take r := τ
    refine ⟨τ, ?hr, ?hbd⟩
    · rfl
    · have hαle1 : α ≤ 1 := by
        rw [abs_of_nonneg hαge] at hαabs
        exact hαabs
      have hnonneg : 0 ≤ 1 - α := by linarith
      have hid : τ • e + g - τ • f = (τ * (1 - α)) • e + (-τ) • w + g := by
        rw [hf']
        module
      have hnorm1 : ‖(τ * (1 - α)) • e‖ = |τ| * (1 - |α|) := by
        calc
          ‖(τ * (1 - α)) • e‖ = ‖τ * (1 - α)‖ * ‖e‖ := by rw [norm_smul]
          _ = ‖τ * (1 - α)‖ := by rw [he, mul_one]
          _ = |τ * (1 - α)| := by rw [Real.norm_eq_abs]
          _ = |τ| * |1 - α| := abs_mul τ (1 - α)
          _ = |τ| * (1 - α) := by rw [abs_of_nonneg hnonneg]
          _ = |τ| * (1 - |α|) := by rw [abs_of_nonneg hαge]
      have hnorm2 : ‖(-τ) • w‖ = |τ| * ‖w‖ := by
        calc
          ‖(-τ) • w‖ = ‖(-τ)‖ * ‖w‖ := by rw [norm_smul]
          _ = |(-τ)| * ‖w‖ := by rw [Real.norm_eq_abs]
          _ = |τ| * ‖w‖ := by rw [abs_neg]
      rw [hid]
      calc
        ‖(τ * (1 - α)) • e + (-τ) • w + g‖
            ≤ ‖(τ * (1 - α)) • e‖ + ‖(-τ) • w‖ + ‖g‖ :=
              norm_add₃_le (a := (τ * (1 - α)) • e) (b := (-τ) • w) (c := g)
        _ = |τ| * (1 - |α|) + |τ| * ‖w‖ + ‖g‖ := by rw [hnorm1, hnorm2]
  · -- case α < 0 : take r := -τ
    have hαlt : α < 0 := lt_of_not_ge hαge
    have hα_ge_neg1 : -1 ≤ α := by
      calc
        -1 ≤ -|α| := by linarith [hαabs]
        _ ≤ α := neg_abs_le α
    have hone : 0 ≤ 1 + α := by linarith
    have hαm : |α| = -α := abs_of_neg hαlt
    refine ⟨-τ, ?hrqr, ?hbd2⟩
    · exact abs_neg τ
    · have hid : τ • e + g - (-τ) • f = (τ * (1 + α)) • e + τ • w + g := by
        rw [hf']
        module
      have hnorm1 : ‖(τ * (1 + α)) • e‖ = |τ| * (1 - |α|) := by
        calc
          ‖(τ * (1 + α)) • e‖ = ‖τ * (1 + α)‖ * ‖e‖ := by rw [norm_smul]
          _ = ‖τ * (1 + α)‖ := by rw [he, mul_one]
          _ = |τ * (1 + α)| := by rw [Real.norm_eq_abs]
          _ = |τ| * |1 + α| := abs_mul τ (1 + α)
          _ = |τ| * (1 + α) := by rw [abs_of_nonneg hone]
          _ = |τ| * (1 - |α|) := by
            congr 1
            rw [hαm]
            ring
      have hnorm2 : ‖τ • w‖ = |τ| * ‖w‖ := by
        calc
          ‖τ • w‖ = ‖τ‖ * ‖w‖ := by rw [norm_smul]
          _ = |τ| * ‖w‖ := by rw [Real.norm_eq_abs]
      rw [hid]
      calc
        ‖(τ * (1 + α)) • e + τ • w + g‖
            ≤ ‖(τ * (1 + α)) • e‖ + ‖τ • w‖ + ‖g‖ :=
              norm_add₃_le (a := (τ * (1 + α)) • e) (b := τ • w) (c := g)
        _ = |τ| * (1 - |α|) + |τ| * ‖w‖ + ‖g‖ := by rw [hnorm1, hnorm2]

namespace Tube

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **Axis representation of a point of a dilate** (blueprint `lem:ml1bootDilateAxisRepr`).

A point `z` of the homothety `c · T` of a `δ`-tube `T` is `c δ`-close to an explicit point
`T.center + s • T.direction` of the axis of `T` whose longitudinal parameter is confined to
`[-c/2, c/2]`.

This is the converse of `Tube.mem_dilate_of_dist_axis_le`, and it is sharper than
`Tube.abs_inner_and_perp_le_of_mem_dilate`, which resolves `z - T.center` into its axial and
transverse components and so pays `c / 2 + c δ` on the axial one.  Here the two errors are not
mixed: the longitudinal parameter is bounded by `c / 2` on the nose and the *whole* remaining
displacement, not merely its transverse part, by `c δ`.  That unmixed form is what
`Kakeya.Tube.exists_axis_repr_sub_midpoint_of_mem_dilate` needs, three displacements being
added there.  No positivity on `δ` is assumed. -/
theorem exists_axis_repr_of_mem_dilate {δ : NNReal} (T : Tube δ E) {c : ℝ} (hc : 0 < c)
    {z : E} (hz : z ∈ (dilate T c).carrier) :
    ∃ s : ℝ, |s| ≤ c / 2 ∧ ‖z - (T.center + s • T.direction)‖ ≤ c * (δ : ℝ) := by
  have hcnonneg : 0 ≤ c := le_of_lt hc
  have hδ0 : 0 ≤ (δ : ℝ) := NNReal.coe_nonneg δ
  have hcr : 0 ≤ c * (δ : ℝ) := mul_nonneg hcnonneg hδ0
  have hz' : z ∈ cthickening (c * (δ : ℝ))
      (segment ℝ (T.center - (c / 2) • T.direction) (T.center + (c / 2) • T.direction)) := by
    rw [_root_.Tube.dilate_carrier_eq_cthickening T hc] at hz
    exact hz
  have hz'' : z ∈ ⋃ x ∈ segment ℝ (T.center - (c / 2) • T.direction)
      (T.center + (c / 2) • T.direction), closedBall x (c * (δ : ℝ)) := by
    rwa [← isClosed_segment.cthickening_eq_biUnion_closedBall hcr]
  rw [Set.mem_iUnion₂] at hz''
  rcases hz'' with ⟨w, hw, hzw⟩
  rw [Metric.mem_closedBall] at hzw
  rcases (segment_eq_image_lineMap ℝ (T.center - (c / 2) • T.direction)
      (T.center + (c / 2) • T.direction)).symm ▸ hw with ⟨s, hs, hw_eq⟩
  let t : ℝ := (2 * s - 1) * (c / 2)
  have hw_eq' : w = T.center + t • T.direction := by
    rw [← hw_eq]
    rw [AffineMap.lineMap_apply_module]
    dsimp [t]
    module
  have hs0 : 0 ≤ s := hs.1
  have hs1 : s ≤ 1 := hs.2
  have h2s : -1 ≤ 2 * s - 1 ∧ 2 * s - 1 ≤ 1 := by
    constructor <;> linarith
  have hc2 : 0 ≤ c / 2 := by positivity
  have ht : |t| ≤ c / 2 := by
    dsimp [t]
    calc
      |(2 * s - 1) * (c / 2)| = |2 * s - 1| * |c / 2| := abs_mul _ _
      _ = |2 * s - 1| * (c / 2) := by rw [abs_of_nonneg hc2]
      _ ≤ 1 * (c / 2) := mul_le_mul_of_nonneg_right (abs_le.mpr h2s) hc2
      _ = c / 2 := by ring
  have htbound : ‖z - (T.center + t • T.direction)‖ ≤ c * (δ : ℝ) := by
    rw [← hw_eq']
    have hnorm : ‖z - w‖ ≤ c * (δ : ℝ) := by
      simpa [dist_eq_norm] using hzw
    exact hnorm
  exact ⟨t, ht, htbound⟩

/-- **Axis representation relative to the midpoint of two points of a dilate** (blueprint
`lem:ml1bootCentreRelativeAxisRepr`).

For `p`, `q`, `z` all in the homothety `c · T` of a `δ`-tube `T`, the displacement of `z` from
the midpoint `m₁` of `p` and `q` splits as `τ • T.direction + g` with `|τ| ≤ c` and
`‖g‖ ≤ 2 c δ`.

The centre of `T` does not appear: it cancels between `z` and `m₁`, which is the whole point of
measuring from the midpoint rather than from the axis.  In the application `p`, `q` are the
endpoints of the core of a unit-length tube inscribed in `c · T`, so `m₁` is that tube's
centre.  Both constants are twice those of `Kakeya.Tube.exists_axis_repr_of_mem_dilate`, the
doubling being the single subtraction of two axis representations and nothing more.  No
positivity on `δ` is assumed. -/
theorem exists_axis_repr_sub_midpoint_of_mem_dilate {δ : NNReal} (T : Tube δ E) {c : ℝ}
    (hc : 0 < c) {p q z : E}
    (hp : p ∈ (dilate T c).carrier)
    (hq : q ∈ (dilate T c).carrier)
    (hz : z ∈ (dilate T c).carrier) :
    ∃ (τ : ℝ) (g : E), z - midpoint ℝ p q = τ • T.direction + g ∧
      |τ| ≤ c ∧ ‖g‖ ≤ 2 * c * (δ : ℝ) := by
  obtain ⟨s₀, hs₀, hu⟩ := exists_axis_repr_of_mem_dilate T hc hp
  obtain ⟨s₁, hs₁, hv⟩ := exists_axis_repr_of_mem_dilate T hc hq
  obtain ⟨t, ht, hξ⟩ := exists_axis_repr_of_mem_dilate T hc hz
  set u : E := p - (T.center + s₀ • T.direction) with hudef
  set v : E := q - (T.center + s₁ • T.direction) with hvdef
  set ξ : E := z - (T.center + t • T.direction) with hξdef
  have hu' : ‖u‖ ≤ c * (δ : ℝ) := by simpa [u] using hu
  have hv' : ‖v‖ ≤ c * (δ : ℝ) := by simpa [v] using hv
  have hξ' : ‖ξ‖ ≤ c * (δ : ℝ) := by simpa [ξ] using hξ
  refine ⟨t - (s₀ + s₁) / 2, ξ - (2 : ℝ)⁻¹ • (u + v), ?_, ?_, ?_⟩
  · have hp' : p = T.center + s₀ • T.direction + u := by
      rw [hudef]
      abel
    have hq' : q = T.center + s₁ • T.direction + v := by
      rw [hvdef]
      abel
    have hz' : z = T.center + t • T.direction + ξ := by
      rw [hξdef]
      abel
    calc
      z - midpoint ℝ p q
          = (T.center + t • T.direction + ξ) - (2 : ℝ)⁻¹ • (p + q) := by
            rw [← hz']
            rw [midpoint_eq_smul_add, invOf_eq_inv]
      _ = (t - (s₀ + s₁) / 2) • T.direction + (ξ - (2 : ℝ)⁻¹ • (u + v)) := by
            rw [hp', hq']
            module
  · rw [abs_le] at hs₀ hs₁ ht ⊢
    constructor <;> linarith
  · have hsmul : ‖(2 : ℝ)⁻¹ • (u + v)‖ ≤ (2 : ℝ)⁻¹ * (‖u‖ + ‖v‖) := by
      rw [norm_smul]
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 : ℝ)⁻¹)]
      exact mul_le_mul_of_nonneg_left (norm_add_le u v) (by positivity : (0 : ℝ) ≤ (2 : ℝ)⁻¹)
    calc
      ‖ξ - (2 : ℝ)⁻¹ • (u + v)‖ ≤ ‖ξ‖ + ‖(2 : ℝ)⁻¹ • (u + v)‖ := norm_sub_le ξ _
      _ ≤ ‖ξ‖ + (2 : ℝ)⁻¹ * (‖u‖ + ‖v‖) := add_le_add le_rfl hsmul
      _ ≤ c * (δ : ℝ) + (2 : ℝ)⁻¹ * (c * (δ : ℝ) + c * (δ : ℝ)) := by
            exact add_le_add hξ'
              (mul_le_mul_of_nonneg_left (add_le_add hu' hv') (by positivity : (0 : ℝ) ≤ (2 : ℝ)⁻¹))
      _ ≤ 2 * c * (δ : ℝ) := by
            nlinarith [hc, NNReal.coe_nonneg δ]

/-- **A unit chord of a dilate is nearly parallel to its axis: the transverse bound**
(blueprint `lem:ml1bootUnitChordTilt`, first conclusion).

If `x` and `y` lie in the homothety `c · T` of a `δ`-tube `T` and `dist x y = 1`, then the unit
vector `f = y - x` has transverse part of norm at most `2 c δ` with respect to the axis
`e = T.direction`: writing `α = ⟪e, f⟫`, one has `‖f - α • e‖ ≤ 2 c δ`.

In the application `x`, `y` are the endpoints of the core of a unit-length tube contained in
`c · T` — `dist x y = 1` being then exactly `Tube.dist_eq_one` — so `f` is a unit direction of
that tube and the bound says it is tilted away from the axis of `T` by an angle of at most
`arcsin (2 c δ)`.

The blueprint states this jointly with
`Kakeya.Tube.one_sub_abs_inner_chord_le_of_endpoints_mem_dilate`; the two halves are separate
declarations here because the second is deduced from the first and each is used on its own.
The bound is unconditional: where the right-hand side exceeds `1` the left-hand side is
trivially below it, `f` being a unit vector.  The length hypothesis is not consumed by this
half — the estimate holds for any two points of `c · T` — and is kept only so that the pair is
a faithful split of the blueprint lemma. -/
theorem norm_chord_transverse_le_of_endpoints_mem_dilate {δ : NNReal} (T : Tube δ E) {c : ℝ}
    (hc : 0 < c) {x y : E} (_hxy : dist x y = 1)
    (hx : x ∈ (dilate T c).carrier) (hy : y ∈ (dilate T c).carrier) :
    ‖(y - x) - inner ℝ T.direction (y - x) • T.direction‖ ≤ 2 * c * (δ : ℝ) := by
  let e : E := T.direction
  have he : ‖e‖ = 1 := by
    dsimp [e]
    exact T.norm_direction
  have hnorm_pi : ∀ z : E, ‖z - inner ℝ e z • e‖ ≤ ‖z‖ := by
    intro z
    have hmain := Kakeya.inner_sq_add_norm_transverse_sq_eq he z
    have hsq : ‖z - inner ℝ e z • e‖ ^ 2 ≤ ‖z‖ ^ 2 := by
      nlinarith [hmain, sq_nonneg (inner ℝ e z)]
    have h := sq_le_sq.mp hsq
    simpa using h
  have hpi_add : ∀ a b : E, (a + b) - inner ℝ e (a + b) • e
      = (a - inner ℝ e a • e) + (b - inner ℝ e b • e) := by
    intro a b
    rw [inner_add_right]
    module
  have hpi_k : ∀ t : ℝ, (t • e) - inner ℝ e (t • e) • e = 0 := by
    intro t
    rw [real_inner_smul_right]
    rw [real_inner_self_eq_norm_sq, he]
    norm_num
  obtain ⟨s0, hs0, hxu⟩ := exists_axis_repr_of_mem_dilate T hc hx
  obtain ⟨s1, hs1, hyav⟩ := exists_axis_repr_of_mem_dilate T hc hy
  let u : E := x - (T.center + s0 • e)
  let v : E := y - (T.center + s1 • e)
  have hu : ‖u‖ ≤ c * (δ : ℝ) := by
    dsimp [u]
    simpa [e] using hxu
  have hv : ‖v‖ ≤ c * (δ : ℝ) := by
    dsimp [v]
    simpa [e] using hyav
  have hurep : x = T.center + s0 • e + u := by
    dsimp [u]
    abel
  have hvrep : y = T.center + s1 • e + v := by
    dsimp [v]
    abel
  have hdiff : y - x = (s1 - s0) • e + (v - u) := by
    rw [hvrep, hurep]
    module
  have hEq : (y - x) - inner ℝ e (y - x) • e = (v - u) - inner ℝ e (v - u) • e := by
    rw [hdiff]
    rw [hpi_add ((s1 - s0) • e) (v - u)]
    rw [hpi_k (s1 - s0)]
    simp
  change ‖(y - x) - inner ℝ e (y - x) • e‖ ≤ 2 * c * (δ : ℝ)
  calc
    ‖(y - x) - inner ℝ e (y - x) • e‖ = ‖(v - u) - inner ℝ e (v - u) • e‖ := by rw [hEq]
    _ ≤ ‖v - u‖ := hnorm_pi (v - u)
    _ ≤ ‖v‖ + ‖u‖ := norm_sub_le v u
    _ ≤ c * (δ : ℝ) + c * (δ : ℝ) := add_le_add hv hu
    _ = 2 * c * (δ : ℝ) := by ring

/-- **A unit chord of a dilate is nearly parallel to its axis: the quadratic defect bound**
(blueprint `lem:ml1bootUnitChordTilt`, second conclusion).

In the situation of `Kakeya.Tube.norm_chord_transverse_le_of_endpoints_mem_dilate`, the
alignment defect of the unit chord `f = y - x` against the axis `e = T.direction` is
*quadratic* in `δ`: writing `α = ⟪e, f⟫`, one has `1 - |α| ≤ 4 c² δ²`.

This is the transverse bound of that lemma fed through the unit-vector clause of
`Kakeya.inner_sq_add_norm_transverse_sq_eq`, which turns `1 - |α| ≤ ‖f - α • e‖²` into the
displayed estimate; the length hypothesis is what makes `f` a unit vector and so is genuinely
consumed here.  Being quadratic is the point: it is what makes the longitudinal error term of
`Kakeya.Tube.subset_dilate_rescale_of_subset_dilate` affordable.  The bound is
unconditional, the left-hand side being at most `1`. -/
theorem one_sub_abs_inner_chord_le_of_endpoints_mem_dilate {δ : NNReal} (T : Tube δ E) {c : ℝ}
    (hc : 0 < c) {x y : E} (hxy : dist x y = 1)
    (hx : x ∈ (dilate T c).carrier) (hy : y ∈ (dilate T c).carrier) :
    1 - |inner ℝ T.direction (y - x)| ≤ 4 * c ^ 2 * (δ : ℝ) ^ 2 := by
  let e : E := T.direction
  let f : E := y - x
  let α : ℝ := inner ℝ e f
  have he : ‖e‖ = 1 := by
    dsimp [e]
    exact T.norm_direction
  have hf : ‖f‖ = 1 := by
    dsimp [f]
    rwa [dist_eq_norm'] at hxy
  have hcore : α ^ 2 + ‖f - α • e‖ ^ 2 = 1 := by
    have hmain := inner_sq_add_norm_transverse_sq_eq he f
    rw [hf] at hmain
    simpa [α] using hmain
  have hα_le : |α| ≤ 1 := by
    have hα2 : α ^ 2 ≤ 1 := by
      nlinarith [hcore, sq_nonneg ‖f - α • e‖]
    have hsq : |α| ^ 2 ≤ 1 ^ 2 := by
      simpa [sq_abs] using hα2
    exact le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0)
      (by norm_num : (0 : ℝ) ≤ 1) hsq
  have hA := norm_chord_transverse_le_of_endpoints_mem_dilate T hc hxy hx hy
  have hA' : ‖f - α • e‖ ≤ 2 * c * (δ : ℝ) := by
    simpa [e, f, α] using hA
  have hA_sq : ‖f - α • e‖ ^ 2 ≤ (2 * c * (δ : ℝ)) ^ 2 := by
    exact pow_le_pow_left₀ (norm_nonneg (f - α • e)) hA' 2
  have hsq_val : (2 * c * (δ : ℝ)) ^ 2 = 4 * c ^ 2 * (δ : ℝ) ^ 2 := by ring
  have hsq : ‖f - α • e‖ ^ 2 ≤ 4 * c ^ 2 * (δ : ℝ) ^ 2 := by
    exact le_trans hA_sq (le_of_eq hsq_val)
  have hfin' : 1 - |α| ≤ ‖f - α • e‖ ^ 2 := by
    have hw : ‖f - α • e‖ ^ 2 = 1 - α ^ 2 := by
      nlinarith [hcore]
    rw [hw]
    have hcl : α ^ 2 ≤ |α| := by
      have hle : |α| ^ 2 ≤ |α| := by
        nlinarith [hα_le, abs_nonneg α]
      simpa [sq_abs] using hle
    linarith
  simpa [α, e, f] using le_trans hfin' hsq

/-- **Enlargement, plank case: the tube-level core** (blueprint
`lem:ml1bootEnlargementPlankCore`).

Let `T` be a `δ`-tube and `T₀` a `σ₀`-tube (both of unit length, by the definition of `Tube`),
let `c ≥ 1`, and let `K` be a set with `T₀ ⊆ K ⊆ c · T`.  Then, for any homothety ratio `Λ` and
rescaling radius `ρ` meeting the two budgets

* longitudinal: `2 c ≤ Λ`,
* transverse:   `6 c² δ ≤ Λ ρ`,

one has `K ⊆ Λ · (T₀^{(ρ)})`, a body of longitudinal extent `Λ` and transverse radius `Λ ρ`.

The earlier, fixed-ratio statement is the instance `c = 2`, `Λ = 8`, `ρ = 3 δ`, where both
budgets hold — `4 ≤ 8` and `24 δ ≤ 24 δ`, the transverse one on the nose (blueprint
`def:ml1bootEnlargementPlankConstant`).

This is the whole geometric content of the plank case with the plank removed: what is used of
`K` is only that it sits in a `c`-dilate of *some* unit-length `δ`-tube and contains the
unit-length tube `T₀`.  No upper bound on `δ`, no relation between `δ` and `σ₀`, and no
positivity on either radius is assumed, and `K` is an arbitrary set — no convexity,
compactness or measurability.  The radius `σ₀` never enters: `T₀` is used only through the two
endpoints of its core.

**Why no upper bound on `δ` is needed.**  Run the three inputs at the given `c`, writing `e` for
`T.direction`, `f` for the unit chord of `T₀`'s core and `α` for `⟪e, f⟫`: the endpoints of
that core lie in `c · T`, so `‖f - α • e‖ ≤ 2 c δ`
(`Kakeya.Tube.norm_chord_transverse_le_of_endpoints_mem_dilate`) and `1 - |α| ≤ 4 c² δ²`
(`Kakeya.Tube.one_sub_abs_inner_chord_le_of_endpoints_mem_dilate`), while any `z ∈ K` splits as
`z - T₀.center = τ • e + g` with `|τ| ≤ c` and `‖g‖ ≤ 2 c δ`
(`Kakeya.Tube.exists_axis_repr_sub_midpoint_of_mem_dilate`).  All three are already stated at a
free `c`.  Feeding these to `Kakeya.norm_smul_add_sub_smul_le` puts `z` within
`|τ| (1 - |α|) + |τ| ‖f - α • e‖ + ‖g‖` of `T₀.center + r • f` with `|r| = |τ| ≤ c`.

The three terms are `≤ 2 c² δ` each, so the total is `≤ 6 c² δ`.  For the second this is
`c · 2 c δ`, and for the third `2 c δ ≤ 2 c² δ` by `1 ≤ c`.  The first is unconditional by a
two-case reading:

* `2 c δ ≤ 1`: keep the quadratic bound, `c (1 - |α|) ≤ 4 c³ δ² = c (2 c δ)(2 c δ) ≤ 2 c² δ`;
* `2 c δ ≥ 1`: discard it for the trivial `1 - |α| ≤ 1 ≤ 2 c δ`, so `c (1 - |α|) ≤ 2 c² δ`.

This is also why the quadratic form of
`Kakeya.Tube.one_sub_abs_inner_chord_le_of_endpoints_mem_dilate` is stated unconditionally
rather than under a smallness hypothesis: the large-`δ` case does not use it at all.

The conclusion is **not** a concentric rescaling `T₀^{(r)}` and cannot be strengthened to one
with `r = O(δ)`; nor may the radius factor be read *after* the homothety.  Both
obstructions are worked out at blueprint `def:ml1bootEnlargementPlankConstant`. -/
theorem subset_dilate_rescale_of_subset_dilate {δ σ₀ ρ : NNReal} (T : Tube δ E)
    (T₀ : Tube σ₀ E) {c Λ : ℝ} (hc : 1 ≤ c) (hΛ : 2 * c ≤ Λ)
    (hρ : 6 * c ^ 2 * (δ : ℝ) ≤ Λ * (ρ : ℝ)) {K : Set E}
    (hT₀ : T₀.carrier ⊆ K) (hK : K ⊆ (dilate T c).carrier) :
    K ⊆ (dilate (T₀.rescale ρ) Λ).carrier := by
  intro z hzk
  have hcpos : 0 < c := by linarith
  have hc0 : 0 ≤ c := le_of_lt hcpos
  have hzT : z ∈ (dilate T c).carrier := hK hzk
  have hx : T₀.x ∈ (dilate T c).carrier := hK (hT₀ T₀.x_mem_carrier)
  have hy : T₀.y ∈ (dilate T c).carrier := hK (hT₀ T₀.y_mem_carrier)
  let α : ℝ := inner ℝ T.direction T₀.direction
  let S : ℝ := ‖T₀.direction - α • T.direction‖
  rcases exists_axis_repr_sub_midpoint_of_mem_dilate (T := T) (c := c) hcpos
      (p := T₀.x) (q := T₀.y) (z := z) hx hy hzT with ⟨τ, g, hzmid, hτc, hgm⟩
  have hδ0 : 0 ≤ (δ : ℝ) := NNReal.coe_nonneg δ
  have hα_le_one : |α| ≤ 1 := by
    calc
      |α| ≤ ‖T.direction‖ * ‖T₀.direction‖ := abs_real_inner_le_norm T.direction T₀.direction
      _ = 1 := by rw [T.norm_direction, T₀.norm_direction]; norm_num
  have h1ma0 : 0 ≤ 1 - |α| := by linarith
  have hquad : 1 - |α| ≤ 4 * c ^ 2 * (δ : ℝ) ^ 2 := by
    have hQ := one_sub_abs_inner_chord_le_of_endpoints_mem_dilate (T := T) (c := c) hcpos
      (x := T₀.x) (y := T₀.y) T₀.dist_eq_one hx hy
    simpa [α] using hQ
  have hS : S ≤ 2 * c * (δ : ℝ) := by
    have hch := norm_chord_transverse_le_of_endpoints_mem_dilate (T := T) (c := c) hcpos
      (x := T₀.x) (y := T₀.y) T₀.dist_eq_one hx hy
    simpa [S, α] using hch
  rcases norm_smul_add_sub_smul_le T.norm_direction T₀.norm_direction τ g with ⟨r, hrm, hb⟩
  have hb' : ‖τ • T.direction + g - r • T₀.direction‖
      ≤ |τ| * (1 - |α|) + |τ| * S + ‖g‖ := by
    simpa [α, S] using hb
  have hterm1 : |τ| * (1 - |α|) ≤ 2 * c ^ 2 * (δ : ℝ) := by
    have h1ma_c : c * (1 - |α|) ≤ 2 * c ^ 2 * (δ : ℝ) := by
      rcases le_total (2 * c * (δ : ℝ)) (1 : ℝ) with hsmall | hlarge
      · have ht0 : 0 ≤ 2 * c * (δ : ℝ) := by positivity
        have htsq : (2 * c * (δ : ℝ)) ^ 2 ≤ 2 * c * (δ : ℝ) := by
          nlinarith [hsmall, ht0]
        have h1ma : 1 - |α| ≤ 2 * c * (δ : ℝ) := by
          nlinarith [hquad, htsq]
        calc
          c * (1 - |α|) ≤ c * (2 * c * (δ : ℝ)) := mul_le_mul_of_nonneg_left h1ma hc0
          _ = 2 * c ^ 2 * (δ : ℝ) := by ring
      · have htriv : 1 - |α| ≤ 1 := by linarith [abs_nonneg α]
        have h1ma : 1 - |α| ≤ 2 * c * (δ : ℝ) := by
          nlinarith [htriv, hlarge]
        calc
          c * (1 - |α|) ≤ c * (2 * c * (δ : ℝ)) := mul_le_mul_of_nonneg_left h1ma hc0
          _ = 2 * c ^ 2 * (δ : ℝ) := by ring
    exact (mul_le_mul_of_nonneg_right hτc h1ma0).trans h1ma_c
  have hS0 : 0 ≤ S := by dsimp [S]; exact norm_nonneg _
  have hterm2 : |τ| * S ≤ 2 * c ^ 2 * (δ : ℝ) := by
    calc
      |τ| * S ≤ c * S := mul_le_mul_of_nonneg_right hτc hS0
      _ ≤ c * (2 * c * (δ : ℝ)) := mul_le_mul_of_nonneg_left hS hc0
      _ = 2 * c ^ 2 * (δ : ℝ) := by ring
  have hc_le_c2 : c ≤ c ^ 2 := by nlinarith [hc]
  have hg : ‖g‖ ≤ 2 * c ^ 2 * (δ : ℝ) := by
    calc
      ‖g‖ ≤ 2 * c * (δ : ℝ) := hgm
      _ = 2 * (c * (δ : ℝ)) := by ring
      _ ≤ 2 * (c ^ 2 * (δ : ℝ)) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc_le_c2 hδ0)
          (by positivity : (0 : ℝ) ≤ 2)
      _ = 2 * c ^ 2 * (δ : ℝ) := by ring
  have hsum : |τ| * (1 - |α|) + |τ| * S + ‖g‖ ≤ 6 * c ^ 2 * (δ : ℝ) := by
    nlinarith [hterm1, hterm2, hg]
  have hdist : dist z (T₀.center + r • (T₀.direction)) ≤ 6 * c ^ 2 * (δ : ℝ) := by
    rw [dist_eq_norm]
    have hlead : z - (T₀.center + r • (T₀.direction))
        = (τ • T.direction + g) - r • (T₀.direction) := by
      calc
        z - (T₀.center + r • (T₀.direction)) = (z - T₀.center) - r • (T₀.direction) := by module
        _ = (τ • T.direction + g) - r • (T₀.direction) := by rw [← hzmid]
    rw [hlead]
    exact hb'.trans hsum
  have hident : (T₀.rescale ρ).center + r • (T₀.rescale ρ).direction
      = T₀.center + r • (T₀.direction) := by
    simp [Tube.rescale, Tube.center, Tube.direction]
  have hRdist : 6 * c ^ 2 * (δ : ℝ) ≤ Λ * ((ρ : NNReal) : ℝ) := by
    simpa using hρ
  have hdist' : dist z ((T₀.rescale ρ).center + r • (T₀.rescale ρ).direction)
      ≤ Λ * ((ρ : NNReal) : ℝ) := by
    rw [hident]
    exact hdist.trans hRdist
  have hΛ0 : 0 < Λ := by nlinarith [hΛ, hc]
  have hR : |r| ≤ Λ / 2 := by
    calc
      |r| = |τ| := hrm
      _ ≤ c := hτc
      _ ≤ Λ / 2 := by nlinarith [hΛ]
  exact mem_dilate_of_dist_axis_le (T := T₀.rescale ρ) (C := Λ) hΛ0 (s := r) hR hdist'

end Tube

end Kakeya
