/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.AffineMap
public import Kakeya.Homothety
public import Kakeya.Mathlib.Topology.CoveringNumber
public import Kakeya.Multiplicity
public import Kakeya.Pigeonhole
public import Kakeya.Shading
public import Kakeya.Tube.Basic
public import Kakeya.Tube.CardEssentiallyDistinct
public import Kakeya.Tube.Dilate
public import Kakeya.Tube.EssentiallyDistinctReduction
public import Kakeya.Tube.IntersectionVolume
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Normalizing a coarse tube to the unit ball

The bootstrapping step of GWZ Main Lemma 1 replaces a family of `τ`-tubes contained
in one fixed `θ`-tube `T_θ` by a family of bodies of thickness `τ / θ` living in a
ball of bounded radius.  This is *not* `Tube.rescale`, which re-thickens a tube in
place and does not move the ambient ball.  The correct map is the **anisotropic
normalization of `T_θ`**: it is the identity along the core direction of `T_θ` and
dilates the orthogonal complement of that direction by `θ⁻¹`.

Writing `[x, y]` for the core segment of `T_θ`, `e = y - x` (a unit vector), `π` for
the orthogonal projection onto `ℝ ∙ e` and `π⊥ = id - π`, the map is

```
Φ_{T_θ} (z) = x + π (z - x) + θ⁻¹ • π⊥ (z - x).
```

This file supplies `Tube.normalization` (the map), `Tube.normalization.C` (its
distortion constant), `Tube.normalization_distortion` (the geometric estimate),
`ShadedTube.normalizeInto` (the induced operation on shaded tubes) and
`ShadedTube.normalizeInto_transport` (invariance of all the ratio-of-volume
quantities along it).

It also supplies the companion step that turns bodies comparable to tubes back into
honest tubes, `Tube.exists_comparableReplacement` with its selection constant
`Tube.comparableReplacement.C` (blueprint `lem:comparableBodiesToTubes` and
`def:comparableBodiesToTubesConstant`).

## Blueprint correspondence

Each of the three main lemmas states its conclusion as a `Prop`-valued structure whose
fields are the numbered items of the corresponding blueprint lemma, so that a downstream
argument can quote one item instead of projecting out of a nested conjunction.

* `Tube.normalization.C` ↔ `def:tubeNormalizationConstant`: value `2 ^ (n + 3)`.
* `Tube.IsNormalizationDistortion` ↔ `lem:tubeNormalizationDistortion`:
  `one_le_dist`, `dist_le_C` ↔ (i); `image_subset_cthickening` ↔ (ii);
  `exists_subsegment` ↔ (iii); `image_ambient_subset_closedBall` ↔ (iv).
* `ShadedTube.IsNormalizeIntoTransport` ↔ `lem:tubeNormalizationTransport`:
  `card` ↔ (i); `multiplicity` ↔ (ii); `fullness` ↔ (iii);
  `densityIn`, `maxDensity` ↔ (iv); `frostmanConstIn` ↔ (v);
  `essentiallyDistinct` ↔ (vi).
* `Tube.comparableReplacement.C` ↔ `def:comparableBodiesToTubesConstant`:
  value `1 + 2 * C * C_n`.
* `Tube.essDistinctTubesInDilate.thin_absorbed` ↔ `lem:essDistinctTubesInThinDilateAbsorbed`
  and `Tube.essDistinctTubesInDilate.fat_absorbed` ↔ `lem:essDistinctTubesInFatDilateAbsorbed`:
  the two regimes of the packing count are produced in `Kakeya/Tube/Dilate.lean`
  (`Tube.essDistinctTubesInThinDilate`, `Tube.essDistinctTubesInFatDilate`) and absorbed into
  `Tube.comparableReplacement.C` here, where that constant is defined.
* `Tube.essDistinctTubesInDilate` ↔ `lem:essDistinctTubesInDilate`.
* `Tube.IsComparableReplacement` ↔ `lem:comparableBodiesToTubes`:
  `multiplicity` ↔ (i); `fullness` ↔ (ii); `frostmanConstIn` ↔ (iii);
  `select` ↔ (iv) and (v), bundled since they share the witness `s'`.
* `Tube.rescaleMap` ↔ `def:tubeRescale`: the normalization followed by the homothety
  `z ↦ (z - T₀.x) / (4 R)`.  The blueprint records the target `Tube.rescale`, which is
  already taken by the unrelated re-thickening operation of `Kakeya/Tube/Basic.lean`.
* `Tube.IsRescalingSituation` ↔ the standing hypotheses that
  `section8_finenormalize_select.tex` names *the rescaling situation*.
* `Tube.centredExtension` ↔ `def:centredExtensionTube`.
* `Tube.cthickening_subset_centredExtension`, `Tube.centredExtension_subset_closedBall`,
  `Tube.center_centredExtension` and `Tube.direction_centredExtension` ↔
  `lem:centredExtensionProperties` (i), (ii), (iii); item (iii) asserts two independent
  equalities and is therefore two Lean lemmas rather than one conjunction.
* `Tube.volume_centredExtension_le_mul_volume_rescale_image` ↔ `lem:rescaleImageVolumeRatio`,
  at the general dimension and with the dimensional factor `κ(n)` explicit.
* `Tube.rescale_outer_tube` ↔ `lem:coreOuterTube`, whose four hypotheses (a)–(d) are the
  distortion package, so it is stated with `Tube.IsNormalizationDistortion` in their place.
  Its volume clause is the `n = 3` clause of the blueprint lemma and is stated under
  `Module.finrank ℝ E = 3`: the numeral `(4 R) ^ 6` is **not** the general-`n` bound
  `(4 R) ^ (2 n)`, which is false — see the statement.

* `Tube.rescaleMap_apply`, `Tube.rescaleMap_apply_x`: the metric layer of `Tube.rescaleMap`.
* `Tube.rescale_symm_apply_add_smul` ↔ `lem:rescalePullbackAxis`,
  `Tube.norm_rescale_symm_vector_le` ↔ `lem:rescalePullbackVector` and
  `Tube.preimage_rescale_dilate_subset_dilate` ↔ `lem:rescalePullbackDilate`: the three
  pullbacks of the downstairs selection.  All three are stated *forwards*, in terms of
  `Tube.rescaleMap` rather than of an affine equivalence `Ψ⁻¹`; see the section docstring
  there for why, and why the forward forms are equivalent and not weaker.
* `Tube.essDistinctTubesInSelfDilate.C` ↔ `def:essDistinctTubesInSelfDilateConstant` and
  `Tube.essDistinctTubesInSelfDilate` ↔ `lem:essDistinctTubesInSelfDilate`, the single **open
  leaf** of that route.

* `Tube.card_le_mul_card_of_dilateCover_affine` ↔ `lem:comparableAffineFibreBound` and
  `Tube.exists_comparableReplacement_affine` ↔ `lem:comparableAffineImagesToTubes`, the two
  lemmas of `section8_finenormalize_count.tex` built on that leaf: the affine substitutes for
  `Tube.card_le_mul_card_of_dilateCover` and `Tube.exists_comparableReplacement` on the
  fine-normalization route.  Their conclusion bundle is `Tube.IsComparableReplacementFree`,
  which is `Tube.IsComparableReplacement` at a free selection constant, and the refinement
  clause is cited at that free constant as `Tube.isCRefinement_of_card_le_free` ↔
  `lem:comparableRefinementClauseFree`.  Both are proved *modulo* the open leaf above and
  nothing else.

`lem:rescaleImageVolumeRatio` and `lem:coreOuterTube` are still not stated here; see the
section docstring in the middle of this file for what they need.

Two entries deviate deliberately from the informal wording, in each case strengthening or
correcting it; both deviations are documented at the structure they occur in.
`IsNormalizationDistortion` states (ii) and (iii) with `Metric.cthickening` of a segment
in place of "is contained in / contains a tube" — see the next section, and blueprint
`note:tubeNormalizationNotTubes`.  `IsNormalizeIntoTransport` states (iii) as an equality
rather than a two-sided comparison, and quantifies (iv), (v) over *every* convex body.

## Divergence from the informal statement

The blueprint (`GWZAdapted/section8_infra.tex`,
`lem:tubeNormalizationDistortion`) asserts that `Φ_{T_θ} (T)` is *contained in a
`C (τ/θ)`-tube* and *contains a `C⁻¹ (τ/θ)`-tube*.  Both halves are false for the
`Tube` structure of this development, because a `Tube` has a core segment of length
**exactly one**:

* `Φ_{T_θ}` is the identity along `e` and expands `e^⊥` by `θ⁻¹ ≥ 1`, so it
  *lengthens* core segments.  Quantitatively, if `T ⊆ T_θ` is a `τ`-tube with unit
  core direction `f`, then `f = c • e + g` with `g ⊥ e` and `‖g‖ ≤ 2 θ`, so the
  image core has length `√(c² + θ⁻²‖g‖²) ∈ [1, √5]`.  A set whose core has length
  `> 1 + O(ρ)` is not contained in any `ρ`-tube for small `ρ`.
* Symmetrically, a `ρ`-tube is the closed `ρ`-neighbourhood of a *unit* segment, so
  its end caps stick out by `ρ` beyond the core; the image `Φ_{T_θ} (T)` only sticks
  out by `τ = θ ρ ≪ ρ` beyond its own core, so it contains no `C⁻¹ ρ`-tube either
  (take `f = e`, where the image core has length exactly one and there is no slack).

What is true — and what the informal proof actually establishes — is the same
two-sided estimate with `ρ`-tubes replaced by closed `ρ`-neighbourhoods of segments
of length comparable to one (`Metric.cthickening ρ (segment ℝ a b)`, which is the
carrier of a tube by `Tube.carrier_eq_cthickening` exactly when `dist a b = 1`).
`Tube.normalization_distortion` is stated in that form.  Passing from there to
honest `τ/θ`-tubes is a separate step, with a bounded loss; in the blueprint it is
`lem:comparableBodiesToTubes` (`GWZAdapted/section8_genkf.tex`), formalized below as
`Tube.exists_comparableReplacement`.  That step needs *two-sided* comparability — an inner
tube inside each body as well as an outer one — see the docstring there and blueprint
`note:comparableBodiesGap`.

The transport lemma `ShadedTube.normalizeInto_transport` is unaffected by this: it
concerns only ratios of volumes along the affine bijection `Φ_{T_θ}`, and needs
neither `τ ≤ θ` nor `T_i ⊆ T_θ`.  Its fullness clause is an *equality*, not the
two-sided comparison of the informal statement: the normalized family consists of
the images `Φ_{T_θ}(T_i)` themselves, not of honest tubes replacing them, so the
constant Jacobian of `Φ_{T_θ}` cancels exactly.
-/

@[expose] public section

open MeasureTheory Metric Set

namespace Tube

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {θ τ : NNReal}

/-- The anisotropic dilation of ratio `c` along the core direction of `T`: the identity on
the line `ℝ ∙ T.direction` and the dilation by `c` on its orthogonal complement.  Written as
`c • id + (1 - c) • (z ↦ ⟪e, z⟫ • e)` with `e = T.direction`, which is legitimate because
`‖T.direction‖ = 1` (`Tube.norm_direction`).

Only the two values `c = θ⁻¹` (`Tube.normalizationLinear`) and `c = θ` (its inverse) are
used; the parameter is left free so that the two are inverse to each other by the single
composition rule `Tube.dilateAux_comp`. -/
noncomputable def dilateAux (T : Tube θ E) (c : ℝ) : E →L[ℝ] E :=
  c • ContinuousLinearMap.id ℝ E
    + (1 - c) • (innerSL ℝ T.direction).smulRight T.direction

omit [MeasurableSpace E] [BorelSpace E] in
theorem dilateAux_apply (T : Tube θ E) (c : ℝ) (z : E) :
    T.dilateAux c z = c • z + (1 - c) • (inner ℝ T.direction z • T.direction) := rfl

omit [MeasurableSpace E] [BorelSpace E] in
@[simp]
theorem dilateAux_one (T : Tube θ E) : T.dilateAux 1 = ContinuousLinearMap.id ℝ E := by
  ext z; simp [dilateAux_apply]

omit [MeasurableSpace E] [BorelSpace E] in
/-- `Tube.dilateAux` is multiplicative in its ratio: the composition of the dilations of
ratios `c` and `c'` is the dilation of ratio `c * c'`.  This is where `‖T.direction‖ = 1`
enters, through the idempotence of `z ↦ ⟪e, z⟫ • e`. -/
theorem dilateAux_comp (T : Tube θ E) (c c' : ℝ) (z : E) :
    T.dilateAux c (T.dilateAux c' z) = T.dilateAux (c * c') z := by
  have he : (inner ℝ T.direction T.direction : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, T.norm_direction]; norm_num
  simp only [dilateAux_apply, inner_add_right, inner_smul_right, he]
  module

/-- The linear part of `Tube.normalization T`: the identity on the line `ℝ ∙ T.direction`
and the dilation by `θ⁻¹` on its orthogonal complement.  Written as
`θ⁻¹ • id + (1 - θ⁻¹) • (z ↦ ⟪e, z⟫ • e)` with `e = T.direction`, which is legitimate
because `‖T.direction‖ = 1` (`Tube.norm_direction`). -/
noncomputable def normalizationLinear (T : Tube θ E) : E →L[ℝ] E := T.dilateAux (θ : ℝ)⁻¹

omit [MeasurableSpace E] [BorelSpace E] in
theorem normalizationLinear_eq_dilateAux (T : Tube θ E) :
    T.normalizationLinear = T.dilateAux (θ : ℝ)⁻¹ := rfl

omit [MeasurableSpace E] [BorelSpace E] in
theorem normalizationLinear_comp_dilateAux (hθ : 0 < θ) (T : Tube θ E) :
    T.normalizationLinear.toLinearMap ∘ₗ (T.dilateAux (θ : ℝ)).toLinearMap = LinearMap.id := by
  have hθ' : (θ : ℝ) ≠ 0 := ne_of_gt hθ
  ext z
  simp [normalizationLinear, dilateAux_comp, inv_mul_cancel₀ hθ']

omit [MeasurableSpace E] [BorelSpace E] in
theorem dilateAux_comp_normalizationLinear (hθ : 0 < θ) (T : Tube θ E) :
    (T.dilateAux (θ : ℝ)).toLinearMap ∘ₗ T.normalizationLinear.toLinearMap = LinearMap.id := by
  have hθ' : (θ : ℝ) ≠ 0 := ne_of_gt hθ
  ext z
  simp [normalizationLinear, dilateAux_comp, mul_inv_cancel₀ hθ']

/-- **The linear part of the normalization as a continuous linear equivalence.**  Its inverse
is given by the same formula with `θ` in place of `θ⁻¹`, i.e. by `Tube.dilateAux θ`. -/
noncomputable def normalizationLinearEquiv (hθ : 0 < θ) (T : Tube θ E) : E ≃L[ℝ] E where
  toLinearEquiv :=
    LinearEquiv.ofLinear T.normalizationLinear.toLinearMap (T.dilateAux (θ : ℝ)).toLinearMap
      (normalizationLinear_comp_dilateAux hθ T) (dilateAux_comp_normalizationLinear hθ T)
  continuous_toFun := T.normalizationLinear.continuous
  continuous_invFun := (T.dilateAux (θ : ℝ)).continuous

omit [MeasurableSpace E] [BorelSpace E] in
@[simp]
theorem normalizationLinearEquiv_apply (hθ : 0 < θ) (T : Tube θ E) (z : E) :
    normalizationLinearEquiv hθ T z = T.normalizationLinear z := rfl

/-- **The normalization of a `θ`-tube.**  With core segment `[x, y]`, `e = y - x`,
`π` the orthogonal projection onto `ℝ ∙ e` and `π⊥ = id - π`, this is the affine map

```
Φ_{T_θ} (z) = x + π (z - x) + θ⁻¹ • π⊥ (z - x).
```

It fixes `x` and the direction `e`, and stretches `e^⊥` by `θ⁻¹`; it is invertible as
soon as `0 < θ` (`Tube.normalization_injective`). -/
noncomputable def normalization (T : Tube θ E) : E →ᵃ[ℝ] E :=
  (AffineEquiv.constVAdd ℝ E T.x).toAffineMap.comp
    (T.normalizationLinear.toLinearMap.toAffineMap.comp
      (AffineEquiv.constVAdd ℝ E (-T.x)).toAffineMap)

/-- **The normalization of a nondegenerate tube as an affine equivalence.**  It is the
conjugate of `Tube.normalizationLinearEquiv` by the translation taking `T.x` to the origin;
`Tube.normalization` is its underlying affine map (`Tube.normalizationEquiv_apply`). -/
noncomputable def normalizationEquiv (hθ : 0 < θ) (T : Tube θ E) : E ≃ᵃ[ℝ] E :=
  ((AffineEquiv.constVAdd ℝ E (-T.x)).trans
      (normalizationLinearEquiv hθ T).toLinearEquiv.toAffineEquiv).trans
    (AffineEquiv.constVAdd ℝ E T.x)

omit [MeasurableSpace E] [BorelSpace E] in
@[simp]
theorem normalizationEquiv_apply (hθ : 0 < θ) (T : Tube θ E) (z : E) :
    normalizationEquiv hθ T z = T.normalization z := by
  simp [normalizationEquiv, normalization, AffineEquiv.constVAdd]

omit [MeasurableSpace E] [BorelSpace E] in
theorem normalizationEquiv_coe (hθ : 0 < θ) (T : Tube θ E) :
    ⇑(normalizationEquiv hθ T) = ⇑T.normalization :=
  funext fun z => normalizationEquiv_apply hθ T z

/-- The defining formula for `Tube.normalization`. -/
theorem normalization_apply (T : Tube θ E) (z : E) :
    T.normalization z = T.x + (inner ℝ T.direction (z - T.x) • T.direction +
      (θ : ℝ)⁻¹ • (z - T.x - inner ℝ T.direction (z - T.x) • T.direction)) := by
  simp [normalization, normalizationLinear, dilateAux_apply, AffineEquiv.constVAdd]
  rw [show -T.x + z = z - T.x by abel]
  module

@[simp]
theorem normalization_apply_x (T : Tube θ E) : T.normalization T.x = T.x := by
  simp [normalization, normalizationLinear, dilateAux_apply, AffineEquiv.constVAdd]

omit [MeasurableSpace E] [BorelSpace E] in
theorem normalization_continuous (T : Tube θ E) : Continuous T.normalization := by
  rw [← AffineMap.continuous_linear_iff]
  exact T.normalizationLinear.continuous

omit [MeasurableSpace E] [BorelSpace E] in
/-- The normalization of a nondegenerate tube is injective. -/
theorem normalization_injective (hθ : 0 < θ) (T : Tube θ E) :
    Function.Injective T.normalization := by
  rw [← normalizationEquiv_coe hθ T]
  exact (normalizationEquiv hθ T).toEquiv.injective

omit [MeasurableSpace E] [BorelSpace E] in
/-- The normalization of a nondegenerate tube is surjective; together with
`Tube.normalization_injective` this is the invertibility asserted in the blueprint. -/
theorem normalization_surjective (hθ : 0 < θ) (T : Tube θ E) :
    Function.Surjective T.normalization := by
  rw [← normalizationEquiv_coe hθ T]
  exact (normalizationEquiv hθ T).toEquiv.surjective

/-- The normalization of a nondegenerate tube is a measurable embedding.  This is what lets
the shading of a `ShadedTube` be pushed forward along it; compare
`Kakeya.measurableEmbedding_homothety`. -/
theorem measurableEmbedding_normalization (hθ : 0 < θ) (T : Tube θ E) :
    MeasurableEmbedding T.normalization := by
  rw [← normalizationEquiv_coe hθ T]
  exact (AffineEquiv.toContinuousAffineEquiv
    (normalizationEquiv hθ T)).toHomeomorph.measurableEmbedding

omit [MeasurableSpace E] [BorelSpace E] in
/-- **The determinant of the anisotropic dilation `Tube.dilateAux T c` is `c ^ (n - 1)`.**  The
map is the identity on the line `ℝ ∙ T.direction` and the dilation by `c` on the
`(n-1)`-dimensional quotient by that line, so the determinant splits as `1 * c ^ (n - 1)`
(`LinearMap.det_eq_det_mul_det`).  This is the one computation behind
`Tube.volume_image_normalization`, which is the case `c = θ⁻¹`. -/
private lemma det_dilateAux (T : Tube θ E) (c : ℝ) : -- (extracted by Fuse golfer)
    LinearMap.det (T.dilateAux c : E →ₗ[ℝ] E) = c ^ (Module.finrank ℝ E - 1) := by
  set Lm : E →ₗ[ℝ] E := (T.dilateAux c : E →ₗ[ℝ] E)
  have hLapply (v : E) : Lm v = c • v + (1 - c) • (inner ℝ T.direction v • T.direction) :=
    T.dilateAux_apply c v
  have hne : T.direction ≠ 0 := norm_ne_zero_iff.mp (by rw [T.norm_direction]; exact one_ne_zero)
  have hmem : T.direction ∈ (ℝ ∙ T.direction : Submodule ℝ E) :=
    Submodule.mem_span_singleton_self _
  have hLdir : Lm T.direction = T.direction := by
    rw [hLapply, real_inner_self_eq_norm_sq, T.norm_direction, one_pow, one_smul, ← add_smul,
      add_sub_cancel, one_smul]
  have hle : (ℝ ∙ T.direction : Submodule ℝ E) ≤ (ℝ ∙ T.direction).comap Lm := by
    rw [Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Submodule.mem_comap, hLdir]
    exact hmem
  have hrestrict : Lm.restrict hle = LinearMap.id := by
    refine LinearMap.ext fun w => Subtype.ext ?_
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp w.2
    simp only [LinearMap.restrict_apply, LinearMap.id_coe, id_eq, ← ha, map_smul, hLdir]
  have hmapQ : (ℝ ∙ T.direction).mapQ (ℝ ∙ T.direction) Lm hle = c • LinearMap.id := by
    refine LinearMap.ext fun q => Submodule.Quotient.induction_on _ q fun v => ?_
    rw [Submodule.mapQ_apply, LinearMap.smul_apply, LinearMap.id_apply,
      ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq,
      show Lm v - c • v = (1 - c) • (inner ℝ T.direction v • T.direction) from by
        rw [hLapply, add_sub_cancel_left]]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hmem)
  rw [LinearMap.det_eq_det_mul_det (ℝ ∙ T.direction) Lm hle, hrestrict, LinearMap.det_id,
    one_mul, hmapQ, LinearMap.det_smul, LinearMap.det_id, mul_one]
  congr 1
  have hfin := Submodule.finrank_quotient_add_finrank (R := ℝ) (M := E) (ℝ ∙ T.direction)
  rw [finrank_span_singleton hne] at hfin
  omega

/-- The normalization has constant Jacobian `θ^{-(n-1)}`: it multiplies every volume by
`θ^{-(n-1)}`, where `n = finrank ℝ E`.  This single fact is what makes every clause of
`ShadedTube.normalizeInto_transport` a cancellation of a common factor.

The factor is the *expansion* ratio, matching the convention of
`ConvexSpaceBody.volume_homothety`: `Tube.normalizationLinear` has eigenvalue `1` on
`ℝ ∙ T.direction` and eigenvalue `θ⁻¹ ≥ 1` on its orthogonal complement, so its
determinant has absolute value `θ^{-(n-1)}` (`Tube.det_dilateAux`) and the map *enlarges*
volumes.

The `Nontrivial E` instance makes `1 ≤ n`, so that the truncated natural subtraction
`Module.finrank ℝ E - 1` is the honest exponent `n - 1`. -/
theorem volume_image_normalization [Nontrivial E] (hθ : 0 < θ) (T : Tube θ E) (A : Set E) :
    volume (T.normalization '' A)
      = (θ : ENNReal)⁻¹ ^ (Module.finrank ℝ E - 1) * volume A := by
  set Lm : E →ₗ[ℝ] E := (T.normalizationLinear : E →ₗ[ℝ] E)
  have hnn : (0 : ℝ) ≤ (θ : ℝ)⁻¹ := inv_nonneg.mpr θ.coe_nonneg
  have hdet : LinearMap.det Lm = (θ : ℝ)⁻¹ ^ (Module.finrank ℝ E - 1) :=
    T.det_dilateAux (θ : ℝ)⁻¹
  have hLm (z : E) : T.normalization z = (T.x - Lm T.x) + Lm z := by
    change T.x + Lm (-T.x + z) = _
    rw [map_add, map_neg, ← add_assoc, ← sub_eq_add_neg]
  have himg : T.normalization '' A = (fun z => (T.x - Lm T.x) + z) '' (Lm '' A) := by
    rw [← Set.image_comp]; exact Set.image_congr' hLm
  have hvadd (v : E) (S : Set E) : volume ((fun z => v + z) '' S) = volume S := by
    rw [Set.image_add_left]; exact measure_preimage_vadd (μ := volume) (-v) S
  rw [himg, hvadd, Measure.addHaar_image_linearMap, hdet, abs_of_nonneg (pow_nonneg hnn _),
    ENNReal.ofReal_pow hnn, ENNReal.ofReal_inv_of_pos (NNReal.coe_pos.mpr hθ),
    ENNReal.ofReal_coe_nnreal]

/-- The **distortion constant of the normalization** in dimension `n`; the blueprint writes
it `C_{lem:tubeNormalizationDistortion}(n) ≥ 1`.
It depends only on the ambient dimension and on nothing else — in particular not on `θ`,
not on `τ`, and not on the tubes involved.  The value `2 ^ (n + 3)` is a deliberately
generous explicit choice for the bound established by
`Tube.normalization_distortion`. -/
noncomputable abbrev normalization.C (n : ℕ) : NNReal := 2 ^ (n + 3)

theorem normalization.one_le_C (n : ℕ) : 1 ≤ normalization.C n := by
  exact one_le_pow₀ (a := (2 : NNReal)) (n := n + 3) (by norm_num)

/-- **The conclusions of `Tube.normalization_distortion`, one field per item.**

Here `T₀` is a `θ`-tube, `T` a `τ`-tube contained in it, `C = Tube.normalization.C n` and
`ρ = τ / θ`; write `a = Φ_{T₀}(T.x)` and `b = Φ_{T₀}(T.y)` for the endpoints of the image
core.  The fields are the items (i)–(iv) of the blueprint lemma
`lem:tubeNormalizationDistortion`, with item (i) split into its two halves `one_le_dist`
and `dist_le_C`; they are named rather than bundled into a nested conjunction so that a
downstream argument can quote a single item, matching the convention already used by
`ShadedTube.IsNormalizeIntoTransport` and `Tube.IsComparableReplacement`.

The fields `image_subset_cthickening` and `exists_subsegment` — the blueprint's (ii) and
(iii) — replace the earlier reading "contained in a `C ρ`-tube / contains a `C⁻¹ ρ`-tube":
see the module docstring for why the literal statement is false for tubes with a core of
length exactly one. -/
structure IsNormalizationDistortion (T₀ : Tube θ E) (T : Tube τ E) : Prop where
  /-- (i, lower half) The image core is at least as long as the original unit core: the
  normalization is the identity along `T₀.direction` and expands its orthogonal complement
  by `θ⁻¹ ≥ 1`, so it never shortens a segment. -/
  one_le_dist : 1 ≤ dist (T₀.normalization T.x) (T₀.normalization T.y)
  /-- (i, upper half) The image core has length at most `C`. -/
  dist_le_C : dist (T₀.normalization T.x) (T₀.normalization T.y)
    ≤ (normalization.C (Module.finrank ℝ E) : ℝ)
  /-- (ii) `Φ_{T₀}(T)` is contained in the closed `C ρ`-neighbourhood of the image core
  `[a, b]`. -/
  image_subset_cthickening : T₀.normalization '' T.carrier ⊆
    cthickening ((normalization.C (Module.finrank ℝ E) : ℝ) * ((τ : ℝ) / (θ : ℝ)))
      (segment ℝ (T₀.normalization T.x) (T₀.normalization T.y))
  /-- (iii) `Φ_{T₀}(T)` contains the closed `C⁻¹ ρ`-neighbourhood of a sub-segment of the
  image core `[a, b]` of length at least `7/8`; taking the sub-segment inside `[a, b]` is
  what makes it "a segment with the same direction as `[a, b]`".

  The length `7/8 = 1 - 2 * (1/16)` is the strongest this route delivers, and *unit* length is
  **false** (module docstring, blueprint `note:tubeNormalizationNotTubes`): the trimming
  parameter is `lam = C⁻¹ ρ ≤ 1/16`, so the sub-segment has length `1 - 2 lam ≥ 7/8`, and one
  cannot take `lam = 0`.  Indeed `Φ_{T₀}(T)` protrudes beyond `[a', b']` by only `τ = θ ρ`,
  whereas the `C⁻¹ ρ`-neighbourhood of a *unit* sub-segment must protrude by `C⁻¹ ρ`; and when
  the core of `T` is parallel to the axis of `T₀` one has `dist a' b' = 1` exactly, so a unit
  sub-segment is the whole of `[a', b']` and there is no interior slack to take up.  The
  unit-length reading therefore forces `τ ≥ C⁻¹`, which fails in the whole regime of interest.
  The radius of the neighbourhood stays `C⁻¹ ρ`; only the length is strengthened. -/
  exists_subsegment : ∃ a ∈ segment ℝ (T₀.normalization T.x) (T₀.normalization T.y),
    ∃ b ∈ segment ℝ (T₀.normalization T.x) (T₀.normalization T.y),
      (7 / 8 : ℝ) ≤ dist a b ∧
      cthickening ((normalization.C (Module.finrank ℝ E) : ℝ)⁻¹ * ((τ : ℝ) / (θ : ℝ)))
        (segment ℝ a b) ⊆ T₀.normalization '' T.carrier
  /-- (iv) `Φ_{T₀}(T₀)` lies in the ball of radius `C` about the fixed point `T₀.x`. -/
  image_ambient_subset_closedBall : T₀.normalization '' T₀.carrier
    ⊆ closedBall T₀.x (normalization.C (Module.finrank ℝ E) : ℝ)

/-! ### The metric layer behind `Tube.normalization_distortion`

Everything in `Tube.normalization_distortion` rests on one computation,
`Tube.norm_sq_normalization_sub`: writing `e = T.direction` and `u = z - w`,

```
‖Φ z - Φ w‖² = ⟪e, u⟫² + θ⁻² ‖u - ⟪e, u⟫ • e‖².
```

The parallel component is untouched and the perpendicular one is multiplied by `θ⁻¹ ≥ 1`.
The lemmas below record that identity, its two immediate consequences (`Φ` never shortens
and is `θ⁻¹`-Lipschitz), and the one geometric input coming from `T ⊆ T₀`, namely that a
point of a `θ`-tube is within `θ` of its core axis. -/

/-- Displacement formula for `Tube.normalization`: it is the identity on `T.direction` and
dilates the orthogonal complement by `θ⁻¹`. -/
lemma normalization_sub_apply (T : Tube θ E) (z w : E) :
    T.normalization z - T.normalization w =
      (inner ℝ T.direction (z - w)) • T.direction +
        (θ : ℝ)⁻¹ • (z - w - (inner ℝ T.direction (z - w)) • T.direction) := by
  have hlin : (T.normalization : E →ᵃ[ℝ] E).linear = T.normalizationLinear.toLinearMap := by
    rfl
  calc
    T.normalization z - T.normalization w = T.normalization.linear (z - w) := by
      simpa [vsub_eq_sub] using (AffineMap.linearMap_vsub T.normalization z w).symm
    _ = T.normalizationLinear (z - w) := by
      rw [hlin]; rfl
    _ = (θ : ℝ)⁻¹ • (z - w) + (1 - (θ : ℝ)⁻¹) • (inner ℝ T.direction (z - w) • T.direction) := by
      simp [normalizationLinear, dilateAux_apply]
    _ = (inner ℝ T.direction (z - w)) • T.direction +
        (θ : ℝ)⁻¹ • (z - w - (inner ℝ T.direction (z - w)) • T.direction) := by
      module

/-- The perpendicular part of `d` with respect to `T.direction` is orthogonal to
`T.direction`. -/
lemma inner_direction_sub_proj (T : Tube θ E) (d : E) :
    inner ℝ T.direction (d - (inner ℝ T.direction d) • T.direction) = 0 := by
  have he : (inner ℝ T.direction T.direction : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, T.norm_direction]; norm_num
  rw [inner_sub_right, inner_smul_right, he]
  ring

/-- The perpendicular part of `d` with respect to the unit vector `T.direction` is no longer
than `d` itself. -/
lemma norm_perp_le (T : Tube θ E) (d : E) :
    ‖d - (inner ℝ T.direction d) • T.direction‖ ≤ ‖d‖ := by
  have he : (inner ℝ T.direction T.direction : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, T.norm_direction]; norm_num
  have hsq : ‖d - (inner ℝ T.direction d) • T.direction‖ ^ 2 ≤ ‖d‖ ^ 2 := by
    have hmain := norm_add_sq (𝕜 := ℝ) (x := (inner ℝ T.direction d) • T.direction)
      (y := d - (inner ℝ T.direction d) • T.direction)
    have hdecomp : d = (inner ℝ T.direction d) • T.direction +
        (d - (inner ℝ T.direction d) • T.direction) := by abel
    rw [← hdecomp] at hmain
    have hcross : inner ℝ ((inner ℝ T.direction d) • T.direction)
        (d - (inner ℝ T.direction d) • T.direction) = 0 := by
      simp [inner_smul_left, inner_direction_sub_proj]
    have hd : ‖d‖ ^ 2 = ‖(inner ℝ T.direction d) • T.direction‖ ^ 2 +
        ‖d - (inner ℝ T.direction d) • T.direction‖ ^ 2 := by
      rw [hmain, hcross]
      simp
    have hpe : ‖(inner ℝ T.direction d) • T.direction‖ ^ 2 = (inner ℝ T.direction d) ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, T.norm_direction, mul_one, sq_abs]
    nlinarith [hd, hpe, sq_nonneg (inner ℝ T.direction d)]
  have h := sq_le_sq.mp hsq
  simpa using h

/-- The linear part of the normalization multiplies the perpendicular part `d - ⟪e, d⟫ • e`
of a vector `d` by `θ⁻¹`. -/
lemma normalizationLinear_perp (T : Tube θ E) (d : E) :
    T.normalizationLinear (d - (inner ℝ T.direction d) • T.direction) =
      (θ : ℝ)⁻¹ • (d - (inner ℝ T.direction d) • T.direction) := by
  simp [normalizationLinear, dilateAux_apply, inner_direction_sub_proj]

/-- The linear part of the normalization fixes `T.direction`. -/
lemma normalizationLinear_direction (T : Tube θ E) :
    T.normalizationLinear T.direction = T.direction := by
  simp [normalizationLinear, dilateAux_apply, T.norm_direction]

/-- **The single computation behind `Tube.normalization_distortion`.**  With `e = T.direction`
and `u = z - w`, the parallel component of `u` is preserved and the perpendicular one is
multiplied by `θ⁻¹`, so

```
‖Φ z - Φ w‖² = ⟪e, u⟫² + θ⁻² ‖u - ⟪e, u⟫ • e‖².
```

Every clause of `Tube.IsNormalizationDistortion` is an inequality consequence of this identity
together with `θ ≤ 1`. -/
lemma norm_sq_normalization_sub (T : Tube θ E) (z w : E) :
    ‖T.normalization z - T.normalization w‖ ^ 2 =
      (inner ℝ T.direction (z - w)) ^ 2 +
        ((θ : ℝ)⁻¹) ^ 2 * ‖z - w - (inner ℝ T.direction (z - w)) • T.direction‖ ^ 2 := by
  rw [normalization_sub_apply]
  have hcross : inner ℝ ((inner ℝ T.direction (z - w)) • T.direction)
      ((θ : ℝ)⁻¹ • (z - w - (inner ℝ T.direction (z - w)) • T.direction)) = 0 := by
    simp [inner_smul_left, inner_smul_right, inner_direction_sub_proj]
  rw [norm_add_sq (𝕜 := ℝ)]
  rw [hcross]
  have he : ‖T.direction‖ = 1 := T.norm_direction
  simp [he, sq_abs, norm_smul, Real.norm_eq_abs]
  ring

/-- The Pythagoras decomposition of a displacement into parallel and perpendicular parts. -/
lemma norm_sq_sub (T : Tube θ E) (z w : E) :
    ‖z - w‖ ^ 2 = (inner ℝ T.direction (z - w)) ^ 2 +
      ‖z - w - (inner ℝ T.direction (z - w)) • T.direction‖ ^ 2 := by
  have hdecomp : (inner ℝ T.direction (z - w)) • T.direction +
      (z - w - (inner ℝ T.direction (z - w)) • T.direction) = z - w := by abel
  have hcross : inner ℝ ((inner ℝ T.direction (z - w)) • T.direction)
      (z - w - (inner ℝ T.direction (z - w)) • T.direction) = 0 := by
    simp [inner_smul_left, inner_direction_sub_proj]
  have hmain := norm_add_sq (𝕜 := ℝ) (x := (inner ℝ T.direction (z - w)) • T.direction)
    (y := z - w - (inner ℝ T.direction (z - w)) • T.direction)
  rw [hdecomp] at hmain
  rw [hmain, hcross]
  have he : ‖T.direction‖ = 1 := T.norm_direction
  simp [he, sq_abs, norm_smul, Real.norm_eq_abs]

/-- The normalization never shortens: `dist z w ≤ dist (Φ z) (Φ w)`. -/
lemma dist_le_dist_normalization (hθ : 0 < θ) (hθ1 : θ ≤ 1) (T : Tube θ E) (z w : E) :
    dist z w ≤ dist (T.normalization z) (T.normalization w) := by
  rw [dist_eq_norm, dist_eq_norm]
  have hθinv : (1 : ℝ) ≤ (θ : ℝ)⁻¹ := (one_le_inv₀ (by exact_mod_cast hθ)).2 (by exact_mod_cast hθ1)
  have hθinv_sq : (1 : ℝ) ≤ ((θ : ℝ)⁻¹) ^ 2 := by
    nlinarith [hθinv]
  have hsq : ‖z - w‖ ^ 2 ≤ ‖T.normalization z - T.normalization w‖ ^ 2 := by
    rw [norm_sq_normalization_sub, norm_sq_sub T z w]
    have hg : (0 : ℝ) ≤ ‖z - w - (inner ℝ T.direction (z - w)) • T.direction‖ ^ 2 := sq_nonneg _
    nlinarith [hθinv_sq, hg]
  have h := sq_le_sq.mp hsq
  simpa using h

/-- The normalization is `θ⁻¹`-Lipschitz. -/
lemma dist_normalization_le (hθ : 0 < θ) (hθ1 : θ ≤ 1) (T : Tube θ E) (z w : E) :
    dist (T.normalization z) (T.normalization w) ≤ (θ : ℝ)⁻¹ * dist z w := by
  rw [dist_eq_norm, dist_eq_norm]
  have hθinv : (1 : ℝ) ≤ (θ : ℝ)⁻¹ := (one_le_inv₀ (by exact_mod_cast hθ)).2 (by exact_mod_cast hθ1)
  have hθinv_sq : (1 : ℝ) ≤ ((θ : ℝ)⁻¹) ^ 2 := by
    nlinarith [hθinv]
  have hsq : ‖T.normalization z - T.normalization w‖ ^ 2 ≤ ((θ : ℝ)⁻¹ * ‖z - w‖) ^ 2 := by
    rw [norm_sq_normalization_sub, mul_pow, norm_sq_sub T z w]
    have hp : (0 : ℝ) ≤ (inner ℝ T.direction (z - w)) ^ 2 := sq_nonneg _
    have hg : (0 : ℝ) ≤ ‖z - w - (inner ℝ T.direction (z - w)) • T.direction‖ ^ 2 := sq_nonneg _
    nlinarith [hθinv_sq, hp, hg]
  have h := sq_le_sq.mp hsq
  have hnn : (0 : ℝ) ≤ (θ : ℝ)⁻¹ * ‖z - w‖ := mul_nonneg (inv_nonneg.mpr hθ.le) (norm_nonneg _)
  simpa [abs_of_nonneg hnn] using h

/-- Every point of a `θ`-tube is within `θ` of its core axis: the perpendicular component of
`z - T₀.x` has norm at most `θ`. -/
lemma perp_norm_le_of_mem_carrier (T₀ : Tube θ E) {z : E} (hz : z ∈ T₀.carrier) :
    ‖z - T₀.x - (inner ℝ T₀.direction (z - T₀.x)) • T₀.direction‖ ≤ (θ : ℝ) := by
  have hz' : z ∈ cthickening ((θ : ℝ)) (segment ℝ T₀.x T₀.y) := by
    rwa [← T₀.carrier_eq_cthickening]
  have hz'' : z ∈ ⋃ x ∈ segment ℝ T₀.x T₀.y, closedBall x (θ : ℝ) := by
    rwa [← isClosed_segment.cthickening_eq_biUnion_closedBall (by positivity : (0 : ℝ) ≤ (θ : ℝ))]
  rw [Set.mem_iUnion₂] at hz''
  rcases hz'' with ⟨c, hc, hzc⟩
  rw [Metric.mem_closedBall] at hzc
  rw [segment_eq_image_lineMap] at hc
  rcases hc with ⟨s, hs, hc_eq⟩
  let u : E := z - c
  have hc_eq' : c = T₀.x + s • T₀.direction := by
    rw [← hc_eq]
    simp [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    abel
  have hnorm_u : ‖u‖ ≤ (θ : ℝ) := by
    dsimp [u]
    rw [← dist_eq_norm]
    exact hzc
  have hinner : inner ℝ T₀.direction (z - T₀.x - s • T₀.direction) =
      inner ℝ T₀.direction (z - T₀.x) - s := by
    rw [inner_sub_right, inner_smul_right]
    have he : (inner ℝ T₀.direction T₀.direction : ℝ) = 1 := by
      rw [real_inner_self_eq_norm_sq, T₀.norm_direction]; norm_num
    rw [he]
    ring
  have hu : u - (inner ℝ T₀.direction u) • T₀.direction =
      z - T₀.x - (inner ℝ T₀.direction (z - T₀.x)) • T₀.direction := by
    dsimp [u]
    rw [hc_eq']
    calc
      (z - (T₀.x + s • T₀.direction))
            - (inner ℝ T₀.direction (z - (T₀.x + s • T₀.direction))) • T₀.direction
          = (z - T₀.x - s • T₀.direction)
              - (inner ℝ T₀.direction (z - T₀.x - s • T₀.direction)) • T₀.direction := by
            have hz' : z - (T₀.x + s • T₀.direction) = z - T₀.x - s • T₀.direction := by abel
            rw [hz']
      _ = (z - T₀.x - s • T₀.direction)
            - (inner ℝ T₀.direction (z - T₀.x) - s) • T₀.direction := by
            rw [hinner]
      _ = z - T₀.x - (inner ℝ T₀.direction (z - T₀.x)) • T₀.direction := by
            module
  calc
    ‖z - T₀.x - (inner ℝ T₀.direction (z - T₀.x)) • T₀.direction‖
        = ‖u - (inner ℝ T₀.direction u) • T₀.direction‖ := by rw [hu]
    _ ≤ ‖u‖ := norm_perp_le T₀ u
    _ ≤ (θ : ℝ) := hnorm_u

/-! ### The four items of `Tube.normalization_distortion`, one lemma each

The blueprint proves the four items of `lem:tubeNormalizationDistortion` separately, each from
the metric layer above, and the lemma itself is their conjunction.  Throughout the statements
below (the blueprint's "standing situation") `T₀` is a `θ`-tube with core `[x, y]` and unit
direction `e = T₀.direction`, `T ⊆ T₀` is a `τ`-tube with core `[a, b]` and unit direction
`f = T.direction`, `Φ = Tube.normalization T₀`, `ρ = τ / θ` and
`C = Tube.normalization.C n = 2 ^ (n + 3) ≥ 16`; for `d : E` the perpendicular component is
written `d - ⟪e, d⟫ • e`. -/

/-- **Endpoints of the inner core, and its perpendicular spread** (blueprint
`lem:tubeNormalizationEndpointsPerp`).

The endpoints of the core of `T` lie in `T` (`Tube.x_mem_carrier`, `Tube.y_mem_carrier`), hence
in `T₀`; applying `Tube.perp_norm_le_of_mem_carrier` at each and subtracting bounds the
perpendicular component of `a - b` — equivalently of the direction `f` — by `2 θ`.  This is what
makes the image core short: the component that `Φ` stretches by `θ⁻¹` is itself only `O(θ)`. -/
theorem perp_norm_core_sub_le_of_subset (T₀ : Tube θ E) (T : Tube τ E)
    (hT : T.carrier ⊆ T₀.carrier) :
    T.x ∈ T₀.carrier ∧ T.y ∈ T₀.carrier ∧
      ‖T.x - T.y - inner ℝ T₀.direction (T.x - T.y) • T₀.direction‖ ≤ 2 * (θ : ℝ) := by
  have hxT : T.x ∈ T.carrier := by
    rw [T.carrier_eq]
    exact Set.mem_iUnion₂.mpr
      ⟨T.x, left_mem_segment ℝ T.x T.y, Metric.mem_closedBall_self τ.coe_nonneg⟩
  have hyT : T.y ∈ T.carrier := by
    rw [T.carrier_eq]
    exact Set.mem_iUnion₂.mpr
      ⟨T.y, right_mem_segment ℝ T.x T.y, Metric.mem_closedBall_self τ.coe_nonneg⟩
  have hx : T.x ∈ T₀.carrier := hT hxT
  have hy : T.y ∈ T₀.carrier := hT hyT
  have hxpn : ‖T.x - T₀.x - (inner ℝ T₀.direction (T.x - T₀.x)) • T₀.direction‖ ≤ (θ : ℝ) :=
    perp_norm_le_of_mem_carrier T₀ hx
  have hypn : ‖T.y - T₀.x - (inner ℝ T₀.direction (T.y - T₀.x)) • T₀.direction‖ ≤ (θ : ℝ) :=
    perp_norm_le_of_mem_carrier T₀ hy
  refine ⟨hx, hy, ?_⟩
  calc
    ‖T.x - T.y - inner ℝ T₀.direction (T.x - T.y) • T₀.direction‖
        = ‖(T.x - T₀.x - (inner ℝ T₀.direction (T.x - T₀.x)) • T₀.direction) -
            (T.y - T₀.x - (inner ℝ T₀.direction (T.y - T₀.x)) • T₀.direction)‖ := by
          congr 1
          rw [inner_sub_right, inner_sub_right, inner_sub_right]
          module
    _ ≤ ‖T.x - T₀.x - (inner ℝ T₀.direction (T.x - T₀.x)) • T₀.direction‖ +
        ‖T.y - T₀.x - (inner ℝ T₀.direction (T.y - T₀.x)) • T₀.direction‖ := norm_sub_le _ _
    _ ≤ 2 * (θ : ℝ) := by linarith

/-- **Endpoints of the inner core, and its perpendicular spread, over a dilate** (blueprint
`lem:tubeDilateCoreEndpointsPerp`).

This is the dilate analogue of `Tube.perp_norm_core_sub_le_of_subset`: the containment
`T ⊆ T₀` is weakened to `T ⊆ c · T₀`, and the perpendicular spread `2 θ` becomes `2 c θ`.

It is a two-line corollary of an estimate that is already available:
`Kakeya.Tube.norm_chord_transverse_le_of_endpoints_mem_dilate` bounds the transverse part of
a *unit chord* of a dilate, and the core of `T` is such a chord — its endpoints lie in `T`
(`Tube.x_mem_carrier`, `Tube.y_mem_carrier`), hence in `c · T₀`, and `dist T.x T.y = 1`
(`Tube.dist_eq_one`).  No separate argument through
`Tube.abs_inner_and_perp_le_of_mem_dilate` is needed.

At `c = 1` this is `Tube.perp_norm_core_sub_le_of_subset` again.  At `c = 2` the bound is
`4 θ`, which is the tilt bound of `lem:ml1bootFineNormalizeCore` at `κ = 4`, the largest
value that lemma admits: since `‖T.x - T.y‖ = 1` (`Tube.dist_eq_one`), the left-hand side is
exactly the sine of the angle between the core of `T` and the axis `T₀.direction`, so the
statement says that a `τ`-tube inside `2 · T₀` is tilted against the axis of `T₀` by at most
`4 θ`. -/
theorem perp_norm_core_sub_le_of_subset_dilate {c : ℝ} (hc : 0 < c)
    (T₀ : Tube θ E) (T : Tube τ E) (hT : T.carrier ⊆ (Kakeya.Tube.dilate T₀ c).carrier) :
    T.x ∈ (Kakeya.Tube.dilate T₀ c).carrier ∧ T.y ∈ (Kakeya.Tube.dilate T₀ c).carrier ∧
      ‖T.x - T.y - inner ℝ T₀.direction (T.x - T.y) • T₀.direction‖ ≤ 2 * c * (θ : ℝ) :=
  ⟨hT T.x_mem_carrier, hT T.y_mem_carrier,
    Kakeya.Tube.norm_chord_transverse_le_of_endpoints_mem_dilate T₀ hc
      (by rw [dist_comm]; exact T.dist_eq_one) (hT T.y_mem_carrier) (hT T.x_mem_carrier)⟩

/-- **Length of the image core** (blueprint `lem:tubeNormalizationCoreLength`): item (i) of
`Tube.IsNormalizationDistortion`, whose two halves are the fields `one_le_dist` and
`dist_le_C`.

The lower bound is that `Φ` never shortens; the upper bound is
`Tube.perp_norm_core_sub_le_of_subset` substituted into the Pythagoras identity
`Tube.norm_sq_normalization_sub`, which gives `|a' - b'|² ≤ 5`.  The `θ⁻¹`-Lipschitz bound alone
gives only `|a' - b'| ≤ θ⁻¹`, which is unbounded as `θ → 0`. -/
theorem normalization_core_length (hθ : 0 < θ) (hθ1 : θ ≤ 1) (T₀ : Tube θ E) (T : Tube τ E)
    (hT : T.carrier ⊆ T₀.carrier) :
    1 ≤ dist (T₀.normalization T.x) (T₀.normalization T.y) ∧
      dist (T₀.normalization T.x) (T₀.normalization T.y)
        ≤ (normalization.C (Module.finrank ℝ E) : ℝ) := by
  refine ⟨?_, ?_⟩
  · -- lower bound: Φ never shortens
    have h := dist_le_dist_normalization hθ hθ1 T₀ T.x T.y
    exact le_trans (le_of_eq T.dist_eq_one.symm) h
  · -- upper bound
    rw [dist_eq_norm]
    let p : ℝ := inner ℝ T₀.direction (T.x - T.y)
    let perp : E := T.x - T.y - (inner ℝ T₀.direction (T.x - T.y)) • T₀.direction
    have hperp : ‖perp‖ ≤ 2 * (θ : ℝ) := by
      simpa [perp] using (perp_norm_core_sub_le_of_subset T₀ T hT).2.2
    have hp1 : |p| ≤ (1 : ℝ) := by
      dsimp [p]
      calc
        |inner ℝ T₀.direction (T.x - T.y)| ≤ ‖T₀.direction‖ * ‖T.x - T.y‖ :=
          abs_real_inner_le_norm _ _
        _ = 1 := by
          rw [T₀.norm_direction]
          have hxy : ‖T.x - T.y‖ = (1 : ℝ) := by rw [← dist_eq_norm, T.dist_eq_one]
          rw [hxy]
          norm_num
    have hp : p ^ 2 ≤ (1 : ℝ) := by
      have hpm : |p| ≤ |(1 : ℝ)| := by simpa using hp1
      simpa using (sq_le_sq.mpr hpm)
    have hq2 : ((θ : ℝ)⁻¹) ^ 2 * ‖perp‖ ^ 2 ≤ (4 : ℝ) := by
      have hqsq : ‖perp‖ ^ 2 ≤ (2 * (θ : ℝ)) ^ 2 := by
        apply sq_le_sq.mpr
        rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * (θ : ℝ))]
        exact hperp
      have hθinvsq : ((θ : ℝ)⁻¹) ^ 2 * (2 * (θ : ℝ)) ^ 2 = (4 : ℝ) := by
        have hθne : (θ : ℝ) ≠ 0 := by exact_mod_cast hθ.ne'
        calc
          ((θ : ℝ)⁻¹) ^ 2 * (2 * (θ : ℝ)) ^ 2 = (2 * ((θ : ℝ)⁻¹ * (θ : ℝ))) ^ 2 := by ring
          _ = (2 * 1) ^ 2 := by rw [inv_mul_cancel₀ hθne]
          _ = (4 : ℝ) := by norm_num
      have hmain : ((θ : ℝ)⁻¹) ^ 2 * ‖perp‖ ^ 2 ≤ ((θ : ℝ)⁻¹) ^ 2 * (2 * (θ : ℝ)) ^ 2 := by
        exact mul_le_mul_of_nonneg_left hqsq (sq_nonneg ((θ : ℝ)⁻¹))
      rw [hθinvsq] at hmain
      exact hmain
    have hnorm_sq : ‖T₀.normalization T.x - T₀.normalization T.y‖ ^ 2 ≤ (3 : ℝ) ^ 2 := by
      rw [Tube.norm_sq_normalization_sub T₀ T.x T.y]
      change p ^ 2 + ((θ : ℝ)⁻¹) ^ 2 * ‖perp‖ ^ 2 ≤ (3 : ℝ) ^ 2
      have hsum : p ^ 2 + ((θ : ℝ)⁻¹) ^ 2 * ‖perp‖ ^ 2 ≤ (5 : ℝ) := by nlinarith [hp, hq2]
      have h5 : (5 : ℝ) ≤ (3 : ℝ) ^ 2 := by norm_num
      nlinarith [hsum, h5]
    have hs3 := sq_le_sq.mp hnorm_sq
    have h3 : ‖T₀.normalization T.x - T₀.normalization T.y‖ ≤ (3 : ℝ) := by
      simpa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (3 : ℝ))]
        using hs3
    refine le_trans h3 ?_
    unfold normalization.C
    have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ Module.finrank ℝ E :=
      one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
    calc
      (3 : ℝ) ≤ (2 : ℝ) ^ 3 := by norm_num
      _ ≤ 1 * (2 : ℝ) ^ 3 := by norm_num
      _ ≤ (2 : ℝ) ^ Module.finrank ℝ E * (2 : ℝ) ^ 3 := by
        exact mul_le_mul_of_nonneg_right hpow (by norm_num)
      _ = (2 : ℝ) ^ (Module.finrank ℝ E + 3) := by rw [pow_add]
      _ = ((2 ^ (Module.finrank ℝ E + 3) : NNReal) : ℝ) := by norm_num

/-- **The image of the inner tube is thin about the image core** (blueprint
`lem:tubeNormalizationImageSubset`): item (ii) of `Tube.IsNormalizationDistortion`.

Only the `θ⁻¹`-Lipschitz bound `Tube.dist_normalization_le` is used, so the hypothesis
`T ⊆ T₀` is not needed here. -/
theorem normalization_image_subset_cthickening (hθ : 0 < θ) (hθ1 : θ ≤ 1) (T₀ : Tube θ E)
    (T : Tube τ E) :
    T₀.normalization '' T.carrier ⊆
      cthickening ((normalization.C (Module.finrank ℝ E) : ℝ) * ((τ : ℝ) / (θ : ℝ)))
        (segment ℝ (T₀.normalization T.x) (T₀.normalization T.y)) := by
  rintro _ ⟨z, hz, rfl⟩
  have hz' : z ∈ cthickening ((τ : ℝ)) (segment ℝ T.x T.y) := by
    rwa [← T.carrier_eq_cthickening]
  have hz'' : z ∈ ⋃ x ∈ segment ℝ T.x T.y, closedBall x (τ : ℝ) := by
    rwa [← isClosed_segment.cthickening_eq_biUnion_closedBall (by positivity : (0 : ℝ) ≤ (τ : ℝ))]
  rw [Set.mem_iUnion₂] at hz''
  rcases hz'' with ⟨w, hw, hzw⟩
  rw [Metric.mem_closedBall] at hzw
  have hseg : T₀.normalization w ∈ segment ℝ (T₀.normalization T.x) (T₀.normalization T.y) := by
    rw [← image_segment ℝ T₀.normalization T.x T.y]
    exact Set.mem_image_of_mem T₀.normalization hw
  have hdist : dist (T₀.normalization z) (T₀.normalization w) ≤
      (normalization.C (Module.finrank ℝ E) : ℝ) * ((τ : ℝ) / (θ : ℝ)) := by
    have hlip : dist (T₀.normalization z) (T₀.normalization w) ≤ ((θ : ℝ)⁻¹) * dist z w :=
      dist_normalization_le hθ hθ1 T₀ z w
    have hτ0 : (0 : ℝ) ≤ (τ : ℝ) := le_trans dist_nonneg hzw
    have hnn : (0 : ℝ) ≤ (τ : ℝ) / (θ : ℝ) := div_nonneg hτ0 hθ.le
    have hC : (1 : ℝ) ≤ (normalization.C (Module.finrank ℝ E) : ℝ) := by
      exact_mod_cast normalization.one_le_C (Module.finrank ℝ E)
    have hmid : ((θ : ℝ)⁻¹) * dist z w ≤
        (normalization.C (Module.finrank ℝ E) : ℝ) * ((τ : ℝ) / (θ : ℝ)) := by
      calc
        ((θ : ℝ)⁻¹) * dist z w ≤ ((θ : ℝ)⁻¹) * (τ : ℝ) :=
          mul_le_mul_of_nonneg_left hzw (inv_nonneg.mpr hθ.le)
        _ = (τ : ℝ) / (θ : ℝ) := by rw [div_eq_inv_mul, mul_comm]
        _ ≤ (normalization.C (Module.finrank ℝ E) : ℝ) * ((τ : ℝ) / (θ : ℝ)) :=
          le_mul_of_one_le_left hnn hC
    exact le_trans hlip hmid
  exact Metric.mem_cthickening_of_dist_le (T₀.normalization z) (T₀.normalization w)
    ((normalization.C (Module.finrank ℝ E) : ℝ) * ((τ : ℝ) / (θ : ℝ)))
    (segment ℝ (T₀.normalization T.x) (T₀.normalization T.y)) hseg hdist

/-- **Pulling a bound back through the normalization** (blueprint
`lem:tubeNormalizationPullback`).

This is the anisotropic replacement for "`Φ⁻¹` is `1`-Lipschitz": both summands of
`Tube.norm_sq_normalization_sub` are at most `r²`, so the parallel component of `z - w` is at
most `r` but the perpendicular one at most `θ r`, smaller by a factor `θ`.  The plain
non-shortening bound gives only `|z - w| ≤ r`, which is too weak for
`Tube.mem_image_normalization_of_dist_trimmed_le`; it is exactly this asymmetry that forces the
sub-segment of item (iii) to be *trimmed* rather than all of `[a', b']`. -/
theorem abs_inner_and_perp_le_of_dist_normalization_le (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (T₀ : Tube θ E) {r : ℝ} (hr : 0 ≤ r) {z w : E}
    (h : dist (T₀.normalization z) (T₀.normalization w) ≤ r) :
    |inner ℝ T₀.direction (z - w)| ≤ r ∧
      ‖z - w - inner ℝ T₀.direction (z - w) • T₀.direction‖ ≤ (θ : ℝ) * r := by
  let perp : E := z - w - inner ℝ T₀.direction (z - w) • T₀.direction
  have hterm : ‖T₀.normalization z - T₀.normalization w‖ ≤ r := by
    rwa [dist_eq_norm] at h
  have hnn : 0 ≤ ‖T₀.normalization z - T₀.normalization w‖ := norm_nonneg _
  have hterm2 : (‖T₀.normalization z - T₀.normalization w‖) ^ 2 ≤ r ^ 2 := by
    nlinarith [hterm, hr, hnn]
  rw [norm_sq_normalization_sub] at hterm2
  have hA0 : (0 : ℝ) ≤ (inner ℝ T₀.direction (z - w)) ^ 2 := sq_nonneg _
  have hC0 : (0 : ℝ) ≤ ((θ : ℝ)⁻¹) ^ 2 * ‖perp‖ ^ 2 := by
    exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hA : (inner ℝ T₀.direction (z - w)) ^ 2 ≤ r ^ 2 := by
    nlinarith [hterm2, hC0]
  have hC : ((θ : ℝ)⁻¹) ^ 2 * ‖perp‖ ^ 2 ≤ r ^ 2 := by
    nlinarith [hterm2, hA0]
  refine ⟨?_, ?_⟩
  · have h1 : |inner ℝ T₀.direction (z - w)| ≤ |r| := sq_le_sq.mp hA
    simpa [abs_of_nonneg hr] using h1
  · have hθne : (θ : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hθ
    have hθmul : (θ : ℝ) ^ 2 * ((θ : ℝ)⁻¹) ^ 2 = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hθne]; norm_num
    have hperpsq : ‖perp‖ ^ 2 ≤ ((θ : ℝ) * r) ^ 2 := by
      nlinarith [hC, hr, hθmul, sq_nonneg (θ : ℝ)]
    have hθr : 0 ≤ (θ : ℝ) * r := mul_nonneg (le_of_lt hθ) hr
    have h11 : |‖perp‖| ≤ |(θ : ℝ) * r| := sq_le_sq.mp hperpsq
    simpa [abs_of_nonneg hθr, abs_of_nonneg (norm_nonneg perp)] using h11

/-- **Sliding inside a trimmed segment** (blueprint `lem:trimmedSegmentShift`).

Writing `f = b - a`, the segment `[a, b]` trimmed by `lam` at each end is contained in `[a, b]`,
and shifting a point of the trimmed segment along `f` by at most `lam` keeps it in `[a, b]`.
No tube, no normalization and no dimension bound is involved: this is arithmetic on the segment
parameter. -/
theorem _root_.segment_add_smul_mem_of_mem_trimmed {a b : E} (hab : dist a b = 1) {lam : ℝ}
    (hlam0 : 0 ≤ lam) (hlam : lam ≤ 1 / 2) :
    segment ℝ (a + lam • (b - a)) (b - lam • (b - a)) ⊆ segment ℝ a b ∧
      ∀ w ∈ segment ℝ (a + lam • (b - a)) (b - lam • (b - a)), ∀ c : ℝ, |c| ≤ lam →
        w + c • (b - a) ∈ segment ℝ a b := by
  let f : E := b - a
  let p : E := a + lam • f
  let q : E := b - lam • f
  have hlam1 : lam ≤ (1 : ℝ) := hlam.trans (by norm_num)
  have htwo : (0 : ℝ) ≤ 1 - 2 * lam := sub_nonneg.mpr (by nlinarith [hlam])
  have hpseg : p ∈ segment ℝ a b := by
    have hpe : (1 - lam) • a + lam • b = p := by
      dsimp [p, f]
      module
    rw [segment_eq_image ℝ a b]
    exact ⟨lam, ⟨hlam0, hlam1⟩, hpe⟩
  have hqseg : q ∈ segment ℝ a b := by
    have hqe2 : (1 - (1 - lam)) • a + (1 - lam) • b = q := by
      dsimp [q, f]
      module
    rw [segment_eq_image ℝ a b]
    exact ⟨1 - lam, ⟨sub_nonneg.mpr hlam1, sub_le_self _ hlam0⟩, hqe2⟩
  constructor
  · simpa [p, q, f] using Convex.segment_subset (convex_segment (𝕜 := ℝ) a b) hpseg hqseg
  · intro w hw c hc
    have hc_low : -lam ≤ c := (abs_le.mp hc).1
    have hc_up : c ≤ lam := (abs_le.mp hc).2
    have hw' : w ∈ segment ℝ p q := by simpa [p, q, f] using hw
    rw [segment_eq_image ℝ p q] at hw'
    rcases hw' with ⟨r, hr, hw_eq⟩
    -- Both endpoints `p + c•f` and `q + c•f` remain in the segment `[a, b]`.
    have hS1 : lam + c ≤ (1 : ℝ) := by linarith
    have hS0 : (0 : ℝ) ≤ lam + c := by linarith
    have hpcf : p + c • f ∈ segment ℝ a b := by
      have hpe : (1 - (lam + c)) • a + (lam + c) • b = p + c • f := by
        dsimp [p, f]
        module
      rw [segment_eq_image ℝ a b]
      exact ⟨lam + c, ⟨hS0, hS1⟩, hpe⟩
    have hQlow : (0 : ℝ) ≤ 1 + c - lam := by linarith [htwo, hc_low]
    have hQup : 1 + c - lam ≤ 1 := by linarith [hc_up]
    have hqcf : q + c • f ∈ segment ℝ a b := by
      have hqe : (1 - (1 + c - lam)) • a + (1 + c - lam) • b = q + c • f := by
        dsimp [q, f]
        module
      rw [segment_eq_image ℝ a b]
      exact ⟨1 + c - lam, ⟨hQlow, hQup⟩, hqe⟩
    -- `w + c•f` is an affine combination of `p + c•f` and `q + c•f`, both in `[a, b]`.
    have hw_comb : (1 - r) • (p + c • f) + r • (q + c • f) = w + c • f := by
      rw [← hw_eq]
      module
    have hmem : (1 - r) • (p + c • f) + r • (q + c • f) ∈
        segment ℝ (p + c • f) (q + c • f) := by
      rw [segment_eq_image ℝ (p + c • f) (q + c • f)]
      exact ⟨r, hr, rfl⟩
    have hin : (1 - r) • (p + c • f) + r • (q + c • f) ∈ segment ℝ a b :=
      Convex.segment_subset (convex_segment (𝕜 := ℝ) a b) hpcf hqcf hmem
    rw [hw_comb] at hin
    simpa [f] using hin

/-- **The shift estimate at a free tilt bound** (blueprint `lem:tubeShiftFreeTilt`).

`Tube.dist_add_smul_direction_segment_le` with the containment `T ⊆ T₀` replaced by the one
consequence of it that the proof uses: a bound `B` on the transverse part of `T.direction`
against the axis of `T₀`.  The conclusion is the same estimate with `2 θ` replaced by `B`.

The containment enters that lemma only through
`Tube.perp_norm_core_sub_le_of_subset`, which gives `B = 2 θ`; the dilate containment
`T ⊆ c · T₀` gives `B = 2 c θ` by `Tube.perp_norm_core_sub_le_of_subset_dilate`, and every
consumer of the trimmed-core geometry is an instance of this one lemma at the appropriate `B`.
Both instances are recorded below. -/
theorem dist_add_smul_direction_segment_le_of_perp (T₀ : Tube θ E) (T : Tube τ E)
    {B : ℝ} (hperp_bnd : ‖T.direction - (inner ℝ T₀.direction T.direction : ℝ) • T₀.direction‖ ≤ B)
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam : lam ≤ 1 / 4) {w : E}
    (hw : w ∈ segment ℝ (T.x + lam • T.direction) (T.y - lam • T.direction)) {t : ℝ}
    (ht : |t| ≤ lam) :
    infDist (w + t • T₀.direction) (segment ℝ T.x T.y) ≤ B * |t| := by
  let e : E := T₀.direction
  let f : E := T.direction
  let c : ℝ := inner ℝ e f
  have hnorm_e : ‖e‖ = 1 := by dsimp [e]; exact T₀.norm_direction
  have hnorm_f : ‖f‖ = 1 := by dsimp [f]; exact T.norm_direction
  -- The perpendicular part of the ambient direction has norm at most `2θ`.
  -- The perpendicular parts of `e` w.r.t. `f` and of `f` w.r.t. `e` have the same norm.
  have h_sq_e : ‖e - c • f‖ ^ 2 = 1 - c ^ 2 := by
    rw [norm_sub_sq (𝕜 := ℝ)]
    have hcf : ‖c • f‖ ^ 2 = c ^ 2 := by
      rw [norm_smul, hnorm_f, mul_one, Real.norm_eq_abs, sq_abs]
    have hecf : inner ℝ e (c • f) = c * inner ℝ e f := by
      simpa using (inner_smul_right (x := e) (r := c) (y := f) :
        inner ℝ e (c • f) = star c * inner ℝ e f)
    rw [hcf, hecf, hnorm_e]
    dsimp [c]
    ring
  have h_sq_f : ‖f - c • e‖ ^ 2 = 1 - c ^ 2 := by
    rw [norm_sub_sq (𝕜 := ℝ)]
    have hce : ‖c • e‖ ^ 2 = c ^ 2 := by
      rw [norm_smul, hnorm_e, mul_one, Real.norm_eq_abs, sq_abs]
    have hfce : inner ℝ f (c • e) = c * inner ℝ f e := by
      simpa using (inner_smul_right (x := f) (r := c) (y := e) :
        inner ℝ f (c • e) = star c * inner ℝ f e)
    rw [hce, hfce, hnorm_f]
    dsimp [c]
    rw [real_inner_comm]
    ring
  have hperp_amb : ‖e - c • f‖ ≤ B := by
    rw [show ‖e - c • f‖ = ‖f - c • e‖ by
      exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (h_sq_e.trans h_sq_f.symm)]
    exact hperp_bnd
  -- `|c| ≤ 1`, so `|t·c| ≤ lam`.
  have hc_abs : |c| ≤ 1 := by
    dsimp [c]
    calc
      |inner ℝ e f| ≤ ‖e‖ * ‖f‖ := abs_real_inner_le_norm e f
      _ = 1 := by rw [hnorm_e, hnorm_f]; norm_num
  have hlam2 : lam ≤ 1 / 2 := by nlinarith [hlam]
  have h_tc : |t * c| ≤ lam := by
    calc
      |t * c| = |t| * |c| := by rw [abs_mul]
      _ ≤ lam * 1 := mul_le_mul ht hc_abs (abs_nonneg c) hlam0
      _ = lam := by ring
  -- The shifted point `w + (t·c) f` stays in the core segment of `T`.
  let x : E := w + (t * c) • f
  have hx : x ∈ segment ℝ T.x T.y := by
    have hx' := (segment_add_smul_mem_of_mem_trimmed (a := T.x) (b := T.y)
      T.dist_eq_one hlam0 hlam2).2 w hw (t * c) h_tc
    simpa [x, Tube.direction] using hx'
  calc
    infDist (w + t • T₀.direction) (segment ℝ T.x T.y)
        ≤ dist (w + t • T₀.direction) x := Metric.infDist_le_dist_of_mem hx
    _ = ‖(w + t • T₀.direction) - x‖ := by rw [dist_eq_norm]
    _ = |t| * ‖e - c • f‖ := by
      have hdiff : (w + t • T₀.direction) - x = t • (e - c • f) := by
        dsimp [x, c]
        module
      rw [hdiff]
      rw [norm_smul]
      simp
    _ ≤ |t| * B := mul_le_mul_of_nonneg_left hperp_amb (abs_nonneg t)
    _ = B * |t| := by ring

/-- **Shifting along the ambient axis stays near the inner core** (blueprint
`lem:tubeNormalizationAxisShift`).

Decompose the ambient direction `e` along the inner one as `e = ⟪f, e⟫ • f + h` with `h ⊥ f` and
`‖h‖ ≤ 2 θ` by `Tube.perp_norm_core_sub_le_of_subset`.  Shifting `w` by `t • e` therefore moves
it inside `[a, b]` up to the error `t • h`, of norm at most `2 θ |t|`.

This is `Tube.dist_add_smul_direction_segment_le_of_perp` at `B = 2 θ`; the containment is used
for nothing else. -/
theorem dist_add_smul_direction_segment_le (T₀ : Tube θ E) (T : Tube τ E)
    (hT : T.carrier ⊆ T₀.carrier) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam : lam ≤ 1 / 4) {w : E}
    (hw : w ∈ segment ℝ (T.x + lam • T.direction) (T.y - lam • T.direction)) {t : ℝ}
    (ht : |t| ≤ lam) :
    infDist (w + t • T₀.direction) (segment ℝ T.x T.y) ≤ 2 * (θ : ℝ) * |t| := by
  refine dist_add_smul_direction_segment_le_of_perp T₀ T ?_ hlam0 hlam hw ht
  have hcore := (perp_norm_core_sub_le_of_subset T₀ T hT).2.2
  have hrew : T.x - T.y - inner ℝ T₀.direction (T.x - T.y) • T₀.direction
      = (inner ℝ T₀.direction T.direction : ℝ) • T₀.direction - T.direction := by
    calc
      T.x - T.y - inner ℝ T₀.direction (T.x - T.y) • T₀.direction
          = -T.direction - inner ℝ T₀.direction (-T.direction) • T₀.direction := by
              rw [show T.x - T.y = -T.direction by simp [Tube.direction]]
      _ = -T.direction + (inner ℝ T₀.direction T.direction) • T₀.direction := by
              rw [inner_neg_right, neg_smul, sub_neg_eq_add]
      _ = (inner ℝ T₀.direction T.direction : ℝ) • T₀.direction - T.direction := by abel
  rw [hrew] at hcore
  rwa [← norm_neg, neg_sub] at hcore

/-- **Shifting along the ambient axis, over a dilate** (blueprint
`lem:tubeNormalizationAxisShiftDilate`).

`Tube.dist_add_smul_direction_segment_le` with the containment weakened from `T ⊆ T₀` to
`T ⊆ c · T₀`, at the cost of the tilt: the error becomes `2 c θ |t|` instead of `2 θ |t|`.

This is `Tube.dist_add_smul_direction_segment_le_of_perp` at `B = 2 c θ`, the tilt bound being
`Tube.perp_norm_core_sub_le_of_subset_dilate`.  It is the first of the trimmed-core estimates
that `Kakeya.ml1Boot.exists_fineNormalization_dilate` needs in dilated form; the containment
`T ⊆ T₀` is used for nothing in this part of the argument beyond that one bound. -/
theorem dist_add_smul_direction_segment_le_dilate {c : ℝ} (hc : 0 < c)
    (T₀ : Tube θ E) (T : Tube τ E)
    (hT : T.carrier ⊆ (Kakeya.Tube.dilate T₀ c).carrier)
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam : lam ≤ 1 / 4) {w : E}
    (hw : w ∈ segment ℝ (T.x + lam • T.direction) (T.y - lam • T.direction)) {t : ℝ}
    (ht : |t| ≤ lam) :
    infDist (w + t • T₀.direction) (segment ℝ T.x T.y) ≤ 2 * c * (θ : ℝ) * |t| := by
  refine dist_add_smul_direction_segment_le_of_perp T₀ T ?_ hlam0 hlam hw ht
  have hcore := (perp_norm_core_sub_le_of_subset_dilate hc T₀ T hT).2.2
  have hrew : T.x - T.y - inner ℝ T₀.direction (T.x - T.y) • T₀.direction
      = (inner ℝ T₀.direction T.direction : ℝ) • T₀.direction - T.direction := by
    calc
      T.x - T.y - inner ℝ T₀.direction (T.x - T.y) • T₀.direction
          = -T.direction - inner ℝ T₀.direction (-T.direction) • T₀.direction := by
              rw [show T.x - T.y = -T.direction by simp [Tube.direction]]
      _ = -T.direction + (inner ℝ T₀.direction T.direction) • T₀.direction := by
              rw [inner_neg_right, neg_smul, sub_neg_eq_add]
      _ = (inner ℝ T₀.direction T.direction : ℝ) • T₀.direction - T.direction := by abel
  rw [hrew] at hcore
  rwa [← norm_neg, neg_sub] at hcore

/-- **The trimmed image core is a long sub-segment** (blueprint
`lem:tubeNormalizationTrimmedCore`).

The trimmed segment lies in `[a, b]` and `Φ` is affine, so its image lies in `[a', b']`; and `Φ`
never shortens, so the image of the trimmed core has length at least `1 - 2 lam ≥ 7/8`.

The blueprint fixes `lam = C⁻¹ ρ` and notes once and for all that `0 ≤ lam ≤ C⁻¹ ≤ 1/16`; the
statement is recorded here for a general `lam` in that range, which is a faithful
generalisation and is what the two call sites want. -/
theorem normalization_trimmed_core (hθ : 0 < θ) (hθ1 : θ ≤ 1) (T₀ : Tube θ E) (T : Tube τ E)
    {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam : lam ≤ 1 / 16) :
    T₀.normalization (T.x + lam • T.direction)
        ∈ segment ℝ (T₀.normalization T.x) (T₀.normalization T.y) ∧
      T₀.normalization (T.y - lam • T.direction)
        ∈ segment ℝ (T₀.normalization T.x) (T₀.normalization T.y) ∧
      7 / 8 ≤ dist (T₀.normalization (T.x + lam • T.direction))
        (T₀.normalization (T.y - lam • T.direction)) := by
  let a : E := T₀.normalization T.x
  let b : E := T₀.normalization T.y
  have hlam_le_1 : lam ≤ 1 := hlam.trans (by norm_num)
  have hline1 : T.x + lam • T.direction = AffineMap.lineMap T.x T.y lam := by
    rw [Tube.direction, AffineMap.lineMap_apply_module]
    module
  have hline2 : T.y - lam • T.direction = AffineMap.lineMap T.x T.y (1 - lam) := by
    rw [Tube.direction, AffineMap.lineMap_apply_module]
    module
  have hnorm_trimx : T₀.normalization (T.x + lam • T.direction) = AffineMap.lineMap a b lam := by
    rw [hline1]
    simp [a, b]
  have hnorm_trimy :
      T₀.normalization (T.y - lam • T.direction) = AffineMap.lineMap a b (1 - lam) := by
    rw [hline2]
    simp [a, b]
  have hlen1 : 1 ≤ dist a b := by
    have h := dist_le_dist_normalization hθ hθ1 T₀ T.x T.y
    have h' : (1 : ℝ) ≤ dist (T₀.normalization T.x) (T₀.normalization T.y) := by
      rwa [T.dist_eq_one] at h
    simpa [a, b] using h'
  have hdlam : dist lam (1 - lam) = 1 - 2 * lam := by
    rw [dist_eq_norm, Real.norm_eq_abs]
    have hnonpos : lam - (1 - lam) ≤ 0 := by nlinarith [hlam]
    rw [abs_of_nonpos hnonpos]
    ring
  have hterm : 7 / 8 ≤ dist lam (1 - lam) * dist a b := by
    have h0 : 0 ≤ 1 - 2 * lam := by nlinarith [hlam]
    calc
      7 / 8 ≤ 1 - 2 * lam := by nlinarith [hlam]
      _ ≤ (1 - 2 * lam) * dist a b := by
        simpa using mul_le_mul_of_nonneg_left hlen1 h0
      _ = dist lam (1 - lam) * dist a b := by
        rw [← hdlam]
  refine ⟨?_, ?_, ?_⟩
  · rw [hnorm_trimx]
    exact lineMap_mem_segment (𝕜 := ℝ) a b ⟨hlam0, hlam_le_1⟩
  · rw [hnorm_trimy]
    exact lineMap_mem_segment (𝕜 := ℝ) a b ⟨sub_nonneg.mpr hlam_le_1, sub_le_self _ hlam0⟩
  · rw [hnorm_trimx, hnorm_trimy]
    have hdl := dist_lineMap_lineMap (𝕜 := ℝ) a b lam (1 - lam)
    rw [hdl]
    exact hterm

/-- **Pointwise containment near the trimmed image core** (blueprint
`lem:tubeNormalizationPointwiseContainment`).

Unlike `Tube.normalization_trimmed_core`, here the trimming parameter must be exactly
`lam = C⁻¹ ρ`: the proof turns `θ · lam` into `C⁻¹ τ`, and adds the two errors `2 C⁻¹ τ` (from
`Tube.dist_add_smul_direction_segment_le`) and `C⁻¹ τ` (from
`Tube.abs_inner_and_perp_le_of_dist_normalization_le`) to get `3 C⁻¹ τ ≤ τ`. -/
theorem mem_image_normalization_of_dist_trimmed_le (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hτθ : τ ≤ θ)
    (T₀ : Tube θ E) (T : Tube τ E) (hT : T.carrier ⊆ T₀.carrier) {z : E}
    (hz : infDist z (segment ℝ
        (T₀.normalization (T.x + ((normalization.C (Module.finrank ℝ E) : ℝ)⁻¹
          * ((τ : ℝ) / (θ : ℝ))) • T.direction))
        (T₀.normalization (T.y - ((normalization.C (Module.finrank ℝ E) : ℝ)⁻¹
          * ((τ : ℝ) / (θ : ℝ))) • T.direction)))
      ≤ (normalization.C (Module.finrank ℝ E) : ℝ)⁻¹ * ((τ : ℝ) / (θ : ℝ))) :
    z ∈ T₀.normalization '' T.carrier := by
  let C : ℝ := (normalization.C (Module.finrank ℝ E) : ℝ)
  let lam : ℝ := C⁻¹ * ((τ : ℝ) / (θ : ℝ))
  let p : E := T.x + lam • T.direction
  let q : E := T.y - lam • T.direction
  have htheta0 : (0 : ℝ) < (θ : ℝ) := by exact_mod_cast hθ
  have hθne : (θ : ℝ) ≠ 0 := ne_of_gt htheta0
  have htau0 : (0 : ℝ) ≤ (τ : ℝ) := by positivity
  -- bound on the normalization constant `C = 2^(n+3) ≥ 8`
  have h8leC : (8 : ℝ) ≤ C := by
    have hpown : (2 : ℝ) ^ 3 ≤ (2 : ℝ) ^ (Module.finrank ℝ E + 3) :=
      (pow_right_mono₀ (a := (2 : ℝ)) (by norm_num : (1 : ℝ) ≤ 2))
        (by omega : (3 : ℕ) ≤ Module.finrank ℝ E + 3)
    have hcoer : (2 : ℝ) ^ (Module.finrank ℝ E + 3) = C := by
      dsimp [C, normalization.C]
    calc (8 : ℝ) = (2 : ℝ) ^ 3 := by norm_num
      _ ≤ (2 : ℝ) ^ (Module.finrank ℝ E + 3) := hpown
      _ = C := hcoer
  have hCpos : (0 : ℝ) < C := by nlinarith [h8leC]
  have hCgt3 : (3 : ℝ) ≤ C := by nlinarith [h8leC]
  have hCgt4 : (4 : ℝ) ≤ C := by nlinarith [h8leC]
  have hCinv3 : (3 : ℝ) * C⁻¹ ≤ 1 := by
    have hlc : C⁻¹ ≤ (3 : ℝ)⁻¹ :=
      (inv_le_inv₀ (a := C) (b := (3 : ℝ)) hCpos (by norm_num : (0 : ℝ) < 3)).mpr hCgt3
    calc (3 : ℝ) * C⁻¹ ≤ (3 : ℝ) * (3 : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_left hlc (by norm_num : (0 : ℝ) ≤ 3)
      _ = 1 := by norm_num
  have hCinv14 : C⁻¹ ≤ 1 / 4 := by
    have hlc : C⁻¹ ≤ (4 : ℝ)⁻¹ :=
      (inv_le_inv₀ (a := C) (b := (4 : ℝ)) hCpos (by norm_num : (0 : ℝ) < 4)).mpr hCgt4
    have h4 : (4 : ℝ)⁻¹ = 1 / 4 := by norm_num
    rwa [h4] at hlc
  -- `lam = C⁻¹ · (τ/θ)` satisfies `0 ≤ lam ≤ 1/4`
  have htau_rho : (τ : ℝ) / (θ : ℝ) ≤ 1 := by
    have htc : (τ : ℝ) ≤ (θ : ℝ) := by exact_mod_cast hτθ
    rw [div_le_iff₀ htheta0]
    simpa using htc
  have hlam0 : 0 ≤ lam := by
    dsimp [lam]
    exact mul_nonneg (inv_nonneg.mpr hCpos.le) (div_nonneg htau0 htheta0.le)
  have hlam_low : lam ≤ 1 / 4 := by
    have h1 : lam ≤ C⁻¹ := by
      calc lam
          _ = C⁻¹ * ((τ : ℝ) / (θ : ℝ)) := by rfl
          _ ≤ C⁻¹ * 1 := mul_le_mul_of_nonneg_left htau_rho (inv_nonneg.mpr hCpos.le)
          _ = C⁻¹ := by ring
    exact h1.trans hCinv14
  -- the pull-back `3θ · lam = 3 C⁻¹ τ ≤ τ`
  have h3θlam : 3 * ((θ : ℝ) * lam) ≤ (τ : ℝ) := by
    have hprod : 3 * ((θ : ℝ) * lam) = (3 * C⁻¹) * (τ : ℝ) := by
      calc 3 * ((θ : ℝ) * lam)
          = 3 * ((θ : ℝ) * (C⁻¹ * ((τ : ℝ) / (θ : ℝ)))) := by dsimp [lam]
        _ = (3 * C⁻¹) * ((θ : ℝ) * ((τ : ℝ) / (θ : ℝ))) := by ring
        _ = (3 * C⁻¹) * (τ : ℝ) := by
          congr 1
          field_simp [hθne]
    calc 3 * ((θ : ℝ) * lam) = (3 * C⁻¹) * (τ : ℝ) := hprod
      _ ≤ 1 * (τ : ℝ) := mul_le_mul_of_nonneg_right hCinv3 htau0
      _ = (τ : ℝ) := by ring
  -- the hypothesis, expressed with `p` and `q`
  have hz_pq : infDist z (segment ℝ (T₀.normalization p) (T₀.normalization q)) ≤ lam := by
    simpa [p, q, lam, C] using hz
  -- `Φ` is surjective: `z = Φ z′`
  rcases T₀.normalization_surjective hθ z with ⟨z', hz'⟩
  -- a point of the trimmed image core near `z`
  have hseg_ne : (segment ℝ (T₀.normalization p) (T₀.normalization q)).Nonempty :=
    ⟨T₀.normalization p, left_mem_segment ℝ (T₀.normalization p) (T₀.normalization q)⟩
  obtain ⟨y, hy_pq, hy_eq⟩ :=
    isCompact_segment.exists_infDist_eq_dist hseg_ne z
  have hy_le : dist z y ≤ lam := by
    rw [← hy_eq]
    exact hz_pq
  have hy_im : y ∈ T₀.normalization '' segment ℝ p q := by simpa using hy_pq
  rcases hy_im with ⟨w, hw_pq, hw_eq⟩
  have hzw : dist (T₀.normalization z') (T₀.normalization w) ≤ lam := by
    rw [hz', hw_eq]
    exact hy_le
  -- anisotropic pull-back of the distance bound
  let t : ℝ := inner ℝ T₀.direction (z' - w)
  have habs := abs_inner_and_perp_le_of_dist_normalization_le hθ hθ1 T₀ (r := lam) (hr := hlam0)
    (z := z') (w := w) hzw
  have ht_le : |t| ≤ lam := by simpa [t] using habs.1
  have hperp : ‖z' - w - t • T₀.direction‖ ≤ (θ : ℝ) * lam := by simpa [t] using habs.2
  -- slide `w` along the ambient direction
  let u : E := w + t • T₀.direction
  have hshift : infDist u (segment ℝ T.x T.y) ≤ 2 * (θ : ℝ) * |t| := by
    simpa [u] using (dist_add_smul_direction_segment_le T₀ T hT hlam0 hlam_low (w := w)
      (hw := by simpa [p, q] using hw_pq) (t := t) ht_le)
  have hdistz : dist z' u ≤ (θ : ℝ) * lam := by
    have heq : z' - u = z' - w - t • T₀.direction := by simp [u]; abel
    rw [dist_eq_norm, heq]
    exact hperp
  have hz'_inf : infDist z' (segment ℝ T.x T.y) ≤ (τ : ℝ) := by
    calc
      infDist z' (segment ℝ T.x T.y)
          ≤ infDist u (segment ℝ T.x T.y) + dist z' u :=
            Metric.infDist_le_infDist_add_dist (x := z') (y := u)
              (s := segment ℝ T.x T.y)
      _ ≤ 2 * (θ : ℝ) * lam + (θ : ℝ) * lam := by
            have h2t : (0 : ℝ) ≤ 2 * (θ : ℝ) := by positivity
            have ht2 : 2 * (θ : ℝ) * |t| ≤ 2 * (θ : ℝ) * lam := mul_le_mul_of_nonneg_left ht_le h2t
            have h1 : infDist u (segment ℝ T.x T.y) ≤ 2 * (θ : ℝ) * lam :=
              le_trans hshift ht2
            linarith
      _ = 3 * ((θ : ℝ) * lam) := by ring
      _ ≤ (τ : ℝ) := h3θlam
  -- `z′ ∈ T.carrier`, whence `z = Φ z′ ∈ Φ '' T.carrier`
  have hz'_mem : z' ∈ T.carrier := by
    rw [T.carrier_eq_cthickening]
    have hne : (segment ℝ T.x T.y).Nonempty := ⟨T.x, left_mem_segment ℝ T.x T.y⟩
    obtain ⟨y₀, hy₀_mem, hy₀_eq⟩ := isCompact_segment.exists_infDist_eq_dist hne z'
    have hdist : dist z' y₀ ≤ (τ : ℝ) := by
      rw [← hy₀_eq]
      exact hz'_inf
    exact Metric.mem_cthickening_of_dist_le z' y₀ (τ : ℝ) (segment ℝ T.x T.y) hy₀_mem hdist
  exact ⟨z', hz'_mem, hz'⟩

/-- **The image of the inner tube is fat about a trimmed image core** (blueprint
`lem:tubeNormalizationSubsegment`): item (iii) of `Tube.IsNormalizationDistortion`, obtained by
combining `Tube.normalization_trimmed_core` with
`Tube.mem_image_normalization_of_dist_trimmed_le` at `lam = C⁻¹ ρ`.

The length is `7/8`, the value `Tube.normalization_trimmed_core` delivers at `lam ≤ 1/16`, and
not the weaker `C⁻¹`; unit length is false, see the field docstring of
`Tube.IsNormalizationDistortion.exists_subsegment` and blueprint
`note:tubeNormalizationNotTubes`. -/
theorem normalization_exists_subsegment (hθ : 0 < θ) (hτθ : τ ≤ θ) (hθ1 : θ ≤ 1)
    (T₀ : Tube θ E) (T : Tube τ E) (hT : T.carrier ⊆ T₀.carrier) :
    ∃ a ∈ segment ℝ (T₀.normalization T.x) (T₀.normalization T.y),
      ∃ b ∈ segment ℝ (T₀.normalization T.x) (T₀.normalization T.y),
        (7 / 8 : ℝ) ≤ dist a b ∧
          cthickening ((normalization.C (Module.finrank ℝ E) : ℝ)⁻¹ * ((τ : ℝ) / (θ : ℝ)))
            (segment ℝ a b) ⊆ T₀.normalization '' T.carrier := by
  let lam : ℝ := (normalization.C (Module.finrank ℝ E) : ℝ)⁻¹ * ((τ : ℝ) / (θ : ℝ))
  let a : E := T₀.normalization (T.x + lam • T.direction)
  let b : E := T₀.normalization (T.y - lam • T.direction)
  have hxy : T.x ≠ T.y := by
    have hd : dist T.x T.y ≠ 0 := by
      rw [T.dist_eq_one]
      norm_num
    exact dist_ne_zero.mp hd
  haveI : Nontrivial E := Nontrivial.mk ⟨T.x, T.y, hxy⟩
  have hC16 : (16 : ℝ) ≤ (normalization.C (Module.finrank ℝ E) : ℝ) := by
    have hrank : (4 : ℕ) ≤ Module.finrank ℝ E + 3 := by
      have hp : 0 < Module.finrank ℝ E := Module.finrank_pos (R := ℝ) (M := E)
      omega
    unfold normalization.C
    push_cast
    rw [show (16 : ℝ) = (2 : ℝ) ^ 4 by norm_num]
    exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hrank
  have hCinv : (normalization.C (Module.finrank ℝ E) : ℝ)⁻¹ ≤ (1 / 16 : ℝ) := by
    have hC16' : ((1 : ℝ) / 16)⁻¹ ≤ (normalization.C (Module.finrank ℝ E) : ℝ) := by
      simpa using hC16
    exact inv_le_of_inv_le₀ (by norm_num : (0 : ℝ) < 1 / 16) hC16'
  have hlam0 : 0 ≤ lam := by
    dsimp [lam]
    positivity
  have hquo : (τ : ℝ) / (θ : ℝ) ≤ 1 := by
    have hτθ : (τ : ℝ) ≤ (θ : ℝ) := by exact_mod_cast hτθ
    exact (div_le_one (by exact_mod_cast hθ)).mpr hτθ
  have hlam : lam ≤ 1 / 16 := by
    have hle : lam ≤ (normalization.C (Module.finrank ℝ E) : ℝ)⁻¹ := by
      dsimp [lam]
      calc
        (normalization.C (Module.finrank ℝ E) : ℝ)⁻¹ * ((τ : ℝ) / (θ : ℝ))
            ≤ (normalization.C (Module.finrank ℝ E) : ℝ)⁻¹ * 1 := by
              gcongr
        _ = (normalization.C (Module.finrank ℝ E) : ℝ)⁻¹ := by ring
    exact le_trans hle hCinv
  have htrim := normalization_trimmed_core hθ hθ1 T₀ T hlam0 hlam
  have h78 : (7 / 8 : ℝ) ≤ dist a b := by
    simpa [a, b] using htrim.2.2
  refine ⟨a, ?_, b, ?_, h78, ?_⟩
  · simpa [a] using htrim.1
  · simpa [b] using htrim.2.1
  · intro w hw
    change w ∈ cthickening lam (segment ℝ a b) at hw
    rw [isClosed_segment.cthickening_eq_biUnion_closedBall (by positivity : (0 : ℝ) ≤ lam)] at hw
    rw [Set.mem_iUnion₂] at hw
    rcases hw with ⟨p, hp, hwp⟩
    rw [Metric.mem_closedBall] at hwp
    have hz : infDist w (segment ℝ a b) ≤ lam := by
      exact le_trans (Metric.infDist_le_dist_of_mem hp) hwp
    exact mem_image_normalization_of_dist_trimmed_le hθ hθ1 hτθ T₀ T hT (z := w) hz

/-- **The image of the ambient tube is bounded** (blueprint
`lem:tubeNormalizationAmbientBall`): item (iv) of `Tube.IsNormalizationDistortion`.

Along the core `Φ` is the identity and fixes `T₀.x`, so the image of the core stays within `1`
of `T₀.x`; and `Φ` is `θ⁻¹`-Lipschitz while every point of `T₀` is within `θ` of its core, so
the image of `T₀` stays within a further `1`.  Hence `Φ(T₀) ⊆ B̄(x, 2) ⊆ B̄(x, C)`. -/
theorem normalization_image_ambient_subset_closedBall (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (T₀ : Tube θ E) :
    T₀.normalization '' T₀.carrier
      ⊆ closedBall T₀.x (normalization.C (Module.finrank ℝ E) : ℝ) := by
  rw [Set.image_subset_iff]
  intro z hz
  rw [Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm]
  have hθnneg : (0 : ℝ) ≤ (θ : ℝ) := by exact_mod_cast hθ.le
  have hθmod : (θ : ℝ) ≤ 1 := by exact_mod_cast hθ1
  have hzT : ‖z - T₀.x‖ ≤ 1 + (θ : ℝ) := by
    have hz' : z ∈ cthickening (θ : ℝ) (segment ℝ T₀.x T₀.y) := by
      rwa [← T₀.carrier_eq_cthickening]
    have hz'' : z ∈ ⋃ x ∈ segment ℝ T₀.x T₀.y, closedBall x (θ : ℝ) := by
      rwa [← isClosed_segment.cthickening_eq_biUnion_closedBall (by positivity : (0 : ℝ) ≤ (θ : ℝ))]
    rw [Set.mem_iUnion₂] at hz''
    rcases hz'' with ⟨w, hw, hzw⟩
    rw [Metric.mem_closedBall] at hzw
    have hwB : w ∈ closedBall T₀.x (dist T₀.x T₀.y) := segment_subset_closedBall_left T₀.x T₀.y hw
    rw [Metric.mem_closedBall] at hwB
    have hwt : dist w T₀.x ≤ (1 : ℝ) := by
      rwa [T₀.dist_eq_one] at hwB
    have hzTd : dist z T₀.x ≤ 1 + (θ : ℝ) := by
      have ht := dist_triangle z w T₀.x
      nlinarith
    rw [← dist_eq_norm]
    exact hzTd
  let p : ℝ := inner ℝ T₀.direction (z - T₀.x)
  let q : E := z - T₀.x - (inner ℝ T₀.direction (z - T₀.x)) • T₀.direction
  have hperp : ‖q‖ ≤ (θ : ℝ) := by
    simpa [q] using T₀.perp_norm_le_of_mem_carrier hz
  have hp1 : p ^ 2 ≤ ‖z - T₀.x‖ ^ 2 := by
    rw [norm_sq_sub T₀ z T₀.x]
    change p ^ 2 ≤ p ^ 2 + ‖q‖ ^ 2
    nlinarith [sq_nonneg ‖q‖]
  have hp_le : |p| ≤ 1 + (θ : ℝ) := by
    have hzt2 : ‖z - T₀.x‖ ^ 2 ≤ (1 + (θ : ℝ)) ^ 2 := by
      apply sq_le_sq.mpr
      rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (by nlinarith : (0 : ℝ) ≤ 1 + (θ : ℝ))]
      exact hzT
    simpa [abs_of_nonneg (by nlinarith : (0 : ℝ) ≤ 1 + (θ : ℝ))] using
      sq_le_sq.mp (le_trans hp1 hzt2)
  have hp2 : p ^ 2 ≤ (4 : ℝ) := by
    have hle2 : |p| ≤ (2 : ℝ) := by nlinarith [hp_le, hθmod]
    have hs2 : p ^ 2 ≤ (2 : ℝ) ^ 2 := by
      apply sq_le_sq.mpr
      simpa using hle2
    nlinarith [hs2, (by norm_num : (2 : ℝ) ^ 2 = (4 : ℝ))]
  have hq2 : ((θ : ℝ)⁻¹) ^ 2 * ‖q‖ ^ 2 ≤ (1 : ℝ) := by
    have hqsq : ‖q‖ ^ 2 ≤ (θ : ℝ) ^ 2 := by
      apply sq_le_sq.mpr
      rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hθnneg]
      exact hperp
    have hθinvsq : ((θ : ℝ)⁻¹) ^ 2 * (θ : ℝ) ^ 2 = 1 := by
      have hθne : (θ : ℝ) ≠ 0 := by exact_mod_cast hθ.ne'
      calc
        ((θ : ℝ)⁻¹) ^ 2 * (θ : ℝ) ^ 2 = (((θ : ℝ)⁻¹) * (θ : ℝ)) ^ 2 := by ring
        _ = 1 ^ 2 := by rw [inv_mul_cancel₀ hθne]
        _ = 1 := by norm_num
    have hmain : ((θ : ℝ)⁻¹) ^ 2 * ‖q‖ ^ 2 ≤ ((θ : ℝ)⁻¹) ^ 2 * (θ : ℝ) ^ 2 := by
      exact mul_le_mul_of_nonneg_left hqsq (sq_nonneg ((θ : ℝ)⁻¹))
    rw [hθinvsq] at hmain
    exact hmain
  have hqnorm : ‖T₀.normalization z - T₀.x‖ ≤ (3 : ℝ) := by
    rw [← T₀.normalization_apply_x]
    have hnorm_sq : ‖T₀.normalization z - T₀.normalization T₀.x‖ ^ 2 ≤ (3 : ℝ) ^ 2 := by
      rw [Tube.norm_sq_normalization_sub T₀ z T₀.x]
      change p ^ 2 + ((θ : ℝ)⁻¹) ^ 2 * ‖q‖ ^ 2 ≤ (3 : ℝ) ^ 2
      have hsum : p ^ 2 + ((θ : ℝ)⁻¹) ^ 2 * ‖q‖ ^ 2 ≤ (5 : ℝ) := by nlinarith [hp2, hq2]
      have h5 : (5 : ℝ) ≤ (3 : ℝ) ^ 2 := by norm_num
      nlinarith [hsum, h5]
    have hs3 := sq_le_sq.mp hnorm_sq
    simpa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (3 : ℝ))] using hs3
  refine le_trans hqnorm ?_
  unfold normalization.C
  have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ Module.finrank ℝ E :=
    one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  calc
    (3 : ℝ) ≤ (2 : ℝ) ^ 3 := by norm_num
    _ ≤ 1 * (2 : ℝ) ^ 3 := by norm_num
    _ ≤ (2 : ℝ) ^ Module.finrank ℝ E * (2 : ℝ) ^ 3 := by
      exact mul_le_mul_of_nonneg_right hpow (by norm_num)
    _ = (2 : ℝ) ^ (Module.finrank ℝ E + 3) := by rw [pow_add]
    _ = ((2 ^ (Module.finrank ℝ E + 3) : NNReal) : ℝ) := by norm_num

/-- **The normalization distorts tubes by a bounded factor** (GWZ, the estimate behind
Equation (multTildeT); blueprint `lem:tubeNormalizationDistortion`).

Let `0 < τ ≤ θ ≤ 1`, let `T₀` be a `θ`-tube and let `T ⊆ T₀` be a `τ`-tube.  Then all four
items of the blueprint lemma hold; they are packaged as the fields of
`Tube.IsNormalizationDistortion`.

The blueprint's standing assumption is `0 < τ ≤ θ ≤ 1`, but only `0 < θ` is used: it is
what makes `Tube.normalization T₀` the intended invertible map rather than the orthogonal
projection onto the core axis (recall `(0 : ℝ)⁻¹ = 0` in Lean).  It is therefore `hθ` that
is assumed here; `0 < τ` is not needed, and the degenerate case `τ = 0` is still true, with
`T.carrier` the unit core segment and `ρ = 0`.  At the call sites `0 < τ ≤ θ` is always
available, so `hθ` costs nothing. -/
theorem normalization_distortion (hθ : 0 < θ) (hτθ : τ ≤ θ) (hθ1 : θ ≤ 1)
    (T₀ : Tube θ E) (T : Tube τ E) (hT : T.carrier ⊆ T₀.carrier) :
    IsNormalizationDistortion T₀ T :=
  ⟨(normalization_core_length hθ hθ1 T₀ T hT).1,
    (normalization_core_length hθ hθ1 T₀ T hT).2,
    normalization_image_subset_cthickening hθ hθ1 T₀ T,
    normalization_exists_subsegment hθ hτθ hθ1 T₀ T hT,
    normalization_image_ambient_subset_closedBall hθ hθ1 T₀⟩

end Tube

namespace ShadedTube

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {θ τ : NNReal}

/-- **The normalized shaded body of a shaded `τ`-tube, relative to a `θ`-tube `T₀`.**

Both the carrier and the shading are pushed forward along `Tube.normalization T₀`.  A
family `𝕋 = (T i)_{i ∈ s}` with shading `Y` is normalized index by index, as
`fun i => (𝕋 i).normalizeInto T₀ hθ`; the index set is unchanged, and the result is a
family of *shaded bodies*, not of shaded tubes, since `Tube.normalization` does not
preserve the class of tubes (see `Tube.normalization_distortion`). -/
noncomputable def normalizeInto (S : ShadedTube τ E) (T₀ : Tube θ E) (hθ : 0 < θ) :
    ShadedBody E :=
  S.toShadedBody.affineImage T₀.normalization T₀.normalization_continuous
    (T₀.measurableEmbedding_normalization hθ)

@[simp]
theorem normalizeInto_carrier (S : ShadedTube τ E) (T₀ : Tube θ E) (hθ : 0 < θ) :
    (S.normalizeInto T₀ hθ).carrier = T₀.normalization '' S.carrier := rfl

@[simp]
theorem normalizeInto_shade (S : ShadedTube τ E) (T₀ : Tube θ E) (hθ : 0 < θ) :
    (S.normalizeInto T₀ hθ).shade = T₀.normalization '' S.shade := rfl

/-- **The conclusions of `ShadedTube.normalizeInto_transport`, one field per item.**

Every quantity of the argument that is a *ratio* of volumes is unchanged when a shaded
family of `τ`-tubes inside a `θ`-tube `T₀` is replaced by its normalization, because
`Tube.normalization T₀` is an affine bijection with constant Jacobian
(`Tube.volume_image_normalization`).  The fields are the items (i)–(vi) of the blueprint
lemma `lem:tubeNormalizationTransport`, with item (iv) split into its two halves
`densityIn` and `maxDensity`; they are named rather than bundled into a nested
conjunction so that a downstream argument can quote a single item.

The fullness clause `fullness` is an equality rather than the two-sided comparison of the
informal statement, and `densityIn`, `maxDensity`, `frostmanConstIn` hold for *every*
convex body `K`, not only for `K ⊆ T₀`: both strengthenings come for free from `Φ_{T₀}`
being an affine bijection with constant Jacobian.  Correspondingly the hypotheses
`τ ≤ θ` and `T i ⊆ T₀` of the blueprint are not needed here; they belong to
`Tube.normalization_distortion`. -/
structure IsNormalizeIntoTransport {ι : Type*} (s : Finset ι) (𝕋 : ι → ShadedTube τ E)
    (T₀ : Tube θ E) (hθ : 0 < θ) : Prop where
  /-- (i) Nothing is collapsed: two members of the normalized family carry the same convex
  body only if the two original members already did.  Together with the index set being
  unchanged this is the blueprint's `|𝕋̃| = |𝕋|`. -/
  card : ∀ i ∈ s, ∀ j ∈ s,
      ((𝕋 i).normalizeInto T₀ hθ).toConvexSpaceBody
        = ((𝕋 j).normalizeInto T₀ hθ).toConvexSpaceBody →
      (𝕋 i).toConvexSpaceBody = (𝕋 j).toConvexSpaceBody
  /-- (ii) Multiplicity `μ` is unchanged. -/
  multiplicity : ShadedBody.multiplicity s (fun i => (𝕋 i).normalizeInto T₀ hθ)
    = ShadedBody.multiplicity s (fun i => (𝕋 i).toShadedBody)
  /-- (iii) Fullness `λ` is unchanged. -/
  fullness : ShadedBody.fullness s (fun i => (𝕋 i).normalizeInto T₀ hθ)
    = ShadedBody.fullness s (fun i => (𝕋 i).toShadedBody)
  /-- (iv) Density `Δ(·, K)` inside a body is transported along `Φ_{T₀}`, for every convex
  body `K`. -/
  densityIn : ∀ K : ConvexSpaceBody E,
    Kakeya.densityIn s (fun i => ((𝕋 i).normalizeInto T₀ hθ).toConvexSpaceBody)
        (K.affineImage T₀.normalization T₀.normalization_continuous)
      = Kakeya.densityIn s (fun i => (𝕋 i).toConvexSpaceBody) K
  /-- (iv') Consequently `Δ_max` is unchanged. -/
  maxDensity : Kakeya.maxDensity s (fun i => ((𝕋 i).normalizeInto T₀ hθ).toConvexSpaceBody)
    = Kakeya.maxDensity s (fun i => (𝕋 i).toConvexSpaceBody)
  /-- (v) The Frostman constant `C_F(·, K)` is transported along `Φ_{T₀}`, for every convex
  body `K`. -/
  frostmanConstIn : ∀ K : ConvexSpaceBody E,
    ConvexSpaceBody.frostmanConstIn s
        (fun i => ((𝕋 i).normalizeInto T₀ hθ).toConvexSpaceBody)
        (K.affineImage T₀.normalization T₀.normalization_continuous)
      = ConvexSpaceBody.frostmanConstIn s (fun i => (𝕋 i).toConvexSpaceBody) K
  /-- (vi) Essential distinctness is preserved in both directions. -/
  essentiallyDistinct : ∀ i j, IsEssentiallyDistinct ((𝕋 i).normalizeInto T₀ hθ).carrier
      ((𝕋 j).normalizeInto T₀ hθ).carrier
    ↔ IsEssentiallyDistinct (𝕋 i).carrier (𝕋 j).carrier

/-- **Transport along the normalization** (blueprint `lem:tubeNormalizationTransport`).

All six items of the blueprint lemma hold for every shaded family of `τ`-tubes and every
`θ`-tube `T₀` with `0 < θ`; they are packaged as the fields of
`ShadedTube.IsNormalizeIntoTransport`. -/
theorem normalizeInto_transport {ι : Type*} (hθ : 0 < θ) (T₀ : Tube θ E) (s : Finset ι)
    (𝕋 : ι → ShadedTube τ E) : IsNormalizeIntoTransport s 𝕋 T₀ hθ := by
  -- `Tube.normalization T₀` is the underlying affine map of the affine *equivalence*
  -- `Tube.normalizationEquiv hθ T₀`, so all six items are instances of the general transport
  -- lemmas of `Kakeya/AffineMap.lean`, whose only input is that an affine equivalence multiplies
  -- every volume by the single nonzero finite factor `|det L.linear|`.
  obtain ⟨L, hmap⟩ : ∃ L : E ≃ᵃ[ℝ] E, L.toAffineMap = T₀.normalization :=
    ⟨Tube.normalizationEquiv hθ T₀, AffineMap.ext (Tube.normalizationEquiv_apply hθ T₀)⟩
  have hcont : Continuous L := AffineEquiv.continuous_of_finiteDimensional L
  have hemb : MeasurableEmbedding L :=
    (AffineEquiv.toContinuousAffineEquiv L).toHomeomorph.measurableEmbedding
  -- Transport of `affineImage` along `hmap`: its continuity and measurable-embedding arguments
  -- are propositions, so only the underlying affine map matters.
  have hCB : ∀ (f g : E →ᵃ[ℝ] E) (hf : Continuous f) (hg : Continuous g), f = g →
      ∀ K : ConvexSpaceBody E, K.affineImage f hf = K.affineImage g hg := by
    rintro f g hf hg rfl K; rfl
  have hSB : ∀ (f g : E →ᵃ[ℝ] E) (hf : Continuous f) (hg : Continuous g)
      (ef : MeasurableEmbedding f) (eg : MeasurableEmbedding g), f = g →
      ∀ Y : ShadedBody E, Y.affineImage f hf ef = Y.affineImage g hg eg := by
    rintro f g hf hg ef eg rfl Y; rfl
  -- The normalized family, rewritten as an affine image along `L`.
  have hfam : (fun i => (𝕋 i).normalizeInto T₀ hθ)
      = fun i => ((𝕋 i).toShadedBody).affineImage L.toAffineMap hcont hemb :=
    funext fun i => hSB _ _ _ _ _ _ hmap.symm _
  have hfamCB (i : ι) : ((𝕋 i).normalizeInto T₀ hθ).toConvexSpaceBody
      = ((𝕋 i).toConvexSpaceBody).affineImage L.toAffineMap hcont :=
    hCB T₀.normalization L.toAffineMap T₀.normalization_continuous hcont hmap.symm _
  have hK (K : ConvexSpaceBody E) :
      K.affineImage T₀.normalization T₀.normalization_continuous
        = K.affineImage L.toAffineMap hcont :=
    hCB T₀.normalization L.toAffineMap T₀.normalization_continuous hcont hmap.symm K
  -- (iv) Density, which items (iv') and (v) are built from.
  have hdensityIn (K : ConvexSpaceBody E) :
      Kakeya.densityIn s (fun i => ((𝕋 i).normalizeInto T₀ hθ).toConvexSpaceBody)
          (K.affineImage T₀.normalization T₀.normalization_continuous)
        = Kakeya.densityIn s (fun i => (𝕋 i).toConvexSpaceBody) K := by
    simp only [hfamCB, hK]
    exact Kakeya.densityIn_affineImage s (fun i => (𝕋 i).toConvexSpaceBody) K L hcont
  refine ⟨fun i _ j _ h => ConvexSpaceBody.ext
      (Set.image_injective.mpr (T₀.normalization_injective hθ)
        (congrArg (fun B : ConvexSpaceBody E => B.carrier) h)), ?_, ?_, hdensityIn, ?_, ?_, ?_⟩
  · -- (ii) Multiplicity.
    rw [hfam]; exact ShadedBody.multiplicity_affineImage s _ L hcont hemb
  · -- (iii) Fullness.
    rw [hfam]; exact ShadedBody.fullness_affineImage s _ L hcont hemb
  · -- (iv') `Δ_max`.
    simp only [hfamCB]
    exact Kakeya.maxDensity_affineImage s (fun i => (𝕋 i).toConvexSpaceBody) L hcont
  · -- (v) The Frostman constant.
    intro K
    simp only [hfamCB, hK]
    exact ConvexSpaceBody.frostmanConstIn_affineImage s _ K L hcont
  · -- (vi) Essential distinctness.
    intro i j
    rw [normalizeInto_carrier, normalizeInto_carrier, ← hmap]
    exact isEssentiallyDistinct_affineImage_iff L

end ShadedTube

namespace Tube

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {ρ : NNReal}

/-- **The dimensional prefactor `K_∗(n)`** of `Tube.comparableReplacement.C` (blueprint
`def:comparableBodiesToTubesConstant`, equation `eq:comparableBodiesToTubesConstant`):

```
K_∗(n) = 24 ω_{n-1}² C_{lem:separatedSetCardBound}(2n-1) (32 n) ^ (2n-1)
           + 6 ^ (2n) C_{lem:essDistinctTubeCount}(n).
```

The two summands are the two regimes of the packing count `Tube.essDistinctTubesInDilate`: the
first is the count in the `(2n-1)`-dimensional parameter space of `Tube.parameterMap`, the
second the crude ball count of `Tube.essDistinctTubesInFatDilate`.  Here
`ω_d = 2 ^ d · Metric.coveringNumber_mul_pow_le_volume_cthickening.C d` is the volume of the
unit ball of `ℝ ^ d`, and the blueprint's packing constant
`C_{lem:separatedSetCardBound}(d) = 2 ^ d / ω_d` is the inverse of that same abbreviation.
That both summands fit is `Tube.essDistinctTubesInDilate.constant_bounds`. -/
noncomputable abbrev comparableReplacement.Kstar (n : ℕ) : NNReal :=
  24 * (2 ^ (n - 1) * Metric.coveringNumber_mul_pow_le_volume_cthickening.C (n - 1)) ^ 2
      * (Metric.coveringNumber_mul_pow_le_volume_cthickening.C (2 * n - 1))⁻¹
      * (32 * (n : NNReal)) ^ (2 * n - 1)
    + 6 ^ (2 * n) * (card_le_of_EssDistinct.C n).toNNReal

/-- **The selection constant `C_{lem:comparableBodiesToTubes}(n, C)`** of
`Tube.exists_comparableReplacement` (blueprint `def:comparableBodiesToTubesConstant`):

```
C_{lem:comparableBodiesToTubes}(n, C) = 1 + K_∗(n) C ^ (2n) C_n ^ (4n).
```

It depends only on the ambient dimension `n`, on the comparability constant `C` of that
lemma, and on the linear dilation constant `C_n = Kakeya.Tube.tubeOverlapCoreClose.C n`; it
does *not* depend on the scale `ρ`, on the family, or on the shading.  It serves both as the
selection constant of that lemma and as the packing bound of `Tube.essDistinctTubesInDilate`.
The additive `1` makes `1 ≤ Tube.comparableReplacement.C n C` hold unconditionally.

The degrees cannot be lowered much: for `n = 3`, `C = 1`, the dilate `C_n · V` has core length
`≈ C_n` and thickness `≈ C_n ρ`, hence contains `≈ C_n` axial by `≈ C_n²` perpendicular
translates of pairwise essentially distinct `ρ`-tubes, so no bound of size `O(C_n)` holds.

Two earlier values were too small and made `Tube.essDistinctTubesInDilate` false:
`1 + 2 C · Kakeya.Tube.overlapContainment.C n`, which is linear in the dilation factor and uses
a *volume* ratio in place of the *linear* factor `C_n`, and `1 + 2 ^ (n+3) C ^ (2n) C_n ^ (2n+1)`,
whose leading factor cannot absorb the `(32 n) ^ (2n-1)` of the thin regime and whose exponent
`2n + 1` is below the degree `4n` of the fat regime (blueprint
`note:comparableBodiesToTubesConstantEnlarged`). -/
noncomputable abbrev comparableReplacement.C (n : ℕ) (C : NNReal) : NNReal :=
  1 + comparableReplacement.Kstar n * C ^ (2 * n)
    * (Kakeya.Tube.tubeOverlapCoreClose.C n).toNNReal ^ (4 * n)

theorem comparableReplacement.one_le_C (n : ℕ) (C : NNReal) :
    1 ≤ comparableReplacement.C n C := by
  unfold comparableReplacement.C
  exact le_add_of_nonneg_right (by positivity)

/-- **The numerical fit of `Tube.comparableReplacement.C`** (blueprint
`lem:essDistinctTubesInDilateConstantBounds`).

Writing
```
K(n)  = 2 ^ (2n-1) C_{lem:separatedSetCardBound}(2n-1) (c_∗/4) ^ -(2n-1) c_{lem:endpointRegionMeasure}(n),
K'(n) = 6 ^ (2n) C_{lem:essDistinctTubeCount}(n),
```
one has `K(n) + K'(n) = K_∗(n) = Tube.comparableReplacement.Kstar n`, and the two products
`K(n) C ^ (2n-1) C_n ^ (2n)` (the thin regime) and `K'(n) C ^ (2n) C_n ^ (4n)` (the fat regime)
are both at most `Tube.comparableReplacement.C n C`.  With `c_∗ = 1 / (4n)` the factor
`(c_∗/4) ^ -(2n-1)` is `(16 n) ^ (2n-1)`.

This is the single place where the explicit value of `Tube.comparableReplacement.C` is
consumed. -/
theorem essDistinctTubesInDilate.constant_bounds (n : ℕ) (C : NNReal) (hC : 1 ≤ C) :
    2 ^ (2 * n - 1) * (Metric.coveringNumber_mul_pow_le_volume_cthickening.C (2 * n - 1))⁻¹
          * (16 * (n : NNReal)) ^ (2 * n - 1) * parameterRegion.C n
          * C ^ (2 * n - 1) * (Kakeya.Tube.tubeOverlapCoreClose.C n).toNNReal ^ (2 * n)
        ≤ comparableReplacement.C n C ∧
      6 ^ (2 * n) * (card_le_of_EssDistinct.C n).toNNReal * C ^ (2 * n)
          * (Kakeya.Tube.tubeOverlapCoreClose.C n).toNNReal ^ (4 * n)
        ≤ comparableReplacement.C n C := by
  -- From the linear dilation constant `C_n > 1` (real) to `1 ≤ C_n` as an `NNReal`.
  have hCn0 : (0 : ℝ) ≤ Kakeya.Tube.tubeOverlapCoreClose.C n := le_trans (by norm_num)
    (le_of_lt (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C n))
  have hCn : (1 : NNReal) ≤ (Kakeya.Tube.tubeOverlapCoreClose.C n).toNNReal := by
    rw [← NNReal.coe_le_coe]
    rw [Real.toNNReal_of_nonneg hCn0]
    exact le_of_lt (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C n)
  -- Unfold the target constant and abbreviate `C_n = (tubeOverlapCoreClose.C n).toNNReal`.
  unfold comparableReplacement.C
  set CnNN : NNReal := (Kakeya.Tube.tubeOverlapCoreClose.C n).toNNReal with hCnNN
  -- The rate factor is monotone in both exponents.
  have hrate : C ^ (2 * n - 1) * CnNN ^ (2 * n) ≤ C ^ (2 * n) * CnNN ^ (4 * n) := by
    exact mul_le_mul (pow_le_pow_right₀ hC (by omega)) (pow_le_pow_right₀ hCn (by omega))
      (by positivity) (by positivity)
  -- `2 ^ (2n-1) * (16 n) ^ (2n-1) = (32 n) ^ (2n-1)`.
  have hmerge : 2 ^ (2 * n - 1) * (16 * (n : NNReal)) ^ (2 * n - 1)
      = (32 * (n : NNReal)) ^ (2 * n - 1) := by
    calc
      2 ^ (2 * n - 1) * (16 * (n : NNReal)) ^ (2 * n - 1)
          = (2 * (16 * (n : NNReal))) ^ (2 * n - 1) := by
            exact (mul_pow (a := (2 : NNReal)) (b := (16 * (n : NNReal)))
              (n := 2 * n - 1)).symm
      _ = (32 * (n : NNReal)) ^ (2 * n - 1) := by
            congr 1
            ring
  have hpow16 : 2 ^ (2 * n - 1) * (16 * (n : NNReal)) ^ (2 * n - 1)
      ≤ (32 * (n : NNReal)) ^ (2 * n - 1) := by
    rw [hmerge]
  -- `K_1 = parameterRegion.C n · Cvol⁻¹ · (32n)^(2n-1)` is the first summand of `K_*`.
  have hK1le : parameterRegion.C n * (Metric.coveringNumber_mul_pow_le_volume_cthickening.C
        (2 * n - 1))⁻¹ * (32 * (n : NNReal)) ^ (2 * n - 1) ≤ comparableReplacement.Kstar n := by
    unfold comparableReplacement.Kstar parameterRegion.C
    calc
      parameterRegion.C n * (Metric.coveringNumber_mul_pow_le_volume_cthickening.C
          (2 * n - 1))⁻¹ * (32 * (n : NNReal)) ^ (2 * n - 1)
          = (24 * (2 ^ (n - 1) * Metric.coveringNumber_mul_pow_le_volume_cthickening.C
              (n - 1)) ^ 2) * (Metric.coveringNumber_mul_pow_le_volume_cthickening.C
              (2 * n - 1))⁻¹ * (32 * (n : NNReal)) ^ (2 * n - 1) := by
            ring
      _ ≤ (24 * (2 ^ (n - 1) * Metric.coveringNumber_mul_pow_le_volume_cthickening.C
              (n - 1)) ^ 2) * (Metric.coveringNumber_mul_pow_le_volume_cthickening.C
              (2 * n - 1))⁻¹ * (32 * (n : NNReal)) ^ (2 * n - 1)
            + 6 ^ (2 * n) * (card_le_of_EssDistinct.C n).toNNReal := by
            exact le_add_of_nonneg_right (by positivity)
  -- The thin regime ≤ K_* · C^(2n) · Cn^(4n).
  have hthin :
      2 ^ (2 * n - 1) * (Metric.coveringNumber_mul_pow_le_volume_cthickening.C
          (2 * n - 1))⁻¹ * (16 * (n : NNReal)) ^ (2 * n - 1) * parameterRegion.C n
        * C ^ (2 * n - 1) * CnNN ^ (2 * n)
      ≤ comparableReplacement.Kstar n * C ^ (2 * n) * CnNN ^ (4 * n) := by
    calc
      2 ^ (2 * n - 1) * (Metric.coveringNumber_mul_pow_le_volume_cthickening.C
          (2 * n - 1))⁻¹ * (16 * (n : NNReal)) ^ (2 * n - 1) * parameterRegion.C n
          * C ^ (2 * n - 1) * CnNN ^ (2 * n)
          = (2 ^ (2 * n - 1) * (Metric.coveringNumber_mul_pow_le_volume_cthickening.C
              (2 * n - 1))⁻¹ * (16 * (n : NNReal)) ^ (2 * n - 1) * parameterRegion.C n)
              * (C ^ (2 * n - 1) * CnNN ^ (2 * n)) := by
            ring
      _ ≤ (2 ^ (2 * n - 1) * (Metric.coveringNumber_mul_pow_le_volume_cthickening.C
              (2 * n - 1))⁻¹ * (16 * (n : NNReal)) ^ (2 * n - 1) * parameterRegion.C n)
              * (C ^ (2 * n) * CnNN ^ (4 * n)) := by
            exact mul_le_mul_of_nonneg_left hrate
              (show 0 ≤ (2 ^ (2 * n - 1) * (Metric.coveringNumber_mul_pow_le_volume_cthickening.C
                (2 * n - 1))⁻¹ * (16 * (n : NNReal)) ^ (2 * n - 1) * parameterRegion.C n)
                from by positivity)
      _ = 2 ^ (2 * n - 1) * (Metric.coveringNumber_mul_pow_le_volume_cthickening.C
              (2 * n - 1))⁻¹ * (16 * (n : NNReal)) ^ (2 * n - 1) * parameterRegion.C n
              * C ^ (2 * n) * CnNN ^ (4 * n) := by
            ring
      _ = (2 ^ (2 * n - 1) * (16 * (n : NNReal)) ^ (2 * n - 1))
            * ((Metric.coveringNumber_mul_pow_le_volume_cthickening.C
                (2 * n - 1))⁻¹ * parameterRegion.C n * C ^ (2 * n) * CnNN ^ (4 * n)) := by
            ring
      _ ≤ (32 * (n : NNReal)) ^ (2 * n - 1)
            * ((Metric.coveringNumber_mul_pow_le_volume_cthickening.C
                (2 * n - 1))⁻¹ * parameterRegion.C n * C ^ (2 * n) * CnNN ^ (4 * n)) := by
            exact (mul_le_mul_of_nonneg_right hpow16
              (show 0 ≤ (Metric.coveringNumber_mul_pow_le_volume_cthickening.C
                (2 * n - 1))⁻¹ * parameterRegion.C n * C ^ (2 * n) * CnNN ^ (4 * n)
                from by positivity))
      _ ≤ comparableReplacement.Kstar n * C ^ (2 * n) * CnNN ^ (4 * n) := by
            calc
              (32 * (n : NNReal)) ^ (2 * n - 1)
                  * ((Metric.coveringNumber_mul_pow_le_volume_cthickening.C
                      (2 * n - 1))⁻¹ * parameterRegion.C n * C ^ (2 * n) * CnNN ^ (4 * n))
                  = (parameterRegion.C n * (Metric.coveringNumber_mul_pow_le_volume_cthickening.C
                      (2 * n - 1))⁻¹ * (32 * (n : NNReal)) ^ (2 * n - 1))
                      * (C ^ (2 * n) * CnNN ^ (4 * n)) := by
                    ring
              _ ≤ comparableReplacement.Kstar n * (C ^ (2 * n) * CnNN ^ (4 * n)) := by
                    exact mul_le_mul_of_nonneg_right hK1le
                      (show 0 ≤ C ^ (2 * n) * CnNN ^ (4 * n) from by positivity)
              _ = comparableReplacement.Kstar n * C ^ (2 * n) * CnNN ^ (4 * n) := by
                    ring
  -- The fat regime ≤ K_* · C^(2n) · Cn^(4n).
  have hfat :
      6 ^ (2 * n) * (card_le_of_EssDistinct.C n).toNNReal * C ^ (2 * n) * CnNN ^ (4 * n)
      ≤ comparableReplacement.Kstar n * C ^ (2 * n) * CnNN ^ (4 * n) := by
    have h2 : 6 ^ (2 * n) * (card_le_of_EssDistinct.C n).toNNReal ≤
        comparableReplacement.Kstar n := by
      unfold comparableReplacement.Kstar
      exact le_add_of_nonneg_left (by positivity)
    have h3 : 0 ≤ C ^ (2 * n) * CnNN ^ (4 * n) := by positivity
    calc
      6 ^ (2 * n) * (card_le_of_EssDistinct.C n).toNNReal * C ^ (2 * n) * CnNN ^ (4 * n)
          = (6 ^ (2 * n) * (card_le_of_EssDistinct.C n).toNNReal) *
              (C ^ (2 * n) * CnNN ^ (4 * n)) := by
            ring
      _ ≤ comparableReplacement.Kstar n * (C ^ (2 * n) * CnNN ^ (4 * n)) := by
            exact mul_le_mul_of_nonneg_right h2 h3
      _ = comparableReplacement.Kstar n * C ^ (2 * n) * CnNN ^ (4 * n) := by
            ring
  have hasThin :
      (2 ^ (2 * n - 1) * (Metric.coveringNumber_mul_pow_le_volume_cthickening.C
          (2 * n - 1))⁻¹ * (16 * (n : NNReal)) ^ (2 * n - 1) * parameterRegion.C n
          * C ^ (2 * n - 1) * CnNN ^ (2 * n))
      ≤ 1 + comparableReplacement.Kstar n * C ^ (2 * n) * CnNN ^ (4 * n) := by
    exact le_trans hthin (le_add_of_nonneg_left (show (0 : NNReal) ≤ 1 by norm_num))
  have hasFat :
      (6 ^ (2 * n) * (card_le_of_EssDistinct.C n).toNNReal * C ^ (2 * n) * CnNN ^ (4 * n))
      ≤ 1 + comparableReplacement.Kstar n * C ^ (2 * n) * CnNN ^ (4 * n) := by
    exact le_trans hfat (le_add_of_nonneg_left (show (0 : NNReal) ≤ 1 by norm_num))
  exact ⟨hasThin, hasFat⟩

/-- **Absorbing the thin bound into the selection constant** (blueprint
`lem:essDistinctTubesInThinDilateAbsorbed`).

The hypothesis is verbatim the conclusion of `Tube.essDistinctTubesInThinDilate`
(`Kakeya/Tube/Dilate.lean`); this lemma only identifies its right-hand side.  With
`r = c_∗ σ / 4 = σ / (16 n)` one has `r ^ -(2n-1) = (16 n) ^ (2n-1) σ ^ -(2n-1)`, and
`σ ^ -(2n-1) · σ · ρ ^ (2n-2) = (ρ / σ) ^ (2n-2) = C ^ (2n-2)` because `σ = C⁻¹ ρ`, so the
right-hand side is `K(n) C ^ (2n-1) C_n ^ (2n)` — the left-hand side of the first conjunct of
`Tube.essDistinctTubesInDilate.constant_bounds`.

It is stated for an arbitrary `N : ENNReal` rather than for a cardinality: nothing about a
family survives into the arithmetic, and the two regimes then compose by `le_trans`.  No upper
bound on `ρ` is assumed — the powers of `ρ` cancel identically — but `0 < ρ` is needed, since at
`ρ = 0` the second factor is `∞`. -/
private lemma thin_absorbed_real_eq {n : ℕ} (hn : 0 < n) {C ρ P Cn σ : ℝ}
    (hσ : σ = C⁻¹ * ρ) (hρ : 0 < ρ) (hC : 0 < C) :
    ((((1 / 4 * (1 / (4 * (n : ℝ))) * σ)⁻¹) ^ (2 * n - 1))
        * (P * C * Cn ^ (2 * n) * σ * ρ ^ (2 * n - 2)))
      = (16 * (n : ℝ)) ^ (2 * n - 1) * P * C ^ (2 * n - 1) * Cn ^ (2 * n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h1 : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
  have h2 : 2 * (m + 1) - 2 = 2 * m := by omega
  have hpu : 2 * (m + 1) = 2 * m + 2 := by omega
  rw [h1, h2, hpu]
  let a : ℝ := (m + 1 : ℕ)
  have ha0 : (0 : ℝ) < a := by dsimp [a]; exact_mod_cast Nat.succ_pos m
  have hane : a ≠ 0 := ne_of_gt ha0
  have hρ0 : ρ ≠ 0 := ne_of_gt hρ
  have hCne : C ≠ 0 := ne_of_gt hC
  have hσse : σ ≠ 0 := by rw [hσ]; exact mul_ne_zero (inv_ne_zero hCne) hρ0
  have hconst : (1 / 4 * (1 / (4 * a)))⁻¹ = 16 * a := by
    field_simp [hane]
    ring
  have hack : ((1 / 4 * (1 / (4 * a)) * σ)⁻¹) = (16 * a) * σ⁻¹ := by
    field_simp [hane, hσse]
    ring
  have hpair_σ : (σ⁻¹) ^ (2 * m + 1) * σ = (σ⁻¹) ^ (2 * m) := by
    calc
      (σ⁻¹) ^ (2 * m + 1) * σ = ((σ⁻¹) ^ (2 * m) * σ⁻¹) * σ := by rw [pow_succ]
      _ = (σ⁻¹) ^ (2 * m) * (σ⁻¹ * σ) := by ring
      _ = (σ⁻¹) ^ (2 * m) := by rw [inv_mul_cancel₀ hσse, mul_one]
  have hCrσ : ρ * σ⁻¹ = C := by
    rw [hσ]
    field_simp [hCne, hρ0]
  have hpair : (σ⁻¹) ^ (2 * m + 1) * σ * ρ ^ (2 * m) = C ^ (2 * m) := by
    calc
      (σ⁻¹) ^ (2 * m + 1) * σ * ρ ^ (2 * m) = (σ⁻¹) ^ (2 * m) * ρ ^ (2 * m) := by
        rw [hpair_σ]
      _ = (σ⁻¹ * ρ) ^ (2 * m) := by rw [mul_pow]
      _ = (ρ * σ⁻¹) ^ (2 * m) := by ring_nf
      _ = C ^ (2 * m) := by rw [hCrσ]
  have hcc : C * C ^ (2 * m) = C ^ (2 * m + 1) := by
    rw [mul_comm, ← pow_succ]
  calc
    ((1 / 4 * (1 / (4 * a)) * σ)⁻¹) ^ (2 * m + 1)
        * (P * C * Cn ^ (2 * m + 2) * σ * ρ ^ (2 * m))
        = (16 * a * σ⁻¹) ^ (2 * m + 1)
            * (P * C * Cn ^ (2 * m + 2) * σ * ρ ^ (2 * m)) := by rw [hack]
    _ = (16 * a) ^ (2 * m + 1) * (σ⁻¹) ^ (2 * m + 1)
            * (P * C * Cn ^ (2 * m + 2) * σ * ρ ^ (2 * m)) := by
            rw [mul_pow]
    _ = (16 * a) ^ (2 * m + 1) * P * C * Cn ^ (2 * m + 2)
            * ((σ⁻¹) ^ (2 * m + 1) * σ * ρ ^ (2 * m)) := by ring
    _ = (16 * a) ^ (2 * m + 1) * P * C * Cn ^ (2 * m + 2) * C ^ (2 * m) := by
            rw [hpair]
    _ = (16 * a) ^ (2 * m + 1) * P * (C * C ^ (2 * m)) * Cn ^ (2 * m + 2) := by ring
    _ = (16 * a) ^ (2 * m + 1) * P * C ^ (2 * m + 1) * Cn ^ (2 * m + 2) := by
            rw [hcc]

theorem essDistinctTubesInDilate.thin_absorbed [Nontrivial E] {C : NNReal} (hC : 1 ≤ C)
    (hρ0 : 0 < ρ) {N : ENNReal}
    (hN : N ≤ (Metric.coveringNumber_mul_pow_le_volume_cthickening.C
            (2 * Module.finrank ℝ E - 1) : ENNReal)⁻¹
          * (ENNReal.ofReal (1 / 4 * (1 / (4 * (Module.finrank ℝ E : ℝ)))
                * ((C : ℝ)⁻¹ * (ρ : ℝ))))⁻¹ ^ (2 * Module.finrank ℝ E - 1)
          * 2 ^ (2 * Module.finrank ℝ E - 1)
          * ENNReal.ofReal ((parameterRegion.C (Module.finrank ℝ E) : ℝ) * (C : ℝ)
              * Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E)
                  ^ (2 * Module.finrank ℝ E)
              * ((C : ℝ)⁻¹ * (ρ : ℝ)) * (ρ : ℝ) ^ (2 * Module.finrank ℝ E - 2))) :
    N ≤ (comparableReplacement.C (Module.finrank ℝ E) C : ENNReal) := by
  set n : ℕ := Module.finrank ℝ E
  have hn : 0 < n := by simpa [n] using Module.finrank_pos (R := ℝ) (M := E)
  let σ : ℝ := (C : ℝ)⁻¹ * (ρ : ℝ)
  let c : ℝ := 1 / 4 * (1 / (4 * (n : ℝ))) * σ
  let P : ℝ := (parameterRegion.C n : ℝ)
  let Cn : ℝ := Kakeya.Tube.tubeOverlapCoreClose.C n
  let CnNN : NNReal := (Kakeya.Tube.tubeOverlapCoreClose.C n).toNNReal
  let Ccover : NNReal := Metric.coveringNumber_mul_pow_le_volume_cthickening.C (2 * n - 1)
  let B : ℝ := P * (C : ℝ) * Cn ^ (2 * n) * σ * (ρ : ℝ) ^ (2 * n - 2)
  let rp : ℝ := (Ccover : ℝ)⁻¹ * 2 ^ (2 * n - 1) * (c⁻¹) ^ (2 * n - 1) * B
  let K : NNReal := 2 ^ (2 * n - 1) * Ccover⁻¹ * (16 * (n : NNReal)) ^ (2 * n - 1)
      * parameterRegion.C n * C ^ (2 * n - 1) * CnNN ^ (2 * n)
  have hC0 : (0 : ℝ) < (C : ℝ) := by
    exact lt_of_lt_of_le (by norm_num) (by exact_mod_cast hC : (1 : ℝ) ≤ (C : ℝ))
  have hρR : (0 : ℝ) < (ρ : ℝ) := by exact_mod_cast hρ0
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hCn0 : (0 : ℝ) ≤ Cn := by
    dsimp [Cn]
    exact le_trans (by norm_num) (le_of_lt (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C n))
  have hcover_pos : 0 < Ccover := Metric.coveringNumber_mul_pow_le_volume_cthickening.C_pos (2 * n - 1)
  have hcoverR : (0 : ℝ) < (Ccover : ℝ) := by exact_mod_cast hcover_pos
  have hcover_ne : Ccover ≠ 0 := ne_of_gt hcover_pos
  have hσpos : 0 < σ := by dsimp [σ]; positivity
  have hc_pos : 0 < c := by dsimp [c]; positivity
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hmid : (c⁻¹) ^ (2 * n - 1) * B = (16 * (n : ℝ)) ^ (2 * n - 1) * P * (C : ℝ) ^ (2 * n - 1) * Cn ^ (2 * n) := by
    simpa [c, B, P, σ] using
      (thin_absorbed_real_eq (n := n) (hn := hn) (C := (C : ℝ)) (ρ := (ρ : ℝ)) (P := P) (Cn := Cn)
        (σ := σ) (hσ := rfl) (hρ := hρR) (hC := hC0))
  have hKreal : (K : ℝ) = (Ccover : ℝ)⁻¹ * 2 ^ (2 * n - 1) * (16 * (n : ℝ)) ^ (2 * n - 1)
      * P * (C : ℝ) ^ (2 * n - 1) * Cn ^ (2 * n) := by
    have hCnm_ne : Metric.coveringNumber_mul_pow_le_volume_cthickening.C (n - 1) ≠ 0 :=
      ne_of_gt (Metric.coveringNumber_mul_pow_le_volume_cthickening.C_pos (n - 1))
    have htubeR : (0 : ℝ) < Kakeya.Tube.tubeOverlapCoreClose.C n :=
      lt_of_lt_of_le (by norm_num : (0 : ℝ) < (1 : ℝ)) (le_of_lt (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C n))
    have htube_ne : Kakeya.Tube.tubeOverlapCoreClose.C n ≠ 0 := ne_of_gt htubeR
    have hCnn0 : (C : NNReal) ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : NNReal) < (1 : NNReal)) hC)
    simp [K, CnNN, Cn, P, hCn0, hCnm_ne, htube_ne, hCnn0]
    ring
    exact Or.inl trivial
  have hreal : rp = (K : ℝ) := by
    unfold rp
    calc
      (Ccover : ℝ)⁻¹ * 2 ^ (2 * n - 1) * (c⁻¹) ^ (2 * n - 1) * B
          = (Ccover : ℝ)⁻¹ * 2 ^ (2 * n - 1) * ((c⁻¹) ^ (2 * n - 1) * B) := by ring
      _ = (Ccover : ℝ)⁻¹ * 2 ^ (2 * n - 1)
            * ((16 * (n : ℝ)) ^ (2 * n - 1) * P * (C : ℝ) ^ (2 * n - 1) * Cn ^ (2 * n)) := by
            rw [hmid]
      _ = (K : ℝ) := by rw [hKreal]; ring
  have hcovi : (Ccover : ENNReal)⁻¹ = ENNReal.ofReal ((Ccover : ℝ)⁻¹) := by
    rw [← ENNReal.ofReal_coe_nnreal]
    rw [← ENNReal.ofReal_inv_of_pos hcoverR]
  have hcinv : (ENNReal.ofReal c)⁻¹ ^ (2 * n - 1) = ENNReal.ofReal ((c⁻¹) ^ (2 * n - 1)) := by
    rw [← ENNReal.ofReal_inv_of_pos hc_pos]
    rw [← ENNReal.ofReal_pow (show (0 : ℝ) ≤ c⁻¹ by positivity)]
  have h2e : (2 : ENNReal) ^ (2 * n - 1) = ENNReal.ofReal (2 ^ (2 * n - 1)) := by
    rw [show (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) by simp]
    rw [← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2)]
  have hprod1 : ENNReal.ofReal ((Ccover : ℝ)⁻¹) * ENNReal.ofReal ((c⁻¹) ^ (2 * n - 1)) =
      ENNReal.ofReal ((Ccover : ℝ)⁻¹ * ((c⁻¹) ^ (2 * n - 1))) :=
    (ENNReal.ofReal_mul (p := (Ccover : ℝ)⁻¹) (q := (c⁻¹) ^ (2 * n - 1))
      (by positivity : (0 : ℝ) ≤ (Ccover : ℝ)⁻¹)).symm
  have hprod2 : ENNReal.ofReal ((Ccover : ℝ)⁻¹ * ((c⁻¹) ^ (2 * n - 1))) *
        ENNReal.ofReal (2 ^ (2 * n - 1)) =
      ENNReal.ofReal ((Ccover : ℝ)⁻¹ * ((c⁻¹) ^ (2 * n - 1)) * 2 ^ (2 * n - 1)) :=
    (ENNReal.ofReal_mul (p := (Ccover : ℝ)⁻¹ * ((c⁻¹) ^ (2 * n - 1))) (q := 2 ^ (2 * n - 1))
      (by positivity : (0 : ℝ) ≤ (Ccover : ℝ)⁻¹ * ((c⁻¹) ^ (2 * n - 1)))).symm
  have hprod3 : ENNReal.ofReal ((Ccover : ℝ)⁻¹ * ((c⁻¹) ^ (2 * n - 1)) * 2 ^ (2 * n - 1)) *
        ENNReal.ofReal B =
      ENNReal.ofReal ((Ccover : ℝ)⁻¹ * ((c⁻¹) ^ (2 * n - 1)) * 2 ^ (2 * n - 1) * B) :=
    (ENNReal.ofReal_mul (p := (Ccover : ℝ)⁻¹ * ((c⁻¹) ^ (2 * n - 1)) * 2 ^ (2 * n - 1)) (q := B)
      (by positivity : (0 : ℝ) ≤ (Ccover : ℝ)⁻¹ * ((c⁻¹) ^ (2 * n - 1)) * 2 ^ (2 * n - 1))).symm
  have hR : (Ccover : ENNReal)⁻¹ * (ENNReal.ofReal c)⁻¹ ^ (2 * n - 1)
        * 2 ^ (2 * n - 1) * ENNReal.ofReal B = (K : ENNReal) := by
    calc
      (Ccover : ENNReal)⁻¹ * (ENNReal.ofReal c)⁻¹ ^ (2 * n - 1) * 2 ^ (2 * n - 1)
            * ENNReal.ofReal B
          = ENNReal.ofReal ((Ccover : ℝ)⁻¹) * ENNReal.ofReal ((c⁻¹) ^ (2 * n - 1))
              * ENNReal.ofReal (2 ^ (2 * n - 1)) * ENNReal.ofReal B := by
                rw [hcovi, hcinv, h2e]
      _ = ENNReal.ofReal ((Ccover : ℝ)⁻¹ * ((c⁻¹) ^ (2 * n - 1)) * 2 ^ (2 * n - 1) * B) := by
            rw [hprod1, hprod2, hprod3]
      _ = ENNReal.ofReal rp := by
            congr 1
            dsimp [rp]
            ring
      _ = ENNReal.ofReal (K : ℝ) := by rw [hreal]
      _ = (K : ENNReal) := by exact (ENNReal.ofReal_coe_nnreal : ENNReal.ofReal (K : ℝ) = (K : ENNReal))
  have hnn : (K : NNReal) ≤ comparableReplacement.C n C := by
    simpa [K, Ccover, CnNN] using (essDistinctTubesInDilate.constant_bounds n C hC).1
  refine le_trans hN ?_
  rw [hR]
  exact ENNReal.coe_le_coe.2 hnn

/-- **Absorbing the fat bound into the selection constant** (blueprint
`lem:essDistinctTubesInFatDilateAbsorbed`).

The hypothesis is verbatim the conclusion of `Tube.essDistinctTubesInFatDilate`
(`Kakeya/Tube/Dilate.lean`).  By `mul_pow` its right-hand side is `K'(n) C ^ (2n) C_n ^ (4n)`
with `K'(n) = 6 ^ (2n) C_{lem:essDistinctTubeCount}(n)`, the left-hand side of the second
conjunct of `Tube.essDistinctTubesInDilate.constant_bounds`.  The only real work is the change
of ambient ordered semiring: the fat regime is counted in `ℝ` whereas the thin regime, and the
conclusion of `Tube.essDistinctTubesInDilate`, live in `[0, ∞]`. -/
theorem essDistinctTubesInDilate.fat_absorbed {C : NNReal} (hC : 1 ≤ C) {m : ℕ}
    (hm : (m : ℝ) ≤ card_le_of_EssDistinct.C (Module.finrank ℝ E)
      * (6 * (C : ℝ) * Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) ^ 2)
        ^ (2 * Module.finrank ℝ E)) :
    (m : ENNReal) ≤ (comparableReplacement.C (Module.finrank ℝ E) C : ENNReal) := by
  set n : ℕ := Module.finrank ℝ E
  let Cn : ℝ := Kakeya.Tube.tubeOverlapCoreClose.C n
  let CnNN : NNReal := (Kakeya.Tube.tubeOverlapCoreClose.C n).toNNReal
  let X : ℝ := (6 : ℝ) ^ (2 * n) * card_le_of_EssDistinct.C n
      * (C : ℝ) ^ (2 * n) * Cn ^ (4 * n)
  let C' : NNReal := 6 ^ (2 * n) * (card_le_of_EssDistinct.C n).toNNReal
      * C ^ (2 * n) * CnNN ^ (4 * n)
  have hcard0 : (0 : ℝ) ≤ card_le_of_EssDistinct.C n :=
    le_of_lt (card_le_of_EssDistinct.C_pos)
  have hCn0 : (0 : ℝ) ≤ Cn := by
    dsimp [Cn]
    exact le_trans (by norm_num) (le_of_lt (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C n))
  have hcardNN : ((card_le_of_EssDistinct.C n).toNNReal : ℝ) = card_le_of_EssDistinct.C n := by
    simp [Real.toNNReal_of_nonneg hcard0]
  have hCnNN : (CnNN : ℝ) = Cn := by
    simp [CnNN, Cn, Real.toNNReal_of_nonneg hCn0]
  have hcb : 6 ^ (2 * n) * (card_le_of_EssDistinct.C n).toNNReal * C ^ (2 * n)
        * CnNN ^ (4 * n) ≤ comparableReplacement.C n C := by
    simpa [CnNN] using (essDistinctTubesInDilate.constant_bounds n C hC).2
  have hcb' : (C' : ENNReal) ≤ (comparableReplacement.C n C : ENNReal) := by
    exact (ENNReal.coe_le_coe).mpr (by simpa [C', CnNN] using hcb)
  have hXreal : (C' : ℝ) = X := by
    norm_num [C', CnNN, X, Cn, Real.toNNReal_of_nonneg hCn0, Real.toNNReal_of_nonneg hcard0]
  have hexp : (Cn ^ 2) ^ (2 * n) = Cn ^ (4 * n) := by
    calc
      (Cn ^ 2) ^ (2 * n) = Cn ^ (2 * (2 * n)) := (pow_mul Cn 2 (2 * n)).symm
      _ = Cn ^ (4 * n) := by congr 1; omega
  have hRHSpow : ((6 : ℝ) * (C : ℝ) * Cn ^ 2) ^ (2 * n)
      = (6 : ℝ) ^ (2 * n) * (C : ℝ) ^ (2 * n) * Cn ^ (4 * n) := by
    calc
      ((6 : ℝ) * (C : ℝ) * Cn ^ 2) ^ (2 * n)
          = (6 : ℝ) ^ (2 * n) * (C : ℝ) ^ (2 * n) * (Cn ^ 2) ^ (2 * n) := by
            rw [mul_pow, mul_pow]
      _ = (6 : ℝ) ^ (2 * n) * (C : ℝ) ^ (2 * n) * Cn ^ (4 * n) := by
            rw [hexp]
  have hRHS : card_le_of_EssDistinct.C n * ((6 : ℝ) * (C : ℝ) * Cn ^ 2) ^ (2 * n) = X := by
    rw [hRHSpow]
    dsimp [X]
    ring
  have hmR : (m : ℝ) ≤ X := by
    have hmCn : (m : ℝ) ≤ card_le_of_EssDistinct.C n * ((6 : ℝ) * (C : ℝ) * Cn ^ 2) ^ (2 * n) := by
      simpa [Cn] using hm
    rwa [hRHS] at hmCn
  by_cases hm0 : m = 0
  · subst m
    simp
  · have hXnn : 0 ≤ X := by
      rw [← hXreal]
      exact NNReal.coe_nonneg C'
    have hmc : (m : ENNReal) ≤ ENNReal.ofReal X :=
      (ENNReal.natCast_le_ofReal hm0).mpr hmR
    have hof : ENNReal.ofReal X = (C' : ENNReal) := by
      rw [ENNReal.ofReal_eq_coe_nnreal hXnn]
      congr 1
      exact Subtype.ext hXreal.symm
    calc
      (m : ENNReal) ≤ ENNReal.ofReal X := hmc
      _ = (C' : ENNReal) := hof
      _ ≤ (comparableReplacement.C n C : ENNReal) := hcb'

/-- **Essentially distinct thin tubes trapped in a dilate of a fat tube** (blueprint
`lem:essDistinctTubesInDilate`).

Let `V` be a `ρ`-tube and let `C_n = C_{lem:tubeOverlapCoreClose}` be the dilation factor
produced by `Kakeya.Tube.tubeOverlapCoreClose`.  A family of pairwise essentially distinct
`C⁻¹ ρ`-tubes all contained in the dilate `C_n · V` has at most
`C_{lem:comparableBodiesToTubes}(n, C)` members, a bound independent of `ρ`, of `V` and of the
family.

This is the packing input of `Tube.exists_comparableReplacement`, and the only place where the
inner tubes of that lemma are used.  The dilate is written as `Kakeya.Tube.dilate V C_n`, the
concrete convex body that `Kakeya.Tube.overlapContainment` produces, rather than as an abstract
body of comparable volume: the counting argument needs its shape, not only its volume.

The proof is the case split of blueprint `note:essDistinctTubesInDilateRegimes` on the size of
`ρ` against `1 / (4 C_n)`, each branch being one count followed by one absorption:
`Tube.essDistinctTubesInThinDilate` then `Tube.essDistinctTubesInDilate.thin_absorbed` in the
thin branch, and `Tube.essDistinctTubesInFatDilate` then
`Tube.essDistinctTubesInDilate.fat_absorbed` in the fat one. -/
theorem essDistinctTubesInDilate {ι : Type*} [Nontrivial E] {C : NNReal} (hC : 1 ≤ C)
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (V : Tube ρ E) (a : Finset ι) (U : ι → Tube (C⁻¹ * ρ) E)
    (hUED : (↑a : Set ι).Pairwise fun i j => IsEssentiallyDistinct (U i).carrier (U j).carrier)
    (hUV : ∀ j ∈ a, (U j).carrier
      ⊆ (Kakeya.Tube.dilate V
          (Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E))).carrier) :
    (a.card : ENNReal) ≤ (comparableReplacement.C (Module.finrank ℝ E) C : ENNReal) := by
  by_cases h : (ρ : ℝ) ≤ 1 / (4 * Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E))
  · exact essDistinctTubesInDilate.thin_absorbed hC hρ0
      (Tube.essDistinctTubesInThinDilate hC hρ0 h V a U hUED hUV)
  · have hlt : 1 / (4 * Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E)) < (ρ : ℝ) :=
      lt_of_not_ge h
    exact essDistinctTubesInDilate.fat_absorbed hC
      (Tube.essDistinctTubesInFatDilate hC hlt hρ1 V a U hUED hUV)

/-! ### Transporting the shaded-family quantities to comparable bodies

The five items of `Tube.IsComparableReplacement` split into three that need only the *one-sided*
comparability `W_i ⊆ V_i ⊆ K`, `|V_i| ≤ C |W_i|` (blueprint `lem:comparableTransportOneSided`)
and two that need the inner tubes and the two-sided shade bounds.  The one-sided half is
isolated because `ConvexSpaceBody.frostmanConstIn_ge_of_comparable` also consumes it. -/

/-- **Multiplicity depends only on the shading** (blueprint `lem:comparableMultiplicity`).

`ShadedBody.multiplicity` is built from the shades and their union alone, so this is a
congruence rather than an estimate. -/
theorem multiplicity_congr_of_shading_eq {ι : Type*} (s : Finset ι) (𝕎 𝕍 : ι → ShadedBody E)
    (hshade : ∀ i ∈ s, (𝕍 i).shade = (𝕎 i).shade) :
    ShadedBody.multiplicity s 𝕍 = ShadedBody.multiplicity s 𝕎 := by
  change (∑ i ∈ s, volume (𝕍 i).shade) / volume (⋃ i ∈ s, (𝕍 i).shade) =
    (∑ i ∈ s, volume (𝕎 i).shade) / volume (⋃ i ∈ s, (𝕎 i).shade)
  congr 1
  · exact Finset.sum_congr rfl (fun i hi => by rw [hshade i hi])
  · congr 1
    exact iUnion_congr (fun i => iUnion_congr (fun hi => by rw [hshade i hi]))

/-- **Fullness drops by at most the comparability constant** (blueprint
`lem:comparableFullness`).  Summing `|V_i| ≤ C |W_i|` over `i ∈ s` and dividing the common
numerator `∑ |Z_i|` by the two denominators. -/
theorem le_fullness_of_volume_le {ι : Type*} {C : NNReal} (hC : 1 ≤ C) (s : Finset ι)
    (𝕎 𝕍 : ι → ShadedBody E) (hshade : ∀ i ∈ s, (𝕍 i).shade = (𝕎 i).shade)
    (hvol : ∀ i ∈ s, volume (𝕍 i).carrier ≤ (C : ENNReal) * volume (𝕎 i).carrier) :
    C⁻¹ * ShadedBody.fullness s 𝕎 ≤ ShadedBody.fullness s 𝕍 := by
  have hCpos : 0 < C := lt_of_lt_of_le (zero_lt_one : (0 : NNReal) < 1) hC
  have hN : (∑ i ∈ s, volume (𝕍 i).shade) = ∑ i ∈ s, volume (𝕎 i).shade := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    simp [hshade i hi]
  have hVden : (∑ i ∈ s, volume (𝕍 i).carrier) ≤ (C : ENNReal) * ∑ i ∈ s, volume (𝕎 i).carrier := by
    calc
      ∑ i ∈ s, volume (𝕍 i).carrier ≤ ∑ i ∈ s, (C : ENNReal) * volume (𝕎 i).carrier :=
            Finset.sum_le_sum hvol
      _ = (C : ENNReal) * ∑ i ∈ s, volume (𝕎 i).carrier := by rw [Finset.mul_sum]
  apply ENNReal.coe_le_coe.1
  rw [ENNReal.coe_mul, ENNReal.coe_inv (ne_of_gt hCpos)]
  rw [ShadedBody.coe_fullness, ShadedBody.coe_fullness]
  unfold ShadedBody.fullness'
  rw [hN]
  calc
    (C : ENNReal)⁻¹ * ((∑ i ∈ s, volume (𝕎 i).shade) / (∑ i ∈ s, volume (𝕎 i).carrier))
        = (∑ i ∈ s, volume (𝕎 i).shade) / ((C : ENNReal) * ∑ i ∈ s, volume (𝕎 i).carrier) := by
          change (C : ENNReal)⁻¹ *
              ((∑ i ∈ s, volume (𝕎 i).shade) * (∑ i ∈ s, volume (𝕎 i).carrier)⁻¹)
              = (∑ i ∈ s, volume (𝕎 i).shade) * ((C : ENNReal) * ∑ i ∈ s, volume (𝕎 i).carrier)⁻¹
          rw [ENNReal.mul_inv (a := (C : ENNReal)) (b := ∑ i ∈ s, volume (𝕎 i).carrier)
            (ha := Or.inl (ENNReal.coe_ne_zero.mpr (ne_of_gt hCpos)))
            (hb := Or.inl ENNReal.coe_ne_top)]
          ac_rfl
    _ ≤ (∑ i ∈ s, volume (𝕎 i).shade) / (∑ i ∈ s, volume (𝕍 i).carrier) := by
          exact ENNReal.div_le_div_left hVden (∑ i ∈ s, volume (𝕎 i).shade)

/-- **Comparable bodies: the density in a test body grows by at most `C`** (blueprint
`lem:comparableDensityUpper`).  If `V_i ⊆ K''` then `W_i ⊆ K''`, so `𝕍[K''] ⊆ 𝕎[K'']`; enlarging
the index set and using `|V_i| ≤ C |W_i|` gives the bound. -/
theorem densityIn_le_of_comparable {ι : Type*} {C : NNReal} (hC : 1 ≤ C) (s : Finset ι)
    (𝕎 𝕍 : ι → ConvexSpaceBody E) (hsub : ∀ i ∈ s, 𝕎 i ≤ 𝕍 i)
    (hvol : ∀ i ∈ s, volume (𝕍 i).carrier ≤ (C : ENNReal) * volume (𝕎 i).carrier)
    (K : ConvexSpaceBody E) :
    Kakeya.densityIn s 𝕍 K ≤ (C : ENNReal) * Kakeya.densityIn s 𝕎 K := by
  classical
  have hsubK : s.filter (fun i => 𝕍 i ≤ K) ⊆ s.filter (fun i => 𝕎 i ≤ K) := by
    intro i hi
    have hi' := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨hi'.1, le_trans (hsub i hi'.1) hi'.2⟩
  have hmain :
      (∑ i ∈ s with 𝕍 i ≤ K, volume (𝕍 i).carrier)
          ≤ (C : ENNReal) * (∑ i ∈ s with 𝕎 i ≤ K, volume (𝕎 i).carrier) := by
    calc
      (∑ i ∈ s with 𝕍 i ≤ K, volume (𝕍 i).carrier)
          ≤ (∑ i ∈ s with 𝕍 i ≤ K, (C : ENNReal) * volume (𝕎 i).carrier) := by
            refine Finset.sum_le_sum ?_
            intro i hi
            exact hvol i (Finset.mem_filter.mp hi).1
      _ = (C : ENNReal) * (∑ i ∈ s with 𝕍 i ≤ K, volume (𝕎 i).carrier) := by
            rw [← Finset.mul_sum]
      _ ≤ (C : ENNReal) * (∑ i ∈ s with 𝕎 i ≤ K, volume (𝕎 i).carrier) := by
            gcongr
  calc
    Kakeya.densityIn s 𝕍 K
        = (∑ i ∈ s with 𝕍 i ≤ K, volume (𝕍 i).carrier) / volume K.carrier := by
          rfl
    _ ≤ ((C : ENNReal) * (∑ i ∈ s with 𝕎 i ≤ K, volume (𝕎 i).carrier)) / volume K.carrier := by
          exact ENNReal.div_le_div_right hmain (volume K.carrier)
    _ = (C : ENNReal) * ((∑ i ∈ s with 𝕎 i ≤ K, volume (𝕎 i).carrier) / volume K.carrier) := by
          rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc]
    _ = (C : ENNReal) * Kakeya.densityIn s 𝕎 K := by
          rfl

/-- **Comparable bodies: the density in the ambient body does not drop** (blueprint
`lem:comparableDensityAmbient`).  Every `W_i` and every `V_i` lies in `K`, so both families
index all of `s` there, and `|W_i| ≤ |V_i|`. -/
theorem densityIn_ambient_le_of_comparable {ι : Type*} (s : Finset ι)
    (𝕎 𝕍 : ι → ConvexSpaceBody E) (K : ConvexSpaceBody E) (hsub : ∀ i ∈ s, 𝕎 i ≤ 𝕍 i)
    (hVK : ∀ i ∈ s, 𝕍 i ≤ K) :
    Kakeya.densityIn s 𝕎 K ≤ Kakeya.densityIn s 𝕍 K := by
  have hWK : ∀ i ∈ s, 𝕎 i ≤ K := fun i hi => le_trans (hsub i hi) (hVK i hi)
  rw [Kakeya.densityIn_of_all_le hWK, Kakeya.densityIn_of_all_le hVK]
  gcongr with i hi
  exact SetLike.coe_subset_coe.mpr (hsub i hi)

/-- **Comparable bodies: the Frostman constant grows by at most `C`** (blueprint
`lem:comparableFrostmanConst`).  Chaining `Tube.densityIn_le_of_comparable`, the Frostman
property of `𝕎` and `Tube.densityIn_ambient_le_of_comparable` shows that `𝕍` is
`C · C_F(𝕎, K)`-Frostman in `K`. -/
theorem frostmanConstIn_le_of_comparable {ι : Type*} {C : NNReal} (hC : 1 ≤ C) (s : Finset ι)
    (𝕎 𝕍 : ι → ConvexSpaceBody E) (K : ConvexSpaceBody E) (hsub : ∀ i ∈ s, 𝕎 i ≤ 𝕍 i)
    (hVK : ∀ i ∈ s, 𝕍 i ≤ K)
    (hvol : ∀ i ∈ s, volume (𝕍 i).carrier ≤ (C : ENNReal) * volume (𝕎 i).carrier) :
    ConvexSpaceBody.frostmanConstIn s 𝕍 K
      ≤ (C : ENNReal) * ConvexSpaceBody.frostmanConstIn s 𝕎 K := by
  have h_isFrostmanW : ConvexSpaceBody.IsFrostmanIn s 𝕎 K
      (ConvexSpaceBody.frostmanConstIn s 𝕎 K) :=
    ConvexSpaceBody.isFrostmanIn_frostmanConstIn s 𝕎 K
  have h_isFrostmanV : ConvexSpaceBody.IsFrostmanIn s 𝕍 K
      ((C : ENNReal) * ConvexSpaceBody.frostmanConstIn s 𝕎 K) := by
    intro K' hK'
    calc
      Kakeya.densityIn s 𝕍 K' ≤ (C : ENNReal) * Kakeya.densityIn s 𝕎 K' :=
        densityIn_le_of_comparable hC s 𝕎 𝕍 hsub hvol K'
      _ ≤ (C : ENNReal) * (ConvexSpaceBody.frostmanConstIn s 𝕎 K * Kakeya.densityIn s 𝕎 K) := by
        gcongr
        exact h_isFrostmanW K' hK'
      _ = (C : ENNReal) * ConvexSpaceBody.frostmanConstIn s 𝕎 K * Kakeya.densityIn s 𝕎 K := by
        ring
      _ ≤ (C : ENNReal) * ConvexSpaceBody.frostmanConstIn s 𝕎 K * Kakeya.densityIn s 𝕍 K := by
        gcongr
        exact densityIn_ambient_le_of_comparable s 𝕎 𝕍 K hsub hVK
  exact ConvexSpaceBody.frostmanConstIn_le h_isFrostmanV

/-- **One-sided transport of multiplicity, fullness and the Frostman constant** (blueprint
`lem:comparableTransportOneSided`).

The three conjuncts are items (i)–(iii) of the blueprint lemma.  No tube, no scale, no inner
body and no bound on the shading volumes is involved. -/
theorem comparableTransport_oneSided {ι : Type*} {C : NNReal} (hC : 1 ≤ C) (s : Finset ι)
    (𝕎 𝕍 : ι → ShadedBody E) (K : ConvexSpaceBody E)
    (hshade : ∀ i ∈ s, (𝕍 i).shade = (𝕎 i).shade)
    (hsub : ∀ i ∈ s, (𝕎 i).toConvexSpaceBody ≤ (𝕍 i).toConvexSpaceBody)
    (hVK : ∀ i ∈ s, (𝕍 i).toConvexSpaceBody ≤ K)
    (hvol : ∀ i ∈ s, volume (𝕍 i).carrier ≤ (C : ENNReal) * volume (𝕎 i).carrier) :
    ShadedBody.multiplicity s 𝕍 = ShadedBody.multiplicity s 𝕎 ∧
      C⁻¹ * ShadedBody.fullness s 𝕎 ≤ ShadedBody.fullness s 𝕍 ∧
      ConvexSpaceBody.frostmanConstIn s (fun i => (𝕍 i).toConvexSpaceBody) K
        ≤ (C : ENNReal)
          * ConvexSpaceBody.frostmanConstIn s (fun i => (𝕎 i).toConvexSpaceBody) K := by
  refine ⟨?_, ?_, ?_⟩
  · exact multiplicity_congr_of_shading_eq s 𝕎 𝕍 hshade
  · exact le_fullness_of_volume_le hC s 𝕎 𝕍 hshade hvol
  · exact frostmanConstIn_le_of_comparable hC s (fun i => (𝕎 i).toConvexSpaceBody)
      (fun i => (𝕍 i).toConvexSpaceBody) K hsub hVK hvol

/-- **A maximal essentially distinct subfamily whose dilates cover** (blueprint
`lem:comparableMaximalSubfamily`).

Take `s'` maximal among the subsets of `s` indexing a pairwise essentially distinct
subcollection (`Kakeya.Tube.exists_maximal_essDistinct`).  A retained tube lies in its own
dilate by `Tube.subset_dilate`, and a discarded one overlaps some retained tube heavily, so
`Kakeya.Tube.tubeOverlapCoreClose` puts it in the dilate of that one. -/
theorem exists_essDistinct_dilateCover {ι : Type*} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (s : Finset ι)
    (𝕍 : ι → Tube ρ E) :
    ∃ s' ⊆ s,
      (↑s' : Set ι).Pairwise (fun i j => IsEssentiallyDistinct (𝕍 i).carrier (𝕍 j).carrier) ∧
        ∀ j ∈ s, ∃ i ∈ s', (𝕍 j).carrier ⊆ (Kakeya.Tube.dilate (𝕍 i)
          (Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E))).carrier := by
  classical
  obtain ⟨s', hs'sub, hpair, hmax⟩ := Kakeya.Tube.exists_maximal_essDistinct s 𝕍
  refine ⟨s', hs'sub, hpair, ?_⟩
  intro j hj
  by_cases hj' : j ∈ s'
  · refine ⟨j, hj', ?_⟩
    exact Tube.subset_dilate (𝕍 j)
      (le_of_lt (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C (Module.finrank ℝ E)))
  · rcases hmax j hj hj' with ⟨i, hi, hnot⟩
    have hxy : (𝕍 j).x ≠ (𝕍 j).y := by
      have hd : dist (𝕍 j).x (𝕍 j).y ≠ 0 := by
        rw [(𝕍 j).dist_eq_one]
        norm_num
      exact dist_ne_zero.mp hd
    haveI : Nontrivial E := Nontrivial.mk ⟨(𝕍 j).x, (𝕍 j).y, hxy⟩
    have hhalf : (1 / 2 : ENNReal) * volume (𝕍 i).carrier <
        volume ((𝕍 i).carrier ∩ (𝕍 j).carrier) := by
      have hnot_unfold : (1 / 2 : ENNReal) *
          max (volume (𝕍 i).carrier) (volume (𝕍 j).carrier) <
          volume ((𝕍 i).carrier ∩ (𝕍 j).carrier) := lt_of_not_ge hnot
      calc
        (1 / 2 : ENNReal) * volume (𝕍 i).carrier ≤
            (1 / 2 : ENNReal) * max (volume (𝕍 i).carrier) (volume (𝕍 j).carrier) := by
              gcongr; exact le_max_left _ _
        _ < volume ((𝕍 i).carrier ∩ (𝕍 j).carrier) := hnot_unfold
    refine ⟨i, hi, ?_⟩
    exact Kakeya.Tube.tubeOverlapCoreClose hρ0 hρ1 (𝕍 i) (𝕍 j) hhalf

/-- **Each retained tube carries boundedly many discarded ones** (blueprint
`lem:comparableFibreBound`).

The fibres `A_i = {j ∈ s | U_j ⊆ C_n · V_i}`, `i ∈ s'`, cover `s`, and each has at most
`C_{lem:comparableBodiesToTubes}(n, C)` elements by `Tube.essDistinctTubesInDilate`; the
cardinality bound is then `Kakeya.card_le_card_cover_mul`. -/
theorem card_le_mul_card_of_dilateCover {ι : Type*} [Nontrivial E] {C : NNReal} (hC : 1 ≤ C)
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) {s s' : Finset ι} (hs' : s' ⊆ s) (𝕍 : ι → Tube ρ E)
    (𝕌 : ι → Tube (C⁻¹ * ρ) E) (hUsub : ∀ i ∈ s, (𝕌 i).carrier ⊆ (𝕍 i).carrier)
    (hUED : (↑s : Set ι).Pairwise fun i j => IsEssentiallyDistinct (𝕌 i).carrier (𝕌 j).carrier)
    (hcover : ∀ j ∈ s, ∃ i ∈ s', (𝕍 j).carrier ⊆ (Kakeya.Tube.dilate (𝕍 i)
      (Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E))).carrier) :
    (s.card : ENNReal)
      ≤ (comparableReplacement.C (Module.finrank ℝ E) C : ENNReal) * (s'.card : ENNReal) := by
  classical
  let Cn : ℝ := Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E)
  let Cb : NNReal := comparableReplacement.C (Module.finrank ℝ E) C
  let A : ι → Finset ι := fun i =>
    s.filter (fun j => (𝕌 j).carrier ⊆ (Kakeya.Tube.dilate (𝕍 i) Cn).carrier)
  have hA : ∀ i, A i ⊆ s := by
    intro i
    exact
      Finset.filter_subset (fun j => (𝕌 j).carrier ⊆ (Kakeya.Tube.dilate (𝕍 i) Cn).carrier) s
  have hcover_fibres : s ⊆ s'.biUnion A := by
    intro j hj
    rcases hcover j hj with ⟨i, hi, hjd⟩
    have hUd : (𝕌 j).carrier ⊆ (Kakeya.Tube.dilate (𝕍 i) Cn).carrier :=
      Set.Subset.trans (hUsub j hj) hjd
    exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_filter.mpr ⟨hj, hUd⟩⟩
  have hfibre_enn : ∀ i ∈ s', ((A i).card : ENNReal) ≤ (Cb : ENNReal) := by
    intro i hi
    have hAi_ED : (↑(A i) : Set ι).Pairwise
        (fun j k => IsEssentiallyDistinct (𝕌 j).carrier (𝕌 k).carrier) := by
      exact hUED.mono (Finset.coe_subset.mpr (hA i))
    have hUV : ∀ j ∈ A i, (𝕌 j).carrier ⊆ (Kakeya.Tube.dilate (𝕍 i) Cn).carrier := by
      intro j hj
      exact (Finset.mem_filter.mp hj).2
    exact essDistinctTubesInDilate hC hρ0 hρ1 (𝕍 i) (A i) 𝕌 hAi_ED hUV
  calc
    (s.card : ENNReal) ≤ ((s'.biUnion A).card : ENNReal) := by
      exact_mod_cast (Finset.card_le_card hcover_fibres)
    _ ≤ (∑ i ∈ s', (A i).card : ENNReal) := by
      exact_mod_cast (Finset.card_biUnion_le (t := A))
    _ ≤ (∑ i ∈ s', (Cb : ENNReal)) := by
      exact Finset.sum_le_sum (fun i hi => hfibre_enn i hi)
    _ = (Cb : ENNReal) * (s'.card : ENNReal) := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- **From a cardinality bound to a refinement** (blueprint
`lem:comparableRefinementClause`).

Let `C₁ = C_{lem:comparableBodiesToTubes}(n, C)`.  The two-sided shade bounds
`Λ⁻¹ μ₀ W ≤ |Z_i| ≤ Λ μ₀ W` give, in total, `|s| · Λ μ₀ W` as an upper bound on the
sum of the shades over `s` and `|s'| · Λ⁻¹ μ₀ W` as a lower bound on the sum over
`s'`.  Combining these with the cardinality bound `|s| ≤ C₁ |s'|` and the identification
`(C₁ Λ²)⁻¹ = C₁⁻¹ Λ⁻²` in `ENNReal` yields
`(C₁ Λ²)⁻¹ ∑_{i ∈ s} |Z_i| ≤ ∑_{i ∈ s'} |Z_i|`, i.e. the claimed `(C₁ Λ²)⁻¹`-refinement.
(The abstract reference `W` is used directly, so no equal-tube-volume fact is needed.) -/
theorem isCRefinement_of_card_le {ι : Type*} [Nontrivial E] {C Λ : NNReal} {μ₀ W : ENNReal}
    (hC : 1 ≤ C) (hΛ : 1 ≤ Λ) (hρ0 : 0 < ρ) (hW : W ≠ 0) (hW' : W ≠ ⊤) (hμ₀ : μ₀ ≠ 0)
    (hμ₀' : μ₀ ≠ ⊤) {s s' : Finset ι} (hs : s.Nonempty) (hs'sub : s' ⊆ s) (hs'ne : s'.Nonempty)
    (𝕍 : ι → ShadedTube ρ E)
    (hlow : ∀ i ∈ s, (Λ : ENNReal)⁻¹ * μ₀ * W ≤ volume (𝕍 i).shade)
    (hupp : ∀ i ∈ s, volume (𝕍 i).shade ≤ (Λ : ENNReal) * μ₀ * W)
    (hcard : (s.card : ENNReal)
      ≤ (comparableReplacement.C (Module.finrank ℝ E) C : ENNReal) * (s'.card : ENNReal)) :
    ShadedBody.IsCRefinement s' (fun i => (𝕍 i).toShadedBody) s (fun i => (𝕍 i).toShadedBody)
      (comparableReplacement.C (Module.finrank ℝ E) C * Λ ^ 2)⁻¹ := by
  classical
  set C₁ : NNReal := comparableReplacement.C (Module.finrank ℝ E) C
  let Λe : ENNReal := (Λ : ENNReal)
  let Z : ι → ENNReal := fun i => volume (𝕍 i).shade
  let S : ENNReal := ∑ i ∈ s, Z i
  let T : ENNReal := ∑ i ∈ s', Z i
  have hΛne0 : (Λ : ENNReal) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one hΛ))
  have hΛne : (Λ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hΛ2_ne0 : (Λ ^ 2 : NNReal) ≠ 0 :=
    pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le zero_lt_one hΛ))
  have hC1_ne0 : (C₁ : NNReal) ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one
      (comparableReplacement.one_le_C (Module.finrank ℝ E) C))
  have hC1_ne0e : (C₁ : ENNReal) ≠ 0 := by exact_mod_cast hC1_ne0
  have hC1_ne_top : (C₁ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hC1_mul_Λ2_ne0 : (C₁ * Λ ^ 2 : NNReal) ≠ 0 := mul_ne_zero hC1_ne0 hΛ2_ne0
  have hcoepow : (Λe : ENNReal) ^ 2 = ((Λ ^ 2 : NNReal) : ENNReal) := by
    simp [Λe]
  have hΛinv2 : ((Λ ^ 2 : NNReal) : ENNReal)⁻¹ = Λe⁻¹ * Λe⁻¹ := by
    rw [← hcoepow, ENNReal.inv_pow, pow_two]
  have hκcard : ((C₁⁻¹ : NNReal) : ENNReal) * (s.card : ENNReal) ≤ (s'.card : ENNReal) := by
    calc
      ((C₁⁻¹ : NNReal) : ENNReal) * (s.card : ENNReal)
          ≤ ((C₁⁻¹ : NNReal) : ENNReal) * ((C₁ : ENNReal) * (s'.card : ENNReal)) := by
            exact mul_le_mul_right hcard _
      _ = (((C₁⁻¹ : NNReal) : ENNReal) * (C₁ : ENNReal)) * (s'.card : ENNReal) := by
            rw [← mul_assoc]
      _ = ((C₁ : ENNReal)⁻¹ * (C₁ : ENNReal)) * (s'.card : ENNReal) := by
            rw [ENNReal.coe_inv hC1_ne0]
      _ = (1 : ENNReal) * (s'.card : ENNReal) := by
            rw [ENNReal.inv_mul_cancel hC1_ne0e hC1_ne_top]
      _ = (s'.card : ENNReal) := by
            rw [one_mul]
  have hS : S ≤ (s.card : ENNReal) * (Λe * μ₀ * W) := by
    calc
      S = ∑ i ∈ s, Z i := rfl
      _ ≤ ∑ i ∈ s, (Λe * μ₀ * W) := by
        exact Finset.sum_le_sum (fun i hi => hupp i hi)
      _ = (s.card : ENNReal) * (Λe * μ₀ * W) := by
        rw [Finset.sum_const, nsmul_eq_mul]
  have hC : (s'.card : ENNReal) * (Λe⁻¹ * μ₀ * W) ≤ T := by
    calc
      (s'.card : ENNReal) * (Λe⁻¹ * μ₀ * W) = ∑ i ∈ s', (Λe⁻¹ * μ₀ * W) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ T := by
        dsimp [T, Z]
        exact Finset.sum_le_sum (fun i hi => hlow i (hs'sub hi))
  have hmid : ((C₁⁻¹ : NNReal) : ENNReal) * (Λe⁻¹ * Λe⁻¹) * (s.card : ENNReal) * (Λe * μ₀ * W)
      ≤ (s'.card : ENNReal) * (Λe⁻¹ * μ₀ * W) := by
    calc
      ((C₁⁻¹ : NNReal) : ENNReal) * (Λe⁻¹ * Λe⁻¹) * (s.card : ENNReal) * (Λe * μ₀ * W)
          = ((C₁⁻¹ : NNReal) : ENNReal) * (s.card : ENNReal) * (Λe⁻¹ * Λe⁻¹)
            * (Λe * μ₀ * W) := by ring
      _ = ((C₁⁻¹ : NNReal) : ENNReal) * (s.card : ENNReal) * ((Λe⁻¹ * Λe⁻¹) * Λe)
            * μ₀ * W := by ring
      _ = ((C₁⁻¹ : NNReal) : ENNReal) * (s.card : ENNReal)
            * (Λe⁻¹ * (Λe⁻¹ * Λe)) * μ₀ * W := by ring
      _ = ((C₁⁻¹ : NNReal) : ENNReal) * (s.card : ENNReal) * (Λe⁻¹ * 1) * μ₀ * W := by
        rw [show (Λe : ENNReal)⁻¹ * (Λe : ENNReal) = 1 by
          exact ENNReal.inv_mul_cancel hΛne0 hΛne]
      _ = ((C₁⁻¹ : NNReal) : ENNReal) * (s.card : ENNReal) * Λe⁻¹ * μ₀ * W := by ring
      _ = ((C₁⁻¹ : NNReal) : ENNReal) * (s.card : ENNReal) * (Λe⁻¹ * μ₀ * W) := by ring
      _ ≤ (s'.card : ENNReal) * (Λe⁻¹ * μ₀ * W) := by gcongr
  have hκmatch : ((C₁ * Λ ^ 2 : NNReal)⁻¹ : ENNReal)
      = ((C₁⁻¹ : NNReal) : ENNReal) * (Λe⁻¹ * Λe⁻¹) := by
    rw [ENNReal.coe_mul, ENNReal.mul_inv (Or.inl hC1_ne0e) (Or.inl hC1_ne_top),
      ← ENNReal.coe_inv hC1_ne0, hΛinv2]
  have hgoal : ((C₁ * Λ ^ 2 : NNReal)⁻¹ : ENNReal) * S ≤ T := by
    calc
      ((C₁ * Λ ^ 2 : NNReal)⁻¹ : ENNReal) * S
          = ((C₁⁻¹ : NNReal) : ENNReal) * (Λe⁻¹ * Λe⁻¹) * S := by
            rw [hκmatch]
      _ ≤ ((C₁⁻¹ : NNReal) : ENNReal) * (Λe⁻¹ * Λe⁻¹) * ((s.card : ENNReal) * (Λe * μ₀ * W)) := by
            gcongr
      _ = ((C₁⁻¹ : NNReal) : ENNReal) * (Λe⁻¹ * Λe⁻¹) * (s.card : ENNReal)
            * (Λe * μ₀ * W) := by ring
      _ ≤ (s'.card : ENNReal) * (Λe⁻¹ * μ₀ * W) := hmid
      _ ≤ T := hC
  constructor
  · exact ⟨hs'sub, fun i hi => ⟨rfl, Subset.rfl⟩⟩
  · dsimp
    simpa only [S, T, Z, ENNReal.coe_inv hC1_mul_Λ2_ne0] using hgoal

/-- **The conclusions of `Tube.exists_comparableReplacement`, one field per item.**

Here `𝕎 = (W_i)_{i ∈ s}` is a family of shaded convex bodies (its shading is the `Z` of the
blueprint) and `𝕍 = (V_i)_{i ∈ s}` is a family of `ρ`-tubes carrying the *same* shading, so
that the blueprint's "`Z` is a shading of `𝕍`" is built into the type `ShadedTube ρ E`.
The fields are the items (i)–(v) of the blueprint lemma `lem:comparableBodiesToTubes`,
with (iv) and (v) bundled into the single field `select` because they share the witness
`s'`. -/
structure IsComparableReplacement {ι : Type*} (s : Finset ι) (𝕎 : ι → ShadedBody E)
    (𝕍 : ι → ShadedTube ρ E) (K : ConvexSpaceBody E) (C Λ : NNReal) : Prop where
  /-- (i) Multiplicity is unchanged: it depends only on the shading, not on the bodies
  carrying it. -/
  multiplicity : ShadedBody.multiplicity s (fun i => (𝕍 i).toShadedBody)
    = ShadedBody.multiplicity s 𝕎
  /-- (ii) Fullness drops by at most the comparability factor `C`. -/
  fullness : C⁻¹ * ShadedBody.fullness s 𝕎 ≤ ShadedBody.fullness s (fun i => (𝕍 i).toShadedBody)
  /-- (iii) The Frostman constant in `K` grows by at most the comparability factor `C`. -/
  frostmanConstIn : ConvexSpaceBody.frostmanConstIn s (fun i => (𝕍 i).toConvexSpaceBody) K
    ≤ (C : ENNReal) * ConvexSpaceBody.frostmanConstIn s (fun i => (𝕎 i).toConvexSpaceBody) K
  /-- (iv) There is `s' ⊆ s` indexing a pairwise essentially distinct subfamily of `𝕍` with
  `|s'| ≥ C₁⁻¹ |s|`, written multiplicatively as `|s| ≤ C₁ |s'|`, and (v) for that `s'` the
  restricted shaded family is a `(C₁ Λ²)⁻¹`-refinement of `(𝕍, Z)`. -/
  select : ∃ s' ⊆ s,
    (↑s' : Set ι).Pairwise (fun i j => IsEssentiallyDistinct (𝕍 i).carrier (𝕍 j).carrier) ∧
    (s.card : ENNReal)
        ≤ (comparableReplacement.C (Module.finrank ℝ E) C : ENNReal) * (s'.card : ENNReal) ∧
    ShadedBody.IsCRefinement s' (fun i => (𝕍 i).toShadedBody) s (fun i => (𝕍 i).toShadedBody)
      (comparableReplacement.C (Module.finrank ℝ E) C * Λ ^ 2)⁻¹

/-- **Replacing comparable bodies by honest `ρ`-tubes** (blueprint
`lem:comparableBodiesToTubes`).

Let `𝕎 = (W_i)_{i ∈ s}` be a nonempty family of pairwise essentially distinct convex bodies
of common volume `W > 0`, all contained in a convex body `K` of positive volume, shaded by
`Z_i = (𝕎 i).shade` with `Λ⁻¹ μ₀ W ≤ |Z_i| ≤ Λ μ₀ W`.  Suppose each `W_i` is *two-sidedly*
comparable to a tube: there are a `ρ`-tube `V_i` and a `C⁻¹ ρ`-tube `U_i` with

```
U_i ⊆ W_i ⊆ V_i ⊆ K,      |V_i| ≤ C |W_i|,
```

that `V_i` carries the same shading `Z_i`, and that the *inner* tubes `(U_i)_{i ∈ s}` are
pairwise essentially distinct.  Then all five items of `Tube.IsComparableReplacement` hold.

The inner tubes enter only through the selection item `select`, via
`Tube.essDistinctTubesInDilate`; the fields `multiplicity`, `fullness` and `frostmanConstIn`
are proved from `W_i ⊆ V_i` and `|V_i| ≤ C |W_i|` alone.  Blueprint
`note:comparableBodiesGap` records why the selection item is *not* available from that
one-sided data: it would require bounding the number of pairwise essentially distinct bodies
of volume `W` inside a body of volume `≲ C W`, and the only counting tools in the development
(`lem:tubesInBodyCount`, which is a Katz–Tao bound, and the naive `L²` count) both fail at
the constants needed here.  An earlier version of this Lean statement omitted the inner tubes
and was therefore not provable.

The `ρ`-tubes are supplied as a family of `ShadedTube ρ E` rather than as bare tubes plus a
separate shading: the containment `Z_i ⊆ W_i ⊆ V_i` that makes `Z` a shading of `𝕍` is then
part of the type, and the conclusions can be stated with the existing `ShadedBody` API.  The
inner tubes carry no shading and are supplied as bare `Tube (C⁻¹ * ρ) E`. -/
theorem exists_comparableReplacement {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    (𝕎 : ι → ShadedBody E) (𝕍 : ι → ShadedTube ρ E) {C Λ : NNReal} (𝕌 : ι → Tube (C⁻¹ * ρ) E)
    (K : ConvexSpaceBody E)
    {W μ₀ : ENNReal} (hC : 1 ≤ C) (hΛ : 1 ≤ Λ) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hW : 0 < W) (hμ₀ : 0 < μ₀) (hK : 0 < volume K.carrier)
    (hcommon : ∀ i ∈ s, volume (𝕎 i).carrier = W)
    (hWK : ∀ i ∈ s, (𝕎 i).toConvexSpaceBody ≤ K)
    (hED : (↑s : Set ι).Pairwise fun i j => IsEssentiallyDistinct (𝕎 i).carrier (𝕎 j).carrier)
    (hshade : ∀ i ∈ s, (𝕍 i).shade = (𝕎 i).shade)
    (hsub : ∀ i ∈ s, (𝕎 i).carrier ⊆ (𝕍 i).carrier)
    (hVK : ∀ i ∈ s, (𝕍 i).toConvexSpaceBody ≤ K)
    (hvol : ∀ i ∈ s, volume (𝕍 i).carrier ≤ (C : ENNReal) * volume (𝕎 i).carrier)
    (hUsub : ∀ i ∈ s, (𝕌 i).carrier ⊆ (𝕎 i).carrier)
    (hUED : (↑s : Set ι).Pairwise fun i j => IsEssentiallyDistinct (𝕌 i).carrier (𝕌 j).carrier)
    (hZ : ∀ i ∈ s, (Λ : ENNReal)⁻¹ * μ₀ * W ≤ volume (𝕎 i).shade ∧
      volume (𝕎 i).shade ≤ (Λ : ENNReal) * μ₀ * W) :
    IsComparableReplacement s 𝕎 𝕍 K C Λ := by
  classical
  haveI : Nontrivial E := by
    rcases hs with ⟨i₀, hi₀⟩
    let T : Tube ρ E := (𝕍 i₀).toTube
    refine ⟨T.x, T.y, ?_⟩
    intro hxy
    have hd : (0 : ℝ) = 1 := by
      simpa [hxy, dist_self] using T.dist_eq_one
    norm_num at hd
  -- Items (i)–(iii): one-sided transport of multiplicity, fullness and the Frostman constant
  have htr := comparableTransport_oneSided hC s 𝕎 (fun i => (𝕍 i).toShadedBody) K
    (by intro i hi; simpa using hshade i hi)
    (by intro i hi; exact SetLike.coe_subset_coe.mpr (hsub i hi))
    (by intro i hi; simpa using hVK i hi)
    hvol
  -- Items (iv)–(v): selection of a maximal essentially distinct subfamily
  obtain ⟨s', hs'sub, hpair, hcover⟩ :=
    exists_essDistinct_dilateCover hρ0 hρ1 s (fun i => (𝕍 i).toTube)
  have hUsubV : ∀ i ∈ s, (𝕌 i).carrier ⊆ ((𝕍 i).toTube).carrier := by
    intro i hi
    exact (hUsub i hi).trans (hsub i hi)
  have hcard : (s.card : ENNReal)
      ≤ (comparableReplacement.C (Module.finrank ℝ E) C : ENNReal) * (s'.card : ENNReal) := by
    exact card_le_mul_card_of_dilateCover hC hρ0 hρ1 hs'sub (fun i => (𝕍 i).toTube) 𝕌
      hUsubV hUED hcover
  have hs'ne : s'.Nonempty := by
    rcases hs with ⟨j₀, hj₀⟩
    rcases hcover j₀ hj₀ with ⟨i, hi, _⟩
    exact ⟨i, hi⟩
  have hW_top : W ≠ ⊤ := by
    rcases hs with ⟨i₀, hi₀⟩
    have hWtop' : volume (𝕎 i₀).carrier ≠ ⊤ := (𝕎 i₀).isCompact.measure_ne_top
    rw [hcommon i₀ hi₀] at hWtop'
    exact hWtop'
  have hμ₀_top : μ₀ ≠ ⊤ := by
    rcases hs with ⟨i₀, hi₀⟩
    have hshade_lt : volume (𝕎 i₀).shade < ⊤ := by
      calc
        volume (𝕎 i₀).shade ≤ volume (𝕎 i₀).carrier := measure_mono (𝕎 i₀).shade_subset
        _ = W := hcommon i₀ hi₀
        _ < ⊤ := hW_top.lt_top
    have hLHS_lt : (Λ : ENNReal)⁻¹ * μ₀ * W < ⊤ :=
      lt_of_le_of_lt (hZ i₀ hi₀).1 hshade_lt
    intro hμ₀top
    have hΛ_inv_ne_zero : (Λ : ENNReal)⁻¹ ≠ 0 :=
      ENNReal.inv_ne_zero.mpr (by exact ENNReal.coe_ne_top)
    have hLHS_eq : (Λ : ENNReal)⁻¹ * μ₀ * W = ⊤ := by
      rw [hμ₀top, ENNReal.mul_top hΛ_inv_ne_zero, ENNReal.top_mul (ne_of_gt hW)]
    rw [hLHS_eq] at hLHS_lt
    exact lt_irrefl _ hLHS_lt
  have hcref : ShadedBody.IsCRefinement s' (fun i => (𝕍 i).toShadedBody) s
      (fun i => (𝕍 i).toShadedBody)
      (comparableReplacement.C (Module.finrank ℝ E) C * Λ ^ 2)⁻¹ := by
    exact isCRefinement_of_card_le hC hΛ hρ0 (ne_of_gt hW) hW_top (ne_of_gt hμ₀) hμ₀_top
      hs hs'sub hs'ne 𝕍
      (by intro i hi; simpa [hshade i hi] using (hZ i hi).1)
      (by intro i hi; simpa [hshade i hi] using (hZ i hi).2)
      hcard
  refine ⟨htr.1, htr.2.1, htr.2.2, ?_⟩
  · refine ⟨s', hs'sub, ?_, ?_, ?_⟩
    · simpa using hpair
    · exact hcard
    · exact hcref

/-! ### The rescaling of a tube at a normalized ambient radius

Blueprint `section8_finenormalize_select.tex` calls the situation below *the rescaling
situation*; the declarations of this section are that situation, the centred extension it produces, the
three pullbacks of the downstairs selection and the count they feed
(`lem:essDistinctTubesInSelfDilate`, the open leaf of that route).

Notation, translated into the naming convention of this file: the blueprint's ambient
`τ`-tube `T_τ` with initial core endpoint `x` is `T₀ : Tube θ E` with `x = T₀.x`; the
blueprint's inner `δ`-tube `T` is `T : Tube τ E`; the blueprint's `ρ = δ / τ` is
`(τ : ℝ) / (θ : ℝ)`; the blueprint's output scale `σ ∈ (0, 1/4]` with `σ ≤ ρ` is `σ : NNReal`;
`C_N = Tube.normalization.C n` and the normalized ambient radius satisfies `C_N ≤ R`.  The
blueprint's `Φ = Φ_{T_τ}` is `T₀.normalization` and its `Ψ = h ∘ Φ` is `T₀.rescaleMap R`.

The scale hypotheses `0 < θ`, `τ ≤ θ`, `θ ≤ 1`, `0 < σ`, `σ ≤ 1/4`, `σ ≤ ρ`, `C_N ≤ R` are
exactly that standing situation, so they travel bundled, as `Tube.IsRescalingSituation`.  The
extra hypothesis `ρ ≤ 4 σ` of the outer-tube lemma is *not* part of it — it is what that one
lemma adds — and is spelled out there. -/

section Rescaling

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {θ τ σ : NNReal}

/-- **The rescaling situation** (blueprint `section8_finenormalize_select.tex`, the standing
hypotheses of that subsubsection).

`IsRescalingSituation θ τ σ R n` collects the scale hypotheses under which the rescaling
`Tube.rescaleMap` of an ambient `θ`-tube at radius `R` carries an inner `τ`-tube to a body
comparable to a `σ`-tube in the unit ball, in dimension `n`: the ambient scale `θ` is a
genuine tube scale (`pos_ambient`, `ambient_le_one`) containing the inner scale
(`inner_le_ambient`), the output scale `σ` is positive, truncated at `1/4` and no larger than
the ratio `ρ = τ / θ`, and the ambient radius is past the distortion constant
`C_N = Tube.normalization.C n`.

These seven inequalities are one mathematical situation and not an incidental list, which is
why they are a structure: every statement about the rescaling needs all of them, the
blueprint names the package, and `Tube.rescale_outer_tube` would otherwise open with nine
hypothesis binders.  What is deliberately *not* in it is the extra inequality `ρ ≤ 4 σ` used
by `Tube.rescale_outer_tube`; that one belongs to that lemma alone, and is what forces the
homothety ratio `4 R` rather than `R`.

The dimension is a bare `n : ℕ` rather than `Module.finrank ℝ E` so that the structure carries
no typeclass baggage; consumers instantiate it at `n = Module.finrank ℝ E`. -/
structure IsRescalingSituation (θ τ σ : NNReal) (R : ℝ) (n : ℕ) : Prop where
  /-- The ambient tube scale is positive. -/
  pos_ambient : 0 < θ
  /-- The inner tube scale does not exceed the ambient one, so `ρ = τ / θ ≤ 1`. -/
  inner_le_ambient : τ ≤ θ
  /-- The ambient tube scale is a scale, `θ ≤ 1`; this is what makes `Φ_{T₀}` expanding. -/
  ambient_le_one : θ ≤ 1
  /-- The output scale is positive. -/
  pos_out : 0 < σ
  /-- The output scale is truncated at `1/4`; this is what keeps the outer tube in `B₁`. -/
  out_le_quarter : (σ : ℝ) ≤ 1 / 4
  /-- The output scale does not exceed the ratio `ρ = τ / θ`. -/
  out_le_ratio : (σ : ℝ) ≤ (τ : ℝ) / (θ : ℝ)
  /-- The ambient radius is past the distortion constant `C_N = Tube.normalization.C n`. -/
  normalizationConst_le_radius : (normalization.C n : ℝ) ≤ R

/-- **The rescaling of a `θ`-tube at a normalized ambient radius `R`** (blueprint
`def:tubeRescale`): the normalization `Φ_{T₀}` of `Tube.normalization` followed by the
homothety `h : z ↦ (z - T₀.x) / (4 R)` about the initial endpoint `T₀.x` of the core, that is

```
Ψ_{T₀,R} (z) = (4 R)⁻¹ • (Φ_{T₀} (z) - T₀.x).
```

Recentring at `T₀.x` rather than dividing by `4 R` outright is what makes
`Ψ (B̄(T₀.x, R)) = B̄(0, 1/4)` exact rather than exact up to a translation, and it is why
`Ψ_{T₀,R} (T₀.x) = 0` (`Tube.normalization_apply_x`).  For `0 < θ` and `0 < R` the map is
an affine equivalence, its linear part being `(4 R)⁻¹ • A` with `A` the linear part of
`Φ_{T₀}` (`Tube.normalizationLinear`): the identity on `ℝ ∙ T₀.direction` and multiplication
by `θ⁻¹` on its orthogonal complement.  Consequently the linear part of `Ψ⁻¹` is `4 R • A⁻¹`,
which is multiplication by `4 R` on `ℝ ∙ T₀.direction` and by `4 R θ` on its orthogonal
complement.

The name is `rescaleMap` and not `rescale` because `Tube.rescale` of `Kakeya/Tube/Basic.lean`
is an unrelated operation — it re-thickens a tube in place, keeping its core — while this is
a map of the ambient space.  The blueprint records the Lean target as `Tube.rescale`; that
target is unavailable and the blueprint should be corrected to `Tube.rescaleMap`. -/
noncomputable def rescaleMap (T₀ : Tube θ E) (R : ℝ) : E →ᵃ[ℝ] E :=
  (((4 * R)⁻¹ • (LinearMap.id : E →ₗ[ℝ] E)).toAffineMap).comp
    ((AffineEquiv.constVAdd ℝ E (-T₀.x)).toAffineMap.comp T₀.normalization)

/-- **The `s`-tube on the centred unit extension of a segment** (blueprint
`def:centredExtensionTube`).

For `p ≠ q` and `s : NNReal`, `Tube.centredExtension s hpq` is the `s`-tube whose core is the
segment of length `1` centred at `midpoint ℝ p q` in the direction `g = (q - p) / ‖q - p‖`,
namely `[midpoint ℝ p q - g / 2, midpoint ℝ p q + g / 2]`.  Its carrier is the closed
`s`-neighbourhood of that core (`Tube.carrier_eq_cthickening`).

This is the "extension to unit length" that the proof of blueprint
`lem:ml1bootFineNormalizeCore` takes at `p = Ψ(a)`, `q = Ψ(b)` for the images of the
endpoints of the core of an inner tube: an honest `Tube` has a core of length exactly `1`
(`Tube.dist_eq_one`), whereas `Ψ` shortens the image core by the factor `4 R`, so the core
has to be extended rather than used as it stands.  The hypothesis `p ≠ q` is what makes the
direction `g` a unit vector and hence the construction legitimate.

The four properties it is used for are separated out as
`Tube.cthickening_subset_centredExtension`, `Tube.centredExtension_subset_closedBall`,
`Tube.center_centredExtension` and `Tube.direction_centredExtension`.

Formally this is nothing but `Tube.ofMidpointDirection` — the tube with prescribed midpoint and
unit direction of `Kakeya/Tube/Basic.lean` — read at `m = midpoint ℝ p q` and `u = g`; the only
work is checking `‖g‖ = 1`, which is where `p ≠ q` is spent.  Consequently the two `@[simps!]`
lemmas `Tube.ofMidpointDirection_x` and `Tube.ofMidpointDirection_y` compute the core endpoints
of a `centredExtension`, and no separate simp set is needed. -/
noncomputable def centredExtension (s : NNReal) {p q : E} (hpq : p ≠ q) : Tube s E :=
  ofMidpointDirection s (_root_.midpoint ℝ p q) (‖q - p‖⁻¹ • (q - p)) (by
    have h : ‖q - p‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero_of_ne (Ne.symm hpq))
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ h])

/-- **The centred extension covers the `s`-neighbourhood of the original segment** (blueprint
`lem:centredExtensionProperties`\ `item:centredExtCover`).

If `dist p q ≤ 1` then `[p, q]` is contained in the core of `Tube.centredExtension s hpq`,
because both segments are centred at `midpoint ℝ p q` and point in the same direction `g`,
the first having half-length `dist p q / 2 ≤ 1/2` and the second half-length `1/2`;
neighbourhoods of the same radius are then nested (`Metric.cthickening_subset_of_subset`,
after `Tube.carrier_eq_cthickening`).

The intended route: parametrise `[p, q] = {midpoint ℝ p q + t • g : |t| ≤ dist p q / 2}` and
cite `Tube.midpoint_add_smul_direction_mem_segment` for the resulting membership in the
core. -/
theorem cthickening_subset_centredExtension {s : NNReal} {p q : E} (hpq : p ≠ q)
    (hlen : dist p q ≤ 1) :
    cthickening (s : ℝ) (segment ℝ p q) ⊆ (centredExtension s hpq).carrier := by
  set T : Tube s E := centredExtension s hpq
  set g : E := ‖q - p‖⁻¹ • (q - p) with hg_def
  have hx : T.x = _root_.midpoint ℝ p q - (1 / 2 : ℝ) • g := by rfl
  have hy : T.y = _root_.midpoint ℝ p q + (1 / 2 : ℝ) • g := by rfl
  have hmid : T.midpoint = _root_.midpoint ℝ p q := by
    rw [Tube.midpoint, hx, hy]
    module
  have hdir : T.direction = g := by
    rw [Tube.direction, hx, hy]
    module
  have hqpn : ‖q - p‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero_of_ne (Ne.symm hpq))
  have hqpn_eq : ‖q - p‖ = dist p q := by rw [dist_eq_norm, norm_sub_rev]
  have hdist_ne : dist p q ≠ 0 := dist_ne_zero.mpr hpq
  have hdist_nn : (0 : ℝ) ≤ dist p q := dist_nonneg
  have hsc : (dist p q / 2 : ℝ) • g = (1 / 2 : ℝ) • (q - p) := by
    rw [hg_def, smul_smul, hqpn_eq]
    congr 1
    field_simp [hdist_ne]
  have hsc_neg : (-(dist p q / 2 : ℝ)) • g = -(1 / 2 : ℝ) • (q - p) := by
    rw [hg_def, smul_smul, hqpn_eq]
    congr 1
    field_simp [hdist_ne]
  have hp : p = _root_.midpoint ℝ p q + (-(dist p q / 2 : ℝ)) • g := by
    rw [hsc_neg]
    rw [midpoint_eq_smul_add]
    norm_num
    module
  have hq : q = _root_.midpoint ℝ p q + (dist p q / 2 : ℝ) • g := by
    rw [hsc]
    rw [midpoint_eq_smul_add]
    norm_num
    module
  have hp_mem : p ∈ segment ℝ T.x T.y := by
    convert T.midpoint_add_smul_direction_mem_segment (s := -(dist p q / 2 : ℝ))
        (by linarith [hlen, hdist_nn]) (by linarith [hdist_nn]) using 1
    rw [hmid, hdir, ← hp]
  have hq_mem : q ∈ segment ℝ T.x T.y := by
    convert T.midpoint_add_smul_direction_mem_segment (s := dist p q / 2)
        (by linarith [hdist_nn]) (by linarith [hlen]) using 1
    rw [hmid, hdir, ← hq]
  have hseg : segment ℝ p q ⊆ segment ℝ T.x T.y :=
    (convex_segment (𝕜 := ℝ) T.x T.y).segment_subset hp_mem hq_mem
  rw [T.carrier_eq_cthickening]
  exact Metric.cthickening_subset_of_subset (s : ℝ) hseg

/-- **The centred extension stays inside the unit ball** (blueprint
`lem:centredExtensionProperties`\ `item:centredExtBall`).

If `p, q ∈ B̄(z, 1/4)` and `s ≤ 1/4` then `Tube.centredExtension s hpq ⊆ B̄(z, 1)`: the
midpoint of two points of `B̄(z, 1/4)` lies in `B̄(z, 1/4)` by convexity
(`convex_closedBall`), so the core — of length `1` and centred there — lies in `B̄(z, 3/4)`
by convexity again (each core endpoint is `1/2` from the midpoint, since `‖(1/2) • g‖ = 1/2`),
and its closed `s`-neighbourhood equals `B̄(z, 3/4 + s)` via `Metric.cthickening_closedBall`,
which is `⊆ B̄(z, 1)` by `hs`.

This is the clause that spends `σ ≤ 1/4`, and it is what places the outer tube of
`Tube.rescale_outer_tube` inside `B_1`. -/
theorem centredExtension_subset_closedBall {s : NNReal} {p q : E} (hpq : p ≠ q) {z : E}
    (hp : dist p z ≤ 1 / 4) (hq : dist q z ≤ 1 / 4) (hs : (s : ℝ) ≤ 1 / 4) :
    (centredExtension s hpq).carrier ⊆ closedBall z 1 := by
  set T : Tube s E := centredExtension s hpq
  set g : E := ‖q - p‖⁻¹ • (q - p) with hg_def
  have hx : T.x = _root_.midpoint ℝ p q - (1 / 2 : ℝ) • g := by rfl
  have hy : T.y = _root_.midpoint ℝ p q + (1 / 2 : ℝ) • g := by rfl
  have hgdir : T.direction = g := by
    rw [Tube.direction, hx, hy]
    module
  have hnorm_g : ‖g‖ = 1 := by
    rw [← hgdir]
    exact T.norm_direction
  -- The midpoint of two points of `B̄(z, 1/4)` lies in `B̄(z, 1/4)` by convexity.
  have hp_ball : p ∈ closedBall z (1 / 4 : ℝ) := Metric.mem_closedBall.mpr hp
  have hq_ball : q ∈ closedBall z (1 / 4 : ℝ) := Metric.mem_closedBall.mpr hq
  have hconv : Convex ℝ (closedBall z (1 / 4 : ℝ)) := convex_closedBall z (1 / 4 : ℝ)
  have hmid_ball : _root_.midpoint ℝ p q ∈ closedBall z (1 / 4 : ℝ) :=
    hconv.midpoint_mem hp_ball hq_ball
  have hmid_le : dist (_root_.midpoint ℝ p q) z ≤ 1 / 4 := Metric.mem_closedBall.mp hmid_ball
  -- Each core endpoint is `1/2` from the midpoint, hence in `B̄(z, 3/4)`.
  have hTx_mid : dist T.x (_root_.midpoint ℝ p q) ≤ 1 / 2 := by
    rw [dist_eq_norm, hx]
    have hv : _root_.midpoint ℝ p q - (1 / 2 : ℝ) • g - _root_.midpoint ℝ p q =
        -(1 / 2 : ℝ) • g := by
      module
    rw [hv, norm_smul, Real.norm_eq_abs, hnorm_g]
    norm_num
  have hTy_mid : dist T.y (_root_.midpoint ℝ p q) ≤ 1 / 2 := by
    rw [dist_eq_norm, hy]
    have hv : _root_.midpoint ℝ p q + (1 / 2 : ℝ) • g - _root_.midpoint ℝ p q =
        (1 / 2 : ℝ) • g := by
      module
    rw [hv, norm_smul, Real.norm_eq_abs, hnorm_g]
    norm_num
  have hTx_ball : T.x ∈ closedBall z (3 / 4 : ℝ) := by
    rw [Metric.mem_closedBall]
    calc
      dist T.x z ≤ dist T.x (_root_.midpoint ℝ p q) + dist (_root_.midpoint ℝ p q) z :=
        dist_triangle T.x (_root_.midpoint ℝ p q) z
      _ ≤ (1 / 2 : ℝ) + (1 / 4 : ℝ) := add_le_add hTx_mid hmid_le
      _ = 3 / 4 := by norm_num
  have hTy_ball : T.y ∈ closedBall z (3 / 4 : ℝ) := by
    rw [Metric.mem_closedBall]
    calc
      dist T.y z ≤ dist T.y (_root_.midpoint ℝ p q) + dist (_root_.midpoint ℝ p q) z :=
        dist_triangle T.y (_root_.midpoint ℝ p q) z
      _ ≤ (1 / 2 : ℝ) + (1 / 4 : ℝ) := add_le_add hTy_mid hmid_le
      _ = 3 / 4 := by norm_num
  -- The whole core lies in `B̄(z, 3/4)` by convexity.
  have hcore_ball : segment ℝ T.x T.y ⊆ closedBall z (3 / 4 : ℝ) := by
    exact (convex_closedBall z (3 / 4 : ℝ)).segment_subset hTx_ball hTy_ball
  -- The carrier is the closed `s`-neighbourhood of the core.
  have hcarrier_subset :
      T.carrier ⊆ cthickening (s : ℝ) (closedBall z (3 / 4 : ℝ)) := by
    rw [T.carrier_eq_cthickening]
    exact Metric.cthickening_subset_of_subset (s : ℝ) hcore_ball
  have hthick : cthickening (s : ℝ) (closedBall z (3 / 4 : ℝ)) = closedBall z ((s : ℝ) + 3 / 4) :=
    cthickening_closedBall s.coe_nonneg (by norm_num) z
  have hs_le : (s : ℝ) + 3 / 4 ≤ 1 := by
    calc
      (s : ℝ) + 3 / 4 ≤ 1 / 4 + 3 / 4 := by gcongr
      _ = 1 := by norm_num
  calc
    (centredExtension s hpq).carrier ⊆ cthickening (s : ℝ) (closedBall z (3 / 4 : ℝ)) := by
      simpa [T] using hcarrier_subset
    _ = closedBall z ((s : ℝ) + 3 / 4) := hthick
    _ ⊆ closedBall z 1 := Metric.closedBall_subset_closedBall hs_le

/-- **The centre of the centred extension** (blueprint
`lem:centredExtensionProperties`\ `item:centredExtCentre`, first half).

Read off `Tube.centredExtension`: its core is by construction the segment of length `1`
centred at `midpoint ℝ p q` in the direction `g = (q - p) / ‖q - p‖`, so `Tube.center` — the
midpoint of the two core endpoints — is `midpoint ℝ p q`.  This should be `rfl` up to
`midpoint_sub_left`/`midpoint_add_self`-style rearrangement.

The consequence the blueprint records — that for an affine map `L` and a segment `[a, b]`
with midpoint `m`, the centre of `ext_s[L a, L b]` is `L m`, an affine map preserving
midpoints (`AffineMap.map_midpoint`) — is this statement composed with that one lemma, and is
not separately named. -/
theorem center_centredExtension {s : NNReal} {p q : E} (hpq : p ≠ q) :
    (centredExtension s hpq).center = _root_.midpoint ℝ p q := by
  set T : Tube s E := centredExtension s hpq
  set g : E := ‖q - p‖⁻¹ • (q - p)
  have hx : T.x = _root_.midpoint ℝ p q - (1 / 2 : ℝ) • g := by rfl
  have hy : T.y = _root_.midpoint ℝ p q + (1 / 2 : ℝ) • g := by rfl
  have hcm : T.center = T.midpoint := by
    change _root_.midpoint ℝ T.x T.y = (1 / 2 : ℝ) • (T.x + T.y)
    rw [midpoint_eq_smul_add, invOf_eq_inv, one_div]
  have hmid : T.midpoint = _root_.midpoint ℝ p q := by
    rw [Tube.midpoint, hx, hy]
    module
  change T.center = _root_.midpoint ℝ p q
  rw [hcm, hmid]

/-- **The unit direction of the centred extension** (blueprint
`lem:centredExtensionProperties`\ `item:centredExtCentre`, second half).

Read off `Tube.centredExtension` exactly as `Tube.center_centredExtension` is:
`Tube.direction` — the difference of the two core endpoints — is the unit vector
`g = (q - p) / ‖q - p‖` the extension was built along.

The two halves of blueprint item (iii) are two lemmas and not one conjunction because they are
independent facts about the same object, and the proof of `lem:rescalePullbackDilate` quotes
them separately. -/
theorem direction_centredExtension {s : NNReal} {p q : E} (hpq : p ≠ q) :
    (centredExtension s hpq).direction = ‖q - p‖⁻¹ • (q - p) := by
  change _root_.midpoint ℝ p q + (1 / 2 : ℝ) • (‖q - p‖⁻¹ • (q - p)) -
      (_root_.midpoint ℝ p q - (1 / 2 : ℝ) • (‖q - p‖⁻¹ • (q - p))) = ‖q - p‖⁻¹ • (q - p)
  module

/-! ### Volume and containment in the rescaling situation

The following estimates correspond to `lem:rescaleImageVolumeRatio` and `lem:coreOuterTube`
in the fine-normalization argument.

**The outer tube is volume-comparable to the rescaled image** (blueprint
`lem:rescaleImageVolumeRatio`).

In the rescaling situation, suppose `Φ_{T₀}(T)` contains the closed `C_N⁻¹ ρ`-neighbourhood
of *some* segment `[p, q]` of length `ℓ ∈ (0, 1]`, and write `V = ext_σ[Ψ(T.x), Ψ(T.y)]` and
`W = Ψ(T)`.  Then

```
|V| ≤ (C_{Tube.volume_le}(n) / c_{Tube.le_volume}(n)) * ℓ⁻¹ * C_N ^ (n-1) * (4 R) ^ n * |W|.
```

The intended route is two volume estimates and one cancellation.  Upper bound: `V` is a
`σ`-tube with `σ ≤ 1`, so `Tube.volume_le` gives `|V| ≤ C_{volume_le}(n) σ ^ (n-1)`.  Lower
bound: the homothety `h : z ↦ (z - T₀.x) / (4 R)` of `Tube.rescaleMap` divides every distance
by `4 R`, so `W = h(Φ_{T₀}(T))` contains the closed `r̂`-neighbourhood of a segment of length
`ℓ̂`, with `r̂ = C_N⁻¹ ρ / (4 R)` and `ℓ̂ = ℓ / (4 R)`; that neighbourhood is the image of the
carrier of an honest `(r̂ / ℓ̂)`-tube under the homothety of ratio `ℓ̂` about the midpoint of
the segment, so `Tube.le_volume` together with the volume law for an affine image
(`Kakeya.volume_affineImage`, as used in `Tube.volume_image_normalization`) gives
`|W| ≥ c_{le_volume}(n) * ℓ̂ * r̂ ^ (n-1)`.  Dividing and using `σ ≤ ρ` to cancel the powers
of `ρ` leaves the stated factor, the surviving `(σ / ρ) ^ (n-1)` being at most `1`.

At `n = 3` the dimensional ratio is `C_{volume_le}(3) / c_{le_volume}(3) = 36 / π < 12`, so
with `C_N ≤ R` and `ℓ ≥ 7/8` (the length `Tube.normalization_exists_subsegment` delivers) the
whole factor is at most `(4 R) ^ 6`, which is the comparability constant that blueprint
`def:ml1bootFineNormalizeCoreConstant`(iii) is stated at; that numerical step is
`Tube.rescale_outer_tube`, not this lemma, and it is available **only** at `n = 3`: the ratio
`κ(n) = C_{volume_le}(n) / c_{le_volume}(n)` grows like `Γ(n / 2 + 1)`, so it outgrows any
fixed power of `4 R` at the smallest admissible radius `R = C_N`, and the general-`n` reading
`(4 R) ^ (2 n)` of that numerical step is false.

**The outer tube of a rescaled tube** (blueprint `lem:coreOuterTube`).

In the rescaling situation (`Tube.IsRescalingSituation`) assume in addition `ρ ≤ 4 σ`, that the
distortion package `Tube.IsNormalizationDistortion T₀ T` holds, and that
`Φ_{T₀}(T) ⊆ B̄(T₀.x, R)`.  Write `V = ext_σ[Ψ(T.x), Ψ(T.y)]` and `W = Ψ(T)`.  Then `V` is a
`σ`-tube with

```
W ⊆ V ⊆ B̄(Ψ(T₀.x), 1) = B̄(0, 1),      |V| ≤ (4 R) ^ 6 |W|      (n = 3).
```

Three claims, and the homothety `h : z ↦ (z - T₀.x) / (4 R)` of `Tube.rescaleMap` divides
every distance by `4 R` and sends `T₀.x` to `0`.

*Thickness.*  By `IsNormalizationDistortion.image_subset_cthickening`, `W = h(Φ_{T₀}(T))`
lies in the closed `(C_N ρ / (4 R))`-neighbourhood of `[Ψ(T.x), Ψ(T.y)]`, and
`C_N ρ / (4 R) ≤ ρ / 4 ≤ σ` by `C_N ≤ R` and the added hypothesis `ρ ≤ 4 σ`.  By
`IsNormalizationDistortion.dist_le_C`, `dist (Ψ T.x) (Ψ T.y) = dist (Φ T.x) (Φ T.y) / (4 R)
≤ C_N / (4 R) ≤ 1/4 ≤ 1`, so `Tube.cthickening_subset_centredExtension` puts the closed
`σ`-neighbourhood of `[Ψ(T.x), Ψ(T.y)]` inside `V`, and hence `W ⊆ V`.  This is the one step
at which the value `4 R` of the homothety ratio is used: at ratio `R` the chain would read
`C_N ρ / R ≤ ρ ≤ σ`, whose second step is false whenever `ρ > 1/4`, that is exactly in the
regime where the output scale `σ = min (ρ, 1/4)` is truncated.

*Position.*  By `hball` and `T.x, T.y ∈ T.carrier`, `Ψ(T.x), Ψ(T.y) ∈ B̄(0, 1/4)`, and
`σ ≤ 1/4`, so `Tube.centredExtension_subset_closedBall` at `z = 0 = Ψ(T₀.x)` gives
`V ⊆ B̄(0, 1)`.  This is where `σ ≤ 1/4` itself is spent.

*Volume.*  This is `Tube.volume_centredExtension_le_mul_volume_rescale_image`, whose
hypothesis is `IsNormalizationDistortion.exists_subsegment` read at `ℓ = 7/8`, together with
the numerics recorded there: at `n = 3` the factor is at most
`(36/π) * (8/7) * C_N ^ 2 * (4 R) ^ 3 ≤ (4 R) ^ 6`, using `C_N ≤ R`, and indeed
`C_N (3) = 64`, so `(4 R) ^ 3 ≥ 256 ^ 3` leaves three orders of magnitude of room.

## Why the volume clause is stated at `n = 3`

The hypothesis `hn : Module.finrank ℝ E = 3` is spent on the volume clause only; the two
inclusions hold in every dimension.  It cannot be dropped, because the general-`n` reading
`|V| ≤ (4 R) ^ (2 n) |W|` of that clause is **false**.  Feeding the general estimate
`Tube.volume_centredExtension_le_mul_volume_rescale_image` at `ℓ = 7/8` and the smallest
admissible radius `R = C_N = 2 ^ (n + 3)` — so `4 R = 2 ^ (n + 5)` — the required inequality
`κ(n) * (8/7) * C_N ^ (n-1) ≤ (4 R) ^ n` reduces, with
`volume_le.C n = 2 ^ (n + 1)` and `le_volume.c n = √π ^ n / Γ(n / 2 + 1) / 3`, to
`Γ(n / 2 + 1) ≤ (7/6) * (4 √π) ^ n`.  The left side is superexponential in `n` and the right
side exponential, so the inequality holds with enormous room at `n = 3`
(`1.33 ≤ 416`) and fails for `n` past roughly `274`.  Since both volume estimates are sharp up
to their dimensional constants, the failure is a failure of the statement, not of the route.
The general-dimension form of this clause is
`Tube.volume_centredExtension_le_mul_volume_rescale_image` itself, with `κ(n)` explicit; the
blueprint likewise claims `(4 R) ^ 6` at `n = 3` only. -/

/-! ### The metric layer of `Tube.rescaleMap`, the three pullbacks and the count

The declarations below are the downstairs-selection route of blueprint
`section8_finenormalize_select.tex` and `section8_finenormalize_count.tex`: two equation
lemmas for `Tube.rescaleMap`, then the three pullbacks `lem:rescalePullbackAxis`,
`lem:rescalePullbackVector`, `lem:rescalePullbackDilate`, then the constant
`def:essDistinctTubesInSelfDilateConstant` and the count `lem:essDistinctTubesInSelfDilate`,
which is the single **open leaf** of the route.

## Divergence from the informal statement: the pullbacks are stated forwards

The blueprint writes the first two pullbacks with `Ψ⁻¹`, which presupposes the affine
*equivalence* underlying `Tube.rescaleMap`.  Building that equivalence would make every
statement below carry the two proof terms `0 < θ` and `R ≠ 0` inside the term `Ψ`, and would
make the statements harder to apply, since a consumer holds `Ψ z ∈ …` and not
`z = Ψ⁻¹ …`.  They are therefore stated in the equivalent *forward* form, which mentions only
the affine map `Tube.rescaleMap`:

* `Ψ⁻¹(m̂ + α f̂) = m + α' f` becomes `Ψ(m + α' f) = Ψ m + α f̂`;
* `u = Ψ⁻¹(w + v) - Ψ⁻¹ w` becomes the hypothesis `Ψ (z + u) = Ψ z + v`;
* `Ψ⁻¹(c · V) ⊆ c' · T` becomes `Ψ ⁻¹' (c · V).carrier ⊆ (c' · T).carrier`, which is the same
  set inclusion for a bijective `Ψ` and is what the fibre bound actually uses.

`Tube.rescaleMap` is injective for `0 < θ` and `R ≠ 0` (`Tube.normalization_injective` and the
homothety), so the forward forms are equivalent to the blueprint ones and not weaker; the Lean
names are the blueprint's, so the `\lean{…}` links stay valid. -/

/-- The defining formula for `Tube.rescaleMap`: the normalization recentred at `T₀.x` and
divided by `4 R`. -/
theorem rescaleMap_apply (T₀ : Tube θ E) (R : ℝ) (z : E) :
    T₀.rescaleMap R z = (4 * R)⁻¹ • (T₀.normalization z - T₀.x) := by
  show (4 * R)⁻¹ • (-T₀.x + T₀.normalization z) = _
  rw [neg_add_eq_sub]

@[simp]
theorem rescaleMap_apply_x (T₀ : Tube θ E) (R : ℝ) : T₀.rescaleMap R T₀.x = 0 := by
  rw [rescaleMap_apply, normalization_apply_x, sub_self, smul_zero]

/-! ### The three pullbacks and the count: the informal statements

The following geometric estimates describe the downstairs-selection route.

**The rescaling pulls the image direction back to the inner direction** (blueprint
`lem:rescalePullbackAxis`).

Write `m = T.center`, `f = T.direction`, `â = Ψ(T.x)`, `b̂ = Ψ(T.y)` and
`f̂ = (b̂ - â)/‖b̂ - â‖` for the unit direction of the image core.  The displacement `α • f̂`
*along the image core* pulls back to a displacement `α' • f` along the inner core — with no
transverse error at all — and `|α'| ≤ 4 R |α|`.

Stated forwards (see the section docstring): the assertion is that `α • f̂` is *hit* by such a
displacement, `Ψ(m + α' f) = Ψ m + α f̂`, which for the injective `Ψ` is the blueprint's
`Ψ⁻¹(m̂ + α f̂) = m + α' f`.  The scalar `α • ‖b̂ - â‖⁻¹` is folded into one coefficient of
`b̂ - â`, so that the unit vector `f̂` need not be named.

The linear part of `Ψ` is `(4 R)⁻¹ A` with `A` the linear part of `Φ_{T₀}`, so
`b̂ - â = (4 R)⁻¹ A f` and `α' = 4 R α / ‖A f‖`; the bound is `‖A f‖ ≥ ‖f‖ = 1`, which is
`Tube.dist_le_dist_normalization` and is where `0 < θ ≤ 1` is spent.

**Pulling a transverse displacement back through the rescaling** (blueprint
`lem:rescalePullbackVector`).

Suppose the inner direction `f = T.direction` is nearly parallel to the ambient axis
`e = T₀.direction`, `‖f - ⟪e, f⟫ e‖ ≤ κ θ`, and let `v` be a displacement of norm at most `s`
upstairs.  Its pullback `u` — the vector with `Ψ(z + u) = Ψ z + v`, which does not depend on
`z` — splits along and across `f` as

```
|⟪f, u⟫| ≤ 4 R (1 + θ) s,        ‖u - ⟪f, u⟫ f‖ ≤ 4 R (κ + 1) θ s.
```

The gain is the second bound: *perpendicularly to the inner direction* the pullback is smaller
by a factor `θ` than along it, which is what turns a `σ`-thickness upstairs into a
`τ`-thickness downstairs.  The parallel component is written `|⟪f, u⟫|` rather than
`‖⟪f, u⟫ • f‖`; the two agree because `‖f‖ = 1` (`Tube.norm_direction`).

The linear part of `Ψ⁻¹` is `4 R A⁻¹`, which is multiplication by `4 R` on `ℝ ∙ e` and by
`4 R θ` on `e^⊥`, so `u = 4 R (v^∥ + θ v^⊥)`; the transverse bound then uses
`‖e - ⟪f, e⟫ f‖ = ‖f - ⟪e, f⟫ e‖`, both sides being `sin ∠(e, f)`.  No upper bound on `θ` is
needed, only `0 < θ`, which is what makes `Ψ` invertible.

**Pulling a dilate of the outer tube back into a dilate of the inner tube** (blueprint
`lem:rescalePullbackDilate`).

In the rescaling situation, with the inner direction nearly parallel to the ambient axis
(`‖f - ⟪e, f⟫ e‖ ≤ κ θ`) and `V = ext_σ[Ψ(T.x), Ψ(T.y)]` the outer tube of the image core,
every point whose image lies in the dilate `c · V` lies in the dilate
`(4 (κ + 2) R c) · T` downstairs.

This is the step that makes a *downstairs* selection possible: a failure of essential
distinctness upstairs is turned by `Kakeya.Tube.tubeOverlapCoreClose` into a containment in
`C_n · V`, and this lemma turns that into a containment in a bounded dilate of the original
`τ`-tube, where `Tube.essDistinctTubesInSelfDilate` counts.

The two values used are `κ = 2`, which is `Tube.perp_norm_core_sub_le_of_subset` for
`T ⊆ T₀`, and `κ = 4`, which is `Tube.perp_norm_core_sub_le_of_subset_dilate` at `c = 2` for
`T ⊆ 2 · T₀`.

Assembly, from the two pullbacks above: `Kakeya.Tube.dilate_carrier_eq_cthickening` together
with `Tube.center_centredExtension` and `Tube.direction_centredExtension` writes a point of
`c · V` as `Ψ(T.center) + t • f̂ + v` with `|t| ≤ c / 2` and `‖v‖ ≤ c σ`; pulling back with
`Tube.rescale_symm_apply_add_smul` and `Tube.norm_rescale_symm_vector_le` at `s = c σ` puts
the point within `4 R (κ + 1) c τ` of the segment of length `8 R c` centred at `T.center`
along `f`, using `θ ≤ 1` and `σ ≤ 1/4` along `f` and `σ ≤ τ / θ` across it — both of which are
fields of `Tube.IsRescalingSituation`. -/

/-- The thin-regime summand of `Tube.essDistinctTubesInSelfDilate.C`: the parameter-space
packing count `K_thin(n) c ^ (2n)` with `K_thin(n) = parameterRegion.C n ·
(coveringNumber_mul_pow_le_volume_cthickening.C (2n-1))⁻¹ · (32n)^(2n-1)`. -/
noncomputable abbrev essDistinctTubesInSelfDilate.thinC (n : ℕ) (c : ℝ) : NNReal :=
  24 * (2 ^ (n - 1) * Metric.coveringNumber_mul_pow_le_volume_cthickening.C (n - 1)) ^ 2
      * (Metric.coveringNumber_mul_pow_le_volume_cthickening.C (2 * n - 1))⁻¹
      * (32 * (n : NNReal)) ^ (2 * n - 1) * c.toNNReal ^ (2 * n)
/-- The fat-regime summand of `Tube.essDistinctTubesInSelfDilate.C`: the crude ball count
`K_fat(n) c ^ (4n)` with `K_fat(n) = 6^(2n) · card_le_of_EssDistinct.C n`. -/
noncomputable abbrev essDistinctTubesInSelfDilate.fatC (n : ℕ) (c : ℝ) : NNReal :=
  6 ^ (2 * n) * (card_le_of_EssDistinct.C n).toNNReal * c.toNNReal ^ (4 * n)
/-- **The constant `C_{lem:essDistinctTubesInSelfDilate}(n, c)`** of
`Tube.essDistinctTubesInSelfDilate` (blueprint `def:essDistinctTubesInSelfDilateConstant`).

It is defined in Lean as the sum `essDistinctTubesInSelfDilate.thinC n c +
essDistinctTubesInSelfDilate.fatC n c` of the thin- and fat-regime summands:

```
C(n, c) = K_thin(n) c ^ (2n) + K_fat(n) c ^ (4n),
K_thin(n) = 24 ω_{n-1}² C_{lem:separatedSetCardBound}(2n-1) (32 n) ^ (2n-1),
K_fat(n)  = 6 ^ (2n) C_{lem:essDistinctTubeCount}(n).
```

The two summands are the two summands of `Tube.comparableReplacement.Kstar` — the thin and fat
regimes of `Tube.essDistinctTubesInDilate` — each carrying its own power of the *free*
dilation ratio `c` in place of the fixed ratio `C_n` of that lemma.  As there,
`ω_d = 2 ^ d * Metric.coveringNumber_mul_pow_le_volume_cthickening.C d` and the packing
constant `C_{lem:separatedSetCardBound}(d) = 2 ^ d / ω_d` is the inverse of that abbreviation.
The constant is nondecreasing in `c` and depends only on `n` and `c`: not on the scale, not on
the tube and not on the family.

**The value is verified**: `Tube.essDistinctTubesInSelfDilate` proves the bound with exactly
this constant.  The fat summand is the computation of `Tube.essDistinctTubesInFatDilate` with
`C_n` replaced by `c` and `C = 1`; the thin summand is what the parameter-space packing route
of `Tube.essDistinctTubesInThinDilate` produces under the same substitution, carried out here
as a reproof rather than a citation (`Tube.freeParameterMap` and the free-ratio lemmas
around it).  It is written down rather than left existential so that the numerical obligation
of `Kakeya.ml1Boot.exists_fineNormalization` can be checked at all.

The ratio is a real number, as `Kakeya.Tube.dilate` takes a real ratio, and is truncated by
`Real.toNNReal`; the intended range is `1 ≤ c`, where the truncation is inert. -/
noncomputable abbrev essDistinctTubesInSelfDilate.C (n : ℕ) (c : ℝ) : NNReal :=
  essDistinctTubesInSelfDilate.thinC n c + essDistinctTubesInSelfDilate.fatC n c

/-- The fat regime `δ > 1/(4c)` of `Tube.essDistinctTubesInSelfDilate` (blueprint
`note:essDistinctTubesInDilateRegimes`): `dilate_carrier_eq_cthickening` puts `c · T` inside
`B̄(T.center, 3c/2)`, `Tube.card_le_of_EssDistinct` at radius `3c/2` counts there, and
`(3c/2)/δ < 6 c²` gives the `K_fat(n) c ^ (4n)` summand. -/
private lemma essDistinctTubesInSelfDilate.fat_bound {ι : Type*} [Nontrivial E]
    {δ : NNReal} {c : ℝ} (hc : 1 ≤ c) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (T : Tube δ E)
    (a : Finset ι) (U : ι → Tube δ E)
    (hUED : (↑a : Set ι).Pairwise fun i j => IsEssentiallyDistinct (U i).carrier (U j).carrier)
    (hUT : ∀ j ∈ a, (U j).carrier ⊆ (Kakeya.Tube.dilate T c).carrier)
    (hρ : 1 / (4 * c) < (δ : ℝ)) :
    (a.card : ENNReal)
      ≤ (essDistinctTubesInSelfDilate.fatC (Module.finrank ℝ E) c : ENNReal) := by
  classical
  set n : ℕ := Module.finrank ℝ E
  let R0 : ℝ := 3 * c / 2
  -- positivity of the constants
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hcposR : (0 : ℝ) < c := by exact_mod_cast hc0
  have hδ0R : 0 < (δ : ℝ) := by exact_mod_cast hδ0
  have hδ1R : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1
  have hCa0 : 0 < card_le_of_EssDistinct.C n := by simpa [n] using card_le_of_EssDistinct.C_pos
  -- the dilate `c · T` sits inside the ball of radius `3c/2` about `T.center`
  have hseg_ball :
      segment ℝ (T.center - (c / 2) • T.direction) (T.center + (c / 2) • T.direction)
        ⊆ closedBall T.center (c / 2) := by
    refine (convex_closedBall T.center (c / 2)).segment_subset ?_ ?_
    · rw [Metric.mem_closedBall, dist_eq_norm]
      calc
        ‖(T.center - (c / 2) • T.direction) - T.center‖
            = ‖(c / 2) • T.direction‖ := by
              rw [← norm_neg]
              congr 1
              module
        _ = c / 2 := by
          rw [norm_smul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ c / 2),
              T.norm_direction, mul_one]
        _ ≤ c / 2 := le_rfl
    · rw [Metric.mem_closedBall, dist_eq_norm]
      calc
        ‖(T.center + (c / 2) • T.direction) - T.center‖
            = ‖(c / 2) • T.direction‖ := by
              congr 1
              module
        _ = c / 2 := by
          rw [norm_smul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ c / 2),
              T.norm_direction, mul_one]
        _ ≤ c / 2 := le_rfl
  have hct_sub :
      cthickening (c * (δ : ℝ))
          (segment ℝ (T.center - (c / 2) • T.direction) (T.center + (c / 2) • T.direction))
        ⊆ closedBall T.center (c / 2 + c * (δ : ℝ)) := by
    intro z hz
    rw [isCompact_segment.cthickening_eq_biUnion_closedBall
        (by positivity : (0 : ℝ) ≤ c * (δ : ℝ))] at hz
    rw [Set.mem_iUnion₂] at hz
    obtain ⟨w, hwseg, hwz⟩ := hz
    rw [Metric.mem_closedBall] at hwz ⊢
    calc
      dist z T.center ≤ dist z w + dist w T.center := dist_triangle z w T.center
      _ ≤ c * (δ : ℝ) + c / 2 := by
        exact add_le_add hwz (by
          have := hseg_ball hwseg
          rwa [Metric.mem_closedBall] at this)
      _ = c / 2 + c * (δ : ℝ) := by ring
  have hdilate_ball : (Kakeya.Tube.dilate T c).carrier ⊆ closedBall T.center (3 * c / 2) := by
    rw [dilate_carrier_eq_cthickening T hc0]
    refine hct_sub.trans ?_
    apply Metric.closedBall_subset_closedBall
    have hcδ : c * (δ : ℝ) ≤ c := mul_le_of_le_one_right hcposR.le hδ1R
    nlinarith
  -- translate by `-T.center`: essential distinctness and the ball are preserved
  have hU'ball : ∀ i ∈ a, ((U i).vadd (-T.center)).carrier ⊆ closedBall (0 : E) R0 := by
    intro i hi z hz
    rw [Tube.vadd_carrier] at hz
    rcases hz with ⟨x, hx, rfl⟩
    have hx_mem : x ∈ closedBall T.center R0 := hdilate_ball (hUT i hi hx)
    rw [Metric.mem_closedBall] at hx_mem
    rw [Metric.mem_closedBall]
    rw [dist_comm]
    change dist 0 (-T.center +ᵥ x) ≤ R0
    rw [vadd_eq_add]
    calc
      dist 0 (-T.center + x) = ‖T.center - x‖ := by
        rw [dist_eq_norm]
        congr 1
        abel
      _ = dist x T.center := by
        rw [dist_eq_norm]
        rw [← norm_neg]
        congr 1
        abel
      _ ≤ R0 := hx_mem
  have hU'ED : (↑a : Set ι).Pairwise
      (fun i j => IsEssentiallyDistinct ((U i).vadd (-T.center)).carrier
        ((U j).vadd (-T.center)).carrier) := by
    intro i hi j hj hij
    rw [Tube.vadd_carrier]
    change IsEssentiallyDistinct ((fun x : E => -T.center +ᵥ x) '' (U i).carrier)
        ((fun x : E => -T.center +ᵥ x) '' (U j).carrier)
    simp only [vadd_eq_add]
    exact (Kakeya.isEssentiallyDistinct_translate (U i).carrier (U j).carrier (-T.center)).mpr
      (hUED hi hj hij)
  -- scale comparison: `(3c/2)/δ ≤ 6c²`
  have hratio : R0 / (δ : ℝ) ≤ 6 * c ^ 2 := by
    have hden0 : 0 < (δ : ℝ) := hδ0R
    rw [div_le_iff₀ hden0]
    have hmul : 6 * c ^ 2 * (1 / (4 * c)) < 6 * c ^ 2 * (δ : ℝ) :=
      mul_lt_mul_of_pos_left hρ (by positivity : (0 : ℝ) < 6 * c ^ 2)
    have hR0_ge : R0 ≤ 6 * c ^ 2 * (δ : ℝ) := by
      have hcalc : 6 * c ^ 2 * (1 / (4 * c)) = 3 * c / 2 := by
        field_simp [hc0.ne']
        ring
      dsimp [R0]
      linarith
    exact hR0_ge
  -- assemble
  have hcard := Tube.card_le_of_EssDistinct (E := E) (δ := δ) hδ0 R0 a
      (fun i => (U i).vadd (-T.center)) hU'ball hU'ED
  have hRHSbase :
      (a.card : ℝ) ≤ card_le_of_EssDistinct.C n * ((6 * c ^ 2) ^ (2 * n)) := by
    calc
      (a.card : ℝ) ≤ card_le_of_EssDistinct.C n * (R0 / (δ : ℝ)) ^ (2 * n) := by
        simpa [n] using hcard
      _ ≤ card_le_of_EssDistinct.C n * ((6 * c ^ 2) ^ (2 * n)) := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (div_nonneg (by dsimp [R0]; positivity) hδ0R.le) hratio (2 * n))
          (le_of_lt hCa0)
  -- convert to ENNReal
  let fatNN : NNReal := essDistinctTubesInSelfDilate.fatC n c
  have hfatNN : (fatNN : ℝ) = 6 ^ (2 * n) * card_le_of_EssDistinct.C n * c ^ (4 * n) := by
    dsimp [fatNN, essDistinctTubesInSelfDilate.fatC]
    rw [max_eq_left hcposR.le, max_eq_left (le_of_lt hCa0)]
  have hexp : (c ^ 2) ^ (2 * n) = c ^ (4 * n) := by
    calc
      (c ^ 2) ^ (2 * n) = c ^ (2 * (2 * n)) := (pow_mul c 2 (2 * n)).symm
      _ = c ^ (4 * n) := by congr 1; omega
  have hRHS : card_le_of_EssDistinct.C n * ((6 * c ^ 2) ^ (2 * n)) = (fatNN : ℝ) := by
    calc
      card_le_of_EssDistinct.C n * ((6 * c ^ 2) ^ (2 * n))
          = card_le_of_EssDistinct.C n * (6 ^ (2 * n) * (c ^ 2) ^ (2 * n)) := by
            rw [mul_pow]
      _ = card_le_of_EssDistinct.C n * (6 ^ (2 * n) * c ^ (4 * n)) := by rw [hexp]
      _ = 6 ^ (2 * n) * card_le_of_EssDistinct.C n * c ^ (4 * n) := by ring
      _ = (fatNN : ℝ) := by rw [hfatNN]
  have hXnn : 0 ≤ (fatNN : ℝ) := by rw [hfatNN]; positivity
  have hcR : (a.card : ℝ) ≤ (fatNN : ℝ) := le_trans hRHSbase (le_of_eq hRHS)
  have hmc : (a.card : ENNReal) ≤ ENNReal.ofReal (fatNN : ℝ) := by
    rw [← ENNReal.ofReal_natCast a.card]
    exact ENNReal.ofReal_le_ofReal hcR
  have hof : ENNReal.ofReal (fatNN : ℝ) = (fatNN : ENNReal) :=
    ENNReal.ofReal_coe_nnreal
  exact hof ▸ hmc

/-- Free-ratio axial resolution `κ_c(n) = 1 / (32 n c)`, replacing
`Tube.axialSeparation.kappa n C` — which hard-wires `Tube.tubeOverlapCoreClose.C n` — in the
free-ratio mirror of the thin-regime packing count. -/
private noncomputable def freeKappa (n : ℕ) (c : ℝ) : ℝ :=
  1 / (32 * (n : ℝ) * c)

/-- Free-ratio parameter map: `Tube.parameterMap` with the axial rescaling dividing by a free
axial resolution `κ` instead of by `Tube.axialSeparation.kappa`, and with the inner tubes at the
same scale as the ambient one. -/
private noncomputable def freeParameterMap {δ : NNReal} (T : Tube δ E) (κ : ℝ) (U : Tube δ E) :
    parameterSpace T :=
  WithLp.toLp 2
    (1 / (4 * (Module.finrank ℝ E : ℝ)) * (δ : ℝ) / κ
        * inner ℝ (U.x - T.center) T.direction,
      WithLp.toLp 2 (((ℝ ∙ T.direction)ᗮ).orthogonalProjectionOnto (U.x - T.center),
        ((ℝ ∙ T.direction)ᗮ).orthogonalProjectionOnto (U.y - T.center)))

/-- Free-ratio form of `Tube.lt_dist_parameterMap_of_max_lt`: a separation of the three
coordinates is a separation in `Tube.parameterSpace`.  The argument is pure `WithLp` coordinate
bookkeeping and is ratio-agnostic; only the axial rescaling factor differs. -/
private lemma lt_dist_freeParameterMap_of_max_lt {δ : NNReal} (T : Tube δ E) (κ : ℝ)
    (U U' : Tube δ E) {r : ℝ}
    (hrκ : 0 ≤ 1 / (4 * (Module.finrank ℝ E : ℝ)) * (δ : ℝ) / κ)
    (hr : r < max (max ‖U.x - U'.x - inner ℝ T.direction (U.x - U'.x) • T.direction‖
                  ‖U.y - U'.y - inner ℝ T.direction (U.y - U'.y) • T.direction‖)
              (1 / (4 * (Module.finrank ℝ E : ℝ)) * (δ : ℝ) / κ
                * |inner ℝ (U.x - U'.x) T.direction|)) :
    r < dist (freeParameterMap T κ U) (freeParameterMap T κ U') := by
  let P : parameterSpace T := freeParameterMap T κ U
  let P' : parameterSpace T := freeParameterMap T κ U'
  let cstar : ℝ := 1 / (4 * (Module.finrank ℝ E : ℝ)) * (δ : ℝ) / κ
  have hcstar_nonneg : 0 ≤ cstar := by
    dsimp [cstar]
    exact hrκ
  have hcanc_x : U.x - U'.x = (U.x - T.center) - (U'.x - T.center) := by abel
  have hcanc_y : U.y - U'.y = (U.y - T.center) - (U'.y - T.center) := by abel
  have hinner_ax : inner ℝ (U.x - T.center) T.direction - inner ℝ (U'.x - T.center) T.direction
      = inner ℝ (U.x - U'.x) T.direction := by
    rw [← inner_sub_left]
    rw [hcanc_x]
  have haxial : |WithLp.fst P - WithLp.fst P'| = cstar * |inner ℝ (U.x - U'.x) T.direction| := by
    have hin : WithLp.fst P - WithLp.fst P' = cstar * inner ℝ (U.x - U'.x) T.direction := by
      calc
        WithLp.fst P - WithLp.fst P'
            = cstar * inner ℝ (U.x - T.center) T.direction
                - cstar * inner ℝ (U'.x - T.center) T.direction := by
              simp [P, P', freeParameterMap, cstar]
        _ = cstar * (inner ℝ (U.x - T.center) T.direction - inner ℝ (U'.x - T.center) T.direction) := by
            rw [mul_sub]
        _ = cstar * inner ℝ (U.x - U'.x) T.direction := by rw [hinner_ax]
    rw [hin, abs_mul, abs_of_nonneg hcstar_nonneg]
  have hperp_x : ((ℝ ∙ T.direction)ᗮ).orthogonalProjectionOnto (U.x - U'.x)
      = ((ℝ ∙ T.direction)ᗮ).orthogonalProjectionOnto (U.x - T.center)
          - ((ℝ ∙ T.direction)ᗮ).orthogonalProjectionOnto (U'.x - T.center) := by
    rw [hcanc_x]
    exact map_sub ((ℝ ∙ T.direction)ᗮ).orthogonalProjectionOnto (U.x - T.center) (U'.x - T.center)
  have hperp_y : ((ℝ ∙ T.direction)ᗮ).orthogonalProjectionOnto (U.y - U'.y)
      = ((ℝ ∙ T.direction)ᗮ).orthogonalProjectionOnto (U.y - T.center)
          - ((ℝ ∙ T.direction)ᗮ).orthogonalProjectionOnto (U'.y - T.center) := by
    rw [hcanc_y]
    exact map_sub ((ℝ ∙ T.direction)ᗮ).orthogonalProjectionOnto (U.y - T.center) (U'.y - T.center)
  have hT1 : ‖WithLp.fst (WithLp.snd P) - WithLp.fst (WithLp.snd P')‖
      = ‖U.x - U'.x - inner ℝ T.direction (U.x - U'.x) • T.direction‖ := by
    rw [show WithLp.fst (WithLp.snd P) = ((ℝ ∙ T.direction)ᗮ).orthogonalProjectionOnto (U.x - T.center) by
        simp [P, freeParameterMap]]
    rw [show WithLp.fst (WithLp.snd P') = ((ℝ ∙ T.direction)ᗮ).orthogonalProjectionOnto (U'.x - T.center) by
        simp [P', freeParameterMap]]
    rw [← hperp_x]
    exact (Submodule.norm_orthogonalProjectionOnto_perp_span_singleton T.norm_direction (U.x - U'.x)).2
  have hT2 : ‖WithLp.snd (WithLp.snd P) - WithLp.snd (WithLp.snd P')‖
      = ‖U.y - U'.y - inner ℝ T.direction (U.y - U'.y) • T.direction‖ := by
    rw [show WithLp.snd (WithLp.snd P) = ((ℝ ∙ T.direction)ᗮ).orthogonalProjectionOnto (U.y - T.center) by
        simp [P, freeParameterMap]]
    rw [show WithLp.snd (WithLp.snd P') = ((ℝ ∙ T.direction)ᗮ).orthogonalProjectionOnto (U'.y - T.center) by
        simp [P', freeParameterMap]]
    rw [← hperp_y]
    exact (Submodule.norm_orthogonalProjectionOnto_perp_span_singleton T.norm_direction (U.y - U'.y)).2
  have hc : max (max ‖U.x - U'.x - inner ℝ T.direction (U.x - U'.x) • T.direction‖
                  ‖U.y - U'.y - inner ℝ T.direction (U.y - U'.y) • T.direction‖)
              (cstar * |inner ℝ (U.x - U'.x) T.direction|) ≤ dist P P' := by
    simpa [hT1, hT2, haxial, P, P'] using Tube.max_coord_dist_le_dist T P P'
  simpa [cstar, P, P'] using lt_of_lt_of_le hr hc

/-- Free-ratio form of `Tube.axial_separation_of_essDistinct`: two essentially distinct
`δ`-tubes inside `c · T` have parameters separated at the resolution `δ / (16 n)`.

This is the one step of the thin-regime route that the fixed-ratio lemma cannot supply, since
that lemma bakes `Tube.tubeOverlapCoreClose.C n` into its dilation hypotheses *and* into
`Tube.axialSeparation.kappa`.  Here the ratio is free and the axial resolution is
`Tube.freeKappa n c`.  No upper bound on `c` is needed. -/
private lemma free_separation_essDistinct [Nontrivial E] {δ : NNReal} {c : ℝ} (hc : 1 ≤ c)
    (hδ0 : 0 < δ) (hδ : (δ : ℝ) ≤ 1 / (4 * c)) (T : Tube δ E) (U U' : Tube δ E)
    (hU : U.carrier ⊆ (Kakeya.Tube.dilate T c).carrier)
    (hU' : U'.carrier ⊆ (Kakeya.Tube.dilate T c).carrier)
    (hUo : 0 ≤ inner ℝ U.direction T.direction)
    (hU'o : 0 ≤ inner ℝ U'.direction T.direction)
    (hED : IsEssentiallyDistinct U.carrier U'.carrier) :
    1 / 4 * (1 / (4 * (Module.finrank ℝ E : ℝ))) * (δ : ℝ)
      < max (max ‖U.x - U'.x - inner ℝ T.direction (U.x - U'.x) • T.direction‖
              ‖U.y - U'.y - inner ℝ T.direction (U.y - U'.y) • T.direction‖)
          ((1 / (4 * (Module.finrank ℝ E : ℝ))) * (δ : ℝ)
            / (1 / (32 * (Module.finrank ℝ E : ℝ) * c))
            * |inner ℝ (U.x - U'.x) T.direction|) := by
  classical
  set n : ℕ := Module.finrank ℝ E
  set cstar : ℝ := 1 / (4 * (n : ℝ))
  set κ : ℝ := 1 / (32 * (n : ℝ) * c)
  set η : ℝ := 1 / 4 * cstar * (δ : ℝ)
  set α0 : ℝ := inner ℝ (U.x - U'.x) T.direction
  set u : E := (U.x - U'.x) - α0 • T.direction
  set β0 : ℝ := inner ℝ (U.y - U'.y) T.direction
  set w : E := (U.y - U'.y) - β0 • T.direction
  set α : ℝ := -α0 * inner ℝ T.direction U.direction
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast Module.finrank_pos (R := ℝ) (M := E)
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hcne : c ≠ 0 := ne_of_gt hc0
  have hc1r : (1 : ℝ) ≤ c := hc
  have hδr : 0 < (δ : ℝ) := by exact_mod_cast hδ0
  have hδnr : 0 ≤ (δ : ℝ) := le_of_lt hδr
  have hδ1 : δ ≤ 1 := by
    have hbig : (1 / (4 * c) : ℝ) ≤ 1 := by
      rw [div_le_one (by positivity : 0 < 4 * c)]
      nlinarith [hc]
    exact_mod_cast (hδ.trans hbig)
  have hcs : 0 < cstar := by dsimp [cstar]; positivity
  have hη : 0 < η := by dsimp [η]; positivity
  have hcstar0 : cstar ≠ 0 := ne_of_gt hcs
  have hδ0r : (δ : ℝ) ≠ 0 := ne_of_gt hδr
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hκ0 : κ ≠ 0 := ne_of_gt hκ
  have hδrle : (δ : ℝ) ≤ 1 / (4 * c) := hδ
  -- bounded directions, from containment in `c · T`
  have hUpar := Tube.parameters_mem_of_subset_dilate_free hc0 T U hU
  have hU'par := Tube.parameters_mem_of_subset_dilate_free hc0 T U' hU'
  have hdirU : ‖U.direction - inner ℝ T.direction U.direction • T.direction‖
      ≤ 2 * c * (δ : ℝ) := hUpar.2.2
  have hdirU' : ‖U'.direction - inner ℝ T.direction U'.direction • T.direction‖
      ≤ 2 * c * (δ : ℝ) := hU'par.2.2
  have h2cδ : 2 * c * (δ : ℝ) ≤ 1 / 2 := by
    calc
      2 * c * (δ : ℝ) ≤ 2 * c * (1 / (4 * c)) := by
        exact mul_le_mul_of_nonneg_left hδ (by positivity : 0 ≤ 2 * c)
      _ = 1 / 2 := by
        field_simp [hcne]
        norm_num
  have hdirU12 : ‖U.direction - inner ℝ T.direction U.direction • T.direction‖ ≤ 1 / 2 :=
    hdirU.trans h2cδ
  have hdirU'12 : ‖U'.direction - inner ℝ T.direction U'.direction • T.direction‖ ≤ 1 / 2 :=
    hdirU'.trans h2cδ
  have hdir : |inner ℝ (U.direction - U'.direction) T.direction| ≤
      ‖(U.direction - inner ℝ T.direction U.direction • T.direction) -
        (U'.direction - inner ℝ T.direction U'.direction • T.direction)‖ :=
    abs_inner_sub_le_norm_perp_sub (e := T.direction) (f := U.direction) (f' := U'.direction)
      T.norm_direction U.norm_direction U'.norm_direction hUo hU'o hdirU12 hdirU'12
  by_contra hnot
  have hle : max (max ‖U.x - U'.x - inner ℝ T.direction (U.x - U'.x) • T.direction‖
              ‖U.y - U'.y - inner ℝ T.direction (U.y - U'.y) • T.direction‖)
          (cstar * (δ : ℝ) / κ * |inner ℝ (U.x - U'.x) T.direction|) ≤ η := by
    simpa [η, κ, cstar, u] using le_of_not_gt hnot
  have hle1 : ‖U.x - U'.x - inner ℝ T.direction (U.x - U'.x) • T.direction‖ ≤ η := by
    exact (le_max_left _ _).trans ((le_max_left _ _).trans hle)
  have hle2 : ‖U.y - U'.y - inner ℝ T.direction (U.y - U'.y) • T.direction‖ ≤ η := by
    exact (le_max_right _ _).trans ((le_max_left _ _).trans hle)
  have hle3 : cstar * (δ : ℝ) / κ * |α0| ≤ η := by
    exact (le_max_right _ _).trans hle
  have hηeq4 : η = cstar * (δ : ℝ) / 4 := by dsimp [η]; ring
  have hα0 : |α0| ≤ κ / 4 := by
    have hmul : cstar * (δ : ℝ) / κ * |α0| ≤ cstar * (δ : ℝ) / 4 := by
      simpa [hηeq4] using hle3
    have hposM : 0 < cstar * (δ : ℝ) / κ := by
      exact div_pos (mul_pos hcs hδr) hκ
    have hdiv : |α0| ≤ (cstar * (δ : ℝ) / 4) / (cstar * (δ : ℝ) / κ) :=
      (le_div_iff₀ hposM).mpr (by simpa [mul_comm] using hmul)
    have hid : (cstar * (δ : ℝ) / 4) / (cstar * (δ : ℝ) / κ) = κ / 4 := by
      field_simp [hcstar0, hδ0r, hκ0]
    rw [hid] at hdiv
    exact hdiv
  have hα0eqx : inner ℝ T.direction (U.x - U'.x) = α0 := by
    exact real_inner_comm (U.x - U'.x) T.direction
  have hu : ‖u‖ ≤ η := by
    dsimp [u]
    rw [← hα0eqx]
    exact hle1
  have hβ0eq_y : inner ℝ T.direction (U.y - U'.y) = β0 := by
    exact real_inner_comm (U.y - U'.y) T.direction
  have hw : ‖w‖ ≤ η := by
    dsimp [w]
    rw [← hβ0eq_y]
    exact hle2
  have hdecomp : U.x - U'.x = α0 • T.direction + u := by
    dsimp [u]; abel
  have hdectold : U.y - U'.y = β0 • T.direction + w := by
    dsimp [w]; abel
  have h2 : (U.y - U'.y) - (U.x - U'.x) = U.direction - U'.direction := by
    rw [show U.direction = U.y - U.x by rfl, show U'.direction = U'.y - U'.x by rfl]
    module
  have hβdiff : β0 - α0 = inner ℝ (U.direction - U'.direction) T.direction := by
    dsimp [β0, α0]
    rw [← inner_sub_left]
    rw [h2]
  have hperpdiff :
      (U.direction - inner ℝ T.direction U.direction • T.direction) -
        (U'.direction - inner ℝ T.direction U'.direction • T.direction) = w - u := by
    have hsub : (U.direction - inner ℝ T.direction U.direction • T.direction) -
        (U'.direction - inner ℝ T.direction U'.direction • T.direction)
        = (U.direction - U'.direction) - (inner ℝ T.direction U.direction - inner ℝ T.direction U'.direction) • T.direction := by
      module
    have hsub' : (U.direction - inner ℝ T.direction U.direction • T.direction) -
        (U'.direction - inner ℝ T.direction U'.direction • T.direction)
        = (U.direction - U'.direction) - inner ℝ T.direction (U.direction - U'.direction) • T.direction := by
      rw [hsub]
      congr 1
      congr 1
      rw [← inner_sub_right]
    have hwsu : w - u = (U.direction - U'.direction)
        - inner ℝ T.direction (U.direction - U'.direction) • T.direction := by
      dsimp [w, u, α0, β0]
      have h1 : (U.y - U'.y) - inner ℝ (U.y - U'.y) T.direction • T.direction
          - ((U.x - U'.x) - inner ℝ (U.x - U'.x) T.direction • T.direction)
          = (U.y - U'.y - (U.x - U'.x)) - (inner ℝ (U.y - U'.y) T.direction - inner ℝ (U.x - U'.x) T.direction) • T.direction := by
        module
      rw [h1]
      rw [h2]
      congr 1
      congr 1
      rw [← inner_sub_left]
      rw [h2]
      exact (real_inner_comm (U.direction - U'.direction) T.direction).symm
    exact hsub'.trans hwsu.symm
  have hperp_norm :
      ‖(U.direction - inner ℝ T.direction U.direction • T.direction) -
          (U'.direction - inner ℝ T.direction U'.direction • T.direction)‖ ≤ 2 * η := by
    rw [hperpdiff]
    calc
      ‖w - u‖ ≤ ‖w‖ + ‖u‖ := norm_sub_le w u
      _ ≤ η + η := add_le_add hw hu
      _ = 2 * η := by ring
  have hβ0a : |β0 - α0| ≤ 2 * η := by
    rw [hβdiff]
    exact hdir.trans hperp_norm
  have hperp_swap : ‖T.direction - inner ℝ T.direction U.direction • U.direction‖
      = ‖U.direction - inner ℝ T.direction U.direction • T.direction‖ := by
    let t : ℝ := inner ℝ T.direction U.direction
    have htU : inner ℝ T.direction U.direction = t := rfl
    have htV : inner ℝ U.direction T.direction = t := by
      rw [← htU]
      exact real_inner_comm T.direction U.direction
    have hsq_a : ‖T.direction - t • U.direction‖ ^ 2 = 1 - t ^ 2 := by
      rw [norm_sub_sq_real]
      simp [T.norm_direction, U.norm_direction, norm_smul, inner_smul_right, htU]
      ring_nf
    have hsq_b : ‖U.direction - t • T.direction‖ ^ 2 = 1 - t ^ 2 := by
      rw [norm_sub_sq_real]
      simp [T.norm_direction, U.norm_direction, norm_smul, inner_smul_right, htV]
      ring_nf
    have hsq : ‖T.direction - t • U.direction‖ ^ 2 = ‖U.direction - t • T.direction‖ ^ 2 := by
      rw [hsq_a, hsq_b]
    have hmain : ‖T.direction - t • U.direction‖ = ‖U.direction - t • T.direction‖ := by
      have ha : 0 ≤ ‖T.direction - t • U.direction‖ := norm_nonneg _
      have hb : 0 ≤ ‖U.direction - t • T.direction‖ := norm_nonneg _
      exact le_antisymm (le_of_sq_le_sq hsq.le hb) (le_of_sq_le_sq hsq.symm.le ha)
    rw [show inner ℝ T.direction U.direction = t by rfl]
    exact hmain
  have hperp1 : ‖T.direction - inner ℝ T.direction U.direction • U.direction‖
      ≤ 2 * c * (δ : ℝ) := by
    calc
      ‖T.direction - inner ℝ T.direction U.direction • U.direction‖
          = ‖U.direction - inner ℝ T.direction U.direction • T.direction‖ := hperp_swap
      _ ≤ 2 * c * (δ : ℝ) := hdirU
  have hslide : ‖-α0 • T.direction - α • U.direction‖
      = |α0| * ‖T.direction - inner ℝ T.direction U.direction • U.direction‖ := by
    have hvid : -α0 • T.direction - α • U.direction
        = -α0 • (T.direction - inner ℝ T.direction U.direction • U.direction) := by
      dsimp [α]
      module
    rw [hvid]
    rw [norm_smul]
    rw [show ‖(-α0 : ℝ)‖ = |α0| by exact (Real.norm_eq_abs (-α0)).trans (abs_neg α0)]
  have hslide_le : ‖-α0 • T.direction - α • U.direction‖ ≤ (κ / 4) * (2 * c * (δ : ℝ)) := by
    rw [hslide]
    exact mul_le_mul hα0 hperp1 (norm_nonneg _) (by positivity : 0 ≤ κ / 4)
  have hbU : |inner ℝ T.direction U.direction| ≤ 1 := by
    calc
      |inner ℝ T.direction U.direction| ≤ ‖T.direction‖ * ‖U.direction‖ := abs_real_inner_le_norm T.direction U.direction
      _ = 1 := by rw [T.norm_direction, U.norm_direction]; norm_num
  have hα4 : |α| ≤ κ / 4 := by
    dsimp [α]
    calc
      |-α0 * inner ℝ T.direction U.direction| = |α0| * |inner ℝ T.direction U.direction| := by
        rw [abs_mul, abs_neg]
      _ ≤ |α0| * 1 := by
        exact mul_le_mul_of_nonneg_left hbU (abs_nonneg α0)
      _ = |α0| := by ring
      _ ≤ κ / 4 := hα0
  have hκval : κ = 1 / (32 * (n : ℝ) * c) := rfl
  have hκcstar : κ / 4 ≤ cstar := by
    rw [hκval]
    dsimp [cstar]
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
    rw [div_le_iff₀ (by positivity : 0 < 32 * (n : ℝ) * c)]
    have hide : (1 / (4 * (n : ℝ))) * 4 * (32 * (n : ℝ) * c) = 32 * c := by
      field_simp [hn0]
    rw [hide]
    nlinarith only [hc]
  have hmain_eq : (κ / 4) * (2 * c * (δ : ℝ)) = η / 4 := by
    rw [hκval]
    dsimp [η, cstar]
    field_simp [hn0, hc0.ne']
    ring
  have hsliderr : (κ / 4) * (2 * c * (δ : ℝ)) ≤ η := by
    calc
      (κ / 4) * (2 * c * (δ : ℝ)) = η / 4 := hmain_eq
      _ ≤ η := div_le_self hη.le (by norm_num : (1 : ℝ) ≤ 4)
  have hp_id : U'.x - (U.x + α • U.direction) = (-α0 • T.direction - α • U.direction) - u := by
    dsimp [u]
    module
  have hpnorm : ‖U'.x - (U.x + α • U.direction)‖ ≤ cstar * (δ : ℝ) := by
    rw [hp_id]
    calc
      ‖(-α0 • T.direction - α • U.direction) - u‖ ≤ ‖-α0 • T.direction - α • U.direction‖ + ‖u‖ := norm_sub_le _ _
      _ ≤ (κ / 4) * (2 * c * (δ : ℝ)) + η := add_le_add hslide_le hu
      _ ≤ cstar * (δ : ℝ) := by nlinarith only [hsliderr, hηeq4, hη]
  have hp : dist U'.x (U.x + α • U.direction) ≤ 1 / (4 * (Module.finrank ℝ E : ℝ)) * (δ : ℝ) := by
    simpa [cstar, dist_eq_norm] using hpnorm
  have hq_id : U'.y - (U.y + α • U.direction)
      = (-α0 • T.direction - α • U.direction) - (β0 - α0) • T.direction - w := by
    dsimp [w]
    module
  have hbq : ‖(β0 - α0) • T.direction‖ ≤ |β0 - α0| := by
    rw [norm_smul, Real.norm_eq_abs, T.norm_direction]
    simp
  have hqnorm : ‖U'.y - (U.y + α • U.direction)‖ ≤ cstar * (δ : ℝ) := by
    rw [hq_id]
    calc
      ‖((-α0 • T.direction - α • U.direction) - (β0 - α0) • T.direction) - w‖
          ≤ ‖(-α0 • T.direction - α • U.direction) - (β0 - α0) • T.direction‖ + ‖w‖ := norm_sub_le _ _
      _ ≤ (‖-α0 • T.direction - α • U.direction‖ + ‖(β0 - α0) • T.direction‖) + ‖w‖ := by
            gcongr
            exact norm_sub_le (-α0 • T.direction - α • U.direction) ((β0 - α0) • T.direction)
      _ ≤ ‖-α0 • T.direction - α • U.direction‖ + |β0 - α0| + η := by
            nlinarith only [hbq, hw]
      _ ≤ (κ / 4) * (2 * c * (δ : ℝ)) + 2 * η + η := by
            nlinarith only [hslide_le, hβ0a]
      _ ≤ cstar * (δ : ℝ) := by nlinarith only [hsliderr, hηeq4, hη]
  have hq : dist U'.y (U.y + α • U.direction) ≤ 1 / (4 * (Module.finrank ℝ E : ℝ)) * (δ : ℝ) := by
    simpa [cstar, dist_eq_norm] using hqnorm
  have hαcstar : |α| ≤ cstar := hα4.trans hκcstar
  have hslide_not_ed : ¬ IsEssentiallyDistinct U.carrier U'.carrier :=
    not_essDistinct_of_axial_slide (σ := δ) hδ0 hδ1 U U' (α := α) hαcstar hp hq
  exact hslide_not_ed hED

/-- Free-ratio form of `Tube.parameterMap_mem_parameterRegion`: the free parameters of a
`δ`-tube inside `c · T` lie in the box of half-sides `(12 c² δ, c δ, c δ)`.

These are the half-sides `Tube.parameterRegion` collapses to at `C = 1`, ratio `c` and
`ρ = σ = δ`, so no free-ratio `parameterRegion` definition is needed: the box is written out.
The axial half-side is the product of the rescaling factor `(1/(4n)) δ / κ = 8 c δ` with the
axial bound `c/2 + c δ ≤ 3c/2` of `Tube.parameters_mem_of_subset_dilate_free`. -/
private lemma freeParameterMap_mem_prodBox [Nontrivial E] {δ : NNReal} {c : ℝ} (hc : 1 ≤ c)
    (hδ0 : 0 < δ) (hδ1 : (δ : ℝ) ≤ 1) (T : Tube δ E) (U : Tube δ E)
    (hU : U.carrier ⊆ (Kakeya.Tube.dilate T c).carrier) :
    freeParameterMap T (freeKappa (Module.finrank ℝ E) c) U ∈
      Metric.prodBox (F₁ := perpSpace T) (F₂ := perpSpace T)
        (12 * c ^ 2 * (δ : ℝ)) (c * (δ : ℝ)) (c * (δ : ℝ)) := by
  classical
  set n : ℕ := Module.finrank ℝ E
  let cstar : ℝ := 1 / (4 * (n : ℝ))
  let κ : ℝ := freeKappa n c
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hc0le : 0 ≤ c := le_of_lt hc0
  have hδ0R : 0 < (δ : ℝ) := by exact_mod_cast hδ0
  have hδ0le : 0 ≤ (δ : ℝ) := le_of_lt hδ0R
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (Module.finrank_pos (R := ℝ) (M := E)))
  have hκ : 0 < κ := by dsimp [κ, freeKappa]; positivity
  have hfac0 : 0 ≤ cstar * (δ : ℝ) / κ := by
    exact div_nonneg (mul_nonneg (by dsimp [cstar]; positivity) hδ0le) (le_of_lt hκ)
  have hfac : cstar * (δ : ℝ) / κ = 8 * c * (δ : ℝ) := by
    dsimp [cstar, κ, freeKappa]
    field_simp [hn0, hc0.ne']
    ring
  have hfac' : 1 / (4 * (Module.finrank ℝ E : ℝ)) * (δ : ℝ)
      / freeKappa (Module.finrank ℝ E) c = 8 * c * (δ : ℝ) := by
    simpa [cstar, κ] using hfac
  have hfac_nonneg : 0 ≤ 8 * c * (δ : ℝ) := by positivity
  have hP := Tube.parameters_mem_of_subset_dilate_free (σ := δ) hc0 T U hU
  have hxax : |inner ℝ (U.x - T.center) T.direction| ≤ c / 2 + c * (δ : ℝ) := hP.1.1
  have hcδ_le_c : c * (δ : ℝ) ≤ c := by
    simpa [mul_one] using mul_le_mul_of_nonneg_left hδ1 hc0le
  have haxial : |cstar * (δ : ℝ) / κ * inner ℝ (U.x - T.center) T.direction|
      ≤ 12 * c ^ 2 * (δ : ℝ) := by
    calc
      |cstar * (δ : ℝ) / κ * inner ℝ (U.x - T.center) T.direction|
          = |cstar * (δ : ℝ) / κ| * |inner ℝ (U.x - T.center) T.direction| := by rw [abs_mul]
      _ = cstar * (δ : ℝ) / κ * |inner ℝ (U.x - T.center) T.direction| := by
            rw [abs_of_nonneg hfac0]
      _ = (8 * c * (δ : ℝ)) * |inner ℝ (U.x - T.center) T.direction| := by rw [hfac]
      _ ≤ (8 * c * (δ : ℝ)) * (c / 2 + c * (δ : ℝ)) := by
            exact mul_le_mul_of_nonneg_left hxax hfac_nonneg
      _ ≤ 12 * c ^ 2 * (δ : ℝ) := by
            have hle : c / 2 + c * (δ : ℝ) ≤ 3 / 2 * c := by nlinarith [hcδ_le_c]
            calc
              (8 * c * (δ : ℝ)) * (c / 2 + c * (δ : ℝ)) ≤ (8 * c * (δ : ℝ)) * (3 / 2 * c) := by
                exact mul_le_mul_of_nonneg_left hle hfac_nonneg
              _ = 12 * c ^ 2 * (δ : ℝ) := by ring
  have hproj_x : ‖((ℝ ∙ T.direction)ᗮ).orthogonalProjectionOnto (U.x - T.center)‖
      ≤ c * (δ : ℝ) := by
    have h := (Submodule.norm_orthogonalProjectionOnto_perp_span_singleton T.norm_direction
      (U.x - T.center)).2
    rw [h]
    exact hP.2.1.1
  have hproj_y : ‖((ℝ ∙ T.direction)ᗮ).orthogonalProjectionOnto (U.y - T.center)‖
      ≤ c * (δ : ℝ) := by
    have h := (Submodule.norm_orthogonalProjectionOnto_perp_span_singleton T.norm_direction
      (U.y - T.center)).2
    rw [h]
    exact hP.2.1.2
  dsimp [Metric.prodBox]
  constructor
  · have hfst0 : WithLp.fst (freeParameterMap T (freeKappa (Module.finrank ℝ E) c) U)
        = 1 / (4 * (Module.finrank ℝ E : ℝ)) * (δ : ℝ)
          / freeKappa (Module.finrank ℝ E) c
          * inner ℝ (U.x - T.center) T.direction := by
        rfl
    have hfst : WithLp.fst (freeParameterMap T (freeKappa (Module.finrank ℝ E) c) U)
        = cstar * (δ : ℝ) / κ * inner ℝ (U.x - T.center) T.direction := by
        calc
          WithLp.fst (freeParameterMap T (freeKappa (Module.finrank ℝ E) c) U)
              = 1 / (4 * (Module.finrank ℝ E : ℝ)) * (δ : ℝ)
                / freeKappa (Module.finrank ℝ E) c
                * inner ℝ (U.x - T.center) T.direction := hfst0
          _ = 8 * c * (δ : ℝ) * inner ℝ (U.x - T.center) T.direction := by rw [hfac']
          _ = cstar * (δ : ℝ) / κ * inner ℝ (U.x - T.center) T.direction := by rw [hfac]
    rw [hfst]
    exact haxial
  · constructor
    · have hf1 : (WithLp.snd (freeParameterMap T (freeKappa (Module.finrank ℝ E) c) U)).fst
        = ((ℝ ∙ T.direction)ᗮ).orthogonalProjectionOnto (U.x - T.center) := by
        simp [freeParameterMap]
      rw [hf1]
      exact hproj_x
    · have hf2 : (WithLp.snd (freeParameterMap T (freeKappa (Module.finrank ℝ E) c) U)).snd
        = ((ℝ ∙ T.direction)ᗮ).orthogonalProjectionOnto (U.y - T.center) := by
        simp [freeParameterMap]
      rw [hf2]
      exact hproj_y

/-- The volume of the free-ratio parameter box, in the form the packing count consumes.

This is `Tube.volume_parameterRegion` with the half-sides written out: `Metric.volume_prodBox`
and `Tube.volume_closedBall_perpSpace` give
`2 · 12 c² δ · (2^(n-1) C_cov(n-1) (c δ)^(n-1))² = 24 ω² c^(2n) δ^(2n-1)`, and
`Tube.parameterRegion.C n = 24 ω²` with `ω = 2^(n-1) C_cov(n-1)`. -/
private lemma volume_prodBox_free_le [Nontrivial E] {δ : NNReal} {c : ℝ} (hc : 1 ≤ c)
    (hδ0 : 0 < δ) (T : Tube δ E) :
    volume (Metric.prodBox (F₁ := perpSpace T) (F₂ := perpSpace T)
        (12 * c ^ 2 * (δ : ℝ)) (c * (δ : ℝ)) (c * (δ : ℝ)))
      ≤ ENNReal.ofReal ((parameterRegion.C (Module.finrank ℝ E) : ℝ)
          * c ^ (2 * Module.finrank ℝ E) * (δ : ℝ) ^ (2 * Module.finrank ℝ E - 1)) := by
  classical
  set n : ℕ := Module.finrank ℝ E
  let h0 : ℝ := 12 * c ^ 2 * (δ : ℝ)
  let h1 : ℝ := c * (δ : ℝ)
  let ω : ℝ := (2 : ℝ) ^ (n - 1) *
    (Metric.coveringNumber_mul_pow_le_volume_cthickening.C (n - 1) : ℝ)
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hδ0R : 0 < (δ : ℝ) := by exact_mod_cast hδ0
  have h1_nonneg : 0 ≤ h1 := by dsimp [h1]; positivity
  have h0_nonneg : 0 ≤ h0 := by dsimp [h0]; positivity
  have hω_nonneg : 0 ≤ ω := by
    dsimp [ω]
    positivity
  have hB_nonneg : 0 ≤ ω * h1 ^ (n - 1) := mul_nonneg hω_nonneg (pow_nonneg h1_nonneg _)
  have hA_nonneg : 0 ≤ 2 * h0 := mul_nonneg (by norm_num) h0_nonneg
  have hn1 : 1 ≤ n := by
    dsimp [n]
    exact Nat.succ_le_of_lt (Module.finrank_pos (R := ℝ) (M := E))
  have h_nat : (n - 1) + (n - 1) = 2 * n - 2 := by omega
  have hparamC : (parameterRegion.C n : ℝ) = 24 * ω ^ 2 := by
    dsimp [parameterRegion.C, ω]
  have h2c : c ^ 2 * c ^ (2 * n - 2) = c ^ (2 * n) := by
    have hsum : 2 + (2 * n - 2) = 2 * n := by omega
    rw [← pow_add]
    rw [hsum]
  have hδ1 : (δ : ℝ) * (δ : ℝ) ^ (2 * n - 2) = (δ : ℝ) ^ (2 * n - 1) := by
    have hsum : 1 + (2 * n - 2) = 2 * n - 1 := by omega
    calc
      (δ : ℝ) * (δ : ℝ) ^ (2 * n - 2) = (δ : ℝ) ^ 1 * (δ : ℝ) ^ (2 * n - 2) := by rw [pow_one]
      _ = (δ : ℝ) ^ (1 + (2 * n - 2)) := by rw [← pow_add]
      _ = (δ : ℝ) ^ (2 * n - 1) := by rw [hsum]
  have hmp : (c * (δ : ℝ)) ^ (2 * n - 2) = c ^ (2 * n - 2) * (δ : ℝ) ^ (2 * n - 2) := by
    rw [mul_pow]
  have hid : (2 * h0) * ω ^ 2 * (c * (δ : ℝ)) ^ (2 * n - 2)
      = (parameterRegion.C n : ℝ) * c ^ (2 * n) * (δ : ℝ) ^ (2 * n - 1) := by
    calc
      (2 * h0) * ω ^ 2 * (c * (δ : ℝ)) ^ (2 * n - 2)
          = (2 * h0) * ω ^ 2 * (c ^ (2 * n - 2) * (δ : ℝ) ^ (2 * n - 2)) := by rw [hmp]
      _ = 24 * ω ^ 2 * (c ^ 2 * c ^ (2 * n - 2)) * ((δ : ℝ) * (δ : ℝ) ^ (2 * n - 2)) := by
            dsimp [h0]
            ring
      _ = 24 * ω ^ 2 * c ^ (2 * n) * (δ : ℝ) ^ (2 * n - 1) := by
            rw [h2c, hδ1]
      _ = (parameterRegion.C n : ℝ) * c ^ (2 * n) * (δ : ℝ) ^ (2 * n - 1) := by rw [hparamC]
  have heq :
      volume (Metric.prodBox (F₁ := perpSpace T) (F₂ := perpSpace T)
        (12 * c ^ 2 * (δ : ℝ)) (c * (δ : ℝ)) (c * (δ : ℝ)))
        = ENNReal.ofReal ((parameterRegion.C (Module.finrank ℝ E) : ℝ)
          * c ^ (2 * Module.finrank ℝ E) * (δ : ℝ) ^ (2 * Module.finrank ℝ E - 1)) := by
    rw [Metric.volume_prodBox]
    rw [Tube.volume_closedBall_perpSpace T h1_nonneg]
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
                      = ω * ω * (h1 ^ (n - 1) * h1 ^ (n - 1)) := by ring
                  _ = ω * ω * h1 ^ ((n - 1) + (n - 1)) := by rw [← pow_add]
                  _ = ω ^ 2 * h1 ^ (2 * n - 2) := by rw [← pow_two ω, h_nat]]
              ring
      _ = ENNReal.ofReal ((2 * h0) * ω ^ 2 * (c * (δ : ℝ)) ^ (2 * n - 2)) := by
              dsimp [h1]
      _ = ENNReal.ofReal ((parameterRegion.C n : ℝ) * c ^ (2 * n)
              * (δ : ℝ) ^ (2 * n - 1)) := by
              rw [hid]
  exact le_of_eq heq

/-- The arithmetic of the thin-regime packing count: the raw bound produced by
`Tube.card_le_of_separated_parameterSpace` at radius `δ / (16 n)` collapses to the constant
`Tube.essDistinctTubesInSelfDilate.thinC n c`. -/
private lemma essDistinctTubesInSelfDilate.thin_bound_arith {n : ℕ} (hn : 1 ≤ n) {c : ℝ}
    (hc : 1 ≤ c) {δ : NNReal} (hδ0 : 0 < δ) :
    ((Metric.coveringNumber_mul_pow_le_volume_cthickening.C (2 * n - 1) : NNReal) : ENNReal)⁻¹
        * (((δ / (16 * (n : NNReal)) : NNReal) : ENNReal))⁻¹ ^ (2 * n - 1)
        * ((2 : ENNReal) ^ (2 * n - 1)
            * ENNReal.ofReal ((parameterRegion.C n : ℝ) * c ^ (2 * n) * (δ : ℝ) ^ (2 * n - 1)))
      ≤ (essDistinctTubesInSelfDilate.thinC n c : ENNReal) := by
  classical
  let A : NNReal := Metric.coveringNumber_mul_pow_le_volume_cthickening.C (2 * n - 1)
  let P : NNReal := parameterRegion.C n
  have hA0 : 0 < A := by
    dsimp [A]
    exact Metric.coveringNumber_mul_pow_le_volume_cthickening.C_pos (2 * n - 1)
  have hAne : A ≠ 0 := ne_of_gt hA0
  have hnN : (n : NNReal) ≠ 0 := by
    exact_mod_cast (ne_of_gt hn)
  have hδne : δ ≠ 0 := ne_of_gt hδ0
  have hden : (16 * (n : NNReal) : NNReal) ≠ 0 := by
    exact mul_ne_zero (by norm_num : (16 : NNReal) ≠ 0) hnN
  have hrd : δ / (16 * (n : NNReal)) ≠ 0 := by
    exact div_ne_zero hδne hden
  have hc0 : 0 ≤ c := le_trans zero_le_one hc
  have hδR0 : 0 ≤ (δ : ℝ) := by exact_mod_cast (le_of_lt hδ0)
  have hPnn : 0 ≤ (P : ℝ) := by
    exact_mod_cast (by positivity : (0 : NNReal) ≤ P)
  have hpc : 0 ≤ c ^ (2 * n) := pow_nonneg hc0 (2 * n)
  -- ENNReal-to-NNReal rewriting lemmas
  have hIA : (A : ENNReal)⁻¹ = ((A⁻¹ : NNReal) : ENNReal) := by
    rw [← ENNReal.coe_inv hAne]
  have hIr : (((δ / (16 * (n : NNReal)) : NNReal) : ENNReal))⁻¹
      = (((δ / (16 * (n : NNReal)) : NNReal)⁻¹ : NNReal) : ENNReal) := by
    rw [← ENNReal.coe_inv hrd]
  have h2eq : (2 : ENNReal) = ((2 : NNReal) : ENNReal) := by norm_num
  have h2p : (2 : ENNReal) ^ (2 * n - 1) = (((2 : NNReal) ^ (2 * n - 1) : NNReal) : ENNReal) := by
    rw [h2eq, ← ENNReal.coe_pow]
  -- the ofReal factor becomes the coerced NNReal product
  have htoNN :
      Real.toNNReal ((P : ℝ) * c ^ (2 * n) * (δ : ℝ) ^ (2 * n - 1))
        = P * c.toNNReal ^ (2 * n) * δ ^ (2 * n - 1) := by
    rw [mul_assoc, Real.toNNReal_mul hPnn, Real.toNNReal_coe]
    rw [Real.toNNReal_mul hpc]
    rw [Real.toNNReal_pow hc0, Real.toNNReal_pow hδR0, Real.toNNReal_coe]
    ac_rfl
  have hOf : ENNReal.ofReal ((P : ℝ) * c ^ (2 * n) * (δ : ℝ) ^ (2 * n - 1))
      = ((P * c.toNNReal ^ (2 * n) * δ ^ (2 * n - 1) : NNReal) : ENNReal) := by
    rw [ENNReal.ofReal]
    exact congrArg (fun r : NNReal => (r : ENNReal)) htoNN
  -- the pure NNReal identity behind the collapse
  have hred : ((δ / (16 * (n : NNReal)) : NNReal)⁻¹) ^ (2 * n - 1) * δ ^ (2 * n - 1)
      = (16 * (n : NNReal)) ^ (2 * n - 1) := by
    calc
      ((δ / (16 * (n : NNReal)) : NNReal)⁻¹) ^ (2 * n - 1) * δ ^ (2 * n - 1)
          = ((16 * (n : NNReal)) / δ : NNReal) ^ (2 * n - 1) * δ ^ (2 * n - 1) := by
              rw [inv_div]
      _ = ((16 * (n : NNReal)) ^ (2 * n - 1) / δ ^ (2 * n - 1)) * δ ^ (2 * n - 1) := by
              rw [div_pow]
      _ = (16 * (n : NNReal)) ^ (2 * n - 1) := by
              field_simp [pow_ne_zero (2 * n - 1) hδne]
  have hsec : ((δ / (16 * (n : NNReal)) : NNReal)⁻¹) ^ (2 * n - 1)
        * (2 : NNReal) ^ (2 * n - 1) * δ ^ (2 * n - 1)
      = (32 * (n : NNReal)) ^ (2 * n - 1) := by
    calc
      ((δ / (16 * (n : NNReal)) : NNReal)⁻¹) ^ (2 * n - 1)
          * (2 : NNReal) ^ (2 * n - 1) * δ ^ (2 * n - 1)
          = ((δ / (16 * (n : NNReal)) : NNReal)⁻¹) ^ (2 * n - 1) * δ ^ (2 * n - 1)
              * (2 : NNReal) ^ (2 * n - 1) := by
        ac_rfl
      _ = (16 * (n : NNReal)) ^ (2 * n - 1) * (2 : NNReal) ^ (2 * n - 1) := by
          rw [hred]
      _ = (32 * (n : NNReal)) ^ (2 * n - 1) := by
          rw [← mul_pow]
          congr 1
          ring
  have hmain :
      (A⁻¹ : NNReal) * ((δ / (16 * (n : NNReal)) : NNReal)⁻¹) ^ (2 * n - 1)
        * (2 : NNReal) ^ (2 * n - 1) * (P * c.toNNReal ^ (2 * n) * δ ^ (2 * n - 1))
        = P * c.toNNReal ^ (2 * n) * (32 * (n : NNReal)) ^ (2 * n - 1) * A⁻¹ := by
    calc
      (A⁻¹ : NNReal) * ((δ / (16 * (n : NNReal)) : NNReal)⁻¹) ^ (2 * n - 1)
          * (2 : NNReal) ^ (2 * n - 1) * (P * c.toNNReal ^ (2 * n) * δ ^ (2 * n - 1))
          = ((δ / (16 * (n : NNReal)) : NNReal)⁻¹) ^ (2 * n - 1)
              * (2 : NNReal) ^ (2 * n - 1) * δ ^ (2 * n - 1)
              * A⁻¹ * (P * c.toNNReal ^ (2 * n)) := by
              ac_rfl
      _ = (32 * (n : NNReal)) ^ (2 * n - 1) * A⁻¹ * (P * c.toNNReal ^ (2 * n)) := by
              rw [hsec]
      _ = P * c.toNNReal ^ (2 * n) * (32 * (n : NNReal)) ^ (2 * n - 1) * A⁻¹ := by
              ac_rfl
  have hnn :
      (A⁻¹ : NNReal) * ((δ / (16 * (n : NNReal)) : NNReal)⁻¹) ^ (2 * n - 1)
          * ((2 : NNReal) ^ (2 * n - 1) * (P * c.toNNReal ^ (2 * n) * δ ^ (2 * n - 1)))
        = essDistinctTubesInSelfDilate.thinC n c := by
    calc
      (A⁻¹ : NNReal) * ((δ / (16 * (n : NNReal)) : NNReal)⁻¹) ^ (2 * n - 1)
          * ((2 : NNReal) ^ (2 * n - 1) * (P * c.toNNReal ^ (2 * n) * δ ^ (2 * n - 1)))
          = (A⁻¹ : NNReal) * ((δ / (16 * (n : NNReal)) : NNReal)⁻¹) ^ (2 * n - 1)
              * (2 : NNReal) ^ (2 * n - 1) * (P * c.toNNReal ^ (2 * n) * δ ^ (2 * n - 1)) :=
              by ac_rfl
      _ = P * c.toNNReal ^ (2 * n) * (32 * (n : NNReal)) ^ (2 * n - 1) * A⁻¹ := hmain
      _ = essDistinctTubesInSelfDilate.thinC n c := by
            change P * c.toNNReal ^ (2 * n) * (32 * (n : NNReal)) ^ (2 * n - 1) * A⁻¹
              = (24 * (2 ^ (n - 1) * Metric.coveringNumber_mul_pow_le_volume_cthickening.C (n - 1)) ^ 2
                  * ((Metric.coveringNumber_mul_pow_le_volume_cthickening.C (2 * n - 1))⁻¹)
                  * (32 * (n : NNReal)) ^ (2 * n - 1) * c.toNNReal ^ (2 * n))
            dsimp [P, A, parameterRegion.C]
            ac_rfl
  -- assemble in ENNReal
  rw [hIA, hIr, h2p, hOf]
  rw [← ENNReal.coe_pow]
  rw [← ENNReal.coe_mul, ← ENNReal.coe_mul, ← ENNReal.coe_mul]
  exact ENNReal.coe_le_coe.2 (le_of_eq hnn)

/-- The thickened free-ratio parameter box, in the form the packing count consumes: thickening
at the separation radius `δ / (16 n)` costs a factor `2 ^ (2n-1)`. -/
private lemma essDistinctTubesInSelfDilate.thin_cthickening_le [Nontrivial E] {δ : NNReal}
    {c : ℝ} (hc : 1 ≤ c) (hδ0 : 0 < δ) (T : Tube δ E) :
    volume (cthickening (((δ / (16 * (Module.finrank ℝ E : NNReal)) : NNReal) : ℝ))
        (Metric.prodBox (F₁ := perpSpace T) (F₂ := perpSpace T)
          (12 * c ^ 2 * (δ : ℝ)) (c * (δ : ℝ)) (c * (δ : ℝ))))
      ≤ 2 ^ (2 * Module.finrank ℝ E - 1)
        * ENNReal.ofReal ((parameterRegion.C (Module.finrank ℝ E) : ℝ)
            * c ^ (2 * Module.finrank ℝ E) * (δ : ℝ) ^ (2 * Module.finrank ℝ E - 1)) := by
  classical
  set n : ℕ := Module.finrank ℝ E with hndef
  have hn1 : 1 ≤ n := by
    dsimp [n]
    exact Nat.succ_le_of_lt (Module.finrank_pos (R := ℝ) (M := E))
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn1
  have hn1R : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hδR : 0 < (δ : ℝ) := by exact_mod_cast hδ0
  have hden_pos : 0 < 16 * (n : ℝ) := by
    exact mul_pos (by norm_num) hnR
  let B : Set (WithLp 2 (ℝ × WithLp 2 (perpSpace T × perpSpace T))) :=
    Metric.prodBox (F₁ := perpSpace T) (F₂ := perpSpace T)
      (12 * c ^ 2 * (δ : ℝ)) (c * (δ : ℝ)) (c * (δ : ℝ))
  let r : ℝ := ((δ / (16 * (n : NNReal)) : NNReal) : ℝ)
  have hr_eq : r = (δ : ℝ) / (16 * (n : ℝ)) := by
    change ((δ / (16 * (n : NNReal)) : NNReal) : ℝ) = (δ : ℝ) / (16 * (n : ℝ))
    rw [NNReal.coe_div]
    push_cast
    ring
  have hr_pos : 0 < r := by
    rw [hr_eq]
    exact div_pos hδR hden_pos
  have h16n : (1 : ℝ) ≤ 16 * (n : ℝ) := by nlinarith [hn1R]
  have hδ_le_cδ : (δ : ℝ) ≤ c * (δ : ℝ) := by
    simpa using mul_le_mul_of_nonneg_right hc (le_of_lt hδR)
  have hcδ_le : c * (δ : ℝ) ≤ c * (δ : ℝ) * (16 * (n : ℝ)) := by
    simpa using mul_le_mul_of_nonneg_left h16n (mul_nonneg (le_of_lt hc0) (le_of_lt hδR))
  have hs1 : r ≤ c * (δ : ℝ) := by
    rw [hr_eq]
    rw [div_le_iff₀ hden_pos]
    exact le_trans hδ_le_cδ hcδ_le
  have hc_le_12c2 : c ≤ 12 * c ^ 2 := by
    calc
      c ≤ c ^ 2 := by
        have hmain : c * (1 : ℝ) ≤ c * c :=
          mul_le_mul_of_nonneg_left hc (le_trans zero_le_one hc)
        simpa [pow_two] using hmain
      _ ≤ 12 * c ^ 2 := by
        have hbig : c ^ 2 * (1 : ℝ) ≤ c ^ 2 * (12 : ℝ) :=
          mul_le_mul_of_nonneg_left (by norm_num : (1 : ℝ) ≤ 12) (sq_nonneg c)
        calc
          c ^ 2 ≤ c ^ 2 * (12 : ℝ) := by simpa using hbig
          _ = 12 * c ^ 2 := by ring
  have hs0 : r ≤ 12 * c ^ 2 * (δ : ℝ) := by
    exact le_trans hs1 (mul_le_mul_of_nonneg_right hc_le_12c2 (le_of_lt hδR))
  have hbox := (Metric.volume_cthickening_box_le (F₁ := perpSpace T) (F₂ := perpSpace T)
      (h₀ := 12 * c ^ 2 * (δ : ℝ)) (h₁ := c * (δ : ℝ)) (h₂ := c * (δ : ℝ)) (s := r)
      hr_pos hs0 hs1 hs1).2
  have hfinp : Module.finrank ℝ (perpSpace T) = n - 1 := by
    simpa [← hndef] using Tube.finrank_perpSpace T
  have hfin1 : 1 + (n - 1) + (n - 1) = 2 * n - 1 := by omega
  have hcthick_bound : volume (cthickening r B) ≤ 2 ^ (2 * n - 1) * volume B := by
    simpa [hfin1, hfinp, n, B] using hbox
  have hvolB : volume B ≤ ENNReal.ofReal ((parameterRegion.C n : ℝ) * c ^ (2 * n)
      * (δ : ℝ) ^ (2 * n - 1)) := by
    simpa [hndef, n, B] using volume_prodBox_free_le hc hδ0 T
  calc
    volume (cthickening r B) ≤ 2 ^ (2 * n - 1) * volume B := hcthick_bound
    _ ≤ 2 ^ (2 * n - 1) * ENNReal.ofReal ((parameterRegion.C n : ℝ) * c ^ (2 * n)
        * (δ : ℝ) ^ (2 * n - 1)) := by
          exact mul_le_mul_of_nonneg_left hvolB (by positivity)

/-- Pairwise separation of the free-ratio parameters at the resolution `δ / (16 n)`, for an
oriented family of essentially distinct `δ`-tubes inside `c · T`. -/
private lemma essDistinctTubesInSelfDilate.thin_pairwise_separated {ι : Type*} [Nontrivial E]
    {δ : NNReal} {c : ℝ} (hc : 1 ≤ c) (hδ0 : 0 < δ) (hδ : (δ : ℝ) ≤ 1 / (4 * c))
    (T : Tube δ E) (a : Finset ι) (U : ι → Tube δ E)
    (hUo : ∀ j, 0 ≤ inner ℝ (U j).direction T.direction)
    (hUED : (↑a : Set ι).Pairwise fun i j => IsEssentiallyDistinct (U i).carrier (U j).carrier)
    (hUT : ∀ j ∈ a, (U j).carrier ⊆ (Kakeya.Tube.dilate T c).carrier) :
    (↑a : Set ι).Pairwise fun i j =>
      ((δ / (16 * (Module.finrank ℝ E : NNReal)) : NNReal) : ℝ)
        < dist (freeParameterMap T (freeKappa (Module.finrank ℝ E) c) (U i))
            (freeParameterMap T (freeKappa (Module.finrank ℝ E) c) (U j)) := by
  classical
  intro i hi j hj hij
  have hnR : (0 : ℝ) < (Module.finrank ℝ E : ℝ) := by
    exact_mod_cast (Module.finrank_pos (R := ℝ) (M := E))
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
  have hr_eq : ((δ / (16 * (Module.finrank ℝ E : NNReal)) : NNReal) : ℝ)
      = 1 / 4 * (1 / (4 * (Module.finrank ℝ E : ℝ))) * (δ : ℝ) := by
    rw [NNReal.coe_div]
    push_cast
    field_simp
    ring
  have hsep := free_separation_essDistinct hc hδ0 hδ T (U i) (U j) (hUT i hi) (hUT j hj)
      (hUo i) (hUo j) (hUED (x := i) hi (y := j) hj hij)
  have hr : ((δ / (16 * (Module.finrank ℝ E : NNReal)) : NNReal) : ℝ)
        < max (max ‖(U i).x - (U j).x - inner ℝ T.direction ((U i).x - (U j).x) • T.direction‖
                ‖(U i).y - (U j).y - inner ℝ T.direction ((U i).y - (U j).y) • T.direction‖)
            ((1 / (4 * (Module.finrank ℝ E : ℝ))) * (δ : ℝ)
              / freeKappa (Module.finrank ℝ E) c
              * |inner ℝ ((U i).x - (U j).x) T.direction|) := by
    rw [hr_eq]
    simpa only [freeKappa] using hsep
  have hrκ : 0 ≤ 1 / (4 * (Module.finrank ℝ E : ℝ)) * (δ : ℝ)
      / freeKappa (Module.finrank ℝ E) c := by
    simp only [freeKappa]
    positivity
  exact lt_dist_freeParameterMap_of_max_lt (δ := δ) T (freeKappa (Module.finrank ℝ E) c)
    (U i) (U j) (r := ((δ / (16 * (Module.finrank ℝ E : NNReal)) : NNReal) : ℝ)) hrκ hr

/-- The thin regime `δ ≤ 1/(4c)` of `Tube.essDistinctTubesInSelfDilate`: the
parameter-space packing count of `Tube.essDistinctTubesInThinDilate` run at the free ratio `c`,
giving the `K_thin(n) c ^ (2n)` summand. -/
private lemma essDistinctTubesInSelfDilate.thin_bound {ι : Type*} [Nontrivial E]
    {δ : NNReal} {c : ℝ} (hc : 1 ≤ c) (hδ0 : 0 < δ) (T : Tube δ E)
    (a : Finset ι) (U : ι → Tube δ E)
    (hUED : (↑a : Set ι).Pairwise fun i j => IsEssentiallyDistinct (U i).carrier (U j).carrier)
    (hUT : ∀ j ∈ a, (U j).carrier ⊆ (Kakeya.Tube.dilate T c).carrier)
    (hδ : (δ : ℝ) ≤ 1 / (4 * c)) :
    (a.card : ENNReal)
      ≤ (essDistinctTubesInSelfDilate.thinC (Module.finrank ℝ E) c : ENNReal) := by
  classical
  have hn1 : 1 ≤ Module.finrank ℝ E :=
    Nat.succ_le_of_lt (Module.finrank_pos (R := ℝ) (M := E))
  have hδ1 : (δ : ℝ) ≤ 1 := by
    have : (1 / (4 * c) : ℝ) ≤ 1 := by
      rw [div_le_one (by positivity : (0 : ℝ) < 4 * c)]
      nlinarith
    exact hδ.trans this
  obtain ⟨U', hU'⟩ := exists_orientedFamily U T.direction
  have hcar : ∀ j, (U' j).carrier = (U j).carrier := fun j => (hU' j).1
  have hUED' : (↑a : Set ι).Pairwise fun i j =>
      IsEssentiallyDistinct (U' i).carrier (U' j).carrier := by
    intro i hi j hj hij
    rw [hcar i, hcar j]
    exact hUED (x := i) hi (y := j) hj hij
  have hUT' : ∀ j ∈ a, (U' j).carrier ⊆ (Kakeya.Tube.dilate T c).carrier := by
    intro j hj; rw [hcar j]; exact hUT j hj
  let r : NNReal := δ / (16 * (Module.finrank ℝ E : NNReal))
  let A : Set (parameterSpace T) :=
    Metric.prodBox (F₁ := perpSpace T) (F₂ := perpSpace T)
      (12 * c ^ 2 * (δ : ℝ)) (c * (δ : ℝ)) (c * (δ : ℝ))
  have hr0 : 0 < r := by
    dsimp [r]
    rw [← NNReal.coe_lt_coe]
    rw [NNReal.coe_div]
    push_cast
    have hden : (0 : ℝ) < 16 * (Module.finrank ℝ E : ℝ) :=
      mul_pos (by norm_num)
        (by exact_mod_cast (Module.finrank_pos (R := ℝ) (M := E)))
    exact div_pos (by exact_mod_cast hδ0) hden
  have hsep := essDistinctTubesInSelfDilate.thin_pairwise_separated hc hδ0 hδ T a U'
    (fun j => (hU' j).2) hUED' hUT'
  have hmem : ∀ i ∈ a,
      freeParameterMap T (freeKappa (Module.finrank ℝ E) c) (U' i) ∈ A :=
    fun i hi => freeParameterMap_mem_prodBox hc hδ0 hδ1 T (U' i) (hUT' i hi)
  have hcard := card_le_of_separated_parameterSpace (F := parameterSpace T) (G := a)
    (Ψ := fun i => freeParameterMap T (freeKappa (Module.finrank ℝ E) c) (U' i))
    (A := A) (r := r) hr0 hmem hsep
  rw [Tube.finrank_parameterSpace T] at hcard
  have htv : volume (cthickening ((r : NNReal) : ℝ) A)
        ≤ 2 ^ (2 * Module.finrank ℝ E - 1) * ENNReal.ofReal
            ((parameterRegion.C (Module.finrank ℝ E) : ℝ)
              * c ^ (2 * Module.finrank ℝ E) * (δ : ℝ) ^ (2 * Module.finrank ℝ E - 1)) :=
    essDistinctTubesInSelfDilate.thin_cthickening_le hc hδ0 T
  calc
    (a.card : ENNReal)
        ≤ (Metric.coveringNumber_mul_pow_le_volume_cthickening.C (2 * Module.finrank ℝ E - 1) : ENNReal)⁻¹
            * (r : ENNReal)⁻¹ ^ (2 * Module.finrank ℝ E - 1)
            * volume (cthickening ((r : NNReal) : ℝ) A) := hcard
    _ ≤ (Metric.coveringNumber_mul_pow_le_volume_cthickening.C (2 * Module.finrank ℝ E - 1) : ENNReal)⁻¹
            * (r : ENNReal)⁻¹ ^ (2 * Module.finrank ℝ E - 1)
            * (2 ^ (2 * Module.finrank ℝ E - 1) * ENNReal.ofReal
                ((parameterRegion.C (Module.finrank ℝ E) : ℝ)
                  * c ^ (2 * Module.finrank ℝ E) * (δ : ℝ) ^ (2 * Module.finrank ℝ E - 1))) := by
          gcongr
    _ ≤ (essDistinctTubesInSelfDilate.thinC (Module.finrank ℝ E) c : ENNReal) :=
          essDistinctTubesInSelfDilate.thin_bound_arith hn1 hc hδ0

/-- **Counting essentially distinct tubes in a dilate of a tube of the same scale** (blueprint
`lem:essDistinctTubesInSelfDilate`).

A family of pairwise essentially distinct `δ`-tubes all contained in the dilate `c · T` of a
single `δ`-tube `T` has at most `Tube.essDistinctTubesInSelfDilate.C n c` members.  Both scales
are `δ` here — hence *self* dilate — where `Tube.essDistinctTubesInDilate` has the two scales
`ρ` and `C⁻¹ ρ`; and the ratio `c` is free, where that lemma has the fixed ratio
`C_n = Kakeya.Tube.tubeOverlapCoreClose.C n`.  The free ratio is what the route needs, because
`Tube.preimage_rescale_dilate_subset_dilate` produces the ratio `4 (κ + 2) R C_n`.

The proof splits at `δ = 1/(4c)`, as in blueprint `note:essDistinctTubesInDilateRegimes`, and
the two regimes contribute the two summands of
`Tube.essDistinctTubesInSelfDilate.C`.  The fat regime `δ > 1/(4c)` is four lines:
`Kakeya.Tube.dilate_carrier_eq_cthickening` puts `c · T` inside `B̄(T.center, 3c/2)`, and
`Tube.card_le_of_EssDistinct` at radius `3c/2` counts there with `r / δ < 6 c²`, giving
`K_fat(n) c ^ (4n)`.  The thin regime `δ ≤ 1/(4c)` is the parameter-space packing count of
`Tube.essDistinctTubesInThinDilate`, which is stated *and* argued at the ratio `C_n`
throughout, so running it at a free ratio is a reproof rather than a citation. -/
theorem essDistinctTubesInSelfDilate {ι : Type*} [Nontrivial E] {δ : NNReal} {c : ℝ}
    (hc : 1 ≤ c) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (T : Tube δ E) (a : Finset ι)
    (U : ι → Tube δ E)
    (hUED : (↑a : Set ι).Pairwise fun i j => IsEssentiallyDistinct (U i).carrier (U j).carrier)
    (hUT : ∀ j ∈ a, (U j).carrier ⊆ (Kakeya.Tube.dilate T c).carrier) :
    (a.card : ENNReal)
      ≤ (essDistinctTubesInSelfDilate.C (Module.finrank ℝ E) c : ENNReal) := by
  classical
  by_cases hδ : (δ : ℝ) ≤ 1 / (4 * c)
  · have hthin := essDistinctTubesInSelfDilate.thin_bound hc hδ0 T a U hUED hUT hδ
    refine le_trans hthin ?_
    apply ENNReal.coe_le_coe.2
    unfold essDistinctTubesInSelfDilate.C
    exact le_add_of_nonneg_right
      (zero_le : (0 : NNReal) ≤ essDistinctTubesInSelfDilate.fatC (Module.finrank ℝ E) c)
  · have hρ : 1 / (4 * c) < (δ : ℝ) := lt_of_not_ge hδ
    have hfat := essDistinctTubesInSelfDilate.fat_bound (ι := ι) (E := E) hc hδ0 hδ1 T a U hUED hUT hρ
    refine le_trans hfat ?_
    apply ENNReal.coe_le_coe.2
    unfold essDistinctTubesInSelfDilate.C
    exact le_add_of_nonneg_left
      (zero_le : (0 : NNReal) ≤ essDistinctTubesInSelfDilate.thinC (Module.finrank ℝ E) c)

/-! ### The three pullbacks, in Lean

The three statements of blueprint `section8_finenormalize_select.tex` announced above are
supplied here, in the *forward* form explained in the section docstring (blueprint
`note:rescalePullbacksStatedForwards`).  Only the metric layer of `Tube.rescaleMap` is needed
for the first two, and they are stated at a general base point `z` rather than at the centre
`T.center` of the blueprint, which costs nothing and saves the consumer a rewriting step. -/

/-- **The rescaling pulls the image direction back to the inner direction** (blueprint
`lem:rescalePullbackAxis`), stated forwards.

Write `Ψ = Tube.rescaleMap T₀ R`, `f = T.direction`, `â = Ψ(T.x)`, `b̂ = Ψ(T.y)` and
`f̂ = (b̂ - â)/‖b̂ - â‖` for the unit direction of the image core.  Every displacement
`α • f̂` *along the image core* is hit by a displacement `α' • f` along the inner core — with
no transverse error at all — and `|α'| ≤ 4 R |α|`.

This is the blueprint's `Ψ⁻¹(m̂ + α f̂) = m + α' f` read forwards for the injective `Ψ`; the
scalar `α ‖b̂ - â‖⁻¹` is folded into one coefficient of `b̂ - â`, so the unit vector `f̂` is
not named.  The base point is a general `z`, the blueprint reading it at `z = T.center`.

The linear part of `Ψ` is `(4 R)⁻¹ A` with `A = Tube.normalizationLinear T₀`, so
`b̂ - â = (4 R)⁻¹ • A f` and `α' = 4 R α / ‖A f‖`; the bound is `‖A f‖ ≥ ‖f‖ = 1`, which is
`Tube.dist_le_dist_normalization` and is where `0 < θ ≤ 1` is spent. -/
theorem rescale_symm_apply_add_smul (hθ : 0 < θ) (hθ1 : θ ≤ 1) {R : ℝ} (hR : 0 < R)
    (T₀ : Tube θ E) (T : Tube τ E) (α : ℝ) (z : E) :
    ∃ α' : ℝ, |α'| ≤ 4 * R * |α| ∧
      T₀.rescaleMap R (z + α' • T.direction)
        = T₀.rescaleMap R z
          + (α * ‖T₀.rescaleMap R T.y - T₀.rescaleMap R T.x‖⁻¹)
              • (T₀.rescaleMap R T.y - T₀.rescaleMap R T.x) := by
  let D : E := T₀.rescaleMap R T.y - T₀.rescaleMap R T.x
  let α' : ℝ := α * ‖D‖⁻¹
  have hΨ (w u : E) :
      T₀.rescaleMap R (w + u) - T₀.rescaleMap R w
        = (4 * R)⁻¹ • (T₀.normalizationLinear u) := by
    rw [rescaleMap_apply, rescaleMap_apply]
    calc
      (4 * R)⁻¹ • (T₀.normalization (w + u) - T₀.x)
          - (4 * R)⁻¹ • (T₀.normalization w - T₀.x)
          = (4 * R)⁻¹ • ((T₀.normalization (w + u) - T₀.x)
              - (T₀.normalization w - T₀.x)) := by
            rw [← smul_sub]
      _ = (4 * R)⁻¹ • (T₀.normalization (w + u) - T₀.normalization w) := by
            congr 1
            abel
      _ = (4 * R)⁻¹ • (T₀.normalizationLinear u) := by
            congr 1
            have hlin : (T₀.normalization : E →ᵃ[ℝ] E).linear
                = T₀.normalizationLinear.toLinearMap := rfl
            calc
              T₀.normalization (w + u) - T₀.normalization w
                  = T₀.normalization.linear ((w + u) - w) := by
                      simpa [vsub_eq_sub]
                        using (AffineMap.linearMap_vsub T₀.normalization (w + u) w).symm
              _ = T₀.normalizationLinear ((w + u) - w) := by
                      rw [hlin]
                      rfl
              _ = T₀.normalizationLinear u := by
                      congr 1
                      abel
  have hD : D = (4 * R)⁻¹ • (T₀.normalizationLinear T.direction) := by
    have hsub : T.y = T.x + T.direction := by
      rw [Tube.direction]
      abel
    dsimp [D]
    rw [hsub]
    exact hΨ T.x T.direction
  have hAnorm : ‖T.direction‖ ≤ ‖T₀.normalizationLinear T.direction‖ := by
    have hsub : T₀.normalization T.y - T₀.normalization T.x
        = T₀.normalizationLinear T.direction := by
      have hlin : (T₀.normalization : E →ᵃ[ℝ] E).linear
          = T₀.normalizationLinear.toLinearMap := rfl
      calc
        T₀.normalization T.y - T₀.normalization T.x = T₀.normalization.linear (T.y - T.x) := by
              simpa [vsub_eq_sub] using (AffineMap.linearMap_vsub T₀.normalization T.y T.x).symm
        _ = T₀.normalizationLinear (T.y - T.x) := by
              rw [hlin]
              rfl
        _ = T₀.normalizationLinear T.direction := by
              rw [Tube.direction]
    calc
      ‖T.direction‖ = ‖T.y - T.x‖ := by rw [Tube.direction]
      _ = dist T.y T.x := by rw [dist_eq_norm]
      _ ≤ dist (T₀.normalization T.y) (T₀.normalization T.x) :=
            dist_le_dist_normalization hθ hθ1 T₀ T.y T.x
      _ = ‖T₀.normalization T.y - T₀.normalization T.x‖ := by rw [dist_eq_norm]
      _ = ‖T₀.normalizationLinear T.direction‖ := by rw [hsub]
  have hAge1 : 1 ≤ ‖T₀.normalizationLinear T.direction‖ := by
    simpa [T.norm_direction] using hAnorm
  have h4R : 0 < 4 * R := by positivity
  have h4Rinv : 0 < (4 * R)⁻¹ := inv_pos.mpr h4R
  have hDnorm : ‖D‖ = (4 * R)⁻¹ * ‖T₀.normalizationLinear T.direction‖ := by
    calc
      ‖D‖ = ‖(4 * R)⁻¹ • T₀.normalizationLinear T.direction‖ := by rw [hD]
      _ = |(4 * R)⁻¹| * ‖T₀.normalizationLinear T.direction‖ := by
            rw [norm_smul, Real.norm_eq_abs]
      _ = (4 * R)⁻¹ * ‖T₀.normalizationLinear T.direction‖ := by
            rw [abs_of_nonneg h4Rinv.le]
  have hDlow : (4 * R)⁻¹ ≤ ‖D‖ := by
    rw [hDnorm]
    calc
      (4 * R)⁻¹ = (4 * R)⁻¹ * 1 := by rw [mul_one]
      _ ≤ (4 * R)⁻¹ * ‖T₀.normalizationLinear T.direction‖ :=
        mul_le_mul_of_nonneg_left hAge1 h4Rinv.le
  have hDpos : 0 < ‖D‖ := lt_of_lt_of_le h4Rinv hDlow
  have hDne : ‖D‖ ≠ 0 := ne_of_gt hDpos
  have hlin : 1 ≤ 4 * R * ‖D‖ := by
    have hstep : 1 = 4 * R * (4 * R)⁻¹ := by rw [← mul_inv_cancel₀ h4R.ne']
    rw [hstep]
    exact mul_le_mul_of_nonneg_left hDlow h4R.le
  have hinv : ‖D‖⁻¹ ≤ 4 * R := by
    rw [show ‖D‖⁻¹ = 1 / ‖D‖ by rw [one_div]]
    rw [div_le_iff₀ hDpos]
    exact hlin
  have hbnd : |α'| ≤ 4 * R * |α| := by
    dsimp [α']
    calc
      |α * ‖D‖⁻¹| = |α| * ‖D‖⁻¹ := by
            rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg D))]
      _ ≤ |α| * (4 * R) := mul_le_mul_of_nonneg_left hinv (abs_nonneg α)
      _ = 4 * R * |α| := by ring
  have hmul : (4 * R)⁻¹ • (T₀.normalizationLinear (α' • T.direction))
      = (α * ‖D‖⁻¹) • D := by
    calc
      (4 * R)⁻¹ • (T₀.normalizationLinear (α' • T.direction))
          = (4 * R)⁻¹ • (α' • T₀.normalizationLinear T.direction) := by
              rw [map_smul]
      _ = α' • ((4 * R)⁻¹ • T₀.normalizationLinear T.direction) := by
              module
      _ = α' • D := by rw [← hD]
      _ = (α * ‖D‖⁻¹) • D := rfl
  have hmain : T₀.rescaleMap R (z + α' • T.direction)
      = T₀.rescaleMap R z + (α * ‖D‖⁻¹) • D := by
    have hdisp := hΨ z (α' • T.direction)
    calc
      T₀.rescaleMap R (z + α' • T.direction)
          = T₀.rescaleMap R z
            + (T₀.rescaleMap R (z + α' • T.direction) - T₀.rescaleMap R z) := by
              abel
      _ = T₀.rescaleMap R z + (4 * R)⁻¹ • (T₀.normalizationLinear (α' • T.direction)) := by
              rw [hdisp]
      _ = T₀.rescaleMap R z + (α * ‖D‖⁻¹) • D := by rw [hmul]
  exact ⟨α', hbnd, by simpa [D] using hmain⟩

/-- **Pulling a transverse displacement back through the rescaling** (blueprint
`lem:rescalePullbackVector`), stated forwards.

Write `Ψ = Tube.rescaleMap T₀ R`, `e = T₀.direction` and `f = T.direction`, and suppose the
inner direction is nearly parallel to the ambient axis, `‖f - ⟪e, f⟫ • e‖ ≤ κ θ`.  Let `u` be
the pullback of a displacement `v` of norm at most `s`, that is `Ψ(z + u) = Ψ z + v` (a
condition that does not depend on `z`, `Ψ` being affine).  Then

```
|⟪f, u⟫| ≤ 4 R (1 + θ) s,        ‖u - ⟪f, u⟫ • f‖ ≤ 4 R (κ + 1) θ s.
```

The gain is the second bound: *perpendicularly to the inner direction* the pullback is smaller
by a factor `θ` than along it, which is what turns a `σ`-thickness upstairs into a
`τ`-thickness downstairs.

The linear part of `Ψ⁻¹` is `4 R A⁻¹` with `A = Tube.normalizationLinear T₀`, which is
multiplication by `4 R` on `ℝ ∙ e` and by `4 R θ` on `e^⊥`, so `u = 4 R (v^∥ + θ v^⊥)`; the
transverse bound then uses `‖e - ⟪f, e⟫ • f‖ = ‖f - ⟪e, f⟫ • e‖`, both sides being
`sin ∠(e, f)` by `InnerProductGeometry.norm_sub_inner_smul_eq_sin_angle` and
`InnerProductGeometry.angle_comm`.

`0 < θ` is what makes `Ψ` invertible; `θ ≤ 1` enters only through the coefficient `1 - θ` of
the parallel part of `A⁻¹`, and holds throughout, `θ` being a tube scale.  The blueprint
records no upper bound on `θ`, but at `θ > 2` the parallel bound as stated is false, the
coefficient being `|1 - θ| = θ - 1` there. -/
theorem norm_rescale_symm_vector_le (hθ : 0 < θ) (hθ1 : θ ≤ 1) {R : ℝ} (hR : 0 < R)
    (T₀ : Tube θ E) (T : Tube τ E) {κ s : ℝ} (hκ : 0 ≤ κ) (hs : 0 ≤ s)
    (hperp : ‖T.direction - (inner ℝ T₀.direction T.direction : ℝ) • T₀.direction‖
      ≤ κ * (θ : ℝ))
    {z u v : E} (huv : T₀.rescaleMap R (z + u) = T₀.rescaleMap R z + v) (hv : ‖v‖ ≤ s) :
    |(inner ℝ T.direction u : ℝ)| ≤ 4 * R * (1 + (θ : ℝ)) * s ∧
      ‖u - (inner ℝ T.direction u : ℝ) • T.direction‖ ≤ 4 * R * (κ + 1) * (θ : ℝ) * s := by
  have h4R : 0 < 4 * R := by positivity
  have h4Rne : (4 * R) ≠ 0 := ne_of_gt h4R
  have hθ0 : 0 ≤ (θ : ℝ) := by exact_mod_cast hθ.le
  have h1mθ : 0 ≤ 1 - (θ : ℝ) := sub_nonneg.mpr (by exact_mod_cast hθ1)
  let a : ℝ := inner ℝ T₀.direction v
  -- STEP 1: the displacement formula of `Tube.rescaleMap`
  have hΨ (w u : E) :
      T₀.rescaleMap R (w + u) - T₀.rescaleMap R w
        = (4 * R)⁻¹ • (T₀.normalizationLinear u) := by
    rw [rescaleMap_apply, rescaleMap_apply]
    calc
      (4 * R)⁻¹ • (T₀.normalization (w + u) - T₀.x)
          - (4 * R)⁻¹ • (T₀.normalization w - T₀.x)
          = (4 * R)⁻¹ • ((T₀.normalization (w + u) - T₀.x)
              - (T₀.normalization w - T₀.x)) := by
            rw [← smul_sub]
      _ = (4 * R)⁻¹ • (T₀.normalization (w + u) - T₀.normalization w) := by
            congr 1
            abel
      _ = (4 * R)⁻¹ • (T₀.normalizationLinear u) := by
            congr 1
            have hlin : (T₀.normalization : E →ᵃ[ℝ] E).linear
                = T₀.normalizationLinear.toLinearMap := rfl
            calc
              T₀.normalization (w + u) - T₀.normalization w
                  = T₀.normalization.linear ((w + u) - w) := by
                      simpa [vsub_eq_sub]
                        using (AffineMap.linearMap_vsub T₀.normalization (w + u) w).symm
              _ = T₀.normalizationLinear ((w + u) - w) := by
                      rw [hlin]
                      rfl
              _ = T₀.normalizationLinear u := by
                      congr 1
                      abel
  have hA' : v = (4 * R)⁻¹ • (T₀.normalizationLinear u) := by
    rw [← hΨ z u]
    rw [huv]
    abel
  have hA : T₀.normalizationLinear u = (4 * R) • v := by
    calc
      T₀.normalizationLinear u = (4 * R) • ((4 * R)⁻¹ • (T₀.normalizationLinear u)) := by
        rw [smul_smul, mul_inv_cancel₀ h4Rne]
        simp
      _ = (4 * R) • v := by
        rw [hA']
  -- STEP 2: invert the linear part, obtaining the explicit formula for `u`
  have hu : u = (4 * R) • ((θ : ℝ) • v + (1 - (θ : ℝ)) • (a • T₀.direction)) := by
    let L : E →ₗ[ℝ] E := (T₀.dilateAux (θ : ℝ)).toLinearMap
    have hcomp : L.comp T₀.normalizationLinear.toLinearMap = LinearMap.id := by
      simpa [L] using dilateAux_comp_normalizationLinear hθ T₀
    have hLu : L (T₀.normalizationLinear u) = u := by
      simpa using (LinearMap.congr_fun hcomp u)
    have hmain : L (T₀.normalizationLinear u) = L ((4 * R) • v) := by
      rw [hA]
    have hLv : L v = (θ : ℝ) • v + (1 - (θ : ℝ)) • (a • T₀.direction) := by
      simpa [a, L] using (T₀.dilateAux_apply (θ : ℝ) v)
    calc
      u = L (T₀.normalizationLinear u) := by rw [hLu]
      _ = L ((4 * R) • v) := hmain
      _ = (4 * R) • L v := by rw [map_smul]
      _ = (4 * R) • ((θ : ℝ) • v + (1 - (θ : ℝ)) • (a • T₀.direction)) := by rw [hLv]
  -- STEP 3: the bound along the inner direction
  have ha : |a| ≤ s := by
    calc
      |a| ≤ ‖T₀.direction‖ * ‖v‖ := by simpa [a] using abs_real_inner_le_norm T₀.direction v
      _ = ‖v‖ := by rw [T₀.norm_direction, one_mul]
      _ ≤ s := hv
  have haT0 : ‖a • T₀.direction‖ ≤ s := by
    calc
      ‖a • T₀.direction‖ = |a| * ‖T₀.direction‖ := by
        rw [norm_smul]
        rw [Real.norm_eq_abs]
      _ = |a| := by rw [T₀.norm_direction, mul_one]
      _ ≤ s := ha
  have hw1 : ‖(θ : ℝ) • v‖ ≤ (θ : ℝ) * s := by
    calc
      ‖(θ : ℝ) • v‖ = |(θ : ℝ)| * ‖v‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ = (θ : ℝ) * ‖v‖ := by rw [abs_of_nonneg hθ0]
      _ ≤ (θ : ℝ) * s := mul_le_mul_of_nonneg_left hv hθ0
  have hw2 : ‖(1 - (θ : ℝ)) • (a • T₀.direction)‖ ≤ (1 - (θ : ℝ)) * s := by
    calc
      ‖(1 - (θ : ℝ)) • (a • T₀.direction)‖ = |1 - (θ : ℝ)| * ‖a • T₀.direction‖ := by
        rw [norm_smul, Real.norm_eq_abs]
      _ = (1 - (θ : ℝ)) * ‖a • T₀.direction‖ := by rw [abs_of_nonneg h1mθ]
      _ ≤ (1 - (θ : ℝ)) * s := mul_le_mul_of_nonneg_left haT0 h1mθ
  have hw : ‖(θ : ℝ) • v + (1 - (θ : ℝ)) • (a • T₀.direction)‖ ≤ s := by
    have hsum : ‖(θ : ℝ) • v + (1 - (θ : ℝ)) • (a • T₀.direction)‖
        ≤ (θ : ℝ) * s + (1 - (θ : ℝ)) * s := by
      exact le_trans (norm_add_le _ _) (add_le_add hw1 hw2)
    rwa [show (θ : ℝ) * s + (1 - (θ : ℝ)) * s = s by ring] at hsum
  have hu_norm : ‖u‖ ≤ 4 * R * s := by
    calc
      ‖u‖ = (4 * R) * ‖(θ : ℝ) • v + (1 - (θ : ℝ)) • (a • T₀.direction)‖ := by
        rw [hu, norm_smul, Real.norm_eq_abs, abs_of_nonneg h4R.le]
      _ ≤ 4 * R * s := mul_le_mul_of_nonneg_left hw h4R.le
  have hb : |inner ℝ T.direction u| ≤ ‖u‖ := by
    calc
      |inner ℝ T.direction u| ≤ ‖T.direction‖ * ‖u‖ := abs_real_inner_le_norm T.direction u
      _ = ‖u‖ := by rw [T.norm_direction, one_mul]
  have hfirst : |(inner ℝ T.direction u : ℝ)| ≤ 4 * R * (1 + (θ : ℝ)) * s := by
    calc
      |inner ℝ T.direction u| ≤ ‖u‖ := hb
      _ ≤ 4 * R * s := hu_norm
      _ ≤ 4 * R * (1 + (θ : ℝ)) * s := by
        have hnn : (0 : ℝ) ≤ 4 * R * (θ : ℝ) * s := by positivity
        calc
          4 * R * s ≤ 4 * R * s + 4 * R * (θ : ℝ) * s := by linarith
          _ = 4 * R * (1 + (θ : ℝ)) * s := by ring
  -- STEP 4: the perpendicular bound
  let P : E → E := fun y => y - (inner ℝ T.direction y) • T.direction
  have hPadd : ∀ x y : E, P (x + y) = P x + P y := by
    intro x y
    dsimp [P]
    rw [inner_add_right, add_smul]
    abel
  have hPsmul : ∀ (c : ℝ) (y : E), P (c • y) = c • P y := by
    intro c y
    dsimp [P]
    rw [real_inner_smul_right]
    module
  have hPnle (y : E) : ‖P y‖ ≤ ‖y‖ := by
    dsimp [P]
    exact Tube.norm_perp_le T y
  have hvP : ‖P v‖ ≤ s := le_trans (hPnle v) hv
  -- the symmetry ‖T₀.direction - ⟪f, T₀.direction⟫ f‖ = ‖f - ⟪e, f⟫ e‖, both sides sin∠(f, e)
  have hT1 : ‖T₀.direction - (inner ℝ T.direction T₀.direction : ℝ) • T.direction‖
      = Real.sin (InnerProductGeometry.angle T.direction T₀.direction) := by
    simpa using (InnerProductGeometry.norm_sub_inner_smul_eq_sin_angle
      (e := T.direction) (f := T₀.direction) T.norm_direction T₀.norm_direction)
  have hT2 : Real.sin (InnerProductGeometry.angle T.direction T₀.direction)
      = Real.sin (InnerProductGeometry.angle T₀.direction T.direction) := by
    rw [InnerProductGeometry.angle_comm]
  have hT3 : Real.sin (InnerProductGeometry.angle T₀.direction T.direction)
      = ‖T.direction - (inner ℝ T₀.direction T.direction : ℝ) • T₀.direction‖ := by
    simpa using (InnerProductGeometry.norm_sub_inner_smul_eq_sin_angle
      (e := T₀.direction) (f := T.direction) T₀.norm_direction T.norm_direction).symm
  have hsym : ‖T₀.direction - (inner ℝ T.direction T₀.direction : ℝ) • T.direction‖
      = ‖T.direction - (inner ℝ T₀.direction T.direction : ℝ) • T₀.direction‖ :=
    hT1.trans (hT2.trans hT3)
  have hPτ : ‖P T₀.direction‖ ≤ κ * (θ : ℝ) := by
    calc
      ‖P T₀.direction‖ = ‖T₀.direction - (inner ℝ T.direction T₀.direction : ℝ) • T.direction‖ := by
        simp [P]
      _ = ‖T.direction - (inner ℝ T₀.direction T.direction : ℝ) • T₀.direction‖ := hsym
      _ ≤ κ * (θ : ℝ) := hperp
  have hPu : P u = (4 * R * θ) • P v + (4 * R * (1 - θ) * a) • P T₀.direction := by
    calc
      P u = P ((4 * R) • ((θ : ℝ) • v + (1 - (θ : ℝ)) • (a • T₀.direction))) := by rw [hu]
      _ = (4 * R) • P ((θ : ℝ) • v + (1 - (θ : ℝ)) • (a • T₀.direction)) := hPsmul (4 * R) _
      _ = (4 * R) • (P ((θ : ℝ) • v) + P ((1 - (θ : ℝ)) • (a • T₀.direction))) := by
            rw [hPadd]
      _ = (4 * R) • ((θ : ℝ) • P v + (1 - (θ : ℝ)) • P (a • T₀.direction)) := by
            rw [hPsmul, hPsmul]
      _ = (4 * R) • ((θ : ℝ) • P v + (1 - (θ : ℝ)) • (a • P T₀.direction)) := by
            rw [hPsmul]
      _ = (4 * R * θ) • P v + (4 * R * (1 - θ) * a) • P T₀.direction := by
            module
  have h4Rθ0 : 0 ≤ 4 * R * (θ : ℝ) := by positivity
  have h4R1mθ0 : 0 ≤ 4 * R * (1 - (θ : ℝ)) := by positivity
  have hb1 : ‖(4 * R * θ) • P v‖ ≤ 4 * R * (θ : ℝ) * s := by
    calc
      ‖(4 * R * θ) • P v‖ = |4 * R * θ| * ‖P v‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ = (4 * R * θ) * ‖P v‖ := by rw [abs_of_nonneg h4Rθ0]
      _ ≤ (4 * R * θ) * s := mul_le_mul_of_nonneg_left hvP h4Rθ0
  have hb2 : ‖(4 * R * (1 - θ) * a) • P T₀.direction‖
      ≤ 4 * R * (1 - (θ : ℝ)) * s * ‖P T₀.direction‖ := by
    calc
      ‖(4 * R * (1 - θ) * a) • P T₀.direction‖ = |4 * R * (1 - θ) * a| * ‖P T₀.direction‖ := by
        rw [norm_smul, Real.norm_eq_abs]
      _ = (4 * R * (1 - (θ : ℝ))) * |a| * ‖P T₀.direction‖ := by
        rw [abs_mul, abs_of_nonneg h4R1mθ0]
      _ ≤ 4 * R * (1 - (θ : ℝ)) * s * ‖P T₀.direction‖ := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ha h4R1mθ0) (norm_nonneg _)
  have hPu_le : ‖P u‖ ≤ 4 * R * (θ : ℝ) * s + 4 * R * (1 - (θ : ℝ)) * s * ‖P T₀.direction‖ := by
    calc
      ‖P u‖ = ‖(4 * R * θ) • P v + (4 * R * (1 - θ) * a) • P T₀.direction‖ := by rw [hPu]
      _ ≤ ‖(4 * R * θ) • P v‖ + ‖(4 * R * (1 - θ) * a) • P T₀.direction‖ := norm_add_le _ _
      _ ≤ 4 * R * (θ : ℝ) * s + 4 * R * (1 - (θ : ℝ)) * s * ‖P T₀.direction‖ := by linarith
  have hκθ0 : 0 ≤ 4 * R * s * (θ : ℝ) * κ := by positivity
  have hPu_final : ‖P u‖ ≤ 4 * R * (κ + 1) * (θ : ℝ) * s := by
    have hstep : 4 * R * (1 - (θ : ℝ)) * s * ‖P T₀.direction‖ ≤ 4 * R * (θ : ℝ) * s * κ := by
      calc
        4 * R * (1 - (θ : ℝ)) * s * ‖P T₀.direction‖
            ≤ 4 * R * (1 - (θ : ℝ)) * s * (κ * (θ : ℝ)) := by
              exact mul_le_mul_of_nonneg_left hPτ
                (by positivity : (0 : ℝ) ≤ 4 * R * (1 - (θ : ℝ)) * s)
        _ = (4 * R * s * (θ : ℝ) * κ) * (1 - (θ : ℝ)) := by ring
        _ ≤ (4 * R * s * (θ : ℝ) * κ) * 1 := by
              exact mul_le_mul_of_nonneg_left (by linarith : (1 - (θ : ℝ)) ≤ 1) hκθ0
        _ = 4 * R * (θ : ℝ) * s * κ := by ring
    calc
      ‖P u‖ ≤ 4 * R * (θ : ℝ) * s + 4 * R * (1 - (θ : ℝ)) * s * ‖P T₀.direction‖ := hPu_le
      _ ≤ 4 * R * (θ : ℝ) * s + 4 * R * (θ : ℝ) * s * κ := by nlinarith [hstep]
      _ = 4 * R * (κ + 1) * (θ : ℝ) * s := by ring
  refine ⟨hfirst, ?_⟩
  simpa [P] using hPu_final

/-- **From a cardinality bound to a refinement, at a free constant** (blueprint
`lem:comparableRefinementClauseFree`).

This is `Tube.isCRefinement_of_card_le` with the selection constant
`C_{lem:comparableBodiesToTubes}(n, C)` replaced by a variable `C₁ ≥ 1`.  The generalization is
a restatement and not an argument: the only use that proof makes of the fixed value is to know
it is nonzero.  It is needed because the affine selection route of
`Tube.exists_comparableReplacement_affine` produces the cardinality bound at the constant
`Tube.essDistinctTubesInSelfDilate.C n (4 (κ + 2) R C_n)` instead, and the existing statement
cannot be cited at that value.

The unused hypotheses of `Tube.isCRefinement_of_card_le` — `Nontrivial E`, `0 < ρ`,
`s.Nonempty` and `s'.Nonempty` — are dropped here. -/
theorem isCRefinement_of_card_le_free {ι : Type*} {ρ C₁ Λ : NNReal} {μ₀ W : ENNReal}
    (hC₁ : 1 ≤ C₁) (hΛ : 1 ≤ Λ) (hW : W ≠ 0) (hW' : W ≠ ⊤) (hμ₀ : μ₀ ≠ 0) (hμ₀' : μ₀ ≠ ⊤)
    {s s' : Finset ι} (hs'sub : s' ⊆ s) (𝕍 : ι → ShadedTube ρ E)
    (hlow : ∀ i ∈ s, (Λ : ENNReal)⁻¹ * μ₀ * W ≤ volume (𝕍 i).shade)
    (hupp : ∀ i ∈ s, volume (𝕍 i).shade ≤ (Λ : ENNReal) * μ₀ * W)
    (hcard : (s.card : ENNReal) ≤ (C₁ : ENNReal) * (s'.card : ENNReal)) :
    ShadedBody.IsCRefinement s' (fun i => (𝕍 i).toShadedBody) s (fun i => (𝕍 i).toShadedBody)
      (C₁ * Λ ^ 2)⁻¹ := by
  classical
  let Λe : ENNReal := (Λ : ENNReal)
  let Z : ι → ENNReal := fun i => volume (𝕍 i).shade
  let S : ENNReal := ∑ i ∈ s, Z i
  let T : ENNReal := ∑ i ∈ s', Z i
  have hΛne0 : (Λ : ENNReal) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one hΛ))
  have hΛne : (Λ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hΛ2_ne0 : (Λ ^ 2 : NNReal) ≠ 0 :=
    pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le zero_lt_one hΛ))
  have hC1_ne0 : (C₁ : NNReal) ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one hC₁)
  have hC1_ne0e : (C₁ : ENNReal) ≠ 0 := by exact_mod_cast hC1_ne0
  have hC1_ne_top : (C₁ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hC1_mul_Λ2_ne0 : (C₁ * Λ ^ 2 : NNReal) ≠ 0 := mul_ne_zero hC1_ne0 hΛ2_ne0
  have hcoepow : (Λe : ENNReal) ^ 2 = ((Λ ^ 2 : NNReal) : ENNReal) := by
    simp [Λe]
  have hΛinv2 : ((Λ ^ 2 : NNReal) : ENNReal)⁻¹ = Λe⁻¹ * Λe⁻¹ := by
    rw [← hcoepow, ENNReal.inv_pow, pow_two]
  have hκcard : ((C₁⁻¹ : NNReal) : ENNReal) * (s.card : ENNReal) ≤ (s'.card : ENNReal) := by
    calc
      ((C₁⁻¹ : NNReal) : ENNReal) * (s.card : ENNReal)
          ≤ ((C₁⁻¹ : NNReal) : ENNReal) * ((C₁ : ENNReal) * (s'.card : ENNReal)) := by
            exact mul_le_mul_right hcard _
      _ = (((C₁⁻¹ : NNReal) : ENNReal) * (C₁ : ENNReal)) * (s'.card : ENNReal) := by
            rw [← mul_assoc]
      _ = ((C₁ : ENNReal)⁻¹ * (C₁ : ENNReal)) * (s'.card : ENNReal) := by
            rw [ENNReal.coe_inv hC1_ne0]
      _ = (1 : ENNReal) * (s'.card : ENNReal) := by
            rw [ENNReal.inv_mul_cancel hC1_ne0e hC1_ne_top]
      _ = (s'.card : ENNReal) := by
            rw [one_mul]
  have hS : S ≤ (s.card : ENNReal) * (Λe * μ₀ * W) := by
    calc
      S = ∑ i ∈ s, Z i := rfl
      _ ≤ ∑ i ∈ s, (Λe * μ₀ * W) := by
        exact Finset.sum_le_sum (fun i hi => hupp i hi)
      _ = (s.card : ENNReal) * (Λe * μ₀ * W) := by
        rw [Finset.sum_const, nsmul_eq_mul]
  have hC : (s'.card : ENNReal) * (Λe⁻¹ * μ₀ * W) ≤ T := by
    calc
      (s'.card : ENNReal) * (Λe⁻¹ * μ₀ * W) = ∑ i ∈ s', (Λe⁻¹ * μ₀ * W) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ T := by
        dsimp [T, Z]
        exact Finset.sum_le_sum (fun i hi => hlow i (hs'sub hi))
  have hmid : ((C₁⁻¹ : NNReal) : ENNReal) * (Λe⁻¹ * Λe⁻¹) * (s.card : ENNReal) * (Λe * μ₀ * W)
      ≤ (s'.card : ENNReal) * (Λe⁻¹ * μ₀ * W) := by
    calc
      ((C₁⁻¹ : NNReal) : ENNReal) * (Λe⁻¹ * Λe⁻¹) * (s.card : ENNReal) * (Λe * μ₀ * W)
          = ((C₁⁻¹ : NNReal) : ENNReal) * (s.card : ENNReal) * (Λe⁻¹ * Λe⁻¹)
            * (Λe * μ₀ * W) := by ring
      _ = ((C₁⁻¹ : NNReal) : ENNReal) * (s.card : ENNReal) * ((Λe⁻¹ * Λe⁻¹) * Λe)
            * μ₀ * W := by ring
      _ = ((C₁⁻¹ : NNReal) : ENNReal) * (s.card : ENNReal)
            * (Λe⁻¹ * (Λe⁻¹ * Λe)) * μ₀ * W := by ring
      _ = ((C₁⁻¹ : NNReal) : ENNReal) * (s.card : ENNReal) * (Λe⁻¹ * 1) * μ₀ * W := by
        rw [show (Λe : ENNReal)⁻¹ * (Λe : ENNReal) = 1 by
          exact ENNReal.inv_mul_cancel hΛne0 hΛne]
      _ = ((C₁⁻¹ : NNReal) : ENNReal) * (s.card : ENNReal) * Λe⁻¹ * μ₀ * W := by ring
      _ = ((C₁⁻¹ : NNReal) : ENNReal) * (s.card : ENNReal) * (Λe⁻¹ * μ₀ * W) := by ring
      _ ≤ (s'.card : ENNReal) * (Λe⁻¹ * μ₀ * W) := by gcongr
  have hκmatch : ((C₁ * Λ ^ 2 : NNReal)⁻¹ : ENNReal)
      = ((C₁⁻¹ : NNReal) : ENNReal) * (Λe⁻¹ * Λe⁻¹) := by
    rw [ENNReal.coe_mul, ENNReal.mul_inv (Or.inl hC1_ne0e) (Or.inl hC1_ne_top),
      ← ENNReal.coe_inv hC1_ne0, hΛinv2]
  have hgoal : ((C₁ * Λ ^ 2 : NNReal)⁻¹ : ENNReal) * S ≤ T := by
    calc
      ((C₁ * Λ ^ 2 : NNReal)⁻¹ : ENNReal) * S
          = ((C₁⁻¹ : NNReal) : ENNReal) * (Λe⁻¹ * Λe⁻¹) * S := by
            rw [hκmatch]
      _ ≤ ((C₁⁻¹ : NNReal) : ENNReal) * (Λe⁻¹ * Λe⁻¹) * ((s.card : ENNReal) * (Λe * μ₀ * W)) := by
            gcongr
      _ = ((C₁⁻¹ : NNReal) : ENNReal) * (Λe⁻¹ * Λe⁻¹) * (s.card : ENNReal)
            * (Λe * μ₀ * W) := by ring
      _ ≤ (s'.card : ENNReal) * (Λe⁻¹ * μ₀ * W) := hmid
      _ ≤ T := hC
  constructor
  · exact ⟨hs'sub, fun i hi => ⟨rfl, Subset.rfl⟩⟩
  · dsimp
    simpa only [S, T, Z, ENNReal.coe_inv hC1_mul_Λ2_ne0] using hgoal

/-- **Pulling a dilate of the outer tube back into a dilate of the inner tube** (blueprint
`lem:rescalePullbackDilate`), stated forwards as a preimage.

In the rescaling situation, with the inner direction nearly parallel to the ambient axis
(`‖f - ⟪e, f⟫ • e‖ ≤ κ θ`) and `V = ext_σ[Ψ(T.x), Ψ(T.y)]` the outer tube of the image core,
every point whose image under `Ψ = Tube.rescaleMap T₀ R` lies in the dilate `c · V` lies in the
dilate `(4 (κ + 2) R c) · T` downstairs.

This is the step that makes a *downstairs* selection possible: a failure of essential
distinctness upstairs is turned by `Kakeya.Tube.tubeOverlapCoreClose` into a containment in
`C_n · V`, and this lemma turns that into a containment in a bounded dilate of the original
`τ`-tube, where `Tube.essDistinctTubesInSelfDilate` counts.  The two values used downstream
are `κ = 2`, which is `Tube.perp_norm_core_sub_le_of_subset` for `T ⊆ T₀`, and `κ = 4`, which
is `Tube.perp_norm_core_sub_le_of_subset_dilate` at `c = 2` for `T ⊆ 2 · T₀`.

The hypothesis `hxy` is not a restriction: `Ψ` is injective for `0 < θ` and `R ≠ 0`, and
`T.x ≠ T.y` because `dist T.x T.y = 1` (`Tube.dist_eq_one`).  It is taken as a hypothesis
rather than derived so that the outer tube `Tube.centredExtension σ hxy` can be named in the
statement.

Assembly, from the two pullbacks above: `Kakeya.Tube.dilate_carrier_eq_cthickening` together
with `Tube.center_centredExtension` and `Tube.direction_centredExtension` writes a point of
`c · V` as `Ψ(T.center) + t • f̂ + v` with `|t| ≤ c / 2` and `‖v‖ ≤ c σ`; pulling back with
`Tube.rescale_symm_apply_add_smul` and `Tube.norm_rescale_symm_vector_le` at `s = c σ` puts the
point within `4 R (κ + 1) c τ` of the segment of length `8 R c` centred at `T.center` along
`f`, using `θ ≤ 1` and `σ ≤ 1/4` along `f` and `σ ≤ τ / θ` across it — both of which are
fields of `Tube.IsRescalingSituation`. -/
theorem preimage_rescale_dilate_subset_dilate {n : ℕ} {R κ c : ℝ}
    (hsit : IsRescalingSituation θ τ σ R n) (hκ : 0 ≤ κ) (hc : 1 ≤ c)
    (T₀ : Tube θ E) (T : Tube τ E)
    (hperp : ‖T.direction - (inner ℝ T₀.direction T.direction : ℝ) • T₀.direction‖
      ≤ κ * (θ : ℝ))
    (hxy : T₀.rescaleMap R T.x ≠ T₀.rescaleMap R T.y) :
    (T₀.rescaleMap R) ⁻¹' (Kakeya.Tube.dilate (centredExtension σ hxy) c).carrier
      ⊆ (Kakeya.Tube.dilate T (4 * (κ + 2) * R * c)).carrier := by
  classical
  let c' : ℝ := 4 * (κ + 2) * R * c
  let m : E := T.center
  let f : E := T.direction
  let V : Tube σ E := centredExtension σ hxy
  let Ψ : E →ᵃ[ℝ] E := T₀.rescaleMap R
  let D : E := Ψ T.y - Ψ T.x
  have hθ : 0 < θ := hsit.pos_ambient
  have hθ1 : θ ≤ 1 := hsit.ambient_le_one
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hR : 0 < R := by
    have h1 : (1 : ℝ) ≤ (normalization.C n : ℝ) := by exact_mod_cast normalization.one_le_C n
    exact lt_of_lt_of_le zero_lt_one (le_trans h1 hsit.normalizationConst_le_radius)
  have hc' : 0 < c' := by
    dsimp [c']
    have hk2 : 0 < κ + 2 := by linarith
    positivity
  have hθσ : (θ : ℝ) * (σ : ℝ) ≤ (τ : ℝ) := by
    have h2 : (σ : ℝ) * (θ : ℝ) ≤ (τ : ℝ) := by
      exact (le_div_iff₀ (show (0 : ℝ) < (θ : ℝ) by exact_mod_cast hθ)).mp hsit.out_le_ratio
    simpa [mul_comm] using h2
  have hVcenter : V.center = Ψ m := by
    dsimp [V, m, Ψ]
    rw [center_centredExtension]
    exact (AffineMap.map_midpoint (T₀.rescaleMap R) T.x T.y).symm
  have hVdir : V.direction = ‖D‖⁻¹ • D := by
    dsimp [V, D]
    exact direction_centredExtension hxy
  rintro z hz
  have hzV : Ψ z ∈ (Kakeya.Tube.dilate V c).carrier := by simpa [Ψ] using hz
  obtain ⟨α, hα, htv⟩ := Kakeya.Tube.exists_axis_repr_of_mem_dilate V hc0 hzV
  obtain ⟨t', htb, hmain'⟩ := rescale_symm_apply_add_smul hθ hθ1 hR T₀ T α m
  have hmain : Ψ (m + t' • f) = Ψ m + (α * ‖D‖⁻¹) • D := by
    simpa [Ψ, f, D] using hmain'
  let w₀ : E := m + t' • f
  have hΨw₀ : Ψ w₀ = Ψ m + (α * ‖D‖⁻¹) • D := by
    dsimp [w₀]
    exact hmain
  have hVcen : V.center + α • V.direction = Ψ w₀ := by
    calc
      V.center + α • V.direction = Ψ m + α • (‖D‖⁻¹ • D) := by rw [hVcenter, hVdir]
      _ = Ψ m + (α * ‖D‖⁻¹) • D := by
        congr 1
        module
      _ = Ψ w₀ := by rw [← hΨw₀]
  let u : E := z - w₀
  have hzu : w₀ + u = z := by dsimp [u]; abel
  let v : E := Ψ z - Ψ w₀
  have hΘ : Ψ (w₀ + u) = Ψ w₀ + v := by
    rw [hzu]
    dsimp [v]
    abel
  let s : ℝ := c * (σ : ℝ)
  have hΘs : (0 : ℝ) ≤ s := by dsimp [s]; positivity
  have hv : ‖v‖ ≤ s := by
    dsimp [v, s]
    rw [← hVcen]
    exact htv
  have hvec : |(inner ℝ T.direction u : ℝ)| ≤ 4 * R * (1 + (θ : ℝ)) * s ∧
      ‖u - (inner ℝ T.direction u : ℝ) • T.direction‖ ≤ 4 * R * (κ + 1) * (θ : ℝ) * s := by
    exact norm_rescale_symm_vector_le (κ := κ) (s := s) hθ hθ1 hR T₀ T hκ
      hΘs hperp hΘ hv
  let β : ℝ := (inner ℝ f (z - m) : ℝ)
  have hff : (inner ℝ f f : ℝ) = 1 := by
    dsimp [f]
    rw [real_inner_self_eq_norm_sq, T.norm_direction]
    norm_num
  have hz_sub : z - m = t' • f + u := by
    dsimp [u, w₀, m]
    abel
  have hβeq : β = t' + (inner ℝ f u : ℝ) := by
    dsimp [β]
    calc
      (inner ℝ f (z - m) : ℝ) = (inner ℝ f (t' • f + u) : ℝ) := by
        rw [hz_sub]
      _ = t' * (inner ℝ f f : ℝ) + (inner ℝ f u : ℝ) := by
        simp [inner_add_right, inner_smul_right]
      _ = t' + (inner ℝ f u : ℝ) := by
        rw [hff]
        ring
  have htc : |t'| ≤ 2 * R * c := by
    calc
      |t'| ≤ 4 * R * |α| := htb
      _ ≤ 4 * R * (c / 2) := by
        exact mul_le_mul_of_nonneg_left hα (by positivity : (0 : ℝ) ≤ 4 * R)
      _ = 2 * R * c := by ring
  have h1σb : (1 + (θ : ℝ)) * (σ : ℝ) ≤ 1 / 2 := by
    have h2m : (1 + (θ : ℝ)) ≤ 2 := by
      have hth : (θ : ℝ) ≤ 1 := by exact_mod_cast hθ1
      linarith
    calc
      (1 + (θ : ℝ)) * (σ : ℝ) ≤ 2 * (σ : ℝ) :=
        mul_le_mul_of_nonneg_right h2m (NNReal.coe_nonneg σ)
      _ ≤ 2 * (1 / 4) := mul_le_mul_of_nonneg_left hsit.out_le_quarter (by norm_num : (0 : ℝ) ≤ 2)
      _ = 1 / 2 := by norm_num
  have hpar : |(inner ℝ f u : ℝ)| ≤ 2 * R * c := by
    calc
      |(inner ℝ f u : ℝ)| ≤ 4 * R * (1 + (θ : ℝ)) * (c * (σ : ℝ)) := by simpa [f, s] using hvec.1
      _ = (4 * R * c) * ((1 + (θ : ℝ)) * (σ : ℝ)) := by ring
      _ ≤ (4 * R * c) * (1 / 2) := by
        exact mul_le_mul_of_nonneg_left h1σb (by positivity : (0 : ℝ) ≤ 4 * R * c)
      _ = 2 * R * c := by ring
  have hβle : |β| ≤ 4 * R * c := by
    calc
      |β| = |t' + (inner ℝ f u : ℝ)| := by rw [hβeq]
      _ ≤ |t'| + |(inner ℝ f u : ℝ)| := abs_add_le _ _
      _ ≤ 2 * R * c + 2 * R * c := by exact add_le_add htc hpar
      _ = 4 * R * c := by ring
  have hbperp : 4 * R * (κ + 1) * (θ : ℝ) * (c * (σ : ℝ)) ≤ c' * (τ : ℝ) := by
    have hA : (κ + 1) * ((θ : ℝ) * (σ : ℝ)) ≤ (κ + 1) * (τ : ℝ) :=
      mul_le_mul_of_nonneg_left hθσ (by positivity : (0 : ℝ) ≤ κ + 1)
    have hB : (κ + 1) * (τ : ℝ) ≤ (κ + 2) * (τ : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith) (NNReal.coe_nonneg τ)
    calc
      4 * R * (κ + 1) * (θ : ℝ) * (c * (σ : ℝ))
          = (4 * R * c) * ((κ + 1) * ((θ : ℝ) * (σ : ℝ))) := by ring
      _ ≤ (4 * R * c) * ((κ + 2) * (τ : ℝ)) := by
        exact mul_le_mul_of_nonneg_left (le_trans hA hB) (by positivity : (0 : ℝ) ≤ 4 * R * c)
      _ = c' * (τ : ℝ) := by
        dsimp [c']
        ring
  have hz_perp : z - m - β • f = u - (inner ℝ f u : ℝ) • f := by
    rw [hz_sub, hβeq]
    module
  have hperp2 : ‖z - m - β • f‖ ≤ c' * (τ : ℝ) := by
    rw [hz_perp]
    calc
      ‖u - (inner ℝ f u : ℝ) • f‖ ≤ 4 * R * (κ + 1) * (θ : ℝ) * (c * (σ : ℝ)) :=
        by simpa [f, s] using hvec.2
      _ ≤ c' * (τ : ℝ) := hbperp
  have hβc' : |β| ≤ c' / 2 := by
    calc
      |β| ≤ 4 * R * c := hβle
      _ ≤ 2 * (κ + 2) * R * c := by
        have h4 : (4 : ℝ) ≤ 2 * (κ + 2) := by linarith [hκ]
        calc
          4 * R * c = 4 * (R * c) := by ring
          _ ≤ (2 * (κ + 2)) * (R * c) :=
            mul_le_mul_of_nonneg_right h4 (by positivity : (0 : ℝ) ≤ R * c)
          _ = 2 * (κ + 2) * R * c := by ring
      _ = c' / 2 := by
        dsimp [c']
        ring
  have hnn : ‖z - (m + β • f)‖ ≤ c' * (τ : ℝ) := by
    rw [show z - (m + β • f) = z - m - β • f by abel]
    exact hperp2
  have hdist : dist z (T.center + β • T.direction) ≤ c' * (τ : ℝ) := by
    rw [dist_eq_norm]
    simpa [m, f] using hnn
  have hland : z ∈ (Kakeya.Tube.dilate T c').carrier :=
    Kakeya.Tube.mem_dilate_of_dist_axis_le T hc' hβc' hdist
  simpa [c'] using hland

/-! ### The affine replacement package

The two declarations below are the affine substitutes for `Tube.card_le_mul_card_of_dilateCover`
and `Tube.exists_comparableReplacement` on the fine-normalization route (blueprint
`lem:comparableAffineFibreBound` and `lem:comparableAffineImagesToTubes`).  The hypothesis that
changes is the inner one: the inner honest `C⁻¹ ρ`-tubes `U_i ⊆ W_i` of the non-affine lemmas
— which that route *cannot* supply, the homothety of `Tube.rescaleMap` having shortened the
image core below unit length — give way to the hypothesis that the `W_i` are the images under
one invertible affine map `Ψ = Tube.rescaleMap T₀ R` of honest, pairwise essentially distinct
`τ`-tubes lying nearly parallel to the ambient axis.  The selection is then made *downstairs*,
through `Tube.preimage_rescale_dilate_subset_dilate` and `Tube.essDistinctTubesInSelfDilate`,
and the constant changes accordingly.

Everything else is unchanged: the multiplicity, fullness and Frostman items are proved from the
one-sided data alone and are literally `Tube.comparableTransport_oneSided`. -/

/-- **The fibre bound for a selection made downstairs** (blueprint
`lem:comparableAffineFibreBound`).

The affine analogue of `Tube.card_le_mul_card_of_dilateCover`.  The fibres
`A_i = {j ∈ s | 𝕋 j ⊆ c' · 𝕋 i}`, `i ∈ s'`, with `c' = 4 (κ + 2) R C_n`, cover `s`: a
`j ∈ s` has some `i ∈ s'` with `V_j ⊆ C_n · V_i`, and then
`Ψ(𝕋 j) ⊆ V_j ⊆ C_n · V_i`, so `Tube.preimage_rescale_dilate_subset_dilate` at `c = C_n`
puts `𝕋 j` inside `c' · 𝕋 i`.  Each fibre has at most
`Tube.essDistinctTubesInSelfDilate.C n c'` elements, the tubes `(𝕋 j)_{j ∈ A_i}` being
pairwise essentially distinct `τ`-tubes inside a dilate of the `τ`-tube `𝕋 i`; the cardinality
bound is then `Kakeya.card_le_card_cover_mul`.

The hypothesis `hxy` is not a restriction (see `Tube.preimage_rescale_dilate_subset_dilate`);
it is taken as a hypothesis so that the outer tubes `ext_σ[Ψ(𝕋 i).x, Ψ(𝕋 i).y]` can be named
in the statement. -/
theorem card_le_mul_card_of_dilateCover_affine {ι : Type*} [Nontrivial E] {n : ℕ} {R κ : ℝ}
    (hsit : IsRescalingSituation θ τ σ R n) (hκ : 0 ≤ κ) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1)
    (T₀ : Tube θ E) {s s' : Finset ι} (hs' : s' ⊆ s) (𝕋 : ι → Tube τ E)
    (hxy : ∀ i : ι, T₀.rescaleMap R (𝕋 i).x ≠ T₀.rescaleMap R (𝕋 i).y)
    (hperp : ∀ i ∈ s, ‖(𝕋 i).direction
      - (inner ℝ T₀.direction (𝕋 i).direction : ℝ) • T₀.direction‖ ≤ κ * (θ : ℝ))
    (hTED : (↑s : Set ι).Pairwise fun i j =>
      IsEssentiallyDistinct (𝕋 i).carrier (𝕋 j).carrier)
    (himg : ∀ i ∈ s, (T₀.rescaleMap R) '' (𝕋 i).carrier ⊆ (centredExtension σ (hxy i)).carrier)
    (hcover : ∀ j ∈ s, ∃ i ∈ s', (centredExtension σ (hxy j)).carrier
      ⊆ (Kakeya.Tube.dilate (centredExtension σ (hxy i))
          (Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E))).carrier) :
    (s.card : ENNReal)
      ≤ (essDistinctTubesInSelfDilate.C (Module.finrank ℝ E)
          (4 * (κ + 2) * R
            * Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E)) : ENNReal)
        * (s'.card : ENNReal) := by
  classical
  let Cn : ℝ := Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E)
  let c' : ℝ := 4 * (κ + 2) * R * Cn
  let Cb : NNReal := essDistinctTubesInSelfDilate.C (Module.finrank ℝ E) c'
  let A : ι → Finset ι := fun i =>
    s.filter (fun j => (𝕋 j).carrier ⊆ (Kakeya.Tube.dilate (𝕋 i) c').carrier)
  have hA : ∀ i, A i ⊆ s := by
    intro i
    exact
      Finset.filter_subset (fun j => (𝕋 j).carrier ⊆ (Kakeya.Tube.dilate (𝕋 i) c').carrier) s
  have hCn1 : (1 : ℝ) ≤ Cn := by
    dsimp [Cn]
    exact_mod_cast
      (le_of_lt (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C (Module.finrank ℝ E)))
  have hc'1 : 1 ≤ c' := by
    dsimp [c', Cn]
    have hR : (1 : ℝ) ≤ R := by
      exact le_trans (by exact_mod_cast normalization.one_le_C n)
        hsit.normalizationConst_le_radius
    have hk1 : (1 : ℝ) ≤ κ + 2 := by linarith
    have hC1 : (1 : ℝ) ≤ Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) := by
      exact_mod_cast
        (le_of_lt (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C (Module.finrank ℝ E)))
    have h1 : (1 : ℝ) ≤ (κ + 2) * R := by nlinarith
    have h2 : (1 : ℝ) ≤ (κ + 2) * R
        * Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) := by
      nlinarith
    nlinarith
  have hcover_fibres : s ⊆ s'.biUnion A := by
    intro j hj
    rcases hcover j hj with ⟨i, hi, hjd⟩
    have hpre : (𝕋 j).carrier
        ⊆ (T₀.rescaleMap R) ⁻¹' (Kakeya.Tube.dilate (centredExtension σ (hxy i))
          Cn).carrier := by
      exact Set.image_subset_iff.mp (Set.Subset.trans (himg j hj) hjd)
    have hback : (T₀.rescaleMap R) ⁻¹' (Kakeya.Tube.dilate (centredExtension σ (hxy i))
          Cn).carrier ⊆ (Kakeya.Tube.dilate (𝕋 i) c').carrier := by
      simpa [c'] using
        preimage_rescale_dilate_subset_dilate hsit hκ hCn1 T₀ (𝕋 i)
          (hperp i (hs' hi)) (hxy i)
    have hT : (𝕋 j).carrier ⊆ (Kakeya.Tube.dilate (𝕋 i) c').carrier :=
      Set.Subset.trans hpre hback
    exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_filter.mpr ⟨hj, hT⟩⟩
  have hfibre_enn : ∀ i ∈ s', ((A i).card : ENNReal) ≤ (Cb : ENNReal) := by
    intro i hi
    have hAi_ED : (↑(A i) : Set ι).Pairwise
        (fun j k => IsEssentiallyDistinct (𝕋 j).carrier (𝕋 k).carrier) := by
      exact hTED.mono (Finset.coe_subset.mpr (hA i))
    have hUT : ∀ j ∈ A i, (𝕋 j).carrier ⊆ (Kakeya.Tube.dilate (𝕋 i) c').carrier := by
      intro j hJ
      exact (Finset.mem_filter.mp hJ).2
    simpa [Cb] using
      (essDistinctTubesInSelfDilate hc'1 hτ0 hτ1 (𝕋 i) (A i) 𝕋 hAi_ED hUT)
  calc
    (s.card : ENNReal) ≤ ((s'.biUnion A).card : ENNReal) := by
      exact_mod_cast (Finset.card_le_card hcover_fibres)
    _ ≤ (∑ i ∈ s', (A i).card : ENNReal) := by
      exact_mod_cast (Finset.card_biUnion_le (t := A))
    _ ≤ (∑ i ∈ s', (Cb : ENNReal)) := by
      exact Finset.sum_le_sum (fun i hi => hfibre_enn i hi)
    _ = (Cb : ENNReal) * (s'.card : ENNReal) := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- **The conclusions of `Tube.exists_comparableReplacement_affine`, one field per item.**

This is `Tube.IsComparableReplacement` with the selection constant
`Tube.comparableReplacement.C n C` freed to a variable `C₁`, and with the nonemptiness of the
retained index set added to the `select` field, as blueprint
`lem:comparableAffineImagesToTubes`\ `item:affineReplaceSelect` states it.  The two structures
are otherwise identical, field for field; they are separate because the existing one is
imported widely and its selection constant is part of its meaning. -/
structure IsComparableReplacementFree {ι : Type*} {ρ : NNReal} (s : Finset ι)
    (𝕎 : ι → ShadedBody E) (𝕍 : ι → ShadedTube ρ E) (K : ConvexSpaceBody E)
    (C Λ C₁ : NNReal) : Prop where
  /-- (i) Multiplicity is unchanged: it depends only on the shading, not on the bodies
  carrying it. -/
  multiplicity : ShadedBody.multiplicity s (fun i => (𝕍 i).toShadedBody)
    = ShadedBody.multiplicity s 𝕎
  /-- (ii) Fullness drops by at most the comparability factor `C`. -/
  fullness : C⁻¹ * ShadedBody.fullness s 𝕎 ≤ ShadedBody.fullness s (fun i => (𝕍 i).toShadedBody)
  /-- (iii) The Frostman constant in `K` grows by at most the comparability factor `C`. -/
  frostmanConstIn : ConvexSpaceBody.frostmanConstIn s (fun i => (𝕍 i).toConvexSpaceBody) K
    ≤ (C : ENNReal) * ConvexSpaceBody.frostmanConstIn s (fun i => (𝕎 i).toConvexSpaceBody) K
  /-- (iv) There is a nonempty `s' ⊆ s` indexing a pairwise essentially distinct subfamily of
  `𝕍` with `|s| ≤ C₁ |s'|`, and (v) for that `s'` the restricted shaded family is a
  `(C₁ Λ²)⁻¹`-refinement of `(𝕍, Z)`. -/
  select : ∃ s' ⊆ s, s'.Nonempty ∧
    (↑s' : Set ι).Pairwise (fun i j => IsEssentiallyDistinct (𝕍 i).carrier (𝕍 j).carrier) ∧
    (s.card : ENNReal) ≤ (C₁ : ENNReal) * (s'.card : ENNReal) ∧
    ShadedBody.IsCRefinement s' (fun i => (𝕍 i).toShadedBody) s (fun i => (𝕍 i).toShadedBody)
      (C₁ * Λ ^ 2)⁻¹

/-- **Replacing affine images of tubes by honest tubes, selecting downstairs** (blueprint
`lem:comparableAffineImagesToTubes`).

This is `Tube.exists_comparableReplacement` with one hypothesis replaced by another: the inner
honest tubes `U_i ⊆ W_i` there — which cannot be supplied on the fine-normalization route —
give way to the hypothesis that the `W_i` sit inside the images under one invertible affine map
`Ψ = Tube.rescaleMap T₀ R` of honest, pairwise essentially distinct `τ`-tubes `𝕋 i` lying
nearly parallel to the ambient axis, and that the outer `σ`-tubes are the centred extensions
`ext_σ[Ψ(𝕋 i).x, Ψ(𝕋 i).y]` of the image cores.

Items (i)–(iii) are unchanged and are `Tube.comparableTransport_oneSided`, proved from the
one-sided data `W_i ⊆ V_i ⊆ K` and `|V_i| ≤ C |W_i|` alone.  The change is confined to items
(iv)–(v), which now go through `Tube.card_le_mul_card_of_dilateCover_affine`, and to the
selection constant, which is `Tube.essDistinctTubesInSelfDilate.C n (4 (κ + 2) R C_n)` rather
than `Tube.comparableReplacement.C n C`; the refinement clause is therefore cited at the free
constant, as `Tube.isCRefinement_of_card_le_free`. -/
theorem exists_comparableReplacement_affine {ι : Type*} [Nontrivial E] {n : ℕ} {R κ : ℝ}
    {s : Finset ι} (hs : s.Nonempty)
    (hsit : IsRescalingSituation θ τ σ R n) (hκ : 0 ≤ κ) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1)
    (T₀ : Tube θ E) (𝕋 : ι → Tube τ E)
    (hxy : ∀ i : ι, T₀.rescaleMap R (𝕋 i).x ≠ T₀.rescaleMap R (𝕋 i).y)
    (𝕎 : ι → ShadedBody E) (𝕍 : ι → ShadedTube σ E) {C Λ : NNReal} (K : ConvexSpaceBody E)
    {W μ₀ : ENNReal} (hC : 1 ≤ C) (hΛ : 1 ≤ Λ) (hW : 0 < W) (hμ₀ : 0 < μ₀)
    (hcommon : ∀ i ∈ s, volume (𝕎 i).carrier = W)
    (hVtube : ∀ i ∈ s, (𝕍 i).toTube = centredExtension σ (hxy i))
    (hperp : ∀ i ∈ s, ‖(𝕋 i).direction
      - (inner ℝ T₀.direction (𝕋 i).direction : ℝ) • T₀.direction‖ ≤ κ * (θ : ℝ))
    (hTED : (↑s : Set ι).Pairwise fun i j =>
      IsEssentiallyDistinct (𝕋 i).carrier (𝕋 j).carrier)
    (himg : ∀ i ∈ s, (T₀.rescaleMap R) '' (𝕋 i).carrier ⊆ ((𝕍 i).toTube).carrier)
    (hshade : ∀ i ∈ s, (𝕍 i).shade = (𝕎 i).shade)
    (hsub : ∀ i ∈ s, (𝕎 i).carrier ⊆ (𝕍 i).carrier)
    (hVK : ∀ i ∈ s, (𝕍 i).toConvexSpaceBody ≤ K)
    (hvol : ∀ i ∈ s, volume (𝕍 i).carrier ≤ (C : ENNReal) * volume (𝕎 i).carrier)
    (hZ : ∀ i ∈ s, (Λ : ENNReal)⁻¹ * μ₀ * W ≤ volume (𝕎 i).shade ∧
      volume (𝕎 i).shade ≤ (Λ : ENNReal) * μ₀ * W) :
    IsComparableReplacementFree s 𝕎 𝕍 K C Λ
      (essDistinctTubesInSelfDilate.C (Module.finrank ℝ E)
        (4 * (κ + 2) * R
          * Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E))) := by
  classical
  -- The output scale is an honest scale: 0 < σ ≤ 1.
  have hσ0 : 0 < σ := hsit.pos_out
  have hσ1 : σ ≤ 1 := by
    exact NNReal.coe_le_coe.mp
      (le_trans hsit.out_le_quarter (by norm_num : (1 / 4 : ℝ) ≤ (1 : ℝ)))
  -- The selection constants `Cn` and `c' = 4 (κ + 2) R Cn`.
  let Cn : ℝ := Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E)
  let c' : ℝ := 4 * (κ + 2) * R * Cn
  -- Items (i)-(iii): the one-sided transport, verbatim from
  -- `Tube.exists_comparableReplacement`.
  have htr := comparableTransport_oneSided hC s 𝕎 (fun i => (𝕍 i).toShadedBody) K
    (by intro i hi; exact (hshade i hi))
    (by intro i hi; exact SetLike.coe_subset_coe.mpr (hsub i hi))
    (by intro i hi; exact (hVK i hi))
    hvol
  -- Items (iv)-(v): the selection is made downstairs on the honest `τ`-tubes.
  obtain ⟨s', hs'sub, hpair, hcover⟩ :=
    exists_essDistinct_dilateCover hσ0 hσ1 s (fun i => (𝕍 i).toTube)
  have himg' : ∀ i ∈ s, (T₀.rescaleMap R) '' (𝕋 i).carrier ⊆
      (centredExtension σ (hxy i)).carrier := by
    intro i hi
    simpa [hVtube i hi] using himg i hi
  have hcover' : ∀ j ∈ s, ∃ i ∈ s',
      (centredExtension σ (hxy j)).carrier
        ⊆ (Kakeya.Tube.dilate (centredExtension σ (hxy i))
            (Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E))).carrier := by
    intro j hj
    rcases hcover j hj with ⟨i, hi, hcov⟩
    refine ⟨i, hi, ?_⟩
    simpa [hVtube j hj, hVtube i (hs'sub hi)] using hcov
  have hcard : (s.card : ENNReal)
      ≤ (essDistinctTubesInSelfDilate.C (Module.finrank ℝ E) c' : ENNReal)
        * (s'.card : ENNReal) := by
    exact card_le_mul_card_of_dilateCover_affine hsit hκ hτ0 hτ1 T₀ hs'sub
      𝕋 hxy hperp hTED himg' hcover'
  have hs'ne : s'.Nonempty := by
    rcases hs with ⟨j₀, hj₀⟩
    rcases hcover j₀ hj₀ with ⟨i, hi, _⟩
    exact ⟨i, hi⟩
  -- The selection constant `hC₁ = essDistinctTubesInSelfDilate.C n c'` is at
  -- least one, as the same count on a one-element family shows.
  have hc1 : (1 : ℝ) ≤ c' := by
    dsimp [c', Cn]
    have hR : (1 : ℝ) ≤ R := by
      exact le_trans (by exact_mod_cast normalization.one_le_C n)
        hsit.normalizationConst_le_radius
    have hk1 : (1 : ℝ) ≤ κ + 2 := by linarith
    have hC1 : (1 : ℝ) ≤
        Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) := by
      exact_mod_cast
        (le_of_lt (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C (Module.finrank ℝ E)))
    have h1 : (1 : ℝ) ≤ (κ + 2) * R := by nlinarith
    have h2 : (1 : ℝ) ≤ (κ + 2) * R
        * Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) := by
      nlinarith
    nlinarith
  have hC₁ : (1 : NNReal) ≤
      essDistinctTubesInSelfDilate.C (Module.finrank ℝ E) c' := by
    rcases hs with ⟨i₀, hi₀⟩
    have hpw₀ : (↑({i₀} : Finset ι) : Set ι).Pairwise
        (fun i j : ι => IsEssentiallyDistinct (𝕋 i).carrier (𝕋 j).carrier) := by
      simp
    have hsub₀ : ∀ j ∈ ({i₀} : Finset ι),
        (𝕋 j).carrier ⊆ (Kakeya.Tube.dilate (𝕋 i₀) c').carrier := by
      intro j hj
      have hji : j = i₀ := by simpa using hj
      subst j
      exact Tube.subset_dilate (𝕋 i₀) hc1
    have hcount₀ : (({i₀} : Finset ι).card : ENNReal)
        ≤ (essDistinctTubesInSelfDilate.C (Module.finrank ℝ E) c' : ENNReal) :=
      essDistinctTubesInSelfDilate hc1 hτ0 hτ1 (𝕋 i₀)
        ({i₀} : Finset ι) 𝕋 hpw₀ hsub₀
    exact ENNReal.coe_le_coe.mp (by simpa using hcount₀)
  -- `W` and `μ₀` are finite, so the refinement can be cited at the free constant.
  have hW_top : W ≠ ⊤ := by
    rcases hs with ⟨i₀, hi₀⟩
    have hWtop' : volume (𝕎 i₀).carrier ≠ ⊤ := (𝕎 i₀).isCompact.measure_ne_top
    rw [hcommon i₀ hi₀] at hWtop'
    exact hWtop'
  have hμ₀_top : μ₀ ≠ ⊤ := by
    rcases hs with ⟨i₀, hi₀⟩
    have hshade_lt : volume (𝕎 i₀).shade < ⊤ := by
      calc
        volume (𝕎 i₀).shade ≤ volume (𝕎 i₀).carrier := measure_mono (𝕎 i₀).shade_subset
        _ = W := hcommon i₀ hi₀
        _ < ⊤ := hW_top.lt_top
    have hLHS_lt : (Λ : ENNReal)⁻¹ * μ₀ * W < ⊤ :=
      lt_of_le_of_lt (hZ i₀ hi₀).1 hshade_lt
    intro hμ₀top
    have hΛ_inv_ne_zero : (Λ : ENNReal)⁻¹ ≠ 0 :=
      ENNReal.inv_ne_zero.mpr (by exact ENNReal.coe_ne_top)
    have hLHS_eq : (Λ : ENNReal)⁻¹ * μ₀ * W = ⊤ := by
      rw [hμ₀top, ENNReal.mul_top hΛ_inv_ne_zero, ENNReal.top_mul (ne_of_gt hW)]
    rw [hLHS_eq] at hLHS_lt
    exact lt_irrefl _ hLHS_lt
  have hcref : ShadedBody.IsCRefinement s' (fun i => (𝕍 i).toShadedBody) s
      (fun i => (𝕍 i).toShadedBody)
      (essDistinctTubesInSelfDilate.C (Module.finrank ℝ E) c' * Λ ^ 2)⁻¹ := by
    exact isCRefinement_of_card_le_free hC₁ hΛ (ne_of_gt hW) hW_top (ne_of_gt hμ₀) hμ₀_top
      hs'sub 𝕍
      (by intro i hi; simpa [hshade i hi] using (hZ i hi).1)
      (by intro i hi; simpa [hshade i hi] using (hZ i hi).2)
      hcard
  exact ⟨htr.1, htr.2.1, htr.2.2, ⟨s', hs'sub, hs'ne, by simpa using hpair, hcard, hcref⟩⟩

/-! ### Step 2 of the fine normalization: the outer tube of a rescaled tube

The four auxiliary declarations below are the metric and measure layer of `Tube.rescaleMap`
that blueprint `lem:coreOuterTube` and `lem:rescaleImageVolumeRatio` need, followed by those
two lemmas themselves.  `Ψ = Tube.rescaleMap T₀ R` is the normalization `Φ_{T₀}` followed by
the homothety `z ↦ (z - T₀.x) / (4 R)`; being an affine equivalence with constant Jacobian it
divides every distance by `4 R` and every volume by `(4 R) ^ n`, on top of the factor
`θ ^ -(n-1)` of `Tube.volume_image_normalization`. -/

/-- **`Ψ` is an affine equivalence.**  For `0 < θ` and `0 < R` the map `Tube.rescaleMap T₀ R`
is the underlying affine map of an affine equivalence of `E`: it is `Tube.normalizationEquiv`
followed by a translation and a nonzero homothety.  Stated existentially, exactly as the
corresponding step inside `ShadedTube.normalizeInto_transport`, so that the transport lemmas
of `Kakeya/AffineMap.lean` — which take an `E ≃ᵃ[ℝ] E` — apply to `Ψ`. -/
theorem exists_rescaleEquiv (hθ : 0 < θ) {R : ℝ} (hR : 0 < R) (T₀ : Tube θ E) :
    ∃ L : E ≃ᵃ[ℝ] E, L.toAffineMap = T₀.rescaleMap R := by
  have h4R : (4 * R : ℝ) ≠ 0 := mul_ne_zero (by norm_num : (4 : ℝ) ≠ 0) (ne_of_gt hR)
  let α : ℝˣ := ⟨(4 * R)⁻¹, 4 * R, inv_mul_cancel₀ h4R, mul_inv_cancel₀ h4R⟩
  let h : E ≃ₗ[ℝ] E := α • (LinearEquiv.refl ℝ E)
  let L : E ≃ᵃ[ℝ] E :=
    ((normalizationEquiv hθ T₀).trans (AffineEquiv.constVAdd ℝ E (-T₀.x))).trans h.toAffineEquiv
  refine ⟨L, ?_⟩
  apply AffineMap.ext
  intro z
  rw [rescaleMap_apply]
  simp [L, h, α]
  rw [smul_sub]
  abel

/-- **`Ψ` divides every distance by `4 R`** (the homothety half of `Tube.rescaleMap`). -/
theorem dist_rescaleMap (T₀ : Tube θ E) {R : ℝ} (hR : 0 < R) (z w : E) :
    dist (T₀.rescaleMap R z) (T₀.rescaleMap R w)
      = dist (T₀.normalization z) (T₀.normalization w) / (4 * R) := by
  have h4R : (0 : ℝ) < 4 * R := by positivity
  calc
    dist (T₀.rescaleMap R z) (T₀.rescaleMap R w)
        = ‖T₀.rescaleMap R z - T₀.rescaleMap R w‖ := by rw [dist_eq_norm]
    _ = ‖(4 * R)⁻¹ • (T₀.normalization z - T₀.normalization w)‖ := by
          rw [rescaleMap_apply, rescaleMap_apply]
          rw [← smul_sub, sub_sub_sub_cancel_right]
    _ = |(4 * R)⁻¹| * dist (T₀.normalization z) (T₀.normalization w) := by
          rw [norm_smul, Real.norm_eq_abs, ← dist_eq_norm]
    _ = (4 * R)⁻¹ * dist (T₀.normalization z) (T₀.normalization w) := by
          rw [abs_inv, abs_of_pos h4R]
    _ = dist (T₀.normalization z) (T₀.normalization w) / (4 * R) := by
          ring

/-- **`Ψ` has constant Jacobian `(4 R) ^ -n · θ ^ -(n-1)`**: the homothety of ratio `(4 R)⁻¹`
composed with `Tube.volume_image_normalization`. -/
theorem volume_image_rescaleMap [Nontrivial E] (hθ : 0 < θ) {R : ℝ} (hR : 0 < R)
    (T₀ : Tube θ E) (A : Set E) :
    volume (T₀.rescaleMap R '' A)
      = ENNReal.ofReal ((4 * R)⁻¹ ^ (Module.finrank ℝ E))
          * ((θ : ENNReal)⁻¹ ^ (Module.finrank ℝ E - 1) * volume A) := by
  set M : E →ₗ[ℝ] E := (4 * R)⁻¹ • LinearMap.id
  have hnn : (0 : ℝ) ≤ (4 * R)⁻¹ := inv_nonneg.mpr (mul_nonneg (by norm_num) hR.le)
  have hdet : LinearMap.det M = (4 * R)⁻¹ ^ (Module.finrank ℝ E) := by
    simp [M]
  have hRescale (z : E) : T₀.rescaleMap R z = (-(4 * R)⁻¹ • T₀.x) + M (T₀.normalization z) := by
    rw [rescaleMap_apply]
    simp [M, sub_eq_add_neg, add_comm]
  have himg : T₀.rescaleMap R '' A =
      (fun z => (-(4 * R)⁻¹ • T₀.x) + z) '' (M '' (T₀.normalization '' A)) := by
    rw [← Set.image_comp, ← Set.image_comp]
    exact Set.image_congr' hRescale
  have hvadd (v : E) (S : Set E) : volume ((fun z => v + z) '' S) = volume S := by
    rw [Set.image_add_left]; exact measure_preimage_vadd (μ := volume) (-v) S
  rw [himg, hvadd, Measure.addHaar_image_linearMap, hdet, abs_of_nonneg (pow_nonneg hnn _),
    volume_image_normalization hθ T₀ A]

/-- **A `cthickening` bound upstairs is a `cthickening` bound downstairs**, at radius divided
by `4 R`: `Ψ` is `Φ_{T₀}` followed by a homothety of ratio `(4 R)⁻¹`, which carries the
segment `[Φ p, Φ q]` to `[Ψ p, Ψ q]` and scales every distance by `(4 R)⁻¹`. -/
theorem rescaleMap_image_subset_cthickening (T₀ : Tube θ E) {R : ℝ} (hR : 0 < R)
    {r : ℝ} (hr : 0 ≤ r) {A : Set E} {p q : E}
    (h : T₀.normalization '' A
      ⊆ cthickening r (segment ℝ (T₀.normalization p) (T₀.normalization q))) :
    T₀.rescaleMap R '' A
      ⊆ cthickening (r / (4 * R))
          (segment ℝ (T₀.rescaleMap R p) (T₀.rescaleMap R q)) := by
  let g : E →ᵃ[ℝ] E :=
    (((4 * R)⁻¹ • (LinearMap.id : E →ₗ[ℝ] E)).toAffineMap).comp
      (AffineEquiv.constVAdd ℝ E (-T₀.x)).toAffineMap
  have hg_apply : ∀ w : E, g w = (4 * R)⁻¹ • (w - T₀.x) := by
    intro w
    simp [g, AffineEquiv.constVAdd, neg_add_eq_sub]
  have hg_rescale : ∀ w : E, g (T₀.normalization w) = T₀.rescaleMap R w := by
    intro w
    rw [hg_apply, rescaleMap_apply]
  have hg_segment :
      g '' segment ℝ (T₀.normalization p) (T₀.normalization q)
        = segment ℝ (T₀.rescaleMap R p) (T₀.rescaleMap R q) := by
    rw [image_segment, hg_rescale, hg_rescale]
  have hg_dist : ∀ a b : E, dist (g a) (g b) = dist a b / (4 * R) := by
    have h4R : (0 : ℝ) < 4 * R := by positivity
    intro a b
    calc
      dist (g a) (g b) = ‖g a - g b‖ := by rw [dist_eq_norm]
      _ = ‖(4 * R)⁻¹ • (a - b)‖ := by
        rw [hg_apply, hg_apply]
        rw [← smul_sub, sub_sub_sub_cancel_right]
      _ = |(4 * R)⁻¹| * dist a b := by
        rw [norm_smul, Real.norm_eq_abs, ← dist_eq_norm]
      _ = (4 * R)⁻¹ * dist a b := by
        rw [abs_inv, abs_of_pos h4R]
      _ = dist a b / (4 * R) := by ring
  have hseg_cpt : IsCompact (segment ℝ (T₀.normalization p) (T₀.normalization q)) :=
    isCompact_segment
  have hseg_ne : (segment ℝ (T₀.normalization p) (T₀.normalization q)).Nonempty :=
    ⟨T₀.normalization p, left_mem_segment ℝ (T₀.normalization p) (T₀.normalization q)⟩
  intro x hx
  rcases hx with ⟨w, hwA, rfl⟩
  have hΦw : T₀.normalization w
      ∈ cthickening r (segment ℝ (T₀.normalization p) (T₀.normalization q)) :=
    h ⟨w, hwA, rfl⟩
  rcases hseg_cpt.exists_infEDist_eq_edist hseg_ne (T₀.normalization w) with ⟨y, hy, hy_eq⟩
  have hdy : dist (T₀.normalization w) y ≤ r := by
    have hleq : infEDist (T₀.normalization w)
        (segment ℝ (T₀.normalization p) (T₀.normalization q)) ≤ ENNReal.ofReal r := by
      simpa using hΦw
    have hed : edist (T₀.normalization w) y ≤ ENNReal.ofReal r := by
      rw [← hy_eq]
      exact hleq
    rw [edist_dist] at hed
    exact (ENNReal.ofReal_le_ofReal_iff hr).mp hed
  apply Metric.mem_cthickening_of_dist_le
      (T₀.rescaleMap R w) (g y) (r / (4 * R))
      (segment ℝ (T₀.rescaleMap R p) (T₀.rescaleMap R q))
  · rw [← hg_segment]
    exact Set.mem_image_of_mem g hy
  · calc
      dist (T₀.rescaleMap R w) (g y) = dist (g (T₀.normalization w)) (g y) := by
        rw [← hg_rescale]
      _ = dist (T₀.normalization w) y / (4 * R) := by
        exact hg_dist _ _
      _ ≤ r / (4 * R) := by
        have h4R' : (0 : ℝ) ≤ 4 * R := by positivity
        exact div_le_div_of_nonneg_right hdy h4R'

/-- **The unit ball has volume at most `C_{Tube.volume_le}(n)`**: it lies inside the carrier of
a `1`-tube whose core starts at the origin, and `Tube.volume_le` bounds that carrier. -/
theorem volume_closedBall_one_le [Nontrivial E] :
    volume (closedBall (0 : E) 1) ≤ (volume_le.C (Module.finrank ℝ E) : ENNReal) := by
  rcases exists_ne (0 : E) with ⟨v, hv⟩
  let u : E := (‖v‖)⁻¹ • v
  have hu_norm : ‖u‖ = 1 := by
    dsimp [u]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg v))]
    exact inv_mul_cancel₀ (ne_of_gt (norm_pos_iff.mpr hv))
  let T : Tube 1 E := Tube.ofMidpointDirection 1 0 u hu_norm
  have hx : T.x = -((1 / 2 : ℝ) • u) := by simp [T, Tube.ofMidpointDirection]
  have hy : T.y = (1 / 2 : ℝ) • u := by simp [T, Tube.ofMidpointDirection]
  have h0 : (0 : E) ∈ segment ℝ T.x T.y := by
    rw [hx, hy]
    refine ⟨(1 / 2 : ℝ), (1 / 2 : ℝ), by norm_num, by norm_num, by norm_num, ?_⟩
    module
  have hsub : closedBall (0 : E) 1 ⊆ T.carrier := by
    rw [T.carrier_eq]
    exact Set.subset_iUnion₂ (s := fun z : E => fun _ : z ∈ segment ℝ T.x T.y =>
      Metric.closedBall z (1 : NNReal)) 0 h0
  have hvol : volume T.carrier ≤ (volume_le.C (Module.finrank ℝ E) : ENNReal) := by
    have h := Tube.volume_le (E := E) (δ := 1)
      (show (1 : NNReal) ≤ 1 from le_rfl) T
    simpa using h
  exact le_trans (measure_mono hsub) hvol

-- The upper half of `Tube.volume_centredExtension_le_mul_volume_rescale_image`: the outer tube
-- is an honest `σ`-tube with `σ ≤ 1`, so `Tube.volume_le` applies to it.
private lemma volume_centredExtension_le_aux [Nontrivial E] {R : ℝ} (hσ1 : σ ≤ 1)
    (T₀ : Tube θ E) (T : Tube τ E)
    (hxy : T₀.rescaleMap R T.x ≠ T₀.rescaleMap R T.y) :
    volume (centredExtension σ hxy).carrier
      ≤ (volume_le.C (Module.finrank ℝ E) : ENNReal)
        * (σ : ENNReal) ^ (Module.finrank ℝ E - 1) := by
  simpa [ENNReal.coe_mul, ENNReal.coe_pow] using
    Tube.volume_le hσ1 (centredExtension σ hxy)

-- The lower half of `Tube.volume_centredExtension_le_mul_volume_rescale_image`: the exact
-- Jacobian of `Ψ` against `Tube.le_volume`, with `σ ≤ τ / θ` absorbing the powers of `θ`.
private lemma le_volume_rescale_image_aux [Nontrivial E] {n : ℕ} {R : ℝ}
    (hsit : IsRescalingSituation θ τ σ R n) (hR : 0 < R)
    (T₀ : Tube θ E) (T : Tube τ E) :
    ENNReal.ofReal ((4 * R)⁻¹ ^ (Module.finrank ℝ E))
        * ((le_volume.c (Module.finrank ℝ E) : ENNReal)
          * (σ : ENNReal) ^ (Module.finrank ℝ E - 1))
      ≤ volume (T₀.rescaleMap R '' T.carrier) := by
  set m : ℕ := Module.finrank ℝ E
  set c : NNReal := le_volume.c m
  have hθ : 0 < θ := hsit.pos_ambient
  have hθne : (θ : NNReal) ≠ 0 := ne_of_gt hθ
  -- σ ≤ τ / θ as NNReal, from the ℝ inequality out_le_ratio
  have hσle_div : σ ≤ τ / θ := by
    change (σ : ℝ) ≤ ((τ / θ : NNReal) : ℝ)
    rw [NNReal.coe_div]
    exact hsit.out_le_ratio
  -- lift to ENNReal and rewrite the division as a product
  have hσle : (σ : ENNReal) ≤ (τ : ENNReal) * (θ : ENNReal)⁻¹ := by
    have h1 : (σ : ENNReal) ≤ ((τ / θ : NNReal) : ENNReal) := ENNReal.coe_le_coe.mpr hσle_div
    simpa [ENNReal.coe_div hθne, ENNReal.div_eq_inv_mul, mul_comm] using h1
  -- lower bound on the volume of the inner tube T
  have hTS : (c : ENNReal) * (τ : ENNReal) ^ (m - 1) ≤ volume T.carrier := by
    have h := Tube.le_volume T
    simpa [c, m] using h
  calc
    ENNReal.ofReal ((4 * R)⁻¹ ^ m) * ((c : ENNReal) * (σ : ENNReal) ^ (m - 1))
        ≤ ENNReal.ofReal ((4 * R)⁻¹ ^ m)
            * ((θ : ENNReal)⁻¹ ^ (m - 1) * volume T.carrier) := by
          have hinner : (c : ENNReal) * (σ : ENNReal) ^ (m - 1)
              ≤ (θ : ENNReal)⁻¹ ^ (m - 1) * volume T.carrier := by
            calc
              (c : ENNReal) * (σ : ENNReal) ^ (m - 1)
                  ≤ (c : ENNReal) * ((τ : ENNReal) * (θ : ENNReal)⁻¹) ^ (m - 1) := by
                    gcongr
              _ = (θ : ENNReal)⁻¹ ^ (m - 1) * ((c : ENNReal) * (τ : ENNReal) ^ (m - 1)) := by
                    simp [mul_pow, mul_assoc, mul_comm, mul_left_comm]
              _ ≤ (θ : ENNReal)⁻¹ ^ (m - 1) * volume T.carrier := by
                    gcongr
          gcongr
    _ = volume (T₀.rescaleMap R '' T.carrier) := by
          exact (Tube.volume_image_rescaleMap hsit.pos_ambient hR T₀ T.carrier).symm

-- The constant cancellation of `Tube.volume_centredExtension_le_mul_volume_rescale_image`:
-- `(C / c) (4 R) ^ m · (4 R) ^ -m · c = C`, for finite positive `c` and `0 < R`.
private lemma ofReal_ratio_mul_inv_pow {m : ℕ} {R : ℝ} (hR : 0 < R) {C c : NNReal}
    (hc : 0 < c) (X : ENNReal) :
    ENNReal.ofReal ((C : ℝ) / (c : ℝ) * (4 * R) ^ m)
        * (ENNReal.ofReal ((4 * R)⁻¹ ^ m) * ((c : ENNReal) * X))
      = (C : ENNReal) * X := by
  set a : ℝ := 4 * R
  set B : ℝ := (C : ℝ) / (c : ℝ)
  have ha : 0 < a := by positivity
  have hha : a ≠ 0 := ne_of_gt ha
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hA : 0 ≤ B * a ^ m := mul_nonneg hB (pow_nonneg ha.le m)
  have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hc)
  calc
    ENNReal.ofReal (B * a ^ m) * (ENNReal.ofReal (a⁻¹ ^ m) * ((c : ENNReal) * X))
        = (ENNReal.ofReal (B * a ^ m) * ENNReal.ofReal (a⁻¹ ^ m)) * ((c : ENNReal) * X) := by
          ac_rfl
    _ = ENNReal.ofReal ((B * a ^ m) * (a⁻¹) ^ m) * ((c : ENNReal) * X) := by
          rw [← ENNReal.ofReal_mul hA]
    _ = ENNReal.ofReal B * ((c : ENNReal) * X) := by
          have hcancel : (B * a ^ m) * (a⁻¹) ^ m = B := by
            rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ hha, one_pow, mul_one]
          rw [hcancel]
    _ = (ENNReal.ofReal B * (c : ENNReal)) * X := by ac_rfl
    _ = ENNReal.ofReal (B * (c : ℝ)) * X := by
          rw [← ENNReal.ofReal_coe_nnreal]
          rw [← ENNReal.ofReal_mul hB]
    _ = (C : ENNReal) * X := by
          have hcB : B * (c : ℝ) = (C : ℝ) := by
            dsimp [B]
            field_simp [hcR]
          rw [hcB]
          rw [ENNReal.ofReal_coe_nnreal]

/-- **The outer tube is volume-comparable to the rescaled image** (blueprint
`lem:rescaleImageVolumeRatio`).

In the rescaling situation, with `V = ext_σ[Ψ(T.x), Ψ(T.y)]` and `W = Ψ(T)`,

```
|V| ≤ (C_{Tube.volume_le}(n) / c_{Tube.le_volume}(n)) * (4 R) ^ n * |W|.
```

Upper bound: `V` is a `σ`-tube with `σ ≤ 1`, so `Tube.volume_le` gives
`|V| ≤ C_{volume_le}(n) σ ^ (n-1)`.  Lower bound: `Tube.volume_image_rescaleMap` and
`Tube.le_volume` give `|W| = (4 R) ^ -n θ ^ -(n-1) |T| ≥ (4 R) ^ -n c_{le_volume}(n) ρ ^ (n-1)`
with `ρ = τ / θ`, and `σ ≤ ρ` is `IsRescalingSituation.out_le_ratio`.  No sub-segment of the
image core is needed: the Jacobian is exact.  -/
theorem volume_centredExtension_le_mul_volume_rescale_image [Nontrivial E] {n : ℕ} {R : ℝ}
    (hsit : IsRescalingSituation θ τ σ R n) (hR : 0 < R)
    (T₀ : Tube θ E) (T : Tube τ E)
    (hxy : T₀.rescaleMap R T.x ≠ T₀.rescaleMap R T.y) :
    volume (centredExtension σ hxy).carrier
      ≤ ENNReal.ofReal ((volume_le.C (Module.finrank ℝ E) : ℝ)
            / (le_volume.c (Module.finrank ℝ E) : ℝ) * (4 * R) ^ (Module.finrank ℝ E))
        * volume (T₀.rescaleMap R '' T.carrier) := by
  set m : ℕ := Module.finrank ℝ E
  set c : NNReal := le_volume.c m
  set C : NNReal := volume_le.C m
  have hσ1 : σ ≤ 1 := by
    exact_mod_cast (le_trans hsit.out_le_quarter (by norm_num : (1 / 4 : ℝ) ≤ 1))
  have hc : 0 < c := by
    dsimp [c]
    exact le_volume.c_pos m
  calc
    volume (centredExtension σ hxy).carrier
        ≤ (C : ENNReal) * (σ : ENNReal) ^ (m - 1) := by
          simpa [C, m] using volume_centredExtension_le_aux hσ1 T₀ T hxy
      _ = ENNReal.ofReal ((C : ℝ) / (c : ℝ) * (4 * R) ^ m)
            * (ENNReal.ofReal ((4 * R)⁻¹ ^ m) * ((c : ENNReal) * (σ : ENNReal) ^ (m - 1))) := by
          exact (ofReal_ratio_mul_inv_pow hR hc (X := (σ : ENNReal) ^ (m - 1))).symm
      _ ≤ ENNReal.ofReal ((C : ℝ) / (c : ℝ) * (4 * R) ^ m) * volume (T₀.rescaleMap R '' T.carrier) := by
          gcongr
          exact le_volume_rescale_image_aux hsit hR T₀ T

/-- **The dimensional volume ratio at `n = 3` is `36 / π < 12`**: `C_{Tube.volume_le}(3) = 16`
and `c_{Tube.le_volume}(3) = √π ^ 3 / Γ(5/2) / 3 = 4 π / 9`. -/
theorem volume_ratio_three_le_twelve :
    (volume_le.C 3 : ℝ) / (le_volume.c 3 : ℝ) ≤ 12 := by
  unfold volume_le.C
  change (2 ^ (3 + 1) : ℝ) / (Real.sqrt Real.pi ^ 3 / Real.Gamma (3 / 2 + 1) / 3) ≤ 12
  have hGamma : Real.Gamma (3 / 2 + 1 : ℝ) = (3 / 4 : ℝ) * Real.sqrt Real.pi := by
    rw [Real.Gamma_add_one (by norm_num : (3 / 2 : ℝ) ≠ 0)]
    have hg : Real.Gamma (3 / 2 : ℝ) = (1 / 2 : ℝ) * Real.sqrt Real.pi := by
      rw [show (3 / 2 : ℝ) = (1 / 2 : ℝ) + 1 by norm_num,
        Real.Gamma_add_one (by norm_num : (1 / 2 : ℝ) ≠ 0), Real.Gamma_one_half_eq]
    rw [hg]
    ring
  have hsqrt3 : (Real.sqrt Real.pi) ^ 3 = Real.pi * Real.sqrt Real.pi := by
    rw [pow_succ, Real.sq_sqrt Real.pi_pos.le]
  rw [hGamma, hsqrt3]
  have hp : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hden : Real.pi * Real.sqrt Real.pi / ((3 / 4 : ℝ) * Real.sqrt Real.pi) / 3
      = (4 / 9 : ℝ) * Real.pi := by
    field_simp [hp.ne']
    ring
  rw [hden]
  norm_num
  rw [div_le_iff₀ (by positivity)]
  nlinarith [Real.pi_gt_three]

/-- **The tilt of an inner core against the ambient axis**, in the form that
`Tube.card_le_mul_card_of_dilateCover_affine` and `Tube.exists_comparableReplacement_affine`
consume it: `Tube.perp_norm_core_sub_le_of_subset` read at `T.direction = T.y - T.x` rather
than at `T.x - T.y`.  This is the instance `κ = 2` of their hypothesis `hperp`. -/
theorem perp_norm_direction_le_of_subset (T₀ : Tube θ E) (T : Tube τ E)
    (hT : T.carrier ⊆ T₀.carrier) :
    ‖T.direction - (inner ℝ T₀.direction T.direction : ℝ) • T₀.direction‖ ≤ 2 * (θ : ℝ) := by
  have h := (perp_norm_core_sub_le_of_subset T₀ T hT).2.2
  have hEq : T.direction - (inner ℝ T₀.direction T.direction : ℝ) • T₀.direction
      = -(T.x - T.y - (inner ℝ T₀.direction (T.x - T.y) : ℝ) • T₀.direction) := by
    simp only [Tube.direction]
    rw [show T.x - T.y = -(T.y - T.x) by abel, inner_neg_right, neg_smul]
    abel
  rw [hEq, norm_neg]
  exact h

/-- **The rescaled ambient tube lies in `B̄(0, 1/4)`**: `Φ_{T₀}(T₀) ⊆ B̄(T₀.x, C_N)` by
`Tube.normalization_image_ambient_subset_closedBall`, while `Ψ` divides every distance by
`4 R ≥ 4 C_N` and sends `T₀.x` to `0`. -/
theorem rescale_image_ambient_subset_closedBall (hθ : 0 < θ) (hθ1 : θ ≤ 1) {R : ℝ} (hR : 0 < R)
    (hCR : (normalization.C (Module.finrank ℝ E) : ℝ) ≤ R) (T₀ : Tube θ E) :
    T₀.rescaleMap R '' T₀.carrier ⊆ closedBall (0 : E) (1 / 4) := by
  rw [Set.image_subset_iff]
  intro w hw
  rw [Set.mem_preimage, Metric.mem_closedBall]
  have hmem : T₀.normalization w
      ∈ closedBall T₀.x (normalization.C (Module.finrank ℝ E) : ℝ) :=
    (normalization_image_ambient_subset_closedBall hθ hθ1 T₀)
      (Set.mem_image_of_mem T₀.normalization hw)
  have hdist : dist (T₀.normalization w) T₀.x
      ≤ (normalization.C (Module.finrank ℝ E) : ℝ) :=
    (Metric.mem_closedBall.mp hmem)
  calc
    dist (T₀.rescaleMap R w) (0 : E)
        = dist (T₀.rescaleMap R w) (T₀.rescaleMap R T₀.x) := by
          rw [← rescaleMap_apply_x]
    _ = dist (T₀.normalization w) (T₀.normalization T₀.x) / (4 * R) :=
          dist_rescaleMap T₀ hR w T₀.x
    _ = dist (T₀.normalization w) T₀.x / (4 * R) := by rw [normalization_apply_x]
    _ ≤ (normalization.C (Module.finrank ℝ E) : ℝ) / (4 * R) := by
      exact div_le_div_of_nonneg_right hdist (by positivity)
    _ ≤ R / (4 * R) := by
      exact div_le_div_of_nonneg_right hCR (by positivity)
    _ = 1 / 4 := by
      field_simp [show (4 * R : ℝ) ≠ 0 by positivity]

/-- **The unit ball is volume-comparable to the rescaled ambient tube**, at `n = 3`.

`|B̄(0,1)| ≤ C_{Tube.volume_le}(3)` by `Tube.volume_closedBall_one_le`, and
`|Ψ(T₀)| = (4R)^{-3} θ^{-2} |T₀| ≥ (4R)^{-3} c_{Tube.le_volume}(3)` by
`Tube.volume_image_rescaleMap` and `Tube.le_volume`; the ratio is therefore at most
`(C/c) (4R)^3 ≤ 12 (4R)^3 ≤ (4R)^6` for `R ≥ 1`.  This is the ambient-enlargement factor that
`Kakeya.ml1Boot.exists_fineNormalization` pays when the Frostman constant is read at `B₁`
instead of at `Ψ(T_τ)` (`ConvexSpaceBody.frostmanConstIn_ambient_mono`). -/
theorem volume_closedBall_one_le_mul_volume_rescale_image_ambient [Nontrivial E]
    (hn : Module.finrank ℝ E = 3) (hθ : 0 < θ) {R : ℝ} (hR : 1 ≤ R) (T₀ : Tube θ E) :
    volume (closedBall (0 : E) 1)
      ≤ ENNReal.ofReal ((4 * R) ^ 6) * volume (T₀.rescaleMap R '' T₀.carrier) := by
  set c : NNReal := le_volume.c 3
  have hRpos : (0 : ℝ) < R := by linarith
  have h4Rpos : (0 : ℝ) < 4 * R := by positivity
  have h4Rne : (4 : ℝ) * R ≠ 0 := ne_of_gt h4Rpos
  have hcpos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast (le_volume.c_pos 3)
  -- Step 1: `(C : ℝ) ≤ (4R)^3 * (c : ℝ)`.
  have hreal : (volume_le.C 3 : ℝ) ≤ (4 * R) ^ 3 * (c : ℝ) := by
    have hC12 : (volume_le.C 3 : ℝ) ≤ 12 * (c : ℝ) := by
      exact (div_le_iff₀ hcpos).mp volume_ratio_three_le_twelve
    have h12 : (12 : ℝ) ≤ (4 * R) ^ 3 := by
      have h4 : (4 : ℝ) ≤ 4 * R := by nlinarith
      have h43 : (4 : ℝ) ^ 3 ≤ (4 * R) ^ 3 := pow_le_pow_left₀ (by norm_num) h4 3
      exact le_trans (by norm_num : (12 : ℝ) ≤ (4 : ℝ) ^ 3) h43
    exact le_trans hC12 (mul_le_mul_of_nonneg_right h12 (le_of_lt hcpos))
  -- Step 5: lift `hreal` through `ENNReal.ofReal`.
  have hre : (volume_le.C 3 : ENNReal) ≤ ENNReal.ofReal ((4 * R) ^ 3) * (c : ENNReal) := by
    have hposc : 0 ≤ (c : ℝ) := NNReal.coe_nonneg _
    calc
      (volume_le.C 3 : ENNReal) = ENNReal.ofReal (volume_le.C 3 : ℝ) := by
          rw [ENNReal.ofReal_coe_nnreal]
      _ ≤ ENNReal.ofReal ((4 * R) ^ 3 * (c : ℝ)) := by
          exact ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal ((4 * R) ^ 3) * (c : ENNReal) := by
          rw [ENNReal.ofReal_mul' hposc]
          rw [ENNReal.ofReal_coe_nnreal]
  -- Step 4: the `(4R)^6 · (4R)⁻³` factors collapse to `(4R)^3 · c`.
  have hstep4 : ENNReal.ofReal ((4 * R) ^ 6) * (ENNReal.ofReal ((4 * R)⁻¹ ^ 3) * (c : ENNReal))
      = ENNReal.ofReal ((4 * R) ^ 3) * (c : ENNReal) := by
    have ha : 0 ≤ (4 * R)⁻¹ ^ 3 := pow_nonneg (inv_nonneg.mpr h4Rpos.le) _
    have hcancel : (4 * R) ^ 6 * (4 * R)⁻¹ ^ 3 = (4 * R) ^ 3 := by
      rw [show (4 * R : ℝ) ^ 6 = (4 * R) ^ 3 * (4 * R) ^ 3 by exact (pow_add (4 * R) 3 3)]
      rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ h4Rne, one_pow, mul_one]
    calc
      ENNReal.ofReal ((4 * R) ^ 6) * (ENNReal.ofReal ((4 * R)⁻¹ ^ 3) * (c : ENNReal))
          = ENNReal.ofReal ((4 * R) ^ 6) * ENNReal.ofReal ((4 * R)⁻¹ ^ 3) * (c : ENNReal) := by
              ac_rfl
      _ = ENNReal.ofReal ((4 * R) ^ 6 * (4 * R)⁻¹ ^ 3) * (c : ENNReal) := by
              rw [← ENNReal.ofReal_mul' ha]
      _ = ENNReal.ofReal ((4 * R) ^ 3) * (c : ENNReal) := by rw [hcancel]
  -- Step 2: `c · θ² ≤ |T₀|`.
  have hle : (c : ENNReal) * (θ : ENNReal) ^ 2 ≤ volume T₀.carrier := by
    have h := Tube.le_volume T₀
    rw [hn] at h
    simpa [c] using h
  -- Step 3: `c ≤ θ⁻² · |T₀|`.
  have hθe0 : (θ : ENNReal) ≠ 0 := by exact_mod_cast (ne_of_gt hθ)
  have hθetop : (θ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hinv : (θ : ENNReal)⁻¹ * (θ : ENNReal) = 1 := ENNReal.inv_mul_cancel hθe0 hθetop
  have hθc : (c : ENNReal) ≤ (θ : ENNReal)⁻¹ ^ 2 * volume T₀.carrier := by
    have hθcancel : (θ : ENNReal)⁻¹ ^ 2 * ((c : ENNReal) * (θ : ENNReal) ^ 2) = (c : ENNReal) := by
      calc
        (θ : ENNReal)⁻¹ ^ 2 * ((c : ENNReal) * (θ : ENNReal) ^ 2)
            = (c : ENNReal) * ((θ : ENNReal)⁻¹ ^ 2 * (θ : ENNReal) ^ 2) := by ring
        _ = (c : ENNReal) * ((θ : ENNReal)⁻¹ * (θ : ENNReal)) ^ 2 := by rw [← mul_pow]
        _ = (c : ENNReal) * 1 := by rw [hinv]; norm_num
        _ = (c : ENNReal) := by simp
    calc
      (c : ENNReal) = (θ : ENNReal)⁻¹ ^ 2 * ((c : ENNReal) * (θ : ENNReal) ^ 2) := hθcancel.symm
      _ ≤ (θ : ENNReal)⁻¹ ^ 2 * volume T₀.carrier := by
          exact mul_le_mul_of_nonneg_left hle (by positivity)
  calc
    volume (closedBall (0 : E) 1) ≤ (volume_le.C 3 : ENNReal) := by
        simpa [hn] using (volume_closedBall_one_le (E := E))
    _ ≤ ENNReal.ofReal ((4 * R) ^ 3) * (c : ENNReal) := hre
    _ = ENNReal.ofReal ((4 * R) ^ 6) * (ENNReal.ofReal ((4 * R)⁻¹ ^ 3) * (c : ENNReal)) := hstep4.symm
    _ ≤ ENNReal.ofReal ((4 * R) ^ 6) * volume (T₀.rescaleMap R '' T₀.carrier) := by
        have hinner : ENNReal.ofReal ((4 * R)⁻¹ ^ 3) * (c : ENNReal)
            ≤ volume (T₀.rescaleMap R '' T₀.carrier) := by
          calc
            ENNReal.ofReal ((4 * R)⁻¹ ^ 3) * (c : ENNReal)
                ≤ ENNReal.ofReal ((4 * R)⁻¹ ^ 3) * ((θ : ENNReal)⁻¹ ^ 2 * volume T₀.carrier) := by
                    exact mul_le_mul_of_nonneg_left hθc (by positivity)
            _ = volume (T₀.rescaleMap R '' T₀.carrier) := by
                    have hvol := Tube.volume_image_rescaleMap (E := E) hθ hRpos T₀ T₀.carrier
                    rw [hn] at hvol
                    simpa using hvol.symm
        exact mul_le_mul_of_nonneg_left hinner (by positivity)

/-- **The outer tube of a rescaled tube** (blueprint `lem:coreOuterTube`).

In the rescaling situation, with the extra hypothesis `ρ ≤ 4 σ`, the distortion package
`Tube.IsNormalizationDistortion T₀ T` and `Φ_{T₀}(T) ⊆ B̄(T₀.x, R)`, the centred extension
`V = ext_σ[Ψ(T.x), Ψ(T.y)]` of the image core satisfies

```
W = Ψ(T) ⊆ V ⊆ B̄(0, 1),      |V| ≤ (4 R) ^ 6 |W|      (n = 3).
```

*Thickness*: `IsNormalizationDistortion.image_subset_cthickening` and
`Tube.rescaleMap_image_subset_cthickening` put `W` in the closed `(C_N ρ / (4 R))`-
neighbourhood of `[Ψ(T.x), Ψ(T.y)]`, and `C_N ρ / (4 R) ≤ ρ / 4 ≤ σ` by `C_N ≤ R` and
`hρσ`; `Tube.cthickening_subset_centredExtension` then gives `W ⊆ V`, its hypothesis
`dist (Ψ T.x) (Ψ T.y) ≤ 1` coming from `IsNormalizationDistortion.dist_le_C`.
*Position*: `hball` puts `Ψ(T.x), Ψ(T.y)` in `B̄(0, 1/4)`, and `σ ≤ 1/4` then gives
`V ⊆ B̄(0, 1)` by `Tube.centredExtension_subset_closedBall` at `z = 0 = Ψ(T₀.x)`.
*Volume*: `Tube.volume_centredExtension_le_mul_volume_rescale_image` together with
`Tube.volume_ratio_three_le_twelve` and `4 R ≥ 4 C_N`. -/
theorem rescale_outer_tube [Nontrivial E] {R : ℝ}
    (hsit : IsRescalingSituation θ τ σ R 3) (hn : Module.finrank ℝ E = 3) (hR : 0 < R)
    (hρσ : (τ : ℝ) / (θ : ℝ) ≤ 4 * (σ : ℝ))
    (T₀ : Tube θ E) (T : Tube τ E)
    (hdist : IsNormalizationDistortion T₀ T)
    (hball : T₀.normalization '' T.carrier ⊆ closedBall T₀.x R)
    (hxy : T₀.rescaleMap R T.x ≠ T₀.rescaleMap R T.y) :
    T₀.rescaleMap R '' T.carrier ⊆ (centredExtension σ hxy).carrier ∧
      (centredExtension σ hxy).carrier ⊆ closedBall (0 : E) 1 ∧
      volume (centredExtension σ hxy).carrier
        ≤ ENNReal.ofReal ((4 * R) ^ 6) * volume (T₀.rescaleMap R '' T.carrier) := by
  let ρ : ℝ := (τ : ℝ) / (θ : ℝ)
  let C0 : ℝ := (normalization.C (Module.finrank ℝ E) : ℝ)
  have hθpos : (0 : ℝ) < (θ : ℝ) := by exact_mod_cast hsit.pos_ambient
  have hρ_nonneg : 0 ≤ ρ := by
    dsimp [ρ]
    exact div_nonneg (by positivity) (le_of_lt hθpos)
  have h4Rpos : (0 : ℝ) < 4 * R := by positivity
  have h4R0 : (4 : ℝ) * R ≠ 0 := ne_of_gt h4Rpos
  have hC0_nonneg : 0 ≤ C0 := by
    dsimp [C0]
    positivity
  have hC0_le_R : C0 ≤ R := by
    dsimp [C0]
    simpa [hn] using hsit.normalizationConst_le_radius
  have hRdiv : R / (4 * R) = (1 : ℝ) / 4 := by
    field_simp [h4R0, (by norm_num : (4 : ℝ) ≠ 0)]
  -- (1) Thickness: `Ψ(T) ⊆ V`.
  have hth0 : T₀.rescaleMap R '' T.carrier ⊆
      cthickening (C0 * ρ / (4 * R)) (segment ℝ (T₀.rescaleMap R T.x) (T₀.rescaleMap R T.y)) := by
    exact rescaleMap_image_subset_cthickening T₀ hR (r := C0 * ρ)
      (A := T.carrier) (p := T.x) (q := T.y)
      (mul_nonneg hC0_nonneg hρ_nonneg) hdist.image_subset_cthickening
  have hrad : C0 * ρ / (4 * R) ≤ (σ : ℝ) := by
    have h1 : C0 * ρ ≤ R * ρ := mul_le_mul_of_nonneg_right hC0_le_R hρ_nonneg
    have h2 : C0 * ρ / (4 * R) ≤ (R * ρ) / (4 * R) := by
      exact div_le_div_of_nonneg_right h1 (le_of_lt h4Rpos)
    have h3 : (R * ρ) / (4 * R) = ρ / 4 := by
      field_simp [h4R0, (by norm_num : (4 : ℝ) ≠ 0)]
    have h4 : ρ / 4 ≤ (σ : ℝ) := by
      have : ρ ≤ 4 * (σ : ℝ) := by simpa [ρ] using hρσ
      linarith
    calc
      C0 * ρ / (4 * R) ≤ (R * ρ) / (4 * R) := h2
      _ = ρ / 4 := h3
      _ ≤ (σ : ℝ) := h4
  have hth1 : T₀.rescaleMap R '' T.carrier ⊆
      cthickening (σ : ℝ) (segment ℝ (T₀.rescaleMap R T.x) (T₀.rescaleMap R T.y)) := by
    exact hth0.trans (Metric.cthickening_mono hrad (segment ℝ (T₀.rescaleMap R T.x) (T₀.rescaleMap R T.y)))
  have hlen : dist (T₀.rescaleMap R T.x) (T₀.rescaleMap R T.y) ≤ 1 := by
    calc
      dist (T₀.rescaleMap R T.x) (T₀.rescaleMap R T.y)
          = dist (T₀.normalization T.x) (T₀.normalization T.y) / (4 * R) := by
            simpa [ρ, C0] using dist_rescaleMap T₀ hR T.x T.y
      _ ≤ C0 / (4 * R) := div_le_div_of_nonneg_right hdist.dist_le_C (le_of_lt h4Rpos)
      _ ≤ R / (4 * R) := div_le_div_of_nonneg_right hC0_le_R (le_of_lt h4Rpos)
      _ = 1 / 4 := hRdiv
      _ ≤ 1 := by norm_num
  have hth2 : T₀.rescaleMap R '' T.carrier ⊆ (centredExtension σ hxy).carrier := by
    exact hth1.trans (cthickening_subset_centredExtension hxy hlen)
  -- (2) Position: `V ⊆ B̄(0,1)`.
  have hpx : dist (T₀.normalization T.x) T₀.x ≤ R := by
    have hmem : T₀.normalization T.x ∈ T₀.normalization '' T.carrier := ⟨T.x, x_mem_carrier T, rfl⟩
    exact Metric.mem_closedBall.mp (hball hmem)
  have hpy : dist (T₀.normalization T.y) T₀.x ≤ R := by
    have hmem : T₀.normalization T.y ∈ T₀.normalization '' T.carrier := ⟨T.y, y_mem_carrier T, rfl⟩
    exact Metric.mem_closedBall.mp (hball hmem)
  have hpx0 : dist (T₀.rescaleMap R T.x) (0 : E) ≤ 1 / 4 := by
    calc
      dist (T₀.rescaleMap R T.x) (0 : E)
          = dist (T₀.rescaleMap R T.x) (T₀.rescaleMap R T₀.x) := by rw [← rescaleMap_apply_x]
      _ = dist (T₀.normalization T.x) (T₀.normalization T₀.x) / (4 * R) := dist_rescaleMap T₀ hR T.x T₀.x
      _ = dist (T₀.normalization T.x) T₀.x / (4 * R) := by rw [normalization_apply_x]
      _ ≤ R / (4 * R) := div_le_div_of_nonneg_right hpx (le_of_lt h4Rpos)
      _ = 1 / 4 := hRdiv
  have hpy0 : dist (T₀.rescaleMap R T.y) (0 : E) ≤ 1 / 4 := by
    calc
      dist (T₀.rescaleMap R T.y) (0 : E)
          = dist (T₀.rescaleMap R T.y) (T₀.rescaleMap R T₀.x) := by rw [← rescaleMap_apply_x]
      _ = dist (T₀.normalization T.y) (T₀.normalization T₀.x) / (4 * R) := dist_rescaleMap T₀ hR T.y T₀.x
      _ = dist (T₀.normalization T.y) T₀.x / (4 * R) := by rw [normalization_apply_x]
      _ ≤ R / (4 * R) := div_le_div_of_nonneg_right hpy (le_of_lt h4Rpos)
      _ = 1 / 4 := hRdiv
  have hpos : (centredExtension σ hxy).carrier ⊆ closedBall (0 : E) 1 := by
    exact centredExtension_subset_closedBall hxy hpx0 hpy0 hsit.out_le_quarter
  -- (3) Volume: `|V| ≤ (4R)^6 |W|`.
  have hvol0 : volume (centredExtension σ hxy).carrier
      ≤ ENNReal.ofReal ((volume_le.C 3 : ℝ) / (le_volume.c 3 : ℝ) * (4 * R) ^ 3)
          * volume (T₀.rescaleMap R '' T.carrier) := by
    simpa [hn] using volume_centredExtension_le_mul_volume_rescale_image (n := 3) hsit hR T₀ T hxy
  have hC64R : (64 : ℝ) ≤ R := by
    have hC : (64 : ℝ) ≤ (normalization.C 3 : ℝ) := by norm_num [normalization.C]
    exact le_trans hC hsit.normalizationConst_le_radius
  have hbig : (256 : ℝ) ≤ 4 * R := by linarith
  have hpow256 : (256 : ℝ) ^ 3 ≤ (4 * R) ^ 3 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 256) hbig 3
  have h12 : (12 : ℝ) ≤ (4 * R) ^ 3 := by nlinarith
  have hcoef : (volume_le.C 3 : ℝ) / (le_volume.c 3 : ℝ) * (4 * R) ^ 3 ≤ (4 * R) ^ 6 := by
    have hvp12 : (volume_le.C 3 : ℝ) / (le_volume.c 3 : ℝ) ≤ 12 := volume_ratio_three_le_twelve
    calc
      (volume_le.C 3 : ℝ) / (le_volume.c 3 : ℝ) * (4 * R) ^ 3 ≤ 12 * (4 * R) ^ 3 := by gcongr
      _ ≤ (4 * R) ^ 3 * (4 * R) ^ 3 := by gcongr
      _ = (4 * R) ^ 6 := by ring
  have hvol : volume (centredExtension σ hxy).carrier
      ≤ ENNReal.ofReal ((4 * R) ^ 6) * volume (T₀.rescaleMap R '' T.carrier) := by
    exact hvol0.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hcoef) le_rfl)
  exact ⟨hth2, hpos, hvol⟩

end Rescaling

end Tube
