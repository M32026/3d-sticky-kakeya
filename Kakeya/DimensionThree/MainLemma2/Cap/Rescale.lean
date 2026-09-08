/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Cap.BroadNarrow
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineOuterTubes

/-!
# The cap rescaling of the Cap Lemma (band item A5)

This file is item **A5** of the Cap Lemma plan (, mathematics in
§2(c) "rescale"): the step that takes a *cap column* of `δ`-tubes — tubes whose directions all lie
within a fixed angular radius of a common direction `p`, and which all sit transversally close to
one line parallel to `p` — and produces from it an honest family of `σ`-tubes **inside the unit
ball**, at the coarser scale `σ = δ / (4 θ)`, transporting the three quantities the induction
reads: multiplicity, fullness and `Δ_max`.

Its consumers are A4 (the narrow mass accounting, which produces the cap columns) and A6 (the
induction, which consumes `Kakeya.CapRescale.exists_capRescaledFamily`).

## What was already in the tree, and what had to be new

The *transport* half is already there:
`Kakeya/DimensionThree/MainLemma2/Reduction/SpineOuterTubes.lean` defines
`Kakeya.ML2Reduction.outerFamily` and proves, for the spine rescaling,

| quantity | lemma | loss |
|---|---|---|
| `carrier ⊆ B₁` | `outerFamily_carrier_subset_closedBall` | none |
| `μ` | `outerFamily_multiplicity` | **none** (an equality) |
| `λ` | `outerFamily_le_fullness` | `outerLoss R = (4 R)^6` |
| `Δ_max` | `outerFamily_maxDensity_le` | `outerLoss R = (4 R)^6` |

Every one of those four is stated under the single hypothesis
`hsub : ∀ i ∈ s, (𝕋 i).carrier ⊆ T₀.carrier`, the containment of each tube in the ambient
reference tube.  **That hypothesis is unavailable in a cap column, and not by a constant.**  A
`Tube` (`Kakeya/Tube/Basic.lean`; it sits at the root namespace, **not** under `Kakeya.`) has a
core of length exactly `1` (`Tube.dist_eq_one`), so a unit-core `θ`-tube cannot contain a
unit-core `δ`-tube whose centre is displaced *along* its axis; and the tubes of a
cap column, all of which live in `B₁`, are displaced along the axis by up to `2`.  So the
containment cannot be arranged by enlarging `θ` either — it fails for a reason of length, not of
thickness.

What this file does is therefore **replace `hsub`, not weaken a constant**:

1. `Kakeya.CapRescale.IsCapDistortion` — the *two* fields of `Tube.IsNormalizationDistortion`
   that `Tube.rescale_outer_tube` actually reads.  Both are position-free.  That the two suffice
   is measured, not argued: `Kakeya.CapRescale.rescale_outer_tube_of_isCapDistortion` re-derives
   the tree's `Tube.rescale_outer_tube` from `Kakeya.CapRescale.capRescale_outer_tube` in one
   step, so the three remaining fields (`one_le_dist`, `exists_subsegment`,
   `image_ambient_subset_closedBall`) are inert in the kernel.  Those three are exactly the ones
   whose proofs need the containment.
2. `Kakeya.CapRescale.isCapDistortion_of_dirDist` — the two fields from the **cap condition
   alone**: `Kakeya.CapBroadNarrow.dirDist (T.direction) (T₀.direction) ≤ θ`.  The image core is
   then of length `≤ √2 ≤ 2 ≤ C_N(n)`, and the thin-image clause needs no hypothesis at all
   beyond `θ ≤ 1`.
3. `Kakeya.CapRescale.norm_perpTo_sub_x_le_of_column` — *column localisation*: a tube of the cap
   whose **midpoint** is transversally within `b θ` of the axis stays transversally within
   `(b + 3/2) θ` of it along its whole length.  This is 's "a tube of `𝕋_p`
   stays within transverse distance `3θ/2 + δ_k` of the line through its centre parallel to `p`",
   proved.  It is the only *positional* hypothesis the rescaling needs, and it is exactly what a
   column partition supplies.
4. `Kakeya.CapRescale.normalization_image_subset_closedBall_of_column` — the `hball` hypothesis of
   `Tube.rescale_outer_tube`, from (3) plus the standing `B₁` hypothesis.  The spine route gets
   this from the containment
   (`Kakeya.ML2Reduction.normalization_image_subset_closedBall_of_subset`); here it is
   `A + b + 3/2 ≤ R`, which at `A = 3`, `b = 2` reads `13/2 ≤ R` and is implied by
   `C_N(3) = 64 ≤ R`.

## The single map, and why there is no translation bookkeeping

 proposes a **per-tube** ambient tube `T₀(i)` (same midpoint as `T_i`,
direction `p`), obtained from `Tube.tube_carrier_subset_of_close`, and then repairs the resulting
mismatch of maps by a translation `v_i` and a `Tube.vadd`.  That route does work — the linear
parts agree, so the maps differ by a constant — but it is **unnecessary here and strictly worse**:
the transport of multiplicity, fullness and `Δ_max` requires *one* affine map for the whole
family, and re-anchoring per tube then costs a translation bookkeeping *plus* a fresh proof that
the translated outer tube still lies in `B₁` (`Tube.centredExtension_subset_closedBall` no longer
applies on the nose).  Using a *single* reference tube `Kakeya.CapRescale.capRefTube θ b hp`
at the column's base point, none of that arises: `Kakeya.CapRescale.capOuterTube_spec` already
delivers `(outerTube …).carrier ⊆ closedBall 0 1`.  So `Tube.tube_carrier_subset_of_close` and
`Tube.vadd` are **not used in this file**, and the reason is recorded here rather than left
implicit.

## The scale, and the constants

* `Kakeya.CapRescale.capScale θ δ = δ / (4 θ)` — the plan's `σ = δ_k/(4 θ')`.  At cap radius
  `θ = θ' = 4 θ_ang` this is `δ/(16 θ_ang)` (`Kakeya.CapRescale.capScale_of_angular`), i.e. the
  plan's `δ_k^{1-c}/16` at `θ_ang = δ_k^c`.  The extra hypothesis `δ/θ ≤ 4 σ` of the outer-tube
  lemma holds with **equality** at this scale (`Kakeya.CapRescale.capScale_ratio`), so the cap
  scale is the coarsest the lemma allows and nothing is thrown away.
* `Kakeya.CapRescale.capLoss = (4 R)^6` at `R = C_N(3) = 64` — the one absolute constant, the
  volume loss of replacing a rescaled body by an honest tube.
* The cap radius is `4 θ_ang`, **not** 's `3 θ_ang`; see  (the net of `Tube.sphere_sep_net` covers only within `2 θ_ang`) and  (at
  `3 θ_ang` the side condition `t + 2 θ ≤ r` reads `4 θ ≤ 3 θ`, false).  Here that correction is
  what makes the *reference thickness* equal the *cap radius*, so the `dir` clause of
  `Kakeya.CapRescale.IsCapColumn` is literally membership in
  `Kakeya.CapBroadNarrow.capFamily s 𝕋 p (4 θ_ang)`.
* `Kakeya.CapBroadNarrow.capPackingConst` (`C_P`) does **not** appear in this file.  It is the
  cap-*overlap* count and belongs to A4's fullness pigeonhole; it enters the composition only
  through the value of `l` that A4 hands to A6, never through the rescaling.  (Same finding as
   for the broad half.)

## Which hypothesis forces which loss

* **Multiplicity: no loss, and none is forced.**  `ShadedBody.multiplicity` reads only the shades
  and their union; the outer replacement changes neither and the affine map multiplies numerator
  and denominator by one Jacobian.  `Kakeya.CapRescale.capOuterFamily_multiplicity` accordingly
  does **not** take `1 ≤ R` and does not mention `capLoss` — a typed certificate that no factor is
  being carried as decoration.
* **Fullness: `capLoss` is forced by the volume clause alone.**  Fullness is `∑|Y_i| / ∑|T_i|`,
  antitone in the denominator, which the replacement enlarges;
  `Kakeya.CapRescale.fullness_loss_is_forced` is the `ℝ≥0∞` refutation of the factor-free
  statement.  The clause's own source is that `Kakeya.ML2Reduction.outerTube` has unit core while
  the rescaled core may be as short as `1/(4R)`
  (`Tube.volume_centredExtension_le_mul_volume_rescale_image`).
* **`Δ_max`: `capLoss` is forced by the volume clause; the containment clause is free.**  The
  containment shrinks the set of bodies inside a test body, which helps;
  `Kakeya.CapRescale.maxDensity_loss_is_forced` refutes the factor-free statement.

## Non-vacuity

`Kakeya.CapRescale.isCapColumn_nonvacuous` exhibits a concrete inhabitant of
`Kakeya.CapRescale.IsCapColumn` (the reference tube itself, shaded by `∅`), so the two
quantitative clauses are simultaneously satisfiable; and
`Kakeya.CapRescale.isCapColumn_capRefTube` is the producer a column partition calls.
-/

@[expose] public section

open MeasureTheory Metric Set Module
open scoped NNReal ENNReal

namespace Kakeya.CapRescale

open Kakeya.CapBroadNarrow Kakeya.ML2Reduction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*} {θ δ σ : NNReal}

/-! ## 1. The perpendicular part along the axis of a reference tube -/

/-- The component of `v` orthogonal to the axis of the reference tube `T₀`. -/
noncomputable def perpTo (T₀ : Tube θ E) (v : E) : E :=
  v - (inner ℝ T₀.direction v) • T₀.direction

omit [MeasurableSpace E] [BorelSpace E] in
theorem perpTo_def (T₀ : Tube θ E) (v : E) :
    perpTo T₀ v = v - (inner ℝ T₀.direction v) • T₀.direction := rfl

omit [MeasurableSpace E] [BorelSpace E] in
theorem perpTo_add (T₀ : Tube θ E) (v w : E) :
    perpTo T₀ (v + w) = perpTo T₀ v + perpTo T₀ w := by
  simp only [perpTo, inner_add_right]
  module

omit [MeasurableSpace E] [BorelSpace E] in
theorem perpTo_smul (T₀ : Tube θ E) (a : ℝ) (v : E) :
    perpTo T₀ (a • v) = a • perpTo T₀ v := by
  simp only [perpTo, inner_smul_right]
  module

omit [MeasurableSpace E] [BorelSpace E] in
theorem perpTo_sub (T₀ : Tube θ E) (v w : E) :
    perpTo T₀ (v - w) = perpTo T₀ v - perpTo T₀ w := by
  simp only [perpTo, inner_sub_right]
  module

omit [MeasurableSpace E] [BorelSpace E] in
@[simp]
theorem perpTo_neg (T₀ : Tube θ E) (v : E) : perpTo T₀ (-v) = -perpTo T₀ v := by
  simp only [perpTo, inner_neg_right]
  module

omit [MeasurableSpace E] [BorelSpace E] in
@[simp]
theorem perpTo_direction (T₀ : Tube θ E) : perpTo T₀ T₀.direction = 0 := by
  have he : (inner ℝ T₀.direction T₀.direction : ℝ) = 1 := by
    rw [real_inner_self_eq_norm_sq, T₀.norm_direction]; norm_num
  rw [perpTo, he, one_smul, sub_self]

theorem norm_perpTo_le (T₀ : Tube θ E) (v : E) : ‖perpTo T₀ v‖ ≤ ‖v‖ :=
  Tube.norm_perp_le T₀ v

omit [MeasurableSpace E] [BorelSpace E] in
theorem abs_inner_direction_le (T₀ : Tube θ E) (v : E) :
    |(inner ℝ T₀.direction v : ℝ)| ≤ ‖v‖ := by
  have h := abs_real_inner_le_norm T₀.direction v
  rwa [T₀.norm_direction, one_mul] at h

/-- **The sign-blind bound on the perpendicular part of a direction.**

`dirDist` is a minimum over the two signs, and `perpTo` kills `T₀.direction`, hence *both*
`±T₀.direction`.  So a `dirDist`-bound transfers to the perpendicular part with **no factor two**:
the sign ambiguity that costs `Kakeya.CapBroadNarrow.capPackingConst` its factor `2` in the cap
*count* costs nothing here. -/
theorem norm_perpTo_le_of_dirDist {ε : ℝ} (T₀ : Tube θ E) {u : E}
    (hu : dirDist u T₀.direction ≤ ε) : ‖perpTo T₀ u‖ ≤ ε := by
  rcases le_total ‖u - T₀.direction‖ ‖u + T₀.direction‖ with h | h
  · have hle : ‖u - T₀.direction‖ ≤ ε := by
      refine le_trans ?_ hu
      simp [dirDist, h]
    calc ‖perpTo T₀ u‖ = ‖perpTo T₀ (u - T₀.direction)‖ := by
          rw [perpTo_sub, perpTo_direction, sub_zero]
      _ ≤ ‖u - T₀.direction‖ := norm_perpTo_le T₀ _
      _ ≤ ε := hle
  · have hle : ‖u + T₀.direction‖ ≤ ε := by
      refine le_trans ?_ hu
      simp [dirDist, h]
    calc ‖perpTo T₀ u‖ = ‖perpTo T₀ (u + T₀.direction)‖ := by
          rw [perpTo_add, perpTo_direction, add_zero]
      _ ≤ ‖u + T₀.direction‖ := norm_perpTo_le T₀ _
      _ ≤ ε := hle

/-- `Tube.perp_norm_le_of_mem_carrier` in the `perpTo` vocabulary. -/
theorem norm_perpTo_le_of_mem_carrier (T₀ : Tube θ E) {z : E} (hz : z ∈ T₀.carrier) :
    ‖perpTo T₀ (z - T₀.x)‖ ≤ (θ : ℝ) :=
  Tube.perp_norm_le_of_mem_carrier T₀ hz

/-- The displacement formula for `Tube.normalization` in the `perpTo` vocabulary. -/
theorem normalization_sub_x (T₀ : Tube θ E) (z : E) :
    T₀.normalization z - T₀.x
      = (inner ℝ T₀.direction (z - T₀.x)) • T₀.direction + (θ : ℝ)⁻¹ • perpTo T₀ (z - T₀.x) := by
  have h := Tube.normalization_sub_apply T₀ z T₀.x
  rw [Tube.normalization_apply_x] at h
  simpa [perpTo] using h

/-- **The image of a point under `Φ_{T₀}` is controlled by its axial distance and its
transverse distance to the axis** — with no containment hypothesis whatsoever. -/
theorem norm_normalization_sub_x_le (T₀ : Tube θ E) (hθ : 0 < θ) (z : E) {A B : ℝ}
    (hax : ‖z - T₀.x‖ ≤ A) (htr : ‖perpTo T₀ (z - T₀.x)‖ ≤ B * (θ : ℝ)) :
    ‖T₀.normalization z - T₀.x‖ ≤ A + B := by
  have hθ0 : (0 : ℝ) < (θ : ℝ) := by exact_mod_cast hθ
  have hB : 0 ≤ B := by
    by_contra hneg
    have : B * (θ : ℝ) < 0 := mul_neg_of_neg_of_pos (not_le.mp hneg) hθ0
    exact absurd (le_trans (norm_nonneg _) htr) (not_le.mpr this)
  rw [normalization_sub_x T₀ z]
  refine le_trans (norm_add_le _ _) ?_
  have h1 : ‖(inner ℝ T₀.direction (z - T₀.x) : ℝ) • T₀.direction‖ ≤ A := by
    rw [norm_smul, Real.norm_eq_abs, T₀.norm_direction, mul_one]
    exact le_trans (abs_inner_direction_le T₀ _) hax
  have h2 : ‖((θ : ℝ)⁻¹) • perpTo T₀ (z - T₀.x)‖ ≤ B := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hθ0)]
    rw [inv_mul_le_iff₀ hθ0]
    calc ‖perpTo T₀ (z - T₀.x)‖ ≤ B * (θ : ℝ) := htr
      _ = (θ : ℝ) * B := by ring
  linarith

/-! ## 2. The two distortion facts that the outer-tube lemma actually reads -/

/-- **The distortion data `Tube.rescale_outer_tube` consumes.**

`Tube.IsNormalizationDistortion` (`Kakeya/Tube/Rescale.lean`) has five fields, and is available
only under the containment `T.carrier ⊆ T₀.carrier` (`Tube.normalization_distortion`).  Of those
five, `Tube.rescale_outer_tube` reads exactly **two**: the upper bound on the image core length
and the thin-image clause.  Both are *position-free*, so both survive the failure of the
containment in a cap column, and that is what makes the cap rescaling possible at all.

That the two fields suffice is not an argument but a compiled fact:
`Kakeya.CapRescale.rescale_outer_tube_of_isCapDistortion` re-derives `Tube.rescale_outer_tube`
from `Kakeya.CapRescale.capRescale_outer_tube` and
`Kakeya.CapRescale.isCapDistortion_of_isNormalizationDistortion` in one step. -/
structure IsCapDistortion (T₀ : Tube θ E) (T : Tube δ E) : Prop where
  /-- (i, upper half of `Tube.IsNormalizationDistortion.dist_le_C`) The image core is short. -/
  dist_le_C : dist (T₀.normalization T.x) (T₀.normalization T.y)
    ≤ (Tube.normalization.C (finrank ℝ E) : ℝ)
  /-- (ii) `Φ_{T₀}(T)` is thin: it lies in the `C (δ/θ)`-neighbourhood of the image core. -/
  image_subset_cthickening : T₀.normalization '' T.carrier ⊆
    cthickening ((Tube.normalization.C (finrank ℝ E) : ℝ) * ((δ : ℝ) / (θ : ℝ)))
      (segment ℝ (T₀.normalization T.x) (T₀.normalization T.y))

omit [MeasurableSpace E] [BorelSpace E] in
/-- The tree's five-field package is stronger than the two-field one. -/
theorem isCapDistortion_of_isNormalizationDistortion {T₀ : Tube θ E} {T : Tube δ E}
    (h : Tube.IsNormalizationDistortion T₀ T) : IsCapDistortion T₀ T :=
  ⟨h.dist_le_C, h.image_subset_cthickening⟩

theorem two_le_normalizationConst (n : ℕ) : (2 : ℝ) ≤ (Tube.normalization.C n : ℝ) := by
  have h : (2 : ℝ) ^ 1 ≤ (2 : ℝ) ^ (n + 3) := by
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  simpa [Tube.normalization.C] using h

theorem one_le_normalizationConst' (n : ℕ) : (1 : ℝ) ≤ (Tube.normalization.C n : ℝ) :=
  le_trans (by norm_num) (two_le_normalizationConst n)

/-- **The image core of a nearly axial tube is short.**

The only input is that the direction of `T` is within `θ` of the axis of `T₀` in the sign-blind
angular distance `Kakeya.CapBroadNarrow.dirDist` — no containment, no position hypothesis.  The
bound is `√2 ≤ 2`, stated as `2`; the mechanism is
`Tube.norm_sq_normalization_sub`: the axial component is untouched (`≤ 1`) and the transverse one
is multiplied by `θ⁻¹`, but is itself `≤ θ`. -/
theorem dist_normalization_core_le_of_dirDist (hθ : 0 < θ) (T₀ : Tube θ E) (T : Tube δ E)
    (hdir : dirDist T.direction T₀.direction ≤ (θ : ℝ)) :
    dist (T₀.normalization T.x) (T₀.normalization T.y) ≤ 2 := by
  have hθ0 : (0 : ℝ) < (θ : ℝ) := by exact_mod_cast hθ
  have hxy : T.x - T.y = -T.direction := by simp [Tube.direction]
  have hperp : ‖perpTo T₀ T.direction‖ ≤ (θ : ℝ) := norm_perpTo_le_of_dirDist T₀ hdir
  have hinner : |(inner ℝ T₀.direction T.direction : ℝ)| ≤ 1 := by
    have h := abs_inner_direction_le T₀ T.direction
    rwa [T.norm_direction] at h
  have e1 : (inner ℝ T₀.direction (-T.direction) : ℝ)
      = -(inner ℝ T₀.direction T.direction : ℝ) := by rw [inner_neg_right]
  have e2 : (-T.direction) - (-(inner ℝ T₀.direction T.direction : ℝ)) • T₀.direction
      = -(perpTo T₀ T.direction) := by rw [perpTo]; module
  have key := Tube.norm_sq_normalization_sub T₀ T.x T.y
  rw [hxy, e1, e2, norm_neg, neg_sq] at key
  have h1 : (inner ℝ T₀.direction T.direction : ℝ) ^ 2 ≤ 1 := by
    nlinarith [abs_nonneg (inner ℝ T₀.direction T.direction : ℝ),
      sq_abs (inner ℝ T₀.direction T.direction : ℝ), hinner]
  have h2 : ((θ : ℝ)⁻¹) ^ 2 * ‖perpTo T₀ T.direction‖ ^ 2 ≤ 1 := by
    have hle : ‖perpTo T₀ T.direction‖ ^ 2 ≤ (θ : ℝ) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hperp 2
    have hstep : ((θ : ℝ)⁻¹) ^ 2 * ‖perpTo T₀ T.direction‖ ^ 2
        ≤ ((θ : ℝ)⁻¹) ^ 2 * (θ : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hle (by positivity)
    calc ((θ : ℝ)⁻¹) ^ 2 * ‖perpTo T₀ T.direction‖ ^ 2
          ≤ ((θ : ℝ)⁻¹) ^ 2 * (θ : ℝ) ^ 2 := hstep
      _ = 1 := by field_simp
  have hsq2 : dist (T₀.normalization T.x) (T₀.normalization T.y) ^ 2 ≤ 2 := by
    rw [dist_eq_norm, key]
    nlinarith [h1, h2]
  nlinarith [dist_nonneg (x := T₀.normalization T.x) (y := T₀.normalization T.y), hsq2]

/-- **The two-field distortion package from the cap hypothesis alone.** -/
theorem isCapDistortion_of_dirDist (hθ : 0 < θ) (hθ1 : θ ≤ 1) (T₀ : Tube θ E) (T : Tube δ E)
    (hdir : dirDist T.direction T₀.direction ≤ (θ : ℝ)) :
    IsCapDistortion T₀ T where
  dist_le_C := le_trans (dist_normalization_core_le_of_dirDist hθ T₀ T hdir)
    (two_le_normalizationConst _)
  image_subset_cthickening := Tube.normalization_image_subset_cthickening hθ hθ1 T₀ T

/-! ## 3. Column localisation: the position hypothesis that replaces the containment -/

/-- **Column localisation.**  A tube whose direction is within `θ` of the axis of `T₀` and whose
*midpoint* is within transverse distance `b θ` of that axis stays within transverse distance
`(b + 3/2) θ` of it, everywhere along its length.

This is 's "a tube of `𝕋_p` stays within transverse distance
`3θ/2 + δ_k` of the line through its centre parallel to `p`", proved.  It is the *only* position
hypothesis the cap rescaling needs, and it is exactly what a column partition supplies. -/
theorem norm_perpTo_sub_x_le_of_column (T₀ : Tube θ E) (T : Tube δ E)
    (hdir : dirDist T.direction T₀.direction ≤ (θ : ℝ)) (hδθ : (δ : ℝ) ≤ (θ : ℝ))
    {b : ℝ} (hmid : ‖perpTo T₀ (T.midpoint - T₀.x)‖ ≤ b * (θ : ℝ))
    {z : E} (hz : z ∈ T.carrier) :
    ‖perpTo T₀ (z - T₀.x)‖ ≤ (b + 3 / 2) * (θ : ℝ) := by
  have hθnn : (0 : ℝ) ≤ (θ : ℝ) := θ.coe_nonneg
  have hperpdir : ‖perpTo T₀ T.direction‖ ≤ (θ : ℝ) := norm_perpTo_le_of_dirDist T₀ hdir
  rw [T.carrier_eq, Set.mem_iUnion₂] at hz
  obtain ⟨c, hc, hzc⟩ := hz
  rw [Metric.mem_closedBall] at hzc
  rw [segment_eq_image_lineMap] at hc
  obtain ⟨t, ht, hceq⟩ := hc
  have hc_eq : c = T.x + t • T.direction := by
    rw [← hceq]
    simp [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, Tube.direction]
    abel
  have hsplit : z - T₀.x = (z - c) + ((t - 1 / 2) • T.direction + (T.midpoint - T₀.x)) := by
    rw [hc_eq]
    simp only [Tube.midpoint, Tube.direction]
    module
  have h1 : ‖perpTo T₀ (z - c)‖ ≤ (θ : ℝ) := by
    refine le_trans (norm_perpTo_le T₀ _) ?_
    rw [← dist_eq_norm]
    exact le_trans hzc hδθ
  have h2 : ‖perpTo T₀ ((t - 1 / 2) • T.direction)‖ ≤ (1 / 2) * (θ : ℝ) := by
    rw [perpTo_smul, norm_smul, Real.norm_eq_abs]
    have habs : |t - 1 / 2| ≤ 1 / 2 := by
      rw [abs_le]; constructor <;> [linarith [ht.1]; linarith [ht.2]]
    exact mul_le_mul habs hperpdir (norm_nonneg _) (by norm_num)
  rw [hsplit, perpTo_add, perpTo_add]
  calc ‖perpTo T₀ (z - c) + (perpTo T₀ ((t - 1 / 2) • T.direction)
          + perpTo T₀ (T.midpoint - T₀.x))‖
        ≤ ‖perpTo T₀ (z - c)‖
          + (‖perpTo T₀ ((t - 1 / 2) • T.direction)‖ + ‖perpTo T₀ (T.midpoint - T₀.x)‖) := by
        exact le_trans (norm_add_le _ _) (by gcongr; exact norm_add_le _ _)
    _ ≤ (θ : ℝ) + ((1 / 2) * (θ : ℝ) + b * (θ : ℝ)) := by gcongr
    _ = (b + 3 / 2) * (θ : ℝ) := by ring

omit [MeasurableSpace E] [BorelSpace E] in
/-- The axial bound is free from the standing `B₁` hypothesis of the Cap Lemma. -/
theorem norm_sub_x_le_of_subset_closedBall {T₀ : Tube θ E} {S : Set E} {A₀ : ℝ}
    (hS : S ⊆ closedBall (0 : E) 1) (hx : ‖T₀.x‖ ≤ A₀) {z : E} (hz : z ∈ S) :
    ‖z - T₀.x‖ ≤ 1 + A₀ := by
  have h1 : ‖z‖ ≤ 1 := by simpa using hS hz
  calc ‖z - T₀.x‖ ≤ ‖z‖ + ‖T₀.x‖ := norm_sub_le _ _
    _ ≤ 1 + A₀ := by linarith

/-- **The `hball` hypothesis of `Tube.rescale_outer_tube`, from cap and column data.**

`Tube.rescale_outer_tube` needs `Φ_{T₀}(T) ⊆ B̄(T₀.x, R)`, which the spine route obtains from the
containment `T ⊆ T₀` (`Kakeya.ML2Reduction.normalization_image_subset_closedBall_of_subset`).  In
a cap column the containment fails, and this lemma replaces it: the axial displacement is bounded
by `A` and the transverse one by `(b + 3/2) θ`, so the image is within `A + b + 3/2` of `T₀.x`. -/
theorem normalization_image_subset_closedBall_of_column (hθ : 0 < θ) (T₀ : Tube θ E)
    (T : Tube δ E) (hdir : dirDist T.direction T₀.direction ≤ (θ : ℝ)) (hδθ : (δ : ℝ) ≤ (θ : ℝ))
    {b A R : ℝ} (hmid : ‖perpTo T₀ (T.midpoint - T₀.x)‖ ≤ b * (θ : ℝ))
    (hax : ∀ z ∈ T.carrier, ‖z - T₀.x‖ ≤ A) (hR : A + (b + 3 / 2) ≤ R) :
    T₀.normalization '' T.carrier ⊆ closedBall T₀.x R := by
  rintro q ⟨z, hz, rfl⟩
  rw [Metric.mem_closedBall, dist_eq_norm]
  refine le_trans ?_ hR
  exact norm_normalization_sub_x_le T₀ hθ z (hax z hz)
    (norm_perpTo_sub_x_le_of_column T₀ T hdir hδθ hmid hz)

/-! ## 4. The outer tube of a cap tube -/

variable [Nontrivial E]

/-- **`Tube.rescale_outer_tube` under the two-field distortion package.**

Identical conclusion, strictly weaker hypothesis: `Tube.IsNormalizationDistortion` is replaced by
`Kakeya.CapRescale.IsCapDistortion`.  The proof is the tree's, with the three unused fields of the
package never mentioned; the volume clause needs no distortion data at all
(`Tube.volume_centredExtension_le_mul_volume_rescale_image` takes only the rescaling situation). -/
theorem capRescale_outer_tube {R : ℝ} (hsit : Tube.IsRescalingSituation θ δ σ R 3)
    (hn : finrank ℝ E = 3) (hR : 0 < R) (hδσ : (δ : ℝ) / (θ : ℝ) ≤ 4 * (σ : ℝ))
    (T₀ : Tube θ E) (T : Tube δ E) (hcap : IsCapDistortion T₀ T)
    (hball : T₀.normalization '' T.carrier ⊆ closedBall T₀.x R)
    (hxy : T₀.rescaleMap R T.x ≠ T₀.rescaleMap R T.y) :
    T₀.rescaleMap R '' T.carrier ⊆ (Tube.centredExtension σ hxy).carrier ∧
      (Tube.centredExtension σ hxy).carrier ⊆ closedBall (0 : E) 1 ∧
      volume (Tube.centredExtension σ hxy).carrier
        ≤ ENNReal.ofReal ((4 * R) ^ 6) * volume (T₀.rescaleMap R '' T.carrier) := by
  have hθpos : (0 : ℝ) < (θ : ℝ) := by exact_mod_cast hsit.pos_ambient
  have hρ_nonneg : (0 : ℝ) ≤ (δ : ℝ) / (θ : ℝ) := div_nonneg (by positivity) hθpos.le
  have h4Rpos : (0 : ℝ) < 4 * R := by positivity
  have h4R0 : (4 : ℝ) * R ≠ 0 := ne_of_gt h4Rpos
  have hC0_nonneg : (0 : ℝ) ≤ (Tube.normalization.C (finrank ℝ E) : ℝ) := by positivity
  have hC0_le_R : (Tube.normalization.C (finrank ℝ E) : ℝ) ≤ R := by
    simpa [hn] using hsit.normalizationConst_le_radius
  have hRdiv : R / (4 * R) = (1 : ℝ) / 4 := by
    field_simp [h4R0, (by norm_num : (4 : ℝ) ≠ 0)]
  -- (1) Thickness.
  have hth0 : T₀.rescaleMap R '' T.carrier ⊆
      cthickening ((Tube.normalization.C (finrank ℝ E) : ℝ) * ((δ : ℝ) / (θ : ℝ)) / (4 * R))
        (segment ℝ (T₀.rescaleMap R T.x) (T₀.rescaleMap R T.y)) :=
    Tube.rescaleMap_image_subset_cthickening T₀ hR
      (mul_nonneg hC0_nonneg hρ_nonneg) hcap.image_subset_cthickening
  have hrad : (Tube.normalization.C (finrank ℝ E) : ℝ) * ((δ : ℝ) / (θ : ℝ)) / (4 * R)
      ≤ (σ : ℝ) := by
    have h1 : (Tube.normalization.C (finrank ℝ E) : ℝ) * ((δ : ℝ) / (θ : ℝ))
        ≤ R * ((δ : ℝ) / (θ : ℝ)) := mul_le_mul_of_nonneg_right hC0_le_R hρ_nonneg
    have h2 : (Tube.normalization.C (finrank ℝ E) : ℝ) * ((δ : ℝ) / (θ : ℝ)) / (4 * R)
        ≤ R * ((δ : ℝ) / (θ : ℝ)) / (4 * R) := div_le_div_of_nonneg_right h1 h4Rpos.le
    have h3 : R * ((δ : ℝ) / (θ : ℝ)) / (4 * R) = ((δ : ℝ) / (θ : ℝ)) / 4 := by
      field_simp [h4R0, (by norm_num : (4 : ℝ) ≠ 0)]
    have h4 : ((δ : ℝ) / (θ : ℝ)) / 4 ≤ (σ : ℝ) := by linarith [hδσ]
    calc (Tube.normalization.C (finrank ℝ E) : ℝ) * ((δ : ℝ) / (θ : ℝ)) / (4 * R)
          ≤ R * ((δ : ℝ) / (θ : ℝ)) / (4 * R) := h2
      _ = ((δ : ℝ) / (θ : ℝ)) / 4 := h3
      _ ≤ (σ : ℝ) := h4
  have hth1 : T₀.rescaleMap R '' T.carrier ⊆
      cthickening (σ : ℝ) (segment ℝ (T₀.rescaleMap R T.x) (T₀.rescaleMap R T.y)) :=
    hth0.trans (Metric.cthickening_mono hrad _)
  have hlen : dist (T₀.rescaleMap R T.x) (T₀.rescaleMap R T.y) ≤ 1 := by
    calc dist (T₀.rescaleMap R T.x) (T₀.rescaleMap R T.y)
          = dist (T₀.normalization T.x) (T₀.normalization T.y) / (4 * R) :=
            Tube.dist_rescaleMap T₀ hR T.x T.y
      _ ≤ (Tube.normalization.C (finrank ℝ E) : ℝ) / (4 * R) :=
            div_le_div_of_nonneg_right hcap.dist_le_C h4Rpos.le
      _ ≤ R / (4 * R) := div_le_div_of_nonneg_right hC0_le_R h4Rpos.le
      _ = 1 / 4 := hRdiv
      _ ≤ 1 := by norm_num
  have hth2 : T₀.rescaleMap R '' T.carrier ⊆ (Tube.centredExtension σ hxy).carrier :=
    hth1.trans (Tube.cthickening_subset_centredExtension hxy hlen)
  -- (2) Position.
  have hpx : dist (T₀.normalization T.x) T₀.x ≤ R :=
    Metric.mem_closedBall.mp (hball ⟨T.x, Tube.x_mem_carrier T, rfl⟩)
  have hpy : dist (T₀.normalization T.y) T₀.x ≤ R :=
    Metric.mem_closedBall.mp (hball ⟨T.y, Tube.y_mem_carrier T, rfl⟩)
  have hpx0 : dist (T₀.rescaleMap R T.x) (0 : E) ≤ 1 / 4 := by
    calc dist (T₀.rescaleMap R T.x) (0 : E)
          = dist (T₀.rescaleMap R T.x) (T₀.rescaleMap R T₀.x) := by rw [← Tube.rescaleMap_apply_x]
      _ = dist (T₀.normalization T.x) (T₀.normalization T₀.x) / (4 * R) :=
            Tube.dist_rescaleMap T₀ hR T.x T₀.x
      _ = dist (T₀.normalization T.x) T₀.x / (4 * R) := by rw [Tube.normalization_apply_x]
      _ ≤ R / (4 * R) := div_le_div_of_nonneg_right hpx h4Rpos.le
      _ = 1 / 4 := hRdiv
  have hpy0 : dist (T₀.rescaleMap R T.y) (0 : E) ≤ 1 / 4 := by
    calc dist (T₀.rescaleMap R T.y) (0 : E)
          = dist (T₀.rescaleMap R T.y) (T₀.rescaleMap R T₀.x) := by rw [← Tube.rescaleMap_apply_x]
      _ = dist (T₀.normalization T.y) (T₀.normalization T₀.x) / (4 * R) :=
            Tube.dist_rescaleMap T₀ hR T.y T₀.x
      _ = dist (T₀.normalization T.y) T₀.x / (4 * R) := by rw [Tube.normalization_apply_x]
      _ ≤ R / (4 * R) := div_le_div_of_nonneg_right hpy h4Rpos.le
      _ = 1 / 4 := hRdiv
  have hpos : (Tube.centredExtension σ hxy).carrier ⊆ closedBall (0 : E) 1 :=
    Tube.centredExtension_subset_closedBall hxy hpx0 hpy0 hsit.out_le_quarter
  -- (3) Volume: no distortion data at all.
  have hvol0 : volume (Tube.centredExtension σ hxy).carrier
      ≤ ENNReal.ofReal ((Tube.volume_le.C 3 : ℝ) / (Tube.le_volume.c 3 : ℝ) * (4 * R) ^ 3)
          * volume (T₀.rescaleMap R '' T.carrier) := by
    simpa [hn] using
      Tube.volume_centredExtension_le_mul_volume_rescale_image (n := 3) hsit hR T₀ T hxy
  have hC64R : (64 : ℝ) ≤ R := by
    have hC : (64 : ℝ) ≤ (Tube.normalization.C 3 : ℝ) := by norm_num [Tube.normalization.C]
    exact le_trans hC hsit.normalizationConst_le_radius
  have hbig : (256 : ℝ) ≤ 4 * R := by linarith
  have hpow256 : (256 : ℝ) ^ 3 ≤ (4 * R) ^ 3 :=
    pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 256) hbig 3
  have h12 : (12 : ℝ) ≤ (4 * R) ^ 3 := by nlinarith [hpow256]
  have hcoef : (Tube.volume_le.C 3 : ℝ) / (Tube.le_volume.c 3 : ℝ) * (4 * R) ^ 3
      ≤ (4 * R) ^ 6 := by
    have hvp12 : (Tube.volume_le.C 3 : ℝ) / (Tube.le_volume.c 3 : ℝ) ≤ 12 :=
      Tube.volume_ratio_three_le_twelve
    calc (Tube.volume_le.C 3 : ℝ) / (Tube.le_volume.c 3 : ℝ) * (4 * R) ^ 3
          ≤ 12 * (4 * R) ^ 3 := by gcongr
      _ ≤ (4 * R) ^ 3 * (4 * R) ^ 3 := by gcongr
      _ = (4 * R) ^ 6 := by ring
  exact ⟨hth2, hpos, hvol0.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hcoef) le_rfl)⟩

/-- **The measurement that justifies the previous lemma.**

`Tube.rescale_outer_tube` is recovered from `Kakeya.CapRescale.capRescale_outer_tube` in one step.
So the two fields of `Kakeya.CapRescale.IsCapDistortion` are, in the kernel, *all* that the
outer-tube lemma consumes: the three remaining fields of `Tube.IsNormalizationDistortion`
(`one_le_dist`, `exists_subsegment`, `image_ambient_subset_closedBall`) are inert here.  That is a
compiler experiment, not an argument, and it is what makes the cap route sound: those three fields
are the ones that need the containment `T ⊆ T₀`. -/
theorem rescale_outer_tube_of_isCapDistortion {R : ℝ}
    (hsit : Tube.IsRescalingSituation θ δ σ R 3) (hn : finrank ℝ E = 3) (hR : 0 < R)
    (hδσ : (δ : ℝ) / (θ : ℝ) ≤ 4 * (σ : ℝ)) (T₀ : Tube θ E) (T : Tube δ E)
    (hdist : Tube.IsNormalizationDistortion T₀ T)
    (hball : T₀.normalization '' T.carrier ⊆ closedBall T₀.x R)
    (hxy : T₀.rescaleMap R T.x ≠ T₀.rescaleMap R T.y) :
    T₀.rescaleMap R '' T.carrier ⊆ (Tube.centredExtension σ hxy).carrier ∧
      (Tube.centredExtension σ hxy).carrier ⊆ closedBall (0 : E) 1 ∧
      volume (Tube.centredExtension σ hxy).carrier
        ≤ ENNReal.ofReal ((4 * R) ^ 6) * volume (T₀.rescaleMap R '' T.carrier) :=
  capRescale_outer_tube hsit hn hR hδσ T₀ T
    (isCapDistortion_of_isNormalizationDistortion hdist) hball hxy

/-! ## 5. The output scale `σ = δ / (4 θ)` -/

/-- **The output scale of the cap rescaling**, `σ = δ / (4 θ)`.

With the reference thickness `θ = θ' = 4 θ_ang` of a cap of angular radius `θ_ang` this is
's `δ_{k+1} = δ_k / (4 θ') = δ_k^{1-c} / 16`. -/
noncomputable def capScale (θ δ : NNReal) : NNReal := δ / (4 * θ)

theorem coe_capScale (θ δ : NNReal) : (capScale θ δ : ℝ) = (δ : ℝ) / (4 * (θ : ℝ)) := by
  simp [capScale]

theorem capScale_pos (hθ : 0 < θ) (hδ : 0 < δ) : 0 < capScale θ δ := by
  have h4θ : (0 : NNReal) < 4 * θ := by positivity
  simpa [capScale] using div_pos hδ h4θ

/-- The extra hypothesis of the outer-tube lemma holds with **equality** at `σ = δ/(4θ)`: the cap
scale is the largest scale the lemma allows, so nothing is thrown away here. -/
theorem capScale_ratio (hθ : 0 < θ) : (δ : ℝ) / (θ : ℝ) = 4 * (capScale θ δ : ℝ) := by
  have hθ0 : (0 : ℝ) < (θ : ℝ) := by exact_mod_cast hθ
  rw [coe_capScale]
  field_simp

theorem capScale_ratio_le (hθ : 0 < θ) : (δ : ℝ) / (θ : ℝ) ≤ 4 * (capScale θ δ : ℝ) :=
  (capScale_ratio hθ).le

/-- **The rescaling situation at the cap scale.**  All seven fields, with `σ = δ/(4θ)`. -/
theorem isRescalingSituation_capScale {R : ℝ} (hθ0 : 0 < θ) (hδ0 : 0 < δ) (hδθ : δ ≤ θ)
    (hθ1 : θ ≤ 1) (hR : (Tube.normalization.C 3 : ℝ) ≤ R) :
    Tube.IsRescalingSituation θ δ (capScale θ δ) R 3 where
  pos_ambient := hθ0
  inner_le_ambient := hδθ
  ambient_le_one := hθ1
  pos_out := capScale_pos hθ0 hδ0
  out_le_quarter := by
    have hθ0' : (0 : ℝ) < (θ : ℝ) := by exact_mod_cast hθ0
    have hδθ' : (δ : ℝ) ≤ (θ : ℝ) := by exact_mod_cast hδθ
    rw [coe_capScale, div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 4)]
    linarith
  out_le_ratio := by
    have hθ0' : (0 : ℝ) < (θ : ℝ) := by exact_mod_cast hθ0
    rw [coe_capScale]
    have hmono : (δ : ℝ) / (4 * (θ : ℝ)) ≤ (δ : ℝ) / (θ : ℝ) := by
      apply div_le_div_of_nonneg_left (by positivity) hθ0'
      linarith
    exact hmono
  normalizationConst_le_radius := hR

/-! ## 6. The cap family and its four transports -/

/-- **The cap–column situation.**

The hypothesis package the cap rescaling runs on.  It replaces the spine route's single
containment `∀ i ∈ s, (𝕋 i).carrier ⊆ T₀.carrier`, which is **unavailable** in a cap column: a
`Tube` (`Kakeya/Tube/Basic.lean`; it sits at the root namespace, **not** under `Kakeya.`) has a
core of length exactly `1` (`Tube.dist_eq_one`), so a unit-core `θ`-tube cannot contain a
unit-core `δ`-tube whose centre is displaced *along* the axis, and the tubes of
a cap column are displaced along the axis by up to `2`.  What replaces it is two position-free
facts plus one genuinely positional one:

* `dir` — the cap condition, i.e. membership in `Kakeya.CapBroadNarrow.capFamily s 𝕋 p (4 θ_ang)`
  at reference thickness `θ = 4 θ_ang`;
* `column` — the column condition: the *midpoint* is within transverse distance `2 θ` of the axis;
* `ball`, `base` — the standing `B₁` hypothesis of the Cap Lemma, and that the reference tube is
  anchored in `B₁`.
-/
structure IsCapColumn (T₀ : Tube θ E) (s : Finset ι) (𝕋 : ι → ShadedTube δ E) : Prop where
  /-- Each tube's direction is within `θ` of the axis, sign-blindly. -/
  dir : ∀ i ∈ s, dirDist (𝕋 i).direction T₀.direction ≤ (θ : ℝ)
  /-- Each tube's midpoint is transversally within `2 θ` of the axis. -/
  column : ∀ i ∈ s, ‖perpTo T₀ ((𝕋 i).midpoint - T₀.x)‖ ≤ 2 * (θ : ℝ)
  /-- The standing `B₁` hypothesis. -/
  ball : ∀ i ∈ s, (𝕋 i).carrier ⊆ closedBall (0 : E) 1
  /-- The reference tube is anchored near `B₁`.  The bound is `2` and not `1` because the core
  endpoint `T₀.x` of a reference tube centred at a point of `B₁` is at distance `1/2` from that
  point (`Tube.ofMidpointDirection`), so `1` would be unsatisfiable at the boundary. -/
  base : ‖T₀.x‖ ≤ 2

variable {R : ℝ} {s : Finset ι} {𝕋 : ι → ShadedTube δ E} {T₀ : Tube θ E}

omit [Nontrivial E] in
/-- Each tube of a cap column satisfies the `hball` hypothesis of the outer-tube lemma, at every
admissible ambient radius (`R ≥ C_N(3) = 64 ≥ 11/2`). -/
theorem normalization_image_subset_closedBall_of_isCapColumn (hθ0 : 0 < θ) (hδθ : δ ≤ θ)
    (hR : (Tube.normalization.C 3 : ℝ) ≤ R) (hcol : IsCapColumn T₀ s 𝕋) {i : ι} (hi : i ∈ s) :
    T₀.normalization '' (𝕋 i).carrier ⊆ closedBall T₀.x R := by
  have hδθ' : (δ : ℝ) ≤ (θ : ℝ) := by exact_mod_cast hδθ
  have hR64 : (64 : ℝ) ≤ R := by
    refine le_trans ?_ hR
    norm_num [Tube.normalization.C]
  refine normalization_image_subset_closedBall_of_column hθ0 T₀ (𝕋 i).toTube
    (hcol.dir i hi) hδθ' (hcol.column i hi)
    (fun z hz => norm_sub_x_le_of_subset_closedBall (hcol.ball i hi) hcol.base hz) ?_
  linarith

omit [Nontrivial E] in
/-- The two-field distortion package for each tube of a cap column. -/
theorem isCapDistortion_of_isCapColumn (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hcol : IsCapColumn T₀ s 𝕋)
    {i : ι} (hi : i ∈ s) : IsCapDistortion T₀ (𝕋 i).toTube :=
  isCapDistortion_of_dirDist hθ0 hθ1 T₀ (𝕋 i).toTube (hcol.dir i hi)

/-- **The outer-tube specification in a cap column** — the cap analogue of
`Kakeya.ML2Reduction.outerTube_spec`, with the containment hypothesis replaced. -/
theorem capOuterTube_spec (hn : finrank ℝ E = 3)
    (hsit : Tube.IsRescalingSituation θ δ σ R 3) (hR : 0 < R)
    (hδσ : (δ : ℝ) / (θ : ℝ) ≤ 4 * (σ : ℝ)) (T₀ : Tube θ E) (T : Tube δ E)
    (hcap : IsCapDistortion T₀ T)
    (hballR : T₀.normalization '' T.carrier ⊆ closedBall T₀.x R) :
    spineRescaleUnit hsit.pos_ambient T₀ hR '' T.carrier
        ⊆ (outerTube hsit.pos_ambient T₀ hR σ T).carrier ∧
      (outerTube hsit.pos_ambient T₀ hR σ T).carrier ⊆ closedBall (0 : E) 1 ∧
      volume (outerTube hsit.pos_ambient T₀ hR σ T).carrier
        ≤ ENNReal.ofReal ((4 * R) ^ 6)
          * volume (spineRescaleUnit hsit.pos_ambient T₀ hR '' T.carrier) := by
  have hxy : T₀.rescaleMap R T.x ≠ T₀.rescaleMap R T.y :=
    rescaleMap_x_ne_rescaleMap_y hsit.pos_ambient T₀ hR T
  obtain ⟨hsub, hpos, hvol⟩ := capRescale_outer_tube hsit hn hR hδσ T₀ T hcap hballR hxy
  refine ⟨?_, hpos, ?_⟩
  · simpa [outerTube, spineRescaleUnit_coe hsit.pos_ambient T₀ hR] using hsub
  · simpa [outerTube, spineRescaleUnit_coe hsit.pos_ambient T₀ hR] using hvol

/-! ### The per-tube specifications, and then the family -/

/-- The shade of the outer tube is exactly the rescaled shade: the intersection in the definition
of `Kakeya.ML2Reduction.outerShadedTube` is inert. -/
theorem capOuterShadedTube_shade_eq (hn : finrank ℝ E = 3)
    (hsit : Tube.IsRescalingSituation θ δ σ R 3) (hR : 0 < R)
    (hδσ : (δ : ℝ) / (θ : ℝ) ≤ 4 * (σ : ℝ)) (T₀ : Tube θ E) (S : ShadedTube δ E)
    (hcap : IsCapDistortion T₀ S.toTube)
    (hballR : T₀.normalization '' S.carrier ⊆ closedBall T₀.x R) :
    (outerShadedTube hsit.pos_ambient T₀ hR σ S).shade
      = spineRescaleUnit hsit.pos_ambient T₀ hR '' S.shade := by
  have h := (capOuterTube_spec hn hsit hR hδσ T₀ S.toTube hcap hballR).1
  refine Set.inter_eq_self_of_subset_left ?_
  exact (Set.image_mono S.shade_subset).trans h

theorem capOuterShadedTube_subset_closedBall (hn : finrank ℝ E = 3)
    (hsit : Tube.IsRescalingSituation θ δ σ R 3) (hR : 0 < R)
    (hδσ : (δ : ℝ) / (θ : ℝ) ≤ 4 * (σ : ℝ)) (T₀ : Tube θ E) (S : ShadedTube δ E)
    (hcap : IsCapDistortion T₀ S.toTube)
    (hballR : T₀.normalization '' S.carrier ⊆ closedBall T₀.x R) :
    (outerShadedTube hsit.pos_ambient T₀ hR σ S).carrier ⊆ closedBall (0 : E) 1 :=
  (capOuterTube_spec hn hsit hR hδσ T₀ S.toTube hcap hballR).2.1

/-- **The volume clause — the single source of every loss factor below.** -/
theorem capOuterShadedTube_volume_le (hn : finrank ℝ E = 3)
    (hsit : Tube.IsRescalingSituation θ δ σ R 3) (hR : 0 < R)
    (hδσ : (δ : ℝ) / (θ : ℝ) ≤ 4 * (σ : ℝ)) (T₀ : Tube θ E) (S : ShadedTube δ E)
    (hcap : IsCapDistortion T₀ S.toTube)
    (hballR : T₀.normalization '' S.carrier ⊆ closedBall T₀.x R) :
    volume (outerShadedTube hsit.pos_ambient T₀ hR σ S).carrier
      ≤ (outerLoss R : ENNReal)
        * volume (spineImage (spineRescaleUnit hsit.pos_ambient T₀ hR) S).carrier := by
  rw [coe_outerLoss, spineImage_carrier]
  exact (capOuterTube_spec hn hsit hR hδσ T₀ S.toTube hcap hballR).2.2

theorem spineImage_le_capOuterShadedTube (hn : finrank ℝ E = 3)
    (hsit : Tube.IsRescalingSituation θ δ σ R 3) (hR : 0 < R)
    (hδσ : (δ : ℝ) / (θ : ℝ) ≤ 4 * (σ : ℝ)) (T₀ : Tube θ E) (S : ShadedTube δ E)
    (hcap : IsCapDistortion T₀ S.toTube)
    (hballR : T₀.normalization '' S.carrier ⊆ closedBall T₀.x R) :
    (spineImage (spineRescaleUnit hsit.pos_ambient T₀ hR) S).toConvexSpaceBody
      ≤ (outerShadedTube hsit.pos_ambient T₀ hR σ S).toConvexSpaceBody :=
  (capOuterTube_spec hn hsit hR hδσ T₀ S.toTube hcap hballR).1

omit [Nontrivial E] in
/-- The `hball` and distortion data for the whole cap column, packaged for the family lemmas. -/
theorem capData (hsit : Tube.IsRescalingSituation θ δ σ R 3) (hθ1 : θ ≤ 1) (hδθ : δ ≤ θ)
    (hRC : (Tube.normalization.C 3 : ℝ) ≤ R) (hcol : IsCapColumn T₀ s 𝕋) :
    ∀ i ∈ s, IsCapDistortion T₀ (𝕋 i).toTube ∧
      T₀.normalization '' (𝕋 i).carrier ⊆ closedBall T₀.x R := fun _ hi =>
  ⟨isCapDistortion_of_isCapColumn hsit.pos_ambient hθ1 hcol hi,
    normalization_image_subset_closedBall_of_isCapColumn hsit.pos_ambient hδθ hRC hcol hi⟩

/-- **(a) Every member of the rescaled cap family lies in `B₁`** — no loss. -/
theorem capOuterFamily_carrier_subset_closedBall (hn : finrank ℝ E = 3)
    (hsit : Tube.IsRescalingSituation θ δ σ R 3) (hR : 0 < R) (hθ1 : θ ≤ 1) (hδθ : δ ≤ θ)
    (hRC : (Tube.normalization.C 3 : ℝ) ≤ R) (hδσ : (δ : ℝ) / (θ : ℝ) ≤ 4 * (σ : ℝ))
    (hcol : IsCapColumn T₀ s 𝕋) :
    ∀ i ∈ s, (outerFamily hsit.pos_ambient T₀ hR σ 𝕋 i).carrier ⊆ closedBall (0 : E) 1 :=
  fun i hi =>
    capOuterShadedTube_subset_closedBall hn hsit hR hδσ T₀ (𝕋 i)
      (capData hsit hθ1 hδθ hRC hcol i hi).1 (capData hsit hθ1 hδθ hRC hcol i hi).2

/-- On the index set the rescaled cap family has exactly the rescaled shades. -/
theorem capOuterFamily_shade_eq (hn : finrank ℝ E = 3)
    (hsit : Tube.IsRescalingSituation θ δ σ R 3) (hR : 0 < R) (hθ1 : θ ≤ 1) (hδθ : δ ≤ θ)
    (hRC : (Tube.normalization.C 3 : ℝ) ≤ R) (hδσ : (δ : ℝ) / (θ : ℝ) ≤ 4 * (σ : ℝ))
    (hcol : IsCapColumn T₀ s 𝕋) :
    ∀ i ∈ s, (outerFamily hsit.pos_ambient T₀ hR σ 𝕋 i).toShadedBody.shade
      = (spineFamily (spineRescaleUnit hsit.pos_ambient T₀ hR) 𝕋 i).shade := by
  intro i hi
  rw [spineFamily_apply, spineImage_shade]
  exact capOuterShadedTube_shade_eq hn hsit hR hδσ T₀ (𝕋 i)
    (capData hsit hθ1 hδθ hRC hcol i hi).1 (capData hsit hθ1 hδθ hRC hcol i hi).2

/-- **(b) The multiplicity is transported EXACTLY — no loss factor, and none is forced.**

`ShadedBody.multiplicity` reads only the shades and their union.  The outer replacement changes
neither (`capOuterFamily_shade_eq`), and the affine rescaling multiplies numerator and denominator
by the same Jacobian (`Kakeya.ML2Reduction.spineFamily_multiplicity`).  So the `(4 R)^6` of the
volume clause is **not** forced here and is not carried: the hypothesis
`capOuterShadedTube_volume_le` is never used in this proof. -/
theorem capOuterFamily_multiplicity (hn : finrank ℝ E = 3)
    (hsit : Tube.IsRescalingSituation θ δ σ R 3) (hR : 0 < R) (hθ1 : θ ≤ 1) (hδθ : δ ≤ θ)
    (hRC : (Tube.normalization.C 3 : ℝ) ≤ R) (hδσ : (δ : ℝ) / (θ : ℝ) ≤ 4 * (σ : ℝ))
    (hcol : IsCapColumn T₀ s 𝕋) :
    ShadedBody.multiplicity s (fun i => (outerFamily hsit.pos_ambient T₀ hR σ 𝕋 i).toShadedBody)
      = ShadedBody.multiplicity s (fun i => (𝕋 i).toShadedBody) := by
  rw [Tube.multiplicity_congr_of_shading_eq s
    (spineFamily (spineRescaleUnit hsit.pos_ambient T₀ hR) 𝕋)
    (fun i => (outerFamily hsit.pos_ambient T₀ hR σ 𝕋 i).toShadedBody)
    (capOuterFamily_shade_eq hn hsit hR hθ1 hδθ hRC hδσ hcol)]
  exact spineFamily_multiplicity (spineRescaleUnit hsit.pos_ambient T₀ hR) s 𝕋

/-- **(c) The fullness drops by at most `(4 R)^6`.**

The loss is forced by, and only by, `capOuterShadedTube_volume_le`: `ShadedBody.fullness` is
`∑|Y_i| / ∑|T_i|`, the shades are unchanged, and the denominator grows by exactly the factor the
volume clause allows.  Its ultimate source is that `Kakeya.ML2Reduction.outerTube` has a core of
length `1` while the rescaled core may be as short as `1/(4 R)`, i.e.
`Tube.volume_centredExtension_le_mul_volume_rescale_image`. -/
theorem capOuterFamily_le_fullness (hn : finrank ℝ E = 3)
    (hsit : Tube.IsRescalingSituation θ δ σ R 3) (hR : 0 < R) (hθ1 : θ ≤ 1) (hδθ : δ ≤ θ)
    (hR1 : 1 ≤ R) (hRC : (Tube.normalization.C 3 : ℝ) ≤ R)
    (hδσ : (δ : ℝ) / (θ : ℝ) ≤ 4 * (σ : ℝ)) (hcol : IsCapColumn T₀ s 𝕋) :
    (outerLoss R)⁻¹ * ShadedBody.fullness s (fun i => (𝕋 i).toShadedBody)
      ≤ ShadedBody.fullness s
          (fun i => (outerFamily hsit.pos_ambient T₀ hR σ 𝕋 i).toShadedBody) := by
  have hfull := Tube.le_fullness_of_volume_le (C := outerLoss R) (one_le_outerLoss hR1) s
    (spineFamily (spineRescaleUnit hsit.pos_ambient T₀ hR) 𝕋)
    (fun i => (outerFamily hsit.pos_ambient T₀ hR σ 𝕋 i).toShadedBody)
    (capOuterFamily_shade_eq hn hsit hR hθ1 hδθ hRC hδσ hcol)
    (fun i hi => capOuterShadedTube_volume_le hn hsit hR hδσ T₀ (𝕋 i)
      (capData hsit hθ1 hδθ hRC hcol i hi).1 (capData hsit hθ1 hδθ hRC hcol i hi).2)
  rwa [spineFamily_fullness (spineRescaleUnit hsit.pos_ambient T₀ hR) s 𝕋] at hfull

/-- **(d) `Δ_max` grows by at most `(4 R)^6`.**

Two hypotheses force this and both are used: the containment `spineImage_le_capOuterShadedTube`
(which makes the set of bodies inside a test body *shrink*, and is therefore free of charge) and
the volume clause (which supplies the factor).  See
`Kakeya.ML2Reduction.maxDensity_le_of_comparable`. -/
theorem capOuterFamily_maxDensity_le (hn : finrank ℝ E = 3)
    (hsit : Tube.IsRescalingSituation θ δ σ R 3) (hR : 0 < R) (hθ1 : θ ≤ 1) (hδθ : δ ≤ θ)
    (hR1 : 1 ≤ R) (hRC : (Tube.normalization.C 3 : ℝ) ≤ R)
    (hδσ : (δ : ℝ) / (θ : ℝ) ≤ 4 * (σ : ℝ)) (hcol : IsCapColumn T₀ s 𝕋) :
    Kakeya.maxDensity s
        (fun i => (outerFamily hsit.pos_ambient T₀ hR σ 𝕋 i).toConvexSpaceBody)
      ≤ (outerLoss R : ENNReal)
        * Kakeya.maxDensity s (fun i => (𝕋 i).toConvexSpaceBody) := by
  have hmax := maxDensity_le_of_comparable (C := outerLoss R) (one_le_outerLoss hR1) s
    (fun i => (spineFamily (spineRescaleUnit hsit.pos_ambient T₀ hR) 𝕋 i).toConvexSpaceBody)
    (fun i => (outerFamily hsit.pos_ambient T₀ hR σ 𝕋 i).toConvexSpaceBody)
    (fun i hi => spineImage_le_capOuterShadedTube hn hsit hR hδσ T₀ (𝕋 i)
      (capData hsit hθ1 hδθ hRC hcol i hi).1 (capData hsit hθ1 hδθ hRC hcol i hi).2)
    (fun i hi => capOuterShadedTube_volume_le hn hsit hR hδσ T₀ (𝕋 i)
      (capData hsit hθ1 hδθ hRC hcol i hi).1 (capData hsit hθ1 hδθ hRC hcol i hi).2)
  rwa [spineFamily_maxDensity (spineRescaleUnit hsit.pos_ambient T₀ hR) s 𝕋] at hmax

/-! ## 7. The reference tube of a cap column, and the packaged output -/

/-- **The reference tube of a cap column**: the `θ`-tube of unit core centred at `b` in the
direction `p`.  It is the `A_Q`  — but note that the map used below is
`Kakeya.ML2Reduction.spineRescaleUnit` of *this one* tube for **every** `i`, not of a per-tube
`T₀(i)`; see the module docstring for why the per-tube version is neither needed nor wanted. -/
noncomputable def capRefTube (θ : NNReal) (b : E) {p : E} (hp : ‖p‖ = 1) : Tube θ E :=
  Tube.ofMidpointDirection θ b p hp

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
@[simp]
theorem capRefTube_direction (θ : NNReal) (b : E) {p : E} (hp : ‖p‖ = 1) :
    (capRefTube θ b hp).direction = p := by
  simp only [capRefTube, Tube.direction, Tube.ofMidpointDirection_x, Tube.ofMidpointDirection_y]
  module

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
@[simp]
theorem capRefTube_midpoint (θ : NNReal) (b : E) {p : E} (hp : ‖p‖ = 1) :
    (capRefTube θ b hp).midpoint = b := by
  simp only [capRefTube, Tube.midpoint, Tube.ofMidpointDirection_x, Tube.ofMidpointDirection_y]
  module

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
@[simp]
theorem capRefTube_x (θ : NNReal) (b : E) {p : E} (hp : ‖p‖ = 1) :
    (capRefTube θ b hp).x = b - (1 / 2 : ℝ) • p := rfl

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
theorem norm_capRefTube_x_le (θ : NNReal) {b : E} {p : E} (hp : ‖p‖ = 1) (hb : ‖b‖ ≤ 1) :
    ‖(capRefTube θ b hp).x‖ ≤ 2 := by
  rw [capRefTube_x]
  calc ‖b - (1 / 2 : ℝ) • p‖ ≤ ‖b‖ + ‖(1 / 2 : ℝ) • p‖ := norm_sub_le _ _
    _ = ‖b‖ + 1 / 2 := by rw [norm_smul, Real.norm_eq_abs, hp]; norm_num
    _ ≤ 2 := by linarith

omit [BorelSpace E] [Nontrivial E] in
/-- **The cap–column package, from the data a column partition supplies.**

This is the producer `A4`/`A6` call: a net direction `p`, a column base point `b ∈ B̄(0,1)`, the
cap condition at radius `θ` (so `θ` is the *cap radius* `4 θ_ang`, matching
`Kakeya.CapBroadNarrow.capFamily s 𝕋 p (4 * θ_ang)` — see  and  for why the radius is `4 θ_ang` and not the plan's `3 θ_ang`) and the column condition on the
midpoints.  Note that the column condition is stated relative to `b` and is automatically
independent of where along the axis `b` sits, because `Kakeya.CapRescale.perpTo` kills `p`. -/
theorem isCapColumn_capRefTube {b p : E} (hp : ‖p‖ = 1) (hb : ‖b‖ ≤ 1)
    (hdir : ∀ i ∈ s, dirDist (𝕋 i).direction p ≤ (θ : ℝ))
    (hcolumn : ∀ i ∈ s,
      ‖((𝕋 i).midpoint - b) - (inner ℝ p ((𝕋 i).midpoint - b) : ℝ) • p‖ ≤ 2 * (θ : ℝ))
    (hball : ∀ i ∈ s, (𝕋 i).carrier ⊆ closedBall (0 : E) 1) :
    IsCapColumn (capRefTube θ b hp) s 𝕋 where
  dir := by simpa using hdir
  column := by
    intro i hi
    have hshift : (𝕋 i).midpoint - (capRefTube θ b hp).x
        = ((𝕋 i).midpoint - b) + (1 / 2 : ℝ) • p := by
      rw [capRefTube_x]; module
    rw [hshift, perpTo_add, perpTo_smul]
    have hkill : perpTo (capRefTube θ b hp) p = 0 := by
      have := perpTo_direction (capRefTube θ b hp)
      rwa [capRefTube_direction] at this
    rw [hkill, smul_zero, add_zero]
    have hrw : perpTo (capRefTube θ b hp) ((𝕋 i).midpoint - b)
        = ((𝕋 i).midpoint - b) - (inner ℝ p ((𝕋 i).midpoint - b) : ℝ) • p := by
      rw [perpTo, capRefTube_direction]
    rw [hrw]
    exact hcolumn i hi
  ball := hball
  base := norm_capRefTube_x_le θ hp hb

/-! ### The packaged output at the canonical ambient radius -/

/-- The canonical ambient normalization radius `R = C_N(3) = 64`. -/
noncomputable def capRadius : ℝ := (Tube.normalization.C 3 : ℝ)

theorem capRadius_eq : capRadius = 64 := by norm_num [capRadius, Tube.normalization.C]

theorem capRadius_pos : 0 < capRadius := by rw [capRadius_eq]; norm_num

theorem one_le_capRadius : 1 ≤ capRadius := by rw [capRadius_eq]; norm_num

/-- **The one absolute constant of the cap rescaling**, `(4 R)^6 = 256^6` at `R = 64`. -/
noncomputable def capLoss : NNReal := outerLoss capRadius

theorem one_le_capLoss : 1 ≤ capLoss := one_le_outerLoss one_le_capRadius

theorem capLoss_ne_zero : capLoss ≠ 0 := outerLoss_ne_zero one_le_capRadius

theorem coe_capLoss : (capLoss : ENNReal) = ENNReal.ofReal ((4 * capRadius) ^ 6) := rfl

/-- **A5's contract: the cap rescaling, packaged.**

From a cap column of `δ`-tubes in `B₁` at reference thickness `θ` we produce a family of honest
`σ`-tubes in `B₁` at the scale `σ = δ/(4θ)` (`Kakeya.CapRescale.capScale`), with

* multiplicity transported **exactly** (no loss, and none is forced: this clause does not mention
  `capLoss`),
* fullness down by at most `capLoss = (4 R)^6`,
* `Δ_max` up by at most `capLoss`.

The index set is literally unchanged, so `N' = N`. -/
theorem exists_capRescaledFamily (hn : finrank ℝ E = 3) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1)
    (hδ0 : 0 < δ) (hδθ : δ ≤ θ) (T₀ : Tube θ E) (hcol : IsCapColumn T₀ s 𝕋) :
    ∃ 𝕋' : ι → ShadedTube (capScale θ δ) E,
      (∀ i ∈ s, (𝕋' i).carrier ⊆ closedBall (0 : E) 1) ∧
      ShadedBody.multiplicity s (fun i => (𝕋' i).toShadedBody)
        = ShadedBody.multiplicity s (fun i => (𝕋 i).toShadedBody) ∧
      (capLoss : ENNReal)⁻¹ * ShadedBody.fullness s (fun i => (𝕋 i).toShadedBody)
        ≤ ShadedBody.fullness s (fun i => (𝕋' i).toShadedBody) ∧
      Kakeya.maxDensity s (fun i => (𝕋' i).toConvexSpaceBody)
        ≤ (capLoss : ENNReal) * Kakeya.maxDensity s (fun i => (𝕋 i).toConvexSpaceBody) := by
  have hRC : (Tube.normalization.C 3 : ℝ) ≤ capRadius := le_rfl
  have hsit : Tube.IsRescalingSituation θ δ (capScale θ δ) capRadius 3 :=
    isRescalingSituation_capScale hθ0 hδ0 hδθ hθ1 hRC
  have hδσ : (δ : ℝ) / (θ : ℝ) ≤ 4 * ((capScale θ δ : NNReal) : ℝ) := capScale_ratio_le hθ0
  refine ⟨outerFamily hsit.pos_ambient T₀ capRadius_pos (capScale θ δ) 𝕋, ?_, ?_, ?_, ?_⟩
  · exact capOuterFamily_carrier_subset_closedBall hn hsit capRadius_pos hθ1 hδθ hRC hδσ hcol
  · exact capOuterFamily_multiplicity hn hsit capRadius_pos hθ1 hδθ hRC hδσ hcol
  · have h := capOuterFamily_le_fullness hn hsit capRadius_pos hθ1 hδθ one_le_capRadius hRC
      hδσ hcol
    have hcoe : ((outerLoss capRadius)⁻¹ : NNReal) * ShadedBody.fullness s
        (fun i => (𝕋 i).toShadedBody)
        ≤ ShadedBody.fullness s
          (fun i => (outerFamily hsit.pos_ambient T₀ capRadius_pos (capScale θ δ) 𝕋 i
            ).toShadedBody) := h
    calc (capLoss : ENNReal)⁻¹ * ShadedBody.fullness s (fun i => (𝕋 i).toShadedBody)
          = (((outerLoss capRadius)⁻¹ * ShadedBody.fullness s
              (fun i => (𝕋 i).toShadedBody) : NNReal) : ENNReal) := by
            rw [ENNReal.coe_mul, ← ENNReal.coe_inv capLoss_ne_zero]
            rfl
      _ ≤ _ := ENNReal.coe_le_coe.mpr hcoe
  · exact capOuterFamily_maxDensity_le hn hsit capRadius_pos hθ1 hδθ one_le_capRadius hRC hδσ hcol

/-! ## 8. The plan's numbers, non-vacuity, and what forces each loss factor -/

/-- 's scale, in the plan's own variables: at cap radius `θ' = 4 θ_ang` the
output scale is `δ/(16 θ_ang)`, i.e. `δ^{1-c}/16` at `θ_ang = δ^c`. -/
theorem capScale_of_angular (θa δ : NNReal) : capScale (4 * θa) δ = δ / (16 * θa) := by
  rw [capScale]
  congr 1
  ring

/-- The reference tube with empty shading, the witness of
`Kakeya.CapRescale.isCapColumn_nonvacuous`. -/
noncomputable def emptyShadedCapRefTube (δ : NNReal) (b : E) {p : E} (hp : ‖p‖ = 1) :
    ShadedTube δ E where
  toTube := capRefTube δ b hp
  shade := (∅ : Set E)
  measurableSet_shade := MeasurableSet.empty
  shade_subset := Set.empty_subset _

omit [BorelSpace E] [Nontrivial E] in
@[simp]
theorem emptyShadedCapRefTube_toTube (δ : NNReal) (b : E) {p : E} (hp : ‖p‖ = 1) :
    (emptyShadedCapRefTube δ b hp).toTube = capRefTube δ b hp := rfl

omit [BorelSpace E] [Nontrivial E] in
/-- **Non-vacuity of `Kakeya.CapRescale.IsCapColumn`, by a concrete witness.**

The reference tube itself, shaded by `∅`, sits in its own cap column: its direction *is* the axis
(so the `dir` clause holds with `dirDist = 0`) and its midpoint *is* the base point (so the
`column` clause holds with `0`).  This is what makes the package a hypothesis and not a disguised
falsehood: the two quantitative clauses are simultaneously satisfiable at any `δ ≤ 1/2`. -/
theorem isCapColumn_nonvacuous {p : E} (hp : ‖p‖ = 1) (hδ : (δ : ℝ) ≤ 1 / 2) (i₀ : ι) :
    IsCapColumn (capRefTube θ (0 : E) hp) {i₀} (fun _ => emptyShadedCapRefTube δ (0 : E) hp) := by
  have hkill : perpTo (capRefTube θ (0 : E) hp) p = 0 := by
    have := perpTo_direction (capRefTube θ (0 : E) hp)
    rwa [capRefTube_direction] at this
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i _
    have : dirDist (emptyShadedCapRefTube δ (0 : E) hp).direction
        (capRefTube θ (0 : E) hp).direction = 0 := by
      simp only [emptyShadedCapRefTube_toTube, capRefTube_direction, dirDist_self]
    rw [this]
    exact θ.coe_nonneg
  · intro i _
    have hshift : (emptyShadedCapRefTube δ (0 : E) hp).midpoint - (capRefTube θ (0 : E) hp).x
        = (1 / 2 : ℝ) • p := by
      simp only [emptyShadedCapRefTube_toTube, capRefTube_midpoint, capRefTube_x]
      module
    rw [hshift, perpTo_smul, hkill, smul_zero, norm_zero]
    positivity
  · intro i _
    refine (Tube.carrier_subset_closedBall_midpoint (E := E) (capRefTube δ (0 : E) hp)).trans ?_
    have hmid : midpoint ℝ (capRefTube δ (0 : E) hp).x (capRefTube δ (0 : E) hp).y = (0 : E) := by
      simp only [capRefTube, Tube.ofMidpointDirection_x, Tube.ofMidpointDirection_y,
        midpoint_eq_smul_add]
      module
    rw [hmid]
    exact Metric.closedBall_subset_closedBall (by linarith)
  · exact norm_capRefTube_x_le θ hp (by simp)

/-- **The fullness loss is forced.**

`ShadedBody.fullness` is `∑|Y_i| / ∑|T_i|` and is therefore *strictly antitone* in the
denominator, which the outer replacement enlarges.  So a transport of fullness across a carrier
enlargement must carry a factor: the statement with the factor deleted is false, and here is the
`ℝ≥0∞` arithmetic that makes it false. -/
theorem fullness_loss_is_forced :
    ∃ a b b' : ENNReal, 0 < a ∧ a ≤ b ∧ b ≤ b' ∧ ¬ (a / b ≤ a / b') := by
  refine ⟨1, 1, 2, by norm_num, le_rfl, by norm_num, ?_⟩
  intro h
  rw [div_one] at h
  have h2 : (1 : ENNReal) / 2 < 1 := by
    refine ENNReal.div_lt_of_lt_mul ?_
    norm_num
  exact absurd h (not_le.mpr h2)

/-- **The `Δ_max` loss is forced**, for the same reason with the inequality the other way up:
`Kakeya.densityIn` is monotone in the volumes of the bodies, which the outer replacement
enlarges. -/
theorem maxDensity_loss_is_forced :
    ∃ a a' k : ENNReal, 0 < k ∧ a ≤ a' ∧ ¬ (a' / k ≤ a / k) := by
  refine ⟨1, 2, 1, by norm_num, by norm_num, ?_⟩
  intro h
  rw [div_one, div_one] at h
  norm_num at h

end Kakeya.CapRescale
