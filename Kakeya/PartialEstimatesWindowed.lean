/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.PartialEstimates
public import Kakeya.Tube.Rescale

/-!
# The windowed Katz–Tao multiplicity bound

`Kakeya.KatzTaoEstimate.multiplicity_bound` and
`Kakeya.KatzTaoEstimate.multiplicity_bound_generalize` are stated for families of `δ`-tubes
contained in `Metric.closedBall 0 1`, and that `1` cannot be moved: it is the ball in which
`Kakeya.KatzTaoEstimate` itself is formulated.

Several consumers have families in a *larger* window `Metric.closedBall 0 R` — the Section-9
node families of `Tube.UniformTubeSet`, for instance, for which the sharpest
containment the hierarchy proves is `Kakeya.MultiScaleFac.node_carrier_subset_ball`, at radius
`4`.  This file supplies the same estimate for such families, with the `R`-dependence explicit
in the loss constant.

## The route

Rescaling.  Under the homothety `Φ = AffineMap.homothety 0 w` of centre `0` and ratio
`w = (4R)⁻¹` a family of `δ`-tubes in `B̄(0, R)` becomes a family of `(w δ)`-thickened segments
of length `w` inside `B̄(0, 1/4)`.  A `Tube` has a core of length exactly one, so the image is
re-tubed by `Tube.centredExtension`, the `(w δ)`-tube on the centred unit extension of the image
core; it contains the image and, `w R = 1/4` and `w δ ≤ 1/4` being what `Tube.centredExtension`
needs, lies in `B̄(0, 1)`.

Extending the core costs volume — a factor `Kakeya.windowLoss R n = C_n / (w c_n)`, from
`Tube.volume_le` above and `Tube.le_volume` below — and that single constant prices all three
transports:

* `ShadedBody.multiplicity` is **exactly** preserved: it reads only the shades, which are moved
  by `Φ` alone (`ShadedBody.multiplicity_homothety`, `Tube.multiplicity_congr_of_shading_eq`);
* `ShadedBody.fullness` drops by at most `windowLoss` (`Tube.le_fullness_of_volume_le`);
* `Kakeya.maxDensity` grows by at most `windowLoss` (`Kakeya.maxDensity_le_of_comparable`, from
  `Tube.densityIn_le_of_comparable`) — note this is the *safe* direction only because
  `Kakeya.maxDensity` is a supremum over convex hulls of subfamilies, so enlarging the bodies
  enlarges the denominators too.

The `(w τ)^{-ε}` that comes back converts to `τ^{-ε}` at the cost of `(4R)^{ε}`; that cost, and
`windowLoss`, are absorbed into the `∀ᶠ δ in 𝓝[>] 0` exactly as the unit-ball proof absorbs its
own dimensional constants.  Nothing here is specific to `R = 4`.

## Main results

* `Kakeya.exists_shadedTube_window` — the transport package (the rescaled family and its three
  laws), the only geometry in the file;
* `Kakeya.KatzTaoEstimate.multiplicity_bound_generalize_window` — the windowed form of
  `Kakeya.KatzTaoEstimate.multiplicity_bound_generalize`, auxiliary scale included;
* `Kakeya.KatzTaoEstimate.multiplicity_bound_window` — its `τ = δ` reading, the windowed form of
  `Kakeya.KatzTaoEstimate.multiplicity_bound`.
-/

@[expose] public section

open MeasureTheory Topology ConvexSpaceBody Filter ShadedBody Metric Set

namespace Kakeya

universe u

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ## `Δ_max` under comparable bodies -/

/-- **Comparable bodies: `Δ_max` grows by at most the comparability constant.**

The `Kakeya.maxDensity` companion of `Tube.densityIn_le_of_comparable`, which is stated for a
single test body.  `Kakeya.maxDensity` is the supremum of `Kakeya.densityIn` over all test
bodies (`Kakeya.maxDensity_le_iff`, `Kakeya.le_maxDensity`), so the pointwise bound passes to
the supremum. -/
theorem maxDensity_le_of_comparable {ι : Type*} {C : NNReal} (hC : 1 ≤ C) (s : Finset ι)
    (𝕎 𝕍 : ι → ConvexSpaceBody E) (hsub : ∀ i ∈ s, 𝕎 i ≤ 𝕍 i)
    (hvol : ∀ i ∈ s, volume (𝕍 i).carrier ≤ (C : ENNReal) * volume (𝕎 i).carrier) :
    maxDensity s 𝕍 ≤ (C : ENNReal) * maxDensity s 𝕎 := by
  rw [maxDensity_le_iff]
  intro K
  refine (_root_.Tube.densityIn_le_of_comparable hC s 𝕎 𝕍 hsub hvol K).trans ?_
  gcongr
  exact le_maxDensity s 𝕎 K

/-! ## The window constants -/

/-- **The rescaling ratio of the window `B̄(0, R)`**: `w = (4R)⁻¹`.

The homothety of centre `0` and ratio `w` carries `B̄(0, R)` into `B̄(0, 1/4)`, which is the
hypothesis `Tube.centredExtension_subset_closedBall` asks of the two image core endpoints. -/
noncomputable def windowRatio (R : NNReal) : NNReal := (4 * R)⁻¹

theorem windowRatio_pos {R : NNReal} (hR : 1 ≤ R) : 0 < windowRatio R := by
  have : (0 : NNReal) < 4 * R := by
    have : (0 : NNReal) < R := lt_of_lt_of_le zero_lt_one hR
    positivity
  simpa [windowRatio] using this

theorem windowRatio_mul_self {R : NNReal} (hR : 1 ≤ R) : windowRatio R * R = 4⁻¹ := by
  have hR0 : (R : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (R : ℝ) := by
      exact_mod_cast lt_of_lt_of_le zero_lt_one hR
    exact this.ne'
  rw [← NNReal.coe_inj]
  push_cast [windowRatio]
  field_simp

theorem windowRatio_le_quarter {R : NNReal} (hR : 1 ≤ R) : windowRatio R ≤ 4⁻¹ := by
  calc windowRatio R = windowRatio R * 1 := (mul_one _).symm
    _ ≤ windowRatio R * R := by gcongr
    _ = 4⁻¹ := windowRatio_mul_self hR

theorem windowRatio_le_one {R : NNReal} (hR : 1 ≤ R) : windowRatio R ≤ 1 :=
  (windowRatio_le_quarter hR).trans (by
    rw [← NNReal.coe_le_coe]; norm_num)

/-- **The volume loss of the window rescaling.**

Re-tubing the image of a `δ`-tube — extending its core, shortened by the factor `w`, back to
unit length — multiplies the volume by at most `C_n / (w c_n)`, with `C_n = Tube.volume_le.C n`
and `c_n = Tube.le_volume.c n` the two dimensional tube-volume constants.  The `max 1` makes
`Kakeya.one_le_windowLoss` unconditional, as the comparability lemmas of `Kakeya/Tube/Rescale.lean`
require. -/
noncomputable def windowLoss (R : NNReal) (n : ℕ) : NNReal :=
  max 1 (_root_.Tube.volume_le.C n / (windowRatio R * _root_.Tube.le_volume.c n))

theorem one_le_windowLoss (R : NNReal) (n : ℕ) : 1 ≤ windowLoss R n := le_max_left _ _

theorem windowLoss_pos (R : NNReal) (n : ℕ) : 0 < windowLoss R n :=
  lt_of_lt_of_le zero_lt_one (one_le_windowLoss R n)

/-- The defining property of `Kakeya.windowLoss`: it clears the two tube-volume constants and
the ratio `w` at once. -/
theorem volume_le_C_le_windowLoss_mul {R : NNReal} (hR : 1 ≤ R) (n : ℕ) :
    _root_.Tube.volume_le.C n
      ≤ windowLoss R n * (windowRatio R * _root_.Tube.le_volume.c n) := by
  have hne : windowRatio R * _root_.Tube.le_volume.c n ≠ 0 :=
    (mul_pos (windowRatio_pos hR) (_root_.Tube.le_volume.c_pos n)).ne'
  have hpos : 0 < windowRatio R * _root_.Tube.le_volume.c n := pos_of_ne_zero hne
  exact (div_le_iff₀ hpos).mp (le_max_right _ _)

/-! ## The window rescaling, geometry -/

section Geometry

variable {δ w : NNReal}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A homothety of centre `0` and ratio `w` acts on a point as `z ↦ w • z`. -/
theorem homothety_zero_apply (w : ℝ) (z : E) :
    AffineMap.homothety (0 : E) w z = w • z := by
  simp [AffineMap.homothety_apply]

omit [MeasurableSpace E] [BorelSpace E] in
/-- The two image core endpoints of a tube under a homothety of nonzero ratio are distinct,
which is what `Tube.centredExtension` needs. -/
theorem homothety_x_ne_homothety_y (hw : 0 < w) (T : Tube δ E) :
    AffineMap.homothety (0 : E) (w : ℝ) T.x ≠ AffineMap.homothety (0 : E) (w : ℝ) T.y := by
  have hxy : T.x ≠ T.y := by
    intro h
    have := T.dist_eq_one
    rw [h, dist_self] at this
    exact zero_ne_one this
  have hw' : (w : ℝ) ≠ 0 := by
    simpa using hw.ne'
  simp only [homothety_zero_apply]
  exact fun h => hxy (smul_right_injective E hw' h)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The image of a segment under a homothety of centre `0` is the segment between the images. -/
theorem homothety_zero_mem_segment {x y z : E} (w : ℝ) (hz : z ∈ segment ℝ x y) :
    w • z ∈ segment ℝ (w • x) (w • y) := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
  exact ⟨a, b, ha, hb, hab, by module⟩

/-- **The image of a `δ`-tube under the homothety of ratio `w ≤ 1` sits in the `(w δ)`-tube on
the centred unit extension of the image core.**

The image is the `(w δ)`-neighbourhood of the image core, a segment of length `w ≤ 1`; the
containment is then `Tube.cthickening_subset_centredExtension`. -/
theorem homothety_image_subset_centredExtension (hw : 0 < w) (hw1 : w ≤ 1) (T : Tube δ E)
    (hpq : AffineMap.homothety (0 : E) (w : ℝ) T.x
        ≠ AffineMap.homothety (0 : E) (w : ℝ) T.y) :
    AffineMap.homothety (0 : E) (w : ℝ) '' T.carrier
      ⊆ (_root_.Tube.centredExtension (w * δ) hpq).carrier := by
  have hw0 : (0 : ℝ) < (w : ℝ) := by exact_mod_cast hw
  have hlen : dist (AffineMap.homothety (0 : E) (w : ℝ) T.x)
      (AffineMap.homothety (0 : E) (w : ℝ) T.y) ≤ 1 := by
    simp only [homothety_zero_apply, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs,
      abs_of_pos hw0]
    have hd : ‖T.x - T.y‖ = 1 := by
      rw [← dist_eq_norm]; exact T.dist_eq_one
    rw [hd, mul_one]
    exact_mod_cast hw1
  refine subset_trans ?_ (_root_.Tube.cthickening_subset_centredExtension hpq hlen)
  rintro _ ⟨v, hv, rfl⟩
  rw [T.carrier_eq] at hv
  obtain ⟨c, hc, hvc⟩ := Set.mem_iUnion₂.mp hv
  refine Metric.mem_cthickening_of_dist_le _ ((w : ℝ) • c) _ _ ?_ ?_
  · simpa only [homothety_zero_apply] using homothety_zero_mem_segment (w : ℝ) hc
  · rw [homothety_zero_apply, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs,
      abs_of_pos hw0, ← dist_eq_norm]
    have : dist v c ≤ (δ : ℝ) := by simpa using hvc
    calc (w : ℝ) * dist v c ≤ (w : ℝ) * (δ : ℝ) := by gcongr
      _ = ((w * δ : NNReal) : ℝ) := by push_cast; ring

end Geometry

/-! ## The window rescaling, transport -/

/-- **The window rescaling of a family of shaded `δ`-tubes.**

Given a family of shaded `δ`-tubes contained in `B̄(0, R)`, this produces a family of shaded
`(w δ)`-tubes contained in `B̄(0, 1)`, `w = Kakeya.windowRatio R = (4R)⁻¹`, with the same index
set, the same shading up to the homothety `Φ = AffineMap.homothety 0 w`, and the three transport
laws the Katz–Tao estimate consumes:

* `ShadedBody.multiplicity` is preserved **exactly** — it reads only the shades;
* `ShadedBody.fullness` drops by at most `Kakeya.windowLoss R n`;
* `Kakeya.maxDensity` grows by at most `Kakeya.windowLoss R n`.

The single source of loss is the re-tubing: `Φ` shortens each core by the factor `w`, and a
`Tube` has a core of length exactly one, so the image has to be replaced by
`Tube.centredExtension`, of volume larger by `≍ w⁻¹`. -/
theorem exists_shadedTube_window [Nontrivial E] {R : NNReal} (hR : 1 ≤ R) {δ : NNReal}
    (hδ1 : δ ≤ 1) {ι : Type*} (s : Finset ι) (T : ι → ShadedTube δ E)
    (hball : ∀ i, (T i).carrier ⊆ closedBall (0 : E) (R : ℝ)) :
    ∃ S : ι → ShadedTube (windowRatio R * δ) E,
      (∀ i, (S i).carrier ⊆ closedBall (0 : E) 1) ∧
      ShadedBody.multiplicity s (fun i ↦ (S i).toShadedBody)
        = ShadedBody.multiplicity s (fun i ↦ (T i).toShadedBody) ∧
      (windowLoss R (Module.finrank ℝ E))⁻¹
          * ShadedBody.fullness s (fun i ↦ (T i).toShadedBody)
        ≤ ShadedBody.fullness s (fun i ↦ (S i).toShadedBody) ∧
      maxDensity s (fun i ↦ (S i).toConvexSpaceBody)
        ≤ (windowLoss R (Module.finrank ℝ E) : ENNReal)
            * maxDensity s (fun i ↦ (T i).toConvexSpaceBody) := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn_def
  have hn : 0 < n := Module.finrank_pos
  set w : NNReal := windowRatio R with hw_def
  have hw : 0 < w := windowRatio_pos hR
  have hw1 : w ≤ 1 := windowRatio_le_one hR
  have hwq : w ≤ 4⁻¹ := windowRatio_le_quarter hR
  have hwR : w * R = 4⁻¹ := windowRatio_mul_self hR
  have hr : ((w : ℝ)) ≠ 0 := by
    simpa using hw.ne'
  have hw0R : (0 : ℝ) < (w : ℝ) := by exact_mod_cast hw
  -- the homothety image family
  set Wf : ι → ShadedBody E := fun i ↦ ((T i).toShadedBody).homothety 0 hr with hWf_def
  have hpq : ∀ i, AffineMap.homothety (0 : E) (w : ℝ) (T i).x
      ≠ AffineMap.homothety (0 : E) (w : ℝ) (T i).y :=
    fun i ↦ homothety_x_ne_homothety_y hw (T i).toTube
  have hwδ : w * δ ≤ 4⁻¹ := by
    calc w * δ ≤ w * 1 := by gcongr
      _ = w := mul_one _
      _ ≤ 4⁻¹ := hwq
  have hwδ1 : w * δ ≤ 1 := hwδ.trans (by rw [← NNReal.coe_le_coe]; norm_num)
  have hWcar : ∀ i, (Wf i).carrier
      = AffineMap.homothety (0 : E) (w : ℝ) '' (T i).carrier := fun i ↦ rfl
  have hsubcar : ∀ i, (Wf i).carrier
      ⊆ (_root_.Tube.centredExtension (w * δ) (hpq i)).carrier := by
    intro i
    rw [hWcar i]
    exact homothety_image_subset_centredExtension hw hw1 (T i).toTube (hpq i)
  set S : ι → ShadedTube (w * δ) E := fun i ↦
    { toTube := _root_.Tube.centredExtension (w * δ) (hpq i)
      shade := (Wf i).shade
      measurableSet_shade := (Wf i).measurableSet_shade
      shade_subset := ((Wf i).shade_subset).trans (hsubcar i) } with hS_def
  have hSshade : ∀ i, (S i).toShadedBody.shade = (Wf i).shade := fun i ↦ rfl
  have hSsub : ∀ i, (Wf i).toConvexSpaceBody ≤ (S i).toConvexSpaceBody := by
    intro i
    exact hsubcar i
  -- volume comparison
  have hpow : w ^ n = w * w ^ (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 from (Nat.sub_add_cancel hn).symm]
    rw [pow_succ]
    ring
  have hkey : _root_.Tube.volume_le.C n * (w * δ) ^ (n - 1)
      ≤ windowLoss R n * (w ^ n * (_root_.Tube.le_volume.c n * δ ^ (n - 1))) := by
    rw [mul_pow, hpow]
    calc _root_.Tube.volume_le.C n * (w ^ (n - 1) * δ ^ (n - 1))
        ≤ (windowLoss R n * (w * _root_.Tube.le_volume.c n)) * (w ^ (n - 1) * δ ^ (n - 1)) :=
          by gcongr; exact volume_le_C_le_windowLoss_mul hR n
      _ = windowLoss R n * (w * w ^ (n - 1) * (_root_.Tube.le_volume.c n * δ ^ (n - 1))) := by
          ring
  have hvolW : ∀ i, volume (Wf i).carrier
      = ((w ^ n : NNReal) : ENNReal) * volume (T i).carrier := by
    intro i
    have h := ConvexSpaceBody.volume_homothety ((T i).toShadedBody).toConvexSpaceBody 0 (w : ℝ)
    have habs : |(w : ℝ) ^ n| = ((w ^ n : NNReal) : ℝ) := by
      rw [abs_of_nonneg (by positivity)]
      push_cast
      ring
    rw [show (Wf i).carrier
        = (((T i).toShadedBody).toConvexSpaceBody.homothety 0 (w : ℝ)).carrier from rfl, h,
      ← hn_def, habs, ENNReal.ofReal_coe_nnreal]
  have hvol : ∀ i, volume (S i).toShadedBody.carrier
      ≤ (windowLoss R n : ENNReal) * volume (Wf i).carrier := by
    intro i
    have h1 : volume (S i).toShadedBody.carrier
        ≤ ((_root_.Tube.volume_le.C n * (w * δ) ^ (n - 1) : NNReal) : ENNReal) := by
      have := _root_.Tube.volume_le (E := E) hwδ1 (_root_.Tube.centredExtension (w * δ) (hpq i))
      rw [← hn_def] at this
      exact this
    have h2 : ((_root_.Tube.le_volume.c n * δ ^ (n - 1) : NNReal) : ENNReal)
        ≤ volume (T i).carrier := by
      have := _root_.Tube.le_volume (E := E) (T i).toTube
      rw [← hn_def] at this
      exact this
    calc volume (S i).toShadedBody.carrier
        ≤ ((_root_.Tube.volume_le.C n * (w * δ) ^ (n - 1) : NNReal) : ENNReal) := h1
      _ ≤ ((windowLoss R n * (w ^ n * (_root_.Tube.le_volume.c n * δ ^ (n - 1))) : NNReal)
            : ENNReal) := by exact_mod_cast hkey
      _ = (windowLoss R n : ENNReal) * (((w ^ n : NNReal) : ENNReal)
            * ((_root_.Tube.le_volume.c n * δ ^ (n - 1) : NNReal) : ENNReal)) := by
          push_cast
          ring
      _ ≤ (windowLoss R n : ENNReal) * (((w ^ n : NNReal) : ENNReal) * volume (T i).carrier) := by
          gcongr
      _ = (windowLoss R n : ENNReal) * volume (Wf i).carrier := by rw [hvolW i]
  refine ⟨S, ?_, ?_, ?_, ?_⟩
  · -- containment in the unit ball
    intro i
    have hxb : dist (AffineMap.homothety (0 : E) (w : ℝ) (T i).x) (0 : E) ≤ 1 / 4 := by
      have hx : ‖(T i).x‖ ≤ (R : ℝ) := by
        have := hball i (_root_.Tube.x_mem_carrier (T i).toTube)
        simpa [dist_zero_right] using this
      rw [homothety_zero_apply, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos hw0R]
      calc (w : ℝ) * ‖(T i).x‖ ≤ (w : ℝ) * (R : ℝ) := by gcongr
        _ = ((w * R : NNReal) : ℝ) := by push_cast; ring
        _ = 1 / 4 := by rw [hwR]; norm_num
    have hyb : dist (AffineMap.homothety (0 : E) (w : ℝ) (T i).y) (0 : E) ≤ 1 / 4 := by
      have hy : ‖(T i).y‖ ≤ (R : ℝ) := by
        have := hball i (_root_.Tube.y_mem_carrier (T i).toTube)
        simpa [dist_zero_right] using this
      rw [homothety_zero_apply, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos hw0R]
      calc (w : ℝ) * ‖(T i).y‖ ≤ (w : ℝ) * (R : ℝ) := by gcongr
        _ = ((w * R : NNReal) : ℝ) := by push_cast; ring
        _ = 1 / 4 := by rw [hwR]; norm_num
    have hsq : ((w * δ : NNReal) : ℝ) ≤ 1 / 4 := by
      have := hwδ
      rw [← NNReal.coe_le_coe] at this
      simpa using this
    exact _root_.Tube.centredExtension_subset_closedBall (hpq i) hxb hyb hsq
  · -- multiplicity
    rw [_root_.Tube.multiplicity_congr_of_shading_eq s Wf (fun i ↦ (S i).toShadedBody)
      (fun i _ ↦ hSshade i)]
    exact ShadedBody.multiplicity_homothety s (fun i ↦ (T i).toShadedBody) 0 hr
  · -- fullness
    have h := _root_.Tube.le_fullness_of_volume_le (one_le_windowLoss R n) s Wf
      (fun i ↦ (S i).toShadedBody) (fun i _ ↦ hSshade i) (fun i _ ↦ hvol i)
    rwa [ShadedBody.fullness_homothety s (fun i ↦ (T i).toShadedBody) 0 hr] at h
  · -- maxDensity
    have h := maxDensity_le_of_comparable (one_le_windowLoss R n) s
      (fun i ↦ (Wf i).toConvexSpaceBody) (fun i ↦ (S i).toConvexSpaceBody)
      (fun i _ ↦ hSsub i) (fun i _ ↦ hvol i)
    rwa [show (fun i ↦ (Wf i).toConvexSpaceBody)
        = (fun i ↦ ((T i).toConvexSpaceBody).homothety 0 (w : ℝ)) from rfl,
      Kakeya.maxDensity_homothety s (fun i ↦ (T i).toConvexSpaceBody) 0 hr] at h

/-! ## Absorbing the window constants into the loss -/

/-- The `(4R)^{ε/2}` produced by reading the loss at the rescaled auxiliary scale, together
with the volume loss `L` of the re-tubing, is absorbed by half of the loss exponent once
`δ` is below the threshold `hδ`.  `τ ≤ δ` is what lets the threshold be stated on `δ`. -/
theorem window_scale_absorb {R : NNReal} {L τ δ : NNReal}
    (hτ0 : 0 < τ) (hτδ : τ ≤ δ) {ε : ℝ} (hε : 0 < ε)
    (hδ : ((4 * R) ^ (ε / 2) * L) * δ ^ (ε / 2) ≤ 1) :
    (windowRatio R * τ) ^ (-(ε / 2)) * L ≤ τ ^ (-ε) := by
  set A : NNReal := (4 * R) ^ (ε / 2) * L with hA_def
  have hτne : τ ≠ 0 := hτ0.ne'
  have hτe : τ ^ (ε / 2) ≠ 0 := (NNReal.rpow_pos hτ0).ne'
  -- `A ≤ τ ^ (-(ε/2))`
  have hAle : A ≤ τ ^ (-(ε / 2)) := by
    have h1 : A * τ ^ (ε / 2) ≤ 1 := by
      refine le_trans ?_ hδ
      gcongr
    rw [NNReal.rpow_neg]
    calc A = A * τ ^ (ε / 2) * (τ ^ (ε / 2))⁻¹ := by
            rw [mul_assoc, mul_inv_cancel₀ hτe, mul_one]
      _ ≤ 1 * (τ ^ (ε / 2))⁻¹ := by gcongr
      _ = (τ ^ (ε / 2))⁻¹ := one_mul _
  -- the ratio contributes exactly `(4R)^{ε/2}`
  have hwsplit : (windowRatio R * τ) ^ (-(ε / 2))
      = (4 * R) ^ (ε / 2) * τ ^ (-(ε / 2)) := by
    rw [NNReal.mul_rpow]
    congr 1
    rw [windowRatio, NNReal.rpow_neg, NNReal.inv_rpow, inv_inv]
  have hsplit : τ ^ (-ε) = τ ^ (-(ε / 2)) * τ ^ (-(ε / 2)) := by
    rw [← NNReal.rpow_add hτne]
    congr 1
    ring
  rw [hwsplit, hsplit]
  calc (4 * R) ^ (ε / 2) * τ ^ (-(ε / 2)) * L
      = A * τ ^ (-(ε / 2)) := by rw [hA_def]; ring
    _ ≤ τ ^ (-(ε / 2)) * τ ^ (-(ε / 2)) := by gcongr

/-- The fullness hypothesis of the unit-ball estimate, at the rescaled auxiliary scale
`w τ`, follows from the windowed one at exponent `η/2` once `δ` is below the threshold `hδ`. -/
theorem window_fullness_absorb {R : NNReal} (hR : 1 ≤ R) {L τ δ f g : NNReal}
    (hτ0 : 0 < τ) (hτδ : τ ≤ δ) {η : ℝ} (hη : 0 < η)
    (hδ : δ ^ (η / 2) ≤ L⁻¹) (hfull : τ ^ (η / 2) ≤ f) (hLf : L⁻¹ * f ≤ g) :
    (windowRatio R * τ) ^ η ≤ g := by
  have hτne : τ ≠ 0 := hτ0.ne'
  have hw1 : windowRatio R ≤ 1 := windowRatio_le_one hR
  calc (windowRatio R * τ) ^ η = windowRatio R ^ η * τ ^ η := NNReal.mul_rpow
    _ ≤ 1 * τ ^ η := by
        gcongr
        exact NNReal.rpow_le_one hw1 hη.le
    _ = τ ^ (η / 2) * τ ^ (η / 2) := by
        rw [one_mul, ← NNReal.rpow_add hτne]
        congr 1
        ring
    _ ≤ L⁻¹ * f :=
        mul_le_mul' (le_trans (NNReal.rpow_le_rpow hτδ (by linarith)) hδ) hfull
    _ ≤ g := hLf

/-! ## The windowed multiplicity bound -/

/-- **[GWZ, Lemma 3.7] on a window of radius `R`, with an auxiliary scale.**

`Kakeya.KatzTaoEstimate.multiplicity_bound_generalize` with the ball hypothesis relaxed from
`Metric.closedBall 0 1` to `Metric.closedBall 0 R`, for any fixed `1 ≤ R`.

The `1` of the unit-ball form cannot be moved — it is the ball in which `Kakeya.KatzTaoEstimate`
is stated — so the family is *rescaled* into the unit ball by
`Kakeya.exists_shadedTube_window`, at the ratio `Kakeya.windowRatio R = (4R)⁻¹`.  The three
costs of that rescaling are

* the volume loss `Kakeya.windowLoss R n` of re-tubing the shortened cores, which prices both
  the drop in `ShadedBody.fullness` and the growth of `Kakeya.maxDensity`, and
* the factor `(4R)^{ε/2}` from reading the loss at the rescaled auxiliary scale `w τ` instead of
  at `τ`,

and all of them are absorbed into `τ ^ (-ε)` for `δ` small (`Kakeya.window_scale_absorb`,
`Kakeya.window_fullness_absorb`), exactly as the unit-ball proof absorbs its own dimensional
constants.  Since `R` is a *parameter*, the threshold on `δ` and the exponent `η` depend on it;
nothing here is specific to any particular value of `R`.

`β ≤ 1` is used, and is genuinely needed by this route: the conclusion carries
`Δ_max ^ (1 - β)`, and the rescaling controls `Δ_max` of the rescaled family from *above*, so
the exponent has to be nonnegative for that control to be usable.  Every consumer of the Kakeya
bootstrap has `β ≤ 1`. -/
theorem KatzTaoEstimate.multiplicity_bound_generalize_window [Nontrivial E] {β : ℝ}
    (hβ_0 : 0 ≤ β) (hβ_1 : β ≤ 1) (h : KatzTaoEstimate.{u} E β) {R : NNReal} (hR : 1 ≤ R) :
    ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
    ∀ τ : NNReal, 0 < τ → τ ≤ δ →
    ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ E),
      (∀ i, (T i).carrier ⊆ Metric.closedBall 0 (R : ℝ)) →
      ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ τ ^ η →
      ShadedBody.multiplicity s (fun i ↦ (T i).toShadedBody) ≤
      (τ : ENNReal) ^ (-ε) * (maxDensity s (fun i ↦ (T i).toConvexSpaceBody)) ^ (1 - β) *
        (s.card : ENNReal) ^ β := by
  classical
  intro ε hε
  set n : ℕ := Module.finrank ℝ E with hn_def
  set w : NNReal := windowRatio R with hw_def
  set L : NNReal := windowLoss R n with hL_def
  have hw : 0 < w := windowRatio_pos hR
  have hw1 : w ≤ 1 := windowRatio_le_one hR
  have hL1 : 1 ≤ L := one_le_windowLoss R n
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  obtain ⟨η₁, hη₁, hev⟩ :=
    KatzTaoEstimate.multiplicity_bound_generalize (E := E) hβ_0 h (ε / 2) (by linarith)
  obtain ⟨u, hu0, hsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hev
  set A : NNReal := (4 * R) ^ (ε / 2) * L with hA_def
  have hA0 : 0 < A := by
    have h4R : (0 : NNReal) < 4 * R := by
      have : (0 : NNReal) < R := lt_of_lt_of_le zero_lt_one hR
      positivity
    exact mul_pos (NNReal.rpow_pos h4R) hL0
  set d3 : NNReal := L⁻¹ ^ (2 / η₁) with hd3_def
  set d4 : NNReal := A⁻¹ ^ (2 / ε) with hd4_def
  have hd3 : 0 < d3 := NNReal.rpow_pos (inv_pos.mpr hL0)
  have hd4 : 0 < d4 := NNReal.rpow_pos (inv_pos.mpr hA0)
  set δ₀ : NNReal := min (min 1 u) (min d3 d4) with hδ₀_def
  have hδ₀ : 0 < δ₀ := lt_min (lt_min zero_lt_one hu0) (lt_min hd3 hd4)
  refine ⟨η₁ / 2, by positivity, ?_⟩
  filter_upwards [Ioo_mem_nhdsGT hδ₀] with δ hδ
  obtain ⟨hδ0, hδlt⟩ := hδ
  have hδ1 : δ ≤ 1 := (hδlt.trans_le ((min_le_left _ _).trans (min_le_left _ _))).le
  have hδu : δ ≤ u := (hδlt.trans_le ((min_le_left _ _).trans (min_le_right _ _))).le
  have hδd3 : δ ≤ d3 := (hδlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le
  have hδd4 : δ ≤ d4 := (hδlt.trans_le ((min_le_right _ _).trans (min_le_right _ _))).le
  -- the two thresholds, in the form the absorption lemmas want
  have hthr3 : δ ^ (η₁ / 2) ≤ L⁻¹ := by
    calc δ ^ (η₁ / 2) ≤ d3 ^ (η₁ / 2) := NNReal.rpow_le_rpow hδd3 (by positivity)
      _ = L⁻¹ := by
          rw [hd3_def, ← NNReal.rpow_mul]
          rw [show 2 / η₁ * (η₁ / 2) = 1 by field_simp, NNReal.rpow_one]
  have hthr4 : A * δ ^ (ε / 2) ≤ 1 := by
    have : δ ^ (ε / 2) ≤ A⁻¹ := by
      calc δ ^ (ε / 2) ≤ d4 ^ (ε / 2) := NNReal.rpow_le_rpow hδd4 (by positivity)
        _ = A⁻¹ := by
            rw [hd4_def, ← NNReal.rpow_mul]
            rw [show 2 / ε * (ε / 2) = 1 by field_simp, NNReal.rpow_one]
    calc A * δ ^ (ε / 2) ≤ A * A⁻¹ := by gcongr
      _ = 1 := mul_inv_cancel₀ hA0.ne'
  intro τ hτ0 hτδ ι s T hball hfull
  obtain ⟨S, hSball, hSmult, hSfull, hSmd⟩ := exists_shadedTube_window hR hδ1 s T hball
  -- apply the unit-ball estimate to the rescaled family
  have hwδ0 : 0 < w * δ := mul_pos hw hδ0
  have hwδu : w * δ ≤ u := by
    calc w * δ ≤ 1 * δ := by gcongr
      _ = δ := one_mul _
      _ ≤ u := hδu
  have hfullS : ShadedBody.fullness s (fun i ↦ (S i).toShadedBody) ≥ (w * τ) ^ η₁ :=
    window_fullness_absorb hR hτ0 hτδ hη₁ hthr3 hfull hSfull
  have hmain := hsub ⟨hwδ0, hwδu⟩ (w * τ) (mul_pos hw hτ0) (by gcongr) s S hSball hfullS
  rw [hSmult] at hmain
  refine hmain.trans ?_
  -- discharge the two losses
  have h1β : (0 : ℝ) ≤ 1 - β := by linarith
  have hLE : (1 : ENNReal) ≤ (L : ENNReal) := by exact_mod_cast hL1
  have hstep1 : (maxDensity s (fun i ↦ (S i).toConvexSpaceBody)) ^ (1 - β)
      ≤ (L : ENNReal) * (maxDensity s (fun i ↦ (T i).toConvexSpaceBody)) ^ (1 - β) := by
    calc (maxDensity s (fun i ↦ (S i).toConvexSpaceBody)) ^ (1 - β)
        ≤ ((L : ENNReal) * maxDensity s (fun i ↦ (T i).toConvexSpaceBody)) ^ (1 - β) :=
          ENNReal.rpow_le_rpow hSmd h1β
      _ = (L : ENNReal) ^ (1 - β)
            * (maxDensity s (fun i ↦ (T i).toConvexSpaceBody)) ^ (1 - β) :=
          ENNReal.mul_rpow_of_nonneg _ _ h1β
      _ ≤ (L : ENNReal) ^ (1 : ℝ)
            * (maxDensity s (fun i ↦ (T i).toConvexSpaceBody)) ^ (1 - β) :=
          mul_le_mul' (ENNReal.rpow_le_rpow_of_exponent_le hLE (by linarith)) le_rfl
      _ = (L : ENNReal) * (maxDensity s (fun i ↦ (T i).toConvexSpaceBody)) ^ (1 - β) := by
          rw [ENNReal.rpow_one]
  have hstep2 : ((w * τ : NNReal) : ENNReal) ^ (-(ε / 2)) * (L : ENNReal)
      ≤ ((τ : NNReal) : ENNReal) ^ (-ε) := by
    have hnn : ((w * τ : NNReal)) ≠ 0 := (mul_pos hw hτ0).ne'
    rw [← ENNReal.coe_rpow_of_ne_zero hnn, ← ENNReal.coe_rpow_of_ne_zero hτ0.ne',
      ← ENNReal.coe_mul, ENNReal.coe_le_coe]
    exact window_scale_absorb hτ0 hτδ hε hthr4
  calc ((w * τ : NNReal) : ENNReal) ^ (-(ε / 2))
        * (maxDensity s (fun i ↦ (S i).toConvexSpaceBody)) ^ (1 - β) * (s.card : ENNReal) ^ β
      ≤ ((w * τ : NNReal) : ENNReal) ^ (-(ε / 2))
        * ((L : ENNReal) * (maxDensity s (fun i ↦ (T i).toConvexSpaceBody)) ^ (1 - β))
        * (s.card : ENNReal) ^ β := by gcongr
    _ = (((w * τ : NNReal) : ENNReal) ^ (-(ε / 2)) * (L : ENNReal))
        * (maxDensity s (fun i ↦ (T i).toConvexSpaceBody)) ^ (1 - β)
        * (s.card : ENNReal) ^ β := by ring
    _ ≤ ((τ : NNReal) : ENNReal) ^ (-ε)
        * (maxDensity s (fun i ↦ (T i).toConvexSpaceBody)) ^ (1 - β)
        * (s.card : ENNReal) ^ β := by gcongr

/-- **[GWZ, Lemma 3.7] on a window of radius `R`.**

`Kakeya.KatzTaoEstimate.multiplicity_bound` with the ball hypothesis relaxed from
`Metric.closedBall 0 1` to `Metric.closedBall 0 R`, for any fixed `1 ≤ R`: the `τ = δ` reading
of `Kakeya.KatzTaoEstimate.multiplicity_bound_generalize_window`. -/
theorem KatzTaoEstimate.multiplicity_bound_window [Nontrivial E] {β : ℝ}
    (hβ_0 : 0 ≤ β) (hβ_1 : β ≤ 1) (h : KatzTaoEstimate.{u} E β) {R : NNReal} (hR : 1 ≤ R) :
    ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
    ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ E),
      (∀ i, (T i).carrier ⊆ Metric.closedBall 0 (R : ℝ)) →
      (ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) : ℝ) ≥ (δ : ℝ) ^ η →
      ShadedBody.multiplicity s (fun i ↦ (T i).toShadedBody) ≤
      (δ : ENNReal) ^ (-ε) * (maxDensity s (fun i ↦ (T i).toConvexSpaceBody)) ^ (1 - β) *
        (s.card : ENNReal) ^ β := by
  intro ε hε
  obtain ⟨η, hη, hev⟩ :=
    KatzTaoEstimate.multiplicity_bound_generalize_window (E := E) hβ_0 hβ_1 h hR ε hε
  refine ⟨η, hη, ?_⟩
  filter_upwards [hev, self_mem_nhdsWithin] with δ hδ hδ0
  intro ι s T hball hfull
  have hδ0' : (0 : NNReal) < δ := hδ0
  have hfull' : ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η := by
    have : ((δ ^ η : NNReal) : ℝ)
        ≤ ((ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) : NNReal) : ℝ) := by
      rw [NNReal.coe_rpow]
      exact hfull
    exact_mod_cast this
  exact hδ δ hδ0' le_rfl s T hball hfull'

/-! ## Non-vacuity -/

/-- **The windowed bound at `R = 1` is the unit-ball bound.**

A compiler-checked certificate that nothing in
`Kakeya.KatzTaoEstimate.multiplicity_bound_generalize_window` is vacuous or unsuppliable: at
`R = 1` its ball hypothesis is *verbatim* that of
`Kakeya.KatzTaoEstimate.multiplicity_bound_generalize`, and its conclusion is verbatim that
conclusion, so the windowed form is at least as strong as the form it generalises (on `β ≤ 1`,
which is the only hypothesis it adds; see the discussion there). -/
example [Nontrivial E] {β : ℝ} (hβ_0 : 0 ≤ β) (hβ_1 : β ≤ 1) (h : KatzTaoEstimate.{u} E β) :
    ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
    ∀ τ : NNReal, 0 < τ → τ ≤ δ →
    ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ E),
      (∀ i, (T i).carrier ⊆ Metric.closedBall 0 1) →
      ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ τ ^ η →
      ShadedBody.multiplicity s (fun i ↦ (T i).toShadedBody) ≤
      (τ : ENNReal) ^ (-ε) * (maxDensity s (fun i ↦ (T i).toConvexSpaceBody)) ^ (1 - β) *
        (s.card : ENNReal) ^ β := by
  simpa using
    KatzTaoEstimate.multiplicity_bound_generalize_window (E := E) hβ_0 hβ_1 h (R := 1) le_rfl

end Kakeya
