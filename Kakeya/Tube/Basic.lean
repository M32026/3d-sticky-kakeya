/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib.Analysis.Normed.Module.Ball.Pointwise
public import Kakeya.Mathlib.Analysis.Segment
public import Kakeya.Mathlib.Topology.Metric
public import Kakeya.Thickness.Basic
public import Kakeya.Thickness.Volume
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
  In this file we collect facts about δ-tubes.

## TODOs :
* Golf `le_volume` further to get it down to 7-digits.

-/

open MeasureTheory ENNReal Metric

variable
  {δ : NNReal}
  {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

@[expose] public section

/-- A `Tube δ E` is a δ-tube in `E`, defined as the closed δ-neighborhood of a unit line segment. -/
structure Tube (δ : NNReal) (E : Type*) [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E] extends ConvexSpaceBody E where
  /-- The starting point of the tube. -/
  x : E
  /-- The endpoint of the tube. -/
  y : E
  dist_eq_one : dist x y = 1
  carrier_eq : carrier = ⋃ z ∈ segment ℝ x y, closedBall z δ

@[ext]
lemma Tube.ext {T1 T2 : Tube δ E} (h1 : T1.carrier = T2.carrier) (h2 : T1.x = T2.x)
    (h3 : T1.y = T2.y) : T1 = T2 := by
  cases T1; cases T2
  congr 1
  simpa using ConvexSpaceBody.ext h1

namespace Tube -- Collect here basics about δ-tubes

/-- The direction of a δ-tube, defined as `T.y - T.x`. -/
abbrev direction (T : Tube δ E) : E := T.y - T.x

theorem norm_direction (T : Tube δ E) : ‖T.direction‖ = 1 :=
  dist_eq_norm_sub' T.x T.y ▸ T.dist_eq_one

/-- The center of a `δ`-tube: the midpoint of its defining endpoints. -/
noncomputable
abbrev center (T : Tube δ E) : E := midpoint ℝ T.x T.y

/-- Translation of a `δ`-tube by a vector, translating its endpoints and carrier. -/
@[simps!]
def vadd (T : Tube δ E) (v : E) : Tube δ E where
  toConvexSpaceBody := T.toConvexSpaceBody.vadd v
  x := v + T.x
  y := v + T.y
  dist_eq_one := by rw [dist_add_left, T.dist_eq_one]
  carrier_eq := by
    change (v + ·) '' T.carrier = _
    rw [T.carrier_eq, Set.image_iUnion₂, ← segment_translate_image, Set.biUnion_image]
    exact Set.iUnion₂_congr fun z _ => vadd_closedBall''

/-- Translation of a `δ`-tube by a vector. -/
@[simps!]
def translate (T : Tube δ E) (v : E) : Tube δ E where
  __ := T.vadd v
  toConvexSpaceBody := ConvexSpaceBody.translate T.toConvexSpaceBody v


variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

theorem carrier_eq_cthickening (T : Tube δ E) :
    T.carrier = cthickening δ (segment ℝ T.x T.y) := by
  rw [T.carrier_eq, isClosed_segment.cthickening_eq_biUnion_closedBall]
  positivity

/-- Build a `δ`-tube from endpoints at distance one. -/
@[simps!]
def mk' (δ) {x y : E} (dist_eq_one : dist x y = 1) : Tube δ E where
  x
  y
  dist_eq_one
  carrier := ⋃ z ∈ segment ℝ x y, closedBall z δ
  carrier_eq := rfl
  convex' := by
    rw [← isClosed_segment.cthickening_eq_biUnion_closedBall δ.coe_nonneg]
    exact ((convex_segment _ _).cthickening _).isConvexSet
  isCompact' := by
    rw [← isClosed_segment.cthickening_eq_biUnion_closedBall δ.coe_nonneg]
    exact isCompact_segment.cthickening
  nonempty' := ⟨x, Set.mem_biUnion (left_mem_segment ℝ x y) (mem_closedBall_self δ.coe_nonneg)⟩

/-- Rescale a `δ`-tube to a `ρ`-tube. -/
def rescale {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {δ : NNReal} (T : Tube δ E) (ρ : NNReal) : Tube ρ E := mk' ρ T.dist_eq_one

/-- Rescaling a `δ`-tube to its own radius `δ` does nothing, as convex bodies.  This is what
makes the `σ = δ` case of the fibre family `𝕋_{σ∣ρ}[i₀]` agree with the plain family `𝕋`. -/
@[simp]
theorem toConvexSpaceBody_rescale_self {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E] {δ : NNReal} (T : Tube δ E) :
    (T.rescale δ).toConvexSpaceBody = T.toConvexSpaceBody :=
  ConvexSpaceBody.ext T.carrier_eq.symm

/-- Rescaling a tube twice keeps only the outer scale: `(T.rescale a).rescale b
= T.rescale b`, since `rescale` preserves the endpoints `T.x, T.y`. -/
theorem rescale_rescale {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E] {δ : NNReal} (T : Tube δ E) (a b : NNReal) :
    (T.rescale a).rescale b = T.rescale b := rfl

/-- Translation and rescaling of tubes commute: `(T.translate v).rescale ρ`
equals `(T.rescale ρ).translate v`. Used downstream in
`subStickyFrostmanLemma.iterate` to manipulate child families. -/
theorem translate_rescale_swap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {δ : NNReal} (T : Tube δ E) (v : E) (ρ : NNReal) :
    (T.translate v).rescale ρ = (T.rescale ρ).translate v :=
  Tube.ext (((T.translate v).rescale ρ).carrier_eq.trans
    ((T.rescale ρ).translate v).carrier_eq.symm) rfl rfl

/-- The `ρ`-rescale of the thin `δ'`-tube sharing `P`'s core has the same carrier
as `P` itself.  Lets free `ρ`-tube parents be presented as `δ'`-tube rescales,
reducing free-parent packing statements to the rescale-parent ones. -/
theorem mk'_rescale_carrier
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {δ' ρ : NNReal} (P : Tube ρ E) :
    ((Tube.mk' δ' P.dist_eq_one).rescale ρ).carrier = P.carrier := by
  rw [((Tube.mk' δ' P.dist_eq_one).rescale ρ).carrier_eq, P.carrier_eq]
  rfl

/-- Convex-body form of `mk'_rescale_carrier`. -/
theorem mk'_rescale_body
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {δ' ρ : NNReal} (P : Tube ρ E) :
    ((Tube.mk' δ' P.dist_eq_one).rescale ρ).toConvexSpaceBody = P.toConvexSpaceBody := by
  apply ConvexSpaceBody.ext
  exact mk'_rescale_carrier P

/-- Carrier-level bridge between `Metric.cthickening` and `Tube.rescale`: the
closed `ρ`-thickening of a `δ`-tube's carrier coincides with the carrier of the
`(δ + ρ)`-rescaled tube. -/
theorem cthickening_carrier
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {δ : NNReal} (T : Tube δ E) (ρ : NNReal) :
    Metric.cthickening (ρ : ℝ) T.carrier = (T.rescale (δ + ρ)).carrier := by
  rw [(T.rescale (δ + ρ)).carrier_eq_cthickening, T.carrier_eq_cthickening,
      cthickening_cthickening ρ.coe_nonneg δ.coe_nonneg, NNReal.coe_add, add_comm (ρ : ℝ)]
  rfl

/-- `ConvexBody`-level form of `Tube.cthickening_carrier`. -/
theorem toConvexBody_cthickening_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {δ : NNReal} (T : Tube δ E) (ρ : NNReal) :
    T.toConvexSpaceBody.cthickening (ρ : ℝ) = (T.rescale (δ + ρ)).toConvexSpaceBody := by
  apply ConvexSpaceBody.ext
  exact T.cthickening_carrier ρ

/-- Shifted form used at the Sticky/Uniform boundary: when `δ ≤ ρ`, the
`(ρ - δ)`-cthickening of a `δ`-tube is the `ρ`-rescaled tube as convex bodies. -/
theorem toConvexBody_cthickening_sub
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {δ ρ : NNReal} (T : Tube δ E) (h : δ ≤ ρ) :
    T.toConvexSpaceBody.cthickening ((ρ : ℝ) - (δ : ℝ)) = (T.rescale ρ).toConvexSpaceBody := by
  have h_sub : (((ρ - δ : NNReal) : ℝ)) = (ρ : ℝ) - (δ : ℝ) := NNReal.coe_sub h
  have h_add : δ + (ρ - δ) = ρ := add_tsub_cancel_of_le h
  have h_eq := T.toConvexBody_cthickening_eq (ρ - δ)
  rw [h_sub, h_add] at h_eq
  exact h_eq

/-- Since a `Tube`'s convex body is determined by its carrier, two tubes with the same
carrier have the same convex body (even though `Tube.ext` also needs the endpoints). -/
theorem body_eq_of_carrier_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {δ : NNReal} {T₁ T₂ : Tube δ E} (h : T₁.carrier = T₂.carrier) :
    T₁.toConvexSpaceBody = T₂.toConvexSpaceBody := by
  exact ConvexSpaceBody.ext h

/-- Carrier-level form of `rescale_body_eq_of_carrier_eq`: for `δ ≤ ρ`, the `ρ`-rescale
carrier of a `δ`-tube depends only on the tube's carrier. -/
theorem rescale_carrier_eq_of_carrier_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {δ ρ : NNReal} {T₁ T₂ : Tube δ E} (h : T₁.carrier = T₂.carrier) (hδρ : δ ≤ ρ) :
    (T₁.rescale ρ).carrier = (T₂.rescale ρ).carrier := by
  calc
    (T₁.rescale ρ).carrier = Metric.cthickening ((ρ - δ : NNReal) : ℝ) T₁.carrier := by
      have h_add : δ + (ρ - δ) = ρ := add_tsub_cancel_of_le hδρ
      have h_eq := T₁.cthickening_carrier (ρ - δ)
      rw [h_add] at h_eq
      rw [h_eq]
    _ = Metric.cthickening ((ρ - δ : NNReal) : ℝ) T₂.carrier := by rw [h]
    _ = (T₂.rescale ρ).carrier := by
      have h_add : δ + (ρ - δ) = ρ := add_tsub_cancel_of_le hδρ
      have h_eq := T₂.cthickening_carrier (ρ - δ)
      rw [h_add] at h_eq
      rw [h_eq]

/-- **Rescale rigidity from the carrier alone.**  For `δ ≤ ρ` the `ρ`-rescale of a
`δ`-tube is the `(ρ - δ)`-thickening of its own body, so tubes sharing a carrier (for
instance `T` and `T.reverse`) have literally equal `ρ`-rescale bodies.  This is what lets
carrier-duplicate tubes be replaced by a class representative with no constant loss. -/
theorem rescale_body_eq_of_carrier_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {δ ρ : NNReal} {T₁ T₂ : Tube δ E} (h : T₁.carrier = T₂.carrier) (hδρ : δ ≤ ρ) :
    (T₁.rescale ρ).toConvexSpaceBody = (T₂.rescale ρ).toConvexSpaceBody := by
  calc
    (T₁.rescale ρ).toConvexSpaceBody = T₁.toConvexSpaceBody.cthickening ((ρ : ℝ) - (δ : ℝ)) := by
      symm; exact T₁.toConvexBody_cthickening_sub hδρ
    _ = T₂.toConvexSpaceBody.cthickening ((ρ : ℝ) - (δ : ℝ)) := by
      rw [body_eq_of_carrier_eq h]
    _ = (T₂.rescale ρ).toConvexSpaceBody := T₂.toConvexBody_cthickening_sub hδρ

/-- When `δ ≤ ρ`, a `δ`-tube's convex body is contained in its own rescale to
`ρ`. Translate-free companion to `translate_le_rescale`. -/
theorem le_rescale {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {δ ρ : NNReal} (T : Tube δ E) (h : δ ≤ ρ) :
    (T.toConvexSpaceBody : ConvexSpaceBody E) ≤ (T.rescale ρ).toConvexSpaceBody := by
  rw [← T.toConvexBody_cthickening_sub h]
  intro x hx
  exact Metric.self_subset_cthickening _ hx

/-- When `δ ≤ ρ`, the convex body of a translated `δ`-tube is contained in
the convex body of the same translated tube rescaled to `ρ`. Used in the
filter-strength transfer for `density_to_isKatzTao`. -/
theorem translate_le_rescale
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {δ ρ : NNReal} (T : Tube δ E) (v : E) (h : δ ≤ ρ) :
    ((T.translate v).toConvexSpaceBody : ConvexSpaceBody E)
      ≤ ((T.translate v).rescale ρ).toConvexSpaceBody :=
  (T.translate v).le_rescale h

/-- `Tube.rescale` radius monotonicity at fixed `T`: a larger target radius
yields a larger convex body. Companion to `le_rescale`
(which varies the target radius from `δ`). Used by the anchor-density
continuous-extension lemma to compare anchor-scale filters across
consecutive chain scales. -/
theorem rescale_le_rescale_of_radius_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {δ : NNReal} (T : Tube δ E) {ρ₁ ρ₂ : NNReal} (h : ρ₁ ≤ ρ₂) :
    (T.rescale ρ₁).toConvexSpaceBody ≤ (T.rescale ρ₂).toConvexSpaceBody := by
  have hbody : ((T.rescale ρ₁).rescale ρ₂).toConvexSpaceBody
      = (T.rescale ρ₂).toConvexSpaceBody := rfl
  rw [← hbody, ← (T.rescale ρ₁).toConvexBody_cthickening_sub h]
  intro x hx
  exact Metric.self_subset_cthickening _ hx

/-- Thickening absorbs small translations: if `‖v‖ ≤ ρ'`, then translating a
`δ`-tube by `v` then rescaling to `ρ` is contained in rescaling the original
tube to `ρ + ρ'`. Used in `Kakeya.Sticky.lean` to bridge leaf and ancestor
rescales in the chain of random translations. -/
theorem translate_rescale_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {δ ρ ρ' : NNReal} (T : Tube δ E) (v : E)
    (h_norm : ‖v‖ ≤ (ρ' : ℝ)) (hδρ : δ ≤ ρ) :
    ((T.translate v).rescale ρ).toConvexSpaceBody
      ≤ (T.rescale (ρ + ρ')).toConvexSpaceBody := by
  have hρ_nn : (0 : ℝ) ≤ (ρ : ℝ) - (δ : ℝ) := by
    have := NNReal.coe_le_coe.mpr hδρ; linarith
  rw [T.translate_rescale_swap v ρ,
      show ((T.rescale ρ).translate v).toConvexSpaceBody
        = ConvexSpaceBody.translate (T.rescale ρ).toConvexSpaceBody v from rfl,
      ← T.toConvexBody_cthickening_sub hδρ,
      ← T.toConvexBody_cthickening_sub (hδρ.trans le_self_add)]
  rintro _ ⟨y, hy, rfl⟩
  change v + y ∈ Metric.cthickening (((ρ + ρ' : NNReal) : ℝ) - (δ : ℝ)) T.carrier
  rw [show ((ρ + ρ' : NNReal) : ℝ) - (δ : ℝ) = (ρ' : ℝ) + ((ρ : ℝ) - (δ : ℝ)) by push_cast; ring]
  exact Metric.cthickening_cthickening_subset ρ'.coe_nonneg hρ_nn T.carrier
    (Metric.mem_cthickening_of_dist_le _ y _ _ hy (by simpa [dist_eq_norm] using h_norm))

/-- Finset-sum form of `translate_rescale_le`: translating a `δ`-tube by a sum vector
`∑ i ∈ S, v i` and then rescaling to `ρ` is contained in rescaling the original tube to
`ρ + ∑ i ∈ S, b i`, provided each `‖v i‖ ≤ (b i : ℝ)`. -/
theorem translate_sum_rescale_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {ι : Type*} {δ ρ : NNReal} (T : Tube δ E) (S : Finset ι)
    (v : ι → E) (b : ι → NNReal)
    (h_norm : ∀ i ∈ S, ‖v i‖ ≤ (b i : ℝ)) (hδρ : δ ≤ ρ) :
    ((T.translate (∑ i ∈ S, v i)).rescale ρ).toConvexSpaceBody
      ≤ (T.rescale (ρ + ∑ i ∈ S, b i)).toConvexSpaceBody := by
  refine T.translate_rescale_le (∑ i ∈ S, v i) ?_ hδρ
  have h1 : ‖∑ i ∈ S, v i‖ ≤ ∑ i ∈ S, ‖v i‖ := norm_sum_le S v
  have h2 : ∑ i ∈ S, ‖v i‖ ≤ ∑ i ∈ S, (b i : ℝ) := Finset.sum_le_sum h_norm
  have h3 : ((∑ i ∈ S, b i : NNReal) : ℝ) = ∑ i ∈ S, (b i : ℝ) := by push_cast; rfl
  linarith

/-- Parameter lemma: for `s t u ∈ [0,1]` with `|t - s| ≥ 1 - 2ρ` and `0 ≤ ρ`,
there exists `λ ∈ [0,1]` such that the affine interpolation `(1-λ)s + λt` lies within
`2ρ` of `u`. -/
private lemma param_close {s t u ρ : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) (hu : u ∈ Set.Icc (0 : ℝ) 1)
    (hρ : 0 ≤ ρ) (hgap : 1 - 2 * ρ ≤ |t - s|) :
    ∃ lam ∈ Set.Icc (0:ℝ) 1, |(1 - lam) * s + lam * t - u| ≤ 2 * ρ := by
  obtain ⟨hs0, hs1⟩ := hs
  obtain ⟨ht0, ht1⟩ := ht
  obtain ⟨hu0, hu1⟩ := hu
  -- The gap hypothesis forces `min s t ≤ 2ρ` and `1 - 2ρ ≤ max s t`.
  have hbounds : min s t ≤ 2 * ρ ∧ 1 - 2 * ρ ≤ max s t := by
    rcases le_total s t with h | h
    · rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ t - s)] at hgap
      rw [min_eq_left h, max_eq_right h]; constructor <;> linarith
    · rw [abs_of_nonpos (by linarith : t - s ≤ 0)] at hgap
      rw [min_eq_right h, max_eq_left h]; constructor <;> linarith
  obtain ⟨hA, hB⟩ := hbounds
  have hAB : min s t ≤ max s t := min_le_max
  -- The witness is `u` clamped into `[min s t, max s t]`, which is the segment from `s` to `t`.
  obtain ⟨a, b, _, hb, hab, hveq⟩ : max (min s t) (min (max s t) u) ∈ segment ℝ s t := by
    rw [segment_eq_uIcc, Set.uIcc, Set.mem_Icc]
    exact ⟨le_max_left _ _, max_le hAB (min_le_left _ _)⟩
  simp only [smul_eq_mul] at hveq
  refine ⟨b, ⟨hb, by linarith⟩, ?_⟩
  rw [show (1:ℝ) - b = a from by linarith, hveq, abs_le]
  rcases le_total u (min s t) with h | h
  · rw [min_eq_right (h.trans hAB), max_eq_left h]; constructor <;> linarith
  · rcases le_total (max s t) u with h' | h'
    · rw [min_eq_left h', max_eq_right hAB]; constructor <;> linarith
    · rw [min_eq_right h', max_eq_right h]; constructor <;> linarith

omit [ProperSpace E] in
/-- Two points of the segment `[c,d]`, given by their affine parameters `x` and `y`, are at
distance `|x - y| * ‖d - c‖`. -/
private lemma norm_segment_param_sub (c d : E) (x y : ℝ) :
    ‖((1 - x) • c + x • d) - ((1 - y) • c + y • d)‖ = |x - y| * ‖d - c‖ := by
  rw [← Real.norm_eq_abs, ← norm_smul]
  congr 1
  simp only [sub_smul, smul_sub, one_smul]; abel

omit [ProperSpace E] in
/-- Geometric core: if every point of unit segment `[a,b]` is within `ρ` of unit
segment `[c,d]`, then every point of `[c,d]` is within `3ρ` of `[a,b]`. -/
lemma symm_hausdorff_segment {a b c d : E} (hab : ‖b - a‖ = 1) (hcd : ‖d - c‖ = 1)
    {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hclose : ∀ p ∈ segment ℝ a b, ∃ q ∈ segment ℝ c d, dist p q ≤ ρ) :
    ∀ z ∈ segment ℝ c d, ∃ w ∈ segment ℝ a b, dist z w ≤ 3 * ρ := by
  -- projections of `a` and `b` onto `[c,d]`, written through their parameters
  obtain ⟨pa, hpa_mem, hpa_le⟩ := hclose a (left_mem_segment ℝ a b)
  obtain ⟨pb, hpb_mem, hpb_le⟩ := hclose b (right_mem_segment ℝ a b)
  rw [segment_eq_image] at hpa_mem hpb_mem
  obtain ⟨s, hs_mem, hs_eq⟩ := hpa_mem
  obtain ⟨t, ht_mem, ht_eq⟩ := hpb_mem
  -- gap: `|t - s| ≥ 1 - 2ρ`, by the triangle inequality along `b → pb → pa → a`
  have hgap : 1 - 2 * ρ ≤ |t - s| := by
    have h4 := dist_triangle4 b pb pa a
    rw [dist_eq_norm b a, hab, dist_comm pa a, show dist pb pa = |t - s| from by
      rw [dist_eq_norm, ← hs_eq, ← ht_eq, norm_segment_param_sub, hcd, mul_one]] at h4
    linarith only [h4, hpa_le, hpb_le]
  rw [dist_eq_norm] at hpa_le hpb_le
  intro z hz
  rw [segment_eq_image] at hz
  obtain ⟨u, hu_mem, hu_eq⟩ := hz
  obtain ⟨lam, ⟨hlam0, hlam1⟩, hlam_bound⟩ := param_close hs_mem ht_mem hu_mem hρ hgap
  -- compare through the interpolated projection `r`
  set r : E := (1 - lam) • pa + lam • pb with hr
  have hwr_norm : ‖(1 - lam) • a + lam • b - r‖ ≤ ρ := by
    rw [hr, show (1 - lam) • a + lam • b - ((1 - lam) • pa + lam • pb)
        = (1 - lam) • (a - pa) + lam • (b - pb) from by
      rw [smul_sub, smul_sub, sub_add_sub_comm], ← mem_closedBall_zero_iff]
    exact convex_closedBall (0 : E) ρ (mem_closedBall_zero_iff.2 hpa_le)
      (mem_closedBall_zero_iff.2 hpb_le) (by linarith only [hlam1]) hlam0 (sub_add_cancel ..)
  have hrz_norm : ‖r - z‖ ≤ 2 * ρ := by
    rw [hr, ← hs_eq, ← ht_eq, ← hu_eq,
      show (1 - lam) • ((1 - s) • c + s • d) + lam • ((1 - t) • c + t • d)
        = (1 - ((1 - lam) * s + lam * t)) • c + ((1 - lam) * s + lam * t) • d from by module,
      norm_segment_param_sub, hcd, mul_one]
    exact hlam_bound
  refine ⟨(1 - lam) • a + lam • b,
    ⟨1 - lam, lam, by linarith only [hlam1], hlam0, sub_add_cancel .., rfl⟩,
    (dist_triangle z r _).trans ?_⟩
  rw [dist_eq_norm', dist_eq_norm']
  linarith only [hwr_norm, hrz_norm]

/-- Enlargement (GWZ-note Lemma 3.1, tube case): if a `σ₀`-tube `T₀` is contained in a
`σ`-tube `K`, then `K` is contained in the *concentric* `4σ`-rescale of `T₀` — same core
`[T₀.x, T₀.y]`, radius `4 * σ`, since `Tube.rescale` keeps the endpoints and only changes
the radius. No upper bound on `σ`, and no relation between `σ₀` and `σ`, is needed.

The constant `4` is absolute (in particular dimension-free) and splits as `3 + 1`:
the core of `T₀` is `σ`-close to the core of `K` (a tube contains its own core, and every
point of `K` is within `σ` of `K`'s core), `symm_hausdorff_segment` upgrades this one-sided
closeness of two unit segments to the reverse closeness at the cost of a factor `3`, and a
final triangle inequality crosses the radius `σ` of `K` once more, giving `3σ + σ = 4σ`.

The name is `le_rescale_of_subset`, not `le_rescale_of_le`, so as not to read as a variant of
the unrelated `Tube.le_rescale`, which enlarges a single tube's own radius. -/
theorem le_rescale_of_subset {σ₀ σ : NNReal} (T₀ : Tube σ₀ E) (K : Tube σ E)
    (h : (T₀.toConvexSpaceBody : ConvexSpaceBody E) ≤ K.toConvexSpaceBody) :
    (K.toConvexSpaceBody : ConvexSpaceBody E) ≤ (T₀.rescale (4 * σ)).toConvexSpaceBody := by
  -- the core of T₀ is σ-close to the core of K
  have hc : ∀ p ∈ segment ℝ T₀.x T₀.y, ∃ q ∈ segment ℝ K.x K.y, dist p q ≤ (σ : ℝ) := by
    intro p hp
    have hpcar : p ∈ T₀.carrier := by
      rw [T₀.carrier_eq]
      exact Set.mem_iUnion₂.mpr ⟨p, hp, Metric.mem_closedBall_self σ₀.coe_nonneg⟩
    have hpk : p ∈ K.carrier := h hpcar
    rw [K.carrier_eq] at hpk
    obtain ⟨q, hq, hpq⟩ := Set.mem_iUnion₂.mp hpk
    rw [Metric.mem_closedBall] at hpq
    exact ⟨q, hq, hpq⟩
  -- reverse closeness via symm_hausdorff_segment
  have hrev : ∀ z ∈ segment ℝ K.x K.y, ∃ w ∈ segment ℝ T₀.x T₀.y,
      dist z w ≤ 3 * (σ : ℝ) :=
    symm_hausdorff_segment T₀.norm_direction K.norm_direction (NNReal.coe_nonneg σ) hc
  -- final triangle inequality across K's radius σ
  intro v hv
  change v ∈ K.carrier at hv
  rw [K.carrier_eq] at hv
  obtain ⟨z, hz, hv_z⟩ := Set.mem_iUnion₂.mp hv
  rw [Metric.mem_closedBall] at hv_z
  obtain ⟨w, hw, hzw⟩ := hrev z hz
  have hss : ((4 * σ : NNReal) : ℝ) = 4 * (σ : ℝ) := by
    rw [NNReal.coe_mul]
    norm_num
  have hvwr : dist v w ≤ ((4 * σ : NNReal) : ℝ) := by
    calc
      dist v w ≤ dist v z + dist z w := dist_triangle v z w
      _ ≤ (σ : ℝ) + 3 * (σ : ℝ) := add_le_add hv_z hzw
      _ = 4 * (σ : ℝ) := by ring
      _ = ((4 * σ : NNReal) : ℝ) := hss.symm
  exact Set.mem_iUnion₂.mpr ⟨w, hw, Metric.mem_closedBall.mpr hvwr⟩

/-- General form: if a `δ'`-tube `T_in` is contained in an arbitrary `ρ'`-tube
`P` (not necessarily a rescaling of a `δ'`-tube), then `P` is contained in the
`4ρ'`-rescaling of `T_in`.  This is `Tube.le_rescale_of_subset` read in an inner-product
space; the statement needs no inner product and is proved in that generality just above. -/
theorem rescale_le_of_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {δ' ρ' : NNReal} (T_in : Tube δ' E) (P : Tube ρ' E)
    (hsub : T_in.toConvexSpaceBody ≤ P.toConvexSpaceBody) :
    P.toConvexSpaceBody ≤ (T_in.rescale (4 * ρ')).toConvexSpaceBody :=
  le_rescale_of_subset T_in P hsub

/-- Segment-Hausdorff symmetry for tubes: if a `δ'`-tube `T_in` sits inside the `ρ'`-rescale of
another `δ'`-tube `T_out` (with `δ' ≤ ρ'`), then the `ρ'`-rescale of `T_out` sits inside the
`(4·ρ')`-rescale of `T_in`.  The constant `4` is dimension-independent (any `C ≥ 3` works). -/
theorem rescale_le_rescale_of_le_rescale
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {δ' ρ' : NNReal} (T_in T_out : Tube δ' E)
    (hsub : T_in.toConvexSpaceBody ≤ (T_out.rescale ρ').toConvexSpaceBody) :
    (T_out.rescale ρ').toConvexSpaceBody ≤ (T_in.rescale (4 * ρ')).toConvexSpaceBody :=
  rescale_le_of_le T_in (T_out.rescale ρ') hsub

/-- If the endpoints of two tubes are close in the `L¹` metric, then a thin rescaling of the
first sits inside a correspondingly fatter rescaling of the second.  The only geometric input
is that a tube is the `cthickening` of the segment joining its endpoints, and that
`‖(a • x₁ + b • y₁) - (a • x₂ + b • y₂)‖ ≤ ‖x₁ - x₂‖ + ‖y₁ - y₂‖` on a segment. -/
theorem rescale_le_rescale_of_endpoint_dist
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {δ₁ δ₂ : NNReal} (A : Tube δ₁ E) (B : Tube δ₂ E)
    {τ θ : NNReal} (h : ‖A.x - B.x‖ + ‖A.y - B.y‖ + (τ : ℝ) ≤ (θ : ℝ)) :
    (A.rescale τ).toConvexSpaceBody ≤ (B.rescale θ).toConvexSpaceBody := by
  set L := ‖A.x - B.x‖ + ‖A.y - B.y‖ with hL_def
  have hL_nonneg : 0 ≤ L := by positivity
  have hseg_sub : segment ℝ A.x A.y ⊆ Metric.cthickening L (segment ℝ B.x B.y) := by
    rintro _ ⟨a, b, ha, hb, hab, rfl⟩
    refine Metric.mem_cthickening_of_dist_le _ (a • B.x + b • B.y) _ _
      ⟨a, b, ha, hb, hab, rfl⟩ ?_
    have hnorm := norm_add_le (a • (A.x - B.x)) (b • (A.y - B.y))
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg ha, abs_of_nonneg hb] at hnorm
    rw [dist_eq_norm, show a • A.x + b • A.y - (a • B.x + b • B.y)
        = a • (A.x - B.x) + b • (A.y - B.y) from by
      rw [smul_sub, smul_sub, add_sub_add_comm]]
    linarith [mul_le_mul_of_nonneg_right (show a ≤ 1 by linarith) (norm_nonneg (A.x - B.x)),
      mul_le_mul_of_nonneg_right (show b ≤ 1 by linarith) (norm_nonneg (A.y - B.y))]
  change (A.rescale τ).carrier ⊆ (B.rescale θ).carrier
  rw [(A.rescale τ).carrier_eq_cthickening, (B.rescale θ).carrier_eq_cthickening]
  exact ((Metric.cthickening_subset_of_subset _ hseg_sub).trans
    (Metric.cthickening_cthickening_subset τ.coe_nonneg hL_nonneg _)).trans
    (Metric.cthickening_mono (by linarith) _)

/-- **Rescaling respects containment, at the price of adding a radius.**  If `A ⊆ B` as convex
bodies, then `A^{(σ)} ⊆ B^{(θ)}` for every `θ ≥ δ_B + σ`.  The `δ_B` is unavoidable: `B^{(θ)}` is
`B` thickened by `θ - δ_B`, so absorbing a `σ`-thickening of `A ⊆ B` costs exactly that much. -/
theorem rescale_le_rescale_of_body_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {δ₁ δ₂ : NNReal} (A : Tube δ₁ E) (B : Tube δ₂ E)
    {σ θ : NNReal} (hδσ : δ₁ ≤ σ) (hθ : δ₂ + σ ≤ θ)
    (h : A.toConvexSpaceBody ≤ B.toConvexSpaceBody) :
    (A.rescale σ).toConvexSpaceBody ≤ (B.rescale θ).toConvexSpaceBody := by
  have hδ₂θ : δ₂ ≤ θ := le_self_add.trans hθ
  have h_rad : (σ : ℝ) - (δ₁ : ℝ) ≤ (θ : ℝ) - (δ₂ : ℝ) := by
    have hδσ' : (δ₁ : ℝ) ≤ (σ : ℝ) := by exact mod_cast hδσ
    have hθ' : (δ₂ : ℝ) + (σ : ℝ) ≤ (θ : ℝ) := by exact mod_cast hθ
    linarith [δ₁.coe_nonneg]
  calc
    (A.rescale σ).toConvexSpaceBody
        = A.toConvexSpaceBody.cthickening ((σ : ℝ) - (δ₁ : ℝ)) :=
      (A.toConvexBody_cthickening_sub hδσ).symm
    _ ≤ A.toConvexSpaceBody.cthickening ((θ : ℝ) - (δ₂ : ℝ)) := by
      apply SetLike.coe_subset_coe.mp
      dsimp [ConvexSpaceBody.cthickening]
      exact Metric.cthickening_mono h_rad (A.toConvexSpaceBody : Set E)
    _ ≤ B.toConvexSpaceBody.cthickening ((θ : ℝ) - (δ₂ : ℝ)) :=
      ConvexSpaceBody.cthickening_mono ((θ : ℝ) - (δ₂ : ℝ)) h
    _ = (B.rescale θ).toConvexSpaceBody :=
      B.toConvexBody_cthickening_sub hδ₂θ

-- Let `E` be a nontrivial finite dimensional Euclidean space.
variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
theorem le_ethickness_zero (T : Tube δ E) : 1/2 ≤ ethickness ℝ T.carrier 0 := by
  rw [Metric.le_ethickness_iff]
  intro r' A hA hsub
  have hmem : ∀ z ∈ segment ℝ T.x T.y, z ∈ T.carrier := fun z hz =>
    T.carrier_eq ▸ Set.mem_iUnion₂.mpr ⟨z, hz, Metric.mem_closedBall_self δ.coe_nonneg⟩
  have hbot : (A.direction : Submodule ℝ E) = ⊥ :=
    Submodule.rank_eq_zero.mp (le_antisymm hA zero_le)
  have hsubs : (A : Set E).Subsingleton := fun p hp q hq =>
    vsub_eq_zero_iff_eq.mp (by
      have := (AffineSubspace.vsub_left_mem_direction_iff_mem hp q).mpr hq
      rwa [hbot, Submodule.mem_bot] at this)
  obtain hempty | ⟨a, hsing⟩ := hsubs.eq_empty_or_singleton
  · rw [hempty, Metric.cthickening_empty] at hsub
    exact (hsub (hmem _ (left_mem_segment ℝ T.x T.y))).elim
  rw [hsing, Metric.cthickening_singleton a r'.coe_nonneg] at hsub
  have hx := Metric.mem_closedBall.mp (hsub (hmem _ (left_mem_segment ℝ T.x T.y)))
  have hy := Metric.mem_closedBall.mp (hsub (hmem _ (right_mem_segment ℝ T.x T.y)))
  have htri := dist_triangle T.x a T.y
  rw [T.dist_eq_one, dist_comm a T.y] at htri
  rw [show (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2) by simp, ← ENNReal.ofReal_coe_nnreal]
  exact ENNReal.ofReal_le_ofReal (by linarith)

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
theorem ethickness_zero_le (T : Tube δ E) : ethickness ℝ T.carrier 0 ≤ 1 + δ := by
  have hsub : T.carrier ⊆ Metric.closedBall T.x ((1 + δ : NNReal) : ℝ) := by
    rw [T.carrier_eq_cthickening, NNReal.coe_add, NNReal.coe_one, add_comm (1 : ℝ),
      ← cthickening_closedBall δ.coe_nonneg zero_le_one T.x]
    exact cthickening_subset_of_subset _ ((convex_closedBall T.x 1).segment_subset
      (mem_closedBall_self zero_le_one) (by rw [mem_closedBall, dist_comm, T.dist_eq_one]))
  simpa [ENNReal.coe_add] using
    Metric.ethickness_le_of_subset_closedBall (𝕜 := ℝ) (1 + δ) hsub 0

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
theorem ethickness_zero_le_two (hδ : δ ≤ 1) (T : Tube δ E) : ethickness ℝ T.carrier 0 ≤ 2 := by
  apply T.ethickness_zero_le.trans
  rw [← one_add_one_eq_two]
  gcongr
  exact coe_le_one_iff.mpr hδ

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
theorem ethickness_one_le (T : Tube δ E) : ethickness ℝ T.carrier 1 ≤ δ := by
  rw [T.carrier_eq_cthickening]
  refine Metric.ethickness_le_of_cthickening (A := affineSpan ℝ ({T.x, T.y} : Set E)) δ ?_
    (Metric.cthickening_subset_of_subset δ
      ((affineSpan ℝ ({T.x, T.y} : Set E)).convex.segment_subset
        (subset_affineSpan ℝ _ (by simp)) (subset_affineSpan ℝ _ (by simp))))
  rw [direction_affineSpan, vectorSpan_pair]
  simpa using rank_span_le ({T.x - T.y} : Set E)

omit [MeasurableSpace E] [BorelSpace E] in
theorem le_ethickness_finrank_sub_one (T : Tube δ E) :
    δ ≤ ethickness ℝ T.carrier (Module.finrank ℝ E - 1) := by
  have h := le_ethickness_cthickening (V := E) (E := E) ⟨T.x, left_mem_segment ℝ T.x T.y⟩
    (ρ := (δ : ℝ)) (n := Module.finrank ℝ E - 1)
    (Nat.sub_lt (Module.finrank_pos (R := ℝ) (M := E)) one_pos)
  rw [← T.carrier_eq_cthickening, ENNReal.ofReal_coe_nnreal] at h
  exact (self_le_add_left _ _).trans h

omit [MeasurableSpace E] [BorelSpace E] in
/-- The smallest affine thickness of a `δ`-tube is at least `δ`. Repackaging of
`Tube.le_ethickness_finrank_sub_one` in the form consumed by the discretization results, whose
thickness hypothesis is phrased with `Metric.ethickness.scale`. -/
theorem le_ethickness_scale (T : Tube δ E) :
    (δ : ENNReal) ≤ Metric.ethickness.scale ℝ T.carrier := by
  rw [Metric.ethickness.scale_eq]
  exact T.le_ethickness_finrank_sub_one

/-- The constant in `Tube.le_volume`, depending only on the dimension -/
@[nolint defsWithUnderscore]
noncomputable abbrev le_volume.c (n : ℕ) : NNReal :=
  ⟨Real.sqrt Real.pi ^ n / Real.Gamma (n / 2 + 1) / 3, by positivity⟩

theorem le_volume.c_pos (n : ℕ) : 0 < le_volume.c n := by
  rw [← NNReal.coe_pos]
  change (0 : ℝ) < Real.sqrt Real.pi ^ n / Real.Gamma (n / 2 + 1) / 3
  positivity

theorem le_volume.c_one_le_one : le_volume.c 1 ≤ 1 := by
  rw [← NNReal.coe_le_coe, NNReal.coe_one]
  change Real.sqrt Real.pi ^ 1 / Real.Gamma (((1 : ℕ) : ℝ) / 2 + 1) / 3 ≤ 1
  rw [Nat.cast_one, pow_one, Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
  have hpi : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  rw [mul_comm (1 / 2 : ℝ), ← div_div, div_self (ne_of_gt hpi)]
  norm_num

omit [Nontrivial E] in
theorem one_le_volume_of_dim_one (h : Module.finrank ℝ E = 1) {δ : NNReal} (T : Tube δ E) :
    1 ≤ volume T.carrier := by
  have hv0 : T.y - T.x ≠ 0 :=
    norm_ne_zero_iff.mp (by rw [T.norm_direction]; exact one_ne_zero)
  have hsub : Metric.closedBall (T.x + (1 / 2 : ℝ) • (T.y - T.x)) (1 / 2 : ℝ) ⊆ T.carrier := by
    intro w hw
    obtain ⟨t, ht⟩ := (finrank_eq_one_iff_of_nonzero' (T.y - T.x) hv0).mp h
      (w - (T.x + (1 / 2 : ℝ) • (T.y - T.x)))
    rw [Metric.mem_closedBall, dist_eq_norm, ← ht, norm_smul, T.norm_direction, mul_one,
      Real.norm_eq_abs, abs_le] at hw
    obtain ⟨ht_ge, ht_le⟩ := hw
    rw [T.carrier_eq]
    refine Set.mem_iUnion₂.mpr ⟨w, ⟨1 / 2 - t, 1 / 2 + t, by linarith, by linarith, by ring, ?_⟩,
      Metric.mem_closedBall_self δ.coe_nonneg⟩
    rw [sub_eq_iff_eq_add.mp ht.symm]
    module
  refine le_trans ?_ (measure_mono hsub)
  rw [InnerProductSpace.volume_closedBall_of_dim_odd (k := 0) (by simpa using h) _ (1 / 2 : ℝ), h,
    pow_one, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  norm_num [Nat.doubleFactorial]

lemma Nat.sub_one_eq_zero {n : ℕ} (hn' : 0 < n) (hn : n - 1 = 0) : n = 1 := by omega

namespace BallVolume

/-- The volume of the unit ball of `ℝⁿ`, as the closed form `π^{n/2} / Γ(n/2 + 1)`. -/
noncomputable abbrev V (n : ℕ) := Real.sqrt Real.pi ^ n / Real.Gamma (n / 2 + 1)

lemma V_pos (n : ℕ) : 0 < V n := by positivity

lemma V_eq (n : ℕ) : V n = 3 * le_volume.c n :=
  mul_div_cancel₀ _ (NeZero.ne' 3).symm |>.symm

lemma c_eq (n : ℕ) : le_volume.c n = V n / 3 := by
  rw [V_eq, mul_div_cancel_left₀ _ (NeZero.ne' 3).symm]

lemma k_mul_eq_volume {δ : NNReal} (T : Tube δ E) (n k : ℕ) (z : ℕ → E)
    (hδ1 : 0 < (δ : ℝ)) (hn : n = Module.finrank ℝ E)
    (hz : z = fun i : ℕ ↦ T.x + ((3 * (δ : ℝ)) * (i : ℝ)) • (T.y - T.x)) :
    (k : ℝ≥0∞) * ((ENNReal.ofReal (δ : ℝ)) ^ n * ENNReal.ofReal (V n))
    = volume (⋃ i ∈ Finset.range k, Metric.closedBall (z i) (δ : ℝ)) := by
  rw [measure_biUnion_finset
    (fun i _ j _ hij => Metric.closedBall_disjoint_closedBall (by
      have h1 : (1 : ℝ) ≤ |(i : ℝ) - (j : ℝ)| := by
        exact_mod_cast Int.one_le_abs (sub_ne_zero.mpr
          (show (i : ℤ) ≠ j from by exact_mod_cast hij))
      rw [dist_eq_norm,
        show z i - z j = (3 * (δ : ℝ) * ((i : ℝ) - j)) • (T.y - T.x) from by
          simp only [hz]; module,
        norm_smul, T.norm_direction, mul_one, Real.norm_eq_abs, abs_mul,
        abs_of_pos (mul_pos three_pos hδ1)]
      linarith [mul_le_mul_of_nonneg_left h1 (mul_pos three_pos hδ1).le]))
    (fun i _ => Metric.isClosed_closedBall.measurableSet)]
  simp_rw [InnerProductSpace.volume_closedBall,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, hn]

end BallVolume

open BallVolume in
/-- Each δ-tube has volume at least `c · δ ^ (n-1)` for a uniform constant `c > 0`
    depending only on the dimension. -/
theorem le_volume {δ : NNReal} (T : Tube δ E) :
    le_volume.c (Module.finrank ℝ E) * δ ^ (Module.finrank ℝ E - 1) ≤ volume T.carrier := by
  set n := Module.finrank ℝ E with hn_def
  have hn : 0 < n := Module.finrank_pos
  if hn₁ : n = 1 then
  simp only [hn₁, tsub_self, pow_zero, mul_one]
  exact (coe_le_one_iff.mpr le_volume.c_one_le_one).trans (one_le_volume_of_dim_one hn₁ T) else
  if hδ : δ = 0 then simp [hδ, zero_pow (fun h ↦ hn₁ (Nat.sub_one_eq_zero hn h) : n - 1 ≠ 0)] else
  have hδr : (0 : ℝ) < (δ : ℝ) := NNReal.coe_pos.mpr (zero_lt_iff.mpr hδ)
  have h3δ : (0 : ℝ) < 3 * (δ : ℝ) := by linarith only [hδr]
  set k : ℕ := ⌊(1 : ℝ) / (3 * (δ : ℝ))⌋₊ + 1 with k_eq
  set z : ℕ → E := fun i => T.x + ((3 * (δ : ℝ)) * (i : ℝ)) • (T.y - T.x) with hz
  -- the `k` balls of radius `δ` centred along the core at spacing `3δ` all lie inside the tube
  have hsub : ∀ i ∈ Finset.range k, Metric.closedBall (z i) (δ : ℝ) ⊆ T.carrier := by
    refine fun i hi p hp ↦ T.carrier_eq ▸ ?_
    have hi : (3 * (δ : ℝ)) * (i : ℝ) ≤ 1 := by
      rw [mul_comm, ← le_div_iff₀ h3δ]
      exact (Nat.cast_le.mpr (Nat.lt_succ_iff.1 (Finset.mem_range.mp hi))).trans
        (Nat.floor_le (div_nonneg zero_le_one h3δ.le))
    exact Set.mem_iUnion₂.mpr ⟨z i, ⟨1 - 3 * (δ : ℝ) * i, 3 * (δ : ℝ) * i, by linarith only [hi],
      mul_nonneg h3δ.le (Nat.cast_nonneg i), sub_add_cancel .., by module⟩, hp⟩
  -- `k ≥ 1 / (3δ)`, so `k · δⁿ · V n ≥ (V n / 3) · δ ^ (n - 1) = c n · δ ^ (n - 1)`
  refine le_trans ?_ ((k_mul_eq_volume T n k z hδr hn_def hz).trans_le
    (measure_mono (Set.iUnion₂_subset hsub)))
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_coe_nnreal,
    ← ENNReal.ofReal_pow hδr.le, ← ENNReal.ofReal_mul (NNReal.coe_nonneg _),
    ← ENNReal.ofReal_pow hδr.le, ← ENNReal.ofReal_natCast k,
    ← ENNReal.ofReal_mul (pow_nonneg hδr.le n), ← ENNReal.ofReal_mul (Nat.cast_nonneg k)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [c_eq, pow_sub₀ _ hδr.ne' hn, pow_one,
    show V n / 3 * ((δ : ℝ) ^ n * (δ : ℝ)⁻¹) = 1 / (3 * δ) * ((δ : ℝ) ^ n * V n) from by ring]
  exact mul_le_mul_of_nonneg_right (Nat.lt_succ_floor _).le
    (mul_nonneg (pow_nonneg hδr.le n) (V_pos n).le)

/-- The dimensional constant in `Tube.volume_le`. -/
@[nolint defsWithUnderscore]
noncomputable abbrev volume_le.C (n : ℕ) : NNReal := 2 ^ (n + 1)

/-- The dimensional constant in `Tube.volume_le` is positive. -/
theorem volume_le.C_pos (n : ℕ) : 0 < volume_le.C n := by
  unfold volume_le.C
  positivity

/-- **Volume upper bound for a tube of any bounded scale.**  An `r`-tube whose scale is bounded by
`b` has volume at most `2 ^ n * (1 + b) * r ^ (n - 1)`, with `n` the ambient dimension.  This is the
flag-box estimate `volume_le_prod_ethickness`: the axial direction contributes `1 + r ≤ 1 + b` and
every other direction contributes `r`.  The instance `b = 1` is `volume_le`; the bound is stated for
general `b` because the fattened scales `3 * ρ k` of GWZ Lemma 7.5 exceed `1`. -/
lemma volume_le_of_le {r b : NNReal} (hrb : r ≤ b) (T : Tube r E) :
    volume T.carrier
      ≤ (((2 : NNReal) ^ Module.finrank ℝ E * (1 + b)
            * r ^ (Module.finrank ℝ E - 1) : NNReal) : ENNReal) := by
  set n := Module.finrank ℝ E
  have htail : ∏ i ∈ Finset.range (n - 1), ethickness ℝ T.carrier (i + 1)
      ≤ (r : ENNReal) ^ (n - 1) := by
    rw [show (r : ENNReal) ^ (n - 1) = ∏ _i ∈ Finset.range (n - 1), (r : ENNReal) by simp]
    exact Finset.prod_le_prod' fun i _ =>
      (ethickness_antitone (Nat.le_add_left 1 i)).trans T.ethickness_one_le
  have hprod : ∏ i ∈ Finset.range n, ethickness ℝ T.carrier i
      ≤ (1 + b : ENNReal) * (r : ENNReal) ^ (n - 1) := by
    conv_lhs => rw [show n = (n - 1) + 1 from (Nat.sub_add_cancel Module.finrank_pos).symm,
      Finset.prod_range_succ']
    exact (mul_comm _ _).trans_le
      (mul_le_mul' (T.ethickness_zero_le.trans (by gcongr)) htail)
  refine (volume_le_prod_ethickness T.carrier).trans ?_
  rw [show (((2 : NNReal) ^ n * (1 + b) * r ^ (n - 1) : NNReal) : ENNReal)
      = (2 : ℝ≥0∞) ^ n * ((1 + b : ENNReal) * (r : ENNReal) ^ (n - 1)) by push_cast; ring]
  gcongr

/-- Each δ-tube has volume at most `M · δ ^ (n-1)` for a uniform constant `M > 0`
    depending only on the dimension, provided `δ ≤ 1`.  The instance `b = 1` of
    `volume_le_of_le`, whose `2 ^ n * (1 + 1)` is exactly `volume_le.C n`. -/
lemma volume_le {δ : NNReal} (hδ : δ ≤ 1) (T : Tube δ E) :
      volume T.carrier ≤ (volume_le.C (Module.finrank ℝ E) * δ ^ (Module.finrank ℝ E - 1)) :=
  (volume_le_of_le hδ T).trans_eq (by unfold volume_le.C; push_cast; ring)

lemma half_le_radius_of_subset_ball
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {δ : NNReal} (hδ : 0 < δ) {r : ℝ} (T : Tube δ E)
    (hT : T.carrier ⊆ Metric.closedBall (0 : E) r) : (1 : ℝ) / 2 ≤ r := by
  have hmem : ∀ z ∈ segment ℝ T.x T.y, dist z 0 ≤ r := fun z hz =>
    hT (T.carrier_eq ▸ Set.mem_biUnion hz
      (Metric.mem_closedBall_self (NNReal.coe_pos.mpr hδ).le))
  have h2 := dist_triangle_right T.x T.y (0 : E)
  rw [T.dist_eq_one] at h2
  linarith [hmem _ (left_mem_segment ℝ T.x T.y), hmem _ (right_mem_segment ℝ T.x T.y)]

/-- Geometric containment: if a δ-tube `T` lies inside the unit ball `B(0, r)`,
and a wider ρ-tube `t` contains the carrier of `T`, then `t.carrier ⊆ B(0, r + 1 + 2ρ)`.
-/
lemma subset_ball_of_carrier_subset_ball
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {δ ρ : NNReal} {r : ℝ} (hδ : 0 < δ) (_hρ : 0 < ρ)
    (T : Tube δ E) (t : Tube ρ E)
    (h_T_ball : T.carrier ⊆ Metric.closedBall (0 : E) r)
    (h_cover : T.carrier ⊆ t.carrier) :
    t.carrier ⊆ Metric.closedBall (0 : E) (r + 1 + 2 * (ρ : ℝ)) := by
  have hTx_mem : T.x ∈ T.carrier := by
    rw [T.carrier_eq]
    exact Set.mem_iUnion₂.mpr ⟨T.x, left_mem_segment ℝ T.x T.y,
      Metric.mem_closedBall_self (NNReal.coe_pos.mpr hδ).le⟩
  have hTx_norm : dist T.x 0 ≤ r := h_T_ball hTx_mem
  obtain ⟨z, hz_seg, hTxz⟩ := Set.mem_iUnion₂.mp (t.carrier_eq ▸ h_cover hTx_mem)
  rw [Metric.mem_closedBall] at hTxz
  have hz_norm : dist z 0 ≤ r + (ρ : ℝ) := by
    have := dist_triangle z T.x 0
    rw [dist_comm z T.x] at this
    linarith
  -- the core segment of `t` has unit length, so `z` is within `1` of both endpoints
  have htx_norm : dist t.x 0 ≤ r + (ρ : ℝ) + 1 := by
    have h1 : dist z t.x ≤ 1 := (convex_closedBall t.x (1 : ℝ)).segment_subset
      (Metric.mem_closedBall_self zero_le_one)
      (by rw [Metric.mem_closedBall, dist_comm]; exact t.dist_eq_one.le) hz_seg
    have h2 := dist_triangle t.x z 0
    rw [dist_comm t.x z] at h2
    linarith
  have hty_norm : dist t.y 0 ≤ r + (ρ : ℝ) + 1 := by
    have h1 : dist z t.y ≤ 1 := (convex_closedBall t.y (1 : ℝ)).segment_subset
      (by rw [Metric.mem_closedBall]; exact t.dist_eq_one.le)
      (Metric.mem_closedBall_self zero_le_one) hz_seg
    have h2 := dist_triangle t.y z 0
    rw [dist_comm t.y z] at h2
    linarith
  have hrad_nn : (0 : ℝ) ≤ r + (ρ : ℝ) + 1 := dist_nonneg.trans htx_norm
  refine t.carrier_eq_cthickening.le.trans ?_
  calc Metric.cthickening (ρ : ℝ) (segment ℝ t.x t.y)
      ⊆ Metric.cthickening (ρ : ℝ) (Metric.cthickening (r + (ρ : ℝ) + 1) ({0} : Set E)) := by
        rw [Metric.cthickening_singleton _ hrad_nn]
        exact Metric.cthickening_subset_of_subset _
          ((convex_closedBall (0 : E) _).segment_subset htx_norm hty_norm)
    _ ⊆ Metric.cthickening ((ρ : ℝ) + (r + (ρ : ℝ) + 1)) ({0} : Set E) :=
        Metric.cthickening_cthickening_subset ρ.coe_nonneg hrad_nn _
    _ = Metric.closedBall (0 : E) (r + 1 + 2 * (ρ : ℝ)) := by
        rw [show (ρ : ℝ) + (r + (ρ : ℝ) + 1) = r + 1 + 2 * (ρ : ℝ) from by ring]
        exact Metric.cthickening_singleton _ (by linarith [ρ.coe_nonneg])

/-- The midpoint of the core segment of a tube. -/
noncomputable abbrev midpoint (T : Tube δ E) : E := (1/2 : ℝ) • (T.x + T.y)

/-- The canonical tube with prescribed midpoint `m` and unit direction `u`. -/
@[simps!]
noncomputable def ofMidpointDirection
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    (δ : NNReal) (m u : E) (hu : ‖u‖ = 1) : Tube δ E :=
  Tube.mk' δ (x := m - (1 / 2 : ℝ) • u) (y := m + (1 / 2 : ℝ) • u) (by
    rw [dist_eq_norm, show (m - (1 / 2 : ℝ) • u) - (m + (1 / 2 : ℝ) • u) = -u from by module,
      norm_neg, hu])

lemma midpoint_mem_carrier
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [Nontrivial E] [ProperSpace E]
    {δ : NNReal} (hδ : 0 < δ) (T : Tube δ E) : T.midpoint ∈ T.carrier := by
  rw [T.carrier_eq, show T.midpoint = _root_.midpoint ℝ T.x T.y from by
    rw [midpoint_eq_smul_add]; norm_num]
  exact Set.mem_iUnion₂.mpr ⟨_, midpoint_mem_segment ..,
    Metric.mem_closedBall_self (NNReal.coe_pos.mpr hδ).le⟩

lemma midpoint_mem_closedBall_of_subset
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [Nontrivial E] [ProperSpace E]
    {δ : NNReal} (hδ : 0 < δ) {r : ℝ} (T : Tube δ E)
    (hT : T.carrier ⊆ Metric.closedBall (0 : E) r) :
    T.midpoint ∈ Metric.closedBall (0 : E) r :=
  hT (midpoint_mem_carrier hδ T)

lemma norm_midpoint_le_of_subset_ball
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [Nontrivial E] [ProperSpace E]
    {δ : NNReal} (hδ : 0 < δ) {r : ℝ} (T : Tube δ E)
    (hT : T.carrier ⊆ Metric.closedBall (0 : E) r) :
    ‖T.midpoint‖ ≤ r := by
  have h := midpoint_mem_closedBall_of_subset hδ T hT
  rw [Metric.mem_closedBall, dist_zero_right] at h
  exact h

/-- **A centred tube** (refined proof l.4851–4855): writing an exact tube as
`{o + t d : |t| ≤ 1/2} + B̄(0, r)` with `‖d‖ = 1`, it is *centred* when `o · d = 0` — the midpoint of the core is the
foot of the perpendicular from the origin to the core's supporting line.  In the source's words, this "removes the
otherwise uncontrolled axial slide of the core along its supporting line": it is the fifth, axial line parameter
(l.156–160) being fixed, and it is the stated hypothesis under which the coarse levels of a threaded tower may be
chosen line-essentially distinct at an absolute constant (l.4900–4901).  The caller of the very-not-sticky estimate
performs this normalisation before building the tower (l.6003–6013).

The binder `[FiniteDimensional ℝ E]` is a genuine elaboration need, not instance-matching with the neighbouring lemmas:
`Tube.midpoint` (`abbrev`, this file, under the section's `variable`s) takes that instance as an argument, so without it
`T.midpoint` fails with `failed to synthesize FiniteDimensional ℝ E`. -/
def IsCentred {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [ProperSpace E] {δ : NNReal} (T : Tube δ E) : Prop :=
  inner ℝ T.midpoint T.direction = (0 : ℝ)

section Reverse

variable
  {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  {δ : NNReal}

/-- Reverse the orientation of a δ-tube by swapping its endpoints `x` and
`y`. The underlying carrier is unchanged, so `reverse` is a purely
notational tool for picking an orientation. -/
def reverse (T : Tube δ E) : Tube δ E where
  toConvexSpaceBody := T.toConvexSpaceBody
  x := T.y
  y := T.x
  dist_eq_one := by rw [dist_comm]; exact T.dist_eq_one
  carrier_eq := by
    rw [T.carrier_eq, segment_symm]

@[simp]
lemma reverse_carrier (T : Tube δ E) : T.reverse.carrier = T.carrier := rfl

@[simp]
lemma reverse_x (T : Tube δ E) : T.reverse.x = T.y := rfl

@[simp]
lemma reverse_y (T : Tube δ E) : T.reverse.y = T.x := rfl

@[simp]
lemma reverse_direction (T : Tube δ E) :
    T.reverse.direction = -T.direction := by
  change T.x - T.y = -(T.y - T.x)
  abel

@[simp]
lemma reverse_reverse (T : Tube δ E) : T.reverse.reverse = T := by
  cases T; rfl

/-- If `c` lies on the segment `[T.x, T.y]`, then the closed `δ`-ball around
`c` is contained in `T.carrier`. (When `δ ≤ 0` this is trivial via the
fact that `c ∈ T.carrier`.) -/
lemma closedBall_subset_carrier_of_mem_segment
    (T : Tube δ E) {c : E} (hc : c ∈ segment ℝ T.x T.y) :
    Metric.closedBall c δ ⊆ T.carrier := by
  rw [T.carrier_eq]
  exact Set.subset_iUnion₂ (s := fun z _ => Metric.closedBall z δ) c hc

end Reverse

section ReverseMidpoint

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E] [ProperSpace E]
  {δ : NNReal}

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
lemma reverse_midpoint (T : Tube δ E) :
    T.reverse.midpoint = T.midpoint := by
  change (1 / 2 : ℝ) • (T.y + T.x) = _; rw [add_comm]

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
/-- For `s ∈ [-1/2, 1/2]`, the point `T.midpoint + s • T.direction` lies on
the segment `[T.x, T.y]`. -/
lemma midpoint_add_smul_direction_mem_segment
    (T : Tube δ E) {s : ℝ} (hs_l : -(1 / 2 : ℝ) ≤ s) (hs_r : s ≤ 1 / 2) :
    T.midpoint + s • T.direction ∈ segment ℝ T.x T.y := by
  refine ⟨1 / 2 - s, 1 / 2 + s, sub_nonneg.mpr hs_r, neg_le_iff_add_nonneg'.mp hs_l, by ring, ?_⟩
  module

end ReverseMidpoint

section CarrierRep

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  {ι : Type*} [Nonempty ι] {δ : NNReal}

/-- The carrier-class representative map: `carrierRep s T i` is the index of `s` that
`Function.invFunOn` selects out of the carrier of `T i`.  Because it is a function of the
*carrier* rather than of the index, it is automatically constant on carrier classes; composing
an injectivity-requiring construction with it is how carrier-duplicate families are reduced to
carrier-injective ones. -/
noncomputable def carrierRep (s : Finset ι) (T : ι → Tube δ E) (i : ι) : ι :=
  Function.invFunOn (fun j => (T j).carrier) (s : Set ι) (T i).carrier

/-- The representative of an index of `s` again lies in `s`. -/
theorem carrierRep_mem {s : Finset ι} {T : ι → Tube δ E} {i : ι} (hi : i ∈ s) :
    carrierRep s T i ∈ s :=
  Finset.mem_coe.mp (Function.invFunOn_apply_mem (Finset.mem_coe.mpr hi))

/-- The representative carries the same carrier, hence (by `body_eq_of_carrier_eq`) the same
convex body. -/
theorem carrierRep_carrier {s : Finset ι} {T : ι → Tube δ E} {i : ι} (hi : i ∈ s) :
    (T (carrierRep s T i)).carrier = (T i).carrier :=
  Function.invFunOn_apply_eq (f := fun j => (T j).carrier) (Finset.mem_coe.mpr hi)

/-- `carrierRep` is constant on carrier classes: it depends on `i` only through `(T i).carrier`. -/
theorem carrierRep_eq_of_carrier_eq {s : Finset ι} {T : ι → Tube δ E} {i j : ι}
    (h : (T i).carrier = (T j).carrier) :
    carrierRep s T i = carrierRep s T j :=
  congrArg (Function.invFunOn (fun j => (T j).carrier) (s : Set ι)) h

/-- `carrierRep` is idempotent on `s`. -/
theorem carrierRep_idem {s : Finset ι} {T : ι → Tube δ E} {i : ι} (hi : i ∈ s) :
    carrierRep s T (carrierRep s T i) = carrierRep s T i :=
  carrierRep_eq_of_carrier_eq (carrierRep_carrier hi)

/-- The representative subfamily is a subset of `s`. -/
theorem carrierRep_image_subset {s : Finset ι} {T : ι → Tube δ E} [DecidableEq ι] :
    s.image (carrierRep s T) ⊆ s := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  exact carrierRep_mem hi

/-- **Carrier-injectivity on the representative subfamily.**  `s.image (carrierRep s T)`
hits each carrier class of `s` exactly once, so it satisfies the `Set.InjOn` hypothesis that
the multiscale tree builder requires. -/
theorem carrierRep_injOn_image {s : Finset ι} {T : ι → Tube δ E} [DecidableEq ι] :
    Set.InjOn (fun i => (T i).carrier) ((s.image (carrierRep s T) : Finset ι) : Set ι) := by
  intro a ha b hb hcarrier
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp ha)
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hb)
  rw [← carrierRep_idem hi, ← carrierRep_idem hj]
  exact carrierRep_eq_of_carrier_eq hcarrier

/-- Membership of a representative in the representative subfamily. -/
theorem carrierRep_mem_image {s : Finset ι} {T : ι → Tube δ E} {i : ι} [DecidableEq ι]
    (hi : i ∈ s) : carrierRep s T i ∈ s.image (carrierRep s T) :=
  Finset.mem_image.mpr ⟨i, hi, rfl⟩

/-- The representative subfamily is nonempty when `s` is. -/
theorem carrierRep_image_nonempty {s : Finset ι} {T : ι → Tube δ E} [DecidableEq ι]
    (hs : s.Nonempty) : (s.image (carrierRep s T)).Nonempty :=
  hs.image _

end CarrierRep

end Tube
end

/-!
# Tube metric and volume helpers
-/

@[expose] public section

open MeasureTheory ENNReal Metric


namespace Kakeya

variable
  (E : Type*)
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

namespace Tube

omit [MeasurableSpace E] [BorelSpace E] in
/-- A length-1 δ-tube `T` is contained in the closed ball of radius `1/2 + δ`
centered at the midpoint of its core line segment. -/
theorem carrier_subset_closedBall_midpoint
    {δ : NNReal} (T : Tube δ E) :
    T.carrier ⊆ Metric.closedBall (midpoint ℝ T.x T.y) (1 / 2 + (δ : ℝ)) := by
  rw [T.carrier_eq]
  refine Set.iUnion₂_subset fun z hz => Metric.closedBall_subset_closedBall' ?_
  have : dist z (midpoint ℝ T.x T.y) ≤ 1 / 2 :=
    (convex_closedBall (midpoint ℝ T.x T.y) (1 / 2 : ℝ)).segment_subset
      (by rw [Metric.mem_closedBall, dist_left_midpoint, T.dist_eq_one]; norm_num)
      (by rw [Metric.mem_closedBall, dist_right_midpoint, T.dist_eq_one]; norm_num) hz
  linarith

section ComparableThickness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
/-- The circumradius of a length-`1` `δ`-tube is at most `1/2 + δ`. -/
theorem ethickness_zero_le_half_add (T : Tube δ E) :
    Metric.ethickness ℝ T.carrier 0 ≤ ((1 / 2 + δ : NNReal) : ENNReal) :=
  Metric.ethickness_le_of_subset_closedBall (𝕜 := ℝ) (s := T.carrier)
    (x := midpoint ℝ T.x T.y) (1 / 2 + δ)
    (by simpa using Tube.carrier_subset_closedBall_midpoint (E := E) T) 0

omit [MeasurableSpace E] [BorelSpace E] in
/-- The middle thicknesses of a `δ`-tube are exactly `δ`. -/
theorem ethickness_eq_of_one_le (T : Tube δ E) {n : ℕ} (hn1 : 1 ≤ n)
    (hn : n < Module.finrank ℝ E) : Metric.ethickness ℝ T.carrier n = (δ : ENNReal) := by
  have hneq : T.x ≠ T.y := by
    intro h
    have : dist T.x T.y = 0 := by rw [h]; exact dist_self _
    rw [T.dist_eq_one] at this
    norm_num at this
  haveI : Nontrivial E := ⟨T.x, T.y, hneq⟩
  apply le_antisymm
  · exact (Metric.ethickness_antitone hn1).trans T.ethickness_one_le
  · exact T.le_ethickness_finrank_sub_one.trans
      (Metric.ethickness_antitone (Nat.le_sub_one_of_lt hn))

omit [MeasurableSpace E] [BorelSpace E] in
/-- Two `δ`-tubes have `2`-comparable thickness sequences when `δ ≤ 1/2`. -/
theorem thickness_le_two_mul_thickness (hδ : (δ : ℝ) ≤ 1 / 2) (T T' : Tube δ E) (n : ℕ) :
    Metric.thickness ℝ T.carrier n ≤ 2 * Metric.thickness ℝ T'.carrier n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · have hδle1 : (1 / 2 + δ : NNReal) ≤ 1 := by
      rw [← NNReal.coe_le_coe]
      push_cast
      linarith [hδ]
    have htrT : ENNReal.toReal (Metric.ethickness ℝ T.carrier 0) ≤ (1 : ℝ) := by
      calc
        ENNReal.toReal (Metric.ethickness ℝ T.carrier 0)
            ≤ ENNReal.toReal ((1 / 2 + δ : NNReal) : ENNReal) := by
          exact ENNReal.toReal_mono (by simp) (ethickness_zero_le_half_add T)
        _ ≤ ENNReal.toReal (1 : ENNReal) := by
          exact ENNReal.toReal_mono (by simp) (by exact_mod_cast hδle1)
        _ = (1 : ℝ) := by simp
    let hbddT : Bornology.IsBounded T.carrier := T.isCompact.isBounded
    have hbridge0 : Metric.thickness ℝ T.carrier 0 =
        ENNReal.toReal (Metric.ethickness ℝ T.carrier 0) :=
      (Metric.toReal_ethickness hbddT 0).symm
    have htopT : Metric.thickness ℝ T.carrier 0 ≤ 1 := by
      rw [hbridge0]
      exact htrT
    let hbddT' : Bornology.IsBounded T'.carrier := T'.isCompact.isBounded
    have hbridge0' : Metric.thickness ℝ T'.carrier 0 =
        ENNReal.toReal (Metric.ethickness ℝ T'.carrier 0) :=
      (Metric.toReal_ethickness hbddT' 0).symm
    have hb : (1 / 2 : ℝ) ≤ Metric.thickness ℝ T'.carrier 0 := by
      rw [hbridge0']
      calc
        (1 / 2 : ℝ) = ENNReal.toReal (1 / 2 : ENNReal) := by norm_num
        _ ≤ ENNReal.toReal (Metric.ethickness ℝ T'.carrier 0) := by
          exact ENNReal.toReal_mono (Metric.ethickness_ne_top hbddT' 0)
            (Tube.le_ethickness_zero T')
    have hbotT' : (1 : ℝ) ≤ 2 * Metric.thickness ℝ T'.carrier 0 := by nlinarith
    exact htopT.trans hbotT'
  · have hn1 : 1 ≤ n := by omega
    have hbridge_n : Metric.thickness ℝ T.carrier n =
        ENNReal.toReal (Metric.ethickness ℝ T.carrier n) :=
      (Metric.toReal_ethickness T.isCompact.isBounded n).symm
    have hbridge_n' : Metric.thickness ℝ T'.carrier n =
        ENNReal.toReal (Metric.ethickness ℝ T'.carrier n) :=
      (Metric.toReal_ethickness T'.isCompact.isBounded n).symm
    rcases Nat.lt_or_ge n (Module.finrank ℝ E) with hnd | hnd
    · have hT : Metric.thickness ℝ T.carrier n = (δ : ℝ) := by
        rw [hbridge_n, ethickness_eq_of_one_le T hn1 hnd]
        simp
      have hT' : Metric.thickness ℝ T'.carrier n = (δ : ℝ) := by
        rw [hbridge_n', ethickness_eq_of_one_le T' hn1 hnd]
        simp
      rw [hT, hT']
      nlinarith [(δ.coe_nonneg : (0 : ℝ) ≤ δ)]
    · have hT0 : Metric.thickness ℝ T.carrier n = 0 := by
        rw [hbridge_n, Metric.ethickness_eq_zero_of_finrank_le hnd]
        simp
      have hT'0 : Metric.thickness ℝ T'.carrier n = 0 := by
        rw [hbridge_n', Metric.ethickness_eq_zero_of_finrank_le hnd]
        simp
      rw [hT0, hT'0]
      norm_num

end ComparableThickness

end Tube

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Tube → containing-ball assignment** (δ-uniform).
There is a *fixed* finite set of points `xs ⊆ E` such that `closedBall 0 2` is
covered by the radius-`1/4` balls around `xs`, and for every `0 ≤ δ ≤ 1/4`,
every length-1 δ-tube whose carrier lies in `closedBall 0 2` fits inside one of
the unit balls `closedBall x 1` for some `x ∈ xs`. The cardinality `xs.card` is
an absolute dimensional constant (independent of `δ`). -/
lemma exists_unit_ball_assignment :
    ∃ (xs : Finset E),
      (∀ x ∈ xs, ‖x‖ ≤ 2) ∧
      (Metric.closedBall (0 : E) 2 : Set E) ⊆ ⋃ x ∈ xs, Metric.closedBall x (1 / 4) ∧
      ∀ {δ : NNReal}, (δ : ℝ) ≤ 1 / 4 →
        ∀ T : Tube δ E, T.carrier ⊆ Metric.closedBall 0 2 →
          ∃ x ∈ xs, T.carrier ⊆ Metric.closedBall x 1 := by
  obtain ⟨xs, hxs_norm, hcover⟩ :=
    closedBall_finite_closedBall_cover (E := E) 2 (by norm_num : (0 : ℝ) < 1 / 4) (0 : E)
  refine ⟨xs, fun x hx => by simpa [Metric.mem_closedBall, dist_zero_right] using hxs_norm x hx,
    hcover, ?_⟩
  intro δ hδ_le T hsub
  have hmid : midpoint ℝ T.x T.y ∈ T.carrier := T.carrier_eq ▸ Set.mem_iUnion₂.mpr
    ⟨midpoint ℝ T.x T.y, midpoint_mem_segment (𝕜 := ℝ) T.x T.y,
      Metric.mem_closedBall_self δ.coe_nonneg⟩
  obtain ⟨x, hx, hmid_close⟩ := Set.mem_iUnion₂.mp (hcover (hsub hmid))
  refine ⟨x, hx, fun p hp => Metric.mem_closedBall.mpr ?_⟩
  have h₁ := Metric.mem_closedBall.mp (Tube.carrier_subset_closedBall_midpoint (E := E) T hp)
  have h₂ := Metric.mem_closedBall.mp hmid_close
  linarith [dist_triangle p (midpoint ℝ T.x T.y) x]

end Kakeya
