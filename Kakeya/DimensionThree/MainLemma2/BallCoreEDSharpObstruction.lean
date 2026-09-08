/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.BallCoreEDFold

/-!
# (C1) is false at every localisation: the clamped-window obstruction

`Kakeya.VeryNotSticky.SharpCapsuleAlignment` asks, for two tubes `i`, `j` of one ball `B` whose
`K`-dilated capsules are not essentially distinct, that the *undilated* capsule of `j`, localised
to `ball (ctr B) (r₁/16)`, lie in the `K`-dilated capsule of `i`. The fold author's model
 put the ball centre at the **centre** of both windows and found a marginal
constant (`≈ 1.11` at `r₁/16`, `≈ 0.90` at `r₁/64`). That model misses the clamping in
`Kakeya.VeryNotSticky.segStart`: when the centre `c` projects at or before the start of a tube's
core (`coreParam T c = 0`), the window is `[0, 2L]` and **`c` sits at its end**, not its middle.

This file compiles the resulting obstruction. Two tubes on parallel cores, both starting next to
`c` — tube `j` at `c`, tube `i` at `c + (L/8) • axis₀ + d • axis₁` with `0 ≤ d ≤ Kδ/8` — have
windows `[0, 2L]` clamped at their starts. Their `K`-dilated capsules overlap in the capsule
`Kakeya.VeryNotSticky.obstructionBody` of length `2L − L/8`, which is more than half of either
(the volume comparison is by one homothety of ratio `8/7`, `(8/7)³ < 2`, and one translation), so
they are **not** essentially distinct; but the point `c` itself lies in `j`'s undilated capsule and
at axial distance `L/8 > K'δ` from `i`'s core window, so it is outside `i`'s `K'`-dilated capsule
for **every** `K'` with `K'δ < L/8` — and it is in `ball c r` for every `r > 0`.

## Main statements

* `Kakeya.VeryNotSticky.not_isEssentiallyDistinct_obstruction` — the two dilated capsules are not
  essentially distinct.
* `Kakeya.VeryNotSticky.obstruction_not_mem_capsuleAt` — `c` is outside `i`'s `K'`-dilate for
  every `K'δ < L/8`.
* `Kakeya.VeryNotSticky.not_capsuleAlignmentBody` — the body of `SharpCapsuleAlignment`, with the
  tubes and the centre free, fails at **every** localisation radius `r > 0`;
  `sharpCapsuleAlignment_iff_body` is the `Iff.rfl` link to the existing `abbrev`.
* `Kakeya.VeryNotSticky.exists_obstruction_at_fold_constants` — the same at the fold's own
  constants `K = edDilateConstant`, `L = r₁/4`, under the fold's radius floor, with the two unit
  tubes disjoint (hence essentially distinct as tubes).

## What this settles

The misalignment is **axial** (along the core), of size `L/8 = r₁/32`, unbounded relative to the
radius `Kδ`; no radius dilate and no localisation radius absorbs it. So (C1) as stated cannot be
proved at `r₁/64` or at any other localisation; the target text has to change (a licence item).
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped ENNReal NNReal

namespace Kakeya.VeryNotSticky

universe u

/-! ### Two coordinate vectors of `E3` -/

/-- The first coordinate vector of `E3`. -/
noncomputable def axis₀ : E3 := EuclideanSpace.single 0 1

/-- The second coordinate vector of `E3`. -/
noncomputable def axis₁ : E3 := EuclideanSpace.single 1 1

theorem norm_axis₀ : ‖axis₀‖ = 1 := by
  simp [axis₀]

theorem norm_axis₁ : ‖axis₁‖ = 1 := by
  simp [axis₁]

theorem inner_axis₀_axis₁ : inner ℝ axis₀ axis₁ = 0 := by
  simp [axis₀, axis₁, EuclideanSpace.inner_single_left]

/-- `‖a • axis₀ + b • axis₁‖² = a² + b²`. -/
theorem norm_sq_axis (a b : ℝ) : ‖a • axis₀ + b • axis₁‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [norm_add_sq_real, norm_smul, norm_smul, norm_axis₀, norm_axis₁, real_inner_smul_left,
    real_inner_smul_right, inner_axis₀_axis₁, Real.norm_eq_abs, Real.norm_eq_abs]
  simp [sq_abs]

theorem norm_axis_eq (a b : ℝ) : ‖a • axis₀ + b • axis₁‖ = Real.sqrt (a ^ 2 + b ^ 2) := by
  rw [← norm_sq_axis, Real.sqrt_sq (norm_nonneg _)]

theorem abs_le_norm_axis (a b : ℝ) : |a| ≤ ‖a • axis₀ + b • axis₁‖ := by
  rw [norm_axis_eq]
  exact Real.abs_le_sqrt (by nlinarith [sq_nonneg b])

theorem abs_le_norm_axis' (a b : ℝ) : |b| ≤ ‖a • axis₀ + b • axis₁‖ := by
  rw [norm_axis_eq]
  exact Real.abs_le_sqrt (by nlinarith [sq_nonneg a])

/-! ### Segments along `axis₀` -/

theorem mem_segment_axis {c : E3} {a b x : ℝ} (hab : a < b) (hx : x ∈ Icc a b) :
    c + x • axis₀ ∈ segment ℝ (c + a • axis₀) (c + b • axis₀) := by
  rw [segment_eq_image' ℝ]
  refine ⟨(x - a) / (b - a), ⟨div_nonneg (by linarith [hx.1]) (by linarith),
    (div_le_one (by linarith)).2 (by linarith [hx.2])⟩, ?_⟩
  have hba : b - a ≠ 0 := by linarith
  simp only
  rw [show c + b • axis₀ - (c + a • axis₀) = (b - a) • axis₀ by module, smul_smul,
    div_mul_cancel₀ _ hba]
  module

theorem exists_of_mem_segment_axis {c : E3} {a b : ℝ} (hab : a ≤ b) {y : E3}
    (hy : y ∈ segment ℝ (c + a • axis₀) (c + b • axis₀)) :
    ∃ x ∈ Icc a b, y = c + x • axis₀ := by
  rw [segment_eq_image' ℝ] at hy
  obtain ⟨θ, hθ, rfl⟩ := hy
  refine ⟨a + θ * (b - a), ⟨by nlinarith [hθ.1], by nlinarith [hθ.2]⟩, ?_⟩
  simp only
  rw [show c + b • axis₀ - (c + a • axis₀) = (b - a) • axis₀ by module, smul_smul]
  module

theorem mem_segment_axis' (p : E3) {b x : ℝ} (hb : 0 < b) (hx : x ∈ Icc 0 b) :
    p + x • axis₀ ∈ segment ℝ p (p + b • axis₀) := by
  rw [segment_eq_image' ℝ]
  refine ⟨x / b, ⟨div_nonneg hx.1 hb.le, (div_le_one hb).2 hx.2⟩, ?_⟩
  simp only
  rw [add_sub_cancel_left, smul_smul, div_mul_cancel₀ _ hb.ne']

theorem exists_of_mem_segment_axis' (p : E3) {b : ℝ} (hb : 0 ≤ b) {y : E3}
    (hy : y ∈ segment ℝ p (p + b • axis₀)) : ∃ x ∈ Icc 0 b, y = p + x • axis₀ := by
  rw [segment_eq_image' ℝ] at hy
  obtain ⟨θ, hθ, rfl⟩ := hy
  refine ⟨θ * b, ⟨mul_nonneg hθ.1 hb, by nlinarith [hθ.2]⟩, ?_⟩
  simp only
  rw [add_sub_cancel_left, smul_smul]

/-- Membership in a compact `cthickening` of a segment, as a witness on the segment. -/
theorem exists_mem_of_mem_cthickening_segment {a b z : E3} {r : ℝ} (hr : 0 ≤ r)
    (hz : z ∈ cthickening r (segment ℝ a b)) : ∃ y ∈ segment ℝ a b, dist z y ≤ r := by
  rw [isCompact_segment.cthickening_eq_biUnion_closedBall hr] at hz
  obtain ⟨y, hy, hzy⟩ := Set.mem_iUnion₂.1 hz
  exact ⟨y, hy, Metric.mem_closedBall.1 hzy⟩

/-! ### Tubes along `axis₀` -/

theorem dist_self_add_axis₀ (p : E3) : dist p (p + axis₀) = 1 := by
  rw [dist_self_add_right, norm_axis₀]

/-- The `δ`-tube whose unit core runs from `p` to `p + axis₀`. -/
noncomputable def axisTube (δ : NNReal) (p : E3) : Tube δ E3 :=
  Tube.mk' δ (dist_self_add_axis₀ p)

variable {δ : NNReal}

@[simp] theorem axisTube_x (p : E3) : (axisTube δ p).x = p := rfl

@[simp] theorem axisTube_y (p : E3) : (axisTube δ p).y = p + axis₀ := rfl

theorem axisTube_direction (p : E3) : (axisTube δ p).direction = axis₀ :=
  add_sub_cancel_left p axis₀

theorem corePt_axisTube (p : E3) (t : ℝ) : corePt (axisTube δ p) t = p + t • axis₀ := by
  rw [corePt, axisTube_direction, axisTube_x]

theorem axisTube_carrier (p : E3) :
    (axisTube δ p).carrier = cthickening (δ : ℝ) (segment ℝ p (p + (1 : ℝ) • axis₀)) := by
  rw [Tube.carrier_eq_cthickening, one_smul]
  rfl

theorem axisTube_x_mem (p : E3) : p ∈ (axisTube δ p).carrier := by
  rw [axisTube_carrier]
  exact self_subset_cthickening _ (left_mem_segment ℝ _ _)

/-- **The clamping.** The core point of `axisTube δ (c + (s • axis₀ + d • axis₁))` nearest to `c`
is its start, for `0 ≤ s`. -/
theorem coreParam_axisTube (c : E3) {s d : ℝ} (hs : 0 ≤ s) :
    coreParam (axisTube δ (c + (s • axis₀ + d • axis₁))) c = 0 := by
  have ht := coreParam_mem (axisTube δ (c + (s • axis₀ + d • axis₁))) c
  have hmin := coreParam_min (axisTube δ (c + (s • axis₀ + d • axis₁))) c (u := 0)
    ⟨le_rfl, zero_le_one⟩
  generalize coreParam (axisTube δ (c + (s • axis₀ + d • axis₁))) c = t at ht hmin ⊢
  rw [corePt_axisTube, corePt_axisTube, zero_smul, add_zero, dist_eq_norm, dist_eq_norm,
    show c + (s • axis₀ + d • axis₁) + t • axis₀ - c = (s + t) • axis₀ + d • axis₁ by module,
    show c + (s • axis₀ + d • axis₁) - c = s • axis₀ + d • axis₁ by module] at hmin
  have h2 := pow_le_pow_left₀ (norm_nonneg _) hmin 2
  rw [norm_sq_axis, norm_sq_axis] at h2
  have ht0 : t ≤ 0 := by nlinarith [ht.1]
  exact le_antisymm ht0 ht.1

theorem coreParam_axisTube_self (c : E3) : coreParam (axisTube δ c) c = 0 := by
  have h := coreParam_axisTube (δ := δ) c (s := 0) (d := 0) le_rfl
  simpa using h

theorem segStart_eq_zero_of_coreParam_eq_zero (T : Tube δ E3) (c : E3)
    (h0 : coreParam T c = 0) {L : ℝ} (hL : 0 ≤ L) (hL1 : 2 * L ≤ 1) : segStart T c L = 0 := by
  rw [segStart, h0, zero_sub, max_eq_right (by linarith), min_eq_left (by linarith)]

/-- The `K`-dilated capsule of a clamped axis tube is the `Kδ`-neighbourhood of the window
`[0, 2L]` **starting at the tube's start**. -/
theorem segCarrierSetAt_axisTube (K : NNReal) (p c : E3) (h0 : coreParam (axisTube δ p) c = 0)
    {L : ℝ} (hL : 0 ≤ L) (hL1 : 2 * L ≤ 1) :
    segCarrierSetAt K (axisTube δ p) c L =
      cthickening ((K : ℝ) * (δ : ℝ)) (segment ℝ p (p + (2 * L) • axis₀)) := by
  rw [segCarrierSetAt, segStart_eq_zero_of_coreParam_eq_zero _ _ h0 hL hL1, corePt_axisTube,
    corePt_axisTube, zero_add, zero_smul, add_zero]

theorem segCarrierSet_axisTube (p c : E3) (h0 : coreParam (axisTube δ p) c = 0)
    {L : ℝ} (hL : 0 ≤ L) (hL1 : 2 * L ≤ 1) :
    segCarrierSet (axisTube δ p) c L =
      cthickening (δ : ℝ) (segment ℝ p (p + (2 * L) • axis₀)) := by
  rw [segCarrierSet, segStart_eq_zero_of_coreParam_eq_zero _ _ h0 hL hL1, corePt_axisTube,
    corePt_axisTube, zero_add, zero_smul, add_zero]

/-! ### The obstruction configuration -/

/-- **The common body**: the `(Kδ − d)`-neighbourhood of the part `[L/8, 2L]` of tube `j`'s
window, which both dilated capsules contain. -/
noncomputable def obstructionBody (K δ : NNReal) (c : E3) (L d : ℝ) : Set E3 :=
  cthickening ((K : ℝ) * (δ : ℝ) - d)
    (segment ℝ (c + (L / 8) • axis₀) (c + (2 * L) • axis₀))

section Obstruction

variable {K : NNReal} {c : E3} {L d : ℝ}

/-- The body lies in tube `j`'s dilated capsule (`j` starts at `c`). -/
theorem obstructionBody_subset_capsule_j (hL : 0 < L) (hL1 : 2 * L ≤ 1) (hd0 : 0 ≤ d) :
    obstructionBody K δ c L d ⊆ segCarrierSetAt K (axisTube δ c) c L := by
  rw [segCarrierSetAt_axisTube K c c (coreParam_axisTube_self c) hL.le hL1]
  refine subset_trans (cthickening_mono (by linarith) _) (cthickening_subset_of_subset _ ?_)
  refine (convex_segment _ _).segment_subset ?_ (right_mem_segment ℝ _ _)
  exact mem_segment_axis' c (by linarith) ⟨by linarith, by linarith⟩

/-- The body lies in tube `i`'s dilated capsule (`i` starts at `c + (L/8) • axis₀ + d • axis₁`). -/
theorem obstructionBody_subset_capsule_i (hL : 0 < L) (hL1 : 2 * L ≤ 1) (hd0 : 0 ≤ d)
    (hdR : d ≤ (K : ℝ) * (δ : ℝ) / 8) :
    obstructionBody K δ c L d ⊆
      segCarrierSetAt K (axisTube δ (c + ((L / 8) • axis₀ + d • axis₁))) c L := by
  rw [segCarrierSetAt_axisTube K _ c (coreParam_axisTube c (by positivity)) hL.le hL1]
  intro z hz
  obtain ⟨y, hy, hzy⟩ := exists_mem_of_mem_cthickening_segment (by linarith) hz
  obtain ⟨x, hx, rfl⟩ := exists_of_mem_segment_axis (by linarith) hy
  refine mem_cthickening_of_dist_le z
    (c + ((L / 8) • axis₀ + d • axis₁) + (x - L / 8) • axis₀) _ _ ?_ ?_
  · exact mem_segment_axis' _ (by linarith) ⟨by linarith [hx.1], by linarith [hx.2]⟩
  · have hd : dist (c + x • axis₀) (c + ((L / 8) • axis₀ + d • axis₁) + (x - L / 8) • axis₀)
        = d := by
      rw [dist_eq_norm, show c + x • axis₀ - (c + ((L / 8) • axis₀ + d • axis₁) +
        (x - L / 8) • axis₀) = (-d) • axis₁ by module, norm_smul, norm_axis₁, mul_one,
        Real.norm_eq_abs, abs_neg, abs_of_nonneg hd0]
    calc dist z (c + ((L / 8) • axis₀ + d • axis₁) + (x - L / 8) • axis₀)
        ≤ dist z (c + x • axis₀) +
          dist (c + x • axis₀) (c + ((L / 8) • axis₀ + d • axis₁) + (x - L / 8) • axis₀) :=
          dist_triangle _ _ _
      _ ≤ ((K : ℝ) * (δ : ℝ) - d) + d := add_le_add hzy (le_of_eq hd)
      _ = (K : ℝ) * (δ : ℝ) := by ring

/-- **The volume comparison, first half**: tube `j`'s dilated capsule lies in the homothety of
ratio `8/7`, about the far end `c + (2L) • axis₀` of the window, of the common body. -/
theorem capsule_j_subset_homothety (hL : 0 < L) (hL1 : 2 * L ≤ 1)
    (hdR : d ≤ (K : ℝ) * (δ : ℝ) / 8) :
    segCarrierSetAt K (axisTube δ c) c L ⊆
      (AffineMap.homothety (c + (2 * L) • axis₀) (8 / 7 : ℝ)) '' obstructionBody K δ c L d := by
  rw [segCarrierSetAt_axisTube K c c (coreParam_axisTube_self c) hL.le hL1]
  intro z hz
  obtain ⟨y, hy, hzy⟩ := exists_mem_of_mem_cthickening_segment (by positivity) hz
  obtain ⟨x, hx, rfl⟩ := exists_of_mem_segment_axis' c (by linarith) hy
  refine ⟨AffineMap.homothety (c + (2 * L) • axis₀) (8 / 7 : ℝ)⁻¹ z, ?_, ?_⟩
  · refine mem_cthickening_of_dist_le _
      (AffineMap.homothety (c + (2 * L) • axis₀) (8 / 7 : ℝ)⁻¹ (c + x • axis₀)) _ _ ?_ ?_
    · have hpt : AffineMap.homothety (c + (2 * L) • axis₀) (8 / 7 : ℝ)⁻¹ (c + x • axis₀) =
          c + (2 * L - (7 / 8) * (2 * L - x)) • axis₀ := by
        simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
        module
      rw [hpt]
      exact mem_segment_axis (by linarith) ⟨by linarith [hx.1], by linarith [hx.2]⟩
    · rw [dist_homothety, abs_of_pos (by norm_num)]
      calc (8 / 7 : ℝ)⁻¹ * dist z (c + x • axis₀) ≤ (8 / 7 : ℝ)⁻¹ * ((K : ℝ) * (δ : ℝ)) := by
            gcongr
        _ = 7 / 8 * ((K : ℝ) * (δ : ℝ)) := by norm_num
        _ ≤ (K : ℝ) * (δ : ℝ) - d := by linarith
  · have h := homothety_inv_apply (p := c + (2 * L) • axis₀) (k := (8 / 7 : ℝ)⁻¹) (by norm_num) z
    rwa [inv_inv] at h

/-- **The volume comparison, second half**: tube `i`'s dilated capsule is the translate of tube
`j`'s by the offset `(L/8) • axis₀ + d • axis₁`. -/
theorem capsule_i_eq_image_add (hL : 0 < L) (hL1 : 2 * L ≤ 1) :
    segCarrierSetAt K (axisTube δ (c + ((L / 8) • axis₀ + d • axis₁))) c L =
      (fun z => ((L / 8) • axis₀ + d • axis₁) + z) '' segCarrierSetAt K (axisTube δ c) c L := by
  rw [segCarrierSetAt_axisTube K _ c (coreParam_axisTube c (by positivity)) hL.le hL1,
    segCarrierSetAt_axisTube K c c (coreParam_axisTube_self c) hL.le hL1]
  have hR : 0 ≤ (K : ℝ) * (δ : ℝ) := by positivity
  ext z
  constructor
  · intro hz
    obtain ⟨y, hy, hzy⟩ := exists_mem_of_mem_cthickening_segment hR hz
    obtain ⟨x, hx, rfl⟩ := exists_of_mem_segment_axis' _ (by linarith) hy
    refine ⟨-((L / 8) • axis₀ + d • axis₁) + z, ?_, add_neg_cancel_left _ _⟩
    refine mem_cthickening_of_dist_le _ (c + x • axis₀) _ _
      (mem_segment_axis' c (by linarith) hx) ?_
    have hdist : dist (-((L / 8) • axis₀ + d • axis₁) + z) (c + x • axis₀) =
        dist z (c + ((L / 8) • axis₀ + d • axis₁) + x • axis₀) := by
      rw [← dist_add_left ((L / 8) • axis₀ + d • axis₁), add_neg_cancel_left]
      congr 1
      abel
    rw [hdist]
    exact hzy
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨y, hy, hwy⟩ := exists_mem_of_mem_cthickening_segment hR hw
    obtain ⟨x, hx, rfl⟩ := exists_of_mem_segment_axis' _ (by linarith) hy
    dsimp only
    refine mem_cthickening_of_dist_le _ (c + ((L / 8) • axis₀ + d • axis₁) + x • axis₀) _ _
      (mem_segment_axis' _ (by linarith) hx) ?_
    rw [show c + ((L / 8) • axis₀ + d • axis₁) + x • axis₀ =
      ((L / 8) • axis₀ + d • axis₁) + (c + x • axis₀) by abel, dist_add_left]
    exact hwy

theorem volume_capsule_i_eq (hL : 0 < L) (hL1 : 2 * L ≤ 1) :
    volume (segCarrierSetAt K (axisTube δ (c + ((L / 8) • axis₀ + d • axis₁))) c L) =
      volume (segCarrierSetAt K (axisTube δ c) c L) := by
  rw [capsule_i_eq_image_add hL hL1, Set.image_add_left, measure_preimage_add]

theorem volume_obstructionBody_ne_zero (hL : 0 < L) (hR : 0 < (K : ℝ) * (δ : ℝ))
    (hdR : d ≤ (K : ℝ) * (δ : ℝ) / 8) : volume (obstructionBody K δ c L d) ≠ 0 := by
  have hpos : 0 < (K : ℝ) * (δ : ℝ) - d := by linarith
  refine ne_of_gt (lt_of_lt_of_le (measure_ball_pos volume (c + L • axis₀) hpos)
    (measure_mono ?_))
  refine subset_trans ball_subset_closedBall (closedBall_subset_cthickening ?_ _)
  exact mem_segment_axis (by linarith) ⟨by linarith, by linarith⟩

theorem volume_obstructionBody_ne_top : volume (obstructionBody K δ c L d) ≠ ⊤ :=
  (isCompact_segment.cthickening.measure_lt_top).ne

/-- **The two dilated capsules are NOT essentially distinct.** The common body has more than half
the volume of either: `vol(A_j) ≤ (8/7)³ · vol(body) < 2 · vol(body)`, and `vol(A_i) = vol(A_j)`. -/
theorem not_isEssentiallyDistinct_obstruction (hR : 0 < (K : ℝ) * (δ : ℝ)) (hL : 0 < L)
    (hL1 : 2 * L ≤ 1) (hd0 : 0 ≤ d) (hdR : d ≤ (K : ℝ) * (δ : ℝ) / 8) :
    ¬ IsEssentiallyDistinct
      (segCarrierSetAt K (axisTube δ (c + ((L / 8) • axis₀ + d • axis₁))) c L)
      (segCarrierSetAt K (axisTube δ c) c L) := by
  intro hED
  have hM0 := volume_obstructionBody_ne_zero (K := K) (δ := δ) (c := c) hL hR hdR
  have hMtop := volume_obstructionBody_ne_top (K := K) (δ := δ) (c := c) (L := L) (d := d)
  have hMsub : obstructionBody K δ c L d ⊆
      segCarrierSetAt K (axisTube δ (c + ((L / 8) • axis₀ + d • axis₁))) c L ∩
        segCarrierSetAt K (axisTube δ c) c L :=
    subset_inter (obstructionBody_subset_capsule_i hL hL1 hd0 hdR)
      (obstructionBody_subset_capsule_j hL hL1 hd0)
  have hAj : volume (segCarrierSetAt K (axisTube δ c) c L) ≤
      ENNReal.ofReal (512 / 343) * volume (obstructionBody K δ c L d) := by
    calc volume (segCarrierSetAt K (axisTube δ c) c L)
        ≤ volume ((AffineMap.homothety (c + (2 * L) • axis₀) (8 / 7 : ℝ)) ''
            obstructionBody K δ c L d) :=
          measure_mono (capsule_j_subset_homothety hL hL1 hdR)
      _ = ENNReal.ofReal |(8 / 7 : ℝ) ^ Module.finrank ℝ E3| *
            volume (obstructionBody K δ c L d) :=
          Measure.addHaar_image_homothety _ _ _ _
      _ = ENNReal.ofReal (512 / 343) * volume (obstructionBody K δ c L d) := by
          rw [finrank_euclideanSpace_fin]
          norm_num
  have hmax : max (volume (segCarrierSetAt K (axisTube δ (c + ((L / 8) • axis₀ + d • axis₁))) c L))
      (volume (segCarrierSetAt K (axisTube δ c) c L)) ≤
        ENNReal.ofReal (512 / 343) * volume (obstructionBody K δ c L d) := by
    rw [volume_capsule_i_eq hL hL1, max_self]
    exact hAj
  have hhalf0 : (1 / 2 : ENNReal) ≠ 0 := by norm_num
  have hhalftop : (1 / 2 : ENNReal) ≠ ⊤ := by norm_num
  have hnum : (1 / 2 : ENNReal) * ENNReal.ofReal (512 / 343) < 1 := by
    have h2 : ENNReal.ofReal (512 / 343) < 2 := by
      rw [← ENNReal.ofReal_ofNat 2, ENNReal.ofReal_lt_ofReal_iff (by norm_num)]
      norm_num
    calc (1 / 2 : ENNReal) * ENNReal.ofReal (512 / 343) < (1 / 2 : ENNReal) * 2 :=
          ENNReal.mul_lt_mul_right hhalf0 hhalftop h2
      _ = 1 := by
          rw [one_div, ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]
  have hlt : (1 / 2 : ENNReal) * (ENNReal.ofReal (512 / 343) * volume (obstructionBody K δ c L d))
      < volume (obstructionBody K δ c L d) := by
    calc (1 / 2 : ENNReal) * (ENNReal.ofReal (512 / 343) * volume (obstructionBody K δ c L d))
        = ((1 / 2 : ENNReal) * ENNReal.ofReal (512 / 343)) *
            volume (obstructionBody K δ c L d) := by
          ring
      _ < 1 * volume (obstructionBody K δ c L d) :=
          ENNReal.mul_lt_mul_left hM0 hMtop hnum
      _ = volume (obstructionBody K δ c L d) := one_mul _
  have hchain : volume (obstructionBody K δ c L d) ≤
      (1 / 2 : ENNReal) * (ENNReal.ofReal (512 / 343) * volume (obstructionBody K δ c L d)) :=
    le_trans (measure_mono hMsub) (le_trans hED (mul_le_mul' le_rfl hmax))
  exact absurd hchain (not_le.2 hlt)

/-- **The misalignment.** The centre `c` lies on tube `j`'s undilated capsule … -/
theorem obstruction_mem_capsule (hL : 0 < L) (hL1 : 2 * L ≤ 1) :
    c ∈ segCarrierSet (axisTube δ c) c L := by
  rw [segCarrierSet_axisTube c c (coreParam_axisTube_self c) hL.le hL1]
  exact self_subset_cthickening _ (left_mem_segment ℝ _ _)

/-- … but outside tube `i`'s `K'`-dilated capsule for **every** `K'` with `K'δ < L/8`: the offset
is axial, of size `L/8`, and no radius dilate absorbs it. -/
theorem obstruction_not_mem_capsuleAt (hL : 0 < L) (hL1 : 2 * L ≤ 1)
    (K' : NNReal) (hK' : (K' : ℝ) * (δ : ℝ) < L / 8) :
    c ∉ segCarrierSetAt K' (axisTube δ (c + ((L / 8) • axis₀ + d • axis₁))) c L := by
  rw [segCarrierSetAt_axisTube K' _ c (coreParam_axisTube c (by positivity)) hL.le hL1]
  intro hc
  obtain ⟨y, hy, hcy⟩ := exists_mem_of_mem_cthickening_segment (by positivity) hc
  obtain ⟨x, hx, rfl⟩ := exists_of_mem_segment_axis' _ (by linarith) hy
  rw [dist_eq_norm, show c - (c + ((L / 8) • axis₀ + d • axis₁) + x • axis₀) =
    (-(L / 8 + x)) • axis₀ + (-d) • axis₁ by module] at hcy
  have h := abs_le_norm_axis (-(L / 8 + x)) (-d)
  rw [abs_neg, abs_of_nonneg (by linarith [hx.1])] at h
  linarith [hx.1]

/-- The start of tube `i` lies in `ball c (L/4)` — the shrunken ball `ball (ctr B) (r₁/16)` at
`L = r₁/4` — so both tubes meet the piece, as the fold's segments do. -/
theorem obstruction_start_mem_ball (hL : 0 < L) (hd0 : 0 ≤ d) (hdL : d < L / 8) :
    c + ((L / 8) • axis₀ + d • axis₁) ∈ ball c (L / 4) := by
  rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_axis_eq,
    Real.sqrt_lt' (by positivity)]
  nlinarith

/-- For `2δ < d` the two **unit tubes** are disjoint, hence essentially distinct as tubes. -/
theorem obstruction_tubes_disjoint (hd : 2 * (δ : ℝ) < d) :
    (axisTube δ (c + ((L / 8) • axis₀ + d • axis₁))).carrier ∩ (axisTube δ c).carrier = ∅ := by
  rw [axisTube_carrier, axisTube_carrier, Set.eq_empty_iff_forall_notMem]
  intro z hz
  obtain ⟨y, hy, hzy⟩ := exists_mem_of_mem_cthickening_segment δ.coe_nonneg hz.1
  obtain ⟨y', hy', hzy'⟩ := exists_mem_of_mem_cthickening_segment δ.coe_nonneg hz.2
  obtain ⟨a, _, rfl⟩ := exists_of_mem_segment_axis' _ zero_le_one hy
  obtain ⟨a', _, rfl⟩ := exists_of_mem_segment_axis' _ zero_le_one hy'
  have htri := dist_triangle (c + ((L / 8) • axis₀ + d • axis₁) + a • axis₀) z (c + a' • axis₀)
  rw [dist_comm _ z] at htri
  have hdd : dist (c + ((L / 8) • axis₀ + d • axis₁) + a • axis₀) (c + a' • axis₀) =
      ‖(L / 8 + a - a') • axis₀ + d • axis₁‖ := by
    rw [dist_eq_norm]
    congr 1
    module
  have h := abs_le_norm_axis' (L / 8 + a - a') d
  rw [abs_of_nonneg (by linarith [δ.coe_nonneg])] at h
  linarith [hdd, htri, hzy, hzy']

theorem obstruction_tubes_essDistinct (hd : 2 * (δ : ℝ) < d) :
    IsEssentiallyDistinct (axisTube δ (c + ((L / 8) • axis₀ + d • axis₁))).carrier
      (axisTube δ c).carrier := by
  rw [IsEssentiallyDistinct, obstruction_tubes_disjoint hd, measure_empty]
  exact bot_le

end Obstruction

/-! ### The body of `SharpCapsuleAlignment`, with the tubes and the centre free -/

/-- The body of `Kakeya.VeryNotSticky.SharpCapsuleAlignment` for two tubes `Ti Tj`, a centre `c`,
a half-length `L` and a localisation radius `r`: non-essential-distinctness of the `K`-dilated
capsules forces the localised undilated capsule of `Tj` into the `K`-dilated capsule of `Ti`. -/
def CapsuleAlignmentBody (K : NNReal) (Ti Tj : Tube δ E3) (c : E3) (L r : ℝ) : Prop :=
  ¬ IsEssentiallyDistinct (segCarrierSetAt K Ti c L) (segCarrierSetAt K Tj c L) →
    segCarrierSet Tj c L ∩ ball c r ⊆ segCarrierSetAt K Ti c L

/-- `SharpCapsuleAlignment core K` **is** the body at `Ti = cfg.T i`, `Tj = cfg.T j`,
`c = core.ctr B`, `L = r₁/4`, `r = r₁/16` — by `Iff.rfl`. -/
theorem sharpCapsuleAlignment_iff_body {cfg : VeryNotSticky.{u}} (core : BallDataCore cfg)
    (K : NNReal) :
    SharpCapsuleAlignment core K ↔
      ∀ B ∈ core.bs, ∀ i ∈ cfg.s, ∀ j ∈ cfg.s,
        CapsuleAlignmentBody K (cfg.T i).toTube (cfg.T j).toTube (core.ctr B)
          ((cfg.r₁ : ℝ) / 4) ((cfg.r₁ : ℝ) / 16) :=
  Iff.rfl

/-- **(C1)'s body is false at every localisation radius `r > 0`**, for every `K ≥ 1`, every
`δ > 0`, every centre `c` and every half-length `L` with `2L ≤ 1` and `8Kδ < L`: the two clamped
axis tubes are the witnesses. The second tube's start lies in `ball c (L/4)`, so both tubes meet
the piece `ball (ctr B) (r₁/16)` at `L = r₁/4`. -/
theorem not_capsuleAlignmentBody (hδ : 0 < δ) (K : NNReal) (hK : 1 ≤ K) (c : E3) {L : ℝ}
    (hL1 : 2 * L ≤ 1) (hRL : 8 * ((K : ℝ) * (δ : ℝ)) < L) {r : ℝ} (hr : 0 < r) :
    ∃ Ti Tj : Tube δ E3,
      ¬ CapsuleAlignmentBody K Ti Tj c L r ∧ Ti.x ∈ ball c (L / 4) ∧ Tj.x = c := by
  have hR : 0 < (K : ℝ) * (δ : ℝ) := by
    have h1 : (0 : ℝ) < K := lt_of_lt_of_le zero_lt_one (by exact_mod_cast hK)
    exact mul_pos h1 (by exact_mod_cast hδ)
  have hL : 0 < L := by linarith
  refine ⟨axisTube δ (c + ((L / 8) • axis₀ + (0 : ℝ) • axis₁)), axisTube δ c, ?_,
    obstruction_start_mem_ball hL le_rfl (by linarith), rfl⟩
  intro hbody
  have hne := not_isEssentiallyDistinct_obstruction (c := c) hR hL hL1 le_rfl
    (by linarith : (0 : ℝ) ≤ (K : ℝ) * (δ : ℝ) / 8)
  have hc := hbody hne ⟨obstruction_mem_capsule hL hL1, Metric.mem_ball_self hr⟩
  exact obstruction_not_mem_capsuleAt hL hL1 K (by linarith) hc

/-- The same with the two unit tubes **disjoint** (hence essentially distinct as tubes), at
offset `d = 3δ`; this needs `24 ≤ K` so that `3δ ≤ Kδ/8`. -/
theorem not_capsuleAlignmentBody_of_essDistinct (hδ : 0 < δ) (K : NNReal) (hK : 24 ≤ K)
    (c : E3) {L : ℝ} (hL1 : 2 * L ≤ 1) (hRL : 8 * ((K : ℝ) * (δ : ℝ)) < L) {r : ℝ} (hr : 0 < r) :
    ∃ Ti Tj : Tube δ E3,
      ¬ CapsuleAlignmentBody K Ti Tj c L r ∧ IsEssentiallyDistinct Ti.carrier Tj.carrier ∧
        Ti.x ∈ ball c (L / 4) ∧ Tj.x = c := by
  have hK' : (24 : ℝ) ≤ K := by exact_mod_cast hK
  have hδ' : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hR : 0 < (K : ℝ) * (δ : ℝ) := mul_pos (by linarith) hδ'
  have hL : 0 < L := by linarith
  have h3 : 3 * (δ : ℝ) ≤ (K : ℝ) * (δ : ℝ) / 8 := by nlinarith
  refine ⟨axisTube δ (c + ((L / 8) • axis₀ + (3 * (δ : ℝ)) • axis₁)), axisTube δ c, ?_,
    obstruction_tubes_essDistinct (by linarith),
    obstruction_start_mem_ball hL (by positivity) (by linarith), rfl⟩
  intro hbody
  have hne := not_isEssentiallyDistinct_obstruction (c := c) hR hL hL1 (by positivity) h3
  have hc := hbody hne ⟨obstruction_mem_capsule hL hL1, Metric.mem_ball_self hr⟩
  exact obstruction_not_mem_capsuleAt hL hL1 K (by linarith) hc

/-! ### At the fold's own constants -/

/-- `Tube.le_volume.c 3 = 4π/9`. -/
theorem le_volume_c_three : ((Tube.le_volume.c 3 : NNReal) : ℝ) = 4 * Real.pi / 9 := by
  change Real.sqrt Real.pi ^ 3 / Real.Gamma (((3 : ℕ) : ℝ) / 2 + 1) / 3 = _
  have h1 : ((3 : ℕ) : ℝ) / 2 + 1 = (1 / 2 + 1) + 1 := by norm_num
  rw [h1, Real.Gamma_add_one (by norm_num), Real.Gamma_add_one (by norm_num),
    Real.Gamma_one_half_eq]
  have hpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have hsq : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
  field_simp
  nlinarith [hsq]

theorem le_volume_c_three_le_two : ((Tube.le_volume.c 3 : NNReal) : ℝ) ≤ 2 := by
  rw [le_volume_c_three]
  linarith [Real.pi_le_four]

/-- `73 ≤ K′₀`: the fold's dilate constant is far above `24`. -/
theorem seventy_three_le_edComparabilityConstant : 73 ≤ edComparabilityConstant := by
  rw [edComparabilityConstant_eq]
  have hc0 : (0 : ℝ) < ((Tube.le_volume.c 3 : NNReal) : ℝ) := by
    exact_mod_cast Tube.le_volume.c_pos 3
  have hc2 := le_volume_c_three_le_two
  have h : (64 : ℝ) ≤ 2 * 4 ^ 3 / ((Tube.le_volume.c 3 : NNReal) : ℝ) := by
    rw [le_div_iff₀ hc0]
    nlinarith
  linarith

theorem twentyFour_le_edDilateConstant : 24 ≤ edDilateConstant := by
  rw [← NNReal.coe_le_coe, coe_edDilateConstant]
  have := seventy_three_le_edComparabilityConstant
  norm_num
  linarith

/-- **The obstruction at the fold's own constants.** For every `cfg` satisfying the fold's radius
floor `edFoldRadiusConstant · δ ≤ r₁`, every centre `c` and every localisation radius `r > 0`,
there are two **essentially distinct** `δ`-tubes, both meeting `ball c (r₁/16)`, whose
`edDilateConstant`-dilated capsules at `c` are **not** essentially distinct and for which the
containment clause of `SharpCapsuleAlignment` fails at `r`. In particular no localisation
`r₁/N` rescues (C1). -/
theorem exists_obstruction_at_fold_constants (cfg : VeryNotSticky.{u})
    (hrad : ((edFoldRadiusConstant : NNReal) : ℝ) * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ))
    (c : E3) {r : ℝ} (hr : 0 < r) :
    ∃ Ti Tj : Tube cfg.δ E3,
      ¬ CapsuleAlignmentBody edDilateConstant Ti Tj c ((cfg.r₁ : ℝ) / 4) r ∧
        IsEssentiallyDistinct Ti.carrier Tj.carrier ∧
        Ti.x ∈ ball c ((cfg.r₁ : ℝ) / 16) ∧ Tj.x = c := by
  have hK4 : (4 : ℝ) < ((edDilateConstant : NNReal) : ℝ) := by
    exact_mod_cast four_lt_edDilateConstant
  have hδ' : (0 : ℝ) < (cfg.δ : ℝ) := by exact_mod_cast cfg.hδ
  have hrad' : 8 * ((edDilateConstant : NNReal) : ℝ) ^ 2 * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ) := by
    have : ((edFoldRadiusConstant : NNReal) : ℝ) = 8 * ((edDilateConstant : NNReal) : ℝ) ^ 2 := by
      simp [edFoldRadiusConstant]
    rwa [this] at hrad
  have hRL : 8 * (((edDilateConstant : NNReal) : ℝ) * (cfg.δ : ℝ)) < (cfg.r₁ : ℝ) / 4 := by
    have hKδ : 0 < ((edDilateConstant : NNReal) : ℝ) * (cfg.δ : ℝ) := mul_pos (by linarith) hδ'
    have h32 : 32 * (((edDilateConstant : NNReal) : ℝ) * (cfg.δ : ℝ)) <
        8 * ((edDilateConstant : NNReal) : ℝ) ^ 2 * (cfg.δ : ℝ) := by
      nlinarith [mul_pos hKδ (by linarith : (0 : ℝ) < ((edDilateConstant : NNReal) : ℝ) - 4)]
    linarith
  have hL1 : 2 * ((cfg.r₁ : ℝ) / 4) ≤ 1 := by linarith [r₁_le_one cfg]
  obtain ⟨Ti, Tj, h1, h2, h3, h4⟩ := not_capsuleAlignmentBody_of_essDistinct cfg.hδ
    edDilateConstant twentyFour_le_edDilateConstant c hL1 hRL hr
  refine ⟨Ti, Tj, h1, h2, ?_, h4⟩
  convert h3 using 2
  ring

end Kakeya.VeryNotSticky
