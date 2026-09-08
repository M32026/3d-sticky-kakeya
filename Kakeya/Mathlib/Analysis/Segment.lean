/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Mathlib.Analysis.AffineSubspace
public import Kakeya.Mathlib.Analysis.InnerProductSpace
public import Mathlib.Algebra.CharP.Invertible
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Analysis.Normed.Group.Uniform

/-!
# Segment
-/

@[expose] public section

variable
  {E} [NormedAddCommGroup E] [Module ℝ E] [ContinuousSMul ℝ E]

theorem isCompact_segment {x y : E} : IsCompact (segment ℝ x y) := by
  rw [segment_eq_image']
  apply isCompact_Icc.image
  continuity

theorem isClosed_segment {x y : E} : IsClosed (segment ℝ x y) := isCompact_segment.isClosed

omit [ContinuousSMul ℝ E] in
/-- A point of a unit segment `[a,b]` is `midpoint + σ • (b - a)` for some
`σ ∈ [-1/2, 1/2]`. -/
lemma mem_unit_segment_param {a b w : E} (hw : w ∈ segment ℝ a b) :
    ∃ σ : ℝ, |σ| ≤ 1/2 ∧ w = midpoint ℝ a b + σ • (b - a) := by
  rw [segment_eq_image] at hw
  obtain ⟨lam, hlam_mem, hlam_eq⟩ := hw
  obtain ⟨hlam0, hlam1⟩ := hlam_mem
  refine ⟨lam - 1/2, ?_, ?_⟩
  · rw [abs_le]; constructor <;> linarith
  · rw [← hlam_eq]
    have hmid : midpoint ℝ a b = (1/2 : ℝ) • (a + b) := by
      rw [midpoint_eq_smul_add, invOf_eq_inv, one_div]
    rw [hmid]
    change (1 - lam) • a + lam • b = (1/2 : ℝ) • (a + b) + (lam - 1/2) • (b - a)
    rw [smul_add, smul_sub]; module

omit [ContinuousSMul ℝ E] in
/-- **The translate of a segment is the segment of the translated endpoints** (blueprint
`lem:segmentTranslate`).  Mathlib's `segment_translate_image` writes the translation on the
left; the slide maps of `Kakeya.Tube.Dilate` write it on the right. -/
theorem segment_add_right_image (p q w : E) :
    (fun z => z + w) '' segment ℝ p q = segment ℝ (p + w) (q + w) := by
  rw [show (fun z : E => z + w) = fun z : E => w + z by
    funext z
    exact add_comm z w]
  rw [add_comm p w]
  rw [show q + w = w + q by exact add_comm q w]
  exact segment_translate_image ℝ w p q

/-- **A rigid motion matching two unit segments** (blueprint `lem:coreMatchingIsometry`).

Assembled from `exists_linearIsometryEquiv_apply_eq_of_norm_eq` (a linear isometry equivalence
`R` with `R (q - p) = q' - p'`) and `AffineIsometryEquiv.ofLinearIsometryEquiv` (turn it into
`z ↦ p' + R (z - p)`); the image of the segment is then `AffineMap.image_segment`. -/
theorem exists_affineIsometryEquiv_image_segment_eq {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] {p q p' q' : F}
    (h : ‖q - p‖ = ‖q' - p'‖) :
    ∃ Φ : F ≃ᵃⁱ[ℝ] F, Φ p = p' ∧ Φ q = q' ∧ Φ '' segment ℝ p q = segment ℝ p' q' := by
  obtain ⟨R, hR⟩ := exists_linearIsometryEquiv_apply_eq_of_norm_eq h
  let Φ : F ≃ᵃⁱ[ℝ] F := AffineIsometryEquiv.ofLinearIsometryEquiv R p p'
  have hp' : Φ p = p' := by
    rw [AffineIsometryEquiv.ofLinearIsometryEquiv_apply, sub_self, map_zero, add_zero]
  have hq' : Φ q = q' := by
    rw [AffineIsometryEquiv.ofLinearIsometryEquiv_apply, hR]
    abel
  refine ⟨Φ, hp', hq', ?_⟩
  simpa [hp', hq'] using image_segment ℝ (Φ : F →ᵃ[ℝ] F) p q
