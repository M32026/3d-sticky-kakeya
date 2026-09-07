import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.GlobalProjectionHelpers

/-!
# General scaling invariance for PureWZ2 paper AD sets

If `S` is AD at scale `delta`, then `c • S` is AD at scale `c * delta` with the
same constant `C`, for any `c > 0`.

This is the mathematically natural scaling law: scaling the ambient space by `c`
scales the AD scale by `c` and preserves the covering-number constant.

This differs from `PureWZ2PaperADSet1.scale` in `GlobalProjectionHelpers.lean`,
which preserves the *same* scale `delta` for `c ∈ [1/4, 4]` at the cost of a
constant factor `100`. The general lemma here is useful for the anchored
rescaling proof where the factor may lie outside `[1/4, 4]`.

## Proof

For any `rho' ≥ c * delta`, set `rho := rho' / c ≥ delta`. An interval
`[left', left' + length']` in the scaled set corresponds to
`[left'/c, left'/c + length'/c]` in the original. The external covering number
at scale `rho'` of `c • A` is bounded by the covering number at scale `rho` of
`A` (via `externalCoveringNumber_scale_image`). The ratio
`length'/rho' = (length'/c)/(rho'/c) = length/rho` is preserved, so the AD
bound transfers directly.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set ENNReal

attribute [local instance] Classical.propDecidable

/-- General scaling invariance: scaling the set by `c > 0` scales the AD
scale by `c` and preserves the constant. -/
lemma PureWZ2PaperADSet1.scale_general
    {S : Set ℝ} {delta alpha : ℝ} {C : ENNReal}
    (hAD : PureWZ2PaperADSet1 S delta alpha C)
    (c : ℝ) (hc_pos : 0 < c) :
    PureWZ2PaperADSet1 ((fun x : ℝ => c * x) '' S) (c * delta) alpha C := by
  rcases hAD with ⟨hδ_pos, hα_pos, hα_one, hC_one, hC_top, hcover⟩
  have hcd_pos : 0 < c * delta := mul_pos hc_pos hδ_pos
  refine ⟨hcd_pos, hα_pos, hα_one, hC_one, hC_top, ?_⟩
  intro rho' hrho' hcd_rho' left' length' hrho'_length'
  set rho : ℝ := rho' / c with hrho_def
  have hrho_nonneg : 0 ≤ rho := by positivity
  have hdelta_rho : delta ≤ rho := by
    dsimp only [rho]
    have h : c * delta ≤ rho' := hcd_rho'
    have h2 : delta ≤ rho' / c := by
      calc delta = (c * delta) / c := by field_simp [hc_pos.ne'] <;> ring
        _ ≤ rho' / c := by gcongr
    exact h2
  set left : ℝ := left' / c with hleft_def
  set length : ℝ := length' / c with hlength_def
  have hrho_length : rho ≤ length := by
    dsimp only [rho, length]
    have h : rho' ≤ length' := hrho'_length'
    gcongr
  set A : Set ℝ := S ∩ Set.Icc left (left + length) with hA_def
  set S' : Set ℝ := (fun x : ℝ => c * x) '' S with hS'_def
  set B : Set ℝ := S' ∩ Set.Icc left' (left' + length') with hB_def
  have hB_eq : B = (fun x : ℝ => c * x) '' A := by
    ext z
    simp only [hB_def, hS'_def, hA_def, Set.mem_inter_iff, Set.mem_image, Set.mem_Icc]
    constructor
    · rintro ⟨⟨x, hxS, rfl⟩, h1, h2⟩
      have h3 : left ≤ x := by
        dsimp only [left]
        calc left' / c ≤ (c * x) / c := by gcongr
          _ = x := by field_simp [hc_pos.ne'] <;> ring
      have h4 : x ≤ left + length := by
        dsimp only [left, length]
        calc x = (c * x) / c := by field_simp [hc_pos.ne'] <;> ring
          _ ≤ (left' + length') / c := by gcongr
          _ = left' / c + length' / c := by rw [add_div]
      exact ⟨x, ⟨hxS, h3, h4⟩, rfl⟩
    · rintro ⟨x, ⟨hxS, h1, h2⟩, rfl⟩
      have h3 : left' ≤ c * x := by
        dsimp only [left] at h1
        calc left' = c * (left' / c) := by field_simp [hc_pos.ne'] <;> ring
          _ ≤ c * x := by gcongr
      have h4 : c * x ≤ left' + length' := by
        dsimp only [left, length] at h2
        calc c * x ≤ c * (left' / c + length' / c) := by gcongr
          _ = left' + length' := by
            rw [mul_add] <;> field_simp [hc_pos.ne'] <;> ring
      exact ⟨⟨x, hxS, rfl⟩, h3, h4⟩
  have hrho'_pos : 0 < rho' := by linarith
  have h_scale_img :
      (Metric.externalCoveringNumber ⟨rho', hrho'⟩ B : ENNReal) ≤
      (Metric.externalCoveringNumber ⟨rho, hrho_nonneg⟩ A : ENNReal) := by
    rw [hB_eq]
    have h : Metric.externalCoveringNumber ⟨rho', hrho'⟩ ((fun x : ℝ => c * x) '' A) ≤
        Metric.externalCoveringNumber ⟨rho, hrho_nonneg⟩ A :=
      externalCoveringNumber_scale_image (A := A) (rho := rho') hrho'_pos c hc_pos
    exact_mod_cast h
  have h_main :
      (Metric.externalCoveringNumber ⟨rho, hrho_nonneg⟩ A : ENNReal) ≤
      C * Kakeya.realRpowENN (length / rho) alpha :=
    hcover rho hrho_nonneg hdelta_rho left length hrho_length
  have h_ratio : length / rho = length' / rho' := by
    dsimp only [length, rho]
    field_simp [hc_pos.ne'] <;> ring
  rw [h_ratio] at h_main
  exact le_trans h_scale_img h_main

end Kakeya.Assouad

end
