import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic

open MeasureTheory ENNReal Set

namespace Geometry

/-!
# Prékopa-Leindler Inequality — Inductive Step

Proves that if the Prékopa-Leindler inequality holds on a real vector space α
with measure μ, then it holds on α × ℝ with product measure μ ⊗ volume.

This is the inductive step for proving PL on ℝⁿ by induction on dimension.

## Proof

Given f, g, h : α × ℝ → ℝ≥0∞ satisfying the PL condition, define the
fiber integrals:
  F(x₁) = ∫ f(x₁, t) dt
  G(y₁) = ∫ g(y₁, t) dt
  H(z₁) = ∫ h(z₁, t) dt

For fixed x₁, y₁ ∈ α, the 1D PL condition holds for the slices
f(x₁, ·), g(y₁, ·), h((1-λ)x₁+λy₁, ·). Applying 1D PL gives:
  H((1-λ)x₁ + λy₁) ≥ F(x₁)^(1-λ) · G(y₁)^λ

This is precisely the PL condition for F, G, H on α. Applying the
inductive hypothesis (PL on α) and Fubini's theorem yields the result.

## Whiteprint node

Supports the `prekopa_leindler` node in the BM proof chain.
-/

section PLInduction

variable {α : Type*} [NormedAddCommGroup α] [NormedSpace ℝ α]
  [MeasurableSpace α] [BorelSpace α] {μ : Measure α}

/-- The Prékopa-Leindler property for a measure on a real vector space.

If `h((1-λ)x + λy) ≥ f(x)^(1-λ) * g(y)^λ` for all x,y, then
`∫ h ≥ (∫ f)^(1-λ) * (∫ g)^λ`. -/
def PrekopaLeindlerProp (μ : Measure α) : Prop :=
  ∀ (lam : ℝ) (hlam1 : 0 < lam) (hlam2 : lam < 1)
    (f g h : α → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g) (hh : Measurable h),
    (∀ x y, h ((1 - lam) • x + lam • y) ≥ f x ^ (1 - lam) * g y ^ lam) →
    ∫⁻ z, h z ∂μ ≥ (∫⁻ x, f x ∂μ) ^ (1 - lam) * (∫⁻ y, g y ∂μ) ^ lam

/-- **Inductive step**: If PL holds on α and on ℝ, then PL holds on
α × ℝ with the product measure μ ⊗ volume. -/
theorem prekopa_leindler_prod (hPL : PrekopaLeindlerProp μ)
    (hPL1D : PrekopaLeindlerProp (volume : Measure ℝ)) :
    PrekopaLeindlerProp (Measure.prod μ (volume : Measure ℝ)) := by
  intro lam hlam1 hlam2 f g h hf hg hh hcond

  -- Fiber integrals
  let F : α → ℝ≥0∞ := fun x₁ => ∫⁻ t : ℝ, f (x₁, t)
  let G : α → ℝ≥0∞ := fun y₁ => ∫⁻ t : ℝ, g (y₁, t)
  let H : α → ℝ≥0∞ := fun z₁ => ∫⁻ t : ℝ, h (z₁, t)

  -- Measurability of fiber integrals (volume on ℝ is SFinite)
  have hF_meas : Measurable F := hf.lintegral_prod_right'
  have hG_meas : Measurable G := hg.lintegral_prod_right'
  have hH_meas : Measurable H := hh.lintegral_prod_right'

  -- PL condition for F, G, H on α, obtained by applying 1D PL to each fiber
  have hcond_alpha : ∀ (x₁ y₁ : α),
      H ((1 - lam) • x₁ + lam • y₁) ≥ F x₁ ^ (1 - lam) * G y₁ ^ lam := by
    intro x₁ y₁
    let f_slice : ℝ → ℝ≥0∞ := fun s => f (x₁, s)
    let g_slice : ℝ → ℝ≥0∞ := fun t => g (y₁, t)
    let h_slice : ℝ → ℝ≥0∞ := fun u => h ((1 - lam) • x₁ + lam • y₁, u)

    have hf_slice : Measurable f_slice := by
      have h1 : Measurable (fun s : ℝ => (x₁, s)) := by fun_prop
      exact hf.comp h1
    have hg_slice : Measurable g_slice := by
      have h1 : Measurable (fun t : ℝ => (y₁, t)) := by fun_prop
      exact hg.comp h1
    have hh_slice : Measurable h_slice := by
      have h1 : Measurable (fun u : ℝ => ((1 - lam) • x₁ + lam • y₁, u)) := by fun_prop
      exact hh.comp h1

    have hcond_1d : ∀ (s t : ℝ),
        h_slice ((1 - lam) * s + lam * t) ≥
        f_slice s ^ (1 - lam) * g_slice t ^ lam := by
      intro s t
      simpa [f_slice, g_slice, h_slice] using hcond (x₁, s) (y₁, t)

    exact hPL1D lam hlam1 hlam2 f_slice g_slice h_slice
      hf_slice hg_slice hh_slice hcond_1d

  -- Apply PL on α to F, G, H
  have h_main : ∫⁻ z₁, H z₁ ∂μ ≥
      (∫⁻ x₁, F x₁ ∂μ) ^ (1 - lam) * (∫⁻ y₁, G y₁ ∂μ) ^ lam :=
    hPL lam hlam1 hlam2 F G H hF_meas hG_meas hH_meas hcond_alpha

  -- Fubini: ∫⁻ x₁, ∫⁻ t, h(x₁,t) = ∫⁻ p, h(p) over product measure
  have hFubini_H : ∫⁻ z₁, H z₁ ∂μ = ∫⁻ z : α × ℝ, h z ∂Measure.prod μ (volume : Measure ℝ) := by
    have hH_def : ∫⁻ z₁, H z₁ ∂μ = ∫⁻ z₁, ∫⁻ t : ℝ, h (z₁, t) ∂volume ∂μ := by rfl
    rw [hH_def]
    have hh_ae : AEMeasurable h (Measure.prod μ (volume : Measure ℝ)) := by
      refine' ⟨h, hh, _⟩
      filter_upwards with x <;> rfl
    exact (MeasureTheory.lintegral_prod h hh_ae).symm

  have hFubini_F : ∫⁻ x₁, F x₁ ∂μ = ∫⁻ z : α × ℝ, f z ∂Measure.prod μ (volume : Measure ℝ) := by
    have hF_def : ∫⁻ x₁, F x₁ ∂μ = ∫⁻ x₁, ∫⁻ t : ℝ, f (x₁, t) ∂volume ∂μ := by rfl
    rw [hF_def]
    have hf_ae : AEMeasurable f (Measure.prod μ (volume : Measure ℝ)) := by
      refine' ⟨f, hf, _⟩
      filter_upwards with x <;> rfl
    exact (MeasureTheory.lintegral_prod f hf_ae).symm

  have hFubini_G : ∫⁻ y₁, G y₁ ∂μ = ∫⁻ z : α × ℝ, g z ∂Measure.prod μ (volume : Measure ℝ) := by
    have hG_def : ∫⁻ y₁, G y₁ ∂μ = ∫⁻ y₁, ∫⁻ t : ℝ, g (y₁, t) ∂volume ∂μ := by rfl
    rw [hG_def]
    have hg_ae : AEMeasurable g (Measure.prod μ (volume : Measure ℝ)) := by
      refine' ⟨g, hg, _⟩
      filter_upwards with x <;> rfl
    exact (MeasureTheory.lintegral_prod g hg_ae).symm

  rw [hFubini_H, hFubini_F, hFubini_G] at h_main
  exact h_main

/-- Transfer PL along a measure-preserving linear equivalence.

If `e : α ≃ₗ[ℝ] β` preserves the measure and PL holds on α, then PL holds on β. -/
theorem prekopa_leindler_transfer {β : Type*}
    [NormedAddCommGroup β] [NormedSpace ℝ β]
    [MeasurableSpace β] [BorelSpace β] {ν : Measure β}
    (e : α ≃L[ℝ] β) (hme : MeasurePreserving e μ ν)
    (hPL : PrekopaLeindlerProp μ) : PrekopaLeindlerProp ν := by
  intro lam hlam1 hlam2 f g h hf hg hh hcond

  let f' : α → ℝ≥0∞ := f ∘ e
  let g' : α → ℝ≥0∞ := g ∘ e
  let h' : α → ℝ≥0∞ := h ∘ e

  have he_meas : Measurable (e : α → β) := e.continuous.measurable
  have hf' : Measurable f' := hf.comp he_meas
  have hg' : Measurable g' := hg.comp he_meas
  have hh' : Measurable h' := hh.comp he_meas

  have hcond' : ∀ (x y : α),
      h' ((1 - lam) • x + lam • y) ≥ f' x ^ (1 - lam) * g' y ^ lam := by
    intro x y
    have h1 : e ((1 - lam) • x + lam • y) = (1 - lam) • e x + lam • e y := by
      rw [e.map_add, e.map_smul, e.map_smul]
    simpa [f', g', h', h1] using hcond (e x) (e y)

  have h_main := hPL lam hlam1 hlam2 f' g' h' hf' hg' hh' hcond'

  have h_int_f : ∫⁻ x, f' x ∂μ = ∫⁻ y, f y ∂ν := hme.lintegral_comp hf
  have h_int_g : ∫⁻ x, g' x ∂μ = ∫⁻ y, g y ∂ν := hme.lintegral_comp hg
  have h_int_h : ∫⁻ x, h' x ∂μ = ∫⁻ y, h y ∂ν := hme.lintegral_comp hh

  rw [h_int_h, h_int_f, h_int_g] at h_main
  exact h_main

end PLInduction

end Geometry
