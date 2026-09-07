/-
Distance function gradient norm.

For d(x) = infDist x C where C is a nonempty closed set:
- d is 1-Lipschitz
- d is differentiable a.e. (Rademacher)
- Where d is differentiable and d(x) > 0, ‖fderiv d x‖ = 1
-/

import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

open MeasureTheory Metric Filter Set

namespace Geometry

variable {n : ℕ}

/-- The distance function is 1-Lipschitz. -/
theorem infDist_lipschitz {C : Set (E n)} :
    LipschitzWith 1 (fun x : E n => infDist x C) :=
  Metric.lipschitz_infDist_pt (s := C)

/-- At any point of differentiability, ‖fderiv d x‖ ≤ 1. -/
theorem norm_fderiv_infDist_le_one {C : Set (E n)} {x : E n}
    (hdiff : DifferentiableAt ℝ (fun x : E n => infDist x C) x) :
    ‖fderiv ℝ (fun x : E n => infDist x C) x‖ ≤ 1 := by
  have h := norm_fderiv_le_of_lipschitz ℝ
    (f := fun x : E n => infDist x C) (x₀ := x) (C := 1) infDist_lipschitz
  simpa using h

/-- Nearest point exists for closed nonempty C in proper space. -/
theorem exists_nearest_point {C : Set (E n)} (hC : IsClosed C)
    (hne : C.Nonempty) {x : E n} (hpos : 0 < infDist x C) :
    ∃ (y : E n), y ∈ C ∧ dist x y = infDist x C := by
  have h := hC.exists_infDist_eq_dist hne x
  rcases h with ⟨y, hyC, h_eq⟩
  exact ⟨y, hyC, h_eq.symm⟩

/-- Where d is differentiable and positive, ‖fderiv d x‖ ≥ 1. -/
theorem norm_fderiv_infDist_ge_one {C : Set (E n)} (hC : IsClosed C)
    (hne : C.Nonempty) {x : E n}
    (hdiff : DifferentiableAt ℝ (fun x : E n => infDist x C) x)
    (hpos : 0 < infDist x C) :
    1 ≤ ‖fderiv ℝ (fun x : E n => infDist x C) x‖ := by
  let d : E n → ℝ := fun x => infDist x C
  let f' := fderiv ℝ d x
  rcases exists_nearest_point hC hne hpos with ⟨y, hyC, hydist⟩
  set v : E n := (d x)⁻¹ • (x - y) with hv_def
  have hv_norm : ‖v‖ = 1 := by
    have h : ‖v‖ = |(d x)⁻¹| * ‖x - y‖ := by
      rw [hv_def, norm_smul] <;> rfl
    rw [h]
    have h3 : ‖x - y‖ = d x := by simpa [dist_eq_norm] using hydist
    rw [h3]
    have h4 : 0 < d x := hpos
    have h5 : |(d x)⁻¹| = (d x)⁻¹ := abs_of_pos (inv_pos.mpr h4)
    rw [h5]
    field_simp [h4.ne'] <;> ring
  have h3 : (d x) • v = x - y := by
    rw [hv_def]
    have h6 : (d x) • ((d x)⁻¹ • (x - y)) = ((d x) * (d x)⁻¹) • (x - y) := by
      rw [smul_smul]
    rw [h6]
    have h7 : (d x) * (d x)⁻¹ = 1 := by
      have h8 : d x ≠ 0 := hpos.ne'
      field_simp [h8]
      <;> exact h8
    rw [h7, one_smul]
  have h1 : ∀ (s : ℝ), 0 < s → s < d x → d (x - s • v) ≤ d x - s := by
    intro s hs hlt
    have h4 : (x - s • v) - y = (d x - s) • v := by
      calc
        (x - s • v) - y = (x - y) - s • v := by abel
        _ = (d x) • v - s • v := by rw [←h3]
        _ = (d x - s) • v := by rw [←sub_smul]
    have h2 : ‖(x - s • v) - y‖ = d x - s := by
      rw [h4, norm_smul, Real.norm_eq_abs]
      have h6 : 0 ≤ d x - s := by linarith
      rw [abs_of_nonneg h6, hv_norm] <;> linarith
    have h5 : d (x - s • v) ≤ ‖(x - s • v) - y‖ :=
      infDist_le_dist_of_mem hyC
    rw [h2] at h5
    exact h5
  let g : ℝ → E n := fun s => x - s • v
  have hg_deriv : HasDerivAt g (-v) 0 := by
    have h1 : HasDerivAt (fun s : ℝ => s • v) v 0 := by
      have h2 : HasDerivAt (fun s : ℝ => s • v) ((1 : ℝ) • v) 0 :=
        (hasDerivAt_id (0 : ℝ)).smul_const v
      have h3 : (1 : ℝ) • v = v := one_smul ℝ v
      rw [h3] at h2
      exact h2
    exact h1.const_sub x
  have hg : HasFDerivAt g (ContinuousLinearMap.toSpanSingleton ℝ (-v)) 0 :=
    hg_deriv.hasFDerivAt
  have h_fderiv : HasFDerivAt d f' x := hdiff.hasFDerivAt
  have h_g0 : g 0 = x := by simp [g]
  have h_fderiv' : HasFDerivAt d f' (g 0) := by
    rw [h_g0] <;> exact h_fderiv
  have h_comp_fderiv : HasFDerivAt (d ∘ g)
      (f'.comp (ContinuousLinearMap.toSpanSingleton ℝ (-v))) 0 :=
    HasFDerivAt.comp (x := 0) h_fderiv' hg
  have h_comp : HasDerivAt (d ∘ g)
      ((f'.comp (ContinuousLinearMap.toSpanSingleton ℝ (-v))) 1) 0 :=
    h_comp_fderiv.hasDerivAt
  have h_val : (f'.comp (ContinuousLinearMap.toSpanSingleton ℝ (-v))) 1
      = f' (-v) := by simp [f'] <;> rfl
  rw [h_val] at h_comp
  have h_neg : f' (-v) = -f' v := by exact map_neg f' v
  rw [h_neg] at h_comp
  have h6 : ∀ (s : ℝ), 0 < s → s < d x →
      ((d ∘ g) s - (d ∘ g) 0) / s ≤ -1 := by
    intro s hs hlt
    have h7 : d (g s) ≤ d x - s := h1 s hs hlt
    have h8 : (d (g s) - d x) / s ≤ -1 := by
      have h9 : (d (g s) - d x) / s ≤ ((d x - s) - d x) / s := by gcongr
      have h10 : ((d x - s) - d x) / s = -1 := by
        field_simp [hs.ne'] <;> linarith
      rw [h10] at h9
      exact h9
    simpa [g] using h8
  have h_nhds : Set.Ioo (0 : ℝ) (d x) ∈ nhdsWithin 0 (Set.Ioi 0) := by
    apply mem_nhdsWithin.mpr
    refine ⟨Set.Iio (d x), isOpen_Iio, ?_, ?_⟩
    · exact hpos
    · intro y hy
      exact ⟨hy.2, hy.1⟩
  have h_event : ∀ᶠ (s : ℝ) in nhdsWithin 0 (Set.Ioi 0),
      ((d ∘ g) s - (d ∘ g) 0) / s ≤ -1 := by
    filter_upwards [h_nhds] with s hs
    exact h6 s hs.1 hs.2
  have h_tendsto1 : Tendsto (slope (d ∘ g) 0)
      (nhdsWithin 0 {0}ᶜ) (nhds (-f' v)) :=
    h_comp.tendsto_slope
  have h_le_nhds : nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhdsWithin (0 : ℝ) {0}ᶜ := by
    apply nhdsWithin_mono
    intro s hs
    exact ne_of_gt hs
  have h_tendsto : Tendsto (slope (d ∘ g) 0)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (-f' v)) :=
    h_tendsto1.mono_left h_le_nhds
  have h_slope_eq : ∀ (s : ℝ), slope (d ∘ g) 0 s = ((d ∘ g) s - (d ∘ g) 0) / s := by
    intro s
    simp [slope]
    <;> ring
  have h_event' : ∀ᶠ (s : ℝ) in nhdsWithin 0 (Set.Ioi 0),
      slope (d ∘ g) 0 s ≤ -1 := by
    filter_upwards [h_event] with s hs
    rw [h_slope_eq s]
    exact hs
  have h11 : -f' v ≤ -1 := le_of_tendsto h_tendsto h_event'
  have h12 : 1 ≤ f' v := by linarith
  have h13 : |f' v| ≤ ‖f'‖ * ‖v‖ := f'.le_opNorm v
  rw [hv_norm] at h13
  have h14 : |f' v| ≤ ‖f'‖ := by simpa using h13
  have h15 : 0 ≤ f' v := by linarith
  have h16 : |f' v| = f' v := abs_of_nonneg h15
  rw [h16] at h14
  linarith

/-- Where d is differentiable and positive, ‖fderiv d x‖ = 1. -/
theorem norm_fderiv_infDist_eq_one {C : Set (E n)} (hC : IsClosed C)
    (hne : C.Nonempty) {x : E n}
    (hdiff : DifferentiableAt ℝ (fun x : E n => infDist x C) x)
    (hpos : 0 < infDist x C) :
    ‖fderiv ℝ (fun x : E n => infDist x C) x‖ = 1 := by
  have h_le : ‖fderiv ℝ (fun x : E n => infDist x C) x‖ ≤ 1 :=
    norm_fderiv_infDist_le_one hdiff
  have h_ge : 1 ≤ ‖fderiv ℝ (fun x : E n => infDist x C) x‖ :=
    norm_fderiv_infDist_ge_one hC hne hdiff hpos
  exact le_antisymm h_le h_ge

/-- a.e., d differentiable and where positive, ‖fderiv d x‖ = 1. -/
theorem ae_norm_fderiv_infDist_eq_one {C : Set (E n)} (hC : IsClosed C)
    (hne : C.Nonempty) :
    ∀ᵐ (x : E n) ∂volume,
      (0 < infDist x C) → ‖fderiv ℝ (fun x : E n => infDist x C) x‖ = 1 := by
  have h_ae_diff : ∀ᵐ (x : E n) ∂volume,
      DifferentiableAt ℝ (fun x : E n => infDist x C) x :=
    infDist_lipschitz.ae_differentiableAt
  filter_upwards [h_ae_diff] with x hdiff hpos
  exact norm_fderiv_infDist_eq_one hC hne hdiff hpos

end Geometry
