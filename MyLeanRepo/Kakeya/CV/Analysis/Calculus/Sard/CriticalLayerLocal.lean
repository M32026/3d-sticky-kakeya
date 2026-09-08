/-
Copyright (c) 2026 SeedProver. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SeedProver
-/
module

public import MyLeanRepo.Kakeya.CV.Analysis.Calculus.Sard.CriticalSet
public import MyLeanRepo.Kakeya.CV.Analysis.Calculus.Sard.LocalStraighteningHomeomorph
public import MyLeanRepo.Kakeya.CV.Analysis.Calculus.Sard.CoordinateHyperplane
public import MyLeanRepo.Kakeya.CV.Analysis.Calculus.Sard.LocalCriticalImage
public import MyLeanRepo.Kakeya.CV.Analysis.Calculus.Sard.Measure

@[expose] public section

namespace ForMathlib.Analysis.Calculus.Sard

open MeasureTheory
open scoped ContDiff

/-- Sub-lemma A: For each `k ≥ 1`, the image of `C k \ C (k + 1)` has measure zero,
where `C k` is the set where all iterated derivatives of order `≤ k` vanish. -/
lemma sub_lemma_A_local {m : ℕ} (k : ℕ) (hk_pos : 1 ≤ k)
    (f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ) (hf : ContDiff ℝ ∞ f)
    (ih : ∀ (g : EuclideanSpace ℝ (Fin m) → ℝ), ContDiff ℝ ∞ g →
      (volume : Measure ℝ) (g '' {x | fderiv ℝ g x = 0}) = 0) :
    (volume : Measure ℝ) (f '' (C f k \ C f (k + 1))) = 0 := by
  have h_main : ∀ (x : EuclideanSpace ℝ (Fin (m + 1))), x ∈ C f k \ C f (k + 1) →
      ∃ (U : Set (EuclideanSpace ℝ (Fin (m + 1)))), U ∈ nhds x ∧
        (volume : Measure ℝ) (f '' ((C f k \ C f (k + 1)) ∩ U)) = 0 := by
    intro x hx
    have hx1 : x ∈ C f k := hx.1
    have hx2 : x ∉ C f (k + 1) := hx.2
    let E := EuclideanSpace ℝ (Fin (m + 1))
    let F := EuclideanSpace ℝ (Fin m)
    have h_main1 : ∃ (h : E → ℝ), ContDiff ℝ ∞ h ∧ fderiv ℝ h x ≠ 0 ∧ ∀ y ∈ C f k, h y = 0 :=
      exists_helper_function k hk_pos x hx1 hx2 hf
    rcases h_main1 with ⟨h, hh, hx_h, h_zero⟩
    have h_pos : 0 < m + 1 := by linarith
    rcases local_straightening_oph h_pos h hh x hx_h with ⟨i, φ, e_phi, hx_in_source, hφ_diff, h_phi_eq, h_prop1, h_strict_exists⟩
    rcases h_strict_exists with ⟨f', h_strict⟩
    have h_fderiv_eq : fderiv ℝ φ x = (f' : E →L[ℝ] E) := h_strict.hasFDerivAt.fderiv
    have h_bij_at_x : Function.Bijective (fderiv ℝ φ x) := by
      rw [h_fderiv_eq]
      exact f'.bijective
    have h_prop : ∀ (y : E), y ∈ e_phi.source → (e_phi y) i = h y := h_prop1
    let S : Set E := {y | Function.Bijective (fderiv ℝ φ y)}
    have h_fderiv_continuous : Continuous (fderiv ℝ φ) := hφ_diff.continuous_fderiv (by simp)
    have hS_open : IsOpen S := by
      let bijective_set : Set (E →L[ℝ] E) := {f' | Function.Bijective f'}
      have h_eq1 : bijective_set = Set.range (fun (f' : E ≃L[ℝ] E) => (f' : E →L[ℝ] E)) := by
        ext f'
        simp only [bijective_set, Set.mem_setOf_eq, Set.mem_range]
        constructor
        · intro h
          have hinj : (f' : E →ₗ[ℝ] E).ker = ⊥ := LinearMap.ker_eq_bot.mpr h.1
          have hsurj : (f' : E →ₗ[ℝ] E).range = ⊤ := LinearMap.range_eq_top.mpr h.2
          let g : E ≃L[ℝ] E := ContinuousLinearEquiv.ofBijective f' hinj hsurj
          refine' ⟨g, _⟩
          exact ContinuousLinearEquiv.coe_ofBijective f' hinj hsurj
        · rintro ⟨g, rfl⟩
          exact g.bijective
      have hGL_open : IsOpen bijective_set := by
        rw [h_eq1]
        exact ContinuousLinearEquiv.isOpen (𝕜 := ℝ)
      have hS_eq : S = (fderiv ℝ φ) ⁻¹' bijective_set := by
        ext y
        simp [S, bijective_set]
        rfl
      rw [hS_eq]
      exact hGL_open.preimage h_fderiv_continuous
    have hx_in_S : x ∈ S := h_bij_at_x
    let U_full : Set E := e_phi.source ∩ S
    have hU_full_open : IsOpen U_full := e_phi.open_source.inter hS_open
    have hx_in_U_full : x ∈ U_full := ⟨hx_in_source, hx_in_S⟩
    have hU_full_nhds : U_full ∈ nhds x := IsOpen.mem_nhds hU_full_open hx_in_U_full
    have hU_full_subset : U_full ⊆ e_phi.source := by
      intro z hz
      exact hz.1
    let V_full : Set E := e_phi '' U_full
    have hV_full_open : IsOpen V_full := OpenPartialHomeomorph.isOpen_image_source_inter e_phi hS_open
    let e1 : E ≃L[ℝ] (Fin (m + 1) → ℝ) := EuclideanSpace.equiv (Fin (m + 1)) ℝ
    let e2 : F ≃L[ℝ] (Fin m → ℝ) := EuclideanSpace.equiv (Fin m) ℝ
    let π : E → F := fun z => e2.symm (pi_drop_coord i (e1 z))
    let ι : F → E := fun w => e1.symm (pi_insert_zero i (e2 w))
    have hpi2 : ∀ (w : F), (e1 (ι w)) i = 0 := by
      intro w
      simp [ι, pi_insert_zero]
    have hpi3 : ∀ (z : E), (e1 z) i = 0 → ι (π z) = z := by
      intro z hz
      have h1 : e1 (ι (π z)) = e1 z := by
        have h2 : e1 (ι (π z)) = pi_insert_zero i (pi_drop_coord i (e1 z)) := by
          simp [ι, π]
        rw [h2]
        exact pi_insert_zero_drop_coord i (e1 z) hz
      exact e1.injective h1
    have h_ι_π : ∀ (w : F), π (ι w) = w := by
      intro w
      have h1 : e2 (π (ι w)) = e2 w := by
        have h2 : e2 (π (ι w)) = pi_drop_coord i (pi_insert_zero i (e2 w)) := by
          simp [ι, π]
        rw [h2]
        exact pi_drop_coord_insert_zero i (e2 w)
      exact e2.injective h1
    have h_ι_contDiff : ContDiff ℝ ∞ ι := by
      have h1 : ContDiff ℝ ∞ (pi_insert_zero i) := pi_insert_zero_contDiff i
      exact e1.symm.contDiff.comp (h1.comp e2.contDiff)
    have h_ι_continuous : Continuous ι := h_ι_contDiff.continuous
    let z₀ : E := e_phi x
    have hz₀_in_V_full : z₀ ∈ V_full := ⟨x, hx_in_U_full, rfl⟩
    have hz₀_i : (e1 z₀) i = 0 := by
      have h_hx : h x = 0 := h_zero x hx1
      have h_eq : (e_phi x) i = h x := h_prop x hx_in_source
      have h1 : (e1 z₀) i = (e_phi x) i := by rfl
      rw [h1, h_eq, h_hx]
    have h_z₀_eq : ι (π z₀) = z₀ := hpi3 z₀ hz₀_i
    let w₀ : F := π z₀
    let W : Set F := {w | ι w ∈ V_full}
    have hW_open : IsOpen W := hV_full_open.preimage h_ι_continuous
    have hw₀_W : w₀ ∈ W := by
      simpa [W, w₀, h_z₀_eq] using hz₀_in_V_full
    have h_strict_all : ∀ (x : E), HasStrictFDerivAt φ (fderiv ℝ φ x) x := by
      intro x
      exact hφ_diff.hasStrictFDerivAt (by simp)
    have h_phi_hasFDerivAt : ∀ (y : E), y ∈ U_full →
        ∃ (f' : E ≃L[ℝ] E), HasStrictFDerivAt φ (f' : E →L[ℝ] E) y := by
      intro y hy
      have h_bij : Function.Bijective (fderiv ℝ φ y) := hy.2
      let f' : E ≃L[ℝ] E :=
        ContinuousLinearEquiv.ofBijective (fderiv ℝ φ y)
          (LinearMap.ker_eq_bot.mpr h_bij.1) (LinearMap.range_eq_top.mpr h_bij.2)
      have h_hasFDeriv_strict : HasStrictFDerivAt φ (f' : E →L[ℝ] E) y := h_strict_all y
      exact ⟨f', h_hasFDeriv_strict⟩
    have h1 : ∀ z ∈ V_full, ContDiffAt ℝ ∞ (e_phi.symm) z := by
      intro z hz
      rcases hz with ⟨y, hy_in_Ufull, rfl⟩
      have hy_in_source : y ∈ e_phi.source := hy_in_Ufull.1
      rcases h_phi_hasFDerivAt y hy_in_Ufull with ⟨f', hf'⟩
      have h_eq_on : ∀ᶠ (z : E) in nhds y, φ z = (e_phi : E → E) z := by
        filter_upwards [IsOpen.mem_nhds e_phi.open_source hy_in_source] with z hz
        exact (h_phi_eq z hz).symm
      have h_eq_on' : ∀ᶠ (z : E) in nhds y, (e_phi : E → E) z = φ z := Filter.EventuallyEq.symm h_eq_on
      have h_hasFDeriv_e_strict : HasStrictFDerivAt (e_phi : E → E) (f' : E →L[ℝ] E) y :=
        hf'.congr_of_eventuallyEq (Filter.EventuallyEq.symm h_eq_on')
      have h_hasFDeriv_e : HasFDerivAt (e_phi : E → E) (f' : E →L[ℝ] E) y :=
        h_hasFDeriv_e_strict.hasFDerivAt
      have h_contDiffAt_φ : ContDiffAt ℝ ∞ φ y := hφ_diff.contDiffAt
      have h_contDiffAt : ContDiffAt ℝ ∞ (e_phi : E → E) y := h_contDiffAt_φ.congr_of_eventuallyEq h_eq_on'
      have h_left_inv : e_phi.symm (e_phi y) = y := e_phi.left_inv hy_in_source
      have h_hasFDeriv' : HasFDerivAt (e_phi : E → E) (f' : E →L[ℝ] E) (e_phi.symm (e_phi y)) := by
        rw [h_left_inv]
        exact h_hasFDeriv_e
      have h_contDiffAt' : ContDiffAt ℝ ∞ (e_phi : E → E) (e_phi.symm (e_phi y)) := by
        rw [h_left_inv]
        exact h_contDiffAt
      exact e_phi.contDiffAt_symm (e_phi.map_source hy_in_source) h_hasFDeriv' h_contDiffAt'
    have h_symm_contDiffOn : ContDiffOn ℝ ∞ (e_phi.symm) V_full := by
      have h_iff : ContDiffOn ℝ ∞ (e_phi.symm) V_full ↔ ∀ z ∈ V_full, ContDiffAt ℝ ∞ (e_phi.symm) z :=
        IsOpen.contDiffOn_iff hV_full_open
      exact h_iff.mpr h1
    let g : F → ℝ := fun w => f (e_phi.symm (ι w))
    have hg : ContDiffOn ℝ ∞ g W := by
      have h1 : ContDiffOn ℝ ∞ (e_phi.symm ∘ ι) W :=
        h_symm_contDiffOn.comp (h_ι_contDiff.contDiffOn) (fun w hw => hw)
      exact hf.contDiffOn.comp h1 (fun _ _ => Set.mem_univ _)
    have h_ind : (volume : Measure ℝ) (g '' {w ∈ W | fderiv ℝ g w = 0}) = 0 :=
      local_critical_image_null ih (hU_open := hW_open) g hg
    let S_set : Set E := (C f k \ C f (k + 1)) ∩ U_full
    have h_subset : f '' S_set ⊆ g '' {w ∈ W | fderiv ℝ g w = 0} := by
      intro y hy
      rcases hy with ⟨y, ⟨hy_C, hy_U⟩, rfl⟩
      have hy_C_k : y ∈ C f k := hy_C.1
      have h_hy : h y = 0 := h_zero y hy_C_k
      have hy_in_source : y ∈ e_phi.source := hy_U.1
      have h4 : (e1 (e_phi y)) i = 0 := by
        have h5 : (e_phi y) i = h y := h_prop y hy_in_source
        have h6 : (e1 (e_phi y)) i = (e_phi y) i := by rfl
        rw [h6, h5, h_hy]
      let z : E := e_phi y
      have hz_in_V_full : z ∈ V_full := ⟨y, hy_U, rfl⟩
      have hz_i : (e1 z) i = 0 := h4
      have h7 : ι (π z) = z := hpi3 z hz_i
      let w : F := π z
      have hw_W : w ∈ W := by
        simpa [W, w, h7] using hz_in_V_full
      have h8 : e_phi.symm (ι w) = y := by
        have h9 : ι w = z := by
          simpa [w] using h7
        rw [h9]
        exact e_phi.left_inv hy_in_source
      have h10 : g w = f y := by
        dsimp only [g]
        rw [h8]
      have h11 : fderiv ℝ f y = 0 := by
        have h12 : iteratedFDeriv ℝ 1 f y = 0 := hy_C_k 1 (by norm_num) (by linarith)
        have h_norm : ‖iteratedFDeriv ℝ 1 f y‖ = ‖fderiv ℝ f y‖ := norm_iteratedFDeriv_one f
        have h13 : ‖iteratedFDeriv ℝ 1 f y‖ = 0 := by
          rw [h12]
          simp
        have h14 : ‖fderiv ℝ f y‖ = 0 := by
          rw [←h_norm, h13]
        exact norm_eq_zero.mp h14
      have h_ι_diff : Differentiable ℝ ι := h_ι_contDiff.differentiable (by simp)
      have h_symm_diff : DifferentiableAt ℝ (e_phi.symm) (ι w) :=
        (h_symm_contDiffOn.differentiableOn (by simp)).differentiableAt
          (IsOpen.mem_nhds hV_full_open hw_W)
      have h_fderiv_g : fderiv ℝ g w = 0 := by
        have h_diff1 : DifferentiableAt ℝ f (e_phi.symm (ι w)) :=
          hf.differentiable (by simp) (e_phi.symm (ι w))
        have h_diff2 : DifferentiableAt ℝ (e_phi.symm ∘ ι) w :=
          h_symm_diff.comp w (h_ι_diff.differentiableAt)
        have h_chain : fderiv ℝ g w = (fderiv ℝ f (e_phi.symm (ι w))).comp (fderiv ℝ (e_phi.symm ∘ ι) w) := by
          exact fderiv_comp w h_diff1 h_diff2
        rw [h_chain, h8, h11]
        simp
      have h15 : w ∈ {w ∈ W | fderiv ℝ g w = 0} := ⟨hw_W, h_fderiv_g⟩
      exact ⟨w, h15, h10⟩
    have h_final : (volume : Measure ℝ) (f '' S_set) = 0 :=
      measure_mono_null h_subset h_ind
    exact ⟨U_full, hU_full_nhds, h_final⟩
  exact measure_zero_of_locally_null (h := h_main)


end ForMathlib.Analysis.Calculus.Sard
