module

public import MyLeanRepo.Kakeya.CV.Analysis.Calculus.Sard.TaylorEstimate

@[expose] public section

namespace ForMathlib.Analysis.Calculus.Sard

open MeasureTheory
open scoped ContDiff

variable {m : ℕ}

/-- General Taylor estimate: if all iterated derivatives of `f` of order `1 ≤ j ≤ k` vanish at `x`,
then `‖f y - f x‖ ≤ C * ‖y - x‖^(k + 1)` for `y` in a convex compact set containing `x`.
This works for any normed space codomain `F`. -/
lemma taylor_estimate_general {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (k : ℕ)
    {K : Set (EuclideanSpace ℝ (Fin m))} (hK : Convex ℝ K) (hK' : IsCompact K)
    {f : EuclideanSpace ℝ (Fin m) → F} (hf : ContDiff ℝ (k + 1) f)
    {x : EuclideanSpace ℝ (Fin m)} (hx : x ∈ K)
    (hderiv : ∀ j, 1 ≤ j → j ≤ k → iteratedFDeriv ℝ j f x = 0) :
    ∃ C : ℝ, ∀ y ∈ K, ‖f y - f x‖ ≤ C * ‖y - x‖ ^ (k + 1) := by
  induction k generalizing F with
  | zero =>
    -- Base case k = 0: just the mean value theorem (no derivatives need to vanish)
    have h1 : ContDiff ℝ 1 f := by simpa using hf
    have h1' : ContDiffOn ℝ 1 f K := h1.contDiffOn
    have h_lip : ∃ (C₁ : NNReal), LipschitzOnWith C₁ f K :=
      h1'.exists_lipschitzOnWith (by norm_num) hK hK'
    rcases h_lip with ⟨C₁, hC₁⟩
    have h_dist_le : ∀ (x : _), x ∈ K → ∀ (y : _), y ∈ K → dist (f x) (f y) ≤ (C₁ : ℝ) * dist x y :=
      lipschitzOnWith_iff_dist_le_mul.mp hC₁
    use (C₁ : ℝ)
    intro y hy
    have h4 : dist (f y) (f x) ≤ (C₁ : ℝ) * dist y x := h_dist_le y hy x hx
    have h6 : ‖f y - f x‖ = dist (f y) (f x) := by rw [dist_eq_norm]
    have h7 : ‖y - x‖ = dist y x := by rw [dist_eq_norm]
    rw [h6, h7]
    simpa [pow_one] using h4
  | succ k ih =>
    -- Inductive step
    let g : EuclideanSpace ℝ (Fin m) → (EuclideanSpace ℝ (Fin m) →L[ℝ] F) := fderiv ℝ f
    have h1 : ContDiff ℝ (k + 1) g := by
      have h11 : ContDiff ℝ ((k + 1) + 1) f := by simpa using hf
      have h12 := (contDiff_succ_iff_fderiv.mp h11)
      exact h12.2.2
    have hderiv' : ∀ j, 1 ≤ j → j ≤ k → iteratedFDeriv ℝ j g x = 0 := by
      intro j hj1 hj2
      have h10 : 1 ≤ j + 1 := by linarith
      have h11 : j + 1 ≤ k + 1 := by linarith
      have h12 : iteratedFDeriv ℝ (j + 1) f x = 0 := hderiv (j + 1) h10 h11
      have h9 : iteratedFDeriv ℝ (j + 1) f x =
          (continuousMultilinearCurryRightEquiv' ℝ j (EuclideanSpace ℝ (Fin m)) F).symm
            (iteratedFDeriv ℝ j g x) := by
        exact iteratedFDeriv_succ_eq_comp_right (f := f) (n := j)
      have h13 : (continuousMultilinearCurryRightEquiv' ℝ j (EuclideanSpace ℝ (Fin m)) F).symm
          (iteratedFDeriv ℝ j g x) = 0 := by
        rw [←h9, h12]
      have h14 : iteratedFDeriv ℝ j g x = 0 := by
        exact (continuousMultilinearCurryRightEquiv' ℝ j (EuclideanSpace ℝ (Fin m)) F).symm.injective h13
      exact h14
    have h_ih : ∃ (C₁ : ℝ), ∀ (y : EuclideanSpace ℝ (Fin m)), y ∈ K →
        ‖g y - g x‖ ≤ C₁ * ‖y - x‖ ^ (k + 1) :=
      ih (F := (EuclideanSpace ℝ (Fin m) →L[ℝ] F)) (f := g) h1 hderiv'
    rcases h_ih with ⟨C₁, hC₁⟩
    let C₁' : ℝ := max C₁ 0
    have hC₁' : ∀ (y : EuclideanSpace ℝ (Fin m)), y ∈ K →
        ‖g y - g x‖ ≤ C₁' * ‖y - x‖ ^ (k + 1) := by
      intro y hy
      have h_pos : 0 ≤ ‖y - x‖ ^ (k + 1) := by positivity
      calc
        ‖g y - g x‖ ≤ C₁ * ‖y - x‖ ^ (k + 1) := hC₁ y hy
        _ ≤ max C₁ 0 * ‖y - x‖ ^ (k + 1) := by
          gcongr
          exact le_max_left C₁ 0
    have hC₁'_nonneg : 0 ≤ C₁' := by
      simp [C₁']
    have h_diff : Differentiable ℝ f := by
      have h : ContDiff ℝ 1 f := hf.of_le (by simp)
      exact h.differentiable (by simp)
    have h_gx_zero : g x = 0 := by
      have h7 : iteratedFDeriv ℝ 1 f x = 0 := hderiv 1 (by norm_num) (by norm_num)
      have h_norm : ‖iteratedFDeriv ℝ 1 f x‖ = ‖g x‖ := by
        exact norm_iteratedFDeriv_one f
      have h8 : ‖iteratedFDeriv ℝ 1 f x‖ = 0 := by
        rw [h7]
        simp
      have h9 : ‖g x‖ = 0 := by linarith [h_norm]
      exact norm_eq_zero.mp h9
    use C₁'
    intro y hy
    let S := segment ℝ x y
    have hS_sub : S ⊆ K := hK.segment_subset hx hy
    have h4 : ∀ z ∈ S, ‖g z‖ ≤ C₁' * ‖z - x‖ ^ (k + 1) := by
      intro z hz
      have hzK : z ∈ K := hS_sub hz
      have h5 : ‖g z - g x‖ ≤ C₁' * ‖z - x‖ ^ (k + 1) := hC₁' z hzK
      rw [h_gx_zero, sub_zero] at h5
      exact h5
    have h4' : ∀ z ∈ S, ‖g z‖ ≤ C₁' * ‖y - x‖ ^ (k + 1) := by
      intro z hz
      have h5 : ‖z - x‖ ≤ ‖y - x‖ := norm_sub_le_of_mem_segment hz
      have h6 : ‖g z‖ ≤ C₁' * ‖z - x‖ ^ (k + 1) := h4 z hz
      calc
        ‖g z‖ ≤ C₁' * ‖z - x‖ ^ (k + 1) := h6
        _ ≤ C₁' * ‖y - x‖ ^ (k + 1) := by
          gcongr
    have h_main : ‖f y - f x‖ ≤ C₁' * ‖y - x‖ ^ (k + 1) * ‖y - x‖ := by
      have h_conv : Convex ℝ S := convex_segment _ _
      exact h_conv.norm_image_sub_le_of_norm_fderiv_le
        (fun z _ => h_diff.differentiableAt) h4' (by exact left_mem_segment ℝ x y) (by exact right_mem_segment ℝ x y)
    have h_final : ‖f y - f x‖ ≤ C₁' * ‖y - x‖ ^ (k + 2) := by
      have h10 : C₁' * ‖y - x‖ ^ (k + 1) * ‖y - x‖ = C₁' * ‖y - x‖ ^ (k + 2) := by
        simp [pow_succ]
        ring
      rw [h10] at h_main
      exact h_main
    simpa using h_final


end ForMathlib.Analysis.Calculus.Sard
