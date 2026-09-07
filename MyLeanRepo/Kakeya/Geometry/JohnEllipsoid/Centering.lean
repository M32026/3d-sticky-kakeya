import MyLeanRepo.Kakeya.Geometry.JohnEllipsoid.Basic
import MyLeanRepo.Kakeya.Geometry.JohnEllipsoid.VolumeUtils
import MyLeanRepo.Kakeya.Geometry.JohnEllipsoid.EuclideanUtils
import MyLeanRepo.Kakeya.Geometry.JohnEllipsoid.ConvexHullUtils
import Mathlib.Tactic


noncomputable section

open MeasureTheory
open scoped Pointwise Real InnerProductSpace

namespace JohnEllipsoid

variable {n : ℕ}

/-- Norm squared expansion in a real inner product space. -/
lemma norm_sub_sq_formula (a b : E n) :
    ‖a - b‖ ^ 2 = ‖a‖ ^ 2 - 2 * inner ℝ a b + ‖b‖ ^ 2 := by
  have h1 : ‖a - b‖ ^ 2 = inner ℝ (a - b) (a - b) := by
    rw [← real_inner_self_eq_norm_sq]
  rw [h1]
  have h21 : inner ℝ (a - b) (a - b) = inner ℝ a (a - b) - inner ℝ b (a - b) := by
    rw [inner_sub_left]
  have h22 : inner ℝ a (a - b) = inner ℝ a a - inner ℝ a b := by
    rw [inner_sub_right]
  have h23 : inner ℝ b (a - b) = inner ℝ b a - inner ℝ b b := by
    rw [inner_sub_right]
  rw [h21, h22, h23]
  have h3 : inner ℝ b a = inner ℝ a b := (real_inner_comm b a).symm
  have h4 : inner ℝ a a = ‖a‖ ^ 2 := by rw [real_inner_self_eq_norm_sq]
  have h5 : inner ℝ b b = ‖b‖ ^ 2 := by rw [real_inner_self_eq_norm_sq]
  rw [h3, h4, h5] <;> ring

/-- Scaling linear equivalence x ↦ R • x for R ≠ 0. -/
def scaleEquiv (n : ℕ) {R : ℝ} (hR : R ≠ 0) : E n ≃ₗ[ℝ] E n :=
  LinearEquiv.ofLinear
    (R • (LinearMap.id : E n →ₗ[ℝ] E n))
    (R⁻¹ • (LinearMap.id : E n →ₗ[ℝ] E n))
    (by ext x; simp [smul_smul] <;> field_simp [hR] <;> ring)
    (by ext x; simp [smul_smul] <;> field_simp [hR] <;> ring)

lemma scaleEquiv_det (n : ℕ) {R : ℝ} (hR : R ≠ 0) :
    LinearMap.det (scaleEquiv n hR : E n →ₗ[ℝ] E n) = R ^ n := by
  have h1 : (scaleEquiv n hR : E n →ₗ[ℝ] E n) = R • (LinearMap.id : E n →ₗ[ℝ] E n) := by
    ext x
    rfl
  rw [h1, LinearMap.det_smul]
  have h2 : Module.finrank ℝ (E n) = n := by
    exact finrank_euclideanSpace_fin
  rw [h2] <;> simp

/-- Image of unit ball under scaling by R > 0 is ball of radius R. -/
lemma image_scaled_ball {R : ℝ} (hR : 0 < R) :
    (fun x : E n => R • x) '' Metric.closedBall (0 : E n) 1 = Metric.closedBall (0 : E n) R := by
  ext y
  simp only [Set.mem_image, Metric.mem_closedBall, dist_zero_right]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have h : ‖R • x‖ = R * ‖x‖ := by
      calc
        ‖R • x‖ = ‖R‖ * ‖x‖ := norm_smul R x
        _ = |R| * ‖x‖ := by rw [Real.norm_eq_abs]
        _ = R * ‖x‖ := by rw [abs_of_pos hR]
    rw [h]
    have h' : ‖x‖ ≤ 1 := hx
    nlinarith
  · intro hy
    refine ⟨R⁻¹ • y, ?_, ?_⟩
    · have h : ‖R⁻¹ • y‖ = R⁻¹ * ‖y‖ := by
        calc
          ‖R⁻¹ • y‖ = ‖R⁻¹‖ * ‖y‖ := norm_smul R⁻¹ y
          _ = |R⁻¹| * ‖y‖ := by rw [Real.norm_eq_abs]
          _ = R⁻¹ * ‖y‖ := by rw [abs_of_pos (inv_pos.mpr hR)]
      rw [h]
      have h' : ‖y‖ ≤ R := hy
      have h'' : 0 < R := hR
      calc
        R⁻¹ * ‖y‖ ≤ R⁻¹ * R := by gcongr
        _ = 1 := by field_simp [h''.ne'] <;> ring
    · have h : R • (R⁻¹ • y) = y := by
        rw [smul_smul]
        have h' : R * R⁻¹ = 1 := by field_simp [hR.ne'] <;> ring
        rw [h']
        exact one_smul ℝ y
      exact h

lemma ellipsoid_scaled {c : E n} {R : ℝ} (hR : 0 < R) :
    ellipsoid c (scaleEquiv n hR.ne') = Metric.closedBall c R := by
  have h_fun : (scaleEquiv n hR.ne' : E n → E n) = fun x : E n => R • x := by
    funext x; rfl
  have h_image : (scaleEquiv n hR.ne' : E n → E n) '' Metric.closedBall (0 : E n) 1 =
      Metric.closedBall (0 : E n) R := by
    rw [h_fun]
    exact image_scaled_ball hR
  have h_main : ellipsoid c (scaleEquiv n hR.ne') = c +ᵥ Metric.closedBall (0 : E n) R := by
    simpa [ellipsoid, h_image] using rfl
  rw [h_main]
  ext z
  simp only [Set.mem_vadd, Metric.mem_closedBall]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have h : dist (c +ᵥ y) c = ‖y‖ := by
      simp [vadd_eq_add, dist_eq_norm] <;> abel
    rw [h]
    simpa [Metric.mem_closedBall, dist_zero_right] using hy
  · intro hz
    refine ⟨z - c, ?_, ?_⟩
    · have h : ‖z - c‖ = dist z c := by
        simp [dist_eq_norm] <;> abel
      simpa [Metric.mem_closedBall, dist_zero_right, h] using hz
    · simp [vadd_eq_add] <;> abel

/-- In E n with n > 0, every singleton has empty interior. -/
lemma singleton_interior_empty (hn : 0 < n) (x : E n) :
    interior ({x} : Set (E n)) = ∅ := by
  by_contra h
  have h1 : (interior ({x} : Set (E n))).Nonempty := Set.nonempty_iff_ne_empty.mpr h
  have h2 : interior ({x} : Set (E n)) ⊆ {x} := interior_subset
  rcases h1 with ⟨y, hy⟩
  have hy_eq : y = x := by simpa using h2 hy
  have h3 : x ∈ interior ({x} : Set (E n)) := by
    have h4 : y = x := hy_eq
    rw [h4] at hy
    exact hy
  have h4 : IsOpen ({x} : Set (E n)) := by
    have h5 : interior ({x} : Set (E n)) = {x} := by
      apply Set.Subset.antisymm h2
      intro z hz
      simp only [Set.mem_singleton_iff] at hz ⊢
      rw [hz] <;> exact h3
    rw [←h5] <;> exact isOpen_interior
  have h6 : ∃ (ε : ℝ), 0 < ε ∧ ∀ (y : E n), dist y x < ε → y = x := by
    rw [Metric.isOpen_singleton_iff] at h4
    exact h4
  rcases h6 with ⟨ε, hε_pos, h6⟩
  have h2 : Module.finrank ℝ (E n) = n := by
    exact finrank_euclideanSpace_fin
  have h3 : 0 < Module.finrank ℝ (E n) := by rw [h2] <;> exact hn
  have h_exists : ∃ (x : E n), x ≠ 0 := by
    by_contra h
    push Not at h
    have h4 : Subsingleton (E n) := ⟨fun a b => by rw [h a, h b]⟩
    have h5 : Module.finrank ℝ (E n) = 0 := by
      exact Module.finrank_eq_zero_of_subsingleton ℝ (E n)
    rw [h5] at h3
    exact lt_irrefl 0 h3
  rcases h_exists with ⟨z, hz_ne_zero⟩
  have hznorm_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz_ne_zero
  let v : E n := (ε / (2 * ‖z‖)) • z
  have hv_norm : ‖v‖ = ε / 2 := by
    dsimp only [v]
    rw [norm_smul, Real.norm_eq_abs]
    have hpos : 0 < ε / (2 * ‖z‖) := by positivity
    rw [abs_of_pos hpos]
    field_simp [hznorm_pos.ne'] <;> ring
  have h7 : dist (x + v) x < ε := by
    have h8 : dist (x + v) x = ‖v‖ := by
      simp [dist_eq_norm] <;> abel
    rw [h8, hv_norm] <;> linarith
  have h9 : x + v = x := h6 (x + v) h7
  have h10 : v = 0 := by simpa using h9
  have h11 : ‖v‖ = 0 := by
    rw [h10] <;> simp
  have h12 : ‖v‖ = ε / 2 := hv_norm
  have h13 : ε / 2 = 0 := by
    rw [←h12, h11]
  have h14 : 0 < ε / 2 := half_pos hε_pos
  have h15 : ¬(ε / 2 = 0) := h14.ne'
  exact h15 h13

/-- Common contradiction: if K is contained in a closed ball of radius 0 < R < 1,
    then h_min is violated. -/
lemma ball_contradicts_h_min (hn : 0 < n) {K : Set (E n)}
    (hK : IsConvexBody K)
    (h_min : ∀ (c : E n) (A : E n ≃ₗ[ℝ] E n),
        K ⊆ ellipsoid c A →
        volume (ellipsoid (0 : E n) (1 : E n ≃ₗ[ℝ] E n)) ≤ volume (ellipsoid c A))
    {c : E n} {R : ℝ} (hR_pos : 0 < R) (hR_lt_one : R < 1)
    (hK_sub : K ⊆ Metric.closedBall c R) : False := by
  have h_ellipsoid : K ⊆ ellipsoid c (scaleEquiv n hR_pos.ne') := by
    rw [ellipsoid_scaled hR_pos] <;> exact hK_sub
  have h_vol := h_min c (scaleEquiv n hR_pos.ne') h_ellipsoid
  rw [volume_ellipsoid_le_iff (0 : E n) (1 : E n ≃ₗ[ℝ] E n) c (scaleEquiv n hR_pos.ne')] at h_vol
  have h_det1 : LinearMap.det ((1 : E n ≃ₗ[ℝ] E n) : E n →ₗ[ℝ] E n) = 1 := by simp
  have h_det2 : LinearMap.det (scaleEquiv n hR_pos.ne' : E n →ₗ[ℝ] E n) = R ^ n :=
    scaleEquiv_det n hR_pos.ne'
  rw [h_det1, h_det2] at h_vol
  have h_abs : |R ^ n| = R ^ n := by
    rw [abs_pow] <;> rw [abs_of_pos hR_pos]
  have h_abs2 : |(1 : ℝ)| = 1 := by simp
  rw [h_abs, h_abs2] at h_vol
  have h1 : 0 ≤ R := by linarith
  have h_pow_lt_one : R ^ n < 1 := by
    have h : R ^ n < 1 ^ n := by gcongr
    simpa using h
  linarith

lemma centering_lemma (hn : 0 < n) {K : Set (E n)}
    (hK : IsConvexBody K)
    (hK_sub : K ⊆ Metric.closedBall (0 : E n) 1)
    (h_min : ∀ (c : E n) (A : E n ≃ₗ[ℝ] E n),
        K ⊆ ellipsoid c A →
        volume (ellipsoid (0 : E n) (1 : E n ≃ₗ[ℝ] E n)) ≤ volume (ellipsoid c A)) :
    (0 : E n) ∈ convexHull ℝ (K ∩ Metric.sphere (0 : E n) 1) := by
  let S := K ∩ Metric.sphere (0 : E n) 1
  have hK_conv : Convex ℝ K := hK.1
  have hK_comp : IsCompact K := hK.2.1
  have hK_int : (interior K).Nonempty := hK.2.2
  have hK_nonempty : K.Nonempty := hK_int.mono interior_subset
  have h_sphere_closed : IsClosed (Metric.sphere (0 : E n) 1) := Metric.isClosed_sphere
  have hS_comp : IsCompact S := hK_comp.inter_right h_sphere_closed

  -- Step 1: Prove S is nonempty
  have hS_nonempty : S.Nonempty := by
    by_contra hS_empty
    have hS_empty' : S = ∅ := by simpa [Set.not_nonempty_iff_eq_empty] using hS_empty
    have h1 : ∀ x ∈ K, ‖x‖ < 1 := by
      intro x hx
      have h2 : ‖x‖ ≤ 1 := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hK_sub hx
      by_contra h4
      have h5 : ‖x‖ = 1 := by linarith
      have h6 : x ∈ Metric.sphere (0 : E n) 1 := by
        simpa [Metric.mem_sphere, dist_zero_right] using h5
      have h7 : x ∈ S := ⟨hx, h6⟩
      rw [hS_empty'] at h7 <;> simp at h7
    have hmax : ∃ (x0 : E n), x0 ∈ K ∧ ∀ x ∈ K, ‖x‖ ≤ ‖x0‖ :=
      hK_comp.exists_isMaxOn hK_nonempty continuous_norm.continuousOn
    rcases hmax with ⟨x0, hx0K, hmax_norm⟩
    let r := ‖x0‖
    have hr_lt_one : r < 1 := h1 x0 hx0K
    have hr_pos : 0 < r := by
      by_contra h
      have h'' : r = 0 := by linarith [norm_nonneg x0]
      have h3 : ∀ x ∈ K, x = (0 : E n) := by
        intro x hx
        have h4 : ‖x‖ ≤ r := hmax_norm x hx
        rw [h''] at h4
        have h5 : ‖x‖ = 0 := by linarith [norm_nonneg x]
        have h6 : x = 0 := by simpa using h5
        exact h6
      have h4 : K ⊆ {(0 : E n)} := by
        intro x hx
        exact Set.mem_singleton_iff.mpr (h3 x hx)
      have h5 : interior K ⊆ interior ({(0 : E n)} : Set (E n)) := interior_mono h4
      rw [singleton_interior_empty hn (0 : E n)] at h5
      rcases hK_int with ⟨y, hy⟩
      have h6 : y ∈ interior K := hy
      have h7 : y ∈ (∅ : Set (E n)) := h5 h6
      simp at h7
    have hK_sub' : K ⊆ Metric.closedBall (0 : E n) r := by
      intro x hx
      have h : ‖x‖ ≤ r := hmax_norm x hx
      simpa [Metric.mem_closedBall, dist_zero_right] using h
    exact ball_contradicts_h_min hn hK h_min hr_pos hr_lt_one hK_sub'

  -- Step 2: Assume 0 ∉ convexHull ℝ S, derive contradiction
  by_cases h_main : (0 : E n) ∈ convexHull ℝ S
  · exact h_main
  · let C := convexHull ℝ S
    have hC_conv : Convex ℝ C := convex_convexHull ℝ S
    have hC_comp : IsCompact C := ConvexHullUtils.convexHull_compact hS_comp
    have hC_nonempty : C.Nonempty := hS_nonempty.mono (subset_convexHull ℝ S)
    have h0_notin_C : (0 : E n) ∉ C := h_main

    have h_sep := strict_separation_compact_convex hC_nonempty hC_conv hC_comp h0_notin_C
    rcases h_sep with ⟨w, c, ε, hw_ne_zero, hε_pos, h_inner0, h_innerC⟩
    have h_inner0' : inner ℝ w (0 : E n) = 0 := by simp
    have hc_lt_neg_eps : c < -ε := by
      have h : inner ℝ w (0 : E n) > c + ε := h_inner0
      rw [h_inner0'] at h
      linarith
    have h_innerS : ∀ u ∈ S, inner ℝ w u < c := by
      intro u hu
      exact h_innerC u (subset_convexHull ℝ S hu)

    have hwnorm_pos : 0 < ‖w‖ := norm_pos_iff.mpr hw_ne_zero
    let w' := ‖w‖⁻¹ • (-w)
    have hwnorm' : ‖w'‖ = 1 := by
      dsimp only [w']
      rw [norm_smul, norm_neg]
      have h1 : ‖‖w‖⁻¹‖ = ‖w‖⁻¹ := by
        rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hwnorm_pos)]
      rw [h1]
      field_simp [hwnorm_pos.ne'] <;> ring
    let α := ε / ‖w‖
    have hα_pos : 0 < α := by
      dsimp only [α] <;> exact div_pos hε_pos hwnorm_pos
    have h_innerS' : ∀ u ∈ S, inner ℝ w' u > α := by
      intro u hu
      have h1 : inner ℝ w u < c := h_innerS u hu
      have h2 : inner ℝ w u < -ε := by linarith
      have h3 : - (inner ℝ w u) > ε := by linarith
      have h4 : inner ℝ w' u = - (inner ℝ w u) / ‖w‖ := by
        simp [w', inner_smul_left] <;> ring
      rw [h4]
      have h5 : - (inner ℝ w u) / ‖w‖ > ε / ‖w‖ := by
        apply div_lt_div_of_pos_right h3 hwnorm_pos
      simpa [α] using h5

    let C0 : Set (E n) := {x ∈ K | inner ℝ w' x ≤ α / 2}
    have h_cont : Continuous (fun x : E n => inner ℝ w' x) := by fun_prop
    have h_set_closed : IsClosed {x : E n | inner ℝ w' x ≤ α / 2} :=
      isClosed_le h_cont continuous_const
    have hC0_comp : IsCompact C0 := hK_comp.inter_right h_set_closed
    have hC0_disj_S : Disjoint C0 S := by
      rw [Set.disjoint_left]
      intro x hx1 hx2
      have h6 : inner ℝ w' x > α := h_innerS' x hx2
      have h7 : inner ℝ w' x ≤ α / 2 := hx1.2
      have h8 : α / 2 < α := half_lt_self hα_pos
      have h9 : inner ℝ w' x ≤ α := by
        calc inner ℝ w' x ≤ α / 2 := h7
          _ ≤ α := h8.le
      exact not_le.mpr h6 h9

    have h_exists : ∃ (ε0 : ℝ), 0 < ε0 ∧ ∀ x ∈ K, ‖x - ε0 • w'‖ < 1 := by
      by_cases hC0_empty : C0 = ∅
      · -- Case C0 empty
        have h1 : ∀ x ∈ K, inner ℝ w' x > α / 2 := by
          intro x hx
          by_contra h
          have h2 : inner ℝ w' x ≤ α / 2 := by linarith
          have h3 : x ∈ C0 := ⟨hx, h2⟩
          rw [hC0_empty] at h3 <;> simp at h3
        use α / 2
        constructor
        · linarith [hα_pos]
        · intro x hx
          have h4 : inner ℝ w' x > α / 2 := h1 x hx
          have h5 : ‖x‖ ≤ 1 := by
            simpa [Metric.mem_closedBall, dist_zero_right] using hK_sub hx
          set b := (α / 2 : ℝ) • w' with hb_def
          have h_comm : inner ℝ x w' = inner ℝ w' x := (real_inner_comm x w').symm
          have h_inner_ab : inner ℝ x b = (α / 2 : ℝ) * inner ℝ w' x := by
            rw [inner_smul_right, h_comm] <;> ring
          have h_norm_b : ‖b‖ ^ 2 = (α / 2 : ℝ) ^ 2 := by
            rw [norm_smul, hwnorm']
            rw [Real.norm_eq_abs, abs_of_pos (by linarith [hα_pos] : 0 < (α / 2 : ℝ))]
            <;> ring
          have h_norm_expand : ‖x - b‖ ^ 2 = ‖x‖ ^ 2 - 2 * inner ℝ x b + ‖b‖ ^ 2 :=
            norm_sub_sq_formula x b
          have h6 : α * inner ℝ w' x > α ^ 2 / 2 := by
            have h7 : inner ℝ w' x > α / 2 := h4
            have h8 : α * inner ℝ w' x > α * (α / 2) := by gcongr
            linarith
          have h_norm2_lt_one : ‖x - b‖ ^ 2 < 1 := by
            calc
              ‖x - b‖ ^ 2 = ‖x‖ ^ 2 - 2 * inner ℝ x b + ‖b‖ ^ 2 := h_norm_expand
              _ = ‖x‖ ^ 2 - 2 * ((α / 2 : ℝ) * inner ℝ w' x) + (α / 2 : ℝ) ^ 2 := by
                rw [h_inner_ab, h_norm_b]
              _ = ‖x‖ ^ 2 - α * inner ℝ w' x + α ^ 2 / 4 := by ring
              _ < 1 := by
                have h10 : 0 ≤ ‖x‖ := norm_nonneg x
                have h11 : ‖x‖ ^ 2 ≤ 1 := by
                  calc ‖x‖ ^ 2 ≤ 1 ^ 2 := by gcongr
                    _ = 1 := by norm_num
                nlinarith [h6, hα_pos, h11]
          have h_norm_nonneg : 0 ≤ ‖x - b‖ := norm_nonneg (x - b)
          nlinarith
      · -- Case C0 nonempty
        have hC0_nonempty : C0.Nonempty := Set.nonempty_iff_ne_empty.mpr hC0_empty
        have hmax : ∃ (x1 : E n), x1 ∈ C0 ∧ ∀ x ∈ C0, ‖x‖ ≤ ‖x1‖ :=
          hC0_comp.exists_isMaxOn hC0_nonempty continuous_norm.continuousOn
        rcases hmax with ⟨x1, hx1C0, hmax_norm⟩
        let r := ‖x1‖
        have hr_lt_one : r < 1 := by
          have h_x1_in_K : x1 ∈ K := hx1C0.1
          have h9 : ‖x1‖ ≤ 1 := by
            simpa [Metric.mem_closedBall, dist_zero_right] using hK_sub h_x1_in_K
          by_contra h11
          have h12 : ‖x1‖ = 1 := by linarith
          have h13 : x1 ∈ Metric.sphere (0 : E n) 1 := by
            simpa [Metric.mem_sphere, dist_zero_right] using h12
          have h14 : x1 ∈ S := ⟨h_x1_in_K, h13⟩
          have h15 : x1 ∉ C0 := (Set.disjoint_right.mp hC0_disj_S) h14
          exact h15 hx1C0
        let ε0 := min (α / 2) ((1 - r) / 2)
        have hε0_pos : 0 < ε0 := by
          dsimp only [ε0]
          exact lt_min (by linarith [hα_pos]) (by linarith)
        have hε0_lt_alpha : ε0 < α := by
          dsimp only [ε0]
          have h : min (α / 2) ((1 - r) / 2) ≤ α / 2 := min_le_left _ _
          linarith [hα_pos]
        have hε0_lt_1mr : ε0 < 1 - r := by
          dsimp only [ε0]
          have h : min (α / 2) ((1 - r) / 2) ≤ (1 - r) / 2 := min_le_right _ _
          linarith
        refine ⟨ε0, hε0_pos, ?_⟩
        intro x hx
        by_cases h_x_in_C0 : x ∈ C0
        · have h9 : ‖x‖ ≤ r := hmax_norm x h_x_in_C0
          have h10 : ‖x - ε0 • w'‖ ≤ ‖x‖ + ε0 := by
            calc
              ‖x - ε0 • w'‖ ≤ ‖x‖ + ‖ε0 • w'‖ := norm_sub_le _ _
              _ = ‖x‖ + ε0 := by
                have h11 : ‖ε0 • w'‖ = ε0 := by
                  rw [norm_smul, hwnorm']
                  rw [Real.norm_eq_abs, abs_of_pos hε0_pos] <;> ring
                rw [h11]
          linarith
        · have h9 : inner ℝ w' x > α / 2 := by
            by_contra h10
            have h11 : inner ℝ w' x ≤ α / 2 := by linarith
            have h12 : x ∈ C0 := ⟨hx, h11⟩
            exact h_x_in_C0 h12
          have h10 : ‖x‖ ≤ 1 := by
            simpa [Metric.mem_closedBall, dist_zero_right] using hK_sub hx
          set b := ε0 • w' with hb_def
          have h_comm : inner ℝ x w' = inner ℝ w' x := (real_inner_comm x w').symm
          have h_inner_ab : inner ℝ x b = ε0 * inner ℝ w' x := by
            rw [inner_smul_right, h_comm] <;> ring
          have h_norm_b : ‖b‖ ^ 2 = ε0 ^ 2 := by
            rw [norm_smul, hwnorm']
            rw [Real.norm_eq_abs, abs_of_pos hε0_pos] <;> ring
          have h_norm_expand : ‖x - b‖ ^ 2 = ‖x‖ ^ 2 - 2 * inner ℝ x b + ‖b‖ ^ 2 :=
            norm_sub_sq_formula x b
          have h11 : 2 * ε0 * inner ℝ w' x > ε0 * α := by
            have h12 : inner ℝ w' x > α / 2 := h9
            have h13 : 2 * ε0 * inner ℝ w' x > 2 * ε0 * (α / 2) := by gcongr
            have h14 : 2 * ε0 * (α / 2) = ε0 * α := by ring
            linarith
          have h15 : ε0 ^ 2 < ε0 * α := by
            nlinarith [hε0_pos, hε0_lt_alpha]
          have h_norm2_lt_one : ‖x - b‖ ^ 2 < 1 := by
            calc
              ‖x - b‖ ^ 2 = ‖x‖ ^ 2 - 2 * inner ℝ x b + ‖b‖ ^ 2 := h_norm_expand
              _ = ‖x‖ ^ 2 - 2 * (ε0 * inner ℝ w' x) + ε0 ^ 2 := by
                rw [h_inner_ab, h_norm_b]
              _ < 1 := by
                have h16 : -2 * (ε0 * inner ℝ w' x) + ε0 ^ 2 < 0 := by nlinarith [h11, h15]
                have h17 : ‖x‖ ^ 2 ≤ 1 := by
                  calc ‖x‖ ^ 2 ≤ 1 ^ 2 := by gcongr
                    _ = 1 := by norm_num
                nlinarith [h16, h17]
          have h_norm_nonneg : 0 ≤ ‖x - b‖ := norm_nonneg (x - b)
          nlinarith

    rcases h_exists with ⟨ε0, hε0_pos, h_ball_strict⟩

    have hmaxR : ∃ (x2 : E n), x2 ∈ K ∧ ∀ x ∈ K, ‖x - ε0 • w'‖ ≤ ‖x2 - ε0 • w'‖ :=
      hK_comp.exists_isMaxOn hK_nonempty
        (continuous_norm.comp (continuous_id.sub continuous_const)).continuousOn
    rcases hmaxR with ⟨x2, hx2K, hmaxR_norm⟩
    let R := ‖x2 - ε0 • w'‖
    have hR_lt_one : R < 1 := h_ball_strict x2 hx2K
    have hR_pos : 0 < R := by
      by_contra h
      have h'' : R = 0 := by linarith [norm_nonneg (x2 - ε0 • w')]
      have h3 : ∀ x ∈ K, x = ε0 • w' := by
        intro x hx
        have h4 : ‖x - ε0 • w'‖ ≤ R := hmaxR_norm x hx
        rw [h''] at h4
        have h5 : ‖x - ε0 • w'‖ = 0 := by linarith [norm_nonneg (x - ε0 • w')]
        have h6 : x - ε0 • w' = 0 := by simpa using h5
        exact sub_eq_zero.mp h6
      have h4 : K ⊆ {ε0 • w'} := by
        intro x hx
        exact Set.mem_singleton_iff.mpr (h3 x hx)
      have h5 : interior K ⊆ interior ({ε0 • w'} : Set (E n)) := interior_mono h4
      rw [singleton_interior_empty hn (ε0 • w')] at h5
      rcases hK_int with ⟨y, hy⟩
      have h6 : y ∈ interior K := hy
      have h7 : y ∈ (∅ : Set (E n)) := h5 h6
      simp at h7
    have hK_sub_R : K ⊆ Metric.closedBall (ε0 • w') R := by
      intro x hx
      have h : ‖x - ε0 • w'‖ ≤ R := hmaxR_norm x hx
      simpa [Metric.mem_closedBall, dist_eq_norm] using h
    exfalso
    exact ball_contradicts_h_min hn hK h_min hR_pos hR_lt_one hK_sub_R

end JohnEllipsoid
