import MyLeanRepo.Kakeya.Cinematic.TangencySublevelStructure.Basic

/-!
# Lower bound lemmas

Algebraic core, distance-to-boundary, and the monotone-case lower bound
used in the final sublevel structure theorem.
-/

namespace Kakeya.Cinematic

lemma abs_add_real (a b : ℝ) : |a + b| ≤ |a| + |b| := by
  have h1 : a ≤ |a| := by
    by_cases h : 0 ≤ a
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg (by linarith)] <;> linarith
  have h2 : -a ≤ |a| := by
    by_cases h : 0 ≤ a
    · rw [abs_of_nonneg h] <;> linarith
    · rw [abs_of_neg (by linarith)]
  have h3 : b ≤ |b| := by
    by_cases h : 0 ≤ b
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg (by linarith)] <;> linarith
  have h4 : -b ≤ |b| := by
    by_cases h : 0 ≤ b
    · rw [abs_of_nonneg h] <;> linarith
    · rw [abs_of_neg (by linarith)]
  have h5 : a + b ≤ |a| + |b| := by linarith
  have h6 : -(a + b) ≤ |a| + |b| := by linarith
  by_cases h7 : 0 ≤ a + b
  · rw [abs_of_nonneg h7] <;> linarith
  · rw [abs_of_neg (by linarith)] <;> linarith

/-- Algebraic core for lower bound: 2*h'_max/(C1*scale) + δ/(C1²*(Δ+δ)) ≤ 1. -/
lemma lower_bound_algebraic_core
    {K t delta Delta C1 scale h'_max : ℝ}
    (hK : 1 ≤ K) (ht_pos : 0 < t) (hdelta : 0 < delta)
    (hdelta_le : delta ≤ t / (6 * K))
    (hDelta_le : Delta ≤ 2 * t / (3 * K))
    (hDelta_nonneg : 0 ≤ Delta)
    (hC1_large : 1000 * K^2 ≤ C1)
    (hscale : scale = Real.sqrt ((Delta + delta) * t))
    (h'_max_le : h'_max ≤ Delta + delta / 2) :
    2 * h'_max / (C1 * scale) + delta / (C1^2 * (Delta + delta)) ≤ 1 := by
  have hK_pos : 0 < K := by linarith
  have hC1_pos : 0 < C1 := by nlinarith
  set S := Delta + delta with hS
  have hS_pos : 0 < S := by linarith
  have hS_le : S ≤ 5 * t / (6 * K) := by
    have h1 : Delta + delta ≤ 2 * t / (3 * K) + t / (6 * K) := by linarith
    have h2 : 2 * t / (3 * K) + t / (6 * K) = 5 * t / (6 * K) := by
      field_simp [hK_pos.ne'] <;> ring
    rw [h2] at h1
    rw [hS]
    exact h1
  have hscale_pos : 0 < scale := by
    rw [hscale] <;> positivity
  have h1 : 2 * h'_max ≤ 2 * Delta + delta := by linarith
  have h_sqrtS_pos : 0 < Real.sqrt S := by positivity
  have h_sqrtt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht_pos
  have h2 : (2 * Delta + delta) / (C1 * scale) ≤ 2 * Real.sqrt (5 / (6 * K)) / C1 := by
    have h3 : 2 * Delta + delta ≤ 2 * S := by linarith
    have h4 : scale = Real.sqrt (S * t) := by simpa [hS] using hscale
    rw [h4]
    have h51 : Real.sqrt (S * t) = Real.sqrt S * Real.sqrt t := by
      rw [← Real.sqrt_mul (by linarith)] <;> ring
    have h5 : (2 * Delta + delta) / Real.sqrt (S * t) ≤ 2 * Real.sqrt S / Real.sqrt t := by
      rw [h51]
      have h6 : (2 * Delta + delta) / (Real.sqrt S * Real.sqrt t) ≤ (2 * S) / (Real.sqrt S * Real.sqrt t) := by
        gcongr
      have h7 : (2 * S) / (Real.sqrt S * Real.sqrt t) = 2 * Real.sqrt S / Real.sqrt t := by
        have h8 : (Real.sqrt S) ^ 2 = S := Real.sq_sqrt (by linarith)
        field_simp [h_sqrtS_pos.ne', h_sqrtt_pos.ne'] <;> nlinarith
      rw [h7] at h6
      exact h6
    have h9 : Real.sqrt S ≤ Real.sqrt (5 * t / (6 * K)) := Real.sqrt_le_sqrt hS_le
    have h10 : Real.sqrt (5 * t / (6 * K)) = Real.sqrt (5 / (6 * K)) * Real.sqrt t := by
      have h_pos : 0 ≤ 5 / (6 * K) := by positivity
      have h_eq : Real.sqrt ((5 / (6 * K)) * t) = Real.sqrt (5 / (6 * K)) * Real.sqrt t :=
        by exact Real.sqrt_mul h_pos t
      have h2 : (5 / (6 * K)) * t = 5 * t / (6 * K) := by ring
      rw [h2] at h_eq
      exact h_eq
    calc (2 * Delta + delta) / (C1 * Real.sqrt (S * t))
        = ((2 * Delta + delta) / Real.sqrt (S * t)) / C1 := by ring
      _ ≤ (2 * Real.sqrt S / Real.sqrt t) / C1 := by gcongr
      _ = 2 * Real.sqrt S / (C1 * Real.sqrt t) := by ring
      _ ≤ 2 * Real.sqrt (5 * t / (6 * K)) / (C1 * Real.sqrt t) := by gcongr
      _ = 2 * Real.sqrt (5 / (6 * K)) / C1 := by
        rw [h10] <;> field_simp <;> ring
  have h3 : delta / (C1^2 * S) ≤ 1 / C1^2 := by
    have h4 : delta ≤ S := by linarith [hS]
    have h5 : 0 < C1^2 * S := by positivity
    have h6 : delta / (C1^2 * S) ≤ S / (C1^2 * S) := by gcongr
    have h7 : S / (C1^2 * S) = 1 / C1^2 := by
      field_simp [h5.ne'] <;> ring
    rw [h7] at h6
    exact h6
  have h6 : 2 * Real.sqrt (5 / (6 * K)) / C1 + 1 / C1^2 ≤ 1 := by
    have h7 : Real.sqrt (5 / (6 * K)) ≤ 1 := by
      have h81 : 0 < 6 * K := by positivity
      have h82 : 5 ≤ 6 * K := by linarith
      have h83 : 5 / (6 * K) ≤ 1 := by
        calc 5 / (6 * K) ≤ (6 * K) / (6 * K) := by gcongr
          _ = 1 := by field_simp [h81.ne'] <;> ring
      have h : Real.sqrt (5 / (6 * K)) ≤ Real.sqrt 1 := Real.sqrt_le_sqrt h83
      have h2 : Real.sqrt 1 = 1 := by simp
      rw [h2] at h
      exact h
    have h9 : 2 * Real.sqrt (5 / (6 * K)) / C1 ≤ 1 / 500 := by
      have h10 : C1 ≥ 1000 * K^2 := hC1_large
      have h11 : 2 * Real.sqrt (5 / (6 * K)) ≤ 2 := by
        have h12 : Real.sqrt (5 / (6 * K)) ≤ 1 := h7
        linarith
      have h13 : C1 ≥ 1000 := by nlinarith
      calc 2 * Real.sqrt (5 / (6 * K)) / C1
          ≤ 2 / C1 := by gcongr
        _ ≤ 2 / 1000 := by gcongr
        _ = 1 / 500 := by norm_num
    have h14 : 1 / C1^2 ≤ 1 / 1000000 := by
      have h15 : C1 ≥ 1000 := by nlinarith
      have h16 : C1^2 ≥ 1000000 := by nlinarith
      have h17 : 0 < C1^2 := by positivity
      exact one_div_le_one_div_of_le (by positivity) h16
    linarith
  calc 2 * h'_max / (C1 * scale) + delta / (C1^2 * (Delta + delta))
      ≤ (2 * Delta + delta) / (C1 * scale) + delta / (C1^2 * S) := by
        gcongr <;> linarith
    _ ≤ 2 * Real.sqrt (5 / (6 * K)) / C1 + 1 / C1^2 := by gcongr
    _ ≤ 1 := h6

/-- Lower bound for monotone case (L)h': |H'| ≥ t/(6K) everywhere. -/
lemma lower_bound_monotone
    {K : ℝ} (hK : 1 ≤ K)
    {I : ParameterInterval} {f g : C2Function} {t delta scale : ℝ}
    (ht_pos : 0 < t) (ht_eq : t = c2Distance f g) (hdelta : 0 < delta)
    (E E_half : Set UnitPoint)
    (hE : E = tangencySublevelSetOn I f g delta)
    (hE_half : E_half = tangencySublevelSetOn I f g (delta / 2))
    (C1 : ℝ) (hC1_large : 100 * K ≤ C1)
    (hscale : scale = Real.sqrt ((tangencyParameterOn I f g + delta) * t))
    (hI_controlled : I.IsControlled K)
    (hL_h' : ∀ (x : UnitPoint), x ∈ I.carrier → (6 * K)⁻¹ * t ≤ |f.firstDeriv x - g.firstDeriv x|)
    (hdelta_le : delta ≤ (6 * K)⁻¹ * t)
    (F : IntervalFamily)
    (hF_card1 : F.card = 1)
    (hF_union : F.union = E) :
    ∀ (x : UnitPoint), x ∈ E_half →
      ∃ (j : Fin F.card), x ∈ (F.interval j).carrier ∧
        delta ≤ C1 * scale * (F.interval j).length := by
  intro x hx
  have hK_pos : 0 < K := by linarith
  set H : ℝ → ℝ := f.extension - g.extension with hH
  have hHx : |H (x : ℝ)| ≤ delta / 2 := by
    simp only [hE_half, tangencySublevelSetOn, Set.mem_setOf_eq] at hx
    have h_eq : H (x : ℝ) = f x - g x := by
      have h1 : H (x : ℝ) = f.extension (x : ℝ) - g.extension (x : ℝ) := by
        simp [H] <;> rfl
      have h2 : f.extension (x : ℝ) = f x := C2Function.extension_eq_value f x
      have h3 : g.extension (x : ℝ) = g x := C2Function.extension_eq_value g x
      rw [h1, h2, h3] <;> abel
    rw [h_eq]
    exact hx.2
  have h_x_center1 : x ∈ I.centeredCarrier (1 / 4) := by
    simp only [hE_half, tangencySublevelSetOn, Set.mem_setOf_eq] at hx
    exact hx.1
  have h_x_dist : |(x : ℝ) - I.midpoint| ≤ I.length / 8 := by
    have h : |(x : ℝ) - I.midpoint| ≤ (1 / 4 : ℝ) * I.length / 2 := h_x_center1
    have h2 : (1 / 4 : ℝ) * I.length / 2 = I.length / 8 := by ring
    rw [h2] at h
    exact h
  have hΔ_lower : tangencyParameterOn I f g ≥ (6 * K)⁻¹ * t := by
    rcases tangency_parameter_attained I f g with ⟨xΔ, hxΔ_in, h_eq⟩
    have h_xΔ_I : xΔ ∈ I.carrier :=
      I.centeredCarrier_subset_carrier (by norm_num) (by norm_num) hxΔ_in
    have h2 : (6 * K)⁻¹ * t ≤ |f.firstDeriv xΔ - g.firstDeriv xΔ| := hL_h' xΔ h_xΔ_I
    have h3 : |f xΔ - g xΔ| + |f.firstDeriv xΔ - g.firstDeriv xΔ| = tangencyParameterOn I f g := h_eq
    have h4 : |f xΔ - g xΔ| + |f.firstDeriv xΔ - g.firstDeriv xΔ| ≥ |f.firstDeriv xΔ - g.firstDeriv xΔ| :=
      le_add_of_nonneg_left (abs_nonneg _)
    linarith
  set S : ℝ := tangencyParameterOn I f g + delta with hS
  have hS_pos : 0 < S := by linarith [hΔ_lower, hdelta]
  have hscaleS : scale = Real.sqrt (S * t) := by
    simpa [hS] using hscale
  have hscale_pos : 0 < scale := by
    rw [hscaleS]
    exact Real.sqrt_pos.mpr (mul_pos hS_pos ht_pos)
  have hC1_pos : 0 < C1 := by linarith [hC1_large, hK_pos]
  have h_sqrt6K_pos : 0 < Real.sqrt (6 * K) := by positivity
  have h_sqrt6K_le : Real.sqrt (6 * K) ≤ 50 * K := by
    nlinarith [Real.sq_sqrt (show 0 ≤ 6 * K by linarith)]
  have hC1_scale : C1 * scale ≥ 2 * t := by
    rw [hscaleS]
    have h51 : S * t ≥ ((6 * K)⁻¹ * t) * t := by
      have hS_lower : S ≥ (6 * K)⁻¹ * t := by
        simp only [hS]
        linarith [hΔ_lower]
      gcongr <;> linarith
    have h52 : Real.sqrt (((6 * K)⁻¹ * t) * t) = t / Real.sqrt (6 * K) := by
      have h7 : ((6 * K)⁻¹ * t) * t = t^2 / (6 * K) := by
        field_simp [hK_pos.ne'] <;> ring
      rw [h7, Real.sqrt_div (by positivity), Real.sqrt_sq (by linarith)] <;> ring
    have h4 : Real.sqrt (S * t) ≥ t / Real.sqrt (6 * K) := by
      have h53 : Real.sqrt (S * t) ≥ Real.sqrt (((6 * K)⁻¹ * t) * t) := Real.sqrt_le_sqrt h51
      rw [h52] at h53
      exact h53
    have h7 : C1 * Real.sqrt (S * t) ≥ C1 * (t / Real.sqrt (6 * K)) := by
      gcongr <;> linarith
    have h8 : C1 * (t / Real.sqrt (6 * K)) ≥ 2 * t := by
      have h9 : C1 / Real.sqrt (6 * K) ≥ 2 := by
        calc C1 / Real.sqrt (6 * K)
          ≥ (100 * K) / Real.sqrt (6 * K) := by gcongr
        _ ≥ (100 * K) / (50 * K) := by gcongr
        _ = 2 := by field_simp [hK_pos.ne'] <;> ring
      have h10 : C1 * (t / Real.sqrt (6 * K)) = (C1 / Real.sqrt (6 * K)) * t := by ring
      rw [h10]
      exact mul_le_mul_of_nonneg_right h9 (by linarith)
    linarith
  have h_x_in_E : x ∈ E := by
    simp only [hE_half, hE, tangencySublevelSetOn, Set.mem_setOf_eq] at hx ⊢
    exact ⟨hx.1, by linarith [hx.2]⟩
  have h_x_in_union : x ∈ F.union := by rw [hF_union] <;> exact h_x_in_E
  rcases h_x_in_union with ⟨j, hj⟩
  let J := F.interval j
  have h_x_in_J : x ∈ J.carrier := hj
  have hJ_eq_E : J.carrier = E := by
    have h1 : F.union = J.carrier := by
      ext y
      simp only [IntervalFamily.union, Set.mem_setOf_eq]
      constructor
      · rintro ⟨i, hi⟩
        have h_i_val : i.val = 0 := by
          have h : i.val < F.card := i.is_lt
          have h' : i.val < 1 := by simpa [hF_card1] using h
          omega
        have h_j_val : j.val = 0 := by
          have h : j.val < F.card := j.is_lt
          have h' : j.val < 1 := by simpa [hF_card1] using h
          omega
        have h_i_eq_j : i = j := by
          apply Fin.ext
          rw [h_i_val, h_j_val]
        rw [h_i_eq_j] at hi
        exact hi
      · intro hy
        exact ⟨j, hy⟩
    rw [h1] at hF_union
    exact hF_union
  let L_left := I.midpoint - I.length / 8
  let L_right := I.midpoint + I.length / 8
  have hL_left_ge_Ileft : L_left ≥ I.left := by
    dsimp only [L_left, ParameterInterval.midpoint, ParameterInterval.length]
    linarith [I.left_le_right]
  have hL_right_le_Iright : L_right ≤ I.right := by
    dsimp only [L_right, ParameterInterval.midpoint, ParameterInterval.length]
    linarith [I.left_le_right]
  have h_x_left : L_left ≤ (x : ℝ) := by
    dsimp only [L_left]
    have h_abs : |(x : ℝ) - I.midpoint| ≤ I.length / 8 := h_x_dist
    have h_neg : -(I.length / 8) ≤ (x : ℝ) - I.midpoint := by
      by_contra h
      have h' : (x : ℝ) - I.midpoint < -(I.length / 8) := by linarith
      have h'' : (x : ℝ) - I.midpoint < 0 := by linarith [I.length_nonneg]
      have h3 : |(x : ℝ) - I.midpoint| = -((x : ℝ) - I.midpoint) := abs_of_neg h''
      rw [h3] at h_abs
      linarith
    linarith
  have h_x_right : (x : ℝ) ≤ L_right := by
    dsimp only [L_right]
    have h_abs : |(x : ℝ) - I.midpoint| ≤ I.length / 8 := h_x_dist
    have h_pos : (x : ℝ) - I.midpoint ≤ I.length / 8 := by
      by_contra h
      have h' : (x : ℝ) - I.midpoint > I.length / 8 := by linarith
      have h'' : 0 < (x : ℝ) - I.midpoint := by linarith [I.length_nonneg]
      have h3 : |(x : ℝ) - I.midpoint| = (x : ℝ) - I.midpoint := abs_of_pos h''
      rw [h3] at h_abs
      linarith
    linarith
  let d := delta / (2 * t)
  have hd_pos : 0 < d := by positivity
  let rL := max L_left ((x : ℝ) - d)
  let rR := min L_right ((x : ℝ) + d)
  have hrL_ge : L_left ≤ rL := le_max_left _ _
  have hrL_le : rL ≤ (x : ℝ) := by
    dsimp only [rL]
    have h1 : L_left ≤ (x : ℝ) := h_x_left
    have h2 : (x : ℝ) - d ≤ (x : ℝ) := by linarith [hd_pos]
    exact max_le h1 h2
  have hrR_ge : (x : ℝ) ≤ rR := by
    dsimp only [rR]
    have h1 : (x : ℝ) ≤ L_right := h_x_right
    have h2 : (x : ℝ) ≤ (x : ℝ) + d := by linarith [hd_pos]
    exact le_min h1 h2
  have hrR_le : rR ≤ L_right := min_le_left _ _
  have hrL_in : L_left ≤ rL ∧ rL ≤ L_right := ⟨hrL_ge, by linarith [hrL_le, h_x_right]⟩
  have hrR_in : L_left ≤ rR ∧ rR ≤ L_right := ⟨by linarith [hrR_ge, h_x_left], hrR_le⟩
  have hrL_dist : |rL - (x : ℝ)| ≤ d := by
    dsimp only [rL]
    have h1 : max L_left ((x : ℝ) - d) ≤ (x : ℝ) := hrL_le
    have h2 : (x : ℝ) - d ≤ max L_left ((x : ℝ) - d) := le_max_right _ _
    have h3 : -d ≤ max L_left ((x : ℝ) - d) - (x : ℝ) := by linarith
    have h4 : max L_left ((x : ℝ) - d) - (x : ℝ) ≤ 0 := by linarith
    have h5 : |max L_left ((x : ℝ) - d) - (x : ℝ)| ≤ d := by
      rw [abs_of_nonpos h4] <;> linarith
    exact h5
  have hrR_dist : |rR - (x : ℝ)| ≤ d := by
    dsimp only [rR]
    have h1 : (x : ℝ) ≤ min L_right ((x : ℝ) + d) := hrR_ge
    have h2 : min L_right ((x : ℝ) + d) ≤ (x : ℝ) + d := min_le_right _ _
    have h3 : 0 ≤ min L_right ((x : ℝ) + d) - (x : ℝ) := by linarith
    have h4 : min L_right ((x : ℝ) + d) - (x : ℝ) ≤ d := by linarith
    have h5 : |min L_right ((x : ℝ) + d) - (x : ℝ)| ≤ d := by
      rw [abs_of_nonneg h3] <;> linarith
    exact h5
  have h_ball : ∀ (r : ℝ), L_left ≤ r → r ≤ L_right → |r - (x : ℝ)| ≤ d → |H r| ≤ delta := by
    intro r hrL hrR hdist
    have hr0 : 0 ≤ r := by linarith [hL_left_ge_Ileft, I.left_mem.1]
    have hr1 : r ≤ 1 := by linarith [hL_right_le_Iright, I.right_mem.2]
    let p : UnitPoint := ⟨r, ⟨hr0, hr1⟩⟩
    have h2 : |(f p - g p) - (f x - g x)| ≤ c2Distance f g * |r - (x : ℝ)| :=
      lipschitz_value f g p x
    have h3 : c2Distance f g = t := ht_eq.symm
    have h41 : f.extension r = f p := by
      have h : f.extension (p : ℝ) = f p := C2Function.extension_eq_value f p
      have h' : (p : ℝ) = r := by rfl
      rw [h'] at h
      exact h
    have h42 : g.extension r = g p := by
      have h : g.extension (p : ℝ) = g p := C2Function.extension_eq_value g p
      have h' : (p : ℝ) = r := by rfl
      rw [h'] at h
      exact h
    have h43 : f.extension (x : ℝ) = f x := C2Function.extension_eq_value f x
    have h44 : g.extension (x : ℝ) = g x := C2Function.extension_eq_value g x
    have h5 : H r = f p - g p := by
      have hH_r : H r = f.extension r - g.extension r := by simp [H] <;> rfl
      rw [hH_r, h41, h42] <;> abel
    have h6 : H (x : ℝ) = f x - g x := by
      have hH_x : H (x : ℝ) = f.extension (x : ℝ) - g.extension (x : ℝ) := by simp [H] <;> rfl
      rw [hH_x, h43, h44] <;> abel
    have h4 : |H r - H (x : ℝ)| ≤ t * |r - (x : ℝ)| := by
      have h2' : |(f p - g p) - (f x - g x)| ≤ t * |r - (x : ℝ)| := by
        rw [h3] at h2
        exact h2
      rw [h5, h6] at *
      exact h2'
    have h7 : |H r| ≤ |H (x : ℝ)| + |H r - H (x : ℝ)| := by
      have h8 : H r = H (x : ℝ) + (H r - H (x : ℝ)) := by ring
      have h9 : |H (x : ℝ) + (H r - H (x : ℝ))| ≤ |H (x : ℝ)| + |H r - H (x : ℝ)| :=
        abs_add_real (H (x : ℝ)) (H r - H (x : ℝ))
      have h10 : |H r| = |H (x : ℝ) + (H r - H (x : ℝ))| := by
        apply congr_arg
        exact h8
      rw [h10]
      exact h9
    calc |H r|
      ≤ |H (x : ℝ)| + t * |r - (x : ℝ)| := by linarith
    _ ≤ delta / 2 + t * d := by gcongr
    _ = delta := by
      dsimp only [d]
      field_simp [ht_pos.ne'] <;> ring
  have hpL1 : (0 : ℝ) ≤ rL := by linarith [hL_left_ge_Ileft, I.left_mem.1]
  have hpL2 : rL ≤ 1 := by linarith [hL_right_le_Iright, I.right_mem.2]
  let pL : UnitPoint := ⟨rL, ⟨hpL1, hpL2⟩⟩
  have hpL_eq : (pL : ℝ) = rL := by rfl
  have hpL_in_I : pL ∈ I.carrier := by
    simp only [ParameterInterval.carrier, Set.mem_setOf_eq]
    exact ⟨by linarith [hL_left_ge_Ileft], by linarith [hL_right_le_Iright]⟩
  have hpL_dist : |(pL : ℝ) - I.midpoint| ≤ (1 / 4 : ℝ) * I.length / 2 := by
    rw [hpL_eq]
    have h12 : |rL - I.midpoint| ≤ I.length / 8 := by
      rw [abs_le]
      constructor
      · have h13 : rL ≥ L_left := hrL_ge
        have h14 : L_left = I.midpoint - I.length / 8 := by rfl
        linarith
      · have h13 : rL ≤ (x : ℝ) := hrL_le
        have h14 : (x : ℝ) ≤ L_right := h_x_right
        have h15 : L_right = I.midpoint + I.length / 8 := by rfl
        linarith
    have h13 : I.length / 8 = (1 / 4 : ℝ) * I.length / 2 := by ring
    rw [h13] at h12
    exact h12
  have hpL_center : pL ∈ I.centeredCarrier (1 / 4) := by
    simp only [ParameterInterval.centeredCarrier, Set.mem_setOf_eq]
    exact hpL_dist
  have hpR1 : (0 : ℝ) ≤ rR := by linarith [hL_left_ge_Ileft, I.left_mem.1]
  have hpR2 : rR ≤ 1 := by linarith [hL_right_le_Iright, I.right_mem.2]
  let pR : UnitPoint := ⟨rR, ⟨hpR1, hpR2⟩⟩
  have hpR_eq : (pR : ℝ) = rR := by rfl
  have hpR_in_I : pR ∈ I.carrier := by
    simp only [ParameterInterval.carrier, Set.mem_setOf_eq]
    exact ⟨by linarith [hL_left_ge_Ileft], by linarith [hL_right_le_Iright]⟩
  have hpR_dist : |(pR : ℝ) - I.midpoint| ≤ (1 / 4 : ℝ) * I.length / 2 := by
    rw [hpR_eq]
    have h12 : |rR - I.midpoint| ≤ I.length / 8 := by
      rw [abs_le]
      constructor
      · have h13 : L_left ≤ rR := by linarith [h_x_left, hrR_ge]
        have h14 : L_left = I.midpoint - I.length / 8 := by rfl
        linarith
      · have h13 : rR ≤ L_right := hrR_le
        have h14 : L_right = I.midpoint + I.length / 8 := by rfl
        linarith
    have h13 : I.length / 8 = (1 / 4 : ℝ) * I.length / 2 := by ring
    rw [h13] at h12
    exact h12
  have hpR_center : pR ∈ I.centeredCarrier (1 / 4) := by
    simp only [ParameterInterval.centeredCarrier, Set.mem_setOf_eq]
    exact hpR_dist
  have hrL_J : rL ∈ Set.Icc J.left J.right := by
    have h1 : |H rL| ≤ delta := h_ball rL hrL_in.1 hrL_in.2 hrL_dist
    have h2 : H rL = f pL - g pL := by
      have hH_r : H rL = f.extension rL - g.extension rL := by simp [H] <;> rfl
      have hfe : f.extension rL = f pL := by
        have h : f.extension (pL : ℝ) = f pL := C2Function.extension_eq_value f pL
        rw [hpL_eq] at h; exact h
      have hge : g.extension rL = g pL := by
        have h : g.extension (pL : ℝ) = g pL := C2Function.extension_eq_value g pL
        rw [hpL_eq] at h; exact h
      rw [hH_r, hfe, hge] <;> abel
    have hp_E : pL ∈ E := by
      simp only [hE, tangencySublevelSetOn, Set.mem_setOf_eq]
      exact ⟨hpL_center, by simpa [h2] using h1⟩
    have hp_J : pL ∈ J.carrier := by rw [hJ_eq_E] <;> exact hp_E
    simp only [ParameterInterval.carrier, Set.mem_setOf_eq] at hp_J
    exact hp_J
  have hrR_J : rR ∈ Set.Icc J.left J.right := by
    have h1 : |H rR| ≤ delta := h_ball rR hrR_in.1 hrR_in.2 hrR_dist
    have h2 : H rR = f pR - g pR := by
      have hH_r : H rR = f.extension rR - g.extension rR := by simp [H] <;> rfl
      have hfe : f.extension rR = f pR := by
        have h : f.extension (pR : ℝ) = f pR := C2Function.extension_eq_value f pR
        rw [hpR_eq] at h; exact h
      have hge : g.extension rR = g pR := by
        have h : g.extension (pR : ℝ) = g pR := C2Function.extension_eq_value g pR
        rw [hpR_eq] at h; exact h
      rw [hH_r, hfe, hge] <;> abel
    have hp_E : pR ∈ E := by
      simp only [hE, tangencySublevelSetOn, Set.mem_setOf_eq]
      exact ⟨hpR_center, by simpa [h2] using h1⟩
    have hp_J : pR ∈ J.carrier := by rw [hJ_eq_E] <;> exact hp_E
    simp only [ParameterInterval.carrier, Set.mem_setOf_eq] at hp_J
    exact hp_J
  have h_len1 : J.length ≥ rR - rL := by
    simp only [ParameterInterval.length]
    linarith [hrL_J.1, hrR_J.2]
  have h_dL : 0 ≤ (x : ℝ) - L_left := by linarith [h_x_left]
  have h_dR : 0 ≤ L_right - (x : ℝ) := by linarith [h_x_right]
  have h_len2 : rR - rL ≥ min d (I.length / 4) := by
    by_cases h : rR - rL ≥ d
    · have hmin : min d (I.length / 4) ≤ d := min_le_left _ _
      linarith
    · -- Case rR - rL < d
      have h_lt : rR - rL < d := by linarith
      have h_rL : rL = L_left := by
        by_contra h_rL
        have h_rL' : rL = (x : ℝ) - d := by
          dsimp only [rL]
          have h_max : max L_left ((x : ℝ) - d) = L_left ∨ max L_left ((x : ℝ) - d) = (x : ℝ) - d := by
            by_cases h : L_left ≥ (x : ℝ) - d
            · left
              rw [max_eq_left h]
            · right
              rw [max_eq_right (by linarith)]
          rcases h_max with (h_max | h_max)
          · contradiction
          · exact h_max
        rw [h_rL'] at h_lt
        linarith [hrR_ge]
      have h_rR : rR = L_right := by
        by_contra h_rR
        have h_rR' : rR = (x : ℝ) + d := by
          dsimp only [rR]
          have h_min : min L_right ((x : ℝ) + d) = L_right ∨ min L_right ((x : ℝ) + d) = (x : ℝ) + d := by
            by_cases h : L_right ≤ (x : ℝ) + d
            · left
              rw [min_eq_left h]
            · right
              rw [min_eq_right (by linarith)]
          rcases h_min with (h_min | h_min)
          · contradiction
          · exact h_min
        rw [h_rR'] at h_lt
        linarith [hrL_le]
      have h_eq : rR - rL = I.length / 4 := by
        rw [h_rL, h_rR]
        dsimp only [L_left, L_right] <;> ring
      have hmin : min d (I.length / 4) ≤ I.length / 4 := min_le_right _ _
      linarith [h_eq]
  have h_final : min d (I.length / 4) ≥ delta / (C1 * scale) := by
    by_cases h_case : d ≤ I.length / 4
    · rw [min_eq_left h_case]
      dsimp only [d]
      field_simp [hscale_pos.ne'] <;> nlinarith [hC1_scale]
    · have h_ge : I.length / 4 ≤ d := by
        exact le_of_not_ge h_case
      rw [min_eq_right h_ge]
      have hI_len1 : (12 * K)⁻¹ ≤ I.length := hI_controlled.1
      have h11 : I.length / 4 ≥ 1 / (48 * K) := by
        have h12 : (12 * K)⁻¹ ≤ I.length := hI_len1
        have h13 : (12 * K)⁻¹ = 1 / (12 * K) := by
          field_simp [hK_pos.ne'] <;> ring
        rw [h13] at h12
        have h14 : I.length / 4 ≥ (1 / (12 * K)) / 4 := by gcongr
        have h15 : (1 / (12 * K)) / 4 = 1 / (48 * K) := by
          field_simp [hK_pos.ne'] <;> ring
        rw [h15] at h14
        exact h14
      have h13 : delta / scale ≤ 1 / Real.sqrt (6 * K) :=
        delta_div_scale_bound hK_pos ht_pos hdelta hscale hΔ_lower hdelta_le
      have h19 : 1 / (48 * K) ≥ (1 / Real.sqrt (6 * K)) / C1 := by
        have h20 : C1 * Real.sqrt (6 * K) ≥ 48 * K := by
          have h21 : C1 ≥ 100 * K := hC1_large
          have h22 : Real.sqrt (6 * K) ≥ 1 := by
            have h23 : 6 * K ≥ 1 := by linarith
            have h24 : Real.sqrt (6 * K) ≥ Real.sqrt 1 := Real.sqrt_le_sqrt h23
            have h25 : Real.sqrt 1 = 1 := by simp
            linarith
          have h26 : C1 * Real.sqrt (6 * K) ≥ 100 * K := by
            have h27 : C1 ≥ 0 := by linarith
            have h28 : C1 * Real.sqrt (6 * K) ≥ C1 := by
              have h29 : C1 * Real.sqrt (6 * K) ≥ C1 * 1 := by gcongr
              simpa using h29
            linarith
          linarith
        have h_pos1 : 0 < 48 * K := by positivity
        have h_pos2 : 0 < C1 * Real.sqrt (6 * K) := by positivity
        have h27 : 1 / (48 * K) ≥ 1 / (C1 * Real.sqrt (6 * K)) := by
          apply one_div_le_one_div_of_le
          · positivity
          · exact h20
        have h28 : (1 / Real.sqrt (6 * K)) / C1 = 1 / (C1 * Real.sqrt (6 * K)) := by
          field_simp <;> ring
        rw [h28]
        exact h27
      calc delta / (C1 * scale)
        = (delta / scale) / C1 := by ring
      _ ≤ (1 / Real.sqrt (6 * K)) / C1 := by gcongr
      _ ≤ 1 / (48 * K) := h19
      _ ≤ I.length / 4 := h11
  have h_main : J.length ≥ delta / (C1 * scale) := by
    linarith [h_len1, h_len2, h_final]
  have h_bound : delta ≤ C1 * scale * J.length := by
    have h_pos : 0 < C1 * scale := mul_pos hC1_pos hscale_pos
    have hne : (C1 * scale) ≠ 0 := h_pos.ne'
    have h : C1 * scale * (delta / (C1 * scale)) = delta := by
      field_simp [hne]
    have h_ineq : C1 * scale * (delta / (C1 * scale)) ≤ C1 * scale * J.length := by
      gcongr <;> linarith
    rw [h] at h_ineq
    exact h_ineq
  exact ⟨j, h_x_in_J, h_bound⟩

end Kakeya.Cinematic
