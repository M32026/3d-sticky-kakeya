import MyLeanRepo.Kakeya.Cinematic.Statements
import MyLeanRepo.Kakeya.Cinematic.PreliminaryDichotomy
import MyLeanRepo.Kakeya.Cinematic.Targets.TangencySublevelDiameter.Helpers
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Real.Sqrt

-- Dune's verified wing-width ratio helper
-- import .ConvexCaseHelpers -- inline the lemma instead to avoid import issues

/-!
# Complete sublevel structure proof (PYZ Lemma 16(2b)+(2c))
-/

namespace Kakeya.Cinematic

-- ============================================================================
-- Rolle contradiction: three equal values of H on [a,b] leads to False
-- ============================================================================

lemma rolle_three_points
    {H : ℝ → ℝ} {K t a b : ℝ} (hK : 1 ≤ K) (ht : 0 < t)
    (H_diff1 : Differentiable ℝ H) (H_diff2 : Differentiable ℝ (deriv H))
    (hH'_bound : ∀ x ∈ Set.Icc a b, |deriv H x| ≤ t)
    (hH''_bound : ∀ x ∈ Set.Icc a b, |deriv (deriv H) x| ≤ t)
    (hH_large : ∀ x ∈ Set.Icc a b, (6 * K)⁻¹ * t ≤ |H x|)
    (h_curv : ∀ x ∈ Set.Icc a b, K⁻¹ * t ≤ |H x| + |deriv H x| + |deriv (deriv H) x|)
    (h_len : b - a ≤ 1 / (6 * K))
    (x1 x2 x3 : ℝ) (hx1 : x1 ∈ Set.Icc a b) (hx2 : x2 ∈ Set.Icc a b) (hx3 : x3 ∈ Set.Icc a b)
    (h12 : x1 < x2) (h23 : x2 < x3)
    (h_eq12 : H x1 = H x2) (h_eq23 : H x2 = H x3)
    (hHx1 : |H x1| = (6 * K)⁻¹ * t) : False := by
  let m := (6 * K)⁻¹ * t
  have hK_pos : 0 < K := by linarith
  have hm_pos : 0 < m := by positivity
  have h_mvt1 : ∃ y1 ∈ Set.Ioo x1 x2, deriv H y1 = 0 :=
    exists_hasDerivAt_eq_zero h12 (H_diff1.continuous.continuousOn) h_eq12
      (fun z _ => H_diff1.differentiableAt.hasDerivAt)
  rcases h_mvt1 with ⟨y1, hy1_Ioo, hH_y1⟩
  have h_mvt2 : ∃ y2 ∈ Set.Ioo x2 x3, deriv H y2 = 0 :=
    exists_hasDerivAt_eq_zero h23 (H_diff1.continuous.continuousOn) h_eq23
      (fun z _ => H_diff1.differentiableAt.hasDerivAt)
  rcases h_mvt2 with ⟨y2, hy2_Ioo, hH_y2⟩
  have hy12 : y1 < y2 := by linarith [hy1_Ioo.2, hy2_Ioo.1]
  have h_mvt3 : ∃ z ∈ Set.Ioo y1 y2, deriv (deriv H) z = 0 :=
    exists_hasDerivAt_eq_zero hy12 (H_diff2.continuous.continuousOn)
      (by rw [hH_y1, hH_y2])
      (fun z _ => H_diff2.differentiableAt.hasDerivAt)
  rcases h_mvt3 with ⟨z, hz_Ioo, hH''z⟩
  have hz_Icc : z ∈ Set.Icc a b := by
    have h1 : a ≤ y1 := by linarith [hx1.1, hy1_Ioo.1]
    have h2 : y2 ≤ b := by linarith [hy2_Ioo.2, hx3.2]
    exact ⟨by linarith [hz_Ioo.1], by linarith [hz_Ioo.2]⟩
  have hy1_Icc : y1 ∈ Set.Icc a b := by
    exact ⟨by linarith [hx1.1, hy1_Ioo.1], by linarith [hy1_Ioo.2, hx2.2]⟩
  have h_z_y1_nonneg : 0 ≤ z - y1 := by linarith [hz_Ioo.1]
  have h_z_y1_dist : |z - y1| ≤ b - a := by
    rw [abs_of_nonneg h_z_y1_nonneg]
    have h1 : z < y2 := hz_Ioo.2
    have h2 : y2 < x3 := hy2_Ioo.2
    have h3 : x3 ≤ b := hx3.2
    have h4 : a ≤ y1 := hy1_Icc.1
    linarith
  have h_bound_H'' : ∀ w : ℝ, w ∈ Set.Icc (min y1 z) (max y1 z) → |deriv (deriv H) w| ≤ t := by
    intro w hw
    have w_Icc : w ∈ Set.Icc a b := by
      have hmin1 : a ≤ min y1 z := by apply le_min <;> linarith [hy1_Icc.1, hz_Icc.1]
      have hmax2 : max y1 z ≤ b := by apply max_le <;> linarith [hy1_Icc.2, hz_Icc.2]
      exact ⟨by linarith [hw.1, hmin1], by linarith [hw.2, hmax2]⟩
    exact hH''_bound w w_Icc
  have hMVT_deriv : |deriv H z - deriv H y1| ≤ t * |z - y1| :=
    real_lipschitz_of_deriv_bound H_diff2 h_bound_H''
  have h_deriv_z_le : |deriv H z| ≤ m := by
    calc |deriv H z|
      = |deriv H z - deriv H y1| := by rw [hH_y1] <;> simp
    _ ≤ t * |z - y1| := hMVT_deriv
    _ ≤ t * (b - a) := by gcongr
    _ ≤ m := by
      have h5 : t * (b - a) ≤ t / (6 * K) := by
        calc t * (b - a) ≤ t * (1 / (6 * K)) := by gcongr
          _ = t / (6 * K) := by ring
      have h6 : t / (6 * K) = m := by
        simp [m] <;> field_simp [hK_pos.ne'] <;> ring
      rw [h6] at h5; exact h5
  have h_curv_z : K⁻¹ * t ≤ |H z| + |deriv H z| + |deriv (deriv H) z| := h_curv z hz_Icc
  have h_six_m : K⁻¹ * t = 6 * m := by
    simp [m] <;> field_simp [hK_pos.ne'] <;> ring
  rw [h_six_m] at h_curv_z
  have h0 : |deriv (deriv H) z| = 0 := by rw [hH''z] <;> simp
  rw [h0] at h_curv_z
  have h_H_z_lower : 5 * m ≤ |H z| := by linarith
  have h_z_x1_nonneg : 0 ≤ z - x1 := by linarith [hz_Ioo.1, hy1_Ioo.1]
  have h_z_x1_dist : |z - x1| ≤ b - a := by
    rw [abs_of_nonneg h_z_x1_nonneg]
    have h1 : z < y2 := hz_Ioo.2
    have h2 : y2 < x3 := hy2_Ioo.2
    have h3 : x3 ≤ b := hx3.2
    have h4 : a ≤ x1 := hx1.1
    linarith
  have h_bound_H' : ∀ w : ℝ, w ∈ Set.Icc (min x1 z) (max x1 z) → |deriv H w| ≤ t := by
    intro w hw
    have w_Icc : w ∈ Set.Icc a b := by
      have hmin1 : a ≤ min x1 z := by apply le_min <;> linarith [hx1.1, hz_Icc.1]
      have hmax2 : max x1 z ≤ b := by apply max_le <;> linarith [hx1.2, hz_Icc.2]
      exact ⟨by linarith [hw.1, hmin1], by linarith [hw.2, hmax2]⟩
    exact hH'_bound w w_Icc
  have hMVT_H : |H z - H x1| ≤ t * |z - x1| :=
    real_lipschitz_of_deriv_bound H_diff1 h_bound_H'
  have h_triangle : |H z| ≤ |H x1| + |H z - H x1| := by
    have h_eq : H z = H x1 + (H z - H x1) := by ring
    have h : |H z| ≤ |H x1| + |H z - H x1| := by
      rw [h_eq]
      simpa [Real.norm_eq_abs] using norm_add_le (H x1) (H z - H x1)
    exact h
  have h_H_z_upper : |H z| ≤ 2 * m := by
    calc |H z|
      ≤ |H x1| + |H z - H x1| := h_triangle
    _ = m + |H z - H x1| := by rw [hHx1] <;> ring
    _ ≤ m + t * |z - x1| := by gcongr
    _ ≤ m + t * (b - a) := by gcongr
    _ ≤ m + m := by
      have h5 : t * (b - a) ≤ m := by
        calc t * (b - a) ≤ t * (1 / (6 * K)) := by gcongr
          _ = t / (6 * K) := by ring
          _ = m := by simp [m] <;> field_simp [hK_pos.ne'] <;> ring
      linarith
    _ = 2 * m := by ring
  linarith

-- ============================================================================
-- Key helper: (L) for h → E has at most 2 points (Rolle argument)
-- ============================================================================

lemma large_h_at_most_two_points
    {K : ℝ} (hK : 1 ≤ K)
    {I : ParameterInterval} {f g : C2Function} {t delta : ℝ}
    (ht_pos : 0 < t)
    (ht_eq : t = c2Distance f g)
    (hI_short : I.IsShort K)
    (hL_h : ∀ (x : UnitPoint), x ∈ I.carrier → (6 * K)⁻¹ * t ≤ |f x - g x|)
    (h_curv : ∀ (x : UnitPoint), K⁻¹ * t ≤ jetGap f g x)
    (hdelta : 0 < delta)
    (hdelta_le : delta ≤ (6 * K)⁻¹ * t)
    (E : Set UnitPoint)
    (hE : E = tangencySublevelSetOn I f g delta) :
    E.Finite ∧ Set.ncard E ≤ 2 := by
  let H : ℝ → ℝ := f.extension - g.extension
  let a := I.left
  let b := I.right
  let m : ℝ := (6 * K)⁻¹ * t
  have hK_pos : 0 < K := by linarith
  have hm_pos : 0 < m := by positivity
  have hH_c2 : ContDiff ℝ 2 H := ContDiff.sub f.extension_contDiff g.extension_contDiff
  have hH_diff1 : Differentiable ℝ H := hH_c2.differentiable (by norm_num)
  have hH_diff2 : Differentiable ℝ (deriv H) := by
    have h1 : ContDiff ℝ 1 (deriv H) := hH_c2.deriv'
    exact h1.differentiable (by norm_num)
  have h_len : b - a ≤ (6 * K)⁻¹ := by
    have h : I.length ≤ (6 * K)⁻¹ := hI_short
    have h2 : I.length = b - a := by
      simp [ParameterInterval.length, a, b] <;> ring
    rw [h2] at h
    exact h
  have h_eval : ∀ (x : UnitPoint), H (x : ℝ) = f x - g x := by
    intro x; simp [H]
  have h_deriv_eval : ∀ (x : UnitPoint), deriv H (x : ℝ) = f.firstDeriv x - g.firstDeriv x := by
    intro x
    have h_f_diff : Differentiable ℝ f.extension := f.extension_contDiff.differentiable (by norm_num)
    have h_g_diff : Differentiable ℝ g.extension := g.extension_contDiff.differentiable (by norm_num)
    have h1 : deriv H (x : ℝ) = deriv f.extension (x : ℝ) - deriv g.extension (x : ℝ) :=
      deriv_sub h_f_diff.differentiableAt h_g_diff.differentiableAt
    rw [h1]
    rw [C2Function.deriv_extension_eq_firstDeriv, C2Function.deriv_extension_eq_firstDeriv] <;> abel
  have h_deriv2_eval : ∀ (x : UnitPoint), deriv (deriv H) (x : ℝ) = f.secondDeriv x - g.secondDeriv x := by
    intro x
    have h_f_c2 : ContDiff ℝ 2 f.extension := f.extension_contDiff
    have h_g_c2 : ContDiff ℝ 2 g.extension := g.extension_contDiff
    have h_f_diff1 : Differentiable ℝ f.extension := h_f_c2.differentiable (by norm_num)
    have h_g_diff1 : Differentiable ℝ g.extension := h_g_c2.differentiable (by norm_num)
    have h_eq_fun : deriv H = deriv f.extension - deriv g.extension := by
      funext y
      exact deriv_sub h_f_diff1.differentiableAt h_g_diff1.differentiableAt
    have h_f_deriv_c2 : ContDiff ℝ 1 (deriv f.extension) := h_f_c2.deriv'
    have h_g_deriv_c2 : ContDiff ℝ 1 (deriv g.extension) := h_g_c2.deriv'
    have h_f_diff2 : Differentiable ℝ (deriv f.extension) := h_f_deriv_c2.differentiable (by norm_num)
    have h_g_diff2 : Differentiable ℝ (deriv g.extension) := h_g_deriv_c2.differentiable (by norm_num)
    rw [h_eq_fun]
    have h2 : deriv (deriv f.extension - deriv g.extension) (x : ℝ) =
        deriv (deriv f.extension) (x : ℝ) - deriv (deriv g.extension) (x : ℝ) :=
      deriv_sub h_f_diff2.differentiableAt h_g_diff2.differentiableAt
    rw [h2]
    rw [C2Function.secondDeriv_extension_eq_secondDeriv, C2Function.secondDeriv_extension_eq_secondDeriv] <;> abel
  have hH_large : ∀ (r : ℝ), r ∈ Set.Icc a b → m ≤ |H r| := by
    intro r hr
    let x : UnitPoint := ⟨r, ⟨by linarith [I.left_mem.1, hr.1], by linarith [I.right_mem.2, hr.2]⟩⟩
    have h_x_I : x ∈ I.carrier := by
      simp only [ParameterInterval.carrier, Set.mem_setOf_eq] <;> exact hr
    have h : H r = f x - g x := h_eval x
    rw [h]; exact hL_h x h_x_I
  have hH''_bound : ∀ (r : ℝ), r ∈ Set.Icc a b → |deriv (deriv H) r| ≤ t := by
    intro r hr
    let x : UnitPoint := ⟨r, ⟨by linarith [I.left_mem.1, hr.1], by linarith [I.right_mem.2, hr.2]⟩⟩
    have h : deriv (deriv H) r = f.secondDeriv x - g.secondDeriv x := h_deriv2_eval x
    rw [h]
    have h_bound : |f.secondDeriv x - g.secondDeriv x| ≤ c2Distance f g :=
      abs_secondDeriv_sub_le_c2Distance f g x
    rw [ht_eq] at *; exact h_bound
  have hH'_bound : ∀ (r : ℝ), r ∈ Set.Icc a b → |deriv H r| ≤ t := by
    intro r hr
    let x : UnitPoint := ⟨r, ⟨by linarith [I.left_mem.1, hr.1], by linarith [I.right_mem.2, hr.2]⟩⟩
    have h : deriv H r = f.firstDeriv x - g.firstDeriv x := h_deriv_eval x
    rw [h]
    have h_bound : |f.firstDeriv x - g.firstDeriv x| ≤ c2Distance f g :=
      abs_firstDeriv_sub_le_c2Distance f g x
    rw [ht_eq] at *; exact h_bound
  have h_len' : b - a ≤ 1 / (6 * K) := by
    have h : b - a ≤ (6 * K)⁻¹ := h_len
    have h2 : (1 : ℝ) / (6 * K) = (6 * K)⁻¹ := by field_simp <;> ring
    rw [h2]
    exact h
  have h_curv_real : ∀ (r : ℝ), r ∈ Set.Icc a b → K⁻¹ * t ≤ |H r| + |deriv H r| + |deriv (deriv H) r| := by
    intro r hr
    let x : UnitPoint := ⟨r, ⟨by linarith [I.left_mem.1, hr.1], by linarith [I.right_mem.2, hr.2]⟩⟩
    have h1 : H r = f x - g x := h_eval x
    have h2 : deriv H r = f.firstDeriv x - g.firstDeriv x := h_deriv_eval x
    have h3 : deriv (deriv H) r = f.secondDeriv x - g.secondDeriv x := h_deriv2_eval x
    rw [h1, h2, h3]
    exact h_curv x
  have h_ne_zero : ∀ (r : ℝ), r ∈ Set.Icc a b → H r ≠ 0 := by
    intro r hr
    have h1 : m ≤ |H r| := hH_large r hr
    have h2 : 0 < |H r| := by linarith
    exact abs_ne_zero.mp (ne_of_gt h2)
  have hH_cont : ContinuousOn H (Set.Icc a b) := hH_diff1.continuous.continuousOn
  have h_sign : (∀ r ∈ Set.Icc a b, 0 < H r) ∨ (∀ r ∈ Set.Icc a b, H r < 0) :=
    constant_sign_of_never_zero I.left_le_right hH_cont h_ne_zero
  let S_real : Set ℝ := {r ∈ Set.Icc a b | |H r| ≤ delta}
  -- On S_real, |H| = m exactly, and H is constant
  have hS_eq : ∀ r ∈ S_real, |H r| = m := by
    intro r hr
    have h1 : r ∈ Set.Icc a b := hr.1
    have h2 : |H r| ≤ delta := hr.2
    have h3 : m ≤ |H r| := hH_large r h1
    have h4 : delta ≤ m := hdelta_le
    linarith
  have h_const : ∀ (r1 r2 : ℝ), r1 ∈ S_real → r2 ∈ S_real → H r1 = H r2 := by
    intro r1 r2 hr1 hr2
    have h_abs1 : |H r1| = m := hS_eq r1 hr1
    have h_abs2 : |H r2| = m := hS_eq r2 hr2
    rcases h_sign with (h_pos | h_neg)
    · have h1 : H r1 = m := by
        have hpos : 0 < H r1 := h_pos r1 hr1.1
        rw [abs_of_pos hpos] at h_abs1; linarith
      have h2 : H r2 = m := by
        have hpos : 0 < H r2 := h_pos r2 hr2.1
        rw [abs_of_pos hpos] at h_abs2; linarith
      linarith
    · have h1 : H r1 = -m := by
        have hneg : H r1 < 0 := h_neg r1 hr1.1
        rw [abs_of_neg hneg] at h_abs1; linarith
      have h2 : H r2 = -m := by
        have hneg : H r2 < 0 := h_neg r2 hr2.1
        rw [abs_of_neg hneg] at h_abs2; linarith
      linarith
  -- No three distinct points in S_real
  have h_no_three : ∀ (r1 r2 r3 : ℝ), r1 ∈ S_real → r2 ∈ S_real → r3 ∈ S_real →
      r1 = r2 ∨ r2 = r3 ∨ r1 = r3 := by
    intro r1 r2 r3 hr1 hr2 hr3
    by_cases h12 : r1 = r2
    · exact Or.inl h12
    · by_cases h23 : r2 = r3
      · exact Or.inr (Or.inl h23)
      · by_cases h13 : r1 = r3
        · exact Or.inr (Or.inr h13)
        · exfalso
          have h_eq12 : H r1 = H r2 := h_const r1 r2 hr1 hr2
          have h_eq23 : H r2 = H r3 := h_const r2 r3 hr2 hr3
          have h_eq13 : H r1 = H r3 := h_const r1 r3 hr1 hr3
          have h_eq21 : H r2 = H r1 := h_const r2 r1 hr2 hr1
          have h_eq31 : H r3 = H r1 := h_const r3 r1 hr3 hr1
          have h_eq32 : H r3 = H r2 := h_const r3 r2 hr3 hr2
          have hr1_I : r1 ∈ Set.Icc a b := hr1.1
          have hr2_I : r2 ∈ Set.Icc a b := hr2.1
          have hr3_I : r3 ∈ Set.Icc a b := hr3.1
          have hHx1 : |H r1| = m := hS_eq r1 hr1
          have hHx2 : |H r2| = m := hS_eq r2 hr2
          have hHx3 : |H r3| = m := hS_eq r3 hr3
          by_cases h_a : r1 < r2
          · -- r1 < r2
            by_cases h_b : r2 < r3
            · -- r1 < r2 < r3
              exact rolle_three_points hK ht_pos hH_diff1 hH_diff2 hH'_bound hH''_bound hH_large h_curv_real h_len'
                r1 r2 r3 hr1_I hr2_I hr3_I h_a h_b h_eq12 h_eq23 hHx1
            · -- r3 < r2
              have h_b' : r3 < r2 := by
                have h_le : r3 ≤ r2 := by linarith
                exact lt_of_le_of_ne h_le (Ne.symm h23)
              by_cases h_c : r1 < r3
              · -- r1 < r3 < r2
                exact rolle_three_points hK ht_pos hH_diff1 hH_diff2 hH'_bound hH''_bound hH_large h_curv_real h_len'
                  r1 r3 r2 hr1_I hr3_I hr2_I h_c h_b' h_eq13 h_eq32 hHx1
              · -- r3 < r1 < r2
                have h_c' : r3 < r1 := by
                  have h_le : r3 ≤ r1 := by linarith
                  exact lt_of_le_of_ne h_le (Ne.symm h13)
                exact rolle_three_points hK ht_pos hH_diff1 hH_diff2 hH'_bound hH''_bound hH_large h_curv_real h_len'
                  r3 r1 r2 hr3_I hr1_I hr2_I h_c' h_a h_eq31 h_eq12 hHx3
          · -- r2 < r1
            have h_a' : r2 < r1 := by
              have h_le : r2 ≤ r1 := by linarith
              exact lt_of_le_of_ne h_le (Ne.symm h12)
            by_cases h_b : r1 < r3
            · -- r2 < r1 < r3
              exact rolle_three_points hK ht_pos hH_diff1 hH_diff2 hH'_bound hH''_bound hH_large h_curv_real h_len'
                r2 r1 r3 hr2_I hr1_I hr3_I h_a' h_b h_eq21 h_eq13 hHx2
            · -- r3 < r1
              have h_b' : r3 < r1 := by
                have h_le : r3 ≤ r1 := by linarith
                exact lt_of_le_of_ne h_le (Ne.symm h13)
              by_cases h_c : r2 < r3
              · -- r2 < r3 < r1
                exact rolle_three_points hK ht_pos hH_diff1 hH_diff2 hH'_bound hH''_bound hH_large h_curv_real h_len'
                  r2 r3 r1 hr2_I hr3_I hr1_I h_c h_b' h_eq23 h_eq31 hHx2
              · -- r3 < r2 < r1
                have h_c' : r3 < r2 := by
                  have h_le : r3 ≤ r2 := by linarith
                  exact lt_of_le_of_ne h_le (Ne.symm h23)
                exact rolle_three_points hK ht_pos hH_diff1 hH_diff2 hH'_bound hH''_bound hH_large h_curv_real h_len'
                  r3 r2 r1 hr3_I hr2_I hr1_I h_c' h_a' h_eq32 h_eq21 hHx3
  -- E maps injectively into S_real
  have hE_sub : ∀ (x : UnitPoint), x ∈ E → (x : ℝ) ∈ S_real := by
    intro x hx
    have h1 : x ∈ I.centeredCarrier (1 / 4) := (hE ▸ hx).1
    have h2 : x ∈ I.carrier :=
      I.centeredCarrier_subset_carrier (by norm_num) (by norm_num) h1
    have h3 : |f x - g x| ≤ delta := (hE ▸ hx).2
    have h4 : H (x : ℝ) = f x - g x := h_eval x
    exact ⟨h2, by rw [h4]; exact h3⟩
  have h_inj : Set.InjOn (fun (x : UnitPoint) => (x : ℝ)) E := by
    intro x _ y _ h
    exact Subtype.ext h
  have h_img_sub : (fun (x : UnitPoint) => (x : ℝ)) '' E ⊆ S_real := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact hE_sub x hx
  -- Prove S_real.Finite: if infinite, pick 3 distinct elements, contradiction
  have hS_fin : S_real.Finite := by
    by_contra hinf
    have hS_inf : S_real.Infinite := by exact Set.not_finite.mp hinf
    rcases Set.Infinite.exists_subset_ncard_eq hS_inf 3 with ⟨t, ht_sub, ht_fin, ht_ncard⟩
    let tfin := ht_fin.toFinset
    have h_t_coe : (tfin : Set ℝ) = t := ht_fin.coe_toFinset
    have hcard : tfin.card = 3 := by
      have h_eq : Set.ncard t = tfin.card := by
        exact Set.ncard_eq_toFinset_card t ht_fin
      rw [←h_eq]; exact ht_ncard
    rcases Finset.card_eq_three.1 hcard with ⟨x1, x2, x3, hx12, hx13, hx23, h_t_eq⟩
    have h1t : x1 ∈ tfin := by rw [h_t_eq] <;> simp
    have h2t : x2 ∈ tfin := by rw [h_t_eq] <;> simp
    have h3t : x3 ∈ tfin := by rw [h_t_eq] <;> simp
    have h1 : x1 ∈ S_real := ht_sub (by rw [←h_t_coe]; exact h1t)
    have h2 : x2 ∈ S_real := ht_sub (by rw [←h_t_coe]; exact h2t)
    have h3 : x3 ∈ S_real := ht_sub (by rw [←h_t_coe]; exact h3t)
    have h4 := h_no_three x1 x2 x3 h1 h2 h3
    rcases h4 with (h4 | h5 | h6)
    · exact hx12 h4
    · exact hx23 h5
    · exact hx13 h6
  -- E is finite because it injects into S_real
  let img : Set ℝ := (fun (x : UnitPoint) => (x : ℝ)) '' E
  have himg_fin : img.Finite := hS_fin.subset h_img_sub
  have hE_fin : E.Finite := by
    exact (Set.finite_image_iff h_inj).mp himg_fin
  -- Prove Set.ncard E ≤ 2
  have himg_sub : img ⊆ S_real := h_img_sub
  have h_eq : Set.ncard img = Set.ncard E := by
    exact Set.InjOn.ncard_image h_inj
  have h_ncard_E_le_2 : Set.ncard E ≤ 2 := by
    rw [←h_eq]
    by_contra h
    have h3 : 3 ≤ Set.ncard img := by linarith
    let sfin : Finset ℝ := himg_fin.toFinset
    have h4 : (sfin : Set ℝ) = img := himg_fin.coe_toFinset
    have h5 : Set.ncard img = sfin.card := by
      exact Set.ncard_eq_toFinset_card img himg_fin
    have h3' : 3 ≤ sfin.card := by
      rw [←h5]; exact h3
    have h6 : ∃ (t : Finset ℝ), t ⊆ sfin ∧ t.card = 3 := Finset.exists_subset_card_eq h3'
    rcases h6 with ⟨t, ht_sub, ht_card⟩
    rcases Finset.card_eq_three.1 ht_card with ⟨x1, x2, x3, hx12, hx13, hx23, h_t_eq⟩
    have h1t : x1 ∈ t := by rw [h_t_eq] <;> simp
    have h2t : x2 ∈ t := by rw [h_t_eq] <;> simp
    have h3t : x3 ∈ t := by rw [h_t_eq] <;> simp
    have h1 : x1 ∈ S_real := himg_sub (h4 ▸ ht_sub h1t)
    have h2 : x2 ∈ S_real := himg_sub (h4 ▸ ht_sub h2t)
    have h3'' : x3 ∈ S_real := himg_sub (h4 ▸ ht_sub h3t)
    have h4' := h_no_three x1 x2 x3 h1 h2 h3''
    rcases h4' with (h4' | h5' | h6')
    · exact hx12 h4'
    · exact hx23 h5'
    · exact hx13 h6'
  exact ⟨hE_fin, h_ncard_E_le_2⟩

-- ============================================================================
-- Helper: abstract scale-to-length bound
-- ============================================================================

lemma abstract_scale_bound {K t delta scale C1 : ℝ}
    (hK : 1 ≤ K) (ht_pos : 0 < t) (hdelta : 0 < delta)
    (h_scale_pos : 0 < scale) (hC1_large : 100 * K ≤ C1)
    (h_scale_le : scale ≤ Real.sqrt 3 * t) :
    12 * K * delta / t ≤ C1 * delta / scale := by
  have h1 : 12 * K * scale ≤ 12 * K * (Real.sqrt 3 * t) := by
    have h_pos : 0 ≤ 12 * K := by linarith
    exact mul_le_mul_of_nonneg_left h_scale_le h_pos
  have h2 : 12 * Real.sqrt 3 ≤ 100 := by
    have h3 : Real.sqrt 3 ≤ 2 := by
      have h4 : Real.sqrt 3 ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by norm_num)
      have h5 : Real.sqrt 4 = 2 := by rw [Real.sqrt_eq_cases] <;> norm_num
      linarith
    nlinarith
  have h3 : 12 * K * scale ≤ 100 * K * t := by
    calc 12 * K * scale
      ≤ 12 * K * (Real.sqrt 3 * t) := h1
    _ = (12 * Real.sqrt 3) * K * t := by ring
    _ ≤ 100 * K * t := by
      have h_pos : 0 ≤ K * t := by positivity
      nlinarith
  have h4 : 12 * K * scale ≤ C1 * t := by
    calc 12 * K * scale ≤ 100 * K * t := h3
    _ ≤ C1 * t := mul_le_mul_of_nonneg_right hC1_large (by linarith)
  have hdelta_nonneg : 0 ≤ delta := le_of_lt hdelta
  have h5 : 12 * K * delta * scale ≤ C1 * delta * t := by
    have h51 : 12 * K * delta * scale = (12 * K * scale) * delta := by ring
    have h52 : C1 * delta * t = (C1 * t) * delta := by ring
    rw [h51, h52]
    exact mul_le_mul_of_nonneg_right h4 hdelta_nonneg
  have h_pos1 : 0 < t := ht_pos
  have h_pos2 : 0 < scale := h_scale_pos
  have h6 : 12 * K * delta / t = (12 * K * delta * scale) / (t * scale) := by
    field_simp [h_pos1.ne', h_pos2.ne'] <;> ring
  have h7 : C1 * delta / scale = (C1 * delta * t) / (t * scale) := by
    field_simp [h_pos1.ne', h_pos2.ne'] <;> ring
  rw [h6, h7]
  apply div_le_div_of_nonneg_right h5
  positivity

lemma scale_le_sqrt3_t {I : ParameterInterval} {f g : C2Function} {t delta scale : ℝ}
    (ht_pos : 0 < t) (hdelta : 0 < delta)
    (hΔ_le : tangencyParameterOn I f g ≤ 2 * t)
    (hdelta_le_t : delta ≤ t)
    (hscale : scale = Real.sqrt ((tangencyParameterOn I f g + delta) * t)) :
    scale ≤ Real.sqrt 3 * t := by
  rw [hscale]
  have h1 : (tangencyParameterOn I f g + delta) * t ≤ 3 * t^2 := by
    have h2 : tangencyParameterOn I f g + delta ≤ 3 * t := by linarith
    nlinarith
  have h3 : Real.sqrt ((tangencyParameterOn I f g + delta) * t) ≤ Real.sqrt (3 * t^2) :=
    Real.sqrt_le_sqrt h1
  have h4 : Real.sqrt (3 * t^2) = Real.sqrt 3 * t := by
    have h5 : 0 ≤ t := by linarith
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq h5]
  rw [h4] at h3
  exact h3

-- Helper: bound delta / scale in terms of K (abstracts tangencyParameterOn)
lemma delta_div_scale_bound {K t delta scale Δ : ℝ}
    (hK_pos : 0 < K) (ht_pos : 0 < t) (hdelta : 0 < delta)
    (hscale : scale = Real.sqrt ((Δ + delta) * t))
    (hΔ_lower : (6 * K)⁻¹ * t ≤ Δ)
    (hdelta_le : delta ≤ (6 * K)⁻¹ * t) :
    delta / scale ≤ 1 / Real.sqrt (6 * K) := by
  have h14 : (6 * K)⁻¹ * t = t / (6 * K) := by
    field_simp [hK_pos.ne'] <;> ring
  have h15 : delta ≤ t / (6 * K) := by
    rw [←h14]
    exact hdelta_le
  have h18 : 0 ≤ Δ + delta := by
    have h181 : 0 ≤ (6 * K)⁻¹ * t := by positivity
    linarith
  have h19 : delta / Real.sqrt ((Δ + delta) * t) ≤ Real.sqrt (delta / t) := by
    have h20 : Real.sqrt ((Δ + delta) * t) ≥ Real.sqrt (delta * t) := by
      gcongr <;> linarith
    have h21 : delta / Real.sqrt ((Δ + delta) * t) ≤ delta / Real.sqrt (delta * t) := by
      gcongr
    have h22 : delta / Real.sqrt (delta * t) = Real.sqrt (delta / t) := by
      have h23 : 0 ≤ delta * t := by positivity
      have h24 : Real.sqrt (delta * t) = Real.sqrt delta * Real.sqrt t := by
        rw [Real.sqrt_mul] <;> linarith
      rw [h24]
      have h25 : (Real.sqrt delta)^2 = delta := Real.sq_sqrt (by linarith)
      have hsqrt_delta_pos : 0 < Real.sqrt delta := Real.sqrt_pos.mpr hdelta
      have hsqrt_t_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht_pos
      have h26 : delta / (Real.sqrt delta * Real.sqrt t) = Real.sqrt delta / Real.sqrt t := by
        set y := Real.sqrt delta * Real.sqrt t with hy_def
        have hne : y ≠ 0 := mul_ne_zero hsqrt_delta_pos.ne' hsqrt_t_pos.ne'
        have h : delta = (Real.sqrt delta / Real.sqrt t) * y := by
          simp only [hy_def]
          have h3 : (Real.sqrt delta / Real.sqrt t) * (Real.sqrt delta * Real.sqrt t) = (Real.sqrt delta)^2 := by
            field_simp [hsqrt_t_pos.ne'] <;> ring
          rw [h3]
          exact h25.symm
        exact (div_eq_iff hne).mpr h
      rw [h26]
      have h28 : Real.sqrt (delta / t) = Real.sqrt delta / Real.sqrt t := by
        rw [Real.sqrt_div (by positivity)] <;> ring
      exact h28.symm
    rw [h22] at h21
    exact h21
  have h23 : Real.sqrt (delta / t) ≤ 1 / Real.sqrt (6 * K) := by
    have h24 : delta / t ≤ 1 / (6 * K) := by
      have h25 : delta ≤ t / (6 * K) := h15
      have h26 : delta / t ≤ (t / (6 * K)) / t := by gcongr
      have h27 : (t / (6 * K)) / t = 1 / (6 * K) := by
        field_simp [ht_pos.ne', hK_pos.ne'] <;> ring
      rw [h27] at h26
      exact h26
    have h28 : Real.sqrt (delta / t) ≤ Real.sqrt (1 / (6 * K)) := Real.sqrt_le_sqrt h24
    have h29 : Real.sqrt (1 / (6 * K)) = 1 / Real.sqrt (6 * K) := by
      have h30 : Real.sqrt (1 / (6 * K)) = Real.sqrt 1 / Real.sqrt (6 * K) := by
        rw [Real.sqrt_div (by positivity)]
      rw [h30]
      have h31 : Real.sqrt 1 = 1 := by simp
      rw [h31] <;> ring
    rw [h29] at h28
    exact h28
  have h_scale_eq : delta / scale = delta / Real.sqrt ((Δ + delta) * t) := by
    rw [hscale]
  rw [h_scale_eq]
  exact h19.trans h23

-- ============================================================================
-- Helper: monotone h → E is one interval with length bound
-- ============================================================================


end Kakeya.Cinematic
