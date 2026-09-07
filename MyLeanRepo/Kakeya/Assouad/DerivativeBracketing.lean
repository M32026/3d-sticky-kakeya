import MyLeanRepo.Kakeya.Assouad.Definitions
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Derivative bracketing on a short interval

This isolates the one-dimensional pigeonholing step used before the centered
slope rescaling.
-/

namespace Kakeya.Assouad

/--
If `|f'|` is bounded below by `L`, bounded above by one, and `|f''| ≤ 1` on
`[a,b]`, then a subinterval of length at least `L/4` has `|f'|` confined to
one dyadic bracket `[m,2m]`.
-/
lemma derivative_bracketing
    {f : ℝ → ℝ} {a b L : ℝ}
    (hf : ContDiff ℝ 2 f)
    (hfd2 : ∀ x ∈ Set.Icc a b, |deriv (deriv f) x| ≤ 1)
    (hab : a < b) (hL : 0 < L)
    (h_length : L / 4 ≤ b - a)
    (h_low : ∀ x ∈ Set.Icc a b, L ≤ |deriv f x|)
    (h_high : ∀ x ∈ Set.Icc a b, |deriv f x| ≤ 1) :
    ∃ c d m : ℝ,
      a ≤ c ∧ c < d ∧ d ≤ b ∧
      L / 4 ≤ d - c ∧
      0 < m ∧ L ≤ m ∧ m ≤ 1 ∧
      ∀ x ∈ Set.Icc c d,
        m ≤ |deriv f x| ∧ |deriv f x| ≤ 2 * m := by
  have hdf_cd : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have hdf_diff : Differentiable ℝ (deriv f) :=
    hdf_cd.differentiable (by norm_num)
  have hdf_lipschitz :
      LipschitzOnWith 1 (deriv f) (Set.Icc a b) := by
    apply (convex_Icc a b).lipschitzOnWith_of_nnnorm_deriv_le
    · intro x _
      exact hdf_diff.differentiableAt
    · intro x hx
      apply NNReal.coe_le_coe.mp
      simpa [Real.norm_eq_abs] using hfd2 x hx
  let g : ℝ → ℝ := fun x => |deriv f x|
  have hg_cont : Continuous g :=
    hdf_diff.continuous.abs
  have hg_lipschitz :
      ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
        |g x - g y| ≤ |x - y| := by
    intro x hx y hy
    calc
      |g x - g y|
          = abs (|deriv f x| - |deriv f y|) := rfl
      _ ≤ |deriv f x - deriv f y| := abs_abs_sub_abs_le _ _
      _ = dist (deriv f x) (deriv f y) := by
        rw [Real.dist_eq]
      _ ≤ dist x y := by
        simpa using hdf_lipschitz.dist_le_mul x hx y hy
      _ = |x - y| := Real.dist_eq x y
  obtain ⟨x_min, hx_min, hmin⟩ :
      ∃ x_min ∈ Set.Icc a b, ∀ x ∈ Set.Icc a b, g x_min ≤ g x :=
    isCompact_Icc.exists_isMinOn
      ⟨a, le_rfl, hab.le⟩ hg_cont.continuousOn
  set m : ℝ := g x_min with hm_def
  have hm_pos : 0 < m := by
    have := h_low x_min hx_min
    linarith
  have hm_low : L ≤ m := h_low x_min hx_min
  have hm_high : m ≤ 1 := h_high x_min hx_min
  let c : ℝ := max a (x_min - m)
  let d : ℝ := min b (x_min + m)
  have hc : a ≤ c := le_max_left _ _
  have hd : d ≤ b := min_le_left _ _
  have hcd_length : L / 4 ≤ d - c := by
    by_cases hleft : a ≤ x_min - m
    · rw [show c = x_min - m by simp [c, max_eq_right hleft]]
      by_cases hright : b ≤ x_min + m
      · rw [show d = b by simp [d, min_eq_left hright]]
        have : m ≤ b - x_min + m := by linarith [hx_min.2]
        linarith
      · rw [show d = x_min + m by
          simp [d, min_eq_right (le_of_not_ge hright)]]
        linarith
    · rw [show c = a by simp [c, max_eq_left (le_of_not_ge hleft)]]
      by_cases hright : b ≤ x_min + m
      · rw [show d = b by simp [d, min_eq_left hright]]
        exact h_length
      · rw [show d = x_min + m by
          simp [d, min_eq_right (le_of_not_ge hright)]]
        have : m ≤ x_min + m - a := by linarith [hx_min.1]
        linarith
  have hcd : c < d := by
    linarith [hcd_length]
  have hbracket :
      ∀ x ∈ Set.Icc c d,
        m ≤ |deriv f x| ∧ |deriv f x| ≤ 2 * m := by
    intro x hx
    have hx_ab : x ∈ Set.Icc a b :=
      ⟨hc.trans hx.1, hx.2.trans hd⟩
    have hx_near : |x - x_min| ≤ m := by
      have hleft : x_min - m ≤ x := by
        exact (le_max_right a (x_min - m)).trans (hx.1)
      have hright : x ≤ x_min + m := by
        exact hx.2.trans (min_le_right b (x_min + m))
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    constructor
    · exact hmin x hx_ab
    · have hchange := hg_lipschitz x hx_ab x_min hx_min
      have hg_upper : g x ≤ g x_min + |x - x_min| := by
        linarith [le_abs_self (g x - g x_min)]
      simpa [g, hm_def] using
        (show g x ≤ 2 * m by linarith)
  exact ⟨c, d, m, hc, hcd, hd, hcd_length, hm_pos, hm_low, hm_high,
    hbracket⟩

end Kakeya.Assouad
