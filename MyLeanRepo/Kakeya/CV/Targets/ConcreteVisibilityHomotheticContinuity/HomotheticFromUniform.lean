import MyLeanRepo.Kakeya.CV.Mollification
import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Homothetic convergence from uniform gauge convergence

A sequence of one-homogeneous nonnegative gauge functions converging uniformly
on the unit ball induces homothetic convergence of the corresponding unit
gauge balls.
-/

namespace Kakeya.CV

theorem homothetic_converges_of_uniform_gauge
    (A : ℕ → Point 3 → ℝ) (B : Point 3 → ℝ)
    (hAm : ∀ (n : ℕ) (u : Point 3), 0 ≤ A n u)
    (hBm : ∀ (u : Point 3), 0 ≤ B u)
    (hAh : ∀ (n : ℕ) (c : ℝ) (u : Point 3), 0 ≤ c → A n (c • u) = c * A n u)
    (hBh : ∀ (c : ℝ) (u : Point 3), 0 ≤ c → B (c • u) = c * B u)
    (huni : TendstoUniformlyOn A B Filter.atTop (unitBall 3)) :
    HomotheticConvergesAt 0
      (fun n => unitBall 3 ∩ {u | A n u ≤ 1})
      (unitBall 3 ∩ {u | B u ≤ 1}) := by
  intro α hα
  set δ : ℝ := α - 1 with hδdef
  have hδpos : 0 < δ := by linarith
  have hαpos : 0 < α := by linarith
  have hαinvpos : 0 < α⁻¹ := by positivity
  have hαinvle1 : α⁻¹ ≤ 1 := by
    have h : 1 ≤ α := by linarith
    exact inv_le_one_of_one_le₀ h
  have h_main : ∀ᶠ n in Filter.atTop,
      ∀ u ∈ unitBall 3, dist (B u) (A n u) < δ :=
    (Metric.tendstoUniformlyOn_iff.mp huni) δ hδpos
  filter_upwards [h_main] with n hn
  let K_n := unitBall 3 ∩ {u | A n u ≤ 1}
  let K := unitBall 3 ∩ {u | B u ≤ 1}
  have h_homothety_zero : ∀ (r : ℝ) (x : Point 3),
      (AffineMap.homothety (0 : Point 3) r) x = r • x := by
    intro r x
    simp [AffineMap.homothety_apply]
  have h1 : dilateAbout 0 α⁻¹ K_n ⊆ K := by
    intro x hx
    rcases hx with ⟨u, hu, hx_eq⟩
    have h_u1 : u ∈ unitBall 3 := hu.1
    have h_u2 : A n u ≤ 1 := hu.2
    have h_x_eq : x = α⁻¹ • u := by
      rw [h_homothety_zero] at hx_eq
      exact hx_eq.symm
    have h_δ : dist (B u) (A n u) < δ := hn u h_u1
    have h_Bu_lt : B u < α := by
      have h : |B u - A n u| < δ := by simpa [Real.dist_eq] using h_δ
      have h' : B u - A n u < δ := by
        calc B u - A n u ≤ |B u - A n u| := le_abs_self (B u - A n u)
             _ < δ := h
      linarith
    have h_norm : ‖α⁻¹ • u‖ ≤ 1 := by
      have h : ‖α⁻¹ • u‖ = α⁻¹ * ‖u‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hαinvpos]
      rw [h]
      have h2 : ‖u‖ ≤ 1 := by
        simpa [unitBall, Metric.mem_closedBall] using h_u1
      have h3 : α⁻¹ * ‖u‖ ≤ 1 := by
        calc α⁻¹ * ‖u‖ ≤ α⁻¹ * 1 := by gcongr
             _ = α⁻¹ := by exact mul_one α⁻¹
             _ ≤ 1 := hαinvle1
      exact h3
    have h_Bx : B (α⁻¹ • u) ≤ 1 := by
      have h5 : B (α⁻¹ • u) = α⁻¹ * B u := hBh α⁻¹ u (by positivity)
      rw [h5]
      have h6 : α⁻¹ * B u < 1 := by
        calc α⁻¹ * B u < α⁻¹ * α := by gcongr
             _ = 1 := by field_simp [hαpos.ne']
      linarith
    rw [h_x_eq]
    exact ⟨by simpa [unitBall, Metric.mem_closedBall] using h_norm, h_Bx⟩
  have h2 : K ⊆ dilateAbout 0 α K_n := by
    intro v hv
    have h_v1 : v ∈ unitBall 3 := hv.1
    have h_v2 : B v ≤ 1 := hv.2
    have h_δ : dist (B v) (A n v) < δ := hn v h_v1
    have h_Anv_lt : A n v < α := by
      have h : |B v - A n v| < δ := by simpa [Real.dist_eq] using h_δ
      have h' : A n v - B v < δ := by
        have h_abs : |A n v - B v| = |B v - A n v| := by
          rw [show A n v - B v = -(B v - A n v) by ring, abs_neg]
        calc A n v - B v ≤ |A n v - B v| := le_abs_self (A n v - B v)
             _ = |B v - A n v| := h_abs
             _ < δ := h
      linarith
    set w : Point 3 := α⁻¹ • v with hw_def
    have h_w1 : w ∈ unitBall 3 := by
      have h_norm_w : ‖w‖ = α⁻¹ * ‖v‖ := by
        rw [hw_def, norm_smul, Real.norm_eq_abs, abs_of_pos hαinvpos]
      have h2 : ‖v‖ ≤ 1 := by
        simpa [unitBall, Metric.mem_closedBall] using h_v1
      have h3 : ‖w‖ ≤ 1 := by
        rw [h_norm_w]
        calc α⁻¹ * ‖v‖ ≤ α⁻¹ * 1 := by gcongr
             _ = α⁻¹ := by exact mul_one α⁻¹
             _ ≤ 1 := hαinvle1
      simpa [unitBall, Metric.mem_closedBall] using h3
    have h_w2 : A n w ≤ 1 := by
      have h5 : A n w = α⁻¹ * A n v := by
        rw [hw_def]
        exact hAh n α⁻¹ v (by positivity)
      rw [h5]
      have h6 : α⁻¹ * A n v < 1 := by
        calc α⁻¹ * A n v < α⁻¹ * α := by gcongr
             _ = 1 := by field_simp [hαpos.ne']
      linarith
    have h_w_in_Kn : w ∈ K_n := ⟨h_w1, h_w2⟩
    have h_v_eq : (AffineMap.homothety (0 : Point 3) α) w = v := by
      rw [h_homothety_zero, hw_def]
      have h : α • (α⁻¹ • v) = v := by
        rw [smul_smul]
        have h2 : α * α⁻¹ = 1 := by field_simp [hαpos.ne']
        rw [h2, one_smul]
      exact h
    exact ⟨w, h_w_in_Kn, h_v_eq⟩
  exact ⟨h1, h2⟩

end Kakeya.CV
