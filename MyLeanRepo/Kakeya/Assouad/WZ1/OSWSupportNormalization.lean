import MyLeanRepo.Kakeya.Assouad.WZ1.OSWSupportNormalizationStatement
import MyLeanRepo.Kakeya.Assouad.WZ1.SmoothedMeasure.Support

/-!
WZ1 Proposition 41 infrastructure: normalize one separated finite pair by a
common similarity so its smoothed measures satisfy the OSW support geometry.
-/

namespace Kakeya.Assouad

open MeasureTheory Set Metric

theorem wz1_osw_support_normalization : WZ1OSWSupportNormalizationStatement := by
  intro delta G₁ G₂ hG1ne hG2ne hdelta_pos hdelta_le
    hG1_sep hG2_sep hG1_ball hG2_ball hG1_diam hG2_diam h_mutual
  classical
  -- Step 1: Find closest pair
  have h_product_nonempty : (G₁ ×ˢ G₂).Nonempty := hG1ne.product hG2ne
  have h_min : ∃ p ∈ G₁ ×ˢ G₂, ∀ q ∈ G₁ ×ˢ G₂, dist p.1 p.2 ≤ dist q.1 q.2 :=
    Finset.exists_min_image (G₁ ×ˢ G₂) (fun p : Point2 × Point2 => dist p.1 p.2) h_product_nonempty
  rcases h_min with ⟨⟨center₁, center₂⟩, hmem, hmin⟩
  have hcenter1_mem : center₁ ∈ G₁ := (Finset.mem_product.mp hmem).1
  have hcenter2_mem : center₂ ∈ G₂ := (Finset.mem_product.mp hmem).2
  have h_closest : ∀ x ∈ G₁, ∀ y ∈ G₂, dist center₁ center₂ ≤ dist x y := by
    intro x hx y hy
    exact hmin (x, y) (Finset.mem_product.mpr ⟨hx, hy⟩)
  set d : ℝ := dist center₁ center₂ with hd_def
  -- Step 2: Scale bounds
  have hd_lower : (1 : ℝ) / 2 ≤ d := h_mutual center₁ hcenter1_mem center₂ hcenter2_mem
  have hd_upper : d ≤ 2 := by
    have h1 : dist center₁ 0 ≤ 1 := hG1_ball center₁ hcenter1_mem
    have h2 : dist center₂ 0 ≤ 1 := hG2_ball center₂ hcenter2_mem
    have h3 : dist center₁ center₂ ≤ dist center₁ 0 + dist 0 center₂ := dist_triangle _ _ _
    have h4 : dist 0 center₂ = dist center₂ 0 := dist_comm _ _
    linarith
  have hd_pos : 0 < d := by linarith
  set scale : ℝ := d⁻¹ with hscale_def
  have hscale_pos : 0 < scale := by positivity
  have hscale_ne_zero : scale ≠ 0 := hscale_pos.ne'
  have hscale_lower : (1 : ℝ) / 2 ≤ scale := by
    rw [hscale_def]
    have h : d⁻¹ ≥ (2 : ℝ)⁻¹ := by gcongr
    norm_num at h ⊢
    exact h
  have hscale_upper : scale ≤ 2 := by
    rw [hscale_def]
    have h : d⁻¹ ≤ ((1 : ℝ) / 2)⁻¹ := by gcongr
    norm_num at h ⊢
    exact h
  have hscale_mul_d : scale * d = 1 := by
    rw [hscale_def]
    field_simp [hd_pos.ne'] <;> ring
  -- Step 3: Normalized delta
  set normalizedDelta : ℝ := scale * delta with hnd_eq
  have hnd_pos : 0 < normalizedDelta := by positivity
  have hnd_upper : normalizedDelta ≤ (1 : ℝ) / 5 := by
    calc
      normalizedDelta = scale * delta := hnd_eq
      _ ≤ 2 * delta := by gcongr <;> linarith
      _ ≤ 2 * ((1 : ℝ) / 10) := by gcongr
      _ = (1 : ℝ) / 5 := by norm_num
  -- Step 4: Homothety
  let m : Point2 := (2 : ℝ)⁻¹ • (center₁ + center₂)
  let f : Point2 → Point2 := wz1OSWPairNormalize center₁ center₂
  have hf_eq : ∀ (x : Point2), f x = scale • (x - m) := by
    intro x; rfl
  have hf_dist : ∀ (x y : Point2), dist (f x) (f y) = scale * dist x y := by
    intro x y
    have h1 : f x - f y = scale • (x - y) := by
      rw [hf_eq x, hf_eq y]
      simp [smul_sub] <;> abel
    have h2 : dist (f x) (f y) = ‖f x - f y‖ := by rw [dist_eq_norm]
    rw [h2, h1, norm_smul]
    have h3 : ‖scale‖ = scale := abs_of_pos hscale_pos
    have h4 : ‖scale‖ * ‖x - y‖ = scale * dist x y := by
      rw [h3, dist_eq_norm] <;> ring
    exact h4
  have hf_inj : Function.Injective f := by
    intro x y h
    have h' : scale • (x - m) = scale • (y - m) := by
      simpa [hf_eq] using h
    have h_inj : Function.Injective (fun z : Point2 => scale • z) :=
      smul_right_injective _ hscale_ne_zero
    have h'' : x - m = y - m := h_inj h'
    simpa using h''
  have hf_norm : ∀ (x : Point2), ‖f x‖ = scale * ‖x - m‖ := by
    intro x
    rw [hf_eq x, norm_smul]
    have h3 : ‖scale‖ = scale := abs_of_pos hscale_pos
    have h4 : ‖scale‖ * ‖x - m‖ = scale * ‖x - m‖ := by rw [h3] <;> ring
    exact h4
  -- Step 5: Normalized sets
  set normalized₁ : DiscreteSet 2 := G₁.image f with hn1_eq
  set normalized₂ : DiscreteSet 2 := G₂.image f with hn2_eq
  have hn1_nonempty : normalized₁.Nonempty := hG1ne.image f
  have hn2_nonempty : normalized₂.Nonempty := hG2ne.image f
  -- Step 6: Separation
  have hn1_sep : normalized₁.IsDeltaSeparated normalizedDelta := by
    intro x' hx' y' hy' hne'
    rcases Finset.mem_image.mp hx' with ⟨x, hx, hx_eq⟩
    rcases Finset.mem_image.mp hy' with ⟨y, hy, hy_eq⟩
    have h_x_ne_y : x ≠ y := by
      intro h
      have h_contra : f x = y' := by
        calc f x = f y := by rw [h]
          _ = y' := hy_eq
      have h_contra2 : x' = y' := by
        calc x' = f x := hx_eq.symm
          _ = y' := h_contra
      exact hne' h_contra2
    have h : delta ≤ dist x y := hG1_sep hx hy h_x_ne_y
    calc
      normalizedDelta = scale * delta := hnd_eq
      _ ≤ scale * dist x y := by gcongr
      _ = dist (f x) (f y) := (hf_dist x y).symm
      _ = dist x' y' := by rw [hx_eq, hy_eq]
  have hn2_sep : normalized₂.IsDeltaSeparated normalizedDelta := by
    intro x' hx' y' hy' hne'
    rcases Finset.mem_image.mp hx' with ⟨x, hx, hx_eq⟩
    rcases Finset.mem_image.mp hy' with ⟨y, hy, hy_eq⟩
    have h_x_ne_y : x ≠ y := by
      intro h
      have h_contra : f x = y' := by
        calc f x = f y := by rw [h]
          _ = y' := hy_eq
      have h_contra2 : x' = y' := by
        calc x' = f x := hx_eq.symm
          _ = y' := h_contra
      exact hne' h_contra2
    have h : delta ≤ dist x y := hG2_sep hx hy h_x_ne_y
    calc
      normalizedDelta = scale * delta := hnd_eq
      _ ≤ scale * dist x y := by gcongr
      _ = dist (f x) (f y) := (hf_dist x y).symm
      _ = dist x' y' := by rw [hx_eq, hy_eq]
  -- Step 7: Ball containment
  have h_center1_m : ‖center₁ - m‖ = d / 2 := by
    have h1 : center₁ - m = (2 : ℝ)⁻¹ • (center₁ - center₂) := by
      ext i
      simp [m, two_smul] <;> ring
    rw [h1, norm_smul]
    have h2 : ‖(2 : ℝ)⁻¹‖ = (2 : ℝ)⁻¹ := by norm_num
    rw [h2]
    have h4 : ‖center₁ - center₂‖ = dist center₁ center₂ := by rw [dist_eq_norm]
    rw [h4, hd_def] <;> ring
  have hn1_ball : (normalized₁ : Set Point2) ⊆ Metric.closedBall 0 (7 / 10 : ℝ) := by
    intro x' hx'
    rcases Finset.mem_image.mp hx' with ⟨x, hx, rfl⟩
    have h1 : ‖x - center₁‖ ≤ (1 : ℝ) / 10 := hG1_diam x hx center₁ hcenter1_mem
    have h2 : ‖x - m‖ ≤ ‖x - center₁‖ + ‖center₁ - m‖ := by
      calc ‖x - m‖ = ‖(x - center₁) + (center₁ - m)‖ := by congr 1 <;> abel
        _ ≤ ‖x - center₁‖ + ‖center₁ - m‖ := norm_add_le _ _
    have h3 : ‖f x‖ = scale * ‖x - m‖ := hf_norm x
    rw [Metric.mem_closedBall, dist_zero_right]
    rw [h3]
    calc
      scale * ‖x - m‖
        ≤ scale * (‖x - center₁‖ + ‖center₁ - m‖) := by gcongr
      _ = scale * ‖x - center₁‖ + scale * ‖center₁ - m‖ := by ring
      _ ≤ scale * ((1 : ℝ) / 10) + scale * (d / 2) := by gcongr <;> linarith
      _ = scale / 10 + 1 / 2 := by
        have h : scale * (d / 2) = 1 / 2 := by
          calc scale * (d / 2) = (scale * d) / 2 := by ring
            _ = 1 / 2 := by rw [hscale_mul_d] <;> ring
        rw [h] <;> ring
      _ ≤ (1 : ℝ) / 5 + 1 / 2 := by linarith
      _ = (7 : ℝ) / 10 := by norm_num
  have h_center2_m : ‖center₂ - m‖ = d / 2 := by
    have h1 : (2 : ℝ) • m = center₁ + center₂ := by
      rw [show m = (2 : ℝ)⁻¹ • (center₁ + center₂) from rfl]
      have h2 : (2 : ℝ) • ((2 : ℝ)⁻¹ • (center₁ + center₂)) = ((2 : ℝ) * (2 : ℝ)⁻¹) • (center₁ + center₂) := by
        rw [smul_smul]
      rw [h2]
      have h3 : (2 : ℝ) * (2 : ℝ)⁻¹ = (1 : ℝ) := by norm_num
      rw [h3, one_smul]
    have h_m2 : m + m = (2 : ℝ) • m := by simp [two_smul]
    have h_sum : center₂ - m + (center₁ - m) = (center₂ + center₁) - (m + m) := by
      have h : ∀ (a b c : Point2), a - c + (b - c) = (a + b) - (c + c) := by
        intro a b c; abel
      exact h center₂ center₁ m
    have h_main : center₂ - m + (center₁ - m) = 0 := by
      rw [h_sum, h_m2, h1]
      <;> simp [add_comm]
      <;> abel
    have h_symm : center₂ - m = -(center₁ - m) :=
      eq_neg_of_add_eq_zero_left h_main
    rw [h_symm, norm_neg, h_center1_m]
  have hn2_ball : (normalized₂ : Set Point2) ⊆ Metric.closedBall 0 (7 / 10 : ℝ) := by
    intro y' hy'
    rcases Finset.mem_image.mp hy' with ⟨y, hy, rfl⟩
    have h1 : ‖y - center₂‖ ≤ (1 : ℝ) / 10 := hG2_diam y hy center₂ hcenter2_mem
    have h2 : ‖y - m‖ ≤ ‖y - center₂‖ + ‖center₂ - m‖ := by
      calc ‖y - m‖ = ‖(y - center₂) + (center₂ - m)‖ := by congr 1 <;> abel
        _ ≤ ‖y - center₂‖ + ‖center₂ - m‖ := norm_add_le _ _
    have h3 : ‖f y‖ = scale * ‖y - m‖ := hf_norm y
    rw [Metric.mem_closedBall, dist_zero_right]
    rw [h3]
    calc
      scale * ‖y - m‖
        ≤ scale * (‖y - center₂‖ + ‖center₂ - m‖) := by gcongr
      _ = scale * ‖y - center₂‖ + scale * ‖center₂ - m‖ := by ring
      _ ≤ scale * ((1 : ℝ) / 10) + scale * (d / 2) := by gcongr <;> linarith
      _ = scale / 10 + 1 / 2 := by
        have h : scale * (d / 2) = 1 / 2 := by
          calc scale * (d / 2) = (scale * d) / 2 := by ring
            _ = 1 / 2 := by rw [hscale_mul_d] <;> ring
        rw [h] <;> ring
      _ ≤ (1 : ℝ) / 5 + 1 / 2 := by linarith
      _ = (7 : ℝ) / 10 := by norm_num
  -- Step 8: Mutual distance
  have h_mutual' : ∀ x' ∈ normalized₁, ∀ y' ∈ normalized₂, (1 : ℝ) ≤ dist x' y' := by
    intro x' hx' y' hy'
    rcases Finset.mem_image.mp hx' with ⟨x, hx, rfl⟩
    rcases Finset.mem_image.mp hy' with ⟨y, hy, rfl⟩
    have h4 : d ≤ dist x y := h_closest x hx y hy
    calc
      (1 : ℝ)
        = scale * d := hscale_mul_d.symm
      _ ≤ scale * dist x y := by gcongr
      _ = dist (f x) (f y) := (hf_dist x y).symm
  -- Step 9: Smoothing
  set ρ : ℝ := normalizedDelta / 10 with hρ_def
  have hρ_pos : 0 < ρ := by positivity
  have hρ_upper : ρ ≤ (1 : ℝ) / 50 := by
    calc
      ρ = normalizedDelta / 10 := hρ_def
      _ ≤ ((1 : ℝ) / 5) / 10 := by gcongr
      _ = (1 : ℝ) / 50 := by norm_num
  let μ₁ : Measure Point2 := smoothMeasure normalized₁ hn1_nonempty ρ hρ_pos
  let μ₂ : Measure Point2 := smoothMeasure normalized₂ hn2_nonempty ρ hρ_pos
  have h_supp1_subset : μ₁.support ⊆ ⋃ a ∈ normalized₁, Metric.closedBall a ρ :=
    smoothMeasure_support_subset (A := normalized₁) (hne := hn1_nonempty) (ρ := ρ) (hρ := hρ_pos)
  have h_supp2_subset : μ₂.support ⊆ ⋃ a ∈ normalized₂, Metric.closedBall a ρ :=
    smoothMeasure_support_subset (A := normalized₂) (hne := hn2_nonempty) (ρ := ρ) (hρ := hρ_pos)
  -- Smooth support in unit ball
  have h_smooth1_support : μ₁.support ⊆ Metric.closedBall 0 1 := by
    intro u hu
    have h4 : u ∈ ⋃ a ∈ normalized₁, Metric.closedBall a ρ := h_supp1_subset hu
    rcases Set.mem_iUnion₂.mp h4 with ⟨a, ha, h5⟩
    have h6 : dist u a ≤ ρ := by simpa [Metric.mem_closedBall] using h5
    have h7 : a ∈ (normalized₁ : Set Point2) := ha
    have h8 : a ∈ Metric.closedBall 0 (7 / 10 : ℝ) := hn1_ball h7
    have h9 : ‖a‖ ≤ (7 : ℝ) / 10 := by simpa [Metric.mem_closedBall, dist_zero_right] using h8
    rw [Metric.mem_closedBall, dist_zero_right]
    have h10 : ‖u‖ ≤ ‖a‖ + ‖u - a‖ := by
      calc ‖u‖ = ‖a + (u - a)‖ := by congr 1 <;> abel
        _ ≤ ‖a‖ + ‖u - a‖ := norm_add_le _ _
    have h11 : ‖u - a‖ = dist u a := by rw [dist_eq_norm]
    rw [h11] at h10
    linarith
  have h_smooth2_support : μ₂.support ⊆ Metric.closedBall 0 1 := by
    intro u hu
    have h4 : u ∈ ⋃ a ∈ normalized₂, Metric.closedBall a ρ := h_supp2_subset hu
    rcases Set.mem_iUnion₂.mp h4 with ⟨a, ha, h5⟩
    have h6 : dist u a ≤ ρ := by simpa [Metric.mem_closedBall] using h5
    have h7 : a ∈ (normalized₂ : Set Point2) := ha
    have h8 : a ∈ Metric.closedBall 0 (7 / 10 : ℝ) := hn2_ball h7
    have h9 : ‖a‖ ≤ (7 : ℝ) / 10 := by simpa [Metric.mem_closedBall, dist_zero_right] using h8
    rw [Metric.mem_closedBall, dist_zero_right]
    have h10 : ‖u‖ ≤ ‖a‖ + ‖u - a‖ := by
      calc ‖u‖ = ‖a + (u - a)‖ := by congr 1 <;> abel
        _ ≤ ‖a‖ + ‖u - a‖ := norm_add_le _ _
    have h11 : ‖u - a‖ = dist u a := by rw [dist_eq_norm]
    rw [h11] at h10
    linarith
  -- Smooth mutual distance
  let S : Set ℝ := {d | ∃ x ∈ μ₁.support, ∃ y ∈ μ₂.support, dist x y = d}
  have hμ1_ne_zero : μ₁ ≠ 0 := by
    have h : μ₁ Set.univ = 1 := by simp [μ₁]
    intro h0
    rw [h0] at h
    <;> simp at h
  have hμ2_ne_zero : μ₂ ≠ 0 := by
    have h : μ₂ Set.univ = 1 := by simp [μ₂]
    intro h0
    rw [h0] at h
    <;> simp at h
  have hS1_nonempty : μ₁.support.Nonempty := Measure.nonempty_support hμ1_ne_zero
  have hS2_nonempty : μ₂.support.Nonempty := Measure.nonempty_support hμ2_ne_zero
  have hS_nonempty : S.Nonempty := by
    rcases hS1_nonempty with ⟨x, hx⟩
    rcases hS2_nonempty with ⟨y, hy⟩
    refine ⟨dist x y, ?_⟩
    exact ⟨x, hx, y, hy, rfl⟩
  have hS_lower : ∀ d ∈ S, (1 : ℝ) / 2 ≤ d := by
    intro d hd
    rcases hd with ⟨u, hu, v, hv, rfl⟩
    have h4 : u ∈ ⋃ a ∈ normalized₁, Metric.closedBall a ρ := h_supp1_subset hu
    have h5 : v ∈ ⋃ b ∈ normalized₂, Metric.closedBall b ρ := h_supp2_subset hv
    rcases Set.mem_iUnion₂.mp h4 with ⟨a, ha, h6⟩
    rcases Set.mem_iUnion₂.mp h5 with ⟨b, hb, h7⟩
    have h8 : dist u a ≤ ρ := by simpa [Metric.mem_closedBall] using h6
    have h8' : dist a u ≤ ρ := by rwa [dist_comm] at h8
    have h9 : dist v b ≤ ρ := by simpa [Metric.mem_closedBall] using h7
    have h10 : (1 : ℝ) ≤ dist a b := h_mutual' a ha b hb
    have h11 : dist a b ≤ dist a u + dist u v + dist v b := by
      calc
        dist a b ≤ dist a u + dist u b := dist_triangle a u b
        _ ≤ dist a u + (dist u v + dist v b) := by gcongr <;> exact dist_triangle u v b
        _ = dist a u + dist u v + dist v b := by ring
    have h14 : dist a u + dist u v + dist v b ≤ 2 * ρ + dist u v := by
      have h15 : dist a u ≤ ρ := h8'
      have h16 : dist v b ≤ ρ := h9
      linarith
    have h17 : 1 ≤ 2 * ρ + dist u v := by
      calc 1 ≤ dist a b := h10
        _ ≤ dist a u + dist u v + dist v b := h11
        _ ≤ 2 * ρ + dist u v := h14
    have h12 : dist u v ≥ 1 - 2 * ρ := by linarith
    have h13 : 1 - 2 * ρ ≥ (1 : ℝ) / 2 := by
      linarith [hρ_upper]
    linarith
  have h_main : (1 : ℝ) / 2 ≤ sInf S := le_csInf hS_nonempty hS_lower
  -- Assemble the record
  dsimp only [S, μ₁, μ₂, ρ] at h_main h_smooth1_support h_smooth2_support
  refine' ⟨center₁, center₂, hcenter1_mem, hcenter2_mem, h_closest,
    scale, hscale_def, hscale_lower, hscale_upper,
    normalizedDelta, hnd_eq, hnd_pos, hnd_upper,
    normalized₁, normalized₂, hn1_eq, hn2_eq,
    hn1_nonempty, hn2_nonempty, hn1_sep, hn2_sep,
    hn1_ball, hn2_ball, h_mutual',
    h_smooth1_support, h_smooth2_support, h_main⟩

end Kakeya.Assouad
