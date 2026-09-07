module

/-
  Merging helper lemmas for the Combinatorial Kaufman Decomposition.

  These lemmas adapt the helper results from MultiscaleDecomposition.lean
  to use the target definitions `chordSlope`, `chordValue`, `EpsilonLinear`,
  and `EpsilonSuperlinear`.

  Main results:
  - `chordSlope_convex`: weighted average formula for chord slopes
  - `largest_chordSlope_eq`: existence of largest point with given slope via IVT
  - `merged_epsilonSuperlinear`: merge superlinear prefix with linear suffix
  - `truncated_epsilonLinear`: truncate an ε-linear interval
  - `chordSlope0_gt_s_of_middle`: slope inference from convex combination
  - `merge_adjacent_epsilonSuperlinear`: merge two adjacent superlinear intervals
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombinatorialKaufman.Definitions
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

namespace CombinatorialKaufman.MergingLemmas

variable {f : ℝ → ℝ}

-- =====================================================================
-- Basic properties of chordValue and EpsilonLinear/EpsilonSuperlinear
-- =====================================================================

/-- `chordValue` agrees with `f` at the endpoints. -/
lemma chordValue_endpoints (f : ℝ → ℝ) {a b : ℝ} (h : a < b) :
    chordValue f a b a = f a ∧ chordValue f a b b = f b := by
  constructor
  · simp [chordValue, chordSlope] <;> ring
  · simp [chordValue, chordSlope]
    <;> field_simp [show (b - a : ℝ) ≠ 0 by linarith] <;> ring

/-- `EpsilonLinear` implies `EpsilonSuperlinear`. -/
lemma EpsilonLinear.toSuperlinear {f : ℝ → ℝ} {ε a b : ℝ}
    (h : EpsilonLinear f ε a b) :
    EpsilonSuperlinear f ε a b := by
  intro x hx
  have h3 : |f x - chordValue f a b x| ≤ ε * (b - a) := h x hx
  have h4 : -(ε * (b - a)) ≤ f x - chordValue f a b x := by
    linarith [abs_le.mp h3]
  linarith

/-- An ε-superlinear function with non-negative slope has a lower bound. -/
lemma EpsilonSuperlinear.lower_bound {f : ℝ → ℝ} {ε a b : ℝ}
    (h : EpsilonSuperlinear f ε a b) (hslope : 0 ≤ chordSlope f a b)
    (hab : a < b) :
    ∀ x ∈ Set.Icc a b, f x ≥ f a - ε * (b - a) := by
  intro x hx
  have h1 : chordValue f a b x - ε * (b - a) ≤ f x := h x hx
  have h2 : chordValue f a b x ≥ f a := by
    have h3 : x - a ≥ 0 := by exact sub_nonneg.mpr hx.1
    have h4 : chordSlope f a b * (x - a) ≥ 0 := by positivity
    simpa [chordValue] using h4
  linarith

-- =====================================================================
-- Slope convexity
-- =====================================================================

/-- Chord slope convexity: for a < x < b, `chordSlope f a b` is a weighted
    average of `chordSlope f a x` and `chordSlope f x b`. -/
lemma chordSlope_convex (f : ℝ → ℝ) {a x b : ℝ} (hax : a < x) (hxb : x < b) :
    chordSlope f a b =
      ((x - a) / (b - a)) * chordSlope f a x +
      ((b - x) / (b - a)) * chordSlope f x b := by
  have h1 : b - a ≠ 0 := by linarith
  have h2 : x - a ≠ 0 := by linarith
  have h3 : b - x ≠ 0 := by linarith
  dsimp only [chordSlope]
  field_simp [h1, h2, h3] <;> ring

-- =====================================================================
-- Continuity of slope and largest_slope_eq
-- =====================================================================

/-- `chordSlope f x b` is continuous on (-∞, b) when `f` is continuous. -/
lemma chordSlope_right_continuous (f : ℝ → ℝ) (hf : Continuous f) (b : ℝ) :
    ContinuousOn (fun x : ℝ ↦ chordSlope f x b) (Set.Iio b) := by
  have h1 : Continuous (fun x : ℝ ↦ f b - f x) := by fun_prop
  have h2 : Continuous (fun x : ℝ ↦ b - x) := by fun_prop
  have h3 : ∀ (x : ℝ), x ∈ Set.Iio b → b - x ≠ 0 := by
    intro x hx; simp only [Set.mem_Iio] at hx; linarith
  exact h1.continuousOn.div h2.continuousOn h3

/-- Given a < c < b, `chordSlope f a b > s`, `chordSlope f c b < s`,
    `f` continuous, there exists a largest x₀ ∈ [a,c] with
    `chordSlope f x0 b = s`, and `chordSlope f y b ≤ s` for all y ∈ (x₀, c]. -/
lemma largest_chordSlope_eq (f : ℝ → ℝ) (hf : Continuous f) {a c b s : ℝ}
    (hac : a < c) (hcb : c < b)
    (h1 : chordSlope f a b > s) (h2 : chordSlope f c b < s) :
    ∃ (x0 : ℝ), a ≤ x0 ∧ x0 ≤ c ∧ chordSlope f x0 b = s ∧
      ∀ y ∈ Set.Ioc x0 c, chordSlope f y b ≤ s := by
  let g : ℝ → ℝ := fun x ↦ chordSlope f x b
  have hg_cont : ContinuousOn g (Set.Icc a c) := by
    apply ContinuousOn.mono (s := Set.Iio b)
    · exact chordSlope_right_continuous f hf b
    · intro x hx; simp only [Set.mem_Icc, Set.mem_Iio] at *; linarith
  have h_s_in_image : s ∈ g '' Set.Icc a c := by
    have h_ivt : Set.Icc (g c) (g a) ⊆ g '' Set.Icc a c :=
      intermediate_value_Icc' hac.le hg_cont
    have h_s_in : s ∈ Set.Icc (g c) (g a) := by
      exact ⟨le_of_lt h2, le_of_lt h1⟩
    exact h_ivt h_s_in
  rcases h_s_in_image with ⟨xmid, hxmid, hxmid_eq⟩
  let S : Set ℝ := Set.Icc a c ∩ g ⁻¹' {s}
  have hS_nonempty : S.Nonempty := ⟨xmid, hxmid, hxmid_eq⟩
  have hS_closed : IsClosed S :=
    hg_cont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hS_bdd : BddAbove S := ⟨c, fun x hx ↦ hx.1.2⟩
  let x0 := sSup S
  have hx0_in_S : x0 ∈ S := hS_closed.csSup_mem hS_nonempty hS_bdd
  have hx0_Icc : x0 ∈ Set.Icc a c := hx0_in_S.1
  have h_slope : g x0 = s := hx0_in_S.2
  have h_main : ∀ y ∈ Set.Ioc x0 c, g y ≤ s := by
    intro y hy
    by_contra h
    push Not at h
    have h_gt : g y > s := h
    have h_y_lt_c : y < c := by
      have h_y_le_c : y ≤ c := hy.2
      by_contra h_eq
      have : y = c := by linarith
      rw [this] at h_gt
      exact False.elim (not_lt.mpr (le_of_lt h2) h_gt)
    have h_cont2 : ContinuousOn g (Set.Icc y c) := by
      apply ContinuousOn.mono (s := Set.Iio b)
      · exact chordSlope_right_continuous f hf b
      · intro z hz; simp only [Set.mem_Icc, Set.mem_Iio] at *; linarith
    have h_s_in_image2 : s ∈ g '' Set.Icc y c := by
      have h_ivt : Set.Icc (g c) (g y) ⊆ g '' Set.Icc y c :=
        intermediate_value_Icc' (by linarith) h_cont2
      have h_s_in : s ∈ Set.Icc (g c) (g y) := by
        exact ⟨le_of_lt h2, le_of_lt h_gt⟩
      exact h_ivt h_s_in
    rcases h_s_in_image2 with ⟨z, hz, hz_eq⟩
    have hz_in_Icc_yc : z ∈ Set.Icc y c := hz
    have hz_ge_y : y ≤ z := hz_in_Icc_yc.1
    have hz_le_c : z ≤ c := hz_in_Icc_yc.2
    have hz_ne_y : z ≠ y := by
      intro eq; rw [eq] at hz_eq; exact False.elim (not_le.mpr h_gt (le_of_eq hz_eq))
    have hz_gt_y : y < z := lt_of_le_of_ne hz_ge_y hz_ne_y.symm
    have hz_ge_x0 : x0 ≤ z := by linarith [hy.1]
    have h_a_le_z : a ≤ z := by linarith [hx0_Icc.1, hz_ge_x0]
    have hz_in_S : z ∈ S := ⟨⟨h_a_le_z, hz_le_c⟩, hz_eq⟩
    have hz_le_x0 : z ≤ x0 := le_csSup hS_bdd hz_in_S
    have hz_eq_x0 : z = x0 := by linarith
    rw [hz_eq_x0] at hz_gt_y
    exact False.elim (not_lt.mpr (le_of_lt hy.1) hz_gt_y)
  exact ⟨x0, hx0_Icc.1, hx0_Icc.2, h_slope, h_main⟩

-- =====================================================================
-- Merged superlinear
-- =====================================================================

/-- If [c_k, d_k] is ε-linear with slope < s, and x0 < c_k with
    `chordSlope f x0 d_k = s` and `chordSlope f y d_k ≤ s` for y ∈ (x0, c_k],
    then [x0, d_k] is ε-superlinear at slope s. -/
lemma merged_epsilonSuperlinear (f : ℝ → ℝ) {x0 c_k d_k s ε : ℝ}
    (hε : 0 ≤ ε)
    (h_x0_lt_c : x0 < c_k) (h_c_lt_d : c_k < d_k)
    (h_slope : chordSlope f x0 d_k = s)
    (h_slope_c : chordSlope f c_k d_k < s)
    (h_eps_lin : EpsilonLinear f ε c_k d_k)
    (h_mon : ∀ y ∈ Set.Ioc x0 c_k, chordSlope f y d_k ≤ s) :
    EpsilonSuperlinear f ε x0 d_k := by
  have h_x0_lt_d : x0 < d_k := by linarith
  intro x hx
  have h_x_ge_x0 : x0 ≤ x := hx.1
  have h_x_le_d : x ≤ d_k := hx.2
  by_cases h_case : x ≤ c_k
  · -- Case 1: x ∈ [x0, c_k]
    by_cases h_eq : x = x0
    · rw [h_eq]
      have h_lin : chordValue f x0 d_k x0 = f x0 := by simp [chordValue]
      rw [h_lin]
      have h : 0 ≤ ε * (d_k - x0) := by positivity
      linarith
    · have h_x_gt_x0 : x0 < x := by exact lt_of_le_of_ne hx.1 (Ne.symm h_eq)
      have h_slope_x : chordSlope f x d_k ≤ s := h_mon x ⟨h_x_gt_x0, h_case⟩
      have hden : 0 < d_k - x0 := by linarith
      have hpos1 : 0 < x - x0 := by linarith
      set w1 := (x - x0) / (d_k - x0) with hw1_def
      set w2 := (d_k - x) / (d_k - x0) with hw2_def
      have hw1_pos : 0 < w1 := by positivity
      have hw2_nonneg : 0 ≤ w2 := by positivity
      have hwsum : w1 + w2 = 1 := by
        simp [hw1_def, hw2_def] <;> field_simp [hden.ne'] <;> ring
      have h_x_lt_d : x < d_k := by
        by_contra h'; have : x = d_k := by linarith
        rw [this] at h_x_gt_x0; linarith
      have h_conv : chordSlope f x0 d_k = w1 * chordSlope f x0 x + w2 * chordSlope f x d_k :=
        chordSlope_convex f h_x_gt_x0 h_x_lt_d
      have h_eq1 : s = w1 * chordSlope f x0 x + w2 * chordSlope f x d_k := by
        rw [h_slope] at h_conv; exact h_conv
      have h_slope_x0x : chordSlope f x0 x ≥ s := by
        have h_ineq1 : w1 * chordSlope f x0 x + w2 * chordSlope f x d_k ≤ w1 * chordSlope f x0 x + w2 * s := by gcongr
        have h_ineq2 : s ≤ w1 * chordSlope f x0 x + w2 * s := by
          have h_eq2 : w1 * chordSlope f x0 x + w2 * chordSlope f x d_k = s := h_eq1.symm
          linarith
        have h_ineq3 : s - w2 * s ≤ w1 * chordSlope f x0 x := by linarith
        have h_ineq4 : (1 - w2) * s ≤ w1 * chordSlope f x0 x := by
          have h : (1 - w2) * s = s - w2 * s := by ring
          rw [h]; exact h_ineq3
        have h_ineq5 : w1 * s ≤ w1 * chordSlope f x0 x := by
          have h6 : 1 - w2 = w1 := by linarith [hwsum]
          rw [h6] at h_ineq4; exact h_ineq4
        have h7 : 0 < w1 := hw1_pos
        have h9 : s ≤ chordSlope f x0 x := by
          calc s = (w1 * s) / w1 := by field_simp [h7.ne'] <;> ring
               _ ≤ (w1 * chordSlope f x0 x) / w1 := by gcongr
               _ = chordSlope f x0 x := by field_simp [h7.ne'] <;> ring
        exact h9
      have h_f_ge : f x ≥ f x0 + s * (x - x0) := by
        dsimp only [chordSlope] at h_slope_x0x
        have h : (f x - f x0) / (x - x0) ≥ s := h_slope_x0x
        have h2 : f x - f x0 ≥ s * (x - x0) := by
          calc (f x - f x0)
            = ((f x - f x0) / (x - x0)) * (x - x0) := by field_simp [hpos1.ne'] <;> ring
          _ ≥ s * (x - x0) := by gcongr
        linarith
      have h_lin : chordValue f x0 d_k x = f x0 + chordSlope f x0 d_k * (x - x0) := by
        simp [chordValue]
      rw [h_lin, h_slope]
      have h_abs_nonneg : 0 ≤ ε * (d_k - x0) := by positivity
      linarith
  · -- Case 2: x ∈ (c_k, d_k]
    have h_x_gt_c : c_k < x := by linarith
    have h_eps_super : EpsilonSuperlinear f ε c_k d_k := EpsilonLinear.toSuperlinear h_eps_lin
    have h_alt_form : f x ≥ f d_k - chordSlope f c_k d_k * (d_k - x) - ε * (d_k - c_k) := by
      have h_super := h_eps_super x ⟨by linarith, h_x_le_d⟩
      have h_eq : f c_k + chordSlope f c_k d_k * (x - c_k) =
               f d_k - chordSlope f c_k d_k * (d_k - x) := by
        dsimp only [chordSlope]
        field_simp [show (d_k - c_k : ℝ) ≠ 0 by linarith] <;> ring
      have h_lin : chordValue f c_k d_k x = f c_k + chordSlope f c_k d_k * (x - c_k) := by
        simp [chordValue]
      rw [h_lin] at h_super
      rw [h_eq] at h_super
      exact h_super
    have h10 : f d_k = f x0 + s * (d_k - x0) := by
      dsimp only [chordSlope] at h_slope
      have hden : d_k - x0 ≠ 0 := by linarith
      field_simp [hden] at h_slope ⊢ <;> linarith
    have h_dk_x_nonneg : 0 ≤ d_k - x := by linarith
    have h14 : ε * (d_k - c_k) ≤ ε * (d_k - x0) := by
      have h15 : d_k - c_k ≤ d_k - x0 := by linarith
      gcongr
    have h_main : f x ≥ f x0 + s * (x - x0) - ε * (d_k - x0) := by
      calc f x
        ≥ f d_k - chordSlope f c_k d_k * (d_k - x) - ε * (d_k - c_k) := h_alt_form
      _ ≥ f d_k - s * (d_k - x) - ε * (d_k - c_k) := by
        have h16 : chordSlope f c_k d_k < s := h_slope_c
        have h17 : 0 ≤ d_k - x := h_dk_x_nonneg
        have h18 : (s - chordSlope f c_k d_k) * (d_k - x) ≥ 0 := by
          have h19 : 0 < s - chordSlope f c_k d_k := by linarith
          exact mul_nonneg (by linarith) h17
        have h20 : -chordSlope f c_k d_k * (d_k - x) ≥ -s * (d_k - x) := by
          have h21 : -chordSlope f c_k d_k * (d_k - x) - (-s * (d_k - x)) = (s - chordSlope f c_k d_k) * (d_k - x) := by ring
          linarith
        linarith
      _ = f x0 + s * (d_k - x0) - s * (d_k - x) - ε * (d_k - c_k) := by rw [h10]
      _ = f x0 + s * (x - x0) - ε * (d_k - c_k) := by ring
      _ ≥ f x0 + s * (x - x0) - ε * (d_k - x0) := by linarith [h14]
    have h_lin : chordValue f x0 d_k x = f x0 + chordSlope f x0 d_k * (x - x0) := by
      simp [chordValue]
    rw [h_lin, h_slope]
    exact h_main

-- =====================================================================
-- Truncated linear
-- =====================================================================

/-- If [a,b] is δ-linear and a < c < b with c-a > η·(b-a),
    then [a,c] is (2δ/η)-linear. -/
lemma truncated_epsilonLinear (f : ℝ → ℝ) {a b c δ η : ℝ}
    (hδ : 0 ≤ δ) (hη : 0 < η)
    (hac : a < c) (hcb : c < b)
    (h_lin : EpsilonLinear f δ a b)
    (h_frac : c - a > η * (b - a)) :
    EpsilonLinear f (2 * δ / η) a c := by
  have h_err_c : |f c - chordValue f a b c| ≤ δ * (b - a) :=
    h_lin c ⟨by linarith, by linarith⟩
  have h_slope_diff : |chordSlope f a c - chordSlope f a b| ≤ δ * (b - a) / (c - a) := by
    have h_lin_c : chordValue f a b c = f a + chordSlope f a b * (c - a) := by
      simp [chordValue]
    have h_eq : (f c - chordValue f a b c) / (c - a) = chordSlope f a c - chordSlope f a b := by
      rw [h_lin_c]
      dsimp only [chordSlope]
      field_simp [show c - a ≠ 0 by linarith] <;> ring
    have hpos : 0 < c - a := by linarith
    have hba : 0 < b - a := by linarith
    have h_nonneg : 0 ≤ δ * (b - a) / (c - a) := by
      apply div_nonneg
      · exact mul_nonneg hδ (by linarith)
      · exact by linarith
    have h : |(f c - chordValue f a b c) / (c - a)| ≤ δ * (b - a) / (c - a) := by
      rw [abs_div, abs_of_pos hpos]
      gcongr <;> linarith
    rw [←h_eq]
    exact h
  have h2 : ∀ x ∈ Set.Icc a c, |f x - chordValue f a c x| ≤ (2 * δ / η) * (c - a) := by
    intro x hx
    have h_x_le_c : x ≤ c := hx.2
    have h_x_le_b : x ≤ b := by linarith
    have h_x_in_ab : x ∈ Set.Icc a b := ⟨hx.1, h_x_le_b⟩
    have h3 : |f x - chordValue f a b x| ≤ δ * (b - a) := h_lin x h_x_in_ab
    have h4 : |chordValue f a b x - chordValue f a c x| ≤ δ * (b - a) := by
      have h_eq2 : chordValue f a c x - chordValue f a b x =
                   (chordSlope f a c - chordSlope f a b) * (x - a) := by
        simp [chordValue] <;> ring
      have h_abs : |chordValue f a b x - chordValue f a c x| =
                     |(chordSlope f a c - chordSlope f a b) * (x - a)| := by
        rw [show chordValue f a b x - chordValue f a c x =
                       -(chordValue f a c x - chordValue f a b x) by ring]
        rw [abs_neg, h_eq2]
      rw [h_abs]
      have hba : 0 < b - a := by linarith
      have hca : 0 < c - a := by linarith
      have h5 : |(chordSlope f a c - chordSlope f a b) * (x - a)| ≤ δ * (b - a) := by
        calc |(chordSlope f a c - chordSlope f a b) * (x - a)|
          = |chordSlope f a c - chordSlope f a b| * |x - a| := by rw [abs_mul]
        _ ≤ (δ * (b - a) / (c - a)) * |x - a| := by gcongr
        _ ≤ (δ * (b - a) / (c - a)) * (c - a) := by
          have h_nonneg2 : 0 ≤ δ * (b - a) / (c - a) := by
            apply div_nonneg
            · exact mul_nonneg hδ (by linarith)
            · exact by linarith
          have h_xa_nonneg : 0 ≤ x - a := by linarith [hx.1]
          have h_xa_le : x - a ≤ c - a := by linarith [hx.2]
          have h_abs_le : |x - a| ≤ c - a := by
            rw [abs_of_nonneg h_xa_nonneg]
            exact h_xa_le
          nlinarith
        _ = δ * (b - a) := by
          field_simp [show c - a ≠ 0 by linarith] <;> ring
      exact h5
    have h_triangle : |f x - chordValue f a c x| ≤
        |f x - chordValue f a b x| + |chordValue f a b x - chordValue f a c x| := by
      calc |f x - chordValue f a c x|
        = |(f x - chordValue f a b x) + (chordValue f a b x - chordValue f a c x)| := by ring_nf
      _ ≤ |f x - chordValue f a b x| + |chordValue f a b x - chordValue f a c x| := by
        exact abs_add_le _ _
    calc |f x - chordValue f a c x|
      ≤ |f x - chordValue f a b x| + |chordValue f a b x - chordValue f a c x| := h_triangle
    _ ≤ δ * (b - a) + δ * (b - a) := by gcongr
    _ = 2 * δ * (b - a) := by ring
    _ ≤ (2 * δ / η) * (c - a) := by
      have h9 : 0 < c - a := by linarith
      have h10 : b - a < (c - a) / η := by
        have h11 : η * (b - a) < c - a := h_frac
        have h12 : 0 < η := hη
        calc b - a
          = (η * (b - a)) / η := by field_simp [h12.ne'] <;> ring
        _ < (c - a) / η := by gcongr
      have h13 : 2 * δ * (b - a) ≤ (2 * δ / η) * (c - a) := by
        have h14 : (2 * δ / η) * (c - a) = 2 * δ * ((c - a) / η) := by ring
        rw [h14]
        gcongr <;> linarith
      exact h13
  exact h2

-- =====================================================================
-- Slope inference
-- =====================================================================

/-- If `chordSlope f 0 b > s` and `chordSlope f c b = s` with 0 < c < b,
    then `chordSlope f 0 c > s`. -/
lemma chordSlope0_gt_s_of_middle (f : ℝ → ℝ) {s b c : ℝ}
    (hc_pos : 0 < c) (hcb : c < b)
    (h1 : chordSlope f 0 b > s) (h2 : chordSlope f c b = s) :
    chordSlope f 0 c > s := by
  have h_conv : chordSlope f 0 b = (c / b) * chordSlope f 0 c + ((b - c) / b) * chordSlope f c b := by
    have h := chordSlope_convex f hc_pos hcb
    simpa using h
  rw [h_conv, h2] at h1
  have hb_pos : 0 < b := by linarith
  have h' : (c / b) * chordSlope f 0 c > (c / b) * s := by
    have h_eq : (c / b) * s + ((b - c) / b) * s = s := by
      field_simp [hb_pos.ne'] <;> ring
    linarith
  have hcb_pos : 0 < c / b := by positivity
  nlinarith

-- =====================================================================
-- Merge adjacent superlinear intervals
-- =====================================================================

/-- Merge two adjacent ε-superlinear intervals with the same slope s. -/
lemma merge_adjacent_epsilonSuperlinear (f : ℝ → ℝ) {a c b s δ1 δ2 : ℝ}
    (hac : a < c) (hcb : c < b)
    (h1 : EpsilonSuperlinear f δ1 a c) (h2 : EpsilonSuperlinear f δ2 c b)
    (hs1 : chordSlope f a c = s) (hs2 : chordSlope f c b = s)
    (hδ1 : 0 ≤ δ1) (hδ2 : 0 ≤ δ2) :
    EpsilonSuperlinear f (max δ1 δ2) a b ∧ chordSlope f a b = s := by
  have h_slope : chordSlope f a b = s := by
    rw [chordSlope_convex f hac hcb, hs1, hs2]
    have hden : (b - a : ℝ) ≠ 0 := by linarith
    field_simp [hden] <;> ring
  have h_main : EpsilonSuperlinear f (max δ1 δ2) a b := by
    intro x hx
    have h_goal : chordValue f a b x - max δ1 δ2 * (b - a) ≤ f x := by
      by_cases h : x ≤ c
      · have h3 : chordValue f a c x - δ1 * (c - a) ≤ f x := h1 x ⟨hx.1, h⟩
        have h4 : chordValue f a c x = f a + s * (x - a) := by
          simp [chordValue, hs1] <;> ring
        have h5 : δ1 * (c - a) ≤ max δ1 δ2 * (b - a) := by
          have h51 : δ1 ≤ max δ1 δ2 := le_max_left δ1 δ2
          have h52 : c - a ≤ b - a := by linarith
          exact mul_le_mul h51 h52 (by linarith) (by positivity)
        have h_lin_ab : chordValue f a b x = f a + s * (x - a) := by
          simp [chordValue, h_slope] <;> ring
        rw [h4] at h3
        rw [h_lin_ab]
        linarith
      · have h_x_gt_c : c < x := by linarith
        have h3 : chordValue f c b x - δ2 * (b - c) ≤ f x := h2 x ⟨by linarith, hx.2⟩
        have h_fc : f c = f a + s * (c - a) := by
          dsimp only [chordSlope] at hs1
          have hden : c - a ≠ 0 := by linarith
          field_simp [hden] at hs1 ⊢ <;> linarith
        have h4 : chordValue f c b x = f c + s * (x - c) := by
          simp [chordValue, hs2] <;> ring
        have h6 : δ2 * (b - c) ≤ max δ1 δ2 * (b - a) := by
          have h61 : δ2 ≤ max δ1 δ2 := le_max_right δ1 δ2
          have h62 : b - c ≤ b - a := by linarith
          exact mul_le_mul h61 h62 (by linarith) (by positivity)
        have h_lin_ab : chordValue f a b x = f a + s * (x - a) := by
          simp [chordValue, h_slope] <;> ring
        rw [h4, h_fc] at h3
        rw [h_lin_ab]
        linarith
    exact h_goal
  exact ⟨h_main, h_slope⟩

end CombinatorialKaufman.MergingLemmas
