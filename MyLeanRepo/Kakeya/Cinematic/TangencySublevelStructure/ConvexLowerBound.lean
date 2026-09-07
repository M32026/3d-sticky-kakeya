import MyLeanRepo.Kakeya.Cinematic.TangencySublevelStructure.Basic
import MyLeanRepo.Kakeya.Cinematic.Targets.TangencySublevelDiameter.Helpers
import MyLeanRepo.Kakeya.Cinematic.TangencyIntervalExtension.Calculus

/-!
# Convex case lower bound for E_half points

Taylor neighborhood approach:
1. Use convexity quadratic to bound |x-y| where y is tangency point.
2. Solve quadratic → |H'(x)| ≤ (1+6K+6√K)·scale.
3. Taylor remainder → |H(w)| ≤ δ for |w-x| ≤ δ/(C₁·scale).
4. L ≤ I.length/8, so one direction fits in centered quarter.
5. Component property gives length ≥ L.
-/

namespace Kakeya.Cinematic

-- ============================================================================
-- Helper: constant sign from |g| ≥ m > 0
-- ============================================================================

private lemma constant_sign_of_abs_ge' {g : ℝ → ℝ} {a b m : ℝ}
    (hab : a ≤ b) (hm_pos : 0 < m)
    (hcont : ContinuousOn g (Set.Icc a b))
    (hbound : ∀ x ∈ Set.Icc a b, m ≤ |g x|) :
    (∀ x ∈ Set.Icc a b, 0 < g x) ∨ (∀ x ∈ Set.Icc a b, g x < 0) := by
  have hne : ∀ x ∈ Set.Icc a b, g x ≠ 0 := by
    intro x hx
    have h1 : m ≤ |g x| := hbound x hx
    have h2 : 0 < |g x| := by linarith
    exact abs_ne_zero.mp (ne_of_gt h2)
  exact constant_sign_of_never_zero hab hcont hne

-- ============================================================================
-- Helper: convexity quadratic on [a,b]
-- ============================================================================

private lemma distance_quadratic {H : ℝ → ℝ} {x y a b m Delta delta : ℝ}
    (hH1 : Differentiable ℝ H) (hH2 : Differentiable ℝ (deriv H))
    (hm_pos : 0 < m)
    (hab : a ≤ b) (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b)
    (hH''_lower : ∀ r ∈ Set.Icc a b, deriv (deriv H) r ≥ m)
    (hHy : |H y| + |deriv H y| ≤ Delta) (hHx_upper : |H x| ≤ delta / 2) :
    m / 2 * |x - y|^2 - Delta * |x - y| - (Delta + delta / 2) ≤ 0 := by
  set S : ℝ := |x - y| with hS
  have h1 : H x ≥ H y + deriv H y * (x - y) + m / 2 * (x - y)^2 :=
    taylor_quadratic_lower_bound hH1 hH2 hab hy hx hH''_lower
  have h2 : H y ≥ -|H y| := neg_abs_le (H y)
  have h3 : deriv H y * (x - y) ≥ -|deriv H y| * S := by
    have h31 : deriv H y * (x - y) ≥ -|deriv H y * (x - y)| := neg_abs_le _
    have h32 : |deriv H y * (x - y)| = |deriv H y| * |x - y| := by rw [abs_mul]
    have h33 : |x - y| = S := by simp [hS]
    have h34 : deriv H y * (x - y) ≥ -|deriv H y| * S := by
      calc deriv H y * (x - y)
        ≥ -|deriv H y * (x - y)| := h31
      _ = -(|deriv H y| * |x - y|) := by rw [h32]
      _ = -|deriv H y| * S := by rw [h33] <;> ring
    exact h34
  have h4 : H x ≤ delta / 2 := by
    have h5 : H x ≤ |H x| := le_abs_self (H x)
    linarith [hHx_upper]
  have h5 : |H y| ≤ Delta := by
    have h6 : 0 ≤ |deriv H y| := abs_nonneg _
    linarith [hHy]
  have h6 : |deriv H y| ≤ Delta := by
    have h7 : 0 ≤ |H y| := abs_nonneg _
    linarith [hHy]
  have h9 : (x - y)^2 = S^2 := by rw [hS, sq_abs]
  have h1' : H x ≥ H y + deriv H y * (x - y) + m / 2 * S^2 := by
    rw [h9] at h1
    exact h1
  have h10 : m / 2 * S^2 ≤ delta / 2 + |H y| + |deriv H y| * S := by linarith
  have hDelta_nonneg : 0 ≤ Delta := by
    have h : 0 ≤ |H y| + |deriv H y| := by positivity
    linarith [hHy]
  have h11 : |deriv H y| * S ≤ Delta * S := by
    have h12 : 0 ≤ S := abs_nonneg _
    have h13 : 0 ≤ Delta := hDelta_nonneg
    exact mul_le_mul h6 (le_refl S) h12 h13
  nlinarith

-- ============================================================================
-- Helper: Delta ≤ scale
-- ============================================================================

private lemma delta_le_scale {K t Delta delta scale : ℝ}
    (hK : 1 ≤ K) (ht_pos : 0 < t) (hdelta : 0 < delta)
    (hDelta_nonneg : 0 ≤ Delta) (hDelta_lt : Delta < 2 * t / (3 * K))
    (hscale : scale = Real.sqrt ((Delta + delta) * t)) :
    Delta ≤ scale := by
  have hK_pos : 0 < K := by linarith
  have h1 : 2 * t / (3 * K) ≤ t := by
    have h2 : 0 < K := hK_pos
    have h3 : 0 < t := ht_pos
    have h4 : 2 / (3 * K) ≤ 1 := by
      have h5 : 2 ≤ 3 * K := by nlinarith [hK]
      have h6 : 0 < 3 * K := by positivity
      exact (div_le_one h6).mpr h5
    calc 2 * t / (3 * K) = (2 / (3 * K)) * t := by ring
      _ ≤ 1 * t := by gcongr
      _ = t := by ring
  have h1' : Delta < t := by linarith [hDelta_lt, h1]
  have h2 : Delta^2 < (Delta + delta) * t := by
    nlinarith [hdelta, h1', hDelta_nonneg]
  have h3 : 0 < scale := by
    rw [hscale]
    have h4 : 0 < (Delta + delta) * t := by positivity
    exact Real.sqrt_pos.mpr h4
  have h4 : scale^2 = (Delta + delta) * t := by
    rw [hscale]
    have h5 : 0 ≤ (Delta + delta) * t := by positivity
    rw [Real.sq_sqrt h5]
  have h5 : Delta^2 < scale^2 := by
    rw [h4]
    exact h2
  nlinarith [hDelta_nonneg, h3]

-- ============================================================================
-- Helper: t * s ≤ (6K + 6√K) * scale from quadratic inequality
-- ============================================================================

private lemma t_distance_bound {K t Delta delta scale m : ℝ}
    (hK : 1 ≤ K) (ht_pos : 0 < t) (hdelta : 0 < delta)
    (hm_eq : m = t / (6 * K)) (hDelta_nonneg : 0 ≤ Delta)
    (hDelta_lt : Delta < 2 * t / (3 * K))
    (hscale : scale = Real.sqrt ((Delta + delta) * t)) (hscale_pos : 0 < scale)
    (s : ℝ) (hs_nonneg : 0 ≤ s)
    (hquad : m / 2 * s^2 - Delta * s - (Delta + delta / 2) ≤ 0) :
    t * s ≤ (6 * K + 6 * Real.sqrt K) * scale := by
  have hK_pos : 0 < K := by linarith
  have h_pos : 0 < m := by
    rw [hm_eq]
    positivity
  set D : ℝ := Delta^2 + 2 * m * (Delta + delta / 2) with hD_def
  have hD_nonneg : 0 ≤ D := by positivity

  -- Step 1: solve quadratic
  have h10 : s^2 - 2 * Delta / m * s - 2 * (Delta + delta / 2) / m ≤ 0 := by
    have h11 : (2 / m) * (m / 2 * s^2 - Delta * s - (Delta + delta / 2)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) hquad
    have h12 : (2 / m) * (m / 2 * s^2 - Delta * s - (Delta + delta / 2)) =
        s^2 - 2 * Delta / m * s - 2 * (Delta + delta / 2) / m := by
      field_simp [h_pos.ne'] <;> ring
    rw [h12] at h11
    exact h11
  have h13 : (s - Delta / m)^2 ≤ D / m^2 := by
    have h14 : (s - Delta / m)^2 = s^2 - 2 * Delta / m * s + (Delta / m)^2 := by ring
    rw [h14]
    have h15 : D / m^2 = (Delta / m)^2 + 2 * (Delta + delta / 2) / m := by
      simp only [hD_def]
      field_simp [h_pos.ne'] <;> ring
    rw [h15]
    linarith
  have h16 : (s - Delta / m)^2 ≤ (Real.sqrt D / m)^2 := by
    have h17 : (Real.sqrt D / m)^2 = D / m^2 := by
      field_simp [h_pos.ne'] <;> nlinarith [Real.sq_sqrt hD_nonneg]
    rw [h17]
    exact h13
  have h18 : |s - Delta / m| ≤ Real.sqrt D / m := by
    have h19 : 0 ≤ Real.sqrt D / m := by positivity
    have h20 : |s - Delta / m|^2 ≤ (Real.sqrt D / m)^2 := by
      have h21 : |s - Delta / m|^2 = (s - Delta / m)^2 := by rw [sq_abs]
      rw [h21]
      exact h16
    nlinarith [sq_nonneg (|s - Delta / m| - Real.sqrt D / m)]
  have h_root : s ≤ (Delta + Real.sqrt D) / m := by
    have h21 : s - Delta / m ≤ |s - Delta / m| := le_abs_self (s - Delta / m)
    have h22 : s ≤ Delta / m + Real.sqrt D / m := by linarith
    have h23 : Delta / m + Real.sqrt D / m = (Delta + Real.sqrt D) / m := by ring
    rw [h23] at h22
    exact h22

  -- Step 2: bound D ≤ t(Delta+delta)/K
  have h3 : 2 * m = t / (3 * K) := by
    rw [hm_eq]
    field_simp [hK_pos.ne'] <;> ring
  have h4 : Delta^2 ≤ (2 * t / (3 * K)) * Delta := by
    by_cases hD0 : Delta = 0
    · subst hD0
      simp
    · have hD_pos : 0 < Delta := lt_of_le_of_ne hDelta_nonneg (Ne.symm hD0)
      have h5 : Delta < 2 * t / (3 * K) := hDelta_lt
      have h6 : Delta * Delta ≤ (2 * t / (3 * K)) * Delta := by
        have h61 : Delta ≤ 2 * t / (3 * K) := by linarith [h5]
        have h62 : 0 ≤ Delta := by linarith
        exact mul_le_mul_of_nonneg_right h61 h62
      have h7 : Delta * Delta = Delta^2 := by ring
      rw [h7] at h6
      exact h6
  have h_bound1 : D ≤ t * (Delta + delta) / K := by
    have h_goal : Delta^2 + (t / (3 * K)) * (Delta + delta / 2) ≤ t * (Delta + delta) / K := by
      have h8 : (t / (3 * K)) * (Delta + delta / 2) = (t / (3 * K)) * Delta + (t / (6 * K)) * delta := by
        field_simp [hK_pos.ne'] <;> ring
      have h9 : t * (Delta + delta) / K = (t / K) * Delta + (t / K) * delta := by
        field_simp [hK_pos.ne'] <;> ring
      rw [h8, h9]
      have h10 : Delta^2 ≤ (2 * t / (3 * K)) * Delta := h4
      have h11 : (t / (3 * K)) * Delta ≤ (t / K) * Delta := by
        have h12 : t / (3 * K) ≤ t / K := by
          gcongr <;> nlinarith
        gcongr
      have h13 : (t / (6 * K)) * delta ≤ (t / K) * delta := by
        gcongr <;> nlinarith
      have h14 : Delta^2 + (t / (3 * K)) * Delta + (t / (6 * K)) * delta ≤
          (2 * t / (3 * K)) * Delta + (t / (3 * K)) * Delta + (t / (6 * K)) * delta := by
        gcongr
      have h15 : (2 * t / (3 * K)) * Delta + (t / (3 * K)) * Delta + (t / (6 * K)) * delta =
          (t / K) * Delta + (t / (6 * K)) * delta := by
        field_simp [hK_pos.ne'] <;> ring
      have h16 : (t / K) * Delta + (t / (6 * K)) * delta ≤ (t / K) * Delta + (t / K) * delta := by
        gcongr
        <;> gcongr <;> nlinarith
      linarith
    have h_expand : D = Delta^2 + 2 * m * (Delta + delta / 2) := by simp [hD_def]
    rw [h_expand, h3]
    exact h_goal

  -- Step 3: sqrt D ≤ scale / sqrt K
  have h_sqrt_bound : Real.sqrt D ≤ scale / Real.sqrt K := by
    have h6 : Real.sqrt D ≤ Real.sqrt (t * (Delta + delta) / K) := Real.sqrt_le_sqrt h_bound1
    have h7 : Real.sqrt (t * (Delta + delta) / K) = scale / Real.sqrt K := by
      have h8 : t * (Delta + delta) / K = (Delta + delta) * t / K := by ring
      rw [h8]
      rw [Real.sqrt_div (by positivity)]
      rw [hscale] <;> ring
    rw [h7] at h6
    exact h6

  -- Step 4: Delta ≤ scale
  have h11 : Delta ≤ scale := delta_le_scale hK ht_pos hdelta hDelta_nonneg hDelta_lt hscale

  -- Step 5: combine
  have h24 : t * s ≤ t * ((Delta + Real.sqrt D) / m) :=
    mul_le_mul_of_nonneg_left h_root (by linarith)
  have h25 : t * ((Delta + Real.sqrt D) / m) = (t / m) * (Delta + Real.sqrt D) := by ring
  have h26 : t / m = 6 * K := by
    rw [hm_eq]
    field_simp [hK_pos.ne'] <;> ring
  have h27 : (t / m) * (Delta + Real.sqrt D) ≤ (6 * K) * (Delta + scale / Real.sqrt K) := by
    rw [h26]
    have h271 : Delta + Real.sqrt D ≤ Delta + scale / Real.sqrt K := by linarith [h_sqrt_bound]
    exact mul_le_mul_of_nonneg_left h271 (by positivity)
  have hsqrt_pos : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK_pos
  have h29 : (Real.sqrt K)^2 = K := Real.sq_sqrt (by linarith)
  have h281 : K / Real.sqrt K = Real.sqrt K := by
    have hpos : 0 < Real.sqrt K := hsqrt_pos
    have h_eq : K / Real.sqrt K = (Real.sqrt K)^2 / Real.sqrt K := by
      congr 1
      · exact h29.symm
    rw [h_eq]
    have h_div : (Real.sqrt K)^2 / Real.sqrt K = Real.sqrt K := by
      field_simp [hpos.ne'] <;> ring
    exact h_div
  have h28 : (6 * K) * (Delta + scale / Real.sqrt K) = 6 * K * Delta + 6 * Real.sqrt K * scale := by
    calc
      (6 * K) * (Delta + scale / Real.sqrt K)
        = 6 * K * Delta + 6 * K * (scale / Real.sqrt K) := by ring
      _ = 6 * K * Delta + 6 * (K / Real.sqrt K) * scale := by ring
      _ = 6 * K * Delta + 6 * Real.sqrt K * scale := by rw [h281] <;> ring
  have h30 : 6 * K * Delta + 6 * Real.sqrt K * scale ≤ (6 * K + 6 * Real.sqrt K) * scale := by
    have h31 : 6 * K * Delta ≤ 6 * K * scale := by
      exact mul_le_mul_of_nonneg_left h11 (by positivity)
    linarith
  calc t * s
    ≤ t * ((Delta + Real.sqrt D) / m) := h24
  _ = (t / m) * (Delta + Real.sqrt D) := h25
  _ ≤ (6 * K) * (Delta + scale / Real.sqrt K) := h27
  _ = 6 * K * Delta + 6 * Real.sqrt K * scale := h28
  _ ≤ (6 * K + 6 * Real.sqrt K) * scale := h30

-- ============================================================================
-- Helper: algebraic bound for Taylor neighborhood
-- ============================================================================

private lemma taylor_algebraic_bound {K C1 : ℝ} (hK : 1 ≤ K) (hC1 : 1000 * K ≤ C1) :
    (1 + 6 * K + 6 * Real.sqrt K) / C1 + 1 / (2 * C1^2) ≤ 1 / 2 := by
  have hK_pos : 0 < K := by linarith
  have hC1_pos : 0 < C1 := by nlinarith
  have hsqrt_le : Real.sqrt K ≤ K := by
    have h4 : Real.sqrt K ≤ Real.sqrt (K^2) := Real.sqrt_le_sqrt (by nlinarith)
    have h5 : Real.sqrt (K^2) = K := by
      rw [Real.sqrt_sq_eq_abs] <;> rw [abs_of_nonneg] <;> linarith
    linarith
  have h9 : 6 * Real.sqrt K ≤ 6 * K := by
    exact mul_le_mul_of_nonneg_left hsqrt_le (by norm_num)
  have h8 : 1 + 6 * K + 6 * Real.sqrt K ≤ 13 * K := by nlinarith
  have h7 : (1 + 6 * K + 6 * Real.sqrt K) / C1 ≤ 13 / 1000 := by
    have h10 : (1 + 6 * K + 6 * Real.sqrt K) / C1 ≤ (13 * K) / (1000 * K) := by
      gcongr <;> linarith
    have h11 : (13 * K) / (1000 * K) = 13 / 1000 := by
      field_simp [hK_pos.ne'] <;> ring
    rw [h11] at h10
    exact h10
  have h10 : 1 / (2 * C1^2) ≤ 1 / 2000000 := by
    have h11 : C1 ≥ 1000 := by nlinarith
    have h12 : C1^2 ≥ 1000000 := by nlinarith
    have h13 : (0 : ℝ) < 1000000 := by norm_num
    exact one_div_le_one_div_of_le (by norm_num) (by nlinarith)
  nlinarith

-- ============================================================================
-- Helper: disjoint closed intervals ordered
-- ============================================================================

private lemma disjoint_intervals_order {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (h_disj : Disjoint (Set.Icc a b) (Set.Icc c d)) : b < c ∨ d < a := by
  by_cases h : b < c
  · exact Or.inl h
  · have h' : c ≤ b := by linarith
    by_cases h2 : d < a
    · exact Or.inr h2
    · have h3 : a ≤ d := by linarith
      have h4 : max a c ∈ Set.Icc a b := by
        have h41 : a ≤ max a c := le_max_left a c
        have h42 : max a c ≤ b := by
          apply max_le <;> linarith
        exact ⟨h41, h42⟩
      have h5 : max a c ∈ Set.Icc c d := by
        have h51 : c ≤ max a c := le_max_right a c
        have h52 : max a c ≤ d := by
          apply max_le <;> linarith
        exact ⟨h51, h52⟩
      exfalso
      simp only [Set.disjoint_left] at h_disj
      exact h_disj h4 h5

-- ============================================================================
-- Helper: connected interval in union of two disjoint intervals
-- ============================================================================

private lemma interval_in_union_disjoint {p q a b c d : ℝ} (hpq : p ≤ q)
    (hab : a ≤ b) (hcd : c ≤ d) (h_disj : Disjoint (Set.Icc a b) (Set.Icc c d))
    (h_sub : Set.Icc p q ⊆ Set.Icc a b ∪ Set.Icc c d)
    (x : ℝ) (hx : x ∈ Set.Icc p q) (hxa : x ∈ Set.Icc a b) :
    Set.Icc p q ⊆ Set.Icc a b := by
  have h_order : b < c ∨ d < a := disjoint_intervals_order hab hcd h_disj
  rcases h_order with (hbc | hda)
  · -- b < c
    intro y hy
    by_contra hya
    have hyb : y ∈ Set.Icc c d := (h_sub hy).resolve_left hya
    set z : ℝ := (b + c) / 2 with hz_def
    have hz1 : p ≤ z := by
      have h1 : p ≤ x := hx.1
      have h2 : x ≤ b := hxa.2
      have h3 : b < z := by linarith [hbc]
      linarith
    have hz2 : z ≤ q := by
      have h1 : c ≤ y := hyb.1
      have h2 : y ≤ q := hy.2
      have h3 : z < c := by linarith [hbc]
      linarith
    have hz : z ∈ Set.Icc p q := ⟨hz1, hz2⟩
    have h1 := h_sub hz
    have h2 : z ∉ Set.Icc a b := by
      intro h
      have h21 : a ≤ z := h.1
      have h22 : z ≤ b := h.2
      linarith [hbc]
    have h3 : z ∉ Set.Icc c d := by
      intro h
      have h31 : c ≤ z := h.1
      have h32 : z ≤ d := h.2
      linarith [hbc]
    exact h2 (h1.resolve_right h3)
  · -- d < a
    intro y hy
    by_contra hya
    have hyb : y ∈ Set.Icc c d := (h_sub hy).resolve_left hya
    set z : ℝ := (d + a) / 2 with hz_def
    have hz1 : p ≤ z := by
      have h1 : p ≤ y := hy.1
      have h2 : y ≤ d := hyb.2
      have h3 : d < z := by linarith [hda]
      linarith
    have hz2 : z ≤ q := by
      have h1 : a ≤ x := hxa.1
      have h2 : x ≤ q := hx.2
      have h3 : z < a := by linarith [hda]
      linarith
    have hz : z ∈ Set.Icc p q := ⟨hz1, hz2⟩
    have h1 := h_sub hz
    have h2 : z ∉ Set.Icc a b := by
      intro h
      have h21 : a ≤ z := h.1
      have h22 : z ≤ b := h.2
      linarith [hda]
    have h3 : z ∉ Set.Icc c d := by
      intro h
      have h31 : c ≤ z := h.1
      have h32 : z ≤ d := h.2
      linarith [hda]
    exact h2 (h1.resolve_right h3)

-- ============================================================================
-- Helper: neighborhood bound implies component length bound
-- ============================================================================

private lemma neighborhood_implies_length_bound
    {I : ParameterInterval} {f g : C2Function} {delta L_target : ℝ}
    {H : ℝ → ℝ} {E : Set UnitPoint}
    {pieces : IntervalFamily} {x : UnitPoint} {j : Fin pieces.card}
    (hE : E = tangencySublevelSetOn I f g delta)
    (h_eval : ∀ (x : UnitPoint), H (x : ℝ) = f x - g x)
    (h_pieces_union : pieces.union = E)
    (h_pieces_card : pieces.card ≤ 2)
    (h_pieces_disjoint : ∀ (j1 j2 : Fin pieces.card), j1 ≠ j2 →
      Disjoint (pieces.interval j1).carrier (pieces.interval j2).carrier)
    (h_x_in_J : x ∈ (pieces.interval j).carrier)
    (h_neighborhood : ∀ (w : ℝ), w ∈ Set.Icc I.left I.right → |w - (x : ℝ)| ≤ L_target → |H w| ≤ delta)
    (h_L_le_eighth : L_target ≤ I.length / 8)
    (hL_target_pos : 0 < L_target) :
    (pieces.interval j).length ≥ L_target := by
  let J := pieces.interval j
  let a := J.left
  let b := J.right
  let xr : ℝ := (x : ℝ)
  let cL := I.midpoint - I.length / 8
  let cR := I.midpoint + I.length / 8
  have h_mid_left : I.midpoint - I.length / 2 = I.left := by
    simp [ParameterInterval.midpoint, ParameterInterval.length] <;> ring
  have h_mid_right : I.midpoint + I.length / 2 = I.right := by
    simp [ParameterInterval.midpoint, ParameterInterval.length] <;> ring
  have h_cL_eq : cL = I.midpoint - I.length / 8 := by rfl
  have h_cR_eq : cR = I.midpoint + I.length / 8 := by rfl
  have h_cL_ge : cL ≥ I.left := by
    rw [h_cL_eq]; linarith [h_mid_left, I.left_le_right, I.length_nonneg]
  have h_cR_le : cR ≤ I.right := by
    rw [h_cR_eq]; linarith [h_mid_right, I.left_le_right, I.length_nonneg]
  have h_x_in_E : x ∈ E := by
    have h1 : x ∈ pieces.union := ⟨j, h_x_in_J⟩
    rwa [h_pieces_union] at h1
  have h_x_center : x ∈ I.centeredCarrier (1 / 4) := by
    have h2 : x ∈ tangencySublevelSetOn I f g delta := by
      rw [hE] at h_x_in_E; exact h_x_in_E
    have h3 : x ∈ I.centeredCarrier (1 / 4) ∧ |f x - g x| ≤ delta := by
      simpa [tangencySublevelSetOn, Set.mem_setOf_eq] using h2
    exact h3.1
  have h_x_center' : |xr - I.midpoint| ≤ (1 / 4 : ℝ) * I.length / 2 := by
    simpa [ParameterInterval.centeredCarrier, Set.mem_setOf_eq] using h_x_center
  have h_x_bounds : cL ≤ xr ∧ xr ≤ cR := by
    have h1 : |xr - I.midpoint| ≤ I.length / 8 := by
      have h2 : |xr - I.midpoint| ≤ (1 / 4 : ℝ) * I.length / 2 := h_x_center'
      have h3 : (1 / 4 : ℝ) * I.length / 2 = I.length / 8 := by ring
      rw [h3] at h2; exact h2
    rw [abs_le] at h1
    rw [h_cL_eq, h_cR_eq]
    exact ⟨by linarith, by linarith⟩
  have h_room : xr - L_target ≥ cL ∨ xr + L_target ≤ cR := by
    have h_a : 0 ≤ xr - cL := by linarith [h_x_bounds.1]
    have h_b : 0 ≤ cR - xr := by linarith [h_x_bounds.2]
    have h1 : (xr - cL) + (cR - xr) = I.length / 4 := by
      rw [h_cL_eq, h_cR_eq] <;> ring
    have h4 : max (xr - cL) (cR - xr) ≥ I.length / 8 := by
      by_contra h5
      have h6 : max (xr - cL) (cR - xr) < I.length / 8 := by linarith
      have h7 : xr - cL < I.length / 8 := lt_of_le_of_lt (le_max_left _ _) h6
      have h8 : cR - xr < I.length / 8 := lt_of_le_of_lt (le_max_right _ _) h6
      linarith
    have h5 : L_target ≤ I.length / 8 := h_L_le_eighth
    by_cases h6 : xr - cL ≥ L_target
    · exact Or.inl (by linarith)
    · have h7 : cR - xr ≥ L_target := by linarith
      exact Or.inr (by linarith)
  let pieces_union_real : Set ℝ := ⋃ (k : Fin pieces.card), Set.Icc (pieces.interval k).left (pieces.interval k).right
  have hJ_component : ∀ (p q : ℝ), p ≤ q → xr ∈ Set.Icc p q →
      (∀ r ∈ Set.Icc p q, |r - I.midpoint| ≤ (1 / 4 : ℝ) * I.length / 2 ∧ |H r| ≤ delta) →
      Set.Icc p q ⊆ Set.Icc a b := by
    intro p q hpq hxr_pq h_interval
    have h_forall_in_E : ∀ r ∈ Set.Icc p q, r ∈ pieces_union_real := by
      intro r hr
      have h2_real : |r - I.midpoint| ≤ (1 / 4 : ℝ) * I.length / 2 := (h_interval r hr).1
      have h2_real' : |r - I.midpoint| ≤ I.length / 8 := by
        have h_eq : (1 / 4 : ℝ) * I.length / 2 = I.length / 8 := by ring
        rw [h_eq] at h2_real; exact h2_real
      have h_r_ge : I.left ≤ r := by
        have h2 : -(I.length / 8) ≤ r - I.midpoint := (abs_le.mp h2_real').1
        have h3 : I.midpoint - I.length / 2 ≤ r := by linarith
        rw [h_mid_left] at h3; exact h3
      have h_r_le : r ≤ I.right := by
        have h2 : r - I.midpoint ≤ I.length / 8 := (abs_le.mp h2_real').2
        have h3 : r ≤ I.midpoint + I.length / 2 := by linarith
        rw [h_mid_right] at h3; exact h3
      have h_r0 : 0 ≤ r := by linarith [I.left_mem.1]
      have h_r1 : r ≤ 1 := by linarith [I.right_mem.2]
      let z : UnitPoint := ⟨r, ⟨h_r0, h_r1⟩⟩
      have hz_eq : (z : ℝ) = r := by rfl
      have h2 : z ∈ I.centeredCarrier (1 / 4) := by
        simp only [ParameterInterval.centeredCarrier, Set.mem_setOf_eq]
        rw [hz_eq]
        exact h2_real
      have h3 : z ∈ I.carrier := I.centeredCarrier_subset_carrier (by norm_num) (by norm_num) h2
      have h6 : H r = f z - g z := h_eval z
      have h_fg_bound : |f z - g z| ≤ delta := by
        have h_eq : f z - g z = H r := h6.symm
        rw [h_eq]
        exact (h_interval r hr).2
      have h7 : z ∈ E := by
        rw [hE]
        simp only [tangencySublevelSetOn, Set.mem_setOf_eq]
        exact ⟨h2, h_fg_bound⟩
      have h8 : z ∈ pieces.union := by rw [h_pieces_union] <;> exact h7
      rcases h8 with ⟨k, hk⟩
      have h9 : r ∈ Set.Icc (pieces.interval k).left (pieces.interval k).right := by
        simp only [ParameterInterval.carrier, Set.mem_setOf_eq] at hk
        exact hk
      exact Set.mem_iUnion.mpr ⟨k, h9⟩
    have h_card_pos : 0 < pieces.card := by
      by_contra h
      have h0 : pieces.card = 0 := by omega
      have h1 : x ∈ pieces.union := ⟨j, h_x_in_J⟩
      have h_empty : pieces.union = (∅ : Set UnitPoint) := by
        ext y
        simp only [IntervalFamily.union, Set.mem_iUnion, Set.mem_empty_iff_false, iff_false]
        intro h2
        rcases h2 with ⟨k, _⟩
        have h3 : k.val < pieces.card := k.is_lt
        have h4 : k.val < 0 := by omega
        exact False.elim (Nat.not_lt_zero k.val h4)
      rw [h_empty] at h1
      simpa using h1
    by_cases h_card1 : pieces.card = 1
    · have h_only_J : ∀ (k : Fin pieces.card), k = j := by
        intro k
        have h2 : k.val = 0 := by omega
        have h3 : j.val = 0 := by omega
        apply Fin.ext; rw [h2, h3]
      have h_def : pieces_union_real = ⋃ (k : Fin pieces.card), Set.Icc (pieces.interval k).left (pieces.interval k).right := by rfl
      have h_union_real : pieces_union_real = Set.Icc a b := by
        rw [h_def]
        apply Set.ext
        intro r
        simp only [Set.mem_iUnion]
        constructor
        · rintro ⟨k, hk⟩
          have h5 : k = j := h_only_J k
          rw [h5] at hk
          exact hk
        · intro hr
          exact ⟨j, hr⟩
      rw [h_union_real] at h_forall_in_E
      exact h_forall_in_E
    · have h_card2 : pieces.card = 2 := by omega
      let e : Fin pieces.card ≃ Fin 2 := Equiv.cast (congr_arg Fin h_card2)
      let j2 : Fin 2 := e j
      let j'2 : Fin 2 := 1 - j2
      let j' : Fin pieces.card := e.symm j'2
      have h_j'2_ne_j2 : j'2 ≠ j2 := by
        intro h
        have h1 : j'2.val = j2.val := congr_arg (fun (x : Fin 2) => x.val) h
        have h2 : j'2.val = 1 - j2.val := by
          simp [j'2] <;> omega
        omega
      have hj'_ne : j' ≠ j := by
        intro h
        have h' : j'2 = j2 := by
          simpa [j', e.apply_symm_apply] using congr_arg e h
        exact h_j'2_ne_j2 h'
      let J' := pieces.interval j'
      have h_disj_real : Disjoint (Set.Icc a b) (Set.Icc J'.left J'.right) := by
        rw [Set.disjoint_left]
        intro r hr1 hr2
        have h4 : 0 ≤ r := by linarith [J.left_mem.1, hr1.1]
        have h5 : r ≤ 1 := by linarith [J.right_mem.2, hr1.2]
        let z : UnitPoint := ⟨r, ⟨h4, h5⟩⟩
        have hz1 : z ∈ J.carrier := by
          simp only [ParameterInterval.carrier, Set.mem_setOf_eq] <;> exact hr1
        have hz2 : z ∈ J'.carrier := by
          simp only [ParameterInterval.carrier, Set.mem_setOf_eq] <;> exact hr2
        have h_disj : Disjoint J.carrier J'.carrier := h_pieces_disjoint j j' (Ne.symm hj'_ne)
        have h_contra : z ∉ J'.carrier := by
          intro hz2
          exact Set.disjoint_left.mp h_disj hz1 hz2
        exact h_contra hz2
      have h_all_fin2 : ∀ (a b : Fin 2), a = b ∨ a = 1 - b := by
        intro a b
        fin_cases a <;> fin_cases b <;> simp <;> decide
      have h_def : pieces_union_real = ⋃ (k : Fin pieces.card), Set.Icc (pieces.interval k).left (pieces.interval k).right := by rfl
      have h_union2 : pieces_union_real = Set.Icc a b ∪ Set.Icc J'.left J'.right := by
        rw [h_def]
        apply Set.ext
        intro r
        simp only [Set.mem_iUnion, Set.mem_union]
        constructor
        · rintro ⟨k, hk⟩
          let k2 : Fin 2 := e k
          have h : k2 = j2 ∨ k2 = j'2 := by
            have h' := h_all_fin2 k2 j2
            simpa [j'2] using h'
          have h_k_eq : k = j ∨ k = j' := by
            rcases h with (h | h)
            · left
              have h_eq : e k = e j := by
                have h_k2 : k2 = e k := by rfl
                have h_j2 : j2 = e j := by rfl
                rw [h_k2, h_j2] at h; exact h
              exact e.injective h_eq
            · right
              have h_eq : e k = e j' := by
                have h_k2 : k2 = e k := by rfl
                have h_j'2 : j'2 = e j' := (e.apply_symm_apply j'2).symm
                rw [h_k2, h_j'2] at h; exact h
              exact e.injective h_eq
          rcases h_k_eq with (rfl | rfl) <;> tauto
        · rintro (h | h)
          · exact ⟨j, h⟩
          · exact ⟨j', h⟩
      rw [h_union2] at h_forall_in_E
      have h_xr_in_J : xr ∈ Set.Icc a b := by
        simpa [ParameterInterval.carrier, Set.mem_setOf_eq] using h_x_in_J
      exact interval_in_union_disjoint hpq J.left_le_right J'.left_le_right h_disj_real
        h_forall_in_E xr hxr_pq h_xr_in_J
  rcases h_room with (h_left | h_right)
  · let z := xr - L_target
    have hz_ge : z ≥ cL := by linarith
    have h_interval_E : ∀ r ∈ Set.Icc z xr, |r - I.midpoint| ≤ (1 / 4 : ℝ) * I.length / 2 ∧ |H r| ≤ delta := by
      intro r hr
      have h1 : cL ≤ r := by linarith [hr.1]
      have h2 : r ≤ cR := by linarith [h_x_bounds.2, hr.2]
      have h4 : |r - I.midpoint| ≤ (1 / 4 : ℝ) * I.length / 2 := by
        have h5 : |r - I.midpoint| ≤ I.length / 8 := by
          rw [abs_le] <;> constructor <;> linarith
        have h6 : I.length / 8 = (1 / 4 : ℝ) * I.length / 2 := by ring
        rw [h6] at h5; exact h5
      have h5 : r ∈ Set.Icc I.left I.right := by
        have h51 : I.left ≤ r := by linarith [I.left_mem.1, h1]
        have h52 : r ≤ I.right := by linarith [I.right_mem.2, h2]
        exact ⟨h51, h52⟩
      have h6 : |r - xr| ≤ L_target := by
        have h7 : xr - L_target ≤ r := hr.1
        have h8 : r ≤ xr := hr.2
        have h9 : r - xr ≤ 0 := by linarith
        have h10 : |r - xr| = xr - r := by
          rw [abs_of_nonpos h9] <;> linarith
        rw [h10]
        linarith
      exact ⟨h4, h_neighborhood r h5 h6⟩
    have h_zle : z ≤ xr := by
      dsimp only [z]
      linarith [hL_target_pos]
    have h_xrin : xr ∈ Set.Icc z xr := by
      simp only [Set.mem_Icc] <;> constructor <;> linarith [hL_target_pos]
    have h_sub : Set.Icc z xr ⊆ Set.Icc a b := hJ_component z xr h_zle h_xrin h_interval_E
    have h_z_mem : z ∈ Set.Icc z xr := ⟨by linarith, by linarith⟩
    have h_xr_mem : xr ∈ Set.Icc z xr := ⟨by linarith, by linarith⟩
    have h_a_le_z : a ≤ z := (h_sub h_z_mem).1
    have h_b_ge_xr : b ≥ xr := (h_sub h_xr_mem).2
    have hz : z = xr - L_target := by rfl
    have ha : a = J.left := by rfl
    have hb : b = J.right := by rfl
    have h_goal : b - a ≥ L_target := by
      linarith [hz, ha, hb, h_a_le_z, h_b_ge_xr]
    simpa [ParameterInterval.length] using h_goal
  · let z := xr + L_target
    have hz_le : z ≤ cR := by linarith
    have h_interval_E : ∀ r ∈ Set.Icc xr z, |r - I.midpoint| ≤ (1 / 4 : ℝ) * I.length / 2 ∧ |H r| ≤ delta := by
      intro r hr
      have h1 : cL ≤ r := by linarith [h_x_bounds.1, hr.1]
      have h2 : r ≤ cR := by linarith [hr.2]
      have h4 : |r - I.midpoint| ≤ (1 / 4 : ℝ) * I.length / 2 := by
        have h5 : |r - I.midpoint| ≤ I.length / 8 := by
          rw [abs_le] <;> constructor <;> linarith
        have h6 : I.length / 8 = (1 / 4 : ℝ) * I.length / 2 := by ring
        rw [h6] at h5; exact h5
      have h5 : r ∈ Set.Icc I.left I.right := by
        have h51 : I.left ≤ r := by linarith [I.left_mem.1, h1]
        have h52 : r ≤ I.right := by linarith [I.right_mem.2, h2]
        exact ⟨h51, h52⟩
      have h6 : |r - xr| ≤ L_target := by
        have h7 : xr ≤ r := hr.1
        have h8 : r ≤ xr + L_target := hr.2
        have h9 : 0 ≤ r - xr := by linarith
        have h10 : |r - xr| = r - xr := by
          rw [abs_of_nonneg h9] <;> linarith
        rw [h10]
        linarith
      exact ⟨h4, h_neighborhood r h5 h6⟩
    have h_xrle : xr ≤ z := by
      dsimp only [z]
      linarith [hL_target_pos]
    have h_xrin2 : xr ∈ Set.Icc xr z := by
      simp only [Set.mem_Icc] <;> constructor <;> linarith [hL_target_pos]
    have h_sub : Set.Icc xr z ⊆ Set.Icc a b := hJ_component xr z h_xrle h_xrin2 h_interval_E
    have h_xr_mem : xr ∈ Set.Icc xr z := ⟨by linarith, by linarith⟩
    have h_z_mem : z ∈ Set.Icc xr z := ⟨by linarith, by linarith⟩
    have h_a_le_xr : a ≤ xr := (h_sub h_xr_mem).1
    have h_b_ge_z : b ≥ z := (h_sub h_z_mem).2
    have hz : z = xr + L_target := by rfl
    have ha : a = J.left := by rfl
    have hb : b = J.right := by rfl
    have h_goal : b - a ≥ L_target := by
      linarith [hz, ha, hb, h_a_le_xr, h_b_ge_z]
    simpa [ParameterInterval.length] using h_goal

-- ============================================================================
-- Core lemma: assumes H'' ≥ m on I.carrier
-- ============================================================================

private lemma convex_case_lower_bound_core
    {K : ℝ} (hK : 1 ≤ K)
    {I : ParameterInterval} {f g : C2Function} {t delta scale : ℝ}
    (ht_pos : 0 < t) (ht_eq : t = c2Distance f g) (hdelta : 0 < delta)
    (hI_controlled : I.IsControlled K)
    (C1 : ℝ) (hC1_large : 1000 * K ≤ C1)
    (hscale : scale = Real.sqrt ((tangencyParameterOn I f g + delta) * t))
    (hdelta_le : delta ≤ (6 * K)⁻¹ * t)
    (H : ℝ → ℝ) (hH1 : Differentiable ℝ H) (hH2 : Differentiable ℝ (deriv H))
    (h_small_h : ∀ x ∈ I.carrier, |H (x : ℝ)| < (3 * K)⁻¹ * t)
    (h_small_h' : ∀ x ∈ I.carrier, |deriv H (x : ℝ)| < (3 * K)⁻¹ * t)
    (m : ℝ) (hm_eq : m = t / (6 * K))
    (hH''_lower : ∀ r ∈ I.carrier, deriv (deriv H) r ≥ m)
    (hH''_upper : ∀ r ∈ I.carrier, |deriv (deriv H) r| ≤ t)
    (h_eval : ∀ (x : UnitPoint), H (x : ℝ) = f x - g x)
    (h_deriv_eval : ∀ (x : UnitPoint), deriv H (x : ℝ) = f.firstDeriv x - g.firstDeriv x)
    (E E_half : Set UnitPoint)
    (hE : E = tangencySublevelSetOn I f g delta)
    (hE_half : E_half = tangencySublevelSetOn I f g (delta / 2))
    (pieces : IntervalFamily)
    (h_pieces_union : pieces.union = E)
    (h_pieces_card : pieces.card ≤ 2)
    (h_pieces_disjoint : ∀ (j1 j2 : Fin pieces.card), j1 ≠ j2 →
      Disjoint (pieces.interval j1).carrier (pieces.interval j2).carrier)
    (x : UnitPoint) (hx : x ∈ E_half)
    (j : Fin pieces.card) (h_x_in_J : x ∈ (pieces.interval j).carrier) :
    delta ≤ C1 * scale * (pieces.interval j).length := by
  let J := pieces.interval j
  let a := J.left
  let b := J.right
  let xr : ℝ := (x : ℝ)
  set Delta : ℝ := tangencyParameterOn I f g with hDelta_def
  have hK_pos : 0 < K := by linarith
  have hC1_pos : 0 < C1 := by nlinarith

  -- Convert I.carrier (Set UnitPoint) to real interval helpers
  have h_to_real : ∀ (z : UnitPoint), z ∈ I.carrier → (z : ℝ) ∈ Set.Icc I.left I.right := by
    intro z hz
    simp only [ParameterInterval.carrier, Set.mem_setOf_eq] at hz
    exact hz
  have h_from_real : ∀ (r : ℝ), r ∈ Set.Icc I.left I.right →
      ∃ (z : UnitPoint), (z : ℝ) = r ∧ z ∈ I.carrier := by
    intro r hr
    have h4 : 0 ≤ r := by linarith [I.left_mem.1, hr.1]
    have h5 : r ≤ 1 := by linarith [I.right_mem.2, hr.2]
    let z : UnitPoint := ⟨r, ⟨h4, h5⟩⟩
    have hz : z ∈ I.carrier := by
      simp only [ParameterInterval.carrier, Set.mem_setOf_eq] <;> exact hr
    exact ⟨z, rfl, hz⟩

  -- x in centered quarter and |H(x)| ≤ δ/2
  have h_x_center : x ∈ I.centeredCarrier (1 / 4) := by
    simp only [hE_half, tangencySublevelSetOn, Set.mem_setOf_eq] at hx
    exact hx.1
  have h_Hx_abs : |H xr| ≤ delta / 2 := by
    have h1 : H xr = f x - g x := h_eval x
    rw [h1]
    simp only [hE_half, tangencySublevelSetOn, Set.mem_setOf_eq] at hx
    exact hx.2
  have h_x_in_Icarrier : x ∈ I.carrier :=
    I.centeredCarrier_subset_carrier (by norm_num) (by norm_num) h_x_center
  have h_x_in_Icc : xr ∈ Set.Icc I.left I.right := h_to_real x h_x_in_Icarrier

  -- Tangency point y
  rcases tangency_parameter_attained I f g with ⟨y, hy_center, hΔ_eq⟩
  let yr : ℝ := (y : ℝ)
  have h_y_in_Icarrier : y ∈ I.carrier :=
    I.centeredCarrier_subset_carrier (by norm_num) (by norm_num) hy_center
  have h_y_in_Icc : yr ∈ Set.Icc I.left I.right := h_to_real y h_y_in_Icarrier
  have hHy_eq : |H yr| + |deriv H yr| = Delta := by
    have h1 : |f y - g y| + |f.firstDeriv y - g.firstDeriv y| = Delta := hΔ_eq
    have h2 : H yr = f y - g y := h_eval y
    have h3 : deriv H yr = f.firstDeriv y - g.firstDeriv y := h_deriv_eval y
    rw [h2, h3] at *
    exact h1
  have hDelta_nonneg : 0 ≤ Delta := by
    have h_pos : 0 ≤ |H yr| + |deriv H yr| := by positivity
    have h_eq : |H yr| + |deriv H yr| = Delta := hHy_eq
    linarith
  have hDelta_lt : Delta < 2 * t / (3 * K) := by
    have h1 : |H yr| < (3 * K)⁻¹ * t := h_small_h y h_y_in_Icarrier
    have h3 : |deriv H yr| < (3 * K)⁻¹ * t := h_small_h' y h_y_in_Icarrier
    have h5 : |H yr| + |deriv H yr| < 2 * ((3 * K)⁻¹ * t) := by linarith
    have h6 : 2 * ((3 * K)⁻¹ * t) = 2 * t / (3 * K) := by
      field_simp [hK_pos.ne'] <;> ring
    rw [h6] at h5
    linarith [hHy_eq]

  have hscale_pos : 0 < scale := by
    rw [hscale]
    have h1 : 0 < (Delta + delta) * t := by positivity
    exact Real.sqrt_pos.mpr h1

  -- Convert H'' bounds to real interval
  have hH''_lower_real : ∀ r ∈ Set.Icc I.left I.right, deriv (deriv H) r ≥ m := by
    intro r hr
    rcases h_from_real r hr with ⟨z, hz_eq, hz_carrier⟩
    have h1 : deriv (deriv H) r = deriv (deriv H) (z : ℝ) := by rw [hz_eq]
    rw [h1]
    exact hH''_lower z hz_carrier
  have hH''_upper_real : ∀ r ∈ Set.Icc I.left I.right, |deriv (deriv H) r| ≤ t := by
    intro r hr
    rcases h_from_real r hr with ⟨z, hz_eq, hz_carrier⟩
    have h1 : deriv (deriv H) r = deriv (deriv H) (z : ℝ) := by rw [hz_eq]
    rw [h1]
    exact hH''_upper z hz_carrier

  -- Step 1: quadratic bound on |x-y|
  set s : ℝ := |xr - yr| with hs_def
  have hs_nonneg : 0 ≤ s := abs_nonneg _
  have hm_pos' : 0 < m := by
    rw [hm_eq]
    positivity
  have hHy_le : |H yr| + |deriv H yr| ≤ Delta := le_of_eq hHy_eq
  have hquad := distance_quadratic hH1 hH2 hm_pos' I.left_le_right h_x_in_Icc h_y_in_Icc
    hH''_lower_real hHy_le h_Hx_abs
  have h_ts_bound : t * s ≤ (6 * K + 6 * Real.sqrt K) * scale :=
    t_distance_bound hK ht_pos hdelta hm_eq hDelta_nonneg hDelta_lt hscale hscale_pos s hs_nonneg hquad

  -- Step 2: bound |H'(x)|
  have h_H'x_bound : |deriv H xr| ≤ (1 + 6 * K + 6 * Real.sqrt K) * scale := by
    have h1 : |deriv H xr - deriv H yr| ≤ t * s := by
      have h2 := lipschitz_deriv f g x y
      have h3 : c2Distance f g = t := ht_eq.symm
      rw [h3] at h2
      have h4 : |deriv H xr - deriv H yr| =
          |(f.firstDeriv x - g.firstDeriv x) - (f.firstDeriv y - g.firstDeriv y)| := by
        rw [h_deriv_eval x, h_deriv_eval y] <;> rfl
      rw [h4]
      simpa [hs_def] using h2
    have h4 : |deriv H xr| ≤ |deriv H yr| + t * s := by
      calc |deriv H xr|
        = |deriv H yr + (deriv H xr - deriv H yr)| := by ring_nf
      _ ≤ |deriv H yr| + |deriv H xr - deriv H yr| := abs_add_le (deriv H yr) (deriv H xr - deriv H yr)
      _ ≤ |deriv H yr| + t * s := by gcongr
    have h5 : |deriv H yr| ≤ Delta := by
      have h6 : |deriv H yr| ≤ |H yr| + |deriv H yr| := by linarith [abs_nonneg (H yr)]
      linarith [hHy_eq]
    have h7 : Delta ≤ scale := delta_le_scale hK ht_pos hdelta hDelta_nonneg hDelta_lt hscale
    linarith [h_ts_bound]

  set A : ℝ := (1 + 6 * K + 6 * Real.sqrt K) * scale with hA_def
  set L_target : ℝ := delta / (C1 * scale) with hL_target_def
  have hL_target_pos : 0 < L_target := by
    simp [hL_target_def] <;> positivity

  -- Step 3: Taylor neighborhood bound
  have h_algebraic : A * L_target + t / 2 * L_target^2 ≤ delta / 2 := by
    have h1 : A * L_target = (1 + 6 * K + 6 * Real.sqrt K) * delta / C1 := by
      rw [hA_def, hL_target_def]
      field_simp [hscale_pos.ne'] <;> ring
    have h2 : t * delta ≤ scale^2 := by
      have h3 : scale^2 = (Delta + delta) * t := by
        rw [hscale]
        have h4 : 0 ≤ (Delta + delta) * t := by positivity
        rw [Real.sq_sqrt h4]
      rw [h3]
      have h4 : t * delta ≤ (Delta + delta) * t := by
        have h5 : 0 ≤ Delta * t := by positivity
        linarith
      exact h4
    have h3 : t / 2 * L_target^2 ≤ delta / (2 * C1^2) := by
      rw [hL_target_def]
      have h4 : t / 2 * (delta / (C1 * scale))^2 = (t * delta^2) / (2 * C1^2 * scale^2) := by
        field_simp [hscale_pos.ne'] <;> ring
      rw [h4]
      have h5 : t * delta^2 ≤ delta * scale^2 := by
        have h51 : t * delta^2 = delta * (t * delta) := by ring
        rw [h51]
        have h52 : 0 ≤ delta := by linarith
        exact mul_le_mul_of_nonneg_left h2 h52
      have h6 : (t * delta^2) / (2 * C1^2 * scale^2) ≤ delta / (2 * C1^2) := by
        have h7 : 0 < 2 * C1^2 * scale^2 := by positivity
        have h8 : (t * delta^2) / (2 * C1^2 * scale^2) ≤ (delta * scale^2) / (2 * C1^2 * scale^2) :=
          div_le_div_of_nonneg_right h5 (by positivity)
        have h9 : (delta * scale^2) / (2 * C1^2 * scale^2) = delta / (2 * C1^2) := by
          field_simp [hscale_pos.ne'] <;> ring
        rw [h9] at h8
        exact h8
      exact h6
    have h4 := taylor_algebraic_bound hK hC1_large
    have h_goal : A * L_target + t / 2 * L_target^2 ≤ delta / 2 := by
      have h5 : A * L_target + t / 2 * L_target^2 ≤ A * L_target + delta / (2 * C1^2) := by
        linarith [h3]
      have h6 : A * L_target + delta / (2 * C1^2) =
          (1 + 6 * K + 6 * Real.sqrt K) * delta / C1 + delta / (2 * C1^2) := by
        rw [h1] <;> ring
      rw [h6] at h5
      have h7 : (1 + 6 * K + 6 * Real.sqrt K) * delta / C1 + delta / (2 * C1^2) =
          delta * ((1 + 6 * K + 6 * Real.sqrt K) / C1 + 1 / (2 * C1^2)) := by ring
      rw [h7] at h5
      have h8 : delta * ((1 + 6 * K + 6 * Real.sqrt K) / C1 + 1 / (2 * C1^2)) ≤ delta / 2 := by
        have h9 : 0 ≤ delta := by linarith
        have h10 := mul_le_mul_of_nonneg_left h4 h9
        ring_nf at h10 ⊢
        exact h10
      linarith
    exact h_goal

  have h_neighborhood : ∀ (w : ℝ), w ∈ Set.Icc I.left I.right → |w - xr| ≤ L_target → |H w| ≤ delta := by
    intro w hw hdist
    have h_taylor : |H w - H xr - deriv H xr * (w - xr)| ≤ t / 2 * (w - xr)^2 :=
      taylor_remainder_bound_on_interval hH1 hH2 I.left_le_right hw h_x_in_Icc hH''_upper_real
    have h1 : |H w - H xr| ≤ |deriv H xr| * |w - xr| + t / 2 * (w - xr)^2 := by
      calc |H w - H xr|
        = |(H w - H xr - deriv H xr * (w - xr)) + deriv H xr * (w - xr)| := by ring_nf
      _ ≤ |H w - H xr - deriv H xr * (w - xr)| + |deriv H xr * (w - xr)| :=
          abs_add_le (H w - H xr - deriv H xr * (w - xr)) (deriv H xr * (w - xr))
      _ ≤ t / 2 * (w - xr)^2 + |deriv H xr| * |w - xr| := by
          gcongr <;> rw [abs_mul] <;> ring
      _ = |deriv H xr| * |w - xr| + t / 2 * (w - xr)^2 := by ring
    have h2 : |deriv H xr| * |w - xr| ≤ A * L_target := by
      have h3 : |deriv H xr| ≤ A := h_H'x_bound
      calc |deriv H xr| * |w - xr|
        ≤ A * |w - xr| := by gcongr
      _ ≤ A * L_target := by gcongr <;> exact hdist
    have h5 : (w - xr)^2 ≤ L_target^2 := by
      have h51 : (w - xr)^2 = |w - xr|^2 := by rw [sq_abs]
      rw [h51]
      gcongr <;> exact hdist
    have h7 : |H w - H xr| ≤ A * L_target + t / 2 * L_target^2 := by
      calc |H w - H xr|
        ≤ |deriv H xr| * |w - xr| + t / 2 * (w - xr)^2 := h1
      _ ≤ A * L_target + t / 2 * L_target^2 := by gcongr <;> linarith
    have h8 : |H w| ≤ |H xr| + |H w - H xr| := by
      have h9 : H w = H xr + (H w - H xr) := by ring
      rw [h9]
      simpa using norm_add_le (H xr) (H w - H xr)
    linarith [h_Hx_abs, h_algebraic]

  -- Step 4: L_target ≤ I.length/8
  have h_delta_le_scale : delta ≤ scale := by
    have h1 : delta ≤ t / (6 * K) := by
      have h2 : (6 * K)⁻¹ * t = t / (6 * K) := by field_simp [hK_pos.ne'] <;> ring
      rw [h2] at hdelta_le
      exact hdelta_le
    have h3 : delta^2 ≤ (Delta + delta) * t := by
      have h41 : delta ≤ t / (6 * K) := h1
      have h42 : t / (6 * K) ≤ t := by
        have h43 : 0 < t := ht_pos
        have h44 : 1 / (6 * K) ≤ 1 := by
          have h45 : 1 ≤ 6 * K := by linarith
          have h46 : 0 < 6 * K := by positivity
          exact (div_le_one h46).mpr h45
        calc t / (6 * K) = (1 / (6 * K)) * t := by ring
          _ ≤ 1 * t := by gcongr
          _ = t := by ring
      have h4 : delta ≤ t := by linarith
      nlinarith [hdelta, hDelta_nonneg, ht_pos]
    have h5 : 0 ≤ delta := by linarith
    have h6 : delta^2 ≤ scale^2 := by
      have h7 : scale^2 = (Delta + delta) * t := by
        rw [hscale]
        have h8 : 0 ≤ (Delta + delta) * t := by positivity
        rw [Real.sq_sqrt h8]
      rw [h7]
      exact h3
    nlinarith [h5, hscale_pos]
  have h_L_le_eighth : L_target ≤ I.length / 8 := by
    have h1 : L_target = (delta / scale) / C1 := by
      simp [hL_target_def] <;> ring
    rw [h1]
    have h2 : delta / scale ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact h_delta_le_scale
    have h3 : (delta / scale) / C1 ≤ 1 / C1 := by
      apply div_le_div_of_nonneg_right h2
      positivity
    have h4 : 1 / C1 ≤ 1 / (96 * K) := by
      have h5 : C1 ≥ 96 * K := by linarith [hC1_large]
      exact one_div_le_one_div_of_le (by positivity) h5
    have h6 : 1 / (96 * K) ≤ I.length / 8 := by
      have h7 : (12 * K)⁻¹ ≤ I.length := hI_controlled.1
      have h8 : (12 * K)⁻¹ = 1 / (12 * K) := by
        field_simp [hK_pos.ne'] <;> ring
      rw [h8] at h7
      have h9 : 1 / (12 * K) ≤ I.length := h7
      have h10 : 1 / (96 * K) = (1 / (12 * K)) / 8 := by
        field_simp [hK_pos.ne'] <;> ring
      rw [h10]
      exact div_le_div_of_nonneg_right h9 (by norm_num)
    linarith

  -- Steps 5-7: use extracted lemma to prove J.length ≥ L_target
  have h_final : J.length ≥ L_target :=
    neighborhood_implies_length_bound hE h_eval h_pieces_union h_pieces_card
      h_pieces_disjoint h_x_in_J h_neighborhood h_L_le_eighth hL_target_pos

  have h_pos : 0 < C1 * scale := by positivity
  have hne : (C1 * scale) ≠ 0 := h_pos.ne'
  have h9 : C1 * scale * L_target = delta := by
    simp [hL_target_def, hne] <;> field_simp [hne] <;> ring
  have h10 : C1 * scale * J.length ≥ delta := by
    have h11 : C1 * scale * L_target ≤ C1 * scale * J.length := by gcongr
    rw [h9] at h11
    exact h11
  exact h10

-- ============================================================================
-- Main lemma: handle sign of H''
-- ============================================================================

/-- Main lower bound lemma for the convex case. -/
lemma convex_case_lower_bound
    {K : ℝ} (hK : 1 ≤ K)
    {I : ParameterInterval} {f g : C2Function} {t delta scale : ℝ}
    (ht_pos : 0 < t) (ht_eq : t = c2Distance f g) (hdelta : 0 < delta)
    (hI_controlled : I.IsControlled K)
    (h_small_h : ∀ x ∈ I.carrier, |f x - g x| < (3 * K)⁻¹ * t)
    (h_small_h' : ∀ x ∈ I.carrier, |f.firstDeriv x - g.firstDeriv x| < (3 * K)⁻¹ * t)
    (h_large_h'' : ∀ x ∈ I.carrier, (6 * K)⁻¹ * t ≤ |f.secondDeriv x - g.secondDeriv x|)
    (C1 : ℝ) (hC1_large : 1000 * K ≤ C1)
    (hscale : scale = Real.sqrt ((tangencyParameterOn I f g + delta) * t))
    (hdelta_le : delta ≤ (6 * K)⁻¹ * t)
    (E E_half : Set UnitPoint)
    (hE : E = tangencySublevelSetOn I f g delta)
    (hE_half : E_half = tangencySublevelSetOn I f g (delta / 2))
    (pieces : IntervalFamily)
    (h_pieces_union : pieces.union = E)
    (h_pieces_card : pieces.card ≤ 2)
    (h_pieces_disjoint : ∀ (j1 j2 : Fin pieces.card), j1 ≠ j2 →
      Disjoint (pieces.interval j1).carrier (pieces.interval j2).carrier) :
    ∀ (x : UnitPoint), x ∈ E_half →
      ∃ (j : Fin pieces.card), x ∈ (pieces.interval j).carrier ∧
        delta ≤ C1 * scale * (pieces.interval j).length := by
  intro x hx
  have h_x_in_E : x ∈ E := by
    simp only [hE_half, hE, tangencySublevelSetOn, Set.mem_setOf_eq] at hx ⊢
    exact ⟨hx.1, by linarith [hx.2]⟩
  have h_x_in_union : x ∈ pieces.union := by
    rw [h_pieces_union] <;> exact h_x_in_E
  rcases h_x_in_union with ⟨j, h_x_in_J⟩

  let H : ℝ → ℝ := f.extension - g.extension
  have hH_c2 : ContDiff ℝ 2 H := ContDiff.sub f.extension_contDiff g.extension_contDiff
  have hH1 : Differentiable ℝ H := hH_c2.differentiable (by norm_num)
  have hH2 : Differentiable ℝ (deriv H) := by
    have h1 : ContDiff ℝ 1 (deriv H) := hH_c2.deriv'
    exact h1.differentiable (by norm_num)
  let m : ℝ := t / (6 * K)
  have hm_pos : 0 < m := by positivity

  have h_eval : ∀ (z : UnitPoint), H (z : ℝ) = f z - g z := by
    intro z
    simp [H]
  have h_deriv_eval : ∀ (z : UnitPoint), deriv H (z : ℝ) = f.firstDeriv z - g.firstDeriv z := by
    intro z
    have h_f_diff : Differentiable ℝ f.extension := f.extension_contDiff.differentiable (by norm_num)
    have h_g_diff : Differentiable ℝ g.extension := g.extension_contDiff.differentiable (by norm_num)
    have h1 : deriv H (z : ℝ) = deriv f.extension (z : ℝ) - deriv g.extension (z : ℝ) :=
      deriv_sub h_f_diff.differentiableAt h_g_diff.differentiableAt
    rw [h1, C2Function.deriv_extension_eq_firstDeriv, C2Function.deriv_extension_eq_firstDeriv] <;> abel

  have h_deriv2_eval : ∀ (z : UnitPoint), deriv (deriv H) (z : ℝ) = f.secondDeriv z - g.secondDeriv z := by
    intro z
    have h_eq_fun : deriv H = deriv f.extension - deriv g.extension := by
      funext w
      exact deriv_sub (f.extension_contDiff.differentiable (by norm_num)).differentiableAt
                      (g.extension_contDiff.differentiable (by norm_num)).differentiableAt
    rw [h_eq_fun]
    have h_f_diff2 : Differentiable ℝ (deriv f.extension) :=
      ContDiff.differentiable (ContDiff.deriv' (n := 1) f.extension_contDiff) (by norm_num)
    have h_g_diff2 : Differentiable ℝ (deriv g.extension) :=
      ContDiff.differentiable (ContDiff.deriv' (n := 1) g.extension_contDiff) (by norm_num)
    have h2 : deriv (deriv f.extension - deriv g.extension) (z : ℝ) =
               deriv (deriv f.extension) (z : ℝ) - deriv (deriv g.extension) (z : ℝ) :=
      deriv_sub (h_f_diff2 (z : ℝ)) (h_g_diff2 (z : ℝ))
    rw [h2, C2Function.secondDeriv_extension_eq_secondDeriv, C2Function.secondDeriv_extension_eq_secondDeriv] <;> abel

  have hK_pos : 0 < K := by linarith

  have hH''_abs : ∀ r ∈ Set.Icc I.left I.right, m ≤ |deriv (deriv H) r| := by
    intro r hr
    let z : UnitPoint := ⟨r, ⟨by linarith [I.left_mem.1, hr.1], by linarith [I.right_mem.2, hr.2]⟩⟩
    have hz : z ∈ I.carrier := by
      simp only [ParameterInterval.carrier, Set.mem_setOf_eq] <;> exact hr
    have h1 : deriv (deriv H) r = f.secondDeriv z - g.secondDeriv z := h_deriv2_eval z
    rw [h1]
    have h9 : m = (6 * K)⁻¹ * t := by
      simp [m]
      <;> field_simp [hK_pos.ne'] <;> ring
    rw [h9]
    exact h_large_h'' z hz
  have hH''_upper : ∀ r ∈ Set.Icc I.left I.right, |deriv (deriv H) r| ≤ t := by
    intro r hr
    let z : UnitPoint := ⟨r, ⟨by linarith [I.left_mem.1, hr.1], by linarith [I.right_mem.2, hr.2]⟩⟩
    have h1 : deriv (deriv H) r = f.secondDeriv z - g.secondDeriv z := h_deriv2_eval z
    rw [h1]
    have h2 : |f.secondDeriv z - g.secondDeriv z| ≤ c2Distance f g :=
      abs_secondDeriv_sub_le_c2Distance f g z
    have h3 : c2Distance f g = t := ht_eq.symm
    rw [h3] at h2
    exact h2
  have h1_diff : ContDiff ℝ 1 (deriv H) := ContDiff.deriv' (n := 1) hH_c2
  have h2_diff : ContDiff ℝ 0 (deriv (deriv H)) := ContDiff.deriv' (n := 0) h1_diff
  have hH''_cont : ContinuousOn (deriv (deriv H)) (Set.Icc I.left I.right) :=
    h2_diff.continuous.continuousOn

  have h_sign : (∀ r ∈ Set.Icc I.left I.right, 0 < deriv (deriv H) r) ∨
                  (∀ r ∈ Set.Icc I.left I.right, deriv (deriv H) r < 0) :=
    constant_sign_of_abs_ge' I.left_le_right hm_pos hH''_cont hH''_abs

  rcases h_sign with (h_pos | h_neg)
  · -- Case H'' > 0
    have h_lower : ∀ r ∈ I.carrier, deriv (deriv H) r ≥ m := by
      intro r hr
      have hr' : (r : ℝ) ∈ Set.Icc I.left I.right := by
        simp only [ParameterInterval.carrier, Set.mem_setOf_eq] at hr
        exact hr
      have h1 : 0 < deriv (deriv H) (r : ℝ) := h_pos (r : ℝ) hr'
      have h2 : m ≤ |deriv (deriv H) (r : ℝ)| := hH''_abs (r : ℝ) hr'
      have h3 : |deriv (deriv H) (r : ℝ)| = deriv (deriv H) (r : ℝ) := by
        rw [abs_of_pos] <;> exact h1
      linarith
    have h_upper : ∀ r ∈ I.carrier, |deriv (deriv H) r| ≤ t := by
      intro r hr
      have hr' : (r : ℝ) ∈ Set.Icc I.left I.right := by
        simp only [ParameterInterval.carrier, Set.mem_setOf_eq] at hr
        exact hr
      exact hH''_upper (r : ℝ) hr'
    have h_small_h_H : ∀ x ∈ I.carrier, |H (x : ℝ)| < (3 * K)⁻¹ * t := by
      intro x hx
      have h_eq : H (x : ℝ) = f x - g x := h_eval x
      rw [h_eq]
      exact h_small_h x hx
    have h_small_h'_H : ∀ x ∈ I.carrier, |deriv H (x : ℝ)| < (3 * K)⁻¹ * t := by
      intro x hx
      have h_eq : deriv H (x : ℝ) = f.firstDeriv x - g.firstDeriv x := h_deriv_eval x
      rw [h_eq]
      exact h_small_h' x hx
    exact ⟨j, h_x_in_J, convex_case_lower_bound_core hK ht_pos ht_eq hdelta hI_controlled
      C1 hC1_large hscale hdelta_le H hH1 hH2 h_small_h_H h_small_h'_H m rfl h_lower h_upper
      h_eval h_deriv_eval E E_half hE hE_half pieces h_pieces_union h_pieces_card h_pieces_disjoint
      x hx j h_x_in_J⟩

  · -- Case H'' < 0: apply to -H
    let H' : ℝ → ℝ := -H
    have hH'1 : Differentiable ℝ H' := hH1.neg
    have hH'2 : Differentiable ℝ (deriv H') := by
      have h_eq : deriv H' = -deriv H := by funext z; simp [H']
      rw [h_eq]
      exact hH2.neg
    have h_deriv_neg : deriv (-deriv H) = -deriv (deriv H) := by
      funext z
      have h4 : DifferentiableAt ℝ (deriv H) z := hH2 z
      have h5 : HasDerivAt (deriv H) (deriv (deriv H) z) z := h4.hasDerivAt
      exact h5.neg.deriv
    have h_lower : ∀ r ∈ I.carrier, deriv (deriv H') r ≥ m := by
      intro r hr
      have hr' : (r : ℝ) ∈ Set.Icc I.left I.right := by
        simp only [ParameterInterval.carrier, Set.mem_setOf_eq] at hr
        exact hr
      have h_eq1 : deriv H' = -deriv H := by funext z; simp [H']
      have h1 : deriv (deriv H') (r : ℝ) = -deriv (deriv H) (r : ℝ) := by
        have h2 : deriv (deriv H') = -deriv (deriv H) := by
          calc deriv (deriv H')
            = deriv (-deriv H) := by exact congr_arg deriv h_eq1
          _ = -deriv (deriv H) := h_deriv_neg
        exact congrFun h2 (r : ℝ)
      rw [h1]
      have h4 : deriv (deriv H) (r : ℝ) < 0 := h_neg (r : ℝ) hr'
      have h5 : m ≤ |deriv (deriv H) (r : ℝ)| := hH''_abs (r : ℝ) hr'
      have h6 : |deriv (deriv H) (r : ℝ)| = -deriv (deriv H) (r : ℝ) := by
        rw [abs_of_neg h4] <;> linarith
      linarith
    have h_upper : ∀ r ∈ I.carrier, |deriv (deriv H') r| ≤ t := by
      intro r hr
      have hr' : (r : ℝ) ∈ Set.Icc I.left I.right := by
        simp only [ParameterInterval.carrier, Set.mem_setOf_eq] at hr
        exact hr
      have h_eq1 : deriv H' = -deriv H := by funext z; simp [H']
      have h1 : deriv (deriv H') (r : ℝ) = -deriv (deriv H) (r : ℝ) := by
        have h2 : deriv (deriv H') = -deriv (deriv H) := by
          calc deriv (deriv H')
            = deriv (-deriv H) := by exact congr_arg deriv h_eq1
          _ = -deriv (deriv H) := h_deriv_neg
        exact congrFun h2 (r : ℝ)
      rw [h1]
      rw [abs_neg]
      exact hH''_upper (r : ℝ) hr'
    have h_eval' : ∀ (z : UnitPoint), H' (z : ℝ) = g z - f z := by
      intro z
      simp [H', h_eval z] <;> abel
    have h_deriv_eval' : ∀ (z : UnitPoint), deriv H' (z : ℝ) = g.firstDeriv z - f.firstDeriv z := by
      intro z
      have h1 : deriv H' (z : ℝ) = -deriv H (z : ℝ) := by
        have h_eq : deriv H' = -deriv H := by funext w; simp [H']
        rw [h_eq] <;> simp
      rw [h1, h_deriv_eval z] <;> abel
    have h_small_h_H' : ∀ x ∈ I.carrier, |H' (x : ℝ)| < (3 * K)⁻¹ * t := by
      intro x hx
      have h1 : |H' (x : ℝ)| = |H (x : ℝ)| := by
        have h2 : H' (x : ℝ) = -H (x : ℝ) := by simp [H']
        rw [h2, abs_neg]
      rw [h1]
      have h_eq : H (x : ℝ) = f x - g x := h_eval x
      rw [h_eq]
      exact h_small_h x hx
    have h_small_h'_H' : ∀ x ∈ I.carrier, |deriv H' (x : ℝ)| < (3 * K)⁻¹ * t := by
      intro x hx
      have h1 : |deriv H' (x : ℝ)| = |deriv H (x : ℝ)| := by
        have h2 : deriv H' (x : ℝ) = -deriv H (x : ℝ) := by
          have h_eq : deriv H' = -deriv H := by funext w; simp [H']
          rw [h_eq] <;> simp
        rw [h2, abs_neg]
      rw [h1]
      have h_eq : deriv H (x : ℝ) = f.firstDeriv x - g.firstDeriv x := h_deriv_eval x
      rw [h_eq]
      exact h_small_h' x hx
    -- Symmetry lemmas for swapping f and g
    have h_c2_sym : c2Distance g f = c2Distance f g := by
      have h1 : c2Distance g f = dist g f := by rfl
      have h2 : c2Distance f g = dist f g := by rfl
      rw [h1, h2]
      exact dist_comm g f
    have h_tp_sym : tangencyParameterOn I g f = tangencyParameterOn I f g := by
      unfold tangencyParameterOn
      congr
      ext r
      simp only [Set.mem_setOf_eq]
      constructor
      · rintro ⟨x, hx, rfl⟩
        refine ⟨x, hx, ?_⟩
        have h1 : |g x - f x| = |f x - g x| := by rw [abs_sub_comm]
        have h2 : |g.firstDeriv x - f.firstDeriv x| = |f.firstDeriv x - g.firstDeriv x| := by rw [abs_sub_comm]
        rw [h1, h2]
      · rintro ⟨x, hx, rfl⟩
        refine ⟨x, hx, ?_⟩
        have h1 : |f x - g x| = |g x - f x| := by rw [abs_sub_comm]
        have h2 : |f.firstDeriv x - g.firstDeriv x| = |g.firstDeriv x - f.firstDeriv x| := by rw [abs_sub_comm]
        rw [h1, h2]
    have h_E_sym : ∀ (d : ℝ), tangencySublevelSetOn I g f d = tangencySublevelSetOn I f g d := by
      intro d
      ext x
      simp only [tangencySublevelSetOn, Set.mem_setOf_eq]
      <;> rw [abs_sub_comm]
      <;> rfl
    have ht_eq' : t = c2Distance g f := by
      rw [h_c2_sym]
      exact ht_eq
    have hscale' : scale = Real.sqrt ((tangencyParameterOn I g f + delta) * t) := by
      rw [h_tp_sym]
      exact hscale
    have hE' : E = tangencySublevelSetOn I g f delta := by
      rw [h_E_sym delta]
      exact hE
    have hE_half' : E_half = tangencySublevelSetOn I g f (delta / 2) := by
      rw [h_E_sym (delta / 2)]
      exact hE_half
    exact ⟨j, h_x_in_J, convex_case_lower_bound_core (hK := hK) (I := I) (f := g) (g := f) (t := t)
      ht_pos ht_eq' hdelta hI_controlled C1 hC1_large hscale' hdelta_le H' hH'1 hH'2
      h_small_h_H' h_small_h'_H' m rfl h_lower h_upper h_eval' h_deriv_eval'
      E E_half hE' hE_half' pieces h_pieces_union h_pieces_card h_pieces_disjoint
      x hx j h_x_in_J⟩

end Kakeya.Cinematic
