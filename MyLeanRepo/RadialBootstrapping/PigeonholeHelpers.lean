module

/-
Dyadic annulus pigeonholing helpers for the concentrated case.
-/

public import MyLeanRepo.RadialBootstrapping.Basic

@[expose] public section


open MeasureTheory Metric Set Finset

noncomputable section

namespace RadialBootstrapping

/-- The finset of dyadic scales used by `dyadic_annulus_pigeonhole`:
    `{r · 2^k | k < N} ∪ {r^κ}`. -/
def dyadicAnnulusScales (r κ : ℝ) (N : ℕ) : Finset ℝ :=
  Finset.image (fun k : ℕ => r * (2 : ℝ)^k) (Finset.range N) ∪ {Real.rpow r κ}

/-- If the sum of a finite nonempty family of ENNReal values is ≥ c (c ≠ ⊤),
then at least one value is ≥ c / |s|. -/
lemma finset_pigeonhole_ennreal {ι : Type*} {s : Finset ι}
    (f : ι → ENNReal) {c : ENNReal} (hc : c ≠ ⊤)
    (hs : s.Nonempty) (h : ∑ i ∈ s, f i ≥ c) :
    ∃ i ∈ s, f i ≥ c / s.card := by
  by_cases h0 : c = 0
  · rw [h0]; rcases hs with ⟨i, hi⟩; exact ⟨i, hi, by simp⟩
  have hcard_pos : 0 < s.card := Finset.card_pos.mpr hs
  by_contra h'; push Not at h'
  have h2 : ∀ i ∈ s, f i < c / s.card := h'
  rcases hs with ⟨i0, hi0⟩
  have h_fin : ∀ i ∈ s, f i ≠ ⊤ := by
    intro i hi
    have hlt : f i < c / s.card := h2 i hi
    exact ne_top_of_lt hlt
  have hdiv_fin : c / s.card ≠ ⊤ := by
    have hpos : (s.card : ENNReal) ≠ 0 := by exact_mod_cast hcard_pos.ne'
    exact ENNReal.div_ne_top hc hpos
  have h3 : ∀ i ∈ s, ENNReal.toReal (f i) < ENNReal.toReal (c / s.card) := by
    intro i hi
    exact ENNReal.toReal_lt_toReal (h_fin i hi) hdiv_fin |>.mpr (h2 i hi)
  have h4 : ∑ i ∈ s, ENNReal.toReal (f i) < ∑ i ∈ s, ENNReal.toReal (c / s.card) := by
    apply Finset.sum_lt_sum
    · intro i hi; exact le_of_lt (h3 i hi)
    · exact ⟨i0, hi0, h3 i0 hi0⟩
  have h5 : ∑ i ∈ s, ENNReal.toReal (c / s.card) =
      (s.card : ℝ) * ENNReal.toReal (c / s.card) := by
    simp [Finset.sum_const] <;> ring
  have h6 : ENNReal.toReal (c / s.card) = ENNReal.toReal c / (s.card : ℝ) := by
    simp [ENNReal.toReal_div, hcard_pos.ne'] <;> ring
  rw [h5, h6] at h4
  have h7 : (s.card : ℝ) * (ENNReal.toReal c / (s.card : ℝ)) = ENNReal.toReal c := by
    field_simp [hcard_pos.ne'] <;> ring
  rw [h7] at h4
  have h8 : ENNReal.toReal (∑ i ∈ s, f i) = ∑ i ∈ s, ENNReal.toReal (f i) := by
    rw [ENNReal.toReal_sum]
    <;> intro i _; exact h_fin i ‹_›
  have h9 : ENNReal.toReal (∑ i ∈ s, f i) < ENNReal.toReal c := by
    rw [h8]; exact h4
  have hsum_fin : (∑ i ∈ s, f i) ≠ ⊤ := by
    rw [ENNReal.sum_ne_top]; intro i _; exact h_fin i ‹_›
  have h10 : ∑ i ∈ s, f i < c := by
    exact ENNReal.toReal_lt_toReal hsum_fin hc |>.mp h9
  exact not_le.mpr h10 h

/-- Given d ∈ [r, r·2^N), find k < N with r·2^k ≤ d < r·2^{k+1}. -/
lemma exists_dyadic_interval (r d : ℝ) (N : ℕ) (hr : 0 < r) (hN : 0 < N)
    (h_ge : r ≤ d) (h_lt : d < r * (2 : ℝ)^N) :
    ∃ k : ℕ, k < N ∧ r * (2 : ℝ)^k ≤ d ∧ d < r * (2 : ℝ)^(k + 1) := by
  have hP : ∃ n : ℕ, d < r * (2 : ℝ)^(n + 1) := by
    refine ⟨N - 1, ?_⟩
    have h_eq : (N - 1) + 1 = N := by omega
    rw [h_eq]; exact h_lt
  let k := Nat.find hP
  have hk_lt : d < r * (2 : ℝ)^(k + 1) := Nat.find_spec hP
  have hk_le_N1 : k ≤ N - 1 := by
    by_contra h
    have h' : N - 1 < k := by omega
    have h_not := Nat.find_min hP h'
    have h_PN1 : d < r * (2 : ℝ)^((N - 1) + 1) := by
      have h_eq : (N - 1) + 1 = N := by omega
      rw [h_eq]; exact h_lt
    contradiction
  have hk_lt_N : k < N := by omega
  have hk_ge : r * (2 : ℝ)^k ≤ d := by
    by_cases h_k0 : k = 0
    · rw [h_k0]; norm_num at *; linarith
    · have h_kpos : 0 < k := by omega
      let k' := k - 1
      have h_k'_lt_k : k' < k := by dsimp only [k']; omega
      have h_not := Nat.find_min hP h_k'_lt_k
      have h_k'_lt_N : k' < N := by omega
      have h_ge' : ¬(d < r * (2 : ℝ)^(k' + 1)) := by simpa using h_not
      have h_eq : k' + 1 = k := by dsimp only [k']; omega
      rw [h_eq] at h_ge'
      exact le_of_not_gt h_ge'
  exact ⟨k, hk_lt_N, hk_ge, hk_lt⟩

/-- The identity 2^x = r^(κ-1) where x = (1-κ)·log(1/r)/log(2). -/
lemma dyadic_pow_identity (r kappa : ℝ) (hr : 0 < r) (hr_small : r < 1)
    (hkappa_pos : 0 < kappa) (hkappa_lt_one : kappa < 1) :
    (2 : ℝ)^((1 - kappa) * Real.log (1 / r) / Real.log 2) = r ^ (kappa - 1) := by
  set x : ℝ := (1 - kappa) * Real.log (1 / r) / Real.log 2 with hx_def
  have h_pos1 : 0 < (1 / r) := by positivity
  have h_log2_ne_zero : Real.log 2 ≠ 0 := by
    have h : 0 < Real.log 2 := Real.log_pos (by norm_num)
    exact h.ne'
  have h1 : (2 : ℝ)^x = Real.exp (x * Real.log 2) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)] <;> ring_nf
  rw [h1]
  have h2 : x * Real.log 2 = (1 - kappa) * Real.log (1 / r) := by
    dsimp only [x]
    have h : ((1 - kappa) * Real.log (1 / r) / Real.log 2) * Real.log 2 =
        (1 - kappa) * Real.log (1 / r) := by
      field_simp [h_log2_ne_zero] <;> ring
    exact h
  rw [h2]
  have h3 : Real.exp ((1 - kappa) * Real.log (1 / r)) = (1 / r) ^ (1 - kappa) := by
    have h4 : (1 / r) ^ (1 - kappa) = Real.exp ((1 - kappa) * Real.log (1 / r)) := by
      rw [Real.rpow_def_of_pos h_pos1] <;> ring_nf
    exact h4.symm
  rw [h3]
  have h5 : (1 / r) ^ (1 - kappa) = r ^ (-(1 - kappa)) := by
    have h6 : (1 / r) = r ^ (-1 : ℝ) := by
      have h7 : r ^ (-1 : ℝ) = 1 / r := by
        rw [Real.rpow_neg (show 0 ≤ r by linarith)] <;> simp
      exact h7.symm
    rw [h6]
    have h8 : (r ^ (-1 : ℝ)) ^ (1 - kappa) = r ^ ((-1 : ℝ) * (1 - kappa)) := by
      rw [← Real.rpow_mul (show 0 ≤ r by linarith)] <;> ring
    rw [h8] <;> ring_nf
  rw [h5]
  have h9 : -(1 - kappa) = kappa - 1 := by ring
  rw [h9]

/-- Number of dyadic scales N+1 < (1/6)·r^{-η}. -/
lemma dyadic_scale_count_bound (r eta kappa C : ℝ)
    (hr : 0 < r) (hr_small : r < 1) (heta : 0 < eta)
    (hkappa_pos : 0 < kappa) (hkappa_lt_one : kappa < 1) (hC : 1 ≤ C)
    (h_r_log_small : Real.rpow r eta * Real.log (1 / r) ≤ 1 / 100)
    (h_r_final : 20 * C * Real.rpow r eta < 1) :
    (Nat.ceil ((1 - kappa) * Real.log (1 / r) / Real.log 2) + 1 : ℝ) <
      (1 / 6 : ℝ) * Real.rpow r (-eta) := by
  set x : ℝ := (1 - kappa) * Real.log (1 / r) / Real.log 2 with hx_def
  set N : ℕ := Nat.ceil x with hN_def
  have h1k_pos : 0 < 1 - kappa := by linarith
  have h_ir_gt_one : 1 < 1 / r := by apply one_lt_one_div <;> linarith
  have hlog_pos : 0 < Real.log (1 / r) := Real.log_pos h_ir_gt_one
  have hx_pos : 0 < x := by
    dsimp only [x]; have h1 : 0 < 1 - kappa := by linarith
    have h2 : 0 < Real.log (1 / r) := hlog_pos
    have h3 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  have hN_pos : 0 < N := Nat.ceil_pos.mpr hx_pos
  have h_ceil_lt : (N : ℝ) - 1 < x := by
    by_contra h
    have h' : x ≤ (N : ℝ) - 1 := by linarith
    have h_eq : (↑(N - 1) : ℝ) = (N : ℝ) - 1 := by simp [hN_pos] <;> omega
    have h'2 : x ≤ ↑(N - 1) := by rw [h_eq]; exact h'
    have h'' : N ≤ N - 1 := (Nat.ceil_le).mpr h'2
    omega
  have hN_le : (N : ℝ) ≤ x + 1 := by linarith
  have h_log2_gt_half : (1 / 2 : ℝ) < Real.log 2 := by
    have h5 : Real.exp (1 / 2 : ℝ) < 2 := by
      have h6 : Real.exp (1 / 2 : ℝ) * Real.exp (1 / 2 : ℝ) = Real.exp 1 := by
        rw [← Real.exp_add] <;> norm_num
      nlinarith [Real.exp_pos (1 / 2 : ℝ), Real.exp_one_lt_d9]
    have h7 : (1 / 2 : ℝ) < Real.log 2 := by
      have h8 : Real.log (Real.exp (1 / 2 : ℝ)) < Real.log 2 := Real.log_lt_log (by positivity) h5
      have h9 : Real.log (Real.exp (1 / 2 : ℝ)) = (1 / 2 : ℝ) := by rw [Real.log_exp]
      linarith
    exact h7
  have h_rpow_neg_eq : Real.rpow r (-eta) = (Real.rpow r eta)⁻¹ := by
    have h1 : Real.rpow r ((-eta) + eta) = Real.rpow r (-eta) * Real.rpow r eta :=
      Real.rpow_add hr (-eta) eta
    have h2 : (-eta) + eta = 0 := by ring
    have h3 : Real.rpow r (-eta) * Real.rpow r eta = 1 := by
      rw [← h1, h2] <;> simp
    exact eq_inv_of_mul_eq_one_left h3
  have h3pos : 0 < Real.rpow r eta := Real.rpow_pos_of_pos hr eta
  have h3' : Real.rpow r eta ≠ 0 := h3pos.ne'
  have h_log_small : Real.log (1 / r) ≤ (1 / 100 : ℝ) * Real.rpow r (-eta) := by
    have h4 : Real.rpow r eta * Real.log (1 / r) ≤ 1 / 100 := h_r_log_small
    have h_div : (Real.rpow r eta * Real.log (1 / r)) / Real.rpow r eta = Real.log (1 / r) := by
      field_simp [h3'] <;> ring
    have h51 : (Real.rpow r eta * Real.log (1 / r)) / Real.rpow r eta ≤ (1 / 100 : ℝ) / Real.rpow r eta := by
      apply div_le_div_of_nonneg_right h4 (by positivity)
    have h5 : Real.log (1 / r) ≤ (1 / 100 : ℝ) / Real.rpow r eta := by
      rw [h_div] at h51; exact h51
    have h6 : (1 / 100 : ℝ) / Real.rpow r eta = (1 / 100 : ℝ) * (Real.rpow r eta)⁻¹ := by ring
    rw [h6] at h5
    have h7 : (1 / 100 : ℝ) * (Real.rpow r eta)⁻¹ = (1 / 100 : ℝ) * Real.rpow r (-eta) := by
      rw [← h_rpow_neg_eq]
    rw [h7] at h5; exact h5
  have h_x_le : x ≤ (1 / 50 : ℝ) * Real.rpow r (-eta) := by
    have h_step1 : x ≤ Real.log (1 / r) / Real.log 2 := by
      dsimp only [x]
      have h : (1 - kappa) * Real.log (1 / r) ≤ Real.log (1 / r) := by nlinarith
      exact div_le_div_of_nonneg_right h (by positivity)
    have h_step2 : Real.log (1 / r) / Real.log 2 ≤ 2 * Real.log (1 / r) := by
      have h : (1 / 2 : ℝ) < Real.log 2 := h_log2_gt_half
      have h' : 0 ≤ Real.log (1 / r) := by positivity
      have h'' : Real.log (1 / r) / Real.log 2 ≤ Real.log (1 / r) / (1 / 2 : ℝ) := by gcongr <;> linarith
      have h3 : Real.log (1 / r) / (1 / 2 : ℝ) = 2 * Real.log (1 / r) := by ring
      linarith
    calc x ≤ Real.log (1 / r) / Real.log 2 := h_step1
    _ ≤ 2 * Real.log (1 / r) := h_step2
    _ ≤ 2 * ((1 / 100 : ℝ) * Real.rpow r (-eta)) := by gcongr
    _ = (1 / 50 : ℝ) * Real.rpow r (-eta) := by ring
  have h2 : 20 * Real.rpow r eta < 1 := by
    have h3 : 20 * Real.rpow r eta ≤ 20 * C * Real.rpow r eta := by gcongr <;> linarith
    linarith
  have h4 : Real.rpow r eta < 1 / 20 := by linarith
  have h_rinv_gt : 20 < (Real.rpow r eta)⁻¹ := by
    have h5 : (Real.rpow r eta)⁻¹ > (1 / 20 : ℝ)⁻¹ := by gcongr <;> linarith
    norm_num at h5 ⊢ <;> exact h5
  have h_rinv_gt' : 20 < Real.rpow r (-eta) := by rw [h_rpow_neg_eq]; exact h_rinv_gt
  have h2_bound : (2 : ℝ) ≤ (1 / 10 : ℝ) * Real.rpow r (-eta) := by
    have h : 20 ≤ Real.rpow r (-eta) := by linarith
    calc (2 : ℝ) = (1 / 10 : ℝ) * (20 : ℝ) := by norm_num
    _ ≤ (1 / 10 : ℝ) * Real.rpow r (-eta) := by gcongr
  have hpos_rpow : 0 < Real.rpow r (-eta) := by
    rw [h_rpow_neg_eq]; exact inv_pos.mpr h3pos
  have h_main : (N + 1 : ℝ) < (1 / 6 : ℝ) * Real.rpow r (-eta) := by
    calc (N + 1 : ℝ)
      ≤ x + 2 := by linarith
    _ ≤ (1 / 50 : ℝ) * Real.rpow r (-eta) + 2 := by gcongr
    _ ≤ (1 / 50 : ℝ) * Real.rpow r (-eta) + (1 / 10 : ℝ) * Real.rpow r (-eta) := by gcongr
    _ = (3 / 25 : ℝ) * Real.rpow r (-eta) := by ring
    _ < (1 / 6 : ℝ) * Real.rpow r (-eta) := by
      have h : (3 / 25 : ℝ) < (1 / 6 : ℝ) := by norm_num
      exact mul_lt_mul_of_pos_right h hpos_rpow
  exact h_main

/-- Helper: r * r^(κ-1) = r^κ. -/
lemma mul_rpow_kappa (r kappa : ℝ) (hr : 0 < r) (hkappa_pos : 0 < kappa) :
    r * r ^ (kappa - 1) = r ^ kappa := by
  have h_add : r ^ kappa = r ^ (1 : ℝ) * r ^ (kappa - 1) := by
    have h : r ^ ((1 : ℝ) + (kappa - 1)) = r ^ (1 : ℝ) * r ^ (kappa - 1) :=
      Real.rpow_add hr (1 : ℝ) (kappa - 1)
    have h4 : (1 : ℝ) + (kappa - 1) = kappa := by ring
    rw [h4] at h
    exact h
  have h1 : r ^ (1 : ℝ) = r := by simp
  rw [h1] at h_add
  exact h_add.symm

/-- Helper: ceil(x) - 1 < x for x > 0. -/
lemma ceil_sub_one_lt {x : ℝ} (hx : 0 < x) {N : ℕ} (hN : N = Nat.ceil x) :
    (N : ℝ) - 1 < x := by
  rw [hN]
  by_contra h
  have h' : x ≤ (Nat.ceil x : ℝ) - 1 := by linarith
  have hN_pos : 0 < Nat.ceil x := Nat.ceil_pos.mpr hx
  have h_eq : (↑(Nat.ceil x - 1) : ℝ) = (Nat.ceil x : ℝ) - 1 := by
    simp [hN_pos] <;> omega
  have h'2 : x ≤ ↑(Nat.ceil x - 1) := by rw [h_eq]; exact h'
  have h'' : Nat.ceil x ≤ Nat.ceil x - 1 := (Nat.ceil_le).mpr h'2
  omega

/-- Dyadic annulus pigeonholing: if S has mass ≥ (1/3)·r^{σ+3η} in
B(y, 2r^κ) and mass ≤ (1/6)·r^{σ+3η} in B(y, r), then some dyadic
annulus A(y, ξ) with r ≤ ξ ≤ r^κ has mass ≥ r^{σ+4η}. -/
lemma dyadic_annulus_pigeonhole
    (nu : Measure Point) (y : Point) (r kappa sigma eta C : ℝ)
    (hr : 0 < r) (hr_small : r < 1)
    (hsigma : 0 ≤ sigma) (heta : 0 < eta)
    (hC : 1 ≤ C)
    (hkappa_pos : 0 < kappa) (hkappa_lt_one : kappa < 1)
    (S : Set Point)
    (h_outer : nu (S ∩ ball y (2 * Real.rpow r kappa)) ≥
        ENNReal.ofReal ((1 / 3 : ℝ) * Real.rpow r (sigma + 3 * eta)))
    (h_inner : nu (S ∩ ball y r) ≤
        ENNReal.ofReal ((1 / 6 : ℝ) * Real.rpow r (sigma + 3 * eta)))
    (h_r_log_small : Real.rpow r eta * Real.log (1 / r) ≤ 1 / 100)
    (h_r_final : 20 * C * Real.rpow r eta < 1) :
    ∃ (xi : ℝ), xi ∈ dyadicAnnulusScales r kappa (Nat.ceil ((1 - kappa) * Real.log (1 / r) / Real.log 2)) ∧
      r ≤ xi ∧ xi ≤ Real.rpow r kappa ∧
      nu (S ∩ {z | xi ≤ dist z y ∧ dist z y < 2 * xi}) >
        ENNReal.ofReal (Real.rpow r (sigma + 4 * eta)) := by
  set r_kappa : ℝ := Real.rpow r kappa with hr_kappa_def
  have hr_kappa_pos : 0 < r_kappa := Real.rpow_pos_of_pos hr kappa
  have hr_lt_rkappa : r < r_kappa := by
    have hlog_r_neg : Real.log r < 0 := Real.log_neg hr hr_small
    have hlog_rkappa : Real.log (r ^ kappa) = kappa * Real.log r := by
      rw [Real.log_rpow hr] <;> ring
    have h2 : Real.log r < Real.log (r ^ kappa) := by
      rw [hlog_rkappa]
      nlinarith
    have h3 : 0 < r := hr
    have h4 : 0 < r ^ kappa := Real.rpow_pos_of_pos hr kappa
    exact (Real.log_lt_log_iff h3 h4).mp h2
  let Annulus (xi : ℝ) : Set Point := {z | xi ≤ dist z y ∧ dist z y < 2 * xi}
  have h_annulus_meas : ∀ (xi : ℝ), MeasurableSet (Annulus xi) := by
    intro xi
    have h1 : Annulus xi = ball y (2 * xi) \ ball y xi := by
      ext z
      simp [Annulus, dist_comm z y] <;> constructor <;> intro h <;> exact ⟨by linarith, by linarith⟩
    rw [h1]
    exact isOpen_ball.measurableSet.diff isOpen_ball.measurableSet
  let B_outer := ball y (2 * r_kappa)
  let B_inner := ball y r
  have hB_inner_sub_outer : B_inner ⊆ B_outer := by
    intro z hz
    have h : dist z y < r := hz
    have h' : r < 2 * r_kappa := by linarith [hr_lt_rkappa]
    have h'' : dist z y < 2 * r_kappa := by linarith
    exact h''
  let Region := S ∩ (B_outer \ B_inner)
  let a := nu (S ∩ B_inner)
  let b := nu Region
  have h_disj : Disjoint (S ∩ B_inner) Region := by
    rw [Set.disjoint_left]; intro x hx1 hx2; exact hx2.2.2 hx1.2
  have hB_inner_sub_outer : B_inner ⊆ B_outer := by
    intro z hz
    have h : dist z y < r := hz
    have h' : r < 2 * r_kappa := by linarith [hr_lt_rkappa]
    have h'' : dist z y < 2 * r_kappa := by linarith
    exact h''
  have h_union : (S ∩ B_inner) ∪ Region = S ∩ B_outer := by
    ext x
    simp only [Region, Set.mem_union, Set.mem_inter_iff, Set.mem_diff]
    <;> constructor <;> intro h <;> tauto
  have h_sub : nu (S ∩ B_outer) ≤ a + b := by
    have h_eq : (S ∩ B_inner) ∪ Region = S ∩ B_outer := h_union
    rw [← h_eq]
    exact measure_union_le _ _
  let M_ann : ENNReal := ENNReal.ofReal ((1 / 6 : ℝ) * Real.rpow r (sigma + 3 * eta))
  let M_outer : ENNReal := ENNReal.ofReal ((1 / 3 : ℝ) * Real.rpow r (sigma + 3 * eta))
  have hM_ann_ne_top : M_ann ≠ ⊤ := ENNReal.ofReal_ne_top
  have h_sigma3eta_nonneg : 0 ≤ sigma + 3 * eta := by linarith
  have hM_outer_eq : M_outer = 2 * M_ann := by
    have h_real : (1 / 3 : ℝ) * Real.rpow r (sigma + 3 * eta) =
        2 * ((1 / 6 : ℝ) * Real.rpow r (sigma + 3 * eta)) := by ring
    simp only [M_outer, M_ann]
    rw [h_real]
    have h_pos : 0 ≤ (2 : ℝ) := by norm_num
    have h_pos2 : 0 ≤ (1 / 6 : ℝ) * Real.rpow r (sigma + 3 * eta) := by
      exact mul_nonneg (by norm_num) (Real.rpow_nonneg (by linarith) _)
    have h_eq : ENNReal.ofReal (2 * ((1 / 6 : ℝ) * Real.rpow r (sigma + 3 * eta))) =
        (2 : ENNReal) * ENNReal.ofReal ((1 / 6 : ℝ) * Real.rpow r (sigma + 3 * eta)) := by
      rw [ENNReal.ofReal_mul h_pos]
      <;> norm_cast
    exact h_eq
  have h_a_le : a ≤ M_ann := h_inner
  have h_ab_ge : M_outer ≤ a + b := le_trans h_outer h_sub
  have h_b_ge : b ≥ M_ann := by
    by_contra h
    have h' : b < M_ann := lt_of_not_ge h
    have h_fin_b : b ≠ ⊤ := ne_top_of_lt h'
    have h_fin_a : a ≠ ⊤ := ne_top_of_le_ne_top hM_ann_ne_top h_a_le
    have h4 : a + b < M_ann + M_ann := by
      by_cases h_strict : a < M_ann
      · exact ENNReal.add_lt_add_of_lt_of_le h_fin_b h_strict (le_of_lt h')
      · have h_ge : M_ann ≤ a := le_of_not_gt h_strict
        have h_eq : a = M_ann := le_antisymm h_a_le h_ge
        rw [h_eq]
        have h5 : M_ann + b < M_ann + M_ann := by
          rw [add_comm M_ann b, add_comm M_ann M_ann]
          exact ENNReal.add_lt_add_of_lt_of_le hM_ann_ne_top h' (le_refl M_ann)
        exact h5
    rw [hM_outer_eq] at h_ab_ge
    have h5 : a + b ≥ M_ann + M_ann := by
      simpa [two_mul] using h_ab_ge
    exact not_le.mpr h4 h5
  set x : ℝ := (1 - kappa) * Real.log (1 / r) / Real.log 2 with hx_def
  set N : ℕ := Nat.ceil x with hN_def
  have hx_pos : 0 < x := by
    dsimp only [x]
    have h1 : 0 < 1 - kappa := by linarith
    have h2 : 0 < Real.log (1 / r) := by
      have h_ir : 1 < 1 / r := by apply one_lt_one_div <;> linarith
      exact Real.log_pos h_ir
    have h3 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  have hN_pos : 0 < N := Nat.ceil_pos.mpr hx_pos
  let scales : Finset ℝ := dyadicAnnulusScales r kappa N
  have hscales_def : scales = dyadicAnnulusScales r kappa N := rfl
  have h_inj : Function.Injective (fun k : ℕ => r * (2 : ℝ)^k) := by
    intro k1 k2 h
    have h' : (2 : ℝ)^k1 = (2 : ℝ)^k2 := by
      apply (mul_right_inj' (ne_of_gt hr)).mp; exact h
    by_cases hne : k1 < k2
    · have h'' : (2 : ℝ)^k1 < (2 : ℝ)^k2 := by gcongr <;> norm_num
      linarith
    · by_cases hne2 : k2 < k1
      · have h'' : (2 : ℝ)^k2 < (2 : ℝ)^k1 := by gcongr <;> norm_num
        linarith
      · have h_eq : k1 = k2 := by omega
        exact h_eq
  have h_scales_card : scales.card ≤ N + 1 := by
    have h1 : (Finset.image (fun k : ℕ => r * (2 : ℝ)^k) (Finset.range N)).card = N := by
      rw [Finset.card_image_of_injective _ h_inj]; simp
    calc scales.card
      ≤ (Finset.image (fun k : ℕ => r * (2 : ℝ)^k) (Finset.range N)).card + 1 := Finset.card_union_le _ _
    _ = N + 1 := by rw [h1] <;> ring
  have h_scales_nonempty : scales.Nonempty := by
    have h : r_kappa ∈ scales := by
      dsimp only [scales]
      apply Finset.mem_union_right
      exact Finset.mem_singleton_self r_kappa
    exact ⟨r_kappa, h⟩
  have h_ceil_lt : (N : ℝ) - 1 < x := ceil_sub_one_lt hx_pos rfl
  have h_pow_id : (2 : ℝ)^x = r ^ (kappa - 1) :=
    dyadic_pow_identity r kappa hr hr_small hkappa_pos hkappa_lt_one
  have h_scales_bounds : ∀ xi ∈ scales, r ≤ xi ∧ xi ≤ r_kappa := by
    intro xi hxi
    have hxi' : xi ∈ (Finset.image (fun k : ℕ => r * (2 : ℝ)^k) (Finset.range N) ∪ {r_kappa}) := by
      have h_unfold : scales = (Finset.image (fun k : ℕ => r * (2 : ℝ)^k) (Finset.range N) ∪ {r_kappa}) := by
        simp [scales, dyadicAnnulusScales, hr_kappa_def]
        <;> rfl
      rw [h_unfold] at hxi
      exact hxi
    rcases Finset.mem_union.mp hxi' with (hxi | hxi)
    · rcases Finset.mem_image.mp hxi with ⟨k, hk, rfl⟩
      have hk_lt_N : k < N := Finset.mem_range.mp hk
      have h_lower : r ≤ r * (2 : ℝ)^k := by
        have h2 : (1 : ℝ) ≤ (2 : ℝ) := by norm_num
        have h3 : (1 : ℝ)^k ≤ (2 : ℝ)^k := by gcongr
        have h4 : (1 : ℝ)^k = (1 : ℝ) := by simp
        nlinarith
      have h_k_le_N1 : k ≤ N - 1 := by omega
      have h3 : (2 : ℝ)^k ≤ (2 : ℝ)^(N - 1) := by
        have h_pow_mono : ∀ (m n : ℕ), m ≤ n → (2 : ℝ)^m ≤ (2 : ℝ)^n := by
          intro m n hmn
          induction' hmn with n hmn ih
          · simp
          · calc (2 : ℝ)^m ≤ (2 : ℝ)^n := ih
            _ ≤ (2 : ℝ)^(n + 1) := by
              simp [pow_succ] <;> norm_num <;> linarith
        exact h_pow_mono k (N - 1) h_k_le_N1
      have h6 : (N - 1 : ℝ) < x := h_ceil_lt
      have h7 : (2 : ℝ)^(N - 1) < (2 : ℝ)^x := by
        have h71 : (2 : ℝ)^(N - 1) = (2 : ℝ) ^ ((N - 1 : ℕ) : ℝ) := by
          simp [Real.rpow_natCast]
        rw [h71]
        have h6' : ((N - 1 : ℕ) : ℝ) < x := by
          have h_eq : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
            simp [hN_pos] <;> omega
          rw [h_eq]
          exact h6
        exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h6'
      have h_upper : r * (2 : ℝ)^k < r_kappa := by
        calc r * (2 : ℝ)^k
          ≤ r * (2 : ℝ)^(N - 1) := by gcongr
        _ < r * (2 : ℝ)^x := by gcongr
        _ = r * r ^ (kappa - 1) := by
          have h_pow : (2 : ℝ)^x = r ^ (kappa - 1) :=
            dyadic_pow_identity r kappa hr hr_small hkappa_pos hkappa_lt_one
          rw [h_pow]
        _ = r ^ kappa := mul_rpow_kappa r kappa hr hkappa_pos
        _ = r_kappa := by simp [r_kappa]
      exact ⟨h_lower, le_of_lt h_upper⟩
    · rw [Finset.mem_singleton] at hxi
      rw [hxi]; exact ⟨by linarith, by linarith⟩
  have h_cover : Region ⊆ ⋃ xi ∈ scales, S ∩ Annulus xi := by
    intro z hz
    have hz_S : z ∈ S := hz.1
    have hz_not_inner : z ∉ B_inner := hz.2.2
    have hz_ge : r ≤ dist z y := by
      simpa [B_inner] using not_lt.mp hz_not_inner
    have hz_lt : dist z y < 2 * r_kappa := hz.2.1
    by_cases h_case : dist z y < r_kappa
    · have hN_ge_x : (N : ℝ) ≥ x := Nat.le_ceil x
      have h2pow_ge : (2 : ℝ)^N ≥ (2 : ℝ)^x := by
        have h71 : (2 : ℝ)^N = (2 : ℝ) ^ ((N : ℝ)) := by
          simp [Real.rpow_natCast]
        rw [h71]
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hN_ge_x
      have h_r2N_ge : r * (2 : ℝ)^N ≥ r_kappa := by
        calc r * (2 : ℝ)^N
          ≥ r * (2 : ℝ)^x := by gcongr
        _ = r * r ^ (kappa - 1) := by
          have h_pow : (2 : ℝ)^x = r ^ (kappa - 1) :=
            dyadic_pow_identity r kappa hr hr_small hkappa_pos hkappa_lt_one
          rw [h_pow]
        _ = r ^ kappa := mul_rpow_kappa r kappa hr hkappa_pos
        _ = r_kappa := by simp [r_kappa]
      have h_upp : dist z y < r * (2 : ℝ)^N := by linarith
      have h_exists_k := exists_dyadic_interval r (dist z y) N hr hN_pos hz_ge h_upp
      rcases h_exists_k with ⟨k, hk_lt_N, h_ge, h_lt⟩
      let xi : ℝ := r * (2 : ℝ)^k
      have hxi_in : xi ∈ scales := by
        apply Finset.mem_union_left
        exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk_lt_N, rfl⟩
      have hz_ann : z ∈ Annulus xi := by
        simp only [Annulus, Set.mem_setOf_eq]
        have h_eq : 2 * xi = r * (2 : ℝ)^(k + 1) := by
          dsimp only [xi]; ring
        exact ⟨h_ge, by rw [h_eq]; exact h_lt⟩
      have h_goal : z ∈ ⋃ xi ∈ scales, S ∩ Annulus xi := by
        have h_in : z ∈ S ∩ Annulus xi := ⟨hz_S, hz_ann⟩
        exact Set.subset_biUnion_of_mem hxi_in h_in
      exact h_goal
    · have hz_ge_kappa : r_kappa ≤ dist z y := by linarith
      have hz_ann : z ∈ Annulus r_kappa := by
        simp only [Annulus, Set.mem_setOf_eq]; exact ⟨hz_ge_kappa, hz_lt⟩
      have hkappa_in : r_kappa ∈ scales := by
        apply Finset.mem_union_right
        exact Finset.mem_singleton_self _
      have h_goal : z ∈ ⋃ xi ∈ scales, S ∩ Annulus xi := by
        have h_in : z ∈ S ∩ Annulus r_kappa := ⟨hz_S, hz_ann⟩
        exact Set.subset_biUnion_of_mem hkappa_in h_in
      exact h_goal
  have h_sum_ge : ∑ xi ∈ scales, nu (S ∩ Annulus xi) ≥ b := by
    have h1 : Region ⊆ ⋃ xi ∈ scales, S ∩ Annulus xi := h_cover
    have h2 : nu Region ≤ nu (⋃ xi ∈ scales, S ∩ Annulus xi) := measure_mono h1
    have h3 : nu (⋃ xi ∈ scales, S ∩ Annulus xi) ≤ ∑ xi ∈ scales, nu (S ∩ Annulus xi) :=
      measure_biUnion_finset_le _ _
    exact le_trans h2 h3
  have h_sum_ge_Mann : ∑ xi ∈ scales, nu (S ∩ Annulus xi) ≥ M_ann :=
    le_trans h_b_ge h_sum_ge
  have h_pigeon := finset_pigeonhole_ennreal (fun xi => nu (S ∩ Annulus xi)) hM_ann_ne_top h_scales_nonempty h_sum_ge_Mann
  rcases h_pigeon with ⟨xi, hxi_scales, h_ge⟩
  have hxi_bounds : r ≤ xi ∧ xi ≤ r_kappa := h_scales_bounds xi hxi_scales
  have h_card_pos : 0 < scales.card := Finset.card_pos.mpr h_scales_nonempty
  have h_count_bound : (scales.card : ℝ) < (1 / 6 : ℝ) * Real.rpow r (-eta) := by
    have h1 : (scales.card : ℝ) ≤ (N + 1 : ℝ) := by exact_mod_cast h_scales_card
    have h2 := dyadic_scale_count_bound r eta kappa C hr hr_small heta hkappa_pos hkappa_lt_one hC h_r_log_small h_r_final
    linarith
  have h_rpow4_pos : 0 < Real.rpow r (sigma + 4 * eta) := Real.rpow_pos_of_pos hr _
  have h_sigma3eta_nonneg : 0 ≤ sigma + 3 * eta := by linarith
  have h_goal : M_ann / scales.card > ENNReal.ofReal (Real.rpow r (sigma + 4 * eta)) := by
    have h1 : (scales.card : ENNReal) < ENNReal.ofReal ((1 / 6 : ℝ) * Real.rpow r (-eta)) := by
      have h1' : (scales.card : ℝ) < (1 / 6 : ℝ) * Real.rpow r (-eta) := h_count_bound
      have h2 : (scales.card : ENNReal) = ENNReal.ofReal (scales.card : ℝ) := by simp
      rw [h2]
      have h_nonneg1 : 0 ≤ (scales.card : ℝ) := by positivity
      have h_rpow_pos : 0 < Real.rpow r (-eta) := Real.rpow_pos_of_pos hr (-eta)
      have h_nonneg2 : 0 ≤ (1 / 6 : ℝ) * Real.rpow r (-eta) := by positivity
      have h_le : ENNReal.ofReal (scales.card : ℝ) ≤ ENNReal.ofReal ((1 / 6 : ℝ) * Real.rpow r (-eta)) :=
        (ENNReal.ofReal_le_ofReal_iff h_nonneg2).mpr (by linarith)
      have h_ne : ENNReal.ofReal (scales.card : ℝ) ≠ ENNReal.ofReal ((1 / 6 : ℝ) * Real.rpow r (-eta)) := by
        intro h_eq
        have h_toReal1 : (ENNReal.ofReal (scales.card : ℝ)).toReal = (scales.card : ℝ) := by
          rw [ENNReal.toReal_ofReal h_nonneg1]
        have h_toReal2 : (ENNReal.ofReal ((1 / 6 : ℝ) * Real.rpow r (-eta))).toReal =
            (1 / 6 : ℝ) * Real.rpow r (-eta) := by
          rw [ENNReal.toReal_ofReal h_nonneg2]
        have h_eq' : (ENNReal.ofReal (scales.card : ℝ)).toReal =
            (ENNReal.ofReal ((1 / 6 : ℝ) * Real.rpow r (-eta))).toReal := by
          rw [h_eq]
        rw [h_toReal1, h_toReal2] at h_eq'
        linarith
      exact lt_of_le_of_ne h_le h_ne
    have h_inv : (ENNReal.ofReal ((1 / 6 : ℝ) * Real.rpow r (-eta)))⁻¹ < (scales.card : ENNReal)⁻¹ :=
      ENNReal.inv_lt_inv.mpr h1
    have h_mult : M_ann * (ENNReal.ofReal ((1 / 6 : ℝ) * Real.rpow r (-eta)))⁻¹ <
        M_ann * (scales.card : ENNReal)⁻¹ := by
      gcongr
      <;> simpa [M_ann] using ENNReal.ofReal_pos.mpr (by positivity)
    have h2 : M_ann / (scales.card : ENNReal) > M_ann / ENNReal.ofReal ((1 / 6 : ℝ) * Real.rpow r (-eta)) := by
      simpa [div_eq_mul_inv] using h_mult
    have h_posA : 0 < (1 / 6 : ℝ) * Real.rpow r (sigma + 3 * eta) := by
      have h : 0 < Real.rpow r (sigma + 3 * eta) := Real.rpow_pos_of_pos hr _
      positivity
    have h_posB : 0 < (1 / 6 : ℝ) * Real.rpow r (-eta) := by
      have h : 0 < Real.rpow r (-eta) := Real.rpow_pos_of_pos hr _
      positivity
    have h3 : M_ann / ENNReal.ofReal ((1 / 6 : ℝ) * Real.rpow r (-eta)) =
        ENNReal.ofReal (Real.rpow r (sigma + 4 * eta)) := by
      simp only [M_ann]
      have h4 : ENNReal.ofReal ((1 / 6 : ℝ) * Real.rpow r (sigma + 3 * eta)) /
          ENNReal.ofReal ((1 / 6 : ℝ) * Real.rpow r (-eta)) =
          ENNReal.ofReal (((1 / 6 : ℝ) * Real.rpow r (sigma + 3 * eta)) /
            ((1 / 6 : ℝ) * Real.rpow r (-eta))) := by
        exact (ENNReal.ofReal_div_of_pos h_posB).symm
      rw [h4]
      have h_cancel : ((1 / 6 : ℝ) * Real.rpow r (sigma + 3 * eta)) /
          ((1 / 6 : ℝ) * Real.rpow r (-eta)) =
          Real.rpow r (sigma + 3 * eta) / Real.rpow r (-eta) := by
        field_simp [h_posB.ne'] <;> ring
      rw [h_cancel]
      have h52 : (Real.rpow r (-eta))⁻¹ = Real.rpow r eta := by
        have h_prod : Real.rpow r (-eta) * Real.rpow r eta = 1 := by
          have h_add_rpow : Real.rpow r ((-eta) + eta) =
              Real.rpow r (-eta) * Real.rpow r eta := by
            have h : (r ^ ((-eta) + eta)) = (r ^ (-eta)) * (r ^ eta) := Real.rpow_add hr (-eta) eta
            exact h
          have h2 : (-eta) + eta = 0 := by ring
          rw [h2] at h_add_rpow
          have h3 : Real.rpow r 0 = 1 := by simp
          rw [h3] at h_add_rpow
          exact h_add_rpow.symm
        exact inv_eq_of_mul_eq_one_right h_prod
      have h_div : Real.rpow r (sigma + 3 * eta) / Real.rpow r (-eta) =
          Real.rpow r (sigma + 3 * eta) * (Real.rpow r (-eta))⁻¹ := by
        field_simp
      rw [h_div, h52]
      have h53 : Real.rpow r (sigma + 3 * eta) * Real.rpow r eta =
          Real.rpow r (sigma + 4 * eta) := by
        have h_add_rpow2 : Real.rpow r (sigma + 3 * eta) * Real.rpow r eta =
            Real.rpow r ((sigma + 3 * eta) + eta) := by
          have h : Real.rpow r ((sigma + 3 * eta) + eta) =
              Real.rpow r (sigma + 3 * eta) * Real.rpow r eta := by
            have h2 : (r ^ ((sigma + 3 * eta) + eta)) =
                (r ^ (sigma + 3 * eta)) * (r ^ eta) := Real.rpow_add hr (sigma + 3 * eta) eta
            exact h2
          exact h.symm
        rw [h_add_rpow2]
        have h2 : (sigma + 3 * eta) + eta = sigma + 4 * eta := by ring
        rw [h2] <;> rfl
      rw [h53]
      <;> rfl
    rw [h3] at h2
    exact h2
  exact ⟨xi, hxi_scales, hxi_bounds.1, hxi_bounds.2, lt_of_lt_of_le h_goal h_ge⟩

/-- Generalized dyadic annulus pigeonhole: takes arbitrary outer/inner mass bounds
    and concludes some annulus has mass ≥ (outer - inner) / ((1/6) * r^(-η)). -/
lemma dyadic_annulus_pigeonhole_general
    (nu : Measure Point) (y : Point) (r kappa sigma eta C : ℝ)
    (outer inner : ℝ)
    (hr : 0 < r) (hr_small : r < 1)
    (hsigma : 0 ≤ sigma) (heta : 0 < eta)
    (hC : 1 ≤ C)
    (hkappa_pos : 0 < kappa) (hkappa_lt_one : kappa < 1)
    (S : Set Point)
    (h_outer : nu (S ∩ ball y (2 * Real.rpow r kappa)) ≥ ENNReal.ofReal outer)
    (h_inner : nu (S ∩ ball y r) ≤ ENNReal.ofReal inner)
    (h_inner_nonneg : 0 ≤ inner) (h_outer_pos : 0 < outer) (h_lt : inner < outer)
    (h_r_log_small : Real.rpow r eta * Real.log (1 / r) ≤ 1 / 100)
    (h_r_final : 20 * C * Real.rpow r eta < 1) :
    ∃ (xi : ℝ), xi ∈ dyadicAnnulusScales r kappa (Nat.ceil ((1 - kappa) * Real.log (1 / r) / Real.log 2)) ∧
      r ≤ xi ∧ xi ≤ Real.rpow r kappa ∧
      nu (S ∩ {z | xi ≤ dist z y ∧ dist z y < 2 * xi}) ≥
        ENNReal.ofReal ((outer - inner) / ((1 / 6 : ℝ) * Real.rpow r (-eta))) := by
  set r_kappa : ℝ := Real.rpow r kappa with hr_kappa_def
  have hr_kappa_pos : 0 < r_kappa := Real.rpow_pos_of_pos hr kappa
  have hr_lt_rkappa : r < r_kappa := by
    have hlog_r_neg : Real.log r < 0 := Real.log_neg hr hr_small
    have hlog_rkappa : Real.log (r ^ kappa) = kappa * Real.log r := by
      rw [Real.log_rpow hr] <;> ring
    have h2 : Real.log r < Real.log (r ^ kappa) := by
      rw [hlog_rkappa]; nlinarith
    have h3 : 0 < r := hr
    have h4 : 0 < r ^ kappa := Real.rpow_pos_of_pos hr kappa
    exact (Real.log_lt_log_iff h3 h4).mp h2
  let Annulus (xi : ℝ) : Set Point := {z | xi ≤ dist z y ∧ dist z y < 2 * xi}
  let B_outer := ball y (2 * r_kappa)
  let B_inner := ball y r
  let Region := S ∩ (B_outer \ B_inner)
  let a := nu (S ∩ B_inner)
  let b := nu Region
  have hB_inner_sub_outer : B_inner ⊆ B_outer := by
    intro z hz
    have h : dist z y < r := hz
    have h' : r < 2 * r_kappa := by
      have h_rpos : 0 < r := hr
      have h_rkpos : 0 < r_kappa := hr_kappa_pos
      have h_rlt : r < r_kappa := hr_lt_rkappa
      linarith
    have h'' : dist z y < 2 * r_kappa := by linarith
    exact h''
  have h_union : (S ∩ B_inner) ∪ Region = S ∩ B_outer := by
    have h1 : B_outer = B_inner ∪ (B_outer \ B_inner) := by
      ext z
      simp only [Set.mem_union, Set.mem_diff]
      <;> constructor
      · intro hz
        by_cases h : z ∈ B_inner
        · exact Or.inl h
        · exact Or.inr ⟨hz, h⟩
      · rintro (h | h)
        · exact hB_inner_sub_outer h
        · exact h.1
    rw [h1, Set.inter_union_distrib_left]
    <;> rfl
  have h_sub : nu (S ∩ B_outer) ≤ a + b := by
    rw [← h_union]; exact measure_union_le _ _
  let M_diff : ENNReal := ENNReal.ofReal (outer - inner)
  have hM_diff_ne_top : M_diff ≠ ⊤ := ENNReal.ofReal_ne_top
  have h_diff_pos : 0 < outer - inner := by linarith
  have h_a_le : a ≤ ENNReal.ofReal inner := h_inner
  have h_ab_ge : ENNReal.ofReal outer ≤ a + b := le_trans h_outer h_sub
  have h_b_ge : b ≥ M_diff := by
    have h3 : ENNReal.ofReal outer ≤ ENNReal.ofReal inner + b := by
      calc ENNReal.ofReal outer
        ≤ a + b := h_ab_ge
      _ ≤ ENNReal.ofReal inner + b := by gcongr
    have h4 : ENNReal.ofReal outer - ENNReal.ofReal inner ≤ b := by
      exact tsub_le_iff_left.mpr h3
    have h5 : ENNReal.ofReal outer - ENNReal.ofReal inner = M_diff := by
      have h_inner_nonneg : 0 ≤ inner := by linarith
      have h6 : ENNReal.ofReal (outer - inner) = ENNReal.ofReal outer - ENNReal.ofReal inner :=
        ENNReal.ofReal_sub outer h_inner_nonneg
      exact h6.symm
    rw [h5] at h4
    exact h4
  set x : ℝ := (1 - kappa) * Real.log (1 / r) / Real.log 2 with hx_def
  set N : ℕ := Nat.ceil x with hN_def
  have hx_pos : 0 < x := by
    dsimp only [x]
    have h1 : 0 < 1 - kappa := by linarith
    have h2 : 0 < Real.log (1 / r) := by
      have h_ir : 1 < 1 / r := by apply one_lt_one_div <;> linarith
      exact Real.log_pos h_ir
    have h3 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  have hN_pos : 0 < N := Nat.ceil_pos.mpr hx_pos
  have h_pow_id : (2 : ℝ)^x = r ^ (kappa - 1) :=
    dyadic_pow_identity r kappa hr hr_small hkappa_pos hkappa_lt_one
  let scales : Finset ℝ := dyadicAnnulusScales r kappa N
  have h_inj : Function.Injective (fun k : ℕ => r * (2 : ℝ)^k) := by
    intro k1 k2 h
    have h' : (2 : ℝ)^k1 = (2 : ℝ)^k2 := by
      apply (mul_right_inj' (ne_of_gt hr)).mp; exact h
    by_cases hne : k1 < k2
    · have h'' : (2 : ℝ)^k1 < (2 : ℝ)^k2 := by gcongr <;> norm_num
      linarith
    · by_cases hne2 : k2 < k1
      · have h'' : (2 : ℝ)^k2 < (2 : ℝ)^k1 := by gcongr <;> norm_num
        linarith
      · have h_eq : k1 = k2 := by omega
        exact h_eq
  have h_scales_card : scales.card ≤ N + 1 := by
    have h1 : (Finset.image (fun k : ℕ => r * (2 : ℝ)^k) (Finset.range N)).card = N := by
      rw [Finset.card_image_of_injective _ h_inj]; simp
    calc scales.card
      ≤ (Finset.image (fun k : ℕ => r * (2 : ℝ)^k) (Finset.range N)).card + 1 := Finset.card_union_le _ _
    _ = N + 1 := by rw [h1] <;> ring
  have h_scales_nonempty : scales.Nonempty := by
    have h : r_kappa ∈ scales := by
      dsimp only [scales]; apply Finset.mem_union_right; exact Finset.mem_singleton_self r_kappa
    exact ⟨r_kappa, h⟩
  have h_scales_bounds : ∀ xi ∈ scales, r ≤ xi ∧ xi ≤ r_kappa := by
    intro xi hxi
    have hxi' : xi ∈ (Finset.image (fun k : ℕ => r * (2 : ℝ)^k) (Finset.range N) ∪ {r_kappa}) := by
      have h_unfold : scales = Finset.image (fun k : ℕ => r * (2 : ℝ)^k) (Finset.range N) ∪ {r_kappa} := by
        dsimp only [scales, dyadicAnnulusScales]
        <;> congr
        <;> simp [hr_kappa_def] <;> rfl
      rw [h_unfold] at hxi; exact hxi
    have hxi'' : xi ∈ Finset.image (fun k : ℕ => r * (2 : ℝ)^k) (Finset.range N) ∨ xi ∈ ({r_kappa} : Finset ℝ) := by
      have h : xi = r_kappa ∨ ∃ a < N, r * (2 : ℝ)^a = xi := by
        simpa [Finset.mem_union, Finset.mem_image, Finset.mem_range, Finset.mem_singleton] using hxi'
      rcases h with (h | h)
      · exact Or.inr (by simp [h])
      · exact Or.inl (by simpa [Finset.mem_image, Finset.mem_range] using h)
    rcases hxi'' with (hxi | hxi)
    · rcases Finset.mem_image.mp hxi with ⟨k, hk, rfl⟩
      have hk_lt_N : k < N := Finset.mem_range.mp hk
      have h_lower : r ≤ r * (2 : ℝ)^k := by
        have h2 : (1 : ℝ) ≤ (2 : ℝ) := by norm_num
        have h3 : (1 : ℝ)^k ≤ (2 : ℝ)^k := by gcongr
        have h4 : (1 : ℝ)^k = (1 : ℝ) := by simp
        nlinarith
      have h_k_le_N1 : k ≤ N - 1 := by omega
      have h3 : (2 : ℝ)^k ≤ (2 : ℝ)^(N - 1) := by
        have h_pow_mono : ∀ (m n : ℕ), m ≤ n → (2 : ℝ)^m ≤ (2 : ℝ)^n := by
          intro m n hmn; induction' hmn with n hmn ih
          · simp
          · calc (2 : ℝ)^m ≤ (2 : ℝ)^n := ih
            _ ≤ (2 : ℝ)^(n + 1) := by simp [pow_succ] <;> norm_num <;> linarith
        exact h_pow_mono k (N - 1) h_k_le_N1
      have h_ceil_lt : (N : ℝ) - 1 < x := ceil_sub_one_lt hx_pos rfl
      have h6 : ((N - 1 : ℕ) : ℝ) < x := by
        have h_eq : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by simp [hN_pos] <;> omega
        rw [h_eq]; exact h_ceil_lt
      have h7 : (2 : ℝ)^(N - 1) < (2 : ℝ)^x := by
        have h71 : (2 : ℝ)^(N - 1) = (2 : ℝ) ^ ((N - 1 : ℕ) : ℝ) := by simp [Real.rpow_natCast]
        rw [h71]; exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h6
      have h_upper : r * (2 : ℝ)^k < r_kappa := by
        calc r * (2 : ℝ)^k
          ≤ r * (2 : ℝ)^(N - 1) := by gcongr
        _ < r * (2 : ℝ)^x := by gcongr
        _ = r * r ^ (kappa - 1) := by
          have h_pow : (2 : ℝ)^x = r ^ (kappa - 1) :=
            dyadic_pow_identity r kappa hr hr_small hkappa_pos hkappa_lt_one
          rw [h_pow]
        _ = r ^ kappa := mul_rpow_kappa r kappa hr hkappa_pos
        _ = r_kappa := by simp [r_kappa]
      exact ⟨h_lower, le_of_lt h_upper⟩
    · rw [Finset.mem_singleton] at hxi; rw [hxi]; exact ⟨by linarith, by linarith⟩
  have h_cover : Region ⊆ ⋃ xi ∈ scales, S ∩ Annulus xi := by
    intro z hz
    have hz_S : z ∈ S := hz.1
    have hz_not_inner : z ∉ B_inner := hz.2.2
    have hz_ge : r ≤ dist z y := by simpa [B_inner] using not_lt.mp hz_not_inner
    have hz_lt : dist z y < 2 * r_kappa := hz.2.1
    by_cases h_case : dist z y < r_kappa
    · have hN_ge_x : (N : ℝ) ≥ x := Nat.le_ceil x
      have h2pow_ge : (2 : ℝ)^N ≥ (2 : ℝ)^x := by
        have h71 : (2 : ℝ)^N = (2 : ℝ) ^ ((N : ℝ)) := by simp [Real.rpow_natCast]
        rw [h71]; exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hN_ge_x
      have h_r2N_ge : r * (2 : ℝ)^N ≥ r_kappa := by
        calc r * (2 : ℝ)^N
          ≥ r * (2 : ℝ)^x := by gcongr
        _ = r * r ^ (kappa - 1) := by
          have h_pow : (2 : ℝ)^x = r ^ (kappa - 1) :=
            dyadic_pow_identity r kappa hr hr_small hkappa_pos hkappa_lt_one
          rw [h_pow]
        _ = r ^ kappa := mul_rpow_kappa r kappa hr hkappa_pos
        _ = r_kappa := by simp [r_kappa]
      have h_upp : dist z y < r * (2 : ℝ)^N := by linarith
      have h_exists_k := exists_dyadic_interval r (dist z y) N hr hN_pos hz_ge h_upp
      rcases h_exists_k with ⟨k, hk_lt_N, h_ge, h_lt⟩
      let xi : ℝ := r * (2 : ℝ)^k
      have hxi_in : xi ∈ scales := by
        apply Finset.mem_union_left; exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk_lt_N, rfl⟩
      have hz_ann : z ∈ Annulus xi := by
        simp only [Annulus, Set.mem_setOf_eq]
        have h_eq : 2 * xi = r * (2 : ℝ)^(k + 1) := by dsimp only [xi]; ring
        exact ⟨h_ge, by rw [h_eq]; exact h_lt⟩
      exact Set.subset_biUnion_of_mem hxi_in ⟨hz_S, hz_ann⟩
    · have hz_ge_kappa : r_kappa ≤ dist z y := by linarith
      have hz_ann : z ∈ Annulus r_kappa := by
        simp only [Annulus, Set.mem_setOf_eq]; exact ⟨hz_ge_kappa, hz_lt⟩
      have hkappa_in : r_kappa ∈ scales := by
        apply Finset.mem_union_right; exact Finset.mem_singleton_self _
      exact Set.subset_biUnion_of_mem hkappa_in ⟨hz_S, hz_ann⟩
  have h_sum_ge : ∑ xi ∈ scales, nu (S ∩ Annulus xi) ≥ b := by
    have h1 : Region ⊆ ⋃ xi ∈ scales, S ∩ Annulus xi := h_cover
    have h2 : nu Region ≤ nu (⋃ xi ∈ scales, S ∩ Annulus xi) := measure_mono h1
    have h3 : nu (⋃ xi ∈ scales, S ∩ Annulus xi) ≤ ∑ xi ∈ scales, nu (S ∩ Annulus xi) :=
      measure_biUnion_finset_le _ _
    exact le_trans h2 h3
  have h_sum_ge_Mdiff : ∑ xi ∈ scales, nu (S ∩ Annulus xi) ≥ M_diff :=
    le_trans h_b_ge h_sum_ge
  have h_pigeon := finset_pigeonhole_ennreal (fun xi => nu (S ∩ Annulus xi)) hM_diff_ne_top h_scales_nonempty h_sum_ge_Mdiff
  rcases h_pigeon with ⟨xi, hxi_scales, h_ge⟩
  have hxi_bounds : r ≤ xi ∧ xi ≤ r_kappa := h_scales_bounds xi hxi_scales
  have h_count_bound : (scales.card : ℝ) ≤ (1 / 6 : ℝ) * Real.rpow r (-eta) := by
    have h1 : (scales.card : ℝ) ≤ (N + 1 : ℝ) := by exact_mod_cast h_scales_card
    have h2 := dyadic_scale_count_bound r eta kappa C hr hr_small heta hkappa_pos hkappa_lt_one hC h_r_log_small h_r_final
    linarith
  have h_posB : 0 < (1 / 6 : ℝ) * Real.rpow r (-eta) := by
    have h : 0 < Real.rpow r (-eta) := Real.rpow_pos_of_pos hr _
    positivity
  have h_goal : M_diff / scales.card ≥ ENNReal.ofReal ((outer - inner) / ((1 / 6 : ℝ) * Real.rpow r (-eta))) := by
    have h1 : (scales.card : ENNReal) ≤ ENNReal.ofReal ((1 / 6 : ℝ) * Real.rpow r (-eta)) := by
      have h1' : (scales.card : ℝ) ≤ (1 / 6 : ℝ) * Real.rpow r (-eta) := h_count_bound
      have h2 : (scales.card : ENNReal) = ENNReal.ofReal (scales.card : ℝ) := by simp
      rw [h2]; exact ENNReal.ofReal_le_ofReal h1'
    have h_mult : M_diff / (scales.card : ENNReal) ≥ M_diff / ENNReal.ofReal ((1 / 6 : ℝ) * Real.rpow r (-eta)) := by
      exact ENNReal.div_le_div_left h1 M_diff
    have h3 : M_diff / ENNReal.ofReal ((1 / 6 : ℝ) * Real.rpow r (-eta)) =
        ENNReal.ofReal ((outer - inner) / ((1 / 6 : ℝ) * Real.rpow r (-eta))) := by
      simp only [M_diff]
      rw [ENNReal.ofReal_div_of_pos h_posB]
      <;> rfl
    rw [h3] at h_mult
    exact h_mult
  exact ⟨xi, hxi_scales, hxi_bounds.1, hxi_bounds.2, le_trans h_goal h_ge⟩

/-- Strong version: like `dyadic_annulus_pigeonhole_general`, but accepts
    a custom upper bound on the number of dyadic scales. -/
lemma dyadic_annulus_pigeonhole_strong
    (nu : Measure Point) (y : Point) (r kappa sigma eta C : ℝ)
    (outer inner card_bound_val : ℝ)
    (hr : 0 < r) (hr_small : r < 1)
    (hsigma : 0 ≤ sigma) (heta : 0 < eta)
    (hC : 1 ≤ C)
    (hkappa_pos : 0 < kappa) (hkappa_lt_one : kappa < 1)
    (S : Set Point)
    (h_outer : nu (S ∩ ball y (2 * Real.rpow r kappa)) ≥ ENNReal.ofReal outer)
    (h_inner : nu (S ∩ ball y r) ≤ ENNReal.ofReal inner)
    (h_inner_nonneg : 0 ≤ inner) (h_outer_pos : 0 < outer) (h_lt : inner < outer)
    (h_card_bound_pos : 0 < card_bound_val)
    (h_card_bound_real : ((dyadicAnnulusScales r kappa (Nat.ceil ((1 - kappa) * Real.log (1 / r) / Real.log 2))).card : ℝ) ≤ card_bound_val) :
    ∃ (xi : ℝ), xi ∈ dyadicAnnulusScales r kappa (Nat.ceil ((1 - kappa) * Real.log (1 / r) / Real.log 2)) ∧
      r ≤ xi ∧ xi ≤ Real.rpow r kappa ∧
      nu (S ∩ {z | xi ≤ dist z y ∧ dist z y < 2 * xi}) ≥
        ENNReal.ofReal ((outer - inner) / card_bound_val) := by
  set x : ℝ := (1 - kappa) * Real.log (1 / r) / Real.log 2 with hx_def
  set N : ℕ := Nat.ceil x with hN_def
  have hx_pos : 0 < x := by
    dsimp only [x]
    have h1 : 0 < 1 - kappa := by linarith
    have h2 : 0 < Real.log (1 / r) := by
      have h_ir : 1 < 1 / r := by apply one_lt_one_div <;> linarith
      exact Real.log_pos h_ir
    have h3 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  have hN_pos : 0 < N := Nat.ceil_pos.mpr hx_pos
  set r_kappa : ℝ := Real.rpow r kappa with hr_kappa_def
  have hr_kappa_pos : 0 < r_kappa := Real.rpow_pos_of_pos hr kappa
  let scales : Finset ℝ := dyadicAnnulusScales r kappa N
  let Annulus (xi : ℝ) : Set Point := {z | xi ≤ dist z y ∧ dist z y < 2 * xi}
  let B_outer := ball y (2 * r_kappa)
  let B_inner := ball y r
  let Region := S ∩ (B_outer \ B_inner)
  let a := nu (S ∩ B_inner)
  let b := nu Region
  have hB_inner_sub_outer : B_inner ⊆ B_outer := by
    intro z hz
    have h : dist z y < r := hz
    have h_rlt : r < r_kappa := by
      have hlog_r_neg : Real.log r < 0 := Real.log_neg hr hr_small
      have hlog_rkappa : Real.log (r ^ kappa) = kappa * Real.log r := by
        rw [Real.log_rpow hr] <;> ring
      have h2 : Real.log r < Real.log (r ^ kappa) := by
        rw [hlog_rkappa]; nlinarith
      have h3 : 0 < r := hr
      have h4 : 0 < r ^ kappa := Real.rpow_pos_of_pos hr kappa
      exact (Real.log_lt_log_iff h3 h4).mp h2
    have h'' : dist z y < 2 * r_kappa := by linarith
    exact h''
  have h_union : (S ∩ B_inner) ∪ Region = S ∩ B_outer := by
    have h1 : B_outer = B_inner ∪ (B_outer \ B_inner) := by
      ext z; simp only [Set.mem_union, Set.mem_diff] <;> tauto
    rw [h1, Set.inter_union_distrib_left] <;> rfl
  have h_sub : nu (S ∩ B_outer) ≤ a + b := by
    rw [← h_union]; exact measure_union_le _ _
  let M_diff : ENNReal := ENNReal.ofReal (outer - inner)
  have hM_diff_ne_top : M_diff ≠ ⊤ := ENNReal.ofReal_ne_top
  have h_diff_pos : 0 < outer - inner := by linarith
  have h_a_le : a ≤ ENNReal.ofReal inner := h_inner
  have h_ab_ge : ENNReal.ofReal outer ≤ a + b := le_trans h_outer h_sub
  have h_b_ge : b ≥ M_diff := by
    have h3 : ENNReal.ofReal outer ≤ ENNReal.ofReal inner + b := by
      calc ENNReal.ofReal outer
        ≤ a + b := h_ab_ge
      _ ≤ ENNReal.ofReal inner + b := by gcongr
    have h4 : ENNReal.ofReal outer - ENNReal.ofReal inner ≤ b := by
      exact tsub_le_iff_left.mpr h3
    have h5 : ENNReal.ofReal outer - ENNReal.ofReal inner = M_diff := by
      have h6 : ENNReal.ofReal (outer - inner) = ENNReal.ofReal outer - ENNReal.ofReal inner :=
        ENNReal.ofReal_sub outer h_inner_nonneg
      exact h6.symm
    rw [h5] at h4
    exact h4
  have h_scales_nonempty : scales.Nonempty := by
    have h : r_kappa ∈ scales := by
      dsimp only [scales]; apply Finset.mem_union_right; exact Finset.mem_singleton_self _
    exact ⟨r_kappa, h⟩
  have h_pow_id : (2 : ℝ)^x = r ^ (kappa - 1) :=
    dyadic_pow_identity r kappa hr hr_small hkappa_pos hkappa_lt_one
  have h_scales_bounds : ∀ xi ∈ scales, r ≤ xi ∧ xi ≤ r_kappa := by
    intro xi hxi
    have hxi' : xi ∈ (Finset.image (fun k : ℕ => r * (2 : ℝ)^k) (Finset.range N) ∪ {r_kappa}) := by
      have h_unfold : scales = Finset.image (fun k : ℕ => r * (2 : ℝ)^k) (Finset.range N) ∪ {r_kappa} := by
        dsimp only [scales, dyadicAnnulusScales] <;> congr <;> simp [hr_kappa_def] <;> rfl
      rw [h_unfold] at hxi; exact hxi
    have hxi'' : xi ∈ Finset.image (fun k : ℕ => r * (2 : ℝ)^k) (Finset.range N) ∨ xi ∈ ({r_kappa} : Finset ℝ) := by
      have h : xi = r_kappa ∨ ∃ a < N, r * (2 : ℝ)^a = xi := by
        simpa [Finset.mem_union, Finset.mem_image, Finset.mem_range, Finset.mem_singleton] using hxi'
      rcases h with (h | h)
      · exact Or.inr (by simp [h])
      · exact Or.inl (by simpa [Finset.mem_image, Finset.mem_range] using h)
    rcases hxi'' with (hxi | hxi)
    · rcases Finset.mem_image.mp hxi with ⟨k, hk, rfl⟩
      have hk_lt_N : k < N := Finset.mem_range.mp hk
      have h_lower : r ≤ r * (2 : ℝ)^k := by
        have h2 : (1 : ℝ) ≤ (2 : ℝ) := by norm_num
        have h3 : (1 : ℝ)^k ≤ (2 : ℝ)^k := by gcongr
        have h4 : (1 : ℝ)^k = (1 : ℝ) := by simp
        nlinarith
      have h_k_le_N1 : k ≤ N - 1 := by omega
      have h3 : (2 : ℝ)^k ≤ (2 : ℝ)^(N - 1) := by
        have h_pow_mono : ∀ (m n : ℕ), m ≤ n → (2 : ℝ)^m ≤ (2 : ℝ)^n := by
          intro m n hmn; induction' hmn with n hmn ih
          · simp
          · calc (2 : ℝ)^m ≤ (2 : ℝ)^n := ih
            _ ≤ (2 : ℝ)^(n + 1) := by simp [pow_succ] <;> norm_num <;> linarith
        exact h_pow_mono k (N - 1) h_k_le_N1
      have h_ceil_lt : (N : ℝ) - 1 < x := ceil_sub_one_lt hx_pos rfl
      have h6 : ((N - 1 : ℕ) : ℝ) < x := by
        have h_eq : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by simp [hN_pos] <;> omega
        rw [h_eq]; exact h_ceil_lt
      have h7 : (2 : ℝ)^(N - 1) < (2 : ℝ)^x := by
        have h71 : (2 : ℝ)^(N - 1) = (2 : ℝ) ^ ((N - 1 : ℕ) : ℝ) := by simp [Real.rpow_natCast]
        rw [h71]; exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) h6
      have h_upper : r * (2 : ℝ)^k < r_kappa := by
        calc r * (2 : ℝ)^k
          ≤ r * (2 : ℝ)^(N - 1) := by gcongr
        _ < r * (2 : ℝ)^x := by gcongr
        _ = r * r ^ (kappa - 1) := by
          have h_pow : (2 : ℝ)^x = r ^ (kappa - 1) :=
            dyadic_pow_identity r kappa hr hr_small hkappa_pos hkappa_lt_one
          rw [h_pow]
        _ = r ^ kappa := mul_rpow_kappa r kappa hr hkappa_pos
        _ = r_kappa := by simp [r_kappa]
      exact ⟨h_lower, le_of_lt h_upper⟩
    · rw [Finset.mem_singleton] at hxi; rw [hxi]
      have h_r_le_kappa : r ≤ r_kappa := by
        have hlog_r_neg : Real.log r < 0 := Real.log_neg hr hr_small
        have h2 : Real.log r ≤ Real.log (r ^ kappa) := by
          rw [Real.log_rpow hr]; nlinarith
        have h3 : 0 < r := hr
        have h4 : 0 < r ^ kappa := Real.rpow_pos_of_pos hr kappa
        exact (Real.log_le_log_iff h3 h4).mp h2
      exact ⟨h_r_le_kappa, by linarith⟩
  have h_cover : Region ⊆ ⋃ xi ∈ scales, S ∩ Annulus xi := by
    intro z hz
    have hzS : z ∈ S := hz.1
    have hz1 : z ∈ B_outer := hz.2.1
    have hz2 : z ∉ B_inner := hz.2.2
    have h_dist1 : r ≤ dist z y := by simpa [B_inner] using hz2
    have h_dist2 : dist z y < 2 * r_kappa := by simpa [B_outer] using hz1
    by_cases h : dist z y < r_kappa
    · have h_upp : dist z y < r * (2 : ℝ)^N := by
        have hN_ge_x : (N : ℝ) ≥ x := Nat.le_ceil x
        have h_r2N_ge : r * (2 : ℝ)^N ≥ r_kappa := by
          have h_pow_le : (2 : ℝ)^x ≤ (2 : ℝ)^N := by
            have h71 : (2 : ℝ)^N = (2 : ℝ) ^ ((N : ℝ)) := by simp [Real.rpow_natCast]
            rw [h71]
            exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hN_ge_x
          calc r * (2 : ℝ)^N
            ≥ r * (2 : ℝ)^x := by gcongr
          _ = r * r ^ (kappa - 1) := by
            have h_pow : (2 : ℝ)^x = r ^ (kappa - 1) :=
              dyadic_pow_identity r kappa hr hr_small hkappa_pos hkappa_lt_one
            rw [h_pow]
          _ = r ^ kappa := mul_rpow_kappa r kappa hr hkappa_pos
          _ = r_kappa := by simp [r_kappa]
        linarith
      rcases exists_dyadic_interval r (dist z y) N hr hN_pos h_dist1 h_upp with ⟨k, hk_lt_N, h_ge, h_lt⟩
      let xi : ℝ := r * (2 : ℝ)^k
      have hxi_in : xi ∈ scales := by
        apply Finset.mem_union_left; exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr hk_lt_N, rfl⟩
      have hz_ann : z ∈ Annulus xi := by
        simp only [Annulus, Set.mem_setOf_eq]
        have h_eq : 2 * xi = r * (2 : ℝ)^(k + 1) := by dsimp only [xi]; ring
        exact ⟨h_ge, by rw [h_eq]; exact h_lt⟩
      exact Set.subset_biUnion_of_mem hxi_in ⟨hzS, hz_ann⟩
    · have hz_ge_kappa : r_kappa ≤ dist z y := by linarith
      have hz_ann : z ∈ Annulus r_kappa := by
        simp only [Annulus, Set.mem_setOf_eq]; exact ⟨hz_ge_kappa, h_dist2⟩
      have hkappa_in : r_kappa ∈ scales := by
        apply Finset.mem_union_right; exact Finset.mem_singleton_self _
      exact Set.subset_biUnion_of_mem hkappa_in ⟨hzS, hz_ann⟩
  have h_sum_ge : ∑ xi ∈ scales, nu (S ∩ Annulus xi) ≥ b := by
    have h1 : Region ⊆ ⋃ xi ∈ scales, S ∩ Annulus xi := h_cover
    have h2 : nu Region ≤ nu (⋃ xi ∈ scales, S ∩ Annulus xi) := measure_mono h1
    have h3 : nu (⋃ xi ∈ scales, S ∩ Annulus xi) ≤ ∑ xi ∈ scales, nu (S ∩ Annulus xi) :=
      measure_biUnion_finset_le _ _
    exact le_trans h2 h3
  have h_sum_ge_Mdiff : ∑ xi ∈ scales, nu (S ∩ Annulus xi) ≥ M_diff :=
    le_trans h_b_ge h_sum_ge
  rcases finset_pigeonhole_ennreal (fun xi => nu (S ∩ Annulus xi)) hM_diff_ne_top h_scales_nonempty h_sum_ge_Mdiff
    with ⟨xi, hxi_scales, h_ge⟩
  have hxi_bounds : r ≤ xi ∧ xi ≤ r_kappa := h_scales_bounds xi hxi_scales
  have h_goal : M_diff / (scales.card : ENNReal) ≥ ENNReal.ofReal ((outer - inner) / card_bound_val) := by
    have h1 : (scales.card : ENNReal) ≤ ENNReal.ofReal card_bound_val := by
      rw [show (scales.card : ENNReal) = ENNReal.ofReal (scales.card : ℝ) by simp]
      exact ENNReal.ofReal_le_ofReal h_card_bound_real
    have h2 : M_diff / (scales.card : ENNReal) ≥ M_diff / ENNReal.ofReal card_bound_val :=
      ENNReal.div_le_div_left h1 M_diff
    have h3 : M_diff / ENNReal.ofReal card_bound_val =
        ENNReal.ofReal ((outer - inner) / card_bound_val) := by
      simp only [M_diff]
      rw [ENNReal.ofReal_div_of_pos h_card_bound_pos] <;> rfl
    rw [h3] at h2
    exact h2
  exact ⟨xi, hxi_scales, hxi_bounds.1, hxi_bounds.2, le_trans h_goal h_ge⟩

end RadialBootstrapping

end
