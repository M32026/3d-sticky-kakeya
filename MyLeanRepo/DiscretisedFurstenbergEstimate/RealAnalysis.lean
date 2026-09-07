module

/-
  RealAnalysis.lean

  Real-analysis lemmas for parameter bookkeeping in the discretised
  Furstenberg estimate.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

@[expose] public section

noncomputable section

open scoped ENNReal NNReal

namespace DirecretisedFurstenbergEstimate.RealAnalysis

-- ======================================================================
-- 1. Dyadic number approximation
-- ======================================================================

/-- For every `0 < δ ≤ 1`, there exists `n : ℕ` such that
`2^{-n} ≤ δ < 2 * 2^{-n}`. -/
lemma exists_dyadic_approx (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ (n : ℕ), (1 / 2 : ℝ) ^ n ≤ δ ∧ δ < 2 * (1 / 2 : ℝ) ^ n := by
  have h_main : ∃ (n : ℕ), (1 / 2 : ℝ) ^ n ≤ δ := by
    have h : ∃ (n : ℕ), (1 / 2 : ℝ) ^ n < δ :=
      exists_pow_lt_of_lt_one hδ (by norm_num)
    rcases h with ⟨n, hn⟩
    exact ⟨n, by linarith⟩
  let n := Nat.find h_main
  have hn : (1 / 2 : ℝ) ^ n ≤ δ := Nat.find_spec h_main
  by_cases h0 : n = 0
  · have hδeq : δ = 1 := by
      have h1 : (1 / 2 : ℝ) ^ n ≤ δ := hn
      rw [h0] at h1
      norm_num at h1
      <;> linarith
    rw [hδeq]
    exact ⟨0, by norm_num, by norm_num⟩
  · have hpos : 0 < n := Nat.pos_of_ne_zero h0
    have h_prev : ¬(1 / 2 : ℝ) ^ (n - 1) ≤ δ :=
      Nat.find_min h_main (Nat.sub_lt hpos (by norm_num))
    have h_prev' : δ < (1 / 2 : ℝ) ^ (n - 1) := by linarith
    have h_eq : n = (n - 1) + 1 := by omega
    have h_rec : (1 / 2 : ℝ) ^ (n - 1) = 2 * (1 / 2 : ℝ) ^ n := by
      rw [h_eq]
      simp [pow_succ]
      <;> ring
    rw [h_rec] at h_prev'
    exact ⟨n, hn, h_prev'⟩

-- ======================================================================
-- 2. Real.rpow algebra
-- ======================================================================

/-- For `0 < δ < 1` and `a > 0`, we have `δ^{-a} > 1`. -/
lemma rpow_neg_gt_one {δ a : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (ha : 0 < a) :
    1 < δ ^ (-a) := by
  have h1 : 1 < δ⁻¹ := by
    have h4 : 1 / δ > 1 := by
      calc 1 / δ > 1 / 1 := by gcongr
        _ = 1 := by norm_num
    have h5 : δ⁻¹ = 1 / δ := by simp
    rw [h5]; exact h4
  have h7 : δ ^ (-a) = (δ ^ a)⁻¹ := Real.rpow_neg (by linarith) a
  have h8 : (δ⁻¹) ^ a = (δ ^ a)⁻¹ := Real.inv_rpow (by linarith) a
  have h6 : δ ^ (-a) = (δ⁻¹) ^ a := by rw [h7, h8]
  rw [h6]
  have h9 : (1 : ℝ) < δ⁻¹ := h1
  have h10 : (1 : ℝ) ^ a < (δ⁻¹) ^ a := Real.rpow_lt_rpow (by linarith) h9 ha
  simpa using h10

/-- `δ^{-a} * δ^{-b} = δ^{-(a+b)}`. -/
lemma rpow_neg_mul {δ a b : ℝ} (hδ : 0 < δ) :
    δ ^ (-a) * δ ^ (-b) = δ ^ (-(a + b)) := by
  rw [← Real.rpow_add hδ]
  <;> ring_nf

/-- `(δ^{-a})^b = δ^{-a*b}` for `b ≥ 0`. -/
lemma rpow_neg_pow {δ a b : ℝ} (hδ : 0 < δ) (hb : 0 ≤ b) :
    (δ ^ (-a)) ^ b = δ ^ (-(a * b)) := by
  have hnonneg : 0 ≤ δ := by linarith
  rw [← Real.rpow_mul hnonneg]
  <;> ring_nf

-- ======================================================================
-- 3. Logarithmic loss absorption
-- ======================================================================

/-- For any real `C` and `ε > 0`, `(log(1/δ))^C ≤ δ^{-ε}` for all
sufficiently small `δ > 0`. -/
lemma log_pow_le_rpow_neg (C ε : ℝ) (hε : 0 < ε) :
    ∃ (δ₀ : ℝ), 0 < δ₀ ∧ ∀ (δ : ℝ), 0 < δ → δ < δ₀ →
      (Real.log (1 / δ)) ^ C ≤ δ ^ (-ε) := by
  by_cases hC : C ≤ 0
  · -- C ≤ 0: need log(1/δ) ≥ 1, then (log(1/δ))^C ≤ 1 ≤ δ^{-ε}
    let δ₀ := Real.exp (-1)
    have hδ₀_pos : 0 < δ₀ := Real.exp_pos _
    refine ⟨δ₀, hδ₀_pos, fun δ hδ_pos hδ_lt => ?_⟩
    have hx_gt_one : 1 < Real.log (1 / δ) := by
      have h1 : 1 / δ > 1 / δ₀ := by
        apply one_div_lt_one_div_of_lt <;> linarith
      have h2 : Real.log (1 / δ₀) = 1 := by
        simp [δ₀, Real.log_exp] <;> ring
      have h3 : Real.log (1 / δ₀) < Real.log (1 / δ) := Real.log_lt_log (by positivity) h1
      rw [h2] at h3
      exact h3
    have h3 : (Real.log (1 / δ)) ^ C ≤ 1 := by
      have h4 : 1 ≤ Real.log (1 / δ) := by linarith
      have h5 : (Real.log (1 / δ)) ^ C ≤ (Real.log (1 / δ)) ^ (0 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le h4 hC
      simpa using h5
    have h9 : 1 ≤ δ ^ (-ε) := by
      have h10 : 0 < δ := hδ_pos
      have h11 : δ < 1 := by
        have h111 : δ₀ < 1 := by
          simp [δ₀, Real.exp_lt_one_iff]
          <;> linarith
        linarith
      have h12 : 1 < δ⁻¹ := by
        have h13 : 1 / δ > 1 := by apply one_lt_one_div <;> linarith
        have h14 : δ⁻¹ = 1 / δ := by simp
        rw [h14]; exact h13
      have h15 : (1 : ℝ) ^ ε < (δ⁻¹) ^ ε := Real.rpow_lt_rpow (by linarith) h12 hε
      have h15' : (1 : ℝ) < (δ⁻¹) ^ ε := by
        have h16 : (1 : ℝ) ^ ε = (1 : ℝ) := by simp
        rw [h16] at h15
        exact h15
      have h16 : δ ^ (-ε) = (δ⁻¹) ^ ε := by
        rw [Real.rpow_neg (by linarith) ε, Real.inv_rpow (by linarith) ε]
      rw [h16]
      exact le_of_lt h15'
    linarith
  · -- C > 0: elementary proof using log x ≤ 2 * sqrt x
    have hC_pos : 0 < C := by linarith
    set K : ℝ := (2 * C / ε) ^ 2 with hK_def
    have hK_nonneg : 0 ≤ K := by positivity
    set x₀ : ℝ := max 1 K with hx₀_def
    let δ₀ := Real.exp (-x₀)
    have hδ₀_pos : 0 < δ₀ := Real.exp_pos _
    refine ⟨δ₀, hδ₀_pos, fun δ hδ_pos hδ_lt => ?_⟩
    set x : ℝ := Real.log (1 / δ) with hx_def
    have hx_gt : x₀ ≤ x := by
      have h1 : 1 / δ₀ < 1 / δ := by
        apply one_div_lt_one_div_of_lt <;> linarith
      have h2 : Real.log (1 / δ₀) ≤ Real.log (1 / δ) := Real.log_le_log (by positivity) (by linarith)
      have h3 : Real.log (1 / δ₀) = x₀ := by
        simp [δ₀, Real.log_exp] <;> ring
      linarith
    have hx1 : 1 ≤ x := by
      have h4 : 1 ≤ x₀ := by simp [hx₀_def] <;> linarith
      linarith
    have hxK : K ≤ x := by
      have h4 : K ≤ x₀ := by simp [hx₀_def] <;> linarith
      linarith
    -- log x ≤ 2 * sqrt x for x ≥ 1
    have h_log1 : Real.log x ≤ 2 * Real.sqrt x := by
      have h5 : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 :=
        Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr (by linarith))
      have h6 : Real.log (Real.sqrt x) = (1 / 2 : ℝ) * Real.log x := by
        rw [Real.sqrt_eq_rpow, Real.log_rpow (by linarith)] <;> ring
      rw [h6] at h5
      linarith
    have h_sqrt_eq : x ^ (1 / 2 : ℝ) = Real.sqrt x := by
      rw [Real.sqrt_eq_rpow]
    have h_Clog : C * Real.log x ≤ ε * x := by
      have h7 : C * Real.log x ≤ C * (2 * Real.sqrt x) := by
        exact mul_le_mul_of_nonneg_left h_log1 (by linarith)
      have h7' : C * (2 * Real.sqrt x) = 2 * C * Real.sqrt x := by ring
      have h8 : 2 * C / ε ≤ Real.sqrt x := by
        have h9 : (2 * C / ε) ^ 2 ≤ x := by simpa [hK_def] using hxK
        have h10 : 0 ≤ 2 * C / ε := by positivity
        have h11 : Real.sqrt ((2 * C / ε) ^ 2) ≤ Real.sqrt x := Real.sqrt_le_sqrt h9
        have h12 : Real.sqrt ((2 * C / ε) ^ 2) = 2 * C / ε := by
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg h10]
        rw [h12] at h11
        exact h11
      have h9 : 2 * C * Real.sqrt x ≤ ε * x := by
        have h10 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
        have h11 : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt (by linarith)
        have h12 : 2 * C * Real.sqrt x = ε * (2 * C / ε) * Real.sqrt x := by field_simp [hε.ne'] <;> ring
        rw [h12]
        have h13 : ε * (2 * C / ε) * Real.sqrt x ≤ ε * (Real.sqrt x) * (Real.sqrt x) := by gcongr
        have h14 : ε * (Real.sqrt x) * (Real.sqrt x) = ε * x := by
          have h15 : (Real.sqrt x) ^ 2 = x := h11
          have h16 : ε * (Real.sqrt x) * (Real.sqrt x) = ε * ((Real.sqrt x) ^ 2) := by ring
          rw [h16, h15] <;> ring
        rw [h14] at h13
        exact h13
      linarith
    have h_posx : 0 < x := by linarith
    have h17 : Real.log (x ^ C) = C * Real.log x := by
      rw [Real.log_rpow (by positivity)] <;> ring
    have h18 : x ^ C ≤ Real.exp (ε * x) := by
      have h19 : Real.log (x ^ C) ≤ ε * x := by
        rw [h17] <;> exact h_Clog
      have h20 : x ^ C = Real.exp (Real.log (x ^ C)) := by
        rw [Real.exp_log (by positivity)]
      rw [h20]
      exact Real.exp_le_exp.mpr h19
    have h21 : Real.exp (ε * x) = δ ^ (-ε) := by
      have h22 : x = Real.log (1 / δ) := rfl
      rw [h22]
      have h23 : Real.exp (ε * Real.log (1 / δ)) = (1 / δ) ^ ε := by
        rw [← Real.exp_log (show 0 < (1 / δ) ^ ε by positivity)]
        rw [Real.log_rpow (by positivity)] <;> ring
      rw [h23]
      have h24 : (1 / δ) ^ ε = δ ^ (-ε) := by
        have h25 : (1 / δ) ^ ε = (δ⁻¹) ^ ε := by ring_nf
        rw [h25, Real.inv_rpow (by linarith) ε, ← Real.rpow_neg (by linarith) ε]
        <;> ring
      exact h24
    rw [h21] at h18
    exact h18

/-- For any `C > 0`, `ε > 0`, and `a : ℝ`, we have
`C * δ^{-a} ≤ δ^{-a-ε}` for all sufficiently small `δ > 0`. -/
lemma constant_absorption (C ε a : ℝ) (hC : 0 < C) (hε : 0 < ε) :
    ∃ (δ₀ : ℝ), 0 < δ₀ ∧ ∀ (δ : ℝ), 0 < δ → δ < δ₀ →
      C * δ ^ (-a) ≤ δ ^ (-(a + ε)) := by
  let δ₀ := C ^ (-1 / ε)
  have hδ₀_pos : 0 < δ₀ := Real.rpow_pos_of_pos hC _
  refine ⟨δ₀, hδ₀_pos, fun δ hδ_pos hδ_lt => ?_⟩
  have h4 : δ₀ ^ ε = C⁻¹ := by
    dsimp only [δ₀]
    have hC_nonneg : 0 ≤ C := by linarith [hC]
    have h5 : (C ^ (-1 / ε)) ^ ε = C ^ ((-1 / ε) * ε) :=
      (Real.rpow_mul hC_nonneg (-1 / ε) ε).symm
    rw [h5]
    have h6 : (-1 / ε) * ε = -1 := by field_simp [hε.ne'] <;> ring
    rw [h6]
    have h7 : C ^ (-1 : ℝ) = C⁻¹ := by
      rw [Real.rpow_neg_one]
      <;> ring
    rw [h7]
  have h1 : δ ^ ε < δ₀ ^ ε := Real.rpow_lt_rpow (by linarith) hδ_lt hε
  rw [h4] at h1
  have hpos1 : 0 < δ ^ ε := Real.rpow_pos_of_pos hδ_pos _
  have h5 : C ≤ (δ ^ ε)⁻¹ := by
    have h6 : δ ^ ε < C⁻¹ := h1
    have h7 : (C⁻¹)⁻¹ < (δ ^ ε)⁻¹ := by
      gcongr
      <;> positivity
    have h8 : (C⁻¹)⁻¹ = C := by
      field_simp [hC.ne']
    rw [h8] at h7
    exact h7.le
  have h9 : (δ ^ ε)⁻¹ = δ ^ (-ε) := by
    rw [Real.rpow_neg (by linarith) ε] <;> ring
  rw [h9] at h5
  have hpos2 : 0 < δ ^ (-a) := Real.rpow_pos_of_pos hδ_pos _
  calc
    C * δ ^ (-a) ≤ δ ^ (-ε) * δ ^ (-a) := by gcongr
    _ = δ ^ (-(a + ε)) := by
      rw [← Real.rpow_add hδ_pos] <;> ring_nf

-- ======================================================================
-- 4. Compact uniformity
-- ======================================================================

/-- If every point of a compact set `K` has an open neighborhood on which
`f` is bounded below by a positive constant, then `f` has a uniform positive
lower bound on `K`. -/
lemma compact_uniform_lower_bound {X : Type*} [TopologicalSpace X]
    {f : X → ℝ} {K : Set X} (hK : IsCompact K)
    (h : ∀ x ∈ K, ∃ (ε_x : ℝ), 0 < ε_x ∧
      ∃ (V : Set X), IsOpen V ∧ x ∈ V ∧ (∀ y ∈ V, ε_x ≤ f y)) :
    ∃ (ε₀ : ℝ), 0 < ε₀ ∧ ∀ x ∈ K, ε₀ ≤ f x := by
  classical
  by_cases hK_empty : K = ∅
  · subst hK_empty
    exact ⟨1, by norm_num, fun x hx => by simpa using hx⟩
  · choose ε_x hε_pos V hV_open hxV hV_bound using
      fun (x : K) => h x.val x.property
    have hcover : K ⊆ ⋃ (x : K), V x := by
      intro y hy
      let z : K := ⟨y, hy⟩
      have h5 : y ∈ V z := hxV z
      exact Set.mem_iUnion.mpr ⟨z, h5⟩
    rcases hK.elim_finite_subcover (fun (x : K) => V x)
      (fun x => hV_open x) hcover with ⟨t, htcover⟩
    have ht_nonempty : t.Nonempty := by
      by_contra h2
      have h3 : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp h2
      rw [h3] at htcover
      have h4 : K ⊆ (∅ : Set X) := by simpa using htcover
      have h5 : K = ∅ := by simpa using h4
      exact hK_empty h5
    let S : Finset ℝ := t.image ε_x
    have hS_nonempty : S.Nonempty := Finset.Nonempty.image ht_nonempty ε_x
    let ε₀ : ℝ := Finset.min' S hS_nonempty
    have hε₀_pos : 0 < ε₀ := by
      have h9 : ∀ r ∈ S, 0 < r := by
        intro r hr
        rcases Finset.mem_image.mp hr with ⟨x, hxt, h_eq⟩
        have h10 : r = ε_x x := h_eq.symm
        rw [h10]
        exact hε_pos x
      exact h9 ε₀ (Finset.min'_mem S hS_nonempty)
    have hε₀_le : ∀ (x : K), x ∈ t → ε₀ ≤ ε_x x := by
      intro x hxt
      have h10 : ε_x x ∈ S := Finset.mem_image.mpr ⟨x, hxt, rfl⟩
      exact Finset.min'_le S (ε_x x) h10
    refine ⟨ε₀, hε₀_pos, fun y hy => ?_⟩
    have h : y ∈ ⋃ (x : K) (_ : x ∈ t), V x := htcover hy
    have hcov' : ∃ (x : K), x ∈ t ∧ y ∈ V x := by
      simpa using h
    rcases hcov' with ⟨x, hxt, hyV⟩
    have h6 : ε₀ ≤ ε_x x := hε₀_le x hxt
    have h7 : ε_x x ≤ f y := hV_bound x y hyV
    linarith

-- ======================================================================
-- 5. IsDeltaSSet parameter adjustment
-- ======================================================================

section DeltaSAdjustment

variable {X : Type*} [PseudoMetricSpace X] {δ s C : ℝ} {P : Set X}

/-- If `C ≥ 1` and `0 ≤ s' ≤ s`, then a `(δ, s, C)`-set is also a
`(δ, s', C)`-set. -/
lemma IsDeltaSSet.of_smaller_exponent (h : IsDeltaSSet δ s C P)
    (hC : 1 ≤ C) (s' : ℝ) (hs' : 0 ≤ s') (h_le : s' ≤ s) :
    IsDeltaSSet δ s' C P := by
  rcases h with ⟨hP_nonempty, hδ_pos, hC_pos, hs_nonneg, h_main⟩
  refine ⟨hP_nonempty, hδ_pos, hC_pos, hs', fun x r hr => ?_⟩
  by_cases h1 : r ≤ 1
  · -- r ≤ 1: smaller exponent gives larger rpow
    have h2 : 0 ≤ r := by linarith [hδ_pos]
    have h_real : r ^ s ≤ r ^ s' := by
      have h4 : r ^ s = r ^ s' * r ^ (s - s') := by
        rw [← Real.rpow_add (show 0 < r by linarith)] <;> ring_nf
      rw [h4]
      have h5 : r ^ (s - s') ≤ 1 := Real.rpow_le_one h2 (by linarith) (by linarith)
      have h6 : 0 ≤ r ^ s' := by positivity
      nlinarith
    have h3 : (ENNReal.ofReal r) ^ s ≤ (ENNReal.ofReal r) ^ s' := by
      rw [ENNReal.ofReal_rpow_of_nonneg h2 (by linarith),
          ENNReal.ofReal_rpow_of_nonneg h2 (by linarith)]
      have h_pos_s : 0 ≤ r ^ s := by positivity
      have h_pos_s' : 0 ≤ r ^ s' := by positivity
      have h_enn : ENNReal.ofReal (r ^ s) ≤ ENNReal.ofReal (r ^ s') := by
        gcongr
      exact h_enn
    have h4 : ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
          Metric.externalCoveringNumber δ.toNNReal P ≤
        ENNReal.ofReal C * (ENNReal.ofReal r) ^ s' *
          Metric.externalCoveringNumber δ.toNNReal P := by gcongr
    exact le_trans (h_main x r hr) h4
  · -- r > 1: use trivial bound covering(P ∩ B) ≤ covering(P) ≤ C * r^s' * covering(P)
    have h1' : 1 < r := by linarith
    have h2 : 0 ≤ r := by linarith
    have hmono : (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) : ENNReal) ≤
        (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by
      have h_inc : P ∩ Metric.closedBall x r ⊆ P := by
        exact Set.inter_subset_left
      have h : Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) ≤
          Metric.externalCoveringNumber δ.toNNReal P :=
        Metric.externalCoveringNumber_mono_set h_inc
      exact_mod_cast h
    have h3 : (1 : ENNReal) ≤ ENNReal.ofReal C := by
      have h31 : (1 : ℝ) ≤ C := hC
      have h32 : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal C := by
        simpa [ENNReal.ofReal_le_ofReal_iff] using h31
      simpa using h32
    have h41 : 1 ≤ r ^ s' := Real.one_le_rpow (by linarith) (by linarith)
    have h4 : (1 : ENNReal) ≤ (ENNReal.ofReal r) ^ s' := by
      have h42 : ENNReal.ofReal (r ^ s') = (ENNReal.ofReal r) ^ s' :=
        (ENNReal.ofReal_rpow_of_nonneg h2 (by linarith)).symm
      rw [← h42]
      have h43 : (1 : ℝ) ≤ r ^ s' := h41
      have h44 : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal (r ^ s') := by
        simpa [ENNReal.ofReal_le_ofReal_iff] using h43
      simpa using h44
    have h6 : (1 : ENNReal) ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s' := by
      calc (1 : ENNReal)
          = (1 : ENNReal) * (1 : ENNReal) := by simp
        _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s' := by gcongr
    have h_goal : (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) ≤
        ENNReal.ofReal C * (ENNReal.ofReal r) ^ s' *
          (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by
      calc
        (Metric.externalCoveringNumber δ.toNNReal P : ENNReal)
          = (1 : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by simp
        _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s' *
              (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by gcongr
    exact le_trans hmono h_goal

end DeltaSAdjustment

-- ======================================================================
-- 6. ENNReal / Real conversion for rpow
-- ======================================================================

section ENNRealConversion

/-- For `δ > 0` and real `a`,
`ENNReal.ofReal (δ^a) = (ENNReal.ofReal δ)^a`. -/
lemma ofReal_rpow {δ a : ℝ} (hδ : 0 < δ) :
    ENNReal.ofReal (δ ^ a) = (ENNReal.ofReal δ) ^ a :=
  (ENNReal.ofReal_rpow_of_pos hδ).symm

/-- For `δ > 0`, `a, b : ℝ`,
`ofReal(δ^{-a}) * ofReal(δ^{-b}) = ofReal(δ^{-(a+b)})`. -/
lemma ofReal_rpow_neg_mul {δ a b : ℝ} (hδ : 0 < δ) :
    ENNReal.ofReal (δ ^ (-a)) * ENNReal.ofReal (δ ^ (-b)) =
    ENNReal.ofReal (δ ^ (-(a + b))) := by
  have h1 : 0 ≤ δ ^ (-a) := by positivity
  have h2 : 0 ≤ δ ^ (-b) := by positivity
  have h3 : δ ^ (-a) * δ ^ (-b) = δ ^ (-(a + b)) := by
    rw [← Real.rpow_add hδ] <;> ring_nf
  rw [← ENNReal.ofReal_mul h1, h3]

/-- For `δ > 0`, `a : ℝ`, `n : ℕ`,
`ofReal(δ^{-a})^n = ofReal(δ^{-a*n})`. -/
lemma ofReal_rpow_neg_pow {δ a : ℝ} {n : ℕ} (hδ : 0 < δ) :
    (ENNReal.ofReal (δ ^ (-a))) ^ n =
    ENNReal.ofReal (δ ^ (-(a * (n : ℝ)))) := by
  have h_pos : 0 ≤ δ ^ (-a) := by positivity
  have h1 : (ENNReal.ofReal (δ ^ (-a))) ^ n =
      ENNReal.ofReal ((δ ^ (-a)) ^ n) := by
    rw [← ENNReal.ofReal_pow h_pos n]
  rw [h1]
  congr 1
  have h21 : (δ ^ (-a)) ^ n = (δ ^ (-a)) ^ (n : ℝ) := by exact Eq.symm (Real.rpow_natCast (δ ^ (-a)) n)
  rw [h21]
  have hnonneg2 : 0 ≤ δ := by linarith
  have h22 : (δ ^ (-a)) ^ (n : ℝ) = δ ^ ((-a) * (n : ℝ)) :=
    (Real.rpow_mul hnonneg2 (-a) (n : ℝ)).symm
  rw [h22]
  <;> ring_nf

end ENNRealConversion

-- ======================================================================
-- 7. AM-GM inequality for NNReal / ENNReal
-- ======================================================================

section AMGM

/-- AM-GM for two `NNReal` values: `4ab ≤ (a+b)^2`. -/
lemma nnreal_am_gm (a b : NNReal) : 4 * a * b ≤ (a + b)^2 := by
  exact_mod_cast show (4 : ℝ) * (a : ℝ) * (b : ℝ) ≤ ((a : ℝ) + (b : ℝ))^2 by
    nlinarith [sq_nonneg ((a : ℝ) - (b : ℝ))]

/-- AM-GM for two `ENNReal` values: `4ab ≤ (a+b)^2`.
Equivalently, the geometric mean is at most the arithmetic mean. -/
lemma ennreal_am_gm (a b : ENNReal) : 4 * a * b ≤ (a + b)^2 := by
  by_cases ha : a = ⊤
  · rw [ha]
    by_cases hb : b = 0
    · rw [hb] <;> simp
    · have hb' : b ≠ 0 := hb
      simp [hb', ENNReal.top_mul] <;> exact le_top
  · by_cases hb : b = ⊤
    · rw [hb]
      by_cases ha' : a = 0
      · rw [ha'] <;> simp
      · have ha'' : a ≠ 0 := ha'
        simp [ha'', ENNReal.top_mul] <;> exact le_top
    · -- Both finite
      have h_a : ∃ (a' : NNReal), (a' : ENNReal) = a := by
        exact Option.ne_none_iff_exists.mp ha
      have h_b : ∃ (b' : NNReal), (b' : ENNReal) = b := by
        exact Option.ne_none_iff_exists.mp hb
      rcases h_a with ⟨a', rfl⟩
      rcases h_b with ⟨b', rfl⟩
      have h_main : (4 : ENNReal) * (a' : ENNReal) * (b' : ENNReal) ≤
          ((a' : ENNReal) + (b' : ENNReal))^2 := by
        exact_mod_cast nnreal_am_gm a' b'
      exact h_main

/-- Geometric-mean form of AM-GM for `ENNReal`:
`a * b ≤ ((a + b) / 2)^2` when `a + b ≠ ⊤`. -/
lemma ennreal_geometric_mean_le (a b : ENNReal) (h : a + b ≠ ⊤) :
    a * b ≤ ((a + b) / 2)^2 := by
  have h1 : a ≠ ⊤ := by
    intro h2; rw [h2] at h; simp at h <;> tauto
  have h2 : b ≠ ⊤ := by
    intro h3; rw [h3] at h; simp at h <;> tauto
  have h3 : (4 : ENNReal) * a * b ≤ (a + b)^2 := ennreal_am_gm a b
  have h4 : ((a + b) / 2)^2 = (a + b)^2 / 4 := by
    have h5 : ((a + b) / 2) = (a + b) * (2 : ENNReal)⁻¹ := by
      simp [div_eq_mul_inv]
    rw [h5]
    have h6 : ((a + b) * (2 : ENNReal)⁻¹)^2 = (a + b)^2 * ((2 : ENNReal)⁻¹)^2 := by
      rw [mul_pow]
    rw [h6]
    have h7 : ((2 : ENNReal)⁻¹)^2 = (4 : ENNReal)⁻¹ := by
      have h71 : ((2 : NNReal)⁻¹ * (2 : NNReal)⁻¹ : ENNReal) = ((4 : NNReal)⁻¹ : ENNReal) := by
        have h : (2 : NNReal)⁻¹ * (2 : NNReal)⁻¹ = (4 : NNReal)⁻¹ := by
          ext <;> simp <;> field_simp <;> norm_num
        exact_mod_cast h
      simpa [pow_two] using h71
    rw [h7]
    <;> rfl
  rw [h4]
  have h8 : a * b ≤ (a + b)^2 / 4 := by
    have h9 : (4 : ENNReal) * (a * b) ≤ (a + b)^2 := by simpa [mul_assoc] using h3
    have h10 : a * b ≤ (a + b)^2 / 4 := by
      calc
        a * b
          = (4 : ENNReal) * (a * b) / 4 := by
            have h_div4 : (4 : ENNReal) * (a * b) / 4 = (4 : ENNReal) * (a * b) * (4 : ENNReal)⁻¹ := by
              simp [div_eq_mul_inv]
            rw [h_div4]
            have h_cancel : (4 : ENNReal) * (a * b) * (4 : ENNReal)⁻¹ = a * b := by
              by_cases h_ab : a * b = ⊤
              · rw [h_ab] <;> simp
              · have h4_ne_zero : (4 : ENNReal) ≠ 0 := by norm_num
                have h4_ne_top : (4 : ENNReal) ≠ ⊤ := by norm_num
                have h : (4 : ENNReal) * (a * b) * (4 : ENNReal)⁻¹ =
                    (4 : ENNReal) * (4 : ENNReal)⁻¹ * (a * b) := by
                  simp [mul_assoc, mul_comm, mul_left_comm]
                  <;> ac_rfl
                rw [h, ENNReal.mul_inv_cancel h4_ne_zero h4_ne_top, one_mul]
            exact h_cancel.symm
        _ ≤ (a + b)^2 / 4 := by gcongr
    exact h10
  exact h8

end AMGM

-- ======================================================================
-- 8. Finset product of powers
-- ======================================================================

section ProductPowers

/-- Product of powers equals power of sum, for positive real base. -/
lemma finset_prod_real_rpow {ι : Type*} {s : Finset ι} {x : ℝ} (hx : 0 < x)
    {a : ι → ℝ} : (∏ i ∈ s, x ^ a i) = x ^ (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, ← Real.rpow_add hx]
    <;> ring

/-- Product of powers equals power of sum, for `ENNReal` base. -/
lemma finset_prod_ennreal_rpow {ι : Type*} {s : Finset ι} {x : ENNReal}
    (hx_ne_zero : x ≠ 0) (hx_ne_top : x ≠ ⊤) {a : ι → ℝ} :
    (∏ i ∈ s, x ^ a i) = x ^ (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, ih]
    have h_rpow : x ^ (a i + ∑ j ∈ s, a j) = x ^ (a i) * x ^ (∑ j ∈ s, a j) :=
      ENNReal.rpow_add (a i) (∑ j ∈ s, a j) hx_ne_zero hx_ne_top
    exact h_rpow.symm

/-- Product of `δ^{-a_i}` equals `δ^{-∑ a_i}`. -/
lemma finset_prod_rpow_neg {ι : Type*} {s : Finset ι} {δ : ℝ} (hδ : 0 < δ)
    {a : ι → ℝ} : (∏ i ∈ s, δ ^ (-(a i))) = δ ^ (-(∑ i ∈ s, a i)) := by
  have h1 : (∏ i ∈ s, δ ^ (-(a i))) = δ ^ (∑ i ∈ s, -(a i)) :=
    finset_prod_real_rpow hδ
  rw [h1]
  have h2 : (∑ i ∈ s, -(a i)) = -(∑ i ∈ s, a i) := by
    rw [Finset.sum_neg_distrib]
  rw [h2]

end ProductPowers

-- ======================================================================
-- 9. Finset product telescoping
-- ======================================================================

section Telescoping

/-- Telescoping product over `Finset.range n`:
`∏_{i=0}^{n-1} f(i+1)/f(i) = f(n)/f(0)` in a commutative group. -/
lemma finset_prod_range_telescoping {G : Type*} [CommGroup G] {f : ℕ → G} {n : ℕ} :
    (∏ i ∈ Finset.range n, f (i + 1) / f i) = f n / f 0 :=
  Finset.prod_range_div f n

/-- Telescoping product in positive reals:
`∏_{i=0}^{n-1} f(i+1)/f(i) = f(n)/f(0)`. -/
lemma real_prod_range_telescoping {f : ℕ → ℝ} {n : ℕ} (hpos : ∀ i ≤ n, 0 < f i) :
    (∏ i ∈ Finset.range n, f (i + 1) / f i) = f n / f 0 := by
  induction n with
  | zero =>
    have h0 : f 0 ≠ 0 := (hpos 0 (by linarith)).ne'
    have h : f 0 / f 0 = 1 := by field_simp [h0]
    simpa using h.symm
  | succ n ih =>
    rw [Finset.prod_range_succ, ih (fun i hi => hpos i (by linarith))]
    have h0 : f 0 ≠ 0 := (hpos 0 (by linarith)).ne'
    have hn : f n ≠ 0 := (hpos n (by linarith)).ne'
    field_simp [h0, hn] <;> ring

/-- Telescoping product in `ENNReal`:
`∏_{i=0}^{n-1} f(i+1) / f(i) = f(n) / f(0)`, assuming all `f(i)` are nonzero and finite. -/
lemma ennreal_prod_range_telescoping {f : ℕ → ENNReal} {n : ℕ}
    (h_ne_zero : ∀ i ≤ n, f i ≠ 0) (h_ne_top : ∀ i ≤ n, f i ≠ ⊤) :
    (∏ i ∈ Finset.range n, f (i + 1) / f i) = f n / f 0 := by
  induction n with
  | zero =>
    have h0 : f 0 ≠ 0 := h_ne_zero 0 (by linarith)
    have h0t : f 0 ≠ ⊤ := h_ne_top 0 (by linarith)
    have h : f 0 / f 0 = 1 := ENNReal.div_self h0 h0t
    simpa using h.symm
  | succ n ih =>
    rw [Finset.prod_range_succ, ih (fun i hi => h_ne_zero i (by linarith))
      (fun i hi => h_ne_top i (by linarith))]
    have hn : f n ≠ 0 := h_ne_zero n (by linarith)
    have hnt : f n ≠ ⊤ := h_ne_top n (by linarith)
    have h_goal : (f n / f 0) * (f (n + 1) / f n) = f (n + 1) / f 0 := by
      rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
      have h_comm : f n * (f 0)⁻¹ * (f (n + 1) * (f n)⁻¹) =
          (f n * (f n)⁻¹) * (f (n + 1) * (f 0)⁻¹) := by
        simp [mul_assoc, mul_comm, mul_left_comm] <;> ac_rfl
      rw [h_comm, ENNReal.mul_inv_cancel hn hnt]
      <;> simp
    exact h_goal

/-- Product of ratios over `Finset.Ico a b` telescopes:
`∏_{i=a}^{b-1} f(i+1)/f(i) = f(b)/f(a)` in a commutative group. -/
lemma finset_prod_Ico_telescoping {G : Type*} [CommGroup G] {f : ℕ → G} {a b : ℕ} (h : a ≤ b) :
    (∏ i ∈ Finset.Ico a b, f (i + 1) / f i) = f b / f a := by
  have h_main : ∀ (a b : ℕ), a ≤ b →
      (∏ i ∈ Finset.Ico a b, f (i + 1) / f i) = f b / f a := by
    intro a b h
    induction b with
    | zero =>
      have h_a0 : a = 0 := by omega
      subst h_a0
      simp
    | succ b ih =>
      by_cases h_ab : a ≤ b
      · have h_Ico : Finset.Ico a (b + 1) = Finset.Ico a b ∪ {b} := by
          ext x
          simp [Finset.mem_Ico, Nat.lt_succ_iff] <;> omega
        rw [h_Ico]
        have h_disj : Disjoint (Finset.Ico a b) ({b} : Finset ℕ) := by
          simp [Finset.disjoint_left, Finset.mem_Ico] <;> omega
        rw [Finset.prod_union h_disj, ih h_ab]
        have h_prod : (∏ x ∈ ({b} : Finset ℕ), f (x + 1) / f x) = f (b + 1) / f b := by
          simp
        rw [h_prod]
        have h_goal : (f b / f a) * (f (b + 1) / f b) = f (b + 1) / f a := by
          have h1 : (f b / f a) * (f (b + 1) / f b) =
              f b * ((f a)⁻¹ * (f (b + 1) * (f b)⁻¹)) := by
            simp [div_eq_mul_inv, mul_assoc] <;> rfl
          rw [h1]
          have h2 : (f a)⁻¹ * (f (b + 1) * (f b)⁻¹) = (f b)⁻¹ * ((f a)⁻¹ * f (b + 1)) := by
            have h21 : (f a)⁻¹ * (f (b + 1) * (f b)⁻¹) = (f a)⁻¹ * f (b + 1) * (f b)⁻¹ := by
              simp [mul_assoc] <;> rfl
            rw [h21]
            have h22 : (f a)⁻¹ * f (b + 1) * (f b)⁻¹ = (f b)⁻¹ * ((f a)⁻¹ * f (b + 1)) := by
              simp [mul_assoc, mul_comm, mul_left_comm] <;> rfl
            exact h22
          rw [h2]
          have h3 : f b * ((f b)⁻¹ * ((f a)⁻¹ * f (b + 1))) = (f a)⁻¹ * f (b + 1) :=
            mul_inv_cancel_left (f b) ((f a)⁻¹ * f (b + 1))
          rw [h3]
          have h4 : (f a)⁻¹ * f (b + 1) = f (b + 1) * (f a)⁻¹ := mul_comm _ _
          rw [h4]
          <;> simp [div_eq_mul_inv]
        exact h_goal
      · have h_a : a = b + 1 := by omega
        rw [h_a]
        simp
  exact h_main a b h

end Telescoping

-- ======================================================================
-- 10. Additional NNReal / ENNReal conversion lemmas
-- ======================================================================

section MoreConversions

/-- `ENNReal.ofReal` distributes over finite products when all factors
are non-negative. -/
lemma ofReal_finset_prod {ι : Type*} {s : Finset ι} {f : ι → ℝ}
    (hnonneg : ∀ i ∈ s, 0 ≤ f i) :
    ENNReal.ofReal (∏ i ∈ s, f i) = ∏ i ∈ s, ENNReal.ofReal (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    rw [ENNReal.ofReal_mul (hnonneg i (Finset.mem_insert_self i s))]
    rw [ih (fun j hj => hnonneg j (Finset.mem_insert_of_mem hj))]
    <;> rfl

/-- `ENNReal.ofReal` distributes over finite sums when all summands
are non-negative. -/
lemma ofReal_finset_sum {ι : Type*} {s : Finset ι} {f : ι → ℝ}
    (hnonneg : ∀ i ∈ s, 0 ≤ f i) :
    ENNReal.ofReal (∑ i ∈ s, f i) = ∑ i ∈ s, ENNReal.ofReal (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    rw [ENNReal.ofReal_add (hnonneg i (Finset.mem_insert_self i s))
      (Finset.sum_nonneg fun j hj => hnonneg j (Finset.mem_insert_of_mem hj))]
    rw [ih (fun j hj => hnonneg j (Finset.mem_insert_of_mem hj))]
    <;> rfl

/-- Convert a `NNReal`-valued product to `ENNReal`. -/
lemma coe_nnreal_finset_prod {ι : Type*} {s : Finset ι} {f : ι → NNReal} :
    (↑(∏ i ∈ s, f i) : ENNReal) = ∏ i ∈ s, (↑(f i) : ENNReal) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    rw [← ih]
    <;> simp [NNReal.coe_prod]
    <;> rfl

/-- `ENNReal.ofNNReal` distributes over products. -/
lemma ofNNReal_finset_prod {ι : Type*} {s : Finset ι} {f : ι → NNReal} :
    ENNReal.ofNNReal (∏ i ∈ s, f i) = ∏ i ∈ s, ENNReal.ofNNReal (f i) := by
  exact coe_nnreal_finset_prod

/-- For `0 ≤ x`, `ENNReal.ofReal x = ENNReal.ofNNReal x.toNNReal`. -/
lemma ofReal_eq_ofNNReal {x : ℝ} (hx : 0 ≤ x) :
    ENNReal.ofReal x = ENNReal.ofNNReal x.toNNReal := by
  have h1 : (x.toNNReal : ℝ) = x := Real.coe_toNNReal x hx
  have h2 : ENNReal.ofReal x = ↑(x.toNNReal) := by
    rw [← ENNReal.ofReal_coe_nnreal, h1]
  exact h2

end MoreConversions

end DirecretisedFurstenbergEstimate.RealAnalysis
