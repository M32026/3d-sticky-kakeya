module

/-
  Independent helper lemmas for Step 5 orientation-first assembly.

  These lemmas do NOT depend on bounded_slope_bridge or normalize_and_partition.
  They can be integrated into the main skeleton once those upstream pieces are ready.

  Provides:
  1. ncover_monotone_scale: Ncover antitone in scale
  2. exponent_chain_eps_final_lt_root: ε_final < ε_Root from definitions
  3. dyadic_scale_le_half: Δ ≤ 1/2 from dyadicScales
  4. decomposition_good_product: good product bound from RawMultiscaleDecomp
  5. decomposition_bad_product: bad product bound from RawMultiscaleDecomp
  6. budget_verification_eps_root: budget verification using ε_Root
  7. coarser_smallness_threshold: construct δ₀ for hδ_small
  8. combining_scale_threshold: construct δ₀ for hk_le
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Section9.RawMultiscaleDecomp
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Section9.GoodProductBound
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Section9.AbsorptionHelpers
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Section9.BudgetVerification
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.AbsorptionHypotheses
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DirecretisedFurstenbergEstimate.Section9

open DirecretisedFurstenbergEstimate (EuclideanPlane)
open MultiscaleDecomposition (IsSetBetweenScales IsRegularBetweenScales)

/-! ### 1. Ncover monotonicity in scale -/

lemma ncover_monotone_scale {X : Type*} [PseudoMetricSpace X]
    {δ δ' : ℝ} (hδ_pos : 0 < δ) (hδ'_pos : 0 < δ')
    (h : δ ≤ δ') (E : Set X) :
    Metric.externalCoveringNumber δ'.toNNReal E ≤
    Metric.externalCoveringNumber δ.toNNReal E := by
  have h2 : (δ.toNNReal : ℝ) = δ := by
    simp [hδ_pos.le]
  have h3 : (δ'.toNNReal : ℝ) = δ' := by
    simp [hδ'_pos.le]
  have h4 : (δ.toNNReal : ℝ) ≤ (δ'.toNNReal : ℝ) := by
    rw [h2, h3]; exact h
  have h5 : δ.toNNReal ≤ δ'.toNNReal := NNReal.coe_le_coe.mp h4
  exact Metric.externalCoveringNumber_anti h5

/-! ### 2. Exponent chain: ε_final < ε_Root -/

lemma exponent_chain_eps_final_lt_root
    (ε_N ε_Root ε_final B_K : ℝ)
    (hεN_pos : 0 < ε_N) (hBK_ge3 : B_K ≥ 3)
    (hε_Root_eq : ε_Root = ε_N / (4 * B_K))
    (hε_final_eq : ε_final = ε_Root / 4) :
    ε_final < ε_Root := by
  have h1 : 0 < ε_Root := by
    rw [hε_Root_eq]
    have h2 : 0 < 4 * B_K := by linarith
    positivity
  rw [hε_final_eq]
  linarith

/-! ### 3. Δ ≤ 1/2 from dyadicScales -/

lemma dyadic_scale_le_half {Δ : ℝ} (hΔ_dyadic : Δ ∈ dyadicScales) (hΔ_lt_one : Δ < 1) :
    Δ ≤ 1 / 2 := by
  rcases hΔ_dyadic with ⟨n, hn⟩
  have h1 : Δ = (2 : ℝ) ^ (-(n : ℤ)) := hn
  rw [h1]
  have h2 : (n : ℤ) ≥ 1 := by
    by_contra h
    have h3 : (n : ℤ) ≤ 0 := by linarith
    have h4 : (2 : ℝ) ^ (-(n : ℤ)) ≥ 1 := by
      have h5 : -(n : ℤ) ≥ 0 := by linarith
      have h6 : (2 : ℝ) ^ (-(n : ℤ)) ≥ (2 : ℝ) ^ (0 : ℤ) := by
        gcongr <;> linarith
      simpa using h6
    linarith
  have h7 : (2 : ℝ) ^ (-(n : ℤ)) ≤ (2 : ℝ) ^ (-1 : ℤ) := by
    gcongr <;> linarith
  simpa using h7

/-! ### 4. Good product bound from RawMultiscaleDecomp -/

/-- Telescoping product: ∏_{i=0}^{n-1} f(i)/f(i+1) = f(0)/f(n). -/
lemma telescoping_prod {f : ℕ → ℝ} (hf_pos : ∀ i, 0 < f i) (n : ℕ) :
    ∏ i ∈ Finset.range n, (f i / f (i + 1)) = f 0 / f n := by
  induction n with
  | zero =>
    have h : f 0 / f 0 = 1 := by
      field_simp [(hf_pos 0).ne']
    simp [h]
  | succ n ih =>
    rw [Finset.prod_range_succ, ih]
    have hfn_ne : f n ≠ 0 := (hf_pos n).ne'
    have hfn1_ne : f (n + 1) ≠ 0 := (hf_pos (n + 1)).ne'
    field_simp [hfn_ne, hfn1_ne] <;> ring

lemma decomposition_good_product
    {δ_d s t ε_G ε_bad η τ : ℝ}
    (hδ_d_pos : 0 < δ_d) (hδ_d_lt_one : δ_d < 1)
    (hs : 0 < s) (hst : s < t)
    (hεG_pos : 0 < ε_G) (hε_bad_pos : 0 < ε_bad)
    (hη_nonneg : 0 ≤ η)
    (hεG_small : ε_G < 2 * (t - s))
    (hε_bad_le : ε_bad ≤ ε_G / 4)
    {n : ℕ} {P : Set EuclideanPlane}
    (decomp : RawMultiscaleDecomp δ_d s t τ ε_G ε_bad n P)
    (hΔ_pos : 0 < decomp.Δ) (hΔ_lt_one : decomp.Δ < 1) :
    let G := decomp.S.filter (fun j => decomp.t_j j.val ≥ t - ε_G / 2)
    let ratio := fun j : Fin n =>
      (decomp.Δ ^ decomp.i j.val : ℝ) / (decomp.Δ ^ decomp.i (j.val + 1))
    (∏ j ∈ G, (ratio j) ^ η) ≥ δ_d ^ (-(ε_G * η / 8)) := by
  let f : ℕ → ℝ := fun i => decomp.Δ ^ decomp.i i
  let ratio : Fin n → ℝ := fun j => f j.val / f (j.val + 1)
  let G : Finset (Fin n) := decomp.S.filter (fun j => decomp.t_j j.val ≥ t - ε_G / 2)
  let t_j_fin : Fin n → ℝ := fun j => decomp.t_j j.val

  have hf_pos : ∀ i, 0 < f i := by intro i; positivity

  have h_ratio_gt_one : ∀ j : Fin n, 1 < ratio j := by
    intro j
    have h1 : decomp.i j.val < decomp.i (j.val + 1) := decomp.h_strict_mono j.val j.is_lt
    have h2 : f (j.val + 1) < f j.val := by
      dsimp only [f]
      have h_exp : decomp.i j.val < decomp.i (j.val + 1) := h1
      let k : ℕ := decomp.i (j.val + 1) - decomp.i j.val
      have hk_pos : 0 < k := by omega
      have h9 : decomp.i (j.val + 1) = decomp.i j.val + k := by omega
      have h10 : decomp.Δ ^ decomp.i (j.val + 1) = decomp.Δ ^ decomp.i j.val * decomp.Δ ^ k := by
        rw [h9, pow_add]
      rw [h10]
      have h11 : decomp.Δ ^ k < 1 := by
        have h12 : 0 ≤ decomp.Δ := hΔ_pos.le
        let k' : ℕ := k - 1
        have hk_eq : k = k' + 1 := by omega
        have h14 : ∀ (n : ℕ), decomp.Δ ^ n ≤ 1 := by
          intro n
          induction n with
          | zero => norm_num
          | succ n'' ih =>
            calc decomp.Δ ^ (n'' + 1)
              = decomp.Δ ^ n'' * decomp.Δ := by ring
            _ ≤ 1 * 1 := by gcongr <;> linarith
            _ = 1 := by ring
        rw [hk_eq]
        calc decomp.Δ ^ (k' + 1)
          = decomp.Δ ^ k' * decomp.Δ := by ring
        _ ≤ 1 * decomp.Δ := by gcongr <;> exact h14 k'
        _ = decomp.Δ := by ring
        _ < 1 := hΔ_lt_one
      have h13 : 0 < decomp.Δ ^ decomp.i j.val := by positivity
      nlinarith
    have h3 : 0 < f (j.val + 1) := hf_pos (j.val + 1)
    exact (one_lt_div h3).mpr h2

  have h_total : ∏ j ∈ (Finset.univ : Finset (Fin n)), ratio j = 1 / δ_d := by
    have h1 : ∏ j ∈ (Finset.univ : Finset (Fin n)), ratio j =
        ∏ i ∈ Finset.range n, (f i / f (i + 1)) := by
      apply Finset.prod_bij' (fun (j : Fin n) _ => j.val) (fun i hi => ⟨i, Finset.mem_range.mp hi⟩)
      <;> simp [ratio] <;> omega
    rw [h1, telescoping_prod hf_pos n]
    have h_f0 : f 0 = 1 := by
      dsimp only [f]; rw [decomp.hi0]; norm_num
    have h_fn : f n = δ_d := by
      dsimp only [f]; rw [decomp.hin]
      exact decomp.hδ_d.symm
    rw [h_f0, h_fn] <;> ring

  have h_tj_le_two : ∀ j ∈ decomp.S, t_j_fin j ≤ 2 := by
    intro j hj
    have h2 := decomp.h_tj_range j
    exact h2.2

  have h_S_prod : ∏ j ∈ decomp.S, (ratio j) ^ (t_j_fin j) ≥
      δ_d ^ (ε_bad - t) := by
    simpa [ratio, t_j_fin] using decomp.h_S_product

  exact good_product_bound
    δ_d hδ_d_pos hδ_d_lt_one
    s t ε_G ε_bad η
    hs hst hεG_pos hε_bad_pos hη_nonneg
    hεG_small hε_bad_le
    ratio h_ratio_gt_one h_total
    decomp.S decomp.B decomp.h_partition decomp.h_disjoint
    t_j_fin h_tj_le_two h_S_prod
    G rfl

/-! ### 5. Bad product bound from RawMultiscaleDecomp -/

lemma decomposition_bad_product
    {δ_d s t ε_G ε_bad τ : ℝ}
    (hδ_d_pos : 0 < δ_d)
    (hε_bad_pos : 0 < ε_bad)
    {n : ℕ} {P : Set EuclideanPlane}
    (decomp : RawMultiscaleDecomp δ_d s t τ ε_G ε_bad n P)
    (Δ_arr : Fin (n + 1) → ℝ)
    (hΔ_arr_pos : ∀ i, 0 < Δ_arr i)
    (hΔ_arr_eq : ∀ j : Fin n,
      Δ_arr j.castSucc / Δ_arr (Fin.succ j) =
        (decomp.Δ ^ decomp.i j.val : ℝ) / (decomp.Δ ^ decomp.i (j.val + 1))) :
    (∏ j ∈ decomp.B, Δ_arr (Fin.succ j) / Δ_arr j.castSucc) ≥ δ_d ^ ε_bad := by
  have h : (∏ j ∈ decomp.B, (Δ_arr j.castSucc / Δ_arr (Fin.succ j))) ≤
      δ_d ^ (-ε_bad) := by
    have h2 : ∏ j ∈ decomp.B, (Δ_arr j.castSucc / Δ_arr (Fin.succ j)) =
        ∏ j ∈ decomp.B, ((decomp.Δ ^ decomp.i j.val : ℝ) / (decomp.Δ ^ decomp.i (j.val + 1))) := by
      apply Finset.prod_congr rfl
      intro j _
      exact hΔ_arr_eq j
    rw [h2]
    exact decomp.h_B_product
  exact bad_product_reciprocation hΔ_arr_pos h hδ_d_pos hε_bad_pos.le

/-! ### 6. Budget verification with ε_Root as working exponent -/

lemma budget_verification_eps_root
    (ε_G η ε_N ε_bad ε_Root : ℝ)
    (hεG_pos : 0 < ε_G) (hη_pos : 0 < η)
    (hε_bad_pos : 0 < ε_bad)
    (hεN_eq : ε_N = ε_G * η / 100)
    (hε_bad_lt : ε_bad < ε_N)
    (B_K : ℝ) (hBK_ge3 : B_K ≥ 3)
    (hε_Root_eq : ε_Root = ε_N / (4 * B_K))
    (C' lam ρ_M ρ_T ε_log_loss : ℝ)
    (hlam_bound : (1 + C') * lam ≤ ε_G * η / 800)
    (hρM_bound : ρ_M ≤ ε_G * η / 800)
    (hρT_bound : ρ_T ≤ ε_G * η / 800)
    (hεlog_bound : ε_log_loss ≤ ε_G * η / 800) :
    ε_G * η / 8 ≥ (1 + C') * lam + ρ_M + ρ_T + ε_N + ε_bad + ε_log_loss + ε_Root := by
  have h1 : ε_N ≤ ε_G * η / 100 := by rw [hεN_eq]
  have h2 : ε_bad < ε_G * η / 100 := by
    rw [hεN_eq] at hε_bad_lt; exact hε_bad_lt
  have h3 : ε_Root ≤ ε_G * η / 1200 := by
    rw [hε_Root_eq, hεN_eq]
    have h41 : ε_G * η / 100 / (4 * B_K) = ε_G * η / (400 * B_K) := by ring
    rw [h41]
    have h42 : 400 * B_K ≥ 1200 := by nlinarith
    have h_pos : 0 < ε_G * η := mul_pos hεG_pos hη_pos
    exact div_le_div_of_nonneg_left h_pos.le (by positivity) h42
  have h4 : (1 + C') * lam + ρ_M + ρ_T + ε_N + ε_bad + ε_log_loss + ε_Root ≤
      ε_G * η / 800 + ε_G * η / 800 + ε_G * η / 800 + ε_G * η / 100 + ε_G * η / 100 + ε_G * η / 800 + ε_G * η / 1200 := by
    gcongr
  have h5 : ε_G * η / 800 + ε_G * η / 800 + ε_G * η / 800 + ε_G * η / 100 + ε_G * η / 100 + ε_G * η / 800 + ε_G * η / 1200 ≤ ε_G * η / 8 := by
    have h_pos : 0 < ε_G * η := mul_pos hεG_pos hη_pos
    linarith
  linarith

/-! ### 7. Coarser smallness threshold -/

lemma coarser_smallness_threshold
    (s ε_work ε_final C_ratio : ℝ)
    (hs : 0 < s) (hε_work_pos : 0 < ε_work) (hε_final_pos : 0 < ε_final)
    (hε_final_lt_work : ε_final < ε_work)
    (hC_ratio_ge1 : 1 ≤ C_ratio) :
    ∃ (δ₀ : ℝ), 0 < δ₀ ∧
      ∀ (δ : ℝ), 0 < δ → δ ≤ δ₀ →
        δ ≤ C_ratio ^ (-(2 * s + ε_work) / (ε_work - ε_final)) := by
  let threshold : ℝ := C_ratio ^ (-(2 * s + ε_work) / (ε_work - ε_final))
  have h_threshold_pos : 0 < threshold := by
    have h1 : 0 < C_ratio := by linarith
    positivity
  refine ⟨threshold, h_threshold_pos, fun δ hδ_pos hδ_le => ?_⟩
  exact hδ_le

/-! ### 8. Combining scale threshold -/

lemma combining_scale_threshold
    (Δ δ₀_comb : ℝ) (hΔ_pos : 0 < Δ) (hδ₀_comb_pos : 0 < δ₀_comb) :
    ∃ (δ₀_comb_scale : ℝ), 0 < δ₀_comb_scale ∧
      ∀ (δ : ℝ), 0 < δ → δ ≤ δ₀_comb_scale →
        ∀ (δ_d : ℝ), δ_d ≤ (1 / Δ) * δ → δ_d ≤ δ₀_comb := by
  let δ₀_comb_scale : ℝ := Δ * δ₀_comb
  have h_pos : 0 < δ₀_comb_scale := mul_pos hΔ_pos hδ₀_comb_pos
  refine ⟨δ₀_comb_scale, h_pos, fun δ hδ_pos hδ_le δ_d hδ_d_le => ?_⟩
  calc δ_d
    ≤ (1 / Δ) * δ := hδ_d_le
  _ = δ / Δ := by field_simp [hΔ_pos.ne'] <;> ring
  _ ≤ (Δ * δ₀_comb) / Δ := by gcongr
  _ = δ₀_comb := by field_simp [hΔ_pos.ne'] <;> ring

/-! ### 9. Thickening absorption bounds -/

/-- Construct all three thickening absorption bounds for a given ratio.

    Uses absorb_normal, absorb_good_high, absorb_good_low from
    CombiningTheoremRework.AbsorptionHypotheses.

    The constant K = 72900 * Δ^(-4) must be absorbed by log(1/δ_k)^C_P.
    This is ensured by h_core. -/
lemma thickening_absorption_all
    (Δ C_P ε_G ε_N ε_bad : ℝ)
    (hΔ_pos : 0 < Δ)
    (hCP : 0 < C_P) (hεG_pos : 0 < ε_G) (hεN_pos : 0 < ε_N)
    (hε_bad_pos : 0 < ε_bad)
    (hε_bad_lt_εN : ε_bad < ε_N)
    (hεN_le_εG : ε_N ≤ ε_G)
    (hε_bad_lt_half_εG : ε_bad < ε_G / 2)
    (δ_k : ℝ) (hδ_k_pos : 0 < δ_k) (hδ_k_lt_one : δ_k < 1)
    (ratio : ℝ) (hratio_one : 1 ≤ ratio)
    (h_core : (72900 : ℝ) * Real.rpow Δ (-4) ≤
        Real.rpow (Real.log (1 / δ_k)) C_P) :
    ((72900 : ℝ) * Real.rpow Δ (-4) * ratio ^ ε_bad ≤
        Real.rpow (Real.log (1 / δ_k)) C_P * ratio ^ ε_N) ∧
    ((72900 : ℝ) * Real.rpow Δ (-4) * ratio ^ ε_bad ≤
        Real.rpow (Real.log (1 / δ_k)) C_P * ratio ^ ε_G) ∧
    (((72900 : ℝ) * Real.rpow Δ (-4) * ratio ^ ε_bad) * ratio ^ (ε_G / 2) ≤
        Real.rpow (Real.log (1 / δ_k)) C_P * ratio ^ ε_G) := by
  let K : ℝ := (72900 : ℝ) * Real.rpow Δ (-4)
  have h_rpow_pos : 0 < Real.rpow Δ (-4) := Real.rpow_pos_of_pos hΔ_pos _
  have hK_pos : 0 < K := by
    dsimp only [K]
    exact mul_pos (by norm_num) h_rpow_pos
  have hε_bad_nonneg : 0 ≤ ε_bad := by linarith
  have h_gap_normal : ε_bad < ε_N := hε_bad_lt_εN
  have h_gap_high : ε_bad < ε_G := by linarith
  have h1 := DirecretisedFurstenbergEstimate.MultiscaleDecomposition.absorb_normal
    K C_P ε_bad ε_N ratio δ_k hK_pos hCP hε_bad_nonneg hεN_pos h_gap_normal
    hratio_one hδ_k_pos hδ_k_lt_one h_core
  have h2 := DirecretisedFurstenbergEstimate.MultiscaleDecomposition.absorb_good_high
    K C_P ε_bad ε_G ratio δ_k hK_pos hCP hε_bad_nonneg hεG_pos h_gap_high
    hratio_one hδ_k_pos hδ_k_lt_one h_core
  have h3_raw := DirecretisedFurstenbergEstimate.MultiscaleDecomposition.absorb_good_low
    K C_P ε_bad ε_G ratio δ_k hK_pos hCP hε_bad_nonneg hεG_pos hε_bad_lt_half_εG
    hratio_one hδ_k_pos hδ_k_lt_one h_core
  have h3 : ((72900 : ℝ) * Real.rpow Δ (-4) * ratio ^ ε_bad) * ratio ^ (ε_G / 2) ≤
      Real.rpow (Real.log (1 / δ_k)) C_P * ratio ^ ε_G := by
    simpa [K, mul_assoc] using h3_raw
  exact ⟨h1, h2, h3⟩

/-- Construct δ₀ for the thickening absorption core bound.

    Ensures 72900 * Δ^(-4) ≤ log(1/δ_k)^C_P for δ_k small enough.
    Since δ_k ≤ (1/Δ) * δ, we can ensure via outer δ₀. -/
lemma thickening_absorption_threshold
    (Δ C_P : ℝ) (hΔ_pos : 0 < Δ) (hCP : 0 < C_P) :
    ∃ (δ₀_absorb : ℝ), 0 < δ₀_absorb ∧
      ∀ (δ_k : ℝ), 0 < δ_k → δ_k < δ₀_absorb →
        (72900 : ℝ) * Real.rpow Δ (-4) ≤
          Real.rpow (Real.log (1 / δ_k)) C_P := by
  let K : ℝ := (72900 : ℝ) * Real.rpow Δ (-4)
  have h_rpow_pos : 0 < Real.rpow Δ (-4) := Real.rpow_pos_of_pos hΔ_pos _
  have hK_pos : 0 < K := mul_pos (by norm_num) h_rpow_pos
  have h_main : ∃ (δ₀ : ℝ), 0 < δ₀ ∧ ∀ (δ : ℝ), 0 < δ → δ < δ₀ →
      K ≤ Real.rpow (Real.log (1 / δ)) C_P :=
    DirecretisedFurstenbergEstimate.MultiscaleDecomposition.const_le_polylog K C_P hK_pos hCP
  rcases h_main with ⟨δ₀, hδ₀_pos, h⟩
  exact ⟨δ₀, hδ₀_pos, fun δ_k hδ_k_pos hδ_k_lt => h δ_k hδ_k_pos hδ_k_lt⟩

end DirecretisedFurstenbergEstimate.Section9
