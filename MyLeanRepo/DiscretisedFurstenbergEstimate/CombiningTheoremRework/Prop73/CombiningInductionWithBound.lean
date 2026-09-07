module

/-
  Combining Induction with Explicit C' Upper Bound

  Proves that the Prop73 combining induction can be stated with
  C' ≤ combiningCprime(n,τ), where combiningCprime(n,τ) = 2·Σ_{i=0}^{n-1}(2/τ)^i.

  Uses the _with_data uniform induction (CombiningExtraHypotheses_v2) and
  inductive_step_core_v2. This is the permanent bounded-consumer form:
  UniformIncidenceData is a required input parameter, not a temporary
  hypothesis.

  The actual C' from the induction satisfies:
    C'(1) = 1
    C'(n) = 1 + (2/τ)·C'(n-1)
  so C'(n) = Σ_{i=0}^{n-1}(2/τ)^i, which is exactly half of combiningCprime(n,τ).

  This explicit bound lets downstream consumers choose λ before calling the
  combining theorem, breaking the circularity between λ selection and the
  existential C'.

  Whiteprint node: combining_theorem_genuine / combining_induction_with_bound
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.Statement
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.RestructuredStatement
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.BaseCaseUniform
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.InductiveStepCore_v2
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.GoodCaseImprovedIncidence
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ParameterBudgetLemmas
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.BoundedStatement
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.CoarseAbsorptionHelpers
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.FineAbsorptionHelpers
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.GoodImprovedIncidenceWrapper
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.ThresholdHelpers
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

set_option maxHeartbeats 500000

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DiscretisedFurstenbergEstimate.CombiningTheorem
open DiscretisedFurstenbergEstimate.DyadicConversion
open DirecretisedFurstenbergEstimate.FormatConversion.M2
open DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73BaseCase
open DirecretisedFurstenbergEstimate.RegularIncidence

/-! ### Helper lemmas for analytic threshold arguments -/

/-- Exponential dominates degree-7 polynomial: for b>0, C≥0, ∃ K, ∀ k≥K,
    C * (4k+7)^7 ≤ Real.exp (b * k). -/
lemma exists_K_poly_le_exp (b C : ℝ) (hb : 0 < b) (hC : 0 ≤ C) :
    ∃ (K : ℕ), ∀ (k : ℕ), k ≥ K →
      C * (4 * (k : ℝ) + 7)^7 ≤ Real.exp (b * (k : ℝ)) := by
  let P : ℝ := C * 11^7
  let threshold : ℝ := P * (8 : ℝ)^8 / b^8
  rcases exists_nat_ge threshold with ⟨K, hK⟩
  let K' := max K 1
  use K'
  intro k hk
  have hk_ge1 : (k : ℝ) ≥ 1 := by
    have h : k ≥ K' := hk
    have h2 : K' ≥ 1 := le_max_right _ _
    exact_mod_cast (le_trans h2 h)
  have h_k_ge_K : (k : ℝ) ≥ (K : ℝ) := by
    have h : k ≥ K' := hk
    have h2 : K' ≥ K := le_max_left _ _
    exact_mod_cast (le_trans h2 h)
  have h1 : (4 * (k : ℝ) + 7) ≤ 11 * (k : ℝ) := by linarith
  have h2 : C * (4 * (k : ℝ) + 7)^7 ≤ P * (k : ℝ)^7 := by
    have h3 : (4 * (k : ℝ) + 7)^7 ≤ (11 * (k : ℝ))^7 := by gcongr <;> linarith
    calc C * (4 * (k : ℝ) + 7)^7
      ≤ C * (11 * (k : ℝ))^7 := by gcongr
      _ = C * 11^7 * (k : ℝ)^7 := by ring
      _ = P * (k : ℝ)^7 := by simp [P] <;> ring
  have h_b8_pos : 0 < b^8 := by positivity
  have h5 : (k : ℝ) ≥ threshold := by
    calc (k : ℝ) ≥ (K : ℝ) := h_k_ge_K
         _ ≥ threshold := hK
  have h6 : P ≤ b^8 * (k : ℝ) / (8 : ℝ)^8 := by
    have h7 : b^8 * (k : ℝ) / (8 : ℝ)^8 ≥ b^8 * threshold / (8 : ℝ)^8 := by gcongr
    have h8 : b^8 * threshold / (8 : ℝ)^8 = P := by
      dsimp only [threshold]
      have h9 : b^8 * (P * (8 : ℝ)^8 / b^8) / (8 : ℝ)^8 = P := by
        field_simp [h_b8_pos.ne'] <;> ring
      exact h9
    linarith
  have h4 : P * (k : ℝ)^7 ≤ b^8 * (k : ℝ)^8 / (8 : ℝ)^8 := by
    have h10 : 0 ≤ (k : ℝ)^7 := by positivity
    calc P * (k : ℝ)^7
      ≤ (b^8 * (k : ℝ) / (8 : ℝ)^8) * (k : ℝ)^7 := by gcongr
      _ = b^8 * (k : ℝ)^8 / (8 : ℝ)^8 := by ring
  have h_pos_bk : 0 < b * (k : ℝ) := by positivity
  have h8 : b^8 * (k : ℝ)^8 / (8 : ℝ)^8 ≤ Real.exp (b * (k : ℝ)) := by
    have h9 : (b * (k : ℝ))^8 / (8 : ℝ)^8 = b^8 * (k : ℝ)^8 / (8 : ℝ)^8 := by
      rw [mul_pow] <;> ring
    rw [← h9]
    set y := b * (k : ℝ) / 8 with hy_def
    have hy_pos : 0 < y := by positivity
    have h10 : Real.exp (b * (k : ℝ)) ≥ (b * (k : ℝ))^8 / (8 : ℝ)^8 := by
      have h11 : Real.exp y > y := by
        have h12 : y + 1 < Real.exp y := Real.add_one_lt_exp hy_pos.ne'
        have h125 : y < y + 1 := by linarith
        exact lt_trans h125 h12
      have h13 : Real.exp (b * (k : ℝ)) = (Real.exp y)^8 := by
        have h14 : b * (k : ℝ) = 8 * y := by
          simp [hy_def] <;> ring
        rw [h14, ← Real.exp_nat_mul] <;> norm_cast
      rw [h13]
      have h15 : (Real.exp y)^8 > y^8 := by gcongr <;> linarith
      have h16 : y^8 = (b * (k : ℝ))^8 / (8 : ℝ)^8 := by
        simp [hy_def] <;> ring
      rw [h16] at h15
      exact h15.le
    exact h10
  calc C * (4 * (k : ℝ) + 7)^7
    ≤ P * (k : ℝ)^7 := h2
    _ ≤ b^8 * (k : ℝ)^8 / (8 : ℝ)^8 := h4
    _ ≤ Real.exp (b * (k : ℝ)) := h8

/-- Polynomial lower bound: for C≥0, ∃ K, ∀ k≥K, 2700*3145728*(4k+7)^7 ≥ C. -/
lemma exists_K_poly_ge (C : ℝ) (hC : 0 ≤ C) :
    ∃ (K : ℕ), ∀ (k : ℕ), k ≥ K →
      (2700 : ℝ) * 3145728 * (4 * (k : ℝ) + 7)^7 ≥ C := by
  by_cases hC0 : C ≤ 0
  · use 1
    intro k _
    have hpos : 0 < (2700 : ℝ) * 3145728 * (4 * (k : ℝ) + 7)^7 := by positivity
    linarith
  · have hCpos : 0 < C := by linarith
    let base : ℝ := (2700 : ℝ) * 3145728
    have hbase_pos : 0 < base := by positivity
    let q : ℝ := (C / base) ^ (1 / (7 : ℝ))
    rcases exists_nat_ge q with ⟨K, hK⟩
    let K' := max K 1
    use K'
    intro k hk
    have hk_ge1 : (k : ℝ) ≥ 1 := by
      have h : k ≥ K' := hk
      have h2 : K' ≥ 1 := le_max_right _ _
      exact_mod_cast (le_trans h2 h)
    have h_k_ge_K : (k : ℝ) ≥ (K : ℝ) := by
      have h : k ≥ K' := hk
      have h2 : K' ≥ K := le_max_left _ _
      exact_mod_cast (le_trans h2 h)
    have hq_nonneg : 0 ≤ q := by positivity
    have h_pos : 0 < C / base := by positivity
    have h_q7 : q^7 = C / base := by
      have h1 : q^7 = ((C / base) ^ (1 / (7 : ℝ))) ^ 7 := by rfl
      rw [h1]
      have h2 : ((C / base) ^ (1 / (7 : ℝ))) ^ 7
               = ((C / base) ^ (1 / (7 : ℝ))) ^ (7 : ℝ) := by norm_cast
      rw [h2]
      have h3 : ((C / base) ^ (1 / (7 : ℝ))) ^ (7 : ℝ)
               = (C / base) ^ ((1 / (7 : ℝ)) * (7 : ℝ)) := by
        rw [Real.rpow_mul h_pos.le]
      rw [h3]
      have h4 : (1 / (7 : ℝ)) * (7 : ℝ) = 1 := by ring
      rw [h4]
      simp
    have h1 : (k : ℝ)^7 ≥ C / base := by
      have h2 : (k : ℝ) ≥ q := by
        calc (k : ℝ) ≥ (K : ℝ) := h_k_ge_K
             _ ≥ q := hK
      have h4 : (k : ℝ)^7 ≥ q^7 := by gcongr <;> linarith
      rw [h_q7] at h4
      exact h4
    have h6 : 4 * (k : ℝ) + 7 ≥ (k : ℝ) := by linarith
    have h7 : (4 * (k : ℝ) + 7)^7 ≥ (k : ℝ)^7 := by gcongr <;> linarith
    calc (2700 : ℝ) * 3145728 * (4 * (k : ℝ) + 7)^7
      ≥ base * (k : ℝ)^7 := by gcongr
      _ ≥ base * (C / base) := by gcongr
      _ = C := by
        field_simp [hbase_pos.ne'] <;> ring

/-- Positive-base rpow of a product. -/
lemma rpow_mul_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (a : ℝ) :
    (x * y) ^ a = x ^ a * y ^ a := by
  have h : ∀ (x y : ℝ), 0 ≤ x → 0 ≤ y → (x * y) ^ a = x ^ a * y ^ a := by
    intro x y hx hy
    simpa using Real.mul_rpow (x := x) (y := y) (z := a) hx hy
  exact h x y hx.le hy.le

/-- Positive-base rpow of a sum of exponents. -/
lemma rpow_add_pos {x : ℝ} (hx : 0 < x) (a b : ℝ) :
    x ^ (a + b) = x ^ a * x ^ b :=
  Real.rpow_add hx a b

/-- Absorption helper: from `p * exp(-b*k) < 1/C` derive `C*p < exp(b*k)`. -/
lemma exp_absorb_helper {p b C : ℝ} (k : ℝ) (hp : 0 < p) (hb : 0 < b) (hC : 0 < C)
    (h : p * Real.exp (-b * k) < 1 / C) :
    C * p < Real.exp (b * k) := by
  have h1 : 0 < Real.exp (b * k) := Real.exp_pos (b * k)
  have h2 : Real.exp (-b * k) * Real.exp (b * k) = 1 := by
    rw [← Real.exp_add]; ring_nf; rw [Real.exp_zero]
  have h3 : C * (p * Real.exp (-b * k)) < 1 := by
    calc C * (p * Real.exp (-b * k))
      = C * (p * Real.exp (-b * k)) := rfl
      _ < C * (1 / C) := by gcongr
      _ = 1 := by field_simp [hC.ne'] <;> ring
  calc C * p
    = C * p * (Real.exp (-b * k) * Real.exp (b * k)) := by rw [h2] <;> ring
    _ = (C * (p * Real.exp (-b * k))) * Real.exp (b * k) := by ring
    _ < 1 * Real.exp (b * k) := by gcongr
    _ = Real.exp (b * k) := by ring

/-- Monotonicity of real power in the base: `0 ≤ x ≤ y`, `0 ≤ a` implies `x^a ≤ y^a`. -/
lemma rpow_base_mono {x y a : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (ha : 0 ≤ a) :
    x ^ a ≤ y ^ a :=
  Real.rpow_le_rpow hx hxy ha

/-- Helper: `1/4 ≤ (Real.exp 1)⁻¹` since `Real.exp 1 < 3 < 4`. -/
lemma one_fourth_le_exp_neg_one : (1 : ℝ) / 4 ≤ (Real.exp 1)⁻¹ := by
  have h3 : Real.exp 1 ≤ 4 := by
    have h4 : Real.exp 1 < 3 := Real.exp_one_lt_three
    linarith
  have h5 : 0 < Real.exp 1 := Real.exp_pos 1
  have h6 : (Real.exp 1)⁻¹ = 1 / (Real.exp 1) := by exact inv_eq_one_div (Real.exp 1)
  rw [h6]
  exact one_div_le_one_div_of_le h5 h3

/-- Helper: `conversionKGeo` is monotone in its argument. -/
lemma conversionKGeo_monotone {s t : ℝ} (h : s ≤ t) :
    conversionKGeo s ≤ conversionKGeo t := by
  dsimp only [conversionKGeo]
  have h1 : Real.rpow 2 s ≤ Real.rpow 2 t :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) h
  exact mul_le_mul_of_nonneg_left h1 (by norm_num)

/-- Helper: A_log comparison for the normal base case branch.

    Given `0 < K`, `s ≤ 2`, and
    `h_log_ge_A : Real.log (1/δ) ≥ K * conversionKGeo 2 * 13 * 2^s`,
    conclude `Real.log (1/δ) ≥ K * conversionKGeo s * 13 * 2^s`. -/
lemma A_log_compare (K s : ℝ) (hK_pos : 0 < K) (hs_le2 : s ≤ 2)
    {δ : ℝ} (h_log_ge_A : Real.log (1 / δ) ≥ K * conversionKGeo 2 * 13 * Real.rpow 2 s) :
    Real.log (1 / δ) ≥ K * conversionKGeo s * 13 * Real.rpow 2 s := by
  have h_conv : conversionKGeo s ≤ conversionKGeo 2 := conversionKGeo_monotone hs_le2
  have h_rp_pos : 0 < Real.rpow 2 s := Real.rpow_pos_of_pos (by norm_num) s
  have h_factor_pos : 0 ≤ K * (13 : ℝ) * Real.rpow 2 s := by positivity
  have h_mul : K * conversionKGeo 2 * 13 * Real.rpow 2 s ≥
      K * conversionKGeo s * 13 * Real.rpow 2 s := by
    have h10 : K * conversionKGeo 2 * 13 * Real.rpow 2 s =
        (K * (13 : ℝ) * Real.rpow 2 s) * conversionKGeo 2 := by ring
    have h11 : K * conversionKGeo s * 13 * Real.rpow 2 s =
        (K * (13 : ℝ) * Real.rpow 2 s) * conversionKGeo s := by ring
    rw [h10, h11]
    exact mul_le_mul_of_nonneg_left h_conv h_factor_pos
  exact le_trans h_mul h_log_ge_A

/-- Reorder KSpec binders: move `m, 2≤m` before `C_P, C_T, M`. -/
lemma kspec_adapter
    {s K : ℝ}
    (hK_spec_all : ∀ (t : ℝ), s ≤ t → t ≤ 1 → KSpec s t K) :
    ∀ (t : ℝ), s ≤ t → t ≤ 1 →
      ∀ (m : ℕ), 2 ≤ m →
        ∀ (C_P C_T M : ℝ), 0 < C_P → 1 ≤ C_P → 0 < C_T → 1 ≤ C_T → 1 ≤ M →
          ∀ (P : Finset (DSquare m)), P.Nonempty →
            IsFinsetDeltaSSet (DiscretisedFurstenbergEstimate.δ m) t C_P P →
            (∀ (x y : DSquare m), x ∈ P → y ∈ P → dist x y ≤ 3) →
            (∀ p ∈ P, ∀ (x : ℝ × ℝ), x ∈ p.toSet → |x.1| ≤ 1) →
            ∀ (Tp : TubeFamily m),
              (∀ p ∈ P, ∀ T ∈ Tp p, (T.toSet ∩ p.toSet).Nonempty) →
              (∀ p ∈ P, ∀ T ∈ Tp p, |T.slope| ≤ 1) →
              (∀ p ∈ P, IsFinsetDeltaSSet (DiscretisedFurstenbergEstimate.δ m) s C_T (Tp p)) →
              (∀ p ∈ P, M / 2 < (Tp p).card ∧ (Tp p).card ≤ M) →
                let T := P.biUnion fun p => Tp p
                (T.card : ℝ) ≥ (1 / K) * Real.log (1 / DiscretisedFurstenbergEstimate.δ m) ^ (-K) *
                  (1 / (C_P * C_T)) * M * (DiscretisedFurstenbergEstimate.δ m) ^ (-s) *
                    (M * (DiscretisedFurstenbergEstimate.δ m) ^ s) ^ ((t - s) / (1 - s)) := by
  intro t hst ht1 m hm C_P C_T M hCP_pos hCP hCT_pos hCT hM
  exact hK_spec_all t hst ht1 (n := m) C_P C_T M hCP_pos hCP hCT_pos hCT hM hm

/-- If `KSpec s t K1` holds and `K1 ≤ K2`, then `KSpec s t K2` holds.
    The bound `(1/K) * L^(-K)` weakens as K increases. -/
lemma KSpec_weaken (s t : ℝ) {K1 K2 : ℝ} (hK1_pos : 0 < K1) (hK2_pos : 0 < K2)
    (hK_le : K1 ≤ K2) (h : KSpec s t K1) : KSpec s t K2 := by
  intro n C_P C_T M hCP_pos hCP hCT_pos hCT hM hn P hP_nonempty hP_set h_diam h_unit Tp h_intersect h_slope h_tube_sset h_size
  have h_main := @h n C_P C_T M hCP_pos hCP hCT_pos hCT hM hn P hP_nonempty hP_set h_diam h_unit Tp h_intersect h_slope h_tube_sset h_size
  have hδ_pos : 0 < DiscretisedFurstenbergEstimate.δ n := by
    simp [DiscretisedFurstenbergEstimate.δ] <;> positivity
  have hδ_le_quarter : DiscretisedFurstenbergEstimate.δ n ≤ 1 / 4 := by
    have h2 : n ≥ 2 := hn
    have h5 : DiscretisedFurstenbergEstimate.δ n = (2 : ℝ) ^ (- (n : ℤ)) := by
      simp [DiscretisedFurstenbergEstimate.δ] <;> ring
    rw [h5]
    have h3 : (2 : ℝ) ^ (- (n : ℤ)) ≤ (2 : ℝ) ^ (- (2 : ℤ)) := by
      gcongr <;> norm_cast <;> omega
    have h4 : (2 : ℝ) ^ (- (2 : ℤ)) = 1 / 4 := by norm_num
    rw [h4] at h3; exact h3
  have hL_ge1 : 1 ≤ Real.log (1 / DiscretisedFurstenbergEstimate.δ n) := by
    have h1 : (1 : ℝ) / DiscretisedFurstenbergEstimate.δ n ≥ 4 := by
      calc 1 / DiscretisedFurstenbergEstimate.δ n ≥ 1 / (1 / 4) := by gcongr
      _ = 4 := by norm_num
    have h5 : Real.log (1 / DiscretisedFurstenbergEstimate.δ n) ≥ Real.log 4 :=
      Real.log_le_log (by positivity) h1
    have h6 : (1 : ℝ) < Real.log 4 := by
      have h7 : Real.exp 1 < (4 : ℝ) := by linarith [Real.exp_one_lt_d9]
      have h8 : Real.log (Real.exp 1) < Real.log 4 := Real.log_lt_log (by positivity) h7
      have h9 : Real.log (Real.exp 1) = 1 := Real.log_exp 1
      rw [h9] at h8; exact h8
    linarith
  set L : ℝ := Real.log (1 / DiscretisedFurstenbergEstimate.δ n) with hL_def
  have hL_pos : 0 < L := by linarith
  have h1 : (1 / K2) * L ^ (-K2) ≤ (1 / K1) * L ^ (-K1) := by
    have h2 : (1 / K2) ≤ (1 / K1) := by
      gcongr
    have h3 : L ^ (-K2) ≤ L ^ (-K1) := by
      apply Real.rpow_le_rpow_of_exponent_le hL_ge1
      linarith [hK_le]
    exact mul_le_mul h2 h3 (by positivity) (by positivity)
  set Z : ℝ := (1 / (C_P * C_T)) * M * (DiscretisedFurstenbergEstimate.δ n) ^ (-s) *
      (M * (DiscretisedFurstenbergEstimate.δ n) ^ s) ^ ((t - s) / (1 - s)) with hZ
  have hZ_pos : 0 < Z := by positivity
  have h5 : (1 / K2) * L ^ (-K2) * Z ≤ (1 / K1) * L ^ (-K1) * Z :=
    mul_le_mul_of_nonneg_right h1 hZ_pos.le
  have h4 : (1 / K2) * L ^ (-K2) * (1 / (C_P * C_T)) * M * (DiscretisedFurstenbergEstimate.δ n) ^ (-s) *
      (M * (DiscretisedFurstenbergEstimate.δ n) ^ s) ^ ((t - s) / (1 - s)) ≤
    (1 / K1) * L ^ (-K1) * (1 / (C_P * C_T)) * M * (DiscretisedFurstenbergEstimate.δ n) ^ (-s) *
      (M * (DiscretisedFurstenbergEstimate.δ n) ^ s) ^ ((t - s) / (1 - s)) := by
    simpa [hZ, mul_assoc] using h5
  exact le_trans h4 h_main

/-- Positivity of combiningC for n > 0 and C_P ≥ 1. -/
lemma combiningC_pos (τ K : ℝ) (hK : 0 < K) (hτ : 0 < τ) :
    ∀ (n : ℕ), 0 < n → ∀ (C_P : ℝ), 1 ≤ C_P → 0 < combiningC τ K n C_P := by
  intro n hn
  induction n with
  | zero =>
    exfalso
    linarith
  | succ n' ih =>
    intro C_P hCP
    by_cases h : n' = 0
    · subst h
      simp only [combiningC]
      <;> linarith
    · obtain ⟨m, rfl⟩ : ∃ m, n' = m + 1 := by
        refine' ⟨n' - 1, _⟩
        omega
      simp only [combiningC]
      have h_n'_pos : 0 < m + 1 := by omega
      set C_P_fine : ℝ := C_P + 2 * (((m + 2 : ℕ) : ℝ) + 4) with hC_P_fine
      have hCP_fine : 1 ≤ C_P_fine := by
        dsimp only [C_P_fine]
        linarith
      have h_pos_rec : 0 < combiningC τ K (m + 1) C_P_fine := ih h_n'_pos C_P_fine hCP_fine
      have h_pos1 : 0 < (1 + (7 : ℝ)) * (1 + (1 : ℝ) + combiningCprime (m + 1) τ) := by
        have h_cc_pos : 0 < combiningCprime (m + 1) τ := combiningCprime_pos (by omega) hτ
        positivity
      have hK' : 0 < K := hK
      have hC_P' : 0 < C_P := by linarith
      have h8 : 0 < (8 : ℝ) := by norm_num
      have h_eq2 : C_P + 2 * (↑m + 2 + 4) = C_P_fine := by
        dsimp only [C_P_fine]
        simp [Nat.cast_add]
        <;> ring
      rw [h_eq2]
      exact add_pos (add_pos (add_pos (add_pos h_pos1 hK') hC_P') h8) h_pos_rec

/-! ### Bounded uniform _with_data induction -/

/-- Extract per-(τ,n) data from the refactored bounded induction to obtain
    the ordinary CombiningInductionUniform_with_data. -/
lemma bounded_uniform_implies_uniform_with_data
    {s t τ ε_inc K : ℝ} {n : ℕ}
    (hK : 1 ≤ K)
    (hτ : 0 < τ) (hτ1 : τ < 1) (hn : 0 < n)
    (h_uniform : UniformIncidenceData s t ε_inc)
    (h : CombiningInductionUniform_with_data_bounded s t ε_inc K) :
    CombiningInductionUniform_with_data s t τ ε_inc n := by
  rcases h hK with ⟨ε_G0, η0, hεG0_pos, hη0_pos, hsmall, h_main⟩
  rcases h_main τ hτ hτ1 n hn with ⟨lam_0, hlam0_pos, h_body⟩
  let C' : ℝ := combiningCprime n τ
  have hC'_pos : 0 < C' := combiningCprime_pos hn hτ
  refine' ⟨ε_G0, η0, lam_0, C', hεG0_pos, hη0_pos, hlam0_pos, hC'_pos, hsmall, _⟩
  intro C_P hCP
  have hC_pos : 0 < combiningC τ K n C_P := (h_body C_P hCP).1
  let C : ℝ := combiningC τ K n C_P
  refine' ⟨C, hC_pos, _⟩
  intro ε_G η ε_N lam hεG hεG_le hη hη_le hεN hεN_le hlam hlam_le h_uniform
  have h_outer := (h_body C_P hCP).2 ε_N lam hεN hlam hlam_le h_uniform
  rcases h_outer with ⟨δ₀, hδ₀_pos, h_inner⟩
  exact ⟨δ₀, hδ₀_pos, h_inner ε_G η hεG hεG_le hεN_le hη hη_le⟩

/-- Base case n=1 with pre-specified ε_G0, η0, K (for quantifier-refactored induction).

    K depends only on s (from uniform Corollary 2.5). δ₀ is chosen based only on
    K, C_P (NOT ε_G, η), achieving the uniform quantifier order required by OS Prop 7.3. -/
lemma base_case_inner
    (s t τ ε_inc ε_G0 η0 K : ℝ)
    (hs : 0 < s) (hst : s < t) (hs1 : s < 1)
    (hτ : 0 < τ) (hτ1 : τ < 1)
    (hε_inc_pos : 0 < ε_inc)
    (hεG0_pos : 0 < ε_G0) (hεG0_lt_εinc : ε_G0 < ε_inc) (hη0_pos : 0 < η0)
    (hK_ge1 : 1 ≤ K)
    (hK_spec_all : ∀ (t : ℝ), s ≤ t → t ≤ 1 → KSpec s t K)
    (hsmall : ∀ (ε_G η : ℝ), 0 < ε_G → ε_G ≤ ε_G0 → 0 < η → η ≤ η0 →
      (η + 2 * ε_G) * (1 - s) / (min t 1 - s) + η ≤ ε_inc) :
    ∃ (lam_0 : ℝ), 0 < lam_0 ∧
      ∀ (C_P : ℝ), 1 ≤ C_P →
        0 < combiningC τ K 1 C_P ∧
        ∀ (ε_N lam : ℝ), 0 < ε_N → 0 < lam → lam ≤ lam_0 →
          ∀ (h_uniform : UniformIncidenceData s t ε_inc),
            ∃ (δ₀ : ℝ), 0 < δ₀ ∧
            ∀ (ε_G η : ℝ), 0 < ε_G → ε_G ≤ ε_G0 → ε_N ≤ ε_G →
              0 < η → η ≤ η0 →
                ∀ (k : ℕ), dyadicDelta k ≤ δ₀ →
                  ∀ (M : ℕ)
                    (config : CTNiceConfiguration k s (Real.rpow (dyadicDelta k) (-lam)) M)
                    (Δ : Fin 2 → ℝ)
                    (scaleClass : Fin 1 → ScaleClass)
                    (N : Fin 1 → ℕ)
                    (C_between : Fin 1 → ℝ),
                    CombiningConfig s t τ 1 ε_G η lam ε_N C_P C_between k M config Δ scaleClass N →
                    B1BridgeHypotheses k config →
                    CombiningExtraHypotheses_v2 s t ε_G η ε_N C_P ε_inc 1 lam k M config Δ scaleClass →
                    CombiningConclusion s t τ ε_G η ε_N C_P
                      (combiningC τ K 1 C_P) (combiningCprime 1 τ) lam 1 Δ scaleClass k M config := by
  let u : ℝ := min t 1
  have hu_le_one : u ≤ 1 := min_le_right _ _
  have hs_lt_u : s < u := lt_min hst hs1
  have hK_pos : 0 < K := by linarith
  -- lam_0 must be < τ*ε_inc to absorb CΔ' ≤ δ_k^{-lam} into δ_m^{-ε_inc} ≥ δ_k^{-τ*ε_inc}
  let lam_0 : ℝ := min 1 (τ * ε_inc / 2)
  have hlam0_pos : 0 < lam_0 := by
    dsimp only [lam_0]
    have h1 : 0 < τ * ε_inc / 2 := by positivity
    have h2 : 0 < min (1 : ℝ) (τ * ε_inc / 2) := by positivity
    exact h2
  refine' ⟨lam_0, hlam0_pos, _⟩
  intro C_P hCP
  have hC_pos : 0 < combiningC τ K 1 C_P := by
    simp [combiningC] <;> linarith [hK_ge1]
  have hC_ge : K + C_P + 1 ≤ combiningC τ K 1 C_P := by
    simp [combiningC] <;> norm_num
  have hC'_ge : 1 ≤ combiningCprime 1 τ := by
    have h1 : combiningCprime 1 τ = 2 := by
      simp [combiningCprime, Finset.sum_range_succ] <;> norm_num
    rw [h1] <;> norm_num
  refine' ⟨hC_pos, _⟩
  intro ε_N lam hεN hlam hlam_le
  intro (h_uniform : UniformIncidenceData s t ε_inc)
  let A_log : ℝ := K * conversionKGeo 2 * 13 * Real.rpow 2 s
  have hA_log_nonneg : 0 ≤ A_log := by
    have h1 : 0 ≤ K := by linarith
    have h2 : 0 ≤ conversionKGeo 2 := by
      dsimp only [conversionKGeo]; exact mul_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num) 2)
    have h3 : 0 ≤ Real.rpow 2 s := Real.rpow_nonneg (by norm_num) s
    positivity
  -- Absorption threshold: worst case ε_G = ε_G0 gives smallest exponent ε_inc - ε_G0
  have h_xmin_pos : 0 < ε_inc - ε_G0 := by linarith
  rcases DirecretisedFurstenbergEstimate.RealAnalysis.log_pow_le_rpow_neg C_P (ε_inc - ε_G0) h_xmin_pos with ⟨δ_abs, hδ_abs_pos, hδ_abs_iff⟩
  let δ_abs' : ℝ := δ_abs / 2
  have hδ_abs'_pos : 0 < δ_abs' := by positivity
  have hδ_abs'_lt : δ_abs' < δ_abs := by
    dsimp only [δ_abs']
    have h : δ_abs / 2 < δ_abs := by
      exact div_lt_self hδ_abs_pos (by norm_num)
    exact h
  let δ₀ : ℝ := min (min (1 / 4) (Real.exp (-A_log))) (min h_uniform.δR δ_abs')
  have hδ₀_pos : 0 < δ₀ := by
    dsimp only [δ₀]
    have h1 : 0 < min (1 / 4) (Real.exp (-A_log)) := by positivity
    have h2 : 0 < min h_uniform.δR δ_abs' := lt_min h_uniform.hδR_pos hδ_abs'_pos
    exact lt_min h1 h2
  have hδ₀_le_quarter : δ₀ ≤ 1 / 4 := by
    dsimp only [δ₀]
    have h : δ₀ ≤ min (1 / 4) (Real.exp (-A_log)) := min_le_left _ _
    exact le_trans h (min_le_left _ _)
  have hδ₀_le_exp : δ₀ ≤ Real.exp (-A_log) := by
    dsimp only [δ₀]
    have h : δ₀ ≤ min (1 / 4) (Real.exp (-A_log)) := min_le_left _ _
    exact le_trans h (min_le_right _ _)
  have hδ₀_le_δR : δ₀ ≤ h_uniform.δR := by
    dsimp only [δ₀]
    have h : δ₀ ≤ min h_uniform.δR δ_abs' := min_le_right _ _
    exact le_trans h (min_le_left _ _)
  have hδ₀_le_abs' : δ₀ ≤ δ_abs' := by
    dsimp only [δ₀]
    have h : δ₀ ≤ min h_uniform.δR δ_abs' := min_le_right _ _
    exact le_trans h (min_le_right _ _)
  refine' ⟨δ₀, hδ₀_pos, _⟩
  intro ε_G η hεG hεG_le hεN_le hη hη_le
  intro k hk M config Δ scaleClass N C_between hcfg hB1 hextra
  have hδ_le_δ₀ : dyadicDelta k ≤ δ₀ := hk
  have hδ_le_quarter : dyadicDelta k ≤ 1 / 4 := le_trans hδ_le_δ₀ hδ₀_le_quarter
  have hk_ge_2 : 2 ≤ k := by
    by_contra h9
    have h10 : k < 2 := by omega
    have h11 : k = 0 ∨ k = 1 := by omega
    rcases h11 with (rfl | rfl)
    · norm_num [dyadicDelta] at hδ_le_quarter <;> linarith
    · norm_num [dyadicDelta] at hδ_le_quarter <;> linarith
  have hk_exp1 : dyadicDelta k ≤ Real.exp (-1) := by
    have h1 : dyadicDelta k ≤ (1 : ℝ) / 4 := hδ_le_quarter
    have h2 : (1 : ℝ) / 4 ≤ Real.exp (-1) := by
      have h3 : Real.exp 1 ≤ 4 := by
        have h4 : Real.exp 1 < 3 := Real.exp_one_lt_three
        linarith
      have h5 : 0 < Real.exp 1 := Real.exp_pos 1
      have h6 : Real.exp (-1) = (Real.exp 1)⁻¹ := by rw [Real.exp_neg]
      rw [h6]
      have h7 : (1 : ℝ) / 4 ≤ (Real.exp 1)⁻¹ := one_fourth_le_exp_neg_one
      exact h7
    exact le_trans h1 h2
  have hδ_pos : 0 < dyadicDelta k := dyadicDelta_pos k
  have hδ_lt_one : dyadicDelta k < 1 := by
    have h1 : (k : ℕ) ≥ 2 := hk_ge_2
    have h2 : dyadicDelta k = ((2 : ℝ)^k)⁻¹ := by
      simp [dyadicDelta, zpow_neg, zpow_ofNat] <;> ring
    rw [h2]
    have h3 : (2 : ℝ)^k > 1 := by
      have h4 : (2 : ℝ)^k ≥ (2 : ℝ)^(2 : ℕ) := by gcongr <;> norm_num
      norm_num at h4 ⊢ <;> linarith
    have h5 : 0 < (2 : ℝ)^k := by positivity
    have h6 : ((2 : ℝ)^k)⁻¹ < 1 := by
      have h7 : 1 < (2 : ℝ)^k := h3
      have h8 : 0 < (2 : ℝ)^k := by positivity
      calc ((2 : ℝ)^k)⁻¹
        = 1 / (2 : ℝ)^k := by simp
      _ < 1 := by apply (div_lt_one h8).mpr; exact h7
    exact h6
  have h_log_ge_A : Real.log (1 / dyadicDelta k) ≥ A_log := by
    have h1 : dyadicDelta k ≤ Real.exp (-A_log) := le_trans hδ_le_δ₀ hδ₀_le_exp
    have h2 : 0 < dyadicDelta k := hδ_pos
    have h3 : 1 / dyadicDelta k ≥ Real.exp A_log := by
      have h4 : dyadicDelta k ≤ Real.exp (-A_log) := h1
      have h5 : 0 < Real.exp (-A_log) := Real.exp_pos _
      have h6 : 1 / dyadicDelta k ≥ 1 / Real.exp (-A_log) := one_div_le_one_div_of_le h2 h4
      have h7 : 1 / Real.exp (-A_log) = Real.exp A_log := by
        have h8 : Real.exp (-A_log) * Real.exp A_log = 1 := by
          have h9 : Real.exp (-A_log) * Real.exp A_log = Real.exp ((-A_log) + A_log) := by
            rw [← Real.exp_add]
          rw [h9]
          have h10 : (-A_log) + A_log = 0 := by ring
          rw [h10, Real.exp_zero]
        field_simp [(Real.exp_pos (-A_log)).ne'] <;> linarith
      rw [h7] at h6
      exact h6
    have h9 : Real.log (1 / dyadicDelta k) ≥ Real.log (Real.exp A_log) :=
      Real.log_le_log (by positivity) h3
    have h10 : Real.log (Real.exp A_log) = A_log := Real.log_exp A_log
    rw [h10] at h9
    exact h9
  have hL_ge_one : 1 ≤ Real.log (1 / dyadicDelta k) := by
    have h1 : dyadicDelta k ≤ 1 / 4 := hδ_le_quarter
    have h2 : 0 < dyadicDelta k := hδ_pos
    have h3 : 1 / dyadicDelta k ≥ 4 := by
      calc 1 / dyadicDelta k ≥ 1 / (1 / 4) := by gcongr
      _ = 4 := by norm_num
    have h4 : Real.log (1 / dyadicDelta k) ≥ Real.log 4 := Real.log_le_log (by positivity) h3
    have h5 : (1 : ℝ) < Real.log 4 := by
      have h6 : Real.exp 1 < (4 : ℝ) := by linarith [Real.exp_one_lt_d9]
      have h7 : Real.log (Real.exp 1) < Real.log 4 := Real.log_lt_log (by positivity) h6
      have h8 : Real.log (Real.exp 1) = 1 := Real.log_exp 1
      rw [h8] at h7; exact h7
    linarith
  cases h_sc0 : scaleClass 0 with
  | normal =>
    have hK_spec_s : KSpec s s K := hK_spec_all s (by linarith) (by linarith)
    -- Phase 2: derive global S-set from single block between-scales property
    have hP_nonempty_dispatch : config.P₀.Nonempty := by
      have h1 : config.pointSet.Nonempty := hcfg.h_uniform.1
      rcases h1 with ⟨x, hx⟩
      simp only [NiceConfiguration.pointSet, Set.mem_iUnion] at hx
      rcases hx with ⟨p, hp, _⟩
      exact ⟨p, hp⟩
    have h_normal_raw : IsSetBetweenScales config.pointSet (dyadicDelta k) 1 s (C_between 0) := by
      have h1 : (Fin.succ (0 : Fin 1) : Fin 2) = 1 := by decide
      have h2 : (Fin.castSucc (0 : Fin 1) : Fin 2) = 0 := by decide
      have hΔ0 : Δ 0 = 1 := hcfg.hΔ_start
      have hΔ1 : Δ 1 = dyadicDelta k := hcfg.hΔ_end
      simpa [h1, h2, hΔ1, hΔ0] using hcfg.h_normal 0 h_sc0
    let C_point : ℝ := conversionKGeo s * C_between 0
    have hC_between_pos : 0 < C_between 0 := h_normal_raw.2.2.2.2.1
    have hC_point_pos : 0 < C_point := by
      dsimp only [C_point]
      have hK_geo_pos : 0 < conversionKGeo s := by
        dsimp only [conversionKGeo]
        have h1 : 0 < Real.rpow 2 s := Real.rpow_pos_of_pos (by norm_num) s
        exact mul_pos (by norm_num) h1
      exact mul_pos hK_geo_pos hC_between_pos
    have hP_set_base : IsFinsetDeltaSSet (dyadicDelta k) s C_point
        (finsetDyadicToDSquare config.P₀) :=
      isSetBetweenScales_to_isFinsetDeltaSSet hP_nonempty_dispatch hs.le h_normal_raw
    have hC_point_bound : C_point ≤ conversionKGeo s * (Real.log (1 / dyadicDelta k)) ^ C_P * Real.rpow (dyadicDelta k) (-ε_N) := by
      have h1 : C_between 0 ≤ (Real.log (1 / dyadicDelta k)) ^ C_P * Real.rpow (dyadicDelta k) (-ε_N) := by
        have h2 := hcfg.h_C_between_normal 0 h_sc0
        have hfi1 : (Fin.succ (0 : Fin 1) : Fin 2) = 1 := by decide
        have hfi2 : (Fin.castSucc (0 : Fin 1) : Fin 2) = 0 := by decide
        have hΔ0 : Δ 0 = 1 := hcfg.hΔ_start
        have hΔ1 : Δ 1 = dyadicDelta k := hcfg.hΔ_end
        have h3 : Δ (Fin.castSucc (0 : Fin 1)) / Δ (Fin.succ (0 : Fin 1)) = (1 : ℝ) / dyadicDelta k := by
          rw [hfi2, hfi1, hΔ0, hΔ1] <;> ring
        rw [h3] at h2
        have h4 : ((1 : ℝ) / dyadicDelta k) ^ ε_N = Real.rpow (dyadicDelta k) (-ε_N) := by
          have h51 : (1 / dyadicDelta k) = (dyadicDelta k)⁻¹ := by ring
          rw [h51]
          have h52 : (dyadicDelta k)⁻¹ ^ ε_N = (Real.rpow (dyadicDelta k) ε_N)⁻¹ := Real.inv_rpow hδ_pos.le ε_N
          have h53 : (Real.rpow (dyadicDelta k) ε_N)⁻¹ = Real.rpow (dyadicDelta k) (-ε_N) := (Real.rpow_neg hδ_pos.le ε_N).symm
          rw [h52, h53]
        rw [h4] at h2
        exact h2
      dsimp only [C_point]
      have hK_geo_nonneg : 0 ≤ conversionKGeo s := by
        dsimp only [conversionKGeo]
        have h_rp_pos : 0 < Real.rpow 2 s := Real.rpow_pos_of_pos (by norm_num) s
        exact mul_nonneg (by norm_num) h_rp_pos.le
      have h_mul : conversionKGeo s * C_between 0 ≤ conversionKGeo s * ((Real.log (1 / dyadicDelta k)) ^ C_P * Real.rpow (dyadicDelta k) (-ε_N)) :=
        mul_le_mul_of_nonneg_left h1 hK_geo_nonneg
      simpa [mul_assoc] using h_mul
    have h_log_ge_s : Real.log (1 / dyadicDelta k) ≥ K * conversionKGeo s * 13 * Real.rpow 2 s := by
      have h_conv_s_le_2 : conversionKGeo s ≤ conversionKGeo 2 := by
        dsimp only [conversionKGeo]
        have h1 : s ≤ (2 : ℝ) := by linarith
        have h2 : Real.rpow 2 s ≤ Real.rpow 2 (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
        exact mul_le_mul_of_nonneg_left h2 (by norm_num)
      calc Real.log (1 / dyadicDelta k)
        ≥ K * conversionKGeo 2 * 13 * Real.rpow 2 s := h_log_ge_A
      _ ≥ K * conversionKGeo s * 13 * Real.rpow 2 s := by
        have h_conv : conversionKGeo s ≤ conversionKGeo 2 := conversionKGeo_monotone (by linarith)
        have h_rpow_pos : 0 < Real.rpow 2 s := Real.rpow_pos_of_pos (by norm_num) s
        have h_factor_pos : 0 ≤ K * (13 : ℝ) * Real.rpow 2 s := by
          have h1 : 0 < K := hK_pos
          have h2 : 0 < (13 : ℝ) := by norm_num
          exact mul_nonneg (mul_nonneg h1.le h2.le) h_rpow_pos.le
        have h10 : K * conversionKGeo 2 * 13 * Real.rpow 2 s =
            (K * (13 : ℝ) * Real.rpow 2 s) * conversionKGeo 2 := by ring
        have h11 : K * conversionKGeo s * 13 * Real.rpow 2 s =
            (K * (13 : ℝ) * Real.rpow 2 s) * conversionKGeo s := by ring
        rw [h10, h11]
        exact mul_le_mul_of_nonneg_left h_conv h_factor_pos
    exact base_case_normal_branch_v2 K hK_pos hK_spec_s hs hs1 hτ hτ1 hεG hη hεN hεN_le hCP hlam
      h_log_ge_s hk_ge_2 h_sc0 hcfg hB1 hP_set_base hC_point_pos hC_point_bound hextra.h_slope hC_ge hC'_ge
  | good t_j =>
    have hK_spec_u : KSpec s u K := hK_spec_all u (by linarith) hu_le_one
    have hΔ0 : Δ 0 = 1 := hcfg.hΔ_start
    have hΔ1 : Δ 1 = dyadicDelta k := hcfg.hΔ_end
    -- Phase 2: derive global S-set from single block between-scales property
    have hP_nonempty_dispatch : config.P₀.Nonempty := by
      have h1 : config.pointSet.Nonempty := hcfg.h_uniform.1
      rcases h1 with ⟨x, hx⟩
      simp only [NiceConfiguration.pointSet, Set.mem_iUnion] at hx
      rcases hx with ⟨p, hp, _⟩
      exact ⟨p, hp⟩
    have h_good_raw := hcfg.h_good (0 : Fin 1) t_j h_sc0
    have h_good_scaled : IsRegularBetweenScales config.pointSet (dyadicDelta k) 1 t_j (C_between 0) (C_between 0) := by
      have h1 : (Fin.succ (0 : Fin 1) : Fin 2) = 1 := by decide
      have h2 : (Fin.castSucc (0 : Fin 1) : Fin 2) = 0 := by decide
      simpa [h1, h2, hΔ1, hΔ0] using h_good_raw
    let C_point_raw : ℝ := conversionKGeo t_j * (C_between 0)
    let C_point : ℝ := max C_point_raw 1
    have hC_point_pos : 0 < C_point := by positivity
    have hC_point_ge1 : 1 ≤ C_point := le_max_right _ _
    have h_tj_pos : 0 < t_j := by
      have h1 : s < t_j := by
        have h2 : s < t := hst
        have h3 : t ≤ t_j := hextra.h_tj_ge_t (0 : Fin 1) t_j h_sc0
        linarith
      linarith
    have hP_set_tj_raw : IsFinsetDeltaSSet (dyadicDelta k) t_j C_point_raw
        (finsetDyadicToDSquare config.P₀) :=
      isSetBetweenScales_to_isFinsetDeltaSSet hP_nonempty_dispatch h_tj_pos.le
        h_good_scaled.1
    have hP_set_tj_const : IsFinsetDeltaSSet (dyadicDelta k) t_j C_point
        (finsetDyadicToDSquare config.P₀) :=
      IsDeltaSSet.weaken_constant' hP_set_tj_raw (le_max_left _ _) hC_point_pos
    have h_min_tj_pos : 0 ≤ min t_j 1 := by positivity
    have h_min_le_tj : min t_j 1 ≤ t_j := min_le_left _ _
    have hP_set_tj_base : IsFinsetDeltaSSet (dyadicDelta k) (min t_j 1) C_point
        (finsetDyadicToDSquare config.P₀) :=
      finset_deltaSSet_weaken_exponent hP_set_tj_const h_min_tj_pos h_min_le_tj hC_point_ge1
    have hC_between_bound : C_between 0 ≤ (Real.log (1 / dyadicDelta k)) ^ C_P *
        Real.rpow (dyadicDelta k) (-ε_G) := by
      have h1 := hcfg.h_C_between_good 0 t_j h_sc0
      have hfi1 : (Fin.succ (0 : Fin 1) : Fin 2) = 1 := by decide
      have hfi2 : (Fin.castSucc (0 : Fin 1) : Fin 2) = 0 := by decide
      have h4 : (1 / dyadicDelta k) ^ ε_G = Real.rpow (dyadicDelta k) (-ε_G) := by
        have h51 : (1 / dyadicDelta k) = (dyadicDelta k)⁻¹ := by ring
        rw [h51]
        have h52 : (dyadicDelta k)⁻¹ ^ ε_G = (Real.rpow (dyadicDelta k) ε_G)⁻¹ := Real.inv_rpow hδ_pos.le ε_G
        have h53 : (Real.rpow (dyadicDelta k) ε_G)⁻¹ = Real.rpow (dyadicDelta k) (-ε_G) := (Real.rpow_neg hδ_pos.le ε_G).symm
        rw [h52, h53]
      have h1' : C_between 0 ≤ (Real.log (1 / dyadicDelta k)) ^ C_P * (1 / dyadicDelta k) ^ ε_G := by
        simpa [hfi1, hfi2, hΔ1, hΔ0] using h1
      rw [h4] at h1'
      exact h1'
    have hC_point_bound : C_point ≤ conversionKGeo t_j * (Real.log (1 / dyadicDelta k)) ^ C_P *
        Real.rpow (dyadicDelta k) (-ε_G) := by
      by_cases h : C_point_raw ≥ 1
      · have h4 : C_point = C_point_raw := by
          dsimp only [C_point]
          rw [max_eq_left h]
        rw [h4]
        dsimp only [C_point_raw]
        have h_pos : 0 ≤ conversionKGeo t_j := by
          dsimp only [conversionKGeo]
          have h1 : 0 < Real.rpow 2 t_j := Real.rpow_pos_of_pos (by norm_num) t_j
          exact mul_nonneg (by norm_num) h1.le
        have h5 : conversionKGeo t_j * C_between 0 ≤
            conversionKGeo t_j * ((Real.log (1 / dyadicDelta k)) ^ C_P * Real.rpow (dyadicDelta k) (-ε_G)) :=
          mul_le_mul_of_nonneg_left hC_between_bound h_pos
        linarith
      · have h4 : C_point = 1 := by
          dsimp only [C_point]
          have h' : C_point_raw ≤ 1 := by linarith [h]
          rw [max_eq_right h']
        rw [h4]
        have h5 : (1 : ℝ) ≤ conversionKGeo t_j := by
          dsimp only [conversionKGeo]
          have h6 : (1 : ℝ) ≤ Real.rpow 2 t_j := by
            have h61 : (1 : ℝ) ≤ (2 : ℝ) := by norm_num
            have h62 : 0 ≤ t_j := by linarith
            exact Real.one_le_rpow h61 h62
          nlinarith
        have h7 : (1 : ℝ) ≤ (Real.log (1 / dyadicDelta k)) ^ C_P := by
          have h8 : 1 ≤ Real.log (1 / dyadicDelta k) := hL_ge_one
          have h9 : 0 ≤ C_P := by linarith
          exact Real.one_le_rpow h8 h9
        have h10 : (1 : ℝ) ≤ Real.rpow (dyadicDelta k) (-ε_G) := by
          have h1 : Real.rpow (dyadicDelta k) ε_G ≤ 1 :=
            Real.rpow_le_one (by linarith) (by linarith) (by linarith)
          have h2 : 0 < Real.rpow (dyadicDelta k) ε_G := Real.rpow_pos_of_pos hδ_pos ε_G
          have h3 : Real.rpow (dyadicDelta k) (-ε_G) = (Real.rpow (dyadicDelta k) ε_G)⁻¹ := by
            exact Real.rpow_neg hδ_pos.le ε_G
          rw [h3]
          have h4 : (Real.rpow (dyadicDelta k) ε_G)⁻¹ ≥ 1 := by
            calc (Real.rpow (dyadicDelta k) ε_G)⁻¹
              ≥ (1 : ℝ)⁻¹ := by gcongr
            _ = 1 := by norm_num
          exact h4
        have h_mul1 : (1 : ℝ) ≤ conversionKGeo t_j * (Real.log (1 / dyadicDelta k)) ^ C_P := by
          have h : (1 : ℝ) * (1 : ℝ) ≤ conversionKGeo t_j * (Real.log (1 / dyadicDelta k)) ^ C_P :=
            mul_le_mul h5 h7 (by linarith) (by linarith)
          simpa using h
        have h_final : (1 : ℝ) ≤ conversionKGeo t_j * (Real.log (1 / dyadicDelta k)) ^ C_P * Real.rpow (dyadicDelta k) (-ε_G) := by
          have h : (1 : ℝ) * (1 : ℝ) ≤ (conversionKGeo t_j * (Real.log (1 / dyadicDelta k)) ^ C_P) * Real.rpow (dyadicDelta k) (-ε_G) :=
            mul_le_mul h_mul1 h10 (by linarith) (by linarith)
          simpa [mul_assoc] using h
        exact h_final
    have h_tj_le_two : t_j ≤ 2 := hextra.h_tj_le_two (0 : Fin 1) t_j h_sc0
    have hK_geo_mono : conversionKGeo t_j ≤ conversionKGeo 2 := by
      dsimp only [conversionKGeo]
      have h1 : t_j ≤ 2 := h_tj_le_two
      have h2 : 0 ≤ t_j := by linarith
      have h3 : Real.rpow 2 t_j ≤ Real.rpow 2 2 := Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
      have h4 : (2000 : ℝ) * Real.rpow 2 t_j ≤ (2000 : ℝ) * Real.rpow 2 2 :=
        mul_le_mul_of_nonneg_left h3 (by norm_num)
      exact h4
    have h_log_ge_good : Real.log (1 / dyadicDelta k) ≥ K * conversionKGeo t_j * 13 * Real.rpow 2 s := by
      have h_factor : 0 ≤ K * (13 : ℝ) * Real.rpow 2 s := by
        have hK_nonneg : 0 ≤ K := by linarith [hK_pos]
        have h13_pos : (0 : ℝ) < 13 := by norm_num
        have hrp_nonneg : 0 ≤ Real.rpow 2 s := Real.rpow_nonneg (by norm_num) s
        exact mul_nonneg (mul_nonneg hK_nonneg h13_pos.le) hrp_nonneg
      have h5 : K * conversionKGeo t_j * 13 * Real.rpow 2 s ≤ K * conversionKGeo 2 * 13 * Real.rpow 2 s := by
        have h6 : K * conversionKGeo t_j * 13 * Real.rpow 2 s = K * (13 : ℝ) * Real.rpow 2 s * conversionKGeo t_j := by ring
        have h7 : K * conversionKGeo 2 * 13 * Real.rpow 2 s = K * (13 : ℝ) * Real.rpow 2 s * conversionKGeo 2 := by ring
        rw [h6, h7]
        exact mul_le_mul_of_nonneg_left hK_geo_mono h_factor
      calc Real.log (1 / dyadicDelta k)
        ≥ K * conversionKGeo 2 * 13 * Real.rpow 2 s := h_log_ge_A
      _ ≥ K * conversionKGeo t_j * 13 * Real.rpow 2 s := h5
    -- Improved incidence via geometric bridge
    have h_improved_incidence : (config.T₀.card : ENNReal) ≥
        ENNReal.ofReal (Real.rpow (dyadicDelta k) (-(2 * s + ε_inc))) := by
      let δ : ℝ := dyadicDelta k
      have hδ_pos' : 0 < δ := dyadicDelta_pos k
      have hδ_lt_one' : δ < 1 := hδ_lt_one
      have hδ_le_R' : δ ≤ h_uniform.δR := by
        exact le_trans hk hδ₀_le_δR
      have hlam_le_εinc : lam ≤ ε_inc := by
        have h1 : lam ≤ lam_0 := hlam_le
        have h2 : lam_0 ≤ τ * ε_inc / 2 := by
          dsimp only [lam_0]
          exact min_le_right _ _
        have h3 : τ * ε_inc / 2 < ε_inc := by
          have h4 : τ < 1 := hτ1
          nlinarith
        linarith
      have h_config_unit : config.pointSet ⊆ dyadicSquare 1 0 0 :=
        pointSet_sub_dyadicSquare1 hB1.h_squares_unit
      have hP_nonempty : config.pointSet.Nonempty := hcfg.h_uniform.1
      have h_sqrt_reg : IsSquareRootRegular δ t_j (C_between 0) (C_between 0) config.pointSet :=
        square_root_regular_from_unit_between_scales h_good_scaled h_config_unit hP_nonempty
      -- Absorption: C_between 0 ≤ δ^{-ε_inc}
      have h_x_ge : ε_inc - ε_G ≥ ε_inc - ε_G0 := by linarith [hεG_le]
      have hδ_lt_abs : δ < δ_abs := by
        have h1 : δ ≤ δ₀ := hk
        have h2 : δ₀ ≤ δ_abs' := hδ₀_le_abs'
        have h3 : δ_abs' < δ_abs := hδ_abs'_lt
        linarith
      have h_absorption0 : (Real.log (1 / δ)) ^ C_P ≤ δ ^ (-(ε_inc - ε_G0)) :=
        hδ_abs_iff δ hδ_pos' hδ_lt_abs
      have h_absorption : (Real.log (1 / δ)) ^ C_P ≤ Real.rpow δ (-(ε_inc - ε_G)) := by
        have h1 : δ ^ (-(ε_inc - ε_G0)) = Real.rpow δ (-(ε_inc - ε_G0)) := by rfl
        rw [h1] at h_absorption0
        have h2 : Real.rpow δ (-(ε_inc - ε_G0)) ≤ Real.rpow δ (-(ε_inc - ε_G)) := by
          have h3 : -(ε_inc - ε_G) ≤ -(ε_inc - ε_G0) := by linarith [hεG_le]
          exact Real.rpow_le_rpow_of_exponent_ge hδ_pos' hδ_lt_one'.le h3
        exact le_trans h_absorption0 h2
      have hCb_abs : C_between 0 ≤ Real.rpow δ (-ε_inc) := by
        calc C_between 0
          ≤ Real.log (1 / δ) ^ C_P * Real.rpow δ (-ε_G) := hC_between_bound
        _ = Real.rpow δ (-ε_G) * Real.log (1 / δ) ^ C_P := by ring
        _ ≤ Real.rpow δ (-ε_G) * Real.rpow δ (-(ε_inc - ε_G)) := by
          have h_nonneg : 0 ≤ Real.rpow δ (-ε_G) := Real.rpow_nonneg hδ_pos'.le (-ε_G)
          exact mul_le_mul_of_nonneg_left h_absorption h_nonneg
        _ = Real.rpow δ (-ε_inc) := by
          have h_rpow : Real.rpow δ (-ε_G) * Real.rpow δ (-(ε_inc - ε_G)) =
              Real.rpow δ ((-ε_G) + (-(ε_inc - ε_G))) :=
            (Real.rpow_add hδ_pos' (-ε_G) (-(ε_inc - ε_G))).symm
          have h_sum : (-ε_G) + (-(ε_inc - ε_G)) = -ε_inc := by ring
          rw [h_rpow, h_sum]
      have h_reg_final : IsSquareRootRegular δ t_j
          (Real.rpow δ (-ε_inc)) (Real.rpow δ (-ε_inc)) config.pointSet :=
        IsSquareRootRegular.weaken_CK h_sqrt_reg hCb_abs hCb_abs
          (Real.rpow_pos_of_pos hδ_pos' _) (Real.rpow_pos_of_pos hδ_pos' _)
      let P_orig : Set DirecretisedFurstenbergEstimate.EuclideanPlane := translationEquiv centerTranslation '' config.pointSet
      have hP_orig_regular : IsSquareRootRegular δ t_j
          (Real.rpow δ (-ε_inc)) (Real.rpow δ (-ε_inc)) P_orig :=
        isSquareRootRegular_translate h_reg_final
      have hP_orig_ball : P_orig ⊆ Metric.closedBall 0 1 :=
        unit_square_translate_sub_ball h_config_unit
      have hP_orig_sub : P_orig ⊆ translatedCoarsePointSet config := by
        simp [P_orig, translatedCoarsePointSet]
      have hCΔ_weaken : Real.rpow δ (-lam) ≤ Real.rpow δ (-ε_inc) := by
        have h_exp : -ε_inc ≤ -lam := by linarith
        exact Real.rpow_le_rpow_of_exponent_ge (by linarith [hδ_pos']) (by linarith [hδ_lt_one']) h_exp
      have h_slope_coarse : ∀ T ∈ config.T₀, |T.slope| ≤ 1 := hextra.h_slope
      have h_bridge : (config.T₀.card : ENNReal) ≥
          ENNReal.ofReal (Real.rpow δ (-(2 * s + ε_inc))) :=
        coarse_incidence_geometric_bridge
          (coarseConfig := config)
          (h_slope_coarse := h_slope_coarse)
          (hεReg_pos := hextra.hε_inc_pos)
          (hη_pos := hextra.hε_inc_pos)
          (δ := δ)
          (hδ_pos := hδ_pos')
          (h_est_body := h_uniform.h_body k hδ_le_R')
          (hu_t := by exact hextra.h_tj_ge_t (0 : Fin 1) t_j h_sc0)
          (hu_two := h_tj_le_two)
          (hδ_eq := by rfl)
          (P_orig := P_orig)
          (hP_sub := hP_orig_sub)
          (hP_ball := hP_orig_ball)
          (hP_regular := hP_orig_regular)
          (hCΔ_weaken := hCΔ_weaken)
      exact h_bridge
    exact base_case_good_uniform_v2 hcfg hB1 hextra hP_set_tj_base hC_point_pos hC_point_ge1
      hC_point_bound h_improved_incidence
      u rfl K hK_pos hK_spec_u hs hst hs1 hs_lt_u hu_le_one hεG hη hεN hCP hlam
      h_log_ge_good hk_ge_2 h_sc0 hC_ge hC'_ge
  | bad =>
    exact base_case_bad_branch hs1 hlam hεN hk_ge_2 h_sc0 hcfg hL_ge_one (by linarith [hC_ge, hK_ge1]) hC'_ge

/-- Strong induction for the combining theorem with explicit C' upper bound.

    K-UNIFORM: K is chosen once depending only on s (via uniform_prop5),
    then the theorem holds for ALL t, ε_inc with that same K.

    ε_G0, η0 depend on s,t,ε_inc (not τ,n).
    C = combiningC τ K n C_P, C' = combiningCprime n τ are explicit.

    Base case n=1: filled via base_case_inner.
    Inductive step n≥2: wired to inductive_step_core_v2. -/
theorem combining_induction_uniform_with_data_bounded
    (s : ℝ)
    (hs : 0 < s) (hs1 : s < 1) :
    ∃ (K : ℝ), 1 ≤ K ∧
      ∀ (t ε_inc : ℝ), s < t → t < 2 → 0 < ε_inc →
        CombiningInductionUniform_with_data_bounded s t ε_inc K := by
  -- Choose K uniformly from Prop5 (depends only on s)
  rcases uniform_prop5 s hs hs1 with ⟨K_p5, hK_p5_pos, hK_p5_spec_all⟩
  let K : ℝ := max K_p5 1
  have hK_pos : 0 < K := by positivity
  have hK_ge1 : 1 ≤ K := le_max_right _ _
  have hK_spec_all : ∀ (t : ℝ), s ≤ t → t ≤ 1 → KSpec s t K :=
    fun t hst ht1 => KSpec_weaken s t hK_p5_pos hK_pos (le_max_left _ _) (hK_p5_spec_all t hst ht1)
  have hK_p5_spec_adapted := kspec_adapter hK_spec_all
  refine' ⟨K, hK_ge1, _⟩
  intro t ε_inc hst h_t_lt_2 hε_inc_pos
  intro hK_ge1'
  -- Choose ε_G0, η0 uniformly (depends on s,t,ε_inc, NOT τ,n)
  let u : ℝ := min t 1
  have hu_le_one : u ≤ 1 := min_le_right _ _
  have hs_lt_u : s < u := lt_min hst hs1
  have h_u_sub_s_pos : 0 < u - s := by linarith
  have h_one_sub_s_pos : 0 < 1 - s := by linarith
  let ratio : ℝ := (1 - s) / (u - s)
  have hratio_ge_one : 1 ≤ ratio := by
    dsimp only [ratio]
    apply (one_le_div h_u_sub_s_pos).mpr
    linarith [hu_le_one]
  let ε_G0 : ℝ := ε_inc / (4 * ratio + 4)
  let η0 : ℝ := ε_inc / (4 * ratio + 4)
  have hεG0_pos : 0 < ε_G0 := by dsimp only [ε_G0]; positivity
  have hη0_pos : 0 < η0 := by dsimp only [η0]; positivity
  have hsmall : ∀ (ε_G η : ℝ), 0 < ε_G → ε_G ≤ ε_G0 → 0 < η → η ≤ η0 →
      (η + 2 * ε_G) * (1 - s) / (min t 1 - s) + η ≤ ε_inc := by
    intro ε_G η hεG hεG_le hη hη_le
    have h_denom : min t 1 - s = u - s := by
      have h7 : min t 1 = u := by simp [u]
      rw [h7] <;> ring
    have h_main : (η + 2 * ε_G) * ratio + η ≤ ε_inc := by
      have hεG_bound : ε_G ≤ ε_inc / (4 * ratio + 4) := by simpa [ε_G0] using hεG_le
      have hη_bound : η ≤ ε_inc / (4 * ratio + 4) := by simpa [η0] using hη_le
      have h1 : (η + 2 * ε_G) * ratio + η ≤
          (ε_inc / (4 * ratio + 4) + 2 * (ε_inc / (4 * ratio + 4))) * ratio + ε_inc / (4 * ratio + 4) := by
        gcongr <;> linarith
      have h2 : (ε_inc / (4 * ratio + 4) + 2 * (ε_inc / (4 * ratio + 4))) * ratio + ε_inc / (4 * ratio + 4) =
          ε_inc * (3 * ratio + 1) / (4 * ratio + 4) := by
        field_simp <;> ring
      rw [h2] at h1
      have h3 : ε_inc * (3 * ratio + 1) / (4 * ratio + 4) ≤ ε_inc := by
        have h4 : 0 < 4 * ratio + 4 := by positivity
        have h5 : 3 * ratio + 1 ≤ 4 * ratio + 4 := by linarith [hratio_ge_one]
        have h6 : ε_inc * (3 * ratio + 1) / (4 * ratio + 4) ≤ ε_inc * (4 * ratio + 4) / (4 * ratio + 4) := by gcongr
        have h7 : ε_inc * (4 * ratio + 4) / (4 * ratio + 4) = ε_inc := by
          field_simp [h4.ne'] <;> ring
        rw [h7] at h6
        exact h6
      exact le_trans h1 h3
    have h4 : (η + 2 * ε_G) * (1 - s) / (min t 1 - s) = (η + 2 * ε_G) * ratio := by
      rw [h_denom] <;> simp [ratio] <;> ring
    rw [h4]
    exact h_main
  refine' ⟨ε_G0, η0, hεG0_pos, hη0_pos, hsmall, _⟩
  intro τ hτ hτ1 n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h1 : n = 1
    · -- Base case n = 1
      subst h1
      have hεG0_lt_εinc : ε_G0 < ε_inc := by
        dsimp only [ε_G0]
        have h1 : 1 < 4 * ratio + 4 := by linarith [hratio_ge_one]
        exact div_lt_self hε_inc_pos h1
      exact base_case_inner s t τ ε_inc ε_G0 η0 K hs hst hs1 hτ hτ1 hε_inc_pos
        hεG0_pos hεG0_lt_εinc hη0_pos hK_ge1 hK_spec_all hsmall
    · -- Inductive step n ≥ 2
      have h2 : 2 ≤ n := by omega
      have h_n1_pos : 0 < n - 1 := by omega
      -- Extract IH for n-1
      rcases ih (n - 1) (by omega) h_n1_pos with ⟨lam_0_fine, hlam0_fine_pos, h_body_fine⟩
      -- Set lam_0 = min(τ * lam_0_fine / 2, τ * ε_inc / 2) so:
      --   (a) lam_tail = 2*lam/τ ≤ lam_0_fine
      --   (b) lam ≤ τ*ε_inc/2, needed for good-case absorption of CΔ'
      let lam_0 : ℝ := min (τ * lam_0_fine / 2) (τ * ε_inc / 2)
      have hlam0_pos : 0 < lam_0 := by positivity
      have hlam0_le_half : lam_0 ≤ τ * lam_0_fine / 2 := min_le_left _ _
      have hlam0_le_τε_half : lam_0 ≤ τ * ε_inc / 2 := min_le_right _ _
      refine' ⟨lam_0, hlam0_pos, _⟩
      intro C_P hCP
      -- Fine C_P amplification
      let C_n : ℝ := (n : ℝ) + 4
      have hCn_ge1 : 1 ≤ C_n := by
        have h2' : (n : ℝ) ≥ 2 := by exact_mod_cast h2
        dsimp only [C_n] <;> linarith
      let C_P_fine : ℝ := C_P + 2 * C_n
      have hCP_fine : 1 ≤ C_P_fine := by
        have h2' : (n : ℝ) ≥ 2 := by exact_mod_cast h2
        dsimp only [C_P_fine, C_n] <;> linarith
      have hCP_fine_eq : C_P_fine = C_P + 2 * C_n := by simp [C_P_fine, C_n] <;> ring
      -- Get C_fine from IH at C_P_fine
      have h_fine_body := h_body_fine C_P_fine hCP_fine
      let C_fine : ℝ := combiningC τ K (n - 1) C_P_fine
      let C'_fine : ℝ := combiningCprime (n - 1) τ
      have hC_fine_pos : 0 < C_fine := h_fine_body.1
      have hC'_fine_pos : 0 < C'_fine := combiningCprime_pos h_n1_pos hτ
      -- Positivity of combiningC
      have hC_pos : 0 < combiningC τ K n C_P := combiningC_pos τ K hK_pos hτ n hn C_P hCP
      have hC'_pos : 0 < combiningCprime n τ := combiningCprime_pos hn hτ
      -- C' bound: combiningCprime n τ ≥ 1 + 2*C'_fine/τ
      have hC'_ge : combiningCprime n τ ≥ (1 : ℝ) + 2 * C'_fine / τ := by
        have h1 : C'_fine ≤ combiningCprime (n - 1) τ := by rfl
        have h2 : (1 : ℝ) + 2 * C'_fine / τ ≤ (1 : ℝ) + 2 * combiningCprime (n - 1) τ / τ := by gcongr <;> linarith
        have h3 : (1 : ℝ) + 2 * combiningCprime (n - 1) τ / τ ≤ combiningCprime n τ := by
          have h41 : n - 1 + 1 = n := by omega
          have h4 : combiningCprime n τ = 2 + (2 / τ) * combiningCprime (n - 1) τ := by
            have h5 := combiningCprime_succ (n - 1) τ hτ
            rw [h41] at h5; exact h5
          rw [h4]
          have h5 : 2 * combiningCprime (n - 1) τ / τ = (2 / τ) * combiningCprime (n - 1) τ := by
            field_simp [hτ.ne'] <;> ring
          rw [h5] <;> linarith
        exact le_trans h2 h3
      -- C bound from recursive definition
      have hC_ge : combiningC τ K n C_P ≥ (1 + (7 : ℝ)) * (1 + (1 : ℝ) + C'_fine) + K + C_P + 8 + C_fine := by
        have h_eq : combiningC τ K n C_P =
            (1 + (7 : ℝ)) * (1 + (1 : ℝ) + combiningCprime (n - 1) τ) + K + C_P + 8 + C_fine := by
          cases n with
          | zero => omega
          | succ n' =>
            cases n' with
            | zero => omega
            | succ n'' =>
              simp [combiningC, C_fine, C_P_fine, C_n] <;> ring_nf <;> congr <;> omega
        rw [h_eq] <;> rfl
      refine' ⟨hC_pos, _⟩
      intro ε_N lam hεN hlam hlam_le
      intro (h_uniform : UniformIncidenceData s t ε_inc)
      -- lam_tail = 2*lam/τ; lam ≤ lam_0 ensures lam_tail ≤ lam_0_fine
      let lam_tail : ℝ := 2 * lam / τ
      have hlam_tail_pos : 0 < lam_tail := by positivity
      have hτ_lam_tail : τ * lam_tail = 2 * lam := by
        dsimp only [lam_tail]; field_simp [hτ.ne'] <;> ring
      have hlam_tail_le : lam_tail ≤ lam_0_fine := by
        dsimp only [lam_tail]
        have h : lam ≤ τ * lam_0_fine / 2 := le_trans hlam_le hlam0_le_half
        calc 2 * lam / τ ≤ 2 * (τ * lam_0_fine / 2) / τ := by gcongr
           _ = lam_0_fine := by field_simp [hτ.ne'] <;> ring
      -- Get δ_tail from IH at fine scale
      rcases h_fine_body.2 ε_N lam_tail hεN hlam_tail_pos hlam_tail_le h_uniform with ⟨δ_tail, hδ_tail_pos, h_ih_fine_bound⟩
      -- Choose A for K polylog bound
      let A : ℝ := 2700 * 3145728 * (8 / Real.log 2)^7
      have hA_pos : 0 < A := by positivity
      have hA_ge1 : 1 ≤ A := by
        have h1 : (0 : ℝ) < Real.log 2 := by positivity
        have h2 : (8 / Real.log 2 : ℝ) ≥ 1 := by
          have h3 : Real.log 2 < 8 := by linarith [Real.log_two_lt_d9]
          have h4 : (8 / Real.log 2 : ℝ) ≥ 1 := by
            apply (one_le_div h1).mpr
            linarith [Real.log_two_lt_d9]
          exact h4
        have h5 : (8 / Real.log 2 : ℝ)^7 ≥ 1 := by
          have h6 : 1 ≤ (8 / Real.log 2 : ℝ) := h2
          exact one_le_pow₀ h6
        nlinarith
      have hA_eq : A = 2700 * 3145728 * (8 / Real.log 2)^7 := by rfl
      -- Threshold for h_poly_K_le_δlam: Poly(k) ≤ δ^{-lam} = 2^{lam*k}
      have hb_pos : 0 < lam * Real.log 2 := by positivity
      rcases exists_K_poly_le_exp (lam * Real.log 2) (2700 * 3145728) hb_pos (by positivity) with ⟨K_poly, hK_poly⟩
      -- Threshold for h_k_large: Poly(k) ≥ 2^{s+η0-ε_N} (η0 upper-bounds η)
      let B_large : ℝ := Real.rpow 2 (s + η0 - ε_N)
      let C0_large : ℝ := max 1 (B_large / (2700 * 3145728))
      rcases exists_nat_ge ((C0_large - 7) / 4) with ⟨K_large, hK_large_thresh⟩
      -- Threshold for h_eq89: k * log 2 ≥ τ^{-C_P_fine}
      have hlog2_pos : 0 < Real.log 2 := by positivity
      let B_eq89 : ℝ := Real.rpow τ (-(C_P_fine : ℝ)) / Real.log 2
      rcases exists_nat_ge B_eq89 with ⟨K_eq89, hK_eq89_thresh⟩
      -- Threshold for hδτ_le_dtail: (δ^k)^τ ≤ δ_tail
      let K_dtail : ℕ := if h : δ_tail < 1 then
        Nat.ceil (Real.log (1 / δ_tail) / (τ * Real.log 2))
      else 0
      have hK_dtail : ∀ (k : ℕ), k ≥ K_dtail → Real.rpow (dyadicDelta k) τ ≤ δ_tail := by
        intro k hk_ge
        by_cases h : δ_tail < 1
        · -- δ_tail < 1: need k ≥ log(1/δ_tail)/(τ*log 2)
          have h1 : (K_dtail : ℝ) ≥ Real.log (1 / δ_tail) / (τ * Real.log 2) := by
            simp [K_dtail, h] <;> exact Nat.le_ceil _
          have h2 : (k : ℝ) ≥ Real.log (1 / δ_tail) / (τ * Real.log 2) := by
            exact le_trans h1 (by exact_mod_cast hk_ge)
          have h3 : τ * (k : ℝ) * Real.log 2 ≥ Real.log (1 / δ_tail) := by
            have h4 : 0 < τ * Real.log 2 := by positivity
            calc τ * (k : ℝ) * Real.log 2
              = (τ * Real.log 2) * (k : ℝ) := by ring
            _ ≥ (τ * Real.log 2) * (Real.log (1 / δ_tail) / (τ * Real.log 2)) := by gcongr
            _ = Real.log (1 / δ_tail) := by
              field_simp [h4.ne']
          have h6 : dyadicDelta k = Real.exp (-(k : ℝ) * Real.log 2) := by
            have h61 : dyadicDelta k = Real.rpow 2 (-(k : ℝ)) := by
              simp [dyadicDelta] <;> norm_cast
            rw [h61]
            have h62 : Real.rpow (2 : ℝ) (-(k : ℝ)) = Real.exp ((-(k : ℝ)) * Real.log 2) := by
              have h : ∀ (x : ℝ), 0 < x → ∀ (y : ℝ), Real.rpow x y = Real.exp (y * Real.log x) := by
                intro x hx y
                have h' : Real.rpow x y = Real.exp (Real.log x * y) := Real.rpow_def_of_pos hx y
                rw [h']
                <;> ring_nf
              exact h 2 (by norm_num) (-(k : ℝ))
            exact h62
          have h5 : Real.rpow (dyadicDelta k) τ = Real.exp (-τ * (k : ℝ) * Real.log 2) := by
            rw [h6]
            have h7 : Real.rpow (Real.exp (-(k : ℝ) * Real.log 2)) τ = Real.exp ((-(k : ℝ) * Real.log 2) * τ) := by
              have h : ∀ (x : ℝ), 0 < x → ∀ (y : ℝ), Real.rpow x y = Real.exp (y * Real.log x) := by
                intro x hx y
                have h' : Real.rpow x y = Real.exp (Real.log x * y) := Real.rpow_def_of_pos hx y
                rw [h'] <;> ring_nf
              rw [h (Real.exp (-(k : ℝ) * Real.log 2)) (Real.exp_pos _) τ]
              have hlog : Real.log (Real.exp (-(k : ℝ) * Real.log 2)) = -(k : ℝ) * Real.log 2 := by
                rw [Real.log_exp]
              rw [hlog] <;> ring_nf
            rw [h7] <;> ring_nf
          rw [h5]
          have h7 : Real.exp (-τ * (k : ℝ) * Real.log 2) ≤ δ_tail := by
            have h8 : -τ * (k : ℝ) * Real.log 2 ≤ Real.log δ_tail := by
              have h9 : Real.log (1 / δ_tail) = -Real.log δ_tail := by
                rw [Real.log_div (by norm_num) hδ_tail_pos.ne'] <;> simp
              linarith
            have h10 : Real.exp (-τ * (k : ℝ) * Real.log 2) ≤ Real.exp (Real.log δ_tail) := Real.exp_le_exp.mpr h8
            have h11 : Real.exp (Real.log δ_tail) = δ_tail := Real.exp_log hδ_tail_pos
            rw [h11] at h10
            exact h10
          exact h7
        · -- δ_tail ≥ 1: (dyadicDelta k)^τ ≤ 1 ≤ δ_tail
          have h10 : δ_tail ≥ 1 := by linarith
          have h11 : Real.rpow (dyadicDelta k) τ ≤ 1 := by
            have h12 : 0 < dyadicDelta k := dyadicDelta_pos k
            have h13 : dyadicDelta k ≤ 1 := dyadicDelta_le_one k
            exact Real.rpow_le_one h12.le h13 hτ.le
          linarith
      -- Threshold for coarse polylog absorption (normal scale):
      -- need k large enough that log(1/Δ_m)^(C_P+8) dominates K * Poly(k) * C_between * Δ_m^ε_N
      -- Since m ≥ τ*k, log(1/Δ_m) ≥ τ*log(1/δ), and degree C_P+8 ≥ 9 dominates Poly(k) degree 7.
      let C_absorb : ℝ := K * 81 * (2700 * 3145728) * 13 *
          (2 * Real.sqrt 2) * (2 : ℝ) ^ s * (5 : ℝ) ^ 7 /
          (Real.rpow τ (C_P + 8) * (Real.log 2) ^ 8)
      rcases exists_nat_ge C_absorb with ⟨K_absorb0, hK_absorb0⟩
      let K_absorb : ℕ := max 7 K_absorb0
      have hK_absorb : (K_absorb : ℝ) ≥ C_absorb := by
        have h1 : (K_absorb0 : ℝ) ≥ C_absorb := by exact_mod_cast hK_absorb0
        have h2 : (K_absorb : ℝ) ≥ (K_absorb0 : ℝ) := by exact_mod_cast le_max_right _ _
        linarith
      have hK_absorb7 : K_absorb ≥ 7 := by
        exact Nat.le_max_left 7 K_absorb0
      -- Threshold for good-case absorption:
      -- C_absorb2_const * k^(7+C_P) ≤ δ_k^{-τ*ε_inc/2}
      -- This handles hC_weaken1, hC_weaken2, hCΔ_weaken simultaneously.
      have h_eps_half_pos : 0 < τ * ε_inc / 2 := by positivity
      let b_absorb : ℝ := (τ * ε_inc / 2) * Real.log 2
      have hb_absorb_pos : 0 < b_absorb := by positivity
      let C_absorb2_const : ℝ := 9 * 2700 * 3145728 * 11^7
      have hC_absorb2_const_pos : 0 < C_absorb2_const := by positivity
      rcases Prop73Restructure.exp_dominates_poly_threshold (7 + C_P) b_absorb C_absorb2_const
          hb_absorb_pos hC_absorb2_const_pos
        with ⟨K_absorb2, hK_absorb2_ge1, hK_absorb2_core⟩
      have hK_absorb2_exp : ∀ (k : ℕ), k ≥ K_absorb2 →
          C_absorb2_const * (k : ℝ)^(7 + C_P) < Real.rpow (dyadicDelta k) (-(τ * ε_inc / 2)) := by
        intro k hk
        have h9 := hK_absorb2_core k hk
        have h10 : Real.exp (b_absorb * (k : ℝ)) = Real.rpow (dyadicDelta k) (-(τ * ε_inc / 2)) := by
          have h11 : b_absorb = (τ * ε_inc / 2) * Real.log 2 := by rfl
          rw [h11]
          have h12 : dyadicDelta k = Real.rpow 2 (-(k : ℝ)) := by simp [dyadicDelta] <;> norm_cast
          rw [h12]
          exact Prop73Restructure.exp_log2_to_dyadicDelta (c := τ * ε_inc / 2) k
        rw [h10] at h9
        exact h9
      have hK_absorb2 : ∀ (k : ℕ), k ≥ K_absorb2 →
          (2700 : ℝ) * 3145728 * (4 * (k : ℝ) + 7)^7 * Real.log (k : ℝ)^C_P ≤ Real.rpow (dyadicDelta k) (-(τ * ε_inc / 2)) := by
        intro k hk
        have hk1 : (k : ℝ) ≥ 1 := by exact_mod_cast le_trans hK_absorb2_ge1 hk
        have h4 : Real.log (k : ℝ) ≤ (k : ℝ) := Real.log_le_self (by linarith)
        have h5 : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg hk1
        have h6 : Real.log (k : ℝ)^C_P ≤ (k : ℝ)^C_P := by gcongr
        have h7 : (4 * (k : ℝ) + 7) ≤ 11 * (k : ℝ) := by linarith
        have h_k_pos : 0 < (k : ℝ) := by linarith [hk1]
        have h12 : (k : ℝ)^7 * (k : ℝ)^C_P = (k : ℝ)^(7 + C_P) := by
          have h13 : (k : ℝ)^7 = (k : ℝ)^(7 : ℝ) := by simp
          rw [h13]
          rw [← Real.rpow_add h_k_pos (7 : ℝ) C_P]
          <;> norm_cast
        have h9 := hK_absorb2_exp k hk
        have h10 : (2700 : ℝ) * 3145728 * (4 * (k : ℝ) + 7)^7 * Real.log (k : ℝ)^C_P ≤
            (2700 * 3145728 * 11^7 : ℝ) * (k : ℝ)^(7 + C_P) := by
          calc (2700 : ℝ) * 3145728 * (4 * (k : ℝ) + 7)^7 * Real.log (k : ℝ)^C_P
            ≤ (2700 : ℝ) * 3145728 * (11 * (k : ℝ))^7 * (k : ℝ)^C_P := by gcongr <;> linarith
          _ = (2700 * 3145728 * 11^7 : ℝ) * ((k : ℝ)^7 * (k : ℝ)^C_P) := by ring
          _ = (2700 * 3145728 * 11^7 : ℝ) * (k : ℝ)^(7 + C_P) := by rw [h12]
        have h11 : (2700 * 3145728 * 11^7 : ℝ) * (k : ℝ)^(7 + C_P) ≤ C_absorb2_const * (k : ℝ)^(7 + C_P) := by
          gcongr <;> norm_num
        exact le_trans h10 (le_trans h11 (le_of_lt h9))
      -- δR threshold: need δ_k ≤ δR^(1/τ) so that δ_m ≤ δ_k^τ ≤ δR
      have hδR_pos' : 0 < h_uniform.δR := h_uniform.hδR_pos
      let δR_threshold : ℝ := Real.rpow h_uniform.δR (1 / τ)
      have hδR_threshold_pos : 0 < δR_threshold := Real.rpow_pos_of_pos hδR_pos' (1 / τ)
      -- Fine absorption threshold: ensure k^(n+2) dominates polynomial constants
      have hn2 : 2 ≤ n := h2
      have h_n1_pos : 0 < (n - 1 : ℝ) := by
        have h' : (n : ℝ) ≥ 2 := by exact_mod_cast h2
        linarith
      let C_fine_total : ℝ :=
        (18 : ℝ) * (2700 * 3145728 * (11 : ℝ)^7) *
        ((24 : ℝ) / (n - 1 : ℝ))^(n - 1) * (4 : ℝ)^(n - 1) /
        (τ * Real.log 2)^(C_P + 2 * C_n)
      have hC_fine_total_pos : 0 < C_fine_total := by positivity
      let K_fine : ℕ := Nat.ceil (max 1 C_fine_total)
      -- K_max = max of all thresholds
      let K_max : ℕ := max (max (max (max (max K_poly K_large) (max K_eq89 K_dtail)) K_absorb) K_absorb2) K_fine
      -- δ₀ = min(1/4, exp(-A), dyadicDelta K_max, δR^(1/τ))
      let δ₀ : ℝ := min (min (min (1 / 4) (Real.exp (-A))) (dyadicDelta K_max)) δR_threshold
      have hδ₀_pos : 0 < δ₀ :=
        Prop73Restructure.pos_min4 (by norm_num) (Real.exp_pos _) (dyadicDelta_pos K_max) hδR_threshold_pos
      refine' ⟨δ₀, hδ₀_pos, _⟩
      intro ε_G η hεG hεG_le hεN_le hη hη_le
      intro k hk M config Δ scaleClass N C_between hcfg hB1 hextra
      -- k ≥ K_max from dyadicDelta k ≤ δ₀ ≤ dyadicDelta K_max
      have hkδ : dyadicDelta k ≤ dyadicDelta K_max := by
        have h1 : dyadicDelta k ≤ δ₀ := hk
        have h2 : δ₀ ≤ dyadicDelta K_max := by
          dsimp only [δ₀]; exact le_trans (min_le_left _ _) (min_le_right _ _)
        exact le_trans h1 h2
      have hk_ge_Kmax : k ≥ K_max := by
        by_contra h
        have h' : k < K_max := by omega
        have h9 : (K_max : ℤ) > (k : ℤ) := by exact_mod_cast h'
        have h10 : (2 : ℝ)^(-(K_max : ℤ)) < (2 : ℝ)^(-(k : ℤ)) := by
          gcongr <;> norm_num <;> linarith
        have h11 : dyadicDelta K_max < dyadicDelta k := by
          simpa [dyadicDelta] using h10
        exact not_le.mpr h11 hkδ
      have hk_ge_poly : k ≥ K_poly := by omega
      have hk_ge_large : k ≥ K_large := by omega
      have hk_ge_eq89 : k ≥ K_eq89 := by omega
      have hk_ge_dtail : k ≥ K_dtail := by omega
      have hk_ge_absorb : k ≥ K_absorb := by omega
      have hk_ge_absorb2 : k ≥ K_absorb2 := by omega
      have hk_ge_fine : k ≥ K_fine := by omega
      have hk_exp1 : dyadicDelta k ≤ Real.exp (-1) := by
        have h1 : dyadicDelta k ≤ (1 : ℝ) / 4 := by
          have h2 : dyadicDelta k ≤ δ₀ := hk
          have h3 : δ₀ ≤ 1 / 4 := by
            dsimp only [δ₀]
            exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
          exact le_trans h2 h3
        have h4 : (1 : ℝ) / 4 ≤ Real.exp (-1) := by
          have h5 : Real.exp 1 < 3 := Real.exp_one_lt_three
          have h6 : Real.exp 1 ≤ 4 := by linarith
          have h7 : 0 < Real.exp 1 := Real.exp_pos 1
          have h8 : Real.exp (-1) = (Real.exp 1)⁻¹ := by rw [Real.exp_neg]
          rw [h8]
          have h9 : (1 : ℝ) / 4 ≤ (Real.exp 1)⁻¹ := one_fourth_le_exp_neg_one
          exact h9
        exact le_trans h1 h4
      have hk_ge_one : (1 : ℝ) ≤ (k : ℝ) := by
        have h : k ≥ 2 := by
          have hδ : dyadicDelta k ≤ 1 / 4 := by
            have h1 : dyadicDelta k ≤ δ₀ := hk
            have h2 : δ₀ ≤ 1 / 4 := by
              dsimp only [δ₀]
              exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
            exact le_trans h1 h2
          by_contra h'; have h'' : k < 2 := by omega
          interval_cases k <;> norm_num [dyadicDelta] at hδ <;> linarith
        have h' : 1 ≤ k := by omega
        exact_mod_cast h'
      -- Extract m from Δ 1 ∈ dyadicScales
      have hΔ1_dyadic : Δ 1 ∈ dyadicScales := hcfg.hΔ_dyadic 1
      rcases hΔ1_dyadic with ⟨m, hm_eq⟩
      have hm_eq2 : Δ 1 = dyadicDelta m := by
        have h1 : Δ 1 = (2 : ℝ) ^ (-(m : ℤ)) := hm_eq
        have h2 : (2 : ℝ) ^ (-(m : ℤ)) = dyadicDelta m := by
          simp [dyadicDelta, zpow_neg, zpow_ofNat] <;> ring
        rw [h1, h2]
      have hδ_le_quarter : dyadicDelta k ≤ 1 / 4 := by
        have h : dyadicDelta k ≤ δ₀ := hk
        have h2 : δ₀ ≤ 1 / 4 := by
          dsimp only [δ₀]
          exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
        exact le_trans h h2
      have hk_ge_2 : 2 ≤ k := by
        by_contra h9
        have h10 : k < 2 := by omega
        have h11 : k = 0 ∨ k = 1 := by omega
        rcases h11 with (rfl | rfl)
        · norm_num [dyadicDelta] at hδ_le_quarter <;> linarith
        · norm_num [dyadicDelta] at hδ_le_quarter <;> linarith
      have hk' : dyadicDelta k ≤ Real.exp (-A) := by
        have h : dyadicDelta k ≤ δ₀ := hk
        have h2 : δ₀ ≤ Real.exp (-A) := by
          dsimp only [δ₀]
          exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
        exact le_trans h h2
      -- h_poly_K_le_δlam from threshold
      have h_poly_K_le_δlam : (2700 : ℝ) * 3145728 * (4 * (k : ℝ) + 7)^7 ≤ Real.rpow (dyadicDelta k) (-lam) := by
        have h1 := hK_poly k hk_ge_poly
        have h2 : Real.exp ((lam * Real.log 2) * (k : ℝ)) = Real.rpow (dyadicDelta k) (-lam) := by
          have h3 : dyadicDelta k = Real.rpow 2 (-(k : ℝ)) := by simp [dyadicDelta] <;> norm_cast
          rw [h3]
          exact Prop73Restructure.exp_log2_to_dyadicDelta (c := lam) k
        rw [h2] at h1
        exact h1
      -- h_k_large from threshold (η ≤ η0)
      have h_k_large : (2700 : ℝ) * 3145728 * (4 * (k : ℝ) + 7)^7 ≥ Real.rpow 2 (s + η - ε_N) := by
        have hη_le0 : η ≤ η0 := hη_le
        have h_exp_le : s + η - ε_N ≤ s + η0 - ε_N := by linarith
        have hB_le : Real.rpow 2 (s + η - ε_N) ≤ Real.rpow 2 (s + η0 - ε_N) := by
          apply Real.rpow_le_rpow_of_exponent_le
          <;> norm_num <;> linarith
        have h4 : (4 * (k : ℝ) + 7) ≥ C0_large := by
          have h5 : (k : ℝ) ≥ (K_large : ℝ) := by exact_mod_cast hk_ge_large
          have h6 : (K_large : ℝ) ≥ (C0_large - 7) / 4 := by exact_mod_cast hK_large_thresh
          linarith
        have h7 : (4 * (k : ℝ) + 7) ≥ 1 := by linarith [h4, show (1 : ℝ) ≤ C0_large from le_max_left _ _]
        have h8 : (4 * (k : ℝ) + 7)^7 ≥ (4 * (k : ℝ) + 7) := by
          have h9 : (4 * (k : ℝ) + 7)^7 ≥ (4 * (k : ℝ) + 7)^1 := by gcongr <;> linarith
          simpa using h9
        have h10 : (4 * (k : ℝ) + 7)^7 ≥ B_large / (2700 * 3145728) := by
          calc (4 * (k : ℝ) + 7)^7 ≥ (4 * (k : ℝ) + 7) := h8
            _ ≥ C0_large := h4
            _ ≥ B_large / (2700 * 3145728) := le_max_right _ _
        have h11 : (2700 : ℝ) * 3145728 * (4 * (k : ℝ) + 7)^7 ≥ B_large := by
          calc (2700 : ℝ) * 3145728 * (4 * (k : ℝ) + 7)^7
            = (2700 * 3145728) * ((4 * (k : ℝ) + 7)^7) := by ring
            _ ≥ (2700 * 3145728) * (B_large / (2700 * 3145728)) := by gcongr
            _ = B_large := by
              field_simp [show (2700 * 3145728 : ℝ) ≠ 0 by positivity] <;> ring
        exact le_trans hB_le h11
      -- h_eq89 from threshold
      have h_eq89 : Real.log (1 / dyadicDelta k) ≥ Real.rpow τ (-(C_P_fine : ℝ)) := by
        have h1 : Real.log (1 / dyadicDelta k) = (k : ℝ) * Real.log 2 := by
          have h2 : 1 / dyadicDelta k = Real.rpow 2 (k : ℝ) := by
            simp [dyadicDelta] <;> field_simp <;> ring
          rw [h2]
          have h_log_rpow : ∀ (x : ℝ), 0 < x → ∀ (y : ℝ), Real.log (Real.rpow x y) = y * Real.log x := by
            intro x hx y
            simpa using Real.log_rpow hx y
          rw [h_log_rpow 2 (by norm_num) (k : ℝ)] <;> norm_num
        rw [h1]
        have h3 : (k : ℝ) ≥ B_eq89 := by
          exact le_trans (by exact_mod_cast hK_eq89_thresh) (by exact_mod_cast hk_ge_eq89)
        have h4 : (k : ℝ) * Real.log 2 ≥ Real.rpow τ (-(C_P_fine : ℝ)) := by
          dsimp only [B_eq89] at h3
          calc (k : ℝ) * Real.log 2
            ≥ B_eq89 * Real.log 2 := by gcongr
            _ = Real.rpow τ (-(C_P_fine : ℝ)) := by
              dsimp only [B_eq89]
              field_simp [hlog2_pos.ne'] <;> ring
        exact h4
      -- hδτ_le_dtail from threshold
      have hδτ_le_dtail : Real.rpow (dyadicDelta k) τ ≤ δ_tail := hK_dtail k hk_ge_dtail
      -- h_ih_bound: apply IH at fine scale with current ε_G, η
      -- The IH takes CombiningExtraHypotheses_v2; the core constructs it via fine_extra_from_coarse
      have h_ih_bound : ∀ (k' : ℕ), dyadicDelta k' ≤ δ_tail →
          ∀ (M' : ℕ)
            (config' : CTNiceConfiguration k' s (Real.rpow (dyadicDelta k') (-lam_tail)) M')
            (Δ' : Fin ((n - 1) + 1) → ℝ)
            (scaleClass' : Fin (n - 1) → ScaleClass)
            (N' : Fin (n - 1) → ℕ)
            (C_between' : Fin (n - 1) → ℝ),
            CombiningConfig s t τ (n - 1) ε_G η lam_tail ε_N C_P_fine C_between' k' M' config' Δ' scaleClass' N' →
            B1BridgeHypotheses k' config' →
            CombiningExtraHypotheses_v2 s t ε_G η ε_N C_P_fine ε_inc (n - 1) lam_tail k' M' config' Δ' scaleClass' →
            (config'.T₀.card : ENNReal) ≥
              ENNReal.ofReal (combiningLowerBound (dyadicDelta k') (M' : ℝ) C_fine C'_fine lam_tail s ε_N η (n - 1) Δ' scaleClass') :=
        h_ih_fine_bound ε_G η hεG hεG_le hεN_le hη hη_le
      -- Coarse absorption for normal scale:
      -- log(1/Δ_m)^(C_P+8) ≥ K * Poly(k) * max(C_between,1) * Δ_m^ε_N
      have h_absorb_coarse : scaleClass ⟨0, by omega⟩ = ScaleClass.normal →
          Real.rpow (Real.log (1 / dyadicDelta m)) (C_P + 8) ≥
          K * (81 * ((2700 : ℝ) * 3145728 * (4 * (k : ℝ) + 7)^7) *
            max (C_between ⟨0, by omega⟩) 1 * (2 * Real.sqrt 2) ^ s) * 13 * (2 : ℝ) ^ s *
          Real.rpow (dyadicDelta m) ε_N := by
        intro h_normal
        have hk7 : k ≥ 7 := le_trans hK_absorb7 hk_ge_absorb
        have hlogδ_pos : 0 < Real.log (1 / dyadicDelta k) := by
          apply Real.log_pos
          have h3 : dyadicDelta k < 1 := by
            have h4 : dyadicDelta k ≤ Real.exp (-1) := hk_exp1
            have h5 : Real.exp (-1) < 1 := by
              have h6 : Real.exp (-1 : ℝ) < Real.exp 0 := Real.exp_strictMono (by norm_num)
              have h7 : Real.exp 0 = 1 := by simp
              rw [h7] at h6; exact h6
            exact lt_of_le_of_lt h4 h5
          exact one_lt_one_div (dyadicDelta_pos k) h3
        have hlogδ_ge1 : 1 ≤ Real.log (1 / dyadicDelta k) :=
          Prop73Restructure.dyadicDelta_log_ge_one hk_ge_2
        have hCP_nonneg : 0 ≤ C_P := by linarith [hCP]
        -- Scale ratio gives m ≥ τ*k
        have h_scale0 := hcfg.h_scale_ratio ⟨0, by omega⟩ (by simp [h_normal, ScaleClass.isBad])
        have hΔ0 : Δ 0 = 1 := hcfg.hΔ_start
        have hΔ1 : Δ 1 = dyadicDelta m := hm_eq2
        have h_scale_ratio0 : Δ 1 / Δ 0 ≤ Real.rpow (dyadicDelta k) τ :=
          Prop73Restructure.first_scale_ratio hn Δ (Real.rpow (dyadicDelta k) τ) h_scale0
        have h_scale_ratio1 : dyadicDelta m ≤ Real.rpow (dyadicDelta k) τ := by
          simpa [div_one, hΔ0, hΔ1] using h_scale_ratio0
        have hm_geτk : (m : ℝ) ≥ τ * (k : ℝ) :=
          scale_ratio_to_ge hτ h_scale_ratio1
        have hlogm_ge : Real.log (1 / dyadicDelta m) ≥ τ * Real.log (1 / dyadicDelta k) := by
          have h1 : Real.log (1 / dyadicDelta m) = (m : ℝ) * Real.log 2 := by
            have h2 : 1 / dyadicDelta m = Real.rpow 2 (m : ℝ) := by
              simp [dyadicDelta] <;> field_simp <;> ring
            rw [h2]
            simpa using Real.log_rpow (by norm_num) (m : ℝ)
          have h3 : Real.log (1 / dyadicDelta k) = (k : ℝ) * Real.log 2 := by
            have h4 : 1 / dyadicDelta k = Real.rpow 2 (k : ℝ) := by
              simp [dyadicDelta] <;> field_simp <;> ring
            rw [h4]
            simpa using Real.log_rpow (by norm_num) (k : ℝ)
          rw [h1, h3]
          have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
          calc (m : ℝ) * Real.log 2
            ≥ (τ * (k : ℝ)) * Real.log 2 := by gcongr
          _ = τ * ((k : ℝ) * Real.log 2) := by ring
        -- C_between bound cancellation
        have hCb : C_between ⟨0, by omega⟩ ≤ Real.rpow (Real.log (1 / dyadicDelta k)) C_P *
            Real.rpow (1 / dyadicDelta m) ε_N := by
          have h := hcfg.h_C_between_normal ⟨0, by omega⟩ h_normal
          have h_succ : Fin.succ (⟨0, by omega⟩ : Fin n) = (1 : Fin (n + 1)) := by
            apply Fin.ext
            simp [Nat.mod_eq_of_lt (show 1 < n + 1 by omega)]
          have h_cast : Fin.castSucc (⟨0, by omega⟩ : Fin n) = (0 : Fin (n + 1)) := by
            apply Fin.ext
            simp [Nat.mod_eq_of_lt (show 0 < n + 1 by omega)]
          rw [h_succ, h_cast, hcfg.hΔ_start, hm_eq2] at h
          simpa using h
        have hmax_cancel : max (C_between ⟨0, by omega⟩) 1 * Real.rpow (dyadicDelta m) ε_N ≤
            Real.rpow (Real.log (1 / dyadicDelta k)) C_P := by
          have h_pos1 : 0 < Real.rpow (dyadicDelta m) ε_N := Real.rpow_pos_of_pos (dyadicDelta_pos m) _
          by_cases h : C_between ⟨0, by omega⟩ ≥ 1
          · have hmax : max (C_between ⟨0, by omega⟩) 1 = C_between ⟨0, by omega⟩ := by
              rw [max_eq_left] <;> exact h
            rw [hmax]
            have h9 : Real.rpow (1 / dyadicDelta m) ε_N * Real.rpow (dyadicDelta m) ε_N = 1 := by
              have hpos : 0 < dyadicDelta m := dyadicDelta_pos m
              have h_inv : 1 / dyadicDelta m = (dyadicDelta m)⁻¹ := by ring
              have h1 : Real.rpow (1 / dyadicDelta m) ε_N = (Real.rpow (dyadicDelta m) ε_N)⁻¹ := by
                rw [h_inv]
                exact Real.inv_rpow hpos.le ε_N
              rw [h1]
              field_simp [(Real.rpow_pos_of_pos hpos ε_N).ne'] <;> ring
            have h10 : C_between ⟨0, by omega⟩ * Real.rpow (dyadicDelta m) ε_N ≤
                Real.rpow (Real.log (1 / dyadicDelta k)) C_P := by
              have h_rpow_nonneg : 0 ≤ Real.rpow (dyadicDelta m) ε_N := by positivity
              have h11 : C_between ⟨0, by omega⟩ * Real.rpow (dyadicDelta m) ε_N ≤
                  (Real.rpow (Real.log (1 / dyadicDelta k)) C_P * Real.rpow (1 / dyadicDelta m) ε_N) * Real.rpow (dyadicDelta m) ε_N :=
                mul_le_mul_of_nonneg_right hCb h_rpow_nonneg
              have h12 : (Real.rpow (Real.log (1 / dyadicDelta k)) C_P * Real.rpow (1 / dyadicDelta m) ε_N) * Real.rpow (dyadicDelta m) ε_N =
                  Real.rpow (Real.log (1 / dyadicDelta k)) C_P := by
                rw [mul_assoc, h9, mul_one]
              rw [h12] at h11
              exact h11
            exact h10
          · have hmax : max (C_between ⟨0, by omega⟩) 1 = 1 := by
              rw [max_eq_right] <;> linarith
            rw [hmax]
            have h11 : Real.rpow (dyadicDelta m) ε_N ≤ 1 := by
              exact Real.rpow_le_one (dyadicDelta_pos m).le (dyadicDelta_le_one m) hεN.le
            have h12 : (1 : ℝ) ≤ Real.rpow (Real.log (1 / dyadicDelta k)) C_P := by
              apply Real.one_le_rpow hlogδ_ge1 hCP_nonneg
            linarith
        -- Main polynomial domination + combine via helper lemmas
        let logδ := Real.log (1 / dyadicDelta k)
        let logΔm := Real.log (1 / dyadicDelta m)
        let A_normal := K * (81 * ((2700 : ℝ) * 3145728 * (4 * (k : ℝ) + 7)^7) * (2 * Real.sqrt 2) ^ s) * 13 * (2 : ℝ) ^ s
        let Cb := max (C_between ⟨0, by omega⟩) 1
        let δm := dyadicDelta m
        have h_main_poly : Real.rpow τ (C_P + 8) * logδ ^ 8 ≥ A_normal := by
          have h_k_ge : (k : ℝ) ≥ C_absorb := le_trans hK_absorb (by exact_mod_cast hk_ge_absorb)
          have h_logδ_eq : logδ = (k : ℝ) * Real.log 2 := by
            dsimp only [logδ]
            have h4 : 1 / dyadicDelta k = Real.rpow 2 (k : ℝ) := by simp [dyadicDelta] <;> field_simp <;> ring
            rw [h4]
            simpa using Real.log_rpow (by norm_num) (k : ℝ)
          rw [h_logδ_eq]
          have h5 : C_absorb * (k : ℝ) ^ 7 ≤ (k : ℝ) ^ 8 :=
            Prop73Restructure.absorb_power h_k_ge (by positivity)
          let D := Real.rpow τ (C_P + 8) * (Real.log 2) ^ 8
          let B_normal := K * 81 * (2700 * 3145728) * 13 * (2 * Real.sqrt 2) * (2 : ℝ) ^ s * (5 : ℝ) ^ 7
          have hD : 0 < D := by
            have h1 : 0 < Real.rpow τ (C_P + 8) := Real.rpow_pos_of_pos hτ (C_P + 8)
            have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
            exact mul_pos h1 (pow_pos h2 8)
          have hC : C_absorb = B_normal / D := by
            dsimp only [D, C_absorb, B_normal] <;> field_simp [hD.ne'] <;> ring
          have h9 : B_normal * (k : ℝ) ^ 7 ≤ D * (k : ℝ) ^ 8 :=
            Prop73Restructure.threshold_scale hD hC h5
          have h9_conv : D * (k : ℝ) ^ 8 = Real.rpow τ (C_P + 8) * ((k : ℝ) * Real.log 2) ^ 8 := by
            dsimp only [D] <;> ring
          rw [h9_conv] at h9
          have hcommon : 0 ≤ K * 81 * (2700 * 3145728) * 13 * Real.rpow 2 s :=
            Prop73Restructure.normal_common_nonneg K s hK_pos
          have hbase : Real.rpow (2 * Real.sqrt 2) s ≤ 2 * Real.sqrt 2 := Prop73Restructure.sqrt_bound s hs hs1
          have hpoly : (4 * (k : ℝ) + 7) ^ 7 ≤ (5 : ℝ) ^ 7 * (k : ℝ) ^ 7 := Prop73Restructure.poly_bound1 k hk7
          have hpoly_nonneg : 0 ≤ (4 * (k : ℝ) + 7) ^ 7 := by positivity
          have h12 := Prop73Restructure.normal_fixed_factor K s (k : ℝ) hcommon hbase hpoly hpoly_nonneg
          exact le_trans h12 h9
        have hA_normal_pos : 0 < A_normal := by positivity
        have hCb_nonneg : 0 ≤ Cb := by positivity
        have hδm_pos : 0 < δm := dyadicDelta_pos m
        have h_final := Prop73Restructure.coarse_absorption_normal
          hlogδ_pos hlogδ_ge1 hCP_nonneg hτ hlogm_ge
          hA_normal_pos hCb_nonneg hδm_pos h_main_poly hmax_cancel
        have h_rhs : A_normal * Cb * Real.rpow δm ε_N =
            K * (81 * ((2700 : ℝ) * 3145728 * (4 * (k : ℝ) + 7)^7) *
              max (C_between ⟨0, by omega⟩) 1 * (2 * Real.sqrt 2) ^ s) * 13 * (2 : ℝ) ^ s *
            Real.rpow (dyadicDelta m) ε_N := by
          dsimp only [A_normal, Cb, δm] <;> ring
        rw [h_rhs] at h_final
        exact h_final
      have h_absorb_coarse_good : ∀ (t_j : ℝ), scaleClass ⟨0, by omega⟩ = ScaleClass.good t_j →
          Real.rpow (Real.log (1 / dyadicDelta m)) (C_P + 8) ≥
          K * (81 * ((2700 : ℝ) * 3145728 * (4 * (k : ℝ) + 7)^7) *
            max (C_between ⟨0, by omega⟩) 1 * (2 * Real.sqrt 2)) * 13 * (2 : ℝ) ^ s *
          Real.rpow (dyadicDelta m) (2 * ε_G + ε_N) := by
        intro t_j h_good
        have hk7 : k ≥ 7 := le_trans hK_absorb7 hk_ge_absorb
        have hlogδ_pos : 0 < Real.log (1 / dyadicDelta k) := by
          apply Real.log_pos
          have h3 : dyadicDelta k < 1 := by
            have h4 : dyadicDelta k ≤ Real.exp (-1) := hk_exp1
            have h5 : Real.exp (-1) < 1 := by
              have h6 : Real.exp (-1 : ℝ) < Real.exp 0 := Real.exp_strictMono (by norm_num)
              have h7 : Real.exp 0 = 1 := by simp
              rw [h7] at h6; exact h6
            exact lt_of_le_of_lt h4 h5
          exact one_lt_one_div (dyadicDelta_pos k) h3
        have hlogδ_ge1 : 1 ≤ Real.log (1 / dyadicDelta k) :=
          Prop73Restructure.dyadicDelta_log_ge_one hk_ge_2
        have hCP_nonneg : 0 ≤ C_P := by linarith [hCP]
        have hεG_pos : 0 < ε_G := hεG
        -- Scale ratio gives m ≥ τ*k
        have h_scale0 := hcfg.h_scale_ratio ⟨0, by omega⟩ (by simp [h_good, ScaleClass.isBad])
        have hΔ0 : Δ 0 = 1 := hcfg.hΔ_start
        have hΔ1 : Δ 1 = dyadicDelta m := hm_eq2
        have h_scale_ratio0 : Δ 1 / Δ 0 ≤ Real.rpow (dyadicDelta k) τ :=
          Prop73Restructure.first_scale_ratio hn Δ (Real.rpow (dyadicDelta k) τ) h_scale0
        have h_scale_ratio1 : dyadicDelta m ≤ Real.rpow (dyadicDelta k) τ := by
          simpa [div_one, hΔ0, hΔ1] using h_scale_ratio0
        have hm_geτk : (m : ℝ) ≥ τ * (k : ℝ) :=
          scale_ratio_to_ge hτ h_scale_ratio1
        have hlogm_ge : Real.log (1 / dyadicDelta m) ≥ τ * Real.log (1 / dyadicDelta k) := by
          have h1 : Real.log (1 / dyadicDelta m) = (m : ℝ) * Real.log 2 := by
            have h2 : 1 / dyadicDelta m = Real.rpow 2 (m : ℝ) := by
              simp [dyadicDelta] <;> field_simp <;> ring
            rw [h2]; simpa using Real.log_rpow (by norm_num) (m : ℝ)
          have h3 : Real.log (1 / dyadicDelta k) = (k : ℝ) * Real.log 2 := by
            have h4 : 1 / dyadicDelta k = Real.rpow 2 (k : ℝ) := by
              simp [dyadicDelta] <;> field_simp <;> ring
            rw [h4]; simpa using Real.log_rpow (by norm_num) (k : ℝ)
          rw [h1, h3]
          have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
          calc (m : ℝ) * Real.log 2
            ≥ (τ * (k : ℝ)) * Real.log 2 := by gcongr
          _ = τ * ((k : ℝ) * Real.log 2) := by ring
        -- Good C_between bound cancellation
        have hCb_good : C_between ⟨0, by omega⟩ ≤ Real.rpow (Real.log (1 / dyadicDelta k)) C_P *
            Real.rpow (1 / dyadicDelta m) ε_G := by
          have h := hcfg.h_C_between_good ⟨0, by omega⟩ t_j h_good
          have h_succ : Fin.succ (⟨0, by omega⟩ : Fin n) = (1 : Fin (n + 1)) := by
            apply Fin.ext
            simp [Nat.mod_eq_of_lt (show 1 < n + 1 by omega)]
          have h_cast : Fin.castSucc (⟨0, by omega⟩ : Fin n) = (0 : Fin (n + 1)) := by
            apply Fin.ext
            simp [Nat.mod_eq_of_lt (show 0 < n + 1 by omega)]
          rw [h_succ, h_cast, hcfg.hΔ_start, hm_eq2] at h
          simpa using h
        have hmax_cancel_good : max (C_between ⟨0, by omega⟩) 1 * Real.rpow (dyadicDelta m) (2 * ε_G + ε_N) ≤
            Real.rpow (Real.log (1 / dyadicDelta k)) C_P := by
          have h_pos1 : 0 < Real.rpow (dyadicDelta m) (2 * ε_G + ε_N) := Real.rpow_pos_of_pos (dyadicDelta_pos m) _
          by_cases h : C_between ⟨0, by omega⟩ ≥ 1
          · have hmax : max (C_between ⟨0, by omega⟩) 1 = C_between ⟨0, by omega⟩ := by
              rw [max_eq_left] <;> linarith
            rw [hmax]
            have h9 : Real.rpow (1 / dyadicDelta m) ε_G * Real.rpow (dyadicDelta m) (2 * ε_G + ε_N) =
                Real.rpow (dyadicDelta m) (ε_G + ε_N) := by
              have h1 : 1 / dyadicDelta m = (dyadicDelta m)⁻¹ := by ring
              have h10 : Real.rpow (1 / dyadicDelta m) ε_G = Real.rpow (dyadicDelta m) (-ε_G) := by
                rw [h1]
                exact (Real.rpow_neg_eq_inv_rpow (dyadicDelta m) ε_G).symm
              rw [h10]
              have h_add : Real.rpow (dyadicDelta m) (-ε_G) * Real.rpow (dyadicDelta m) (2 * ε_G + ε_N) =
                  Real.rpow (dyadicDelta m) ((-ε_G) + (2 * ε_G + ε_N)) := by
                exact (Real.rpow_add (dyadicDelta_pos m) (-ε_G) (2 * ε_G + ε_N)).symm
              rw [h_add]
              have h_sum : (-ε_G) + (2 * ε_G + ε_N) = ε_G + ε_N := by ring
              rw [h_sum]
            have h10 : C_between ⟨0, by omega⟩ * Real.rpow (dyadicDelta m) (2 * ε_G + ε_N) ≤
                Real.rpow (Real.log (1 / dyadicDelta k)) C_P * Real.rpow (dyadicDelta m) (ε_G + ε_N) := by
              have h_rpow_nonneg : 0 ≤ Real.rpow (dyadicDelta m) (2 * ε_G + ε_N) := by positivity
              have h11 : C_between ⟨0, by omega⟩ * Real.rpow (dyadicDelta m) (2 * ε_G + ε_N) ≤
                  (Real.rpow (Real.log (1 / dyadicDelta k)) C_P * Real.rpow (1 / dyadicDelta m) ε_G) * Real.rpow (dyadicDelta m) (2 * ε_G + ε_N) :=
                mul_le_mul_of_nonneg_right hCb_good h_rpow_nonneg
              rw [mul_assoc] at h11
              rw [h9] at h11
              exact h11
            have h11 : Real.rpow (dyadicDelta m) (ε_G + ε_N) ≤ 1 := by
              have h_exp_pos : 0 ≤ ε_G + ε_N := by linarith [hεG, hεN]
              exact Real.rpow_le_one (dyadicDelta_pos m).le (dyadicDelta_le_one m) h_exp_pos
            have h12 : Real.rpow (Real.log (1 / dyadicDelta k)) C_P * Real.rpow (dyadicDelta m) (ε_G + ε_N) ≤
                Real.rpow (Real.log (1 / dyadicDelta k)) C_P := by
              have hA_nonneg : 0 ≤ Real.rpow (Real.log (1 / dyadicDelta k)) C_P := Real.rpow_nonneg (by linarith) C_P
              have h : Real.rpow (Real.log (1 / dyadicDelta k)) C_P * Real.rpow (dyadicDelta m) (ε_G + ε_N) ≤ Real.rpow (Real.log (1 / dyadicDelta k)) C_P * 1 :=
                mul_le_mul_of_nonneg_left h11 hA_nonneg
              simpa using h
            exact le_trans h10 h12
          · have hmax : max (C_between ⟨0, by omega⟩) 1 = 1 := by
              rw [max_eq_right] <;> linarith
            rw [hmax]
            have h11 : Real.rpow (dyadicDelta m) (2 * ε_G + ε_N) ≤ 1 := by
              have h_exp_pos : 0 ≤ 2 * ε_G + ε_N := by linarith [hεG, hεN]
              exact Real.rpow_le_one (dyadicDelta_pos m).le (dyadicDelta_le_one m) h_exp_pos
            have h12 : (1 : ℝ) ≤ Real.rpow (Real.log (1 / dyadicDelta k)) C_P := by
              apply Real.one_le_rpow hlogδ_ge1 hCP_nonneg
            linarith
        -- Main polynomial domination + combine via helper lemmas
        let logδ_g := Real.log (1 / dyadicDelta k)
        let logΔm_g := Real.log (1 / dyadicDelta m)
        let A_good := K * (81 * ((2700 : ℝ) * 3145728 * (4 * (k : ℝ) + 7)^7) * (2 * Real.sqrt 2)) * 13 * (2 : ℝ) ^ s
        let Cb_g := max (C_between ⟨0, by omega⟩) 1
        let δm_g := dyadicDelta m
        have h_main_poly_good : Real.rpow τ (C_P + 8) * logδ_g ^ 8 ≥ A_good := by
          have h_k_ge : (k : ℝ) ≥ C_absorb := le_trans hK_absorb (by exact_mod_cast hk_ge_absorb)
          have h_logδ_eq : logδ_g = (k : ℝ) * Real.log 2 := by
            dsimp only [logδ_g]
            have h4 : 1 / dyadicDelta k = Real.rpow 2 (k : ℝ) := by simp [dyadicDelta] <;> field_simp <;> ring
            rw [h4]; simpa using Real.log_rpow (by norm_num) (k : ℝ)
          rw [h_logδ_eq]
          have h5 : C_absorb * (k : ℝ) ^ 7 ≤ (k : ℝ) ^ 8 :=
            Prop73Restructure.absorb_power h_k_ge (by positivity)
          let D := Real.rpow τ (C_P + 8) * (Real.log 2) ^ 8
          let B_good := K * 81 * (2700 * 3145728) * 13 * (2 * Real.sqrt 2) * (2 : ℝ) ^ s * (5 : ℝ) ^ 7
          have hD : 0 < D := by
            have h1 : 0 < Real.rpow τ (C_P + 8) := Real.rpow_pos_of_pos hτ (C_P + 8)
            have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
            exact mul_pos h1 (pow_pos h2 8)
          have hC : C_absorb = B_good / D := by
            dsimp only [D, C_absorb, B_good] <;> field_simp [hD.ne'] <;> ring
          have h9 : B_good * (k : ℝ) ^ 7 ≤ D * (k : ℝ) ^ 8 :=
            Prop73Restructure.threshold_scale hD hC h5
          have h9_conv : D * (k : ℝ) ^ 8 = Real.rpow τ (C_P + 8) * ((k : ℝ) * Real.log 2) ^ 8 := by
            dsimp only [D] <;> ring
          rw [h9_conv] at h9
          have hcommon : 0 ≤ K * 81 * (2700 * 3145728) * 13 * (2 * Real.sqrt 2) * Real.rpow 2 s :=
            Prop73Restructure.good_common_nonneg K s hK_pos
          have hpoly : (4 * (k : ℝ) + 7) ^ 7 ≤ (5 : ℝ) ^ 7 * (k : ℝ) ^ 7 := Prop73Restructure.poly_bound1 k hk7
          have h12 := Prop73Restructure.good_fixed_factor K s (k : ℝ) hcommon hpoly
          exact le_trans h12 h9
        have hA_good_pos : 0 < A_good := by positivity
        have hCb_g_nonneg : 0 ≤ Cb_g := by positivity
        have hδm_g_pos : 0 < δm_g := dyadicDelta_pos m
        have h_final_g := Prop73Restructure.coarse_absorption_good
          hlogδ_pos hlogδ_ge1 hCP_nonneg hτ hlogm_ge
          hA_good_pos hCb_g_nonneg hδm_g_pos h_main_poly_good hmax_cancel_good
        have h_rhs_g : A_good * Cb_g * Real.rpow δm_g (2 * ε_G + ε_N) =
            K * (81 * ((2700 : ℝ) * 3145728 * (4 * (k : ℝ) + 7)^7) *
              max (C_between ⟨0, by omega⟩) 1 * (2 * Real.sqrt 2)) * 13 * (2 : ℝ) ^ s *
            Real.rpow (dyadicDelta m) (2 * ε_G + ε_N) := by
          dsimp only [A_good, Cb_g, δm_g] <;> ring
        rw [h_rhs_g] at h_final_g
        exact h_final_g
      -- Reuse KSpec adapter instantiated outside induction
      have hK_p5_spec := hK_p5_spec_adapted
      -- h_good_improved_incidence: provided by caller via UniformIncidenceData + coarse config
      -- Call inductive_step_core_v2
      classical
      -- Helper: L = log(1/δbar), L_k = log(1/δ_k)
      let L_fine := Real.log (1 / dyadicDelta (k - m))
      let L_k_fine := Real.log (1 / dyadicDelta k)
      have hLk_eq : L_k_fine = (k : ℝ) * Real.log 2 := by
        simp [L_k_fine, dyadicDelta, Real.log_div, Real.log_pow] <;> ring
      have hL_eq : L_fine = ((k - m : ℕ) : ℝ) * Real.log 2 := by
        simp [L_fine, dyadicDelta, Real.log_div, Real.log_pow] <;> ring
      have hLk_le_k : L_k_fine ≤ (k : ℝ) := by
        rw [hLk_eq]
        exact Prop73Restructure.index_log_two_le k
      have hL_le_k : L_fine ≤ (k : ℝ) := by
        rw [hL_eq]
        exact Prop73Restructure.tail_index_log_two_le k m
      have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      -- Polynomial domination constant
      have h_fine_poly : (k : ℝ)^(n + 2) ≥ C_fine_total := by
        have h1 : (k : ℝ) ≥ C_fine_total := by
          have h2 : (k : ℝ) ≥ (K_fine : ℝ) := by exact_mod_cast hk_ge_fine
          have h3 : (K_fine : ℝ) ≥ max 1 C_fine_total := Nat.le_ceil _
          have h4 : (K_fine : ℝ) ≥ C_fine_total := by
            have h5 : max 1 C_fine_total ≥ C_fine_total := le_max_right _ _
            linarith
          linarith
        have h5 : (k : ℝ) ≥ 1 := hk_ge_one
        have h6 : (k : ℝ)^(n + 2) ≥ (k : ℝ) := by
          have h71 : 1 ≤ (k : ℝ) := h5
          have h72 : 1 ≤ n + 2 := by omega
          have h : (k : ℝ)^1 ≤ (k : ℝ)^(n + 2) := pow_le_pow_right₀ h71 h72
          simpa using h
        linarith
      -- Generic fine absorption for exponent ε > 0, at a specific non-bad index j
      have h_fine_absorb_core : ∀ (ε : ℝ), 0 < ε →
          ∀ (j : Fin (n - 1)),
          (C_between (Prop73Restructure.finSuccN h2 j) ≤ L_k_fine ^ C_P *
            (Δ (Prop73Restructure.finCast1N h2 j) / Δ (Prop73Restructure.finSucc2N h2 j)) ^ ε) →
          ∀ (K : ℝ), 1 ≤ K → K ≤ 2700 * 3145728 * (4 * (k : ℝ) + 7)^7 →
          scaleClass (Prop73Restructure.finSuccN h2 j) ≠ ScaleClass.bad →
            9 * (C_between (Prop73Restructure.finSuccN h2 j)) * 2 * K *
              (24 * L_fine / ((n - 1 : ℕ) : ℝ)) ^ (n - 1) * (4 : ℝ) ^ (n - 1) ≤
            L_fine ^ C_P_fine * (Δ (Prop73Restructure.finCast1N h2 j) / Δ (Prop73Restructure.finSucc2N h2 j)) ^ ε := by
        intro ε hε_pos j hCb K hK_ge1 hK_bound hj_nonbad
        let idx : Fin n := Prop73Restructure.finSuccN h2 j
        let idx2 : Fin (n + 1) := Prop73Restructure.finSucc2N h2 j
        have hCb' : C_between idx ≤ L_k_fine ^ C_P * (Δ (Fin.castSucc idx) / Δ idx2) ^ ε := by
          exact hCb
        -- Derive L_fine ≥ τ * L_k_fine from non-bad tail scale
        have h_exists : ∃ (j' : Fin n), j' ∈ (Finset.univ.erase (⟨0, by omega⟩ : Fin n)) ∧ ¬(scaleClass j').isBad := by
          let zero : Fin n := ⟨0, by omega⟩
          have h1 : idx ≠ zero := by
            intro h
            have h2 : idx.val = 0 := by exact congr_arg Fin.val h
            have h3 : idx.val = j.val + 1 := by
              simp [idx, Prop73Restructure.finSuccN]
            rw [h3] at h2
            omega
          refine' ⟨idx, _, _⟩
          · rw [Finset.mem_erase] <;> exact ⟨h1, Finset.mem_univ _⟩
          · have h4 : scaleClass idx ≠ ScaleClass.bad := by
              dsimp only [idx]
              exact hj_nonbad
            simpa [ScaleClass.isBad] using h4
        have hΔn_lt_Δ1 : Δ (Fin.last n) < Δ 1 := by
          have h_chain : Δ (Fin.last n) ≤ Δ (2 : Fin (n + 1)) :=
            delta_chain_property hcfg.hΔ_strict hcfg.hΔ_start (2 : Fin (n + 1))
          let one_fin : Fin n := ⟨1, by omega⟩
          have h4 : Δ (Fin.succ one_fin) < Δ (Fin.castSucc one_fin) := hcfg.hΔ_strict one_fin
          have h_eq1 : (2 : Fin (n + 1)) = Fin.succ one_fin := by
            apply Fin.ext; simp [one_fin] <;> omega
          have h_eq2 : (1 : Fin (n + 1)) = Fin.castSucc one_fin := by
            apply Fin.ext; simp [one_fin] <;> omega
          have h_strict : Δ (2 : Fin (n + 1)) < Δ (1 : Fin (n + 1)) := by
            rw [h_eq1, h_eq2]; exact h4
          exact h_chain.trans_lt h_strict
        have hΔk_lt_Δm : dyadicDelta k < dyadicDelta m := by
          rw [←hcfg.hΔ_end, ←hm_eq2]; exact hΔn_lt_Δ1
        have hkm : m ≤ k := le_of_lt (Prop73Restructure.dyadicDelta_strict_anti hΔk_lt_Δm)
        have hδbar_eq2 : dyadicDelta (k - m) = Δ (Fin.last n) / Δ 1 := by
          rw [hcfg.hΔ_end, hm_eq2]
          have h_mul : dyadicDelta (k - m) * dyadicDelta m = dyadicDelta k := by
            have h_sub : k - m + m = k := by omega
            simpa [dyadicDelta, pow_add] using congr_arg (fun x : ℕ => (2 : ℝ)⁻¹ ^ x) h_sub
          field_simp [dyadicDelta] <;> linarith
        have hδbar_le : dyadicDelta (k - m) ≤ (dyadicDelta k)^τ :=
          tail_nonbad_deltabar_le_deltaτ h2 hτ Δ scaleClass hcfg.hΔ_pos hcfg.hΔ_strict hcfg.h_scale_ratio
            (dyadicDelta (k - m)) hδbar_eq2 h_exists
        have hL_ge : L_fine ≥ τ * L_k_fine := by
          have h1 : 0 < dyadicDelta (k - m) := dyadicDelta_pos (k - m)
          have h2 : 0 < (dyadicDelta k)^τ := Real.rpow_pos_of_pos (dyadicDelta_pos k) τ
          have h3 : Real.log (1 / dyadicDelta (k - m)) ≥ Real.log (1 / (dyadicDelta k)^τ) :=
            Real.log_le_log (by positivity) (one_div_le_one_div_of_le (by positivity) hδbar_le)
          have h4 : Real.log (1 / (dyadicDelta k)^τ) = τ * Real.log (1 / dyadicDelta k) := by
            have h5 : Real.log (1 / (dyadicDelta k)^τ) = -Real.log ((dyadicDelta k)^τ) := by
              rw [show (1 / (dyadicDelta k)^τ) = ((dyadicDelta k)^τ)⁻¹ by ring]
              rw [Real.log_inv]
            rw [h5]
            have h6 : Real.log ((dyadicDelta k)^τ) = τ * Real.log (dyadicDelta k) := Real.log_rpow (dyadicDelta_pos k) τ
            rw [h6]
            have h7 : Real.log (1 / dyadicDelta k) = -Real.log (dyadicDelta k) := by
              rw [Real.log_div (by norm_num) (dyadicDelta_pos k).ne', Real.log_one, zero_sub]
            rw [h7] <;> ring
          rw [h4] at h3; exact h3
        -- Positivity
        have hLk_nonneg : 0 ≤ L_k_fine := by
          rw [hLk_eq]; exact mul_nonneg (by linarith [hk_ge_one]) (by linarith [hlog2_pos])
        have hL_fine_nonneg : 0 ≤ L_fine := by
          rw [hL_eq]; exact mul_nonneg (by positivity) (by linarith [hlog2_pos])
        -- C_fine_total cancellation
        have hC_cancel : C_fine_total * (τ * Real.log 2)^C_P_fine =
            18 * (2700 * 3145728 * (11 : ℝ)^7) *
            (((24 : ℝ) / ((n - 1 : ℕ) : ℝ))^(n - 1)) * (4 : ℝ)^(n - 1) := by
          exact Prop73Restructure.fine_C_cancel
            C_fine_total C_P C_n C_P_fine τ n h2 hτ hlog2_pos
            (by dsimp only [C_fine_total] <;> rfl) hCP_fine_eq
        -- Degree equality
        have h_deg : (n : ℝ) + 6 + C_P = C_P_fine - ((n : ℝ) + 2) := by
          rw [hCP_fine_eq]
          exact Prop73Restructure.fine_spare_degree C_P n
        -- Ratio positivity
        have h_ratio_pos : 0 < Δ (Fin.castSucc idx) / Δ idx2 := by
          apply div_pos <;> exact hcfg.hΔ_pos _
        -- Call scalar absorption helper
        exact Prop73Restructure.fine_scalar_absorption
          n h2 k hk_ge_one τ hτ C_P C_P_fine (by linarith [hCP]) hCP_fine hlog2_pos
          L_fine L_k_fine C_fine_total
          hL_fine_nonneg hLk_nonneg hLk_eq hLk_le_k hL_le_k hL_ge
          h_fine_poly hC_cancel h_deg
          (C_between idx) K hK_ge1 hK_bound
          (Δ (Fin.castSucc idx) / Δ idx2) h_ratio_pos ε hε_pos hCb'
      -- Normal case: per-index bound from hcfg.h_C_between_normal
      have h_absorb_fine_normal' : ∀ (K : ℝ), 1 ≤ K →
          K ≤ 2700 * 3145728 * (4 * (k : ℝ) + 7)^7 →
          ∀ (j : Fin (n - 1)), scaleClass (Prop73Restructure.finSuccN h2 j) = ScaleClass.normal →
            9 * (C_between (Prop73Restructure.finSuccN h2 j)) * 2 * K *
              (24 * L_fine / ((n - 1 : ℕ) : ℝ)) ^ (n - 1) * (4 : ℝ) ^ (n - 1) ≤
            L_fine ^ C_P_fine * (Δ (Prop73Restructure.finCast1N h2 j) / Δ (Prop73Restructure.finSucc2N h2 j)) ^ ε_N := by
        intro K hK_ge1 hK_bound j hj
        let idx : Fin n := Prop73Restructure.finSuccN h2 j
        let idx2 : Fin (n + 1) := Prop73Restructure.finSucc2N h2 j
        have h_log_eq : Real.log (1 / dyadicDelta k) = L_k_fine := by
          rw [hLk_eq]; simp [dyadicDelta, Real.log_div, Real.log_pow] <;> ring
        have hCb : C_between idx ≤ L_k_fine ^ C_P * (Δ (Fin.castSucc idx) / Δ idx2) ^ ε_N := by
          have h := hcfg.h_C_between_normal idx hj
          rw [h_log_eq] at h
          exact h
        have h_nonbad : scaleClass idx ≠ ScaleClass.bad := by
          rw [hj]; simp
        exact h_fine_absorb_core ε_N hεN j hCb K hK_ge1 hK_bound h_nonbad
      -- Pre-derive absorption facts for good-case wrapper (reduces lambda expression size)
      have h6_abs_wrapper : (9 * (2700 : ℝ) * 3145728 * (11 : ℝ)^7) * (k : ℝ)^(7 + C_P) < Real.rpow (dyadicDelta k) (-(τ * ε_inc / 2)) :=
        hK_absorb2_exp k hk_ge_absorb2
      have hlam_le_τε_half_wrapper : lam ≤ τ * ε_inc / 2 :=
        le_trans hlam_le hlam0_le_τε_half
      exact Prop73Restructure.inductive_step_core_v2
        (m := m)
        (hs := hs) (hst := hst) (hs1 := hs1)
        (hτ := hτ) (hτ1 := hτ1)
        (hεG := hεG) (hη := hη) (hεN := hεN) (hεN_le := hεN_le)
        (hCP := hCP) (hCP_fine := hCP_fine)
        (C_n := C_n) (hCn_ge1 := hCn_ge1)
        (hCP_fine_eq := hCP_fine_eq)
        (h2 := h2)
        (hC_fine_pos := hC_fine_pos) (hC'_fine_pos := hC'_fine_pos)
        (K_p5 := K) (hK_p5_ge1 := hK_ge1) (hK_p5_pos := hK_pos)
        (hK_p5_spec := hK_p5_spec)
        (ε_inc := ε_inc)
        (h_eq89 := h_eq89)
        (lam := lam) (hlam := hlam)
        (lam_tail := lam_tail) (hlam_tail_pos := hlam_tail_pos)
        (hτ_lam_tail := hτ_lam_tail)
        (δ_tail := δ_tail) (hδ_tail_pos := hδ_tail_pos)
        (h_ih_bound := h_ih_bound)
        (hδτ_le_dtail := hδτ_le_dtail)
        (h_poly_K_le_δlam := h_poly_K_le_δlam)
        (h_k_large := h_k_large)
        (A := A) (hA_pos := hA_pos) (hA_ge1 := hA_ge1) (hA_eq := hA_eq)
        (hC_pos := hC_pos) (hC'_pos := hC'_pos)
        (hC_ge := hC_ge) (hC'_ge := hC'_ge)
        (hk := hk')
        (config := config)
        (Δ := Δ)
        (hm_eq2 := hm_eq2)
        (scaleClass := scaleClass)
        (N := N)
        (C_between := C_between)
        (h_absorb_coarse := h_absorb_coarse)
        (h_absorb_coarse_good := h_absorb_coarse_good)
        (h_absorb_fine_normal := h_absorb_fine_normal')
        (h_absorb_fine_good := Prop73Restructure.fine_good_adapter
          n h2 k C_P C_P_fine L_fine L_k_fine C_between Δ scaleClass
          ε_G hεG h_fine_absorb_core hcfg.h_C_between_good)
        (h_good_improved_incidence := fun t_j h_good_scale hnm K' CΔ' MΔ' coarseConfig' P' hP_sub' hcoarse_P_eq' h_card_bound' hK_bound' hCΔ_bounds1' hCΔ_bounds2' h_slope_coarse' hP_nonempty' => by
          have hδm_leδR : dyadicDelta m ≤ h_uniform.δR := by
            have h_scale0 := hcfg.h_scale_ratio ⟨0, by omega⟩ (by simp [h_good_scale, ScaleClass.isBad])
            have hΔ0 : Δ 0 = 1 := hcfg.hΔ_start
            have hΔ1 : Δ 1 = dyadicDelta m := hm_eq2
            have h_ratio : dyadicDelta m ≤ Real.rpow (dyadicDelta k) τ := by
              simpa [div_one, hΔ0, hΔ1] using Prop73Restructure.first_scale_ratio hn Δ (Real.rpow (dyadicDelta k) τ) h_scale0
            have hdk_le : dyadicDelta k ≤ Real.rpow h_uniform.δR (1 / τ) := by
              have h1 : dyadicDelta k ≤ δ₀ := hk
              have h2 : δ₀ ≤ Real.rpow h_uniform.δR (1 / τ) := by dsimp only [δ₀]; exact min_le_right _ _
              exact le_trans h1 h2
            have h3 : Real.rpow (dyadicDelta k) τ ≤ h_uniform.δR := by
              have h_posR : 0 < h_uniform.δR := h_uniform.hδR_pos
              have h4 : Real.rpow (Real.rpow h_uniform.δR (1 / τ)) τ = h_uniform.δR := by
                have h_mul : (1 / τ) * τ = 1 := by field_simp [hτ.ne'] <;> ring
                have h_eq : Real.rpow (Real.rpow h_uniform.δR (1 / τ)) τ = Real.rpow h_uniform.δR ((1 / τ) * τ) :=
                  (Real.rpow_mul h_posR.le (1 / τ) τ).symm
                rw [h_eq, h_mul]
                simp
              have h5 : Real.rpow (dyadicDelta k) τ ≤ Real.rpow (Real.rpow h_uniform.δR (1 / τ)) τ :=
                Real.rpow_le_rpow (dyadicDelta_pos k).le hdk_le hτ.le
              rw [h4] at h5; exact h5
            exact le_trans h_ratio h3
          exact good_improved_incidence_wrapper
            s t τ hs hs1 hst n h2 k m hk_ge_one
            ε_G η lam ε_N C_P ε_inc hεG hτ hη hεN hCP
            C_between Δ scaleClass N M config hcfg hB1 h_uniform hextra hm_eq2
            h6_abs_wrapper hlam_le_τε_half_wrapper hδm_leδR
            t_j h_good_scale hnm K' CΔ' MΔ' coarseConfig' P' hP_sub' hcoarse_P_eq' h_card_bound' hK_bound' hCΔ_bounds1' hCΔ_bounds2' h_slope_coarse' hP_nonempty')
        (hcfg := hcfg)
        (hB1 := hB1)
        (h_uniform := h_uniform)
        (hextra := hextra)
/- ### Bounded-consumer front-end

    Provides the `CombiningInductionBody` interface with explicit
    C' bound. Takes UniformIncidenceData as a permanent input parameter.

    Per-configuration data (h_slope, hP_set, good incidence) is derived
    internally from CombiningConfig + B1BridgeHypotheses. -/

/-- The body of CombiningInductionGenuine, parameterized by C and C'. -/
abbrev CombiningInductionBody
    (s t τ ε_G η ε_N C_P : ℝ) (n : ℕ) (C C' : ℝ) : Prop :=
  ∀ (lam : ℝ), 0 < lam →
    ∃ (δ₀ : ℝ), 0 < δ₀ ∧
      ∀ (k : ℕ), dyadicDelta k ≤ δ₀ →
        ∀ (M : ℕ)
          (config : CTNiceConfiguration k s (Real.rpow (dyadicDelta k) (-lam)) M)
          (Δ : Fin (n + 1) → ℝ)
          (scaleClass : Fin n → ScaleClass)
          (N : Fin n → ℕ)
          (C_between : Fin n → ℝ),
          CombiningConfig s t τ n ε_G η lam ε_N C_P C_between k M config Δ scaleClass N →
          B1BridgeHypotheses k config →
          (config.T₀.card : ENNReal) ≥
            ENNReal.ofReal (combiningLowerBound (dyadicDelta k) (M : ℝ) C C' lam s ε_N η n Δ scaleClass)

/-- Combining induction with explicit C' upper bound (bounded-consumer front-end). -/
abbrev CombiningInductionGenuine_bounded
    (s t τ ε_G η ε_N C_P : ℝ) (n : ℕ) : Prop :=
  ∃ (C C' : ℝ), 0 < C ∧ 0 < C' ∧ C' ≤ combiningCprime n τ ∧
    CombiningInductionBody s t τ ε_G η ε_N C_P n C C'

/-- The bounded version implies the ordinary CombiningInductionGenuine. -/
lemma bounded_implies_genuine
    {s t τ ε_G η ε_N C_P : ℝ} {n : ℕ}
    (h : CombiningInductionGenuine_bounded s t τ ε_G η ε_N C_P n) :
    CombiningInductionGenuine s t τ ε_G η ε_N C_P n := by
  rcases h with ⟨C, C', hC_pos, hC'_pos, _, h_body⟩
  exact ⟨C, C', hC_pos, hC'_pos, h_body⟩

/- NOTE: `combining_induction_bounded_clean` is intentionally NOT provided.

    Deriving `CombiningExtraHypotheses_v2` from bare inputs is not possible
    in general. Downstream consumers must use
    `combining_induction_uniform_with_data_bounded` with explicit
    `CombiningExtraHypotheses_v2` hypotheses and UniformIncidenceData. -/

/- ### Numerical evaluation of combiningLowerBound

    Given product bounds and parameter budget, show that
    combiningLowerBound dominates δ^{-(2s+ε_G*η/16)}.

    The exponent calculation (OS Section 9, lines 1336--1339):
      combiningLowerBound
        = L^{-C} * M * δ^{C'λ} * δ^{-s+ε_N} * ∏_G ratio^η * ∏_B 1/ratio
        ≥ L^{-C} * δ^{-s+λ} * δ^{C'λ} * δ^{-s+ε_N} * δ^{-ε_Gη/8} * δ^{ε_N}
        = L^{-C} * δ^{-2s + (1+C')λ + 2ε_N - ε_Gη/8}

    Let R = ε_Gη/16 - (1+C')λ - 2ε_N. If R > 0 and L^{-C} ≥ δ^R, then:
        ≥ δ^R * δ^{-2s + (1+C')λ + 2ε_N - ε_Gη/8}
        = δ^{-2s - ε_Gη/16}.
-/

/-- Evaluate combiningLowerBound against target δ^{-(2s+ε_G*η/16)}.

    Requires:
    - M ≥ δ^{-s+lam} (from nice configuration)
    - Good product: ∏_{j∈G} ratio_j^η ≥ δ^{-ε_G*η/8}
    - Bad product: ∏_{j∈B} 1/ratio_j ≥ δ^{ε_N}
    - Budget: (1+C')*lam + 2*ε_N < ε_G*η/16
    - Log absorption: L^{-C} ≥ δ^R where R = ε_G*η/16 - (1+C')*lam - 2*ε_N
-/
lemma combiningLowerBound_dominates
    {δ M C C' lam s ε_N η ε_G : ℝ} {n : ℕ}
    {Δ : Fin (n + 1) → ℝ} {scaleClass : Fin n → ScaleClass}
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hM_lower : (M : ℝ) ≥ Real.rpow δ (-s + lam))
    (hC_pos : 0 < C) (hC'_pos : 0 < C')
    (hlam_pos : 0 < lam) (hεN_pos : 0 < ε_N)
    (hη_pos : 0 < η) (hεG_pos : 0 < ε_G)
    (h_good_product :
      ∏ j ∈ Finset.univ.filter (fun j : Fin n => (scaleClass j).isGood),
        Real.rpow (Δ j.castSucc / Δ (Fin.succ j)) η ≥
      Real.rpow δ (-ε_G * η / 8))
    (h_bad_product :
      ∏ j ∈ Finset.univ.filter (fun j : Fin n => (scaleClass j).isBad),
        Δ (Fin.succ j) / Δ j.castSucc ≥
      Real.rpow δ ε_N)
    (h_budget : (1 + C') * lam + 2 * ε_N < ε_G * η / 16)
    (h_log_absorb :
      Real.rpow (Real.log (1 / δ)) (-C) ≥
      Real.rpow δ (ε_G * η / 16 - ((1 + C') * lam + 2 * ε_N))) :
    combiningLowerBound δ M C C' lam s ε_N η n Δ scaleClass ≥
      Real.rpow δ (-(2 * s + ε_G * η / 16)) := by
  let G := Finset.univ.filter (fun j : Fin n => (scaleClass j).isGood)
  let B := Finset.univ.filter (fun j : Fin n => (scaleClass j).isBad)
  let R := ε_G * η / 16 - ((1 + C') * lam + 2 * ε_N)
  let E := -2 * s + (1 + C') * lam + 2 * ε_N - ε_G * η / 8
  have hR_pos : 0 < R := by dsimp only [R] <;> linarith
  have hRE : R + E = -(2 * s + ε_G * η / 16) := by
    dsimp only [R, E] <;> ring
  have hL_pos : 0 < Real.log (1 / δ) := by
    apply Real.log_pos
    have h3 : 1 < 1 / δ := by
      apply one_lt_one_div hδ_pos
      exact hδ_lt_one
    exact h3
  have h_rpow_mul : ∀ (x y : ℝ), Real.rpow δ x * Real.rpow δ y = Real.rpow δ (x + y) := by
    intro x y
    exact (Real.rpow_add hδ_pos x y).symm
  have h_exp_eq : ((-s + lam) + C' * lam) + (-s + ε_N) + (-ε_G * η / 8) + ε_N = E := by
    dsimp only [E] <;> linarith
  have h1 : Real.rpow δ (-s + lam) * Real.rpow δ (C' * lam) * Real.rpow δ (-s + ε_N) *
      Real.rpow δ (-ε_G * η / 8) * Real.rpow δ ε_N = Real.rpow δ E := by
    rw [h_rpow_mul (-s + lam) (C' * lam), h_rpow_mul ((-s + lam) + C' * lam) (-s + ε_N),
        h_rpow_mul (((-s + lam) + C' * lam) + (-s + ε_N)) (-ε_G * η / 8),
        h_rpow_mul ((((-s + lam) + C' * lam) + (-s + ε_N)) + (-ε_G * η / 8)) ε_N]
    rw [h_exp_eq]
  set P_G := (∏ j ∈ G, Real.rpow (Δ j.castSucc / Δ (Fin.succ j)) η) with hPG
  set P_B := (∏ j ∈ B, Δ (Fin.succ j) / Δ j.castSucc) with hPB
  have h_rpow_pos : ∀ (x : ℝ), 0 < Real.rpow δ x := fun x => Real.rpow_pos_of_pos hδ_pos x
  have hG_pos : 0 < P_G := by
    have h : P_G ≥ Real.rpow δ (-ε_G * η / 8) := h_good_product
    exact lt_of_lt_of_le (h_rpow_pos _) h
  have hB_pos : 0 < P_B := by
    have h : P_B ≥ Real.rpow δ ε_N := h_bad_product
    exact lt_of_lt_of_le (h_rpow_pos _) h
  have h_product_ge : (M : ℝ) * Real.rpow δ (C' * lam) * Real.rpow δ (-s + ε_N) * P_G * P_B ≥ Real.rpow δ E := by
    set r1 := Real.rpow δ (C' * lam) with hr1
    set r2 := Real.rpow δ (-s + ε_N) with hr2
    set r3 := Real.rpow δ (-ε_G * η / 8) with hr3
    set r4 := Real.rpow δ ε_N with hr4
    set x := Real.rpow δ (-s + lam) with hx
    have h_pos1 : 0 < r1 := h_rpow_pos _
    have h_pos2 : 0 < r2 := h_rpow_pos _
    have h_pos3 : 0 < r3 := h_rpow_pos _
    have h_pos4 : 0 < r4 := h_rpow_pos _
    have h_posx : 0 < x := h_rpow_pos _
    have hM' : (M : ℝ) ≥ x := hM_lower
    have hG' : P_G ≥ r3 := h_good_product
    have hB' : P_B ≥ r4 := h_bad_product
    have h_step1 : (M : ℝ) * r1 * r2 * P_G * P_B ≥ x * r1 * r2 * P_G * P_B := by
      have h_pos : 0 < r1 * r2 * P_G * P_B := by positivity
      have h : (M : ℝ) * (r1 * r2 * P_G * P_B) ≥ x * (r1 * r2 * P_G * P_B) :=
        mul_le_mul_of_nonneg_right hM' h_pos.le
      simpa [mul_assoc] using h
    have h_step2 : x * r1 * r2 * P_G * P_B ≥ x * r1 * r2 * r3 * P_B := by
      have h_pos : 0 < x * r1 * r2 * P_B := by positivity
      have h : (x * r1 * r2 * P_B) * P_G ≥ (x * r1 * r2 * P_B) * r3 :=
        mul_le_mul_of_nonneg_left hG' h_pos.le
      simpa [mul_assoc, mul_comm, mul_left_comm] using h
    have h_step3 : x * r1 * r2 * r3 * P_B ≥ x * r1 * r2 * r3 * r4 := by
      have h_pos : 0 < x * r1 * r2 * r3 := by positivity
      have h : (x * r1 * r2 * r3) * P_B ≥ (x * r1 * r2 * r3) * r4 :=
        mul_le_mul_of_nonneg_left hB' h_pos.le
      simpa [mul_assoc] using h
    have h_final : x * r1 * r2 * r3 * r4 = Real.rpow δ E := h1
    calc
      (M : ℝ) * r1 * r2 * P_G * P_B
        ≥ x * r1 * r2 * P_G * P_B := h_step1
      _ ≥ x * r1 * r2 * r3 * P_B := h_step2
      _ ≥ x * r1 * r2 * r3 * r4 := h_step3
      _ = Real.rpow δ E := h_final
  have h_log : Real.rpow (Real.log (1 / δ)) (-C) * Real.rpow δ E ≥
      Real.rpow δ (-(2 * s + ε_G * η / 16)) := by
    have h3 : Real.rpow (Real.log (1 / δ)) (-C) ≥ Real.rpow δ R := h_log_absorb
    have h4 : Real.rpow δ R * Real.rpow δ E = Real.rpow δ (R + E) := h_rpow_mul R E
    have hE_rpow_pos : 0 < Real.rpow δ E := h_rpow_pos E
    calc
      Real.rpow (Real.log (1 / δ)) (-C) * Real.rpow δ E
        ≥ Real.rpow δ R * Real.rpow δ E := by gcongr <;> exact hE_rpow_pos.le
      _ = Real.rpow δ (R + E) := h4
      _ = Real.rpow δ (-(2 * s + ε_G * η / 16)) := by rw [hRE]
  have hL_rpow_pos : 0 < Real.rpow (Real.log (1 / δ)) (-C) :=
    Real.rpow_pos_of_pos hL_pos _
  dsimp only [combiningLowerBound]
  calc
    Real.rpow (Real.log (1 / δ)) (-C) * (M : ℝ) * Real.rpow δ (C' * lam) * Real.rpow δ (-s + ε_N) * P_G * P_B
      = Real.rpow (Real.log (1 / δ)) (-C) * ((M : ℝ) * Real.rpow δ (C' * lam) * Real.rpow δ (-s + ε_N) * P_G * P_B) := by ring
    _ ≥ Real.rpow (Real.log (1 / δ)) (-C) * Real.rpow δ E :=
        mul_le_mul_of_nonneg_left h_product_ge hL_rpow_pos.le
    _ ≥ Real.rpow δ (-(2 * s + ε_G * η / 16)) := h_log

/-- Existence of δ₀ for log absorption in the combining bound evaluation.

    Given C > 0 and R > 0, there exists δ₀ > 0 such that for all 0 < δ ≤ δ₀:
      log(1/δ)^{-C} ≥ δ^R.
    This follows from ParameterBudget.polylog_absorption. -/
lemma exists_combining_log_absorb (C R : ℝ) (hC : 0 < C) (hR : 0 < R) :
    ∃ (δ₀ : ℝ), 0 < δ₀ ∧ ∀ (δ : ℝ), 0 < δ → δ < 1 → δ ≤ δ₀ →
      Real.rpow (Real.log (1 / δ)) (-C) ≥ Real.rpow δ R := by
  have h1 := ParameterBudget.polylog_absorption C R hC hR
  rcases h1 with ⟨δ₀, hδ₀_pos, h_main⟩
  refine' ⟨δ₀, hδ₀_pos, _⟩
  intro δ hδ_pos hδ_lt_one hδ_le
  have h2 : Real.rpow (Real.log (1 / δ)) C ≤ Real.rpow δ (-R) := h_main δ hδ_pos hδ_le
  have h_posL : 0 < Real.log (1 / δ) := by
    apply Real.log_pos
    have h3 : 1 < 1 / δ := by
      apply one_lt_one_div hδ_pos
      exact hδ_lt_one
    exact h3
  have h3 : Real.rpow (Real.log (1 / δ)) (-C) = (Real.rpow (Real.log (1 / δ)) C)⁻¹ :=
    Real.rpow_neg (le_of_lt h_posL) C
  have h41 : Real.rpow δ (-R) = (Real.rpow δ R)⁻¹ := Real.rpow_neg (le_of_lt hδ_pos) R
  have h4 : Real.rpow δ R = (Real.rpow δ (-R))⁻¹ := by
    rw [h41]
    have h_pos : 0 < Real.rpow δ R := Real.rpow_pos_of_pos hδ_pos R
    field_simp [h_pos.ne'] <;> ring
  rw [h3, h4]
  have h5 : 0 < Real.rpow (Real.log (1 / δ)) C := Real.rpow_pos_of_pos h_posL _
  have h6 : 0 < Real.rpow δ (-R) := Real.rpow_pos_of_pos hδ_pos _
  gcongr

end DiscretisedFurstenbergEstimate.CombiningTheoremRework
