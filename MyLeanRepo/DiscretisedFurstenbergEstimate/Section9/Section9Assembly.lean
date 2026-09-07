module

/-
  Step 5 — Source-Faithful Integration (v8)

  Corrections from v7:
  1. ε_input source hypotheses (not ε_Root): theorem outputs ∃ ε_input δ₀,
     then ∀ source-data-with-ε_input, conclusion. ε_Root - ε_input absorbs losses.
  2. Interior chart: P_orien ⊆ [1/4,3/4]² → P_ready → P_common chain.
  3. Orientation constant: c_slope = 1/2, point S-set constant = C_P_norm / c_slope.
  4. Nearby-power strictness: use hδ_norm_lt_Δ : δ/4 < Δ, non-strict δ_d ≤ Δ.
  5. Fibre uniformization uses DyadicTube k (not AffineLine).
  6. P_ready S-set enlarged constant: C_P_d * 9 * (K_ready + 1) [logarithmic loss].
  7. squares_common filtering: {q ∈ squares' | q.toSet ∩ P_common ≠ ∅} passed to config.
  8. Config assembly via assemble_config_from_fibres, B1 from interior chart.
  9. multiscaleToCombining_thickened handles general Δ = 2^-q (aurora confirmed).

  Pipeline:
  0. Select uniform λ, δ₀, ε_input (finite_minimum_threshold)
  1. Normalize δ → δ/4
  2. Orient (P_orien, T_orien, Tp_orien, c_slope, interior chart)
  3. Nearby exact scale δ_d = Δ^m, k = q*m, transfer S-sets
  4. Fibre uniformization → squares', tubeFam (DyadicTube), T₀, exact M
  5. P_ready = points of P_orien in squares'
  6. Uniformize/decompose P_ready → P_common + RawMultiscaleDecomp
  7. Map P_common points to their squares
  8. Assemble config from fibres + finalize B1 from interior chart
  8b. multiscaleToCombining_thickened → CombiningConfig
  9. exponent_absorption
  10. Final Ncover transfer (T_orien = T_norm → fixed-ratio → T)
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Section9.Normalization
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Section9.LineNormalizationSSet
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Section9.OrientationPartitionHelper
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Section9.NormalizedSSetTransfer
public import MyLeanRepo.DiscretisedFurstenbergEstimate.SnappingSSetTransfer
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Section9.RawMultiscaleDecomp
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Section9.ThickeningTransfer
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Section9.ExtraHypothesesConstruction
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Section9.GoodProductBound
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Section9.AbsorptionHelpers
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Section9.BudgetVerification
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Section9.Step5IndependentHelpers
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Section9.ThresholdExistentials
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Section9.ScaleTransferHelpers
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Section9.FiniteThreshold
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Section9.ExponentAbsorption
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Section9.RawFibreProducer
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Section9.PReadySSet
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Section9.FibreUniformizationStep
public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.UniformizeWithRepresentatives
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.ContinuousExtraction
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.IncidenceOffsetBound
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicBridge
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.B1BridgeConstruction
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.AbsorptionHypotheses
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.RestructuredStatement
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.BoundedStatement
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.BaseCaseCommon
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CoordinatePartition
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ConstructNiceConfiguration
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicCardToNcover
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DirecretisedFurstenbergEstimate.Section9Assembly

open DirecretisedFurstenbergEstimate.Section9
open DiscretisedFurstenbergEstimate.CombiningTheorem
open DiscretisedFurstenbergEstimate.CombiningTheoremRework
open DiscretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral
open DirecretisedFurstenbergEstimate.MultiscaleDecomposition
open DirecretisedFurstenbergEstimate.FormatConversion
open DirecretisedFurstenbergEstimate.MainAppendix
open Normalization
open CoordinatePartition
open DirecretisedFurstenbergEstimate.FormatConversion.M2 (B1BridgeHypotheses)
open DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral (affineLineSlopeIntercept)
open DyadicCardToNcover (toAffineLine)

abbrev Ncover {X : Type*} [PseudoMetricSpace X] (δ : ℝ) (E : Set X) : ENNReal :=
  Metric.externalCoveringNumber δ.toNNReal E

/-- For any C ≥ 0, ε > 0, there exists δ₀ > 0 such that for 0 < δ ≤ δ₀:
    (log(1/δ))^{-C} ≥ δ^ε.

    Uses polylog_absorption_threshold: log(1/δ)^C ≤ δ^{-ε}, then reciprocate. -/
lemma log_factor_bound_threshold (C ε : ℝ) (hC_nonneg : 0 ≤ C) (hε_pos : 0 < ε) :
    ∃ (δ₀ : ℝ), 0 < δ₀ ∧ ∀ (δ : ℝ), 0 < δ → δ ≤ δ₀ →
      (Real.log (1 / δ)) ^ (-C) ≥ δ ^ ε := by
  by_cases hC : C = 0
  · -- C = 0: log^0 = 1 ≥ δ^ε for δ ≤ 1
    refine ⟨1 / 2, by norm_num, fun δ hδ_pos hδ_le => ?_⟩
    have h1 : δ ≤ 1 := by linarith
    have h2 : δ ^ ε ≤ 1 := Real.rpow_le_one hδ_pos.le h1 hε_pos.le
    simpa [hC] using h2
  · -- C > 0: use polylog_absorption_threshold with C=1, A=C_comb
    have hC_pos : 0 < C := by
      exact lt_of_le_of_ne hC_nonneg (Ne.symm hC)
    rcases polylog_absorption_threshold (1 : ℝ) C ε hC_pos hε_pos (by norm_num)
      with ⟨δ₀, hδ₀_pos, hδ₀_le_one, h1⟩
    let δ₀' : ℝ := min δ₀ (1 / 2)
    have hδ₀'_pos : 0 < δ₀' := by positivity
    have hδ₀'_le : δ₀' ≤ δ₀ := min_le_left _ _
    refine ⟨δ₀', hδ₀'_pos, fun δ hδ_pos hδ_le => ?_⟩
    have hδ_le₀ : δ ≤ δ₀ := le_trans hδ_le hδ₀'_le
    have h2 : (1 : ℝ) * (Real.log (1 / δ)) ^ C ≤ δ ^ (-ε) := h1 δ hδ_pos hδ_le₀
    have h3 : (Real.log (1 / δ)) ^ C ≤ δ ^ (-ε) := by simpa using h2
    have h9 : δ < 1 := by
      have h10 : δ ≤ 1 / 2 := le_trans hδ_le (min_le_right _ _)
      linarith
    have h10 : 1 < 1 / δ := by
      apply one_lt_one_div hδ_pos
      exact h9
    have hlog_pos2 : 0 < Real.log (1 / δ) := Real.log_pos h10
    have h4 : 0 < (Real.log (1 / δ)) ^ C := Real.rpow_pos_of_pos hlog_pos2 C
    have h5 : 0 < δ ^ (-ε) := by positivity
    have h6 : ((Real.log (1 / δ)) ^ C)⁻¹ ≥ (δ ^ (-ε))⁻¹ := by
      have h61 : 1 / (δ ^ (-ε)) ≤ 1 / ((Real.log (1 / δ)) ^ C) :=
        one_div_le_one_div_of_le h4 h3
      have h_eq1 : (1 / ((Real.log (1 / δ)) ^ C)) = ((Real.log (1 / δ)) ^ C)⁻¹ := by
        field_simp
      have h_eq2 : (1 / (δ ^ (-ε))) = (δ ^ (-ε))⁻¹ := by field_simp
      rw [h_eq1, h_eq2] at h61
      exact h61
    have h7 : ((Real.log (1 / δ)) ^ C)⁻¹ = (Real.log (1 / δ)) ^ (-C) := by
      have h71 : (Real.log (1 / δ)) ^ (-C) = ((Real.log (1 / δ)) ^ C)⁻¹ := by
        rw [Real.rpow_neg hlog_pos2.le C] <;> ring
      exact h71.symm
    have h8 : (δ ^ (-ε))⁻¹ = δ ^ ε := by
      have h81 : δ ^ (-ε) = (δ ^ ε)⁻¹ := Real.rpow_neg hδ_pos.le ε
      rw [h81]
      exact inv_inv (δ ^ ε)
    rw [h7, h8] at h6
    exact h6

/-- Helper: combiningC is nonnegative for nonnegative K, C_P. -/
lemma _root_.lagoon_combiningC_nonneg (τ K : ℝ) (hK : 0 ≤ K) (hτ : 0 < τ) :
    ∀ (n : ℕ) (C_P : ℝ), 0 ≤ C_P → 0 ≤ combiningC τ K n C_P := by
  intro n
  induction n with
  | zero =>
    intro C_P hCP
    simp [combiningC] <;> norm_num
  | succ n ih =>
    intro C_P hCP
    by_cases h : n = 0
    · subst h
      simp [combiningC] <;> linarith
    · rcases Nat.exists_eq_succ_of_ne_zero h with ⟨m, rfl⟩
      set C_P_fine : ℝ := C_P + 2 * (((m + 2 : ℝ) + 4)) with hC_P_fine_def
      have h_C_P_fine_nonneg : 0 ≤ C_P_fine := by linarith
      have h_ih' : 0 ≤ combiningC τ K (m + 1) C_P_fine := ih C_P_fine h_C_P_fine_nonneg
      have h_cc' : 0 < combiningCprime (m + 1) τ := combiningCprime_pos (by linarith) hτ
      have h_unfold : combiningC τ K (m + 2) C_P =
          (1 + 7) * (1 + 1 + combiningCprime (m + 1) τ) +
          K + C_P + 8 + combiningC τ K (m + 1) C_P_fine := by
        simp only [combiningC]
        <;> ring
      rw [h_unfold]
      have h1 : 0 ≤ (1 + 7) * (1 + 1 + combiningCprime (m + 1) τ) := by positivity
      have h2 : 0 ≤ K := hK
      have h3 : 0 ≤ C_P := hCP
      have h4 : 0 ≤ (8 : ℝ) := by norm_num
      linarith

/-- Helper: for any natural n, (n : ℝ) + 1 > 0. -/
lemma _root_.lagoon_nat_cast_add_one_pos (n : ℕ) : 0 < (n : ℝ) + 1 := by
  have h : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have h2 : (0 : ℝ) < 1 := by norm_num
  linarith

/-- Helper: scale conversion for negative exponents. If 0 < a ≤ b and p < 0, then b^p ≤ a^p. -/
lemma scale_conversion_neg_exp {a b p : ℝ} (ha : 0 < a) (h : a ≤ b) (hp : p < 0) :
    b ^ p ≤ a ^ p := by
  have h_anti : StrictAntiOn (fun x : ℝ => x ^ p) (Set.Ioi 0) :=
    Real.strictAntiOn_rpow_Ioi_of_exponent_neg hp
  have hb_pos : 0 < b := by linarith
  have ha' : a ∈ Set.Ioi (0 : ℝ) := ha
  have hb' : b ∈ Set.Ioi (0 : ℝ) := hb_pos
  by_cases h_lt : a < b
  · have h_strict : b ^ p < a ^ p := by simpa using h_anti ha' hb' h_lt
    exact h_strict.le
  · have h_eq : a = b := by linarith
    rw [h_eq]

set_option maxHeartbeats 10000000

/-- Source-faithful Step 5 — v8.

    Outputs ε_input and δ₀ first; then for any source data at exponent ε_input
    and scale δ ≤ δ₀, proves the final Ncover lower bound at ε_target. -/
theorem step5_source_faithful_v8
    -- ===== Exponent parameters =====
    (s t τ ε_G η ε_N ε_inc ε_Root ε_bad : ℝ)
    (hs : 0 < s) (hs1 : s < 1) (hst : s < t) (ht2 : t < 2)
    (hτ_pos : 0 < τ) (hτ_lt_one : τ < 1)
    (hεG_pos : 0 < ε_G) (hη_pos : 0 < η) (hεN_pos : 0 < ε_N)
    (hε_inc_pos : 0 < ε_inc) (hε_bad_pos : 0 < ε_bad) (hε_Root_pos : 0 < ε_Root)
    (hεG_le : ε_G ≤ 1) (hη_le : η ≤ 1) (hεN_le_εG : ε_N ≤ ε_G)
    (h_εG_small : ε_G < 2 * (t - s))
    (h_exp_condition : (η + 2 * ε_G) * (1 - s) / (min t 1 - s) + η ≤ ε_inc)
    -- Two output exponents
    (ε_section9 ε_target : ℝ)
    (hε_section9_pos : 0 < ε_section9)
    (hε_target_pos : 0 < ε_target)
    (hε_target_lt_section9 : ε_target < ε_section9)
    -- Combining
    (K_prop73 : ℝ) (hK_ge1 : 1 ≤ K_prop73)
    (h_uniform : UniformIncidenceData s t ε_inc)
    (ε_G0 η0 : ℝ) (hεG0_pos : 0 < ε_G0) (hη0_pos : 0 < η0)
    (hεG_le_uniform : ε_G ≤ ε_G0) (hη_le_uniform : η ≤ η0)
    -- Raw combining induction
    (H_main : ∀ (τ : ℝ), 0 < τ → τ < 1 → ∀ (n : ℕ), 0 < n →
      ∃ (lam_0 : ℝ), 0 < lam_0 ∧
        ∀ (C_P : ℝ), 1 ≤ C_P →
          0 < combiningC τ K_prop73 n C_P ∧
          ∀ (ε_N lam : ℝ), 0 < ε_N → 0 < lam → lam ≤ lam_0 →
            ∀ (h_uniform : UniformIncidenceData s t ε_inc),
              ∃ (δ₀ : ℝ), 0 < δ₀ ∧
              ∀ (ε_G η : ℝ), 0 < ε_G → ε_G ≤ ε_G0 → ε_N ≤ ε_G →
                0 < η → η ≤ η0 →
                  ∀ (k : ℕ), DiscretisedFurstenbergEstimate.dyadicDelta k ≤ δ₀ →
                    ∀ (M : ℕ)
                      (config : DiscretisedFurstenbergEstimate.CombiningTheorem.CTNiceConfiguration k s (Real.rpow (DiscretisedFurstenbergEstimate.dyadicDelta k) (-lam)) M)
                      (Δ : Fin (n + 1) → ℝ)
                      (scaleClass : Fin n → ScaleClass)
                      (N : Fin n → ℕ)
                      (C_between : Fin n → ℝ),
                      CombiningConfig s t τ n ε_G η lam ε_N C_P C_between k M config Δ scaleClass N →
                      B1BridgeHypotheses k config →
                      CombiningExtraHypotheses_v2 s t ε_G η ε_N C_P ε_inc n lam k M config Δ scaleClass →
                      CombiningConclusion s t τ ε_G η ε_N C_P
                        (combiningC τ K_prop73 n C_P) (combiningCprime n τ) lam n Δ scaleClass k M config)
    -- Exponent chain
    (B_K : ℝ) (hB_K_ge3 : B_K ≥ 3)
    (hε_Root_eq : ε_Root = ε_N / (4 * B_K))
    (hε_bad_lt_εN : ε_bad < ε_N)
    (hε_bad_le_quarter_εG : ε_bad ≤ ε_G / 4)
    (hε_bad_lt_half_εG : ε_bad < ε_G / 2)
    -- Combining budget schedule
    (hεN_eq : ε_N = ε_G * η / 100)
    (hε_section9_le : ε_section9 ≤ ε_N / (16 * B_K))
    -- Scale base
    (Δ : ℝ) (q : ℕ) (hq_pos : 0 < q)
    (hΔ_pos : 0 < Δ) (hΔ_lt_one : Δ < 1)
    (hΔ_eq : Δ = (1 / 2 : ℝ) ^ q)
    (hΔ_dyadic : Δ ∈ dyadicScales)
    -- Feasibility: uniformization logarithmic exponent fits in budget
    (h_rho_bound : Real.log (48 * Real.log (1 / Δ)) / Real.log (1 / Δ) ≤ ε_Root / 4)
    -- Transfer constants
    (K_plane K_affine : ℝ) (hK_plane_ge1 : 1 ≤ K_plane) (hK_affine_ge1 : 1 ≤ K_affine)
    -- Reserved budget
    (reserved_budget : ℝ) (hbudget_pos : 0 < reserved_budget)
    -- Root decomposition for fixed τ, ε_bad (supplied by caller from multiscaleDecompKaufman)
    (m0_root : ℕ)
    (H_root : ∀ (m : ℕ), m ≥ m0_root → ∀ (P : Set EuclideanPlane) (N : ℕ → ℕ),
        P ⊆ Metric.closedBall 0 1 →
        IsDyadicUniform P m Δ N →
        IsDeltaSSet (Δ ^ m) t (Real.rpow (Δ ^ m) (-ε_Root)) P →
        ∃ (n : ℕ) (i : ℕ → ℕ) (t_j : ℕ → ℝ)
          (S B : Finset (Fin n)),
          (i 0 = 0) ∧ (i n = m) ∧
          (∀ j < n, i j < i (j + 1)) ∧
          (∀ j : Fin n, t_j j.val ∈ Set.Icc s 2) ∧
          (S ∪ B = Finset.univ) ∧ (Disjoint S B) ∧
          (∀ j : Fin n, j ∈ S →
            (Δ ^ i j.val : ℝ) / (Δ ^ i (j.val + 1)) ≥
              Real.rpow (Δ ^ m) (-τ)) ∧
          (∏ j ∈ B, ((Δ ^ i j.val : ℝ) / (Δ ^ i (j.val + 1)))) ≤
            Real.rpow (Δ ^ m) (-ε_bad) ∧
          (∀ j : Fin n, j ∈ S →
            DirecretisedFurstenbergEstimate.MultiscaleDecomposition.IsSetBetweenScales P
              (Δ ^ i (j.val + 1)) (Δ ^ i j.val) (t_j j.val)
              ((81 : ℝ) * Real.rpow Δ (-4) *
                Real.rpow ((Δ ^ i j.val : ℝ) / (Δ ^ i (j.val + 1))) ε_bad)) ∧
          (∀ j : Fin n, j ∈ S → t_j j.val > s →
            DirecretisedFurstenbergEstimate.MultiscaleDecomposition.IsRegularBetweenScales P
              (Δ ^ i (j.val + 1)) (Δ ^ i j.val) (t_j j.val)
              ((81 : ℝ) * Real.rpow Δ (-4) *
                Real.rpow ((Δ ^ i j.val : ℝ) / (Δ ^ i (j.val + 1))) ε_bad)
              ((81 : ℝ) * Real.rpow Δ (-4) *
                Real.rpow ((Δ ^ i j.val : ℝ) / (Δ ^ i (j.val + 1))) ε_bad)) ∧
          (∏ j ∈ S, Real.rpow ((Δ ^ i j.val : ℝ) / (Δ ^ i (j.val + 1))) (t_j j.val) ≥
            Real.rpow (Δ ^ m) (ε_bad - t)) ∧
          (∀ j : Fin n, j ∈ B →
            ∀ k : Fin n, k.val = j.val + 1 → k ∉ B))
    :
    ∃ (ε_input δ₀ : ℝ),
      0 < ε_input ∧ ε_input < ε_Root ∧ 0 < δ₀ ∧
      ∀ (δ : ℝ) (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
        (hδ_le_Δ : δ ≤ Δ)
        (P : Set EuclideanPlane) (hP_bdd : P ⊆ Metric.closedBall 0 1)
        (hP_sset : IsDeltaSSet δ t (Real.rpow δ (-ε_input)) P)
        (T : Set AffineLine)
        (Tp : ∀ (p : EuclideanPlane), p ∈ P → Set AffineLine)
        (hTp_sub : ∀ p hp, Tp p hp ⊆ T)
        (hTp_sset : ∀ p hp, IsDeltaSSet δ s (Real.rpow δ (-ε_input)) (Tp p hp))
        (hTp_near : ∀ p hp, ∀ ℓ ∈ Tp p hp, p ∈ Metric.cthickening δ ℓ.1)
        (hδ_small : δ ≤ δ₀),
        Ncover δ T ≥ ENNReal.ofReal (Real.rpow δ (-(2 * s + min ε_input ε_target))) := by

  -- ==========================================================================
  -- Step 0: Select uniform λ, δ₀, ε_input (BEFORE introducing source data)
  -- ==========================================================================
  let n0 : ℕ := 2 * Nat.floor (1 / τ) + 1
  have hn0_pos : 0 < n0 := by positivity
  let C'_max : ℝ := combiningCprime n0 τ
  have hC'max_nonneg : 0 ≤ C'_max := (combiningCprime_pos hn0_pos hτ_pos).le
  let budget_lam : ℝ := ε_G * η / 800
  have hbudget_lam_pos : 0 < budget_lam := by positivity

  rcases @finite_minimum_threshold s t ε_inc K_prop73 ε_G0 η0 n0
      hn0_pos H_main
      τ hτ_pos hτ_lt_one (1 : ℝ) (by norm_num)
      ε_N hεN_pos h_uniform
      budget_lam hbudget_lam_pos C'_max hC'max_nonneg
    with ⟨lam, lam_0_uniform, δ₀_uniform, ε_input_0,
      hlam_pos, hlam_0_uniform_pos, hδ₀_uniform_pos, hlam_le_0,
      hbudget_lam, hε_input_0_pos, hε_input_0_lt_lam, H_combining_uniform⟩

  -- Cap ε_input by ε_Root/8 so the gap ε_Root - ε_input absorbs all losses.
  let ε_input : ℝ := min ε_input_0 (ε_Root / 8)
  have hε_input_pos : 0 < ε_input := by
    dsimp only [ε_input]
    exact lt_min hε_input_0_pos (by linarith)
  have hε_input_lt_Root : ε_input < ε_Root := by
    dsimp only [ε_input]
    have h : min ε_input_0 (ε_Root / 8) ≤ ε_Root / 8 := min_le_right _ _
    linarith
  have hε_input_lt_lam : ε_input < lam := by
    dsimp only [ε_input]
    have h : min ε_input_0 (ε_Root / 8) ≤ ε_input_0 := min_le_left _ _
    linarith [hε_input_0_lt_lam]

  -- ==========================================================================
  -- Outer δ₀: finite minimum of ALL absorption thresholds
  -- Each threshold is the scale below which its ledger inequality holds.
  -- ==========================================================================
  let E : ℝ := 2 * s + ε_section9
  have hE_pos : 0 < E := by positivity
  let ε_gap : ℝ := ε_section9 - ε_target
  have hε_gap_pos : 0 < ε_gap := by linarith [hε_target_lt_section9]
  let C_fixed : ℝ := (affineLine_packing_constant : ℝ)^(-3 : ℤ) * Δ^E * 4^E
  have hC_fixed_pos : 0 < C_fixed := by
    dsimp only [C_fixed]
    have hK : 0 < (affineLine_packing_constant : ℝ) := by
      exact_mod_cast DirecretisedFurstenbergEstimate.Snapping.affineLine_packing_constant_pos'
    have h1 : 0 < (affineLine_packing_constant : ℝ)^(-3 : ℤ) := by
      exact zpow_pos hK (-3)
    have h2 : 0 < Δ ^ E := by positivity
    have h3 : 0 < (4 : ℝ) ^ E := by positivity
    exact mul_pos (mul_pos h1 h2) h3
  -- Scale threshold: ensures δ_d = Δ^m ≤ δ₀_uniform
  -- Since δ_d ≤ δ/(4Δ), requiring δ ≤ 4Δ·δ₀_uniform gives δ_d ≤ δ₀_uniform.
  let δ₀_uniform_source : ℝ := 4 * Δ * δ₀_uniform
  have hδ₀_uniform_source_pos : 0 < δ₀_uniform_source := by
    dsimp only [δ₀_uniform_source]
    exact mul_pos (mul_pos (by norm_num) hΔ_pos) hδ₀_uniform_pos

  -- δ_d-scale thresholds (each is the scale below which its ledger holds at δ_d)
  let Kpack : ℝ := affineLine_packing_constant
  -- Fibre-side constant: exact factorization including snap factors
  -- 18*C_raw ≤ δ^(-ε_input) * [36*3721*4^s*58^s*Kpack^(q+10)]
  -- Using δ^(-ε_input) ≤ (4Δ)^(-ε_input) * δ_d^(-ε_input), we get
  -- 18*C_raw ≤ C_fibre_fixed * δ_d^(-ε_input)
  -- where C_fibre_fixed absorbs all parameter-only factors and the (4Δ)^(-ε_input) term.
  let C_fibre_fixed : ℝ :=
    36 * 3721 * (4 : ℝ)^s * (58 : ℝ)^s * Kpack^(q + 10) * (4 * Δ)^(-ε_input)
  have hC_fibre_fixed_nonneg : 0 ≤ C_fibre_fixed := by positivity
  let δ₀_fibre_d : ℝ := Classical.choose
    (fibre_to_lambda_threshold C_fibre_fixed hC_fibre_fixed_nonneg lam ε_input hε_input_pos hε_input_lt_lam)
  -- Square band: K_band ≤ n0, so 9*(K_band+1) ≤ 9*(n0+1)
  let ε_band : ℝ := ε_Root / 8
  let C_band_upper : ℝ := 9 * ((n0 : ℝ) + 1)
  let δ₀_square_band_d : ℝ := Classical.choose
    (constant_absorption_threshold C_band_upper ε_band (by positivity) (by positivity))
  -- Uniformization log factors: absorbed by polylog threshold
  let δ₀_uniformization_d : ℝ := Classical.choose
    (polylog_absorption_threshold (1 : ℝ) (1 : ℝ) (ε_Root / 4) (by norm_num) (by positivity) (by norm_num))
  -- Ambient constant: bounded by 1000000 (from fibre_uniformization_step)
  let K_ambient_upper : ℝ := 1000000
  let δ₀_ambient_d : ℝ := Classical.choose
    (constant_absorption_threshold K_ambient_upper (ε_G * η / 800) (by positivity) (by positivity))
  -- Log thickening: 72900*Δ^-4 absorbed by polylog
  let C_log_upper : ℝ := 72900 * Δ^(-4 : ℝ)
  let δ₀_log_d : ℝ := Classical.choose
    (polylog_absorption_threshold C_log_upper (1 : ℝ) (ε_Root / 8) (by norm_num) (by positivity) (by positivity))

  have hδ₀_fibre_d_pos : 0 < δ₀_fibre_d :=
    (Classical.choose_spec (fibre_to_lambda_threshold C_fibre_fixed hC_fibre_fixed_nonneg lam ε_input hε_input_pos hε_input_lt_lam)).1
  have hδ₀_square_band_d_pos : 0 < δ₀_square_band_d :=
    (Classical.choose_spec (constant_absorption_threshold C_band_upper ε_band (by positivity) (by positivity))).1
  have hδ₀_uniformization_d_pos : 0 < δ₀_uniformization_d :=
    (Classical.choose_spec (polylog_absorption_threshold (1 : ℝ) (1 : ℝ) (ε_Root / 4) (by norm_num) (by positivity) (by norm_num))).1
  have hδ₀_ambient_d_pos : 0 < δ₀_ambient_d :=
    (Classical.choose_spec (constant_absorption_threshold K_ambient_upper (ε_G * η / 800) (by positivity) (by positivity))).1
  have hδ₀_log_d_pos : 0 < δ₀_log_d :=
    (Classical.choose_spec (polylog_absorption_threshold C_log_upper (1 : ℝ) (ε_Root / 8) (by norm_num) (by positivity) (by positivity))).1

  -- Log lower bound: ensures log(1/δ_d) ≥ 72900 * Δ^(-4) for ratio exponent absorption.
  let C_log_lower : ℝ := 72900 * Δ^(-4 : ℝ)
  let δ₀_log_lower_d : ℝ := Real.exp (-C_log_lower)
  have hC_log_lower_pos : 0 < C_log_lower := by positivity
  have hδ₀_log_lower_d_pos : 0 < δ₀_log_lower_d := by positivity
  have hδ₀_log_lower_d_lt_one : δ₀_log_lower_d < 1 := by
    have h1 : -C_log_lower < 0 := by linarith
    have h2 : Real.exp (-C_log_lower) < 1 := Real.exp_lt_one_iff.mpr h1
    exact h2
  have h_log_lower_bound : ∀ (x : ℝ), 0 < x → x ≤ δ₀_log_lower_d → Real.log (1 / x) ≥ C_log_lower := by
    intro x hx_pos hx_le
    have h1 : 1 / x ≥ 1 / δ₀_log_lower_d := one_div_le_one_div_of_le hx_pos hx_le
    have h2 : 1 / δ₀_log_lower_d = Real.exp C_log_lower := by
      dsimp only [δ₀_log_lower_d]
      rw [Real.exp_neg]
      <;> field_simp
    rw [h2] at h1
    have h3 : Real.log (1 / x) ≥ Real.log (Real.exp C_log_lower) := Real.log_le_log (by positivity) h1
    have h4 : Real.log (Real.exp C_log_lower) = C_log_lower := by simp
    rw [h4] at h3
    exact h3

  -- Source-scale pullbacks: θ_source = 4*Δ*θ_d
  -- From δ ≤ θ_source and δ_d ≤ δ/(4*Δ), we get δ_d ≤ θ_d.
  let δ₀_fibre_source : ℝ := 4 * Δ * δ₀_fibre_d
  let δ₀_square_band_source : ℝ := 4 * Δ * δ₀_square_band_d
  let δ₀_uniformization_source : ℝ := 4 * Δ * δ₀_uniformization_d
  let δ₀_ambient_source : ℝ := 4 * Δ * δ₀_ambient_d
  let δ₀_log_source : ℝ := 4 * Δ * δ₀_log_d
  let δ₀_log_lower_source : ℝ := 4 * Δ * δ₀_log_lower_d

  have hδ₀_fibre_source_pos : 0 < δ₀_fibre_source := by positivity
  have hδ₀_square_band_source_pos : 0 < δ₀_square_band_source := by positivity
  have hδ₀_uniformization_source_pos : 0 < δ₀_uniformization_source := by positivity
  have hδ₀_ambient_source_pos : 0 < δ₀_ambient_source := by positivity
  have hδ₀_log_source_pos : 0 < δ₀_log_source := by positivity
  have hδ₀_log_lower_source_pos : 0 < δ₀_log_lower_source := by positivity

  -- Combining log factor threshold: (log(1/δ_d))^{-C_comb} ≥ δ_d^{ε_log_loss}
  -- Use uniform upper bound C_sum over all n ≤ n0, since n_decomp not known yet.
  let ε_log_loss : ℝ := ε_G * η / 800
  have hε_log_loss_pos : 0 < ε_log_loss := by positivity
  let C_combining_sum : ℝ := ∑ n ∈ Finset.Icc 1 n0, combiningC τ K_prop73 n 1
  have hC_combining_sum_nonneg : 0 ≤ C_combining_sum := by
    dsimp only [C_combining_sum]
    apply Finset.sum_nonneg
    intro n hn
    have hK_prop73_pos : 0 < K_prop73 := by linarith
    have hn_pos : 0 < n := by
      have h2 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      linarith
    have h_main_n := H_main τ hτ_pos hτ_lt_one n hn_pos
    exact (Classical.choose_spec h_main_n).2 1 (by norm_num) |>.1.le
  let δ₀_log_combining_d : ℝ := Classical.choose
    (log_factor_bound_threshold C_combining_sum ε_log_loss hC_combining_sum_nonneg hε_log_loss_pos)
  have hδ₀_log_combining_d_pos : 0 < δ₀_log_combining_d :=
    (Classical.choose_spec (log_factor_bound_threshold C_combining_sum ε_log_loss hC_combining_sum_nonneg hε_log_loss_pos)).1
  let δ₀_log_combining_source : ℝ := 4 * Δ * δ₀_log_combining_d
  have hδ₀_log_combining_source_pos : 0 < δ₀_log_combining_source := by positivity

  -- ==========================================================================
  -- Point ledger threshold (via point_to_root_with_band)
  -- Defined at δ_d scale, then pulled back to source scale.
  -- ==========================================================================
  let rho_Delta : ℝ := Real.log (48 * Real.log (1 / Δ)) / Real.log (1 / Δ)
  have hrho_Delta_nonneg : 0 ≤ rho_Delta := by
    dsimp only [rho_Delta]
    have h1 : 0 < Real.log (1 / Δ) := by
      have h11 : 1 < 1 / Δ := by
        apply one_lt_one_div hΔ_pos hΔ_lt_one
      exact Real.log_pos h11
    have hq1 : 1 ≤ q := by omega
    have hΔ_half : Δ ≤ 1 / 2 := by
      rw [hΔ_eq]
      have h : (1 / 2 : ℝ) ^ q ≤ (1 / 2 : ℝ) ^ 1 := by
        have hq1 : 1 ≤ q := by omega
        exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hq1
      simpa using h
    have h2 : 1 / Δ ≥ 2 := by
      calc 1 / Δ ≥ 1 / (1 / 2 : ℝ) := by gcongr
           _ = 2 := by norm_num
    have h3 : Real.log (1 / Δ) ≥ Real.log 2 := Real.log_le_log (by positivity) h2
    have h4 : Real.log 2 ≥ 1 / 2 := by
      have h5 : Real.log (1 / (2 : ℝ)) ≤ 1 / (2 : ℝ) - 1 :=
        Real.log_le_sub_one_of_pos (by norm_num)
      have h6 : Real.log (1 / (2 : ℝ)) = -Real.log 2 := by
        rw [Real.log_div (by norm_num) (by norm_num)] <;> simp
      rw [h6] at h5
      linarith
    have h5 : 48 * Real.log (1 / Δ) ≥ 1 := by
      calc 48 * Real.log (1 / Δ) ≥ 48 * Real.log 2 := by gcongr
           _ ≥ 48 * (1 / 2 : ℝ) := by gcongr
           _ = 24 := by norm_num
           _ ≥ 1 := by norm_num
    have h6 : 0 ≤ Real.log (48 * Real.log (1 / Δ)) := by
      apply Real.log_nonneg
      linarith
    exact div_nonneg h6 h1.le
  have h_rho_bound : rho_Delta ≤ ε_Root / 4 := by
    dsimp only [rho_Delta]
    exact h_rho_bound

  let ε_band : ℝ := ε_Root / 8
  have hε_band_pos : 0 < ε_band := by
    dsimp only [ε_band]
    exact div_pos hε_Root_pos (by norm_num)
  have h_point_sum : ε_input + rho_Delta + ε_band < ε_Root := by
    have h1 : ε_input ≤ ε_Root / 8 := by
      dsimp only [ε_input]
      exact le_trans (min_le_right _ _) (by linarith [hε_Root_pos])
    have h2 : rho_Delta ≤ ε_Root / 4 := h_rho_bound
    dsimp only [ε_band]
    linarith

  -- Fixed point residual: polylog-only constant (independent of δ)
  -- = 2 * 4^t * 9^q * 9 * (4*Δ)^(-ε_input)
  -- Derived from: C_P_norm=δ^{-ε_input}*4^t, C_P_orien=2*C_P_norm, C_P_d=C_P_orien*9^q,
  --   and δ^{-ε_input} ≤ (4*Δ)^{-ε_input}*δ_d^{-ε_input} from δ_d ≤ δ/(4*Δ).
  let point_coeff (x : ℝ) : ℝ := 2 * (4 : ℝ)^t * (9 : ℝ)^q * 9 * (4 * Δ)^(-ε_input)
  -- K_band at dyadic scale x = 2^(-k): square band count = 2*k+7 grows like log(1/x)/log 2
  let K_band (x : ℝ) : ℕ := 2 * Nat.ceil (Real.log (1 / x) / Real.log 2) + 7

  -- Growth bound for K_band: 2*ceil(log(1/x)/log 2)+7 ≤ C*log(1/x)
  have h_K_band_growth : ∃ (C0_band A_band : ℝ), 0 ≤ C0_band ∧ 0 < A_band ∧
      ∃ (δ₂ : ℝ), 0 < δ₂ ∧ ∀ (x : ℝ), 0 < x → x ≤ δ₂ →
        (K_band x : ℝ) ≤ C0_band * (Real.log (1 / x)) ^ A_band := by
    let C0_band : ℝ := 2 / Real.log 2 + 9
    let A_band : ℝ := 1
    let δ₂ : ℝ := Real.exp (-1)
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hC0_nonneg : 0 ≤ C0_band := by positivity
    have hA_pos : 0 < A_band := by norm_num
    have hδ₂_pos : 0 < δ₂ := by positivity
    refine ⟨C0_band, A_band, hC0_nonneg, hA_pos, δ₂, hδ₂_pos, fun x hx hx_le => ?_⟩
    have hlog_ge_one : 1 ≤ Real.log (1 / x) := by
      have h1 : x ≤ Real.exp (-1) := hx_le
      have h2 : 1 / x ≥ Real.exp 1 := by
        have h3 : 1 / x ≥ 1 / Real.exp (-1) := one_div_le_one_div_of_le hx h1
        have h4 : 1 / Real.exp (-1) = Real.exp 1 := by simp [Real.exp_neg]
        rw [h4] at h3; exact h3
      have h5 : Real.log (1 / x) ≥ Real.log (Real.exp 1) := Real.log_le_log (by positivity) h2
      have h6 : Real.log (Real.exp 1) = 1 := by simp
      linarith
    set y : ℝ := Real.log (1 / x) / Real.log 2 with hy_def
    have hy_nonneg : 0 ≤ y := by
      dsimp only [y] <;> positivity
    have h_ceil : (Nat.ceil y : ℝ) < y + 1 := Nat.ceil_lt_add_one hy_nonneg
    have h_ceil_le : (Nat.ceil y : ℝ) ≤ y + 1 := h_ceil.le
    have h71 : ((K_band x : ℝ)) = 2 * (Nat.ceil y : ℝ) + 7 := by
      dsimp only [K_band]
      norm_cast
      <;> ring
    have h7 : (K_band x : ℝ) ≤ 2 * y + 9 := by
      rw [h71]
      have h : 2 * (Nat.ceil y : ℝ) + 7 ≤ 2 * (y + 1) + 7 := by gcongr
      have h2 : 2 * (y + 1) + 7 = 2 * y + 9 := by ring
      rw [h2] at h
      exact h
    have h10 : 9 ≤ 9 * Real.log (1 / x) := by
      have h11 : 1 ≤ Real.log (1 / x) := hlog_ge_one
      calc (9 : ℝ) = 9 * 1 := by ring
           _ ≤ 9 * Real.log (1 / x) := by gcongr
    have h12 : 2 * y = (2 / Real.log 2) * Real.log (1 / x) := by
      dsimp only [y] <;> field_simp [hlog2_pos.ne'] <;> ring
    have h9 : 2 * y + 9 ≤ C0_band * Real.log (1 / x) := by
      dsimp only [C0_band]
      calc 2 * y + 9
        = (2 / Real.log 2) * Real.log (1 / x) + 9 := by rw [h12] <;> ring
      _ ≤ (2 / Real.log 2) * Real.log (1 / x) + 9 * Real.log (1 / x) := by gcongr
      _ = (2 / Real.log 2 + 9) * Real.log (1 / x) := by ring
    have h13 : C0_band * (Real.log (1 / x)) ^ A_band = C0_band * Real.log (1 / x) := by
      dsimp only [A_band]
      simp
    rw [h13]
    exact h7.trans h9

  rcases h_K_band_growth with ⟨C0_band, A_band, hC0_band_nonneg, hA_band_pos, δ₂, hδ₂_pos, h_K_band_bound⟩

  -- Point coefficient polylog bound: point_coeff is constant, so ≤ C*log(1/x) for small x
  let C0_point : ℝ := point_coeff (Real.exp (-1))
  let A_point : ℝ := 1
  have hC0_point_nonneg : 0 ≤ C0_point := by positivity
  have hA_point_pos : 0 < A_point := by norm_num
  have h_point_coeff_bound : ∃ (δ₁ : ℝ), 0 < δ₁ ∧ ∀ (x : ℝ), 0 < x → x ≤ δ₁ →
      point_coeff x ≤ C0_point * (Real.log (1 / x)) ^ A_point := by
    let δ₁ : ℝ := Real.exp (-1)
    have hδ₁_pos : 0 < δ₁ := by positivity
    refine ⟨δ₁, hδ₁_pos, fun x hx hx_le => ?_⟩
    have hlog_ge_one : 1 ≤ Real.log (1 / x) := by
      have h1 : x ≤ Real.exp (-1) := hx_le
      have h2 : 1 / x ≥ Real.exp 1 := by
        have h3 : 1 / x ≥ 1 / Real.exp (-1) := one_div_le_one_div_of_le hx h1
        have h4 : 1 / Real.exp (-1) = Real.exp 1 := by simp [Real.exp_neg]
        rw [h4] at h3; exact h3
      have h5 : Real.log (1 / x) ≥ Real.log (Real.exp 1) := Real.log_le_log (by positivity) h2
      have h6 : Real.log (Real.exp 1) = 1 := by simp
      linarith
    have h7 : point_coeff x = C0_point := by
      dsimp only [point_coeff, C0_point] <;> rfl
    rw [h7]
    have h8 : C0_point ≤ C0_point * Real.log (1 / x) := by
      have h9 : C0_point * 1 ≤ C0_point * Real.log (1 / x) := mul_le_mul_of_nonneg_left hlog_ge_one hC0_point_nonneg
      simpa using h9
    have h10 : C0_point * (Real.log (1 / x)) ^ A_point = C0_point * Real.log (1 / x) := by
      dsimp only [A_point]
      simp
    rw [h10]
    exact h8

  rcases point_to_root_with_band point_coeff K_band
      ε_input rho_Delta ε_band ε_Root
      hε_input_pos.le hrho_Delta_nonneg hε_band_pos hε_Root_pos h_point_sum
      C0_point A_point hC0_point_nonneg hA_point_pos h_point_coeff_bound
      C0_band A_band hC0_band_nonneg hA_band_pos ⟨δ₂, hδ₂_pos, h_K_band_bound⟩
    with ⟨δ₀_point_d, hδ₀_point_d_pos, h_point_lemma_d⟩

  let δ₀_point_source : ℝ := 4 * Δ * δ₀_point_d
  have hδ₀_point_source_pos : 0 < δ₀_point_source := by positivity

  -- Final transfer threshold (at source scale)
  let δ₀_final_transfer : ℝ := C_fixed ^ (1 / ε_gap)
  have hδ₀_final_transfer_pos : 0 < δ₀_final_transfer := by
    dsimp only [δ₀_final_transfer] <;> positivity

  -- m0_root threshold: ensures δ/4 ≤ Δ^m0_root, so chosen m ≥ m0_root
  let δ₀_m0_root : ℝ := 4 * Δ ^ m0_root
  have hδ₀_m0_root_pos : 0 < δ₀_m0_root := by positivity

  -- Inner threshold: min of all source-scale thresholds except m0_root
  let δ₀_inner : ℝ :=
    min δ₀_uniform_source
      (min δ₀_fibre_source
        (min δ₀_square_band_source
          (min δ₀_uniformization_source
            (min δ₀_ambient_source
              (min δ₀_log_source
                (min δ₀_log_combining_source
                  (min δ₀_point_source
                    (min δ₀_final_transfer δ₀_log_lower_source))))))))

  -- Outer threshold: min of inner threshold and m0_root threshold
  let δ₀_outer : ℝ := min δ₀_inner δ₀_m0_root
  have hδ₀_outer_pos : 0 < δ₀_outer := by
    dsimp only [δ₀_outer]
    positivity

  refine' ⟨ε_input, δ₀_outer, hε_input_pos, hε_input_lt_Root, hδ₀_outer_pos, _⟩

  intro δ hδ_pos hδ_lt_one hδ_le_Δ P hP_bdd hP_sset T Tp hTp_sub hTp_sset hTp_near hδ_small

  -- Derive each threshold bound from δ ≤ δ₀_outer
  -- Derive source-scale bounds from δ ≤ δ₀_outer
  -- Helper for peeling min layers
  have peel_right {a b c : ℝ} (h : a ≤ min b c) : a ≤ c := le_trans h (min_le_right _ _)
  have peel_left {a b c : ℝ} (h : a ≤ min b c) : a ≤ b := le_trans h (min_le_left _ _)

  have hδ_le_inner : δ ≤ δ₀_inner := peel_left hδ_small
  have hδ_le_m0_root : δ ≤ δ₀_m0_root := peel_right hδ_small

  have hδ_le_uniform_source : δ ≤ δ₀_uniform_source := peel_left hδ_le_inner
  have h1 : δ ≤ _ := peel_right hδ_le_inner
  have hδ_le_fibre_source : δ ≤ δ₀_fibre_source := peel_left h1
  have h2 : δ ≤ _ := peel_right h1
  have hδ_le_square_band_source : δ ≤ δ₀_square_band_source := peel_left h2
  have h3 : δ ≤ _ := peel_right h2
  have hδ_le_uniformization_source : δ ≤ δ₀_uniformization_source := peel_left h3
  have h4 : δ ≤ _ := peel_right h3
  have hδ_le_ambient_source : δ ≤ δ₀_ambient_source := peel_left h4
  have h5 : δ ≤ _ := peel_right h4
  have hδ_le_log_source : δ ≤ δ₀_log_source := peel_left h5
  have h6 : δ ≤ _ := peel_right h5
  have hδ_le_log_combining_source : δ ≤ δ₀_log_combining_source := peel_left h6
  have h7 : δ ≤ _ := peel_right h6
  have hδ_le_point_source : δ ≤ δ₀_point_source := peel_left h7
  have h8 : δ ≤ _ := peel_right h7
  have hδ_le_final_transfer : δ ≤ δ₀_final_transfer := peel_left h8
  have hδ_le_log_lower_source : δ ≤ δ₀_log_lower_source := peel_right h8

  -- ==========================================================================
  -- Step 1: Normalize δ → δ/4
  -- ==========================================================================
  let δ_norm : ℝ := δ / 4
  have hδ_norm_pos : 0 < δ_norm := by positivity
  have hδ_norm_lt_one : δ_norm < 1 := by
    dsimp only [δ_norm]
    have h : δ / 4 < 1 := by linarith
    exact h

  let P_norm : Set EuclideanPlane := Normalization.φ '' P
  let T_norm : Set AffineLine := Normalization.φ_line '' T
  let Tp_norm (p : EuclideanPlane) (hp : p ∈ P_norm) : Set AffineLine :=
    have h_exists : ∃ (p_orig : EuclideanPlane), p_orig ∈ P ∧ Normalization.φ p_orig = p := by
      simpa [P_norm, Set.mem_image] using hp
    let p_orig : EuclideanPlane := Classical.choose h_exists
    let hp_orig : p_orig ∈ P := (Classical.choose_spec h_exists).1
    Normalization.φ_line '' (Tp p_orig hp_orig)

  -- Source constant uses ε_input (not ε_Root)
  let C_P_norm : ℝ := Real.rpow δ (-ε_input) * (4 : ℝ) ^ t
  let C_T_norm : ℝ := Real.rpow δ (-ε_input) * (4 : ℝ) ^ s * (MainAppendix.affineLine_packing_constant : ℝ) ^ 3

  have hP_norm_sset : IsDeltaSSet δ_norm t C_P_norm P_norm :=
    Normalization.normalize_sset hP_sset
  have hTp_norm_sset : ∀ p hp, IsDeltaSSet δ_norm s C_T_norm (Tp_norm p hp) := by
    intro p hp
    have h_exists : ∃ (p_orig : EuclideanPlane), p_orig ∈ P ∧ Normalization.φ p_orig = p := by
      simpa [P_norm, Set.mem_image] using hp
    let p_orig : EuclideanPlane := Classical.choose h_exists
    let hp_orig : p_orig ∈ P := (Classical.choose_spec h_exists).1
    have h_eq : Tp_norm p hp = Normalization.φ_line '' (Tp p_orig hp_orig) := by rfl
    rw [h_eq]
    have h_orig : IsDeltaSSet δ s (Real.rpow δ (-ε_input)) (Tp p_orig hp_orig) := hTp_sset p_orig hp_orig
    have hC_pos : 0 < Real.rpow δ (-ε_input) := h_orig.2.2.1
    exact LineNormalizationSSet.line_normalization_sset_transfer
      hδ_pos (show 0 ≤ s from by linarith) hC_pos h_orig

  -- Interior chart: φ maps closedBall 0 1 into [1/4, 3/4]²
  have hP_norm_interior : P_norm ⊆
      {p : EuclideanPlane | p 0 ∈ Set.Icc (1 / 4) (3 / 4) ∧ p 1 ∈ Set.Icc (1 / 4) (3 / 4)} := by
    intro y hy
    rcases hy with ⟨p, hp, rfl⟩
    have h1 : ‖p‖ ≤ 1 := by
      have h11 : p ∈ Metric.closedBall (0 : EuclideanPlane) 1 := hP_bdd hp
      simpa [Metric.mem_closedBall] using h11
    have h2 : ∀ (i : Fin 2), |p i| ≤ ‖p‖ := Normalization.coord_bound_norm p
    have h3 : ∀ (i : Fin 2), -1 ≤ p i ∧ p i ≤ 1 := by
      intro i
      have h4 : |p i| ≤ 1 := by linarith [h2 i, h1]
      exact abs_le.mp h4
    have h5 : ∀ (i : Fin 2), Normalization.φ p i = p i / 4 + 1 / 2 := by
      intro i
      simp [Normalization.φ, Normalization.c, Normalization.halfVec_apply] <;> ring
    constructor
    · rw [h5 0]
      have h6 := h3 0
      constructor <;> linarith
    · rw [h5 1]
      have h6 := h3 1
      constructor <;> linarith

  -- ==========================================================================
  -- Step 2: Orientation partition (production orientation_partition_helper)
  -- ==========================================================================

  -- Positivity of normalized constants
  have hC_P_norm_pos : 0 < C_P_norm := by
    dsimp only [C_P_norm]
    have h1 : 0 < Real.rpow δ (-ε_input) := Real.rpow_pos_of_pos hδ_pos _
    have h2 : 0 < (4 : ℝ) ^ t := by positivity
    positivity
  have hC_T_norm_pos : 0 < C_T_norm := by
    dsimp only [C_T_norm]
    have h1 : 0 < Real.rpow δ (-ε_input) := Real.rpow_pos_of_pos hδ_pos _
    have h2 : 0 < (4 : ℝ) ^ s := by positivity
    have h3 : 0 < (affineLine_packing_constant : ℝ) := by
      exact_mod_cast DirecretisedFurstenbergEstimate.Snapping.affineLine_packing_constant_pos'
    positivity

  -- Normalized fibres subset of normalized tube family
  have hTp_norm_sub : ∀ p hp, Tp_norm p hp ⊆ T_norm := by
    intro p hp
    have h_exists : ∃ (p_orig : EuclideanPlane), p_orig ∈ P ∧ Normalization.φ p_orig = p := by
      simpa [P_norm, Set.mem_image] using hp
    let p_orig : EuclideanPlane := Classical.choose h_exists
    let hp_orig : p_orig ∈ P := (Classical.choose_spec h_exists).1
    have h_eq : Tp_norm p hp = Normalization.φ_line '' (Tp p_orig hp_orig) := by rfl
    rw [h_eq]
    exact Set.image_mono (hTp_sub p_orig hp_orig)

  -- Normalized near property transfers under φ
  have hTp_norm_near : ∀ p hp, ∀ ℓ ∈ Tp_norm p hp, p ∈ Metric.cthickening δ_norm ℓ.1 := by
    intro p hp ℓ hℓ
    have h_exists : ∃ (p_orig : EuclideanPlane), p_orig ∈ P ∧ Normalization.φ p_orig = p := by
      simpa [P_norm, Set.mem_image] using hp
    let p_orig : EuclideanPlane := Classical.choose h_exists
    let hp_orig : p_orig ∈ P := (Classical.choose_spec h_exists).1
    have hφ_eq : Normalization.φ p_orig = p := (Classical.choose_spec h_exists).2
    have h_eq : Tp_norm p hp = Normalization.φ_line '' (Tp p_orig hp_orig) := by rfl
    rw [h_eq] at hℓ
    rcases hℓ with ⟨ℓ_orig, hℓ_orig, rfl⟩
    have h_near_orig : p_orig ∈ Metric.cthickening δ ℓ_orig.1 := hTp_near p_orig hp_orig ℓ_orig hℓ_orig
    have h : Normalization.φ p_orig ∈ Metric.cthickening (δ / 4) ((Normalization.φ_line ℓ_orig).1) :=
      normalized_near_transfer hδ_pos h_near_orig
    rw [hφ_eq] at h
    simpa [δ_norm] using h

  -- P_norm ball bound: φ maps unit ball into unit ball
  have hP_norm_bdd : P_norm ⊆ Metric.closedBall 0 1 :=
    Normalization.φ_image_unit_ball hP_bdd

  -- ρ_slope = 1 works since δ_norm = δ/4 ≤ Δ/4 < 1/4 < 1/2
  let ρ_slope : ℝ := 1
  have hρ_slope_nonneg : 0 ≤ ρ_slope := by norm_num
  have hδ_slope : δ_norm ^ ρ_slope ≤ 1 / 2 := by
    dsimp only [ρ_slope, δ_norm]
    have h : δ / 4 ≤ 1 / 2 := by linarith [hΔ_lt_one]
    simpa [pow_one] using h

  let Kpack : ℝ := (affineLine_packing_constant : ℝ)
  let C_fibre_orien : ℝ := (max 1 (Kpack * C_T_norm)) * 2 * Kpack
  have hC_fibre_orien_pos : 0 < C_fibre_orien := by
    dsimp only [C_fibre_orien]
    have hKpack_pos : 0 < Kpack := by
      have h : 0 < affineLine_packing_constant := affineLine_packing_constant_pos
      exact Nat.cast_pos.mpr h
    positivity

  -- Production orientation_partition_helper: extracts finite fibres, partitions slopes
  rcases orientation_partition_helper
      δ_norm s t C_T_norm C_P_norm
      hs hC_T_norm_pos hC_P_norm_pos
      hδ_norm_pos (by linarith)
      P_norm hP_norm_bdd hP_norm_sset hP_norm_interior
      T_norm Tp_norm hTp_norm_sub hTp_norm_sset hTp_norm_near
      ρ_slope hρ_slope_nonneg hδ_slope
    with ⟨swapped, P_orien, T_orien, Fp_orien, c_slope,
      hc_slope_pos, hc_slope_eq, hc_slope_ge, hNcover_P_orien,
      hP_orien_sset_helper, hP_orien_interior, h_swapped_false, h_swapped_true,
      hNcover_T_orien_eq, hFp_orien_sub, hFp_orien_sset, hFp_orien_v0,
      hFp_orien_slope, hFp_orien_near⟩

  let interior_set : Set EuclideanPlane :=
    {p | p 0 ∈ Set.Icc (1 / 4) (3 / 4) ∧ p 1 ∈ Set.Icc (1 / 4) (3 / 4)}

  let C_P_orien : ℝ := C_P_norm / c_slope  -- = 2 * C_P_norm
  have hC_P_orien_pos : 0 < C_P_orien := by
    dsimp only [C_P_orien]
    have h2 : 0 < c_slope := by
      rw [hc_slope_eq] <;> norm_num
    exact div_pos hC_P_norm_pos h2

  -- Helper gives IsDeltaSSet δ_norm t (2 * C_P_norm) P_orien; convert to C_P_orien form
  have hP_orien_sset : IsDeltaSSet δ_norm t C_P_orien P_orien := by
    have h_eq : C_P_orien = 2 * C_P_norm := by
      dsimp only [C_P_orien]
      rw [hc_slope_eq] <;> ring
    rw [h_eq]
    exact hP_orien_sset_helper

  -- ==========================================================================
  -- Step 3: Nearby exact scale transfer δ_d = Δ^m
  -- ==========================================================================
  -- Strict fact: δ/4 < Δ follows from δ > 0 and δ ≤ Δ
  have hδ_norm_lt_Δ : δ_norm < Δ := by
    dsimp only [δ_norm]
    linarith

  have h_exists : ∃ m0 : ℕ, Δ ^ m0 < δ_norm :=
    exists_pow_lt_of_lt_one hδ_norm_pos hΔ_lt_one
  let m0 := Nat.find h_exists
  have hP_m0 : Δ ^ m0 < δ_norm := Nat.find_spec h_exists
  have h_m0_ge2 : 2 ≤ m0 := by
    by_contra h
    have h1 : m0 = 0 ∨ m0 = 1 := by omega
    rcases h1 with (h1 | h1)
    · rw [h1] at hP_m0; norm_num at hP_m0 <;> linarith
    · have h2 : Δ ^ 1 < δ_norm := by rw [h1] at hP_m0; exact hP_m0
      have h3 : Δ < δ_norm := by simpa using h2
      linarith [hδ_norm_lt_Δ]
  let m : ℕ := m0 - 1
  have hm_pos : 0 < m := by omega
  have h_m_lt_m0 : m < m0 := by omega
  have h_notP_m : ¬(Δ ^ m < δ_norm) := Nat.find_min h_exists h_m_lt_m0
  have hδ_norm_le_d : δ_norm ≤ Δ ^ m := by linarith

  -- Prove m ≥ m0_root: δ_norm ≤ Δ^m0_root implies Nat.find index > m0_root
  have hδ_norm_le_m0_root : δ_norm ≤ Δ ^ m0_root := by
    have h1 : δ ≤ 4 * Δ ^ m0_root := hδ_le_m0_root
    have h2 : δ / 4 ≤ Δ ^ m0_root := by linarith
    exact h2
  have h_m0_root_lt_m0 : m0_root < m0 := by
    by_contra h
    have h' : m0 ≤ m0_root := by omega
    have h4 : Δ ^ m0 ≥ Δ ^ m0_root := by
      exact pow_le_pow_of_le_one hΔ_pos.le hΔ_lt_one.le h'
    have h5 : Δ ^ m0 ≥ δ_norm := by linarith
    linarith [hP_m0]
  have hm_ge_m0_root : m ≥ m0_root := by omega
  have hΔm_lt_delta_div : Δ ^ m < δ_norm / Δ := by
    have h : Δ ^ m0 < δ_norm := hP_m0
    have h2 : m0 = m + 1 := by omega
    rw [h2] at h
    have h3 : Δ ^ (m + 1) = Δ ^ m * Δ := by simp [pow_succ] <;> ring
    rw [h3] at h
    have h4 : 0 < Δ := hΔ_pos
    calc Δ ^ m
      = (Δ ^ m * Δ) / Δ := by field_simp [h4.ne'] <;> ring
    _ < δ_norm / Δ := by gcongr
  have hδ_d_le_ratio : Δ ^ m ≤ (1 / Δ) * δ_norm := by
    have h : Δ ^ m < δ_norm / Δ := hΔm_lt_delta_div
    have h2 : δ_norm / Δ = (1 / Δ) * δ_norm := by ring
    rw [h2] at h
    exact h.le
  have hδ_d_le_delta : Δ ^ m ≤ Δ := by
    have h1 : m ≠ 0 := by omega
    have h2 : 0 ≤ Δ := by linarith
    exact pow_le_of_le_one h2 hΔ_lt_one.le h1

  let δ_d : ℝ := Δ ^ m
  have hδ_d_pos : 0 < δ_d := by positivity
  have hδ_d_lt_one : δ_d < 1 := by
    have h1 : m ≠ 0 := by omega
    have h2 : 0 ≤ Δ := by linarith
    have h3 : Δ ^ m ≤ Δ := pow_le_of_le_one h2 hΔ_lt_one.le h1
    have h4 : Δ < 1 := hΔ_lt_one
    exact h3.trans_lt h4
  let k : ℕ := q * m
  have hk_pos : 0 < k := mul_pos hq_pos hm_pos
  have hscale_eq : DiscretisedFurstenbergEstimate.dyadicDelta k = δ_d := by
    have h1 : DiscretisedFurstenbergEstimate.dyadicDelta k = 1 / (2 : ℝ)^k := by rfl
    rw [h1]
    have hk : k = q * m := by rfl
    have h2 : δ_d = 1 / (2 : ℝ)^k := by
      have h3 : δ_d = Δ ^ m := by rfl
      rw [h3, hΔ_eq, hk]
      have h4 : ((1 / 2 : ℝ) ^ q) ^ m = (1 / 2 : ℝ) ^ (q * m) := by
        rw [← pow_mul] <;> ring
      rw [h4]
      have h5 : (1 / 2 : ℝ) ^ (q * m) = 1 / (2 : ℝ) ^ (q * m) := by
        rw [div_pow] <;> norm_num
      rw [h5]
    rw [h2]

  have hδ4_le_d : δ / 4 ≤ δ_d := by simpa [δ_norm, δ_d] using hδ_norm_le_d
  have hδ_d_le_ratio4 : δ_d ≤ (1 / Δ) * (δ / 4) := by simpa [δ_norm] using hδ_d_le_ratio

  -- Log lower bound for absorption: log(1/δ_d) ≥ 72900 * Δ^(-4)
  have hδ_d_le_log_lower : δ_d ≤ δ₀_log_lower_d := by
    have h1 : δ_d ≤ (1 / Δ) * (δ / 4) := hδ_d_le_ratio4
    have h2 : δ ≤ δ₀_log_lower_source := hδ_le_log_lower_source
    have h3 : (1 / Δ) * (δ / 4) ≤ (1 / Δ) * (δ₀_log_lower_source / 4) := by gcongr
    have h4 : (1 / Δ) * (δ₀_log_lower_source / 4) = δ₀_log_lower_d := by
      dsimp only [δ₀_log_lower_source]
      <;> field_simp [hΔ_pos.ne'] <;> ring
    calc δ_d ≤ (1 / Δ) * (δ / 4) := h1
         _ ≤ (1 / Δ) * (δ₀_log_lower_source / 4) := h3
         _ = δ₀_log_lower_d := h4
  have h_log_lower : Real.log (1 / δ_d) ≥ 72900 * Δ^(-4 : ℝ) :=
    h_log_lower_bound δ_d hδ_d_pos hδ_d_le_log_lower

  -- Transfer point S-set: constant C_P_orien * 9^q
  let C_P_d : ℝ := C_P_orien * (9 : ℝ)^q
  have hC_P_d_pos : 0 < C_P_d := by
    dsimp only [C_P_d]
    positivity

  have hP_orien_sset' : IsDeltaSSet δ_norm t C_P_orien P_orien := hP_orien_sset

  have hP_orien_sset_d : IsDeltaSSet δ_d t C_P_d P_orien :=
    @sset_transfer_norm_to_dd_plane Δ hΔ_pos δ δ_d hδ_pos hδ_d_pos hδ4_le_d hδ_d_le_ratio4 q hΔ_eq
      t C_P_orien (by linarith) hC_P_orien_pos P_orien hP_orien_sset'

  -- Transfer fibre S-set: constant C_fibre_orien * Kpack^q
  let C_T_d : ℝ := C_fibre_orien * (affineLine_packing_constant : ℝ)^q
  have hC_T_d_pos : 0 < C_T_d := by
    dsimp only [C_T_d]
    have hKpack_pos : 0 < (affineLine_packing_constant : ℝ) := by
      exact_mod_cast DirecretisedFurstenbergEstimate.Snapping.affineLine_packing_constant_pos'
    positivity

  have hFp_orien_sset_d : ∀ p hp, IsDeltaSSet δ_d s C_T_d (Fp_orien p hp : Set AffineLine) :=
    fun p hp => @sset_transfer_norm_to_dd_affineLine Δ hΔ_pos δ δ_d hδ_pos hδ_d_pos hδ4_le_d hδ_d_le_ratio4 q hΔ_eq
      s C_fibre_orien (by linarith) hC_fibre_orien_pos (Fp_orien p hp : Set AffineLine) (hFp_orien_sset p hp)

  have hk_le : DiscretisedFurstenbergEstimate.dyadicDelta k ≤ δ₀_uniform := by
    -- δ_d ≤ (1/Δ) * (δ/4) = δ/(4Δ)
    have h1 : δ_d ≤ δ / (4 * Δ) := by
      have h2 : (1 / Δ) * (δ / 4) = δ / (4 * Δ) := by ring
      rw [h2] at hδ_d_le_ratio4
      exact hδ_d_le_ratio4
    -- δ ≤ 4Δ·δ₀_uniform from hδ_le_uniform_source
    have h3 : δ ≤ 4 * Δ * δ₀_uniform := hδ_le_uniform_source
    have h5 : 0 < 4 * Δ := by positivity
    have h4 : δ / (4 * Δ) ≤ δ₀_uniform := by
      have h41 : δ / (4 * Δ) ≤ (4 * Δ * δ₀_uniform) / (4 * Δ) :=
        div_le_div_of_nonneg_right h3 h5.le
      have h42 : (4 * Δ * δ₀_uniform) / (4 * Δ) = δ₀_uniform := by
        rw [div_eq_iff h5.ne'] <;> ring
      rw [h42] at h41
      exact h41
    have h6 : δ_d ≤ δ₀_uniform := le_trans h1 h4
    rw [hscale_eq]
    exact h6

  -- General pullback lemma: δ ≤ 4*Δ*θ_d and δ_d ≤ δ/(4*Δ) implies δ_d ≤ θ_d
  have h_pullback : ∀ (θ_d : ℝ), δ ≤ 4 * Δ * θ_d → δ_d ≤ θ_d := by
    intro θ_d hδ_le
    have h1 : δ_d ≤ δ / (4 * Δ) := by
      have h2 : (1 / Δ) * (δ / 4) = δ / (4 * Δ) := by ring
      rw [h2] at hδ_d_le_ratio4
      exact hδ_d_le_ratio4
    have h3 : 0 < 4 * Δ := by positivity
    have h4 : δ / (4 * Δ) ≤ θ_d := by
      have h5 : δ ≤ 4 * Δ * θ_d := hδ_le
      have h6 : δ / (4 * Δ) ≤ (4 * Δ * θ_d) / (4 * Δ) :=
        div_le_div_of_nonneg_right h5 h3.le
      have h7 : (4 * Δ * θ_d) / (4 * Δ) = θ_d := by
        rw [div_eq_iff h3.ne'] <;> ring
      rw [h7] at h6
      exact h6
    exact le_trans h1 h4

  -- Derive δ_d-scale bounds from source pullbacks
  have hδ_d_le_fibre : δ_d ≤ δ₀_fibre_d := h_pullback δ₀_fibre_d hδ_le_fibre_source
  have hδ_d_le_square_band : δ_d ≤ δ₀_square_band_d := h_pullback δ₀_square_band_d hδ_le_square_band_source
  have hδ_d_le_uniformization : δ_d ≤ δ₀_uniformization_d := h_pullback δ₀_uniformization_d hδ_le_uniformization_source
  have hδ_d_le_ambient : δ_d ≤ δ₀_ambient_d := h_pullback δ₀_ambient_d hδ_le_ambient_source
  have hδ_d_le_log : δ_d ≤ δ₀_log_d := h_pullback δ₀_log_d hδ_le_log_source
  have hδ_d_le_log_combining : δ_d ≤ δ₀_log_combining_d :=
    h_pullback δ₀_log_combining_d hδ_le_log_combining_source
  have hδ_d_le_point : δ_d ≤ δ₀_point_d := h_pullback δ₀_point_d hδ_le_point_source
  have hδ_d_le_log_lower : δ_d ≤ δ₀_log_lower_d := h_pullback δ₀_log_lower_d hδ_le_log_lower_source

  -- ==========================================================================
  -- LEDGER 2: Fibre losses → λ
  --   Fibre factors (line normalization, snapping, factor 18) are absorbed
  --   into λ - ε_input. Output fibre S-set constant is exactly δ_d^(-λ).
  --
  --   Chain:
  --     18*C_raw ≤ C_fibre_fixed * δ_d^(-ε_input)   [factorization + antitonicity]
  --     C_fibre_fixed ≤ δ_d^(-(λ - ε_input))         [threshold, below]
  --     Therefore 18*C_raw ≤ δ_d^(-λ)                [multiply, exponents add]
  -- ==========================================================================
  have h_fibre_to_lambda : C_fibre_fixed ≤ δ_d ^ (-(lam - ε_input)) :=
    (Classical.choose_spec
      (fibre_to_lambda_threshold C_fibre_fixed hC_fibre_fixed_nonneg lam ε_input
        hε_input_pos hε_input_lt_lam)).2 δ_d hδ_d_pos hδ_d_le_fibre
  -- fibre ledger: threshold δ₀_fibre_d ensures fibre losses fit in lam - ε_input

  -- ==========================================================================
  -- Step 4: Fibre uniformization → squares', tubeFam (DyadicTube), T₀, M
  -- ==========================================================================
  let ρ_M : ℝ := ε_G * η / 800
  let ρ_T : ℝ := ε_G * η / 800
  -- ρ_mass not needed: multiscaleToCombining_thickened has no mass bound requirement

  -- P_orien ⊆ closedBall 0 1: follows from P_norm ⊆ closedBall 0 1 and
  -- P_orien ⊆ P_norm (if not swapped) or P_orien ⊆ swapCoords '' P_norm (if swapped).
  -- swapCoords is an isometry, so it preserves the unit ball.
  have hP_orien_bdd : P_orien ⊆ Metric.closedBall 0 1 := by
    by_cases h_sw : swapped
    · -- swapped = true
      have h : P_orien ⊆ swapCoords '' P_norm := (h_swapped_true h_sw).1
      intro p hp
      rcases h hp with ⟨q, hq, rfl⟩
      have hq_ball : q ∈ Metric.closedBall 0 1 := hP_norm_bdd hq
      have h_iso : ‖swapCoords q‖ = ‖q‖ := by
        have h1 : dist (swapCoords q) (swapCoords 0) = dist q 0 := swapCoords_isometry.dist_eq q 0
        have h2 : swapCoords 0 = 0 := by
          ext i <;> simp [swapCoords] <;> norm_num
        rw [h2] at h1
        have h3 : dist (swapCoords q) 0 = ‖swapCoords q‖ := by
          rw [dist_zero_right]
        have h4 : dist q 0 = ‖q‖ := by rw [dist_zero_right]
        rw [h3, h4] at h1
        exact h1
      simpa [Metric.mem_closedBall, h_iso] using hq_ball
    · -- swapped = false
      have h_sw' : swapped = false :=
        Bool.eq_false_iff.mpr h_sw
      have h : P_orien ⊆ P_norm := (h_swapped_false h_sw').1
      intro x hx
      exact hP_norm_bdd (h hx)
  have hP_orien_nonempty : P_orien.Nonempty := hP_orien_sset_d.1

  -- Upgrade near property from δ_norm to δ_d (δ_norm ≤ δ_d)
  have hFp_orien_near_d : ∀ p hp, ∀ ℓ ∈ Fp_orien p hp, p ∈ Metric.cthickening δ_d ℓ.1 := by
    intro p hp ℓ hℓ
    let S : Set EuclideanPlane := ℓ.1
    have h1 : p ∈ Metric.cthickening δ_norm S := hFp_orien_near p hp ℓ hℓ
    have h2 : Metric.cthickening δ_norm S ⊆ Metric.cthickening δ_d S :=
      Metric.cthickening_mono hδ_norm_le_d S
    exact h2 h1

  -- Kpack already defined at line 792; do NOT redefine (shadowing breaks C_fibre_orien expansion)
  -- C_in = C_T_d directly (no second extraction, so no max 1/Kpack factor)
  let C_in : ℝ := C_T_d
  have hC_in_pos : 0 < C_in := hC_T_d_pos

  -- Raw fibre producer: cover by squares + snap (Fp_orien comes directly from orientation)
  rcases raw_fibre_producer
      (hδ_pos := hδ_d_pos) (hδ_le_one := by linarith [hδ_d_lt_one])
      (hδn_pos := DiscretisedFurstenbergEstimate.dyadicDelta_pos k) (hδn_leδ := by rw [hscale_eq])
      (hδ_le2δn := by rw [hscale_eq] <;> linarith [DiscretisedFurstenbergEstimate.dyadicDelta_pos k])
      (hs_nonneg := by linarith [hs])
      (P := P_orien) (hP_bdd := hP_orien_bdd) (hP_nonempty := hP_orien_nonempty)
      (Fp := Fp_orien) (C_in := C_in) (hC_in_pos := hC_in_pos)
      (hF_sset := hFp_orien_sset_d) (hF_v0 := hFp_orien_v0) (hF_slope := hFp_orien_slope)
      (hF_near := hFp_orien_near_d) (T_oriented := T_orien) (hF_sub := hFp_orien_sub)
    with ⟨squares, rawTubes, C_raw, K_raw,
      hsquares_nonempty, hcover, hC_raw_pos, hC_raw_eq, hK_eq,
      hraw_sset, hraw_card, hraw_intersect, hraw_prov, hraw_slope, hraw_intercept, hraw_strip, hraw_occupancy⟩

  -- Absorption bound: 18*C_raw ≤ δ_d^(-lam)
  -- Chain: 18*C_raw = C_fibre_fixed * δ^(-ε_input)
  --       ≤ C_fibre_fixed * (4Δ*δ_d)^(-ε_input)   [δ ≥ 4Δ*δ_d, exponent negative]
  --       = C_fibre_fixed * δ_d^(-ε_input)
  --       ≤ δ_d^(-(lam-ε_input)) * δ_d^(-ε_input)  [h_fibre_to_lambda]
  --       = δ_d^(-lam)

  -- Exact fibre constant identity: C_fibre_orien = 2 * 4^s * Kpack^5 * δ^(-ε_input)
  have hKpack_ge_one : 1 ≤ Kpack := by
    dsimp only [Kpack]
    have h : 1 ≤ affineLine_packing_constant := Nat.succ_le_iff.mpr affineLine_packing_constant_pos
    exact_mod_cast h
  have hCT_norm_large : 1 < Kpack * C_T_norm := by
    dsimp only [C_T_norm]
    have hδ_lt_one : δ < 1 := by linarith [hδ_le_Δ, hΔ_lt_one]
    have h_neg : -ε_input < 0 := by linarith [hε_input_pos]
    have h1 : 1 < δ ^ (-ε_input) := by
      have h_pos : 0 < δ := hδ_pos
      have h_small : δ ^ ε_input < 1 := Real.rpow_lt_one h_pos.le hδ_lt_one hε_input_pos
      have h_inv : δ ^ (-ε_input) = (δ ^ ε_input)⁻¹ := by
        rw [Real.rpow_neg h_pos.le]
      rw [h_inv]
      have h2 : 0 < δ ^ ε_input := by positivity
      have h_goal : 1 < (δ ^ ε_input)⁻¹ := by
        have h_div : 1 < 1 / δ ^ ε_input := one_lt_one_div h2 h_small
        have h_eq : (1 / δ ^ ε_input) = (δ ^ ε_input)⁻¹ := by field_simp
        rw [h_eq] at h_div
        exact h_div
      exact h_goal
    have h2 : 1 < (4 : ℝ)^s := by
      have h4pos : (1 : ℝ) < (4 : ℝ) := by norm_num
      exact Real.one_lt_rpow h4pos hs
    have h3 : 1 ≤ Kpack := hKpack_ge_one
    have h4 : 1 ≤ Kpack^4 := by
      calc 1 ≤ (1 : ℝ)^4 := by norm_num
           _ ≤ Kpack^4 := by gcongr
    have h_pos1 : 0 < δ ^ (-ε_input) := by positivity
    have h_main : 1 < δ ^ (-ε_input) * (4 : ℝ)^s * Kpack^4 := by
      calc 1
        < δ ^ (-ε_input) := h1
      _ ≤ δ ^ (-ε_input) * (4 : ℝ)^s := le_mul_of_one_le_right h_pos1.le h2.le
      _ ≤ δ ^ (-ε_input) * (4 : ℝ)^s * Kpack^4 := le_mul_of_one_le_right (by positivity) h4
    have h_eq : (Kpack : ℝ) * (δ ^ (-ε_input) * (4 : ℝ)^s * (affineLine_packing_constant : ℝ)^3) =
        δ ^ (-ε_input) * (4 : ℝ)^s * (Kpack : ℝ)^4 := by
      have hK : (Kpack : ℝ) = (affineLine_packing_constant : ℝ) := by rfl
      rw [hK] <;> ring
    have h_final : 1 < (Kpack : ℝ) * (δ ^ (-ε_input) * (4 : ℝ)^s * (affineLine_packing_constant : ℝ)^3) := by
      rw [h_eq]
      exact h_main
    exact_mod_cast h_final
  have h_max_eq : max 1 (Kpack * C_T_norm) = Kpack * C_T_norm := by
    rw [max_eq_right] <;> exact hCT_norm_large.le
  have hC_fibre_orien_eq : C_fibre_orien = 2 * (4 : ℝ)^s * Kpack^5 * δ^(-ε_input) := by
    have h1 : C_fibre_orien = (max 1 (Kpack * C_T_norm)) * 2 * Kpack := by rfl
    rw [h1, h_max_eq]
    have hCT : C_T_norm = δ^(-ε_input) * (4 : ℝ)^s * (MainAppendix.affineLine_packing_constant : ℝ)^3 := by rfl
    rw [hCT]
    have hK : Kpack = (affineLine_packing_constant : ℝ) := by rfl
    rw [hK]
    have h_main_eq : (MainAppendix.affineLine_packing_constant : ℝ) = (affineLine_packing_constant : ℝ) := by rfl
    rw [h_main_eq]
    <;> ring

  have h_absorb : 18 * C_raw ≤ (DiscretisedFurstenbergEstimate.dyadicDelta k)^(-lam) := by
    rw [hscale_eq]
    have hKpack_def : Kpack = (affineLine_packing_constant : ℝ) := by rfl
    have h4Δδd_le_δ : 4 * Δ * δ_d ≤ δ := by
      have h1 : δ_d ≤ (1 / Δ) * (δ / 4) := hδ_d_le_ratio4
      have h2 : (1 / Δ) * (δ / 4) = δ / (4 * Δ) := by ring
      rw [h2] at h1
      have h3 : 0 < 4 * Δ := by positivity
      calc 4 * Δ * δ_d ≤ 4 * Δ * (δ / (4 * Δ)) := by gcongr
        _ = δ := by field_simp [h3.ne'] <;> ring
    have h4Δδd_pos : 0 < 4 * Δ * δ_d := by positivity
    have hδ_pos' : 0 < δ := hδ_pos
    -- δ^(-ε_input) ≤ (4Δ*δ_d)^(-ε_input) since 4Δ*δ_d ≤ δ and -ε_input < 0
    have h_exp_nonpos : -ε_input ≤ 0 := by
      have h : 0 < ε_input := hε_input_pos
      exact neg_nonpos.mpr h.le
    have h_rpow_mono : δ ^ (-ε_input) ≤ (4 * Δ * δ_d) ^ (-ε_input) := by
      exact Real.rpow_le_rpow_of_nonpos h4Δδd_pos h4Δδd_le_δ h_exp_nonpos
    -- Factorize 18*C_raw
    have h_Cin_eq : C_in = C_fibre_orien * Kpack ^ q := by
      rfl
    have h18_Craw : 18 * C_raw =
        36 * 3721 * (4 : ℝ)^s * (58 : ℝ)^s * Kpack^(q + 10) * δ^(-ε_input) := by
      rw [hC_raw_eq, h_Cin_eq, hC_fibre_orien_eq]
      simp [hKpack_def, pow_add]
      <;> ring
    rw [h18_Craw]
    have h_main : 36 * 3721 * (4 : ℝ)^s * (58 : ℝ)^s * Kpack^(q + 10) * δ^(-ε_input) ≤
        C_fibre_fixed * δ_d^(-ε_input) := by
      have h_rpow_mul : (4 * Δ * δ_d)^(-ε_input) = (4 * Δ)^(-ε_input) * δ_d^(-ε_input) := by
        rw [← Real.mul_rpow (by positivity) (by positivity)] <;> ring
      have h_coeff_pos : 0 < 36 * 3721 * (4 : ℝ)^s * (58 : ℝ)^s * Kpack^(q + 10) := by positivity
      have h : 36 * 3721 * (4 : ℝ)^s * (58 : ℝ)^s * Kpack^(q + 10) * δ^(-ε_input) ≤
          36 * 3721 * (4 : ℝ)^s * (58 : ℝ)^s * Kpack^(q + 10) * (4 * Δ * δ_d)^(-ε_input) :=
        mul_le_mul_of_nonneg_left h_rpow_mono h_coeff_pos.le
      have h_eq : 36 * 3721 * (4 : ℝ)^s * (58 : ℝ)^s * Kpack^(q + 10) * (4 * Δ * δ_d)^(-ε_input) =
          C_fibre_fixed * δ_d^(-ε_input) := by
        dsimp only [C_fibre_fixed]
        have h5 : (4 * Δ * δ_d)^(-ε_input) = (4 * Δ)^(-ε_input) * δ_d^(-ε_input) := h_rpow_mul
        have h6 : 36 * 3721 * (4 : ℝ)^s * (58 : ℝ)^s * Kpack^(q + 10) * (4 * Δ * δ_d)^(-ε_input) =
            36 * 3721 * (4 : ℝ)^s * (58 : ℝ)^s * Kpack^(q + 10) * ((4 * Δ)^(-ε_input) * δ_d^(-ε_input)) := by
          rw [h5]
        rw [h6]
        <;> ring
      exact le_trans h h_eq.le
    have h_final : C_fibre_fixed * δ_d^(-ε_input) ≤ δ_d^(-lam) := by
      have h1 : C_fibre_fixed ≤ δ_d ^ (-(lam - ε_input)) := h_fibre_to_lambda
      have h2 : 0 < δ_d^(-ε_input) := by positivity
      have h3 : C_fibre_fixed * δ_d^(-ε_input) ≤ δ_d^(-(lam - ε_input)) * δ_d^(-ε_input) := by
        gcongr
      have h4 : δ_d^(-(lam - ε_input)) * δ_d^(-ε_input) = δ_d^(-lam) := by
        have h5 : δ_d^(-(lam - ε_input)) * δ_d^(-ε_input) = δ_d^((-(lam - ε_input)) + (-ε_input)) := by
          rw [← Real.rpow_add hδ_d_pos] <;> ring
        rw [h5]
        have h6 : (-(lam - ε_input)) + (-ε_input) = -lam := by ring
        rw [h6]
      rw [h4] at h3
      exact h3
    exact le_trans h_main h_final

  -- Fibre uniformization step
  rcases fibre_uniformization_step
      (hδ_pos := hδ_d_pos) (hδn_pos := DiscretisedFurstenbergEstimate.dyadicDelta_pos k)
      (hδn_leδ := by rw [hscale_eq]) (hδ_lt2δn := by rw [hscale_eq] <;> linarith [DiscretisedFurstenbergEstimate.dyadicDelta_pos k])
      squares rawTubes C_raw hC_raw_pos hraw_sset
      K_raw hraw_card hlam_pos h_absorb
      hraw_intersect T_orien
      (3 / 2 : ℝ) (by norm_num) (le_refl (3 / 2 : ℝ))
      hraw_slope hraw_intercept
      (fun q hq U hU => by
        rcases hraw_prov q hq U hU with ⟨ℓ, hℓ, hdist⟩
        have h_eq : dist (toAffineLine U) ℓ = AffineLine.dist ℓ (toAffineLine U) := by
          rw [← dist_comm] <;> rfl
        exact ⟨ℓ, hℓ, h_eq ▸ hdist⟩)
      hraw_strip
      hsquares_nonempty ρ_M (by linarith [hεG_pos, hη_pos])
    with ⟨squares_all, K_band_out, squares', tubeFam, T₀, M, K_ambient,
      hsquares_all_eq, hK_band_eq, hsquares'_sub, hretention, hM_pos', hTube_card,
      hTube_sset, hTube_intersect, hTube_in_T0, hK_ambient_pos, hT0_bound,
      hK_ambient_le, hM_lower, hT0_eq_union, hTube_strip, hTube_subset_raw⟩

  let K_ready : ℕ := K_band_out

  -- Provenance for tubeFam (transfers via subset of rawTubes)
  have hTube_provenance : ∀ q hq (U : DiscretisedFurstenbergEstimate.DyadicTube k), U ∈ tubeFam q hq →
      ∃ (ℓ : AffineLine), ℓ ∈ T_orien ∧ AffineLine.dist ℓ (toAffineLine U) ≤ 7 * δ_d := by
    intro q hq U hU
    rcases hTube_subset_raw q hq with ⟨hqs, hsub⟩
    have h_in_raw : U ∈ rawTubes q hqs := hsub hU
    rcases hraw_prov q hqs U h_in_raw with ⟨ℓ, hℓ, hdist⟩
    have h_eq : dist (toAffineLine U) ℓ = AffineLine.dist ℓ (toAffineLine U) := by
      rw [← dist_comm] <;> rfl
    exact ⟨ℓ, hℓ, h_eq ▸ hdist⟩

  have hTube_sub : ∀ q hq, (tubeFam q hq : Set (DiscretisedFurstenbergEstimate.DyadicTube k)) ⊆
      (T₀ : Set (DiscretisedFurstenbergEstimate.DyadicTube k)) :=
    fun q hq => hTube_in_T0 q hq

  have hT₀_def : T₀ = Finset.biUnion squares'.attach (fun q => tubeFam q.val q.property) := by
    ext U
    simp only [Finset.mem_biUnion, Finset.mem_coe, Subtype.exists]
    have h : (T₀ : Set (DiscretisedFurstenbergEstimate.DyadicTube k)) =
        ⋃ (q : DiscretisedFurstenbergEstimate.DyadicSquare k) (hq : q ∈ squares'),
          (tubeFam q hq : Set (DiscretisedFurstenbergEstimate.DyadicTube k)) := hT0_eq_union
    rw [Set.ext_iff] at h
    simpa using h U

  -- ==========================================================================
  -- Step 5: P_ready = points of P_orien lying in some square of squares'
  -- ==========================================================================
  let P_ready : Set EuclideanPlane :=
    {p ∈ P_orien | ∃ (q : DiscretisedFurstenbergEstimate.DyadicSquare k), q ∈ squares' ∧ p ∈ q.toSet}
  have hP_ready_sub : P_ready ⊆ P_orien := by
    intro x hx
    exact hx.1
  have hP_ready_interior : P_ready ⊆ interior_set := by
    intro p hp
    have h : p ∈ P_orien := hp.1
    exact hP_orien_interior h
  -- P_ready S-set with ENLARGED constant: C_P_d * 9 * (K_ready + 1)
  -- The factor 9*(K_ready+1) is a logarithmic loss from the P_ready construction.
  let C_P_ready : ℝ := C_P_d * 9 * ((K_ready : ℝ) + 1)
  have hC_P_ready_pos : 0 < C_P_ready := by
    dsimp only [C_P_ready]
    have h1 : 0 < C_P_d := hC_P_d_pos
    have h2 : 0 < (9 : ℝ) := by norm_num
    have h3 : 0 < ((K_ready : ℝ) + 1) := lagoon_nat_cast_add_one_pos K_ready
    exact mul_pos (mul_pos h1 h2) h3
  -- Cover P_orien by squares_all (= squares from producer)
  have hP_orien_cover_all : P_orien ⊆ ⋃ q ∈ (squares_all : Set (DiscretisedFurstenbergEstimate.DyadicSquare k)), (q.toSet : Set EuclideanPlane) := by
    have h_eq : squares_all = squares := hsquares_all_eq
    rw [h_eq]
    exact hcover

  -- Occupancy: every retained square contains a P_ready point.
  -- Follows from RawFibreProducer filtering squares to P-intersecting ones,
  -- and squares' ⊆ squares_all = squares.
  have h_ready_occupancy : ∀ q ∈ squares', ((q.toSet : Set EuclideanPlane) ∩ P_ready).Nonempty := by
    intro q hq
    have hq_squares : q ∈ squares := by
      have h1 : q ∈ squares_all := hsquares'_sub hq
      rw [hsquares_all_eq] at h1
      exact h1
    have h_occ : (P_orien ∩ (q.toSet : Set EuclideanPlane)).Nonempty := hraw_occupancy q hq_squares
    rcases h_occ with ⟨p, hp_orien, hp_in_square⟩
    have hp_ready : p ∈ P_ready := by
      simp only [P_ready, Set.mem_setOf_eq]
      exact ⟨hp_orien, q, hq, hp_in_square⟩
    exact ⟨p, hp_in_square, hp_ready⟩
  -- [SORRY-indigo] occupancy witness from RawFibreProducer h_occupancy

  have hK_ready_pos : 0 < K_ready + 1 := by positivity

  -- Convert P_orien S-set to dyadicDelta k scale
  have hP_orien_sset_k : IsDeltaSSet (DiscretisedFurstenbergEstimate.dyadicDelta k) t C_P_d P_orien := by
    rw [hscale_eq]
    exact hP_orien_sset_d

  -- Production p_ready_sset: gives Ncover ratio AND P_ready S-set
  have h_p_ready_main := p_ready_sset
    hP_orien_sset_k
    hP_ready_sub
    hP_orien_cover_all
    hretention
    h_ready_occupancy
    hK_ready_pos

  have hP_ready_ncover_ratio : Ncover (DiscretisedFurstenbergEstimate.dyadicDelta k) P_orien ≤
      (9 : ENNReal) * (K_ready + 1 : ENNReal) * Ncover (DiscretisedFurstenbergEstimate.dyadicDelta k) P_ready :=
    h_p_ready_main.1

  have hP_ready_sset : IsDeltaSSet δ_d t C_P_ready P_ready := by
    have h := h_p_ready_main.2
    rw [hscale_eq] at h
    have h_const : C_P_d * (9 * ((K_ready : ℝ) + 1)) = C_P_ready := by
      dsimp only [C_P_ready] <;> ring
    rw [h_const] at h
    exact h

  -- ==========================================================================
  -- LEDGER 1: Point losses → ε_Root
  --   Exact factorization:
  --     C_P_ready = 2 * δ^{-ε_input} * 4^t * 9^q * 9 * (K_ready+1)
  --     δ^{-ε_input} ≤ (4*Δ)^{-ε_input} * δ_d^{-ε_input}  [scale conversion]
  --     δ_d^{-rho_Delta} = (48*log(1/Δ))^m  [uniformization density]
  --   So C_P_ready * (48*log)^m * 9
  --     ≤ point_coeff(δ_d) * δ_d^{-ε_input} * δ_d^{-rho_Delta} * 9*(K_band+1)
  --     ≤ δ_d^{-ε_Root}  [by point_to_root_with_band]
  -- ==========================================================================

  -- Apply point_to_root_with_band at scale δ_d
  have h_point_main : point_coeff δ_d * δ_d ^ (-ε_input) * δ_d ^ (-rho_Delta) *
        (9 * ((K_band δ_d : ℝ) + 1)) ≤ δ_d ^ (-ε_Root) :=
    h_point_lemma_d δ_d hδ_d_pos hδ_d_le_point

  -- Scale conversion: δ^{-ε_input} ≤ (4*Δ)^{-ε_input} * δ_d^{-ε_input}
  -- From δ_d ≤ δ/(4*Δ) we get 4*Δ*δ_d ≤ δ, and x ↦ x^{-ε_input} is decreasing.
  have h_scale_conv : δ ^ (-ε_input) ≤ (4 * Δ) ^ (-ε_input) * δ_d ^ (-ε_input) := by
    have h1 : 0 < 4 * Δ := by positivity
    have h1' : (4 * Δ : ℝ) ≠ 0 := h1.ne'
    have h3 : δ_d ≤ δ / (4 * Δ) := by
      have h4 : (1 / Δ) * (δ / 4) = δ / (4 * Δ) := by ring
      rw [h4] at hδ_d_le_ratio4
      exact hδ_d_le_ratio4
    have h2 : 4 * Δ * δ_d ≤ δ := by
      have h21 : 4 * Δ * δ_d ≤ 4 * Δ * (δ / (4 * Δ)) :=
        mul_le_mul_of_nonneg_left h3 h1.le
      have h22 : 4 * Δ * (δ / (4 * Δ)) = δ := by
        rw [mul_comm, div_mul_cancel₀ _ h1']
      rw [h22] at h21
      exact h21
    have h_pos : 0 < 4 * Δ * δ_d :=
      mul_pos (mul_pos (by norm_num) hΔ_pos) hδ_d_pos
    have h_exp_neg : -ε_input < 0 := by linarith [hε_input_pos]
    have h41 : δ ^ (-ε_input) ≤ (4 * Δ * δ_d) ^ (-ε_input) :=
      scale_conversion_neg_exp h_pos h2 h_exp_neg
    have h5 : (4 * Δ * δ_d) ^ (-ε_input) = (4 * Δ) ^ (-ε_input) * δ_d ^ (-ε_input) :=
      Real.mul_rpow (by positivity) (by positivity)
    calc δ ^ (-ε_input)
      ≤ (4 * Δ * δ_d) ^ (-ε_input) := h41
    _ = (4 * Δ) ^ (-ε_input) * δ_d ^ (-ε_input) := h5

  -- K_ready from fibre step equals K_band(δ_d) = 2*k+7
  -- Full explicit dyadic identity chain:
  --   (1) K_ready = K_band_out          [definition of K_ready]
  --   (2) K_band_out = K_raw            [hK_band_eq, fibre step output]
  --   (3) K_raw = 2*k+7                 [hK_eq, raw producer output]
  --   (4) δ_d = dyadicDelta k           [hscale_eq]
  --   (5) dyadicDelta k = 2^(-k)        [by definition dyadicDelta]
  --   (6) ceil(log(1/δ_d)/log 2) = k    [ceil_log_dyadicDelta k, using (4)-(5)]
  --   (7) K_band(δ_d) = 2*k+7           [k_band_dyadic_eq k, using (6)]
  -- Therefore K_ready = K_band(δ_d).
  have h_K_ready_eq : (K_ready : ℝ) = (K_band δ_d : ℝ) := by
    -- (1)-(2): K_ready = K_band_out = K_raw
    have h1 : K_ready = K_raw := by
      dsimp only [K_ready]
      exact hK_band_eq
    -- (3): K_raw = 2*k+7
    have h2 : K_raw = 2 * k + 7 := hK_eq
    -- (4): δ_d = dyadicDelta k
    have h4 : δ_d = DiscretisedFurstenbergEstimate.dyadicDelta k := by
      exact hscale_eq.symm
    -- (5)-(6): ceil(log(1/δ_d)/log 2) = k
    have h6 : Nat.ceil (Real.log (1 / δ_d) / Real.log 2) = k := by
      rw [h4]
      exact ceil_log_dyadicDelta k
    -- (7): K_band δ_d = 2*k+7
    have h7 : K_band δ_d = 2 * k + 7 := by
      dsimp only [K_band]
      rw [h6] <;> ring
    -- Chain all equalities
    calc (K_ready : ℝ)
      = (K_raw : ℝ) := by exact_mod_cast h1
    _ = ((2 * k + 7 : ℕ) : ℝ) := by rw [h2]
    _ = (K_band δ_d : ℝ) := by rw [h7]

  -- Expand C_P_ready: C_P_d * 9 * (K_ready+1) = C_P_orien * 9^q * 9 * (K_ready+1)
  --   = 2 * C_P_norm * 9^q * 9 * (K_ready+1)
  --   = 2 * δ^{-ε_input} * 4^t * 9^q * 9 * (K_ready+1)
  have h_C_P_ready_expand : C_P_ready =
      2 * δ ^ (-ε_input) * (4 : ℝ)^t * (9 : ℝ)^q * 9 * ((K_ready : ℝ) + 1) := by
    dsimp only [C_P_ready, C_P_d, C_P_orien, C_P_norm]
    rw [hc_slope_eq]
    have h_ne : (1 / 2 : ℝ) ≠ 0 := by norm_num
    have h_div2 : ∀ (x : ℝ), x / (1 / 2 : ℝ) = 2 * x := by
      intro x; field_simp [h_ne] <;> ring
    simp [h_div2, mul_assoc]
    <;> ring

  -- rho_Delta identity: δ_d^{-rho_Delta} = (48*log(1/Δ))^m
  have h_rho_identity : δ_d ^ (-rho_Delta) = (48 * Real.log (1 / Δ)) ^ m := by
    dsimp only [δ_d, rho_Delta]
    have hlogΔ_pos : 0 < Real.log (1 / Δ) := by
      have h1 : 1 < 1 / Δ := by apply one_lt_one_div hΔ_pos hΔ_lt_one
      exact Real.log_pos h1
    have hlog48_pos : 0 < 48 * Real.log (1 / Δ) :=
      mul_pos (by norm_num) hlogΔ_pos
    let a : ℝ := Real.log (48 * Real.log (1 / Δ))
    let b : ℝ := Real.log (1 / Δ)
    have hb_ne : b ≠ 0 := hlogΔ_pos.ne'
    have h1 : Real.log Δ = -b := by
      have h11 : Real.log (1 / Δ) = -Real.log Δ := by
        simp [Real.log_div, hΔ_pos.ne'] <;> ring
      have h12 : b = Real.log (1 / Δ) := by rfl
      have h13 : -b = Real.log Δ := by
        rw [h12, h11] <;> ring
      exact h13.symm
    have h2 : Real.log ((Δ ^ m : ℝ)) = m * Real.log Δ := by
      rw [Real.log_pow] <;> ring
    have h_pos2 : 0 < (Δ ^ m : ℝ) := by positivity
    have h3 : (Δ ^ m : ℝ) ^ (-(a / b)) = Real.exp ((-(a / b)) * Real.log ((Δ ^ m : ℝ))) := by
      have h31 : (Δ ^ m : ℝ) ^ (-(a / b)) = Real.exp (Real.log ((Δ ^ m : ℝ)) * (-(a / b))) :=
        Real.rpow_def_of_pos h_pos2 (-(a / b))
      rw [h31]
      have h32 : Real.log ((Δ ^ m : ℝ)) * (-(a / b)) = (-(a / b)) * Real.log ((Δ ^ m : ℝ)) := by ring
      rw [h32]
    rw [h3, h2, h1]
    have h4 : (-(a / b)) * (m * (-b)) = m * a := by
      have h41 : (-(a / b)) * (m * (-b)) = (a / b) * ((m : ℝ) * b) := by ring
      rw [h41]
      have h42 : (a / b) * ((m : ℝ) * b) = (m : ℝ) * a := by
        have h43 : (a / b) * b = a := by
          have h : (a / b) * b = a * (b⁻¹ * b) := by ring
          rw [h]
          have h2 : b⁻¹ * b = 1 := by
            exact inv_mul_cancel₀ hb_ne
          rw [h2, mul_one]
        calc (a / b) * ((m : ℝ) * b)
            = (m : ℝ) * ((a / b) * b) := by ring
          _ = (m : ℝ) * a := by rw [h43] <;> ring
      exact_mod_cast h42
    rw [h4]
    have h51 : Real.exp (m * a) = (Real.exp a) ^ m := Real.exp_nat_mul a m
    have h52 : Real.exp a = 48 * Real.log (1 / Δ) := Real.exp_log hlog48_pos
    rw [h51, h52]

  -- Full factorization inequality
  have h_factor : C_P_ready * (48 * Real.log (1 / Δ)) ^ m * 9 ≤
      point_coeff δ_d * δ_d ^ (-ε_input) * δ_d ^ (-rho_Delta) *
        (9 * ((K_band δ_d : ℝ) + 1)) := by
    rw [h_C_P_ready_expand, h_K_ready_eq, ←h_rho_identity]
    dsimp only [point_coeff]
    have h1 : δ ^ (-ε_input) ≤ (4 * Δ) ^ (-ε_input) * δ_d ^ (-ε_input) := h_scale_conv
    have h_rho_pos : 0 ≤ δ_d ^ (-rho_Delta) := by positivity
    have h8 : δ ^ (-ε_input) * δ_d ^ (-rho_Delta) ≤
        (4 * Δ)^(-ε_input) * δ_d ^ (-ε_input) * δ_d ^ (-rho_Delta) :=
      mul_le_mul_of_nonneg_right h1 h_rho_pos
    have h_common_pos : 0 < 2 * (4 : ℝ)^t * (9 : ℝ)^q * 9 * ((K_band δ_d : ℝ) + 1) * 9 := by positivity
    have h9 : 0 ≤ 2 * (4 : ℝ)^t * (9 : ℝ)^q * 9 * ((K_band δ_d : ℝ) + 1) * 9 := h_common_pos.le
    have h10 : (2 * (4 : ℝ)^t * (9 : ℝ)^q * 9 * ((K_band δ_d : ℝ) + 1) * 9) * (δ ^ (-ε_input) * δ_d ^ (-rho_Delta)) ≤
        (2 * (4 : ℝ)^t * (9 : ℝ)^q * 9 * ((K_band δ_d : ℝ) + 1) * 9) * ((4 * Δ)^(-ε_input) * δ_d ^ (-ε_input) * δ_d ^ (-rho_Delta)) :=
      mul_le_mul_of_nonneg_left h8 h9
    ring_nf at h10 ⊢
    exact h10

  have h_point_to_root : C_P_ready * (48 * Real.log (1 / Δ)) ^ m * 9 ≤
      Real.rpow δ_d (-ε_Root) :=
    le_trans h_factor h_point_main

  -- ==========================================================================
  -- Step 6: Uniformize/decompose P_ready → P_common + RawMultiscaleDecomp
  -- ==========================================================================
  -- Budget for point uniformization: covered by h_point_to_root
  have h_budget_unif : C_P_ready * (48 * Real.log (1 / Δ)) ^ m * 9 ≤
      Real.rpow δ_d (-ε_Root) := h_point_to_root

  -- Step 6a: Uniformize P_ready → P_common (the ONE decomposition after all thinning)
  have hP_ready_bdd : P_ready ⊆ Metric.closedBall 0 1 :=
    Set.Subset.trans hP_ready_sub hP_orien_bdd

  rcases uniformize_with_representatives
      s t Δ m hm_pos hΔ_pos hΔ_lt_one q hq_pos hΔ_eq
      C_P_ready ε_Root hC_P_ready_pos hε_Root_pos
      P_ready hP_ready_bdd hP_ready_sset h_budget_unif
    with ⟨P_common, N_uniform, hP_common_sub, hP_common_uniform, _, hP_common_sset⟩

  have hP_common_bdd : P_common ⊆ Metric.closedBall 0 1 :=
    Set.Subset.trans hP_common_sub hP_ready_bdd

  have hP_common_interior : P_common ⊆ interior_set :=
    Set.Subset.trans hP_common_sub hP_ready_interior

  -- Step 6b: Apply Root decomposition to P_common
  rcases H_root m hm_ge_m0_root P_common N_uniform hP_common_bdd hP_common_uniform hP_common_sset
    with ⟨n_decomp, i, t_j, S, B, h_i0, h_in, h_ij, h_tj, h_SB, h_disj, h_good_ratio, h_bad_prod, h_set_between, h_reg_between, h_good_prod, h_bad_adj⟩

  let decomp : RawMultiscaleDecomp δ_d s t τ ε_G ε_bad n_decomp P_common :=
    { Δ := Δ
      m := m
      hδ_d := by rfl
      i := i
      t_j := t_j
      S := S
      B := B
      hi0 := h_i0
      hin := h_in
      h_strict_mono := h_ij
      h_tj_range := h_tj
      h_partition := h_SB
      h_disjoint := h_disj
      h_S_ratio := h_good_ratio
      h_B_product := h_bad_prod
      h_S_set := h_set_between
      h_S_regular := h_reg_between
      h_S_product := h_good_prod
      h_B_no_adjacent := h_bad_adj }

  have hn_pos : 0 < n_decomp := by
    by_contra h
    have h' : n_decomp = 0 := by omega
    have : m = 0 := by
      rw [h'] at h_in
      rw [h_i0] at h_in
      exact h_in.symm
    exact Nat.pos_iff_ne_zero.mp hm_pos this

  have hn_le_n0 : n_decomp ≤ n0 := by
    have h1 : (n_decomp : Int) ≤ 2 * ⌊1 / τ⌋ + 1 :=
      DirecretisedFurstenbergEstimate.Section9.n_bound decomp hτ_pos hΔ_pos hΔ_lt_one hm_pos
    have h2 : 0 < 1 / τ := by positivity
    have h3 : ⌊1 / τ⌋ = (Nat.floor (1 / τ) : Int) := by
      have h4 : 0 ≤ 1 / τ := by positivity
      apply Int.floor_eq_iff.mpr
      constructor
      · exact Nat.floor_le h4
      · exact Nat.lt_floor_add_one (1 / τ)
    rw [h3] at h1
    exact_mod_cast h1

  have h_decomp_m_eq : decomp.m = m := rfl
  have h_decompΔ_eq : decomp.Δ = Δ := rfl

  have h_decompΔ_pos : 0 < decomp.Δ := by
    rw [h_decompΔ_eq]
    exact hΔ_pos

  have h_decompΔ_lt_one : decomp.Δ < 1 := by
    rw [h_decompΔ_eq] <;> exact hΔ_lt_one

  -- ==========================================================================
  -- Step 6b: Filter squares' to squares_common (only squares meeting P_common)
  -- ==========================================================================
  let squares_common : Finset (DiscretisedFurstenbergEstimate.DyadicSquare k) :=
    squares'.filter (fun q => (q.toSet ∩ P_common).Nonempty)
  have hsq_common_sub : squares_common ⊆ squares' := Finset.filter_subset _ _
  have hsq_common_nonempty : ∀ q ∈ squares_common, (q.toSet ∩ P_common).Nonempty :=
    fun q hq => (Finset.mem_filter.mp hq).2

  -- Restrict tubeFam to squares_common domain
  let tubeFam_common (q : DiscretisedFurstenbergEstimate.DyadicSquare k) (hq : q ∈ squares_common) : Finset (DiscretisedFurstenbergEstimate.DyadicTube k) :=
    tubeFam q (hsq_common_sub hq)

  -- T₀_common: only tubes from squares_common squares
  let T₀_common : Finset (DiscretisedFurstenbergEstimate.DyadicTube k) :=
    Finset.biUnion squares_common.attach (fun q => tubeFam_common q.val q.property)
  have hT0_common_sub : T₀_common ⊆ T₀ := by
    intro T hT
    rcases Finset.mem_biUnion.mp hT with ⟨q, _, hT⟩
    exact hTube_sub q.val (hsq_common_sub q.property) hT

  -- Step 7: Map each P_common point to its square in squares_common
  -- ==========================================================================
  have hP_common_in_ready : P_common ⊆ P_ready := hP_common_sub
  have h_exists_square : ∀ (p : EuclideanPlane), p ∈ P_common →
      ∃ (q : DiscretisedFurstenbergEstimate.DyadicSquare k), q ∈ squares_common ∧ p ∈ q.toSet := by
    intro p hp
    have hp_ready : p ∈ P_ready := hP_common_in_ready hp
    have hp_orien : p ∈ P_orien := hp_ready.1
    rcases hp_ready.2 with ⟨q, hq_squares', hp_in_q⟩
    have hq_common : q ∈ squares_common := by
      apply Finset.mem_filter.mpr
      exact ⟨hq_squares', ⟨p, hp_in_q, hp⟩⟩
    exact ⟨q, hq_common, hp_in_q⟩
  let pointToSquare (p : EuclideanPlane) (hp : p ∈ P_common) : DiscretisedFurstenbergEstimate.DyadicSquare k :=
    Classical.choose (h_exists_square p hp)
  have hpts_in_squares : ∀ p hp, pointToSquare p hp ∈ squares_common := by
    intro p hp
    exact (Classical.choose_spec (h_exists_square p hp)).1
  have hpts_in_cell : ∀ p hp, p ∈ (pointToSquare p hp).toSet := by
    intro p hp
    exact (Classical.choose_spec (h_exists_square p hp)).2

  let Tp_common (p : EuclideanPlane) (hp : p ∈ P_common) : Finset (DiscretisedFurstenbergEstimate.DyadicTube k) :=
    tubeFam_common (pointToSquare p hp) (hpts_in_squares p hp)

  -- ==========================================================================
  -- Step 8: Assemble config from fibres + B1 from interior chart
  -- ==========================================================================
  -- Config assembled manually using juniper's assemble_config_from_fibres.
  -- NOT construct_nice_configuration (which sets M=1).
  -- Config assembled from squares_common (not squares') using juniper's
  -- assemble_config_from_fibres. P_common is unchanged; we only filter the
  -- square domain to squares that actually meet P_common.
  let config : DiscretisedFurstenbergEstimate.CombiningTheorem.CTNiceConfiguration k s (Real.rpow (DiscretisedFurstenbergEstimate.dyadicDelta k) (-lam)) M :=
    { P₀ := squares_common
      T₀ := T₀_common
      tubeFamily := tubeFam_common
      h_subset := fun q hq U hU => by
        exact Finset.mem_biUnion.mpr ⟨⟨q, hq⟩, by simp, hU⟩
      h_size := fun q hq => hTube_card q (hsq_common_sub hq)
      h_delta_s_set := fun q hq => hTube_sset q (hsq_common_sub hq)
      h_intersect := fun q hq U hU => hTube_intersect q (hsq_common_sub hq) U hU
      h_tube_parameters := (Finset.finite_toSet T₀_common).isBounded
      h_bounded := (Bornology.isBounded_biUnion_finset squares_common).mpr
        (fun q _ => DyadicSquare.toSet_isBounded q)
    }

  have hP0_eq : config.P₀ = squares_common := by rfl
  have hT0_eq : config.T₀ = T₀_common := by rfl
  have hP_common_sub_config : P_common ⊆ config.pointSet := by
    intro p hp
    let q := pointToSquare p hp
    have hq : q ∈ squares_common := hpts_in_squares p hp
    have hpq : p ∈ q.toSet := hpts_in_cell p hp
    have h : p ∈ (⋃ q' ∈ (squares_common : Set (DiscretisedFurstenbergEstimate.DyadicSquare k)), (q'.toSet : Set EuclideanPlane)) := by
      exact Set.mem_iUnion₂.mpr ⟨q, hq, hpq⟩
    simpa [config, CombiningTheorem.NiceConfiguration.pointSet] using h
  have h_each_square : ∀ q ∈ config.P₀, (q.toSet ∩ P_common).Nonempty :=
    fun q hq => by
      rw [hP0_eq] at hq
      exact hsq_common_nonempty q hq

  -- B1 from interior chart: P_common ⊆ [1/4,3/4]², config.pointSet ⊆ [0,1]²
  -- Do NOT assume config.pointSet ⊆ [1/4,3/4]² — that's false.
  -- B1 from interior chart: use clamp-aware strip bound directly
  -- Do NOT use abs(slope) < 1 — boundary U.a = -2^k gives slope = -1

  -- P_common ⊆ [1/4,3/4]² ⊆ [0,1)²
  have hP_common_unit : ∀ p ∈ P_common, 0 ≤ p 0 ∧ p 0 < 1 ∧ 0 ≤ p 1 ∧ p 1 < 1 := by
    intro p hp
    have h_int : p ∈ interior_set := hP_common_interior hp
    have h0 : 1 / 4 ≤ p 0 := h_int.1.1
    have h1 : p 0 ≤ 3 / 4 := h_int.1.2
    have h2 : 1 / 4 ≤ p 1 := h_int.2.1
    have h3 : p 1 ≤ 3 / 4 := h_int.2.2
    have h4 : 0 ≤ p 0 := by
      have h41 : (0 : ℝ) ≤ 1 / 4 := by norm_num
      exact le_trans h41 h0
    have h5 : p 0 < 1 := by
      have h51 : (3 / 4 : ℝ) < 1 := by norm_num
      exact lt_of_le_of_lt h1 h51
    have h6 : 0 ≤ p 1 := by
      have h61 : (0 : ℝ) ≤ 1 / 4 := by norm_num
      exact le_trans h61 h2
    have h7 : p 1 < 1 := by
      have h71 : (3 / 4 : ℝ) < 1 := by norm_num
      exact lt_of_le_of_lt h3 h71
    exact ⟨h4, h5, h6, h7⟩

  -- Squares in config.P₀ meet P_common, hence indices lie in [0,2^k)
  have h_squares_unit : ∀ (q : DiscretisedFurstenbergEstimate.DyadicSquare k), q ∈ config.P₀ →
      0 ≤ q.i ∧ q.i < (2 ^ k : ℤ) ∧ 0 ≤ q.j ∧ q.j < (2 ^ k : ℤ) := by
    intro q hq
    rw [hP0_eq] at hq
    have h_inter : (P_common ∩ (q.toSet : Set EuclideanPlane)).Nonempty := by
      have h : (q.toSet ∩ P_common).Nonempty := hsq_common_nonempty q hq
      rcases h with ⟨x, hx1, hx2⟩
      exact ⟨x, hx2, hx1⟩
    exact squares_unit_from_unit_interval hP_common_unit h_inter

  -- Strip bound for all tubes in config.T₀
  have h_tubes_strip : ∀ (T : DiscretisedFurstenbergEstimate.DyadicTube k), T ∈ config.T₀ →
      -(2 ^ k : ℤ) ≤ T.a ∧ T.a < (2 ^ k : ℤ) := by
    intro T hT
    rw [hT0_eq] at hT
    rcases Finset.mem_biUnion.mp hT with ⟨q, _, hT'⟩
    exact hTube_strip q.val (hsq_common_sub q.property) T hT'

  have hT0_intersects : ∀ (T : DiscretisedFurstenbergEstimate.DyadicTube k), T ∈ config.T₀ →
      ∃ (p : DiscretisedFurstenbergEstimate.DyadicSquare k), p ∈ config.P₀ ∧ (T.toSet ∩ p.toSet).Nonempty := by
    intro T hT
    rw [hT0_eq] at hT
    rcases Finset.mem_biUnion.mp hT with ⟨q, _, hT'⟩
    have hq_common : q.val ∈ squares_common := q.property
    have h_inter : (T.toSet ∩ (q.val.toSet : Set EuclideanPlane)).Nonempty :=
      hTube_intersect q.val (hsq_common_sub q.property) T hT'
    refine ⟨q.val, ?_, h_inter⟩
    rw [hP0_eq]; exact hq_common

  have h_b_bound : ∀ (T : DiscretisedFurstenbergEstimate.DyadicTube k), T ∈ config.T₀ →
      |(T.b : ℝ)| < 3 * (2 ^ k : ℝ) :=
    intercept_bound_from_geometry
      h_squares_unit h_tubes_strip hT0_intersects

  have h_tubes_bounded : config.T₀.card ≤ 12 * 16 ^ k :=
    tube_card_bounded_from_index_bounds
      h_tubes_strip h_b_bound

  have hB1 : B1BridgeHypotheses k config :=
    { h_squares_unit := h_squares_unit
      h_tubes_strip := h_tubes_strip
      h_tubes_bounded := h_tubes_bounded }

  have htube_bound : (config.T₀.card : ENNReal) ≤
      ENNReal.ofReal ((DiscretisedFurstenbergEstimate.dyadicDelta k) ^ (-ρ_T)) * Ncover δ_d T_orien := by
    have hρ_T_pos : 0 < ρ_T := by dsimp only [ρ_T]; positivity
    have h_ambient_absorb : K_ambient_upper ≤ δ_d ^ (-ρ_T) :=
      (Classical.choose_spec
        (constant_absorption_threshold K_ambient_upper ρ_T (by positivity) hρ_T_pos)).2
        δ_d hδ_d_pos hδ_d_le_ambient
    have hK_ambient_le_upper : (K_ambient : ℝ) ≤ K_ambient_upper := by
      dsimp only [K_ambient_upper]
      exact_mod_cast hK_ambient_le
    have hK_ennreal : (K_ambient : ENNReal) ≤ ENNReal.ofReal K_ambient_upper := by
      have h_eq : (K_ambient : ENNReal) = ENNReal.ofReal (K_ambient : ℝ) := by
        simp
      rw [h_eq]
      exact ENNReal.ofReal_le_ofReal hK_ambient_le_upper
    have h_absorb_ennreal : ENNReal.ofReal K_ambient_upper ≤ ENNReal.ofReal (δ_d ^ (-ρ_T)) := by
      exact ENNReal.ofReal_le_ofReal h_ambient_absorb
    have hT0_common_sub : T₀_common ⊆ T₀ := by
      intro T hT
      rcases Finset.mem_biUnion.mp hT with ⟨q, _, hT'⟩
      exact hTube_sub q.val (hsq_common_sub q.property) hT'
    have h_card_le : (config.T₀.card : ENNReal) ≤ (T₀.card : ENNReal) := by
      rw [hT0_eq]
      exact_mod_cast Finset.card_le_card hT0_common_sub
    have h_scale_eq : (DiscretisedFurstenbergEstimate.dyadicDelta k) = δ_d := hscale_eq
    calc (config.T₀.card : ENNReal)
      ≤ (T₀.card : ENNReal) := h_card_le
    _ ≤ (K_ambient : ENNReal) * Ncover δ_d T_orien := hT0_bound
    _ ≤ ENNReal.ofReal K_ambient_upper * Ncover δ_d T_orien :=
      mul_le_mul_right' hK_ennreal _
    _ ≤ ENNReal.ofReal (δ_d ^ (-ρ_T)) * Ncover δ_d T_orien :=
      mul_le_mul_right' h_absorb_ennreal _
    _ = ENNReal.ofReal ((DiscretisedFurstenbergEstimate.dyadicDelta k) ^ (-ρ_T)) * Ncover δ_d T_orien := by
      rw [h_scale_eq]

  -- ==========================================================================
  -- Step 8b: multiscaleToCombining_thickened P_common → CombiningConfig
  -- ==========================================================================
  -- This thickened version handles general Δ = 2^-q (not just Δ = 1/2).
  let C_P : ℝ := 1
  let Δ_arr : Fin (n_decomp + 1) → ℝ := fun j => Δ ^ decomp.i j.val
  have hΔ_arr_pos : ∀ i, 0 < Δ_arr i := by intro i; positivity

  -- Common log absorption fact: log(1/δ_d) ≥ 72900 * Δ^(-4)
  have h_log_absorb : Real.log (1 / δ_d) ≥ (72900 : ℝ) * Real.rpow Δ (-4) :=
    h_log_lower_bound δ_d hδ_d_pos hδ_d_le_log_lower
  have h_log_k : Real.log (1 / DiscretisedFurstenbergEstimate.dyadicDelta k) = Real.log (1 / δ_d) := by
    rw [hscale_eq]
  have h_log_pos : 0 < Real.log (1 / δ_d) := by
    have h1 : 1 < 1 / δ_d := by apply one_lt_one_div hδ_d_pos hδ_d_lt_one
    exact Real.log_pos h1

  -- Helper: ratio of consecutive Δ-powers is ≥ 1
  have hr_ge_one_helper : ∀ (j : Fin n_decomp),
      1 ≤ (Δ ^ decomp.i j.val : ℝ) / (Δ ^ decomp.i (j.val + 1)) := by
    intro j
    have h1 : decomp.i j.val < decomp.i (j.val + 1) := decomp.h_strict_mono j j.is_lt
    have h1' : decomp.i j.val ≤ decomp.i (j.val + 1) := le_of_lt h1
    have h2 : (Δ ^ decomp.i (j.val + 1) : ℝ) ≤ (Δ ^ decomp.i j.val : ℝ) :=
      pow_le_pow_of_le_one hΔ_pos.le hΔ_lt_one.le h1'
    have h3 : 0 < (Δ ^ decomp.i (j.val + 1) : ℝ) := by positivity
    have h_b_div : (Δ ^ decomp.i (j.val + 1) : ℝ) / (Δ ^ decomp.i (j.val + 1) : ℝ) = 1 := by
      apply div_self
      exact h3.ne'
    have h5 : 1 ≤ (Δ ^ decomp.i j.val : ℝ) / (Δ ^ decomp.i (j.val + 1)) := by
      rw [← h_b_div]
      gcongr
    exact h5

  -- Helper: log(1/dyadicDelta k)^C_P = log(1/δ_d)
  have h_log_cp : Real.log (1 / DiscretisedFurstenbergEstimate.dyadicDelta k) ^ C_P = Real.log (1 / δ_d) := by
    have h_eq : Real.log (1 / DiscretisedFurstenbergEstimate.dyadicDelta k) = Real.log (1 / δ_d) := h_log_k
    rw [h_eq]
    have hC_P_eq : C_P = 1 := by rfl
    rw [hC_P_eq, Real.rpow_one]

  have h_absorb_normal : ∀ (j : Fin n_decomp), j ∈ decomp.S →
      decomp.t_j j.val < t - ε_G / 2 →
      (72900 : ℝ) * Real.rpow Δ (-4) *
        ((Δ ^ decomp.i j.val : ℝ) / (Δ ^ decomp.i (j.val + 1))) ^ ε_bad ≤
      Real.log (1 / DiscretisedFurstenbergEstimate.dyadicDelta k) ^ C_P *
        ((Δ ^ decomp.i j.val : ℝ) / (Δ ^ decomp.i (j.val + 1))) ^ ε_N := by
    intro j hj _
    let r := (Δ ^ decomp.i j.val : ℝ) / (Δ ^ decomp.i (j.val + 1))
    have hr_ge_one : 1 ≤ r := hr_ge_one_helper j
    have h4 : r ^ ε_bad ≤ r ^ ε_N :=
      Real.rpow_le_rpow_of_exponent_le hr_ge_one hε_bad_lt_εN.le
    have hlog_nonneg : 0 ≤ Real.log (1 / DiscretisedFurstenbergEstimate.dyadicDelta k) ^ C_P := by
      rw [h_log_cp] <;> exact h_log_pos.le
    have hr_pos : 0 < r := by
      have h_zero_lt_one : (0 : ℝ) < 1 := by norm_num
      exact lt_of_lt_of_le h_zero_lt_one hr_ge_one
    have h_r_eps_pos : 0 < r ^ ε_bad := Real.rpow_pos_of_pos hr_pos ε_bad
    have h_step1 : (72900 : ℝ) * Real.rpow Δ (-4) * r ^ ε_bad ≤
        Real.log (1 / δ_d) * r ^ ε_bad :=
      mul_le_mul_of_nonneg_right h_log_absorb h_r_eps_pos.le
    have h_step2 : Real.log (1 / δ_d) * r ^ ε_bad =
        Real.log (1 / DiscretisedFurstenbergEstimate.dyadicDelta k) ^ C_P * r ^ ε_bad := by
      rw [h_log_cp]
    have h_step3 : Real.log (1 / DiscretisedFurstenbergEstimate.dyadicDelta k) ^ C_P * r ^ ε_bad ≤
        Real.log (1 / DiscretisedFurstenbergEstimate.dyadicDelta k) ^ C_P * r ^ ε_N :=
      mul_le_mul_of_nonneg_left h4 hlog_nonneg
    rw [h_step2] at h_step1
    exact le_trans h_step1 h_step3

  have h_absorb_good_high : ∀ (j : Fin n_decomp), j ∈ decomp.S →
      decomp.t_j j.val ≥ t →
      (72900 : ℝ) * Real.rpow Δ (-4) *
        ((Δ ^ decomp.i j.val : ℝ) / (Δ ^ decomp.i (j.val + 1))) ^ ε_bad ≤
      Real.log (1 / DiscretisedFurstenbergEstimate.dyadicDelta k) ^ C_P *
        ((Δ ^ decomp.i j.val : ℝ) / (Δ ^ decomp.i (j.val + 1))) ^ ε_G := by
    intro j hj _
    let r := (Δ ^ decomp.i j.val : ℝ) / (Δ ^ decomp.i (j.val + 1))
    have hr_ge_one : 1 ≤ r := hr_ge_one_helper j
    have hε_bad_le_εG : ε_bad ≤ ε_G := by linarith [hε_bad_le_quarter_εG]
    have h4 : r ^ ε_bad ≤ r ^ ε_G :=
      Real.rpow_le_rpow_of_exponent_le hr_ge_one hε_bad_le_εG
    have hlog_nonneg : 0 ≤ Real.log (1 / DiscretisedFurstenbergEstimate.dyadicDelta k) ^ C_P := by
      rw [h_log_cp] <;> exact h_log_pos.le
    have hr_pos : 0 < r := by
      have h_zero_lt_one : (0 : ℝ) < 1 := by norm_num
      exact lt_of_lt_of_le h_zero_lt_one hr_ge_one
    have h_r_eps_pos : 0 < r ^ ε_bad := Real.rpow_pos_of_pos hr_pos ε_bad
    have h_step1 : (72900 : ℝ) * Real.rpow Δ (-4) * r ^ ε_bad ≤
        Real.log (1 / δ_d) * r ^ ε_bad :=
      mul_le_mul_of_nonneg_right h_log_absorb h_r_eps_pos.le
    have h_step2 : Real.log (1 / δ_d) * r ^ ε_bad =
        Real.log (1 / DiscretisedFurstenbergEstimate.dyadicDelta k) ^ C_P * r ^ ε_bad := by
      rw [h_log_cp]
    have h_step3 : Real.log (1 / DiscretisedFurstenbergEstimate.dyadicDelta k) ^ C_P * r ^ ε_bad ≤
        Real.log (1 / DiscretisedFurstenbergEstimate.dyadicDelta k) ^ C_P * r ^ ε_G :=
      mul_le_mul_of_nonneg_left h4 hlog_nonneg
    rw [h_step2] at h_step1
    exact le_trans h_step1 h_step3

  have h_absorb_good_low : ∀ (j : Fin n_decomp), j ∈ decomp.S →
      t - ε_G / 2 ≤ decomp.t_j j.val → decomp.t_j j.val < t →
      ((72900 : ℝ) * Real.rpow Δ (-4) *
        ((Δ ^ decomp.i j.val : ℝ) / (Δ ^ decomp.i (j.val + 1))) ^ ε_bad) *
        ((Δ ^ decomp.i j.val : ℝ) / (Δ ^ decomp.i (j.val + 1))) ^ (ε_G / 2) ≤
      Real.log (1 / DiscretisedFurstenbergEstimate.dyadicDelta k) ^ C_P *
        ((Δ ^ decomp.i j.val : ℝ) / (Δ ^ decomp.i (j.val + 1))) ^ ε_G := by
    intro j hj _ _
    set r : ℝ := (Δ ^ decomp.i j.val : ℝ) / (Δ ^ decomp.i (j.val + 1)) with hr_def
    have hr_ge_one : 1 ≤ r := hr_ge_one_helper j
    have hr_nonneg : 0 ≤ r := le_trans (show (0 : ℝ) ≤ 1 by norm_num) hr_ge_one
    have hr_pos : 0 < r := lt_of_lt_of_le (show (0 : ℝ) < 1 by norm_num) hr_ge_one
    have h_sum : ε_bad + ε_G / 2 ≤ ε_G := by
      have h : ε_bad < ε_G / 2 := hε_bad_lt_half_εG
      have h2 : ε_bad + ε_G / 2 < ε_G := by
        calc ε_bad + ε_G / 2
          = ε_G / 2 + ε_bad := by ring
        _ < ε_G / 2 + ε_G / 2 := by gcongr
        _ = ε_G := by ring
      exact h2.le
    have h_rpow_add : Real.rpow r (ε_bad + ε_G / 2) = Real.rpow r ε_bad * Real.rpow r (ε_G / 2) :=
      Real.rpow_add hr_pos ε_bad (ε_G / 2)
    have h4 : Real.rpow r (ε_bad + ε_G / 2) ≤ Real.rpow r ε_G :=
      Real.rpow_le_rpow_of_exponent_le hr_ge_one h_sum
    have h6 : Real.rpow r ε_bad * Real.rpow r (ε_G / 2) ≤ Real.rpow r ε_G := by
      rw [←h_rpow_add]; exact h4
    have h7 : 0 < Real.rpow r ε_G := Real.rpow_pos_of_pos hr_pos ε_G
    have h8 : 0 ≤ (72900 : ℝ) * Real.rpow Δ (-4) := by
      have h1 : 0 ≤ (72900 : ℝ) := by norm_num
      have h2 : 0 < Real.rpow Δ (-4) := Real.rpow_pos_of_pos hΔ_pos (-4)
      exact mul_nonneg h1 h2.le
    have h9 : (72900 : ℝ) * Real.rpow Δ (-4) * (Real.rpow r ε_bad * Real.rpow r (ε_G / 2)) ≤
        (72900 : ℝ) * Real.rpow Δ (-4) * Real.rpow r ε_G :=
      mul_le_mul_of_nonneg_left h6 h8
    have h10 : (72900 : ℝ) * Real.rpow Δ (-4) * Real.rpow r ε_G ≤
        Real.log (1 / δ_d) * Real.rpow r ε_G :=
      mul_le_mul_of_nonneg_right h_log_absorb h7.le
    have h11 : Real.log (1 / δ_d) * Real.rpow r ε_G =
        Real.log (1 / DiscretisedFurstenbergEstimate.dyadicDelta k) ^ C_P * Real.rpow r ε_G := by
      rw [h_log_cp]
    have h_final : (72900 : ℝ) * Real.rpow Δ (-4) * (Real.rpow r ε_bad * Real.rpow r (ε_G / 2)) ≤
        Real.log (1 / DiscretisedFurstenbergEstimate.dyadicDelta k) ^ C_P * Real.rpow r ε_G :=
      le_trans h9 (le_trans h10 (le_of_eq h11))
    have h_goal : ((72900 : ℝ) * Real.rpow Δ (-4) * r ^ ε_bad) * r ^ (ε_G / 2) =
        (72900 : ℝ) * Real.rpow Δ (-4) * (Real.rpow r ε_bad * Real.rpow r (ε_G / 2)) := by
      exact mul_assoc ((72900 : ℝ) * Real.rpow Δ (-4)) (Real.rpow r ε_bad) (Real.rpow r (ε_G / 2))
    exact h_goal ▸ h_final

  have h_in : decomp.i n_decomp = m :=
    calc decomp.i n_decomp = decomp.m := decomp.hin
         _ = m := h_decomp_m_eq

  rcases multiscaleToCombining_thickened
      hs hst ht2.le hτ_pos hΔ_pos hΔ_lt_one hΔ_dyadic hε_bad_pos
      (m := m) (n := n_decomp) (i := decomp.i) (t_j := decomp.t_j)
      (S := decomp.S) (B := decomp.B) (P := P_common) (N := N_uniform)
      (k := k) (M := M) (lam := lam) (ε_G := ε_G) (η := η) (ε_N := ε_N) (C_P := C_P)
      hεG_pos h_εG_small config
      decomp.hi0 h_in decomp.h_strict_mono
      decomp.h_tj_range
      decomp.h_partition decomp.h_disjoint
      (fun j hj => by
        have h := decomp.h_S_ratio j hj
        rw [h_decompΔ_eq] at h
        exact h)
      (by
        have h := decomp.h_B_product
        rw [h_decompΔ_eq] at h
        exact h)
      (fun j hj => by
        have h := decomp.h_S_set j hj
        rw [h_decompΔ_eq] at h
        exact h)
      (fun j hj hts => by
        have h := decomp.h_S_regular j hj hts
        rw [h_decompΔ_eq] at h
        exact h)
      (by
        have h := decomp.h_S_product
        rw [h_decompΔ_eq] at h
        exact h)
      decomp.h_B_no_adjacent
      hP_common_uniform
      hP_common_sub_config h_each_square
      (by exact hscale_eq)
      h_absorb_normal h_absorb_good_high h_absorb_good_low
    with ⟨C_between, scaleClass, N', hcfg, h_tj_ge_t, h_tj_le_two, h_good_indices, h_bad_indices⟩

  have h_slope_bound : ∀ (T : DiscretisedFurstenbergEstimate.DyadicTube k), T ∈ config.T₀ → |T.slope| ≤ 1 := by
    intro T hT
    have h_strip := h_tubes_strip T hT
    have h1 : -(2 ^ k : ℝ) ≤ (T.a : ℝ) := by exact_mod_cast h_strip.1
    have h2 : (T.a : ℝ) ≤ (2 ^ k : ℝ) - 1 := by
      have h2' : T.a < (2 ^ k : ℤ) := by exact_mod_cast h_strip.2
      have h2'' : T.a ≤ (2 ^ k : ℤ) - 1 := by omega
      exact_mod_cast h2''
    have h4 : T.slope = (T.a : ℝ) * DiscretisedFurstenbergEstimate.dyadicDelta k := by
      rfl
    have h5 : DiscretisedFurstenbergEstimate.dyadicDelta k = 1 / (2 ^ k : ℝ) := by
      simp [DiscretisedFurstenbergEstimate.dyadicDelta] <;> norm_cast
    have h_pos : (0 : ℝ) < (2 ^ k : ℝ) := by positivity
    have h6 : -1 ≤ (T.a : ℝ) * (1 / (2 ^ k : ℝ)) := by
      have h61 : (-(2 ^ k : ℝ)) ≤ (T.a : ℝ) := h1
      have h : (-(2 ^ k : ℝ)) * (1 / (2 ^ k : ℝ)) ≤ (T.a : ℝ) * (1 / (2 ^ k : ℝ)) := by
        gcongr
      have h2 : (-(2 ^ k : ℝ)) * (1 / (2 ^ k : ℝ)) = -1 := by
        field_simp [h_pos.ne'] <;> ring
      rw [h2] at h
      exact h
    have h7 : (T.a : ℝ) * (1 / (2 ^ k : ℝ)) ≤ 1 := by
      have h71 : (T.a : ℝ) ≤ ((2 ^ k : ℝ) - 1) := h2
      have h : (T.a : ℝ) * (1 / (2 ^ k : ℝ)) ≤ ((2 ^ k : ℝ) - 1) * (1 / (2 ^ k : ℝ)) := by gcongr
      have h2 : ((2 ^ k : ℝ) - 1) * (1 / (2 ^ k : ℝ)) = 1 - 1 / (2 ^ k : ℝ) := by
        field_simp [h_pos.ne'] <;> ring
      rw [h2] at h
      have h3 : 1 - 1 / (2 ^ k : ℝ) ≤ 1 := by
        have h4 : 0 ≤ 1 / (2 ^ k : ℝ) := by positivity
        exact sub_le_self 1 h4
      exact le_trans h h3
    have h8 : -1 ≤ (T.a : ℝ) * DiscretisedFurstenbergEstimate.dyadicDelta k := by
      rw [h5] <;> exact h6
    have h9 : (T.a : ℝ) * DiscretisedFurstenbergEstimate.dyadicDelta k ≤ 1 := by
      rw [h5] <;> exact h7
    have h10 : |(T.a : ℝ) * DiscretisedFurstenbergEstimate.dyadicDelta k| ≤ 1 :=
      abs_le.mpr ⟨h8, h9⟩
    exact h4 ▸ h10

  have hextra : CombiningExtraHypotheses_v2
      s t ε_G η ε_N C_P ε_inc n_decomp lam k M config Δ_arr scaleClass :=
    construct_extra_hypotheses
      s t ε_G η ε_N C_P ε_inc n_decomp lam k M config Δ_arr scaleClass
      h_tj_ge_t h_tj_le_two
      h_slope_bound
      h_uniform h_exp_condition
  -- slope bound derived from h_tubes_strip (-(2^k) ≤ T.a < 2^k)

  have h_combining : CombiningConclusion
      s t τ ε_G η ε_N C_P
      (combiningC τ K_prop73 n_decomp C_P) (combiningCprime n_decomp τ)
      lam n_decomp Δ_arr scaleClass k M config :=
    H_combining_uniform n_decomp hn_pos hn_le_n0
      |>.2 ε_G η hεG_pos hεG_le_uniform hεN_le_εG hη_pos hη_le_uniform
      k hk_le M config Δ_arr scaleClass N' C_between
      hcfg hB1 hextra

  -- ==========================================================================
  -- Step 9: exponent_absorption
  -- ==========================================================================
  -- ==========================================================================
  -- LEDGER 3: Combining losses → good_gain
  --   thickening absorption + bad product + log factor + section9 exponent
  --   ≤ good_gain = ε_G * η / 8
  -- ==========================================================================
  let good_gain : ℝ := ε_G * η / 8

  -- Bridge: scaleClass-good scales correspond to decomposition's good scales
  -- (t_j ≥ t - ε_G/2). Provided by multiscaleToCombining_thickened.
  have h_good_scales_eq :
      Finset.univ.filter (fun j : Fin n_decomp => (scaleClass j).isGood) =
      decomp.S.filter (fun j => decomp.t_j j.val ≥ t - ε_G / 2) := h_good_indices

  have h_ratio_eq : ∀ (j : Fin n_decomp),
      Δ_arr j.castSucc / Δ_arr (Fin.succ j) =
      (decomp.Δ ^ decomp.i j.val : ℝ) / (decomp.Δ ^ decomp.i (j.val + 1)) := by
    intro j
    dsimp only [Δ_arr]
    rw [h_decompΔ_eq]
    <;> rfl

  have h_good_product : (∏ j ∈ Finset.univ.filter (fun j => (scaleClass j).isGood),
      (Δ_arr j.castSucc / Δ_arr (Fin.succ j)) ^ η) ≥ δ_d ^ (-good_gain) := by
    let G := decomp.S.filter (fun j : Fin n_decomp => decomp.t_j j.val ≥ t - ε_G / 2)
    have h_main : (∏ j ∈ G, ((decomp.Δ ^ decomp.i j.val : ℝ) / (decomp.Δ ^ decomp.i (j.val + 1))) ^ η) ≥
        δ_d ^ (-good_gain) :=
      decomposition_good_product
        hδ_d_pos hδ_d_lt_one hs hst hεG_pos hε_bad_pos hη_pos.le
        h_εG_small hε_bad_le_quarter_εG decomp h_decompΔ_pos h_decompΔ_lt_one
    have h_prod_eq : (∏ j ∈ Finset.univ.filter (fun j => (scaleClass j).isGood),
          (Δ_arr j.castSucc / Δ_arr (Fin.succ j)) ^ η) =
        (∏ j ∈ G, ((decomp.Δ ^ decomp.i j.val : ℝ) / (decomp.Δ ^ decomp.i (j.val + 1))) ^ η) := by
      rw [h_good_scales_eq]
      apply Finset.prod_congr rfl
      intro j _
      rw [h_ratio_eq j]
    rw [h_prod_eq]
    exact h_main
  -- Good product from decomposition_good_product (Step5IndependentHelpers)
  have h_bad_product : (∏ j ∈ Finset.univ.filter (fun j => (scaleClass j).isBad),
      Δ_arr (Fin.succ j) / Δ_arr j.castSucc) ≥ δ_d ^ ε_bad := by
    have hΔ_arr_pos : ∀ i, 0 < Δ_arr i := by intro i; positivity
    have h_main : (∏ j ∈ decomp.B, Δ_arr (Fin.succ j) / Δ_arr j.castSucc) ≥ δ_d ^ ε_bad :=
      decomposition_bad_product hδ_d_pos hε_bad_pos decomp Δ_arr hΔ_arr_pos
        (fun j => h_ratio_eq j)
    have h_prod_eq : (∏ j ∈ Finset.univ.filter (fun j => (scaleClass j).isBad),
          Δ_arr (Fin.succ j) / Δ_arr j.castSucc) =
        (∏ j ∈ decomp.B, Δ_arr (Fin.succ j) / Δ_arr j.castSucc) := by
      rw [h_bad_indices]
    rw [h_prod_eq]
    exact h_main
  have hC_pos : 0 < combiningC τ K_prop73 n_decomp C_P :=
    (H_combining_uniform n_decomp hn_pos hn_le_n0).1
  have hC_nonneg : 0 ≤ combiningC τ K_prop73 n_decomp C_P := hC_pos.le
  have hC_le_sum : combiningC τ K_prop73 n_decomp C_P ≤ C_combining_sum := by
    have h9 : n_decomp ∈ Finset.Icc 1 n0 := by
      simp only [Finset.mem_Icc] <;> omega
    have h10 : ∀ i ∈ Finset.Icc 1 n0, 0 ≤ combiningC τ K_prop73 i 1 := by
      intro i hi
      have h11 : 0 < i := (Finset.mem_Icc.mp hi).1
      exact (H_combining_uniform i h11 (Finset.mem_Icc.mp hi).2).1.le
    exact Finset.single_le_sum h10 h9
  have h_main_sum : (Real.log (1 / δ_d)) ^ (-C_combining_sum) ≥ δ_d ^ ε_log_loss :=
    (Classical.choose_spec (log_factor_bound_threshold C_combining_sum ε_log_loss hC_combining_sum_nonneg hε_log_loss_pos)).2
      δ_d hδ_d_pos hδ_d_le_log_combining
  have h_log_factor : (Real.log (1 / δ_d)) ^ (-(combiningC τ K_prop73 n_decomp C_P)) ≥
      δ_d ^ ε_log_loss := by
    set y : ℝ := Real.log (1 / δ_d) with hy_def
    have h_y_pos : 0 < y := by
      have h1 : 1 < 1 / δ_d := one_lt_one_div hδ_d_pos hδ_d_lt_one
      exact Real.log_pos h1
    by_cases h_y_ge_one : y ≥ 1
    · -- y ≥ 1: y^{-C} ≥ y^{-C_sum} since C ≤ C_sum
      have h10 : -(combiningC τ K_prop73 n_decomp C_P) ≥ -C_combining_sum := by linarith
      have h11 : y ^ (-(combiningC τ K_prop73 n_decomp C_P)) ≥ y ^ (-C_combining_sum) := by
        gcongr
        <;> linarith
      exact le_trans h_main_sum h11
    · -- y < 1: y^{-C} > 1 > δ_d^ε
      have h_y_lt_one : y < 1 := by linarith
      have h12 : y ^ (-(combiningC τ K_prop73 n_decomp C_P)) > 1 := by
        have h13 : y ^ (combiningC τ K_prop73 n_decomp C_P) < 1 :=
          Real.rpow_lt_one h_y_pos.le h_y_lt_one hC_pos
        have h14 : 0 < y ^ (combiningC τ K_prop73 n_decomp C_P) := by positivity
        have h15 : (y ^ (combiningC τ K_prop73 n_decomp C_P))⁻¹ > 1 := by
          have h : (y ^ (combiningC τ K_prop73 n_decomp C_P))⁻¹ = 1 / (y ^ (combiningC τ K_prop73 n_decomp C_P)) := by simp
          rw [h]
          have h17 : (1 : ℝ) / 1 < 1 / (y ^ (combiningC τ K_prop73 n_decomp C_P)) := one_div_lt_one_div_of_lt h14 h13
          have h18 : (1 : ℝ) / 1 = (1 : ℝ) := by norm_num
          rw [h18] at h17
          exact h17
        have h16 : (y ^ (combiningC τ K_prop73 n_decomp C_P))⁻¹ = y ^ (-(combiningC τ K_prop73 n_decomp C_P)) := by
          rw [← Real.rpow_neg h_y_pos.le] <;> ring
        rw [h16] at h15; exact h15
      have h17 : δ_d ^ ε_log_loss < 1 :=
        Real.rpow_lt_one hδ_d_pos.le hδ_d_lt_one hε_log_loss_pos
      have h18 : (1 : ℝ) < y ^ (-(combiningC τ K_prop73 n_decomp C_P)) := h12
      exact le_of_lt (lt_trans h17 h18)

  -- Combining budget via absorption_budget_verification
  let ε_combining_final : ℝ := ε_N / (16 * B_K)
  have hε_combining_final_pos : 0 < ε_combining_final := by
    dsimp only [ε_combining_final] <;> positivity

  have hC'_nonneg : 0 ≤ combiningCprime n_decomp τ :=
    (combiningCprime_pos hn_pos hτ_pos).le

  have hC'_mono : combiningCprime n_decomp τ ≤ combiningCprime n0 τ := by
    dsimp only [combiningCprime]
    have h_sum : ∑ i ∈ Finset.range n_decomp, (2 / τ) ^ i ≤ ∑ i ∈ Finset.range n0, (2 / τ) ^ i := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · have h_range : ∀ x, x < n_decomp → x ∈ Finset.range n0 := by
          intro x hx
          have h2 : x < n0 := lt_of_lt_of_le hx hn_le_n0
          exact Finset.mem_range.mpr h2
        exact Finset.range_subset.mpr h_range
      · intro i _ _; positivity
    exact mul_le_mul_of_nonneg_left h_sum (by norm_num)

  have hlam_bound' : (1 + combiningCprime n_decomp τ) * lam ≤ ε_G * η / 800 := by
    have h1 : (1 + combiningCprime n_decomp τ) * lam ≤ (1 + combiningCprime n0 τ) * lam := by
      gcongr
      <;> linarith
    exact h1.trans hbudget_lam

  have hρM_bound : ρ_M ≤ ε_G * η / 800 := by
    dsimp only [ρ_M]; exact le_refl _
  have hρT_bound : ρ_T ≤ ε_G * η / 800 := by
    dsimp only [ρ_T]; exact le_refl _
  have hεlog_bound : ε_log_loss ≤ ε_G * η / 800 := by
    dsimp only [ε_log_loss]; exact le_refl _

  have hρM_nonneg : 0 ≤ ρ_M := by dsimp only [ρ_M]; positivity
  have hρT_nonneg : 0 ≤ ρ_T := by dsimp only [ρ_T]; positivity
  have hεlog_nonneg : 0 ≤ ε_log_loss := by dsimp only [ε_log_loss]; positivity

  have h_budget_full : good_gain ≥
      (1 + combiningCprime n_decomp τ) * lam + ρ_M + ρ_T + ε_N + ε_bad + ε_log_loss + ε_combining_final :=
    absorption_budget_verification
      ε_G η ε_N ε_bad ε_combining_final
      hεG_pos hη_pos hεN_pos hε_bad_pos hε_combining_final_pos
      hεN_eq hε_bad_lt_εN B_K hB_K_ge3
      (by dsimp only [ε_combining_final] <;> ring)
      (combiningCprime n_decomp τ) lam ρ_M ρ_T ε_log_loss
      hC'_nonneg hlam_pos hρM_nonneg hρT_nonneg hεlog_nonneg
      hlam_bound' hρM_bound hρT_bound hεlog_bound

  have h_final_gain : good_gain ≥
      (1 + combiningCprime n_decomp τ) * lam + ρ_M + ρ_T + ε_N + ε_bad + ε_log_loss + ε_section9 := by
    have h : ε_section9 ≤ ε_combining_final := hε_section9_le
    have h_sum : (1 + combiningCprime n_decomp τ) * lam + ρ_M + ρ_T + ε_N + ε_bad + ε_log_loss + ε_section9 ≤
        (1 + combiningCprime n_decomp τ) * lam + ρ_M + ρ_T + ε_N + ε_bad + ε_log_loss + ε_combining_final := by
      gcongr
    exact le_trans h_sum h_budget_full
  -- Combining ledger proved via absorption_budget_verification

  -- LEDGER 4 (output gap): ε_target < ε_section9 (already hε_target_lt_section9)

  have hM_lower_d : (M : ℝ) ≥ δ_d ^ (-s + lam + ρ_M) := by
    have h : (M : ℝ) ≥ (DiscretisedFurstenbergEstimate.dyadicDelta k) ^ (-s + lam + ρ_M) := hM_lower
    rw [hscale_eq] at h
    exact h
  have hM_pos : 0 < M := hM_pos'
  have hgg_nonneg : 0 ≤ good_gain := by positivity

  have h_absorption : combiningLowerBound δ_d (M : ℝ)
      (combiningC τ K_prop73 n_decomp C_P) (combiningCprime n_decomp τ)
      lam s ε_N η n_decomp Δ_arr scaleClass ≥
      δ_d ^ (-(2 * s + ε_section9 + ρ_T)) :=
    exponent_absorption δ_d s hδ_d_pos hδ_d_lt_one M hM_pos
      (combiningC τ K_prop73 n_decomp C_P) (combiningCprime n_decomp τ)
      lam ε_N η good_gain n_decomp Δ_arr scaleClass
      ρ_M ρ_T ε_section9 ε_bad ε_log_loss
      hM_lower_d h_good_product h_bad_product h_log_factor h_final_gain
      hlam_pos.le hεN_pos.le hη_pos.le
      hρM_nonneg hρT_nonneg hε_section9_pos.le
      hε_bad_pos.le hεlog_nonneg
      hC'_nonneg hC_nonneg hgg_nonneg hΔ_arr_pos

  have hNcover_d : Ncover δ_d T_orien ≥
      ENNReal.ofReal (δ_d ^ (-(2 * s + ε_section9))) := by
    -- h_combining: config.T₀.card ≥ combiningLowerBound (at dyadicDelta k = δ_d)
    have h1 : (config.T₀.card : ENNReal) ≥
        ENNReal.ofReal (combiningLowerBound δ_d (M : ℝ)
          (combiningC τ K_prop73 n_decomp C_P) (combiningCprime n_decomp τ)
          lam s ε_N η n_decomp Δ_arr scaleClass) := by
      simpa [hscale_eq] using h_combining
    -- h_absorption: combiningLowerBound ≥ δ_d^{-(2s+ε_section9+ρ_T)}
    have h2 : ENNReal.ofReal (combiningLowerBound δ_d (M : ℝ)
          (combiningC τ K_prop73 n_decomp C_P) (combiningCprime n_decomp τ)
          lam s ε_N η n_decomp Δ_arr scaleClass) ≥
        ENNReal.ofReal (δ_d ^ (-(2 * s + ε_section9 + ρ_T))) :=
      ENNReal.ofReal_le_ofReal h_absorption
    have h3 : (config.T₀.card : ENNReal) ≥
        ENNReal.ofReal (δ_d ^ (-(2 * s + ε_section9 + ρ_T))) :=
      le_trans h2 h1
    -- htube_bound: config.T₀.card ≤ δ_d^{-ρ_T} * Ncover δ_d T_orien
    have h4 : (config.T₀.card : ENNReal) ≤
        ENNReal.ofReal (δ_d ^ (-ρ_T)) * Ncover δ_d T_orien := by
      simpa [hscale_eq] using htube_bound
    have h5 : ENNReal.ofReal (δ_d ^ (-(2 * s + ε_section9 + ρ_T))) ≤
        ENNReal.ofReal (δ_d ^ (-ρ_T)) * Ncover δ_d T_orien :=
      le_trans h3 h4
    -- Factor: δ_d^{-(2s+ε_section9+ρ_T)} = δ_d^{-ρ_T} * δ_d^{-(2s+ε_section9)}
    have h6 : δ_d ^ (-(2 * s + ε_section9 + ρ_T)) =
        δ_d ^ (-ρ_T) * δ_d ^ (-(2 * s + ε_section9)) := by
      rw [← Real.rpow_add hδ_d_pos] <;> ring_nf
    rw [h6] at h5
    have h7 : ENNReal.ofReal (δ_d ^ (-ρ_T)) * ENNReal.ofReal (δ_d ^ (-(2 * s + ε_section9))) ≤
        ENNReal.ofReal (δ_d ^ (-ρ_T)) * Ncover δ_d T_orien := by
      have h8 : ENNReal.ofReal (δ_d ^ (-ρ_T) * δ_d ^ (-(2 * s + ε_section9))) =
          ENNReal.ofReal (δ_d ^ (-ρ_T)) * ENNReal.ofReal (δ_d ^ (-(2 * s + ε_section9))) := by
        rw [← ENNReal.ofReal_mul] <;> positivity
      rw [h8] at h5
      exact h5
    set a : ENNReal := ENNReal.ofReal (δ_d ^ (-ρ_T)) with ha_def
    set b : ENNReal := ENNReal.ofReal (δ_d ^ (-(2 * s + ε_section9))) with hb_def
    set c : ENNReal := Ncover δ_d T_orien with hc_def
    have h_pos : 0 < δ_d ^ (-ρ_T) := Real.rpow_pos_of_pos hδ_d_pos _
    have h10 : a ≠ 0 := by
      rw [ha_def]
      have h : 0 < ENNReal.ofReal (δ_d ^ (-ρ_T)) := ENNReal.ofReal_pos.mpr h_pos
      exact h.ne'
    have h11 : a ≠ ⊤ := by
      rw [ha_def]; simp
    have h12 : a * b ≤ a * c := by
      simpa [ha_def, hb_def, hc_def] using h7
    have h14 : (a * b) / a ≤ (a * c) / a := by gcongr
    have h15 : (a * b) / a = b := by
      have h_comm : a * b = b * a := mul_comm a b
      rw [h_comm]
      exact ENNReal.mul_div_cancel_right h10 h11
    have h16 : (a * c) / a = c := by
      have h_comm : a * c = c * a := mul_comm a c
      rw [h_comm]
      exact ENNReal.mul_div_cancel_right h10 h11
    rw [h15, h16] at h14
    exact h14
  -- [SORRY-harbor] combiningConclusion + absorption + tube_bound → Ncover lower bound

  -- ==========================================================================
  -- Step 10: Final Ncover transfer
  -- ==========================================================================
  -- T_orien =(Ncover) T_norm =(fixed-ratio Kpack^3) T
  have hNcover_orien_eq : Ncover δ_norm T_orien = Ncover δ_norm T_norm := hNcover_T_orien_eq

  have hNcover_norm_ge_d : Ncover δ_norm T_orien ≥ Ncover δ_d T_orien := by
    -- δ_norm ≤ δ_d, so covering at finer scale δ_norm gives ≥ covering at coarser scale δ_d
    have h_toNN : δ_norm.toNNReal ≤ δ_d.toNNReal := by
      have h : δ_norm ≤ δ_d := by
        simpa [δ_d] using hδ_norm_le_d
      apply Real.toNNReal_le_toNNReal
      <;> linarith
    have h : Metric.externalCoveringNumber δ_d.toNNReal T_orien ≤
        Metric.externalCoveringNumber δ_norm.toNNReal T_orien :=
      Metric.externalCoveringNumber_anti h_toNN
    simpa [Ncover] using h

  -- Smallness condition for final transfer:
  -- δ^(ε_section9 - ε_target) ≤ Kpack^(-3) * Δ^E * 4^E = C_fixed
  have hδ_small_final : δ ^ (ε_section9 - ε_target) ≤ C_fixed := by
    have h1 : δ ≤ δ₀_final_transfer := hδ_le_final_transfer
    have hδ_nonneg : 0 ≤ δ := hδ_pos.le
    have h2 : δ ^ ε_gap ≤ δ₀_final_transfer ^ ε_gap :=
      Real.rpow_le_rpow hδ_nonneg h1 hε_gap_pos.le
    have h31 : δ₀_final_transfer = C_fixed ^ (1 / ε_gap) := by rfl
    have h32 : (C_fixed ^ (1 / ε_gap)) ^ ε_gap = C_fixed := by
      rw [← Real.rpow_mul hC_fixed_pos.le]
      have h4 : (1 / ε_gap) * ε_gap = 1 := by
        field_simp [hε_gap_pos.ne'] <;> ring
      rw [h4, Real.rpow_one]
    calc δ ^ ε_gap ≤ δ₀_final_transfer ^ ε_gap := h2
         _ = (C_fixed ^ (1 / ε_gap)) ^ ε_gap := by rw [h31]
         _ = C_fixed := h32

  have h_final_target : Ncover δ T ≥ ENNReal.ofReal (Real.rpow δ (-(2 * s + ε_target))) := by
    let Kpack := affineLine_packing_constant
    have hKpack_pos : 0 < (Kpack : ℝ) := by
      exact_mod_cast DirecretisedFurstenbergEstimate.Snapping.affineLine_packing_constant_pos'

    -- Step A: Ncover δ_norm T_norm ≥ δ_d^{-E}
    have hA1 : Ncover δ_norm T_norm ≥ ENNReal.ofReal (δ_d ^ (-E)) := by
      have h_eq : Ncover δ_norm T_orien = Ncover δ_norm T_norm := hNcover_orien_eq
      have h_ge : Ncover δ_norm T_orien ≥ Ncover δ_d T_orien := hNcover_norm_ge_d
      have h_main : Ncover δ_norm T_orien ≥ ENNReal.ofReal (δ_d ^ (-E)) :=
        le_trans hNcover_d h_ge
      rw [h_eq] at h_main
      exact h_main

    -- Step B: δ_d^{-E} ≥ Δ^E * δ_norm^{-E}  (since δ_d ≤ (1/Δ)*δ_norm and -E < 0)
    have hB2 : δ_d ^ (-E) ≥ Δ ^ E * δ_norm ^ (-E) := by
      have h1 : δ_d ≤ (1 / Δ) * δ_norm := hδ_d_le_ratio
      have h2 : 0 < δ_d := hδ_d_pos
      have h3 : 0 < (1 / Δ) * δ_norm := by positivity
      have h4 : δ_d ^ (-E) ≥ ((1 / Δ) * δ_norm) ^ (-E) := by
        have hE_pos : 0 < E := by linarith
        have h1' : 0 ≤ δ_d := by positivity
        have h2' : δ_d ≤ (1 / Δ) * δ_norm := h1
        have h3' : δ_d ^ E ≤ ((1 / Δ) * δ_norm) ^ E :=
          Real.rpow_le_rpow h1' h2' hE_pos.le
        have h4' : 0 < δ_d ^ E := by positivity
        have h5' : 0 < ((1 / Δ) * δ_norm) ^ E := by positivity
        have h6' : (((1 / Δ) * δ_norm) ^ E)⁻¹ ≤ (δ_d ^ E)⁻¹ := by
          have h61 : 1 / ((1 / Δ) * δ_norm) ^ E ≤ 1 / (δ_d ^ E) := one_div_le_one_div_of_le h4' h3'
          have h62 : (((1 / Δ) * δ_norm) ^ E)⁻¹ = 1 / ((1 / Δ) * δ_norm) ^ E := by simp
          have h63 : (δ_d ^ E)⁻¹ = 1 / (δ_d ^ E) := by simp
          rw [h62, h63]
          exact h61
        have h7' : δ_d ^ (-E) = (δ_d ^ E)⁻¹ := by
          rw [Real.rpow_neg hδ_d_pos.le] <;> ring
        have h8' : ((1 / Δ) * δ_norm) ^ (-E) = (((1 / Δ) * δ_norm) ^ E)⁻¹ := by
          rw [Real.rpow_neg (show 0 ≤ (1 / Δ) * δ_norm by positivity)] <;> ring
        rw [h7', h8']
        exact h6'
      have h5 : ((1 / Δ) * δ_norm) ^ (-E) = (1 / Δ) ^ (-E) * δ_norm ^ (-E) := by
        rw [Real.mul_rpow (by positivity) (by positivity)]
      have h6 : (1 / Δ) ^ (-E) = Δ ^ E := by
        have h71 : (1 / Δ) ^ (-E) = ((1 / Δ) ^ E)⁻¹ := by
          rw [← Real.rpow_neg (show 0 ≤ 1 / Δ by positivity)] <;> ring
        rw [h71]
        have h72 : (1 / Δ) ^ E = (1 : ℝ) / Δ ^ E := by
          rw [Real.div_rpow (by norm_num) (by positivity)]
          have h1 : (1 : ℝ) ^ E = 1 := by simp
          rw [h1]
        rw [h72]
        have h73 : ((1 : ℝ) / Δ ^ E)⁻¹ = Δ ^ E := by
          field_simp [hΔ_pos.ne'] <;> ring
        exact h73
      rw [h5, h6] at h4
      exact h4
    have hB3 : ENNReal.ofReal (δ_d ^ (-E)) ≥ ENNReal.ofReal (Δ ^ E * δ_norm ^ (-E)) :=
      ENNReal.ofReal_le_ofReal hB2

    -- Step C: Ncover δ_norm T_norm ≥ ENNReal.ofReal (Δ^E * δ_norm^{-E})
    have hC : Ncover δ_norm T_norm ≥ ENNReal.ofReal (Δ ^ E * δ_norm ^ (-E)) :=
      le_trans hB3 hA1

    -- Step D: Packing transfer + exponent gap absorption
    let Kpack := affineLine_packing_constant
    have hKpack_pos : 0 < (Kpack : ℝ) := by
      exact_mod_cast DirecretisedFurstenbergEstimate.Snapping.affineLine_packing_constant_pos'
    have hKpack_ge1 : 1 ≤ (Kpack : ℝ) := by exact_mod_cast hKpack_pos

    -- D1: 3x doubling: Ncover(δ_norm, T_norm) ≤ Kpack^3 * Ncover(2δ, T_norm)
    have hD1 : Ncover δ_norm T_norm ≤ (Kpack : ENNReal)^3 * Ncover (2 * δ) T_norm := by
      have h_doub2 := DirecretisedFurstenbergEstimate.Snapping.affineLine_doubling_iter δ_norm hδ_norm_pos 3 (S := T_norm)
      have h9 : ((2 ^ 3 : ℕ) : ℝ) * δ_norm = 2 * δ := by
        norm_num <;> dsimp only [δ_norm] <;> ring
      have hK : (affineLine_packing_constant : ENNReal) = (Kpack : ENNReal) := by
        simp [Kpack] <;> norm_cast
      have h6 : (affineLine_packing_constant : ENNReal)^3 = (Kpack : ENNReal)^3 := by rw [hK]
      have h7 : (((2 ^ 3 : ℕ) : ℝ) * δ_norm).toNNReal = (2 * δ).toNNReal := by rw [h9]
      have h_main : Metric.externalCoveringNumber δ_norm.toNNReal T_norm ≤ (Kpack : ENNReal)^3 * Metric.externalCoveringNumber (2 * δ).toNNReal T_norm := by
        rw [h6, h7] at h_doub2
        exact h_doub2
      exact h_main

    -- D2: Therefore Ncover(2δ, T_norm) ≥ Ncover(δ_norm, T_norm) / Kpack^3
    have hD2 : Ncover (2 * δ) T_norm ≥ Ncover δ_norm T_norm / (Kpack : ENNReal)^3 := by
      have h_ne_zero : (Kpack : ENNReal)^3 ≠ 0 := by
        have h : (Kpack : ENNReal) ≠ 0 := by exact_mod_cast hKpack_pos.ne'
        exact pow_ne_zero 3 h
      have h_ne_top : (Kpack : ENNReal)^3 ≠ ⊤ := by simp
      exact ENNReal.div_le_of_le_mul' hD1

    -- D3: Get explicit U < 2 from normalization
    rcases ncover_line_upper_explicit with ⟨U, hU_pos, hU_lt_2, h_ncover_upper⟩

    -- D4: U*δ < 2δ, so Ncover(U*δ, T_norm) ≥ Ncover(2δ, T_norm)
    have hUδ_lt_2δ : U * δ < 2 * δ :=
      mul_lt_mul_of_pos_right hU_lt_2 hδ_pos
    have hD4 : Ncover (U * δ) T_norm ≥ Ncover (2 * δ) T_norm := by
      have h_toNN : (U * δ).toNNReal ≤ (2 * δ).toNNReal := by
        have h_nonneg1 : 0 ≤ U * δ := mul_pos hU_pos hδ_pos |>.le
        have h_le : U * δ ≤ 2 * δ := hUδ_lt_2δ.le
        exact Real.toNNReal_le_toNNReal h_le
      simpa [Ncover] using Metric.externalCoveringNumber_anti (A := T_norm) h_toNN

    -- D5: Lipschitz: Ncover(U*δ, T_norm) ≤ Ncover(δ, T)
    have hT_norm_def : T_norm = Normalization.φ_line '' T := by rfl
    have hD5 : Ncover (U * δ) T_norm ≤ Ncover δ T := by
      rw [hT_norm_def]
      simpa [Ncover] using h_ncover_upper δ T hδ_pos

    -- D6: Chain: Ncover(δ, T) ≥ Ncover(U*δ, T_norm) ≥ Ncover(2δ, T_norm) ≥ Ncover(δ_norm, T_norm) / Kpack^3
    have hD6 : Ncover δ T ≥ Ncover δ_norm T_norm / (Kpack : ENNReal)^3 :=
      calc Ncover δ T
        ≥ Ncover (U * δ) T_norm := hD5
      _ ≥ Ncover (2 * δ) T_norm := hD4
      _ ≥ Ncover δ_norm T_norm / (Kpack : ENNReal)^3 := hD2

    -- D7: Lower bound in real form
    have hD7 : Ncover δ T ≥ ENNReal.ofReal ((Δ ^ E * δ_norm ^ (-E)) / (Kpack : ℝ)^3) := by
      have h_pos1 : 0 ≤ Δ ^ E * δ_norm ^ (-E) := by positivity
      have hKpack_cube_pos : 0 < (Kpack : ℝ)^3 := by positivity
      have hKpack_enreal_eq : (Kpack : ENNReal)^3 = ENNReal.ofReal ((Kpack : ℝ)^3) := by
        have h1 : ∀ (n : ℕ), (↑n : ENNReal) = ENNReal.ofReal (↑n : ℝ) := by
          intro n; simp
        simpa using h1 ((Kpack : ℕ)^3)
      have h_div_eq : ENNReal.ofReal (Δ ^ E * δ_norm ^ (-E)) / (Kpack : ENNReal)^3 =
          ENNReal.ofReal ((Δ ^ E * δ_norm ^ (-E)) / (Kpack : ℝ)^3) := by
        rw [ENNReal.ofReal_div_of_pos hKpack_cube_pos, hKpack_enreal_eq]
      have hC_div : ENNReal.ofReal (Δ ^ E * δ_norm ^ (-E)) / (Kpack : ENNReal)^3 ≤
          Ncover δ_norm T_norm / (Kpack : ENNReal)^3 :=
        ENNReal.div_le_div_right hC ((Kpack : ENNReal)^3)
      rw [h_div_eq] at hC_div
      exact le_trans hC_div hD6

    -- D8: Simplify (Δ^E * δ_norm^{-E}) / Kpack^3 = C_fixed * δ^{-E}
    have hD8 : (Δ ^ E * δ_norm ^ (-E)) / (Kpack : ℝ)^3 = C_fixed * δ ^ (-E) := by
      have h9 : δ_norm = δ / 4 := by rfl
      have h10 : δ_norm ^ (-E) = (4 : ℝ) ^ E * δ ^ (-E) := by
        rw [h9]
        have h11 : (δ / 4 : ℝ) ^ (-E) = (4 : ℝ) ^ E * δ ^ (-E) := by
          have h12 : (δ / 4 : ℝ) ^ (-E) = ((δ / 4 : ℝ) ^ E)⁻¹ := by
            rw [← Real.rpow_neg (show 0 ≤ δ / 4 by positivity)] <;> ring
          rw [h12]
          have h13 : (δ / 4 : ℝ) ^ E = δ ^ E / (4 : ℝ) ^ E := by
            rw [Real.div_rpow (by positivity) (by positivity)]
          rw [h13]
          have h14 : (δ ^ E / (4 : ℝ) ^ E)⁻¹ = (4 : ℝ) ^ E / δ ^ E := by
            field_simp [hδ_pos.ne'] <;> ring
          rw [h14]
          have h15 : (4 : ℝ) ^ E / δ ^ E = (4 : ℝ) ^ E * δ ^ (-E) := by
            have h16 : δ ^ (-E) = (δ ^ E)⁻¹ := by
              rw [← Real.rpow_neg hδ_pos.le] <;> ring
            rw [h16] <;> ring
          exact h15
        exact h11
      have h_coeff : (Δ ^ E * ((4 : ℝ) ^ E * δ ^ (-E))) / (Kpack : ℝ)^3 =
          ((Δ ^ E * (4 : ℝ) ^ E) / (Kpack : ℝ)^3) * δ ^ (-E) := by ring
      rw [h10, h_coeff]
      have h_C_fixed_eq : C_fixed = (Δ ^ E * (4 : ℝ) ^ E) / (Kpack : ℝ)^3 := by
        dsimp only [C_fixed]
        have h_int_power : (Kpack : ℝ)^(-3 : ℤ) = 1 / (Kpack : ℝ)^3 := by
          simp [zpow_neg, zpow_ofNat]
          <;> field_simp [hKpack_pos.ne'] <;> ring
        rw [h_int_power] <;> ring
      rw [h_C_fixed_eq]

    -- D9: C_fixed * δ^{-E} ≥ δ^{-(2s+ε_target)} using δ^{ε_gap} ≤ C_fixed
    have hD9 : C_fixed * δ ^ (-E) ≥ δ ^ (-(2 * s + ε_target)) := by
      have h11 : ε_gap - E = -(2 * s + ε_target) := by
        dsimp only [ε_gap, E] <;> ring
      have h12 : C_fixed * δ ^ (-E) ≥ δ ^ ε_gap * δ ^ (-E) := by
        have h13 : 0 ≤ δ ^ (-E) := by positivity
        exact mul_le_mul_of_nonneg_right hδ_small_final h13
      have h14 : δ ^ ε_gap * δ ^ (-E) = δ ^ (ε_gap - E) := by
        rw [← Real.rpow_add hδ_pos] <;> ring_nf
      rw [h14, h11] at h12
      exact h12

    have h_final_target : Ncover δ T ≥ ENNReal.ofReal (Real.rpow δ (-(2 * s + ε_target))) := by
      rw [hD8] at hD7
      have h15 : ENNReal.ofReal (C_fixed * δ ^ (-E)) ≥
          ENNReal.ofReal (δ ^ (-(2 * s + ε_target))) :=
        ENNReal.ofReal_le_ofReal hD9
      exact le_trans h15 hD7

    exact h_final_target

  -- Weaken from ε_target to min ε_input ε_target
  have h_min_le : min ε_input ε_target ≤ ε_target := min_le_right _ _
  have h_sum_le : 2 * s + min ε_input ε_target ≤ 2 * s + ε_target :=
    add_le_add_right h_min_le (2 * s)
  have h_exp : -(2 * s + min ε_input ε_target) ≥ -(2 * s + ε_target) :=
    neg_le_neg h_sum_le
  have h_rpow : Real.rpow δ (-(2 * s + min ε_input ε_target)) ≤ Real.rpow δ (-(2 * s + ε_target)) :=
    Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_lt_one.le h_exp
  have h' : ENNReal.ofReal (Real.rpow δ (-(2 * s + min ε_input ε_target))) ≤
      ENNReal.ofReal (Real.rpow δ (-(2 * s + ε_target))) :=
    ENNReal.ofReal_le_ofReal h_rpow
  have h_final : Ncover δ T ≥ ENNReal.ofReal (Real.rpow δ (-(2 * s + min ε_input ε_target))) :=
    le_trans h' h_final_target

  exact h_final

end DirecretisedFurstenbergEstimate.Section9Assembly
