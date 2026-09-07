module

/-
  CBetweenGlue — C_between amplification bridge for fine config.

  Bridges between shifted coarse C_between constants and the
  consumer-amplified C_between_out constants.

  Key facts:
  1. C_between_out j = A_amp * C (normal) or max(A_amp * C_reg j, K_reg j) (good)
  2. Under sufficient smallness of δ, A_amp ≥ 1, so shifted coarse C_between
     ≤ C_between_out (when C_between ≤ C)
  3. C_between_out satisfies equation-(89) (from FineConfigFromConsumer)

  This lemma packages the consumer output so cobalt can directly use
  C_between_out as the C_between field of the fine CombiningConfig.

  Whiteprint node: combining_theorem_rework / cbetween_amplification_bridge
  Status: In progress.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.Equation89Bounds
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DiscretisedFurstenbergEstimate.CombiningTheorem

/-- Amplification factor A_amp for the tail uniformisation consumer. -/
def consumerAmplificationFactor
    (n_fine : ℕ) (K : ℝ) (δ : ℝ) : ℝ :=
  9 * 2 * K * (24 * Real.log (1 / δ) / (n_fine : ℝ)) ^ n_fine * (4 : ℝ)^n_fine

/-- Helper: 1 ≤ x^n for x ≥ 1 and n ≥ 0. -/
lemma one_le_pow' {x : ℝ} {n : ℕ} (hx : 1 ≤ x) : 1 ≤ x ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    simp [pow_succ] at *
    <;> nlinarith

/-- The amplification factor is ≥ 1 when K ≥ 1, n_fine ≥ 1, and
    24 * log(1/δ) ≥ n_fine.

    In practice δ is sufficiently small that this holds. -/
lemma consumerAmplificationFactor_ge_one
    {n_fine : ℕ} (hn_fine_pos : 0 < n_fine)
    {K : ℝ} (hK_ge_one : 1 ≤ K)
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (h_log_large : (n_fine : ℝ) ≤ 24 * Real.log (1 / δ)) :
    1 ≤ consumerAmplificationFactor n_fine K δ := by
  dsimp only [consumerAmplificationFactor]
  have h_npos : (n_fine : ℝ) > 0 := by exact_mod_cast hn_fine_pos
  have h2 : 1 ≤ 24 * Real.log (1 / δ) / (n_fine : ℝ) := by
    have h4 : 24 * Real.log (1 / δ) / (n_fine : ℝ) ≥
        (n_fine : ℝ) / (n_fine : ℝ) := by gcongr
    have h5 : (n_fine : ℝ) / (n_fine : ℝ) = 1 := by
      field_simp [h_npos.ne'] <;> ring
    linarith
  have h3 : 1 ≤ (24 * Real.log (1 / δ) / (n_fine : ℝ)) ^ n_fine :=
    one_le_pow' h2
  have h4 : 1 ≤ (4 : ℝ)^n_fine := one_le_pow' (by norm_num)
  have h5 : 1 ≤ 9 * 2 * K := by
    have h6 : 1 ≤ K := hK_ge_one
    nlinarith
  calc 1
    = 1 * 1 * 1 := by ring
  _ ≤ (9 * 2 * K) * ((24 * Real.log (1 / δ) / (n_fine : ℝ)) ^ n_fine) * (4 : ℝ)^n_fine := by
    gcongr <;> linarith

/-- Bridge: shifted coarse C_between ≤ amplified C_between_out (normal levels).

    Requires C_between (shift j) ≤ C (the coarse S-set constant used by the
    consumer). Since A_amp ≥ 1, we have C_between (shift j) ≤ C ≤ A_amp * C. -/
lemma cbetween_normal_amplification_bridge
    {n_fine : ℕ} (hn_fine_pos : 0 < n_fine)
    {K : ℝ} (hK_ge_one : 1 ≤ K)
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (h_log_large : (n_fine : ℝ) ≤ 24 * Real.log (1 / δ))
    {C : ℝ} (hC_nonneg : 0 ≤ C)
    (C_between_coarse : ℝ)
    (h_le : C_between_coarse ≤ C) :
    C_between_coarse ≤ consumerAmplificationFactor n_fine K δ * C := by
  have hA_ge_one : 1 ≤ consumerAmplificationFactor n_fine K δ :=
    consumerAmplificationFactor_ge_one hn_fine_pos hK_ge_one hδ_pos hδ_lt_one h_log_large
  calc
    C_between_coarse ≤ C := h_le
    _ = 1 * C := by ring
    _ ≤ consumerAmplificationFactor n_fine K δ * C := by
      gcongr <;> linarith

/-- Bridge: shifted coarse C_between ≤ amplified C_between_out (good levels).

    The output constant is max(A_amp * C_reg j, K_reg j). If both
    C_between_coarse ≤ C_reg j and C_between_coarse ≤ K_reg j, then
    C_between_coarse ≤ max(A_amp * C_reg j, K_reg j). -/
lemma cbetween_good_amplification_bridge
    {n_fine : ℕ} (hn_fine_pos : 0 < n_fine)
    {K : ℝ} (hK_ge_one : 1 ≤ K)
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (h_log_large : (n_fine : ℝ) ≤ 24 * Real.log (1 / δ))
    {C_reg K_reg : ℝ} (hC_reg_nonneg : 0 ≤ C_reg)
    (C_between_coarse : ℝ)
    (h_le_Creg : C_between_coarse ≤ C_reg)
    (h_le_Kreg : C_between_coarse ≤ K_reg) :
    C_between_coarse ≤
      max (consumerAmplificationFactor n_fine K δ * C_reg) K_reg := by
  have h1 : C_between_coarse ≤ consumerAmplificationFactor n_fine K δ * C_reg :=
    cbetween_normal_amplification_bridge hn_fine_pos hK_ge_one hδ_pos hδ_lt_one
      h_log_large hC_reg_nonneg C_between_coarse h_le_Creg
  exact le_max_of_le_left h1

/-- Package the consumer's equation-(89) output for the amplified constant
    (normal levels). This is a trivial restatement to make the glue explicit. -/
lemma amplified_cbetween_satisfies_eq89_normal
    {n_fine : ℕ} {δ : ℝ} {Δ' : Fin (n_fine + 1) → ℝ}
    {C_P_fine ε_N : ℝ} {scaleClass' : Fin n_fine → ScaleClass}
    (A_amp C : ℝ)
    (h_bound : ∀ j, scaleClass' j = ScaleClass.normal →
      A_amp * C ≤ (Real.log (1 / δ)) ^ C_P_fine *
        ((Δ' j.castSucc) / (Δ' (Fin.succ j))) ^ ε_N) :
    ∀ j, scaleClass' j = ScaleClass.normal →
      (A_amp * C) ≤ (Real.log (1 / δ)) ^ C_P_fine *
        ((Δ' j.castSucc) / (Δ' (Fin.succ j))) ^ ε_N :=
  h_bound

/-- Package the consumer's equation-(89) output for the amplified good constant. -/
lemma amplified_cbetween_satisfies_eq89_good
    {n_fine : ℕ} {δ : ℝ} {Δ' : Fin (n_fine + 1) → ℝ}
    {C_P_fine ε_G : ℝ} {scaleClass' : Fin n_fine → ScaleClass}
    (A_amp C_reg K_reg : Fin n_fine → ℝ)
    (h_bound : ∀ j (t_j : ℝ), scaleClass' j = ScaleClass.good t_j →
      max (A_amp j * C_reg j) (K_reg j) ≤ (Real.log (1 / δ)) ^ C_P_fine *
        ((Δ' j.castSucc) / (Δ' (Fin.succ j))) ^ ε_G) :
    ∀ j (t_j : ℝ), scaleClass' j = ScaleClass.good t_j →
      max (A_amp j * C_reg j) (K_reg j) ≤ (Real.log (1 / δ)) ^ C_P_fine *
        ((Δ' j.castSucc) / (Δ' (Fin.succ j))) ^ ε_G :=
  h_bound

/-- Monotonicity of IsDeltaSSet in the constant parameter. -/
lemma isDeltaSSet_mono {X : Type*} [PseudoMetricSpace X]
    {δ s C C' : ℝ} {P : Set X}
    (h : IsDeltaSSet δ s C P) (hC : C ≤ C') (hC'_pos : 0 < C') :
    IsDeltaSSet δ s C' P := by
  rcases h with ⟨h1, h2, h3, h4, h5⟩
  refine ⟨h1, h2, hC'_pos, h4, fun x r hr => ?_⟩
  have h6 := h5 x r hr
  have h7 : ENNReal.ofReal C ≤ ENNReal.ofReal C' :=
    ENNReal.ofReal_le_ofReal hC
  calc (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) : ℝ≥0∞)
    ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
        (Metric.externalCoveringNumber δ.toNNReal P : ℝ≥0∞) := h6
  _ ≤ ENNReal.ofReal C' * (ENNReal.ofReal r) ^ s *
        (Metric.externalCoveringNumber δ.toNNReal P : ℝ≥0∞) := by
    gcongr

/-- Monotonicity of IsSetBetweenScales in the constant parameter. -/
lemma isSetBetweenScales_mono
    {P : Set (EuclideanSpace ℝ (Fin 2))} {δ Δ s C C' : ℝ}
    (h : IsSetBetweenScales P δ Δ s C)
    (hC : C ≤ C') (hC'_pos : 0 < C') :
    IsSetBetweenScales P δ Δ s C' := by
  rcases h with ⟨hδ_pos, hΔ_pos, hδ_le, hs, hC_pos, hmain⟩
  refine ⟨hδ_pos, hΔ_pos, hδ_le, hs, hC'_pos, fun i j hnonempty => ?_⟩
  exact isDeltaSSet_mono (hmain i j hnonempty) hC hC'_pos

/-- Monotonicity of IsRegularBetweenScales in both constant parameters. -/
lemma isRegularBetweenScales_mono
    {P : Set (EuclideanSpace ℝ (Fin 2))} {δ Δ t C C' K K' : ℝ}
    (h : IsRegularBetweenScales P δ Δ t C K)
    (hC : C ≤ C') (hC'_pos : 0 < C')
    (hK : K ≤ K') (hK'_pos : 0 < K') :
    IsRegularBetweenScales P δ Δ t C' K' := by
  have hset : IsSetBetweenScales P δ Δ t C := h.1
  have hδ_pos : 0 < δ := hset.1
  have hΔ_pos : 0 < Δ := hset.2.1
  have hratio_pos : 0 < δ / Δ := div_pos hδ_pos hΔ_pos
  have hmain : ∀ (i j : ℤ), (P ∩ CombiningTheorem.dyadicSquare Δ i j).Nonempty →
      (Metric.externalCoveringNumber (Real.sqrt (δ / Δ)).toNNReal
         (CombiningTheorem.homothetyS Δ i j '' (P ∩ CombiningTheorem.dyadicSquare Δ i j)) : ENNReal) ≤
      ENNReal.ofReal (K * Real.rpow (δ / Δ) (-t / 2)) := h.2.2
  refine ⟨isSetBetweenScales_mono hset hC hC'_pos, hK'_pos, fun i j hnonempty => ?_⟩
  have h6 := hmain i j hnonempty
  have h7 : 0 ≤ Real.rpow (δ / Δ) (-t / 2) := Real.rpow_nonneg (by linarith) _
  have h8 : K * Real.rpow (δ / Δ) (-t / 2) ≤ K' * Real.rpow (δ / Δ) (-t / 2) := by
    gcongr
  have h9 : ENNReal.ofReal (K * Real.rpow (δ / Δ) (-t / 2)) ≤
      ENNReal.ofReal (K' * Real.rpow (δ / Δ) (-t / 2)) :=
    ENNReal.ofReal_le_ofReal h8
  exact le_trans h6 h9

end DiscretisedFurstenbergEstimate.CombiningTheoremRework
