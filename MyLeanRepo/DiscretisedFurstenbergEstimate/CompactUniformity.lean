module

/-
  Compact uniformity for the discretised Furstenberg estimate.

  Key insight for local uniformity:
  1. Transfer p → p_SE (southeast): if estimate holds at p with ε, it holds
     at p_SE = (s+a, t-a) with ε/2, provided 2a ≤ ε/2.
  2. Transfer p_SE → p' (northwest): all points near p are northwest of p_SE,
     and the tube exponent upgrade costs δ^{-(s_SE-s')} which fits in ε/2.

  Whiteprint node: final_assembly / compact_uniformity
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DirecretisedFurstenbergEstimate.FinalProof

open DirecretisedFurstenbergEstimate

-- ============================================================================
-- Part 1: distToBoundary
-- ============================================================================

def distToBoundary (p : ℝ × ℝ) : ℝ :=
  min p.1 (min (1 - p.1) (min (p.2 - p.1) (2 - p.2)))

lemma distToBoundary_pos {p : ℝ × ℝ} (hp : p ∈ parameterRange) :
    0 < distToBoundary p := by
  have h1 : 0 < p.1 := hp.1.1
  have h2 : p.1 < 1 := hp.1.2
  have h3 : p.1 < p.2 := hp.2.1
  have h4 : p.2 < 2 := hp.2.2
  dsimp only [distToBoundary]
  positivity

lemma distToBoundary_continuous : Continuous distToBoundary := by
  have h1 : Continuous (fun p : ℝ × ℝ => p.1) := continuous_fst
  have h2 : Continuous (fun p : ℝ × ℝ => 1 - p.1) := by continuity
  have h3 : Continuous (fun p : ℝ × ℝ => p.2 - p.1) := by continuity
  have h4 : Continuous (fun p : ℝ × ℝ => 2 - p.2) := by continuity
  exact h1.min (h2.min (h3.min h4))

lemma distToBoundary_le_s {p : ℝ × ℝ} : distToBoundary p ≤ p.1 := min_le_left _ _
lemma distToBoundary_le_1ms {p : ℝ × ℝ} : distToBoundary p ≤ 1 - p.1 :=
  le_trans (min_le_right _ _) (min_le_left _ _)
lemma distToBoundary_le_ts {p : ℝ × ℝ} : distToBoundary p ≤ p.2 - p.1 :=
  le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
lemma distToBoundary_le_2t {p : ℝ × ℝ} : distToBoundary p ≤ 2 - p.2 :=
  le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))

-- ============================================================================
-- Part 2: IsDeltaSSet helpers
-- ============================================================================

lemma IsDeltaSSet.weaken_C {X : Type*} [PseudoMetricSpace X]
    {δ s C C' : ℝ} {P : Set X}
    (h : IsDeltaSSet δ s C P) (hC : C ≤ C') : IsDeltaSSet δ s C' P := by
  have hC'_pos : 0 < C' := by linarith [h.2.2.1]
  refine ⟨h.1, h.2.1, hC'_pos, h.2.2.2.1, ?_⟩
  intro x r hr
  have h3 := h.2.2.2.2 x r hr
  have h4 : ENNReal.ofReal C ≤ ENNReal.ofReal C' := ENNReal.ofReal_le_ofReal hC
  have h5 : ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) ≤
      ENNReal.ofReal C' * (ENNReal.ofReal r) ^ s * (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by
    gcongr <;> exact h4
  exact le_trans h3 h5

lemma IsDeltaSSet.downgrade_exponent {X : Type*} [PseudoMetricSpace X]
    {δ t t' C : ℝ} {P : Set X}
    (hδ_pos : 0 < δ) (hC_ge_one : 1 ≤ C) (ht_nonneg : 0 ≤ t) (ht_le : t ≤ t')
    (h : IsDeltaSSet δ t' C P) : IsDeltaSSet δ t C P := by
  have hP : P.Nonempty := h.1
  have hδ' : 0 < δ := h.2.1
  have hC_pos : 0 < C := h.2.2.1
  have hmain := h.2.2.2.2
  refine ⟨hP, hδ', hC_pos, ht_nonneg, ?_⟩
  intro x r hr
  by_cases h_r1 : r ≤ 1
  · have h_ennreal_r_le_one : (ENNReal.ofReal r) ≤ 1 := by exact_mod_cast h_r1
    have h_rt : (ENNReal.ofReal r) ^ t' ≤ (ENNReal.ofReal r) ^ t :=
      ENNReal.rpow_le_rpow_of_exponent_ge h_ennreal_r_le_one ht_le
    have h1 := hmain x r hr
    have h_mul : ENNReal.ofReal C * (ENNReal.ofReal r) ^ t' ≤
        ENNReal.ofReal C * (ENNReal.ofReal r) ^ t := by
      exact mul_le_mul_of_nonneg_left h_rt (by positivity)
    exact le_trans h1 (mul_le_mul_of_nonneg_right h_mul (by positivity))
  · have h_r_ge_one : 1 ≤ r := by linarith
    have h5 : (1 : ENNReal) ≤ ENNReal.ofReal r := by
      simpa [ENNReal.one_le_ofReal] using h_r_ge_one
    have h_rt : (1 : ENNReal) ≤ (ENNReal.ofReal r) ^ t := by
      by_cases h_t0 : t = 0
      · rw [h_t0]; simp
      · have h_t_pos : 0 < t := by
          exact lt_of_le_of_ne ht_nonneg (Ne.symm h_t0)
        exact ENNReal.one_le_rpow h5 h_t_pos
    have h6 : (1 : ENNReal) ≤ ENNReal.ofReal C := by
      simpa [ENNReal.one_le_ofReal] using hC_ge_one
    have h4 : (1 : ENNReal) ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ t := by
      calc (1 : ENNReal)
        ≤ ENNReal.ofReal C := h6
      _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ t :=
        le_mul_of_one_le_right (by positivity) h_rt
    have h3 : (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) : ENNReal) ≤
        (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by
      exact_mod_cast Metric.externalCoveringNumber_mono_set (show (P ∩ Metric.closedBall x r) ⊆ P from by simp)
    have h7 : (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) ≤
        ENNReal.ofReal C * (ENNReal.ofReal r) ^ t * (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by
      have h8 : (1 : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) ≤
          ENNReal.ofReal C * (ENNReal.ofReal r) ^ t * (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by
        gcongr <;> exact h4
      simpa using h8
    exact le_trans h3 h7

lemma IsDeltaSSet.upgrade_exponent {X : Type*} [PseudoMetricSpace X]
    {δ s s' C : ℝ} {P : Set X}
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1) (hC_ge_one : 1 ≤ C)
    (hs'_nonneg : 0 ≤ s') (hs_le : s' ≤ s)
    (h : IsDeltaSSet δ s' C P) :
    IsDeltaSSet δ s (C * Real.rpow δ (-(s - s'))) P := by
  set C' : ℝ := C * Real.rpow δ (-(s - s')) with hC'_def
  have hC_pos : 0 < C := h.2.2.1
  have h_rpow_pos : 0 < Real.rpow δ (-(s - s')) := Real.rpow_pos_of_pos hδ_pos _
  have hC'_pos : 0 < C' := mul_pos hC_pos h_rpow_pos
  have hC'_ge_one : 1 ≤ C' := by
    have h1 : 1 ≤ Real.rpow δ (-(s - s')) := by
      have h2 : -(s - s') ≤ 0 := by linarith
      have h3 := Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_lt_one.le h2
      simpa using h3
    have h4 : 1 ≤ C := hC_ge_one
    have h5 : 1 ≤ C * Real.rpow δ (-(s - s')) := by
      calc 1 = 1 * 1 := by ring
        _ ≤ C * Real.rpow δ (-(s - s')) := by gcongr <;> linarith
    exact h5
  have hs_nonneg : 0 ≤ s := by linarith
  have h_ofReal_rpow : ∀ (x : ℝ), 0 ≤ x → ∀ (e : ℝ), 0 ≤ e →
      ENNReal.ofReal (x ^ e) = (ENNReal.ofReal x) ^ e := by
    intro x hx e he
    exact (ENNReal.ofReal_rpow_of_nonneg hx he).symm
  have h_main_goal : ∀ (x : X) (r : ℝ), δ ≤ r →
      (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) : ENNReal) ≤
      ENNReal.ofReal C' * (ENNReal.ofReal r) ^ s * (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by
    intro x r hr
    by_cases h_r1 : r ≤ 1
    · -- r ≤ 1: use real inequality C * r^s' ≤ C' * r^s
      have h_rpos : 0 < r := by linarith [hδ_pos, hr]
      have h_rnonneg : 0 ≤ r := by linarith
      have h_exp_nonpos : s' - s ≤ 0 := by linarith
      have h1 : r ^ (s' - s) ≤ δ ^ (s' - s) :=
        Real.rpow_le_rpow_of_nonpos hδ_pos (by linarith) h_exp_nonpos
      have h2 : r ^ s' = r ^ s * r ^ (s' - s) := by
        have h21 : r ^ s * r ^ (s' - s) = r ^ (s + (s' - s)) := by
          rw [← Real.rpow_add h_rpos]
          <;> ring
        rw [h21] <;> ring_nf
      have h_real_ineq : C * r ^ s' ≤ C' * r ^ s := by
        rw [h2, hC'_def]
        have h4 : r ^ (s' - s) ≤ δ ^ (-(s - s')) := by
          have h5 : s' - s = -(s - s') := by ring
          have h7 : δ ^ (s' - s) = δ ^ (-(s - s')) := by rw [h5]
          rw [h7] at h1
          exact h1
        have h6 : C * (r ^ s * r ^ (s' - s)) ≤
            C * (r ^ s * δ ^ (-(s - s'))) := by
          gcongr
          <;> linarith
        have h7 : C * (r ^ s * δ ^ (-(s - s'))) =
            (C * δ ^ (-(s - s'))) * r ^ s := by ring
        rw [h7] at h6
        exact h6
      have h_ennreal_ineq : ENNReal.ofReal (C * r ^ s') ≤ ENNReal.ofReal (C' * r ^ s) :=
        ENNReal.ofReal_le_ofReal h_real_ineq
      have hC_nonneg : 0 ≤ C := by linarith
      have hC'_nonneg : 0 ≤ C' := by linarith
      have hrp_nonneg : 0 ≤ r ^ s' := by positivity
      have hr_nonneg2 : 0 ≤ r ^ s := by positivity
      have h_mul1 : ENNReal.ofReal (C * r ^ s') =
          ENNReal.ofReal C * ENNReal.ofReal (r ^ s') :=
        ENNReal.ofReal_mul hC_nonneg
      have h_mul2 : ENNReal.ofReal (C' * r ^ s) =
          ENNReal.ofReal C' * ENNReal.ofReal (r ^ s) :=
        ENNReal.ofReal_mul hC'_nonneg
      have h_left : ENNReal.ofReal (C * r ^ s') =
          ENNReal.ofReal C * (ENNReal.ofReal r) ^ s' := by
        rw [h_mul1, h_ofReal_rpow r h_rnonneg s' hs'_nonneg]
      have h_right : ENNReal.ofReal (C' * r ^ s) =
          ENNReal.ofReal C' * (ENNReal.ofReal r) ^ s := by
        rw [h_mul2, h_ofReal_rpow r h_rnonneg s hs_nonneg]
      have h_key : ENNReal.ofReal C * (ENNReal.ofReal r) ^ s' ≤
          ENNReal.ofReal C' * (ENNReal.ofReal r) ^ s := by
        rw [← h_left, ← h_right]; exact h_ennreal_ineq
      have h1' := h.2.2.2.2 x r hr
      calc (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) : ENNReal)
        ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s' * (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := h1'
      _ ≤ ENNReal.ofReal C' * (ENNReal.ofReal r) ^ s * (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by
        exact mul_le_mul_of_nonneg_right h_key (by positivity)
    · -- r > 1: bound automatic since C' ≥ 1 and r^s ≥ 1
      have h_r_ge_one : 1 ≤ r := by linarith
      have h_rnonneg : 0 ≤ r := by linarith
      have h5 : (1 : ENNReal) ≤ ENNReal.ofReal r := by
        simpa [ENNReal.one_le_ofReal] using h_r_ge_one
      have h_rt : (1 : ENNReal) ≤ (ENNReal.ofReal r) ^ s := by
        by_cases h_s0 : s = 0
        · rw [h_s0]; simp
        · have h_s_pos : 0 < s := by
            exact lt_of_le_of_ne hs_nonneg (Ne.symm h_s0)
          exact ENNReal.one_le_rpow h5 h_s_pos
      have h6 : (1 : ENNReal) ≤ ENNReal.ofReal C' := by
        simpa [ENNReal.one_le_ofReal] using hC'_ge_one
      have h4 : (1 : ENNReal) ≤ ENNReal.ofReal C' * (ENNReal.ofReal r) ^ s := by
        calc (1 : ENNReal)
          ≤ ENNReal.ofReal C' := h6
        _ ≤ ENNReal.ofReal C' * (ENNReal.ofReal r) ^ s :=
          le_mul_of_one_le_right (by positivity) h_rt
      have h3 : (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) : ENNReal) ≤
          (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by
        exact_mod_cast Metric.externalCoveringNumber_mono_set (show (P ∩ Metric.closedBall x r) ⊆ P from by simp)
      have h7 : (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) ≤
          ENNReal.ofReal C' * (ENNReal.ofReal r) ^ s * (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by
        have h8 : (1 : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) ≤
            ENNReal.ofReal C' * (ENNReal.ofReal r) ^ s * (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) :=
          mul_le_mul_of_nonneg_right h4 (by positivity)
        simpa using h8
      exact le_trans h3 h7
  exact ⟨h.1, h.2.1, hC'_pos, hs_nonneg, h_main_goal⟩

-- ============================================================================
-- Part 3: CoreEstimateHolds and weakening
-- ============================================================================

def CoreEstimateHolds (s t ε : ℝ) : Prop :=
  0 < ε ∧ ∃ (δ₀ : ℝ), 0 < δ₀ ∧
    ∀ (δ : ℝ), δ ∈ Set.Ioc (0 : ℝ) δ₀ →
      ∀ (X : Set EuclideanPlane),
        X ⊆ Metric.closedBall 0 1 →
          IsDeltaSSet δ t (Real.rpow δ (-ε)) X →
          ∀ (𝓣 : ∀ (x : EuclideanPlane), x ∈ X → Set AffineLine),
            (∀ x hx, IsDeltaSSet δ s (Real.rpow δ (-ε)) (𝓣 x hx)) →
            (∀ x hx, ∀ ℓ ∈ 𝓣 x hx, x ∈ Metric.cthickening δ ℓ.1) →
            (Metric.externalCoveringNumber δ.toNNReal
               (⋃ (x : EuclideanPlane) (hx : x ∈ X), 𝓣 x hx) : ENNReal) ≥
              ENNReal.ofReal (Real.rpow δ (-(2 * s + ε)))

lemma core_estimate_weaken_ε {s t ε ε' : ℝ} (hε'_pos : 0 < ε') (hε'_le : ε' ≤ ε)
    (h : CoreEstimateHolds s t ε) : CoreEstimateHolds s t ε' := by
  rcases h with ⟨_, δ₀, hδ₀_pos, h_main⟩
  let δ₀' := min δ₀ (1 / 2)
  have hδ₀'_pos : 0 < δ₀' := by positivity
  have hδ₀'_le : δ₀' ≤ δ₀ := min_le_left _ _
  refine ⟨hε'_pos, δ₀', hδ₀'_pos, ?_⟩
  intro δ hδ X hX_bounded hX_sset 𝓣 h𝓣_sset h𝓣_near
  have hδ_pos : 0 < δ := hδ.1
  have hδ_lt_one : δ < 1 := by
    have h5 : δ ≤ δ₀' := hδ.2
    have h6 : δ₀' ≤ 1 / 2 := min_le_right _ _
    linarith
  have hC_le : Real.rpow δ (-ε') ≤ Real.rpow δ (-ε) :=
    Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_lt_one.le (show -ε ≤ -ε' from by linarith)
  have hX_sset' : IsDeltaSSet δ t (Real.rpow δ (-ε)) X :=
    IsDeltaSSet.weaken_C hX_sset hC_le
  have h𝓣_sset' : ∀ x hx, IsDeltaSSet δ s (Real.rpow δ (-ε)) (𝓣 x hx) := by
    intro x hx
    exact IsDeltaSSet.weaken_C (h𝓣_sset x hx) hC_le
  have hδ_orig : δ ∈ Set.Ioc (0 : ℝ) δ₀ := ⟨hδ.1, le_trans hδ.2 hδ₀'_le⟩
  have h_result := h_main δ hδ_orig X hX_bounded hX_sset' 𝓣 h𝓣_sset' h𝓣_near
  have h_exp : -(2 * s + ε) ≤ -(2 * s + ε') := by linarith
  have h_rpow : Real.rpow δ (-(2 * s + ε')) ≤ Real.rpow δ (-(2 * s + ε)) :=
    Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_lt_one.le h_exp
  exact le_trans (ENNReal.ofReal_le_ofReal h_rpow) h_result

-- ============================================================================
-- Part 4: Southeast transfer: p → p_SE = (s+a, t-a)
-- If estimate holds at (s,t) with ε, it holds at (s+a, t-a) with ε/2
-- provided 2a ≤ ε/2 and p_SE ∈ parameterRange.
-- ============================================================================

lemma core_estimate_transfer_se {s t ε a : ℝ}
    (hε_pos : 0 < ε) (hs_pos : 0 < s) (ha_nonneg : 0 ≤ a) (h2a : 2 * a ≤ ε / 2)
    (h_dom_in_range : (s + a, t - a) ∈ parameterRange)
    (h : CoreEstimateHolds s t ε) : CoreEstimateHolds (s + a) (t - a) (ε / 2) := by
  set ε_SE : ℝ := ε / 2 with hε_SE_def
  have hε_SE_pos : 0 < ε_SE := by linarith
  rcases h with ⟨_, δ₀, hδ₀_pos, h_main⟩
  let δ₀' := min δ₀ (1 / 2)
  have hδ₀'_pos : 0 < δ₀' := by positivity
  have hδ₀'_le : δ₀' ≤ δ₀ := min_le_left _ _
  refine ⟨hε_SE_pos, δ₀', hδ₀'_pos, ?_⟩
  intro δ hδ X hX_bounded hX_sset 𝓣 h𝓣_sset h𝓣_near
  have hδ_pos : 0 < δ := hδ.1
  have hδ_lt_one : δ < 1 := by
    have h5 : δ ≤ δ₀' := hδ.2
    have h6 : δ₀' ≤ 1 / 2 := min_le_right _ _
    linarith
  have hC_SE_ge_one : 1 ≤ Real.rpow δ (-ε_SE) := by
    have h7 : -ε_SE ≤ 0 := by linarith
    have h8 := Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_lt_one.le h7
    simpa using h8
  -- Upgrade X from (t-a) to t: constant δ^{-ε_SE} * δ^{-a} = δ^{-(ε_SE + a)}
  have h_sum1 : ε_SE + a ≤ ε := by linarith
  have h_upgraded_X_const : Real.rpow δ (-(ε_SE + a)) ≤ Real.rpow δ (-ε) :=
    Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_lt_one.le (by linarith)
  have hX_upgraded : IsDeltaSSet δ t (Real.rpow δ (-ε)) X := by
    have h15 : 0 ≤ t - a := by
      have h151 : 0 < s + a := h_dom_in_range.1.1
      have h152 : s + a < t - a := h_dom_in_range.2.1
      linarith
    have h16 : IsDeltaSSet δ (t - a) (Real.rpow δ (-ε_SE)) X := hX_sset
    have h17_raw : IsDeltaSSet δ t (Real.rpow δ (-ε_SE) * Real.rpow δ (-a)) X := by
      have h_diff : t - (t - a) = a := by ring
      have h_goal := IsDeltaSSet.upgrade_exponent hδ_pos hδ_lt_one hC_SE_ge_one h15 (show t - a ≤ t from by linarith) h16
      simpa [h_diff] using h_goal
    have h_eq : Real.rpow δ (-ε_SE) * Real.rpow δ (-a) = Real.rpow δ (-(ε_SE + a)) := by
      have h_rpow : Real.rpow δ (-ε_SE + -a) = Real.rpow δ (-ε_SE) * Real.rpow δ (-a) :=
        Real.rpow_add hδ_pos (-ε_SE) (-a)
      have h_sum : -ε_SE + -a = -(ε_SE + a) := by ring
      rw [h_sum] at h_rpow
      exact h_rpow.symm
    have h17 : IsDeltaSSet δ t (Real.rpow δ (-(ε_SE + a))) X := by
      rw [h_eq] at h17_raw
      exact h17_raw
    exact IsDeltaSSet.weaken_C h17 h_upgraded_X_const
  -- Downgrade tubes from (s+a) to s: free, then weaken constant
  have h_sum2 : ε_SE ≤ ε := by linarith
  have h_tube_const : Real.rpow δ (-ε_SE) ≤ Real.rpow δ (-ε) :=
    Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_lt_one.le (by linarith)
  have h𝓣_downgraded : ∀ x hx, IsDeltaSSet δ s (Real.rpow δ (-ε)) (𝓣 x hx) := by
    intro x hx
    have h19 : 0 ≤ s := by linarith
    have h20 : IsDeltaSSet δ (s + a) (Real.rpow δ (-ε_SE)) (𝓣 x hx) := h𝓣_sset x hx
    have h21 : IsDeltaSSet δ s (Real.rpow δ (-ε_SE)) (𝓣 x hx) :=
      IsDeltaSSet.downgrade_exponent hδ_pos hC_SE_ge_one h19 (by linarith) h20
    exact IsDeltaSSet.weaken_C h21 h_tube_const
  have hδ_orig : δ ∈ Set.Ioc (0 : ℝ) δ₀ := ⟨hδ.1, le_trans hδ.2 hδ₀'_le⟩
  have h_result := h_main δ hδ_orig X hX_bounded hX_upgraded 𝓣 h𝓣_downgraded h𝓣_near
  -- Conclusion: need δ^{-2(s+a)-ε_SE}, have δ^{-2s-ε}
  -- Need -2(s+a)-ε_SE ≥ -2s-ε, i.e., 2a + ε_SE ≤ ε
  have h_concl : 2 * a + ε_SE ≤ ε := by linarith
  have h_exp : -(2 * s + ε) ≤ -(2 * (s + a) + ε_SE) := by linarith
  have h_rpow : Real.rpow δ (-(2 * (s + a) + ε_SE)) ≤ Real.rpow δ (-(2 * s + ε)) :=
    Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_lt_one.le h_exp
  exact le_trans (ENNReal.ofReal_le_ofReal h_rpow) h_result

-- ============================================================================
-- Part 5: Local uniformity
-- ============================================================================

lemma local_uniformity (s t : ℝ) (hp : (s, t) ∈ parameterRange)
    (h_core : ∀ (s t : ℝ), (s, t) ∈ parameterRange →
      ∃ (ε δ₀ : ℝ), 0 < ε ∧ 0 < δ₀ ∧ CoreEstimateHolds s t ε) :
    ∃ (r ε_local : ℝ), 0 < r ∧ 0 < ε_local ∧
      ∀ (p : ℝ × ℝ), p ∈ Metric.ball (s, t) r → p ∈ parameterRange →
        CoreEstimateHolds p.1 p.2 ε_local := by
  have h1 : 0 < s := hp.1.1
  have h2 : s < 1 := hp.1.2
  have h3 : s < t := hp.2.1
  have h4 : t < 2 := hp.2.2
  set d : ℝ := distToBoundary (s, t) with hd_def
  have hd_pos : 0 < d := distToBoundary_pos hp
  have hd_le_s : d ≤ s := distToBoundary_le_s (p := (s, t))
  have hd_le_1ms : d ≤ 1 - s := distToBoundary_le_1ms (p := (s, t))
  have hd_le_ts : d ≤ t - s := distToBoundary_le_ts (p := (s, t))
  have hd_le_2t : d ≤ 2 - t := distToBoundary_le_2t (p := (s, t))
  rcases h_core s t hp with ⟨ε, δ₀, hε_pos, hδ₀_pos, h_holds⟩
  set a : ℝ := min (d / 3) (ε / 8) with ha_def
  have ha_pos : 0 < a := by positivity
  have ha_le_d3 : a ≤ d / 3 := min_le_left _ _
  have ha_le_ep8 : a ≤ ε / 8 := min_le_right _ _
  have h2a : 2 * a ≤ ε / 2 := by linarith
  set s_SE : ℝ := s + a with hs_SE_def
  set t_SE : ℝ := t - a with ht_SE_def
  have h_SE_in_range : (s_SE, t_SE) ∈ parameterRange := by
    simp only [parameterRange, Set.mem_setOf_eq]
    have h_s1 : 0 < s_SE := by linarith
    have h_s2 : s_SE < 1 := by linarith
    have h_s3 : s_SE < t_SE := by linarith [ha_le_d3, hd_le_ts]
    have h_s4 : t_SE < 2 := by linarith
    exact ⟨⟨h_s1, h_s2⟩, ⟨h_s3, h_s4⟩⟩
  have h_holds_SE : CoreEstimateHolds s_SE t_SE (ε / 2) :=
    core_estimate_transfer_se hε_pos h1 (by linarith) h2a h_SE_in_range h_holds
  set r : ℝ := min (a / 2) (ε / 8) with hr_def
  have hr_pos : 0 < r := by positivity
  have hr_le_a2 : r ≤ a / 2 := min_le_left _ _
  have hr_le_ep8 : r ≤ ε / 8 := min_le_right _ _
  set ε_local : ℝ := ε / 4 with hε_local_def
  have hε_local_pos : 0 < ε_local := by linarith
  refine ⟨r, ε_local, hr_pos, hε_local_pos, ?_⟩
  intro p hball hp'
  set s' := p.1 with hs'_def
  set t' := p.2 with ht'_def
  have h_dist : dist p (s, t) < r := hball
  have h_dist_eq : dist p (s, t) = max (|s' - s|) (|t' - t|) := by
    rw [Prod.dist_eq] <;> rfl
  have h_s'_diff : |s' - s| ≤ dist p (s, t) := by
    rw [h_dist_eq]; exact le_max_left _ _
  have h_t'_diff : |t' - t| ≤ dist p (s, t) := by
    rw [h_dist_eq]; exact le_max_right _ _
  have h_s'_lt : s' < s + r := by
    have h : |s' - s| < r := by linarith
    have h' : s' - s < r := (abs_lt.mp h).2
    linarith
  have h_s'_gt : s - r < s' := by
    have h : |s' - s| < r := by linarith
    have h' : -(r) < s' - s := (abs_lt.mp h).1
    linarith
  have h_t'_gt : t - r < t' := by
    have h : |t' - t| < r := by linarith
    have h' : -(r) < t' - t := (abs_lt.mp h).1
    linarith
  have h_s'_le_SE : s' ≤ s_SE := by
    dsimp only [s_SE]; linarith [hr_le_a2]
  have h_t'_ge_SE : t_SE ≤ t' := by
    dsimp only [t_SE]; linarith [hr_le_a2]
  have h_gap : s_SE - s' < ε / 2 := by
    dsimp only [s_SE]
    have h : s_SE - s' < a + r := by linarith
    have h2 : a + r ≤ ε / 8 + ε / 8 := by linarith [ha_le_ep8, hr_le_ep8]
    linarith
  have h1' : 0 < s' := hp'.1.1
  have h_sum : ε_local + (s_SE - s') < ε / 2 := by
    dsimp only [ε_local]
    linarith [h_gap]
  have h_sum_le : ε_local + (s_SE - s') ≤ ε / 2 := by linarith
  rcases h_holds_SE with ⟨_, δ₀_SE, hδ₀_SE_pos, h_main_SE⟩
  let δ₀' := min δ₀_SE (1 / 2)
  have hδ₀'_pos : 0 < δ₀' := by positivity
  have hδ₀'_le : δ₀' ≤ δ₀_SE := min_le_left _ _
  refine ⟨hε_local_pos, δ₀', hδ₀'_pos, ?_⟩
  intro δ hδ X hX_bounded hX_sset 𝓣 h𝓣_sset h𝓣_near
  have hδ_pos : 0 < δ := hδ.1
  have hδ_lt_one : δ < 1 := by
    have h5 : δ ≤ δ₀' := hδ.2
    have h6 : δ₀' ≤ 1 / 2 := min_le_right _ _
    linarith
  have hC_local_ge_one : 1 ≤ Real.rpow δ (-ε_local) := by
    have h7 : -ε_local ≤ 0 := by linarith
    have h8 := Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_lt_one.le h7
    simpa using h8
  have h_upgraded_const_le : Real.rpow δ (-(ε_local + (s_SE - s'))) ≤ Real.rpow δ (-(ε / 2)) :=
    Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_lt_one.le (by linarith)
  have h𝓣_upgraded : ∀ x hx, IsDeltaSSet δ s_SE (Real.rpow δ (-(ε / 2))) (𝓣 x hx) := by
    intro x hx
    have h11 : IsDeltaSSet δ s' (Real.rpow δ (-ε_local)) (𝓣 x hx) := h𝓣_sset x hx
    have h12 : IsDeltaSSet δ s_SE
        (Real.rpow δ (-ε_local) * Real.rpow δ (-(s_SE - s'))) (𝓣 x hx) :=
      IsDeltaSSet.upgrade_exponent hδ_pos hδ_lt_one hC_local_ge_one h1'.le h_s'_le_SE h11
    have h13 : Real.rpow δ (-ε_local) * Real.rpow δ (-(s_SE - s')) =
        Real.rpow δ (-ε_local + -(s_SE - s')) := by
      have h_rpow := Real.rpow_add hδ_pos (-ε_local) (-(s_SE - s'))
      exact h_rpow.symm
    have h14 : -ε_local + -(s_SE - s') = -(ε_local + (s_SE - s')) := by ring
    rw [h13, h14] at h12
    exact IsDeltaSSet.weaken_C h12 h_upgraded_const_le
  have h14 : 0 ≤ t_SE := by linarith
  have hX_downgraded : IsDeltaSSet δ t_SE (Real.rpow δ (-(ε / 2))) X := by
    have h15 : IsDeltaSSet δ t' (Real.rpow δ (-ε_local)) X := hX_sset
    have h16 : IsDeltaSSet δ t_SE (Real.rpow δ (-ε_local)) X :=
      IsDeltaSSet.downgrade_exponent hδ_pos hC_local_ge_one h14 h_t'_ge_SE h15
    have h17 : Real.rpow δ (-ε_local) ≤ Real.rpow δ (-(ε / 2)) :=
      Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_lt_one.le (by linarith)
    exact IsDeltaSSet.weaken_C h16 h17
  have hδ_orig : δ ∈ Set.Ioc (0 : ℝ) δ₀_SE := ⟨hδ.1, le_trans hδ.2 hδ₀'_le⟩
  have h_result := h_main_SE δ hδ_orig X hX_bounded hX_downgraded 𝓣 h𝓣_upgraded h𝓣_near
  have h_exp : -(2 * s_SE + (ε / 2)) ≤ -(2 * s' + ε_local) := by linarith
  have h_rpow : Real.rpow δ (-(2 * s' + ε_local)) ≤ Real.rpow δ (-(2 * s_SE + (ε / 2))) :=
    Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_lt_one.le h_exp
  exact le_trans (ENNReal.ofReal_le_ofReal h_rpow) h_result

-- ============================================================================
-- Part 6: Compact uniformity via finite subcover
-- ============================================================================

lemma compact_uniformity_from_core
    (h_core : ∀ (s t : ℝ), (s, t) ∈ parameterRange →
      ∃ (ε δ₀ : ℝ), 0 < ε ∧ 0 < δ₀ ∧ CoreEstimateHolds s t ε)
    {A : Set (ℝ × ℝ)} (hA : IsCompact A) (hA_sub : A ⊆ parameterRange) :
    ∃ (ε₀ : ℝ), 0 < ε₀ ∧ ∀ (p : ℝ × ℝ), p ∈ A → CoreEstimateHolds p.1 p.2 ε₀ := by
  by_cases hA_empty : A = ∅
  · refine ⟨1, by norm_num, fun p hp => by rw [hA_empty] at hp <;> simp at hp⟩
  · have hA_nonempty : A.Nonempty := Set.nonempty_iff_ne_empty.mpr hA_empty
    have h1 : ∀ (x : ℝ × ℝ), x ∈ A → ∃ (r ε_x : ℝ), 0 < r ∧ 0 < ε_x ∧
        ∀ (y : ℝ × ℝ), y ∈ Metric.ball x r → y ∈ parameterRange →
          CoreEstimateHolds y.1 y.2 ε_x := by
      intro x hx
      exact local_uniformity x.1 x.2 (hA_sub hx) h_core
    choose r ε_x hr_pos hε_x_pos h_local using h1
    let ι := {x : ℝ × ℝ // x ∈ A}
    let U (i : ι) : Set (ℝ × ℝ) := Metric.ball (i : ℝ × ℝ) (r i i.prop / 2)
    have hU_open : ∀ (i : ι), IsOpen (U i) := fun i => Metric.isOpen_ball
    have hcover : A ⊆ ⋃ (i : ι), U i := by
      intro y hy
      let i : ι := ⟨y, hy⟩
      have h2 : y ∈ U i := by
        dsimp only [U]
        have h3 : dist y y < r y hy / 2 := by
          simp [hr_pos y hy] <;> linarith
        exact h3
      exact Set.mem_iUnion.mpr ⟨i, h2⟩
    have h_main : ∃ (s : Finset ι), A ⊆ ⋃ i ∈ s, U i :=
      hA.elim_finite_subcover U hU_open hcover
    rcases h_main with ⟨s, hcover_s⟩
    have h4 : s.Nonempty := by
      by_contra h5
      have h6 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp h5
      rw [h6] at hcover_s
      have h7 : A = ∅ := by simpa using hcover_s
      exact hA_empty h7
    let εs : Finset ℝ := Finset.image (fun i : ι => ε_x i i.prop) s
    have hεs_nonempty : εs.Nonempty := Finset.image_nonempty.mpr h4
    let ε₀ : ℝ := εs.min' hεs_nonempty
    have hε₀_mem : ε₀ ∈ εs := εs.min'_mem hεs_nonempty
    have hε₀_pos : 0 < ε₀ := by
      rcases Finset.mem_image.mp hε₀_mem with ⟨i, hi_s, h_eq⟩
      rw [← h_eq]
      exact hε_x_pos i i.prop
    have hε₀_le : ∀ i ∈ s, ε₀ ≤ ε_x i i.prop := by
      intro i hi
      have h_in : ε_x i i.prop ∈ εs := Finset.mem_image.mpr ⟨i, hi, rfl⟩
      exact εs.min'_le (ε_x i i.prop) h_in
    refine ⟨ε₀, hε₀_pos, ?_⟩
    intro p hpA
    have h5 : p ∈ ⋃ i ∈ s, U i := hcover_s hpA
    have h5' : ∃ (i : ι), i ∈ s ∧ p ∈ U i := by
      simpa using h5
    rcases h5' with ⟨i, hi_s, h_i_ball⟩
    have h6 : p ∈ Metric.ball (i : ℝ × ℝ) (r i i.prop) := by
      dsimp only [U] at h_i_ball
      have h7 : dist p (i : ℝ × ℝ) < r i i.prop / 2 := h_i_ball
      have h8 : 0 < r i i.prop := hr_pos i i.prop
      have h9 : dist p (i : ℝ × ℝ) < r i i.prop := by linarith
      exact h9
    have h8 : CoreEstimateHolds p.1 p.2 (ε_x i i.prop) :=
      h_local i i.prop p h6 (hA_sub hpA)
    have h9 : ε₀ ≤ ε_x i i.prop := hε₀_le i hi_s
    exact core_estimate_weaken_ε hε₀_pos h9 h8

end DirecretisedFurstenbergEstimate.FinalProof
