module

/-
  FineCor25Data from fixed K — correct quantifier order.

  K is chosen at the OUTER theorem level (from uniform_prop5), before any
  incidence data. This lemma takes the fixed K and its spec, applies
  uniform_prop5_wrapper_with_K to the fine B1 config, and combines with
  the explicit scale conversion to produce FineCor25Data directly.

  The threshold δ₀ from fine_ratio_explicit_uniform is computed at the
  outer level and included in δR; hδ_small is the hypothesis that the
  current scale satisfies it.

  Whiteprint node: section6 / fine_cor25_from_fixed_K
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Section6.B1InductionDataType
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Section6.CleanSSetConversion
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Section6.CleanB1Geometry
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Section6.CleanLocalFineSSet
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.UniformProp5Wrapper
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Section6.FineRatioExplicit
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Section6.Types
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DirecretisedFurstenbergEstimate.Section6

open DiscretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.CombiningTheorem
open DiscretisedFurstenbergEstimate.CombiningTheoremRework
open DiscretisedFurstenbergEstimate.DyadicConversion

/-- Monotonicity of IsDeltaSSet in the constant C. -/
lemma isDeltaSSet_mono_const {X : Type*} [PseudoMetricSpace X] {δ s C C' : ℝ} {P : Set X}
    (h : IsDeltaSSet δ s C P) (hC : C ≤ C') (hC'_pos : 0 < C') :
    IsDeltaSSet δ s C' P := by
  rcases h with ⟨hne, hδ_pos, _, hs_nonneg, h_bound⟩
  refine' ⟨hne, hδ_pos, hC'_pos, hs_nonneg, _⟩
  intro x r hr
  have h1 := h_bound x r hr
  have h2 : ENNReal.ofReal C ≤ ENNReal.ofReal C' := ENNReal.ofReal_le_ofReal hC
  have h_goal : Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) ≤
      ENNReal.ofReal C' * (ENNReal.ofReal r) ^ s * Metric.externalCoveringNumber δ.toNNReal P := by
    calc Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r)
      ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * Metric.externalCoveringNumber δ.toNNReal P := h1
    _ ≤ ENNReal.ofReal C' * (ENNReal.ofReal r) ^ s * Metric.externalCoveringNumber δ.toNNReal P := by
      gcongr
      <;> exact h2
  exact h_goal

/-- Produce FineCor25Data using a fixed K chosen at the outer level.

    K and hK_spec come from uniform_prop5 at the outer theorem level.
    hδ_small is the scale condition (δ_n ≤ δ₀), where δ₀ was computed
    at the outer level using fine_ratio_explicit_uniform with this K.

    Generalized to accept an arbitrary exponent `u` for the input point-set
    S-set, with `s ≤ u`. The S-set is then weakened to exponent `s` via
    `fine_pointset_sset_to_finset_sset`. The parameter `t` is retained
    only for the `B1InductionData` type.

    Returns FineCor25Data directly — no threshold in the return type. -/
def fine_cor25_from_fixed_K
    {n m : ℕ} {hnm : m ≤ n}
    {s t u C₁ : ℝ} {M : ℕ}
    {config : CombiningTheorem.NiceConfiguration n s C₁ M}
    -- Fixed K from outer level
    (K : ℝ) (hK_pos : 0 < K)
    -- hK_spec specialized to fine scale (n-m) and exponent s
    (hK_spec : ∀ (C_P C_T M : ℝ), 0 < C_P → 1 ≤ C_P → 0 < C_T → 1 ≤ C_T → 1 ≤ M → 2 ≤ n - m →
      ∀ (P : Finset (DSquare (n - m))), P.Nonempty →
        IsFinsetDeltaSSet (δ (n - m)) s C_P P →
        (∀ (x y : DSquare (n - m)), x ∈ P → y ∈ P → dist x y ≤ 3) →
        (∀ p ∈ P, ∀ (x : ℝ × ℝ), x ∈ p.toSet → |x.1| ≤ 1) →
        ∀ (Tp : TubeFamily (n - m)),
          (∀ p ∈ P, ∀ T ∈ Tp p, (T.toSet ∩ p.toSet).Nonempty) →
          (∀ p ∈ P, ∀ T ∈ Tp p, |T.slope| ≤ 1) →
          (∀ p ∈ P, IsFinsetDeltaSSet (δ (n - m)) s C_T (Tp p)) →
          (∀ p ∈ P, M / 2 < (Tp p).card ∧ (Tp p).card ≤ M) →
            let T := P.biUnion fun p => Tp p
            (T.card : ℝ) ≥ (1 / K) * Real.log (1 / δ (n - m)) ^ (-K) *
              (1 / (C_P * C_T)) * M * (δ (n - m)) ^ (-s) *
                (M * (δ (n - m)) ^ s) ^ ((s - s) / (1 - s)))
    -- B1 data
    (data : B1InductionData n m hnm s t C₁ M config)
    (Q : DiscretisedFurstenbergEstimate.DyadicSquare m)
    (hQ : Q ∈ data.coarseConfig.P₀)
    (hs_pos : 0 < s) (hs_lt_one : s < 1) (hs_u : s ≤ u)
    {C_ret : ℝ}
    (h_ret_sset : IsDeltaSSet (δd (n - m)) u C_ret
      (data.fineConfig Q hQ).pointSet)
    (hnm_ge2 : 2 ≤ n - m)
    (hP_nonempty : (data.fineConfig Q hQ).P₀.Nonempty)
    -- Explicit power bounds
    {a b polylogLoss : ℝ} (ha_nonneg : 0 ≤ a) (hb_nonneg : 0 ≤ b)
    (hpolylogLoss_pos : 0 < polylogLoss)
    (hC_ret_bound : C_ret ≤ (δd n) ^ (-a))
    (hC_Q_bound : max (data.CQ Q) 1 ≤ (δd n) ^ (-b))
    -- Even scale
    (h_even : n = 2 * m)
    -- Scale conversion (proved at outer level using fine_ratio_explicit_uniform + threshold)
    (h_convert : (1 / K) * Real.log (1 / δd (n - m)) ^ (-K) *
        (1 / ((81 * max C_ret 1 * (2 * Real.sqrt 2) ^ s) *
          (13 * max (data.CQ Q) 1 * Real.rpow 2 s))) *
        (δd (n - m)) ^ (-s) ≥
      (δd n) ^ (-(s / 2 - (a + b + polylogLoss)))) :
    FineCor25Data (δd n) s := by
  let fineCfg := data.fineConfig Q hQ
  let δ' := δd (n - m)
  let δ := δd n
  let C_Q : ℝ := max (data.CQ Q) 1
  let NQ : ℝ := (fineCfg.T₀.card : ℝ)
  let MQ : ℝ := (data.MQ Q : ℝ)
  let C_P : ℝ := 81 * max C_ret 1 * (2 * Real.sqrt 2) ^ s

  have hMQ_pos : 0 < MQ := Nat.cast_pos.mpr (data.hMQ Q hQ)
  have hC_ret_pos : 0 < C_ret := h_ret_sset.2.2.1
  have hCQ_pos : 0 < C_Q := by
    have h1 : 0 < (1 : ℝ) := by norm_num
    exact lt_max_of_lt_right h1
  have hCQ_ge1 : 1 ≤ C_Q := le_max_right (data.CQ Q) 1
  have hCQ_le : data.CQ Q ≤ C_Q := le_max_left (data.CQ Q) 1

  -- Weaken fineCfg to have constant C_Q = max(data.CQ Q, 1)
  -- IsDeltaSSet is monotone in the constant C.
  let fineCfg' : CombiningTheorem.NiceConfiguration (n - m) s C_Q (data.MQ Q) :=
    { P₀ := fineCfg.P₀
      T₀ := fineCfg.T₀
      tubeFamily := fineCfg.tubeFamily
      h_subset := fineCfg.h_subset
      h_size := fineCfg.h_size
      h_delta_s_set := fun p hp => isDeltaSSet_mono_const (fineCfg.h_delta_s_set p hp) hCQ_le hCQ_pos
      h_intersect := fineCfg.h_intersect
      h_tube_parameters := fineCfg.h_tube_parameters
      h_bounded := fineCfg.h_bounded }

  have hCP_pos : 0 < C_P := by positivity
  have hCP_ge1 : 1 ≤ C_P := by
    have h1 : 0 ≤ s := by linarith
    have h2 : 1 ≤ (2 * Real.sqrt 2) ^ s := by
      have h3 : 1 ≤ (2 * Real.sqrt 2) := by
        have h4 : 1 ≤ Real.sqrt 2 := by
          have h5 : (1 : ℝ) ^ 2 ≤ 2 := by norm_num
          exact Real.le_sqrt_of_sq_le h5
        linarith
      exact Real.one_le_rpow h3 h1
    have h4 : 1 ≤ max C_ret 1 := le_max_right C_ret 1
    have h5 : 1 ≤ (81 : ℝ) := by norm_num
    have h6 : 1 ≤ (81 : ℝ) * max C_ret 1 := by
      calc 1
        = (1 : ℝ) * (1 : ℝ) := by ring
      _ ≤ (81 : ℝ) * max C_ret 1 := by gcongr <;> linarith
    have h7 : 1 ≤ (81 : ℝ) * max C_ret 1 * (2 * Real.sqrt 2) ^ s := by
      calc 1
        = 1 * 1 := by ring
      _ ≤ ((81 : ℝ) * max C_ret 1) * (2 * Real.sqrt 2) ^ s := by gcongr <;> linarith
    exact h7

  have hP_set : IsFinsetDeltaSSet (δd (n - m)) s C_P
      (finsetDyadicToDSquare fineCfg.P₀) :=
    fine_pointset_sset_to_finset_sset
      fineCfg.P₀ hP_nonempty fineCfg.pointSet rfl h_ret_sset (by linarith) hs_u

  let hB1_fine := data.fineConfig_B1 Q hQ
  have h_slope : ∀ T ∈ fineCfg.T₀, |T.slope| ≤ 1 := b1_geometry_slope hB1_fine
  have h_diam : ∀ (p q : DSquare (n - m)),
      p ∈ finsetDyadicToDSquare fineCfg.P₀ →
      q ∈ finsetDyadicToDSquare fineCfg.P₀ → dist p q ≤ 3 :=
    b1_geometry_diam hB1_fine
  have h_unit : ∀ (p : DSquare (n - m)),
      p ∈ finsetDyadicToDSquare fineCfg.P₀ →
      ∀ (x : ℝ × ℝ), x ∈ p.toSet → |x.1| ≤ 1 :=
    b1_geometry_unit hB1_fine

  -- Apply fixed-K Prop 5.1 wrapper
  have h_bound : NQ ≥ (1 / K) * Real.log (1 / δ') ^ (-K) *
      (1 / (C_P * (13 * C_Q * Real.rpow 2 s))) * MQ * δ' ^ (-s) := by
    have h_main := uniform_prop5_wrapper_with_K (hK_pos := hK_pos) (hK_spec := hK_spec)
      fineCfg' hnm_ge2 (data.hMQ Q hQ) hP_nonempty
      hCP_pos hCP_ge1 hCQ_pos hCQ_ge1 (by linarith) hP_set h_slope h_diam h_unit
    have h_exp : (s - s) / (1 - s) = 0 := by
      have h1 : 1 - s > 0 := by linarith
      field_simp [h1.ne'] <;> ring
    have h_last : (MQ * δ' ^ s) ^ ((s - s) / (1 - s)) = 1 := by
      rw [h_exp]; exact Real.rpow_zero _
    have h_main' : NQ ≥ (1 / K) * Real.log (1 / δ') ^ (-K) *
        (1 / (C_P * (13 * C_Q * Real.rpow 2 s))) * MQ * δ' ^ (-s) *
        (MQ * δ' ^ s) ^ ((s - s) / (1 - s)) := by
      convert h_main using 1
      · rfl
    rw [h_last] at h_main'
    simpa using h_main'

  have h_ratio : NQ / MQ ≥ (1 / K) * Real.log (1 / δ') ^ (-K) *
      (1 / (C_P * (13 * C_Q * Real.rpow 2 s))) * δ' ^ (-s) := by
    have h : NQ ≥ (1 / K) * Real.log (1 / δ') ^ (-K) *
        (1 / (C_P * (13 * C_Q * Real.rpow 2 s))) * MQ * δ' ^ (-s) := h_bound
    have h' : NQ / MQ ≥
        ((1 / K) * Real.log (1 / δ') ^ (-K) *
          (1 / (C_P * (13 * C_Q * Real.rpow 2 s))) * MQ * δ' ^ (-s)) / MQ := by gcongr
    have h'' : (((1 / K) * Real.log (1 / δ') ^ (-K) *
        (1 / (C_P * (13 * C_Q * Real.rpow 2 s))) * MQ * δ' ^ (-s)) / MQ) =
        (1 / K) * Real.log (1 / δ') ^ (-K) *
        (1 / (C_P * (13 * C_Q * Real.rpow 2 s))) * δ' ^ (-s) := by
      field_simp [hMQ_pos.ne'] <;> ring
    rw [h''] at h'
    exact h'

  let localLoss : ℝ := a + b + polylogLoss
  have hloss : 0 ≤ localLoss := by
    have h1 : 0 ≤ a := ha_nonneg
    have h2 : 0 ≤ b := hb_nonneg
    have h3 : 0 < polylogLoss := hpolylogLoss_pos
    dsimp only [localLoss]
    linarith

  -- Scale conversion from outer level
  have h_scale : (1 / K) * Real.log (1 / δ') ^ (-K) *
      (1 / (C_P * (13 * C_Q * Real.rpow 2 s))) * δ' ^ (-s) ≥
      δ ^ (-(s / 2 - localLoss)) := by
    simpa [C_P, C_Q, δ', δ, localLoss] using h_convert

  have h_final : δ ^ (-(s / 2 - localLoss)) ≤ NQ / MQ :=
    le_trans h_scale h_ratio

  exact {
    localCount := NQ,
    localMultiplicity := MQ,
    localLoss := localLoss,
    hMQ_pos := hMQ_pos,
    hlossQ := hloss,
    hfine := h_final
  }

end DirecretisedFurstenbergEstimate.Section6

end
