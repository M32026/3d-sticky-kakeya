module

/-
  B1InductionData Constructor

  Provides `b1_induction_data_from_raw`, which packages the raw fields
  from `b1_bridge_decomposition` into a `B1InductionData` structure.

  Since `b1_bridge_decomposition` returns a deeply nested existential (`Prop`),
  it cannot be directly destructured into a Type like `B1InductionData`.
  Instead, callers in a Prop context (e.g., the main theorem proof) should
  use `rcases` on the bridge output and then pass the individual fields
  to this lemma.

  Every field of B1InductionData maps directly to a bridge output field.

  Whiteprint node: b1_induction_data_constructor
  Status: IMPLEMENTED
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.B1Integration
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.B1ToSection6
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Section6.B1InductionDataType
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DiscretisedFurstenbergEstimate.CombiningTheorem
open DiscretisedFurstenbergEstimate.InductionConfigurations
open DiscretisedFurstenbergEstimate.Bridge
open DirecretisedFurstenbergEstimate.FormatConversion.M2
open DirecretisedFurstenbergEstimate.Section6

/-- Package raw B1 bridge decomposition output into B1InductionData.

    Callers should first `rcases` the output of `b1_bridge_decomposition`
    and then pass the individual witnesses to this lemma.

    All fields are directly mapped; no additional mathematics is needed. -/
def b1_induction_data_from_raw
    {n m : ℕ} (hnm : m ≤ n)
    {s t C₁ : ℝ} {M : ℕ}
    {config : CombiningTheorem.NiceConfiguration n s C₁ M}
    -- Bridge output witnesses
    (K : ℝ)
    (hK_ge1 : 1 ≤ K)
    (P : Finset (CTMainSquare n))
    (hP_sub : P ⊆ config.P₀)
    (hP_nonempty : P.Nonempty)
    (tubeFamily : (p : CTMainSquare n) → p ∈ P → Finset (CTMainTube n))
    (CΔ : ℝ)
    (MΔ : ℕ)
    (hMΔ_pos : 0 < MΔ)
    (coarseConfig : CTMainConfig m s CΔ MΔ)
    (CQ : CTMainSquare m → ℝ)
    (MQ : CTMainSquare m → ℕ)
    (hMQ : ∀ Q ∈ coarseConfig.P₀, 0 < MQ Q)
    (fineConfig : (Q : CTMainSquare m) → (hQ : Q ∈ coarseConfig.P₀) →
      CTMainConfig (n - m) s (CQ Q) (MQ Q))
    (fineConfig_B1 : (Q : CTMainSquare m) → (hQ : Q ∈ coarseConfig.P₀) →
      B1BridgeHypotheses (n - m) (fineConfig Q hQ))
    (h_coarse_P_eq : coarseConfig.P₀ = P.image (InductionConfigurations.containingSquare hnm))
    (h_per_Q_ret : ∀ Q ∈ coarseConfig.P₀,
      ((config.P₀.filter fun p => InductionConfigurations.squareContained hnm p Q).card : ℝ) ≤
      K * ((P.filter fun p => InductionConfigurations.squareContained hnm p Q).card : ℝ))
    (h_tube_sub : ∀ p hp, tubeFamily p hp ⊆ config.tubeFamily p (hP_sub hp))
    (h_tube_size : ∀ p hp, (M : ℝ) ≤ K * ((tubeFamily p hp).card : ℝ))
    (h_tube_intersect : ∀ p hp T, T ∈ tubeFamily p hp →
      (T.toSet ∩ p.toSet).Nonempty)
    (h_tube_geometry : ∀ (p : CTMainSquare n) (hp : p ∈ P) (T : CTMainTube n), T ∈ tubeFamily p hp →
      ∃ (hQ : InductionConfigurations.containingSquare hnm p ∈ coarseConfig.P₀)
        (U_stand : DiscretisedFurstenbergEstimate.Bridge.StandTube m)
        (C : DiscretisedFurstenbergEstimate.Bridge.StandTube n),
        C ∈ DiscretisedFurstenbergEstimate.Bridge.Geometric.coveringCells n T.a T.b ∧
        DiscretisedFurstenbergEstimate.Bridge.tubeToMainShifted U_stand ∈
          coarseConfig.tubeFamily (InductionConfigurations.containingSquare hnm p) hQ ∧
        C.toSet ⊆ U_stand.toSet)
    (hCΔ_compare : CΔ ≤ K * C₁ ∧ C₁ ≤ K * CΔ)
    (hCQ_compare : ∀ Q ∈ coarseConfig.P₀, CQ Q ≤ K * C₁ ∧ C₁ ≤ K * CQ Q)
    (h_coarse_slope : ∀ T ∈ coarseConfig.T₀, |T.slope| ≤ 1) :
    B1InductionData n m hnm s t C₁ M config :=
  { K := K
    hK_ge1 := hK_ge1
    P := P
    hP_sub := hP_sub
    hP_nonempty := hP_nonempty
    CΔ := CΔ
    MΔ := MΔ
    hMΔ_pos := hMΔ_pos
    coarseConfig := coarseConfig
    CQ := CQ
    MQ := MQ
    hMQ := hMQ
    fineConfig := fineConfig
    fineConfig_B1 := fineConfig_B1
    h_coarse_P_eq := h_coarse_P_eq
    h_per_Q_ret := h_per_Q_ret
    tubeFamily := tubeFamily
    h_tube_sub := h_tube_sub
    h_tube_size := h_tube_size
    h_tube_intersect := h_tube_intersect
    h_tube_geometry := h_tube_geometry
    hCΔ_compare := hCΔ_compare
    hCQ_compare := hCQ_compare
    h_coarse_slope := h_coarse_slope }

/-- Convenience wrapper: from the combined tube data hypothesis.

    The bridge outputs tube sub/size as a single conjunction:
      `∀ p hp, tubeFamily p hp ⊆ ... ∧ (M : ℝ) ≤ K * ...`
    This wrapper splits it automatically. -/
def b1_induction_data_from_bridge_conj
    {n m : ℕ} (hnm : m ≤ n)
    {s t C₁ : ℝ} {M : ℕ}
    {config : CombiningTheorem.NiceConfiguration n s C₁ M}
    (K : ℝ) (hK_ge1 : 1 ≤ K)
    (P : Finset (CTMainSquare n))
    (hP_sub : P ⊆ config.P₀)
    (hP_nonempty : P.Nonempty)
    (tubeFamily : (p : CTMainSquare n) → p ∈ P → Finset (CTMainTube n))
    (CΔ : ℝ) (MΔ : ℕ) (hMΔ_pos : 0 < MΔ)
    (coarseConfig : CTMainConfig m s CΔ MΔ)
    (CQ : CTMainSquare m → ℝ)
    (MQ : CTMainSquare m → ℕ)
    (hMQ : ∀ Q ∈ coarseConfig.P₀, 0 < MQ Q)
    (fineConfig : (Q : CTMainSquare m) → (hQ : Q ∈ coarseConfig.P₀) →
      CTMainConfig (n - m) s (CQ Q) (MQ Q))
    (fineConfig_B1 : (Q : CTMainSquare m) → (hQ : Q ∈ coarseConfig.P₀) →
      B1BridgeHypotheses (n - m) (fineConfig Q hQ))
    (h_coarse_P_eq : coarseConfig.P₀ = P.image (InductionConfigurations.containingSquare hnm))
    (h_per_Q_ret : ∀ Q ∈ coarseConfig.P₀,
      ((config.P₀.filter fun p => InductionConfigurations.squareContained hnm p Q).card : ℝ) ≤
      K * ((P.filter fun p => InductionConfigurations.squareContained hnm p Q).card : ℝ))
    (h_tube_data : ∀ p hp, tubeFamily p hp ⊆ config.tubeFamily p (hP_sub hp) ∧
      (M : ℝ) ≤ K * ((tubeFamily p hp).card : ℝ))
    (hCΔ_compare : CΔ ≤ K * C₁ ∧ C₁ ≤ K * CΔ)
    (hCQ_compare : ∀ Q ∈ coarseConfig.P₀, CQ Q ≤ K * C₁ ∧ C₁ ≤ K * CQ Q)
    (h_tube_intersect : ∀ p hp T, T ∈ tubeFamily p hp →
      (T.toSet ∩ p.toSet).Nonempty)
    (h_tube_geometry : ∀ (p : CTMainSquare n) (hp : p ∈ P) (T : CTMainTube n), T ∈ tubeFamily p hp →
      ∃ (hQ : InductionConfigurations.containingSquare hnm p ∈ coarseConfig.P₀)
        (U_stand : DiscretisedFurstenbergEstimate.Bridge.StandTube m)
        (C : DiscretisedFurstenbergEstimate.Bridge.StandTube n),
        C ∈ DiscretisedFurstenbergEstimate.Bridge.Geometric.coveringCells n T.a T.b ∧
        DiscretisedFurstenbergEstimate.Bridge.tubeToMainShifted U_stand ∈
          coarseConfig.tubeFamily (InductionConfigurations.containingSquare hnm p) hQ ∧
        C.toSet ⊆ U_stand.toSet)
    (h_coarse_slope : ∀ T ∈ coarseConfig.T₀, |T.slope| ≤ 1) :
    B1InductionData n m hnm s t C₁ M config :=
  b1_induction_data_from_raw hnm
    K hK_ge1 P hP_sub hP_nonempty tubeFamily
    CΔ MΔ hMΔ_pos coarseConfig CQ MQ hMQ fineConfig fineConfig_B1
    h_coarse_P_eq h_per_Q_ret
    (fun p hp => (h_tube_data p hp).1)
    (fun p hp => (h_tube_data p hp).2)
    h_tube_intersect h_tube_geometry hCΔ_compare hCQ_compare h_coarse_slope

/-! ========================================================================
   Q selection wrapper: B1InductionData → retained-fiber density
   ======================================================================== -/

/-- Select a heavy coarse square Q from B1InductionData.

    Given `B1InductionData` plus global retention `K_global`, use
    `b1_retained_fiber_density` to select Q ∈ coarseConfig.P₀ such that:
      Ncover(config.pointSet) ≤ 9·K_global·|coarseConfig.P₀| · Ncover(E_ret(Q))

    Also returns the fine-P₀ equality specialized to Q.

    The universal `h_fineP_eq_all` comes from the B1 bridge output (it is
    one of the conjuncts not stored in B1InductionData). -/
lemma b1_induction_data_select_fiber
    {n m : ℕ} (hnm : m ≤ n)
    {s t C₁ : ℝ} {M : ℕ}
    {config : CombiningTheorem.NiceConfiguration n s C₁ M}
    (data : B1InductionData n m hnm s t C₁ M config)
    (K_global : ℝ)
    (hK_global_pos : 0 < K_global)
    (h_global_ret : (config.P₀.card : ℝ) ≤ K_global * (data.P.card : ℝ))
    (h_fineP_eq_all : ∀ (Q : CTMainSquare m) (hQ : Q ∈ data.coarseConfig.P₀),
      (data.fineConfig Q hQ).P₀ =
        (data.P.filter (fun p => InductionConfigurations.squareContained hnm p Q)).image
          (InductionConfigurations.squareHomothety hnm Q)) :
    ∃ (Q : CTMainSquare m) (hQ : Q ∈ data.coarseConfig.P₀),
      (Metric.externalCoveringNumber (DiscretisedFurstenbergEstimate.dyadicDelta n).toNNReal
        config.pointSet : ENNReal) ≤
      ENNReal.ofReal (9 * K_global * (data.coarseConfig.P₀.card : ℝ)) *
      Metric.externalCoveringNumber (DiscretisedFurstenbergEstimate.dyadicDelta n).toNNReal
        (⋃ p ∈ (data.P.filter (fun p => InductionConfigurations.squareContained hnm p Q)),
          (p.toSet : Set (EuclideanSpace ℝ (Fin 2)))) ∧
      (data.fineConfig Q hQ).P₀ =
        (data.P.filter (fun p => InductionConfigurations.squareContained hnm p Q)).image
          (InductionConfigurations.squareHomothety hnm Q) := by
  have h_density : ∃ (Q : CTMainSquare m) (hQ : Q ∈ data.coarseConfig.P₀), _ :=
    b1_retained_fiber_density
      (hnm := hnm)
      (config := config)
      (K_global := K_global)
      (P := data.P)
      (CΔ := data.CΔ)
      (MΔ := data.MΔ)
      (coarseConfig := data.coarseConfig)
      (hK_global_pos := hK_global_pos)
      (hP_nonempty := data.hP_nonempty)
      (hP_sub := data.hP_sub)
      (h_coarse_P_eq := data.h_coarse_P_eq)
      (h_global_ret := h_global_ret)
  rcases h_density with ⟨Q, hQ, hQ_density⟩
  refine ⟨Q, hQ, hQ_density, h_fineP_eq_all Q hQ⟩

end DiscretisedFurstenbergEstimate.CombiningTheoremRework

end
