module

/-
  Clean Fine Cor25 End-to-End Chain

  Wires all clean links with the same Q:
  1. local_fine_sset_with_density_clean → C_ret and fine S-set
  2. produce_CRet → power bound on C_ret
  3. fine_cor25_from_fixed_K → FineCor25Data

  Q and h_density are inputs (from b1_retained_fiber_density upstream).
  All clean imports, no Prop73 contamination.

  Whiteprint node: clean_fine_cor25_chain
  Status: IMPLEMENTED
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.RegularIncidence.Definitions
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Section6.B1InductionDataType
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Section6.CleanLocalFineSSet
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Section6.CRetProducer
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Section6.FineCor25FixedK
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DiscretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.CombiningTheorem
open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.RegularIncidence
open DirecretisedFurstenbergEstimate.Section6
open InductionConfigurations

/-- End-to-end clean chain: local S-set → CRet bound → FineCor25Data.

    Q and h_density come from b1_retained_fiber_density (upstream).
    The same Q is used for all steps.

    K_density = K_global throughout. -/
def clean_fine_cor25_chain
    {n m : ℕ}
    (h_even : n = 2 * m)
    (hnm : m ≤ n)
    {s t u C₁ : ℝ} {M : ℕ}
    {config : CombiningTheorem.NiceConfiguration n s C₁ M}
    (data : B1InductionData n m hnm s t C₁ M config)
    -- Fixed K from uniform_prop5
    (K : ℝ) (hK_pos : 0 < K)
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
    -- Point-set regularity
    (C_point : ℝ)
    (hE : IsDeltaSSet (dyadicDelta n) u C_point config.pointSet)
    (hu_pos : 0 < u)
    (hs_u : s ≤ u)
    -- Q and density (from b1_retained_fiber_density)
    (K_global : ℝ)
    (hK_global_pos : 0 < K_global)
    (Q : DyadicSquare m)
    (hQ : Q ∈ data.coarseConfig.P₀)
    (h_density : Metric.externalCoveringNumber (dyadicDelta n).toNNReal config.pointSet ≤
        ENNReal.ofReal (9 * K_global * (data.coarseConfig.P₀.card : ℝ)) *
        Metric.externalCoveringNumber (dyadicDelta n).toNNReal
          (⋃ p ∈ (data.P.filter (fun p => squareContained hnm p Q)),
            (p.toSet : Set EuclideanPlane)))
    (h_fineP_eq : (data.fineConfig Q hQ).P₀ =
        (data.P.filter (fun p => squareContained hnm p Q)).image (squareHomothety hnm Q))
    -- CRet producer inputs
    (K_P : ℝ)
    (h_KP_pos : 0 < K_P)
    (h_cancellation : (data.coarseConfig.P₀.card : ℝ) * (dyadicDelta m)^u ≤ 9 * K_P)
    (pointRegularityLoss rho_sqrt loss_global margin a_C_ret : ℝ)
    (h_CP : C_point ≤ (dyadicDelta n)^(-pointRegularityLoss))
    (h_Kglobal : K_global ≤ (dyadicDelta n)^(-loss_global))
    (h_KP : K_P ≤ (dyadicDelta n)^(-rho_sqrt))
    (h_small : (81 : ℝ) ≤ (dyadicDelta n)^(-margin))
    (ha : a_C_ret = pointRegularityLoss + rho_sqrt + loss_global + margin)
    -- FineCor25 inputs
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hnm_ge2 : 2 ≤ n - m)
    (b polylogLoss : ℝ)
    (ha_nonneg : 0 ≤ a_C_ret) (hb_nonneg : 0 ≤ b)
    (hpolylogLoss_pos : 0 < polylogLoss)
    (hC_Q_bound : max (data.CQ Q) 1 ≤ (dyadicDelta n)^(-b))
    -- Scale conversion
    (h_convert : (1 / K) * Real.log (1 / dyadicDelta (n - m)) ^ (-K) *
        (1 / ((81 * max (C_point * 9 * K_global * (data.coarseConfig.P₀.card : ℝ) * (dyadicDelta m)^u) 1 *
          (2 * Real.sqrt 2) ^ s) *
          (13 * max (data.CQ Q) 1 * Real.rpow 2 s))) *
        (dyadicDelta (n - m)) ^ (-s) ≥
      (dyadicDelta n) ^ (-(s / 2 - (a_C_ret + b + polylogLoss)))) :
    FineCor25Data (dyadicDelta n) s := by
  -- Step 1: Transfer S-set to normalized fine fiber
  have h_local : ∃ (C_ret : ℝ), 0 < C_ret ∧
      IsDeltaSSet (dyadicDelta (n - m)) u C_ret (data.fineConfig Q hQ).pointSet ∧
      C_ret = C_point * 9 * K_global * (data.coarseConfig.P₀.card : ℝ) * (dyadicDelta m)^u :=
    local_fine_sset_with_density_clean
      hnm data K_global hK_global_pos Q hQ hE hu_pos h_density h_fineP_eq
  let C_ret : ℝ := Classical.choose h_local
  have hC_ret_pos : 0 < C_ret := (Classical.choose_spec h_local).1
  have h_ret_sset : IsDeltaSSet (dyadicDelta (n - m)) u C_ret (data.fineConfig Q hQ).pointSet :=
    (Classical.choose_spec h_local).2.1
  have h_formula : C_ret = C_point * 9 * K_global * (data.coarseConfig.P₀.card : ℝ) * (dyadicDelta m)^u :=
    (Classical.choose_spec h_local).2.2

  -- Step 2: Produce CRet power bound
  let cRetProd : CRetProducer n m u a_C_ret (data.fineConfig Q hQ).pointSet :=
    produce_CRet
      (hnm := h_even)
      (C_ret := C_ret)
      (hC_ret_pos := hC_ret_pos)
      (h_ret_sset := h_ret_sset)
      (h_formula := h_formula)
      (h_CP_pos := hE.2.2.1)
      (h_KP_pos := h_KP_pos)
      (h_Kdensity_pos := hK_global_pos)
      (h_Kglobal_pos := hK_global_pos)
      (h_coarseCard_nonneg := by positivity)
      (hK_density_le_global := le_refl K_global)
      (h_cancellation := h_cancellation)
      (h_CP := h_CP)
      (h_Kglobal := h_Kglobal)
      (h_KP := h_KP)
      (h_small := h_small)
      (ha := ha)

  have hP_nonempty : (data.fineConfig Q hQ).P₀.Nonempty := by
    have h_img : Q ∈ data.P.image (InductionConfigurations.containingSquare hnm) := by
      rw [←data.h_coarse_P_eq] <;> exact hQ
    rcases Finset.mem_image.mp h_img with ⟨p, hp, h_eq⟩
    have h_cont : squareContained hnm p Q :=
      (containingSquare_iff hnm p Q).mp h_eq
    let p' := squareHomothety hnm Q p
    have h_p'_in : p' ∈ (data.fineConfig Q hQ).P₀ := by
      rw [h_fineP_eq]
      exact Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, h_cont⟩, rfl⟩
    exact ⟨p', h_p'_in⟩

  -- Rewrite h_convert with actual C_ret
  have h_convert' : (1 / K) * Real.log (1 / dyadicDelta (n - m)) ^ (-K) *
      (1 / ((81 * max C_ret 1 * (2 * Real.sqrt 2) ^ s) *
        (13 * max (data.CQ Q) 1 * Real.rpow 2 s))) *
      (dyadicDelta (n - m)) ^ (-s) ≥
    (dyadicDelta n) ^ (-(s / 2 - (a_C_ret + b + polylogLoss))) := by
    have h : C_ret = C_point * 9 * K_global * (data.coarseConfig.P₀.card : ℝ) * (dyadicDelta m)^u := h_formula
    rw [←h] at h_convert
    exact h_convert

  -- Step 3: FineCor25 from fixed K
  exact fine_cor25_from_fixed_K
    (K := K) (hK_pos := hK_pos) (hK_spec := hK_spec)
    data Q hQ hs_pos hs_lt_one hs_u
    (C_ret := C_ret)
    (h_ret_sset := h_ret_sset)
    hnm_ge2 hP_nonempty
    (a := a_C_ret) (b := b) (polylogLoss := polylogLoss)
    ha_nonneg hb_nonneg hpolylogLoss_pos
    cRetProd.hC_ret_bound
    hC_Q_bound
    h_even
    h_convert'

end DiscretisedFurstenbergEstimate.CombiningTheoremRework

end
