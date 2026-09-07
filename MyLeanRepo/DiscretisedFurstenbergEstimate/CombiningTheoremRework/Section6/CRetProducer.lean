module

/-
  CRet Producer

  Extracts the ACTUAL C_ret from the fine-fiber S-set transfer and proves the
  power bound `C_ret ≤ δ_n^{-a_C_ret}` using the parent cancellation bound and
  individual factor bounds.

  Mathematical chain (all exponents are u, no t-u remainder):
    C_ret = C_point * 9 * K_density * |P₀| * δ_m^u
          = C_point * 9 * K_density * (|P₀| * δ_m^u)
          ≤ C_point * 9 * K_density * 9 * K_P           (parent cancellation)
          = 81 * C_point * K_density * K_P
          ≤ δ_n^{-a_C_ret}                             (power bounds + smallness)

  Factor roles:
    - K_density: local density factor from the fine-fiber S-set transfer
      (replaces data.K; equals 9 * K_B1 in the application, but is a SEPARATE
      input here, not referenced from B1InductionData)
    - K_global: global retention bound; K_density ≤ K_global and
      K_global ≤ δ_n^{-loss_global}
    - K_P: parent square regularity constant; K_P ≤ δ_n^{-εInc}
    - C_point: point-set S-set constant; C_point ≤ δ_n^{-pointRegularityLoss}
    - 81 = 9 (density) * 9 (cancellation); bounded by δ_n^{-margin}

  Exponent:
    a_C_ret = pointRegularityLoss + εInc + loss_global + margin

  All power bounds (K_global, parent cancellation, point bound, 81 threshold)
  are explicit hypotheses, not constructed internally.

  Whiteprint node: c_ret_producer
  Status: IMPLEMENTED
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.RegularIncidence.Definitions
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DiscretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.RegularIncidence

/-- Packaged C_ret result: actual constant, S-set proof, and power bound. -/
structure CRetProducer (n m : ℕ) (u a_C_ret : ℝ) (PointSet : Set (EuclideanSpace ℝ (Fin 2))) where
  C_ret : ℝ
  h_ret_pos : 0 < C_ret
  h_ret_sset : IsDeltaSSet (dyadicDelta (n - m)) u C_ret PointSet
  hC_ret_bound : C_ret ≤ (dyadicDelta n) ^ (-a_C_ret)

/-- Produce a bounded C_ret from the actual C_ret and its S-set proof.

    Inputs (all conditional — nothing is constructed internally):
    - C_ret, hC_ret_pos, h_ret_sset: destructured output of fine-fiber transfer
    - h_formula: `C_ret = C_point * 9 * K_density * coarseCard * δ_m^u`
    - hK_density_le_global: `K_density ≤ K_global`
    - h_cancellation: `coarseCard * δ_m^u ≤ 9 * K_P` (parent cancellation)
    - Power bounds: C_point, K_global, K_P, and the constant 81

    NOTE: `K_density` is a separate parameter. It is NOT `data.K` from
    B1InductionData. In the application, K_density = 9 * K_B1 where K_B1 = data.K,
    but this relationship is established by the caller, not assumed here.
    `K_global` is the global retention factor that bounds K_density. -/
def produce_CRet
    {n m : ℕ} (hnm : n = 2 * m)
    {u pointRegularityLoss rho_sqrt loss_global margin a_C_ret : ℝ}
    {C_point K_P K_density K_global coarseCard : ℝ}
    {PointSet : Set (EuclideanSpace ℝ (Fin 2))}
    (C_ret : ℝ)
    (hC_ret_pos : 0 < C_ret)
    (h_ret_sset : IsDeltaSSet (dyadicDelta (n - m)) u C_ret PointSet)
    (h_formula : C_ret = C_point * 9 * K_density * coarseCard * (dyadicDelta m)^u)
    (h_CP_pos : 0 < C_point)
    (h_KP_pos : 0 < K_P)
    (h_Kdensity_pos : 0 < K_density)
    (h_Kglobal_pos : 0 < K_global)
    (h_coarseCard_nonneg : 0 ≤ coarseCard)
    -- K_density bounded by K_global
    (hK_density_le_global : K_density ≤ K_global)
    -- Parent cancellation
    (h_cancellation : coarseCard * (dyadicDelta m)^u ≤ 9 * K_P)
    -- Power bounds (all explicit inputs)
    (h_CP : C_point ≤ (dyadicDelta n)^(-pointRegularityLoss))
    (h_Kglobal : K_global ≤ (dyadicDelta n)^(-loss_global))
    (h_KP : K_P ≤ (dyadicDelta n)^(-rho_sqrt))
    (h_small : (81 : ℝ) ≤ (dyadicDelta n)^(-margin))
    (ha : a_C_ret = pointRegularityLoss + rho_sqrt + loss_global + margin) :
    CRetProducer n m u a_C_ret PointSet := by
  have hδn_pos : 0 < dyadicDelta n := dyadicDelta_pos n
  have hδm_pos : 0 < dyadicDelta m := dyadicDelta_pos m

  -- K_density ≤ K_global ≤ δ_n^{-loss_global}
  have hK_density_bound : K_density ≤ (dyadicDelta n)^(-loss_global) :=
    le_trans hK_density_le_global h_Kglobal

  -- Main cancellation: C_ret ≤ 81 * C_point * K_density * K_P
  have h1 : C_ret ≤ (81 : ℝ) * C_point * K_density * K_P := by
    rw [h_formula]
    have h2 : coarseCard * (dyadicDelta m)^u ≤ 9 * K_P := h_cancellation
    have h3 : 0 ≤ C_point := by linarith
    have h4 : 0 ≤ K_density := by linarith
    have h5 : 0 ≤ (dyadicDelta m)^u := Real.rpow_nonneg hδm_pos.le _
    have h7 : C_point * 9 * K_density * coarseCard * (dyadicDelta m)^u ≤
        C_point * 9 * K_density * (9 * K_P) := by
      have h71 : C_point * 9 * K_density * coarseCard * (dyadicDelta m)^u =
          C_point * 9 * K_density * (coarseCard * (dyadicDelta m)^u) := by ring
      rw [h71]
      gcongr <;> linarith
    have h10 : C_point * 9 * K_density * (9 * K_P) =
        (81 : ℝ) * C_point * K_density * K_P := by ring
    rw [h10] at h7
    exact h7

  -- Power bound: 81 * C_point * K_density * K_P ≤ δ_n^{-a_C_ret}
  have h_bound : C_ret ≤ (dyadicDelta n)^(-a_C_ret) := by
    calc C_ret
      ≤ (81 : ℝ) * C_point * K_density * K_P := h1
    _ ≤ (dyadicDelta n)^(-margin) * (dyadicDelta n)^(-pointRegularityLoss) *
          (dyadicDelta n)^(-loss_global) * (dyadicDelta n)^(-rho_sqrt) := by gcongr
    _ = (dyadicDelta n)^(-a_C_ret) := by
      rw [ha]
      have h_sum : (-margin) + (-pointRegularityLoss) + (-loss_global) + (-rho_sqrt) =
          -(pointRegularityLoss + rho_sqrt + loss_global + margin) := by ring
      have h : (dyadicDelta n)^(-margin) * (dyadicDelta n)^(-pointRegularityLoss) *
          (dyadicDelta n)^(-loss_global) * (dyadicDelta n)^(-rho_sqrt) =
          (dyadicDelta n)^((-margin) + (-pointRegularityLoss) + (-loss_global) + (-rho_sqrt)) := by
        simpa [Real.rpow_add hδn_pos] using rfl
      rw [h, h_sum]
  exact ⟨C_ret, hC_ret_pos, h_ret_sset, h_bound⟩

/-- Helper to package CRetProducer for `fine_cor25_from_fixed_K`.

    CRITICAL: Do NOT double-count the 81*max factor.

    The C_ret in `CRetProducer` is the RAW point-set S-set constant:
      C_ret = C_point * 9 * K_density * coarseCard * δ_m^u

    When passed to `fine_cor25_from_fixed_K`, that lemma internally calls
    `fine_pointset_sset_to_finset_sset`, which converts the point-set S-set
    to a finset S-set with constant:
      C_P_finset = 81 * max(C_ret, 1) * (2√2)^s

    The denominator in `fine_ratio_explicit_uniform` already includes this
    `81 * max(C_ret, 1) * (2√2)^s` factor. Therefore:

    - The exponent `a_C_ret` bounds ONLY the raw C_ret.
    - Do NOT add extra exponents for 81, max, or (2√2)^s.
    - The `margin` exponent in `produce_CRet` accounts for the 81 from
      the CANCELLATION step (9 density * 9 cancellation = 81), NOT the 81
      from `fine_pointset_sset_to_finset_sset`.

    Usage with `fine_cor25_from_fixed_K`:
    ```lean
    let cret : CRetProducer ... := produce_CRet ...
    fine_cor25_from_fixed_K K hK_pos hK_spec data Q hQ ...
      (h_ret_sset := cret.h_ret_sset)
      ...
      (a := a_C_ret) (b := b_C_Q) (polylogLoss := polylogLoss)
      (hC_ret_bound := cret.hC_ret_bound)
      (hC_Q_bound := hC_Q_bound)
      h_even h_convert
    ```

    The resulting `localLoss` = `a_C_ret + b_C_Q + polylogLoss`.
-/
def CRetProducer.for_fine_cor25 {n m u a_C_ret PointSet}
    (cret : CRetProducer n m u a_C_ret PointSet) :
    { C_ret : ℝ // 0 < C_ret ∧
      IsDeltaSSet (dyadicDelta (n - m)) u C_ret PointSet ∧
      C_ret ≤ (dyadicDelta n) ^ (-a_C_ret) } :=
  ⟨cret.C_ret, cret.h_ret_pos, cret.h_ret_sset, cret.hC_ret_bound⟩

end DiscretisedFurstenbergEstimate.CombiningTheoremRework

end
