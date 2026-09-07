module

public import MyLeanRepo.InductionOnScales.Basic
public import MyLeanRepo.InductionOnScales.SlopeCells
public import MyLeanRepo.InductionOnScales.UniformFibers
public import MyLeanRepo.InductionOnScales.Definitions
public import MyLeanRepo.OSWPrelude

@[expose] public section

/-!
# Cardinality Final (OS 5.5)

Final cardinality bound for condition (5.5), assuming a fiber-uniform
coarse configuration with fiber sizes in `[NΔ, 4·NΔ)`.

## Algebra

1. est1 (form80): |config.tubes| ≥ |coarseConfig.tubes| * NΔ
2. est2 (form71): |TQ_local Q| ≤ MΔ * 4 * NΔ
3. est3: |TQ_local Q| ≥ |fineConfig.tubes| * m_Q / 9
4. Retention: M ≤ K_ret * K_loss * m_Q * MQ

Combining:
  |coarseTubes| * |TQ_local| ≤ |config.tubes| * 4 * MΔ   (est1+est2)
  |fineTubes| ≤ 9 * |TQ_local| / m_Q                      (est3)
  |coarseTubes| * |fineTubes| * M
    ≤ 36 * K_ret * K_loss * |config.tubes| * MΔ * MQ
    ≤ K * |config.tubes| * MΔ * MQ                         (K ≥ 36 * K_ret * K_loss)
-/

attribute [local instance] Classical.propDecidable

noncomputable section

namespace InductionOnScales

lemma cardinality_final
    {n m : ℕ} (hnm : m ≤ n)
    (s : ℝ) (hs : 0 ≤ s) (hs_one : s ≤ 1)
    (C₁ : ℝ) (hC₁ : 1 ≤ C₁)
    (M : ℕ) (hM : 0 < M)
    (config : NiceConfiguration n s C₁ M)
    (CΔ : ℝ) (MΔ : ℕ) (hMΔ : 0 < MΔ)
    (coarseConfig : NiceConfiguration m s CΔ MΔ)
    (Q : DyadicSquare m) (hQ : Q ∈ coarseConfig.points)
    (CQ : ℝ) (MQ : ℕ) (hMQ_pos : 0 < MQ)
    (fineConfig : NiceConfiguration (n - m) s CQ MQ)
    (m_Q : ℕ) (hmQ_pos : 0 < m_Q)
    (K_ret K_loss K : ℝ)
    (hK_ret_one : 1 ≤ K_ret) (hK_loss_one : 1 ≤ K_loss)
    (hK_one : 1 ≤ K)
    (hK_bound : 36 * K_ret * K_loss ≤ K)
    (NΔ : ℕ) (hNΔ_pos : 0 < NΔ)
    (h_fiber_lower : ∀ U ∈ coarseConfig.tubes, NΔ ≤ fiberSize hnm config.tubes U)
    (h_fiber_upper : ∀ U ∈ coarseConfig.tubes, fiberSize hnm config.tubes U < 4 * NΔ)
    (TQ_local : Finset (DyadicTube n))
    (hTQ_local_eq : TQ_local =
        (coarseConfig.tubeFamily Q hQ).biUnion
          (fun U => config.tubes.filter (fun T => T.toSet ⊆ U.toSet)))
    (h_est3 : (TQ_local.card : ℝ) ≥
        (fineConfig.tubes.card : ℝ) * (m_Q : ℝ) / 9)
    (h_M_bound : (M : ℝ) ≤ K_ret * K_loss * (m_Q : ℝ) * (MQ : ℝ)) :
    K * (config.tubes.card : ℝ) * MΔ * MQ ≥
      (coarseConfig.tubes.card : ℝ) * (fineConfig.tubes.card : ℝ) * M := by
  set mQr : ℝ := (m_Q : ℝ) with hmQr
  set NDr : ℝ := (NΔ : ℝ) with hNDr
  set NΔ2 : ℕ := 2 * NΔ with hNΔ2
  have h_mQ_pos' : 0 < mQr := by positivity
  have h_ND_pos' : 0 < NDr := by positivity
  have h_mQ_ne : mQr ≠ 0 := h_mQ_pos'.ne'
  have h_ND_ne : NDr ≠ 0 := h_ND_pos'.ne'

  -- est1: |config.tubes| ≥ |coarseConfig.tubes| * NΔ
  have h_est1 : (config.tubes.card : ℝ) ≥ (coarseConfig.tubes.card : ℝ) * NDr :=
    form80_bound hnm config.tubes coarseConfig.tubes NΔ h_fiber_lower

  -- est2: |TQ_local| ≤ MΔ * 4 * NΔ
  -- Use form71_bound with NΔ2 = 2*NΔ, so it requires fiberSize < 2*NΔ2 = 4*NΔ
  -- and gives bound MΔ * 2 * NΔ2 = MΔ * 4 * NΔ
  have h_est2 : (TQ_local.card : ℝ) ≤ (MΔ : ℝ) * 4 * NDr := by
    rw [hTQ_local_eq]
    have h_family_card : (coarseConfig.tubeFamily Q hQ).card ≤ MΔ := by
      have h : (coarseConfig.tubeFamily Q hQ).card = MΔ := coarseConfig.h_size Q hQ
      rw [h] <;> exact Nat.le_refl MΔ
    have h_upper_family : ∀ U ∈ coarseConfig.tubeFamily Q hQ,
        fiberSize hnm config.tubes U < 2 * NΔ2 := by
      intro U hU
      have hU_in_tubes : U ∈ coarseConfig.tubes := coarseConfig.h_subset Q hQ hU
      have h : fiberSize hnm config.tubes U < 4 * NΔ := h_fiber_upper U hU_in_tubes
      have h' : 2 * NΔ2 = 4 * NΔ := by
        simp [hNΔ2] <;> ring
      rw [h']
      exact h
    have h := form71_bound hnm config.tubes
      (coarseConfig.tubeFamily Q hQ) MΔ h_family_card NΔ2 h_upper_family
    have h' : ((coarseConfig.tubeFamily Q hQ).biUnion
          (fun U => config.tubes.filter (fun T => T.toSet ⊆ U.toSet))).card
        ≤ MΔ * 2 * NΔ2 := h
    have h_cast : ((MΔ * 2 * NΔ2 : ℕ) : ℝ) = (MΔ : ℝ) * 4 * NDr := by
      simp [hNDr, hNΔ2] <;> ring
    have h_real : (((coarseConfig.tubeFamily Q hQ).biUnion
          (fun U => config.tubes.filter (fun T => T.toSet ⊆ U.toSet))).card : ℝ)
        ≤ ((MΔ * 2 * NΔ2 : ℕ) : ℝ) := by exact_mod_cast h'
    rw [h_cast] at h_real
    exact h_real

  -- If fineConfig.tubes is empty, RHS = 0 and we're done
  by_cases h_fine_ne : fineConfig.tubes.Nonempty
  · -- Nonempty case
    have h_fine_card_pos : 0 < fineConfig.tubes.card := h_fine_ne.card_pos
    have h2 : 0 < (fineConfig.tubes.card : ℝ) := by exact_mod_cast h_fine_card_pos
    have h_TQ_pos : 0 < (TQ_local.card : ℝ) := by
      have h4 : 0 < (fineConfig.tubes.card : ℝ) * mQr / 9 := by positivity
      exact lt_of_lt_of_le h4 h_est3
    have h_TQ_ne : (TQ_local.card : ℝ) ≠ 0 := h_TQ_pos.ne'

    -- |coarseTubes| * |TQ_local| ≤ |config.tubes| * 4 * MΔ
    have h_coarse_TQ : (coarseConfig.tubes.card : ℝ) * (TQ_local.card : ℝ) ≤
        (config.tubes.card : ℝ) * 4 * (MΔ : ℝ) := by
      have h1 : (coarseConfig.tubes.card : ℝ) * NDr ≤ (config.tubes.card : ℝ) := h_est1
      have h2 : (TQ_local.card : ℝ) ≤ (MΔ : ℝ) * 4 * NDr := h_est2
      calc
        (coarseConfig.tubes.card : ℝ) * (TQ_local.card : ℝ)
          ≤ (coarseConfig.tubes.card : ℝ) * ((MΔ : ℝ) * 4 * NDr) := by gcongr
        _ = (MΔ : ℝ) * 4 * ((coarseConfig.tubes.card : ℝ) * NDr) := by ring
        _ ≤ (MΔ : ℝ) * 4 * (config.tubes.card : ℝ) := by gcongr
        _ = (config.tubes.card : ℝ) * 4 * (MΔ : ℝ) := by ring

    -- |fineTubes| ≤ 9 * |TQ_local| / m_Q
    have h_fine_le : (fineConfig.tubes.card : ℝ) ≤ 9 * (TQ_local.card : ℝ) / mQr := by
      have h : (fineConfig.tubes.card : ℝ) * mQr ≤ 9 * (TQ_local.card : ℝ) := by
        have h' : (fineConfig.tubes.card : ℝ) * mQr / 9 ≤ (TQ_local.card : ℝ) := h_est3
        linarith
      have h_eq : (fineConfig.tubes.card : ℝ) = ((fineConfig.tubes.card : ℝ) * mQr) / mQr := by
        field_simp [h_mQ_ne] <;> ring
      rw [h_eq]
      gcongr

    have h_main1 : (coarseConfig.tubes.card : ℝ) * (fineConfig.tubes.card : ℝ) * (M : ℝ) ≤
        36 * K_ret * K_loss * (config.tubes.card : ℝ) * (MΔ : ℝ) * (MQ : ℝ) := by
      calc
        (coarseConfig.tubes.card : ℝ) * (fineConfig.tubes.card : ℝ) * (M : ℝ)
          ≤ (coarseConfig.tubes.card : ℝ) * (9 * (TQ_local.card : ℝ) / mQr) * (M : ℝ) := by
            gcongr <;> linarith
        _ = (9 / mQr) * ((coarseConfig.tubes.card : ℝ) * (TQ_local.card : ℝ)) * (M : ℝ) := by ring
        _ ≤ (9 / mQr) * ((config.tubes.card : ℝ) * 4 * (MΔ : ℝ)) * (M : ℝ) := by
            gcongr <;> linarith
        _ = 36 * (MΔ : ℝ) * (config.tubes.card : ℝ) * (M : ℝ) / mQr := by ring
        _ ≤ 36 * (MΔ : ℝ) * (config.tubes.card : ℝ) *
              (K_ret * K_loss * mQr * (MQ : ℝ)) / mQr := by gcongr <;> linarith
        _ = 36 * K_ret * K_loss * (config.tubes.card : ℝ) * (MΔ : ℝ) * (MQ : ℝ) := by
            field_simp [h_mQ_ne] <;> ring

    calc
      (coarseConfig.tubes.card : ℝ) * (fineConfig.tubes.card : ℝ) * (M : ℝ)
        ≤ 36 * K_ret * K_loss * (config.tubes.card : ℝ) * (MΔ : ℝ) * (MQ : ℝ) := h_main1
      _ ≤ K * (config.tubes.card : ℝ) * (MΔ : ℝ) * (MQ : ℝ) := by
          have h_pos1 : 0 ≤ (config.tubes.card : ℝ) := by positivity
          have h_pos2 : 0 ≤ (MΔ : ℝ) := by positivity
          have h_pos3 : 0 ≤ (MQ : ℝ) := by positivity
          gcongr <;> linarith
  · -- Empty case
    have h_empty : fineConfig.tubes = ∅ := by
      simpa [Finset.not_nonempty_iff_eq_empty] using h_fine_ne
    rw [h_empty]
    <;> simp <;> positivity

end InductionOnScales
