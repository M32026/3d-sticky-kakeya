module

/-
  Variant of global_2s_bound without the hP_large condition.
  Gives |U| ≥ |P|·M/(4(1+K)) where K = C_common·C_P·C_T·K_energy·δ^s·|P|.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Global2sBound
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section


namespace DirecretisedFurstenbergEstimate.Global2sBound

open DirecretisedFurstenbergEstimate

theorem global_2s_bound_no_hP_large
    {X : Type*} [PseudoMetricSpace X] [DecidableEq X]
    {δ s t C_P C_T M C_common K_energy : ℝ}
    (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1)
    (hs : 0 < s) (hst : s < t)
    (hCP_pos : 0 < C_P) (hCT_pos : 0 < C_T) (hM_pos : 0 < M)
    (hCcommon_pos : 0 < C_common) (hK_pos : 0 < K_energy)
    {P : Finset X}
    (hP_nonempty : P.Nonempty)
    (hP_sep : Set.Pairwise (P : Set X) (fun p q => δ ≤ dist p q))
    {Tp : X → Finset Tube}
    (hTp_card_lower : ∀ p ∈ P, (M / 2 : ℝ) ≤ (Tp p).card)
    (hTp_card_upper : ∀ p ∈ P, (Tp p).card ≤ M)
    (h_common_bound : ∀ p ∈ P, ∀ q ∈ P, p ≠ q →
      ((Tp p) ∩ (Tp q)).card ≤ C_common * C_T * M * (δ / dist p q)^s)
    (h_energy : ∑ p ∈ P, ∑ q ∈ P.erase p, (dist p q)^(-s) ≤
        K_energy * C_P * (P.card : ℝ)^2) :
    ((P.biUnion Tp).card : ℝ) ≥
      (P.card : ℝ) * M / (4 * (1 + C_common * C_P * C_T * K_energy * δ^s * (P.card : ℝ))) := by
  set U : Finset Tube := P.biUnion Tp with hU_def
  set d : Tube → ℕ := fun ℓ => (P.filter (fun p => ℓ ∈ Tp p)).card with hd_def
  set K : ℝ := C_common * C_P * C_T * K_energy * δ^s * (P.card : ℝ) with hK_def

  have hTp_sub : ∀ p ∈ P, Tp p ⊆ U := by
    intro p hp ℓ hℓ
    exact Finset.mem_biUnion.mpr ⟨p, hp, hℓ⟩

  have hI : (∑ p ∈ P, (Tp p).card : ℝ) = (∑ ℓ ∈ U, (d ℓ : ℝ)) := by
    have h1 : (∑ ℓ ∈ U, (d ℓ : ℝ)) = (∑ p ∈ P, (Tp p).card : ℝ) := by
      have h2 := sum_weighted_fiber (f := fun (_ : Tube) => (1 : ℝ)) hTp_sub
      simpa [d, Finset.sum_const] using h2
    exact h1.symm

  have hI_lower : (∑ p ∈ P, (Tp p).card : ℝ) ≥ (P.card : ℝ) * (M / 2) := by
    have h : ∀ p ∈ P, (M / 2 : ℝ) ≤ ((Tp p).card : ℝ) := by
      intro p hp; exact_mod_cast hTp_card_lower p hp
    have h2 : (∑ p ∈ P, (M / 2 : ℝ)) ≤ ∑ p ∈ P, ((Tp p).card : ℝ) :=
      Finset.sum_le_sum h
    simpa [Finset.sum_const] using h2

  have hI_upper : (∑ p ∈ P, (Tp p).card : ℝ) ≤ (P.card : ℝ) * M := by
    have h : ∀ p ∈ P, ((Tp p).card : ℝ) ≤ M := by
      intro p hp; exact_mod_cast hTp_card_upper p hp
    have h2 : ∑ p ∈ P, ((Tp p).card : ℝ) ≤ ∑ p ∈ P, M := Finset.sum_le_sum h
    simpa [Finset.sum_const] using h2

  have h_sum_d2 : (∑ ℓ ∈ U, (d ℓ : ℝ)^2) =
      ∑ p ∈ P, ∑ q ∈ P, (((Tp p) ∩ (Tp q)).card : ℝ) := by
    have h1 : (∑ ℓ ∈ U, (d ℓ : ℝ)^2) = ∑ p ∈ P, ∑ ℓ ∈ Tp p, (d ℓ : ℝ) := by
      have h2 : ∑ ℓ ∈ U, (d ℓ : ℝ)^2 = ∑ ℓ ∈ U, (d ℓ : ℝ) * (d ℓ : ℝ) := by
        apply Finset.sum_congr rfl; intro ℓ _; ring
      rw [h2]
      exact sum_weighted_fiber hTp_sub
    rw [h1]
    apply Finset.sum_congr rfl
    intro p _
    have h3 : ∑ ℓ ∈ Tp p, (d ℓ : ℝ) =
        ∑ q ∈ P, (((Tp p) ∩ (Tp q)).card : ℝ) := by
      have h4 : ∑ ℓ ∈ Tp p, (d ℓ : ℝ) =
          ∑ q ∈ P, ∑ ℓ ∈ Tp p, (if ℓ ∈ Tp q then (1 : ℝ) else 0) := by
        have h5 : ∀ ℓ ∈ Tp p, (d ℓ : ℝ) = ∑ q ∈ P, (if ℓ ∈ Tp q then (1 : ℝ) else 0) := by
          intro ℓ _
          simp [d, Finset.sum_ite] <;> rfl
        rw [Finset.sum_congr rfl h5]
        rw [Finset.sum_comm]
      rw [h4]
      apply Finset.sum_congr rfl
      intro q _
      rw [Finset.sum_ite]
      <;> simp [Finset.filter_and]
      <;> rfl
    exact h3

  have h_split : (∑ p ∈ P, ∑ q ∈ P, (((Tp p) ∩ (Tp q)).card : ℝ)) =
      (∑ p ∈ P, (Tp p).card : ℝ) +
      ∑ p ∈ P, ∑ q ∈ P.erase p, (((Tp p) ∩ (Tp q)).card : ℝ) := by
    have h1 : ∀ p ∈ P, ∑ q ∈ P, (((Tp p) ∩ (Tp q)).card : ℝ) =
        ((Tp p).card : ℝ) + ∑ q ∈ P.erase p, (((Tp p) ∩ (Tp q)).card : ℝ) := by
      intro p hp
      have h2 : P = insert p (P.erase p) := by rw [Finset.insert_erase hp]
      rw [h2]
      simp [Finset.sum_insert, Finset.mem_erase, hp] <;> ring
    have h3 : ∑ p ∈ P, ∑ q ∈ P, (((Tp p) ∩ (Tp q)).card : ℝ) =
        ∑ p ∈ P, (((Tp p).card : ℝ) + ∑ q ∈ P.erase p, (((Tp p) ∩ (Tp q)).card : ℝ)) :=
      Finset.sum_congr rfl (fun p hp => h1 p hp)
    rw [h3, Finset.sum_add_distrib]

  have h_off_bound : ∑ p ∈ P, ∑ q ∈ P.erase p, (((Tp p) ∩ (Tp q)).card : ℝ) ≤
      C_common * C_T * M * δ^s * K_energy * C_P * (P.card : ℝ)^2 := by
    let K' := C_common * C_T * M * δ^s
    have h1 : ∑ p ∈ P, ∑ q ∈ P.erase p, (((Tp p) ∩ (Tp q)).card : ℝ) ≤
        ∑ p ∈ P, ∑ q ∈ P.erase p, (K' * (dist p q)^(-s)) := by
      apply Finset.sum_le_sum
      intro p _
      apply Finset.sum_le_sum
      intro q hq
      have hne_q : q ≠ p := (Finset.mem_erase.mp hq).1
      have hne : p ≠ q := hne_q.symm
      have hq' : q ∈ P := (Finset.mem_erase.mp hq).2
      have h5 : ((Tp p) ∩ (Tp q)).card ≤ C_common * C_T * M * (δ / dist p q)^s :=
        h_common_bound p ‹_› q hq' hne
      have h6 : (δ / dist p q)^s = δ^s * (dist p q)^(-s) := by
        have hdist_pos : 0 < dist p q := by
          have h_sep : δ ≤ dist p q := hP_sep (show p ∈ P from ‹_›) (show q ∈ P from hq') hne
          linarith [hδ_pos]
        by_cases hδ0 : δ = 0
        · rw [hδ0]; simp [hs.ne', Real.zero_rpow] <;> ring
        · have hδ_pos' : 0 < δ := by linarith
          have h1 : (δ / dist p q)^s = δ^s * ((dist p q)⁻¹)^s := by
            rw [div_eq_mul_inv, Real.mul_rpow (by positivity) (by positivity)]
          have h2 : ((dist p q)⁻¹)^s = (dist p q)^(-s) := by
            have h3 : 0 < (dist p q)⁻¹ := by positivity
            have h5 : ((dist p q)⁻¹)^s = Real.exp (Real.log ((dist p q)⁻¹) * s) := by
              rw [Real.rpow_def_of_pos h3]
            have h6' : (dist p q)^(-s) = Real.exp (Real.log (dist p q) * (-s)) := by
              rw [Real.rpow_def_of_pos hdist_pos]
            have h7 : Real.log ((dist p q)⁻¹) = -Real.log (dist p q) := by
              rw [Real.log_inv] <;> linarith
            rw [h5, h6', h7] <;> ring_nf
          rw [h1, h2]
      rw [h6] at h5
      have hK_eq : K' * (dist p q)^(-s) = C_common * C_T * M * (δ^s * (dist p q)^(-s)) := by
        simp [K'] <;> ring
      rw [hK_eq]
      exact_mod_cast h5
    have h2 : ∑ p ∈ P, ∑ q ∈ P.erase p, (K' * (dist p q)^(-s)) =
        K' * ∑ p ∈ P, ∑ q ∈ P.erase p, (dist p q)^(-s) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.mul_sum]
    rw [h2] at h1
    calc
      ∑ p ∈ P, ∑ q ∈ P.erase p, (((Tp p) ∩ (Tp q)).card : ℝ)
        ≤ K' * ∑ p ∈ P, ∑ q ∈ P.erase p, (dist p q)^(-s) := h1
      _ ≤ K' * (K_energy * C_P * (P.card : ℝ)^2) := by gcongr <;> exact h_energy
      _ = C_common * C_T * M * δ^s * K_energy * C_P * (P.card : ℝ)^2 := by ring

  have hPcard_pos : 0 < (P.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hP_nonempty

  -- d² bound WITHOUT hP_large:
  have h_d2_bound : (∑ ℓ ∈ U, (d ℓ : ℝ)^2) ≤
      (P.card : ℝ) * M * (1 + K) := by
    rw [h_sum_d2, h_split]
    have h1 : (∑ p ∈ P, (Tp p).card : ℝ) ≤ (P.card : ℝ) * M := hI_upper
    have h2 : ∑ p ∈ P, ∑ q ∈ P.erase p, (((Tp p) ∩ (Tp q)).card : ℝ) ≤
        C_common * C_T * M * δ^s * K_energy * C_P * (P.card : ℝ)^2 := h_off_bound
    have h3 : C_common * C_T * M * δ^s * K_energy * C_P * (P.card : ℝ)^2 =
        (P.card : ℝ) * M * K := by
      simp [hK_def] <;> ring
    rw [h3] at h2
    linarith

  have h_sum_pos : 0 < ∑ ℓ ∈ U, (d ℓ : ℝ)^2 := by
    have hI_pos : 0 < (∑ ℓ ∈ U, (d ℓ : ℝ)) := by
      rw [←hI]
      have h : 0 < (P.card : ℝ) * (M / 2) := by positivity
      linarith [hI_lower]
    have h_nonneg : 0 ≤ ∑ ℓ ∈ U, (d ℓ : ℝ)^2 :=
      Finset.sum_nonneg (fun ℓ _ => sq_nonneg (d ℓ : ℝ))
    by_cases h_case : 0 < ∑ ℓ ∈ U, (d ℓ : ℝ)^2
    · exact h_case
    · have h_le : ∑ ℓ ∈ U, (d ℓ : ℝ)^2 ≤ 0 := by exact Std.not_lt.mp h_case
      have h_eq : ∑ ℓ ∈ U, (d ℓ : ℝ)^2 = 0 := le_antisymm h_le h_nonneg
      have h4 : ∀ ℓ ∈ U, (d ℓ : ℝ)^2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)).mp h_eq
      have h3 : ∀ ℓ ∈ U, (d ℓ : ℝ) = 0 := by
        intro ℓ hℓ
        have h5 : (d ℓ : ℝ)^2 = 0 := h4 ℓ hℓ
        simpa using h5
      have h7 : ∑ ℓ ∈ U, (d ℓ : ℝ) = 0 := by
        apply Finset.sum_eq_zero
        intro ℓ _
        exact h3 ℓ ‹_›
      rw [h7] at hI_pos
      exact False.elim (lt_irrefl 0 hI_pos)

  have hS2_pos : 0 < ∑ ℓ ∈ U, (d ℓ : ℝ)^2 := h_sum_pos
  have h_cs : (∑ ℓ ∈ U, (d ℓ : ℝ))^2 ≤
      (U.card : ℝ) * (∑ ℓ ∈ U, (d ℓ : ℝ)^2) := cauchy_schwarz_card

  have h_main_ineq : (U.card : ℝ) ≥
      (∑ ℓ ∈ U, (d ℓ : ℝ))^2 / (∑ ℓ ∈ U, (d ℓ : ℝ)^2) := by
    have h' : (∑ ℓ ∈ U, (d ℓ : ℝ))^2 / (∑ ℓ ∈ U, (d ℓ : ℝ)^2) ≤
        (U.card : ℝ) * (∑ ℓ ∈ U, (d ℓ : ℝ)^2) / (∑ ℓ ∈ U, (d ℓ : ℝ)^2) :=
      div_le_div_of_nonneg_right h_cs (by linarith)
    have h'' : (U.card : ℝ) * (∑ ℓ ∈ U, (d ℓ : ℝ)^2) / (∑ ℓ ∈ U, (d ℓ : ℝ)^2) = (U.card : ℝ) := by
      exact mul_div_cancel_right₀ (U.card : ℝ) hS2_pos.ne'
    rw [h''] at h'
    exact h'

  have hI2 : (∑ ℓ ∈ U, (d ℓ : ℝ)) ≥ (P.card : ℝ) * (M / 2) := by
    rw [←hI]; exact hI_lower
  have h_nonneg_sum : 0 ≤ ∑ ℓ ∈ U, (d ℓ : ℝ) :=
    Finset.sum_nonneg (fun ℓ _ => Nat.cast_nonneg (d ℓ))
  have h_nonneg_lower : 0 ≤ (P.card : ℝ) * (M / 2) := by positivity
  have h_lower2 : ((P.card : ℝ) * (M / 2))^2 ≤ (∑ ℓ ∈ U, (d ℓ : ℝ))^2 := by
    have h_le : (P.card : ℝ) * (M / 2) ≤ ∑ ℓ ∈ U, (d ℓ : ℝ) := hI2
    nlinarith [h_nonneg_lower, h_nonneg_sum]

  have hK_nonneg : 0 ≤ K := by positivity
  have h_denom_pos : 0 < (P.card : ℝ) * M * (1 + K) := by positivity

  calc
    (U.card : ℝ)
      ≥ (∑ ℓ ∈ U, (d ℓ : ℝ))^2 / (∑ ℓ ∈ U, (d ℓ : ℝ)^2) := h_main_ineq
    _ ≥ ((P.card : ℝ) * (M / 2))^2 / (∑ ℓ ∈ U, (d ℓ : ℝ)^2) := by
      exact div_le_div_of_nonneg_right h_lower2 (by linarith)
    _ ≥ ((P.card : ℝ) * (M / 2))^2 / ((P.card : ℝ) * M * (1 + K)) := by
      have h_num_nonneg : 0 ≤ ((P.card : ℝ) * (M / 2))^2 := by positivity
      exact div_le_div_of_nonneg_left h_num_nonneg hS2_pos h_d2_bound
    _ = (P.card : ℝ) * M / (4 * (1 + K)) := by
      field_simp [hPcard_pos.ne', hM_pos.ne'] <;> ring

/-- When K ≤ 1, the no-hP_large bound simplifies to |U| ≥ |P|·M/8. -/
lemma global_2s_bound_no_hP_large_K_le_one
    {X : Type*} [PseudoMetricSpace X] [DecidableEq X]
    {δ s t C_P C_T M C_common K_energy : ℝ}
    (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1)
    (hs : 0 < s) (hst : s < t)
    (hCP_pos : 0 < C_P) (hCT_pos : 0 < C_T) (hM_pos : 0 < M)
    (hCcommon_pos : 0 < C_common) (hK_pos : 0 < K_energy)
    {P : Finset X}
    (hP_nonempty : P.Nonempty)
    (hP_sep : Set.Pairwise (P : Set X) (fun p q => δ ≤ dist p q))
    {Tp : X → Finset Tube}
    (hTp_card_lower : ∀ p ∈ P, (M / 2 : ℝ) ≤ (Tp p).card)
    (hTp_card_upper : ∀ p ∈ P, (Tp p).card ≤ M)
    (h_common_bound : ∀ p ∈ P, ∀ q ∈ P, p ≠ q →
      ((Tp p) ∩ (Tp q)).card ≤ C_common * C_T * M * (δ / dist p q)^s)
    (h_energy : ∑ p ∈ P, ∑ q ∈ P.erase p, (dist p q)^(-s) ≤
        K_energy * C_P * (P.card : ℝ)^2)
    (hK_le_one : C_common * C_P * C_T * K_energy * δ^s * (P.card : ℝ) ≤ 1) :
    ((P.biUnion Tp).card : ℝ) ≥ (P.card : ℝ) * M / 8 := by
  have h_main := global_2s_bound_no_hP_large
    hδ_pos hδ_le_one hs hst hCP_pos hCT_pos hM_pos hCcommon_pos hK_pos
    hP_nonempty hP_sep hTp_card_lower hTp_card_upper h_common_bound h_energy
  set K : ℝ := C_common * C_P * C_T * K_energy * δ^s * (P.card : ℝ) with hK_def
  have hK_le_one' : K ≤ 1 := hK_le_one
  have h1 : 1 + K ≤ 2 := by linarith
  have h2 : (P.card : ℝ) * M / (4 * (1 + K)) ≥ (P.card : ℝ) * M / 8 := by
    have h_pos : 0 < (P.card : ℝ) * M := by positivity
    gcongr
    <;> linarith
  exact le_trans h2 h_main

end DirecretisedFurstenbergEstimate.Global2sBound
