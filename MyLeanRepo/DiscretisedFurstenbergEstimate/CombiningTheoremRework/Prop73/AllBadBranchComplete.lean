module

/-
  AllBadBranchComplete — Complete all-tail-bad branch extraction.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.AllBadBranch
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.Statement
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.B1Integration
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable


noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73Restructure

open DiscretisedFurstenbergEstimate.CombiningTheorem
open DiscretisedFurstenbergEstimate.InductionConfigurations

/-- Telescoping product for Fin-indexed sequences in a field. -/
lemma telescoping_product_fin (n : ℕ) (f : Fin (n + 1) → ℝ) (hpos : ∀ i, 0 < f i) :
    (∏ j : Fin n, f (Fin.succ j) / f j.castSucc) = f (Fin.last n) / f 0 := by
  induction n with
  | zero =>
    have h_empty : (∏ j : Fin 0, f (Fin.succ j) / f j.castSucc) = 1 := by simp
    have h_last : Fin.last 0 = (0 : Fin 1) := by simp [Fin.last]
    have h0 : 0 < f 0 := hpos 0
    rw [h_empty, h_last]
    field_simp [h0.ne']
  | succ n ih =>
    let g : Fin (n + 1) → ℝ := fun k => f (Fin.succ k)
    have hpos' : ∀ i, 0 < g i := fun i => hpos (Fin.succ i)
    set F : Fin (n + 1) → ℝ := fun j => f (Fin.succ j) / f j.castSucc with hF
    have h_prod : (∏ j : Fin (n + 1), F j) = F 0 * ∏ i : Fin n, F i.succ :=
      Fin.prod_univ_succ F
    have h_eq1 : ∀ i : Fin n, F i.succ = g (Fin.succ i) / g i.castSucc := by
      intro i
      simp only [hF, g]
      have h1 : (Fin.succ i).castSucc = Fin.succ (i.castSucc) := by
        apply Fin.ext; simp
      rw [h1] <;> rfl
    have h_eq2 : F 0 = g 0 / f 0 := by
      simp only [hF, g] <;> rfl
    rw [h_prod, h_eq2]
    rw [Finset.prod_congr rfl (fun i _ => h_eq1 i)]
    rw [ih g hpos']
    have h_last : g (Fin.last n) = f (Fin.last (n + 1)) := by
      simp [g, Fin.last]
      <;> rfl
    rw [h_last]
    have h0 : 0 < f 0 := hpos 0
    have hg0 : 0 < g 0 := hpos' 0
    field_simp [h0.ne', hg0.ne'] <;> ring

/-- Complete all-tail-bad branch. -/
lemma all_bad_branch_complete
    {n_fine k m M MΔ M_Q : ℕ}
    {s ε_N η C_coarse C'_coarse C C' lam : ℝ}
    {K Δ_coarse δ δbar PΔ Pb α A CΔ C_Q : ℝ}
    (config : CTNiceConfiguration k s (Real.rpow (dyadicDelta k) (-lam)) M)
    (coarseConfig : CTNiceConfiguration m s CΔ MΔ)
    (fineConfig_Q : CTNiceConfiguration (k - m) s C_Q M_Q)
    (P : Finset (DyadicSquare k))
    (Q : DyadicSquare m)
    (Δ : Fin (n_fine + 2) → ℝ)
    (scaleClass : Fin (n_fine + 1) → ScaleClass)
    (Δ' : Fin (n_fine + 1) → ℝ)
    (G' B' : Finset (Fin n_fine))
    (j0 : Fin (n_fine + 1))
    (hnm : m ≤ k)
    (hj0 : j0 = 0)
    (h_all_bad : ∀ j ∈ (Finset.univ.erase j0), (scaleClass j).isBad)
    (hΔ_pos : ∀ i, 0 < Δ i)
    (hΔ_end : Δ (Fin.last (n_fine + 1)) = dyadicDelta k)
    (hm_eq2 : Δ 1 = dyadicDelta m)
    (hΔ'_def : ∀ i, Δ' i = Δ (Fin.succ i) / Δ 1)
    (hG'_def : G' = Finset.univ.filter (fun j => (scaleClass (Fin.succ j)).isGood))
    (hB'_def : B' = Finset.univ.filter (fun j => (scaleClass (Fin.succ j)).isBad))
    (hPb_def : Pb = (∏ j ∈ G', Real.rpow (Δ' j.castSucc / Δ' (Fin.succ j)) η) *
                        (∏ j ∈ B', Δ' (Fin.succ j) / Δ' j.castSucc))
    (hδbar_eq : δbar = dyadicDelta (k - m))
    (hδbar_pos : 0 < δbar)
    (hδbar_lt_one : δbar < 1)
    (hδ_pos : 0 < δ)
    (hδ_lt_one : δ < 1)
    (hδ_eq : δ = Δ_coarse * δbar)
    (hΔ_coarse_pos : 0 < Δ_coarse)
    (hΔ_lt_one : Δ_coarse < 1)
    (hK_pos : 0 < K)
    (hK_ge1 : 1 ≤ K)
    (hM_pos : 0 < M)
    (hMΔ_pos : 0 < MΔ)
    (hMQ_pos : 0 < M_Q)
    (hPΔ_pos : 0 < PΔ)
    (hP_sub : P ⊆ config.P₀)
    (hcoarse_P_eq : coarseConfig.P₀ = P.image (InductionConfigurations.containingSquare hnm))
    (hQ : Q ∈ coarseConfig.P₀)
    (hfine_P_eq : fineConfig_Q.P₀ =
        (P.filter (fun p => InductionConfigurations.squareContained hnm p Q)).image
          (InductionConfigurations.squareHomothety hnm Q))
    (h_card_ineq : K * (config.T₀.card : ℝ) * (MΔ : ℝ) * (M_Q : ℝ) ≥
        (coarseConfig.T₀.card : ℝ) * (fineConfig_Q.T₀.card : ℝ) * (M : ℝ))
    (h_coarse_bound : (coarseConfig.T₀.card : ℝ) ≥
        Real.rpow (Real.log (1 / Δ_coarse)) (-C_coarse) * (MΔ : ℝ) *
        Real.rpow K (-C'_coarse) * Real.rpow δ (C'_coarse * lam) *
        Real.rpow Δ_coarse (-s + ε_N) * PΔ)
    (hL_ge1 : 1 ≤ Real.log (1 / δ))
    (hL_ge_A : Real.log (1 / δ) ≥ A)
    (hK_poly : K ≤ A * (Real.log (1 / δ)) ^ α)
    (hC_coarse_nonneg : 0 ≤ C_coarse)
    (hC'_coarse_ge1 : 1 ≤ C'_coarse)
    (hC_pos : 0 < C)
    (hC_ge_simple : C ≥ C_coarse + (1 + α) * (C'_coarse + 1))
    (hC'_lam_ge : C'_coarse * lam ≤ C' * lam)
    (hs1 : s < 1)
    (hεN : 0 < ε_N)
    (hA_pos : 0 < A)
    (hα_pos : 0 < α)
    (h_product : combiningLowerBound (dyadicDelta k) (M : ℝ) C C' lam s ε_N η (n_fine + 1) Δ scaleClass =
        Real.rpow (Real.log (1 / dyadicDelta k)) (-C) * (M : ℝ) *
        Real.rpow (dyadicDelta k) (C' * lam) * Real.rpow (dyadicDelta k) (-s + ε_N) * (PΔ * Pb))
    (hδ_def : δ = dyadicDelta k) :
    (config.T₀.card : ENNReal) ≥
      ENNReal.ofReal (combiningLowerBound (dyadicDelta k) (M : ℝ) C C' lam s ε_N η (n_fine + 1) Δ scaleClass) := by
  let shift : Fin n_fine → Fin (n_fine + 1) := Fin.succ
  -- Step 1: B' = univ, G' = empty
  have hB'_univ : B' = (Finset.univ : Finset (Fin n_fine)) := by
    ext j
    have h_j_in_erase : shift j ∈ (Finset.univ.erase j0) := by
      rw [hj0]; simp [shift, Fin.ext_iff] <;> omega
    have hbad : (scaleClass (shift j)).isBad := h_all_bad (shift j) h_j_in_erase
    have h_goal : j ∈ B' := by
      rw [hB'_def]
      simpa using hbad
    simpa using h_goal
  have hG'_empty : G' = (∅ : Finset (Fin n_fine)) := by
    ext j
    have h_j_in_erase : shift j ∈ (Finset.univ.erase j0) := by
      rw [hj0]; simp [shift, Fin.ext_iff] <;> omega
    have hbad : (scaleClass (shift j)).isBad := h_all_bad (shift j) h_j_in_erase
    have hbad' : (scaleClass (shift j)).isBad = true := by exact Eq.symm ((fun {x y} => Bool.not_inj_iff.mp) (congrArg not (id (Eq.symm hbad))))
    have h_is_bad : scaleClass (shift j) = .bad := by
      cases h2 : scaleClass (shift j)
      · simp [ScaleClass.isBad, h2] at hbad'
      · simp [ScaleClass.isBad, h2] at hbad'
      · rfl
    have h_ng'' : (scaleClass (Fin.succ j)).isGood = false := by
      have h_shift : shift j = Fin.succ j := rfl
      have h_bad2 : scaleClass (Fin.succ j) = .bad := by
        rw [←h_shift]; exact h_is_bad
      rw [h_bad2]
      simp [ScaleClass.isGood]
    have h_goal : j ∉ G' := by
      rw [hG'_def]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simpa using h_ng''
    simpa using h_goal
  have hΔ'_pos : ∀ i, 0 < Δ' i := by
    intro i; rw [hΔ'_def i]; exact div_pos (hΔ_pos (Fin.succ i)) (hΔ_pos 1)
  have h_succ0 : Fin.succ (0 : Fin (n_fine + 1)) = (1 : Fin (n_fine + 2)) := by
    apply Fin.ext; simp
  have hΔ'_start : Δ' 0 = 1 := by
    rw [hΔ'_def 0, h_succ0]
    have h_pos1 : 0 < Δ 1 := hΔ_pos 1
    have h : Δ 1 / Δ 1 = 1 := by
      rw [div_self h_pos1.ne']
    exact h
  have hΔ'_end : Δ' (Fin.last n_fine) = δbar := by
    rw [hΔ'_def (Fin.last n_fine)]
    have h_succ_last : Fin.succ (Fin.last n_fine) = Fin.last (n_fine + 1) := by
      apply Fin.ext; simp [Fin.last] <;> omega
    rw [h_succ_last, hΔ_end, hm_eq2]
    have h7 : dyadicDelta k / dyadicDelta m = dyadicDelta (k - m) := by
      have h8 : m + (k - m) = k := by omega
      have h91 : (2 : ℝ)^m * (2 : ℝ)^(k - m) = (2 : ℝ)^k := by
        rw [← pow_add] <;> rw [h8]
      have h9 : dyadicDelta k = dyadicDelta m * dyadicDelta (k - m) := by
        simp only [dyadicDelta]; field_simp <;> rw [h91] <;> ring
      rw [h9]
      have h10 : 0 < dyadicDelta m := dyadicDelta_pos m
      field_simp [h10.ne'] <;> ring
    rw [h7, hδbar_eq]
  -- Telescoping product
  have hPb_eq : Pb = δbar := by
    rw [hPb_def, hG'_empty, hB'_univ]
    simp only [Finset.prod_empty, mul_one]
    have h_telescope : (∏ j : Fin n_fine, Δ' (Fin.succ j) / Δ' j.castSucc) =
        Δ' (Fin.last n_fine) / Δ' 0 := telescoping_product_fin n_fine Δ' hΔ'_pos
    rw [h_telescope, hΔ'_end, hΔ'_start] <;> ring
  -- Step 2: fineConfig_Q.P₀.Nonempty
  have hfine_P0_nonempty : fineConfig_Q.P₀.Nonempty := by
    have hQ_in_image : Q ∈ P.image (InductionConfigurations.containingSquare hnm) := by
      rw [←hcoarse_P_eq]; exact hQ
    rcases Finset.mem_image.mp hQ_in_image with ⟨p, hp, h_eq⟩
    have h_contained : InductionConfigurations.squareContained hnm p Q :=
      (InductionConfigurations.containingSquare_iff hnm p Q).mp h_eq
    have h_p_in_filter : p ∈ P.filter (fun p => InductionConfigurations.squareContained hnm p Q) :=
      Finset.mem_filter.mpr ⟨hp, h_contained⟩
    rw [hfine_P_eq]
    refine' ⟨InductionConfigurations.squareHomothety hnm Q p, _⟩
    exact Finset.mem_image.mpr ⟨p, h_p_in_filter, rfl⟩
  -- Step 3: TQ_card ≥ MQ_Q
  have hTQ_ge_MQ : (fineConfig_Q.T₀.card : ℝ) ≥ (M_Q : ℝ) := by
    rcases hfine_P0_nonempty with ⟨p, hp⟩
    have h1 : fineConfig_Q.tubeFamily p hp ⊆ fineConfig_Q.T₀ := fineConfig_Q.h_subset p hp
    have h2 : (fineConfig_Q.tubeFamily p hp).card = M_Q := fineConfig_Q.h_size p hp
    have h3 : (fineConfig_Q.tubeFamily p hp).card ≤ fineConfig_Q.T₀.card := Finset.card_le_card h1
    rw [h2] at h3
    exact_mod_cast h3
  -- Step 4: Simplified card inequality
  have h_card_simple : K * (config.T₀.card : ℝ) * (MΔ : ℝ) ≥
      (coarseConfig.T₀.card : ℝ) * (M : ℝ) := by
    have h4 : K * (config.T₀.card : ℝ) * (MΔ : ℝ) * (M_Q : ℝ) ≥
        (coarseConfig.T₀.card : ℝ) * (fineConfig_Q.T₀.card : ℝ) * (M : ℝ) := h_card_ineq
    have h5 : (coarseConfig.T₀.card : ℝ) * (fineConfig_Q.T₀.card : ℝ) * (M : ℝ) ≥
        (coarseConfig.T₀.card : ℝ) * (M_Q : ℝ) * (M : ℝ) := by
      gcongr <;> exact_mod_cast hTQ_ge_MQ
    have h6 : K * (config.T₀.card : ℝ) * (MΔ : ℝ) * (M_Q : ℝ) ≥
        (coarseConfig.T₀.card : ℝ) * (M_Q : ℝ) * (M : ℝ) := le_trans h5 h4
    have hMQ_pos' : 0 < (M_Q : ℝ) := by exact_mod_cast hMQ_pos
    nlinarith
  -- Step 5: Lower bound on T_card from coarse bound
  have hK_pos' : 0 < K := hK_pos
  have hMΔ_pos' : 0 < (MΔ : ℝ) := by exact_mod_cast hMΔ_pos
  have h_pos : 0 < K * (MΔ : ℝ) := mul_pos hK_pos' hMΔ_pos'
  have h_ne : (K * (MΔ : ℝ)) ≠ 0 := h_pos.ne'
  have h_card_simple2 : (config.T₀.card : ℝ) * (K * (MΔ : ℝ)) ≥
      (coarseConfig.T₀.card : ℝ) * (M : ℝ) := by
    have h : K * (config.T₀.card : ℝ) * (MΔ : ℝ) = (config.T₀.card : ℝ) * (K * (MΔ : ℝ)) := by ring
    rw [h] at h_card_simple
    exact h_card_simple
  have h_div : (config.T₀.card : ℝ) ≥
      (coarseConfig.T₀.card : ℝ) * (M : ℝ) / (K * (MΔ : ℝ)) := by
    have h_eq : (config.T₀.card : ℝ) = ((config.T₀.card : ℝ) * (K * (MΔ : ℝ))) / (K * (MΔ : ℝ)) := by
      field_simp [h_ne] <;> ring
    rw [h_eq]
    gcongr
  have hT_lower : (config.T₀.card : ℝ) ≥
      Real.rpow (Real.log (1 / Δ_coarse)) (-C_coarse) * (M : ℝ) *
      Real.rpow K (-(C'_coarse + 1)) * Real.rpow δ (C'_coarse * lam) *
      Real.rpow Δ_coarse (-s + ε_N) * PΔ := by
    have h_pos2 : 0 < (M : ℝ) / (K * (MΔ : ℝ)) := by positivity
    have h_coarse_le : (Real.rpow (Real.log (1 / Δ_coarse)) (-C_coarse) * (MΔ : ℝ) *
          Real.rpow K (-C'_coarse) * Real.rpow δ (C'_coarse * lam) *
          Real.rpow Δ_coarse (-s + ε_N) * PΔ) ≤ (coarseConfig.T₀.card : ℝ) := h_coarse_bound
    have hM_pos' : 0 < (M : ℝ) := by exact_mod_cast hM_pos
    have h_coarse_mul :
        (Real.rpow (Real.log (1 / Δ_coarse)) (-C_coarse) * (MΔ : ℝ) *
          Real.rpow K (-C'_coarse) * Real.rpow δ (C'_coarse * lam) *
          Real.rpow Δ_coarse (-s + ε_N) * PΔ) * (M : ℝ) ≤
        (coarseConfig.T₀.card : ℝ) * (M : ℝ) :=
      mul_le_mul_of_nonneg_right h_coarse_le hM_pos'.le
    have h_coarse_scaled : (coarseConfig.T₀.card : ℝ) * (M : ℝ) / (K * (MΔ : ℝ)) ≥
        (Real.rpow (Real.log (1 / Δ_coarse)) (-C_coarse) * (MΔ : ℝ) *
          Real.rpow K (-C'_coarse) * Real.rpow δ (C'_coarse * lam) *
          Real.rpow Δ_coarse (-s + ε_N) * PΔ) * (M : ℝ) / (K * (MΔ : ℝ)) :=
      div_le_div_of_nonneg_right h_coarse_mul h_pos.le
    have hK_ne : K ≠ 0 := hK_pos'.ne'
    have hMΔ_ne : (MΔ : ℝ) ≠ 0 := hMΔ_pos'.ne'
    have h_rpow_neg1 : Real.rpow K (-1 : ℝ) = K⁻¹ := Real.rpow_neg_one K
    have h_inv : K⁻¹ = 1 / K := by simp
    have h_rpow_add : Real.rpow K (-(C'_coarse + 1)) =
        Real.rpow K (-C'_coarse) * Real.rpow K (-1 : ℝ) := by
      have h_exp : -(C'_coarse + 1) = (-C'_coarse) + (-1 : ℝ) := by ring
      rw [h_exp]
      exact Real.rpow_add hK_pos (-C'_coarse) (-1 : ℝ)
    have h_alg : (Real.rpow (Real.log (1 / Δ_coarse)) (-C_coarse) * (MΔ : ℝ) *
            Real.rpow K (-C'_coarse) * Real.rpow δ (C'_coarse * lam) *
            Real.rpow Δ_coarse (-s + ε_N) * PΔ) * (M : ℝ) / (K * (MΔ : ℝ)) =
        Real.rpow (Real.log (1 / Δ_coarse)) (-C_coarse) * (M : ℝ) *
            Real.rpow K (-(C'_coarse + 1)) * Real.rpow δ (C'_coarse * lam) *
            Real.rpow Δ_coarse (-s + ε_N) * PΔ := by
      set A := Real.rpow (Real.log (1 / Δ_coarse)) (-C_coarse) with hA
      set B := Real.rpow δ (C'_coarse * lam) with hB
      set D := Real.rpow Δ_coarse (-s + ε_N) with hD
      set E := Real.rpow K (-C'_coarse) with hE
      have h1 : A * (MΔ : ℝ) * E * B * D * PΔ * (M : ℝ) / (K * (MΔ : ℝ)) =
          A * (M : ℝ) * (E / K) * B * D * PΔ := by
        field_simp [hK_ne, hMΔ_ne] <;> ring
      have h2 : E / K = E * Real.rpow K (-1 : ℝ) := by
        rw [h_rpow_neg1, h_inv] <;> field_simp [hK_ne] <;> ring
      have h3 : E * Real.rpow K (-1 : ℝ) = Real.rpow K (-(C'_coarse + 1)) := by
        rw [←h_rpow_add] <;> rfl
      rw [h1, h2, h3] <;> ring
    calc (config.T₀.card : ℝ)
      ≥ (coarseConfig.T₀.card : ℝ) * (M : ℝ) / (K * (MΔ : ℝ)) := h_div
    _ ≥ (Real.rpow (Real.log (1 / Δ_coarse)) (-C_coarse) * (MΔ : ℝ) *
            Real.rpow K (-C'_coarse) * Real.rpow δ (C'_coarse * lam) *
            Real.rpow Δ_coarse (-s + ε_N) * PΔ) * (M : ℝ) / (K * (MΔ : ℝ)) := h_coarse_scaled
    _ = Real.rpow (Real.log (1 / Δ_coarse)) (-C_coarse) * (M : ℝ) *
            Real.rpow K (-(C'_coarse + 1)) * Real.rpow δ (C'_coarse * lam) *
            Real.rpow Δ_coarse (-s + ε_N) * PΔ := h_alg
  -- Step 6-7: Absorption + final assembly
  let L := Real.log (1 / δ)
  have h_product' : combiningLowerBound δ (M : ℝ) C C' lam s ε_N η (n_fine + 1) Δ scaleClass =
      Real.rpow L (-C) * (M : ℝ) * Real.rpow δ (C' * lam) *
      Real.rpow δ (-s + ε_N) * (PΔ * δbar) := by
    have h1 : δ = dyadicDelta k := by simp [hδ_def]
    rw [h1, h_product, hPb_eq] <;> simp [L, hδ_def] <;> ring
  have h_final : (config.T₀.card : ℝ) ≥
      combiningLowerBound δ (M : ℝ) C C' lam s ε_N η (n_fine + 1) Δ scaleClass :=
    all_bad_final_assembly
      (hK_pos := hK_pos) (hM_pos := by exact_mod_cast hM_pos)
      (hΔ_coarse_pos := hΔ_coarse_pos) (hΔ_lt_one := hΔ_lt_one)
      (hδ_pos := hδ_pos) (hδ_lt_one := hδ_lt_one)
      (hδbar_pos := hδbar_pos) (hδbar_lt_one := hδbar_lt_one)
      (hδ_eq := hδ_eq)
      (hL_ge1 := hL_ge1) (hL_ge_A := hL_ge_A) (hL_def := rfl)
      (hA_pos := hA_pos) (hα_pos := hα_pos)
      (hK_ge1 := hK_ge1) (hK_poly := hK_poly)
      (hC_coarse_nonneg := hC_coarse_nonneg)
      (hC'_coarse_ge1 := hC'_coarse_ge1)
      (hC_pos := hC_pos) (hC_ge := hC_ge_simple)
      (hC'_lam_ge := hC'_lam_ge)
      (hs1 := hs1) (hεN := hεN)
      (hPΔ_pos := hPΔ_pos)
      (hT_lower := hT_lower)
      (h_product := h_product')
  have h_eq : combiningLowerBound (dyadicDelta k) (M : ℝ) C C' lam s ε_N η (n_fine + 1) Δ scaleClass =
      combiningLowerBound δ (M : ℝ) C C' lam s ε_N η (n_fine + 1) Δ scaleClass := by
    congr; simp [hδ_def]
  have h1 : (config.T₀.card : ENNReal) = ENNReal.ofReal (config.T₀.card : ℝ) := by simp
  rw [h1]
  rw [h_eq]
  exact ENNReal.ofReal_le_ofReal h_final

end DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73Restructure
