module

/-
  core_v2_sorry2 — Close the recursive fine CombiningConfig sorry.

  Strategy:
  1. S_full = normalized indices of ALL config.P₀ squares in Q
  2. S' = normalized indices of fineConfig'_tail.P₀ (B1-selected subset)
  3. S' ⊆ S_full with density card(S_full) ≤ K * card(S')
  4. Transfer coarse uniformity to RangeUniformityProp on S_full
  5. Apply basic_uniformization_dyadic to get uniform S'' ⊆ S'
  6. Transfer between-scales per-scale for normal/good scales
  7. Build new NiceConfiguration with P₀ = S'' squares
  8. Build CombiningConfig and apply IH

  Whiteprint node: combining_theorem_rework / core_v2_sorry2
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.FineConfigSublemma
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.FineIntegrationHelpers
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.AmplificationProof
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.TailUniformisationConsumer
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.BetweenScalesTransfer
public import MyLeanRepo.DiscretisedFurstenbergEstimate.GeometricIntersection
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FormatConversionLemmas
public import MyLeanRepo.DiscretisedFurstenbergEstimate.BasicUniformization
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.CoarseIntegrationLemmas
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DiscretisedFurstenbergEstimate.CombiningTheorem
open DiscretisedFurstenbergEstimate.InductionConfigurations
open DiscretisedFurstenbergEstimate.BasicUniformization

/-! ========================================================================
   Helper: density_dyadic_at_scale

   Given uniform sets S and S'' with S'' ⊆ S and per-level density,
   prove the dyadic square count density at one scale j.
   ======================================================================== -/

lemma density_dyadic_at_scale
    {n_fine : ℕ} {a : Fin (n_fine + 1) → ℕ}
    {S S'' : Finset (ℤ × ℤ)} {N N'' : Fin n_fine → ℕ}
    (h_unif_S : RangeUniformityProp n_fine a S N)
    (h_unif_S'' : RangeUniformityProp n_fine a S'' N'')
    (hS''_sub : S'' ⊆ S)
    (h_a_mono : ∀ j : Fin n_fine, a j.castSucc ≤ a (Fin.succ j))
    (h_a_last : ∀ i, a i ≤ a (Fin.last n_fine))
    (M : ℝ) (hM_pos : 0 < M)
    (h_per_level : ∀ j : Fin n_fine, (N'' j : ℝ) ≥ (N j : ℝ) / (M * (4 : ℝ)^n_fine))
    (δbar : ℝ) (nδ : ℕ) (hδbar_eq : δbar = dyadicDelta nδ)
    (h_a_last_eq : a (Fin.last n_fine) = nδ)
    (Δ' : Fin (n_fine + 1) → ℝ)
    (hΔ'_spec : ∀ i, Δ' i = dyadicDelta (a i))
    (j : Fin n_fine)
    (c : ℝ) (hc_pos : 0 < c)
    (hc_eq : c = 1 / (2 * M * (4 : ℝ)^n_fine)) :
    ∀ (a_idx b_idx : ℤ),
      (setFromIndices δbar S'' ∩ BasicUniformization.dyadicSquare (Δ' j.castSucc) a_idx b_idx).Nonempty →
      (OSUniformisation.dyadicSquareCount (Δ' (Fin.succ j))
        (setFromIndices δbar S'' ∩ OSUniformisation.dyadicSquare (Δ' j.castSucc) a_idx b_idx) : ENNReal) ≥
      ENNReal.ofReal c *
      (OSUniformisation.dyadicSquareCount (Δ' (Fin.succ j))
        (setFromIndices δbar S ∩ OSUniformisation.dyadicSquare (Δ' j.castSucc) a_idx b_idx) : ENNReal) := by
  intro a_idx b_idx h_nonempty
  let g : ℤ × ℤ := (a_idx, b_idx)
  let a_fine := a (Fin.succ j)
  let a_coarse := a j.castSucc
  let k := a (Fin.last n_fine)
  have h_k_eq_nδ : k = nδ := h_a_last_eq
  have h_coarse_le_fine : a_coarse ≤ a_fine := h_a_mono j
  have h_fine_le_k : a_fine ≤ k := h_a_last (Fin.succ j)
  let m_fine := k - a_fine
  let m_coarse := a_fine - a_coarse
  let fineSq_S'' := S''.image (parentBy m_fine)
  let filtered_S'' := fineSq_S''.filter (fun idx => parentBy m_coarse idx = g)
  let fineSq_S := S.image (parentBy m_fine)
  let filtered_S := fineSq_S.filter (fun idx => parentBy m_coarse idx = g)
  have h_bridge_S'' := OSUniformisation.dyadicSquareCount_setFromIndices_inter k a_fine a_coarse
    h_coarse_le_fine h_fine_le_k S'' g
  have h_bridge_S := OSUniformisation.dyadicSquareCount_setFromIndices_inter k a_fine a_coarse
    h_coarse_le_fine h_fine_le_k S g
  have h_fine_eq : dyadicDelta a_fine = Δ' (Fin.succ j) := (hΔ'_spec (Fin.succ j)).symm
  have h_coarse_eq : dyadicDelta a_coarse = Δ' j.castSucc := (hΔ'_spec j.castSucc).symm
  have h_k_eq2 : dyadicDelta k = δbar := by
    rw [h_k_eq_nδ, hδbar_eq]
  have h_count_S'' : OSUniformisation.dyadicSquareCount (Δ' (Fin.succ j))
      (setFromIndices δbar S'' ∩ OSUniformisation.dyadicSquare (Δ' j.castSucc) a_idx b_idx) =
      ↑filtered_S''.card := by
    have h_g : g = (a_idx, b_idx) := by ext <;> rfl
    rw [h_fine_eq, h_coarse_eq, h_k_eq2, h_g] at h_bridge_S''
    exact h_bridge_S''
  have h_count_S : OSUniformisation.dyadicSquareCount (Δ' (Fin.succ j))
      (setFromIndices δbar S ∩ OSUniformisation.dyadicSquare (Δ' j.castSucc) a_idx b_idx) =
      ↑filtered_S.card := by
    have h_g : g = (a_idx, b_idx) := by ext <;> rfl
    rw [h_fine_eq, h_coarse_eq, h_k_eq2, h_g] at h_bridge_S
    exact h_bridge_S
  rcases h_nonempty with ⟨x, hx⟩
  have hx_in_S'' : x ∈ setFromIndices δbar S'' := hx.1
  have hx_coarse : x ∈ OSUniformisation.dyadicSquare (Δ' j.castSucc) a_idx b_idx := hx.2
  rcases Set.mem_iUnion₂.mp hx_in_S'' with ⟨idx, hidx, hx_square⟩
  have hδk : δbar = dyadicDelta k := by rw [h_k_eq_nδ, hδbar_eq]
  have hx_square_k : x ∈ OSUniformisation.dyadicSquare (dyadicDelta k) idx.1 idx.2 := by
    rw [hδk] at hx_square; exact hx_square
  have hx_coarse_k : x ∈ OSUniformisation.dyadicSquare (dyadicDelta a_coarse) a_idx b_idx := by
    simpa [h_coarse_eq] using hx_coarse
  let p := parentBy m_fine idx
  have hp_in_img : p ∈ fineSq_S'' := Finset.mem_image.mpr ⟨idx, hidx, rfl⟩
  have h_inter : (OSUniformisation.dyadicSquare (dyadicDelta k) idx.1 idx.2 ∩
      OSUniformisation.dyadicSquare (dyadicDelta a_coarse) a_idx b_idx).Nonempty :=
    ⟨x, hx_square_k, hx_coarse_k⟩
  have h_rewrite : k - (m_fine + m_coarse) = a_coarse := by
    dsimp only [m_fine, m_coarse]; omega
  have h_le : m_fine + m_coarse ≤ k := by
    dsimp only [m_fine, m_coarse]; omega
  have h_total : parentBy (m_fine + m_coarse) idx = g := by
    have h_inter' : (OSUniformisation.dyadicSquare (dyadicDelta k) idx.1 idx.2 ∩
        OSUniformisation.dyadicSquare (dyadicDelta (k - (m_fine + m_coarse))) g.1 g.2).Nonempty := by
      rw [h_rewrite]; exact h_inter
    exact OSUniformisation.dyadicSquare_inter_parentBy h_le idx g h_inter'
  have hp_filter : parentBy m_coarse p = g := by
    have h_comp : parentBy m_coarse (parentBy m_fine idx) = parentBy (m_fine + m_coarse) idx := by
      have h := parentBy_comp m_coarse m_fine idx
      rw [add_comm m_coarse m_fine] at h; exact h
    exact h_comp.trans h_total
  have h_p_in_filtered : p ∈ filtered_S'' := by
    simp only [filtered_S'', Finset.mem_filter]; exact ⟨hp_in_img, hp_filter⟩
  have hS''_nonzero : filtered_S''.card ≠ 0 :=
    Finset.card_ne_zero.mpr ⟨p, h_p_in_filtered⟩
  have h_sl_raw := OSUniformisation.single_level_density h_unif_S h_unif_S'' M hM_pos h_per_level j g hS''_sub hS''_nonzero
  have h_sl : (filtered_S''.card : ℝ) ≥ c * (filtered_S.card : ℝ) := by
    dsimp only [filtered_S'', filtered_S] at h_sl_raw
    rw [hc_eq] at *
    <;> exact h_sl_raw
  rw [h_count_S'', h_count_S]
  have h_enn : (↑filtered_S''.card : ENNReal) ≥ ENNReal.ofReal c * (↑filtered_S.card : ENNReal) := by
    have h1 : (↑filtered_S''.card : ENNReal) = ENNReal.ofReal (filtered_S''.card : ℝ) := by simp
    have h2 : (↑filtered_S.card : ENNReal) = ENNReal.ofReal (filtered_S.card : ℝ) := by simp
    rw [h1, h2]
    have h3 : ENNReal.ofReal (filtered_S''.card : ℝ) ≥ ENNReal.ofReal (c * (filtered_S.card : ℝ)) :=
      ENNReal.ofReal_le_ofReal h_sl
    have h4 : ENNReal.ofReal (c * (filtered_S.card : ℝ)) =
        ENNReal.ofReal c * ENNReal.ofReal (filtered_S.card : ℝ) := by
      rw [ENNReal.ofReal_mul] <;> positivity
    rw [h4] at h3; exact h3
  exact h_enn

/-! ========================================================================
   Helper: transfer_between_one_scale

   Transfer an IsSetBetweenScales property from S to S'' at one scale,
   using the dyadic density lemma and uniformisation_Sset_transfer.
   ======================================================================== -/

lemma transfer_between_one_scale
    {n_fine : ℕ} {a : Fin (n_fine + 1) → ℕ}
    {S S'' : Finset (ℤ × ℤ)} {N N'' : Fin n_fine → ℕ}
    (h_unif_S : RangeUniformityProp n_fine a S N)
    (h_unif_S'' : RangeUniformityProp n_fine a S'' N'')
    (hS''_sub : S'' ⊆ S)
    (h_a0 : a 0 = 0)
    (h_a_mono : ∀ j : Fin n_fine, a j.castSucc ≤ a (Fin.succ j))
    (h_a_last : ∀ i, a i ≤ a (Fin.last n_fine))
    (h_unit_S : ∀ idx ∈ S, 0 ≤ idx.1 ∧ 0 ≤ idx.2 ∧
      idx.1 < (2 : ℤ)^(a (Fin.last n_fine)) ∧ idx.2 < (2 : ℤ)^(a (Fin.last n_fine)))
    (h_unit_S'' : ∀ idx ∈ S'', 0 ≤ idx.1 ∧ 0 ≤ idx.2 ∧
      idx.1 < (2 : ℤ)^(a (Fin.last n_fine)) ∧ idx.2 < (2 : ℤ)^(a (Fin.last n_fine)))
    (M : ℝ) (hM_pos : 0 < M)
    (h_per_level : ∀ j : Fin n_fine, (N'' j : ℝ) ≥ (N j : ℝ) / (M * (4 : ℝ)^n_fine))
    (δbar : ℝ) (nδ : ℕ) (hδbar_eq : δbar = dyadicDelta nδ)
    (h_a_last_eq : a (Fin.last n_fine) = nδ)
    (Δ' : Fin (n_fine + 1) → ℝ)
    (hΔ'_spec : ∀ i, Δ' i = dyadicDelta (a i))
    (hΔ'_pos : ∀ i, 0 < Δ' i)
    (hΔ'_dyadic : ∀ i, Δ' i ∈ dyadicScales)
    (j : Fin n_fine)
    (s C_j : ℝ) (hs_nonneg : 0 ≤ s) (hC_j_pos : 0 < C_j)
    (h_between_S : OSUniformisation.IsSetBetweenScales
        (setFromIndices δbar S) (Δ' (Fin.succ j)) (Δ' j.castSucc) s C_j) :
    OSUniformisation.IsSetBetweenScales (setFromIndices δbar S'')
      (Δ' (Fin.succ j)) (Δ' j.castSucc) s
      (9 * C_j * 2 * M * (4 : ℝ)^n_fine) := by
  let c : ℝ := 1 / (2 * M * (4 : ℝ)^n_fine)
  have hc_pos : 0 < c := by positivity
  have hc_eq : c = 1 / (2 * M * (4 : ℝ)^n_fine) := by rfl
  have hdensity_dyadic := density_dyadic_at_scale
    h_unif_S h_unif_S'' hS''_sub h_a_mono h_a_last M hM_pos h_per_level
    δbar nδ hδbar_eq h_a_last_eq Δ' hΔ'_spec j c hc_pos hc_eq
  have hδ_fine_pos : 0 < Δ' (Fin.succ j) := hΔ'_pos (Fin.succ j)
  have hδ_fine_dyadic : Δ' (Fin.succ j) ∈ dyadicScales := hΔ'_dyadic (Fin.succ j)
  have hδ_coarse_pos : 0 < Δ' j.castSucc := hΔ'_pos j.castSucc
  have hδ_fine_le_coarse : Δ' (Fin.succ j) ≤ Δ' j.castSucc := by
    have h : a j.castSucc ≤ a (Fin.succ j) := h_a_mono j
    have h2 : dyadicDelta (a (Fin.succ j)) ≤ dyadicDelta (a j.castSucc) := dyadicDelta_anti h
    have h3 : Δ' (Fin.succ j) = dyadicDelta (a (Fin.succ j)) := hΔ'_spec (Fin.succ j)
    have h4 : Δ' j.castSucc = dyadicDelta (a j.castSucc) := hΔ'_spec j.castSucc
    rw [h3, h4]
    exact h2
  have hP_bounded : Bornology.IsBounded (setFromIndices δbar S) := by
    rw [hδbar_eq]; exact setFromIndices_isBounded nδ S
  have hP''_bounded : Bornology.IsBounded (setFromIndices δbar S'') := by
    rw [hδbar_eq]; exact setFromIndices_isBounded nδ S''
  have hsub : setFromIndices δbar S'' ⊆ setFromIndices δbar S :=
    setFromIndices_subset hS''_sub
  have h_result := OSUniformisation.uniformisation_Sset_transfer
    hδ_fine_pos hδ_fine_dyadic hδ_coarse_pos hδ_fine_le_coarse
    hs_nonneg hC_j_pos hc_pos hP_bounded hP''_bounded h_between_S hsub hdensity_dyadic
  have h_const : 9 * C_j / c = 9 * C_j * 2 * M * (4 : ℝ)^n_fine := by
    dsimp only [c]
    have hpos : (0 : ℝ) < 2 * M * (4 : ℝ)^n_fine := by positivity
    field_simp [hpos.ne'] <;> ring
  rw [h_const] at h_result
  exact h_result

/-- Weaken IsDeltaSSet to a larger constant C'. -/
lemma isDeltaSSet_weaken_C
    {P : Set (EuclideanSpace ℝ (Fin 2))} {δ s C C' : ℝ}
    (h : IsDeltaSSet δ s C P)
    (hC_le : C ≤ C') (hC'_pos : 0 < C') :
    IsDeltaSSet δ s C' P := by
  exact ⟨h.1, h.2.1, hC'_pos, h.2.2.2.1,
    fun x r hr =>
      have h6 : ENNReal.ofReal C ≤ ENNReal.ofReal C' := ENNReal.ofReal_le_ofReal hC_le
      have h7 : ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
          (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) ≤
          ENNReal.ofReal C' * (ENNReal.ofReal r) ^ s *
          (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by
        gcongr
      le_trans (h.2.2.2.2 x r hr) h7⟩

/-- Weaken IsSetBetweenScales to a larger constant C'. -/
lemma between_scales_weaken_C
    {P : Set (EuclideanSpace ℝ (Fin 2))} {δ_fine δ_coarse s C C' : ℝ}
    (h : OSUniformisation.IsSetBetweenScales P δ_fine δ_coarse s C)
    (hC_le : C ≤ C') (hC'_pos : 0 < C') :
    OSUniformisation.IsSetBetweenScales P δ_fine δ_coarse s C' := by
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, hC'_pos,
    fun i j hnonempty =>
      isDeltaSSet_weaken_C (h.2.2.2.2.2 i j hnonempty) hC_le hC'_pos⟩

/-- Weaken IsRegularBetweenScales to larger constants. -/
lemma regular_between_scales_weaken
    {P : Set (EuclideanSpace ℝ (Fin 2))} {δ_fine δ_coarse s C K C' K' : ℝ}
    (h : OSUniformisation.IsRegularBetweenScales P δ_fine δ_coarse s C K)
    (hC_le : C ≤ C') (hK_le : K ≤ K') (hC'_pos : 0 < C') (hK'_pos : 0 < K') :
    OSUniformisation.IsRegularBetweenScales P δ_fine δ_coarse s C' K' := by
  have h1' : OSUniformisation.IsSetBetweenScales P δ_fine δ_coarse s C' :=
    between_scales_weaken_C h.1 hC_le hC'_pos
  have h2 : 0 < K := h.2.1
  have h3 : ∀ (i j : ℤ), (P ∩ OSUniformisation.dyadicSquare δ_coarse i j).Nonempty →
      (Metric.externalCoveringNumber (Real.sqrt (δ_fine / δ_coarse)).toNNReal
         (OSUniformisation.homothetyS δ_coarse i j '' (P ∩ OSUniformisation.dyadicSquare δ_coarse i j)) : ENNReal) ≤
      ENNReal.ofReal (K * Real.rpow (δ_fine / δ_coarse) (-s / 2)) := h.2.2
  have h_ratio_nonneg : 0 ≤ δ_fine / δ_coarse := by
    have hδf : 0 ≤ δ_fine := le_of_lt h.1.1
    have hδc : 0 < δ_coarse := h.1.2.1
    exact div_nonneg hδf hδc.le
  have h3' : ∀ (i j : ℤ), (P ∩ OSUniformisation.dyadicSquare δ_coarse i j).Nonempty →
      (Metric.externalCoveringNumber (Real.sqrt (δ_fine / δ_coarse)).toNNReal
         (OSUniformisation.homothetyS δ_coarse i j '' (P ∩ OSUniformisation.dyadicSquare δ_coarse i j)) : ENNReal) ≤
      ENNReal.ofReal (K' * Real.rpow (δ_fine / δ_coarse) (-s / 2)) := by
    intro i j hnonempty
    have h4 := h3 i j hnonempty
    have h_rpow_nonneg : 0 ≤ Real.rpow (δ_fine / δ_coarse) (-s / 2) :=
      Real.rpow_nonneg h_ratio_nonneg _
    have h5 : K * Real.rpow (δ_fine / δ_coarse) (-s / 2) ≤ K' * Real.rpow (δ_fine / δ_coarse) (-s / 2) := by
      gcongr
    have h6 : ENNReal.ofReal (K * Real.rpow (δ_fine / δ_coarse) (-s / 2)) ≤
        ENNReal.ofReal (K' * Real.rpow (δ_fine / δ_coarse) (-s / 2)) :=
      ENNReal.ofReal_le_ofReal h5
    exact le_trans h4 h6
  exact ⟨h1', hK'_pos, h3'⟩

/-- Transfer IsRegularBetweenScales from S to S'' at one scale, with both
    output constants set to the amplified value. -/
lemma transfer_regular_one_scale
    {n_fine : ℕ} {a : Fin (n_fine + 1) → ℕ}
    {S S'' : Finset (ℤ × ℤ)} {N N'' : Fin n_fine → ℕ}
    (h_unif_S : RangeUniformityProp n_fine a S N)
    (h_unif_S'' : RangeUniformityProp n_fine a S'' N'')
    (hS''_sub : S'' ⊆ S)
    (h_a0 : a 0 = 0)
    (h_a_mono : ∀ j : Fin n_fine, a j.castSucc ≤ a (Fin.succ j))
    (h_a_last : ∀ i, a i ≤ a (Fin.last n_fine))
    (h_unit_S : ∀ idx ∈ S, 0 ≤ idx.1 ∧ 0 ≤ idx.2 ∧
      idx.1 < (2 : ℤ)^(a (Fin.last n_fine)) ∧ idx.2 < (2 : ℤ)^(a (Fin.last n_fine)))
    (h_unit_S'' : ∀ idx ∈ S'', 0 ≤ idx.1 ∧ 0 ≤ idx.2 ∧
      idx.1 < (2 : ℤ)^(a (Fin.last n_fine)) ∧ idx.2 < (2 : ℤ)^(a (Fin.last n_fine)))
    (M : ℝ) (hM_pos : 0 < M) (hM_ge1 : 1 ≤ M)
    (h_per_level : ∀ j : Fin n_fine, (N'' j : ℝ) ≥ (N j : ℝ) / (M * (4 : ℝ)^n_fine))
    (δbar : ℝ) (nδ : ℕ) (hδbar_eq : δbar = dyadicDelta nδ)
    (h_a_last_eq : a (Fin.last n_fine) = nδ)
    (Δ' : Fin (n_fine + 1) → ℝ)
    (hΔ'_spec : ∀ i, Δ' i = dyadicDelta (a i))
    (hΔ'_pos : ∀ i, 0 < Δ' i)
    (hΔ'_dyadic : ∀ i, Δ' i ∈ dyadicScales)
    (j : Fin n_fine)
    (s t_j C_j K_j : ℝ) (ht_j_nonneg : 0 ≤ t_j) (hC_j_pos : 0 < C_j) (hK_j_pos : 0 < K_j)
    (hK_le_C : K_j ≤ C_j)
    (h_regular_S : OSUniformisation.IsRegularBetweenScales
        (setFromIndices δbar S) (Δ' (Fin.succ j)) (Δ' j.castSucc) t_j C_j K_j) :
    OSUniformisation.IsRegularBetweenScales (setFromIndices δbar S'')
      (Δ' (Fin.succ j)) (Δ' j.castSucc) t_j
      (9 * C_j * 2 * M * (4 : ℝ)^n_fine)
      (9 * C_j * 2 * M * (4 : ℝ)^n_fine) := by
  let c : ℝ := 1 / (2 * M * (4 : ℝ)^n_fine)
  have hc_pos : 0 < c := by positivity
  have hc_eq : c = 1 / (2 * M * (4 : ℝ)^n_fine) := by rfl
  have hdensity_dyadic := density_dyadic_at_scale
    h_unif_S h_unif_S'' hS''_sub h_a_mono h_a_last M hM_pos h_per_level
    δbar nδ hδbar_eq h_a_last_eq Δ' hΔ'_spec j c hc_pos hc_eq
  have hδ_fine_pos : 0 < Δ' (Fin.succ j) := hΔ'_pos (Fin.succ j)
  have hδ_fine_dyadic : Δ' (Fin.succ j) ∈ dyadicScales := hΔ'_dyadic (Fin.succ j)
  have hδ_coarse_pos : 0 < Δ' j.castSucc := hΔ'_pos j.castSucc
  have hδ_fine_le_coarse : Δ' (Fin.succ j) ≤ Δ' j.castSucc := by
    have h : a j.castSucc ≤ a (Fin.succ j) := h_a_mono j
    have h2 : dyadicDelta (a (Fin.succ j)) ≤ dyadicDelta (a j.castSucc) := dyadicDelta_anti h
    have h3 : Δ' (Fin.succ j) = dyadicDelta (a (Fin.succ j)) := hΔ'_spec (Fin.succ j)
    have h4 : Δ' j.castSucc = dyadicDelta (a j.castSucc) := hΔ'_spec j.castSucc
    rw [h3, h4]; exact h2
  have hP_bounded : Bornology.IsBounded (setFromIndices δbar S) := by
    rw [hδbar_eq]; exact setFromIndices_isBounded nδ S
  have hP''_bounded : Bornology.IsBounded (setFromIndices δbar S'') := by
    rw [hδbar_eq]; exact setFromIndices_isBounded nδ S''
  have hsub : setFromIndices δbar S'' ⊆ setFromIndices δbar S :=
    setFromIndices_subset hS''_sub
  let C_amp := 9 * C_j * 2 * M * (4 : ℝ)^n_fine
  have hC_amp_pos : 0 < C_amp := by positivity
  have h_transferred : OSUniformisation.IsRegularBetweenScales (setFromIndices δbar S'')
      (Δ' (Fin.succ j)) (Δ' j.castSucc) t_j (9 * C_j / c) K_j :=
    OSUniformisation.uniformisation_regular_transfer
      hδ_fine_pos hδ_fine_dyadic hδ_coarse_pos hδ_fine_le_coarse
      ht_j_nonneg hC_j_pos hK_j_pos hc_pos hP_bounded hP''_bounded
      h_regular_S hsub hdensity_dyadic
  have h_const : 9 * C_j / c = C_amp := by
    dsimp only [c, C_amp]
    have hpos : (0 : ℝ) < 2 * M * (4 : ℝ)^n_fine := by positivity
    field_simp [hpos.ne'] <;> ring
  rw [h_const] at h_transferred
  have h4_pow_ge1 : (1 : ℝ) ≤ (4 : ℝ)^n_fine := by
    have h : ∀ m : ℕ, (1 : ℝ) ≤ (4 : ℝ)^m := by
      intro m; induction m <;> norm_num [*, pow_succ] <;> linarith
    exact h n_fine
  have h_factor_ge1 : (1 : ℝ) ≤ 9 * 2 * M * (4 : ℝ)^n_fine := by
    have h1 : (1 : ℝ) ≤ M := hM_ge1
    have h2 : (1 : ℝ) ≤ (4 : ℝ)^n_fine := h4_pow_ge1
    calc (1 : ℝ)
      ≤ 9 * 2 * (1 : ℝ) * (1 : ℝ) := by norm_num
    _ ≤ 9 * 2 * M * (4 : ℝ)^n_fine := by gcongr <;> linarith
  have hK_le_amp : K_j ≤ C_amp := by
    dsimp only [C_amp]
    calc K_j
      ≤ C_j := hK_le_C
    _ = C_j * 1 := by ring
    _ ≤ C_j * (9 * 2 * M * (4 : ℝ)^n_fine) := by gcongr <;> linarith
    _ = 9 * C_j * 2 * M * (4 : ℝ)^n_fine := by ring
  exact regular_between_scales_weaken h_transferred le_rfl hK_le_amp hC_amp_pos hC_amp_pos

/-! ========================================================================
   Main assembly: thin a dense subset to recover uniformity, then transfer
   between-scales properties per-scale for normal/good scales.

   Input:
   - S_full: full index set, uniform, with between-scales properties
   - S': dense subset of S_full (card S_full ≤ K * card S')
   - scaleClass', C_between': fine scale classification and constants

   Output:
   - S'': uniform subset of S'
   - N'': uniformity constants for S''
   - Transferred between-scales for normal/good scales
   ======================================================================== -/

/-- Core thinning and transfer lemma for fine CombiningConfig construction. -/
lemma thin_and_transfer
    {n_fine : ℕ} (hn_fine_pos : 0 < n_fine)
    {δbar : ℝ} (hδbar_pos : 0 < δbar) (hδbar_lt_one : δbar < 1)
    {nδ : ℕ} (hδbar_eq : δbar = dyadicDelta nδ)
    {Δ' : Fin (n_fine + 1) → ℝ}
    (hΔ'_pos : ∀ i, 0 < Δ' i)
    (hΔ'_dyadic : ∀ i, Δ' i ∈ dyadicScales)
    (hΔ'_strict : ∀ j : Fin n_fine, Δ' (Fin.succ j) < Δ' j.castSucc)
    (hΔ'_end : Δ' (Fin.last n_fine) = δbar)
    (hΔ'_start : Δ' 0 = 1)
    {a : Fin (n_fine + 1) → ℕ}
    (ha_spec : ∀ i, Δ' i = dyadicDelta (a i))
    (ha_mono : ∀ j : Fin n_fine, a j.castSucc ≤ a (Fin.succ j))
    (ha_last_max : ∀ i, a i ≤ a (Fin.last n_fine))
    (ha_last_eq : a (Fin.last n_fine) = nδ)
    {S_full S' : Finset (ℤ × ℤ)}
    {N_full : Fin n_fine → ℕ}
    (h_unif_full : RangeUniformityProp n_fine a S_full N_full)
    (hS'_sub : S' ⊆ S_full)
    (h_unit_full : ∀ idx ∈ S_full, 0 ≤ idx.1 ∧ 0 ≤ idx.2 ∧
      idx.1 < (2 : ℤ)^(a (Fin.last n_fine)) ∧ idx.2 < (2 : ℤ)^(a (Fin.last n_fine)))
    (h_unit_S' : ∀ idx ∈ S', 0 ≤ idx.1 ∧ 0 ≤ idx.2 ∧
      idx.1 < (2 : ℤ)^(a (Fin.last n_fine)) ∧ idx.2 < (2 : ℤ)^(a (Fin.last n_fine)))
    (K : ℝ) (hK_pos : 0 < K) (hK_ge1 : 1 ≤ K)
    (h_density : (S'.card : ℝ) ≥ (S_full.card : ℝ) / K)
    {scaleClass' : Fin n_fine → ScaleClass}
    {C_between' : Fin n_fine → ℝ}
    (s t : ℝ) (hs_nonneg : 0 ≤ s)
    -- Between-scales for S_full
    (h_between_normal : ∀ (j : Fin n_fine), scaleClass' j = ScaleClass.normal →
      OSUniformisation.IsSetBetweenScales (setFromIndices δbar S_full)
        (Δ' (Fin.succ j)) (Δ' j.castSucc) s (C_between' j))
    (h_between_good : ∀ (j : Fin n_fine) (t_j : ℝ),
      scaleClass' j = ScaleClass.good t_j →
        OSUniformisation.IsRegularBetweenScales (setFromIndices δbar S_full)
          (Δ' (Fin.succ j)) (Δ' j.castSucc) t_j (C_between' j) (C_between' j))
    (M_amp : ℝ) (hM_amp_ge : K * (24 * Real.log (1 / δbar) / (n_fine : ℝ)) ^ n_fine ≤ M_amp)
    (hM_amp_ge1 : 1 ≤ M_amp) :
    ∃ (S'' : Finset (ℤ × ℤ)) (N'' : Fin n_fine → ℕ),
      S'' ⊆ S' ∧
      RangeUniformityProp n_fine a S'' N'' ∧
      (∀ (j : Fin n_fine), scaleClass' j = ScaleClass.normal →
        OSUniformisation.IsSetBetweenScales (setFromIndices δbar S'')
          (Δ' (Fin.succ j)) (Δ' j.castSucc) s
          (9 * (C_between' j : ℝ) * 2 * M_amp * (4 : ℝ)^n_fine)) ∧
      (∀ (j : Fin n_fine) (t_j : ℝ), scaleClass' j = ScaleClass.good t_j →
        OSUniformisation.IsRegularBetweenScales (setFromIndices δbar S'')
          (Δ' (Fin.succ j)) (Δ' j.castSucc) t_j
          (9 * (C_between' j : ℝ) * 2 * M_amp * (4 : ℝ)^n_fine)
          (9 * (C_between' j : ℝ) * 2 * M_amp * (4 : ℝ)^n_fine)) := by
  let L_unif : ℝ := (24 * Real.log (1 / δbar) / (n_fine : ℝ)) ^ n_fine
  have hlog_pos : 0 < Real.log (1 / δbar) := Real.log_pos (by
    have h : 1 < 1 / δbar := by
      apply one_lt_one_div <;> linarith
    exact h)
  have hL_unif_pos : 0 < L_unif := by positivity
  let M_total : ℝ := K * L_unif
  have hM_total_pos : 0 < M_total := mul_pos hK_pos hL_unif_pos
  have hM_amp_ge_Mtotal : M_total ≤ M_amp := by
    dsimp only [M_total]
    exact hM_amp_ge
  have hM_amp_pos : 0 < M_amp := by linarith
  let P' : Set (EuclideanSpace ℝ (Fin 2)) := setFromIndices δbar S'
  have hP'_bounded : Bornology.IsBounded P' := by
    have h : P' = setFromIndices (dyadicDelta nδ) S' := by
      dsimp only [P']; rw [hδbar_eq]
    rw [h]
    exact setFromIndices_isBounded nδ S'
  have hS_full_nonempty : S_full.Nonempty := h_unif_full.1
  have hS'_nonempty : S'.Nonempty := by
    by_contra h
    have h' : S' = ∅ := by simpa using h
    rw [h'] at h_density
    have h0 : (0 : ℝ) ≥ (S_full.card : ℝ) / K := by simpa using h_density
    have h1 : (S_full.card : ℝ) ≤ 0 := by
      have h2 : 0 < K := hK_pos
      calc (S_full.card : ℝ)
        = ((S_full.card : ℝ) / K) * K := by field_simp [h2.ne'] <;> ring
      _ ≤ 0 * K := by gcongr
      _ = 0 := by ring
    have h5 : S_full.card ≤ 0 := by exact_mod_cast h1
    have h6 : S_full.card = 0 := Nat.eq_zero_of_le_zero h5
    have h7 : S_full = ∅ := Finset.card_eq_zero.mp h6
    rw [h7] at hS_full_nonempty
    simp at hS_full_nonempty
  have hP'_nonempty : P'.Nonempty := by
    rcases hS'_nonempty with ⟨idx, hidx⟩
    let x : EuclideanSpace ℝ (Fin 2) := WithLp.toLp (2 : ENNReal) fun k : Fin 2 =>
      if k = 0 then (idx.1 : ℝ) * δbar else (idx.2 : ℝ) * δbar
    have hx : x ∈ P' := by
      exact Set.mem_iUnion₂.mpr ⟨idx, hidx, by
        simp only [BasicUniformization.dyadicSquare, Set.mem_setOf_eq] <;> constructor <;> simp [x] <;> linarith⟩
    exact ⟨x, hx⟩
  have hP'_union_squares : ∀ (x : EuclideanSpace ℝ (Fin 2)), x ∈ P' →
      ∃ (i j : ℤ), x ∈ BasicUniformization.dyadicSquare δbar i j ∧
        (BasicUniformization.dyadicSquare δbar i j : Set (EuclideanSpace ℝ (Fin 2))) ⊆ P' := by
    intro x hx
    rcases Set.mem_iUnion₂.mp hx with ⟨idx, hidx, hx2⟩
    refine ⟨idx.1, idx.2, hx2, ?_⟩
    intro y hy
    exact Set.mem_iUnion₂.mpr ⟨idx, hidx, hy⟩
  rcases basic_uniformization_dyadic n_fine hn_fine_pos δbar hδbar_pos hδbar_lt_one nδ hδbar_eq
      Δ' hΔ'_dyadic hΔ'_pos hΔ'_strict hΔ'_end hΔ'_start
      P' hP'_bounded hP'_nonempty hP'_union_squares
    with ⟨S'', N'', hS''_sub_set, h_unif_S'', h_cover_density⟩
  have hS''_sub : S'' ⊆ S' := by
    have h : setFromIndices δbar S'' ⊆ setFromIndices δbar S' := hS''_sub_set
    exact (OSUniformisation.setFromIndices_subset_iff hδbar_pos).mp h
  let a_choice : Fin (n_fine + 1) → ℕ := fun i =>
    Classical.choose (show ∃ (n : ℕ), Δ' i = (2 : ℝ)^(-(n : ℤ)) from
      by simpa [dyadicScales] using hΔ'_dyadic i)
  have ha'_spec : ∀ i, Δ' i = dyadicDelta (a_choice i) := by
    intro i
    have h_exists : ∃ (n : ℕ), Δ' i = (2 : ℝ)^(-(n : ℤ)) := by
      simpa [dyadicScales] using hΔ'_dyadic i
    have h : Δ' i = (2 : ℝ)^(-(a_choice i : ℤ)) := Classical.choose_spec h_exists
    have h2 : dyadicDelta (a_choice i) = (2 : ℝ)^(-(a_choice i : ℤ)) := by
      simp [dyadicDelta] <;> field_simp <;> ring
    rw [h, h2]
  have h_a_eq : a = a_choice := by
    funext i
    have h1 : Δ' i = dyadicDelta (a i) := ha_spec i
    have h2 : Δ' i = dyadicDelta (a_choice i) := ha'_spec i
    have h3 : dyadicDelta (a i) = dyadicDelta (a_choice i) := by rw [←h1, h2]
    exact OSUniformisation.dyadicDelta_injective h3
  have h_unif_S''_a : RangeUniformityProp n_fine a S'' N'' := by
    have h4 : RangeUniformityProp n_fine a_choice S'' N'' := h_unif_S''
    rw [h_a_eq.symm] at h4
    exact h4
  have h_a0 : a 0 = 0 := by
    have h1 : Δ' 0 = dyadicDelta (a 0) := ha_spec 0
    rw [hΔ'_start] at h1
    have h2 : dyadicDelta (a 0) = 1 := h1.symm
    by_contra h3
    have h4 : 0 < a 0 := by omega
    have h5 : dyadicDelta (a 0) < 1 := by
      simp [dyadicDelta]
      have h6 : (1 : ℝ) < (2 : ℝ) ^ (a 0) := by
        have h7 : a 0 ≠ 0 := by omega
        have h8 : (1 : ℝ) < (2 : ℝ) := by norm_num
        exact one_lt_pow₀ h8 h7
      field_simp [h6.ne'] <;> linarith
    linarith
  have h_unit_S'' : ∀ idx ∈ S'', 0 ≤ idx.1 ∧ 0 ≤ idx.2 ∧
      idx.1 < (2 : ℤ)^(a (Fin.last n_fine)) ∧ idx.2 < (2 : ℤ)^(a (Fin.last n_fine)) := by
    intro idx hidx
    have hsub : idx ∈ S' := hS''_sub hidx
    exact h_unit_S' idx hsub
  have hP'_eq2 : P' = setFromIndices (dyadicDelta nδ) S' := by
    dsimp only [P']; rw [hδbar_eq]
  have h_cover_S' : (DyadicCubes.dyadicCoveringNumber nδ P' hP'_bounded : ℝ) = (S'.card : ℝ) := by
    have h_gen : ∀ (X : Set (EuclideanSpace ℝ (Fin 2))) (hX : Bornology.IsBounded X),
        X = setFromIndices (dyadicDelta nδ) S' →
        (DyadicCubes.dyadicCoveringNumber nδ X hX : ℝ) = (S'.card : ℝ) := by
      intro X hX h_eq; subst h_eq; exact_mod_cast count_eq_card nδ S' hS'_nonempty
    exact h_gen P' hP'_bounded hP'_eq2
  have hS''_nonempty : S''.Nonempty := h_unif_S''_a.1
  have hP''_bounded : Bornology.IsBounded (setFromIndices δbar S'') := by
    have h_eq : setFromIndices δbar S'' = setFromIndices (dyadicDelta nδ) S'' := by rw [hδbar_eq]
    rw [h_eq]; exact setFromIndices_isBounded nδ S''
  have h_cover_S'' : (DyadicCubes.dyadicCoveringNumber nδ (setFromIndices δbar S'') hP''_bounded : ℝ) = (S''.card : ℝ) := by
    have h_gen : ∀ (X : Set (EuclideanSpace ℝ (Fin 2))) (hX : Bornology.IsBounded X),
        X = setFromIndices (dyadicDelta nδ) S'' →
        (DyadicCubes.dyadicCoveringNumber nδ X hX : ℝ) = (S''.card : ℝ) := by
      intro X hX h_eq; subst h_eq; exact_mod_cast count_eq_card nδ S'' hS''_nonempty
    exact h_gen (setFromIndices δbar S'') hP''_bounded (by rw [hδbar_eq])
  have h_density_S'' : (S''.card : ℝ) ≥ (S'.card : ℝ) / L_unif := by
    rw [h_cover_S''] at h_cover_density
    rw [h_cover_S'] at h_cover_density
    exact h_cover_density
  have h_global_density : (S''.card : ℝ) ≥ (S_full.card : ℝ) / M_total := by
    dsimp only [M_total]
    calc (S''.card : ℝ)
      ≥ (S'.card : ℝ) / L_unif := h_density_S''
    _ ≥ ((S_full.card : ℝ) / K) / L_unif := by gcongr
    _ = (S_full.card : ℝ) / (K * L_unif) := by
      have hK_ne : K ≠ 0 := hK_pos.ne'
      have hL_ne : L_unif ≠ 0 := hL_unif_pos.ne'
      have h : ((S_full.card : ℝ) / K) / L_unif = (S_full.card : ℝ) / (K * L_unif) := by
        have hK_ne : K ≠ 0 := hK_pos.ne'
        have hL_ne : L_unif ≠ 0 := hL_unif_pos.ne'
        simp [div_eq_mul_inv, hK_ne, hL_ne] <;> ring
      exact h
  have hS''_sub_full : S'' ⊆ S_full := Finset.Subset.trans hS''_sub hS'_sub
  have h_per_level_Mtotal : ∀ (j : Fin n_fine), (N'' j : ℝ) ≥ (N_full j : ℝ) / (M_total * (4 : ℝ)^n_fine) :=
    OSUniformisation.per_level_density hS''_sub_full h_unif_full h_unif_S''_a h_a0 ha_mono ha_last_max
      h_unit_full h_unit_S'' M_total hM_total_pos h_global_density
  have h_per_level : ∀ (j : Fin n_fine), (N'' j : ℝ) ≥ (N_full j : ℝ) / (M_amp * (4 : ℝ)^n_fine) := by
    intro j
    have h1 : (N'' j : ℝ) ≥ (N_full j : ℝ) / (M_total * (4 : ℝ)^n_fine) := h_per_level_Mtotal j
    have h2 : M_amp * (4 : ℝ)^n_fine ≥ M_total * (4 : ℝ)^n_fine := by gcongr
    have h3 : (N_full j : ℝ) / (M_amp * (4 : ℝ)^n_fine) ≤ (N_full j : ℝ) / (M_total * (4 : ℝ)^n_fine) := by
      gcongr
    exact le_trans h3 h1
  let C_amp := fun (j : Fin n_fine) =>
    9 * (C_between' j : ℝ) * 2 * M_amp * (4 : ℝ)^n_fine
  have h_transfer_normal : ∀ (j : Fin n_fine), scaleClass' j = ScaleClass.normal →
      OSUniformisation.IsSetBetweenScales (setFromIndices δbar S'')
        (Δ' (Fin.succ j)) (Δ' j.castSucc) s (C_amp j) := by
    intro j hj
    have h_between := h_between_normal j hj
    have hC_j_pos : 0 < (C_between' j : ℝ) := h_between.2.2.2.2.1
    exact transfer_between_one_scale
      h_unif_full h_unif_S''_a hS''_sub_full h_a0 ha_mono ha_last_max
      h_unit_full h_unit_S''
      M_amp hM_amp_pos h_per_level
      δbar nδ hδbar_eq ha_last_eq Δ' ha_spec hΔ'_pos hΔ'_dyadic
      j s (C_between' j : ℝ) hs_nonneg hC_j_pos h_between
  have h_transfer_good : ∀ (j : Fin n_fine) (t_j : ℝ),
      scaleClass' j = ScaleClass.good t_j →
        OSUniformisation.IsRegularBetweenScales (setFromIndices δbar S'')
          (Δ' (Fin.succ j)) (Δ' j.castSucc) t_j (C_amp j) (C_amp j) := by
    intro j t_j hj
    have h_regular := h_between_good j t_j hj
    have hC_j_pos : 0 < (C_between' j : ℝ) := h_regular.1.2.2.2.2.1
    exact transfer_regular_one_scale
      h_unif_full h_unif_S''_a hS''_sub_full h_a0 ha_mono ha_last_max
      h_unit_full h_unit_S''
      M_amp hM_amp_pos hM_amp_ge1 h_per_level
      δbar nδ hδbar_eq ha_last_eq Δ' ha_spec hΔ'_pos hΔ'_dyadic
      j s t_j (C_between' j : ℝ) (C_between' j : ℝ)
      (have h : 0 ≤ t_j := h_regular.1.2.2.2.1; h)
      hC_j_pos hC_j_pos (le_refl (C_between' j : ℝ))
      h_regular
  have hC_amp_eq : ∀ j, C_amp j =
      9 * (C_between' j : ℝ) * 2 * M_amp * (4 : ℝ)^n_fine := by
    intro j
    rfl
  refine ⟨S'', N'', hS''_sub, h_unif_S''_a, ?_⟩
  constructor
  · intro j hj
    have h := h_transfer_normal j hj
    rw [hC_amp_eq j] at h
    exact h
  · intro j t_j hj
    have h := h_transfer_good j t_j hj
    rw [hC_amp_eq j] at h
    exact h

/-! ========================================================================
   Point-set intersection lemma for thinning integration.
   ======================================================================== -/

/-- The intersection of config.pointSet with a coarse dyadic square Q
    equals the union of fine squares in config.P₀ contained in Q. -/
lemma pointSet_inter_coarseSquare
    {k m : ℕ} (hnm : m ≤ k)
    {s C : ℝ} {M : ℕ}
    (config : CTNiceConfiguration k s C M)
    (Q : DyadicSquare m) :
    config.pointSet ∩ CombiningTheorem.dyadicSquare (dyadicDelta m) Q.i Q.j =
    setFromIndices (dyadicDelta k)
      ((config.P₀.filter (fun p => squareContained hnm p Q)).image (fun p => (p.i, p.j))) := by
  have h1 : config.pointSet = setFromIndices (dyadicDelta k)
      (config.P₀.image (fun p : DyadicSquare k => (p.i, p.j))) :=
    config_pointSet_eq_setFromIndices config
  rw [h1]
  let P_full_Q := config.P₀.filter (fun p => squareContained hnm p Q)
  let S_global := P_full_Q.image (fun p : DyadicSquare k => (p.i, p.j))
  have h_p_toSet : ∀ (p : DyadicSquare k),
      (p.toSet : Set Plane) = CombiningTheorem.dyadicSquare (dyadicDelta k) p.i p.j := by
    intro p
    ext x
    simp [DyadicSquare.toSet, CombiningTheorem.dyadicSquare, Set.mem_Ico] <;> tauto
  have h_Q_toSet : (Q.toSet : Set Plane) = CombiningTheorem.dyadicSquare (dyadicDelta m) Q.i Q.j := by
    ext x
    simp [DyadicSquare.toSet, CombiningTheorem.dyadicSquare, Set.mem_Ico] <;> tauto
  have h_main : setFromIndices (dyadicDelta k) (config.P₀.image (fun p => (p.i, p.j))) ∩
      CombiningTheorem.dyadicSquare (dyadicDelta m) Q.i Q.j =
      setFromIndices (dyadicDelta k) S_global := by
    ext x
    simp only [setFromIndices, Set.mem_inter_iff, Set.mem_iUnion, S_global, P_full_Q,
      Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨⟨idx, ⟨p, hp, rfl⟩, hxp⟩, hxQ⟩
      have hxp' : x ∈ (p : DyadicSquare k).toSet := by
        rw [h_p_toSet p]; exact hxp
      have hxQ' : x ∈ (Q.toSet : Set Plane) := by
        rw [h_Q_toSet]; exact hxQ
      have h_cont : squareContained hnm p Q :=
        fine_point_in_coarse_square_implies_contained hnm hxp' hxQ'
      have h_goal : x ∈ BasicUniformization.dyadicSquare (dyadicDelta k) p.i p.j := hxp
      exact ⟨(p.i, p.j), ⟨p, ⟨hp, h_cont⟩, rfl⟩, h_goal⟩
    · rintro ⟨idx, ⟨p, ⟨hp, h_cont⟩, rfl⟩, hxp⟩
      have hxp' : x ∈ (p : DyadicSquare k).toSet := by
        rw [h_p_toSet p]; exact hxp
      have hxQ' : x ∈ (Q.toSet : Set Plane) :=
        InductionOnScales.squareContained_toSet_subset hnm h_cont hxp'
      have hxQ : x ∈ CombiningTheorem.dyadicSquare (dyadicDelta m) Q.i Q.j := by
        rw [←h_Q_toSet]; exact hxQ'
      exact ⟨⟨(p.i, p.j), ⟨p, hp, rfl⟩, hxp⟩, hxQ⟩
  exact h_main

/-- Chain property: if Δ' is strictly decreasing on n_fine levels and starts at 1,
    then Δ' (Fin.last n_fine) ≤ Δ' i for all i. -/
lemma delta_chain_property {n_fine : ℕ} {Δ' : Fin (n_fine + 1) → ℝ}
    (hΔ'_strict : ∀ j : Fin n_fine, Δ' (Fin.succ j) < Δ' j.castSucc)
    (hΔ'_start : Δ' 0 = 1) :
    ∀ (i : Fin (n_fine + 1)), Δ' (Fin.last n_fine) ≤ Δ' i := by
  have h_main : ∀ (k : ℕ), ∀ (i : Fin (n_fine + 1)), i.val + k = n_fine → Δ' (Fin.last n_fine) ≤ Δ' i := by
    intro k
    induction k with
    | zero =>
      intro i hi
      have h_val : i.val = n_fine := by omega
      have h_i_last : i = Fin.last n_fine := by
        apply Fin.ext
        simp [h_val, Fin.last]
      rw [h_i_last] <;> rfl
    | succ k ih =>
      intro i hi
      let i' : Fin (n_fine + 1) := ⟨i.val + 1, by omega⟩
      have h_i'_val : i'.val + k = n_fine := by
        simp [i', hi] <;> omega
      have h_ih' := ih i' h_i'_val
      let j : Fin n_fine := ⟨i.val, by omega⟩
      have h1 : j.castSucc = i := by apply Fin.ext; simp [j] <;> omega
      have h2 : Fin.succ j = i' := by apply Fin.ext; simp [j, i'] <;> omega
      have h_strict : Δ' i' < Δ' i := by
        have h := hΔ'_strict j
        rw [h2, h1] at h
        exact h
      exact h_ih'.trans h_strict.le
  intro i
  exact h_main (n_fine - i.val) i (by omega)

/-- Chain property: if Δ' is strictly decreasing on n_fine levels,
    then Δ' i ≤ Δ' 0 for all i. -/
lemma delta_chain_start_property {n_fine : ℕ} {Δ' : Fin (n_fine + 1) → ℝ}
    (hΔ'_strict : ∀ j : Fin n_fine, Δ' (Fin.succ j) < Δ' j.castSucc) :
    ∀ (i : Fin (n_fine + 1)), Δ' i ≤ Δ' 0 := by
  have h_main : ∀ (k : ℕ), ∀ (i : Fin (n_fine + 1)), i.val = k → Δ' i ≤ Δ' 0 := by
    intro k
    induction k with
    | zero =>
      intro i hi
      have h_i0 : i = 0 := by apply Fin.ext; simp [hi]
      rw [h_i0] <;> rfl
    | succ k ih =>
      intro i hi
      let j : Fin n_fine := ⟨k, by omega⟩
      have h1 : Fin.succ j = i := by
        apply Fin.ext; simp [j, hi] <;> omega
      have h_strict : Δ' i < Δ' (j.castSucc) := by
        have h := hΔ'_strict j
        rw [h1] at h
        exact h
      have h_ih' := ih (j.castSucc) (by simp [j])
      exact h_strict.le.trans h_ih'
  intro i
  exact h_main i.val i rfl

end DiscretisedFurstenbergEstimate.CombiningTheoremRework
