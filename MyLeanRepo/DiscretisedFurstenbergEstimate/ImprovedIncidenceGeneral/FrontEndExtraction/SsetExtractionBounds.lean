module

/-
  S-set Extraction Bounds for Front-End Extraction.

  Provides quantitative bounds needed by the front-end extraction and
  B1 bridge decomposition:
  1. `sset_card_lower_bound'`: finite set cardinality ≥ δ^{-s}/C from S-set
  2. `counter_assumption_M_upper`: M upper bound from global_2s_bound + counter-assumption
  3. `at_most_25_in_delta_ball`: δ-ball ≤ 25 δ-separated points (Besicovitch)
  4. `separated_card_le_25_cover`: |S| ≤ 25·N_δ(S) packing-covering inequality
  5. `sset_ball_growth`: |P∩B(c,r)| ≤ 25·C·r^t·|P| from S-set + separation

  Whiteprint node: improved_incidence_general / front_end_extraction / sset_extraction_bounds
  Dependencies: Global2sBoundNoHLarge, ElementaryIncidence, PackingBound
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Global2sBoundNoHLarge
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ElementaryIncidence
public import MyLeanRepo.DiscretisedFurstenbergEstimate.PackingBound
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.FrontEndExtraction

open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.Global2sBound

/-- Lower bound: a (δ,t,C)-set has cardinality ≥ δ^{-t}/C.

    For C = δ^{-ε}, this gives |P| ≥ δ^{-t+ε}. -/
lemma sset_card_lower_bound' {X : Type*} [PseudoMetricSpace X] [DecidableEq X]
    {δ s C : ℝ} {P : Finset X}
    (hδ_pos : 0 < δ) (hs : 0 ≤ s) (hC_pos : 0 < C)
    (hP_nonempty : P.Nonempty)
    (hP_set : IsDeltaSSet δ s C (P : Set X)) :
    (P.card : ℝ) ≥ δ^(-s) / C := by
  rcases hP_nonempty with ⟨p, hp⟩
  let S : Set X := (P : Set X) ∩ Metric.closedBall p δ
  have hS_nonempty : S.Nonempty := by
    refine' ⟨p, _⟩
    simp only [S, Set.mem_inter_iff, Finset.mem_coe, Metric.mem_closedBall]
    <;> exact ⟨hp, by simp [hδ_pos.le]⟩
  let eS : ENat := Metric.externalCoveringNumber δ.toNNReal S
  let eP : ENat := Metric.externalCoveringNumber δ.toNNReal (P : Set X)
  have h1 : eS ≠ 0 := by
    have h_eq : eS = 0 ↔ S = ∅ := Metric.externalCoveringNumber_eq_zero
    exact h_eq.not.mpr hS_nonempty.ne_empty
  have h1' : (1 : ENat) ≤ eS := ENat.one_le_iff_ne_zero.mpr h1
  have h1E : (1 : ENNReal) ≤ (eS : ENNReal) := by exact_mod_cast h1'
  have h2 : (eS : ENNReal) ≤
      ENNReal.ofReal C * (ENNReal.ofReal δ) ^ s * (eP : ENNReal) :=
    hP_set.2.2.2.2 p δ (by linarith)
  have h3 : (1 : ENNReal) ≤
      ENNReal.ofReal C * (ENNReal.ofReal δ) ^ s * (eP : ENNReal) :=
    le_trans h1E h2
  have h4 : eP ≤ (P : Set X).encard :=
    Metric.externalCoveringNumber_le_encard_self (P : Set X)
  have h42 : (P : Set X).encard = ↑(P.card) := by simp
  have h43 : eP ≤ ↑(P.card) := by
    rw [h42] at h4
    exact h4
  have h4E : (eP : ENNReal) ≤ ENNReal.ofReal (P.card : ℝ) := by
    have h44 : (eP : ENNReal) ≤ (↑(P.card) : ENNReal) := by
      have h : ∀ (a b : ENat), a ≤ b → (a : ENNReal) ≤ (b : ENNReal) := by
        intro a b h; exact ENat.toENNReal_le.mpr h
      exact h eP (↑(P.card)) h43
    have h45 : (↑(P.card) : ENNReal) = ENNReal.ofReal (P.card : ℝ) := by simp
    rw [h45] at h44
    exact h44
  have h5 : (1 : ENNReal) ≤ ENNReal.ofReal C * (ENNReal.ofReal δ) ^ s *
      ENNReal.ofReal (P.card : ℝ) :=
    le_trans h3 (by gcongr)
  have h6 : (ENNReal.ofReal δ) ^ s = ENNReal.ofReal (δ ^ s) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg (by linarith) hs] <;> rfl
  rw [h6] at h5
  have h7 : ENNReal.ofReal C * ENNReal.ofReal (δ ^ s) * ENNReal.ofReal (P.card : ℝ) =
      ENNReal.ofReal (C * δ ^ s * (P.card : ℝ)) := by
    rw [← ENNReal.ofReal_mul, ← ENNReal.ofReal_mul] <;> positivity
  rw [h7] at h5
  have h_pos : 0 ≤ C * δ ^ s * (P.card : ℝ) := by positivity
  have h9' : ENNReal.ofReal 1 ≤ ENNReal.ofReal (C * δ ^ s * (P.card : ℝ)) := by
    have h_eq : (1 : ENNReal) = ENNReal.ofReal 1 := by rw [ENNReal.ofReal_one]
    rw [h_eq] at h5; exact h5
  have h8 : (1 : ℝ) ≤ C * δ ^ s * (P.card : ℝ) :=
    (ENNReal.ofReal_le_ofReal_iff h_pos).mp h9'
  have h9 : 0 < δ ^ s := Real.rpow_pos_of_pos hδ_pos s
  have h10 : 0 < C * δ ^ s := mul_pos hC_pos h9
  have h11 : (P.card : ℝ) ≥ 1 / (C * δ ^ s) := by
    have h12 : 1 / (C * δ ^ s) ≤ (P.card : ℝ) := by
      calc 1 / (C * δ ^ s)
        ≤ (C * δ ^ s * (P.card : ℝ)) / (C * δ ^ s) := by gcongr
      _ = (P.card : ℝ) := by field_simp [h10.ne'] <;> ring
    exact h12
  have h13 : 1 / (C * δ ^ s) = δ ^ (-s) / C := by
    have h14 : δ ^ (-s) = (δ ^ s)⁻¹ := by rw [Real.rpow_neg (by linarith)]
    rw [h14] <;> field_simp [h9.ne'] <;> ring
  rw [h13] at h11
  exact h11

/-- Lemma B: M upper bound from counter-assumption + global_2s_bound.

    Given:
    - global_2s_bound gives |U| ≥ M·δ^{-s}/D where D = 8·C_common·C_P·C_T·K_energy
    - Counter-assumption: Ncover δ T < δ^{-(2s+ε_G)}
    - Union-to-cover: |U| ≤ C_doubling · Ncover δ T

    Conclude: M ≤ D · C_doubling · δ^{-s-ε_G}.

    With δ = Δ², this is M ≤ D · C_doubling · Δ^{-2s-2ε_G}.
    For sufficiently small Δ, D·C_doubling absorbs into Δ^{-ε}, giving M ≤ Δ^{-2s-ε}. -/
lemma counter_assumption_M_upper
    {δ s ε_G : ℝ}
    (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1)
    (hs : 0 < s) (hs1 : s < 1) (hεG_pos : 0 < ε_G)
    {M : ℕ} (hM_pos : 0 < M)
    {P : Finset EuclideanPlane}
    (hP_nonempty : P.Nonempty)
    (hP_sep : Set.Pairwise (P : Set EuclideanPlane) (fun p q => δ ≤ dist p q))
    {Tp : EuclideanPlane → Finset AffineLine}
    (hTp_card_lower : ∀ p ∈ P, (M / 2 : ℝ) ≤ (Tp p).card)
    (hTp_card_upper : ∀ p ∈ P, (Tp p).card ≤ M)
    -- global_2s_bound parameters
    {C_P C_T C_common K_energy : ℝ}
    (hCP_pos : 0 < C_P) (hCT_pos : 0 < C_T)
    (hCcommon_pos : 0 < C_common) (hK_pos : 0 < K_energy)
    (h_common_bound : ∀ p ∈ P, ∀ q ∈ P, p ≠ q →
      ((Tp p) ∩ (Tp q)).card ≤ C_common * C_T * M * (δ / dist p q)^s)
    (h_energy : ∑ p ∈ P, ∑ q ∈ P.erase p, (dist p q)^(-s) ≤
        K_energy * C_P * (P.card : ℝ)^2)
    (hP_large : 2 ≤ C_common * C_P * C_T * K_energy * δ^s * (P.card : ℝ))
    -- counter-assumption + union cover
    {T : Set AffineLine}
    (h_counter : (Metric.externalCoveringNumber δ.toNNReal T : ENNReal) <
        ENNReal.ofReal (Real.rpow δ (-(2 * s + ε_G))))
    (C_doubling : ℝ) (hC_doubling_pos : 0 < C_doubling)
    (h_union_cover : ((P.biUnion Tp).card : ℝ) ≤
        C_doubling * (Metric.externalCoveringNumber δ.toNNReal T : ENNReal).toReal) :
    (M : ℝ) ≤ 8 * C_common * C_P * C_T * K_energy * C_doubling * δ^(-s - ε_G) := by
  set K : ℝ := C_common * C_P * C_T * K_energy * δ^s * (P.card : ℝ) with hK_def
  have hK_ge_one : 1 ≤ K := by linarith
  have h_main : ((P.biUnion Tp).card : ℝ) ≥
      (P.card : ℝ) * (M : ℝ) / (4 * (1 + K)) :=
    global_2s_bound_no_hP_large
      hδ_pos hδ_le_one hs hs1
      hCP_pos hCT_pos (show (0 : ℝ) < (M : ℝ) by exact_mod_cast hM_pos)
      hCcommon_pos hK_pos
      hP_nonempty hP_sep hTp_card_lower (fun p hp => by exact_mod_cast hTp_card_upper p hp) h_common_bound h_energy
  have h1 : 1 + K ≤ 2 * K := by linarith
  have h2 : (P.card : ℝ) * (M : ℝ) / (4 * (1 + K)) ≥
      (P.card : ℝ) * (M : ℝ) / (8 * K) := by
    have h_pos1 : 0 < 4 * (1 + K) := by positivity
    have h_pos2 : 0 < 8 * K := by positivity
    have h_denom : 4 * (1 + K) ≤ 8 * K := by linarith
    have h_num_pos : 0 ≤ (P.card : ℝ) * (M : ℝ) := by positivity
    exact div_le_div_of_nonneg_left h_num_pos h_pos1 h_denom
  have h3 : (P.card : ℝ) * (M : ℝ) / (8 * K) =
      (M : ℝ) * δ^(-s) / (8 * C_common * C_P * C_T * K_energy) := by
    have h5 : 0 < δ^s := Real.rpow_pos_of_pos hδ_pos s
    have h6 : 0 < (P.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hP_nonempty
    have h7 : K = C_common * C_P * C_T * K_energy * δ^s * (P.card : ℝ) := hK_def
    rw [h7]
    have h8 : δ^(-s) = (δ^s)⁻¹ := by rw [Real.rpow_neg (by linarith)]
    rw [h8]
    field_simp [h5.ne', h6.ne'] <;> ring
  have h4 : (M : ℝ) * δ^(-s) / (8 * C_common * C_P * C_T * K_energy) ≤
      ((P.biUnion Tp).card : ℝ) :=
    by rw [h3] at h2; exact le_trans h2 h_main
  let ncoverT : ENNReal := (Metric.externalCoveringNumber δ.toNNReal T : ENNReal)
  have h5 : ((P.biUnion Tp).card : ℝ) ≤ C_doubling * ncoverT.toReal := h_union_cover
  have h_pos_rpow : 0 < Real.rpow δ (-(2 * s + ε_G)) := Real.rpow_pos_of_pos hδ_pos _
  have h_ne_top1 : ncoverT ≠ ⊤ := by
    have h_lt : ncoverT < ENNReal.ofReal (Real.rpow δ (-(2 * s + ε_G))) := h_counter
    have h_lt_top : ncoverT < ⊤ := lt_trans h_lt ENNReal.ofReal_lt_top
    exact ne_of_lt h_lt_top
  have h_ne_top2 : (ENNReal.ofReal (Real.rpow δ (-(2 * s + ε_G)))) ≠ ⊤ := ENNReal.ofReal_ne_top
  have h6 : ncoverT.toReal < Real.rpow δ (-(2 * s + ε_G)) := by
    have h_iff : ncoverT.toReal < (ENNReal.ofReal (Real.rpow δ (-(2 * s + ε_G)))).toReal ↔
        ncoverT < ENNReal.ofReal (Real.rpow δ (-(2 * s + ε_G))) :=
      ENNReal.toReal_lt_toReal h_ne_top1 h_ne_top2
    have h7 : (ENNReal.ofReal (Real.rpow δ (-(2 * s + ε_G)))).toReal = Real.rpow δ (-(2 * s + ε_G)) := by
      have h_nonneg : 0 ≤ Real.rpow δ (-(2 * s + ε_G)) := Real.rpow_nonneg hδ_pos.le _
      exact ENNReal.toReal_ofReal h_nonneg
    rw [h7] at h_iff
    exact h_iff.mpr h_counter
  have h9 : ((P.biUnion Tp).card : ℝ) <
      C_doubling * Real.rpow δ (-(2 * s + ε_G)) := by
    calc
      ((P.biUnion Tp).card : ℝ) ≤ C_doubling * ncoverT.toReal := h5
      _ < C_doubling * Real.rpow δ (-(2 * s + ε_G)) := by
        gcongr
        <;> linarith
  have h10 : (M : ℝ) * δ^(-s) / (8 * C_common * C_P * C_T * K_energy) <
      C_doubling * Real.rpow δ (-(2 * s + ε_G)) :=
    lt_of_le_of_lt h4 h9
  set D : ℝ := 8 * C_common * C_P * C_T * K_energy with hD_def
  have hD_pos : 0 < D := by positivity
  have h13 : 0 < δ^(-s) := Real.rpow_pos_of_pos hδ_pos (-s)
  have h14 : (M : ℝ) * δ^(-s) < D * (C_doubling * Real.rpow δ (-(2 * s + ε_G))) := by
    have h15 : (M : ℝ) * δ^(-s) / D < C_doubling * Real.rpow δ (-(2 * s + ε_G)) := h10
    have h16 : (M : ℝ) * δ^(-s) < D * (C_doubling * Real.rpow δ (-(2 * s + ε_G))) := by
      calc
        (M : ℝ) * δ^(-s)
          = ((M : ℝ) * δ^(-s) / D) * D := by field_simp [hD_pos.ne'] <;> ring
        _ < (C_doubling * Real.rpow δ (-(2 * s + ε_G))) * D := by gcongr
        _ = D * (C_doubling * Real.rpow δ (-(2 * s + ε_G))) := by ring
    exact h16
  have h17 : Real.rpow δ (-(2 * s + ε_G)) = Real.rpow δ (-s - ε_G) * Real.rpow δ (-s) := by
    have h18 : (-(2 * s + ε_G)) = (-s - ε_G) + (-s) := by ring
    rw [h18]
    exact Real.rpow_add hδ_pos (-s - ε_G) (-s)
  have h19 : (M : ℝ) < D * C_doubling * Real.rpow δ (-s - ε_G) := by
    have h20 : D * (C_doubling * Real.rpow δ (-(2 * s + ε_G))) =
        D * C_doubling * (Real.rpow δ (-s - ε_G) * Real.rpow δ (-s)) := by
      rw [h17] <;> ring
    rw [h20] at h14
    have h21 : (M : ℝ) * δ^(-s) < D * C_doubling * (Real.rpow δ (-s - ε_G) * Real.rpow δ (-s)) := h14
    have h22 : 0 < Real.rpow δ (-s) := h13
    have h23 : (M : ℝ) * Real.rpow δ (-s) <
        (D * C_doubling * Real.rpow δ (-s - ε_G)) * Real.rpow δ (-s) := by
      have h231 : D * C_doubling * (Real.rpow δ (-s - ε_G) * Real.rpow δ (-s)) =
          (D * C_doubling * Real.rpow δ (-s - ε_G)) * Real.rpow δ (-s) := by ring
      rw [h231] at h21
      exact h21
    have h24 : 0 < Real.rpow δ (-s) := h13
    have h25 : (M : ℝ) < D * C_doubling * Real.rpow δ (-s - ε_G) := by
      have h26 : (M : ℝ) * Real.rpow δ (-s) <
          (D * C_doubling * Real.rpow δ (-s - ε_G)) * Real.rpow δ (-s) := h23
      have h27 : (M : ℝ) < D * C_doubling * Real.rpow δ (-s - ε_G) := by
        calc (M : ℝ)
          = ((M : ℝ) * Real.rpow δ (-s)) / Real.rpow δ (-s) := by field_simp [h24.ne'] <;> ring
        _ < ((D * C_doubling * Real.rpow δ (-s - ε_G)) * Real.rpow δ (-s)) / Real.rpow δ (-s) := by gcongr
        _ = D * C_doubling * Real.rpow δ (-s - ε_G) := by field_simp [h24.ne'] <;> ring
      exact h27
    exact h25
  exact le_of_lt h19

/-- A δ-ball in R² contains at most 25 points that are pairwise δ-separated.

    Uses Besicovitch.card_le_of_separated (5^finrank = 25 in dimension 2). -/
lemma at_most_25_in_delta_ball
    {δ : ℝ} (hδ_pos : 0 < δ)
    {S : Finset EuclideanPlane}
    (hS_sep : Set.Pairwise (S : Set EuclideanPlane) (fun p q => δ ≤ dist p q))
    (c : EuclideanPlane) :
    (S.filter (fun p => dist c p ≤ δ)).card ≤ 25 := by
  let Q := S.filter (fun p => dist c p ≤ δ)
  have hQ_sub : (Q : Set EuclideanPlane) ⊆ (S : Set EuclideanPlane) := by
    intro x hx
    have h : x ∈ Q := hx
    have h' : x ∈ S := (Finset.mem_filter.mp h).1
    exact h'
  have hQ_sep : Set.Pairwise (Q : Set EuclideanPlane) (fun p q => δ ≤ dist p q) := by
    intro p hp q hq hne
    exact hS_sep (hQ_sub hp) (hQ_sub hq) hne
  let f : EuclideanPlane → EuclideanPlane := fun p => (2 / δ) • (p - c)
  have hf_inj : Function.Injective f := by
    intro p q h
    have h' : (2 / δ) • (p - c) = (2 / δ) • (q - c) := h
    have h'' : p - c = q - c := by
      apply_fun (fun v : EuclideanPlane => (δ / 2 : ℝ) • v) at h'
      have h_mul : (δ / 2 : ℝ) * (2 / δ) = 1 := by field_simp [hδ_pos.ne'] <;> ring
      simpa [smul_smul, h_mul] using h'
    simpa using h''
  have h1 : ∀ p ∈ Q, ‖f p‖ ≤ 2 := by
    intro p hp
    have h2 : dist c p ≤ δ := (Finset.mem_filter.mp hp).2
    have h3 : dist p c = dist c p := dist_comm p c
    have h4 : ‖f p‖ = (2 / δ) * dist p c := by
      rw [show f p = (2 / δ) • (p - c) from rfl]
      have h_pos2 : 0 < (2 / δ : ℝ) := by positivity
      rw [norm_smul, dist_eq_norm]
      have h5 : ‖(2 / δ : ℝ)‖ = 2 / δ := by
        have h_abs : |δ| = δ := abs_of_pos hδ_pos
        simp [Real.norm_eq_abs, h_abs] <;> field_simp [hδ_pos.ne'] <;> ring
      rw [h5] <;> ring
    rw [h4, h3]
    have h5 : (2 / δ) * dist c p ≤ (2 / δ) * δ := by gcongr
    have h6 : (2 / δ) * δ = 2 := by field_simp [hδ_pos.ne'] <;> ring
    linarith
  have h3 : ∀ p ∈ Q, ∀ q ∈ Q, p ≠ q → 1 ≤ ‖f p - f q‖ := by
    intro p hp q hq hne
    have h4 : δ ≤ dist p q := hQ_sep hp hq hne
    have h5 : f p - f q = (2 / δ) • (p - q) := by
      have h51 : f p - f q = (2 / δ) • (p - c) - (2 / δ) • (q - c) := by rfl
      rw [h51]
      have h52 : (2 / δ) • (p - c) - (2 / δ) • (q - c) = (2 / δ) • ((p - c) - (q - c)) := by
        rw [← smul_sub]
      rw [h52]
      have h53 : (p - c) - (q - c) = p - q := by abel
      rw [h53]
    rw [h5]
    have h6 : ‖(2 / δ) • (p - q)‖ = (2 / δ) * ‖p - q‖ := by
      have h_pos2 : 0 < (2 / δ : ℝ) := by positivity
      rw [norm_smul]
      have h7 : ‖(2 / δ : ℝ)‖ = 2 / δ := by
        have h_abs : |δ| = δ := abs_of_pos hδ_pos
        simp [Real.norm_eq_abs, h_abs] <;> field_simp [hδ_pos.ne'] <;> ring
      rw [h7] <;> ring
    rw [h6]
    have h7 : ‖p - q‖ = dist p q := by rw [dist_eq_norm]
    rw [h7]
    have h8 : (2 / δ) * dist p q ≥ (2 / δ) * δ := by gcongr
    have h9 : (2 / δ) * δ = 2 := by field_simp [hδ_pos.ne'] <;> ring
    linarith
  let Q' := Q.image f
  have hQ'_card : Q'.card = Q.card := Finset.card_image_of_injective _ hf_inj
  have hBs1 : ∀ x ∈ Q', ‖x‖ ≤ 2 := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨p, hp, rfl⟩
    exact h1 p hp
  have hBs2 : ∀ x ∈ Q', ∀ y ∈ Q', x ≠ y → 1 ≤ ‖x - y‖ := by
    intro x hx y hy hne
    rcases Finset.mem_image.mp hx with ⟨p, hp, hpx⟩
    rcases Finset.mem_image.mp hy with ⟨q, hq, hqy⟩
    have hpnq : p ≠ q := by
      intro h
      have : f p = f q := by rw [h]
      rw [hpx, hqy] at this
      exact hne this
    have h10 : f p = x := hpx
    have h11 : f q = y := hqy
    have h12 : 1 ≤ ‖f p - f q‖ := h3 p hp q hq hpnq
    rw [h10, h11] at h12
    exact h12
  have h_finrank : Module.finrank ℝ EuclideanPlane = 2 := by simp
  have h_main : Q'.card ≤ 25 := by
    have h := Besicovitch.card_le_of_separated (E := EuclideanPlane) Q' hBs1 hBs2
    rw [h_finrank] at h
    <;> norm_num at h ⊢ <;> exact h
  rw [← hQ'_card]
  exact h_main

/-- Packing-covering inequality: for a finite δ-separated set S in R²,
    |S| ≤ 25 · N_δ(S). -/
lemma separated_card_le_25_cover
    {δ : ℝ} (hδ_pos : 0 < δ)
    {S : Finset EuclideanPlane}
    (hS_sep : Set.Pairwise (S : Set EuclideanPlane) (fun p q => δ ≤ dist p q)) :
    (S.card : ENat) ≤ 25 * Metric.externalCoveringNumber δ.toNNReal (S : Set EuclideanPlane) := by
  have hS_fin : (S : Set EuclideanPlane).Finite := Finset.finite_toSet S
  have h_ne_top : Metric.externalCoveringNumber δ.toNNReal (S : Set EuclideanPlane) ≠ ⊤ := by
    have h : Metric.externalCoveringNumber δ.toNNReal (S : Set EuclideanPlane) ≤ (S : Set EuclideanPlane).encard :=
      Metric.externalCoveringNumber_le_encard_self _
    have h2 : (S : Set EuclideanPlane).encard < ⊤ := Set.Finite.encard_lt_top hS_fin
    exact ne_of_lt (lt_of_le_of_lt h h2)
  letI : Nonempty {C : Set EuclideanPlane // Metric.IsCover δ.toNNReal (S : Set EuclideanPlane) C} :=
    ⟨⟨(S : Set EuclideanPlane), by simp⟩⟩
  have h_exists := ENat.exists_eq_iInf
    (fun (C : {C : Set EuclideanPlane // Metric.IsCover δ.toNNReal (S : Set EuclideanPlane) C}) =>
      (C.val : Set EuclideanPlane).encard)
  rcases h_exists with ⟨C, hC_eq⟩
  have hC_cover : Metric.IsCover δ.toNNReal (S : Set EuclideanPlane) C.val := C.property
  have hC_encard : C.val.encard = Metric.externalCoveringNumber δ.toNNReal (S : Set EuclideanPlane) := by
    rw [hC_eq]
    simp_rw [Metric.externalCoveringNumber, iInf_subtype]
    <;> rfl
  have hC_fin : C.val.Finite := by
    have h : C.val.encard ≠ ⊤ := by rw [hC_encard]; exact h_ne_top
    exact Set.encard_ne_top_iff.mp h
  let Cfin := hC_fin.toFinset
  have hCfin_coe : (Cfin : Set EuclideanPlane) = C.val := by
    exact hC_fin.coe_toFinset
  have hCfin_card : (Cfin.card : ENat) = C.val.encard := by
    have h1 : (Cfin : Set EuclideanPlane) = C.val := hC_fin.coe_toFinset
    have h2 : (Cfin : Set EuclideanPlane).encard = ↑Cfin.card := by simp
    rw [← h2, h1]
  have h_cover : ∀ p ∈ S, ∃ c ∈ Cfin, dist p c ≤ δ := by
    intro p hp
    have h6 : p ∈ (S : Set EuclideanPlane) := by exact_mod_cast hp
    have h7 : ∃ c, c ∈ C.val ∧ edist p c ≤ (δ.toNNReal : ENNReal) := hC_cover h6
    rcases h7 with ⟨c, hc, h8⟩
    have h9 : c ∈ Cfin := by
      have h10 : c ∈ (Cfin : Set EuclideanPlane) := by
        simpa [hCfin_coe] using hc
      exact Finset.mem_coe.mp h10
    have h11 : dist p c ≤ δ := by
      by_cases h14 : p = c
      · rw [h14] <;> simp [hδ_pos.le]
      · have h15 : edist p c = ENNReal.ofReal (dist p c) := by
          rw [edist_dist] <;> simp [h14]
        rw [h15] at h8
        exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h8
    exact ⟨c, h9, h11⟩
  let g : EuclideanPlane → Finset EuclideanPlane := fun c => S.filter (fun p => dist p c ≤ δ)
  have h12 : S ⊆ Cfin.biUnion g := by
    intro p hp
    rcases h_cover p hp with ⟨c, hc, hdist⟩
    exact Finset.mem_biUnion.mpr ⟨c, hc, Finset.mem_filter.mpr ⟨hp, hdist⟩⟩
  have h_sum : S.card ≤ ∑ c ∈ Cfin, (g c).card := by
    have h13 : S.card ≤ (Cfin.biUnion g).card := Finset.card_le_card h12
    have h14 : (Cfin.biUnion g).card ≤ ∑ c ∈ Cfin, (g c).card :=
      Finset.card_biUnion_le
    exact le_trans h13 h14
  have h_each : ∀ c ∈ Cfin, (g c).card ≤ 25 := by
    intro c _
    have h_eq : g c = S.filter (fun p => dist c p ≤ δ) := by
      apply Finset.ext
      intro p
      simp [g, dist_comm c p]
    rw [h_eq]
    exact at_most_25_in_delta_ball hδ_pos hS_sep c
  calc (S.card : ENat)
    ≤ ↑(∑ c ∈ Cfin, (g c).card) := by exact_mod_cast h_sum
  _ ≤ ↑(∑ c ∈ Cfin, 25) := by
    exact_mod_cast Finset.sum_le_sum h_each
  _ = ↑(25 * Cfin.card) := by simp [Finset.sum_const] <;> ring
  _ = 25 * C.val.encard := by
    have h_eq : (↑(25 * Cfin.card) : ENat) = 25 * (Cfin.card : ENat) := by
      simp [mul_comm]
      <;> norm_cast
    rw [h_eq, hCfin_card]
  _ = 25 * Metric.externalCoveringNumber δ.toNNReal (S : Set EuclideanPlane) := by
    rw [hC_encard]

/-- Lemma A: Ball growth bound from S-set property.

    If P is a finite δ-separated (δ,t,C)-set, then for any ball B(c,r) with r ≥ δ:
    |P ∩ B(c,r)| ≤ 25 · C · r^t · |P| -/
lemma sset_ball_growth
    {δ t C : ℝ} {P : Finset EuclideanPlane}
    (hδ_pos : 0 < δ) (ht : 0 ≤ t) (hC_pos : 0 < C)
    (hP_sep : Set.Pairwise (P : Set EuclideanPlane) (fun p q => δ ≤ dist p q))
    (hP_sset : IsDeltaSSet δ t C (P : Set EuclideanPlane)) :
    ∀ (c : EuclideanPlane) (r : ℝ), δ ≤ r →
      ((P.filter (fun y => dist c y ≤ r)).card : ℝ) ≤
        (25 : ℝ) * C * r^t * (P.card : ℝ) := by
  intro c r hr
  let S : Set EuclideanPlane := (P : Set EuclideanPlane) ∩ Metric.closedBall c r
  let Pfin := P.filter (fun y => dist c y ≤ r)
  have hS_eq : (Pfin : Set EuclideanPlane) = S := by
    ext x
    have h_dist : dist c x = dist x c := dist_comm c x
    simp [Pfin, S, Metric.mem_closedBall, h_dist]
  have hPfin_sep : Set.Pairwise (Pfin : Set EuclideanPlane) (fun p q => δ ≤ dist p q) := by
    intro p hp q hq hne
    have hps : p ∈ (P : Set EuclideanPlane) := by
      simp only [Pfin, Finset.mem_coe, Finset.mem_filter] at hp <;> exact hp.1
    have hqs : q ∈ (P : Set EuclideanPlane) := by
      simp only [Pfin, Finset.mem_coe, Finset.mem_filter] at hq <;> exact hq.1
    exact hP_sep hps hqs hne
  have h1 : (Pfin.card : ENat) ≤ 25 * Metric.externalCoveringNumber δ.toNNReal S := by
    rw [show S = (Pfin : Set EuclideanPlane) from hS_eq.symm]
    exact separated_card_le_25_cover hδ_pos hPfin_sep
  have h2 : (Metric.externalCoveringNumber δ.toNNReal S : ENNReal) ≤
      ENNReal.ofReal C * (ENNReal.ofReal r) ^ t *
        (Metric.externalCoveringNumber δ.toNNReal (P : Set EuclideanPlane) : ENNReal) :=
    hP_sset.2.2.2.2 c r hr
  have h3 : Metric.externalCoveringNumber δ.toNNReal (P : Set EuclideanPlane) ≤
      (P : Set EuclideanPlane).encard :=
    Metric.externalCoveringNumber_le_encard_self (P : Set EuclideanPlane)
  have h4 : (Pfin.card : ENNReal) ≤
      (25 : ENNReal) * ENNReal.ofReal C * (ENNReal.ofReal r) ^ t *
        ENNReal.ofReal (P.card : ℝ) := by
    have h5 : (Pfin.card : ENNReal) ≤
        (25 : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal S : ENNReal) := by
      exact_mod_cast h1
    have h6 : (Metric.externalCoveringNumber δ.toNNReal S : ENNReal) ≤
        ENNReal.ofReal C * (ENNReal.ofReal r) ^ t *
          (Metric.externalCoveringNumber δ.toNNReal (P : Set EuclideanPlane) : ENNReal) := h2
    have h7 : (Metric.externalCoveringNumber δ.toNNReal (P : Set EuclideanPlane) : ENNReal) ≤
        ENNReal.ofReal (P.card : ℝ) := by
      have h8 : (Metric.externalCoveringNumber δ.toNNReal (P : Set EuclideanPlane) : ENNReal) ≤
          ((P : Set EuclideanPlane).encard : ENNReal) := by exact_mod_cast h3
      have h9 : ((P : Set EuclideanPlane).encard : ENNReal) = ENNReal.ofReal (P.card : ℝ) := by
        simp
      rw [h9] at h8
      exact h8
    calc (Pfin.card : ENNReal)
      ≤ (25 : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal S : ENNReal) := h5
    _ ≤ (25 : ENNReal) * (ENNReal.ofReal C * (ENNReal.ofReal r) ^ t *
          (Metric.externalCoveringNumber δ.toNNReal (P : Set EuclideanPlane) : ENNReal)) := by gcongr
    _ ≤ (25 : ENNReal) * (ENNReal.ofReal C * (ENNReal.ofReal r) ^ t *
          ENNReal.ofReal (P.card : ℝ)) := by gcongr
    _ = (25 : ENNReal) * ENNReal.ofReal C * (ENNReal.ofReal r) ^ t *
          ENNReal.ofReal (P.card : ℝ) := by ring
  have h_pos : 0 ≤ (25 : ℝ) * C * r^t * (P.card : ℝ) := by
    have hr_pos : 0 ≤ r := by linarith
    positivity
  have h_final : ENNReal.ofReal ((Pfin.card : ℝ)) ≤
      ENNReal.ofReal ((25 : ℝ) * C * r^t * (P.card : ℝ)) := by
    have h_rt : (ENNReal.ofReal r) ^ t = ENNReal.ofReal (r^t) := by
      rw [← ENNReal.ofReal_rpow_of_nonneg (by linarith) ht] <;> rfl
    have h25 : (25 : ENNReal) = ENNReal.ofReal (25 : ℝ) := by simp
    have h_conv : ENNReal.ofReal ((25 : ℝ) * C * r^t * (P.card : ℝ)) =
        (25 : ENNReal) * ENNReal.ofReal C * (ENNReal.ofReal r) ^ t *
          ENNReal.ofReal (P.card : ℝ) := by
      have hr_nonneg : 0 ≤ r := by linarith
      have h_rt_nonneg : 0 ≤ r^t := Real.rpow_nonneg hr_nonneg t
      have h_pos25 : 0 ≤ (25 : ℝ) := by norm_num
      have h_posC : 0 ≤ C := by linarith
      have h_poscard : 0 ≤ (P.card : ℝ) := by positivity
      have h_a : ENNReal.ofReal ((25 : ℝ) * C) = ENNReal.ofReal (25 : ℝ) * ENNReal.ofReal C := by
        simp [ENNReal.ofReal_mul, h_pos25, h_posC]
      have h_posac : 0 ≤ (25 : ℝ) * C := by positivity
      have h_b : ENNReal.ofReal (((25 : ℝ) * C) * r^t) = ENNReal.ofReal ((25 : ℝ) * C) * ENNReal.ofReal (r^t) := by
        simp [ENNReal.ofReal_mul, h_posac, h_rt_nonneg]
      have h_posabc : 0 ≤ ((25 : ℝ) * C) * r^t := by positivity
      have h_c : ENNReal.ofReal ((((25 : ℝ) * C) * r^t) * (P.card : ℝ)) =
          ENNReal.ofReal (((25 : ℝ) * C) * r^t) * ENNReal.ofReal (P.card : ℝ) := by
        simp [ENNReal.ofReal_mul, h_posabc, h_poscard]
      have h_assoc : (25 : ℝ) * C * r^t * (P.card : ℝ) = (((25 : ℝ) * C) * r^t) * (P.card : ℝ) := by ring
      rw [h_assoc, h_c, h_b, h_a, h_rt, h25] <;> ring
    have h4' : (↑Pfin.card : ENNReal) ≤
        (25 : ENNReal) * ENNReal.ofReal C * (ENNReal.ofReal r) ^ t *
          ENNReal.ofReal (P.card : ℝ) := h4
    have h_eq : (↑Pfin.card : ENNReal) = ENNReal.ofReal (Pfin.card : ℝ) := by simp
    rw [h_eq] at h4'
    rw [h_conv]
    exact h4'
  exact (ENNReal.ofReal_le_ofReal_iff h_pos).mp h_final

end DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.FrontEndExtraction
