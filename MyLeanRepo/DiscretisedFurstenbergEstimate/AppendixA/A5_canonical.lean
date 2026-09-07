module

/-
  Appendix A, Step A5: Freeze global fine-child multiplicities (CANONICAL).

  Given A4_Output with per-square C_Q_pi (good directions from RKP),
  construct a global coarse family C_global and uniform DISTINCT fine-child
  count N satisfying G1-G4 quantitative bounds.

  Uses dyadic binning by |globalFiber(T_full, U)| (distinct count, not incidence),
  following OS lines 1427-1454.

  Key definitions:
  - T_full = actual global fine tube family (union of all T_Q(p))
  - n(U) = |globalFiber(T_full, U)| = distinct fine tubes with parent U
  - cm(U) = coarse membership = number of Q with U ∈ C_Q_pi(Q)
  - Layer by n(U) into dyadic bins, pick bin with large coarse incidence
  - 2s-bound gives layer size; partition gives N bound

  Whiteprint node: appendix_a_alternative / A5
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.Interfaces
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A5_LooseCore
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A4_CQpiSSet
public import MyLeanRepo.DiscretisedFurstenbergEstimate.HeavySquareRefinement
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

attribute [local instance] Classical.propDecidable

namespace DirecretisedFurstenbergEstimate.AppendixA5

open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.AppendixA
open DirecretisedFurstenbergEstimate.Lagoon (squareCenter)

abbrev Plane := EuclideanPlane
abbrev CoarseTube := AffineLine
abbrev FineTube := AffineLine

/-- Generalized subset transfer for IsDeltaSSet. -/
lemma IsDeltaSSet.subset_with_cover_ratio {X : Type*} [PseudoMetricSpace X]
    {δ s C K : ℝ} {S S' : Set X}
    (hS : IsDeltaSSet δ s C S)
    (hS'_sub : S' ⊆ S)
    (hK_pos : 0 < K)
    (h_ratio : (Metric.externalCoveringNumber δ.toNNReal S : ENNReal) ≤
               ENNReal.ofReal K * (Metric.externalCoveringNumber δ.toNNReal S')) :
    IsDeltaSSet δ s (K * C) S' := by
  rcases hS with ⟨hS_nonempty, hδ_pos, hC_pos, hs_nonneg, h_main⟩
  have hKC_pos : 0 < K * C := mul_pos hK_pos hC_pos
  have hS'_nonempty : S'.Nonempty := by
    by_contra h
    have h_empty : S' = ∅ := by simpa [Set.not_nonempty_iff_eq_empty] using h
    rw [h_empty] at h_ratio
    have h_zero : (Metric.externalCoveringNumber δ.toNNReal S : ENNReal) = 0 := by
      simpa [Metric.externalCoveringNumber_empty] using h_ratio
    have h_zero' : Metric.externalCoveringNumber δ.toNNReal S = 0 := by exact_mod_cast h_zero
    have hS_empty : S = ∅ := Metric.externalCoveringNumber_eq_zero.mp h_zero'
    rw [hS_empty] at hS_nonempty
    simp at hS_nonempty
  refine' ⟨hS'_nonempty, hδ_pos, hKC_pos, hs_nonneg, _⟩
  intro x r hr
  have h_sub_set : S' ∩ Metric.closedBall x r ⊆ S ∩ Metric.closedBall x r := by
    intro y hy; exact ⟨hS'_sub hy.1, hy.2⟩
  have h1 : (Metric.externalCoveringNumber δ.toNNReal (S' ∩ Metric.closedBall x r) : ENNReal) ≤
           (Metric.externalCoveringNumber δ.toNNReal (S ∩ Metric.closedBall x r) : ENNReal) := by
    exact_mod_cast Metric.externalCoveringNumber_mono_set h_sub_set
  have h2 := h_main x r hr
  have hC_nonneg : 0 ≤ C := by linarith
  have hKC_nonneg : 0 ≤ K * C := by linarith
  calc
    (Metric.externalCoveringNumber δ.toNNReal (S' ∩ Metric.closedBall x r) : ENNReal)
      ≤ (Metric.externalCoveringNumber δ.toNNReal (S ∩ Metric.closedBall x r) : ENNReal) := h1
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
          Metric.externalCoveringNumber δ.toNNReal S := h2
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
          (ENNReal.ofReal K * Metric.externalCoveringNumber δ.toNNReal S') := by
      gcongr <;> exact h_ratio
    _ = ENNReal.ofReal (K * C) * (ENNReal.ofReal r) ^ s *
          Metric.externalCoveringNumber δ.toNNReal S' := by
      have h_mul : ENNReal.ofReal C * ENNReal.ofReal K = ENNReal.ofReal (C * K) := by
        rw [← ENNReal.ofReal_mul hC_nonneg] <;> ring
      let X := Metric.externalCoveringNumber δ.toNNReal S'
      let b := (ENNReal.ofReal r) ^ s
      have h_comm : ENNReal.ofReal C * b * (ENNReal.ofReal K * X) =
                       (ENNReal.ofReal C * ENNReal.ofReal K) * b * X := by ring
      rw [h_comm, h_mul] <;> ring_nf <;> rfl

set_option maxHeartbeats 2000000 in
/-- A5: Freeze global fine-child multiplicities using DISTINCT fiber counts.

  Dyadic binning argument (OS lines 1427-1454):
  1. Bin all occupied coarse parents by |globalFiber(T_full, U)|
  2. Pick bin maximizing coarse membership incidence
  3. Extract good squares with many tubes in selected bin
  4. Apply 2s-bound to get lower bound on selected layer size
  5. Partition identity gives N upper bound

  Inputs:
  - a4: A4 output with per-square C_Q_pi
  - C_global_A2: global coarse family (must have distinct parent cells)
  - hT_full_upper: |T_full| ≤ Δ^{-(4s+3ε)} (from counter-assumption)
  - hC_global_A2_distinct: C_global_A2 has at most one tube per parent cell
-/
theorem A5_freeze_multiplicities_main
    (Δ δ s t ε : ℝ)
    (hΔ_pos : 0 < Δ) (hΔ_lt_half : Δ < 1 / 2)
    (hs : 0 < s) (hs1 : s < 1) (hst : s < t) (ht2 : t < 2)
    (hε_pos : 0 < ε) (hε_lt_one : ε < 1)
    (hε_small : 55 * ε ≤ 2 * (t - s))
    (a4 : A4_Output Δ δ s t ε)
    (C_global_A2 : Finset CoarseTube)
    (hCglobal_A2_upper : (C_global_A2.card : ℝ) ≤ Real.rpow Δ (-2 * s - 3 * ε))
    (hC_Q_pi_sub_global : ∀ Q hQ,
      (a4.perSquare Q hQ).C_Q_pi ⊆ C_global_A2)
    -- Upper bound on DISTINCT global fine tube count (from counter-assumption)
    (hT_full_upper : (a5FullFineFamily Δ δ s t ε a4.Qset a4.perSquare).card ≤
        Real.rpow Δ (-(4 * s + 3 * ε)))
    -- C_global_A2 has distinct parent cells (one CoarseTube per dyadic cell)
    (hC_global_A2_distinct : ∀ (U1 : CoarseTube), U1 ∈ C_global_A2 →
      ∀ (U2 : CoarseTube), U2 ∈ C_global_A2 → U1 ≠ U2 →
      parentCell Δ hΔ_pos U1 ≠ parentCell Δ hΔ_pos U2)
    -- 2s-bound for C_Q_pi families
    (h_2s_bound : TwoSBoundWithLower Δ s t ε a4.Qset
        (fun Q hQ => (a4.perSquare Q hQ).C_Q_pi) C_global_A2
        (-2 * s + 210 * ε))
    (hQset_size_lower : (a4.Qset.card : ℝ) ≥ Real.rpow Δ (-t + 4 * ε))
    (hQset_size_upper : (a4.Qset.card : ℝ) ≤ Real.rpow Δ (-t - ε))
    (hK_bound : (4 * s + 3 * ε) * Real.log (1 / Δ) / Real.log 2 + 1 ≤
        Real.rpow Δ (-2 * ε) / 2)
    (hΔ_3ε : Real.rpow Δ (-3 * ε) ≥ 2) :
    ∃ (out : A5_Output Δ δ s t ε), out.C_global_input = C_global_A2 ∧ out.Qset ⊆ a4.Qset := by
  let T_full : Finset FineTube := a5FullFineFamily Δ δ s t ε a4.Qset a4.perSquare
  let n : CoarseTube → ℕ := fun U => (globalFiber Δ hΔ_pos T_full U).card
  -- Total function version of C_Q_pi, for use in filters
  let C' : CoarseSquare Δ → Finset CoarseTube := fun Q =>
    if hQ : Q ∈ a4.Qset then (a4.perSquare Q hQ).C_Q_pi else ∅
  let cm : CoarseTube → ℕ := fun U =>
    (a4.Qset.filter (fun Q => U ∈ C' Q)).card
  let T_Δ : Finset CoarseTube := C_global_A2.filter (fun U => 0 < n U)

  have hTΔ_sub : T_Δ ⊆ C_global_A2 := Finset.filter_subset _ _
  have hTΔ_distinct : ∀ (U1 : CoarseTube), U1 ∈ T_Δ →
      ∀ (U2 : CoarseTube), U2 ∈ T_Δ → U1 ≠ U2 →
      parentCell Δ hΔ_pos U1 ≠ parentCell Δ hΔ_pos U2 := by
    intro U1 hU1 U2 hU2 hne
    exact hC_global_A2_distinct U1 (hTΔ_sub hU1) U2 (hTΔ_sub hU2) hne

  -- General double-counting identity: Σ_U cm(U) over T = Σ_Q |C'_Q ∩ T|
  have h_double_count : ∀ (T : Finset CoarseTube),
      ∑ U ∈ T, (cm U : ℝ) = ∑ Q ∈ a4.Qset, (((C' Q).filter (· ∈ T)).card : ℝ) := by
    intro T
    have h1 : ∀ (U : CoarseTube), (cm U : ℝ) = ∑ Q ∈ a4.Qset, (if U ∈ C' Q then (1 : ℝ) else 0) := by
      intro U
      have h2 : (cm U : ℝ) = ((a4.Qset.filter (fun Q => U ∈ C' Q)).card : ℝ) := by rfl
      have h3 : ∑ Q ∈ a4.Qset, (if U ∈ C' Q then (1 : ℕ) else 0) =
          (a4.Qset.filter (fun Q => U ∈ C' Q)).card := by
        rw [Finset.sum_ite] <;> simp [Finset.sum_const_zero] <;> ring
      have h4 : ∑ Q ∈ a4.Qset, (if U ∈ C' Q then (1 : ℝ) else 0) =
          ((a4.Qset.filter (fun Q => U ∈ C' Q)).card : ℝ) := by
        have h5 : ∀ Q ∈ a4.Qset, (if U ∈ C' Q then (1 : ℝ) else 0) = ↑(if U ∈ C' Q then (1 : ℕ) else 0) := by
          intro Q _; split_ifs <;> norm_num
        rw [Finset.sum_congr rfl h5, ← Nat.cast_sum, h3]
      rw [h2, h4]
    have h1' : ∑ U ∈ T, (cm U : ℝ) =
        ∑ U ∈ T, ∑ Q ∈ a4.Qset, (if U ∈ C' Q then (1 : ℝ) else 0) :=
      Finset.sum_congr rfl (fun x _ => h1 x)
    rw [h1']
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro Q _
    have h4 : ∑ U ∈ T, (if U ∈ C' Q then (1 : ℝ) else 0) =
        (((C' Q).filter (· ∈ T)).card : ℝ) := by
      have h5 : ∑ U ∈ T, (if U ∈ C' Q then (1 : ℕ) else 0) =
          (T.filter (fun U => U ∈ C' Q)).card := by
        rw [Finset.sum_ite] <;> simp [Finset.sum_const_zero] <;> ring
      have h6 : T.filter (fun U => U ∈ C' Q) = (C' Q).filter (· ∈ T) := by
        ext x; simp [Finset.mem_filter] <;> tauto
      have h7 : ∑ U ∈ T, (if U ∈ C' Q then (1 : ℝ) else 0) =
          ((T.filter (fun U => U ∈ C' Q)).card : ℝ) := by
        have h8 : ∀ U ∈ T, (if U ∈ C' Q then (1 : ℝ) else 0) = ↑(if U ∈ C' Q then (1 : ℕ) else 0) := by
          intro U _; split_ifs <;> norm_num
        rw [Finset.sum_congr rfl h8, ← Nat.cast_sum, h5]
      rw [h7, h6]
    exact h4

  have hΔ_lt_one : Δ < 1 := by linarith
  have hΔ_le_one : Δ ≤ 1 := by linarith
  have h_rpow_pos : ∀ (x : ℝ), 0 < Real.rpow Δ x := fun x => Real.rpow_pos_of_pos hΔ_pos x
  have h_rpow_mul : ∀ (a b : ℝ), Real.rpow Δ a * Real.rpow Δ b = Real.rpow Δ (a + b) := by
    intro a b; exact (Real.rpow_add hΔ_pos a b).symm

  -- Helper: Δ^a / Δ^b = Δ^(a-b)
  have h_rpow_div : ∀ (a b : ℝ), Real.rpow Δ a / Real.rpow Δ b = Real.rpow Δ (a - b) := by
    intro a b
    have h1 : Real.rpow Δ a = Real.rpow Δ (a - b) * Real.rpow Δ b := by
      have h2 : (a - b) + b = a := by ring
      rw [h_rpow_mul (a - b) b, h2]
    rw [h1]
    have h3 : 0 < Real.rpow Δ b := h_rpow_pos b
    field_simp [h3.ne'] <;> ring

  -- Δ^{3ε} ≤ 1/2 (from Δ^{-3ε} ≥ 2)
  have hΔ3ε_le_half : Real.rpow Δ (3 * ε) ≤ 1 / 2 := by
    have h1 : Real.rpow Δ (-3 * ε) ≥ 2 := hΔ_3ε
    have h2 : Real.rpow Δ (3 * ε) * Real.rpow Δ (-3 * ε) = 1 := by
      rw [h_rpow_mul (3 * ε) (-3 * ε)] <;> ring_nf <;> norm_num
    have h3 : 0 < Real.rpow Δ (3 * ε) := h_rpow_pos (3 * ε)
    nlinarith

  -- Δ^{2ε} ≤ 1/2 (from hK_bound: LHS ≥ 1 ≤ Δ^{-2ε}/2)
  have hΔ2ε_le_half : Real.rpow Δ (2 * ε) ≤ 1 / 2 := by
    have h_pos1 : 0 < 4 * s + 3 * ε := by linarith
    have h_pos2 : 0 < Real.log (1 / Δ) := by
      have h : 1 < 1 / Δ := by
        apply one_lt_one_div
        <;> linarith
      exact Real.log_pos h
    have h_pos3 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h2 : 0 ≤ (4 * s + 3 * ε) * Real.log (1 / Δ) / Real.log 2 := by
      apply div_nonneg
      · exact mul_nonneg h_pos1.le h_pos2.le
      · exact h_pos3.le
    have h1 : (1 : ℝ) ≤ Real.rpow Δ (-2 * ε) / 2 := by
      linarith [hK_bound, h2]
    have h3 : Real.rpow Δ (-2 * ε) ≥ 2 := by linarith
    have h4 : Real.rpow Δ (2 * ε) * Real.rpow Δ (-2 * ε) = 1 := by
      rw [h_rpow_mul (2 * ε) (-2 * ε)] <;> ring_nf <;> norm_num
    have h5 : 0 < Real.rpow Δ (2 * ε) := h_rpow_pos (2 * ε)
    nlinarith

  -- C_Q_pi ⊆ T_Δ: H2 gives positive incidence → at least one distinct tube
  have hC_sub_TΔ : ∀ Q hQ, ((a4.perSquare Q hQ).C_Q_pi : Set CoarseTube) ⊆ (T_Δ : Set CoarseTube) := by
    intro Q hQ T hT
    let sd := a4.perSquare Q hQ
    have h_in_CQ : T ∈ sd.base.C_Q := sd.hC_Q_pi_sub hT
    have h_in_global : T ∈ C_global_A2 := hC_Q_pi_sub_global Q hQ hT
    have hH2 : sd.base.H_Q ≤ ↑(∑ p ∈ sd.base.P_Q,
        assignedCountDyadic Δ hΔ_pos sd.base.T_Q p T) := sd.base.hH2 T h_in_CQ
    have h_pos : 0 < sd.base.H_Q := sd.base.hH_Q_pos
    have h_contrib : 0 < (↑(∑ p ∈ sd.base.P_Q,
        assignedCountDyadic Δ hΔ_pos sd.base.T_Q p T) : ℝ) :=
      lt_of_lt_of_le h_pos hH2
    have h_n_pos : 0 < n T := by
      have h1 : (∑ p ∈ sd.base.P_Q, assignedCountDyadic Δ hΔ_pos sd.base.T_Q p T) > 0 :=
        by exact_mod_cast h_contrib
      have h2 : ∃ p ∈ sd.base.P_Q, 0 < assignedCountDyadic Δ hΔ_pos sd.base.T_Q p T := by
        by_contra h
        push Not at h
        have h3 : ∑ p ∈ sd.base.P_Q, assignedCountDyadic Δ hΔ_pos sd.base.T_Q p T = 0 := by
          apply Finset.sum_eq_zero
          intro p hp
          have h4 : assignedCountDyadic Δ hΔ_pos sd.base.T_Q p T ≤ 0 := h p hp
          omega
        rw [h3] at h1
        <;> simp at h1
      rcases h2 with ⟨p, hp, hpos⟩
      have h4 : ∃ T_fine ∈ sd.base.T_Q p, InParent Δ hΔ_pos T_fine T := by
        have h5 : ((sd.base.T_Q p).filter (fun T_fine => InParent Δ hΔ_pos T_fine T)).Nonempty :=
          Finset.card_pos.mp hpos
        rcases h5 with ⟨T_fine, hT_fine⟩
        have hT_in : T_fine ∈ sd.base.T_Q p := (Finset.mem_filter.mp hT_fine).1
        have hInP : InParent Δ hΔ_pos T_fine T := (Finset.mem_filter.mp hT_fine).2
        exact ⟨T_fine, hT_in, hInP⟩
      rcases h4 with ⟨T_fine, hT_fine, h_inparent⟩
      have h5 : T_fine ∈ T_full := by
        dsimp only [T_full, a5FullFineFamily]
        apply Finset.mem_biUnion.mpr
        refine ⟨⟨Q, hQ⟩, by simp, ?_⟩
        apply Finset.mem_biUnion.mpr
        exact ⟨p, hp, hT_fine⟩
      have h6 : T_fine ∈ globalFiber Δ hΔ_pos T_full T := by
        dsimp only [globalFiber]
        rw [Finset.mem_filter] <;> exact ⟨h5, h_inparent⟩
      exact Finset.card_pos.mpr ⟨T_fine, h6⟩
    exact Finset.mem_filter.mpr ⟨h_in_global, h_n_pos⟩

  -- C_Q_pi cardinality bounds
  have hC_pi_lower : ∀ Q hQ, ((a4.perSquare Q hQ).C_Q_pi.card : ℝ) ≥ Real.rpow Δ (-s + 12 * ε) := by
    intro Q hQ
    let sd := a4.perSquare Q hQ
    have h1 : (sd.base.C_Q.card : ℝ) ≥ Real.rpow Δ (-s + 11 * ε) := sd.base.hC_card_lower
    have h2 : (sd.C_Q_pi.card : ℝ) ≥ (sd.base.C_Q.card : ℝ) * Real.rpow Δ ε := by
      have h3 : (sd.base.C_Q.card : ℝ) ≤ Real.rpow Δ (-ε) * (sd.C_Q_pi.card : ℝ) := sd.hC_Q_pi_card
      have h4 : 0 < Real.rpow Δ ε := h_rpow_pos ε
      have h5 : Real.rpow Δ (-ε) * Real.rpow Δ ε = 1 := by
        have h6 : Real.rpow Δ (-ε) * Real.rpow Δ ε = Real.rpow Δ ((-ε) + ε) := h_rpow_mul (-ε) ε
        rw [h6]
        have h7 : (-ε : ℝ) + ε = 0 := by ring
        rw [h7]
        simp
      nlinarith
    calc (sd.C_Q_pi.card : ℝ)
      ≥ (sd.base.C_Q.card : ℝ) * Real.rpow Δ ε := h2
    _ ≥ Real.rpow Δ (-s + 11 * ε) * Real.rpow Δ ε := by
      gcongr <;> exact (h_rpow_pos ε).le
    _ = Real.rpow Δ (-s + 12 * ε) := by rw [h_rpow_mul (-s + 11 * ε) ε] <;> ring_nf

  have hC_pi_upper : ∀ Q hQ, ((a4.perSquare Q hQ).C_Q_pi.card : ℝ) ≤ Real.rpow Δ (-s - 29 * ε) := by
    intro Q hQ
    let sd := a4.perSquare Q hQ
    have h1 : (sd.C_Q_pi.card : ℝ) ≤ (sd.base.C_Q.card : ℝ) := by exact_mod_cast Finset.card_le_card sd.hC_Q_pi_sub
    have h2 : (sd.base.C_Q.card : ℝ) ≤ Real.rpow Δ (-s - 29 * ε) := sd.hC_card_upper
    exact le_trans h1 h2

  let C : (Q : CoarseSquare Δ) → Q ∈ a4.Qset → Finset CoarseTube :=
    fun Q hQ => (a4.perSquare Q hQ).C_Q_pi
  have hC'_eq : ∀ (Q : CoarseSquare Δ), ∀ (hQ : Q ∈ a4.Qset), C' Q = C Q hQ := by
    intro Q hQ
    simp [C', C, hQ]

  -- Total coarse incidence: Σ_U cm(U) = Σ_Q |C_Q_pi(Q)|
  have h_total_cm : ∑ U ∈ T_Δ, (cm U : ℝ) ≥ Real.rpow Δ (-s - t + 16 * ε) := by
    have h_cm_sum : ∑ U ∈ T_Δ, (cm U : ℝ) =
        ∑ Q ∈ a4.Qset, (((C' Q).filter (· ∈ T_Δ)).card : ℝ) :=
      h_double_count T_Δ
    rw [h_cm_sum]
    have h3 : ∀ Q ∈ a4.Qset, (C' Q).filter (· ∈ T_Δ) = C' Q := by
      intro Q hQ
      apply Finset.filter_true_of_mem
      intro U hU
      have h4 : U ∈ C Q hQ := by
        have h5 : C' Q = C Q hQ := hC'_eq Q hQ
        exact h5 ▸ hU
      exact hC_sub_TΔ Q hQ h4
    have h4 : ∑ Q ∈ a4.Qset, (((C' Q).filter (· ∈ T_Δ)).card : ℝ) =
        ∑ Q ∈ a4.Qset, ((C' Q).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro Q hQ
      rw [h3 Q hQ]
    rw [h4]
    have h2 : ∀ Q ∈ a4.Qset, ((C' Q).card : ℝ) ≥ Real.rpow Δ (-s + 12 * ε) := by
      intro Q hQ
      rw [hC'_eq Q hQ]
      exact hC_pi_lower Q hQ
    have h3 : ∑ Q ∈ a4.Qset, ((C' Q).card : ℝ) ≥
        (a4.Qset.card : ℝ) * Real.rpow Δ (-s + 12 * ε) := by
      have h4 : ∑ Q ∈ a4.Qset, ((C' Q).card : ℝ) ≥
          ∑ Q ∈ a4.Qset, Real.rpow Δ (-s + 12 * ε) := Finset.sum_le_sum h2
      have h5 : ∑ Q ∈ a4.Qset, Real.rpow Δ (-s + 12 * ε) =
          (a4.Qset.card : ℝ) * Real.rpow Δ (-s + 12 * ε) := by
        simp [Finset.sum_const] <;> ring
      rw [h5] at h4; exact h4
    have h6 : (a4.Qset.card : ℝ) ≥ Real.rpow Δ (-t + 4 * ε) := hQset_size_lower
    calc ∑ Q ∈ a4.Qset, ((C' Q).card : ℝ)
      ≥ (a4.Qset.card : ℝ) * Real.rpow Δ (-s + 12 * ε) := h3
    _ ≥ Real.rpow Δ (-t + 4 * ε) * Real.rpow Δ (-s + 12 * ε) := by gcongr <;> exact (h_rpow_pos (-s + 12 * ε)).le
    _ = Real.rpow Δ (-s - t + 16 * ε) := by rw [h_rpow_mul (-t + 4 * ε) (-s + 12 * ε)] <;> ring_nf

  -- Total distinct fine tubes upper bound
  have hD_upper : (T_full.card : ℝ) ≤ Real.rpow Δ (-(4 * s + 3 * ε)) := by
    exact_mod_cast hT_full_upper

  -- Number of dyadic layers
  let X : ℝ := (4 * s + 3 * ε) * Real.log (1 / Δ) / Real.log 2
  let K : ℕ := Nat.ceil X + 1
  have hX_pos : 0 < X := by
    have h1 : 0 < 4 * s + 3 * ε := by linarith
    have hΔ_lt_one : Δ < 1 := by linarith
    have h2 : 0 < Real.log (1 / Δ) := Real.log_pos (one_lt_one_div hΔ_pos hΔ_lt_one)
    have h3 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  have hR_ge_2 : Real.rpow Δ (-2 * ε) ≥ 2 := by
    have h4 : X + 1 ≤ Real.rpow Δ (-2 * ε) / 2 := hK_bound
    have h5 : 1 < X + 1 := by linarith
    have h6 : 1 < Real.rpow Δ (-2 * ε) / 2 := by linarith
    linarith
  have hK_real : (K : ℝ) ≤ Real.rpow Δ (-2 * ε) := by
    have h1 : (K : ℝ) = (Nat.ceil X : ℝ) + 1 := by
      simp [K] <;> norm_cast
    rw [h1]
    have h2 : (Nat.ceil X : ℝ) ≤ X + 1 := by
      have h21 : (Nat.ceil X : ℝ) < X + 1 := Nat.ceil_lt_add_one hX_pos.le
      exact h21.le
    have h3 : X + 2 ≤ Real.rpow Δ (-2 * ε) := by
      have h4 : X + 1 ≤ Real.rpow Δ (-2 * ε) / 2 := hK_bound
      linarith [hR_ge_2]
    linarith

  -- 2^X = Δ^{-(4s+2ε)}
  have h2X : (2 : ℝ)^X = Real.rpow Δ (-(4 * s + 3 * ε)) := by
    have h_pos1 : 0 < (2 : ℝ)^X := by positivity
    have h_pos2 : 0 < Real.rpow Δ (-(4 * s + 3 * ε)) := h_rpow_pos (-(4 * s + 3 * ε))
    have h_log1 : Real.log ((2 : ℝ)^X) = (4 * s + 3 * ε) * Real.log (1 / Δ) := by
      have h : Real.log ((2 : ℝ)^X) = X * Real.log 2 := Real.log_rpow (by norm_num) X
      rw [h]
      have hX_def : X = (4 * s + 3 * ε) * Real.log (1 / Δ) / Real.log 2 := by rfl
      rw [hX_def]
      have hlog2_ne_zero : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
      field_simp [hlog2_ne_zero] <;> ring
    have h_log2 : Real.log (Real.rpow Δ (-(4 * s + 3 * ε))) = (4 * s + 3 * ε) * Real.log (1 / Δ) := by
      have h : Real.log (Real.rpow Δ (-(4 * s + 3 * ε))) = (-(4 * s + 3 * ε)) * Real.log Δ := by
        rw [← Real.log_rpow hΔ_pos (-(4 * s + 3 * ε))]
        <;> rfl
      rw [h]
      have hlog : Real.log (1 / Δ) = - Real.log Δ := by
        rw [Real.log_div (by positivity) (by positivity)] <;> simp
      rw [hlog] <;> ring
    have h_eq : Real.log ((2 : ℝ)^X) = Real.log (Real.rpow Δ (-(4 * s + 3 * ε))) := by
      rw [h_log1, h_log2]
    exact Real.log_injOn_pos (Set.mem_Ioi.mpr h_pos1) (Set.mem_Ioi.mpr h_pos2) h_eq
  have hK_ge_X1 : (K : ℝ) ≥ X + 1 := by
    simp [K]
    have h : (Nat.ceil X : ℝ) ≥ X := Nat.le_ceil X
    linarith

  -- For all U ∈ T_Δ, n(U) < 2^K
  have h_n_lt_2K : ∀ U ∈ T_Δ, n U < (2 : ℕ)^K := by
    intro U hU
    have h1 : (n U : ℝ) ≤ (T_full.card : ℝ) := by
      have h11 : n U ≤ T_full.card := Finset.card_le_card (Finset.filter_subset _ _)
      exact_mod_cast h11
    have h2 : (T_full.card : ℝ) ≤ Real.rpow Δ (-(4 * s + 3 * ε)) := hD_upper
    have h3 : Real.rpow Δ (-(4 * s + 3 * ε)) < ((2 : ℕ)^K : ℝ) := by
      have h4 : ((2 : ℕ)^K : ℝ) ≥ (2 : ℝ)^(X + 1) := by
        have h41 : (X + 1 : ℝ) ≤ (K : ℝ) := hK_ge_X1
        have h42 : (1 : ℝ) ≤ (2 : ℝ) := by norm_num
        have h43 : (2 : ℝ)^(X + 1) ≤ (2 : ℝ)^(K : ℝ) := Real.rpow_le_rpow_of_exponent_le h42 h41
        have h44 : ((2 : ℕ)^K : ℝ) = (2 : ℝ)^(K : ℝ) := by norm_cast
        rw [h44]
        exact h43
      have h5 : (2 : ℝ)^(X + 1) = 2 * (2 : ℝ)^X := by
        rw [Real.rpow_add (by norm_num)] <;> ring
      have h6 : ((2 : ℕ)^K : ℝ) ≥ 2 * (2 : ℝ)^X := by
        calc ((2 : ℕ)^K : ℝ)
          ≥ (2 : ℝ)^(X + 1) := h4
        _ = 2 * (2 : ℝ)^X := h5
      have h7 : (2 : ℝ)^X = Real.rpow Δ (-(4 * s + 3 * ε)) := h2X
      rw [h7] at h6
      have hpos : 0 < Real.rpow Δ (-(4 * s + 3 * ε)) := h_rpow_pos (-(4 * s + 3 * ε))
      linarith
    have h9 : (n U : ℝ) < ((2 : ℕ)^K : ℝ) := by linarith
    exact_mod_cast h9

  -- Dyadic layer j: 2^j ≤ n(U) < 2^(j+1)
  let layer (j : ℕ) : Finset CoarseTube :=
    T_Δ.filter (fun U => (2 : ℕ)^j ≤ n U ∧ n U < (2 : ℕ)^(j + 1))

  -- Every U ∈ T_Δ is in some layer j < K
  have h_cover : ∀ U ∈ T_Δ, ∃ j ∈ Finset.range K, U ∈ layer j := by
    intro U hU
    have h1 : n U < (2 : ℕ)^K := h_n_lt_2K U hU
    have h2 : 0 < n U := (Finset.mem_filter.mp hU).2
    have h2' : n U ≠ 0 := by linarith
    have h3 : ∃ j : ℕ, (2 : ℕ)^j ≤ n U ∧ n U < (2 : ℕ)^(j + 1) := by
      let j := Nat.log 2 (n U)
      have h4 : (2 : ℕ)^j ≤ n U := Nat.pow_log_le_self 2 h2'
      have h5 : n U < (2 : ℕ)^(j + 1) := by
        by_contra h6
        have h7 : (2 : ℕ)^(j + 1) ≤ n U := by linarith
        have h8 : j + 1 ≤ Nat.log 2 (n U) := by
          apply Nat.le_log_of_pow_le
          <;> norm_num <;> exact h7
        omega
      exact ⟨j, h4, h5⟩
    rcases h3 with ⟨j, hj1, hj2⟩
    have hjK : j < K := by
      by_contra h
      have h6 : j ≥ K := by linarith
      have h7 : (2 : ℕ)^K ≤ (2 : ℕ)^j := by
        gcongr <;> norm_num
      linarith
    exact ⟨j, Finset.mem_range.mpr hjK, Finset.mem_filter.mpr ⟨hU, ⟨hj1, hj2⟩⟩⟩

  -- Coarse incidence of layer j
  let layerCm (j : ℕ) : ℝ := ∑ U ∈ layer j, (cm U : ℝ)

  -- Disjointness of layers
  have h_disj : ∀ j1 ∈ Finset.range K, ∀ j2 ∈ Finset.range K, j1 ≠ j2 → Disjoint (layer j1) (layer j2) := by
    intro j1 _ j2 _ hne
    simp only [layer, Finset.disjoint_left]
    intro U h1 h2
    have h3 : (2 : ℕ)^j1 ≤ n U := (Finset.mem_filter.mp h1).2.1
    have h4 : n U < (2 : ℕ)^(j1 + 1) := (Finset.mem_filter.mp h1).2.2
    have h5 : (2 : ℕ)^j2 ≤ n U := (Finset.mem_filter.mp h2).2.1
    have h6 : n U < (2 : ℕ)^(j2 + 1) := (Finset.mem_filter.mp h2).2.2
    by_cases h : j1 < j2
    · have h7 : j1 + 1 ≤ j2 := by omega
      have h8 : (2 : ℕ)^(j1 + 1) ≤ (2 : ℕ)^j2 := by gcongr <;> norm_num
      linarith
    · have h9 : j2 < j1 := by omega
      have h10 : j2 + 1 ≤ j1 := by omega
      have h11 : (2 : ℕ)^(j2 + 1) ≤ (2 : ℕ)^j1 := by gcongr <;> norm_num
      linarith
  have h_biUnion : (Finset.range K).biUnion layer = T_Δ := by
    ext U
    simp only [Finset.mem_biUnion]
    constructor
    · rintro ⟨j, hj, hUlayer⟩
      exact (Finset.mem_filter.mp hUlayer).1
    · intro hU
      rcases h_cover U hU with ⟨j, hj, hUlayer⟩
      exact ⟨j, hj, hUlayer⟩

  -- Total incidence over all layers
  have h_sum_layers : ∑ j ∈ Finset.range K, layerCm j = ∑ U ∈ T_Δ, (cm U : ℝ) := by
    dsimp only [layerCm]
    have h : ∑ U ∈ (Finset.range K).biUnion layer, (cm U : ℝ) =
        ∑ j ∈ Finset.range K, ∑ U ∈ layer j, (cm U : ℝ) := Finset.sum_biUnion h_disj
    have h' : ∑ j ∈ Finset.range K, ∑ U ∈ layer j, (cm U : ℝ) =
        ∑ U ∈ (Finset.range K).biUnion layer, (cm U : ℝ) := h.symm
    rw [h', h_biUnion]

  -- Pick layer j with maximum coarse incidence
  have h_exists_max : ∃ j ∈ Finset.range K, ∀ j' ∈ Finset.range K, layerCm j' ≤ layerCm j :=
    Finset.exists_max_image (Finset.range K) layerCm (by simp)
  rcases h_exists_max with ⟨j_max, hj_max, h_j_max_max⟩

  have h_nonempty_range : (Finset.range K).Nonempty := by
    refine' ⟨0, _⟩
    simp [K]
    <;> omega

  have hK_pos' : (0 : ℝ) < (K : ℝ) := by positivity

  have h_avg : layerCm j_max ≥ (∑ j ∈ Finset.range K, layerCm j) / (K : ℝ) := by
    have h1 : ∑ j ∈ Finset.range K, layerCm j ≤ (K : ℝ) * layerCm j_max := by
      calc ∑ j ∈ Finset.range K, layerCm j
        ≤ ∑ j ∈ Finset.range K, layerCm j_max := Finset.sum_le_sum h_j_max_max
      _ = (K : ℝ) * layerCm j_max := by
        simp [Finset.sum_const] <;> ring
    have hK_pos : (0 : ℝ) < (K : ℝ) := hK_pos'
    calc (∑ j ∈ Finset.range K, layerCm j) / (K : ℝ)
      ≤ ((K : ℝ) * layerCm j_max) / (K : ℝ) := by gcongr
    _ = layerCm j_max := by field_simp [hK_pos.ne'] <;> ring

  have hK_pos' : (0 : ℝ) < (K : ℝ) := by positivity
  have h_layer_cm : layerCm j_max ≥ Real.rpow Δ (-s - t + 18 * ε) := by
    have h1 : layerCm j_max ≥ (∑ j ∈ Finset.range K, layerCm j) / (K : ℝ) := h_avg
    have h2 : (∑ j ∈ Finset.range K, layerCm j) ≥ Real.rpow Δ (-s - t + 16 * ε) := by
      rw [h_sum_layers]; exact h_total_cm
    have h3 : (K : ℝ) ≤ Real.rpow Δ (-2 * ε) := hK_real
    have h4 : 1 / (K : ℝ) ≥ Real.rpow Δ (2 * ε) := by
      have h5 : 0 < (K : ℝ) := hK_pos'
      have h6 : (K : ℝ) ≤ Real.rpow Δ (-2 * ε) := h3
      have h7 : 0 < Real.rpow Δ (-2 * ε) := h_rpow_pos (-2 * ε)
      calc 1 / (K : ℝ)
        ≥ 1 / Real.rpow Δ (-2 * ε) := by gcongr
      _ = Real.rpow Δ (2 * ε) := by
        have h8 : Real.rpow Δ (-2 * ε) * Real.rpow Δ (2 * ε) = 1 := by
          rw [h_rpow_mul (-2 * ε) (2 * ε)] <;> ring_nf <;> norm_num
        have h9 : 1 / Real.rpow Δ (-2 * ε) = Real.rpow Δ (2 * ε) := by
          apply (div_eq_iff h7.ne').mpr
          linarith
        exact h9
    have h_posA : 0 < Real.rpow Δ (-s - t + 16 * ε) := h_rpow_pos (-s - t + 16 * ε)
    calc layerCm j_max
      ≥ (∑ j ∈ Finset.range K, layerCm j) / (K : ℝ) := h1
    _ ≥ Real.rpow Δ (-s - t + 16 * ε) / (K : ℝ) := by gcongr
    _ = Real.rpow Δ (-s - t + 16 * ε) * (1 / (K : ℝ)) := by ring
    _ ≥ Real.rpow Δ (-s - t + 16 * ε) * Real.rpow Δ (2 * ε) := by gcongr
    _ = Real.rpow Δ (-s - t + 18 * ε) := by rw [h_rpow_mul (-s - t + 16 * ε) (2 * ε)] <;> ring_nf

  let T_j : Finset CoarseTube := layer j_max
  let N : ℝ := (2 : ℝ)^(j_max + 1)

  -- Good squares: |C_Q_pi ∩ T_j| ≥ Δ^{-s+23ε}
  let Q_good : Finset (CoarseSquare Δ) :=
    a4.Qset.filter (fun Q =>
      ((C' Q).filter (· ∈ T_j)).card ≥ Real.rpow Δ (-s + 23 * ε))

  have h_layer_cm' : layerCm j_max =
      ∑ Q ∈ a4.Qset, (((C' Q).filter (· ∈ T_j)).card : ℝ) := by
    dsimp only [layerCm]
    exact h_double_count T_j

  -- Bad part upper bound
  have hQ_good_sub : Q_good ⊆ a4.Qset := Finset.filter_subset _ _
  have h_bad : ∑ Q ∈ a4.Qset, (((C' Q).filter (· ∈ T_j)).card : ℝ) ≤
      (Q_good.card : ℝ) * Real.rpow Δ (-s - 29 * ε) +
      (a4.Qset.card : ℝ) * Real.rpow Δ (-s + 23 * ε) := by
    have h1 : ∑ Q ∈ a4.Qset, (((C' Q).filter (· ∈ T_j)).card : ℝ) =
        ∑ Q ∈ Q_good, (((C' Q).filter (· ∈ T_j)).card : ℝ) +
        ∑ Q ∈ (a4.Qset \ Q_good), (((C' Q).filter (· ∈ T_j)).card : ℝ) := by
      have h_disj : Disjoint Q_good (a4.Qset \ Q_good) := by
        simp only [Finset.disjoint_left, Finset.mem_sdiff]
        intro x hx1 hx2
        exact hx2.2 hx1
      have h_union : Q_good ∪ (a4.Qset \ Q_good) = a4.Qset := by
        rw [Finset.union_sdiff_of_subset hQ_good_sub]
      rw [← Finset.sum_union h_disj, h_union]
    rw [h1]
    have h_good_sum : ∑ Q ∈ Q_good, (((C' Q).filter (· ∈ T_j)).card : ℝ) ≤
        (Q_good.card : ℝ) * Real.rpow Δ (-s - 29 * ε) := by
      have h2 : ∀ Q ∈ Q_good, (((C' Q).filter (· ∈ T_j)).card : ℝ) ≤
          Real.rpow Δ (-s - 29 * ε) := by
        intro Q hQ
        have hQ_in : Q ∈ a4.Qset := hQ_good_sub hQ
        have h3 : ((C' Q).filter (· ∈ T_j)).card ≤ (C' Q).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
        have h4 : ((C' Q).card : ℝ) ≤ Real.rpow Δ (-s - 29 * ε) := by
          have h5 : (C' Q).card = (C Q hQ_in).card := by
            apply congr_arg Finset.card
            exact hC'_eq Q hQ_in
          rw [h5]
          exact hC_pi_upper Q hQ_in
        have h3' : (((C' Q).filter (· ∈ T_j)).card : ℝ) ≤ ((C' Q).card : ℝ) := by exact_mod_cast h3
        exact le_trans h3' h4
      have h5 : ∑ Q ∈ Q_good, (((C' Q).filter (· ∈ T_j)).card : ℝ) ≤
          ∑ Q ∈ Q_good, Real.rpow Δ (-s - 29 * ε) := Finset.sum_le_sum h2
      have h6 : ∑ Q ∈ Q_good, Real.rpow Δ (-s - 29 * ε) =
          (Q_good.card : ℝ) * Real.rpow Δ (-s - 29 * ε) := by
        simp [Finset.sum_const] <;> ring
      rw [h6] at h5; exact h5
    have h_bad_sum : ∑ Q ∈ (a4.Qset \ Q_good), (((C' Q).filter (· ∈ T_j)).card : ℝ) ≤
        (a4.Qset.card : ℝ) * Real.rpow Δ (-s + 23 * ε) := by
      have h2 : ∀ Q ∈ (a4.Qset \ Q_good), (((C' Q).filter (· ∈ T_j)).card : ℝ) <
          Real.rpow Δ (-s + 23 * ε) := by
        intro Q hQ
        have hQ_in : Q ∈ a4.Qset := (Finset.mem_sdiff.mp hQ).1
        have hQ_not_good : Q ∉ Q_good := (Finset.mem_sdiff.mp hQ).2
        simp only [Q_good, Finset.mem_filter] at hQ_not_good
        have h_not_ge : ¬ (((C' Q).filter (· ∈ T_j)).card ≥ Real.rpow Δ (-s + 23 * ε)) := by
          intro h
          exact hQ_not_good ⟨hQ_in, h⟩
        exact lt_of_not_ge h_not_ge
      have h3 : ∑ Q ∈ (a4.Qset \ Q_good), (((C' Q).filter (· ∈ T_j)).card : ℝ) ≤
          ∑ Q ∈ (a4.Qset \ Q_good), Real.rpow Δ (-s + 23 * ε) := by
        apply Finset.sum_le_sum
        intro Q hQ
        exact (h2 Q hQ).le
      have h4 : ∑ Q ∈ (a4.Qset \ Q_good), Real.rpow Δ (-s + 23 * ε) =
          ((a4.Qset \ Q_good).card : ℝ) * Real.rpow Δ (-s + 23 * ε) := by
        simp [Finset.sum_const] <;> ring
      rw [h4] at h3
      have h5 : (a4.Qset \ Q_good) ⊆ a4.Qset := by
        intro x hx
        exact (Finset.mem_sdiff.mp hx).1
      have h6 : ((a4.Qset \ Q_good).card : ℝ) ≤ (a4.Qset.card : ℝ) := by
        exact_mod_cast Finset.card_le_card h5
      have h7 : 0 ≤ Real.rpow Δ (-s + 23 * ε) := (h_rpow_pos (-s + 23 * ε)).le
      have h8 : ((a4.Qset \ Q_good).card : ℝ) * Real.rpow Δ (-s + 23 * ε) ≤
          (a4.Qset.card : ℝ) * Real.rpow Δ (-s + 23 * ε) := by gcongr
      exact le_trans h3 h8
    linarith

  -- Good squares lower bound
  -- layerCm ≥ Δ^{-s-t+18ε}
  -- bad ≤ Δ^{-t-ε} · Δ^{-s+23ε} = Δ^{-s-t+22ε} = Δ^{4ε} · Δ^{-s-t+18ε} ≤ (1/2)·Δ^{-s-t+18ε}
  -- good ≥ (1/2)·layerCm ≥ (1/2)·Δ^{-s-t+18ε}
  -- good ≤ |Q_good| · Δ^{-s-29ε}
  -- Therefore |Q_good| ≥ (1/2)·Δ^{-t+47ε}
  have hQ_good_lower_47 : (Q_good.card : ℝ) ≥ (1 / 2 : ℝ) * Real.rpow Δ (-t + 47 * ε) := by
    have h1 : layerCm j_max ≥ Real.rpow Δ (-s - t + 18 * ε) := h_layer_cm
    rw [h_layer_cm'] at h1
    have h2 : Real.rpow Δ (-s - t + 18 * ε) ≤
        (Q_good.card : ℝ) * Real.rpow Δ (-s - 29 * ε) +
        (a4.Qset.card : ℝ) * Real.rpow Δ (-s + 23 * ε) :=
      le_trans h1 h_bad
    -- Δ^{4ε} ≤ 1/2
    have hΔ4ε_le_half : Real.rpow Δ (4 * ε) ≤ 1 / 2 := by
      have h1 : Real.rpow Δ (4 * ε) ≤ Real.rpow Δ (3 * ε) := by
        apply Real.rpow_le_rpow_of_exponent_ge hΔ_pos hΔ_le_one <;> linarith
      linarith [hΔ3ε_le_half]
    -- |Qset| * Δ^{-s+23ε} ≤ (1/2) * Δ^{-s-t+18ε}
    have h3 : (a4.Qset.card : ℝ) * Real.rpow Δ (-s + 23 * ε) ≤
        (1 / 2 : ℝ) * Real.rpow Δ (-s - t + 18 * ε) := by
      have h4 : (a4.Qset.card : ℝ) ≤ Real.rpow Δ (-t - ε) := hQset_size_upper
      have h5 : Real.rpow Δ (-t - ε) * Real.rpow Δ (-s + 23 * ε) =
          Real.rpow Δ (-s - t + 22 * ε) := by
        rw [h_rpow_mul (-t - ε) (-s + 23 * ε)] <;> ring_nf
      have h6 : Real.rpow Δ (-s - t + 22 * ε) =
          Real.rpow Δ (4 * ε) * Real.rpow Δ (-s - t + 18 * ε) := by
        have h_exp : (-s - t + 22 * ε) = (4 * ε) + (-s - t + 18 * ε) := by ring
        rw [h_exp, h_rpow_mul (4 * ε) (-s - t + 18 * ε)]
      have h7 : 0 ≤ Real.rpow Δ (-s - t + 18 * ε) := (h_rpow_pos (-s - t + 18 * ε)).le
      calc (a4.Qset.card : ℝ) * Real.rpow Δ (-s + 23 * ε)
        ≤ Real.rpow Δ (-t - ε) * Real.rpow Δ (-s + 23 * ε) := by gcongr <;> exact (h_rpow_pos (-s + 23 * ε)).le
      _ = Real.rpow Δ (-s - t + 22 * ε) := h5
      _ = Real.rpow Δ (4 * ε) * Real.rpow Δ (-s - t + 18 * ε) := h6
      _ ≤ (1 / 2 : ℝ) * Real.rpow Δ (-s - t + 18 * ε) := by
        exact mul_le_mul_of_nonneg_right hΔ4ε_le_half h7
    have h7 : (1 / 2 : ℝ) * Real.rpow Δ (-s - t + 18 * ε) ≤
        (Q_good.card : ℝ) * Real.rpow Δ (-s - 29 * ε) := by linarith
    have h8 : Real.rpow Δ (-s - t + 18 * ε) ≤
        2 * (Q_good.card : ℝ) * Real.rpow Δ (-s - 29 * ε) := by linarith
    have h9 : Real.rpow Δ (-s - t + 18 * ε) =
        Real.rpow Δ (-s - 29 * ε) * Real.rpow Δ (-t + 47 * ε) := by
      have h_exp : (-s - t + 18 * ε) = (-s - 29 * ε) + (-t + 47 * ε) := by ring
      rw [h_exp, h_rpow_mul (-s - 29 * ε) (-t + 47 * ε)]
    rw [h9] at h8
    have h10 : 0 < Real.rpow Δ (-s - 29 * ε) := h_rpow_pos (-s - 29 * ε)
    have h11 : Real.rpow Δ (-t + 47 * ε) ≤ 2 * (Q_good.card : ℝ) := by
      have h_comm : 2 * (Q_good.card : ℝ) * Real.rpow Δ (-s - 29 * ε) =
          Real.rpow Δ (-s - 29 * ε) * (2 * (Q_good.card : ℝ)) := by ring
      rw [h_comm] at h8
      nlinarith [h10]
    linarith

  -- Derive 49ε lower bound: Δ^{-t+49ε} = Δ^{2ε}·Δ^{-t+47ε} ≤ (1/2)·Δ^{-t+47ε} ≤ |Q_good|
  have hQ_good_lower_49 : (Q_good.card : ℝ) ≥ Real.rpow Δ (-t + 49 * ε) := by
    have h13 : Real.rpow Δ (-t + 49 * ε) ≤ (1 / 2 : ℝ) * Real.rpow Δ (-t + 47 * ε) := by
      have h14 : Real.rpow Δ (-t + 49 * ε) =
          Real.rpow Δ (2 * ε) * Real.rpow Δ (-t + 47 * ε) := by
        have h_exp : (-t + 49 * ε) = (2 * ε) + (-t + 47 * ε) := by ring
        rw [h_exp, h_rpow_mul (2 * ε) (-t + 47 * ε)]
      rw [h14]
      have h15 : 0 ≤ Real.rpow Δ (-t + 47 * ε) := (h_rpow_pos (-t + 47 * ε)).le
      exact mul_le_mul_of_nonneg_right hΔ2ε_le_half h15
    exact le_trans h13 hQ_good_lower_47

  -- Derive 50ε lower bound: Δ^{-t+50ε} ≤ Δ^{-t+49ε} (since Δ<1)
  have hQ_good_lower_50 : (Q_good.card : ℝ) ≥ Real.rpow Δ (-t + 50 * ε) := by
    have h16 : Real.rpow Δ (-t + 50 * ε) ≤ Real.rpow Δ (-t + 49 * ε) := by
      apply Real.rpow_le_rpow_of_exponent_ge hΔ_pos hΔ_le_one <;> linarith
    exact le_trans h16 hQ_good_lower_49

  -- Apply 2s-bound directly with D_good
  rcases h_2s_bound with ⟨c, hc_pos, hc_ge, hc_abs, h_bound⟩
  let D_good : (Q : CoarseSquare Δ) → Q ∈ Q_good → Finset CoarseTube :=
    fun Q hQ =>
      let hQ_in : Q ∈ a4.Qset := (Finset.mem_filter.mp hQ).1
      (C Q hQ_in).filter (· ∈ T_j)
  have hD_sub : ∀ Q hQ, D_good Q hQ ⊆ C Q ((Finset.mem_filter.mp hQ).1) := by
    intro Q hQ
    dsimp only [D_good]
    exact Finset.filter_subset _ _
  have hD1 : ∀ Q hQ, (D_good Q hQ).card ≥ Real.rpow Δ (-s + 23 * ε) := by
    intro Q hQ
    have hQ_in : Q ∈ a4.Qset := (Finset.mem_filter.mp hQ).1
    have h_eq : D_good Q hQ = (C' Q).filter (· ∈ T_j) := by
      dsimp only [D_good]
      apply congr_arg (fun X : Finset CoarseTube => X.filter (· ∈ T_j))
      simp [C', C, hQ_in]
    rw [h_eq]
    exact (Finset.mem_filter.mp hQ).2
  have hQ_good_sub' : Q_good ⊆ a4.Qset := hQ_good_sub
  -- D_good Q hQ ⊆ T_j for all Q, hQ
  have hD_sub_Tj : ∀ Q hQ, D_good Q hQ ⊆ T_j := by
    intro Q hQ
    dsimp only [D_good]
    intro x hx
    exact (Finset.mem_filter.mp hx).2
  -- Therefore filtering over C_global_A2 or T_j gives the same result
  have h_filter_eq : C_global_A2.filter (fun T => ∃ Q hQ, T ∈ D_good Q hQ) =
      T_j.filter (fun T => ∃ Q hQ, T ∈ D_good Q hQ) := by
    ext T
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hT, ⟨Q, hQ, hTD⟩⟩
      have h_in_Tj : T ∈ T_j := hD_sub_Tj Q hQ hTD
      exact ⟨h_in_Tj, ⟨Q, hQ, hTD⟩⟩
    · rintro ⟨hT, h⟩
      have hT_in_Cglobal : T ∈ C_global_A2 := hTΔ_sub ((Finset.mem_filter.mp hT).1)
      exact ⟨hT_in_Cglobal, h⟩
  have hT_j_size : (C_global_A2.filter (fun T => ∃ Q hQ, T ∈ D_good Q hQ)).card ≥
      c * Real.rpow Δ (-2 * s + 210 * ε) := by
    rcases h_bound Q_good hQ_good_sub' D_good hD_sub hQ_good_lower_49 hD1 with ⟨S, hS_mem, hS_card⟩
    have hS_eq : S = C_global_A2.filter (fun T => ∃ Q hQ, T ∈ D_good Q hQ) := by
      ext T
      simp only [hS_mem, Finset.mem_filter]
      <;> tauto
    rw [hS_eq] at hS_card
    exact hS_card
  rw [h_filter_eq] at hT_j_size
  have h_filter_sub : T_j.filter (fun T => ∃ Q hQ, T ∈ D_good Q hQ) ⊆ T_j :=
    Finset.filter_subset _ _
  have hT_j_lower : (T_j.card : ℝ) ≥ c * Real.rpow Δ (-2 * s + 210 * ε) := by
    have h1 : (T_j.filter (fun T => ∃ Q hQ, T ∈ D_good Q hQ)).card ≤ T_j.card :=
      Finset.card_le_card h_filter_sub
    have h1' : ((T_j.filter (fun T => ∃ Q hQ, T ∈ D_good Q hQ)).card : ℝ) ≤ (T_j.card : ℝ) := by
      exact_mod_cast h1
    exact le_trans hT_j_size h1'
  have hc_ge' : c ≥ Real.rpow Δ ε := hc_ge
  have hc_abs' : (2 : ℝ) / c ≤ Real.rpow Δ (-ε) := hc_abs
  have h_c_lower : c ≥ 2 * Real.rpow Δ ε := by
    have h1 : (2 : ℝ) / c ≤ Real.rpow Δ (-ε) := hc_abs'
    have h2 : 0 < c := hc_pos
    have h3 : 0 < Real.rpow Δ ε := h_rpow_pos ε
    have h4 : 2 ≤ c * Real.rpow Δ (-ε) := by
      calc (2 : ℝ)
        = c * ((2 : ℝ) / c) := by field_simp [h2.ne'] <;> ring
      _ ≤ c * Real.rpow Δ (-ε) := by gcongr
    have h5 : Real.rpow Δ (-ε) * Real.rpow Δ ε = 1 := by
      rw [h_rpow_mul (-ε) ε] <;> ring_nf <;> norm_num
    have h6 : c = c * (Real.rpow Δ (-ε) * Real.rpow Δ ε) := by rw [h5] <;> ring
    rw [h6]
    have h7 : c * (Real.rpow Δ (-ε) * Real.rpow Δ ε) =
        (c * Real.rpow Δ (-ε)) * Real.rpow Δ ε := by ring
    rw [h7]
    exact mul_le_mul_of_nonneg_right h4 (h_rpow_pos ε).le
  have hT_j_lower2 : (T_j.card : ℝ) ≥ 2 * Real.rpow Δ (-2 * s + 211 * ε) := by
    have h1 : c * Real.rpow Δ (-2 * s + 210 * ε) ≥
        2 * Real.rpow Δ ε * Real.rpow Δ (-2 * s + 210 * ε) := by
      have h_pos : 0 ≤ Real.rpow Δ (-2 * s + 210 * ε) := (h_rpow_pos (-2 * s + 210 * ε)).le
      have h : c * Real.rpow Δ (-2 * s + 210 * ε) ≥
          (2 * Real.rpow Δ ε) * Real.rpow Δ (-2 * s + 210 * ε) :=
        mul_le_mul_of_nonneg_right h_c_lower h_pos
      have h_comm : (2 * Real.rpow Δ ε) * Real.rpow Δ (-2 * s + 210 * ε) =
          2 * Real.rpow Δ ε * Real.rpow Δ (-2 * s + 210 * ε) := by ring
      rw [h_comm] at h
      exact h
    have h2 : 2 * Real.rpow Δ ε * Real.rpow Δ (-2 * s + 210 * ε) =
        2 * Real.rpow Δ (-2 * s + 211 * ε) := by
      have h_prod : Real.rpow Δ ε * Real.rpow Δ (-2 * s + 210 * ε) = Real.rpow Δ (-2 * s + 211 * ε) := by
        rw [h_rpow_mul ε (-2 * s + 210 * ε)] <;> ring_nf
      calc 2 * Real.rpow Δ ε * Real.rpow Δ (-2 * s + 210 * ε)
        = 2 * (Real.rpow Δ ε * Real.rpow Δ (-2 * s + 210 * ε)) := by ring
      _ = 2 * Real.rpow Δ (-2 * s + 211 * ε) := by rw [h_prod]
    rw [h2] at h1
    exact le_trans h1 hT_j_lower

  have hTj_sub_TΔ : T_j ⊆ T_Δ := Finset.filter_subset _ _

  -- N upper bound from partition
  have h_sum_fibers : ∑ U ∈ T_j, (n U : ℝ) ≤ (T_full.card : ℝ) := by
    have h1 : ∀ U ∈ T_j, globalFiber Δ hΔ_pos T_full U ⊆ T_full := by
      intro U _
      exact Finset.filter_subset _ _
    have h2 : ∑ U ∈ T_j, (n U : ℝ) = ∑ U ∈ T_j, ((globalFiber Δ hΔ_pos T_full U).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro U _
      rfl
    rw [h2]
    -- Fibers are disjoint because T_j has distinct parent cells
    have h4 : Set.Pairwise (T_j : Set CoarseTube) (fun U1 U2 =>
        Disjoint (globalFiber Δ hΔ_pos T_full U1) (globalFiber Δ hΔ_pos T_full U2)) := by
      intro U1 hU1 U2 hU2 hne
      have h5 : parentCell Δ hΔ_pos U1 ≠ parentCell Δ hΔ_pos U2 :=
        hTΔ_distinct U1 (hTj_sub_TΔ hU1) U2 (hTj_sub_TΔ hU2) hne
      simp only [Finset.disjoint_left, globalFiber, Finset.mem_filter]
      intro T hT1 hT2
      have h6 : InParent Δ hΔ_pos T U1 := hT1.2
      have h7 : InParent Δ hΔ_pos T U2 := hT2.2
      have h8 : parentCell Δ hΔ_pos T = parentCell Δ hΔ_pos U1 := h6
      have h9 : parentCell Δ hΔ_pos T = parentCell Δ hΔ_pos U2 := h7
      have h10 : parentCell Δ hΔ_pos U1 = parentCell Δ hΔ_pos U2 := by
        rw [←h8, h9]
      exact h5 h10
    have h_biUnion_card : (T_j.biUnion (fun U => globalFiber Δ hΔ_pos T_full U)).card =
        ∑ U ∈ T_j, (globalFiber Δ hΔ_pos T_full U).card := by
      rw [Finset.card_biUnion h4]
      <;> rfl
    have h_biUnion_sub : T_j.biUnion (fun U => globalFiber Δ hΔ_pos T_full U) ⊆ T_full := by
      intro T hT
      rcases Finset.mem_biUnion.mp hT with ⟨U, _, hT⟩
      exact (Finset.mem_filter.mp hT).1
    have h5 : (∑ U ∈ T_j, (globalFiber Δ hΔ_pos T_full U).card) ≤ T_full.card := by
      rw [←h_biUnion_card]
      exact Finset.card_le_card h_biUnion_sub
    exact_mod_cast h5

  have h_n_lower : ∀ U ∈ T_j, (n U : ℝ) ≥ N / 2 := by
    intro U hU
    have h1 : (2 : ℕ)^j_max ≤ n U := (Finset.mem_filter.mp hU).2.1
    have h2 : N / 2 = ((2 : ℕ)^j_max : ℝ) := by
      simp [N] <;> ring
    rw [h2]
    exact_mod_cast h1

  have h_sum_lower : ∑ U ∈ T_j, (n U : ℝ) ≥ (T_j.card : ℝ) * (N / 2) := by
    have h1 : ∑ U ∈ T_j, (n U : ℝ) ≥ ∑ U ∈ T_j, (N / 2) := Finset.sum_le_sum h_n_lower
    have h2 : ∑ U ∈ T_j, (N / 2) = (T_j.card : ℝ) * (N / 2) := by
      simp [Finset.sum_const] <;> ring
    rw [h2] at h1
    exact h1

  have h_div : ∀ (a b : ℝ), Real.rpow Δ a / Real.rpow Δ b = Real.rpow Δ (a - b) := by
    intro a b
    have h_pos : 0 < Real.rpow Δ b := h_rpow_pos b
    have h9 : Real.rpow Δ a = Real.rpow Δ (a - b) * Real.rpow Δ b := by
      have h10 : (a - b) + b = a := by ring
      have h11 : Real.rpow Δ (a - b) * Real.rpow Δ b = Real.rpow Δ ((a - b) + b) := h_rpow_mul (a - b) b
      rw [h11, h10]
    rw [h9]
    have h12 : (Real.rpow Δ (a - b) * Real.rpow Δ b) / Real.rpow Δ b = Real.rpow Δ (a - b) := by
      have h13 : Real.rpow Δ b / Real.rpow Δ b = 1 := by
        field_simp [h_pos.ne']
      have h14 : (Real.rpow Δ (a - b) * Real.rpow Δ b) / Real.rpow Δ b =
          Real.rpow Δ (a - b) * (Real.rpow Δ b / Real.rpow Δ b) := by ring
      rw [h14, h13] <;> ring
    exact h12
  have h_div_right_lemma : ∀ {a b d : ℝ}, 0 < d → a ≤ b → a / d ≤ b / d := by
    intro a b d hd h
    have h' : a * d⁻¹ ≤ b * d⁻¹ := mul_le_mul_of_nonneg_right h (by positivity)
    simpa [div_eq_mul_inv] using h'
  have hN_upper_internal : N ≤ Real.rpow Δ (-2 * s - 214 * ε) := by
    set A : ℝ := Real.rpow Δ (-(4 * s + 3 * ε)) with hA_def
    set B : ℝ := 2 * Real.rpow Δ (-2 * s + 211 * ε) with hB_def
    have h1 : (T_j.card : ℝ) * (N / 2) ≤ (T_full.card : ℝ) :=
      le_trans h_sum_lower h_sum_fibers
    have h2 : (T_j.card : ℝ) ≥ B := hT_j_lower2
    have h3 : (T_full.card : ℝ) ≤ A := hD_upper
    have hB_pos : 0 < B := by
      have h6 : 0 < Real.rpow Δ (-2 * s + 211 * ε) := h_rpow_pos (-2 * s + 211 * ε)
      dsimp only [B]
      linarith
    have h4 : 0 < (T_j.card : ℝ) := by
      have h5 : (T_j.card : ℝ) ≥ B := h2
      have h6 : 0 < Real.rpow Δ (-2 * s + 211 * ε) := h_rpow_pos (-2 * s + 211 * ε)
      linarith
    have hA_nonneg : 0 ≤ A := (h_rpow_pos (-(4 * s + 3 * ε))).le
    have hTfull_nonneg : 0 ≤ (T_full.card : ℝ) := by positivity
    have h5 : N ≤ 2 * (T_full.card : ℝ) / (T_j.card : ℝ) := by
      have h_eq : N = 2 * ((T_j.card : ℝ) * (N / 2)) / (T_j.card : ℝ) := by
        field_simp [h4.ne'] <;> ring
      rw [h_eq]
      have h_ineq : (T_j.card : ℝ) * (N / 2) ≤ (T_full.card : ℝ) := h1
      have h : 2 * ((T_j.card : ℝ) * (N / 2)) ≤ 2 * (T_full.card : ℝ) := by
        exact mul_le_mul_of_nonneg_left h_ineq (by norm_num)
      exact h_div_right_lemma h4 h
    have h_div2 : (T_full.card : ℝ) / (T_j.card : ℝ) ≤ A / B := by
      have h_step1 : (T_full.card : ℝ) / (T_j.card : ℝ) ≤ (T_full.card : ℝ) / B := by
        have h_inv : 1 / (T_j.card : ℝ) ≤ 1 / B := by
          apply one_div_le_one_div_of_le <;> linarith
        calc (T_full.card : ℝ) / (T_j.card : ℝ)
          = (T_full.card : ℝ) * (1 / (T_j.card : ℝ)) := by ring
        _ ≤ (T_full.card : ℝ) * (1 / B) := by gcongr
        _ = (T_full.card : ℝ) / B := by ring
      have h_step2 : (T_full.card : ℝ) / B ≤ A / B := h_div_right_lemma hB_pos h3
      exact le_trans h_step1 h_step2
    have h6 : 2 * (T_full.card : ℝ) / (T_j.card : ℝ) ≤ 2 * (A / B) := by
      have h : 2 * (T_full.card : ℝ) / (T_j.card : ℝ) = 2 * ((T_full.card : ℝ) / (T_j.card : ℝ)) := by ring
      rw [h]
      have h' : 2 * ((T_full.card : ℝ) / (T_j.card : ℝ)) ≤ 2 * (A / B) := by
        exact mul_le_mul_of_nonneg_left h_div2 (by norm_num)
      exact h'
    have h7 : 2 * (A / B) = Real.rpow Δ (-2 * s - 214 * ε) := by
      have h_ring : 2 * (A / B) = (2 * A) / B := by ring
      rw [h_ring]
      simp only [hA_def, hB_def]
      have h_cancel : (2 * Real.rpow Δ (-(4 * s + 3 * ε))) / (2 * Real.rpow Δ (-2 * s + 211 * ε)) =
          Real.rpow Δ (-(4 * s + 3 * ε)) / Real.rpow Δ (-2 * s + 211 * ε) := by
        field_simp [(h_rpow_pos (-2 * s + 211 * ε)).ne'] <;> ring
      rw [h_cancel]
      have h8 := h_div (-(4 * s + 3 * ε)) (-2 * s + 211 * ε)
      rw [h8]
      have h9 : (-(4 * s + 3 * ε)) - (-2 * s + 211 * ε) = -2 * s - 214 * ε := by ring
      rw [h9]
    have h10 : 2 * (T_full.card : ℝ) / (T_j.card : ℝ) ≤ Real.rpow Δ (-2 * s - 214 * ε) := by
      calc 2 * (T_full.card : ℝ) / (T_j.card : ℝ)
        ≤ 2 * (A / B) := h6
      _ = Real.rpow Δ (-2 * s - 214 * ε) := h7
    exact le_trans h5 h10
  have hN_upper : N ≤ Real.rpow Δ (-2 * s - 214 * ε) := hN_upper_internal

  have hN_pos : 0 < N := by
    simp [N] <;> positivity

  -- G4 upper: n(U) ≤ N for U ∈ T_j
  have hG4_upper : ∀ boldT ∈ T_j, ((globalFiber Δ hΔ_pos T_full boldT).card : ℝ) ≤ N := by
    intro boldT hT
    have h1 : n boldT < (2 : ℕ)^(j_max + 1) := (Finset.mem_filter.mp hT).2.2
    have h2 : N = ((2 : ℕ)^(j_max + 1) : ℝ) := by simp [N] <;> norm_cast
    rw [h2]
    exact_mod_cast h1.le

  -- Define T_global = T_full restricted to parents in T_j
  let parentCells : Finset (DyadicTubeCell Δ) :=
    T_j.image (parentCell Δ hΔ_pos)
  let T_global : Finset FineTube :=
    T_full.filter (fun T => parentCell Δ hΔ_pos T ∈ parentCells)

  -- globalFiber(T_global, U) = globalFiber(T_full, U) for U ∈ T_j
  have h_fiber_eq : ∀ U ∈ T_j,
      globalFiber Δ hΔ_pos T_global U = globalFiber Δ hΔ_pos T_full U := by
    intro U hU
    ext T
    have h1 : T ∈ globalFiber Δ hΔ_pos T_global U ↔
        T ∈ T_global ∧ InParent Δ hΔ_pos T U := by
      unfold globalFiber
      exact Finset.mem_filter
    have h2 : T ∈ globalFiber Δ hΔ_pos T_full U ↔
        T ∈ T_full ∧ InParent Δ hΔ_pos T U := by
      unfold globalFiber
      exact Finset.mem_filter
    rw [h1, h2]
    constructor
    · rintro ⟨hT_in_global, h_inparent⟩
      have hT_full : T ∈ T_full := (Finset.mem_filter.mp hT_in_global).1
      exact ⟨hT_full, h_inparent⟩
    · rintro ⟨hT_full, h_inparent⟩
      have h_cell : parentCell Δ hΔ_pos T = parentCell Δ hΔ_pos U := h_inparent
      have h_in_parentCells : parentCell Δ hΔ_pos T ∈ parentCells := by
        rw [h_cell]
        exact Finset.mem_image.mpr ⟨U, hU, rfl⟩
      have hT_in_Tglobal : T ∈ T_global := by
        dsimp only [T_global]
        rw [Finset.mem_filter] <;> exact ⟨hT_full, h_in_parentCells⟩
      exact ⟨hT_in_Tglobal, h_inparent⟩

  -- h_partition
  have h_partition : ∑ U ∈ T_j, (globalFiber Δ hΔ_pos T_global U).card = T_global.card := by
    have h1 : ∀ U ∈ T_j, globalFiber Δ hΔ_pos T_global U =
        T_global.filter (fun T => InParent Δ hΔ_pos T U) := by
      intro U _; rfl
    have h2 : Set.Pairwise (T_j : Set CoarseTube) (fun U1 U2 =>
        Disjoint (globalFiber Δ hΔ_pos T_global U1) (globalFiber Δ hΔ_pos T_global U2)) := by
      intro U1 hU1 U2 hU2 hne
      have h5 : parentCell Δ hΔ_pos U1 ≠ parentCell Δ hΔ_pos U2 :=
        hTΔ_distinct U1 (hTj_sub_TΔ hU1) U2 (hTj_sub_TΔ hU2) hne
      simp only [Finset.disjoint_left, globalFiber, Finset.mem_filter]
      intro T hT1 hT2
      have h6 : InParent Δ hΔ_pos T U1 := hT1.2
      have h7 : InParent Δ hΔ_pos T U2 := hT2.2
      have h8 : parentCell Δ hΔ_pos U1 = parentCell Δ hΔ_pos U2 := by
        dsimp only [InParent] at h6 h7
        rw [←h6, h7]
      exact h5 h8
    have h3 : (∑ U ∈ T_j, (globalFiber Δ hΔ_pos T_global U).card : ℕ) =
        (T_j.biUnion (fun U => globalFiber Δ hΔ_pos T_global U)).card := by
      rw [Finset.card_biUnion h2]
      <;> rfl
    have h4 : T_j.biUnion (fun U => globalFiber Δ hΔ_pos T_global U) = T_global := by
      ext T
      simp only [Finset.mem_biUnion]
      constructor
      · rintro ⟨U, hU, hT⟩
        have h6 : T ∈ T_global.filter (fun T => InParent Δ hΔ_pos T U) := hT
        exact (Finset.mem_filter.mp h6).1
      · intro hT
        have hT' : T ∈ T_full.filter (fun T => parentCell Δ hΔ_pos T ∈ parentCells) := hT
        have h_cell_in : parentCell Δ hΔ_pos T ∈ parentCells := (Finset.mem_filter.mp hT').2
        rcases Finset.mem_image.mp h_cell_in with ⟨U, hU, h_eq⟩
        have h6 : InParent Δ hΔ_pos T U := by
          dsimp only [InParent]
          exact h_eq.symm
        have h7 : T ∈ globalFiber Δ hΔ_pos T_global U := by
          dsimp only [globalFiber]
          exact Finset.mem_filter.mpr ⟨hT, h6⟩
        exact ⟨U, hU, h7⟩
    rw [h3, h4]

  -- h_parent_unique
  have h_parent_unique : ∀ T ∈ T_global,
      ∃! (U : CoarseTube), U ∈ T_j ∧ InParent Δ hΔ_pos T U := by
    intro T hT
    have hT' : T ∈ T_full.filter (fun T => parentCell Δ hΔ_pos T ∈ parentCells) := hT
    have h_cell_in : parentCell Δ hΔ_pos T ∈ parentCells := (Finset.mem_filter.mp hT').2
    rcases Finset.mem_image.mp h_cell_in with ⟨U, hU, hcell⟩
    have h_inparent : InParent Δ hΔ_pos T U := by
      dsimp only [InParent]
      exact hcell.symm
    refine' ⟨U, ⟨hU, h_inparent⟩, _⟩
    intro U' hU'
    have h_inparent' : InParent Δ hΔ_pos T U' := hU'.2
    have h_cell_eq : parentCell Δ hΔ_pos U = parentCell Δ hΔ_pos U' := by
      dsimp only [InParent] at h_inparent h_inparent'
      rw [←h_inparent, h_inparent']
    have h_eq : U = U' := by
      by_contra hne
      exact hTΔ_distinct U (hTj_sub_TΔ hU) U' (hTj_sub_TΔ hU'.1) hne h_cell_eq
    exact h_eq.symm

  -- G3 for Q_good
  have hG3 : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ Q_good),
      Real.rpow Δ (-s + 23 * ε) ≤ (((C' Q) ∩ T_j).card : ℝ) := by
    intro Q hQ
    have h_pred : ((C' Q).filter (· ∈ T_j)).card ≥ Real.rpow Δ (-s + 23 * ε) :=
      (Finset.mem_filter.mp hQ).2
    have h_eq : (C' Q).filter (· ∈ T_j) = (C' Q) ∩ T_j := by
      ext T
      simp [Finset.mem_filter, Finset.mem_inter]
      <;> tauto
    rw [h_eq] at h_pred
    exact h_pred

  -- Card ratio: |Qset| ≤ Δ^{-50ε} * |Q_good|
  have h_card_ratio : (a4.Qset.card : ℝ) ≤ Real.rpow Δ (-50 * ε) * (Q_good.card : ℝ) := by
    have h6 : (Q_good.card : ℝ) ≥ Real.rpow Δ (-t + 49 * ε) := hQ_good_lower_49
    have h7 : (a4.Qset.card : ℝ) ≤ Real.rpow Δ (-t - ε) := hQset_size_upper
    have h8 : Real.rpow Δ (-t - ε) ≤ Real.rpow Δ (-50 * ε) * Real.rpow Δ (-t + 49 * ε) := by
      have h9 : Real.rpow Δ (-50 * ε) * Real.rpow Δ (-t + 49 * ε) = Real.rpow Δ (-t - ε) := by
        rw [h_rpow_mul (-50 * ε) (-t + 49 * ε)] <;> ring_nf
      rw [h9] <;> exact le_refl _
    calc (a4.Qset.card : ℝ)
      ≤ Real.rpow Δ (-t - ε) := h7
    _ ≤ Real.rpow Δ (-50 * ε) * Real.rpow Δ (-t + 49 * ε) := h8
    _ ≤ Real.rpow Δ (-50 * ε) * (Q_good.card : ℝ) := by
      apply mul_le_mul_of_nonneg_left h6
      exact (h_rpow_pos (-50 * ε)).le

  -- Qbar S-set transfer (reuse old proof pattern)
  have hQbar_sset : IsDeltaSSet Δ t (Real.rpow Δ (-75 * ε)) (Q_good : Set (CoarseSquare Δ)) := by
    have h_int_dist : ∀ (a b : ℤ), a ≠ b → (1 : ℝ) ≤ dist a b := by
      intro a b hdiff
      have hne : a - b ≠ 0 := by omega
      have h2 : 1 ≤ |a - b| := by
        have h3 : 0 < |a - b| := abs_pos.mpr hne
        omega
      have h3 : (dist a b : ℝ) = ↑(|a - b|) := by simp [Int.dist_eq] <;> rfl
      rw [h3]; exact_mod_cast h2
    have h_dist : ∀ (x y : CoarseSquare Δ), x ≠ y → (1 : ℝ) ≤ dist x y := by
      intro x y hxy
      rw [Prod.dist_eq]
      by_cases h : x.1 ≠ y.1
      · exact le_max_of_le_left (h_int_dist x.1 y.1 h)
      · have h3 : x.2 ≠ y.2 := by intro h4; apply hxy; ext <;> tauto
        exact le_max_of_le_right (h_int_dist x.2 y.2 h3)
    have h_eps_lt_one : (2 * Δ.toNNReal : ENNReal) < 1 := by
      have h51 : (Δ.toNNReal : ℝ) = Δ := by
        rw [Real.toNNReal_of_nonneg (by linarith)] <;> rfl
      have h52 : (2 * Δ.toNNReal : ℝ) < 1 := by
        rw [show (2 * Δ.toNNReal : ℝ) = 2 * Δ by rw [h51] <;> ring] <;> linarith
      exact_mod_cast h52
    have h_sep : Metric.IsSeparated (2 * Δ.toNNReal) (Q_good : Set (CoarseSquare Δ)) := by
      intro x _ y _ hxy
      have h6 : (1 : ENNReal) ≤ edist x y := by
        have h61 : (1 : ℝ) ≤ dist x y := h_dist x y hxy
        have h62 : edist x y = ENNReal.ofReal (dist x y) := by exact edist_dist x y
        rw [h62]
        have h63 : (1 : ENNReal) = ENNReal.ofReal (1 : ℝ) := by simp
        rw [h63]
        exact ENNReal.ofReal_le_ofReal h61
      exact h_eps_lt_one.trans_le h6
    have h_pack : (Q_good : Set (CoarseSquare Δ)).encard ≤ Metric.packingNumber (2 * Δ.toNNReal) (Q_good : Set (CoarseSquare Δ)) :=
      Metric.IsSeparated.encard_le_packingNumber (Set.Subset.refl _) h_sep
    have h_cover : Metric.packingNumber (2 * Δ.toNNReal) (Q_good : Set (CoarseSquare Δ)) ≤
        Metric.externalCoveringNumber Δ.toNNReal (Q_good : Set (CoarseSquare Δ)) :=
      Metric.packingNumber_two_mul_le_externalCoveringNumber Δ.toNNReal _
    have h_qbar_cover : (Q_good.card : ENNReal) ≤ (Metric.externalCoveringNumber Δ.toNNReal (Q_good : Set (CoarseSquare Δ)) : ENNReal) := by
      have h : (Q_good : Set (CoarseSquare Δ)).encard ≤ Metric.externalCoveringNumber Δ.toNNReal (Q_good : Set (CoarseSquare Δ)) := by
        calc
          (Q_good : Set (CoarseSquare Δ)).encard
            ≤ Metric.packingNumber (2 * Δ.toNNReal) (Q_good : Set (CoarseSquare Δ)) := h_pack
          _ ≤ Metric.externalCoveringNumber Δ.toNNReal (Q_good : Set (CoarseSquare Δ)) := h_cover
      have h' : (Q_good.card : ENNReal) = ((Q_good : Set (CoarseSquare Δ)).encard : ENNReal) := by simp
      rw [h']
      exact_mod_cast h
    have h_ratio : (Metric.externalCoveringNumber Δ.toNNReal (a4.Qset : Set (CoarseSquare Δ)) : ENNReal) ≤
        ENNReal.ofReal (Real.rpow Δ (-50 * ε)) *
        Metric.externalCoveringNumber Δ.toNNReal (Q_good : Set (CoarseSquare Δ)) := by
      have h1 : (Metric.externalCoveringNumber Δ.toNNReal (a4.Qset : Set (CoarseSquare Δ)) : ENNReal) ≤
          (a4.Qset.card : ENNReal) := by
        have h11 : Metric.externalCoveringNumber Δ.toNNReal (a4.Qset : Set (CoarseSquare Δ)) ≤
            (a4.Qset : Set (CoarseSquare Δ)).encard := Metric.externalCoveringNumber_le_encard_self _
        have h12 : (a4.Qset : Set (CoarseSquare Δ)).encard = (a4.Qset.card : ENNReal) := by simp
        exact_mod_cast h11
      have h_pos1 : 0 ≤ Real.rpow Δ (-50 * ε) := (h_rpow_pos (-50 * ε)).le
      have h2 : (a4.Qset.card : ENNReal) ≤
          ENNReal.ofReal (Real.rpow Δ (-50 * ε)) * (Q_good.card : ENNReal) := by
        have h21 : (a4.Qset.card : ℝ) ≤ Real.rpow Δ (-50 * ε) * (Q_good.card : ℝ) := h_card_ratio
        have h22 : ENNReal.ofReal (a4.Qset.card : ℝ) ≤
            ENNReal.ofReal (Real.rpow Δ (-50 * ε) * (Q_good.card : ℝ)) := by
          apply ENNReal.ofReal_le_ofReal; exact h21
        have h23 : ENNReal.ofReal (Real.rpow Δ (-50 * ε) * (Q_good.card : ℝ)) =
            ENNReal.ofReal (Real.rpow Δ (-50 * ε)) * (Q_good.card : ENNReal) := by
          rw [ENNReal.ofReal_mul h_pos1] <;> simp
        have h24 : (a4.Qset.card : ENNReal) = ENNReal.ofReal (a4.Qset.card : ℝ) := by simp
        rw [h24]
        exact h22.trans (by rw [h23])
      calc
        (Metric.externalCoveringNumber Δ.toNNReal (a4.Qset : Set (CoarseSquare Δ)) : ENNReal)
          ≤ (a4.Qset.card : ENNReal) := h1
        _ ≤ ENNReal.ofReal (Real.rpow Δ (-50 * ε)) * (Q_good.card : ENNReal) := h2
        _ ≤ ENNReal.ofReal (Real.rpow Δ (-50 * ε)) *
            Metric.externalCoveringNumber Δ.toNNReal (Q_good : Set (CoarseSquare Δ)) := by
          gcongr <;> exact h_qbar_cover
    have hK_pos : 0 < Real.rpow Δ (-50 * ε) := h_rpow_pos (-50 * ε)
    have h_const : Real.rpow Δ (-50 * ε) * Real.rpow Δ (-25 * ε) = Real.rpow Δ (-75 * ε) := by
      rw [h_rpow_mul (-50 * ε) (-25 * ε)] <;> ring_nf
    have h_result : IsDeltaSSet Δ t (Real.rpow Δ (-50 * ε) * Real.rpow Δ (-25 * ε)) (Q_good : Set (CoarseSquare Δ)) :=
      IsDeltaSSet.subset_with_cover_ratio a4.hQset_sset (Finset.filter_subset _ _) hK_pos h_ratio
    rw [h_const] at h_result
    exact h_result

  -- G2
  have hG2 : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ Q_good), Real.rpow Δ (-s + 13 * ε) ≤
      ((a4.perSquare Q ((Finset.mem_filter.mp hQ).1)).C_Q_pi.card : ℝ) := by
    intro Q hQ
    let hQ_in : Q ∈ a4.Qset := (Finset.mem_filter.mp hQ).1
    have h1 : ((a4.perSquare Q hQ_in).C_Q_pi.card : ℝ) ≥
        Real.rpow Δ (-s + 12 * ε) := hC_pi_lower Q hQ_in
    have h2 : Real.rpow Δ (-s + 12 * ε) ≥ Real.rpow Δ (-s + 13 * ε) := by
      apply Real.rpow_le_rpow_of_exponent_ge hΔ_pos hΔ_le_one <;> linarith
    linarith

  -- G1
  have hG1 : (T_j.card : ℝ) ≤ Real.rpow Δ (-2 * s - 3 * ε) := by
    have h2 : (T_j.card : ℝ) ≤ (C_global_A2.card : ℝ) := by
      exact_mod_cast Finset.card_le_card (hTj_sub_TΔ.trans hTΔ_sub)
    have h3 : (C_global_A2.card : ℝ) ≤ Real.rpow Δ (-2 * s - 3 * ε) := hCglobal_A2_upper
    linarith

  -- H_uniform
  have hH_uniform_lower' : a4.H_uniform ≥ Real.rpow Δ (-(s + t) + 37 * ε) := a4.hH_uniform_lower
  have hH_uniform' : ∀ (Q : CoarseSquare Δ) (hQ : Q ∈ Q_good),
      (a4.perSquare Q ((Finset.mem_filter.mp hQ).1)).base.H_Q ∈
        Set.Icc (a4.H_uniform / 2) (2 * a4.H_uniform) := by
    intro Q hQ
    exact a4.hH_uniform Q ((Finset.mem_filter.mp hQ).1)

  -- Q_good card bounds
  have hQ_good_card_lower : Real.rpow Δ (-t + 50 * ε) ≤ (Q_good.card : ℝ) := hQ_good_lower_50
  have hQ_good_card_upper : (Q_good.card : ℝ) ≤ Real.rpow Δ (-t - ε) := by
    have h1 : Q_good ⊆ a4.Qset := Finset.filter_subset _ _
    have h2 : (Q_good.card : ℝ) ≤ (a4.Qset.card : ℝ) := by exact_mod_cast Finset.card_le_card h1
    have h3 : (a4.Qset.card : ℝ) ≤ Real.rpow Δ (-t - ε) := hQset_size_upper
    exact le_trans h2 h3

  -- Physical ball-growth
  have hQ_good_phys_growth : ∀ (c : Plane) (r : ℝ), Δ ≤ r →
      ((Q_good.filter (fun Q => dist (squareCenter Δ Q) c ≤ r)).card : ℝ) ≤
        Real.rpow Δ (-80 * ε) * r^t * (Q_good.card : ℝ) := by
    intro c r hr
    let f : CoarseSquare Δ → Prop := fun Q => dist (squareCenter Δ Q) c ≤ r
    have h_filter_sub : Q_good.filter f ⊆ a4.Qset.filter f :=
      Finset.filter_subset_filter _ (Finset.filter_subset _ _)
    have h1 : ((Q_good.filter f).card : ℝ) ≤ ((a4.Qset.filter f).card : ℝ) := by
      exact_mod_cast Finset.card_le_card h_filter_sub
    have h2 : (a4.Qset.card : ℝ) ≤ Real.rpow Δ (-50 * ε) * (Q_good.card : ℝ) := h_card_ratio
    have h3 : ((a4.Qset.filter f).card : ℝ) ≤
        Real.rpow Δ (-20 * ε) * r^t * (a4.Qset.card : ℝ) := a4.hQset_phys_growth c r hr
    have h_rt_nonneg : 0 ≤ r^t := Real.rpow_nonneg (by linarith) t
    have h_rpow20_nonneg : 0 ≤ Real.rpow Δ (-20 * ε) := Real.rpow_nonneg hΔ_pos.le _
    have h_a_nonneg : 0 ≤ Real.rpow Δ (-20 * ε) * r^t := mul_nonneg h_rpow20_nonneg h_rt_nonneg
    have h9 : Real.rpow Δ (-20 * ε) * Real.rpow Δ (-50 * ε) = Real.rpow Δ (-70 * ε) := by
      have h_add : Real.rpow Δ (-20 * ε) * Real.rpow Δ (-50 * ε) =
          Real.rpow Δ ((-20 * ε) + (-50 * ε)) :=
        (Real.rpow_add hΔ_pos (-20 * ε) (-50 * ε)).symm
      rw [h_add]
      have h_sum : (-20 * ε) + (-50 * ε) = -70 * ε := by ring
      rw [h_sum]
    have h10 : Real.rpow Δ (-70 * ε) ≤ Real.rpow Δ (-80 * ε) :=
      Real.rpow_le_rpow_of_exponent_ge hΔ_pos hΔ_le_one (by linarith)
    have h4 : Real.rpow Δ (-20 * ε) * r^t * (a4.Qset.card : ℝ) ≤
        Real.rpow Δ (-80 * ε) * r^t * (Q_good.card : ℝ) := by
      calc Real.rpow Δ (-20 * ε) * r^t * (a4.Qset.card : ℝ)
        ≤ Real.rpow Δ (-20 * ε) * r^t * (Real.rpow Δ (-50 * ε) * (Q_good.card : ℝ)) :=
          mul_le_mul_of_nonneg_left h2 h_a_nonneg
      _ = (Real.rpow Δ (-20 * ε) * Real.rpow Δ (-50 * ε)) * r^t * (Q_good.card : ℝ) := by ring
      _ = Real.rpow Δ (-70 * ε) * r^t * (Q_good.card : ℝ) := by rw [h9] <;> ring
      _ ≤ Real.rpow Δ (-80 * ε) * r^t * (Q_good.card : ℝ) := by
          have h_b_nonneg : 0 ≤ r^t * (Q_good.card : ℝ) := by positivity
          have h : Real.rpow Δ (-70 * ε) * (r^t * (Q_good.card : ℝ)) ≤
              Real.rpow Δ (-80 * ε) * (r^t * (Q_good.card : ℝ)) :=
            mul_le_mul_of_nonneg_right h10 h_b_nonneg
          simpa [mul_assoc] using h
    exact le_trans h1 (le_trans h3 h4)

  let perSquare' : ∀ (Q : CoarseSquare Δ), Q ∈ Q_good → A4_SquareData Δ δ s t ε Q :=
    fun Q hQ => a4.perSquare Q ((Finset.mem_filter.mp hQ).1)

  have h_local_sub_T_full : a5FullFineFamily Δ δ s t ε Q_good perSquare' ⊆ T_full := by
    intro T hT
    rcases Finset.mem_biUnion.mp hT with ⟨Q', hT_in⟩
    have hQ_in : Q'.val ∈ a4.Qset := (Finset.mem_filter.mp Q'.property).1
    have h_eq : perSquare' Q'.val Q'.property = a4.perSquare Q'.val hQ_in := by
      dsimp only [perSquare'] <;> rfl
    let Q'' : {x : CoarseSquare Δ // x ∈ a4.Qset} := ⟨Q'.val, hQ_in⟩
    have hT_mem : T ∈ (a4.perSquare Q'.val hQ_in).base.P_Q.biUnion
        (fun p => (a4.perSquare Q'.val hQ_in).base.T_Q p) := by
      have h : T ∈ (perSquare' Q'.val Q'.property).base.P_Q.biUnion
          (fun p => (perSquare' Q'.val Q'.property).base.T_Q p) := hT_in.2
      rw [h_eq] at h
      exact h
    have h : T ∈ a5FullFineFamily Δ δ s t ε a4.Qset a4.perSquare :=
      Finset.mem_biUnion.mpr ⟨Q'', by simp [Q''], hT_mem⟩
    exact h

  let out : A5_Output Δ δ s t ε :=
    { hΔ_pos := hΔ_pos
    , Qset := Q_good
    , perSquare := perSquare'
    , hQset_sset := hQbar_sset
    , hQset_card_lower := hQ_good_card_lower
    , hQset_card_upper := hQ_good_card_upper
    , C_global := T_j
    , C_global_input := C_global_A2
    , hC_global_sub := hTj_sub_TΔ.trans hTΔ_sub
    , T_full := T_full
    , h_local_sub_T_full := h_local_sub_T_full
    , T_global := T_global
    , hT_selected_eq := by rfl
    , h_parent_unique := h_parent_unique
    , N := N
    , hN_pos := hN_pos
    , hN_upper_core := hN_upper
    , hN_upper := hN_upper
    , hG1_Cglobal_size := hG1
    , hG2_local_size := hG2
    , hG3_intersection := fun (Q : CoarseSquare Δ) (hQ : Q ∈ Q_good) => by
        have hQ_in : Q ∈ a4.Qset := (Finset.mem_filter.mp hQ).1
        have h_eq : (perSquare' Q hQ).C_Q_pi = C' Q := by
          dsimp only [perSquare', C']
          rw [dif_pos hQ_in]
          <;> rfl
        have h : Real.rpow Δ (-s + 23 * ε) ≤ (((C' Q) ∩ T_j).card : ℝ) := hG3 Q hQ
        simpa [h_eq] using h
    , hG4_uniform := fun boldT hT => by
        have h_eq : globalFiber Δ hΔ_pos T_global boldT = globalFiber Δ hΔ_pos T_full boldT :=
          h_fiber_eq boldT hT
        rw [h_eq]
        exact h_n_lower boldT hT
    , hG4_upper := fun boldT hT => by
        have h_eq : globalFiber Δ hΔ_pos T_global boldT = globalFiber Δ hΔ_pos T_full boldT :=
          h_fiber_eq boldT hT
        rw [h_eq]
        exact hG4_upper boldT hT
    , h_partition := h_partition
    , H_uniform := a4.H_uniform
    , hH_uniform_lower := hH_uniform_lower'
    , hH_uniform := hH_uniform'
    , hQset_phys_growth := hQ_good_phys_growth
    }
  exact ⟨out, rfl, hQ_good_sub⟩

end DirecretisedFurstenbergEstimate.AppendixA5
