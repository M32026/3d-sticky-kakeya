module

/-
  QTTC assembly for AffineLine families.

  Packages the complete pipeline:
  1. Set up coarse map + coarseRange on AffineLine via maximal separated subset
  2. Bound coarseRange cardinality using parameter-space antilipschitz + grid counting
  3. Call quantitative_thick_tube_cover directly on L = AffineLine
  4. Convert output IsFiniteDeltaSSet → IsDeltaSSet via PackingBound

  Dependencies:
  - QuantitativeThickTubeCover.lean (generic QTTC)
  - AffineLineCoarseningBridge.lean (exists_affineLine_coarsening)
  - AffineLineLipschitzTransfer.lean (bilipschitz bounds)
  - PackingBound.lean (affineLine_packing_constant, separated_set_card_le_covering)

  Whiteprint node: Phase4 / QTTC_Assembly
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.QuantitativeThickTubeCover
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AffineLineParams
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AffineLineLipschitzTransfer
public import MyLeanRepo.DiscretisedFurstenbergEstimate.PackingBound
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DirecretisedFurstenbergEstimate.QTTC_Assembly

open LemmaE

noncomputable def C_PACK : ℝ :=
  (DirecretisedFurstenbergEstimate.MainAppendix.affineLine_packing_constant : ℝ)

/-- Convert IsFiniteDeltaSSet to IsDeltaSSet for AffineLine.
    Uses affineLine_packing_constant and separated_set_card_le_covering. -/
lemma IsFiniteDeltaSSet.to_delta_sset_affineLine
    {δ s C : ℝ} {S : Finset AffineLine}
    (h : _root_.IsFiniteDeltaSSet δ s C S) :
    IsDeltaSSet δ s (max 1 (C_PACK * C)) (S : Set AffineLine) := by
  rcases h with ⟨hS_nonempty, hδ_pos, hC_ge1, hs_nonneg, hS_sep, h_growth⟩
  have hC_pos : 0 < C := by linarith
  let K_pack := DirecretisedFurstenbergEstimate.MainAppendix.affineLine_packing_constant
  let δnn : NNReal := δ.toNNReal
  have hδnn_eq : (δnn : ℝ) = δ := by
    simp [δnn, Real.toNNReal_of_nonneg hδ_pos.le]
  have hS_sep_nn : Set.Pairwise (S : Set AffineLine) (fun x y => (δnn : ℝ) ≤ dist x y) := by
    simpa [hδnn_eq, _root_.SeparatedAt] using hS_sep
  have h_pack_bound : ∀ (z : AffineLine) (T : Set AffineLine),
      Set.Pairwise T (fun x y => (δnn : ℝ) ≤ dist x y) →
      T ⊆ Metric.closedBall z (2 * (δnn : ℝ)) →
      T.Finite ∧ T.encard ≤ (K_pack : ENat) := by
    intro z T hT_sep hT_sub
    have hT_sep' : Set.Pairwise T (fun x y => δ ≤ dist x y) := by
      simpa [hδnn_eq] using hT_sep
    have hT_sub' : T ⊆ Metric.closedBall z (2 * δ) := by
      simpa [hδnn_eq] using hT_sub
    exact DirecretisedFurstenbergEstimate.MainAppendix.affineLine_packing_bound δ hδ_pos hT_sep' z hT_sub'
  have hcov_fin : (Metric.externalCoveringNumber δnn (S : Set AffineLine) : ENNReal) < ⊤ := by
    have h1 : Metric.externalCoveringNumber δnn (S : Set AffineLine) ≤ (S : Set AffineLine).encard :=
      Metric.externalCoveringNumber_le_encard_self (S : Set AffineLine)
    have h2 : (S : Set AffineLine).encard ≠ ⊤ := by simp
    have h3 : Metric.externalCoveringNumber δnn (S : Set AffineLine) ≠ ⊤ :=
      ne_top_of_le_ne_top h2 h1
    have h4 : (Metric.externalCoveringNumber δnn (S : Set AffineLine) : ENNReal) ≠ ⊤ := by
      exact_mod_cast h3
    exact lt_top_iff_ne_top.mpr h4
  have hS_card_le : (S.card : ENNReal) ≤
      (K_pack : ENNReal) * (Metric.externalCoveringNumber δnn (S : Set AffineLine) : ENNReal) := by
    have h_enc : ((S : Set AffineLine).encard : ENNReal) ≤
        (K_pack : ENNReal) * (Metric.externalCoveringNumber δnn (S : Set AffineLine) : ENNReal) :=
      DirecretisedFurstenbergEstimate.MainAppendix.separated_set_card_le_covering
        hS_sep_nn K_pack h_pack_bound hcov_fin
    have h_eq : ((S : Set AffineLine).encard : ENNReal) = (S.card : ENNReal) := by simp
    rw [h_eq] at h_enc
    exact h_enc
  refine' ⟨hS_nonempty, hδ_pos, by positivity, hs_nonneg, _⟩
  intro x r hr
  let S' : Finset AffineLine := S.filter (fun y => dist y x ≤ r)
  have hS'_eq : (S' : Set AffineLine) = (S : Set AffineLine) ∩ Metric.closedBall x r := by
    ext y; simp [S', Metric.mem_closedBall]
  have h1 : (Metric.externalCoveringNumber δnn (S' : Set AffineLine) : ENNReal) ≤ (S'.card : ENNReal) := by
    have h11 : Metric.externalCoveringNumber δnn (S' : Set AffineLine) ≤ (S' : Set AffineLine).encard :=
      Metric.externalCoveringNumber_le_encard_self (S' : Set AffineLine)
    have h12 : (S' : Set AffineLine).encard = ↑(S'.card) := by simp
    rw [h12] at h11
    exact_mod_cast h11
  have h2 : (S'.card : ℝ) ≤ C * r ^ s * (S.card : ℝ) := h_growth x r hr
  have h_nonneg_C : 0 ≤ C := by linarith
  have h_nonneg_r : 0 ≤ r := by linarith
  have h_nonneg_s : 0 ≤ s := hs_nonneg
  have h3 : (Metric.externalCoveringNumber δnn (S' : Set AffineLine) : ENNReal) ≤
      ENNReal.ofReal (C * r ^ s * (S.card : ℝ)) := by
    calc (Metric.externalCoveringNumber δnn (S' : Set AffineLine) : ENNReal)
      ≤ (S'.card : ENNReal) := h1
    _ = ENNReal.ofReal ((S'.card : ℝ)) := by simp
    _ ≤ ENNReal.ofReal (C * r ^ s * (S.card : ℝ)) := by
      exact ENNReal.ofReal_le_ofReal h2
  have h4 : ENNReal.ofReal (C * r ^ s * (S.card : ℝ)) ≤
      ENNReal.ofReal C * ENNReal.ofReal (r ^ s) * (S.card : ENNReal) := by
    have h5 : ENNReal.ofReal (C * r ^ s * (S.card : ℝ)) =
        ENNReal.ofReal (C * r ^ s) * (S.card : ENNReal) := by
      rw [ENNReal.ofReal_mul (show 0 ≤ C * r ^ s by positivity)] <;> simp
    rw [h5]
    have h6 : ENNReal.ofReal (C * r ^ s) = ENNReal.ofReal C * ENNReal.ofReal (r ^ s) := by
      rw [ENNReal.ofReal_mul h_nonneg_C]
    rw [h6] <;> ring
  have h5 : (S.card : ENNReal) ≤
      (K_pack : ENNReal) * (Metric.externalCoveringNumber δnn (S : Set AffineLine) : ENNReal) :=
    hS_card_le
  have h_rpow : (ENNReal.ofReal r) ^ s = ENNReal.ofReal (r ^ s) := by
    rw [ENNReal.ofReal_rpow_of_nonneg h_nonneg_r h_nonneg_s]
  have h_main : (Metric.externalCoveringNumber δnn (S' : Set AffineLine) : ENNReal) ≤
      ENNReal.ofReal (max 1 (C_PACK * C)) * (ENNReal.ofReal r) ^ s *
        (Metric.externalCoveringNumber δnn (S : Set AffineLine) : ENNReal) := by
    calc (Metric.externalCoveringNumber δnn (S' : Set AffineLine) : ENNReal)
      ≤ ENNReal.ofReal C * ENNReal.ofReal (r ^ s) * (S.card : ENNReal) := le_trans h3 h4
    _ ≤ ENNReal.ofReal C * ENNReal.ofReal (r ^ s) *
          ((K_pack : ENNReal) * (Metric.externalCoveringNumber δnn (S : Set AffineLine) : ENNReal)) := by
      gcongr
    _ = (K_pack : ENNReal) * ENNReal.ofReal C * ENNReal.ofReal (r ^ s) *
          (Metric.externalCoveringNumber δnn (S : Set AffineLine) : ENNReal) := by ring
    _ = ENNReal.ofReal ((K_pack : ℝ) * C) * ENNReal.ofReal (r ^ s) *
          (Metric.externalCoveringNumber δnn (S : Set AffineLine) : ENNReal) := by
      have h7 : (K_pack : ENNReal) = ENNReal.ofReal ((K_pack : ℝ)) := by simp
      rw [h7]
      have h8 : ENNReal.ofReal ((K_pack : ℝ)) * ENNReal.ofReal C =
          ENNReal.ofReal (((K_pack : ℝ) * C)) := by
        rw [← ENNReal.ofReal_mul (show 0 ≤ (K_pack : ℝ) by positivity)]
      rw [h8] <;> ring
    _ ≤ ENNReal.ofReal (max 1 (C_PACK * C)) * ENNReal.ofReal (r ^ s) *
          (Metric.externalCoveringNumber δnn (S : Set AffineLine) : ENNReal) := by
      have h9 : (K_pack : ℝ) = C_PACK := by
        simp [C_PACK, K_pack] <;> rfl
      rw [h9]
      have h10 : C_PACK * C ≤ max 1 (C_PACK * C) := le_max_right _ _
      gcongr
    _ = ENNReal.ofReal (max 1 (C_PACK * C)) * (ENNReal.ofReal r) ^ s *
          (Metric.externalCoveringNumber δnn (S : Set AffineLine) : ENNReal) := by
      rw [h_rpow]
  have h_final : (Metric.externalCoveringNumber δ.toNNReal ((S : Set AffineLine) ∩ Metric.closedBall x r) : ENNReal) ≤
      ENNReal.ofReal (max 1 (C_PACK * C)) * (ENNReal.ofReal r) ^ s *
        (Metric.externalCoveringNumber δ.toNNReal (S : Set AffineLine) : ENNReal) := by
    have h_eq1 : δnn = δ.toNNReal := by simp [δnn]
    have h_eq2 : (S' : Set AffineLine) = (S : Set AffineLine) ∩ Metric.closedBall x r := hS'_eq
    simpa [h_eq1, h_eq2] using h_main
  exact h_final

end DirecretisedFurstenbergEstimate.QTTC_Assembly

end
