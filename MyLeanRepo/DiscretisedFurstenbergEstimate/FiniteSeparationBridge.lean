module

/-
  Finite separation bridge: extract finite δ-separated S-subsets from S-sets.

  Key lemma: `finite_separated_tube_sset` — given a bounded (δ,s,C)-set of
  AffineLines, produce a finite δ-separated subset that is itself a
  (δ,s,C*K)-set with K = affineLine_packing_constant.

  Whiteprint node: lemmaB_coarse_structure (bridge sub-part)
  Dependencies: FiniteSeparatedTubes, PackingBound, ThickTubeCoverAffineLine
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FiniteSeparatedTubes
public import MyLeanRepo.DiscretisedFurstenbergEstimate.PackingBound
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ThickTubeCoverAffineLine
public import MyLeanRepo.OSWPrelude

@[expose] public section


noncomputable section

open scoped ENNReal NNReal

namespace DirecretisedFurstenbergEstimate

/-- A finite δ-separated subset of a bounded (δ,s,C)-set of AffineLines
    is itself a (δ,s,C*K)-set, where K = affineLine_packing_constant.

    This is the bridge needed to go from the main theorem's potentially
    infinite tube families (which are S-sets) to the finite δ-separated
    tube families required by `thick_tube_cover_affine`. -/
lemma finite_separated_tube_sset {δ s C : ℝ} {T : Set AffineLine}
    (hδ_pos : 0 < δ)
    (h : IsDeltaSSet δ s C T)
    (hT_bounded : Bornology.IsBounded T) :
    ∃ (T' : Set AffineLine), T'.Finite ∧ T' ⊆ T ∧
      Separated' δ T' ∧
      Metric.IsCover δ.toNNReal T T' ∧
      IsDeltaSSet δ s (C * (K_pack : ℝ)) T' := by
  have hT_nonempty : T.Nonempty := h.1
  let δnn : NNReal := δ.toNNReal
  have hδ_nonneg : 0 ≤ δ := by linarith
  have hδnn_coe : (δnn : ℝ) = δ := by
    simp [δnn, hδ_nonneg]
  have hδnn_pos : 0 < δnn := by
    rw [← NNReal.coe_pos, hδnn_coe]
    exact hδ_pos
  -- Step 1: Extract finite δ-separated cover
  rcases finite_separated_tubes (δ := δnn) hδnn_pos hT_bounded hT_nonempty
    with ⟨T', hT'_finite, hT'_sub, hT'_sep, hT'_cover, hT'_ge⟩
  -- Step 2: Convert Metric.IsSeparated to Separated'
  have hT'_sep' : Separated' δ T' := by
    intro x hx y hy hxy
    have h_strict : (δnn : ENNReal) < edist x y := hT'_sep hx hy hxy
    have h_le : (δnn : ENNReal) ≤ edist x y := le_of_lt h_strict
    have h2 : edist x y = ENNReal.ofReal (dist x y) := edist_dist x y
    rw [h2] at h_le
    have h3 : ENNReal.ofReal δ ≤ ENNReal.ofReal (dist x y) := by
      have h4 : (δnn : ENNReal) = ENNReal.ofReal δ := by
        simp [δnn, ENNReal.coe_nnreal_eq]
      rw [h4] at h_le
      exact h_le
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h3
  -- Step 2b: Convert to Set.Pairwise for separated_set_card_le_covering
  have hT'_pairwise : Set.Pairwise T' (fun x y : AffineLine => δ ≤ dist x y) := by
    intro x hx y hy hne
    exact hT'_sep' x hx y hy hne
  -- Step 3: T' is nonempty
  have hT'_nonempty : T'.Nonempty := hT'_cover.nonempty hT_nonempty
  -- Step 4: covering_δ(T') is finite
  have hcov_T' : (Metric.externalCoveringNumber δnn T' : ENNReal) < ⊤ := by
    have h_le : Metric.externalCoveringNumber δnn T' ≤ T'.encard :=
      Metric.externalCoveringNumber_le_encard_self T'
    have h2 : T'.encard ≠ ⊤ := hT'_finite.encard_lt_top.ne
    have h3 : Metric.externalCoveringNumber δnn T' ≠ ⊤ := ne_top_of_le_ne_top h2 h_le
    have h4 : (Metric.externalCoveringNumber δnn T' : ENNReal) ≠ ⊤ := by
      exact_mod_cast h3
    exact lt_top_iff_ne_top.mpr h4
  -- Step 5: |T'| ≤ K * covering_δ(T')
  have hT'_pairwise_nn : Set.Pairwise T' (fun x y : AffineLine => (δnn : ℝ) ≤ dist x y) := by
    simpa [hδnn_coe] using hT'_pairwise
  have h_pack_bound : (T'.encard : ENNReal) ≤
      (K_pack : ENNReal) * (Metric.externalCoveringNumber δnn T' : ENNReal) :=
    MainAppendix.separated_set_card_le_covering
      hT'_pairwise_nn
      K_pack
      (fun z S hsep hsub =>
        have hsep' : Set.Pairwise S (fun x y : AffineLine => δ ≤ dist x y) := by
          simpa [hδnn_coe] using hsep
        have hsub' : S ⊆ Metric.closedBall z (2 * δ) := by
          simpa [hδnn_coe] using hsub
        MainAppendix.affineLine_packing_bound δ hδ_pos hsep' z hsub')
      hcov_T'
  -- Step 6: T' is an S-set with constant C * K
  let K : ℝ := (K_pack : ℝ)
  have hK_pos : 0 < K := by
    have h : 0 < K_pack := K_pack_pos
    have h' : (0 : ℝ) < (K_pack : ℝ) := by exact_mod_cast h
    simpa [K] using h'
  have hCK_pos : 0 < C * K := mul_pos h.2.2.1 hK_pos
  have hδnn_eq : δnn = δ.toNNReal := by simp [δnn]
  have hT'_cover' : Metric.IsCover δ.toNNReal T T' := by
    rw [hδnn_eq] at hT'_cover
    exact hT'_cover
  refine ⟨T', hT'_finite, hT'_sub, hT'_sep', hT'_cover', ?_⟩
  refine ⟨hT'_nonempty, hδ_pos, hCK_pos, h.2.2.2.1, ?_⟩
  intro x r hr
  have h1 : (Metric.externalCoveringNumber δ.toNNReal (T' ∩ Metric.closedBall x r) : ENNReal) ≤
      (Metric.externalCoveringNumber δ.toNNReal (T ∩ Metric.closedBall x r) : ENNReal) := by
    have h_sub : (T' ∩ Metric.closedBall x r) ⊆ (T ∩ Metric.closedBall x r) := by gcongr
    have h : Metric.externalCoveringNumber δ.toNNReal (T' ∩ Metric.closedBall x r) ≤
        Metric.externalCoveringNumber δ.toNNReal (T ∩ Metric.closedBall x r) :=
      Metric.externalCoveringNumber_mono_set h_sub
    exact_mod_cast h
  have h2 : (Metric.externalCoveringNumber δ.toNNReal (T ∩ Metric.closedBall x r) : ENNReal) ≤
      ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
        (Metric.externalCoveringNumber δ.toNNReal T : ENNReal) :=
    h.2.2.2.2 x r hr
  have h3 : (Metric.externalCoveringNumber δ.toNNReal T : ENNReal) ≤ (T'.encard : ENNReal) := by
    rw [hδnn_eq] at hT'_ge
    exact_mod_cast hT'_ge
  have h4 : (T'.encard : ENNReal) ≤
      ENNReal.ofReal K * (Metric.externalCoveringNumber δ.toNNReal T' : ENNReal) := by
    rw [hδnn_eq] at h_pack_bound
    simpa [K] using h_pack_bound
  calc (Metric.externalCoveringNumber δ.toNNReal (T' ∩ Metric.closedBall x r) : ENNReal)
    ≤ (Metric.externalCoveringNumber δ.toNNReal (T ∩ Metric.closedBall x r) : ENNReal) := h1
  _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
        (Metric.externalCoveringNumber δ.toNNReal T : ENNReal) := h2
  _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * (T'.encard : ENNReal) := by gcongr
  _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
        (ENNReal.ofReal K * (Metric.externalCoveringNumber δ.toNNReal T' : ENNReal)) := by gcongr
  _ = ENNReal.ofReal (C * K) * (ENNReal.ofReal r) ^ s *
        (Metric.externalCoveringNumber δ.toNNReal T' : ENNReal) := by
    have h6 : ENNReal.ofReal C * ENNReal.ofReal K = ENNReal.ofReal (C * K) := by
      rw [← ENNReal.ofReal_mul (show 0 ≤ C from h.2.2.1.le)] <;> rfl
    have h_goal : ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * (ENNReal.ofReal K * (Metric.externalCoveringNumber δ.toNNReal T' : ENNReal)) =
        ENNReal.ofReal (C * K) * (ENNReal.ofReal r) ^ s * (Metric.externalCoveringNumber δ.toNNReal T' : ENNReal) := by
      calc
        ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * (ENNReal.ofReal K * (Metric.externalCoveringNumber δ.toNNReal T' : ENNReal))
          = (ENNReal.ofReal C * ENNReal.ofReal K) * ((ENNReal.ofReal r) ^ s) * (Metric.externalCoveringNumber δ.toNNReal T' : ENNReal) := by
            simp [mul_assoc, mul_comm, mul_left_comm]
        _ = ENNReal.ofReal (C * K) * ((ENNReal.ofReal r) ^ s) * (Metric.externalCoveringNumber δ.toNNReal T' : ENNReal) := by
            rw [h6]
    exact h_goal

end DirecretisedFurstenbergEstimate

end
