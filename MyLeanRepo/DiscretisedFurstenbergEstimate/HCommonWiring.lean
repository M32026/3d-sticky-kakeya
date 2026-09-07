module

/-
  h_common wiring: extract maximal δ-separated subsets and apply
  common_tubes_bound_proof.

  Given two finite (δ,s,C_s)-sets T1, T2 of tubes near q1, q2,
  extract maximal δ-separated subsets T1', T2' and prove
  |T1' ∩ T2'| ≤ C_common * dist(q1,q2)^{-s}.

  The separated subsets inherit the S-set property with constant C_s * K_pack,
  where K_pack = affineLine_packing_constant.

  Whiteprint node: Phase2 / HCommonWiring
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.PackingBound
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CommonTubeGeometricLemma
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DirecretisedFurstenbergEstimate.MainAppendix

open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.Phase2
open Metric Set

/-- The affine line packing constant is positive. -/
lemma affineLine_packing_constant_pos : 0 < affineLine_packing_constant := by
  let h_exists := exists_packing_constant_general (R := (8 : ℝ)) (by norm_num)
    (V := AffineLineEmbeddingV)
  have h_main : ∀ (x : AffineLineEmbeddingV) (S : Set AffineLineEmbeddingV),
      S ⊆ Metric.closedBall x 8 →
      Set.Pairwise S (fun a b => (1 : ℝ) ≤ dist a b) →
      S.Finite ∧ S.encard ≤ (affineLine_packing_constant : ENat) :=
    Classical.choose_spec h_exists
  let z : AffineLineEmbeddingV := 0
  have h1 : ({z} : Set AffineLineEmbeddingV) ⊆ Metric.closedBall z 8 := by simp
  have h2 : Set.Pairwise ({z} : Set AffineLineEmbeddingV) (fun a b => (1 : ℝ) ≤ dist a b) := by
    intro a ha b hb hab
    have ha' : a = z := by simpa using ha
    have hb' : b = z := by simpa using hb
    exact False.elim (hab (by rw [ha', hb']))
  have h3 := h_main z ({z} : Set AffineLineEmbeddingV) h1 h2
  have h4 : ({z} : Set AffineLineEmbeddingV).encard = 1 := by simp
  rw [h4] at h3
  have h5 : (1 : ENat) ≤ (affineLine_packing_constant : ENat) := h3.2
  have h6 : 0 < affineLine_packing_constant := by
    by_contra h
    have h7 : affineLine_packing_constant = 0 := by omega
    rw [h7] at h5
    simp at h5
  exact h6

/-- Transfer S-set property to a maximal δ-separated subset.

    If T' is a maximal δ-separated subset of T (hence a δ-cover of T),
    then T' is a (δ, s, C_s * K_pack)-set. -/
lemma separated_subset_sset_transfer
    {δ s C_s : ℝ} (hδ_pos : 0 < δ) (hs_nonneg : 0 ≤ s) (hC_s_pos : 0 < C_s)
    {T T' : Set AffineLine}
    (hT_sset : IsDeltaSSet δ s C_s T)
    (hT'_sub : T' ⊆ T)
    (hT'_sep : Set.Pairwise T' (fun x y => δ ≤ dist x y))
    (hT'_cover : Metric.IsCover δ.toNNReal T T')
    (hT'_finite : Set.Finite T') :
    IsDeltaSSet δ s (C_s * (affineLine_packing_constant : ℝ)) T' := by
  let δnn : NNReal := δ.toNNReal
  have hδnn_eq : (δnn : ℝ) = δ := by simp [δnn, hδ_pos.le]
  let Kpack : ℕ := affineLine_packing_constant
  have hK_pos : 0 < (Kpack : ℝ) := Nat.cast_pos.mpr affineLine_packing_constant_pos

  have h1 : (Metric.externalCoveringNumber δnn T' : ENNReal) ≤
      (Metric.externalCoveringNumber δnn T : ENNReal) := by
    simpa using Metric.externalCoveringNumber_mono_set hT'_sub

  have h2 : (Metric.externalCoveringNumber δnn T : ENNReal) ≤
      ENat.toENNReal T'.encard := by
    simpa using hT'_cover.externalCoveringNumber_le_encard

  have hcov_fin : (Metric.externalCoveringNumber δnn T' : ENNReal) < ⊤ := by
    have hcover_self : Metric.IsCover δnn T' T' := by
      intro x hx; exact ⟨x, hx, by simp [hδ_pos.le]⟩
    have h : (Metric.externalCoveringNumber δnn T' : ENNReal) ≤ ENat.toENNReal T'.encard := by
      simpa using hcover_self.externalCoveringNumber_le_encard
    have h' : ENat.toENNReal T'.encard < ⊤ := by simpa using hT'_finite.encard_lt_top
    exact lt_of_le_of_lt h h'

  have h_pack_arg : ∀ (z : AffineLine) (T : Set AffineLine),
      Set.Pairwise T (fun x y => (δnn : ℝ) ≤ dist x y) →
      T ⊆ Metric.closedBall z (2 * (δnn : ℝ)) →
      T.Finite ∧ T.encard ≤ (Kpack : ENat) := by
    intro z T hT_sep hT_sub
    have hT_sep' : Set.Pairwise T (fun x y => δ ≤ dist x y) := by simpa [hδnn_eq] using hT_sep
    have hT_sub' : T ⊆ Metric.closedBall z (2 * δ) := by simpa [hδnn_eq] using hT_sub
    exact affineLine_packing_bound δ hδ_pos hT_sep' z hT_sub'

  have h3 : ENat.toENNReal T'.encard ≤
      (Kpack : ENNReal) * (Metric.externalCoveringNumber δnn T' : ENNReal) :=
    separated_set_card_le_covering (hS_sep := by simpa [hδnn_eq] using hT'_sep)
      Kpack h_pack_arg hcov_fin

  have h4 : (Metric.externalCoveringNumber δnn T : ENNReal) ≤
      (Kpack : ENNReal) * (Metric.externalCoveringNumber δnn T' : ENNReal) := by
    calc (Metric.externalCoveringNumber δnn T : ENNReal)
      ≤ ENat.toENNReal T'.encard := h2
    _ ≤ (Kpack : ENNReal) * (Metric.externalCoveringNumber δnn T' : ENNReal) := h3

  rcases hT_sset with ⟨hT_nonempty, hδ_pos', hC_pos', hs_nonneg', hmain⟩
  have hT'_nonempty : T'.Nonempty := by
    by_contra h
    have h_empty : T' = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    rw [h_empty] at hT'_cover
    have h6 : T = ∅ := by simpa [Metric.IsCover] using hT'_cover
    rw [h6] at hT_nonempty; simp at hT_nonempty
  have hC'_pos : 0 < C_s * (Kpack : ℝ) := mul_pos hC_s_pos hK_pos
  refine ⟨hT'_nonempty, hδ_pos', hC'_pos, hs_nonneg', ?_⟩
  intro x r hr
  have h_sub_int : T' ∩ Metric.closedBall x r ⊆ T ∩ Metric.closedBall x r := by
    intro y hy; exact ⟨hT'_sub hy.1, hy.2⟩
  have h5 : (Metric.externalCoveringNumber δnn (T' ∩ Metric.closedBall x r) : ENNReal) ≤
      (Metric.externalCoveringNumber δnn (T ∩ Metric.closedBall x r) : ENNReal) := by
    simpa using Metric.externalCoveringNumber_mono_set h_sub_int
  have h6 : (Metric.externalCoveringNumber δnn (T ∩ Metric.closedBall x r) : ENNReal) ≤
      ENNReal.ofReal C_s * (ENNReal.ofReal r) ^ s * (Metric.externalCoveringNumber δnn T : ENNReal) :=
    hmain x r hr
  have h7 : (Metric.externalCoveringNumber δnn (T' ∩ Metric.closedBall x r) : ENNReal) ≤
      ENNReal.ofReal C_s * (ENNReal.ofReal r) ^ s *
        ((Kpack : ENNReal) * (Metric.externalCoveringNumber δnn T' : ENNReal)) := by
    calc (Metric.externalCoveringNumber δnn (T' ∩ Metric.closedBall x r) : ENNReal)
      ≤ (Metric.externalCoveringNumber δnn (T ∩ Metric.closedBall x r) : ENNReal) := h5
    _ ≤ ENNReal.ofReal C_s * (ENNReal.ofReal r) ^ s * (Metric.externalCoveringNumber δnn T : ENNReal) := h6
    _ ≤ ENNReal.ofReal C_s * (ENNReal.ofReal r) ^ s *
          ((Kpack : ENNReal) * (Metric.externalCoveringNumber δnn T' : ENNReal)) := by
      gcongr
  have h_pos_C : 0 ≤ C_s := by linarith
  have h_mul : ENNReal.ofReal C_s * ENNReal.ofReal (Kpack : ℝ) =
      ENNReal.ofReal (C_s * (Kpack : ℝ)) := by
    rw [←ENNReal.ofReal_mul h_pos_C] <;> rfl
  have h_final : ENNReal.ofReal C_s * (ENNReal.ofReal r) ^ s *
        ((Kpack : ENNReal) * (Metric.externalCoveringNumber δnn T' : ENNReal)) =
      ENNReal.ofReal (C_s * (Kpack : ℝ)) * (ENNReal.ofReal r) ^ s *
        (Metric.externalCoveringNumber δnn T' : ENNReal) := by
    have h_eq1 : (Kpack : ENNReal) = ENNReal.ofReal (Kpack : ℝ) := by
      have h : (Kpack : ℝ) = ↑Kpack := by rfl
      rw [h]; norm_cast
    calc
      ENNReal.ofReal C_s * (ENNReal.ofReal r) ^ s *
          ((Kpack : ENNReal) * (Metric.externalCoveringNumber δnn T' : ENNReal))
        = ENNReal.ofReal C_s * (ENNReal.ofReal r) ^ s *
            (ENNReal.ofReal (Kpack : ℝ) * (Metric.externalCoveringNumber δnn T' : ENNReal)) := by
          rw [h_eq1]
      _ = (ENNReal.ofReal C_s * ENNReal.ofReal (Kpack : ℝ)) * (ENNReal.ofReal r) ^ s *
            (Metric.externalCoveringNumber δnn T' : ENNReal) := by
          simp [mul_assoc, mul_comm, mul_left_comm]
      _ = ENNReal.ofReal (C_s * (Kpack : ℝ)) * (ENNReal.ofReal r) ^ s *
            (Metric.externalCoveringNumber δnn T' : ENNReal) := by
          rw [h_mul]
  rw [h_final] at h7
  exact h7

/-- h_common bound for maximal δ-separated subsets of two tube families.

    Extracts maximal δ-separated subsets T1', T2' and proves
    |T1' ∩ T2'| ≤ C_common * dist(q,q')^{-s}.

    Constant requirement: C_s^2 * K_pack^3 * 1600^s ≤ C_common. -/
lemma h_common_for_separated_subsets
    (δ s C_s C_common : ℝ)
    (hδ_pos : 0 < δ) (hs_pos : 0 < s) (hC_s_pos : 0 < C_s) (hC_common_pos : 0 < C_common)
    (q q' : EuclideanPlane) (hd : δ ≤ dist q q')
    (hq_bound : ‖q‖ ≤ 2) (hq'_bound : ‖q'‖ ≤ 2)
    (T1 T2 : Set AffineLine)
    (hT1_sset : IsDeltaSSet δ s C_s T1)
    (hT2_sset : IsDeltaSSet δ s C_s T2)
    (hT1_near : ∀ ℓ ∈ T1, q ∈ Metric.cthickening (2 * δ) ℓ.1)
    (hT2_near : ∀ ℓ ∈ T2, q' ∈ Metric.cthickening (2 * δ) ℓ.1)
    (hT1_size : ENat.toENNReal T1.encard ≤ ENNReal.ofReal (C_s * δ ^ (-s)))
    (hT1_finite : Set.Finite T1) (hT2_finite : Set.Finite T2)
    (h_const : C_s^2 * (affineLine_packing_constant : ℝ)^3 * (1600 : ℝ)^s ≤ C_common) :
    let T1' := Metric.maximalSeparatedSet δ.toNNReal T1
    let T2' := Metric.maximalSeparatedSet δ.toNNReal T2
    ENat.toENNReal (T1' ∩ T2').encard ≤
      ENNReal.ofReal (C_common * (dist q q') ^ (-s)) := by
  let δnn : NNReal := δ.toNNReal
  have hδnn_eq : (δnn : ℝ) = δ := by simp [δnn, hδ_pos.le]
  let T1' := Metric.maximalSeparatedSet δnn T1
  let T2' := Metric.maximalSeparatedSet δnn T2
  let Kpack : ℝ := (affineLine_packing_constant : ℝ)
  let C_s' : ℝ := C_s * Kpack
  have hK_pos : 0 < Kpack := Nat.cast_pos.mpr affineLine_packing_constant_pos
  have hC_s'_pos : 0 < C_s' := mul_pos hC_s_pos hK_pos

  have hT1'_sub : T1' ⊆ T1 := Metric.maximalSeparatedSet_subset
  have hT2'_sub : T2' ⊆ T2 := Metric.maximalSeparatedSet_subset

  have h_sep1 : Metric.IsSeparated δnn T1' := Metric.isSeparated_maximalSeparatedSet
  have hT1'_sep : Set.Pairwise T1' (fun x y => δ ≤ dist x y) := by
    intro x hx y hy hxy
    have h' : (↑δnn : ENNReal) < edist x y := h_sep1 hx hy hxy
    have h'' : (δnn : ℝ) < dist x y := by simpa [edist_dist, hδ_pos.le] using h'
    have h_eq : (δnn : ℝ) = δ := hδnn_eq
    rw [h_eq] at h''; linarith
  have h_sep2 : Metric.IsSeparated δnn T2' := Metric.isSeparated_maximalSeparatedSet
  have hT2'_sep : Set.Pairwise T2' (fun x y => δ ≤ dist x y) := by
    intro x hx y hy hxy
    have h' : (↑δnn : ENNReal) < edist x y := h_sep2 hx hy hxy
    have h'' : (δnn : ℝ) < dist x y := by simpa [edist_dist, hδ_pos.le] using h'
    have h_eq : (δnn : ℝ) = δ := hδnn_eq
    rw [h_eq] at h''; linarith

  have h_pack1 : Metric.packingNumber δnn T1 ≠ ⊤ := by
    have h : Metric.packingNumber δnn T1 ≤ T1.encard := Metric.packingNumber_le_encard_self T1
    have h' : T1.encard < ⊤ := hT1_finite.encard_lt_top
    exact ne_of_lt (lt_of_le_of_lt h h')
  have h_pack2 : Metric.packingNumber δnn T2 ≠ ⊤ := by
    have h : Metric.packingNumber δnn T2 ≤ T2.encard := Metric.packingNumber_le_encard_self T2
    have h' : T2.encard < ⊤ := hT2_finite.encard_lt_top
    exact ne_of_lt (lt_of_le_of_lt h h')

  have hT1'_cover : Metric.IsCover δnn T1 T1' := Metric.isCover_maximalSeparatedSet h_pack1
  have hT2'_cover : Metric.IsCover δnn T2 T2' := Metric.isCover_maximalSeparatedSet h_pack2
  have hT1'_finite : Set.Finite T1' := hT1_finite.subset hT1'_sub
  have hT2'_finite : Set.Finite T2' := hT2_finite.subset hT2'_sub

  have hT1'_sset : IsDeltaSSet δ s C_s' T1' :=
    separated_subset_sset_transfer hδ_pos (by linarith) hC_s_pos hT1_sset hT1'_sub hT1'_sep hT1'_cover hT1'_finite
  have hT2'_sset : IsDeltaSSet δ s C_s' T2' :=
    separated_subset_sset_transfer hδ_pos (by linarith) hC_s_pos hT2_sset hT2'_sub hT2'_sep hT2'_cover hT2'_finite

  have hT1'_near : ∀ ℓ ∈ T1', q ∈ Metric.cthickening (2 * δ) ℓ.1 := by
    intro ℓ hℓ; exact hT1_near ℓ (hT1'_sub hℓ)
  have hT2'_near : ∀ ℓ ∈ T2', q' ∈ Metric.cthickening (2 * δ) ℓ.1 := by
    intro ℓ hℓ; exact hT2_near ℓ (hT2'_sub hℓ)

  -- Size bound: |T1'| ≤ Kpack * Ncover(T1') ≤ Kpack * Ncover(T1) ≤ Kpack * |T1| ≤ C_s' * δ^{-s}
  have hT1'_size : ENat.toENNReal T1'.encard ≤ ENNReal.ofReal (C_s' * δ ^ (-s)) := by
    have hcov_fin : (Metric.externalCoveringNumber δnn T1' : ENNReal) < ⊤ := by
      have hcover_self : Metric.IsCover δnn T1' T1' := by
        intro x hx; exact ⟨x, hx, by simp [hδ_pos.le]⟩
      have h : (Metric.externalCoveringNumber δnn T1' : ENNReal) ≤ ENat.toENNReal T1'.encard := by
        simpa using hcover_self.externalCoveringNumber_le_encard
      have h' : ENat.toENNReal T1'.encard < ⊤ := by simpa using hT1'_finite.encard_lt_top
      exact lt_of_le_of_lt h h'
    have h_pack_arg : ∀ (z : AffineLine) (T : Set AffineLine),
        Set.Pairwise T (fun x y => (δnn : ℝ) ≤ dist x y) →
        T ⊆ Metric.closedBall z (2 * (δnn : ℝ)) →
        T.Finite ∧ T.encard ≤ (affineLine_packing_constant : ENat) := by
      intro z T hT_sep hT_sub
      have hT_sep' : Set.Pairwise T (fun x y => δ ≤ dist x y) := by simpa [hδnn_eq] using hT_sep
      have hT_sub' : T ⊆ Metric.closedBall z (2 * δ) := by simpa [hδnn_eq] using hT_sub
      exact affineLine_packing_bound δ hδ_pos hT_sep' z hT_sub'
    have h3 : ENat.toENNReal T1'.encard ≤
        (affineLine_packing_constant : ENNReal) * (Metric.externalCoveringNumber δnn T1' : ENNReal) :=
      separated_set_card_le_covering (hS_sep := by simpa [hδnn_eq] using hT1'_sep)
        affineLine_packing_constant h_pack_arg hcov_fin
    have h4 : (Metric.externalCoveringNumber δnn T1' : ENNReal) ≤
        (Metric.externalCoveringNumber δnn T1 : ENNReal) := by
      simpa using Metric.externalCoveringNumber_mono_set hT1'_sub
    have h5 : (Metric.externalCoveringNumber δnn T1 : ENNReal) ≤ ENat.toENNReal T1.encard := by
      have hcover_self : Metric.IsCover δnn T1 T1 := by
        intro x hx; exact ⟨x, hx, by simp [hδ_pos.le]⟩
      simpa using hcover_self.externalCoveringNumber_le_encard
    have h_eq1 : (affineLine_packing_constant : ENNReal) = ENNReal.ofReal (Kpack : ℝ) := by
      have h : (Kpack : ℝ) = ↑affineLine_packing_constant := by rfl
      rw [h]; norm_cast
    have h_pos1 : 0 ≤ Kpack := by positivity
    have h_pos2 : 0 ≤ C_s * δ ^ (-s) := by positivity
    have h_goal : Kpack * (C_s * δ ^ (-s)) = C_s' * δ ^ (-s) := by
      simp [C_s'] <;> ring
    calc ENat.toENNReal T1'.encard
      ≤ (affineLine_packing_constant : ENNReal) * (Metric.externalCoveringNumber δnn T1' : ENNReal) := h3
    _ ≤ (affineLine_packing_constant : ENNReal) * (Metric.externalCoveringNumber δnn T1 : ENNReal) := by gcongr
    _ ≤ (affineLine_packing_constant : ENNReal) * ENat.toENNReal T1.encard := by gcongr
    _ ≤ (affineLine_packing_constant : ENNReal) * ENNReal.ofReal (C_s * δ ^ (-s)) := by gcongr
    _ = ENNReal.ofReal (Kpack * (C_s * δ ^ (-s))) := by
      rw [h_eq1, ←ENNReal.ofReal_mul h_pos1] <;> rfl
    _ = ENNReal.ofReal (C_s' * δ ^ (-s)) := by rw [h_goal]

  have h_const' : C_s'^2 * (1600 : ℝ)^s * (affineLine_packing_constant : ℝ) ≤ C_common := by
    dsimp only [C_s']
    have h : (C_s * Kpack)^2 * (1600 : ℝ)^s * Kpack = C_s^2 * Kpack^3 * (1600 : ℝ)^s := by ring
    rw [h]; exact h_const

  let h_geom : ∀ (δ' : ℝ), 0 < δ' → ∀ (q q' : EuclideanPlane),
      ‖q‖ ≤ 2 → ‖q'‖ ≤ 2 → 0 < dist q q' →
      ∀ (ℓ : AffineLine),
        q ∈ Metric.cthickening (2 * δ') ℓ.1 →
        q' ∈ Metric.cthickening (2 * δ') ℓ.1 →
        ∃ (ℓ₀ : AffineLine), q ∈ ℓ₀.1 ∧ q' ∈ ℓ₀.1 ∧
          dist ℓ ℓ₀ ≤ 200 * (δ' + δ' / dist q q') := by
    intro δ' hδ' q q' hq hq' hd ℓ h1 h2
    exact common_tube_geometric_lemma_bounded δ' hδ' q q' hd hq hq' ℓ h1 h2

  exact common_tubes_bound_proof δ s C_s' C_common hδ_pos hs_pos hC_s'_pos hC_common_pos
    q q' (by linarith) hq_bound hq'_bound T1' T2' hT1'_sep hT1'_sset hT1'_near hT2'_near hT1'_size h_geom h_const'

end DirecretisedFurstenbergEstimate.MainAppendix

end
