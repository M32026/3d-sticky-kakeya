module

/-
  A2 Main Theorem: Per-square QTTC + H2.

  Takes A1_Output and produces A2_Output by applying the Quantitative
  Thick Tube Cover (QTTC) to each coarse square's point/tube configuration.

  Whiteprint node: appendix_a_alternative / A2_Main
  Dependencies: Interfaces, QTTC_Assembly, A2_StripPacking, PackingBound
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.Interfaces
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A2_TypedQTTC_Adapter
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A2DyadicAdapter
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A2_PointFiberUpper
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A2_StripPacking
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A2_Gaps
public import MyLeanRepo.DiscretisedFurstenbergEstimate.PackingBound
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal


noncomputable section

attribute [local instance] Classical.propDecidable

namespace DirecretisedFurstenbergEstimate.AppendixA.A2

open DirecretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.QTTC_Assembly
open DirecretisedFurstenbergEstimate.AppendixA.A2_RemainingGaps
open DirecretisedFurstenbergEstimate.AppendixA.A2DyadicAdapter
open DirecretisedFurstenbergEstimate.AppendixA.TypedQTTC_Assembly
open DirecretisedFurstenbergEstimate.AppendixA4

/-! ========================================================================
   Direct IsDeltaSSet → IsFiniteDeltaSSet for already-separated AffineLine
   ======================================================================== -/

/-- Direct conversion: IsDeltaSSet + SeparatedAt δ → IsFiniteDeltaSSet
    on the SAME finset (no subset extraction). Constant blows up by
    affineLine_packing_constant. -/
lemma IsDeltaSSet.to_finite_delta_sset_affineLine_already_separated
    {δ s C : ℝ} {P : Finset AffineLine}
    (h : IsDeltaSSet δ s C (P : Set AffineLine))
    (h_sep : SeparatedAt δ (P : Set AffineLine)) :
    _root_.IsFiniteDeltaSSet δ s (max 1 ((MainAppendix.affineLine_packing_constant : ℝ) * C)) P := by
  rcases h with ⟨hP_nonempty, hδ_pos, hC_pos, hs_nonneg, h_sset⟩
  let δnn : NNReal := δ.toNNReal
  have hδnn_eq : (δnn : ℝ) = δ := by
    simp [δnn, Real.toNNReal_of_nonneg hδ_pos.le]
  let K_pack := MainAppendix.affineLine_packing_constant
  have hS_sep : Set.Pairwise (P : Set AffineLine) (fun x y => δ ≤ dist x y) := h_sep
  have hS_sep_half : Set.Pairwise (P : Set AffineLine) (fun x y => δ / 2 ≤ dist x y) := by
    intro x hx y hy hne
    have h : δ ≤ dist x y := hS_sep hx hy hne
    linarith
  have hS_sep_nn : Set.Pairwise (P : Set AffineLine) (fun x y => (δnn : ℝ) ≤ dist x y) := by
    simpa [hδnn_eq] using hS_sep
  have h_pack' : ∀ (z : AffineLine) (T : Set AffineLine),
      Set.Pairwise T (fun x y => (δnn : ℝ) ≤ dist x y) →
      T ⊆ Metric.closedBall z (2 * (δnn : ℝ)) →
      T.Finite ∧ T.encard ≤ (K_pack : ENat) := by
    intro z T hT_sep hT_sub
    have hT_sep' : Set.Pairwise T (fun x y => δ ≤ dist x y) := by
      simpa [hδnn_eq] using hT_sep
    have hT_sub' : T ⊆ Metric.closedBall z (2 * δ) := by
      simpa [hδnn_eq] using hT_sub
    exact MainAppendix.affineLine_packing_bound δ hδ_pos hT_sep' z hT_sub'
  have h_ball_growth : ∀ (x : AffineLine) (r : ℝ), δ ≤ r →
      ((P.filter fun y => dist y x ≤ r).card : ℝ) ≤
        (max 1 ((K_pack : ℝ) * C)) * r ^ s * (P.card : ℝ) := by
    intro x r hr
    let S' : Finset AffineLine := P.filter (fun y => dist y x ≤ r)
    have hS'_sub : (S' : Set AffineLine) ⊆ (P : Set AffineLine) := by
      intro y hy; exact (Finset.mem_filter.mp hy).1
    have hS'_sep : Set.Pairwise (S' : Set AffineLine) (fun x y => (δnn : ℝ) ≤ dist x y) :=
      hS_sep_nn.mono hS'_sub
    have hcov_fin : (Metric.externalCoveringNumber δnn (S' : Set AffineLine) : ENNReal) < ⊤ := by
      have h1 : (Metric.externalCoveringNumber δnn (S' : Set AffineLine) : ENNReal) ≤ (S'.card : ENNReal) := by
        exact_mod_cast Metric.externalCoveringNumber_le_encard_self (S' : Set AffineLine)
      have h2 : (S'.card : ENNReal) < ⊤ := by simp
      exact lt_of_le_of_lt h1 h2
    have h_pack_cover : (S'.card : ENNReal) ≤
        (K_pack : ENNReal) * (Metric.externalCoveringNumber δnn (S' : Set AffineLine) : ENNReal) := by
      have h : ((S' : Set AffineLine).encard : ENNReal) ≤
          (K_pack : ENNReal) * (Metric.externalCoveringNumber δnn (S' : Set AffineLine) : ENNReal) :=
        MainAppendix.separated_set_card_le_covering hS'_sep K_pack h_pack' hcov_fin
      have h_eq : ((S' : Set AffineLine).encard : ENNReal) = (S'.card : ENNReal) := by simp
      rw [h_eq] at h
      exact h
    have hS'_sub_P : (S' : Set AffineLine) ⊆ (P : Set AffineLine) ∩ Metric.closedBall x r := by
      intro y hy
      have h1 : y ∈ (P : Set AffineLine) := (Finset.mem_filter.mp hy).1
      have h2 : dist y x ≤ r := (Finset.mem_filter.mp hy).2
      exact ⟨h1, h2⟩
    have h_cov_mono : (Metric.externalCoveringNumber δnn (S' : Set AffineLine) : ENNReal) ≤
        (Metric.externalCoveringNumber δnn ((P : Set AffineLine) ∩ Metric.closedBall x r) : ENNReal) := by
      exact_mod_cast Metric.externalCoveringNumber_mono_set hS'_sub_P
    have h_sset' : (Metric.externalCoveringNumber δnn ((P : Set AffineLine) ∩ Metric.closedBall x r) : ENNReal) ≤
        ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * (Metric.externalCoveringNumber δnn (P : Set AffineLine) : ENNReal) :=
      h_sset x r hr
    have hcov_P_le_card : (Metric.externalCoveringNumber δnn (P : Set AffineLine) : ENNReal) ≤ (P.card : ENNReal) := by
      exact_mod_cast Metric.externalCoveringNumber_le_encard_self (P : Set AffineLine)
    let C' := max 1 ((K_pack : ℝ) * C)
    have hC'_one : 1 ≤ C' := le_max_left _ _
    have hC'_nonneg : 0 ≤ C' := by positivity
    have hr_nonneg : 0 ≤ r := by linarith
    have h_rpow_nonneg : 0 ≤ r ^ s := Real.rpow_nonneg hr_nonneg s
    have h_rpow : (ENNReal.ofReal r) ^ s = ENNReal.ofReal (r ^ s) := by
      rw [ENNReal.ofReal_rpow_of_nonneg hr_nonneg hs_nonneg]
    have h_main : (S'.card : ENNReal) ≤ ENNReal.ofReal (C' * r ^ s * (P.card : ℝ)) := by
      calc (S'.card : ENNReal)
        ≤ (K_pack : ENNReal) * (Metric.externalCoveringNumber δnn (S' : Set AffineLine) : ENNReal) := h_pack_cover
      _ ≤ (K_pack : ENNReal) * (Metric.externalCoveringNumber δnn ((P : Set AffineLine) ∩ Metric.closedBall x r) : ENNReal) := by gcongr
      _ ≤ (K_pack : ENNReal) * (ENNReal.ofReal C * ENNReal.ofReal (r ^ s) * (Metric.externalCoveringNumber δnn (P : Set AffineLine) : ENNReal)) := by
          rw [h_rpow] at h_sset' <;> gcongr
      _ = ENNReal.ofReal ((K_pack : ℝ)) * (ENNReal.ofReal C * ENNReal.ofReal (r ^ s) * (Metric.externalCoveringNumber δnn (P : Set AffineLine) : ENNReal)) := by simp
      _ = (ENNReal.ofReal ((K_pack : ℝ)) * ENNReal.ofReal C) * ENNReal.ofReal (r ^ s) * (Metric.externalCoveringNumber δnn (P : Set AffineLine) : ENNReal) := by ring
      _ = ENNReal.ofReal (((K_pack : ℝ) * C)) * ENNReal.ofReal (r ^ s) * (Metric.externalCoveringNumber δnn (P : Set AffineLine) : ENNReal) := by
          have h_pos1 : 0 ≤ (K_pack : ℝ) := by positivity
          rw [← ENNReal.ofReal_mul h_pos1] <;> ring
      _ ≤ ENNReal.ofReal C' * ENNReal.ofReal (r ^ s) * (Metric.externalCoveringNumber δnn (P : Set AffineLine) : ENNReal) := by
          have h9 : (K_pack : ℝ) * C ≤ C' := le_max_right _ _
          gcongr
      _ ≤ ENNReal.ofReal C' * ENNReal.ofReal (r ^ s) * (P.card : ENNReal) := by gcongr <;> exact hcov_P_le_card
      _ = ENNReal.ofReal (C' * r ^ s * (P.card : ℝ)) := by
          have h_card : (P.card : ENNReal) = ENNReal.ofReal ((P.card : ℝ)) := by simp
          rw [h_card]
          rw [← ENNReal.ofReal_mul hC'_nonneg, ← ENNReal.ofReal_mul (mul_nonneg hC'_nonneg h_rpow_nonneg)] <;> ring
    have h_product_nonneg : 0 ≤ C' * r ^ s * (P.card : ℝ) := by positivity
    have h_card' : (S'.card : ENNReal) = ENNReal.ofReal ((S'.card : ℝ)) := by simp
    rw [h_card'] at h_main
    have h_final : (S'.card : ℝ) ≤ C' * r ^ s * (P.card : ℝ) := by
      exact (ENNReal.ofReal_le_ofReal_iff h_product_nonneg).mp h_main
    exact h_final
  exact ⟨hP_nonempty, hδ_pos, le_max_left _ _, hs_nonneg, hS_sep, h_ball_growth⟩

/-! ========================================================================
   Generalized packing-covering for δ/2-separated sets with δ-covering
   ======================================================================== -/

/-- Packing-covering inequality when separation scale is half the covering scale.
    If S is r-separated and 2r = δ, then |S| ≤ K_pack * covering_number(δ, S),
    provided every r-separated subset of a 2r-ball has size ≤ K_pack. -/
lemma separated_set_card_le_covering_half
    {X : Type*} [PseudoMetricSpace X] {r δ : NNReal} (h2r : 2 * r = δ)
    {S : Set X}
    (hS_sep : Set.Pairwise S (fun x y => (r : ℝ) ≤ dist x y))
    (K_pack : ℕ)
    (h_pack : ∀ (z : X) (T : Set X),
      Set.Pairwise T (fun x y => (r : ℝ) ≤ dist x y) →
      T ⊆ Metric.closedBall z (2 * (r : ℝ)) →
      T.Finite ∧ T.encard ≤ (K_pack : ENat))
    (hcov : (Metric.externalCoveringNumber δ S : ENNReal) < ⊤) :
    (S.encard : ENNReal) ≤ (K_pack : ENNReal) * (Metric.externalCoveringNumber δ S : ENNReal) := by
  classical
  have hcov' : Metric.externalCoveringNumber δ S < ⊤ := by exact_mod_cast hcov
  rcases DiscretisedFurstenbergEstimate.CoveringUtils.exists_external_cover_eq hcov' with ⟨C, hCcover, hC_eq⟩
  have hC_fin : C.Finite := by
    have h_lt : C.encard < ⊤ := by
      rw [hC_eq]
      exact hcov'
    exact Set.encard_lt_top_iff.mp h_lt
  let C' : Finset X := hC_fin.toFinset
  have hC'_eq : (C' : Set X) = C := hC_fin.coe_toFinset
  have hδ_eq_r : (δ : ℝ) = 2 * (r : ℝ) := by
    have h := congr_arg (fun x : NNReal => (x : ℝ)) h2r
    simpa using h.symm
  have h_each : ∀ c ∈ C', (S ∩ Metric.closedBall c (δ : ℝ)).Finite ∧
      (S ∩ Metric.closedBall c (δ : ℝ)).encard ≤ (K_pack : ENat) := by
    intro c hc
    let T := S ∩ Metric.closedBall c (δ : ℝ)
    have hT_subS : T ⊆ S := Set.inter_subset_left
    have hT_sep : Set.Pairwise T (fun x y => (r : ℝ) ≤ dist x y) := hS_sep.mono hT_subS
    have hT_sub : T ⊆ Metric.closedBall c (2 * (r : ℝ)) := by
      intro x hx
      have h1 : dist x c ≤ (δ : ℝ) := hx.2
      rw [hδ_eq_r] at h1
      exact h1
    exact h_pack c T hT_sep hT_sub
  let G : X → Finset X := fun c =>
    if h : c ∈ C' then (h_each c h).1.toFinset else ∅
  have hG_eq : ∀ (c : X) (hc : c ∈ C'), G c = (h_each c hc).1.toFinset := by
    intro c hc
    dsimp only [G]
    rw [dif_pos hc]
  have h_cover : S ⊆ ⋃ c ∈ (C' : Set X), S ∩ Metric.closedBall c (δ : ℝ) := by
    intro x hx
    have h10 : ∃ (c : X), c ∈ C ∧ edist x c ≤ ↑δ := hCcover hx
    rcases h10 with ⟨c, hc, hed⟩
    have hc' : c ∈ (C' : Set X) := by
      rw [hC'_eq] <;> exact hc
    have h11 : dist x c ≤ (δ : ℝ) := by
      simpa [edist_dist] using hed
    have h12 : x ∈ S ∩ Metric.closedBall c (δ : ℝ) := ⟨hx, h11⟩
    exact Set.mem_biUnion hc' h12
  let F : Finset X := C'.biUnion G
  have hF_sub : (S : Set X) ⊆ (F : Set X) := by
    intro x hx
    have h10 : ∃ (c : X), c ∈ C ∧ edist x c ≤ ↑δ := hCcover hx
    rcases h10 with ⟨c, hc, hed⟩
    have hc' : c ∈ (C' : Set X) := by
      rw [hC'_eq] <;> exact hc
    have h11 : dist x c ≤ (δ : ℝ) := by
      simpa [edist_dist] using hed
    have h12 : x ∈ S ∩ Metric.closedBall c (δ : ℝ) := ⟨hx, h11⟩
    have h13 : x ∈ (h_each c hc').1.toFinset := by simpa using h12
    have h14 : x ∈ G c := by rw [hG_eq c hc']; exact h13
    exact Finset.mem_biUnion.mpr ⟨c, hc', h14⟩
  have hS_fin : S.Finite := Set.Finite.subset (Finset.finite_toSet F) hF_sub
  let S' : Finset X := hS_fin.toFinset
  have hS'_eq : (S' : Set X) = S := hS_fin.coe_toFinset
  have hF_sub' : S' ⊆ F := by
    intro x hx
    have h_xinS : x ∈ S := by
      rw [←hS'_eq] <;> exact hx
    exact hF_sub h_xinS
  have h_card_F : F.card ≤ ∑ c ∈ C', (G c).card := by
    exact Finset.card_biUnion_le
  have h_main : S'.card ≤ K_pack * C'.card := by
    calc S'.card
      ≤ F.card := Finset.card_le_card hF_sub'
    _ ≤ ∑ c ∈ C', (G c).card := h_card_F
    _ ≤ ∑ c ∈ C', K_pack := by
      apply Finset.sum_le_sum
      intro c hc
      rw [hG_eq c hc]
      have h5 : (S ∩ Metric.closedBall c (δ : ℝ)).encard ≤ (K_pack : ENat) := (h_each c hc).2
      have h6 : ((h_each c hc).1.toFinset).card ≤ K_pack := by
        have h_fin : (S ∩ Metric.closedBall c (δ : ℝ)).Finite := (h_each c hc).1
        have h7 : (S ∩ Metric.closedBall c (δ : ℝ)).encard = ↑(h_fin.toFinset).card := by exact Set.Finite.encard_eq_coe_toFinset_card h_fin
        rw [h7] at h5
        exact_mod_cast h5
      exact h6
    _ = K_pack * C'.card := by
      simp [Finset.sum_const] <;> ring
  have h1 : (S.encard : ENNReal) = (S'.card : ENNReal) := by
    rw [←hS'_eq] <;> simp
  have h2 : (C'.card : ENNReal) = (Metric.externalCoveringNumber δ S : ENNReal) := by
    have h3 : (C'.card : ENat) = C.encard := by simp [←hC'_eq]
    have h4 : C.encard = Metric.externalCoveringNumber δ S := hC_eq
    have h5 : (C'.card : ENat) = Metric.externalCoveringNumber δ S := by
      rw [h3, h4]
    exact_mod_cast h5
  calc (S.encard : ENNReal)
    = (S'.card : ENNReal) := h1
  _ ≤ (K_pack : ENNReal) * (C'.card : ENNReal) := by exact_mod_cast h_main
  _ = (K_pack : ENNReal) * (Metric.externalCoveringNumber δ S : ENNReal) := by rw [h2]

/-- Convert IsDeltaSSet + SeparatedAt (δ/2) to BallGrowth at scale δ.
    Uses affineLine_packing_bound at scale δ/2 for the packing-covering step.
    Constant blows up by affineLine_packing_constant. -/
lemma IsDeltaSSet.to_ball_growth_half_separated
    {δ s C : ℝ} {P : Finset AffineLine}
    (h : IsDeltaSSet δ s C (P : Set AffineLine))
    (h_sep : SeparatedAt (δ / 2) (P : Set AffineLine)) :
    BallGrowth δ s (max 1 ((MainAppendix.affineLine_packing_constant : ℝ) * C)) P := by
  rcases h with ⟨hP_nonempty, hδ_pos, hC_pos, hs_nonneg, h_sset⟩
  let δnn : NNReal := δ.toNNReal
  let rnn : NNReal := (δ / 2).toNNReal
  have hδnn_eq : (δnn : ℝ) = δ := by
    have h : (δnn : ℝ) = max δ 0 := by rfl
    rw [h, max_eq_left hδ_pos.le]
  have h2pos : 0 ≤ δ / 2 := by linarith [hδ_pos]
  have hrnn_eq : (rnn : ℝ) = δ / 2 := by
    have h : (rnn : ℝ) = max (δ / 2) 0 := by rfl
    rw [h, max_eq_left h2pos]
  have h2r : 2 * rnn = δnn := by
    apply NNReal.coe_injective
    simp [hδnn_eq, hrnn_eq] <;> ring
  let K_pack := MainAppendix.affineLine_packing_constant
  have hS_sep : Set.Pairwise (P : Set AffineLine) (fun x y => (δ / 2 : ℝ) ≤ dist x y) := h_sep
  have hS_sep_nn : Set.Pairwise (P : Set AffineLine) (fun x y => (rnn : ℝ) ≤ dist x y) := by
    simpa [hrnn_eq] using hS_sep
  have h_pack' : ∀ (z : AffineLine) (T : Set AffineLine),
      Set.Pairwise T (fun x y => (rnn : ℝ) ≤ dist x y) →
      T ⊆ Metric.closedBall z (2 * (rnn : ℝ)) →
      T.Finite ∧ T.encard ≤ (K_pack : ENat) := by
    intro z T hT_sep hT_sub
    have hT_sep' : Set.Pairwise T (fun x y => (δ / 2 : ℝ) ≤ dist x y) := by
      simpa [hrnn_eq] using hT_sep
    have hT_sub' : T ⊆ Metric.closedBall z (2 * (δ / 2 : ℝ)) := by
      simpa [hrnn_eq] using hT_sub
    have hδ2_pos : 0 < δ / 2 := by linarith
    exact MainAppendix.affineLine_packing_bound (δ / 2) hδ2_pos hT_sep' z hT_sub'
  let C' := max 1 ((K_pack : ℝ) * C)
  have hC_one : 1 ≤ C' := le_max_left _ _
  have hC'_nonneg : 0 ≤ C' := by positivity
  have h_growth : ∀ (x : AffineLine) (r : ℝ), δ ≤ r →
      ((P.filter fun y => dist y x ≤ r).card : ℝ) ≤
        C' * r ^ s * (P.card : ℝ) := by
    intro x r hr
    let S' : Finset AffineLine := P.filter (fun y => dist y x ≤ r)
    have hS'_sub : (S' : Set AffineLine) ⊆ (P : Set AffineLine) := by
      intro y hy; exact (Finset.mem_filter.mp hy).1
    have hS'_sep : Set.Pairwise (S' : Set AffineLine) (fun x y => (rnn : ℝ) ≤ dist x y) :=
      hS_sep_nn.mono hS'_sub
    have hcov_fin : (Metric.externalCoveringNumber δnn (S' : Set AffineLine) : ENNReal) < ⊤ := by
      have h1 : (Metric.externalCoveringNumber δnn (S' : Set AffineLine) : ENNReal) ≤ (S'.card : ENNReal) := by
        exact_mod_cast Metric.externalCoveringNumber_le_encard_self (S' : Set AffineLine)
      have h2 : (S'.card : ENNReal) < ⊤ := by simp
      exact lt_of_le_of_lt h1 h2
    have h_pack_cover : (S'.card : ENNReal) ≤
        (K_pack : ENNReal) * (Metric.externalCoveringNumber δnn (S' : Set AffineLine) : ENNReal) := by
      have h : ((S' : Set AffineLine).encard : ENNReal) ≤
          (K_pack : ENNReal) * (Metric.externalCoveringNumber δnn (S' : Set AffineLine) : ENNReal) :=
        separated_set_card_le_covering_half h2r hS'_sep K_pack h_pack' hcov_fin
      have h_eq : ((S' : Set AffineLine).encard : ENNReal) = (S'.card : ENNReal) := by simp
      rw [h_eq] at h
      exact h
    have hS'_sub_P : (S' : Set AffineLine) ⊆ (P : Set AffineLine) ∩ Metric.closedBall x r := by
      intro y hy
      have h1 : y ∈ (P : Set AffineLine) := (Finset.mem_filter.mp hy).1
      have h2 : dist y x ≤ r := (Finset.mem_filter.mp hy).2
      exact ⟨h1, h2⟩
    have h_cov_mono : (Metric.externalCoveringNumber δnn (S' : Set AffineLine) : ENNReal) ≤
        (Metric.externalCoveringNumber δnn ((P : Set AffineLine) ∩ Metric.closedBall x r) : ENNReal) := by
      exact_mod_cast Metric.externalCoveringNumber_mono_set hS'_sub_P
    have h_sset' : (Metric.externalCoveringNumber δnn ((P : Set AffineLine) ∩ Metric.closedBall x r) : ENNReal) ≤
        ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * (Metric.externalCoveringNumber δnn (P : Set AffineLine) : ENNReal) :=
      h_sset x r hr
    have hcov_P_le_card : (Metric.externalCoveringNumber δnn (P : Set AffineLine) : ENNReal) ≤ (P.card : ENNReal) := by
      exact_mod_cast Metric.externalCoveringNumber_le_encard_self (P : Set AffineLine)
    have hr_nonneg : 0 ≤ r := by linarith
    have h_rpow_nonneg : 0 ≤ r ^ s := Real.rpow_nonneg hr_nonneg s
    have h_rpow : (ENNReal.ofReal r) ^ s = ENNReal.ofReal (r ^ s) := by
      rw [ENNReal.ofReal_rpow_of_nonneg hr_nonneg hs_nonneg]
    have h_main : (S'.card : ENNReal) ≤ ENNReal.ofReal (C' * r ^ s * (P.card : ℝ)) := by
      calc (S'.card : ENNReal)
        ≤ (K_pack : ENNReal) * (Metric.externalCoveringNumber δnn (S' : Set AffineLine) : ENNReal) := h_pack_cover
      _ ≤ (K_pack : ENNReal) * (Metric.externalCoveringNumber δnn ((P : Set AffineLine) ∩ Metric.closedBall x r) : ENNReal) := by gcongr
      _ ≤ (K_pack : ENNReal) * (ENNReal.ofReal C * ENNReal.ofReal (r ^ s) * (Metric.externalCoveringNumber δnn (P : Set AffineLine) : ENNReal)) := by
          rw [h_rpow] at h_sset' <;> gcongr
      _ = ENNReal.ofReal ((K_pack : ℝ)) * (ENNReal.ofReal C * ENNReal.ofReal (r ^ s) * (Metric.externalCoveringNumber δnn (P : Set AffineLine) : ENNReal)) := by simp
      _ = (ENNReal.ofReal ((K_pack : ℝ)) * ENNReal.ofReal C) * ENNReal.ofReal (r ^ s) * (Metric.externalCoveringNumber δnn (P : Set AffineLine) : ENNReal) := by ring
      _ = ENNReal.ofReal (((K_pack : ℝ) * C)) * ENNReal.ofReal (r ^ s) * (Metric.externalCoveringNumber δnn (P : Set AffineLine) : ENNReal) := by
          have h_pos1 : 0 ≤ (K_pack : ℝ) := by positivity
          rw [← ENNReal.ofReal_mul h_pos1] <;> ring
      _ ≤ ENNReal.ofReal C' * ENNReal.ofReal (r ^ s) * (Metric.externalCoveringNumber δnn (P : Set AffineLine) : ENNReal) := by
          have h9 : (K_pack : ℝ) * C ≤ C' := le_max_right _ _
          gcongr
      _ ≤ ENNReal.ofReal C' * ENNReal.ofReal (r ^ s) * (P.card : ENNReal) := by gcongr <;> exact hcov_P_le_card
      _ = ENNReal.ofReal (C' * r ^ s * (P.card : ℝ)) := by
          have h_card : (P.card : ENNReal) = ENNReal.ofReal ((P.card : ℝ)) := by simp
          rw [h_card]
          rw [← ENNReal.ofReal_mul hC'_nonneg, ← ENNReal.ofReal_mul (mul_nonneg hC'_nonneg h_rpow_nonneg)] <;> ring
    have h_product_nonneg : 0 ≤ C' * r ^ s * (P.card : ℝ) := by positivity
    have h_card' : (S'.card : ENNReal) = ENNReal.ofReal ((S'.card : ℝ)) := by simp
    rw [h_card'] at h_main
    have h_final : (S'.card : ℝ) ≤ C' * r ^ s * (P.card : ℝ) := by
      exact (ENNReal.ofReal_le_ofReal_iff h_product_nonneg).mp h_main
    exact h_final
  exact ⟨hP_nonempty, hδ_pos, hC_one, hs_nonneg, h_growth⟩

/-! ========================================================================
   Strip packing cardinality bound for C_Q
   ======================================================================== -/

/-- Given a Δ-separated family of coarse tubes each passing through a point
    in a fixed Δ-square (within the unit ball), bound its cardinality by
    Δ^{-1-5ε} using strip packing. -/
lemma strip_packing_card_upper
    {Δ δ ε : ℝ} {Q : CoarseSquare Δ}
    {P : Finset Plane} {T : Plane → Finset FineTube}
    {C_Q : Finset CoarseTube}
    (hΔ_pos : 0 < Δ) (hΔ_lt_half : Δ ≤ 1 / 2)
    (hδ_pos : 0 < δ) (hδ_le_Δ : δ ≤ Δ)
    (hε_pos : 0 < ε)
    (hstrip_loss : (42 : ℝ) * (40 * 4 + 110) ≤ Real.rpow Δ (-5 * ε))
    (hC_Q_sep : SeparatedAt Δ (C_Q : Set CoarseTube))
    (hC_Q_sub_U : C_Q ⊆ Finset.biUnion P T)
    (hP_in_square : (P : Set Plane) ⊆ squareSet Δ Q)
    (hP_y_bound : ∀ p ∈ P, |p 1| ≤ Real.sqrt 2)
    (h_slope_bound : ∀ p ∈ P, ∀ ℓ ∈ T p,
      (LemmaE.getDirV ℓ) 1 ≠ 0 ∧ |tubeSlope ℓ| ≤ 1 ∧ |tubeIntercept ℓ| ≤ 3)
    (h_inc : ∀ p ∈ P, ∀ ℓ ∈ T p, p ∈ Metric.cthickening (2 * δ) ℓ.1) :
    (C_Q.card : ℝ) ≤ Real.rpow Δ (-1 - 5 * ε) := by
  have hΔ_lt_one : Δ < 1 := by linarith
  have hS_v : ∀ ℓ ∈ C_Q, (LemmaE.getDirV ℓ) 1 ≠ 0 := by
    intro ℓ hℓ
    rcases Finset.mem_biUnion.mp (hC_Q_sub_U hℓ) with ⟨p, hp, hℓTp⟩
    exact (h_slope_bound p hp ℓ hℓTp).1
  have hS_a : ∀ ℓ ∈ C_Q, |tubeSlope ℓ| ≤ 1 := by
    intro ℓ hℓ
    rcases Finset.mem_biUnion.mp (hC_Q_sub_U hℓ) with ⟨p, hp, hℓTp⟩
    exact (h_slope_bound p hp ℓ hℓTp).2.1
  have hS_b : ∀ ℓ ∈ C_Q, |tubeIntercept ℓ| ≤ 3 := by
    intro ℓ hℓ
    rcases Finset.mem_biUnion.mp (hC_Q_sub_U hℓ) with ⟨p, hp, hℓTp⟩
    exact (h_slope_bound p hp ℓ hℓTp).2.2
  have h_strip : ∀ ℓ ∈ C_Q, ∃ (p : Plane), p ∈ squareSet Δ Q ∧ |p 1| ≤ Real.sqrt 2 ∧
      |tubeIntercept ℓ - (p 0 - tubeSlope ℓ * p 1)| ≤ 4 * Δ := by
    intro ℓ hℓ
    rcases Finset.mem_biUnion.mp (hC_Q_sub_U hℓ) with ⟨p, hp, hℓTp⟩
    have hpin_sq : p ∈ squareSet Δ Q := hP_in_square hp
    have hpy : |p 1| ≤ Real.sqrt 2 := hP_y_bound p hp
    have h_near : p ∈ Metric.cthickening (2 * δ) (ℓ.1 : Set Plane) := h_inc p hp ℓ hℓTp
    have h_res : |tubeIntercept ℓ - (p 0 - tubeSlope ℓ * p 1)| ≤ 4 * δ := by
      have h_tmp := TubesAndSlopes.near_point_intercept_bound_affine (by linarith) (hS_a ℓ hℓ) (hS_v ℓ hℓ) h_near
      have h_mul : (2 * (2 * δ) : ℝ) = 4 * δ := by ring
      simpa [tubeSlope, tubeIntercept, h_mul] using h_tmp
    have h_res2 : |tubeIntercept ℓ - (p 0 - tubeSlope ℓ * p 1)| ≤ 4 * Δ := by
      calc _ ≤ 4 * δ := h_res
           _ ≤ 4 * Δ := by gcongr <;> linarith
    exact ⟨p, hpin_sq, hpy, h_res2⟩
  have h_main : (C_Q.card : ℝ) ≤ (42 : ℝ) * (40 * (4 : ℝ) + 110) / Δ :=
    affineLine_strip_packing hΔ_pos hΔ_lt_one 4 (by norm_num) C_Q hC_Q_sep
      hS_v hS_a hS_b Q h_strip
  have h_loss : (42 : ℝ) * (40 * (4 : ℝ) + 110) / Δ ≤ Real.rpow Δ (-1 - 5 * ε) := by
    have h1 : (42 : ℝ) * (40 * (4 : ℝ) + 110) ≤ Real.rpow Δ (-5 * ε) := hstrip_loss
    have h2 : (42 : ℝ) * (40 * (4 : ℝ) + 110) / Δ =
        ((42 : ℝ) * (40 * (4 : ℝ) + 110)) * (1 / Δ) := by
      field_simp [hΔ_pos.ne'] <;> ring
    rw [h2]
    have h3 : (1 / Δ) = Real.rpow Δ (-1 : ℝ) := by
      have h4 : Real.rpow Δ (-1 : ℝ) = (Real.rpow Δ (1 : ℝ))⁻¹ := Real.rpow_neg hΔ_pos.le (1 : ℝ)
      have h5 : Real.rpow Δ (1 : ℝ) = Δ := by simp
      rw [h4, h5] <;> ring
    rw [h3]
    have h_rpow1_pos : 0 < Real.rpow Δ (-1 : ℝ) := Real.rpow_pos_of_pos hΔ_pos (-1 : ℝ)
    have h4 : ((42 : ℝ) * (40 * (4 : ℝ) + 110)) * Real.rpow Δ (-1 : ℝ) ≤
        Real.rpow Δ (-5 * ε) * Real.rpow Δ (-1 : ℝ) := by
      gcongr
    have h5 : Real.rpow Δ (-5 * ε) * Real.rpow Δ (-1 : ℝ) = Real.rpow Δ ((-5 * ε) + (-1 : ℝ)) := by
      exact (Real.rpow_add hΔ_pos (-5 * ε) (-1 : ℝ)).symm
    have h6 : (-5 * ε) + (-1 : ℝ) = -1 - 5 * ε := by ring
    rw [h5, h6] at h4
    exact h4
  exact h_main.trans h_loss

/-! ========================================================================
   A2 Per-Square QTTC Lemma
   ======================================================================== -/

/-- Smallness conditions for A2: all polylogarithmic QTTC constants are
    absorbed into negative powers of Δ. -/
structure A2_Smallness (Δ δ s t ε A K_pack M : ℝ) : Prop where
  hΔ_pos : 0 < Δ
  hΔ_lt_half : Δ ≤ 1 / 2
  hδ_le_Δ : δ ≤ Δ
  hA_pos : 0 < A
  hK_loss : 6 * A * Real.rpow (Real.log (2 / Δ)) A ≤ Real.rpow Δ (-ε)
  hK_loss_strong : 6 * A * Real.rpow (Real.log (2 / Δ)) A ≤ Real.rpow Δ (-2 * ε)
  hC2_loss : A * Real.rpow (A * Real.rpow (Real.log (2 / Δ)) A) A *
    (MainAppendix.affineLine_packing_constant : ℝ)^2 *
    max 1 (K_pack * Real.rpow δ (-ε)) ≤ Real.rpow Δ (-10 * ε)
  hstrip_loss : (42 : ℝ) * (40 * 4 + 110) ≤ Real.rpow Δ (-5 * ε)
  hKpack_loss : 6 * K_pack * Real.rpow Δ (-ε) ≤ Real.rpow Δ (-3 * ε)
  hKpack_loss_strong : 6 * K_pack ≤ Real.rpow Δ (-ε)
  hM_large : 2 ≤ Real.rpow Δ (-2 * s + 2 * ε) / K_pack
  hM_upper : max 1 ((MainAppendix.affineLine_packing_constant : ℝ) * max 1 (K_pack * Real.rpow δ (-ε))) * M ≤ Real.rpow Δ (-2 * s - 6 * ε)
  hKpack_const_ge1 : 1 ≤ (MainAppendix.affineLine_packing_constant : ℝ)
  hslope_sset_const : (1680000 : ℝ) ≤ Real.rpow Δ (-15 * ε)
  hcover_lower_pack : (2000 : ENNReal) * (affinePackingM : ENNReal) ≤
    ENNReal.ofReal (Real.rpow Δ (-14 * ε))

/-- Helper: prove `0 < ε` from strip packing smallness condition. -/
lemma a2_eps_pos {Δ ε : ℝ} (hΔ_pos : 0 < Δ) (hΔ_le_half : Δ ≤ 1 / 2)
    (hstrip_loss : (42 : ℝ) * (40 * 4 + 110) ≤ Real.rpow Δ (-5 * ε)) : 0 < ε := by
  by_contra h
  have hε' : ε ≤ 0 := le_of_not_gt h
  have h5ε : 0 ≤ -5 * ε :=
    mul_nonneg_of_nonpos_of_nonpos (show (-5 : ℝ) ≤ 0 from by norm_num) hε'
  have hΔ_le_one : Δ ≤ 1 := hΔ_le_half.trans (by norm_num)
  have h_rpow_le_one : Real.rpow Δ (-5 * ε) ≤ 1 :=
    Real.rpow_le_one hΔ_pos.le hΔ_le_one h5ε
  have h_const : (1 : ℝ) < (42 : ℝ) * (40 * 4 + 110) := by norm_num
  have h_contra : (42 : ℝ) * (40 * 4 + 110) ≤ 1 := hstrip_loss.trans h_rpow_le_one
  exact not_le.mpr h_const h_contra

/-- Helper: prove `Real.rpow Δ (2 * ε) ≤ K_Q` from smallness conditions. -/
lemma a2_K_Q_lower {Δ ε K K_Q : ℝ} (hΔ_pos : 0 < Δ) (hΔ_le_half : Δ ≤ 1 / 2)
    (hstrip_loss : (42 : ℝ) * (40 * 4 + 110) ≤ Real.rpow Δ (-5 * ε))
    (hK_one : 1 ≤ K) (hKQ_eq : K_Q = 6 * K) :
    Real.rpow Δ (2 * ε) ≤ K_Q := by
  have hε_pos : 0 < ε := by
    by_contra h
    have hε' : ε ≤ 0 := le_of_not_gt h
    have h5ε : 0 ≤ -5 * ε :=
      mul_nonneg_of_nonpos_of_nonpos (show (-5 : ℝ) ≤ 0 from by norm_num) hε'
    have hΔ_le_one : Δ ≤ 1 := hΔ_le_half.trans (by norm_num)
    have h_rpow_le_one : Real.rpow Δ (-5 * ε) ≤ 1 :=
      Real.rpow_le_one hΔ_pos.le hΔ_le_one h5ε
    have h_const : (1 : ℝ) < (42 : ℝ) * (40 * 4 + 110) := by norm_num
    have h_contra : (42 : ℝ) * (40 * 4 + 110) ≤ 1 := hstrip_loss.trans h_rpow_le_one
    exact not_le.mpr h_const h_contra
  have h2ε_nonneg : 0 ≤ 2 * ε :=
    mul_nonneg (show (0 : ℝ) ≤ 2 from by norm_num) (le_of_lt hε_pos)
  have hΔ_le_one : Δ ≤ 1 := hΔ_le_half.trans (by norm_num)
  have h1 : Real.rpow Δ (2 * ε) ≤ 1 :=
    Real.rpow_le_one hΔ_pos.le hΔ_le_one h2ε_nonneg
  have hK_nonneg : 0 ≤ K := by
    calc 0 ≤ 1 := by norm_num
      _ ≤ K := hK_one
  have h5 : (1 : ℝ) ≤ K_Q := by
    rw [hKQ_eq]
    have h7 : (1 : ℝ) ≤ K := hK_one
    have h8 : K ≤ 6 * K := by
      calc K = 1 * K := by ring
        _ ≤ 6 * K := by exact mul_le_mul_of_nonneg_right (by norm_num) hK_nonneg
    exact h7.trans h8
  exact h1.trans h5

/-- Helper: bound on assigned tubes per coarse tube. -/
lemma a2_per_coarse_upper (δ Δ s ε C₁ M : ℝ) (p : Plane)
    (T : Plane → Finset FineTube) (T_Q : Plane → Finset FineTube) (boldT : CoarseTube)
    (hδ_le_Δ : δ ≤ Δ) (hΔ_pos : 0 < Δ)
    (h_finite : BallGrowth δ s C₁ (T p))
    (hT_Q_sub : T_Q p ⊆ T p)
    (h_card : ((T p).card : ℝ) ≤ M)
    (hM_upper : C₁ * M ≤ Real.rpow Δ (-2 * s - 6 * ε)) :
    assignedCount Δ T_Q p boldT ≤ Real.rpow Δ (-s - 6 * ε) := by
  have h3 : ((T p).filter (fun ℓ => dist ℓ boldT ≤ Δ)).card ≤ C₁ * Δ ^ s * (T p).card :=
    h_finite.growth boldT Δ hδ_le_Δ
  have h4 : assignedCount Δ T_Q p boldT ≤ ((T p).filter (fun ℓ => dist ℓ boldT ≤ Δ)).card := by
    apply Finset.card_le_card
    intro ℓ hℓ
    have h5 : ℓ ∈ T_Q p := (Finset.mem_filter.mp hℓ).1
    have h6 : ℓ ∈ T p := hT_Q_sub h5
    have h7 : dist ℓ boldT ≤ Δ := (Finset.mem_filter.mp hℓ).2
    exact Finset.mem_filter.mpr ⟨h6, h7⟩
  have h5 : C₁ * Δ ^ s * ((T p).card : ℝ) ≤ C₁ * Δ ^ s * M := by
    have h6 : ((T p).card : ℝ) ≤ M := h_card
    have hC1 : 0 ≤ C₁ := by
      have h : 1 ≤ C₁ := h_finite.C_one
      linarith
    have hΔs : 0 ≤ Δ ^ s := by positivity
    have hpos : 0 ≤ C₁ * Δ ^ s := mul_nonneg hC1 hΔs
    exact mul_le_mul_of_nonneg_left h6 hpos
  have h7 : C₁ * M ≤ Real.rpow Δ (-2 * s - 6 * ε) := hM_upper
  calc (assignedCount Δ T_Q p boldT : ℝ)
    ≤ ↑((T p).filter (fun ℓ => dist ℓ boldT ≤ Δ)).card := by exact_mod_cast h4
  _ ≤ C₁ * Δ ^ s * ↑((T p).card) := h3
  _ ≤ C₁ * Δ ^ s * M := h5
  _ = (C₁ * M) * Δ ^ s := by ring
  _ ≤ Real.rpow Δ (-2 * s - 6 * ε) * Δ ^ s := by gcongr
  _ = Real.rpow Δ (-s - 6 * ε) := by
    have h9 : (Δ ^ s : ℝ) = Real.rpow Δ s := by rfl
    rw [h9]
    have h10 : Real.rpow Δ (-2 * s - 6 * ε) * Real.rpow Δ s = Real.rpow Δ ((-2 * s - 6 * ε) + s) :=
      (Real.rpow_add hΔ_pos (-2 * s - 6 * ε) s).symm
    rw [h10]
    have h11 : (-2 * s - 6 * ε) + s = -s - 6 * ε := by ring
    rw [h11]

/-- Helper: construct per-coarse upper bound in a clean context to avoid
    elaboration timeouts inside the huge a2_per_square theorem. -/
lemma a2_get_per_coarse_upper (δ Δ s ε C₁ M : ℝ)
    (P_Q : Finset Plane) (T_Q : Plane → Finset FineTube) (C_Q : Finset CoarseTube)
    (T : Plane → Finset FineTube) (P_sub : Finset Plane) (P : Finset Plane)
    (hP_Q_sub : P_Q ⊆ P_sub) (hP_sub_P : P_sub ⊆ P)
    (h_finite_sset : ∀ p ∈ P_sub, BallGrowth δ s C₁ (T p))
    (hT_Q_sub : ∀ p ∈ P_Q, T_Q p ⊆ T p)
    (h_tubes_card : ∀ p ∈ P, (T p).card ≥ M / 2 ∧ (T p).card ≤ M)
    (hδ_le_Δ : δ ≤ Δ) (hΔ_pos : 0 < Δ)
    (hM_upper : C₁ * M ≤ Real.rpow Δ (-2 * s - 6 * ε)) :
    ∀ p ∈ P_Q, ∀ boldT ∈ C_Q,
      assignedCount Δ T_Q p boldT ≤ Real.rpow Δ (-s - 6 * ε) := by
  intro p hp boldT hboldT
  have h1 : p ∈ P := hP_sub_P (hP_Q_sub hp)
  have h2 : p ∈ P_sub := hP_Q_sub hp
  exact a2_per_coarse_upper δ Δ s ε C₁ M p T T_Q boldT
    hδ_le_Δ hΔ_pos
    (h_finite_sset p h2) (hT_Q_sub p hp)
    (h_tubes_card p h1).2 hM_upper

/-- rpow arithmetic: simplify product/ratio of powers for H_Q lower bound. -/
lemma a2_rpow_H_bound (Δ s t ε K_pack : ℝ) (hΔ_pos : 0 < Δ)
    (hKpack : K_pack ≤ Real.rpow Δ (-2 * ε) / 6) (hKpack_pos : 0 < K_pack) :
    (Real.rpow Δ (-2 * s + 2 * ε) / K_pack) * Real.rpow Δ (-t + 3 * ε) /
      (Real.rpow Δ (-ε) * Real.rpow Δ (-s - 5 * ε)) ≥
    Real.rpow Δ (-s - t + 13 * ε) := by
  have h1 : Real.rpow Δ (-2 * s + 2 * ε) * Real.rpow Δ (-t + 3 * ε) =
      Real.rpow Δ (-2 * s - t + 5 * ε) := by
    have h_sum : (-2 * s + 2 * ε) + (-t + 3 * ε) = -2 * s - t + 5 * ε := by ring
    have h_add : Real.rpow Δ ((-2 * s + 2 * ε) + (-t + 3 * ε)) =
        Real.rpow Δ (-2 * s + 2 * ε) * Real.rpow Δ (-t + 3 * ε) := by
      simpa using Real.rpow_add hΔ_pos (-2 * s + 2 * ε) (-t + 3 * ε)
    rw [h_sum] at h_add
    exact h_add.symm
  have h2 : Real.rpow Δ (-ε) * Real.rpow Δ (-s - 5 * ε) =
      Real.rpow Δ (-s - 6 * ε) := by
    have h_sum : (-ε) + (-s - 5 * ε) = -s - 6 * ε := by ring
    have h_add : Real.rpow Δ ((-ε) + (-s - 5 * ε)) =
        Real.rpow Δ (-ε) * Real.rpow Δ (-s - 5 * ε) := by
      simpa using Real.rpow_add hΔ_pos (-ε) (-s - 5 * ε)
    rw [h_sum] at h_add
    exact h_add.symm
  have h3 : Real.rpow Δ (-2 * s - t + 5 * ε) / Real.rpow Δ (-s - 6 * ε) =
      Real.rpow Δ (-s - t + 11 * ε) := by
    have h_sum : (-s - t + 11 * ε) + (-s - 6 * ε) = -2 * s - t + 5 * ε := by ring
    have h_add : Real.rpow Δ ((-s - t + 11 * ε) + (-s - 6 * ε)) =
        Real.rpow Δ (-s - t + 11 * ε) * Real.rpow Δ (-s - 6 * ε) := by
      simpa using Real.rpow_add hΔ_pos (-s - t + 11 * ε) (-s - 6 * ε)
    have h_eq : Real.rpow Δ (-2 * s - t + 5 * ε) =
        Real.rpow Δ (-s - t + 11 * ε) * Real.rpow Δ (-s - 6 * ε) := by
      rw [h_sum] at h_add; exact h_add
    have h_pos : 0 < Real.rpow Δ (-s - 6 * ε) := Real.rpow_pos_of_pos hΔ_pos _
    have h_cancel : (Real.rpow Δ (-s - t + 11 * ε) * Real.rpow Δ (-s - 6 * ε)) / Real.rpow Δ (-s - 6 * ε) = Real.rpow Δ (-s - t + 11 * ε) := by
      exact mul_div_cancel_right₀ (Real.rpow Δ (-s - t + 11 * ε)) h_pos.ne'
    rw [h_eq]
    exact h_cancel
  have h_expr : (Real.rpow Δ (-2 * s + 2 * ε) / K_pack) * Real.rpow Δ (-t + 3 * ε) /
        (Real.rpow Δ (-ε) * Real.rpow Δ (-s - 5 * ε)) =
      Real.rpow Δ (-s - t + 11 * ε) / K_pack := by
    calc (Real.rpow Δ (-2 * s + 2 * ε) / K_pack) * Real.rpow Δ (-t + 3 * ε) /
          (Real.rpow Δ (-ε) * Real.rpow Δ (-s - 5 * ε))
      = (Real.rpow Δ (-2 * s + 2 * ε) * Real.rpow Δ (-t + 3 * ε)) /
          (K_pack * (Real.rpow Δ (-ε) * Real.rpow Δ (-s - 5 * ε))) := by ring
    _ = Real.rpow Δ (-2 * s - t + 5 * ε) / (K_pack * Real.rpow Δ (-s - 6 * ε)) := by
      rw [h1, h2] <;> ring
    _ = (Real.rpow Δ (-2 * s - t + 5 * ε) / Real.rpow Δ (-s - 6 * ε)) / K_pack := by ring
    _ = Real.rpow Δ (-s - t + 11 * ε) / K_pack := by rw [h3]
  rw [h_expr]
  have h_rpow2_pos : 0 < Real.rpow Δ (-2 * ε) := Real.rpow_pos_of_pos hΔ_pos _
  have h6 : (Real.rpow Δ (-2 * ε))⁻¹ = Real.rpow Δ (2 * ε) := by
    have h7 : Real.rpow Δ (-2 * ε) = (Real.rpow Δ (2 * ε))⁻¹ := by
      simpa using Real.rpow_neg hΔ_pos.le (2 * ε)
    rw [h7]; simp
  have h_inv : 1 / K_pack ≥ 6 * Real.rpow Δ (2 * ε) := by
    have h5 : 1 / K_pack ≥ 1 / (Real.rpow Δ (-2 * ε) / 6) := by gcongr
    have h8 : 1 / (Real.rpow Δ (-2 * ε) / 6) = 6 * Real.rpow Δ (2 * ε) := by
      have h9 : 1 / (Real.rpow Δ (-2 * ε) / 6) = 6 / Real.rpow Δ (-2 * ε) := by
        field_simp [h_rpow2_pos.ne'] <;> ring
      have h10 : 6 / Real.rpow Δ (-2 * ε) = 6 * (Real.rpow Δ (-2 * ε))⁻¹ := by
        field_simp [h_rpow2_pos.ne'] <;> ring
      rw [h9, h10, h6] <;> ring
    calc 1 / K_pack
      ≥ 1 / (Real.rpow Δ (-2 * ε) / 6) := h5
    _ = 6 * Real.rpow Δ (2 * ε) := h8
  have h9 : Real.rpow Δ (-s - t + 11 * ε) / K_pack =
      Real.rpow Δ (-s - t + 11 * ε) * (1 / K_pack) := by ring
  rw [h9]
  have h10 : 0 ≤ Real.rpow Δ (-s - t + 11 * ε) := Real.rpow_nonneg hΔ_pos.le _
  have h11 : Real.rpow Δ (-s - t + 11 * ε) * (1 / K_pack) ≥
      Real.rpow Δ (-s - t + 11 * ε) * (6 * Real.rpow Δ (2 * ε)) := by
    exact mul_le_mul_of_nonneg_left h_inv h10
  have h13 : Real.rpow Δ (-s - t + 11 * ε) * Real.rpow Δ (2 * ε) =
      Real.rpow Δ (-s - t + 13 * ε) := by
    have h_sum : (-s - t + 11 * ε) + (2 * ε) = -s - t + 13 * ε := by ring
    have h_add : Real.rpow Δ ((-s - t + 11 * ε) + (2 * ε)) =
        Real.rpow Δ (-s - t + 11 * ε) * Real.rpow Δ (2 * ε) := by
      simpa using Real.rpow_add hΔ_pos (-s - t + 11 * ε) (2 * ε)
    rw [h_sum] at h_add
    exact h_add.symm
  have h12 : Real.rpow Δ (-s - t + 11 * ε) * (6 * Real.rpow Δ (2 * ε)) =
      6 * Real.rpow Δ (-s - t + 13 * ε) := by
    have h14 : Real.rpow Δ (-s - t + 11 * ε) * (6 * Real.rpow Δ (2 * ε)) =
        6 * (Real.rpow Δ (-s - t + 11 * ε) * Real.rpow Δ (2 * ε)) := by ring
    rw [h14, h13] <;> ring
  rw [h12] at h11
  have h14 : 0 < Real.rpow Δ (-s - t + 13 * ε) := Real.rpow_pos_of_pos hΔ_pos _
  linarith

/-- rpow arithmetic: simplify ratio for C_Q card lower bound. -/
lemma a2_rpow_C_bound (Δ s ε K_pack : ℝ) (hΔ_pos : 0 < Δ)
    (hKpack : K_pack ≤ Real.rpow Δ (-2 * ε) / 6) (hKpack_pos : 0 < K_pack) :
    (Real.rpow Δ (-2 * s + 2 * ε) / K_pack) /
      (Real.rpow Δ (-ε) * Real.rpow Δ (-s - 6 * ε)) ≥
    Real.rpow Δ (-s + 11 * ε) := by
  have h1 : Real.rpow Δ (-ε) * Real.rpow Δ (-s - 6 * ε) =
      Real.rpow Δ (-s - 7 * ε) := by
    have h_sum : (-ε) + (-s - 6 * ε) = -s - 7 * ε := by ring
    have h_add : Real.rpow Δ ((-ε) + (-s - 6 * ε)) =
        Real.rpow Δ (-ε) * Real.rpow Δ (-s - 6 * ε) := by
      simpa using Real.rpow_add hΔ_pos (-ε) (-s - 6 * ε)
    rw [h_sum] at h_add
    exact h_add.symm
  have h2 : Real.rpow Δ (-2 * s + 2 * ε) / Real.rpow Δ (-s - 7 * ε) =
      Real.rpow Δ (-s + 9 * ε) := by
    have h_sum : (-s + 9 * ε) + (-s - 7 * ε) = -2 * s + 2 * ε := by ring
    have h_add : Real.rpow Δ ((-s + 9 * ε) + (-s - 7 * ε)) =
        Real.rpow Δ (-s + 9 * ε) * Real.rpow Δ (-s - 7 * ε) := by
      simpa using Real.rpow_add hΔ_pos (-s + 9 * ε) (-s - 7 * ε)
    have h_eq : Real.rpow Δ (-2 * s + 2 * ε) =
        Real.rpow Δ (-s + 9 * ε) * Real.rpow Δ (-s - 7 * ε) := by
      rw [h_sum] at h_add; exact h_add
    have h_pos : 0 < Real.rpow Δ (-s - 7 * ε) := Real.rpow_pos_of_pos hΔ_pos _
    have h_cancel : (Real.rpow Δ (-s + 9 * ε) * Real.rpow Δ (-s - 7 * ε)) / Real.rpow Δ (-s - 7 * ε) = Real.rpow Δ (-s + 9 * ε) := by
      exact mul_div_cancel_right₀ (Real.rpow Δ (-s + 9 * ε)) h_pos.ne'
    rw [h_eq]
    exact h_cancel
  have h_expr : (Real.rpow Δ (-2 * s + 2 * ε) / K_pack) /
        (Real.rpow Δ (-ε) * Real.rpow Δ (-s - 6 * ε)) =
      Real.rpow Δ (-s + 9 * ε) / K_pack := by
    calc (Real.rpow Δ (-2 * s + 2 * ε) / K_pack) /
          (Real.rpow Δ (-ε) * Real.rpow Δ (-s - 6 * ε))
      = Real.rpow Δ (-2 * s + 2 * ε) / (K_pack * (Real.rpow Δ (-ε) * Real.rpow Δ (-s - 6 * ε))) := by ring
    _ = Real.rpow Δ (-2 * s + 2 * ε) / (K_pack * Real.rpow Δ (-s - 7 * ε)) := by rw [h1]
    _ = (Real.rpow Δ (-2 * s + 2 * ε) / Real.rpow Δ (-s - 7 * ε)) / K_pack := by ring
    _ = Real.rpow Δ (-s + 9 * ε) / K_pack := by rw [h2]
  rw [h_expr]
  have h_rpow2_pos : 0 < Real.rpow Δ (-2 * ε) := Real.rpow_pos_of_pos hΔ_pos _
  have h6 : (Real.rpow Δ (-2 * ε))⁻¹ = Real.rpow Δ (2 * ε) := by
    have h7 : Real.rpow Δ (-2 * ε) = (Real.rpow Δ (2 * ε))⁻¹ := by
      simpa using Real.rpow_neg hΔ_pos.le (2 * ε)
    rw [h7]; simp
  have h_inv : 1 / K_pack ≥ 6 * Real.rpow Δ (2 * ε) := by
    have h5 : 1 / K_pack ≥ 1 / (Real.rpow Δ (-2 * ε) / 6) := by gcongr
    have h8 : 1 / (Real.rpow Δ (-2 * ε) / 6) = 6 * Real.rpow Δ (2 * ε) := by
      have h9 : 1 / (Real.rpow Δ (-2 * ε) / 6) = 6 / Real.rpow Δ (-2 * ε) := by
        field_simp [h_rpow2_pos.ne'] <;> ring
      have h10 : 6 / Real.rpow Δ (-2 * ε) = 6 * (Real.rpow Δ (-2 * ε))⁻¹ := by
        field_simp [h_rpow2_pos.ne'] <;> ring
      rw [h9, h10, h6] <;> ring
    calc 1 / K_pack
      ≥ 1 / (Real.rpow Δ (-2 * ε) / 6) := h5
    _ = 6 * Real.rpow Δ (2 * ε) := h8
  have h9 : Real.rpow Δ (-s + 9 * ε) / K_pack =
      Real.rpow Δ (-s + 9 * ε) * (1 / K_pack) := by ring
  rw [h9]
  have h10 : 0 ≤ Real.rpow Δ (-s + 9 * ε) := Real.rpow_nonneg hΔ_pos.le _
  have h11 : Real.rpow Δ (-s + 9 * ε) * (1 / K_pack) ≥
      Real.rpow Δ (-s + 9 * ε) * (6 * Real.rpow Δ (2 * ε)) := by
    exact mul_le_mul_of_nonneg_left h_inv h10
  have h13 : Real.rpow Δ (-s + 9 * ε) * Real.rpow Δ (2 * ε) =
      Real.rpow Δ (-s + 11 * ε) := by
    have h_sum : (-s + 9 * ε) + (2 * ε) = -s + 11 * ε := by ring
    have h_add : Real.rpow Δ ((-s + 9 * ε) + (2 * ε)) =
        Real.rpow Δ (-s + 9 * ε) * Real.rpow Δ (2 * ε) := by
      simpa using Real.rpow_add hΔ_pos (-s + 9 * ε) (2 * ε)
    rw [h_sum] at h_add
    exact h_add.symm
  have h12 : Real.rpow Δ (-s + 9 * ε) * (6 * Real.rpow Δ (2 * ε)) =
      6 * Real.rpow Δ (-s + 11 * ε) := by
    have h14 : Real.rpow Δ (-s + 9 * ε) * (6 * Real.rpow Δ (2 * ε)) =
        6 * (Real.rpow Δ (-s + 9 * ε) * Real.rpow Δ (2 * ε)) := by ring
    rw [h14, h13] <;> ring
  rw [h12] at h11
  have h14 : 0 < Real.rpow Δ (-s + 11 * ε) := Real.rpow_pos_of_pos hΔ_pos _
  linarith

/-- Helper: prove C_Q cardinality lower bound in a clean context. -/
lemma a2_C_card_lower (Δ s ε : ℝ) (M : ℝ) (P_card P_Q_card C_Q_card : ℕ)
    (K_Q H_Q K_pack : ℝ)
    (hΔ_pos : 0 < Δ)
    (h_balance : (M : ℝ) * (P_card : ℝ) ≤ K_Q * H_Q * (C_Q_card : ℝ))
    (hH_Q_upper : H_Q ≤ (P_Q_card : ℝ) * Real.rpow Δ (-s - 7 * ε))
    (hP_Q_le_P : P_Q_card ≤ P_card)
    (hM_lower : (M : ℝ) ≥ Real.rpow Δ (-2 * s + 2 * ε) / K_pack)
    (hK_Q_loss : K_Q ≤ Real.rpow Δ (-ε))
    (hKpack : K_pack ≤ Real.rpow Δ (-ε) / 6)
    (hKpack_pos : 0 < K_pack)
    (hK_Q_pos : 0 < K_Q)
    (hH_Q_pos : 0 < H_Q)
    (hP_pos : 0 < P_card) :
    Real.rpow Δ (-s + 11 * ε) ≤ (C_Q_card : ℝ) := by
  have hM_nonneg : 0 ≤ M := by
    have h_rpow_pos : 0 < Real.rpow Δ (-2 * s + 2 * ε) := Real.rpow_pos_of_pos hΔ_pos _
    have h_pos : 0 < Real.rpow Δ (-2 * s + 2 * ε) / K_pack := div_pos h_rpow_pos hKpack_pos
    linarith [hM_lower]
  have hP_card_nonneg : 0 ≤ (P_card : ℝ) := Nat.cast_nonneg _
  have hMP_nonneg : 0 ≤ M * (P_card : ℝ) := mul_nonneg hM_nonneg hP_card_nonneg
  have h1 : (C_Q_card : ℝ) ≥ M * (P_card : ℝ) / (K_Q * H_Q) := by
    have h_pos : 0 < K_Q * H_Q := mul_pos hK_Q_pos hH_Q_pos
    have h : M * (P_card : ℝ) ≤ K_Q * H_Q * (C_Q_card : ℝ) := h_balance
    have h2 : M * (P_card : ℝ) / (K_Q * H_Q) ≤ (K_Q * H_Q * (C_Q_card : ℝ)) / (K_Q * H_Q) := by
      exact div_le_div_of_nonneg_right h h_pos.le
    have h3 : (K_Q * H_Q * (C_Q_card : ℝ)) / (K_Q * H_Q) = (C_Q_card : ℝ) := by
      field_simp [h_pos.ne'] <;> ring
    rw [h3] at h2
    exact h2
  have h4 : H_Q ≤ (P_card : ℝ) * Real.rpow Δ (-s - 7 * ε) := by
    have h5 : (P_Q_card : ℝ) ≤ (P_card : ℝ) := by exact_mod_cast hP_Q_le_P
    have h6 : 0 ≤ Real.rpow Δ (-s - 7 * ε) := Real.rpow_nonneg hΔ_pos.le _
    calc H_Q
      ≤ (P_Q_card : ℝ) * Real.rpow Δ (-s - 7 * ε) := hH_Q_upper
    _ ≤ (P_card : ℝ) * Real.rpow Δ (-s - 7 * ε) := by gcongr
  have hD_pos : 0 < Real.rpow Δ (-s - 7 * ε) := Real.rpow_pos_of_pos hΔ_pos _
  have hP_card_pos : 0 < (P_card : ℝ) := by exact_mod_cast hP_pos
  have h5 : (C_Q_card : ℝ) ≥ M / (K_Q * Real.rpow Δ (-s - 7 * ε)) := by
    calc (C_Q_card : ℝ)
      ≥ M * (P_card : ℝ) / (K_Q * H_Q) := h1
    _ ≥ M * (P_card : ℝ) / (K_Q * ((P_card : ℝ) * Real.rpow Δ (-s - 7 * ε))) := by
      gcongr <;> exact hMP_nonneg
    _ = M / (K_Q * Real.rpow Δ (-s - 7 * ε)) := by
      field_simp [hP_card_pos.ne', hD_pos.ne'] <;> ring
  have hA_nonneg : 0 ≤ Real.rpow Δ (-2 * s + 2 * ε) / K_pack :=
    div_nonneg (Real.rpow_nonneg hΔ_pos.le _) hKpack_pos.le
  have h_denom_pos : 0 < K_Q * Real.rpow Δ (-s - 7 * ε) := mul_pos hK_Q_pos hD_pos
  have h_denom_step : (Real.rpow Δ (-2 * s + 2 * ε) / K_pack) / (K_Q * Real.rpow Δ (-s - 7 * ε)) ≥
      (Real.rpow Δ (-2 * s + 2 * ε) / K_pack) / (Real.rpow Δ (-ε) * Real.rpow Δ (-s - 7 * ε)) := by
    have h : K_Q * Real.rpow Δ (-s - 7 * ε) ≤ Real.rpow Δ (-ε) * Real.rpow Δ (-s - 7 * ε) := by
      exact mul_le_mul_of_nonneg_right hK_Q_loss hD_pos.le
    exact div_le_div_of_nonneg_left hA_nonneg h_denom_pos h
  have h_final : (Real.rpow Δ (-2 * s + 2 * ε) / K_pack) /
      (Real.rpow Δ (-ε) * Real.rpow Δ (-s - 7 * ε)) ≥ Real.rpow Δ (-s + 11 * ε) := by
    have h1 : Real.rpow Δ (-ε) * Real.rpow Δ (-s - 7 * ε) = Real.rpow Δ (-s - 8 * ε) := by
      have h_sum : (-ε) + (-s - 7 * ε) = -s - 8 * ε := by ring
      have h_add : Real.rpow Δ ((-ε) + (-s - 7 * ε)) =
          Real.rpow Δ (-ε) * Real.rpow Δ (-s - 7 * ε) := by
        simpa using Real.rpow_add hΔ_pos (-ε) (-s - 7 * ε)
      rw [h_sum] at h_add; exact h_add.symm
    rw [h1]
    have h2 : Real.rpow Δ (-2 * s + 2 * ε) / Real.rpow Δ (-s - 8 * ε) =
        Real.rpow Δ (-s + 10 * ε) := by
      have h_sum : (-s + 10 * ε) + (-s - 8 * ε) = -2 * s + 2 * ε := by ring
      have h_add : Real.rpow Δ ((-s + 10 * ε) + (-s - 8 * ε)) =
          Real.rpow Δ (-s + 10 * ε) * Real.rpow Δ (-s - 8 * ε) := by
        simpa using Real.rpow_add hΔ_pos (-s + 10 * ε) (-s - 8 * ε)
      have h_eq : Real.rpow Δ (-2 * s + 2 * ε) =
          Real.rpow Δ (-s + 10 * ε) * Real.rpow Δ (-s - 8 * ε) := by
        rw [h_sum] at h_add; exact h_add
      have h_pos : 0 < Real.rpow Δ (-s - 8 * ε) := Real.rpow_pos_of_pos hΔ_pos _
      have h_cancel : (Real.rpow Δ (-s + 10 * ε) * Real.rpow Δ (-s - 8 * ε)) / Real.rpow Δ (-s - 8 * ε) =
          Real.rpow Δ (-s + 10 * ε) := by
        exact mul_div_cancel_right₀ (Real.rpow Δ (-s + 10 * ε)) h_pos.ne'
      rw [h_eq]; exact h_cancel
    have h_pos8 : 0 < Real.rpow Δ (-s - 8 * ε) := Real.rpow_pos_of_pos hΔ_pos _
    have h_rearrange : (Real.rpow Δ (-2 * s + 2 * ε) / K_pack) / Real.rpow Δ (-s - 8 * ε) =
        (Real.rpow Δ (-2 * s + 2 * ε) / Real.rpow Δ (-s - 8 * ε)) / K_pack := by
      field_simp [hKpack_pos.ne', h_pos8.ne'] <;> ring
    rw [h_rearrange, h2]
    have h3 : Real.rpow Δ (-s + 10 * ε) / K_pack ≥ Real.rpow Δ (-s + 11 * ε) := by
      have h4 : K_pack ≤ Real.rpow Δ (-ε) / 6 := hKpack
      have h5 : 0 < K_pack := hKpack_pos
      have h_nonneg : 0 ≤ Real.rpow Δ (-s + 10 * ε) := Real.rpow_nonneg hΔ_pos.le _
      have h_denom_pos : 0 < Real.rpow Δ (-ε) / 6 :=
        div_pos (Real.rpow_pos_of_pos hΔ_pos _) (by norm_num)
      have h6 : Real.rpow Δ (-s + 10 * ε) / K_pack ≥
          Real.rpow Δ (-s + 10 * ε) / (Real.rpow Δ (-ε) / 6) :=
        div_le_div_of_nonneg_left h_nonneg h5 h4
      have h_pos_eps : 0 < Real.rpow Δ (-ε) := Real.rpow_pos_of_pos hΔ_pos _
      have h7 : Real.rpow Δ (-s + 10 * ε) / (Real.rpow Δ (-ε) / 6) =
          6 * Real.rpow Δ (-s + 11 * ε) := by
        have h_eq1 : Real.rpow Δ (-s + 10 * ε) / (Real.rpow Δ (-ε) / 6) =
            6 * Real.rpow Δ (-s + 10 * ε) / Real.rpow Δ (-ε) := by
          field_simp [h_pos_eps.ne'] <;> ring
        rw [h_eq1]
        have h_eq2 : Real.rpow Δ (-s + 10 * ε) =
            Real.rpow Δ (-s + 11 * ε) * Real.rpow Δ (-ε) := by
          have h_sum : (-s + 11 * ε) + (-ε) = -s + 10 * ε := by ring
          have h_add : Real.rpow Δ ((-s + 11 * ε) + (-ε)) =
              Real.rpow Δ (-s + 11 * ε) * Real.rpow Δ (-ε) := by
            simpa using Real.rpow_add hΔ_pos (-s + 11 * ε) (-ε)
          rw [h_sum] at h_add; exact h_add
        rw [h_eq2]
        field_simp [h_pos_eps.ne'] <;> ring
      have h8 : (6 : ℝ) * Real.rpow Δ (-s + 11 * ε) ≥ Real.rpow Δ (-s + 11 * ε) := by
        have h9 : (1 : ℝ) ≤ (6 : ℝ) := by norm_num
        exact le_mul_of_one_le_left (Real.rpow_nonneg hΔ_pos.le _) h9
      calc Real.rpow Δ (-s + 10 * ε) / K_pack
        ≥ Real.rpow Δ (-s + 10 * ε) / (Real.rpow Δ (-ε) / 6) := h6
      _ = 6 * Real.rpow Δ (-s + 11 * ε) := h7
      _ ≥ Real.rpow Δ (-s + 11 * ε) := h8
    exact h3
  calc (C_Q_card : ℝ)
    ≥ M / (K_Q * Real.rpow Δ (-s - 7 * ε)) := h5
  _ ≥ (Real.rpow Δ (-2 * s + 2 * ε) / K_pack) / (K_Q * Real.rpow Δ (-s - 7 * ε)) := by
    gcongr <;> exact hM_nonneg
  _ ≥ (Real.rpow Δ (-2 * s + 2 * ε) / K_pack) / (Real.rpow Δ (-ε) * Real.rpow Δ (-s - 7 * ε)) := h_denom_step
  _ ≥ Real.rpow Δ (-s + 11 * ε) := h_final

/-- Helper: prove H_Q lower bound in a clean context. -/
lemma a2_H_Q_lower (Δ s t ε M K K_Q K_pack H_Q : ℝ)
    (M_qttc : ℕ) (P_hi P : Finset Plane) (C_Q : Finset CoarseTube)
    (hK_pos : 0 < K) (hK_Q_pos : 0 < K_Q) (hKQ_eq : K_Q = 6 * K)
    (h_avg_lower : (M_qttc : ℝ) * (P_hi.card : ℝ) ≤ K * H_Q * (C_Q.card : ℝ))
    (hP_hi_large : P_hi.card * 2 ≥ P.card)
    (hM_le_mqttc : M ≤ (M_qttc : ℝ))
    (hC_Q_nonempty : C_Q.Nonempty)
    (hC_upper : (C_Q.card : ℝ) ≤ Real.rpow Δ (-s - 5 * ε))
    (hK_upper : K_Q ≤ Real.rpow Δ (-ε))
    (hM_lower : M ≥ Real.rpow Δ (-2 * s + 2 * ε) / K_pack)
    (hP_lower : Real.rpow Δ (-t + 3 * ε) ≤ (P.card : ℝ))
    (hKpack : K_pack ≤ Real.rpow Δ (-2 * ε) / 6)
    (hKpack_pos : 0 < K_pack)
    (hΔ_pos : 0 < Δ) :
    H_Q ≥ Real.rpow Δ (-s - t + 13 * ε) := by
  have h1 : H_Q * (C_Q.card : ℝ) ≥ (M_qttc : ℝ) * (P_hi.card : ℝ) / K := by
    have h2' : (M_qttc : ℝ) * (P_hi.card : ℝ) ≤ K * H_Q * (C_Q.card : ℝ) := h_avg_lower
    have h_eq : K * H_Q * (C_Q.card : ℝ) = K * (H_Q * (C_Q.card : ℝ)) := by ring
    have h2 : (M_qttc : ℝ) * (P_hi.card : ℝ) ≤ K * (H_Q * (C_Q.card : ℝ)) := by
      rw [h_eq] at h2'; exact h2'
    have h3 : (M_qttc : ℝ) * (P_hi.card : ℝ) / K ≤ (K * (H_Q * (C_Q.card : ℝ))) / K :=
      div_le_div_of_nonneg_right h2 hK_pos.le
    have h4 : (K * (H_Q * (C_Q.card : ℝ))) / K = H_Q * (C_Q.card : ℝ) := by
      field_simp [hK_pos.ne'] <;> ring
    rw [h4] at h3
    exact h3
  have hPcard_nonneg : 0 ≤ (P.card : ℝ) := Nat.cast_nonneg _
  have hP_hi_nonneg : 0 ≤ (P_hi.card : ℝ) := Nat.cast_nonneg _
  have hM_nonneg : 0 ≤ (M : ℝ) := by
    have h_rpow_pos : 0 < Real.rpow Δ (-2 * s + 2 * ε) := Real.rpow_pos_of_pos hΔ_pos _
    have h_pos : 0 < Real.rpow Δ (-2 * s + 2 * ε) / K_pack := div_pos h_rpow_pos hKpack_pos
    have h : (M : ℝ) ≥ Real.rpow Δ (-2 * s + 2 * ε) / K_pack := hM_lower
    linarith
  have hMqttc_nonneg : 0 ≤ (M_qttc : ℝ) := Nat.cast_nonneg _
  have h3 : (P.card : ℝ) ≤ 2 * (P_hi.card : ℝ) := by
    have h4 : (P_hi.card : ℝ) * 2 ≥ (P.card : ℝ) := by exact_mod_cast hP_hi_large
    linarith
  have hP_half : (P.card : ℝ) / 2 ≤ (P_hi.card : ℝ) := by linarith
  have h_two_pos : (0 : ℝ) < 2 := by norm_num
  have hP_half_nonneg : 0 ≤ (P.card : ℝ) / 2 := div_nonneg hPcard_nonneg h_two_pos.le
  have h_step1 : (M : ℝ) * ((P.card : ℝ) / 2) ≤ (M_qttc : ℝ) * ((P.card : ℝ) / 2) :=
    mul_le_mul_of_nonneg_right hM_le_mqttc hP_half_nonneg
  have h_step2 : (M_qttc : ℝ) * ((P.card : ℝ) / 2) ≤ (M_qttc : ℝ) * (P_hi.card : ℝ) :=
    mul_le_mul_of_nonneg_left hP_half hMqttc_nonneg
  have h_step : (M : ℝ) * ((P.card : ℝ) / 2) ≤ (M_qttc : ℝ) * (P_hi.card : ℝ) :=
    h_step1.trans h_step2
  have hCcard_pos : 0 < (C_Q.card : ℝ) := by
    exact_mod_cast hC_Q_nonempty.card_pos
  have h5 : H_Q ≥ (M : ℝ) * (P.card : ℝ) / (K_Q * (C_Q.card : ℝ)) := by
    have h6 : H_Q * (C_Q.card : ℝ) ≥ (M : ℝ) * (P.card : ℝ) / K_Q := by
      calc H_Q * (C_Q.card : ℝ)
        ≥ (M_qttc : ℝ) * (P_hi.card : ℝ) / K := h1
      _ ≥ (M : ℝ) * ((P.card : ℝ) / 2) / K :=
        div_le_div_of_nonneg_right h_step hK_pos.le
      _ = (M : ℝ) * (P.card : ℝ) / (2 * K) := by ring
      _ ≥ (M : ℝ) * (P.card : ℝ) / K_Q := by
        rw [hKQ_eq]
        have h7 : 0 < K := hK_pos
        have h8 : 0 ≤ (M : ℝ) * (P.card : ℝ) := mul_nonneg hM_nonneg hPcard_nonneg
        have h9 : (M : ℝ) * (P.card : ℝ) / (2 * K) ≥ (M : ℝ) * (P.card : ℝ) / (6 * K) := by
          have h10 : 0 < 2 * K := by positivity
          have h11 : 2 * K ≤ 6 * K := by linarith
          exact div_le_div_of_nonneg_left h8 h10 h11
        exact h9
    have h_pos2 : 0 < K_Q := hK_Q_pos
    have h8 : (H_Q * (C_Q.card : ℝ)) * K_Q ≥ (M : ℝ) * (P.card : ℝ) := by
      have h9 : (H_Q * (C_Q.card : ℝ)) * K_Q ≥ ((M : ℝ) * (P.card : ℝ) / K_Q) * K_Q := by
        exact mul_le_mul_of_nonneg_right h6 (by positivity)
      have h10 : ((M : ℝ) * (P.card : ℝ) / K_Q) * K_Q = (M : ℝ) * (P.card : ℝ) := by
        field_simp [h_pos2.ne'] <;> ring
      rw [h10] at h9
      exact h9
    have h11 : H_Q * (K_Q * (C_Q.card : ℝ)) ≥ (M : ℝ) * (P.card : ℝ) := by
      have h12 : H_Q * (K_Q * (C_Q.card : ℝ)) = (H_Q * (C_Q.card : ℝ)) * K_Q := by ring
      rw [h12]
      exact h8
    have h13 : 0 < K_Q * (C_Q.card : ℝ) := mul_pos h_pos2 hCcard_pos
    have h14 : H_Q ≥ (M : ℝ) * (P.card : ℝ) / (K_Q * (C_Q.card : ℝ)) := by
      have h_eq : (H_Q * (K_Q * (C_Q.card : ℝ))) / (K_Q * (C_Q.card : ℝ)) = H_Q := by
        field_simp [h13.ne']
      calc H_Q
        = (H_Q * (K_Q * (C_Q.card : ℝ))) / (K_Q * (C_Q.card : ℝ)) := h_eq.symm
      _ ≥ ((M : ℝ) * (P.card : ℝ)) / (K_Q * (C_Q.card : ℝ)) := by gcongr
    exact h14
  have hA_pos : 0 < Real.rpow Δ (-2 * s + 2 * ε) / K_pack :=
    div_pos (Real.rpow_pos_of_pos hΔ_pos _) hKpack_pos
  have hB_nonneg : 0 ≤ Real.rpow Δ (-t + 3 * ε) := Real.rpow_nonneg hΔ_pos.le _
  have hD1_pos : 0 < Real.rpow Δ (-ε) := Real.rpow_pos_of_pos hΔ_pos _
  have hD2_pos : 0 < Real.rpow Δ (-s - 5 * ε) := Real.rpow_pos_of_pos hΔ_pos _
  have h_num : (Real.rpow Δ (-2 * s + 2 * ε) / K_pack) * Real.rpow Δ (-t + 3 * ε) ≤
      (M : ℝ) * (P.card : ℝ) := by
    exact mul_le_mul hM_lower hP_lower hB_nonneg hM_nonneg
  have h_den : K_Q * (C_Q.card : ℝ) ≤
      Real.rpow Δ (-ε) * Real.rpow Δ (-s - 5 * ε) := by
    exact mul_le_mul hK_upper hC_upper hCcard_pos.le (by positivity)
  have h13 : 0 < K_Q * (C_Q.card : ℝ) := mul_pos hK_Q_pos hCcard_pos
  have h_pos2 : 0 < Real.rpow Δ (-ε) * Real.rpow Δ (-s - 5 * ε) := mul_pos hD1_pos hD2_pos
  have h_rpow_step : (M : ℝ) * (P.card : ℝ) / (K_Q * (C_Q.card : ℝ)) ≥
      (Real.rpow Δ (-2 * s + 2 * ε) / K_pack) * Real.rpow Δ (-t + 3 * ε) /
        (Real.rpow Δ (-ε) * Real.rpow Δ (-s - 5 * ε)) := by
    set AB := (Real.rpow Δ (-2 * s + 2 * ε) / K_pack) * Real.rpow Δ (-t + 3 * ε) with hAB_def
    have hAB_pos : 0 < AB := mul_pos hA_pos (Real.rpow_pos_of_pos hΔ_pos _)
    have h1 : AB / (K_Q * (C_Q.card : ℝ)) ≤ (M : ℝ) * (P.card : ℝ) / (K_Q * (C_Q.card : ℝ)) := by
      exact div_le_div_of_nonneg_right h_num h13.le
    have h2 : AB / (Real.rpow Δ (-ε) * Real.rpow Δ (-s - 5 * ε)) ≤ AB / (K_Q * (C_Q.card : ℝ)) := by
      exact div_le_div_of_nonneg_left hAB_pos.le h13 h_den
    exact le_trans h2 h1
  calc H_Q
    ≥ (M : ℝ) * (P.card : ℝ) / (K_Q * (C_Q.card : ℝ)) := h5
  _ ≥ (Real.rpow Δ (-2 * s + 2 * ε) / K_pack) * Real.rpow Δ (-t + 3 * ε) /
        (Real.rpow Δ (-ε) * Real.rpow Δ (-s - 5 * ε)) := h_rpow_step
  _ ≥ Real.rpow Δ (-s - t + 13 * ε) := a2_rpow_H_bound Δ s t ε K_pack hΔ_pos hKpack hKpack_pos

/-- Helper: P_lo branch ratio H_Q ≥ M*P.card/(K_Q*C_Q.card). -/
lemma a2_P_lo_ratio (Δ : ℝ) (M : ℝ) (M_qttc : ℕ) (P_lo P : Finset Plane)
    (C_Q : Finset CoarseTube) (K K_Q H_nat : ℝ) (H_Q : ℝ)
    (hK_one : 1 ≤ K) (hKQ_eq : K_Q = 6 * K)
    (h_avg_lower : (M_qttc : ℝ) * (P_lo.card : ℝ) ≤ K * H_nat * (C_Q.card : ℝ))
    (hH_Q_eq : H_Q = H_nat)
    (hP_lo_large : P_lo.card * 2 ≥ P.card)
    (hM_le_3Mqttc : (M : ℝ) ≤ 3 * (M_qttc : ℝ))
    (hC_Q_nonempty : C_Q.Nonempty)
    (hK_Q_pos : 0 < K_Q) :
    H_Q ≥ (M : ℝ) * (P.card : ℝ) / (K_Q * (C_Q.card : ℝ)) := by
  have hK_pos : 0 < K := by linarith
  have hC_pos : 0 < (C_Q.card : ℝ) := by exact_mod_cast hC_Q_nonempty.card_pos
  have h1 : H_Q * (C_Q.card : ℝ) ≥ (M_qttc : ℝ) * (P_lo.card : ℝ) / K := by
    have h2 : (M_qttc : ℝ) * (P_lo.card : ℝ) ≤ K * (H_Q * (C_Q.card : ℝ)) := by
      have h21 : (M_qttc : ℝ) * (P_lo.card : ℝ) ≤ K * H_nat * (C_Q.card : ℝ) := h_avg_lower
      have h22 : K * H_nat * (C_Q.card : ℝ) = K * (H_Q * (C_Q.card : ℝ)) := by
        rw [hH_Q_eq] <;> ring
      rw [h22] at h21
      exact h21
    have h3 : (M_qttc : ℝ) * (P_lo.card : ℝ) / K ≤ H_Q * (C_Q.card : ℝ) := by
      calc (M_qttc : ℝ) * (P_lo.card : ℝ) / K
        ≤ (K * (H_Q * (C_Q.card : ℝ))) / K := by gcongr
      _ = H_Q * (C_Q.card : ℝ) := by
        exact mul_div_cancel_left₀ (H_Q * (C_Q.card : ℝ)) hK_pos.ne'
    exact h3
  have hP_le : (P.card : ℝ) ≤ 2 * (P_lo.card : ℝ) := by
    have h41 : P.card ≤ 2 * P_lo.card := by omega
    exact_mod_cast h41
  have hM_div3 : (M : ℝ) / 3 ≤ (M_qttc : ℝ) := by linarith [hM_le_3Mqttc]
  have hP_div2 : (P.card : ℝ) / 2 ≤ (P_lo.card : ℝ) := by linarith [hP_le]
  have hMqttc_nonneg : 0 ≤ (M_qttc : ℝ) := Nat.cast_nonneg _
  have hPdiv2_nonneg : 0 ≤ (P.card : ℝ) / 2 := by positivity
  have h_mul : ((M : ℝ) / 3) * ((P.card : ℝ) / 2) ≤ (M_qttc : ℝ) * (P_lo.card : ℝ) :=
    mul_le_mul hM_div3 hP_div2 hPdiv2_nonneg hMqttc_nonneg
  have h6 : H_Q * (C_Q.card : ℝ) ≥ (M : ℝ) * (P.card : ℝ) / K_Q := by
    calc H_Q * (C_Q.card : ℝ)
      ≥ (M_qttc : ℝ) * (P_lo.card : ℝ) / K := h1
    _ ≥ ((M : ℝ) / 3) * ((P.card : ℝ) / 2) / K :=
      div_le_div_of_nonneg_right h_mul hK_pos.le
    _ = (M : ℝ) * (P.card : ℝ) / (6 * K) := by ring
    _ = (M : ℝ) * (P.card : ℝ) / K_Q := by rw [hKQ_eq]
  have h7 : 0 < K_Q * (C_Q.card : ℝ) := mul_pos hK_Q_pos hC_pos
  have h_eq : (H_Q * (C_Q.card : ℝ)) / (C_Q.card : ℝ) = H_Q := by
    field_simp [hC_pos.ne'] <;> ring
  calc H_Q
    = (H_Q * (C_Q.card : ℝ)) / (C_Q.card : ℝ) := h_eq.symm
  _ ≥ ((M : ℝ) * (P.card : ℝ) / K_Q) / (C_Q.card : ℝ) := by gcongr
  _ = (M : ℝ) * (P.card : ℝ) / (K_Q * (C_Q.card : ℝ)) := by ring

/-- Helper: from H_Q ≥ M*P.card/(K_Q*C_Q.card), derive the final H_Q lower bound. -/
lemma a2_H_Q_lower_from_ratio (Δ s t ε M P_card C_Q_card K_Q K_pack H_Q : ℝ)
    (hΔ_pos : 0 < Δ)
    (h5 : H_Q ≥ M * P_card / (K_Q * C_Q_card))
    (hC_upper : C_Q_card ≤ Real.rpow Δ (-s - 5 * ε))
    (hK_upper : K_Q ≤ Real.rpow Δ (-ε))
    (hM_lower : M ≥ Real.rpow Δ (-2 * s + 2 * ε) / K_pack)
    (hP_lower : Real.rpow Δ (-t + 3 * ε) ≤ P_card)
    (hKpack : K_pack ≤ Real.rpow Δ (-2 * ε) / 6)
    (hKpack_pos : 0 < K_pack)
    (hK_Q_pos : 0 < K_Q)
    (hCcard_pos : 0 < C_Q_card) :
    H_Q ≥ Real.rpow Δ (-s - t + 13 * ε) := by
  have hM_nonneg : 0 ≤ M := by
    have h_rpow_pos : 0 < Real.rpow Δ (-2 * s + 2 * ε) := Real.rpow_pos_of_pos hΔ_pos _
    have h_pos : 0 < Real.rpow Δ (-2 * s + 2 * ε) / K_pack := div_pos h_rpow_pos hKpack_pos
    have h : M ≥ Real.rpow Δ (-2 * s + 2 * ε) / K_pack := hM_lower
    linarith
  have hPcard_nonneg : 0 ≤ P_card := by
    have h : 0 ≤ Real.rpow Δ (-t + 3 * ε) := Real.rpow_nonneg hΔ_pos.le _
    linarith [hP_lower]
  have hA_pos : 0 < Real.rpow Δ (-2 * s + 2 * ε) / K_pack :=
    div_pos (Real.rpow_pos_of_pos hΔ_pos _) hKpack_pos
  have hB_nonneg : 0 ≤ Real.rpow Δ (-t + 3 * ε) := Real.rpow_nonneg hΔ_pos.le _
  have hD1_pos : 0 < Real.rpow Δ (-ε) := Real.rpow_pos_of_pos hΔ_pos _
  have hD2_pos : 0 < Real.rpow Δ (-s - 5 * ε) := Real.rpow_pos_of_pos hΔ_pos _
  have h_num : (Real.rpow Δ (-2 * s + 2 * ε) / K_pack) * Real.rpow Δ (-t + 3 * ε) ≤ M * P_card := by
    exact mul_le_mul hM_lower hP_lower hB_nonneg hM_nonneg
  have h_den : K_Q * C_Q_card ≤ Real.rpow Δ (-ε) * Real.rpow Δ (-s - 5 * ε) := by
    exact mul_le_mul hK_upper hC_upper hCcard_pos.le (by positivity)
  have h13 : 0 < K_Q * C_Q_card := mul_pos hK_Q_pos hCcard_pos
  have h_pos2 : 0 < Real.rpow Δ (-ε) * Real.rpow Δ (-s - 5 * ε) := mul_pos hD1_pos hD2_pos
  set AB := (Real.rpow Δ (-2 * s + 2 * ε) / K_pack) * Real.rpow Δ (-t + 3 * ε) with hAB_def
  have hAB_pos : 0 < AB := mul_pos hA_pos (Real.rpow_pos_of_pos hΔ_pos _)
  have h1 : AB / (K_Q * C_Q_card) ≤ M * P_card / (K_Q * C_Q_card) := by
    exact div_le_div_of_nonneg_right h_num h13.le
  have h2 : AB / (Real.rpow Δ (-ε) * Real.rpow Δ (-s - 5 * ε)) ≤ AB / (K_Q * C_Q_card) := by
    exact div_le_div_of_nonneg_left hAB_pos.le h13 h_den
  have h_rpow_step : M * P_card / (K_Q * C_Q_card) ≥ AB / (Real.rpow Δ (-ε) * Real.rpow Δ (-s - 5 * ε)) :=
    le_trans h2 h1
  calc H_Q
    ≥ M * P_card / (K_Q * C_Q_card) := h5
  _ ≥ AB / (Real.rpow Δ (-ε) * Real.rpow Δ (-s - 5 * ε)) := h_rpow_step
  _ ≥ Real.rpow Δ (-s - t + 13 * ε) := a2_rpow_H_bound Δ s t ε K_pack hΔ_pos hKpack hKpack_pos

/-- Transfer IsDeltaSSet from a set S to a subset S' with a factor D,
    given that N_δ(S) ≤ D * N_δ(S'). -/
lemma IsDeltaSSet.transfer_subset {X : Type*} [PseudoMetricSpace X]
    {δ s C : ℝ} {S S' : Set X}
    (hS : IsDeltaSSet δ s C S)
    (hS'_sub : S' ⊆ S)
    {D : ℝ} (hD_pos : 0 < D)
    (h_factor : (Metric.externalCoveringNumber δ.toNNReal S : ENNReal) ≤
               ENNReal.ofReal D * (Metric.externalCoveringNumber δ.toNNReal S')) :
    IsDeltaSSet δ s (D * C) S' := by
  rcases hS with ⟨hS_nonempty, hδ_pos, hC_pos, hs_nonneg, h_main⟩
  have hDC_pos : 0 < D * C := mul_pos hD_pos hC_pos
  have hS'_nonempty : S'.Nonempty := by
    by_contra h
    have h_empty : S' = ∅ := by simpa [Set.not_nonempty_iff_eq_empty] using h
    rw [h_empty] at h_factor
    have h_z : (Metric.externalCoveringNumber δ.toNNReal S : ENNReal) ≤ 0 := by
      simpa [Metric.externalCoveringNumber_empty] using h_factor
    have h_z' : (Metric.externalCoveringNumber δ.toNNReal S : ENNReal) = 0 := by
      simpa using h_z
    have h_eq : Metric.externalCoveringNumber δ.toNNReal S = 0 := by
      exact_mod_cast h_z'
    have hS_empty : S = ∅ := Metric.externalCoveringNumber_eq_zero.mp h_eq
    exact hS_nonempty.ne_empty hS_empty
  refine' ⟨hS'_nonempty, hδ_pos, hDC_pos, hs_nonneg, _⟩
  intro x r hr
  have h1 : (Metric.externalCoveringNumber δ.toNNReal (S' ∩ Metric.closedBall x r) : ENNReal) ≤
      (Metric.externalCoveringNumber δ.toNNReal (S ∩ Metric.closedBall x r) : ENNReal) := by
    exact_mod_cast Metric.externalCoveringNumber_mono_set (by gcongr)
  have h2 := h_main x r hr
  set N' := Metric.externalCoveringNumber δ.toNNReal S' with hN'_def
  have h_mul : ENNReal.ofReal C * ENNReal.ofReal D = ENNReal.ofReal (D * C) := by
    have hC_nonneg : 0 ≤ C := by linarith
    have h : ENNReal.ofReal C * ENNReal.ofReal D = ENNReal.ofReal (C * D) :=
      (ENNReal.ofReal_mul hC_nonneg).symm
    rw [h, mul_comm C D]
  calc
    (Metric.externalCoveringNumber δ.toNNReal (S' ∩ Metric.closedBall x r) : ENNReal)
      ≤ Metric.externalCoveringNumber δ.toNNReal (S ∩ Metric.closedBall x r) := h1
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
          Metric.externalCoveringNumber δ.toNNReal S := h2
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * (ENNReal.ofReal D * N') := by gcongr
    _ = (ENNReal.ofReal C * ENNReal.ofReal D) * (ENNReal.ofReal r) ^ s * N' := by
      have h_alg : ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * (ENNReal.ofReal D * N') =
          (ENNReal.ofReal C * ENNReal.ofReal D) * (ENNReal.ofReal r) ^ s * N' := by
        simp [mul_assoc, mul_comm, mul_left_comm]
      exact h_alg
    _ = ENNReal.ofReal (D * C) * (ENNReal.ofReal r) ^ s * N' := by rw [h_mul]

/-- Helper: transfer IsDeltaSSet from original tube family to QTTC-refined subset.
    Uses covering ≤ card, QTTC refinement, and affine packing bound (half-separation). -/
lemma a2_transfer_tube_sset
    {δ s C K_Q M : ℝ} {p : Plane}
    {T : Plane → Finset FineTube} {T_Q : Plane → Finset FineTube}
    (hδ_pos : 0 < δ)
    (hC_pos : 0 < C)
    (hK_Q_pos : 0 < K_Q)
    (hM_pos : 0 < M)
    (h_pack_pos : 0 < (MainAppendix.affineLine_packing_constant : ℝ))
    (h_orig_sset : IsDeltaSSet δ s C (T p : Set FineTube))
    (h_sub : (T_Q p : Set FineTube) ⊆ (T p : Set FineTube))
    (h_sep : SeparatedAt (δ / 2) (T_Q p : Set FineTube))
    (h_card_Tp : (T p).card ≤ M)
    (h_refine : (M : ℝ) ≤ K_Q * ((T_Q p).card : ℝ)) :
    IsDeltaSSet δ s (C * K_Q * (MainAppendix.affineLine_packing_constant : ℝ)) (T_Q p : Set FineTube) := by
  let D := K_Q * (MainAppendix.affineLine_packing_constant : ℝ)
  have hD_pos : 0 < D := mul_pos hK_Q_pos h_pack_pos
  let δnn : NNReal := δ.toNNReal
  let rnn : NNReal := (δ / 2).toNNReal
  have hδnn_eq : (δnn : ℝ) = δ := by
    have h : (δnn : ℝ) = max δ 0 := by rfl
    rw [h, max_eq_left hδ_pos.le]
  have h2pos : 0 ≤ δ / 2 := by linarith [hδ_pos]
  have hrnn_eq : (rnn : ℝ) = δ / 2 := by
    have h : (rnn : ℝ) = max (δ / 2) 0 := by rfl
    rw [h, max_eq_left h2pos]
  have h2r : 2 * rnn = δnn := by
    apply NNReal.coe_injective
    simp [hδnn_eq, hrnn_eq] <;> ring
  have hM_nonneg : 0 ≤ M := by linarith
  have hKQ_nonneg : 0 ≤ K_Q := by linarith
  have h_factor : (Metric.externalCoveringNumber δnn (T p : Set FineTube) : ENNReal) ≤
      ENNReal.ofReal D * Metric.externalCoveringNumber δnn (T_Q p : Set FineTube) := by
    have h1 : (Metric.externalCoveringNumber δnn (T p : Set FineTube) : ENNReal) ≤
        ((T p).card : ENNReal) := by
      have h11 : Metric.externalCoveringNumber δnn (T p : Set FineTube) ≤
          (T p : Set FineTube).encard := Metric.externalCoveringNumber_le_encard_self _
      have h12 : (T p : Set FineTube).encard = ↑(T p).card := by simp
      rw [h12] at h11
      exact_mod_cast h11
    have h2 : ((T p).card : ENNReal) ≤ ENNReal.ofReal M := by
      have h21 : ((T p).card : ℝ) ≤ M := h_card_Tp
      have h22 : ((T p).card : ENNReal) = ENNReal.ofReal ((T p).card : ℝ) := by simp
      rw [h22]
      exact ENNReal.ofReal_le_ofReal h21
    have h3 : ENNReal.ofReal M ≤ ENNReal.ofReal K_Q * ((T_Q p).card : ENNReal) := by
      have h31 : (M : ℝ) ≤ K_Q * ((T_Q p).card : ℝ) := h_refine
      have h32 : ((T_Q p).card : ENNReal) = ENNReal.ofReal ((T_Q p).card : ℝ) := by simp
      rw [h32]
      have h33 : ENNReal.ofReal M ≤ ENNReal.ofReal (K_Q * ((T_Q p).card : ℝ)) :=
        ENNReal.ofReal_le_ofReal h31
      have h34 : ENNReal.ofReal (K_Q * ((T_Q p).card : ℝ)) =
          ENNReal.ofReal K_Q * ENNReal.ofReal ((T_Q p).card : ℝ) := by
        rw [ENNReal.ofReal_mul hKQ_nonneg] <;> rfl
      rw [h34] at h33
      exact h33
    have h_pack_arg : ∀ (z : AffineLine) (T : Set AffineLine),
        Set.Pairwise T (fun x y => (rnn : ℝ) ≤ dist x y) →
        T ⊆ Metric.closedBall z (2 * (rnn : ℝ)) →
        T.Finite ∧ T.encard ≤ (MainAppendix.affineLine_packing_constant : ENat) := by
      intro z T hsep hsub
      have hsep' : Set.Pairwise T (fun x y => (δ / 2 : ℝ) ≤ dist x y) := by
        simpa [hrnn_eq] using hsep
      have hsub' : T ⊆ Metric.closedBall z (2 * (δ / 2 : ℝ)) := by
        simpa [hrnn_eq] using hsub
      have hδ2_pos : 0 < δ / 2 := by linarith
      exact MainAppendix.affineLine_packing_bound (δ / 2) hδ2_pos hsep' z hsub'
    have h_sep' : Set.Pairwise (T_Q p : Set FineTube) (fun x y => (rnn : ℝ) ≤ dist x y) := by
      intro x hx y hy hne
      have h : (δ / 2 : ℝ) ≤ dist x y := h_sep hx hy hne
      have h' : (rnn : ℝ) ≤ dist x y := by
        rw [hrnn_eq]
        exact h
      exact h'
    have hcov_fin : (Metric.externalCoveringNumber δnn (T_Q p : Set FineTube) : ENNReal) < ⊤ := by
      have h : Metric.externalCoveringNumber δnn (T_Q p : Set FineTube) ≤
          (T_Q p : Set FineTube).encard := Metric.externalCoveringNumber_le_encard_self _
      have h' : (Metric.externalCoveringNumber δnn (T_Q p : Set FineTube) : ENNReal) ≤
          ((T_Q p).card : ENNReal) := by
        have h2 : (T_Q p : Set FineTube).encard = ↑(T_Q p).card := by simp
        rw [h2] at h
        exact_mod_cast h
      exact h'.trans_lt (ENNReal.coe_lt_top)
    have h4 : ((T_Q p : Set FineTube).encard : ENNReal) ≤
        (MainAppendix.affineLine_packing_constant : ENNReal) *
        Metric.externalCoveringNumber δnn (T_Q p : Set FineTube) :=
      separated_set_card_le_covering_half h2r h_sep'
        MainAppendix.affineLine_packing_constant h_pack_arg hcov_fin
    have h5 : ((T_Q p).card : ENNReal) = ((T_Q p : Set FineTube).encard : ENNReal) := by simp
    have h6 : ((T_Q p).card : ENNReal) ≤
        (MainAppendix.affineLine_packing_constant : ENNReal) *
        Metric.externalCoveringNumber δnn (T_Q p : Set FineTube) := by
      rw [h5] <;> exact h4
    have hD_eq : ENNReal.ofReal D =
        ENNReal.ofReal K_Q * (MainAppendix.affineLine_packing_constant : ENNReal) := by
      have h1 : ENNReal.ofReal D =
          ENNReal.ofReal K_Q * ENNReal.ofReal (MainAppendix.affineLine_packing_constant : ℝ) := by
        rw [ENNReal.ofReal_mul hKQ_nonneg] <;> rfl
      rw [h1]
      have h2 : ENNReal.ofReal (MainAppendix.affineLine_packing_constant : ℝ) =
          (MainAppendix.affineLine_packing_constant : ENNReal) := by simp
      rw [h2]
    calc
      (Metric.externalCoveringNumber δnn (T p : Set FineTube) : ENNReal)
        ≤ ((T p).card : ENNReal) := h1
      _ ≤ ENNReal.ofReal M := h2
      _ ≤ ENNReal.ofReal K_Q * ((T_Q p).card : ENNReal) := h3
      _ ≤ ENNReal.ofReal K_Q * ((MainAppendix.affineLine_packing_constant : ENNReal) *
            Metric.externalCoveringNumber δnn (T_Q p : Set FineTube)) := by gcongr
      _ = ENNReal.ofReal D * Metric.externalCoveringNumber δnn (T_Q p : Set FineTube) := by
        rw [hD_eq] <;> simp [mul_assoc]
  have h_result : IsDeltaSSet δ s (D * C) (T_Q p : Set FineTube) :=
    IsDeltaSSet.transfer_subset h_orig_sset h_sub hD_pos h_factor
  have hDC_eq : D * C = C * K_Q * (MainAppendix.affineLine_packing_constant : ℝ) := by
    dsimp only [D] <;> ring
  rw [hDC_eq] at h_result
  exact h_result

end DirecretisedFurstenbergEstimate.AppendixA.A2
