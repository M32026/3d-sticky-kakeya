module

/-
  Cardinality lower bound for tube families from S-set property.

  Given a (δ,s,C)-set T of AffineLines:
  1. Ncover_δ(T) ≥ C^{-1} · δ^{-s} (from S-set at r=δ)
  2. A maximal δ-separated subset S has |S| ≥ Ncover_δ(T)
  3. Therefore |S| ≥ C^{-1} · δ^{-s}

  The extracted S is also a (δ, s, max 1 (K_pack * C))-set.

  Whiteprint node: improved_incidence_general / b1_metric_to_dyadic / cardinality_lower_bound
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FiniteSeparatedTubes
public import MyLeanRepo.DiscretisedFurstenbergEstimate.PackingBound
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal


noncomputable section

namespace ImprovedIncidenceAssembly

open DirecretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate

/-- Lower bound on the δ-covering number of a (δ,s,C)-set.

    From the S-set condition at r=δ, any point x ∈ T gives:
    1 ≤ cov_δ(T ∩ B(x,δ)) ≤ C · δ^s · cov_δ(T)
    Hence cov_δ(T) ≥ (C · δ^s)⁻¹. -/
lemma sset_ncover_lower_bound {δ s C : ℝ} {X : Type*} [PseudoMetricSpace X]
    {T : Set X} (hT_sset : IsDeltaSSet δ s C T) :
    ENNReal.ofReal ((C * δ^s)⁻¹) ≤
      (Metric.externalCoveringNumber δ.toNNReal T : ENNReal) := by
  rcases hT_sset with ⟨hT_nonempty, hδ_pos, hC_pos, hs_nonneg, h_sset⟩
  rcases hT_nonempty with ⟨x, hx⟩
  have hδ_nonneg : 0 ≤ δ := by linarith
  have h_inter_nonempty : (T ∩ Metric.closedBall x δ).Nonempty :=
    ⟨x, ⟨hx, by simp [Metric.mem_closedBall, hδ_nonneg]⟩⟩
  have h_singleton : ({x} : Set X) ⊆ T ∩ Metric.closedBall x δ := by
    simp [hx, hδ_nonneg, Metric.mem_closedBall]
  have h1 : (1 : ENNReal) ≤
      (Metric.externalCoveringNumber δ.toNNReal (T ∩ Metric.closedBall x δ) : ENNReal) := by
    have h2 : Metric.externalCoveringNumber δ.toNNReal ({x} : Set X) ≤
        Metric.externalCoveringNumber δ.toNNReal (T ∩ Metric.closedBall x δ) :=
      Metric.externalCoveringNumber_mono_set h_singleton
    have h3 : Metric.externalCoveringNumber δ.toNNReal ({x} : Set X) = 1 :=
      Metric.externalCoveringNumber_singleton δ.toNNReal x
    rw [h3] at h2
    exact_mod_cast h2
  have h2 := h_sset x δ (by linarith)
  have h3 : (1 : ENNReal) ≤
      ENNReal.ofReal C * (ENNReal.ofReal δ) ^ s *
        (Metric.externalCoveringNumber δ.toNNReal T : ENNReal) :=
    le_trans h1 h2
  have h41 : (ENNReal.ofReal δ) ^ s = ENNReal.ofReal (δ ^ s) :=
    ENNReal.ofReal_rpow_of_pos hδ_pos
  have h4 : ENNReal.ofReal C * (ENNReal.ofReal δ) ^ s = ENNReal.ofReal (C * δ ^ s) := by
    rw [h41, ← ENNReal.ofReal_mul (by positivity)] <;> rfl
  rw [h4] at h3
  set a : ENNReal := ENNReal.ofReal (C * δ ^ s) with ha_def
  have ha_pos : 0 < C * δ ^ s := by positivity
  have ha_ne_zero : a ≠ 0 := by positivity
  have ha_ne_top : a ≠ ⊤ := by simp [a, ha_def]
  set b : ENNReal := (Metric.externalCoveringNumber δ.toNNReal T : ENNReal) with hb_def
  have h6 : 1 ≤ a * b := h3
  have h7 : a⁻¹ ≤ b := by
    have h8 : a⁻¹ * 1 ≤ a⁻¹ * (a * b) := by gcongr
    have h9 : a⁻¹ * (a * b) = b := by
      calc a⁻¹ * (a * b)
        = (a⁻¹ * a) * b := by rw [mul_assoc]
      _ = 1 * b := by rw [ENNReal.inv_mul_cancel ha_ne_zero ha_ne_top]
      _ = b := by simp
    rw [h9] at h8
    simpa using h8
  have h10 : a⁻¹ = ENNReal.ofReal ((C * δ ^ s)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos ha_pos] <;> rfl
  rw [h10] at h7
  exact h7

/-- Extract a finite δ-separated subset S from a bounded (δ,s,C)-set T,
    with cardinality lower bound |S| ≥ Ncover_δ(T).

    The extracted S is a maximal δ-separated subset, so its δ-balls cover T.
    S is also a (δ, s, max 1 (K_pack * C))-set. -/
lemma extract_finite_tube_sset_with_card
    {δ s C : ℝ} {T : Set AffineLine}
    (hT_sset : IsDeltaSSet δ s C T)
    (hT_bdd : Bornology.IsBounded T) :
    ∃ (S : Finset AffineLine),
      (S : Set AffineLine) ⊆ T ∧
      S.Nonempty ∧
      Set.Pairwise (S : Set AffineLine) (fun x y => δ ≤ dist x y) ∧
      IsDeltaSSet δ s (max 1 (MainAppendix.affineLine_packing_constant * C)) (S : Set AffineLine) ∧
      (Metric.externalCoveringNumber δ.toNNReal T : ENNReal) ≤ (S.card : ENNReal) := by
  -- Reuse the proof structure from extract_finite_tube_sset
  rcases hT_sset with ⟨hT_nonempty, hδ_pos, hC_pos, hs_nonneg, h_sset⟩
  let K_pack := MainAppendix.affineLine_packing_constant
  let δnn : NNReal := δ.toNNReal
  have hδnn_eq : (δnn : ℝ) = δ := by
    simp [δnn, Real.toNNReal_of_nonneg hδ_pos.le]

  have hT_tb : TotallyBounded T := affineLine_bounded_totallyBounded hT_bdd

  have hε_pos : 0 < (δnn / 2 : ℝ) := by
    have h' : 0 < (δnn : ℝ) := by rw [hδnn_eq] <;> exact hδ_pos
    exact half_pos h'
  let d : Set (AffineLine × AffineLine) := {p | dist p.1 p.2 < (δnn / 2 : ℝ)}
  have h_uniform : d ∈ uniformity AffineLine := Metric.dist_mem_uniformity hε_pos
  have h1 : ∃ (t : Set AffineLine), t.Finite ∧ T ⊆ ⋃ y ∈ t, {x | (x, y) ∈ d} :=
    hT_tb d h_uniform
  rcases h1 with ⟨t, ht_fin, ht_cover⟩
  let t' : Finset AffineLine := ht_fin.toFinset
  have h_t'_eq : (t' : Set AffineLine) = t := ht_fin.coe_toFinset
  have h2 : T ⊆ ⋃ y ∈ t', Metric.ball y (δnn / 2 : ℝ) := by
    have h21 : T ⊆ ⋃ y ∈ t, {x | (x, y) ∈ d} := ht_cover
    have h22 : (⋃ y ∈ t, {x | (x, y) ∈ d}) = ⋃ y ∈ t, Metric.ball y (δnn / 2 : ℝ) := by
      ext z; simp [d, Metric.mem_ball] <;> aesop
    rw [h22] at h21
    have h23 : t = (t' : Set AffineLine) := h_t'_eq.symm
    rw [h23] at h21
    exact h21
  have hC2 : Metric.IsCover (δnn / 2) T (t' : Set AffineLine) := by
    intro x hx
    have h3 : ∃ (y : AffineLine), y ∈ t' ∧ x ∈ Metric.ball y (δnn / 2 : ℝ) := by
      simpa [Set.mem_iUnion] using h2 hx
    rcases h3 with ⟨y, hy, hxy⟩
    refine ⟨y, hy, ?_⟩
    have h4 : dist x y < (δnn / 2 : ℝ) := hxy
    have h5 : edist x y ≤ ↑(δnn / 2) := by
      rw [edist_dist]
      have h_le' : ENNReal.ofReal (dist x y) ≤ ↑(δnn / 2) := by
        have h4' : dist x y ≤ (δnn / 2 : ℝ) := le_of_lt h4
        exact_mod_cast h4'
      exact h_le'
    simpa using h5
  have hcov_ne_top : (Metric.externalCoveringNumber (δnn / 2) T : ENNReal) < ⊤ := by
    have h4 : (Metric.externalCoveringNumber (δnn / 2) T : ENNReal) ≤ (t'.card : ENNReal) := by
      have h5 : Metric.externalCoveringNumber (δnn / 2) T ≤ (t' : Set AffineLine).encard :=
        hC2.externalCoveringNumber_le_encard
      have h6 : (t' : Set AffineLine).encard = (t'.card : ENat) := by simp
      rw [h6] at h5
      exact_mod_cast h5
    have h7 : (t'.card : ENNReal) < ⊤ := by simp
    exact lt_of_le_of_lt h4 h7
  have hpack_le : Metric.packingNumber δnn T ≤ Metric.externalCoveringNumber (δnn / 2) T := by
    have h2 := Metric.packingNumber_two_mul_le_externalCoveringNumber (δnn / 2) T
    have h3 : 2 * (δnn / 2) = δnn := by
      apply NNReal.coe_injective
      simp <;> ring
    rw [h3] at h2
    exact h2
  have hpack_ne_top : Metric.packingNumber δnn T ≠ ⊤ := by
    have h4 : (Metric.packingNumber δnn T : ENNReal) ≤ (Metric.externalCoveringNumber (δnn / 2) T : ENNReal) := by
      exact_mod_cast hpack_le
    have h5 : (Metric.packingNumber δnn T : ENNReal) < ⊤ := lt_of_le_of_lt h4 hcov_ne_top
    intro h6
    rw [h6] at h5
    simp at h5

  let Sset : Set AffineLine := Metric.maximalSeparatedSet δnn T
  have hS_sub : Sset ⊆ T := Metric.maximalSeparatedSet_subset
  have hS_sep_edist : Metric.IsSeparated (δnn : ENNReal) Sset :=
    Metric.isSeparated_maximalSeparatedSet
  have hS_cover : Metric.IsCover δnn T Sset :=
    Metric.isCover_maximalSeparatedSet hpack_ne_top
  have hS_nonempty' : Sset.Nonempty := hS_cover.nonempty hT_nonempty
  have hS_encard : Sset.encard = Metric.packingNumber δnn T :=
    Metric.encard_maximalSeparatedSet hpack_ne_top
  have hS_fin : Sset.Finite := by
    have h : Sset.encard < ⊤ := by
      rw [hS_encard]
      exact hpack_ne_top.lt_top
    exact Set.encard_lt_top_iff.mp h
  let S : Finset AffineLine := hS_fin.toFinset
  have hS_eq : (S : Set AffineLine) = Sset := hS_fin.coe_toFinset
  have hS_nonempty : S.Nonempty := by
    have h : (S : Set AffineLine).Nonempty := by rw [hS_eq] <;> exact hS_nonempty'
    exact Finset.coe_nonempty.mp h

  -- Cardinality bound: Ncover δ T ≤ |S|
  have hcov_T_le_S : (Metric.externalCoveringNumber δnn T : ENNReal) ≤ (S.card : ENNReal) := by
    have h1 : Metric.externalCoveringNumber δnn T ≤ Sset.encard :=
      hS_cover.externalCoveringNumber_le_encard
    have h2 : Sset.encard = ↑(S.card) := by
      rw [← hS_eq] <;> simp
    rw [h2] at h1
    exact_mod_cast h1

  -- S-set property for S (same proof as extract_finite_tube_sset)
  have hS_sep' : Set.Pairwise Sset (fun x y => δ ≤ dist x y) := by
    intro x hx y hy hxy
    have h_edist : (δnn : ENNReal) < edist x y := hS_sep_edist hx hy hxy
    have h1 : (δnn : ENNReal) ≤ edist x y := le_of_lt h_edist
    have h2 : edist x y = ENNReal.ofReal (dist x y) := by rw [edist_dist] <;> rfl
    rw [h2] at h1
    have h3 : (δnn : ℝ) ≤ dist x y := by
      have h4 : ENNReal.ofReal (δnn : ℝ) ≤ ENNReal.ofReal (dist x y) := by
        convert h1 using 1 <;> simp
      have h5 : 0 ≤ dist x y := dist_nonneg
      exact (ENNReal.ofReal_le_ofReal_iff h5).mp h4
    rw [hδnn_eq] at h3
    exact h3

  have h_pack' : ∀ (z : AffineLine) (T' : Set AffineLine),
      Set.Pairwise T' (fun x y => (δnn : ℝ) ≤ dist x y) →
      T' ⊆ Metric.closedBall z (2 * (δnn : ℝ)) →
      T'.Finite ∧ T'.encard ≤ (K_pack : ENat) := by
    intro z T' hT_sep hT_sub
    have hT_sep' : Set.Pairwise T' (fun x y => δ ≤ dist x y) := by
      simpa [hδnn_eq] using hT_sep
    have hT_sub' : T' ⊆ Metric.closedBall z (2 * δ) := by
      simpa [hδnn_eq] using hT_sub
    exact MainAppendix.affineLine_packing_bound δ hδ_pos hT_sep' z hT_sub'

  have hS_sep_nn : Set.Pairwise (S : Set AffineLine) (fun x y => (δnn : ℝ) ≤ dist x y) := by
    simpa [hS_eq, hδnn_eq] using hS_sep'
  have hcov_S_fin : (Metric.externalCoveringNumber δnn (S : Set AffineLine) : ENNReal) < ⊤ := by
    have h1 : (Metric.externalCoveringNumber δnn (S : Set AffineLine) : ENNReal) ≤ (S.card : ENNReal) := by
      exact_mod_cast Metric.externalCoveringNumber_le_encard_self (S : Set AffineLine)
    have h2 : (S.card : ENNReal) < ⊤ := by simp
    exact lt_of_le_of_lt h1 h2
  have hS_card_le_cover : (S.card : ENNReal) ≤
      (K_pack : ENNReal) * (Metric.externalCoveringNumber δnn (S : Set AffineLine) : ENNReal) := by
    have h_enc : ((S : Set AffineLine).encard : ENNReal) ≤
        (K_pack : ENNReal) * (Metric.externalCoveringNumber δnn (S : Set AffineLine) : ENNReal) :=
      MainAppendix.separated_set_card_le_covering hS_sep_nn K_pack h_pack' hcov_S_fin
    have h_eq : ((S : Set AffineLine).encard : ENNReal) = (S.card : ENNReal) := by simp
    rw [←h_eq]
    exact h_enc

  have hS_coe_sub : (S : Set AffineLine) ⊆ T := by
    have h : (S : Set AffineLine) = Sset := hS_eq
    rw [h]
    exact hS_sub

  let C' := max 1 ((K_pack : ℝ) * C)
  have hC'_nonneg : 0 ≤ C' := by positivity
  have hK_pack_nonneg : 0 ≤ (K_pack : ℝ) := by positivity
  have hK_eq : (K_pack : ENNReal) = ENNReal.ofReal (K_pack : ℝ) := by simp

  have h_main_goal : ∀ (x : AffineLine) (r : ℝ), δ ≤ r →
      (Metric.externalCoveringNumber δnn ((S : Set AffineLine) ∩ Metric.closedBall x r) : ENNReal) ≤
        ENNReal.ofReal C' * (ENNReal.ofReal r) ^ s * Metric.externalCoveringNumber δnn (S : Set AffineLine) := by
    intro x r hr
    have h_r_nonneg : 0 ≤ r := by linarith
    have h_sub_inter : (S : Set AffineLine) ∩ Metric.closedBall x r ⊆ T ∩ Metric.closedBall x r :=
      Set.inter_subset_inter_left _ hS_coe_sub
    have h1 : (Metric.externalCoveringNumber δnn ((S : Set AffineLine) ∩ Metric.closedBall x r) : ENNReal) ≤
        (Metric.externalCoveringNumber δnn (T ∩ Metric.closedBall x r) : ENNReal) := by
      exact_mod_cast Metric.externalCoveringNumber_mono_set h_sub_inter
    have h2 : (Metric.externalCoveringNumber δnn (T ∩ Metric.closedBall x r) : ENNReal) ≤
        ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * Metric.externalCoveringNumber δnn T := h_sset x r hr
    calc (Metric.externalCoveringNumber δnn ((S : Set AffineLine) ∩ Metric.closedBall x r) : ENNReal)
      ≤ Metric.externalCoveringNumber δnn (T ∩ Metric.closedBall x r) := h1
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * Metric.externalCoveringNumber δnn T := h2
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * (S.card : ENNReal) := by
        gcongr <;> exact hcov_T_le_S
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * ((K_pack : ENNReal) * Metric.externalCoveringNumber δnn (S : Set AffineLine)) := by
        gcongr <;> exact hS_card_le_cover
    _ = (K_pack : ENNReal) * ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * Metric.externalCoveringNumber δnn (S : Set AffineLine) := by
        simp [mul_assoc, mul_comm, mul_left_comm]
    _ = ENNReal.ofReal (K_pack : ℝ) * ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * Metric.externalCoveringNumber δnn (S : Set AffineLine) := by
        rw [hK_eq]
    _ = ENNReal.ofReal (((K_pack : ℝ) * C)) * (ENNReal.ofReal r) ^ s * Metric.externalCoveringNumber δnn (S : Set AffineLine) := by
        rw [← ENNReal.ofReal_mul hK_pack_nonneg] <;> simp [mul_assoc]
    _ ≤ ENNReal.ofReal C' * (ENNReal.ofReal r) ^ s * Metric.externalCoveringNumber δnn (S : Set AffineLine) := by
        have h9 : (K_pack : ℝ) * C ≤ C' := le_max_right _ _
        have h10 : ENNReal.ofReal (((K_pack : ℝ) * C)) ≤ ENNReal.ofReal C' := by
          exact ENNReal.ofReal_le_ofReal_iff (by positivity) |>.mpr h9
        gcongr

  have h_delta_sset : IsDeltaSSet δ s C' (S : Set AffineLine) :=
    ⟨hS_nonempty, hδ_pos, by positivity, hs_nonneg, h_main_goal⟩

  have hS_sep'' : Set.Pairwise (S : Set AffineLine) (fun x y => δ ≤ dist x y) := by
    rw [hS_eq] <;> exact hS_sep'
  exact ⟨S, by rw [hS_eq] <;> exact hS_sub, hS_nonempty, hS_sep'', h_delta_sset, hcov_T_le_S⟩

end ImprovedIncidenceAssembly
