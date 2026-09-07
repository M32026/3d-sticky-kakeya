module

/-
  Energy bound for Qset centers.

  Provides:
  - card_le_pack_mul_cover_with_K: cardinality ≤ K_pack * covering number
  - ball_growth_to_sset: ball-counting → IsDeltaSSet
  - energy_bound_from_ball_growth: ball-growth → s-energy bound
  - squareCenters_separated: Δ-separation of square centers
  - center_ball_growth_from_a1: derive center ball-growth from A1_Output
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.Interfaces
public import MyLeanRepo.DiscretisedFurstenbergEstimate.HeavySquareRefinement
public import MyLeanRepo.DiscretisedFurstenbergEstimate.SsetTransfer
public import MyLeanRepo.DiscretisedFurstenbergEstimate.EnergyBoundPlane
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

attribute [local instance] Classical.propDecidable

namespace DirecretisedFurstenbergEstimate.AppendixA

open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.Lagoon (squareCenter)
open DirecretisedFurstenbergEstimate.MainAppendix

/-- For a δ-separated finite set P, |P| ≤ K_pack * externalCoveringNumber δ P,
given an explicit packing constant K_pack. -/
lemma card_le_pack_mul_cover_with_K {δ : ℝ} (hδ_pos : 0 < δ)
    (K_pack : ℕ)
    (hK_pack : ∀ (z : Plane) (T : Set Plane),
      Set.Pairwise T (fun x y => δ ≤ dist x y) →
      T ⊆ Metric.closedBall z (2 * δ) → T.Finite ∧ T.encard ≤ (K_pack : ENat))
    {P : Finset Plane} (hP_sep : Set.Pairwise (P : Set Plane) (fun p p' => δ ≤ dist p p')) :
    (P.card : ENNReal) ≤ (K_pack : ENNReal) * Metric.externalCoveringNumber δ.toNNReal (P : Set Plane) := by
  have h_ne_top : Metric.externalCoveringNumber δ.toNNReal (P : Set Plane) ≠ ⊤ := by
    have h_cover : Metric.IsCover δ.toNNReal (P : Set Plane) (P : Set Plane) := by
      intro y hy
      have h : edist y y ≤ ↑δ.toNNReal := by
        rw [edist_dist, dist_self] <;> simp [hδ_pos.le] <;> exact zero_le _
      exact ⟨y, hy, h⟩
    have h : Metric.externalCoveringNumber δ.toNNReal (P : Set Plane) ≤ (P : Set Plane).encard :=
      h_cover.externalCoveringNumber_le_encard
    have h2 : (P : Set Plane).encard < ⊤ := by simp
    exact ne_top_of_le_ne_top h2.ne h
  rcases exists_minimal_external_cover h_ne_top with ⟨C, hC_cover, hC_card⟩
  have hC_fin : C.Finite := by
    have h : C.encard ≠ ⊤ := by rw [hC_card]; exact h_ne_top
    exact Set.encard_ne_top_iff.mp h
  let Cfin : Finset Plane := hC_fin.toFinset
  have hCfin_eq : (Cfin : Set Plane) = C := hC_fin.coe_toFinset
  have h1 : ∀ z ∈ Cfin, ((P.filter (fun p => edist p z ≤ ↑δ.toNNReal)).card) ≤ K_pack := by
    intro z hz
    let F : Finset Plane := P.filter (fun p => edist p z ≤ ↑δ.toNNReal)
    let T : Set Plane := (F : Set Plane)
    have hT_subP : T ⊆ (P : Set Plane) := by
      intro p hp; exact (Finset.mem_filter.mp hp).1
    have hT_sep : Set.Pairwise T (fun x y => δ ≤ dist x y) := by
      intro x hx y hy hne; exact hP_sep (hT_subP hx) (hT_subP hy) hne
    have hT_sub : T ⊆ Metric.closedBall z (2 * δ) := by
      intro p hp
      have h2 : edist p z ≤ ↑δ.toNNReal := (Finset.mem_filter.mp hp).2
      have h3 : dist p z ≤ δ := by simpa [edist_dist, hδ_pos.le] using h2
      have h4 : dist p z ≤ 2 * δ := by linarith
      simpa [Metric.mem_closedBall] using h4
    rcases hK_pack z T hT_sep hT_sub with ⟨_, h4⟩
    have h5 : T.encard ≤ (K_pack : ENat) := h4
    have h8 : T.encard = ↑(F.card) := by
      have h9 : T = (F : Set Plane) := by rfl
      rw [h9]; exact Set.encard_coe_eq_coe_finsetCard F
    rw [h8] at h5
    simpa [F] using h5
  have h_coverP : (P : Set Plane) ⊆ ⋃ z ∈ C, {p | edist p z ≤ ↑δ.toNNReal} := by
    intro p hp
    have h4 : ∃ y ∈ C, edist p y ≤ ↑δ.toNNReal := hC_cover hp
    rcases h4 with ⟨z, hz, h5⟩
    exact Set.mem_iUnion₂.mpr ⟨z, hz, h5⟩
  classical
  have h3 : P ⊆ Cfin.biUnion (fun z => P.filter (fun p => edist p z ≤ ↑δ.toNNReal)) := by
    intro p hp
    have h4 := h_coverP hp
    simp only [Finset.mem_biUnion, Set.mem_iUnion] at h4 ⊢
    rcases h4 with ⟨z, hz, h5⟩
    have hz' : z ∈ Cfin := by
      have h9 : z ∈ (Cfin : Set Plane) := by rw [hCfin_eq]; exact hz
      simpa [Finset.mem_coe] using h9
    exact ⟨z, hz', Finset.mem_filter.mpr ⟨hp, h5⟩⟩
  have h4 : P.card ≤ (Cfin.biUnion (fun z => P.filter (fun p => edist p z ≤ ↑δ.toNNReal))).card :=
    Finset.card_le_card h3
  have h5 : (Cfin.biUnion (fun z => P.filter (fun p => edist p z ≤ ↑δ.toNNReal))).card ≤
      ∑ z ∈ Cfin, (P.filter (fun p => edist p z ≤ ↑δ.toNNReal)).card :=
    Finset.card_biUnion_le
  have h6 : P.card ≤ ∑ z ∈ Cfin, (P.filter (fun p => edist p z ≤ ↑δ.toNNReal)).card :=
    le_trans h4 h5
  have h7 : ∑ z ∈ Cfin, (P.filter (fun p => edist p z ≤ ↑δ.toNNReal)).card ≤ (K_pack : ℕ) * Cfin.card := by
    calc ∑ z ∈ Cfin, (P.filter (fun p => edist p z ≤ ↑δ.toNNReal)).card
      ≤ ∑ z ∈ Cfin, K_pack := Finset.sum_le_sum (fun z hz => by
        have h := h1 z hz; simpa using h)
    _ = Cfin.card * K_pack := by simp [Finset.sum_const] <;> ring
    _ = (K_pack : ℕ) * Cfin.card := by ring
  have h8 : (P.card : ENNReal) ≤ (K_pack : ENNReal) * (Cfin.card : ENNReal) := by
    have h9 : (P.card : ℕ) ≤ (K_pack : ℕ) * Cfin.card := le_trans h6 h7
    exact_mod_cast h9
  have h10 : (Cfin.card : ENNReal) = Metric.externalCoveringNumber δ.toNNReal (P : Set Plane) := by
    have h11 : (Cfin.card : ENat) = C.encard := by
      calc (Cfin.card : ENat)
        = (Cfin : Set Plane).encard := by simp
      _ = C.encard := by rw [hCfin_eq]
    have h12 : (Cfin.card : ENNReal) = ↑(Cfin.card : ENat) := by simp
    rw [h12, h11, hC_card]
  rw [h10] at h8
  exact h8

/-- For a δ-separated finite set P, ∃ K_pack, |P| ≤ K_pack * externalCoveringNumber δ P. -/
lemma card_le_pack_mul_cover {δ : ℝ} (hδ_pos : 0 < δ)
    {P : Finset Plane} (hP_sep : Set.Pairwise (P : Set Plane) (fun p p' => δ ≤ dist p p')) :
    ∃ (K_pack : ℕ), (P.card : ENNReal) ≤ (K_pack : ENNReal) * Metric.externalCoveringNumber δ.toNNReal (P : Set Plane) := by
  rcases plane_packing_bound δ hδ_pos with ⟨K_pack, hK_pack⟩
  exact ⟨K_pack, card_le_pack_mul_cover_with_K hδ_pos K_pack hK_pack hP_sep⟩

/-- Convert a direct ball-counting bound on plane centers to IsDeltaSSet,
losing a packing constant factor. -/
lemma ball_growth_to_sset
    {Δ t C : ℝ} (hΔ_pos : 0 < Δ) (hC_pos : 0 < C) (ht_nonneg : 0 ≤ t)
    {Qset : Finset (CoarseSquare Δ)}
    (hQset_nonempty : Qset.Nonempty)
    (hP_sep : Set.Pairwise (Qset.image (squareCenter Δ) : Set Plane) (fun p p' => Δ ≤ dist p p'))
    (h_ball : ∀ (c : Plane) (r : ℝ), Δ ≤ r →
      ((Qset.image (squareCenter Δ)).filter (fun q => dist q c ≤ r)).card ≤
        (C * r^t * (Qset.image (squareCenter Δ)).card : ℝ)) :
    ∃ (C' : ℝ), 0 < C' ∧ C' = C * (plane_packing_constant : ℝ) ∧
      IsDeltaSSet Δ t C' (Qset.image (squareCenter Δ) : Set Plane) := by
  let P := Qset.image (squareCenter Δ)
  have hP_nonempty : (P : Set Plane).Nonempty := by
    rcases hQset_nonempty with ⟨Q, hQ⟩
    exact ⟨squareCenter Δ Q, Finset.mem_image.mpr ⟨Q, hQ, rfl⟩⟩
  have hKpack_ge_one : 1 ≤ plane_packing_constant := by
    have hpos : 0 < plane_packing_constant := plane_packing_constant_pos
    exact Nat.succ_le_iff.mpr hpos
  let K_pack' : ℕ := plane_packing_constant
  have hK_pack'_pos : 0 < (K_pack' : ℝ) := by exact_mod_cast plane_packing_constant_pos
  let C' : ℝ := C * (K_pack' : ℝ)
  have hC'_pos : 0 < C' := mul_pos hC_pos hK_pack'_pos
  have hC'_eq : C' = C * (plane_packing_constant : ℝ) := by rfl
  have h_card_cover : (P.card : ENNReal) ≤ (K_pack' : ENNReal) * Metric.externalCoveringNumber Δ.toNNReal (P : Set Plane) :=
    card_le_pack_mul_cover_with_K hΔ_pos K_pack' (plane_packing_constant_bound Δ hΔ_pos) hP_sep
  refine' ⟨C', hC'_pos, hC'_eq, _⟩
  refine' ⟨hP_nonempty, hΔ_pos, hC'_pos, ht_nonneg, _⟩
  intro c r hr
  let A : Finset Plane := P.filter (fun q => dist q c ≤ r)
  have hA_eq : (A : Set Plane) = (P : Set Plane) ∩ Metric.closedBall c r := by
    ext y; simp [A, Metric.mem_closedBall] <;> tauto
  have h_cover_A : Metric.IsCover Δ.toNNReal (A : Set Plane) (A : Set Plane) := by
    intro y hy
    have h : edist y y ≤ ↑Δ.toNNReal := by
      rw [edist_dist, dist_self] <;> simp [hΔ_pos.le] <;> exact zero_le _
    exact ⟨y, hy, h⟩
  have h_ncover_A' : (Metric.externalCoveringNumber Δ.toNNReal (A : Set Plane) : ENNReal) ≤ (A.card : ENNReal) := by
    have h2 : (A : Set Plane).encard = ↑A.card := by simp
    have h3 : Metric.externalCoveringNumber Δ.toNNReal (A : Set Plane) ≤ (A : Set Plane).encard :=
      h_cover_A.externalCoveringNumber_le_encard
    rw [h2] at h3
    exact_mod_cast h3
  have h_main : (A.card : ℝ) ≤ C * r^t * (P.card : ℝ) := h_ball c r hr
  have hpos1 : 0 ≤ r := by linarith
  have h_enn1 : (A.card : ENNReal) ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ t * (P.card : ENNReal) := by
    have h1 : ENNReal.ofReal (A.card : ℝ) ≤ ENNReal.ofReal (C * r^t * (P.card : ℝ)) :=
      ENNReal.ofReal_le_ofReal h_main
    have h2 : ENNReal.ofReal (A.card : ℝ) = (A.card : ENNReal) := by simp
    rw [h2] at h1
    have h3 : ENNReal.ofReal (C * r^t * (P.card : ℝ)) =
        ENNReal.ofReal C * (ENNReal.ofReal r) ^ t * ENNReal.ofReal (P.card : ℝ) := by
      have h4 : ENNReal.ofReal (C * r^t * (P.card : ℝ)) =
          ENNReal.ofReal (C * r^t) * ENNReal.ofReal (P.card : ℝ) :=
        ENNReal.ofReal_mul (by positivity)
      rw [h4]
      have h5 : ENNReal.ofReal (C * r^t) = ENNReal.ofReal C * ENNReal.ofReal (r^t) :=
        ENNReal.ofReal_mul hC_pos.le
      rw [h5]
      have h6 : ENNReal.ofReal (r^t) = (ENNReal.ofReal r) ^ t :=
        (ENNReal.ofReal_rpow_of_nonneg hpos1 ht_nonneg).symm
      rw [h6] <;> ring
    rw [h3] at h1
    have h7 : ENNReal.ofReal (P.card : ℝ) = (P.card : ENNReal) := by simp
    rw [h7] at h1
    exact h1
  calc (Metric.externalCoveringNumber Δ.toNNReal ((P : Set Plane) ∩ Metric.closedBall c r) : ENNReal)
    = Metric.externalCoveringNumber Δ.toNNReal (A : Set Plane) := by rw [hA_eq]
  _ ≤ (A.card : ENNReal) := h_ncover_A'
  _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ t * (P.card : ENNReal) := h_enn1
  _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ t * ((K_pack' : ENNReal) * Metric.externalCoveringNumber Δ.toNNReal (P : Set Plane)) := by
      gcongr
  _ = ENNReal.ofReal C' * (ENNReal.ofReal r) ^ t * Metric.externalCoveringNumber Δ.toNNReal (P : Set Plane) := by
      have h7 : ENNReal.ofReal C' = ENNReal.ofReal C * (K_pack' : ENNReal) := by
        have h8 : ENNReal.ofReal C' = ENNReal.ofReal (C * (K_pack' : ℝ)) := by rfl
        rw [h8]
        have h9 : ENNReal.ofReal (C * (K_pack' : ℝ)) = ENNReal.ofReal C * ENNReal.ofReal (K_pack' : ℝ) :=
          ENNReal.ofReal_mul hC_pos.le
        rw [h9] <;> simp
      rw [h7] <;> ring

/-- Energy bound for Qset centers from ball-growth. -/
lemma energy_bound_from_ball_growth
    {Δ s t C R : ℝ}
    (hΔ_pos : 0 < Δ) (hs_pos : 0 < s) (hst : s < t)
    (hR_pos : 0 < R) (hC_pos : 0 < C)
    {Qset : Finset (CoarseSquare Δ)}
    (hQset_nonempty : Qset.Nonempty)
    (hP_sep : Set.Pairwise (Qset.image (squareCenter Δ) : Set Plane) (fun p p' => Δ ≤ dist p p'))
    (hP_bdd : ∀ p ∈ Qset.image (squareCenter Δ), ‖p‖ ≤ R)
    (h_ball : ∀ (c : Plane) (r : ℝ), Δ ≤ r →
      ((Qset.image (squareCenter Δ)).filter (fun q => dist q c ≤ r)).card ≤
        (C * r^t * (Qset.image (squareCenter Δ)).card : ℝ)) :
    ∃ (K_total : ℝ), 0 < K_total ∧
      K_total = plane_energy_constant s t R * (plane_packing_constant : ℝ) ∧
      ∑ p ∈ Qset.image (squareCenter Δ),
        ∑ q ∈ (Qset.image (squareCenter Δ)).erase p, Real.rpow (dist p q) (-s) ≤
        K_total * C * ((Qset.image (squareCenter Δ)).card : ℝ)^2 := by
  rcases ball_growth_to_sset hΔ_pos hC_pos (by linarith) hQset_nonempty hP_sep h_ball with ⟨C', hC'_pos, hC'_eq, hP_set⟩
  have h_main := s_energy_bound_plane_exists hΔ_pos hs_pos hst hR_pos hC'_pos hP_sep hP_set hP_bdd
  rcases h_main with ⟨K_energy, hK_pos, hK_ge, hK_eq, hE⟩
  let K_total : ℝ := K_energy * (plane_packing_constant : ℝ)
  have hK_total_pos : 0 < K_total :=
    mul_pos hK_pos (by exact_mod_cast plane_packing_constant_pos)
  have hK_total_eq : K_total = plane_energy_constant s t R * (plane_packing_constant : ℝ) := by
    dsimp only [K_total]
    rw [hK_eq] <;> ring
  have hC'_div : C' / C = (plane_packing_constant : ℝ) := by
    rw [hC'_eq]
    field_simp [hC_pos.ne'] <;> ring
  refine' ⟨K_total, hK_total_pos, hK_total_eq, _⟩
  have h_goal : K_energy * C' * ((Qset.image (squareCenter Δ)).card : ℝ)^2 =
      K_total * C * ((Qset.image (squareCenter Δ)).card : ℝ)^2 := by
    dsimp only [K_total]
    have h9 : K_energy * C' = K_energy * (plane_packing_constant : ℝ) * C := by
      rw [hC'_eq] <;> ring
    rw [h9] <;> ring
  rw [h_goal] at hE
  exact hE

/-- Square centers are Δ-separated. -/
lemma squareCenters_separated {Δ : ℝ} (hΔ_pos : 0 < Δ)
    {Qset : Finset (CoarseSquare Δ)} :
    Set.Pairwise (Qset.image (squareCenter Δ) : Set Plane) (fun p p' => Δ ≤ dist p p') := by
  intro p hp p' hp' hne
  rcases Finset.mem_image.mp hp with ⟨Q, hQ, rfl⟩
  rcases Finset.mem_image.mp hp' with ⟨Q', hQ', rfl⟩
  have hQne : Q ≠ Q' := by intro h; apply hne; rw [h]
  have h_coord : (Q.1 : ℝ) ≠ (Q'.1 : ℝ) ∨ (Q.2 : ℝ) ≠ (Q'.2 : ℝ) := by
    by_contra h; push Not at h
    have hQ1 : Q.1 = Q'.1 := by exact_mod_cast h.1
    have hQ2 : Q.2 = Q'.2 := by exact_mod_cast h.2
    exact hQne (Prod.ext hQ1 hQ2)
  let v := squareCenter Δ Q - squareCenter Δ Q'
  have hv0 : v 0 = Δ * ((Q.1 : ℝ) - (Q'.1 : ℝ)) := by simp [v, squareCenter] <;> ring
  have hv1 : v 1 = Δ * ((Q.2 : ℝ) - (Q'.2 : ℝ)) := by simp [v, squareCenter] <;> ring
  have h_abs_le_norm : ∀ (i : Fin 2), |v i| ≤ ‖v‖ := by exact fun i => TubesAndSlopes.coord_abs_le_norm v i
  rcases h_coord with (h | h)
  · have h_int : Q.1 ≠ Q'.1 := by exact_mod_cast h
    have h_abs : 1 ≤ |(Q.1 : ℝ) - (Q'.1 : ℝ)| := by
      have h1 : (Q.1 : ℤ) - Q'.1 ≠ 0 := by omega
      have h2 : 1 ≤ |Q.1 - Q'.1| := Int.one_le_abs h1
      exact_mod_cast h2
    have h3 : |v 0| ≥ Δ := by
      rw [hv0, abs_mul, abs_of_pos hΔ_pos]
      have h4 : Δ * |(Q.1 : ℝ) - (Q'.1 : ℝ)| ≥ Δ * 1 := by gcongr
      linarith
    have h5 : Δ ≤ ‖v‖ := by
      calc Δ ≤ |v 0| := h3
           _ ≤ ‖v‖ := h_abs_le_norm 0
    simpa [dist_eq_norm] using h5
  · have h_int : Q.2 ≠ Q'.2 := by exact_mod_cast h
    have h_abs : 1 ≤ |(Q.2 : ℝ) - (Q'.2 : ℝ)| := by
      have h1 : (Q.2 : ℤ) - Q'.2 ≠ 0 := by omega
      have h2 : 1 ≤ |Q.2 - Q'.2| := Int.one_le_abs h1
      exact_mod_cast h2
    have h3 : |v 1| ≥ Δ := by
      rw [hv1, abs_mul, abs_of_pos hΔ_pos]
      have h4 : Δ * |(Q.2 : ℝ) - (Q'.2 : ℝ)| ≥ Δ * 1 := by gcongr
      linarith
    have h5 : Δ ≤ ‖v‖ := by
      calc Δ ≤ |v 1| := h3
           _ ≤ ‖v‖ := h_abs_le_norm 1
    simpa [dist_eq_norm] using h5

/-- Disjointness of square sets for different coarse squares. -/
lemma squareSets_disjoint {Δ : ℝ} (hΔ_pos : 0 < Δ) {Q1 Q2 : CoarseSquare Δ} (hne : Q1 ≠ Q2) :
    Disjoint (squareSet Δ Q1) (squareSet Δ Q2) := by
  rw [Set.disjoint_left]
  intro p hp1 hp2
  have h1 : p 0 ∈ Set.Ico (Δ * (Q1.1 : ℝ)) (Δ * ((Q1.1 : ℝ) + 1)) := hp1.1
  have h2 : p 0 ∈ Set.Ico (Δ * (Q2.1 : ℝ)) (Δ * ((Q2.1 : ℝ) + 1)) := hp2.1
  have h3 : p 1 ∈ Set.Ico (Δ * (Q1.2 : ℝ)) (Δ * ((Q1.2 : ℝ) + 1)) := hp1.2
  have h4 : p 1 ∈ Set.Ico (Δ * (Q2.2 : ℝ)) (Δ * ((Q2.2 : ℝ) + 1)) := hp2.2
  have h_coord : Q1.1 ≠ Q2.1 ∨ Q1.2 ≠ Q2.2 := by
    by_contra h; push Not at h
    exact hne (Prod.ext h.1 h.2)
  rcases h_coord with (h | h)
  · have h_lt : Q1.1 < Q2.1 ∨ Q2.1 < Q1.1 := lt_or_gt_of_ne h
    rcases h_lt with (h_lt | h_lt)
    · have h6 : (Q1.1 : ℝ) + 1 ≤ (Q2.1 : ℝ) := by exact_mod_cast Int.add_one_le_of_lt h_lt
      have h7 : p 0 < Δ * ((Q1.1 : ℝ) + 1) := h1.2
      have h8 : Δ * (Q2.1 : ℝ) ≤ p 0 := h2.1
      have h9 : Δ * ((Q1.1 : ℝ) + 1) ≤ Δ * (Q2.1 : ℝ) := by gcongr
      linarith
    · have h6 : (Q2.1 : ℝ) + 1 ≤ (Q1.1 : ℝ) := by exact_mod_cast Int.add_one_le_of_lt h_lt
      have h7 : p 0 < Δ * ((Q2.1 : ℝ) + 1) := h2.2
      have h8 : Δ * (Q1.1 : ℝ) ≤ p 0 := h1.1
      have h9 : Δ * ((Q2.1 : ℝ) + 1) ≤ Δ * (Q1.1 : ℝ) := by gcongr
      linarith
  · have h_lt : Q1.2 < Q2.2 ∨ Q2.2 < Q1.2 := lt_or_gt_of_ne h
    rcases h_lt with (h_lt | h_lt)
    · have h6 : (Q1.2 : ℝ) + 1 ≤ (Q2.2 : ℝ) := by exact_mod_cast Int.add_one_le_of_lt h_lt
      have h7 : p 1 < Δ * ((Q1.2 : ℝ) + 1) := h3.2
      have h8 : Δ * (Q2.2 : ℝ) ≤ p 1 := h4.1
      have h9 : Δ * ((Q1.2 : ℝ) + 1) ≤ Δ * (Q2.2 : ℝ) := by gcongr
      linarith
    · have h6 : (Q2.2 : ℝ) + 1 ≤ (Q1.2 : ℝ) := by exact_mod_cast Int.add_one_le_of_lt h_lt
      have h7 : p 1 < Δ * ((Q2.2 : ℝ) + 1) := h4.2
      have h8 : Δ * (Q1.2 : ℝ) ≤ p 1 := h3.1
      have h9 : Δ * ((Q2.2 : ℝ) + 1) ≤ Δ * (Q1.2 : ℝ) := by gcongr
      linarith

/-- Derive center ball-growth from A1_Output's physical growth bound.

    Uses `a1.hQset_phys_growth` directly, converting from the Qset.filter
    form to the centers.image.filter form via injectivity of squareCenter.
    The resulting constant is `Δ^{-10ε}`. -/
lemma center_ball_growth_from_a1
    {Δ δ s t ε : ℝ}
    (hΔ_pos : 0 < Δ) (hδ_pos : 0 < δ) (hδ_le_Δ : δ ≤ Δ)
    (hε_pos : 0 < ε) (ht_nonneg : 0 ≤ t)
    (a1 : A1_Output Δ δ t s ε) :
    ∃ (Cball : ℝ), 0 < Cball ∧ Cball = Real.rpow Δ (-11 * ε) ∧
      ∀ (c : Plane) (r : ℝ), Δ ≤ r →
        ((a1.Qset.image (squareCenter Δ)).filter (fun q => dist q c ≤ r)).card ≤
        Cball * r^t * ((a1.Qset.image (squareCenter Δ)).card : ℝ) := by
  let centers := a1.Qset.image (squareCenter Δ)
  have h_inj : Function.Injective (squareCenter Δ) := by
    intro Q1 Q2 h
    have h1 : squareCenter Δ Q1 0 = squareCenter Δ Q2 0 := by rw [h]
    have h2 : squareCenter Δ Q1 1 = squareCenter Δ Q2 1 := by rw [h]
    have hq1 : Δ * ((Q1.1 : ℝ) + 1 / 2) = Δ * ((Q2.1 : ℝ) + 1 / 2) := by
      simpa [Lagoon.squareCenter_zero] using h1
    have hq2 : Δ * ((Q1.2 : ℝ) + 1 / 2) = Δ * ((Q2.2 : ℝ) + 1 / 2) := by
      simpa [Lagoon.squareCenter_one] using h2
    have hq1' : (Q1.1 : ℝ) + 1 / 2 = (Q2.1 : ℝ) + 1 / 2 := by
      apply (mul_right_inj' hΔ_pos.ne').mp hq1
    have hq2' : (Q1.2 : ℝ) + 1 / 2 = (Q2.2 : ℝ) + 1 / 2 := by
      apply (mul_right_inj' hΔ_pos.ne').mp hq2
    have hQ1 : (Q1.1 : ℝ) = (Q2.1 : ℝ) := by linarith
    have hQ2 : (Q1.2 : ℝ) = (Q2.2 : ℝ) := by linarith
    have hQ1' : Q1.1 = Q2.1 := by exact_mod_cast hQ1
    have hQ2' : Q1.2 = Q2.2 := by exact_mod_cast hQ2
    exact Prod.ext hQ1' hQ2'
  have h_card_image : centers.card = a1.Qset.card := by
    rw [Finset.card_image_of_injective a1.Qset h_inj]
  have h_filter_eq : ∀ (c : Plane) (r : ℝ),
      (centers.filter (fun q => dist q c ≤ r)).card =
        (a1.Qset.filter (fun Q => dist (squareCenter Δ Q) c ≤ r)).card := by
    intro c r
    have h1 : centers.filter (fun q => dist q c ≤ r) =
        (a1.Qset.filter (fun Q => dist (squareCenter Δ Q) c ≤ r)).image (squareCenter Δ) := by
      ext q
      simp only [centers, Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨Q, hQ, rfl⟩, hdist⟩; exact ⟨Q, ⟨hQ, hdist⟩, rfl⟩
      · rintro ⟨Q, ⟨hQ, hdist⟩, rfl⟩; exact ⟨⟨Q, hQ, rfl⟩, hdist⟩
    rw [h1]
    rw [Finset.card_image_of_injOn]
    exact fun Q _ Q' _ h => h_inj h
  let Cball : ℝ := Real.rpow Δ (-11 * ε)
  have hCball_pos : 0 < Cball := Real.rpow_pos_of_pos hΔ_pos _
  have hCball_eq : Cball = Real.rpow Δ (-11 * ε) := by rfl
  refine ⟨Cball, hCball_pos, hCball_eq, ?_⟩
  intro c r hr
  have h_phys : ((a1.Qset.filter (fun Q => dist (squareCenter Δ Q) c ≤ r)).card : ℝ) ≤
      Real.rpow Δ (-11 * ε) * r^t * (a1.Qset.card : ℝ) :=
    a1.hQset_phys_growth c r hr
  have h_goal : ((centers.filter (fun q => dist q c ≤ r)).card : ℝ) ≤
      Cball * r^t * (centers.card : ℝ) := by
    rw [h_filter_eq c r, h_card_image]
    exact h_phys
  exact_mod_cast h_goal

/-- Derive an energy bound for Qset centers from A1_Output.

    Produces ∃ K_abs > 0, energy ≤ K_abs * |centers|^2
    where K_abs = K_total * Δ^{-10ε}, with K_total depending only on
    s, t, R and universal packing constants.

    To obtain the exact Δ^{-10ε} bound required by A3 canonical,
    the caller must absorb K_total using numerical hypotheses. -/
lemma energy_all_from_a1_exists
    {Δ δ s t ε R : ℝ}
    (hΔ_pos : 0 < Δ) (hδ_pos : 0 < δ) (hδ_le_Δ : δ ≤ Δ)
    (hε_pos : 0 < ε) (hs_pos : 0 < s) (hst : s < t) (ht_nonneg : 0 ≤ t)
    (hR_pos : 0 < R)
    (a1 : A1_Output Δ δ t s ε)
    (hP_bdd : ∀ p ∈ a1.Qset.image (squareCenter Δ), ‖p‖ ≤ R) :
    ∃ (K_abs : ℝ), 0 < K_abs ∧
      ∑ p ∈ (a1.Qset.image (squareCenter Δ)),
        ∑ q ∈ (a1.Qset.image (squareCenter Δ)).erase p,
          Real.rpow (dist p q) (-s) ≤
        K_abs * ((a1.Qset.image (squareCenter Δ)).card : ℝ)^2 := by
  rcases center_ball_growth_from_a1 hΔ_pos hδ_pos hδ_le_Δ hε_pos ht_nonneg a1 with ⟨Cball, hCball_pos, _, h_ball⟩
  have hP_sep : Set.Pairwise ((a1.Qset.image (squareCenter Δ)) : Set Plane) (fun p p' => Δ ≤ dist p p') :=
    squareCenters_separated (Qset := a1.Qset) hΔ_pos
  have hQset_nonempty : a1.Qset.Nonempty := a1.hQset_sset.1
  rcases energy_bound_from_ball_growth hΔ_pos hs_pos hst hR_pos hCball_pos hQset_nonempty hP_sep hP_bdd h_ball with ⟨K_total, hK_pos, _, hE⟩
  refine ⟨K_total * Cball, mul_pos hK_pos hCball_pos, ?_⟩
  have h_final : (K_total * Cball) * ((a1.Qset.image (squareCenter Δ)).card : ℝ)^2 =
      K_total * Cball * ((a1.Qset.image (squareCenter Δ)).card : ℝ)^2 := by ring
  rw [←h_final]
  exact hE

end DirecretisedFurstenbergEstimate.AppendixA
