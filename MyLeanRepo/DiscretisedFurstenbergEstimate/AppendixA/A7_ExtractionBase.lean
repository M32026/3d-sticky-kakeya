module

/-
  A7 extraction base: packing helpers, A5 utilities, square center distance,
  and Phase 1+2 physical energy extraction.

  Provides `A7_ExtractionResult` and `a7_extraction` used by the subsequent
  index growth, index S-set, and physical S-set phases.

  Split from A7_PhysicalSSet.lean to reduce per-file elaboration memory.

  Dependencies:
  - A7_PhysicalExtraction
  - EnergyToDeltaSSet
  - CommonTubeEnergyExtraction
  - Interfaces
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A7_PhysicalExtraction
public import MyLeanRepo.DiscretisedFurstenbergEstimate.EnergyToDeltaSSet
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CommonTubeEnergyExtraction
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.Interfaces
public import MyLeanRepo.OSWPrelude

@[expose] public section


open scoped ENNReal NNReal
attribute [local instance] Classical.propDecidable

open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.Lagoon (squareCenter)
open DirecretisedFurstenbergEstimate.Phase2

namespace DirecretisedFurstenbergEstimate.AppendixA

noncomputable section

/-! ========================================================================
   Non-strict separation covering bound
   ======================================================================== -/

/-- Non-strict version: a δ-separated (δ ≤ dist) finite set in a 2δ-ball has ≤ 25 points. -/
lemma ball_separated_card_le_25_nonstrict {δ : ℝ} (hδ_pos : 0 < δ)
    {x : Plane} {T : Finset Plane}
    (hT_sub : (T : Set Plane) ⊆ Metric.closedBall x (2 * δ))
    (h_sep : Set.Pairwise (T : Set Plane) (fun y z => δ ≤ dist y z)) :
    T.card ≤ 25 := by
  let f : Plane → Plane := fun y => (δ⁻¹) • (y - x)
  let T' : Finset Plane := T.image f
  have h_inj : Set.InjOn f (T : Set Plane) := by
    intro y _ z _ h
    have h' : (δ⁻¹ : ℝ) • (y - x) = (δ⁻¹ : ℝ) • (z - x) := h
    have h'' : y - x = z - x := by
      have h_sub : (δ⁻¹ : ℝ) • ((y - x) - (z - x)) = 0 := by
        rw [smul_sub] <;> exact sub_eq_zero.mpr h'
      have h' : (δ⁻¹ : ℝ) = 0 ∨ (y - x) - (z - x) = 0 := smul_eq_zero.mp h_sub
      have h_eq_zero : (y - x) - (z - x) = 0 := h'.resolve_left (by positivity)
      simpa [sub_eq_zero] using h_eq_zero
    have h3 : y = z := by simpa [sub_eq_sub_iff_sub_eq_sub] using h''
    exact h3
  have h_card : T'.card = T.card := by
    rw [Finset.card_image_of_injOn]; exact h_inj
  have h_norm : ∀ z ∈ T', ‖z‖ ≤ 2 := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨y, hy, rfl⟩
    have h_dist : dist y x ≤ 2 * δ := hT_sub hy
    have h_pos : 0 < δ⁻¹ := by positivity
    have h : ‖f y‖ = δ⁻¹ * ‖y - x‖ := by
      have h1 : ‖f y‖ = ‖(δ⁻¹ : ℝ)‖ * ‖y - x‖ := norm_smul (δ⁻¹ : ℝ) (y - x)
      rw [h1]
      have h2 : ‖(δ⁻¹ : ℝ)‖ = δ⁻¹ := by rw [Real.norm_eq_abs, abs_of_pos h_pos]
      rw [h2] <;> ring
    rw [h]
    have h2 : ‖y - x‖ = dist y x := by rw [dist_eq_norm]
    rw [h2]
    have h3 : δ⁻¹ * dist y x ≤ 2 := by
      calc δ⁻¹ * dist y x ≤ δ⁻¹ * (2 * δ) := by gcongr
        _ = 2 := by field_simp [hδ_pos.ne'] <;> ring
    exact h3
  have h_sep' : ∀ (z1 : Plane), z1 ∈ T' → ∀ (z2 : Plane), z2 ∈ T' → z1 ≠ z2 → 1 ≤ ‖z1 - z2‖ := by
    intro z1 hz1 z2 hz2 hne
    rcases Finset.mem_image.mp hz1 with ⟨y1, hy1, rfl⟩
    rcases Finset.mem_image.mp hz2 with ⟨y2, hy2, rfl⟩
    have hy12 : y1 ≠ y2 := by intro h; apply hne; simp [h]
    have h_dist : δ ≤ dist y1 y2 := h_sep hy1 hy2 hy12
    have h_pos : 0 < δ⁻¹ := by positivity
    have h5 : ‖f y1 - f y2‖ = δ⁻¹ * dist y1 y2 := by
      have h_eq : f y1 - f y2 = (δ⁻¹ : ℝ) • (y1 - y2) := by simp [f, smul_sub] <;> abel
      rw [h_eq]
      have h1 : ‖(δ⁻¹ : ℝ) • (y1 - y2)‖ = ‖(δ⁻¹ : ℝ)‖ * ‖y1 - y2‖ := norm_smul _ _
      rw [h1]
      have h2 : ‖(δ⁻¹ : ℝ)‖ = δ⁻¹ := by rw [Real.norm_eq_abs, abs_of_pos h_pos]
      rw [h2, dist_eq_norm] <;> ring
    rw [h5]
    have h6 : δ⁻¹ * dist y1 y2 ≥ 1 := by
      calc δ⁻¹ * dist y1 y2 ≥ δ⁻¹ * δ := by gcongr
        _ = 1 := by field_simp [hδ_pos.ne'] <;> ring
    exact h6
  have h_finrank : Module.finrank ℝ Plane = 2 := by
    rw [finrank_euclideanSpace_fin] <;> decide
  have h_main : T'.card ≤ 25 := by
    have h := Besicovitch.card_le_of_separated T' h_norm h_sep'
    rw [h_finrank] at h
    norm_num at h ⊢
    exact h
  rw [h_card] at h_main
  exact h_main

/-- Non-strict version: |S| ≤ 25 * covering(δ, S) for δ-separated (δ ≤ dist) finite set. -/
lemma separated_card_le_25_mul_covering_nonstrict {δ : ℝ} (hδ_pos : 0 < δ)
    {S : Finset Plane}
    (h_sep : Set.Pairwise (S : Set Plane) (fun x y => δ ≤ dist x y)) :
    (S.card : ENNReal) ≤ 25 * Metric.externalCoveringNumber δ.toNNReal (S : Set Plane) := by
  let ε : NNReal := 2 * δ.toNNReal
  have hε_pos : 0 < ε := by positivity
  have h_pack_le : Metric.packingNumber ε (S : Set Plane) ≤ (S : Set Plane).encard :=
    Metric.packingNumber_le_encard_self (S : Set Plane)
  have h_pack_fin : Metric.packingNumber ε (S : Set Plane) ≠ ⊤ :=
    ne_top_of_le_ne_top S.finite_toSet.encard_lt_top.ne h_pack_le
  let C : Set Plane := Metric.maximalSeparatedSet ε (S : Set Plane)
  have hC_sub : C ⊆ (S : Set Plane) := Metric.maximalSeparatedSet_subset
  have hC_sep : Metric.IsSeparated (↑ε) C := Metric.isSeparated_maximalSeparatedSet
  have hC_cover : Metric.IsCover ε (S : Set Plane) C := Metric.isCover_maximalSeparatedSet h_pack_fin
  have hC_fin : C.Finite := Set.Finite.subset S.finite_toSet hC_sub
  let C' : Finset Plane := hC_fin.toFinset
  have hC'_eq : (C' : Set Plane) = C := hC_fin.coe_toFinset
  have h_cover : ∀ (x : Plane), x ∈ (S : Set Plane) → ∃ (c : Plane), c ∈ C ∧ dist x c ≤ 2 * δ := by
    intro x hx
    have h : ∃ c ∈ C, edist x c ≤ ↑ε := hC_cover hx
    rcases h with ⟨c, hc, hed⟩
    have hdist : dist x c ≤ 2 * δ := by
      have h2 : edist x c = ENNReal.ofReal (dist x c) := edist_dist x c
      have h3 : (↑ε : ENNReal) = ENNReal.ofReal (2 * δ) := by simp [ε] <;> norm_cast <;> ring
      rw [h2, h3] at hed
      by_contra h4
      have h5 : 2 * δ < dist x c := by linarith
      have h6 : ENNReal.ofReal (2 * δ) ≤ ENNReal.ofReal (dist x c) := ENNReal.ofReal_le_ofReal (by linarith)
      have h7 : ENNReal.ofReal (dist x c) = ENNReal.ofReal (2 * δ) := le_antisymm hed h6
      have h8 : dist x c = 2 * δ := by
        have h_pos1 : 0 ≤ dist x c := by positivity
        have h_pos2 : 0 ≤ 2 * δ := by positivity
        exact Eq.symm ((fun {p q} hp hq => (ENNReal.ofReal_eq_ofReal_iff hp hq).mp) h_pos2 h_pos1 (id (Eq.symm h7)))
      linarith
    exact ⟨c, hc, hdist⟩
  let f : Plane → Plane := fun x =>
    if h : x ∈ (S : Set Plane) then Classical.choose (h_cover x h) else 0
  have hf : ∀ (x : Plane), x ∈ (S : Set Plane) → f x ∈ C ∧ dist x (f x) ≤ 2 * δ := by
    intro x hx
    have h_def : f x = Classical.choose (h_cover x hx) := by
      have h9 : f x = (if h : x ∈ (S : Set Plane) then Classical.choose (h_cover x h) else 0) := by rfl
      rw [h9, dif_pos hx]
    rw [h_def]
    exact Classical.choose_spec (h_cover x hx)
  have hf1 : ∀ x, x ∈ (S : Set Plane) → f x ∈ C := fun x hx => (hf x hx).1
  have hf2 : ∀ x, x ∈ (S : Set Plane) → dist x (f x) ≤ 2 * δ := fun x hx => (hf x hx).2
  have h_fiber : ∀ c ∈ C', (S.filter (fun x => f x = c)).card ≤ 25 := by
    intro c hc
    have hcC : c ∈ C := by rw [← hC'_eq] <;> exact hc
    let T := S.filter (fun x => f x = c)
    have hT_sub : (T : Set Plane) ⊆ Metric.closedBall c (2 * δ) := by
      intro y hy
      have hfy : f y = c := (Finset.mem_filter.mp hy).2
      have h : dist y c ≤ 2 * δ := by rw [← hfy]; exact hf2 y (Finset.mem_filter.mp hy).1
      exact h
    have hT_sep : Set.Pairwise (T : Set Plane) (fun y z => δ ≤ dist y z) := by
      intro x hx y hy hxy
      have h_x_in_S : x ∈ (S : Set Plane) := (Finset.mem_filter.mp hx).1
      have h_y_in_S : y ∈ (S : Set Plane) := (Finset.mem_filter.mp hy).1
      exact h_sep h_x_in_S h_y_in_S hxy
    exact ball_separated_card_le_25_nonstrict hδ_pos hT_sub hT_sep
  have h_disj : (C' : Set Plane).PairwiseDisjoint (fun c : Plane => S.filter (fun x => f x = c)) := by
    intro c1 _ c2 _ hne
    simp only [Finset.disjoint_left]
    intro x hx1 hx2
    have h1 : f x = c1 := (Finset.mem_filter.mp hx1).2
    have h2 : f x = c2 := (Finset.mem_filter.mp hx2).2
    rw [h1] at h2; exact hne h2
  have h_biUnion_eq : S = C'.biUnion (fun c => S.filter (fun x => f x = c)) := by
    ext x
    simp only [Finset.mem_biUnion]
    constructor
    · intro hx
      have h_fx_in_C : f x ∈ C := hf1 x hx
      have h_fx_in_C' : f x ∈ C' := by
        have h : f x ∈ (C' : Set Plane) := by rw [hC'_eq] <;> exact h_fx_in_C
        simpa using h
      exact ⟨f x, h_fx_in_C', by simp [hx]⟩
    · rintro ⟨c, _, hx⟩
      exact (Finset.mem_filter.mp hx).1
  have hS_card_eq : S.card = ∑ c ∈ C', (S.filter (fun x => f x = c)).card := by
    have h_eq : S = C'.biUnion (fun c => S.filter (fun x => f x = c)) := h_biUnion_eq
    have h_sum : (C'.biUnion (fun c => S.filter (fun x => f x = c))).card =
        ∑ c ∈ C', (S.filter (fun x => f x = c)).card := Finset.card_biUnion h_disj
    exact Eq.trans (congr_arg Finset.card h_eq) h_sum
  have hS_le : S.card ≤ 25 * C'.card := by
    rw [hS_card_eq]
    have h : ∑ c ∈ C', (S.filter (fun x => f x = c)).card ≤ ∑ c ∈ C', 25 := by
      apply Finset.sum_le_sum
      intro c hc
      exact h_fiber c hc
    calc
      ∑ c ∈ C', (S.filter (fun x => f x = c)).card ≤ ∑ c ∈ C', 25 := h
      _ = 25 * C'.card := by simp [Finset.sum_const] <;> ring
  have hC_le_pack : (C'.card : ENNReal) ≤ Metric.packingNumber ε (S : Set Plane) := by
    have h : C.encard ≤ Metric.packingNumber ε (S : Set Plane) :=
      Metric.IsSeparated.encard_le_packingNumber hC_sub hC_sep
    have h10 : (C'.card : ENNReal) = C.encard := by
      have h11 : (C' : Set Plane) = C := hC'_eq
      have h12 : (C'.card : ENNReal) = (C' : Set Plane).encard := by simp
      rw [h12, h11]
    rw [h10]
    simpa using h
  have h_pack_le_cov : Metric.packingNumber ε (S : Set Plane) ≤
      Metric.externalCoveringNumber δ.toNNReal (S : Set Plane) :=
    Metric.packingNumber_two_mul_le_externalCoveringNumber δ.toNNReal (S : Set Plane)
  calc (S.card : ENNReal)
    ≤ (25 * C'.card : ENNReal) := by exact_mod_cast hS_le
    _ = 25 * (C'.card : ENNReal) := by ring
    _ ≤ 25 * Metric.packingNumber ε (S : Set Plane) := by gcongr
    _ ≤ 25 * Metric.externalCoveringNumber δ.toNNReal (S : Set Plane) := by gcongr

/-! ========================================================================
   A5 data bounds
   ======================================================================== -/

/-- Lower bound on I = Σ_Q |Cπ(Q)| from A5 data. -/
lemma a5_I_lower {Δ δ s t ε : ℝ} (hΔ_pos : 0 < Δ)
    (a5 : A5_Output Δ δ s t ε) :
    Real.rpow Δ (-(s + t) + 73 * ε) ≤ (∑ Q ∈ a5.Qset, (a5Cpi a5 Q).card : ℝ) := by
  have h1 : ∀ Q ∈ a5.Qset, Real.rpow Δ (-s + 23 * ε) ≤ ((a5Cpi a5 Q).card : ℝ) := by
    intro Q hQ
    have h2 : a5Cpi a5 Q = (a5.perSquare Q hQ).C_Q_pi ∩ a5.C_global := by
      simp [a5Cpi, hQ]
    rw [h2]
    exact a5.hG3_intersection Q hQ
  have h3 : (a5.Qset.card : ℝ) * Real.rpow Δ (-s + 23 * ε) ≤
      (∑ Q ∈ a5.Qset, (a5Cpi a5 Q).card : ℝ) := by
    have h4 : ∑ Q ∈ a5.Qset, ((a5Cpi a5 Q).card : ℝ) ≥
        ∑ Q ∈ a5.Qset, Real.rpow Δ (-s + 23 * ε) := by
      apply Finset.sum_le_sum
      intro Q hQ
      exact h1 Q hQ
    have h5 : ∑ Q ∈ a5.Qset, Real.rpow Δ (-s + 23 * ε) =
        (a5.Qset.card : ℝ) * Real.rpow Δ (-s + 23 * ε) := by
      simp [Finset.sum_const] <;> ring
    linarith
  have h6 : Real.rpow Δ (-t + 50 * ε) ≤ (a5.Qset.card : ℝ) := a5.hQset_card_lower
  have h7 : 0 < Real.rpow Δ (-s + 23 * ε) := Real.rpow_pos_of_pos hΔ_pos _
  calc
    Real.rpow Δ (-(s + t) + 73 * ε)
      = Real.rpow Δ (-t + 50 * ε) * Real.rpow Δ (-s + 23 * ε) := by
      have h_add : (-(s + t) + 73 * ε) = (-t + 50 * ε) + (-s + 23 * ε) := by ring
      rw [h_add]
      exact Real.rpow_add hΔ_pos (-t + 50 * ε) (-s + 23 * ε)
    _ ≤ (a5.Qset.card : ℝ) * Real.rpow Δ (-s + 23 * ε) := by gcongr
    _ ≤ (∑ Q ∈ a5.Qset, (a5Cpi a5 Q).card : ℝ) := h3

/-- C_global is nonempty. -/
lemma a5_Cglobal_nonempty {Δ δ s t ε : ℝ} (hΔ_pos : 0 < Δ)
    (a5 : A5_Output Δ δ s t ε) : a5.C_global.Nonempty := by
  have h2 : a5.Qset.Nonempty := a5.hQset_sset.1
  rcases h2 with ⟨Q, hQ⟩
  have h4 : 0 < (a5Cpi a5 Q).card := by
    have h5 : a5Cpi a5 Q = (a5.perSquare Q hQ).C_Q_pi ∩ a5.C_global := by
      simp [a5Cpi, hQ]
    have h6 : Real.rpow Δ (-s + 23 * ε) ≤ ((a5Cpi a5 Q).card : ℝ) := by
      rw [h5]; exact a5.hG3_intersection Q hQ
    have h7 : 0 < Real.rpow Δ (-s + 23 * ε) := Real.rpow_pos_of_pos hΔ_pos _
    exact_mod_cast lt_of_lt_of_le h7 h6
  have h3 : (a5Cpi a5 Q).Nonempty := Finset.card_pos.mp h4
  rcases h3 with ⟨T, hT⟩
  have h8 : a5Cpi a5 Q ⊆ a5.C_global := by
    simp [a5Cpi, hQ] <;> tauto
  exact ⟨T, h8 hT⟩

/-! ========================================================================
   Cardinality lower bound helper
   ======================================================================== -/

lemma a7_card_lower_helper
    {Δ s t ε : ℝ} (hΔ_pos : 0 < Δ)
    (u : ℝ) (I L : ℝ) (Q0_card : ℝ)
    (hI_lower : Real.rpow Δ (-(s + t) + 73 * ε) ≤ I)
    (hL_upper : L ≤ Real.rpow Δ (-2 * s - 3 * ε))
    (hL_pos : 0 < L)
    (hQ0_card : I ≤ 4 * L * Q0_card)
    (hu_eq : u = t - s) :
    (1 / 4 : ℝ) * Real.rpow Δ (-u + 76 * ε) ≤ Q0_card := by
  have h_posR : 0 < Real.rpow Δ (-2 * s - 3 * ε) := Real.rpow_pos_of_pos hΔ_pos _
  have h1 : I / (4 * L) ≤ Q0_card := by
    have h2 : I ≤ 4 * L * Q0_card := hQ0_card
    have h3 : 0 < 4 * L := by positivity
    have h4 : I / (4 * L) ≤ (4 * L * Q0_card) / (4 * L) := by gcongr
    have h5 : (4 * L * Q0_card) / (4 * L) = Q0_card := by
      field_simp [h3.ne'] <;> ring
    rw [h5] at h4
    exact h4
  have h_div_card : Real.rpow Δ (-(s + t) + 73 * ε) / Real.rpow Δ (-2 * s - 3 * ε) =
      Real.rpow Δ (-u + 76 * ε) := by
    have h_exp : (-(s + t) + 73 * ε) - (-2 * s - 3 * ε) = -u + 76 * ε := by
      rw [hu_eq] <;> ring
    have h : Real.rpow Δ (-(s + t) + 73 * ε) / Real.rpow Δ (-2 * s - 3 * ε) =
        Real.rpow Δ ((-(s + t) + 73 * ε) - (-2 * s - 3 * ε)) := by
      exact (rpow_sub_eq hΔ_pos (-(s + t) + 73 * ε) (-2 * s - 3 * ε)).symm
    rw [h, h_exp]
  have h_posL : 0 < L := hL_pos
  have h_num_nonneg : 0 ≤ Real.rpow Δ (-(s + t) + 73 * ε) := Real.rpow_nonneg hΔ_pos.le _
  have h_denom : 4 * L ≤ 4 * Real.rpow Δ (-2 * s - 3 * ε) := by gcongr
  have h_step2 : Real.rpow Δ (-(s + t) + 73 * ε) / (4 * Real.rpow Δ (-2 * s - 3 * ε)) ≤
      Real.rpow Δ (-(s + t) + 73 * ε) / (4 * L) := by
    exact div_le_div_of_nonneg_left h_num_nonneg (by positivity) h_denom
  have h_step1 : Real.rpow Δ (-(s + t) + 73 * ε) / (4 * L) ≤ I / (4 * L) := by
    exact div_le_div_of_nonneg_right hI_lower (by positivity)
  have h_final : Real.rpow Δ (-(s + t) + 73 * ε) / (4 * Real.rpow Δ (-2 * s - 3 * ε)) =
      (1 / 4 : ℝ) * Real.rpow Δ (-u + 76 * ε) := by
    have h : Real.rpow Δ (-(s + t) + 73 * ε) / (4 * Real.rpow Δ (-2 * s - 3 * ε)) =
        (1 / 4 : ℝ) * (Real.rpow Δ (-(s + t) + 73 * ε) / Real.rpow Δ (-2 * s - 3 * ε)) := by ring
    rw [h, h_div_card] <;> ring
  linarith [h_step1, h_step2, h_final, h1]

/-! ========================================================================
   Distance upper bound for squareCenter
   ======================================================================== -/

/-- Physical distance between square centers is at most √2·Δ times index distance. -/
lemma squareCenter_dist_upper {Δ : ℝ} (hΔ_pos : 0 < Δ)
    (Q1 Q2 : CoarseSquare Δ) :
    dist (squareCenter Δ Q1) (squareCenter Δ Q2) ≤ Real.sqrt 2 * Δ * dist Q1 Q2 := by
  let a : ℝ := |(Q1.1 : ℝ) - (Q2.1 : ℝ)|
  let b : ℝ := |(Q1.2 : ℝ) - (Q2.2 : ℝ)|
  have h_idx : dist Q1 Q2 = max a b := by simp [dist, a, b] <;> rfl
  let x := squareCenter Δ Q1 - squareCenter Δ Q2
  have h_norm2 : ‖x‖ = Real.sqrt (|x 0|^2 + |x 1|^2) := by
    rw [PiLp.norm_eq_of_L2] <;> simp [Fin.sum_univ_two] <;> rfl
  have h_coord0 : |x 0| = Δ * a := by
    have h5 : x 0 = Δ * ((Q1.1 : ℝ) - (Q2.1 : ℝ)) := by
      simp [x, Lagoon.squareCenter_zero] <;> ring
    rw [h5, abs_mul, abs_of_pos hΔ_pos] <;> rfl
  have h_coord1 : |x 1| = Δ * b := by
    have h6 : x 1 = Δ * ((Q1.2 : ℝ) - (Q2.2 : ℝ)) := by
      simp [x, Lagoon.squareCenter_one] <;> ring
    rw [h6, abs_mul, abs_of_pos hΔ_pos] <;> rfl
  have h_a_le_max : a ≤ max a b := le_max_left a b
  have h_b_le_max : b ≤ max a b := le_max_right a b
  have h_sq : a^2 + b^2 ≤ 2 * (max a b)^2 := by
    have h1 : a^2 ≤ (max a b)^2 := by gcongr <;> exact h_a_le_max
    have h2 : b^2 ≤ (max a b)^2 := by gcongr <;> exact h_b_le_max
    linarith
  have h_main : Real.sqrt (a^2 + b^2) ≤ Real.sqrt 2 * (max a b) := by
    have h_nonneg : 0 ≤ max a b := by positivity
    have h : Real.sqrt (a^2 + b^2) ≤ Real.sqrt (2 * (max a b)^2) := Real.sqrt_le_sqrt h_sq
    have h2 : Real.sqrt (2 * (max a b)^2) = Real.sqrt 2 * (max a b) := by
      have h_pos2 : 0 ≤ max a b := h_nonneg
      have h_eq : (Real.sqrt 2 * (max a b))^2 = 2 * (max a b)^2 := by
        calc (Real.sqrt 2 * (max a b))^2
          = (Real.sqrt 2)^2 * (max a b)^2 := by ring
        _ = 2 * (max a b)^2 := by rw [Real.sq_sqrt (by positivity)] <;> ring
      rw [←h_eq, Real.sqrt_sq (by positivity)]
    rw [h2] at h
    exact h
  have h_dist : dist (squareCenter Δ Q1) (squareCenter Δ Q2) = ‖x‖ := by
    simp [x, dist_eq_norm]
  rw [h_dist, h_norm2]
  have h4 : |x 0|^2 + |x 1|^2 = Δ^2 * (a^2 + b^2) := by
    rw [h_coord0, h_coord1] <;> ring
  rw [h4]
  have h5 : Real.sqrt (Δ^2 * (a^2 + b^2)) = Δ * Real.sqrt (a^2 + b^2) := by
    have h6 : 0 ≤ Δ := by linarith
    have h_pos : 0 ≤ Δ * Real.sqrt (a^2 + b^2) := by positivity
    have h_eq : (Δ * Real.sqrt (a^2 + b^2))^2 = Δ^2 * (a^2 + b^2) := by
      calc (Δ * Real.sqrt (a^2 + b^2))^2
        = Δ^2 * (Real.sqrt (a^2 + b^2))^2 := by ring
      _ = Δ^2 * (a^2 + b^2) := by rw [Real.sq_sqrt (by positivity)] <;> ring
    rw [←h_eq, Real.sqrt_sq h_pos]
  rw [h5, h_idx]
  have h_final : Δ * Real.sqrt (a^2 + b^2) ≤ Real.sqrt 2 * Δ * (max a b) := by
    have h : Δ * Real.sqrt (a^2 + b^2) ≤ Δ * (Real.sqrt 2 * (max a b)) := mul_le_mul_of_nonneg_left h_main hΔ_pos.le
    have h_eq : Δ * (Real.sqrt 2 * (max a b)) = Real.sqrt 2 * Δ * (max a b) := by ring
    rw [h_eq] at h
    exact h
  exact h_final

/-! ========================================================================
   Full A7_Output construction using physical extraction (split version)
   ======================================================================== -/

/-- Data produced by the physical extraction and Q0 reconstruction phases. -/
structure A7_ExtractionResult (Δ δ s t ε : ℝ) (a5 : A5_Output Δ δ s t ε) where
  u : ℝ
  hu_pos : 0 < u
  hu_eq : u = t - s
  hu_lt_two : u < 2
  hε_pos' : 0 < ε
  T0 : CoarseTube
  Q0 : Finset (CoarseSquare Δ)
  Q0_phys : Finset Plane
  A_phys : ℝ
  A_idx : ℝ
  hT0_in : T0 ∈ a5.C_global
  hQ0_sub_Qset : Q0 ⊆ a5.Qset
  hQ0_phys_eq : Q0.image (squareCenter Δ) = Q0_phys
  hT0_incidence : ∀ Q ∈ Q0, T0 ∈ a5Cpi a5 Q
  hQ0_card_eq : (Q0.card : ℝ) = (Q0_phys.card : ℝ)
  hQ0_nonempty : Q0.Nonempty
  h_card_lower : (1 / 4 : ℝ) * Real.rpow Δ (-u + 76 * ε) ≤ (Q0_phys.card : ℝ)
  hQ0_card_lower_final : Real.rpow Δ (s - t + 78 * ε) ≤ (Q0.card : ℝ)
  hA_bound : A_phys ≤ 16 * Real.rpow Δ (-u - 300 * ε)
  hA_nonneg : 0 ≤ A_phys
  hA_idx_nonneg : 0 ≤ A_idx
  hA_idx_def : A_idx = A_phys * (Real.sqrt 2 * Δ)^u
  hPE_bound : ∀ c ∈ Q0_phys, pointEnergy u Q0_phys c ≤ A_phys
  h_growth_phys : ∀ c ∈ Q0_phys, ∀ r : ℝ, Δ ≤ r →
    ((Q0_phys.filter fun c' => dist c c' ≤ r).card : ℝ) ≤ 1 + A_phys * Real.rpow r u
  hQsep : SeparatedAt Δ (a5.Qset.image (squareCenter Δ) : Set Plane)
  hQ0_sub_centers : Q0_phys ⊆ a5.Qset.image (squareCenter Δ)
  h_inj : Function.Injective (squareCenter Δ)

/-- Phase 1+2: Physical energy extraction and Q0 reconstruction. -/
def a7_extraction {Δ δ s t ε : ℝ}
    (hΔ_pos : 0 < Δ) (hΔ_lt_half : Δ < 1 / 2)
    (hs : 0 < s) (hs1 : s < 1) (hst : s < t) (ht2 : t < 2) (hε_pos : 0 < ε)
    (hδ_pos : 0 < δ) (hδ_le_Δ : δ ≤ Δ)
    (a5 : A5_Output Δ δ s t ε)
    (hQset_bdd : ∀ p ∈ a5.Qset.image (squareCenter Δ), ‖p‖ ≤ 2)
    (hQset_le_3 : ∀ (p1 : Plane) (hp1 : p1 ∈ a5.Qset.image (squareCenter Δ))
      (p2 : Plane) (hp2 : p2 ∈ a5.Qset.image (squareCenter Δ)), dist p1 p2 ≤ 3)
    (h_log_absorb : 4 * Real.log (3 / Δ) + 1 ≤ Real.rpow Δ (-3 * ε))
    (h_pack_absorb : (MainAppendix.affineLine_packing_constant : ℝ) ≤ Real.rpow Δ (-ε))
    (h_const_absorb : (MainAppendix.affineLine_packing_constant : ℝ)^2 * ((800 * (53 : ℝ)) : ℝ)^s * (4 : ℝ)^t + 1 ≤ Real.rpow Δ (-ε))
    (h_small_half : Real.rpow Δ ε ≤ 1 / 2) :
    A7_ExtractionResult Δ δ s t ε a5 := by
  classical
  let u : ℝ := t - s
  have hu_pos : 0 < u := by linarith
  let I : ℝ := ∑ Q ∈ a5.Qset, (a5Cpi a5 Q).card
  let L : ℝ := (a5.C_global.card : ℝ)
  let E_phys : ℝ := ∑ T ∈ a5.C_global, pairEnergy u ((a5Fiber a5 T).image (squareCenter Δ))
  let A_phys : ℝ := 4 * E_phys / I
  let centers : Finset Plane := a5.Qset.image (squareCenter Δ)
  let fiber_phys (T : CoarseTube) : Finset Plane := (a5Fiber a5 T).image (squareCenter Δ)
  have hI_pos : 0 < I := by
    have h1 : a5.Qset.Nonempty := a5.hQset_sset.1
    have h2 : ∀ Q ∈ a5.Qset, 0 < (a5Cpi a5 Q).card := by
      intro Q hQ
      have h3 : Real.rpow Δ (-s + 23 * ε) ≤ ((a5Cpi a5 Q).card : ℝ) := by
        have h4 : a5Cpi a5 Q = (a5.perSquare Q hQ).C_Q_pi ∩ a5.C_global := by simp [a5Cpi, hQ]
        rw [h4]; exact a5.hG3_intersection Q hQ
      have h4 : 0 < Real.rpow Δ (-s + 23 * ε) := Real.rpow_pos_of_pos hΔ_pos _
      exact_mod_cast lt_of_lt_of_le h4 h3
    exact Finset.sum_pos (fun Q hQ => by exact_mod_cast h2 Q hQ) h1
  have hE_nonneg : 0 ≤ E_phys := by
    apply Finset.sum_nonneg; intro T _; exact pairEnergy_nonneg
  have hL_pos : 0 < L := by
    dsimp only [L]
    have h : a5.C_global.Nonempty := a5_Cglobal_nonempty hΔ_pos a5
    exact_mod_cast Finset.card_pos.mpr h
  have hQsep : SeparatedAt Δ (centers : Set Plane) := by
    intro c1 hc1 c2 hc2 hne
    rcases Finset.mem_image.mp hc1 with ⟨Q1, hQ1, rfl⟩
    rcases Finset.mem_image.mp hc2 with ⟨Q2, hQ2, rfl⟩
    have hQne : Q1 ≠ Q2 := by intro h; apply hne; rw [h]
    have h_dist : Δ * dist Q1 Q2 ≤ dist (squareCenter Δ Q1) (squareCenter Δ Q2) :=
      squareCenter_dist_lower hΔ_pos Q1 Q2
    have h2 : (1 : ℝ) ≤ dist Q1 Q2 := coarseSquare_dist_one (Δ := Δ) hQne
    have h3 : Δ ≤ Δ * dist Q1 Q2 := by
      have h4 : Δ * 1 ≤ Δ * dist Q1 Q2 := mul_le_mul_of_nonneg_left h2 hΔ_pos.le
      have h5 : Δ * 1 = Δ := by ring
      rw [h5] at h4; exact h4
    exact le_trans h3 h_dist
  have hfiber : ∀ T ∈ a5.C_global, fiber_phys T ⊆ centers := by
    intro T _; apply Finset.image_mono; exact a5Fiber_subset (a5 := a5)
  have hcard : (a5.C_global.card : ℝ) ≤ L := by simp [L]
  have h_inj : Function.Injective (squareCenter Δ) := squareCenter_injective' hΔ_pos
  have hincidence : I ≤ ∑ T ∈ a5.C_global, ((fiber_phys T).card : ℝ) := by
    have h1 : ∀ T ∈ a5.C_global, (fiber_phys T).card = (a5Fiber a5 T).card := by
      intro T _; rw [Finset.card_image_of_injective _ h_inj]
    have h_eq : I = ∑ T ∈ a5.C_global, ((a5Fiber a5 T).card : ℝ) := by
      have h_dc := a5_double_counting a5
      have h_dc' : (∑ Q ∈ a5.Qset, (a5Cpi a5 Q).card : ℝ) =
          (∑ T ∈ a5.C_global, (a5Fiber a5 T).card : ℝ) := by exact_mod_cast h_dc
      simpa [I] using h_dc'
    rw [h_eq]
    apply Finset.sum_le_sum; intro T hT; rw [h1 T hT]
  have henergy : ∑ T ∈ a5.C_global, pairEnergy u (fiber_phys T) ≤ E_phys := by rfl
  have h_main : ∃ (T0 : CoarseTube), T0 ∈ a5.C_global ∧
      ∃ (Q0_phys : Finset Plane),
        Q0_phys ⊆ fiber_phys T0 ∧
        I ≤ 4 * L * (Q0_phys.card : ℝ) ∧
        (∀ c ∈ Q0_phys, pointEnergy u Q0_phys c ≤ 4 * E_phys / I) ∧
        ∀ c ∈ Q0_phys, ∀ r : ℝ, Δ ≤ r →
          ((Q0_phys.filter fun c' => dist c c' ≤ r).card : ℝ) ≤
            1 + (4 * E_phys / I) * Real.rpow r u :=
    common_tube_energy_extraction
      (δ := Δ) (u := u) (I := I) (E := E_phys) (L := L)
      (Q := centers) (𝒯 := a5.C_global) (fiber := fiber_phys)
      hΔ_pos hu_pos hI_pos hE_nonneg hL_pos hQsep hfiber hcard hincidence henergy
  let T0 : CoarseTube := Classical.choose h_main
  have hT0_spec : T0 ∈ a5.C_global ∧
      ∃ (Q0_phys : Finset Plane),
        Q0_phys ⊆ fiber_phys T0 ∧
        I ≤ 4 * L * (Q0_phys.card : ℝ) ∧
        (∀ c ∈ Q0_phys, pointEnergy u Q0_phys c ≤ 4 * E_phys / I) ∧
        ∀ c ∈ Q0_phys, ∀ r : ℝ, Δ ≤ r →
          ((Q0_phys.filter fun c' => dist c c' ≤ r).card : ℝ) ≤
            1 + (4 * E_phys / I) * Real.rpow r u :=
    Classical.choose_spec h_main
  let Q0_phys : Finset Plane := Classical.choose hT0_spec.2
  have hQ0_spec : Q0_phys ⊆ fiber_phys T0 ∧
        I ≤ 4 * L * (Q0_phys.card : ℝ) ∧
        (∀ c ∈ Q0_phys, pointEnergy u Q0_phys c ≤ 4 * E_phys / I) ∧
        ∀ c ∈ Q0_phys, ∀ r : ℝ, Δ ≤ r →
          ((Q0_phys.filter fun c' => dist c c' ≤ r).card : ℝ) ≤
            1 + (4 * E_phys / I) * Real.rpow r u :=
    Classical.choose_spec hT0_spec.2
  have hT0_in : T0 ∈ a5.C_global := hT0_spec.1
  have hQ0_sub_fiber : Q0_phys ⊆ fiber_phys T0 := hQ0_spec.1
  have hQ0_card : I ≤ 4 * L * (Q0_phys.card : ℝ) := hQ0_spec.2.1
  have hPE_bound : ∀ c ∈ Q0_phys, pointEnergy u Q0_phys c ≤ 4 * E_phys / I := hQ0_spec.2.2.1
  have h_growth_phys : ∀ c ∈ Q0_phys, ∀ r : ℝ, Δ ≤ r →
      ((Q0_phys.filter fun c' => dist c c' ≤ r).card : ℝ) ≤
        1 + (4 * E_phys / I) * Real.rpow r u := hQ0_spec.2.2.2
  have hA_bound : A_phys ≤ 16 * Real.rpow Δ (-u - 300 * ε) := by
    have hE : E_phys ≤ 4 * Real.rpow Δ (-u - 300 * ε) * I :=
      physical_energy_bound hΔ_pos hΔ_lt_half hs hs1 hst ht2 hε_pos
        hδ_pos hδ_le_Δ a5
        hQset_bdd hQset_le_3 h_log_absorb h_pack_absorb h_const_absorb
        I (by simp [I])
    have h_posI : 0 < I := hI_pos
    have h : 4 * E_phys ≤ 4 * (4 * Real.rpow Δ (-u - 300 * ε) * I) := by gcongr
    have h2 : 4 * E_phys / I ≤ 4 * (4 * Real.rpow Δ (-u - 300 * ε) * I) / I := by
      exact div_le_div_of_nonneg_right h h_posI.le
    have h3 : 4 * (4 * Real.rpow Δ (-u - 300 * ε) * I) / I = 16 * Real.rpow Δ (-u - 300 * ε) := by
      field_simp [h_posI.ne'] <;> ring
    rw [h3] at h2; exact h2
  have hA_nonneg : 0 ≤ A_phys := by
    dsimp only [A_phys]; exact div_nonneg (mul_nonneg (by norm_num) hE_nonneg) hI_pos.le
  have hI_lower : Real.rpow Δ (-(s + t) + 73 * ε) ≤ I := a5_I_lower hΔ_pos a5
  have hL_upper : L ≤ Real.rpow Δ (-2 * s - 3 * ε) := a5.hG1_Cglobal_size
  have h_card_lower : (1 / 4 : ℝ) * Real.rpow Δ (-u + 76 * ε) ≤ (Q0_phys.card : ℝ) :=
    a7_card_lower_helper hΔ_pos u I L (Q0_phys.card : ℝ) hI_lower hL_upper hL_pos hQ0_card rfl
  -- Reconstruct Q0 from Q0_phys
  let Q0 : Finset (CoarseSquare Δ) :=
    (a5Fiber a5 T0).filter (fun Q => squareCenter Δ Q ∈ Q0_phys)
  have hQ0_idx_sub_fiber : Q0 ⊆ a5Fiber a5 T0 := Finset.filter_subset _ _
  have hQ0_sub_Qset : Q0 ⊆ a5.Qset := hQ0_idx_sub_fiber.trans (a5Fiber_subset (a5 := a5))
  have hQ0_phys_eq : Q0.image (squareCenter Δ) = Q0_phys := by
    ext x; simp only [Finset.mem_image]
    constructor
    · rintro ⟨Q, hQ, rfl⟩; exact (Finset.mem_filter.mp hQ).2
    · intro hx
      have h_in_fiber : x ∈ (a5Fiber a5 T0).image (squareCenter Δ) := by
        have h1 : x ∈ fiber_phys T0 := hQ0_sub_fiber hx
        exact h1
      rcases Finset.mem_image.mp h_in_fiber with ⟨Q, hQ_fiber, rfl⟩
      have hQ_in_Q0 : Q ∈ Q0 := by
        simp only [Q0, Finset.mem_filter]; exact ⟨hQ_fiber, hx⟩
      exact ⟨Q, hQ_in_Q0, rfl⟩
  have hT0_incidence : ∀ Q ∈ Q0, T0 ∈ a5Cpi a5 Q := by
    intro Q hQ
    have hQ_in_fiber : Q ∈ a5Fiber a5 T0 := hQ0_idx_sub_fiber hQ
    have h2 : Q ∈ a5.Qset ∧ T0 ∈ a5Cpi a5 Q := by
      simpa [a5Fiber, Finset.mem_filter] using hQ_in_fiber
    exact h2.2
  have hQ0_card_eq : (Q0.card : ℝ) = (Q0_phys.card : ℝ) := by
    have h : Q0.card = Q0_phys.card := by
      rw [←Finset.card_image_of_injective Q0 h_inj, hQ0_phys_eq]
    exact_mod_cast h
  have hQ0_nonempty : Q0.Nonempty := by
    have h_pos : 0 < (Q0_phys.card : ℝ) := by
      have h4 : 0 < (1 / 4 : ℝ) * Real.rpow Δ (-u + 76 * ε) := mul_pos (by norm_num) (Real.rpow_pos_of_pos hΔ_pos _)
      exact lt_of_lt_of_le h4 h_card_lower
    have h5 : 0 < Q0_phys.card := by exact_mod_cast h_pos
    have h6 : Q0_phys.Nonempty := Finset.card_pos.mp h5
    rcases h6 with ⟨c, hc⟩
    rcases Finset.mem_image.mp (hQ0_phys_eq.symm ▸ hc) with ⟨Q, hQ, rfl⟩
    exact ⟨Q, hQ⟩
  -- Card lower bound with exponent s-t+73ε
  have h15ε : Real.rpow Δ (15 * ε) ≤ 1 / 4 := by
    have h3 : Real.rpow Δ (15 * ε) = (Real.rpow Δ ε)^15 := by
      have h4 : ∀ n : ℕ, Real.rpow Δ ((n : ℝ) * ε) = (Real.rpow Δ ε)^n := by
        intro n; induction n with
        | zero => simp
        | succ n ih =>
          have h5 : ((n.succ : ℝ) * ε) = (n : ℝ) * ε + ε := by simp [Nat.cast_add, Nat.cast_one] <;> ring
          rw [h5, rpow_add_eq hΔ_pos] <;> rw [ih] <;> ring
      exact h4 15
    rw [h3]
    have h6 : 0 ≤ Real.rpow Δ ε := Real.rpow_nonneg hΔ_pos.le ε
    have h7 : Real.rpow Δ ε ≤ 1 / 2 := h_small_half
    have h8 : (Real.rpow Δ ε)^15 ≤ (1 / 2 : ℝ)^15 := by gcongr
    have h9 : (1 / 2 : ℝ)^15 ≤ 1 / 4 := by norm_num
    exact h8.trans h9
  have hQ0_card_lower_final : Real.rpow Δ (s - t + 78 * ε) ≤ (Q0.card : ℝ) := by
    have h10 : Real.rpow Δ (s - t + 78 * ε) ≤ (1 / 4 : ℝ) * Real.rpow Δ (s - t + 76 * ε) := by
      have h11 : Real.rpow Δ (s - t + 78 * ε) =
          Real.rpow Δ (s - t + 76 * ε) * Real.rpow Δ (2 * ε) := by
        have h := rpow_add_eq hΔ_pos (s - t + 76 * ε) (2 * ε)
        have h' : (s - t + 76 * ε) + (2 * ε) = s - t + 78 * ε := by ring
        rw [h'] at h; exact h
      rw [h11]
      have h_pos : 0 < Real.rpow Δ (s - t + 76 * ε) := Real.rpow_pos_of_pos hΔ_pos _
      have h2ε : Real.rpow Δ (2 * ε) ≤ 1 / 4 := by
        have h_pos2 : 0 ≤ Δ := by linarith
        have h : Real.rpow Δ (2 * ε) = Real.rpow Δ ε * Real.rpow Δ ε := by
          have h_eq : (2 * ε) = ε + ε := by ring
          rw [h_eq]
          exact rpow_add_eq hΔ_pos ε ε
        rw [h]
        have h3 : 0 ≤ Real.rpow Δ ε := Real.rpow_nonneg h_pos2 ε
        have h4 : Real.rpow Δ ε ≤ 1 / 2 := h_small_half
        nlinarith
      nlinarith
    have h12 : (1 / 4 : ℝ) * Real.rpow Δ (s - t + 76 * ε) ≤ (Q0.card : ℝ) := by
      rw [hQ0_card_eq]; simpa [u] using h_card_lower
    exact h10.trans h12
  let A_idx : ℝ := A_phys * (Real.sqrt 2 * Δ)^u
  have hA_idx_nonneg : 0 ≤ A_idx := by
    dsimp only [A_idx]
    have h1 : 0 ≤ A_phys := hA_nonneg
    have h2 : 0 ≤ (Real.sqrt 2 * Δ)^u := Real.rpow_nonneg (by positivity) u
    exact mul_nonneg h1 h2
  have hQ0_sub_centers : Q0_phys ⊆ centers := hQ0_sub_fiber.trans (hfiber T0 hT0_in)
  exact {
    u := u, hu_pos := hu_pos, hu_eq := by rfl, hu_lt_two := by linarith [hst, ht2], hε_pos' := hε_pos, T0 := T0, Q0 := Q0, Q0_phys := Q0_phys,
    A_phys := A_phys, A_idx := A_idx,
    hT0_in := hT0_in, hQ0_sub_Qset := hQ0_sub_Qset,
    hQ0_phys_eq := hQ0_phys_eq, hT0_incidence := hT0_incidence,
    hQ0_card_eq := hQ0_card_eq, hQ0_nonempty := hQ0_nonempty,
    h_card_lower := h_card_lower, hQ0_card_lower_final := hQ0_card_lower_final,
    hA_bound := hA_bound, hA_nonneg := hA_nonneg, hA_idx_nonneg := hA_idx_nonneg,
    hA_idx_def := by dsimp only [A_idx] <;> rfl,
    hPE_bound := hPE_bound, h_growth_phys := h_growth_phys,
    hQsep := hQsep, hQ0_sub_centers := hQ0_sub_centers, h_inj := h_inj
  }


end

end DirecretisedFurstenbergEstimate.AppendixA
