module

/-
  Ball-growth and packing lemmas for δ-separated sets, extracted QTTC-free.

  Provides:
  - SeparatedAt: pairwise distance ≥ r
  - IsFiniteDeltaSSet: finite δ-separated set with cardinal Frostman growth
  - Packing bounds: at most 9 δ-separated points in a δ-ball (ℝ×ℝ and EuclideanPlane)
  - Packing-to-covering bound: |S| ≤ K * covering_δ(S)
  - IsDeltaSSet → finite ball-growth subset (ℝ×ℝ and EuclideanPlane)
  - IsDeltaSSet ↔ IsFiniteDeltaSSet conversions

  Whiteprint node: Phase4 / SSetBridges / BallGrowth
  Dependencies: discretised_furstenberg_estimate, Mathlib
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal


noncomputable section

namespace DirecretisedFurstenbergEstimate.SSetBridges

/-- Pairwise separation: all distinct points in P are at distance ≥ r. -/
def SeparatedAt {X : Type*} [PseudoMetricSpace X] (r : ℝ) (P : Set X) : Prop :=
  P.Pairwise fun x y => r ≤ dist x y

/-- A finite δ-separated set with cardinal Frostman (ball-growth) estimate. -/
def IsFiniteDeltaSSet {X : Type*} [PseudoMetricSpace X]
    (δ s C : ℝ) (P : Finset X) : Prop :=
  P.Nonempty ∧ 0 < δ ∧ 1 ≤ C ∧ 0 ≤ s ∧
    SeparatedAt δ (P : Set X) ∧
    ∀ x : X, ∀ r : ℝ, δ ≤ r →
      ((P.filter fun y => dist y x ≤ r).card : ℝ) ≤
        C * r ^ s * (P.card : ℝ)

/-! ### Local packing in ℝ×ℝ with sup metric -/

lemma same_third_bound {δ c a b : ℝ} (hδ : 0 < δ)
    (ha : |a - c| ≤ δ) (hb : |b - c| ≤ δ)
    (h_eq : (if a < c - δ / 3 then (0 : ℤ) else if a < c + δ / 3 then 1 else 2) =
            (if b < c - δ / 3 then (0 : ℤ) else if b < c + δ / 3 then 1 else 2)) :
    |a - b| ≤ 2 * δ / 3 := by
  let f : ℝ → ℤ := fun t => if t < c - δ / 3 then 0 else if t < c + δ / 3 then 1 else 2
  have hf : f a = f b := h_eq
  have h1 : c - δ ≤ a := by linarith [abs_le.mp ha]
  have h2 : a ≤ c + δ := by linarith [abs_le.mp ha]
  have h3 : c - δ ≤ b := by linarith [abs_le.mp hb]
  have h4 : b ≤ c + δ := by linarith [abs_le.mp hb]
  by_cases h : a < c - δ / 3
  · have hfa : f a = 0 := by simp [f, h]
    rw [hfa] at hf
    have hb' : b < c - δ / 3 := by simp only [f] at hf <;> split_ifs at hf <;> tauto
    cases' abs_cases (a - b) with h7 h7 <;> linarith
  · by_cases h6 : a < c + δ / 3
    · have hfa : f a = 1 := by simp [f, h, h6] <;> split_ifs <;> tauto
      rw [hfa] at hf
      have hb1 : ¬(b < c - δ / 3) := by simp only [f] at hf <;> split_ifs at hf <;> tauto
      have hb2 : b < c + δ / 3 := by simp only [f] at hf <;> split_ifs at hf <;> tauto
      have hla1 : c - δ / 3 ≤ a := by linarith
      have hlb1 : c - δ / 3 ≤ b := by linarith
      cases' abs_cases (a - b) with h7 h7 <;> linarith
    · have hfa : f a = 2 := by simp [f, h, h6] <;> split_ifs <;> tauto
      rw [hfa] at hf
      have hb3 : ¬(b < c + δ / 3) := by simp only [f] at hf <;> split_ifs at hf <;> tauto
      have h8 : c + δ / 3 ≤ a := by linarith
      have h9 : c + δ / 3 ≤ b := by linarith
      cases' abs_cases (a - b) with h10 h10 <;> linarith

lemma max_points_in_delta_ball {δ : ℝ} (hδ_pos : 0 < δ)
    (S : Finset (ℝ × ℝ)) (hsep : SeparatedAt δ (S : Set (ℝ × ℝ)))
    (x : ℝ × ℝ) :
    (S.filter (fun y => dist y x ≤ δ)).card ≤ 9 := by
  let B : Finset (ℝ × ℝ) := S.filter (fun y => dist y x ≤ δ)
  have hB_sub : (B : Set (ℝ × ℝ)) ⊆ (S : Set (ℝ × ℝ)) := by
    intro y hy; exact (Finset.mem_filter.mp hy).1
  have hB_sep : SeparatedAt δ (B : Set (ℝ × ℝ)) := hsep.mono hB_sub
  let cell : (ℝ × ℝ) → (ℤ × ℤ) := fun y =>
    ( if y.1 < x.1 - δ / 3 then 0 else if y.1 < x.1 + δ / 3 then 1 else 2
    , if y.2 < x.2 - δ / 3 then 0 else if y.2 < x.2 + δ / 3 then 1 else 2 )
  have h_inj : Set.InjOn cell (B : Set (ℝ × ℝ)) := by
    intro y hy z hz h_eq
    by_cases hne : y ≠ z
    · have h_yin : dist y x ≤ δ := (Finset.mem_filter.mp hy).2
      have h_zin : dist z x ≤ δ := (Finset.mem_filter.mp hz).2
      have h_y1 : |y.1 - x.1| ≤ δ := by
        have h : dist y x = max (|y.1 - x.1|) (|y.2 - x.2|) := by simp [dist_eq_norm] <;> rfl
        rw [h] at h_yin; exact le_trans (le_max_left _ _) h_yin
      have h_y2 : |y.2 - x.2| ≤ δ := by
        have h : dist y x = max (|y.1 - x.1|) (|y.2 - x.2|) := by simp [dist_eq_norm] <;> rfl
        rw [h] at h_yin; exact le_trans (le_max_right _ _) h_yin
      have h_z1 : |z.1 - x.1| ≤ δ := by
        have h : dist z x = max (|z.1 - x.1|) (|z.2 - x.2|) := by simp [dist_eq_norm] <;> rfl
        rw [h] at h_zin; exact le_trans (le_max_left _ _) h_zin
      have h_z2 : |z.2 - x.2| ≤ δ := by
        have h : dist z x = max (|z.1 - x.1|) (|z.2 - x.2|) := by simp [dist_eq_norm] <;> rfl
        rw [h] at h_zin; exact le_trans (le_max_right _ _) h_zin
      have h_eq1 : (cell y).1 = (cell z).1 := by rw [h_eq]
      have h_eq2 : (cell y).2 = (cell z).2 := by rw [h_eq]
      have h_d1 : |y.1 - z.1| ≤ 2 * δ / 3 := same_third_bound hδ_pos h_y1 h_z1 h_eq1
      have h_d2 : |y.2 - z.2| ≤ 2 * δ / 3 := same_third_bound hδ_pos h_y2 h_z2 h_eq2
      have h_dist : dist y z ≤ 2 * δ / 3 := by
        have h : dist y z = max (|y.1 - z.1|) (|y.2 - z.2|) := by simp [dist_eq_norm] <;> rfl
        rw [h]; exact max_le h_d1 h_d2
      have h_sep' : δ ≤ dist y z := hB_sep (Finset.mem_coe.mp hy) (Finset.mem_coe.mp hz) hne
      have h_lt : 2 * δ / 3 < δ := by linarith
      linarith
    · simpa using hne
  have h_image_subset : B.image cell ⊆ (Finset.Icc 0 2 ×ˢ Finset.Icc 0 2) := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨y, _, rfl⟩
    have h1 : (cell y).1 ∈ Finset.Icc (0 : ℤ) 2 := by
      simp [cell, Finset.mem_Icc] <;> split_ifs <;> norm_num
    have h2 : (cell y).2 ∈ Finset.Icc (0 : ℤ) 2 := by
      simp [cell, Finset.mem_Icc] <;> split_ifs <;> norm_num
    exact Finset.mem_product.mpr ⟨h1, h2⟩
  have h_card9 : (Finset.Icc 0 2 ×ˢ Finset.Icc 0 2).card = 9 := by simp [Finset.card_product]
  have h_card_B : B.card = (B.image cell).card := by rw [Finset.card_image_of_injOn h_inj]
  have h_card_image : (B.image cell).card ≤ (Finset.Icc 0 2 ×ˢ Finset.Icc 0 2).card :=
    Finset.card_le_card h_image_subset
  rw [h_card_B]; rw [h_card9] at h_card_image; exact h_card_image

/-! ### Packing-to-covering bound -/

lemma packing_cover_R2 {δ : ℝ} (hδ_pos : 0 < δ)
    {S : Finset (ℝ × ℝ)} (hsep : SeparatedAt δ (S : Set (ℝ × ℝ))) :
    (S.card : ENNReal) ≤ 9 * (Metric.externalCoveringNumber δ.toNNReal (S : Set (ℝ × ℝ)) : ENNReal) := by
  classical
  let P : ℕ → Prop := fun n => ∃ (C : Finset (ℝ × ℝ)),
    C.card = n ∧ Metric.IsCover δ.toNNReal (S : Set (ℝ × ℝ)) (C : Set (ℝ × ℝ))
  have hP : ∃ n, P n := by
    refine ⟨S.card, S, rfl, ?_⟩
    intro x hx; exact ⟨x, hx, by simp⟩
  let n₀ := Nat.find hP
  have hn₀ : P n₀ := Nat.find_spec hP
  rcases hn₀ with ⟨C₀, hC₀_card, hC₀_cover⟩
  have h_ge : ∀ (C : Set (ℝ × ℝ)), Metric.IsCover δ.toNNReal (S : Set (ℝ × ℝ)) C →
      (n₀ : ℕ∞) ≤ C.encard := by
    intro C hC
    by_cases hC_fin : C.Finite
    · let Cfin : Finset (ℝ × ℝ) := hC_fin.toFinset
      have hCfin_eq : (Cfin : Set (ℝ × ℝ)) = C := by simp [Cfin]
      have hP_Cfin : P Cfin.card := ⟨Cfin, rfl, by rwa [hCfin_eq]⟩
      have h : n₀ ≤ Cfin.card := by
        by_contra h'
        have h'' : Cfin.card < n₀ := by linarith
        have h3 : ¬P Cfin.card := Nat.find_min hP h''
        exact h3 hP_Cfin
      have h2 : C.encard = ↑Cfin.card := by rw [←hCfin_eq] <;> simp
      rw [h2]; exact_mod_cast h
    · have hC_inf : C.encard = ⊤ := by
        exact Set.encard_eq_top_iff.mpr (show ¬C.Finite from hC_fin)
      rw [hC_inf] <;> simp
  have h_n₀_le_ec : (n₀ : ℕ∞) ≤ Metric.externalCoveringNumber δ.toNNReal (S : Set (ℝ × ℝ)) := by
    have h : ∀ (C : Set (ℝ × ℝ)) (hC : Metric.IsCover δ.toNNReal (S : Set (ℝ × ℝ)) C), (n₀ : ℕ∞) ≤ C.encard := h_ge
    have h' : (n₀ : ℕ∞) ≤ ⨅ (C : Set (ℝ × ℝ)) (_ : Metric.IsCover δ.toNNReal (S : Set (ℝ × ℝ)) C), C.encard := by
      apply le_iInf_iff.mpr
      intro C
      by_cases hC : Metric.IsCover δ.toNNReal (S : Set (ℝ × ℝ)) C
      · have h_inner : (⨅ (hC' : Metric.IsCover δ.toNNReal (S : Set (ℝ × ℝ)) C), C.encard) = C.encard := by simp [hC]
        rw [h_inner]; exact h C hC
      · have h_inner : (⨅ (hC' : Metric.IsCover δ.toNNReal (S : Set (ℝ × ℝ)) C), C.encard) = ⊤ := by simp [hC]
        rw [h_inner] <;> simp
    simpa [Metric.externalCoveringNumber] using h'
  have h_card_bound : S.card ≤ 9 * n₀ := by
    have hcover : (S : Set (ℝ × ℝ)) ⊆ ⋃ c ∈ (C₀ : Set (ℝ × ℝ)), Metric.closedBall c δ := by
      intro x hx
      have h3 := hC₀_cover hx
      rcases h3 with ⟨c, hc, h4⟩
      have h5 : dist x c ≤ δ := by
        have h6 : (δ.toNNReal : ℝ) = δ := by simp [Real.toNNReal_of_nonneg hδ_pos.le]
        simpa [edist_dist, h6] using h4
      exact Set.mem_iUnion₂.mpr ⟨c, hc, h5⟩
    have h5 : S ⊆ C₀.biUnion (fun c => S.filter (fun y => dist y c ≤ δ)) := by
      intro x hx
      have h6 := hcover hx
      rcases Set.mem_iUnion₂.mp h6 with ⟨c, hc, h7⟩
      exact Finset.mem_biUnion.mpr ⟨c, hc, Finset.mem_filter.mpr ⟨hx, h7⟩⟩
    have h7 : S.card ≤ (C₀.biUnion (fun c => S.filter (fun y => dist y c ≤ δ))).card :=
      Finset.card_le_card h5
    have h8 : (C₀.biUnion (fun c => S.filter (fun y => dist y c ≤ δ))).card ≤
        ∑ c ∈ C₀, (S.filter (fun y => dist y c ≤ δ)).card := Finset.card_biUnion_le
    have h9 : ∑ c ∈ C₀, (S.filter (fun y => dist y c ≤ δ)).card ≤ ∑ c ∈ C₀, (9 : ℕ) := by
      apply Finset.sum_le_sum; intro c _; exact max_points_in_delta_ball hδ_pos S hsep c
    have h10 : ∑ c ∈ C₀, (9 : ℕ) = 9 * C₀.card := by simp [Finset.sum_const, mul_comm]
    calc S.card
      ≤ (C₀.biUnion (fun c => S.filter (fun y => dist y c ≤ δ))).card := h7
    _ ≤ ∑ c ∈ C₀, (S.filter (fun y => dist y c ≤ δ)).card := h8
    _ ≤ ∑ c ∈ C₀, (9 : ℕ) := h9
    _ = 9 * C₀.card := h10
    _ = 9 * n₀ := by rw [hC₀_card] <;> ring
  have h_main_nat : (S.card : ℕ∞) ≤ 9 * Metric.externalCoveringNumber δ.toNNReal (S : Set (ℝ × ℝ)) := by
    calc (S.card : ℕ∞)
      ≤ ↑(9 * n₀) := by exact_mod_cast h_card_bound
    _ = 9 * (n₀ : ℕ∞) := by simp [mul_comm] <;> ring
    _ ≤ 9 * Metric.externalCoveringNumber δ.toNNReal (S : Set (ℝ × ℝ)) := by gcongr
  exact_mod_cast h_main_nat

/-! ### IsDeltaSSet → ball-growth finite subset in ℝ×ℝ -/

theorem IsDeltaSSet_to_ball_growth_R2
    {δ s C : ℝ} {P : Set (ℝ × ℝ)}
    (h : IsDeltaSSet δ s C P)
    (hP_bounded : Bornology.IsBounded P) :
    ∃ (S : Finset (ℝ × ℝ)),
      (S : Set (ℝ × ℝ)) ⊆ P ∧
      S.Nonempty ∧
      SeparatedAt δ (S : Set (ℝ × ℝ)) ∧
      ((Metric.externalCoveringNumber δ.toNNReal P : ENNReal) ≤ (S.card : ENNReal)) ∧
      (∀ x, ∀ r : ℝ, δ ≤ r →
        (S.filter (fun y => dist y x ≤ r)).card ≤ (9 * C) * r ^ s * S.card) := by
  rcases h with ⟨hP_nonempty, hδ_pos, hC_pos, hs_nonneg, h_sset⟩
  let εnn : NNReal := δ.toNNReal
  have hεnn_coe : (εnn : ℝ) = δ := by simp [εnn, Real.toNNReal_of_nonneg hδ_pos.le]

  have hP_tb : TotallyBounded P := by
    rcases hP_bounded.subset_closedBall (0 : ℝ × ℝ) with ⟨R, hR⟩
    have hK : IsCompact (Metric.closedBall (0 : ℝ × ℝ) R) := isCompact_closedBall _ _
    exact hK.totallyBounded.subset hR

  have h_half_pos : 0 < εnn / 2 := by
    have hδnn_pos : 0 < εnn := by
      simpa [εnn, NNReal.coe_pos] using hδ_pos
    positivity
  rcases Metric.exists_finite_isCover_of_totallyBounded h_half_pos.ne' hP_tb with ⟨N, _, hNfin, hNcover⟩
  have h_ec_ne_top : Metric.externalCoveringNumber (εnn / 2) P ≠ ⊤ := by
    have h : Metric.externalCoveringNumber (εnn / 2) P ≤ N.encard :=
      Metric.IsCover.externalCoveringNumber_le_encard hNcover
    have h2 : N.encard ≠ ⊤ := by exact Set.encard_ne_top_iff.mpr hNfin
    exact ne_top_of_le_ne_top h2 h
  have hmul : 2 * (εnn / 2) = εnn := by
    apply NNReal.coe_injective; simp [hεnn_coe] <;> ring
  have h_pack_ne_top : Metric.packingNumber εnn P ≠ ⊤ := by
    have h : Metric.packingNumber (2 * (εnn / 2)) P ≤ Metric.externalCoveringNumber (εnn / 2) P :=
      Metric.packingNumber_two_mul_le_externalCoveringNumber (εnn / 2) P
    rw [hmul] at h; exact ne_top_of_le_ne_top h_ec_ne_top h

  let Sset : Set (ℝ × ℝ) := Metric.maximalSeparatedSet εnn P
  have hS_subset : Sset ⊆ P := Metric.maximalSeparatedSet_subset
  have hS_sep : Metric.IsSeparated εnn Sset := Metric.isSeparated_maximalSeparatedSet
  have hS_cover : Metric.IsCover εnn P Sset := Metric.isCover_maximalSeparatedSet h_pack_ne_top
  have hS_finite : Sset.Finite := by
    have h : Sset.encard ≠ ⊤ := by
      rw [Metric.encard_maximalSeparatedSet h_pack_ne_top] <;> exact h_pack_ne_top
    exact Set.encard_ne_top_iff.mp h
  have hS_nonempty_set : Sset.Nonempty := hS_cover.nonempty hP_nonempty
  classical
  let S : Finset (ℝ × ℝ) := hS_finite.toFinset
  have hS_eq : (S : Set (ℝ × ℝ)) = Sset := by simp [S]
  have hS_nonempty : S.Nonempty := by
    have h : Sset.Nonempty := hS_nonempty_set
    have h' : (S : Set (ℝ × ℝ)).Nonempty := by
      have h'' : (S : Set (ℝ × ℝ)) = Sset := hS_eq
      rw [h'']; exact h
    have h_iff : S.Nonempty ↔ (S : Set (ℝ × ℝ)).Nonempty := by
      simp [Finset.nonempty_iff_ne_empty]
    exact h_iff.mpr h'
  have hS_pos : 0 < S.card := by
    have h_pack_pos : 0 < Metric.packingNumber εnn P := Metric.packingNumber_pos_iff.mpr hP_nonempty
    have h_encard : Sset.encard = Metric.packingNumber εnn P := Metric.encard_maximalSeparatedSet h_pack_ne_top
    have h : 0 < Sset.encard := by rw [h_encard]; exact h_pack_pos
    have h2 : Sset.encard = ↑S.card := by
      have h3 : Sset = (S : Set (ℝ × ℝ)) := hS_eq.symm; rw [h3] <;> simp
    rw [h2] at h; exact_mod_cast h

  have hS_sep' : SeparatedAt δ (S : Set (ℝ × ℝ)) := by
    rw [hS_eq]
    intro x hx y hy hne
    have h_edist : (εnn : ENNReal) < edist x y := hS_sep hx hy hne
    have h_dist : edist x y = ENNReal.ofReal (dist x y) := by rw [edist_dist] <;> rfl
    rw [h_dist] at h_edist
    have h' : (εnn : ℝ) < dist x y := by exact ENNReal.coe_lt_ofReal.mp h_edist
    rw [hεnn_coe] at h'; exact le_of_lt h'

  have hcov_P_le_S : (Metric.externalCoveringNumber εnn P : ENNReal) ≤ (S.card : ENNReal) := by
    have h1 : Metric.externalCoveringNumber εnn P ≤ Sset.encard :=
      Metric.IsCover.externalCoveringNumber_le_encard hS_cover
    have h2 : Sset.encard = ↑S.card := by
      have h3 : Sset = (S : Set (ℝ × ℝ)) := hS_eq.symm; rw [h3] <;> simp
    rw [h2] at h1
    exact_mod_cast h1

  have h_ball_growth : ∀ (x : ℝ × ℝ) (r : ℝ), δ ≤ r →
      ((S.filter fun y => dist y x ≤ r).card : ℝ) ≤ (9 * C) * r ^ s * (S.card : ℝ) := by
    intro x r hr
    let S' : Finset (ℝ × ℝ) := S.filter (fun y => dist y x ≤ r)
    have hS'_sub : (S' : Set (ℝ × ℝ)) ⊆ (S : Set (ℝ × ℝ)) := by
      intro y hy; exact (Finset.mem_filter.mp hy).1
    have hS'_sep : SeparatedAt δ (S' : Set (ℝ × ℝ)) := hS_sep'.mono hS'_sub
    have h_pack_cover : (S'.card : ENNReal) ≤
        9 * (Metric.externalCoveringNumber εnn (S' : Set (ℝ × ℝ)) : ENNReal) :=
      packing_cover_R2 (hδ_pos := hδ_pos) (S := S') (hsep := hS'_sep)
    have hS'_sub_P : (S' : Set (ℝ × ℝ)) ⊆ P ∩ Metric.closedBall x r := by
      intro y hy
      have h1 : y ∈ S := (Finset.mem_filter.mp hy).1
      have h2 : dist y x ≤ r := (Finset.mem_filter.mp hy).2
      have h3 : y ∈ Sset := by
        have h4 : y ∈ (S : Set (ℝ × ℝ)) := h1
        rw [hS_eq] at h4; exact h4
      exact ⟨hS_subset h3, h2⟩
    have h_cov_mono_nat : Metric.externalCoveringNumber εnn (S' : Set (ℝ × ℝ)) ≤
        Metric.externalCoveringNumber εnn (P ∩ Metric.closedBall x r) :=
      Metric.externalCoveringNumber_mono_set hS'_sub_P
    have h_cov_mono : (Metric.externalCoveringNumber εnn (S' : Set (ℝ × ℝ)) : ENNReal) ≤
        (Metric.externalCoveringNumber εnn (P ∩ Metric.closedBall x r) : ENNReal) := by
      exact_mod_cast h_cov_mono_nat
    have h_sset' : (Metric.externalCoveringNumber εnn (P ∩ Metric.closedBall x r) : ENNReal) ≤
        ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * (Metric.externalCoveringNumber εnn P : ENNReal) :=
      h_sset x r hr
    have h_cov_S : (Metric.externalCoveringNumber εnn (S' : Set (ℝ × ℝ)) : ENNReal) ≤
        ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * (Metric.externalCoveringNumber εnn P : ENNReal) :=
      le_trans h_cov_mono h_sset'
    have h_rpow : (ENNReal.ofReal r) ^ s = ENNReal.ofReal (r ^ s) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (by linarith) (by linarith)]
    rw [h_rpow] at h_cov_S
    have h_nonneg_C : 0 ≤ C := by linarith
    have h_nonneg_r : 0 ≤ r := by linarith
    have h4 : (Metric.externalCoveringNumber εnn P : ENNReal) ≤ (S.card : ENNReal) := hcov_P_le_S
    have h_eq1 : ENNReal.ofReal C * ENNReal.ofReal (r ^ s) = ENNReal.ofReal (C * r ^ s) := by
      rw [← ENNReal.ofReal_mul h_nonneg_C]
    have h_card : (S.card : ENNReal) = ENNReal.ofReal ((S.card : ℝ)) := by simp
    have h_eq2 : ENNReal.ofReal (C * r ^ s) * (S.card : ENNReal) =
        ENNReal.ofReal ((C * r ^ s) * (S.card : ℝ)) := by
      rw [h_card, ← ENNReal.ofReal_mul (by positivity)] <;> ring
    have h9 : (9 : ENNReal) = ENNReal.ofReal 9 := by norm_cast
    have h_eq3 : (9 : ENNReal) * ENNReal.ofReal ((C * r ^ s) * (S.card : ℝ)) =
        ENNReal.ofReal (9 * ((C * r ^ s) * (S.card : ℝ))) := by
      rw [h9, ← ENNReal.ofReal_mul (by positivity)] <;> ring
    have h_eq4 : ENNReal.ofReal (9 * ((C * r ^ s) * (S.card : ℝ))) =
        ENNReal.ofReal ((9 * C) * r ^ s * (S.card : ℝ)) := by congr 1 <;> ring
    have h_final : (S'.card : ENNReal) ≤ ENNReal.ofReal ((9 * C) * r ^ s * (S.card : ℝ)) := by
      calc (S'.card : ENNReal)
        ≤ 9 * (Metric.externalCoveringNumber εnn (S' : Set (ℝ × ℝ)) : ENNReal) := h_pack_cover
      _ ≤ 9 * (ENNReal.ofReal C * ENNReal.ofReal (r ^ s) * (Metric.externalCoveringNumber εnn P : ENNReal)) := by gcongr
      _ ≤ 9 * (ENNReal.ofReal C * ENNReal.ofReal (r ^ s) * (S.card : ENNReal)) := by gcongr
      _ = (9 : ENNReal) * (ENNReal.ofReal (C * r ^ s) * (S.card : ENNReal)) := by rw [h_eq1] <;> ring
      _ = (9 : ENNReal) * ENNReal.ofReal ((C * r ^ s) * (S.card : ℝ)) := by rw [h_eq2]
      _ = ENNReal.ofReal (9 * ((C * r ^ s) * (S.card : ℝ))) := h_eq3
      _ = ENNReal.ofReal ((9 * C) * r ^ s * (S.card : ℝ)) := h_eq4
    have h_card' : (S'.card : ENNReal) = ENNReal.ofReal ((S'.card : ℝ)) := by simp
    rw [h_card'] at h_final
    have h_pos2 : 0 ≤ (9 * C) * r ^ s * (S.card : ℝ) := by positivity
    have h_iff : ENNReal.ofReal ((S'.card : ℝ)) ≤ ENNReal.ofReal ((9 * C) * r ^ s * (S.card : ℝ)) ↔
        (S'.card : ℝ) ≤ (9 * C) * r ^ s * (S.card : ℝ) :=
      ENNReal.ofReal_le_ofReal_iff h_pos2
    exact h_iff.mp h_final

  have hS_subset' : (S : Set (ℝ × ℝ)) ⊆ P := by
    rw [hS_eq]; exact hS_subset
  exact ⟨S, hS_subset', hS_nonempty, hS_sep', hcov_P_le_S, h_ball_growth⟩

/-- Convert IsDeltaSSet to IsFiniteDeltaSSet in ℝ×ℝ.
    Uses constant max(1, 9*C) to satisfy the 1 ≤ C' requirement. -/
lemma IsDeltaSSet_to_finite_delta_sset_R2
    {δ s C : ℝ} {P : Set (ℝ × ℝ)}
    (h : IsDeltaSSet δ s C P)
    (hP_bounded : Bornology.IsBounded P) :
    ∃ (S : Finset (ℝ × ℝ)),
      (S : Set (ℝ × ℝ)) ⊆ P ∧
      IsFiniteDeltaSSet δ s (max 1 (9 * C)) S := by
  rcases h with ⟨hP_nonempty, hδ_pos, hC_pos, hs_nonneg, h_sset⟩
  rcases IsDeltaSSet_to_ball_growth_R2 (⟨hP_nonempty, hδ_pos, hC_pos, hs_nonneg, h_sset⟩) hP_bounded with
    ⟨S, hS_sub, hS_nonempty, hS_sep, hS_cover, hS_growth⟩
  refine' ⟨S, hS_sub, _⟩
  let C' := max 1 (9 * C)
  have hC1 : 1 ≤ C' := le_max_left 1 (9 * C)
  have hC9 : 9 * C ≤ C' := le_max_right 1 (9 * C)
  have h_growth' : ∀ (x : ℝ × ℝ) (r : ℝ), δ ≤ r →
      ((S.filter fun y => dist y x ≤ r).card : ℝ) ≤ C' * r ^ s * (S.card : ℝ) := by
    intro x r hr
    have h : ((S.filter fun y => dist y x ≤ r).card : ℝ) ≤ (9 * C) * r ^ s * (S.card : ℝ) :=
      hS_growth x r hr
    have h' : (9 * C) * r ^ s * (S.card : ℝ) ≤ C' * r ^ s * (S.card : ℝ) := by
      have hr' : 0 ≤ r := by linarith
      have hs' : 0 ≤ s := hs_nonneg
      gcongr
    exact le_trans h h'
  exact ⟨hS_nonempty, hδ_pos, hC1, hs_nonneg, hS_sep, h_growth'⟩

/-! ### IsFiniteDeltaSSet → IsDeltaSSet in ℝ×ℝ -/

lemma IsFiniteDeltaSSet_to_delta_sset_R2
    {δ s C : ℝ} {S : Finset (ℝ × ℝ)}
    (h : IsFiniteDeltaSSet δ s C S) :
    IsDeltaSSet δ s (9 * C) (S : Set (ℝ × ℝ)) := by
  rcases h with ⟨hS_nonempty, hδ_pos, hC_ge1, hs_nonneg, hS_sep, h_growth⟩
  have hC_pos : 0 < C := by linarith
  let εnn : NNReal := δ.toNNReal
  have hεnn_coe : (εnn : ℝ) = δ := by simp [εnn, Real.toNNReal_of_nonneg hδ_pos.le]

  have h_pack_cover : (S.card : ENNReal) ≤
      9 * (Metric.externalCoveringNumber εnn (S : Set (ℝ × ℝ)) : ENNReal) :=
    packing_cover_R2 (hδ_pos := hδ_pos) (S := S) (hsep := hS_sep)

  refine' ⟨hS_nonempty, hδ_pos, by positivity, hs_nonneg, _⟩
  intro x r hr
  let S' : Finset (ℝ × ℝ) := S.filter (fun y => dist y x ≤ r)
  have hS'_eq : (S' : Set (ℝ × ℝ)) = (S : Set (ℝ × ℝ)) ∩ Metric.closedBall x r := by
    ext y; simp [S', Metric.mem_closedBall]
  have h1_nat : Metric.externalCoveringNumber εnn (S' : Set (ℝ × ℝ)) ≤ (S' : Set (ℝ × ℝ)).encard := by
    have hcover : Metric.IsCover εnn (S' : Set (ℝ × ℝ)) (S' : Set (ℝ × ℝ)) := by
      intro y hy; exact ⟨y, hy, by simp⟩
    exact Metric.IsCover.externalCoveringNumber_le_encard hcover
  have h1 : (Metric.externalCoveringNumber εnn (S' : Set (ℝ × ℝ)) : ENNReal) ≤ (S'.card : ENNReal) := by
    exact_mod_cast h1_nat
  have h2 : (S'.card : ℝ) ≤ C * r ^ s * (S.card : ℝ) := h_growth x r hr
  have h_nonneg_C : 0 ≤ C := by linarith
  have h_nonneg_r : 0 ≤ r := by linarith
  have h_nonneg_s : 0 ≤ s := hs_nonneg
  have h3 : (Metric.externalCoveringNumber εnn (S' : Set (ℝ × ℝ)) : ENNReal) ≤
      ENNReal.ofReal (C * r ^ s * (S.card : ℝ)) := by
    calc (Metric.externalCoveringNumber εnn (S' : Set (ℝ × ℝ)) : ENNReal)
      ≤ (S'.card : ENNReal) := h1
    _ = ENNReal.ofReal ((S'.card : ℝ)) := by simp
    _ ≤ ENNReal.ofReal (C * r ^ s * (S.card : ℝ)) := by
      exact ENNReal.ofReal_le_ofReal h2
  have h4 : (S.card : ENNReal) ≤ 9 * (Metric.externalCoveringNumber εnn (S : Set (ℝ × ℝ)) : ENNReal) := h_pack_cover
  have h5 : (Metric.externalCoveringNumber εnn (S : Set (ℝ × ℝ)) : ENNReal) ≠ ⊤ := by
    have h6 : (S.card : ENNReal) ≠ ⊤ := by simp
    have h7 : (Metric.externalCoveringNumber εnn (S : Set (ℝ × ℝ)) : ENNReal) ≤ (S.card : ENNReal) := by
      exact_mod_cast Metric.externalCoveringNumber_le_encard_self (S : Set (ℝ × ℝ))
    exact ne_top_of_le_ne_top h6 h7
  have h_rpow : (ENNReal.ofReal r) ^ s = ENNReal.ofReal (r ^ s) := by
    rw [ENNReal.ofReal_rpow_of_nonneg h_nonneg_r h_nonneg_s]
  have h9 : ENNReal.ofReal (C * r ^ s * (S.card : ℝ)) ≤
      ENNReal.ofReal (9 * C) * ENNReal.ofReal (r ^ s) *
        (Metric.externalCoveringNumber εnn (S : Set (ℝ × ℝ)) : ENNReal) := by
    have h10 : ENNReal.ofReal (C * r ^ s * (S.card : ℝ)) =
        ENNReal.ofReal (C * r ^ s) * (S.card : ENNReal) := by
      have h10a : ENNReal.ofReal (C * r ^ s * (S.card : ℝ)) =
          ENNReal.ofReal (C * r ^ s) * ENNReal.ofReal ((S.card : ℝ)) := by
        rw [ENNReal.ofReal_mul (show 0 ≤ C * r ^ s by positivity)]
      rw [h10a]
      have h10b : ENNReal.ofReal ((S.card : ℝ)) = (S.card : ENNReal) := by simp
      rw [h10b]
    rw [h10]
    have h11 : ENNReal.ofReal (C * r ^ s) * (S.card : ENNReal) ≤
        ENNReal.ofReal (C * r ^ s) * (9 * (Metric.externalCoveringNumber εnn (S : Set (ℝ × ℝ)) : ENNReal)) := by
      gcongr
    have h12 : ENNReal.ofReal (C * r ^ s) = ENNReal.ofReal C * ENNReal.ofReal (r ^ s) := by
      rw [ENNReal.ofReal_mul h_nonneg_C]
    have h13 : ENNReal.ofReal (C * r ^ s) * (9 * (Metric.externalCoveringNumber εnn (S : Set (ℝ × ℝ)) : ENNReal)) =
        ENNReal.ofReal (9 * C) * ENNReal.ofReal (r ^ s) * (Metric.externalCoveringNumber εnn (S : Set (ℝ × ℝ)) : ENNReal) := by
      rw [h12]
      have h14 : ENNReal.ofReal (9 * C) = (9 : ENNReal) * ENNReal.ofReal C := by
        have h15 : ENNReal.ofReal (9 * C) = ENNReal.ofReal 9 * ENNReal.ofReal C := by
          rw [ENNReal.ofReal_mul (show 0 ≤ (9 : ℝ) by norm_num)]
        have h16 : ENNReal.ofReal 9 = (9 : ENNReal) := by norm_cast
        rw [h15, h16] <;> ring
      rw [h14]
      <;> simp [mul_assoc, mul_comm, mul_left_comm] <;> ring
    rw [h13] at h11
    exact h11
  have h_main : (Metric.externalCoveringNumber εnn (S' : Set (ℝ × ℝ)) : ENNReal) ≤
      ENNReal.ofReal (9 * C) * (ENNReal.ofReal r) ^ s *
        (Metric.externalCoveringNumber εnn (S : Set (ℝ × ℝ)) : ENNReal) := by
    rw [h_rpow]; exact le_trans h3 h9
  have h_final : (Metric.externalCoveringNumber δ.toNNReal ((S : Set (ℝ × ℝ)) ∩ Metric.closedBall x r) : ENNReal) ≤
      ENNReal.ofReal (9 * C) * (ENNReal.ofReal r) ^ s *
        (Metric.externalCoveringNumber δ.toNNReal (S : Set (ℝ × ℝ)) : ENNReal) := by
    have h_eq1 : εnn = δ.toNNReal := by simp [εnn]
    have h_eq2 : (S' : Set (ℝ × ℝ)) = (S : Set (ℝ × ℝ)) ∩ Metric.closedBall x r := hS'_eq
    rw [h_eq1] at h_main
    rw [h_eq2] at h_main
    exact h_main
  exact h_final

/-! ### Generic packing-cover bound -/

/-- Generic packing-to-covering bound: if every δ-ball contains at most K points
    of a δ-separated finite set S, then |S| ≤ K * covering_δ(S). -/
lemma packing_cover_generic {X : Type*} [MetricSpace X] [DecidableEq X] {δ : ℝ} (hδ_pos : 0 < δ)
    {S : Finset X} (hsep : SeparatedAt δ (S : Set X))
    {K : ℕ} (hK_pos : 0 < K)
    (h_pack : ∀ (x : X), (S.filter (fun y => dist y x ≤ δ)).card ≤ K) :
    (S.card : ENNReal) ≤ (K : ENNReal) * Metric.externalCoveringNumber δ.toNNReal (S : Set X) := by
  classical
  let P : ℕ → Prop := fun n => ∃ (C : Finset X),
    C.card = n ∧ Metric.IsCover δ.toNNReal (S : Set X) (C : Set X)
  have hP : ∃ n, P n := by
    refine ⟨S.card, S, rfl, ?_⟩
    intro x hx; exact ⟨x, hx, by simp⟩
  let n₀ := Nat.find hP
  have hn₀ : P n₀ := Nat.find_spec hP
  rcases hn₀ with ⟨C₀, hC₀_card, hC₀_cover⟩
  have h_ge : ∀ (C : Set X), Metric.IsCover δ.toNNReal (S : Set X) C → (n₀ : ℕ∞) ≤ C.encard := by
    intro C hC
    by_cases hC_fin : C.Finite
    · let Cfin : Finset X := hC_fin.toFinset
      have hCfin_eq : (Cfin : Set X) = C := by simp [Cfin]
      have hP_Cfin : P Cfin.card := ⟨Cfin, rfl, by rwa [hCfin_eq]⟩
      have h : n₀ ≤ Cfin.card := by
        by_contra h'
        have h'' : Cfin.card < n₀ := by linarith
        have h3 : ¬P Cfin.card := Nat.find_min hP h''
        exact h3 hP_Cfin
      have h2 : C.encard = ↑Cfin.card := by rw [←hCfin_eq] <;> simp
      rw [h2]; exact_mod_cast h
    · have hC_inf : C.encard = ⊤ := by
        exact Set.encard_eq_top_iff.mpr (show ¬C.Finite from hC_fin)
      rw [hC_inf] <;> simp
  have h_n₀_le_ec : (n₀ : ℕ∞) ≤ Metric.externalCoveringNumber δ.toNNReal (S : Set X) := by
    have h' : (n₀ : ℕ∞) ≤ ⨅ (C : Set X) (_ : Metric.IsCover δ.toNNReal (S : Set X) C), C.encard := by
      apply le_iInf_iff.mpr
      intro C
      by_cases hC : Metric.IsCover δ.toNNReal (S : Set X) C
      · have h_inner : (⨅ (hC' : Metric.IsCover δ.toNNReal (S : Set X) C), C.encard) = C.encard := by simp [hC]
        rw [h_inner]; exact h_ge C hC
      · have h_inner : (⨅ (hC' : Metric.IsCover δ.toNNReal (S : Set X) C), C.encard) = ⊤ := by simp [hC]
        rw [h_inner] <;> simp
    simpa [Metric.externalCoveringNumber] using h'
  have h_card_bound : S.card ≤ K * n₀ := by
    have hcover : (S : Set X) ⊆ ⋃ c ∈ (C₀ : Set X), Metric.closedBall c δ := by
      intro x hx
      have h3 := hC₀_cover hx
      rcases h3 with ⟨c, hc, h4⟩
      have h5 : dist x c ≤ δ := by
        have h6 : (δ.toNNReal : ℝ) = δ := by simp [Real.toNNReal_of_nonneg hδ_pos.le]
        simpa [edist_dist, h6] using h4
      exact Set.mem_iUnion₂.mpr ⟨c, hc, h5⟩
    have h5 : S ⊆ C₀.biUnion (fun c => S.filter (fun y => dist y c ≤ δ)) := by
      intro x hx
      have h6 := hcover hx
      rcases Set.mem_iUnion₂.mp h6 with ⟨c, hc, h7⟩
      exact Finset.mem_biUnion.mpr ⟨c, hc, Finset.mem_filter.mpr ⟨hx, h7⟩⟩
    have h7 : S.card ≤ (C₀.biUnion (fun c => S.filter (fun y => dist y c ≤ δ))).card :=
      Finset.card_le_card h5
    have h8 : (C₀.biUnion (fun c => S.filter (fun y => dist y c ≤ δ))).card ≤
        ∑ c ∈ C₀, (S.filter (fun y => dist y c ≤ δ)).card := Finset.card_biUnion_le
    have h9 : ∑ c ∈ C₀, (S.filter (fun y => dist y c ≤ δ)).card ≤ ∑ c ∈ C₀, K := by
      apply Finset.sum_le_sum; intro c _; exact h_pack c
    have h10 : ∑ c ∈ C₀, K = K * C₀.card := by simp [Finset.sum_const, mul_comm]
    calc S.card
      ≤ (C₀.biUnion (fun c => S.filter (fun y => dist y c ≤ δ))).card := h7
    _ ≤ ∑ c ∈ C₀, (S.filter (fun y => dist y c ≤ δ)).card := h8
    _ ≤ ∑ c ∈ C₀, K := h9
    _ = K * C₀.card := h10
    _ = K * n₀ := by rw [hC₀_card] <;> ring
  have h_main_nat : (S.card : ℕ∞) ≤ (K : ℕ∞) * Metric.externalCoveringNumber δ.toNNReal (S : Set X) := by
    calc (S.card : ℕ∞)
      ≤ ↑(K * n₀) := by exact_mod_cast h_card_bound
    _ = (K : ℕ∞) * (n₀ : ℕ∞) := by simp [mul_comm] <;> ring
    _ ≤ (K : ℕ∞) * Metric.externalCoveringNumber δ.toNNReal (S : Set X) := by gcongr
  exact_mod_cast h_main_nat

/-! ### EuclideanPlane packing bound -/

/-- Helper: for v : EuclideanPlane, ‖v‖^2 = (v 0)^2 + (v 1)^2. -/
lemma euclidean_norm_sq (v : EuclideanPlane) :
    ‖v‖ ^ 2 = (v 0)^2 + (v 1)^2 := by
  have h : ‖v‖ = Real.sqrt ((v 0)^2 + (v 1)^2) := by
    rw [EuclideanSpace.norm_eq]
    <;> simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
    <;> ring
  rw [h]
  rw [Real.sq_sqrt] <;> positivity

/-- Helper: |v i| ≤ ‖v‖ for EuclideanPlane. -/
lemma euclidean_coord_le_norm (v : EuclideanPlane) (i : Fin 2) : |v i| ≤ ‖v‖ := by
  have h2 : (v i)^2 ≤ ‖v‖^2 := by
    have h3 : ‖v‖^2 = ∑ j : Fin 2, (v j)^2 := by
      have h4 : ‖v‖ = Real.sqrt (∑ j : Fin 2, (v j)^2) := by
        simpa [EuclideanSpace.norm_eq] using rfl
      rw [h4]
      rw [Real.sq_sqrt] <;> positivity
    rw [h3]
    exact Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)
  have h4 : 0 ≤ ‖v‖ := by positivity
  have h5 : 0 ≤ |v i| := by positivity
  nlinarith [sq_abs (v i)]

/-- Maximum 9 δ-separated points in a Euclidean δ-ball.

    A Euclidean δ-ball is contained in the coordinate square [x₀-δ,x₀+δ]×[x₁-δ,x₁+δ].
    A 3×3 grid gives cells with coordinate width 2δ/3, hence Euclidean diameter
    2√2 δ/3 < δ, so each cell contains at most one δ-separated point. -/
lemma max_points_in_delta_ball_EuclideanPlane {δ : ℝ} (hδ_pos : 0 < δ)
    (S : Finset EuclideanPlane) (hsep : SeparatedAt δ (S : Set EuclideanPlane))
    (x : EuclideanPlane) :
    (S.filter (fun y => dist y x ≤ δ)).card ≤ 9 := by
  let B : Finset EuclideanPlane := S.filter (fun y => dist y x ≤ δ)
  have hB_sub : (B : Set EuclideanPlane) ⊆ (S : Set EuclideanPlane) := by
    intro y hy; exact (Finset.mem_filter.mp hy).1
  have hB_sep : SeparatedAt δ (B : Set EuclideanPlane) := hsep.mono hB_sub
  let cell : EuclideanPlane → (ℤ × ℤ) := fun y =>
    ( if y 0 < x 0 - δ / 3 then 0 else if y 0 < x 0 + δ / 3 then 1 else 2
    , if y 1 < x 1 - δ / 3 then 0 else if y 1 < x 1 + δ / 3 then 1 else 2 )
  have h_inj : Set.InjOn cell (B : Set EuclideanPlane) := by
    intro y hy z hz h_eq
    by_cases hne : y ≠ z
    · have h_yin : dist y x ≤ δ := (Finset.mem_filter.mp hy).2
      have h_zin : dist z x ≤ δ := (Finset.mem_filter.mp hz).2
      have h_y1 : |y 0 - x 0| ≤ δ := by
        have h : |(y - x) 0| ≤ ‖y - x‖ := euclidean_coord_le_norm (y - x) 0
        have h2 : (y - x) 0 = y 0 - x 0 := by simp
        rw [h2] at h; exact le_trans h h_yin
      have h_y2 : |y 1 - x 1| ≤ δ := by
        have h : |(y - x) 1| ≤ ‖y - x‖ := euclidean_coord_le_norm (y - x) 1
        have h2 : (y - x) 1 = y 1 - x 1 := by simp
        rw [h2] at h; exact le_trans h h_yin
      have h_z1 : |z 0 - x 0| ≤ δ := by
        have h : |(z - x) 0| ≤ ‖z - x‖ := euclidean_coord_le_norm (z - x) 0
        have h2 : (z - x) 0 = z 0 - x 0 := by simp
        rw [h2] at h; exact le_trans h h_zin
      have h_z2 : |z 1 - x 1| ≤ δ := by
        have h : |(z - x) 1| ≤ ‖z - x‖ := euclidean_coord_le_norm (z - x) 1
        have h2 : (z - x) 1 = z 1 - x 1 := by simp
        rw [h2] at h; exact le_trans h h_zin
      have h_eq1 : (cell y).1 = (cell z).1 := by rw [h_eq]
      have h_eq2 : (cell y).2 = (cell z).2 := by rw [h_eq]
      have h_d1 : |y 0 - z 0| ≤ 2 * δ / 3 := same_third_bound hδ_pos h_y1 h_z1 h_eq1
      have h_d2 : |y 1 - z 1| ≤ 2 * δ / 3 := same_third_bound hδ_pos h_y2 h_z2 h_eq2
      have h_norm_sq : ‖y - z‖ ^ 2 = (y 0 - z 0)^2 + (y 1 - z 1)^2 :=
        euclidean_norm_sq (y - z)
      have h_sq : ‖y - z‖ ^ 2 ≤ (2 * δ / 3)^2 + (2 * δ / 3)^2 := by
        rw [h_norm_sq]
        have h1 : (y 0 - z 0)^2 ≤ (2 * δ / 3)^2 := by
          have h2 : |y 0 - z 0| ≤ 2 * δ / 3 := h_d1
          nlinarith [abs_le.mp h2]
        have h3 : (y 1 - z 1)^2 ≤ (2 * δ / 3)^2 := by
          have h4 : |y 1 - z 1| ≤ 2 * δ / 3 := h_d2
          nlinarith [abs_le.mp h4]
        nlinarith
      have h_dist : ‖y - z‖ < δ := by
        have h_pos : 0 ≤ ‖y - z‖ := by positivity
        nlinarith [Real.sqrt_nonneg 8, Real.sqrt_nonneg 3,
          Real.sqrt_nonneg ((2 * δ / 3)^2 + (2 * δ / 3)^2),
          Real.sq_sqrt (show 0 ≤ (2 * δ / 3)^2 + (2 * δ / 3)^2 by positivity)]
      have h_sep' : δ ≤ dist y z := hB_sep (Finset.mem_coe.mp hy) (Finset.mem_coe.mp hz) hne
      have h_eq_dist : dist y z = ‖y - z‖ := by simp [dist_eq_norm]
      rw [h_eq_dist] at h_sep'
      linarith
    · simpa using hne
  have h_image_subset : B.image cell ⊆ (Finset.Icc 0 2 ×ˢ Finset.Icc 0 2) := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨y, _, rfl⟩
    have h1 : (cell y).1 ∈ Finset.Icc (0 : ℤ) 2 := by
      simp [cell, Finset.mem_Icc] <;> split_ifs <;> norm_num
    have h2 : (cell y).2 ∈ Finset.Icc (0 : ℤ) 2 := by
      simp [cell, Finset.mem_Icc] <;> split_ifs <;> norm_num
    exact Finset.mem_product.mpr ⟨h1, h2⟩
  have h_card9 : (Finset.Icc 0 2 ×ˢ Finset.Icc 0 2).card = 9 := by simp [Finset.card_product]
  have h_card_B : B.card = (B.image cell).card := by rw [Finset.card_image_of_injOn h_inj]
  have h_card_image : (B.image cell).card ≤ (Finset.Icc 0 2 ×ˢ Finset.Icc 0 2).card :=
    Finset.card_le_card h_image_subset
  rw [h_card_B]; rw [h_card9] at h_card_image; exact h_card_image

/-! ### IsDeltaSSet → ball-growth finite subset in EuclideanPlane -/

/-- Extract a finite δ-separated subset with ball-growth from an S-set in
    EuclideanPlane, with constant 9*C for ALL centers.

    Uses the generic maximal-separated-set construction plus the 9-point
    Euclidean packing bound. -/
theorem IsDeltaSSet_to_ball_growth_EuclideanPlane
    {δ s C : ℝ} {P : Set EuclideanPlane}
    (h : IsDeltaSSet δ s C P)
    (hP_bounded : Bornology.IsBounded P) :
    ∃ (S : Finset EuclideanPlane),
      (S : Set EuclideanPlane) ⊆ P ∧
      S.Nonempty ∧
      SeparatedAt δ (S : Set EuclideanPlane) ∧
      ((Metric.externalCoveringNumber δ.toNNReal P : ENNReal) ≤ (S.card : ENNReal)) ∧
      (∀ x, ∀ r : ℝ, δ ≤ r →
        (S.filter (fun y => dist y x ≤ r)).card ≤ (9 * C) * r ^ s * S.card) := by
  rcases h with ⟨hP_nonempty, hδ_pos, hC_pos, hs_nonneg, h_sset⟩
  let εnn : NNReal := δ.toNNReal
  have hεnn_coe : (εnn : ℝ) = δ := by simp [εnn, Real.toNNReal_of_nonneg hδ_pos.le]
  have hP_tb : TotallyBounded P := by
    rcases hP_bounded.subset_closedBall (0 : EuclideanPlane) with ⟨R, hR⟩
    have hK : IsCompact (Metric.closedBall (0 : EuclideanPlane) R) := isCompact_closedBall _ _
    exact hK.totallyBounded.subset hR
  have h_half_pos : 0 < εnn / 2 := by
    have hδnn_pos : 0 < εnn := by simpa [εnn, NNReal.coe_pos] using hδ_pos
    positivity
  rcases Metric.exists_finite_isCover_of_totallyBounded h_half_pos.ne' hP_tb with ⟨N, _, hNfin, hNcover⟩
  have h_ec_ne_top : Metric.externalCoveringNumber (εnn / 2) P ≠ ⊤ := by
    have h : Metric.externalCoveringNumber (εnn / 2) P ≤ N.encard :=
      Metric.IsCover.externalCoveringNumber_le_encard hNcover
    have h2 : N.encard ≠ ⊤ := by exact Set.encard_ne_top_iff.mpr hNfin
    exact ne_top_of_le_ne_top h2 h
  have hmul : 2 * (εnn / 2) = εnn := by
    apply NNReal.coe_injective; simp [hεnn_coe] <;> ring
  have h_pack_ne_top : Metric.packingNumber εnn P ≠ ⊤ := by
    have h : Metric.packingNumber (2 * (εnn / 2)) P ≤ Metric.externalCoveringNumber (εnn / 2) P :=
      Metric.packingNumber_two_mul_le_externalCoveringNumber (εnn / 2) P
    rw [hmul] at h; exact ne_top_of_le_ne_top h_ec_ne_top h
  let Sset : Set EuclideanPlane := Metric.maximalSeparatedSet εnn P
  have hS_subset : Sset ⊆ P := Metric.maximalSeparatedSet_subset
  have hS_sep : Metric.IsSeparated εnn Sset := Metric.isSeparated_maximalSeparatedSet
  have hS_cover : Metric.IsCover εnn P Sset := Metric.isCover_maximalSeparatedSet h_pack_ne_top
  have hS_finite : Sset.Finite := by
    have h : Sset.encard ≠ ⊤ := by
      rw [Metric.encard_maximalSeparatedSet h_pack_ne_top] <;> exact h_pack_ne_top
    exact Set.encard_ne_top_iff.mp h
  have hS_nonempty_set : Sset.Nonempty := hS_cover.nonempty hP_nonempty
  classical
  let S : Finset EuclideanPlane := hS_finite.toFinset
  have hS_eq : (S : Set EuclideanPlane) = Sset := by simp [S]
  have hS_nonempty : S.Nonempty := by
    have h : (S : Set EuclideanPlane).Nonempty := by rw [hS_eq]; exact hS_nonempty_set
    have h_iff : S.Nonempty ↔ (S : Set EuclideanPlane).Nonempty := by
      simp [Finset.nonempty_iff_ne_empty]
    exact h_iff.mpr h
  have hS_pos : 0 < S.card := by
    have h_pack_pos : 0 < Metric.packingNumber εnn P := Metric.packingNumber_pos_iff.mpr hP_nonempty
    have h_encard : Sset.encard = Metric.packingNumber εnn P := Metric.encard_maximalSeparatedSet h_pack_ne_top
    have h : 0 < Sset.encard := by rw [h_encard]; exact h_pack_pos
    have h2 : Sset.encard = ↑S.card := by
      have h3 : Sset = (S : Set EuclideanPlane) := hS_eq.symm; rw [h3] <;> simp
    rw [h2] at h; exact_mod_cast h
  have hS_sep' : SeparatedAt δ (S : Set EuclideanPlane) := by
    rw [hS_eq]
    intro x hx y hy hne
    have h_edist : (εnn : ENNReal) < edist x y := hS_sep hx hy hne
    have h_dist : edist x y = ENNReal.ofReal (dist x y) := by rw [edist_dist] <;> rfl
    rw [h_dist] at h_edist
    have h' : (εnn : ℝ) < dist x y := by exact ENNReal.coe_lt_ofReal.mp h_edist
    rw [hεnn_coe] at h'; exact le_of_lt h'
  have hcov_P_le_S : (Metric.externalCoveringNumber εnn P : ENNReal) ≤ (S.card : ENNReal) := by
    have h1 : Metric.externalCoveringNumber εnn P ≤ Sset.encard :=
      Metric.IsCover.externalCoveringNumber_le_encard hS_cover
    have h2 : Sset.encard = ↑S.card := by
      have h3 : Sset = (S : Set EuclideanPlane) := hS_eq.symm; rw [h3] <;> simp
    rw [h2] at h1; exact_mod_cast h1
  have h_ball_growth : ∀ (x : EuclideanPlane) (r : ℝ), δ ≤ r →
      ((S.filter fun y => dist y x ≤ r).card : ℝ) ≤ (9 * C) * r ^ s * (S.card : ℝ) := by
    intro x r hr
    let S' : Finset EuclideanPlane := S.filter (fun y => dist y x ≤ r)
    have hS'_sub : (S' : Set EuclideanPlane) ⊆ (S : Set EuclideanPlane) := by
      intro y hy; exact (Finset.mem_filter.mp hy).1
    have hS'_sep : SeparatedAt δ (S' : Set EuclideanPlane) := hS_sep'.mono hS'_sub
    have h_pack_cover : (S'.card : ENNReal) ≤
        (9 : ENNReal) * (Metric.externalCoveringNumber εnn (S' : Set EuclideanPlane)) :=
      packing_cover_generic (hδ_pos := hδ_pos) (hsep := hS'_sep) (hK_pos := by norm_num)
        (max_points_in_delta_ball_EuclideanPlane hδ_pos S' hS'_sep)
    have hS'_sub_P : (S' : Set EuclideanPlane) ⊆ P ∩ Metric.closedBall x r := by
      intro y hy
      have h1 : y ∈ S := (Finset.mem_filter.mp hy).1
      have h2 : dist y x ≤ r := (Finset.mem_filter.mp hy).2
      have h3 : y ∈ Sset := by
        have h4 : y ∈ (S : Set EuclideanPlane) := h1
        rw [hS_eq] at h4; exact h4
      exact ⟨hS_subset h3, h2⟩
    have h_cov_mono_nat : Metric.externalCoveringNumber εnn (S' : Set EuclideanPlane) ≤
        Metric.externalCoveringNumber εnn (P ∩ Metric.closedBall x r) :=
      Metric.externalCoveringNumber_mono_set hS'_sub_P
    have h_cov_mono : (Metric.externalCoveringNumber εnn (S' : Set EuclideanPlane) : ENNReal) ≤
        (Metric.externalCoveringNumber εnn (P ∩ Metric.closedBall x r) : ENNReal) := by
      exact_mod_cast h_cov_mono_nat
    have h_sset' : (Metric.externalCoveringNumber εnn (P ∩ Metric.closedBall x r) : ENNReal) ≤
        ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * (Metric.externalCoveringNumber εnn P : ENNReal) :=
      h_sset x r hr
    have h_cov_S : (Metric.externalCoveringNumber εnn (S' : Set EuclideanPlane) : ENNReal) ≤
        ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * (Metric.externalCoveringNumber εnn P : ENNReal) :=
      le_trans h_cov_mono h_sset'
    have h_rpow : (ENNReal.ofReal r) ^ s = ENNReal.ofReal (r ^ s) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (by linarith) (by linarith)]
    rw [h_rpow] at h_cov_S
    have h_nonneg_C : 0 ≤ C := by linarith
    have h_nonneg_r : 0 ≤ r := by linarith
    have h4 : (Metric.externalCoveringNumber εnn P : ENNReal) ≤ (S.card : ENNReal) := hcov_P_le_S
    have h_eq1 : ENNReal.ofReal C * ENNReal.ofReal (r ^ s) = ENNReal.ofReal (C * r ^ s) := by
      rw [← ENNReal.ofReal_mul h_nonneg_C]
    have h_card : (S.card : ENNReal) = ENNReal.ofReal ((S.card : ℝ)) := by simp
    have h_eq2 : ENNReal.ofReal (C * r ^ s) * (S.card : ENNReal) =
        ENNReal.ofReal ((C * r ^ s) * (S.card : ℝ)) := by
      rw [h_card, ← ENNReal.ofReal_mul (by positivity)] <;> ring
    have h9 : (9 : ENNReal) = ENNReal.ofReal 9 := by norm_cast
    have h_eq3 : (9 : ENNReal) * ENNReal.ofReal ((C * r ^ s) * (S.card : ℝ)) =
        ENNReal.ofReal (9 * ((C * r ^ s) * (S.card : ℝ))) := by
      rw [h9, ← ENNReal.ofReal_mul (by positivity)] <;> ring
    have h_eq4 : ENNReal.ofReal (9 * ((C * r ^ s) * (S.card : ℝ))) =
        ENNReal.ofReal ((9 * C) * r ^ s * (S.card : ℝ)) := by congr 1 <;> ring
    have h_final : (S'.card : ENNReal) ≤ ENNReal.ofReal ((9 * C) * r ^ s * (S.card : ℝ)) := by
      calc (S'.card : ENNReal)
        ≤ (9 : ENNReal) * (Metric.externalCoveringNumber εnn (S' : Set EuclideanPlane)) := h_pack_cover
      _ ≤ (9 : ENNReal) * (ENNReal.ofReal C * ENNReal.ofReal (r ^ s) * (Metric.externalCoveringNumber εnn P)) := by gcongr
      _ = (9 : ENNReal) * (ENNReal.ofReal (C * r ^ s) * (Metric.externalCoveringNumber εnn P)) := by rw [h_eq1] <;> ring
      _ ≤ (9 : ENNReal) * (ENNReal.ofReal (C * r ^ s) * (S.card : ENNReal)) := by gcongr
      _ = (9 : ENNReal) * ENNReal.ofReal ((C * r ^ s) * (S.card : ℝ)) := by rw [h_eq2]
      _ = ENNReal.ofReal (9 * ((C * r ^ s) * (S.card : ℝ))) := h_eq3
      _ = ENNReal.ofReal ((9 * C) * r ^ s * (S.card : ℝ)) := h_eq4
    have h_card' : (S'.card : ENNReal) = ENNReal.ofReal ((S'.card : ℝ)) := by simp
    rw [h_card'] at h_final
    have h_pos2 : 0 ≤ (9 * C) * r ^ s * (S.card : ℝ) := by positivity
    have h_iff : ENNReal.ofReal ((S'.card : ℝ)) ≤ ENNReal.ofReal ((9 * C) * r ^ s * (S.card : ℝ)) ↔
        (S'.card : ℝ) ≤ (9 * C) * r ^ s * (S.card : ℝ) :=
      ENNReal.ofReal_le_ofReal_iff h_pos2
    exact h_iff.mp h_final
  have hS_subset' : (S : Set EuclideanPlane) ⊆ P := by
    rw [hS_eq]; exact hS_subset
  exact ⟨S, hS_subset', hS_nonempty, hS_sep', hcov_P_le_S, h_ball_growth⟩

/-- Convert IsDeltaSSet to IsFiniteDeltaSSet for EuclideanPlane with
    constant max(1, 9*C). Uses the direct maximal-separated-set construction
    with the 9-point Euclidean packing bound. -/
theorem IsDeltaSSet_to_finite_delta_sset_EuclideanPlane_tight
    {δ s C : ℝ} {P : Set EuclideanPlane}
    (h : IsDeltaSSet δ s C P)
    (hP_bounded : Bornology.IsBounded P) :
    ∃ (S : Finset EuclideanPlane),
      (S : Set EuclideanPlane) ⊆ P ∧
      IsFiniteDeltaSSet δ s (max 1 (9 * C)) S := by
  rcases h with ⟨hP_nonempty, hδ_pos, hC_pos, hs_nonneg, h_sset⟩
  rcases IsDeltaSSet_to_ball_growth_EuclideanPlane
      (⟨hP_nonempty, hδ_pos, hC_pos, hs_nonneg, h_sset⟩) hP_bounded with
    ⟨S, hS_sub, hS_nonempty, hS_sep, hS_cover, hS_growth⟩
  let C' := max 1 (9 * C)
  have hC1 : 1 ≤ C' := le_max_left 1 (9 * C)
  have hC9 : (9 * C) ≤ C' := le_max_right 1 (9 * C)
  have h_growth' : ∀ (x : EuclideanPlane) (r : ℝ), δ ≤ r →
      ((S.filter fun y => dist y x ≤ r).card : ℝ) ≤ C' * r ^ s * (S.card : ℝ) := by
    intro x r hr
    have h : ((S.filter fun y => dist y x ≤ r).card : ℝ) ≤ (9 * C) * r ^ s * (S.card : ℝ) :=
      hS_growth x r hr
    have h' : (9 * C) * r ^ s * (S.card : ℝ) ≤ C' * r ^ s * (S.card : ℝ) := by
      have hr' : 0 ≤ r := by linarith
      gcongr
    exact le_trans h h'
  exact ⟨S, hS_sub, hS_nonempty, hδ_pos, hC1, hs_nonneg, hS_sep, h_growth'⟩

end SSetBridges

end DirecretisedFurstenbergEstimate
