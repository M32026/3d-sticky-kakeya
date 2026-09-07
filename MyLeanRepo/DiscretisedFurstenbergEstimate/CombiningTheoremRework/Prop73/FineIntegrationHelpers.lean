module

/-
  FineIntegrationHelpers — Integration helpers for wiring
  fine_config_from_consumer into InductiveStepCore_v2.

  Four helpers:
  1. normalizedIndex: convert DyadicSquare k ⊆ Q to ℤ×ℤ index at scale k-m
  2. density_cardinality_to_index: transfer B1 cardinality density to index finsets
  3. between_scales_to_P_Q: transfer coarse between-scales to full fiber P_Q (rescaled)
  4. uniformity_to_rangeUniformity_Q: convert coarse IsUniformAtScales to RangeUniformityProp

  Whiteprint node: combining_theorem_rework / fine_integration_helpers
  Status: All 4 helpers proved.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.BetweenScalesTransfer
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Prop73.FineConfigSublemma
public import MyLeanRepo.DiscretisedFurstenbergEstimate.GeometricIntersection
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FormatConversionLemmas
public import MyLeanRepo.DiscretisedFurstenbergEstimate.BasicUniformization
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DiscretisedFurstenbergEstimate.CombiningTheorem
open DiscretisedFurstenbergEstimate.InductionConfigurations
open DiscretisedFurstenbergEstimate.BasicUniformization

/-! ========================================================================
   Helper 1: Dyadic square to normalized index

   Given a fine dyadic square p at scale k contained in coarse square Q at
   scale m, compute its normalized index at scale k-m within Q.

   The normalized index is (p.i - Q.i * 2^(k-m), p.j - Q.j * 2^(k-m)).
   ======================================================================== -/

/-- Normalized index of a dyadic square p (scale k) within coarse square Q (scale m). -/
def normalizedIndex (k m : ℕ) (hnm : m ≤ k) (Q : DyadicSquare m)
    (p : DyadicSquare k) : ℤ × ℤ :=
  (p.i - Q.i * (2^(k - m) : ℤ), p.j - Q.j * (2^(k - m) : ℤ))

/-- If p is contained in Q, its normalized index is within [0, 2^(k-m))². -/
lemma normalizedIndex_in_bounds
    {k m : ℕ} (hnm : m ≤ k) (Q : DyadicSquare m) (p : DyadicSquare k)
    (h_cont : squareContained hnm p Q) :
    0 ≤ (normalizedIndex k m hnm Q p).1 ∧
    (normalizedIndex k m hnm Q p).1 < (2 : ℤ)^(k - m) ∧
    0 ≤ (normalizedIndex k m hnm Q p).2 ∧
    (normalizedIndex k m hnm Q p).2 < (2 : ℤ)^(k - m) := by
  let r : ℤ := 2^(k - m)
  have hr_pos : 0 < r := by positivity
  have h1 : Q.i * r ≤ p.i := h_cont.1
  have h2 : p.i < (Q.i + 1) * r := h_cont.2.1
  have h3 : Q.j * r ≤ p.j := h_cont.2.2.1
  have h4 : p.j < (Q.j + 1) * r := h_cont.2.2.2
  have h_i1 : 0 ≤ p.i - Q.i * r := by linarith
  have h_i2 : p.i - Q.i * r < r := by linarith
  have h_j1 : 0 ≤ p.j - Q.j * r := by linarith
  have h_j2 : p.j - Q.j * r < r := by linarith
  dsimp only [normalizedIndex]
  exact ⟨h_i1, h_i2, h_j1, h_j2⟩

/-- The normalized index map is injective on squares contained in Q. -/
lemma normalizedIndex_injective_on
    {k m : ℕ} (hnm : m ≤ k) (Q : DyadicSquare m) :
    Set.InjOn (normalizedIndex k m hnm Q) {p | squareContained hnm p Q} := by
  intro p1 hp1 p2 hp2 h_eq
  have h1 : (normalizedIndex k m hnm Q p1).1 = (normalizedIndex k m hnm Q p2).1 := by
    rw [h_eq]
  have h2 : (normalizedIndex k m hnm Q p1).2 = (normalizedIndex k m hnm Q p2).2 := by
    rw [h_eq]
  simp [normalizedIndex] at h1 h2
  have hi : p1.i = p2.i := by omega
  have hj : p1.j = p2.j := by omega
  cases p1
  cases p2
  simp_all

/-- Convert a finset of dyadic squares (all contained in Q) to normalized indices.
    Cardinality is preserved. -/
lemma normalizedIndex_finset_card
    {k m : ℕ} (hnm : m ≤ k) (Q : DyadicSquare m)
    (P : Finset (DyadicSquare k))
    (hP_sub : ∀ p ∈ P, squareContained hnm p Q) :
    (P.image (normalizedIndex k m hnm Q)).card = P.card := by
  apply Finset.card_image_of_injOn
  intro p1 hp1 p2 hp2 h_eq
  exact normalizedIndex_injective_on hnm Q (hP_sub p1 hp1) (hP_sub p2 hp2) h_eq

/-! ========================================================================
   Helper 2: Density preservation at index level

   From B1 cardinality bound card(full) ≤ K * card(thin), derive
   card(S') ≥ card(S_full) / K at the normalized index level.
   ======================================================================== -/

/-- Transfer cardinality density from dyadic square finsets to normalized index finsets. -/
lemma density_cardinality_to_index
    {k m : ℕ} (hnm : m ≤ k) (Q : DyadicSquare m)
    (P_full P_thin : Finset (DyadicSquare k))
    (h_full_sub : ∀ p ∈ P_full, squareContained hnm p Q)
    (h_thin_sub : ∀ p ∈ P_thin, squareContained hnm p Q)
    (K : ℝ) (hK_pos : 0 < K)
    (h_card : (P_full.card : ℝ) ≤ K * (P_thin.card : ℝ)) :
    let S_full := P_full.image (normalizedIndex k m hnm Q)
    let S' := P_thin.image (normalizedIndex k m hnm Q)
    (S'.card : ℝ) ≥ (S_full.card : ℝ) / K := by
  dsimp only
  have h1 : ((P_full.image (normalizedIndex k m hnm Q)).card : ℝ) = (P_full.card : ℝ) := by
    exact_mod_cast normalizedIndex_finset_card hnm Q P_full h_full_sub
  have h2 : ((P_thin.image (normalizedIndex k m hnm Q)).card : ℝ) = (P_thin.card : ℝ) := by
    exact_mod_cast normalizedIndex_finset_card hnm Q P_thin h_thin_sub
  have h3 : (P_thin.card : ℝ) ≥ (P_full.card : ℝ) / K := by
    have h4 : (P_full.card : ℝ) ≤ K * (P_thin.card : ℝ) := h_card
    have h5 : (P_full.card : ℝ) / K ≤ (P_thin.card : ℝ) := by
      calc (P_full.card : ℝ) / K
        ≤ (K * (P_thin.card : ℝ)) / K := by gcongr
      _ = (P_thin.card : ℝ) := by
        field_simp [hK_pos.ne'] <;> ring
    exact h5
  rw [h1, h2]
  exact h3

/-! ========================================================================
   Helper 3: Between-scales transfer to P_Q

   Transfer coarse h_normal/h_good from config.pointSet to
   P_Q = homothety '' (config.pointSet ∩ Q) using between_scales_transfer_all.

   The output scales are RESCALED by 1/Δ₁, matching the normalized fine
   configuration scales Δ' j = Δ(j+1)/Δ₁.
   ======================================================================== -/

/-- Transfer all between-scales properties from P to P_Q with rescaled scales. -/
lemma between_scales_to_P_Q
    {n_fine : ℕ} {P : Set Plane} {Δ₁ : ℝ} {i₀ j₀ : ℤ}
    (hΔ₁_pos : 0 < Δ₁)
    (hΔ₁_dyadic : Δ₁ ∈ dyadicScales)
    (Δ : Fin (n_fine + 1) → ℝ)
    (hΔ_dyadic : ∀ i, Δ i ∈ dyadicScales)
    (hΔ_pos : ∀ i, 0 < Δ i)
    (hΔ_decreasing : ∀ j : Fin n_fine, Δ (Fin.succ j) ≤ Δ j.castSucc)
    (hΔ_j_le_Δ₁ : ∀ j : Fin n_fine, Δ j.castSucc ≤ Δ₁)
    (scaleClass : Fin n_fine → ScaleClass)
    (s : ℝ)
    (C_between : Fin n_fine → ℝ)
    (h_normal : ∀ (j : Fin n_fine),
      scaleClass j = ScaleClass.normal →
        IsSetBetweenScales P (Δ (Fin.succ j)) (Δ j.castSucc) s (C_between j))
    (h_good : ∀ (j : Fin n_fine) (t_j : ℝ),
      scaleClass j = ScaleClass.good t_j →
        IsRegularBetweenScales P (Δ (Fin.succ j)) (Δ j.castSucc) t_j
          (C_between j) (C_between j)) :
    let P_Q : Set Plane := homothetyS Δ₁ i₀ j₀ ''
      (P ∩ CombiningTheorem.dyadicSquare Δ₁ i₀ j₀)
    (∀ (j : Fin n_fine),
      scaleClass j = ScaleClass.normal →
        IsSetBetweenScales P_Q
          (Δ (Fin.succ j) / Δ₁) (Δ j.castSucc / Δ₁) s (C_between j)) ∧
    (∀ (j : Fin n_fine) (t_j : ℝ),
      scaleClass j = ScaleClass.good t_j →
        IsRegularBetweenScales P_Q
          (Δ (Fin.succ j) / Δ₁) (Δ j.castSucc / Δ₁) t_j
          (C_between j) (C_between j)) :=
  between_scales_transfer_all
    hΔ₁_pos hΔ₁_dyadic n_fine Δ hΔ_dyadic hΔ_pos hΔ_decreasing hΔ_j_le_Δ₁
    scaleClass s C_between h_normal h_good

/-! ========================================================================
   Helper 4: Uniformity transfer to RangeUniformityProp

   Convert coarse IsUniformAtScales on config.pointSet to RangeUniformityProp
   on the normalized full index set S_full.
   ======================================================================== -/

/-- Convert coarse uniformity to RangeUniformityProp on normalized indices.

    This is a thin wrapper around `isUniformAtScales_to_rangeUniformity_Q`
    that supplies the scale normalization parameters. -/
lemma uniformity_to_rangeUniformity_Q
    {n n_fine k : ℕ} (hn_fine : n_fine + 1 = n)
    (P : Set Plane) (Δ : Fin (n + 1) → ℝ) (N : Fin n → ℕ)
    (h_uniform : IsUniformAtScales P n Δ N)
    (m : ℕ) (Q : DyadicSquare m)
    (hΔ1_eq : Δ 1 = dyadicDelta m)
    (hΔk_eq : Δ (Fin.last n) = dyadicDelta k)
    (a : Fin (n_fine + 1) → ℕ)
    (ha_spec : ∀ (i : Fin (n_fine + 1)),
      Δ (⟨i.val + 1, by omega⟩ : Fin (n + 1)) / Δ 1 = dyadicDelta (a i))
    (ha_mono : ∀ j : Fin n_fine, a j.castSucc ≤ a (Fin.succ j))
    (ha_last_max : ∀ i, a i ≤ a (Fin.last n_fine))
    (S_full_norm : Finset (ℤ × ℤ))
    (hS_nonempty : S_full_norm.Nonempty)
    (hP_Q_eq : homothetyS (Δ 1) Q.i Q.j ''
      (P ∩ CombiningTheorem.dyadicSquare (Δ 1) Q.i Q.j)
                    = setFromIndices (dyadicDelta (a (Fin.last n_fine))) S_full_norm)
    (h_unit_S : ∀ idx ∈ S_full_norm, 0 ≤ idx.1 ∧ 0 ≤ idx.2 ∧
                 idx.1 < (2 : ℤ)^(a (Fin.last n_fine)) ∧
                 idx.2 < (2 : ℤ)^(a (Fin.last n_fine))) :
    RangeUniformityProp n_fine a S_full_norm (fun j' : Fin n_fine =>
      N ⟨j'.val + 1, by omega⟩) :=
  isUniformAtScales_to_rangeUniformity_Q
    (n := n) (n_fine := n_fine) hn_fine
    P Δ N h_uniform
    m Q hΔ1_eq hΔk_eq
    a ha_spec ha_mono ha_last_max
    S_full_norm hS_nonempty hP_Q_eq h_unit_S

end DiscretisedFurstenbergEstimate.CombiningTheoremRework

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

/-- `dyadicDelta` is strictly decreasing: m < n → dyadicDelta m > dyadicDelta n. -/
lemma dyadicDelta_strict_decreasing {m n : ℕ} (h : m < n) :
    dyadicDelta m > dyadicDelta n := by
  simp only [dyadicDelta]
  have h1 : (2 : ℝ)^m < (2 : ℝ)^n := by
    have h11 : (2 : ℕ)^m < (2 : ℕ)^n := Nat.pow_lt_pow_right (by norm_num) h
    exact_mod_cast h11
  have h2 : 0 < (2 : ℝ)^m := by positivity
  have h4 : (1 : ℝ) / (2 : ℝ)^n < (1 : ℝ) / (2 : ℝ)^m := by
    apply one_div_lt_one_div_of_lt h2 h1
  exact h4

/-- Construct `a : Fin (n_fine+1) → ℕ` from dyadic scales Δ'.

    Given Δ' with all scales dyadic and strictly decreasing, produces
    `a` such that Δ' i = dyadicDelta (a i), with monotonicity and last-max. -/
lemma construct_a_from_dyadic_scales
    {n_fine : ℕ} (hn_fine_pos : 0 < n_fine)
    (Δ' : Fin (n_fine + 1) → ℝ)
    (hΔ'_dyadic : ∀ i, Δ' i ∈ dyadicScales)
    (hΔ'_strict : ∀ j : Fin n_fine, Δ' (Fin.succ j) < Δ' j.castSucc) :
    ∃ (a : Fin (n_fine + 1) → ℕ),
      (∀ i, Δ' i = dyadicDelta (a i)) ∧
      (∀ j : Fin n_fine, a j.castSucc ≤ a (Fin.succ j)) ∧
      (∀ i, a i ≤ a (Fin.last n_fine)) := by
  let a : Fin (n_fine + 1) → ℕ := fun i => Classical.choose (hΔ'_dyadic i)
  have ha_spec_raw : ∀ i, Δ' i = (2 : ℝ)^(-(a i : ℤ)) := by
    intro i
    exact Classical.choose_spec (hΔ'_dyadic i)
  have ha_spec : ∀ i, Δ' i = dyadicDelta (a i) := by
    intro i
    have h_eq : dyadicDelta (a i) = (2 : ℝ)^(-(a i : ℤ)) := by
      simp [dyadicDelta]
      <;> field_simp
      <;> ring
    rw [h_eq]
    exact ha_spec_raw i
  have ha_mono : ∀ j : Fin n_fine, a j.castSucc ≤ a (Fin.succ j) := by
    intro j
    have h1 : Δ' (Fin.succ j) < Δ' j.castSucc := hΔ'_strict j
    have h2 : dyadicDelta (a (Fin.succ j)) < dyadicDelta (a j.castSucc) := by
      rw [←ha_spec (Fin.succ j), ←ha_spec j.castSucc] <;> exact h1
    by_contra h3
    have h4 : a (Fin.succ j) < a j.castSucc := by omega
    have h5 : dyadicDelta (a j.castSucc) < dyadicDelta (a (Fin.succ j)) :=
      dyadicDelta_strict_decreasing h4
    linarith
  have h_last_min : ∀ i : Fin (n_fine + 1), Δ' (Fin.last n_fine) ≤ Δ' i := by
    have h_antitone : ∀ (i j : Fin (n_fine + 1)), i.val ≤ j.val → Δ' j ≤ Δ' i := by
      intro i j hij
      have h_main : ∀ (k : ℕ), ∀ (hk : i.val + k ≤ n_fine),
          Δ' ⟨i.val + k, Nat.lt_succ_of_le hk⟩ ≤ Δ' i := by
        intro k
        induction k with
        | zero =>
          intro hk
          have h_eq : (⟨i.val + 0, Nat.lt_succ_of_le hk⟩ : Fin (n_fine + 1)) = i := by
            apply Fin.ext <;> simp
          rw [h_eq] <;> rfl
        | succ k ih =>
          intro hk
          have h_k : i.val + k ≤ n_fine := by omega
          let j' : Fin n_fine := ⟨i.val + k, by omega⟩
          have h1 : Δ' (Fin.succ j') < Δ' (j'.castSucc) := hΔ'_strict j'
          have h_eq1 : (j'.castSucc : Fin (n_fine + 1)) = ⟨i.val + k, Nat.lt_succ_of_le h_k⟩ := by
            apply Fin.ext <;> simp [j']
          have h_eq2 : (Fin.succ j' : Fin (n_fine + 1)) = ⟨i.val + k + 1, Nat.lt_succ_of_le hk⟩ := by
            apply Fin.ext <;> simp [j', Fin.val_succ] <;> omega
          rw [h_eq1, h_eq2] at h1
          exact le_trans h1.le (ih h_k)
      have h_k : i.val + (j.val - i.val) ≤ n_fine := by omega
      have h_add : i.val + (j.val - i.val) = j.val := Nat.add_sub_of_le hij
      have h_result := h_main (j.val - i.val) h_k
      have h_eq : (⟨i.val + (j.val - i.val), Nat.lt_succ_of_le h_k⟩ : Fin (n_fine + 1)) = j := by
        apply Fin.ext
        have h_val : (⟨i.val + (j.val - i.val), Nat.lt_succ_of_le h_k⟩ : Fin (n_fine + 1)).val = j.val := by
          exact h_add
        exact h_val
      rw [h_eq] at h_result
      exact h_result
    intro i
    have h : i.val ≤ (Fin.last n_fine).val := by
      have h_i_lt : i.val < n_fine + 1 := i.is_lt
      have h_last_val : (Fin.last n_fine).val = n_fine := by simp
      rw [h_last_val]
      exact Nat.lt_succ_iff.mp h_i_lt
    exact h_antitone i (Fin.last n_fine) h
  have ha_last_max : ∀ i, a i ≤ a (Fin.last n_fine) := by
    intro i
    have h1 : Δ' (Fin.last n_fine) ≤ Δ' i := h_last_min i
    have h2 : dyadicDelta (a (Fin.last n_fine)) ≤ dyadicDelta (a i) := by
      rw [←ha_spec (Fin.last n_fine), ←ha_spec i] <;> exact h1
    by_contra h3
    have h4 : a (Fin.last n_fine) < a i := by omega
    have h5 : dyadicDelta (a i) < dyadicDelta (a (Fin.last n_fine)) :=
      dyadicDelta_strict_decreasing h4
    linarith
  exact ⟨a, ha_spec, ha_mono, ha_last_max⟩

end DiscretisedFurstenbergEstimate.CombiningTheoremRework
