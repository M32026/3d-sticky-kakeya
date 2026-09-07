module

/-
  Section 9 type definition: RawMultiscaleDecomp.

  Faithfully packages the output tuple of
  `MultiscaleDecomposition.multiscaleDecompKaufman` (Root.lean) for a
  fixed number of decomposition steps n and point set P.

  Whiteprint node: section9 / raw_multiscale_decomp
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DirecretisedFurstenbergEstimate.Section9

open MultiscaleDecomposition (IsSetBetweenScales IsRegularBetweenScales)
open DirecretisedFurstenbergEstimate (EuclideanPlane)

/-- Faithful packaging of `multiscaleDecompKaufman` output for a fixed `n`, `P`.

    Fields correspond exactly to the conjunction in Root.lean lines 810-837. -/
structure RawMultiscaleDecomp
    (δ_d s t τ ε_G ε_bad : ℝ) (n : ℕ) (P : Set EuclideanPlane) where
  /-- The base dyadic ratio Δ such that δ_d = Δ ^ m. -/
  Δ : ℝ
  /-- The top exponent m such that δ_d = Δ ^ m. -/
  m : ℕ
  /-- Consistency: the base scale equals Δ ^ m. -/
  hδ_d : δ_d = Δ ^ m
  /-- Exponent at each decomposition boundary: i(0)=0, i(n)=m. -/
  i : ℕ → ℕ
  /-- Dimension assigned to each structured interval. -/
  t_j : ℕ → ℝ
  /-- Indices classified as "structured" (good). -/
  S : Finset (Fin n)
  /-- Indices classified as "bad". -/
  B : Finset (Fin n)
  hi0 : i 0 = 0
  hin : i n = m
  h_strict_mono : ∀ j < n, i j < i (j + 1)
  h_tj_range : ∀ j : Fin n, t_j j.val ∈ Set.Icc s 2
  h_partition : S ∪ B = Finset.univ
  h_disjoint : Disjoint S B
  h_S_ratio : ∀ j : Fin n, j ∈ S →
    (Δ ^ i j.val : ℝ) / (Δ ^ i (j.val + 1)) ≥ Real.rpow δ_d (-τ)
  h_B_product :
    (∏ j ∈ B, ((Δ ^ i j.val : ℝ) / (Δ ^ i (j.val + 1)))) ≤
      Real.rpow δ_d (-ε_bad)
  h_S_set : ∀ j : Fin n, j ∈ S →
    IsSetBetweenScales P
      (Δ ^ i (j.val + 1))
      (Δ ^ i j.val)
      (t_j j.val)
      ((81 : ℝ) * Real.rpow Δ (-4) *
        Real.rpow ((Δ ^ i j.val : ℝ) / (Δ ^ i (j.val + 1))) ε_bad)
  h_S_regular : ∀ j : Fin n, j ∈ S → t_j j.val > s →
    IsRegularBetweenScales P
      (Δ ^ i (j.val + 1))
      (Δ ^ i j.val)
      (t_j j.val)
      ((81 : ℝ) * Real.rpow Δ (-4) *
        Real.rpow ((Δ ^ i j.val : ℝ) / (Δ ^ i (j.val + 1))) ε_bad)
      ((81 : ℝ) * Real.rpow Δ (-4) *
        Real.rpow ((Δ ^ i j.val : ℝ) / (Δ ^ i (j.val + 1))) ε_bad)
  h_S_product :
    (∏ j ∈ S, Real.rpow ((Δ ^ i j.val : ℝ) / (Δ ^ i (j.val + 1))) (t_j j.val)) ≥
      Real.rpow δ_d (ε_bad - t)
  h_B_no_adjacent : ∀ j : Fin n, j ∈ B →
    ∀ k : Fin n, k.val = j.val + 1 → k ∉ B

/-- Bound on the number of decomposition steps: `n ≤ 2 * floor(1/τ) + 1`.

    Each structured block has width ≥ m*τ, and there are at most 1/τ structured blocks.
    No two bad blocks are adjacent, so |B| ≤ |S| + 1.
    Hence n = |S| + |B| ≤ 2*|S| + 1 ≤ 2*floor(1/τ) + 1. -/
lemma n_bound {δ_d s t τ ε_G ε_bad : ℝ} {n : ℕ} {P : Set EuclideanPlane}
    (d : RawMultiscaleDecomp δ_d s t τ ε_G ε_bad n P)
    (hτ_pos : 0 < τ) (hΔ_pos : 0 < d.Δ) (hΔ_lt_one : d.Δ < 1)
    (hm_pos : 0 < d.m) :
    n ≤ 2 * ⌊1 / τ⌋ + 1 := by
  by_cases h_n : n = 0
  · rw [h_n]
    have h_floor_nonneg : 0 ≤ ⌊1 / τ⌋ := Int.floor_nonneg.mpr (by positivity)
    omega
  · have h_n_pos : 0 < n := by omega
    have h_logΔ_neg : Real.log d.Δ < 0 := Real.log_neg hΔ_pos hΔ_lt_one
    have h_width : ∀ (j : Fin n), j ∈ d.S →
        (d.i (j.val + 1) : ℝ) - (d.i j.val : ℝ) ≥ (d.m : ℝ) * τ := by
      intro j hj
      have h1 := d.h_S_ratio j hj
      have hδ : δ_d = d.Δ ^ d.m := d.hδ_d
      have hδd_pos : 0 < δ_d := by rw [hδ] <;> positivity
      have h_log_LHS : Real.log ((d.Δ ^ d.i j.val : ℝ) / (d.Δ ^ d.i (j.val + 1))) =
          ((d.i j.val : ℝ) - (d.i (j.val + 1) : ℝ)) * Real.log d.Δ := by
        rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow] <;> ring
      have h_log_RHS : Real.log (Real.rpow δ_d (-τ)) =
          -(d.m : ℝ) * τ * Real.log d.Δ := by
        have h1 : Real.log (Real.rpow δ_d (-τ)) = (-τ) * Real.log δ_d :=
          Real.log_rpow (by linarith) (-τ)
        have h2 : Real.log δ_d = Real.log (d.Δ ^ d.m) := by congr 1
        have h3 : Real.log (d.Δ ^ d.m) = (d.m : ℝ) * Real.log d.Δ := by
          rw [Real.log_pow] <;> ring
        rw [h1, h2, h3] <;> ring
      have h_pos1 : 0 < (d.Δ ^ d.i j.val : ℝ) / (d.Δ ^ d.i (j.val + 1)) := by positivity
      have h_pos2 : 0 < Real.rpow δ_d (-τ) := Real.rpow_pos_of_pos hδd_pos _
      have h_log_ineq : Real.log ((d.Δ ^ d.i j.val : ℝ) / (d.Δ ^ d.i (j.val + 1))) ≥
          Real.log (Real.rpow δ_d (-τ)) :=
        Real.log_le_log h_pos2 h1
      rw [h_log_LHS, h_log_RHS] at h_log_ineq
      nlinarith [h_logΔ_neg]
    let w_nat : ℕ → ℝ := fun i => (d.i (i + 1) : ℝ) - (d.i i : ℝ)
    let w : Fin n → ℝ := fun j => w_nat j.val
    have h_sum_all : ∑ j : Fin n, w j = (d.m : ℝ) := by
      have h1 : ∑ j : Fin n, w j = ∑ i ∈ Finset.range n, w_nat i := by
        rw [Finset.sum_fin_eq_sum_range]
        apply Finset.sum_congr rfl
        intro i hi
        have h_i_lt_n : i < n := Finset.mem_range.mp hi
        simp [h_i_lt_n, w, w_nat]
      rw [h1]
      have h2 : ∑ i ∈ Finset.range n, w_nat i = (d.i n : ℝ) - (d.i 0 : ℝ) := by
        exact Finset.sum_range_sub (fun i : ℕ => (d.i i : ℝ)) n
      rw [h2, d.hin, d.hi0] <;> norm_num
    have h_nonneg : ∀ j : Fin n, 0 ≤ w j := by
      intro j
      have h : d.i j.val < d.i (j.val + 1) := d.h_strict_mono j.val j.is_lt
      have h' : (d.i j.val : ℝ) ≤ (d.i (j.val + 1) : ℝ) := by exact_mod_cast h.le
      exact sub_nonneg.mpr h'
    have h_sum_S_le : ∑ j ∈ d.S, w j ≤ (d.m : ℝ) := by
      have h : ∑ j ∈ d.S, w j ≤ ∑ j : Fin n, w j :=
        Finset.sum_le_sum_of_subset_of_nonneg d.S.subset_univ (fun _ _ _ => h_nonneg _)
      rw [h_sum_all] at h
      exact h
    have h_sum_const : ∑ j ∈ d.S, ((d.m : ℝ) * τ) = (d.S.card : ℝ) * ((d.m : ℝ) * τ) := by
      rw [Finset.sum_const] <;> ring
    have h_sum_S_ge : ∑ j ∈ d.S, w j ≥ (d.S.card : ℝ) * (d.m : ℝ) * τ := by
      have h : ∑ j ∈ d.S, w j ≥ ∑ j ∈ d.S, ((d.m : ℝ) * τ) := by
        apply Finset.sum_le_sum
        intro j hj
        exact h_width j hj
      rw [h_sum_const] at h
      have h' : (d.S.card : ℝ) * ((d.m : ℝ) * τ) = (d.S.card : ℝ) * (d.m : ℝ) * τ := by ring
      rw [h'] at h
      exact h
    have h_S_card_le : (d.S.card : ℝ) ≤ 1 / τ := by
      have h7 : (d.S.card : ℝ) * (d.m : ℝ) * τ ≤ (d.m : ℝ) := by linarith
      have hm_pos' : (d.m : ℝ) > 0 := by exact_mod_cast hm_pos
      have h8 : (d.S.card : ℝ) * τ ≤ 1 := by nlinarith
      calc (d.S.card : ℝ)
        = ((d.S.card : ℝ) * τ) / τ := by field_simp [hτ_pos.ne'] <;> ring
      _ ≤ 1 / τ := by gcongr
    have h_S_card_floor : (d.S.card : Int) ≤ ⌊1 / τ⌋ := by
      rw [Int.le_floor]
      exact h_S_card_le
    have h_B_card_le : d.B.card ≤ d.S.card + 1 := by
      by_cases hB_empty : d.B = ∅
      · simp [hB_empty]
      · have hB_nonempty : d.B.Nonempty := by
          simpa [Finset.nonempty_iff_ne_empty] using hB_empty
        let b_max := d.B.max' hB_nonempty
        have h_bmax_mem : b_max ∈ d.B := d.B.max'_mem hB_nonempty
        let B' := d.B.erase b_max
        have h_B'_card : B'.card = d.B.card - 1 := by
          rw [Finset.card_erase_of_mem h_bmax_mem] <;> omega
        have h_map : ∀ j ∈ B', ∃ (k : Fin n), k.val = j.val + 1 ∧ k ∈ d.S := by
          intro j hj
          have h_j_in_B : j ∈ d.B := (Finset.mem_erase.mp hj).2
          have h_j_ne_max : j ≠ b_max := (Finset.mem_erase.mp hj).1
          have h_j_le_max : j.val ≤ b_max.val := Finset.le_max' d.B j h_j_in_B
          have h_j_lt_max : j.val < b_max.val := by
            by_contra h_eq
            have h : j.val = b_max.val := by omega
            have h' : j = b_max := Fin.ext h
            exact h_j_ne_max h'
          have h_j1_lt_n : j.val + 1 < n := by omega
          let k : Fin n := ⟨j.val + 1, h_j1_lt_n⟩
          have h_k_not_B : k ∉ d.B := d.h_B_no_adjacent j h_j_in_B k rfl
          have h_k_in_univ : k ∈ d.S ∪ d.B := by
            rw [d.h_partition]; exact Finset.mem_univ k
          have h_k_in_S : k ∈ d.S :=
            (Finset.mem_union.mp h_k_in_univ).resolve_right h_k_not_B
          exact ⟨k, rfl, h_k_in_S⟩
        let f : Fin n → Fin n := fun j =>
          if hj : j ∈ B' then Classical.choose (h_map j hj) else j
        have hf1 : ∀ j ∈ B', (f j).val = j.val + 1 := by
          intro j hj
          have h_fj : f j = Classical.choose (h_map j hj) := by
            rw [show f j = Classical.choose (h_map j hj) from by simp [f, hj]]
          rw [h_fj]
          exact (Classical.choose_spec (h_map j hj)).1
        have hf2 : ∀ j ∈ B', f j ∈ d.S := by
          intro j hj
          have h_fj : f j = Classical.choose (h_map j hj) := by simp [f, hj]
          rw [h_fj]
          exact (Classical.choose_spec (h_map j hj)).2
        have h_f_inj : Set.InjOn f (B' : Set (Fin n)) := by
          intro j1 hj1 j2 hj2 h_eq
          have h1 : (f j1).val = j1.val + 1 := hf1 j1 hj1
          have h2 : (f j2).val = j2.val + 1 := hf1 j2 hj2
          have h3 : j1.val + 1 = j2.val + 1 := by rw [←h1, ←h2, h_eq]
          have h4 : j1.val = j2.val := by omega
          exact Fin.ext h4
        have h10 : B'.card ≤ d.S.card := by
          have h11 : Finset.image f B' ⊆ d.S := by
            intro x hx
            rcases Finset.mem_image.mp hx with ⟨j, hj, rfl⟩
            exact hf2 j hj
          have h12 : (Finset.image f B').card = B'.card := by
            rw [Finset.card_image_of_injOn h_f_inj]
          have h13 : (Finset.image f B').card ≤ d.S.card := Finset.card_le_card h11
          rw [h12] at h13
          exact h13
        rw [h_B'_card] at h10
        omega
    have h_n_eq : n = d.S.card + d.B.card := by
      have h1 : (d.S ∪ d.B).card = d.S.card + d.B.card := by
        rw [Finset.card_union_of_disjoint d.h_disjoint]
      have h2 : d.S ∪ d.B = Finset.univ := d.h_partition
      have h3 : (Finset.univ : Finset (Fin n)).card = n := by simp
      rw [h2] at h1
      rw [h3] at h1
      have h4 : n = d.S.card + d.B.card := by omega
      exact h4
    have h_final : (n : ℝ) ≤ 2 * (⌊1 / τ⌋ : ℝ) + 1 := by
      have h4 : (n : ℝ) = (d.S.card : ℝ) + (d.B.card : ℝ) := by exact_mod_cast h_n_eq
      have h5 : (d.B.card : ℝ) ≤ (d.S.card : ℝ) + 1 := by exact_mod_cast h_B_card_le
      have h6 : (d.S.card : ℝ) ≤ (⌊1 / τ⌋ : ℝ) := by exact_mod_cast h_S_card_floor
      linarith
    exact_mod_cast h_final

end DirecretisedFurstenbergEstimate.Section9

end
