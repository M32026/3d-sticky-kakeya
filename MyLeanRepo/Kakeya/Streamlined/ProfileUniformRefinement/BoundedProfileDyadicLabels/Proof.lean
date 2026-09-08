import MyLeanRepo.Kakeya.Streamlined.ProfileUniformRefinement.BoundedProfileDyadicLabels

noncomputable section

namespace Kakeya.Streamlined

lemma exists_profile_dyadic_bin
    (N : ℕ) (_hN : 1 ≤ N) (x : ENNReal)
    (hx1 : 1 ≤ x) (hx2 : x ≤ (N : ENNReal)) :
    ∃ k : Fin (Nat.log 2 N + 1), InDyadicProfileBin k x := by
  let S : Finset ℕ :=
    Finset.filter
      (fun k : ℕ => ((2 ^ k : ℕ) : ENNReal) ≤ x)
      (Finset.range (Nat.log 2 N + 1))
  have h0_in : 0 ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_range]
    constructor
    · omega
    · simpa using hx1
  have hS_nonempty : S.Nonempty := ⟨0, h0_in⟩
  let k : ℕ := S.max' hS_nonempty
  have hk_in : k ∈ S := Finset.max'_mem S hS_nonempty
  have hk_range : k ∈ Finset.range (Nat.log 2 N + 1) :=
    (Finset.mem_filter.mp hk_in).1
  have hk_lt : k < Nat.log 2 N + 1 :=
    Finset.mem_range.mp hk_range
  have hk_le : ((2 ^ k : ℕ) : ENNReal) ≤ x :=
    (Finset.mem_filter.mp hk_in).2
  let kfin : Fin (Nat.log 2 N + 1) := ⟨k, hk_lt⟩
  have h_upper : x ≤ ((2 ^ (k + 1) : ℕ) : ENNReal) := by
    by_cases h : k < Nat.log 2 N
    · have h_k1_range :
          k + 1 ∈ Finset.range (Nat.log 2 N + 1) := by
        simp only [Finset.mem_range]
        omega
      have h_k1_notin_S : k + 1 ∉ S := by
        intro h'
        have h_max : k + 1 ≤ k :=
          Finset.le_max' S (k + 1) h'
        omega
      have h_not_le :
          ¬ (((2 ^ (k + 1) : ℕ) : ENNReal) ≤ x) := by
        intro h_le
        have h_in : k + 1 ∈ S := by
          simp only [S, Finset.mem_filter]
          exact ⟨h_k1_range, h_le⟩
        exact h_k1_notin_S h_in
      exact (not_le.mp h_not_le).le
    · have h_k_eq : k = Nat.log 2 N := by
        omega
      have hN_lt : N < 2 ^ (Nat.log 2 N + 1) :=
        Nat.lt_pow_succ_log_self (by norm_num) N
      rw [h_k_eq]
      have h1 : x ≤ (N : ENNReal) := hx2
      have h2 :
          (N : ENNReal) <
            ((2 ^ (Nat.log 2 N + 1) : ℕ) : ENNReal) := by
        exact_mod_cast hN_lt
      exact h1.trans h2.le
  refine ⟨kfin, hk_le, ?_⟩
  have h_eq :
      2 * ((2 ^ k : ℕ) : ENNReal) =
        ((2 ^ (k + 1) : ℕ) : ENNReal) := by
    norm_cast
    ring
  rw [h_eq]
  exact h_upper

theorem bounded_profile_dyadic_labels :
    BoundedProfileDyadicLabelsStatement := by
  intro J _ _ N hN branchProfile frostmanProfile deltaMaxProfile
    hbranch hfrostman hdelta
  have h_branch :
      ∀ j : J, ∃ k : Fin (Nat.log 2 N + 1),
        InDyadicProfileBin k (branchProfile j) := by
    intro j
    exact exists_profile_dyadic_bin N hN (branchProfile j)
      (hbranch j).1 (hbranch j).2
  have h_frostman :
      ∀ j : J, ∃ k : Fin (Nat.log 2 N + 1),
        InDyadicProfileBin k (frostmanProfile j) := by
    intro j
    exact exists_profile_dyadic_bin N hN (frostmanProfile j)
      (hfrostman j).1 (hfrostman j).2
  have h_delta :
      ∀ j : J, ∃ k : Fin (Nat.log 2 N + 1),
        InDyadicProfileBin k (deltaMaxProfile j) := by
    intro j
    exact exists_profile_dyadic_bin N hN (deltaMaxProfile j)
      (hdelta j).1 (hdelta j).2
  choose branchBin hbranchBin using h_branch
  choose frostmanBin hfrostmanBin using h_frostman
  choose deltaMaxBin hdeltaMaxBin using h_delta
  exact ⟨branchBin, frostmanBin, deltaMaxBin,
    hbranchBin, hfrostmanBin, hdeltaMaxBin⟩

end Kakeya.Streamlined
