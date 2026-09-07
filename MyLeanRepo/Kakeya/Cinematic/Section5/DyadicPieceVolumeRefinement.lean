import MyLeanRepo.Kakeya.Cinematic.Section5.DyadicPieceVolumeRefinementInputs

/-!
# Retain one dyadic layer of assigned piece volumes
-/

namespace Kakeya.Cinematic

theorem dyadic_piece_volume_refinement :
    DyadicPieceVolumeRefinementStatement := by
  intro N L weight lower upper hL h_lower_pos h_range h_weight h_total_pos h_half
  classical

  let S : Finset (Fin N) := Finset.univ.filter (fun i => lower ≤ weight i)

  have hS_nonempty : S.Nonempty := by
    by_contra h
    have hS_empty : S = ∅ := by simpa using h
    have h_sum_S : ∑ i ∈ S, weight i = 0 := by
      rw [hS_empty]
      simp
    have h1 : (∑ i, weight i) ≤ 2 * (∑ i ∈ S, weight i) := h_half
    rw [h_sum_S] at h1
    have h2 : (∑ i, weight i) ≤ 0 := by simpa using h1
    have h3 : (∑ i, weight i) = 0 := by
      simpa [le_zero_iff] using h2
    rw [h3] at h_total_pos
    exact False.elim (lt_irrefl 0 h_total_pos)

  have h_exists : ∀ (i : Fin N), ∃ j : ℕ,
      weight i < (2 : ENNReal) ^ (j + 1) * lower := by
    intro i
    have h1 : weight i ≤ upper := h_weight i
    have h2 : weight i < (2 : ENNReal) ^ L * lower := h1.trans_lt h_range
    refine ⟨L - 1, ?_⟩
    have h3 : (L - 1) + 1 = L := by omega
    rw [h3]
    exact h2

  let layer : Fin N → ℕ := fun i => Nat.find (h_exists i)

  have h_layer_upper : ∀ i,
      weight i < (2 : ENNReal) ^ (layer i + 1) * lower := by
    intro i
    exact Nat.find_spec (h_exists i)

  have h_layer_le : ∀ i, layer i ≤ L - 1 := by
    intro i
    exact Nat.find_min' (h_exists i) (by
      have h3 : (L - 1) + 1 = L := by omega
      rw [h3]
      exact (h_weight i).trans_lt h_range)

  have h_layer_lt_L : ∀ i, layer i < L := by
    intro i
    have h4 : layer i ≤ L - 1 := h_layer_le i
    omega

  have h_layer_lower : ∀ i ∈ S,
      (2 : ENNReal) ^ layer i * lower ≤ weight i := by
    intro i hi
    have h_iS : lower ≤ weight i := (Finset.mem_filter.mp hi).2
    by_cases h_case : layer i = 0
    · rw [h_case]
      simpa using h_iS
    · have h_pos : 0 < layer i := Nat.pos_of_ne_zero h_case
      set k : ℕ := layer i - 1 with hk
      have h_k_lt : k < layer i := by omega
      have h4 :
          ¬weight i < (2 : ENNReal) ^ (k + 1) * lower :=
        Nat.find_min (h_exists i) h_k_lt
      have h5 : k + 1 = layer i := by omega
      rw [h5] at h4
      exact le_of_not_gt h4

  let S_j : Fin L → Finset (Fin N) :=
    fun j => S.filter (fun i => layer i = j.val)

  have h_disj : ∀ (j1 j2 : Fin L), j1 ≠ j2 →
      Disjoint (S_j j1) (S_j j2) := by
    intro j1 j2 hne
    simp only [S_j, Finset.disjoint_left]
    intro i hi1 hi2
    have h1 : layer i = j1.val := (Finset.mem_filter.mp hi1).2
    have h2 : layer i = j2.val := (Finset.mem_filter.mp hi2).2
    have h3 : j1.val = j2.val := by rw [← h1, h2]
    have h4 : j1 = j2 := by
      apply Fin.ext
      exact h3
    exact hne h4

  have h_union :
      S = Finset.biUnion (Finset.univ : Finset (Fin L)) S_j := by
    ext i
    simp only [S_j, Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · intro hi
      let j : Fin L := ⟨layer i, h_layer_lt_L i⟩
      refine ⟨j, ?_⟩
      simp only [Finset.mem_filter]
      exact ⟨hi, by simp [j]⟩
    · rintro ⟨j, hj⟩
      exact (Finset.mem_filter.mp hj).1

  have h_sum_decomp :
      ∑ i ∈ S, weight i =
        ∑ j : Fin L, ∑ i ∈ S_j j, weight i := by
    rw [h_union, Finset.sum_biUnion]
    intro j _ k _ hne
    exact h_disj j k hne

  let a : Fin L → ENNReal := fun j => ∑ i ∈ S_j j, weight i

  have h_univ_nonempty :
      (Finset.univ : Finset (Fin L)).Nonempty := by
    refine ⟨⟨0, hL⟩, by simp⟩
  have h_max_exists : ∃ (j0 : Fin L), ∀ j : Fin L, a j ≤ a j0 := by
    have h := Finset.exists_max_image
      (Finset.univ : Finset (Fin L)) a h_univ_nonempty
    rcases h with ⟨j0, _, h_max⟩
    exact ⟨j0, fun j => h_max j (Finset.mem_univ j)⟩
  rcases h_max_exists with ⟨j0, h_max⟩

  have h_pigeon : ∑ j : Fin L, a j ≤ (L : ENNReal) * a j0 := by
    have h1 : ∑ j : Fin L, a j ≤ ∑ j : Fin L, a j0 :=
      Finset.sum_le_sum (fun j _ => h_max j)
    have h2 : ∑ j : Fin L, a j0 = (L : ENNReal) * a j0 := by
      calc
        ∑ j : Fin L, a j0 =
            Finset.card (Finset.univ : Finset (Fin L)) • a j0 := by
              rw [Finset.sum_const]
        _ = L • a j0 := by
          rw [show Finset.card (Finset.univ : Finset (Fin L)) = L by simp]
        _ = (L : ENNReal) * a j0 := by
          exact nsmul_eq_mul L (a j0)
    rw [h2] at h1
    exact h1

  have h_sum_S_le :
      ∑ i ∈ S, weight i ≤ (L : ENNReal) * a j0 := by
    rw [h_sum_decomp]
    exact h_pigeon

  have h_mass :
      (∑ i, weight i) ≤ ((2 * L : ℕ) : ENNReal) * a j0 := by
    calc
      (∑ i, weight i) ≤ 2 * ∑ i ∈ S, weight i := h_half
      _ ≤ 2 * ((L : ENNReal) * a j0) := by gcongr
      _ = ((2 * L : ℕ) : ENNReal) * a j0 := by
        have h2 : (2 : ENNReal) * (L : ENNReal) =
            ((2 * L : ℕ) : ENNReal) := by norm_cast
        rw [← mul_assoc, h2]

  have h_a_pos : 0 < a j0 := by
    by_contra h
    have h' : a j0 = 0 := by simpa using h
    rw [h'] at h_mass
    have h4 : (∑ i, weight i) ≤ 0 := by simpa using h_mass
    have h5 : (∑ i, weight i) = 0 := by
      simpa [le_zero_iff] using h4
    rw [h5] at h_total_pos
    exact False.elim (lt_irrefl 0 h_total_pos)

  have h_Sj_nonempty : (S_j j0).Nonempty := by
    by_contra h
    have h' : S_j j0 = ∅ := by simpa using h
    have h6 : a j0 = 0 := by
      dsimp only [a]
      rw [h']
      simp
    rw [h6] at h_a_pos
    simp at h_a_pos

  have h_layer_property : ∀ i ∈ S_j j0,
      (2 : ENNReal) ^ j0.val * lower ≤ weight i ∧
      weight i < (2 : ENNReal) ^ (j0.val + 1) * lower := by
    intro i hi
    have h_iS : i ∈ S := (Finset.mem_filter.mp hi).1
    have h_layer_eq : layer i = j0.val := (Finset.mem_filter.mp hi).2
    constructor
    · have h7 := h_layer_lower i h_iS
      rw [h_layer_eq] at h7
      exact h7
    · have h8 := h_layer_upper i
      rw [h_layer_eq] at h8
      exact h8

  exact ⟨j0, S_j j0, h_Sj_nonempty, h_layer_property, h_mass⟩

end Kakeya.Cinematic
