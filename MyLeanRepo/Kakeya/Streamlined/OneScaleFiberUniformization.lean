import MyLeanRepo.Kakeya.Streamlined.MultiplicityPigeonhole

/-!
# One-scale finite-fiber uniformization

This module contains the cover-independent combinatorial regularization used
by both the historical multiscale assigned-cover construction and the
paper-facing dilated refinement producer.
-/

noncomputable section

namespace Kakeya.Streamlined

/--
One-scale dyadic uniformization on a finite subset `S`.

Given `parent : I → J` and mass `w`, select `S' ⊆ S` that is a union
of entire parent fibers within `S`, all nonempty selected fibers have
cardinalities within factor 2, and retained mass ≥ mass(S) / (log |S| + 1).
-/
lemma one_scale_on_finset
    {I J : Type*} [DecidableEq I] [DecidableEq J]
    (S : Finset I) (hS_nonempty : S.Nonempty)
    (parent : I → J) (w : I → ENNReal) :
    ∃ (S' : Finset I),
      S' ⊆ S ∧
      (∀ i ∈ S', ∀ i' ∈ S, parent i' = parent i → i' ∈ S') ∧
      (∀ (j j' : J),
        0 < (S'.filter (fun i => parent i = j)).card →
        0 < (S'.filter (fun i => parent i = j')).card →
        ((S'.filter (fun i => parent i = j)).card : ENNReal) ≤
          2 * ((S'.filter (fun i => parent i = j')).card : ENNReal)) ∧
      (∑ i ∈ S', w i) * (Nat.log 2 S.card + 1 : ENNReal) ≥
        ∑ i ∈ S, w i := by
  classical
  let n := S.card
  have hn_pos : 0 < n := Finset.Nonempty.card_pos hS_nonempty

  let fiberSize (j : J) : ℕ := (S.filter (fun i => parent i = j)).card
  let bin (j : J) : ℕ := Nat.log 2 (fiberSize j)

  have h_fiber_le_n : ∀ j, fiberSize j ≤ n := by
    intro j
    exact Finset.card_le_card (Finset.filter_subset _ _)
  have h_bin_le : ∀ j, bin j ≤ Nat.log 2 n := by
    intro j
    exact Nat.log_mono_right (h_fiber_le_n j)

  let K := Nat.log 2 n + 1
  let bins : Finset ℕ := Finset.range K

  have h_bins_cover : ∀ j, fiberSize j > 0 → bin j ∈ bins := by
    intro j hj
    have h1 : bin j ≤ Nat.log 2 n := h_bin_le j
    have h2 : bin j < K := by
      dsimp only [K]
      omega
    exact Finset.mem_range.mpr h2

  let idxBin (i : I) : ℕ := bin (parent i)
  let binMass (k : ℕ) : ENNReal :=
    ∑ i ∈ (S.filter (fun i => idxBin i = k)), w i
  let t : ℕ → Finset I := fun k => S.filter (fun i => idxBin i = k)

  have h_disj :
      ∀ k1 ∈ bins, ∀ k2 ∈ bins, k1 ≠ k2 → Disjoint (t k1) (t k2) := by
    intro k1 _ k2 _ hne
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    have h1 : idxBin i = k1 := (Finset.mem_filter.mp hi1).2
    have h2 : idxBin i = k2 := (Finset.mem_filter.mp hi2).2
    exact hne (h1.symm.trans h2)

  have h_union : bins.biUnion t = S := by
    apply Finset.ext
    intro i
    simp only [Finset.mem_biUnion]
    constructor
    · rintro ⟨k, _, hik⟩
      exact (Finset.mem_filter.mp hik).1
    · intro hi
      have h_pos : fiberSize (parent i) > 0 := by
        have h_i_in :
            i ∈ S.filter (fun i' => parent i' = parent i) := by
          rw [Finset.mem_filter]
          exact ⟨hi, rfl⟩
        exact Finset.card_pos.mpr ⟨i, h_i_in⟩
      have hbin : idxBin i ∈ bins :=
        h_bins_cover (parent i) h_pos
      exact
        ⟨idxBin i, hbin,
          by simpa [t, Finset.mem_filter] using hi⟩

  have h_sum_bins :
      ∑ k ∈ bins, binMass k = ∑ i ∈ S, w i := by
    have h :
        ∑ k ∈ bins, ∑ i ∈ t k, w i =
          ∑ i ∈ bins.biUnion t, w i :=
      (Finset.sum_biUnion h_disj).symm
    rw [h, h_union]

  have h_bins_pos : 0 < bins.card := by
    simp [bins, K]
    <;> omega

  have h_exists :
      ∃ k ∈ bins, ∀ j ∈ bins, binMass j ≤ binMass k := by
    exact Finset.exists_max_image bins binMass
      (Finset.nonempty_iff_ne_empty.mpr
        (by simp [bins, K] <;> omega))
  rcases h_exists with ⟨k, _hk, hmax⟩

  let S' : Finset I := t k

  have hS'_subset : S' ⊆ S := by
    intro i hi
    exact (Finset.mem_filter.mp hi).1

  have h1_union :
      ∀ i ∈ S', ∀ i' ∈ S, parent i' = parent i → i' ∈ S' := by
    intro i hi i' hi' hparent
    have h_i_bin : idxBin i = k :=
      (Finset.mem_filter.mp hi).2
    have h_i'_bin : idxBin i' = bin (parent i') := by
      rfl
    have h_eq : bin (parent i') = bin (parent i) := by
      rw [hparent]
    have h_i'_bin_k : idxBin i' = k := by
      rw [h_i'_bin, h_eq]
      exact h_i_bin
    simpa [S', t, Finset.mem_filter] using
      ⟨hi', h_i'_bin_k⟩

  let fiberSize' (j : J) : ℕ :=
    (S'.filter (fun i => parent i = j)).card

  have h_fiber_full :
      ∀ j, 0 < fiberSize' j → fiberSize' j = fiberSize j := by
    intro j hj
    have h_nonempty : ∃ i, i ∈ S' ∧ parent i = j := by
      rcases Finset.card_pos.mp hj with ⟨i, hi⟩
      exact
        ⟨i, (Finset.mem_filter.mp hi).1,
          (Finset.mem_filter.mp hi).2⟩
    rcases h_nonempty with ⟨i, hi, hparent⟩
    have h_j_bin : bin j = k := by
      have h : idxBin i = k := (Finset.mem_filter.mp hi).2
      have h2 : idxBin i = bin (parent i) := by
        rfl
      rw [h2] at h
      rw [hparent] at h
      exact h
    have h_iff :
        ∀ i', i' ∈ S → parent i' = j → i' ∈ S' := by
      intro i' hi' hparent'
      have h_i'_bin : idxBin i' = bin j := by
        have h3 : idxBin i' = bin (parent i') := by
          rfl
        rw [h3, hparent']
      have h4 : idxBin i' = k := by
        rw [h_i'_bin, h_j_bin]
      simpa [S', t, Finset.mem_filter] using ⟨hi', h4⟩
    have h_eq :
        S'.filter (fun i' => parent i' = j) =
          S.filter (fun i' => parent i' = j) := by
      apply Finset.ext
      intro i'
      simp only [Finset.mem_filter]
      constructor
      · intro h
        exact ⟨hS'_subset h.1, h.2⟩
      · intro h
        exact ⟨h_iff i' h.1 h.2, h.2⟩
    dsimp only [fiberSize']
    rw [h_eq]

  have h2_uniform :
      ∀ j j', 0 < fiberSize' j → 0 < fiberSize' j' →
        (fiberSize' j : ENNReal) ≤
          2 * (fiberSize' j' : ENNReal) := by
    intro j j' hj hj'
    have h_j_nonempty : ∃ i, i ∈ S' ∧ parent i = j := by
      rcases Finset.card_pos.mp hj with ⟨i, hi⟩
      exact
        ⟨i, (Finset.mem_filter.mp hi).1,
          (Finset.mem_filter.mp hi).2⟩
    rcases h_j_nonempty with ⟨i, hi, hparent⟩
    have h_j_bin : bin j = k := by
      have h : idxBin i = k := (Finset.mem_filter.mp hi).2
      have h2 : idxBin i = bin (parent i) := by
        rfl
      rw [h2] at h
      rw [hparent] at h
      exact h
    have h_j'_nonempty :
        ∃ i', i' ∈ S' ∧ parent i' = j' := by
      rcases Finset.card_pos.mp hj' with ⟨i', hi'⟩
      exact
        ⟨i', (Finset.mem_filter.mp hi').1,
          (Finset.mem_filter.mp hi').2⟩
    rcases h_j'_nonempty with ⟨i', hi', hparent'⟩
    have h_j'_bin : bin j' = k := by
      have h : idxBin i' = k := (Finset.mem_filter.mp hi').2
      have h2 : idxBin i' = bin (parent i') := by
        rfl
      rw [h2] at h
      rw [hparent'] at h
      exact h
    have h_eq_j : fiberSize' j = fiberSize j :=
      h_fiber_full j hj
    have h_eq_j' : fiberSize' j' = fiberSize j' :=
      h_fiber_full j' hj'
    rw [h_eq_j, h_eq_j']
    have h_fiber_j_pos : 0 < fiberSize j := by
      rw [← h_eq_j]
      exact hj
    have h_fiber_j'_pos : 0 < fiberSize j' := by
      rw [← h_eq_j']
      exact hj'
    have h3 : 2 ^ k ≤ fiberSize j := by
      rw [← h_j_bin]
      exact Nat.pow_log_le_self 2 (ne_of_gt h_fiber_j_pos)
    have h4 : fiberSize j' < 2 ^ (k + 1) := by
      rw [← h_j'_bin]
      exact
        Nat.lt_pow_succ_log_self (by norm_num) (fiberSize j')
    have h5 : fiberSize j < 2 ^ (k + 1) := by
      rw [← h_j_bin]
      exact
        Nat.lt_pow_succ_log_self (by norm_num) (fiberSize j)
    have h6 : 2 ^ k ≤ fiberSize j' := by
      rw [← h_j'_bin]
      exact Nat.pow_log_le_self 2 (ne_of_gt h_fiber_j'_pos)
    exact_mod_cast by omega

  have h3_mass :
      (∑ i ∈ S', w i) * (K : ENNReal) ≥
        ∑ i ∈ S, w i := by
    have h_sum :
        ∑ j ∈ bins, binMass j ≤
          ∑ j ∈ bins, binMass k := by
      apply Finset.sum_le_sum
      intro j hj
      exact hmax j hj
    have h_count :
        ∑ j ∈ bins, binMass k =
          (bins.card : ENNReal) * binMass k := by
      rw [Finset.sum_const, mul_comm]
      <;> ring
    have h_K :
        (bins.card : ENNReal) = (K : ENNReal) := by
      simp [bins, Finset.card_range]
    have h_final :
        (K : ENNReal) * binMass k ≥ ∑ i ∈ S, w i := by
      calc
        ∑ i ∈ S, w i
            = ∑ j ∈ bins, binMass j := h_sum_bins.symm
        _ ≤ ∑ j ∈ bins, binMass k := h_sum
        _ = (bins.card : ENNReal) * binMass k := h_count
        _ = (K : ENNReal) * binMass k := by rw [h_K]
    have h_comm :
        binMass k * (K : ENNReal) =
          (K : ENNReal) * binMass k := by
      ring
    have h_final2 :
        binMass k * (K : ENNReal) ≥ ∑ i ∈ S, w i := by
      rw [h_comm]
      exact h_final
    have h_S'_mass : ∑ i ∈ S', w i = binMass k := by
      rfl
    rw [h_S'_mass]
    exact h_final2

  have h_K_def :
      (K : ENNReal) =
        (Nat.log 2 n + 1 : ENNReal) := by
    simp [K]
  rw [h_K_def] at h3_mass

  exact
    ⟨S', hS'_subset, h1_union, h2_uniform, h3_mass⟩

end Kakeya.Streamlined
