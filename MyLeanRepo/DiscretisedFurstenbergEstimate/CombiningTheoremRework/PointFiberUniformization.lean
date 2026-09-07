module

/-
  Point Fiber Uniformization

  Single-scale dyadic band selection for point fibers over coarse squares.

  Given a fine point set P₀ and its coarse square image Q0, with positive
  fiber sizes bounded by N_max, selects a subset Q0' ⊆ Q0 such that all
  fibers lie in [M, 2M), |Q0| ≤ 2*M*numDyadicLevels(N_max) * |Q0'|,
  AND P₀'.card ≥ P₀.card / numDyadicLevels(N_max) (sum-based retention).

  Restricts P₀ to P₀' = points whose containing square is in Q0'.

  Core: exists_dyadic_sum_subfamily (sum-weighted dyadic pigeonhole, real-valued).
-/

public import MyLeanRepo.InductionOnScales.Pigeonhole
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.DiscretisedFurstenbergEstimate.InductionConfigurations
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DiscretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.CombiningTheorem
open InductionConfigurations

/-- Sum-weighted dyadic subfamily selection (real division).

    Given weights `f : ι → ℕ` bounded by N and positive on s, selects
    `s' ⊆ s` and `M` such that all weights in s' are in `[M, 2*M)`, and
    the total real weight of s' is at least `total_weight / numDyadicLevels N`.

    Uses a real averaging argument to avoid truncated ℕ division. -/
lemma exists_dyadic_sum_subfamily {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℕ) {N : ℕ} (hN : 0 < N)
    (h_bound : ∀ i ∈ s, f i ≤ N) (h_pos : ∀ i ∈ s, 0 < f i) :
    ∃ (M : ℕ) (s' : Finset ι), s' ⊆ s ∧
      (∀ i ∈ s', M ≤ f i ∧ f i < 2 * M) ∧
      ∑ i ∈ s', (f i : ℝ) ≥ (∑ i ∈ s, (f i : ℝ)) / (numDyadicLevels N : ℝ) := by
  let L := numDyadicLevels N
  have hL_pos : 0 < L := by simp [L, numDyadicLevels] <;> omega
  let g : ι → ℕ := fun i => dyadicLevel (f i)
  let levelSet := fun j : ℕ => s.filter (fun x => g x = j)

  have h_g_range : ∀ i ∈ s, g i ∈ Finset.range L := by
    intro i hi
    have hfi_pos : 0 < f i := h_pos i hi
    have hfi_ne_zero : f i ≠ 0 := by linarith
    have h1 : g i = Nat.log 2 (f i) + 1 := by
      simp [g, dyadicLevel, hfi_ne_zero]
    rw [h1]
    have h2 : Nat.log 2 (f i) ≤ Nat.log 2 N := Nat.log_mono_right (h_bound i hi)
    have h4 : Nat.log 2 N + 1 < L := by
      simp [L, numDyadicLevels] <;> omega
    have h5 : Nat.log 2 (f i) + 1 < L := by linarith
    exact Finset.mem_range.mpr h5

  have h_disj : (Finset.range L : Set ℕ).PairwiseDisjoint levelSet := by
    intro j _ k _ hjk
    have h : Disjoint (levelSet j) (levelSet k) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      have h1 : g x = j := (Finset.mem_filter.mp hx1).2
      have h2 : g x = k := (Finset.mem_filter.mp hx2).2
      have h3 : j = k := h1.symm.trans h2
      exact hjk h3
    exact h

  have h_union : (Finset.biUnion (Finset.range L) levelSet) = s := by
    ext i
    simp only [Finset.mem_biUnion, levelSet, Finset.mem_filter]
    constructor
    · rintro ⟨j, _, hi, _⟩; exact hi
    · intro hi; exact ⟨g i, h_g_range i hi, hi, rfl⟩

  have h_partition : ∑ j ∈ Finset.range L, ∑ i ∈ levelSet j, (f i : ℝ) = ∑ i ∈ s, (f i : ℝ) := by
    rw [← Finset.sum_biUnion h_disj, h_union]

  have h_avg : ∃ j ∈ Finset.range L,
      (∑ i ∈ levelSet j, (f i : ℝ)) ≥ (∑ i ∈ s, (f i : ℝ)) / (L : ℝ) := by
    by_contra h
    push Not at h
    have h_sum_lt : ∑ j ∈ Finset.range L, (∑ i ∈ levelSet j, (f i : ℝ)) <
        ∑ j ∈ Finset.range L, ((∑ i ∈ s, (f i : ℝ)) / (L : ℝ)) :=
      Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr (ne_of_gt hL_pos))
        (fun j hj => h j hj)
    have h_rhs : ∑ j ∈ Finset.range L, ((∑ i ∈ s, (f i : ℝ)) / (L : ℝ)) = (∑ i ∈ s, (f i : ℝ)) := by
      simp [Finset.sum_const, hL_pos.ne'] <;> field_simp [hL_pos.ne'] <;> ring
    rw [h_rhs] at h_sum_lt
    rw [h_partition] at h_sum_lt
    exact lt_irrefl _ h_sum_lt

  rcases h_avg with ⟨j, hj_range, h_sum_real⟩
  let s' := levelSet j

  by_cases h_j0 : j = 0
  · -- j = 0: all f i > 0, so level 0 must be empty; hence s is empty.
    have h_s'_empty : s' = ∅ := by
      ext i
      simp only [s', levelSet, Finset.mem_filter]
      constructor
      · rintro ⟨hi, hlev⟩
        have h0 : f i = 0 := by
          simp [dyadicLevel, g, h_j0] at hlev <;> omega
        have hpos : 0 < f i := h_pos i hi
        linarith
      · intro h_cont
        simpa using h_cont
    have h_sum_real' : ∑ i ∈ s', (f i : ℝ) ≥ (∑ i ∈ s, (f i : ℝ)) / (L : ℝ) := by
      simpa [s'] using h_sum_real
    rw [h_s'_empty] at h_sum_real'
    have h_total_nonneg : 0 ≤ (∑ i ∈ s, (f i : ℝ)) := by positivity
    have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL_pos
    have h_total_zero : (∑ i ∈ s, (f i : ℝ)) = 0 := by
      have h : (∑ i ∈ s, (f i : ℝ)) / (L : ℝ) ≤ 0 := by simpa using h_sum_real'
      have h2 : 0 ≤ (∑ i ∈ s, (f i : ℝ)) / (L : ℝ) := by positivity
      have h3 : (∑ i ∈ s, (f i : ℝ)) / (L : ℝ) = 0 := by linarith
      have h4 : (∑ i ∈ s, (f i : ℝ)) = 0 := by
        exact (div_eq_zero_iff).mp h3 |>.resolve_right hLpos.ne'
      exact h4
    have h_s_empty : s = ∅ := by
      have h_all_nonneg : ∀ i ∈ s, 0 ≤ (f i : ℝ) := by intro i _; positivity
      have h_all_zero : ∀ i ∈ s, (f i : ℝ) = 0 :=
        Finset.sum_eq_zero_iff_of_nonneg h_all_nonneg |>.mp h_total_zero
      by_contra hne
      rcases Finset.nonempty_iff_ne_empty.mpr hne with ⟨i, hi⟩
      have hpos : 0 < f i := h_pos i hi
      have h0 : (f i : ℝ) = 0 := h_all_zero i hi
      have hpos' : (0 : ℝ) < (f i : ℝ) := by exact_mod_cast hpos
      rw [h0] at hpos'
      <;> linarith
    refine ⟨1, ∅, by simp, by simp, ?_⟩
    rw [h_s_empty] <;> simp
  · -- j ≥ 1
    have h_j_pos : 1 ≤ j := by omega
    let M := 2^(j-1)
    have h_range : ∀ i ∈ s', M ≤ f i ∧ f i < 2 * M := by
      intro i hi
      have h_eq : g i = j := (Finset.mem_filter.mp hi).2
      have h_posi : 0 < f i := h_pos i (Finset.mem_filter.mp hi).1
      have hfi_ne_zero : f i ≠ 0 := by linarith
      have h_log : Nat.log 2 (f i) + 1 = j := by
        simp [dyadicLevel, g, hfi_ne_zero] at h_eq <;> omega
      have h1 : 2 ^ (j - 1) ≤ f i := by
        have h2 : 2 ^ Nat.log 2 (f i) ≤ f i := Nat.pow_log_le_self 2 hfi_ne_zero
        have h3 : Nat.log 2 (f i) = j - 1 := by omega
        rw [h3] at h2; exact h2
      have h4 : f i < 2 ^ j := by
        by_cases hfi1 : f i = 1
        · have hlog_val : Nat.log 2 (f i) = 0 := by rw [hfi1] <;> simp
          have hj1 : j = 1 := by omega
          rw [hj1, hfi1] <;> norm_num
        · have h41 : f i < 2 ^ (Nat.log 2 (f i) + 1) :=
            Nat.lt_pow_succ_log_self (by norm_num) (f i)
          rw [h_log] at h41; exact h41
      have h5 : 2 ^ j = 2 * M := by
        cases j with | zero => omega | succ j' => simp [M, pow_succ] <;> ring
      exact ⟨h1, by rw [h5] at h4; exact h4⟩
    exact ⟨M, s', Finset.filter_subset _ _, h_range, h_sum_real⟩

/-- Point-fiber uniformization: select coarse squares with uniform fiber sizes.

    Returns uniform fibers, Q0 density bound (with M factor), and P₀ retention. -/
lemma point_fiber_uniformization
    {n m : ℕ} (hnm : m ≤ n)
    {P₀ : Finset (DyadicSquare n)}
    {Q0 : Finset (DyadicSquare m)}
    (hQ0_eq : Q0 = P₀.image (containingSquare hnm))
    (h_pos : ∀ Q ∈ Q0, 0 < (P₀.filter (fun p => squareContained hnm p Q)).card)
    (N_max : ℕ) (hN_max : ∀ Q ∈ Q0, (P₀.filter (fun p => squareContained hnm p Q)).card ≤ N_max) :
    ∃ (M : ℕ) (Q0' : Finset (DyadicSquare m))
      (P₀' : Finset (DyadicSquare n)),
      Q0' ⊆ Q0 ∧
      P₀' = P₀.filter (fun p => containingSquare hnm p ∈ Q0') ∧
      P₀' ⊆ P₀ ∧
      (∀ Q ∈ Q0', M ≤ (P₀'.filter (fun p => squareContained hnm p Q)).card ∧
                        (P₀'.filter (fun p => squareContained hnm p Q)).card < 2 * M) ∧
      (Q0.card : ℝ) ≤ (2 * (M : ℝ) * (numDyadicLevels N_max : ℝ)) * (Q0'.card : ℝ) ∧
      (P₀'.card : ℝ) ≥ (P₀.card : ℝ) / (numDyadicLevels N_max : ℝ) := by
  let fiberSize (Q : DyadicSquare m) : ℕ :=
    (P₀.filter (fun p => squareContained hnm p Q)).card

  have h_sum_fibers : ∑ Q ∈ Q0, fiberSize Q = P₀.card := by
    have h_mapsTo : (P₀ : Set (DyadicSquare n)).MapsTo
        (containingSquare hnm) (Q0 : Set (DyadicSquare m)) := by
      rw [hQ0_eq]
      intro p hp
      exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
    have h := Finset.card_eq_sum_card_fiberwise h_mapsTo
    have h_eq1 : ∀ q ∈ Q0,
        (P₀.filter (fun p => containingSquare hnm p = q)).card = fiberSize q := by
      intro q _
      have h_filter_eq : P₀.filter (fun p => containingSquare hnm p = q) =
          P₀.filter (fun p => squareContained hnm p q) := by
        ext p
        simp only [Finset.mem_filter]
        <;> rw [containingSquare_iff hnm p q]
      rw [h_filter_eq]
    have h_sum : ∑ Q ∈ Q0, fiberSize Q = ∑ Q ∈ Q0,
        (P₀.filter (fun p => containingSquare hnm p = Q)).card := by
      apply Finset.sum_congr rfl
      intro Q hQ
      exact (h_eq1 Q hQ).symm
    rw [h_sum]
    exact_mod_cast h.symm

  by_cases hQ0_empty : Q0 = ∅
  · -- Empty case
    have hP0_empty : P₀ = ∅ := by
      rw [hQ0_eq] at hQ0_empty
      simpa using hQ0_empty
    exact ⟨1, ∅, ∅, by simp, by simp, by simp, by simp,
      by rw [hQ0_empty] <;> simp,
      by rw [hP0_empty] <;> simp⟩
  · -- Nonempty case
    have hQ0_nonempty : Q0.Nonempty := Finset.nonempty_iff_ne_empty.mpr hQ0_empty

    have hN_max_pos : 0 < N_max := by
      rcases hQ0_nonempty with ⟨Q, hQ⟩
      have h1 : 0 < fiberSize Q := h_pos Q hQ
      have h2 : fiberSize Q ≤ N_max := hN_max Q hQ
      exact lt_of_lt_of_le h1 h2

    rcases exists_dyadic_sum_subfamily Q0 fiberSize hN_max_pos hN_max h_pos
      with ⟨M, Q0', hQ0'_sub, h_band, h_sum⟩

    let P₀' : Finset (DyadicSquare n) :=
      P₀.filter (fun p => containingSquare hnm p ∈ Q0')

    have hP0'_sub : P₀' ⊆ P₀ := Finset.filter_subset _ _

    have h_fiber_eq : ∀ Q ∈ Q0',
        (P₀'.filter (fun p => squareContained hnm p Q)).card = fiberSize Q := by
      intro Q hQ
      have h_eq : P₀'.filter (fun p => squareContained hnm p Q) =
          P₀.filter (fun p => squareContained hnm p Q) := by
        ext p
        simp only [P₀', Finset.mem_filter]
        constructor
        · rintro ⟨⟨hp, _⟩, hsq⟩
          exact ⟨hp, hsq⟩
        · rintro ⟨hp, hsq⟩
          have h_cont : containingSquare hnm p = Q :=
            (containingSquare_iff hnm p Q).mpr hsq
          exact ⟨⟨hp, h_cont ▸ hQ⟩, hsq⟩
      rw [h_eq]

    have h_uniform : ∀ Q ∈ Q0', M ≤ (P₀'.filter (fun p => squareContained hnm p Q)).card ∧
        (P₀'.filter (fun p => squareContained hnm p Q)).card < 2 * M := by
      intro Q hQ
      have h1 : M ≤ fiberSize Q ∧ fiberSize Q < 2 * M := h_band Q hQ
      rw [h_fiber_eq Q hQ]
      exact h1

    have hP0'_card_eq : P₀'.card = ∑ Q ∈ Q0', fiberSize Q := by
      have h_mapsTo : (P₀' : Set (DyadicSquare n)).MapsTo
          (containingSquare hnm) (Q0' : Set (DyadicSquare m)) := by
        intro p hp
        exact (Finset.mem_filter.mp hp).2
      have h_card : P₀'.card = ∑ Q ∈ Q0',
          (P₀'.filter (fun p => containingSquare hnm p = Q)).card :=
        Finset.card_eq_sum_card_fiberwise h_mapsTo
      have h_eq1 : ∀ q ∈ Q0',
          (P₀'.filter (fun p => containingSquare hnm p = q)).card =
          (P₀'.filter (fun p => squareContained hnm p q)).card := by
        intro q _
        have h_filter_eq : P₀'.filter (fun p => containingSquare hnm p = q) =
            P₀'.filter (fun p => squareContained hnm p q) := by
          ext p
          simp only [Finset.mem_filter]
          <;> rw [containingSquare_iff hnm p q]
        rw [h_filter_eq]
      have h3 : ∑ Q ∈ Q0', (P₀'.filter (fun p => containingSquare hnm p = Q)).card =
          ∑ Q ∈ Q0', (P₀'.filter (fun p => squareContained hnm p Q)).card := by
        apply Finset.sum_congr rfl
        intro Q hQ
        exact h_eq1 Q hQ
      have h_sum2 : ∑ Q ∈ Q0', (P₀'.filter (fun p => squareContained hnm p Q)).card =
          ∑ Q ∈ Q0', fiberSize Q := by
        apply Finset.sum_congr rfl
        intro Q hQ
        rw [h_fiber_eq Q hQ]
      rw [h_card, h3, h_sum2]

    let L := numDyadicLevels N_max
    have hL_pos : 0 < L := by simp [L, numDyadicLevels] <;> omega

    have hP0'_card_eq_real : (P₀'.card : ℝ) = ∑ Q ∈ Q0', (fiberSize Q : ℝ) := by
      exact_mod_cast hP0'_card_eq
    have h_sum_fibers_real : (∑ Q ∈ Q0, (fiberSize Q : ℝ)) = (P₀.card : ℝ) := by
      exact_mod_cast h_sum_fibers

    have h_retention_real : (P₀'.card : ℝ) ≥ (P₀.card : ℝ) / (L : ℝ) := by
      rw [hP0'_card_eq_real]
      have h_sum' : ∑ Q ∈ Q0', (fiberSize Q : ℝ) ≥
          (∑ Q ∈ Q0, (fiberSize Q : ℝ)) / (L : ℝ) := h_sum
      rw [h_sum_fibers_real] at h_sum'
      exact h_sum'

    have h_sum_upper : (∑ Q ∈ Q0', (fiberSize Q : ℝ)) ≤ (2 * (M : ℝ)) * (Q0'.card : ℝ) := by
      have h : ∀ Q ∈ Q0', (fiberSize Q : ℝ) < 2 * (M : ℝ) := by
        intro Q hQ
        exact_mod_cast (h_band Q hQ).2
      calc (∑ Q ∈ Q0', (fiberSize Q : ℝ))
        ≤ ∑ Q ∈ Q0', (2 * (M : ℝ)) := Finset.sum_le_sum (fun Q hQ => (h Q hQ).le)
        _ = (Q0'.card : ℝ) * (2 * (M : ℝ)) := by simp [Finset.sum_const] <;> ring
        _ = (2 * (M : ℝ)) * (Q0'.card : ℝ) := by ring

    have hQ0_le_P0 : (Q0.card : ℝ) ≤ (P₀.card : ℝ) := by
      have h1 : ∀ Q ∈ Q0, (1 : ℝ) ≤ (fiberSize Q : ℝ) := by
        intro Q hQ
        exact_mod_cast h_pos Q hQ
      have h2 : (Q0.card : ℝ) ≤ ∑ Q ∈ Q0, (fiberSize Q : ℝ) := by
        calc (Q0.card : ℝ)
          = ∑ Q ∈ Q0, (1 : ℝ) := by simp
          _ ≤ ∑ Q ∈ Q0, (fiberSize Q : ℝ) := Finset.sum_le_sum h1
      rw [h_sum_fibers_real] at h2
      exact h2

    have hP0_le_Lsum : (P₀.card : ℝ) ≤ (L : ℝ) * (∑ Q ∈ Q0', (fiberSize Q : ℝ)) := by
      have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL_pos
      have h' : (P₀'.card : ℝ) ≥ (P₀.card : ℝ) / (L : ℝ) := h_retention_real
      calc (P₀.card : ℝ)
        = (L : ℝ) * ((P₀.card : ℝ) / (L : ℝ)) := by field_simp [hLpos.ne'] <;> ring
        _ ≤ (L : ℝ) * (P₀'.card : ℝ) := by gcongr
        _ = (L : ℝ) * (∑ Q ∈ Q0', (fiberSize Q : ℝ)) := by rw [hP0'_card_eq_real]

    have hQ0_density : (Q0.card : ℝ) ≤ (2 * (M : ℝ) * (L : ℝ)) * (Q0'.card : ℝ) := by
      calc (Q0.card : ℝ)
        ≤ (P₀.card : ℝ) := hQ0_le_P0
        _ ≤ (L : ℝ) * (∑ Q ∈ Q0', (fiberSize Q : ℝ)) := hP0_le_Lsum
        _ ≤ (L : ℝ) * ((2 * (M : ℝ)) * (Q0'.card : ℝ)) := by gcongr
        _ = (2 * (M : ℝ) * (L : ℝ)) * (Q0'.card : ℝ) := by ring

    exact ⟨M, Q0', P₀', hQ0'_sub, rfl, hP0'_sub, h_uniform, hQ0_density, h_retention_real⟩

/-- Bound numDyadicLevels N ≤ 2 * Real.log (N + 1) + 2 for polylog absorption. -/
lemma numDyadicLevels_le_polylog (N : ℕ) (hN : 0 < N) :
    (numDyadicLevels N : ℝ) ≤ 2 * Real.log (N + 1) + 2 := by
  have hN' : N ≠ 0 := by linarith
  have h_log2_ge_half : Real.log 2 ≥ 1 / 2 := by
    have h1 : Real.exp (1 / 2 : ℝ) < 2 := by
      have h2 : Real.exp 1 < (2.7182818286 : ℝ) := Real.exp_one_lt_d9
      have h3 : Real.exp (1 / 2 : ℝ) * Real.exp (1 / 2 : ℝ) = Real.exp 1 := by
        rw [← Real.exp_add] <;> ring_nf
      have h4 : (Real.exp (1 / 2 : ℝ)) ^ 2 = Real.exp 1 := by
        simpa [pow_two] using h3
      nlinarith [Real.exp_pos (1 / 2 : ℝ)]
    have h4 : Real.exp (1 / 2 : ℝ) ≤ 2 := by linarith
    have h5 : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have h_pos1 : 0 < (2 : ℝ) := by norm_num
      have h_log : Real.log (Real.exp (1 / 2 : ℝ)) ≤ Real.log 2 := Real.log_le_log (by positivity) h4
      have h_eq : Real.log (Real.exp (1 / 2 : ℝ)) = (1 / 2 : ℝ) := by
        rw [Real.log_exp]
      rw [h_eq] at h_log
      exact h_log
    exact h5
  have h1 : (Nat.log 2 N : ℝ) ≤ Real.log (N : ℝ) / Real.log 2 := by
    have h2 : (2 : ℝ) ^ (Nat.log 2 N) ≤ (N : ℝ) := by
      exact_mod_cast Nat.pow_log_le_self 2 hN'
    have h3 : Real.log ((2 : ℝ) ^ (Nat.log 2 N)) ≤ Real.log (N : ℝ) :=
      Real.log_le_log (by positivity) h2
    have h4 : Real.log ((2 : ℝ) ^ (Nat.log 2 N)) = (Nat.log 2 N : ℝ) * Real.log 2 := by
      rw [Real.log_pow] <;> norm_cast
    rw [h4] at h3
    have h5 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    calc (Nat.log 2 N : ℝ)
      = ((Nat.log 2 N : ℝ) * Real.log 2) / Real.log 2 := by field_simp [h5.ne'] <;> ring
      _ ≤ Real.log (N : ℝ) / Real.log 2 := by gcongr
  have h_logN1_nonneg : 0 ≤ Real.log ((N : ℝ) + 1) := by
    have h : (N : ℝ) + 1 ≥ 1 := by linarith
    exact Real.log_nonneg h
  have h_inv_log2_le_2 : (1 : ℝ) / Real.log 2 ≤ 2 := by
    have h5 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h6 : (1 : ℝ) ≤ 2 * Real.log 2 := by linarith [h_log2_ge_half]
    calc (1 : ℝ) / Real.log 2
      ≤ (2 * Real.log 2) / Real.log 2 := by gcongr
      _ = 2 := by field_simp [h5.ne'] <;> ring
  have h6 : Real.log (N : ℝ) / Real.log 2 ≤ 2 * Real.log ((N : ℝ) + 1) := by
    have h7 : Real.log (N : ℝ) ≤ Real.log ((N : ℝ) + 1) :=
      Real.log_le_log (by positivity) (by linarith)
    calc Real.log (N : ℝ) / Real.log 2
      = (1 / Real.log 2) * Real.log (N : ℝ) := by ring
      _ ≤ (1 / Real.log 2) * Real.log ((N : ℝ) + 1) := by gcongr
      _ ≤ 2 * Real.log ((N : ℝ) + 1) := by
        exact mul_le_mul_of_nonneg_right h_inv_log2_le_2 h_logN1_nonneg
  have h8 : (Nat.log 2 N : ℝ) ≤ 2 * Real.log ((N : ℝ) + 1) := by
    calc (Nat.log 2 N : ℝ)
      ≤ Real.log (N : ℝ) / Real.log 2 := h1
      _ ≤ 2 * Real.log ((N : ℝ) + 1) := h6
  have h_main : (numDyadicLevels N : ℝ) = (Nat.log 2 N : ℝ) + 2 := by
    simp [numDyadicLevels] <;> norm_cast
  rw [h_main]
  linarith [h8]

end DiscretisedFurstenbergEstimate.CombiningTheoremRework

end
