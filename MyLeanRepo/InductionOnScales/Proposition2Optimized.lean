module

public import MyLeanRepo.InductionOnScales.Pigeonhole
public import MyLeanRepo.InductionOnScales.Prop2_Step12
public import MyLeanRepo.InductionOnScales.SSetVerificationWeighted
public import MyLeanRepo.InductionOnScales.ExtraBasic
public import MyLeanRepo.InductionOnScales.Definitions
public import MyLeanRepo.OSWPrelude

@[expose] public section

/-!
# Proposition 2 (Optimized): Thick Tube Cover

Exponent-2 version using per-point dyadic bands + weighted popularity pigeonhole.

K = 32 * (log M + 2) * (log(|P|*M) + 2)
-/

open scoped BigOperators

attribute [local instance] Classical.propDecidable

namespace InductionOnScales

noncomputable section

variable {n m : ℕ} (hnm : m ≤ n)

/-- Coarse ancestor. -/
abbrev coarseAnc (T : DyadicTube n) : DyadicTube m :=
  deprecatedCoordinatewiseAncestor hnm T

/-- Number of fine tubes from F whose coarse ancestor is U. -/
def countInCoarse (F : Finset (DyadicTube n)) (U : DyadicTube m) : ℕ :=
  (F.filter (fun T => coarseAnc hnm T = U)).card

/-- Per-point dyadic band selection. -/
lemma per_point_dyadic_band {n m : ℕ} (hnm : m ≤ n)
    (T : Finset (DyadicTube n)) (M : ℕ) (hM : 0 < M)
    (h_size : T.card = M) :
    ∃ (j : ℕ),
      (T.filter (fun t =>
        let c := countInCoarse hnm T (coarseAnc hnm t)
        2^j ≤ c ∧ c < 2^(j+1))).Nonempty ∧
      (T.filter (fun t =>
        let c := countInCoarse hnm T (coarseAnc hnm t)
        2^j ≤ c ∧ c < 2^(j+1))).card ≥ M / (Nat.log 2 M + 2) := by
  let w : DyadicTube n → ℕ := fun t =>
    countInCoarse hnm T (coarseAnc hnm t)
  have h_pos : ∀ t ∈ T, 0 < w t := by
    intro t ht
    have h1 : t ∈ T.filter (fun T' => coarseAnc hnm T' = coarseAnc hnm t) :=
      Finset.mem_filter.mpr ⟨ht, rfl⟩
    have h2 : 0 < (T.filter (fun T' => coarseAnc hnm T' = coarseAnc hnm t)).card :=
      Finset.card_pos.mpr ⟨t, h1⟩
    simpa [w, countInCoarse] using h2
  have h_bound : ∀ t ∈ T, w t ≤ M := by
    intro t ht
    have h : w t ≤ T.card := by
      simpa [w, countInCoarse] using Finset.card_filter_le _ _
    rw [h_size] at h
    exact h
  rcases uniformize_positive_by_dyadic_level T w hM h_bound h_pos with
    ⟨s', j0, h_sub, h_j1, _h_j2, h_range, h_card⟩
  let j := j0 - 1
  have h_j0_pos : 1 ≤ j0 := h_j1
  have h_j_eq : j0 = j + 1 := by omega
  let band : Finset (DyadicTube n) :=
    T.filter (fun t => 2^j ≤ w t ∧ w t < 2^(j+1))
  have h_sub_band : s' ⊆ band := by
    intro t ht
    have h_in_T : t ∈ T := h_sub ht
    have h_band : 2^(j0-1) ≤ w t ∧ w t < 2^j0 := h_range t ht
    have h1 : 2^j ≤ w t := by
      have h2 : j0 - 1 = j := by omega
      rw [h2] at h_band
      exact h_band.1
    have h3 : w t < 2^(j+1) := by
      have h4 : j0 = j + 1 := by omega
      rw [h4] at h_band
      exact h_band.2
    exact Finset.mem_filter.mpr ⟨h_in_T, ⟨h1, h3⟩⟩
  have h_card_band : s'.card ≤ band.card := Finset.card_le_card h_sub_band
  have h_final : M / (Nat.log 2 M + 2) ≤ band.card := by
    have h1 : M / (Nat.log 2 M + 2) = T.card / numDyadicLevels M := by
      rw [h_size] <;> rfl
    rw [h1]
    exact le_trans h_card h_card_band
  by_cases h_nonempty : band.Nonempty
  · refine ⟨j, ?_⟩
    simpa [band, w] using ⟨h_nonempty, h_final⟩
  · -- Band is empty, so M / (log M + 2) = 0. Pick the level of any tube.
    have hT_card_pos : 0 < T.card := by
      rw [h_size] <;> exact hM
    have hT_nonempty : T.Nonempty := Finset.card_pos.mp hT_card_pos
    rcases hT_nonempty with ⟨t, ht⟩
    let j' := Nat.log 2 (w t)
    have h_wt_pos : 0 < w t := h_pos t ht
    have h_j'_spec : 2^j' ≤ w t ∧ w t < 2^(j'+1) := by
      have h1 : 2 ^ Nat.log 2 (w t) ≤ w t := Nat.pow_log_le_self 2 h_wt_pos.ne'
      have h2 : w t < 2 ^ (Nat.log 2 (w t) + 1) := Nat.lt_pow_succ_log_self (by norm_num) (w t)
      exact ⟨h1, h2⟩
    let band' := T.filter (fun t' => 2^j' ≤ w t' ∧ w t' < 2^(j'+1))
    have h_t_in : t ∈ band' := by
      exact Finset.mem_filter.mpr ⟨ht, h_j'_spec⟩
    have h_band'_nonempty : band'.Nonempty := ⟨t, h_t_in⟩
    have h_final' : M / (Nat.log 2 M + 2) ≤ band'.card := by
      have h_empty : band = ∅ := by simpa [Finset.not_nonempty_iff_eq_empty] using h_nonempty
      have h_le : M / (Nat.log 2 M + 2) ≤ 0 := by
        have h : M / (Nat.log 2 M + 2) ≤ band.card := h_final
        rw [h_empty] at h
        simpa using h
      have h_div : M / (Nat.log 2 M + 2) = 0 := Nat.eq_zero_of_le_zero h_le
      rw [h_div]
      exact Nat.zero_le _
    refine ⟨j', ?_⟩
    simpa [band', w] using ⟨h_band'_nonempty, h_final'⟩

/-- Sum of counts over a set S of coarse ancestors equals the size of the
subset of fine tubes whose ancestors are in S. -/
lemma sum_countInCoarse_band {n m : ℕ} (hnm : m ≤ n)
    (T : Finset (DyadicTube n)) (S : Finset (DyadicTube m)) :
    ∑ U ∈ S, countInCoarse hnm T U = (T.filter (fun t => coarseAnc hnm t ∈ S)).card := by
  let fiber (U : DyadicTube m) := T.filter (fun T' => coarseAnc hnm T' = U)
  have h_disj : (S : Set (DyadicTube m)).PairwiseDisjoint fiber := by
    intro U _ V _ hne
    have h : Disjoint (fiber U) (fiber V) := by
      rw [Finset.disjoint_left]
      intro T hT1 hT2
      have h1 : coarseAnc hnm T = U := (Finset.mem_filter.mp hT1).2
      have h2 : coarseAnc hnm T = V := (Finset.mem_filter.mp hT2).2
      exact hne (h1.symm.trans h2)
    exact h
  have h_union : S.biUnion fiber = T.filter (fun t => coarseAnc hnm t ∈ S) := by
    ext t
    simp only [Finset.mem_biUnion, fiber, Finset.mem_filter]
    <;> aesop
  calc ∑ U ∈ S, (fiber U).card
    = (S.biUnion fiber).card := by rw [Finset.card_biUnion h_disj]
  _ = (T.filter (fun t => coarseAnc hnm t ∈ S)).card := by rw [h_union]

/-- Helper: if `a ≥ b > 0`, then `↑(a / b) > a / (2 * b)` in reals. -/
lemma div_half_lt {a b : ℕ} (hb_pos : 0 < b) (h : a ≥ b) :
    (a : ℝ) / (2 * (b : ℝ)) < ↑(a / b) := by
  have h1 : a / b ≥ 1 := by
    apply Nat.one_le_div_iff hb_pos |>.mpr
    exact h
  have h2 : a < (a / b + 1) * b := by
    have h3 : b * (a / b) + a % b = a := Nat.div_add_mod a b
    have h4 : a % b < b := Nat.mod_lt a hb_pos
    nlinarith
  have h5 : (a / b + 1) * b ≤ 2 * (a / b) * b := by
    have h6 : a / b ≥ 1 := h1
    nlinarith
  have h7 : (a : ℝ) < 2 * ↑(a / b) * (b : ℝ) := by exact_mod_cast lt_of_lt_of_le h2 h5
  have h8 : 0 < (2 * (b : ℝ)) := by positivity
  have h9 : (a : ℝ) / (2 * (b : ℝ)) < ↑(a / b) := by
    calc (a : ℝ) / (2 * (b : ℝ))
      < (2 * ↑(a / b) * (b : ℝ)) / (2 * (b : ℝ)) := by gcongr
    _ = ↑(a / b) := by
      field_simp [h8.ne'] <;> ring
  exact h9

/-- Helper: `a < (a / b + 1) * b` for positive `b`. -/
lemma div_add_one_mul_lt (a b : ℕ) (hb_pos : 0 < b) : a < (a / b + 1) * b := by
  have h1 : a % b < b := Nat.mod_lt a hb_pos
  have h2 : a = (a / b) * b + a % b := by
    have h3 := Nat.div_add_mod a b
    have h4 : b * (a / b) + a % b = a := h3
    have h5 : b * (a / b) = (a / b) * b := by ring
    rw [h5] at h4
    exact h4.symm
  have h6 : (a / b) * b + b = (a / b + 1) * b := by ring
  calc a
    = (a / b) * b + a % b := h2
  _ < (a / b) * b + b := by
    have h7 : a % b < b := h1
    linarith
  _ = (a / b + 1) * b := h6

/-- Final step for h_card_upper: `P_card * M ≤ K * M * P_card` when `1 ≤ K`. -/
lemma card_upper_final_step (K : ℝ) (hK : 1 ≤ K) (M P_card : ℕ) :
    (P_card : ℝ) * (M : ℝ) ≤ K * (M : ℝ) * (P_card : ℝ) := by
  have hM : 0 ≤ (M : ℝ) := by exact_mod_cast Nat.zero_le M
  have hP : 0 ≤ (P_card : ℝ) := by exact_mod_cast Nat.zero_le P_card
  calc (P_card : ℝ) * (M : ℝ)
    = 1 * ((P_card : ℝ) * (M : ℝ)) := by ring
  _ ≤ K * ((P_card : ℝ) * (M : ℝ)) := by
    exact mul_le_mul_of_nonneg_right hK (mul_nonneg hP hM)
  _ = K * (M : ℝ) * (P_card : ℝ) := by ring

/-- Helper for h_card_lower: from `L ≥ M*P_card/(K_sset*card)`, deduce `M*P_card ≤ 2*K_sset*L*card`. -/
lemma card_lower_helper (L K_sset card : ℝ) (M P_card : ℕ)
    (h_card_pos : 0 < card) (hK_sset_pos : 0 < K_sset)
    (h_relation : L ≥ (M : ℝ) * (P_card : ℝ) / (K_sset * card)) :
    (M : ℝ) * (P_card : ℝ) ≤ (2 * K_sset) * L * card := by
  have h5 : 0 < K_sset * card := mul_pos hK_sset_pos h_card_pos
  have h5' : 0 ≤ K_sset * card := by linarith
  have hM : 0 ≤ (M : ℝ) := by exact_mod_cast Nat.zero_le M
  have hP : 0 ≤ (P_card : ℝ) := by exact_mod_cast Nat.zero_le P_card
  have hMP : 0 ≤ (M : ℝ) * (P_card : ℝ) := mul_nonneg hM hP
  have h_step1 : L * (K_sset * card) ≥ ((M : ℝ) * (P_card : ℝ) / (K_sset * card)) * (K_sset * card) :=
    mul_le_mul_of_nonneg_right h_relation h5'
  have h_step2 : ((M : ℝ) * (P_card : ℝ) / (K_sset * card)) * (K_sset * card) = (M : ℝ) * (P_card : ℝ) := by
    field_simp [h5.ne'] <;> ring
  have h4 : L * (K_sset * card) ≥ (M : ℝ) * (P_card : ℝ) := by
    rw [h_step2] at h_step1
    exact h_step1
  have h6 : (2 * K_sset) * L * card = 2 * (L * (K_sset * card)) := by ring
  rw [h6]
  have h7 : 2 * (L * (K_sset * card)) ≥ (M : ℝ) * (P_card : ℝ) := by
    have h8 : 2 * (L * (K_sset * card)) ≥ 2 * ((M : ℝ) * (P_card : ℝ)) := by
      gcongr
    have h9 : 2 * ((M : ℝ) * (P_card : ℝ)) ≥ (M : ℝ) * (P_card : ℝ) := by
      linarith
    linarith
  exact h7

/-- Simple helper: `P_card ≤ K * P_card` when `1 ≤ K`. -/
lemma P_card_le_K_helper (K : ℝ) (hK : 1 ≤ K) (P_card : ℕ) :
    (P_card : ℝ) ≤ K * (P_card : ℝ) := by
  have hP : 0 ≤ (P_card : ℝ) := by exact_mod_cast Nat.zero_le P_card
  calc (P_card : ℝ)
    = 1 * (P_card : ℝ) := by ring
  _ ≤ K * (P_card : ℝ) := by exact mul_le_mul_of_nonneg_right hK hP

/-- Helper for h_relation: proves `L * card ≥ M * P_card / (16 * k_real * numLevels)`. -/
lemma relation_helper_weighted
    (total_wpop numLevels L card M P_card : ℕ)
    (k_real : ℝ)
    (h_numLevels_pos : 0 < numLevels)
    (h_card_pos : 0 < card)
    (hL_pos : 0 < L)
    (h_total_lower : (total_wpop : ℝ) ≥ (P_card : ℝ) * (M : ℝ) / (4 * k_real))
    (h_k_pos : 0 < k_real)
    (h_div_lt : (total_wpop / numLevels : ℕ) < 2 * L * card) :
    (L : ℝ) * (card : ℝ) ≥ (M : ℝ) * (P_card : ℝ) / (16 * k_real * (numLevels : ℝ)) := by
  have h4 : ((total_wpop / numLevels : ℕ) : ℝ) < 2 * (L : ℝ) * (card : ℝ) := by exact_mod_cast h_div_lt
  have h5 : (L : ℝ) * (card : ℝ) > ((total_wpop / numLevels : ℕ) : ℝ) / 2 := by linarith
  by_cases h_case : total_wpop ≥ numLevels
  · -- Case 1: total_wpop ≥ numLevels
    have h6 : ((total_wpop / numLevels : ℕ) : ℝ) > (total_wpop : ℝ) / (2 * (numLevels : ℝ)) :=
      div_half_lt h_numLevels_pos h_case
    have h7 : (L : ℝ) * (card : ℝ) > (total_wpop : ℝ) / (4 * (numLevels : ℝ)) := by
      calc (L : ℝ) * (card : ℝ)
        > ((total_wpop / numLevels : ℕ) : ℝ) / 2 := h5
      _ > ((total_wpop : ℝ) / (2 * (numLevels : ℝ))) / 2 := by gcongr
      _ = (total_wpop : ℝ) / (4 * (numLevels : ℝ)) := by ring
    have h8 : (total_wpop : ℝ) ≥ (P_card : ℝ) * (M : ℝ) / (4 * k_real) := h_total_lower
    have h9 : (L : ℝ) * (card : ℝ) > (M : ℝ) * (P_card : ℝ) / (16 * k_real * (numLevels : ℝ)) := by
      calc (L : ℝ) * (card : ℝ)
        > (total_wpop : ℝ) / (4 * (numLevels : ℝ)) := h7
      _ ≥ ((P_card : ℝ) * (M : ℝ) / (4 * k_real)) / (4 * (numLevels : ℝ)) := by gcongr
      _ = (M : ℝ) * (P_card : ℝ) / (16 * k_real * (numLevels : ℝ)) := by ring
    exact le_of_lt h9
  · -- Case 2: total_wpop < numLevels
    have h_case' : total_wpop < numLevels := by omega
    have h_pos4 : 0 < 4 * k_real := by positivity
    have h11 : (P_card : ℝ) * (M : ℝ) / (4 * k_real) ≤ (total_wpop : ℝ) := h_total_lower
    have h12 : (total_wpop : ℝ) < (numLevels : ℝ) := by exact_mod_cast h_case'
    have h13 : (P_card : ℝ) * (M : ℝ) / (4 * k_real) < (numLevels : ℝ) := by linarith
    have h10 : (P_card : ℝ) * (M : ℝ) < 4 * k_real * (numLevels : ℝ) := by
      have h14 : ((P_card : ℝ) * (M : ℝ) / (4 * k_real)) * (4 * k_real) = (P_card : ℝ) * (M : ℝ) := by
        field_simp [h_pos4.ne'] <;> ring
      have h15 : ((P_card : ℝ) * (M : ℝ) / (4 * k_real)) * (4 * k_real) < (numLevels : ℝ) * (4 * k_real) := by
        gcongr
      rw [h14] at h15
      linarith
    have h16 : (M : ℝ) * (P_card : ℝ) < 16 * k_real * (numLevels : ℝ) := by
      calc (M : ℝ) * (P_card : ℝ)
        = (P_card : ℝ) * (M : ℝ) := by ring
      _ < 4 * k_real * (numLevels : ℝ) := h10
      _ ≤ 16 * k_real * (numLevels : ℝ) := by
        have h17 : 0 < k_real * (numLevels : ℝ) := by positivity
        nlinarith
    have h18 : 0 < 16 * k_real * (numLevels : ℝ) := by positivity
    have h19 : (M : ℝ) * (P_card : ℝ) / (16 * k_real * (numLevels : ℝ)) < 1 := by
      exact (div_lt_one h18).mpr h16
    have h20 : (1 : ℝ) ≤ (L : ℝ) * (card : ℝ) := by
      have h21 : 1 ≤ L := by exact_mod_cast hL_pos
      have h22 : 1 ≤ card := by exact_mod_cast h_card_pos
      exact_mod_cast mul_le_mul h21 h22 (by positivity) (by positivity)
    linarith

/-- Final algebra step for h_relation: from `L * card ≥ X / Y`, deduce `L ≥ X / (Y * card)`. -/
lemma final_relation_step (L card X Y : ℝ) (h_card_pos : 0 < card) (hY_pos : 0 < Y)
    (h_main : L * card ≥ X / Y) : L ≥ X / (Y * card) := by
  have h1 : L * card * Y ≥ X := by
    calc L * card * Y
      = (L * card) * Y := by ring
    _ ≥ (X / Y) * Y := by gcongr
    _ = X := by
      field_simp [hY_pos.ne'] <;> ring
  have h2 : 0 < Y * card := mul_pos hY_pos h_card_pos
  have h3 : L * (Y * card) ≥ X := by
    have h4 : L * (Y * card) = L * card * Y := by ring
    rw [h4]
    exact h1
  calc L
    = (L * (Y * card)) / (Y * card) := by field_simp [h2.ne'] <;> ring
  _ ≥ X / (Y * card) := by
    exact div_le_div_of_nonneg_right h3 (by positivity)

/-- OS Proposition 2 (optimized, exponent 2). -/
theorem proposition2_optimized
    (s : ℝ) (hs : 0 ≤ s) (hs_one : s ≤ 1)
    (C₁ : ℝ) (hC₁ : 1 ≤ C₁)
    (M : ℕ) (hM : 0 < M)
    (P : Finset (DyadicSquare n))
    (tubeFamily : (p : DyadicSquare n) → p ∈ P → Finset (DyadicTube n))
    (h_sset : ∀ p hp, IsFiniteTubeSSet s C₁ (tubeFamily p hp))
    (h_size : ∀ p hp, (tubeFamily p hp).card = M)
    (h_incidence : ∀ p hp T, T ∈ tubeFamily p hp →
      (T.toSet ∩ p.toSet).Nonempty)
    (h_tube_params : ∀ p hp T, T ∈ tubeFamily p hp →
      T.IsInAllowedParameterStrip)
    (h_bounded : ∀ p ∈ P, p.toSet ⊆ unitSquare)
    (hP_nonempty : P.Nonempty) :
    ∃ (K : ℝ) (hK : 1 ≤ K)
      (P' : Finset (DyadicSquare n)) (hP' : P' ⊆ P)
      (coarseTubes : Finset (DyadicTube m))
      (C₂ : ℝ) (hC₂ : 1 ≤ C₂)
      (H : ℝ) (hH : 1 ≤ H),
      let tfOpt : DyadicSquare n → Finset (DyadicTube n) :=
        fun p => if hp : p ∈ P then tubeFamily p hp else ∅;
      P'.Nonempty ∧
      (P.card : ℝ) ≤ K * (P'.card : ℝ) ∧
      IsFiniteTubeSSet s C₂ coarseTubes ∧
      C₂ ≤ K * C₁ ∧
      H * (coarseTubes.card : ℝ) ≤ K * (M : ℝ) * (P'.card : ℝ) ∧
      (M : ℝ) * (P'.card : ℝ) ≤ K * H * (coarseTubes.card : ℝ) ∧
      (∀ U ∈ coarseTubes,
        H ≤ ∑ p ∈ P', (countInCoarse hnm (tfOpt p) U : ℝ)) := by
  -- Definitions
  let tfOpt : DyadicSquare n → Finset (DyadicTube n) :=
    fun p => if hp : p ∈ P then tubeFamily p hp else ∅
  have h_tfOpt : ∀ p hp, tfOpt p = tubeFamily p hp := by
    intro p hp
    simp [tfOpt, hp]

  -- Step 1: For each p, select a dyadic band
  choose j hj using fun (p : DyadicSquare n) (hp : p ∈ P) =>
    per_point_dyadic_band hnm (tubeFamily p hp) M hM (h_size p hp)

  let m₁ : DyadicSquare n → ℕ := fun p =>
    if hp : p ∈ P then 2^(j p hp) else 1
  let bandTubes : DyadicSquare n → Finset (DyadicTube n) := fun p =>
    if hp : p ∈ P then
      (tubeFamily p hp).filter (fun t =>
        let c := countInCoarse hnm (tubeFamily p hp) (coarseAnc hnm t)
        2^(j p hp) ≤ c ∧ c < 2^(j p hp + 1))
    else ∅
  let coarseFamily : DyadicSquare n → Finset (DyadicTube m) := fun p =>
    (bandTubes p).image (coarseAnc hnm)

  have h_band_eq : ∀ p hp, bandTubes p = (tubeFamily p hp).filter (fun t =>
      let c := countInCoarse hnm (tubeFamily p hp) (coarseAnc hnm t)
      2^(j p hp) ≤ c ∧ c < 2^(j p hp + 1)) := by
    intro p hp
    simp [bandTubes, hp]

  have h_m1_eq : ∀ p hp, m₁ p = 2^(j p hp) := by
    intro p hp
    simp [m₁, hp]

  have h_band_union : ∀ p hp,
      (tubeFamily p hp).filter (fun t => coarseAnc hnm t ∈ coarseFamily p) = bandTubes p := by
    intro p hp
    have h_band_def : bandTubes p = (tubeFamily p hp).filter (fun t =>
        let c := countInCoarse hnm (tubeFamily p hp) (coarseAnc hnm t)
        2^(j p hp) ≤ c ∧ c < 2^(j p hp + 1)) := h_band_eq p hp
    apply Finset.ext
    intro t
    have h_iff1 : t ∈ (tubeFamily p hp).filter (fun t => coarseAnc hnm t ∈ coarseFamily p) ↔
        t ∈ tubeFamily p hp ∧ coarseAnc hnm t ∈ coarseFamily p := by
      rw [Finset.mem_filter]
    have h_iff2 : t ∈ bandTubes p ↔
        t ∈ tubeFamily p hp ∧ (let c := countInCoarse hnm (tubeFamily p hp) (coarseAnc hnm t)
          2^(j p hp) ≤ c ∧ c < 2^(j p hp + 1)) := by
      rw [h_band_def, Finset.mem_filter]
    rw [h_iff1, h_iff2]
    constructor
    · rintro ⟨h_t_in_T, h_in_image⟩
      rcases Finset.mem_image.mp h_in_image with ⟨t', ht'_in_band, h_eq⟩
      have h_band_def' := h_band_def
      rw [h_band_def'] at ht'_in_band
      have h_t'_in_T : t' ∈ tubeFamily p hp := (Finset.mem_filter.mp ht'_in_band).1
      have h_cond' := (Finset.mem_filter.mp ht'_in_band).2
      have h_same : coarseAnc hnm t = coarseAnc hnm t' := h_eq.symm
      have h_cond : (let c := countInCoarse hnm (tubeFamily p hp) (coarseAnc hnm t)
          2^(j p hp) ≤ c ∧ c < 2^(j p hp + 1)) := by
        rw [h_same] <;> exact h_cond'
      exact ⟨h_t_in_T, h_cond⟩
    · rintro ⟨h_t_in_T, h_cond⟩
      have h_t_in_band : t ∈ bandTubes p := by
        rw [h_band_def]
        exact Finset.mem_filter.mpr ⟨h_t_in_T, h_cond⟩
      have h_in_image : coarseAnc hnm t ∈ coarseFamily p :=
        Finset.mem_image.mpr ⟨t, h_t_in_band, rfl⟩
      exact ⟨h_t_in_T, h_in_image⟩

  have h_mult : ∀ p hp, ∀ U ∈ coarseFamily p,
      m₁ p ≤ countInCoarse hnm (tubeFamily p hp) U ∧
      countInCoarse hnm (tubeFamily p hp) U < 2 * m₁ p := by
    intro p hp U hU
    rcases Finset.mem_image.mp hU with ⟨t, ht, rfl⟩
    have h_band_def : bandTubes p = (tubeFamily p hp).filter (fun t =>
        let c := countInCoarse hnm (tubeFamily p hp) (coarseAnc hnm t)
        2^(j p hp) ≤ c ∧ c < 2^(j p hp + 1)) := h_band_eq p hp
    rw [h_band_def] at ht
    have h5 : (let c := countInCoarse hnm (tubeFamily p hp) (coarseAnc hnm t)
        2^(j p hp) ≤ c ∧ c < 2^(j p hp + 1)) := (Finset.mem_filter.mp ht).2
    have h_m1 : m₁ p = 2^(j p hp) := h_m1_eq p hp
    rw [h_m1]
    have h6 : countInCoarse hnm (tubeFamily p hp) (coarseAnc hnm t) < 2 * 2^(j p hp) := by
      have h7 : 2^(j p hp + 1) = 2 * 2^(j p hp) := by simp [pow_succ] <;> ring
      rw [h7] at h5
      exact h5.2
    exact ⟨h5.1, h6⟩

  have h_band_size : ∀ (p : DyadicSquare n) (hp : p ∈ P), (bandTubes p).card ≥ M / (Nat.log 2 M + 2) := by
    intro p hp
    have h1 : bandTubes p = (tubeFamily p hp).filter (fun t =>
        let c := countInCoarse hnm (tubeFamily p hp) (coarseAnc hnm t)
        2^(j p hp) ≤ c ∧ c < 2^(j p hp + 1)) := by
      simp [bandTubes, hp]
    rw [h1]
    exact (hj p hp).2

  have h_band_nonempty : ∀ (p : DyadicSquare n) (hp : p ∈ P), (bandTubes p).Nonempty := by
    intro p hp
    have h1 : bandTubes p = (tubeFamily p hp).filter (fun t =>
        let c := countInCoarse hnm (tubeFamily p hp) (coarseAnc hnm t)
        2^(j p hp) ≤ c ∧ c < 2^(j p hp + 1)) := by
      simp [bandTubes, hp]
    rw [h1]
    exact (hj p hp).1

  have h_m1_pos : ∀ (p : DyadicSquare n) (hp : p ∈ P), 0 < m₁ p := by
    intro p hp
    have h_eq : m₁ p = 2^(j p hp) := by
      simp [m₁, hp]
    rw [h_eq]
    positivity

  have h_m1_le_M : ∀ (p : DyadicSquare n) (hp : p ∈ P), m₁ p ≤ M := by
    intro p hp
    have h_nonempty : (bandTubes p).Nonempty := h_band_nonempty p hp
    rcases h_nonempty with ⟨t, ht⟩
    have h_band_def : bandTubes p = (tubeFamily p hp).filter (fun t =>
        let c := countInCoarse hnm (tubeFamily p hp) (coarseAnc hnm t)
        2^(j p hp) ≤ c ∧ c < 2^(j p hp + 1)) := h_band_eq p hp
    rw [h_band_def] at ht
    have h2 : 2^(j p hp) ≤ countInCoarse hnm (tubeFamily p hp) (coarseAnc hnm t) :=
      (Finset.mem_filter.mp ht).2.1
    have h3 : countInCoarse hnm (tubeFamily p hp) (coarseAnc hnm t) ≤ M := by
      have h4 : countInCoarse hnm (tubeFamily p hp) (coarseAnc hnm t) ≤ (tubeFamily p hp).card :=
        by simpa [countInCoarse] using Finset.card_filter_le _ _
      rw [h_size p hp] at h4
      exact h4
    have h_m1 : m₁ p = 2^(j p hp) := h_m1_eq p hp
    rw [h_m1]
    exact le_trans h2 h3

  -- Step 2: Define all coarse tubes and weighted popularity
  let TΔ_all : Finset (DyadicTube m) :=
    P.biUnion coarseFamily
  let wpop : DyadicTube m → ℕ := fun U =>
    ∑ p ∈ P.filter (fun p => U ∈ coarseFamily p), m₁ p

  have h_wpop_pos : ∀ U ∈ TΔ_all, 0 < wpop U := by
    intro U hU
    rcases Finset.mem_biUnion.mp hU with ⟨p, hp, hU_coarse⟩
    have h1 : U ∈ coarseFamily p := hU_coarse
    have h2 : p ∈ P.filter (fun p => U ∈ coarseFamily p) :=
      Finset.mem_filter.mpr ⟨hp, h1⟩
    have h3 : 0 < m₁ p := h_m1_pos p hp
    have h4 : m₁ p ≤ wpop U := Finset.single_le_sum (fun i _ => Nat.zero_le _) h2
    exact lt_of_lt_of_le h3 h4

  have h_wpop_bound : ∀ U ∈ TΔ_all, wpop U ≤ P.card * M := by
    intro U _
    have h1 : wpop U ≤ ∑ p ∈ P, m₁ p := by
      apply Finset.sum_le_sum_of_subset
      exact Finset.filter_subset _ _
    have h2 : ∑ p ∈ P, m₁ p ≤ ∑ p ∈ P, M := by
      apply Finset.sum_le_sum
      intro p hp
      exact h_m1_le_M p hp
    have h3 : ∑ p ∈ P, M = P.card * M := by
      simp [Finset.sum_const] <;> ring
    rw [h3] at h2
    exact le_trans h1 h2

  -- Total weighted popularity
  let total_wpop : ℕ := ∑ U ∈ TΔ_all, wpop U

  have h_swap : total_wpop = ∑ p ∈ P, m₁ p * (coarseFamily p).card := by
    dsimp only [total_wpop, wpop]
    have h1 : ∀ (U : DyadicTube m),
        ∑ p ∈ P.filter (fun p => U ∈ coarseFamily p), m₁ p =
        ∑ p ∈ P, (if U ∈ coarseFamily p then m₁ p else 0) := by
      intro U
      rw [Finset.sum_filter]
      <;> rfl
    have h2 : ∑ U ∈ TΔ_all, ∑ p ∈ P.filter (fun p => U ∈ coarseFamily p), m₁ p =
        ∑ U ∈ TΔ_all, ∑ p ∈ P, (if U ∈ coarseFamily p then m₁ p else 0) := by
      apply Finset.sum_congr rfl
      intro U _
      exact h1 U
    rw [h2]
    have h3 : ∑ U ∈ TΔ_all, ∑ p ∈ P, (if U ∈ coarseFamily p then m₁ p else 0) =
        ∑ p ∈ P, ∑ U ∈ TΔ_all, (if U ∈ coarseFamily p then m₁ p else 0) := by
      rw [Finset.sum_comm]
    rw [h3]
    apply Finset.sum_congr rfl
    intro p hp
    have h4 : ∑ U ∈ TΔ_all, (if U ∈ coarseFamily p then m₁ p else 0) =
        m₁ p * (coarseFamily p).card := by
      have h5 : coarseFamily p ⊆ TΔ_all := Finset.subset_biUnion_of_mem coarseFamily hp
      rw [Finset.sum_ite]
      <;> simp [h5, Finset.sum_const] <;> ring
    exact h4

  -- Lower bound on m₁(p) * |coarseFamily(p)|
  have h_per_point_lower : ∀ (p : DyadicSquare n) (hp : p ∈ P),
      (m₁ p : ℝ) * ((coarseFamily p).card : ℝ) ≥ (M : ℝ) / (4 * ((Nat.log 2 M : ℝ) + 2)) := by
    intro p hp
    set k : ℕ := Nat.log 2 M + 2 with hk_def
    have hk_pos : 0 < k := by positivity
    have h_coarse_nonempty : (coarseFamily p).Nonempty := by
      have h1 : (bandTubes p).Nonempty := h_band_nonempty p hp
      rcases h1 with ⟨t, ht⟩
      exact ⟨coarseAnc hnm t, Finset.mem_image.mpr ⟨t, ht, rfl⟩⟩
    have h_sum_mult : ∑ U ∈ coarseFamily p, countInCoarse hnm (tubeFamily p hp) U =
        (bandTubes p).card := by
      have h := sum_countInCoarse_band hnm (tubeFamily p hp) (coarseFamily p)
      rw [h_band_union p hp] at h
      exact h
    have h1 : ((bandTubes p).card : ℝ) = ∑ U ∈ coarseFamily p, (countInCoarse hnm (tubeFamily p hp) U : ℝ) := by
      norm_cast <;> exact h_sum_mult.symm
    have h2 : ∑ U ∈ coarseFamily p, (countInCoarse hnm (tubeFamily p hp) U : ℝ) < ∑ U ∈ coarseFamily p, (2 * (m₁ p : ℝ)) := by
      apply Finset.sum_lt_sum_of_nonempty h_coarse_nonempty
      intro U hU
      exact_mod_cast (h_mult p hp U hU).2
    have h3 : ∑ U ∈ coarseFamily p, (2 * (m₁ p : ℝ)) = 2 * (m₁ p : ℝ) * ((coarseFamily p).card : ℝ) := by
      simp [Finset.sum_const] <;> ring
    have h4 : ((bandTubes p).card : ℝ) < 2 * (m₁ p : ℝ) * ((coarseFamily p).card : ℝ) := by
      rw [h1]
      rw [h3] at h2
      exact h2
    have h5 : (m₁ p : ℝ) * ((coarseFamily p).card : ℝ) > ((bandTubes p).card : ℝ) / 2 := by linarith
    -- Show |bandTubes| ≥ M / (2 * k) in reals
    have h_band_ge : ((bandTubes p).card : ℝ) ≥ (M : ℝ) / (2 * (k : ℝ)) := by
      by_cases hM_small : (M : ℝ) < 2 * (k : ℝ)
      · -- M < 2k, so M / (2k) < 1, and |bandTubes| ≥ 1
        have h6 : (M : ℝ) / (2 * (k : ℝ)) < 1 := by
          have h7 : 0 < (2 * (k : ℝ)) := by positivity
          exact (div_lt_one h7).mpr hM_small
        have h8 : ((bandTubes p).card : ℝ) ≥ 1 := by
          exact_mod_cast (h_band_nonempty p hp).card_pos
        linarith
      · -- M ≥ 2k
        have hM_ge : (M : ℝ) ≥ 2 * (k : ℝ) := by linarith
        have h9 : ((bandTubes p).card : ℝ) ≥ ↑(M / k) := by
          exact_mod_cast h_band_size p hp
        have h10 : M ≥ 2 * k := by exact_mod_cast hM_ge
        have h10' : k ≤ M := by omega
        have h11 : M / k ≥ 1 := by
          apply Nat.one_le_div_iff (by positivity) |>.mpr
          exact h10'
        have h12 : M < (M / k + 1) * k := div_add_one_mul_lt M k hk_pos
        have h13 : (M : ℝ) < 2 * (↑(M / k) : ℝ) * (k : ℝ) := by
          have h14 : (M / k + 1) * k ≤ 2 * (M / k) * k := by
            have h15 : M / k ≥ 1 := h11
            nlinarith
          have h16 : M < (M / k + 1) * k := h12
          exact_mod_cast lt_of_lt_of_le h16 h14
        have h17 : (M : ℝ) / (2 * (k : ℝ)) < (↑(M / k) : ℝ) := by
          have h18 : 0 < (k : ℝ) := by positivity
          have h19 : 0 < (2 * (k : ℝ)) := by positivity
          calc (M : ℝ) / (2 * (k : ℝ))
            < (2 * (↑(M / k) : ℝ) * (k : ℝ)) / (2 * (k : ℝ)) := by gcongr
          _ = (↑(M / k) : ℝ) := by
            field_simp [h19.ne'] <;> ring
        linarith
    have h6 : (m₁ p : ℝ) * ((coarseFamily p).card : ℝ) > (M : ℝ) / (4 * (k : ℝ)) := by
      calc (m₁ p : ℝ) * ((coarseFamily p).card : ℝ)
        > ((bandTubes p).card : ℝ) / 2 := h5
      _ ≥ ((M : ℝ) / (2 * (k : ℝ))) / 2 := by gcongr
      _ = (M : ℝ) / (4 * (k : ℝ)) := by ring
    simpa [hk_def] using le_of_lt h6

  have h_total_lower : (total_wpop : ℝ) ≥
      (P.card : ℝ) * (M : ℝ) / (4 * ((Nat.log 2 M : ℝ) + 2)) := by
    have h_swap' : (total_wpop : ℝ) = ∑ p ∈ P, ((m₁ p : ℝ) * ((coarseFamily p).card : ℝ)) := by
      exact_mod_cast h_swap
    rw [h_swap']
    have h : ∑ p ∈ P, ((m₁ p : ℝ) * ((coarseFamily p).card : ℝ)) ≥
        ∑ p ∈ P, ((M : ℝ) / (4 * ((Nat.log 2 M : ℝ) + 2))) := by
      apply Finset.sum_le_sum
      intro p hp
      exact h_per_point_lower p hp
    have h2 : ∑ p ∈ P, ((M : ℝ) / (4 * ((Nat.log 2 M : ℝ) + 2))) =
        (P.card : ℝ) * (M : ℝ) / (4 * ((Nat.log 2 M : ℝ) + 2)) := by
      simp [Finset.sum_const] <;> ring
    rw [h2] at h
    exact h

  -- Step 3: Dyadic pigeonhole on weighted popularity
  let N : ℕ := P.card * M
  have hN_pos : 0 < N := by
    exact mul_pos hP_nonempty.card_pos hM

  rcases exists_dyadic_level_weighted TΔ_all wpop hN_pos h_wpop_bound with
    ⟨j_level_orig, hj_le, h_weight_orig⟩

  -- Ensure coarseTubes is nonempty: if the pigeonhole level is empty, pick U0's level.
  have hTΔ_all_nonempty : TΔ_all.Nonempty := by
    rcases hP_nonempty with ⟨p, hp⟩
    have h2 : (coarseFamily p).Nonempty := Finset.image_nonempty.mpr (h_band_nonempty p hp)
    exact Finset.Nonempty.mono (Finset.subset_biUnion_of_mem coarseFamily hp) h2

  rcases hTΔ_all_nonempty with ⟨U0, hU0⟩

  let coarseTubes_orig : Finset (DyadicTube m) :=
    TΔ_all.filter (fun U => dyadicLevel (wpop U) = j_level_orig)

  let j_level : ℕ :=
    if coarseTubes_orig.Nonempty then j_level_orig else dyadicLevel (wpop U0)

  have h_j_level_pos : 1 ≤ j_level := by
    by_cases h : coarseTubes_orig.Nonempty
    · have h_j : j_level = j_level_orig := by simp [j_level, h]
      rw [h_j]
      by_contra h'
      have h0 : j_level_orig = 0 := by omega
      have h_empty : coarseTubes_orig = ∅ := by
        have h11 : ∀ (x : DyadicTube m), x ∉ coarseTubes_orig := by
          intro x hU
          have h_pos : 0 < wpop x := h_wpop_pos x (Finset.mem_filter.mp hU).1
          have h_ne : wpop x ≠ 0 := by linarith
          have h9 : dyadicLevel (wpop x) ≠ 0 := by
            have h_pos2 : 0 < dyadicLevel (wpop x) := by
              simp [dyadicLevel, h_ne] <;> positivity
            exact ne_of_gt h_pos2
          have h10 : dyadicLevel (wpop x) = 0 := by
            have hU' : x ∈ TΔ_all.filter (fun U => dyadicLevel (wpop U) = j_level_orig) := hU
            have h11 : dyadicLevel (wpop x) = j_level_orig := (Finset.mem_filter.mp hU').2
            rw [h0] at h11
            exact h11
          exact h9 h10
        by_contra h12
        have h13 : coarseTubes_orig.Nonempty := Finset.nonempty_iff_ne_empty.mpr h12
        rcases h13 with ⟨x, hx⟩
        exact h11 x hx
      have h_contra : ¬ coarseTubes_orig.Nonempty := by
        rw [h_empty]
        simp
      exact h_contra h
    · have h_j : j_level = dyadicLevel (wpop U0) := by simp [j_level, h]
      rw [h_j]
      have h_pos : 0 < wpop U0 := h_wpop_pos U0 hU0
      have h_ne : wpop U0 ≠ 0 := by linarith
      have h_log : Nat.log 2 (wpop U0) + 1 = dyadicLevel (wpop U0) := by
        simp [dyadicLevel, h_ne]
      rw [←h_log]
      have h_nonneg : 0 ≤ Nat.log 2 (wpop U0) := Nat.zero_le _
      linarith

  let coarseTubes : Finset (DyadicTube m) :=
    TΔ_all.filter (fun U => dyadicLevel (wpop U) = j_level)
  let L : ℕ := 2^(j_level - 1)

  have hL_pos : 0 < L := by
    dsimp only [L]
    positivity

  have h_coarseTubes_nonempty : coarseTubes.Nonempty := by
    by_cases h : coarseTubes_orig.Nonempty
    · have h_j : j_level = j_level_orig := by simp [j_level, h]
      have h_eq : coarseTubes = coarseTubes_orig := by
        ext x
        simp [coarseTubes, coarseTubes_orig, h_j]
      rw [h_eq]
      exact h
    · have h_j : j_level = dyadicLevel (wpop U0) := by simp [j_level, h]
      refine ⟨U0, Finset.mem_filter.mpr ⟨hU0, ?_⟩⟩
      exact h_j.symm

  have h_weight : ∑ U ∈ coarseTubes, wpop U ≥ total_wpop / numDyadicLevels N := by
    by_cases h : coarseTubes_orig.Nonempty
    · have h_j : j_level = j_level_orig := by simp [j_level, h]
      have h_eq : coarseTubes = coarseTubes_orig := by
        ext x
        simp [coarseTubes, coarseTubes_orig, h_j]
      rw [h_eq]
      have h_total_def : total_wpop = ∑ x ∈ TΔ_all, wpop x := by rfl
      rw [h_total_def]
      exact h_weight_orig
    · have h_small : total_wpop / numDyadicLevels N = 0 := by
        have h_empty : coarseTubes_orig = ∅ := by
          simpa [Finset.not_nonempty_iff_eq_empty] using h
        have h' : total_wpop / numDyadicLevels N ≤ ∑ U ∈ coarseTubes_orig, wpop U := by
          have h_total_def : total_wpop = ∑ x ∈ TΔ_all, wpop x := by rfl
          rw [h_total_def]
          exact h_weight_orig
        rw [h_empty] at h'
        have h_simp : ∑ U ∈ (∅ : Finset (DyadicTube m)), wpop U = 0 := by simp
        rw [h_simp] at h'
        exact Nat.eq_zero_of_le_zero h'
      rw [h_small]
      exact Nat.zero_le _

  have h_wpop_range : ∀ U ∈ coarseTubes, L ≤ wpop U ∧ wpop U < 2 * L := by
    intro U hU
    have h1 : dyadicLevel (wpop U) = j_level := (Finset.mem_filter.mp hU).2
    have h2 : 0 < wpop U := h_wpop_pos U (Finset.filter_subset _ _ hU)
    have h_ne : wpop U ≠ 0 := by linarith
    have h_log : Nat.log 2 (wpop U) + 1 = j_level := by
      simpa [dyadicLevel, h_ne] using h1
    have h_log2 : Nat.log 2 (wpop U) = j_level - 1 := by omega
    have h4 : 2 ^ (j_level - 1) ≤ wpop U := by
      rw [←h_log2]
      exact Nat.pow_log_le_self 2 h_ne
    have h5 : wpop U < 2 ^ j_level := by
      have h6 : Nat.log 2 (wpop U) < j_level := by omega
      exact Nat.lt_pow_of_log_lt (by norm_num) h6
    have h_eq : 2 ^ j_level = 2 * L := by
      dsimp only [L]
      have h_jpos : 1 ≤ j_level := h_j_level_pos
      have h9 : 0 < j_level := by omega
      have h10 : ∃ j' : ℕ, j_level = j' + 1 := by
        refine ⟨j_level - 1, ?_⟩
        omega
      rcases h10 with ⟨j', hj⟩
      rw [hj]
      simp [pow_succ] <;> ring
    dsimp only [L]
    exact ⟨h4, by rw [h_eq] at h5; exact h5⟩

  let coarseFamily' : DyadicSquare n → Finset (DyadicTube m) := fun p =>
    (coarseFamily p) ∩ coarseTubes

  have h_coarse_sub' : ∀ p ∈ P, coarseFamily' p ⊆ coarseTubes := by
    intro p _ x hx
    exact (Finset.mem_inter.mp hx).2

  have h_fine_per_coarse : ∀ p ∈ P, ∀ U ∈ coarseFamily' p,
      ((tfOpt p).filter (fun T => T.toSet ⊆ U.toSet)).card ≥ m₁ p := by
    intro p hp U hU
    have hU_in_coarse : U ∈ coarseFamily p := (Finset.mem_inter.mp hU).1
    rcases Finset.mem_image.mp hU_in_coarse with ⟨t, ht, rfl⟩
    have h_band_def : bandTubes p = (tubeFamily p hp).filter (fun t =>
      let c := countInCoarse hnm (tubeFamily p hp) (coarseAnc hnm t)
      2^(j p hp) ≤ c ∧ c < 2^(j p hp + 1)) := h_band_eq p hp
    have ht' : t ∈ (tubeFamily p hp).filter (fun t =>
      let c := countInCoarse hnm (tubeFamily p hp) (coarseAnc hnm t)
      2^(j p hp) ≤ c ∧ c < 2^(j p hp + 1)) := by
      have h : t ∈ bandTubes p := ht
      rw [h_band_def] at h
      exact h
    have h_filter := Finset.mem_filter.mp ht'
    have h5 : 2^(j p hp) ≤ countInCoarse hnm (tubeFamily p hp) (coarseAnc hnm t) := h_filter.2.1
    have h_count : m₁ p ≤ countInCoarse hnm (tfOpt p) (coarseAnc hnm t) := by
      have h6 : tfOpt p = tubeFamily p hp := h_tfOpt p hp
      have h7 : m₁ p = 2^(j p hp) := h_m1_eq p hp
      rw [h6, h7]
      exact h5
    have h_iff : ∀ (T : DyadicTube n), T.toSet ⊆ (coarseAnc hnm t).toSet ↔ coarseAnc hnm T = coarseAnc hnm t := by
      intro T
      constructor
      · intro hcont
        exact (InductionOnScales.unique_coarse_ancestor hnm T (coarseAnc hnm t) hcont).symm
      · intro h
        have hcont : T.toSet ⊆ (coarseAnc hnm T).toSet := by exact coarseAnc_contains hnm T
        convert hcont using 2 <;> exact h.symm
    have h_eq : ((tfOpt p).filter (fun T => T.toSet ⊆ (coarseAnc hnm t).toSet)) =
        (tfOpt p).filter (fun T => coarseAnc hnm T = coarseAnc hnm t) := by
      apply Finset.filter_congr
      intro T _
      exact h_iff T
    rw [h_eq]
    simpa [countInCoarse] using h_count

  have h_count_eq : ∀ (p : DyadicSquare n) (hp : p ∈ P) (U : DyadicTube m),
      U ∈ coarseFamily' p →
      countInCoarse hnm (tfOpt p) U = ((tfOpt p).filter (fun T => T.toSet ⊆ U.toSet)).card := by
    intro p hp U hU
    have hU_in_coarse : U ∈ coarseFamily p := (Finset.mem_inter.mp hU).1
    rcases Finset.mem_image.mp hU_in_coarse with ⟨t, _ht, rfl⟩
    have h_iff : ∀ (T : DyadicTube n), T.toSet ⊆ (coarseAnc hnm t).toSet ↔ coarseAnc hnm T = coarseAnc hnm t := by
      intro T
      constructor
      · intro hcont
        exact (InductionOnScales.unique_coarse_ancestor hnm T (coarseAnc hnm t) hcont).symm
      · intro h
        have hcont : T.toSet ⊆ (coarseAnc hnm T).toSet := by exact coarseAnc_contains hnm T
        convert hcont using 2 <;> exact h.symm
    have h_filter_eq : (tfOpt p).filter (fun T => T.toSet ⊆ (coarseAnc hnm t).toSet) =
        (tfOpt p).filter (fun T => coarseAnc hnm T = coarseAnc hnm t) := by
      apply Finset.filter_congr
      intro T _
      exact h_iff T
    rw [h_filter_eq]
    <;> rfl

  have h_wpop' : ∀ U ∈ coarseTubes,
      ∑ p ∈ P.filter (fun p => U ∈ coarseFamily' p), (m₁ p : ℝ) ≥ (L : ℝ) := by
    intro U hU
    have h1 : ∀ p ∈ P, U ∈ coarseFamily' p ↔ U ∈ coarseFamily p := by
      intro p _
      simp [coarseFamily', hU]
      <;> exact and_iff_left hU
    have h2 : (P.filter (fun p => U ∈ coarseFamily' p)) = (P.filter (fun p => U ∈ coarseFamily p)) := by
      ext p
      simp only [Finset.mem_filter]
      by_cases hP : p ∈ P
      · simp [hP, h1 p hP]
      · simp [hP]
    rw [h2]
    have h_def : (wpop U : ℝ) = ∑ p ∈ P.filter (fun p => U ∈ coarseFamily p), (m₁ p : ℝ) := by
      simp [wpop] <;> rfl
    rw [←h_def]
    exact_mod_cast (h_wpop_range U hU).1

  have h_fine_sset : ∀ p ∈ P, IsFiniteTubeSSet s C₁ (tfOpt p) := by
    intro p hp
    rw [h_tfOpt p hp]
    exact h_sset p hp

  have h_fine_size : ∀ p ∈ P, (tfOpt p).card = M := by
    intro p hp
    rw [h_tfOpt p hp]
    exact h_size p hp

  -- Relation: L ≥ M * |P| / (K_sset * |coarseTubes|)
  let numLevels : ℕ := numDyadicLevels N
  let k_real : ℝ := (Nat.log 2 M : ℝ) + 2
  let K : ℝ := 32 * k_real * (numLevels : ℝ)
  let K_sset : ℝ := K / 2

  have hK_pos : 1 ≤ K := by
    dsimp only [K, k_real, numLevels, numDyadicLevels]
    have h1 : 0 ≤ (Nat.log 2 M : ℝ) := by positivity
    have h2 : 0 ≤ (Nat.log 2 N : ℝ) := by positivity
    have h3 : (Nat.log 2 M : ℝ) + 2 ≥ 1 := by linarith
    have h4 : (↑(Nat.log 2 N + 2) : ℝ) ≥ 1 := by
      have h5 : (↑(Nat.log 2 N + 2) : ℝ) = (Nat.log 2 N : ℝ) + 2 := by simp
      rw [h5] <;> linarith
    have h6 : 1 ≤ 32 * ((Nat.log 2 M : ℝ) + 2) * (↑(Nat.log 2 N + 2) : ℝ) := by
      calc 1
        ≤ 32 * (1 : ℝ) * 1 := by norm_num
      _ ≤ 32 * ((Nat.log 2 M : ℝ) + 2) * (↑(Nat.log 2 N + 2) : ℝ) := by gcongr <;> linarith
    exact h6

  have hK_sset_pos : 1 ≤ K_sset := by
    dsimp only [K_sset, K, k_real, numLevels, numDyadicLevels]
    have h1 : 0 ≤ (Nat.log 2 M : ℝ) := by positivity
    have h2 : (Nat.log 2 M : ℝ) + 2 ≥ 2 := by linarith
    have h3 : 0 ≤ (Nat.log 2 N : ℝ) := by positivity
    have h4 : (↑(Nat.log 2 N + 2) : ℝ) = (Nat.log 2 N : ℝ) + 2 := by simp
    rw [h4]
    have h5 : (Nat.log 2 N : ℝ) + 2 ≥ 2 := by linarith
    nlinarith

  have h_relation : (L : ℝ) ≥ (M : ℝ) * (P.card : ℝ) / (K_sset * (coarseTubes.card : ℝ)) := by
    have h_numLevels_pos : 0 < numLevels := by
      dsimp only [numLevels, numDyadicLevels] <;> positivity
    have h_card_pos : 0 < coarseTubes.card := h_coarseTubes_nonempty.card_pos
    have h_k_pos : 0 < k_real := by
      dsimp only [k_real]
      have h1 : 0 ≤ (Nat.log 2 M : ℝ) := by positivity
      linarith
    have h_sum_upper : (∑ U ∈ coarseTubes, wpop U) < 2 * L * coarseTubes.card := by
      have h1 : ∀ U ∈ coarseTubes, wpop U < 2 * L := fun U hU => (h_wpop_range U hU).2
      have h2 : ∑ U ∈ coarseTubes, wpop U < ∑ U ∈ coarseTubes, (2 * L) :=
        Finset.sum_lt_sum_of_nonempty h_coarseTubes_nonempty h1
      have h3 : ∑ U ∈ coarseTubes, (2 * L) = 2 * L * coarseTubes.card := by
        simp [Finset.sum_const] <;> ring
      rw [h3] at h2
      exact h2
    have h_div_lt : (total_wpop / numLevels : ℕ) < 2 * L * coarseTubes.card :=
      lt_of_le_of_lt h_weight h_sum_upper
    have h_main : (L : ℝ) * (coarseTubes.card : ℝ) ≥
        (M : ℝ) * (P.card : ℝ) / (16 * k_real * (numLevels : ℝ)) :=
      relation_helper_weighted total_wpop numLevels L coarseTubes.card M P.card k_real
        h_numLevels_pos h_card_pos hL_pos h_total_lower h_k_pos h_div_lt
    have h_K_sset_eq : K_sset = 16 * k_real * (numLevels : ℝ) := by
      dsimp only [K_sset, K] <;> ring
    rw [h_K_sset_eq]
    have h_card_pos' : 0 < (coarseTubes.card : ℝ) := by exact_mod_cast h_card_pos
    have hY_pos : 0 < (16 * k_real * (numLevels : ℝ)) := by positivity
    exact final_relation_step (L : ℝ) (coarseTubes.card : ℝ) ((M : ℝ) * (P.card : ℝ))
      (16 * k_real * (numLevels : ℝ)) h_card_pos' hY_pos h_main

  -- Step 4: SSet verification
  have h_sset_coarse : IsFiniteTubeSSet s (K_sset * 2 * C₁) coarseTubes :=
    InductionOnScales.coarse_sset_verification_weighted hnm
      s hs hs_one C₁ hC₁ M hM
      coarseTubes h_coarseTubes_nonempty P hP_nonempty
      coarseFamily' tfOpt m₁ (fun p hp => h_m1_pos p hp)
      L hL_pos K_sset hK_sset_pos
      h_coarse_sub' h_wpop' h_fine_per_coarse h_fine_sset h_fine_size
      h_relation

  let C₂ : ℝ := K_sset * 2 * C₁
  have hC₂ : 1 ≤ C₂ := by
    dsimp only [C₂]
    have h1 : 1 ≤ K_sset := hK_sset_pos
    have h2 : 1 ≤ C₁ := hC₁
    nlinarith

  have hC₂_eq : C₂ = K * C₁ := by
    dsimp only [C₂, K_sset]
    <;> ring

  have hC₂_le : C₂ ≤ K * C₁ := by
    rw [hC₂_eq]
    <;> rfl

  let H : ℝ := (L : ℝ)
  have hH : 1 ≤ H := by
    dsimp only [H]
    have h1 : 1 ≤ L := hL_pos
    exact_mod_cast h1

  -- Incidence: H ≤ ∑ p ∈ P, countInCoarse(tfOpt p, U)
  have h_incidence_final : ∀ U ∈ coarseTubes,
      H ≤ ∑ p ∈ P, (countInCoarse hnm (tfOpt p) U : ℝ) := by
    intro U hU
    have h1 : H ≤ ∑ p ∈ P.filter (fun p => U ∈ coarseFamily' p), (m₁ p : ℝ) := h_wpop' U hU
    have h2a : ∑ p ∈ P.filter (fun p => U ∈ coarseFamily' p), (m₁ p : ℝ) ≤
        ∑ p ∈ P.filter (fun p => U ∈ coarseFamily' p), (countInCoarse hnm (tfOpt p) U : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      have h3 : U ∈ coarseFamily' p := (Finset.mem_filter.mp hp).2
      have h4 : p ∈ P := (Finset.mem_filter.mp hp).1
      have h5 : countInCoarse hnm (tfOpt p) U = ((tfOpt p).filter (fun T => T.toSet ⊆ U.toSet)).card :=
        h_count_eq p h4 U h3
      rw [h5]
      exact_mod_cast h_fine_per_coarse p h4 U h3
    have h2b : ∑ p ∈ P.filter (fun p => U ∈ coarseFamily' p), (countInCoarse hnm (tfOpt p) U : ℝ) ≤
        ∑ p ∈ P, (countInCoarse hnm (tfOpt p) U : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro _ _ _
      positivity
    have h2 : ∑ p ∈ P.filter (fun p => U ∈ coarseFamily' p), (m₁ p : ℝ) ≤
        ∑ p ∈ P, (countInCoarse hnm (tfOpt p) U : ℝ) :=
      le_trans h2a h2b
    exact le_trans h1 h2

  -- H * |coarseTubes| ≤ K * M * |P|
  have h_card_upper : H * (coarseTubes.card : ℝ) ≤ K * (M : ℝ) * (P.card : ℝ) := by
    have h1 : ∑ U ∈ coarseTubes, (wpop U : ℝ) ≤ (total_wpop : ℝ) := by
      have h1a : coarseTubes ⊆ TΔ_all := Finset.filter_subset _ _
      have h1b : ∑ U ∈ coarseTubes, (wpop U : ℝ) ≤ ∑ U ∈ TΔ_all, (wpop U : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg h1a
        intro _ _ _
        positivity
      have h1c : (total_wpop : ℝ) = ∑ U ∈ TΔ_all, (wpop U : ℝ) := by
        simp [total_wpop] <;> rfl
      rw [h1c]
      exact h1b
    have h2 : H * (coarseTubes.card : ℝ) ≤ ∑ U ∈ coarseTubes, (wpop U : ℝ) := by
      have h3 : ∑ U ∈ coarseTubes, (L : ℝ) ≤ ∑ U ∈ coarseTubes, (wpop U : ℝ) := by
        apply Finset.sum_le_sum
        intro U hU
        exact_mod_cast (h_wpop_range U hU).1
      have h4 : ∑ U ∈ coarseTubes, (L : ℝ) = (L : ℝ) * (coarseTubes.card : ℝ) := by
        simp [Finset.sum_const] <;> ring
      rw [h4] at h3
      exact h3
    have h5 : (total_wpop : ℝ) ≤ (P.card : ℝ) * (M : ℝ) := by
      have h_swap' : (total_wpop : ℝ) = ∑ p ∈ P, ((m₁ p : ℝ) * ((coarseFamily p).card : ℝ)) := by
        exact_mod_cast h_swap
      rw [h_swap']
      have h6 : ∀ p ∈ P, (m₁ p : ℝ) * ((coarseFamily p).card : ℝ) ≤ (M : ℝ) := by
        intro p hp
        have h7 : (m₁ p : ℝ) * ((coarseFamily p).card : ℝ) ≤ ((bandTubes p).card : ℝ) := by
          have h8 : ∑ U ∈ coarseFamily p, (countInCoarse hnm (tubeFamily p hp) U : ℝ) = ((bandTubes p).card : ℝ) := by
            have h := sum_countInCoarse_band hnm (tubeFamily p hp) (coarseFamily p)
            rw [h_band_union p hp] at h
            exact_mod_cast h
          have h9 : ∑ U ∈ coarseFamily p, (m₁ p : ℝ) ≤ ∑ U ∈ coarseFamily p, (countInCoarse hnm (tubeFamily p hp) U : ℝ) := by
            apply Finset.sum_le_sum
            intro U hU
            exact_mod_cast (h_mult p hp U hU).1
          have h9a : ∑ U ∈ coarseFamily p, (m₁ p : ℝ) = (m₁ p : ℝ) * ((coarseFamily p).card : ℝ) := by
            simp [Finset.sum_const] <;> ring
          rw [h9a, h8] at h9
          exact h9
        have h10 : ((bandTubes p).card : ℝ) ≤ (M : ℝ) := by
          have h11 : bandTubes p ⊆ tubeFamily p hp := by
            simp [bandTubes, hp] <;> exact Finset.filter_subset _ _
          have h12 : (bandTubes p).card ≤ (tubeFamily p hp).card := Finset.card_le_card h11
          have h13 : (tubeFamily p hp).card = M := h_size p hp
          have h14 : (bandTubes p).card ≤ M := by
            rw [h13] at h12
            exact h12
          exact_mod_cast h14
        linarith
      have h_sum : ∑ p ∈ P, ((m₁ p : ℝ) * ((coarseFamily p).card : ℝ)) ≤ ∑ p ∈ P, (M : ℝ) :=
        Finset.sum_le_sum h6
      have h_final : ∑ p ∈ P, (M : ℝ) = (P.card : ℝ) * (M : ℝ) := by
        simp [Finset.sum_const] <;> ring
      rw [h_final] at h_sum
      exact h_sum
    calc H * (coarseTubes.card : ℝ)
      ≤ ∑ U ∈ coarseTubes, (wpop U : ℝ) := h2
    _ ≤ (total_wpop : ℝ) := h1
    _ ≤ (P.card : ℝ) * (M : ℝ) := h5
    _ ≤ K * (M : ℝ) * (P.card : ℝ) := card_upper_final_step K hK_pos M P.card

  -- M * |P| ≤ K * H * |coarseTubes|
  have h_card_lower : (M : ℝ) * (P.card : ℝ) ≤ K * H * (coarseTubes.card : ℝ) := by
    have h2 : 0 < (coarseTubes.card : ℝ) := by exact_mod_cast h_coarseTubes_nonempty.card_pos
    have h3 : 0 < K_sset := by linarith [hK_sset_pos]
    have h5 : H = (L : ℝ) := by rfl
    have h6 : K = 2 * K_sset := by
      dsimp only [K_sset] <;> ring
    rw [h5, h6]
    exact card_lower_helper (L : ℝ) K_sset (coarseTubes.card : ℝ) M P.card h2 h3 h_relation

  have h_P_card : (P.card : ℝ) ≤ K * (P.card : ℝ) :=
    P_card_le_K_helper K hK_pos P.card

  refine' ⟨K, hK_pos, P, Finset.Subset.refl P, coarseTubes, C₂, hC₂, H, hH, _⟩
  dsimp only
  exact ⟨hP_nonempty, h_P_card, h_sset_coarse, hC₂_le, h_card_upper, h_card_lower, h_incidence_final⟩

end

end InductionOnScales
