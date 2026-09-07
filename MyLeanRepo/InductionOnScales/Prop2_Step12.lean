module

/-
# Proposition 2, Steps 1-2: Per-point and across-point multiplicity pigeonholing
-/

public import MyLeanRepo.InductionOnScales.Pigeonhole
public import MyLeanRepo.InductionOnScales.Definitions
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped BigOperators

noncomputable section

variable {n m : ℕ} (hnm : m ≤ n)

/-- Coarse ancestor. -/
abbrev coarseAnc' (T : DyadicTube n) : DyadicTube m :=
  deprecatedCoordinatewiseAncestor hnm T

/-- Number of fine tubes from F whose coarse ancestor is U. -/
def countInCoarse' (F : Finset (DyadicTube n)) (U : DyadicTube m) : ℕ :=
  (F.filter (fun T => coarseAnc' hnm T = U)).card

/-- The fine tubes partition among their coarse ancestors. -/
lemma sum_countInCoarse' (F : Finset (DyadicTube n)) :
    ∑ U ∈ F.image (coarseAnc' hnm), countInCoarse' hnm F U = F.card := by
  let fiber (U : DyadicTube m) := F.filter (fun T => coarseAnc' hnm T = U)
  have h_disj : (F.image (coarseAnc' hnm) : Set (DyadicTube m)).PairwiseDisjoint fiber := by
    intro U _ V _ hne
    simp only [Finset.disjoint_left, fiber, Finset.mem_filter]
    intro T hT1 hT2
    have h1 : coarseAnc' hnm T = U := hT1.2
    have h2 : coarseAnc' hnm T = V := hT2.2
    have h3 : U = V := h1.symm.trans h2
    exact hne h3
  have h_union : (F.image (coarseAnc' hnm)).biUnion fiber = F := by
    ext T
    simp only [Finset.mem_biUnion, fiber, Finset.mem_filter, Finset.mem_image]
    <;> aesop
  calc
    ∑ U ∈ F.image (coarseAnc' hnm), countInCoarse' hnm F U
      = ∑ U ∈ F.image (coarseAnc' hnm), (fiber U).card := by rfl
    _ = ((F.image (coarseAnc' hnm)).biUnion fiber).card := by
      rw [Finset.card_biUnion h_disj]
    _ = F.card := by rw [h_union]

/-- Filtering fine tubes by a predicate on their coarse-ancestor multiplicity
equals the sum of multiplicities of coarse tubes satisfying the predicate. -/
lemma filter_by_multiplicity_eq_sum'
    (F : Finset (DyadicTube n))
    (Q : ℕ → Prop) [DecidablePred Q] :
    (F.filter (fun T => Q (countInCoarse' hnm F (coarseAnc' hnm T)))).card =
    ∑ U ∈ F.image (coarseAnc' hnm),
      if Q (countInCoarse' hnm F U)
      then (countInCoarse' hnm F U) else 0 := by
  let fiber (U : DyadicTube m) := F.filter (fun T => coarseAnc' hnm T = U)
  let goodFibers := (F.image (coarseAnc' hnm)).filter (fun U => Q (countInCoarse' hnm F U))
  have h1 : F.filter (fun T => Q (countInCoarse' hnm F (coarseAnc' hnm T))) =
      goodFibers.biUnion fiber := by
    ext T
    simp only [Finset.mem_filter, Finset.mem_biUnion, goodFibers, fiber]
    <;> aesop
  rw [h1]
  have h_disj : (goodFibers : Set (DyadicTube m)).PairwiseDisjoint fiber := by
    intro U _ V _ hne
    simp only [Finset.disjoint_left, fiber, Finset.mem_filter]
    intro T hT1 hT2
    have h1 : coarseAnc' hnm T = U := hT1.2
    have h2 : coarseAnc' hnm T = V := hT2.2
    have h3 : U = V := h1.symm.trans h2
    exact hne h3
  rw [Finset.card_biUnion h_disj]
  have h_sum : ∑ U ∈ goodFibers, (fiber U).card =
      ∑ U ∈ F.image (coarseAnc' hnm),
        if Q (countInCoarse' hnm F U) then (fiber U).card else 0 := by
    rw [Finset.sum_filter]
    <;> rfl
  rw [h_sum]
  apply Finset.sum_congr rfl
  intro U _
  rfl

/-- Dyadic band lemma. -/
lemma exists_dyadic_band' {α : Type*} [DecidableEq α]
    (s : Finset α) (w : α → ℕ) (N : ℝ) (L : ℕ)
    (h_sum : N ≤ ∑ i ∈ s, (w i : ℝ))
    (h_max : ∀ i ∈ s, w i ≤ 2^L) :
    ∃ j : ℕ, j ≤ L ∧
      (N : ℝ) / ((L : ℝ) + 1) ≤
        ∑ i ∈ s.filter (fun i => 2^j ≤ w i ∧ w i < 2^(j+1)), (w i : ℝ) := by
  let B (j : ℕ) : Finset α := s.filter (fun i => 2^j ≤ w i ∧ w i < 2^(j+1))
  have h_disj : ∀ (j k : ℕ), j ≠ k → Disjoint (B j) (B k) := by
    intro j k hjk
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    have h1 : 2^j ≤ w i ∧ w i < 2^(j+1) := (Finset.mem_filter.mp hi1).2
    have h2 : 2^k ≤ w i ∧ w i < 2^(k+1) := (Finset.mem_filter.mp hi2).2
    by_cases h : j < k
    · have h5 : 2^(j+1) ≤ 2^k := by gcongr <;> omega
      linarith
    · have h6 : k < j := by omega
      have h9 : 2^(k+1) ≤ 2^j := by gcongr <;> omega
      linarith
  have h_exists_band : ∀ (i : α), i ∈ s → 0 < w i →
      ∃ (j : ℕ), j ≤ L ∧ i ∈ B j := by
    intro i hi hpos
    let j := Nat.log 2 (w i)
    have hj1 : 2^j ≤ w i := by
      have h : 2 ^ Nat.log 2 (w i) ≤ w i := Nat.pow_log_le_self 2 (by omega)
      exact h
    have hj2 : w i < 2^(j + 1) := by
      have h : w i < 2 ^ (Nat.log 2 (w i) + 1) := Nat.lt_pow_succ_log_self (by norm_num) (w i)
      exact h
    have hj3 : j ≤ L := by
      by_contra h
      have h4 : L < j := by omega
      have h5 : 2^L < 2^j := by gcongr <;> omega
      have h6 : w i ≤ 2^L := h_max i hi
      linarith
    exact ⟨j, hj3, Finset.mem_filter.mpr ⟨hi, ⟨hj1, hj2⟩⟩⟩
  let S : Finset α := Finset.biUnion (Finset.range (L + 1)) B
  have hS_cover : s.filter (fun i => 0 < w i) ⊆ S := by
    intro i hi
    have hpos : 0 < w i := (Finset.mem_filter.mp hi).2
    have hi' : i ∈ s := (Finset.mem_filter.mp hi).1
    rcases h_exists_band i hi' hpos with ⟨j, hj, hB⟩
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr (by omega), hB⟩
  have h_sum_bands : ∑ j ∈ Finset.range (L + 1), ∑ i ∈ B j, (w i : ℝ) =
      ∑ i ∈ S, (w i : ℝ) := by
    rw [Finset.sum_biUnion]
    intro j _ k _ hne
    exact h_disj j k hne
  have h_sum_S : (N : ℝ) ≤ ∑ i ∈ S, (w i : ℝ) := by
    have h1 : ∑ i ∈ s.filter (fun i => 0 < w i), (w i : ℝ) = ∑ i ∈ s, (w i : ℝ) := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases h : 0 < w i
      · simp [h]
      · have h' : w i = 0 := by omega
        simp [h', h] <;> norm_cast
    have h2 : ∑ i ∈ s.filter (fun i => 0 < w i), (w i : ℝ) ≤ ∑ i ∈ S, (w i : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hS_cover (fun _ _ _ => by positivity)
    have h3 : (N : ℝ) ≤ ∑ i ∈ s, (w i : ℝ) := by exact_mod_cast h_sum
    calc (N : ℝ)
      ≤ ∑ i ∈ s, (w i : ℝ) := h3
    _ = ∑ i ∈ s.filter (fun i => 0 < w i), (w i : ℝ) := h1.symm
    _ ≤ ∑ i ∈ S, (w i : ℝ) := h2
  have h_main : ∃ j ∈ Finset.range (L + 1),
      (N : ℝ) / ((L : ℝ) + 1) ≤ ∑ i ∈ B j, (w i : ℝ) := by
    by_contra h
    push Not at h
    have h_nonempty : (Finset.range (L + 1)).Nonempty := by simp
    have h_lt : ∑ j ∈ Finset.range (L + 1), ∑ i ∈ B j, (w i : ℝ) < (N : ℝ) := by
      calc ∑ j ∈ Finset.range (L + 1), ∑ i ∈ B j, (w i : ℝ)
        < ∑ j ∈ Finset.range (L + 1), (N : ℝ) / ((L : ℝ) + 1) :=
          Finset.sum_lt_sum_of_nonempty h_nonempty (fun j hj => h j hj)
      _ = (N : ℝ) := by
        simp [Finset.sum_const, Finset.card_range] <;> field_simp <;> ring
    rw [h_sum_bands] at h_lt
    linarith
  rcases h_main with ⟨j, hj, hband⟩
  have hj' : j ≤ L := by
    have h : j < L + 1 := Finset.mem_range.mp hj
    omega
  exact ⟨j, hj', hband⟩

/-- Simple pigeonhole. -/
lemma simple_pigeonhole' {α : Type*} [DecidableEq α]
    (S : Finset α) (f : α → ℕ) (B : ℕ) (hB : ∀ x ∈ S, f x ≤ B) :
    ∃ k : ℕ, k ≤ B ∧
      (S.card : ℝ) ≤ ((B : ℝ) + 1) * ((S.filter (fun x => f x = k)).card : ℝ) := by
  let t := Finset.range (B + 1)
  have hf : ∀ x ∈ S, f x ∈ t := by
    intro x hx
    have hle : f x ≤ B := hB x hx
    have h : f x < B + 1 := by linarith
    exact Finset.mem_range.mpr h
  have h_sum : ∑ k ∈ t, (S.filter (fun x => f x = k)).card = S.card := by
    have h : ∑ k ∈ t, (S.filter (fun x => f x = k)).card =
        (S.filter (fun x => f x ∈ t)).card := by
      rw [Finset.sum_card_fiberwise_eq_card_filter]
    have h2 : S.filter (fun x => f x ∈ t) = S := by
      ext x
      simp only [Finset.mem_filter]
      <;> constructor <;> intro h <;> tauto
    rw [h, h2]
  by_cases hS : S = ∅
  · subst hS
    refine ⟨0, by omega, ?_⟩
    simp
  · have htn : t.Nonempty := by simp [t] <;> omega
    by_contra h'
    push Not at h'
    have h_lt : ∀ k ∈ t, ((S.filter (fun x => f x = k)).card : ℝ) * ((B + 1 : ℝ)) < (S.card : ℝ) := by
      intro k hk
      have hk' : k ≤ B := by
        have h : k < B + 1 := Finset.mem_range.mp hk
        omega
      have h : (B + 1 : ℝ) * ((S.filter (fun x => f x = k)).card : ℝ) < (S.card : ℝ) := h' k hk'
      have h_comm : ((S.filter (fun x => f x = k)).card : ℝ) * ((B + 1 : ℝ)) =
          (B + 1 : ℝ) * ((S.filter (fun x => f x = k)).card : ℝ) := by ring
      rw [h_comm]
      exact h
    have h_sum_lt : ∑ k ∈ t, (((S.filter (fun x => f x = k)).card : ℝ) * (B + 1 : ℝ)) <
        ∑ k ∈ t, (S.card : ℝ) := by
      apply Finset.sum_lt_sum_of_nonempty htn
      intro k hk
      exact h_lt k hk
    have h_sumR : (∑ k ∈ t, ((S.filter (fun x => f x = k)).card : ℝ)) = (S.card : ℝ) := by
      exact_mod_cast h_sum
    have h_eq1 : ∑ k ∈ t, (((S.filter (fun x => f x = k)).card : ℝ) * (B + 1 : ℝ)) =
        (B + 1 : ℝ) * (∑ k ∈ t, ((S.filter (fun x => f x = k)).card : ℝ)) := by
      have h : ∑ k ∈ t, (((S.filter (fun x => f x = k)).card : ℝ) * (B + 1 : ℝ)) =
          ∑ k ∈ t, ((B + 1 : ℝ) * ((S.filter (fun x => f x = k)).card : ℝ)) := by
        apply Finset.sum_congr rfl; intro k _; ring
      rw [h, Finset.mul_sum]
    have h_eq2 : ∑ k ∈ t, (S.card : ℝ) = (B + 1 : ℝ) * (S.card : ℝ) := by
      simp [t, Finset.sum_const] <;> norm_cast <;> ring
    rw [h_eq1, h_eq2] at h_sum_lt
    rw [h_sumR] at h_sum_lt <;> linarith

/-- Steps 1-2 of Proposition 2. -/
lemma prop2_step12
    {α : Type*} [DecidableEq α]
    (P : Finset α)
    (T : α → Finset (DyadicTube n))
    (M : ℕ) (hM : 0 < M)
    (h_size : ∀ p ∈ P, (T p).card = M)
    (hP_nonempty : P.Nonempty) :
    ∃ (m1 : ℕ) (P1 : Finset α),
      P1 ⊆ P ∧
      P1.Nonempty ∧
      (∀ p ∈ P1, (M : ℝ) / ((Nat.log 2 M + 2 : ℕ) : ℝ) ≤
        (((T p).filter (fun t =>
          let c := countInCoarse' hnm (T p) (coarseAnc' hnm t)
          m1 ≤ c ∧ c < 2 * m1)).card : ℝ)) ∧
      (P1.card : ℝ) * ((Nat.log 2 M + 2 : ℕ) : ℝ) ≥ (P.card : ℝ) := by
  let L := Nat.log 2 M + 1
  have hM_bound : M ≤ 2 ^ L := by
    have h1 : M < 2 ^ (Nat.log 2 M + 1) := Nat.lt_pow_succ_log_self (by norm_num) M
    simpa [L] using h1.le
  -- For each p ∈ P, find a dyadic band j(p)
  have h_exists : ∀ (p : α), p ∈ P →
      ∃ (j : ℕ), j ≤ L ∧
        (M : ℝ) / ((L : ℝ) + 1) ≤
          ∑ U ∈ (T p).image (coarseAnc' hnm),
            if 2^j ≤ countInCoarse' hnm (T p) U ∧ countInCoarse' hnm (T p) U < 2^(j+1)
            then (countInCoarse' hnm (T p) U : ℝ) else 0 := by
    intro p hp
    let coarseImg := (T p).image (coarseAnc' hnm)
    let w : DyadicTube m → ℕ := fun U => countInCoarse' hnm (T p) U
    have h_sum : (M : ℝ) ≤ ∑ U ∈ coarseImg, (w U : ℝ) := by
      have h : ∑ U ∈ coarseImg, w U = (T p).card := sum_countInCoarse' hnm (T p)
      have h2 : (T p).card = M := h_size p hp
      have h3 : (∑ U ∈ coarseImg, (w U : ℝ)) = ((T p).card : ℝ) := by exact_mod_cast h
      rw [h3, h2] <;> norm_cast
    have h_max : ∀ U ∈ coarseImg, w U ≤ 2 ^ L := by
      intro U _
      have h3 : w U ≤ (T p).card := by
        simpa [w, countInCoarse'] using Finset.card_filter_le _ _
      rw [h_size p hp] at h3
      exact h3.trans hM_bound
    rcases exists_dyadic_band' coarseImg w (M : ℝ) L h_sum h_max with ⟨j, hj_le, hband⟩
    have hband' : (M : ℝ) / ((L : ℝ) + 1) ≤
        ∑ U ∈ coarseImg,
          if (2^j ≤ w U ∧ w U < 2^(j+1))
          then (w U : ℝ) else 0 := by
      have h_eq : ∑ U ∈ coarseImg.filter (fun U => 2^j ≤ w U ∧ w U < 2^(j+1)), (w U : ℝ) =
          ∑ U ∈ coarseImg, (if (2^j ≤ w U ∧ w U < 2^(j+1)) then (w U : ℝ) else 0) := by
        rw [Finset.sum_filter]
        <;> rfl
      have h : (M : ℝ) / ((L : ℝ) + 1) ≤ ∑ U ∈ coarseImg.filter (fun U => 2^j ≤ w U ∧ w U < 2^(j+1)), (w U : ℝ) := hband
      rw [h_eq] at h
      exact h
    exact ⟨j, hj_le, hband'⟩
  -- Define j(p) for p ∈ P, and 0 otherwise
  let j : α → ℕ := fun p =>
    if hp : p ∈ P then Classical.choose (h_exists p hp) else 0
  have hj_le : ∀ p ∈ P, j p ≤ L := by
    intro p hp
    have h4 : j p = Classical.choose (h_exists p hp) := by
      simp [j, hp]
    rw [h4]
    exact (Classical.choose_spec (h_exists p hp)).1
  have hband : ∀ p ∈ P, (M : ℝ) / ((L : ℝ) + 1) ≤
      ∑ U ∈ (T p).image (coarseAnc' hnm),
        if 2^(j p) ≤ countInCoarse' hnm (T p) U ∧ countInCoarse' hnm (T p) U < 2^(j p + 1)
          then (countInCoarse' hnm (T p) U : ℝ) else 0 := by
    intro p hp
    have h4 : j p = Classical.choose (h_exists p hp) := by simp [j, hp]
    rw [h4]
    exact (Classical.choose_spec (h_exists p hp)).2
  -- Pigeonhole across points to find fixed j
  have h_j_bdd : ∀ p ∈ P, j p ≤ L := hj_le
  have h_main := simple_pigeonhole' P j L h_j_bdd
  rcases h_main with ⟨j_fixed, hj_fixed_le, hcard⟩
  let P1 := P.filter (fun p => j p = j_fixed)
  have hP1_sub : P1 ⊆ P := Finset.filter_subset _ _
  have hP1_nonempty : P1.Nonempty := by
    by_contra h
    have h' : P1 = ∅ := by simpa using h
    have h5 : (P1.card : ℝ) = 0 := by
      rw [h'] <;> simp
    rw [h5] at hcard
    have h6 : (P.card : ℝ) ≤ 0 := by linarith
    have h7 : P.card = 0 := by
      have h_nonpos : (P.card : ℝ) ≤ 0 := h6
      have h_nat : P.card ≤ 0 := by exact_mod_cast h_nonpos
      omega
    have h8 : ¬P.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h9
      have h10 : P = ∅ := by
        simpa [Finset.eq_empty_iff_forall_notMem] using h7
      rw [h10] at h9
      simp at h9
    exact h8 hP_nonempty
  have hP1_card : (P.card : ℝ) ≤ ((L : ℝ) + 1) * (P1.card : ℝ) := hcard
  let m1 := 2 ^ j_fixed
  refine ⟨m1, P1, hP1_sub, hP1_nonempty, ?_, ?_⟩
  · intro p hp
    have h_jp : j p = j_fixed := (Finset.mem_filter.mp hp).2
    have hp' : p ∈ P := (Finset.mem_filter.mp hp).1
    have h_band_p : (M : ℝ) / ((L : ℝ) + 1) ≤
        ∑ U ∈ (T p).image (coarseAnc' hnm),
          if 2^(j p) ≤ countInCoarse' hnm (T p) U ∧ countInCoarse' hnm (T p) U < 2^(j p + 1)
          then (countInCoarse' hnm (T p) U : ℝ) else 0 := hband p hp'
    rw [h_jp] at h_band_p
    have h_eq : (((T p).filter (fun t =>
          let c := countInCoarse' hnm (T p) (coarseAnc' hnm t)
          m1 ≤ c ∧ c < 2 * m1)).card : ℝ) =
        ∑ U ∈ (T p).image (coarseAnc' hnm),
          if m1 ≤ countInCoarse' hnm (T p) U ∧ countInCoarse' hnm (T p) U < 2 * m1
          then (countInCoarse' hnm (T p) U : ℝ) else 0 := by
      have h := filter_by_multiplicity_eq_sum' hnm (T p)
        (fun c => m1 ≤ c ∧ c < 2 * m1)
      exact_mod_cast h
    rw [h_eq]
    have h_final : (M : ℝ) / ((Nat.log 2 M + 2 : ℕ) : ℝ) ≤
        ∑ U ∈ (T p).image (coarseAnc' hnm),
          if m1 ≤ countInCoarse' hnm (T p) U ∧ countInCoarse' hnm (T p) U < 2 * m1
          then (countInCoarse' hnm (T p) U : ℝ) else 0 := by
      have h6 : (L : ℝ) + 1 = (Nat.log 2 M + 2 : ℕ) := by
        simp [L] <;> norm_cast <;> ring
      have h7 : ∀ (c : ℕ), (2^(j_fixed) ≤ c ∧ c < 2^(j_fixed + 1)) ↔ (m1 ≤ c ∧ c < 2 * m1) := by
        intro c
        have h_m1 : m1 = 2 ^ j_fixed := by rfl
        constructor
        · intro h
          have h1 : m1 ≤ c := by
            rw [h_m1]
            exact h.1
          have h2 : c < 2 * m1 := by
            rw [h_m1]
            have h3 : 2 * (2 ^ j_fixed) = 2 ^ (j_fixed + 1) := by
              simp [pow_succ] <;> ring
            rw [h3]
            exact h.2
          exact ⟨h1, h2⟩
        · intro h
          have h11 : m1 ≤ c := h.1
          have h12 : c < 2 * m1 := h.2
          have h1 : 2 ^ j_fixed ≤ c := by
            have h_eq : m1 = 2 ^ j_fixed := h_m1
            rw [h_eq] at h11
            exact h11
          have h2 : c < 2 ^ (j_fixed + 1) := by
            have h3 : 2 * m1 = 2 ^ (j_fixed + 1) := by
              simp [m1, pow_succ] <;> ring
            rw [h3] at h12
            exact h12
          exact ⟨h1, h2⟩
      have h_sum_eq : ∑ U ∈ (T p).image (coarseAnc' hnm),
          (if (2^(j_fixed) ≤ countInCoarse' hnm (T p) U ∧ countInCoarse' hnm (T p) U < 2^(j_fixed + 1))
           then (countInCoarse' hnm (T p) U : ℝ) else 0) =
        ∑ U ∈ (T p).image (coarseAnc' hnm),
          (if (m1 ≤ countInCoarse' hnm (T p) U ∧ countInCoarse' hnm (T p) U < 2 * m1)
           then (countInCoarse' hnm (T p) U : ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro U _
        let c := countInCoarse' hnm (T p) U
        have h_iff : (2^(j_fixed) ≤ c ∧ c < 2^(j_fixed + 1)) ↔ (m1 ≤ c ∧ c < 2 * m1) := h7 c
        split_ifs <;> tauto
      rw [h6] at h_band_p
      rw [h_sum_eq] at h_band_p
      exact h_band_p
    exact h_final
  · have h6 : (L : ℝ) + 1 = (Nat.log 2 M + 2 : ℕ) := by
      simp [L] <;> norm_cast <;> ring
    rw [h6] at hP1_card
    linarith
