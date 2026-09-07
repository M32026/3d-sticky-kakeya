import MyLeanRepo.Kakeya.Assouad.Definitions
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-!
# Multiscale cardinality uniform refinement

Given a finite set `A` and `T` levels of nested partitions, produce a subset
`A' ⊆ A` such that at every level, any two occupied cells have cardinalities
within a factor of two. Retention: `|A| ≤ (log_2 |A| + 1)^T · |A'|`.
-/

open Finset

namespace Kakeya.Assouad

-- Single-level dyadic uniformity lemma
lemma dyadic_uniformity_single_level {α : Type*} [DecidableEq α]
  (X : Finset α) (hX : X.Nonempty)
  (Q : Finset (Finset α))
  (h_disj : ∀ c₁ ∈ Q, ∀ c₂ ∈ Q, c₁ ≠ c₂ → Disjoint c₁ c₂)
  (h_cover : X ⊆ Finset.biUnion Q id) :
  ∃ (X' : Finset α) (kept : Finset (Finset α)),
    kept ⊆ Q ∧
    X' = Finset.biUnion kept (fun c => X ∩ c) ∧
    X'.Nonempty ∧
    (∀ c₁ ∈ Q, ∀ c₂ ∈ Q, (X' ∩ c₁).Nonempty → (X' ∩ c₂).Nonempty →
      (X' ∩ c₁).card ≤ 2 * (X' ∩ c₂).card) ∧
    (X'.card : ℝ) ≥ (X.card : ℝ) / (Nat.log 2 X.card + 1 : ℝ) := by
  let levelOf (c : Finset α) : ℕ := Nat.log 2 (X ∩ c).card
  let K := Finset.range (Nat.log 2 X.card + 1)

  have h_level_in_K : ∀ c ∈ Q, levelOf c ∈ K := by
    intro c _
    have h1 : (X ∩ c).card ≤ X.card := by
      apply card_le_card
      simp
    have h2 : levelOf c ≤ Nat.log 2 X.card := Nat.log_mono_right h1
    simp only [K, Finset.mem_range]
    <;> omega

  let classCells (k : ℕ) : Finset (Finset α) := Q.filter (fun c => levelOf c = k)
  let binTotal (k : ℕ) : ℕ := ∑ c ∈ classCells k, (X ∩ c).card

  have h_disj' : (Q : Set (Finset α)).PairwiseDisjoint (fun c => X ∩ c) := by
    intro c₁ hc₁ c₂ hc₂ hne
    have h : Disjoint c₁ c₂ := h_disj c₁ hc₁ c₂ hc₂ hne
    exact h.mono (by simp) (by simp)

  have h_sum_cells : ∑ c ∈ Q, (X ∩ c).card = X.card := by
    have h1 : X = Finset.biUnion Q (fun c => X ∩ c) := by
      ext x
      simp only [mem_biUnion, mem_inter]
      constructor
      · intro hx
        have h3 : x ∈ Finset.biUnion Q id := h_cover hx
        rcases mem_biUnion.mp h3 with ⟨c, hc, hxc⟩
        exact ⟨c, hc, ⟨hx, hxc⟩⟩
      · rintro ⟨c, _, ⟨hx, _⟩⟩; exact hx
    have h2 : (Finset.biUnion Q (fun c => X ∩ c)).card = ∑ c ∈ Q, (X ∩ c).card :=
      card_biUnion h_disj'
    rw [←h2, ←h1]

  have h_binTotal_eq : ∀ k, binTotal k = ∑ c ∈ Q, (if levelOf c = k then (X ∩ c).card else 0) := by
    intro k
    simp [binTotal, classCells, Finset.sum_ite]
    <;> rfl

  have h_sum : ∑ k ∈ K, binTotal k = X.card := by
    have h2 : ∑ k ∈ K, binTotal k = ∑ k ∈ K, ∑ c ∈ Q, (if levelOf c = k then (X ∩ c).card else 0) := by
      apply Finset.sum_congr rfl
      intro k _
      exact h_binTotal_eq k
    rw [h2]
    have h3 : ∑ k ∈ K, ∑ c ∈ Q, (if levelOf c = k then (X ∩ c).card else 0) =
        ∑ c ∈ Q, ∑ k ∈ K, (if levelOf c = k then (X ∩ c).card else 0) := by
      rw [Finset.sum_comm]
    rw [h3]
    have h4 : ∀ c ∈ Q, ∑ k ∈ K, (if levelOf c = k then (X ∩ c).card else 0) = (X ∩ c).card := by
      intro c hc
      have hbin : levelOf c ∈ K := h_level_in_K c hc
      simp [hbin]
      <;> omega
    rw [Finset.sum_congr rfl h4, h_sum_cells]

  have hK_nonempty : K.Nonempty := by
    simp [K] <;> omega

  rcases Finset.exists_max_image K binTotal hK_nonempty with ⟨k_opt, hk_opt, h_max⟩

  have hK_card : K.card = Nat.log 2 X.card + 1 := by simp [K]

  have h_pigeon : X.card ≤ K.card * binTotal k_opt := by
    calc
      X.card = ∑ k ∈ K, binTotal k := h_sum.symm
      _ ≤ ∑ k ∈ K, binTotal k_opt := Finset.sum_le_sum (fun j _ => h_max j ‹_›)
      _ = K.card * binTotal k_opt := by simp

  let kept := classCells k_opt
  let X' : Finset α := Finset.biUnion kept (fun c => X ∩ c)

  have h_kept_sub : kept ⊆ Q := filter_subset _ _

  have h_disj_kept : (kept : Set (Finset α)).PairwiseDisjoint (fun c => X ∩ c) := by
    intro c₁ hc₁ c₂ hc₂ hne
    have h1 : c₁ ∈ Q := (mem_filter.mp hc₁).1
    have h2 : c₂ ∈ Q := (mem_filter.mp hc₂).1
    have h : Disjoint c₁ c₂ := h_disj c₁ h1 c₂ h2 hne
    exact h.mono (by simp) (by simp)

  have hX'card : X'.card = binTotal k_opt := by
    rw [card_biUnion h_disj_kept] <;> rfl

  have hX'_nonempty : X'.Nonempty := by
    have h_pos : 0 < X'.card := by
      rw [hX'card]
      by_contra h
      have h' : binTotal k_opt = 0 := by omega
      have h_all : ∀ j ∈ K, binTotal j = 0 := by
        intro j hj
        have h_le : binTotal j ≤ binTotal k_opt := h_max j hj
        omega
      have h_sum0 : ∑ k ∈ K, binTotal k = 0 := by
        rw [Finset.sum_congr rfl h_all] <;> simp
      rw [h_sum] at h_sum0
      exact hX.card_pos.ne' h_sum0
    exact card_pos.mp h_pos

  have h_inter_kept : ∀ c ∈ kept, X' ∩ c = X ∩ c := by
    intro c hc
    have h1 : X ∩ c ⊆ X' := by
      intro x hx
      exact mem_biUnion.mpr ⟨c, hc, hx⟩
    have h2 : X' ⊆ X := by
      intro x hx
      rcases mem_biUnion.mp hx with ⟨d, _, hxd⟩
      exact (mem_inter.mp hxd).1
    ext x
    simp only [mem_inter]
    constructor
    · rintro ⟨hx1, hx2⟩; exact ⟨h2 hx1, hx2⟩
    · intro hx
      exact ⟨h1 (mem_inter.mpr hx), hx.2⟩

  have h_inter_not_kept : ∀ c ∈ Q, c ∉ kept → X' ∩ c = ∅ := by
    intro c hc hnk
    have h : ∀ x, x ∉ X' ∩ c := by
      intro x hx
      have h_x_in_X' : x ∈ X' := (mem_inter.mp hx).1
      have h_x_in_c : x ∈ c := (mem_inter.mp hx).2
      rcases mem_biUnion.mp h_x_in_X' with ⟨d, hd, hxd⟩
      have h_x_in_d : x ∈ d := (mem_inter.mp hxd).2
      have h_d_in_Q : d ∈ Q := (mem_filter.mp hd).1
      by_cases h_eq : d = c
      · rw [h_eq] at hd
        exact hnk hd
      · have h_disj : Disjoint d c := h_disj d h_d_in_Q c hc h_eq
        have h_contra : x ∈ d ∩ c := mem_inter.mpr ⟨h_x_in_d, h_x_in_c⟩
        have h_bot : x ∈ (∅ : Finset α) := h_disj.le_bot h_contra
        simp at h_bot
    by_contra hne
    have h7 : (X' ∩ c).Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
    rcases h7 with ⟨x, hx⟩
    exact h x hx

  have h_uniformity : ∀ c₁ ∈ Q, ∀ c₂ ∈ Q, (X' ∩ c₁).Nonempty → (X' ∩ c₂).Nonempty →
      (X' ∩ c₁).card ≤ 2 * (X' ∩ c₂).card := by
    intro c₁ hc1 c₂ hc2 hne1 hne2
    have h1 : c₁ ∈ kept := by
      by_contra h
      have h_empty : X' ∩ c₁ = ∅ := h_inter_not_kept c₁ hc1 h
      rw [h_empty] at hne1
      simp at hne1
    have h2 : c₂ ∈ kept := by
      by_contra h
      have h_empty : X' ∩ c₂ = ∅ := h_inter_not_kept c₂ hc2 h
      rw [h_empty] at hne2
      simp at hne2
    have h_eq1 : X' ∩ c₁ = X ∩ c₁ := h_inter_kept c₁ h1
    have h_eq2 : X' ∩ c₂ = X ∩ c₂ := h_inter_kept c₂ h2
    have h_bin1 : levelOf c₁ = k_opt := (mem_filter.mp h1).2
    have h_bin2 : levelOf c₂ = k_opt := (mem_filter.mp h2).2
    have h_pos1 : 0 < (X ∩ c₁).card := by
      rw [←h_eq1]; exact hne1.card_pos
    have h_pos2 : 0 < (X ∩ c₂).card := by
      rw [←h_eq2]; exact hne2.card_pos
    have h_bounds1 : 2 ^ k_opt ≤ (X ∩ c₁).card ∧ (X ∩ c₁).card < 2 ^ (k_opt + 1) := by
      have h_log_eq : Nat.log 2 (X ∩ c₁).card = k_opt := by
        simpa [levelOf] using h_bin1
      exact (Nat.log_eq_iff (Or.inr ⟨by norm_num, h_pos1.ne'⟩)).mp h_log_eq
    have h_bounds2 : 2 ^ k_opt ≤ (X ∩ c₂).card ∧ (X ∩ c₂).card < 2 ^ (k_opt + 1) := by
      have h_log_eq : Nat.log 2 (X ∩ c₂).card = k_opt := by
        simpa [levelOf] using h_bin2
      exact (Nat.log_eq_iff (Or.inr ⟨by norm_num, h_pos2.ne'⟩)).mp h_log_eq
    rw [h_eq1, h_eq2]
    omega

  have h_retention : (X'.card : ℝ) ≥ (X.card : ℝ) / (Nat.log 2 X.card + 1 : ℝ) := by
    have h' : X.card ≤ K.card * X'.card := by
      have h_pigeon2 : X.card ≤ K.card * binTotal k_opt := h_pigeon
      rw [←hX'card] at h_pigeon2
      exact h_pigeon2
    have h : X.card ≤ (Nat.log 2 X.card + 1) * X'.card := by
      rw [hK_card] at h'
      exact h'
    have h_pos : (0 : ℝ) < (Nat.log 2 X.card + 1 : ℝ) := by positivity
    have h_goal : (Nat.log 2 X.card + 1 : ℝ) * (X'.card : ℝ) ≥ (X.card : ℝ) := by
      exact_mod_cast h
    have h_final : (X.card : ℝ) / (Nat.log 2 X.card + 1 : ℝ) ≤ (X'.card : ℝ) := by
      calc
        (X.card : ℝ) / (Nat.log 2 X.card + 1 : ℝ)
          ≤ ((Nat.log 2 X.card + 1 : ℝ) * (X'.card : ℝ)) / (Nat.log 2 X.card + 1 : ℝ) := by gcongr
        _ = (X'.card : ℝ) := by
          field_simp [h_pos.ne'] <;> ring
    exact h_final

  exact ⟨X', kept, h_kept_sub, rfl, hX'_nonempty, h_uniformity, h_retention⟩

-- Ancestor chain lemma for nested partitions
lemma find_ancestor {α : Type*} [DecidableEq α]
  (T : ℕ) (P : ℕ → Finset (Finset α))
  (h_refine : ∀ k, k + 1 < T → ∀ c ∈ P (k + 1), ∃ p ∈ P k, c ⊆ p)
  {k j : ℕ} (hkj : k ≤ j) (hjt : j < T) :
  ∀ c ∈ P j, ∃ p ∈ P k, c ⊆ p := by
  induction j with
  | zero =>
    have h_k0 : k = 0 := by omega
    subst h_k0
    intro c hc
    exact ⟨c, hc, rfl.subset⟩
  | succ j ih =>
    by_cases h : k ≤ j
    · intro c hc
      rcases h_refine j (by omega) c hc with ⟨p, hp, hsub⟩
      rcases ih h (by omega) p hp with ⟨p', hp', hsub'⟩
      exact ⟨p', hp', hsub.trans hsub'⟩
    · have h_kj : k = j + 1 := by omega
      subst h_kj
      intro c hc
      exact ⟨c, hc, rfl.subset⟩

-- Multiscale induction: process n levels from T-n to T-1
lemma multiscale_uniformity_induction {α : Type*} [DecidableEq α]
  (A : Finset α) (hA : A.Nonempty) (T : ℕ) (P : ℕ → Finset (Finset α))
  (h_partition : ∀ k < T,
    (∀ c ∈ P k, c ⊆ A) ∧
    (∀ c₁ ∈ P k, ∀ c₂ ∈ P k, c₁ ≠ c₂ → Disjoint c₁ c₂) ∧
    A ⊆ Finset.biUnion (P k) id)
  (h_refine : ∀ k, k + 1 < T → ∀ c ∈ P (k + 1), ∃ p ∈ P k, c ⊆ p)
  (L : ℕ) (hL : L = Nat.log 2 A.card + 1) :
  ∀ n : ℕ, n ≤ T →
  ∃ (A' : Finset α), A'.Nonempty ∧ A' ⊆ A ∧
    (∀ j, T - n ≤ j → j < T →
      ∀ c₁ ∈ P j, ∀ c₂ ∈ P j, (A' ∩ c₁).Nonempty → (A' ∩ c₂).Nonempty →
        (A' ∩ c₁).card ≤ 2 * (A' ∩ c₂).card) ∧
    (A.card : ℝ) ≤ (L : ℝ)^n * (A'.card : ℝ) := by
  intro n hn
  induction n with
  | zero =>
    refine ⟨A, hA, rfl.subset, ?_, ?_⟩
    · intro j hj1 hj2
      exfalso; omega
    · simp [hL] <;> norm_cast
  | succ n ih =>
    have h_n_le_T : n ≤ T := by linarith
    rcases ih h_n_le_T with ⟨A'', hA''_nonempty, hA''_sub, hA''_unif, hA''_ret⟩

    let k := T - (n + 1)
    have h_k_lt_T : k < T := by omega

    let Q := P k
    have hQ_disj : ∀ c₁ ∈ Q, ∀ c₂ ∈ Q, c₁ ≠ c₂ → Disjoint c₁ c₂ :=
      (h_partition k h_k_lt_T).2.1
    have hQ_cover : A'' ⊆ Finset.biUnion Q id :=
      Subset.trans hA''_sub (h_partition k h_k_lt_T).2.2

    rcases dyadic_uniformity_single_level A'' hA''_nonempty Q hQ_disj hQ_cover with
      ⟨A', kept, h_kept_sub_Q, hX'_def, hA'_nonempty, hA'_unif_k, hA'_ret⟩

    have hA'_sub_A'' : A' ⊆ A'' := by
      rw [hX'_def]
      intro x hx
      rcases mem_biUnion.mp hx with ⟨c, _, hxc⟩
      exact (mem_inter.mp hxc).1

    have hA'_sub_A : A' ⊆ A := hA'_sub_A''.trans hA''_sub

    -- Retention
    have h_log_mono : Nat.log 2 A''.card ≤ Nat.log 2 A.card :=
      Nat.log_mono_right (card_le_card hA''_sub)
    have hL'' : Nat.log 2 A''.card + 1 ≤ L := by omega

    have h_retention : (A''.card : ℝ) ≤ (L : ℝ) * (A'.card : ℝ) := by
      have h1 : (A'.card : ℝ) ≥ (A''.card : ℝ) / (Nat.log 2 A''.card + 1 : ℝ) := hA'_ret
      have h2 : 0 < (Nat.log 2 A''.card + 1 : ℝ) := by positivity
      have h3 : (A''.card : ℝ) ≤ (Nat.log 2 A''.card + 1 : ℝ) * (A'.card : ℝ) := by
        calc
          (A''.card : ℝ)
            ≤ (Nat.log 2 A''.card + 1 : ℝ) * ((A''.card : ℝ) / (Nat.log 2 A''.card + 1 : ℝ)) := by
              field_simp [h2.ne'] <;> ring_nf <;> nlinarith
          _ ≤ (Nat.log 2 A''.card + 1 : ℝ) * (A'.card : ℝ) := by gcongr
      calc
        (A''.card : ℝ) ≤ (Nat.log 2 A''.card + 1 : ℝ) * (A'.card : ℝ) := h3
        _ ≤ (L : ℝ) * (A'.card : ℝ) := by
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hL'') (by positivity)

    have h_main_retention : (A.card : ℝ) ≤ (L : ℝ)^(n + 1) * (A'.card : ℝ) := by
      calc
        (A.card : ℝ) ≤ (L : ℝ)^n * (A''.card : ℝ) := hA''_ret
        _ ≤ (L : ℝ)^n * ((L : ℝ) * (A'.card : ℝ)) := by gcongr
        _ = (L : ℝ)^(n + 1) * (A'.card : ℝ) := by ring

    -- Ancestor lemma specialized to k
    have h_ancestor : ∀ (j : ℕ), k ≤ j → j < T → ∀ c ∈ P j, ∃ p ∈ P k, c ⊆ p :=
      fun j hkj hjt => find_ancestor T P h_refine hkj hjt

    -- Preservation: if ancestor p ∈ kept, then A' ∩ c = A'' ∩ c
    have h_preservation : ∀ (j : ℕ), k < j → j < T →
        ∀ (c : Finset α), c ∈ P j →
          (∃ (p : Finset α), p ∈ P k ∧ p ∈ kept ∧ c ⊆ p) →
            A' ∩ c = A'' ∩ c := by
      intro j _ _ c hc ⟨p, _, hpkept, hsub⟩
      have h1 : A'' ∩ c ⊆ A' := by
        intro x hx
        have h_x_in_A'' : x ∈ A'' := (mem_inter.mp hx).1
        have h_x_in_p : x ∈ p := hsub (mem_inter.mp hx).2
        have h_x_in_A''interp : x ∈ A'' ∩ p := mem_inter.mpr ⟨h_x_in_A'', h_x_in_p⟩
        rw [hX'_def]
        exact mem_biUnion.mpr ⟨p, hpkept, h_x_in_A''interp⟩
      have h2 : A' ⊆ A'' := hA'_sub_A''
      ext x
      simp only [mem_inter]
      constructor
      · rintro ⟨hx1, hx2⟩; exact ⟨h2 hx1, hx2⟩
      · intro hx
        exact ⟨h1 (mem_inter.mpr hx), hx.2⟩

    -- Emptiness: if ancestor p ∉ kept, then A' ∩ c = ∅
    have h_emptiness : ∀ (j : ℕ), k < j → j < T →
        ∀ (c : Finset α), c ∈ P j →
          (∃ (p : Finset α), p ∈ P k ∧ p ∉ kept ∧ c ⊆ p) →
            A' ∩ c = ∅ := by
      intro j _ _ c hc ⟨p, hpQ, hpnotkept, hsub⟩
      have h : ∀ x, x ∉ A' ∩ c := by
        intro x hx
        have h_x_in_A' : x ∈ A' := (mem_inter.mp hx).1
        have h_x_in_c : x ∈ c := (mem_inter.mp hx).2
        have h_x_in_p : x ∈ p := hsub h_x_in_c
        rw [hX'_def] at h_x_in_A'
        rcases mem_biUnion.mp h_x_in_A' with ⟨d, hdkept, hxd⟩
        have h_x_in_d : x ∈ d := (mem_inter.mp hxd).2
        have h_d_in_Q : d ∈ P k := h_kept_sub_Q hdkept
        by_cases h_eq : d = p
        · rw [h_eq] at hdkept
          exact hpnotkept hdkept
        · have h_disj : Disjoint d p := hQ_disj d h_d_in_Q p hpQ h_eq
          have h_contra : x ∈ d ∩ p := mem_inter.mpr ⟨h_x_in_d, h_x_in_p⟩
          have h_bot : x ∈ (∅ : Finset α) := h_disj.le_bot h_contra
          simp at h_bot
      by_contra hne
      have h7 : (A' ∩ c).Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
      rcases h7 with ⟨x, hx⟩
      exact h x hx

    -- Uniformity at finer levels j > k
    have h_unif_finer : ∀ (j : ℕ), k < j → j < T →
        ∀ c₁ ∈ P j, ∀ c₂ ∈ P j, (A' ∩ c₁).Nonempty → (A' ∩ c₂).Nonempty →
          (A' ∩ c₁).card ≤ 2 * (A' ∩ c₂).card := by
      intro j hkj hjt c₁ hc1 c₂ hc2 hne1 hne2
      rcases h_ancestor j (by omega) hjt c₁ hc1 with ⟨p1, hp1Q, hsub1⟩
      rcases h_ancestor j (by omega) hjt c₂ hc2 with ⟨p2, hp2Q, hsub2⟩

      have h_p1_kept : p1 ∈ kept := by
        by_contra h
        have h_empty : A' ∩ c₁ = ∅ := h_emptiness j hkj hjt c₁ hc1 ⟨p1, hp1Q, h, hsub1⟩
        rw [h_empty] at hne1
        simp at hne1
      have h_p2_kept : p2 ∈ kept := by
        by_contra h
        have h_empty : A' ∩ c₂ = ∅ := h_emptiness j hkj hjt c₂ hc2 ⟨p2, hp2Q, h, hsub2⟩
        rw [h_empty] at hne2
        simp at hne2

      have h_eq1 : A' ∩ c₁ = A'' ∩ c₁ :=
        h_preservation j hkj hjt c₁ hc1 ⟨p1, hp1Q, h_p1_kept, hsub1⟩
      have h_eq2 : A' ∩ c₂ = A'' ∩ c₂ :=
        h_preservation j hkj hjt c₂ hc2 ⟨p2, hp2Q, h_p2_kept, hsub2⟩

      have h_ne1' : (A'' ∩ c₁).Nonempty := by
        rw [←h_eq1]; exact hne1
      have h_ne2' : (A'' ∩ c₂).Nonempty := by
        rw [←h_eq2]; exact hne2

      have h_ih_unif := hA''_unif j (by omega) hjt c₁ hc1 c₂ hc2 h_ne1' h_ne2'
      rw [h_eq1, h_eq2]
      exact h_ih_unif

    -- Combine uniformity for all j ≥ k
    have h_unif_all : ∀ j, k ≤ j → j < T →
        ∀ c₁ ∈ P j, ∀ c₂ ∈ P j, (A' ∩ c₁).Nonempty → (A' ∩ c₂).Nonempty →
          (A' ∩ c₁).card ≤ 2 * (A' ∩ c₂).card := by
      intro j hkj hjt
      by_cases h : k = j
      · have h' : j = k := h.symm
        rw [h']
        exact hA'_unif_k
      · have h' : k < j := by omega
        exact h_unif_finer j h' hjt

    refine ⟨A', hA'_nonempty, hA'_sub_A, ?_, h_main_retention⟩
    · intro j hj1 hj2
      have h_k_le_j : k ≤ j := by
        simp only [k] at * <;> omega
      exact h_unif_all j h_k_le_j hj2

end Kakeya.Assouad
