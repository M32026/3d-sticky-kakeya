/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Density
public import Kakeya.Frostman
public import Kakeya.Tube.Basic
public import Kakeya.Tube.EssentiallyDistinctReduction
public import Kakeya.Tube.IsUniformAtScale
public import Kakeya.Uniform.Tree
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Pruning a tube family into a uniform one

The construction behind `Tube.exists_uniformTubeSet_subfamily`: a multi-level dyadic
pigeonhole prunes an arbitrary family until every parent of the multiscale tube tree carries
comparably many leaves, which is exactly GWZ Definition 2.1(iii).  The output is a
`Tube.IsUniformAtScale` witness at every scale of the chain.

`Tube.refineToEssDistinctUniform` at the end is the packaged form the sticky-Kakeya argument
consumes.
-/

@[expose] public section


open MeasureTheory

namespace Tube

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E]
  {ι : Type*}

section UniformConstruction

open Classical in
/-- Multi-level dyadic pigeonhole.  Iteratively prunes `s` by dyadic pigeonhole on the class sizes
at levels `K-1, …, 1` (bottom-up), each pruning losing a factor `B = ⌊log₂|s|⌋ + 1`, for a total
loss `B^(K-1)`.  In the result, for every level `1 ≤ k < K` and every `i ∈ S`, the level-`k` class
size of `i` lies in `[N k, 2 * N k)` for a single constant `N k`. -/
private lemma dyadic_pigeonhole_multi
    (s : Finset ι) (hs : s.Nonempty)
    (K : ℕ) (f : ℕ → ι → ι)
    (h_nested : ∀ k, k + 1 < K → ∀ ⦃i j : ι⦄, i ∈ s → j ∈ s →
      f (k + 1) i = f (k + 1) j → f k i = f k j) :
    ∃ (S : Finset ι) (N : ℕ → ℕ),
      S ⊆ s ∧
      S.Nonempty ∧
      (s.card : ℝ) / ((⌊Real.logb 2 (s.card : ℝ)⌋₊ + 1 : ℝ) ^ (K - 1))
        ≤ (S.card : ℝ) ∧
      (∀ k, 1 ≤ k → k < K → ∀ i ∈ S,
        N k ≤ (S.filter (fun i' => f k i' = f k i)).card ∧
        (S.filter (fun i' => f k i' = f k i)).card < 2 * N k) := by
  classical
  suffices h : ∀ K : ℕ, ∀ (s : Finset ι), s.Nonempty → ∀ (f : ℕ → ι → ι),
      (∀ k, k + 1 < K → ∀ ⦃i j : ι⦄, i ∈ s → j ∈ s →
        f (k + 1) i = f (k + 1) j → f k i = f k j) →
      ∃ (S : Finset ι) (N : ℕ → ℕ),
        S ⊆ s ∧
        S.Nonempty ∧
        (s.card : ℝ) / ((⌊Real.logb 2 (s.card : ℝ)⌋₊ + 1 : ℝ) ^ (K - 1))
          ≤ (S.card : ℝ) ∧
        (∀ k, 1 ≤ k → k < K → ∀ i ∈ S,
          N k ≤ (S.filter (fun i' => f k i' = f k i)).card ∧
          (S.filter (fun i' => f k i' = f k i)).card < 2 * N k) ∧
        (1 ≤ K → ∀ ⦃i⦄, i ∈ S → ∀ ⦃i'⦄, i' ∈ s →
          f (K - 1) i' = f (K - 1) i → i' ∈ S) by
    obtain ⟨S, N, h1, h2, h3, h4, _⟩ := h K s hs f h_nested
    exact ⟨S, N, h1, h2, h3, h4⟩
  clear hs h_nested s K f
  intro K
  induction K with
  | zero =>
    intro s hs f _
    refine ⟨s, fun _ => 0, Finset.Subset.refl _, hs, ?_, ?_, ?_⟩
    · simp
    · intro k _ hk
      exact absurd hk (Nat.not_lt_zero _)
    · intro hK
      exact absurd hK (Nat.not_succ_le_zero _)
  | succ K' ih =>
    intro s hs f h_nested
    obtain ⟨j_max, S₀, hS₀_sub, hS₀_band, hS₀_complete, hS₀_card, _⟩ :=
      Nat.dyadic_pigeonhole_fibre s (f K')
    by_cases hK'_zero : K' = 0
    · subst hK'_zero
      refine ⟨s, fun _ => 0, Finset.Subset.refl _, hs, ?_, ?_, ?_⟩
      · simp
      · intro k hk1 hk2
        interval_cases k
      · intro _ i hi i' hi' _; exact hi'
    have hK'_pos : 0 < K' := Nat.pos_of_ne_zero hK'_zero
    set sR : ℝ := (s.card : ℝ)
    set B_s : ℕ := ⌊Real.logb 2 sR⌋₊ + 1
    have hs_pos : 0 < s.card := Finset.card_pos.mpr hs
    have hB_s_pos : 0 < B_s := by change 0 < ⌊Real.logb 2 sR⌋₊ + 1; omega
    have hsR_pos : (0 : ℝ) < sR := by change (0 : ℝ) < (s.card : ℝ); exact_mod_cast hs_pos
    have hB_s_R_pos : (0 : ℝ) < (B_s : ℝ) := by exact_mod_cast hB_s_pos
    have hS₀_pos : 0 < S₀.card := by
      by_contra h
      have hzero : S₀.card = 0 := by omega
      have hS₀_R_zero : (S₀.card : ℝ) = 0 := by exact_mod_cast hzero
      have : (s.card : ℝ) / (B_s : ℝ) ≤ 0 := by
        have h0 : ((⌊Real.logb 2 sR⌋₊ : ℝ) + 1) = (B_s : ℝ) := by
          change ((⌊Real.logb 2 sR⌋₊ : ℝ) + 1) = ((⌊Real.logb 2 sR⌋₊ + 1 : ℕ) : ℝ)
          push_cast; ring
        rw [h0] at hS₀_card
        rw [hS₀_R_zero] at hS₀_card
        exact hS₀_card
      have hposdiv : (0 : ℝ) < (s.card : ℝ) / (B_s : ℝ) :=
        div_pos (by exact_mod_cast hs_pos) hB_s_R_pos
      linarith
    have hS₀_ne : S₀.Nonempty := Finset.card_pos.mp hS₀_pos
    have h_nested_S₀ : ∀ k, k + 1 < K' → ∀ ⦃i j : ι⦄, i ∈ S₀ → j ∈ S₀ →
        f (k + 1) i = f (k + 1) j → f k i = f k j := by
      intro k hk i j hi hj hij
      have hi_s : i ∈ s := hS₀_sub hi
      have hj_s : j ∈ s := hS₀_sub hj
      exact h_nested k (by omega) hi_s hj_s hij
    obtain ⟨S₁, N₀, hS₁_sub, hS₁_ne, hS₁_card, hS₁_band, hS₁_closure⟩ :=
      ih S₀ hS₀_ne f h_nested_S₀
    refine ⟨S₁, Function.update N₀ K' (2 ^ j_max), ?_, hS₁_ne, ?_, ?_, ?_⟩
    · exact hS₁_sub.trans hS₀_sub
    · set sR₀ : ℝ := (S₀.card : ℝ)
      set B_S₀ : ℕ := ⌊Real.logb 2 sR₀⌋₊ + 1
      have hB_S₀_pos : 0 < B_S₀ := by change 0 < ⌊Real.logb 2 sR₀⌋₊ + 1; omega
      have hB_S₀_R_pos : (0 : ℝ) < (B_S₀ : ℝ) := by exact_mod_cast hB_S₀_pos
      have hsR₀_pos : (0 : ℝ) < sR₀ := by
        change (0 : ℝ) < (S₀.card : ℝ); exact_mod_cast hS₀_pos
      have hB_le : (B_S₀ : ℝ) ≤ (B_s : ℝ) := by
        change ((⌊Real.logb 2 sR₀⌋₊ + 1 : ℕ) : ℝ) ≤ ((⌊Real.logb 2 sR⌋₊ + 1 : ℕ) : ℝ)
        push_cast
        have hsub : sR₀ ≤ sR := by
          change (S₀.card : ℝ) ≤ (s.card : ℝ)
          exact_mod_cast Finset.card_le_card hS₀_sub
        have hlog : Real.logb 2 sR₀ ≤ Real.logb 2 sR := by
          have h1lt2 : (1 : ℝ) < 2 := by norm_num
          exact (Real.logb_le_logb h1lt2 hsR₀_pos hsR_pos).mpr hsub
        have hfloor : (⌊Real.logb 2 sR₀⌋₊ : ℝ) ≤ (⌊Real.logb 2 sR⌋₊ : ℝ) := by
          exact_mod_cast Nat.floor_mono hlog
        linarith
      have hB_S₀_pow_le : (B_S₀ : ℝ) ^ (K' - 1) ≤ (B_s : ℝ) ^ (K' - 1) :=
        pow_le_pow_left₀ (by positivity) hB_le _
      have h_outer_bound : (s.card : ℝ) / (B_s : ℝ) ≤ (S₀.card : ℝ) := by
        have h0 : ((⌊Real.logb 2 sR⌋₊ : ℝ) + 1) = (B_s : ℝ) := by
          change ((⌊Real.logb 2 sR⌋₊ : ℝ) + 1) = ((⌊Real.logb 2 sR⌋₊ + 1 : ℕ) : ℝ)
          push_cast; ring
        rw [h0] at hS₀_card
        exact hS₀_card
      have h_inner_bound : (S₀.card : ℝ) / (B_S₀ : ℝ) ^ (K' - 1) ≤ (S₁.card : ℝ) := by
        have h0 : ((⌊Real.logb 2 sR₀⌋₊ : ℝ) + 1) = (B_S₀ : ℝ) := by
          change ((⌊Real.logb 2 sR₀⌋₊ : ℝ) + 1) = ((⌊Real.logb 2 sR₀⌋₊ + 1 : ℕ) : ℝ)
          push_cast; ring
        rw [h0] at hS₁_card
        exact hS₁_card
      have h_eq : (K' + 1 - 1 : ℕ) = K' := by omega
      rw [h_eq]
      have h_split : (B_s : ℝ) ^ K' = (B_s : ℝ) * (B_s : ℝ) ^ (K' - 1) := by
        have hK'_eq : K' = (K' - 1) + 1 := by omega
        conv_lhs => rw [hK'_eq]
        rw [pow_succ]
        ring
      have h0' : ((⌊Real.logb 2 sR⌋₊ : ℝ) + 1) = (B_s : ℝ) := by
        change ((⌊Real.logb 2 sR⌋₊ : ℝ) + 1) = ((⌊Real.logb 2 sR⌋₊ + 1 : ℕ) : ℝ)
        push_cast; ring
      rw [h0', h_split]
      have hB_s_pow_pos : (0 : ℝ) < (B_s : ℝ) ^ (K' - 1) :=
        pow_pos hB_s_R_pos _
      rw [div_mul_eq_div_div, div_le_iff₀ hB_s_pow_pos]
      calc (s.card : ℝ) / (B_s : ℝ)
          ≤ (S₀.card : ℝ) := h_outer_bound
        _ = (S₀.card : ℝ) / (B_S₀ : ℝ) ^ (K' - 1) * (B_S₀ : ℝ) ^ (K' - 1) := by
            rw [div_mul_cancel₀]
            exact (pow_pos hB_S₀_R_pos _).ne'
        _ ≤ (S₁.card : ℝ) * (B_S₀ : ℝ) ^ (K' - 1) := by
            exact mul_le_mul_of_nonneg_right h_inner_bound (by positivity)
        _ ≤ (S₁.card : ℝ) * (B_s : ℝ) ^ (K' - 1) := by
            exact mul_le_mul_of_nonneg_left hB_S₀_pow_le (by positivity)
    · intro k hk1 hk2 i hi
      have hk2' : k < K' + 1 := hk2
      by_cases hk_eq : k = K'
      · rw [hk_eq]
        rw [hk_eq] at hk1
        simp only [Function.update_self]
        have h_i_s : i ∈ s := (hS₁_sub.trans hS₀_sub) hi
        have hi_S₀ : i ∈ S₀ := hS₁_sub hi
        have h_outer_band_i := hS₀_band i hi_S₀
        have h_closure : ∀ i' ∈ s, f K' i' = f K' i → i' ∈ S₁ := by
          intro i' hi' hii'
          have h_class_eq : (s.filter (fun i'' => f K' i'' = f K' i')) =
              (s.filter (fun i'' => f K' i'' = f K' i)) := by
            apply Finset.filter_congr
            intro x _
            rw [hii']
          have h_i'_S₀ : i' ∈ S₀ := by
            apply hS₀_complete i' hi'
            rw [h_class_eq]
            exact h_outer_band_i
          have h_nest : f (K' - 1) i' = f (K' - 1) i := by
            have hKK : K' - 1 + 1 < K' + 1 := by omega
            have hKK_eq : K' - 1 + 1 = K' := by omega
            have := h_nested (K' - 1) hKK hi' h_i_s
            rw [hKK_eq] at this
            exact this hii'
          exact hS₁_closure hK'_pos hi h_i'_S₀ h_nest
        have h_filter_eq : (S₁.filter (fun i' => f K' i' = f K' i)).card =
            (s.filter (fun i' => f K' i' = f K' i)).card := by
          congr 1
          apply Finset.ext
          intro x
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨hx, hfx⟩
            exact ⟨(hS₁_sub.trans hS₀_sub) hx, hfx⟩
          · rintro ⟨hx, hfx⟩
            exact ⟨h_closure x hx hfx, hfx⟩
        rw [h_filter_eq]
        constructor
        · exact h_outer_band_i.1
        · have h_two : 2 ^ (j_max + 1) = 2 * 2 ^ j_max := by ring
          rw [h_two] at h_outer_band_i
          exact h_outer_band_i.2
      · have hk_lt : k < K' := by omega
        have hN_eq : Function.update N₀ K' (2 ^ j_max) k = N₀ k := by
          rw [Function.update_of_ne]
          omega
        rw [hN_eq]
        exact hS₁_band k hk1 hk_lt i hi
    · intro _ i hi i' hi' h_eq
      have hi_S₀ : i ∈ S₀ := hS₁_sub hi
      have h_i_s : i ∈ s := hS₀_sub hi_S₀
      have h_outer_band_i := hS₀_band i hi_S₀
      have h_class_eq : (s.filter (fun i'' => f ((K' + 1) - 1) i'' = f ((K' + 1) - 1) i')) =
          (s.filter (fun i'' => f ((K' + 1) - 1) i'' = f ((K' + 1) - 1) i)) := by
        apply Finset.filter_congr
        intro x _
        rw [h_eq]
      have hKK1 : (K' + 1) - 1 = K' := by omega
      rw [hKK1] at h_eq h_class_eq
      have h_i'_S₀ : i' ∈ S₀ := by
        apply hS₀_complete i' hi'
        rw [h_class_eq]
        exact h_outer_band_i
      have h_nest : f (K' - 1) i' = f (K' - 1) i := by
        have hKK : K' - 1 + 1 < K' + 1 := by omega
        have hKK_eq : K' - 1 + 1 = K' := by omega
        have := h_nested (K' - 1) hKK hi' h_i_s
        rw [hKK_eq] at this
        exact this h_eq
      exact hS₁_closure hK'_pos hi h_i'_S₀ h_nest

/-! ### Lemma A — pure combinatorial nested-partition dyadic pigeonhole

Inputs: a finite set `s`, a tower of "parent" finsets `parent 0, …, parent M`
together with an assignment `assign k : ι → ι` describing, for each `i ∈ s`,
its level-`k` ancestor.  The geometric content (tubes, scales, ED) does not
enter this lemma: the only data used are the nesting condition `h_nested`
("level `k+1` refines level `k`"), the single-root condition `h_root`
(`parent 0 = {root}`), and the leaf condition `h_top` (`assign M = id`).

This is the rigorous form of Lemma A in the blueprint (Step 2,
"bottom-up dyadic pigeonholing"), and contains the **entire pigeonhole
argument** behind the `B^{M-1}` loss.  No bridge, no tubes, no `Tube.C_*`.
-/

open Classical in
/-- **Lemma A.**  Pure combinatorial nested-partition dyadic pigeonhole.  Given a tower of nested
parent families with tree coherence, a single root and self-assignment at the leaves, bottom-up
multi-level dyadic pigeonholing produces `s' ⊆ s`, per-level constants `N k` and a pruned family
`parent' k ⊆ parent k` in which every class size in `s'` lies in `[1, 2 * N k)`, with the bound
`|s| / (⌊log₂ |s|⌋ + 1)^(M-1) ≤ |s'|`. -/
lemma exists_pruned_subset
    (s : Finset ι) (M : ℕ)
    (parent : ℕ → Finset ι) (assign : ℕ → ι → ι) (root : ι)
    (h_assign_mem : ∀ k ≤ M, ∀ ⦃i⦄, i ∈ s → assign k i ∈ parent k)
    (h_top : ∀ ⦃i⦄, i ∈ s → assign M i = i)
    (h_root : parent 0 = {root})
    (h_nested : ∀ k, k < M → ∀ ⦃i j⦄, i ∈ s → j ∈ s →
      assign (k + 1) i = assign (k + 1) j → assign k i = assign k j) :
    ∃ (s' : Finset ι) (N : ℕ → ℕ) (parent' : ℕ → Finset ι),
      s' ⊆ s ∧
      (s.card : ℝ) /
        ((⌊Real.logb 2 (s.card : ℝ)⌋₊ + 1 : ℝ) ^ (M - 1)) ≤ (s'.card : ℝ) ∧
      (∀ k ≤ M, parent' k ⊆ parent k) ∧
      (∀ k ≤ M, ∀ ⦃i⦄, i ∈ s' → assign k i ∈ parent' k) ∧
      (∀ k ≤ M, ∀ v ∈ parent' k,
        0 < (s'.filter (fun i => assign k i = v)).card) ∧
      (∀ k ≤ M, ∀ v ∈ parent' k,
        N k ≤ (s'.filter (fun i => assign k i = v)).card ∧
        (s'.filter (fun i => assign k i = v)).card < 2 * N k) := by
  classical
  by_cases hs0 : s.card = 0
  · refine ⟨∅, fun _ => 0, fun _ => ∅,
            Finset.empty_subset _, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hs0]
    · intro k _; exact Finset.empty_subset _
    · intro k _ i hi; simp at hi
    · intro k _ v hv; simp at hv
    · intro k _ v hv; simp at hv
  have hs_pos : 0 < s.card := Nat.pos_of_ne_zero hs0
  have hs_ne : s.Nonempty := Finset.card_pos.mp hs_pos
  have hi0_ex : ∃ i, i ∈ s := hs_ne
  obtain ⟨i0, hi0⟩ := hi0_ex
  set sR : ℝ := (s.card : ℝ) with hsR_def
  set B : ℕ := ⌊Real.logb 2 sR⌋₊ + 1 with hBdef
  have hB_pos : 0 < B := by omega
  have hBR_pos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB_pos
  have hsR_pos : (0 : ℝ) < sR := by
    rw [hsR_def]; exact_mod_cast hs_pos
  by_cases hM_le : M ≤ 1
  · refine ⟨s, fun k => if k = 0 then s.card else 1,
            fun k => s.image (assign k), subset_refl _,
            ?_, ?_, ?_, ?_, ?_⟩
    · have hMm1 : M - 1 = 0 := by omega
      rw [hMm1, pow_zero, div_one]
    · intro k hk v hv
      rw [Finset.mem_image] at hv
      obtain ⟨i, hi_in, rfl⟩ := hv
      exact h_assign_mem k hk hi_in
    · intro k _ i hi
      exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
    · intro k _ v hv
      rw [Finset.mem_image] at hv
      obtain ⟨i, hi_in, hi_eq⟩ := hv
      exact Finset.card_pos.mpr ⟨i,
        by rw [Finset.mem_filter]; exact ⟨hi_in, hi_eq⟩⟩
    · intro k hk v hv
      rw [Finset.mem_image] at hv
      obtain ⟨i, hi_in, hi_eq⟩ := hv
      by_cases hk0 : k = 0
      · subst hk0
        have hroot_eq : assign 0 i = root := by
          have := h_assign_mem 0 (Nat.zero_le _) hi_in
          rw [h_root, Finset.mem_singleton] at this; exact this
        have hv_root : v = root := hroot_eq ▸ hi_eq.symm
        have hfilter_eq : s.filter (fun j => assign 0 j = v) = s := by
          apply Finset.filter_eq_self.mpr
          intro j hj
          have := h_assign_mem 0 (Nat.zero_le _) hj
          rw [h_root, Finset.mem_singleton] at this
          rw [this, hv_root]
        rw [hfilter_eq]
        simp only [↓reduceIte]
        omega
      · have hkM : k = M := by omega
        have hi_in_filter : i ∈ s.filter (fun j => assign k j = v) := by
          rw [Finset.mem_filter]; exact ⟨hi_in, hi_eq⟩
        have hcard_le_1 : (s.filter (fun j => assign k j = v)).card ≤ 1 := by
          apply Finset.card_le_one.mpr
          intro a ha b hb
          rw [Finset.mem_filter] at ha hb
          rw [hkM] at ha hb
          have ha' := h_top ha.1
          have hb' := h_top hb.1
          rw [ha'] at ha
          rw [hb'] at hb
          exact ha.2.trans hb.2.symm
        have hcard_pos : 0 < (s.filter (fun j => assign k j = v)).card :=
          Finset.card_pos.mpr ⟨i, hi_in_filter⟩
        simp only [hk0, ↓reduceIte]
        omega
  push Not at hM_le
  obtain ⟨S, N_int, hS_sub, hS_ne, hS_card, hS_band⟩ :=
    dyadic_pigeonhole_multi s hs_ne M assign
      (fun k hk i j hi hj => h_nested k (by omega) hi hj)
  let parent' : ℕ → Finset ι := fun k => S.image (assign k)
  let N : ℕ → ℕ := fun k =>
    if k = 0 then S.card
    else if k = M then 1
    else N_int k
  refine ⟨S, N, parent', hS_sub, ?_, ?_, ?_, ?_, ?_⟩
  · have hBR_eq : (⌊Real.logb 2 sR⌋₊ + 1 : ℝ) = (B : ℝ) := by
      rw [hBdef]; push_cast; ring
    change sR / _ ≤ _
    rw [hsR_def]
    exact hS_card
  · intro k hk v hv
    simp only [parent'] at hv
    rw [Finset.mem_image] at hv
    obtain ⟨i, hi_in_S, rfl⟩ := hv
    exact h_assign_mem k hk (hS_sub hi_in_S)
  · intro k _ i hi
    simp only [parent']
    exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
  · intro k _ v hv
    simp only [parent'] at hv
    rw [Finset.mem_image] at hv
    obtain ⟨i, hi_S, hi_eq⟩ := hv
    exact Finset.card_pos.mpr
      ⟨i, by rw [Finset.mem_filter]; exact ⟨hi_S, hi_eq⟩⟩
  · intro k hk v hv
    simp only [parent'] at hv
    rw [Finset.mem_image] at hv
    obtain ⟨i, hi_S, hi_eq⟩ := hv
    by_cases hk0 : k = 0
    · subst hk0
      have hi_in_s : i ∈ s := hS_sub hi_S
      have hroot_eq : assign 0 i = root := by
        have := h_assign_mem 0 (Nat.zero_le _) hi_in_s
        rw [h_root, Finset.mem_singleton] at this; exact this
      have hv_root : v = root := hroot_eq ▸ hi_eq.symm
      have hfilter_eq : S.filter (fun j => assign 0 j = v) = S := by
        apply Finset.filter_eq_self.mpr
        intro j hj
        have := h_assign_mem 0 (Nat.zero_le _) (hS_sub hj)
        rw [h_root, Finset.mem_singleton] at this
        rw [this, hv_root]
      rw [hfilter_eq]
      simp only [N, ↓reduceIte]
      have hS_pos : 0 < S.card := Finset.card_pos.mpr ⟨i, hi_S⟩
      omega
    · by_cases hkM : k = M
      · subst hkM
        simp only [N, hk0, ↓reduceIte]
        have hi_in_filter : i ∈ S.filter (fun j => assign k j = v) := by
          rw [Finset.mem_filter]; exact ⟨hi_S, hi_eq⟩
        have hcard_le_1 : (S.filter (fun j => assign k j = v)).card ≤ 1 := by
          apply Finset.card_le_one.mpr
          intro a ha b hb
          rw [Finset.mem_filter] at ha hb
          have ha' := h_top (hS_sub ha.1)
          have hb' := h_top (hS_sub hb.1)
          rw [ha'] at ha
          rw [hb'] at hb
          exact ha.2.trans hb.2.symm
        have hcard_pos : 0 < (S.filter (fun j => assign k j = v)).card :=
          Finset.card_pos.mpr ⟨i, hi_in_filter⟩
        omega
      · have hk_lt : k < M := lt_of_le_of_ne hk hkM
        have hk_ge : 1 ≤ k := by omega
        have hclass_eq : S.filter (fun j => assign k j = v) =
                          S.filter (fun j => assign k j = assign k i) := by
          rw [← hi_eq]
        rw [hclass_eq]
        simp only [N, hk0, hkM, ↓reduceIte]
        exact hS_band k hk_ge hk_lt i hi_S

open Classical in
/-- **`exists_pruned_subset` without the single-root hypothesis.**  Since `parent 0` is now a whole
grid net rather than a singleton, `h_root` is unavailable; all it was ever used for was to make the
level-0 assignment class equal to all of `s`, and the dyadic pigeonhole runs over levels `M-1, …, 1`
only, so it never had to touch level 0. -/
private lemma exists_pruned_subset_noroot
    (s : Finset ι) (M : ℕ) (hs_ne : s.Nonempty)
    (parent : ℕ → Finset ι) (assign : ℕ → ι → ι)
    (h_assign_mem : ∀ k ≤ M, ∀ ⦃i⦄, i ∈ s → assign k i ∈ parent k)
    (h_top : ∀ ⦃i⦄, i ∈ s → assign M i = i)
    (h_nested : ∀ k, k < M → ∀ ⦃i j⦄, i ∈ s → j ∈ s →
      assign (k + 1) i = assign (k + 1) j → assign k i = assign k j)
    (C₀ : ℝ) (hC₀_pos : 0 < C₀) (hC₀ : ((parent 0).card : ℝ) ≤ C₀) :
    ∃ (s' : Finset ι) (N : ℕ → ℕ) (parent' : ℕ → Finset ι),
      s' ⊆ s ∧
      (s.card : ℝ) / (C₀ * ((⌊Real.logb 2 (s.card : ℝ)⌋₊ + 1 : ℝ) ^ (M - 1)))
        ≤ (s'.card : ℝ) ∧
      (∀ k ≤ M, parent' k ⊆ parent k) ∧
      (∀ k ≤ M, ∀ ⦃i⦄, i ∈ s' → assign k i ∈ parent' k) ∧
      (∀ k ≤ M, ∀ v ∈ parent' k,
        0 < (s'.filter (fun i => assign k i = v)).card) ∧
      (∀ k ≤ M, ∀ v ∈ parent' k,
        N k ≤ (s'.filter (fun i => assign k i = v)).card ∧
        (s'.filter (fun i => assign k i = v)).card < 2 * N k) := by
  classical
  have h_parent0_ne : (parent 0).Nonempty := by
    obtain ⟨i, hi⟩ := hs_ne
    refine ⟨assign 0 i, h_assign_mem 0 (Nat.zero_le M) hi⟩
  obtain ⟨v₀, hv₀, h_max⟩ := Finset.exists_max_image (parent 0)
    (fun v => (s.filter (fun i => assign 0 i = v)).card) h_parent0_ne
  set s₀ : Finset ι := s.filter (fun i => assign 0 i = v₀) with hs₀_def
  have hs₀_nonempty : s₀.Nonempty := by
    by_contra h_empty
    rw [Finset.not_nonempty_iff_eq_empty] at h_empty
    have hzero : s₀.card = 0 := by
      rw [h_empty, Finset.card_empty]
    have h_all_zero : ∀ v ∈ parent 0, (s.filter (fun i => assign 0 i = v)).card = 0 := by
      intro v hv
      have hle := h_max v hv
      have hzero' : (s.filter (fun i => assign 0 i = v₀)).card = 0 := by
        simpa [hs₀_def] using hzero
      rw [hzero'] at hle
      exact Nat.eq_zero_of_le_zero hle
    have h_cover : s ⊆ (parent 0).biUnion
        (fun v => s.filter (fun i => assign 0 i = v)) := by
      intro i hi
      have hv : assign 0 i ∈ parent 0 := h_assign_mem 0 (Nat.zero_le M) hi
      refine Finset.mem_biUnion.mpr ⟨assign 0 i, hv, ?_⟩
      rw [Finset.mem_filter]
      exact ⟨hi, rfl⟩
    have h_card_le : s.card ≤ ∑ v ∈ parent 0,
        (s.filter (fun i => assign 0 i = v)).card :=
      le_trans (Finset.card_le_card h_cover) Finset.card_biUnion_le
    have h_sum_zero : ∑ v ∈ parent 0, (s.filter (fun i => assign 0 i = v)).card = 0 := by
      rw [Finset.sum_eq_zero]
      intro v hv
      rw [h_all_zero v hv]
    rw [h_sum_zero] at h_card_le
    have hs_pos : 0 < s.card := Finset.card_pos.mpr hs_ne
    omega
  have hs₀_sub : s₀ ⊆ s := Finset.filter_subset _ _
  have h_cover : s ⊆ (parent 0).biUnion
      (fun v => s.filter (fun i => assign 0 i = v)) := by
    intro i hi
    have hv : assign 0 i ∈ parent 0 := h_assign_mem 0 (Nat.zero_le M) hi
    refine Finset.mem_biUnion.mpr ⟨assign 0 i, hv, ?_⟩
    rw [Finset.mem_filter]
    exact ⟨hi, rfl⟩
  have h_card_nat : s.card ≤ ∑ v ∈ parent 0,
      (s.filter (fun i => assign 0 i = v)).card :=
    le_trans (Finset.card_le_card h_cover) Finset.card_biUnion_le
  have h_card_real : (s.card : ℝ) ≤ (∑ v ∈ parent 0,
      (s.filter (fun i => assign 0 i = v)).card : ℝ) := by exact_mod_cast h_card_nat
  have h_sum_max : (∑ v ∈ parent 0,
      (s.filter (fun i => assign 0 i = v)).card : ℝ) ≤
      ((parent 0).card : ℝ) * (s₀.card : ℝ) := by
    have h_each : ∀ v ∈ parent 0,
        ((s.filter (fun i => assign 0 i = v)).card : ℝ) ≤ (s₀.card : ℝ) := by
      intro v hv
      have h_nat : (s.filter (fun i => assign 0 i = v)).card ≤
          (s.filter (fun i => assign 0 i = v₀)).card := h_max v hv
      have h_s₀_card : (s.filter (fun i => assign 0 i = v₀)).card = s₀.card := rfl
      rw [h_s₀_card]
      exact_mod_cast h_nat
    calc
      (∑ v ∈ parent 0, ((s.filter (fun i => assign 0 i = v)).card : ℝ)) ≤
          (∑ v ∈ parent 0, (s₀.card : ℝ)) :=
        Finset.sum_le_sum (fun v hv => h_each v hv)
      _ = ((parent 0).card : ℝ) * (s₀.card : ℝ) := by simp [Finset.sum_const]
  have h_card_real' : (s.card : ℝ) ≤ ((parent 0).card : ℝ) * (s₀.card : ℝ) :=
    h_card_real.trans h_sum_max
  have h_avg : (s.card : ℝ) / C₀ ≤ (s₀.card : ℝ) := by
    have h_nonneg_s₀ : (0 : ℝ) ≤ (s₀.card : ℝ) := by exact_mod_cast Nat.zero_le _
    calc
      (s.card : ℝ) / C₀ ≤ (((parent 0).card : ℝ) * (s₀.card : ℝ)) / C₀ :=
        div_le_div_of_nonneg_right h_card_real' (by positivity : (0 : ℝ) ≤ C₀)
      _ = (s₀.card : ℝ) * ((parent 0).card : ℝ) / C₀ := by ring
      _ ≤ (s₀.card : ℝ) * C₀ / C₀ :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hC₀ h_nonneg_s₀)
          (by positivity : (0 : ℝ) ≤ C₀)
      _ = (s₀.card : ℝ) := by field_simp [hC₀_pos.ne']
  set parent'' : ℕ → Finset ι := fun k => if k = 0 then {v₀} else parent k with hparent''_def
  have h_root : parent'' 0 = {v₀} := by
    simp [parent'']
  have h_assign_mem'' : ∀ k ≤ M, ∀ ⦃i⦄, i ∈ s₀ → assign k i ∈ parent'' k := by
    intro k hk i hi
    have hi_s : i ∈ s := hs₀_sub hi
    rw [hs₀_def, Finset.mem_filter] at hi
    obtain ⟨_, hi_assign⟩ := hi
    dsimp [parent'']
    by_cases hk0 : k = 0
    · subst hk0
      simp [hi_assign]
    · simp [hk0, h_assign_mem k hk hi_s]
  have h_top'' : ∀ ⦃i⦄, i ∈ s₀ → assign M i = i := by
    intro i hi; exact h_top (hs₀_sub hi)
  have h_nested'' : ∀ k, k < M → ∀ ⦃i j⦄, i ∈ s₀ → j ∈ s₀ →
      assign (k + 1) i = assign (k + 1) j → assign k i = assign k j := by
    intro k hk i j hi hj hij
    exact h_nested k hk (hs₀_sub hi) (hs₀_sub hj) hij
  obtain ⟨s', N, parent', h_s'_sub_s₀, h_card_pruned, h_parent'_sub, h_assign'_mem,
      h_active, h_band⟩ :=
    exists_pruned_subset s₀ M parent'' assign v₀ h_assign_mem'' h_top'' h_root h_nested''
  have h_parent''_sub : ∀ k, parent'' k ⊆ parent k := by
    intro k
    dsimp [parent'']
    by_cases hk : k = 0
    · subst hk
      simp [hv₀]
    · simp [hk]
  have h_parent'_sub_parent : ∀ k ≤ M, parent' k ⊆ parent k := by
    intro k hk
    exact (h_parent'_sub k hk).trans (h_parent''_sub k)
  refine ⟨s', N, parent', ?_, ?_, h_parent'_sub_parent, h_assign'_mem, h_active, h_band⟩
  · exact h_s'_sub_s₀.trans hs₀_sub
  · set Ls : ℝ := (⌊Real.logb 2 (s.card : ℝ)⌋₊ + 1 : ℝ) ^ (M - 1)
    set Ls₀ : ℝ := (⌊Real.logb 2 (s₀.card : ℝ)⌋₊ + 1 : ℝ) ^ (M - 1)
    have hcard_s_pos : (0 : ℝ) < (s.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr hs_ne
    have hcard_s₀_pos : (0 : ℝ) < (s₀.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr hs₀_nonempty
    have hcard_s₀_le_s : (s₀.card : ℝ) ≤ (s.card : ℝ) := by
      exact_mod_cast Finset.card_le_card hs₀_sub
    have h_logb_le : Real.logb 2 (s₀.card : ℝ) ≤ Real.logb 2 (s.card : ℝ) :=
      Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hcard_s₀_pos hcard_s₀_le_s
    have h_floor_le : (⌊Real.logb 2 (s₀.card : ℝ)⌋₊ : ℝ) ≤ (⌊Real.logb 2 (s.card : ℝ)⌋₊ : ℝ) := by
      have h_floor_nat : (⌊Real.logb 2 (s₀.card : ℝ)⌋₊ : ℕ) ≤ (⌊Real.logb 2 (s.card : ℝ)⌋₊ : ℕ) :=
        Nat.floor_mono h_logb_le
      exact_mod_cast h_floor_nat
    have h_base : (⌊Real.logb 2 (s₀.card : ℝ)⌋₊ + 1 : ℝ) ≤
        (⌊Real.logb 2 (s.card : ℝ)⌋₊ + 1 : ℝ) := by
      linarith
    have h_base_nonneg : 0 ≤ (⌊Real.logb 2 (s₀.card : ℝ)⌋₊ + 1 : ℝ) := by positivity
    have h_Ls₀_le_Ls : Ls₀ ≤ Ls :=
      pow_le_pow_left₀ h_base_nonneg h_base (M - 1)
    have h_Ls₀_pos : (0 : ℝ) < Ls₀ := by
      have hpos : (0 : ℝ) < (⌊Real.logb 2 (s₀.card : ℝ)⌋₊ + 1 : ℝ) := by positivity
      exact pow_pos hpos (M - 1)
    have h_Ls_pos : (0 : ℝ) < Ls := by
      have hpos : (0 : ℝ) < (⌊Real.logb 2 (s.card : ℝ)⌋₊ + 1 : ℝ) := by positivity
      exact pow_pos hpos (M - 1)
    have h_nonneg_s₀_card : (0 : ℝ) ≤ (s₀.card : ℝ) := by exact_mod_cast Nat.zero_le _
    calc
      (s.card : ℝ) / (C₀ * Ls) = ((s.card : ℝ) / C₀) / Ls := by ring
      _ ≤ (s₀.card : ℝ) / Ls :=
        div_le_div_of_nonneg_right h_avg (by positivity : 0 ≤ Ls)
      _ ≤ (s₀.card : ℝ) / Ls₀ :=
        div_le_div_of_nonneg_left h_nonneg_s₀_card h_Ls₀_pos h_Ls₀_le_Ls
      _ ≤ (s'.card : ℝ) := h_card_pruned

/-! ### Pruning without the leaf self-assignment hypothesis

`exists_pruned_subset` and its variants require `h_top : ∀ i ∈ s, assign M i = i`, i.e. that the
finest level of the tower separates `s` into singletons.  That holds only when the leaf tubes are
pairwise distinct as *records*, which fails as soon as `T` is allowed to repeat a carrier.

The wrappers below remove `h_top` by **appending one artificial level `M + 1`** with
`assign (M+1) := id` and `parent (M+1) := s`.  For that tower `h_top` is a triviality and
`h_nested` at `k = M` is vacuous (its hypothesis is `i = j`), so the pigeonhole core is reused
verbatim: the level-`M` multiplicity classes are pigeonholed by the very same machinery that used
to handle intermediate levels.  The only cost is one extra dyadic factor, so the polylog exponent
goes from `M - 1` to `M` — still `δ^{o(1)}` at every call site. -/

open Classical in
/-- **`exists_pruned_subset_noroot` without `h_top`.**  Same appended-level trick as
`exists_pruned_subset_notop`, applied to the root-free variant; the dimensional constant `C₀` is
unchanged and the polylog exponent becomes `M`.  Public because it is the pigeonhole step of
`Tube.exists_uniformTubeSet_subfamily`. -/
lemma exists_pruned_subset_noroot_notop
    (s : Finset ι) (M : ℕ) (hs_ne : s.Nonempty)
    (parent : ℕ → Finset ι) (assign : ℕ → ι → ι)
    (h_assign_mem : ∀ k ≤ M, ∀ ⦃i⦄, i ∈ s → assign k i ∈ parent k)
    (h_nested : ∀ k, k < M → ∀ ⦃i j⦄, i ∈ s → j ∈ s →
      assign (k + 1) i = assign (k + 1) j → assign k i = assign k j)
    (C₀ : ℝ) (hC₀_pos : 0 < C₀) (hC₀ : ((parent 0).card : ℝ) ≤ C₀) :
    ∃ (s' : Finset ι) (N : ℕ → ℕ) (parent' : ℕ → Finset ι),
      s' ⊆ s ∧
      (s.card : ℝ) / (C₀ * ((⌊Real.logb 2 (s.card : ℝ)⌋₊ + 1 : ℝ) ^ M))
        ≤ (s'.card : ℝ) ∧
      (∀ k ≤ M, parent' k ⊆ parent k) ∧
      (∀ k ≤ M, ∀ ⦃i⦄, i ∈ s' → assign k i ∈ parent' k) ∧
      (∀ k ≤ M, ∀ v ∈ parent' k,
        0 < (s'.filter (fun i => assign k i = v)).card) ∧
      (∀ k ≤ M, ∀ v ∈ parent' k,
        N k ≤ (s'.filter (fun i => assign k i = v)).card ∧
        (s'.filter (fun i => assign k i = v)).card < 2 * N k) := by
  classical
  set assignE : ℕ → ι → ι := fun k => if k ≤ M then assign k else id with hassignE
  set parentE : ℕ → Finset ι := fun k => if k ≤ M then parent k else s with hparentE
  have h_assign_mem' : ∀ k ≤ M + 1, ∀ ⦃i⦄, i ∈ s → assignE k i ∈ parentE k := by
    intro k hk i hi
    by_cases hkM : k ≤ M
    · simpa [hassignE, hparentE, if_pos hkM] using h_assign_mem k hkM hi
    · have hk_eq : k = M + 1 := by omega
      subst hk_eq
      simp [hassignE, hparentE, hi]
  have h_top' : ∀ ⦃i⦄, i ∈ s → assignE (M + 1) i = i := by
    intro i hi
    simp [hassignE, show ¬ (M + 1 ≤ M) from by omega]
  have h_nested' : ∀ k, k < M + 1 → ∀ ⦃i j⦄, i ∈ s → j ∈ s →
      assignE (k + 1) i = assignE (k + 1) j → assignE k i = assignE k j := by
    intro k hk i j hi hj h_eq
    by_cases hkM : k < M
    · have hk_succ_le_M : k + 1 ≤ M := by omega
      have hk_le_M : k ≤ M := by omega
      have h_nested := h_nested k hkM hi hj
      have h_assign_eq : assign (k + 1) i = assign (k + 1) j := by
        simpa [hassignE, if_pos hk_succ_le_M] using h_eq
      simpa [hassignE, if_pos hk_le_M] using h_nested h_assign_eq
    · have hk_eq_M : k = M := by omega
      rw [hk_eq_M] at h_eq
      have hM_not_succ_le_M : ¬ (M + 1 ≤ M) := by omega
      have hi_eq_j : i = j := by
        simpa [hassignE, if_neg hM_not_succ_le_M] using h_eq
      rw [hi_eq_j]
  have hC₀' : ((parentE 0).card : ℝ) ≤ C₀ := by
    have h0M : (0 : ℕ) ≤ M := by omega
    simpa [hparentE, if_pos h0M] using hC₀
  obtain ⟨s', N, parent', hsub, hcard, hpsub, hamem, hact, hband⟩ :=
    exists_pruned_subset_noroot s (M + 1) hs_ne parentE assignE
      h_assign_mem' h_top' h_nested' C₀ hC₀_pos hC₀'
  refine ⟨s', N, parent', hsub, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Nat.add_sub_cancel] using hcard
  · intro k hk
    have hk' : k ≤ M + 1 := by omega
    simpa [hparentE, if_pos hk] using hpsub k hk'
  · intro k hk i hi
    have hk' : k ≤ M + 1 := by omega
    simpa [hassignE, if_pos hk] using hamem k hk' hi
  · intro k hk v hv
    have hk' : k ≤ M + 1 := by omega
    simpa [hassignE, if_pos hk] using hact k hk' v hv
  · intro k hk v hv
    have hk' : k ≤ M + 1 := by omega
    simpa [hassignE, if_pos hk] using hband k hk' v hv

end UniformConstruction

open Classical in
omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- Tight variant of `isUniformAtScale_of_pruned`: identical construction (parent tubes `W k`), with
the tight bounded-overlap constant `overlapConstBOTight`. Consumed by
`exists_uniform_subset_tight`. -/
theorem isUniformAtScale_of_pruned_tight
    {δ : NNReal} (_hδ : 0 < δ) (_hδ1 : δ < 1)
    (s : Finset ι) (T : ι → Tube δ E)
    (M : ℕ) (ρ : ℕ → NNReal) (_hρ_pos : ∀ k, 0 < ρ k)
    (parent : ℕ → Finset ι) (assign : ℕ → ι → ι)
    (W : ∀ k, ι → Tube (ρ k) E)
    (h_cover : ∀ k ≤ M, ∀ ⦃i⦄, i ∈ s →
      (T i).toConvexSpaceBody ≤ (W k (assign k i)).toConvexSpaceBody)
    (h_injOn : ∀ k ≤ M, Set.InjOn (W k) (parent k : Set ι))
    (h_overlap : ∀ k ≤ M, ∀ (V : Tube (ρ k) E),
      ((parent k).filter (fun v => ∃ i ∈ s,
          (T i).toConvexSpaceBody ≤ (W k v).toConvexSpaceBody ∧
          (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody)).card ≤
        Tube.overlapConstBOTight (Module.finrank ℝ E))
    (s' : Finset ι) (N : ℕ → ℕ) (parent' : ℕ → Finset ι)
    (hs'_sub : s' ⊆ s)
    (h_parent'_sub : ∀ k ≤ M, parent' k ⊆ parent k)
    (h_assign'_mem : ∀ k ≤ M, ∀ ⦃i⦄, i ∈ s' → assign k i ∈ parent' k)
    (_h_active : ∀ k ≤ M, ∀ v ∈ parent' k,
      0 < (s'.filter (fun i => assign k i = v)).card)
    (h_band : ∀ k ≤ M, ∀ v ∈ parent' k,
      N k ≤ (s'.filter (fun i => assign k i = v)).card ∧
      (s'.filter (fun i => assign k i = v)).card < 2 * N k)
    (hs'_ne : s'.Nonempty)
    (h_pcard : ∀ kk, kk < M → ((parent kk).card : ℝ) ≤
      (641 : ℝ) ^ (2 * Module.finrank ℝ E)
        * ((4 : ℝ) / ((ρ kk : NNReal) : ℝ)) ^ (2 * Module.finrank ℝ E))
    {k : ℕ} (hk : k ≤ M) :
    ∃ u : IsUniformAtScale s' T (ρ k)
        (2 * (Tube.overlapConstBOTight (Module.finrank ℝ E) : NNReal)),
      (1 : NNReal) ≤ u.branchingN ∧
      (k < M → ((u.parent.card : ℝ) ≤
        (641 : ℝ) ^ (2 * Module.finrank ℝ E)
          * ((4 : ℝ) / ((ρ k : NNReal) : ℝ)) ^ (2 * Module.finrank ℝ E))) ∧
      u.parent = parent' k ∧ u.parentTube = W k ∧ u.branchingN = (N k : NNReal) := by
  classical
  set n := Module.finrank ℝ E with hn
  set Dnat : ℕ := Tube.overlapConstBOTight n with hDnat
  set K : NNReal := 2 * (Tube.overlapConstBOTight n : NNReal) with hK
  have hKcast : K = ((2 * Dnat : ℕ) : NNReal) := by
    rw [hK, hDnat]; push_cast; ring
  refine ⟨{
    branchingN := (N k : NNReal)
    parent := parent' k
    parentTube := W k
    exists_le_rescale := ?_
    boundedOverlap := ?_
    parentTube_injOn := ?_
    card_filter_le := ?_
    le_mul_card_filter := ?_ }, ?_, ?_, rfl, rfl, rfl⟩
  · intro i hi
    exact ⟨assign k i, h_assign'_mem k hk hi, h_cover k hk (hs'_sub hi)⟩
  · intro V
    have hsub : ((parent' k).filter (fun j => ∃ i ∈ s',
          (T i).toConvexSpaceBody ≤ (W k j).toConvexSpaceBody ∧
          (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody)) ⊆
        ((parent k).filter (fun j => ∃ i ∈ s,
          (T i).toConvexSpaceBody ≤ (W k j).toConvexSpaceBody ∧
          (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody)) := by
      intro v hv
      rw [Finset.mem_filter] at hv ⊢
      obtain ⟨hv_par, i, hi_s', hPij⟩ := hv
      exact ⟨h_parent'_sub k hk hv_par, i, hs'_sub hi_s', hPij⟩
    have hle : ((parent' k).filter (fun j => ∃ i ∈ s',
          (T i).toConvexSpaceBody ≤ (W k j).toConvexSpaceBody ∧
          (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody)).card ≤ Dnat :=
      le_trans (Finset.card_le_card hsub) (h_overlap k hk V)
    have hDK : (Dnat : NNReal) ≤ K := by
      rw [hK, hDnat, two_mul]
      exact le_add_self
    calc (((parent' k).filter (fun j => ∃ i ∈ s',
            (T i).toConvexSpaceBody ≤ (W k j).toConvexSpaceBody ∧
            (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody)).card : NNReal)
        ≤ (Dnat : NNReal) := by exact_mod_cast hle
      _ ≤ K := hDK
  · exact Set.InjOn.mono (Finset.coe_subset.mpr (h_parent'_sub k hk)) (h_injOn k hk)
  · intro j hj
    set V : Tube (ρ k) E := W k j with hV
    set F : Finset ι := s'.filter (fun i => (T i).toConvexSpaceBody ≤ (W k j).toConvexSpaceBody)
      with hF
    set Comp : Finset ι := (parent' k).filter (fun v => ∃ i ∈ s,
        (T i).toConvexSpaceBody ≤ (W k v).toConvexSpaceBody ∧
        (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody) with hComp
    have hsub : F ⊆ Comp.biUnion (fun v => s'.filter (fun i => assign k i = v)) := by
      intro i hi
      rw [hF, Finset.mem_filter] at hi
      obtain ⟨hi_s', hi_le⟩ := hi
      rw [Finset.mem_biUnion]
      refine ⟨assign k i, ?_, ?_⟩
      · rw [hComp, Finset.mem_filter]
        refine ⟨h_assign'_mem k hk hi_s', i, hs'_sub hi_s', ?_, ?_⟩
        · exact h_cover k hk (hs'_sub hi_s')
        · rw [hV]; exact hi_le
      · rw [Finset.mem_filter]; exact ⟨hi_s', rfl⟩
    have hcard1 : F.card ≤ ∑ v ∈ Comp, (s'.filter (fun i => assign k i = v)).card :=
      le_trans (Finset.card_le_card hsub) (Finset.card_biUnion_le)
    have hcard2 : ∑ v ∈ Comp, (s'.filter (fun i => assign k i = v)).card ≤
        ∑ v ∈ Comp, (2 * N k) := by
      apply Finset.sum_le_sum
      intro v hv
      have hv' : v ∈ parent' k := (Finset.mem_filter.mp hv).1
      exact (h_band k hk v hv').2.le
    have hComp_card : Comp.card ≤ Dnat := by
      have hCompsub : Comp ⊆ (parent k).filter (fun v => ∃ i ∈ s,
          (T i).toConvexSpaceBody ≤ (W k v).toConvexSpaceBody ∧
          (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody) := by
        intro v hv
        rw [hComp, Finset.mem_filter] at hv
        rw [Finset.mem_filter]
        exact ⟨h_parent'_sub k hk hv.1, hv.2⟩
      calc Comp.card ≤ _ := Finset.card_le_card hCompsub
        _ ≤ Dnat := h_overlap k hk V
    have hsum_const : ∑ v ∈ Comp, (2 * N k) = Comp.card * (2 * N k) := by
      rw [Finset.sum_const, smul_eq_mul]
    have hFnat : F.card ≤ 2 * Dnat * N k := by
      calc F.card ≤ Comp.card * (2 * N k) := le_trans hcard1 (by rw [← hsum_const]; exact hcard2)
        _ ≤ Dnat * (2 * N k) := by
            apply Nat.mul_le_mul_right; exact hComp_card
        _ = 2 * Dnat * N k := by ring
    calc ((F.card : ℕ) : NNReal) ≤ ((2 * Dnat * N k : ℕ) : NNReal) := by exact_mod_cast hFnat
      _ = K * (N k : NNReal) := by rw [hKcast]; push_cast; ring
  · intro j hj
    set F : Finset ι := s'.filter (fun i => (T i).toConvexSpaceBody ≤ (W k j).toConvexSpaceBody)
      with hF
    set Cls : Finset ι := s'.filter (fun i => assign k i = j) with hCls
    have hClsF : Cls ⊆ F := by
      intro i hi
      rw [hCls, Finset.mem_filter] at hi
      obtain ⟨hi_s', hi_eq⟩ := hi
      rw [hF, Finset.mem_filter]
      refine ⟨hi_s', ?_⟩
      have := h_cover k hk (hs'_sub hi_s')
      rwa [hi_eq] at this
    have hNk : N k ≤ F.card := le_trans (h_band k hk j hj).1 (Finset.card_le_card hClsF)
    have h1K : (1 : NNReal) ≤ K := by
      rw [hK]
      have h1 : (1 : ℕ) ≤ Tube.overlapConstBOTight n :=
        Nat.one_le_iff_ne_zero.mpr (by simp [Tube.overlapConstBOTight])
      have h1' : (1 : NNReal) ≤ (Tube.overlapConstBOTight n : NNReal) := by exact_mod_cast h1
      calc (1 : NNReal) ≤ 2 * 1 := by norm_num
        _ ≤ 2 * (Tube.overlapConstBOTight n : NNReal) := by gcongr
    calc (N k : NNReal) ≤ (F.card : NNReal) := by exact_mod_cast hNk
      _ = 1 * (F.card : NNReal) := (one_mul _).symm
      _ ≤ K * (F.card : NNReal) := by gcongr
  · obtain ⟨i₀, hi₀⟩ := hs'_ne
    have hv : assign k i₀ ∈ parent' k := h_assign'_mem k hk hi₀
    have h3 := _h_active k hk (assign k i₀) hv
    have h2 := (h_band k hk (assign k i₀) hv).2
    have hNk1 : 1 ≤ N k := by omega
    change (1 : NNReal) ≤ (N k : NNReal)
    exact_mod_cast hNk1
  · intro hkM
    change ((parent' k).card : ℝ) ≤
      (641 : ℝ) ^ (2 * Module.finrank ℝ E)
        * ((4 : ℝ) / ((ρ k : NNReal) : ℝ)) ^ (2 * Module.finrank ℝ E)
    calc ((parent' k).card : ℝ)
        ≤ ((parent k).card : ℝ) := by
          exact_mod_cast Finset.card_le_card (h_parent'_sub k hk)
      _ ≤ _ := h_pcard k hkM

/-- Pure `Nat` step behind the child-count telescope: `a ≤ 4·b·max 1 (a / (2·b))` for `0 < b`.
`a < (a/(2b) + 1)·(2b)` and `a/(2b) + 1 ≤ 2·max 1 (a/(2b))`. -/
private lemma nat_le_four_mul_max_div (a b : ℕ) (hb : 0 < b) :
    a ≤ 4 * b * max 1 (a / (2 * b)) := by
  have hb2 : 0 < 2 * b := by omega
  have hmod := Nat.div_add_mod a (2 * b)
  have hlt : a % (2 * b) < 2 * b := Nat.mod_lt _ hb2
  set q := a / (2 * b) with hq
  have hq1 : q + 1 ≤ 2 * max 1 q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · simp [h]
    · have : max 1 q = q := Nat.max_eq_right h
      omega
  nlinarith

open Classical in
/-- Every band value `N k` (`k ≤ M`) is positive: the fibre over `assign k i₀` is nonempty, and the
band caps it by `2 · N k`. -/
private lemma band_N_pos
    {ι : Type*} (M : ℕ) (assign : ℕ → ι → ι) (parent' : ℕ → Finset ι) (N : ℕ → ℕ)
    (s' : Finset ι) {i₀ : ι} (hi₀ : i₀ ∈ s')
    (h_assign'_mem : ∀ k ≤ M, ∀ ⦃i⦄, i ∈ s' → assign k i ∈ parent' k)
    (h_active : ∀ k ≤ M, ∀ v ∈ parent' k, 0 < (s'.filter (fun i => assign k i = v)).card)
    (h_band : ∀ k ≤ M, ∀ v ∈ parent' k,
      N k ≤ (s'.filter (fun i => assign k i = v)).card ∧
      (s'.filter (fun i => assign k i = v)).card < 2 * N k) :
    ∀ k ≤ M, 0 < N k := by
  intro k hk
  have hv : assign k i₀ ∈ parent' k := h_assign'_mem k hk hi₀
  have h1 : 0 < (s'.filter (fun i => assign k i = assign k i₀)).card :=
    h_active k hk (assign k i₀) hv
  have h2 : (s'.filter (fun i => assign k i = assign k i₀)).card < 2 * N k :=
    (h_band k hk (assign k i₀) hv).2
  omega

open Classical in
/-- `N M ≤ 1`: at the finest scale `assign M` is the identity on `s`, so its fibres in `s'` are
singletons and the band's lower bound forces `N M ≤ 1`. -/
private lemma band_N_last_le_one
    {ι : Type*} (s : Finset ι) (M : ℕ) (assign : ℕ → ι → ι) (parent' : ℕ → Finset ι) (N : ℕ → ℕ)
    (s' : Finset ι) (hs'_sub : s' ⊆ s) {i₀ : ι} (hi₀ : i₀ ∈ s')
    (h_top : ∀ ⦃i⦄, i ∈ s → assign M i = i)
    (h_assign'_mem : ∀ k ≤ M, ∀ ⦃i⦄, i ∈ s' → assign k i ∈ parent' k)
    (h_band : ∀ k ≤ M, ∀ v ∈ parent' k,
      N k ≤ (s'.filter (fun i => assign k i = v)).card ∧
      (s'.filter (fun i => assign k i = v)).card < 2 * N k) :
    N M ≤ 1 := by
  have htop0 : assign M i₀ = i₀ := h_top (hs'_sub hi₀)
  have hv : assign M i₀ ∈ parent' M := h_assign'_mem M le_rfl hi₀
  have hfib : s'.filter (fun i => assign M i = assign M i₀) = {i₀} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨Finset.mem_filter.mpr ⟨hi₀, rfl⟩, ?_⟩
    intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hxs, hxeq⟩
    rw [h_top (hs'_sub hxs), htop0] at hxeq
    exact hxeq
  have h := (h_band M le_rfl (assign M i₀) hv).1
  rw [hfib] at h
  simpa using h

open Classical in
/-- The coarsest scale covers `s'`: summing the band's upper bound over `parent' 0` gives
`|s'| ≤ 2 · |parent' 0| · N 0`. -/
private lemma band_card_le_root
    {ι : Type*} (M : ℕ) (assign : ℕ → ι → ι) (parent' : ℕ → Finset ι) (N : ℕ → ℕ)
    (s' : Finset ι)
    (h_assign'_mem : ∀ k ≤ M, ∀ ⦃i⦄, i ∈ s' → assign k i ∈ parent' k)
    (h_band : ∀ k ≤ M, ∀ v ∈ parent' k,
      N k ≤ (s'.filter (fun i => assign k i = v)).card ∧
      (s'.filter (fun i => assign k i = v)).card < 2 * N k) :
    s'.card ≤ 2 * ((parent' 0).card * N 0) := by
  have hfib : s'.card
      = ∑ v ∈ parent' 0, (s'.filter (fun i => assign 0 i = v)).card :=
    Finset.card_eq_sum_card_fiberwise (fun i hi => h_assign'_mem 0 (Nat.zero_le M) hi)
  rw [hfib]
  calc ∑ v ∈ parent' 0, (s'.filter (fun i => assign 0 i = v)).card
      ≤ ∑ _v ∈ parent' 0, 2 * N 0 :=
        Finset.sum_le_sum (fun v hv => (h_band 0 (Nat.zero_le M) v hv).2.le)
    _ = 2 * ((parent' 0).card * N 0) := by
      rw [Finset.sum_const, smul_eq_mul]; ring

open Classical in
omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **The child count.**  A coarse parent `j ∈ parent' k` has at least `max 1 (N k / (2·N (k+1)))`
fine children in the containment filter: the `assign (k+1)`-fibres refine the `assign k`-fibres,
`j`'s coarse fibre has `≥ N k` leaves and each fine fibre `< 2·N (k+1)`, and the factor-1
cross-level nesting puts the image of `j`'s fibre inside the containment filter. -/
private lemma band_child_card_ge
    {δ : NNReal} {ι : Type*} (s : Finset ι) (_T : ι → Tube δ E)
    (M : ℕ) (ρ : ℕ → NNReal) (W : ∀ k, ι → Tube (ρ k) E)
    (assign : ℕ → ι → ι) (parent' : ℕ → Finset ι) (N : ℕ → ℕ) (s' : Finset ι)
    (hs'_sub : s' ⊆ s)
    (h_assign'_mem : ∀ k ≤ M, ∀ ⦃i⦄, i ∈ s' → assign k i ∈ parent' k)
    (h_active : ∀ k ≤ M, ∀ v ∈ parent' k, 0 < (s'.filter (fun i => assign k i = v)).card)
    (h_band : ∀ k ≤ M, ∀ v ∈ parent' k,
      N k ≤ (s'.filter (fun i => assign k i = v)).card ∧
      (s'.filter (fun i => assign k i = v)).card < 2 * N k)
    (h_level_nest : ∀ k, k < M → ∀ ⦃i⦄, i ∈ s →
      (W (k + 1) (assign (k + 1) i)).toConvexSpaceBody ≤ (W k (assign k i)).toConvexSpaceBody)
    (k : ℕ) (hk : k < M) (j : ι) (hj : j ∈ parent' k) :
    max 1 (N k / (2 * N (k + 1))) ≤ ((parent' (k + 1)).filter (fun i : ι =>
      (W (k + 1) i).toConvexSpaceBody ≤ (W k j).toConvexSpaceBody)).card := by
  classical
  set Cls := s'.filter (fun i => assign k i = j) with hCls
  set Img := Cls.image (assign (k + 1)) with hImg
  have hk1 : k + 1 ≤ M := by omega
  have hkle : k ≤ M := by omega
  have hsub : Img ⊆ (parent' (k + 1)).filter (fun i : ι =>
      (W (k + 1) i).toConvexSpaceBody ≤ (W k j).toConvexSpaceBody) := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨i, hi, hiv⟩
    rcases Finset.mem_filter.mp hi with ⟨hi_s', hi_j⟩
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · rw [← hiv]; exact h_assign'_mem (k + 1) hk1 hi_s'
    · have := h_level_nest k hk (hs'_sub hi_s')
      rw [hiv, hi_j] at this
      exact this
  have hfiber : ∀ v ∈ Img, (Cls.filter (fun a => assign (k + 1) a = v)).card ≤ 2 * N (k + 1) := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨i, hi, hiv⟩
    rcases Finset.mem_filter.mp hi with ⟨hi_s', hi_j⟩
    have hvmem : v ∈ parent' (k + 1) := by
      rw [← hiv]; exact h_assign'_mem (k + 1) hk1 hi_s'
    have hsub2 : Cls.filter (fun i => assign (k + 1) i = v)
        ⊆ s'.filter (fun i => assign (k + 1) i = v) := by
      intro x hx
      rcases Finset.mem_filter.mp hx with ⟨hxCls, hxv⟩
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hxCls).1, hxv⟩
    have hlt : (s'.filter (fun i => assign (k + 1) i = v)).card < 2 * N (k + 1) :=
      (h_band (k + 1) hk1 v hvmem).2
    exact le_trans (Finset.card_le_card hsub2) (Nat.le_of_lt hlt)
  have hCls_le : Cls.card ≤ (2 * N (k + 1)) * Img.card :=
    Finset.card_le_mul_card_image Cls (2 * N (k + 1)) hfiber
  have hNk : N k ≤ Cls.card := (h_band k hkle j hj).1
  have hdiv : N k / (2 * N (k + 1)) ≤ Img.card :=
    Nat.div_le_of_le_mul (le_trans hNk hCls_le)
  have hone : 1 ≤ Img.card := by
    have hpos : 0 < Cls.card := h_active k hkle j hj
    have hpos_nonempty : Cls.Nonempty := Finset.card_pos.mp hpos
    have himg_nonempty : Img.Nonempty := hpos_nonempty.image (assign (k + 1))
    have hpos_img : 0 < Img.card := Finset.card_pos.mpr himg_nonempty
    exact Nat.succ_le_of_lt hpos_img
  have hmax : max 1 (N k / (2 * N (k + 1))) ≤ Img.card :=
    (Nat.max_le.mpr ⟨hone, hdiv⟩)
  exact hmax.trans (Finset.card_le_card hsub)

open Classical in
omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **The child count, upper side.**  A coarse parent has at most `2·D·N k / N (k+1)` fine children
in the containment filter, where `D = overlapConstBOTight n`.  This is the two-sidedness of GWZ's
common fibre cardinality `b_m`, and it is what the `J k`-copies calibration needs; it is stated in
multiplied form to avoid `Nat` division. -/
private lemma band_child_card_le
    {δ : NNReal} {ι : Type*} (s : Finset ι) (T : ι → Tube δ E)
    (M : ℕ) (ρ : ℕ → NNReal) (W : ∀ k, ι → Tube (ρ k) E)
    (assign : ℕ → ι → ι) (parent parent' : ℕ → Finset ι) (N : ℕ → ℕ) (s' : Finset ι)
    (hs'_sub : s' ⊆ s)
    (h_cover : ∀ k ≤ M, ∀ ⦃i⦄, i ∈ s →
      (T i).toConvexSpaceBody ≤ (W k (assign k i)).toConvexSpaceBody)
    (h_overlap : ∀ k ≤ M, ∀ (V : Tube (ρ k) E),
      ((parent k).filter (fun v => ∃ i ∈ s,
          (T i).toConvexSpaceBody ≤ (W k v).toConvexSpaceBody ∧
          (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody)).card ≤
        Tube.overlapConstBOTight (Module.finrank ℝ E))
    (h_parent'_sub : ∀ k ≤ M, parent' k ⊆ parent k)
    (h_assign'_mem : ∀ k ≤ M, ∀ ⦃i⦄, i ∈ s' → assign k i ∈ parent' k)
    (h_band : ∀ k ≤ M, ∀ v ∈ parent' k,
      N k ≤ (s'.filter (fun i => assign k i = v)).card ∧
      (s'.filter (fun i => assign k i = v)).card < 2 * N k)
    (k : ℕ) (hk : k < M) (j : ι) (_hj : j ∈ parent' k) :
    ((parent' (k + 1)).filter (fun i : ι =>
        (W (k + 1) i).toConvexSpaceBody ≤ (W k j).toConvexSpaceBody)).card * N (k + 1)
      ≤ 2 * Tube.overlapConstBOTight (Module.finrank ℝ E) * N k := by
  set D := Tube.overlapConstBOTight (Module.finrank ℝ E) with hD
  set F := (parent' (k + 1)).filter (fun i : ι =>
    (W (k + 1) i).toConvexSpaceBody ≤ (W k j).toConvexSpaceBody) with hF
  set L := s'.filter (fun i => (T i).toConvexSpaceBody ≤ (W k j).toConvexSpaceBody) with hL
  set Fib := fun (v : ι) => s'.filter (fun i => assign (k + 1) i = v) with hFib
  have hk1 : k + 1 ≤ M := by omega
  have hkle : k ≤ M := by omega
  have hFib_card : ∀ v ∈ F, N (k + 1) ≤ (Fib v).card := by
    intro v hv
    rcases Finset.mem_filter.mp hv with ⟨hv_parent', _⟩
    exact (h_band (k + 1) hk1 v hv_parent').1
  have hFib_sub_L : ∀ v ∈ F, Fib v ⊆ L := by
    intro v hv i hi
    rcases Finset.mem_filter.mp hi with ⟨hi_s', hi_assign⟩
    have hv_contain : (W (k + 1) v).toConvexSpaceBody ≤ (W k j).toConvexSpaceBody :=
      (Finset.mem_filter.mp hv).2
    refine Finset.mem_filter.mpr ⟨hi_s', ?_⟩
    calc (T i).toConvexSpaceBody ≤ (W (k + 1) (assign (k + 1) i)).toConvexSpaceBody :=
      h_cover (k + 1) hk1 (hs'_sub hi_s')
    _ = (W (k + 1) v).toConvexSpaceBody := by rw [hi_assign]
    _ ≤ (W k j).toConvexSpaceBody := hv_contain
  have h_disjoint : (F : Set ι).PairwiseDisjoint Fib := by
    intro v1 hv1 v2 hv2 hne
    refine Finset.disjoint_left.mpr ?_
    intro i hi1 hi2
    rcases Finset.mem_filter.mp hi1 with ⟨_, hi_assign1⟩
    rcases Finset.mem_filter.mp hi2 with ⟨_, hi_assign2⟩
    exact hne (hi_assign1.symm.trans hi_assign2)
  have h_card_biUnion : (F.biUnion Fib).card = ∑ v ∈ F, (Fib v).card :=
    Finset.card_biUnion h_disjoint
  have h_biUnion_sub_L : F.biUnion Fib ⊆ L := by
    intro i hi
    rcases Finset.mem_biUnion.mp hi with ⟨v, hvF, hiFib⟩
    exact hFib_sub_L v hvF hiFib
  have h_sum_le : ∑ v ∈ F, (Fib v).card ≤ L.card := by
    calc ∑ v ∈ F, (Fib v).card = (F.biUnion Fib).card := h_card_biUnion.symm
      _ ≤ L.card := Finset.card_le_card h_biUnion_sub_L
  have hF_card_mul : F.card * N (k + 1) ≤ L.card := by
    calc
      F.card * N (k + 1) = ∑ v ∈ F, N (k + 1) := by
        simp [Finset.sum_eq_card_nsmul (fun v _ => rfl), smul_eq_mul]
      _ ≤ ∑ v ∈ F, (Fib v).card := Finset.sum_le_sum fun v hv => hFib_card v hv
      _ ≤ L.card := h_sum_le
  set Img := L.image (assign k) with hImg
  have hImg_card_le_D : Img.card ≤ D := by
    have hsub : Img ⊆ (parent k).filter (fun v => ∃ i ∈ s,
        (T i).toConvexSpaceBody ≤ (W k v).toConvexSpaceBody ∧
        (T i).toConvexSpaceBody ≤ (W k j).toConvexSpaceBody) := by
      intro v hv
      rcases Finset.mem_image.mp hv with ⟨i, hiL, hiv⟩
      rcases Finset.mem_filter.mp hiL with ⟨hi_s', hi_T⟩
      have hv_parent' : v ∈ parent' k := by
        rw [← hiv]; exact h_assign'_mem k hkle hi_s'
      refine Finset.mem_filter.mpr ⟨h_parent'_sub k hkle hv_parent',
        i, hs'_sub hi_s', ?_, hi_T⟩
      rw [← hiv]; exact h_cover k hkle (hs'_sub hi_s')
    have hcard : ((parent k).filter (fun v => ∃ i ∈ s,
        (T i).toConvexSpaceBody ≤ (W k v).toConvexSpaceBody ∧
        (T i).toConvexSpaceBody ≤ (W k j).toConvexSpaceBody)).card ≤ D :=
      h_overlap k hkle (W k j)
    exact (Finset.card_le_card hsub).trans hcard
  have hfiber : ∀ v ∈ Img, (L.filter (fun i => assign k i = v)).card ≤ 2 * N k := by
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨i, hiL, hiv⟩
    rcases Finset.mem_filter.mp hiL with ⟨hi_s', hi_T⟩
    have hv_parent' : v ∈ parent' k := by
      rw [← hiv]; exact h_assign'_mem k hkle hi_s'
    have hsub : L.filter (fun i => assign k i = v) ⊆ s'.filter (fun i => assign k i = v) := by
      intro x hx
      rcases Finset.mem_filter.mp hx with ⟨hxL, hx_assign⟩
      rcases Finset.mem_filter.mp hxL with ⟨hx_s', _⟩
      exact Finset.mem_filter.mpr ⟨hx_s', hx_assign⟩
    have hlt : (s'.filter (fun i => assign k i = v)).card < 2 * N k :=
      (h_band k hkle v hv_parent').2
    exact le_trans (Finset.card_le_card hsub) (Nat.le_of_lt hlt)
  have hL_card_le : L.card ≤ (2 * N k) * Img.card :=
    Finset.card_le_mul_card_image L (2 * N k) hfiber
  have hL_card_le_D : L.card ≤ 2 * D * N k := by
    calc
      L.card ≤ (2 * N k) * Img.card := hL_card_le
      _ ≤ (2 * N k) * D := Nat.mul_le_mul_left (2 * N k) hImg_card_le_D
      _ = 2 * D * N k := by ring
  calc
    F.card * N (k + 1) ≤ L.card := hF_card_mul
    _ ≤ 2 * D * N k := hL_card_le_D

/-- Telescoped form of `nat_le_four_mul_max_div` along the scale chain. -/
private lemma band_telescope
    (M : ℕ) (N : ℕ → ℕ) (N₂ : ℕ → ℕ)
    (hN₂ : ∀ k, N₂ k = max 1 (N k / (2 * N (k + 1))))
    (hN_pos : ∀ k ≤ M, 0 < N k) :
    ∀ m, m ≤ M → (N 0 : ℝ) ≤ (4 : ℝ) ^ m * (N m : ℝ) * ∏ k ∈ Finset.range m, (N₂ k : ℝ) := by
  intro m
  induction m with
  | zero =>
    intro hm
    simp
  | succ m ih =>
    intro hm
    have hm' : m ≤ M := by omega
    have hN_pos_succ : 0 < N (m + 1) := hN_pos (m + 1) (by omega)
    have hstep : N m ≤ 4 * N (m + 1) * N₂ m := by
      rw [hN₂ m]
      exact nat_le_four_mul_max_div (N m) (N (m + 1)) hN_pos_succ
    have hstepR : (N m : ℝ) ≤ 4 * (N (m + 1) : ℝ) * (N₂ m : ℝ) := by exact_mod_cast hstep
    have h_nonneg_pow : 0 ≤ (4 : ℝ) ^ m := by positivity
    have h_nonneg_prod : 0 ≤ ∏ k ∈ Finset.range m, (N₂ k : ℝ) :=
      Finset.prod_nonneg fun k _ => by
        have : 0 ≤ N₂ k := Nat.zero_le _
        exact_mod_cast this
    calc
      (N 0 : ℝ) ≤ (4 : ℝ) ^ m * (N m : ℝ) * ∏ k ∈ Finset.range m, (N₂ k : ℝ) := ih hm'
      _ ≤ (4 : ℝ) ^ m * (4 * (N (m + 1) : ℝ) * (N₂ m : ℝ)) * ∏ k ∈ Finset.range m, (N₂ k : ℝ) := by
        apply mul_le_mul_of_nonneg_right ?_ h_nonneg_prod
        apply mul_le_mul_of_nonneg_left hstepR h_nonneg_pow
      _ = (4 : ℝ) ^ (m + 1) * (N (m + 1) : ℝ)
          * ((∏ k ∈ Finset.range m, (N₂ k : ℝ)) * (N₂ m : ℝ)) := by ring
      _ = (4 : ℝ) ^ (m + 1) * (N (m + 1) : ℝ) * ∏ k ∈ Finset.range (m + 1), (N₂ k : ℝ) := by
        rw [Finset.prod_range_succ]

open Classical in
omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **Per-parent child count from the dyadic band.**  Every coarse parent has a uniformly bounded
number of fine children, with NO pigeonholing: fine fibres refine coarse ones, each coarse fibre has
at least `N k` leaves and each fine one fewer than `2 · N (k+1)`.  The companion product bound
telescopes the same band data to `|s'| ≤ 2 · |parent' 0| · 4^M · ∏ N₂`, `δ`-independently. -/
private lemma exists_child_count_of_band
    {δ : NNReal} {ι : Type*} (s : Finset ι) (T : ι → Tube δ E)
    (M : ℕ) (ρ : ℕ → NNReal) (W : ∀ k, ι → Tube (ρ k) E)
    (assign : ℕ → ι → ι) (parent parent' : ℕ → Finset ι) (N : ℕ → ℕ) (s' : Finset ι)
    (hs'_sub : s' ⊆ s) (hs'_ne : s'.Nonempty)
    (h_top : ∀ ⦃i⦄, i ∈ s → assign M i = i)
    (_h_nested : ∀ k, k < M → ∀ ⦃i j⦄, i ∈ s → j ∈ s →
      assign (k + 1) i = assign (k + 1) j → assign k i = assign k j)
    (h_cover : ∀ k ≤ M, ∀ ⦃i⦄, i ∈ s →
      (T i).toConvexSpaceBody ≤ (W k (assign k i)).toConvexSpaceBody)
    (h_overlap : ∀ k ≤ M, ∀ (V : Tube (ρ k) E),
      ((parent k).filter (fun v => ∃ i ∈ s,
          (T i).toConvexSpaceBody ≤ (W k v).toConvexSpaceBody ∧
          (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody)).card ≤
        Tube.overlapConstBOTight (Module.finrank ℝ E))
    (h_parent'_sub : ∀ k ≤ M, parent' k ⊆ parent k)
    (h_assign'_mem : ∀ k ≤ M, ∀ ⦃i⦄, i ∈ s' → assign k i ∈ parent' k)
    (h_active : ∀ k ≤ M, ∀ v ∈ parent' k, 0 < (s'.filter (fun i => assign k i = v)).card)
    (h_band : ∀ k ≤ M, ∀ v ∈ parent' k,
      N k ≤ (s'.filter (fun i => assign k i = v)).card ∧
      (s'.filter (fun i => assign k i = v)).card < 2 * N k)
    (h_level_nest : ∀ k, k < M → ∀ ⦃i⦄, i ∈ s →
      (W (k + 1) (assign (k + 1) i)).toConvexSpaceBody ≤ (W k (assign k i)).toConvexSpaceBody) :
    ∃ N₂ : ℕ → ℕ, (∀ k, 0 < N₂ k) ∧
      (∀ k, k < M → ∀ j ∈ parent' k,
        (N₂ k : ℝ) ≤ (((parent' (k + 1)).filter (fun i : ι =>
          (W (k + 1) i).toConvexSpaceBody ≤ (W k j).toConvexSpaceBody)).card : ℝ)) ∧
      (∀ k, k < M → ∀ j ∈ parent' k,
        (((parent' (k + 1)).filter (fun i : ι =>
            (W (k + 1) i).toConvexSpaceBody ≤ (W k j).toConvexSpaceBody)).card : ℝ)
          ≤ 8 * (Tube.overlapConstBOTight (Module.finrank ℝ E) : ℝ) * (N₂ k : ℝ)) ∧
      (s'.card : ℝ) ≤ 2 * ((parent' 0).card : ℝ) * (4 : ℝ) ^ M
          * ∏ k ∈ Finset.range M, (N₂ k : ℝ) := by
  classical
  obtain ⟨i₀, hi₀⟩ := hs'_ne
  have hN_pos : ∀ k ≤ M, 0 < N k :=
    band_N_pos M assign parent' N s' hi₀ h_assign'_mem h_active h_band
  have hNM_le : N M ≤ 1 :=
    band_N_last_le_one s M assign parent' N s' hs'_sub hi₀ h_top h_assign'_mem h_band
  set N₂ : ℕ → ℕ := fun k => max 1 (N k / (2 * N (k + 1))) with hN₂_def
  have hN₂_pos : ∀ k, 0 < N₂ k := fun k => lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hchild : ∀ k, k < M → ∀ j ∈ parent' k,
      N₂ k ≤ ((parent' (k + 1)).filter (fun i : ι =>
        (W (k + 1) i).toConvexSpaceBody ≤ (W k j).toConvexSpaceBody)).card := fun k hk j hj =>
    band_child_card_ge s T M ρ W assign parent' N s' hs'_sub h_assign'_mem h_active h_band
      h_level_nest k hk j hj
  have htel : ∀ m, m ≤ M →
      (N 0 : ℝ) ≤ (4 : ℝ) ^ m * (N m : ℝ) * ∏ k ∈ Finset.range m, (N₂ k : ℝ) :=
    band_telescope M N N₂ (fun _ => rfl) hN_pos
  have hchild_le : ∀ k, k < M → ∀ j ∈ parent' k,
      (((parent' (k + 1)).filter (fun i : ι =>
          (W (k + 1) i).toConvexSpaceBody ≤ (W k j).toConvexSpaceBody)).card : ℝ)
        ≤ 8 * (Tube.overlapConstBOTight (Module.finrank ℝ E) : ℝ) * (N₂ k : ℝ) := by
    intro k hk j hj
    have hmul := band_child_card_le s T M ρ W assign parent parent' N s' hs'_sub h_cover h_overlap
      h_parent'_sub h_assign'_mem h_band k hk j hj
    have hstep : N k ≤ 4 * N (k + 1) * N₂ k := by
      rw [hN₂_def]
      exact nat_le_four_mul_max_div (N k) (N (k + 1)) (hN_pos (k + 1) (by omega))
    have hchain : ((parent' (k + 1)).filter (fun i : ι =>
        (W (k + 1) i).toConvexSpaceBody ≤ (W k j).toConvexSpaceBody)).card * N (k + 1)
        ≤ (8 * Tube.overlapConstBOTight (Module.finrank ℝ E) * N₂ k) * N (k + 1) := by
      calc ((parent' (k + 1)).filter (fun i : ι =>
              (W (k + 1) i).toConvexSpaceBody ≤ (W k j).toConvexSpaceBody)).card * N (k + 1)
          ≤ 2 * Tube.overlapConstBOTight (Module.finrank ℝ E) * N k := hmul
        _ ≤ 2 * Tube.overlapConstBOTight (Module.finrank ℝ E) * (4 * N (k + 1) * N₂ k) := by
            exact Nat.mul_le_mul_left _ hstep
        _ = (8 * Tube.overlapConstBOTight (Module.finrank ℝ E) * N₂ k) * N (k + 1) := by ring
    have hNk1_pos : 0 < N (k + 1) := hN_pos (k + 1) (by omega)
    have hnat : ((parent' (k + 1)).filter (fun i : ι =>
        (W (k + 1) i).toConvexSpaceBody ≤ (W k j).toConvexSpaceBody)).card
        ≤ 8 * Tube.overlapConstBOTight (Module.finrank ℝ E) * N₂ k :=
      Nat.le_of_mul_le_mul_right hchain hNk1_pos
    calc (((parent' (k + 1)).filter (fun i : ι =>
            (W (k + 1) i).toConvexSpaceBody ≤ (W k j).toConvexSpaceBody)).card : ℝ)
        ≤ ((8 * Tube.overlapConstBOTight (Module.finrank ℝ E) * N₂ k : ℕ) : ℝ) := by
          exact_mod_cast hnat
      _ = 8 * (Tube.overlapConstBOTight (Module.finrank ℝ E) : ℝ) * (N₂ k : ℝ) := by
          push_cast; ring
  refine ⟨N₂, hN₂_pos, ?_, hchild_le, ?_⟩
  · intro k hk j hj
    exact_mod_cast hchild k hk j hj
  · have hcover : s'.card ≤ 2 * ((parent' 0).card * N 0) :=
      band_card_le_root M assign parent' N s' h_assign'_mem h_band
    have hcover' : (s'.card : ℝ) ≤ 2 * (((parent' 0).card : ℝ) * (N 0 : ℝ)) := by
      exact_mod_cast hcover
    have hN0 := htel M le_rfl
    have hNM' : (N M : ℝ) ≤ 1 := by exact_mod_cast hNM_le
    have hprod_nonneg : (0 : ℝ) ≤ ∏ k ∈ Finset.range M, (N₂ k : ℝ) :=
      Finset.prod_nonneg (fun k _ => Nat.cast_nonneg _)
    have hP0 : (0 : ℝ) ≤ ((parent' 0).card : ℝ) := Nat.cast_nonneg _
    have hchain : (N 0 : ℝ) ≤ (4 : ℝ) ^ M * ∏ k ∈ Finset.range M, (N₂ k : ℝ) := by
      calc (N 0 : ℝ) ≤ (4 : ℝ) ^ M * (N M : ℝ) * ∏ k ∈ Finset.range M, (N₂ k : ℝ) := hN0
        _ ≤ (4 : ℝ) ^ M * 1 * ∏ k ∈ Finset.range M, (N₂ k : ℝ) := by
            gcongr
        _ = (4 : ℝ) ^ M * ∏ k ∈ Finset.range M, (N₂ k : ℝ) := by ring
    calc (s'.card : ℝ) ≤ 2 * (((parent' 0).card : ℝ) * (N 0 : ℝ)) := hcover'
      _ ≤ 2 * (((parent' 0).card : ℝ)
            * ((4 : ℝ) ^ M * ∏ k ∈ Finset.range M, (N₂ k : ℝ))) := by
          gcongr
      _ = 2 * ((parent' 0).card : ℝ) * (4 : ℝ) ^ M
            * ∏ k ∈ Finset.range M, (N₂ k : ℝ) := by ring

open Classical in
/-- **Tight refine-to-uniform pigeonholing for carrier-injective leaves.**  Sharper form of the
refine-to-uniform statement under `Set.InjOn (fun i => (T i).carrier) s`: the polylog exponent is
`M - 1` instead of `M` and the child-count product bound carries no leaf-multiplicity factor.  The
conclusion adds the `[δ,1]` `s'`-leaf-rescale covering at every grid scale `ρ_k`. -/
theorem exists_uniform_subset_tight_injLeaves
    {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ < 1)
    (s : Finset ι) (T : ι → Tube δ E)
    (hT_inj : Set.InjOn (fun i => (T i).carrier) (s : Set ι))
    (M : ℕ) (hM_pos : 0 < M)
    (hgap : (δ : ℝ) ^ ((1 : ℝ) / (M : ℝ)) ≤ 1 / 2)
    (hs_B1 : ∀ ⦃i⦄, i ∈ s → (T i).carrier ⊆ Metric.closedBall (0 : E) 1)
    (hs_ne : s.Nonempty) :
    ∃ s' ⊆ s,
      (∀ ρ₀ ∈ { ρ : NNReal | ∃ k : ℕ, k ≤ M ∧ ρ = δ ^ ((k : ℝ) / (M : ℝ)) },
        ∃ u : IsUniformAtScale s' T ρ₀
            (2 * (Tube.overlapConstBOTight (Module.finrank ℝ E) : NNReal)),
          (1 : NNReal) ≤ u.branchingN ∧
          (ρ₀ ≠ δ → ((u.parent.card : ℝ) ≤
            (641 : ℝ) ^ (2 * Module.finrank ℝ E)
              * ((4 : ℝ) / (ρ₀ : ℝ)) ^ (2 * Module.finrank ℝ E)))) ∧
      (s.card : ℝ) / (((641 : ℝ) ^ (2 * Module.finrank ℝ E) * (4 : ℝ) ^ (2 * Module.finrank ℝ E))
          * ((⌊Real.logb 2 (s.card : ℝ)⌋₊ + 1 : ℝ) ^ (M - 1)))
        ≤ (s'.card : ℝ) ∧
      (∀ k, 1 ≤ k → k ≤ M → ∀ ⦃i⦄, i ∈ s' →
        ∃ j' ∈ s', (T i).toConvexSpaceBody ≤
          ((T j').rescale (δ ^ ((k : ℝ) / (M : ℝ)))).toConvexSpaceBody) ∧
      (∃ (u : ∀ k : Fin (M + 1), IsUniformAtScale s' T (δ ^ ((k.val : ℝ) / (M : ℝ)))
              (2 * (Tube.overlapConstBOTight (Module.finrank ℝ E) : NNReal)))
          (p : ℕ → ι → ι),
        (∀ k : Fin (M + 1), (1 : NNReal) ≤ (u k).branchingN) ∧
        (∀ k : Fin (M + 1), k.val < M → (((u k).parent.card : ℝ) ≤
          (641 : ℝ) ^ (2 * Module.finrank ℝ E)
            * ((4 : ℝ) / ((δ ^ ((k.val : ℝ) / (M : ℝ)) : NNReal) : ℝ))
              ^ (2 * Module.finrank ℝ E))) ∧
        (∀ k : Fin M, ∀ j ∈ (u k.succ).parent,
          p k.val j ∈ (u k.castSucc).parent ∧
            ((u k.succ).parentTube j).toConvexSpaceBody ≤
              ((u k.castSucc).parentTube (p k.val j)).toConvexSpaceBody) ∧
        (∀ k : Fin (M + 1),
          ((u k).parent.card : ℝ) * ((u k).branchingN : ℝ) ≤ (s'.card : ℝ) ∧
            (s'.card : ℝ) ≤ 2 * (((u k).parent.card : ℝ) * ((u k).branchingN : ℝ))) ∧
        (∃ N₂ : ℕ → ℕ, (∀ k, 0 < N₂ k) ∧
          (∀ k : Fin M, ∀ j ∈ (u k.castSucc).parent,
            (N₂ k.val : ℝ) ≤ (((u k.succ).parent.filter (fun i : ι =>
              ((u k.succ).parentTube i).toConvexSpaceBody ≤
                ((u k.castSucc).parentTube j).toConvexSpaceBody)).card : ℝ)) ∧
          (∀ k : Fin M, ∀ j ∈ (u k.castSucc).parent,
            (((u k.succ).parent.filter (fun i : ι =>
                ((u k.succ).parentTube i).toConvexSpaceBody ≤
                  ((u k.castSucc).parentTube j).toConvexSpaceBody)).card : ℝ)
              ≤ 8 * (Tube.overlapConstBOTight (Module.finrank ℝ E) : ℝ) * (N₂ k.val : ℝ)) ∧
          (s'.card : ℝ) ≤ 2 * ((641 : ℝ) ^ (2 * Module.finrank ℝ E)
                * (4 : ℝ) ^ (2 * Module.finrank ℝ E)) * (4 : ℝ) ^ M
              * ∏ k ∈ Finset.range M, (N₂ k : ℝ))) := by
  classical
  set ρ : ℕ → NNReal := fun k => δ ^ ((k : ℝ) / (M : ℝ)) with hρ_def
  obtain ⟨parent, assign, root, W, h_assign_mem, h_top, h_nested,
      h_cover, _h_leaf_body, _h_leaf_carrier, h_injOn, h_overlap, h_rescale, hPcard_builder,
      h_level_nest⟩ :=
    exists_multiscale_tube_tree_bo_tight hδ hδ1 s T hT_inj M hM_pos hgap hs_B1 hs_ne
  set C₀ : ℝ := (641 : ℝ) ^ (2 * Module.finrank ℝ E) * (4 : ℝ) ^ (2 * Module.finrank ℝ E)
    with hC₀_def
  have hC₀_pos : (0 : ℝ) < C₀ := by rw [hC₀_def]; positivity
  have hC₀ : ((parent 0).card : ℝ) ≤ C₀ := by
    have h := hPcard_builder 0 hM_pos
    have hρ0 : ((ρ 0 : NNReal) : ℝ) = 1 := by
      simp only [hρ_def, Nat.cast_zero, zero_div, NNReal.rpow_zero, NNReal.coe_one]
    rw [hρ0] at h
    simpa [hC₀_def] using h
  obtain ⟨s', N, parent', hs'_sub, hs'_card, h_parent'_sub, h_assign'_mem,
      h_active, h_band⟩ :=
    exists_pruned_subset_noroot s M hs_ne parent assign h_assign_mem h_top h_nested
      C₀ hC₀_pos hC₀
  have hs'_ne : s'.Nonempty := by
    rw [← Finset.card_pos]
    have hnum : (0 : ℝ) < (s.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hs_ne
    have hden : (0 : ℝ) < C₀ * ((⌊Real.logb 2 (s.card : ℝ)⌋₊ + 1 : ℝ) ^ (M - 1)) := by
      have : (0 : ℝ) < ((⌊Real.logb 2 (s.card : ℝ)⌋₊ + 1 : ℝ) ^ (M - 1)) := by positivity
      exact mul_pos hC₀_pos this
    have h0 : (0 : ℝ) < (s'.card : ℝ) := lt_of_lt_of_le (div_pos hnum hden) hs'_card
    exact_mod_cast h0
  refine ⟨s', hs'_sub, ?_, hs'_card, ?_, ?_⟩
  · intro ρ0 hρ0
    obtain ⟨k, hk, rfl⟩ := hρ0
    have hρk : ρ k = δ ^ ((k : ℝ) / (M : ℝ)) := rfl
    rw [← hρk]
    obtain ⟨u, hbn, hcount, _hu_parent, _hu_parentTube, _hu_bn⟩ :=
      isUniformAtScale_of_pruned_tight hδ hδ1 s T M ρ
      (fun k => NNReal.rpow_pos hδ)
      parent assign W
      h_cover h_injOn h_overlap s' N parent' hs'_sub h_parent'_sub h_assign'_mem
      h_active h_band hs'_ne hPcard_builder hk
    refine ⟨u, hbn, ?_⟩
    intro hne
    apply hcount
    rcases lt_or_eq_of_le hk with hlt | heq
    · exact hlt
    · exfalso; apply hne
      rw [hρk, heq]
      show (δ : NNReal) ^ ((M : ℝ) / (M : ℝ)) = δ
      rw [div_self (by exact_mod_cast hM_pos.ne'), NNReal.rpow_one]
  · intro k hk1 hkM i hi
    have hpar : assign k i ∈ parent' k := h_assign'_mem k hkM hi
    obtain ⟨j', hj'⟩ := Finset.card_pos.mp (h_active k hkM (assign k i) hpar)
    rw [Finset.mem_filter] at hj'
    obtain ⟨hj's', hj'eq⟩ := hj'
    exact ⟨j', hj's', h_rescale k hk1 hkM (hs'_sub hi) (hs'_sub hj's') hj'eq.symm⟩
  · have hforall : ∀ (k : ℕ), k ≤ M → ∃ u : IsUniformAtScale s' T (ρ k)
        (2 * (Tube.overlapConstBOTight (Module.finrank ℝ E) : NNReal)),
      (1 : NNReal) ≤ u.branchingN ∧
      (k < M → ((u.parent.card : ℝ) ≤
        (641 : ℝ) ^ (2 * Module.finrank ℝ E)
          * ((4 : ℝ) / ((ρ k : NNReal) : ℝ)) ^ (2 * Module.finrank ℝ E))) ∧
      u.parent = parent' k ∧ u.parentTube = W k ∧ u.branchingN = (N k : NNReal) := by
      intro k hk
      exact isUniformAtScale_of_pruned_tight hδ hδ1 s T M ρ
        (fun k => NNReal.rpow_pos hδ)
        parent assign W
        h_cover h_injOn h_overlap s' N parent' hs'_sub h_parent'_sub h_assign'_mem
        h_active h_band hs'_ne hPcard_builder hk
    set u : ∀ k : Fin (M + 1), IsUniformAtScale s' T (δ ^ ((k.val : ℝ) / (M : ℝ)))
        (2 * (Tube.overlapConstBOTight (Module.finrank ℝ E) : NNReal)) :=
      fun k => (hforall k.val (by
        have hk_val_lt : k.val < M + 1 := k.2
        omega)).choose with hu_def
    have hu_spec : ∀ k : Fin (M + 1),
      (1 : NNReal) ≤ (u k).branchingN ∧
      (k.val < M → (((u k).parent.card : ℝ) ≤
        (641 : ℝ) ^ (2 * Module.finrank ℝ E)
          * ((4 : ℝ) / ((δ ^ ((k.val : ℝ) / (M : ℝ)) : NNReal) : ℝ)) ^ (2 * Module.finrank ℝ E))) ∧
      (u k).parent = parent' (k.val) ∧ (u k).parentTube = W (k.val) ∧
      (u k).branchingN = (N (k.val) : NNReal) := by
      intro k
      dsimp [u]
      have hk_val_le_M : k.val ≤ M := by
        have hk : k.val < M + 1 := k.2
        omega
      rcases (hforall k.val hk_val_le_M).choose_spec with ⟨hbn, hcount, hpar, htube, hbnval⟩
      refine ⟨hbn, ?_, hpar, htube, hbnval⟩
      intro hkM
      have hbound := hcount hkM
      simpa [show ρ (k.val) = δ ^ ((k.val : ℝ) / (M : ℝ)) from rfl] using hbound
    set p : ℕ → ι → ι := fun k j =>
      if h : ∃ i, i ∈ s' ∧ assign (k + 1) i = j then assign k h.choose else j with hp_def
    refine ⟨u, p, ?_, ?_, ?_, ?_, ?_⟩
    · intro k
      exact (hu_spec k).1
    · intro k hk_val_lt_M
      exact (hu_spec k).2.1 hk_val_lt_M
    · intro k j hj
      have hk_val_lt_M : k.val < M := k.2
      have hksucc_val_eq : (k.succ).val = k.val + 1 := by simp
      have hkcast_val_eq : (k.castSucc).val = k.val := by simp
      have hpar_succ : (u k.succ).parent = parent' ((k.succ).val) := (hu_spec k.succ).2.2.1
      have hpar_castSucc : (u k.castSucc).parent = parent' ((k.castSucc).val) :=
        (hu_spec k.castSucc).2.2.1
      have htube_succ : (u k.succ).parentTube = W ((k.succ).val) := (hu_spec k.succ).2.2.2.1
      have htube_castSucc : (u k.castSucc).parentTube = W ((k.castSucc).val) :=
        (hu_spec k.castSucc).2.2.2.1
      have hj_parent' : j ∈ parent' ((k.succ).val) := by
        rw [hpar_succ] at hj
        exact hj
      have h_active_pos : 0 < (s'.filter (fun i => assign ((k.succ).val) i = j)).card :=
        h_active ((k.succ).val) (by
          have h : (k.succ).val < M + 1 := k.succ.2
          omega) j hj_parent'
      obtain ⟨i, hi⟩ := Finset.card_pos.mp h_active_pos
      rw [Finset.mem_filter] at hi
      obtain ⟨hi_s', hi_assign⟩ := hi
      have hi_assign_succ : assign (k.val + 1) i = j := by
        simpa [hksucc_val_eq] using hi_assign
      have hi_s : i ∈ s := hs'_sub hi_s'
      have h_exists_p : ∃ i, i ∈ s' ∧ assign (k.val + 1) i = j := ⟨i, hi_s', hi_assign_succ⟩
      have hp_val : p k.val j = assign k.val i := by
        dsimp [p]
        have h_temp_spec : h_exists_p.choose ∈ s' ∧ assign (k.val + 1) h_exists_p.choose = j :=
          h_exists_p.choose_spec
        have h_choose_s : h_exists_p.choose ∈ s := hs'_sub h_temp_spec.1
        have h_eq_assign_succ : assign (k.val + 1) i = assign (k.val + 1) h_exists_p.choose := by
          calc
            assign (k.val + 1) i = j := hi_assign_succ
            _ = assign (k.val + 1) h_exists_p.choose := h_temp_spec.2.symm
        have h_nested_eq : assign k.val i = assign k.val h_exists_p.choose :=
          h_nested (k.val) hk_val_lt_M hi_s h_choose_s h_eq_assign_succ
        rw [dif_pos h_exists_p, h_nested_eq]
      have h_mem_goal : p k.val j ∈ (u k.castSucc).parent := by
        rw [hpar_castSucc, hkcast_val_eq, hp_val]
        exact h_assign'_mem k.val (by omega) hi_s'
      have h_contain_goal :
        ((u k.succ).parentTube j).toConvexSpaceBody ≤
          ((u k.castSucc).parentTube (p k.val j)).toConvexSpaceBody := by
        rw [htube_succ, htube_castSucc, hp_val]
        calc
          (W ((k.succ).val) j).toConvexSpaceBody
              = (W (k.val + 1) (assign (k.val + 1) i)).toConvexSpaceBody := by
                rw [hksucc_val_eq, hi_assign_succ]
          _ ≤ (W k.val (assign k.val i)).toConvexSpaceBody :=
                h_level_nest (k.val) hk_val_lt_M hi_s
          _ = (W ((k.castSucc).val) (assign k.val i)).toConvexSpaceBody := by
                rw [← hkcast_val_eq]
      exact ⟨h_mem_goal, h_contain_goal⟩
    · intro k
      have hk_le_M : k.val ≤ M := by
        have hk : k.val < M + 1 := k.2
        omega
      obtain ⟨-, -, hpar, -, hbn⟩ := hu_spec k
      have hfib : s'.card
          = ∑ v ∈ parent' k.val, (s'.filter (fun i => assign k.val i = v)).card :=
        Finset.card_eq_sum_card_fiberwise (fun i hi => h_assign'_mem k.val hk_le_M hi)
      have hlow : (parent' k.val).card * N k.val ≤ s'.card := by
        rw [hfib]
        calc (parent' k.val).card * N k.val
            = ∑ _v ∈ parent' k.val, N k.val := by
              rw [Finset.sum_const, smul_eq_mul]
          _ ≤ ∑ v ∈ parent' k.val, (s'.filter (fun i => assign k.val i = v)).card :=
              Finset.sum_le_sum (fun v hv => (h_band k.val hk_le_M v hv).1)
      have hhigh : s'.card ≤ 2 * ((parent' k.val).card * N k.val) := by
        rw [hfib]
        calc ∑ v ∈ parent' k.val, (s'.filter (fun i => assign k.val i = v)).card
            ≤ ∑ _v ∈ parent' k.val, 2 * N k.val :=
              Finset.sum_le_sum (fun v hv => (h_band k.val hk_le_M v hv).2.le)
          _ = 2 * ((parent' k.val).card * N k.val) := by
              rw [Finset.sum_const, smul_eq_mul]; ring
      rw [hpar, hbn]
      refine ⟨?_, ?_⟩
      · push_cast
        exact_mod_cast hlow
      · push_cast
        exact_mod_cast hhigh
    · obtain ⟨N₂, hN₂_pos, hN₂_child, hN₂_child_le, hN₂_prod⟩ :=
        exists_child_count_of_band s T M ρ W assign parent parent' N s' hs'_sub hs'_ne h_top
          h_nested h_cover h_overlap h_parent'_sub h_assign'_mem h_active h_band h_level_nest
      have hP0_le : ((parent' 0).card : ℝ) ≤ (641 : ℝ) ^ (2 * Module.finrank ℝ E)
          * (4 : ℝ) ^ (2 * Module.finrank ℝ E) := by
        refine le_trans ?_ hC₀
        exact_mod_cast Finset.card_le_card (h_parent'_sub 0 (Nat.zero_le M))
      refine ⟨N₂, hN₂_pos, ?_, ?_, ?_⟩
      · intro k j hj
        have hk_lt : k.val < M := k.2
        obtain ⟨-, -, hpar_cs, htube_cs, -⟩ := hu_spec k.castSucc
        obtain ⟨-, -, hpar_sc, htube_sc, -⟩ := hu_spec k.succ
        have hcs : (k.castSucc).val = k.val := by simp
        have hsc : (k.succ).val = k.val + 1 := by simp
        rw [hpar_cs, hcs] at hj
        have hmain := hN₂_child k.val hk_lt j hj
        rw [hpar_sc, htube_sc, htube_cs, hsc, hcs]
        exact hmain
      · intro k j hj
        have hk_lt : k.val < M := k.2
        obtain ⟨-, -, hpar_cs, htube_cs, -⟩ := hu_spec k.castSucc
        obtain ⟨-, -, hpar_sc, htube_sc, -⟩ := hu_spec k.succ
        have hcs : (k.castSucc).val = k.val := by simp
        have hsc : (k.succ).val = k.val + 1 := by simp
        rw [hpar_cs, hcs] at hj
        have hmain := hN₂_child_le k.val hk_lt j hj
        rw [hpar_sc, htube_sc, htube_cs, hsc, hcs]
        exact hmain
      · refine le_trans hN₂_prod ?_
        have hprod_nonneg : (0 : ℝ) ≤ ∏ kk ∈ Finset.range M, (N₂ kk : ℝ) :=
          Finset.prod_nonneg (fun kk _ => Nat.cast_nonneg _)
        gcongr

/-- (blueprint `lem:refineToEssDistinctUniform`)  Combining the leaf-scale essentially-distinct
reduction `Tube.refineToEssDistinctLeaves` with the refine-to-uniform pigeonholing
`exists_uniform_subset_tight_injLeaves`: a family of `δ`-tubes in `B_1` with maximal density
`≤ D < ⊤` has a subfamily that is *at once* pairwise essentially distinct and uniform at every scale
of the `M`-grid, with cardinality down by at most `C_n · D · polylog(|s|)^{M-1}`. -/
theorem refineToEssDistinctUniform
    {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ < 1)
    (s : Finset ι) (T : ι → Tube δ E)
    (M : ℕ) (hM_pos : 0 < M)
    (hgap : (δ : ℝ) ^ ((1 : ℝ) / (M : ℝ)) ≤ 1 / 2)
    (hs_B1 : ∀ ⦃i⦄, i ∈ s → (T i).carrier ⊆ Metric.closedBall (0 : E) 1)
    (hs_ne : s.Nonempty)
    {D : ENNReal} (_hD_ne : D ≠ ⊤)
    (hD : Kakeya.maxDensity s (fun i => (T i).toConvexSpaceBody) ≤ D) :
    ∃ s' ⊆ s,
      (↑s' : Set ι).Pairwise
          (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) ∧
      (∀ ρ₀ ∈ { ρ : NNReal | ∃ k : ℕ, k ≤ M ∧ ρ = δ ^ ((k : ℝ) / (M : ℝ)) },
        ∃ u : IsUniformAtScale s' T ρ₀
            (2 * (Tube.overlapConstBOTight (Module.finrank ℝ E) : NNReal)),
          (1 : NNReal) ≤ u.branchingN ∧
          (ρ₀ ≠ δ → ((u.parent.card : ℝ) ≤
            (641 : ℝ) ^ (2 * Module.finrank ℝ E)
              * ((4 : ℝ) / (ρ₀ : ℝ)) ^ (2 * Module.finrank ℝ E)))) ∧
      s'.Nonempty ∧
      (s.card : ENNReal) ≤
        Kakeya.Tube.refineToEssDistinctLeaves.C (Module.finrank ℝ E) * D
          * ENNReal.ofReal
              (((641 : ℝ) ^ (2 * Module.finrank ℝ E) * (4 : ℝ) ^ (2 * Module.finrank ℝ E))
                * (⌊Real.logb 2 (s.card : ℝ)⌋₊ + 1 : ℝ) ^ (M - 1))
          * (s'.card : ENNReal) ∧
      (∃ (u : ∀ k : Fin (M + 1), IsUniformAtScale s' T (δ ^ ((k.val : ℝ) / (M : ℝ)))
              (2 * (Tube.overlapConstBOTight (Module.finrank ℝ E) : NNReal)))
          (p : ℕ → ι → ι),
        (∀ k : Fin (M + 1), (1 : NNReal) ≤ (u k).branchingN) ∧
        (∀ k : Fin (M + 1), k.val < M → (((u k).parent.card : ℝ) ≤
          (641 : ℝ) ^ (2 * Module.finrank ℝ E)
            * ((4 : ℝ) / ((δ ^ ((k.val : ℝ) / (M : ℝ)) : NNReal) : ℝ))
              ^ (2 * Module.finrank ℝ E))) ∧
        (∀ k : Fin M, ∀ j ∈ (u k.succ).parent,
          p k.val j ∈ (u k.castSucc).parent ∧
            ((u k.succ).parentTube j).toConvexSpaceBody ≤
              ((u k.castSucc).parentTube (p k.val j)).toConvexSpaceBody) ∧
        (∀ k : Fin (M + 1),
          ((u k).parent.card : ℝ) * ((u k).branchingN : ℝ) ≤ (s'.card : ℝ) ∧
            (s'.card : ℝ) ≤ 2 * (((u k).parent.card : ℝ) * ((u k).branchingN : ℝ))) ∧
        (∃ N₂ : ℕ → ℕ, (∀ k, 0 < N₂ k) ∧
          (∀ k : Fin M, ∀ j ∈ (u k.castSucc).parent,
            (N₂ k.val : ℝ) ≤ (((u k.succ).parent.filter (fun i : ι =>
              ((u k.succ).parentTube i).toConvexSpaceBody ≤
                ((u k.castSucc).parentTube j).toConvexSpaceBody)).card : ℝ)) ∧
          (∀ k : Fin M, ∀ j ∈ (u k.castSucc).parent,
            (((u k.succ).parent.filter (fun i : ι =>
                ((u k.succ).parentTube i).toConvexSpaceBody ≤
                  ((u k.castSucc).parentTube j).toConvexSpaceBody)).card : ℝ)
              ≤ 8 * (Tube.overlapConstBOTight (Module.finrank ℝ E) : ℝ) * (N₂ k.val : ℝ)) ∧
          (s'.card : ℝ) ≤ 2 * ((641 : ℝ) ^ (2 * Module.finrank ℝ E)
                * (4 : ℝ) ^ (2 * Module.finrank ℝ E)) * (4 : ℝ) ^ M
              * ∏ k ∈ Finset.range M, (N₂ k : ℝ))) := by
  classical
  set C := Kakeya.Tube.refineToEssDistinctLeaves.C (Module.finrank ℝ E) with hC_def
  have hδ1_le : δ ≤ 1 := hδ1.le
  obtain ⟨s0, hs0_sub, hpair, hcard_le⟩ :=
    Kakeya.Tube.refineToEssDistinctLeaves hδ hδ1_le s T hD
  have h_injOn_s0 : Set.InjOn (fun i => (T i).carrier) (s0 : Set ι) := by
    intro i hi j hj h_eq
    by_contra hne
    have hED := hpair hi hj hne
    have hED' : IsEssentiallyDistinct (T i).carrier (T j).carrier := hED
    have h_eq' : (T i).carrier = (T j).carrier := by
      simpa using h_eq
    rw [h_eq'] at hED'
    have hvol_pos : volume (T j).carrier ≠ 0 := by
      have h1 : (0 : NNReal) <
          Tube.le_volume.c (Module.finrank ℝ E) * δ ^ (Module.finrank ℝ E - 1) :=
        mul_pos (Tube.le_volume.c_pos _) (pow_pos hδ _)
      exact ne_of_gt (lt_of_lt_of_le (by exact_mod_cast h1) (Tube.le_volume (T j)))
    exact absurd hED'
      (not_isEssentiallyDistinct_self hvol_pos (T j).isCompact.measure_lt_top.ne)
  have hs0_ne : s0.Nonempty := by
    by_contra h0
    have hs0_empty : s0 = ∅ := Finset.not_nonempty_iff_eq_empty.mp h0
    have hcards0 : (s0.card : ENNReal) = 0 := by
      simp [hs0_empty]
    have hcard0 : (s.card : ENNReal) ≤ 0 := by
      calc
        (s.card : ENNReal) ≤ C * D * (s0.card : ENNReal) := hcard_le
        _ = C * D * (0 : ENNReal) := by rw [hcards0]
        _ = 0 := by simp
    have hcard_pos : (0 : ENNReal) < (s.card : ENNReal) :=
      Nat.cast_pos.mpr (Finset.card_pos.mpr hs_ne)
    exact not_lt.mpr hcard0 hcard_pos
  have hs_B1_s0 : ∀ ⦃i⦄, i ∈ s0 → (T i).carrier ⊆ Metric.closedBall (0 : E) 1 := by
    intro i hi
    exact hs_B1 (hs0_sub hi)
  obtain ⟨s', hs'_sub_s0, huniform_card⟩ :=
    exists_uniform_subset_tight_injLeaves hδ hδ1 s0 T h_injOn_s0 M hM_pos hgap hs_B1_s0 hs0_ne
  rcases huniform_card with ⟨huniform, hcard_s0_s', hrescale, hbundle⟩
  have hs'_ne : s'.Nonempty := by
    by_contra h0
    have hs'_empty : s' = ∅ := Finset.not_nonempty_iff_eq_empty.mp h0
    have hcard_s' : (s'.card : ℝ) = 0 := by
      simp [hs'_empty]
    have hcard_s0_pos : (0 : ℝ) < (s0.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr hs0_ne
    have hL0_pos : (0 : ℝ) <
        ((641 : ℝ) ^ (2 * Module.finrank ℝ E) * (4 : ℝ) ^ (2 * Module.finrank ℝ E))
          * ((⌊Real.logb 2 (s0.card : ℝ)⌋₊ + 1 : ℝ) ^ (M - 1)) := by
      positivity
    have hdiv : (s0.card : ℝ) /
        (((641 : ℝ) ^ (2 * Module.finrank ℝ E) * (4 : ℝ) ^ (2 * Module.finrank ℝ E))
          * ((⌊Real.logb 2 (s0.card : ℝ)⌋₊ + 1 : ℝ) ^ (M - 1))) ≤ (0 : ℝ) := by
      calc
        (s0.card : ℝ) /
            (((641 : ℝ) ^ (2 * Module.finrank ℝ E) * (4 : ℝ) ^ (2 * Module.finrank ℝ E))
              * ((⌊Real.logb 2 (s0.card : ℝ)⌋₊ + 1 : ℝ) ^ (M - 1))) ≤ (s'.card : ℝ) :=
          hcard_s0_s'
        _ = 0 := hcard_s'
    have hpos_div : (0 : ℝ) < (s0.card : ℝ) /
        (((641 : ℝ) ^ (2 * Module.finrank ℝ E) * (4 : ℝ) ^ (2 * Module.finrank ℝ E))
          * ((⌊Real.logb 2 (s0.card : ℝ)⌋₊ + 1 : ℝ) ^ (M - 1))) :=
      div_pos hcard_s0_pos hL0_pos
    linarith
  have hpair_s' : (↑s' : Set ι).Pairwise
      (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) :=
    hpair.mono (Finset.coe_subset.mpr hs'_sub_s0)
  have hcard_goal : (s.card : ENNReal) ≤ C * D
      * ENNReal.ofReal
          (((641 : ℝ) ^ (2 * Module.finrank ℝ E) * (4 : ℝ) ^ (2 * Module.finrank ℝ E))
            * (⌊Real.logb 2 (s.card : ℝ)⌋₊ + 1 : ℝ) ^ (M - 1))
      * (s'.card : ENNReal) := by
    set C₀ : ℝ :=
      (641 : ℝ) ^ (2 * Module.finrank ℝ E) * (4 : ℝ) ^ (2 * Module.finrank ℝ E) with hC₀_def
    have hC₀_pos : (0 : ℝ) < C₀ := by rw [hC₀_def]; positivity
    set L := C₀ * (⌊Real.logb 2 (s.card : ℝ)⌋₊ + 1 : ℝ) ^ (M - 1) with hL_def
    set L0 := C₀ * (⌊Real.logb 2 (s0.card : ℝ)⌋₊ + 1 : ℝ) ^ (M - 1) with hL0_def
    have hL0_pos' : (0 : ℝ) < L0 := by
      rw [hL0_def]; positivity
    have hL_nonneg : (0 : ℝ) ≤ L := by
      rw [hL_def]; positivity
    have hcard_s0_s'ℝ : (s0.card : ℝ) ≤ (s'.card : ℝ) * L0 := by
      rw [div_le_iff₀ hL0_pos'] at hcard_s0_s'
      exact hcard_s0_s'
    have hcard_s0_le_s_nat : s0.card ≤ s.card := Finset.card_le_card hs0_sub
    have hcard_s0_le_s : (s0.card : ℝ) ≤ (s.card : ℝ) := by exact_mod_cast hcard_s0_le_s_nat
    have hcard_s0_pos_nat : 0 < s0.card := Finset.card_pos.mpr hs0_ne
    have hcard_s_pos_nat : 0 < s.card := Finset.card_pos.mpr hs_ne
    have hcard_s0_pos' : (0 : ℝ) < (s0.card : ℝ) := by exact_mod_cast hcard_s0_pos_nat
    have hcard_s_pos' : (0 : ℝ) < (s.card : ℝ) := by exact_mod_cast hcard_s_pos_nat
    have h_logb_le : Real.logb 2 (s0.card : ℝ) ≤ Real.logb 2 (s.card : ℝ) :=
      Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hcard_s0_pos' hcard_s0_le_s
    have h_floor_le : (⌊Real.logb 2 (s0.card : ℝ)⌋₊ : ℝ) ≤ (⌊Real.logb 2 (s.card : ℝ)⌋₊ : ℝ) := by
      have h_floor_nat : (⌊Real.logb 2 (s0.card : ℝ)⌋₊ : ℕ) ≤ (⌊Real.logb 2 (s.card : ℝ)⌋₊ : ℕ) :=
        Nat.floor_mono h_logb_le
      exact_mod_cast h_floor_nat
    have hL0_le_L : L0 ≤ L := by
      rw [hL0_def, hL_def]
      have h_base : (⌊Real.logb 2 (s0.card : ℝ)⌋₊ + 1 : ℝ) ≤
        (⌊Real.logb 2 (s.card : ℝ)⌋₊ + 1 : ℝ) := by
        linarith
      have h_base_nonneg : 0 ≤ (⌊Real.logb 2 (s0.card : ℝ)⌋₊ + 1 : ℝ) := by positivity
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ h_base_nonneg h_base (M - 1)) hC₀_pos.le
    have hcard_s0_s'L : (s0.card : ℝ) ≤ (s'.card : ℝ) * L := by
      calc
        (s0.card : ℝ) ≤ (s'.card : ℝ) * L0 := hcard_s0_s'ℝ
        _ ≤ (s'.card : ℝ) * L :=
          mul_le_mul_of_nonneg_left hL0_le_L (by norm_num : (0 : ℝ) ≤ (s'.card : ℝ))
    have hcard_s0_ENN : (s0.card : ENNReal) ≤ (s'.card : ENNReal) * ENNReal.ofReal L := by
      calc
        (s0.card : ENNReal) = ENNReal.ofReal (s0.card : ℝ) := by
          simp
        _ ≤ ENNReal.ofReal ((s'.card : ℝ) * L) := ENNReal.ofReal_le_ofReal hcard_s0_s'L
        _ = ENNReal.ofReal (s'.card : ℝ) * ENNReal.ofReal L := by
          rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (s'.card : ℝ))]
        _ = (s'.card : ENNReal) * ENNReal.ofReal L := by simp
    calc
      (s.card : ENNReal) ≤ C * D * (s0.card : ENNReal) := hcard_le
      _ ≤ C * D * ((s'.card : ENNReal) * ENNReal.ofReal L) :=
        mul_le_mul_of_nonneg_left hcard_s0_ENN (by positivity : (0 : ENNReal) ≤ C * D)
      _ = C * D * ENNReal.ofReal L * (s'.card : ENNReal) := by ring
  exact ⟨s', Finset.Subset.trans hs'_sub_s0 hs0_sub, hpair_s', huniform, hs'_ne, hcard_goal,
    hbundle⟩

end Tube
