import MyLeanRepo.Kakeya.Cinematic.Geometry
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Finset.Card

/-!
# Deterministic sampling for the bipartite reduction

The paper phrases this step probabilistically.  A greedy averaging argument
gives the exact finite statement needed below: after sampling both colors,
a fixed positive proportion of the rectangles survives while the sampled
cardinalities are controlled by the normalized multiplicities.
-/

namespace Kakeya.Cinematic

open Finset

section GreedyCover

variable {W R : Type*} [DecidableEq W] [DecidableEq R]

lemma greedy_cover
    (W_set : Finset W) (R_set : Finset R)
    (A : W → Finset R) (m : ℕ) (hm_pos : 0 < m)
    (hA_sub : ∀ w, A w ⊆ R_set)
    (hcover : ∀ r ∈ R_set,
      m ≤ (W_set.filter (fun w => r ∈ A w)).card) :
    ∃ W' : Finset W,
      W' ⊆ W_set ∧
      (W'.card : ℝ) ≤ 2 * (W_set.card : ℝ) / (m : ℝ) ∧
      (1 - Real.exp (-1)) * (R_set.card : ℝ) ≤
        ((R_set.filter (fun r => ∃ w ∈ W', r ∈ A w)).card : ℝ) := by
  by_cases hm1 : m = 1
  · subst hm1
    have hcov_all :
        R_set.filter (fun r => ∃ w ∈ W_set, r ∈ A w) = R_set := by
      ext r
      simp only [Finset.mem_filter]
      constructor
      · exact fun h => h.1
      · intro hr
        have hcard : 1 ≤ (W_set.filter (fun w => r ∈ A w)).card :=
          hcover r hr
        have hnonempty :
            (W_set.filter (fun w => r ∈ A w)).Nonempty := by
          simpa [Finset.card_pos] using hcard
        rcases hnonempty with ⟨w, hw⟩
        exact ⟨hr, w, (Finset.mem_filter.mp hw).1,
          (Finset.mem_filter.mp hw).2⟩
    refine ⟨W_set, by simp, ?_, ?_⟩
    · have hcard : (0 : ℝ) ≤ (W_set.card : ℝ) := by positivity
      nlinarith
    · rw [hcov_all]
      have hexp : 0 < Real.exp (-1) := Real.exp_pos _
      have hcard : 0 ≤ (R_set.card : ℝ) := by positivity
      nlinarith
  · have hm2 : 2 ≤ m := by omega
    by_cases hmN : m ≤ W_set.card
    · let N := W_set.card
      have hN_pos : 0 < N := lt_of_lt_of_le hm_pos hmN
      let k : ℕ := N / m + 1
      have hk_le_N : k ≤ N := by
        have hhalf : N / m ≤ N / 2 := by
          rw [Nat.le_div_iff_mul_le (by norm_num)]
          have hmul : 2 * (N / m) ≤ m * (N / m) :=
            mul_le_mul_of_nonneg_right hm2 (by positivity)
          have hdiv : m * (N / m) ≤ N := by
            simpa [mul_comm] using Nat.div_mul_le_self N m
          simpa [mul_comm] using hmul.trans hdiv
        omega
      have hk_real :
          (k : ℝ) ≤ 2 * (N : ℝ) / (m : ℝ) := by
        have hm_real : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm_pos
        have hdiv_le :
            ((N / m : ℕ) : ℝ) ≤ (N : ℝ) / (m : ℝ) := by
          rw [le_div_iff₀ hm_real]
          exact_mod_cast Nat.div_mul_le_self N m
        have hone_le : 1 ≤ (N : ℝ) / (m : ℝ) := by
          rw [le_div_iff₀ hm_real]
          simpa using (show (m : ℝ) ≤ (N : ℝ) by exact_mod_cast hmN)
        let q : ℝ := (N / m : ℕ)
        have hq : q ≤ (N : ℝ) / (m : ℝ) := by
          simpa [q] using hdiv_le
        have hk_cast : (k : ℝ) = q + 1 := by
          simp [k, q]
        rw [hk_cast]
        have : q + 1 ≤
            (N : ℝ) / (m : ℝ) + (N : ℝ) / (m : ℝ) := by
          linarith
        calc
          q + 1 ≤
              (N : ℝ) / (m : ℝ) + (N : ℝ) / (m : ℝ) := this
          _ = 2 * (N : ℝ) / (m : ℝ) := by ring
      have hinduction : ∀ j : ℕ, ∃ W' : Finset W,
          W' ⊆ W_set ∧ W'.card ≤ j ∧
          ((R_set.filter
              (fun r => ¬ ∃ w ∈ W', r ∈ A w)).card : ℝ) ≤
            (R_set.card : ℝ) *
              (1 - (m : ℝ) / (N : ℝ)) ^ j := by
        intro j
        induction j with
        | zero =>
            refine ⟨∅, by simp, by simp, ?_⟩
            simp
        | succ j ih =>
            rcases ih with ⟨W', hW'_sub, hW'_card, hremain⟩
            let remaining :=
              R_set.filter (fun r => ¬ ∃ w ∈ W', r ∈ A w)
            by_cases hempty : remaining = ∅
            · refine ⟨W', hW'_sub, by omega, ?_⟩
              have hbase :
                  0 ≤ 1 - (m : ℝ) / (N : ℝ) := by
                have hN_real : (0 : ℝ) < (N : ℝ) := by
                  exact_mod_cast hN_pos
                rw [sub_nonneg, div_le_one hN_real]
                exact_mod_cast hmN
              have hfilter :
                  R_set.filter (fun r => ¬ ∃ w ∈ W', r ∈ A w) =
                    remaining := rfl
              rw [hfilter, hempty]
              simp only [Finset.card_empty, Nat.cast_zero]
              exact mul_nonneg (Nat.cast_nonneg' R_set.card)
                (pow_nonneg hbase (j + 1))
            · have hW_nonempty : W_set.Nonempty :=
                Finset.card_pos.mp hN_pos
              obtain ⟨best, hbest, hmax⟩ :=
                Finset.exists_max_image W_set
                  (fun w => (A w ∩ remaining).card) hW_nonempty
              have hsum :
                  m * remaining.card ≤
                    ∑ w ∈ W_set, (A w ∩ remaining).card := by
                have hswap :
                    ∑ w ∈ W_set, (A w ∩ remaining).card =
                      ∑ r ∈ remaining,
                        (W_set.filter (fun w => r ∈ A w)).card := by
                  have hleft : ∀ w ∈ W_set,
                      (A w ∩ remaining).card =
                        ∑ r ∈ remaining,
                          if r ∈ A w then (1 : ℕ) else 0 := by
                    intro w _
                    have hfilter :
                        (∑ r ∈ remaining,
                            if r ∈ A w then (1 : ℕ) else 0) =
                          (remaining.filter (fun r => r ∈ A w)).card := by
                      rw [Finset.sum_ite]
                      simp
                    have hinter :
                        remaining.filter (fun r => r ∈ A w) =
                          A w ∩ remaining := by
                      ext r
                      simp [and_comm]
                    rw [hfilter, hinter]
                  calc
                    ∑ w ∈ W_set, (A w ∩ remaining).card =
                        ∑ w ∈ W_set, ∑ r ∈ remaining,
                          if r ∈ A w then (1 : ℕ) else 0 := by
                      apply Finset.sum_congr rfl
                      exact hleft
                    _ = ∑ r ∈ remaining, ∑ w ∈ W_set,
                          if r ∈ A w then (1 : ℕ) else 0 := by
                      rw [Finset.sum_comm]
                    _ = ∑ r ∈ remaining,
                          (W_set.filter (fun w => r ∈ A w)).card := by
                      apply Finset.sum_congr rfl
                      intro r _
                      rw [Finset.sum_ite]
                      simp
                calc
                  m * remaining.card =
                      ∑ r ∈ remaining, m := by simp [mul_comm]
                  _ ≤
                      ∑ r ∈ remaining,
                        (W_set.filter (fun w => r ∈ A w)).card := by
                    apply Finset.sum_le_sum
                    intro r hr
                    exact hcover r (Finset.filter_subset _ _ hr)
                  _ = ∑ w ∈ W_set, (A w ∩ remaining).card :=
                    hswap.symm
              have havg :
                  (m : ℝ) * (remaining.card : ℝ) /
                      (N : ℝ) ≤
                    ((A best ∩ remaining).card : ℝ) := by
                have hsum_real :
                    (m : ℝ) * (remaining.card : ℝ) ≤
                      ∑ w ∈ W_set,
                        ((A w ∩ remaining).card : ℝ) := by
                  exact_mod_cast hsum
                have hmaxsum :
                    (∑ w ∈ W_set,
                        ((A w ∩ remaining).card : ℝ)) ≤
                      (N : ℝ) *
                        ((A best ∩ remaining).card : ℝ) := by
                  calc
                    (∑ w ∈ W_set,
                        ((A w ∩ remaining).card : ℝ))
                        ≤ ∑ _w ∈ W_set,
                            ((A best ∩ remaining).card : ℝ) := by
                          apply Finset.sum_le_sum
                          intro w hw
                          exact_mod_cast hmax w hw
                    _ = (N : ℝ) *
                          ((A best ∩ remaining).card : ℝ) := by
                        simp [N]
                have hN_real : (0 : ℝ) < (N : ℝ) := by
                  exact_mod_cast hN_pos
                rw [div_le_iff₀ hN_real]
                exact hsum_real.trans (by simpa [mul_comm] using hmaxsum)
              let W'' := insert best W'
              have hW''_sub : W'' ⊆ W_set := by
                intro w hw
                simp only [W'', Finset.mem_insert] at hw
                rcases hw with (rfl | hw)
                · exact hbest
                · exact hW'_sub hw
              have hW''_card : W''.card ≤ j + 1 :=
                (Finset.card_insert_le _ _).trans (Nat.add_le_add_right hW'_card 1)
              have hremaining_eq :
                  R_set.filter
                      (fun r => ¬ ∃ w ∈ W'', r ∈ A w) =
                    remaining \ A best := by
                ext r
                have hiff :
                    (∃ w ∈ W'', r ∈ A w) ↔
                      r ∈ A best ∨ ∃ w ∈ W', r ∈ A w := by
                  dsimp only [W'']
                  exact Finset.exists_mem_insert best W'
                    (fun w => r ∈ A w)
                have hrem :
                    r ∈ remaining ↔
                      r ∈ R_set ∧ ¬ ∃ w ∈ W', r ∈ A w := by
                  simp [remaining]
                rw [Finset.mem_filter, Finset.mem_sdiff, hrem, hiff]
                constructor
                · rintro ⟨hr, hnot⟩
                  exact ⟨⟨hr, fun hex => hnot (Or.inr hex)⟩,
                    fun hbest' => hnot (Or.inl hbest')⟩
                · rintro ⟨⟨hr, hrest⟩, hbest'⟩
                  exact ⟨hr, fun hor => hor.elim hbest' hrest⟩
              have hcard_sub :
                  ((remaining \ A best).card : ℝ) =
                    (remaining.card : ℝ) -
                      ((A best ∩ remaining).card : ℝ) := by
                have hnat :
                    (remaining \ A best).card =
                      remaining.card - (A best ∩ remaining).card := by
                  rw [Finset.card_sdiff]
                rw [hnat, Nat.cast_sub]
                apply Finset.card_le_card Finset.inter_subset_right
              have hstep :
                  ((remaining \ A best).card : ℝ) ≤
                    (remaining.card : ℝ) *
                      (1 - (m : ℝ) / (N : ℝ)) := by
                rw [hcard_sub]
                calc
                  (remaining.card : ℝ) -
                      ((A best ∩ remaining).card : ℝ) ≤
                    (remaining.card : ℝ) -
                      ((m : ℝ) * (remaining.card : ℝ) / (N : ℝ)) :=
                    sub_le_sub_left havg _
                  _ = (remaining.card : ℝ) *
                      (1 - (m : ℝ) / (N : ℝ)) := by ring
              refine ⟨W'', hW''_sub, hW''_card, ?_⟩
              rw [hremaining_eq]
              calc
                ((remaining \ A best).card : ℝ)
                    ≤ (remaining.card : ℝ) *
                        (1 - (m : ℝ) / (N : ℝ)) := hstep
                _ ≤ ((R_set.card : ℝ) *
                      (1 - (m : ℝ) / (N : ℝ)) ^ j) *
                        (1 - (m : ℝ) / (N : ℝ)) := by
                    have hbase :
                        0 ≤ 1 - (m : ℝ) / (N : ℝ) := by
                      have hN_real : (0 : ℝ) < (N : ℝ) := by
                        exact_mod_cast hN_pos
                      rw [sub_nonneg, div_le_one hN_real]
                      exact_mod_cast hmN
                    exact mul_le_mul_of_nonneg_right hremain hbase
                _ = (R_set.card : ℝ) *
                      (1 - (m : ℝ) / (N : ℝ)) ^ (j + 1) := by
                    rw [pow_succ]
                    ring
      rcases hinduction k with ⟨W', hW'_sub, hW'_card, hremain⟩
      let remaining :=
        R_set.filter (fun r => ¬ ∃ w ∈ W', r ∈ A w)
      let covered :=
        R_set.filter (fun r => ∃ w ∈ W', r ∈ A w)
      have hpartition :
          remaining.card + covered.card = R_set.card := by
        have hdisjoint : Disjoint remaining covered := by
          rw [Finset.disjoint_left]
          intro r hr hc
          exact (Finset.mem_filter.mp hr).2 (Finset.mem_filter.mp hc).2
        have hunion : remaining ∪ covered = R_set := by
          ext r
          simp only [remaining, covered, Finset.mem_union,
            Finset.mem_filter]
          by_cases h : ∃ w ∈ W', r ∈ A w <;> simp [h]
        rw [← hunion, Finset.card_union_of_disjoint hdisjoint]
      have hexp_bound :
          (1 - (m : ℝ) / (N : ℝ)) ^ k ≤ Real.exp (-1) := by
        have hbase :
            1 - (m : ℝ) / (N : ℝ) ≤
              Real.exp (-(m : ℝ) / (N : ℝ)) := by
          have h := Real.add_one_le_exp (-(m : ℝ) / (N : ℝ))
          have heq :
              (-(m : ℝ) / (N : ℝ)) + 1 =
                1 - (m : ℝ) / (N : ℝ) := by ring
          rwa [heq] at h
        have hbase_nonneg :
            0 ≤ 1 - (m : ℝ) / (N : ℝ) := by
          have hN_real : (0 : ℝ) < (N : ℝ) := by
            exact_mod_cast hN_pos
          rw [sub_nonneg, div_le_one hN_real]
          exact_mod_cast hmN
        have hpow :
            (1 - (m : ℝ) / (N : ℝ)) ^ k ≤
              Real.exp (-(m : ℝ) / (N : ℝ) * (k : ℝ)) := by
          calc
            (1 - (m : ℝ) / (N : ℝ)) ^ k
                ≤ (Real.exp (-(m : ℝ) / (N : ℝ))) ^ k := by
                  gcongr
            _ = Real.exp (-(m : ℝ) / (N : ℝ) * (k : ℝ)) := by
                  rw [← Real.exp_nat_mul]
                  congr 1
                  ring
        have hmk : 1 ≤ (m : ℝ) / (N : ℝ) * (k : ℝ) := by
          have hk_lower : (N : ℝ) / (m : ℝ) ≤ (k : ℝ) := by
            let q : ℕ := N / m
            have hdecomp : N = q * m + N % m := by
              have h := Nat.div_add_mod N m
              simpa [q, mul_comm] using h.symm
            have hmod : N % m < m := Nat.mod_lt N hm_pos
            have hlt_nat : N < (q + 1) * m := by
              calc
                N = q * m + N % m := hdecomp
                _ < q * m + m := Nat.add_lt_add_left hmod _
                _ = (q + 1) * m := by ring
            have hlt_real :
                (N : ℝ) < ((q + 1 : ℕ) : ℝ) * (m : ℝ) := by
              exact_mod_cast hlt_nat
            have hm_real : (0 : ℝ) < (m : ℝ) := by
              exact_mod_cast hm_pos
            have :
                (N : ℝ) / (m : ℝ) < ((q + 1 : ℕ) : ℝ) := by
              rw [div_lt_iff₀ hm_real]
              exact hlt_real
            simpa [k, q] using this.le
          have hN_real : (0 : ℝ) < (N : ℝ) := by
            exact_mod_cast hN_pos
          have hm_real : (0 : ℝ) < (m : ℝ) := by
            exact_mod_cast hm_pos
          calc
            1 = (m : ℝ) / (N : ℝ) *
                ((N : ℝ) / (m : ℝ)) := by
                  field_simp [hN_real.ne', hm_real.ne']
            _ ≤ (m : ℝ) / (N : ℝ) * (k : ℝ) := by
                  gcongr
        have hneg :
            -(m : ℝ) / (N : ℝ) * (k : ℝ) ≤ -1 := by
          have : -(m : ℝ) / (N : ℝ) * (k : ℝ) =
              -((m : ℝ) / (N : ℝ) * (k : ℝ)) := by ring
          rw [this]
          exact neg_le_neg hmk
        exact hpow.trans (Real.exp_le_exp.mpr hneg)
      have hremaining_bound :
          (remaining.card : ℝ) ≤
            (R_set.card : ℝ) * Real.exp (-1) :=
        hremain.trans (mul_le_mul_of_nonneg_left hexp_bound (by positivity))
      refine ⟨W', hW'_sub, ?_, ?_⟩
      · have hk_card : (W'.card : ℝ) ≤ (k : ℝ) := by
          exact_mod_cast hW'_card
        exact hk_card.trans (by simpa [N] using hk_real)
      · have hpartition_real :
            (remaining.card : ℝ) + (covered.card : ℝ) =
              (R_set.card : ℝ) := by exact_mod_cast hpartition
        have :
            (1 - Real.exp (-1)) * (R_set.card : ℝ) ≤
              (covered.card : ℝ) := by
          linarith
        simpa [covered] using this
    · have hR_empty : R_set = ∅ := by
        by_contra h
        obtain ⟨r, hr⟩ := Finset.nonempty_iff_ne_empty.mpr h
        have := hcover r hr
        have hle :
            (W_set.filter (fun w => r ∈ A w)).card ≤ W_set.card :=
          Finset.card_filter_le _ _
        omega
      refine ⟨∅, by simp, ?_, ?_⟩
      · have : (0 : ℝ) ≤ 2 * (W_set.card : ℝ) / (m : ℝ) := by
          positivity
        simpa using this
      · simp [hR_empty]

end GreedyCover

section TwoSidedSampling

variable {W B R : Type*} [DecidableEq W] [DecidableEq B] [DecidableEq R]

lemma two_sided_sampling
    (W_set : Finset W) (B_set : Finset B) (R_set : Finset R)
    (T_W : R → Finset W) (T_B : R → Finset B)
    (m n : ℕ) (hm_pos : 0 < m) (hn_pos : 0 < n)
    (hW : ∀ r ∈ R_set, m ≤ (T_W r).card)
    (hB : ∀ r ∈ R_set, n ≤ (T_B r).card)
    (hT_W_sub : ∀ r ∈ R_set, T_W r ⊆ W_set)
    (hT_B_sub : ∀ r ∈ R_set, T_B r ⊆ B_set) :
    ∃ (W' : Finset W) (B' : Finset B),
      W' ⊆ W_set ∧
      B' ⊆ B_set ∧
      (W'.card : ℝ) ≤ 2 * (W_set.card : ℝ) / (m : ℝ) ∧
      (B'.card : ℝ) ≤ 2 * (B_set.card : ℝ) / (n : ℝ) ∧
      (1 - Real.exp (-1)) ^ 2 * (R_set.card : ℝ) ≤
        ((R_set.filter (fun r =>
          (T_W r ∩ W').Nonempty ∧
            (T_B r ∩ B').Nonempty)).card : ℝ) := by
  let A_W : W → Finset R :=
    fun w => R_set.filter (fun r => w ∈ T_W r)
  have hA_W_sub : ∀ w, A_W w ⊆ R_set :=
    fun _ => Finset.filter_subset _ _
  have hcover_W :
      ∀ r ∈ R_set,
        m ≤ (W_set.filter (fun w => r ∈ A_W w)).card := by
    intro r hr
    have heq :
        W_set.filter (fun w => r ∈ A_W w) = T_W r := by
      ext w
      simp only [A_W, Finset.mem_filter]
      constructor
      · exact fun h => h.2.2
      · intro hw
        exact ⟨hT_W_sub r hr hw, hr, hw⟩
    rw [heq]
    exact hW r hr
  rcases greedy_cover W_set R_set A_W m hm_pos hA_W_sub hcover_W with
    ⟨W', hW'_sub, hW'_card, hcovered_W⟩
  let R_W :=
    R_set.filter (fun r => (T_W r ∩ W').Nonempty)
  have hR_W :
      (1 - Real.exp (-1)) * (R_set.card : ℝ) ≤
        (R_W.card : ℝ) := by
    have heq :
        R_set.filter (fun r => ∃ w ∈ W', r ∈ A_W w) = R_W := by
      ext r
      simp only [A_W, R_W, Finset.mem_filter]
      constructor
      · rintro ⟨hr, w, hwW', hr', htw⟩
        exact ⟨hr, ⟨w, Finset.mem_inter.mpr ⟨htw, hwW'⟩⟩⟩
      · rintro ⟨hr, ⟨w, hw⟩⟩
        exact ⟨hr, w, (Finset.mem_inter.mp hw).2, hr,
          (Finset.mem_inter.mp hw).1⟩
    rwa [heq] at hcovered_W
  let A_B : B → Finset R :=
    fun b => R_W.filter (fun r => b ∈ T_B r)
  have hA_B_sub : ∀ b, A_B b ⊆ R_W :=
    fun _ => Finset.filter_subset _ _
  have hcover_B :
      ∀ r ∈ R_W,
        n ≤ (B_set.filter (fun b => r ∈ A_B b)).card := by
    intro r hr
    have hrR : r ∈ R_set := Finset.filter_subset _ _ hr
    have heq :
        B_set.filter (fun b => r ∈ A_B b) = T_B r := by
      ext b
      simp only [A_B, Finset.mem_filter]
      constructor
      · exact fun h => h.2.2
      · intro hb
        exact ⟨hT_B_sub r hrR hb, hr, hb⟩
    rw [heq]
    exact hB r hrR
  rcases greedy_cover B_set R_W A_B n hn_pos hA_B_sub hcover_B with
    ⟨B', hB'_sub, hB'_card, hcovered_B⟩
  let R_both :=
    R_set.filter (fun r =>
      (T_W r ∩ W').Nonempty ∧ (T_B r ∩ B').Nonempty)
  have hR_both :
      (1 - Real.exp (-1)) * (R_W.card : ℝ) ≤
        (R_both.card : ℝ) := by
    have heq :
        R_W.filter (fun r => ∃ b ∈ B', r ∈ A_B b) =
          R_both := by
      ext r
      simp only [A_B, R_W, R_both, Finset.mem_filter]
      constructor
      · rintro ⟨hrW, b, hbB', hrW', htb⟩
        have hr : r ∈ R_set := hrW.1
        have hW_nonempty : (T_W r ∩ W').Nonempty := hrW.2
        exact ⟨hr, hW_nonempty,
          ⟨b, Finset.mem_inter.mpr ⟨htb, hbB'⟩⟩⟩
      · rintro ⟨hr, hW_nonempty, ⟨b, hb⟩⟩
        have hrW : r ∈ R_set ∧ (T_W r ∩ W').Nonempty :=
          ⟨hr, hW_nonempty⟩
        exact ⟨hrW, b, (Finset.mem_inter.mp hb).2, hrW,
          (Finset.mem_inter.mp hb).1⟩
    rwa [heq] at hcovered_B
  have hnonneg : 0 ≤ 1 - Real.exp (-1) := by
    have : Real.exp (-1) ≤ Real.exp 0 :=
      Real.exp_le_exp.mpr (by norm_num)
    simpa using sub_nonneg.mpr this
  refine ⟨W', B', hW'_sub, hB'_sub, hW'_card, hB'_card, ?_⟩
  calc
    (1 - Real.exp (-1)) ^ 2 * (R_set.card : ℝ) =
        (1 - Real.exp (-1)) *
          ((1 - Real.exp (-1)) * (R_set.card : ℝ)) := by ring
    _ ≤ (1 - Real.exp (-1)) * (R_W.card : ℝ) := by
      gcongr
    _ ≤ (R_both.card : ℝ) := hR_both
    _ = ((R_set.filter (fun r =>
        (T_W r ∩ W').Nonempty ∧
          (T_B r ∩ B').Nonempty)).card : ℝ) := rfl

end TwoSidedSampling

end Kakeya.Cinematic
