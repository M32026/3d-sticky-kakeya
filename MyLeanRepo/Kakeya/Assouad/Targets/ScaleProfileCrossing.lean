import MyLeanRepo.Kakeya.Assouad.Statements

/-! WZ2 Section 7: arithmetic crossing step in the spacing lemma. -/

namespace Kakeya.Assouad

theorem scale_profile_crossing : ScaleProfileCrossingStatement := by
  intro N hN n s ε hn hε hε2 hs hsn a t ha0 haN hinc ht hav
  by_contra h
  push Not at h
  classical

  let E : Finset (Fin N) :=
    Finset.univ.filter (fun i => a i.castSucc ≤ 1 - ε / (2 * n))
  let L : Finset (Fin N) :=
    Finset.univ.filter (fun i => a i.castSucc > 1 - ε / (2 * n))

  have hE_L_univ : E ∪ L = Finset.univ := by
    ext i
    simp only [E, L, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases h' : a i.castSucc ≤ 1 - ε / (2 * n) <;> simp [h'] <;> linarith

  have h_disj : Disjoint E L := by
    rw [Finset.disjoint_left]
    intro i hi1 hi2
    have h1 : a i.castSucc ≤ 1 - ε / (2 * n) := (Finset.mem_filter.mp hi1).2
    have h2 : a i.castSucc > 1 - ε / (2 * n) := (Finset.mem_filter.mp hi2).2
    linarith

  have h_partition : ∀ (f : Fin N → ℝ),
      ∑ i ∈ E, f i + ∑ i ∈ L, f i = ∑ i : Fin N, f i := by
    intro f
    have h : ∑ i ∈ (E ∪ L), f i = ∑ i ∈ E, f i + ∑ i ∈ L, f i := by
      rw [Finset.sum_union h_disj]
    rw [hE_L_univ] at h
    exact h.symm

  have h1 : ∀ i ∈ E, t i < s - ε := by
    intro i hi
    have h_i_E : a i.castSucc ≤ 1 - ε / (2 * n) := (Finset.mem_filter.mp hi).2
    have h_not : ¬(s - ε ≤ t i) := by
      intro h_le
      have h' := h i h_le
      linarith
    exact not_le.mp h_not

  have h2 : ∀ i ∈ L, a i.castSucc > 1 - ε / (2 * n) := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2

  -- Telescoping sum lemma on ℕ
  have h_telescoping_range : ∀ (f : ℕ → ℝ) (n : ℕ),
      ∑ j ∈ Finset.range n, (f (j + 1) - f j) = f n - f 0 := by
    intro f n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih] <;> ring

  -- Telescoping over Ico, direct induction
  have h_telescoping_Ico : ∀ (f : ℕ → ℝ) (m k : ℕ), m ≤ k →
      ∑ j ∈ Finset.Ico m k, (f (j + 1) - f j) = f k - f m := by
    intro f m k hmk
    induction k with
    | zero =>
      have hm0 : m = 0 := by omega
      subst hm0
      simp
    | succ k ih =>
      by_cases h : m ≤ k
      · rw [Finset.sum_Ico_succ_top h]
        rw [ih h] <;> ring
      · have hm : m = k + 1 := by omega
        subst hm
        simp [Finset.Ico_eq_empty] <;> ring

  -- Extend a to ℕ for telescoping
  let g : ℕ → ℝ := fun m => if h : m ≤ N then a ⟨m, Nat.lt_succ_iff.mpr h⟩ else 0

  have hg_step : ∀ (j : ℕ), (hj : j < N) →
      g (j + 1) - g j =
        a (⟨j, hj⟩ : Fin N).succ - a (⟨j, hj⟩ : Fin N).castSucc := by
    intro j hj
    have h1 : j ≤ N := by linarith
    have h2 : j + 1 ≤ N := by linarith
    have hgj : g j = a ⟨j, Nat.lt_succ_iff.mpr h1⟩ := by
      unfold g; rw [dif_pos h1] <;> rfl
    have hgj1 : g (j + 1) = a ⟨j + 1, Nat.lt_succ_iff.mpr h2⟩ := by
      unfold g; rw [dif_pos h2] <;> rfl
    have h_eq1 : (⟨j, hj⟩ : Fin N).castSucc = (⟨j, Nat.lt_succ_iff.mpr h1⟩ : Fin (N + 1)) := by
      ext <;> simp
    have h_eq2 : (⟨j, hj⟩ : Fin N).succ = (⟨j + 1, Nat.lt_succ_iff.mpr h2⟩ : Fin (N + 1)) := by
      ext <;> simp
    rw [hgj1, hgj, h_eq2, h_eq1]

  have hg_N : g N = a (Fin.last N) := by
    have h1 : N ≤ N := by linarith
    unfold g; rw [dif_pos h1]
    have h_eq : (⟨N, Nat.lt_succ_iff.mpr h1⟩ : Fin (N + 1)) = Fin.last N := by
      ext <;> simp [Fin.last]
    rw [h_eq]

  have hg_0 : g 0 = a 0 := by
    have h0 : 0 ≤ N := by linarith
    unfold g; rw [dif_pos h0]
    have h_eq : (⟨0, Nat.lt_succ_iff.mpr h0⟩ : Fin (N + 1)) = (0 : Fin (N + 1)) := by
      ext <;> simp
    rw [h_eq]

  have hg_val : ∀ (i : Fin N), g i.val = a i.castSucc := by
    intro i
    have h1 : i.val ≤ N := by have h : i.val < N := i.is_lt; linarith
    unfold g; rw [dif_pos h1]
    have h_eq : (⟨i.val, Nat.lt_succ_iff.mpr h1⟩ : Fin (N + 1)) = i.castSucc := by
      ext <;> simp
    rw [h_eq]

  let f : Fin N → ℝ := fun i => a i.succ - a i.castSucc
  let mkFin : ℕ → Fin N := fun x => if h : x < N then ⟨x, h⟩ else ⟨0, hN⟩

  have hmkFin_eq : ∀ (j : ℕ), (hj : j < N) → mkFin j = (⟨j, hj⟩ : Fin N) := by
    intro j hj
    simp [mkFin, hj] <;> ext <;> simp

  have hmkFin_val : ∀ (j : ℕ), (hj : j < N) → (mkFin j).val = j := by
    intro j hj
    rw [hmkFin_eq j hj] <;> simp

  have hmkFin_inj : ∀ x ∈ Finset.range N, ∀ y ∈ Finset.range N, mkFin x = mkFin y → x = y := by
    intro x hx y hy hxy
    have h1 : (mkFin x).val = (mkFin y).val := by rw [hxy]
    have h2 : (mkFin x).val = x := hmkFin_val x (Finset.mem_range.mp hx)
    have h3 : (mkFin y).val = y := hmkFin_val y (Finset.mem_range.mp hy)
    rw [h2, h3] at h1
    exact h1

  -- Total telescoping sum via Finset.image
  have h_sum_all : ∑ i : Fin N, f i = 1 := by
    have h_image : Finset.image mkFin (Finset.range N) = (Finset.univ : Finset (Fin N)) := by
      ext y
      constructor
      · intro h
        rcases Finset.mem_image.mp h with ⟨x, _, rfl⟩
        simp
      · intro _
        have h2 : mkFin y.val = y := hmkFin_eq y.val y.is_lt
        exact Finset.mem_image.mpr ⟨y.val, Finset.mem_range.mpr y.is_lt, h2⟩
    have h_eq : ∑ i : Fin N, f i = ∑ j ∈ Finset.range N, f (mkFin j) := by
      rw [←h_image, Finset.sum_image hmkFin_inj]
    rw [h_eq]
    have h_eq2 : ∑ j ∈ Finset.range N, f (mkFin j) = ∑ j ∈ Finset.range N, (g (j + 1) - g j) := by
      apply Finset.sum_congr rfl
      intro j hj
      have h_j_lt_N : j < N := Finset.mem_range.mp hj
      rw [hmkFin_eq j h_j_lt_N]
      exact (hg_step j h_j_lt_N).symm
    rw [h_eq2, h_telescoping_range g N, hg_N, hg_0, haN, ha0] <;> ring

  -- g is strictly increasing on {0, ..., N}
  have h_step_pos : ∀ (j : ℕ), (hj : j < N) → 0 < g (j + 1) - g j := by
    intro j hj
    rw [hg_step j hj]
    have h : 0 < a (⟨j, hj⟩ : Fin N).succ - a (⟨j, hj⟩ : Fin N).castSucc := by
      linarith [hinc ⟨j, hj⟩]
    exact h

  -- g is monotone on {0, ..., N}
  have h_g_mono : ∀ (m k : ℕ), m ≤ k → k ≤ N → g m ≤ g k := by
    intro m k hmk hkN
    have h_pos_terms : ∀ j ∈ Finset.Ico m k, 0 ≤ g (j + 1) - g j := by
      intro j hj
      have h_j_lt_N : j < N := by
        simp only [Finset.mem_Ico] at hj
        omega
      exact le_of_lt (h_step_pos j h_j_lt_N)
    have h_sum_nonneg : 0 ≤ ∑ j ∈ Finset.Ico m k, (g (j + 1) - g j) :=
      Finset.sum_nonneg h_pos_terms
    have h_eq : g k - g m = ∑ j ∈ Finset.Ico m k, (g (j + 1) - g j) :=
      (h_telescoping_Ico g m k hmk).symm
    linarith

  -- L is an upper set
  have hL_upper : ∀ (i j : Fin N), i ∈ L → i ≤ j → j ∈ L := by
    intro i j hi hij
    have h_i : a i.castSucc > 1 - ε / (2 * n) := h2 i hi
    have h_ij : i.val ≤ j.val := by exact_mod_cast hij
    have h_i_le_N : i.val ≤ N := by have h : i.val < N := i.is_lt; linarith
    have h_j_le_N : j.val ≤ N := by have h : j.val < N := j.is_lt; linarith
    have h_j_le : g i.val ≤ g j.val := h_g_mono i.val j.val h_ij h_j_le_N
    have h_eq_i : g i.val = a i.castSucc := hg_val i
    have h_eq_j : g j.val = a j.castSucc := hg_val j
    rw [h_eq_i, h_eq_j] at h_j_le
    have h' : a j.castSucc > 1 - ε / (2 * n) := by linarith
    simp only [L, Finset.mem_filter, Finset.mem_univ, true_and]
    exact h'

  -- Bound on sum over L
  have hL_bound : ∑ i ∈ L, (a i.succ - a i.castSucc) ≤ ε / (2 * n) := by
    by_cases hL_empty : L = ∅
    · rw [hL_empty]
      have h_pos : 0 ≤ ε / (2 * n) := by positivity
      simpa using h_pos
    · have hL_nonempty : L.Nonempty := by
        simpa [Finset.nonempty_iff_ne_empty] using hL_empty
      let k : Fin N := Finset.min' L hL_nonempty
      have hk_in_L : k ∈ L := Finset.min'_mem L hL_nonempty
      have hk_min : ∀ i ∈ L, k ≤ i := fun i hi => Finset.min'_le L i hi
      have hL_eq : L = Finset.Ici k := by
        ext i
        simp only [Finset.mem_Ici]
        constructor
        · exact hk_min i
        · intro hki
          exact hL_upper k i hk_in_L hki

      -- Prefix sum via Finset.image
      have h_prefix_image : Finset.image mkFin (Finset.range k.val) = Finset.Iio k := by
        ext y
        simp only [Finset.mem_image, Finset.mem_range, Finset.mem_Iio]
        constructor
        · rintro ⟨x, hx, rfl⟩
          have h_x_lt_k : x < k.val := hx
          have h : mkFin x < k := by
            rw [hmkFin_eq x (by omega)]
            exact_mod_cast h_x_lt_k
          exact h
        · intro hy
          have h_y_lt_k : y.val < k.val := by exact_mod_cast hy
          refine ⟨y.val, h_y_lt_k, ?_⟩
          exact hmkFin_eq y.val y.is_lt
      have hmkFin_inj' : ∀ x ∈ Finset.range k.val, ∀ y ∈ Finset.range k.val, mkFin x = mkFin y → x = y := by
        intro x hx y hy hxy
        have hxN : x < N := by have h : x < k.val := Finset.mem_range.mp hx; omega
        have hyN : y < N := by have h : y < k.val := Finset.mem_range.mp hy; omega
        exact hmkFin_inj x (Finset.mem_range.mpr hxN) y (Finset.mem_range.mpr hyN) hxy
      have h_prefix : ∑ i ∈ Finset.Iio k, f i = g k.val - g 0 := by
        rw [←h_prefix_image, Finset.sum_image hmkFin_inj']
        have h_eq3 : ∑ j ∈ Finset.range k.val, f (mkFin j) =
              ∑ j ∈ Finset.range k.val, (g (j + 1) - g j) := by
          apply Finset.sum_congr rfl
          intro j hj
          have h_j_lt_k : j < k.val := Finset.mem_range.mp hj
          have h_j_lt_N : j < N := by omega
          rw [hmkFin_eq j h_j_lt_N]
          exact (hg_step j h_j_lt_N).symm
        rw [h_eq3, h_telescoping_range g k.val]
      rw [hL_eq]
      have h_univ_part : (Finset.univ : Finset (Fin N)) =
            Finset.Iio k ∪ Finset.Ici k := by
        ext i
        simp [Finset.mem_Ici, Finset.mem_Iio] <;> omega
      have h_disj2 : Disjoint (Finset.Iio k) (Finset.Ici k) := by
        rw [Finset.disjoint_left]
        intro i hi1 hi2
        simp [Finset.mem_Iio, Finset.mem_Ici] at hi1 hi2 <;> omega
      have h_sum_split : ∑ i : Fin N, f i =
            ∑ i ∈ Finset.Iio k, f i + ∑ i ∈ Finset.Ici k, f i := by
        rw [h_univ_part, Finset.sum_union h_disj2]
      have h_k_in_L : a k.castSucc > 1 - ε / (2 * n) := h2 k hk_in_L
      have h_gk : g k.val = a k.castSucc := hg_val k
      have h_g0 : g 0 = a 0 := hg_0
      have h_main : ∑ i ∈ Finset.Ici k, f i = 1 - a k.castSucc := by
        linarith [h_sum_split, h_sum_all, h_prefix, h_gk, h_g0, ha0]
      rw [h_main]
      linarith

  -- E is nonempty
  have hE_nonempty : E.Nonempty := by
    by_contra hE_empty
    have hE_empty' : E = ∅ := by simpa using hE_empty
    have hL_univ : L = Finset.univ := by
      rw [←hE_L_univ, hE_empty'] <;> simp
    rw [hL_univ] at hL_bound
    rw [h_sum_all] at hL_bound
    have h_cont : ε / (2 * n) < 1 := by
      have h1 : ε ≤ n := by linarith
      have h2 : ε / (2 * n) ≤ 1 / 2 := by
        calc
          ε / (2 * n) ≤ ε / (2 * ε) := by gcongr <;> linarith
          _ = 1 / 2 := by
            field_simp [hε.ne'] <;> ring
      linarith
    linarith

  -- Main bound
  let S_E := ∑ i ∈ E, (a i.succ - a i.castSucc)
  let S_L := ∑ i ∈ L, (a i.succ - a i.castSucc)

  have hS_sum : S_E + S_L = 1 := by
    have h := h_partition (fun i => a i.succ - a i.castSucc)
    rw [h_sum_all] at h
    exact h

  have h_pos_delta : ∀ i : Fin N, 0 < a i.succ - a i.castSucc := by
    intro i
    have h : 0 < a i.succ - a i.castSucc := by linarith [hinc i]
    exact h

  have h_strict_E : ∑ i ∈ E, t i * (a i.succ - a i.castSucc) < (s - ε) * S_E := by
    have h3 : ∀ i ∈ E, t i * (a i.succ - a i.castSucc) <
          (s - ε) * (a i.succ - a i.castSucc) := by
      intro i hi
      have h4 : t i < s - ε := h1 i hi
      have h5 : 0 < a i.succ - a i.castSucc := h_pos_delta i
      nlinarith
    have h6 : ∑ i ∈ E, t i * (a i.succ - a i.castSucc) <
          ∑ i ∈ E, (s - ε) * (a i.succ - a i.castSucc) := by
      apply Finset.sum_lt_sum_of_nonempty hE_nonempty
      intro i hi
      exact h3 i hi
    have h7 : ∑ i ∈ E, (s - ε) * (a i.succ - a i.castSucc) = (s - ε) * S_E := by
      rw [Finset.mul_sum] <;> rfl
    rw [h7] at h6
    exact h6

  have h_leq_L : ∑ i ∈ L, t i * (a i.succ - a i.castSucc) ≤ n * S_L := by
    have h3 : ∀ i ∈ L, t i * (a i.succ - a i.castSucc) ≤
          n * (a i.succ - a i.castSucc) := by
      intro i hi
      have h4 : t i ≤ n := (ht i).2
      have h5 : 0 < a i.succ - a i.castSucc := h_pos_delta i
      nlinarith
    have h6 : ∑ i ∈ L, t i * (a i.succ - a i.castSucc) ≤
          ∑ i ∈ L, n * (a i.succ - a i.castSucc) := by
      apply Finset.sum_le_sum
      intro i hi
      exact h3 i hi
    have h7 : ∑ i ∈ L, n * (a i.succ - a i.castSucc) = n * S_L := by
      rw [Finset.mul_sum] <;> rfl
    rw [h7] at h6
    exact h6

  have h_main1 : ∑ i : Fin N, t i * (a i.succ - a i.castSucc) <
        (s - ε) * S_E + n * S_L := by
    have h := h_partition (fun i => t i * (a i.succ - a i.castSucc))
    linarith [h_strict_E, h_leq_L]

  have h_nsm1 : 0 ≤ n - s + ε := by linarith

  have h_pos2 : 0 < 2 * n := by positivity

  have h1_ineq : (n - s + ε) / (2 * n) ≤ 1 - ε := by
    have h_eps_nonpos : ε - s ≤ 0 := by linarith
    have h_n_nonneg : 0 ≤ n * (1 - 2 * ε) := by
      have h1 : 0 ≤ 1 - 2 * ε := by linarith
      exact mul_nonneg hn.le h1
    have h_main : n - s + ε ≤ n * (1 - 2 * ε) + n := by
      have h2 : ε - s ≤ n * (1 - 2 * ε) := by linarith
      linarith
    calc
      (n - s + ε) / (2 * n)
        ≤ (n * (1 - 2 * ε) + n) / (2 * n) := by gcongr
      _ = 1 - ε := by
        field_simp [h_pos2.ne'] <;> ring

  have h2_ineq : (n - s + ε) * (ε / (2 * n)) ≤ ε - ε ^ 2 := by
    have h3 : (n - s + ε) * (ε / (2 * n)) = ε * ((n - s + ε) / (2 * n)) := by
      field_simp [h_pos2.ne'] <;> ring
    rw [h3]
    have h4 : ε * ((n - s + ε) / (2 * n)) ≤ ε * (1 - ε) := by
      exact mul_le_mul_of_nonneg_left h1_ineq hε.le
    have h5 : ε * (1 - ε) = ε - ε ^ 2 := by ring
    rw [h5] at h4
    exact h4

  have h_ineq : (s - ε) + (n - s + ε) * (ε / (2 * n)) ≤ s - ε ^ 2 := by
    linarith [h2_ineq]

  have h_main2 : (s - ε) * S_E + n * S_L ≤ s - ε ^ 2 := by
    have hS_E_eq : S_E = 1 - S_L := by linarith [hS_sum]
    rw [hS_E_eq]
    have hSL_bound : S_L ≤ ε / (2 * n) := hL_bound
    have h5 : (s - ε) * (1 - S_L) + n * S_L =
          (s - ε) + (n - s + ε) * S_L := by ring
    rw [h5]
    have h6 : (n - s + ε) * S_L ≤ (n - s + ε) * (ε / (2 * n)) := by
      exact mul_le_mul_of_nonneg_left hSL_bound h_nsm1
    have h7 : (s - ε) + (n - s + ε) * S_L ≤
          (s - ε) + (n - s + ε) * (ε / (2 * n)) := by
      linarith [h6]
    linarith [h_ineq, h7]

  linarith [hav, h_main1, h_main2]

end Kakeya.Assouad
