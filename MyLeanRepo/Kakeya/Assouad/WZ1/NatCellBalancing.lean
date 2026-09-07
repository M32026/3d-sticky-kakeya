import MyLeanRepo.Kakeya.Assouad.WZ1.CellBalancing

/-!
# Natural-number cell balancing wrapper

Wraps `cell_balance_pigeonhole` to return a natural-number multiplicity bound `m`,
suitable for `WZ1AnisotropicFrostmanRescalingData.fiberMultiplicity`.
-/

noncomputable section

namespace Kakeya.Assouad

open Finset

/--
Natural-number version of the dyadic cell balancing pigeonhole.

Given cells with natural-number sizes in `[1, Vmax]`, there exists `m : ℕ` and a
subset `t` such that all cells in `t` have size in `[m, 2m]` and the total size
of `t` is at least the grand total divided by `log_2(Vmax) + 1`.
-/
lemma nat_cell_balance_pigeonhole
    {α : Type*} [DecidableEq α] (s : Finset α)
    (f : α → ℕ) (hpos : ∀ i ∈ s, 0 < f i)
    (Vmax : ℕ) (hmax : ∀ i ∈ s, f i ≤ Vmax) :
    ∃ (m : ℕ) (t : Finset α),
      t ⊆ s ∧
      (∀ i ∈ t, m ≤ f i ∧ f i ≤ 2 * m) ∧
      (∑ i ∈ t, f i : ENNReal) ≥
        (∑ i ∈ s, f i : ENNReal) / ENNReal.ofReal (Real.logb 2 (Vmax : ℝ) + 1) := by
  by_cases hs : s.Nonempty
  · -- s nonempty
    have hVmax_pos : 0 < Vmax := by
      rcases hs with ⟨i, hi⟩
      have h1 : 0 < f i := hpos i hi
      have h2 : f i ≤ Vmax := hmax i hi
      omega
    have hVmax_one : (1 : ℝ) ≤ (Vmax : ℝ) := by exact_mod_cast hVmax_pos
    let v : α → ENNReal := fun i => ↑(f i)
    have hpos' : ∀ i ∈ s, 0 < v i := by
      intro i hi
      have h1 : 0 < f i := hpos i hi
      have h2 : (0 : ENNReal) < ↑(f i) := by exact_mod_cast h1
      exact h2
    have hmax' : ∀ i ∈ s, v i ≤ ENNReal.ofReal (Vmax : ℝ) := by
      intro i hi
      have h1 : f i ≤ Vmax := hmax i hi
      have h2 : (↑(f i) : ENNReal) ≤ ↑Vmax := by exact_mod_cast h1
      have h3 : (↑Vmax : ENNReal) = ENNReal.ofReal (Vmax : ℝ) := by
        simp
      rw [h3] at h2
      exact h2
    have hmin' : ∀ i ∈ s, ENNReal.ofReal (1 : ℝ) ≤ v i := by
      intro i hi
      have h1 : 1 ≤ f i := by
        have h2 : 0 < f i := hpos i hi
        omega
      have h3 : (ENNReal.ofReal (1 : ℝ)) ≤ (↑(f i) : ENNReal) := by
        exact_mod_cast h1
      exact h3
    obtain ⟨M, t, hts, hband, hsum⟩ :=
      cell_balance_pigeonhole s v (1 : ℝ) (Vmax : ℝ)
        hpos' hmax' hmin' (by norm_num) hVmax_one
    have ht_nonempty : t.Nonempty := by
      by_contra h
      have h_empty : t = ∅ := by
        simpa [Finset.not_nonempty_iff_eq_empty] using h
      rw [h_empty] at hsum
      rcases hs with ⟨i, hi⟩
      have hvi_pos : 0 < v i := hpos' i hi
      have hvi_le : v i ≤ ∑ j ∈ s, v j :=
        Finset.single_le_sum (fun j _ => by positivity) hi
      have h_sum_pos : 0 < ∑ j ∈ s, v j := lt_of_lt_of_le hvi_pos hvi_le
      have hlog_nonneg : 0 ≤ Real.logb 2 ((Vmax : ℝ) / (1 : ℝ)) := by
        apply Real.logb_nonneg
        · norm_num
        · linarith
      have hdenom_real_pos : 0 < Real.logb 2 ((Vmax : ℝ) / (1 : ℝ)) + 1 := by linarith
      have h_denom_pos : 0 < ENNReal.ofReal (Real.logb 2 ((Vmax : ℝ) / (1 : ℝ)) + 1) :=
        ENNReal.ofReal_pos.mpr hdenom_real_pos
      have h_denom_ne_top : ENNReal.ofReal (Real.logb 2 ((Vmax : ℝ) / (1 : ℝ)) + 1) ≠ ⊤ := ENNReal.ofReal_ne_top
      have h_div_pos : 0 < (∑ i ∈ s, v i) / ENNReal.ofReal (Real.logb 2 ((Vmax : ℝ) / (1 : ℝ)) + 1) :=
        ENNReal.div_pos h_sum_pos.ne' h_denom_ne_top
      have hX_eq_zero : (∑ i ∈ s, v i) / ENNReal.ofReal (Real.logb 2 ((Vmax : ℝ) / (1 : ℝ)) + 1) = 0 := by
        simpa [Finset.sum_empty] using hsum
      exact h_div_pos.ne' hX_eq_zero
    let image : Finset ℕ := t.image f
    have himage_nonempty : image.Nonempty := ht_nonempty.image f
    let m : ℕ := Finset.min' image himage_nonempty
    have hm_in : m ∈ image := Finset.min'_mem image himage_nonempty
    have hm_exists : ∃ j ∈ t, f j = m := Finset.mem_image.mp hm_in
    rcases hm_exists with ⟨j, hj, hjm⟩
    have h1 : ∀ i ∈ t, m ≤ f i := by
      intro i hi
      have hfi_in : f i ∈ image := Finset.mem_image.mpr ⟨i, hi, rfl⟩
      exact Finset.min'_le image (f i) hfi_in
    have hM_le_m : M ≤ (↑m : ENNReal) := by
      have hMj : M ≤ v j := (hband j hj).1
      have h_vj : v j = (↑(f j) : ENNReal) := by rfl
      rw [h_vj] at hMj
      rw [hjm] at hMj
      exact hMj
    have h2 : ∀ i ∈ t, f i ≤ 2 * m := by
      intro i hi
      have h3 : v i ≤ 2 * M := (hband i hi).2
      have h4 : v i ≤ 2 * (↑m : ENNReal) := by
        calc
          v i ≤ 2 * M := h3
          _ ≤ 2 * (↑m : ENNReal) := by gcongr
      have h5 : v i = (↑(f i) : ENNReal) := by rfl
      rw [h5] at h4
      have h6 : (↑(f i) : ENNReal) ≤ (↑(2 * m) : ENNReal) := by
        simpa using h4
      exact_mod_cast h6
    have hsum_t : (∑ i ∈ t, v i) = (∑ i ∈ t, f i : ENNReal) := by
      simp [v]
    have hsum_s : (∑ i ∈ s, v i) = (∑ i ∈ s, f i : ENNReal) := by
      simp [v]
    rw [hsum_t, hsum_s] at hsum
    have hlog : (Vmax : ℝ) / (1 : ℝ) = (Vmax : ℝ) := by ring
    rw [hlog] at hsum
    exact ⟨m, t, hts, fun i hi => ⟨h1 i hi, h2 i hi⟩, hsum⟩
  · -- s empty
    refine ⟨1, ∅, by simp, by simp, ?_⟩
    have h_empty : s = ∅ := by
      simpa [Finset.not_nonempty_iff_eq_empty] using hs
    rw [h_empty]
    simp

end Kakeya.Assouad
