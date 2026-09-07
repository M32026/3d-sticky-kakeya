import MyLeanRepo.Kakeya.Assouad.WZ1.Helpers
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

/-!
# Mass-weighted dyadic band selection

Given a finite family indexed by `α`, each with a value `v i ∈ [Vmin, Vmax]`
and a weight `w i`, select a dyadic band `[M, 2*M]` whose indices retain a
logarithmic fraction of the total weight.
-/

noncomputable section

namespace Kakeya.Assouad

open Finset

/--
Given `v i ∈ [Vmin, Vmax]` and arbitrary nonnegative `ENNReal` weights `w i`,
there is a dyadic band `[M, 2*M]` whose indices retain at least the reciprocal
logarithmic fraction of the total weight.
-/
lemma mass_weighted_dyadic_band
    {α : Type*} [DecidableEq α]
    (s : Finset α)
    (v : α → ENNReal)
    (w : α → ENNReal)
    (Vmin Vmax : ℝ)
    (hVmin_pos : 0 < Vmin)
    (hVmin_le_Vmax : Vmin ≤ Vmax)
    (hv_lower : ∀ i ∈ s, ENNReal.ofReal Vmin ≤ v i)
    (hv_upper : ∀ i ∈ s, v i ≤ ENNReal.ofReal Vmax) :
    ∃ (M : ℝ) (t : Finset α),
      Vmin ≤ M ∧
      t ⊆ s ∧
      (∀ i ∈ t, ENNReal.ofReal M ≤ v i ∧ v i ≤ ENNReal.ofReal (2 * M)) ∧
      (∑ i ∈ t, w i) * ENNReal.ofReal (Real.logb 2 (Vmax / Vmin) + 1) ≥
        ∑ i ∈ s, w i := by
  by_cases hs : s.Nonempty
  · let x : ℝ := Real.logb 2 (Vmax / Vmin)
    have h_ratio_ge_one : 1 ≤ Vmax / Vmin := by
      exact (one_le_div hVmin_pos).mpr hVmin_le_Vmax
    have h_ratio_pos : 0 < Vmax / Vmin := by positivity
    have hx_nonneg : 0 ≤ x := by
      apply Real.logb_nonneg
      · norm_num
      · exact h_ratio_ge_one
    let N : ℕ := Nat.floor x + 1
    have hN_pos : 0 < N := by
      simp [N] <;> omega
    have hN_le_log : (N : ℝ) ≤ x + 1 := by
      have h : (Nat.floor x : ℝ) ≤ x := Nat.floor_le hx_nonneg
      simp only [N, Nat.cast_add, Nat.cast_one]
      linarith
    have h2 : x < (N : ℝ) := by
      simp only [N, Nat.cast_add, Nat.cast_one]
      exact Nat.lt_floor_add_one x
    have h4 : Vmax / Vmin < (2 : ℝ) ^ (N : ℝ) :=
      (Real.logb_lt_iff_lt_rpow (by norm_num) h_ratio_pos).mp h2
    have h5 : (2 : ℝ) ^ N = (2 : ℝ) ^ (N : ℝ) := by norm_cast
    have h1 : Vmax < (2 : ℝ) ^ N * Vmin := by
      rw [h5] at *
      calc
        Vmax = (Vmax / Vmin) * Vmin := by
          field_simp [hVmin_pos.ne']
        _ < (2 : ℝ) ^ (N : ℝ) * Vmin := by gcongr
    let f : ℕ → Finset α := fun k =>
      s.filter (fun i => v i < ENNReal.ofReal ((2 : ℝ) ^ k * Vmin))
    have hf_mono : ∀ k, f k ⊆ f (k + 1) := by
      intro k i hi
      have h_in_s : i ∈ s := (Finset.mem_filter.mp hi).1
      have h_lt : v i < ENNReal.ofReal ((2 : ℝ) ^ k * Vmin) :=
        (Finset.mem_filter.mp hi).2
      have h6 : (2 : ℝ) ^ k * Vmin < (2 : ℝ) ^ (k + 1) * Vmin := by
        have h7 : 0 < (2 : ℝ) ^ k * Vmin := by positivity
        have h8 : (2 : ℝ) ^ (k + 1) * Vmin =
            2 * ((2 : ℝ) ^ k * Vmin) := by ring
        rw [h8]
        linarith
      have h_pos1 : 0 ≤ (2 : ℝ) ^ k * Vmin := by positivity
      have h9 :
          ENNReal.ofReal ((2 : ℝ) ^ k * Vmin) <
            ENNReal.ofReal ((2 : ℝ) ^ (k + 1) * Vmin) :=
        (ENNReal.ofReal_lt_ofReal_iff_of_nonneg h_pos1).mpr h6
      exact Finset.mem_filter.mpr ⟨h_in_s, lt_trans h_lt h9⟩
    have hf0 : f 0 = ∅ := by
      ext i
      simp only [f, Finset.mem_filter]
      constructor
      · rintro ⟨h_in, h_lt⟩
        have hV : (2 : ℝ) ^ 0 * Vmin = Vmin := by ring
        rw [hV] at h_lt
        exact False.elim (not_le.mpr h_lt (hv_lower i h_in))
      · intro h
        simp at h
    have h_pos1 : 0 ≤ Vmax := by linarith
    have h10 :
        ENNReal.ofReal Vmax < ENNReal.ofReal ((2 : ℝ) ^ N * Vmin) :=
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg h_pos1).mpr h1
    have hfN : f N = s := by
      ext i
      simp only [f, Finset.mem_filter]
      constructor
      · rintro ⟨h, _⟩
        exact h
      · intro hi
        exact ⟨hi, lt_of_le_of_lt (hv_upper i hi) h10⟩
    have hf_mono' : ∀ (m n : ℕ), m ≤ n → f m ⊆ f n := by
      intro m n hmn
      have h_main : ∀ k : ℕ, f m ⊆ f (m + k) := by
        intro k
        induction k with
        | zero => simp
        | succ k ih => exact ih.trans (hf_mono (m + k))
      have h : n = m + (n - m) := by omega
      rw [h]
      exact h_main (n - m)
    let band : ℕ → Finset α := fun k => f (k + 1) \ f k
    have h_sum_bands : ∀ n : ℕ,
        ∑ i ∈ f n, w i = ∑ k ∈ Finset.range n, ∑ i ∈ band k, w i := by
      intro n
      induction n with
      | zero =>
          rw [hf0]
          simp
      | succ n ih =>
          have h_sub : f n ⊆ f (n + 1) := hf_mono n
          have h_eq : f (n + 1) = f n ∪ band n :=
            (Finset.union_sdiff_of_subset h_sub).symm
          have h_disj : Disjoint (f n) (band n) := Finset.disjoint_sdiff
          rw [h_eq, Finset.sum_union h_disj, ih, Finset.sum_range_succ]
    have h_total :
        ∑ k ∈ Finset.range N, ∑ i ∈ band k, w i = ∑ i ∈ s, w i := by
      have h := h_sum_bands N
      rw [hfN] at h
      exact h.symm
    have hN_nonempty : (Finset.range N).Nonempty :=
      Finset.nonempty_range_iff.mpr (ne_of_gt hN_pos)
    rcases finset_ennreal_pigeonhole hN_nonempty
        (fun k : ℕ => ∑ i ∈ band k, w i) with
      ⟨k, hk_in, hge⟩
    let t : Finset α := band k
    let M : ℝ := (2 : ℝ) ^ k * Vmin
    have h_t_subset : t ⊆ s := by
      intro i hi
      exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hi).1).1
    have h_band_property :
        ∀ i ∈ t,
          ENNReal.ofReal M ≤ v i ∧ v i < ENNReal.ofReal (2 * M) := by
      intro i hi
      have h1i : i ∈ f (k + 1) := (Finset.mem_sdiff.mp hi).1
      have h2i : i ∉ f k := (Finset.mem_sdiff.mp hi).2
      have h_in_s : i ∈ s := (Finset.mem_filter.mp h1i).1
      have h3 : v i < ENNReal.ofReal ((2 : ℝ) ^ (k + 1) * Vmin) :=
        (Finset.mem_filter.mp h1i).2
      have h4 : ¬v i < ENNReal.ofReal ((2 : ℝ) ^ k * Vmin) := by
        intro h
        exact h2i (Finset.mem_filter.mpr ⟨h_in_s, h⟩)
      have h5 : ENNReal.ofReal M ≤ v i := by
        by_contra h
        exact h4 (lt_of_not_ge h)
      have h6 : (2 : ℝ) ^ (k + 1) * Vmin = 2 * M := by
        simp [M]
        ring
      rw [h6] at h3
      exact ⟨h5, h3⟩
    have h_retention_N :
        (∑ i ∈ t, w i) * (N : ENNReal) ≥ ∑ i ∈ s, w i := by
      have h :
          (N : ENNReal) * (∑ i ∈ t, w i) ≥ ∑ i ∈ s, w i := by
        simpa [h_total, t] using hge
      simpa [mul_comm] using h
    have h_N_le : (N : ENNReal) ≤ ENNReal.ofReal (x + 1) := by
      have h : (N : ℝ) ≤ x + 1 := hN_le_log
      have h' : (N : ENNReal) = ENNReal.ofReal (N : ℝ) := by simp
      rw [h']
      gcongr
    have h_final :
        (∑ i ∈ t, w i) * ENNReal.ofReal (x + 1) ≥ ∑ i ∈ s, w i := by
      calc
        (∑ i ∈ t, w i) * ENNReal.ofReal (x + 1) ≥
            (∑ i ∈ t, w i) * (N : ENNReal) := by gcongr
        _ ≥ ∑ i ∈ s, w i := h_retention_N
    have hM_ge_Vmin : Vmin ≤ M := by
      dsimp only [M]
      have h : (1 : ℝ) ≤ (2 : ℝ) ^ k := by
        have h' : ∀ n : ℕ, (1 : ℝ) ≤ (2 : ℝ) ^ n := by
          intro n
          induction n with
          | zero => norm_num
          | succ n ih =>
              simp [pow_succ] at *
              linarith
        exact h' k
      have hVmin_nonneg : 0 ≤ Vmin := by linarith
      nlinarith
    refine ⟨M, t, hM_ge_Vmin, h_t_subset, ?_, ?_⟩
    · intro i hi
      exact ⟨(h_band_property i hi).1, le_of_lt (h_band_property i hi).2⟩
    · simpa [x] using h_final
  · refine ⟨Vmin, ∅, le_rfl, by simp, by simp, ?_⟩
    have h_empty : s = ∅ := by
      simpa [Finset.not_nonempty_iff_eq_empty] using hs
    rw [h_empty]
    simp

end Kakeya.Assouad

end section
