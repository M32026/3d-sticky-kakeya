import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains

/-!
# Trivial interval covering lemmas

Elementary covering-number bounds for subsets of intervals, used in the
LOW case of the local AD dichotomy.
-/

noncomputable section

open Metric Set

namespace Kakeya.Assouad

/-- A subset of an interval `[left, left+length]` can be covered by at most
`⌈length/ε⌉ + 1` balls of radius `ε`. -/
lemma externalCoveringNumber_subset_interval
    {S : Set ℝ} {left length ε : ℝ} (hε : 0 < ε) (hlen : 0 ≤ length)
    (hS : S ⊆ Set.Icc left (left + length)) :
    (↑(Metric.externalCoveringNumber ⟨ε, hε.le⟩ S) : ENNReal) ≤
      ENNReal.ofReal (length / ε) + 2 := by
  let n : ℕ := Nat.ceil (length / ε)
  let centers : Finset ℝ :=
    Finset.image (fun k : ℕ => left + (k : ℝ) * ε) (Finset.range (n + 1))
  have hcover : Metric.IsCover ⟨ε, hε.le⟩ S (centers : Set ℝ) := by
    intro x hx
    have hx1 : left ≤ x := (hS hx).1
    have hx2 : x ≤ left + length := (hS hx).2
    set y : ℝ := x - left with hy_def
    have hy0 : 0 ≤ y := by linarith
    have hy1 : y ≤ length := by linarith
    have h_ydiv_nonneg : 0 ≤ y / ε := by positivity
    set k : ℕ := Nat.floor (y / ε) with hk_def
    have hk1 : (k : ℝ) ≤ y / ε := Nat.floor_le h_ydiv_nonneg
    have hk2 : y / ε < (k : ℝ) + 1 := Nat.lt_floor_add_one (y / ε)
    have h_k_le_n : k ≤ n := by
      have h1 : (k : ℝ) ≤ y / ε := hk1
      have h2 : y / ε ≤ length / ε := by gcongr
      have h3 : length / ε ≤ (n : ℝ) := by
        exact Nat.le_ceil (length / ε)
      have h4 : (k : ℝ) ≤ (n : ℝ) := by linarith
      exact_mod_cast h4
    have h_k_lt_succ : k < n + 1 := by omega
    set c : ℝ := left + (k : ℝ) * ε with hc_def
    have hc_in : c ∈ (centers : Set ℝ) := by
      simp only [centers, Finset.mem_coe, Finset.mem_image]
      exact ⟨k, Finset.mem_range.mpr h_k_lt_succ, rfl⟩
    have h_lem1 : (k : ℝ) * ε ≤ y := by
      have h : (k : ℝ) ≤ y / ε := hk1
      have h' : (k : ℝ) * ε ≤ (y / ε) * ε :=
        mul_le_mul_of_nonneg_right h hε.le
      have h'' : (y / ε) * ε = y := by
        field_simp [hε.ne'] <;> ring
      rw [h''] at h'
      exact h'
    have h_lem2 : y < (k : ℝ) * ε + ε := by
      have h : y / ε < (k : ℝ) + 1 := hk2
      have h' : (y / ε) * ε < ((k : ℝ) + 1) * ε :=
        mul_lt_mul_of_pos_right h hε
      have h'' : (y / ε) * ε = y := by
        field_simp [hε.ne'] <;> ring
      rw [h''] at h'
      have h3 : ((k : ℝ) + 1) * ε = (k : ℝ) * ε + ε := by ring
      rw [h3] at h'
      exact h'
    have hdist : dist x c ≤ ε := by
      have h_eq : x - c = y - (k : ℝ) * ε := by
        simp [hy_def, hc_def] <;> ring
      rw [Real.dist_eq, h_eq]
      have h5 : 0 ≤ y - (k : ℝ) * ε := by linarith
      have h6 : y - (k : ℝ) * ε ≤ ε := by linarith
      have h7 : |y - (k : ℝ) * ε| ≤ ε := by
        rw [abs_le] <;> constructor <;> linarith
      exact h7
    exact ⟨c, hc_in, by simpa [Set.mem_setOf_eq] using dist_le_coe.mpr hdist⟩
  have h_main : (Metric.externalCoveringNumber ⟨ε, hε.le⟩ S : ENNReal) ≤
      (centers : Set ℝ).encard := by
    exact_mod_cast hcover.externalCoveringNumber_le_encard
  have h_card1 : (centers : Set ℝ).encard = (centers.card : ENNReal) := by
    simp
  have h_card2 : centers.card ≤ n + 1 := by
    have h : centers.card ≤ (Finset.range (n + 1)).card := by
      exact Finset.card_image_le
    simpa using h
  have h_n_le1 : (n : ENNReal) + 1 ≤ ENNReal.ofReal (length / ε) + 2 := by
    have h4 : (n : ℝ) ≤ length / ε + 1 := by
      have h5 : (n : ℝ) = Nat.ceil (length / ε) := by rfl
      rw [h5]
      have h6 : 0 ≤ length / ε := by positivity
      have h7 : (Nat.ceil (length / ε) : ℝ) < length / ε + 1 :=
        Nat.ceil_lt_add_one h6
      linarith
    have h8 : (n : ENNReal) + 1 = ENNReal.ofReal ((n : ℝ) + 1) := by
      norm_cast
    have h9 : ENNReal.ofReal ((n : ℝ) + 1) ≤ ENNReal.ofReal (length / ε + 2) :=
      ENNReal.ofReal_le_ofReal (by linarith)
    have h10 : ENNReal.ofReal (length / ε + 2) = ENNReal.ofReal (length / ε) + 2 := by
      have h11 : 0 ≤ length / ε := by positivity
      rw [ENNReal.ofReal_add h11 (by norm_num)] <;> simp
    have h12 : (n : ENNReal) + 1 ≤ ENNReal.ofReal (length / ε) + 2 := by
      calc (n : ENNReal) + 1
        = ENNReal.ofReal ((n : ℝ) + 1) := h8
      _ ≤ ENNReal.ofReal (length / ε + 2) := h9
      _ = ENNReal.ofReal (length / ε) + 2 := h10
    exact h12
  calc
    (Metric.externalCoveringNumber ⟨ε, hε.le⟩ S : ENNReal)
      ≤ (centers : Set ℝ).encard := h_main
    _ = (centers.card : ENNReal) := h_card1
    _ ≤ ((n + 1 : ℕ) : ENNReal) := by exact_mod_cast h_card2
    _ = (n : ENNReal) + 1 := by simp
    _ ≤ ENNReal.ofReal (length / ε) + 2 := h_n_le1

end Kakeya.Assouad

end
