import MyLeanRepo.Kakeya.Assouad.Definitions
import Mathlib.Data.Real.Basic

/-!
# First crossing scale bound

A pure arithmetic lemma: given a branching profile whose weighted
average is near the ambient dimension, the first level where branching
reaches `s` occurs at a normalized scale `a < (n-avg)/(n-s)`.
-/

noncomputable section

open Classical Kakeya.Assouad Finset Real

namespace Kakeya.Assouad

/-- Telescoping over Ico: sum of differences = f k - f m. -/
private lemma telescoping_Ico (f : ℕ → ℝ) (m k : ℕ) (hmk : m ≤ k) :
    ∑ j ∈ Finset.Ico m k, (f (j + 1) - f j) = f k - f m := by
  induction k with
  | zero =>
    have hm0 : m = 0 := by omega
    subst hm0
    simp
  | succ k ih =>
    by_cases h : m ≤ k
    · rw [Finset.sum_Ico_succ_top h, ih h] <;> ring
    · have hm : m = k + 1 := by omega
      subst hm
      simp

/--
First crossing scale bound.

Given `t_i ∈ [0,n]`, `a_0=0`, `a_N=1`, strictly increasing `a`,
weighted average `≥ avgLow`, and `iStar` is the FIRST index with
`t_iStar ≥ s`, then `a_iStar < (n - avgLow)/(n - s)`.
-/
lemma first_crossing_scale_bound
    {N : ℕ} [NeZero N]
    {n s avgLow : ℝ} (hn : 0 < n) (hs : s < n) (havg_lt_n : avgLow < n)
    {a : Fin (N + 1) → ℝ} {t : Fin N → ℝ}
    (ha0 : a 0 = 0) (haN : a (Fin.last N) = 1)
    (hinc : ∀ i : Fin N, a i.castSucc < a i.succ)
    (ht_bound : ∀ i : Fin N, 0 ≤ t i ∧ t i ≤ n)
    (havg : avgLow ≤ ∑ i : Fin N, t i * (a i.succ - a i.castSucc))
    (iStar : Fin N)
    (hiStar_first : ∀ j : Fin N, j < iStar → t j < s) :
    a iStar.castSucc < (n - avgLow) / (n - s) := by
  have hN : 0 < N := NeZero.pos N
  -- Extend a to ℕ for telescoping
  let g : ℕ → ℝ := fun k => if h : k ≤ N then a ⟨k, Nat.lt_succ_iff.mpr h⟩ else 0
  have hg_eq : ∀ (k : ℕ) (hk : k ≤ N), g k = a ⟨k, Nat.lt_succ_iff.mpr hk⟩ := by
    intro k hk; simp [g, hk]
  have hg0 : g 0 = 0 := by
    rw [hg_eq 0 (by linarith)]
    have h : (⟨0, by omega⟩ : Fin (N + 1)) = (0 : Fin (N + 1)) := by
      apply Fin.ext; simp
    rw [h, ha0]
  have hgN : g N = 1 := by
    rw [hg_eq N (by linarith)]
    have h : (⟨N, by omega⟩ : Fin (N + 1)) = Fin.last N := by
      apply Fin.ext; simp
    rw [h, haN]
  have hg_val : ∀ (i : Fin N), g i.val = a i.castSucc := by
    intro i
    have h1 : i.val ≤ N := by have h : i.val < N := i.is_lt; linarith
    rw [hg_eq i.val h1]
    have h_eq : (⟨i.val, Nat.lt_succ_iff.mpr h1⟩ : Fin (N + 1)) = i.castSucc := by
      ext <;> simp
    rw [h_eq]
  have hg_step : ∀ (j : ℕ), (hj : j < N) →
      g (j + 1) - g j = a (⟨j, hj⟩ : Fin N).succ - a (⟨j, hj⟩ : Fin N).castSucc := by
    intro j hj
    have h1 : j ≤ N := by linarith
    have h2 : j + 1 ≤ N := by linarith
    have hgj : g j = a ⟨j, Nat.lt_succ_iff.mpr h1⟩ := by
      rw [hg_eq j h1] <;> rfl
    have hgj1 : g (j + 1) = a ⟨j + 1, Nat.lt_succ_iff.mpr h2⟩ := by
      rw [hg_eq (j + 1) h2] <;> rfl
    have h_eq1 : (⟨j, hj⟩ : Fin N).castSucc = (⟨j, Nat.lt_succ_iff.mpr h1⟩ : Fin (N + 1)) := by
      ext <;> simp
    have h_eq2 : (⟨j, hj⟩ : Fin N).succ = (⟨j + 1, Nat.lt_succ_iff.mpr h2⟩ : Fin (N + 1)) := by
      ext <;> simp
    rw [hgj1, hgj, h_eq2, h_eq1]

  -- Total mkFin function
  let mkFin : ℕ → Fin N := fun x => if h : x < N then ⟨x, h⟩ else ⟨0, hN⟩
  have hmkFin_eq : ∀ (j : ℕ), (hj : j < N) → mkFin j = (⟨j, hj⟩ : Fin N) := by
    intro j hj; simp [mkFin, hj] <;> ext <;> simp
  have hmkFin_val : ∀ (j : ℕ), (hj : j < N) → (mkFin j).val = j := by
    intro j hj; rw [hmkFin_eq j hj] <;> simp
  have hmkFin_inj : ∀ x ∈ Finset.range N, ∀ y ∈ Finset.range N, mkFin x = mkFin y → x = y := by
    intro x hx y hy hxy
    have h1 : (mkFin x).val = (mkFin y).val := by rw [hxy]
    have h2 : (mkFin x).val = x := hmkFin_val x (Finset.mem_range.mp hx)
    have h3 : (mkFin y).val = y := hmkFin_val y (Finset.mem_range.mp hy)
    rw [h2, h3] at h1; exact h1
  have h_image : Finset.image mkFin (Finset.range N) = (Finset.univ : Finset (Fin N)) := by
    ext y
    constructor
    · intro h; rcases Finset.mem_image.mp h with ⟨x, _, rfl⟩; simp
    · intro _
      have h2 : mkFin y.val = y := hmkFin_eq y.val y.is_lt
      exact Finset.mem_image.mpr ⟨y.val, Finset.mem_range.mpr y.is_lt, h2⟩

  let W := a iStar.castSucc
  have hW_eq : W = g iStar.val := by
    rw [hg_val iStar]
  let m := iStar.val

  -- Define product function on Fin N
  let f : Fin N → ℝ := fun i => t i * (a i.succ - a i.castSucc)

  -- Convert Fin sum to range sum using mkFin
  have h_sum_range : ∑ i : Fin N, f i =
      ∑ k ∈ Finset.range N, t (mkFin k) * (g (k + 1) - g k) := by
    have h_eq : ∑ i : Fin N, f i = ∑ k ∈ Finset.range N, f (mkFin k) := by
      rw [← h_image, Finset.sum_image hmkFin_inj]
    rw [h_eq]
    apply Finset.sum_congr rfl
    intro k hk
    have h_k_lt_N : k < N := Finset.mem_range.mp hk
    have h_mk : mkFin k = ⟨k, h_k_lt_N⟩ := hmkFin_eq k h_k_lt_N
    rw [h_mk]
    have h6 : g (k + 1) - g k = a (⟨k, h_k_lt_N⟩ : Fin N).succ - a (⟨k, h_k_lt_N⟩ : Fin N).castSucc :=
      hg_step k h_k_lt_N
    rw [h6] <;> rfl

  -- Before: range m, after: Ico m N
  have h_disj : Disjoint (Finset.range m) (Finset.Ico m N) := by
    simp [Finset.disjoint_left] <;> omega
  have h_univ : Finset.range m ∪ Finset.Ico m N = Finset.range N := by
    ext x; simp [Finset.mem_range, Finset.mem_Ico] <;> omega
  have h_sum_split :
      ∑ k ∈ Finset.range N, t (mkFin k) * (g (k + 1) - g k) =
      ∑ k ∈ Finset.range m, t (mkFin k) * (g (k + 1) - g k) +
      ∑ k ∈ Finset.Ico m N, t (mkFin k) * (g (k + 1) - g k) := by
    rw [← Finset.sum_union h_disj, h_univ]

  have h_range_eq_Ico : Finset.range m = Finset.Ico 0 m := by
    ext x; simp [Finset.mem_range, Finset.mem_Ico] <;> omega
  have h_telescope_before : ∑ k ∈ Finset.range m, (g (k + 1) - g k) = g m - g 0 := by
    rw [h_range_eq_Ico]
    exact telescoping_Ico g 0 m (by omega)
  have h_telescope_after : ∑ k ∈ Finset.Ico m N, (g (k + 1) - g k) = g N - g m :=
    telescoping_Ico g m N (by omega)

  by_cases h_m0 : m = 0
  · -- iStar = 0, W = 0
    have h_iStar_val : iStar.val = 0 := h_m0
    have hW : W = 0 := by
      rw [hW_eq, h_iStar_val, hg0]
    have hW' : a iStar.castSucc = 0 := by
      simpa [W] using hW
    rw [hW']
    have h_pos : 0 < (n - avgLow) / (n - s) := by
      apply div_pos
      · linarith [havg_lt_n]
      · linarith [hs]
    exact h_pos
  · have h_m_pos : 0 < m := by omega
    have h_before_nonempty : (Finset.range m).Nonempty := by
      refine' ⟨0, _⟩
      simp [h_m_pos]
    have h_m_lt_N : m < N := iStar.is_lt
    have h_weights_pos : ∀ k ∈ Finset.range m, 0 < g (k + 1) - g k := by
      intro k hk
      have h_k_lt_m : k < m := Finset.mem_range.mp hk
      have h_k_lt_N : k < N := by linarith
      rw [hg_step k h_k_lt_N]
      exact sub_pos.mpr (hinc ⟨k, h_k_lt_N⟩)
    have h_t_before_lt :
        ∑ k ∈ Finset.range m, t (mkFin k) * (g (k + 1) - g k) < s * (g m - g 0) := by
      have h1 : ∑ k ∈ Finset.range m, t (mkFin k) * (g (k + 1) - g k) <
              ∑ k ∈ Finset.range m, s * (g (k + 1) - g k) :=
        Finset.sum_lt_sum_of_nonempty h_before_nonempty
          (fun k hk =>
            have h_k_lt_m : k < m := Finset.mem_range.mp hk
            have h_k_lt_N : k < N := by linarith
            have h_j_lt_iStar : mkFin k < iStar := by
              rw [hmkFin_eq k h_k_lt_N]
              simp [m, Fin.lt_def] <;> linarith
            have h_t_lt : t (mkFin k) < s := hiStar_first (mkFin k) h_j_lt_iStar
            mul_lt_mul_of_pos_right h_t_lt (h_weights_pos k hk))
      have h2 : ∑ k ∈ Finset.range m, s * (g (k + 1) - g k) = s * (g m - g 0) := by
        rw [← Finset.mul_sum, h_telescope_before] <;> ring
      rw [h2] at h1
      exact h1
    have h_t_after_le :
        ∑ k ∈ Finset.Ico m N, t (mkFin k) * (g (k + 1) - g k) ≤ n * (g N - g m) := by
      have h1 : ∑ k ∈ Finset.Ico m N, t (mkFin k) * (g (k + 1) - g k) ≤
              ∑ k ∈ Finset.Ico m N, n * (g (k + 1) - g k) := by
        apply Finset.sum_le_sum
        intro k hk
        have h_k_lt_N : k < N := (Finset.mem_Ico.mp hk).2
        have hti : t (mkFin k) ≤ n := (ht_bound (mkFin k)).2
        have hpos : 0 ≤ g (k + 1) - g k := by
          rw [hg_step k h_k_lt_N]; linarith [hinc ⟨k, h_k_lt_N⟩]
        nlinarith
      have h2 : ∑ k ∈ Finset.Ico m N, n * (g (k + 1) - g k) = n * (g N - g m) := by
        rw [← Finset.mul_sum, h_telescope_after] <;> ring
      rw [h2] at h1
      exact h1
    have h_main : avgLow < n - W * (n - s) := by
      calc
        avgLow
          ≤ ∑ i : Fin N, f i := havg
        _ = ∑ k ∈ Finset.range N, t (mkFin k) * (g (k + 1) - g k) := h_sum_range
        _ = ∑ k ∈ Finset.range m, t (mkFin k) * (g (k + 1) - g k) +
              ∑ k ∈ Finset.Ico m N, t (mkFin k) * (g (k + 1) - g k) := h_sum_split
        _ < s * (g m - g 0) + n * (g N - g m) := by linarith
        _ = s * W + n * (1 - W) := by
          rw [hW_eq, hg0, hgN] <;> ring
        _ = n - W * (n - s) := by ring
    have h_ns_pos : 0 < n - s := by linarith
    have h : W * (n - s) < n - avgLow := by linarith
    have h_final : W < (n - avgLow) / (n - s) := by
      calc
        W = (W * (n - s)) / (n - s) := by field_simp [h_ns_pos.ne'] <;> ring
        _ < ((n - avgLow) / (n - s)) := by gcongr <;> linarith
    exact h_final

end Kakeya.Assouad
