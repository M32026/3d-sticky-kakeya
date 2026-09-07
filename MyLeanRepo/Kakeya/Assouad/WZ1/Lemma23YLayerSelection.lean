import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23YLayerSelectionStatements
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Tactic

/-!
# WZ1 Lemma 23 y-layer selection

Arithmetic identities for the stride, geometric separation of snapped cell
centers, and a weighted pigeonhole principle over finite residue classes.
-/

namespace Kakeya.Assouad

private lemma wz1Lemma23_gridSide_half (rho : ℝ) :
    gridSide (rho / 2) = rho / Real.sqrt 3 := by
  simp [gridSide] <;> ring

private lemma wz1Lemma23_ratio (rho : ℝ) (hrho : 0 < rho) :
    Real.sqrt rho / gridSide (rho / 2) =
      Real.sqrt 3 / Real.sqrt rho := by
  rw [wz1Lemma23_gridSide_half rho]
  have hsqrt_pos : 0 < Real.sqrt rho :=
    Real.sqrt_pos.mpr hrho
  have hsq : (Real.sqrt rho) ^ 2 = rho :=
    Real.sq_sqrt (by linarith)
  field_simp [hsqrt_pos.ne'] <;> nlinarith

private lemma wz1Lemma23_stride_pos
    (rho : ℝ) (hrho : 0 < rho) :
    0 < wz1Lemma23YStride rho := by
  have hpos :
      0 < Real.sqrt rho / gridSide (rho / 2) := by
    rw [wz1Lemma23_ratio rho hrho] <;> positivity
  exact Nat.ceil_pos.mpr hpos

private lemma wz1Lemma23_ratio_ge_one
    (rho : ℝ) (hrho : 0 < rho) (hrho1 : rho ≤ 1) :
    1 ≤ Real.sqrt rho / gridSide (rho / 2) := by
  rw [wz1Lemma23_ratio rho hrho]
  have h3 : 0 < Real.sqrt rho := Real.sqrt_pos.mpr hrho
  have h4 : Real.sqrt rho ≤ Real.sqrt 3 :=
    Real.sqrt_le_sqrt (by linarith)
  have h5 : 0 ≤ Real.sqrt rho := by positivity
  have h6 :
      Real.sqrt rho / Real.sqrt rho ≤
        Real.sqrt 3 / Real.sqrt rho :=
    div_le_div_of_nonneg_right h4 h5
  have h7 : Real.sqrt rho / Real.sqrt rho = 1 := by
    field_simp [h3.ne'] <;> ring
  rw [h7] at h6
  exact h6

private lemma wz1Lemma23_stride_upper_bound
    (rho : ℝ) (hrho : 0 < rho) (hrho1 : rho ≤ 1) :
    (wz1Lemma23YStride rho : ℝ) ≤
      2 * Real.sqrt 3 / Real.sqrt rho := by
  set x := Real.sqrt rho / gridSide (rho / 2) with hx
  have hside_pos : 0 < gridSide (rho / 2) := by
    simp [gridSide] <;> positivity
  have hx_nonneg : 0 ≤ x := by
    rw [hx]
    exact div_nonneg (by positivity) hside_pos.le
  have h1 : (Nat.ceil x : ℝ) < x + 1 :=
    Nat.ceil_lt_add_one hx_nonneg
  have h2 : x + 1 ≤ 2 * x := by
    linarith [wz1Lemma23_ratio_ge_one rho hrho hrho1]
  have h3 :
      2 * x = 2 * Real.sqrt 3 / Real.sqrt rho := by
    have h4 : x = Real.sqrt 3 / Real.sqrt rho :=
      wz1Lemma23_ratio rho hrho
    rw [h4]
    ring
  calc
    (Nat.ceil x : ℝ) ≤ x + 1 := h1.le
    _ ≤ 2 * x := h2
    _ = 2 * Real.sqrt 3 / Real.sqrt rho := h3

private lemma wz1Lemma23_center_y_diff
    (rho : ℝ) (first second : ℤ × ℤ × ℤ) :
    (wz1Lemma23CellCenter rho first) 1 -
        (wz1Lemma23CellCenter rho second) 1 =
      ((first.2.1 - second.2.1 : ℤ) : ℝ) *
        gridSide (rho / 2) := by
  simp [wz1Lemma23CellCenter, point3]
  ring

private lemma wz1Lemma23_int_divisibility
    {n : ℕ} (hn : 0 < n) {a b : ℤ}
    (hmod : a % (n : ℤ) = b % (n : ℤ)) :
    (n : ℤ) ∣ a - b := by
  have h : (a - b) % (n : ℤ) = 0 := by
    rw [Int.sub_emod, hmod]
    simp
  exact Int.dvd_of_emod_eq_zero h

private lemma wz1Lemma23_abs_ge_of_dvd
    {n : ℕ} (hn : 0 < n) {d : ℤ} (hd : d ≠ 0)
    (hdiv : (n : ℤ) ∣ d) :
    (n : ℝ) ≤ |(d : ℝ)| := by
  rcases hdiv with ⟨k, hk⟩
  have hk_ne_zero : k ≠ 0 := by
    intro h
    rw [h, mul_zero] at hk
    contradiction
  have h5 : |(d : ℝ)| = |(k : ℝ)| * (n : ℝ) := by
    rw [hk]
    simp [abs_mul]
    ring
  rw [h5]
  have h6 : (1 : ℝ) ≤ |(k : ℝ)| := by
    by_cases h7 : 0 ≤ k
    · have h8 : (1 : ℝ) ≤ (k : ℝ) := by
        exact_mod_cast (show 1 ≤ k from by omega)
      have h9 : 0 ≤ (k : ℝ) := by
        exact_mod_cast h7
      rw [abs_of_nonneg h9]
      exact h8
    · have h9 : (k : ℝ) ≤ -1 := by
        exact_mod_cast (show k ≤ -1 from by omega)
      rw [abs_of_nonpos (show (k : ℝ) ≤ 0 by linarith)]
      linarith
  have h10 : 0 ≤ (n : ℝ) := by positivity
  nlinarith

private lemma wz1Lemma23_int_separation
    {n : ℕ} (hn : 0 < n) {a b : ℤ}
    (hmod : a % (n : ℤ) = b % (n : ℤ))
    (hne : a ≠ b) :
    (n : ℝ) ≤ |((a - b : ℤ) : ℝ)| := by
  have hdiv : (n : ℤ) ∣ a - b :=
    wz1Lemma23_int_divisibility hn hmod
  have hne2 : a - b ≠ 0 := by
    intro h
    have : a = b := by linarith
    exact hne this
  exact wz1Lemma23_abs_ge_of_dvd hn hne2 hdiv

private lemma wz1Lemma23_stride_times_side
    (rho : ℝ) (hrho : 0 < rho) :
    (wz1Lemma23YStride rho : ℝ) *
        gridSide (rho / 2) ≥
      Real.sqrt rho := by
  set x := Real.sqrt rho / gridSide (rho / 2) with hx
  have hside_pos : 0 < gridSide (rho / 2) := by
    simp [gridSide] <;> positivity
  have h1 : x ≤ (Nat.ceil x : ℝ) := Nat.le_ceil x
  have h_eq :
      x * gridSide (rho / 2) = Real.sqrt rho := by
    rw [hx]
    field_simp [hside_pos.ne'] <;> ring
  calc
    Real.sqrt rho = x * gridSide (rho / 2) := h_eq.symm
    _ ≤ (Nat.ceil x : ℝ) * gridSide (rho / 2) := by
      gcongr

private lemma wz1Lemma23_separation
    (rho : ℝ) (hrho : 0 < rho)
    (first second : ℤ × ℤ × ℤ)
    (hmod1 :
      first.2.1 % (wz1Lemma23YStride rho : ℤ) =
        second.2.1 % (wz1Lemma23YStride rho : ℤ))
    (hne : first.2.1 ≠ second.2.1) :
    Real.sqrt rho ≤
      |(wz1Lemma23CellCenter rho first) 1 -
        (wz1Lemma23CellCenter rho second) 1| := by
  set n := wz1Lemma23YStride rho with hn
  have hn_pos : 0 < n := wz1Lemma23_stride_pos rho hrho
  have h1 :
      (n : ℝ) ≤
        |((first.2.1 - second.2.1 : ℤ) : ℝ)| :=
    wz1Lemma23_int_separation hn_pos hmod1 hne
  have hside_pos : 0 < gridSide (rho / 2) := by
    simp [gridSide] <;> positivity
  have h2 :
      (n : ℝ) * gridSide (rho / 2) ≤
        |((first.2.1 - second.2.1 : ℤ) : ℝ)| *
          gridSide (rho / 2) := by
    gcongr
  have h3 :
      |(wz1Lemma23CellCenter rho first) 1 -
          (wz1Lemma23CellCenter rho second) 1| =
        |((first.2.1 - second.2.1 : ℤ) : ℝ)| *
          gridSide (rho / 2) := by
    rw [wz1Lemma23_center_y_diff rho first second,
      abs_mul, abs_of_pos hside_pos]
  rw [h3]
  exact (wz1Lemma23_stride_times_side rho hrho).trans h2

private lemma wz1Lemma23_sum_fiberwise_eq_sum
    {α : Type*} [DecidableEq α] {n : ℕ}
    (cells : Finset α) (weight : α → ℕ)
    (f : α → Fin n) :
    ∑ r : Fin n,
        ∑ idx ∈ cells.filter (fun idx => f idx = r),
          weight idx =
      ∑ idx ∈ cells, weight idx := by
  have h1 :
      ∀ r : Fin n,
        ∑ idx ∈ cells.filter (fun idx => f idx = r),
            weight idx =
          ∑ idx ∈ cells,
            if f idx = r then weight idx else 0 := by
    intro r
    rw [Finset.sum_filter] <;> simp
  have h2 :
      ∑ r : Fin n,
          ∑ idx ∈ cells.filter (fun idx => f idx = r),
            weight idx =
        ∑ r : Fin n,
          ∑ idx ∈ cells,
            (if f idx = r then weight idx else 0) := by
    apply Finset.sum_congr rfl
    intro r _
    exact h1 r
  rw [h2, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro idx _
  have h4 :
      ∑ r ∈ (Finset.univ : Finset (Fin n)),
          (if f idx = r then weight idx else 0) =
        if f idx = f idx then weight idx else 0 :=
    Finset.sum_eq_single (f idx)
      (fun y _ hy => by
        have hne : f idx ≠ y := Ne.symm hy
        simp [hne])
      (fun h => by
        exfalso
        exact h (Finset.mem_univ (f idx)))
  simpa using h4

lemma wz1Lemma23_weighted_pigeonhole
    {α : Type*} [DecidableEq α]
    {n : ℕ} (hn : 0 < n)
    (cells : Finset α) (weight : α → ℕ)
    (f : α → Fin n) :
    ∃ r : Fin n,
      (∑ idx ∈ cells, weight idx) ≤
        n * ∑ idx ∈
          cells.filter (fun idx => f idx = r),
          weight idx := by
  let total : ℕ := ∑ idx ∈ cells, weight idx
  by_cases htotal : total = 0
  · refine ⟨⟨0, hn⟩, ?_⟩
    have h9 : (∑ idx ∈ cells, weight idx) = 0 := by
      simpa [total] using htotal
    rw [h9]
    positivity
  · by_contra h
    push Not at h
    have hsum :
        ∑ r : Fin n,
            ∑ idx ∈ cells.filter (fun idx => f idx = r),
              weight idx =
          total :=
      wz1Lemma23_sum_fiberwise_eq_sum cells weight f
    let S : Finset (Fin n) := Finset.univ
    have h_le :
        ∀ r ∈ S,
          n * ∑ idx ∈
              cells.filter (fun idx => f idx = r),
              weight idx ≤
            total :=
      fun r _ => le_of_lt (h r)
    have h_lt :
        ∃ r ∈ S,
          n * ∑ idx ∈
              cells.filter (fun idx => f idx = r),
              weight idx <
            total := by
      let r0 : Fin n := ⟨0, hn⟩
      exact ⟨r0, by simp [S], h r0⟩
    have h4 :
        ∑ r ∈ S,
            (n * ∑ idx ∈
              cells.filter (fun idx => f idx = r),
              weight idx) <
          ∑ r ∈ S, total :=
      Finset.sum_lt_sum h_le h_lt
    have h5 : ∑ r ∈ S, total = n * total := by
      simp [S, Finset.sum_const, Finset.card_fin] <;> ring
    have h6 :
        ∑ r ∈ S,
            (n * ∑ idx ∈
              cells.filter (fun idx => f idx = r),
              weight idx) =
          n * total := by
      have h7 :
          ∑ r ∈ S,
              (n * ∑ idx ∈
                cells.filter (fun idx => f idx = r),
                weight idx) =
            n * ∑ r ∈ S,
              ∑ idx ∈
                cells.filter (fun idx => f idx = r),
                weight idx := by
        rw [Finset.mul_sum]
      rw [h7, hsum] <;> ring
    rw [h6, h5] at h4
    omega

theorem wz1_lemma23_y_layer_selection :
    WZ1Lemma23YLayerSelectionStatement := by
  intro rho hrho hrho_le
  set s : ℕ := wz1Lemma23YStride rho with hs
  have hs_pos : 0 < s :=
    wz1Lemma23_stride_pos rho hrho
  have hs_bound :
      (s : ℝ) ≤ 2 * Real.sqrt 3 / Real.sqrt rho :=
    wz1Lemma23_stride_upper_bound rho hrho hrho_le
  refine ⟨hs_pos, hs_bound, ?_⟩
  intro cells weight
  let f : (ℤ × ℤ × ℤ) → Fin s := fun idx =>
    ⟨(idx.2.1 % (s : ℤ)).toNat, by
      have h1 : 0 ≤ idx.2.1 % (s : ℤ) :=
        Int.emod_nonneg _ (by positivity)
      have h2 : idx.2.1 % (s : ℤ) < (s : ℤ) :=
        Int.emod_lt_of_pos _ (by positivity)
      omega⟩
  have h_f_mod :
      ∀ idx, ((f idx : ℕ) : ℤ) =
        idx.2.1 % (s : ℤ) := by
    intro idx
    have h1 : 0 ≤ idx.2.1 % (s : ℤ) :=
      Int.emod_nonneg _ (by positivity)
    simp [f, Int.toNat_of_nonneg h1]
  have h_filter_eq :
      ∀ r : Fin s,
        cells.filter (fun idx => f idx = r) =
          wz1Lemma23YResidueCells rho cells r := by
    intro r
    ext idx
    simp only [Finset.mem_filter,
      wz1Lemma23YResidueCells]
    have h_iff :
        f idx = r ↔
          idx.2.1 % (s : ℤ) = ((r : ℕ) : ℤ) := by
      constructor
      · intro h
        have h' :
            ((f idx : ℕ) : ℤ) = ((r : ℕ) : ℤ) := by
          rw [h]
        rw [h_f_mod idx] at h'
        exact h'
      · intro h
        apply Fin.ext
        have h' :
            ((f idx : ℕ) : ℤ) = ((r : ℕ) : ℤ) := by
          rw [h_f_mod idx, h]
        exact_mod_cast h'
    tauto
  rcases wz1Lemma23_weighted_pigeonhole
      hs_pos cells weight f with
    ⟨residue, hbound⟩
  use residue
  dsimp only
  have h_selected_eq :
      cells.filter (fun idx => f idx = residue) =
        wz1Lemma23YResidueCells rho cells residue :=
    h_filter_eq residue
  constructor
  · rw [h_selected_eq] at hbound
    exact hbound
  constructor
  · exact Finset.filter_subset _ _
  constructor
  · intro idx hidx
    exact (Finset.mem_filter.mp hidx).2
  · intro first hfirst second hsecond
    by_cases h_y : first.2.1 = second.2.1
    · exact Or.inl h_y
    · have hmod1 :
          first.2.1 % (s : ℤ) =
            ((residue : ℕ) : ℤ) :=
        (Finset.mem_filter.mp hfirst).2
      have hmod2 :
          second.2.1 % (s : ℤ) =
            ((residue : ℕ) : ℤ) :=
        (Finset.mem_filter.mp hsecond).2
      have hmod_eq :
          first.2.1 % (s : ℤ) =
            second.2.1 % (s : ℤ) :=
        hmod1.trans hmod2.symm
      exact Or.inr
        (wz1Lemma23_separation
          rho hrho first second hmod_eq h_y)

end Kakeya.Assouad
