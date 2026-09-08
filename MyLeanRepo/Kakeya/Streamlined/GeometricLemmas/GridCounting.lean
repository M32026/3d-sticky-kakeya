import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod

/-!
# Grid covering and counting lemma

Covers a rectangle `[xmin, xmax] × [ymin, ymax]` by a finite grid of cells
of side length `s`, with an explicit bound on the number of cells.

This is used in the phase-space packing argument to count position cells
and direction cells independently.
-/

namespace Kakeya.Streamlined.GeometricLemmas

/--
For any real `t ∈ [0, M]`, there exists a natural number `n ≤ Nat.ceil M`
such that `|t - n| ≤ 1/2`.

We use `n = ⌊t + 1/2⌋`. Since `t ≥ 0`, `n ≥ 0`.
Since `t ≤ M`, we have `t + 1/2 ≤ M + 1/2 < ⌈M⌉ + 1`, so `⌊t + 1/2⌋ ≤ ⌈M⌉`.
-/
lemma exists_nearest_nat_le_ceil {t M : ℝ} (ht0 : 0 ≤ t) (hM : t ≤ M) :
    ∃ (n : ℕ), n ≤ Nat.ceil M ∧ |t - (n : ℝ)| ≤ 1 / 2 := by
  let k : ℤ := Int.floor (t + 1 / 2)
  have h1 : (k : ℝ) ≤ t + 1 / 2 := Int.floor_le (t + 1 / 2)
  have h2 : t + 1 / 2 < (k : ℝ) + 1 := Int.lt_floor_add_one (t + 1 / 2)
  have h_abs : |t - (k : ℝ)| ≤ 1 / 2 := by
    have h3 : (k : ℝ) - 1 / 2 ≤ t := by linarith
    have h4 : t ≤ (k : ℝ) + 1 / 2 := by linarith
    rw [abs_le] <;> constructor <;> linarith
  have hk_nonneg : 0 ≤ k := by
    have h5 : 0 ≤ t + 1 / 2 := by linarith
    exact Int.floor_nonneg.mpr h5
  let n : ℕ := k.toNat
  have hn_eq : (n : ℝ) = (k : ℝ) := by
    have h : (n : ℤ) = k := Int.toNat_of_nonneg hk_nonneg
    exact_mod_cast h
  have h_n_le : n ≤ Nat.ceil M := by
    have h_t_le : t + 1 / 2 ≤ M + 1 / 2 := by linarith
    have h7 : Int.floor (t + 1 / 2) ≤ Int.floor (M + 1 / 2) := Int.floor_mono h_t_le
    have h9 : M + 1 / 2 < (Nat.ceil M : ℝ) + 1 := by
      have h10 : M ≤ (Nat.ceil M : ℝ) := Nat.le_ceil M
      linarith
    have h11 : Int.floor (M + 1 / 2) ≤ (Nat.ceil M : ℤ) := by
      by_contra h12
      have h13 : (Nat.ceil M : ℤ) + 1 ≤ Int.floor (M + 1 / 2) := by linarith
      have h14 : ((Nat.ceil M : ℤ) + 1 : ℝ) ≤ (Int.floor (M + 1 / 2) : ℝ) := by exact_mod_cast h13
      have h15 : (Int.floor (M + 1 / 2) : ℝ) ≤ M + 1 / 2 := Int.floor_le (M + 1 / 2)
      have h16 : (Nat.ceil M : ℝ) + 1 ≤ M + 1 / 2 := by
        calc (Nat.ceil M : ℝ) + 1
          = ((Nat.ceil M : ℤ) + 1 : ℝ) := by simp
        _ ≤ (Int.floor (M + 1 / 2) : ℝ) := h14
        _ ≤ M + 1 / 2 := h15
      linarith
    have h13 : k ≤ (Nat.ceil M : ℤ) := le_trans h7 h11
    have h14 : (n : ℤ) = k := Int.toNat_of_nonneg hk_nonneg
    have h15 : (n : ℤ) ≤ (Nat.ceil M : ℤ) := by
      rw [h14] <;> exact h13
    exact_mod_cast h15
  exact ⟨n, h_n_le, by rw [hn_eq] <;> exact h_abs⟩

/--
A rectangle `[xmin, xmax] × [ymin, ymax]` can be covered by a finite grid of
`s × s` cells (represented by their centers).  The number of cells is at most
`((xmax - xmin)/s + 2) * ((ymax - ymin)/s + 2)`.

Every point in the rectangle is within distance `s/2` (in each coordinate)
of some grid center.
-/
lemma grid_cover_bound (xmin xmax ymin ymax s : ℝ) (hs : 0 < s)
    (hx : xmin ≤ xmax) (hy : ymin ≤ ymax) :
    ∃ (cells : Finset (ℝ × ℝ)),
      (∀ (p : ℝ × ℝ), xmin ≤ p.1 → p.1 ≤ xmax → ymin ≤ p.2 → p.2 ≤ ymax →
        ∃ c ∈ cells, |p.1 - c.1| ≤ s / 2 ∧ |p.2 - c.2| ≤ s / 2) ∧
      (cells.card : ℝ) ≤ ((xmax - xmin) / s + 2) * ((ymax - ymin) / s + 2) := by
  set Mx : ℝ := (xmax - xmin) / s with hMx_def
  set My : ℝ := (ymax - ymin) / s with hMy_def
  set nx : ℕ := Nat.ceil Mx + 1 with hnx_def
  set ny : ℕ := Nat.ceil My + 1 with hny_def
  let grid : Finset (ℕ × ℕ) := (Finset.range nx) ×ˢ (Finset.range ny)
  let cells : Finset (ℝ × ℝ) :=
    grid.image (fun (ij : ℕ × ℕ) => (xmin + (ij.1 : ℝ) * s, ymin + (ij.2 : ℝ) * s))
  have hMx_nonneg : 0 ≤ Mx := by
    rw [hMx_def] <;> apply div_nonneg <;> linarith
  have hMy_nonneg : 0 ≤ My := by
    rw [hMy_def] <;> apply div_nonneg <;> linarith
  have h_inj : Function.Injective
      (fun (ij : ℕ × ℕ) => (xmin + (ij.1 : ℝ) * s, ymin + (ij.2 : ℝ) * s)) := by
    intro ⟨i1, j1⟩ ⟨i2, j2⟩ h
    have h_eq1 : xmin + (i1 : ℝ) * s = xmin + (i2 : ℝ) * s := by
      exact congr_arg Prod.fst h
    have h_eq2 : ymin + (j1 : ℝ) * s = ymin + (j2 : ℝ) * s := by
      exact congr_arg Prod.snd h
    have h1 : (i1 : ℝ) * s = (i2 : ℝ) * s := by linarith
    have h2 : (j1 : ℝ) * s = (j2 : ℝ) * s := by linarith
    have hi : i1 = i2 := by
      have h3 : (i1 : ℝ) = (i2 : ℝ) := by
        apply mul_right_cancel₀ hs.ne'
        exact h1
      exact_mod_cast h3
    have hj : j1 = j2 := by
      have h3 : (j1 : ℝ) = (j2 : ℝ) := by
        apply mul_right_cancel₀ hs.ne'
        exact h2
      exact_mod_cast h3
    exact Prod.ext hi hj
  have h_card : cells.card = nx * ny := by
    rw [Finset.card_image_of_injective _ h_inj]
    rw [Finset.card_product]
    <;> simp [grid]
    <;> ring
  refine ⟨cells, ?_, ?_⟩
  · -- Covering property
    intro p hx1 hx2 hy1 hy2
    set tx : ℝ := (p.1 - xmin) / s with htx_def
    set ty : ℝ := (p.2 - ymin) / s with hty_def
    have htx0 : 0 ≤ tx := by
      rw [htx_def] <;> apply div_nonneg <;> linarith
    have htxM : tx ≤ Mx := by
      rw [htx_def, hMx_def] <;> apply div_le_div_of_nonneg_right <;> linarith
    have hty0 : 0 ≤ ty := by
      rw [hty_def] <;> apply div_nonneg <;> linarith
    have htyM : ty ≤ My := by
      rw [hty_def, hMy_def] <;> apply div_le_div_of_nonneg_right <;> linarith
    rcases exists_nearest_nat_le_ceil htx0 htxM with ⟨i, hi_le, hi_abs⟩
    rcases exists_nearest_nat_le_ceil hty0 htyM with ⟨j, hj_le, hj_abs⟩
    have hi_lt : i < nx := by
      rw [hnx_def] <;> exact Nat.lt_succ_of_le hi_le
    have hj_lt : j < ny := by
      rw [hny_def] <;> exact Nat.lt_succ_of_le hj_le
    let c : ℝ × ℝ := (xmin + (i : ℝ) * s, ymin + (j : ℝ) * s)
    have hc_in : c ∈ cells := by
      apply Finset.mem_image.mpr
      have hmem : (i, j) ∈ grid := by
        have h_i_in : i ∈ Finset.range nx := Finset.mem_range.mpr hi_lt
        have h_j_in : j ∈ Finset.range ny := Finset.mem_range.mpr hj_lt
        exact Finset.mem_product.mpr ⟨h_i_in, h_j_in⟩
      refine ⟨(i, j), hmem, rfl⟩
    have h1 : |p.1 - c.1| ≤ s / 2 := by
      dsimp only [c]
      have h_eq : p.1 - (xmin + (i : ℝ) * s) = s * (tx - (i : ℝ)) := by
        rw [htx_def]
        field_simp [hs.ne'] <;> ring
      rw [h_eq, abs_mul, abs_of_pos hs]
      have h : s * |tx - (i : ℝ)| ≤ s * (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hi_abs (by linarith)
      have h' : s * (1 / 2 : ℝ) = s / 2 := by ring
      rw [h'] at h
      exact h
    have h2 : |p.2 - c.2| ≤ s / 2 := by
      dsimp only [c]
      have h_eq : p.2 - (ymin + (j : ℝ) * s) = s * (ty - (j : ℝ)) := by
        rw [hty_def]
        field_simp [hs.ne'] <;> ring
      rw [h_eq, abs_mul, abs_of_pos hs]
      have h : s * |ty - (j : ℝ)| ≤ s * (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hj_abs (by linarith)
      have h' : s * (1 / 2 : ℝ) = s / 2 := by ring
      rw [h'] at h
      exact h
    exact ⟨c, hc_in, h1, h2⟩
  · -- Cardinality bound
    rw [h_card]
    have h_ceil1 : (Nat.ceil Mx : ℝ) ≤ Mx + 1 := by
      by_cases h : Nat.ceil Mx = 0
      · have h' : (Nat.ceil Mx : ℝ) = 0 := by exact_mod_cast h
        rw [h']
        exact add_nonneg hMx_nonneg (by norm_num)
      · have hpos : 0 < Nat.ceil Mx := Nat.pos_of_ne_zero h
        have h1le : 1 ≤ Nat.ceil Mx := by exact_mod_cast hpos
        let m : ℕ := Nat.ceil Mx - 1
        have h31 : m < Nat.ceil Mx := Nat.sub_lt hpos (by norm_num)
        have h3 : (m : ℝ) < Mx := (Nat.lt_ceil (a := Mx)).mp h31
        have h4 : (m : ℝ) = (Nat.ceil Mx : ℝ) - 1 := by
          rw [Nat.cast_sub h1le] <;> norm_num
        have h5 : (Nat.ceil Mx : ℝ) - 1 < Mx := by
          rw [←h4] <;> exact h3
        linarith
    have h_ceil2 : (Nat.ceil My : ℝ) ≤ My + 1 := by
      by_cases h : Nat.ceil My = 0
      · have h' : (Nat.ceil My : ℝ) = 0 := by exact_mod_cast h
        rw [h']
        exact add_nonneg hMy_nonneg (by norm_num)
      · have hpos : 0 < Nat.ceil My := Nat.pos_of_ne_zero h
        have h1le : 1 ≤ Nat.ceil My := by exact_mod_cast hpos
        let m : ℕ := Nat.ceil My - 1
        have h31 : m < Nat.ceil My := Nat.sub_lt hpos (by norm_num)
        have h3 : (m : ℝ) < My := (Nat.lt_ceil (a := My)).mp h31
        have h4 : (m : ℝ) = (Nat.ceil My : ℝ) - 1 := by
          rw [Nat.cast_sub h1le] <;> norm_num
        have h5 : (Nat.ceil My : ℝ) - 1 < My := by
          rw [←h4] <;> exact h3
        linarith
    have h1 : (nx : ℝ) ≤ Mx + 2 := by
      rw [hnx_def] <;> simp [h_ceil1] <;> linarith
    have h3 : (ny : ℝ) ≤ My + 2 := by
      rw [hny_def] <;> simp [h_ceil2] <;> linarith
    have h4 : ((nx * ny : ℕ) : ℝ) = (nx : ℝ) * (ny : ℝ) := by
      simp
    rw [h4]
    have h5 : 0 ≤ (nx : ℝ) := by exact_mod_cast Nat.zero_le nx
    have h6 : 0 ≤ (ny : ℝ) := by exact_mod_cast Nat.zero_le ny
    have h7 : 0 ≤ Mx + 2 := by linarith
    have h8 : 0 ≤ My + 2 := by linarith
    gcongr
    <;> linarith

end Kakeya.Streamlined.GeometricLemmas
