import MyLeanRepo.Kakeya.Streamlined.Basic
import MyLeanRepo.Kakeya.Streamlined.Geometry
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Finset.Pi

/-!
# Matrix-entry grid for near-orthogonal transformations

Constructs a finite ε-grid on 3×3 real matrices and filters to near-orthogonal
ones. Used by the tube density test net to generate oriented convex test bodies.

## Main results

- `matrixGrid`: all 3×3 matrices with entries on an ε-grid in [-2,2]
- `isNearOrthogonal`: entrywise |M^T M - I| ≤ 1/10
- `frameMatrices`: filtered grid
- `matrixGrid_card`: cardinality ≤ (11/ε)^9
- `orthogonal_matrix_cover`: every orthogonal matrix has a nearby frame matrix
- `near_orthogonal_det_bound`: 1/2 ≤ |det M| ≤ 2
-/

noncomputable section

attribute [local instance] Classical.propDecidable

open Finset Matrix

namespace Kakeya.Streamlined.GeometricLemmas

/-- Finite grid of 3×3 matrices with each entry on an ε-grid in [-2,2]. -/
def matrixGrid (ε : ℝ) (_hε : 0 < ε) : Finset (Matrix (Fin 3) (Fin 3) ℝ) :=
  let N : ℕ := Nat.ceil (4 / ε)
  let I : Finset ℤ := Finset.Icc (-(N : ℤ)) N
  let domain : Finset (∀ (i : Fin 3), i ∈ (Finset.univ : Finset (Fin 3)) →
                      ∀ (j : Fin 3), j ∈ (Finset.univ : Finset (Fin 3)) → ℤ) :=
    Finset.pi Finset.univ (fun _ : Fin 3 =>
      Finset.pi Finset.univ (fun _ : Fin 3 => I))
  Finset.image (fun f =>
    fun i j => (f i (Finset.mem_univ i) j (Finset.mem_univ j) : ℝ) * ε)
    domain

/-- Any matrix with entries in [-1,1] has a nearby matrixGrid point. -/
lemma matrixGrid_cover {ε : ℝ} (hε : 0 < ε) (hε_le_one : ε ≤ 1)
    (R : Matrix (Fin 3) (Fin 3) ℝ) (hR : ∀ i j, |R i j| ≤ 1) :
    ∃ M ∈ matrixGrid ε hε, ∀ i j, |R i j - M i j| ≤ ε / 2 := by
  let N : ℕ := Nat.ceil (4 / ε)
  have hN : (N : ℝ) ≥ 4 / ε := Nat.le_ceil _
  have h1 : ∀ i j, ∃ (k : ℤ), |R i j - (k : ℝ) * ε| ≤ ε / 2 ∧ |(k : ℝ)| ≤ 4 / ε := by
    intro i j
    let k : ℤ := Int.floor (R i j / ε + 1 / 2)
    have h_rd : |R i j / ε - (k : ℝ)| ≤ 1 / 2 := by
      have h1 : (k : ℝ) ≤ R i j / ε + 1 / 2 := Int.floor_le _
      have h2 : R i j / ε + 1 / 2 < (k : ℝ) + 1 := Int.lt_floor_add_one _
      rw [abs_le] <;> constructor <;> linarith
    have h_dist : |R i j - (k : ℝ) * ε| ≤ ε / 2 := by
      have h5 : R i j - (k : ℝ) * ε = ε * (R i j / ε - (k : ℝ)) := by
        field_simp [hε.ne'] <;> ring
      rw [h5, abs_mul, abs_of_pos hε]
      have h6 : ε * |R i j / ε - (k : ℝ)| ≤ ε * (1 / 2 : ℝ) := by gcongr
      linarith
    have h_bound : |(k : ℝ)| ≤ 1 / ε + 1 / 2 := by
      have h7 : |(k : ℝ) * ε| ≤ |R i j| + |R i j - (k : ℝ) * ε| := by
        calc |(k : ℝ) * ε| = |R i j - (R i j - (k : ℝ) * ε)| := by ring_nf
          _ ≤ |R i j| + |R i j - (k : ℝ) * ε| := abs_sub _ _
      have h8 : |(k : ℝ)| * ε ≤ 1 + ε / 2 := by
        rw [abs_mul, abs_of_nonneg hε.le] at h7
        linarith [hR i j, h_dist]
      calc |(k : ℝ)| = (|(k : ℝ)| * ε) / ε := by field_simp [hε.ne'] <;> ring
        _ ≤ (1 + ε / 2) / ε := by gcongr
        _ = 1 / ε + 1 / 2 := by field_simp [hε.ne'] <;> ring
    have h9 : 1 / ε + 1 / 2 ≤ 4 / ε := by
      have h10 : 1 / 2 ≤ 3 / ε := by
        have h11 : ε ≤ 6 := by linarith
        have h12 : 0 < ε := hε
        have h13 : 3 / ε ≥ 1 / 2 := by
          calc 3 / ε ≥ 3 / 6 := by gcongr
            _ = 1 / 2 := by norm_num
        exact h13
      have h14 : 1 / ε + 1 / 2 ≤ 1 / ε + 3 / ε := by gcongr
      have h15 : 1 / ε + 3 / ε = 4 / ε := by ring
      rw [h15] at h14
      exact h14
    have h10 : |(k : ℝ)| ≤ (N : ℝ) := by
      calc |(k : ℝ)| ≤ 1 / ε + 1 / 2 := h_bound
        _ ≤ 4 / ε := h9
        _ ≤ (N : ℝ) := hN
    exact ⟨k, h_dist, by linarith⟩
  choose k hk_dist hk_bound using h1
  let f : ∀ (i : Fin 3), i ∈ Finset.univ → ∀ (j : Fin 3), j ∈ Finset.univ → ℤ :=
    fun i _ j _ => k i j
  have hk_in : ∀ i j, k i j ∈ Finset.Icc (-(N : ℤ)) N := by
    intro i j
    have h5 : |(k i j : ℝ)| ≤ (N : ℝ) := by linarith [hk_bound i j, hN]
    simp only [Finset.mem_Icc]
    exact ⟨by exact_mod_cast (abs_le.mp h5).1, by exact_mod_cast (abs_le.mp h5).2⟩
  have hf_in : f ∈ Finset.pi Finset.univ (fun _ : Fin 3 =>
      Finset.pi Finset.univ (fun _ : Fin 3 => Finset.Icc (-(N : ℤ)) N)) := by
    rw [Finset.mem_pi]
    intro i _
    rw [Finset.mem_pi]
    intro j _
    exact hk_in i j
  let M : Matrix (Fin 3) (Fin 3) ℝ := fun i j => (k i j : ℝ) * ε
  have hM_in : M ∈ matrixGrid ε hε := by
    simp only [matrixGrid, Finset.mem_image]
    exact ⟨f, hf_in, rfl⟩
  exact ⟨M, hM_in, fun i j => hk_dist i j⟩

/-- Cardinality of the matrix grid is O(ε^{-9}). -/
lemma matrixGrid_card {ε : ℝ} (hε : 0 < ε) (hε_le_one : ε ≤ 1) :
    ((matrixGrid ε hε).card : ℝ) ≤ (11 / ε)^9 := by
  let N : ℕ := Nat.ceil (4 / ε)
  let I : Finset ℤ := Finset.Icc (-(N : ℤ)) N
  let domain := Finset.pi Finset.univ (fun _ : Fin 3 =>
    Finset.pi Finset.univ (fun _ : Fin 3 => I))
  have hI_card : I.card = 2 * N + 1 := by
    simp [I] <;> omega
  have h_inner_card : ∀ i : Fin 3, (Finset.pi Finset.univ (fun _ : Fin 3 => I)).card = (I.card)^3 := by
    intro i
    rw [Finset.card_pi]
    simp [hI_card, Finset.prod_const] <;> ring
  have h_domain_card : domain.card = (I.card)^9 := by
    rw [Finset.card_pi]
    rw [Finset.prod_congr rfl (fun i _ => h_inner_card i)]
    simp [Finset.prod_const] <;> ring
  have h : (matrixGrid ε hε).card ≤ domain.card := Finset.card_image_le
  have hN_le : (N : ℝ) ≤ 4 / ε + 1 := by
    have h5 : (N : ℝ) < 4 / ε + 1 := Nat.ceil_lt_add_one (by positivity)
    linarith
  have h61 : 3 ≤ 3 / ε := by
    have h62 : 0 < ε := hε
    have h63 : ε ≤ 1 := hε_le_one
    have h64 : 3 / ε ≥ 3 / 1 := by gcongr
    simpa using h64
  have h6 : (2 * (N : ℝ) + 1) ≤ 11 / ε := by
    calc 2 * (N : ℝ) + 1 ≤ 2 * (4 / ε + 1) + 1 := by gcongr
      _ = 8 / ε + 3 := by ring
      _ ≤ 8 / ε + 3 / ε := by gcongr
      _ = 11 / ε := by ring
  have h7 : ((I.card : ℝ)) = 2 * (N : ℝ) + 1 := by
    rw [hI_card] <;> norm_cast <;> ring
  have h8 : ((I.card : ℝ)^9) ≤ (11 / ε)^9 := by
    rw [h7]
    gcongr <;> linarith
  have h9 : (matrixGrid ε hε).card ≤ (I.card)^9 := by
    rw [h_domain_card] at h
    exact h
  have h10 : ((matrixGrid ε hε).card : ℝ) ≤ ((I.card : ℝ)^9) := by exact_mod_cast h9
  exact h10.trans h8

/-- A matrix is near-orthogonal if M^T M is entrywise within 1/10 of identity. -/
def isNearOrthogonal (M : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∀ i j : Fin 3, |(M.transpose * M) i j - (if i = j then (1 : ℝ) else (0 : ℝ))| ≤ 1 / 10

/-- The filtered grid of near-orthogonal matrices. -/
def frameMatrices (ε : ℝ) (hε : 0 < ε) : Finset (Matrix (Fin 3) (Fin 3) ℝ) :=
  (matrixGrid ε hε).filter isNearOrthogonal

/-- Cardinality of frameMatrices is O(ε^{-9}). -/
lemma frameMatrices_card {ε : ℝ} (hε : 0 < ε) (hε_le_one : ε ≤ 1) :
    ((frameMatrices ε hε).card : ℝ) ≤ (11 / ε)^9 := by
  have h : (frameMatrices ε hε).card ≤ (matrixGrid ε hε).card :=
    Finset.card_le_card (Finset.filter_subset isNearOrthogonal _)
  have h' : ((frameMatrices ε hε).card : ℝ) ≤ ((matrixGrid ε hε).card : ℝ) := by
    exact_mod_cast h
  exact h'.trans (matrixGrid_card hε hε_le_one)

/-- Orthogonal matrices have entries bounded by 1. -/
private lemma orthogonal_entries_bound {R : Matrix (Fin 3) (Fin 3) ℝ}
    (hR : R.transpose * R = 1) : ∀ i j : Fin 3, |R i j| ≤ 1 := by
  have h_col_norm : ∀ j : Fin 3, ∑ i : Fin 3, (R i j)^2 = 1 := by
    intro j
    have h5 : (R.transpose * R) j j = 1 := by
      rw [hR] <;> simp
    have h6 : (R.transpose * R) j j = ∑ i : Fin 3, R i j * R i j := by
      simp [Matrix.mul_apply, Matrix.transpose_apply] <;> rfl
    rw [h6] at h5
    have h7 : ∑ i : Fin 3, R i j * R i j = ∑ i : Fin 3, (R i j)^2 := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [h7] at h5
    exact h5
  intro i j
  have h6 : (R i j)^2 ≤ ∑ k : Fin 3, (R k j)^2 := by
    exact Finset.single_le_sum (fun k _ => sq_nonneg (R k j)) (Finset.mem_univ i)
  rw [h_col_norm j] at h6
  have h7 : (R i j)^2 ≤ 1 := h6
  have h8 : |R i j| ≤ 1 := by
    have h9 : 0 ≤ |R i j| := by positivity
    nlinarith [sq_abs (R i j)]
  exact h8

/-- Every orthogonal matrix has a nearby frameMatrices entry (ε ≤ 1/40). -/
lemma orthogonal_matrix_cover {ε : ℝ} (hε : 0 < ε) (hε_small : ε ≤ 1 / 40)
    (R : Matrix (Fin 3) (Fin 3) ℝ) (hR : R.transpose * R = 1) :
    ∃ M ∈ frameMatrices ε hε, ∀ i j, |R i j - M i j| ≤ ε / 2 := by
  have hR_entry : ∀ i j, |R i j| ≤ 1 := orthogonal_entries_bound hR
  have hε_le_one : ε ≤ 1 := by linarith
  rcases matrixGrid_cover hε hε_le_one R hR_entry with ⟨M, hM_in, hM_dist⟩
  have h_diff : ∀ i j : Fin 3,
      |(M.transpose * M) i j - (R.transpose * R) i j| ≤ 3 * ε + 3 * ε^2 / 4 := by
    intro i j
    have h1 : (M.transpose * M) i j = ∑ k : Fin 3, M k i * M k j := by
      simp [Matrix.mul_apply, Matrix.transpose_apply] <;> rfl
    have h2 : (R.transpose * R) i j = ∑ k : Fin 3, R k i * R k j := by
      simp [Matrix.mul_apply, Matrix.transpose_apply] <;> rfl
    let f : Fin 3 → ℝ := fun k =>
      R k i * (M k j - R k j) + (M k i - R k i) * R k j +
        (M k i - R k i) * (M k j - R k j)
    have h_eq : (M.transpose * M) i j - (R.transpose * R) i j =
        ∑ k : Fin 3, f k := by
      rw [h1, h2]
      have h_sum : ∑ k : Fin 3, M k i * M k j - ∑ k : Fin 3, R k i * R k j =
          ∑ k : Fin 3, (M k i * M k j - R k i * R k j) := by
        rw [Finset.sum_sub_distrib]
      rw [h_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [h_eq]
    have h_term : ∀ k : Fin 3, |f k| ≤ ε + ε^2 / 4 := by
      intro k
      have hRki : |R k i| ≤ 1 := hR_entry k i
      have hRkj : |R k j| ≤ 1 := hR_entry k j
      have hMdist1 : |M k j - R k j| ≤ ε / 2 := by
        have h : |R k j - M k j| ≤ ε / 2 := hM_dist k j
        rwa [abs_sub_comm] at h
      have hMdist2 : |M k i - R k i| ≤ ε / 2 := by
        have h : |R k i - M k i| ≤ ε / 2 := hM_dist k i
        rwa [abs_sub_comm] at h
      have h1 : |R k i * (M k j - R k j)| ≤ ε / 2 := by
        rw [abs_mul]
        have h : |R k i| * |M k j - R k j| ≤ 1 * (ε / 2) := by
          calc |R k i| * |M k j - R k j|
            ≤ 1 * |M k j - R k j| := by gcongr
          _ ≤ 1 * (ε / 2) := by gcongr
        linarith
      have h2 : |(M k i - R k i) * R k j| ≤ ε / 2 := by
        rw [abs_mul]
        have h : |M k i - R k i| * |R k j| ≤ (ε / 2) * 1 := by
          calc |M k i - R k i| * |R k j|
            ≤ (ε / 2) * |R k j| := by gcongr
          _ ≤ (ε / 2) * 1 := by gcongr
        linarith
      have h3 : |(M k i - R k i) * (M k j - R k j)| ≤ ε^2 / 4 := by
        rw [abs_mul]
        have h : |M k i - R k i| * |M k j - R k j| ≤ (ε / 2) * (ε / 2) := by
          calc |M k i - R k i| * |M k j - R k j|
            ≤ (ε / 2) * |M k j - R k j| := by gcongr
          _ ≤ (ε / 2) * (ε / 2) := by gcongr
        linarith
      set a := R k i * (M k j - R k j)
      set b := (M k i - R k i) * R k j
      set c := (M k i - R k i) * (M k j - R k j)
      have hfk : f k = a + b + c := by
        simp [f, a, b, c] <;> ring
      rw [hfk]
      have h51 : |a + b + c| ≤ |a + b| + |c| := abs_add_le (a + b) c
      have h52 : |a + b| ≤ |a| + |b| := abs_add_le a b
      have h4 : |a + b + c| ≤ |a| + |b| + |c| := by linarith
      linarith
    have h_sum : |∑ k : Fin 3, f k| ≤ ∑ k : Fin 3, |f k| :=
      abs_sum_le_sum_abs f Finset.univ
    have h5 : ∑ k : Fin 3, |f k| ≤ ∑ k : Fin 3, (ε + ε^2 / 4) :=
      Finset.sum_le_sum (fun k _ => h_term k)
    have h6 : ∑ k : Fin 3, (ε + ε^2 / 4) = 3 * (ε + ε^2 / 4) := by
      simp [Finset.sum_const] <;> ring
    rw [h6] at h5
    linarith
  have h_thresh : 3 * ε + 3 * ε^2 / 4 ≤ 1 / 10 := by
    have h7 : ε ≤ 1 / 40 := hε_small
    nlinarith [sq_nonneg ε]
  have h_near : isNearOrthogonal M := by
    intro i j
    have h9 : (R.transpose * R) i j = (if i = j then (1 : ℝ) else (0 : ℝ)) := by
      have h10 : R.transpose * R = (1 : Matrix (Fin 3) (Fin 3) ℝ) := hR
      have h11 : (R.transpose * R) i j = (1 : Matrix (Fin 3) (Fin 3) ℝ) i j := by rw [h10]
      rw [h11]
      simp [Matrix.one_apply]
      <;> split_ifs <;> tauto
    have h_goal : |(M.transpose * M) i j - (if i = j then (1 : ℝ) else (0 : ℝ))| ≤ 1 / 10 := by
      have h10 : (M.transpose * M) i j - (if i = j then (1 : ℝ) else (0 : ℝ)) =
          (M.transpose * M) i j - (R.transpose * R) i j := by
        rw [h9]
      rw [h10]
      have h11 : |(M.transpose * M) i j - (R.transpose * R) i j| ≤ 1 / 10 := by
        calc |(M.transpose * M) i j - (R.transpose * R) i j|
          ≤ 3 * ε + 3 * ε^2 / 4 := h_diff i j
        _ ≤ 1 / 10 := h_thresh
      exact h11
    exact h_goal
  have hM_frame : M ∈ frameMatrices ε hε := by
    simp only [frameMatrices, Finset.mem_filter]
    exact ⟨hM_in, h_near⟩
  exact ⟨M, hM_frame, hM_dist⟩

/-- For near-orthogonal M, the Gram matrix A = M^T M is symmetric. -/
private lemma gram_symmetric (M : Matrix (Fin 3) (Fin 3) ℝ) :
    ∀ i j : Fin 3, (M.transpose * M) i j = (M.transpose * M) j i := by
  have h : (M.transpose * M).transpose = M.transpose * M := by
    have h1 : (M.transpose * M).transpose = M.transpose * (M.transpose).transpose := by
      rw [Matrix.transpose_mul]
    rw [h1, Matrix.transpose_transpose]
  intro i j
  have h2 : (M.transpose * M).transpose i j = (M.transpose * M) j i := by rfl
  have h3 : (M.transpose * M) i j = (M.transpose * M) j i := by
    rw [← h2, h]
  exact h3

/-- Determinant bound for near-orthogonal matrices: 1/2 ≤ |det M| ≤ 2. -/
lemma near_orthogonal_det_bound (M : Matrix (Fin 3) (Fin 3) ℝ)
    (h : isNearOrthogonal M) :
    1 / 2 ≤ |M.det| ∧ |M.det| ≤ 2 := by
  let A := M.transpose * M
  have hA_symm : ∀ i j : Fin 3, A i j = A j i := gram_symmetric M
  have h_diag : ∀ i : Fin 3, 9 / 10 ≤ A i i ∧ A i i ≤ 11 / 10 := by
    intro i
    have h1 : |A i i - 1| ≤ 1 / 10 := by simpa [isNearOrthogonal] using h i i
    have h2 : -1 / 10 ≤ A i i - 1 ∧ A i i - 1 ≤ 1 / 10 := by
      have h3 : |A i i - 1| ≤ 1 / 10 := h1
      have h4 : -(1 / 10) ≤ A i i - 1 ∧ A i i - 1 ≤ 1 / 10 := abs_le.mp h3
      exact ⟨by linarith [h4.1], by linarith [h4.2]⟩
    constructor <;> linarith [h2.1, h2.2]
  have h_off : ∀ (i j : Fin 3), i ≠ j → |A i j| ≤ 1 / 10 := by
    intro i j hne
    have h1 : |A i j| ≤ 1 / 10 := by
      have h2 : i ≠ j := hne
      have h3 : (A i j - (if i = j then (1 : ℝ) else (0 : ℝ))) = A i j := by
        simp [h2]
      have h4 := h i j
      rw [h3] at h4
      simpa using h4
    exact h1
  have h00 : 9 / 10 ≤ A 0 0 := (h_diag 0).1
  have h00' : A 0 0 ≤ 11 / 10 := (h_diag 0).2
  have h11 : 9 / 10 ≤ A 1 1 := (h_diag 1).1
  have h11' : A 1 1 ≤ 11 / 10 := (h_diag 1).2
  have h22 : 9 / 10 ≤ A 2 2 := (h_diag 2).1
  have h22' : A 2 2 ≤ 11 / 10 := (h_diag 2).2
  have h01 : |A 0 1| ≤ 1 / 10 := h_off 0 1 (by decide)
  have h02 : |A 0 2| ≤ 1 / 10 := h_off 0 2 (by decide)
  have h12 : |A 1 2| ≤ 1 / 10 := h_off 1 2 (by decide)
  have h01sq : (A 0 1)^2 ≤ (1 / 10 : ℝ)^2 := by
    have hsq : (A 0 1)^2 = |A 0 1|^2 := Eq.symm (sq_abs (A 0 1))
    rw [hsq]
    gcongr
  have h02sq : (A 0 2)^2 ≤ (1 / 10 : ℝ)^2 := by
    have hsq : (A 0 2)^2 = |A 0 2|^2 := Eq.symm (sq_abs (A 0 2))
    rw [hsq]
    gcongr
  have h12sq : (A 1 2)^2 ≤ (1 / 10 : ℝ)^2 := by
    have hsq : (A 1 2)^2 = |A 1 2|^2 := Eq.symm (sq_abs (A 1 2))
    rw [hsq]
    gcongr
  have h_det_eq : A.det = A 0 0 * A 1 1 * A 2 2 - A 0 0 * (A 1 2)^2 -
      (A 0 1)^2 * A 2 2 + 2 * A 0 1 * A 0 2 * A 1 2 - (A 0 2)^2 * A 1 1 := by
    rw [Matrix.det_fin_three]
    have hs1 : A 1 0 = A 0 1 := hA_symm 1 0
    have hs2 : A 2 0 = A 0 2 := hA_symm 2 0
    have hs3 : A 2 1 = A 1 2 := hA_symm 2 1
    rw [hs1, hs2, hs3] <;> ring
  have h_cross_abs : |2 * A 0 1 * A 0 2 * A 1 2| ≤ 2 * (1 / 10 : ℝ)^3 := by
    have h1 : |2 * A 0 1 * A 0 2 * A 1 2| = 2 * |A 0 1| * |A 0 2| * |A 1 2| := by
      simp [abs_mul] <;> ring
    rw [h1]
    have h2 : |A 0 1| ≤ 1 / 10 := h01
    have h3 : |A 0 2| ≤ 1 / 10 := h02
    have h4 : |A 1 2| ≤ 1 / 10 := h12
    have h5 : 0 ≤ |A 0 1| := by positivity
    have h6 : 0 ≤ |A 0 2| := by positivity
    have h7 : 0 ≤ |A 1 2| := by positivity
    have h8 : |A 0 1| * |A 0 2| * |A 1 2| ≤ (1 / 10 : ℝ)^3 := by
      have h9 : |A 0 1| * |A 0 2| ≤ (1 / 10 : ℝ) * (1 / 10 : ℝ) := by
        calc |A 0 1| * |A 0 2|
          ≤ (1 / 10 : ℝ) * |A 0 2| := by gcongr
        _ ≤ (1 / 10 : ℝ) * (1 / 10 : ℝ) := by gcongr
      calc |A 0 1| * |A 0 2| * |A 1 2|
        ≤ ((1 / 10 : ℝ) * (1 / 10 : ℝ)) * |A 1 2| := by gcongr
      _ ≤ ((1 / 10 : ℝ) * (1 / 10 : ℝ)) * (1 / 10 : ℝ) := by gcongr
      _ = (1 / 10 : ℝ)^3 := by ring
    have h10 : 2 * |A 0 1| * |A 0 2| * |A 1 2| ≤ 2 * (1 / 10 : ℝ)^3 := by
      calc 2 * |A 0 1| * |A 0 2| * |A 1 2|
        = 2 * (|A 0 1| * |A 0 2| * |A 1 2|) := by ring
      _ ≤ 2 * (1 / 10 : ℝ)^3 := by gcongr
    exact h10
  have h_det_low : A.det ≥ 1 / 4 := by
    rw [h_det_eq]
    have h_pos : A 0 0 * A 1 1 * A 2 2 ≥ (9 / 10 : ℝ)^3 := by
      have h4 : 0 ≤ A 0 0 := by linarith
      have h5 : 0 ≤ A 1 1 := by linarith
      have h6 : 0 ≤ A 2 2 := by linarith
      have h7 : (9 / 10 : ℝ) * (9 / 10 : ℝ) ≤ A 0 0 * A 1 1 := by
        have h71 : (9 / 10 : ℝ) ≤ A 0 0 := h00
        have h72 : (9 / 10 : ℝ) ≤ A 1 1 := h11
        have h73 : 0 ≤ (9 / 10 : ℝ) := by positivity
        have h74 : 0 ≤ A 0 0 := by linarith
        exact mul_le_mul h71 h72 h73 h74
      have h7' : (9 / 10 : ℝ)^2 ≤ A 0 0 * A 1 1 := by
        have h_eq : (9 / 10 : ℝ)^2 = (9 / 10 : ℝ) * (9 / 10 : ℝ) := by ring
        rw [h_eq]
        exact h7
      have h8 : A 0 0 * A 1 1 * A 2 2 ≥ (9 / 10 : ℝ)^2 * A 2 2 := by
        exact mul_le_mul_of_nonneg_right h7' h6
      have h9 : (9 / 10 : ℝ)^2 * A 2 2 ≥ (9 / 10 : ℝ)^3 := by
        have hpos : 0 ≤ (9 / 10 : ℝ)^2 := by positivity
        exact mul_le_mul_of_nonneg_left h22 hpos
      linarith
    have h_n1 : -A 0 0 * (A 1 2)^2 ≥ -(11 / 10 : ℝ) * (1 / 10 : ℝ)^2 := by nlinarith
    have h_n2 : -(A 0 1)^2 * A 2 2 ≥ -(1 / 10 : ℝ)^2 * (11 / 10 : ℝ) := by nlinarith
    have h_n3 : 2 * A 0 1 * A 0 2 * A 1 2 ≥ -2 * (1 / 10 : ℝ)^3 := by
      linarith [abs_le.mp h_cross_abs]
    have h_n4 : -(A 0 2)^2 * A 1 1 ≥ -(1 / 10 : ℝ)^2 * (11 / 10 : ℝ) := by nlinarith
    linarith
  have h_det_high : A.det ≤ 4 := by
    rw [h_det_eq]
    have h_pos2 : A 0 0 * A 1 1 * A 2 2 ≤ (11 / 10 : ℝ)^3 := by
      have h4 : 0 ≤ A 0 0 := by linarith
      have h5 : 0 ≤ A 1 1 := by linarith
      have h6 : 0 ≤ A 2 2 := by linarith
      have h7 : A 0 0 * A 1 1 ≤ (11 / 10 : ℝ) * (11 / 10 : ℝ) := by
        have h71 : A 0 0 ≤ (11 / 10 : ℝ) := h00'
        have h72 : A 1 1 ≤ (11 / 10 : ℝ) := h11'
        have h73 : 0 ≤ A 1 1 := by linarith
        have h74 : 0 ≤ (11 / 10 : ℝ) := by positivity
        exact mul_le_mul h71 h72 h73 h74
      have h7' : A 0 0 * A 1 1 ≤ (11 / 10 : ℝ)^2 := by
        have h_eq : (11 / 10 : ℝ)^2 = (11 / 10 : ℝ) * (11 / 10 : ℝ) := by ring
        rw [h_eq]
        exact h7
      have h8 : A 0 0 * A 1 1 * A 2 2 ≤ (11 / 10 : ℝ)^2 * A 2 2 := by
        exact mul_le_mul_of_nonneg_right h7' h6
      have h9 : (11 / 10 : ℝ)^2 * A 2 2 ≤ (11 / 10 : ℝ)^3 := by
        exact mul_le_mul_of_nonneg_left h22' (by positivity)
      linarith
    have h_n1 : -A 0 0 * (A 1 2)^2 ≤ 0 := by nlinarith
    have h_n2 : -(A 0 1)^2 * A 2 2 ≤ 0 := by nlinarith
    have h_n3 : 2 * A 0 1 * A 0 2 * A 1 2 ≤ 2 * (1 / 10 : ℝ)^3 := by
      have h5 : 2 * A 0 1 * A 0 2 * A 1 2 ≤ |2 * A 0 1 * A 0 2 * A 1 2| := le_abs_self _
      linarith [h_cross_abs, h5]
    have h_n4 : -(A 0 2)^2 * A 1 1 ≤ 0 := by nlinarith
    linarith
  have h_detA_eq : A.det = M.det ^ 2 := by
    have h1 : A.det = (M.transpose).det * M.det := by
      rw [Matrix.det_mul]
    rw [h1, Matrix.det_transpose] <;> ring
  rw [h_detA_eq] at h_det_low h_det_high
  have h1 : 1 / 4 ≤ M.det ^ 2 := h_det_low
  have h2 : M.det ^ 2 ≤ 4 := h_det_high
  have h3 : 1 / 2 ≤ |M.det| := by
    have h4 : (1 / 2 : ℝ)^2 ≤ M.det ^ 2 := by nlinarith
    have h5 : |(1 / 2 : ℝ)| ≤ |M.det| := sq_le_sq.mp h4
    norm_num at h5 ⊢
    exact h5
  have h4 : |M.det| ≤ 2 := by
    have h5 : M.det ^ 2 ≤ (2 : ℝ)^2 := by nlinarith
    exact abs_le_of_sq_le_sq h5 (by norm_num)
  exact ⟨h3, h4⟩

end Kakeya.Streamlined.GeometricLemmas
