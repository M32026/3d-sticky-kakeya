import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.TubeDensityTestNet.Main
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.TubeDensityTestNet.GeometricLemmas
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.TubeDensityTestNet.Grids
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.FrameMatrixGrid
import MyLeanRepo.Kakeya.Streamlined.VolumeHelpers
import MyLeanRepo.Kakeya.Streamlined.Geometry
import MyLeanRepo.Kakeya.Streamlined.Families

/-!
# Rounding lemma for tube density test net

Given a convex body H with John framed dimensions, construct a test
parallelepiped from the discrete grids containing H with volume
at most 10^7 * volume(H).
-/

noncomputable section

open BigOperators Classical
open MeasureTheory Metric Finset
open scoped Pointwise
open Kakeya.Streamlined.GeometricLemmas
open Kakeya.Streamlined.RandomTranslation.TubeDensityTestNet

namespace Kakeya.Streamlined

/-- If an axis box is contained in a set of diameter ≤ 20, each dimension ≤ 20. -/
lemma box_dim_bound (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (S : Set Point3) (hsub : axisBox a b c ⊆ S)
    (hdiam : ∀ (x y : Point3), x ∈ S → y ∈ S → dist x y ≤ 20) :
    a ≤ 20 ∧ b ≤ 20 ∧ c ≤ 20 := by
  have h_main : ∀ (d : ℝ), 0 < d →
      (∃ (p1 p2 : Point3), p1 ∈ axisBox a b c ∧ p2 ∈ axisBox a b c ∧ dist p1 p2 = d) → d ≤ 20 := by
    intro d hd ⟨p1, p2, hp1, hp2, hdist⟩
    have h4 : dist p1 p2 ≤ 20 := hdiam p1 p2 (hsub hp1) (hsub hp2)
    linarith [hdist]
  let e0 : Point3 := EuclideanSpace.single 0 1
  let e1 : Point3 := EuclideanSpace.single 1 1
  let e2 : Point3 := EuclideanSpace.single 2 1
  have h_in_box : ∀ (p : Point3), (|p 0| ≤ a / 2) → (|p 1| ≤ b / 2) → (|p 2| ≤ c / 2) → p ∈ axisBox a b c := by
    intro p h0 h1 h2
    simp only [axisBox, Set.mem_setOf_eq]
    exact ⟨h0, h1, h2⟩
  have ha2 : a ≤ 20 := by
    let p1 := (a / 2) • e0
    let p2 := (-a / 2) • e0
    have hp1 : p1 ∈ axisBox a b c := by
      have h1 : |p1 0| ≤ a / 2 := by
        have h11 : p1 0 = a / 2 := by simp [p1, e0, EuclideanSpace.single_apply]
        rw [h11]; rw [abs_of_nonneg (by linarith)]
      have h2 : |p1 1| ≤ b / 2 := by
        have h21 : p1 1 = 0 := by simp [p1, e0, EuclideanSpace.single_apply]
        rw [h21]; simp; linarith
      have h3 : |p1 2| ≤ c / 2 := by
        have h31 : p1 2 = 0 := by simp [p1, e0, EuclideanSpace.single_apply]
        rw [h31]; simp; linarith
      exact h_in_box p1 h1 h2 h3
    have hp2 : p2 ∈ axisBox a b c := by
      have h1 : |p2 0| ≤ a / 2 := by
        have h11 : p2 0 = -a / 2 := by simp [p2, e0, EuclideanSpace.single_apply]
        rw [h11]
        rw [abs_le]
        constructor <;> linarith
      have h2 : |p2 1| ≤ b / 2 := by
        have h21 : p2 1 = 0 := by simp [p2, e0, EuclideanSpace.single_apply]
        rw [h21]; simp; linarith
      have h3 : |p2 2| ≤ c / 2 := by
        have h31 : p2 2 = 0 := by simp [p2, e0, EuclideanSpace.single_apply]
        rw [h31]; simp; linarith
      exact h_in_box p2 h1 h2 h3
    have hdist : dist p1 p2 = a := by
      have h : dist p1 p2 = ‖p1 - p2‖ := by rw [dist_eq_norm]
      rw [h]
      have h5 : p1 - p2 = a • e0 := by
        ext i; fin_cases i <;> simp [p1, p2, e0, EuclideanSpace.single_apply] <;> ring
      rw [h5]
      have h6 : ‖a • e0‖ = |a| * ‖e0‖ := by exact norm_smul a e0
      rw [h6]
      have h7 : ‖e0‖ = 1 := by simp [e0, EuclideanSpace.single_apply]
      rw [h7]; simp [abs_of_pos ha]
    exact h_main a ha ⟨p1, p2, hp1, hp2, hdist⟩
  have hb2 : b ≤ 20 := by
    let p1 := (b / 2) • e1
    let p2 := (-b / 2) • e1
    have hp1 : p1 ∈ axisBox a b c := by
      have h1 : |p1 0| ≤ a / 2 := by
        have h11 : p1 0 = 0 := by simp [p1, e1, EuclideanSpace.single_apply]
        rw [h11]; simp; linarith
      have h2 : |p1 1| ≤ b / 2 := by
        have h21 : p1 1 = b / 2 := by simp [p1, e1, EuclideanSpace.single_apply]
        rw [h21]; rw [abs_of_nonneg (by linarith)]
      have h3 : |p1 2| ≤ c / 2 := by
        have h31 : p1 2 = 0 := by simp [p1, e1, EuclideanSpace.single_apply]
        rw [h31]; simp; linarith
      exact h_in_box p1 h1 h2 h3
    have hp2 : p2 ∈ axisBox a b c := by
      have h1 : |p2 0| ≤ a / 2 := by
        have h11 : p2 0 = 0 := by simp [p2, e1, EuclideanSpace.single_apply]
        rw [h11]; simp; linarith
      have h2 : |p2 1| ≤ b / 2 := by
        have h21 : p2 1 = -b / 2 := by simp [p2, e1, EuclideanSpace.single_apply]
        rw [h21]
        rw [abs_le]
        constructor <;> linarith
      have h3 : |p2 2| ≤ c / 2 := by
        have h31 : p2 2 = 0 := by simp [p2, e1, EuclideanSpace.single_apply]
        rw [h31]; simp; linarith
      exact h_in_box p2 h1 h2 h3
    have hdist : dist p1 p2 = b := by
      have h : dist p1 p2 = ‖p1 - p2‖ := by rw [dist_eq_norm]
      rw [h]
      have h5 : p1 - p2 = b • e1 := by
        ext i; fin_cases i <;> simp [p1, p2, e1, EuclideanSpace.single_apply] <;> ring
      rw [h5]
      have h6 : ‖b • e1‖ = |b| * ‖e1‖ := by exact norm_smul b e1
      rw [h6]
      have h7 : ‖e1‖ = 1 := by simp [e1, EuclideanSpace.single_apply]
      rw [h7]; simp [abs_of_pos hb]
    exact h_main b hb ⟨p1, p2, hp1, hp2, hdist⟩
  have hc2 : c ≤ 20 := by
    let p1 := (c / 2) • e2
    let p2 := (-c / 2) • e2
    have hp1 : p1 ∈ axisBox a b c := by
      have h1 : |p1 0| ≤ a / 2 := by
        have h11 : p1 0 = 0 := by simp [p1, e2, EuclideanSpace.single_apply]
        rw [h11]; simp; linarith
      have h2 : |p1 1| ≤ b / 2 := by
        have h21 : p1 1 = 0 := by simp [p1, e2, EuclideanSpace.single_apply]
        rw [h21]; simp; linarith
      have h3 : |p1 2| ≤ c / 2 := by
        have h31 : p1 2 = c / 2 := by simp [p1, e2, EuclideanSpace.single_apply]
        rw [h31]; rw [abs_of_nonneg (by linarith)]
      exact h_in_box p1 h1 h2 h3
    have hp2 : p2 ∈ axisBox a b c := by
      have h1 : |p2 0| ≤ a / 2 := by
        have h11 : p2 0 = 0 := by simp [p2, e2, EuclideanSpace.single_apply]
        rw [h11]; simp; linarith
      have h2 : |p2 1| ≤ b / 2 := by
        have h21 : p2 1 = 0 := by simp [p2, e2, EuclideanSpace.single_apply]
        rw [h21]; simp; linarith
      have h3 : |p2 2| ≤ c / 2 := by
        have h31 : p2 2 = -c / 2 := by simp [p2, e2, EuclideanSpace.single_apply]
        rw [h31]
        rw [abs_le]
        constructor <;> linarith
      exact h_in_box p2 h1 h2 h3
    have hdist : dist p1 p2 = c := by
      have h : dist p1 p2 = ‖p1 - p2‖ := by rw [dist_eq_norm]
      rw [h]
      have h5 : p1 - p2 = c • e2 := by
        ext i; fin_cases i <;> simp [p1, p2, e2, EuclideanSpace.single_apply] <;> ring
      rw [h5]
      have h6 : ‖c • e2‖ = |c| * ‖e2‖ := by exact norm_smul c e2
      rw [h6]
      have h7 : ‖e2‖ = 1 := by simp [e2, EuclideanSpace.single_apply]
      rw [h7]; simp [abs_of_pos hc]
    exact h_main c hc ⟨p1, p2, hp1, hp2, hdist⟩
  exact ⟨ha2, hb2, hc2⟩

/-- Helper: bound the norm of each coordinate of a Point3 by its total norm. -/
lemma point3_coord_bound (v : Point3) (i : Fin 3) : |v i| ≤ ‖v‖ := by
  have h2 : ‖v‖^2 = ∑ j : Fin 3, (v j)^2 := norm_sq_point3 v
  have h1 : (v i)^2 ≤ ‖v‖^2 := by
    rw [h2]
    exact Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have h_abs : |v i|^2 ≤ ‖v‖^2 := by
    have h : |v i|^2 = (v i)^2 := by rw [sq_abs]
    rw [h]; exact h1
  have h_norm_nonneg : 0 ≤ ‖v‖ := by positivity
  have h_abs_nonneg : 0 ≤ |v i| := by positivity
  exact (sq_le_sq₀ h_abs_nonneg h_norm_nonneg).mp h_abs

/-- Helper: bound norm of any point in the enlarged John outer box. -/
lemma outer_box_norm_bound (a b c_dim A_john : ℝ)
    (hA_john_one : 1 ≤ A_john)
    (h_dims_bounded : a ≤ 20 ∧ b ≤ 20 ∧ c_dim ≤ 20)
    (z : Point3) (hz : z ∈ axisBox (A_john * a) (A_john * b) (A_john * c_dim)) :
    ‖z‖ ≤ 10 * Real.sqrt 3 * A_john := by
  have h0 : |z 0| ≤ A_john * a / 2 := hz.1
  have h1 : |z 1| ≤ A_john * b / 2 := hz.2.1
  have h2 : |z 2| ≤ A_john * c_dim / 2 := hz.2.2
  have ha20 : a ≤ 20 := h_dims_bounded.1
  have hb20 : b ≤ 20 := h_dims_bounded.2.1
  have hc20 : c_dim ≤ 20 := h_dims_bounded.2.2
  have hA_nonneg : 0 ≤ A_john := by linarith [hA_john_one]
  have h_bnd : ∀ (i : Fin 3), |z i| ≤ A_john * 10 := by
    intro i
    fin_cases i
    · have h : A_john * a / 2 ≤ A_john * 10 := by
        have h2 : a / 2 ≤ 10 := by linarith [ha20]
        have h3 : A_john * a / 2 = A_john * (a / 2) := by ring
        rw [h3]; exact mul_le_mul_of_nonneg_left h2 hA_nonneg
      exact le_trans h0 h
    · have h : A_john * b / 2 ≤ A_john * 10 := by
        have h2 : b / 2 ≤ 10 := by linarith [hb20]
        have h3 : A_john * b / 2 = A_john * (b / 2) := by ring
        rw [h3]; exact mul_le_mul_of_nonneg_left h2 hA_nonneg
      exact le_trans h1 h
    · have h : A_john * c_dim / 2 ≤ A_john * 10 := by
        have h2 : c_dim / 2 ≤ 10 := by linarith [hc20]
        have h3 : A_john * c_dim / 2 = A_john * (c_dim / 2) := by ring
        rw [h3]; exact mul_le_mul_of_nonneg_left h2 hA_nonneg
      exact le_trans hz.2.2 h
  have h5 : ‖z‖^2 = ∑ i : Fin 3, (z i)^2 := norm_sq_point3 z
  have h4 : ‖z‖^2 ≤ 3 * (A_john * 10)^2 := by
    rw [h5]
    have h7 : ∀ i : Fin 3, (z i)^2 ≤ (A_john * 10)^2 := by
      intro i
      have h8 : |z i| ≤ A_john * 10 := h_bnd i
      have h9 : (z i)^2 = |z i|^2 := by rw [sq_abs]
      rw [h9]; gcongr
    have h10 : ∑ i : Fin 3, (z i)^2 ≤ ∑ i : Fin 3, (A_john * 10)^2 :=
      Finset.sum_le_sum (fun i _ => h7 i)
    simpa using h10
  have h_sq : (10 * Real.sqrt 3 * A_john)^2 = 3 * (A_john * 10)^2 := by
    calc (10 * Real.sqrt 3 * A_john)^2
      = 10^2 * (Real.sqrt 3)^2 * A_john^2 := by ring
    _ = 100 * 3 * A_john^2 := by rw [Real.sq_sqrt (by norm_num)] <;> ring
    _ = 3 * (A_john * 10)^2 := by ring
  have h11 : ‖z‖^2 ≤ (10 * Real.sqrt 3 * A_john)^2 := by rw [h_sq]; exact h4
  have h_norm_nonneg2 : 0 ≤ ‖z‖ := by positivity
  have h_pos2 : 0 ≤ 10 * Real.sqrt 3 * A_john := by positivity
  exact (sq_le_sq₀ h_norm_nonneg2 h_pos2).mp h11

/-- Dimension ratio bounds: a' ≤ 14*A*a, b' ≤ 14*A*b, c' ≤ 14*A*c. -/
lemma dimension_ratio_bounds (δ a b c_dim A_john a' b' c' margin : ℝ)
    (hδ : 0 < δ) (hA_a_lower : A_john * a ≥ 2 * δ)
    (hab : a ≤ b) (hbc : b ≤ c_dim)
    (hA_pos : 0 < A_john)
    (ha'_le : a' ≤ 2 * (A_john * a + 2 * margin))
    (hb'_le : b' ≤ 2 * (A_john * b + 2 * margin))
    (hc'_le : c' ≤ 2 * (A_john * c_dim + 2 * margin))
    (hmargin : margin = 6 * δ) :
    a' ≤ 14 * A_john * a ∧ b' ≤ 14 * A_john * b ∧ c' ≤ 14 * A_john * c_dim := by
  have h12 : 12 * δ ≤ 6 * A_john * a := by
    have h2 : A_john * a ≥ 2 * δ := hA_a_lower
    linarith
  have hA_b : A_john * b ≥ A_john * a := mul_le_mul_of_nonneg_left hab (by linarith)
  have hA_c : A_john * c_dim ≥ A_john * a :=
    mul_le_mul_of_nonneg_left (le_trans hab hbc) (by linarith)
  have h12b : 12 * δ ≤ 6 * A_john * b := by linarith
  have h12c : 12 * δ ≤ 6 * A_john * c_dim := by linarith
  have ha : a' ≤ 14 * A_john * a := by
    calc a' ≤ 2 * (A_john * a + 2 * margin) := ha'_le
      _ = 2 * (A_john * a + 12 * δ) := by rw [hmargin] <;> ring
      _ ≤ 14 * A_john * a := by linarith
  have hb : b' ≤ 14 * A_john * b := by
    calc b' ≤ 2 * (A_john * b + 2 * margin) := hb'_le
      _ = 2 * (A_john * b + 12 * δ) := by rw [hmargin] <;> ring
      _ ≤ 14 * A_john * b := by linarith
  have hc : c' ≤ 14 * A_john * c_dim := by
    calc c' ≤ 2 * (A_john * c_dim + 2 * margin) := hc'_le
      _ = 2 * (A_john * c_dim + 12 * δ) := by rw [hmargin] <;> ring
      _ ≤ 14 * A_john * c_dim := by linarith
  exact ⟨ha, hb, hc⟩

/-- Pure real-number volume bound: |det M| * a' * b' * c' ≤ 10^7 * (a * b * c). -/
lemma rounding_real_volume_bound (M : Matrix (Fin 3) (Fin 3) ℝ)
    (a b c_dim a' b' c' A_john : ℝ)
    (hA_john_le : A_john ≤ 10)
    (hA_john_one : 1 ≤ A_john)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c_dim)
    (ha'_pos : 0 < a') (hb'_pos : 0 < b') (hc'_pos : 0 < c')
    (hdet_bounds : 1 / 2 ≤ |M.det| ∧ |M.det| ≤ 2)
    (ha_ratio : a' ≤ 14 * A_john * a)
    (hb_ratio : b' ≤ 14 * A_john * b)
    (hc_ratio : c' ≤ 14 * A_john * c_dim) :
    |M.det| * a' * b' * c' ≤ (10^7 : ℝ) * (a * b * c_dim) := by
  have h4 : |M.det| ≤ 2 := hdet_bounds.2
  have h5_pos1 : 0 ≤ a' := by positivity
  have h5_pos2 : 0 ≤ b' := by positivity
  have h5_ab : a' * b' ≤ (14 * A_john * a) * (14 * A_john * b) :=
    mul_le_mul ha_ratio hb_ratio (by positivity) (by positivity)
  have h5 : a' * b' * c' ≤ (14 * A_john)^3 * (a * b * c_dim) := by
    have h : a' * b' * c' ≤ (14 * A_john * a) * (14 * A_john * b) * (14 * A_john * c_dim) :=
      mul_le_mul h5_ab hc_ratio (by positivity) (by positivity)
    have h_eq : (14 * A_john * a) * (14 * A_john * b) * (14 * A_john * c_dim) =
        (14 * A_john)^3 * (a * b * c_dim) := by ring
    rw [h_eq] at h
    exact h
  have h6 : (14 * A_john)^3 ≤ (14 * 10)^3 := by
    have h61 : 14 * A_john ≤ 14 * 10 := by linarith [hA_john_le]
    have h62 : 0 ≤ 14 * A_john := by linarith
    have h63 : (14 * A_john)^3 ≤ (14 * 10)^3 := by
      gcongr <;> linarith [hA_john_le]
    exact h63
  have h7 : 2 * (14 * 10)^3 ≤ (10^7 : ℝ) := by norm_num
  have h8 : 0 ≤ a * b * c_dim := by positivity
  have h9 : 0 ≤ a' * b' * c' := by positivity
  have h10 : |M.det| * a' * b' * c' ≤ 2 * (a' * b' * c') := by
    have h10' : |M.det| * (a' * b' * c') ≤ 2 * (a' * b' * c') :=
      mul_le_mul_of_nonneg_right h4 h9
    have h_assoc : |M.det| * a' * b' * c' = |M.det| * (a' * b' * c') := by ring
    rw [h_assoc]
    exact h10'
  have h11 : 2 * (a' * b' * c') ≤ 2 * ((14 * A_john)^3 * (a * b * c_dim)) :=
    mul_le_mul_of_nonneg_left h5 (by norm_num)
  have h12 : 2 * ((14 * A_john)^3 * (a * b * c_dim)) ≤ 2 * ((14 * 10)^3 * (a * b * c_dim)) := by
    have h13 : (14 * A_john)^3 * (a * b * c_dim) ≤ (14 * 10)^3 * (a * b * c_dim) :=
      mul_le_mul_of_nonneg_right h6 h8
    exact mul_le_mul_of_nonneg_left h13 (by norm_num)
  have h14 : 2 * ((14 * 10)^3 * (a * b * c_dim)) = (2 * (14 * 10)^3) * (a * b * c_dim) := by ring
  have h15 : (2 * (14 * 10)^3) * (a * b * c_dim) ≤ (10^7 : ℝ) * (a * b * c_dim) :=
    mul_le_mul_of_nonneg_right h7 h8
  exact le_trans (le_trans (le_trans (le_trans h10 h11) h12) (le_of_eq h14)) h15

/-- Compactness of an axis-aligned box with positive dimensions. -/
lemma isCompact_axisBox (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    IsCompact (axisBox a b c) := by
  have hc0 : Continuous (fun x : Point3 => x 0) := by fun_prop
  have hc1 : Continuous (fun x : Point3 => x 1) := by fun_prop
  have hc2 : Continuous (fun x : Point3 => x 2) := by fun_prop
  have h_closed : IsClosed (axisBox a b c) := by
    have h : axisBox a b c = {x : Point3 | |x 0| ≤ a/2} ∩ {x : Point3 | |x 1| ≤ b/2} ∩ {x : Point3 | |x 2| ≤ c/2} := by
      ext x; simp [axisBox] <;> tauto
    rw [h]
    apply IsClosed.inter
    · apply IsClosed.inter
      · exact isClosed_le (continuous_abs.comp hc0) continuous_const
      · exact isClosed_le (continuous_abs.comp hc1) continuous_const
    · exact isClosed_le (continuous_abs.comp hc2) continuous_const
  let R := Real.sqrt ((a/2)^2 + (b/2)^2 + (c/2)^2)
  have hR_nonneg : 0 ≤ R := by positivity
  have hR2 : R ^ 2 = (a/2)^2 + (b/2)^2 + (c/2)^2 := by
    rw [Real.sq_sqrt (by positivity)]
  have h_bounded : Bornology.IsBounded (axisBox a b c) := by
    have h_sub : axisBox a b c ⊆ Metric.closedBall (0 : Point3) R := by
      intro x hx
      have h4 : ‖x‖ ^ 2 = (x 0)^2 + (x 1)^2 + (x 2)^2 := by
        have h41 : ‖x‖ ^ 2 = ∑ i : Fin 3, (x i)^2 := norm_sq_point3 x
        rw [h41]
        have h42 : ∑ i : Fin 3, (x i)^2 = (x 0)^2 + (x 1)^2 + (x 2)^2 := by
          simp [Fin.sum_univ_succ] <;> ring
        exact h42
      have h6 : (x 0)^2 ≤ (a/2)^2 := by
        have h61 : |x 0| ≤ a/2 := hx.1
        have h : (x 0)^2 = |x 0|^2 := by rw [sq_abs] <;> rfl
        rw [h]
        exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr h61
      have h7 : (x 1)^2 ≤ (b/2)^2 := by
        have h71 : |x 1| ≤ b/2 := hx.2.1
        have h : (x 1)^2 = |x 1|^2 := by rw [sq_abs] <;> rfl
        rw [h]
        exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr h71
      have h8 : (x 2)^2 ≤ (c/2)^2 := by
        have h81 : |x 2| ≤ c/2 := hx.2.2
        have h : (x 2)^2 = |x 2|^2 := by rw [sq_abs] <;> rfl
        rw [h]
        exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr h81
      have h9 : ‖x‖ ^ 2 ≤ R ^ 2 := by
        rw [h4, hR2]
        linarith
      have h10 : 0 ≤ ‖x‖ := by positivity
      have h11 : ‖x‖ ≤ R := (sq_le_sq₀ h10 hR_nonneg).mp h9
      simpa [Metric.mem_closedBall] using h11
    exact Metric.isBounded_closedBall.subset h_sub
  exact Metric.isCompact_of_isClosed_isBounded h_closed h_bounded

/-- Pure real-number margin calculation: 2*(op*z+center) ≤ 6δ. -/
lemma rounding_margin_calc (δ A_john : ℝ) (hδ : 0 < δ)
    (hA_john_le : A_john ≤ 10) (hA_john_one : 1 ≤ A_john)
    (h_op_norm h_z_norm h_center_err : ℝ)
    (h_op_nonneg : 0 ≤ h_op_norm) (h_z_nonneg : 0 ≤ h_z_norm)
    (h1 : h_op_norm ≤ 3 * (δ / 200))
    (h2 : h_z_norm ≤ 10 * Real.sqrt 3 * A_john)
    (h3 : h_center_err ≤ Real.sqrt 3 / 2 * (δ / 10)) :
    2 * (h_op_norm * h_z_norm + h_center_err) ≤ 6 * δ := by
  have hA_nonneg : 0 ≤ A_john := by linarith
  have hδ_nonneg : 0 ≤ δ := by linarith
  have h4 : h_op_norm * h_z_norm ≤ (3 * (δ / 200)) * (10 * Real.sqrt 3 * A_john) := by
    exact mul_le_mul h1 h2 h_z_nonneg (by positivity)
  have h5 : h_op_norm * h_z_norm + h_center_err ≤
      (3 * (δ / 200)) * (10 * Real.sqrt 3 * A_john) + Real.sqrt 3 / 2 * (δ / 10) := by
    exact add_le_add h4 h3
  have h6 : Real.sqrt 3 * (3 * A_john + 1) ≤ 60 := by
    have hsqrt3 : Real.sqrt 3 ≤ 60 / 31 := by
      rw [Real.sqrt_le_left (by norm_num)] <;> norm_num
    have h7 : 3 * A_john + 1 ≤ 31 := by linarith
    calc Real.sqrt 3 * (3 * A_john + 1)
      ≤ (60 / 31 : ℝ) * (3 * A_john + 1) := by gcongr <;> linarith [Real.sqrt_nonneg 3]
    _ ≤ (60 / 31 : ℝ) * 31 := by gcongr
    _ = 60 := by norm_num
  have h7 : 2 * ((3 * (δ / 200)) * (10 * Real.sqrt 3 * A_john) + Real.sqrt 3 / 2 * (δ / 10)) =
      δ * (Real.sqrt 3 * (3 * A_john + 1) / 10) := by ring
  have h8 : 2 * (h_op_norm * h_z_norm + h_center_err) ≤
      2 * ((3 * (δ / 200)) * (10 * Real.sqrt 3 * A_john) + Real.sqrt 3 / 2 * (δ / 10)) := by
    exact mul_le_mul_of_nonneg_left h5 (by norm_num)
  rw [h7] at h8
  have h9 : δ * (Real.sqrt 3 * (3 * A_john + 1) / 10) ≤ δ * (60 / 10) := by
    gcongr <;> linarith
  have h10 : δ * (60 / 10) = 6 * δ := by ring
  rw [h10] at h9
  exact le_trans h8 h9

/-- Dimension ratio helper: x' ≤ 14 * A_john * x. -/
lemma rounding_dim_ratio (δ A_john x : ℝ) (hA_john_one : 1 ≤ A_john)
    (h_lower : A_john * x ≥ 2 * δ) (x' : ℝ)
    (hx'_le : x' ≤ 2 * (A_john * x + 12 * δ)) :
    x' ≤ 14 * A_john * x := by
  have h1 : 12 * δ ≤ 6 * A_john * x := by linarith
  have h2 : 2 * (A_john * x + 12 * δ) ≤ 14 * A_john * x := by linarith
  exact le_trans hx'_le h2

/-- Volume upper bound for a test parallelepiped. -/
lemma test_parallelepiped_volume_bound (center : Point3)
    (M : Matrix (Fin 3) (Fin 3) ℝ)
    (a' b' c' : ℝ) (ha'_pos : 0 < a') (hb'_pos : 0 < b') (hc'_pos : 0 < c')
    (hdet_ne_zero : M.det ≠ 0) :
    volume (testParallelepiped center M a' b' c') ≤
    ENNReal.ofReal (|M.det| * a' * b' * c') := by
  let f : Point3 →ₗ[ℝ] Point3 := matrixToLin M
  let f_clm : Point3 →L[ℝ] Point3 := LinearMap.toContinuousLinearMap f
  have h_det_eq : LinearMap.det f = M.det := by
    let e : Point3 ≃ₗ[ℝ] (Fin 3 → ℝ) := EuclideanSpace.equiv (Fin 3) ℝ
    have h2 : LinearMap.det (matrixToLin M) = LinearMap.det (Matrix.toLin' M) := by
      exact LinearMap.det_conj (Matrix.toLin' M) e.symm
    have h3 : f = matrixToLin M := by rfl
    rw [h3, h2, LinearMap.det_toLin' M]
  have h_f_det_ne_zero : LinearMap.det f ≠ 0 := by
    rw [h_det_eq]; exact hdet_ne_zero
  have h_box_compact : IsCompact (axisBox a' b' c') := isCompact_axisBox a' b' c' ha'_pos hb'_pos hc'_pos
  have h_S_compact : IsCompact (f '' axisBox a' b' c') := h_box_compact.image f_clm.continuous
  have h_S_meas : MeasurableSet (f '' axisBox a' b' c') := h_S_compact.measurableSet
  have h_vol_image : volume (f '' axisBox a' b' c') =
      ENNReal.ofReal |M.det| * volume (axisBox a' b' c') := by
    have h_main := volume_linear_image f_clm h_f_det_ne_zero (axisBox a' b' c')
    simpa [h_det_eq] using h_main
  let S : Set Point3 := f '' axisBox a' b' c'
  let g_inv : Point3 → Point3 := fun x => -center + x
  have hmp_inv : MeasurePreserving g_inv := MeasureTheory.measurePreserving_add_left volume (-center)
  have h_eq : g_inv ⁻¹' S = (center +ᵥ S) := by
    ext x
    have h1 : x ∈ g_inv ⁻¹' S ↔ -center + x ∈ S := by
      simp [g_inv, Set.mem_preimage] <;> rfl
    have h2 : x ∈ center +ᵥ S ↔ ∃ y ∈ S, center + y = x := by
      simp [Set.mem_vadd_set] <;> rfl
    rw [h1, h2]
    constructor
    · intro h
      exact ⟨-center + x, h, by abel⟩
    · rintro ⟨y, hy, h_eq2⟩
      have h3 : -center + x = y := by
        have h4 : x = center + y := h_eq2.symm
        rw [h4]; simp [add_assoc] <;> abel
      rw [h3]; exact hy
  have h_vol_trans : volume (center +ᵥ S) = volume S := by
    have h : volume (g_inv ⁻¹' S) = volume S := hmp_inv.measure_preimage h_S_meas.nullMeasurableSet
    rw [h_eq] at h
    exact h
  have h_vol_box : volume (axisBox a' b' c') = ENNReal.ofReal (a' * b' * c') :=
    volume_axisBox a' b' c' ha'_pos hb'_pos hc'_pos
  have h_vol_parallel : volume (center +ᵥ S) = ENNReal.ofReal (|M.det| * a' * b' * c') := by
    rw [h_vol_trans, h_vol_image, h_vol_box]
    have h_pos_det : 0 ≤ |M.det| := abs_nonneg _
    have h_mul : ENNReal.ofReal (|M.det| * (a' * b' * c')) =
        ENNReal.ofReal |M.det| * ENNReal.ofReal (a' * b' * c') :=
      ENNReal.ofReal_mul h_pos_det
    simpa [mul_assoc] using h_mul.symm
  have h_sub : testParallelepiped center M a' b' c' ⊆ (center +ᵥ S) := by
    intro x hx
    simp only [testParallelepiped] at hx
    exact hx.1
  calc volume (testParallelepiped center M a' b' c')
    ≤ volume (center +ᵥ S) := measure_mono h_sub
  _ = ENNReal.ofReal (|M.det| * a' * b' * c') := h_vol_parallel

/--
Given a convex body H with framed dimensions, find a test parallelepiped
from the grids containing H with volume ≤ L · volume(H).
Requires H contains a δ-ball (e.g. because it contains a δ-tube).
-/
lemma rounding_lemma {δ : ℝ} (hδ : 0 < δ) (hδ_le_one : δ ≤ 1)
    (H : Set Point3)
    (hH_convex : Convex ℝ H)
    (hH_compact : IsCompact H)
    (hH_interior : (interior H).Nonempty)
    (hH_sub_ball : H ⊆ closedBall (0 : Point3) 10)
    (a b c_dim A_john : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c_dim)
    (hab : a ≤ b) (hbc : b ≤ c_dim)
    (hA_john_one : 1 ≤ A_john)
    (hA_john_le : A_john ≤ 10)
    (frame : Point3 ≃ᵃⁱ[ℝ] Point3)
    (h_inner : frame '' axisBox a b c_dim ⊆ H)
    (h_outer : H ⊆ frame '' axisBox (A_john * a) (A_john * b) (A_john * c_dim))
    (h_ball : ∃ (p : Point3), Metric.ball p δ ⊆ H)
    (L : ENNReal) (hL_ne_top : L ≠ ⊤) (hL_big : (10^7 : ENNReal) ≤ L) :
    ∃ (center : Point3) (hc : center ∈ centerGrid δ hδ)
      (M : Matrix (Fin 3) (Fin 3) ℝ)
      (hM : M ∈ frameMatrices (δ / 100) (by positivity))
      (a' b' c' : ℝ)
      (h_dims : (a', (b', c')) ∈ dimTriples δ hδ),
      H ⊆ testParallelepiped center M a' b' c' ∧
      volume (testParallelepiped center M a' b' c') ≤ L * volume H := by
  have hA_pos : 0 < A_john := by linarith
  let t : Point3 := frame 0
  let R_lin : Point3 ≃ₗᵢ[ℝ] Point3 := frame.linearIsometryEquiv
  let R_mat : Matrix (Fin 3) (Fin 3) ℝ := fun i j => R_lin (EuclideanSpace.single j (1 : ℝ)) i
  have hR_orth : R_mat.transpose * R_mat = 1 := (isometry_matrix_orthogonal R_lin).1
  have hR_eq : (matrixToLin R_mat : Point3 →ₗ[ℝ] Point3) = (R_lin : Point3 →ₗ[ℝ] Point3) :=
    (isometry_matrix_orthogonal R_lin).2
  have h_frame_eq : ∀ (x : Point3), frame x = R_lin x + t := by
    intro x; have h := frame.map_vadd (0 : Point3) x; simpa [t] using h

  -- Ball in outer box gives A_john * a ≥ 2δ
  rcases h_ball with ⟨p, hp_ball⟩
  let q : Point3 := frame.symm p
  have hq : frame q = p := frame.apply_symm_apply p
  have h_ball_box : Metric.ball q δ ⊆ axisBox (A_john * a) (A_john * b) (A_john * c_dim) := by
    intro x hx
    have h_dist : dist (frame x) p < δ := by
      have h_eq1 : dist (frame x) p = dist (frame x) (frame q) := by rw [hq]
      rw [h_eq1]
      have h_eq2 : dist (frame x) (frame q) = dist x q :=
        frame.dist_map x q
      rw [h_eq2]; exact hx
    have h_frame_x_in_H : frame x ∈ H := hp_ball (by simpa [Metric.mem_ball] using h_dist)
    have h_frame_x_in_image : frame x ∈ frame '' axisBox (A_john * a) (A_john * b) (A_john * c_dim) :=
      h_outer h_frame_x_in_H
    rcases h_frame_x_in_image with ⟨z, hz, h_eq⟩
    have h_z_eq_x : z = x := frame.injective h_eq
    rw [h_z_eq_x] at hz
    exact hz
  have hA_a_lower : A_john * a ≥ 2 * δ :=
    ball_in_axisBox_dim_bound hδ (by positivity) q h_ball_box

  -- Diameter bound
  have h_diam_H : ∀ (x y : Point3), x ∈ H → y ∈ H → dist x y ≤ 20 := by
    intro x y hx hy
    have hx1 : dist x 0 ≤ 10 := by simpa [Metric.mem_closedBall] using hH_sub_ball hx
    have hy1 : dist y 0 ≤ 10 := by simpa [Metric.mem_closedBall] using hH_sub_ball hy
    calc dist x y ≤ dist x 0 + dist 0 y := dist_triangle x 0 y
      _ = dist x 0 + dist y 0 := by rw [dist_comm 0 y]
      _ ≤ 20 := by linarith
  let S := frame.symm '' H
  have h_diam_S : ∀ (x y : Point3), x ∈ S → y ∈ S → dist x y ≤ 20 := by
    intro x y hx hy
    rcases hx with ⟨x', hx', rfl⟩; rcases hy with ⟨y', hy', rfl⟩
    have h : dist (frame.symm x') (frame.symm y') = dist x' y' :=
      frame.symm.dist_map x' y'
    rw [h]; exact h_diam_H x' y' hx' hy'
  have h_box_sub_S : axisBox a b c_dim ⊆ S := by
    intro z hz; exact ⟨frame z, h_inner ⟨z, hz, rfl⟩, by simp⟩
  have h_dims_bounded : a ≤ 20 ∧ b ≤ 20 ∧ c_dim ≤ 20 :=
    box_dim_bound a b c_dim ha hb hc S h_box_sub_S h_diam_S

  -- Round center
  have ht_in : ‖t‖ ≤ 10 := by
    have h0 : (0 : Point3) ∈ axisBox a b c_dim := by
      simp only [axisBox, Set.mem_setOf_eq]
      exact ⟨by simp [ha.le]; linarith, by simp [hb.le]; linarith, by simp [hc.le]; linarith⟩
    have h_t_in_H : t ∈ H := h_inner ⟨0, h0, rfl⟩
    simpa [Metric.mem_closedBall] using hH_sub_ball h_t_in_H
  have ht_in20 : ‖t‖ ≤ 20 := by linarith [ht_in]
  rcases centerGrid_cover δ hδ t ht_in20 with ⟨center, hc_grid, h_center_err⟩

  -- Round matrix
  have hε_small : δ / 100 ≤ 1 / 40 := by linarith [hδ_le_one]
  rcases orthogonal_matrix_cover (show 0 < δ / 100 from by positivity) hε_small R_mat hR_orth
    with ⟨M, hM, hM_dist⟩

  -- Linear maps
  let f : Point3 →ₗ[ℝ] Point3 := matrixToLin M
  let f_clm := f.toContinuousLinearMap
  let f_inv : Point3 →ₗ[ℝ] Point3 := matrixToLin (M⁻¹)
  let f_inv_clm := f_inv.toContinuousLinearMap
  let R_clm := R_lin.toContinuousLinearMap
  have h_near : isNearOrthogonal M := (Finset.mem_filter.mp hM).2
  have hdet_bounds : 1 / 2 ≤ |Matrix.det M| ∧ |Matrix.det M| ≤ 2 :=
    near_orthogonal_det_bound M h_near
  have hdet_ne_zero : Matrix.det M ≠ 0 := by
    have h : 0 < |Matrix.det M| := by linarith [hdet_bounds.1]
    exact abs_ne_zero.mp (ne_of_gt h)
  have hf_inv_id : ∀ (x : Point3), f_inv (f x) = x := by
    intro x
    have h1 : f_inv (f x) = (matrixToLin (M⁻¹ * M)) x := by
      rw [matrixToLin_mul] <;> rfl
    rw [h1]
    have h2 : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M (IsUnit.mk0 (Matrix.det M) hdet_ne_zero)
    rw [h2, matrixToLin_one] <;> rfl
  have hf_inv_id2 : ∀ (x : Point3), f (f_inv x) = x := by
    intro x
    have h1 : f (f_inv x) = (matrixToLin (M * M⁻¹)) x := by
      rw [matrixToLin_mul] <;> rfl
    rw [h1]
    have h2 : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M (IsUnit.mk0 (Matrix.det M) hdet_ne_zero)
    rw [h2, matrixToLin_one] <;> rfl
  have h_diff : (R_clm - f_clm : Point3 →L[ℝ] Point3) =
      (matrixToLin (R_mat - M)).toContinuousLinearMap := by
    have h : ∀ (x : Point3), (R_clm - f_clm) x =
        (matrixToLin (R_mat - M)).toContinuousLinearMap x := by
      intro x
      have h_eq1 : (R_clm - f_clm) x = R_lin x - f x := by rfl
      rw [h_eq1]
      have h_eq2 : R_lin x = matrixToLin R_mat x := by
        exact congr_arg (fun (lm : Point3 →ₗ[ℝ] Point3) => lm x) hR_eq.symm
      rw [h_eq2]
      have h_eq3 : matrixToLin R_mat x - matrixToLin M x = matrixToLin (R_mat - M) x := by
        rw [matrixToLin_sub] <;> rfl
      simpa [f] using h_eq3
    exact DFunLike.ext _ _ h
  have h_op_norm : ‖R_clm - f_clm‖ ≤ 3 * (δ / 200) := by
    rw [h_diff]
    exact operator_norm_entrywise_bound (R_mat - M) (δ / 200) (by positivity)
      (fun i j => by
        have h_eq : (R_mat - M) i j = R_mat i j - M i j := by rfl
        rw [h_eq]
        have h_bound : |R_mat i j - M i j| ≤ (δ / 100) / 2 := hM_dist i j
        have h_final : (δ / 100) / 2 = δ / 200 := by ring
        rw [h_final] at h_bound
        exact h_bound)
  have h_inv_norm : ‖f_inv_clm‖ ≤ 2 := near_orthogonal_inverse_norm M h_near

  -- Margin
  let margin : ℝ := 6 * δ
  have h_coord : ∀ (v : Point3) (i : Fin 3), |v i| ≤ ‖v‖ := fun v i => point3_coord_bound v i

  -- Bound ‖z‖ for z in outer box: use a,b,c_dim ≤ 20
  have h_R_box : ∀ z ∈ axisBox (A_john * a) (A_john * b) (A_john * c_dim),
      ‖z‖ ≤ 10 * Real.sqrt 3 * A_john :=
    fun z hz => outer_box_norm_bound a b c_dim A_john hA_john_one h_dims_bounded z hz

  have h_center_bound : ‖t - center‖ ≤ Real.sqrt 3 / 2 * (δ / 10) := h_center_err

  have h_margin_bound : ∀ z ∈ axisBox (A_john * a) (A_john * b) (A_john * c_dim),
      ‖f_inv (R_lin z + (t - center)) - z‖ ≤ margin := by
    intro z hz
    set v : Point3 := (R_clm - f_clm) z + (t - center) with hv_def
    have h1 : f_inv (R_lin z + (t - center)) - z = f_inv v := by
      have h2 : R_lin z + (t - center) = f z + v := by
        rw [hv_def]
        have h21 : (R_clm - f_clm) z = R_clm z - f_clm z := by
          exact ContinuousLinearMap.sub_apply R_clm f_clm z
        have h22 : R_clm z = R_lin z := by rfl
        have h23 : f_clm z = f z := by rfl
        rw [h21, h22, h23] <;> abel
      have h_add : f_inv (R_lin z + (t - center)) = f_inv (f z) + f_inv v := by
        rw [h2]; exact f_inv.map_add (f z) v
      have h_id : f_inv (f z) = z := hf_inv_id z
      rw [h_add, h_id] <;> abel
    rw [h1]
    have h_z_norm : ‖z‖ ≤ 10 * Real.sqrt 3 * A_john := h_R_box z hz
    have h_v_norm : ‖v‖ ≤ ‖R_clm - f_clm‖ * ‖z‖ + ‖t - center‖ := by
      calc ‖v‖ ≤ ‖(R_clm - f_clm) z‖ + ‖t - center‖ := norm_add_le _ _
        _ ≤ ‖R_clm - f_clm‖ * ‖z‖ + ‖t - center‖ := add_le_add ((R_clm - f_clm).le_opNorm z) le_rfl
    have h_main : ‖f_inv v‖ ≤ 2 * (‖R_clm - f_clm‖ * ‖z‖ + ‖t - center‖) := by
      calc ‖f_inv v‖ ≤ ‖f_inv_clm‖ * ‖v‖ := f_inv_clm.le_opNorm v
        _ ≤ 2 * ‖v‖ := mul_le_mul_of_nonneg_right h_inv_norm (by positivity)
        _ ≤ 2 * (‖R_clm - f_clm‖ * ‖z‖ + ‖t - center‖) := by
          exact mul_le_mul_of_nonneg_left h_v_norm (by norm_num)
    have h_final : 2 * (‖R_clm - f_clm‖ * ‖z‖ + ‖t - center‖) ≤ 6 * δ :=
      rounding_margin_calc δ A_john hδ hA_john_le hA_john_one
        ‖R_clm - f_clm‖ ‖z‖ ‖t - center‖
        (by positivity) (by positivity)
        h_op_norm h_z_norm h_center_bound
    have h_margin_eq : margin = 6 * δ := by rfl
    rw [h_margin_eq]
    exact le_trans h_main h_final

  -- Round dimensions using dimGrid_round_up_min
  let xa := A_john * a + 2 * margin
  let xb := A_john * b + 2 * margin
  let xc := A_john * c_dim + 2 * margin
  have hδxa : δ ≤ xa := by linarith [hA_a_lower]
  have hδxb : δ ≤ xb := by
    have h1 : A_john * b ≥ A_john * a := by gcongr
    dsimp only [xb, margin]
    linarith [hA_a_lower, h1]
  have hδxc : δ ≤ xc := by
    have h2 : a ≤ c_dim := le_trans hab hbc
    have h1 : A_john * c_dim ≥ A_john * a := mul_le_mul_of_nonneg_left h2 (by linarith)
    dsimp only [xc, margin]
    linarith [hA_a_lower, h1]
  have hxa250 : xa ≤ 250 := by
    dsimp only [xa, margin]
    have hA_nonneg : 0 ≤ A_john := by linarith
    have h1 : A_john * a ≤ 200 := by
      calc A_john * a ≤ A_john * 20 := by gcongr <;> exact h_dims_bounded.1
        _ ≤ 10 * 20 := by gcongr <;> linarith
        _ = 200 := by norm_num
    have h2 : 12 * δ ≤ 50 := by linarith [hδ_le_one]
    linarith
  have hxb250 : xb ≤ 250 := by
    dsimp only [xb, margin]
    have hA_nonneg : 0 ≤ A_john := by linarith [hA_john_one]
    have h1 : A_john * b ≤ 200 := by
      calc A_john * b ≤ A_john * 20 := mul_le_mul_of_nonneg_left h_dims_bounded.2.1 hA_nonneg
        _ ≤ 10 * 20 := by
          have h2 : A_john ≤ 10 := hA_john_le
          exact mul_le_mul_of_nonneg_right h2 (by linarith)
        _ = 200 := by norm_num
    have h2 : 12 * δ ≤ 50 := by linarith [hδ_le_one]
    linarith
  have hxc250 : xc ≤ 250 := by
    dsimp only [xc, margin]
    have h1 : A_john * c_dim ≤ 200 := by
      calc A_john * c_dim ≤ A_john * 20 := by gcongr <;> exact h_dims_bounded.2.2
        _ ≤ 10 * 20 := by gcongr <;> linarith
        _ = 200 := by norm_num
    have h2 : 12 * δ ≤ 50 := by linarith [hδ_le_one]
    linarith
  rcases dimGrid_round_up_min δ hδ xa hδxa hxa250 with ⟨a', ha'_in, ha'_ge, ha'_le, ha'_min⟩
  rcases dimGrid_round_up_min δ hδ xb hδxb hxb250 with ⟨b', hb'_in, hb'_ge, hb'_le, hb'_min⟩
  rcases dimGrid_round_up_min δ hδ xc hδxc hxc250 with ⟨c', hc'_in, hc'_ge, hc'_le, hc'_min⟩
  have h_a'_le_b' : a' ≤ b' := by
    rcases Finset.mem_image.mp hb'_in with ⟨m, _, h_eq⟩
    have h_xa_le_xb : xa ≤ xb := by
      have h : A_john * a ≤ A_john * b := mul_le_mul_of_nonneg_left hab hA_pos.le
      have h2 : A_john * a + 2 * margin ≤ A_john * b + 2 * margin :=
        add_le_add h (le_refl (2 * margin))
      exact h2
    have h_ge : (2:ℝ)^m * δ ≥ xa := by
      have h_b'_ge_xb : b' ≥ xb := hb'_ge
      have h_eq' : (2:ℝ)^m * δ = b' := h_eq
      rw [←h_eq'] at h_b'_ge_xb
      exact le_trans h_xa_le_xb h_b'_ge_xb
    have h_result : a' ≤ (2:ℝ)^m * δ := ha'_min m h_ge
    rw [h_eq] at h_result
    exact h_result
  have h_b'_le_c' : b' ≤ c' := by
    rcases Finset.mem_image.mp hc'_in with ⟨m, _, h_eq⟩
    have h_xb_le_xc : xb ≤ xc := by
      have h : A_john * b ≤ A_john * c_dim := mul_le_mul_of_nonneg_left hbc hA_pos.le
      have h2 : A_john * b + 2 * margin ≤ A_john * c_dim + 2 * margin :=
        add_le_add h (le_refl (2 * margin))
      exact h2
    have h_ge2 : (2:ℝ)^m * δ ≥ xb := by
      have h_c'_ge_xc : c' ≥ xc := hc'_ge
      have h_eq' : (2:ℝ)^m * δ = c' := h_eq
      rw [←h_eq'] at h_c'_ge_xc
      exact le_trans h_xb_le_xc h_c'_ge_xc
    have h_result2 : b' ≤ (2:ℝ)^m * δ := hb'_min m h_ge2
    rw [h_eq] at h_result2
    exact h_result2
  have h_dims : (a', (b', c')) ∈ dimTriples δ hδ := by
    simp only [dimTriples, Finset.mem_filter, Finset.mem_product]
    exact ⟨⟨ha'_in, hb'_in, hc'_in⟩, ⟨h_a'_le_b', h_b'_le_c'⟩⟩

  -- Precompute half-bounds
  have ha_half : A_john * a / 2 + margin ≤ a' / 2 := by
    have h9 : xa ≤ a' := ha'_ge
    have h10 : xa = A_john * a + 2 * margin := by rfl
    rw [h10] at h9
    have h11 : (A_john * a + 2 * margin) / 2 ≤ a' / 2 := div_le_div_of_nonneg_right h9 (by norm_num)
    have h12 : (A_john * a + 2 * margin) / 2 = A_john * a / 2 + margin := by ring
    rw [h12] at h11
    exact h11
  have hb_half : A_john * b / 2 + margin ≤ b' / 2 := by
    have h9 : xb ≤ b' := hb'_ge
    have h10 : xb = A_john * b + 2 * margin := by rfl
    rw [h10] at h9
    have h11 : (A_john * b + 2 * margin) / 2 ≤ b' / 2 := div_le_div_of_nonneg_right h9 (by norm_num)
    have h12 : (A_john * b + 2 * margin) / 2 = A_john * b / 2 + margin := by ring
    rw [h12] at h11
    exact h11
  have hc_half : A_john * c_dim / 2 + margin ≤ c' / 2 := by
    have h9 : xc ≤ c' := hc'_ge
    have h10 : xc = A_john * c_dim + 2 * margin := by rfl
    rw [h10] at h9
    have h11 : (A_john * c_dim + 2 * margin) / 2 ≤ c' / 2 := div_le_div_of_nonneg_right h9 (by norm_num)
    have h12 : (A_john * c_dim + 2 * margin) / 2 = A_john * c_dim / 2 + margin := by ring
    rw [h12] at h11
    exact h11

  -- Containment
  have h_containment : H ⊆ testParallelepiped center M a' b' c' := by
    intro y hy
    have hy_B20 : y ∈ closedBall (0 : Point3) 20 := by
      have h10 : y ∈ H := hy
      have h11 : H ⊆ closedBall (0 : Point3) 10 := hH_sub_ball
      have h12 : y ∈ closedBall (0 : Point3) 10 := h11 h10
      have h13 : dist y (0 : Point3) ≤ 10 := by simpa [Metric.mem_closedBall] using h12
      have h14 : dist y (0 : Point3) ≤ 20 := by linarith
      simpa [Metric.mem_closedBall] using h14
    rcases h_outer hy with ⟨z, hz, rfl⟩
    let z' := f_inv (R_lin z + (t - center))
    have h_z'_diff : ‖z' - z‖ ≤ margin := h_margin_bound z hz
    have h_z0 : |z' 0| ≤ a' / 2 := by
      have h_eq : z' 0 = z 0 + (z' - z) 0 := by simp
      rw [h_eq]
      have h1 : |z 0| ≤ A_john * a / 2 := hz.1
      have h2 : |(z' - z) 0| ≤ ‖z' - z‖ := h_coord (z' - z) 0
      have h3 : |z 0 + (z' - z) 0| ≤ |z 0| + |(z' - z) 0| := by
        simpa using norm_add_le (z 0) ((z' - z) 0)
      calc |z 0 + (z' - z) 0|
        ≤ |z 0| + |(z' - z) 0| := h3
      _ ≤ A_john * a / 2 + ‖z' - z‖ := add_le_add h1 h2
      _ ≤ A_john * a / 2 + margin := by linarith [h_z'_diff]
      _ ≤ a' / 2 := ha_half
    have h_z1 : |z' 1| ≤ b' / 2 := by
      have h_eq : z' 1 = z 1 + (z' - z) 1 := by simp
      rw [h_eq]
      have h1 : |z 1| ≤ A_john * b / 2 := hz.2.1
      have h2 : |(z' - z) 1| ≤ ‖z' - z‖ := h_coord (z' - z) 1
      have h3 : |z 1 + (z' - z) 1| ≤ |z 1| + |(z' - z) 1| := by
        simpa using norm_add_le (z 1) ((z' - z) 1)
      calc |z 1 + (z' - z) 1|
        ≤ |z 1| + |(z' - z) 1| := h3
      _ ≤ A_john * b / 2 + ‖z' - z‖ := add_le_add h1 h2
      _ ≤ A_john * b / 2 + margin := by linarith [h_z'_diff]
      _ ≤ b' / 2 := hb_half
    have h_z2 : |z' 2| ≤ c' / 2 := by
      have h_eq : z' 2 = z 2 + (z' - z) 2 := by simp
      rw [h_eq]
      have h1 : |z 2| ≤ A_john * c_dim / 2 := hz.2.2
      have h2 : |(z' - z) 2| ≤ ‖z' - z‖ := h_coord (z' - z) 2
      have h3 : |z 2 + (z' - z) 2| ≤ |z 2| + |(z' - z) 2| := by
        simpa using norm_add_le (z 2) ((z' - z) 2)
      calc |z 2 + (z' - z) 2|
        ≤ |z 2| + |(z' - z) 2| := h3
      _ ≤ A_john * c_dim / 2 + ‖z' - z‖ := add_le_add h1 h2
      _ ≤ A_john * c_dim / 2 + margin := by linarith [h_z'_diff]
      _ ≤ c' / 2 := hc_half
    have h_z'_in : z' ∈ axisBox a' b' c' := by
      simp only [axisBox, Set.mem_setOf_eq]; exact ⟨h_z0, h_z1, h_z2⟩
    have h_yz : frame z = center + f z' := by
      have h4 : f z' = R_lin z + (t - center) := by
        simpa only [z'] using hf_inv_id2 (R_lin z + (t - center))
      have h6 : frame z = R_lin z + t := h_frame_eq z
      have h_goal : R_lin z + t = center + (R_lin z + (t - center)) := by abel
      calc frame z = R_lin z + t := h6
        _ = center + (R_lin z + (t - center)) := h_goal
        _ = center + f z' := by rw [h4]
    have h_fz' : f z' ∈ f '' axisBox a' b' c' := Set.mem_image_of_mem f h_z'_in
    have h_yz2 : center +ᵥ f z' = frame z := h_yz.symm
    have h_in_vadd : frame z ∈ center +ᵥ (f '' axisBox a' b' c') :=
      ⟨f z', h_fz', h_yz2⟩
    exact ⟨h_in_vadd, hy_B20⟩

  -- Dimension ratio bounds
  have h_ratios : a' ≤ 14 * A_john * a ∧ b' ≤ 14 * A_john * b ∧ c' ≤ 14 * A_john * c_dim :=
    dimension_ratio_bounds δ a b c_dim A_john a' b' c' margin hδ hA_a_lower hab hbc hA_pos
      ha'_le hb'_le hc'_le (by rfl)
  have ha_ratio : a' ≤ 14 * A_john * a := h_ratios.1
  have hb_ratio : b' ≤ 14 * A_john * b := h_ratios.2.1
  have hc_ratio : c' ≤ 14 * A_john * c_dim := h_ratios.2.2

  -- Volume bound
  have ha'_pos : 0 < a' := dimGrid_all_pos δ hδ a' ha'_in
  have hb'_pos : 0 < b' := dimGrid_all_pos δ hδ b' hb'_in
  have hc'_pos : 0 < c' := dimGrid_all_pos δ hδ c' hc'_in

  have h_vol_test : volume (testParallelepiped center M a' b' c') ≤
      ENNReal.ofReal (|Matrix.det M| * a' * b' * c') :=
    test_parallelepiped_volume_bound center M a' b' c' ha'_pos hb'_pos hc'_pos hdet_ne_zero

  have h_vol_H_lower : volume H ≥ ENNReal.ofReal (a * b * c_dim) := by
    have h_ms : MeasurableSet (axisBox a b c_dim) :=
      Kakeya.Streamlined.measurableSet_axisBox a b c_dim
    have h1 : volume (frame '' axisBox a b c_dim) = volume (axisBox a b c_dim) :=
      AffineIsometryEquiv.volume_image frame (axisBox a b c_dim) h_ms
    have h2 : volume (frame '' axisBox a b c_dim) ≤ volume H := measure_mono h_inner
    have h3 : volume (axisBox a b c_dim) = ENNReal.ofReal (a * b * c_dim) :=
      volume_axisBox a b c_dim ha hb hc
    rw [h1, h3] at h2
    exact h2

  have h_real_bound : |Matrix.det M| * a' * b' * c' ≤ (10^7 : ℝ) * (a * b * c_dim) :=
    rounding_real_volume_bound M a b c_dim a' b' c' A_john
      hA_john_le hA_john_one ha hb hc ha'_pos hb'_pos hc'_pos hdet_bounds ha_ratio hb_ratio hc_ratio

  have h_ennreal_bound : ENNReal.ofReal (|Matrix.det M| * a' * b' * c') ≤
      (10^7 : ENNReal) * ENNReal.ofReal (a * b * c_dim) := by
    have h_pos1 : 0 ≤ |Matrix.det M| * a' * b' * c' := by positivity
    have h_pos2 : 0 ≤ a * b * c_dim := by positivity
    have h9 : ENNReal.ofReal (|Matrix.det M| * a' * b' * c') ≤
        ENNReal.ofReal ((10^7 : ℝ) * (a * b * c_dim)) :=
      ENNReal.ofReal_le_ofReal h_real_bound
    have h10 : ENNReal.ofReal ((10^7 : ℝ) * (a * b * c_dim)) =
        (10^7 : ENNReal) * ENNReal.ofReal (a * b * c_dim) := by
      have h_pos : 0 ≤ (a * b * c_dim) := by positivity
      have h11 : ENNReal.ofReal ((10^7 : ℝ) * (a * b * c_dim)) =
          ENNReal.ofReal (10^7 : ℝ) * ENNReal.ofReal (a * b * c_dim) := by
        rw [ENNReal.ofReal_mul (by positivity)]
      rw [h11]
      have h12 : ENNReal.ofReal (10^7 : ℝ) = (10^7 : ENNReal) := by norm_cast
      rw [h12]
    rw [h10] at h9
    exact h9

  have h_final : volume (testParallelepiped center M a' b' c') ≤ (10^7 : ENNReal) * volume H := by
    calc volume (testParallelepiped center M a' b' c')
      ≤ ENNReal.ofReal (|Matrix.det M| * a' * b' * c') := h_vol_test
    _ ≤ (10^7 : ENNReal) * ENNReal.ofReal (a * b * c_dim) := h_ennreal_bound
    _ ≤ (10^7 : ENNReal) * volume H := by
      exact mul_le_mul_left' h_vol_H_lower (10^7 : ENNReal)

  have h_L_bound : (10^7 : ENNReal) * volume H ≤ L * volume H := by
    exact mul_le_mul_of_nonneg_right hL_big (by positivity)

  exact ⟨center, hc_grid, M, hM, a', b', c', h_dims, h_containment, le_trans h_final h_L_bound⟩

end Kakeya.Streamlined
