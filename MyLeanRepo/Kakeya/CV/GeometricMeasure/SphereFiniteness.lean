import MyLeanRepo.Kakeya.CV.Geometry
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Topology.MetricSpace.Antilipschitz
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Unit sphere has finite codimension-one Hausdorff measure

Cube-boundary proof: the unit sphere is the Lipschitz image of the boundary
of the cube [-1,1]^3, which has finite 2D Hausdorff measure as a finite union
of isometric images of the square [-1,1]^2.
-/

noncomputable section

open Set MeasureTheory Metric
open scoped ENNReal Real

namespace Kakeya.CV

section SphereFinite

/-- The square [-1,1]^2 in Point 2. -/
private def Q : Set (Point 2) := {p | -1 ≤ p 0 ∧ p 0 ≤ 1 ∧ -1 ≤ p 1 ∧ p 1 ≤ 1}

private lemma Q_compact : IsCompact Q := by
  have hc0 : Continuous (fun p : Point 2 => p 0) := PiLp.continuous_apply 2 (fun _ => ℝ) 0
  have hc1 : Continuous (fun p : Point 2 => p 1) := PiLp.continuous_apply 2 (fun _ => ℝ) 1
  have h11 : IsClosed {p : Point 2 | -1 ≤ p 0} := by
    simpa using isClosed_le (show Continuous (fun _ => (-1 : ℝ)) from continuous_const) hc0
  have h12 : IsClosed {p : Point 2 | p 0 ≤ 1} := by
    simpa using isClosed_le hc0 (show Continuous (fun _ => (1 : ℝ)) from continuous_const)
  have h13 : IsClosed {p : Point 2 | -1 ≤ p 1} := by
    simpa using isClosed_le (show Continuous (fun _ => (-1 : ℝ)) from continuous_const) hc1
  have h14 : IsClosed {p : Point 2 | p 1 ≤ 1} := by
    simpa using isClosed_le hc1 (show Continuous (fun _ => (1 : ℝ)) from continuous_const)
  have h_eq : Q = {p : Point 2 | -1 ≤ p 0} ∩ {p : Point 2 | p 0 ≤ 1} ∩
      {p : Point 2 | -1 ≤ p 1} ∩ {p : Point 2 | p 1 ≤ 1} := by
    ext x
    simp [Q]
    tauto
  have h1 : IsClosed Q := by
    rw [h_eq]
    simpa [inter_assoc] using (h11.inter h12).inter h13 |>.inter h14
  have h2 : Bornology.IsBounded Q := by
    have h3 : Q ⊆ Metric.closedBall (0 : Point 2) (Real.sqrt 2) := by
      intro x hx
      rcases hx with ⟨h6, h7, h8, h9⟩
      have h4 : ‖x‖ ≤ Real.sqrt 2 := by
        have h5 : ‖x‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 := by
          rw [EuclideanSpace.real_norm_sq_eq]
          simp [Fin.sum_univ_succ]
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      simpa [Metric.mem_closedBall] using h4
    exact Metric.isBounded_closedBall.subset h3
  have h3 : IsCompact (closure Q) := h2.isCompact_closure
  have h4 : closure Q = Q := h1.closure_eq
  rwa [h4] at h3

private lemma Q_lt_top : (μH[(2 : ℝ)] : Measure (Point 2)) Q < ⊤ := by
  have h_finrank : (Module.finrank ℝ (Point 2) : ℝ) = 2 := by simp
  have h_main : (μH[Module.finrank ℝ (Point 2)] : Measure (Point 2)) Q < ⊤ :=
    IsCompact.measure_lt_top Q_compact
  simpa [h_finrank] using h_main

/-- Embedding of a square face into Point 3. -/
private def face (i : Fin 3) (sign : ℝ) : Point 2 → Point 3 := fun y =>
  match i with
  | 0 => WithLp.toLp 2 ![sign, y 0, y 1]
  | 1 => WithLp.toLp 2 ![y 0, sign, y 1]
  | 2 => WithLp.toLp 2 ![y 0, y 1, sign]

private lemma face_iso (i : Fin 3) (sign : ℝ) : Isometry (face i sign) := by
  refine' Isometry.of_dist_eq _
  intro x y
  have h : ‖face i sign x - face i sign y‖ ^ 2 = ‖x - y‖ ^ 2 := by
    fin_cases i <;> simp [face, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ]
  have hpos1 : 0 ≤ ‖face i sign x - face i sign y‖ := by positivity
  have hpos2 : 0 ≤ ‖x - y‖ := by positivity
  have h' : ‖face i sign x - face i sign y‖ = ‖x - y‖ := by nlinarith
  simpa [dist_eq_norm] using h'

/-- Cube boundary C = union of 6 faces. -/
private def C : Set (Point 3) :=
  (face 0 1 '' Q) ∪ (face 0 (-1) '' Q) ∪
  (face 1 1 '' Q) ∪ (face 1 (-1) '' Q) ∪
  (face 2 1 '' Q) ∪ (face 2 (-1) '' Q)

private lemma face_meas_lt_top (i : Fin 3) (sign : ℝ) :
    (μH[(2 : ℝ)] : Measure (Point 3)) (face i sign '' Q) < ⊤ := by
  have h_iso : Isometry (face i sign) := face_iso i sign
  have h_eq : (μH[(2 : ℝ)] : Measure (Point 3)) (face i sign '' Q) =
      (μH[(2 : ℝ)] : Measure (Point 2)) Q :=
    h_iso.hausdorffMeasure_image (Or.inl (by norm_num)) Q
  rw [h_eq]
  exact Q_lt_top

private lemma C_lt_top : (μH[(2 : ℝ)] : Measure (Point 3)) C < ⊤ := by
  let f0 := face 0 1 '' Q
  let f1 := face 0 (-1) '' Q
  let f2 := face 1 1 '' Q
  let f3 := face 1 (-1) '' Q
  let f4 := face 2 1 '' Q
  let f5 := face 2 (-1) '' Q
  let U1 := f0 ∪ f1
  let U2 := U1 ∪ f2
  let U3 := U2 ∪ f3
  let U4 := U3 ∪ f4
  let U5 := U4 ∪ f5
  have h01 : μH[(2 : ℝ)] f0 < ⊤ := face_meas_lt_top 0 1
  have h02 : μH[(2 : ℝ)] f1 < ⊤ := face_meas_lt_top 0 (-1)
  have h11 : μH[(2 : ℝ)] f2 < ⊤ := face_meas_lt_top 1 1
  have h12 : μH[(2 : ℝ)] f3 < ⊤ := face_meas_lt_top 1 (-1)
  have h21 : μH[(2 : ℝ)] f4 < ⊤ := face_meas_lt_top 2 1
  have h22 : μH[(2 : ℝ)] f5 < ⊤ := face_meas_lt_top 2 (-1)
  have h_C : C = U5 := by
    simp [C, U5, U4, U3, U2, U1, f0, f1, f2, f3, f4, f5]
  rw [h_C]
  have h1 : μH[(2 : ℝ)] U1 ≤ μH[(2 : ℝ)] f0 + μH[(2 : ℝ)] f1 := measure_union_le _ _
  have h2 : μH[(2 : ℝ)] U2 ≤ μH[(2 : ℝ)] U1 + μH[(2 : ℝ)] f2 := measure_union_le _ _
  have h3 : μH[(2 : ℝ)] U3 ≤ μH[(2 : ℝ)] U2 + μH[(2 : ℝ)] f3 := measure_union_le _ _
  have h4 : μH[(2 : ℝ)] U4 ≤ μH[(2 : ℝ)] U3 + μH[(2 : ℝ)] f4 := measure_union_le _ _
  have h5 : μH[(2 : ℝ)] U5 ≤ μH[(2 : ℝ)] U4 + μH[(2 : ℝ)] f5 := measure_union_le _ _
  have h_u : μH[(2 : ℝ)] U5 ≤
      μH[(2 : ℝ)] f0 + μH[(2 : ℝ)] f1 + μH[(2 : ℝ)] f2 +
      μH[(2 : ℝ)] f3 + μH[(2 : ℝ)] f4 + μH[(2 : ℝ)] f5 := by
    calc
      μH[(2 : ℝ)] U5
        ≤ μH[(2 : ℝ)] U4 + μH[(2 : ℝ)] f5 := h5
      _ ≤ (μH[(2 : ℝ)] U3 + μH[(2 : ℝ)] f4) + μH[(2 : ℝ)] f5 := by gcongr
      _ ≤ ((μH[(2 : ℝ)] U2 + μH[(2 : ℝ)] f3) + μH[(2 : ℝ)] f4) + μH[(2 : ℝ)] f5 := by gcongr
      _ ≤ (((μH[(2 : ℝ)] U1 + μH[(2 : ℝ)] f2) + μH[(2 : ℝ)] f3) + μH[(2 : ℝ)] f4) + μH[(2 : ℝ)] f5 := by gcongr
      _ ≤ (((μH[(2 : ℝ)] f0 + μH[(2 : ℝ)] f1) + μH[(2 : ℝ)] f2) + μH[(2 : ℝ)] f3) + μH[(2 : ℝ)] f4 + μH[(2 : ℝ)] f5 := by gcongr
      _ = μH[(2 : ℝ)] f0 + μH[(2 : ℝ)] f1 + μH[(2 : ℝ)] f2 + μH[(2 : ℝ)] f3 + μH[(2 : ℝ)] f4 + μH[(2 : ℝ)] f5 := by ring
  have h_s1 : μH[(2 : ℝ)] f0 + μH[(2 : ℝ)] f1 < ⊤ := ENNReal.add_lt_top.mpr ⟨h01, h02⟩
  have h_s2 : (μH[(2 : ℝ)] f0 + μH[(2 : ℝ)] f1) + μH[(2 : ℝ)] f2 < ⊤ := ENNReal.add_lt_top.mpr ⟨h_s1, h11⟩
  have h_s3 : ((μH[(2 : ℝ)] f0 + μH[(2 : ℝ)] f1) + μH[(2 : ℝ)] f2) + μH[(2 : ℝ)] f3 < ⊤ := ENNReal.add_lt_top.mpr ⟨h_s2, h12⟩
  have h_s4 : (((μH[(2 : ℝ)] f0 + μH[(2 : ℝ)] f1) + μH[(2 : ℝ)] f2) + μH[(2 : ℝ)] f3) + μH[(2 : ℝ)] f4 < ⊤ := ENNReal.add_lt_top.mpr ⟨h_s3, h21⟩
  have h_s5 : ((((μH[(2 : ℝ)] f0 + μH[(2 : ℝ)] f1) + μH[(2 : ℝ)] f2) + μH[(2 : ℝ)] f3) + μH[(2 : ℝ)] f4) + μH[(2 : ℝ)] f5 < ⊤ := ENNReal.add_lt_top.mpr ⟨h_s4, h22⟩
  have h_sum : μH[(2 : ℝ)] f0 + μH[(2 : ℝ)] f1 + μH[(2 : ℝ)] f2 +
      μH[(2 : ℝ)] f3 + μH[(2 : ℝ)] f4 + μH[(2 : ℝ)] f5 < ⊤ := by
    simpa [add_assoc] using h_s5
  exact lt_of_le_of_lt h_u h_sum

/-- Coordinate absolute value bounded by Euclidean norm. -/
private lemma coord_norm_le {n : ℕ} (x : Point n) (i : Fin n) : |x i| ≤ ‖x‖ := by
  have h3 : |x i| ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    have h4 : (x i) ^ 2 ≤ ∑ j : Fin n, (x j) ^ 2 :=
      Finset.single_le_sum (f := fun j : Fin n => (x j)^2) (s := Finset.univ)
        (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    simpa [abs_pow] using h4
  have h5 : 0 ≤ |x i| := by positivity
  have h6 : 0 ≤ ‖x‖ := by positivity
  nlinarith

private lemma C_norm_ge_one {x : Point 3} (hx : x ∈ C) : 1 ≤ ‖x‖ := by
  have h_exists : ∃ (i : Fin 3) (sign : ℝ) (y : Point 2),
      (sign = 1 ∨ sign = -1) ∧ y ∈ Q ∧ face i sign y = x := by
    simp only [C, mem_union] at hx
    have h_flat : x ∈ (face 0 1 '' Q) ∨ x ∈ (face 0 (-1) '' Q) ∨
        x ∈ (face 1 1 '' Q) ∨ x ∈ (face 1 (-1) '' Q) ∨
        x ∈ (face 2 1 '' Q) ∨ x ∈ (face 2 (-1) '' Q) := by
      tauto
    rcases h_flat with (h | h | h | h | h | h)
    · rcases h with ⟨y, hy, h_eq⟩; exact ⟨0, 1, y, Or.inl rfl, hy, h_eq⟩
    · rcases h with ⟨y, hy, h_eq⟩; exact ⟨0, -1, y, Or.inr rfl, hy, h_eq⟩
    · rcases h with ⟨y, hy, h_eq⟩; exact ⟨1, 1, y, Or.inl rfl, hy, h_eq⟩
    · rcases h with ⟨y, hy, h_eq⟩; exact ⟨1, -1, y, Or.inr rfl, hy, h_eq⟩
    · rcases h with ⟨y, hy, h_eq⟩; exact ⟨2, 1, y, Or.inl rfl, hy, h_eq⟩
    · rcases h with ⟨y, hy, h_eq⟩; exact ⟨2, -1, y, Or.inr rfl, hy, h_eq⟩
  rcases h_exists with ⟨i, sign, y, hsign, _hy, h_eq⟩
  have h_abs : |sign| = 1 := by rcases hsign with (rfl | rfl) <;> norm_num
  have h_coord : (face i sign y) i = sign := by
    fin_cases i <;> simp [face]
  have h1 : |(face i sign y) i| = 1 := by
    rw [h_coord, h_abs]
  have h2 : |(face i sign y) i| ≤ ‖face i sign y‖ := coord_norm_le (face i sign y) i
  have h3 : 1 ≤ ‖face i sign y‖ := by linarith
  rw [←h_eq]
  exact h3

private lemma face_in_C (i : Fin 3) (sign : ℝ) (hsign : sign = 1 ∨ sign = -1)
    {y : Point 2} (hy : y ∈ Q) : face i sign y ∈ C := by
  have h : face i sign y ∈ face i sign '' Q := ⟨y, hy, rfl⟩
  rcases hsign with (rfl | rfl)
  · fin_cases i
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h))))
    · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
    · exact Or.inl (Or.inr h)
  · fin_cases i
    · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inr h

/-- For any point on sphere, radial projection of cube boundary point hits it. -/
private lemma sphere_subset_C_image :
    unitSphere 3 ⊆ (fun x : Point 3 => (‖x‖)⁻¹ • x) '' C := by
  intro z hz
  have hnorm : ‖z‖ = 1 := by simpa [unitSphere, Metric.mem_sphere] using hz
  have hz_ne_zero : z ≠ 0 := by
    intro h; rw [h] at hnorm; simp at hnorm
  let m : ℝ := max (max (|z 0|) (|z 1|)) (|z 2|)
  have hm_pos : 0 < m := by
    by_cases h : m = 0
    · have h1 : |z 0| ≤ m := le_max_of_le_left (le_max_left _ _)
      have h2 : |z 1| ≤ m := le_max_of_le_left (le_max_right _ _)
      have h3 : |z 2| ≤ m := le_max_right _ _
      rw [h] at h1 h2 h3
      have h4 : |z 0| = 0 := by linarith [abs_nonneg (z 0)]
      have h5 : |z 1| = 0 := by linarith [abs_nonneg (z 1)]
      have h6 : |z 2| = 0 := by linarith [abs_nonneg (z 2)]
      have h7 : z 0 = 0 := by simpa [abs_eq_zero] using h4
      have h8 : z 1 = 0 := by simpa [abs_eq_zero] using h5
      have h9 : z 2 = 0 := by simpa [abs_eq_zero] using h6
      have h10 : z = 0 := by ext i; fin_cases i <;> tauto
      exfalso
      exact hz_ne_zero h10
    · have h' : 0 ≤ m := by positivity
      exact lt_of_le_of_ne h' (Ne.symm h)
  let x : Point 3 := m⁻¹ • z
  have hxi : ∀ i : Fin 3, x i = m⁻¹ * z i := by intro i; rfl
  have h_abs_le : ∀ i : Fin 3, |x i| ≤ 1 := by
    intro i
    have h4 : |x i| = |z i| / m := by
      rw [hxi i, abs_mul, abs_inv, abs_of_pos hm_pos]
      ring
    rw [h4]
    have h5 : |z i| ≤ m := by
      fin_cases i <;> simp [m]
    have h6 : |z i| / m ≤ 1 := by
      apply (div_le_one hm_pos).mpr
      exact h5
    exact h6
  have h_max_eq : |z 0| = m ∨ |z 1| = m ∨ |z 2| = m := by
    have h_a : max (|z 0|) (|z 1|) = |z 0| ∨ max (|z 0|) (|z 1|) = |z 1| :=
      max_choice (|z 0|) (|z 1|)
    rcases h_a with (h_a | h_a)
    · have h_b : m = max (|z 0|) (|z 2|) := by simp [m, h_a]
      have h_c : max (|z 0|) (|z 2|) = |z 0| ∨ max (|z 0|) (|z 2|) = |z 2| :=
        max_choice (|z 0|) (|z 2|)
      rcases h_c with (h_c | h_c)
      · exact Or.inl (by simp [h_b, h_c])
      · exact Or.inr (Or.inr (by simp [h_b, h_c]))
    · have h_b : m = max (|z 1|) (|z 2|) := by simp [m, h_a]
      have h_c : max (|z 1|) (|z 2|) = |z 1| ∨ max (|z 1|) (|z 2|) = |z 2| :=
        max_choice (|z 1|) (|z 2|)
      rcases h_c with (h_c | h_c)
      · exact Or.inr (Or.inl (by simp [h_b, h_c]))
      · exact Or.inr (Or.inr (by simp [h_b, h_c]))
  have h_radial : (‖x‖)⁻¹ • x = z := by
    have h_norm_x : ‖x‖ = m⁻¹ := by
      have h1 : ‖x‖ = ‖(m⁻¹ : ℝ)‖ * ‖z‖ := by
        rw [show x = (m⁻¹ : ℝ) • z from rfl, norm_smul]
      rw [h1, hnorm]
      have h2 : ‖(m⁻¹ : ℝ)‖ = |m⁻¹| := Real.norm_eq_abs (m⁻¹)
      rw [h2, abs_inv, abs_of_pos hm_pos]
      ring
    have h3 : (‖x‖)⁻¹ = m := by
      rw [h_norm_x]
      field_simp [hm_pos.ne']
    rw [h3]
    have h4 : m • x = z := by
      calc
        m • x = m • (m⁻¹ • z) := by rfl
        _ = (m * m⁻¹) • z := by rw [smul_smul]
        _ = (1 : ℝ) • z := by
          have h_mul : m * m⁻¹ = 1 := by field_simp [hm_pos.ne']
          rw [h_mul]
        _ = z := by rw [one_smul]
    exact h4
  have h_bounds : ∀ i : Fin 3, -1 ≤ x i ∧ x i ≤ 1 := by
    intro i
    have h_abs : |x i| ≤ 1 := h_abs_le i
    have h_left : -1 ≤ x i := by linarith [abs_le.mp h_abs]
    have h_right : x i ≤ 1 := by linarith [abs_le.mp h_abs]
    exact ⟨h_left, h_right⟩
  have hQ2 : ∀ (a b : ℝ), -1 ≤ a → a ≤ 1 → -1 ≤ b → b ≤ 1 →
      (WithLp.toLp 2 ![a, b] : Point 2) ∈ Q := by
    intro a b ha1 ha2 hb1 hb2
    simpa [Q] using ⟨ha1, ha2, hb1, hb2⟩
  rcases h_max_eq with (h | h | h)
  · have hx0 : |x 0| = 1 := by
      have h7 : |x 0| = |z 0| / m := by
        rw [hxi 0, abs_mul, abs_inv, abs_of_pos hm_pos]
        ring
      rw [h7, h]
      field_simp [hm_pos.ne']
    have hsi : x 0 = 1 ∨ x 0 = -1 := by
      by_cases hpos : 0 ≤ x 0
      · left; rw [abs_of_nonneg hpos] at hx0; linarith
      · right; rw [abs_of_neg (by linarith)] at hx0; linarith
    rcases hsi with (hsi | hsi)
    · let y : Point 2 := WithLp.toLp 2 ![x 1, x 2]
      have hyQ : y ∈ Q := hQ2 (x 1) (x 2) (h_bounds 1).1 (h_bounds 1).2 (h_bounds 2).1 (h_bounds 2).2
      have hface : face 0 1 y = x := by
        ext j
        fin_cases j <;> simp [face, y, hsi]
      have h_in_C : x ∈ C := by
        rw [←hface]
        exact face_in_C 0 1 (Or.inl rfl) hyQ
      exact ⟨x, h_in_C, h_radial⟩
    · let y : Point 2 := WithLp.toLp 2 ![x 1, x 2]
      have hyQ : y ∈ Q := hQ2 (x 1) (x 2) (h_bounds 1).1 (h_bounds 1).2 (h_bounds 2).1 (h_bounds 2).2
      have hface : face 0 (-1) y = x := by
        ext j
        fin_cases j <;> simp [face, y, hsi]
      have h_in_C : x ∈ C := by
        rw [←hface]
        exact face_in_C 0 (-1) (Or.inr rfl) hyQ
      exact ⟨x, h_in_C, h_radial⟩
  · have hx1 : |x 1| = 1 := by
      have h7 : |x 1| = |z 1| / m := by
        rw [hxi 1, abs_mul, abs_inv, abs_of_pos hm_pos]
        ring
      rw [h7, h]
      field_simp [hm_pos.ne']
    have hsi : x 1 = 1 ∨ x 1 = -1 := by
      by_cases hpos : 0 ≤ x 1
      · left; rw [abs_of_nonneg hpos] at hx1; linarith
      · right; rw [abs_of_neg (by linarith)] at hx1; linarith
    rcases hsi with (hsi | hsi)
    · let y : Point 2 := WithLp.toLp 2 ![x 0, x 2]
      have hyQ : y ∈ Q := hQ2 (x 0) (x 2) (h_bounds 0).1 (h_bounds 0).2 (h_bounds 2).1 (h_bounds 2).2
      have hface : face 1 1 y = x := by
        ext j
        fin_cases j <;> simp [face, y, hsi]
      have h_in_C : x ∈ C := by
        rw [←hface]
        exact face_in_C 1 1 (Or.inl rfl) hyQ
      exact ⟨x, h_in_C, h_radial⟩
    · let y : Point 2 := WithLp.toLp 2 ![x 0, x 2]
      have hyQ : y ∈ Q := hQ2 (x 0) (x 2) (h_bounds 0).1 (h_bounds 0).2 (h_bounds 2).1 (h_bounds 2).2
      have hface : face 1 (-1) y = x := by
        ext j
        fin_cases j <;> simp [face, y, hsi]
      have h_in_C : x ∈ C := by
        rw [←hface]
        exact face_in_C 1 (-1) (Or.inr rfl) hyQ
      exact ⟨x, h_in_C, h_radial⟩
  · have hx2 : |x 2| = 1 := by
      have h7 : |x 2| = |z 2| / m := by
        rw [hxi 2, abs_mul, abs_inv, abs_of_pos hm_pos]
        ring
      rw [h7, h]
      field_simp [hm_pos.ne']
    have hsi : x 2 = 1 ∨ x 2 = -1 := by
      by_cases hpos : 0 ≤ x 2
      · left; rw [abs_of_nonneg hpos] at hx2; linarith
      · right; rw [abs_of_neg (by linarith)] at hx2; linarith
    rcases hsi with (hsi | hsi)
    · let y : Point 2 := WithLp.toLp 2 ![x 0, x 1]
      have hyQ : y ∈ Q := hQ2 (x 0) (x 1) (h_bounds 0).1 (h_bounds 0).2 (h_bounds 1).1 (h_bounds 1).2
      have hface : face 2 1 y = x := by
        ext j
        fin_cases j <;> simp [face, y, hsi]
      have h_in_C : x ∈ C := by
        rw [←hface]
        exact face_in_C 2 1 (Or.inl rfl) hyQ
      exact ⟨x, h_in_C, h_radial⟩
    · let y : Point 2 := WithLp.toLp 2 ![x 0, x 1]
      have hyQ : y ∈ Q := hQ2 (x 0) (x 1) (h_bounds 0).1 (h_bounds 0).2 (h_bounds 1).1 (h_bounds 1).2
      have hface : face 2 (-1) y = x := by
        ext j
        fin_cases j <;> simp [face, y, hsi]
      have h_in_C : x ∈ C := by
        rw [←hface]
        exact face_in_C 2 (-1) (Or.inr rfl) hyQ
      exact ⟨x, h_in_C, h_radial⟩

/-- Unit sphere has finite 2D Hausdorff measure. -/
lemma sphere_finite : codimensionOneMeasure 3 (unitSphere 3) < ⊤ := by
  let radial : Point 3 → Point 3 := fun x => (‖x‖)⁻¹ • x
  have h_lip : LipschitzOnWith (2 : NNReal) radial C := by
    intro x hx y hy
    have hx1 : 1 ≤ ‖x‖ := C_norm_ge_one hx
    have hy1 : 1 ≤ ‖y‖ := C_norm_ge_one hy
    have hpx : 0 < ‖x‖ := by linarith
    have hpy : 0 < ‖y‖ := by linarith
    have hrev : |‖y‖ - ‖x‖| ≤ ‖x - y‖ := by
      have h1 : ‖y‖ ≤ ‖x‖ + ‖y - x‖ := by
        calc ‖y‖ = ‖x + (y - x)‖ := by abel_nf
          _ ≤ ‖x‖ + ‖y - x‖ := norm_add_le _ _
      have h2 : ‖y - x‖ = ‖x - y‖ := by rw [norm_sub_rev]
      have h3 : ‖y‖ - ‖x‖ ≤ ‖x - y‖ := by linarith
      have h4 : ‖x‖ ≤ ‖y‖ + ‖x - y‖ := by
        calc ‖x‖ = ‖y + (x - y)‖ := by abel_nf
          _ ≤ ‖y‖ + ‖x - y‖ := norm_add_le _ _
      have h5 : ‖x‖ - ‖y‖ ≤ ‖x - y‖ := by linarith
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    set nx := radial x with hnx
    set ny := radial y with hny
    have h_main : ‖nx - ny‖ ≤ 2 * ‖x - y‖ := by
      calc
        ‖nx - ny‖
          ≤ ‖nx - (‖x‖)⁻¹ • y‖ + ‖(‖x‖)⁻¹ • y - ny‖ := by
            have h_split : nx - ny = (nx - (‖x‖)⁻¹ • y) + ((‖x‖)⁻¹ • y - ny) := by abel
            rw [h_split]
            exact norm_add_le _ _
        _ = ‖x - y‖ / ‖x‖ + ‖y‖ * |(‖x‖)⁻¹ - (‖y‖)⁻¹| := by
            have h1 : ‖nx - (‖x‖)⁻¹ • y‖ = ‖x - y‖ / ‖x‖ := by
              have h : nx - (‖x‖)⁻¹ • y = (‖x‖)⁻¹ • (x - y) := by
                simp [hnx, radial, smul_sub]
              rw [h, norm_smul, Real.norm_eq_abs]
              have hpos : 0 < (‖x‖)⁻¹ := by positivity
              rw [abs_of_pos hpos]
              ring
            have h2 : ‖(‖x‖)⁻¹ • y - ny‖ = ‖y‖ * |(‖x‖)⁻¹ - (‖y‖)⁻¹| := by
              have h : (‖x‖)⁻¹ • y - ny = ((‖x‖)⁻¹ - (‖y‖)⁻¹) • y := by
                simp [hny, radial, sub_smul]
              rw [h, norm_smul]
              have hnorm : ‖(‖x‖)⁻¹ - (‖y‖)⁻¹‖ = |(‖x‖)⁻¹ - (‖y‖)⁻¹| := Real.norm_eq_abs _
              rw [hnorm]
              ring
            rw [h1, h2]
        _ = ‖x - y‖ / ‖x‖ + |‖y‖ - ‖x‖| / ‖x‖ := by
            have h3 : ‖y‖ * |(‖x‖)⁻¹ - (‖y‖)⁻¹| = |‖y‖ - ‖x‖| / ‖x‖ := by
              have h4 : (‖x‖)⁻¹ - (‖y‖)⁻¹ = (‖y‖ - ‖x‖) / (‖x‖ * ‖y‖) := by
                field_simp [hpx.ne', hpy.ne']
              rw [h4]
              simp [abs_mul, abs_div]
              field_simp [hpx.ne', hpy.ne']
            rw [h3]
        _ ≤ ‖x - y‖ / ‖x‖ + ‖x - y‖ / ‖x‖ := by gcongr
        _ = 2 * ‖x - y‖ / ‖x‖ := by ring
        _ ≤ 2 * ‖x - y‖ := by
          have h6 : (‖x‖)⁻¹ ≤ 1 := by
            have h_pos : 0 < ‖x‖ := hpx
            have h7 : 1 ≤ ‖x‖ := hx1
            calc (‖x‖)⁻¹
              = 1 / ‖x‖ := by simp
            _ ≤ 1 / 1 := by gcongr
            _ = 1 := by norm_num
          have h5 : 2 * ‖x - y‖ / ‖x‖ ≤ 2 * ‖x - y‖ := by
            have h9 : 2 * ‖x - y‖ / ‖x‖ = (‖x‖)⁻¹ * (2 * ‖x - y‖) := by ring
            rw [h9]
            have h10 : (‖x‖)⁻¹ * (2 * ‖x - y‖) ≤ 1 * (2 * ‖x - y‖) := mul_le_mul_of_nonneg_right h6 (by positivity)
            simpa [one_mul] using h10
          exact h5
    have h_dist : dist nx ny ≤ 2 * dist x y := by
      simpa [dist_eq_norm] using h_main
    have h_edist : edist nx ny ≤ (2 : ENNReal) * edist x y := by
      rw [edist_dist, edist_dist]
      have h9 : ENNReal.ofReal (dist nx ny) ≤ ENNReal.ofReal (2 * dist x y) :=
        ENNReal.ofReal_le_ofReal h_dist
      have h10 : ENNReal.ofReal (2 * dist x y) = (2 : ENNReal) * ENNReal.ofReal (dist x y) := by
        have h_pos : 0 ≤ (2 : ℝ) := by norm_num
        rw [ENNReal.ofReal_mul h_pos]
        norm_cast
      rw [h10] at h9
      exact h9
    exact h_edist
  have h_main2 : μH[(2 : ℝ)] (radial '' C) ≤ (4 : ENNReal) * μH[(2 : ℝ)] C := by
    have h := LipschitzOnWith.hausdorffMeasure_image_le h_lip (by norm_num : 0 ≤ (2 : ℝ))
    have h4pow : (↑(2 : NNReal) : ENNReal) ^ (2 : ℝ) = (4 : ENNReal) := by norm_num
    rw [h4pow] at h
    exact h
  have h_final : μH[(2 : ℝ)] (unitSphere 3) ≤ (4 : ENNReal) * μH[(2 : ℝ)] C :=
    le_trans (measure_mono sphere_subset_C_image) h_main2
  have hC_lt : μH[(2 : ℝ)] C < ⊤ := C_lt_top
  have h_ne : (4 : ENNReal) * μH[(2 : ℝ)] C ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) hC_lt.ne
  have h3 : (4 : ENNReal) * μH[(2 : ℝ)] C < ⊤ := by
    exact WithTop.lt_top_iff_ne_top.mpr h_ne
  have h_goal : μH[(2 : ℝ)] (unitSphere 3) < ⊤ :=
    lt_of_le_of_lt h_final h3
  have h_dim : codimensionOneMeasure 3 (unitSphere 3) = μH[(2 : ℝ)] (unitSphere 3) := by
    simp [codimensionOneMeasure]
    norm_num
  rw [h_dim]; exact h_goal

end SphereFinite

end Kakeya.CV
