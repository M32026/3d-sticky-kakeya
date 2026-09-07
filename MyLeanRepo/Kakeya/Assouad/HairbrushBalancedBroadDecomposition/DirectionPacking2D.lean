import MyLeanRepo.Kakeya.Assouad.Subunit.HairbrushStatements
import MyLeanRepo.Kakeya.Assouad.HairbrushBalancedBroadDecomposition.MultiplicityBound
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# 2D direction packing bound in a spherical cap

Given a finite set of unit vectors that are pairwise `(2δ/π)`-separated and all
within acute angle `theta` of a fixed direction `v0`, the cardinality is at most
`C * (theta / δ)^2`.

## Proof

1. Split vectors into same-side/opposite-side halves relative to `v0⊥`.
2. For each half, project orthogonally onto `v0⊥`.
3. For `theta ≤ 1/2`, projection distorts distances by at most `1/√3`.
4. Grid packing in 2D gives `16 * (theta / (ε/√3))^2`.
5. Multiply by 2 for the split: `32 * ... ≤ 300 * (theta/δ)^2`.
6. For `theta > 1/2`, use global sphere packing `26/ε²`.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Finset InnerProductGeometry Real

attribute [local instance] Classical.propDecidable

/-! ### Helper lemmas -/

/-- Sum over `Fin 3`. -/
private lemma sum3 (f : Fin 3 → ℝ) : ∑ i : Fin 3, f i = f 0 + f 1 + f 2 := by
  have h1 : ∑ i : Fin 3, f i = f 0 + ∑ i : Fin 2, f i.succ := Fin.sum_univ_succ f
  have h2 : ∑ i : Fin 2, f i.succ = f 1 + ∑ i : Fin 1, f i.succ.succ := Fin.sum_univ_succ (f ∘ Fin.succ)
  have h3 : ∑ i : Fin 1, f i.succ.succ = f 2 := by
    rw [Fin.sum_univ_succ] <;> simp
  rw [h1, h2, h3] <;> ring

/-- Norm squared of a `Point3` equals sum of component squares. -/
private lemma norm3_sq (x : Point3) : ‖x‖ ^ 2 = (x 0)^2 + (x 1)^2 + (x 2)^2 := by
  have hsum' : ∑ i : Fin 3, ‖x i‖ ^ 2 = ∑ i : Fin 3, (x i)^2 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Real.norm_eq_abs, sq_abs]
  have hsqrt : ‖x‖ = Real.sqrt (∑ i : Fin 3, ‖x i‖ ^ 2) := EuclideanSpace.norm_eq x
  have h : ‖x‖ ^ 2 = ∑ i : Fin 3, ‖x i‖ ^ 2 := by
    rw [hsqrt, Real.sq_sqrt (by positivity)]
  have h2 : ∑ i : Fin 3, (x i)^2 = (x 0)^2 + (x 1)^2 + (x 2)^2 := sum3 (fun i => (x i)^2)
  rw [h, hsum', h2]

/-- Inner product of `Point3` vectors equals dot product. -/
private lemma inner3 (x y : Point3) : inner ℝ x y = x 0 * y 0 + x 1 * y 1 + x 2 * y 2 := by
  have h : inner ℝ x y = ∑ i : Fin 3, x i * y i := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    <;> simp [dotProduct, Fin.sum_univ_succ] <;> ring
  have h2 : ∑ i : Fin 3, x i * y i = x 0 * y 0 + x 1 * y 1 + x 2 * y 2 := sum3 (fun i => x i * y i)
  rw [h, h2]

/-- Existence of a unit vector perpendicular to a given unit vector in `ℝ³`. -/
private lemma exists_perpendicular_unit (v : Point3) (hv : ‖v‖ = 1) :
    ∃ (n : Point3), ‖n‖ = 1 ∧ inner ℝ v n = 0 := by
  by_cases h : (v 0) = 0 ∧ (v 1) = 0
  · let e0 : Point3 := EuclideanSpace.single 0 1
    have he0_norm : ‖e0‖ = 1 := by
      rw [PiLp.norm_single] <;> norm_num
    have h_orth : inner ℝ v e0 = 0 := by
      rw [EuclideanSpace.inner_single_right]
      simp [h.1]
    exact ⟨e0, he0_norm, h_orth⟩
  · let f : Fin 3 → ℝ := fun i =>
      match i with
      | 0 => -(v 1)
      | 1 => v 0
      | 2 => 0
    let w : Point3 := WithLp.toLp 2 f
    have hwf : ∀ i, w i = f i := by intro i; rfl
    have h_orth : inner ℝ v w = 0 := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      have hstar : star (v : Fin 3 → ℝ) = (v : Fin 3 → ℝ) := by ext i; simp
      rw [hstar]
      simp [dotProduct, Fin.sum_univ_succ, hwf] <;> ring
    have h_pos2 : 0 < (v 0)^2 + (v 1)^2 := by
      by_contra h3
      have h4 : (v 0)^2 + (v 1)^2 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
      have h5 : v 0 = 0 := by nlinarith
      have h6 : v 1 = 0 := by nlinarith
      exact h ⟨h5, h6⟩
    have h_norm2 : ‖w‖ ^ 2 = (v 0)^2 + (v 1)^2 := by
      have hsqrt : ‖w‖ = Real.sqrt (∑ i : Fin 3, ‖w i‖ ^ 2) := by
        rw [EuclideanSpace.norm_eq]
      have hsum : ∑ i : Fin 3, (w i)^2 = (v 0)^2 + (v 1)^2 := by
        simp [Fin.sum_univ_succ, hwf] <;> ring
      rw [hsqrt]
      have hsum' : ∑ i : Fin 3, ‖w i‖ ^ 2 = ∑ i : Fin 3, (w i)^2 := by
        apply Finset.sum_congr rfl; intro i _; simp
      rw [hsum', hsum]
      <;> rw [Real.sq_sqrt (by positivity)]
    let c : ℝ := 1 / Real.sqrt ((v 0)^2 + (v 1)^2)
    have hc_pos : 0 < c := by positivity
    let n : Point3 := c • w
    have hn_norm : ‖n‖ = 1 := by
      have h1 : ‖n‖ = |c| * ‖w‖ := by
        simpa [n] using norm_smul c w
      rw [h1, abs_of_pos hc_pos]
      have h2 : ‖w‖ = Real.sqrt ((v 0)^2 + (v 1)^2) := by
        have h21 : 0 ≤ ‖w‖ := by positivity
        have h22 : Real.sqrt (‖w‖ ^ 2) = ‖w‖ := by
          rw [Real.sqrt_sq h21]
        have h23 : Real.sqrt (‖w‖ ^ 2) = Real.sqrt ((v 0)^2 + (v 1)^2) := by
          rw [h_norm2]
        exact h22.symm.trans h23
      rw [h2]
      dsimp only [c]
      field_simp [Real.sqrt_pos.mpr h_pos2] <;> ring
    have hn_orth : inner ℝ v n = 0 := by
      rw [inner_smul_right, h_orth] <;> ring
    exact ⟨n, hn_norm, hn_orth⟩

/-- A concrete unit vector perpendicular to `v`. -/
private def perpendicularUnit (v : Point3) : Point3 :=
  if h : (v 0) = 0 ∧ (v 1) = 0 then
    EuclideanSpace.single 0 1
  else
    let w : Point3 := WithLp.toLp 2 (fun i =>
      match i with
      | 0 => -(v 1)
      | 1 => v 0
      | 2 => 0)
    let c : ℝ := 1 / Real.sqrt ((v 0)^2 + (v 1)^2)
    c • w

/-- `perpendicularUnit v` has norm 1. -/
private lemma perpendicularUnit_norm {v : Point3} (hv : ‖v‖ = 1) :
    ‖perpendicularUnit v‖ = 1 := by
  dsimp only [perpendicularUnit]
  by_cases h : (v 0) = 0 ∧ (v 1) = 0
  · rw [dif_pos h]
    rw [PiLp.norm_single] <;> norm_num
  · rw [dif_neg h]
    let w : Point3 := WithLp.toLp 2 (fun i =>
      match i with
      | 0 => -(v 1)
      | 1 => v 0
      | 2 => 0)
    have hwf : ∀ i, w i = (match i with
      | 0 => -(v 1)
      | 1 => v 0
      | 2 => 0) := by intro i; rfl
    have h_pos2 : 0 < (v 0)^2 + (v 1)^2 := by
      by_contra h3
      have h4 : (v 0)^2 + (v 1)^2 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
      have h5 : v 0 = 0 := by nlinarith
      have h6 : v 1 = 0 := by nlinarith
      exact h ⟨h5, h6⟩
    have h_norm2 : ‖w‖ ^ 2 = (v 0)^2 + (v 1)^2 := by
      have hsqrt : ‖w‖ = Real.sqrt (∑ i : Fin 3, ‖w i‖ ^ 2) := by
        rw [EuclideanSpace.norm_eq]
      have hsum : ∑ i : Fin 3, (w i)^2 = (v 0)^2 + (v 1)^2 := by
        simp [Fin.sum_univ_succ, hwf] <;> ring
      rw [hsqrt]
      have hsum' : ∑ i : Fin 3, ‖w i‖ ^ 2 = ∑ i : Fin 3, (w i)^2 := by
        apply Finset.sum_congr rfl; intro i _; simp
      rw [hsum', hsum]
      <;> rw [Real.sq_sqrt (by positivity)]
    let c : ℝ := 1 / Real.sqrt ((v 0)^2 + (v 1)^2)
    have hc_pos : 0 < c := by positivity
    have h1 : ‖c • w‖ = |c| * ‖w‖ := by simpa using norm_smul c w
    rw [h1, abs_of_pos hc_pos]
    have h2 : ‖w‖ = Real.sqrt ((v 0)^2 + (v 1)^2) := by
      have h21 : 0 ≤ ‖w‖ := by positivity
      have h22 : Real.sqrt (‖w‖ ^ 2) = ‖w‖ := by rw [Real.sqrt_sq h21]
      have h23 : Real.sqrt (‖w‖ ^ 2) = Real.sqrt ((v 0)^2 + (v 1)^2) := by rw [h_norm2]
      exact h22.symm.trans h23
    rw [h2]
    dsimp only [c]
    field_simp [Real.sqrt_pos.mpr h_pos2] <;> ring

/-- `perpendicularUnit v` is perpendicular to `v`. -/
private lemma perpendicularUnit_orth {v : Point3} (hv : ‖v‖ = 1) :
    inner ℝ v (perpendicularUnit v) = 0 := by
  dsimp only [perpendicularUnit]
  by_cases h : (v 0) = 0 ∧ (v 1) = 0
  · rw [dif_pos h]
    rw [EuclideanSpace.inner_single_right]
    simp [h.1]
  · rw [dif_neg h]
    let w : Point3 := WithLp.toLp 2 (fun i =>
      match i with
      | 0 => -(v 1)
      | 1 => v 0
      | 2 => 0)
    have hwf : ∀ i, w i = (match i with
      | 0 => -(v 1)
      | 1 => v 0
      | 2 => 0) := by intro i; rfl
    have h_orth : inner ℝ v w = 0 := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      have hstar : star (v : Fin 3 → ℝ) = (v : Fin 3 → ℝ) := by ext i; simp
      rw [hstar]
      simp [dotProduct, Fin.sum_univ_succ, hwf] <;> ring
    let c : ℝ := 1 / Real.sqrt ((v 0)^2 + (v 1)^2)
    rw [inner_smul_right, h_orth] <;> ring

/-- Lagrange identity for cross product in ℝ³. -/
private lemma lagrange_identity (u0 u1 u2 e0 e1 e2 : ℝ) :
    (u1 * e2 - u2 * e1)^2 + (u2 * e0 - u0 * e2)^2 + (u0 * e1 - u1 * e0)^2 =
    (u0^2 + u1^2 + u2^2) * (e0^2 + e1^2 + e2^2) - (u0 * e0 + u1 * e1 + u2 * e2)^2 := by
  ring

/-- Norm squared equals sum of component squares, proved abstractly. -/
private lemma norm_sq_components {x : Point3} (hx : ‖x‖ = 1) :
    (x 0)^2 + (x 1)^2 + (x 2)^2 = 1 := by
  have h1 : ‖x‖ ^ 2 = (x 0)^2 + (x 1)^2 + (x 2)^2 := norm3_sq x
  have h2 : ‖x‖ ^ 2 = 1 := by
    calc ‖x‖ ^ 2 = ‖x‖ * ‖x‖ := by ring
      _ = 1 * 1 := by rw [hx]
      _ = 1 := by ring
  linarith

/-- Cross product of `u` and `e1` has norm 1 when both are unit and orthogonal. -/
private lemma cross_product_norm (u0 u1 u2 e0 e1 e2 : ℝ)
    (hu_norm2 : u0^2 + u1^2 + u2^2 = 1)
    (he_norm2 : e0^2 + e1^2 + e2^2 = 1)
    (h_perp : u0*e0 + u1*e1 + u2*e2 = 0) :
    (u1*e2 - u2*e1)^2 + (u2*e0 - u0*e2)^2 + (u0*e1 - u1*e0)^2 = 1 := by
  have h_id := lagrange_identity u0 u1 u2 e0 e1 e2
  rw [h_id, hu_norm2, he_norm2, h_perp] <;> norm_num

/-- For unit vectors, `angle v u = Real.arccos (inner ℝ v u)`. -/
private lemma unit_angle_eq_arccos {v u : Point3} (hv : ‖v‖ = 1) (hu : ‖u‖ = 1) :
    angle v u = Real.arccos (inner ℝ v u) := by
  have h1 : Real.cos (angle v u) * (‖v‖ * ‖u‖) = inner ℝ v u :=
    cos_angle_mul_norm_mul_norm v u
  have h2 : Real.cos (angle v u) = inner ℝ v u := by
    rw [hv, hu] at h1
    <;> norm_num at h1 ⊢ <;> exact h1
  have h3 : 0 ≤ angle v u := angle_nonneg v u
  have h4 : angle v u ≤ Real.pi := angle_le_pi v u
  have h5 : Real.arccos (Real.cos (angle v u)) = angle v u := Real.arccos_cos h3 h4
  rw [h2] at h5
  exact h5.symm

/-- For unit vectors, `angle v w ≤ (π/2) * dist v w`. -/
private lemma angle_dist_bound {v w : Point3} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    angle v w ≤ (Real.pi / 2) * dist v w := by
  have h1 : inner ℝ v w = Real.cos (angle v w) := by
    have h2 : Real.cos (angle v w) * (‖v‖ * ‖w‖) = inner ℝ v w :=
      cos_angle_mul_norm_mul_norm v w
    rw [hv, hw] at h2
    have h3 : Real.cos (angle v w) * (1 * 1) = inner ℝ v w := h2
    simpa using h3.symm
  have h_ang_nonneg : 0 ≤ angle v w := angle_nonneg v w
  have h_ang_le_pi : angle v w ≤ Real.pi := angle_le_pi v w
  have h4 : ‖v - w‖ ^ 2 = 2 - 2 * Real.cos (angle v w) := by
    have h5 : ‖v - w‖ ^ 2 = ‖v‖ ^ 2 - 2 * inner ℝ v w + ‖w‖ ^ 2 := norm_sub_sq_real v w
    rw [h5, hv, hw, h1] <;> ring
  have h6 : Real.sin (angle v w / 2) ^ 2 = (1 - Real.cos (angle v w)) / 2 := by
    have h7 : Real.cos (2 * (angle v w / 2)) = 2 * Real.cos (angle v w / 2) ^ 2 - 1 :=
      Real.cos_two_mul (angle v w / 2)
    have h8 : 2 * (angle v w / 2) = angle v w := by ring
    rw [h8] at h7
    have h9 : Real.cos (angle v w / 2) ^ 2 = 1 - Real.sin (angle v w / 2) ^ 2 := by
      rw [Real.sin_sq] <;> ring
    rw [h9] at h7
    linarith
  have h_sin_nonneg : 0 ≤ Real.sin (angle v w / 2) := by
    have h9 : 0 ≤ angle v w / 2 := by linarith
    have h10 : angle v w / 2 ≤ Real.pi / 2 := by linarith [Real.pi_pos]
    exact Real.sin_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  have h7 : ‖v - w‖ = 2 * Real.sin (angle v w / 2) := by
    have h_pos : 0 ≤ ‖v - w‖ := by positivity
    have h_eq : ‖v - w‖ ^ 2 = (2 * Real.sin (angle v w / 2)) ^ 2 := by
      rw [h4]
      have h9 : (2 * Real.sin (angle v w / 2)) ^ 2 = 4 * Real.sin (angle v w / 2) ^ 2 := by ring
      rw [h9]
      linarith [h6]
    have h_nonneg : 0 ≤ 2 * Real.sin (angle v w / 2) := by positivity
    nlinarith
  have h8 : 0 ≤ angle v w / 2 := by linarith
  have h9 : angle v w / 2 ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have h10 : 2 / Real.pi * (angle v w / 2) ≤ Real.sin (angle v w / 2) :=
    Real.mul_le_sin h8 h9
  have h11 : dist v w = ‖v - w‖ := by rfl
  rw [h11, h7]
  have h12 : angle v w ≤ Real.pi * Real.sin (angle v w / 2) := by
    have h13 : 2 / Real.pi * (angle v w / 2) ≤ Real.sin (angle v w / 2) := h10
    have h14 : 0 < Real.pi := Real.pi_pos
    have h15 : angle v w ≤ Real.pi * Real.sin (angle v w / 2) := by
      calc angle v w
        = 2 * (angle v w / 2) := by ring
      _ = Real.pi * (2 / Real.pi * (angle v w / 2)) := by
        field_simp [h14.ne'] <;> ring
      _ ≤ Real.pi * Real.sin (angle v w / 2) := by gcongr
    exact h15
  have h16 : Real.pi * Real.sin (angle v w / 2) = (Real.pi / 2) * (2 * Real.sin (angle v w / 2)) := by ring
  rw [h16] at h12
  exact h12

/-- Grid packing: `ε`-separated points in `[-R,R]^2` have cardinality
at most `16 * (R/ε)^2` when `R ≥ ε`. -/
lemma grid_packing2d {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) (h_ratio : ε ≤ R)
    {s : Finset (ℝ × ℝ)}
    (h1 : ∀ p ∈ s, |p.1| ≤ R ∧ |p.2| ≤ R)
    (h2 : ∀ p ∈ s, ∀ q ∈ s, p ≠ q →
      ε^2 ≤ (p.1 - q.1)^2 + (p.2 - q.2)^2) :
    (s.card : ℝ) ≤ 16 * (R / ε)^2 := by
  let side : ℝ := ε / Real.sqrt 2
  have hside_pos : 0 < side := by positivity
  have hside_diam : side^2 + side^2 = ε^2 := by
    dsimp only [side]
    have hsq : (ε / Real.sqrt 2)^2 = ε^2 / 2 := by
      rw [div_pow]
      have h2 : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
      rw [h2] <;> ring
    rw [hsq] <;> ring
  let cellX (x : ℝ) : ℤ := Int.floor ((x + R) / side)
  let cellY (y : ℝ) : ℤ := Int.floor ((y + R) / side)
  let cell (p : ℝ × ℝ) : ℤ × ℤ := (cellX p.1, cellY p.2)
  have h_inj : Set.InjOn cell (s : Set (ℝ × ℝ)) := by
    intro p hp q hq h_eq
    by_contra hne
    have hcx : cellX p.1 = cellX q.1 := by
      have h : (cell p).1 = (cell q).1 := by rw [h_eq]
      exact h
    have hcy : cellY p.2 = cellY q.2 := by
      have h : (cell p).2 = (cell q).2 := by rw [h_eq]
      exact h
    have hdx : |p.1 - q.1| < side := by
      let x := (p.1 + R) / side
      let y := (q.1 + R) / side
      have hfx : Int.floor x = Int.floor y := hcx
      have h1 : (Int.floor x : ℝ) ≤ x := Int.floor_le x
      have h2 : x < (Int.floor x : ℝ) + 1 := Int.lt_floor_add_one x
      have h3 : (Int.floor x : ℝ) ≤ y := by
        have h3y : (Int.floor y : ℝ) ≤ y := Int.floor_le y
        rw [←hfx] at h3y
        exact h3y
      have h4 : y < (Int.floor x : ℝ) + 1 := by
        have h4y : y < (Int.floor y : ℝ) + 1 := Int.lt_floor_add_one y
        rw [←hfx] at h4y
        exact h4y
      have h5 : |x - y| < 1 := by
        have h6 : x - y < 1 := by linarith
        have h7 : y - x < 1 := by linarith
        exact abs_lt.mpr ⟨by linarith, by linarith⟩
      have h' : x - y = (p.1 - q.1) / side := by ring
      rw [h'] at h5
      have h_abs : |side| = side := abs_of_pos hside_pos
      have h9 : |(p.1 - q.1) / side| = |p.1 - q.1| / side := by
        rw [abs_div, h_abs]
      rw [h9] at h5
      have h'' : |p.1 - q.1| / side < 1 := h5
      calc |p.1 - q.1|
        = (|p.1 - q.1| / side) * side := by field_simp [hside_pos.ne']
      _ < 1 * side := by gcongr
      _ = side := by ring
    have hdy : |p.2 - q.2| < side := by
      let x := (p.2 + R) / side
      let y := (q.2 + R) / side
      have hfx : Int.floor x = Int.floor y := hcy
      have h1 : (Int.floor x : ℝ) ≤ x := Int.floor_le x
      have h2 : x < (Int.floor x : ℝ) + 1 := Int.lt_floor_add_one x
      have h3 : (Int.floor x : ℝ) ≤ y := by
        have h3y : (Int.floor y : ℝ) ≤ y := Int.floor_le y
        rw [←hfx] at h3y
        exact h3y
      have h4 : y < (Int.floor x : ℝ) + 1 := by
        have h4y : y < (Int.floor y : ℝ) + 1 := Int.lt_floor_add_one y
        rw [←hfx] at h4y
        exact h4y
      have h5 : |x - y| < 1 := by
        have h6 : x - y < 1 := by linarith
        have h7 : y - x < 1 := by linarith
        exact abs_lt.mpr ⟨by linarith, by linarith⟩
      have h' : x - y = (p.2 - q.2) / side := by ring
      rw [h'] at h5
      have h_abs : |side| = side := abs_of_pos hside_pos
      have h9 : |(p.2 - q.2) / side| = |p.2 - q.2| / side := by
        rw [abs_div, h_abs]
      rw [h9] at h5
      have h'' : |p.2 - q.2| / side < 1 := h5
      calc |p.2 - q.2|
        = (|p.2 - q.2| / side) * side := by field_simp [hside_pos.ne']
      _ < 1 * side := by gcongr
      _ = side := by ring
    have hsq1 : (p.1 - q.1)^2 < side^2 := by
      have h_abs2 : |p.1 - q.1|^2 < side^2 := by
        have h_a : 0 ≤ |p.1 - q.1| := by positivity
        nlinarith [hdx, hside_pos]
      have h_eq : (p.1 - q.1)^2 = |p.1 - q.1|^2 := by rw [sq_abs]
      rw [h_eq]
      exact h_abs2
    have hsq2 : (p.2 - q.2)^2 < side^2 := by
      have h_abs2 : |p.2 - q.2|^2 < side^2 := by
        have h_a : 0 ≤ |p.2 - q.2| := by positivity
        nlinarith [hdy, hside_pos]
      have h_eq : (p.2 - q.2)^2 = |p.2 - q.2|^2 := by rw [sq_abs]
      rw [h_eq]
      exact h_abs2
    have hsum : (p.1 - q.1)^2 + (p.2 - q.2)^2 < side^2 + side^2 := by linarith
    rw [hside_diam] at hsum
    have h4 := h2 p hp q hq hne
    linarith
  have h_sqrt2_num : 2 * Real.sqrt 2 + 1 ≤ 4 := by
    have h1 : Real.sqrt 2 ≤ 3 / 2 := by
      have h2 : (Real.sqrt 2)^2 ≤ (3 / 2 : ℝ)^2 := by
        rw [Real.sq_sqrt (by norm_num)] <;> norm_num
      have h3 : 0 ≤ Real.sqrt 2 := by positivity
      nlinarith
    nlinarith
  let Ncells_int : ℤ := Int.floor (2 * R / side) + 1
  have hN_pos : 0 < Ncells_int := by
    have h1 : 0 ≤ Int.floor (2 * R / side) := by
      apply Int.floor_nonneg.mpr
      positivity
    omega
  have hN_le : (Ncells_int : ℝ) ≤ 4 * R / ε := by
    have h1 : (Ncells_int : ℝ) = (Int.floor (2 * R / side) : ℝ) + 1 := by
      simp [Ncells_int]
    rw [h1]
    have h_eq_side : 2 * R / side = 2 * Real.sqrt 2 * R / ε := by
      dsimp only [side]
      field_simp
    have h_floor_eq : Int.floor (2 * R / side) = Int.floor (2 * Real.sqrt 2 * R / ε) := by
      rw [h_eq_side]
    rw [h_floor_eq]
    have h2 : (Int.floor (2 * Real.sqrt 2 * R / ε) : ℝ) ≤ 2 * Real.sqrt 2 * R / ε := Int.floor_le _
    have h4 : 1 ≤ R / ε := by
      have h5 : ε ≤ R := h_ratio
      have h6 : 0 < ε := hε
      calc (1 : ℝ)
        = ε / ε := by field_simp [h6.ne']
      _ ≤ R / ε := by gcongr
    have h3 : (2 * Real.sqrt 2 * R / ε) + 1 ≤ 4 * R / ε := by
      have h5 : (2 * Real.sqrt 2) * (R / ε) + 1 ≤ (2 * Real.sqrt 2) * (R / ε) + (R / ε) := by
        exact add_le_add_right h4 ((2 * Real.sqrt 2) * (R / ε))
      have h6 : (2 * Real.sqrt 2 + 1) * (R / ε) ≤ 4 * (R / ε) := by
        have h7 : 0 ≤ R / ε := by positivity
        nlinarith [h_sqrt2_num]
      calc (2 * Real.sqrt 2 * R / ε) + 1
        = (2 * Real.sqrt 2) * (R / ε) + 1 := by ring
      _ ≤ (2 * Real.sqrt 2) * (R / ε) + (R / ε) := h5
      _ = (2 * Real.sqrt 2 + 1) * (R / ε) := by ring
      _ ≤ 4 * (R / ε) := h6
      _ = 4 * R / ε := by ring
    have h_combined : (Int.floor (2 * Real.sqrt 2 * R / ε) : ℝ) + 1 ≤ (2 * Real.sqrt 2 * R / ε) + 1 := by
      gcongr
    exact h_combined.trans h3
  have h_bound : ∀ p ∈ s, (cell p).1 ∈ Finset.Ico 0 Ncells_int ∧
      (cell p).2 ∈ Finset.Ico 0 Ncells_int := by
    intro p hp
    have h9 : |p.1| ≤ R := (h1 p hp).1
    have h91 : -R ≤ p.1 := (abs_le.mp h9).1
    have h92 : p.1 ≤ R := (abs_le.mp h9).2
    have h101 : 0 ≤ p.1 + R := by linarith
    have h10 : 0 ≤ (p.1 + R) / side := by exact div_nonneg h101 hside_pos.le
    have h11 : (p.1 + R) / side ≤ 2 * R / side := by
      have h12 : p.1 + R ≤ 2 * R := by linarith
      gcongr
    have h13 : 0 ≤ cellX p.1 := Int.floor_nonneg.mpr h10
    have h14 : cellX p.1 ≤ Int.floor (2 * R / side) := Int.floor_mono h11
    have h16 : cellX p.1 < Ncells_int := by
      have h17 : cellX p.1 ≤ Int.floor (2 * R / side) := h14
      have h18 : (Int.floor (2 * R / side) : ℤ) < Ncells_int := by
        simp [Ncells_int] <;> omega
      exact lt_of_le_of_lt h17 h18
    have h17 : cellX p.1 ∈ Finset.Ico 0 Ncells_int := by
      simp only [Finset.mem_Ico]
      exact ⟨h13, h16⟩
    have h9' : |p.2| ≤ R := (h1 p hp).2
    have h91' : -R ≤ p.2 := (abs_le.mp h9').1
    have h92' : p.2 ≤ R := (abs_le.mp h9').2
    have h101' : 0 ≤ p.2 + R := by linarith
    have h10' : 0 ≤ (p.2 + R) / side := by exact div_nonneg h101' hside_pos.le
    have h11' : (p.2 + R) / side ≤ 2 * R / side := by
      have h12 : p.2 + R ≤ 2 * R := by linarith
      gcongr
    have h13' : 0 ≤ cellY p.2 := Int.floor_nonneg.mpr h10'
    have h14' : cellY p.2 ≤ Int.floor (2 * R / side) := Int.floor_mono h11'
    have h16' : cellY p.2 < Ncells_int := by
      have h17' : cellY p.2 ≤ Int.floor (2 * R / side) := h14'
      have h18' : (Int.floor (2 * R / side) : ℤ) < Ncells_int := by
        simp [Ncells_int] <;> omega
      exact lt_of_le_of_lt h17' h18'
    have h17' : cellY p.2 ∈ Finset.Ico 0 Ncells_int := by
      simp only [Finset.mem_Ico]
      exact ⟨h13', h16'⟩
    exact ⟨h17, h17'⟩
  have h_image : Finset.image cell s ⊆ (Finset.Ico 0 Ncells_int) ×ˢ (Finset.Ico 0 Ncells_int) := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨p, hp, rfl⟩
    exact Finset.mem_product.mpr (h_bound p hp)
  have h_card : s.card = (Finset.image cell s).card := by
    rw [Finset.card_image_of_injOn h_inj]
  have h5 : s.card ≤
      ((Finset.Ico 0 Ncells_int) ×ˢ (Finset.Ico 0 Ncells_int)).card := by
    rw [h_card]
    exact Finset.card_le_card h_image
  have h_card_ico : (Finset.Ico 0 Ncells_int).card = Ncells_int.natAbs := by
    simp [hN_pos] <;> omega
  have h6 : ((Finset.Ico 0 Ncells_int) ×ˢ (Finset.Ico 0 Ncells_int)).card =
      Ncells_int.natAbs ^ 2 := by
    have h61 := Finset.card_product (Finset.Ico 0 Ncells_int) (Finset.Ico 0 Ncells_int)
    have h62 : (Finset.Ico 0 Ncells_int).card = Ncells_int.natAbs := h_card_ico
    calc ((Finset.Ico 0 Ncells_int) ×ˢ (Finset.Ico 0 Ncells_int)).card
      = (Finset.Ico 0 Ncells_int).card * (Finset.Ico 0 Ncells_int).card := h61
    _ = Ncells_int.natAbs * Ncells_int.natAbs := by
      exact congr_arg₂ (· * ·) h62 h62
    _ = Ncells_int.natAbs ^ 2 := by ring
  rw [h6] at h5
  have h7 : (Ncells_int.natAbs : ℝ) ≤ 4 * R / ε := by
    have hN_nonneg : 0 ≤ Ncells_int := by linarith
    have h1 : (Ncells_int.natAbs : ℤ) = Ncells_int := by omega
    have h2 : (Ncells_int.natAbs : ℝ) = (Ncells_int : ℝ) := by
      have h3 : ((Ncells_int.natAbs : ℤ) : ℝ) = (Ncells_int : ℝ) := by
        rw [h1] <;> rfl
      simpa using h3
    rw [h2]
    exact hN_le
  have h9 : (s.card : ℝ) ≤ (Ncells_int.natAbs : ℝ)^2 := by exact_mod_cast h5
  have h10 : 0 ≤ (Ncells_int.natAbs : ℝ) := by positivity
  calc (s.card : ℝ)
    ≤ (Ncells_int.natAbs : ℝ)^2 := h9
  _ ≤ (4 * R / ε)^2 := by nlinarith
  _ = 16 * (R / ε)^2 := by ring

/-! ### Same-side direction packing -/

/-- Projection separation: projected points are separated by at least `ε/√3`. -/
private lemma projection_separation {δ theta : ℝ}
    (hδ : 0 < δ) (htheta : δ ≤ theta) (htheta_half : theta ≤ 1 / 2)
    {S : Finset Point3}
    (hs1 : ∀ v ∈ S, ‖v‖ = 1)
    (hs2 : ∀ v ∈ S, ∀ w ∈ S, v ≠ w → (2 * δ / Real.pi) ≤ dist v w)
    (u : Point3) (hu : ‖u‖ = 1)
    (h_angle_le : ∀ v ∈ S, Real.arccos (inner ℝ v u) ≤ theta) :
    ∀ v ∈ S, ∀ w ∈ S, v ≠ w →
      (2 * δ / Real.pi)^2 / 3 ≤
      ‖(v - inner ℝ v u • u) - (w - inner ℝ w u • u)‖ ^ 2 := by
  set ε : ℝ := 2 * δ / Real.pi with hε_def
  have hε_pos : 0 < ε := by positivity
  have h_pi2 : Real.pi ^ 2 / 16 ≤ 2 / 3 := by
    have h1 : Real.pi < (3.15 : ℝ) := Real.pi_lt_d2
    have h2 : 0 < Real.pi := Real.pi_pos
    have h3 : Real.pi ^ 2 < (3.15 : ℝ)^2 := by nlinarith
    have h4 : (3.15 : ℝ)^2 = 9.9225 := by norm_num
    rw [h4] at h3
    nlinarith
  intro v hv w hw hne
  set a : ℝ := Real.arccos (inner ℝ v u) with ha_def
  set b : ℝ := Real.arccos (inner ℝ w u) with hb_def
  have ha_le : a ≤ theta := h_angle_le v hv
  have hb_le : b ≤ theta := h_angle_le w hw
  have ha_nonneg : 0 ≤ a := Real.arccos_nonneg _
  have hb_nonneg : 0 ≤ b := Real.arccos_nonneg _
  have h_a_eq_angle : a = angle v u := (unit_angle_eq_arccos (hs1 v hv) hu).symm
  have h_b_eq_angle : b = angle w u := (unit_angle_eq_arccos (hs1 w hw) hu).symm
  have h_tri : |a - b| ≤ angle v w := by
    have h1 : angle v u ≤ angle v w + angle w u := angle_le_angle_add_angle v w u
    have h21 : angle w u ≤ angle w v + angle v u := angle_le_angle_add_angle w v u
    have h22 : angle w v = angle v w := angle_comm w v
    rw [h22] at h21
    rw [h_a_eq_angle, h_b_eq_angle]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have h_bounds_v : -1 ≤ inner ℝ v u ∧ inner ℝ v u ≤ 1 := by
    have h : |inner ℝ v u| ≤ ‖v‖ * ‖u‖ := abs_real_inner_le_norm v u
    rw [hs1 v hv, hu] at h
    exact ⟨by linarith [abs_le.mp h], by linarith [abs_le.mp h]⟩
  have h_bounds_w : -1 ≤ inner ℝ w u ∧ inner ℝ w u ≤ 1 := by
    have h : |inner ℝ w u| ≤ ‖w‖ * ‖u‖ := abs_real_inner_le_norm w u
    rw [hs1 w hw, hu] at h
    exact ⟨by linarith [abs_le.mp h], by linarith [abs_le.mp h]⟩
  have hcv : inner ℝ v u = Real.cos a := by rw [Real.cos_arccos h_bounds_v.1 h_bounds_v.2]
  have hcw : inner ℝ w u = Real.cos b := by rw [Real.cos_arccos h_bounds_w.1 h_bounds_w.2]
  have h_cos_diff1 : |Real.cos a - Real.cos b| ≤ theta * |a - b| := by
    have h_eq : Real.cos a - Real.cos b =
        -2 * Real.sin ((a + b) / 2) * Real.sin ((a - b) / 2) := Real.cos_sub_cos a b
    have h_abs : |Real.cos a - Real.cos b| =
        2 * |Real.sin ((a + b) / 2)| * |Real.sin ((a - b) / 2)| := by
      rw [h_eq]
      have h1 : |(-2 : ℝ) * Real.sin ((a + b) / 2) * Real.sin ((a - b) / 2)| =
          2 * |Real.sin ((a + b) / 2)| * |Real.sin ((a - b) / 2)| := by
        rw [abs_mul, abs_mul] <;> ring
      rw [h1]
    rw [h_abs]
    have h2 : 0 ≤ (a + b) / 2 := by linarith
    have h3 : (a + b) / 2 ≤ theta := by linarith
    have htheta_pi2 : theta ≤ Real.pi / 2 := by
      have h4 : theta ≤ 1 / 2 := htheta_half
      have h5 : (1 / 2 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
      linarith
    have h4' : 0 ≤ Real.sin ((a + b) / 2) := Real.sin_nonneg_of_mem_Icc ⟨h2, by linarith [Real.pi_gt_three]⟩
    have h5' : Real.sin ((a + b) / 2) ≤ Real.sin theta :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) htheta_pi2 h3
    have h6 : |Real.sin ((a + b) / 2)| ≤ Real.sin theta := by
      rw [abs_of_nonneg h4'] <;> exact h5'
    have h7 : |Real.sin ((a - b) / 2)| ≤ |a - b| / 2 := by
      have h8 : |Real.sin ((a - b) / 2)| ≤ |(a - b) / 2| := Real.abs_sin_le_abs
      have h9 : |(a - b) / 2| = |a - b| / 2 := by
        rw [abs_div, abs_of_pos (show (0 : ℝ) < 2 by norm_num)] <;> ring
      rw [h9] at h8
      exact h8
    calc 2 * |Real.sin ((a + b) / 2)| * |Real.sin ((a - b) / 2)|
      ≤ 2 * Real.sin theta * (|a - b| / 2) := by gcongr <;> linarith
    _ = Real.sin theta * |a - b| := by ring
    _ ≤ theta * |a - b| := by
      have h10 : Real.sin theta ≤ theta := Real.sin_le (by linarith)
      have h11 : 0 ≤ |a - b| := by positivity
      nlinarith
  have h_angle_dist : angle v w ≤ (Real.pi / 2) * dist v w :=
    angle_dist_bound (hs1 v hv) (hs1 w hw)
  have h_cos_diff2 : |inner ℝ v u - inner ℝ w u| ≤ theta * (Real.pi / 2) * dist v w := by
    rw [hcv, hcw]
    have h12 : 0 ≤ theta := by linarith
    calc |Real.cos a - Real.cos b|
      ≤ theta * |a - b| := h_cos_diff1
    _ ≤ theta * (angle v w) := by exact mul_le_mul_of_nonneg_left h_tri h12
    _ ≤ theta * ((Real.pi / 2) * dist v w) := by exact mul_le_mul_of_nonneg_left h_angle_dist h12
    _ = theta * (Real.pi / 2) * dist v w := by ring
  have h_main : ‖(v - inner ℝ v u • u) - (w - inner ℝ w u • u)‖ ^ 2 =
      ‖v - w‖ ^ 2 - (inner ℝ v u - inner ℝ w u) ^ 2 := by
    have h2 : (v - inner ℝ v u • u) - (w - inner ℝ w u • u) =
        (v - w) - (inner ℝ v u - inner ℝ w u) • u := by
      have h21 : (v - inner ℝ v u • u) - (w - inner ℝ w u • u) =
          (v - w) - (inner ℝ v u • u - inner ℝ w u • u) := by abel
      rw [h21]
      have h22 : inner ℝ v u • u - inner ℝ w u • u = (inner ℝ v u - inner ℝ w u) • u := by
        rw [← sub_smul]
      rw [h22]
    rw [h2]
    have h3 : ‖(v - w) - (inner ℝ v u - inner ℝ w u) • u‖ ^ 2 =
        ‖v - w‖ ^ 2 - 2 * inner ℝ (v - w) ((inner ℝ v u - inner ℝ w u) • u) +
        ‖(inner ℝ v u - inner ℝ w u) • u‖ ^ 2 :=
      norm_sub_sq_real (v - w) ((inner ℝ v u - inner ℝ w u) • u)
    rw [h3]
    have h4 : inner ℝ (v - w) ((inner ℝ v u - inner ℝ w u) • u) =
        (inner ℝ v u - inner ℝ w u) ^ 2 := by
      rw [inner_smul_right, inner_sub_left] <;> ring
    have h5 : ‖(inner ℝ v u - inner ℝ w u) • u‖ ^ 2 =
        (inner ℝ v u - inner ℝ w u) ^ 2 := by
      have h51 : ‖(inner ℝ v u - inner ℝ w u) • u‖ = |inner ℝ v u - inner ℝ w u| := by
        calc ‖(inner ℝ v u - inner ℝ w u) • u‖
          = |inner ℝ v u - inner ℝ w u| * ‖u‖ := norm_smul _ _
        _ = |inner ℝ v u - inner ℝ w u| * 1 := by rw [hu]
        _ = |inner ℝ v u - inner ℝ w u| := by ring
      rw [h51, sq_abs]
    rw [h4, h5] <;> ring
  rw [h_main]
  have htheta_pos : 0 < theta := by linarith [hδ, htheta]
  have h10 : 0 ≤ theta * (Real.pi / 2) * dist v w := by positivity
  have h11 : |inner ℝ v u - inner ℝ w u| ≤ |theta * (Real.pi / 2) * dist v w| := by
    rw [abs_of_nonneg h10] <;> exact h_cos_diff2
  have h9 : (inner ℝ v u - inner ℝ w u) ^ 2 ≤ (theta * (Real.pi / 2) * dist v w) ^ 2 :=
    sq_le_sq.mpr h11
  have h12 : (theta * (Real.pi / 2)) ^ 2 ≤ Real.pi ^ 2 / 16 := by
    have h13 : theta ≤ 1 / 2 := htheta_half
    have h14 : 0 ≤ theta := by linarith
    have h15 : theta * (Real.pi / 2) ≤ Real.pi / 4 := by
      calc theta * (Real.pi / 2)
        ≤ (1 / 2 : ℝ) * (Real.pi / 2) := by gcongr
      _ = Real.pi / 4 := by ring
    have h16 : 0 ≤ theta * (Real.pi / 2) := by positivity
    have h17 : (theta * (Real.pi / 2)) ^ 2 ≤ (Real.pi / 4) ^ 2 := by nlinarith
    have h18 : (Real.pi / 4) ^ 2 = Real.pi ^ 2 / 16 := by ring
    rw [h18] at h17
    exact h17
  have h14 : ‖v - w‖ = dist v w := by rfl
  have h15 : (inner ℝ v u - inner ℝ w u) ^ 2 ≤ (Real.pi ^ 2 / 16) * ‖v - w‖ ^ 2 := by
    have h9' : (inner ℝ v u - inner ℝ w u) ^ 2 ≤ (theta * (Real.pi / 2)) ^ 2 * (dist v w) ^ 2 := by
      have h : (theta * (Real.pi / 2) * dist v w) ^ 2 =
          (theta * (Real.pi / 2)) ^ 2 * (dist v w) ^ 2 := by ring
      rw [h] at h9
      exact h9
    have h14' : (dist v w) ^ 2 = ‖v - w‖ ^ 2 := by rw [h14] <;> ring
    calc (inner ℝ v u - inner ℝ w u) ^ 2
      ≤ (theta * (Real.pi / 2)) ^ 2 * (dist v w) ^ 2 := h9'
    _ ≤ (Real.pi ^ 2 / 16) * (dist v w) ^ 2 := by gcongr
    _ = (Real.pi ^ 2 / 16) * ‖v - w‖ ^ 2 := by rw [h14']
  have h16 : ‖v - w‖ ^ 2 - (inner ℝ v u - inner ℝ w u) ^ 2 ≥
      (1 - Real.pi ^ 2 / 16) * ‖v - w‖ ^ 2 := by
    have h_nonneg : 0 ≤ ‖v - w‖ ^ 2 := by positivity
    linarith [h15]
  have h17 : (1 - Real.pi ^ 2 / 16) ≥ (1 / 3 : ℝ) := by
    have h18 : Real.pi ^ 2 / 16 ≤ 2 / 3 := h_pi2
    linarith
  have h19 : ε ≤ ‖v - w‖ := by
    have h20 : ε ≤ dist v w := hs2 v hv w hw hne
    have h21 : dist v w = ‖v - w‖ := by rfl
    rw [h21] at h20
    exact h20
  have h22 : 0 ≤ ‖v - w‖ ^ 2 := by positivity
  have h23 : (1 - Real.pi ^ 2 / 16) * ‖v - w‖ ^ 2 ≥ (1 / 3 : ℝ) * ‖v - w‖ ^ 2 := by
    exact mul_le_mul_of_nonneg_right h17 h22
  have h25 : (1 / 3 : ℝ) * ‖v - w‖ ^ 2 ≥ (1 / 3 : ℝ) * ε ^ 2 := by
    have h26 : 0 ≤ ε := by positivity
    have h27 : ε ≤ ‖v - w‖ := h19
    have h28 : |ε| ≤ |‖v - w‖| := by
      rw [abs_of_nonneg h26, abs_of_nonneg (by positivity)]
      exact h27
    have h29 : ε ^ 2 ≤ ‖v - w‖ ^ 2 := sq_le_sq.mpr h28
    have h30 : (1 / 3 : ℝ) ≥ 0 := by norm_num
    exact mul_le_mul_of_nonneg_left h29 h30
  have h27 : ‖v - w‖ ^ 2 - (inner ℝ v u - inner ℝ w u) ^ 2 ≥ (1 / 3 : ℝ) * ε ^ 2 := by
    calc ‖v - w‖ ^ 2 - (inner ℝ v u - inner ℝ w u) ^ 2
      ≥ (1 - Real.pi ^ 2 / 16) * ‖v - w‖ ^ 2 := h16
    _ ≥ (1 / 3 : ℝ) * ‖v - w‖ ^ 2 := h23
    _ ≥ (1 / 3 : ℝ) * ε ^ 2 := h25
  have h_goal : ε ^ 2 / 3 ≤ ‖v - w‖ ^ 2 - (inner ℝ v u - inner ℝ w u) ^ 2 := by
    have h_eq : (1 / 3 : ℝ) * ε ^ 2 = ε ^ 2 / 3 := by ring
    rw [h_eq] at h27
    exact h27
  exact h_goal

/-- Direction packing for vectors all with `0 ≤ inner v u`. -/
lemma same_side_direction_packing {δ theta : ℝ}
    (hδ : 0 < δ) (htheta : δ ≤ theta) (htheta_half : theta ≤ 1 / 2)
    {S : Finset Point3}
    (hs1 : ∀ v ∈ S, ‖v‖ = 1)
    (hs2 : ∀ v ∈ S, ∀ w ∈ S, v ≠ w → (2 * δ / Real.pi) ≤ dist v w)
    (u : Point3) (hu : ‖u‖ = 1)
    (h_side : ∀ v ∈ S, 0 ≤ inner ℝ v u)
    (hcap : ∀ v ∈ S, hairbrushAcuteDirectionAngle v u ≤ theta) :
    (S.card : ℝ) ≤ 16 * (theta / ((2 * δ / Real.pi) / Real.sqrt 3))^2 := by
  set ε : ℝ := 2 * δ / Real.pi with hε_def
  have hε_pos : 0 < ε := by positivity
  let p : Point3 → Point3 := fun v => v - inner ℝ v u • u

  have h_angle_le : ∀ v ∈ S, Real.arccos (inner ℝ v u) ≤ theta := by
    intro v hv
    have h_nonneg : 0 ≤ inner ℝ v u := h_side v hv
    have h_arccos_le_pi2 : Real.arccos (inner ℝ v u) ≤ Real.pi / 2 :=
      Real.arccos_le_pi_div_two.mpr h_nonneg
    have h_min : min (Real.arccos (inner ℝ v u)) (Real.pi - Real.arccos (inner ℝ v u)) =
        Real.arccos (inner ℝ v u) := by
      rw [min_eq_left] <;> linarith
    have h10 : hairbrushAcuteDirectionAngle v u ≤ theta := hcap v hv
    have h11 : hairbrushAcuteDirectionAngle v u =
        min (Real.arccos (inner ℝ v u)) (Real.pi - Real.arccos (inner ℝ v u)) := by rfl
    rw [h11] at h10
    rw [h_min] at h10
    exact h10

  have h_p_norm : ∀ v ∈ S, ‖p v‖ ≤ theta := by
    intro v hv
    set a : ℝ := Real.arccos (inner ℝ v u) with ha_def
    have ha_le : a ≤ theta := h_angle_le v hv
    have ha_nonneg : 0 ≤ a := Real.arccos_nonneg _
    have h_bounds : -1 ≤ inner ℝ v u ∧ inner ℝ v u ≤ 1 := by
      have h : |inner ℝ v u| ≤ ‖v‖ * ‖u‖ := abs_real_inner_le_norm v u
      rw [hs1 v hv, hu] at h
      exact ⟨by linarith [abs_le.mp h], by linarith [abs_le.mp h]⟩
    have h_inner : inner ℝ v u = Real.cos a := by
      rw [Real.cos_arccos h_bounds.1 h_bounds.2]
    have h1 : ‖p v‖ ^ 2 = 1 - (inner ℝ v u) ^ 2 := by
      have h2 : ‖p v‖ ^ 2 = ‖v - inner ℝ v u • u‖ ^ 2 := by rfl
      rw [h2]
      have h3 : ‖v - inner ℝ v u • u‖ ^ 2 =
          ‖v‖ ^ 2 - 2 * inner ℝ v (inner ℝ v u • u) + ‖inner ℝ v u • u‖ ^ 2 :=
        norm_sub_sq_real v (inner ℝ v u • u)
      rw [h3]
      have h4 : inner ℝ v (inner ℝ v u • u) = (inner ℝ v u) ^ 2 := by
        rw [inner_smul_right] <;> ring
      have h5 : ‖inner ℝ v u • u‖ ^ 2 = (inner ℝ v u) ^ 2 := by
        have h51 : ‖inner ℝ v u • u‖ = |inner ℝ v u| := by
          calc ‖inner ℝ v u • u‖
            = |inner ℝ v u| * ‖u‖ := norm_smul _ _
          _ = |inner ℝ v u| * 1 := by rw [hu]
          _ = |inner ℝ v u| := by ring
        rw [h51, sq_abs]
      rw [h4, h5, hs1 v hv] <;> ring
    have h_norm2_le : ‖p v‖ ^ 2 ≤ theta ^ 2 := by
      rw [h1, h_inner]
      have h5 : 1 - Real.cos a ^ 2 = Real.sin a ^ 2 := by
        rw [Real.sin_sq] <;> ring
      rw [h5]
      have ha_le_pi : a ≤ Real.pi := by
        have h1 : a ≤ theta := ha_le
        have h2 : theta ≤ 1 / 2 := htheta_half
        have h3 : (1 / 2 : ℝ) < Real.pi := by linarith [Real.pi_gt_three]
        linarith
      have h6 : 0 ≤ Real.sin a := Real.sin_nonneg_of_mem_Icc ⟨ha_nonneg, ha_le_pi⟩
      have h7 : Real.sin a ≤ a := Real.sin_le ha_nonneg
      nlinarith [ha_le]
    have h_pos : 0 ≤ ‖p v‖ := by positivity
    have h_theta_pos : 0 ≤ theta := by linarith
    nlinarith

  have h_proj_sep : ∀ v ∈ S, ∀ w ∈ S, v ≠ w →
      ε^2 / 3 ≤ ‖p v - p w‖ ^ 2 :=
    projection_separation hδ htheta htheta_half hs1 hs2 u hu h_angle_le

  -- Get e1 as a fresh variable to avoid unfolding perpendicularUnit
  have h_e1_exists : ∃ (e1 : Point3), ‖e1‖ = 1 ∧ inner ℝ u e1 = 0 :=
    ⟨perpendicularUnit u, perpendicularUnit_norm hu, perpendicularUnit_orth hu⟩
  rcases h_e1_exists with ⟨e1, he1_norm, he1_perp⟩
  have h_u_norm2 : (u 0)^2 + (u 1)^2 + (u 2)^2 = 1 := norm_sq_components hu
  have h_e1_norm2 : (e1 0)^2 + (e1 1)^2 + (e1 2)^2 = 1 := norm_sq_components he1_norm
  have h_perp : u 0 * e1 0 + u 1 * e1 1 + u 2 * e1 2 = 0 := by
    have h : inner ℝ u e1 = u 0 * e1 0 + u 1 * e1 1 + u 2 * e1 2 := inner3 u e1
    rw [h] at he1_perp
    exact he1_perp
  let c0 := u 1 * e1 2 - u 2 * e1 1
  let c1 := u 2 * e1 0 - u 0 * e1 2
  let c2 := u 0 * e1 1 - u 1 * e1 0
  have h_norm_sq : c0^2 + c1^2 + c2^2 = 1 :=
    cross_product_norm (u 0) (u 1) (u 2) (e1 0) (e1 1) (e1 2) h_u_norm2 h_e1_norm2 h_perp
  let f2 : Fin 3 → ℝ := fun i =>
    match i with
    | 0 => c0
    | 1 => c1
    | 2 => c2
  let e2 : Point3 := WithLp.toLp 2 f2
  have h_e20 : e2 0 = c0 := by rfl
  have h_e21 : e2 1 = c1 := by rfl
  have h_e22 : e2 2 = c2 := by rfl
  have he2_norm : ‖e2‖ = 1 := by
    have h1 : ‖e2‖ ^ 2 = (e2 0)^2 + (e2 1)^2 + (e2 2)^2 := norm3_sq e2
    have h2 : (e2 0)^2 + (e2 1)^2 + (e2 2)^2 = c0^2 + c1^2 + c2^2 := by
      rw [h_e20, h_e21, h_e22] <;> ring
    have h3 : ‖e2‖ ^ 2 = 1 := by rw [h1, h2, h_norm_sq]
    have h_pos : 0 ≤ ‖e2‖ := by positivity
    nlinarith
  have he2_perp_u : inner ℝ e2 u = 0 := by
    have h : inner ℝ e2 u = e2 0 * u 0 + e2 1 * u 1 + e2 2 * u 2 := inner3 e2 u
    rw [h, h_e20, h_e21, h_e22] <;> ring
  have he2_perp_e1 : inner ℝ e2 e1 = 0 := by
    have h : inner ℝ e2 e1 = e2 0 * e1 0 + e2 1 * e1 1 + e2 2 * e1 2 := inner3 e2 e1
    rw [h, h_e20, h_e21, h_e22] <;> ring
  let b : Fin 3 → Point3 := fun i =>
    match i with
    | 0 => e1
    | 1 => e2
    | 2 => u
  have hb0 : b 0 = e1 := by rfl
  have hb1 : b 1 = e2 := by rfl
  have hb2 : b 2 = u := by rfl
  have h_inner_comm : ∀ (x y : Point3), inner ℝ x y = inner ℝ y x := by
    intro x y
    rw [inner3 x y, inner3 y x] <;> ring
  have he1_perp' : inner ℝ e1 e2 = 0 := by
    rw [h_inner_comm e1 e2, he2_perp_e1]
  have hu_perp_e2 : inner ℝ u e2 = 0 := by
    rw [h_inner_comm u e2, he2_perp_u]
  have he1_perp'' : inner ℝ e1 u = 0 := by
    rw [h_inner_comm e1 u, he1_perp]
  have h_orthonormal : Orthonormal ℝ b := by
    refine' ⟨_, _⟩
    · intro i
      fin_cases i <;> simp [hb0, hb1, hb2, he1_norm, he2_norm, hu]
    · intro i j hne
      fin_cases i <;> fin_cases j <;> (try { contradiction }) <;>
        simp [hb0, hb1, hb2, he1_perp, he2_perp_u, he2_perp_e1, he1_perp', hu_perp_e2, he1_perp''] <;> tauto
  have h_li : LinearIndependent ℝ b := h_orthonormal.linearIndependent
  have h1 : Fintype.card (Fin 3) ≤ Module.finrank ℝ (Submodule.span ℝ (Set.range b)) :=
    (linearIndependent_iff_card_le_finrank_span.mp h_li)
  have h2 : Module.finrank ℝ (Submodule.span ℝ (Set.range b)) ≤ Module.finrank ℝ Point3 :=
    Submodule.finrank_le _
  have h_finrank3 : Module.finrank ℝ Point3 = 3 := by simp
  have h3 : Module.finrank ℝ (Submodule.span ℝ (Set.range b)) = 3 := by
    rw [h_finrank3] at h2
    simp at h1 h2 ⊢ <;> omega
  have h3' : Module.finrank ℝ (Submodule.span ℝ (Set.range b)) = Module.finrank ℝ Point3 := by
    rw [h3, h_finrank3]
  have h_span : Submodule.span ℝ (Set.range b) = ⊤ :=
    Submodule.eq_top_of_finrank_eq h3'
  let ob : OrthonormalBasis (Fin 3) ℝ Point3 :=
    OrthonormalBasis.mk h_orthonormal (by rw [h_span])
  have h_norm_decomp : ∀ (x : Point3), ‖x‖ ^ 2 =
      (inner ℝ x e1)^2 + (inner ℝ x e2)^2 + (inner ℝ x u)^2 := by
    intro x
    have h_sum : ∑ i : Fin 3, ‖inner ℝ (ob i) x‖ ^ 2 = ‖x‖ ^ 2 :=
      ob.sum_sq_norm_inner_right x
    have h_norm_sq_real : ∀ (r : ℝ), ‖r‖ ^ 2 = r ^ 2 := by
      intro r; simp [sq_abs]
    have h_expand : ∑ i : Fin 3, ‖inner ℝ (ob i) x‖ ^ 2 =
        (inner ℝ (ob 0) x)^2 + (inner ℝ (ob 1) x)^2 + (inner ℝ (ob 2) x)^2 := by
      simp [Fin.sum_univ_succ, h_norm_sq_real] <;> ring
    rw [h_expand] at h_sum
    have h_ob_coe : ⇑ob = b := OrthonormalBasis.coe_mk h_orthonormal _
    have h_coe0 : ob 0 = e1 := by rw [h_ob_coe, hb0]
    have h_coe1 : ob 1 = e2 := by rw [h_ob_coe, hb1]
    have h_coe2 : ob 2 = u := by rw [h_ob_coe, hb2]
    have h_eq1 : inner ℝ (ob 0) x = inner ℝ x e1 := by rw [h_coe0, h_inner_comm]
    have h_eq2 : inner ℝ (ob 1) x = inner ℝ x e2 := by rw [h_coe1, h_inner_comm]
    have h_eq3 : inner ℝ (ob 2) x = inner ℝ x u := by rw [h_coe2, h_inner_comm]
    rw [h_eq1, h_eq2, h_eq3] at h_sum
    exact h_sum.symm
  have h_eq_of_inner : ∀ (x y : Point3),
      inner ℝ x e1 = inner ℝ y e1 →
      inner ℝ x e2 = inner ℝ y e2 →
      inner ℝ x u = inner ℝ y u → x = y := by
    intro x y h1 h2 h3
    set z : Point3 := x - y with hz_def
    have hz1 : inner ℝ z e1 = 0 := by
      rw [show inner ℝ z e1 = inner ℝ x e1 - inner ℝ y e1 by
        simp [hz_def, inner_sub_left]] <;> rw [h1] <;> ring
    have hz2 : inner ℝ z e2 = 0 := by
      rw [show inner ℝ z e2 = inner ℝ x e2 - inner ℝ y e2 by
        simp [hz_def, inner_sub_left]] <;> rw [h2] <;> ring
    have hz3 : inner ℝ z u = 0 := by
      rw [show inner ℝ z u = inner ℝ x u - inner ℝ y u by
        simp [hz_def, inner_sub_left]] <;> rw [h3] <;> ring
    have h4 : ‖z‖ ^ 2 = 0 := by
      have h5 := h_norm_decomp z
      rw [h5, hz1, hz2, hz3] <;> ring
    have h6 : ‖z‖ = 0 := sq_eq_zero_iff.mp h4
    have h7 : z = 0 := norm_eq_zero.mp h6
    exact sub_eq_zero.mp h7

  have h_p_perp : ∀ (x : Point3), inner ℝ (p x) u = 0 := by
    intro x
    have h1 : inner ℝ (p x) u = inner ℝ x u - inner ℝ ((inner ℝ x u) • u) u := by
      rw [inner_sub_left] <;> rfl
    have h2 : inner ℝ ((inner ℝ x u) • u) u = (inner ℝ x u) * inner ℝ u u := by
      rw [inner_smul_left] <;> rfl
    have h3 : inner ℝ u u = 1 := by
      have h4 : inner ℝ u u = ‖u‖ ^ 2 := real_inner_self_eq_norm_sq u
      rw [h4, hu] <;> norm_num
    rw [h1, h2, h3] <;> ring
  let coord : Point3 → ℝ × ℝ := fun x => (inner ℝ x e1, inner ℝ x e2)
  have h_coord_bound : ∀ v ∈ S, |(coord (p v)).1| ≤ theta ∧ |(coord (p v)).2| ≤ theta := by
    intro v hv
    have h1 : |inner ℝ (p v) e1| ≤ ‖p v‖ := by
      calc |inner ℝ (p v) e1|
        ≤ ‖p v‖ * ‖e1‖ := abs_real_inner_le_norm (p v) e1
      _ = ‖p v‖ := by rw [he1_norm] <;> ring
    have h2 : |inner ℝ (p v) e2| ≤ ‖p v‖ := by
      calc |inner ℝ (p v) e2|
        ≤ ‖p v‖ * ‖e2‖ := abs_real_inner_le_norm (p v) e2
      _ = ‖p v‖ := by rw [he2_norm] <;> ring
    have h3 : ‖p v‖ ≤ theta := h_p_norm v hv
    exact ⟨by linarith, by linarith⟩
  have h_coord_sep : ∀ v ∈ S, ∀ w ∈ S, v ≠ w →
      (ε / Real.sqrt 3)^2 ≤ ((coord (p v)).1 - (coord (p w)).1)^2 +
        ((coord (p v)).2 - (coord (p w)).2)^2 := by
    intro v hv w hw hne
    have h_i1 : inner ℝ (p v - p w) e1 = (coord (p v)).1 - (coord (p w)).1 := by
      simp [coord, inner_sub_left] <;> rfl
    have h_i2 : inner ℝ (p v - p w) e2 = (coord (p v)).2 - (coord (p w)).2 := by
      simp [coord, inner_sub_left] <;> rfl
    have h1 : ‖p v - p w‖ ^ 2 = ((coord (p v)).1 - (coord (p w)).1)^2 +
        ((coord (p v)).2 - (coord (p w)).2)^2 + (inner ℝ (p v - p w) u)^2 := by
      have hbasis := h_norm_decomp (p v - p w)
      rw [hbasis, h_i1, h_i2]
    have h2 : inner ℝ (p v - p w) u = 0 := by
      rw [inner_sub_left]
      rw [h_p_perp v, h_p_perp w] <;> ring
    have h3 : ε^2 / 3 ≤ ‖p v - p w‖ ^ 2 := h_proj_sep v hv w hw hne
    have h4 : (ε / Real.sqrt 3)^2 = ε^2 / 3 := by
      calc (ε / Real.sqrt 3)^2
        = ε^2 / (Real.sqrt 3)^2 := by ring
      _ = ε^2 / 3 := by rw [Real.sq_sqrt (by norm_num)]
    have h5 : ε^2 / 3 ≤ ((coord (p v)).1 - (coord (p w)).1)^2 + ((coord (p v)).2 - (coord (p w)).2)^2 := by
      rw [h1, h2] at h3
      simpa using h3
    rw [h4]
    exact h5
  let S' : Finset (ℝ × ℝ) := Finset.image (fun v : Point3 => coord (p v)) S
  have h_pe1 : ∀ (x : Point3), inner ℝ (p x) e1 = inner ℝ x e1 := by
    intro x
    have h1 : inner ℝ (p x) e1 = inner ℝ x e1 - inner ℝ ((inner ℝ x u) • u) e1 := by
      rw [inner_sub_left] <;> rfl
    have h2 : inner ℝ ((inner ℝ x u) • u) e1 = (inner ℝ x u) * inner ℝ u e1 := by
      rw [inner_smul_left] <;> rfl
    rw [h1, h2, he1_perp] <;> ring
  have h_pe2 : ∀ (x : Point3), inner ℝ (p x) e2 = inner ℝ x e2 := by
    intro x
    have h1 : inner ℝ (p x) e2 = inner ℝ x e2 - inner ℝ ((inner ℝ x u) • u) e2 := by
      rw [inner_sub_left] <;> rfl
    have h2 : inner ℝ ((inner ℝ x u) • u) e2 = (inner ℝ x u) * inner ℝ u e2 := by
      rw [inner_smul_left] <;> rfl
    have h3 : inner ℝ u e2 = 0 := by
      rw [h_inner_comm u e2, he2_perp_u]
    rw [h1, h2, h3] <;> ring
  have h_inj : Set.InjOn (fun v : Point3 => coord (p v)) (S : Set Point3) := by
    intro v hv w hw h
    have h4 : coord (p v) = coord (p w) := h
    simp only [coord, Prod.ext_iff] at h4
    have h5 : inner ℝ (p v) e1 = inner ℝ (p w) e1 := h4.1
    have h6 : inner ℝ (p v) e2 = inner ℝ (p w) e2 := h4.2
    have h8 : p v = p w := h_eq_of_inner (p v) (p w) h5 h6 (by rw [h_p_perp v, h_p_perp w])
    set c : ℝ := inner ℝ v u - inner ℝ w u with hc_def
    have h_vw : v - w = c • u := by
      have h9 : v = p v + inner ℝ v u • u := by simp [p] <;> abel
      have h10 : w = p w + inner ℝ w u • u := by simp [p] <;> abel
      have h11 : v - w = (p v - p w) + (inner ℝ v u - inner ℝ w u) • u := by
        have h_eq : v - w = (p v + inner ℝ v u • u) - (p w + inner ℝ w u • u) := by
          congr 1 <;> assumption
        calc v - w
          = (p v + inner ℝ v u • u) - (p w + inner ℝ w u • u) := h_eq
        _ = (p v - p w) + (inner ℝ v u • u - inner ℝ w u • u) := by abel
        _ = (p v - p w) + (inner ℝ v u - inner ℝ w u) • u := by rw [sub_smul]
      have h12 : (inner ℝ v u - inner ℝ w u) = c := by exact hc_def.symm
      rw [h11, h8, h12] <;> abel
    have h15 : ‖v‖ ^ 2 = ‖w + c • u‖ ^ 2 := by
      have h16 : v = w + c • u := by
        calc v
          = w + (v - w) := by abel
        _ = w + c • u := by rw [h_vw]
      rw [h16]
    have h18 : ‖w + c • u‖ ^ 2 = ‖w‖ ^ 2 + 2 * c * inner ℝ w u + c ^ 2 := by
      have h19 : ‖w + c • u‖ ^ 2 =
          ‖w‖ ^ 2 + 2 * inner ℝ w (c • u) + ‖c • u‖ ^ 2 :=
        norm_add_pow_two_real w (c • u)
      rw [h19]
      have h20 : inner ℝ w (c • u) = c * inner ℝ w u := by rw [inner_smul_right] <;> ring
      have h21 : ‖c • u‖ ^ 2 = c ^ 2 := by
        have h22 : ‖c • u‖ = |c| * ‖u‖ := by exact norm_smul c u
        rw [h22, hu] <;> simp [abs_pow] <;> ring
      rw [h20, h21] <;> ring
    have h23 : c * (2 * inner ℝ w u + c) = 0 := by
      have hv1 : ‖v‖ ^ 2 = 1 := by rw [hs1 v hv] <;> norm_num
      have hw1 : ‖w‖ ^ 2 = 1 := by rw [hs1 w hw] <;> norm_num
      have h_eq1 : ‖w + c • u‖ ^ 2 = 1 := by
        calc ‖w + c • u‖ ^ 2 = ‖v‖ ^ 2 := by rw [h15]
          _ = 1 := hv1
      have h_eq2 : ‖w‖ ^ 2 + 2 * c * inner ℝ w u + c ^ 2 = 1 := by
        rw [h18] at h_eq1
        exact h_eq1
      rw [hw1] at h_eq2
      have h : 2 * c * inner ℝ w u + c ^ 2 = 0 := by linarith
      have h' : c * (2 * inner ℝ w u + c) = 0 := by linarith
      exact h'
    have h24 : c = 0 := by
      have h26 : c = 0 ∨ 2 * inner ℝ w u + c = 0 := eq_zero_or_eq_zero_of_mul_eq_zero h23
      cases h26 with
      | inl h26 => exact h26
      | inr h26 =>
        have h27 : c = -2 * inner ℝ w u := by linarith
        have h28 : inner ℝ v u = -inner ℝ w u := by linarith [hc_def, h27]
        have h29 : 0 ≤ inner ℝ v u := h_side v hv
        have h30 : 0 ≤ inner ℝ w u := h_side w hw
        have h31 : inner ℝ w u = 0 := by linarith
        linarith
    have h32 : v - w = 0 := by rw [h_vw, h24] <;> simp
    exact sub_eq_zero.mp h32
  have h_card : S'.card = S.card :=
    Finset.card_image_of_injOn h_inj
  have h_ratio : ε / Real.sqrt 3 ≤ theta := by
    have h1 : ε / Real.sqrt 3 = (2 * δ / Real.pi) / Real.sqrt 3 := by rfl
    rw [h1]
    have h2 : (2 : ℝ) / (Real.pi * Real.sqrt 3) ≤ 1 := by
      have h4 : 3 < Real.pi := Real.pi_gt_three
      have h5 : 1 < Real.sqrt 3 := by
        have h6 : (1 : ℝ) < 3 := by norm_num
        have h7 : Real.sqrt 1 < Real.sqrt 3 := Real.sqrt_lt_sqrt (by norm_num) h6
        rw [Real.sqrt_one] at h7
        exact h7
      have h_pos : 0 < Real.pi * Real.sqrt 3 := by positivity
      have h_gt : 2 < Real.pi * Real.sqrt 3 := by
        have h : Real.pi * Real.sqrt 3 > 3 := by
          have h' : Real.pi * Real.sqrt 3 > 3 * 1 := by gcongr <;> linarith
          linarith
        linarith
      exact (div_le_one h_pos).mpr (by linarith)
    have h3 : (2 * δ / Real.pi) / Real.sqrt 3 ≤ δ := by
      calc (2 * δ / Real.pi) / Real.sqrt 3
        = (2 / (Real.pi * Real.sqrt 3)) * δ := by ring
      _ ≤ 1 * δ := by gcongr
      _ = δ := by ring
    have h4 : δ ≤ theta := htheta
    linarith
  have h_sep_pos : 0 < ε / Real.sqrt 3 := by positivity
  have h_coord_sep' : ∀ (p : ℝ × ℝ), p ∈ S' → ∀ (q : ℝ × ℝ), q ∈ S' → p ≠ q →
      (ε / Real.sqrt 3)^2 ≤ (p.1 - q.1)^2 + (p.2 - q.2)^2 := by
    intro p hp q hq hne
    rcases Finset.mem_image.mp hp with ⟨v, hv, rfl⟩
    rcases Finset.mem_image.mp hq with ⟨w, hw, rfl⟩
    have hvw : v ≠ w := by
      intro h
      rw [h] at hne
      exact hne rfl
    exact h_coord_sep v hv w hw hvw
  have h_coord_bound' : ∀ (p : ℝ × ℝ), p ∈ S' → |p.1| ≤ theta ∧ |p.2| ≤ theta := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨v, hv, rfl⟩
    exact h_coord_bound v hv
  have htheta_pos : 0 < theta := lt_of_lt_of_le hδ htheta
  have h_main : (S'.card : ℝ) ≤ 16 * (theta / (ε / Real.sqrt 3))^2 :=
    grid_packing2d (R := theta) (ε := ε / Real.sqrt 3) htheta_pos h_sep_pos h_ratio h_coord_bound' h_coord_sep'
  rw [h_card] at h_main
  exact h_main

/-! ### Main theorem -/

/-- 2D direction packing bound: pairwise `(2δ/π)`-separated unit vectors within
acute angle `theta` of `v0` have cardinality at most `300 * (theta/δ)^2`. -/
lemma direction_cap_packing_2d {δ theta : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (htheta : δ ≤ theta) (htheta1 : theta ≤ 1)
    {s : Finset Point3}
    (hs1 : ∀ v ∈ s, ‖v‖ = 1)
    (hs2 : ∀ v ∈ s, ∀ w ∈ s, v ≠ w → (2 * δ / Real.pi) ≤ dist v w)
    (v0 : Point3) (hv0 : ‖v0‖ = 1)
    (hcap : ∀ v ∈ s, hairbrushAcuteDirectionAngle v v0 ≤ theta) :
    (s.card : ℝ) ≤ 300 * (theta / δ)^2 := by
  set ε : ℝ := 2 * δ / Real.pi with hε_def
  have hε_pos : 0 < ε := by positivity
  by_cases h_case : theta ≤ 1 / 2
  · -- Case 1: theta ≤ 1/2, split into same-side halves
    have htheta_half : theta ≤ 1 / 2 := h_case
    let sPos : Finset Point3 := s.filter (fun v => 0 ≤ inner ℝ v v0)
    let sNeg : Finset Point3 := s.filter (fun v => inner ℝ v v0 < 0)
    have h_sub_pos : sPos ⊆ s := Finset.filter_subset _ _
    have h_sub_neg : sNeg ⊆ s := Finset.filter_subset _ _
    have h_disj : Disjoint sPos sNeg := by
      rw [Finset.disjoint_left]
      intro v hv1 hv2
      have h1 : 0 ≤ inner ℝ v v0 := (Finset.mem_filter.mp hv1).2
      have h2 : inner ℝ v v0 < 0 := (Finset.mem_filter.mp hv2).2
      linarith
    have h_union : sPos ∪ sNeg = s := by
      ext v
      simp only [sPos, sNeg, Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (h | h) <;> exact h.1
      · intro hv
        by_cases h : 0 ≤ inner ℝ v v0
        · left; exact ⟨hv, h⟩
        · right; exact ⟨hv, by linarith⟩
    have h_card_sum : s.card = sPos.card + sNeg.card := by
      rw [← Finset.card_union_of_disjoint h_disj, h_union]
    have h_side_pos : ∀ v ∈ sPos, 0 ≤ inner ℝ v v0 := by
      intro v hv
      simp only [sPos, Finset.mem_filter] at hv
      exact hv.2
    have h_side_neg : ∀ v ∈ sNeg, 0 ≤ inner ℝ v (-v0) := by
      intro v hv
      simp only [sNeg, Finset.mem_filter] at hv
      have h : inner ℝ v v0 < 0 := hv.2
      have h2 : inner ℝ v (-v0) = -inner ℝ v v0 := by
        simp [inner_smul_right] <;> ring
      rw [h2] <;> linarith
    have hcap_neg : ∀ v ∈ sNeg, hairbrushAcuteDirectionAngle v (-v0) ≤ theta := by
      intro v hv
      have h_inner : inner ℝ v (-v0) = -inner ℝ v v0 := by
        simp [inner_smul_right] <;> ring
      have h_arccos : Real.arccos (inner ℝ v (-v0)) = Real.pi - Real.arccos (inner ℝ v v0) := by
        rw [h_inner, Real.arccos_neg]
      have h_arccos2 : Real.pi - Real.arccos (inner ℝ v (-v0)) = Real.arccos (inner ℝ v v0) := by
        rw [h_arccos] <;> ring
      have h1 : hairbrushAcuteDirectionAngle v (-v0) = hairbrushAcuteDirectionAngle v v0 := by
        dsimp only [hairbrushAcuteDirectionAngle]
        rw [h_arccos]
        have h_simp : Real.pi - (Real.pi - Real.arccos (inner ℝ v v0)) = Real.arccos (inner ℝ v v0) := by ring
        rw [h_simp]
        <;> exact min_comm _ _
      rw [h1]
      exact hcap v (h_sub_neg hv)
    have h_pos_bound : (sPos.card : ℝ) ≤ 16 * (theta / (ε / Real.sqrt 3))^2 :=
      same_side_direction_packing hδ htheta htheta_half
        (fun v hv => hs1 v (h_sub_pos hv))
        (fun v hv w hw hne => hs2 v (h_sub_pos hv) w (h_sub_pos hw) hne)
        v0 hv0 h_side_pos
        (fun v hv => hcap v (h_sub_pos hv))
    have h_neg_bound : (sNeg.card : ℝ) ≤ 16 * (theta / (ε / Real.sqrt 3))^2 :=
      same_side_direction_packing hδ htheta htheta_half
        (fun v hv => hs1 v (h_sub_neg hv))
        (fun v hv w hw hne => hs2 v (h_sub_neg hv) w (h_sub_neg hw) hne)
        (-v0) (by simp [hv0])
        h_side_neg hcap_neg
    have h_sum : (s.card : ℝ) = (sPos.card : ℝ) + (sNeg.card : ℝ) := by
      exact_mod_cast h_card_sum
    have h_half : (s.card : ℝ) / 2 ≤ max (sPos.card : ℝ) (sNeg.card : ℝ) := by
      rw [h_sum]
      have h1 : (sPos.card : ℝ) ≤ max (sPos.card : ℝ) (sNeg.card : ℝ) := le_max_left _ _
      have h2 : (sNeg.card : ℝ) ≤ max (sPos.card : ℝ) (sNeg.card : ℝ) := le_max_right _ _
      linarith
    have h_max_bound : max (sPos.card : ℝ) (sNeg.card : ℝ) ≤
        16 * (theta / (ε / Real.sqrt 3))^2 := by
      exact max_le h_pos_bound h_neg_bound
    have h_main : (s.card : ℝ) ≤ 32 * (theta / (ε / Real.sqrt 3))^2 := by linarith
    have h_final : 32 * (theta / (ε / Real.sqrt 3))^2 ≤ 300 * (theta / δ)^2 := by
      have hε : ε = 2 * δ / Real.pi := by rfl
      have hpi2 : Real.pi ^ 2 < 10 := by
        have h1 : Real.pi < (3.15 : ℝ) := Real.pi_lt_d2
        have h2 : 0 < Real.pi := Real.pi_pos
        have h3 : Real.pi ^ 2 < (3.15 : ℝ)^2 := by nlinarith
        have h4 : (3.15 : ℝ)^2 = 9.9225 := by norm_num
        rw [h4] at h3
        linarith
      have hδ_pos' : 0 < δ := hδ
      have h_sqrt3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
      have h_eq1 : (theta / (ε / Real.sqrt 3)) = theta * Real.sqrt 3 * Real.pi / (2 * δ) := by
        rw [hε]
        field_simp [hδ_pos'.ne', Real.pi_ne_zero] <;> ring
      rw [h_eq1]
      have h_sq3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
      have h_eq2 : 32 * (theta * Real.sqrt 3 * Real.pi / (2 * δ))^2 = (24 * Real.pi ^ 2) * (theta / δ)^2 := by
        field_simp [hδ_pos'.ne'] <;> nlinarith [h_sq3]
      rw [h_eq2]
      have h_bound : 24 * Real.pi ^ 2 ≤ 300 := by linarith [hpi2]
      have h_nonneg : 0 ≤ (theta / δ)^2 := by positivity
      exact mul_le_mul_of_nonneg_right h_bound h_nonneg
    exact h_main.trans h_final
  · -- Case 2: theta > 1/2, use global sphere packing bound
    have h_gt_half : 1 / 2 < theta := by linarith
    have h_global : (s.card : ℝ) ≤ 26 / ε ^ 2 := by
      have hε1 : ε ≤ 1 := by
        have h1 : ε = 2 * δ / Real.pi := by rfl
        rw [h1]
        have h2 : 0 < Real.pi := Real.pi_pos
        have h3 : 2 * δ ≤ Real.pi := by
          have h4 : δ ≤ 1 := hδ1
          have h5 : Real.pi > 3 := Real.pi_gt_three
          nlinarith
        exact (div_le_one h2).mpr h3
      exact sphere_separated_card_bound_annulus hε_pos hε1 hs1
        (fun v hv w hw hne => hs2 v hv w hw hne)
    have h1 : 26 / ε ^ 2 ≤ 300 * (theta / δ)^2 := by
      have hε2 : ε = 2 * δ / Real.pi := by rfl
      rw [hε2]
      have hδ_pos : 0 < δ := by linarith
      have hpi2 : Real.pi ^ 2 < 10 := by
        have h1 : Real.pi < (3.15 : ℝ) := Real.pi_lt_d2
        have h2 : 0 < Real.pi := Real.pi_pos
        have h3 : Real.pi ^ 2 < (3.15 : ℝ)^2 := by nlinarith
        have h4 : (3.15 : ℝ)^2 = 9.9225 := by norm_num
        rw [h4] at h3
        linarith
      have h_theta2 : theta ^ 2 > 1 / 4 := by nlinarith
      have h_left : 26 / ((2 * δ / Real.pi) ^ 2) = (26 * Real.pi ^ 2) / (4 * δ ^ 2) := by
        have h_pos : 0 < δ := by linarith
        field_simp [h_pos.ne'] <;> ring
      rw [h_left]
      have h9 : 26 * Real.pi ^ 2 < 300 := by
        have h10 : Real.pi ^ 2 < 10 := by
          have h1 : Real.pi < (3.15 : ℝ) := Real.pi_lt_d2
          have h2 : 0 < Real.pi := Real.pi_pos
          have h3 : Real.pi ^ 2 < (3.15 : ℝ)^2 := by nlinarith
          have h4 : (3.15 : ℝ)^2 = 9.9225 := by norm_num
          rw [h4] at h3
          linarith
        nlinarith
      have h10 : (26 * Real.pi ^ 2) / (4 * δ ^ 2) ≤ (75 : ℝ) / δ ^ 2 := by
        have h11 : 26 * Real.pi ^ 2 ≤ 4 * (75 : ℝ) := by linarith [h9]
        have h_pos : 0 < δ ^ 2 := by positivity
        have h_rewrite : (26 * Real.pi ^ 2) / (4 * δ ^ 2) = (26 * Real.pi ^ 2 / 4) / δ ^ 2 := by
          field_simp [h_pos.ne'] <;> ring
        rw [h_rewrite]
        have h12 : (26 * Real.pi ^ 2 / 4 : ℝ) ≤ (75 : ℝ) := by linarith
        exact div_le_div_of_nonneg_right h12 (by positivity)
      have h12 : (75 : ℝ) / δ ^ 2 ≤ 300 * theta ^ 2 / δ ^ 2 := by
        have h13 : (75 : ℝ) ≤ 300 * theta ^ 2 := by linarith [h_theta2]
        have h_pos : 0 < δ ^ 2 := by positivity
        exact div_le_div_of_nonneg_right h13 (by positivity)
      have h14 : 300 * theta ^ 2 / δ ^ 2 = 300 * (theta / δ)^2 := by
        field_simp [hδ_pos.ne'] <;> ring
      rw [h14] at h12
      exact h10.trans h12
    exact h_global.trans h1

end Kakeya.Assouad
