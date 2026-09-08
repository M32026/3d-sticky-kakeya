import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.PlaneIntercept
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.PlankDirectionBound

/-!
# Bounds on intercept data for tubes in a plank

Helper lemmas for instantiating the generic phase-space grid packing theorem
with intercept-based parameterization.
-/

noncomputable section

namespace Kakeya.Streamlined.GeometricLemmas

open Kakeya.Streamlined

/--
Natural plane index: shift `planeIndex` by `Nat.ceil A` to make it nonnegative.
Given `p2 ∈ [-A/2, A/2]`, we have `-A ≤ planeIndex p2 ≤ A + 1`,
so `planeIndex p2 + Nat.ceil A ≥ 0`.
-/
lemma planeIndex_nat_nonneg (p2 A : ℝ) (hA : 0 ≤ A)
    (hlo : -A / 2 ≤ p2) (hhi : p2 ≤ A / 2) :
    0 ≤ planeIndex p2 + (Nat.ceil A : ℤ) := by
  have h_bounds : -A ≤ (planeIndex p2 : ℝ) :=
    (planeIndex_bound p2 A hA hlo hhi).1
  have h_ceil : (Nat.ceil A : ℝ) ≥ A := Nat.le_ceil A
  have h : (planeIndex p2 : ℝ) + (Nat.ceil A : ℝ) ≥ 0 := by linarith
  exact_mod_cast h

/--
Bound on the natural plane index:
`(planeIndex p2 + Nat.ceil A).toNat < 2 * Nat.ceil A + 2`.
-/
lemma planeIndex_nat_lt (p2 A : ℝ) (hA : 0 ≤ A)
    (hlo : -A / 2 ≤ p2) (hhi : p2 ≤ A / 2) :
    (planeIndex p2 + (Nat.ceil A : ℤ)).toNat < 2 * Nat.ceil A + 2 := by
  have h_bounds : (planeIndex p2 : ℝ) ≤ A + 1 :=
    (planeIndex_bound p2 A hA hlo hhi).2
  have h_ceil : (Nat.ceil A : ℝ) ≥ A := Nat.le_ceil A
  have h1 : ((planeIndex p2 + (Nat.ceil A : ℤ)).toNat : ℝ) ≤ 2 * (Nat.ceil A : ℝ) + 1 := by
    have h2 : ((planeIndex p2 + (Nat.ceil A : ℤ)).toNat : ℤ) = planeIndex p2 + (Nat.ceil A : ℤ) :=
      Int.toNat_of_nonneg (planeIndex_nat_nonneg p2 A hA hlo hhi)
    have h3 : ((planeIndex p2 + (Nat.ceil A : ℤ)).toNat : ℝ) = (planeIndex p2 : ℝ) + (Nat.ceil A : ℝ) := by
      exact_mod_cast h2
    rw [h3]
    linarith
  have h4 : ((planeIndex p2 + (Nat.ceil A : ℤ)).toNat : ℝ) < (2 * Nat.ceil A + 2 : ℝ) := by
    linarith
  exact_mod_cast h4

/--
Generic bound on transverse intercept coordinate.
If `|p| ≤ P` and `|u| ≤ U` and `t0 ∈ [0,1]`, then
`|p + t0 * u| ≤ P + U`.
-/
lemma intercept_coord_bound (p u t0 P U : ℝ)
    (hp : |p| ≤ P) (hu : |u| ≤ U)
    (ht0_0 : 0 ≤ t0) (ht0_1 : t0 ≤ 1) :
    |p + t0 * u| ≤ P + U := by
  have h_tri : |p + t0 * u| ≤ |p| + |t0 * u| := by
    have h2 : -(|p| + |t0 * u|) ≤ p + t0 * u := by
      have h3 : -|p| ≤ p := (abs_le.mp (by rfl : |p| ≤ |p|)).1
      have h4 : -|t0 * u| ≤ t0 * u := (abs_le.mp (by rfl : |t0 * u| ≤ |t0 * u|)).1
      linarith
    have h5 : p + t0 * u ≤ |p| + |t0 * u| := by
      have h6 : p ≤ |p| := (abs_le.mp (by rfl : |p| ≤ |p|)).2
      have h7 : t0 * u ≤ |t0 * u| := (abs_le.mp (by rfl : |t0 * u| ≤ |t0 * u|)).2
      linarith
    exact abs_le.mpr ⟨h2, h5⟩
  have h_abs_mul : |t0 * u| = |t0| * |u| := by rw [abs_mul]
  have h_t0_bound : |t0| ≤ 1 := by
    rw [abs_of_nonneg ht0_0] <;> linarith
  calc |p + t0 * u|
    ≤ |p| + |t0 * u| := h_tri
  _ = |p| + |t0| * |u| := by rw [h_abs_mul]
  _ ≤ P + 1 * U := by gcongr <;> linarith
  _ = P + U := by ring

/--
For a plank with dimensions a × b × 1 in frame coordinates,
the intercept point transverse coordinates satisfy:
- |q_0| ≤ 3 * A * a / 2
- |q_1| ≤ 3 * A * b / 2
-/
lemma plank_intercept_bounds (p' u' : Point3) (t0 : ℝ)
    (A a b : ℝ) (hA : 0 ≤ A) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hp0 : |p' 0| ≤ A * a / 2) (hp1 : |p' 1| ≤ A * b / 2)
    (hu0 : |u' 0| ≤ A * a) (hu1 : |u' 1| ≤ A * b)
    (ht0_0 : 0 ≤ t0) (ht0_1 : t0 ≤ 1) :
    |(p' + t0 • u') 0| ≤ 3 * A * a / 2 ∧
    |(p' + t0 • u') 1| ≤ 3 * A * b / 2 := by
  have hq0 : |(p' + t0 • u') 0| ≤ 3 * A * a / 2 := by
    have h1 : (p' + t0 • u') 0 = p' 0 + t0 * u' 0 := by
      simp [Pi.add_apply, Pi.smul_apply]
    rw [h1]
    have h2 := intercept_coord_bound (p' 0) (u' 0) t0 (A * a / 2) (A * a) hp0 hu0 ht0_0 ht0_1
    linarith
  have hq1 : |(p' + t0 • u') 1| ≤ 3 * A * b / 2 := by
    have h1 : (p' + t0 • u') 1 = p' 1 + t0 * u' 1 := by
      simp [Pi.add_apply, Pi.smul_apply]
    rw [h1]
    have h2 := intercept_coord_bound (p' 1) (u' 1) t0 (A * b / 2) (A * b) hp1 hu1 ht0_0 ht0_1
    linarith
  exact ⟨hq0, hq1⟩

/--
After permuting axes 0 and 2 (so the dominant axis becomes axis 2),
the intercept bounds become:
- |q_0| ≤ 3*A/2
- |q_1| ≤ 3*A*b/2
-/
lemma permuted_intercept_bounds (p' u' : Point3) (t0 : ℝ)
    (A b : ℝ) (hA : 0 ≤ A) (hb : 0 ≤ b)
    (hp2 : |p' 2| ≤ A / 2) (hp1 : |p' 1| ≤ A * b / 2)
    (hu2 : |u' 2| ≤ A) (hu1 : |u' 1| ≤ A * b)
    (ht0_0 : 0 ≤ t0) (ht0_1 : t0 ≤ 1) :
    |p' 2 + t0 * u' 2| ≤ 3 * A / 2 ∧
    |p' 1 + t0 * u' 1| ≤ 3 * A * b / 2 := by
  have hq0 : |p' 2 + t0 * u' 2| ≤ 3 * A / 2 := by
    have h2 := intercept_coord_bound (p' 2) (u' 2) t0 (A / 2) A hp2 hu2 ht0_0 ht0_1
    linarith
  have hq1 : |p' 1 + t0 * u' 1| ≤ 3 * A * b / 2 := by
    have h2 := intercept_coord_bound (p' 1) (u' 1) t0 (A * b / 2) (A * b) hp1 hu1 ht0_0 ht0_1
    linarith
  exact ⟨hq0, hq1⟩

end Kakeya.Streamlined.GeometricLemmas
