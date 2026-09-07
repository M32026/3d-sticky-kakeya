import MyLeanRepo.Kakeya.CV.PolynomialCylinder.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Geometry.Euclidean.Projection

/-!
# Unit tube projection area for the polynomial cylinder estimate

The projection of the unit tube about a line in direction e₃ onto the
perpendicular plane is contained in a closed disk of radius 1, and therefore
has Lebesgue measure at most π.

## Whiteprint node: tube-projection-area
-/

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal Real

namespace Kakeya.CV

variable {n : ℕ}

/-- The infimum distance from `x` to the affine line through `a` in direction
`e₃` equals the Euclidean distance in the first two coordinates. -/
lemma infDist_to_line_e3 (a x : Point 3) :
    infDist x (affineLine a e3) =
      Real.sqrt ((x 0 - a 0) ^ 2 + (x 1 - a 1) ^ 2) := by
  let s : AffineSubspace ℝ (Point 3) := AffineSubspace.mk' a (ℝ ∙ e3)
  have h_line : (affineLine a e3) = (s : Set (Point 3)) := by
    ext y
    simp only [affineLine, Set.mem_setOf_eq]
    have h1 : y ∈ s ↔ ∃ (t : ℝ), t • e3 = y -ᵥ a := by
      simp [s, Submodule.mem_span_singleton, AffineSubspace.mem_mk'] <;> rfl
    constructor
    · rintro ⟨t, rfl⟩
      have h2 : (a + t • e3) -ᵥ a = t • e3 := by
        simp [vsub_eq_sub, vadd_eq_add, e3] <;> abel
      simpa [s, Submodule.mem_span_singleton, AffineSubspace.mem_mk'] using ⟨t, h2⟩
    · rintro h
      have h2 : ∃ (t : ℝ), t • e3 = y -ᵥ a := (h1).mp h
      rcases h2 with ⟨t, ht⟩
      have hvec : y -ᵥ a = t • e3 := ht.symm
      have h_eq : y = a +ᵥ (t • e3) := by
        have h : a +ᵥ (y -ᵥ a) = y := by
          simp [vsub_eq_sub, vadd_eq_add]
        have h2 : a +ᵥ (t • e3) = a +ᵥ (y -ᵥ a) := by rw [hvec]
        rw [h] at h2
        exact h2.symm
      exact ⟨t, h_eq⟩
  rw [h_line]
  let q : Point 3 := a + (x 2 - a 2) • e3
  have hq1 : q ∈ s := by
    have h : q -ᵥ a = (x 2 - a 2) • e3 := by
      simp [q, vsub_eq_sub] <;> abel
    rw [AffineSubspace.mem_mk']
    rw [h]
    exact Submodule.mem_span_singleton.mpr ⟨x 2 - a 2, rfl⟩
  have h_inner_e3 : ∀ (u : Point 3), inner ℝ u e3 = u 2 := by
    intro u
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    have h : (e3 ⬝ᵥ star u) = u 2 := by
      simp [e3, dotProduct, Fin.sum_univ_succ]
      <;> ring
    exact h
  have h_perp_e3 : inner ℝ (x -ᵥ q) e3 = 0 := by
    have h1 : inner ℝ (x -ᵥ q) e3 = (x -ᵥ q) 2 := h_inner_e3 (x -ᵥ q)
    rw [h1]
    have h2 : (x -ᵥ q) 2 = x 2 - q 2 := by rfl
    rw [h2]
    have h3 : q 2 = x 2 := by simp [q, e3] <;> ring
    rw [h3] <;> ring
  have h_perp : ∀ (v : Point 3), v ∈ (ℝ ∙ e3) → inner ℝ (x -ᵥ q) v = 0 := by
    intro v hv
    rcases Submodule.mem_span_singleton.mp hv with ⟨t, rfl⟩
    rw [inner_smul_right, h_perp_e3] <;> ring
  have h_perp' : ∀ (u : Point 3), u ∈ (ℝ ∙ e3) → inner ℝ u (x -ᵥ q) = 0 := by
    intro u hu
    have h := h_perp u hu
    rw [real_inner_comm] at h
    exact h
  have hq2 : x -ᵥ q ∈ (ℝ ∙ e3)ᗮ := by
    rw [Submodule.mem_orthogonal]
    exact h_perp'
  have h_sdir : s.direction = (ℝ ∙ e3) := AffineSubspace.direction_mk' a (ℝ ∙ e3)
  have hproj : EuclideanGeometry.orthogonalProjection s x = q := by
    rw [EuclideanGeometry.coe_orthogonalProjection_eq_iff_mem]
    rw [h_sdir]
    exact ⟨hq1, hq2⟩
  have h_dist : dist x q = Real.sqrt ((x 0 - a 0)^2 + (x 1 - a 1)^2) := by
    rw [EuclideanSpace.dist_eq]
    have h_sum : (∑ i : Fin 3, dist (x i) (q i) ^ 2) = (x 0 - a 0)^2 + (x 1 - a 1)^2 := by
      have h_eval : ∑ i : Fin 3, dist (x i) (q i) ^ 2 =
          dist (x 0) (q 0) ^ 2 + dist (x 1) (q 1) ^ 2 + dist (x 2) (q 2) ^ 2 := by
        rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
        <;> simp
        <;> ring
      rw [h_eval]
      have hq0' : q 0 = a 0 := by simp [q, e3]
      have hq1' : q 1 = a 1 := by simp [q, e3]
      have hq2' : q 2 = x 2 := by simp [q, e3] <;> ring
      rw [hq0', hq1', hq2']
      have h0 : dist (x 0) (a 0) ^ 2 = (x 0 - a 0)^2 := by rw [Real.dist_eq, sq_abs]
      have h1 : dist (x 1) (a 1) ^ 2 = (x 1 - a 1)^2 := by rw [Real.dist_eq, sq_abs]
      have h2 : dist (x 2) (x 2) ^ 2 = 0 := by simp
      rw [h0, h1, h2] <;> ring
    rw [h_sum]
  have h_infdist : infDist x (s : Set (Point 3)) = dist x (EuclideanGeometry.orthogonalProjection s x) :=
    (EuclideanGeometry.dist_orthogonalProjection_eq_infDist s x).symm
  rw [h_infdist, hproj, h_dist]

lemma proj2_dist (x a : Point 3) :
    dist (proj2 x) (proj2 a) = Real.sqrt ((x 0 - a 0)^2 + (x 1 - a 1)^2) := by
  have hx : ∀ (i : Fin 2), (proj2 x) i = x (Fin.castSucc i) := by
    intro i; simp [proj2]
  have ha : ∀ (i : Fin 2), (proj2 a) i = a (Fin.castSucc i) := by
    intro i; simp [proj2]
  rw [EuclideanSpace.dist_eq]
  have h_sum : (∑ i : Fin 2, dist ((proj2 x) i) ((proj2 a) i) ^ 2) =
      (x 0 - a 0)^2 + (x 1 - a 1)^2 := by
    have h_eval : ∑ i : Fin 2, dist ((proj2 x) i) ((proj2 a) i) ^ 2 =
        dist ((proj2 x) 0) ((proj2 a) 0) ^ 2 + dist ((proj2 x) 1) ((proj2 a) 1) ^ 2 := by
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
      <;> simp
      <;> ring
    rw [h_eval]
    have hx0 : (proj2 x) 0 = x 0 := by simp [proj2]
    have ha0 : (proj2 a) 0 = a 0 := by simp [proj2]
    have hx1 : (proj2 x) 1 = x 1 := by simp [proj2]
    have ha1 : (proj2 a) 1 = a 1 := by simp [proj2]
    rw [hx0, ha0, hx1, ha1]
    have h0 : dist (x 0) (a 0) ^ 2 = (x 0 - a 0)^2 := by rw [Real.dist_eq, sq_abs]
    have h1 : dist (x 1) (a 1) ^ 2 = (x 1 - a 1)^2 := by rw [Real.dist_eq, sq_abs]
    rw [h0, h1] <;> ring
  rw [h_sum]

/-- The projection of the unit tube onto the first two coordinates is contained
in a closed disk of radius 1 centered at the projection of `a`. -/
lemma tube_projection_contained (a : Point 3) :
    proj2 '' unitTube a e3 ⊆ Metric.closedBall (proj2 a) 1 := by
  rintro y ⟨x, hx, rfl⟩
  have h2 : infDist x (affineLine a e3) ≤ 1 := hx
  rw [infDist_to_line_e3 a x] at h2
  have h3 : dist (proj2 x) (proj2 a) ≤ 1 := by
    rw [proj2_dist x a]
    exact h2
  exact h3

/-- The Lebesgue measure of the projection of the unit tube is at most π. -/
lemma tube_projection_measure_le (a : Point 3) :
    volume (proj2 '' unitTube a e3) ≤ ENNReal.ofReal Real.pi := by
  have h1 : proj2 '' unitTube a e3 ⊆ Metric.closedBall (proj2 a) 1 :=
    tube_projection_contained a
  have h4 : volume (proj2 '' unitTube a e3) ≤ volume (Metric.closedBall (proj2 a) 1) :=
    measure_mono h1
  have h5 : volume (Metric.closedBall (proj2 a) 1) = ENNReal.ofReal Real.pi := by
    rw [EuclideanSpace.volume_closedBall_fin_two (proj2 a) 1]
    <;> norm_num
  rw [h5] at h4
  exact h4

end Kakeya.CV
