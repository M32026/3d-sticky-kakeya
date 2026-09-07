import MyLeanRepo.Kakeya.CV.Targets.EllipsoidTranslatePacking.Basic
import MyLeanRepo.Kakeya.CV.Statements

/-!
# Scaling lemmas for ellipsoid packing in unit cubes

This file proves three geometric scaling lemmas that transport a packing
from the unit ball into a unit cube:

1. `scaledEllipsoid_half_image`: halving a `2η`-ellipsoid gives an `η`-ellipsoid.
2. `scaledEllipsoid_half_containment`: a halved ellipsoid fits in the unit cube
   when the original `2η`-ellipsoid fits in the unit ball.
3. `scaledEllipsoid_half_disjoint`: halving preserves disjointness.

## Whiteprint node

- `UnitCubeEllipsoidPacking.ScalingLemmas`
-/

noncomputable section

open Set Finset

namespace Kakeya.CV

/-- Each coordinate of a Euclidean vector is bounded by its norm. -/
private lemma coord_abs_le_norm {n : ℕ} (x : Point n) (i : Fin n) :
    |x i| ≤ ‖x‖ := by
  have h1 : (x i) ^ 2 ≤ ‖x‖ ^ 2 := by
    have h2 : ‖x‖ ^ 2 = ∑ j : Fin n, (x j) ^ 2 :=
      EuclideanSpace.real_norm_sq_eq x
    rw [h2]
    have h3 : ∀ (j : Fin n), j ∈ Finset.univ → 0 ≤ (x j) ^ 2 := fun j _ => by positivity
    exact single_le_sum h3 (mem_univ i)
  have h4 : 0 ≤ |x i| := abs_nonneg _
  have h5 : 0 ≤ ‖x‖ := norm_nonneg _
  have h6 : |x i| ^ 2 = (x i) ^ 2 := by rw [sq_abs]
  nlinarith

/-- Halving the points of a `2η`-ellipsoid centered at `z` yields an
`η`-ellipsoid centered at `(1/2) • z`. -/
lemma scaledEllipsoid_half_image (A : Point 3 ≃ₗ[ℝ] Point 3) (η : ℝ)
    (z : Point 3) :
    (fun x : Point 3 => (1 / 2 : ℝ) • x) '' scaledEllipsoid A (2 * η) z =
      scaledEllipsoid A η ((1 / 2 : ℝ) • z) := by
  ext w
  simp only [Set.mem_image, mem_scaledEllipsoid_iff]
  constructor
  · rintro ⟨x, ⟨y, hy, rfl⟩, rfl⟩
    refine' ⟨(1 / 2 : ℝ) • y, _ , _⟩
    · have h_norm : ‖(1 / 2 : ℝ) • y‖ ≤ η := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)]
        <;> linarith
      exact h_norm
    · have h : (1 / 2 : ℝ) • z + A ((1 / 2 : ℝ) • y) =
          (1 / 2 : ℝ) • (z + A y) := by
        rw [smul_add, map_smul A (1 / 2 : ℝ) y] <;> abel
      exact h
  · rintro ⟨y, hy, rfl⟩
    let y' : Point 3 := (2 : ℝ) • y
    have h_y'_norm : ‖y'‖ ≤ 2 * η := by
      dsimp only [y']
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
      <;> linarith
    have h_eq : (1 / 2 : ℝ) • (z + A y') = (1 / 2 : ℝ) • z + A y := by
      have h1 : A y' = (2 : ℝ) • A y := by
        dsimp only [y']
        rw [map_smul A (2 : ℝ) y] <;> rfl
      rw [h1, smul_add]
      <;> simp [smul_smul] <;> abel
    exact ⟨z + A y', ⟨y', h_y'_norm, rfl⟩, h_eq⟩

/-- If the `2η`-ellipsoid centered at `z` is contained in the unit ball, then
the `η`-ellipsoid centered at `c + (1/2) • z` is contained in the unit cube
centered at `c`. -/
lemma scaledEllipsoid_half_containment (A : Point 3 ≃ₗ[ℝ] Point 3) (η : ℝ)
    (_hη : 0 < η) (z c : Point 3)
    (h : scaledEllipsoid A (2 * η) z ⊆ unitBall 3) :
    scaledEllipsoid A η (c + (1 / 2 : ℝ) • z) ⊆ unitCube c := by
  intro x hx
  rcases (mem_scaledEllipsoid_iff A η (c + (1 / 2 : ℝ) • z) x).mp hx
    with ⟨y, hy, rfl⟩
  set y' : Point 3 := (2 : ℝ) • y with hy'_def
  have h_y'_norm : ‖y'‖ ≤ 2 * η := by
    rw [hy'_def, norm_smul, Real.norm_eq_abs, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
    <;> linarith
  have h1 : z + A y' ∈ scaledEllipsoid A (2 * η) z := by
    rw [mem_scaledEllipsoid_iff A (2 * η) z (z + A y')]
    exact ⟨y', h_y'_norm, rfl⟩
  have h2 : z + A y' ∈ unitBall 3 := h h1
  have h3 : ‖z + A y'‖ ≤ 1 := by
    simpa [unitBall, Metric.mem_closedBall] using h2
  set v : Point 3 := (c + (1 / 2 : ℝ) • z + A y) - c with hv_def
  have h4 : v = (1 / 2 : ℝ) • (z + A y') := by
    have h5 : A y' = (2 : ℝ) • A y := by
      rw [hy'_def, map_smul A (2 : ℝ) y] <;> rfl
    simp [hv_def, h5, smul_add, smul_smul] <;> abel
  have h6 : ‖v‖ ≤ 1 / 2 := by
    rw [h4]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)]
    <;> linarith
  have h7 : ∀ (i : Fin 3), |v i| ≤ 1 / 2 := by
    intro i
    have h8 : |v i| ≤ ‖v‖ := coord_abs_le_norm v i
    linarith
  simpa [unitCube, hv_def] using h7

/-- Halving two disjoint `2η`-ellipsoids and translating them by `c` preserves
disjointness. -/
lemma scaledEllipsoid_half_disjoint (A : Point 3 ≃ₗ[ℝ] Point 3) (η : ℝ)
    (z1 z2 c : Point 3)
    (h : Disjoint (scaledEllipsoid A (2 * η) z1)
        (scaledEllipsoid A (2 * η) z2)) :
    Disjoint (scaledEllipsoid A η (c + (1 / 2 : ℝ) • z1))
      (scaledEllipsoid A η (c + (1 / 2 : ℝ) • z2)) := by
  let f : Point 3 → Point 3 := fun x => c + (1 / 2 : ℝ) • x
  have h_inj : Function.Injective f := by
    intro x y hxy
    have h1 : (1 / 2 : ℝ) • x = (1 / 2 : ℝ) • y := by
      simpa [f] using hxy
    have h2 : x = y := by
      simpa [smul_eq_mul] using h1
    exact h2
  have h_trans : ∀ (z : Point 3),
      f '' scaledEllipsoid A (2 * η) z =
        scaledEllipsoid A η (c + (1 / 2 : ℝ) • z) := by
    intro z
    ext w
    simp only [f, Set.mem_image, mem_scaledEllipsoid_iff]
    constructor
    · rintro ⟨x, ⟨y, hy, rfl⟩, rfl⟩
      refine' ⟨(1 / 2 : ℝ) • y, _ , _⟩
      · have h_norm : ‖(1 / 2 : ℝ) • y‖ ≤ η := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)]
          <;> linarith
        exact h_norm
      · have h_eq : c + (1 / 2 : ℝ) • z + A ((1 / 2 : ℝ) • y) =
            c + (1 / 2 : ℝ) • (z + A y) := by
          rw [smul_add, map_smul A (1 / 2 : ℝ) y] <;> abel
        exact h_eq
    · rintro ⟨y, hy, rfl⟩
      let y' : Point 3 := (2 : ℝ) • y
      have h_y'_norm : ‖y'‖ ≤ 2 * η := by
        dsimp only [y']
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
        <;> linarith
      have h_eq : c + (1 / 2 : ℝ) • (z + A y') =
            c + (1 / 2 : ℝ) • z + A y := by
          have h1 : A y' = (2 : ℝ) • A y := by
            dsimp only [y']
            rw [map_smul A (2 : ℝ) y] <;> rfl
          rw [h1, smul_add] <;> simp [smul_smul] <;> abel
      exact ⟨z + A y', ⟨y', h_y'_norm, rfl⟩, h_eq⟩
  have h_eq1 := h_trans z1
  have h_eq2 := h_trans z2
  have h_injOn : Set.InjOn f Set.univ := by
    intro x _ y _ hxy
    exact h_inj hxy
  have h_disj : Disjoint (f '' scaledEllipsoid A (2 * η) z1)
      (f '' scaledEllipsoid A (2 * η) z2) :=
    h.image h_injOn (Set.subset_univ _) (Set.subset_univ _)
  rw [h_eq1, h_eq2] at h_disj
  exact h_disj

end Kakeya.CV
