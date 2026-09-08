/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Mathlib.Analysis.InnerProductSpace
public import Kakeya.DimensionThree.Plank.AngleDef
public import Mathlib.Algebra.Order.Floor.Extended

/-!
# Outer slab model and slab angles for GWZ Lemma 6.13

This file contains the exact outer slab model of a plank–box intersection (`plankSlabModel`,
`plankSlabModel_inter_subset`, `plankSlabModel_dilation_volume`) used by `denseBoxEstimate`, and the
plank/slab angle comparability (`plankSlabAngleComparable`). The homothety-image API used by the
dense-box construction lives in `BoxRescaling`, which imports this file.
-/

@[expose] public section

open MeasureTheory Convexity
open scoped NNReal Real

noncomputable section

namespace Plank

variable {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {ι : Type*}

/-- Two points of a prism differ by at most twice the thickness in each `basis` coordinate. -/
private lemma abs_repr_vsub_le_two_mul_thicknesses -- (extracted by Fuse golfer)
    {n : ℕ} {E S : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [PseudoMetricSpace S]
    [NormedAddTorsor E S] (P : PrismNDim n E S) {x y : S} (hx : x ∈ (P.carrier : Set S))
    (hy : y ∈ (P.carrier : Set S)) (i : Fin n) :
    |P.basis.repr (x -ᵥ y) i| ≤ 2 * (P.thicknesses i : ℝ) := by
  have hx' := (P.mem_carrier_iff x).mp hx i
  have hy' := (P.mem_carrier_iff y).mp hy i
  have h : P.basis.repr (x -ᵥ y) i
      = P.basis.repr (x -ᵥ P.center) i - P.basis.repr (y -ᵥ P.center) i := by
    rw [show x -ᵥ y = (x -ᵥ P.center) - (y -ᵥ P.center) from
      (vsub_sub_vsub_cancel_right _ _ _).symm, map_sub]
    rfl
  rw [h]
  exact (abs_sub _ _).trans (by linarith)

/-- **Diameter bound for a `Prism3D`** (reusable helper): any two points of the carrier are within
`2·√(a² + b² + c²)`. Each coordinate difference in the orthonormal `basis` is at most twice the
corresponding thickness, and the Euclidean norm is the root-sum-of-squares of these coordinates. -/
private lemma prism3D_dist_le_of_mem_carrier {a' b' c' : ℝ≥0} {hab' : a' ≤ b'} {hbc' : b' ≤ c'}
    (P : Prism3D a' b' c' hab' hbc') {x y : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ (P.carrier : Set (EuclideanSpace ℝ (Fin 3))))
    (hy : y ∈ (P.carrier : Set (EuclideanSpace ℝ (Fin 3)))) :
    dist x y ≤ 2 * Real.sqrt (((a' : ℝ)) ^ 2 + ((b' : ℝ)) ^ 2 + ((c' : ℝ)) ^ 2) := by
  have key : ∀ i : Fin 3, ‖P.basis.repr (x -ᵥ y) i‖ ^ 2 ≤ (2 * (P.thicknesses i : ℝ)) ^ 2 :=
    fun i => by
      rw [Real.norm_eq_abs]
      exact (sq_le_sq₀ (abs_nonneg _) (mul_nonneg zero_le_two (P.thicknesses i).coe_nonneg)).mpr
        (abs_repr_vsub_le_two_mul_thicknesses P.toPrismNDim hx hy i)
  rw [dist_eq_norm_vsub (EuclideanSpace ℝ (Fin 3)), ← P.basis.repr.norm_map (x -ᵥ y),
    EuclideanSpace.norm_eq]
  calc Real.sqrt (∑ i : Fin 3, ‖P.basis.repr (x -ᵥ y) i‖ ^ 2)
      ≤ Real.sqrt (∑ i : Fin 3, (2 * (P.thicknesses i : ℝ)) ^ 2) :=
        Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => key i)
    _ = Real.sqrt ((2 : ℝ) ^ 2 * ((a' : ℝ) ^ 2 + (b' : ℝ) ^ 2 + (c' : ℝ) ^ 2)) := by
        congr 1
        rw [P.thicknesses_eq, Fin.sum_univ_three]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Matrix.cons_val_two, Matrix.tail_cons]
        ring
    _ = 2 * Real.sqrt ((a' : ℝ) ^ 2 + (b' : ℝ) ^ 2 + (c' : ℝ) ^ 2) := by
        rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]

/-- A `Prism3D` has diameter at most four times its largest thickness:
`2·√(a² + b² + c²) ≤ 2·√(4c²) = 4c`. -/
private lemma prism3D_dist_le_four_mul -- (extracted by Fuse golfer)
    {a' b' c' : ℝ≥0} {hab' : a' ≤ b'} {hbc' : b' ≤ c'}
    (P : Prism3D a' b' c' hab' hbc') {x y : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ (P.carrier : Set (EuclideanSpace ℝ (Fin 3))))
    (hy : y ∈ (P.carrier : Set (EuclideanSpace ℝ (Fin 3)))) :
    dist x y ≤ 4 * (c' : ℝ) := by
  refine (prism3D_dist_le_of_mem_carrier P hx hy).trans ?_
  have hac : (a' : ℝ) ≤ c' := by exact_mod_cast hab'.trans hbc'
  have hbc : (b' : ℝ) ≤ c' := by exact_mod_cast hbc'
  have h := Real.sqrt_le_sqrt (show (a' : ℝ) ^ 2 + (b' : ℝ) ^ 2 + (c' : ℝ) ^ 2
    ≤ (2 * (c' : ℝ)) ^ 2 from by nlinarith [a'.coe_nonneg, b'.coe_nonneg])
  rw [Real.sqrt_sq (by positivity)] at h
  linarith

/-- The `a × b × b` **outer slab model** of a plank–box intersection: the `Prism3D a b b` sharing
`P`'s orthonormal axes, centred at a chosen base point `x₀` (a point of `P ∩ Q`). This mirrors the
repository's `Plank.toSlab`/`Plank.thickened` construction; its center and basis reduce by `rfl`, so
carrier membership unfolds directly through `P.basis.repr`. -/
def plankSlabModel (P : Plank a b hab hb1) (x₀ : EuclideanSpace ℝ (Fin 3)) :
    Prism3D a b b hab le_rfl where
  toPrismNDim := PrismNDim.mk' x₀ P.basis ![a, b, b]
  thicknesses_eq := PrismNDim.thicknesses_mk' _ _ _

@[simp] theorem plankSlabModel_center (P : Plank a b hab hb1) (x₀ : EuclideanSpace ℝ (Fin 3)) :
    (plankSlabModel P x₀).center = x₀ := rfl

@[simp] theorem plankSlabModel_basis (P : Plank a b hab hb1) (x₀ : EuclideanSpace ℝ (Fin 3)) :
    (plankSlabModel P x₀).basis = P.basis := rfl

/-- **Outer containment for the slab model** (the crux of `plankBoxIntersectionIsSlab`): if the base
point `x₀` lies in both `P` and the box `Q`, then `P ∩ Q` is contained in the `6`-dilate of the
slab model `plankSlabModel P x₀`. Coordinates `0, 1` (in `P`'s axes) are controlled by `P` itself;
coordinate `2` is controlled by the diameter of `Q`. -/
lemma plankSlabModel_inter_subset (P : Plank a b hab hb1) (θ : ℝ≥0) (hθ1 : θ ≤ 1)
    (Q : ThetaBox θ b hθ1) {x₀ : EuclideanSpace ℝ (Fin 3)}
    (hx₀P : x₀ ∈ (P.carrier : Set (EuclideanSpace ℝ (Fin 3))))
    (hx₀Q : x₀ ∈ (Q.carrier : Set (EuclideanSpace ℝ (Fin 3)))) :
    ((P.carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩ Q.carrier) ⊆
      ((plankSlabModel P x₀).dilation 6).carrier := by
  have ha0 : (0 : ℝ) ≤ a := a.coe_nonneg
  have hb0 : (0 : ℝ) ≤ b := b.coe_nonneg
  rintro x ⟨hxP, hxQ⟩
  -- coordinate `0`: at most twice the plank's own thickness `a`
  have h0 : |P.basis.repr (x -ᵥ x₀) 0| ≤ ((6 * a : ℝ≥0) : ℝ) := by
    have h := abs_repr_vsub_le_two_mul_thicknesses P.toPrismNDim hxP hx₀P 0
    rw [P.thicknesses_eq] at h
    simp only [Matrix.cons_val_zero, NNReal.coe_mul, NNReal.coe_ofNat] at h ⊢
    linarith
  -- coordinates `1, 2`: controlled by the diameter of the box `Q`
  have hQ : ∀ i, |P.basis.repr (x -ᵥ x₀) i| ≤ ((6 * b : ℝ≥0) : ℝ) := by
    have hd := prism3D_dist_le_four_mul Q hxQ hx₀Q
    have h6b : ((6 * b : ℝ≥0) : ℝ) = 6 * (b : ℝ) := by
      simp only [NNReal.coe_mul, NNReal.coe_ofNat]
    intro i
    refine (abs_repr_vsub_le_dist_basis P.basis x x₀ i).trans ?_
    rw [h6b]
    linarith
  rw [PrismNDim.mem_carrier_iff]
  exact Fin.cases h0 (Fin.cases (hQ 1) (Fin.cases (hQ 2) fun i => i.elim0))

/-- Volume of the `r`-dilate of the slab model: `|r·σ| = 8·(ra)·(rb)·(rb)`. -/
theorem plankSlabModel_dilation_volume (P : Plank a b hab hb1)
    (x₀ : EuclideanSpace ℝ (Fin 3)) (r : ℝ≥0) :
    volume ((plankSlabModel P x₀).dilation r).carrier
      = 8 * ((r : ENNReal) * a) * ((r : ENNReal) * b) * ((r : ENNReal) * b) := by
  rw [PrismNDim.volume_carrier ((plankSlabModel P x₀).dilation r), finrank_euclideanSpace_fin,
    Fin.prod_univ_three]
  simp only [PrismNDim.dilation_thicknesses, (plankSlabModel P x₀).thicknesses_eq,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, ENNReal.coe_mul]
  ring

/-- **Plank angle and induced slab angle are comparable** (`lem:plankSlabAngleComparableAPI`):
the raw dihedral angle between two planks is comparable, up to an absolute factor, to their
effective plank angle (the angle scale used in `findingTypicalAngleOfIntersection`). This
transfers typical-angle information from planks to the local slab family.

The hypothesis `a / b ≤ P₁.planeAngleNN P₂` is essential: without it, nearly-parallel planks have
`planeAngleNN = 0` while `effectivePlankAngle = a / b > 0` (the effective angle is floored at
`a / b`), so no comparability constant can hold. It says the raw angle is at least the resolution
scale `a / b`, which is exactly the regime in which the two notions of angle agree up to a
constant. -/
theorem plankSlabAngleComparable (P₁ P₂ : Plank a b hab hb1)
    (hlb : a / b ≤ P₁.planeAngleNN P₂) :
    ∃ C : ℝ≥0, 1 ≤ C ∧
      Kakeya.ComparableScalars C (P₁.planeAngleNN P₂) (Kakeya.effectivePlankAngle P₁ P₂) := by
  set x := P₁.planeAngleNN P₂
  -- the effective angle collapses to `1 ⊓ x`, since `hlb` makes the `a / b` floor inactive
  have hy : Kakeya.effectivePlankAngle P₁ P₂ = 1 ⊓ x := by
    rw [Kakeya.effectivePlankAngle, sup_eq_right.mpr hlb]
  -- `C = x ⊔ 1` works in both regimes: `(x ⊔ 1) * (1 ⊓ x) = x` and `1 ⊓ x ≤ x ≤ (x ⊔ 1) * x`
  refine ⟨x ⊔ 1, le_sup_right, ?_, ?_⟩ <;> rw [hy]
  · rcases le_total x 1 with h | h
    · rw [inf_eq_right.mpr h, sup_eq_right.mpr h, one_mul]
    · rw [inf_eq_left.mpr h, sup_eq_left.mpr h, mul_one]
  · exact inf_le_right.trans (le_mul_of_one_le_left zero_le le_sup_right)

end Plank

end
