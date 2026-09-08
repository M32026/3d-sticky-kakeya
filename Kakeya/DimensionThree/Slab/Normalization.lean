/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionN.Volume
public import Kakeya.DimensionThree.AffineTransport
public import Kakeya.DimensionThree.Slab.Basic
public import Kakeya.DimensionThree.Volume

/-!
# The slab normalising map

Sections 6.4 and 6.5 of [GWZ] convert the plank family `𝒫_{θ, S}` inside a `θ × 1 × 1` slab `S`
into a family of `b`-tubes in the unit ball "by a linear change of variables". The transport layer
`Kakeya/DimensionThree/AffineTransport.lean` moves shaded convex bodies along an arbitrary
affine automorphism and shows every scale-free incidence quantity is preserved; it says nothing
about *shape*. This file supplies the first half of the missing shape content: the concrete
normalising map itself (blueprint file `GWZAdapted/extra98.tex`, Deliverable 1).

The map is *anisotropic*: it stretches the short axis of the slab by `θ⁻¹` and leaves the two long
axes alone (up to an overall scalar `κ`). It is therefore built as a **frame scaling**: the
translation carrying the centre of the slab to the origin, followed by the linear map that is
diagonal in the slab's own orthonormal frame.

## Main definitions

* `Kakeya.frameDiagLinear`, `Kakeya.frameDiagEquiv`: the linear map
  `D_{B,r} x = ∑ i, r i * ⟪B i, x⟫ • B i` diagonal in an orthonormal frame `B`, and its packaging
  as a linear automorphism when `r` is nowhere zero.
* `Kakeya.frameScaling`: the affine automorphism `F_{c,B,r} x = D_{B,r} (x - c)`.
* `Slab.unitPrism`, `Slab.scaledUnitPrism`: the unit-scale prisms carrying the slab's own axes.
* `Slab.normalize`, `Slab.normalizeScaled`: the normalising map `f_S` of a `θ × 1 × 1` slab and its
  `κ`-scaled variant `f_S^κ`.

## Main statements

* `Kakeya.frameScaling_image_prism`: a frame scaling carries a prism onto a prism.
* `Slab.normalize_image_carrier`, `Slab.normalizeScaled_image_carrier`: `f_S` carries `S` onto the
  unit prism `U_S`, and `f_S^κ` carries `S` onto `U_S^κ`.
* `Slab.affineJacobian_normalize`, `Slab.affineJacobian_normalizeScaled`: the Jacobians are
  `θ⁻¹` and `κ³ θ⁻¹`.
* `Slab.affineJacobian_normalize_mul_volume`,
  `Slab.affineJacobian_normalizeScaled_mul_volume`: the identity `J(f) |S| = |B|` demanded by the
  closing note of `GWZAdapted/extra97.tex`.

## Positivity

In Lean the slab thickness `θ` carries the type `NNReal` and the ambient hypothesis is only
`θ ≤ 1`; nothing in the types supplies `0 < θ`. Every statement below that inverts `θ` or cancels a
factor therefore carries `0 < θ` (and `0 < κ`) as an explicit hypothesis: at `θ = 0` the map `f_S`
does not exist.
-/

@[expose] public section

open MeasureTheory

noncomputable section

/-! ## Diagonal linear maps adapted to an orthonormal frame (`def:frameDiagLinear`) -/

namespace Kakeya

section FrameDiag

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The **frame-diagonal map** `D_{B,r} x = ∑ i, r i * ⟪B i, x⟫ • B i` attached to an orthonormal
basis `B` of `E` and a vector of scaling factors `r : Fin n → ℝ`.

It is the linear map which is diagonal, with diagonal entries `r`, in the frame `B`. -/
def frameDiagLinear (B : OrthonormalBasis (Fin n) ℝ E) (r : Fin n → ℝ) : E →ₗ[ℝ] E :=
  ∑ i, LinearMap.smulRight ((innerSL ℝ (B i)).toLinearMap) (r i • B i)

/-- The defining formula for the frame-diagonal map. -/
theorem frameDiagLinear_apply (B : OrthonormalBasis (Fin n) ℝ E) (r : Fin n → ℝ) (x : E) :
    frameDiagLinear B r x = ∑ i, (r i * inner ℝ (B i) x) • B i := by
  simp [frameDiagLinear, smul_smul, mul_comm]

/-! ### Coordinates and norm of a frame-diagonal image (`lem:frameDiagCoords`) -/

/-- The `i`-th coordinate of `D_{B,r} x` in the frame `B` is `r i` times the `i`-th coordinate
of `x`. -/
theorem repr_frameDiagLinear (B : OrthonormalBasis (Fin n) ℝ E) (r : Fin n → ℝ) (x : E)
    (i : Fin n) : B.repr (frameDiagLinear B r x) i = r i * B.repr x i := by
  rw [OrthonormalBasis.repr_apply_apply, OrthonormalBasis.repr_apply_apply]
  rw [frameDiagLinear_apply, inner_sum, Finset.sum_eq_single i]
  · simp [real_inner_smul_right]
  · intro j _ hj
    simp [real_inner_smul_right, Ne.symm hj]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- Parseval for a frame-diagonal image: `‖D_{B,r} x‖² = ∑ i, r i ² * ⟪B i, x⟫²`. -/
theorem norm_sq_frameDiagLinear (B : OrthonormalBasis (Fin n) ℝ E) (r : Fin n → ℝ) (x : E) :
    ‖frameDiagLinear B r x‖ ^ 2 = ∑ i, (r i) ^ 2 * (B.repr x i) ^ 2 := by
  calc
    ‖frameDiagLinear B r x‖ ^ 2 = ∑ i, (B.repr (frameDiagLinear B r x) i) ^ 2 := by
      rw [← OrthonormalBasis.sum_sq_inner_left (b := B) (x := frameDiagLinear B r x)]
      congr
      ext i
      rw [OrthonormalBasis.repr_apply_apply, real_inner_comm]
    _ = ∑ i, (r i * B.repr x i) ^ 2 := by
      congr
      ext i
      rw [repr_frameDiagLinear]
    _ = ∑ i, (r i) ^ 2 * (B.repr x i) ^ 2 := by
      congr
      ext i
      simp only [mul_pow]

/-! ### Determinant of a frame-diagonal map (`lem:frameDiagDet`) -/

/-- The determinant of a frame-diagonal map is the product of its diagonal entries: its matrix in
the basis `B` is `diagonal r`. -/
theorem det_frameDiagLinear (B : OrthonormalBasis (Fin n) ℝ E) (r : Fin n → ℝ) :
    LinearMap.det (frameDiagLinear B r) = ∏ i, r i := by
  haveI : FiniteDimensional ℝ E := Module.Basis.finiteDimensional_of_finite B.toBasis
  rw [← LinearMap.det_toMatrix B.toBasis]
  have hmat : LinearMap.toMatrix B.toBasis B.toBasis (frameDiagLinear B r) = Matrix.diagonal r := by
    ext i j
    simp [LinearMap.toMatrix_apply, repr_frameDiagLinear, Matrix.diagonal]
  rw [hmat]
  exact Matrix.det_diagonal

/-- The **frame-diagonal automorphism**: when `r` is nowhere zero, `D_{B,r}` is a linear
automorphism of `E`, with inverse `D_{B, r⁻¹}`. -/
def frameDiagEquiv (B : OrthonormalBasis (Fin n) ℝ E) (r : Fin n → ℝ) (hr : ∀ i, r i ≠ 0) :
    E ≃ₗ[ℝ] E :=
  LinearEquiv.ofLinear (frameDiagLinear B r) (frameDiagLinear B fun i => (r i)⁻¹)
    (by
      apply LinearMap.ext
      intro x
      apply B.repr.injective
      ext i
      rw [LinearMap.comp_apply, LinearMap.id_apply]
      rw [repr_frameDiagLinear, repr_frameDiagLinear]
      rw [← mul_assoc, mul_inv_cancel₀ (hr i), one_mul])
    (by
      apply LinearMap.ext
      intro x
      apply B.repr.injective
      ext i
      rw [LinearMap.comp_apply, LinearMap.id_apply]
      rw [repr_frameDiagLinear, repr_frameDiagLinear]
      rw [← mul_assoc, inv_mul_cancel₀ (hr i), one_mul])

/-- The underlying linear map of `Kakeya.frameDiagEquiv` is `Kakeya.frameDiagLinear`. -/
@[simp]
theorem coe_frameDiagEquiv (B : OrthonormalBasis (Fin n) ℝ E) (r : Fin n → ℝ) (hr : ∀ i, r i ≠ 0) :
    (frameDiagEquiv B r hr : E →ₗ[ℝ] E) = frameDiagLinear B r := rfl

end FrameDiag

/-! ## The frame-diagonal affine automorphism (`def:frameScaling`) -/

section FrameScaling

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The **frame scaling** `F_{c,B,r} x = D_{B,r} (x - c)`: the translation carrying `c` to the
origin, followed by the frame-diagonal automorphism `D_{B,r}`.

This is the shape of every change of variables performed in Sections 6.4 and 6.5: it is assembled
from `AffineEquiv.constVAdd` and `LinearEquiv.toAffineEquiv`, so that its linear part — and hence
its Jacobian — can be read off directly. -/
def frameScaling (c : E) (B : OrthonormalBasis (Fin n) ℝ E) (r : Fin n → ℝ) (hr : ∀ i, r i ≠ 0) :
    E ≃ᵃ[ℝ] E :=
  (AffineEquiv.constVAdd ℝ E (-c)).trans (frameDiagEquiv B r hr).toAffineEquiv

/-- The pointwise formula for a frame scaling. -/
@[simp]
theorem frameScaling_apply (c : E) (B : OrthonormalBasis (Fin n) ℝ E) (r : Fin n → ℝ)
    (hr : ∀ i, r i ≠ 0) (x : E) :
    frameScaling c B r hr x = frameDiagLinear B r (x - c) := by
  simp [frameScaling, frameDiagEquiv, sub_eq_neg_add]

/-- The linear part of a frame scaling is the frame-diagonal automorphism. -/
@[simp]
theorem frameScaling_linear (c : E) (B : OrthonormalBasis (Fin n) ℝ E) (r : Fin n → ℝ)
    (hr : ∀ i, r i ≠ 0) :
    (frameScaling c B r hr).linear = frameDiagEquiv B r hr := rfl

/-- A frame scaling sends its centre to the origin. -/
theorem frameScaling_center (c : E) (B : OrthonormalBasis (Fin n) ℝ E) (r : Fin n → ℝ)
    (hr : ∀ i, r i ≠ 0) : frameScaling c B r hr c = 0 := by
  simp

/-! ### Jacobian of a frame scaling (`lem:frameScalingJacobian`) -/

/-- The Jacobian of a frame scaling is `|∏ i, r i|`: its linear part is `D_{B,r}`, whose
determinant is `∏ i, r i`. -/
theorem affineJacobian_frameScaling (c : E) (B : OrthonormalBasis (Fin n) ℝ E) (r : Fin n → ℝ)
    (hr : ∀ i, r i ≠ 0) :
    affineJacobian (frameScaling c B r hr) = ENNReal.ofReal |∏ i, r i| := by
  rw [affineJacobian, frameScaling_linear, coe_frameDiagEquiv, det_frameDiagLinear]

end FrameScaling

end Kakeya

/-! ## Coordinates of a point of a prism (`lem:prismRepr`)

These two lemmas are about `PrismNDim` alone and would naturally live in
`Kakeya/DimensionN/Prism.lean`; they are declared here only because this region may not edit that
file. Moving them is a pure cleanup. -/

namespace PrismNDim

variable {n : ℕ} {E S : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [PseudoMetricSpace S] [NormedAddTorsor E S]

/-- A point of a prism is its centre plus a combination of the axes with coefficients bounded by
the half-widths, the coefficients being the inner products with the axes. -/
theorem exists_repr_of_mem (P : PrismNDim n E S) {x : S} (hx : x ∈ P.carrier) :
    ∃ a : Fin n → ℝ, (∀ i, |a i| ≤ P.thicknesses i) ∧
      (∀ i, a i = inner ℝ (P.basis i) (x -ᵥ P.center)) ∧
      x = (∑ i, a i • P.basis i) +ᵥ P.center := by
  refine ⟨fun i => P.basis.repr (x -ᵥ P.center) i, (P.mem_carrier_iff x).mp hx, fun i => ?_, ?_⟩
  · exact P.basis.repr_apply_apply (x -ᵥ P.center) i
  · rw [P.basis.sum_repr (x -ᵥ P.center), vsub_vadd]

/-- Conversely, the centre plus a combination of the axes with coefficients bounded by the
half-widths lies in the prism. -/
theorem mem_carrier_of_repr (P : PrismNDim n E S) (a : Fin n → ℝ)
    (ha : ∀ i, |a i| ≤ P.thicknesses i) :
    ((∑ i, a i • P.basis i) +ᵥ P.center) ∈ P.carrier := by
  rw [P.mem_carrier_iff]
  intro j
  simp only [vadd_vsub]
  have h : inner ℝ (P.basis j) (∑ i, a i • P.basis i) = a j := by
    rw [inner_sum Finset.univ (fun i => a i • P.basis i) (P.basis j)]
    rw [Finset.sum_eq_single j]
    · rw [real_inner_smul_right]
      rw [real_inner_self_eq_norm_sq, P.basis.norm_eq_one]
      norm_num
    · intro i _ hij
      rw [real_inner_smul_right, P.basis.inner_eq_zero (by exact hij.symm)]
      norm_num
    · intro hj
      simp at hj
  rw [P.basis.repr_apply_apply]
  rw [h]
  exact ha j

end PrismNDim

/-! ## A frame scaling carries a prism onto a prism (`lem:frameScalingImagePrism`) -/

namespace Kakeya

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Apply `D_{B,r}` after `D_{B,r⁻¹}`: the inverse round-trip for the frame-diagonal map. -/
private lemma frameDiagLinear_inv_round (B : OrthonormalBasis (Fin n) ℝ E) (r : Fin n → ℝ)
    (hr : ∀ i, r i ≠ 0) (x : E) :
    frameDiagLinear B r (frameDiagLinear B (fun i => (r i)⁻¹) x) = x := by
  apply B.repr.injective
  ext i
  rw [repr_frameDiagLinear, repr_frameDiagLinear]
  rw [← mul_assoc, mul_inv_cancel₀ (hr i), one_mul]

/-- The frame scaling built from the centre and the axes of a prism `P` carries `P` **onto** the
prism with centre `0`, the *same* axes, and half-widths `|r i| * P.thicknesses i`.

No ordering of the `|r i| * P.thicknesses i` is required, since `PrismNDim` — unlike `Prism3D` —
imposes none. -/
theorem frameScaling_image_prism (P : PrismNDim n E E) (r : Fin n → ℝ) (hr : ∀ i, r i ≠ 0) :
    (frameScaling P.center P.basis r hr) '' P.carrier
      = (PrismNDim.mk' (0 : E) P.basis fun i => Real.toNNReal |r i| * P.thicknesses i).carrier := by
  set Q := PrismNDim.mk' (0 : E) P.basis fun i => Real.toNNReal |r i| * P.thicknesses i
  have hQthick (i : Fin n) : (Q.thicknesses i : ℝ) = |r i| * (P.thicknesses i : ℝ) := by
    simp [Q, PrismNDim.thicknesses_mk']
  ext y
  constructor
  · rintro ⟨x, hx, hxy⟩
    rw [P.mem_carrier_iff] at hx
    rw [Q.mem_carrier_iff]
    intro i
    have hyeq : y = frameDiagLinear P.basis r (x - P.center) := by
      rw [← hxy, frameScaling_apply]
    calc
      |P.basis.repr (y - 0) i| = |P.basis.repr (frameDiagLinear P.basis r (x - P.center)) i| := by
        rw [hyeq, sub_zero]
      _ = |r i * P.basis.repr (x - P.center) i| := by rw [repr_frameDiagLinear]
      _ = |r i| * |P.basis.repr (x - P.center) i| := by rw [abs_mul]
      _ ≤ |r i| * (P.thicknesses i : ℝ) := by gcongr; exact hx i
      _ = (Q.thicknesses i : ℝ) := by symm; exact hQthick i
  · intro hy
    rw [Q.mem_carrier_iff] at hy
    set x := frameDiagLinear P.basis (fun i => (r i)⁻¹) (y - 0) + P.center
    have h_xsub : x - P.center = frameDiagLinear P.basis (fun i => (r i)⁻¹) (y - 0) := by
      simp [x]
    have hx_mem : x ∈ P.carrier := by
      rw [P.mem_carrier_iff]
      intro i
      calc
        |P.basis.repr (x - P.center) i| = |(r i)⁻¹ * P.basis.repr (y - 0) i| := by
          rw [h_xsub, repr_frameDiagLinear]
        _ = |(r i)⁻¹| * |P.basis.repr (y - 0) i| := by rw [abs_mul]
        _ = (|r i|)⁻¹ * |P.basis.repr (y - 0) i| := by rw [abs_inv]
        _ ≤ (|r i|)⁻¹ * (Q.thicknesses i : ℝ) := by gcongr; exact hy i
        _ = (|r i|)⁻¹ * (|r i| * (P.thicknesses i : ℝ)) := by rw [hQthick i]
        _ = (P.thicknesses i : ℝ) := by
          rw [← mul_assoc, inv_mul_cancel₀ (abs_ne_zero.mpr (hr i)), one_mul]
    have h_image : frameScaling P.center P.basis r hr x = y := by
      calc
        frameScaling P.center P.basis r hr x = frameDiagLinear P.basis r (x - P.center) := by
          rw [frameScaling_apply]
        _ = frameDiagLinear P.basis r (frameDiagLinear P.basis (fun i => (r i)⁻¹) (y - 0)) := by
          rw [h_xsub]
        _ = y - 0 := frameDiagLinear_inv_round P.basis r hr (y - 0)
        _ = y := by simp
    exact ⟨x, hx_mem, h_image⟩

end Kakeya

/-! ## Deliverable 1: the slab normalising map (`def:slabNormalize`) -/

namespace Slab

open Kakeya

variable {θ : NNReal} {hθ : θ ≤ 1}

/-- The **unit prism** of a slab `S`: the cube of half-width `1` centred at the origin carrying
`S`'s own orthonormal axes. This is the unit-scale body that `Slab.normalize` sends `S` onto; it
plays the role of the ball `B₁` of the paper. -/
def unitPrism (S : Slab θ hθ) :
    PrismNDim 3 (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3)) :=
  PrismNDim.mk' 0 S.basis ![1, 1, 1]

/-- The **`κ`-scaled unit prism** of a slab `S`: the cube of half-width `κ` centred at the origin
carrying `S`'s own orthonormal axes. -/
def scaledUnitPrism (S : Slab θ hθ) (κ : NNReal) :
    PrismNDim 3 (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3)) :=
  PrismNDim.mk' 0 S.basis ![κ, κ, κ]

/-- The **`κ`-scaled normalising map** `f_S^κ` of a `θ × 1 × 1` slab `S`: the frame scaling that
translates the centre of `S` to the origin, stretches by `κ θ⁻¹` along the short axis `e₀`, and
scales by `κ` along the two long axes `e₁, e₂`. -/
def normalizeScaled (S : Slab θ hθ) (κ : NNReal) (hθ0 : 0 < θ) (hκ : 0 < κ) :
    EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin 3) :=
  frameScaling S.center S.basis ![(κ : ℝ) * (θ : ℝ)⁻¹, (κ : ℝ), (κ : ℝ)] (by
    have hθ' : ((θ : ℝ)) ≠ 0 := ne_of_gt (NNReal.coe_pos.mpr hθ0)
    have hκ' : ((κ : ℝ)) ≠ 0 := ne_of_gt (NNReal.coe_pos.mpr hκ)
    intro i
    fin_cases i <;> simp [hθ', hκ'])

/-- The **normalising map** `f_S = f_S^1` of a `θ × 1 × 1` slab `S`: it translates the centre of
`S` to the origin and stretches by `θ⁻¹` along the short axis, fixing the lengths along the two
long axes. -/
def normalize (S : Slab θ hθ) (hθ0 : 0 < θ) :
    EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin 3) :=
  normalizeScaled S 1 hθ0 one_pos

/-! ### The `κ`-scaled normalising map (`lem:slabNormalizeScaled`) -/

/-- The `κ`-scaled normalising map carries the slab onto the `κ`-scaled unit prism. -/
theorem normalizeScaled_image_carrier (S : Slab θ hθ) (κ : NNReal) (hθ0 : 0 < θ) (hκ : 0 < κ) :
    (normalizeScaled S κ hθ0 hκ) '' S.carrier = (scaledUnitPrism S κ).carrier := by
  set r : Fin 3 → ℝ := ![(κ : ℝ) * (θ : ℝ)⁻¹, (κ : ℝ), (κ : ℝ)]
  rw [normalizeScaled, scaledUnitPrism]
  rw [frameScaling_image_prism S.toPrismNDim r]
  have hthick : (fun i : Fin 3 => Real.toNNReal |r i| * S.thicknesses i) = ![κ, κ, κ] := by
    funext i
    fin_cases i
    · simp [r, S.thicknesses_eq]
      apply NNReal.coe_inj.mp
      push_cast
      rw [Real.coe_toNNReal ((κ : ℝ) * (θ : ℝ)⁻¹)
        (mul_nonneg (NNReal.coe_nonneg κ) (inv_nonneg.mpr (NNReal.coe_nonneg θ)))]
      rw [mul_assoc, inv_mul_cancel₀ (ne_of_gt (NNReal.coe_pos.mpr hθ0)), mul_one]
    · simp [r, S.thicknesses_eq]
    · simp [r, S.thicknesses_eq]
  rw [hthick]

/-! ### `f_S` normalises `S` to unit scale (`lem:slabNormalizeImage`) -/

/-- The normalising map carries the slab onto its unit prism. -/
theorem normalize_image_carrier (S : Slab θ hθ) (hθ0 : 0 < θ) :
    (normalize S hθ0) '' S.carrier = (unitPrism S).carrier := by
  simpa [normalize, unitPrism, scaledUnitPrism] using normalizeScaled_image_carrier S 1 hθ0 one_pos

/-- Consequently the normalised slab lies in the closed ball of radius `3` about the origin: a
prism is contained in the closed ball about its centre of radius the sum of its half-widths, here
`1 + 1 + 1`. -/
theorem image_carrier_subset_closedBall (S : Slab θ hθ) (hθ0 : 0 < θ) :
    (normalize S hθ0) '' S.carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 3 := by
  rw [normalize_image_carrier]
  convert PrismNDim.carrier_subset_closedBall (unitPrism S) using 2
  · simp [unitPrism, PrismNDim.center_mk']
  · rw [unitPrism]
    simp [PrismNDim.thicknesses_mk', Fin.sum_univ_three]
    norm_num

/-! ### Volumes of the unit prisms -/

/-- The unit prism has volume `2³ = 8`. -/
theorem volume_unitPrism (S : Slab θ hθ) : volume (unitPrism S).carrier = 8 := by
  rw [unitPrism, PrismNDim.volume_carrier, finrank_euclideanSpace_fin]
  simp [Fin.prod_univ_three, PrismNDim.thicknesses_mk']
  norm_num

/-- The `κ`-scaled unit prism has volume `8 κ³`. -/
theorem volume_scaledUnitPrism (S : Slab θ hθ) (κ : NNReal) :
    volume (scaledUnitPrism S κ).carrier = 8 * (κ : ENNReal) ^ 3 := by
  rw [PrismNDim.volume_carrier]
  rw [finrank_euclideanSpace_fin]
  rw [Fin.prod_univ_three]
  simp [scaledUnitPrism, PrismNDim.thicknesses_mk']
  ring

/-! ### Jacobian of the normalising map (`lem:slabNormalizeJacobian`) -/

/-- The Jacobian of the normalising map is `θ⁻¹`. -/
theorem affineJacobian_normalize (S : Slab θ hθ) (hθ0 : 0 < θ) :
    affineJacobian (normalize S hθ0) = ENNReal.ofReal ((θ : ℝ)⁻¹) := by
  rw [normalize, normalizeScaled, affineJacobian_frameScaling]
  rw [Fin.prod_univ_three]
  rw [abs_of_nonneg]
  · simp [one_mul, mul_one]
  · simp [one_mul, mul_one, inv_nonneg.mpr (NNReal.coe_nonneg θ)]

/-- The identity `J(f_S) |S| = |U_S|` flagged by the closing note of `GWZAdapted/extra97.tex` as
needed by the consumers, with the unit-scale prism `U_S` (of volume `8`) in the role of `B₁`.
Since `|S| = 8θ` and `|U_S| = 8`, this is exactly `J(f_S) = |U_S| / |S|`. -/
theorem affineJacobian_normalize_mul_volume (S : Slab θ hθ) (hθ0 : 0 < θ) :
    affineJacobian (normalize S hθ0) * volume S.carrier = volume (unitPrism S).carrier := by
  rw [← volume_image_affineEquiv, normalize_image_carrier]

/-- The Jacobian of the `κ`-scaled normalising map is `κ³ θ⁻¹`. -/
theorem affineJacobian_normalizeScaled (S : Slab θ hθ) (κ : NNReal) (hθ0 : 0 < θ) (hκ : 0 < κ) :
    affineJacobian (normalizeScaled S κ hθ0 hκ) = ENNReal.ofReal ((κ : ℝ) ^ 3 * (θ : ℝ)⁻¹) := by
  rw [normalizeScaled, affineJacobian_frameScaling]
  congr 1
  rw [Fin.prod_univ_three]
  simp
  ring

/-- The identity `J(f_S^κ) |S| = |U_S^κ| = 8 κ³`. This is the form of `J = |B| / |S|` that the
consumers actually use, since the map they apply is `f_S^κ` and not `f_S`. -/
theorem affineJacobian_normalizeScaled_mul_volume (S : Slab θ hθ) (κ : NNReal) (hθ0 : 0 < θ)
    (hκ : 0 < κ) :
    affineJacobian (normalizeScaled S κ hθ0 hκ) * volume S.carrier = 8 * (κ : ENNReal) ^ 3 := by
  rw [← volume_image_affineEquiv, normalizeScaled_image_carrier, volume_scaledUnitPrism]

/-- The `C`-dilation of the slab, of half-widths `(Cθ, C, C)`, is carried onto the prism of
half-widths `(κC, κC, κC)`, hence into the closed ball of radius `3 κ C`.

This is what places the image of the centre of a tangential plank near the origin in
`lem:plankToTube`. -/
theorem normalizeScaled_image_dilation_subset_closedBall (S : Slab θ hθ) (κ C : NNReal)
    (hθ0 : 0 < θ) (hκ : 0 < κ) :
    (normalizeScaled S κ hθ0 hκ) '' (S.toPrismNDim.dilation C).carrier
      ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (3 * (κ : ℝ) * (C : ℝ)) := by
  set r : Fin 3 → ℝ := ![(κ : ℝ) * (θ : ℝ)⁻¹, (κ : ℝ), (κ : ℝ)]
  have himage : (normalizeScaled S κ hθ0 hκ) '' (S.toPrismNDim.dilation C).carrier =
      (PrismNDim.mk' (0 : EuclideanSpace ℝ (Fin 3)) S.basis ![κ * C, κ * C, κ * C]).carrier := by
    rw [normalizeScaled]
    rw [show S.center = (S.toPrismNDim.dilation C).center by
            rw [PrismNDim.dilation_center],
        show S.basis = (S.toPrismNDim.dilation C).basis by
            rw [PrismNDim.dilation_basis]]
    rw [frameScaling_image_prism (S.toPrismNDim.dilation C) r]
    simp only [PrismNDim.dilation_basis, PrismNDim.dilation_thicknesses]
    have hthick : (fun i : Fin 3 =>
          Real.toNNReal |r i| * (C * S.thicknesses i)) = ![κ * C, κ * C, κ * C] := by
      funext i
      fin_cases i
      · simp [r, S.thicknesses_eq]
        apply NNReal.coe_inj.mp
        push_cast
        rw [Real.coe_toNNReal ((κ : ℝ) * (θ : ℝ)⁻¹)
          (mul_nonneg (NNReal.coe_nonneg κ) (inv_nonneg.mpr (NNReal.coe_nonneg θ)))]
        calc
          ((κ : ℝ) * (θ : ℝ)⁻¹) * (↑C * ↑θ) = (κ : ℝ) * ((θ : ℝ)⁻¹ * ↑θ) * ↑C := by ring
          _ = (κ : ℝ) * 1 * ↑C := by
            rw [inv_mul_cancel₀ (ne_of_gt (NNReal.coe_pos.mpr hθ0))]
          _ = ↑κ * ↑C := by ring
      · simp [r, S.thicknesses_eq]
      · simp [r, S.thicknesses_eq]
    rw [hthick]
  rw [himage]
  convert PrismNDim.carrier_subset_closedBall
    (PrismNDim.mk' (0 : EuclideanSpace ℝ (Fin 3)) S.basis ![κ * C, κ * C, κ * C]) using 2
  · rfl
  · rw [Fin.sum_univ_three]
    simp [PrismNDim.thicknesses_mk', NNReal.coe_mul]
    ring_nf

end Slab

end

end
