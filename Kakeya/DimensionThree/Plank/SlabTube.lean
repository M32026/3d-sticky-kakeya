/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.Geometry
public import Kakeya.DimensionThree.Slab.Normalization
public import Kakeya.Tube.Basic
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The tangential plank to tube conversion

GWZ dispose of the following step in one sentence, just before the proofs of Lemma 6.1 and
Lemma 6.4:

> "By a linear change of variables, we can convert `𝒫_{θ, S}` from a set of `θb × b × 1` planks in
> `S` into a set `𝒯` of `b`-tubes in `B₁`. … Let `L : S → B₁` be a linear change of variables.
> Because of the tangency condition on `P`, `L(P)` has dimensions `b × b × 1`."

`Kakeya/DimensionThree/AffineTransport.lean` supplies the measure-theoretic transport
layer and `Kakeya/DimensionThree/Slab/Normalization.lean` the normalising map `f_S^κ`.
This file supplies the remaining geometric content (blueprint file `GWZAdapted/extra98.tex`,
Deliverable 2): the tangency estimates, the conversion of a single tangential thickened plank into
a `b/8`-tube in the closed unit ball, and the family-level interface consumed by Lemma 6.1 and
Lemma 6.4.

## Two honest deviations from the informal sentence

*The conversion is one-sided.* `Tube δ E` is the closed `δ`-neighbourhood of a segment of length
*exactly* `1`, whereas the image `g(P_θ)` has diameter at most `3/8`. So no image contains a
`c b`-tube, for any `c`. The reverse containment is therefore replaced by the exact volume identity
`Plank.volume_image_normalizeScaled_thickened` together with the tube volume upper bound
`Tube.volume_carrier_le`; the pair says the tube exceeds the image by at most an explicit absolute
factor, which is what the reverse containment was wanted for.

*Essential distinctness does not transfer.* It is destroyed by the inflation from the image to the
enclosing tube, not inherited from the planks; see the closing note of `GWZAdapted/extra98.tex`.

## Main definitions

* `Plank.slabTubeConst`: the conversion constant `κ = 1 / (16 (1 + Cang) (1 + Cset))`.
* `Plank.slabTubeDir`, `Plank.slabTube`: the `b/8`-tube attached to a normalised plank.
* `Plank.slabShadedTube`, `Plank.defaultShadedTube`, `Plank.slabTubeFamily`: the tube family
  attached to a tangential plank family in a slab.

## Main statements

* `Plank.image_carrier_subset_slabTube`, `Plank.slabTube_carrier_subset_closedBall`: a tangential
  thickened plank normalises into a `b/8`-tube in the closed unit ball.
* `Plank.slabTubeFamily_carrier_subset_closedBall`, `Plank.slabTubeFamily_shade`,
  `Plank.image_thickened_subset_slabTubeFamily`: the family-level interface.
* `Plank.multiplicity_slabTubeFamily`: `μ` is preserved exactly.
* `Plank.fullness_le_slabTubeFamily`: `λ` is preserved up to the explicit factor
  `C_vol = 40 (1 + Cang)³ (1 + Cset)³`.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

noncomputable section

/-! ## Tangency (`lem:inSlabFamilyCInputs`, `lem:tangentialTransversality`) -/

namespace Plank

variable {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {θ : ℝ≥0} {hθ : θ ≤ 1} {ι : Type*}

/-- Membership in the controlled slab subfamily `𝒫_S^{Cset,Cang}` gives the containment of the
plank's **centre** in the `Cset`-dilation of the slab.

The containment is stated on the centre and not on the whole thickened plank on purpose:
`Plank.inSlabFamilyC` constrains the plank `V i`, not its thickening, and
`(V i).thickened θ ⊆ S^(Cset)` is in general false since thickening enlarges the short axis from
`a` to `θ b`. Only the centre — which is all the conversion needs — transfers. -/
theorem center_mem_slabDilation_of_inSlabFamilyC {Cset Cang : ℝ≥0} {s : Finset ι}
    {V : ι → Plank a b hab hb1} {S : Slab θ hθ} {i : ι}
    (hi : i ∈ inSlabFamilyC Cset Cang s V S) :
    (V i).center ∈ (S.toPrismNDim.dilation Cset).carrier := by
  have hsub : (V i).carrier ⊆ (S.toPrismNDim.dilation Cset).carrier :=
    (mem_inSlabFamilyC.mp hi).2.1
  exact hsub (V i).toPrismNDim.center_mem_carrier

/-- Thickening does not change the angle with the slab: `Plank.thickened` preserves the frame, and
`Prism3D.angle` only sees `basis 0`. -/
theorem angle_thickened_eq (P : Plank a b hab hb1) (S : Slab θ hθ) :
    Prism3D.angle (P.thickened θ hθ) S = Prism3D.angle P S := by
  simp [Prism3D.angle]

/-- **Tangency forces transversality of the two long axes.** If `∠(TP, TS) ≤ Cang · θ` then the two
axes `u₁, u₂` of `P` along which the thickened plank is *long* are nearly orthogonal to the one
direction `e₀ = S.basis 0` that the normalising map stretches.

This is the only place where the angle hypothesis is consumed, and it is the crux of the whole
conversion: were `P` transverse to `S`, the long axis `u₂` would have `|⟪e₀, u₂⟫| ≈ 1` and its
image would have length `≈ κ θ⁻¹` rather than `≈ κ`. -/
theorem inner_sq_slabNormal_add_le (P : Plank a b hab hb1) (S : Slab θ hθ) {Cang : ℝ≥0}
    (hang : Prism3D.angle P S ≤ (Cang : ℝ) * (θ : ℝ)) :
    inner ℝ (S.basis 0) (P.basis 1) ^ 2 + inner ℝ (S.basis 0) (P.basis 2) ^ 2
      ≤ ((Cang : ℝ) * (θ : ℝ)) ^ 2 := by
  -- The whole content is the scalar fact `1 - x² = sin (arccos x)² ≤ (arccos x)² ≤ t²`,
  -- kept on plain reals so that no arithmetic runs on inner-product terms.
  have key : ∀ x y z t : ℝ, x ^ 2 + y ^ 2 + z ^ 2 = 1 → Real.arccos |x| ≤ t →
      y ^ 2 + z ^ 2 ≤ t ^ 2 := by
    intro x y z t hxyz h
    have hnn : 0 ≤ 1 - |x| ^ 2 := by linarith [sq_abs x, sq_nonneg y, sq_nonneg z]
    have hle : Real.sqrt (1 - |x| ^ 2) ≤ t :=
      le_trans (by rw [← Real.sin_arccos]; exact Real.sin_le (Real.arccos_nonneg _)) h
    have hsq := mul_self_le_mul_self (Real.sqrt_nonneg (1 - |x| ^ 2)) hle
    rw [← pow_two, ← pow_two, Real.sq_sqrt hnn] at hsq
    linarith [sq_abs x]
  rw [Prism3D.angle_def] at hang
  refine key (inner ℝ (S.basis 0) (P.basis 0)) _ _ _ ?_ (by rwa [real_inner_comm])
  have hsum := OrthonormalBasis.sum_sq_inner_left (b := P.basis) (x := S.basis 0)
  rwa [Fin.sum_univ_three, OrthonormalBasis.norm_eq_one S.basis 0, one_pow] at hsum

/-- The pointwise form of `Plank.inner_sq_slabNormal_add_le`: each of the two long axes of a
tangential plank makes an inner product of size at most `Cang · θ` with the normal of the slab. -/
theorem abs_inner_slabNormal_basis_le (P : Plank a b hab hb1) (S : Slab θ hθ) {Cang : ℝ≥0}
    (hang : Prism3D.angle P S ≤ (Cang : ℝ) * (θ : ℝ)) {j : Fin 3} (hj : j ≠ 0) :
    |inner ℝ (S.basis 0) (P.basis j)| ≤ (Cang : ℝ) * (θ : ℝ) := by
  have hsum := inner_sq_slabNormal_add_le P S hang
  refine abs_le_of_sq_le_sq ?_ (mul_nonneg (NNReal.coe_nonneg Cang) (NNReal.coe_nonneg θ))
  rcases (show j = 1 ∨ j = 2 by omega) with rfl | rfl
  · linarith [sq_nonneg (inner ℝ (S.basis 0) (P.basis 2))]
  · linarith [sq_nonneg (inner ℝ (S.basis 0) (P.basis 1))]

/-! ## The image lengths of the three plank axes (`lem:normImageAxes`) -/

/-- The exact length of the image of a unit vector under the linear part `L` of `f_S^κ`:
`‖L u‖² = κ² (1 + (θ⁻² - 1) ⟪e₀, u⟫²)`. Everything below about image lengths is read off from
this identity, which carries no tangency hypothesis. -/
theorem norm_sq_normalizeScaled_linear (S : Slab θ hθ) (κ : ℝ≥0) (hθ0 : 0 < θ) (hκ : 0 < κ)
    {u : EuclideanSpace ℝ (Fin 3)} (hu : ‖u‖ = 1) :
    ‖(Slab.normalizeScaled S κ hθ0 hκ).linear u‖ ^ 2
      = (κ : ℝ) ^ 2 * (1 + (((θ : ℝ)⁻¹) ^ 2 - 1) * inner ℝ (S.basis 0) u ^ 2) := by
  have hs := OrthonormalBasis.sum_sq_inner_left (b := S.basis) (x := u)
  rw [hu, one_pow, Fin.sum_univ_three] at hs
  rw [real_inner_comm (S.basis 0) u, real_inner_comm (S.basis 1) u,
    real_inner_comm (S.basis 2) u] at hs
  rw [show (Slab.normalizeScaled S κ hθ0 hκ).linear u
        = Kakeya.frameDiagLinear S.basis ![(κ : ℝ) * (θ : ℝ)⁻¹, (κ : ℝ), (κ : ℝ)] u from rfl,
    Kakeya.norm_sq_frameDiagLinear, Fin.sum_univ_three]
  simp only [OrthonormalBasis.repr_apply_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  linear_combination (κ : ℝ) ^ 2 * hs

/-- The hypothesis-free lower bound `κ ≤ ‖L u‖` for a unit vector `u`: it is attained exactly when
`u` lies in the long plane of `S`. This is what makes the tube direction of `Plank.slabTubeDir`
well defined and the axial rescaling harmless. -/
theorem le_norm_normalizeScaled_linear (S : Slab θ hθ) (κ : ℝ≥0) (hθ0 : 0 < θ) (hκ : 0 < κ)
    {u : EuclideanSpace ℝ (Fin 3)} (hu : ‖u‖ = 1) :
    (κ : ℝ) ≤ ‖(Slab.normalizeScaled S κ hθ0 hκ).linear u‖ := by
  have hth : 1 ≤ ((θ : ℝ)⁻¹) ^ 2 :=
    one_le_pow₀ ((one_le_inv₀ (NNReal.coe_pos.mpr hθ0)).mpr (NNReal.coe_le_coe.mpr hθ))
  refine (le_abs_self _).trans (abs_le_of_sq_le_sq ?_ (norm_nonneg _))
  rw [norm_sq_normalizeScaled_linear S κ hθ0 hκ hu]
  linarith [mul_nonneg (mul_nonneg (sq_nonneg (κ : ℝ)) (sub_nonneg.mpr hth))
    (sq_nonneg (inner ℝ (S.basis 0) u))]

/-- The hypothesis-free upper bound `‖L u‖ ≤ κ θ⁻¹` for a unit vector `u`, attained on the short
axis of `S`. This is the bound used for the short axis `u₀` of the plank. -/
theorem norm_normalizeScaled_linear_le (S : Slab θ hθ) (κ : ℝ≥0) (hθ0 : 0 < θ) (hκ : 0 < κ)
    {u : EuclideanSpace ℝ (Fin 3)} (hu : ‖u‖ = 1) :
    ‖(Slab.normalizeScaled S κ hθ0 hκ).linear u‖ ≤ (κ : ℝ) * (θ : ℝ)⁻¹ := by
  have hθℝ : 0 < (θ : ℝ) := NNReal.coe_pos.mpr hθ0
  have hX : 1 ≤ ((θ : ℝ)⁻¹) ^ 2 := by
    rw [inv_pow]
    exact (one_le_inv₀ (by positivity)).mpr
      (by nlinarith [show (θ : ℝ) ≤ 1 from NNReal.coe_le_coe.mpr hθ])
  have hq : inner ℝ (S.basis 0) u ^ 2 ≤ 1 := by
    have h := abs_real_inner_le_norm (S.basis 0) u
    rw [OrthonormalBasis.norm_eq_one, hu, one_mul] at h
    exact (sq_abs _).symm.trans_le (pow_le_one₀ (abs_nonneg _) h)
  have hsq : ‖(Slab.normalizeScaled S κ hθ0 hκ).linear u‖ ^ 2 ≤ ((κ : ℝ) * (θ : ℝ)⁻¹) ^ 2 := by
    rw [norm_sq_normalizeScaled_linear S κ hθ0 hκ hu, mul_pow]
    nlinarith [mul_nonneg (sq_nonneg (κ : ℝ))
      (mul_nonneg (sub_nonneg.mpr hX) (sub_nonneg.mpr hq))]
  exact (le_abs_self _).trans (abs_le_of_sq_le_sq hsq (by positivity))

/-- Under the tangency bound `⟪e₀, u⟫² ≤ C² θ²` the image length drops to `κ (1 + C)`.

The sharp bound is `κ √(1 + C²)`; the slightly lossy `κ (1 + C)` is used so that no square root
appears in the statement. -/
theorem norm_normalizeScaled_linear_le_of_inner_sq_le (S : Slab θ hθ) (κ : ℝ≥0) (hθ0 : 0 < θ)
    (hκ : 0 < κ) {u : EuclideanSpace ℝ (Fin 3)} (hu : ‖u‖ = 1) {C : ℝ} (hC : 0 ≤ C)
    (hinner : inner ℝ (S.basis 0) u ^ 2 ≤ C ^ 2 * (θ : ℝ) ^ 2) :
    ‖(Slab.normalizeScaled S κ hθ0 hκ).linear u‖ ≤ (κ : ℝ) * (1 + C) := by
  -- The whole content is scalar: with `N = ‖L u‖`, `k = κ`, `t = θ` and `q = ⟪e₀, u⟫²`, the
  -- identity `N² = k²(1 + (t⁻² - 1) q)` and `q ≤ C²t²` give `N² ≤ k²(1 + C²) ≤ (k(1 + C))²`.
  -- Keeping it on plain reals stops any arithmetic from running on inner-product terms, and
  -- `A` stands for `t⁻²` — kept abstract with `A t² = 1`, so everything below is polynomial.
  have key : ∀ N q k t A : ℝ, 0 ≤ N → 0 ≤ k → 0 ≤ A → 0 < t → t ≤ 1 → A * t ^ 2 = 1 →
      q ≤ C ^ 2 * t ^ 2 → N ^ 2 = k ^ 2 * (1 + (A - 1) * q) → N ≤ k * (1 + C) := by
    intro N q k t A hN hk hA ht ht1 hAt hq hNsq
    have hA1 : 1 ≤ A := by
      linarith [mul_le_mul_of_nonneg_left (pow_le_one₀ (n := 2) ht.le ht1) hA]
    have hAq : (A - 1) * q ≤ C ^ 2 := by
      have h := mul_le_mul_of_nonneg_left hq (by linarith : (0 : ℝ) ≤ A - 1)
      rw [show (A - 1) * (C ^ 2 * t ^ 2) = C ^ 2 - C ^ 2 * t ^ 2 from by
        linear_combination C ^ 2 * hAt] at h
      linarith [mul_nonneg (sq_nonneg C) (sq_nonneg t)]
    refine (le_abs_self N).trans (abs_le_of_sq_le_sq ?_ (mul_nonneg hk (by linarith)))
    linarith [mul_le_mul_of_nonneg_left hAq (sq_nonneg k), mul_nonneg (sq_nonneg k) hC]
  have hθ0' : (θ : ℝ) ≠ 0 := (NNReal.coe_pos.mpr hθ0).ne'
  exact key _ _ _ _ _ (norm_nonneg _) (NNReal.coe_nonneg κ) (by positivity)
    (NNReal.coe_pos.mpr hθ0) (NNReal.coe_le_coe.mpr hθ)
    (by rw [← mul_pow, inv_mul_cancel₀ hθ0', one_pow]) hinner
    (norm_sq_normalizeScaled_linear S κ hθ0 hκ hu)

/-! ## The conversion constant and the tube radius (`def:slabTubeConst`) -/

/-- The **conversion constant** `κ(Cset, Cang) = 1 / (16 (1 + Cang) (1 + Cset))`.

It is chosen so that the tubes produced by `Plank.slabTube` land in exactly `closedBall 0 1`, which
is what the downstream consumers `Kakeya.KatzTaoEstimate.multiplicity_bound` and
`Kakeya.FrostmanEstimate.multiplicity_bound` require. The three inequalities that fix the choice
are `Plank.slabTubeConst_mul_two_add_ang_le` (K1), `Plank.three_mul_slabTubeConst_mul_set_le` (K2)
and `Plank.slabTubeConst_mul_one_add_ang_le` (K3); together they give the budget
`3/16 + 1/2 + 1/8 = 13/16 ≤ 1`. -/
def slabTubeConst (Cset Cang : ℝ≥0) : ℝ≥0 :=
  1 / (16 * (1 + Cang) * (1 + Cset))

/-- The conversion constant is strictly positive. This is recorded separately because
`Plank.slabTubeConst` is an `NNReal` and nothing in its type supplies positivity, while
`Slab.normalizeScaled` demands it. -/
theorem slabTubeConst_pos (Cset Cang : ℝ≥0) : 0 < slabTubeConst Cset Cang := by
  rw [← NNReal.coe_lt_coe]
  simp only [slabTubeConst]
  push_cast
  positivity

/-- (K1) `κ (2 + Cang) ≤ 1/8`: this is what bounds the transverse radius of the normalised plank
by the tube radius `δ = b/8`. -/
theorem slabTubeConst_mul_two_add_ang_le (Cset Cang : ℝ≥0) :
    slabTubeConst Cset Cang * (2 + Cang) ≤ 1 / 8 := by
  rw [← NNReal.coe_le_coe]
  simp only [slabTubeConst]
  push_cast
  have h1 : (0 : ℝ) < 1 + (Cang : ℝ) := by positivity
  have h2 : (0 : ℝ) < 1 + (Cset : ℝ) := by positivity
  field_simp [h1.ne', h2.ne']
  nlinarith [NNReal.coe_nonneg Cset, NNReal.coe_nonneg Cang,
    mul_nonneg (NNReal.coe_nonneg Cang) (NNReal.coe_nonneg Cset)]

/-- (K2) `3 κ Cset ≤ 3/16`: this is what places the image of the plank's centre inside
`closedBall 0 (3/16)`. -/
theorem three_mul_slabTubeConst_mul_set_le (Cset Cang : ℝ≥0) :
    3 * slabTubeConst Cset Cang * Cset ≤ 3 / 16 := by
  rw [← NNReal.coe_le_coe]
  simp only [slabTubeConst]
  push_cast
  have h1 : (0 : ℝ) < 1 + (Cang : ℝ) := by positivity
  have h2 : (0 : ℝ) < 1 + (Cset : ℝ) := by positivity
  have hX : (0 : ℝ) < (16 : ℝ) * (1 + (Cang : ℝ)) * (1 + (Cset : ℝ)) := by positivity
  field_simp [h1.ne', h2.ne']
  nlinarith [NNReal.coe_nonneg Cset, NNReal.coe_nonneg Cang]

/-- (K3) `κ (1 + Cang) ≤ 1/16`: this is what guarantees that the axial half-length of the image
does not exceed the half-length `1/2` of a unit tube core. -/
theorem slabTubeConst_mul_one_add_ang_le (Cset Cang : ℝ≥0) :
    slabTubeConst Cset Cang * (1 + Cang) ≤ 1 / 16 := by
  rw [← NNReal.coe_le_coe]
  simp only [slabTubeConst]
  push_cast
  have h1 : (0 : ℝ) < 1 + (Cang : ℝ) := by positivity
  have h2 : (0 : ℝ) < 1 + (Cset : ℝ) := by positivity
  field_simp [h1.ne', h2.ne']
  nlinarith [NNReal.coe_nonneg Cset, NNReal.coe_nonneg Cang]

/-! ## The tube attached to a normalised plank (`def:slabTube`) -/

/-- The **direction** of the tube attached to a normalised plank: the normalisation of the image
`L u₂` of the plank's long axis under the linear part `L` of `f_S^κ`.

This is well defined with no tangency hypothesis and no lower bound on `‖L u₂‖`: `u₂` is a member
of an orthonormal basis, hence nonzero, and `L` is injective. -/
def slabTubeDir (P : Plank a b hab hb1) (S : Slab θ hθ) (κ : ℝ≥0) (hθ0 : 0 < θ) (hκ : 0 < κ) :
    EuclideanSpace ℝ (Fin 3) :=
  ‖(Slab.normalizeScaled S κ hθ0 hκ).linear (P.basis 2)‖⁻¹ •
    (Slab.normalizeScaled S κ hθ0 hκ).linear (P.basis 2)

/-- The tube direction is a unit vector, which is exactly the hypothesis of `Tube.mk'`. -/
theorem norm_slabTubeDir (P : Plank a b hab hb1) (S : Slab θ hθ) (κ : ℝ≥0) (hθ0 : 0 < θ)
    (hκ : 0 < κ) : ‖P.slabTubeDir S κ hθ0 hκ‖ = 1 := by
  rw [slabTubeDir]
  have hu : ‖P.basis 2‖ = 1 := OrthonormalBasis.norm_eq_one P.basis 2
  have hle : (κ : ℝ) ≤ ‖(Slab.normalizeScaled S κ hθ0 hκ).linear (P.basis 2)‖ :=
    le_norm_normalizeScaled_linear S κ hθ0 hκ hu
  have hk : 0 < (κ : ℝ) := NNReal.coe_pos.mpr hκ
  have hpos : 0 < ‖(Slab.normalizeScaled S κ hθ0 hκ).linear (P.basis 2)‖ := by linarith
  exact norm_smul_inv_norm (norm_pos_iff.mp hpos)

/-- The **`b/8`-tube attached to a normalised plank**: the tube whose core is the unit segment
through the image `f_S^κ(p)` of the plank's centre, in the direction `Plank.slabTubeDir`.

The radius `δ = b/8` is the one for which (K1) makes the transverse bound of
`Plank.image_carrier_subset_slabTube` work out. -/
def slabTube (P : Plank a b hab hb1) (S : Slab θ hθ) (κ : ℝ≥0) (hθ0 : 0 < θ) (hκ : 0 < κ) :
    Tube (b / 8) (EuclideanSpace ℝ (Fin 3)) :=
  Tube.mk' (b / 8)
    (x := Slab.normalizeScaled S κ hθ0 hκ P.center - (2 : ℝ)⁻¹ • P.slabTubeDir S κ hθ0 hκ)
    (y := Slab.normalizeScaled S κ hθ0 hκ P.center + (2 : ℝ)⁻¹ • P.slabTubeDir S κ hθ0 hκ)
    (by
      rw [dist_eq_norm]
      have h : (Slab.normalizeScaled S κ hθ0 hκ P.center - (2 : ℝ)⁻¹ • P.slabTubeDir S κ hθ0 hκ)
            - (Slab.normalizeScaled S κ hθ0 hκ P.center + (2 : ℝ)⁻¹ • P.slabTubeDir S κ hθ0 hκ)
            = -(P.slabTubeDir S κ hθ0 hκ) := by module
      rw [h, norm_neg]
      exact P.norm_slabTubeDir S κ hθ0 hκ)

/-! ## A tangential thickened plank normalises into a `b/8`-tube (`lem:plankToTube`) -/

/-- The image of a *long* plank axis under the linear part `L` of `f_S^κ` is short:
`‖L u_j‖ ≤ κ (1 + Cang)` for `j ≠ 0`. This is `Plank.abs_inner_slabNormal_basis_le` fed into
`Plank.norm_normalizeScaled_linear_le_of_inner_sq_le`. -/
private lemma norm_linear_basis_le_of_ne_zero (P : Plank a b hab hb1) (S : Slab θ hθ)
    {Cang : ℝ≥0} (κ : ℝ≥0) (hθ0 : 0 < θ) (hκ : 0 < κ)
    (hang : Prism3D.angle P S ≤ (Cang : ℝ) * (θ : ℝ)) {j : Fin 3} (hj : j ≠ 0) :
    ‖(Slab.normalizeScaled S κ hθ0 hκ).linear (P.basis j)‖ ≤ (κ : ℝ) * (1 + (Cang : ℝ)) := by
  have hu : ‖P.basis j‖ = 1 := OrthonormalBasis.norm_eq_one P.basis j
  have hC : 0 ≤ (Cang : ℝ) := NNReal.coe_nonneg Cang
  have hinner : inner ℝ (S.basis 0) (P.basis j) ^ 2 ≤ (Cang : ℝ) ^ 2 * (θ : ℝ) ^ 2 := by
    have h : |inner ℝ (S.basis 0) (P.basis j)| ≤ (Cang : ℝ) * (θ : ℝ) :=
      Plank.abs_inner_slabNormal_basis_le P S hang hj
    have ht0 : 0 ≤ (Cang : ℝ) * (θ : ℝ) :=
      mul_nonneg (NNReal.coe_nonneg Cang) (NNReal.coe_nonneg θ)
    have hsq : inner ℝ (S.basis 0) (P.basis j) ^ 2 ≤ ((Cang : ℝ) * (θ : ℝ)) ^ 2 := by
      exact (sq_le_sq.mpr (by simpa [abs_of_nonneg ht0] using h))
    simpa [mul_pow] using hsq
  exact Plank.norm_normalizeScaled_linear_le_of_inner_sq_le S κ hθ0 hκ hu hC hinner

/-- A difference of two values of `f_S^κ` is its linear part applied to the difference. -/
private lemma normalizeScaled_sub (S : Slab θ hθ) (κ : ℝ≥0) (hθ0 : 0 < θ) (hκ : 0 < κ)
    (x z : EuclideanSpace ℝ (Fin 3)) :
    Slab.normalizeScaled S κ hθ0 hκ x - Slab.normalizeScaled S κ hθ0 hκ z
      = (Slab.normalizeScaled S κ hθ0 hκ).linear (x - z) := by
  simpa [vsub_eq_sub] using
    (AffineMap.linearMap_vsub
      (Slab.normalizeScaled S κ hθ0 hκ : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ]
        EuclideanSpace ℝ (Fin 3)) x z).symm

/-- A point at signed distance at most `1/2` from `c` along `d` lies on the segment from
`c - d/2` to `c + d/2`. This is the witness used for the axial component in
`Plank.image_carrier_subset_slabTube`. -/
private lemma mem_segment_of_abs_le (c d : EuclideanSpace ℝ (Fin 3)) {t : ℝ} (ht : |t| ≤ 2⁻¹) :
    c + t • d ∈ segment ℝ (c - (2 : ℝ)⁻¹ • d) (c + (2 : ℝ)⁻¹ • d) := by
  refine ⟨2⁻¹ - t, 2⁻¹ + t, by linarith [(abs_le.mp ht).2], by linarith [(abs_le.mp ht).1],
    by ring, ?_⟩
  module

/-- **The conversion, pointwise.** Under the tangency hypothesis `∠(TP, TS) ≤ Cang · θ` alone the
normalising map `f_S^κ` carries the thickened plank `P_θ` into the `b/8`-tube of `Plank.slabTube`.

The transverse bound is `κ b (2 + Cang) ≤ b/8` by (K1) and the axial bound is
`κ (1 + Cang) ≤ 1/16 ≤ 1/2` by (K3). Neither uses the location of the centre of `P` — the tube is
built around the image of that centre — nor `0 < b`: at `b = 0` both the plank half-widths and the
tube radius degenerate to `0` and the containment still holds. Only the *location* statement
`Plank.slabTube_carrier_subset_closedBall` consumes the dilation hypothesis. -/
theorem image_carrier_subset_slabTube (P : Plank a b hab hb1) (S : Slab θ hθ) {Cset Cang : ℝ≥0}
    (hθ0 : 0 < θ)
    (hang : Prism3D.angle P S ≤ (Cang : ℝ) * (θ : ℝ)) :
    (Slab.normalizeScaled S (slabTubeConst Cset Cang) hθ0 (slabTubeConst_pos Cset Cang)) ''
        (P.thickened θ hθ).carrier
      ⊆ (P.slabTube S (slabTubeConst Cset Cang) hθ0 (slabTubeConst_pos Cset Cang)).carrier := by
  let κ : ℝ≥0 := slabTubeConst Cset Cang
  let hκ : 0 < κ := slabTubeConst_pos Cset Cang
  let g : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin 3) :=
    Slab.normalizeScaled S κ hθ0 hκ
  let L : EuclideanSpace ℝ (Fin 3) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 3) := g.linear
  let c : EuclideanSpace ℝ (Fin 3) := g P.center
  let d : EuclideanSpace ℝ (Fin 3) := P.slabTubeDir S κ hθ0 hκ
  change (g '' (P.thickened θ hθ).carrier) ⊆ (P.slabTube S κ hθ0 hκ).carrier
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨α, hα, -, hx_eq⟩ :=
    PrismNDim.exists_repr_of_mem (P.thickened θ hθ).toPrismNDim hx
  -- The half-widths of `P_θ` are `(θ b, b, 1)` by definition.
  have hα0 : |α 0| ≤ (θ : ℝ) * (b : ℝ) := by
    have h := hα 0
    rwa [show (P.thickened θ hθ).toPrismNDim.thicknesses 0 = θ * b from rfl, NNReal.coe_mul] at h
  have hα1 : |α 1| ≤ (b : ℝ) := by
    have h := hα 1
    rwa [show (P.thickened θ hθ).toPrismNDim.thicknesses 1 = b from rfl] at h
  have hα2 : |α 2| ≤ 1 := by
    have h := hα 2
    rwa [show (P.thickened θ hθ).toPrismNDim.thicknesses 2 = 1 from rfl, NNReal.coe_one] at h
  have hx_gen : x = (∑ i, α i • P.basis i) +ᵥ P.center := hx_eq
  have hv : x - P.center = α 0 • P.basis 0 + α 1 • P.basis 1 + α 2 • P.basis 2 := by
    rw [hx_gen, vadd_eq_add, add_sub_cancel_right, Fin.sum_univ_three]
  -- The image of `x` in the frame of the image axes.
  have hw : g x - c = α 0 • L (P.basis 0) + α 1 • L (P.basis 1) + α 2 • L (P.basis 2) := by
    have hlin : g x - c = L (x - P.center) := normalizeScaled_sub S κ hθ0 hκ x P.center
    rw [hlin, hv]
    simp only [map_add, map_smul]
  have hL2b : ‖L (P.basis 2)‖ ≤ (κ : ℝ) * (1 + (Cang : ℝ)) :=
    norm_linear_basis_le_of_ne_zero P S κ hθ0 hκ hang (j := 2) (by decide)
  have hL2_pos : 0 < ‖L (P.basis 2)‖ :=
    lt_of_lt_of_le (NNReal.coe_pos.mpr hκ)
      (le_norm_normalizeScaled_linear S κ hθ0 hκ (OrthonormalBasis.norm_eq_one P.basis 2))
  -- The axial component `α 2 • L u₂` is a multiple of the tube direction `d`.
  have hts : (α 2 * ‖L (P.basis 2)‖) • d = α 2 • L (P.basis 2) := by
    rw [show d = ‖L (P.basis 2)‖⁻¹ • L (P.basis 2) from rfl,
      smul_smul, mul_assoc, mul_inv_cancel₀ hL2_pos.ne', mul_one]
  have hgz : g x - (c + (α 2 * ‖L (P.basis 2)‖) • d)
      = α 0 • L (P.basis 0) + α 1 • L (P.basis 1) := by
    rw [hts, sub_add_eq_sub_sub, hw, add_sub_cancel_right]
  have hL0 : ‖L (P.basis 0)‖ ≤ (κ : ℝ) * (θ : ℝ)⁻¹ :=
    norm_normalizeScaled_linear_le S κ hθ0 hκ (OrthonormalBasis.norm_eq_one P.basis 0)
  have hL1b : ‖L (P.basis 1)‖ ≤ (κ : ℝ) * (1 + (Cang : ℝ)) :=
    norm_linear_basis_le_of_ne_zero P S κ hθ0 hκ hang (j := 1) (by decide)
  have hb0 : 0 ≤ (b : ℝ) := NNReal.coe_nonneg b
  have hK1 : (κ : ℝ) * (2 + (Cang : ℝ)) ≤ (1 : ℝ) / 8 := by
    exact_mod_cast slabTubeConst_mul_two_add_ang_le Cset Cang
  have hK3 : (κ : ℝ) * (1 + (Cang : ℝ)) ≤ (1 : ℝ) / 16 := by
    exact_mod_cast slabTubeConst_mul_one_add_ang_le Cset Cang
  -- Transverse bound: `θ b · κ θ⁻¹ + b · κ (1 + Cang) = κ b (2 + Cang) ≤ b / 8` by (K1).
  have hfinal : ‖g x - (c + (α 2 * ‖L (P.basis 2)‖) • d)‖ ≤ (b : ℝ) / 8 := by
    have h0mul : |α 0| * ‖L (P.basis 0)‖ ≤ (κ : ℝ) * (b : ℝ) := by
      have h := mul_le_mul hα0 hL0 (norm_nonneg _)
        (mul_nonneg (NNReal.coe_nonneg θ) (NNReal.coe_nonneg b))
      rwa [show (θ : ℝ) * (b : ℝ) * ((κ : ℝ) * (θ : ℝ)⁻¹)
            = ((θ : ℝ) * (θ : ℝ)⁻¹) * ((κ : ℝ) * (b : ℝ)) from by ring,
        mul_inv_cancel₀ (ne_of_gt (NNReal.coe_pos.mpr hθ0)), one_mul] at h
    rw [hgz]
    calc ‖α 0 • L (P.basis 0) + α 1 • L (P.basis 1)‖
        ≤ |α 0| * ‖L (P.basis 0)‖ + |α 1| * ‖L (P.basis 1)‖ := by
          rw [← Real.norm_eq_abs, ← Real.norm_eq_abs, ← norm_smul, ← norm_smul]
          exact norm_add_le _ _
      _ ≤ (κ : ℝ) * (b : ℝ) + (b : ℝ) * ((κ : ℝ) * (1 + (Cang : ℝ))) :=
          add_le_add h0mul (mul_le_mul hα1 hL1b (norm_nonneg _) hb0)
      _ ≤ (b : ℝ) / 8 := by linarith [mul_le_mul_of_nonneg_left hK1 hb0]
  -- Axial bound: `|α 2| ‖L u₂‖ ≤ κ (1 + Cang) ≤ 1/16 ≤ 1/2` by (K3).
  have hlt : |α 2 * ‖L (P.basis 2)‖| ≤ (2 : ℝ)⁻¹ := by
    rw [abs_mul, abs_of_nonneg (norm_nonneg _)]
    calc |α 2| * ‖L (P.basis 2)‖ ≤ 1 * ((κ : ℝ) * (1 + (Cang : ℝ))) :=
          mul_le_mul hα2 hL2b (norm_nonneg _) zero_le_one
      _ ≤ (2 : ℝ)⁻¹ := by linarith
  rw [slabTube, Tube.carrier_eq]
  refine Set.mem_iUnion₂.mpr
    ⟨c + (α 2 * ‖L (P.basis 2)‖) • d, mem_segment_of_abs_le c d hlt, ?_⟩
  rw [Metric.mem_closedBall, dist_eq_norm, NNReal.coe_div]
  exact hfinal

/-- **The conversion, location.** The tube attached to a plank whose centre lies in the
`Cset`-dilation of `S` lies in the closed unit ball: its centre is within `3 κ Cset ≤ 3/16` of the
origin by (K2), its core has half-length `1/2`, and its radius is `b/8 ≤ 1/8`, for a total budget
of `3/16 + 1/2 + 1/8 = 13/16 ≤ 1`. -/
theorem slabTube_carrier_subset_closedBall (P : Plank a b hab hb1) (S : Slab θ hθ)
    {Cset Cang : ℝ≥0} (hθ0 : 0 < θ)
    (hcen : P.center ∈ (S.toPrismNDim.dilation Cset).carrier) :
    (P.slabTube S (slabTubeConst Cset Cang) hθ0 (slabTubeConst_pos Cset Cang)).carrier
      ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  let κ : ℝ≥0 := slabTubeConst Cset Cang
  let c : EuclideanSpace ℝ (Fin 3) :=
    Slab.normalizeScaled S κ hθ0 (slabTubeConst_pos Cset Cang) P.center
  -- (K2): the image of the centre is within `3 κ Cset ≤ 3/16` of the origin.
  have hc' : ‖c‖ ≤ (3 : ℝ) / 16 :=
    (mem_closedBall_zero_iff.mp (Slab.normalizeScaled_image_dilation_subset_closedBall S κ Cset
      hθ0 (slabTubeConst_pos Cset Cang) ⟨P.center, hcen, rfl⟩)).trans (by
        exact_mod_cast (three_mul_slabTubeConst_mul_set_le Cset Cang : 3 * κ * Cset ≤ 3 / 16))
  -- The core of the tube has midpoint `c`, so the tube lies in `closedBall c (1/2 + b/8)`.
  have hmid : midpoint ℝ (P.slabTube S κ hθ0 (slabTubeConst_pos Cset Cang)).x
      (P.slabTube S κ hθ0 (slabTubeConst_pos Cset Cang)).y = c := midpoint_sub_add ℝ c _
  have hbco : (b : ℝ) ≤ 1 := by exact_mod_cast hb1
  refine (Kakeya.Tube.carrier_subset_closedBall_midpoint _ _).trans
    (Metric.closedBall_subset_closedBall' ?_)
  rw [hmid, dist_zero_right, NNReal.coe_div, NNReal.coe_ofNat]
  linarith

/-- **The quantitative content of "`L(P)` has dimensions `b × b × 1`".** The normalised thickened
plank has exactly the volume of a `b × b × 1` box, up to the absolute factor `κ³`:
`|g(P_θ)| = J(g) |P_θ| = κ³θ⁻¹ · 8θb² = 8κ³b²`. -/
theorem volume_image_normalizeScaled_thickened (P : Plank a b hab hb1) (S : Slab θ hθ) (κ : ℝ≥0)
    (hθ0 : 0 < θ) (hκ : 0 < κ) :
    volume ((Slab.normalizeScaled S κ hθ0 hκ) '' (P.thickened θ hθ).carrier)
      = 8 * (κ : ENNReal) ^ 3 * (b : ENNReal) ^ 2 := by
  rw [Kakeya.volume_image_affineEquiv]
  rw [Slab.affineJacobian_normalizeScaled]
  rw [Plank.volume_thickened]
  have hκ3 : 0 ≤ (κ : ℝ) ^ 3 := by positivity
  have hθℝ : 0 < (θ : ℝ) := NNReal.coe_pos.mpr hθ0
  have hof : ENNReal.ofReal ((κ : ℝ) ^ 3 * (θ : ℝ)⁻¹)
      = (κ : ENNReal) ^ 3 * (θ : ENNReal)⁻¹ := by
    rw [ENNReal.ofReal_mul hκ3]
    rw [ENNReal.ofReal_pow (n := 3) (NNReal.coe_nonneg κ)]
    rw [ENNReal.ofReal_coe_nnreal]
    rw [ENNReal.ofReal_inv_of_pos hθℝ]
    rw [ENNReal.ofReal_coe_nnreal]
  rw [hof]
  have hT0 : (θ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hθ0.ne'
  have hTtop : (θ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hcancel : (θ : ENNReal)⁻¹ * (θ : ENNReal) = 1 := ENNReal.inv_mul_cancel hT0 hTtop
  calc
    (κ : ENNReal) ^ 3 * (θ : ENNReal)⁻¹ * (8 * (θ : ENNReal) * b * b)
        = (κ : ENNReal) ^ 3 * 8 * ((θ : ENNReal)⁻¹ * (θ : ENNReal)) * b * b := by
          ac_rfl
    _ = (κ : ENNReal) ^ 3 * 8 * 1 * b * b := by rw [hcancel]
    _ = 8 * (κ : ENNReal) ^ 3 * (b : ENNReal) ^ 2 := by
          rw [sq]
          ring

end Plank

/-! ## A tube sits inside a prism (`lem:orthonormalBasisLast`, `lem:tubeVolumeUpperBound`)

These two results concern `Tube` and `PrismNDim` only and would naturally live under
`Kakeya/Tube/`; they are declared in this Section 6 module only because this region may not create
files elsewhere. -/

namespace Kakeya

/-- Every unit vector of `ℝ³` is the last vector of an orthonormal basis.

The index `2` rather than `0` matches the `Prism3D` convention that `basis 2` is the long axis;
`PrismNDim` imposes no ordering on the half-widths, so any index would do. -/
theorem exists_orthonormalBasis_last_eq {u : EuclideanSpace ℝ (Fin 3)} (hu : ‖u‖ = 1) :
    ∃ B : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)), B 2 = u := by
  rcases Orthonormal.exists_orthonormalBasis_extension_of_card_eq (𝕜 := ℝ)
      (E := EuclideanSpace ℝ (Fin 3)) (card_ι := by simp)
      (v := fun _ : Fin 3 => u) (s := ({2} : Set (Fin 3)))
      (hv := by
        constructor
        · intro i
          simp [hu]
        · intro i j hij
          exact absurd (Subtype.ext (i.2.trans j.2.symm)) hij) with
    ⟨B, hB⟩
  refine ⟨B, ?_⟩
  exact hB 2 (by simp)

end Kakeya

namespace Tube

variable {δ : ℝ≥0}

/-- A `δ`-tube in `ℝ³` is contained in the prism centred at the tube's centre, with long axis the
tube's direction, and half-widths `(δ, δ, 1/2 + δ)`. -/
theorem exists_prism_carrier_superset (T : Tube δ (EuclideanSpace ℝ (Fin 3))) :
    ∃ B : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)), B 2 = T.direction ∧
      (T.carrier : Set (EuclideanSpace ℝ (Fin 3)))
        ⊆ (PrismNDim.mk' T.center B ![δ, δ, 1 / 2 + δ]).carrier := by
  obtain ⟨B, hB⟩ := Kakeya.exists_orthonormalBasis_last_eq T.norm_direction
  refine ⟨B, hB, fun p hp => ?_⟩
  rw [T.carrier_eq] at hp
  obtain ⟨z, hz, hpz⟩ := Set.mem_iUnion₂.mp hp
  rw [segment_eq_image] at hz
  obtain ⟨t, ht, hz_eq⟩ := hz
  have hw : ‖p - z‖ ≤ (δ : ℝ) := mem_closedBall_iff_norm.mp hpz
  have key (i : Fin 3) : |inner ℝ (B i) (p - z)| ≤ (δ : ℝ) := by
    have h := abs_real_inner_le_norm (B i) (p - z)
    rw [B.norm_eq_one i, one_mul] at h
    exact h.trans hw
  have ht_half : |t - (1 / 2 : ℝ)| ≤ (1 / 2 : ℝ) := by
    obtain ⟨h0, h1⟩ := Set.mem_Icc.mp ht
    rw [abs_le]
    constructor <;> linarith
  have hz_center : z - T.center = (t - (1 / 2 : ℝ)) • (T.y - T.x) := by
    rw [← hz_eq, show T.center = (1 / 2 : ℝ) • (T.x + T.y) from by
      rw [show T.center = _root_.midpoint ℝ T.x T.y from rfl, _root_.midpoint_eq_smul_add]
      norm_num]
    module
  rw [PrismNDim.mem_carrier_iff]
  intro i
  simp only [PrismNDim.center_mk', PrismNDim.basis_mk', PrismNDim.thicknesses_mk']
  rw [vsub_eq_sub, B.repr_apply_apply, show p - T.center = (p - z) + (z - T.center) from by abel,
    inner_add_right, hz_center, real_inner_smul_right, show T.y - T.x = B 2 from hB.symm,
    B.inner_eq_ite]
  fin_cases i <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.reduceEq, reduceIte,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons, mul_zero, mul_one, add_zero, NNReal.coe_add, NNReal.coe_div,
      NNReal.coe_one, NNReal.coe_ofNat]
  · exact key 0
  · exact key 1
  · linarith [key 2, ht_half, abs_add_le (inner ℝ (B 2) (p - z)) (t - (1 / 2 : ℝ))]

/-- The volume of a `δ`-tube in `ℝ³` is at most `8 δ² (1/2 + δ)`.
The elementary prism bound gives `5 δ²` for `δ ≤ 1/8`, compared with the
general bound `16 δ²` from `Tube.volume_le`. -/
theorem volume_carrier_le (T : Tube δ (EuclideanSpace ℝ (Fin 3))) :
    volume T.carrier ≤ 8 * (δ : ENNReal) ^ 2 * (1 / 2 + (δ : ENNReal)) := by
  rcases Tube.exists_prism_carrier_superset T with ⟨B, _, hsub⟩
  calc
    volume T.carrier ≤ volume (PrismNDim.mk' T.center B ![δ, δ, 1 / 2 + δ]).carrier :=
      measure_mono hsub
    _ = 8 * (δ : ENNReal) ^ 2 * (1 / 2 + (δ : ENNReal)) := by
      rw [PrismNDim.volume_carrier]
      rw [finrank_euclideanSpace_fin]
      rw [Fin.prod_univ_three]
      simp [PrismNDim.thicknesses_mk']
      norm_num
      ring

end Tube

/-! ## Multiplicity depends only on the shadings (`lem:multiplicityCongr`) -/

namespace ShadedBody

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*}

/-- `μ` is a function of the shadings alone.

This is needed because the tube family of `Plank.slabTubeFamily` is *not* the transported family
`g_♯𝒫` — its carriers are tubes, not images of planks — and only its shadings agree with those of
`g_♯𝒫`; without this step `ShadedBody.multiplicity_mapAffine` could not be applied.

**Name note.** This declaration owns the name `ShadedBody.multiplicity_congr`.  Until  an
identically-stated theorem of the same name also lived in
`Kakeya/DimensionThree/Slab/Multiplicity.lean`; since neither module imports the other and both are
imported by `Kakeya.lean`, the two were merged silently by the import machinery.  That copy is now
`ShadedBody.multiplicity_eq_of_forall_shade_eq`.  Two further copies of the same statement exist
under different names -- `ShadedBody.multiplicity_congr_shade`
(`Plank/Section6FactorAdapter.lean`) and `Kakeya.multiplicity_eq_of_shade_eqOn`
(`Plank/InnerMultiplicityTransport.lean`) -- so do not add a fifth. -/
theorem multiplicity_congr (s : Finset ι) (V W : ι → ShadedBody E)
    (h : ∀ i ∈ s, (V i).shade = (W i).shade) : multiplicity s V = multiplicity s W := by
  rw [multiplicity_eq_div, multiplicity_eq_div]
  congr 1
  · exact Finset.sum_congr rfl fun i hi => by rw [h i hi]
  · congr 1
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i, hi, hx⟩
      exact ⟨i, hi, by rw [h i hi] at hx; exact hx⟩
    · rintro ⟨i, hi, hx⟩
      exact ⟨i, hi, by rw [h i hi]; exact hx⟩

end ShadedBody

/-! ## The tube family attached to a tangential plank family (`def:slabTubeFamily`) -/

namespace Plank

variable {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {θ : ℝ≥0} {hθ : θ ≤ 1} {ι : Type*}

/-- The shaded `b/8`-tube attached to a plank `P` carrying the shading `Y`: the tube of
`Plank.slabTube`, shaded by the image `g(Y(V))` of the shading, intersected with the tube.

The intersection is a device, not a loss: under the hypotheses of
`Plank.image_carrier_subset_slabTube` one has `g(Y(V)) ⊆ g(P_θ) ⊆ T`, so the intersection is inert.
Taking it makes the `shade_subset` field hold unconditionally, so that the family can be defined
before the hypotheses are invoked — which is what lets it be a plain function of the index rather
than a function of a proof. -/
def slabShadedTube (P : Plank a b hab hb1) (Y : ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (S : Slab θ hθ) (κ : ℝ≥0) (hθ0 : 0 < θ) (hκ : 0 < κ) :
    ShadedTube (b / 8) (EuclideanSpace ℝ (Fin 3)) where
  toTube := P.slabTube S κ hθ0 hκ
  shade := (Slab.normalizeScaled S κ hθ0 hκ) '' Y.shade ∩ (P.slabTube S κ hθ0 hκ).carrier
  measurableSet_shade := by
    exact (Kakeya.measurableSet_affineEquiv_image (Slab.normalizeScaled S κ hθ0 hκ)
      Y.measurableSet_shade).inter (P.slabTube S κ hθ0 hκ).isCompact.measurableSet
  shade_subset := by
    exact Set.inter_subset_right

/-- The fixed shadeless `δ`-tube used for indices outside the family: its core is the segment from
`-e/2` to `e/2`, where `e` is the first standard basis vector. -/
def defaultShadedTube (δ : ℝ≥0) : ShadedTube δ (EuclideanSpace ℝ (Fin 3)) where
  toTube := Tube.mk' δ
    (x := -((2 : ℝ)⁻¹ • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)))
    (y := (2 : ℝ)⁻¹ • EuclideanSpace.single (0 : Fin 3) (1 : ℝ))
    (by
      rw [dist_eq_norm]
      have h : -((2 : ℝ)⁻¹ • EuclideanSpace.single (0 : Fin 3) (1 : ℝ))
            - ((2 : ℝ)⁻¹ • EuclideanSpace.single (0 : Fin 3) (1 : ℝ))
            = -(EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) := by module
      rw [h, norm_neg]
      rw [PiLp.norm_single]
      norm_num)
  shade := ∅
  measurableSet_shade := MeasurableSet.empty
  shade_subset := Set.empty_subset _

open Classical in
/-- The **tube family** `𝒯` attached to a tangential plank family in a slab: on the index set `s`
it is `Plank.slabShadedTube`, and off `s` it is the fixed `Plank.defaultShadedTube`.

`μ` and `λ` are defined on families of type `ι → ShadedBody E`, so wherever they are applied to
`𝒯` they are applied to `fun i => (𝒯 i).toShadedBody`. -/
def slabTubeFamily (s : Finset ι) (V : ι → Plank a b hab hb1)
    (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))) (S : Slab θ hθ) (κ : ℝ≥0) (hθ0 : 0 < θ)
    (hκ : 0 < κ) (i : ι) : ShadedTube (b / 8) (EuclideanSpace ℝ (Fin 3)) :=
  if i ∈ s then (V i).slabShadedTube (Y i) S κ hθ0 hκ else defaultShadedTube (b / 8)

/-! ### The family-level interface (`thm:slabTubeFamilyBasic`)

This is the interface consumed by GWZ Lemma 6.1 (`plankKTUnified`) and Lemma 6.4 (`plankF`). -/

section Family

variable {Cset Cang : ℝ≥0} {s : Finset ι} {V : ι → Plank a b hab hb1}
  {Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))} {S : Slab θ hθ}

/-- **(1)** Every tube of the family lies in the closed unit ball, including at the indices outside
`s`, where the default tube lies in `closedBall 0 (1/2 + δ)` and only `b ≤ 1` is used. -/
theorem slabTubeFamily_carrier_subset_closedBall (hθ0 : 0 < θ)
    (hmem : ∀ i ∈ s, i ∈ inSlabFamilyC Cset Cang s V S) (i : ι) :
    (slabTubeFamily s V Y S (slabTubeConst Cset Cang) hθ0 (slabTubeConst_pos Cset Cang)
        i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  by_cases hi : i ∈ s
  · have hcen : (V i).center ∈ (S.toPrismNDim.dilation Cset).carrier :=
      Plank.center_mem_slabDilation_of_inSlabFamilyC (hmem i hi)
    simpa only [slabTubeFamily, if_pos hi, slabShadedTube] using
      Plank.slabTube_carrier_subset_closedBall (V i) S hθ0 hcen
  · have hbco : (b : ℝ) ≤ 1 := by exact_mod_cast hb1
    simp only [slabTubeFamily, if_neg hi]
    refine (Kakeya.Tube.carrier_subset_closedBall_midpoint _ _).trans
      (Metric.closedBall_subset_closedBall' ?_)
    rw [show midpoint ℝ (defaultShadedTube (b / 8 : ℝ≥0)).x
        (defaultShadedTube (b / 8 : ℝ≥0)).y = (0 : EuclideanSpace ℝ (Fin 3)) from
      midpoint_neg_self ℝ _, dist_self, NNReal.coe_div, NNReal.coe_ofNat]
    linarith

/-- **(2)** On `s` the tube family carries exactly the transported shadings: the intersection with
the tube in `Plank.slabShadedTube` is inert, because the shading is contained in the thickened
plank, whose image is contained in the tube. -/
theorem slabTubeFamily_shade (hθ0 : 0 < θ)
    (hmem : ∀ i ∈ s, i ∈ inSlabFamilyC Cset Cang s V S)
    (hcar : ∀ i ∈ s, (Y i).carrier = ((V i).thickened θ hθ).carrier) {i : ι} (hi : i ∈ s) :
    (slabTubeFamily s V Y S (slabTubeConst Cset Cang) hθ0 (slabTubeConst_pos Cset Cang) i).shade
      = (Slab.normalizeScaled S (slabTubeConst Cset Cang) hθ0 (slabTubeConst_pos Cset Cang)) ''
          (Y i).shade := by
  have hang : Prism3D.angle (V i) S ≤ (Cang : ℝ) * (θ : ℝ) :=
    (mem_inSlabFamilyC.mp (hmem i hi)).2.2
  have hshade : (Y i).shade ⊆ ((V i).thickened θ hθ).carrier := by
    rw [← hcar i hi]
    exact (Y i).shade_subset
  have hsub : (Slab.normalizeScaled S (slabTubeConst Cset Cang) hθ0
        (slabTubeConst_pos Cset Cang)) '' (Y i).shade
      ⊆ ((V i).slabTube S (slabTubeConst Cset Cang) hθ0 (slabTubeConst_pos Cset Cang)).carrier :=
    (Set.image_mono hshade).trans (image_carrier_subset_slabTube (V i) S hθ0 hang)
  simp only [slabTubeFamily, slabShadedTube, if_pos hi]
  exact Set.inter_eq_self_of_subset_left hsub

/-- **(3)** On `s` the normalised thickened plank is contained in the tube. -/
theorem image_thickened_subset_slabTubeFamily (hθ0 : 0 < θ)
    (hmem : ∀ i ∈ s, i ∈ inSlabFamilyC Cset Cang s V S) {i : ι} (hi : i ∈ s) :
    (Slab.normalizeScaled S (slabTubeConst Cset Cang) hθ0 (slabTubeConst_pos Cset Cang)) ''
        ((V i).thickened θ hθ).carrier
      ⊆ (slabTubeFamily s V Y S (slabTubeConst Cset Cang) hθ0
          (slabTubeConst_pos Cset Cang) i).carrier := by
  have hang : Prism3D.angle (V i) S ≤ (Cang : ℝ) * (θ : ℝ) :=
    (mem_inSlabFamilyC.mp (hmem i hi)).2.2
  simpa [slabTubeFamily, slabShadedTube, if_pos hi] using
    image_carrier_subset_slabTube (V i) S hθ0 hang

/-- **Tube conversion: the multiplicity `μ` is preserved exactly.**

The shadings of `𝒯` are exactly the shadings of `g_♯𝒫` (`Plank.slabTubeFamily_shade`), so
`ShadedBody.multiplicity_congr` reduces the claim to `ShadedBody.multiplicity_mapAffine`; in
particular `μ` sees only the shadings, so no positivity of `b` is involved. -/
theorem multiplicity_slabTubeFamily (hθ0 : 0 < θ)
    (hmem : ∀ i ∈ s, i ∈ inSlabFamilyC Cset Cang s V S)
    (hcar : ∀ i ∈ s, (Y i).carrier = ((V i).thickened θ hθ).carrier) :
    ShadedBody.multiplicity s (fun i => (slabTubeFamily s V Y S (slabTubeConst Cset Cang) hθ0
        (slabTubeConst_pos Cset Cang) i).toShadedBody)
      = ShadedBody.multiplicity s Y := by
  let g : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin 3) :=
    Slab.normalizeScaled S (slabTubeConst Cset Cang) hθ0 (slabTubeConst_pos Cset Cang)
  have h : ∀ i ∈ s,
      ((slabTubeFamily s V Y S (slabTubeConst Cset Cang) hθ0
        (slabTubeConst_pos Cset Cang) i).toShadedBody).shade = ((Y i).mapAffine g).shade := by
    intro i hi
    change (slabTubeFamily s V Y S (slabTubeConst Cset Cang) hθ0
        (slabTubeConst_pos Cset Cang) i).shade = ((Y i).mapAffine g).shade
    rw [slabTubeFamily_shade hθ0 hmem hcar hi, ShadedBody.mapAffine_shade]
  rw [ShadedBody.multiplicity_congr s _ (fun i => (Y i).mapAffine g) h]
  exact ShadedBody.multiplicity_mapAffine s Y g

/-- The per-index volume comparison behind `Plank.fullness_le_slabTubeFamily`: the enclosing tube
exceeds the normalised thickened plank by at most the absolute factor
`C_vol = 40 (1 + Cang)³ (1 + Cset)³`. Both sides are `5 b² / 64` up to the slack `b ≤ 1`.

Also consumed by the Katz–Tao tube family of `PlankToTubeDilated.lean`, whose shading bodies are
fixed dilations of the thickened plank; that is why this is not `private`. -/
lemma volume_slabTube_le (P : Plank a b hab hb1) (S : Slab θ hθ) {Cset Cang : ℝ≥0}
    (hθ0 : 0 < θ) :
    volume (P.slabTube S (slabTubeConst Cset Cang) hθ0 (slabTubeConst_pos Cset Cang)).carrier
      ≤ (40 * (1 + (Cang : ENNReal)) ^ 3 * (1 + (Cset : ENNReal)) ^ 3) *
          volume ((Slab.normalizeScaled S (slabTubeConst Cset Cang) hθ0
            (slabTubeConst_pos Cset Cang)) '' (P.thickened θ hθ).carrier) := by
  -- `C_vol · 8κ³ = 5/64`, so the claim is the scalar bound `8 (b/8)² (1/2 + b/8) ≤ 5b²/64`,
  -- which is `b³ ≤ b²`. Everything is a coercion of `ℝ≥0`, so it is proved there and cast.
  have hid : (40 : ℝ≥0) * (1 + Cang) ^ 3 * (1 + Cset) ^ 3
      * (8 * slabTubeConst Cset Cang ^ 3 * b ^ 2) = 5 / 64 * b ^ 2 := by
    have h1 : (1 : ℝ≥0) + Cang ≠ 0 := by positivity
    have h2 : (1 : ℝ≥0) + Cset ≠ 0 := by positivity
    simp only [slabTubeConst]
    field_simp
    ring
  have key : (8 : ℝ≥0) * (b / 8) ^ 2 * (1 / 2 + b / 8)
      ≤ 40 * (1 + Cang) ^ 3 * (1 + Cset) ^ 3 * (8 * slabTubeConst Cset Cang ^ 3 * b ^ 2) := by
    rw [hid, ← NNReal.coe_le_coe]
    push_cast
    linarith [mul_nonneg (sq_nonneg (b : ℝ))
      (sub_nonneg.mpr (show (b : ℝ) ≤ 1 from by exact_mod_cast hb1))]
  rw [volume_image_normalizeScaled_thickened P S _ hθ0 (slabTubeConst_pos Cset Cang)]
  refine (Tube.volume_carrier_le _).trans ?_
  rw [show (1 / 2 : ENNReal) = ((1 / 2 : ℝ≥0) : ENNReal) from by
    rw [ENNReal.coe_div (by norm_num)]; norm_num]
  exact_mod_cast key

/-- **Tube conversion: the density `λ` is preserved up to the explicit factor**
`C_vol = 5 / (512 κ³) = 40 (1 + Cang)³ (1 + Cset)³`.

The numerators agree by `Plank.slabTubeFamily_shade`. For the denominators,
`Tube.volume_carrier_le` gives `|T i| ≤ 5b²/64` while
`Plank.volume_image_normalizeScaled_thickened` gives `|g((V i)_θ)| = 8κ³b²`, so the tube
denominator exceeds the plank denominator by at most `C_vol`; dividing a common numerator by a
larger denominator gives a smaller quotient.

This is the only statement of the family-level interface that needs `0 < b`: the denominator
`|g((V i)_θ)| = 8κ³b²` has to be nonzero for the comparison of quotients. -/
theorem fullness_le_slabTubeFamily (hθ0 : 0 < θ) (hb0 : 0 < b)
    (hmem : ∀ i ∈ s, i ∈ inSlabFamilyC Cset Cang s V S)
    (hcar : ∀ i ∈ s, (Y i).carrier = ((V i).thickened θ hθ).carrier) :
    ShadedBody.fullness' s Y
      ≤ (40 * (1 + (Cang : ENNReal)) ^ 3 * (1 + (Cset : ENNReal)) ^ 3) *
          ShadedBody.fullness' s (fun i => (slabTubeFamily s V Y S (slabTubeConst Cset Cang) hθ0
            (slabTubeConst_pos Cset Cang) i).toShadedBody) := by
  -- The scalar core: a common Jacobian factor `J` on the numerators and the factor `C · J`
  -- bounding the denominators reduce the claim to `ENNReal.div_le_div_left`.
  have core : ∀ N D N' D' J C : ENNReal, C * J ≠ 0 → C * J ≠ ⊤ →
      N' = J * N → D' ≤ C * (J * D) → N / D ≤ C * (N' / D') := by
    intro N D N' D' J C h0 htop hN hD
    subst hN
    rw [← mul_assoc] at hD
    calc N / D = C * J * N / (C * J * D) :=
          (ENNReal.mul_div_mul_left (a := N) (b := D) (c := C * J) h0 htop).symm
      _ ≤ C * J * N / D' := ENNReal.div_le_div_left hD _
      _ = C * (J * N / D') := by rw [mul_assoc, mul_div_assoc]
  have hone (r : ℝ≥0) : (1 : ENNReal) + (r : ENNReal) ≠ 0 := (zero_lt_one.trans_le le_self_add).ne'
  have htop (r : ℝ≥0) : (1 : ENNReal) + (r : ENNReal) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, ENNReal.coe_ne_top⟩
  have hC0 : (40 : ENNReal) * (1 + (Cang : ENNReal)) ^ 3 * (1 + (Cset : ENNReal)) ^ 3 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 3 (hone Cang))) (pow_ne_zero 3 (hone Cset))
  have hCtop : (40 : ENNReal) * (1 + (Cang : ENNReal)) ^ 3 * (1 + (Cset : ENNReal)) ^ 3 ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) (ENNReal.pow_ne_top (htop Cang)))
      (ENNReal.pow_ne_top (htop Cset))
  dsimp only [ShadedBody.fullness']
  refine core _ _ _ _ (Kakeya.affineJacobian (Slab.normalizeScaled S (slabTubeConst Cset Cang)
      hθ0 (slabTubeConst_pos Cset Cang))) _
    (mul_ne_zero hC0 (Kakeya.affineJacobian_ne_zero _))
    (ENNReal.mul_ne_top hCtop (Kakeya.affineJacobian_ne_top _)) ?_ ?_
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [slabTubeFamily_shade hθ0 hmem hcar hi, Kakeya.volume_image_affineEquiv]
  · simp only [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [hcar i hi, ← Kakeya.volume_image_affineEquiv,
      show volume (slabTubeFamily s V Y S (slabTubeConst Cset Cang) hθ0
            (slabTubeConst_pos Cset Cang) i).carrier
          = volume ((V i).slabTube S (slabTubeConst Cset Cang) hθ0
            (slabTubeConst_pos Cset Cang)).carrier from by
        simp only [slabTubeFamily, if_pos hi]; rfl]
    exact volume_slabTube_le (V i) S hθ0

end Family

end Plank

end
