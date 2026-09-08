/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.BallConstruction
public import Kakeya.DimensionThree.MainLemma2.ThinFactorFamily

/-!
# GWZ Lemma 9.2 run per ball on the segment family of a `BallDataCore`

General-branch steps G1/G2. GWZ
§9.3, `gwz.txt` l.2036–2038: "Now we apply the biased maximal density factoring, Lemma 9.2, to
`𝕋_B`, and we let `𝕎_B` be the resulting family of convex sets (the maximal density factoring
replaces `𝕋_B` by a large subset …)". The tree's Lemma 9.2 is
`ConvexSpaceBody.nonempty_biasedFactorization` (`Kakeya/Factorization.lean`), stated for a family
of convex bodies inside the unit ball `B̄(0, 1)` with reference body `closedUnitBall`; a ball
`B = B̄(ctr B, r₁)` of a `Kakeya.VeryNotSticky.BallDataCore` is carried onto it by the affine
change of variables `Kakeya.VeryNotSticky.ballHomothety`, `x ↦ r₁⁻¹ • (x - ctr B)`, and the
output is pulled back along its inverse.

## Contents

* `ballHomothety` with its action on `B̄(ctr, r)`, on `Metric.ethickness`, `Metric.thickness`
  and `Metric.ethickness.scale` (a homothety of ratio `r⁻¹` composed with a translation:
  `Metric.ethickness_homothety_image`, `Kakeya.ThinCase.ethickness_image_add_left`).
* `lemma92_on_core`: Lemma 9.2 elaborated against the transported segment family of one ball
  (P1). Its inputs are the two `BallDataCore` fields that are *not* `BallData` fields and were
  put there for this purpose: `segs_subset_ball` and `segs_scale`.
* The transports of the Frostman clause, of the biased density comparison `factmaxmod1` (GWZ
  (82)) and of GWZ (91) back along an affine equivalence (`Kakeya.densityIn_mapAffine`,
  `Kakeya.maxDensity_mapAffine`, `ConvexSpaceBody.volume_mapAffine`).
* `antiClustering_of_biasedFactorization`, `coe_Cbias_eq` (P2): from Lemma 9.2's Katz–Tao clause
  `Δ_max(𝕎) ≤ C (|W|/|U|)^{-ϱ}` — GWZ (83), l.1962 — and a volume-ratio floor `c₃ δ² ≤ |W|/|U|`
  to the field text of `Kakeya.VeryNotSticky.BallData.bodies_antiClustering`,
  `Δ_max(𝕎_B) ≤ C_bias δ^{-2ϱ}`, with the `δ`-free `C_bias := C · c₃^{-ϱ}`.
* `volume_ratio_floor`: the floor itself, from the thickness profile `(r₁, δ, δ)` of one segment
  of the block (`Convex.ethickness_prod_le_volume`), at the explicit dimensional constant
  `ratioFloorConstant C₀ = c(3) C₀^{-3} / 8`.
* **`exists_ballFactoring_core`**, the output theorem: for every ball `B ∈ core.bs`, a retained
  tier `s' ⊆ core.segs B`, the family `parts` of blocks, the bodies `Wb` and the block map `blk`
  with (i) the carrier-volume retention at Lemma 9.2's polylogarithmic loss
  `ConvexSpaceBody.nonempty_biasedFactorization.L`, (ii)–(vii) the binders `blk_mem`, `segs_le`,
  `bodies_subset_ball`, `frostman`, `biasedDensity`, `bodies_antiClustering` of
  `Kakeya.VeryNotSticky.BallDataCore.toBallData` in their per-ball form (with `s'` for
  `core.segs B` and `parts` for `bodies B`), at the constants `CF := lemma92Constant cfg.ϱ`,
  `Cbias := lemma92Bias core.C₀ cfg.ϱ`, and (viii)–(ix) the two extra clauses the dims
  pigeonhole (G4) and the thick producer (G10) read: GWZ (91) at `U = B` and `simDims`, both
  pulled back into the ball.

## What Lemma 9.2 does not deliver (left to the consumers, never asserted here)

`bodies_thickness` and `bodies_w₁` (the dims pigeonhole, G4), `segs_density` (the Markov tier,
G3) and `segs_dilation` (T3's `Kakeya.VeryNotSticky.segs_dilation_capsules`). Nothing here
changes a existing statement.

Essential distinctness of a ball's bodies is not on that list, and is owed to no one: Lemma
4.1/9.2 assert Katz–Tao and Frostman and never essential distinctness, and statement question
R26 accordingly deleted the field `BallData.bodies_essDistinct` outright.
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

universe u

namespace Kakeya.VeryNotSticky

/-! ### The ball homothety `B̄(ctr, r) → B̄(0, 1)` -/

section BallHomothety

variable (ctr : EuclideanSpace ℝ (Fin 3)) (r : NNReal) (hr : 0 < r)

/-- The affine change of variables `x ↦ r⁻¹ • (x - ctr)`, taking `B̄(ctr, r)` onto `B̄(0, 1)`;
its inverse is `y ↦ r • y + ctr`. -/
noncomputable def ballHomothety :
    EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin 3) where
  toFun x := (r : ℝ)⁻¹ • (x - ctr)
  invFun y := (r : ℝ) • y + ctr
  left_inv x := by
    have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
    simp [smul_smul, mul_inv_cancel₀ hr']
  right_inv y := by
    have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
    simp [smul_smul, inv_mul_cancel₀ hr']
  linear := LinearEquiv.smulOfNeZero ℝ (EuclideanSpace ℝ (Fin 3)) (r : ℝ)⁻¹
    (inv_ne_zero (by exact_mod_cast hr.ne'))
  map_vadd' p v := by
    simp only [LinearEquiv.smulOfNeZero_apply, vadd_eq_add, Equiv.coe_fn_mk]
    rw [add_sub_assoc, smul_add]

@[simp] theorem ballHomothety_apply (x : EuclideanSpace ℝ (Fin 3)) :
    ballHomothety ctr r hr x = (r : ℝ)⁻¹ • (x - ctr) := rfl

@[simp] theorem ballHomothety_symm_apply (y : EuclideanSpace ℝ (Fin 3)) :
    (ballHomothety ctr r hr).symm y = (r : ℝ) • y + ctr := rfl

/-- The ball homothety carries `B̄(ctr, r)` onto the unit ball. -/
theorem ballHomothety_image_closedBall :
    ballHomothety ctr r hr '' closedBall ctr (r : ℝ) =
      closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_closedBall, dist_eq_norm] at hx
    rw [mem_closedBall_zero_iff, ballHomothety_apply, norm_smul, norm_inv,
      Real.norm_of_nonneg hr'.le]
    calc (r : ℝ)⁻¹ * ‖x - ctr‖ ≤ (r : ℝ)⁻¹ * r := by gcongr
      _ = 1 := inv_mul_cancel₀ hr'.ne'
  · intro hy
    rw [mem_closedBall_zero_iff] at hy
    refine ⟨(r : ℝ) • y + ctr, ?_, ?_⟩
    · rw [mem_closedBall, dist_eq_norm, add_sub_cancel_right, norm_smul,
        Real.norm_of_nonneg hr'.le]
      calc (r : ℝ) * ‖y‖ ≤ (r : ℝ) * 1 := by gcongr
        _ = r := mul_one _
    · exact (ballHomothety ctr r hr).apply_symm_apply y

/-- The inverse ball homothety carries the unit ball onto `B̄(ctr, r)`. -/
theorem ballHomothety_symm_image_closedBall :
    (ballHomothety ctr r hr).symm '' closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 =
      closedBall ctr (r : ℝ) := by
  rw [AffineEquiv.image_symm, ← ballHomothety_image_closedBall ctr r hr,
    (ballHomothety ctr r hr).injective.preimage_image]

/-- The ball homothety is the homothety of centre `0` and ratio `r⁻¹` after the translation by
`-ctr`. -/
theorem ballHomothety_image_eq (X : Set (EuclideanSpace ℝ (Fin 3))) :
    ballHomothety ctr r hr '' X =
      AffineMap.homothety (0 : EuclideanSpace ℝ (Fin 3)) (r : ℝ)⁻¹ ''
        ((fun x ↦ -ctr + x) '' X) := by
  rw [Set.image_image]
  refine Set.image_congr fun x _ ↦ ?_
  simp [AffineMap.homothety_apply, neg_add_eq_sub]

/-- **Ethickness under the ball homothety**: every affine thickness is multiplied by `r⁻¹`. -/
theorem ethickness_ballHomothety_image (X : Set (EuclideanSpace ℝ (Fin 3))) (n : ℕ) :
    ethickness ℝ (ballHomothety ctr r hr '' X) n = (r : ENNReal)⁻¹ * ethickness ℝ X n := by
  have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [ballHomothety_image_eq, ethickness_homothety_image _ (inv_ne_zero hr'),
    Kakeya.ThinCase.ethickness_image_add_left, nnnorm_inv, NNReal.nnnorm_eq,
    ENNReal.coe_inv hr.ne']

/-- **The scale under the ball homothety**: `Metric.ethickness.scale` is multiplied by `r⁻¹`. -/
theorem ethickness_scale_ballHomothety_image (X : Set (EuclideanSpace ℝ (Fin 3))) :
    ethickness.scale ℝ (ballHomothety ctr r hr '' X) =
      (r : ENNReal)⁻¹ * ethickness.scale ℝ X := by
  have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [ballHomothety_image_eq, ethickness.scale_homothety_image _ (inv_ne_zero hr'),
    Kakeya.ThinCase.ethickness_scale_image_add_left, nnnorm_inv, NNReal.nnnorm_eq,
    ENNReal.coe_inv hr.ne']

/-- The image of a bounded set under the ball homothety is bounded. -/
theorem isBounded_ballHomothety_image {X : Set (EuclideanSpace ℝ (Fin 3))}
    (hX : Bornology.IsBounded X) : Bornology.IsBounded (ballHomothety ctr r hr '' X) := by
  rw [ballHomothety_image_eq]
  exact (Kakeya.lipschitzWith_homothety _ _).isBounded_image
    (Kakeya.ThinCase.isBounded_image_add_left _ hX)

/-- **Thickness under the ball homothety**, real-valued form. -/
theorem thickness_ballHomothety_image {X : Set (EuclideanSpace ℝ (Fin 3))}
    (hX : Bornology.IsBounded X) (n : ℕ) :
    thickness ℝ (ballHomothety ctr r hr '' X) n = (r : ℝ)⁻¹ * thickness ℝ X n := by
  rw [← toReal_ethickness (isBounded_ballHomothety_image ctr r hr hX), ← toReal_ethickness hX,
    ethickness_ballHomothety_image, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.coe_toReal]

/-- A comparison of ethickness profiles read in the unit ball holds in the ball itself (the
common factor `r⁻¹` cancels). -/
theorem ethickness_le_smul_of_ballHomothety_image {X X' : Set (EuclideanSpace ℝ (Fin 3))}
    {C : NNReal}
    (h : ethickness ℝ (ballHomothety ctr r hr '' X) ≤
      C • ethickness ℝ (ballHomothety ctr r hr '' X')) :
    ethickness ℝ X ≤ C • ethickness ℝ X' := by
  intro n
  have hn := h n
  simp only [Pi.smul_apply, ethickness_ballHomothety_image, ENNReal.smul_def, smul_eq_mul] at hn ⊢
  rw [mul_left_comm] at hn
  exact (ENNReal.mul_le_mul_iff_right (ENNReal.inv_ne_zero.2 ENNReal.coe_ne_top)
    (ENNReal.inv_ne_top.2 (by exact_mod_cast hr.ne'))).1 hn

end BallHomothety

/-! ### Lemma 9.2 on the transported segment family of one ball (P1) -/

open scoped Classical in
/-- **Lemma 9.2 on one ball of a `BallDataCore`** (P1). For any affine change of variables `L`
under which the segments of the ball `B` land in the unit ball with scale `≥ δ'`, Lemma 9.2
(`ConvexSpaceBody.nonempty_biasedFactorization`) returns a retained tier `s' ⊆ core.segs B`, the
carrier-volume retention at the polylogarithmic loss `L`, and a biased factoring of `s'` at bias
`cfg.ϱ` and the `δ`-free constant `C (finrank) cfg.ϱ`. -/
theorem lemma92_on_core (cfg : VeryNotSticky.{u}) (core : BallDataCore cfg) {B : core.bι}
    (hB : B ∈ core.bs) (L : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin 3))
    {δ' : NNReal} (hδ' : 0 < δ')
    (h1 : ∀ p ∈ core.segs B,
      (((core.Y p).toConvexSpaceBody).mapAffine L).carrier ⊆ Metric.closedBall 0 1)
    (h2 : ∀ p ∈ core.segs B,
      δ' ≤ Metric.ethickness.scale ℝ (((core.Y p).toConvexSpaceBody).mapAffine L).carrier) :
    ∃ s' ⊆ core.segs B,
      (∑ p ∈ core.segs B, volume (((core.Y p).toConvexSpaceBody).mapAffine L).carrier ≤
        ConvexSpaceBody.nonempty_biasedFactorization.L
            (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) (core.segs B).card δ' cfg.ϱ *
          ∑ p ∈ s', volume (((core.Y p).toConvexSpaceBody).mapAffine L).carrier) ∧
      Nonempty (ConvexSpaceBody.BiasedFactorization s'
        (fun p ↦ ((core.Y p).toConvexSpaceBody).mapAffine L)
        ConvexSpaceBody.closedUnitBall cfg.ϱ
        (ConvexSpaceBody.nonempty_biasedFactorization.C
          (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) cfg.ϱ)) :=
  ConvexSpaceBody.nonempty_biasedFactorization (s := core.segs B)
    (V := fun p ↦ ((core.Y p).toConvexSpaceBody).mapAffine L)
    cfg.hϱ hδ' (core.segs_nonempty B hB) h1 h2

/-! ### Transports back along an affine equivalence -/

section Transport

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*}

/-- The Frostman property (GWZ Definition 3.2) is invariant under affine transport. -/
theorem isFrostmanIn_mapAffine_iff (s : Finset ι) (W : ι → ConvexSpaceBody E)
    (K : ConvexSpaceBody E) (f : E ≃ᵃ[ℝ] E) (C : ENNReal) :
    ConvexSpaceBody.IsFrostmanIn s (fun i ↦ (W i).mapAffine f) (K.mapAffine f) C ↔
      ConvexSpaceBody.IsFrostmanIn s W K C := by
  constructor
  · intro h K' hK'
    have := h (K'.mapAffine f) ((ConvexSpaceBody.mapAffine_le_mapAffine_iff f).2 hK')
    rwa [densityIn_mapAffine, densityIn_mapAffine] at this
  · intro h K' hK'
    have h1 : K'.mapAffine f.symm ≤ K := by
      have := (ConvexSpaceBody.mapAffine_le_mapAffine_iff f.symm).2 hK'
      rwa [ConvexSpaceBody.mapAffine_symm_mapAffine] at this
    have h2 := h _ h1
    rwa [← densityIn_mapAffine s W (K'.mapAffine f.symm) f, ← densityIn_mapAffine s W K f,
      ConvexSpaceBody.symm_mapAffine_mapAffine] at h2

/-- The biased density comparison `factmaxmod1` (GWZ (82)) transports back along an affine
equivalence: the volume ratio is affine-invariant (the Jacobians cancel). -/
theorem densityIn_le_biased_of_mapAffine (s : Finset ι) (W : ι → ConvexSpaceBody E)
    (Wb : ConvexSpaceBody E) (f : E ≃ᵃ[ℝ] E) {C : ENNReal} {ϱ : ℝ}
    (h : ∀ K : ConvexSpaceBody E,
      densityIn s (fun i ↦ (W i).mapAffine f) K ≤
        C * (volume K.carrier / volume (Wb.mapAffine f).carrier) ^ ϱ *
          densityIn s (fun i ↦ (W i).mapAffine f) (Wb.mapAffine f)) :
    ∀ K : ConvexSpaceBody E,
      densityIn s W K ≤ C * (volume K.carrier / volume Wb.carrier) ^ ϱ * densityIn s W Wb := by
  intro K
  have := h (K.mapAffine f)
  rwa [densityIn_mapAffine, densityIn_mapAffine, ConvexSpaceBody.volume_mapAffine,
    ConvexSpaceBody.volume_mapAffine,
    ENNReal.mul_div_mul_left _ _ (affineJacobian_ne_zero f) (affineJacobian_ne_top f)] at this

/-- GWZ (91), `Δ(𝕍_W, W) ≳ (|W|/|U|)^ϱ Δ_max(𝕍)` (the maximal density of the whole family `s`,
the density of the block `t`), transports back along an affine equivalence carrying the
reference set `U` onto `f '' U`. -/
theorem maxDensity_le_densityIn_biased_of_mapAffine (s t : Finset ι)
    (W : ι → ConvexSpaceBody E) (Wb : ConvexSpaceBody E) (U : Set E) (f : E ≃ᵃ[ℝ] E)
    {C : ENNReal} {ϱ : ℝ}
    (h : C⁻¹ * (volume (Wb.mapAffine f).carrier / volume (f '' U)) ^ ϱ *
        maxDensity s (fun i ↦ (W i).mapAffine f) ≤
      densityIn t (fun i ↦ (W i).mapAffine f) (Wb.mapAffine f)) :
    C⁻¹ * (volume Wb.carrier / volume U) ^ ϱ * maxDensity s W ≤ densityIn t W Wb := by
  rwa [densityIn_mapAffine, maxDensity_mapAffine, ConvexSpaceBody.volume_mapAffine,
    volume_image_affineEquiv,
    ENNReal.mul_div_mul_left _ _ (affineJacobian_ne_zero f) (affineJacobian_ne_top f)] at h

end Transport

/-! ### From Lemma 9.2's Katz–Tao clause to `bodies_antiClustering` (P2) -/

section AntiClustering

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem antiClustering_of_isKatzTao_ratio {ι : Type*} (parts : Finset ι)
    (W : ι → ConvexSpaceBody E) (U : ConvexSpaceBody E) {ϱ : ℝ} (hϱ : 0 ≤ ϱ)
    {C c : NNReal} (hc : c ≠ 0) {δ : NNReal} (hδ : δ ≠ 0) {t : ι} (_ht : t ∈ parts)
    (hKT : ConvexSpaceBody.IsKatzTao parts W
      ((C : ENNReal) * (volume (W t).carrier / volume U.carrier) ^ (-ϱ)))
    (hratio : (c : ENNReal) * (δ : ENNReal) ^ (2 : ℝ) ≤ volume (W t).carrier / volume U.carrier) :
    maxDensity parts W ≤ (C : ENNReal) * (c : ENNReal) ^ (-ϱ) * (δ : ENNReal) ^ (-(2 * ϱ)) := by
  have hδpos : (0 : ENNReal) < (δ : ENNReal) := ENNReal.coe_pos.2 (pos_iff_ne_zero.2 hδ)
  have hδ2 : (δ : ENNReal) ^ (2 : ℝ) ≠ 0 := (ENNReal.rpow_pos hδpos ENNReal.coe_ne_top).ne'
  have hc' : (c : ENNReal) ≠ 0 := by exact_mod_cast hc
  have hmono : (volume (W t).carrier / volume U.carrier) ^ (-ϱ) ≤
      ((c : ENNReal) * (δ : ENNReal) ^ (2 : ℝ)) ^ (-ϱ) := by
    rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
    exact ENNReal.inv_le_inv.2 (ENNReal.rpow_le_rpow hratio hϱ)
  have hsplit : ((c : ENNReal) * (δ : ENNReal) ^ (2 : ℝ)) ^ (-ϱ) =
      (c : ENNReal) ^ (-ϱ) * (δ : ENNReal) ^ (-(2 * ϱ)) := by
    rw [ENNReal.mul_rpow_of_ne_zero hc' hδ2, ← ENNReal.rpow_mul]
    congr 2; ring
  calc maxDensity parts W
      ≤ (C : ENNReal) * (volume (W t).carrier / volume U.carrier) ^ (-ϱ) := hKT
    _ ≤ (C : ENNReal) * ((c : ENNReal) * (δ : ENNReal) ^ (2 : ℝ)) ^ (-ϱ) := by gcongr
    _ = (C : ENNReal) * (c : ENNReal) ^ (-ϱ) * (δ : ENNReal) ^ (-(2 * ϱ)) := by
        rw [hsplit, mul_assoc]

/-- The same, read directly off a `BiasedFactorization` (Lemma 9.2's output type), on the family
of outer bodies `t ↦ t.convexHull_biUnion V` that `Kakeya.VeryNotSticky.BallData.Wb` will be
(before the pull-back). -/
theorem antiClustering_of_biasedFactorization {ι : Type*} [DecidableEq ι] {s' : Finset ι}
    {V : ι → ConvexSpaceBody E} {U : ConvexSpaceBody E} {ϱ : ℝ} (hϱ : 0 ≤ ϱ) {C : NNReal}
    (f : ConvexSpaceBody.BiasedFactorization s' V U ϱ C) {c δ : NNReal} (hc : c ≠ 0) (hδ : δ ≠ 0)
    {t : Finset ι} (ht : t ∈ f.parts)
    (hratio : (c : ENNReal) * (δ : ENNReal) ^ (2 : ℝ) ≤
      volume (t.convexHull_biUnion V).carrier / volume U.carrier) :
    maxDensity f.parts (fun t' ↦ t'.convexHull_biUnion V) ≤
      (C : ENNReal) * (c : ENNReal) ^ (-ϱ) * (δ : ENNReal) ^ (-(2 * ϱ)) :=
  antiClustering_of_isKatzTao_ratio f.parts _ U hϱ hc hδ ht (f.isKatzTao t ht) hratio

/-- The δ-free `Cbias := C * c⁻¹ ^ ϱ` as an `NNReal`, cast to the field's coefficient. -/
theorem coe_Cbias_eq {C c : NNReal} (hc : c ≠ 0) {ϱ : ℝ} :
    ((C * c⁻¹ ^ ϱ : NNReal) : ENNReal) = (C : ENNReal) * (c : ENNReal) ^ (-ϱ) := by
  rw [ENNReal.coe_mul, ENNReal.coe_rpow_of_ne_zero (inv_ne_zero hc), ENNReal.coe_inv hc,
    ENNReal.inv_rpow, ENNReal.rpow_neg]

end AntiClustering

/-! ### The constants -/

/-- `CF`: the constant of Lemma 9.2 (`ConvexSpaceBody.nonempty_biasedFactorization.C`) in the
ambient dimension `3` at bias `ϱ`; `2 · volume_comparison.C 3 ^ ϱ`, `δ`-free and `≥ 2`. -/
noncomputable def lemma92Constant (ϱ : ℝ) : NNReal :=
  ConvexSpaceBody.nonempty_biasedFactorization.C 3 ϱ

theorem lemma92Constant_eq (ϱ : ℝ) :
    lemma92Constant ϱ = 2 * Metric.volume_comparison.C 3 ^ ϱ := rfl

theorem one_le_lemma92Constant {ϱ : ℝ} (hϱ : 0 ≤ ϱ) : 1 ≤ lemma92Constant ϱ := by
  rw [lemma92Constant_eq]
  have h1 : (1 : NNReal) ≤ Metric.volume_comparison.C 3 := by
    norm_num [Metric.volume_comparison.C, Metric.lt_volume_convexHull.c]
  calc (1 : NNReal) ≤ 2 * 1 := by norm_num
    _ ≤ 2 * Metric.volume_comparison.C 3 ^ ϱ := by
      gcongr
      exact NNReal.one_le_rpow h1 hϱ

/-- `c₃`: the dimensional constant of the volume-ratio floor `volume_ratio_floor`,
`c(3) · C₀^{-3} / 8` with `c(3) = Metric.lt_volume_convexHull.c 3 = 1/3!`. -/
noncomputable def ratioFloorConstant (C₀ : NNReal) : NNReal :=
  Metric.lt_volume_convexHull.c 3 * C₀⁻¹ ^ 3 / 8

theorem ratioFloorConstant_pos {C₀ : NNReal} (hC₀ : 1 ≤ C₀) : 0 < ratioFloorConstant C₀ := by
  have hC₀' : (0 : NNReal) < C₀ := lt_of_lt_of_le one_pos hC₀
  unfold ratioFloorConstant
  exact div_pos (mul_pos (Metric.lt_volume_convexHull.c_pos 3) (pow_pos (inv_pos.2 hC₀') 3))
    (by norm_num)

theorem ratioFloorConstant_le_one {C₀ : NNReal} (hC₀ : 1 ≤ C₀) : ratioFloorConstant C₀ ≤ 1 := by
  unfold ratioFloorConstant
  have hc : Metric.lt_volume_convexHull.c 3 ≤ 1 := by
    change ((Nat.factorial 3 : ℕ) : NNReal)⁻¹ ≤ 1
    exact inv_le_one_of_one_le₀ (by norm_num [Nat.factorial])
  have hinv : C₀⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hC₀
  calc Metric.lt_volume_convexHull.c 3 * C₀⁻¹ ^ 3 / 8 ≤ 1 * 1 ^ 3 / 8 := by gcongr
    _ = (8 : NNReal)⁻¹ := by rw [one_pow, one_mul, one_div]
    _ ≤ 1 := inv_le_one_of_one_le₀ (by norm_num)

/-- `Cbias := CF · c₃^{-ϱ}`, the coefficient of `bodies_antiClustering` and `biasedDensity`;
`δ`-free, `≥ CF ≥ 1`. -/
noncomputable def lemma92Bias (C₀ : NNReal) (ϱ : ℝ) : NNReal :=
  lemma92Constant ϱ * (ratioFloorConstant C₀)⁻¹ ^ ϱ

theorem lemma92Constant_le_lemma92Bias {C₀ : NNReal} (hC₀ : 1 ≤ C₀) {ϱ : ℝ} (hϱ : 0 ≤ ϱ) :
    lemma92Constant ϱ ≤ lemma92Bias C₀ ϱ := by
  unfold lemma92Bias
  have h1 : 1 ≤ (ratioFloorConstant C₀)⁻¹ ^ ϱ :=
    NNReal.one_le_rpow
      ((one_le_inv₀ (ratioFloorConstant_pos hC₀)).2 (ratioFloorConstant_le_one hC₀)) hϱ
  calc lemma92Constant ϱ = lemma92Constant ϱ * 1 := (mul_one _).symm
    _ ≤ lemma92Constant ϱ * (ratioFloorConstant C₀)⁻¹ ^ ϱ := by gcongr

theorem one_le_lemma92Bias {C₀ : NNReal} (hC₀ : 1 ≤ C₀) {ϱ : ℝ} (hϱ : 0 ≤ ϱ) :
    1 ≤ lemma92Bias C₀ ϱ :=
  (one_le_lemma92Constant hϱ).trans (lemma92Constant_le_lemma92Bias hC₀ hϱ)

theorem coe_lemma92Bias_eq {C₀ : NNReal} (hC₀ : 1 ≤ C₀) (ϱ : ℝ) :
    ((lemma92Bias C₀ ϱ : NNReal) : ENNReal) =
      (lemma92Constant ϱ : ENNReal) * (ratioFloorConstant C₀ : ENNReal) ^ (-ϱ) :=
  coe_Cbias_eq (ratioFloorConstant_pos hC₀).ne'

/-! ### The volume-ratio floor -/

/-- **The volume-ratio floor.** A convex body `K` with thickness profile `(r₁, δ, δ)` at
constant `C₀`, carried into the unit ball by the ball homothety of radius `r₁ ≤ 1`, occupies at
least the fraction `c₃ δ²` of the unit ball: `|K| ≥ c(3) C₀^{-3} r₁ δ²`
(`Convex.ethickness_prod_le_volume`), the homothety multiplies the volume by `r₁^{-3}`, so
`|L K| ≥ c(3) C₀^{-3} (δ/r₁)² ≥ c(3) C₀^{-3} δ²`, and `|B̄(0,1)| ≤ 2³`. This is the
`|W|/|B| ≳ ab/r₁² ≥ δ²` of the docstring of
`Kakeya.VeryNotSticky.BallData.bodies_antiClustering`, read on one segment of the block
(`W ⊇ T_B`). -/
theorem volume_ratio_floor (ctr : EuclideanSpace ℝ (Fin 3)) {r₁ : NNReal} (hr₁ : 0 < r₁)
    (hr₁1 : (r₁ : ℝ) ≤ 1) {C₀ δ : NNReal} (K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
    (hK : HasThicknesses K.carrier C₀ ![(r₁ : ℝ), (δ : ℝ), (δ : ℝ)]) :
    (ratioFloorConstant C₀ : ENNReal) * (δ : ENNReal) ^ (2 : ℝ) ≤
      volume (K.mapAffine (ballHomothety ctr r₁ hr₁)).carrier /
        volume (closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) := by
  have hKbdd : Bornology.IsBounded K.carrier := K.isCompact'.isBounded
  have hr₁ne : r₁ ≠ 0 := hr₁.ne'
  -- the three ethicknesses of `K`
  have h0 : ((C₀⁻¹ * r₁ : NNReal) : ENNReal) ≤ ethickness ℝ K.carrier 0 := by
    rw [ethickness_thickness' hKbdd, ← ENNReal.ofReal_coe_nnreal]
    refine ENNReal.ofReal_le_ofReal ?_
    have := (hK 0).1
    simpa using this
  have h1 : ((C₀⁻¹ * δ : NNReal) : ENNReal) ≤ ethickness ℝ K.carrier 1 := by
    rw [ethickness_thickness' hKbdd, ← ENNReal.ofReal_coe_nnreal]
    refine ENNReal.ofReal_le_ofReal ?_
    have := (hK 1).1
    simpa using this
  have h2 : ((C₀⁻¹ * δ : NNReal) : ENNReal) ≤ ethickness ℝ K.carrier 2 := by
    rw [ethickness_thickness' hKbdd, ← ENNReal.ofReal_coe_nnreal]
    refine ENNReal.ofReal_le_ofReal ?_
    have := (hK 2).1
    simpa using this
  have hprodK : ((C₀⁻¹ ^ 3 * r₁ * δ ^ 2 : NNReal) : ENNReal) ≤
      ∏ i ∈ Finset.range 3, ethickness ℝ K.carrier i := by
    rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ,
      Finset.prod_range_zero, one_mul]
    calc ((C₀⁻¹ ^ 3 * r₁ * δ ^ 2 : NNReal) : ENNReal)
        = ((C₀⁻¹ * r₁ : NNReal) : ENNReal) * ((C₀⁻¹ * δ : NNReal) : ENNReal) *
            ((C₀⁻¹ * δ : NNReal) : ENNReal) := by
          rw [← ENNReal.coe_mul, ← ENNReal.coe_mul]
          congr 1
          ring
      _ ≤ _ := by gcongr
  -- the volume of the transported body
  have hvol : ((ratioFloorConstant C₀ * 8 * δ ^ 2 : NNReal) : ENNReal) ≤
      volume (K.mapAffine (ballHomothety ctr r₁ hr₁)).carrier := by
    have h := (K.mapAffine (ballHomothety ctr r₁ hr₁)).convex.ethickness_prod_le_volume
    rw [finrank_euclideanSpace_fin] at h
    refine le_trans ?_ h
    have hprod : ∏ i ∈ Finset.range 3,
        ethickness ℝ (K.mapAffine (ballHomothety ctr r₁ hr₁)).carrier i =
        (r₁ : ENNReal)⁻¹ ^ 3 * ∏ i ∈ Finset.range 3, ethickness ℝ K.carrier i := by
      simp only [ConvexSpaceBody.mapAffine_carrier, ethickness_ballHomothety_image]
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    rw [hprod]
    have hinv : (1 : NNReal) ≤ r₁⁻¹ ^ 2 :=
      one_le_pow₀ ((one_le_inv₀ hr₁).2 (by exact_mod_cast hr₁1))
    have hkey : (ratioFloorConstant C₀ * 8 * δ ^ 2 : NNReal) ≤
        Metric.lt_volume_convexHull.c 3 * (r₁⁻¹ ^ 3 * (C₀⁻¹ ^ 3 * r₁ * δ ^ 2)) := by
      have h8 : ratioFloorConstant C₀ * 8 = Metric.lt_volume_convexHull.c 3 * C₀⁻¹ ^ 3 :=
        div_mul_cancel₀ _ (by norm_num)
      have hr : r₁⁻¹ ^ 3 * r₁ = r₁⁻¹ ^ 2 := by
        rw [pow_succ, mul_assoc, inv_mul_cancel₀ hr₁ne, mul_one]
      calc ratioFloorConstant C₀ * 8 * δ ^ 2
          = Metric.lt_volume_convexHull.c 3 * C₀⁻¹ ^ 3 * δ ^ 2 * 1 := by rw [h8, mul_one]
        _ ≤ Metric.lt_volume_convexHull.c 3 * C₀⁻¹ ^ 3 * δ ^ 2 * r₁⁻¹ ^ 2 := by gcongr
        _ = Metric.lt_volume_convexHull.c 3 * (r₁⁻¹ ^ 3 * (C₀⁻¹ ^ 3 * r₁ * δ ^ 2)) := by
          rw [← hr]; ring
    calc ((ratioFloorConstant C₀ * 8 * δ ^ 2 : NNReal) : ENNReal)
        ≤ ((Metric.lt_volume_convexHull.c 3 * (r₁⁻¹ ^ 3 * (C₀⁻¹ ^ 3 * r₁ * δ ^ 2)) : NNReal) :
            ENNReal) := by exact_mod_cast hkey
      _ = (Metric.lt_volume_convexHull.c 3 : ENNReal) *
            ((r₁ : ENNReal)⁻¹ ^ 3 * ((C₀⁻¹ ^ 3 * r₁ * δ ^ 2 : NNReal) : ENNReal)) := by
          rw [ENNReal.coe_mul, ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.coe_inv hr₁ne]
      _ ≤ (Metric.lt_volume_convexHull.c 3 : ENNReal) *
            ((r₁ : ENNReal)⁻¹ ^ 3 * ∏ i ∈ Finset.range 3, ethickness ℝ K.carrier i) := by
          gcongr
  -- the unit ball
  have hB8 : volume (closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) ≤ 8 := by
    have := volume_closedBall_le_two_pow_finrank (E := EuclideanSpace ℝ (Fin 3))
    rw [finrank_euclideanSpace_fin] at this
    exact this.trans_eq (by norm_num)
  have hBne : volume (closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) ≠ 0 :=
    (measure_closedBall_pos volume 0 one_pos).ne'
  have hBtop : volume (closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) ≠ ⊤ :=
    ne_top_of_le_ne_top (by norm_num) hB8
  rw [ENNReal.le_div_iff_mul_le (Or.inl hBne) (Or.inl hBtop)]
  calc (ratioFloorConstant C₀ : ENNReal) * (δ : ENNReal) ^ (2 : ℝ) *
        volume (closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)
      ≤ (ratioFloorConstant C₀ : ENNReal) * (δ : ENNReal) ^ (2 : ℝ) * 8 := by gcongr
    _ = ((ratioFloorConstant C₀ * 8 * δ ^ 2 : NNReal) : ENNReal) := by
        rw [ENNReal.rpow_two]; push_cast; ring
    _ ≤ volume (K.mapAffine (ballHomothety ctr r₁ hr₁)).carrier := hvol

/-! ### The output theorem -/

open scoped Classical in
/-- **Lemma 9.2 per ball, pulled back into the ball** (GWZ `gwz.txt` l.2036–2038, (83) at
l.1962 with `U = B`). For every ball `B ∈ core.bs` of a `Kakeya.VeryNotSticky.BallDataCore`
there are a retained tier `s' ⊆ core.segs B`, a family `parts` of blocks (the parts of Lemma 9.2's
partition of `s'`), the bodies `Wb t` (the convex hull of the block's segments, pulled back into
`B`) and the block map `blk` (the part containing a segment), such that

1. the carrier volume of `core.segs B` is retained up to Lemma 9.2's polylogarithmic loss
   `ConvexSpaceBody.nonempty_biasedFactorization.L 3 |segs B| (δ/r₁) ϱ`;
2. `blk_mem`, 3. `segs_le`, 4. `bodies_subset_ball`, 5. `frostman` (at `CF = lemma92Constant ϱ`),
   6. `biasedDensity` and 7. `bodies_antiClustering` (both at `Cbias = lemma92Bias C₀ ϱ`), in the
   binder texts of `Kakeya.VeryNotSticky.BallDataCore.toBallData` read on the one ball `B`, with
   `s'` in place of `core.segs B` and `parts` in place of `bodies B`;
8. GWZ (91) at `U = B`: `CF⁻¹ (|W|/|B|)^ϱ Δ_max(𝕋'_B) ≤ Δ(𝕋_{B,W}, W)` for every block; and
9. `simDims`: the ethickness profiles of the bodies of one ball are `CF`-comparable.

Clauses 8 and 9 are the interface the dims pigeonhole (G4) and the thick producer (G10) read.
Not delivered (see the module docstring): `bodies_thickness`, `bodies_w₁` (G4),
`segs_density` (G3), `segs_dilation` (T3). Essential distinctness of the bodies is not on this
list any more: R26 deleted the field `BallData.bodies_essDistinct`. -/
theorem exists_ballFactoring_core (cfg : VeryNotSticky.{u}) (core : BallDataCore cfg)
    {B : core.bι} (hB : B ∈ core.bs) :
    ∃ (s' : Finset core.σ) (parts : Finset (Finset core.σ))
      (Wb : Finset core.σ → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
      (blk : core.σ → Finset core.σ),
      s' ⊆ core.segs B ∧
      (∑ p ∈ core.segs B, volume (core.Y p).carrier ≤
        ConvexSpaceBody.nonempty_biasedFactorization.L 3 (core.segs B).card (cfg.δ / cfg.r₁)
            cfg.ϱ *
          ∑ p ∈ s', volume (core.Y p).carrier) ∧
      (∀ p ∈ s', blk p ∈ parts) ∧
      (∀ p ∈ s', (core.Y p).toConvexSpaceBody ≤ Wb (blk p)) ∧
      (∀ j ∈ parts, (Wb j).carrier ⊆ closedBall (core.ctr B) (cfg.r₁ : ℝ)) ∧
      (∀ j ∈ parts,
        ConvexSpaceBody.IsFrostmanIn (s'.filter fun p => blk p = j)
          (fun p => (core.Y p).toConvexSpaceBody) (Wb j) (lemma92Constant cfg.ϱ)) ∧
      (∀ j ∈ parts,
        ∀ K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)), K ≤ Wb j →
          densityIn (s'.filter fun p => blk p = j)
              (fun p => (core.Y p).toConvexSpaceBody) K ≤
            (lemma92Bias core.C₀ cfg.ϱ : ENNReal) *
              (volume K.carrier / volume (Wb j).carrier) ^ cfg.ϱ *
              densityIn (s'.filter fun p => blk p = j)
                (fun p => (core.Y p).toConvexSpaceBody) (Wb j)) ∧
      maxDensity parts Wb ≤
        (lemma92Bias core.C₀ cfg.ϱ : ENNReal) * (cfg.δ : ENNReal) ^ (-(2 * cfg.ϱ)) ∧
      (∀ j ∈ parts,
        (lemma92Constant cfg.ϱ : ENNReal)⁻¹ *
            (volume (Wb j).carrier / volume (closedBall (core.ctr B) (cfg.r₁ : ℝ))) ^ cfg.ϱ *
            maxDensity s' (fun p => (core.Y p).toConvexSpaceBody) ≤
          densityIn (s'.filter fun p => blk p = j)
            (fun p => (core.Y p).toConvexSpaceBody) (Wb j)) ∧
      (∀ j ∈ parts, ∀ j' ∈ parts,
        ethickness ℝ (Wb j).carrier ≤ lemma92Constant cfg.ϱ • ethickness ℝ (Wb j').carrier) := by
  have hr₁ : 0 < cfg.r₁ := NNReal.rpow_pos cfg.hδ
  have hr₁1 : (cfg.r₁ : ℝ) ≤ 1 := r₁_le_one cfg
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := finrank_euclideanSpace_fin
  set L := ballHomothety (core.ctr B) cfg.r₁ hr₁ with hL
  set V : core.σ → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) :=
    fun p ↦ ((core.Y p).toConvexSpaceBody).mapAffine L with hV
  have hδ' : (0 : NNReal) < cfg.δ / cfg.r₁ := div_pos cfg.hδ hr₁
  -- the two inputs of Lemma 9.2, from `segs_subset_ball` and `segs_scale`
  have h1 : ∀ p ∈ core.segs B, (V p).carrier ⊆ closedBall 0 1 := by
    intro p hp
    simp only [hV, ConvexSpaceBody.mapAffine_carrier]
    rw [← ballHomothety_image_closedBall (core.ctr B) cfg.r₁ hr₁]
    exact Set.image_mono (core.segs_subset_ball B hB p hp)
  have h2 : ∀ p ∈ core.segs B,
      ((cfg.δ / cfg.r₁ : NNReal) : ENNReal) ≤ ethickness.scale ℝ (V p).carrier := by
    intro p hp
    simp only [hV, ConvexSpaceBody.mapAffine_carrier]
    rw [ethickness_scale_ballHomothety_image, ENNReal.coe_div hr₁.ne', ENNReal.div_eq_inv_mul]
    gcongr
    exact core.segs_scale B hB p hp
  obtain ⟨s', hs', hret, ⟨f⟩⟩ := lemma92_on_core cfg core hB L hδ' h1 h2
  rw [hfin] at hret f
  -- the pulled-back bodies and the block map
  set Wb : Finset core.σ → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) :=
    fun t ↦ (t.convexHull_biUnion V).mapAffine L.symm with hWbdef
  have hWb : ∀ t, (Wb t).mapAffine L = t.convexHull_biUnion V := fun t ↦
    ConvexSpaceBody.symm_mapAffine_mapAffine _ _
  have hfilter : ∀ t ∈ f.parts, s'.filter (fun p ↦ f.part p = t) = t := by
    intro t ht
    ext p
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hp, rfl⟩
      exact f.mem_part hp
    · intro hp
      exact ⟨f.le ht hp, f.part_eq_of_mem ht hp⟩
  have hJ0 := affineJacobian_ne_zero L
  have hJtop := affineJacobian_ne_top L
  refine ⟨s', f.parts, Wb, fun p ↦ f.part p, hs', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- 1. retention, pulled back (the Jacobian cancels)
    simp only [ConvexSpaceBody.volume_mapAffine, ← Finset.mul_sum] at hret
    rw [mul_left_comm] at hret
    exact (ENNReal.mul_le_mul_iff_right hJ0 hJtop).1 hret
  · -- 2. `blk_mem`
    intro p hp
    exact f.part_mem.2 hp
  · -- 3. `segs_le`
    intro p hp
    have h := (ConvexSpaceBody.mapAffine_le_mapAffine_iff L.symm).2
      (Finset.le_convexHull_biUnion V (f.mem_part hp))
    rwa [hV, ConvexSpaceBody.mapAffine_symm_mapAffine] at h
  · -- 4. `bodies_subset_ball`
    intro t ht
    have hle : t.convexHull_biUnion V ≤ ConvexSpaceBody.closedUnitBall :=
      ((f.nonempty_of_mem_parts ht).convexHull_biUnion_le_iff V _).2
        fun p hp ↦ f.contained p (f.le ht hp)
    have hsub : (t.convexHull_biUnion V).carrier ⊆ closedBall 0 1 := hle
    calc (Wb t).carrier = L.symm '' (t.convexHull_biUnion V).carrier := rfl
      _ ⊆ L.symm '' closedBall 0 1 := Set.image_mono hsub
      _ = closedBall (core.ctr B) (cfg.r₁ : ℝ) :=
          ballHomothety_symm_image_closedBall (core.ctr B) cfg.r₁ hr₁
  · -- 5. `frostman`
    intro t ht
    rw [hfilter t ht]
    refine (isFrostmanIn_mapAffine_iff t (fun p => (core.Y p).toConvexSpaceBody) (Wb t) L _).1 ?_
    rw [hWb t]
    exact f.isFrostman cfg.hϱ.le t ht
  · -- 6. `biasedDensity`, at `Cbias ≥ CF`
    intro t ht K _
    rw [hfilter t ht]
    have hC := densityIn_le_biased_of_mapAffine t (fun p => (core.Y p).toConvexSpaceBody) (Wb t) L
      (by rw [hWb t]; exact f.densityIn_le_biased t ht) K
    refine hC.trans ?_
    gcongr
    exact_mod_cast lemma92Constant_le_lemma92Bias core.hC₀ cfg.hϱ.le
  · -- 7. `bodies_antiClustering`
    rcases f.parts.eq_empty_or_nonempty with hemp | ⟨t, ht⟩
    · rw [hemp, maxDensity_empty]
      exact zero_le
    · rw [hWbdef, maxDensity_mapAffine, coe_lemma92Bias_eq core.hC₀]
      refine antiClustering_of_biasedFactorization cfg.hϱ.le f
        (ratioFloorConstant_pos core.hC₀).ne' cfg.hδ.ne' ht ?_
      obtain ⟨p, hp⟩ := f.nonempty_of_mem_parts ht
      have hp' : p ∈ core.segs B := hs' (f.le ht hp)
      calc (ratioFloorConstant core.C₀ : ENNReal) * (cfg.δ : ENNReal) ^ (2 : ℝ)
          ≤ volume (V p).carrier / volume (closedBall 0 1) :=
            volume_ratio_floor (core.ctr B) hr₁ hr₁1 _ (core.segs_thickness B hB p hp')
        _ ≤ volume (t.convexHull_biUnion V).carrier /
              volume ConvexSpaceBody.closedUnitBall.carrier := by
            rw [ConvexSpaceBody.closedUnitBall_carrier]
            exact ENNReal.div_le_div_right
              (measure_mono (Finset.le_convexHull_biUnion V hp)) _
  · -- 8. GWZ (91) at `U = B`
    intro t ht
    rw [hfilter t ht]
    refine maxDensity_le_densityIn_biased_of_mapAffine s' t
      (fun p => (core.Y p).toConvexSpaceBody) (Wb t) (closedBall (core.ctr B) (cfg.r₁ : ℝ)) L ?_
    rw [hWb t, hL, ballHomothety_image_closedBall]
    have h := f.maxDensity_le_densityIn_biased t ht
    rwa [ConvexSpaceBody.closedUnitBall_carrier] at h
  · -- 9. `simDims`
    intro t ht t' ht'
    have h := f.simDims t ht t' ht'
    rw [← hWb t, ← hWb t', ConvexSpaceBody.mapAffine_carrier,
      ConvexSpaceBody.mapAffine_carrier] at h
    exact ethickness_le_smul_of_ballHomothety_image (core.ctr B) cfg.r₁ hr₁ h

end Kakeya.VeryNotSticky
