/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.SlabTube

/-!
# Normalising a *dilated* thickened plank into a tube

`Plank.image_carrier_subset_slabTube` normalises a thickened plank `P_θ` into the `b/8`-tube
`Plank.slabTube P S κ` at the working constant `κ = Plank.slabTubeConst Cset Cang`.  GWZ Lemma 6.13
does not hand back a shading contained in the representative prism `Q` itself, but one contained in a
fixed dilation `Q.dilation Cbox`, so the family-level tube interface has to accept a body that is
`Cbox` times too large.

No new transverse geometry is needed for this: the normalising map `Slab.normalizeScaled S κ` is
linear in `x - S.center`, so replacing `κ` by `κ / C` scales *everything* by `1 / C`, and the image
of the `C`-dilated prism at scale `κ / C` is a **translate** of the image of the undilated prism at
scale `κ`.  The tube attached to the plank translates by the same vector, because its core is the
unit segment through the image of the plank's centre and its direction is scale invariant.  Hence
the same `b/8`-tube radius works.
-/

@[expose] public section

open MeasureTheory Metric
open scoped NNReal

noncomputable section

namespace Slab

variable {θ : ℝ≥0} {hθ : θ ≤ 1}

/-- **The normalising map is homogeneous in its scale.**  `Slab.normalizeScaled S κ` is the frame
scaling with factors `(κ/θ, κ, κ)` applied to `x - S.center`, so rescaling `κ` rescales the map. -/
theorem normalizeScaled_smul (S : Slab θ hθ) (κ κ' : ℝ≥0) (hθ0 : 0 < θ) (hκ : 0 < κ) (hκ' : 0 < κ')
    (x : EuclideanSpace ℝ (Fin 3)) :
    Slab.normalizeScaled S κ' hθ0 hκ' x
      = ((κ' : ℝ) / (κ : ℝ)) • Slab.normalizeScaled S κ hθ0 hκ x := by
  rw [Slab.normalizeScaled, Slab.normalizeScaled]
  rw [Kakeya.frameScaling_apply, Kakeya.frameScaling_apply]
  have hκ0 : (κ : ℝ) ≠ 0 := ne_of_gt (NNReal.coe_pos.mpr hκ)
  have hθ0r : (θ : ℝ) ≠ 0 := ne_of_gt (NNReal.coe_pos.mpr hθ0)
  have hvec : ![(κ' : ℝ) * (θ : ℝ)⁻¹, (κ' : ℝ), (κ' : ℝ)]
      = ((κ' : ℝ) / (κ : ℝ)) • ![(κ : ℝ) * (θ : ℝ)⁻¹, (κ : ℝ), (κ : ℝ)] := by
    funext i
    fin_cases i <;> simp [Pi.smul_apply] <;> field_simp [hκ0, hθ0r]
  rw [hvec]
  rw [Kakeya.frameDiagLinear_apply, Kakeya.frameDiagLinear_apply]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp [Pi.smul_apply, smul_smul, mul_assoc]

end Slab

namespace Plank

variable {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {θ : ℝ≥0} {hθ : θ ≤ 1}

/-- **The tube direction does not depend on the normalisation scale**: it is the normalisation of
the image of the plank's long axis, and rescaling the map rescales that image by a positive
factor. -/
theorem slabTubeDir_scale (P : Plank a b hab hb1) (S : Slab θ hθ) (κ κ' : ℝ≥0) (hθ0 : 0 < θ)
    (hκ : 0 < κ) (hκ' : 0 < κ') :
    P.slabTubeDir S κ' hθ0 hκ' = P.slabTubeDir S κ hθ0 hκ := by
  rw [slabTubeDir, slabTubeDir]
  set w : EuclideanSpace ℝ (Fin 3) := (Slab.normalizeScaled S κ hθ0 hκ).linear (P.basis 2)
  have hw' : (Slab.normalizeScaled S κ' hθ0 hκ').linear (P.basis 2)
      = ((κ' : ℝ) / (κ : ℝ)) • w := by
    have hxA := Slab.normalizeScaled_smul S κ κ' hθ0 hκ hκ' (P.basis 2 + S.center)
    have hx : (Slab.normalizeScaled S κ hθ0 hκ) (P.basis 2 + S.center)
        = (Slab.normalizeScaled S κ hθ0 hκ).linear (P.basis 2) := by
      rw [Slab.normalizeScaled, Kakeya.frameScaling_apply, Kakeya.frameScaling_linear]
      change Kakeya.frameDiagLinear S.basis ![(κ : ℝ) * (θ : ℝ)⁻¹, (κ : ℝ), (κ : ℝ)]
          (P.basis 2 + S.center - S.center)
          = Kakeya.frameDiagLinear S.basis ![(κ : ℝ) * (θ : ℝ)⁻¹, (κ : ℝ), (κ : ℝ)] (P.basis 2)
      simp
    have hx' : (Slab.normalizeScaled S κ' hθ0 hκ') (P.basis 2 + S.center)
        = (Slab.normalizeScaled S κ' hθ0 hκ').linear (P.basis 2) := by
      rw [Slab.normalizeScaled, Kakeya.frameScaling_apply, Kakeya.frameScaling_linear]
      change Kakeya.frameDiagLinear S.basis ![(κ' : ℝ) * (θ : ℝ)⁻¹, (κ' : ℝ), (κ' : ℝ)]
          (P.basis 2 + S.center - S.center)
          = Kakeya.frameDiagLinear S.basis ![(κ' : ℝ) * (θ : ℝ)⁻¹, (κ' : ℝ), (κ' : ℝ)] (P.basis 2)
      simp
    calc
      (Slab.normalizeScaled S κ' hθ0 hκ').linear (P.basis 2)
          = (Slab.normalizeScaled S κ' hθ0 hκ') (P.basis 2 + S.center) := hx'.symm
      _ = ((κ' : ℝ) / (κ : ℝ)) • (Slab.normalizeScaled S κ hθ0 hκ) (P.basis 2 + S.center) := hxA
      _ = ((κ' : ℝ) / (κ : ℝ)) • (Slab.normalizeScaled S κ hθ0 hκ).linear (P.basis 2) := by
        rw [hx]
  rw [hw']
  have htpos : 0 < ((κ' : ℝ) / (κ : ℝ)) :=
    div_pos (NNReal.coe_pos.mpr hκ') (NNReal.coe_pos.mpr hκ)
  have ht : (κ' : ℝ) / (κ : ℝ) ≠ 0 := ne_of_gt htpos
  rw [norm_smul]
  rw [Real.norm_eq_abs, abs_of_pos htpos]
  rw [smul_smul]
  have hnorm : (((κ' : ℝ) / (κ : ℝ)) * ‖w‖)⁻¹ * ((κ' : ℝ) / (κ : ℝ)) = ‖w‖⁻¹ := by
    by_cases hw : ‖w‖ = 0
    · simp [hw]
    · field_simp [ht, hw]
  rw [hnorm]

/-- **The tube of a plank translates when the normalisation scale changes**: both the core's centre
and the tube's direction are read off the same normalising map, so changing `κ` moves the tube by
the displacement of the plank's normalised centre. -/
theorem slabTube_scale_eq_vadd (P : Plank a b hab hb1) (S : Slab θ hθ) (κ κ' : ℝ≥0) (hθ0 : 0 < θ)
    (hκ : 0 < κ) (hκ' : 0 < κ') :
    P.slabTube S κ' hθ0 hκ'
      = (P.slabTube S κ hθ0 hκ).vadd
          (Slab.normalizeScaled S κ' hθ0 hκ' P.center
            - Slab.normalizeScaled S κ hθ0 hκ P.center) := by
  set v := Slab.normalizeScaled S κ' hθ0 hκ' P.center - Slab.normalizeScaled S κ hθ0 hκ P.center
  have hdir : P.slabTubeDir S κ' hθ0 hκ' = P.slabTubeDir S κ hθ0 hκ :=
    slabTubeDir_scale P S κ κ' hθ0 hκ hκ'
  have hx : (P.slabTube S κ' hθ0 hκ').x = v + (P.slabTube S κ hθ0 hκ).x := by
    simp [slabTube, hdir, v]
  have hy : (P.slabTube S κ' hθ0 hκ').y = v + (P.slabTube S κ hθ0 hκ).y := by
    simp [slabTube, hdir, v]
    module
  refine Tube.ext ?_ (by simpa [Tube.vadd_x] using hx) (by simpa [Tube.vadd_y] using hy)
  rw [Tube.carrier_eq, Tube.carrier_eq]
  rw [Tube.vadd_x, Tube.vadd_y]
  rw [hx, hy]

/-- **A `C`-dilated thickened plank normalises into the same `b/8`-tube, at the scale `κ / C`.**

This is the form GWZ Lemma 6.1 consumes: Lemma 6.13's shading `Yθ Q` lies in `Q.dilation Cbox`, and
normalising at `κ / Cbox` puts its image inside the tube attached to `Q` at that same scale.  No
enlargement of the tube radius is needed. -/
theorem image_dilation_carrier_subset_slabTube (P : Plank a b hab hb1) (S : Slab θ hθ)
    (hθ0 : 0 < θ) {κ κ' C : ℝ≥0} (hκ : 0 < κ) (hκ' : 0 < κ') (hC : 0 < C) (hκκ' : κ' * C = κ)
    (hbase : (Slab.normalizeScaled S κ hθ0 hκ) ''
        ((P.thickened θ hθ).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ (P.slabTube S κ hθ0 hκ).carrier) :
    (Slab.normalizeScaled S κ' hθ0 hκ') ''
        (((P.thickened θ hθ).toPrismNDim.dilation C).carrier :
          Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ (P.slabTube S κ' hθ0 hκ').carrier := by
  rintro y ⟨x, hx, rfl⟩
  let gκ : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3) :=
    Slab.normalizeScaled S κ hθ0 hκ
  let gκ' : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3) :=
    Slab.normalizeScaled S κ' hθ0 hκ'
  let c : EuclideanSpace ℝ (Fin 3) := P.center
  let t : ℝ := (C : ℝ)⁻¹
  let xStar : EuclideanSpace ℝ (Fin 3) := c + t • (x - c)
  let Q : PrismNDim 3 (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3)) :=
    (P.thickened θ hθ).toPrismNDim
  have hCpos : (0 : ℝ) < (C : ℝ) := by exact_mod_cast hC
  have hCne : (C : ℝ) ≠ 0 := ne_of_gt hCpos
  have hCinv : (C : ℝ)⁻¹ * (C : ℝ) = 1 := inv_mul_cancel₀ hCne
  have hκne : (κ : ℝ) ≠ 0 := ne_of_gt (NNReal.coe_pos.mpr hκ)
  have h_mul : (κ' : ℝ) * (C : ℝ) = (κ : ℝ) := by exact_mod_cast hκκ'
  have hsc : (κ' : ℝ) / (κ : ℝ) = (C : ℝ)⁻¹ := by
    rw [div_eq_iff hκne]
    calc
      (κ' : ℝ) = (κ' : ℝ) * ((C : ℝ)⁻¹ * (C : ℝ)) := by rw [hCinv, mul_one]
      _ = (C : ℝ)⁻¹ * (κ' : ℝ) * (C : ℝ) := by ring
      _ = (C : ℝ)⁻¹ * ((κ' : ℝ) * (C : ℝ)) := by rw [← mul_assoc]
      _ = (C : ℝ)⁻¹ * (κ : ℝ) := by rw [h_mul]
  have hsmul (w : EuclideanSpace ℝ (Fin 3)) : gκ' w = t • gκ w := by
    have h := Slab.normalizeScaled_smul S κ κ' hθ0 hκ hκ' w
    simpa [gκ, gκ', t, hsc] using h
  have hQc : Q.center = c := by simp [Q, c]
  have hQb : Q.basis = P.basis := by simp [Q]
  have hxQ : x ∈ (Q.dilation C).carrier := by simpa [Q] using hx
  have hxs (i : Fin 3) : |Q.basis.repr (x -ᵥ Q.center) i| ≤ (C : ℝ) * (Q.thicknesses i : ℝ) := by
    have hb := ((Q.dilation C).mem_carrier_iff x).1 hxQ i
    rw [PrismNDim.dilation_basis, PrismNDim.dilation_center, PrismNDim.dilation_thicknesses] at hb
    exact_mod_cast hb
  -- the shrunk point `xStar = c + t • (x - c)` lies in the undilated thickened plank
  have hxStar : xStar ∈ (P.thickened θ hθ).carrier := by
    change xStar ∈ Q.carrier
    rw [Q.mem_carrier_iff]
    intro i
    have hvec : xStar -ᵥ Q.center = t • (x -ᵥ Q.center) := by
      dsimp [xStar, t]
      rw [hQc]
      rw [add_sub_cancel_left]
    rw [hvec]
    dsimp [t]
    rw [map_smul]
    change |(C : ℝ)⁻¹ * (Q.basis.repr (x -ᵥ Q.center)).ofLp i| ≤ Q.thicknesses i
    rw [abs_mul]
    rw [abs_of_nonneg (le_of_lt (inv_pos.mpr hCpos))]
    calc
      (C : ℝ)⁻¹ * |(Q.basis.repr (x -ᵥ Q.center)).ofLp i|
          ≤ (C : ℝ)⁻¹ * ((C : ℝ) * (Q.thicknesses i : ℝ)) :=
        mul_le_mul_of_nonneg_left (hxs i) (le_of_lt (inv_pos.mpr hCpos))
      _ = Q.thicknesses i := by
        rw [← mul_assoc, hCinv, one_mul]
  -- the image of `xStar` lies in the base tube
  have hStar : gκ xStar ∈ (P.slabTube S κ hθ0 hκ).carrier := hbase ⟨xStar, hxStar, rfl⟩
  -- affine computation: `gκ (c + t • (x - c)) = gκ c + t • (gκ x - gκ c)`
  have hgxstar : gκ xStar = gκ c + t • (gκ x - gκ c) := by
    dsimp [xStar]
    rw [show c + t • (x - c) = c +ᵥ t • (x - c) by simp]
    rw [show c +ᵥ t • (x - c) = t • (x - c) +ᵥ c by
      exact (add_comm c (t • (x - c)))]
    rw [AffineMap.map_vadd (f := gκ) c (t • (x - c))]
    rw [add_comm]
    rw [show gκ.linear (t • (x - c)) = t • gκ.linear (x - c) by
      exact map_smul gκ.linear t (x - c)]
    rw [show gκ.linear (x - c) = gκ x - gκ c by
      simpa using (AffineMap.linearMap_vsub (f := gκ) x c)]
    rfl
  have hmain : gκ' x = gκ xStar + (gκ' c - gκ c) := by
    rw [hsmul x, hsmul c]
    rw [hgxstar]
    module
  -- the tube translates by `v = gκ' P.center - gκ P.center`
  rw [Plank.slabTube_scale_eq_vadd P S κ κ' hθ0 hκ hκ']
  rw [Tube.vadd_carrier]
  refine ⟨gκ xStar, hStar, ?_⟩
  change (gκ' c - gκ c) + gκ xStar = gκ' x
  rw [add_comm]
  rw [← hmain]

/-! ## The Katz–Tao normalisation constants

GWZ Lemma 6.13 hands back a shading whose carrier is a fixed dilation `Q.dilation Cfib` of the
representative prism, and the representative itself only sits inside a fixed dilation of the anchor
plank's thickening.  Both losses are absorbed by *shrinking the normalisation constant*: for
`κ = Plank.slabTubeConst Cset Cang = 1 / (16 (1 + Cang) (1 + Cset))`, dividing `κ` by `Cdil` is the
same as replacing `Cset` by `Plank.dilatedSetConst Cset Cdil`, so the whole tube interface of
`PlankToTube.lean` applies verbatim at the enlarged set constant. -/

/-- The set constant for which `Plank.slabTubeConst` shrinks by exactly `Cdil`. -/
def dilatedSetConst (Cset Cdil : ℝ≥0) : ℝ≥0 := Cdil * (1 + Cset) - 1

theorem one_add_dilatedSetConst {Cset Cdil : ℝ≥0} (hCdil : 1 ≤ Cdil) :
    1 + dilatedSetConst Cset Cdil = Cdil * (1 + Cset) := by
  rw [dilatedSetConst]
  have h1 : (1 : ℝ≥0) ≤ 1 + Cset := le_self_add
  have hx : (1 : ℝ≥0) ≤ Cdil * (1 + Cset) := one_le_mul hCdil h1
  rw [add_comm, tsub_add_cancel_of_le hx]

theorem le_dilatedSetConst {Cset Cdil : ℝ≥0} (hCdil : 1 ≤ Cdil) :
    Cset ≤ dilatedSetConst Cset Cdil := by
  rw [dilatedSetConst]
  rw [le_tsub_iff_right (le_trans le_self_add (le_mul_of_one_le_left' hCdil))]
  rw [add_comm]
  exact le_mul_of_one_le_left' hCdil

/-- Dividing the tube constant by `Cdil` is enlarging its set constant. -/
theorem slabTubeConst_dilatedSetConst_mul {Cset Cang Cdil : ℝ≥0} (hCdil : 1 ≤ Cdil) :
    slabTubeConst (dilatedSetConst Cset Cdil) Cang * Cdil = slabTubeConst Cset Cang := by
  simp only [slabTubeConst]
  rw [one_add_dilatedSetConst hCdil]
  rw [← NNReal.coe_inj]
  push_cast
  have h1 : (0 : ℝ) < 1 + (Cang : ℝ) := by positivity
  have h2 : (0 : ℝ) < 1 + (Cset : ℝ) := by positivity
  have hCdil0 : (0 : ℝ≥0) < Cdil := lt_of_lt_of_le (by norm_num : (0 : ℝ≥0) < 1) hCdil
  have h3 : (0 : ℝ) < (Cdil : ℝ) := by exact_mod_cast hCdil0
  field_simp [h1.ne', h2.ne', h3.ne']

/-- **A body inside a `Cdil`-dilated thickened plank normalises into the plank's tube**, at the
tube constant of the enlarged set constant.  This is the containment the Katz–Tao tube family needs
for Lemma 6.13's dilated shadings. -/
theorem image_subset_slabTube_of_subset_dilatedThickened (P : Plank a b hab hb1) (S : Slab θ hθ)
    (hθ0 : 0 < θ) {Cset Cang Cdil : ℝ≥0} (hCdil : 1 ≤ Cdil)
    (hang : Prism3D.angle P S ≤ (Cang : ℝ) * (θ : ℝ))
    {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hA : A ⊆ ((P.thickened θ hθ).toPrismNDim.dilation Cdil).carrier) :
    (Slab.normalizeScaled S (slabTubeConst (dilatedSetConst Cset Cdil) Cang) hθ0
        (slabTubeConst_pos _ _)) '' A
      ⊆ (P.slabTube S (slabTubeConst (dilatedSetConst Cset Cdil) Cang) hθ0
        (slabTubeConst_pos _ _)).carrier := by
  have hC0 : 0 < Cdil := lt_of_lt_of_le zero_lt_one hCdil
  exact (Set.image_mono hA).trans
    (image_dilation_carrier_subset_slabTube P S hθ0
      (κ := slabTubeConst Cset Cang)
      (κ' := slabTubeConst (dilatedSetConst Cset Cdil) Cang)
      (C := Cdil)
      (slabTubeConst_pos Cset Cang)
      (slabTubeConst_pos (dilatedSetConst Cset Cdil) Cang)
      hC0
      (slabTubeConst_dilatedSetConst_mul (Cset := Cset) (Cang := Cang) hCdil)
      (Plank.image_carrier_subset_slabTube P S hθ0 hang))

/-! ## The Katz–Tao tube family

The family-level interface consumed by GWZ Lemma 6.1: `Plank.slabTubeFamily` at the tube constant
of the enlarged set constant, for shadings whose carriers are fixed dilations of the thickened
planks.  Nothing here needs pairwise essential distinctness, because
`Kakeya.KatzTaoEstimate.multiplicity_bound_generalize` does not assume it. -/

section KTFamily

variable {ι : Type*} {Cset Cang Cdil : ℝ≥0} {s : Finset ι} {V : ι → Plank a b hab hb1}
  {Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))} {S : Slab θ hθ}

/-- The controlled slab subfamily is monotone in its set constant. -/
theorem inSlabFamilyC_mono_set {C C' Cang : ℝ≥0} (hCC' : C ≤ C') {i : ι}
    (hi : i ∈ inSlabFamilyC C Cang s V S) : i ∈ inSlabFamilyC C' Cang s V S := by
  rw [mem_inSlabFamilyC] at hi ⊢
  exact ⟨hi.1, hi.2.1.trans (PrismNDim.dilation_carrier_mono _ hCC'), hi.2.2⟩

/-- **(1) The Katz–Tao tubes lie in the unit ball.** -/
theorem ktTubeFamily_carrier_subset_closedBall (hθ0 : 0 < θ) (hCdil : 1 ≤ Cdil)
    (hmem : ∀ i ∈ s, i ∈ inSlabFamilyC Cset Cang s V S) (i : ι) :
    (slabTubeFamily s V Y S (slabTubeConst (dilatedSetConst Cset Cdil) Cang) hθ0
        (slabTubeConst_pos _ _) i).carrier
      ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  refine slabTubeFamily_carrier_subset_closedBall (Cset := dilatedSetConst Cset Cdil)
    (Cang := Cang) hθ0 (fun j hj => ?_) i
  exact inSlabFamilyC_mono_set (le_dilatedSetConst hCdil) (hmem j hj)

/-- **(2) The Katz–Tao tubes carry exactly the transported shadings.**  The intersection in
`Plank.slabShadedTube` is inert because the *whole* dilated shading body normalises into the
tube. -/
theorem ktTubeFamily_shade (hθ0 : 0 < θ) (hCdil : 1 ≤ Cdil)
    (hmem : ∀ i ∈ s, i ∈ inSlabFamilyC Cset Cang s V S)
    (hcar : ∀ i ∈ s, ((Y i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ (((V i).thickened θ hθ).toPrismNDim.dilation Cdil).carrier)
    {i : ι} (hi : i ∈ s) :
    (slabTubeFamily s V Y S (slabTubeConst (dilatedSetConst Cset Cdil) Cang) hθ0
        (slabTubeConst_pos _ _) i).shade
      = (Slab.normalizeScaled S (slabTubeConst (dilatedSetConst Cset Cdil) Cang) hθ0
          (slabTubeConst_pos _ _)) '' (Y i).shade := by
  have hang : Prism3D.angle (V i) S ≤ (Cang : ℝ) * (θ : ℝ) :=
    (mem_inSlabFamilyC.mp (hmem i hi)).2.2
  have hshade : (Y i).shade ⊆
      (((V i).thickened θ hθ).toPrismNDim.dilation Cdil).carrier := by
    exact (Y i).shade_subset.trans (hcar i hi)
  have hsub : (Slab.normalizeScaled S (slabTubeConst (dilatedSetConst Cset Cdil) Cang) hθ0
        (slabTubeConst_pos _ _)) '' (Y i).shade
      ⊆ ((V i).slabTube S (slabTubeConst (dilatedSetConst Cset Cdil) Cang) hθ0
          (slabTubeConst_pos _ _)).carrier :=
    (Set.image_mono hshade).trans
      (image_subset_slabTube_of_subset_dilatedThickened (P := V i) (S := S) (hθ0 := hθ0)
        (hCdil := hCdil) (hang := hang) (hA := Set.Subset.rfl))
  simp only [slabTubeFamily, slabShadedTube, if_pos hi]
  exact Set.inter_eq_self_of_subset_left hsub

/-- **(3) The multiplicity is preserved exactly.** -/
theorem multiplicity_ktTubeFamily (hθ0 : 0 < θ) (hCdil : 1 ≤ Cdil)
    (hmem : ∀ i ∈ s, i ∈ inSlabFamilyC Cset Cang s V S)
    (hcar : ∀ i ∈ s, ((Y i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ (((V i).thickened θ hθ).toPrismNDim.dilation Cdil).carrier) :
    ShadedBody.multiplicity s (fun i =>
        (slabTubeFamily s V Y S (slabTubeConst (dilatedSetConst Cset Cdil) Cang) hθ0
          (slabTubeConst_pos _ _) i).toShadedBody)
      = ShadedBody.multiplicity s Y := by
  let g : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin 3) :=
    Slab.normalizeScaled S (slabTubeConst (dilatedSetConst Cset Cdil) Cang) hθ0
      (slabTubeConst_pos _ _)
  have h : ∀ i ∈ s,
      ((slabTubeFamily s V Y S (slabTubeConst (dilatedSetConst Cset Cdil) Cang) hθ0
        (slabTubeConst_pos _ _) i).toShadedBody).shade
        = ((Y i).mapAffine g).shade := by
    intro i hi
    change (slabTubeFamily s V Y S (slabTubeConst (dilatedSetConst Cset Cdil) Cang) hθ0
        (slabTubeConst_pos _ _) i).shade = ((Y i).mapAffine g).shade
    rw [ktTubeFamily_shade hθ0 hCdil hmem hcar hi, ShadedBody.mapAffine_shade]
  rw [ShadedBody.multiplicity_congr s _ (fun i => (Y i).mapAffine g) h]
  exact ShadedBody.multiplicity_mapAffine s Y g

/-- **(4) The tube carrier is comparable to the normalised shading body.**  The `Cdil³` growth of
the dilated body cancels the `Cdil³` growth of `(1 + dilatedSetConst Cset Cdil)³`, so the comparison
constant is the undilated `40 (1 + Cang)³ (1 + Cset)³`. -/
theorem volume_ktTube_le (P : Plank a b hab hb1) (hθ0 : 0 < θ) (hCdil : 1 ≤ Cdil)
    {A : Set (EuclideanSpace ℝ (Fin 3))}
    (hA : A = (((P.thickened θ hθ).toPrismNDim.dilation Cdil).carrier :
      Set (EuclideanSpace ℝ (Fin 3)))) :
    volume (P.slabTube S (slabTubeConst (dilatedSetConst Cset Cdil) Cang) hθ0
        (slabTubeConst_pos _ _)).carrier
      ≤ (40 * (1 + (Cang : ENNReal)) ^ 3 * (1 + (Cset : ENNReal)) ^ 3) *
          volume ((Slab.normalizeScaled S (slabTubeConst (dilatedSetConst Cset Cdil) Cang) hθ0
            (slabTubeConst_pos _ _)) '' A) := by
  let Cset' : ℝ≥0 := dilatedSetConst Cset Cdil
  let κ' : ℝ≥0 := slabTubeConst Cset' Cang
  let g : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin 3) :=
    Slab.normalizeScaled S κ' hθ0 (slabTubeConst_pos Cset' Cang)
  let a_ang : ENNReal := 40 * (1 + (Cang : ENNReal)) ^ 3
  let b_set : ENNReal := (1 + (Cset : ENNReal)) ^ 3
  let c_dil : ENNReal := (Cdil : ENNReal) ^ 3
  let v0 : ENNReal := volume (g '' (P.thickened θ hθ).carrier)
  have hκ' : 0 < κ' := by
    dsimp [κ', Cset']
    exact slabTubeConst_pos Cset' Cang
  change volume (P.slabTube S κ' hθ0 hκ').carrier ≤ (a_ang * b_set) * volume (g '' A)
  have h1 : (1 + Cset' : ℝ≥0) = Cdil * (1 + Cset) := by
    dsimp [Cset']
    exact one_add_dilatedSetConst hCdil
  have h1e' : ((1 + Cset' : ℝ≥0) : ENNReal) = 1 + (Cset' : ENNReal) := by
    simp [ENNReal.coe_one, ENNReal.coe_add]
  have h1e : ((1 + Cset : ℝ≥0) : ENNReal) = 1 + (Cset : ENNReal) := by
    simp [ENNReal.coe_one, ENNReal.coe_add]
  have h1' : (1 + (Cset' : ENNReal)) ^ 3 = c_dil * b_set := by
    dsimp [c_dil, b_set]
    rw [← h1e']
    rw [h1]
    rw [ENNReal.coe_mul]
    rw [mul_pow]
    rw [h1e]
  have hvol : volume (g '' A) = c_dil * v0 := by
    dsimp [c_dil, v0]
    rw [hA]
    rw [Kakeya.volume_image_affineEquiv, Kakeya.volume_image_affineEquiv]
    rw [PrismNDim.volume_dilation]
    ring
  calc
    volume (P.slabTube S κ' hθ0 hκ').carrier
        ≤ (40 * (1 + (Cang : ENNReal)) ^ 3 * (1 + (Cset' : ENNReal)) ^ 3) *
            volume (g '' (P.thickened θ hθ).carrier) := by
        simpa [κ', Cset', g, hκ', v0] using
          (Plank.volume_slabTube_le (P := P) (S := S) (Cset := Cset') (Cang := Cang) hθ0)
    _ = (a_ang * (c_dil * b_set)) * v0 := by
        dsimp [a_ang, c_dil, b_set]
        rw [h1'.symm]
    _ = (a_ang * b_set) * (c_dil * v0) := by
        ring
    _ = (a_ang * b_set) * volume (g '' A) := by
        rw [hvol]

/-- **(5) Fullness is preserved up to the absolute factor `40 (1 + Cang)³ (1 + Cset)³`.**  The
shadings transport exactly (Jacobian `J`), while the tube carriers exceed the normalised shading
bodies by at most that factor, so the quotient loses only it. -/
theorem fullness'_le_ktTubeFamily (hθ0 : 0 < θ) (hb0 : 0 < b) (hCdil : 1 ≤ Cdil)
    (hmem : ∀ i ∈ s, i ∈ inSlabFamilyC Cset Cang s V S)
    (hcarEq : ∀ i ∈ s, ((Y i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      = (((V i).thickened θ hθ).toPrismNDim.dilation Cdil).carrier) :
    ShadedBody.fullness' s Y
      ≤ (40 * (1 + (Cang : ENNReal)) ^ 3 * (1 + (Cset : ENNReal)) ^ 3) *
          ShadedBody.fullness' s (fun i =>
            (slabTubeFamily s V Y S (slabTubeConst (dilatedSetConst Cset Cdil) Cang) hθ0
              (slabTubeConst_pos _ _) i).toShadedBody) := by
  let κ : ℝ≥0 := slabTubeConst (dilatedSetConst Cset Cdil) Cang
  let hκ : 0 < κ := slabTubeConst_pos _ _
  let g : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin 3) :=
    Slab.normalizeScaled S κ hθ0 hκ
  let C : ENNReal := 40 * (1 + (Cang : ENNReal)) ^ 3 * (1 + (Cset : ENNReal)) ^ 3
  let J : ENNReal := Kakeya.affineJacobian g
  let T : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)) := fun i =>
    (slabTubeFamily s V Y S κ hθ0 hκ i).toShadedBody
  change ShadedBody.fullness' s Y ≤ C * ShadedBody.fullness' s T
  dsimp [ShadedBody.fullness']
  set N : ENNReal := ∑ i ∈ s, volume (Y i).shade
  set D : ENNReal := ∑ i ∈ s, volume (Y i).carrier
  set N_T : ENNReal := ∑ i ∈ s, volume (T i).shade
  set D_T : ENNReal := ∑ i ∈ s, volume (T i).carrier
  have hshade (i : ι) (hi : i ∈ s) : volume (T i).shade = J * volume (Y i).shade := by
    calc
      volume (T i).shade = volume (g '' (Y i).shade) := by
        congr 1
        dsimp [T, g]
        simpa using (ktTubeFamily_shade hθ0 hCdil hmem (fun j hj => (hcarEq j hj).le) hi)
      _ = J * volume (Y i).shade := by
        rw [Kakeya.volume_image_affineEquiv]
  have hNT : N_T = J * N := by
    dsimp [N_T, N]
    calc
      ∑ i ∈ s, volume (T i).shade = ∑ i ∈ s, J * volume (Y i).shade := by
        exact Finset.sum_congr rfl fun i hi => hshade i hi
      _ = J * ∑ i ∈ s, volume (Y i).shade := by
        rw [← Finset.mul_sum]
  have hcarrier (i : ι) (hi : i ∈ s) :
      volume (T i).carrier ≤ (C * J) * volume (Y i).carrier := by
    calc
      volume (T i).carrier = volume ((V i).slabTube S κ hθ0 hκ).carrier := by
        dsimp [T]
        simp [slabTubeFamily, slabShadedTube, hi]
      _ ≤ C * volume (g '' (Y i).carrier) := by
        simpa [κ, hκ, C, g] using
          (volume_ktTube_le (V i) hθ0 hCdil (A := (Y i).carrier) (hA := hcarEq i hi))
      _ = C * (J * volume (Y i).carrier) := by
        rw [Kakeya.volume_image_affineEquiv]
      _ = (C * J) * volume (Y i).carrier := by
        rw [← mul_assoc]
  have hDT : D_T ≤ (C * J) * D := by
    dsimp [D_T, D]
    calc
      ∑ i ∈ s, volume (T i).carrier ≤ ∑ i ∈ s, (C * J) * volume (Y i).carrier := by
        exact Finset.sum_le_sum fun i hi => hcarrier i hi
      _ = (C * J) * ∑ i ∈ s, volume (Y i).carrier := by
        rw [← Finset.mul_sum]
  have hJ0 : J ≠ 0 := by
    dsimp [J]
    exact Kakeya.affineJacobian_ne_zero g
  have hJtop : J ≠ ⊤ := by
    dsimp [J]
    exact Kakeya.affineJacobian_ne_top g
  have hone (x : ENNReal) : (1 : ENNReal) + x ≠ 0 := by
    have hle : (1 : ENNReal) ≤ (1 : ENNReal) + x := le_add_of_nonneg_right bot_le
    exact ne_of_gt (zero_lt_one.trans_le hle)
  have hC0 : C ≠ 0 := by
    dsimp [C]
    exact mul_ne_zero (mul_ne_zero (by norm_num : (40 : ENNReal) ≠ 0)
      (ENNReal.pow_ne_zero (hone (Cang : ENNReal)) 3))
      (ENNReal.pow_ne_zero (hone (Cset : ENNReal)) 3)
  have htopone (r : ℝ≥0) : (1 : ENNReal) + (r : ENNReal) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.coe_ne_top, ENNReal.coe_ne_top⟩
  have hCtop : C ≠ ⊤ := by
    dsimp [C]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num : (40 : ENNReal) ≠ ⊤)
        (ENNReal.pow_ne_top (htopone Cang)))
      (ENNReal.pow_ne_top (htopone Cset))
  have hCJ0 : C * J ≠ 0 := mul_ne_zero hC0 hJ0
  have hCJtop : C * J ≠ ⊤ := ENNReal.mul_ne_top hCtop hJtop
  calc
    N / D = (C * J) * N / ((C * J) * D) := by
      exact (ENNReal.mul_div_mul_left (a := N) (b := D) (c := C * J) hCJ0 hCJtop).symm
    _ ≤ (C * J) * N / D_T := ENNReal.div_le_div_left hDT ((C * J) * N)
    _ = C * (N_T / D_T) := by
      calc
        (C * J) * N / D_T = (C * (J * N)) / D_T := by rw [mul_assoc]
        _ = C * (J * N / D_T) := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          ac_rfl
        _ = C * (N_T / D_T) := by rw [← hNT]

/-- **(6) The maximal density of the tubes is controlled by that of the normalised shading
bodies.**  Each normalised body sits inside its tube and the tube has at most
`40 (1 + Cang)³ (1 + Cset)³` times its volume, so `Kakeya.maxDensity_le_of_subset_of_volume_le`
applies. -/
theorem maxDensity_ktTubeFamily_le (hθ0 : 0 < θ) (hCdil : 1 ≤ Cdil)
    (hmem : ∀ i ∈ s, i ∈ inSlabFamilyC Cset Cang s V S)
    (hcarEq : ∀ i ∈ s, ((Y i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      = (((V i).thickened θ hθ).toPrismNDim.dilation Cdil).carrier) :
    Kakeya.maxDensity s (fun i =>
        (slabTubeFamily s V Y S (slabTubeConst (dilatedSetConst Cset Cdil) Cang) hθ0
          (slabTubeConst_pos _ _) i).toConvexSpaceBody)
      ≤ (40 * (1 + (Cang : ENNReal)) ^ 3 * (1 + (Cset : ENNReal)) ^ 3) *
          Kakeya.maxDensity s (fun i => ((Y i).toConvexSpaceBody).mapAffine
            (Slab.normalizeScaled S (slabTubeConst (dilatedSetConst Cset Cdil) Cang) hθ0
              (slabTubeConst_pos _ _))) := by
  let g : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin 3) :=
    Slab.normalizeScaled S (slabTubeConst (dilatedSetConst Cset Cdil) Cang) hθ0
      (slabTubeConst_pos _ _)
  let C : ENNReal := 40 * (1 + (Cang : ENNReal)) ^ 3 * (1 + (Cset : ENNReal)) ^ 3
  let W : ι → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) :=
    fun i => ((Y i).toConvexSpaceBody).mapAffine g
  let W' : ι → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) :=
    fun i => (slabTubeFamily s V Y S (slabTubeConst (dilatedSetConst Cset Cdil) Cang) hθ0
      (slabTubeConst_pos _ _) i).toConvexSpaceBody
  have hsub : ∀ i ∈ s, (W i).carrier ⊆ (W' i).carrier := by
    intro i hi
    simp only [W, W']
    change (((Y i).toConvexSpaceBody).mapAffine g).carrier ⊆
      (slabTubeFamily s V Y S (slabTubeConst (dilatedSetConst Cset Cdil) Cang) hθ0
        (slabTubeConst_pos _ _) i).toConvexSpaceBody.carrier
    rw [ConvexSpaceBody.mapAffine_carrier]
    simp only [slabTubeFamily, slabShadedTube, if_pos hi]
    simpa [g] using
      (Plank.image_subset_slabTube_of_subset_dilatedThickened (P := V i) (S := S) (hθ0 := hθ0)
        (hCdil := hCdil)
        (hang := (mem_inSlabFamilyC.mp (hmem i hi)).2.2)
        (A := (Y i).carrier) (hA := (hcarEq i hi).le))
  have hvol : ∀ i ∈ s, volume (W' i).carrier ≤ C * volume (W i).carrier := by
    intro i hi
    simp only [W, W']
    change volume ((slabTubeFamily s V Y S (slabTubeConst (dilatedSetConst Cset Cdil) Cang) hθ0
        (slabTubeConst_pos _ _) i).toConvexSpaceBody).carrier
      ≤ C * volume ((((Y i).toConvexSpaceBody).mapAffine g).carrier)
    rw [ConvexSpaceBody.mapAffine_carrier]
    simp only [slabTubeFamily, slabShadedTube, if_pos hi]
    simpa [C, g] using
      (Plank.volume_ktTube_le (P := V i) (hθ0 := hθ0) (hCdil := hCdil)
        (A := (Y i).carrier) (hA := hcarEq i hi))
  classical
  refine Kakeya.maxDensity_le_of_forall_sum_le ?_
  intro K
  calc
    ∑ i ∈ s with W' i ≤ K, volume (W' i).carrier
        ≤ ∑ i ∈ s with W' i ≤ K, C * volume (W i).carrier := by
          exact Finset.sum_le_sum fun i hi => hvol i ((Finset.mem_filter.mp hi).1)
    _ = C * ∑ i ∈ s with W' i ≤ K, volume (W i).carrier := by
          rw [Finset.mul_sum]
    _ ≤ C * ∑ i ∈ s with W i ≤ K, volume (W i).carrier := by
          gcongr
          exact SetLike.coe_subset_coe.mpr (hsub i (by assumption))
    _ ≤ C * (Kakeya.maxDensity s W * volume K.carrier) := by
          gcongr
          exact Kakeya.sum_volume_le_maxDensity_mul_volume s W K
    _ = (C * Kakeya.maxDensity s W) * volume K.carrier := by
          ring

/-! ### Volume inputs for a shading that is a dilated *representative*

GWZ Lemma 6.13's shading `Yθ Q` has carrier `Q.dilation Cbox` for the representative prism `Q`,
which is only *contained* in a dilation of the anchor plank's thickening.  The fullness and maximal
density comparisons therefore run through the explicit volumes: both the tube and the normalised
dilated representative have volume comparable to `b²`. -/

/-- The normalised `Cbox`-dilation of a thickened representative has volume `8 κ³ Cbox³ b²`. -/
theorem volume_image_normalizeScaled_dilation_thickenedPlank (S : Slab θ hθ)
    (Q : ThickenedPlank θ b hθ hb1) (κ Cbox : ℝ≥0) (hθ0 : 0 < θ) (hκ : 0 < κ) :
    volume ((Slab.normalizeScaled S κ hθ0 hκ) ''
        ((Q.toPrismNDim.dilation Cbox).carrier : Set (EuclideanSpace ℝ (Fin 3))))
      = 8 * (κ : ENNReal) ^ 3 * (Cbox : ENNReal) ^ 3 * (b : ENNReal) ^ 2 := by
  rw [Kakeya.volume_image_affineEquiv]
  rw [Slab.affineJacobian_normalizeScaled]
  rw [PrismNDim.volume_dilation]
  have hQvol : volume (Q.carrier : Set (EuclideanSpace ℝ (Fin 3)))
      = 8 * (θ : ENNReal) * (b : ENNReal) * (b : ENNReal) := by
    rw [Prism3D.volume_carrier Q]
    push_cast
    ring
  rw [hQvol]
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
  let p : ENNReal := (κ : ENNReal) ^ 3 * (Cbox : ENNReal) ^ 3
  calc
    (κ : ENNReal) ^ 3 * (θ : ENNReal)⁻¹ * ((Cbox : ENNReal) ^ 3 * (8 * (θ : ENNReal) * b * b))
        = p * 8 * ((θ : ENNReal)⁻¹ * (θ : ENNReal)) * b * b := by
          dsimp [p]
          ring
    _ = p * 8 * 1 * b * b := by rw [hcancel]
    _ = 8 * (κ : ENNReal) ^ 3 * (Cbox : ENNReal) ^ 3 * (b : ENNReal) ^ 2 := by
          dsimp [p]
          ring

/-- A `b/8`-tube has volume at most `(5/64) b²` (from `Tube.volume_carrier_le` and `b ≤ 1`). -/
theorem volume_slabTube_le_sq (P : Plank a b hab hb1) (S : Slab θ hθ) (κ : ℝ≥0) (hθ0 : 0 < θ)
    (hκ : 0 < κ) :
    volume (P.slabTube S κ hθ0 hκ).carrier ≤ (5 / 64 : ENNReal) * (b : ENNReal) ^ 2 := by
  refine (Tube.volume_carrier_le (T := P.slabTube S κ hθ0 hκ)).trans ?_
  have hnn : (8 : ℝ≥0) * (b / 8 : ℝ≥0) ^ 2 * ((1 / 2 : ℝ≥0) + b / 8)
      ≤ (5 / 64 : ℝ≥0) * (b : ℝ≥0) ^ 2 := by
    rw [← NNReal.coe_le_coe]
    push_cast
    have hb0 : (0 : ℝ) ≤ (b : ℝ) := NNReal.coe_nonneg b
    have hb1' : (b : ℝ) ≤ 1 := by exact_mod_cast hb1
    nlinarith [hb0, hb1']
  simpa [ENNReal.coe_mul, ENNReal.coe_add, ENNReal.coe_div, ENNReal.coe_pow] using
    (ENNReal.coe_le_coe.mpr hnn)

end KTFamily

end Plank

namespace ShadedBody

variable {ι : Type*}

/-- **Fullness under an affine transport with a controlled carrier enlargement.**  If the shadings
of `T` are exactly the `g`-images of the shadings of `Y`, and each carrier of `T` is at most `C`
times the volume of the `g`-image of the corresponding carrier of `Y`, then `λ(Y) ≤ C · λ(T)`: the
numerators agree up to the Jacobian, which cancels against the denominators. -/
theorem fullness'_le_of_shade_image_of_volume_le (s : Finset ι)
    (Y T : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (g : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)) {C : ENNReal}
    (hC0 : C ≠ 0) (hCtop : C ≠ ⊤)
    (hshade : ∀ i ∈ s, (T i).shade = g '' (Y i).shade)
    (hvol : ∀ i ∈ s, volume (T i).carrier ≤ C * volume (g '' (Y i).carrier)) :
    ShadedBody.fullness' s Y ≤ C * ShadedBody.fullness' s T := by
  let J : ENNReal := Kakeya.affineJacobian g
  dsimp [ShadedBody.fullness']
  set N : ENNReal := ∑ i ∈ s, volume (Y i).shade
  set D : ENNReal := ∑ i ∈ s, volume (Y i).carrier
  set N_T : ENNReal := ∑ i ∈ s, volume (T i).shade
  set D_T : ENNReal := ∑ i ∈ s, volume (T i).carrier
  have hshade (i : ι) (hi : i ∈ s) : volume (T i).shade = J * volume (Y i).shade := by
    calc
      volume (T i).shade = volume (g '' (Y i).shade) := by
        congr 1
        exact hshade i hi
      _ = J * volume (Y i).shade := by
        rw [Kakeya.volume_image_affineEquiv]
  have hNT : N_T = J * N := by
    dsimp [N_T, N]
    calc
      ∑ i ∈ s, volume (T i).shade = ∑ i ∈ s, J * volume (Y i).shade := by
        exact Finset.sum_congr rfl fun i hi => hshade i hi
      _ = J * ∑ i ∈ s, volume (Y i).shade := by
        rw [← Finset.mul_sum]
  have hcarrier (i : ι) (hi : i ∈ s) :
      volume (T i).carrier ≤ (C * J) * volume (Y i).carrier := by
    calc
      volume (T i).carrier ≤ C * volume (g '' (Y i).carrier) := hvol i hi
      _ = C * (J * volume (Y i).carrier) := by
        rw [Kakeya.volume_image_affineEquiv]
      _ = (C * J) * volume (Y i).carrier := by
        rw [← mul_assoc]
  have hDT : D_T ≤ (C * J) * D := by
    dsimp [D_T, D]
    calc
      ∑ i ∈ s, volume (T i).carrier ≤ ∑ i ∈ s, (C * J) * volume (Y i).carrier := by
        exact Finset.sum_le_sum fun i hi => hcarrier i hi
      _ = (C * J) * ∑ i ∈ s, volume (Y i).carrier := by
        rw [← Finset.mul_sum]
  have hJ0 : J ≠ 0 := by
    dsimp [J]
    exact Kakeya.affineJacobian_ne_zero g
  have hJtop : J ≠ ⊤ := by
    dsimp [J]
    exact Kakeya.affineJacobian_ne_top g
  have hCJ0 : C * J ≠ 0 := mul_ne_zero hC0 hJ0
  have hCJtop : C * J ≠ ⊤ := ENNReal.mul_ne_top hCtop hJtop
  calc
    N / D = (C * J) * N / ((C * J) * D) := by
      exact (ENNReal.mul_div_mul_left (a := N) (b := D) (c := C * J) hCJ0 hCJtop).symm
    _ ≤ (C * J) * N / D_T := ENNReal.div_le_div_left hDT ((C * J) * N)
    _ = C * (N_T / D_T) := by
      calc
        (C * J) * N / D_T = (C * (J * N)) / D_T := by rw [mul_assoc]
        _ = C * (J * N / D_T) := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          ac_rfl
        _ = C * (N_T / D_T) := by rw [← hNT]

end ShadedBody

namespace Kakeya

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*}

/-- **Maximal density under a controlled enlargement.**  If each body of `W'` contains the
corresponding body of `W` and has at most `C` times its volume, then `Δ_max(W') ≤ C · Δ_max(W)`: a
test body containing `W' i` also contains `W i`, so the enlarged family's sums are dominated
termwise by `C` times sums of the original family over a larger index set. -/
theorem maxDensity_le_of_subset_of_volume_le (s : Finset ι) (W W' : ι → ConvexSpaceBody E)
    {C : ENNReal} (hsub : ∀ i ∈ s, (W i).carrier ⊆ (W' i).carrier)
    (hvol : ∀ i ∈ s, volume (W' i).carrier ≤ C * volume (W i).carrier) :
    maxDensity s W' ≤ C * maxDensity s W := by
  classical
  refine maxDensity_le_of_forall_sum_le ?_
  intro K
  calc
    ∑ i ∈ s with W' i ≤ K, volume (W' i).carrier
        ≤ ∑ i ∈ s with W' i ≤ K, C * volume (W i).carrier := by
          exact Finset.sum_le_sum fun i hi => hvol i ((Finset.mem_filter.mp hi).1)
    _ = C * ∑ i ∈ s with W' i ≤ K, volume (W i).carrier := by
          rw [Finset.mul_sum]
    _ ≤ C * ∑ i ∈ s with W i ≤ K, volume (W i).carrier := by
          gcongr
          exact SetLike.coe_subset_coe.mpr (hsub i (by assumption))
    _ ≤ C * (maxDensity s W * volume K.carrier) := by
          gcongr
          exact sum_volume_le_maxDensity_mul_volume s W K
    _ = (C * maxDensity s W) * volume K.carrier := by
          rw [mul_assoc]

end Kakeya

namespace PrismNDim

variable {n : ℕ} {E S : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [PseudoMetricSpace S] [NormedAddTorsor E S]

/-- **Composing containment with dilation.**  If `Q` sits inside the `c`-dilation of `P`, then the
`C`-dilation of `Q` sits inside the `(2C + 1) c`-dilation of `P`: a point of `Q.dilation C` is
`q + C • (y - q)` for `q` the centre and `y ∈ Q`, and all three of `q`, `y` have `P`-coordinates
bounded by `c` times `P`'s half-widths. -/
theorem dilation_carrier_subset_dilation_of_carrier_subset {P Q : PrismNDim n E S} {c C : ℝ≥0}
    (hC : 0 < C) (h : (Q.carrier : Set S) ⊆ (P.dilation c).carrier) :
    ((Q.dilation C).carrier : Set S) ⊆ (P.dilation ((2 * C + 1) * c)).carrier := by
  calc
    ((Q.dilation C).carrier : Set S) ⊆ ((P.dilation c).dilation (1 + 2 * C)).carrier :=
      dilation_carrier_subset_dilation_of_subset (K := P.dilation c) h C
    _ ⊆ (P.dilation ((2 * C + 1) * c)).carrier := by
      rw [dilation_dilation]
      rw [show (1 + 2 * C) * c = (2 * C + 1) * c by ring]

end PrismNDim

end

end
