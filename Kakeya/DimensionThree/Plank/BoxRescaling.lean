/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionN.Prism
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic

/-!
# Lean-facing geometric API for GWZ Lemma 6.13 — affine rescaling
The box-rescaling layer of the plank geometry.

The companion file `Kakeya.DimensionThree.Plank.SlabIntersection` holds the outer slab model and
slab-angle half. This file contains the homothety image lemma for prisms
(`homothety_image_prism_carrier_of_center`) together with the measurability and volume-scaling of
homothety images (`measurableSet_homothety_image`, `volume_iUnion_homothety_image`,
`volume_inter_homothety_image`), which is what the dense-box slab construction consumes.
-/

@[expose] public section

open MeasureTheory Convexity
open scoped NNReal Real

noncomputable section

namespace Plank

variable {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {ι : Type*}

/-- **General-centre homothety image of a prism** (helper for the dense-box slab construction):
a homothety by ratio `r > 0` about an *arbitrary* centre `c` maps a prism's carrier onto the prism
with the same axes, thicknesses scaled by `r`, and centre the image `homothety c r P.center` of the
old centre. This generalises `homothety_image_prism_carrier` (the case `c = P.center`) so that the
box-normalising map `boxRescaleAffine` (a homothety about `Q.center`) can be applied to an outer
slab model `plankSlabModel P x₀` centred at a point `x₀ ≠ Q.center`. -/
theorem homothety_image_prism_carrier_of_center
    (P : PrismNDim 3 (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3)))
    (c : EuclideanSpace ℝ (Fin 3)) (r : ℝ) (hr : 0 < r) :
    (AffineMap.homothety c r) '' (P.carrier : Set (EuclideanSpace ℝ (Fin 3)))
      = (PrismNDim.mk' ((AffineMap.homothety c r) P.center) P.basis
          (fun i => Real.toNNReal r * P.thicknesses i)).carrier := by
  set center' := AffineMap.homothety c r P.center
  set Q := PrismNDim.mk' center' P.basis (fun i => Real.toNNReal r * P.thicknesses i)
  have hQcenter : Q.center = center' := rfl
  have hQbasis : Q.basis = P.basis := rfl
  have hQthick (i : Fin 3) : (Q.thicknesses i : ℝ) = r * (P.thicknesses i : ℝ) := by
    simp [Q, PrismNDim.thicknesses_mk', Real.coe_toNNReal r (show 0 ≤ r from hr.le)]
  set h := AffineMap.homothety c r
  ext y
  constructor
  · rintro ⟨x, hx, hxy⟩
    rw [P.mem_carrier_iff] at hx
    rw [Q.mem_carrier_iff]
    have hxy_vsub : r • (x -ᵥ P.center) = y -ᵥ center' := by
      calc
        r • (x -ᵥ P.center) = h x - h P.center := by
          simp [h, AffineMap.homothety_apply, smul_sub]
        _ = y - (AffineMap.homothety c r P.center) := by rw [hxy]
        _ = y -ᵥ center' := by
          simp [center', vsub_eq_sub]
    intro i
    calc
      |P.basis.repr (y -ᵥ center') i| = |P.basis.repr (r • (x -ᵥ P.center)) i| := by rw [hxy_vsub]
      _ = |r * P.basis.repr (x -ᵥ P.center) i| := by simp
      _ = |r| * |P.basis.repr (x -ᵥ P.center) i| := by rw [abs_mul]
      _ = r * |P.basis.repr (x -ᵥ P.center) i| := by rw [abs_of_pos hr]
      _ ≤ r * (P.thicknesses i : ℝ) := by gcongr; exact hx i
      _ = (Q.thicknesses i : ℝ) := by symm; exact hQthick i
  · intro hy
    rw [Q.mem_carrier_iff] at hy
    have hy_vsub (i : Fin 3) : |P.basis.repr (y -ᵥ center') i| ≤ r * (P.thicknesses i : ℝ) := by
      calc
        |P.basis.repr (y -ᵥ center') i| ≤ (Q.thicknesses i : ℝ) := hy i
        _ = r * (P.thicknesses i : ℝ) := hQthick i
    set x := P.center + r⁻¹ • (y -ᵥ center') with hx
    have h_mul_inv : r * r⁻¹ = (1 : ℝ) := by field_simp [hr.ne.symm]
    have hx_mem : x ∈ P.carrier := by
      rw [P.mem_carrier_iff]
      intro i
      have h_vsub_eq : y -ᵥ center' = r • (x -ᵥ P.center) := by
        calc
          y -ᵥ center' = (1 : ℝ) • (y -ᵥ center') := by simp
          _ = (r * r⁻¹) • (y -ᵥ center') := by rw [h_mul_inv]
          _ = r • (r⁻¹ • (y -ᵥ center')) := by simp [smul_smul]
          _ = r • (x - P.center) := by
            simp [hx, vsub_eq_sub, smul_smul]
          _ = r • (x -ᵥ P.center) := by simp [vsub_eq_sub]
      have h_abs_bound : r * |P.basis.repr (x -ᵥ P.center) i| ≤ r * (P.thicknesses i : ℝ) := by
        calc
          r * |P.basis.repr (x -ᵥ P.center) i|
              = |P.basis.repr (r • (x -ᵥ P.center)) i| := by
                simp [abs_mul, abs_of_pos hr]
          _ = |P.basis.repr (y -ᵥ center') i| := by rw [h_vsub_eq]
          _ ≤ r * (P.thicknesses i : ℝ) := hy_vsub i
      nlinarith
    have h_image : h x = y := by
      calc
        h x = r • (x -ᵥ c) +ᵥ c := by
          simpa [h, vsub_eq_sub, add_comm] using AffineMap.homothety_apply c r x
        _ = r • ((P.center + r⁻¹ • (y -ᵥ center')) -ᵥ c) +ᵥ c := rfl
        _ = r • ((P.center -ᵥ c) + r⁻¹ • (y -ᵥ center')) +ᵥ c := by
          simp only [vsub_eq_sub]
          abel_nf
        _ = (r • (P.center -ᵥ c) + r • (r⁻¹ • (y -ᵥ center'))) +ᵥ c := by simp [smul_add]
        _ = (r • (P.center -ᵥ c) + (y -ᵥ center')) +ᵥ c := by
          simp [smul_smul, h_mul_inv]
        _ = (r • (P.center -ᵥ c) +ᵥ c) + (y -ᵥ center') := by
          simp [add_comm, add_assoc]
        _ = h P.center + (y -ᵥ center') := by
          simp [h, AffineMap.homothety_apply, vsub_eq_sub, add_comm]
        _ = center' + (y -ᵥ center') := rfl
        _ = y := by
          dsimp [center']
          simp
    exact ⟨x, hx_mem, h_image⟩

/-- **A homothety image of a measurable set is measurable** (measurability helper for the dense-box
slab construction). A homothety with nonzero ratio `r` is a homeomorphism `x ↦ r • (x - c) + c`
(a scaling by the unit `r` conjugated by translations), so it maps measurable sets to measurable
sets. Isolated so the `ShadedSlab` pushforward `exists_rescaled_shadedSlab` can discharge its
`measurableSet_shade` field by a single lemma application. -/
theorem measurableSet_homothety_image
    (c : EuclideanSpace ℝ (Fin 3)) (r : ℝ) (hr : r ≠ 0)
    {sh : Set (EuclideanSpace ℝ (Fin 3))} (hsh : MeasurableSet sh) :
    MeasurableSet ((AffineMap.homothety c r) '' sh) := by
  -- The homothety is a homeomorphism, so `MeasurableEmbedding` transfers measurability.
  let h_homeo : EuclideanSpace ℝ (Fin 3) ≃ₜ EuclideanSpace ℝ (Fin 3) :=
    { toFun := AffineMap.homothety c r
      invFun := AffineMap.homothety c (r⁻¹)
      left_inv := by
        intro x
        calc
          AffineMap.homothety c (r⁻¹) (AffineMap.homothety c r x)
              = r⁻¹ • (r • (x -ᵥ c) +ᵥ c -ᵥ c) +ᵥ c := by
                simp [AffineMap.homothety_apply]
          _ = r⁻¹ • (r • (x -ᵥ c)) +ᵥ c := by simp
          _ = (r⁻¹ * r) • (x -ᵥ c) +ᵥ c := by simp [smul_smul]
          _ = 1 • (x -ᵥ c) +ᵥ c := by
            simp [inv_mul_cancel₀ hr]
          _ = (x -ᵥ c) +ᵥ c := by simp
          _ = x := by simp
      right_inv := by
        intro x
        calc
          AffineMap.homothety c r (AffineMap.homothety c (r⁻¹) x)
              = r • (r⁻¹ • (x -ᵥ c) +ᵥ c -ᵥ c) +ᵥ c := by
                simp [AffineMap.homothety_apply]
          _ = r • (r⁻¹ • (x -ᵥ c)) +ᵥ c := by simp
          _ = (r * r⁻¹) • (x -ᵥ c) +ᵥ c := by simp [smul_smul]
          _ = 1 • (x -ᵥ c) +ᵥ c := by
            simp [mul_inv_cancel₀ hr]
          _ = (x -ᵥ c) +ᵥ c := by simp
          _ = x := by simp
      continuous_toFun := AffineMap.homothety_continuous c r
      continuous_invFun := AffineMap.homothety_continuous c (r⁻¹) }
  have h_emb : MeasurableEmbedding h_homeo := h_homeo.measurableEmbedding
  -- `h_homeo` coerces to `AffineMap.homothety c r`, so the goal is exactly
  -- `h_emb.measurableSet_image.mpr hsh`.
  simpa [h_homeo] using (h_emb.measurableSet_image).mpr hsh

/-- **Volume of a homothety image of a finite union** (volume-transfer helper for the dense-box
pullback, step B). The homothety by ratio `r` about `c` scales every volume by the constant
Jacobian `|r|³` (dimension `3`), and commutes with unions, so the image of `⋃ i∈s, g i` has volume
`ofReal |r|³` times that of `⋃ i∈s, g i`. This is the identity used to pull the rescaled
shading-union mass back to the original box. -/
theorem volume_iUnion_homothety_image {ι : Type*}
    (c : EuclideanSpace ℝ (Fin 3)) (r : ℝ)
    (s : Finset ι) (g : ι → Set (EuclideanSpace ℝ (Fin 3))) :
    volume (⋃ i ∈ s, (AffineMap.homothety c r) '' (g i))
      = ENNReal.ofReal (|r| ^ 3) * volume (⋃ i ∈ s, g i) := by
  calc
    volume (⋃ i ∈ s, (AffineMap.homothety c r) '' (g i))
        = volume ((AffineMap.homothety c r) '' (⋃ i ∈ s, g i)) := by
      rw [Set.image_iUnion₂]
    _ = ENNReal.ofReal (abs (r ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))) * volume (⋃ i ∈
        s, g i) := by
      rw [MeasureTheory.Measure.addHaar_image_homothety]
    _ = ENNReal.ofReal (|r| ^ 3) * volume (⋃ i ∈ s, g i) := by
      have hfinrank : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
      rw [hfinrank]
      simp [abs_pow]

/-- **Volume of a homothety image of an intersection** (volume-transfer helper for the incidence
mass, step D).  A homothety with ratio `r ≠ 0` is injective, so it commutes with intersection
(`h '' A ∩ h '' B = h '' (A ∩ B)`); combined with the Jacobian `|r|³` this scales the intersection
volume.  Used to transfer the plank shade-intersection mass `∑ᵢⱼ|Yᵢ ∩ Yⱼ|` to the rescaled slab
family's incidence mass `tri`. -/
theorem volume_inter_homothety_image
    (c : EuclideanSpace ℝ (Fin 3)) (r : ℝ) (hr : r ≠ 0)
    (A B : Set (EuclideanSpace ℝ (Fin 3))) :
    volume ((AffineMap.homothety c r) '' A ∩ (AffineMap.homothety c r) '' B)
      = ENNReal.ofReal (|r| ^ 3) * volume (A ∩ B) := by
  have hinj : Function.Injective (AffineMap.homothety c r) := by
    intro x y h
    have h_vsub : (AffineMap.homothety c r x) -ᵥ c = (AffineMap.homothety c r y) -ᵥ c := by rw [h]
    have h_smul_eq : r • (x -ᵥ c) = r • (y -ᵥ c) := by
      calc
        r • (x -ᵥ c) = (AffineMap.homothety c r x) -ᵥ c := by
          simp [AffineMap.homothety_apply]
        _ = (AffineMap.homothety c r y) -ᵥ c := h_vsub
        _ = r • (y -ᵥ c) := by simp [AffineMap.homothety_apply]
    have h_smul : x -ᵥ c = y -ᵥ c := by
      calc
        x -ᵥ c = (1 : ℝ) • (x -ᵥ c) := by simp
        _ = (r⁻¹ * r) • (x -ᵥ c) := by field_simp [hr]
        _ = r⁻¹ • (r • (x -ᵥ c)) := by simp [smul_smul]
        _ = r⁻¹ • (r • (y -ᵥ c)) := by rw [h_smul_eq]
        _ = (r⁻¹ * r) • (y -ᵥ c) := by simp [smul_smul]
        _ = (1 : ℝ) • (y -ᵥ c) := by field_simp [hr]
        _ = y -ᵥ c := by simp
    calc
      x = (x -ᵥ c) +ᵥ c := by simp
      _ = (y -ᵥ c) +ᵥ c := by rw [h_smul]
      _ = y := by simp
  calc
    volume ((AffineMap.homothety c r) '' A ∩ (AffineMap.homothety c r) '' B)
        = volume ((AffineMap.homothety c r) '' (A ∩ B)) := by
      rw [Set.image_inter hinj]
    _ = ENNReal.ofReal (abs (r ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))) * volume (A ∩ B)
        := by
      rw [MeasureTheory.Measure.addHaar_image_homothety]
    _ = ENNReal.ofReal (|r| ^ 3) * volume (A ∩ B) := by
      have hfinrank : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
      rw [hfinrank]
      simp [abs_pow]

end Plank

end
