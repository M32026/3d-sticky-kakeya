/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionN.Prism
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Geometry.Euclidean.Volume.Measure

/-!
# Volume of an `n`-dimensional prism

The Lebesgue volume and Euclidean Hausdorff measure of an `n`-dimensional prism,
expressed as the product of twice its thicknesses.
-/

open MeasureTheory ENNReal

@[expose] public section

noncomputable section

namespace PrismNDim

variable {n : ℕ} {E S : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [MetricSpace S] [NormedAddTorsor E S]
    [MeasurableSpace S] [BorelSpace S]

/-- The Lebesgue volume of an `n`-dimensional prism, in the special case where the
ambient vector space `E` and the affine space `S` coincide. The volume equals the product
of its side lengths (twice each thickness). -/
theorem volume_carrier (P : PrismNDim n E E) :
    volume P.carrier = 2 ^ Module.finrank ℝ E * ∏ i, (P.thicknesses i : ENNReal) := by
  rw [P.carrier_eq_preimage_Icc]
  -- Step 1: Translation invariance: on E, `(· -ᵥ P.center) = (· + (-P.center))`.
  simp_rw [vsub_eq_sub, sub_eq_add_neg]
  rw [measure_preimage_add_right]
  -- Step 2: `P.basis.repr` is measure-preserving.
  rw [P.basis.measurePreserving_repr.measure_preimage_emb
    P.basis.repr.toHomeomorph.toMeasurableEquiv.measurableEmbedding]
  -- Step 3: `WithLp.ofLp` is measure-preserving.
  rw [(PiLp.volume_preserving_ofLp (ι := Fin n)).measure_preimage_emb
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm.measurableEmbedding]
  -- Step 4: Compute the volume of the box in `Fin n → ℝ`.
  rw [Real.volume_Icc_pi]
  -- Step 5: Algebraic simplification.
  have h2t : ∀ i, ENNReal.ofReal ((P.thicknesses i : ℝ) - -(P.thicknesses i : ℝ)) =
      2 * (P.thicknesses i : ENNReal) := by
    intro i
    rw [sub_neg_eq_add, ← two_mul, ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
      ENNReal.ofReal_ofNat, ENNReal.ofReal_coe_nnreal]
  simp_rw [h2t, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  rw [Fintype.card_fin]
  congr 2
  rw [← Fintype.card_fin n, ← Module.finrank_eq_card_basis P.basis.toBasis]


/-- Dilating an `n`-dimensional prism scales its volume by `c ^ n`: every half-width is scaled
by `c`, and the volume is the product of the half-widths. -/
theorem volume_dilation (P : PrismNDim n E E) (c : NNReal) :
    volume (P.dilation c).carrier = (c : ENNReal) ^ n * volume P.carrier := by
  rw [volume_carrier, volume_carrier]
  simp_rw [dilation_thicknesses, ENNReal.coe_mul]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
  rw [Fintype.card_fin]
  ring

theorem euclideanHausdorffMeasure_carrier (P : PrismNDim n E S) :
    μHE[n] P.carrier = 2 ^ Module.finrank ℝ E * ∏ i, (P.thicknesses i : ENNReal) := by
  -- The canonical isometry `E ≃ᵢ S` given by translation by `P.center`.
  let e : E ≃ᵢ S := IsometryEquiv.vaddConst P.center
  -- The matching prism in `E` centered at `0` with the same basis and thicknesses.
  let Q : PrismNDim n E E := PrismNDim.mk' (0 : E) P.basis P.thicknesses
  have hcarr : (P.carrier : Set S) = e '' Q.carrier := by
    rw [P.carrier_eq_image_Icc, Q.carrier_eq_image_Icc]
    simp [Q, e, Set.image_image, IsometryEquiv.vaddConst, PrismNDim.mk']
  rw [hcarr, e.isometry.euclideanHausdorffMeasure_image]
  have hn : n = Module.finrank ℝ E := by
    rw [← Fintype.card_fin n, Module.finrank_eq_card_basis P.basis.toBasis]
  have heq : (μHE[n] : Measure E) = volume := by
    rw [hn]; exact InnerProductSpace.euclideanHausdorffMeasure_eq_volume
  rw [show μHE[n] Q.carrier = volume Q.carrier from congrArg (· Q.carrier) heq]
  exact Q.volume_carrier

end PrismNDim

end
