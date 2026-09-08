/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.GlobalPlankFactorizationEstimate
public import Kakeya.DimensionThree.Plank.FrostmanPlankAuxScale
public import Kakeya.Factoring.CoreAtScale
public import Kakeya.Tube.Dilate

/-!
# The inner normalisation package for Proposition 6.6(A)

Inside one selected flat-prism block the fine tubes themselves may be used as their coarse-parent
family.  The parent map is the identity, every fibre has cardinality one, and the Frostman datum is
exactly the factorisation's fibrewise Frostman clause.  This file packages that specialization of
the existing Part-(B) inner pipeline; it introduces no new analytic assumption.
-/

@[expose] public section

open MeasureTheory ConvexSpaceBody
open scoped ENNReal NNReal

noncomputable section

namespace ShadedBody

open Classical in
/-- Frostman control survives replacing every body by a larger, uniformly volume-comparable
envelope, provided both families lie in the same ambient body. -/
theorem IsFrostmanIn.of_envelope
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {I : Type*} {s : Finset I} {U P : I → ConvexSpaceBody E} {K : ConvexSpaceBody E}
    {C A : ENNReal} (hFr : IsFrostmanIn s U K C)
    (hUK : ∀ i ∈ s, U i ≤ K) (hPK : ∀ i ∈ s, P i ≤ K)
    (hUP : ∀ i ∈ s, U i ≤ P i)
    (hvol : ∀ i ∈ s, volume (P i).carrier ≤ A * volume (U i).carrier) :
    IsFrostmanIn s P K (A * C) := by
  apply ConvexSpaceBody.IsFrostmanIn.of_maxDensity_le
  have hmax : Kakeya.maxDensity s P ≤ A * Kakeya.maxDensity s U := by
    rw [Kakeya.maxDensity_le_iff]
    intro L
    rw [Kakeya.densityIn_le_iff]
    calc
      ∑ i ∈ s with P i ≤ L, volume (P i).carrier ≤
          ∑ i ∈ s with P i ≤ L, A * volume (U i).carrier := by
        exact Finset.sum_le_sum fun i hi ↦ hvol i (Finset.mem_filter.mp hi).1
      _ = A * ∑ i ∈ s with P i ≤ L, volume (U i).carrier := by
        rw [Finset.mul_sum]
      _ ≤ A * ∑ i ∈ s with U i ≤ L, volume (U i).carrier := by
        gcongr with i hi
        exact hUP i hi
      _ ≤ (A * Kakeya.maxDensity s U) * volume L.carrier := by
        rw [mul_assoc]
        gcongr
        exact (Kakeya.densityIn_le_iff s U L (Kakeya.maxDensity s U)).1
          (Kakeya.le_maxDensity s U L)
  have hdens : Kakeya.densityIn s U K ≤ Kakeya.densityIn s P K := by
    rw [Kakeya.densityIn_of_all_le hUK, Kakeya.densityIn_of_all_le hPK]
    gcongr with i hi
    exact hUP i hi
  calc
    Kakeya.maxDensity s P ≤ A * Kakeya.maxDensity s U := hmax
    _ ≤ A * (C * Kakeya.densityIn s U K) := by
      gcongr
      exact hFr.maxDensity_le_of_carrier_subset hUK
    _ ≤ (A * C) * Kakeya.densityIn s P K := by
      rw [mul_assoc]
      gcongr

/-- If two shaded families have the same shades and the new carriers have at most `A` times
the total old carrier volume, then the old fullness is at most `A` times the new fullness. -/
theorem fullness_le_mul_of_same_shade_of_sum_carrier_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {I : Type*} (s : Finset I) (U P : I → ShadedBody E) {A : NNReal}
    (hA0 : A ≠ 0)
    (hshade : ∀ i ∈ s, (U i).shade = (P i).shade)
    (hcarrier : ∑ i ∈ s, volume (P i).carrier ≤
      (A : ENNReal) * ∑ i ∈ s, volume (U i).carrier) :
    fullness s U ≤ A * fullness s P := by
  rw [← ENNReal.coe_le_coe, ENNReal.coe_mul, coe_fullness, coe_fullness]
  exact fullness'_le_mul_fullness'_reshape s U P hshade
    (ENNReal.coe_ne_zero.mpr hA0) ENNReal.coe_ne_top hcarrier

open Classical in
/-- A mass refinement of the inner family retains outer carrier mass when the complete input
fibres have comparable carrier densities.

This is the carrier ledger needed after the corrected Proposition 5.1 core.  It is deliberately
division-free: the retained coefficient, the input fullness and the two density-comparison
losses all remain visible. -/
theorem outerCarrierMass_retained_of_innerRefinement
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {I J : Type*}
    (F H : FactorFamily E I J) {c C : NNReal}
    (hne : H.outerSet.Nonempty)
    (href : IsCRefinement H.innerSet H.innerBody F.innerSet F.innerBody c)
    (hbody : ∀ i, (H.innerBody i).toConvexSpaceBody = (F.innerBody i).toConvexSpaceBody)
    (houter : H.outerSet ⊆ F.outerSet) (hparent : H.parent = F.parent)
    (hFne : ∀ j ∈ F.outerSet, (F.fiber j).Nonempty)
    (hpos : ∀ i ∈ F.innerSet, 0 < volume (F.innerBody i).carrier)
    (hdens : ∀ j ∈ F.outerSet, ∀ j' ∈ F.outerSet,
      Kakeya.densityIn (F.fiber j)
          (fun i ↦ (F.innerBody i).toConvexSpaceBody) (F.outerBody j) ≤
        (C : ENNReal) * Kakeya.densityIn (F.fiber j')
          (fun i ↦ (F.innerBody i).toConvexSpaceBody) (F.outerBody j')) :
    (c : ENNReal) * (fullness F.innerSet F.innerBody : ENNReal) *
        (∑ j ∈ F.outerSet, volume (F.outerBody j).carrier) ≤
      (C : ENNReal) ^ 2 *
        ∑ j ∈ H.outerSet, volume (F.outerBody j).carrier := by
  let j₀ := hne.choose
  have hj₀H : j₀ ∈ H.outerSet := hne.choose_spec
  have hj₀F : j₀ ∈ F.outerSet := houter hj₀H
  let d₀ : ENNReal := Kakeya.densityIn (F.fiber j₀)
    (fun i ↦ (F.innerBody i).toConvexSpaceBody) (F.outerBody j₀)
  have hd₀top : d₀ ≠ ⊤ := Kakeya.densityIn_ne_top _ _ _
  have hd₀0 : d₀ ≠ 0 := by
    obtain ⟨i, hi⟩ := hFne j₀ hj₀F
    simp only [FactorFamily.fiber, Finset.mem_filter] at hi
    have hle : (F.innerBody i).toConvexSpaceBody ≤ F.outerBody j₀ := by
      simpa only [hi.2] using F.inner_le_parent i hi.1
    exact (Kakeya.densityIn_pos_iff (F.fiber j₀)
      (fun i ↦ (F.innerBody i).toConvexSpaceBody) (F.outerBody j₀)).2
        ⟨i, by simpa only [FactorFamily.fiber, Finset.mem_filter], hpos i hi.1, hle⟩ |>.ne'
  have hFcarrier : d₀ * (∑ j ∈ F.outerSet, volume (F.outerBody j).carrier) ≤
      (C : ENNReal) * ∑ i ∈ F.innerSet, volume (F.innerBody i).carrier := by
    calc
      d₀ * (∑ j ∈ F.outerSet, volume (F.outerBody j).carrier) =
          ∑ j ∈ F.outerSet, d₀ * volume (F.outerBody j).carrier := by
            rw [Finset.mul_sum]
      _ ≤ ∑ j ∈ F.outerSet,
          ((C : ENNReal) * Kakeya.densityIn (F.fiber j)
            (fun i ↦ (F.innerBody i).toConvexSpaceBody) (F.outerBody j)) *
              volume (F.outerBody j).carrier := by
        exact Finset.sum_le_sum fun j hj ↦ by
          gcongr
          exact hdens j₀ hj₀F j hj
      _ = (C : ENNReal) * ∑ j ∈ F.outerSet,
          ∑ i ∈ F.fiber j, volume (F.innerBody i).carrier := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [mul_assoc, ← Kakeya.sum_volume_eq_densityIn_mul_volume'
          (fun i hi ↦ by
            simp only [FactorFamily.fiber, Finset.mem_filter] at hi
            simpa only [hi.2] using F.inner_le_parent i hi.1)]
      _ = (C : ENNReal) * ∑ i ∈ F.innerSet,
          volume (F.innerBody i).carrier := by
        rw [sum_fiber_carrierVolume_eq]
  have hHcarrier : ∑ i ∈ H.innerSet, volume (H.innerBody i).carrier ≤
      (C : ENNReal) * d₀ * ∑ j ∈ H.outerSet, volume (F.outerBody j).carrier := by
    calc
      ∑ i ∈ H.innerSet, volume (H.innerBody i).carrier =
          ∑ j ∈ H.outerSet, ∑ i ∈ H.fiber j,
            volume (H.innerBody i).carrier := (sum_fiber_carrierVolume_eq H).symm
      _ ≤ ∑ j ∈ H.outerSet, ∑ i ∈ F.fiber j,
          volume (F.innerBody i).carrier := by
        apply Finset.sum_le_sum
        intro j hj
        calc
          ∑ i ∈ H.fiber j, volume (H.innerBody i).carrier =
              ∑ i ∈ H.fiber j, volume (F.innerBody i).carrier := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hbody]
          _ ≤ ∑ i ∈ F.fiber j, volume (F.innerBody i).carrier := by
            apply Finset.sum_le_sum_of_subset
            intro i hi
            simp only [FactorFamily.fiber, Finset.mem_filter] at hi ⊢
            exact ⟨href.1.1 hi.1, by simpa only [hparent] using hi.2⟩
      _ = ∑ j ∈ H.outerSet,
          Kakeya.densityIn (F.fiber j)
              (fun i ↦ (F.innerBody i).toConvexSpaceBody) (F.outerBody j) *
            volume (F.outerBody j).carrier := by
        apply Finset.sum_congr rfl
        intro j hj
        exact Kakeya.sum_volume_eq_densityIn_mul_volume'
          (fun i hi ↦ by
            simp only [FactorFamily.fiber, Finset.mem_filter] at hi
            simpa only [hi.2] using F.inner_le_parent i hi.1)
      _ ≤ ∑ j ∈ H.outerSet,
          ((C : ENNReal) * d₀) * volume (F.outerBody j).carrier := by
        exact Finset.sum_le_sum fun j hj ↦ by
          gcongr
          exact hdens j (houter hj) j₀ hj₀F
      _ = (C : ENNReal) * d₀ *
          ∑ j ∈ H.outerSet, volume (F.outerBody j).carrier := by
        rw [Finset.mul_sum]
  have hshade : (c : ENNReal) * (fullness F.innerSet F.innerBody : ENNReal) *
      (∑ i ∈ F.innerSet, volume (F.innerBody i).carrier) ≤
      ∑ i ∈ H.innerSet, volume (H.innerBody i).carrier := by
    calc
      (c : ENNReal) * (fullness F.innerSet F.innerBody : ENNReal) *
          (∑ i ∈ F.innerSet, volume (F.innerBody i).carrier) =
        (c : ENNReal) * ∑ i ∈ F.innerSet, volume (F.innerBody i).shade := by
          rw [ShadedBody.sum_volumeReal_shade_eq_fullness_mul]
          ring
      _ ≤ ∑ i ∈ H.innerSet, volume (H.innerBody i).shade := href.2
      _ ≤ ∑ i ∈ H.innerSet, volume (H.innerBody i).carrier := by
        exact Finset.sum_le_sum fun i hi ↦ measure_mono (H.innerBody i).shade_subset
  have hwithd : d₀ * ((c : ENNReal) * (fullness F.innerSet F.innerBody : ENNReal) *
        (∑ j ∈ F.outerSet, volume (F.outerBody j).carrier)) ≤
      d₀ * ((C : ENNReal) ^ 2 *
        ∑ j ∈ H.outerSet, volume (F.outerBody j).carrier) := by
    calc
      d₀ * ((c : ENNReal) * (fullness F.innerSet F.innerBody : ENNReal) *
          (∑ j ∈ F.outerSet, volume (F.outerBody j).carrier)) =
        (c : ENNReal) * (fullness F.innerSet F.innerBody : ENNReal) *
          (d₀ * ∑ j ∈ F.outerSet, volume (F.outerBody j).carrier) := by ring
      _ ≤ (c : ENNReal) * (fullness F.innerSet F.innerBody : ENNReal) *
          ((C : ENNReal) * ∑ i ∈ F.innerSet,
            volume (F.innerBody i).carrier) := by gcongr
      _ = (C : ENNReal) * ((c : ENNReal) *
          (fullness F.innerSet F.innerBody : ENNReal) *
            ∑ i ∈ F.innerSet, volume (F.innerBody i).carrier) := by ring
      _ ≤ (C : ENNReal) * ∑ i ∈ H.innerSet,
          volume (H.innerBody i).carrier := by gcongr
      _ ≤ (C : ENNReal) * ((C : ENNReal) * d₀ *
          ∑ j ∈ H.outerSet, volume (F.outerBody j).carrier) := by gcongr
      _ = d₀ * ((C : ENNReal) ^ 2 *
          ∑ j ∈ H.outerSet, volume (F.outerBody j).carrier) := by ring
  apply (ENNReal.mul_le_mul_iff_left hd₀0 hd₀top).mp
  simpa only [mul_comm] using hwithd

open Classical in
/-- Comparable fibre densities and comparable outer volumes turn every fibre cardinality into
the average fibre cardinality, up to the product of the two comparison constants.

This is the counting ledger used by Proposition 6.6(A).  The inner carriers need only agree in
volume with a common-radius tube family; their shadings may already have been refined by the
Proposition-5.1 pipeline.  In particular, no lower uniformity bracket is used. -/
theorem fiber_card_mul_outerSet_card_le_of_density_comparable
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
    {ι κ : Type*} {δ : NNReal}
    (H : FactorFamily E ι κ) (hδ : 0 < δ) (T : ι → Tube δ E) (T₀ : Tube δ E)
    (hcarrier : ∀ i, volume (H.innerBody i).carrier = volume (T i).carrier)
    {Cdens Cvol : ENNReal}
    (hdens : ∀ j ∈ H.outerSet, ∀ j' ∈ H.outerSet,
      Kakeya.densityIn (H.fiber j) (fun i ↦ (H.innerBody i).toConvexSpaceBody)
          (H.outerBody j) ≤
        Cdens * Kakeya.densityIn (H.fiber j') (fun i ↦ (H.innerBody i).toConvexSpaceBody)
          (H.outerBody j'))
    (hvol : ∀ j ∈ H.outerSet, ∀ j' ∈ H.outerSet,
      volume (H.outerBody j).carrier ≤ Cvol * volume (H.outerBody j').carrier)
    {j : κ} (hj : j ∈ H.outerSet) :
    ((H.fiber j).card : ENNReal) * (H.outerSet.card : ENNReal) ≤
      Cdens * Cvol * (H.innerSet.card : ENNReal) := by
  classical
  have hsum (j' : κ) (hj' : j' ∈ H.outerSet) :
      ∑ i ∈ H.fiber j, volume (T i).carrier ≤
        (Cdens * Cvol) * ∑ i ∈ H.fiber j', volume (T i).carrier := by
    calc
      ∑ i ∈ H.fiber j, volume (T i).carrier =
          ∑ i ∈ H.fiber j, volume (H.innerBody i).carrier := by
            exact Finset.sum_congr rfl fun i _ ↦ (hcarrier i).symm
      _ = Kakeya.densityIn (H.fiber j) (fun i ↦ (H.innerBody i).toConvexSpaceBody)
            (H.outerBody j) * volume (H.outerBody j).carrier := by
          rw [← Kakeya.sum_volume_eq_densityIn_mul_volume']
          intro i hi
          have hi' := Finset.mem_filter.mp hi
          simpa only [hi'.2] using H.inner_le_parent i hi'.1
      _ ≤ (Cdens * Kakeya.densityIn (H.fiber j')
            (fun i ↦ (H.innerBody i).toConvexSpaceBody)
            (H.outerBody j')) *
          (Cvol * volume (H.outerBody j').carrier) :=
            mul_le_mul (hdens j hj j' hj') (hvol j hj j' hj') bot_le bot_le
      _ = (Cdens * Cvol) *
          (Kakeya.densityIn (H.fiber j') (fun i ↦ (H.innerBody i).toConvexSpaceBody)
            (H.outerBody j') * volume (H.outerBody j').carrier) := by
          ring
      _ = (Cdens * Cvol) *
          ∑ i ∈ H.fiber j', volume (H.innerBody i).carrier := by
            rw [← Kakeya.sum_volume_eq_densityIn_mul_volume']
            intro i hi
            have hi' := Finset.mem_filter.mp hi
            simpa only [hi'.2] using H.inner_le_parent i hi'.1
      _ = (Cdens * Cvol) * ∑ i ∈ H.fiber j', volume (T i).carrier := by
            congr 1
            exact Finset.sum_congr rfl fun i _ ↦ hcarrier i
  have hcard (j' : κ) (hj' : j' ∈ H.outerSet) :
      ((H.fiber j).card : ENNReal) ≤
        (Cdens * Cvol) * ((H.fiber j').card : ENNReal) := by
    have hv := hsum j' hj'
    simpa only [one_mul] using
      ((_root_.Tube.mul_sum_volume_le_iff_mul_card_le hδ T T₀
        (s := H.fiber j) (r := H.fiber j') (c := 1) (d := Cdens * Cvol)).mp (by
          simpa only [one_mul] using hv))
  calc
    ((H.fiber j).card : ENNReal) * (H.outerSet.card : ENNReal) =
        ∑ j' ∈ H.outerSet, ((H.fiber j).card : ENNReal) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ j' ∈ H.outerSet,
        (Cdens * Cvol) * ((H.fiber j').card : ENNReal) := by
          exact Finset.sum_le_sum fun j' hj' ↦ hcard j' hj'
    _ = (Cdens * Cvol) *
        ∑ j' ∈ H.outerSet, ((H.fiber j').card : ENNReal) := by
          rw [Finset.mul_sum]
    _ = (Cdens * Cvol) * (H.innerSet.card : ENNReal) := by
          congr 1
          have hcardNat : ∑ j' ∈ H.outerSet, (H.fiber j').card = H.innerSet.card := by
            simpa only [FactorFamily.fiber] using
              (Finset.card_eq_sum_card_fiberwise H.parent_mem).symm
          exact_mod_cast hcardNat
    _ = Cdens * Cvol * (H.innerSet.card : ENNReal) := by ring

end ShadedBody

namespace Kakeya

/-- Constant in the inner non-concentration estimate used by Proposition 6.6(A).

It is the product of the position-count constant, the pullback test-volume coefficient and the
square of the rectangular direction-packing coefficient. -/
noncomputable def flatPrismInnerNonconcentration.C
    (κ cslide : ℝ) (Cpos : ℕ) (C_NC : ℝ≥0) : ℝ≥0 :=
  max 1 ((Cpos : ℝ≥0) * innerPullbackTestVolumeConst κ C_NC *
    (1 + 64 * C_NC / (Real.toNNReal κ * Real.toNNReal cslide)) ^ 2)

/-- The normalised inner family inherited from pairwise essentially distinct fine tubes is
non-concentrated in the dilated thickenings used by GWZ Lemma 6.4.

The threshold `b₀` is exactly the smallness needed to place every tested tube direction in the
half-projective cap about the anchor.  Direction space is then divided by the two pullback-normal
coordinates, and the sharp position count is applied in each resulting cap. -/
theorem exists_innerPlank_isThickeningNonconcentrated {C_NC : ℝ≥0} (hC_NC : 1 ≤ C_NC)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ (Cinner b₀ : ℝ≥0) (δ₀ : ℝ),
      1 ≤ Cinner ∧ 0 < b₀ ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {ι : Type*} [DecidableEq ι] {δ a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
        (_hδ0 : 0 < δ) (_ha : 0 < a) (_hδa : δ ≤ a) (_hδsmall : (δ : ℝ) ≤ δ₀)
        (_hgeom : δ ≤ b₀ * a) (W : Plank a b hab hb1) (q : Finset ι)
        (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
        {a' b' : ℝ≥0} {ha'b' : a' ≤ b'} {hb'1 : b' ≤ 1}
        (P : ι → ShadedPlank a' b' ha'b' hb'1)
        (_ha'def : a' = δ / b) (_hb'def : b' = δ / a)
        (f : EuclideanSpace ℝ (Fin 3) →ᵃ[ℝ] EuclideanSpace ℝ (Fin 3))
        (F : EuclideanSpace ℝ (Fin 3) ≃ᵃ[ℝ] EuclideanSpace ℝ (Fin 3)) (J : ℝ≥0)
        (g : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)))
        (_hF : ∀ x, F x = f x) (_hJ : 0 < J)
        (_hnorm : Plank.IsPlankNormalisation W f κ g)
        (_hJab : J * (a * b) = Real.toNNReal κ ^ 3)
        (_hvolf : ∀ A : Set (EuclideanSpace ℝ (Fin 3)),
          volume ((F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) '' A) =
            (J : ENNReal) * volume A)
        (_hcarrier : ∀ i ∈ q, ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆ W.carrier)
        (_himg : ∀ i ∈ q,
          (f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) '' (T i).carrier ⊆
            (P i).carrier)
        (_halign : ∀ i ∈ q, (P i).basis 2 =
          (‖f.linear (T i).direction‖)⁻¹ • (f.linear (T i).direction))
        (_hortho : ∀ i ∈ q, (inner ℝ ((P i).basis 0) (g 0) : ℝ) = 0)
        (_hED : (q : Set ι).Pairwise
          (fun i j ↦ _root_.IsEssentiallyDistinct (T i).carrier (T j).carrier)),
        Plank.IsThickeningNonconcentrated q (fun i ↦ (P i).toPrism3D) C_NC
          (Cinner * (b / a) ^ 2) := by
  classical
  obtain ⟨cslide, Cpos, δ₀, hcslide, hCpos, hδ₀, hδ₀1, hcount⟩ :=
    exists_card_le_of_pullback_direction_partition
  let Cinner := flatPrismInnerNonconcentration.C κ cslide Cpos C_NC
  let b₀ : ℝ≥0 := Real.toNNReal (κ / (64 * (C_NC : ℝ)))
  have hCinner : 1 ≤ Cinner := by
    exact le_max_left _ _
  have hb₀ : 0 < b₀ := by
    dsimp [b₀]
    rw [Real.toNNReal_pos]
    positivity
  refine ⟨Cinner, b₀, δ₀, hCinner, hb₀, hδ₀, hδ₀1, ?_⟩
  intro ι _ δ a b hab hb1 hδ0 ha hδa hδsmall hgeom W q T a' b' ha'b' hb'1 P
    ha'def hb'def f F J g hF hJ hnorm hJab hvolf hcarrier himg halign hortho hED
  intro i hi φ hφ1 hφratio
  let s : Finset ι := q.filter fun j ↦
    ((P j).carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
      (((Plank.thickened (P i).toPrism3D φ hφ1).toPrismNDim.dilation C_NC).carrier :
        Set (EuclideanSpace ℝ (Fin 3)))
  let Q := Plank.thickened (P i).toPrism3D φ hφ1
  let K : Set (EuclideanSpace ℝ (Fin 3)) :=
    (F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) ⁻¹'
      ((Q.toPrismNDim.dilation C_NC).carrier : Set (EuclideanSpace ℝ (Fin 3)))
  let r := (T i).direction
  let q₀ := Plank.pullbackNormal W κ g ((P i).basis 0)
  let q₁ := Plank.pullbackNormal W κ g ((P i).basis 1)
  have hlin : f (T i).toTube.y - f (T i).toTube.x =
      f.linear ((T i).toTube.y - (T i).toTube.x) := by
    simpa using (AffineMap.linearMap_vsub f (T i).toTube.y (T i).toTube.x).symm
  have hlin' : f (T i).toTube.y - f (T i).toTube.x =
      f.linear (T i).toTube.direction := by
    simpa [Tube.direction] using hlin
  have halign' : (P i).basis 2 =
      (‖f (T i).toTube.y - f (T i).toTube.x‖)⁻¹ •
        (f (T i).toTube.y - f (T i).toTube.x) := by
    simpa [hlin'] using halign i hi
  have hrunit : ‖r‖ = 1 := by
    simpa [r] using (T i).toTube.norm_direction
  have hunit : ∀ j ∈ s, ‖(T j).toTube.direction‖ = 1 := by
    intro j hj
    exact (T j).toTube.norm_direction
  have hrq₀ : (inner ℝ r q₀ : ℝ) = 0 := by
    dsimp [r, q₀]
    exact inner_direction_pullbackNormal_eq_zero W hnorm (P i).toPrism3D (T i).toTube
      halign' (show (0 : Fin 3) ≠ 2 by decide)
  have hrq₁ : (inner ℝ r q₁ : ℝ) = 0 := by
    dsimp [r, q₁]
    exact inner_direction_pullbackNormal_eq_zero W hnorm (P i).toPrism3D (T i).toTube
      halign' (show (1 : Fin 3) ≠ 2 by decide)
  have hwi : ∀ k : Fin 3,
      |(inner ℝ (T i).toTube.direction (W.basis k) : ℝ)| ≤
        2 * (W.thicknesses k : ℝ) :=
    abs_inner_direction_basis_le_of_subset W (T i).toTube (hcarrier i hi)
  have hLu : f.linear (T i).toTube.direction ≠ 0 :=
    linear_ne_zero_of_affineEquiv_eq hF (by
      intro hzero
      have hdir := (T i).toTube.norm_direction
      simp only [hzero, norm_zero, zero_ne_one] at hdir)
  have hareaLower : κ ^ 2 / (4 * (a : ℝ) * (b : ℝ)) ≤ pullbackArea q₀ q₁ := by
    simpa [q₀, q₁] using le_pullbackArea W hκ hnorm ha (P i).toPrism3D
      (T i).toTube.norm_direction hwi (halign i hi) hLu
  have harea : 0 < pullbackArea q₀ q₁ := by
    have haR : (0 : ℝ) < a := by exact_mod_cast ha
    have hbR : (0 : ℝ) < b := by exact_mod_cast ha.trans_le hab
    exact lt_of_lt_of_le (by positivity) hareaLower
  have hnormq₀ : ‖q₀‖ ≤ κ / (b : ℝ) := by
    dsimp [q₀]
    exact norm_pullbackNormal_le_div_mid W hκ ha g ((P i).basis.norm_eq_one 0) (hortho i hi)
  have hnormq₁ : ‖q₁‖ ≤ κ / (a : ℝ) := by
    dsimp [q₁]
    exact norm_pullbackNormal_le_div_thin W hκ ha g ((P i).basis.norm_eq_one 1)
  have hEDs : (s : Set ι).Pairwise
      (fun j k ↦ _root_.IsEssentiallyDistinct (T j).carrier (T k).carrier) :=
    hED.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _))
  have htest : ∀ j ∈ s,
      (f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) '' (T j).carrier ⊆
        (Q.toPrismNDim.dilation C_NC).carrier := by
    intro j hj
    exact (himg j (Finset.mem_filter.mp hj).1).trans (Finset.mem_filter.mp hj).2
  have hsub : ∀ j ∈ s, (T j).carrier ⊆ K := by
    intro j hj x hx
    change F x ∈ (Q.toPrismNDim.dilation C_NC).carrier
    rw [hF]
    exact htest j hj ⟨x, hx, rfl⟩
  have hKcpt : IsCompact K := by
    dsimp [K]
    exact isCompact_preimage_affineEquiv F (Q.toPrismNDim.dilation C_NC).isCompact
  have hKmeas : MeasurableSet K := hKcpt.isClosed.measurableSet
  let Mnn : ℝ≥0 := innerPullbackTestVolumeConst κ C_NC * φ * (b / a)
  have hMnn : 0 < Mnn := by
    have ha'0 : 0 < a' := by
      rw [ha'def]
      exact div_pos hδ0 (ha.trans_le hab)
    have hb'0 : 0 < b' := ha'0.trans_le ha'b'
    have hφ0 : 0 < φ := lt_of_lt_of_le (div_pos ha'0 hb'0) hφratio
    have hconst : 0 < innerPullbackTestVolumeConst κ C_NC := by
      dsimp [innerPullbackTestVolumeConst]
      have hκNN : 0 < Real.toNNReal κ := Real.toNNReal_pos.mpr hκ
      positivity
    exact mul_pos (mul_pos hconst hφ0) (div_pos (ha.trans_le hab) ha)
  have hKvol : volume K ≤ ENNReal.ofReal (Mnn : ℝ) * (δ : ENNReal) ^ 2 := by
    have hv := volume_preimage_dilation_thickened_inner_plank ha (ha.trans_le hab) hκ
      ha'def hb'def (P i).toPrism3D hφ1 C_NC hJ hJab hvolf
    dsimp [K, Q]
    rw [hv]
    simp only [Mnn, ENNReal.ofReal_coe_nnreal, ENNReal.coe_mul]
    rw [ENNReal.coe_div ha.ne']
  let X : ℝ := 2 * (C_NC : ℝ) * (φ : ℝ) * (b' : ℝ)
  let Y : ℝ := 2 * (C_NC : ℝ) * (b' : ℝ)
  have hX : 0 ≤ X := by positivity
  have hY : 0 ≤ Y := by positivity
  have hprobe₀ : ∀ j ∈ s, |(inner ℝ q₀ (T j).toTube.direction : ℝ)| ≤ X := by
    intro j hj
    have h := abs_inner_direction_pullbackNormal_le_dilation W hnorm Q
      (T j).toTube (htest j hj) 0
    rw [Q.thicknesses_eq] at h
    have h' : |(inner ℝ (T j).toTube.direction q₀ : ℝ)| ≤
        2 * (C_NC : ℝ) * ((φ : ℝ) * (b' : ℝ)) := by
      simpa [q₀, Q, Plank.thickened_basis, real_inner_comm] using h
    simpa [X, mul_assoc, real_inner_comm] using h'
  have hprobe₁ : ∀ j ∈ s, |(inner ℝ q₁ (T j).toTube.direction : ℝ)| ≤ Y := by
    intro j hj
    have h := abs_inner_direction_pullbackNormal_le_dilation W hnorm Q
      (T j).toTube (htest j hj) 1
    rw [Q.thicknesses_eq] at h
    simpa [q₁, Q, Y, Plank.thickened_basis, real_inner_comm] using h
  have hcap : ∀ j ∈ s, projNormalDist (T j).toTube.direction r ≤ 1 / 2 := by
    intro j hj
    have hbase := projNormalDist_le_sqrtTwo_mul_pullbackCoordinates
      hrunit (T j).toTube.norm_direction hrq₀ hrq₁ harea
    have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
    have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast ha.trans_le hab
    have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
    have hCR : (0 : ℝ) < (C_NC : ℝ) := by exact_mod_cast lt_of_lt_of_le zero_lt_one hC_NC
    have hφR : (0 : ℝ) ≤ (φ : ℝ) := NNReal.coe_nonneg φ
    have hb'R : (b' : ℝ) = (δ : ℝ) / (a : ℝ) := by
      exact_mod_cast hb'def
    have hterm₀ : ‖q₀‖ * Y / pullbackArea q₀ q₁ ≤
        8 * (C_NC : ℝ) * (δ : ℝ) / κ := by
      rw [div_le_iff₀ harea]
      calc
        ‖q₀‖ * Y ≤ (κ / (b : ℝ)) * Y := by gcongr
        _ = (8 * (C_NC : ℝ) * (δ : ℝ) / κ) *
            (κ ^ 2 / (4 * (a : ℝ) * (b : ℝ))) := by
          dsimp [Y]
          rw [hb'R]
          field_simp [hκ.ne', haR.ne', hbR.ne']
          ring
        _ ≤ (8 * (C_NC : ℝ) * (δ : ℝ) / κ) *
            pullbackArea q₀ q₁ := by gcongr
    have hterm₁ : ‖q₁‖ * X / pullbackArea q₀ q₁ ≤
        8 * (C_NC : ℝ) * (φ : ℝ) * (δ : ℝ) * (b : ℝ) /
          (κ * (a : ℝ)) := by
      rw [div_le_iff₀ harea]
      calc
        ‖q₁‖ * X ≤ (κ / (a : ℝ)) * X := by gcongr
        _ = (8 * (C_NC : ℝ) * (φ : ℝ) * (δ : ℝ) * (b : ℝ) /
              (κ * (a : ℝ))) *
            (κ ^ 2 / (4 * (a : ℝ) * (b : ℝ))) := by
          dsimp [X]
          rw [hb'R]
          field_simp [hκ.ne', haR.ne', hbR.ne']
          ring
        _ ≤ (8 * (C_NC : ℝ) * (φ : ℝ) * (δ : ℝ) * (b : ℝ) /
              (κ * (a : ℝ))) * pullbackArea q₀ q₁ := by gcongr
    have hcoord :
        (‖q₀‖ * |(inner ℝ q₁ (T j).toTube.direction : ℝ)| +
            ‖q₁‖ * |(inner ℝ q₀ (T j).toTube.direction : ℝ)|) /
              pullbackArea q₀ q₁ ≤
          8 * (C_NC : ℝ) * (δ : ℝ) / κ +
            8 * (C_NC : ℝ) * (φ : ℝ) * (δ : ℝ) * (b : ℝ) /
              (κ * (a : ℝ)) := by
      rw [add_div]
      exact add_le_add
        ((div_le_div_iff_of_pos_right harea).2 (mul_le_mul_of_nonneg_left
          (hprobe₁ j hj) (norm_nonneg q₀)) |>.trans hterm₀)
        ((div_le_div_iff_of_pos_right harea).2 (mul_le_mul_of_nonneg_left
          (hprobe₀ j hj) (norm_nonneg q₁)) |>.trans hterm₁)
    have hb₀R : (b₀ : ℝ) = κ / (64 * (C_NC : ℝ)) := by
      dsimp [b₀]
      rw [max_eq_left (by positivity)]
    have hgeomR : (δ : ℝ) ≤ (b₀ : ℝ) * (a : ℝ) := by exact_mod_cast hgeom
    have hδdiv : (δ : ℝ) / (a : ℝ) ≤ (b₀ : ℝ) := by
      rw [div_le_iff₀ haR]
      simpa [mul_comm] using hgeomR
    have ha1R : (a : ℝ) ≤ 1 := by exact_mod_cast hab.trans hb1
    have hb1R : (b : ℝ) ≤ 1 := by exact_mod_cast hb1
    have hφ1R : (φ : ℝ) ≤ 1 := by exact_mod_cast hφ1
    have hfirst : 8 * (C_NC : ℝ) * (δ : ℝ) / κ ≤ 1 / 8 := by
      have hδb₀ : (δ : ℝ) ≤ (b₀ : ℝ) := by
        calc
          (δ : ℝ) ≤ (b₀ : ℝ) * (a : ℝ) := hgeomR
          _ ≤ (b₀ : ℝ) * 1 := by gcongr
          _ = (b₀ : ℝ) := mul_one _
      calc
        8 * (C_NC : ℝ) * (δ : ℝ) / κ ≤
            8 * (C_NC : ℝ) * (b₀ : ℝ) / κ := by gcongr
        _ = 1 / 8 := by
          rw [hb₀R]
          field_simp [hκ.ne', hCR.ne']
          norm_num
    have hsecond :
        8 * (C_NC : ℝ) * (φ : ℝ) * (δ : ℝ) * (b : ℝ) /
            (κ * (a : ℝ)) ≤ 1 / 8 := by
      have hprod : (φ : ℝ) * ((δ : ℝ) / (a : ℝ)) * (b : ℝ) ≤
          (b₀ : ℝ) := by
        calc
          (φ : ℝ) * ((δ : ℝ) / (a : ℝ)) * (b : ℝ) ≤
              1 * (b₀ : ℝ) * 1 := by gcongr
          _ = (b₀ : ℝ) := by ring
      calc
        8 * (C_NC : ℝ) * (φ : ℝ) * (δ : ℝ) * (b : ℝ) /
              (κ * (a : ℝ)) =
            (8 * (C_NC : ℝ) / κ) *
              ((φ : ℝ) * ((δ : ℝ) / (a : ℝ)) * (b : ℝ)) := by
          field_simp [hκ.ne', haR.ne']
        _ ≤ (8 * (C_NC : ℝ) / κ) * (b₀ : ℝ) := by gcongr
        _ = 1 / 8 := by
          rw [hb₀R]
          field_simp [hκ.ne', hCR.ne']
          norm_num
    have hquarter :
        (‖q₀‖ * |(inner ℝ q₁ (T j).toTube.direction : ℝ)| +
            ‖q₁‖ * |(inner ℝ q₀ (T j).toTube.direction : ℝ)|) /
              pullbackArea q₀ q₁ ≤ 1 / 4 := by
      linarith
    calc
      projNormalDist (T j).toTube.direction r ≤ Real.sqrt 2 *
          ((‖q₀‖ * |(inner ℝ q₁ (T j).toTube.direction : ℝ)| +
              ‖q₁‖ * |(inner ℝ q₀ (T j).toTube.direction : ℝ)|) /
                pullbackArea q₀ q₁) := hbase
      _ ≤ 2 * (1 / 4 : ℝ) := by
        gcongr
        exact (Real.sqrt_le_iff).2 (by norm_num)
      _ = 1 / 2 := by norm_num
  have hraw := hcount hδ0 hδsmall s (fun j ↦ (T j).toTube) hEDs hrunit hunit hrq₀ hrq₁
    harea hX hY hcap hprobe₀ hprobe₁ hKmeas hKcpt hMnn hKvol hsub
  change (s.card : ℝ≥0) ≤ (Cinner * (b / a) ^ 2) * φ
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hbR : (0 : ℝ) < (b : ℝ) := by exact_mod_cast ha.trans_le hab
  have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
  have hCR : (0 : ℝ) < (C_NC : ℝ) := by exact_mod_cast lt_of_lt_of_le zero_lt_one hC_NC
  have hb'R : (b' : ℝ) = (δ : ℝ) / (a : ℝ) := by exact_mod_cast hb'def
  have hterm₀ : ‖q₀‖ * Y / pullbackArea q₀ q₁ ≤
      8 * (C_NC : ℝ) * (δ : ℝ) / κ := by
    rw [div_le_iff₀ harea]
    calc
      ‖q₀‖ * Y ≤ (κ / (b : ℝ)) * Y := by gcongr
      _ = (8 * (C_NC : ℝ) * (δ : ℝ) / κ) *
          (κ ^ 2 / (4 * (a : ℝ) * (b : ℝ))) := by
        dsimp [Y]
        rw [hb'R]
        field_simp [hκ.ne', haR.ne', hbR.ne']
        ring
      _ ≤ (8 * (C_NC : ℝ) * (δ : ℝ) / κ) *
          pullbackArea q₀ q₁ := by gcongr
  have hterm₁ : ‖q₁‖ * X / pullbackArea q₀ q₁ ≤
      8 * (C_NC : ℝ) * (φ : ℝ) * (δ : ℝ) * (b : ℝ) /
        (κ * (a : ℝ)) := by
    rw [div_le_iff₀ harea]
    calc
      ‖q₁‖ * X ≤ (κ / (a : ℝ)) * X := by gcongr
      _ = (8 * (C_NC : ℝ) * (φ : ℝ) * (δ : ℝ) * (b : ℝ) /
            (κ * (a : ℝ))) *
          (κ ^ 2 / (4 * (a : ℝ) * (b : ℝ))) := by
        dsimp [X]
        rw [hb'R]
        field_simp [hκ.ne', haR.ne', hbR.ne']
        ring
      _ ≤ (8 * (C_NC : ℝ) * (φ : ℝ) * (δ : ℝ) * (b : ℝ) /
            (κ * (a : ℝ))) * pullbackArea q₀ q₁ := by gcongr
  let D : ℝ := 1 + 64 * (C_NC : ℝ) / (κ * cslide)
  let x : ℝ := (φ : ℝ) * ((b : ℝ) / (a : ℝ))
  let dcap : ℝ := cslide * (δ : ℝ) / 2 / 4
  have hdcap : 0 < dcap := by dsimp [dcap]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hratioNN : a' / b' = a / b := by
    rw [ha'def, hb'def]
    field_simp [hδ0.ne', ha.ne', (ha.trans_le hab).ne']
  have hratioR : (a' : ℝ) / (b' : ℝ) = (a : ℝ) / (b : ℝ) := by
    exact_mod_cast hratioNN
  have hx1 : 1 ≤ x := by
    have hφratioR : (a : ℝ) / (b : ℝ) ≤ (φ : ℝ) := by
      rw [← hratioR]
      exact_mod_cast hφratio
    calc
      (1 : ℝ) = ((a : ℝ) / (b : ℝ)) * ((b : ℝ) / (a : ℝ)) := by
        field_simp [haR.ne', hbR.ne']
      _ ≤ (φ : ℝ) * ((b : ℝ) / (a : ℝ)) := by gcongr
      _ = x := rfl
  have hxR : x ≤ (b : ℝ) / (a : ℝ) := by
    dsimp [x]
    have hφ1R : (φ : ℝ) ≤ 1 := by exact_mod_cast hφ1
    calc
      (φ : ℝ) * ((b : ℝ) / (a : ℝ)) ≤
          1 * ((b : ℝ) / (a : ℝ)) := by gcongr
      _ = (b : ℝ) / (a : ℝ) := one_mul _
  have hfac₀ :
      ((‖q₁‖ / pullbackArea q₀ q₁) * X + dcap) / dcap ≤ D * x := by
    have hz : (‖q₁‖ / pullbackArea q₀ q₁) * X ≤
        8 * (C_NC : ℝ) * (φ : ℝ) * (δ : ℝ) * (b : ℝ) /
          (κ * (a : ℝ)) := by
      simpa [div_mul_eq_mul_div] using hterm₁
    rw [div_le_iff₀ hdcap]
    calc
      (‖q₁‖ / pullbackArea q₀ q₁) * X + dcap ≤
          8 * (C_NC : ℝ) * (φ : ℝ) * (δ : ℝ) * (b : ℝ) /
              (κ * (a : ℝ)) + dcap := by gcongr
      _ = (64 * (C_NC : ℝ) / (κ * cslide)) * x * dcap + dcap := by
        dsimp [D, x, dcap]
        field_simp [hκ.ne', hcslide.ne', haR.ne', hδR.ne']
        ring
      _ ≤ (64 * (C_NC : ℝ) / (κ * cslide)) * x * dcap + x * dcap := by
        gcongr
        calc
          dcap = 1 * dcap := (one_mul dcap).symm
          _ ≤ x * dcap := mul_le_mul_of_nonneg_right hx1 hdcap.le
      _ = D * x * dcap := by
        dsimp [D]
        ring
  have hfac₁ :
      ((‖q₀‖ / pullbackArea q₀ q₁) * Y + dcap) / dcap ≤ D := by
    have hz : (‖q₀‖ / pullbackArea q₀ q₁) * Y ≤
        8 * (C_NC : ℝ) * (δ : ℝ) / κ := by
      simpa [div_mul_eq_mul_div] using hterm₀
    rw [div_le_iff₀ hdcap]
    calc
      (‖q₀‖ / pullbackArea q₀ q₁) * Y + dcap ≤
          8 * (C_NC : ℝ) * (δ : ℝ) / κ + dcap := by gcongr
      _ = D * dcap := by
        dsimp [D, dcap]
        field_simp [hκ.ne', hcslide.ne', hδR.ne']
        ring
  have hpack :
      (((‖q₁‖ / pullbackArea q₀ q₁) * X + dcap) / dcap) *
          (((‖q₀‖ / pullbackArea q₀ q₁) * Y + dcap) / dcap) ≤
        D ^ 2 * x := by
    calc
      _ ≤ (D * x) * D := mul_le_mul hfac₀ hfac₁ (by positivity) (by positivity)
      _ = D ^ 2 * x := by ring
  have hraw' : (s.card : ℝ) ≤ D ^ 2 * x * (Cpos : ℝ) * (Mnn : ℝ) := by
    calc
      (s.card : ℝ) ≤
          (((‖q₁‖ / pullbackArea q₀ q₁) * X + dcap) / dcap) *
            (((‖q₀‖ / pullbackArea q₀ q₁) * Y + dcap) / dcap) *
              (Cpos : ℝ) * (Mnn : ℝ) := by simpa [dcap] using hraw
      _ ≤ (D ^ 2 * x) * (Cpos : ℝ) * (Mnn : ℝ) := by gcongr
      _ = D ^ 2 * x * (Cpos : ℝ) * (Mnn : ℝ) := rfl
  have hDcoe :
      ((1 + 64 * C_NC /
        (Real.toNNReal κ * Real.toNNReal cslide) : ℝ≥0) : ℝ) = D := by
    dsimp [D]
    push_cast
    rw [max_eq_left hκ.le, max_eq_left hcslide.le]
  have hcoeff :
      (Cpos : ℝ) * (innerPullbackTestVolumeConst κ C_NC : ℝ) * D ^ 2 ≤
        (Cinner : ℝ) := by
    have hm := le_max_right (1 : ℝ≥0)
      ((Cpos : ℝ≥0) * innerPullbackTestVolumeConst κ C_NC *
        (1 + 64 * C_NC /
          (Real.toNNReal κ * Real.toNNReal cslide)) ^ 2)
    change ((Cpos : ℝ≥0) * innerPullbackTestVolumeConst κ C_NC *
        (1 + 64 * C_NC /
          (Real.toNNReal κ * Real.toNNReal cslide)) ^ 2 : ℝ≥0) ≤ Cinner at hm
    have hmR :
        (((Cpos : ℝ≥0) * innerPullbackTestVolumeConst κ C_NC *
          (1 + 64 * C_NC /
            (Real.toNNReal κ * Real.toNNReal cslide)) ^ 2 : ℝ≥0) : ℝ) ≤
          (Cinner : ℝ) := by exact_mod_cast hm
    push_cast at hmR
    rw [Real.coe_toNNReal', Real.coe_toNNReal'] at hmR
    rw [max_eq_left hκ.le, max_eq_left hcslide.le] at hmR
    simpa [D, mul_assoc] using hmR
  have hMnnR : (Mnn : ℝ) =
      (innerPullbackTestVolumeConst κ C_NC : ℝ) * x := by
    dsimp [Mnn, x]
    push_cast
    ring
  have hfinalR : (s.card : ℝ) ≤
      (Cinner : ℝ) * (((b : ℝ) / (a : ℝ)) ^ 2) * (φ : ℝ) := by
    calc
      (s.card : ℝ) ≤ D ^ 2 * x * (Cpos : ℝ) * (Mnn : ℝ) := hraw'
      _ = ((Cpos : ℝ) * (innerPullbackTestVolumeConst κ C_NC : ℝ) * D ^ 2) *
          (x * x) := by rw [hMnnR]; ring
      _ ≤ (Cinner : ℝ) * (((b : ℝ) / (a : ℝ)) * x) := by gcongr
      _ = (Cinner : ℝ) * (((b : ℝ) / (a : ℝ)) ^ 2) * (φ : ℝ) := by
        dsimp [x]
        ring
  exact_mod_cast hfinalR

/-- The master-scale density form of GWZ Lemma 6.1 is a theorem, rather than an extra
Section-6 hypothesis, once the auxiliary-scale Katz--Tao plank estimate is available. -/
theorem KatzTaoEstimate.plankEstimateAtMasterScaleWithDensity {β : ℝ}
    (hβpos : 0 < β) (hβle : β ≤ 1)
    (hKKT : KatzTaoEstimate.{0} (EuclideanSpace ℝ (Fin 3)) β) :
    PlankEstimateAtMasterScaleWithDensity.{0} β := by
  intro ε hε
  obtain ⟨η, hη, b₀, hb₀, hbound⟩ :=
    KatzTaoEstimate.plankEstimate_auxScale hβpos hβle hKKT ε hε
  refine ⟨η, hη, b₀, hb₀, ?_⟩
  intro ι s δ a b hab hb1 V hδ hδa hbb₀ hwin hed hfull γ hγ0 hγ1 hslab
  exact hbound s hab hb1 V hδ hδa hbb₀ hwin hed hfull γ hγ0 hγ1 hslab

/-- Constant in the Frostman transfer from a fine-tube fibre to the essentially-distinct
normalised inner plank family.  The factor `volume plankWindow` is the fixed change of ambient
body; `d + 1` is the conflict-colouring loss. -/
noncomputable def flatPrismInnerNormalisedFrostman.C
    (Cnorm : ℝ≥0) (d : ℕ) (CF : ENNReal) : ENNReal :=
  (Cnorm : ENNReal) * ((d : ENNReal) + 1) * CF * volume plankWindow.carrier

/-- Frostman control of a complete fine-tube fibre survives the fixed affine normalisation and
the conflict-graph extraction.

The proof is deliberately stated only in terms of the data exported by
`exists_inner_ED_family_of_fineTubes`.  No hidden identification of the extracted index type is
used: the cardinality retention and the exact, common plank volume suffice. -/
theorem innerNormalised_isFrostmanIn
    {ι ιj : Type*} [DecidableEq ι] {δ a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    (hδ0 : 0 < δ) (ha : 0 < a) (hδa : δ ≤ a)
    (W : Plank a b hab hb1) (q : Finset ι)
    (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
    (hcarrier : ∀ i ∈ q, ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆ W.carrier)
    {CF : ENNReal} (hFr : IsFrostmanIn q (fun i ↦ (T i).toConvexSpaceBody)
      W.toConvexSpaceBody CF)
    {a' b' : ℝ≥0} {ha'b' : a' ≤ b'} {hb'1 : b' ≤ 1}
    (ha' : a' = δ / b) (hb' : b' = δ / a)
    (Cnorm : ℝ≥0) (d : ℕ) (qj : Finset ιj)
    (P : ιj → ShadedPlank a' b' ha'b' hb'1)
    (hwindow : ∀ i ∈ qj, ((P i).carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
      Metric.closedBall 0 (plankWindowRadius : ℝ))
    (hcard : q.card ≤ (d + 1) * qj.card)
    (hmax : maxDensity qj (fun i ↦ (P i).toConvexSpaceBody) ≤
      (Cnorm : ENNReal) * maxDensity q (fun i ↦ (T i).toConvexSpaceBody)) :
    IsFrostmanIn qj (fun i ↦ (P i).toConvexSpaceBody) plankWindow
      (flatPrismInnerNormalisedFrostman.C Cnorm d CF) := by
  classical
  have hb : 0 < b := ha.trans_le hab
  have hδ1 : δ ≤ 1 := hδa.trans (hab.trans hb1)
  have hTW : ∀ i ∈ q, (T i).toConvexSpaceBody ≤ W.toConvexSpaceBody := hcarrier
  have hPW : ∀ i ∈ qj, (P i).toConvexSpaceBody ≤ plankWindow := by
    intro i hi
    change (P i).carrier ⊆ plankWindow.carrier
    rw [plankWindow_carrier]
    exact hwindow i hi
  have hW0 : volume W.carrier ≠ 0 :=
    (Prism3D.volume_pos_of_pos W ha).ne'
  have hWin0 : volume plankWindow.carrier ≠ 0 :=
    (zero_lt_one.trans_le one_le_volume_plankWindow).ne'
  have hsumT :
      (∑ i ∈ q, volume (T i).carrier) ≤
        (q.card : ENNReal) * (8 * (δ : ENNReal) ^ 2 * 2) := by
    calc
      (∑ i ∈ q, volume (T i).carrier) ≤
          ∑ _i ∈ q, 8 * (δ : ENNReal) ^ 2 * (1 / 2 + (δ : ENNReal)) := by
        exact Finset.sum_le_sum fun i _hi ↦ Tube.volume_carrier_le (T i).toTube
      _ ≤ ∑ _i ∈ q, 8 * (δ : ENNReal) ^ 2 * 2 := by
        apply Finset.sum_le_sum
        intro i hi
        gcongr
        calc
          (1 / 2 : ENNReal) + δ ≤ 1 + 1 := by
            gcongr
            · norm_num
            exact_mod_cast hδ1
          _ = 2 := by norm_num
      _ = (q.card : ENNReal) * (8 * (δ : ENNReal) ^ 2 * 2) := by
        simp [nsmul_eq_mul]
  have hsumP :
      (∑ i ∈ qj, volume (P i).carrier) =
        (qj.card : ENNReal) * (8 * (δ / b : ENNReal) * (δ / a : ENNReal)) := by
    calc
      (∑ i ∈ qj, volume (P i).carrier) =
          ∑ _i ∈ qj, 8 * (a' : ENNReal) * (b' : ENNReal) := by
        apply Finset.sum_congr rfl
        intro i hi
        simpa using (Prism3D.volume_carrier (P i).toPrism3D)
      _ = (qj.card : ENNReal) * (8 * (a' : ENNReal) * (b' : ENNReal)) := by
        simp [nsmul_eq_mul]
      _ = (qj.card : ENNReal) * (8 * (δ / b : ENNReal) * (δ / a : ENNReal)) := by
        rw [ha', hb', ENNReal.coe_div hb.ne', ENNReal.coe_div ha.ne']
  have hWvol : volume W.carrier = 8 * (a : ENNReal) * (b : ENNReal) := by
    simpa using (Prism3D.volume_carrier W)
  have hnumeric :
      (q.card : ENNReal) * (8 * (δ : ENNReal) ^ 2 * 2) ≤
        ((d : ENNReal) + 1) *
          ((qj.card : ENNReal) * (8 * (δ / b : ENNReal) * (δ / a : ENNReal))) *
            (8 * (a : ENNReal) * (b : ENNReal)) := by
    have hcardE : (q.card : ENNReal) ≤ ((d : ENNReal) + 1) * (qj.card : ENNReal) := by
      exact_mod_cast hcard
    have hgeom : 8 * (δ : ENNReal) ^ 2 * 2 ≤
        (8 * ((δ : ENNReal) / b) * ((δ : ENNReal) / a)) *
          (8 * (a : ENNReal) * (b : ENNReal)) := by
      have haE : (a : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr ha.ne'
      have hbE : (b : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hb.ne'
      rw [div_eq_mul_inv, div_eq_mul_inv]
      have hcancelA : (a : ENNReal)⁻¹ * a = 1 :=
        ENNReal.inv_mul_cancel haE ENNReal.coe_ne_top
      have hcancelB : (b : ENNReal)⁻¹ * b = 1 :=
        ENNReal.inv_mul_cancel hbE ENNReal.coe_ne_top
      calc
        8 * (δ : ENNReal) ^ 2 * 2 =
            (8 * 2) * (δ : ENNReal) ^ 2 := by ring
        _ ≤ 64 * (δ : ENNReal) ^ 2 := by
          gcongr
          norm_num
        _ = (8 * ((δ : ENNReal) * (b : ENNReal)⁻¹) *
              ((δ : ENNReal) * (a : ENNReal)⁻¹)) *
                (8 * (a : ENNReal) * (b : ENNReal)) := by
          rw [show (δ : ENNReal) ^ 2 = δ * δ by ring]
          calc
            64 * ((δ : ENNReal) * δ) =
                64 * ((δ : ENNReal) * δ) *
                  ((a : ENNReal)⁻¹ * a) * ((b : ENNReal)⁻¹ * b) := by
                    rw [hcancelA, hcancelB]
                    simp
            _ = _ := by ring
    calc
      (q.card : ENNReal) * (8 * (δ : ENNReal) ^ 2 * 2) ≤
          (((d : ENNReal) + 1) * (qj.card : ENNReal)) *
            (8 * (δ : ENNReal) ^ 2 * 2) := by gcongr
      _ ≤ ((d : ENNReal) + 1) *
          ((qj.card : ENNReal) * (8 * (δ / b : ENNReal) * (δ / a : ENNReal))) *
            (8 * (a : ENNReal) * (b : ENNReal)) := by
        calc
          (((d : ENNReal) + 1) * (qj.card : ENNReal)) *
              (8 * (δ : ENNReal) ^ 2 * 2) ≤
            (((d : ENNReal) + 1) * (qj.card : ENNReal)) *
              ((8 * ((δ : ENNReal) / b) * ((δ : ENNReal) / a)) *
                (8 * (a : ENNReal) * (b : ENNReal))) := by gcongr
          _ = _ := by ring
  have hsumTW : (∑ i ∈ q, volume (T i).carrier) ≤
      ((d : ENNReal) + 1) * (∑ i ∈ qj, volume (P i).carrier) * volume W.carrier := by
    calc
      _ ≤ (q.card : ENNReal) * (8 * (δ : ENNReal) ^ 2 * 2) := hsumT
      _ ≤ _ := by simpa only [hsumP, hWvol] using hnumeric
  have hFrDiv := hFr.maxDensity_mul_volume_le hTW hW0
  have hscaled : maxDensity q (fun i ↦ (T i).toConvexSpaceBody) *
        volume plankWindow.carrier ≤
      (((d : ENNReal) + 1) * CF * volume plankWindow.carrier) *
        (∑ i ∈ qj, volume (P i).carrier) := by
    apply (ENNReal.mul_le_mul_iff_right hW0 W.isCompact.measure_ne_top).mp
    calc
      volume W.carrier *
          (maxDensity q (fun i ↦ (T i).toConvexSpaceBody) * volume plankWindow.carrier) =
        (maxDensity q (fun i ↦ (T i).toConvexSpaceBody) * volume W.carrier) *
          volume plankWindow.carrier := by ring
      _ ≤ (CF * ∑ i ∈ q, volume (T i).carrier) * volume plankWindow.carrier := by
        gcongr
      _ ≤ (CF * (((d : ENNReal) + 1) *
          (∑ i ∈ qj, volume (P i).carrier) * volume W.carrier)) *
            volume plankWindow.carrier := by gcongr
      _ = volume W.carrier * ((((d : ENNReal) + 1) * CF * volume plankWindow.carrier) *
          (∑ i ∈ qj, volume (P i).carrier)) := by ring
  apply ConvexSpaceBody.IsFrostmanIn.of_maxDensity_mul_volume_le hPW hWin0
  calc
    maxDensity qj (fun i ↦ (P i).toConvexSpaceBody) * volume plankWindow.carrier ≤
        ((Cnorm : ENNReal) * maxDensity q (fun i ↦ (T i).toConvexSpaceBody)) *
          volume plankWindow.carrier := by gcongr
    _ ≤ (Cnorm : ENNReal) *
        ((((d : ENNReal) + 1) * CF * volume plankWindow.carrier) *
          (∑ i ∈ qj, volume (P i).carrier)) := by
      rw [mul_assoc]
      gcongr
    _ = flatPrismInnerNormalisedFrostman.C Cnorm d CF *
        ∑ i ∈ qj, volume (P i).carrier := by
      rw [flatPrismInnerNormalisedFrostman.C]
      ring

/-- Run the normalisation/ED-extraction pipeline on a pairwise essentially distinct fine-tube
family.

The wide-slab estimate used here is the relative form needed by Lemma 6.1.  It is automatic at
coefficient `(b / a) ^ 2`: for every admissible slab width `φ ≥ a / b`, that coefficient
times `φ` is at least one, while the slab subfamily is a subset of the whole fibre.  Thus the
fine-tube Frostman hypothesis used by the Part-(B) identity-parent specialization is unnecessary
in Part (A).  Pairwise essential distinctness of the original tubes is used only by the conflict
degree extraction which produces a pairwise essentially distinct normalised plank subfamily.

All returned constants depend only on the fixed normalisation, never on the family, its
cardinality, or any scale. -/
theorem exists_inner_ED_family_of_fineTubes (C_NC : ℝ≥0) (hC_NC : 1 ≤ C_NC) :
    ∃ (Cnorm : ℝ≥0) (d : ℕ) (Cinner bGeom : ℝ≥0) (δ₀ : ℝ),
      1 ≤ Cnorm ∧ 0 < d ∧ 1 ≤ Cinner ∧ 0 < bGeom ∧
      0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {ι : Type*} [DecidableEq ι] {δ a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
        (_hδ0 : 0 < δ) (_ha : 0 < a) (_hδa : δ ≤ a) (_hδconf : (δ : ℝ) ≤ δ₀)
        (a₀ b₀ : ℝ≥0) (_hsmalla : δ ≤ a₀ * b) (_hsmallb : δ ≤ b₀ * a)
        (_hgeom : δ ≤ bGeom * a)
        (W : Plank a b hab hb1) (q : Finset ι)
        (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
        q.Nonempty →
        (∀ i ∈ q, ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆ W.carrier) →
        (q : Set ι).Pairwise
          (fun i j ↦ _root_.IsEssentiallyDistinct
            ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
            ((T j).carrier : Set (EuclideanSpace ℝ (Fin 3)))) →
        ∃ (a' b' : ℝ≥0) (ha'b' : a' ≤ b') (hb'1 : b' ≤ 1) (ιj : Type)
            (qj : Finset ιj) (P : ιj → ShadedPlank a' b' ha'b' hb'1),
            a' = δ / b ∧ b' = δ / a ∧
            0 < a' ∧ δ ≤ a' ∧ b' ≤ b₀ ∧
            a' / b' = a / b ∧
            ((a' : ENNReal) / (b' : ENNReal) = (a : ENNReal) / (b : ENNReal)) ∧
            (∀ i ∈ qj, ((P i).carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
              Metric.closedBall 0 (plankWindowRadius : ℝ)) ∧
            (qj : Set ιj).Pairwise
              (fun i j ↦ _root_.IsEssentiallyDistinct
                ((P i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
                ((P j).carrier : Set (EuclideanSpace ℝ (Fin 3)))) ∧
            q.card ≤ (d + 1) * qj.card ∧ qj.card ≤ q.card ∧
            ShadedBody.fullness q (fun i ↦ (T i).toShadedBody) ≤
              Cnorm * ((d : ℝ≥0) + 1) *
                ShadedBody.fullness qj (fun i ↦ (P i).toShadedBody) ∧
            maxDensity qj (fun i ↦ (P i).toConvexSpaceBody) ≤
              (Cnorm : ENNReal) * maxDensity q (fun i ↦ (T i).toConvexSpaceBody) ∧
            (∀ (φ : ℝ≥0) (hφR : φ ≤ Rslab), a' / b' ≤ φ →
              ∀ (S : Prism3D φ Rslab Rslab hφR le_rfl),
                ((Plank.inWideSlabFamily qj (fun i ↦ (P i).toPrism3D) S).card : ℝ≥0) ≤
                  ((d : ℝ≥0) + 1) * (b / a) ^ 2 *
                    φ ^ (1 : ℝ) * (qj.card : ℝ≥0)) ∧
            Plank.IsThickeningNonconcentrated qj (fun i ↦ (P i).toPrism3D) C_NC
              (Cinner * (b / a) ^ 2) ∧
            ShadedBody.multiplicity q (fun i ↦ (T i).toShadedBody) ≤
              ((d : ENNReal) + 1) *
                ShadedBody.multiplicity qj (fun i ↦ (P i).toShadedBody) := by
  classical
  obtain ⟨kap, _cfac, _Cfac, hkap, _hcfac, _hCfac, hnormfam⟩ :=
    Plank.factorNormalisingAffineEquiv
  obtain ⟨Cnorm, hCnorm, hfam⟩ := innerShadedPlankFamily kap hkap
  obtain ⟨d, hd, δconf, hδconf, hδconf1, hdeg⟩ := exists_inner_plank_conflict_degree_bound hkap
  obtain ⟨Cinner, bGeom, δnc, hCinner, hbGeom, hδnc, hδnc1, hnc⟩ :=
    exists_innerPlank_isThickeningNonconcentrated hC_NC hkap
  let δ₀ := min δconf δnc
  have hδ₀ : 0 < δ₀ := lt_min hδconf hδnc
  have hδ₀1 : δ₀ ≤ 1 := (min_le_left _ _).trans hδconf1
  refine ⟨Cnorm, d, Cinner, bGeom, δ₀, hCnorm, hd, hCinner, hbGeom,
    hδ₀, hδ₀1, ?_⟩
  intro ι _ δ a b hab hb1 hδ0 ha hδa hδsmall a₀ b₀ hsmalla hsmallb hgeom W q T
    _hq hcarrier hED
  obtain ⟨f, J, g, hJ, hnorm, hvolf, himg, hWimg, hJab, _hJabU⟩ := hnormfam ha W
  obtain ⟨a', b', ha'b', hb'1, Pj, ha'def, hb'def, ha'pos, hδa', _ha'a₀, hb'b₀,
      hratioNN, hratioENN, hwindow, hfull, hmaxd, _hpull, hshade, hcarrimg, halign, hortho⟩ :=
    hfam ha hδ0 hδa a₀ b₀ hsmalla hsmallb W q T f J g hJ hnorm hvolf himg hcarrier
  obtain ⟨Faff, hFaff⟩ := Plank.exists_affineEquiv_of_isPlankNormalisation ha W hkap hnorm
  have hJab_deg : J * (a * b) = Real.toNNReal kap ^ 3 :=
    Plank.jacobian_eq ha W hkap hnorm hvolf
  have hvolfF : ∀ A : Set (EuclideanSpace ℝ (Fin 3)),
      volume ((Faff : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) '' A) =
        (J : ENNReal) * volume A := by
    intro A
    have hset : (Faff : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) '' A =
        (f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)) '' A :=
      congrArg (fun m : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) ↦ m '' A)
        (funext hFaff)
    rw [hset]
    exact hvolf A
  have halignlin : ∀ i ∈ q, (Pj i).basis 2 =
      (‖f.linear (T i).direction‖)⁻¹ • (f.linear (T i).direction) := by
    intro i hi
    exact align_linear_of_align_sub (T i).toTube (Pj i).toPrism3D (halign i hi)
  have hdeg' : ∀ i ∈ q, edConflictDegree q (fun j ↦ (Pj j).carrier) i ≤ d := by
    intro i hi
    exact hdeg ha hδ0 (hδsmall.trans (min_le_left _ _))
      (a' := a') (b' := b') (ha'b' := ha'b') (hb'1 := hb'1)
      ha'def hb'def W q (fun k ↦ (T k).toTube) (fun k ↦ (Pj k).toPrism3D)
      f Faff J g hFaff hJ hnorm hJab_deg hvolfF hcarrier hcarrimg halignlin hortho hED i hi
  have hcoef : 1 ≤ (b / a) ^ 2 * (a / b) := by
    rw [← NNReal.coe_le_coe]
    push_cast
    have haR : (0 : ℝ) < a := by exact_mod_cast ha
    have hbR : (0 : ℝ) < b := by exact_mod_cast ha.trans_le hab
    have hba : (1 : ℝ) ≤ (b : ℝ) / a := by
      rw [le_div_iff₀ haR]
      simpa using (show (a : ℝ) ≤ b by exact_mod_cast hab)
    have hone : (1 : ℝ) = ((b : ℝ) / a) * ((a : ℝ) / b) := by
      field_simp [haR.ne', hbR.ne']
    calc
      (1 : ℝ) = ((b : ℝ) / a) * ((a : ℝ) / b) := hone
      _ ≤ (((b : ℝ) / a) * ((b : ℝ) / a)) * ((a : ℝ) / b) := by
        gcongr
        exact le_mul_of_one_le_right (by positivity) hba
      _ = ((b : ℝ) / a) ^ 2 * ((a : ℝ) / b) := by ring
  have hslab : ∀ (φ : ℝ≥0) (hφR : φ ≤ Rslab), a' / b' ≤ φ →
      ∀ (S : Prism3D φ Rslab Rslab hφR le_rfl),
        ((Plank.inWideSlabFamily q (fun i ↦ (Pj i).toPrism3D) S).card : ℝ≥0) ≤
          (b / a) ^ 2 * φ ^ (1 : ℝ) * (q.card : ℝ≥0) := by
    intro φ hφR hratio S
    have hsub := Plank.inWideSlabFamily_subset
      (s := q) (V := fun i ↦ (Pj i).toPrism3D) (Sφ := S)
    have hcard : ((Plank.inWideSlabFamily q
        (fun i ↦ (Pj i).toPrism3D) S).card : ℝ≥0) ≤ (q.card : ℝ≥0) := by
      exact_mod_cast Finset.card_le_card hsub
    have hratio' : a / b ≤ φ := by simpa only [hratioNN] using hratio
    have hone : 1 ≤ (b / a) ^ 2 * φ := hcoef.trans (by gcongr)
    calc
      ((Plank.inWideSlabFamily q (fun i ↦ (Pj i).toPrism3D) S).card : ℝ≥0)
          ≤ (q.card : ℝ≥0) := hcard
      _ = 1 * (q.card : ℝ≥0) := by rw [one_mul]
      _ ≤ ((b / a) ^ 2 * φ) * (q.card : ℝ≥0) := by gcongr
      _ = (b / a) ^ 2 * φ ^ (1 : ℝ) * (q.card : ℝ≥0) := by
        rw [NNReal.rpow_one]
  have hncq : Plank.IsThickeningNonconcentrated q (fun i ↦ (Pj i).toPrism3D) C_NC
      (Cinner * (b / a) ^ 2) :=
    hnc hδ0 ha hδa (hδsmall.trans (min_le_right _ _)) hgeom W q T Pj ha'def hb'def
      f Faff J g hFaff hJ hnorm hJab_deg hvolfF hcarrier hcarrimg halignlin hortho hED
  let hpack := exists_inner_ED_factorisation_package q T Pj Cnorm ((b / a) ^ 2)
    hCnorm hwindow hfull hmaxd hslab hdeg'
  let ιj := hpack.choose
  let hpack₁ := hpack.choose_spec
  let qj := hpack₁.choose
  let hpack₂ := hpack₁.choose_spec
  let P := hpack₂.choose
  let hpack₃ := hpack₂.choose_spec
  let source := hpack₃.choose
  let hrest := hpack₃.choose_spec
  have hwin := hrest.2.2.1
  have hEDpair := hrest.2.2.2.1
  have hcard1 := hrest.2.2.2.2.1
  have hcard2 := hrest.2.2.2.2.2.1
  have hfull' := hrest.2.2.2.2.2.2.2.1
  have hmaxd' := hrest.2.2.2.2.2.2.2.2.1
  have hslab' := hrest.2.2.2.2.2.2.2.2.2.1
  have hmult := hrest.2.2.2.2.2.2.2.2.2.2
  have hnc' := source.isThickeningNonconcentrated hncq
  have hmt : ShadedBody.multiplicity q (fun i ↦ (Pj i).toShadedBody) =
      ShadedBody.multiplicity q (fun i ↦ (T i).toShadedBody) :=
    inner_multiplicity_transport ha hkap W hnorm q T Pj hshade
  refine ⟨a', b', ha'b', hb'1, ιj, qj, P, ha'def, hb'def, ha'pos, hδa', hb'b₀,
    hratioNN, hratioENN,
    hwin, hEDpair, hcard1, hcard2, hfull', hmaxd', hslab', hnc', ?_⟩
  calc
    ShadedBody.multiplicity q (fun i ↦ (T i).toShadedBody) =
        ShadedBody.multiplicity q (fun i ↦ (Pj i).toShadedBody) := hmt.symm
    _ ≤ ((d : ENNReal) + 1) *
        ShadedBody.multiplicity qj (fun i ↦ (P i).toShadedBody) := hmult

end Kakeya

end

end
