/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.FactorFamily.Basic
public import Mathlib.Algebra.Order.Floor.Extended

/-! # Finite weighted second-moment estimates

This file contains the algebraic estimate used to sum the blockwise fullness conclusions in the
corrected condition of GWZ Proposition 5.1.  It is stated for `ENNReal`, so applications do not
need to leave the measure-theoretic codomain.
-/

public section

open scoped ENNReal

namespace ENNReal

/-- A finite weighted Cauchy--Schwarz estimate, with a harmless explicit factor `2`. -/
theorem sq_sum_mul_le_two_mul_sum_mul_sum_sq_mul {I : Type*} (s : Finset I)
    (q b : I → ENNReal) :
    (∑ i ∈ s, q i * b i) ^ 2 ≤
      2 * (∑ i ∈ s, b i) * (∑ i ∈ s, q i ^ 2 * b i) := by
  classical
  calc
    (∑ i ∈ s, q i * b i) ^ 2 =
        ∑ i ∈ s, ∑ j ∈ s, (q i * b i) * (q j * b j) := by
      rw [pow_two, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ s, ∑ j ∈ s,
          ((q i ^ 2 * b i) * b j + (q j ^ 2 * b j) * b i) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      have hq : q i * q j ≤ q i ^ 2 + q j ^ 2 := by
        rcases le_total (q i) (q j) with hij | hji
        · calc
            q i * q j ≤ q j ^ 2 := by
              simpa [pow_two, mul_comm] using mul_le_mul_left hij (q j)
            _ ≤ q i ^ 2 + q j ^ 2 := le_add_of_nonneg_left zero_le
        · calc
            q i * q j ≤ q i ^ 2 := by
              simpa [pow_two, mul_comm] using mul_le_mul_left hji (q i)
            _ ≤ q i ^ 2 + q j ^ 2 := le_add_of_nonneg_right zero_le
      calc
        (q i * b i) * (q j * b j) = (q i * q j) * (b i * b j) := by ring
        _ ≤ (q i ^ 2 + q j ^ 2) * (b i * b j) := by gcongr
        _ = (q i ^ 2 * b i) * b j + (q j ^ 2 * b j) * b i := by ring
    _ = (∑ i ∈ s, q i ^ 2 * b i) * (∑ i ∈ s, b i) +
          (∑ i ∈ s, q i ^ 2 * b i) * (∑ i ∈ s, b i) := by
      have hsplit (i : I) :
          (∑ j ∈ s, ((q i ^ 2 * b i) * b j + (q j ^ 2 * b j) * b i)) =
            (∑ j ∈ s, (q i ^ 2 * b i) * b j) +
              ∑ j ∈ s, (q j ^ 2 * b j) * b i := by
        exact Finset.sum_add_distrib
      rw [Finset.sum_congr rfl (fun i _ ↦ hsplit i), Finset.sum_add_distrib]
      congr 1
      · calc
          ∑ i ∈ s, ∑ j ∈ s, (q i ^ 2 * b i) * b j =
              ∑ i ∈ s, (q i ^ 2 * b i) * (∑ j ∈ s, b j) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
          _ = (∑ i ∈ s, q i ^ 2 * b i) * (∑ j ∈ s, b j) := by
            rw [Finset.sum_mul]
      · calc
          ∑ i ∈ s, ∑ j ∈ s, (q j ^ 2 * b j) * b i =
              ∑ i ∈ s, (∑ j ∈ s, q j ^ 2 * b j) * b i := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_mul]
          _ = (∑ j ∈ s, q j ^ 2 * b j) * (∑ i ∈ s, b i) := by
            rw [Finset.mul_sum]
    _ = 2 * (∑ i ∈ s, b i) * (∑ i ∈ s, q i ^ 2 * b i) := by
      ring

/-- A first weighted moment controls the corresponding second moment. -/
theorem weighted_second_moment_lower {I : Type*} (s : Finset I)
    (q b : I → ENNReal) (lam R : ENNReal)
    (hB0 : (∑ i ∈ s, b i) ≠ 0) (hBtop : (∑ i ∈ s, b i) ≠ ⊤)
    (havg : lam * (∑ i ∈ s, b i) ≤ R * (∑ i ∈ s, q i * b i)) :
    lam ^ 2 * (∑ i ∈ s, b i) ≤
      2 * R ^ 2 * (∑ i ∈ s, q i ^ 2 * b i) := by
  have hsq := pow_le_pow_left' havg 2
  have hcs := sq_sum_mul_le_two_mul_sum_mul_sum_sq_mul s q b
  apply (ENNReal.mul_le_mul_iff_right hB0 hBtop).mp
  calc
    (∑ i ∈ s, b i) * (lam ^ 2 * ∑ i ∈ s, b i) =
        (lam * ∑ i ∈ s, b i) ^ 2 := by ring
    _ ≤ (R * ∑ i ∈ s, q i * b i) ^ 2 := hsq
    _ = R ^ 2 * (∑ i ∈ s, q i * b i) ^ 2 := by ring
    _ ≤ R ^ 2 * (2 * (∑ i ∈ s, b i) *
          (∑ i ∈ s, q i ^ 2 * b i)) := by gcongr
    _ = (∑ i ∈ s, b i) *
          (2 * R ^ 2 * (∑ i ∈ s, q i ^ 2 * b i)) := by ring

end ENNReal

namespace ShadedBody

open MeasureTheory

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {ι κ : Type*}

open Classical in
/-- Summing carrier volumes over all factor-family fibers recovers the total carrier volume. -/
theorem sum_fiber_carrierVolume_eq (F : FactorFamily E ι κ) :
    ∑ j ∈ F.outerSet, ∑ i ∈ F.fiber j, volume (F.innerBody i).carrier =
      ∑ i ∈ F.innerSet, volume (F.innerBody i).carrier := by
  simpa only [FactorFamily.fiber] using
    Finset.sum_fiberwise_of_maps_to F.parent_mem
      (fun i ↦ volume (F.innerBody i).carrier)

open Classical in
/-- Summing shading masses over all factor-family fibers recovers the total shading mass. -/
theorem sum_fiber_shadeVolume_eq (F : FactorFamily E ι κ) :
    ∑ j ∈ F.outerSet, ∑ i ∈ F.fiber j, volume (F.innerBody i).shade =
      ∑ i ∈ F.innerSet, volume (F.innerBody i).shade := by
  simpa only [FactorFamily.fiber] using
    Finset.sum_fiberwise_of_maps_to F.parent_mem
      (fun i ↦ volume (F.innerBody i).shade)

open Classical in
/-- The carrier-weighted sum of fiber fullnesses is the total shading mass. -/
theorem sum_fullness_mul_fiberCarrierVolume_eq (F : FactorFamily E ι κ) :
    ∑ j ∈ F.outerSet, (fullness (F.fiber j) F.innerBody : ENNReal) *
        (∑ i ∈ F.fiber j, volume (F.innerBody i).carrier) =
      ∑ i ∈ F.innerSet, volume (F.innerBody i).shade := by
  calc
    ∑ j ∈ F.outerSet, (fullness (F.fiber j) F.innerBody : ENNReal) *
        (∑ i ∈ F.fiber j, volume (F.innerBody i).carrier) =
        ∑ j ∈ F.outerSet, ∑ i ∈ F.fiber j, volume (F.innerBody i).shade := by
      apply Finset.sum_congr rfl
      intro j _
      exact (sum_volumeReal_shade_eq_fullness_mul (F.fiber j) F.innerBody).symm
    _ = ∑ i ∈ F.innerSet, volume (F.innerBody i).shade :=
      sum_fiber_shadeVolume_eq F

open Classical in
/-- Some used fibre has fullness at least the fullness of the whole factor family.

This is the carrier-weighted averaging principle needed by Proposition 6.6(A).  Notice that it
does not ask for the fibre carrier masses to be comparable: positivity and finiteness of the
total carrier mass are enough. -/
theorem exists_fullness_le_fiber (F : FactorFamily E ι κ)
    (houter : F.outerSet.Nonempty)
    (hcarrier0 : (∑ i ∈ F.innerSet, volume (F.innerBody i).carrier) ≠ 0) :
    ∃ j ∈ F.outerSet,
      (fullness F.innerSet F.innerBody : ENNReal) ≤
        (fullness (F.fiber j) F.innerBody : ENNReal) := by
  let q : κ → ENNReal := fun j ↦ fullness (F.fiber j) F.innerBody
  obtain ⟨j₀, hj₀, hqmax⟩ := Finset.exists_max_image F.outerSet q houter
  have hcarrierTop : (∑ i ∈ F.innerSet, volume (F.innerBody i).carrier) ≠ ⊤ := by
    rw [ENNReal.sum_ne_top]
    intro i hi
    exact (F.innerBody i).isCompact.measure_ne_top
  have hweighted :
      ∑ j ∈ F.outerSet, q j * (∑ i ∈ F.fiber j, volume (F.innerBody i).carrier) ≤
        q j₀ * ∑ i ∈ F.innerSet, volume (F.innerBody i).carrier := by
    calc
      ∑ j ∈ F.outerSet, q j * (∑ i ∈ F.fiber j, volume (F.innerBody i).carrier) ≤
          ∑ j ∈ F.outerSet,
            q j₀ * (∑ i ∈ F.fiber j, volume (F.innerBody i).carrier) := by
              exact Finset.sum_le_sum fun j hj ↦ mul_le_mul_right' (hqmax j hj) _
      _ = q j₀ * ∑ j ∈ F.outerSet,
          ∑ i ∈ F.fiber j, volume (F.innerBody i).carrier := by
            rw [Finset.mul_sum]
      _ = q j₀ * ∑ i ∈ F.innerSet, volume (F.innerBody i).carrier := by
            rw [sum_fiber_carrierVolume_eq F]
  refine ⟨j₀, hj₀, ?_⟩
  rw [← ENNReal.mul_le_mul_iff_left hcarrier0 hcarrierTop]
  calc
    (fullness F.innerSet F.innerBody : ENNReal) *
          ∑ i ∈ F.innerSet, volume (F.innerBody i).carrier =
        ∑ i ∈ F.innerSet, volume (F.innerBody i).shade := by
          exact (sum_volumeReal_shade_eq_fullness_mul F.innerSet F.innerBody).symm
    _ = ∑ j ∈ F.outerSet,
        q j * (∑ i ∈ F.fiber j, volume (F.innerBody i).carrier) := by
          simpa only [q] using (sum_fullness_mul_fiberCarrierVolume_eq F).symm
    _ ≤ q j₀ * ∑ i ∈ F.innerSet, volume (F.innerBody i).carrier := hweighted

end ShadedBody
