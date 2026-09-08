/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Multiplicity
public import Kakeya.Factoring.Step5
public import Kakeya.Mathlib.MeasureTheory.BoundedOverlap

/-! # A general packing lower bound for the multiplicity of a shaded family

The multiplicity `µ(𝒲, Y) = (∑ |Y j|) / |U(𝒲, Y)|` of a shaded family is an *average* incidence
count. Bounding it below by a *pointwise* count needs a packing argument, because a point of high
incidence carries no mass on its own.

This file isolates that argument in the generality in which it is true: no convexity, no tubes, no
relation to any factoring pipeline. The input is

* a finite `r`-separated set `S` of witness centres,
* a cover of the shaded union by the closed `m * r`-balls around `S`, and
* at every centre `z ∈ S`, at least `L` members of the family whose shade contains a ball of
  radius `r / 8` lying within `Metric.ball z (2 * r)`;

and the output is `L ≤ outerShadingPackingLoss n m * µ(𝒲, Y)`.

The loss `ShadedBody.outerShadingPackingLoss n m = 5 ^ n * (8 * m) ^ n` is purely dimensional: it
is the product of the Besicovitch overlap bound `Kakeya.factoringStep5OverlapConstant n` of an
`r`-separated set inside a ball of radius `2 * r` with the volume ratio between a ball of radius
`m * r` and a ball of radius `r / 8`.

`Kakeya/Factoring/RhoTubes.lean` contains the `ρ`-tube instance of this estimate as
`ShadedBody.outerMultiplicity_lower_of_local_balls`, at the fixed cover radius `4 * r`; that
instance is `m = 4` here, with the loss written as `ShadedBody.rhoTubesOuterMultiplicityLoss`
rather than `ShadedBody.outerShadingPackingLoss n 4`. That lemma is no longer `private`, so the
duplication between the two proofs is now removable; it has not been removed here because
`Kakeya/Factoring/RhoTubes.lean` is upstream of the whole Section 8 factoring constant and is not
to be restructured for this.
-/

@[expose] public section

open MeasureTheory Convexity
open scoped NNReal ENNReal

namespace ShadedBody

section OuterPacking

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {κ : Type*}

/-- **The packing loss of `ShadedBody.le_multiplicity_of_local_balls`.**

`n` is the ambient dimension and `m` the ratio between the radius of the covering balls and the
separation `r` of their centres. The two factors are the Besicovitch overlap bound
`Kakeya.factoringStep5OverlapConstant n = 5 ^ n` for an `r`-separated set contained in a ball of
radius `2 * r`, and the volume ratio `(8 * m) ^ n` between a ball of radius `m * r` and a ball of
radius `r / 8`.

It depends on nothing but `n` and `m`; in particular it is independent of the discretization scale
and of the cardinality of the family. -/
def outerShadingPackingLoss (n m : ℕ) : NNReal :=
  ((Kakeya.factoringStep5OverlapConstant n * (8 * m) ^ n : ℕ) : NNReal)

/-- The packing loss is at least `1` as soon as the covering radius is positive. -/
theorem one_le_outerShadingPackingLoss (n : ℕ) {m : ℕ} (hm : 0 < m) :
    1 ≤ outerShadingPackingLoss n m := by
  rw [outerShadingPackingLoss, Kakeya.factoringStep5OverlapConstant]
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by positivity)

open Classical in
/-- **A separated family of witness balls converts uniform local incidence into an average
multiplicity bound.**

If the shaded union of `(t, V)` is covered by the closed `m * r`-balls around an `r`-separated
finite set `S`, and if at every centre `z ∈ S` there are at least `L` indices `j ∈ t` whose shade
`(V j).shade` contains a ball of radius `r / 8` inside `Metric.ball z (2 * r)`, then the *average*
multiplicity `µ(t, V)` is at least `L` up to the dimensional loss
`ShadedBody.outerShadingPackingLoss n m`.

This is the general-shaded-family form of the `ρ`-tube estimate
`ShadedBody.rhoTubesOuterMultiplicityLoss`; nothing about the bodies enters beyond compactness of
their carriers, which is part of `ShadedBody`. -/
theorem le_multiplicity_of_local_balls (t : Finset κ) (V : κ → ShadedBody E)
    (S : Finset E) (r : NNReal) (L m : ℕ) (hr : 0 < r) (hL : 0 < L) (hm : 0 < m)
    (hS : S.Nonempty)
    (hsep : Metric.IsSeparated (r : ENNReal) (S : Set E))
    (hcover : iUnionShade t V ⊆ ⋃ z ∈ S, Metric.closedBall z ((m : ℝ) * (r : ℝ)))
    (hlocal : ∀ z ∈ S, ∃ J : Finset κ, J ⊆ t ∧ L ≤ J.card ∧
      ∀ j ∈ J, ∃ p : E,
        Metric.ball p ((r : ℝ) / 8) ⊆ (V j).shade ∩ Metric.ball z (2 * (r : ℝ))) :
    (L : ENNReal) ≤ (outerShadingPackingLoss (Module.finrank ℝ E) m : ENNReal) *
      multiplicity t V := by
  let n := Module.finrank ℝ E
  let v : ENNReal := volume (Metric.ball (0 : E) ((r : ℝ) / 8))
  let O : ENNReal := Kakeya.factoringStep5OverlapConstant n
  let W : Set E := iUnionShade t V
  have hv0 : v ≠ 0 := by
    dsimp only [v]
    simp only [InnerProductSpace.volume_ball]
    positivity
  have hvtop : v ≠ ⊤ := by
    dsimp only [v]
    simp only [InnerProductSpace.volume_ball]
    finiteness
  have hballm : ∀ z : E, volume (Metric.closedBall z ((m : ℝ) * (r : ℝ))) =
      (((8 * m) ^ n : ℕ) : ENNReal) * v := by
    intro z
    rw [show (m : ℝ) * (r : ℝ) = ((8 * m : ℕ) : ℝ) * ((r : ℝ) / 8) by
      norm_num [Nat.cast_mul]
      ring]
    rw [InnerProductSpace.volume_closedBall]
    simp only [v, InnerProductSpace.volume_ball]
    rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ ((8 * m : ℕ) : ℝ) by positivity)]
    norm_num [n, mul_pow]
    ring
  have hover : ∀ x : E,
      {z ∈ S | x ∈ Metric.ball z (2 * (r : ℝ))}.card ≤
        Kakeya.factoringStep5OverlapConstant n := by
    intro x
    let A : Finset E := {z ∈ S | x ∈ Metric.ball z (2 * (r : ℝ))}
    have hAS : (A : Set E) ⊆ (S : Set E) := by
      intro z hz
      exact (Finset.mem_filter.mp hz).1
    have hdist : ∀ z ∈ A, dist z x ≤ 2 * (r : ℝ) := by
      intro z hz
      exact le_of_lt (by simpa [Metric.mem_ball, dist_comm] using (Finset.mem_filter.mp hz).2)
    simpa only [A, Kakeya.factoringStep5OverlapConstant] using
      Metric.IsSeparated.card_le_pow_of_dist_le hr (hsep.subset hAS) hdist
  have hlocsum : ∀ z ∈ S, (L : ENNReal) * v ≤
      ∑ j ∈ t, volume ((V j).shade ∩ Metric.ball z (2 * (r : ℝ))) := by
    intro z hz
    obtain ⟨J, hJt, hLJ, hJ⟩ := hlocal z hz
    calc
      (L : ENNReal) * v ≤ (J.card : ENNReal) * v := by gcongr
      _ = ∑ j ∈ J, v := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ j ∈ J, volume ((V j).shade ∩ Metric.ball z (2 * (r : ℝ))) := by
        apply Finset.sum_le_sum
        intro j hj
        obtain ⟨p, hp⟩ := hJ j hj
        calc
          v = volume (Metric.ball p ((r : ℝ) / 8)) := by
            rw [MeasureTheory.Measure.addHaar_ball_center volume p ((r : ℝ) / 8)]
          _ ≤ volume ((V j).shade ∩ Metric.ball z (2 * (r : ℝ))) := measure_mono hp
      _ ≤ ∑ j ∈ t, volume ((V j).shade ∩ Metric.ball z (2 * (r : ℝ))) := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hJt (fun _ _ _ ↦ bot_le)
  have hsumlocal : (S.card : ENNReal) * ((L : ENNReal) * v) ≤
      O * ∑ j ∈ t, volume (V j).shade := by
    calc
      (S.card : ENNReal) * ((L : ENNReal) * v) = ∑ z ∈ S, (L : ENNReal) * v := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ z ∈ S, ∑ j ∈ t,
          volume ((V j).shade ∩ Metric.ball z (2 * (r : ℝ))) :=
        Finset.sum_le_sum fun z hz ↦ hlocsum z hz
      _ = ∑ j ∈ t, ∑ z ∈ S,
          volume ((V j).shade ∩ Metric.ball z (2 * (r : ℝ))) := by
        rw [Finset.sum_comm]
      _ ≤ ∑ j ∈ t, O * volume (V j).shade := by
        apply Finset.sum_le_sum
        intro j hj
        calc
          ∑ z ∈ S, volume ((V j).shade ∩ Metric.ball z (2 * (r : ℝ))) ≤
              O * volume (⋃ z ∈ S, (V j).shade ∩ Metric.ball z (2 * (r : ℝ))) := by
            apply MeasureTheory.sum_measure_le_mul_measure_biUnion_of_card_filter_le
            · intro z _
              exact (V j).measurableSet_shade.inter Metric.isOpen_ball.measurableSet
            · intro x
              have hc : {z ∈ S | x ∈ (V j).shade ∩ Metric.ball z (2 * (r : ℝ))}.card ≤
                  {z ∈ S | x ∈ Metric.ball z (2 * (r : ℝ))}.card := by
                apply Finset.card_le_card
                intro z hz
                exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz).1,
                  (Finset.mem_filter.mp hz).2.2⟩
              exact_mod_cast hc.trans (hover x)
          _ ≤ O * volume (V j).shade := by
            gcongr
            intro x hx
            obtain ⟨z, _, hx⟩ := Set.mem_iUnion₂.mp hx
            exact hx.1
      _ = O * ∑ j ∈ t, volume (V j).shade := by rw [Finset.mul_sum]
  have hWvol : volume W ≤ (S.card : ENNReal) * ((((8 * m) ^ n : ℕ) : ENNReal) * v) := by
    calc
      volume W ≤ volume (⋃ z ∈ S, Metric.closedBall z ((m : ℝ) * (r : ℝ))) := measure_mono hcover
      _ ≤ ∑ z ∈ S, volume (Metric.closedBall z ((m : ℝ) * (r : ℝ))) :=
        measure_biUnion_finset_le _ _
      _ = (S.card : ENNReal) * ((((8 * m) ^ n : ℕ) : ENNReal) * v) := by
        simp_rw [hballm]
        rw [Finset.sum_const, nsmul_eq_mul]
  have hcross : (L : ENNReal) * volume W ≤
      (outerShadingPackingLoss n m : ENNReal) * ∑ j ∈ t, volume (V j).shade := by
    calc
      (L : ENNReal) * volume W ≤
          (L : ENNReal) * ((S.card : ENNReal) * ((((8 * m) ^ n : ℕ) : ENNReal) * v)) := by gcongr
      _ = (((8 * m) ^ n : ℕ) : ENNReal) * ((S.card : ENNReal) * ((L : ENNReal) * v)) := by ring
      _ ≤ (((8 * m) ^ n : ℕ) : ENNReal) * (O * ∑ j ∈ t, volume (V j).shade) := by gcongr
      _ = (outerShadingPackingLoss n m : ENNReal) *
          ∑ j ∈ t, volume (V j).shade := by
        simp only [outerShadingPackingLoss, O]
        push_cast
        ring
  have hW0 : volume W ≠ 0 := by
    obtain ⟨z, hz⟩ := hS
    obtain ⟨J, hJt, hLJ, hJ⟩ := hlocal z hz
    obtain ⟨j, hj⟩ := J.nonempty_of_ne_empty (by
      intro hJe
      subst J
      simp at hLJ
      omega)
    obtain ⟨p, hp⟩ := hJ j hj
    apply ne_of_gt
    calc
      0 < v := pos_iff_ne_zero.mpr hv0
      _ = volume (Metric.ball p ((r : ℝ) / 8)) := by
        rw [MeasureTheory.Measure.addHaar_ball_center volume p ((r : ℝ) / 8)]
      _ ≤ volume W := measure_mono ((hp.trans Set.inter_subset_left).trans
        (Set.subset_iUnion₂_of_subset j (hJt hj) (Set.Subset.refl _)))
  have hWtop : volume W ≠ ⊤ := volume_iUnion_shade_ne_top t V
  rw [multiplicity_eq_div]
  calc
    (L : ENNReal) ≤
        ((outerShadingPackingLoss n m : ENNReal) *
          ∑ j ∈ t, volume (V j).shade) / volume W :=
      (ENNReal.le_div_iff_mul_le (Or.inl hW0) (Or.inl hWtop)).2 hcross
    _ = (outerShadingPackingLoss n m : ENNReal) *
        ((∑ j ∈ t, volume (V j).shade) / volume W) := mul_div_assoc _ _ _

end OuterPacking

end ShadedBody
