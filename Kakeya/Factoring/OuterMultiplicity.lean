/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Factoring.Step5
public import Kakeya.Mathlib.MeasureTheory.BoundedOverlap

/-! # From local witness balls to average outer multiplicity

This is the application-independent local-to-global argument used in Item 5 of GWZ Proposition
5.1.  It was first proved for Lemma 5.11; the condition here only refers to shaded bodies.
-/

@[expose] public section

open MeasureTheory Convexity Kakeya
open scoped NNReal ENNReal

namespace ShadedBody

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {κ : Type*}

/-- **Constant in `outerMultiplicity_lower_of_local_balls`**.  The factor `40 ^ n` is the
volume ratio between a covering ball of radius `5 r` and a witness ball of radius `r / 8`; the
other factor is the overlap bound for `r`-separated centres. -/
def outerMultiplicityFromLocalBalls.C (n : ℕ) : NNReal :=
  Kakeya.factoringStep5OverlapConstant n * 40 ^ n

open Classical in
/-- A separated family of witness balls converts uniform local outer incidence into an average
outer multiplicity bound. -/
theorem outerMultiplicity_lower_of_local_balls (t : Finset κ) (V : κ → ShadedBody E)
    (S : Finset E) (r : NNReal) (L : ℕ) (hr : 0 < r) (hL : 0 < L) (hS : S.Nonempty)
    (hsep : Metric.IsSeparated (r : ENNReal) (S : Set E))
    (hcover : iUnionShade t V ⊆ ⋃ z ∈ S, Metric.closedBall z (5 * (r : ℝ)))
    (hlocal : ∀ z ∈ S, ∃ J : Finset κ, J ⊆ t ∧ L ≤ J.card ∧
      ∀ j ∈ J, ∃ p : E,
        Metric.ball p ((r : ℝ) / 8) ⊆ (V j).shade ∩ Metric.ball z (2 * (r : ℝ))) :
    (L : ENNReal) ≤ (outerMultiplicityFromLocalBalls.C (Module.finrank ℝ E) : ENNReal) *
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
  have hball5 : ∀ z : E, volume (Metric.closedBall z (5 * (r : ℝ))) =
      (40 ^ n : ℕ) * v := by
    intro z
    rw [show 5 * (r : ℝ) = 40 * ((r : ℝ) / 8) by ring]
    rw [InnerProductSpace.volume_closedBall]
    simp only [v, InnerProductSpace.volume_ball]
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 40)]
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
                exact Finset.mem_filter.mpr ⟨( Finset.mem_filter.mp hz).1,
                  (Finset.mem_filter.mp hz).2.2⟩
              exact_mod_cast hc.trans (hover x)
          _ ≤ O * volume (V j).shade := by
            gcongr
            intro x hx
            obtain ⟨z, _, hx⟩ := Set.mem_iUnion₂.mp hx
            exact hx.1
      _ = O * ∑ j ∈ t, volume (V j).shade := by rw [Finset.mul_sum]
  have hWvol : volume W ≤ (S.card : ENNReal) * ((40 ^ n : ℕ) * v) := by
    calc
      volume W ≤ volume (⋃ z ∈ S, Metric.closedBall z (5 * (r : ℝ))) := measure_mono hcover
      _ ≤ ∑ z ∈ S, volume (Metric.closedBall z (5 * (r : ℝ))) :=
        measure_biUnion_finset_le _ _
      _ = (S.card : ENNReal) * ((40 ^ n : ℕ) * v) := by
        simp_rw [hball5]
        rw [Finset.sum_const, nsmul_eq_mul]
  have hcross : (L : ENNReal) * volume W ≤
      (outerMultiplicityFromLocalBalls.C n : ENNReal) * ∑ j ∈ t, volume (V j).shade := by
    calc
      (L : ENNReal) * volume W ≤
          (L : ENNReal) * ((S.card : ENNReal) * ((40 ^ n : ℕ) * v)) := by gcongr
      _ = (40 ^ n : ℕ) * ((S.card : ENNReal) * ((L : ENNReal) * v)) := by ring
      _ ≤ (40 ^ n : ℕ) * (O * ∑ j ∈ t, volume (V j).shade) := by gcongr
      _ = (outerMultiplicityFromLocalBalls.C n : ENNReal) *
          ∑ j ∈ t, volume (V j).shade := by
        simp only [outerMultiplicityFromLocalBalls.C, O]
        push_cast
        ring
  have hW0 : volume W ≠ 0 := by
    obtain ⟨z, hz⟩ := hS
    obtain ⟨J, hJt, hLJ, hJ⟩ := hlocal z hz
    obtain ⟨j, hj⟩ : J.Nonempty := Finset.nonempty_of_ne_empty (by
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
        ((outerMultiplicityFromLocalBalls.C n : ENNReal) *
          ∑ j ∈ t, volume (V j).shade) / volume W :=
      (ENNReal.le_div_iff_mul_le (Or.inl hW0) (Or.inl hWtop)).2 hcross
    _ = (outerMultiplicityFromLocalBalls.C n : ENNReal) *
        ((∑ j ∈ t, volume (V j).shade) / volume W) := mul_div_assoc _ _ _

end ShadedBody
