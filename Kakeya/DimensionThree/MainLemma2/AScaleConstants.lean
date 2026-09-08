/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Covers
public import Kakeya.Multiplicity
public import Kakeya.Tube.Basic
public import Kakeya.Tube.IntersectionVolume

/-!
# The comparison constants of the scale-`r` layer of Main Lemma 2

The constants of blueprint `def:ml2tubeVolumeRatioConstant`, `def:ml2DeltamaxScaleAConstant`,
`def:ml2aScaleVolumeConstant` and `def:ml2aScaleBallConstant`, together with the accumulated
constant `C_⋆` of blueprint `def:ml2aScaleDataThreshold` that they combine into.

They are collected in a file of their own, upstream of
`Kakeya.DimensionThree.MainLemma2.VeryNotSticky`, for one reason: the clause of Configuration
`hyp:ml2scale` that absorbs `C_⋆` is recorded as the field
`Kakeya.VeryNotSticky.aScaleData_absorb` of the configuration, so `C_⋆` has to be nameable
where that structure is declared. None of them mentions a configuration, a scale `δ`, or a
tube family; each is a function of the ambient dimension and of the two uniformity constants
`C₀, D₀` of blueprint `uniformSetOfTubes` alone.
-/

@[expose] public section

namespace ShadedBody

/-- The fixed normalization used by the provisional Section 9 coarse-family interface.

The proved Section 5 theorem now exposes the scale-dependent constant
`shadingMultiplicityEstimateForRhoTubesDilate.C`; it no longer provides the former compatibility
projection under this name. Section 9 still states its unproved coarse-family residue with the
normalized constant `1`, so keep that local interface explicit until the residue is connected to
the proved dilated theorem. -/
noncomputable def shadingMultiplicityEstimateForRhoTubes.C : NNReal := 1

end ShadedBody

namespace Kakeya

open MeasureTheory


/-- **Constant in Lemma `lem:ml2tubeVolumeRatio`** (blueprint
`def:ml2tubeVolumeRatioConstant`).

The ratio `c_n / C_n` of the two dimensional constants of `Tube.le_volume` and
`Tube.volume_le`. In the ambient dimension `n = 3` of Section 9 it evaluates to
`(4π/9) / 16 = π / 36 ∈ (0, 1]`.

It is an absolute constant: it depends only on the ambient dimension, and in particular not
on `δ`, on `a`, or on the tubes. -/
noncomputable def tubeVolumeRatioConstant (n : ℕ) : NNReal :=
  Tube.le_volume.c n / Tube.volume_le.C n

/-- The constant of blueprint `def:ml2tubeVolumeRatioConstant` is positive. -/
theorem tubeVolumeRatioConstant_pos (n : ℕ) : 0 < tubeVolumeRatioConstant n := by
  unfold tubeVolumeRatioConstant
  exact div_pos (Tube.le_volume.c_pos n) (Tube.volume_le.C_pos n)

/-- In dimension `3` the tube volume ratio `c₃ / C₃ = (4π/9) / 16 = π/36` is at most `1`. -/
theorem tubeVolumeRatioConstant_three_le_one : tubeVolumeRatioConstant 3 ≤ 1 := by
  rw [← NNReal.coe_le_coe, NNReal.coe_one]
  unfold tubeVolumeRatioConstant
  rw [Tube.le_volume.c]
  simp only [NNReal.coe_div, NNReal.coe_pow, NNReal.coe_ofNat, Nat.reduceAdd]
  norm_num
  change Real.sqrt Real.pi ^ 3 / Real.Gamma (5 / 2) / 3 / 16 ≤ 1
  have hgamma : Real.Gamma (5 / 2) = (3 / 4) * Real.sqrt Real.pi := by
    rw [show (5 : ℝ) / 2 = (3 : ℝ) / 2 + 1 by norm_num]
    rw [Real.Gamma_add_one (by norm_num : (3 : ℝ) / 2 ≠ 0)]
    rw [show (3 : ℝ) / 2 = (1 : ℝ) / 2 + 1 by norm_num]
    rw [Real.Gamma_add_one (by norm_num : (1 : ℝ) / 2 ≠ 0)]
    rw [Real.Gamma_one_half_eq]
    ring
  rw [hgamma]
  have hs_pos : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hsneg : Real.sqrt Real.pi ≠ 0 := hs_pos.ne'
  have hsq : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
  field_simp [hsneg]
  rw [hsq]
  nlinarith [Real.pi_le_four]

/-- **Constant in Lemma `lem:ml2DeltamaxScaleA`** (blueprint
`def:ml2DeltamaxScaleAConstant`).

`C₀² D₀ / c` with `C₀`, `D₀` the branching and overlap constants of blueprint
`uniformSetOfTubes` and `c = Kakeya.tubeVolumeRatioConstant 3 = π/36`; in dimension `3` this
is `(36/π) C₀² D₀ ≥ 1`.

It depends only on the ambient dimension and on the two uniformity constants of `𝕋` at the
scale `a`; in particular not on `δ`, not on `a`, and not on the convex body quantified over
in blueprint `def:Deltamax`. -/
noncomputable def deltamaxScaleAConstant (C₀ D₀ : NNReal) : NNReal :=
  C₀ ^ 2 * D₀ / tubeVolumeRatioConstant 3

/-- **Constant in Lemma `lem:ml2aScaleVolume`** (blueprint `def:ml2aScaleVolumeConstant`).

`C₀² C_{lem:ml2DeltamaxScaleA}(C₀, D₀) / c`, which in dimension `3` is `(36/π)² C₀⁴ D₀ ≥ 1`.
The three factors are the two-sided branching comparison of blueprint `lem:ml2uniformScaleA`,
the two-scale multiplicity bound of blueprint `lem:ml2DeltamaxScaleA`, and one further
application of the tube-volume comparison of blueprint `lem:ml2tubeVolumeRatio`. Blueprint
`genKKT` contributes no multiplicative constant at all. -/
noncomputable def aScaleVolumeConstant (C₀ D₀ : NNReal) : NNReal :=
  C₀ ^ 2 * deltamaxScaleAConstant C₀ D₀ / tubeVolumeRatioConstant 3

/-- The constant of blueprint `def:ml2DeltamaxScaleAConstant` is at least `1`, which is what
lets it survive being raised to a power in `[0, 1]` in
`Kakeya.VeryNotSticky.coarseVolumeLower`. -/
theorem one_le_deltamaxScaleAConstant {C₀ D₀ : NNReal} (hC₀ : 1 ≤ C₀) (hD₀ : 1 ≤ D₀) :
    1 ≤ deltamaxScaleAConstant C₀ D₀ := by
  rw [deltamaxScaleAConstant]
  rw [le_div_iff₀ (tubeVolumeRatioConstant_pos 3)]
  have hC2 : 1 ≤ C₀ ^ 2 := by
    simpa [pow_two] using one_le_mul_of_one_le_of_one_le hC₀ hC₀
  have hCD : 1 ≤ C₀ ^ 2 * D₀ := one_le_mul_of_one_le_of_one_le hC2 hD₀
  simpa [one_mul] using tubeVolumeRatioConstant_three_le_one.trans hCD

/-- The constant of blueprint `def:ml2aScaleVolumeConstant` is at least `1`, for the reason
that `Kakeya.one_le_deltamaxScaleAConstant` is: its numerator is at least `1` and its
denominator at most `1`. -/
theorem one_le_aScaleVolumeConstant {C₀ D₀ : NNReal} (hC₀ : 1 ≤ C₀) (hD₀ : 1 ≤ D₀) :
    1 ≤ aScaleVolumeConstant C₀ D₀ := by
  rw [aScaleVolumeConstant]
  rw [le_div_iff₀ (tubeVolumeRatioConstant_pos 3)]
  have hC2 : 1 ≤ C₀ ^ 2 := by
    simpa [pow_two] using one_le_mul_of_one_le_of_one_le hC₀ hC₀
  have hCD : 1 ≤ C₀ ^ 2 * deltamaxScaleAConstant C₀ D₀ :=
    one_le_mul_of_one_le_of_one_le hC2 (one_le_deltamaxScaleAConstant hC₀ hD₀)
  simpa [one_mul] using tubeVolumeRatioConstant_three_le_one.trans hCD

/-- The defining relation between the two constants, in the division-free form in which
`Kakeya.VeryNotSticky.coarseVolumeLower` consumes it. -/
theorem aScaleVolumeConstant_mul_tubeVolumeRatioConstant (C₀ D₀ : NNReal) :
    aScaleVolumeConstant C₀ D₀ * tubeVolumeRatioConstant 3 =
      C₀ ^ 2 * deltamaxScaleAConstant C₀ D₀ := by
  unfold aScaleVolumeConstant
  exact div_mul_cancel₀ _ (tubeVolumeRatioConstant_pos 3).ne'

/-- **Constant in Lemma `lem:ml2aScaleBall`** (blueprint `def:ml2aScaleBallConstant`).

`5 ^ 3 · Cb`, the factor `5 ^ 3` being the covering number of blueprint
`lem:ballCoverHalfRadius` spent by the re-centring `Kakeya.exists_mem_volume_inter_ball_recentre`,
and `Cb` the constant of blueprint `boundVolumeAcrossTwoScales`.

The blueprint presents this as a definition *by choice*, because it reads the `⪆` of
`boundVolumeAcrossTwoScales` through blueprint `def:leApprox`, which supplies its constant
only existentially. The Lean interface
`Kakeya.ShadedBody.shadingMultiplicityEstimateForRhoTubes` instead carries the *fixed*
constant `Kakeya.ShadedBody.shadingMultiplicityEstimateForRhoTubes.C`, so here the constant is
a formula in it, and `Kakeya.aScaleDataConstant` reads it at that value. -/
noncomputable def aScaleBallConstant (Cb : NNReal) : NNReal :=
  (separatedNetCoverConstant 3 : NNReal) * Cb

/-- **The accumulated comparison constant of the scale-`r` layer** (blueprint
`def:ml2aScaleDataThreshold`, the constant `C_⋆` there).

`C_⋆(C₀, D₀) = max(C_{lem:ml2aScaleBall}, C_{lem:ml2aScaleVolume}(C₀, D₀))`, the two
comparison constants that the proof of blueprint `lem:ml2aScaleData` accumulates: the ball
constant of blueprint `def:ml2aScaleBallConstant`, read at the fixed constant that
`Kakeya.ShadedBody.shadingMultiplicityEstimateForRhoTubes` carries, and the volume constant
of blueprint `def:ml2aScaleVolumeConstant` at the uniformity constants of the configuration.

The ball half is a closed term rather than a free parameter because the Lean form of the
section-5 interface carries a fixed constant; that is what makes `C_⋆` a function of `C₀` and
`D₀` alone, and hence a quantity that can be fixed before the scale `δ`. -/
noncomputable def aScaleDataConstant (C₀ D₀ : NNReal) : NNReal :=
  max (aScaleBallConstant (max 1 (Tube.dilateFullness.C 3)))
    (aScaleVolumeConstant C₀ D₀)

/-- `1 ≤ C_⋆(C₀, D₀)`: the accumulated constant is a comparison constant. -/
theorem one_le_aScaleDataConstant {C₀ D₀ : NNReal} (hC₀ : 1 ≤ C₀) (hD₀ : 1 ≤ D₀) :
    1 ≤ aScaleDataConstant C₀ D₀ :=
  le_max_of_le_right (one_le_aScaleVolumeConstant hC₀ hD₀)

/-- The ball constant of blueprint `def:ml2aScaleBallConstant`, at the constant carried by
`Kakeya.ShadedBody.shadingMultiplicityEstimateForRhoTubes`, is one of the two constants
accumulated by `Kakeya.aScaleDataConstant`. -/
theorem aScaleBallConstant_le_aScaleDataConstant (C₀ D₀ : NNReal) :
    aScaleBallConstant (max 1 (Tube.dilateFullness.C 3)) ≤
      aScaleDataConstant C₀ D₀ :=
  le_max_left _ _

/-- The volume constant of blueprint `def:ml2aScaleVolumeConstant` is the other constant
accumulated by `Kakeya.aScaleDataConstant`. -/
theorem aScaleVolumeConstant_le_aScaleDataConstant (C₀ D₀ : NNReal) :
    aScaleVolumeConstant C₀ D₀ ≤ aScaleDataConstant C₀ D₀ :=
  le_max_right _ _

end Kakeya
