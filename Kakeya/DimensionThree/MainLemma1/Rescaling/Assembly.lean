/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.OneSidedUniform
public import Kakeya.DimensionThree.MainLemma1.Rescaling.FineDilate

/-!
# Main Lemma 1, Case (ii): reduction to the `b`-tubes — the assembly

Split out of `Kakeya/DimensionThree/MainLemma1/Rescaling.lean`.
-/

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology

namespace Kakeya

universe u

namespace ml1Boot

section ReduceToTb

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! #### The assembly -/



/-! #### Folding the two ratios into the collapse step's free constant -/

/-- **The fine-loss constant handed to the collapse step** in the proof of
`Kakeya.ml1Boot.normalized_le_of_coarse_dilate`.

`Kakeya.ml1Boot.reduceToTb_collapse` reads its normalization constant `C` only as `C ²`, in its
hypotheses (b) and (d), and asks only `1 ≤ C`.  Two ratios therefore need not appear in that
lemma at all and are folded in here instead: the ambient volume ratio `M`, and the ratio
`C_F / C_T` between the Frostman budget constant a caller supplies and the density-transfer
constant `Kakeya.ml1Boot.densityTransfer.C` that the collapse step is rigid at.  Writing
`C₃(c) = Kakeya.ml1Boot.fineNormalizeDilate.C c` this is `C₃(c) √(M C_F / C_T)`, chosen so that
`4 C ² (2 C_T) = M · 4 C₃(c)² (2 C_F)` exactly, `C_T` being nonzero by
`Kakeya.ml1Boot.one_le_densityTransfer_C`.  At `C_F = C_T` it is `C₃(c) √M`, which is the
constant this proof used before the Frostman budget became a parameter.

The fold is exact and not an estimate, which is what keeps it leak-free: `C` occurs in (b) and
in (d) of the collapse step, the first a hypothesis this proof supplies and the second one it
consumes, so a strict inequality in either direction would have to be paid twice, in opposite
directions.  It is also why `Kakeya.ml1Boot.reduceToTb_collapse` needs no change: the two
ratios never reach it. -/
noncomputable abbrev normalizedCoarseDilate.foldedFineC (c CF M : NNReal) : NNReal :=
  fineNormalizeDilate.C c * NNReal.sqrt (M * (CF / densityTransfer.C))

/-- `Kakeya.ml1Boot.normalizedCoarseDilate.foldedFineC` meets the `1 ≤ C` side condition of
`Kakeya.ml1Boot.reduceToTb_collapse`.

Both hypotheses are used: `1 ≤ M` together with `C_T ≤ C_F` makes the radicand at least `1`, and
`Kakeya.ml1Boot.one_le_fineNormalizeDilate_C` bounds the other factor.  `1 ≤ C_F` alone would
**not** do — the radicand `M C_F / C_T` may then be smaller than `1`, and nothing bounds `C₃(c)`
below by `√C_T`.  That is why hypothesis (a) of
`Kakeya.ml1Boot.normalized_le_of_coarse_dilate` asks `C_T ≤ C_F` and not merely `1 ≤ C_F`; the
fine chain itself needs only `1 ≤ C_F`. -/
theorem normalizedCoarseDilate.one_le_foldedFineC (c : NNReal) {CF M : NNReal} (hM : 1 ≤ M)
    (hCF : densityTransfer.C ≤ CF) :
    (1 : NNReal) ≤ normalizedCoarseDilate.foldedFineC c CF M := by
  rw [normalizedCoarseDilate.foldedFineC]
  have hCT1 : (1 : NNReal) ≤ densityTransfer.C := one_le_densityTransfer_C
  have hCT_pos : 0 < densityTransfer.C := lt_of_lt_of_le zero_lt_one hCT1
  have hx : (1 : NNReal) ≤ CF / densityTransfer.C := by
    rw [le_div_iff₀ hCT_pos]
    simpa using hCF
  have hrad : (1 : NNReal) ≤ M * (CF / densityTransfer.C) := one_le_mul hM hx
  have hsqrt : (1 : NNReal) ≤ NNReal.sqrt (M * (CF / densityTransfer.C)) :=
    (NNReal.one_le_sqrt).2 hrad
  exact one_le_mul (one_le_fineNormalizeDilate_C c) hsqrt

/-- **The fold is exact on the fine bound.**  The prefactor of
`Kakeya.ml1Boot.reduceToTb_fine_factor_dilate`, volume ratio included, is literally the fine
prefactor `4 C ² (2 C_T)` of hypothesis (b) of `Kakeya.ml1Boot.reduceToTb_collapse` at
`C = Kakeya.ml1Boot.normalizedCoarseDilate.foldedFineC c CF M`.

No hypothesis is needed: `Kakeya.NNReal.sq_sqrt` removes the root and the cancellation
`(C_F / C_T) C_T = C_F` needs only `C_T ≠ 0`, which
`Kakeya.ml1Boot.one_le_densityTransfer_C` gives. -/
theorem normalizedCoarseDilate.foldedFineC_fineBound (c CF M : NNReal) :
    (M : ENNReal) * (reduceToTbFineBoundDilate.C c CF : ENNReal)
      = 4 * ((normalizedCoarseDilate.foldedFineC c CF M : NNReal) : ENNReal) ^ 2
        * (2 * (densityTransfer.C : ENNReal)) := by
  have hC0 : (reduceToTbFineBoundDilate.C c CF : ENNReal)
      = 4 * (fineNormalizeDilate.C c : ENNReal) ^ 2 * (2 * (CF : ENNReal)) := by
    change (4 * fineNormalizeDilate.C c ^ 2 * (2 * CF) : ENNReal)
        = 4 * (fineNormalizeDilate.C c : ENNReal) ^ 2 * (2 * (CF : ENNReal))
    rfl
  have hCT : densityTransfer.C ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one one_le_densityTransfer_C)
  have hcore : (normalizedCoarseDilate.foldedFineC c CF M) ^ 2 * densityTransfer.C
      = fineNormalizeDilate.C c ^ 2 * M * CF := by
    unfold normalizedCoarseDilate.foldedFineC
    rw [mul_pow, NNReal.sq_sqrt]
    field_simp [hCT]
  have hcoreE :
      ((normalizedCoarseDilate.foldedFineC c CF M : NNReal) : ENNReal) ^ 2
        * (densityTransfer.C : ENNReal)
      = (fineNormalizeDilate.C c : ENNReal) ^ 2 * (M : ENNReal) * (CF : ENNReal) := by
    exact_mod_cast hcore
  rw [hC0]
  calc
    (M : ENNReal) * (4 * (fineNormalizeDilate.C c : ENNReal) ^ 2 * (2 * (CF : ENNReal)))
        = 4 * 2
            * ((fineNormalizeDilate.C c : ENNReal) ^ 2 * (M : ENNReal) * (CF : ENNReal)) := by
          ring
    _ = 4 * 2
            * (((normalizedCoarseDilate.foldedFineC c CF M : NNReal) : ENNReal) ^ 2
                * (densityTransfer.C : ENNReal)) := by
          rw [← hcoreE]
    _ = 4 * ((normalizedCoarseDilate.foldedFineC c CF M : NNReal) : ENNReal) ^ 2
            * (2 * (densityTransfer.C : ENNReal)) := by
          ring

/-- **The fold is exact on the prefactor budget.**  The left side is the prefactor of
hypothesis (d) of `Kakeya.ml1Boot.reduceToTb_collapse` at
`C = Kakeya.ml1Boot.normalizedCoarseDilate.foldedFineC c CF M` and `C_u ² = 2`; the right side is
the prefactor of hypothesis (d) of `Kakeya.ml1Boot.normalized_le_of_coarse_dilate`, read at the
caller's `C_F`.  They are equal, so the caller's budget obligation is exactly the collapse
step's and neither side carries slack. -/
theorem normalizedCoarseDilate.foldedFineC_absorb (Cc c CF M : NNReal) :
    4 * (Cc : ENNReal) * ((normalizedCoarseDilate.foldedFineC c CF M : NNReal) : ENNReal) ^ 2
        * 2 * (2 * (densityTransfer.C : ENNReal))
      = 4 * (Cc : ENNReal) * ((fineNormalizeDilate.C c : ENNReal) ^ 2 * (M : ENNReal)) * 2
        * (2 * (CF : ENNReal)) := by
  have hCT : densityTransfer.C ≠ 0 := by
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one one_le_densityTransfer_C)
  have hcore : (normalizedCoarseDilate.foldedFineC c CF M) ^ 2 * densityTransfer.C
      = fineNormalizeDilate.C c ^ 2 * M * CF := by
    unfold normalizedCoarseDilate.foldedFineC
    rw [mul_pow, NNReal.sq_sqrt]
    field_simp [hCT]
  have hcoreE :
      ((normalizedCoarseDilate.foldedFineC c CF M : NNReal) : ENNReal) ^ 2
        * (densityTransfer.C : ENNReal)
      = (fineNormalizeDilate.C c : ENNReal) ^ 2 * (M : ENNReal) * (CF : ENNReal) := by
    exact_mod_cast hcore
  calc
    4 * (Cc : ENNReal) * ((normalizedCoarseDilate.foldedFineC c CF M : NNReal) : ENNReal) ^ 2
        * 2 * (2 * (densityTransfer.C : ENNReal))
        = 4 * (Cc : ENNReal) * 2 * 2
            * (((normalizedCoarseDilate.foldedFineC c CF M : NNReal) : ENNReal) ^ 2
                * (densityTransfer.C : ENNReal)) := by
          ring
    _ = 4 * (Cc : ENNReal) * 2 * 2
            * ((fineNormalizeDilate.C c : ENNReal) ^ 2 * (M : ENNReal) * (CF : ENNReal)) := by
          rw [hcoreE]
    _ = 4 * (Cc : ENNReal) * ((fineNormalizeDilate.C c : ENNReal) ^ 2 * (M : ENNReal)) * 2
            * (2 * (CF : ENNReal)) := by
          ring



end ReduceToTb

end ml1Boot

end Kakeya
