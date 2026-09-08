/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.WangZahl.TopLevelWrapper

/-!
# What failing the Frostman branch of `FrostmanOrDone` actually buys

The obligation `Kakeya.WangZahl.frostmanOrDone_zero` is a dichotomy whose second branch is
`delta^{-eta}`-Frostman control in the unit ball, under a hypothesis
(`ConvexSpaceBody.IsKatzTao` at the *same* constant `delta^{-eta}`) that bounds every
`densityIn` by that constant.  The two interact: a family cannot both saturate the Katz-Tao
bound on some convex subset and be spread out over the ambient body.

`Kakeya.carrier_mass_lt_of_not_frostmanIn` is that interaction, and it is the only
unconditional consequence the non-Frostman branch has: it forces the family to have total
carrier mass strictly below the volume of the ambient body.

Source: `blueprint/src/WZ2/250224e_K3.tex`, Definition `KatzTaoAndFrostmanTubesDefn` and
Definition `KatzTaoAndFrostmanTubesDefn'` (line 935 ff.), where the Katz-Tao and Frostman
Wolff constants are introduced as the two non-clustering conditions of the same family.
-/

@[expose] public section

open MeasureTheory Metric

namespace Kakeya

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- If a family is Katz-Tao with error `C` and is **not** `C`-Frostman in an ambient convex
body `B` that contains it, then its total carrier mass is strictly less than `|B|`.

Indeed, failure of the Frostman property produces a convex `K ≤ B` with
`C * densityIn s W B < densityIn s W K`, while the Katz-Tao hypothesis caps the right-hand
side by `C`; cancelling `C` gives `densityIn s W B < 1`, which is the claim. -/
theorem carrier_mass_lt_of_not_frostmanIn
    {ι : Type*} {s : Finset ι} {W : ι → ConvexSpaceBody E} {B : ConvexSpaceBody E}
    {C : ENNReal} (hB0 : volume B.carrier ≠ 0) (hBtop : volume B.carrier ≠ ⊤)
    (hle : ∀ i ∈ s, W i ≤ B)
    (hKT : ConvexSpaceBody.IsKatzTao s W C)
    (hF : ¬ ConvexSpaceBody.IsFrostmanIn s W B C) :
    ∑ i ∈ s, volume (W i).carrier < volume B.carrier := by
  rw [ConvexSpaceBody.IsFrostmanIn] at hF
  push Not at hF
  obtain ⟨K, hKB, hlt⟩ := hF
  have h1 : densityIn s W K ≤ C := (le_maxDensity s W K).trans hKT
  have hCC : C * densityIn s W B < C := lt_of_lt_of_le hlt h1
  have hlt1 : densityIn s W B < 1 := by
    by_contra hcon
    push Not at hcon
    exact absurd hCC (not_lt.mpr (by
      calc C = C * 1 := (mul_one C).symm
        _ ≤ C * densityIn s W B := by gcongr))
  rw [densityIn_of_all_le hle] at hlt1
  have := (ENNReal.div_lt_iff (Or.inl hB0) (Or.inl hBtop)).mp hlt1
  simpa using this

end Kakeya

namespace Kakeya.WangZahl

open Kakeya

/-- The specialisation used by the dichotomy `Kakeya.WangZahl.FrostmanOrDone`: for a family of
shaded `delta`-tubes inside the closed unit ball, satisfying the Katz-Tao hypothesis at
`delta^{-eta}`, failure of the `delta^{-eta}`-Frostman conclusion forces the total carrier mass
to be strictly below `|B(0,1)|`.

This is the whole unconditional content of the non-Frostman branch, and it is why that branch
cannot be closed by pigeonholing on the given data alone: it constrains the *mass* of the
family but says nothing about the multiplicity `∑ |Y i| / |⋃ Y i|` that the first branch
of the dichotomy bounds. -/
theorem carrier_mass_lt_of_not_frostmanIn_unitBall
    {ι : Type*} {delta : NNReal} {s : Finset ι} (T : ι → ShadedTube delta Space3)
    {C : ENNReal}
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1)
    (hKT : ConvexSpaceBody.IsKatzTao s (fun i => (T i).toConvexSpaceBody) C)
    (hF : ¬ ConvexSpaceBody.IsFrostmanIn s (fun i => (T i).toConvexSpaceBody)
      (ConvexSpaceBody.closedUnitBall (E := Space3)) C) :
    ∑ i ∈ s, volume (T i).carrier < volume (Metric.closedBall (0 : Space3) 1) :=
  carrier_mass_lt_of_not_frostmanIn
    (measure_closedBall_pos volume (0 : Space3) one_pos).ne'
    measure_closedBall_lt_top.ne hball hKT hF

end Kakeya.WangZahl

#print axioms Kakeya.carrier_mass_lt_of_not_frostmanIn
#print axioms Kakeya.WangZahl.carrier_mass_lt_of_not_frostmanIn_unitBall
