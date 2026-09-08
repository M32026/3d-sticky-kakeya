/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.Rescaling.CoarseDensity

/-!
# Main Lemma 1, coarse endgame: the caught mass at the dilated `b`-tube

The Frostman-consequence half of the coarse-endgame seam of
`Kakeya.ml1Boot.multTildeT_of_planksClose`.  Blueprint source
`GWZAdapted/section8_endgame.tex`.
-/

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology

namespace Kakeya

namespace ml1Boot

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

end ml1Boot

end Kakeya
