/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.Geometry
public import Kakeya.DimensionThree.MainLemma2.VeryNotSticky

/-!
# Named constants for density inside a body

This module defines `Kakeya.VeryNotSticky.denseInBodyΘ` and
`Kakeya.VeryNotSticky.denseInBodyC₁`, together with their lower bounds by
`1`. Both `ThickCase.lean` and `DenseInBodyConstants.lean` use these
names, allowing density thresholds to be stated at explicit witnesses.

The definitions require `Plank.windowRadius` from
`DimensionThree/Plank/Geometry.lean` and the `VeryNotSticky` namespace.
-/

@[expose] public section

open MeasureTheory Metric
open scoped ENNReal NNReal

namespace Kakeya.VeryNotSticky

open Kakeya

universe u

noncomputable section

/-! ### The two constants -/

/-- **The `Θ` of `Kakeya.VeryNotSticky.exists_denseInBody`, named**: `Θ' = CP Θ₀ C_bias²`.

The whole bias contribution, hence the whole `δ`-dependence of the pair, is here. `C_bias` is
the field `Kakeya.VeryNotSticky.BallData.Cbias` and enters squared because the correction that
made the bias explicit in `ThickPlankPresentation.nonconcentration` made it explicit in
`frostman` as well. -/
def denseInBodyΘ (CP Θ₀ Cbias : NNReal) : NNReal := CP * Θ₀ * Cbias * Cbias

/-- **The `C₁` of `Kakeya.VeryNotSticky.exists_denseInBody`, named**:
`C₁' = max 1 (64 |B̄(0, Plank.windowRadius)| CP^{ν+3β} CP)`.

`δ`-free: `CP` is the plank comparison constant of blueprint `lem:ml2thickPlank`, `ν` and `β`
are exponents, and the ball is the window the whole presentation lives in. The `max` is what
supplies `1 ≤ C₁'` without a numerical lower bound for the ball volume; it costs nothing, the
constant appearing only on the large side of an inequality. -/
def denseInBodyC₁ (CP : NNReal) (ν β : ℝ) : NNReal :=
  max 1 (64 * (volume (closedBall (0 : EuclideanSpace ℝ (Fin 3))
      Plank.windowRadius)).toNNReal * CP ^ (ν + 3 * β) * CP)

/-- `1 ≤ Θ'`, as `Kakeya.VeryNotSticky.DenseInBodyRaw`'s consumers require. -/
theorem one_le_denseInBodyΘ {CP Θ₀ Cbias : NNReal} (hCP : 1 ≤ CP) (hΘ₀ : 1 ≤ Θ₀)
    (hCbias : 1 ≤ Cbias) : 1 ≤ denseInBodyΘ CP Θ₀ Cbias :=
  one_le_mul (one_le_mul (one_le_mul hCP hΘ₀) hCbias) hCbias

/-- `1 ≤ C₁'`, by the `max`. -/
theorem one_le_denseInBodyC₁ (CP : NNReal) (ν β : ℝ) : 1 ≤ denseInBodyC₁ CP ν β :=
  le_max_left _ _

end

end Kakeya.VeryNotSticky
