/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib.Data.NNReal.Basic
public import Mathlib.Tactic.Positivity

/-!
# Constants of the bush separation lemma

The tolerance `Kakeya.bushSeparation.c` and the scale threshold `Kakeya.bushSeparation.δ`
below which the bush bound `Kakeya.bushCount` operates. They are isolated from the geometry
that consumes them, `Kakeya/Tube/CommonPoint.lean`, so that the *statement* of the bush bound
does not depend on its proof.
-/

@[expose] public section

namespace Kakeya

/-- The tolerance `c` of the bush separation lemma: two `δ`-tubes through a common point
whose direction, transverse and longitudinal parameters agree to within `c * δ`, `c * δ`
and `c` respectively overlap in more than half of their volume. Its value is `10 ^ (-2)`;
any smaller value also works, since decreasing it strengthens the hypotheses of that
lemma. The ambient dimension is `3` throughout. -/
noncomputable def bushSeparation.c : NNReal := 1 / 100

/-- The threshold below which `δ` must lie for the volume estimate of the bush separation
lemma to close. Its value is `1 / 32`; the value `1 / 4` would already suffice for the
volume comparison, and `1 / 32` is taken so that `Tube.nearly_parallel_sliding` applies as
it stands. This is the only source of the smallness restriction on `δ` in
`Kakeya.bushCount` and everything downstream of it. -/
noncomputable def bushSeparation.δ : NNReal := 1 / 32

lemma bushSeparation.δ_pos : 0 < bushSeparation.δ := by
  rw [bushSeparation.δ]; positivity

lemma bushSeparation.δ_le_one : bushSeparation.δ ≤ 1 := by
  rw [bushSeparation.δ, div_le_one (by positivity)]
  norm_num

end Kakeya
