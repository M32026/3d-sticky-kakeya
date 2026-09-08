/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineEveryScale
public import Kakeya.MultiScaleFac.GapsKT

/-!
# The band at the genuine parent

`Kakeya.MultiScaleFac.le_maxDensity_nodesUnder_of_band` upgrades a density witness at **one**
coarse node of a level to a bound at **every** node of that level, at the cost of the band constant.
Row F3 reads it at the pair `(p, c)` — coarse level the genuine parent `p`, fine level a window
level `c` — which is exactly why the twin's field
`Kakeya.ML2Reduction.IsKatzTaoDividingWindowLevels.level_density_band` had to be stated at **all
pairs of levels**: the field at the window's own `a` alone would not reach `p`.

`le_maxDensity_nodesUnder_of_windowLevels` is that instantiation, with the twin's `Cstar` read as
the band constant (`Cstar = ↑C'` for a `C' : NNReal`, which the block's `Cstar ≤ δ^{-ν/20}` supplies
through `ENNReal.ne_top`).
-/

@[expose] public section

open MeasureTheory Tube
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} {δ : NNReal}

omit [Nontrivial E] in
open scoped Classical in
/-- **F3 — one witness at level `p` gives every level-`p` node**, through the twin's two-level band
at the pair `(p, c)`: if some level-`p` node `q` has
`X ≤ D · Δ_max(class image of q at c)`, then every level-`p` node `j` has
`X ≤ D · C' · Δ_max(𝒰.nodesUnder c p j)`. -/
theorem le_maxDensity_nodesUnder_of_windowLevels {s : Finset ι} {T : ι → Tube δ E} {Cu : NNReal}
    (𝒰 : Tube.UniformTubeSet s T (ssfGridLen δ) Cu) {Cstar : ENNReal} {η : ℕ → ℝ} {εd : ℝ}
    {N a b m : ℕ}
    (hwin : ML2Reduction.IsKatzTaoDividingWindowLevels 𝒰 Cstar η εd N a b m)
    {C' : NNReal} (hC' : Cstar = (C' : ENNReal))
    {p c : ℕ} (hpc : p ≤ c) (hc : c ≤ ssfGridLen δ) {X D : ENNReal}
    (hwit : ∃ q ∈ 𝒰.cover.indexSet p,
      X ≤ D * Kakeya.maxDensity
            ((coverClass s (𝒰.cover.assign p) q).image (𝒰.cover.assign c))
            (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)) :
    ∀ j ∈ 𝒰.cover.indexSet p,
      X ≤ D * (C' : ENNReal) * Kakeya.maxDensity (𝒰.nodesUnder c p j)
            (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) := by
  obtain ⟨Φ, hΦ⟩ := hwin.level_density_band
  have hp : p ≤ ssfGridLen δ := hpc.trans hc
  refine Kakeya.MultiScaleFac.le_maxDensity_nodesUnder_of_band 𝒰 hpc hc (Φ := Φ p c) (C' := C')
    (fun j hj => ?_) hwit
  obtain ⟨h1, h2⟩ := hΦ p hp c hc j hj
  exact ⟨h1, by rw [← hC']; exact h2⟩

end Kakeya.ML2Core

end
