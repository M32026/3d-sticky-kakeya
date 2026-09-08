/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorShapeRoute
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineDichotomyInputs

/-!
# Does the trichotomy payload have a producer from the dividing-scales dichotomy?  **No** — and
here are the three rows it does not supply

  The question: `Kakeya.ML2Core.FloorDataAtTrichotomy` is
`∃ a b m, (F) ∨ (D)`, and the twin — conjunct 1 of `hwinfloor`, with no producer as an unconditional
`(F)` claim — *is* produced by the dividing-scales machinery.  Does the trichotomy therefore close?

The tree-wide producer is `Kakeya.ML2Reduction.exists_dichotomy_katzTaoDividingWindow`
(`Reduction/SpineEveryScale.lean:304`), in its shaded form
`Kakeya.ML2Inputs.DividingScalesOutputLevels` (`Reduction/SpineDichotomyInputs.lean:481`), which the
site already reaches (`Reduction/SpineRungWiring.lean`).  Its output is

```
∃ u ⊆ s, ∃ u' ⊆ u, ∃ W, u'.Nonempty ∧ (same tubes) ∧ (sub-shading) ∧
  (CARDINALITY loss)  s.card ≤ δ^{-(η₀+α)} · totalLoss · u'.card  ∧
  (mass loss ON u')   ∑_{u'} |V| ≤ (log₂ #u + 1)^{2L+2} · ∑_{u'} |W|  ∧ … ∧
  ∃ 𝒲 : ShadedUniformTubeSet u' W (ssfGridLen δ) (max C 4),
    𝒲.tubeUniform.IsKatzTaoAtEveryScale … ∨ ∃ a b m, IsKatzTaoDividingWindowLevels 𝒲.tubeUniform …
```

**Answer: no.**  Three rows are missing, and — the point worth stating — **none of them is the `Φ`
cross-node homogeneity** : `level_density_band` is a *field of* the twin, and the producer
already returns the twin, so that cost is paid where  said it was, by
`exists_dichotomy_katzTaoDividingWindow` and not by the floor.

| # | missing row | family / shading / level pair | owner |
|---|---|---|---|
| **S1** | the twin arrives on `𝒲.tubeUniform`, a hierarchy the producer **constructs** on `u'` with family `W` and constant `max C 4`.  `(F)` needs it on `refinedHierarchy ((𝒰.restrictOccupied hS hh).retube …) hS' hhom' hW`, whose cover is the **ambient** `𝒰.cover` restricted.  Nothing in the output relates the two covers, and `u' = S'` is not asserted either. | family `u'` vs `S'`; shading `W` both sides; every level pair `(a,b)` and `(p,c)` | the dividing-scales interface, not the floor |
| **S2** | the other alternative is `IsKatzTaoAtEveryScale`, **not** a potential drop.  `Kakeya.ML2Core.DefectBranchAt` needs `Φ_h(𝕊*) ≤ Φ_h(𝕊') − 1`, and the output mentions `potential` nowhere.  A subfamily alone never supplies it (`Kakeya.ML2Core.no_potential_drop_self`). | family `u'` ⊆ `s`; the potential is a function of the family alone | the `(D)` route (`R8`), not the dividing scales |
| **S3** | the family loss is in **cardinality**; `IsShadedRefinementOf` needs shaded **mass** over `S` on the left (`∑_{S}|Z| ≤ Λf ∑_{S'}|W|`).  The producer's mass row is `∑_{u'}|V| ≤ … ∑_{u'}|W|` — the *shading* loss on a fixed family, not the *family* loss. | numerator `S` vs `u'`; shadings `Z` and `W` | `R0′` / the mass-weighted pigeonhole port  |

`S1`'s missing row is nameable exactly, because the tree already has its analogue for the *other*
alternative: `Kakeya.ML2Reduction.isKatzTaoAtEveryScale_of_cover_eq` transports
`IsKatzTaoAtEveryScale` across an equality of `cover.indexSet` and `cover.tube`.  The twin has no
such lemma; `Kakeya.ML2Core.isKatzTaoDividingWindowLevels_of_cover_eq` below is it, and it needs one
equality more — `cover.assign`, because `level_density_band` reads `Tube.coverClass s (assign p) j`.

**So S1 is a bridge, not an impossibility**: whoever can identify `u'` with `S'` and `𝒲.cover` with
the restricted ambient cover gets the twin transported for free.
-/

@[expose] public section

open MeasureTheory Metric Tube
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

section CoverBridge

variable {ι : Type*} {δ : NNReal} {s : Finset ι} {N : ℕ}

/-- `Tube.UniformTubeSet.nodesUnder` depends on the cover only through `indexSet` and `tube`. -/
theorem nodesUnder_congr {T T' : ι → Tube δ (EuclideanSpace ℝ (Fin 3))} {C C' : NNReal}
    {𝒰 : Tube.UniformTubeSet s T N C} {𝒰' : Tube.UniformTubeSet s T' N C'}
    (hidx : 𝒰'.cover.indexSet = 𝒰.cover.indexSet) (htube : 𝒰'.cover.tube = 𝒰.cover.tube)
    (b a : ℕ) (j : ι) : 𝒰'.nodesUnder b a j = 𝒰.nodesUnder b a j := by
  classical
  simp only [Tube.UniformTubeSet.nodesUnder, Tube.UniformTubeSet.nodesIn, hidx, htube]

/-- **The bridge `S1` needs, named.**  `Kakeya.ML2Reduction.IsKatzTaoDividingWindowLevels` mentions
the cover only through `indexSet`, `tube` and `assign`, so those three equalities transport it
verbatim — the twin's analogue of the existing
`Kakeya.ML2Reduction.isKatzTaoAtEveryScale_of_cover_eq`.

What this lemma does **not** do, and what `S1` still owes: identify the producer's family `u'` with
the refinement's `S'` (the two hierarchies must already be on the same `Finset`), and identify the
producer's constructed cover with the ambient one.  Both are facts about the dividing-scales
producer, not about the twin. -/
theorem isKatzTaoDividingWindowLevels_of_cover_eq
    {T T' : ι → Tube δ (EuclideanSpace ℝ (Fin 3))} {C C' : NNReal}
    {𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) C}
    {𝒰' : Tube.UniformTubeSet s T' (Tube.ssfGridLen δ) C'}
    (hidx : 𝒰'.cover.indexSet = 𝒰.cover.indexSet) (htube : 𝒰'.cover.tube = 𝒰.cover.tube)
    (hassign : 𝒰'.cover.assign = 𝒰.cover.assign)
    {Cstar : ENNReal} {η : ℕ → ℝ} {εd : ℝ} {N' a b m : ℕ}
    (h : ML2Reduction.IsKatzTaoDividingWindowLevels 𝒰 Cstar η εd N' a b m) :
    ML2Reduction.IsKatzTaoDividingWindowLevels 𝒰' Cstar η εd N' a b m where
  step_lt := h.step_lt
  coarse_lt_fine := h.coarse_lt_fine
  fine_le_gridLen := h.fine_le_gridLen
  scale_sep := h.scale_sep
  coarse_maxDensity_le := by rw [hidx, htube]; exact h.coarse_maxDensity_le
  middle_maxDensity_le := by
    intro j hj
    rw [nodesUnder_congr hidx htube, htube]
    exact h.middle_maxDensity_le j (by rwa [hidx] at hj)
  le_window_maxDensity := by
    intro ρ h1 h2 j hj
    rw [nodesUnder_congr hidx htube, htube]
    exact h.le_window_maxDensity ρ h1 h2 j (by rwa [hidx] at hj)
  le_level_maxDensity := by
    intro c h1 h2 j hj
    rw [nodesUnder_congr hidx htube, htube]
    exact h.le_level_maxDensity c h1 h2 j (by rwa [hidx] at hj)
  level_density_band := by
    obtain ⟨Φ, hΦ⟩ := h.level_density_band
    refine ⟨Φ, ?_⟩
    intro p hp c hc j hj
    rw [hassign, htube]
    exact hΦ p hp c hc j (by rwa [hidx] at hj)

end CoverBridge

section NoDrop

variable {ι : Type*} {δ Cu : NNReal} {u : Finset ι}
  {T : ι → Tube δ (EuclideanSpace ℝ (Fin 3))}

/-- **`S2`, sharp.**  The `(D)` branch asks for a *strict* decrease of a `ℕ`-valued potential, and a
subfamily alone never supplies one: at `S' = S` there is nothing to decrease.  The dividing-scales
dichotomy's other alternative is `IsKatzTaoAtEveryScale`, which mentions the potential nowhere, and
its family output `u' ⊆ s` may be all of `s` (the cardinality retention holds at
`totalLoss ≥ 1`). -/
theorem no_potential_drop_self {h : ℝ}
    (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu) (S : Finset ι) :
    ¬ (potential h 𝒰 S + 1 ≤ potential h 𝒰 S) :=
  Nat.not_succ_le_self _

end NoDrop

end Kakeya.ML2Core

end
