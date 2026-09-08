/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Tube.Dilate
public import Kakeya.DimensionThree.MainLemma2.NonSlabAngle
public import Kakeya.DimensionThree.MainLemma2.Conjunct6Refutation

/-!
# Constants for the dilation estimates

`Kakeya.VeryNotSticky.edComparabilityConstant`, `edDilateConstant`,
`edSegmentsConstant`, `edDensityConstant`, and `edRadiusConstant` are
independent of `δ`. They appear in the hypotheses of
`BallDataGeneralTarget` and `exists_core_edSegments_of_cover`.

The comparability constant is determined by
`Kakeya.Tube.tubeOverlapCoreClose`: it is `9 + 2 * 4^3 / c₃`, where
`c₃` is the three-dimensional inscribed-simplex constant. This value,
rather than an arbitrary smaller numeral, controls the required dilate.

The module imports the tube-dilation estimate and the scale definitions
used by `deltaLeR₁_of_radiusFloor`.
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped ENNReal NNReal Topology

namespace Kakeya.VeryNotSticky

universe u

/-! ### The honest dilate constant `K′₀`, from the existing tube geometry -/

/-- **`K′₀`** — the dilation constant GWZ's "comparable" actually costs, read off the existing
`Kakeya.Tube.tubeOverlapCoreClose`: `K′₀ = 9 + 2·4³ / c₃`, where `c₃ = Kakeya.Tube.le_volume.c 3`
is the tube volume constant. It is an explicit number in the ambient dimension `3` and depends
on nothing else — in particular not on `δ`, `r₁` or the family. -/
noncomputable def edComparabilityConstant : ℝ := Kakeya.Tube.tubeOverlapCoreClose.C 3

theorem edComparabilityConstant_eq :
    edComparabilityConstant = 9 + 2 * 4 ^ 3 / ((Tube.le_volume.c 3 : NNReal) : ℝ) := rfl

theorem one_lt_edComparabilityConstant : 1 < edComparabilityConstant :=
  Kakeya.Tube.tubeOverlapCoreClose.one_lt_C 3

theorem edComparabilityConstant_pos : 0 < edComparabilityConstant :=
  lt_trans zero_lt_one one_lt_edComparabilityConstant

/-! ### §G-1's hypothesis floor: the three named constants -/

/-- **`K′` — the dilate of GWZ's "comparable"**, in one named `def` so that a later sharpening
moves one token.

GWZ's word is *comparable*: `gwz.txt` l.2021-2023 ("a set of essentially distinct `δ × δ × r₁`
tubes … of the form `T ∩ B`" and "`𝕋(T_B)` the set of tubes `T` so that `T ∩ B` is **comparable**
to `T_B`"), read with the paper's own vocabulary at l.99-100 ("a family of convex sets, each of
which have comparable volume") and l.921-923 ("each `P′ ∈ P` is contained in a set `P_θ ∈ P_θ`
for which `P′_θ` is comparable to `P_θ` … then they are contained in comparable slabs").
Comparability of convex bodies is containment in a bounded **dilate**, and `K′` is that dilate.

**The value is not free.** The only route in the tree that can *prove* comparability from
`¬ IsEssentiallyDistinct` is `Kakeya.Tube.tubeOverlapCoreClose`, whose constant is
`Kakeya.VeryNotSticky.edComparabilityConstant = 9 + 2·4³ / c₃`. Sharpening the geometry lowers this one token. -/
noncomputable def edDilateConstant : NNReal := edComparabilityConstant.toNNReal

theorem coe_edDilateConstant : ((edDilateConstant : NNReal) : ℝ) = edComparabilityConstant :=
  Real.coe_toNNReal _ (le_of_lt edComparabilityConstant_pos)

theorem one_le_edDilateConstant : 1 ≤ edDilateConstant := by
  rw [← NNReal.coe_le_coe, NNReal.coe_one, coe_edDilateConstant]
  exact le_of_lt one_lt_edComparabilityConstant

/-- **The raised floor on the caller's `C₀`**: `hC₀ : 4 ≤ C₀` becomes
`hC₀ : edSegmentsConstant ≤ C₀`. This changes only the hypothesis block — `core.C₀ = C₀`
survives verbatim, so every consumer's equation survives verbatim. -/
noncomputable def edSegmentsConstant : NNReal := 4 * edDilateConstant

/-- **The raised floor on the caller's `c₁`**:
`4 * c₁ * ballCoverConstant ≤ 1` becomes `edDensityConstant * c₁ * ballCoverConstant ≤ 1`.
The `K′²` is the volume growth of the carrier under the dilate
(`Kakeya.VeryNotSticky.volume_segCarrierSetAt_le_mul_volume_segCarrierSet`). -/
noncomputable def edDensityConstant : NNReal := 4 * edDilateConstant ^ 2

theorem four_le_edSegmentsConstant : 4 ≤ edSegmentsConstant := by
  rw [edSegmentsConstant]
  nth_rewrite 1 [show (4 : NNReal) = 4 * 1 by ring]
  gcongr
  exact one_le_edDilateConstant

/-! ### S-3: the radius floor, and the class count from the density cap -/

/-- **The radius floor.** `Kakeya.VeryNotSticky.card_cone_le` needs its cone radius `ρ ≤ 1`, and
the comparability class of a capsule spreads over `ρ ≈ 8 K′₀ δ / r₁`; so the caller's
`hδr : 16 δ ≤ r₁` has to become `edRadiusConstant · δ ≤ r₁`. Like  §G-1's floors on
`C₀` and on `c₁` this is a **hypothesis-floor** move on a caller-chosen constant, it costs
nothing (`r₁/δ = δ^{exscal−1} → ∞`), and it implies the old binder. -/
noncomputable def edRadiusConstant : NNReal := 8 * edDilateConstant

theorem sixteen_le_edRadiusConstant : 16 ≤ edRadiusConstant := by
  rw [edRadiusConstant]
  nth_rewrite 1 [show (16 : NNReal) = 8 * 2 by norm_num]
  gcongr
  have h1 : (1 : NNReal) ≤ edDilateConstant := one_le_edDilateConstant
  have : (2 : NNReal) ≤ edDilateConstant := by
    rw [← NNReal.coe_le_coe, coe_edDilateConstant]
    rw [edComparabilityConstant_eq]
    have hc : (0 : ℝ) < ((Tube.le_volume.c 3 : NNReal) : ℝ) := by
      exact_mod_cast Tube.le_volume.c_pos 3
    have : (0 : ℝ) ≤ 2 * 4 ^ 3 / ((Tube.le_volume.c 3 : NNReal) : ℝ) := by positivity
    push_cast
    linarith
  exact this

theorem deltaLeR₁_of_radiusFloor {cfg : VeryNotSticky.{u}}
    (h : ((edRadiusConstant : NNReal) : ℝ) * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ)) :
    16 * (cfg.δ : ℝ) ≤ (cfg.r₁ : ℝ) := by
  refine le_trans ?_ h
  have h16 : (16 : ℝ) ≤ ((edRadiusConstant : NNReal) : ℝ) := by
    exact_mod_cast sixteen_le_edRadiusConstant
  exact mul_le_mul_of_nonneg_right h16 (cfg.δ).coe_nonneg

/-- **The `δ`-free constant of the class count**: `64 · coneCardConstant · K′₀²`. -/
noncomputable def edClassCountConstant : NNReal :=
  64 * coneCardConstant * edDilateConstant ^ 2

theorem edClassCountConstant_pos : 0 < edClassCountConstant := by
  rw [edClassCountConstant]
  have h1 : 0 < coneCardConstant := coneCardConstant_pos
  have h2 : 0 < edDilateConstant := lt_of_lt_of_le zero_lt_one one_le_edDilateConstant
  positivity

/-- **The dilation ceiling of `BallDataGeneralTarget`.**  `Kakeya.VeryNotSticky.BallData.Cdil`
is only ever read as an upper bound (it is absorbed by
`Kakeya.VeryNotSticky.SlabScale.final`), so the contract asks for a ceiling, not a value:
`Kakeya.VeryNotSticky.segsDilationConstant = max 1 (3 · 2¹⁵ / c₃)` for T3's core, and room
above it for the canonical-capsule core of the refined `propvnslocalization`, whose segments are
not contained in their parent tubes.  A `δ`-free absolute, its own symbol; the capsule producer
pins the value (one token) and records the measurement.  The bound follows from the compiled capsule dilation bound
(`CanonicalCapsulesDilation.lean`, `le_capsuleDilationConstant_mul`, at `ρ = 2δ` and any
half-length `L` with `4δ ≤ L ≤ 1/4` — the producer `CoverData.capsuleCore` uses `L = r₁/4`) is
`576000 / c₃` with `c₃ = Tube.le_volume.c 3 = 4π/9` — the container
`Convex.exists_homothety_container` costs `(4μ)³ · 3!` at `μ = (1+L)/L` on top of the capsule
volume `8(L+ρ)ρ²`, which the round-2 prose estimate (`5832 / c₃`) had omitted — i.e. `5.86 ×`
`segsDilationConstant`'s `3 · 2¹⁵ / c₃`.  `segsDilationConstant ≤ capsuleDilationConstant` is
`Kakeya.VeryNotSticky.segsDilationConstant_le_capsuleDilationConstant` in
`BallDataGeneral.lean`, the first file importing both (this file does not import
`BallCoreOfCover`). -/
noncomputable def capsuleDilationConstant : NNReal := max 1 (576000 / Tube.le_volume.c 3)

theorem one_le_capsuleDilationConstant : 1 ≤ capsuleDilationConstant := le_max_left _ _

end Kakeya.VeryNotSticky
