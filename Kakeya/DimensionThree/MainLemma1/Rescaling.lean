/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.Rescaling.Normalized
public import Kakeya.DimensionThree.MainLemma1.Rescaling.Window
public import Kakeya.DimensionThree.MainLemma1.Rescaling.WindowTransport
public import Kakeya.DimensionThree.MainLemma1.Rescaling.Pigeonhole
public import Kakeya.DimensionThree.MainLemma1.Rescaling.Dichotomy
public import Kakeya.DimensionThree.MainLemma1.Rescaling.DensityTransfer
public import Kakeya.DimensionThree.MainLemma1.Rescaling.Collapse
public import Kakeya.DimensionThree.MainLemma1.Rescaling.FineDilate
public import Kakeya.DimensionThree.MainLemma1.Rescaling.Assembly
public import Kakeya.DimensionThree.MainLemma1.Rescaling.CoarseDensity
public import Kakeya.DimensionThree.MainLemma1.Rescaling.Bracket
public import Kakeya.DimensionThree.MainLemma1.Rescaling.Numerics
public import Kakeya.DimensionThree.MainLemma1.Rescaling.KatzTao
public import Kakeya.DimensionThree.MainLemma1.Rescaling.KatzTaoBallPrefix

/-!
# Main Lemma 1, Case (ii): the middle factor

This file formalizes the last three subsections of Case (ii) of Section 8 of the adapted
blueprint, which together prove the middle-scale estimate `multTTauInsideTTheta` that
`Kakeya.ml1Boot.multiplicity_le_of_middle` consumes:

* `GWZAdapted/section8_rescaling.tex` — rescaling the middle factor to the unit ball, the
  plank pigeonhole and the flat-prism dichotomy:
  `Kakeya.ml1Boot.middle_le_of_normalized`, `Kakeya.ml1Boot.exists_normalizedMiddleData`,
  `Kakeya.ml1Boot.plankPigeonhole.C`, `Kakeya.ml1Boot.exists_plankDimensions`,
  `Kakeya.ml1Boot.flatPrism_dichotomy`;
* `GWZAdapted/section8_endgame.tex` — the endgame at the plank scale:
  `Kakeya.ml1Boot.densityTransfer.C`,
  `Kakeya.ml1Boot.exists_plank_tube_of_thickness_le_one`,
  `Kakeya.ml1Boot.frostmanConstIn_fibre_le`, `Kakeya.ml1Boot.plankWidth_le`,
  `Kakeya.ml1Boot.normalized_le_of_coarse`;
* `GWZAdapted/section8_katztao.tex` — the Katz–Tao bound at the plank scale and the
  assembly: `Kakeya.ml1Boot.coarsePlank.C`,
  `Kakeya.ml1Boot.exists_plankTube_parentFamily`, `Kakeya.ml1Boot.maxDensity_coarse_le`,
  `Kakeya.ml1Boot.bracket_mem_Icc`, `Kakeya.ml1Boot.bracket_rpow_le`,
  `Kakeya.ml1Boot.numerics`, `Kakeya.ml1Boot.numerics_strong`,
  `Kakeya.ml1Boot.multiplicity_coarse_le`, `Kakeya.ml1Boot.multiplicity_le_middle`.

## The `b`-tube scale `bq`

`Kakeya.IsPlankOfDimensions plankPigeonhole.C ap bp` only bounds the plank's first affine
thickness by `C_𝕎 bp`, and a `bp`-tube has first affine thickness at most `2 bp`, so a plank
does **not** fit in a `bp`-tube (`C_𝕎 ≥ 1024`).  The honest tube scale is therefore carried
as a separate variable `bq` with `bp ≤ bq ≤ plankPigeonhole.C * bp`, and the statements from
`Kakeya.ml1Boot.exists_plank_tube_of_thickness_le_one` onwards are phrased at `bq`.  Since the
plank data must be produced at the parent scale `ρ = δ̃ ^ (6 ε)` for `bq` to stay below
`δ̃ ^ (5 ε)`, `Kakeya.ml1Boot.flatPrism_dichotomy` is stated for an arbitrary parent scale and
the density exponent of `Kakeya.ml1Boot.multiplicity_coarse_le` is `30 ε + ap'`.  That `30 ε`
is `6 ε` times the parent count exponent `5`: `Kakeya.ml1Boot.maxDensity_coarse_le_rpow` reads
the number of `ρ`-tubes at `ρ ^ (-5)`, which is the weakening (valid since `ρ ≤ 1`) of the
sharper `ρ ^ (-4)` that `Kakeya.ml1Boot.card_le` proves.  The window
in which `bq` has to land is the `5 ε`-window, not the `ε`-window, because that is what
`Kakeya.ml1Boot.exists_caseTwoData`(iv) supplies; blueprint
`note:ml1bootWindowConsumers` records the resulting arithmetic, and it is why `ε ≤ g₀ / 96`
and `Kakeya.ml1Boot.numerics_strong` carries `72 ε`.

The geometric and volume-theoretic obligations of
`Kakeya.ml1Boot.exists_plank_tube_of_thickness_le_one` are isolated in
`Kakeya/DimensionThree/MainLemma1/PlankTube.lean`
(`Kakeya.ml1Boot.volume_bounds_of_ethickness_bounds`,
`Kakeya.ml1Boot.volume_bounds_of_isPlankOfDimensions`, `Kakeya.ml1Boot.tube_ethickness_bounds`,
`Kakeya.ml1Boot.volume_bounds_of_tube`, `Kakeya.ml1Boot.unitCoreSegment`,
`Kakeya.ml1Boot.dist_prism_transverse_le`, `Kakeya.ml1Boot.prism_subset_unitCoreTube`,
`Kakeya.ml1Boot.plankTube`, `Kakeya.ml1Boot.subset_plankTube`,
`Kakeya.ml1Boot.plankInTube_constant_bounds`), which carries the plank comparability constant as
a parameter so that it can sit below `Kakeya.ml1Boot.plankPigeonhole.C`.

The three moves of `Kakeya.ml1Boot.exists_dilate_testBody` are likewise isolated, in
`Kakeya/DimensionThree/MainLemma1/TestBody.lean` (`Kakeya.ml1Boot.subset_dilateTestBody`,
`Kakeya.ml1Boot.dilate_tube_subset_dilateTestBody`,
`Kakeya.ml1Boot.volume_dilateTestBody_le`), which run on the prism API
`PrismNDim.mem_selfHomothety_iff`, `PrismNDim.subset_selfHomothety` and
`PrismNDim.homothety_two_mem_selfHomothety` of `Kakeya/DimensionN/Prism.lean`.

This is the only part of Section 8 that uses the Katz–Tao hypothesis, and the only part
where the plank machinery of Sections 4 and 6 enters, through
`Kakeya.multiplicity_le_of_factorsThroughFlatPrisms'`.

## Naming of the scales and the exponents

The rescaled scale of the blueprint, `δ̃ = τ / θ`, is written `δt`; the plank widths `a ≤ b`
are `ap ≤ bp` where a fresh name is needed.  As in
`Kakeya/DimensionThree/MainLemma1/Cases.lean`, the exponents of the parameter package are
*bare real numbers* wherever the statement does not otherwise need
`Kakeya.ml1Boot.params`: `a` for `η_{j-1}`, `n` for `η_j`, `ap'` for the rescaled exponent
`η'_{j-1} = 10 η_{j-1} / (ε β₀)` of `Kakeya.ml1Boot.Params.etaPrime`.  The two statements
that do mention the package, `Kakeya.ml1Boot.numerics` and
`Kakeya.ml1Boot.multiplicity_le_middle`, are the ones whose content *is* the interplay of its
items.  The ambient dimension is `3`, so tube volumes enter as a literal exponent `2`.

## Planks

A plank is a convex body whose three affine thicknesses are comparable to `1`, `b`, `a`; the
predicate is `Kakeya.IsPlankOfDimensions` (see `Kakeya/Factoring/FlatPrisms.lean`), and a
family of planks factoring a fibre is a `ConvexSpaceBody.Factorization` with constant `2`
whose parts carry that predicate.  The blueprint's `𝕎_m = (W_{m,t})_{t ∈ 𝒫_m}` is
`fun part => part.convexHull_biUnion V` over the parts of the factorization, which is the
family that `ConvexSpaceBody.Factorization` is about by definition.

## The retired Rogers–Shephard assumption

The earlier witness `K* = 2 K - K` of `Kakeya.ml1Boot.exists_dilate_testBody` needed the
Rogers–Shephard inequality `|K - K| ≤ (6 choose 3) |K|` in `ℝ³`, which was recorded here as a
deliberate assumption `Kakeya.volume_sub_self_le`.  Blueprint
`prop:ml1bootDifferenceBodyVolume` retires it: the witness is now
`K* = 3 · outerPrism K` (`Kakeya.ml1Boot.dilateTestBody`), a centrally symmetric prism, so no
difference body enters the argument and the declaration has been deleted.  This development now
assumes no difference-body inequality anywhere.
-/
