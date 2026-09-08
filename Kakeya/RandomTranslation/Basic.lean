/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module  -- shake: keep-all

public import Kakeya.RandomTranslation.Measure
public import Kakeya.RandomTranslation.Counting
public import Kakeya.RandomTranslation.TranslationProb
public import Kakeya.RandomTranslation.ScaledCounting

/-!
# Uniform random translations — basic interface

Aggregator for the probabilistic foundations of [GWZ, §3] and the appendix,
split into four layers:

* `Measure.lean` — the class `HasUniformTranslation`, the tube-in-set
  probability bounds it yields, and the product measures `productMeasure` /
  `productMeasureIndexed` with their union bounds.

* `Counting.lean` — the tube-contained count `X(ω) = #{i ∈ s | R(ω)(T i) ⊆ K}`,
  its product-space copies, and the Chernoff tails for `∑_j X_j`.

* `TranslationProb.lean` — the canonical uniform-translation instance
  `instHasUniformTranslationSelf`, its `ρ`-scaled variant, and the two
  probability bounds `prob_smul_add_in_set_self` and
  `prob_tube_translate_subset_le`.

* `ScaledCounting.lean` — the same counts phrased against the `r`-scaled
  translation action, which is the interface
  `RandomTranslation.exists_refinement` consumes.
-/
