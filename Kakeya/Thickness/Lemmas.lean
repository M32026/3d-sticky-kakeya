/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.ConvexHull
public import Kakeya.Thickness.Basic
public import Kakeya.Thickness.Volume
public import Kakeya.Thickness.OuterPrism
public import Kakeya.DimensionN.Volume
public import Kakeya.Thickness.ConvexSpaceBody

/-!
We put in this files lemmas about `ethickness` which are not very well categorized.
-/

@[expose] public section

open MeasureTheory Module
open scoped ENNReal NNReal

namespace ConvexSpaceBody

variable
  {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A finite family of convex bodies is discretized at scale `δ` if every body lies in the
closed unit ball and has smallest affine thickness at least `δ`.

Positivity of `δ` is deliberately not part of this predicate: it is a condition on the scale
parameter, and callers should assume it separately exactly when they need it. -/
structure IsDiscretizedAtScale (s : Finset ι) (V : ι → ConvexSpaceBody E)
    (δ : ℝ≥0) : Prop where
  /-- Every body in the family lies in the closed unit ball. -/
  subset_unitBall : ∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 1
  /-- Every body in the family has smallest affine thickness at least `δ`. -/
  le_scale : ∀ i ∈ s, (δ : ℝ≥0∞) ≤ Metric.ethickness.scale ℝ (V i).carrier

end ConvexSpaceBody

namespace Metric

section -- We show several consequences of h1 and h2 below.
variable
  {ι : Type*}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {δ : NNReal}
  {s : Finset ι}
  {V : ι → ConvexSpaceBody E}
  (h1 : ∀ i ∈ s, (V i).carrier ⊆ closedBall 0 1)
  (h2 : ∀ i ∈ s, δ ≤ ethickness.scale ℝ (V i).carrier)

include h1 h2 in
/-- A scale bound for bodies inside the unit ball forces `δ ≤ 1`. -/
lemma ethickness.le_of_le_scale_of_subset [Nontrivial E] (hs : s.Nonempty) : δ ≤ 1 := by
  suffices (δ : ENNReal) ≤ 1 by simpa
  obtain ⟨i, hi⟩ := hs
  apply (h2 i hi).trans
  rw [scale_eq]
  apply ethickness_le_of_subset_closedBall
  exact h1 i hi

include h1 in
/-- Every ethickness of an outer body `W_t` is at most `1`. -/
lemma ethickness_convexHullBiUnion_le
    {t : Finset ι} (ht : t.Nonempty) (hts : t ⊆ s) (k) :
    ethickness ℝ (t.convexHull_biUnion V).carrier k ≤ 1 := by
  apply ethickness_le_of_subset_closedBall
  · rw [ht.convexHull_biUnion_subset_iff]
    · intro i hi
      exact h1 i (hts hi)
    · exact (convex_closedBall 0 1).isConvexSet

include h2 in
/-- Every ethickness of an outer body `W_t` in a genuine direction is at least `δ`. -/
lemma le_ethickness_convexHullBiUnion
    {t : Finset ι} (ht : t.Nonempty) (hts : t ⊆ s) {k} (hk : k < finrank ℝ E) :
    δ ≤ ethickness ℝ (t.convexHull_biUnion V).carrier k := by
  obtain ⟨i, hi⟩ := ht
  apply (h2 i (hts hi)).trans
  apply (ethickness.scale_le _ hk).trans
  apply ethickness_monotone
  exact Finset.le_convexHull_biUnion V hi

include h1 h2 in
/-- Blueprint `lem:blockEthicknessRange`: under the standing hypotheses `(⋆)` of blueprint
`def:biasedStandingHypotheses`, every ethickness of an outer body `W_t` lies in `[δ, 1]`.

This just packages `Metric.le_ethickness_convexHullBiUnion` and
`Metric.ethickness_convexHullBiUnion_le`. -/
theorem ethickness_convexHullBiUnion_mem_Icc
    {t : Finset ι} (ht : t.Nonempty) (hts : t ⊆ s) {k : ℕ} (hk : k < finrank ℝ E) :
    ethickness ℝ (t.convexHull_biUnion V).carrier k ∈ Set.Icc (δ : ENNReal) 1 :=
  ⟨le_ethickness_convexHullBiUnion h2 ht hts hk, ethickness_convexHullBiUnion_le h1 ht hts k⟩

end

section -- We show several consequences of ethickness comparison below.
variable
  {ι : Type*}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {s : Finset ι}
  {V : ι → ConvexSpaceBody E}
  (h : ∀ i ∈ s, ∀ j ∈ s, ethickness ℝ (V i).carrier ≤ 2 • ethickness ℝ (V j).carrier)
  (h' : ∀ i ∈ s, ∀ j ∈ s, thickness ℝ (V i).carrier ≤ 2 • thickness ℝ (V j).carrier)

/-- **The constant in the outer-prism volume comparison** (blueprint
`def:outerPrismVolumeComparisonConstant`):

`C(n) = 4 ^ n / Metric.lt_volume_convexHull.c n = 4 ^ n · n! ≥ 1`.

`Metric.volume_outerPrism_le_volume_self` states this factor inline as
`Metric.volume_comparison.C n`; the name is introduced so that constants built on it — its
consumer is `Kakeya.ml1Boot.dilateTestBody.C`, through
`Kakeya.ml1Boot.volume_dilateTestBody_le` — can be written symbolically instead of being
collapsed to a numeral.  It depends only on the ambient dimension `n`.

Numerically it agrees with `Metric.volume_comparison.C n`, of which it is a definitional alias,
but it belongs to a different lemma and so, by the conventions of this development, carries that
lemma's name. -/
noncomputable abbrev volume_outerPrism_le_volume_self.C (n : ℕ) : NNReal :=
  volume_comparison.C n

/-- **Convex-body-to-prism volume comparison.**  The outer prism of a nonempty compact convex set
`X` has volume at most `volume_comparison.C (finrank ℝ E) · |X|`.  The prism volume is
`2ⁿ ∏ τ_k(X)` (with `τ_k` the affine thicknesses, which the outer prism reproduces), and the convex
lower bound `c_n ∏ τ_k(X) ≤ |X|` gives `|outerPrism X| ≤ (2ⁿ/c_n)|X| ≤ (4ⁿ/c_n)|X|`. -/
theorem volume_outerPrism_le_volume_self {n : ℕ} (hn : finrank ℝ E = n) {X : Set E}
    (hXcv : Convex ℝ X) (hXc : IsCompact X) (hXne : X.Nonempty) :
    volume (outerPrism (V := E) hn hXc hXne).carrier
      ≤ (volume_comparison.C n : ℝ≥0∞) * volume X := by
  subst hn
  have hc0 : (lt_volume_convexHull.c (finrank ℝ E) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (lt_volume_convexHull.c_pos _).ne'
  have hctop : (lt_volume_convexHull.c (finrank ℝ E) : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  have hCval : (volume_comparison.C (finrank ℝ E) : ℝ≥0∞)
      = (4 : ℝ≥0∞) ^ finrank ℝ E / lt_volume_convexHull.c (finrank ℝ E) := by
    simp only [volume_comparison.C]
    rw [ENNReal.coe_div (lt_volume_convexHull.c_pos _).ne', ENNReal.coe_pow]; norm_num
  have hbdd : Bornology.IsBounded X := hXc.isBounded
  -- prism volume = 2^n * ∏ ethickness over range
  have hPvol : volume (outerPrism (V := E) rfl hXc hXne).carrier
      = 2 ^ finrank ℝ E * ∏ i ∈ Finset.range (finrank ℝ E), ethickness ℝ X i := by
    rw [PrismNDim.volume_carrier]
    congr 1
    rw [← Fin.prod_univ_eq_prod_range (fun k => ethickness ℝ X k) (finrank ℝ E)]
    apply Finset.prod_congr rfl
    intro i _
    rw [outerPrism.thicknesses_eq, ethickness_thickness' hbdd]
    exact ENNReal.ofReal_coe_nnreal.symm
  rw [hPvol, hCval]
  calc 2 ^ finrank ℝ E * ∏ i ∈ Finset.range (finrank ℝ E), ethickness ℝ X i
      ≤ 4 ^ finrank ℝ E * ∏ i ∈ Finset.range (finrank ℝ E), ethickness ℝ X i := by
        gcongr; norm_num
    _ = (4 ^ finrank ℝ E / lt_volume_convexHull.c (finrank ℝ E)) *
          (lt_volume_convexHull.c (finrank ℝ E)
            * ∏ i ∈ Finset.range (finrank ℝ E), ethickness ℝ X i) := by
        rw [← mul_assoc, ENNReal.div_mul_cancel hc0 hctop]
    _ ≤ (4 ^ finrank ℝ E / lt_volume_convexHull.c (finrank ℝ E)) * volume X := by
        gcongr; exact hXcv.ethickness_prod_le_volume

include h in
/-- Volume comparison from `ethickness` comparison for a family -/
lemma ethickness.volume_comparison : ∀ i ∈ s, ∀ j ∈ s,
    volume (V i).carrier ≤ volume_comparison.C (finrank ℝ E) * volume (V j).carrier := by
  peel h with _ _ _ _ h
  exact ConvexSpaceBody.volume_le_of_ethickness_le h

include h' in
/-- Volume comparison from `thickness` comparison -/
lemma thickness.volume_comparison : ∀ i ∈ s, ∀ j ∈ s,
    volume (V i).carrier ≤ volume_comparison.C (finrank ℝ E) * volume (V j).carrier := by
  peel h' with _ _ _ _ h
  exact ConvexSpaceBody.volume_le_of_thickness_le h

include h' in
/-- **Comparable carrier volumes**, sum form (blueprint `lem:volumeComparable`).

From the pairwise factor-`2` thickness comparability `h'`, for every `i ∈ s` the carrier
volumes satisfy `#s · |V i| ≤ κ · ∑ j, |V j|`, where `κ = volume_comparison.C (finrank ℝ E)`
is an absolute constant depending only on the ambient dimension. -/
theorem card_mul_volume_carrier_le_sum {i : ι} (hi : i ∈ s) :
    (s.card : ℝ≥0∞) * volume (V i).carrier
      ≤ volume_comparison.C (finrank ℝ E) * ∑ j ∈ s, volume (V j).carrier := by
  suffices ∑ j ∈ s, volume (V i).carrier ≤
      volume_comparison.C (finrank ℝ E) * ∑ j ∈ s, volume (V j).carrier by
    simpa [Finset.sum_const] using this
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ => thickness.volume_comparison h' i hi j ‹_›

end

end Metric

namespace Kakeya

open Metric

section BiasedRanges
variable
  {ι : Type*}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
  {δ : NNReal}
  {s : Finset ι}
  {V : ι → ConvexSpaceBody E}
  (h1 : ∀ i ∈ s, (V i).carrier ⊆ closedBall 0 1)
  (h2 : ∀ i ∈ s, δ ≤ ethickness.scale ℝ (V i).carrier)

omit [Nontrivial E] in
include h2 in
/-- Blueprint `lem:blockVolumeLowerBound` (lower bound): under `(⋆)`, the volume of an outer body
`W_t` is at least `c * δ ^ n`, where `c = Metric.lt_volume_convexHull.c n`.  Only the scale
hypothesis `h2` is needed. -/
theorem le_volume_convexHullBiUnion {t : Finset ι} (ht : t.Nonempty) (hts : t ⊆ s) :
    (lt_volume_convexHull.c (finrank ℝ E) : ENNReal) * (δ : ENNReal) ^ finrank ℝ E
      ≤ volume (t.convexHull_biUnion V).carrier := by
  have h_convex : Convex ℝ (t.convexHull_biUnion V).carrier :=
    (t.convexHull_biUnion V).convex'.convex
  have hdelta : (δ : ENNReal) ^ (finrank ℝ E) ≤
      ∏ i ∈ Finset.range (finrank ℝ E), ethickness ℝ (t.convexHull_biUnion V).carrier i := by
    calc
      (δ : ENNReal) ^ (finrank ℝ E) = (δ : ENNReal) ^ ((Finset.range (finrank ℝ E)).card) := by
        simp
      _ ≤ ∏ i ∈ Finset.range (finrank ℝ E), ethickness ℝ (t.convexHull_biUnion V).carrier i :=
        Finset.pow_card_le_prod (Finset.range (finrank ℝ E))
          (fun i => ethickness ℝ (t.convexHull_biUnion V).carrier i) (δ : ENNReal)
          (fun i hi => le_ethickness_convexHullBiUnion h2 ht hts (Finset.mem_range.mp hi))
  by_cases htriv : Nontrivial E
  · haveI : Nontrivial E := htriv
    calc
      (lt_volume_convexHull.c (finrank ℝ E) : ENNReal) * (δ : ENNReal) ^ finrank ℝ E
          ≤ (lt_volume_convexHull.c (finrank ℝ E) : ENNReal) *
            ∏ i ∈ Finset.range (finrank ℝ E), ethickness ℝ (t.convexHull_biUnion V).carrier i := by
        gcongr
      _ ≤ volume (t.convexHull_biUnion V).carrier :=
        h_convex.ethickness_prod_le_volume
  · have hsub : Subsingleton E := not_nontrivial_iff_subsingleton.mp htriv
    haveI : Subsingleton E := hsub
    have h_dim0 : finrank ℝ E = 0 := Module.finrank_zero_of_subsingleton
    have h_nonempty : (t.convexHull_biUnion V).carrier.Nonempty :=
      (t.convexHull_biUnion V).nonempty'
    have h_carrier_univ : (t.convexHull_biUnion V).carrier = Set.univ :=
      h_nonempty.eq_univ
    have h_vol_univ : volume (Set.univ : Set E) = 1 := by
      haveI : IsEmpty (Fin (finrank ℝ E)) := by
        rw [h_dim0]; exact inferInstance
      let b : Basis (Fin (finrank ℝ E)) ℝ E := (stdOrthonormalBasis ℝ E).toBasis
      have hpar_singleton : parallelepiped b = {(0 : E)} := by
        ext x; simp [parallelepiped]
      calc
        volume (Set.univ : Set E) = b.addHaar (Set.univ : Set E) := rfl
        _ = b.addHaar {(0 : E)} := by
          have h_univ_singleton : (Set.univ : Set E) = {(0 : E)} := by
            ext x; simp [Subsingleton.elim x 0]
          rw [h_univ_singleton]
        _ = b.addHaar (parallelepiped b) := by rw [hpar_singleton]
        _ = 1 := b.addHaar_self
    simp [h_dim0, h_carrier_univ, h_vol_univ]

omit [Nontrivial E] in
include h1 in
/-- Blueprint `lem:blockVolumeLowerBound` (upper bound): under `(⋆)`, the volume of an outer body
`W_t` is at most `2 ^ n`.  Only the localization hypothesis `h1` is needed. -/
theorem volume_convexHullBiUnion_le {t : Finset ι} (ht : t.Nonempty) (hts : t ⊆ s) :
    volume (t.convexHull_biUnion V).carrier ≤ 2 ^ finrank ℝ E := by
  have h_le := volume_le_prod_ethickness (t.convexHull_biUnion V).carrier
  calc
    volume (t.convexHull_biUnion V).carrier
        ≤ 2 ^ (Module.finrank ℝ E) *
          ∏ i ∈ Finset.range (Module.finrank ℝ E),
            ethickness ℝ (t.convexHull_biUnion V).carrier i :=
      h_le
    _ = 2 ^ finrank ℝ E *
        ∏ i ∈ Finset.range (finrank ℝ E), ethickness ℝ (t.convexHull_biUnion V).carrier i := by
      simp
    _ ≤ 2 ^ finrank ℝ E * ∏ i ∈ Finset.range (finrank ℝ E), (1 : ENNReal) := by
      gcongr with i hi
      exact ethickness_convexHullBiUnion_le h1 ht hts i
    _ = 2 ^ finrank ℝ E := by simp

omit [Nontrivial E] in
include h1 h2 in
/-- Blueprint `lem:blockVolumeLowerBound`: under `(⋆)`, the volume of an outer body `W_t` lies in
`[c * δ ^ n, 2 ^ n]`, where `c = Metric.lt_volume_convexHull.c n`.

This just packages `Kakeya.le_volume_convexHullBiUnion` and
`Kakeya.volume_convexHullBiUnion_le`. -/
theorem volume_convexHullBiUnion_mem_Icc {t : Finset ι} (ht : t.Nonempty) (hts : t ⊆ s) :
    volume (t.convexHull_biUnion V).carrier ∈
      Set.Icc ((lt_volume_convexHull.c (finrank ℝ E) : ENNReal) * (δ : ENNReal) ^ finrank ℝ E)
        (2 ^ finrank ℝ E) :=
  ⟨le_volume_convexHullBiUnion h2 ht hts, volume_convexHullBiUnion_le h1 ht hts⟩

omit [Nontrivial E] in
include h2 in
/-- Blueprint `lem:memberVolumeRange` (lower bound): under `(⋆)`, the volume of a member `V i` of
the family is at least `c * δ ^ n`.  This is `Kakeya.le_volume_convexHullBiUnion` for the
singleton subfamily `{i}`, using `Finset.convexHull_biUnion_singleton`. -/
theorem le_volume_of_le_scale {i : ι} (hi : i ∈ s) :
    (lt_volume_convexHull.c (finrank ℝ E) : ENNReal) * (δ : ENNReal) ^ finrank ℝ E
      ≤ volume (V i).carrier := by
  rw [← Finset.convexHull_biUnion_singleton V i]
  exact le_volume_convexHullBiUnion h2 (Finset.singleton_nonempty i)
    (Finset.singleton_subset_iff.mpr hi)

omit [Nontrivial E] in
include h1 in
/-- Blueprint `lem:memberVolumeRange` (upper bound): under `(⋆)`, the volume of a member `V i` of
the family is at most `2 ^ n`.  This is `Kakeya.volume_convexHullBiUnion_le` for the singleton
subfamily `{i}`, using `Finset.convexHull_biUnion_singleton`. -/
theorem volume_le_of_subset_closedBall {i : ι} (hi : i ∈ s) :
    volume (V i).carrier ≤ 2 ^ finrank ℝ E := by
  rw [← Finset.convexHull_biUnion_singleton V i]
  exact volume_convexHullBiUnion_le h1 (Finset.singleton_nonempty i)
    (Finset.singleton_subset_iff.mpr hi)

omit [Nontrivial E] in
include h1 h2 in
/-- Blueprint `lem:memberVolumeRange`: under `(⋆)`, the volume of a member `V i` of the family
lies in `[c * δ ^ n, 2 ^ n]`.

This just packages `Kakeya.le_volume_of_le_scale` and
`Kakeya.volume_le_of_subset_closedBall`. -/
theorem volume_mem_Icc_of_le_scale {i : ι} (hi : i ∈ s) :
    volume (V i).carrier ∈
      Set.Icc ((lt_volume_convexHull.c (finrank ℝ E) : ENNReal) * (δ : ENNReal) ^ finrank ℝ E)
        (2 ^ finrank ℝ E) :=
  ⟨le_volume_of_le_scale h2 hi, volume_le_of_subset_closedBall h1 hi⟩

end BiasedRanges

end Kakeya
