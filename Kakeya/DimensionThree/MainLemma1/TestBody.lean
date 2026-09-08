/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Thickness.Lemmas
public import Kakeya.Tube.Dilate
public import Kakeya.Tube.IntersectionVolume

/-!
# Main Lemma 1, Case (ii): a test body absorbing the dilates of the tubes it contains

This file collects the three moves of `Kakeya.ml1Boot.exists_dilate_testBody` (blueprint
`lem:ml1bootDilateTestBody`, in `Kakeya/DimensionThree/MainLemma1/Rescaling.lean`), so that the
lemma itself becomes a short assembly, in the same style as
`Kakeya/DimensionThree/MainLemma1/PlankTube.lean`.  It formalizes the group of auxiliary
statements of `GWZAdapted/section8_katztao.tex`:

* `Kakeya.ml1Boot.subset_dilateTestBody` (blueprint `lem:ml1bootDilateTestBodySubset`) —
  `K ⊆ P ⊆ 3 · P`;
* `Kakeya.ml1Boot.dilate_tube_subset_dilateTestBody` (blueprint
  `lem:ml1bootDilateTestBodyAbsorbs`) — `2 · T ⊆ 3 · P` for every tube `T ⊆ K`, of any scale;
* `Kakeya.ml1Boot.volume_dilateTestBody_le` (blueprint `lem:ml1bootDilateTestBodyVolume`) —
  `|3 · P| = 3 ^ n |P| ≤ 3 ^ n · C(n) · |K|`.

Throughout, `P = outerPrism K` is the outer prism of the convex body `K`
(`Kakeya.ml1Boot.outerPrismBody`) and `3 · P` is its homothety of ratio `3` about its own centre
(`Kakeya.ml1Boot.dilateTestBody`).

## Why a prism and not a general convex body

The earlier witness of `Kakeya.ml1Boot.exists_dilate_testBody` was `K* = 2 K - K`, which forced
the Rogers–Shephard inequality in `ℝ³` — the accepted assumption now retired as blueprint
`prop:ml1bootDifferenceBodyVolume` — and which could not even be *named* as a
`ConvexSpaceBody`, that structure carrying no Minkowski arithmetic.  A prism is a convex
body by construction and is centrally symmetric about its own centre, so
`PrismNDim.homothety_two_mem_selfHomothety` replaces the difference-body step by a
coordinate computation.  The price is
`Metric.volume_outerPrism_le_volume_self.C n` in place of `(6 choose 3)`, and `3 ^ n` in place of
`2 ^ n`; nothing downstream uses the numerical value of `Kakeya.ml1Boot.dilateTestBody.C`.

## The ambient dimension

All three statements are at a general ambient dimension `n`; only `n = 3` is used, by
`Kakeya.ml1Boot.exists_dilate_testBody`.  In particular no hypothesis on the tube scale `δ` is
imposed anywhere — not even `0 < δ` — so that "every tube, of any scale" is literally supported;
this is why `Tube.x_mem_carrier` and `Tube.y_mem_carrier` are used in place of
`Tube.midpoint_mem_carrier`, which carries the hypothesis `0 < δ`.
-/

@[expose] public section

open MeasureTheory Module
open scoped ENNReal NNReal

noncomputable section

namespace Kakeya

namespace ml1Boot

section TestBody

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The outer prism `P = outerPrism K` of a convex body `K ⊆ ℝⁿ`, viewed as a prism: the
axis-aligned box whose half-widths are the affine thicknesses of `K` (blueprint
`def:outerPrism`).  An abbreviation, so that the statements of this file can name `P` without
repeating the compactness and nonemptiness witnesses supplied by `K`. -/
abbrev outerPrismBody {n : ℕ} (hn : finrank ℝ E = n) (K : ConvexSpaceBody E) :
    PrismNDim n E E :=
  outerPrism (V := E) hn K.isCompact' K.nonempty'

/-- The test body `K* = 3 · P` of `Kakeya.ml1Boot.exists_dilate_testBody`, where
`P = outerPrism K`: the homothety of ratio `3` of the outer prism of `K` about its *own* centre
(blueprint `def:prismHomothety`).  Being a prism it is in particular a convex body, so no
Minkowski arithmetic of convex bodies is needed in order to name it. -/
abbrev dilateTestBody {n : ℕ} (hn : finrank ℝ E = n) (K : ConvexSpaceBody E) :
    PrismNDim n E E :=
  (outerPrismBody hn K).homothety (outerPrismBody hn K).center 3

omit [MeasurableSpace E] [BorelSpace E] in
/-- **The prism test body contains the body** (blueprint `lem:ml1bootDilateTestBodySubset`).

For a convex body `K ⊆ ℝⁿ` and `P = outerPrism K`,

`K ⊆ P ⊆ 3 · P`.

The first containment is `outerPrism.self_subset`, available because a convex body is
nonempty and compact; the second is `PrismNDim.subset_selfHomothety` at `s = 3 ≥ 1`. -/
theorem subset_dilateTestBody {n : ℕ} (hn : finrank ℝ E = n) (K : ConvexSpaceBody E) :
    K ≤ (outerPrismBody hn K).toConvexSpaceBody ∧
      (outerPrismBody hn K).toConvexSpaceBody ≤ (dilateTestBody hn K).toConvexSpaceBody := by
  constructor
  · rw [SetLike.le_def]
    change K.carrier ⊆ (outerPrismBody hn K).carrier
    simpa [outerPrismBody] using (outerPrism.self_subset hn K.isCompact' K.nonempty')
  · rw [SetLike.le_def]
    change (outerPrismBody hn K).carrier ⊆ (dilateTestBody hn K).carrier
    simpa [dilateTestBody] using
      (PrismNDim.subset_selfHomothety (outerPrismBody hn K) (s := 3)
        (by norm_num : (1 : ℝ≥0) ≤ 3))

/-- **The prism test body absorbs the `2`-dilate of every tube it contains** (blueprint
`lem:ml1bootDilateTestBodyAbsorbs`).

For a convex body `K ⊆ ℝⁿ`, `P = outerPrism K` and a tube `T` of **any** scale `δ` with
`T ⊆ K`,

`2 · T ⊆ 3 · P`,

where `2 · T = Kakeya.Tube.dilate T 2` is the `2`-dilate of `T` about its centre.

There is no hypothesis on `δ` — not even `0 < δ` — no relation between `δ` and the dimensions of
`K` is required, and `T` is not assumed to be centrally placed in `K`.  The centre of `T` is by
definition the midpoint of its core, whose endpoints lie in `T ⊆ K ⊆ P` by
`Tube.x_mem_carrier` and `Tube.y_mem_carrier`; a prism being convex, the centre
lies in `P` as well, and `PrismNDim.homothety_two_mem_selfHomothety` concludes. -/
theorem dilate_tube_subset_dilateTestBody [Nontrivial E] {n : ℕ} (hn : finrank ℝ E = n)
    (K : ConvexSpaceBody E) {δ : NNReal} (T : Tube δ E) (hT : T.toConvexSpaceBody ≤ K) :
    Tube.dilate T 2 ≤ (dilateTestBody hn K).toConvexSpaceBody := by
  let P := (outerPrismBody hn K)
  let Pc : ConvexSpaceBody E := P.toConvexSpaceBody
  have hK : K ≤ Pc := by
    simpa [P, Pc] using (subset_dilateTestBody hn K).1
  have hx : T.x ∈ Pc := hK (by simpa using hT (Tube.x_mem_carrier T))
  have hy : T.y ∈ Pc := hK (by simpa using hT (Tube.y_mem_carrier T))
  have hc : T.center ∈ Pc := by
    change midpoint ℝ T.x T.y ∈ Pc.carrier
    exact (Pc.convex.midpoint_mem hx hy)
  rw [SetLike.le_def]
  intro z
  simp only [Tube.dilate]
  rintro ⟨w, hw, rfl⟩
  have hwP : w ∈ Pc := hK (by simpa using hT hw)
  exact PrismNDim.homothety_two_mem_selfHomothety P (x := w) (z := T.center) hwP hc

/-- In a subsingleton real space the whole-space measure has mass `1`. -/
private lemma volume_univ_subsingleton [Subsingleton E] :
    volume (Set.univ : Set E) = 1 := by
  have h_dim0 : finrank ℝ E = 0 := Module.finrank_zero_of_subsingleton
  haveI : IsEmpty (Fin (finrank ℝ E)) := by
    rw [h_dim0]
    infer_instance
  let b : Basis (Fin (finrank ℝ E)) ℝ E := (stdOrthonormalBasis ℝ E).toBasis
  have hpar_singleton : parallelepiped b = {(0 : E)} := by
    ext x
    simp [parallelepiped]
  calc
    volume (Set.univ : Set E) = b.addHaar (Set.univ : Set E) := rfl
    _ = b.addHaar {(0 : E)} := by
      have h_univ_singleton : (Set.univ : Set E) = {(0 : E)} := by
        ext x
        simp [Subsingleton.elim x 0]
      rw [h_univ_singleton]
    _ = b.addHaar (parallelepiped b) := by rw [hpar_singleton]
    _ = 1 := b.addHaar_self

/-- **Volume of the prism test body** (blueprint `lem:ml1bootDilateTestBodyVolume`).

For a convex body `K ⊆ ℝⁿ` and `P = outerPrism K`,

`|3 · P| = 3 ^ n |P| ≤ 3 ^ n · Metric.volume_outerPrism_le_volume_self.C n · |K|`.

The equality is `PrismNDim.carrier_homothety` (the ratio `3` being positive) followed by
`Kakeya.ConvexSpaceBody.volume_homothety`; the inequality bounds `|P|` by
`Metric.volume_outerPrism_le_volume_self`. -/
theorem volume_dilateTestBody_le {n : ℕ} (hn : finrank ℝ E = n) (K : ConvexSpaceBody E) :
    volume (dilateTestBody hn K).carrier = 3 ^ n * volume (outerPrismBody hn K).carrier ∧
      volume (dilateTestBody hn K).carrier
        ≤ 3 ^ n * (Metric.volume_outerPrism_le_volume_self.C n : ℝ≥0∞) * volume K.carrier := by
  by_cases htriv : Nontrivial E
  · haveI : Nontrivial E := htriv
    let P : PrismNDim n E E := outerPrismBody hn K
    have hP : P = outerPrismBody hn K := rfl
    -- |3 · P| = 3 ^ n · |P| via `PrismNDim.carrier_homothety` + Haar scaling.
    have hvol : volume (dilateTestBody hn K).carrier = (3 : ℝ≥0∞) ^ n * volume P.carrier := by
      rw [hP, dilateTestBody]
      change volume ((P.homothety P.center (3 : ℝ≥0)).carrier : Set E) =
          (3 : ℝ≥0∞) ^ n * volume (P.carrier : Set E)
      rw [PrismNDim.carrier_homothety P P.center (by norm_num : 0 < (3 : ℝ≥0))]
      change volume (AffineMap.homothety P.center (3 : ℝ) '' (P.carrier : Set E)) =
          (3 : ℝ≥0∞) ^ n * volume (P.carrier : Set E)
      rw [MeasureTheory.Measure.addHaar_image_homothety (μ := (volume : Measure E))
        P.center (3 : ℝ) (P.carrier : Set E)]
      rw [hn]
      norm_num [abs_of_nonneg, ENNReal.ofReal_pow]
    -- |P| ≤ C(n) · |K|.
    have hPle : volume (outerPrism (V := E) hn K.isCompact' K.nonempty').carrier
        ≤ (Metric.volume_outerPrism_le_volume_self.C n : ℝ≥0∞) * volume K.carrier :=
      Metric.volume_outerPrism_le_volume_self hn (X := K.carrier) K.convex K.isCompact'
        K.nonempty'
    constructor
    · exact hvol
    · rw [hvol]
      calc
        (3 : ℝ≥0∞) ^ n * volume (outerPrism (V := E) hn K.isCompact' K.nonempty').carrier
            ≤ (3 : ℝ≥0∞) ^ n *
                ((Metric.volume_outerPrism_le_volume_self.C n : ℝ≥0∞) * volume K.carrier) := by
            exact mul_le_mul_right hPle ((3 : ℝ≥0∞) ^ n)
        _ = (3 : ℝ≥0∞) ^ n * (Metric.volume_outerPrism_le_volume_self.C n : ℝ≥0∞) *
              volume K.carrier := by
            rw [← mul_assoc]
  · haveI : Subsingleton E := not_nontrivial_iff_subsingleton.mp htriv
    have hn0 : n = 0 := by rw [← hn]; exact Module.finrank_zero_of_subsingleton
    have hD : (dilateTestBody hn K).carrier = Set.univ := (dilateTestBody hn K).nonempty'.eq_univ
    have hOP : (outerPrismBody hn K).carrier = Set.univ := (outerPrismBody hn K).nonempty'.eq_univ
    have hK : K.carrier = Set.univ := K.nonempty'.eq_univ
    have hC0 : (Metric.volume_outerPrism_le_volume_self.C 0 : ℝ≥0∞) = 1 := by
      norm_num [Metric.volume_outerPrism_le_volume_self.C, Metric.volume_comparison.C]
    constructor
    · rw [hD, hOP, hn0, volume_univ_subsingleton]
      norm_num
    · rw [hD, hK, hn0, volume_univ_subsingleton, hC0]
      norm_num

end TestBody

end ml1Boot

end Kakeya
