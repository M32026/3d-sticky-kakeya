/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineDefectConstantLedger
public import Kakeya.MultiScaleFac.Homogenize

/-!
# `A1` — the source's simultaneous refinement is already available, at the ambient constant

(c)/§6 and   The refined source's device
(l.4055-4060, l.5860-5878) is *one* joint dyadic selection whose output family has its statistics
pinned within a factor two at every level, and whose retained family **inherits the same tower**
(l.4104-4108).  The tree's reading of "inherits the same tower" is
`Tube.UniformTubeSet.restrictOccupied`, whose one debt is
`Kakeya.ML2Core.IsClassHomogeneousOn`; and the producer of the factor-two band is the existing
`Kakeya.Homogenize.exists_classBand_pass_of_uniformTubeSet`, which returns

```
 2 ^ cnt a ≤ (coverClass t' (assign a) j).card ≤ 2 * 2 ^ cnt a
```

on the **occupied** nodes `t'.image (assign a)` — exactly the index set
`Kakeya.ML2Core.IsClassHomogeneousOn` quantifies over.

**The point of this file is the arithmetic of the constant.**  With `bN a := (2 ^ cnt a : ℝ≥0)`
the two halves of `IsClassHomogeneousOn` read

```
 upper :  #class ≤ 2 * 2 ^ cnt a = 2 * bN a ≤ Cu * bN a        (needs `2 ≤ Cu`)
 lower :  bN a = 2 ^ cnt a ≤ #class ≤ Cu * #class              (needs `1 ≤ Cu`)
```

so the pass re-establishes the clause at the **ambient** `Cu`, with **no constant growth at all**.
That is what makes the device affordable, and it is the single fact  rests on:
`Kakeya.ML2Core.not_reentry_le` is the record that the *`GridUniform`* homogenizing pass
`Kakeya.Homogenize.exists_homogenizing_pass_gridUniform` squares `Cu` per re-entry, but that is a
statement about **that** pass, whose output constant is `gridUniformBandConst C 2`.  The
`Tube.UniformTubeSet` pass used here returns the band at the absolute constant `2` and never
touches `Cu`.

## Contents

* `Kakeya.ML2Core.isClassHomogeneousOn_of_classBand` — the arithmetic, at `2 ≤ Cu`.
* `Kakeya.ML2Core.exists_classHomogeneous_pass_of_uniformTubeSet` — `A1` proper: the existing pass,
  composed, delivering `IsClassHomogeneousOn` at the ambient `Cu` together with the pass's own
  polylogarithmic cardinality retention.
* `Kakeya.ML2Core.exists_classHomogeneous_restrictOccupied` — the same, handed on as the restricted
  hierarchy at the *same* `Cu` (the corollary the floor route actually consumes).
* **Firing controls**:
  * `Kakeya.ML2Core.classBand_upper_not_of_one` — at `Cu = 1` the pass's upper half does **not**
    imply `IsClassHomogeneousOn`'s upper half, so the hypothesis `2 ≤ Cu` is load-bearing and `A1`
    is not a vacuous cast;
  * `Kakeya.ML2Core.classBand_lower_not_of_lt_one` — the lower half likewise fails below `1`;
  * `Kakeya.ML2Core.isClassHomogeneousOn_of_classBand_sharp` — the constant `2` is *sharp* for the
    upper half: the hypothesis cannot be weakened to `c ≤ Cu` for any `c < 2`.
-/

open MeasureTheory Metric ConvexSpaceBody
open scoped NNReal ENNReal

@[expose] public section

namespace Kakeya.ML2Core

section ClassBand

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} {δ Cu : NNReal} {u : Finset ι} {T : ι → Tube δ E}

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
open scoped Classical in
/-- **`A1`, the arithmetic half.**  The factor-two class band on the occupied nodes gives
`Kakeya.ML2Core.IsClassHomogeneousOn` at the **ambient** constant `Cu`, as soon as `2 ≤ Cu`.

This is the shape `Kakeya.Homogenize.exists_classBand_pass_of_uniformTubeSet` returns at
`Mg := Tube.ssfGridLen δ`, transcribed with `bN a := (2 ^ cnt a : ℝ≥0)`.  Both halves are one
inequality each; **no constant is created**, which is the whole content of  -/
theorem isClassHomogeneousOn_of_classBand
    (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu) (h2Cu : 2 ≤ Cu)
    {S : Finset ι} {cnt : ℕ → ℕ}
    (hband : ∀ a ≤ Tube.ssfGridLen δ, ∀ j ∈ S.image (𝒰.cover.assign a),
      2 ^ cnt a ≤ (Tube.coverClass S (𝒰.cover.assign a) j).card ∧
        (Tube.coverClass S (𝒰.cover.assign a) j).card ≤ 2 * 2 ^ cnt a) :
    IsClassHomogeneousOn 𝒰 S := by
  classical
  refine ⟨fun k => (2 : ℝ≥0) ^ cnt k, fun k hk j hj => ?_⟩
  obtain ⟨hlow, hup⟩ := hband k hk j hj
  have hlow' : (2 : ℝ≥0) ^ cnt k
      ≤ ((Tube.coverClass S (𝒰.cover.assign k) j).card : ℝ≥0) := by
    exact_mod_cast (Nat.cast_le (α := ℝ≥0)).mpr hlow
  have hup' : ((Tube.coverClass S (𝒰.cover.assign k) j).card : ℝ≥0)
      ≤ 2 * (2 : ℝ≥0) ^ cnt k := by
    have := (Nat.cast_le (α := ℝ≥0)).mpr hup
    push_cast at this
    exact this
  refine ⟨hup'.trans (by gcongr), ?_⟩
  refine hlow'.trans ?_
  exact le_mul_of_one_le_left (by simp) (le_trans one_le_two h2Cu)

open scoped Classical in
/-- **`A1`.**  The existing class-band pass, composed with the arithmetic above: every hierarchy at a
constant `Cu ≥ 2` has a subfamily which retains all but a polylogarithmic share of the members and
on which `Kakeya.ML2Core.IsClassHomogeneousOn` holds **at the same `Cu`**.

This is the tree's form of the refined source's "a simultaneous refinement … retains at least
`Λ_f^{-1}` of that mass" (l.4057-4058) together with "the retained family inherits the same tower"
(l.4104-4108) — in *cardinality*, which is what the existing pass is weighted by.  Converting the
cardinality retention into the source's mass retention is a separate step and needs the trial's
`ML2Shaded.HasDenseShading` / `ML2Shaded.HasComparableDensities` binders; see

The threshold `δ₀` is the pass's own, and `Cu` is quantified **after** it, so no `δ`-free ceiling on
`Cu` is needed — contrast `Kakeya.ML2Core.not_reentry_le`. -/
theorem exists_classHomogeneous_pass_of_uniformTubeSet
    (hn : Module.finrank ℝ E = 3) :
    ∃ δ₀ : NNReal, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → δ ≤ δ₀ →
      ∀ (Cu : NNReal), 2 ≤ Cu →
      ∀ (t : Finset ι) (T : ι → Tube δ E),
      (∀ i ∈ t, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      (t : Set ι).Pairwise (fun i j ↦ IsEssentiallyDistinct ((T i).carrier) ((T j).carrier)) →
      ∀ 𝒰 : Tube.UniformTubeSet t T (Tube.ssfGridLen δ) Cu,
      ∃ t' ⊆ t,
        (t.card : ℝ)
            ≤ (1 - Real.log (δ : ℝ))
                ^ (2 * ((Tube.ssfGridLen δ + 2) * (Tube.ssfGridLen δ + 1))) * (t'.card : ℝ) ∧
          IsClassHomogeneousOn 𝒰 t' := by
  obtain ⟨δ₀, hδ₀pos, hδ₀le, hpass⟩ :=
    Kakeya.Homogenize.exists_classBand_pass_of_uniformTubeSet.{u} (E := E) hn
  refine ⟨δ₀, hδ₀pos, hδ₀le, ?_⟩
  intro ι δ hδ hδ0 Cu h2Cu t T hball hED 𝒰
  obtain ⟨t', ht', hloss, cnt, hband⟩ :=
    hpass hδ hδ0 (Tube.ssfGridLen δ) Cu t T hball hED 𝒰
  exact ⟨t', ht', hloss, isClassHomogeneousOn_of_classBand 𝒰 h2Cu hband⟩

open scoped Classical in
/-- **`A1`, in the form the floor route consumes**: the refined family carries the whole hierarchy
at the **same** constant `Cu`, via `Tube.UniformTubeSet.restrictOccupied`.

 `C-M1b`: `restrictOccupied` is **not** the identity at `S = t` — its index set is
`t.image (assign k)`, only *contained* in the ambient one — so the direction argument for any
statement re-cut onto it goes through `Kakeya.ML2Core.restrictOccupied_cover`'s two clauses and not
through an equality. -/
theorem exists_classHomogeneous_restrictOccupied
    (hn : Module.finrank ℝ E = 3) :
    ∃ δ₀ : NNReal, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → δ ≤ δ₀ →
      ∀ (Cu : NNReal), 2 ≤ Cu →
      ∀ (t : Finset ι) (T : ι → Tube δ E),
      (∀ i ∈ t, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      (t : Set ι).Pairwise (fun i j ↦ IsEssentiallyDistinct ((T i).carrier) ((T j).carrier)) →
      ∀ 𝒰 : Tube.UniformTubeSet t T (Tube.ssfGridLen δ) Cu,
      ∃ (t' : Finset ι) (_ : t' ⊆ t) (_ : IsClassHomogeneousOn 𝒰 t'),
        (t.card : ℝ)
            ≤ (1 - Real.log (δ : ℝ))
                ^ (2 * ((Tube.ssfGridLen δ + 2) * (Tube.ssfGridLen δ + 1))) * (t'.card : ℝ) ∧
          Nonempty (Tube.UniformTubeSet t' T (Tube.ssfGridLen δ) Cu) := by
  obtain ⟨δ₀, hδ₀pos, hδ₀le, hA1⟩ :=
    exists_classHomogeneous_pass_of_uniformTubeSet.{_, u} (E := E) hn
  refine ⟨δ₀, hδ₀pos, hδ₀le, ?_⟩
  intro ι δ hδ hδ0 Cu h2Cu t T hball hED 𝒰
  obtain ⟨t', ht', hloss, hhom⟩ := hA1 hδ hδ0 Cu h2Cu t T hball hED 𝒰
  exact ⟨t', ht', hhom, hloss, ⟨𝒰.restrictOccupied ht' hhom⟩⟩

end ClassBand

/-! ### Firing controls

 requires that `A1` be run with a control: without one, "the pass's band
gives `IsClassHomogeneousOn`" is indistinguishable from a vacuous cast.  The three below are the
smallest statements that fire, and they fire on the *hypothesis* `2 ≤ Cu` rather than on prose. -/

section Controls

/-- **Firing control 1 for `A1`.**  At `Cu = 1` the pass's upper half `#class ≤ 2 * bN` does **not**
give `Kakeya.ML2Core.IsClassHomogeneousOn`'s upper half `#class ≤ Cu * bN`.  Witness: a class of
size `2` sitting in the band at `bN = 1` (i.e. `cnt = 0`), which the pass's output permits and
`IsClassHomogeneousOn` at `Cu = 1` forbids.  So `2 ≤ Cu` is load-bearing. -/
theorem classBand_upper_not_of_one :
    ∃ c b : ℝ≥0, c ≤ 2 * b ∧ ¬ c ≤ (1 : ℝ≥0) * b :=
  ⟨2, 1, by norm_num, by norm_num⟩

/-- **Firing control 2 for `A1`.**  The lower half needs `1 ≤ Cu`; below `1` it fails even with the
band in hand. -/
theorem classBand_lower_not_of_lt_one :
    ∃ c b : ℝ≥0, b ≤ c ∧ ¬ b ≤ (1 / 2 : ℝ≥0) * c :=
  ⟨1, 1, le_rfl, by norm_num⟩

/-- **Firing control 3 for `A1`: the constant `2` is sharp.**  The hypothesis `2 ≤ Cu` cannot be
weakened to `c ≤ Cu` for any `c < 2`: the pass's band alone permits `#class = 2 * bN`, so any `Cu`
strictly below `2` leaves a node whose class violates `IsClassHomogeneousOn`'s upper half. -/
theorem isClassHomogeneousOn_of_classBand_sharp {Cu : ℝ≥0} (hCu : Cu < 2) :
    ∃ c b : ℝ≥0, c ≤ 2 * b ∧ ¬ c ≤ Cu * b := by
  refine ⟨2, 1, by norm_num, ?_⟩
  rw [mul_one]
  exact not_le.mpr hCu

end Controls

end Kakeya.ML2Core
