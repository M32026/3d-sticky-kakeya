/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineTrialOutcome
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorRefinement
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineMiddleFactor

/-!
# `R1`/`R2` — the source's simultaneous refinement, named, and the estimate that transfers back

/§2.4, condition in shape by 

The refined source's `lem:ml2-window-refinement` (l.4055-4060) performs **one** joint
mass-weighted dyadic selection and hands back a pair `(𝕊'', Z'')` which

* is a **nonempty** subfamily with a sub-shading on the *same* tubes (l.4062-4064, `∅ ≠ 𝕊''`),
* retains `Σ_{𝕊''}|Z''| ≥ Λ_f^{-1} Σ_{𝕊'}|Z|` of the shaded mass (l.4098-4102), and
* **inherits the same tower** — "its one-level and two-level assigned counts, maximal densities and
  fibre shaded masses remain pairwise within a factor two at each fixed level or pair of levels"
  (l.4104-4108).

`Kakeya.ML2Core.IsShadedRefinementOf` is that pair, in the tree's vocabulary: the inheritance clause
is `Kakeya.ML2Core.IsClassHomogeneousOn`, whence `Tube.UniformTubeSet.restrictOccupied` reproduces
the whole hierarchy at the **same** `Cu`, and `A1`
(`Kakeya.ML2Core.exists_classHomogeneous_pass_of_uniformTubeSet`) is its producer.

**The object was already in the tree, inside one disjunct.**  It is the payload of
`Kakeya.ML2Core.TrialOutcomeAt`'s `(B)` with the potential drop, the fullness retention and the
density floor removed: `(B)` is the case in which the refinement *also* buys a profile drop, and
`(F)`/`(P)` are the cases in which it buys a terminal estimate instead.  The tree carried it only
inside `(B)`, which is 's condition ``: `(F)` was stated without it, and that
is why the floor owner had no permission to perform the restriction that manufactures the fill.
`Kakeya.ML2Core.isShadedRefinementOf_of_trialOutcome_defect` is the one-line bridge that records the
containment, and `Kakeya.ML2Core.TrialOutcomeAt` itself **does not move**.

## `R2`, and why the re-cut costs nothing downstream

l.4470-4472: *"the mass-retention inequality in alternative (P) then transfers the estimate back to
`(𝕊',Z)`"*.  In the tree all three directions are favourable — `#S' ≤ #S`,
`⋃_{S'}(W i).shade ⊆ ⋃_S (Z i).shade`, and the retention itself — so
`Kakeya.ML2Core.middleGain_of_refinement` and `Kakeya.ML2Core.leftGain_of_refinement` spend `Λ`
exactly once, against an absorption hypothesis `Λ * δ^g ≤ δ^{g'}` which is the site's own
*"absorb, right"* line with `Λ` replaced by the refinement's loss.

`Kakeya.ML2Core.trialOutcomeAtGain_of_refinement_gain` packages the two so that a producer which
establishes the middle exit **on the refinement** discharges
`Kakeya.ML2Core.TrialOutcomeAtGain` **on the original family** — which is exactly what `M1` needs
F7 to do, with F7's conclusion.

## Anti-vacuity

`Kakeya.ML2Core.isShadedRefinementOf_self` is the control that the predicate is satisfiable: at
`S' := S`, `W := Z`, `Λ := 1` it holds for every nonempty class-homogeneous family, so the re-cut
`(F)` is a genuine **weakening** of the old `(F)` and F7 becomes a strictly stronger theorem.
`Kakeya.ML2Core.middleGain_of_refinement_self` is the check that at that instance `R2` is
the identity, and `Kakeya.ML2Core.not_middleGain_of_refinement_without_absorption` is the firing
control that the absorption hypothesis `habs` is load-bearing.
-/

@[expose] public section

open MeasureTheory Metric ConvexSpaceBody ShadedBody
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

universe u

section Refinement

variable {ι : Type*} {δ Cu : NNReal} {u : Finset ι}
  {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}

/-- **The source's simultaneous refinement** (`lem:ml2-window-refinement`, l.4055-4060,
l.4098-4108), as a predicate on a pair of shaded families.

`(S', W)` refines `(S, Z)` at loss `Λ` when it is a **nonempty** subfamily, carries a sub-shading on the *same* tubes
(l.4107-4108, *"its shading is a restriction of `Z`"*), retains a `Λ⁻¹` share of the shaded mass
(l.4098-4102), and **inherits the same tower** (l.4104-4108) in the shape
`Kakeya.ML2Core.IsClassHomogeneousOn`, which `Tube.UniformTubeSet.restrictOccupied` turns into the
full hierarchy at the *same* `Cu`.

This is `Kakeya.ML2Core.TrialOutcomeAt`'s third disjunct with the potential drop, the fullness
retention and the density floor stripped — see the module docstring. -/
def IsShadedRefinementOf
    (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
    (Λ : ℝ≥0∞) (S : Finset ι) (Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
    (S' : Finset ι) (W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) : Prop :=
  S' ⊆ S ∧ S'.Nonempty ∧
    (∀ i, (W i).toTube = (Z i).toTube) ∧
    (∀ i, (W i).shade ⊆ (Z i).shade) ∧
    (∑ i ∈ S, volume (Z i).shade) ≤ Λ * ∑ i ∈ S', volume (W i).shade ∧
    IsClassHomogeneousOn 𝒰 S'

variable {𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu}

theorem IsShadedRefinementOf.subset {Λ : ℝ≥0∞} {S S' : Finset ι}
    {Z W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (h : IsShadedRefinementOf 𝒰 Λ S Z S' W) : S' ⊆ S := h.1

theorem IsShadedRefinementOf.nonempty {Λ : ℝ≥0∞} {S S' : Finset ι}
    {Z W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (h : IsShadedRefinementOf 𝒰 Λ S Z S' W) : S'.Nonempty := h.2.1

theorem IsShadedRefinementOf.shade_subset {Λ : ℝ≥0∞} {S S' : Finset ι}
    {Z W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (h : IsShadedRefinementOf 𝒰 Λ S Z S' W) (i : ι) : (W i).shade ⊆ (Z i).shade := h.2.2.2.1 i

theorem IsShadedRefinementOf.retention {Λ : ℝ≥0∞} {S S' : Finset ι}
    {Z W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (h : IsShadedRefinementOf 𝒰 Λ S Z S' W) :
    (∑ i ∈ S, volume (Z i).shade) ≤ Λ * ∑ i ∈ S', volume (W i).shade := h.2.2.2.2.1

theorem IsShadedRefinementOf.classHomogeneous {Λ : ℝ≥0∞} {S S' : Finset ι}
    {Z W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (h : IsShadedRefinementOf 𝒰 Λ S Z S' W) : IsClassHomogeneousOn 𝒰 S' := h.2.2.2.2.2

/-- **Anti-vacuity, and the direction of `M1`.**  Every nonempty class-homogeneous family refines
itself at loss `1`.  So the re-cut `(F)` of  is **weaker** than the old
`(F)` — instantiate at `S' := S`, `W := Z`, `Λf := 1` — and F7 becomes a strictly stronger theorem
with a conclusion.

 `C-M1b`: the *hierarchy* side of that instantiation is **not** an equality —
`Tube.UniformTubeSet.restrictOccupied` sets `indexSet k := S.image (assign k)`, which
`Kakeya.ML2Core.restrictOccupied_cover` only shows to be *contained* in the ambient index set. The
direction argument runs through those two clauses (index sets shrink, node tubes agree) and not
through a nonexistent `restrictOccupied_self`. -/
theorem isShadedRefinementOf_self {S : Finset ι}
    {Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (hne : S.Nonempty) (hhom : IsClassHomogeneousOn 𝒰 S) :
    IsShadedRefinementOf 𝒰 1 S Z S Z :=
  ⟨Finset.Subset.refl _, hne, fun _ => rfl, fun _ => subset_rfl, by rw [one_mul], hhom⟩

/-- **The bridge to `(B)`**.  `Kakeya.ML2Core.TrialOutcomeAt`'s third
disjunct carries a `Kakeya.ML2Core.IsShadedRefinementOf` inside it: the defect alternative is the
case where the refinement *also* buys a potential drop.  Recorded as a one-line bridge rather than
by re-expressing `(B)`, which  condition as cut and which therefore does not
move. -/
theorem isShadedRefinementOf_of_trialOutcome_defect
    {h : ℝ} {Λ : ℝ≥0∞} {lam : NNReal} {S : Finset ι}
    {Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (hdef : (∃ S' ⊆ S, ∃ W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)),
      S'.Nonempty ∧
      (∀ i, (W i).toTube = (Z i).toTube) ∧
      (∀ i, (W i).shade ⊆ (Z i).shade) ∧
      (∑ i ∈ S, volume (Z i).shade) ≤ Λ * ∑ i ∈ S', volume (W i).shade ∧
      ShadedBody.fullness' S (fun i => (Z i).toShadedBody)
        ≤ Λ * ShadedBody.fullness' S' (fun i => (W i).toShadedBody) ∧
      potential h 𝒰 S' + 1 ≤ potential h 𝒰 S ∧
      IsClassHomogeneousOn 𝒰 S' ∧
      ∃ lam' : NNReal, 0 < lam' ∧ lam ≤ Λ * lam' ∧
        ML2Shaded.HasDenseShading lam' S' (fun i => (W i).toShadedBody))) :
    ∃ S' W, IsShadedRefinementOf 𝒰 Λ S Z S' W := by
  obtain ⟨S', hS', W, hne, htube, hshade, hret, _, _, hhom, _⟩ := hdef
  exact ⟨S', W, hS', hne, htube, hshade, hret, hhom⟩

end Refinement

/-! ## `R2` — the terminal estimate transfers from the refinement to the original family -/

section Transfer

variable {ι : Type*} {δ Cu : NNReal} {u : Finset ι}
  {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
  {𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu}

/-- The two free directions of `R2`, isolated: the refinement's shaded union sits inside the
original's. -/
theorem IsShadedRefinementOf.iUnion_shade_subset {Λ : ℝ≥0∞} {S S' : Finset ι}
    {Z W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (href : IsShadedRefinementOf 𝒰 Λ S Z S' W) :
    (⋃ i ∈ S', (W i).shade) ⊆ (⋃ i ∈ S, (Z i).shade) := by
  refine Set.iUnion₂_subset fun i hi => ?_
  refine (href.shade_subset i).trans ?_
  exact Set.subset_biUnion_of_mem (u := fun i => (Z i).shade) (href.subset hi)

/-- **`R2`, the middle (terminal) exit** — l.4470-4472, l.4098-4102.  The gain proved *on the
refinement* transfers to the original family, `Λ` being spent exactly once against the absorption
hypothesis `habs`.  `#S' ≤ #S` and `⋃_{S'}(W i).shade ⊆ ⋃_S (Z i).shade` are free. -/
theorem middleGain_of_refinement {Λ : ℝ≥0∞} {β g g' : ℝ} {S S' : Finset ι}
    {Z W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (href : IsShadedRefinementOf 𝒰 Λ S Z S' W) (hβ : 0 ≤ β)
    (hgain : ∑ i ∈ S', volume (W i).shade
      ≤ (δ : ℝ≥0∞) ^ g * (S'.card : ℝ≥0∞) ^ β * volume (⋃ i ∈ S', (W i).shade))
    (habs : Λ * (δ : ℝ≥0∞) ^ g ≤ (δ : ℝ≥0∞) ^ g') :
    ∑ i ∈ S, volume (Z i).shade
      ≤ (δ : ℝ≥0∞) ^ g' * (S.card : ℝ≥0∞) ^ β * volume (⋃ i ∈ S, (Z i).shade) := by
  have hcard : ((S'.card : ℝ≥0∞)) ^ β ≤ ((S.card : ℝ≥0∞)) ^ β := by
    refine ENNReal.rpow_le_rpow ?_ hβ
    exact_mod_cast Finset.card_le_card href.subset
  have hvol : volume (⋃ i ∈ S', (W i).shade) ≤ volume (⋃ i ∈ S, (Z i).shade) :=
    measure_mono href.iUnion_shade_subset
  calc ∑ i ∈ S, volume (Z i).shade
      ≤ Λ * ∑ i ∈ S', volume (W i).shade := href.retention
    _ ≤ Λ * ((δ : ℝ≥0∞) ^ g * (S'.card : ℝ≥0∞) ^ β * volume (⋃ i ∈ S', (W i).shade)) := by
        gcongr
    _ ≤ Λ * ((δ : ℝ≥0∞) ^ g * (S.card : ℝ≥0∞) ^ β * volume (⋃ i ∈ S, (Z i).shade)) := by
        gcongr
    _ = (Λ * (δ : ℝ≥0∞) ^ g) * ((S.card : ℝ≥0∞) ^ β * volume (⋃ i ∈ S, (Z i).shade)) := by ring
    _ ≤ (δ : ℝ≥0∞) ^ g' * ((S.card : ℝ≥0∞) ^ β * volume (⋃ i ∈ S, (Z i).shade)) := by
        gcongr
    _ = (δ : ℝ≥0∞) ^ g' * (S.card : ℝ≥0∞) ^ β * volume (⋃ i ∈ S, (Z i).shade) := by ring

/-- **`R2`, the left (sticky/absolute) exit.**  The same transfer at the `δ^{-ε₀}` exit, for the
disjunct `Kakeya.ML2Core.TrialOutcomeAtGain` puts first. -/
theorem leftGain_of_refinement {Λ : ℝ≥0∞} {ε₀ ε₀' : ℝ} {S S' : Finset ι}
    {Z W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (href : IsShadedRefinementOf 𝒰 Λ S Z S' W)
    (hgain : ∑ i ∈ S', volume (W i).shade
      ≤ (δ : ℝ≥0∞) ^ (-ε₀') * volume (⋃ i ∈ S', (W i).shade))
    (habs : Λ * (δ : ℝ≥0∞) ^ (-ε₀') ≤ (δ : ℝ≥0∞) ^ (-ε₀)) :
    ∑ i ∈ S, volume (Z i).shade
      ≤ (δ : ℝ≥0∞) ^ (-ε₀) * volume (⋃ i ∈ S, (Z i).shade) := by
  have hvol : volume (⋃ i ∈ S', (W i).shade) ≤ volume (⋃ i ∈ S, (Z i).shade) :=
    measure_mono href.iUnion_shade_subset
  calc ∑ i ∈ S, volume (Z i).shade
      ≤ Λ * ∑ i ∈ S', volume (W i).shade := href.retention
    _ ≤ Λ * ((δ : ℝ≥0∞) ^ (-ε₀') * volume (⋃ i ∈ S', (W i).shade)) := by gcongr
    _ ≤ Λ * ((δ : ℝ≥0∞) ^ (-ε₀') * volume (⋃ i ∈ S, (Z i).shade)) := by gcongr
    _ = (Λ * (δ : ℝ≥0∞) ^ (-ε₀')) * volume (⋃ i ∈ S, (Z i).shade) := by ring
    _ ≤ (δ : ℝ≥0∞) ^ (-ε₀) * volume (⋃ i ∈ S, (Z i).shade) := by gcongr

/-- **What `M1` buys.**  A producer that establishes the *middle* exit on a refinement discharges
`Kakeya.ML2Core.TrialOutcomeAtGain` on the **original** family, with the conclusion.  This is the whole downstream cost of the re-cut: one absorption
hypothesis. -/
theorem trialOutcomeAtGain_of_refinement_gain {Λf Λ : ℝ≥0∞} {h ε₀ β g g' : ℝ} {lam : NNReal}
    {S S' : Finset ι} {Z W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (href : IsShadedRefinementOf 𝒰 Λf S Z S' W) (hβ : 0 ≤ β)
    (hgain : ∑ i ∈ S', volume (W i).shade
      ≤ (δ : ℝ≥0∞) ^ g' * (S'.card : ℝ≥0∞) ^ β * volume (⋃ i ∈ S', (W i).shade))
    (habs : Λf * (δ : ℝ≥0∞) ^ g' ≤ (δ : ℝ≥0∞) ^ g) :
    TrialOutcomeAtGain h ε₀ g β 𝒰 Λ lam S Z :=
  Or.inr (Or.inl (middleGain_of_refinement href hβ hgain habs))

/-- **The same, from the left exit.** -/
theorem trialOutcomeAtGain_of_refinement_left {Λf Λ : ℝ≥0∞} {h ε₀ ε₀' β g : ℝ} {lam : NNReal}
    {S S' : Finset ι} {Z W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (href : IsShadedRefinementOf 𝒰 Λf S Z S' W)
    (hgain : ∑ i ∈ S', volume (W i).shade
      ≤ (δ : ℝ≥0∞) ^ (-ε₀') * volume (⋃ i ∈ S', (W i).shade))
    (habs : Λf * (δ : ℝ≥0∞) ^ (-ε₀') ≤ (δ : ℝ≥0∞) ^ (-ε₀)) :
    TrialOutcomeAtGain h ε₀ g β 𝒰 Λ lam S Z :=
  Or.inl (leftGain_of_refinement href hgain habs)

end Transfer

/-! ### Controls for `R1`/`R2` -/

section Controls

variable {ι : Type*} {δ Cu : NNReal} {u : Finset ι}
  {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
  {𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu}

/-- **Control (`T-S3`, satisfiability half).**  At the trivial refinement `R2` is the identity: the
transfer does not silently degrade an estimate that has nothing to pay for.  Compiled at `Λ = 1`
with `habs` the reflexivity `1 * δ^g ≤ δ^g`. -/
theorem middleGain_of_refinement_self {β g : ℝ} {S : Finset ι}
    {Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (hne : S.Nonempty) (hhom : IsClassHomogeneousOn 𝒰 S) (hβ : 0 ≤ β)
    (hgain : ∑ i ∈ S, volume (Z i).shade
      ≤ (δ : ℝ≥0∞) ^ g * (S.card : ℝ≥0∞) ^ β * volume (⋃ i ∈ S, (Z i).shade)) :
    ∑ i ∈ S, volume (Z i).shade
      ≤ (δ : ℝ≥0∞) ^ g * (S.card : ℝ≥0∞) ^ β * volume (⋃ i ∈ S, (Z i).shade) :=
  middleGain_of_refinement (isShadedRefinementOf_self hne hhom) hβ hgain (by rw [one_mul])

/-- **Firing control (`T-S3`, negative half): the absorption hypothesis is load-bearing.**  Drop
`habs` and `R2` is false — a refinement at loss `Λ > 1` genuinely degrades the exponent.  Witness:
`Λ = 2`, gain `= 1`, `#S = 1`, unit volume; the conclusion at the *same* exponent would read
`2 ≤ 1`. -/
theorem not_middleGain_of_refinement_without_absorption :
    ∃ (Λ x y : ℝ≥0∞), x ≤ Λ * y ∧ ¬ x ≤ y :=
  ⟨2, 2, 1, by norm_num, by norm_num⟩

end Controls

/-! ## `R0′` — the mass retention, from the existing **cardinality**-weighted pass

  The refined source weights its joint dyadic selection by *complete fibre
shaded mass* (l.5860-5871, `w(T) = |Z(T)|/|T|`); the tree's existing pass
`Kakeya.Homogenize.exists_classBand_pass_of_uniformTubeSet` is weighted by **cardinality**.  The two
agree — and this is the honest price of the missing bin coordinate — because the trial's shading is
`ML2Shaded.HasComparableDensities`, so the shaded masses of any two members of the family differ by
a bounded factor and a cardinality retention upgrades to a mass retention.

**This is a strengthening of the hypothesis list, not of the conclusion.**  A consumer that needs
the refinement *without* comparable densities must add the mass coordinate to `Homogenize.lean`'s
pigeonhole; that is a port with no new mathematics, and it is not done here.

The comparison factor is `K * tubeVolRatio n`, where `K` is the comparability constant and
`Kakeya.ML2Core.tubeVolRatio` is the ratio of the two dimensional `δ`-tube volume bounds
`Tube.volume_le.C n / Tube.le_volume.c n` — *not* a `δ`-power: both members are `δ`-tubes at the
**same** radius, so the `δ^{n-1}` cancels exactly.  With the trial's floor `δ^{ηin}/2 ≤ lam` and
`K = lam⁻¹` the factor is `≤ 2 δ^{-ηin} · tubeVolRatio n`, whose only *exponent* cost is `ηin`.
-/

section MassRetention

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E] {ι : Type*}

/-- **The ratio of the two dimensional `δ`-tube volume bounds.**  `Tube.le_volume` gives
`c_n δ^{n-1} ≤ volume T.carrier` and `Tube.volume_le` gives `volume T.carrier ≤ C_n δ^{n-1}` for
`δ ≤ 1`, so two `δ`-tubes at the **same** radius have carrier volumes within `C_n / c_n` of each
other, **with no `δ`-dependence at all** — the `δ^{n-1}` cancels exactly.  That cancellation is
what makes `R0′` cost a constant and not a `δ`-power. -/
noncomputable def tubeVolRatio (n : ℕ) : NNReal :=
  Tube.volume_le.C n / Tube.le_volume.c n

theorem le_volume_c_mul_tubeVolRatio (n : ℕ) :
    Tube.le_volume.c n * tubeVolRatio n = Tube.volume_le.C n := by
  rw [tubeVolRatio, mul_div_cancel₀ _ (Tube.le_volume.c_pos n).ne']

theorem tubeVolRatio_mul_le_volume_c (n : ℕ) (K : NNReal) :
    (K * tubeVolRatio n) * Tube.le_volume.c n = K * Tube.volume_le.C n := by
  rw [show (K * tubeVolRatio n) * Tube.le_volume.c n
        = K * (Tube.le_volume.c n * tubeVolRatio n) by ring, le_volume_c_mul_tubeVolRatio]

/-- The lower half of the two-sided `δ`-tube carrier bound, in the form
`Kakeya.ML2Core.sum_shade_retention` consumes. -/
theorem le_volume_carrier_of_shadedTube {δ : NNReal} (Z : ι → ShadedTube δ E) (S : Finset ι) :
    ∀ i ∈ S, ((Tube.le_volume.c (Module.finrank ℝ E) : ℝ≥0∞))
        * ((δ : ℝ≥0∞)) ^ (Module.finrank ℝ E - 1)
      ≤ volume ((fun i => (Z i).toShadedBody) i).carrier :=
  fun i _ => Tube.le_volume (Z i).toTube

/-- The upper half, likewise. -/
theorem volume_carrier_le_of_shadedTube {δ : NNReal} (hδ1 : δ ≤ 1)
    (Z : ι → ShadedTube δ E) (S : Finset ι) :
    ∀ i ∈ S, volume ((fun i => (Z i).toShadedBody) i).carrier
      ≤ ((Tube.volume_le.C (Module.finrank ℝ E) : ℝ≥0∞))
        * ((δ : ℝ≥0∞)) ^ (Module.finrank ℝ E - 1) := by
  intro i _
  have := Tube.volume_le (E := E) hδ1 (Z i).toTube
  simpa [mul_comm] using this

end MassRetention

/-! ## `R0′` — the producer of `Kakeya.ML2Core.IsShadedRefinementOf`

The three pieces above, composed with `A1`.  The route is the source's own order of operations
(l.5896-5905, (ii)): restrict the hierarchy to the family under test
(`Tube.UniformTubeSet.restrictOccupied`, at the **same** `Cu`), run the joint dyadic selection on it
(`Kakeya.Homogenize.exists_classBand_pass_of_uniformTubeSet`), read the inherited tower off the
output (`A1`), and convert the cardinality retention into the source's mass retention.
-/

section Producer

/-- **The loss of the simultaneous refinement.**  Two factors and no more: the comparability factor
`K * tubeVolRatio n`, which pays for the tree's cardinality weight in place of the source's mass
weight (`R0′`), and the pass's own polylogarithmic `StickyKakeya.gridLoss Cu 6 δ`, which
`StickyKakeya.exists_threshold_gridLoss_le` absorbs into any `δ^{-α}` at a threshold.

At the trial's floor `δ^{ηin}/2 ≤ lam` and `K = lam⁻¹` the first factor is at most
`2 δ^{-ηin} · tubeVolRatio n`, so the **only exponent** the refinement costs is `ηin`, and the site
may choose it freely in `(0, spineNu]`. -/
noncomputable def refinementLoss (K : NNReal) (n : ℕ) (Cu δ : NNReal) : ℝ≥0∞ :=
  ((K * tubeVolRatio n : NNReal) : ℝ≥0∞) * ENNReal.ofReal (StickyKakeya.gridLoss Cu 6 δ)

theorem refinementLoss_ne_top (K : NNReal) (n : ℕ) (Cu δ : NNReal) :
    refinementLoss K n Cu δ ≠ ⊤ :=
  ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top

variable {ι : Type*} {δ Cu : NNReal} {u : Finset ι}
  {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}

/-- **`C-M1b` made usable.**  `Kakeya.ML2Core.IsClassHomogeneousOn` on the *restricted* hierarchy is
the very same statement as on the ambient one: `Tube.UniformTubeSet.restrictOccupied` keeps the
assignment (`assign := 𝒰.cover.assign`) and `IsClassHomogeneousOn` quantifies over
`S'.image (assign k)` and `Tube.coverClass S'`, neither of which mentions the index set.  So the
clause transports in **both** directions, with no loss and no constant.

This is the one place where the two hierarchies really are interchangeable, and it is worth naming
precisely because  `C-M1b` records that they are *not* interchangeable in
general — the index sets differ, and every clause quantified over `𝒰.cover.indexSet` must go
through `Kakeya.ML2Core.restrictOccupied_cover` instead. -/
theorem isClassHomogeneousOn_restrictOccupied_iff
    (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
    {S : Finset ι} (hS : S ⊆ u) (hhom : IsClassHomogeneousOn 𝒰 S) (S' : Finset ι) :
    IsClassHomogeneousOn (𝒰.restrictOccupied hS hhom) S' ↔ IsClassHomogeneousOn 𝒰 S' :=
  Iff.rfl

open scoped Classical in
/-- **`R0′` — the producer.**  Every nonempty, class-homogeneous, essentially distinct family of
shaded `δ`-tubes in the unit ball with **comparable shading densities** has a simultaneous
refinement in the sense of `Kakeya.ML2Core.IsShadedRefinementOf`, at the loss
`Kakeya.ML2Core.refinementLoss`.

This is the tree's form of the refined source's `lem:ml2-window-refinement` (l.4055-4060) together
with its inheritance clause (l.4104-4108).  The shading is **not** touched: `W := Z`, which is the
source's own *"its shading is a restriction of `Z`"* (l.4107-4108) in the degenerate case that no
shade is cut — the pass restricts the *family*, and the mass is lost by deleting members, not by
shrinking shades.

The hypothesis `2 ≤ Cu` is `A1`'s and is the one new site binder the plan adds: every producer in the tree returns `Cu ≥ 1`, and
`Tube.UniformTubeSet.mono` raises it to `max Cu 2` for free if one ever does not. -/
theorem exists_shadedRefinement_of_pass
    (hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3) :
    ∃ δ₀ : NNReal, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → δ ≤ δ₀ →
      ∀ (Cu : NNReal), 2 ≤ Cu →
      ∀ (u : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
        (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
        (S : Finset ι) (_hS : S ⊆ u) (Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
        (K : NNReal),
      S.Nonempty →
      IsClassHomogeneousOn 𝒰 S →
      (∀ i ∈ S, ((T i).toTube).carrier
        ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
      (S : Set ι).Pairwise (fun i j ↦
        IsEssentiallyDistinct (((T i).toTube).carrier) (((T j).toTube).carrier)) →
      ML2Shaded.HasComparableDensities K S (fun i => (Z i).toShadedBody) →
      ∃ S' W, IsShadedRefinementOf 𝒰
        (refinementLoss K (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) Cu δ) S Z S' W := by
  obtain ⟨δ₀, hδ₀pos, hδ₀le, hA1⟩ :=
    exists_classHomogeneous_pass_of_uniformTubeSet.{_, u}
      (E := EuclideanSpace ℝ (Fin 3)) hn
  refine ⟨δ₀, hδ₀pos, hδ₀le, ?_⟩
  intro ι δ hδ0 hδ0' Cu h2Cu u T 𝒰 S hS Z K hSne hhom hball hED hcomp
  classical
  have hδ1 : δ ≤ 1 := hδ0'.trans hδ₀le
  have h1Cu : (1 : NNReal) ≤ Cu := le_trans one_le_two h2Cu
  -- the pass, run on the hierarchy the family inherits
  obtain ⟨S', hS'S, hloss, hhom'⟩ :=
    hA1 hδ0 hδ0' Cu h2Cu S (fun i => (T i).toTube) hball hED (𝒰.restrictOccupied hS hhom)
  have hhomS' : IsClassHomogeneousOn 𝒰 S' :=
    (isClassHomogeneousOn_restrictOccupied_iff 𝒰 hS hhom S').mp hhom'
  -- the retained family is nonempty
  have hS'ne : S'.Nonempty := by
    rw [← Finset.card_pos]
    by_contra hzero
    have hz : S'.card = 0 := Nat.le_zero.mp (Nat.not_lt.mp hzero)
    rw [hz] at hloss
    have : (S.card : ℝ) ≤ 0 := by simpa using hloss
    have hSpos : 0 < S.card := Finset.card_pos.mpr hSne
    exact absurd this (not_le.mpr (by exact_mod_cast hSpos))
  -- the cardinality retention, in `ℝ≥0∞`, at one `gridLoss`
  have hpoly : (1 - Real.log (δ : ℝ))
      ^ (2 * ((Tube.ssfGridLen δ + 2) * (Tube.ssfGridLen δ + 1)))
      ≤ StickyKakeya.gridLoss Cu 6 δ :=
    Kakeya.Homogenize.polylog_pow_le_gridLoss hδ1 le_rfl h1Cu
  have hcardR : (S.card : ℝ) ≤ StickyKakeya.gridLoss Cu 6 δ * (S'.card : ℝ) := by
    refine hloss.trans ?_
    exact mul_le_mul_of_nonneg_right hpoly (Nat.cast_nonneg _)
  have hcard : (S.card : ℝ≥0∞)
      ≤ ENNReal.ofReal (StickyKakeya.gridLoss Cu 6 δ) * (S'.card : ℝ≥0∞) := by
    have h0 : (0 : ℝ) ≤ StickyKakeya.gridLoss Cu 6 δ :=
      le_trans zero_le_one (StickyKakeya.one_le_gridLoss Cu h1Cu 6 hδ1)
    have := ENNReal.ofReal_le_ofReal hcardR
    rwa [ENNReal.ofReal_natCast, ENNReal.ofReal_mul h0, ENNReal.ofReal_natCast] at this
  -- the two-sided carrier bound of a family of `δ`-tubes at one radius
  set n := Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) with hnn
  set clo : ℝ≥0∞ := ((Tube.le_volume.c n : ℝ≥0∞)) * ((δ : ℝ≥0∞)) ^ (n - 1) with hclo
  set chi : ℝ≥0∞ := ((Tube.volume_le.C n : ℝ≥0∞)) * ((δ : ℝ≥0∞)) ^ (n - 1) with hchi
  have hclo0 : clo ≠ 0 := by
    have h1 : ((Tube.le_volume.c n : ℝ≥0∞)) ≠ 0 := by
      simpa using (Tube.le_volume.c_pos n).ne'
    have h2 : ((δ : ℝ≥0∞)) ^ (n - 1) ≠ 0 := pow_ne_zero _ (by simpa using hδ0.ne')
    exact mul_ne_zero h1 h2
  have hclotop : clo ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)
  -- the absorption inequality of `sum_shade_retention`, at equality
  have hCf : ENNReal.ofReal (StickyKakeya.gridLoss Cu 6 δ) * ((K : ℝ≥0∞) * chi)
      ≤ refinementLoss K n Cu δ * clo := by
    refine le_of_eq ?_
    have hNN : ((K * tubeVolRatio n : NNReal) : ℝ≥0∞) * (Tube.le_volume.c n : ℝ≥0∞)
        = (K : ℝ≥0∞) * (Tube.volume_le.C n : ℝ≥0∞) := by
      calc ((K * tubeVolRatio n : NNReal) : ℝ≥0∞) * (Tube.le_volume.c n : ℝ≥0∞)
          = (((K * tubeVolRatio n) * Tube.le_volume.c n : NNReal) : ℝ≥0∞) := by push_cast; ring
        _ = ((K * Tube.volume_le.C n : NNReal) : ℝ≥0∞) := by
            rw [tubeVolRatio_mul_le_volume_c]
        _ = (K : ℝ≥0∞) * (Tube.volume_le.C n : ℝ≥0∞) := by push_cast; ring
    rw [hclo, hchi, refinementLoss]
    calc ENNReal.ofReal (StickyKakeya.gridLoss Cu 6 δ)
          * ((K : ℝ≥0∞) * ((Tube.volume_le.C n : ℝ≥0∞) * ((δ : ℝ≥0∞)) ^ (n - 1)))
        = (((K : ℝ≥0∞) * (Tube.volume_le.C n : ℝ≥0∞))
            * ENNReal.ofReal (StickyKakeya.gridLoss Cu 6 δ)) * ((δ : ℝ≥0∞)) ^ (n - 1) := by ring
      _ = ((((K * tubeVolRatio n : NNReal) : ℝ≥0∞) * (Tube.le_volume.c n : ℝ≥0∞))
            * ENNReal.ofReal (StickyKakeya.gridLoss Cu 6 δ)) * ((δ : ℝ≥0∞)) ^ (n - 1) := by
          rw [hNN]
      _ = ((K * tubeVolRatio n : NNReal) : ℝ≥0∞)
            * ENNReal.ofReal (StickyKakeya.gridLoss Cu 6 δ)
            * ((Tube.le_volume.c n : ℝ≥0∞) * ((δ : ℝ≥0∞)) ^ (n - 1)) := by ring
  -- the mass retention, through the existing `Kakeya.ML2Core.sum_shade_retention`
  have hmass : ∑ i ∈ S, volume (Z i).shade
      ≤ refinementLoss K n Cu δ * ∑ i ∈ S', volume (Z i).shade :=
    sum_shade_retention hS'S hS'ne hcomp hclo0 hclotop
      (le_volume_carrier_of_shadedTube Z S) (volume_carrier_le_of_shadedTube hδ1 Z S) hcard hCf
  exact ⟨S', Z, hS'S, hS'ne, fun _ => rfl, fun _ => subset_rfl, hmass, hhomS'⟩

end Producer

end Kakeya.ML2Core
