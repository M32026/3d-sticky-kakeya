/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineOuterTubes
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCountClause
public import Kakeya.DimensionThree.MainLemma2.CanonicalCentredCover

/-!
# The centring hand-back: the normalising similarity and the two Props of ′

This leaf sits **below** `Reduction/SpineCoreAssembly.lean`, which is where Lemma 9.1 is
eliminated (`fine_factor_of_lemma91At_of_canonicalCover`, the site ′) and which therefore has to *name* `CentredHandBack` in a binder.  The three declarations
were first written in `Reduction/SpineCentringCover.lean`, which imports `SpineCoreAssembly` and
so is on the wrong side of that edge; they are relocated here unchanged, and
`SpineCentringCover.lean` now imports this module.

Everything the two Props mention lives below `SpineCoreAssembly`: `outerFamily` and
`spineFamily`/`spineRescaleUnit` (`Reduction/SpineOuterTubes.lean`, `Reduction/SpineRescale.lean`),
`Tube.IsCentred` (`Kakeya/Tube/Basic.lean`, D0) and `Tube.IsRescalingSituation`
(`Kakeya/Tube/Rescale.lean`).

## Main declarations

* `Kakeya.VeryNotSticky.centringDilate` and `Kakeya.VeryNotSticky.normalise` — the anisotropic
  map of `eqanisotropicmap` (refined l.4765–4772) **at `ρ = 1`**, where it collapses to the
  similarity `x ↦ (x − m)/8`.
* `Kakeya.VeryNotSticky.CentredHandBack` — the eleven-field Prop.
* `Kakeya.VeryNotSticky.CountTransport` — the A7.
-/

@[expose] public section

open MeasureTheory Metric RealInnerProductSpace Kakeya.ML2Reduction
open scoped NNReal ENNReal

namespace Kakeya.VeryNotSticky

universe u

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E]

/-- **The anisotropic normalisation at `ρ = 1`** (refined `eqanisotropicmap`, l.4765–4772,
composed with l.6003–6005 "apply the anisotropic map with `ρ = 1`" at the fixed unit tube centred
at the origin).  At `ρ = 1` the map `L(x) = (1/8)(((x-m)·e)e + ρ⁻¹((x-m) - ((x-m)·e)e))` collapses
to `x ↦ (x - m)/8`, a **similarity** of ratio `1/8` — and `lemaffineinvariance` (l.4756–4758)
records that a similarity carries exact tubes to exact tubes and preserves line-based essential
distinctness.  Taken at `m = 0`. -/
noncomputable def centringDilate (x : E) : E := (8 : ℝ)⁻¹ • x

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  [ProperSpace E] in
theorem centringDilate_image_subset_ball {A : Set E} (hA : A ⊆ Metric.closedBall (0 : E) 1) :
    centringDilate '' A ⊆ Metric.closedBall (0 : E) (2 / 5) := by
  rintro y ⟨z, hz, rfl⟩
  have hzn : ‖z‖ ≤ 1 := by simpa using Metric.mem_closedBall.mp (hA hz)
  simp only [Metric.mem_closedBall, dist_zero_right, centringDilate, norm_smul, norm_inv,
    Real.norm_ofNat]
  rw [inv_mul_eq_div]
  linarith

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **The image of a tube lies in the `δ/8`-neighbourhood of the image line.**  The similarity
divides both the core's length and the radius by `8`; the direction is unchanged. -/
theorem centringDilate_image_subset_lineNbhd {δ : NNReal} (T : Tube δ E) :
    centringDilate '' T.carrier ⊆
      Metric.cthickening ((δ : ℝ) / 8)
        (Set.range fun t : ℝ ↦ centringDilate T.midpoint + t • T.direction) := by
  rintro y ⟨z, hz, rfl⟩
  rw [T.carrier_eq] at hz
  obtain ⟨w, hw, hzw⟩ := Set.mem_iUnion₂.mp hz
  obtain ⟨t, -, rfl⟩ := T.exists_param_of_mem_segment hw
  refine Metric.mem_cthickening_of_dist_le _
    (centringDilate T.midpoint + (t / 8) • T.direction) _ _ ⟨t / 8, rfl⟩ ?_
  have hd : dist z (T.midpoint + t • T.direction) ≤ (δ : ℝ) := Metric.mem_closedBall.mp hzw
  have hEq : centringDilate z - (centringDilate T.midpoint + (t / 8) • T.direction)
      = (8 : ℝ)⁻¹ • (z - (T.midpoint + t • T.direction)) := by
    unfold centringDilate; module
  rw [dist_eq_norm, hEq, norm_smul, norm_inv, Real.norm_ofNat, ← dist_eq_norm]
  rw [inv_mul_eq_div]
  linarith

/-- **The normalising similarity of the canonical cover** (refined l.4738–4772 at `ρ = 1`). -/
noncomputable def normalise (m x : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  (8 : ℝ)⁻¹ • (x - m)

theorem normalise_eq (m x : EuclideanSpace ℝ (Fin 3)) :
    normalise m x = centringDilate (x - m) := rfl

theorem normalise_image_eq (m : EuclideanSpace ℝ (Fin 3)) (A : Set (EuclideanSpace ℝ (Fin 3))) :
    normalise m '' A = centringDilate '' ((fun x ↦ x - m) '' A) := by
  rw [Set.image_image]; rfl

/-- **The tightened uniformity clause weakens to the existing loose one, by name.**

`Kakeya.ML2Reduction.Lemma91At`'s own `∃ C, 1 ≤ C ∧ C ≤ δ^{-ηd} ∧ …` clause is protected text
(`Reduction/SpineOuterTubes.lean`), and `4a`, caller 1, the eliminator and the companion keep it,
so a site holding the *named* constant discharges them through this — no bridge constant, the
witness is the constant itself.

**.**  The threshold conjunct is not a new cost: it is
`δ' ≤ (ssfUniformConst 3)^{-1/ηd}`, which is exactly what the loose bracket `C ≤ δ'^{-ηd}` was
quantifying away.  At the `ηd ≲ 2.4·10⁻⁹` the supplier actually delivers, that threshold is
astronomically small — which is the point: the cost was always there, and naming the constant
makes it visible instead of charging `ηd` for it at every reading. -/
theorem huni_loose_of_tight {δ' : NNReal} {ηd : ℝ} {α : Type u} {s' : Finset α}
    {U' : α → ShadedTube δ' (EuclideanSpace ℝ (Fin 3))}
    (h : ((ShadedTube.ssfUniformConst 3 : NNReal) : ENNReal) ≤ (δ' : ENNReal) ^ (-ηd) ∧
      Nonempty (ShadedTube.ShadedUniformTubeSet s' U' (Tube.ssfGridLen δ')
        (ShadedTube.ssfUniformConst 3))) :
    ∃ C : NNReal, 1 ≤ C ∧ (C : ENNReal) ≤ (δ' : ENNReal) ^ (-ηd) ∧
      Nonempty (ShadedTube.ShadedUniformTubeSet s' U' (Tube.ssfGridLen δ') C) :=
  ⟨ShadedTube.ssfUniformConst 3, ShadedTube.one_le_ssfUniformConst 3, h.1, h.2⟩

/-- **The centring hand-back**. -/
structure CentredHandBack {b δt δ' : NNReal} {R : ℝ}
    (hsit : Tube.IsRescalingSituation b δt δ' R 3) (hR : 0 < R)
    (T₀ : Tube b (EuclideanSpace ℝ (Fin 3))) (m : EuclideanSpace ℝ (Fin 3)) (qc : ℝ)
    {α : Type u} (fib s' : Finset α)
    (Z' : α → ShadedTube δt (EuclideanSpace ℝ (Fin 3)))
    (U' : α → ShadedTube δ' (EuclideanSpace ℝ (Fin 3))) : Prop where
  subset : s' ⊆ fib
  small : (δ' : ℝ) ≤ 1 / 20
  dens : Kakeya.maxDensity fib
      (fun i ↦ (outerFamily hsit.pos_ambient T₀ hR δ' Z' i).toConvexSpaceBody) ≤
    (δ' : ENNReal) ^ (-qc)
  full : (δ' : ENNReal) ^ qc ≤
    ShadedBody.fullness fib
      (fun i ↦ (outerFamily hsit.pos_ambient T₀ hR δ' Z' i).toShadedBody)
  centred : ∀ i ∈ s', (U' i).toTube.IsCentred
  contained : ∀ i ∈ s', (U' i).carrier ⊆ Metric.closedBall 0 1
  covers : ∀ i ∈ s',
    normalise m '' (outerFamily hsit.pos_ambient T₀ hR δ' Z' i).carrier ⊆ (U' i).carrier
  maxDensity_le : Kakeya.maxDensity s' (fun i ↦ (U' i).toConvexSpaceBody) ≤
    (δ' : ENNReal) ^ (-(2 * qc))
  fullness_ge : (δ' : ENNReal) ^ (3 * qc) ≤
    ShadedBody.fullness s' (fun i ↦ (U' i).toShadedBody)
  card_le : (s'.card : ENNReal) ≤ (fib.card : ENNReal)
  multiplicity_le : ShadedBody.multiplicity fib
      (fun i ↦ (outerFamily hsit.pos_ambient T₀ hR δ' Z' i).toShadedBody) ≤
    (δ' : ENNReal) ^ (-(3 * qc)) *
      ShadedBody.multiplicity s' (fun i ↦ (U' i).toShadedBody)


/-! ## the line-ED levels datum, sourced internally from `huni` -/

/-- **The emitter's line-ED levels constant** (§5.2(c)).

`Tube.lineEDLevelsAt_C3_activeRestrict_of_centred` returns its bound at
`⌈C · Tube.activeLineConstantAt n R₀ C₃⌉₊`.  On the route the middle factor actually takes, all
three arguments are **absolute**: `C` is the uniformiser's own
`ShadedTube.ssfUniformConst 3`, `n = 3`, `R₀ = 1` (the
canonical centred cover's reach `2/5 + ρ/4 ≤ 0.4125` is dominated by `1`, and the hand-back's
`contained` row puts every member of the subfamily in `B̄(0,1)`), and `C₃ =
Kakeya.Tube.tubeOverlapCoreClose.C 3`.  So the constant is a **number**, and it is named here
once and consumed by name — never re-inlined, so it cannot drift from the packing bound it
prices.

This is the tree's counterpart of the source's `2 · 641⁶`
(`Kakeya.VeryNotSticky.lineEDLevelConstant`): the same shape, a different numeral, because the
tree's `activeLineConstantAt` and `ssfUniformConst` are its own. -/
noncomputable def lineEDLevelsConstant : ℕ :=
  ⌈((ShadedTube.ssfUniformConst 3 : NNReal) : ℝ)
      * Tube.activeLineConstantAt 3 1 (Kakeya.Tube.tubeOverlapCoreClose.C 3)⌉₊

/-- The defining equation of `lineEDLevelsConstant`, exposed so that consumers never have to
re-inline the expression. -/
theorem lineEDLevelsConstant_eq :
    lineEDLevelsConstant
      = ⌈((ShadedTube.ssfUniformConst 3 : NNReal) : ℝ)
          * Tube.activeLineConstantAt 3 1 (Kakeya.Tube.tubeOverlapCoreClose.C 3)⌉₊ := rfl

/-- **The grid-separation row `4δ ≤ ρ_k` at the ssf grid length**, from the uniformiser's own
threshold `δ ≤ 16^{-N}` (`Kakeya.Tube.exists_threshold_polylog_pow_ssfGridLen_le`'s second
clause).  Half of `Tube.eight_delta_le_gridScale`; separated out because it is the one input of
the levels datum that is a **threshold on `δ'`** rather than a row already carried at the six
middle-factor sites. -/
theorem four_delta_le_gridScale_ssfGridLen {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hδ16 : δ ≤ (16 : NNReal) ^ (-(Tube.ssfGridLen δ : ℝ)))
    {k : ℕ} (hk : k < Tube.ssfGridLen δ) :
    4 * (δ : ℝ) ≤ (Tube.gridScale δ (Tube.ssfGridLen δ) k : ℝ) := by
  have h8 : 8 * δ ≤ Tube.gridScale δ (Tube.ssfGridLen δ) k :=
    Tube.eight_delta_le_gridScale hδ0 hδ1 hk hδ16
  have h8' : (8 : ℝ) * (δ : ℝ) ≤ (Tube.gridScale δ (Tube.ssfGridLen δ) k : ℝ) := by
    exact_mod_cast h8
  nlinarith [NNReal.coe_nonneg δ]

/-- **the ambient `LineEDLevelsAt C₃ A 𝒰` row, derived instead of assumed.**

 measured that the floor block never constructs the middle factor,
so the eight ambient `LineEDLevelsAt` *fields* it used to carry could not be discharged where they
sat.  They are removed there  and the datum is produced **here**, from the uniformity
witness the middle factor already holds: `Tube.lineEDLevelsAt_C3_activeRestrict_of_centred`
applied to `𝒱.tubeUniform`, at the named constant `lineEDLevelsConstant`.

The four inputs are named, not invented:

* `hδ0` — the site's own `hδ'0`;
* `hcen` — the hand-back's `centred` row (`CentredHandBack.centred`);
* `hball` — the hand-back's `contained` row, which is exactly `R₀ = 1`
  (`Tube.norm_midpoint_le_of_subset_ball`);
* `hδ16` — the ssf uniformiser's own grid threshold, through
  `four_delta_le_gridScale_ssfGridLen`.

No new geometry: the whole content is that a *uniform* hierarchy on a *centred* family of bounded
reach is line-essentially distinct level by level, which is §9 A6. -/
theorem lineEDLevelsAt_C3_of_shadedUniform {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hδ16 : δ ≤ (16 : NNReal) ^ (-(Tube.ssfGridLen δ : ℝ)))
    {α : Type u} {s : Finset α} {U : α → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (hcen : ∀ i ∈ s, (U i).toTube.IsCentred)
    (hball : ∀ i ∈ s, (U i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (𝒱 : ShadedTube.ShadedUniformTubeSet s U (Tube.ssfGridLen δ)
      (ShadedTube.ssfUniformConst 3)) :
    LineEDLevelsAt (Kakeya.Tube.tubeOverlapCoreClose.C 3) lineEDLevelsConstant
      𝒱.tubeUniform.activeRestrict := by
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have h := Tube.lineEDLevelsAt_C3_activeRestrict_of_centred hδ0 𝒱.tubeUniform hcen
    zero_le_one
    (fun i hi ↦ Tube.norm_midpoint_le_of_subset_ball hδ0 (U i).toTube (hball i hi))
    (fun k hk ↦ four_delta_le_gridScale_ssfGridLen hδ0 hδ1 hδ16 hk)
  rw [hn] at h
  exact h

/-- **The same datum, read off the folded `huni` conjunct at a middle-factor site.**

The six sites hold `huni` in the tightened form : a threshold
conjunct and a `Nonempty` uniformity witness at the *named* constant.  This is the levels row on
that witness, with `hδ1` supplied by the hand-back's own `small` row (`δ' ≤ 1/20`), so the only
input beyond `hδ0`, `hcb` and `huni` is the uniformiser's grid threshold `hδ16`. -/
theorem lineEDLevelsAt_C3_of_huni {b δt δ' : NNReal} {R : ℝ}
    {hsit : Tube.IsRescalingSituation b δt δ' R 3} {hR : 0 < R}
    {T₀ : Tube b (EuclideanSpace ℝ (Fin 3))} {mm : EuclideanSpace ℝ (Fin 3)} {qc ηd : ℝ}
    {α : Type u} {fib s' : Finset α}
    {Z' : α → ShadedTube δt (EuclideanSpace ℝ (Fin 3))}
    {U' : α → ShadedTube δ' (EuclideanSpace ℝ (Fin 3))}
    (hδ'0 : 0 < δ')
    (hδ16 : δ' ≤ (16 : NNReal) ^ (-(Tube.ssfGridLen δ' : ℝ)))
    (hcb : CentredHandBack hsit hR T₀ mm qc fib s' Z' U')
    (huni : ((ShadedTube.ssfUniformConst 3 : NNReal) : ENNReal) ≤ (δ' : ENNReal) ^ (-ηd) ∧
      Nonempty (ShadedTube.ShadedUniformTubeSet s' U' (Tube.ssfGridLen δ')
        (ShadedTube.ssfUniformConst 3))) :
    LineEDLevelsAt (Kakeya.Tube.tubeOverlapCoreClose.C 3) lineEDLevelsConstant
      huni.2.some.tubeUniform.activeRestrict :=
  lineEDLevelsAt_C3_of_shadedUniform hδ'0
    (by
      have := hcb.small
      exact_mod_cast this.trans (by norm_num))
    hδ16 hcb.centred hcb.contained huni.2.some
/-- **The centring cover's radius constant**.  The hand-back reads
the canonical cover of the *rescaled bodies* at a radius contracted by this fixed absolute factor.
It is a number, so the contraction is a threshold on `δ'`, never a change of exponent. -/
def centringCoverRadiusConstant : NNReal := 2

/-- **The fibre factor `F`**, named  and measured.

`hfibre` counts a **tube-dilate packing of normalised members**, so the bound is
`Tube.essDistinctTubesInSelfDilate.C` at the dilation ratio PRODUCER-4's pull-back lemma through
`normalise` needs.  That lemma has two hypotheses — `8 · Cn ≤ c₀` on the core and
`8 · C · Cn ≤ c₀` on the radius, with `C = centringCoverRadiusConstant` and
`Cn = Tube.tubeOverlapCoreClose.C 3` — and `c₀ = 16 · C · Cn` dominates both, with a factor of two
to spare.  Minimality is not required; what is required is that the expression be
*derived* from the bounds it pays for, and it is: both factors are named constants and no numeral
is chosen.  `δ'`-free, since neither named constant sees the scale.

**The `1 +` is the tree's own idiom, and it is not cosmetic.**
`Tube.essDistinctTubesInSelfDilate.C` carries no lower bound of its own — `Kakeya/Tube/
CoverCountComparable.lean:171–174` records exactly this, which is why `Tube.coverCountLossAt` and
`Kakeya.ML2Reduction.spineOuterCountLoss` are padded the same way — so `1 ≤ F` is available only
by padding, via `le_self_add`.  Consumers need `1 ≤ F` (it is what lets the transport drop the
factor), so the padding is load-bearing.

After this, both factors of `centringCountLossConstant R` are
`1 + essDistinctTubesInSelfDilate.C 3 _`
at different arguments: a two-stage packing price, one stage for the outer-core transport and one
for the subfamily.

**How big is it?**  `_eq` is an unfolding, so here is the magnitude in prose:
`Tube.essDistinctTubesInSelfDilate.C 3 c ≤ selfDilatePrefactor * c.toNNReal ^ 12` for `1 ≤ c`
(`Kakeya.VeryNotSticky.essDistinctTubesInSelfDilate_C_le`, `MainLemma2/SplitInputsFibreCount.lean`),
so `F ≤ 1 + selfDilatePrefactor · c₀¹²` at `c₀ = 16 · C · Cn`.  The lemma form of this estimate is
deferred: `SplitInputsFibreCount.lean` is on a different import branch, and pulling it into this
leaf for a courtesy bound would be a DAG change.

**The product is doubly padded, `(1 + A)(1 + B)`, and that is accepted and not to be tightened**
( addendum (S)).  Each `1 +` buys `1 ≤` for its own factor by
`le_self_add`, both are needed by their own consumers, and the cross terms are paid by the same
threshold that pays the product — so removing either padding would buy nothing and cost the free
`1 ≤`. -/
noncomputable def centringCoverFibreConstant : NNReal :=
  1 + Tube.essDistinctTubesInSelfDilate.C 3
      (16 * (centringCoverRadiusConstant : ℝ) * (Tube.tubeOverlapCoreClose.C 3 : ℝ))

theorem centringCoverFibreConstant_eq :
    centringCoverFibreConstant
      = 1 + Tube.essDistinctTubesInSelfDilate.C 3
          (16 * (centringCoverRadiusConstant : ℝ) * (Tube.tubeOverlapCoreClose.C 3 : ℝ)) := rfl

@[simp] theorem centringCoverFibreConstant_coe :
    (centringCoverFibreConstant : ℝ)
      = 1 + (Tube.essDistinctTubesInSelfDilate.C 3
          (16 * (centringCoverRadiusConstant : ℝ) * (Tube.tubeOverlapCoreClose.C 3 : ℝ)) : ℝ) := by
  simp [centringCoverFibreConstant]

theorem one_le_centringCoverFibreConstant : (1 : NNReal) ≤ centringCoverFibreConstant :=
  le_self_add

/-- **The centring transport's count-loss constant**.

The hypothesis side of the count transport names a **packing** bound, not the rescaling loss
`Kakeya.ML2Reduction.spineOuterCountLoss R`: the transport factors through the canonical cover's
node assignment, whose fibres are bounded by the cover's own ED constant and not by `1`, so
pairwise essential distinctness is recovered only after passing to one index per node.  That price
is absolute — it depends on the ambient dimension and on the reach `R₀`, not on the scale, not on
the tubes, not on `R` — so it is a threshold on the scale, never an exponent, and it is **defined
from the packing bound rather than chosen**, so it cannot drift from the fibre bound it pays for.

**`R`-dependent and δ-free.**  The `R`-dependent factor is `spineOuterCountLoss R` **by name**
and must never acquire a numeral; the numeral survives only in the `δ`-free packing factor.  `R`
is bounded below by `Tube.normalization.C 3` inside `Tube.IsRescalingSituation` and is not bounded
above anywhere in the tree, so no `R`-free upper bound on `spineOuterCountLoss R` exists and the
argument cannot be dropped.  Nothing here depends on the scale, so the clause it prices is still
**one threshold in `δ'`**.

**`R₀ = 1` dominates the reach** : `Kakeya.VeryNotSticky.exists_setCanonicalCentredCover`
produces nodes of reach `‖midpoint‖ ≤ 2/5 + ρ/4`, and at its own hypothesis `ρ ≤ 1/20` that is at
most `0.4125 ≤ 1`.  So `R₀ = 1` dominates with room, and it is the choice for which the constant
has an integer value, `2 · 641³ · 513³ ≈ 1.07 · 10¹⁶` (`centringCountLossConstant_eq`). -/
noncomputable def centringCountLossConstant (R : ℝ) : NNReal :=
  ML2Reduction.spineOuterCountLoss R * centringCoverFibreConstant

@[simp] theorem centringCountLossConstant_coe (R : ℝ) :
    (centringCountLossConstant R : ℝ)
      = (ML2Reduction.spineOuterCountLoss R : ℝ) * (centringCoverFibreConstant : ℝ) := rfl

theorem centringCountLossConstant_eq (R : ℝ) :
    (centringCountLossConstant R : ℝ)
      = (ML2Reduction.spineOuterCountLoss R : ℝ)
        * (1 + (Tube.essDistinctTubesInSelfDilate.C 3
            (16 * (centringCoverRadiusConstant : ℝ)
              * (Tube.tubeOverlapCoreClose.C 3 : ℝ)) : ℝ)) := by
  rw [centringCountLossConstant_coe, centringCoverFibreConstant_coe]

theorem one_le_centringCountLossConstant (R : ℝ) :
    (1 : NNReal) ≤ centringCountLossConstant R := by
  have h1 : (1 : NNReal) ≤ ML2Reduction.spineOuterCountLoss R := le_self_add
  have h2 := one_le_centringCoverFibreConstant
  calc (1 : NNReal) = 1 * 1 := (one_mul 1).symm
    _ ≤ ML2Reduction.spineOuterCountLoss R * centringCoverFibreConstant := by gcongr
    _ = centringCountLossConstant R := rfl

/-- **The ED-window contraction constant**, the
*hypothesis-side* name of the same number.  Every clause that must *supply* the contracted cover
is stated on a window whose lower endpoint is divided by this constant. -/
def edWindowContractionConstant : NNReal := centringCoverRadiusConstant

@[simp] theorem edWindowContractionConstant_eq_centringCoverRadiusConstant :
    edWindowContractionConstant = centringCoverRadiusConstant := rfl

theorem centringCoverRadiusConstant_pos : 0 < centringCoverRadiusConstant := by
  unfold centringCoverRadiusConstant; norm_num

/-- **`1 ≤ C`, by name.**  So no consumer proves it by `norm_num` on the literal `2`: if the
constant ever moves, every use of this moves with it. -/
theorem one_le_centringCoverRadiusConstant : (1 : NNReal) ≤ centringCoverRadiusConstant := by
  unfold centringCoverRadiusConstant; norm_num

theorem one_le_centringCoverRadiusConstant_coe :
    (1 : ℝ) ≤ (centringCoverRadiusConstant : ℝ) := by
  exact_mod_cast one_le_centringCoverRadiusConstant

theorem div_centringCoverRadiusConstant_le (ρ : NNReal) :
    ρ / centringCoverRadiusConstant ≤ ρ := NNReal.half_le_self ρ

theorem edWindowContractionConstant_pos : 0 < edWindowContractionConstant :=
  centringCoverRadiusConstant_pos

/-- **enabling step.**  Dividing only the *lower* endpoint by the constant puts every
contracted radius back inside the window, for every `ρ` of the original one.  Widening a lower
endpoint downwards can never empty an interval, so no new threshold on the scale is incurred. -/
theorem mem_widened_window_of_mem {δ' ρ : NNReal} {ϖ : ℝ}
    (hρ : ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ)) :
    ρ / centringCoverRadiusConstant
      ∈ Set.Icc (δ' ^ (1 - ϖ) / edWindowContractionConstant) (δ' ^ ϖ) := by
  refine ⟨?_, le_trans (div_centringCoverRadiusConstant_le ρ) hρ.2⟩
  rw [edWindowContractionConstant_eq_centringCoverRadiusConstant]
  gcongr
  exact hρ.1

/-- **input, as a threshold**.  `δ'^ϖ ≤ 1/2` holds
below an explicit scale for every `ϖ > 0` and needs nothing else, so the contracted-cover
producer's `hthr` is a threshold on the scale and never a per-site obligation: a consumer exhibits
it once, at `δ' ≤ (1/2)^{1/ϖ}`, and no per-site satisfiability argument is required. -/
theorem exists_threshold_rpow_le_half {ϖ : ℝ} (hϖ : 0 < ϖ) :
    ∃ δ₀ : NNReal, 0 < δ₀ ∧ ∀ δ' : NNReal, δ' ≤ δ₀ → δ' ^ ϖ ≤ 1 / 2 := by
  refine ⟨(1 / 2 : NNReal) ^ (1 / ϖ), NNReal.rpow_pos (by norm_num), ?_⟩
  intro δ' hδ'
  calc δ' ^ ϖ ≤ ((1 / 2 : NNReal) ^ (1 / ϖ)) ^ ϖ := NNReal.rpow_le_rpow hδ' hϖ.le
    _ = (1 / 2 : NNReal) ^ ((1 / ϖ) * ϖ) := (NNReal.rpow_mul _ _ _).symm
    _ = 1 / 2 := by rw [one_div_mul_cancel (ne_of_gt hϖ), NNReal.rpow_one]

/-- **The `Cf` route's β-threshold, recorded as arithmetic** ( (B)).

Caller 1 was once offered `hCf : (δ')^{-3qc} ≤ Cf` instead of `1 ≤ Cf`, i.e. the `3 qc` charged to
the loss ledger rather than to the gain.  That charge enters `hLoss` at rate `≈ 1.02/β` while the
spine's own ceiling on the multiscale loss is `κ ≤ η_k/(20 e)`, and the two cross well before the
small `β` the argument needs: at `β = 1/4` the charge is `4.08` against a ceiling of `0.05`.  The
numbers below are that crossing, and they are why the unprimed route charges the `3 qc` to the
gain (`hL91` at `gain(…) + 3 qc`, `hνqc := le_rfl`) and leaves `Cf` at `1 ≤ Cf`. -/
theorem cf_beta_threshold_record :
    ∃ β charge ceiling : ℝ,
      0 < β ∧ β ≤ 255 / 1000 ∧ charge = 102 / 100 * (1 / β) ∧ ceiling = 1 / 20 ∧
        ¬ charge ≤ ceiling :=
  ⟨1 / 4, 102 / 100 * (1 / (1 / 4)), 1 / 20, by norm_num, by norm_num, rfl, rfl, by norm_num⟩

/--   The widened bottom still dominates the thickness: `x ≤ x^{1-ϖ}/C` exactly when
`x^ϖ ≤ 1/C`, a threshold on the scale at fixed `ϖ > 0`.  The base is a bound variable, so this is
one lemma applied separately at `δ'` and at `σ`; nothing is transported between instances. -/
theorem le_div_rpow_one_sub {x : NNReal} (hx : 0 < x) {ϖ : ℝ}
    (hthr : x ^ ϖ ≤ 1 / 2) : x ≤ x ^ (1 - ϖ) / edWindowContractionConstant := by
  have hsplit : x ^ (1 - ϖ) * x ^ ϖ = x := by
    rw [← NNReal.rpow_add (ne_of_gt hx)]; simp
  have h : x ≤ x ^ (1 - ϖ) * (1 / 2) := by
    calc x = x ^ (1 - ϖ) * x ^ ϖ := hsplit.symm
      _ ≤ x ^ (1 - ϖ) * (1 / 2) := by gcongr
  rw [edWindowContractionConstant_eq_centringCoverRadiusConstant]
  simpa [centringCoverRadiusConstant, div_eq_mul_inv, mul_one_div] using h

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **A tube of larger radius on the same core contains it.**  Used to hand a cover at the
contracted radius back at the full radius. -/
theorem carrier_subset_mk' {δ ρ : NNReal} (T : Tube δ E) (h : δ ≤ ρ) :
    T.carrier ⊆ (Tube.mk' ρ T.dist_eq_one).carrier := by
  rw [T.carrier_eq_cthickening, (Tube.mk' ρ T.dist_eq_one).carrier_eq_cthickening]
  simp only [Tube.mk'_x, Tube.mk'_y]
  exact Metric.cthickening_mono (by exact_mod_cast h) _

/-- **A7 — the count clause transports to the centred representatives.**  An essentially distinct,
all-used `ρ`-cover of the *rescaled bodies* yields one of the *centred representatives*, at the same
radius and count.  Refined l.4780–4782 (`X_i ⊂ C_i`, axes within `r`) with l.4739–4761 (a similarity
carries exact tubes to exact tubes and preserves line-based essential distinctness).

Stated in the **consumer's** shape — the conclusion is `Kakeya.ML2Reduction.Lemma91At`'s count clause
at `(s', U')`, verbatim — because the earlier producer-shaped version (a thickened
pull-back) could not feed `count_clause_at_uniformised_of_canonicalCover`: the pull-back of a
`ρ`-tube has core `1/8`, and no thickening of it is a unit-core `ρ`-tube. -/
def CountTransport {b δt δ' : NNReal} {R : ℝ}
    (hsit : Tube.IsRescalingSituation b δt δ' R 3) (hR : 0 < R)
    (T₀ : Tube b (EuclideanSpace ℝ (Fin 3))) (m : EuclideanSpace ℝ (Fin 3)) (ϖ ζ : ℝ)
    {α : Type u} (s' : Finset α)
    (Z' : α → ShadedTube δt (EuclideanSpace ℝ (Fin 3)))
    (U' : α → ShadedTube δ' (EuclideanSpace ℝ (Fin 3))) : Prop :=
  ∀ ρ : NNReal, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
    (∃ (κ₀ : Type u) (t : Finset κ₀)
        (W : κ₀ → Tube (ρ / centringCoverRadiusConstant) (EuclideanSpace ℝ (Fin 3))),
      ((t : Set κ₀).Pairwise
        fun j k ↦ _root_.IsEssentiallyDistinct (W j).carrier (W k).carrier) ∧
      (∀ j ∈ t, ∃ i ∈ s',
        (spineFamily (spineRescaleUnit hsit.pos_ambient T₀ hR) Z' i).toConvexSpaceBody
          ≤ (W j).toConvexSpaceBody) ∧
      (centringCountLossConstant R : ℝ)
        * ((ρ / centringCoverRadiusConstant : NNReal) : ℝ) ^ (-2 - ζ) ≤ (t.card : ℝ)) →
    (∃ (κ : Type u) (tρ : Finset κ) (Tρ : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
      (tρ : Set κ).Pairwise
        (fun j k ↦ _root_.IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) ∧
      (∀ j ∈ tρ, ∃ i ∈ s', (U' i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) ∧
      (ρ : ℝ) ^ (-2 - ζ) ≤ (tρ.card : ℝ))

/-- **V-2 for `CountTransport`: a sufficient condition, so the Prop is not unsatisfiable.**

If every centred representative is *inside* the rescaled body it represents, and enlarging the
cover from the contracted radius `ρ/C` back to `ρ` on the same cores keeps it essentially
distinct, the callers' own `hcanon` cover transports: the same index type, the same cores, the
same count.  The count arithmetic is that `spineOuterCountLoss R ≥ 1` and that a *smaller* radius
gives a *larger* value at the negative exponent `-2-ζ`, so both moves strengthen the bound.

**(a) Why `hgrow` was added**.  When `CountTransport`'s
antecedent moved to the contracted radius the identity route stopped typechecking: the supplied
cover is by `Tube (ρ / centringCoverRadiusConstant)` while the conclusion needs `Tube ρ`.
Enlarging on the same core, `Tube.mk' ρ (W j).dist_eq_one`, keeps containment
(`carrier_subset_mk'`) and *improves* the count (a smaller radius gives a larger value at the
negative exponent `-2-ζ`), but it does **not** preserve essential distinctness — two tubes that
are essentially distinct at radius `ρ/C` need not be at radius `ρ`.  So ED at the conclusion's
radius has to be assumed, in exactly the term the proof constructs.

**(b) The other hypothesis is refuted for every produced hand-back.**
`Kakeya.VeryNotSticky.not_le_of_covers_of_far` shows `hle` — the representative sitting *inside*
the body it represents — fails whenever the body sits away from the origin: `normalise 0`
contracts towards the origin by `8`, and a family all of whose points have norm `> 1/8` cannot
contain its own normalised image.  The representative is a *container* of the normalised member,
not a subset of the member.

**(c) Therefore this is a dead-code item, not an available route.**  It is retained (no-golf) and
recorded for the Regulator alongside
`Kakeya.ML2Core.fine_factor_of_lemma91At_of_edCover`.  The real producer proves A7 through the
similarity; the unconditional non-vacuity witness for the re-shaped `CountTransport` is
`countTransport_witness`, which establishes the conclusion outright on the whole window and so
does not depend on the antecedent at all. -/
theorem countTransport_of_le {b δt δ' : NNReal} {R : ℝ}
    (hsit : Tube.IsRescalingSituation b δt δ' R 3) (hR : 0 < R) (hR1 : 1 ≤ R)
    (T₀ : Tube b (EuclideanSpace ℝ (Fin 3))) (m : EuclideanSpace ℝ (Fin 3)) (ϖ ζ : ℝ)
    (hζ : 0 ≤ 2 + ζ) (hδ'0 : 0 < δ')
    {α : Type u} (s' : Finset α)
    (Z' : α → ShadedTube δt (EuclideanSpace ℝ (Fin 3)))
    (U' : α → ShadedTube δ' (EuclideanSpace ℝ (Fin 3)))
    (hle : ∀ i ∈ s', (U' i).toConvexSpaceBody
      ≤ (Kakeya.ML2Reduction.spineFamily
          (Kakeya.ML2Reduction.spineRescaleUnit hsit.pos_ambient T₀ hR) Z' i).toConvexSpaceBody)
    (hgrow : ∀ (ρ : NNReal) {κ₀ : Type u} (t : Finset κ₀)
      (W : κ₀ → Tube (ρ / centringCoverRadiusConstant) (EuclideanSpace ℝ (Fin 3))),
      ((t : Set κ₀).Pairwise
        fun j k ↦ _root_.IsEssentiallyDistinct (W j).carrier (W k).carrier) →
      ((t : Set κ₀).Pairwise fun j k ↦ _root_.IsEssentiallyDistinct
        (Tube.mk' ρ (W j).dist_eq_one).carrier (Tube.mk' ρ (W k).dist_eq_one).carrier)) :
    CountTransport hsit hR T₀ m ϖ ζ s' Z' U' := by
  intro ρ hρ hcanon
  obtain ⟨κ₀, t, W, hED, hused, hcard⟩ := hcanon
  have hρ0 : 0 < ρ := lt_of_lt_of_le (NNReal.rpow_pos hδ'0) hρ.1
  have hcle : ρ / centringCoverRadiusConstant ≤ ρ := div_centringCoverRadiusConstant_le ρ
  have hcpos : (0 : NNReal) < ρ / centringCoverRadiusConstant :=
    div_pos hρ0 centringCoverRadiusConstant_pos
  have hcposR : (0 : ℝ) < ((ρ / centringCoverRadiusConstant : NNReal) : ℝ) := by
    exact_mod_cast hcpos
  refine ⟨κ₀, t, fun j ↦ Tube.mk' ρ (W j).dist_eq_one, hgrow ρ t W hED, fun j hj ↦ ?_, ?_⟩
  · obtain ⟨i, hi, hlei⟩ := hused j hj
    refine ⟨i, hi, ((hle i hi).trans hlei).trans ?_⟩
    rw [← SetLike.coe_subset_coe]
    exact carrier_subset_mk' (W j) hcle
  · have hΛ : (1 : ℝ) ≤ (centringCountLossConstant R : ℝ) := by
      exact_mod_cast one_le_centringCountLossConstant R
    have hmono : (ρ : ℝ) ^ (-2 - ζ)
        ≤ ((ρ / centringCoverRadiusConstant : NNReal) : ℝ) ^ (-2 - ζ) :=
      Real.rpow_le_rpow_of_nonpos hcposR (by exact_mod_cast hcle) (by linarith)
    have hpos : (0 : ℝ) ≤ ((ρ / centringCoverRadiusConstant : NNReal) : ℝ) ^ (-2 - ζ) :=
      Real.rpow_nonneg (le_of_lt hcposR) _
    nlinarith [hcard, hmono, hpos, hΛ]

/-- **V-2: the re-shaped `CountTransport` is inhabited, on a NONEMPTY index set.**

Re-run against the re-shaped clause, as a re-shaped clause is a new clause.  The witness
establishes the *conclusion* outright for every `ρ` of the window, so it does not depend on the
antecedent at all and is unaffected by the antecedent's move to the contracted radius and to
`centringCountLossConstant R`.  At `ζ = -3` the count reads `ρ^{1} ≤ #tρ`, and the window forces
`δ' ≤ ρ ≤ 1`, so a one-node cover on the representative's own core meets it — `s'` is nonempty by
`hi₀`, so this is not vacuity.  The enlargement term is `Tube.mk' ρ (U' i₀).toTube.dist_eq_one`,
the same term `countTransport_of_le`'s `hgrow` names. -/
theorem countTransport_witness {b δt δ' : NNReal} {R : ℝ}
    (hsit : Tube.IsRescalingSituation b δt δ' R 3) (hR : 0 < R)
    (T₀ : Tube b (EuclideanSpace ℝ (Fin 3))) (m : EuclideanSpace ℝ (Fin 3))
    {ϖ : ℝ} (hϖ0 : 0 ≤ ϖ) (hδ'0 : 0 < δ') (hδ'1 : δ' ≤ 1)
    {α : Type u} {s' : Finset α} {i₀ : α} (hi₀ : i₀ ∈ s')
    (Z' : α → ShadedTube δt (EuclideanSpace ℝ (Fin 3)))
    (U' : α → ShadedTube δ' (EuclideanSpace ℝ (Fin 3))) :
    CountTransport hsit hR T₀ m ϖ (-3) s' Z' U' := by
  intro ρ hρ _
  have hδρ : δ' ≤ ρ := by
    refine le_trans ?_ hρ.1
    calc (δ' : NNReal) = δ' ^ (1 : ℝ) := by rw [NNReal.rpow_one]
      _ ≤ δ' ^ (1 - ϖ) := NNReal.rpow_le_rpow_of_exponent_ge hδ'0 hδ'1 (by linarith)
  have hρ1 : ρ ≤ 1 := le_trans hρ.2 (NNReal.rpow_le_one hδ'1 hϖ0)
  refine ⟨PUnit.{u + 1}, {PUnit.unit}, fun _ ↦ Tube.mk' ρ (U' i₀).toTube.dist_eq_one, ?_, ?_, ?_⟩
  · exact Set.Subsingleton.pairwise (Set.subsingleton_of_subsingleton) _
  · intro j _
    refine ⟨i₀, hi₀, ?_⟩
    rw [← SetLike.coe_subset_coe]
    exact carrier_subset_mk' (U' i₀).toTube hδρ
  · simp only [Finset.card_singleton, Nat.cast_one]
    have hx : ((-2 : ℝ) - (-3)) = 1 := by norm_num
    rw [hx, Real.rpow_one]
    exact_mod_cast hρ1

end Kakeya.VeryNotSticky

end
