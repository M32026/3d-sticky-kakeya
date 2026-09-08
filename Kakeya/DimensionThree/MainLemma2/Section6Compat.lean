/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.Reduction
public import Kakeya.DimensionThree.Plank.TypicalAngleIncidence
public import Kakeya.DimensionThree.MainLemma2.Section6CompatSlabWire

/-!
# Section 6 compatibility interfaces used by Main Lemma 2

The current Section 6 API proves the angle-producing plank reduction in
`ShadedPlank.reduction_to_slab`. Section 9 also needs two strictly stronger interfaces: a
typical-angle theorem whose comparison constant is controlled at an auxiliary scale, and a
plank reduction run at an already prescribed typical angle. They are retained here as the
accepted upstream obligations used by Main Lemma 2, without duplicating Section 6's implemented
declarations.
-/

@[expose] public section

open MeasureTheory Metric
open scoped NNReal Real

noncomputable section

namespace Kakeya

variable {ι : Type*}

/-- Shade fibres are preserved when every shade is transported by the same bijection. -/
theorem _root_.shadeFibre_congr_image {E : Type*} [TopologicalSpace E]
    [Convexity.ConvexSpace ℝ E]
    [MeasureSpace E] (s : Finset ι) (Y Y' : ι → ShadedBody E) (g : E ≃ E)
    (hg : ∀ i ∈ s, (Y' i).shade = g '' (Y i).shade) (z : E) :
    shadeFibre s Y' (g z) = shadeFibre s Y z := by
  unfold shadeFibre
  apply Finset.filter_congr
  intro i hi
  rw [hg i hi]
  constructor
  · rintro ⟨w, hw, hgw⟩
    exact g.injective hgw ▸ hw
  · exact Set.mem_image_of_mem g

/-- Typicality is preserved when every shade is transported by the same bijection. -/
theorem IsTypicalPlankAngle.congr_image {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    {s : Finset ι} {Y Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))}
    {P : ι → Plank a b hab hb1} {theta C A : ℝ≥0}
    (g : EuclideanSpace ℝ (Fin 3) ≃ EuclideanSpace ℝ (Fin 3))
    (hg : ∀ i ∈ s, (Y' i).shade = g '' (Y i).shade)
    (h : IsTypicalPlankAngle s Y P theta C A) : IsTypicalPlankAngle s Y' P theta C A := by
  intro x hx
  rw [← g.apply_symm_apply x, shadeFibre_congr_image s Y Y' g hg (g.symm x)]
  apply h
  rcases Set.mem_iUnion₂.mp hx with ⟨i, hi, hxi⟩
  rw [hg i hi] at hxi
  rcases hxi with ⟨w, hw, hgw⟩
  refine Set.mem_iUnion₂.mpr ⟨i, hi, ?_⟩
  simpa [← hgw] using hw

/-- Compatibility form of GWZ Lemma 6.11 used by the Section 9 target branch.

Unlike `findingTypicalAngleOfIntersection`, this statement keeps an auxiliary scale `δ ≤ a`: the
plank-count and multiplicity hypotheses and the two losses `δ ^ (±ε)` are all read at `δ` rather
than at the plank scale `a`, while the geometric scales — the angle window `a / b ≤ θ ≤ 1` and the
stability threshold `Kakeya.plankAngleScaleA a` — stay at `a`.

The comparison constant `C` is quantified **before** the index type and the geometric data, exactly
as in `Kakeya.findingTypicalAngleOfIntersection`, and carries no upper bound.

An earlier revision of this statement returned `C` *after* the configuration, pinched by
`1 ≤ C ∧ C ≤ δ ^ (-ε)`. That statement is **false**, and its refutation does not need small `δ`:
take `η = 1`, `ε = 10⁻⁴`, `C₀ = 3`, `N = 0` and `δ = a = b = 1/2`, so `δ ^ (-η) = 2` satisfies the
multiplicity hypothesis while `δ ^ (-ε) ≈ 1.00007` pins `C` into `[1, 1.00007]` and pins the
refinement constant `C⁻¹ δ ^ ε` above `δ ^ (2ε) ≈ 0.99986`. Take the three axis-aligned
`½ × ½ × 1` planks centred at the origin: pairwise their intersections have half the maximal
volume, so they are pairwise `IsEssentiallyDistinct` (that predicate is non-strict), and the triple
intersection has positive measure. Shade `Y_i := S ∪ E_i` with `S` inside the triple intersection,
`E_i ⊆ P_i` disjoint from the other two planks, and `|E_i| = |S| / 100`; the multiplicity is
about `2.94 ≥ 2` and the cardinality is `3 ≤ C₀ δ ^ (-N)`. Any admissible refinement may delete at
most about `0.014%` of the mass, whereas the multiplicity-`3` part carries `99%` and the
multiplicity-`1` part `0.99%`, so both survive with positive measure and
`ShadedBody.HasCConstantMultiplicity s Y' C` forces `3 ≤ C ≈ 1.00007`, a contradiction. Hoisting
`C` and dropping the upper bound is what repairs it: a consumer that needs `C ≤ δ ^ (-ε)` now
obtains it as a threshold on `δ`, which is meaningful precisely because `C` no longer depends
on `δ`.

It is `Kakeya.findingTypicalAngleOfIntersection_scaled`, whose refinement bookkeeping at the
auxiliary scale is `Kakeya.refineConst_bound_uniform_perScale`. The hypothesis `2 ≤ δ ^ (-η)` is
retained for its consumers and is not used. -/
theorem findingTypicalAngleOfIntersection_perScale {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε)
    (C₀ : ℝ≥0) (N : ℝ) :
    ∃ C : ℝ≥0, 2 ≤ C ∧
    ∀ {ι : Type*} (s : Finset ι) (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
      {a b δ : ℝ≥0} (ha : 0 < a) (ha1 : a < 1) (hab : a ≤ b) (hb1 : b ≤ 1)
      (hδ : 0 < δ) (hδa : δ ≤ a) (P : ι → Plank a b hab hb1),
      (∀ i ∈ s, (Y i).shade ⊆ (P i).carrier) →
      (δ : ENNReal) ^ (-η) ≤ ShadedBody.multiplicity s Y →
      2 ≤ (δ : ENNReal) ^ (-η) →
      (s.card : ℝ≥0) ≤ C₀ * δ ^ (-N) →
      ∃ (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))) (θ : ℝ≥0),
        ShadedBody.IsCRefinement s Y' s Y (C⁻¹ * δ ^ ε) ∧
        a / b ≤ θ ∧ θ ≤ 1 ∧
        ShadedBody.HasCConstantMultiplicity s Y' C ∧
        IsTypicalPlankAngle s Y' P θ (C * δ ^ (-ε))
          (Real.toNNReal (plankAngleScaleA a)) ∧
        (∀ x ∈ ⋃ i ∈ s, (Y' i).shade,
          ComparableScalars C θ (maxPlankAngle P (shadeFibre s Y' x))) ∧
        HasMaxPlankAngleBound s Y' P θ 1 := by
  obtain ⟨C, hC2, H⟩ := findingTypicalAngleOfIntersection_scaled hε C₀ N
  refine ⟨C, hC2, ?_⟩
  intro ι s Y a b δ ha ha1 hab hb1 hδ hδa P hYP hμ _ hcard
  exact H s Y ha ha1 hab hb1 hδ hδa P hYP hη hμ hcard

end Kakeya

namespace ShadedPlank

variable {a b : NNReal} {hab : a ≤ b} {hb1 : b ≤ 1}

/-- **GWZ Lemma 6.13 at an already prescribed typical angle**, narrowed to the interface its
consumer reads.

This is the stronger interface required by the transverse branch of Main Lemma 2, and it is
intentionally separate from the implemented `ShadedPlank.reduction_to_slab`, which produces its
own angle. It remains an accepted Section 6 obligation.

## The 2026-08 narrowing, and why it is a narrowing and not a weakening

An earlier revision of this statement returned the full Lemma 6.13 tuple: the geometric constant
block `cN, cThk, Cbox, Cset, Cang`, and, per configuration, the fibre size `N`, the constants
`cP, cLam, c2, c3, c4`, the thickened representatives
`R : Plank.ThickenedRepr s' (ShadedPlank.planks Y) θ hθ1 cThk`, the slab assignment
`slabOf : Plank.ThickenedPlank θ b hθ1 hb1 → Slab θ hθ1` and the thickened shading
`Yθ : Plank.ThickenedPlank θ b hθ1 hb1 → ShadedBody _`, together with the cardinality retention,
`1 ≤ N`, the `Plank.inSlabFamilyC` membership clause, the `Yθ` carrier equation, the
representative fibre-cardinality clause, and Items 2, 3 and 4.

**Every one of those outputs was read by nothing.** This statement has exactly one consumer in the
development, `Kakeya.VeryNotSticky.exists_isReductionFillAvailable` in
`Kakeya.DimensionThree.MainLemma2.PlankConstants`, and that consumer destructures the tuple and
discards all of them; the only components it forwards into
`Kakeya.VeryNotSticky.IsReductionFillAvailable` are `s'`, `Y'`, `c1`, the two `IsRefinement`
clauses, the nonemptiness of the output union (which it derives from the fullness retention and
the positivity of the input fullness), Item 1, and `c1⁻¹ ≤ δ ^ (-ε')`. So the deleted clauses were
carried through the whole obligation without ever being used.

**What deleting them buys is that `θ` disappears from every type in the statement.** In the old
form `θ` occurred in the *types* of the three witnesses `R`, `slabOf` and `Yθ` — a
`Plank.ThickenedPlank θ b hθ1 hb1` and a `Slab θ hθ1` are indexed by the angle — which is why
prescribing `θ` meant threading it, as a parameter rather than an output, through
`Kakeya.refinement_preassembly_uniform`, `Kakeya.PreassemblyResult` (where `θ` and `hθ1` are
produced *fields*, and `Plank.ThickenedRepr.repr_eq` pins each representative to be the
`θ`-thickening of a selected plank), `Kakeya.plankReduction` and
`ShadedPlank.reduction_to_slab`. After the narrowing, `θ` occurs only in the *terms*
`θ * b` inside Item 1, and no type in the statement mentions it. The remaining obligation is
therefore a single local-density statement at a prescribed radius, not a reconstruction of the
stopping-time representative/slab apparatus at a prescribed angle.

The hypotheses are unchanged, `hθ1 : θ ≤ 1` included; it is now an ordinary hypothesis rather than
a binder occurring in the types of the deleted witnesses, and is retained because the consumer
supplies it and because dropping it would silently strengthen the statement.

## The state of the proof, and the exact remaining gap

With `θ` gone from the types, the prescribed-angle machinery this needs turns out to be **already
public**, and the obstruction is elsewhere.

* `Kakeya.representativeWitness_strong_uniform`
  (`Kakeya.DimensionThree.Plank.RepresentativeSelection`) is the representative/slab preassembly
  **at a prescribed angle**: it takes `(θ : ℝ≥0) (hθ1 : θ ≤ 1)` as inputs and returns `s'`, a
  refined shading, `repr`, `slabOf`, `𝒯`, `𝒮`, a `Plank.ThickenedRepr s' P θ hθ1 cThk`, the
  `Plank.inSlabFamilyC` membership, `Kakeya.HasMaxPlankAngleBound s' _ P θ Cgeom`, the two-sided
  `Kakeya.IsTypicalPlankAngle` at `θ`, the fibre-cardinality clause and the slab overlap.
* `Kakeya.slabwiseDensity_assigned` (`Kakeya.DimensionThree.Plank.SlabwiseReduction`) is Item 1
  **at a prescribed angle**: it is parametric in `{a b θ}` and in an arbitrary representative type,
  and from the slab membership, the max-angle bound at `θ`, the per-slab typicality, per-slab
  fullness and per-slab constant multiplicity it produces exactly the local-density conclusion
  above at radius `θ * b` and dilation `Kakeya.plankReduction.ballDilation = 3`.

So the remaining work is an assembly, not a new construction: it mirrors the Item 1 half of
`Kakeya.plankReduction` with `θ` taken from the caller instead of from the stopping time. Nothing
under `Kakeya/DimensionThree/Plank/` has to be re-parametrised for that.

**What blocks it is a scale mismatch, not the angle.** Every hypothesis of those two producers is
stated at the *plank* scale `a`: `representativeWitness_strong_uniform` asks for
`Cuni⁻¹ * a ^ ε ≤ cAngle` on the incoming refinement coefficient and for
`a ^ η ≤ cLamY ≤ ShadedBody.fullness s Y`, and `slabwiseDensity_assigned` asks for per-slab
fullness `cLamPre * a ^ (η + εwork)` and per-slab constant multiplicity `Cmult * a ^ (-(εwork/4))`.
The data this statement receives are controlled only at the *auxiliary* scale `δ ≤ a`: the incoming
refinement coefficient is `C⁻¹ ≥ δ ^ ε`, the constant multiplicity is `C ≤ δ ^ (-ε)`, and the
multiplicity and cardinality hypotheses are read at `δ`. Since `δ` may be an arbitrarily high power
of `a`, `δ ^ ε · a ^ η` is not bounded below by any power of `a`, so the `a`-scale hypotheses are
not derivable from the `δ`-scale ones. That the statement is nevertheless the right one is visible
in its own exponent ledger: the conclusion asks for `c1` with `c1⁻¹ ≤ δ ^ (-ε')` and assumes
`128 * ε ≤ ε'`, of which this step needs one factor `δ ^ ε` for the passage to `Y''` and one for the
reduction itself — `δ`-scale bookkeeping throughout.

## Corrections to the paragraph above, established in `Section6CompatDense.lean` (2026-09)

The paragraph above is right that the obstruction is a scale mismatch and not the angle, but it
misidentifies *where* the mismatch is and *which* files have to change. Three corrections, all
checked against the actual declarations:

1. **`Kakeya.representativeWitness_strong_uniform` does not need re-parametrising for the
   refinement coefficient.** Its `a`-scale hypothesis is `Cuni⁻¹ * a ^ ε ≤ cAngle` with `Cuni`
   quantified *after* `cEta, Cres, kappa` and *before* the configuration, so instantiating
   `Cuni := C` turns it into `C⁻¹ * a ^ ε ≤ C⁻¹`, which is free. The `Cuni`-dependent outputs
   `cP, cLam, Cref` need not be used either: the theorem separately exposes `q = cGood / 2`,
   `rRef = (cGood - q) * cAngle`, `cEta * a ^ η ≤ cGood` and
   `rRef * λ(s, Y) ≤ λ(s', Y'')` with `cEta` independent of `Cuni`, giving
   `rRef ≥ (cEta / 2) * a ^ η * C⁻¹ ≥ (cEta / 2) * a ^ η * δ ^ ε` at a cost of exactly one
   `δ ^ ε`.
2. **What that witness *cannot* be given is its angular-stability hypothesis.** It asks for
   two-sided comparability on every subfibre retaining a `(Kakeya.plankReserveScale kappa a)⁻¹`
   fraction, i.e. at the **reserve** scale `kappa * plankAngleScaleA a ^ 2`. This statement hands
   it `Kakeya.IsTypicalPlankAngle … C (Real.toNNReal (Kakeya.plankAngleScaleA a))`, i.e. the
   *public* scale `plankAngleScaleA a`. Since `kappa ≥ 1` and `plankAngleScaleA a ≥ 1`, the
   reserve threshold is smaller, so strictly more subfibres are constrained: the reserve clause is
   strictly stronger, and `Kakeya.IsTypicalPlankAngle.mono_scale` runs the other way. The reserve
   is exactly what the 6.13 proof spends (`Kakeya.stopScaleStability_of_fibreRetention` spends one
   factor of `Nov` out of it), so a prescribed-angle 6.13 has to *receive* it. The producer that
   would supply it exists and is already `δ`-parametric —
   `Kakeya.findingTypicalAngleOfIntersection_stable_reserve` is the (`private`)
   `findingTypicalAngleOfIntersection_core` of
   `Kakeya/DimensionThree/Plank/TypicalAngleIncidence.lean` specialised at `δ := a`, and
   `Kakeya.refineConst_bound_uniform_reserve_perScale` is the matching `perScale` refinement
   bound — but `Kakeya.findingTypicalAngleOfIntersection_perScale` publishes only the public-scale
   clause. **Adding the reserve-scale clause to that theorem's conclusion, and to this statement's
   hypotheses, is the interface repair this route needs.**
3. **`Kakeya.slabwiseDensity_assigned` is where the ledger actually breaks.** Its `c1` comes from
   `Kakeya.slabwiseDensity_of_outputs` as `c1 = cBall * cLamBox ^ 2` with
   `cLamBox = (2 * Cmult)⁻¹ * cLamPre / (512 * Nov * cTan)`, so per scale one must take
   `cLamPre ≈ δ ^ ε * cLamPre₀` and `Cmult ≈ δ ^ (-ε) * Cmult₀`, giving
   `c1 ∝ cLamPre ^ 2 / Cmult ^ 2 ≈ δ ^ (4ε)` before the `Nov`/`cTan` growth. Worse, that theorem's
   constant-multiplicity hypothesis is `Cmult * a ^ (-(εwork / 4))` with `εwork ≤ 4 * η / 11`
   fixed *before* the configuration, while the data here only bound `C ≤ δ ^ (-ε)` with `δ` an
   arbitrary power of `a`; and the dependence of `c1` on `Cθ`, `Cmult`, `cTan`, `Ceta`, `Nov` is
   nowhere quantified. So the `δ`-scale reparametrisation is a change to
   `Kakeya/DimensionThree/Plank/SlabwiseReduction.lean` *and its whole dependency stack*, not to
   `RepresentativeSelection.lean`.

## The reduction that is existing, and the single obligation that remains

`Kakeya/DimensionThree/MainLemma2/Section6CompatDense.lean` proves
`ShadedPlank.reduction_to_slab_atTypicalAngle_of_denseRegion`: **this statement verbatim** — same
binders, same hypotheses, same `128 * ε ≤ ε'`, same conclusion — with exactly one hypothesis
inserted, namely that `U(s, Y'')` admits a measurable region `G` retaining a
`δ ^ (ε' - 2ε) * a ^ ε` fraction of it and such that `U(s, Y'') ∩ G` fills a `θ b`-ball around each
of its points to density `δ ^ ε' * a ^ (4η) * a ^ ε`. The witness for `δthr` is `1`: **no smallness
threshold is needed for the soft half**, and of `128 * ε ≤ ε'` this step spends `2 * ε` — one
`δ ^ ε` on the
incoming `C⁻¹`, one on the `C` that
`Plank.isCRefinement_restrictShade_of_dense` charges to convert a union capture into a mass
capture. `ShadedPlank.reduction_to_slab_atTypicalAngle_of_avgDensity` is the same statement with
the obligation given instead as a finite `θ b`-ball cover whose sparse part is small.

The inserted hypothesis is GWZ Step 3 ("sum over the dense tangential pieces and discard the
complement; a final dense-ball selection preserves a substantial fraction of the shading mass"),
and it is the only non-soft content left.

## The smallest obligation currently available (2026-09, `Section6CompatThicken.lean`)

`Kakeya/DimensionThree/MainLemma2/Section6CompatThicken.lean` proves
`ShadedPlank.reduction_to_slab_atTypicalAngle_of_thickening`: **this statement verbatim** with
exactly one hypothesis inserted, and that hypothesis is a **scalar inequality** rather than an
existence statement about sets,

```
54 · δ ^ ε' · a ^ (4η) · a ^ ε · C · |N_{θb}(U(s, Y''))| ≤ |U(s, Y'')|,
```

`N_r` being `Metric.cthickening r`.  There is no region to construct, no cover to exhibit, and the
multiplicity has cancelled.  It is strictly weaker than the dense-region obligation on two counts.

* The discard is done in **mass** rather than in volume: a `θb`-ball is kept when
  `∑_i |Y''_i ∩ B̄(z, θb)| ≥ τ |B̄(z, θb)|`.  So a fixed *half* of the mass can always be retained,
  where the dense-region route — which must convert a union capture into a mass capture through
  `Plank.isCRefinement_restrictShade_of_dense`, at the price of one factor `C` — can never retain
  more than a `1/C` fraction, and therefore has to achieve a retention ratio
  `δ ^ (ε' - 2ε) a ^ ε` that tends to `1` as `a → 1`.
* The threshold `τ := δ ^ ε' a ^ (4η + ε) · C · m₀`, with `m₀` the minimal pointwise multiplicity,
  is exactly the factor `C · m₀` that `ShadedPlank.sum_volume_shade_inter_le_of_hasCConstantMultiplicity`
  charges to convert the surviving mass density into the union density Item 1 asks for, so `m₀`
  cancels.

The threshold witness is `δthr = 2 ^ (-1/ε)`, used exactly once, for `2 δ ^ (ε' - ε) ≤ 1`; that is
the only place `128 * ε ≤ ε'` enters, and it spends `2 * ε` of it.  The obligation carries the
constant `C`
the caller actually supplied rather than its bound `δ ^ (-ε)`.
`ShadedPlank.reduction_to_slab_atTypicalAngle_of_volumeLowerBound` is the crude corollary in which
the thickening is replaced by the window `B̄(0, 5)`, giving the `θ`-free and `b`-free obligation
`54 δ ^ ε' a ^ (4η + ε) C |B̄(0, 5)| ≤ |U(s, Y'')|`; that form is genuinely weaker than the theorem
(it fails for the extremal bush family) and is only for the regime where `θ b` is comparable to the
window.

The obligation is where the multiplicity hypothesis `2 ≤ δ ^ (-η) ≤ µ` must be used: a *single*
plank has thickening ratio `θ b / a`, which violates the obligation as soon as
`θ b ≫ a ^ (1 - 4η - ε)`, and it is the multiplicity hypothesis that excludes it.  For the two
extremal admissible shapes the obligation holds with room — the bush (`|s| = µ` planks through one
core box) has thickening ratio `a ^ (-η/2)` because the fullness hypothesis forces
`θ ≲ a ^ (1 - η/2)`, and the transverse plate (`θ ≈ 1`, `b ≈ 1`) has thickening ratio `a ^ (-η)`
because the same hypothesis forces the plate thickness `≳ a ^ η`; both are below the allowance
`a ^ (-4η - ε)`.

## One correction to the two "elementary facts" recorded below

Fact 1 below is true for Item 1 and **false for the fullness clause**, and that trap is now
certified. Restricting every shade to a *single* ball `B̄(z, θ b)` does give Item 1 outright, but
`ShadedPlank.denseBall_mass_forces_cube_bound` shows the resulting family can only satisfy the
fullness clause if `c1 * a ^ ε * λ(s, bodies Y) * a * b ≤ (θ b) ^ 3`, and
`ShadedPlank.singleBall_necessary_condition_fails` shows this is false for *every* `0 < a < 1`
at `δ = a`, `b = 1`, `θ = a / b`, `λ = a ^ η`, `c1 = δ ^ ε'` whenever `η + ε + ε' < 2`. One ball of
radius `θ b` holds volume `≈ (θ b) ^ 3` while the fullness clause asks for essentially all of the
mass `8 a b λ` of an average plank. The output family must be spread over many `θ b`-balls, which
is what the dense-region construction does.

For the record, two elementary facts established while scoping this. Writing `U'` for the retained
union:

1. A local-density statement transfers *upward* in radius for free and *downward* at the cost of an
   absolute constant only. Downward: if `U'` has density `t` in some ball `B̄(x₀, R)` with
   `R ≥ θ * b`, cover that ball by `O((R / (θ*b)) ^ 3)` balls of radius `θ * b`; the densest one
   `B̄(z, θ*b)` has `U'`-density at least `c * t` with `c` absolute *independent of the ratio*.
   Restricting every shade to `B̄(z, θ*b)` then yields the displayed Item 1 outright, since the
   restricted union lies in `B̄(z, θ*b)` and `B̄(z, θ*b) ⊆ B̄(x, 3 * θ * b)` for every `x` whose
   `θ*b`-ball meets it. **But see the correction above: the retained mass is then far too small
   for the fullness clause, so this is not a route to the theorem.**
2. Consequently, routing through `ShadedPlank.reduction_to_slab` and its *produced* angle `θₚ`
   costs nothing when `θ ≤ 3 θₚ`, and its only public control on `θₚ` is `a / b ≤ θₚ ≤ 1`; in the
   worst case `θ / θₚ = b / a` the inflation loss is `(a/b) ^ 3`, which against `c1⁻¹ ≤ δ ^ (-ε')`
   would demand `ε' ≥ 3` where the consumer supplies `ε' = η / 2`. That route is therefore the
   wrong one, and the prescribed-angle producers above are the right one. A second, independent
   reason: `ShadedPlank.reduction_to_slab` exposes no typicality clause for `θₚ`, so `θ` and `θₚ`
   cannot be compared at all.
-/
theorem reduction_to_slab_atTypicalAngle :
    ∀ {η ε ε' : ℝ}, 0 < η → 0 < ε → 0 < ε' → 128 * ε ≤ ε' →
    ∀ (Ccard : ℝ≥0) (D : ℝ),
    ∃ δthr : ℝ≥0, 0 < δthr ∧ δthr ≤ 1 ∧
    ∀ {ι : Type*} (s : Finset ι)
      {δ a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
      (Y : ι → ShadedPlank a b hab hb1)
      (θ : ℝ≥0) (hθ1 : θ ≤ 1) (C : ℝ≥0)
      (Y'' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))),
      0 < δ → δ ≤ a → a < 1 → δ ≤ δthr →
      Plank.IsWindowedFamily s (ShadedPlank.planks Y) →
      a ^ η ≤ ShadedBody.fullness s (ShadedPlank.bodies Y) →
      (a : ENNReal) ^ (-η) ≤ ShadedBody.multiplicity s (ShadedPlank.bodies Y) →
      (δ : ENNReal) ^ (-η) ≤ ShadedBody.multiplicity s (ShadedPlank.bodies Y) →
      2 ≤ (δ : ENNReal) ^ (-η) →
      (s.card : ℝ≥0) ≤ Ccard * δ ^ (-D) →
      a / b ≤ θ → 1 ≤ C → C ≤ δ ^ (-ε) →
      ShadedBody.IsCRefinement s Y'' s (ShadedPlank.bodies Y) C⁻¹ →
      ShadedBody.HasCConstantMultiplicity s Y'' C →
      Kakeya.IsTypicalPlankAngle s Y'' (ShadedPlank.planks Y) θ C
        (Real.toNNReal (Kakeya.plankAngleScaleA a)) →
      Kakeya.HasMaxPlankAngleBound s Y'' (ShadedPlank.planks Y) θ 1 →
    ∃ (s' : Finset ι)
      (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
      (c1 : ℝ≥0),
      0 < c1 ∧
      ShadedBody.IsRefinement s' Y' s (ShadedPlank.bodies Y) ∧
      ShadedBody.IsRefinement s' Y' s Y'' ∧
      (c1 * a ^ ε) * ShadedBody.fullness s (ShadedPlank.bodies Y) ≤
        ShadedBody.fullness s' Y' ∧
      (∀ x,
        ((⋃ i ∈ s', (Y' i).shade) ∩ Metric.closedBall x ((θ * b : ℝ))).Nonempty →
        (c1 : ENNReal) * a ^ (4 * η) * a ^ ε *
            volume (Metric.closedBall x ((θ * b : ℝ))) ≤
          volume ((⋃ i ∈ s', (Y' i).shade) ∩
            Metric.closedBall x (redPlankTube.ballDilation * θ * b))) ∧
      c1⁻¹ ≤ δ ^ (-ε') := by
  exact reduction_to_slab_atTypicalAngle_of_dyadicBlocks
    reduction_to_slab_atTypicalAngle_block

end ShadedPlank

end
