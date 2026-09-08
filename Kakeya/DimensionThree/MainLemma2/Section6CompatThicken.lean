/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.Reduction
public import Kakeya.DimensionThree.Plank.LocalDensity
public import Kakeya.DimensionThree.Plank.RelativeMultiplicity
public import Kakeya.BallDense

/-!
# The thickening reduction for `ShadedPlank.reduction_to_slab_atTypicalAngle`

This file replaces the *set-existence* obligation of `Section6CompatDense.lean` by a single
**scalar inequality**.  Writing `U = U(s, Y'')` for the shading union and `r = θ b`, the whole
remaining content of `ShadedPlank.reduction_to_slab_atTypicalAngle` is

```
54 · C · δ ^ ε' · a ^ (4η) · a ^ ε · |N_r(U)|  ≤  |U|,
```

a comparison between the volume of the `r`-thickening of the shading union and the volume of the
shading union itself.  There is no region to construct, no cover to exhibit, no `ρ`, and the
multiplicity cancels.

## Why this is strictly better than the dense-region obligation

`Section6CompatDense.lean` reduces the target to: *produce* a measurable `G` retaining a
`δ ^ (ε' - 2ε) a ^ ε` fraction of `U` and filling a `θb`-ball around each of its points.  Two
things make that awkward.

1. It is an existence statement about sets, so a producer has to do the discard construction
   itself.
2. Its retention exponent goes through `Plank.isCRefinement_restrictShade_of_dense`, which
   converts a *union* capture `ρ|U| ≤ |U ∩ G|` into a *mass* capture at the price of one factor
   `C`.  Since `ρ ≤ 1` and `C ≥ 1`, that route can never retain more than a `1/C` fraction of the
   mass, so the retention ratio it must achieve is pushed up to `δ ^ (ε' - 2ε) a ^ ε`, which is
   close to `1` exactly when `a` is close to `1` — a corner in which no discard is affordable.

This file does the discard **in mass rather than in volume**: a ball `B̄(z, r)` is kept when
`∑_i |Y''_i ∩ B̄(z, r)| ≥ τ |B̄(z, r)|`, so the discarded quantity is directly the mass, and a
fixed half of it can always be kept.  The conversion of the surviving mass density into the
*union* density that Item 1 asks for is done once, on a good ball, by
`ShadedPlank.sum_volume_shade_inter_le_of_hasCConstantMultiplicity`, and the factor `C · m₀` it
costs is exactly the factor `C · m₀` that the threshold `τ := t · C · m₀` carries — so `m₀`, the
minimal pointwise multiplicity, cancels out of the final obligation.

## The exponent ledger

`c1 := δ ^ ε'`, `t := c1 · a ^ (4η) · a ^ ε`, `κ := c1 · a ^ ε`.

* One `δ ^ ε` pays the incoming refinement `IsCRefinement s Y'' s (bodies Y) C⁻¹`.
* One more `δ ^ ε` pays the *fixed* half-discard, through `2 · κ · C ≤ 1`.  With `C ≤ δ ^ (-ε)`
  and `a ^ ε ≤ 1` this is `2 δ ^ (ε' - ε) ≤ 1`, and `ε' - ε ≥ ε` because `2 ε ≤ ε'`, so it holds
  as soon as `δ ^ ε ≤ 1/2`.  That is the *only* use of the smallness threshold, and it fixes
  `δthr = 2 ^ (-1/ε)`.

So only `2 * ε ≤ ε'` of the repaired binder `128 * ε ≤ ε'` is spent here, the remaining `126 * ε`
being what the Step-3 ledger needs elsewhere: the remaining obligation carries the
factor `C` explicitly rather than the bound `δ ^ (-ε)`, so a producer may use whatever `C` the
caller actually supplied.

## Sanity of the obligation

The obligation says the `θb`-thickening of `U(s, Y'')` inflates its volume by at most
`(54 C δ ^ ε' a ^ (4η + ε)) ⁻¹`.  Two checks, at the two extreme shapes of a Section-6
configuration:

* the *bush* (`|s| = μ` planks through one core box, the extremal high-multiplicity family):
  the fullness hypothesis `a ^ η ≤ λ` forces `θ ≲ a ^ (1 - η/2)`, the core box is
  `a ^ (η/2) × a ^ (η/2) × a` and `r = θ b` sits between `a` and `a ^ (η/2)`, so the inflation
  ratio is `a ^ (-η/2)` — comfortably below `a ^ (-4η - ε)`;
* the *transverse plate* (`θ ≈ 1`, `b ≈ 1`, planks `a × 1 × 1`): the same fullness hypothesis
  forces the plate thickness `h ≳ a ^ η`, so the inflation ratio at `r = 1` is `≈ a ^ (-η)`,
  again below `a ^ (-4η - ε)`.

The single-plank shape, whose inflation ratio is `θ b / a` and which does violate the obligation
as soon as `θ b ≫ a ^ (1 - 4η - ε)`, is excluded by the multiplicity hypothesis `2 ≤ δ ^ (-η) ≤ µ`.
So the obligation is the exact place where the multiplicity hypothesis has to be used, which is
where GWZ uses it.
-/

@[expose] public section

open MeasureTheory Metric
open scoped NNReal Real ENNReal

noncomputable section

namespace ShadedPlank

variable {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}

/-! ## A packing bound: a separated cover is no bigger than the thickening -/

/-- **Packing bound.**  If `T ⊆ A` is `r`-separated then the balls `B̄(z, r/3)`, `z ∈ T`, are
pairwise disjoint and contained in the `r`-thickening of `A`, so

`∑_{z ∈ T} |B̄(z, r)| = 27 ∑_{z ∈ T} |B̄(z, r/3)| ≤ 27 |N_r(A)|`.

The factor `27 = 3 ^ 3` is the ambient dimension entering; nothing else about `A` is used. -/
theorem sum_volume_closedBall_le_cthickening
    {A : Set (EuclideanSpace ℝ (Fin 3))} {r : ℝ} (hr : 0 < r)
    {T : Finset (EuclideanSpace ℝ (Fin 3))} (hTA : ∀ z ∈ T, z ∈ A)
    (hsep : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → r < dist x y) :
    ∑ z ∈ T, volume (closedBall z r) ≤ 27 * volume (Metric.cthickening r A) := by
  classical
  have hr3 : (0 : ℝ) ≤ r / 3 := by positivity
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by
    simp
  -- each big ball is `27` small balls
  have hball : ∀ z : EuclideanSpace ℝ (Fin 3),
      volume (closedBall z r) = 27 * volume (closedBall z (r / 3)) := by
    intro z
    rw [Measure.addHaar_closedBall volume z hr.le,
      Measure.addHaar_closedBall volume z hr3, hfr]
    rw [← mul_assoc]
    congr 1
    have h27 : r ^ 3 = 27 * (r / 3) ^ 3 := by ring
    rw [h27, ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 27)]
    norm_num
  -- the small balls are pairwise disjoint
  have hdisj : (T : Set (EuclideanSpace ℝ (Fin 3))).PairwiseDisjoint
      (fun z => closedBall z (r / 3)) := by
    intro x hx y hy hxy
    change Disjoint (closedBall x (r / 3)) (closedBall y (r / 3))
    rw [Set.disjoint_left]
    intro w hwx hwy
    have hdx : dist w x ≤ r / 3 := Metric.mem_closedBall.mp hwx
    have hdy : dist w y ≤ r / 3 := Metric.mem_closedBall.mp hwy
    have hxy' : dist x y ≤ 2 * (r / 3) := by
      calc dist x y ≤ dist x w + dist w y := dist_triangle x w y
        _ ≤ r / 3 + r / 3 := add_le_add (by simpa [dist_comm] using hdx) hdy
        _ = 2 * (r / 3) := by ring
    have hgt : r < dist x y := hsep x hx y hy hxy
    linarith
  -- the small balls sit inside the thickening
  have hsub : ∀ z ∈ T, closedBall z (r / 3) ⊆ Metric.cthickening r A := by
    intro z hz w hw
    refine Metric.mem_cthickening_of_dist_le w z r A (hTA z hz) ?_
    exact le_trans (Metric.mem_closedBall.mp hw) (by linarith)
  calc ∑ z ∈ T, volume (closedBall z r)
      = ∑ z ∈ T, 27 * volume (closedBall z (r / 3)) :=
        Finset.sum_congr rfl fun z _ => hball z
    _ = 27 * ∑ z ∈ T, volume (closedBall z (r / 3)) := by rw [Finset.mul_sum]
    _ = 27 * volume (⋃ z ∈ T, closedBall z (r / 3)) := by
        rw [measure_biUnion_finset hdisj (fun z _ => measurableSet_closedBall)]
    _ ≤ 27 * volume (Metric.cthickening r A) := by
        gcongr
        exact Set.iUnion₂_subset hsub

/-! ## Mass on a test set under constant multiplicity -/

variable {ι : Type*}

/-- **Upper bound for the mass inside a test set, from constant multiplicity.**  If `(s, V)` has
constant multiplicity at scale `C` and `y` lies in the shading union, then for *every* set `B`

`∑_i |V_i ∩ B| ≤ C · µ(y) · |U ∩ B|`.

This is `Plank.sum_volume_shade_le_of_hasCConstantMultiplicity` localised to `B`; the case
`B = Set.univ` is that statement.  It is what converts a *mass* density on a ball into the
*union* density Item 1 asks for. -/
theorem sum_volume_shade_inter_le_of_hasCConstantMultiplicity (s : Finset ι)
    (V : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))) {C : ℝ≥0}
    (hC : ShadedBody.HasCConstantMultiplicity s V C)
    {y : EuclideanSpace ℝ (Fin 3)} (hy : y ∈ ⋃ i ∈ s, (V i).shade)
    (B : Set (EuclideanSpace ℝ (Fin 3))) :
    ∑ i ∈ s, volume ((V i).shade ∩ B)
      ≤ (C : ENNReal) * (ShadedBody.pointwiseMultiplicity s V y : ENNReal)
          * volume ((⋃ i ∈ s, (V i).shade) ∩ B) := by
  set U : Set (EuclideanSpace ℝ (Fin 3)) := ⋃ i ∈ s, (V i).shade with hU
  have hstep : ∀ i ∈ s, (V i).shade ∩ B = (V i).shade ∩ (U ∩ B) := by
    intro i hi
    have h : (V i).shade ⊆ U := fun x hx => Set.mem_biUnion hi hx
    ext x
    constructor
    · rintro ⟨hx1, hx2⟩; exact ⟨hx1, h hx1, hx2⟩
    · rintro ⟨hx1, -, hx2⟩; exact ⟨hx1, hx2⟩
  calc ∑ i ∈ s, volume ((V i).shade ∩ B)
      = ∑ i ∈ s, volume ((V i).shade ∩ (U ∩ B)) :=
        Finset.sum_congr rfl fun i hi => by rw [hstep i hi]
    _ = ∫⁻ x in U ∩ B, (ShadedBody.pointwiseMultiplicity s V x : ENNReal) :=
        Plank.sum_volume_shade_inter_eq_lintegral_multiplicity s V _
    _ ≤ ∫⁻ _ in U ∩ B, (C : ENNReal) * (ShadedBody.pointwiseMultiplicity s V y : ENNReal) :=
        setLIntegral_mono_ae aemeasurable_const
          (ae_of_all _ fun x hx => by simpa using ENNReal.coe_le_coe.mpr (hC hx.1 hy))
    _ = _ := setLIntegral_const _ _

/-! ## The mass-based discard -/

/-- **Discarding the mass-sparse balls of a finite ball cover.**

Cover the shading union by the balls `B̄(z, r)`, `z ∈ T`, and call `z` *good* when the family
carries at least `τ |B̄(z, r)|` of **mass** in that ball, `τ |B̄(z, r)| ≤ ∑_i |Y_i ∩ B̄(z, r)|`.
Let `G` be the union of the good balls.  Then

* the mass lost is at most `τ ∑_{z ∈ T} |B̄(z, r)|`, and
* every point of `U ∩ G` lies in a good ball which is *contained* in `G`, so the mass density on
  that ball is unaffected by the passage from `U` to `U ∩ G`.

Unlike `ShadedPlank.exists_denseRegion_of_ballCover` this discards in **mass** and not in volume;
that is what makes a fixed (half) retention affordable, since the retained mass is compared with
the total mass rather than with the volume of the union. -/
theorem exists_massRegion_of_ballCover (s : Finset ι)
    (V : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (r : ℝ) (T : Finset (EuclideanSpace ℝ (Fin 3)))
    (hcov : (⋃ i ∈ s, (V i).shade) ⊆ ⋃ z ∈ T, closedBall z r) (tau : ℝ≥0) :
    ∃ G : Set (EuclideanSpace ℝ (Fin 3)), MeasurableSet G ∧
      (∑ i ∈ s, volume (V i).shade
        ≤ (∑ i ∈ s, volume ((V i).shade ∩ G))
            + (tau : ENNReal) * ∑ z ∈ T, volume (closedBall z r)) ∧
      (∀ y ∈ (⋃ i ∈ s, (V i).shade) ∩ G, ∃ z : EuclideanSpace ℝ (Fin 3),
        y ∈ closedBall z r ∧ closedBall z r ⊆ G ∧
        (tau : ENNReal) * volume (closedBall z r)
          ≤ ∑ i ∈ s, volume ((V i).shade ∩ closedBall z r)) := by
  classical
  set Good : Finset (EuclideanSpace ℝ (Fin 3)) :=
    T.filter (fun z => (tau : ENNReal) * volume (closedBall z r)
      ≤ ∑ i ∈ s, volume ((V i).shade ∩ closedBall z r)) with hGoodDef
  set G : Set (EuclideanSpace ℝ (Fin 3)) := ⋃ z ∈ Good, closedBall z r with hGdef
  have hGmeas : MeasurableSet G :=
    MeasurableSet.biUnion (Finset.countable_toSet Good) fun _ _ => measurableSet_closedBall
  have hbad : ∀ z ∈ T \ Good, ∑ i ∈ s, volume ((V i).shade ∩ closedBall z r)
      ≤ (tau : ENNReal) * volume (closedBall z r) := by
    intro z hz
    have hz' := (Finset.mem_sdiff.mp hz).2
    have hcon : ¬ ((tau : ENNReal) * volume (closedBall z r)
        ≤ ∑ i ∈ s, volume ((V i).shade ∩ closedBall z r)) := by
      intro h
      exact hz' (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hz).1, h⟩)
    exact le_of_lt (not_le.mp hcon)
  refine ⟨G, hGmeas, ?_, ?_⟩
  · have hdiff : ∀ i ∈ s, volume ((V i).shade \ G)
        ≤ ∑ z ∈ T \ Good, volume ((V i).shade ∩ closedBall z r) := by
      intro i hi
      have hsub : (V i).shade \ G ⊆ ⋃ z ∈ (T \ Good), ((V i).shade ∩ closedBall z r) := by
        intro y hy
        have hyU : y ∈ ⋃ j ∈ s, (V j).shade := Set.mem_biUnion hi hy.1
        obtain ⟨z, hzT, hyz⟩ := Set.mem_iUnion₂.mp (hcov hyU)
        have hzG : z ∉ Good := fun hz => hy.2 (Set.mem_iUnion₂.mpr ⟨z, hz, hyz⟩)
        exact Set.mem_iUnion₂.mpr ⟨z, Finset.mem_sdiff.mpr ⟨hzT, hzG⟩, ⟨hy.1, hyz⟩⟩
      exact le_trans (measure_mono hsub) (measure_biUnion_finset_le _ _)
    have hlost : ∑ i ∈ s, volume ((V i).shade \ G)
        ≤ (tau : ENNReal) * ∑ z ∈ T, volume (closedBall z r) := by
      calc ∑ i ∈ s, volume ((V i).shade \ G)
          ≤ ∑ i ∈ s, ∑ z ∈ T \ Good, volume ((V i).shade ∩ closedBall z r) :=
            Finset.sum_le_sum hdiff
        _ = ∑ z ∈ T \ Good, ∑ i ∈ s, volume ((V i).shade ∩ closedBall z r) := Finset.sum_comm
        _ ≤ ∑ z ∈ T \ Good, (tau : ENNReal) * volume (closedBall z r) :=
            Finset.sum_le_sum hbad
        _ ≤ ∑ z ∈ T, (tau : ENNReal) * volume (closedBall z r) :=
            Finset.sum_le_sum_of_subset Finset.sdiff_subset
        _ = (tau : ENNReal) * ∑ z ∈ T, volume (closedBall z r) := by rw [Finset.mul_sum]
    calc ∑ i ∈ s, volume (V i).shade
        = ∑ i ∈ s, (volume ((V i).shade ∩ G) + volume ((V i).shade \ G)) :=
          Finset.sum_congr rfl fun i _ => (measure_inter_add_sdiff _ hGmeas).symm
      _ = (∑ i ∈ s, volume ((V i).shade ∩ G)) + ∑ i ∈ s, volume ((V i).shade \ G) :=
          Finset.sum_add_distrib
      _ ≤ (∑ i ∈ s, volume ((V i).shade ∩ G))
            + (tau : ENNReal) * ∑ z ∈ T, volume (closedBall z r) := by gcongr
  · intro y hy
    obtain ⟨z, hzGood, hyz⟩ := Set.mem_iUnion₂.mp hy.2
    exact ⟨z, hyz, fun w hw => Set.mem_iUnion₂.mpr ⟨z, hzGood, hw⟩,
      (Finset.mem_filter.mp hzGood).2⟩

/-! ## The reduction from a mass-capturing region -/

/-- **The mass-region reduction.**

Given any measurable `G` such that

* `hmass` : the shades cut to `G` still carry `c1 a ^ ε` times the *total* mass of `(s, bodies Y)`,
  and
* `hcover` : every point of the retained union `U(s, Y'') ∩ G` lies in a `θb`-ball on which the
  retained union has density at least `c1 a ^ (4η) a ^ ε`,

the family `Y' i = (Y'' i).restrictShade G` on the **unchanged** index set `s` satisfies every
non-formal clause of `ShadedPlank.reduction_to_slab_atTypicalAngle`.

This is the mass-hypothesis analogue of
`ShadedPlank.reduction_atTypicalAngle_of_denseRegion`: it asks for the retained *mass* directly,
so no factor of the constant-multiplicity constant is spent here.  Nothing in the proof uses
`Kakeya.IsTypicalPlankAngle`, `Kakeya.IsEssentiallyDistinct` or `Plank.IsWindowedFamily`. -/
theorem reduction_atTypicalAngle_of_massRegion {η ε : ℝ}
    (s : Finset ι) (Y : ι → ShadedPlank a b hab hb1)
    (Y'' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (θ c1 : ℝ≥0)
    (hcar : 0 < ∑ i ∈ s, volume (ShadedPlank.bodies Y i).carrier)
    (href : ShadedBody.IsRefinement s Y'' s (ShadedPlank.bodies Y))
    (G : Set (EuclideanSpace ℝ (Fin 3))) (hGmeas : MeasurableSet G)
    (hmass : ((c1 * a ^ ε : ℝ≥0) : ENNReal)
          * (∑ i ∈ s, volume (ShadedPlank.bodies Y i).shade)
        ≤ ∑ i ∈ s, volume ((Y'' i).shade ∩ G))
    (hcover : ∀ y ∈ (⋃ i ∈ s, (Y'' i).shade) ∩ G,
      ∃ z : EuclideanSpace ℝ (Fin 3), y ∈ closedBall z ((θ * b : ℝ≥0) : ℝ) ∧
        ((c1 * a ^ (4 * η) * a ^ ε : ℝ≥0) : ENNReal)
            * volume (closedBall z ((θ * b : ℝ≥0) : ℝ))
          ≤ volume (((⋃ i ∈ s, (Y'' i).shade) ∩ G)
              ∩ closedBall z ((θ * b : ℝ≥0) : ℝ))) :
    ∃ (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))),
      ShadedBody.IsRefinement s Y' s (ShadedPlank.bodies Y) ∧
      ShadedBody.IsRefinement s Y' s Y'' ∧
      (c1 * a ^ ε) * ShadedBody.fullness s (ShadedPlank.bodies Y) ≤
        ShadedBody.fullness s Y' ∧
      (∀ x,
        ((⋃ i ∈ s, (Y' i).shade) ∩ Metric.closedBall x ((θ * b : ℝ))).Nonempty →
        ((c1 * a ^ (4 * η) * a ^ ε : ℝ≥0) : ENNReal) *
            volume (Metric.closedBall x ((θ * b : ℝ))) ≤
          volume ((⋃ i ∈ s, (Y' i).shade) ∩
            Metric.closedBall x (redPlankTube.ballDilation * θ * b))) := by
  classical
  set U : Set (EuclideanSpace ℝ (Fin 3)) := ⋃ i ∈ s, (Y'' i).shade with hU
  set t : ℝ≥0 := c1 * a ^ (4 * η) * a ^ ε with ht
  refine ⟨fun i => (Y'' i).restrictShade G hGmeas, ?_, ?_, ?_, ?_⟩
  · exact (ShadedBody.isRefinement_restrictShade s Y'' G hGmeas).trans href
  · exact ShadedBody.isRefinement_restrictShade s Y'' G hGmeas
  · have hCr : ShadedBody.IsCRefinement s
        (fun i => ShadedBody.restrictShade (Y'' i) G hGmeas) s (ShadedPlank.bodies Y)
        (c1 * a ^ ε) :=
      ⟨(ShadedBody.isRefinement_restrictShade s Y'' G hGmeas).trans href, hmass⟩
    exact ShadedBody.IsCRefinement.mul_fullness_le _ _ _ _ hcar hCr
  · intro x hmeet
    have hUG : (⋃ i ∈ s, (ShadedBody.restrictShade (Y'' i) G hGmeas).shade) = U ∩ G :=
      Plank.biUnion_restrictShade_shade s Y'' G hGmeas
    have hcover' : ∀ y ∈ U ∩ G, ∃ c : EuclideanSpace ℝ (Fin 3),
        y ∈ Plank.thetaBall θ b c ∧
        (t : ENNReal) * volume (Plank.thetaBall θ b c)
          ≤ volume ((U ∩ G) ∩ Plank.thetaBall θ b c) := by
      intro y hy
      obtain ⟨z, hyz, hz⟩ := hcover y hy
      exact ⟨z, hyz, hz⟩
    have hmeet' : ((U ∩ G) ∩ Metric.closedBall x ((θ * b : ℝ≥0) : ℝ)).Nonempty := by
      rw [← hUG]
      simpa using hmeet
    have hmain := Plank.localDensity_of_denseBallCover (theta := θ) (b := b)
      (U ∩ G) t hcover' x hmeet'
    rw [hUG]
    refine le_trans ?_ (le_trans hmain (measure_mono (Set.inter_subset_inter_right _ ?_)))
    · exact le_of_eq (by push_cast; ring)
    · have hrad : ((Kakeya.plankReduction.ballDilation : ℝ) * ((θ * b : ℝ≥0) : ℝ))
          = ((redPlankTube.ballDilation : ℝ) * (θ : ℝ) * (b : ℝ)) := by
        simp [Kakeya.plankReduction.ballDilation, redPlankTube.ballDilation]
        ring
      rw [hrad]

/-! ## The reduction from a ball cover and a scalar budget -/

/-- **The ball-cover budget reduction.**

Everything soft in `ShadedPlank.reduction_to_slab_atTypicalAngle` follows from a finite `θb`-ball
cover `T` of the shading union together with **two scalar inequalities**:

* `hledger : 2 (c1 a ^ ε) C ≤ 1` — the refinement ledger.  It says that after paying the incoming
  refinement coefficient `C⁻¹` there is still a factor `2` of slack, which is what buys the fixed
  half-discard.  In the application `c1 = δ ^ ε'`, `C ≤ δ ^ (-ε)` and `2 ε ≤ ε'`, so this is
  `2 δ ^ (ε' - ε) ≤ 1`, true as soon as `δ ^ ε ≤ 1/2`.
* `hbudget : 2 (c1 a ^ (4η) a ^ ε) C ∑_{z ∈ T} |B̄(z, θb)| ≤ |U(s, Y'')|` — the geometric budget.
  The minimal pointwise multiplicity `m₀` cancels between the discard threshold `τ = t C m₀` and
  the conversion of the surviving mass density into the union density, so `hbudget` does not
  mention the multiplicity at all.

Neither `Kakeya.IsTypicalPlankAngle` nor `Kakeya.IsEssentiallyDistinct` nor
`Plank.IsWindowedFamily` is used: those are what a producer of `hbudget` needs. -/
theorem reduction_atTypicalAngle_of_ballCoverBudget {η ε : ℝ}
    (s : Finset ι) (Y : ι → ShadedPlank a b hab hb1)
    (Y'' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (θ c1 C : ℝ≥0) (hC1 : 1 ≤ C)
    (hcar : 0 < ∑ i ∈ s, volume (ShadedPlank.bodies Y i).carrier)
    (hY'' : ShadedBody.IsCRefinement s Y'' s (ShadedPlank.bodies Y) C⁻¹)
    (hmult : ShadedBody.HasCConstantMultiplicity s Y'' C)
    (T : Finset (EuclideanSpace ℝ (Fin 3)))
    (hcov : (⋃ i ∈ s, (Y'' i).shade) ⊆ ⋃ z ∈ T, closedBall z ((θ * b : ℝ≥0) : ℝ))
    (hledger : 2 * (c1 * a ^ ε) * C ≤ 1)
    (hbudget : 2 * ((c1 * a ^ (4 * η) * a ^ ε * C : ℝ≥0) : ENNReal)
          * (∑ z ∈ T, volume (closedBall z ((θ * b : ℝ≥0) : ℝ)))
        ≤ volume (⋃ i ∈ s, (Y'' i).shade)) :
    ∃ (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))),
      ShadedBody.IsRefinement s Y' s (ShadedPlank.bodies Y) ∧
      ShadedBody.IsRefinement s Y' s Y'' ∧
      (c1 * a ^ ε) * ShadedBody.fullness s (ShadedPlank.bodies Y) ≤
        ShadedBody.fullness s Y' ∧
      (∀ x,
        ((⋃ i ∈ s, (Y' i).shade) ∩ Metric.closedBall x ((θ * b : ℝ))).Nonempty →
        ((c1 * a ^ (4 * η) * a ^ ε : ℝ≥0) : ENNReal) *
            volume (Metric.closedBall x ((θ * b : ℝ))) ≤
          volume ((⋃ i ∈ s, (Y' i).shade) ∩
            Metric.closedBall x (redPlankTube.ballDilation * θ * b))) := by
  classical
  set U : Set (EuclideanSpace ℝ (Fin 3)) := ⋃ i ∈ s, (Y'' i).shade with hU
  set r : ℝ := ((θ * b : ℝ≥0) : ℝ) with hr
  set t : ℝ≥0 := c1 * a ^ (4 * η) * a ^ ε with ht
  set kap : ℝ≥0 := c1 * a ^ ε with hkap
  set P : ENNReal := ∑ i ∈ s, volume (ShadedPlank.bodies Y i).shade with hP
  set S : ENNReal := ∑ i ∈ s, volume ((Y'' i).shade) with hS
  set Q : ENNReal := ∑ z ∈ T, volume (closedBall z r) with hQ
  have hCne : (C : ℝ≥0) ≠ 0 := (lt_of_lt_of_le zero_lt_one hC1).ne'
  -- `P ≤ C · S`, from the incoming refinement
  have hPS : P ≤ (C : ENNReal) * S := by
    have h := hY''.2
    have h' : (C : ENNReal) * ((C⁻¹ : ℝ≥0) : ENNReal) * P ≤ (C : ENNReal) * S := by
      rw [mul_assoc]
      exact mul_le_mul_right h _
    have hCC : (C : ENNReal) * ((C⁻¹ : ℝ≥0) : ENNReal) = 1 := by
      rw [← ENNReal.coe_mul, mul_inv_cancel₀ hCne, ENNReal.coe_one]
    rwa [hCC, one_mul] at h'
  have hB : 2 * ((kap : ℝ≥0) : ENNReal) * P ≤ S := by
    have hl : ((2 * kap * C : ℝ≥0) : ENNReal) ≤ 1 := by
      exact_mod_cast hledger
    calc 2 * ((kap : ℝ≥0) : ENNReal) * P
        ≤ 2 * ((kap : ℝ≥0) : ENNReal) * ((C : ENNReal) * S) := by gcongr
      _ = ((2 * kap * C : ℝ≥0) : ENNReal) * S := by push_cast; ring
      _ ≤ 1 * S := by gcongr
      _ = S := one_mul _
  by_cases hUne : U.Nonempty
  · obtain ⟨y0, hy0U, hy0min⟩ := Plank.exists_min_pointwiseMultiplicity s Y'' hUne
    set m0 : ℕ := ShadedBody.pointwiseMultiplicity s Y'' y0 with hm0
    have hm0pos : 1 ≤ m0 := by
      rw [hm0, Nat.one_le_iff_ne_zero]
      intro hz
      have : 0 < ShadedBody.pointwiseMultiplicity s Y'' y0 := by
        rw [ShadedBody.pointwiseMultiplicity_pos_iff s Y'' y0]
        obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.mp hy0U
        exact ⟨i, hi, hyi⟩
      omega
    set tau : ℝ≥0 := t * C * (m0 : ℝ≥0) with htau
    obtain ⟨G, hGmeas, hsplit, hgood⟩ :=
      exists_massRegion_of_ballCover s Y'' r T hcov tau
    -- lower bound `m₀ |U| ≤ S`
    have hSlow : (m0 : ENNReal) * volume U ≤ S := by
      have h := Plank.mul_volume_inter_le_sum_volume_shade_inter s Y'' hy0min Set.univ
      simpa [hU, hS, hm0] using h
    -- the discard is at most half the mass
    have hA : 2 * ((tau : ℝ≥0) : ENNReal) * Q ≤ S := by
      have hb2 : (m0 : ENNReal) *
          (2 * ((c1 * a ^ (4 * η) * a ^ ε * C : ℝ≥0) : ENNReal) * Q)
            ≤ (m0 : ENNReal) * volume U := by gcongr
      refine le_trans (le_of_eq ?_) (le_trans hb2 hSlow)
      rw [htau, ht]
      push_cast
      ring
    have hQfin : ((tau : ℝ≥0) : ENNReal) * Q ≠ ⊤ := by
      refine ENNReal.mul_ne_top ENNReal.coe_ne_top ?_
      rw [hQ]
      refine (ENNReal.sum_lt_top.2 fun z _ => ?_).ne
      exact measure_closedBall_lt_top
    have htauM : ((tau : ℝ≥0) : ENNReal) * Q ≤ ∑ i ∈ s, volume ((Y'' i).shade ∩ G) := by
      have h1 : ((tau : ℝ≥0) : ENNReal) * Q + ((tau : ℝ≥0) : ENNReal) * Q
          ≤ (∑ i ∈ s, volume ((Y'' i).shade ∩ G)) + ((tau : ℝ≥0) : ENNReal) * Q := by
        refine le_trans (le_of_eq ?_) (le_trans hA hsplit)
        ring
      exact (ENNReal.add_le_add_iff_right hQfin).mp h1
    have hmass : ((kap : ℝ≥0) : ENNReal) * P ≤ ∑ i ∈ s, volume ((Y'' i).shade ∩ G) := by
      have h2 : 2 * (((kap : ℝ≥0) : ENNReal) * P)
          ≤ 2 * (∑ i ∈ s, volume ((Y'' i).shade ∩ G)) := by
        calc 2 * (((kap : ℝ≥0) : ENNReal) * P) = 2 * ((kap : ℝ≥0) : ENNReal) * P := by ring
          _ ≤ S := hB
          _ ≤ (∑ i ∈ s, volume ((Y'' i).shade ∩ G)) + ((tau : ℝ≥0) : ENNReal) * Q := hsplit
          _ ≤ (∑ i ∈ s, volume ((Y'' i).shade ∩ G))
                + (∑ i ∈ s, volume ((Y'' i).shade ∩ G)) := by gcongr
          _ = 2 * (∑ i ∈ s, volume ((Y'' i).shade ∩ G)) := by ring
      exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).mp h2
    -- the union density on a good ball
    have hCm0ne : ((C : ENNReal) * (m0 : ENNReal)) ≠ 0 := by
      refine mul_ne_zero ?_ ?_
      · exact_mod_cast hCne
      · exact_mod_cast Nat.one_le_iff_ne_zero.mp hm0pos
    have hCm0top : ((C : ENNReal) * (m0 : ENNReal)) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.natCast_ne_top m0)
    have hcover : ∀ y ∈ U ∩ G, ∃ z : EuclideanSpace ℝ (Fin 3), y ∈ closedBall z r ∧
        ((t : ℝ≥0) : ENNReal) * volume (closedBall z r)
          ≤ volume ((U ∩ G) ∩ closedBall z r) := by
      intro y hy
      obtain ⟨z, hyz, hzG, hzmass⟩ := hgood y hy
      refine ⟨z, hyz, ?_⟩
      have heq : (U ∩ G) ∩ closedBall z r = U ∩ closedBall z r := by
        ext w
        constructor
        · rintro ⟨⟨hwU, -⟩, hwB⟩; exact ⟨hwU, hwB⟩
        · rintro ⟨hwU, hwB⟩; exact ⟨⟨hwU, hzG hwB⟩, hwB⟩
      rw [heq]
      have hup := sum_volume_shade_inter_le_of_hasCConstantMultiplicity s Y'' hmult hy0U
        (closedBall z r)
      have hchain : ((C : ENNReal) * (m0 : ENNReal)) * (((t : ℝ≥0) : ENNReal)
            * volume (closedBall z r))
          ≤ ((C : ENNReal) * (m0 : ENNReal)) * volume (U ∩ closedBall z r) := by
        refine le_trans (le_of_eq ?_) (le_trans hzmass ?_)
        · rw [htau]; push_cast; ring
        · refine le_trans hup (le_of_eq ?_)
          rw [hU, hm0]
      exact (ENNReal.mul_le_mul_iff_right hCm0ne hCm0top).mp hchain
    exact reduction_atTypicalAngle_of_massRegion (η := η) (ε := ε) s Y Y'' θ c1 hcar hY''.1
      G hGmeas hmass hcover
  · -- degenerate case: the shading union is empty
    rw [Set.not_nonempty_iff_eq_empty] at hUne
    have hS0 : S = 0 := by
      rw [hS]
      refine Finset.sum_eq_zero fun i hi => ?_
      have : (Y'' i).shade ⊆ U := fun x hx => Set.mem_biUnion hi hx
      rw [Set.subset_eq_empty this hUne, measure_empty]
    have hP0 : P = 0 := by
      have h := hPS
      rw [hS0, mul_zero] at h
      exact le_antisymm h bot_le
    refine reduction_atTypicalAngle_of_massRegion (η := η) (ε := ε) s Y Y'' θ c1 hcar hY''.1
      Set.univ MeasurableSet.univ ?_ ?_
    · rw [← hP, hP0, mul_zero]
      exact bot_le
    · intro y hy
      exfalso
      have hyU : y ∈ U := hy.1
      rw [hUne] at hyU
      exact hyU

/-! ## The target, modulo one scalar inequality -/

/-- **`ShadedPlank.reduction_to_slab_atTypicalAngle` modulo one thickening inequality.**

The target statement of `Section6Compat.lean` verbatim — same binders, same hypotheses, same
`128 * ε ≤ ε'`, same conclusion — with exactly one hypothesis inserted just before the conclusion,
and proved.  The inserted hypothesis is the scalar inequality

```
54 · δ ^ ε' · a ^ (4η) · a ^ ε · C · |N_{θb}(U(s, Y''))| ≤ |U(s, Y'')|,
```

`N_r` being `Metric.cthickening r`.  There is no set to construct, no cover to exhibit and no
multiplicity: it is a bound on how much the `θb`-thickening of the shading union may inflate its
volume.

The threshold witness is `δthr = 2 ^ (-1/ε)`, and it is used exactly once, to make
`2 δ ^ (ε' - ε) ≤ 1`; that is the only place `128 * ε ≤ ε'` enters, and it uses only `2 * ε ≤ ε'`
of it.

The factor `C` is the constant the caller actually supplied, not its bound `δ ^ (-ε)`, so a
producer that knows `C` may use it. -/
theorem reduction_to_slab_atTypicalAngle_of_thickening :
    ∀ {η ε ε' : ℝ}, 0 < η → 0 < ε → 0 < ε' → 128 * ε ≤ ε' →
    ∀ (Ccard : ℝ≥0) (D : ℝ),
    ∃ δthr : ℝ≥0, 0 < δthr ∧ δthr ≤ 1 ∧
    ∀ {ι : Type*} (s : Finset ι)
      {δ a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
      (Y : ι → ShadedPlank a b hab hb1)
      (θ : ℝ≥0) (_hθ1 : θ ≤ 1) (C : ℝ≥0)
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
      (((54 * (δ ^ ε' * a ^ (4 * η) * a ^ ε) * C : ℝ≥0) : ENNReal)
          * volume (Metric.cthickening ((θ * b : ℝ≥0) : ℝ) (⋃ i ∈ s, (Y'' i).shade))
        ≤ volume (⋃ i ∈ s, (Y'' i).shade)) →
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
        (c1 : ENNReal) * (a : ENNReal) ^ (4 * η) * (a : ENNReal) ^ ε *
            volume (Metric.closedBall x ((θ * b : ℝ))) ≤
          volume ((⋃ i ∈ s', (Y' i).shade) ∩
            Metric.closedBall x (redPlankTube.ballDilation * θ * b))) ∧
      c1⁻¹ ≤ δ ^ (-ε') := by
  intro η ε ε' hη hε hε' hgap Ccard D
  classical
  refine ⟨(2 : ℝ≥0) ^ (-(1 / ε)), NNReal.rpow_pos (by norm_num), ?_, ?_⟩
  · exact NNReal.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      (neg_nonpos.mpr (by positivity : (0 : ℝ) ≤ 1 / ε))
  intro ι s δ a b hab hb1 Y θ _hθ1 C Y'' hδ hδa ha1 hδthr _hwin hfull _hma _hmd _h2 _hcard
    hθlb hC1 hCδ hYref hYmult _htyp hmaxA hthick
  have ha : (0 : ℝ≥0) < a := lt_of_lt_of_le hδ hδa
  have hb : (0 : ℝ≥0) < b := lt_of_lt_of_le ha hab
  have hδne : (δ : ℝ≥0) ≠ 0 := hδ.ne'
  have hδ1 : (δ : ℝ≥0) ≤ 1 := le_trans hδa ha1.le
  -- the index set is nonempty, because the fullness of the empty family is `0`
  have hsne : s.Nonempty := by
    rcases Finset.eq_empty_or_nonempty s with hs | hs
    · exfalso
      have hz : ShadedBody.fullness s (ShadedPlank.bodies Y) = 0 := by simp [hs]
      rw [hz] at hfull
      exact absurd (le_antisymm hfull bot_le) (NNReal.rpow_pos ha).ne'
    · exact hs
  have hcar : 0 < ∑ i ∈ s, volume (ShadedPlank.bodies Y i).carrier := by
    obtain ⟨i0, hi0⟩ := hsne
    have hpos : 0 < volume ((ShadedPlank.bodies Y i0).carrier :
        Set (EuclideanSpace ℝ (Fin 3))) := by
      rw [show ((ShadedPlank.bodies Y i0).carrier : Set (EuclideanSpace ℝ (Fin 3)))
        = (Y i0).carrier from rfl, ShadedPlank.volume_carrier (Y i0)]
      refine ENNReal.mul_pos (ENNReal.mul_pos (by norm_num) (ENNReal.coe_pos.mpr ha).ne').ne'
        (ENNReal.coe_pos.mpr hb).ne'
    exact lt_of_lt_of_le hpos (Finset.single_le_sum (f := fun i =>
      volume ((ShadedPlank.bodies Y i).carrier : Set (EuclideanSpace ℝ (Fin 3))))
      (fun i _ => bot_le) hi0)
  -- the radius is positive
  have hθ : (0 : ℝ≥0) < θ := lt_of_lt_of_le (by positivity) hθlb
  have hr : (0 : ℝ) < ((θ * b : ℝ≥0) : ℝ) := by
    exact_mod_cast mul_pos hθ hb
  -- the refinement ledger, from the threshold on `δ`
  have hledger : 2 * ((δ : ℝ≥0) ^ ε' * a ^ ε) * C ≤ 1 := by
    have haε : (a : ℝ≥0) ^ ε ≤ 1 := NNReal.rpow_le_one ha1.le hε.le
    have hstep : 2 * ((δ : ℝ≥0) ^ ε' * a ^ ε) * C ≤ 2 * ((δ : ℝ≥0) ^ ε' * 1) * δ ^ (-ε) := by
      gcongr
    have hsimp : (2 : ℝ≥0) * ((δ : ℝ≥0) ^ ε' * 1) * δ ^ (-ε) = 2 * δ ^ (ε' - ε) := by
      rw [mul_one, mul_assoc, ← NNReal.rpow_add hδne]
      ring_nf
    have hge : (δ : ℝ≥0) ^ (ε' - ε) ≤ δ ^ ε :=
      NNReal.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
    have hthr : (δ : ℝ≥0) ^ ε ≤ ((2 : ℝ≥0) ^ (-(1 / ε))) ^ ε :=
      NNReal.rpow_le_rpow hδthr hε.le
    have hval : ((2 : ℝ≥0) ^ (-(1 / ε))) ^ ε = (2 : ℝ≥0)⁻¹ := by
      rw [← NNReal.rpow_mul]
      rw [show (-(1 / ε)) * ε = (-1 : ℝ) by field_simp]
      rw [NNReal.rpow_neg, NNReal.rpow_one]
    calc 2 * ((δ : ℝ≥0) ^ ε' * a ^ ε) * C
        ≤ 2 * ((δ : ℝ≥0) ^ ε' * 1) * δ ^ (-ε) := hstep
      _ = 2 * (δ : ℝ≥0) ^ (ε' - ε) := hsimp
      _ ≤ 2 * (δ : ℝ≥0) ^ ε := by gcongr
      _ ≤ 2 * ((2 : ℝ≥0) ^ (-(1 / ε))) ^ ε := by gcongr
      _ = 2 * (2 : ℝ≥0)⁻¹ := by rw [hval]
      _ = 1 := by
          rw [mul_inv_cancel₀ (by norm_num : (2 : ℝ≥0) ≠ 0)]
  -- produce a `θb`-ball cover of the shading union whose total ball volume is controlled
  obtain ⟨T, hTcov, hbudget⟩ :
      ∃ T : Finset (EuclideanSpace ℝ (Fin 3)),
        (⋃ i ∈ s, (Y'' i).shade) ⊆ ⋃ z ∈ T, closedBall z ((θ * b : ℝ≥0) : ℝ) ∧
        2 * (((δ : ℝ≥0) ^ ε' * a ^ (4 * η) * a ^ ε * C : ℝ≥0) : ENNReal)
            * (∑ z ∈ T, volume (closedBall z ((θ * b : ℝ≥0) : ℝ)))
          ≤ volume (⋃ i ∈ s, (Y'' i).shade) := by
    by_cases hUne : (⋃ i ∈ s, (Y'' i).shade).Nonempty
    · have hbdd : Bornology.IsBounded (⋃ i ∈ s, (Y'' i).shade) := by
        rw [Bornology.isBounded_biUnion_finset s]
        intro i _
        exact ((Y'' i).isCompact.isBounded).subset (Y'' i).shade_subset
      obtain ⟨T, hTA, _hTne, hsep, hcov⟩ :=
        Metric.exists_finset_separated_cover hUne hbdd hr
      refine ⟨T, hcov, ?_⟩
      have hpack := sum_volume_closedBall_le_cthickening (A := ⋃ i ∈ s, (Y'' i).shade)
        hr (fun z hz => hTA hz) hsep
      calc 2 * (((δ : ℝ≥0) ^ ε' * a ^ (4 * η) * a ^ ε * C : ℝ≥0) : ENNReal)
              * (∑ z ∈ T, volume (closedBall z ((θ * b : ℝ≥0) : ℝ)))
          ≤ 2 * (((δ : ℝ≥0) ^ ε' * a ^ (4 * η) * a ^ ε * C : ℝ≥0) : ENNReal)
              * (27 * volume (Metric.cthickening ((θ * b : ℝ≥0) : ℝ)
                  (⋃ i ∈ s, (Y'' i).shade))) := by gcongr
        _ = ((54 * ((δ : ℝ≥0) ^ ε' * a ^ (4 * η) * a ^ ε) * C : ℝ≥0) : ENNReal)
              * volume (Metric.cthickening ((θ * b : ℝ≥0) : ℝ)
                  (⋃ i ∈ s, (Y'' i).shade)) := by
            push_cast
            ring
        _ ≤ volume (⋃ i ∈ s, (Y'' i).shade) := hthick
    · refine ⟨∅, ?_, ?_⟩
      · rw [Set.not_nonempty_iff_eq_empty] at hUne
        rw [hUne]
        exact Set.empty_subset _
      · simp
  obtain ⟨Y', href1, href2, hfullret, hitem1⟩ :=
    reduction_atTypicalAngle_of_ballCoverBudget (η := η) (ε := ε) s Y Y'' θ ((δ : ℝ≥0) ^ ε') C
      hC1 hcar hYref hYmult T hTcov hledger hbudget
  refine ⟨s, Y', (δ : ℝ≥0) ^ ε', NNReal.rpow_pos hδ, href1, href2, hfullret, ?_, ?_⟩
  · intro x hx
    have hco : (((δ : ℝ≥0) ^ ε' * a ^ (4 * η) * a ^ ε : ℝ≥0) : ENNReal)
        = (((δ : ℝ≥0) ^ ε' : ℝ≥0) : ENNReal) * (a : ENNReal) ^ (4 * η)
            * (a : ENNReal) ^ ε := by
      rw [ENNReal.coe_mul, ENNReal.coe_mul,
        ENNReal.coe_rpow_of_nonneg _ (by positivity : (0 : ℝ) ≤ 4 * η),
        ENNReal.coe_rpow_of_nonneg _ hε.le]
    rw [← hco]
    exact hitem1 x hx
  · rw [NNReal.rpow_neg]


/-- **Drift tripwire: the thickening obligation really does close
`ShadedPlank.reduction_to_slab_atTypicalAngle`.**

The hypothesis `H` is the target statement with its conclusion replaced by the thickening
obligation, and the conclusion of this theorem is the target statement *verbatim* — copied from
`Section6Compat.lean`, with only `Type*` written as `Type u` so that the two occurrences share a
universe.

The obligation is allowed its own `δ`-threshold, exactly as the target is; the two thresholds are
combined with `min`. -/
theorem reduction_to_slab_atTypicalAngle_of_thickeningObligation.{u}
    (H :
    ∀ {η ε ε' : ℝ}, 0 < η → 0 < ε → 0 < ε' → 128 * ε ≤ ε' →
    ∀ (Ccard : ℝ≥0) (D : ℝ),
    ∃ δthr : ℝ≥0, 0 < δthr ∧ δthr ≤ 1 ∧
    ∀ {ι : Type u} (s : Finset ι)
      {δ a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
      (Y : ι → ShadedPlank a b hab hb1)
      (θ : ℝ≥0) (_hθ1 : θ ≤ 1) (C : ℝ≥0)
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
    (((54 * (δ ^ ε' * a ^ (4 * η) * a ^ ε) * C : ℝ≥0) : ENNReal)
        * volume (Metric.cthickening ((θ * b : ℝ≥0) : ℝ) (⋃ i ∈ s, (Y'' i).shade))
      ≤ volume (⋃ i ∈ s, (Y'' i).shade))
) :
    ∀ {η ε ε' : ℝ}, 0 < η → 0 < ε → 0 < ε' → 128 * ε ≤ ε' →
    ∀ (Ccard : ℝ≥0) (D : ℝ),
    ∃ δthr : ℝ≥0, 0 < δthr ∧ δthr ≤ 1 ∧
    ∀ {ι : Type u} (s : Finset ι)
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
  intro η ε ε' hη hε hε' hgap Ccard D
  obtain ⟨δthr₁, hpos₁, hle₁, hH⟩ := H hη hε hε' hgap Ccard D
  obtain ⟨δthr₂, hpos₂, hle₂, hmain⟩ :=
    reduction_to_slab_atTypicalAngle_of_thickening hη hε hε' hgap Ccard D
  refine ⟨min δthr₁ δthr₂, lt_min hpos₁ hpos₂, (min_le_left _ _).trans hle₁, ?_⟩
  intro ι s δ a b hab hb1 Y θ hθ1 C Y'' hδ hδa ha1 hthr hwin hfull hma hmd h2 hcard
    hθlb hC1 hCδ hYref hYmult htyp hmaxA
  exact hmain s Y θ hθ1 C Y'' hδ hδa ha1 (hthr.trans (min_le_right _ _)) hwin hfull hma hmd
    h2 hcard hθlb hC1 hCδ hYref hYmult htyp hmaxA
    (hH s Y θ hθ1 C Y'' hδ hδa ha1 (hthr.trans (min_le_left _ _)) hwin hfull hma hmd
      h2 hcard hθlb hC1 hCδ hYref hYmult htyp hmaxA)

/-- **The window form of the obligation**: a bare volume lower bound on the shading union.

Since a windowed family lives in `B̄(0, Plank.windowRadius) = B̄(0, 4)` and `θ b ≤ 1`, the
`θb`-thickening of the shading union is contained in `B̄(0, 5)`, so the thickening obligation of
`ShadedPlank.reduction_to_slab_atTypicalAngle_of_thickening` follows from the `θ`-free and `b`-free
inequality

```
54 · δ ^ ε' · a ^ (4η) · a ^ ε · C · |B̄(0, 5)| ≤ |U(s, Y'')|.
```

This is the crudest of the three entry points and it is genuinely weaker than the theorem: it is
false for the extremal bush family (`|s| = µ` planks through one core box), where `|U(s, Y'')|` is
only `≈ a ^ (1 + η)` while the right-hand side is `≈ a ^ (4η + ε + ε')`.  In that family the sharp
obligation still holds, because the typicality hypothesis forces `θ ≈ a ^ (1 - η/2)` and the
thickening is then only `a ^ (-η/2)` times the union.  So this corollary is for the regimes in
which `θ b` is comparable to the window, where the thickening is the window and nothing is lost. -/
theorem reduction_to_slab_atTypicalAngle_of_volumeLowerBound :
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
      (((54 * (δ ^ ε' * a ^ (4 * η) * a ^ ε) * C : ℝ≥0) : ENNReal)
          * volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 5)
        ≤ volume (⋃ i ∈ s, (Y'' i).shade)) →
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
        (c1 : ENNReal) * (a : ENNReal) ^ (4 * η) * (a : ENNReal) ^ ε *
            volume (Metric.closedBall x ((θ * b : ℝ))) ≤
          volume ((⋃ i ∈ s', (Y' i).shade) ∩
            Metric.closedBall x (redPlankTube.ballDilation * θ * b))) ∧
      c1⁻¹ ≤ δ ^ (-ε') := by
  intro η ε ε' hη hε hε' hgap Ccard D
  obtain ⟨δthr, hpos, hle, hmain⟩ :=
    reduction_to_slab_atTypicalAngle_of_thickening hη hε hε' hgap Ccard D
  refine ⟨δthr, hpos, hle, ?_⟩
  intro ι s δ a b hab hb1 Y θ hθ1 C Y'' hδ hδa ha1 hthr hwin hfull hma hmd h2 hcard
    hθlb hC1 hCδ hYref hYmult htyp hmaxA hvol
  refine hmain s Y θ hθ1 C Y'' hδ hδa ha1 hthr hwin hfull hma hmd h2 hcard hθlb hC1 hCδ
    hYref hYmult htyp hmaxA ?_
  -- the whole `θb`-thickening of the shading union sits inside `B̄(0, 5)`
  have hUwin : (⋃ i ∈ s, (Y'' i).shade)
      ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 4 := by
    refine Set.iUnion₂_subset fun i hi => ?_
    have h1 : (Y'' i).shade ⊆ (ShadedPlank.bodies Y i).shade := (hYref.1.2 i hi).2
    have h2' : (ShadedPlank.bodies Y i).shade
        ⊆ ((ShadedPlank.planks Y i).carrier : Set (EuclideanSpace ℝ (Fin 3))) :=
      ShadedPlank.bodies_shade_subset_planks Y i
    have h3 : ((ShadedPlank.planks Y i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
        ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) Plank.windowRadius := hwin i hi
    exact h1.trans (h2'.trans h3)
  have hrle : ((θ * b : ℝ≥0) : ℝ) ≤ 1 := by
    have : (θ * b : ℝ≥0) ≤ 1 := by
      calc (θ * b : ℝ≥0) ≤ 1 * 1 := by gcongr
        _ = 1 := one_mul 1
    exact_mod_cast this
  have hrnn : (0 : ℝ) ≤ ((θ * b : ℝ≥0) : ℝ) := (θ * b).coe_nonneg
  have hsub : Metric.cthickening ((θ * b : ℝ≥0) : ℝ) (⋃ i ∈ s, (Y'' i).shade)
      ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 5 := by
    refine (Metric.cthickening_subset_of_subset _ hUwin).trans ?_
    rw [_root_.cthickening_closedBall hrnn (by norm_num)]
    exact Metric.closedBall_subset_closedBall (by linarith)
  exact le_trans (by gcongr) hvol

end ShadedPlank

end
