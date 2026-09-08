/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.Reduction
public import Kakeya.DimensionThree.Plank.LocalDensity
public import Kakeya.DimensionThree.Plank.RelativeMultiplicity

/-!
# The dense-region reduction for `ShadedPlank.reduction_to_slab_atTypicalAngle`

`ShadedPlank.reduction_to_slab_atTypicalAngle` (`Section6Compat.lean`) is GWZ Lemma 6.13 read
through GWZ Remark 6.14 (`typicalAngleAlreadyPresent`): the plank-to-slab reduction run at an
*already prescribed* typical angle `θ`, with every loss read at the auxiliary scale `δ ≤ a`
instead of at the plank scale `a`.  Its conclusion has three quantitative clauses — the fullness
retention, Item 1 at *every* centre, and `c1⁻¹ ≤ δ ^ (-ε')`.

This file isolates the *soft* half of that conclusion and reduces the theorem to a single
inequality.  The construction is GWZ's own "final dense-ball selection" of Step 3: cover the
shading union `U = U(s, Y'')` by finitely many `θb`-balls, **discard the sparse ones**, and cut
every shade to the union `G` of the balls that survive.

* `ShadedPlank.reduction_atTypicalAngle_of_denseRegion` is the reduction proper, in its sharpest
  form: from *any* measurable `G` retaining a `ρ`-fraction of `U(s, Y'')` and carrying a
  dense-ball certificate on the retained union, it produces every non-formal clause of the
  target — both `ShadedBody.IsRefinement` clauses, the fullness retention, and Item 1 at every
  centre at the literal dilation `ShadedPlank.redPlankTube.ballDilation = 3`.
* `ShadedPlank.denseBalls_certificate` and `ShadedPlank.exists_denseRegion_of_ballCover` are two
  producers of such a `G`: the first takes a finite family of `t`-dense balls and checks that the
  density survives passing to the retained set; the second is the discard step, for an arbitrary
  set, an arbitrary radius and an arbitrary finite ball cover.
* `ShadedPlank.reduction_atTypicalAngle_of_denseBallCover` composes the two.
* `ShadedPlank.reduction_to_slab_atTypicalAngle_of_denseRegion` and
  `ShadedPlank.reduction_to_slab_atTypicalAngle_of_avgDensity` are the target statement
  *verbatim* — same binders, same hypotheses, same `128 * ε ≤ ε'`, same conclusion — with exactly
  one hypothesis added, and they are proved.  The first takes the region form and is the weakest
  obligation; the second takes the **average-density obligation**

  ```
  ∃ T, U(s, Y'') ⊆ ⋃ z ∈ T, B̄(z, θb) ∧
       δ ^ ε' · a ^ (4η) · a ^ ε · (∑ z ∈ T, |B̄(z, θb)|)
         + δ ^ (ε' - 2ε) · a ^ ε · |U(s, Y'')| ≤ |U(s, Y'')|
  ```

  and it is the whole remaining mathematical content of the target: it says that `U(s, Y'')`
  fills its own `θb`-covering to average density `≳ δ ^ ε' a ^ (4η)`, which is Item 1 in
  *average* form.  It is exactly what GWZ Step 3 (`slab3`, after rescaling each
  `θb × b × b` box) proves, and it is the step at which the typical angle, the constant
  multiplicity and the essential distinctness of the planks must be used.  Nothing else is
  needed: no threshold on `δ` is required (`δthr = 1` works), and the exponent hypothesis
  `128 * ε ≤ ε'` is used *unchanged*.

## The exponent ledger, in full

Take `c1 := δ ^ ε'`, the smallest value the clause `c1⁻¹ ≤ δ ^ (-ε')` permits — every other
clause is hardest there, so it is the right choice.  Two factors of `δ ^ ε` are spent, and only
two:

* the incoming refinement `ShadedBody.IsCRefinement s Y'' s (bodies Y) C⁻¹` costs `C⁻¹ ≥ δ ^ ε`;
* the discard costs one more `C`, because `Plank.isCRefinement_restrictShade_of_dense` converts
  a *union* capture into a *mass* capture at the price of the constant-multiplicity constant.

So the composite refinement coefficient is `C⁻¹ · (c1 a ^ ε · C) = c1 a ^ ε` provided
`(c1 a ^ ε) C ² ≤ ρ`, and with `C ≤ δ ^ (-ε)` the retention ratio that has to be achieved is
`ρ = δ ^ (ε' - 2ε) a ^ ε`, which is `< 1` precisely because `128 * ε ≤ ε'` and `a < 1`.  That is
the second summand of the obligation.  Nothing is left over for a further `δ`-dependent loss:
any route whose Item-1 density degrades by more than `δ ^ (ε' - 2ε)` needs the hypothesis
strengthened, and the honest place to see that is now inside the obligation rather than
diffused through the proof.

## Why the single-ball reduction of `Section6CompatBall.lean` cannot be used

`ShadedPlank.reduction_atTypicalAngle_of_denseBall` takes `Y' i = (Y'' i).restrictShade B̄(z, θb)`
for a **single** ball.  That is sound, but its mass hypothesis is unsatisfiable in the main
regime, and this file certifies it:

* `ShadedPlank.denseBall_mass_forces_ball_volume` shows the single-ball mass clause forces
  `κ · λ(s, bodies Y) · 8ab ≤ |B̄(z, θb)|`;
* `ShadedPlank.denseBall_mass_forces_cube_bound` puts this in closed form,
  `κ · λ · a · b ≤ (θb) ³`;
* `ShadedPlank.singleBall_necessary_condition_fails` shows that at `δ = a`, `b = 1`,
  `θ = a / b = a` (the smallest angle the hypothesis `a / b ≤ θ` allows),
  `λ = a ^ η` and `κ = c1 a ^ ε = δ ^ ε' a ^ ε` this reads `a ^ (1 + η + ε + ε') ≤ a ^ 3`, which
  is false for every `0 < a < 1` as soon as `η + ε + ε' < 2`.

Geometrically: one ball of radius `θb` holds volume `≈ (θb) ³`, while the fullness clause asks
the retained family to keep a `δ ^ ε' a ^ ε`-fraction — i.e. essentially all — of the mass
`8abλ` of an average plank.  For `θb ≈ a` and `b ≈ 1` there is a deficit of `a ^ 2`.  The output
family must therefore be spread over *many* `θb`-balls, which is what the dense-region
construction of this file does and what GWZ's Step 3 does.
-/

@[expose] public section

open MeasureTheory Metric
open scoped NNReal Real ENNReal

noncomputable section

namespace ShadedPlank

variable {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}

/-- **Discarding the sparse balls of a finite ball cover.**

Let `U` have finite volume and be covered by the balls `B̄(z, r)`, `z ∈ T`, with `T` finite.  Call
`z` *good* when `U` fills `B̄(z, r)` to density at least `t`, and let `G` be the union of the good
balls.  Then

* `G` retains a `ρ`-fraction of `U`, `ρ|U| ≤ |U ∩ G|`, as soon as the sparse balls cannot carry
  more than `(1 - ρ)|U|`, which is the hypothesis `hdiscard` written without subtraction; and
* every point of `U ∩ G` is handed a good ball, and on a good ball `U ∩ G` and `U` agree,
  because a good ball is contained in `G`.

The second clause is exactly the `hcover` input of `Plank.localDensity_of_denseBallCover`, so it
upgrades to a local-density statement at *every* centre, at dilation `3`.

No measurability of `U` is needed: `G` is a finite union of closed balls, and
`MeasureTheory.measure_inter_add_sdiff` splits `U` along it. -/
theorem exists_denseRegion_of_ballCover
    (U : Set (EuclideanSpace ℝ (Fin 3))) (hUtop : volume U ≠ ⊤)
    (r : ℝ) (T : Finset (EuclideanSpace ℝ (Fin 3)))
    (hcov : U ⊆ ⋃ z ∈ T, closedBall z r) (t ρ : ℝ≥0)
    (hdiscard : (t : ENNReal) * (∑ z ∈ T, volume (closedBall z r))
        + (ρ : ENNReal) * volume U ≤ volume U) :
    ∃ G : Set (EuclideanSpace ℝ (Fin 3)), MeasurableSet G ∧
      (ρ : ENNReal) * volume U ≤ volume (U ∩ G) ∧
      (∀ y ∈ U ∩ G, ∃ z : EuclideanSpace ℝ (Fin 3), y ∈ closedBall z r ∧
        (t : ENNReal) * volume (closedBall z r)
          ≤ volume ((U ∩ G) ∩ closedBall z r)) := by
  classical
  set Good : Finset (EuclideanSpace ℝ (Fin 3)) :=
    T.filter (fun z => (t : ENNReal) * volume (closedBall z r)
      ≤ volume (U ∩ closedBall z r)) with hGood
  set G : Set (EuclideanSpace ℝ (Fin 3)) := ⋃ z ∈ Good, closedBall z r with hG
  have hGmeas : MeasurableSet G := by
    refine MeasurableSet.biUnion (Finset.countable_toSet Good) ?_
    exact fun z _ => measurableSet_closedBall
  refine ⟨G, hGmeas, ?_, ?_⟩
  · -- the retained fraction
    have hsub : U \ G ⊆ ⋃ z ∈ (T \ Good), (U ∩ closedBall z r) := by
      intro y hy
      obtain ⟨z, hzT, hyz⟩ := Set.mem_iUnion₂.mp (hcov hy.1)
      have hzGood : z ∉ Good := by
        intro hz
        exact hy.2 (Set.mem_iUnion₂.mpr ⟨z, hz, hyz⟩)
      exact Set.mem_iUnion₂.mpr ⟨z, Finset.mem_sdiff.mpr ⟨hzT, hzGood⟩, ⟨hy.1, hyz⟩⟩
    have hbad : ∀ z ∈ T \ Good, volume (U ∩ closedBall z r)
        ≤ (t : ENNReal) * volume (closedBall z r) := by
      intro z hz
      have hz' := (Finset.mem_sdiff.mp hz).2
      have : ¬ ((t : ENNReal) * volume (closedBall z r) ≤ volume (U ∩ closedBall z r)) := by
        intro hcon
        exact hz' (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hz).1, hcon⟩)
      exact le_of_lt (not_le.mp this)
    have hdiff : volume (U \ G) ≤ (t : ENNReal) * (∑ z ∈ T, volume (closedBall z r)) := by
      calc volume (U \ G) ≤ ∑ z ∈ T \ Good, volume (U ∩ closedBall z r) := by
            refine le_trans (measure_mono hsub) ?_
            exact measure_biUnion_finset_le _ _
        _ ≤ ∑ z ∈ T \ Good, (t : ENNReal) * volume (closedBall z r) :=
            Finset.sum_le_sum hbad
        _ ≤ ∑ z ∈ T, (t : ENNReal) * volume (closedBall z r) :=
            Finset.sum_le_sum_of_subset (Finset.sdiff_subset)
        _ = (t : ENNReal) * (∑ z ∈ T, volume (closedBall z r)) := by
            rw [Finset.mul_sum]
    have hsplit : volume (U ∩ G) + volume (U \ G) = volume U :=
      measure_inter_add_sdiff U hGmeas
    have hkey : (ρ : ENNReal) * volume U + volume (U \ G)
        ≤ volume (U ∩ G) + volume (U \ G) := by
      rw [hsplit]
      calc (ρ : ENNReal) * volume U + volume (U \ G)
          ≤ (ρ : ENNReal) * volume U
              + (t : ENNReal) * (∑ z ∈ T, volume (closedBall z r)) := by gcongr
        _ = (t : ENNReal) * (∑ z ∈ T, volume (closedBall z r))
              + (ρ : ENNReal) * volume U := by ring
        _ ≤ volume U := hdiscard
    have hfin : volume (U \ G) ≠ ⊤ :=
      ne_top_of_le_ne_top hUtop (measure_mono Set.sdiff_subset)
    exact (ENNReal.add_le_add_iff_right hfin).mp hkey
  · -- the dense-ball certificate
    intro y hy
    obtain ⟨z, hzGood, hyz⟩ := Set.mem_iUnion₂.mp hy.2
    refine ⟨z, hyz, ?_⟩
    have hball : closedBall z r ⊆ G := fun w hw => Set.mem_iUnion₂.mpr ⟨z, hzGood, hw⟩
    have heq : (U ∩ G) ∩ closedBall z r = U ∩ closedBall z r := by
      ext w
      constructor
      · rintro ⟨⟨hwU, -⟩, hwB⟩; exact ⟨hwU, hwB⟩
      · rintro ⟨hwU, hwB⟩; exact ⟨⟨hwU, hball hwB⟩, hwB⟩
    rw [heq]
    exact (Finset.mem_filter.mp hzGood).2



/-- **A finite family of dense balls is a dense region.**

If every `z ∈ Tg` is the centre of a ball on which `U` has density at least `t`, then the union
`G = ⋃ z ∈ Tg, B̄(z, r)` is measurable and carries the dense-ball certificate of
`ShadedPlank.reduction_atTypicalAngle_of_denseRegion` *for the retained set* `U ∩ G` — the density
does not degrade on passing from `U` to `U ∩ G`, because each good ball is contained in `G`.

So a producer of the remaining obligation only has to exhibit finitely many `t`-dense `θ b`-balls
whose union captures a `ρ`-fraction of `U(s, Y'')`; it never has to reason about the retained set. -/
theorem denseBalls_certificate (U : Set (EuclideanSpace ℝ (Fin 3))) (r : ℝ)
    (Tg : Finset (EuclideanSpace ℝ (Fin 3))) (t : ℝ≥0)
    (hgood : ∀ z ∈ Tg, (t : ENNReal) * volume (closedBall z r)
      ≤ volume (U ∩ closedBall z r)) :
    MeasurableSet (⋃ z ∈ Tg, closedBall z r) ∧
      ∀ y ∈ U ∩ (⋃ z ∈ Tg, closedBall z r),
        ∃ z : EuclideanSpace ℝ (Fin 3), y ∈ closedBall z r ∧
          (t : ENNReal) * volume (closedBall z r)
            ≤ volume ((U ∩ (⋃ z ∈ Tg, closedBall z r)) ∩ closedBall z r) := by
  classical
  refine ⟨MeasurableSet.biUnion (Finset.countable_toSet Tg)
    (fun z _ => measurableSet_closedBall), ?_⟩
  intro y hy
  obtain ⟨z, hzTg, hyz⟩ := Set.mem_iUnion₂.mp hy.2
  refine ⟨z, hyz, ?_⟩
  have hball : closedBall z r ⊆ ⋃ w ∈ Tg, closedBall w r :=
    fun w hw => Set.mem_iUnion₂.mpr ⟨z, hzTg, hw⟩
  have heq : (U ∩ (⋃ w ∈ Tg, closedBall w r)) ∩ closedBall z r = U ∩ closedBall z r := by
    ext w
    constructor
    · rintro ⟨⟨hwU, -⟩, hwB⟩; exact ⟨hwU, hwB⟩
    · rintro ⟨hwU, hwB⟩; exact ⟨⟨hwU, hball hwB⟩, hwB⟩
  rw [heq]
  exact hgood z hzTg

/-- **The dense-region reduction, sharpest form.**

Given *any* measurable region `G` such that

* `hdense` : `G` retains a `ρ`-fraction of the shading union, `ρ|U| ≤ |U ∩ G|`, and
* `hcover` : every point of the retained union `U ∩ G` lies in a `θb`-ball on which `U ∩ G`
  has density at least `c1 · a ^ (4η) · a ^ ε`,

the family `Y' i = (Y'' i).restrictShade G` on the **unchanged** index set `s` satisfies every
non-formal clause of `ShadedPlank.reduction_to_slab_atTypicalAngle`: it refines both
`(s, bodies Y)` and `(s, Y'')`, it retains the fullness at `c1 · a ^ ε`, and it satisfies Item 1
at *every* centre at the literal dilation `ShadedPlank.redPlankTube.ballDilation = 3`.

The ledger hypothesis is `hscale : (c1 * a ^ ε) * C * C ≤ ρ`.  One `C` is the incoming refinement
coefficient `C⁻¹` of `hY''`; the other is the price
`Plank.isCRefinement_restrictShade_of_dense` charges for turning a *union* capture
`ρ|U| ≤ |U ∩ G|` into a *mass* capture `Σ_i |Y''_i ∩ G| ≥ (c1 a ^ ε · C) · Σ_i |Y''_i|`.  The two
compose to exactly `c1 * a ^ ε`, which is where `hC : C ≠ 0` is used.

`hcover` is exactly the shape GWZ Step 3 produces ("sum over the dense tangential pieces and
discard the complement; a final dense-ball selection preserves a substantial fraction of the
shading mass"), and it is the only clause of the target that is not soft.  Nothing here uses
`Kakeya.IsTypicalPlankAngle`, `Kakeya.IsEssentiallyDistinct` or `Plank.IsWindowedFamily`. -/
theorem reduction_atTypicalAngle_of_denseRegion
    {ι : Type*} {η ε : ℝ}
    (s : Finset ι) (Y : ι → ShadedPlank a b hab hb1)
    (Y'' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (θ c1 C ρ : ℝ≥0) (hC : C ≠ 0)
    (hcar : 0 < ∑ i ∈ s, volume (ShadedPlank.bodies Y i).carrier)
    (hY'' : ShadedBody.IsCRefinement s Y'' s (ShadedPlank.bodies Y) C⁻¹)
    (hmult : ShadedBody.HasCConstantMultiplicity s Y'' C)
    (G : Set (EuclideanSpace ℝ (Fin 3))) (hGmeas : MeasurableSet G)
    (hscale : (c1 * a ^ ε) * C * C ≤ ρ)
    (hdense : (ρ : ENNReal) * volume (⋃ i ∈ s, (Y'' i).shade)
      ≤ volume ((⋃ i ∈ s, (Y'' i).shade) ∩ G))
    (hcover : ∀ y ∈ (⋃ i ∈ s, (Y'' i).shade) ∩ G,
      ∃ z : EuclideanSpace ℝ (Fin 3), y ∈ closedBall z ((θ * b : ℝ≥0) : ℝ) ∧
        ((c1 * a ^ (4 * η) * a ^ ε : ℝ≥0) : ENNReal)
            * volume (closedBall z ((θ * b : ℝ≥0) : ℝ))
          ≤ volume (((⋃ i ∈ s, (Y'' i).shade) ∩ G) ∩ closedBall z ((θ * b : ℝ≥0) : ℝ))) :
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
  · exact (ShadedBody.isRefinement_restrictShade s Y'' G hGmeas).trans hY''.1
  · exact ShadedBody.isRefinement_restrictShade s Y'' G hGmeas
  · -- fullness retention
    have hCr : ShadedBody.IsCRefinement s
        (fun i => ShadedBody.restrictShade (Y'' i) G hGmeas) s Y'' ((c1 * a ^ ε) * C) :=
      Plank.isCRefinement_restrictShade_of_dense s Y'' hmult hGmeas hdense hscale
    have hcomp := hCr.trans hY''
    have hcoeff : C⁻¹ * ((c1 * a ^ ε) * C) = c1 * a ^ ε := by
      field_simp
    rw [hcoeff] at hcomp
    exact ShadedBody.IsCRefinement.mul_fullness_le _ _ _ _ hcar hcomp
  · -- Item 1 at an arbitrary centre
    intro x hmeet
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

/-- **The dense-region reduction.**

A finite `θb`-ball cover of `U(s, Y'')` whose sparse part is small produces *every* non-formal
clause of `ShadedPlank.reduction_to_slab_atTypicalAngle`, on the unchanged index set `s`, with
`Y' i = (Y'' i).restrictShade G` for the dense region `G` of
`ShadedPlank.exists_denseRegion_of_ballCover`.

The two ledger hypotheses are separate on purpose.

* `hscale : (c1 * a ^ ε) * C * C ≤ ρ` is the refinement ledger.  `C⁻¹` is the coefficient of the
  incoming refinement `hY''` and the second `C` is the price
  `Plank.isCRefinement_restrictShade_of_dense` charges for turning the union capture
  `ρ|U| ≤ |U ∩ G|` into the mass capture `Σ_i |Y''_i ∩ G| ≥ (c1 a ^ ε · C) Σ_i |Y''_i|`.  The two
  compose to exactly `c1 * a ^ ε` (this is where `hC : C ≠ 0` is used).
* `hdiscard` is the geometric obligation: the balls of the cover, weighted by the Item-1 density
  `c1 a ^ (4η) a ^ ε`, together with the discarded fraction `ρ`, must fit inside `|U(s, Y'')|`.

Nothing here uses `Kakeya.IsTypicalPlankAngle`, `Kakeya.IsEssentiallyDistinct` or
`Plank.IsWindowedFamily`: those are what a *producer* of the cover needs. -/
theorem reduction_atTypicalAngle_of_denseBallCover
    {ι : Type*} {η ε : ℝ}
    (s : Finset ι) (Y : ι → ShadedPlank a b hab hb1)
    (Y'' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (θ c1 C ρ : ℝ≥0) (hC : C ≠ 0)
    (hcar : 0 < ∑ i ∈ s, volume (ShadedPlank.bodies Y i).carrier)
    (hY'' : ShadedBody.IsCRefinement s Y'' s (ShadedPlank.bodies Y) C⁻¹)
    (hmult : ShadedBody.HasCConstantMultiplicity s Y'' C)
    (T : Finset (EuclideanSpace ℝ (Fin 3)))
    (hcov : (⋃ i ∈ s, (Y'' i).shade) ⊆ ⋃ z ∈ T, closedBall z ((θ * b : ℝ≥0) : ℝ))
    (hscale : (c1 * a ^ ε) * C * C ≤ ρ)
    (hdiscard : ((c1 * a ^ (4 * η) * a ^ ε : ℝ≥0) : ENNReal)
          * (∑ z ∈ T, volume (closedBall z ((θ * b : ℝ≥0) : ℝ)))
        + (ρ : ENNReal) * volume (⋃ i ∈ s, (Y'' i).shade)
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
  have hUtop : volume (⋃ i ∈ s, (Y'' i).shade) ≠ ⊤ :=
    ShadedBody.volume_iUnion_shade_ne_top s Y''
  obtain ⟨G, hGmeas, hdense, hcover⟩ :=
    exists_denseRegion_of_ballCover (⋃ i ∈ s, (Y'' i).shade) hUtop ((θ * b : ℝ≥0) : ℝ) T hcov
      (c1 * a ^ (4 * η) * a ^ ε) ρ hdiscard
  exact reduction_atTypicalAngle_of_denseRegion (η := η) (ε := ε) s Y Y'' θ c1 C ρ hC hcar
    hY'' hmult G hGmeas hscale hdense hcover

/-- **`ShadedPlank.reduction_to_slab_atTypicalAngle` modulo one average-density obligation.**

This is the target statement of `Section6Compat.lean` verbatim — same binders, same hypotheses,
same conclusion, same `128 * ε ≤ ε'` — with exactly one hypothesis inserted just before the
conclusion, and it is proved.

The inserted hypothesis is that `U(s, Y'')` admits a finite `θb`-ball cover `T` with

```
δ ^ ε' · a ^ (4η) · a ^ ε · (∑ z ∈ T, |B̄(z, θb)|)
  + δ ^ (ε' - 2ε) · a ^ ε · |U(s, Y'')| ≤ |U(s, Y'')| .
```

Its second summand is a genuine but harmless loss: `δ ^ (ε' - 2ε) a ^ ε ≤ a ^ ε < 1` because
`128 * ε ≤ ε'` and `a < 1`.  Its first summand is Item 1 in average form and is the entire
remaining content.

Consequences worth recording.

1. **No smallness threshold on `δ` is needed** for the soft half: the witness is `δthr = 1`.
   Every threshold the target's docstring anticipated belongs to the obligation.
2. **The exponent hypothesis, now `128 * ε ≤ ε'`, is not weakened.**  (This note anticipated the
   repair that has since been made: the binder was raised from `2 * ε ≤ ε'` to `128 * ε ≤ ε'`
   exactly as prescribed below, against the Step-3 `C`-power traced in
   `Kakeya.DimensionThree.MainLemma2.Section6CompatBudget`.)  If a producer of the cover can only
   achieve the obligation with `δ ^ (kε)` in place of `δ ^ ε'` for some `k > 2`, the repair is
   visible and local: strengthen `128 * ε ≤ ε'` to `k * ε ≤ ε'` in this statement, not anywhere
   else.
3. The output family is `(s, Y''|_G)`: the index set is *not* pruned, so no cardinality is
   spent here. -/
theorem reduction_to_slab_atTypicalAngle_of_avgDensity :
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
      (∃ T : Finset (EuclideanSpace ℝ (Fin 3)),
        (⋃ i ∈ s, (Y'' i).shade) ⊆ ⋃ z ∈ T, closedBall z ((θ * b : ℝ≥0) : ℝ) ∧
        ((δ ^ ε' * a ^ (4 * η) * a ^ ε : ℝ≥0) : ENNReal)
            * (∑ z ∈ T, volume (closedBall z ((θ * b : ℝ≥0) : ℝ)))
          + ((δ ^ (ε' - 2 * ε) * a ^ ε : ℝ≥0) : ENNReal)
              * volume (⋃ i ∈ s, (Y'' i).shade)
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
  refine ⟨1, one_pos, le_rfl, ?_⟩
  intro ι s δ a b hab hb1 Y θ _hθ1 C Y'' hδ hδa ha1 _ _hwin hfull _hma _hmd _h2 _hcard
    _hθlb hC1 hCδ hYref hYmult _htyp hmaxA havg
  classical
  have ha : (0 : ℝ≥0) < a := lt_of_lt_of_le hδ hδa
  have hb : (0 : ℝ≥0) < b := lt_of_lt_of_le ha hab
  have hδne : (δ : ℝ≥0) ≠ 0 := hδ.ne'
  have hCne : (C : ℝ≥0) ≠ 0 := (lt_of_lt_of_le zero_lt_one hC1).ne'
  -- the index set is nonempty, because the fullness of the empty family is `0`
  have hsne : s.Nonempty := by
    rcases Finset.eq_empty_or_nonempty s with hs | hs
    · exfalso
      have hz : ShadedBody.fullness s (ShadedPlank.bodies Y) = 0 := by
        simp [hs]
      rw [hz] at hfull
      exact absurd (le_antisymm hfull zero_le) (NNReal.rpow_pos ha).ne'
    · exact hs
  have hcar : 0 < ∑ i ∈ s, volume (ShadedPlank.bodies Y i).carrier := by
    obtain ⟨i0, hi0⟩ := hsne
    have hpos : 0 < volume ((ShadedPlank.bodies Y i0).carrier :
        Set (EuclideanSpace ℝ (Fin 3))) := by
      rw [show ((ShadedPlank.bodies Y i0).carrier : Set (EuclideanSpace ℝ (Fin 3)))
        = (Y i0).carrier from rfl, ShadedPlank.volume_carrier (Y i0)]
      have : (0 : ENNReal) < 8 * (a : ENNReal) * (b : ENNReal) := by
        refine ENNReal.mul_pos (ENNReal.mul_pos (by norm_num) ?_).ne' ?_
        · exact (ENNReal.coe_pos.mpr ha).ne'
        · exact (ENNReal.coe_pos.mpr hb).ne'
      exact this
    exact lt_of_lt_of_le hpos (Finset.single_le_sum (f := fun i =>
      volume ((ShadedPlank.bodies Y i).carrier : Set (EuclideanSpace ℝ (Fin 3))))
      (fun i _ => zero_le) hi0)
  obtain ⟨T, hcov, hdisc⟩ := havg
  -- the exponent ledger: `(δ ^ ε' · a ^ ε) · C ² ≤ δ ^ (ε' - 2ε) · a ^ ε`
  have hscale : (δ ^ ε' * a ^ ε) * C * C ≤ δ ^ (ε' - 2 * ε) * a ^ ε := by
    have hCC : C * C ≤ δ ^ (-ε) * δ ^ (-ε) := mul_le_mul' hCδ hCδ
    calc (δ ^ ε' * a ^ ε) * C * C = (δ ^ ε' * a ^ ε) * (C * C) := by ring
      _ ≤ (δ ^ ε' * a ^ ε) * (δ ^ (-ε) * δ ^ (-ε)) := by gcongr
      _ = (δ ^ ε' * δ ^ (-ε) * δ ^ (-ε)) * a ^ ε := by ring
      _ = δ ^ (ε' - 2 * ε) * a ^ ε := by
          rw [← NNReal.rpow_add hδne, ← NNReal.rpow_add hδne]
          ring_nf
  obtain ⟨Y', href1, href2, hfullret, hitem1⟩ :=
    reduction_atTypicalAngle_of_denseBallCover (η := η) (ε := ε) s Y Y'' θ (δ ^ ε') C
      (δ ^ (ε' - 2 * ε) * a ^ ε) hCne hcar hYref hYmult T hcov hscale hdisc
  refine ⟨s, Y', δ ^ ε', NNReal.rpow_pos hδ, href1, href2, hfullret, ?_, ?_⟩
  · intro x hx
    have hco : ((δ ^ ε' * a ^ (4 * η) * a ^ ε : ℝ≥0) : ENNReal)
        = ((δ ^ ε' : ℝ≥0) : ENNReal) * (a : ENNReal) ^ (4 * η) * (a : ENNReal) ^ ε := by
      rw [ENNReal.coe_mul, ENNReal.coe_mul,
        ENNReal.coe_rpow_of_nonneg _ (by positivity : (0 : ℝ) ≤ 4 * η),
        ENNReal.coe_rpow_of_nonneg _ hε.le]
    rw [← hco]
    exact hitem1 x hx
  · rw [NNReal.rpow_neg]

/-- **`ShadedPlank.reduction_to_slab_atTypicalAngle` modulo the sharpest possible obligation.**

The target statement of `Section6Compat.lean` verbatim, with exactly one hypothesis inserted just
before the conclusion, and proved.  The inserted hypothesis is the *weakest* form of GWZ Step 3's
output: a measurable region `G` such that

* `G` retains a `δ ^ (ε' - 2ε) · a ^ ε` fraction of the shading union `U(s, Y'')`, and
* the retained union `U(s, Y'') ∩ G` fills a `θb`-ball around each of its points to density
  `δ ^ ε' · a ^ (4η) · a ^ ε`.

This is strictly weaker than the ball-cover obligation of
`ShadedPlank.reduction_to_slab_atTypicalAngle_of_avgDensity` (which produces such a `G` by
discarding the sparse balls of a cover), and it is *exactly* what GWZ's "sum over the dense
tangential pieces and discard the complement; a final dense-ball selection preserves a substantial
fraction of the shading mass" delivers.  Everything else in the target — both refinement clauses,
the fullness ledger, the dilation-`3` upgrade of the density to an arbitrary centre, the
`c1⁻¹ ≤ δ ^ (-ε')` clause, and the entire `δ`-scale exponent bookkeeping — is discharged here.

The retention exponent `δ ^ (ε' - 2ε) · a ^ ε` is forced and is where `128 * ε ≤ ε'` is spent, to the
extent of `2 * ε`: one
`δ ^ ε` for the incoming refinement coefficient `C⁻¹`, one for the constant-multiplicity constant
`C` that converts a union capture into a mass capture.  It is `< 1` — so the obligation is not
vacuous — precisely because `128 * ε ≤ ε'`, `δ ≤ 1` and `a < 1`. -/
theorem reduction_to_slab_atTypicalAngle_of_denseRegion :
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
      (∃ G : Set (EuclideanSpace ℝ (Fin 3)), MeasurableSet G ∧
        ((δ ^ (ε' - 2 * ε) * a ^ ε : ℝ≥0) : ENNReal)
              * volume (⋃ i ∈ s, (Y'' i).shade)
            ≤ volume ((⋃ i ∈ s, (Y'' i).shade) ∩ G) ∧
        ∀ y ∈ (⋃ i ∈ s, (Y'' i).shade) ∩ G,
          ∃ z : EuclideanSpace ℝ (Fin 3), y ∈ closedBall z ((θ * b : ℝ≥0) : ℝ) ∧
            ((δ ^ ε' * a ^ (4 * η) * a ^ ε : ℝ≥0) : ENNReal)
                * volume (closedBall z ((θ * b : ℝ≥0) : ℝ))
              ≤ volume (((⋃ i ∈ s, (Y'' i).shade) ∩ G)
                  ∩ closedBall z ((θ * b : ℝ≥0) : ℝ))) →
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
  refine ⟨1, one_pos, le_rfl, ?_⟩
  intro ι s δ a b hab hb1 Y θ _hθ1 C Y'' hδ hδa ha1 _ _hwin hfull _hma _hmd _h2 _hcard
    _hθlb hC1 hCδ hYref hYmult _htyp hmaxA havg
  classical
  have ha : (0 : ℝ≥0) < a := lt_of_lt_of_le hδ hδa
  have hb : (0 : ℝ≥0) < b := lt_of_lt_of_le ha hab
  have hδne : (δ : ℝ≥0) ≠ 0 := hδ.ne'
  have hCne : (C : ℝ≥0) ≠ 0 := (lt_of_lt_of_le zero_lt_one hC1).ne'
  -- the index set is nonempty, because the fullness of the empty family is `0`
  have hsne : s.Nonempty := by
    rcases Finset.eq_empty_or_nonempty s with hs | hs
    · exfalso
      have hz : ShadedBody.fullness s (ShadedPlank.bodies Y) = 0 := by
        simp [hs]
      rw [hz] at hfull
      exact absurd (le_antisymm hfull zero_le) (NNReal.rpow_pos ha).ne'
    · exact hs
  have hcar : 0 < ∑ i ∈ s, volume (ShadedPlank.bodies Y i).carrier := by
    obtain ⟨i0, hi0⟩ := hsne
    have hpos : 0 < volume ((ShadedPlank.bodies Y i0).carrier :
        Set (EuclideanSpace ℝ (Fin 3))) := by
      rw [show ((ShadedPlank.bodies Y i0).carrier : Set (EuclideanSpace ℝ (Fin 3)))
        = (Y i0).carrier from rfl, ShadedPlank.volume_carrier (Y i0)]
      have : (0 : ENNReal) < 8 * (a : ENNReal) * (b : ENNReal) := by
        refine ENNReal.mul_pos (ENNReal.mul_pos (by norm_num) ?_).ne' ?_
        · exact (ENNReal.coe_pos.mpr ha).ne'
        · exact (ENNReal.coe_pos.mpr hb).ne'
      exact this
    exact lt_of_lt_of_le hpos (Finset.single_le_sum (f := fun i =>
      volume ((ShadedPlank.bodies Y i).carrier : Set (EuclideanSpace ℝ (Fin 3))))
      (fun i _ => zero_le) hi0)
  obtain ⟨G, hGmeas, hdense, hcover⟩ := havg
  -- the exponent ledger: `(δ ^ ε' · a ^ ε) · C ² ≤ δ ^ (ε' - 2ε) · a ^ ε`
  have hscale : (δ ^ ε' * a ^ ε) * C * C ≤ δ ^ (ε' - 2 * ε) * a ^ ε := by
    have hCC : C * C ≤ δ ^ (-ε) * δ ^ (-ε) := mul_le_mul' hCδ hCδ
    calc (δ ^ ε' * a ^ ε) * C * C = (δ ^ ε' * a ^ ε) * (C * C) := by ring
      _ ≤ (δ ^ ε' * a ^ ε) * (δ ^ (-ε) * δ ^ (-ε)) := by gcongr
      _ = (δ ^ ε' * δ ^ (-ε) * δ ^ (-ε)) * a ^ ε := by ring
      _ = δ ^ (ε' - 2 * ε) * a ^ ε := by
          rw [← NNReal.rpow_add hδne, ← NNReal.rpow_add hδne]
          ring_nf
  obtain ⟨Y', href1, href2, hfullret, hitem1⟩ :=
    reduction_atTypicalAngle_of_denseRegion (η := η) (ε := ε) s Y Y'' θ (δ ^ ε') C
      (δ ^ (ε' - 2 * ε) * a ^ ε) hCne hcar hYref hYmult G hGmeas hscale hdense hcover
  refine ⟨s, Y', δ ^ ε', NNReal.rpow_pos hδ, href1, href2, hfullret, ?_, ?_⟩
  · intro x hx
    have hco : ((δ ^ ε' * a ^ (4 * η) * a ^ ε : ℝ≥0) : ENNReal)
        = ((δ ^ ε' : ℝ≥0) : ENNReal) * (a : ENNReal) ^ (4 * η) * (a : ENNReal) ^ ε := by
      rw [ENNReal.coe_mul, ENNReal.coe_mul,
        ENNReal.coe_rpow_of_nonneg _ (by positivity : (0 : ℝ) ≤ 4 * η),
        ENNReal.coe_rpow_of_nonneg _ hε.le]
    rw [← hco]
    exact hitem1 x hx
  · rw [NNReal.rpow_neg]


/-- **Drift tripwire: the dense-region obligation really does close
`ShadedPlank.reduction_to_slab_atTypicalAngle`.**

The hypothesis `H` is the target statement with its conclusion replaced by the obligation, and the
conclusion of this theorem is the target statement *verbatim* — copied from `Section6Compat.lean`,
with only `Type*` written as `Type u` so that the two occurrences share a universe.

The obligation is allowed its own `δ`-threshold, exactly as the target is; the two thresholds are
combined with `min`.

The check is d-sametype-check.lean` at the worktree root; it
elaborates

```
@ShadedPlank.reduction_to_slab_atTypicalAngle_of_obligation.{u} H η ε ε'
  = @ShadedPlank.reduction_to_slab_atTypicalAngle.{u} η ε ε'   := rfl
```

which type-checks only if the two statements coincide. -/
theorem reduction_to_slab_atTypicalAngle_of_obligation.{u}
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
    (∃ G : Set (EuclideanSpace ℝ (Fin 3)), MeasurableSet G ∧
        ((δ ^ (ε' - 2 * ε) * a ^ ε : ℝ≥0) : ENNReal)
              * volume (⋃ i ∈ s, (Y'' i).shade)
            ≤ volume ((⋃ i ∈ s, (Y'' i).shade) ∩ G) ∧
        ∀ y ∈ (⋃ i ∈ s, (Y'' i).shade) ∩ G,
          ∃ z : EuclideanSpace ℝ (Fin 3), y ∈ closedBall z ((θ * b : ℝ≥0) : ℝ) ∧
            ((δ ^ ε' * a ^ (4 * η) * a ^ ε : ℝ≥0) : ENNReal)
                * volume (closedBall z ((θ * b : ℝ≥0) : ℝ))
              ≤ volume (((⋃ i ∈ s, (Y'' i).shade) ∩ G)
                  ∩ closedBall z ((θ * b : ℝ≥0) : ℝ)))) :
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
    reduction_to_slab_atTypicalAngle_of_denseRegion hη hε hε' hgap Ccard D
  refine ⟨min δthr₁ δthr₂, lt_min hpos₁ hpos₂, (min_le_left _ _).trans hle₁, ?_⟩
  intro ι s δ a b hab hb1 Y θ hθ1 C Y'' hδ hδa ha1 hthr hwin hfull hma hmd h2 hcard
    hθlb hC1 hCδ hYref hYmult htyp hmaxA
  exact hmain s Y θ hθ1 C Y'' hδ hδa ha1 (hthr.trans (min_le_right _ _)) hwin hfull hma hmd
    h2 hcard hθlb hC1 hCδ hYref hYmult htyp hmaxA
    (hH s Y θ hθ1 C Y'' hδ hδa ha1 (hthr.trans (min_le_left _ _)) hwin hfull hma hmd
      h2 hcard hθlb hC1 hCδ hYref hYmult htyp hmaxA)


/-! ### Why a single ball cannot carry the reduction -/

/-- **The single-ball form of the mass clause forces the ball to be large.**

If the whole retained mass is to sit inside one ball `B̄(z, r)` — the hypothesis `hmass` of
`ShadedPlank.reduction_atTypicalAngle_of_denseBall` — then, since each
`|Y''_i ∩ B̄(z, r)| ≤ |B̄(z, r)|` and each plank carrier has volume exactly `8ab`, the retention
factor `κ` obeys `κ · λ(s, bodies Y) · 8ab ≤ |B̄(z, r)|`.  The cardinality `|s|` cancels: this is
a statement about a *single* plank's worth of mass. -/
theorem denseBall_mass_forces_ball_volume
    {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (Y : ι → ShadedPlank a b hab hb1)
    (Y'' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))) (κ r : ℝ≥0)
    (z : EuclideanSpace ℝ (Fin 3))
    (hmass : (κ : ENNReal) * (∑ i ∈ s, volume (ShadedPlank.bodies Y i).shade)
        ≤ ∑ i ∈ s, volume ((Y'' i).shade ∩ closedBall z (r : ℝ))) :
    (κ : ENNReal) * (ShadedBody.fullness s (ShadedPlank.bodies Y) : ENNReal)
        * (8 * (a : ENNReal) * (b : ENNReal))
      ≤ volume (closedBall z (r : ℝ)) := by
  classical
  have hcard0 : ((s.card : ENNReal)) ≠ 0 := by
    simpa using (Finset.card_ne_zero_of_mem hs.choose_spec)
  have hcardtop : ((s.card : ENNReal)) ≠ ⊤ := by simp
  -- the right-hand side is at most `|s| · |B|`
  have hRHS : (∑ i ∈ s, volume ((Y'' i).shade ∩ closedBall z (r : ℝ)))
      ≤ (s.card : ENNReal) * volume (closedBall z (r : ℝ)) := by
    calc (∑ i ∈ s, volume ((Y'' i).shade ∩ closedBall z (r : ℝ)))
        ≤ ∑ _i ∈ s, volume (closedBall z (r : ℝ)) :=
          Finset.sum_le_sum fun i _ => measure_mono Set.inter_subset_right
      _ = (s.card : ENNReal) * volume (closedBall z (r : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  -- the left-hand side is `κ · λ · |s| · 8ab`
  have hcarr : (∑ i ∈ s, volume ((ShadedPlank.bodies Y i).carrier :
      Set (EuclideanSpace ℝ (Fin 3))))
      = (s.card : ENNReal) * (8 * (a : ENNReal) * (b : ENNReal)) := by
    rw [Finset.sum_congr rfl (fun i _ => ShadedPlank.volume_carrier (Y i)),
      Finset.sum_const, nsmul_eq_mul]
  have hLHS : (∑ i ∈ s, volume (ShadedPlank.bodies Y i).shade)
      = (ShadedBody.fullness s (ShadedPlank.bodies Y) : ENNReal)
          * ((s.card : ENNReal) * (8 * (a : ENNReal) * (b : ENNReal))) := by
    rw [ShadedBody.sum_volumeReal_shade_eq_fullness_mul, hcarr]
  rw [hLHS] at hmass
  have hkey : (s.card : ENNReal) *
      ((κ : ENNReal) * (ShadedBody.fullness s (ShadedPlank.bodies Y) : ENNReal)
        * (8 * (a : ENNReal) * (b : ENNReal)))
      ≤ (s.card : ENNReal) * volume (closedBall z (r : ℝ)) := by
    refine le_trans (le_of_eq ?_) (hmass.trans hRHS)
    ring
  exact (ENNReal.mul_le_mul_iff_right hcard0 hcardtop).mp hkey

/-- **The single-ball obstruction in closed form**, `κ · λ · a · b ≤ r ³`.

`ShadedPlank.denseBall_mass_forces_ball_volume` with `|B̄(z, r)| ≤ 8 r ³`, which holds because
`MeasureTheory.Measure.addHaar_closedBall'` scales the unit ball and
`MeasureTheory.volume_closedBall_le_two_pow_finrank` bounds the unit ball of
`EuclideanSpace ℝ (Fin 3)` by `2 ³ = 8`.  The factor `8` cancels against the `8ab` of the plank
carrier, which is why the closed form has no constant at all. -/
theorem denseBall_mass_forces_cube_bound
    {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (Y : ι → ShadedPlank a b hab hb1)
    (Y'' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))) (κ r : ℝ≥0)
    (z : EuclideanSpace ℝ (Fin 3))
    (hmass : (κ : ENNReal) * (∑ i ∈ s, volume (ShadedPlank.bodies Y i).shade)
        ≤ ∑ i ∈ s, volume ((Y'' i).shade ∩ closedBall z (r : ℝ))) :
    (κ : ENNReal) * (ShadedBody.fullness s (ShadedPlank.bodies Y) : ENNReal)
        * (a : ENNReal) * (b : ENNReal)
      ≤ (r : ENNReal) ^ (3 : ℕ) := by
  have hball : volume (closedBall z (r : ℝ))
      ≤ ENNReal.ofReal ((r : ℝ) ^ (3 : ℕ)) * 8 := by
    have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by
      simp
    have h1 : volume (closedBall z (r : ℝ))
        = ENNReal.ofReal ((r : ℝ) ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))
          * volume (closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
      Measure.addHaar_closedBall' volume z r.coe_nonneg
    rw [h1, hfr]
    gcongr
    calc volume (closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)
        ≤ 2 ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) :=
          volume_closedBall_le_two_pow_finrank
      _ = 8 := by rw [hfr]; norm_num
  have hmain := denseBall_mass_forces_ball_volume s hs Y Y'' κ r z hmass
  have hofr : ENNReal.ofReal ((r : ℝ) ^ (3 : ℕ)) = (r : ENNReal) ^ (3 : ℕ) := by
    rw [ENNReal.ofReal_pow r.coe_nonneg, ENNReal.ofReal_coe_nnreal]
  have h8 : (κ : ENNReal) * (ShadedBody.fullness s (ShadedPlank.bodies Y) : ENNReal)
      * (8 * (a : ENNReal) * (b : ENNReal))
      = 8 * ((κ : ENNReal) * (ShadedBody.fullness s (ShadedPlank.bodies Y) : ENNReal)
        * (a : ENNReal) * (b : ENNReal)) := by ring
  rw [h8] at hmain
  have hchain : 8 * ((κ : ENNReal) * (ShadedBody.fullness s (ShadedPlank.bodies Y) : ENNReal)
      * (a : ENNReal) * (b : ENNReal)) ≤ 8 * ((r : ENNReal) ^ (3 : ℕ)) := by
    refine (hmain.trans hball).trans (le_of_eq ?_)
    rw [hofr]; ring
  exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).mp hchain

/-- **The single-ball necessary condition fails in the main regime.**

Instantiate `ShadedPlank.denseBall_mass_forces_cube_bound` at the parameters the target permits
and the consumer supplies: `δ = a` (allowed: the hypothesis is only `δ ≤ a`), `b = 1`,
`θ = a / b = a` (the smallest angle `a / b ≤ θ` allows, hence `r = θb = a`),
`λ(s, bodies Y) = a ^ η` (the smallest the hypothesis `a ^ η ≤ λ` allows) and
`κ = c1 · a ^ ε` with `c1 = δ ^ ε' = a ^ ε'` (the smallest `c1⁻¹ ≤ δ ^ (-ε')` allows).  The
necessary condition becomes `a ^ (ε' + ε + η + 1) ≤ a ^ 3`, and this lemma says it is false for
every `0 < a < 1` whenever `η + ε + ε' < 2` — which every intended instantiation satisfies
(the consumer runs at `ε' = η / 2` with `η` small).

So a one-ball output family cannot satisfy the fullness clause of the target, and the
`Section6CompatBall.lean` reduction, while sound, can only be applied in the regime
`(θb) ³ ≥ c1 a ^ ε λ a b`, i.e. essentially `δ ^ ε' ≤ a ^ (2 - η - ε)`. -/
theorem singleBall_necessary_condition_fails
    {η ε ε' : ℝ} (hsum : η + ε + ε' < 2) {a : ℝ≥0} (ha : 0 < a) (ha1 : a < 1) :
    a ^ (3 : ℝ) < a ^ ε' * a ^ ε * a ^ η * a := by
  have hane : (a : ℝ≥0) ≠ 0 := ha.ne'
  have hrw : a ^ (ε' + ε + η + 1) = a ^ ε' * a ^ ε * a ^ η * a := by
    rw [NNReal.rpow_add hane, NNReal.rpow_add hane, NNReal.rpow_add hane, NNReal.rpow_one]
  rw [← hrw]
  exact NNReal.rpow_lt_rpow_of_exponent_gt ha ha1 (by linarith)

end ShadedPlank

end
