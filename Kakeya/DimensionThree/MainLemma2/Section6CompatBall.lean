/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.Reduction
public import Kakeya.DimensionThree.Plank.LocalDensity

/-!
# The single-dense-ball reduction for `ShadedPlank.reduction_to_slab_atTypicalAngle`

`ShadedPlank.reduction_to_slab_atTypicalAngle` (`Section6Compat.lean`) is GWZ Lemma 6.13 read
through GWZ Remark 6.14 (`typicalAngleAlreadyPresent`), i.e. at an already prescribed typical
angle and with every loss read at the auxiliary scale `δ ≤ a`.  Its conclusion has three
quantitative clauses — the fullness retention, Item 1 at *every* centre, and `c1⁻¹ ≤ δ ^ (-ε')`.

This file records the *elementary* half of that conclusion: all three clauses follow from a
**single ball** `B̄(z, θb)` carrying two mass properties, namely

* it retains a `c1 · a ^ ε` fraction of the total shading mass, and
* the retained union fills it to density `c1 · a ^ (4η) · a ^ ε`.

The output family is then simply `(s, Y'' |_{B̄(z, θb)})`: no representative selection, no slab
assignment and no stopping time occur here.  Item 1 at an arbitrary centre comes from
`Plank.localDensity_of_denseBallCover`, whose dense-ball certificate is supplied by the constant
cover `c := z` — the retained union lies in `B̄(z, θb)`, and `B̄(z, θb) ⊆ B̄(x, 3 θb)` for every
`x` whose `θb`-ball meets it.

What is therefore *not* elementary, and is the entire remaining content of the target, is the
production of the ball `z`: it is a statement about the volume of `U(s, Y'')` and about how that
volume distributes over `θb`-balls, and it is where the typical angle, the constant multiplicity
and the essential distinctness of the planks must be used.
-/

@[expose] public section

open MeasureTheory Metric
open scoped NNReal Real ENNReal

noncomputable section

namespace ShadedPlank

variable {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}

/-- **One dense ball produces the whole conclusion of
`ShadedPlank.reduction_to_slab_atTypicalAngle`.**

Given a centre `z` such that the shades cut down to `B̄(z, θ b)` still carry a `c1 · a ^ ε`
fraction of the total shading mass (`hmass`) and such that the cut-down union fills that ball
to density `c1 · a ^ (4 η) · a ^ ε` (`hdense`), the family
`Y' i = (Y'' i).restrictShade B̄(z, θ b)` on the *unchanged* index set `s` satisfies every clause
of the target: it refines both `(s, bodies Y)` and `(s, Y'')`, it retains the fullness, and it
satisfies Item 1 at every centre with the fixed dilation
`ShadedPlank.redPlankTube.ballDilation = 3`.

The two hypotheses are exactly the two clauses of the target that are not formal, restated at a
single ball.  Nothing here uses `IsTypicalPlankAngle`, `HasCConstantMultiplicity`,
`IsEssentiallyDistinct` or `Plank.IsWindowedFamily`: those are what the *producer* of `z` needs. -/
theorem reduction_atTypicalAngle_of_denseBall
    {ι : Type*} {η ε : ℝ} (hη : 0 ≤ η) (hε : 0 ≤ ε)
    (s : Finset ι) (Y : ι → ShadedPlank a b hab hb1)
    (Y'' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (θ c1 : ℝ≥0)
    (hY'' : ShadedBody.IsRefinement s Y'' s (ShadedPlank.bodies Y))
    (z : EuclideanSpace ℝ (Fin 3))
    (hmass : ((c1 * a ^ ε : ℝ≥0) : ENNReal) * (∑ i ∈ s, volume (ShadedPlank.bodies Y i).shade)
        ≤ ∑ i ∈ s, volume ((Y'' i).shade ∩ closedBall z ((θ * b : ℝ≥0) : ℝ)))
    (hdense : (c1 : ENNReal) * (a : ENNReal) ^ (4 * η) * (a : ENNReal) ^ ε *
        volume (closedBall z ((θ * b : ℝ≥0) : ℝ))
        ≤ volume ((⋃ i ∈ s, (Y'' i).shade) ∩ closedBall z ((θ * b : ℝ≥0) : ℝ))) :
    ∃ (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))),
      ShadedBody.IsRefinement s Y' s (ShadedPlank.bodies Y) ∧
      ShadedBody.IsRefinement s Y' s Y'' ∧
      (c1 * a ^ ε) * ShadedBody.fullness s (ShadedPlank.bodies Y) ≤
        ShadedBody.fullness s Y' ∧
      (∀ x,
        ((⋃ i ∈ s, (Y' i).shade) ∩ Metric.closedBall x ((θ * b : ℝ))).Nonempty →
        (c1 : ENNReal) * (a : ENNReal) ^ (4 * η) * (a : ENNReal) ^ ε *
            volume (Metric.closedBall x ((θ * b : ℝ))) ≤
          volume ((⋃ i ∈ s, (Y' i).shade) ∩
            Metric.closedBall x (redPlankTube.ballDilation * θ * b))) := by
  classical
  set B : Set (EuclideanSpace ℝ (Fin 3)) := closedBall z ((θ * b : ℝ≥0) : ℝ) with hB
  have hBmeas : MeasurableSet B := measurableSet_closedBall
  refine ⟨fun i => (Y'' i).restrictShade B hBmeas, ?_, ?_, ?_, ?_⟩
  · -- refines `(s, bodies Y)`
    refine ⟨Finset.Subset.refl s, fun i hi => ⟨?_, ?_⟩⟩
    · exact (hY''.2 i hi).1
    · exact fun x hx => (hY''.2 i hi).2 hx.1
  · -- refines `(s, Y'')`
    exact ShadedBody.isRefinement_restrictShade s Y'' B hBmeas
  · -- fullness retention
    have hcar : ∀ i ∈ s,
        volume (((Y'' i).restrictShade B hBmeas).carrier :
            Set (EuclideanSpace ℝ (Fin 3)))
          = volume ((ShadedPlank.bodies Y i).carrier :
            Set (EuclideanSpace ℝ (Fin 3))) := by
      intro i hi
      have := (hY''.2 i hi).1
      simp only [ShadedBody.toConvexSpaceBody_restrictShade]
      rw [this]
    rw [← ENNReal.coe_le_coe, ENNReal.coe_mul, ShadedBody.fullness_def,
      ShadedBody.fullness_def]
    have hden : (∑ i ∈ s, volume (((Y'' i).restrictShade B hBmeas).carrier :
          Set (EuclideanSpace ℝ (Fin 3))))
        = ∑ i ∈ s, volume ((ShadedPlank.bodies Y i).carrier :
          Set (EuclideanSpace ℝ (Fin 3))) :=
      Finset.sum_congr rfl hcar
    rw [hden, div_eq_mul_inv, div_eq_mul_inv, ← mul_assoc]
    gcongr
    exact hmass
  · -- Item 1 at an arbitrary centre
    have hU : (⋃ i ∈ s, ((Y'' i).restrictShade B hBmeas).shade)
        = (⋃ i ∈ s, (Y'' i).shade) ∩ B :=
      Plank.biUnion_restrictShade_shade s Y'' B hBmeas
    set t : ℝ≥0 := c1 * a ^ (4 * η) * a ^ ε with ht
    have htcoe : ((t : ℝ≥0) : ENNReal)
        = (c1 : ENNReal) * (a : ENNReal) ^ (4 * η) * (a : ENNReal) ^ ε := by
      rw [ht, ENNReal.coe_mul, ENNReal.coe_mul,
        ENNReal.coe_rpow_of_nonneg _ (by positivity : (0 : ℝ) ≤ 4 * η),
        ENNReal.coe_rpow_of_nonneg _ hε]
    have hcover : ∀ y ∈ (⋃ i ∈ s, (Y'' i).shade) ∩ B,
        ∃ c : EuclideanSpace ℝ (Fin 3), y ∈ Plank.thetaBall θ b c ∧
          (t : ENNReal) * volume (Plank.thetaBall θ b c)
            ≤ volume (((⋃ i ∈ s, (Y'' i).shade) ∩ B) ∩ Plank.thetaBall θ b c) := by
      intro y hy
      refine ⟨z, hy.2, ?_⟩
      have hself : ((⋃ i ∈ s, (Y'' i).shade) ∩ B) ∩ Plank.thetaBall θ b z
          = (⋃ i ∈ s, (Y'' i).shade) ∩ B := by
        rw [Plank.thetaBall, ← hB, Set.inter_assoc, Set.inter_self]
      rw [hself, Plank.thetaBall, ← hB, htcoe]
      exact hdense
    intro x hmeet
    have hmeet' : (((⋃ i ∈ s, (Y'' i).shade) ∩ B) ∩
        Metric.closedBall x ((θ * b : ℝ≥0) : ℝ)).Nonempty := by
      rw [← hU]
      exact hmeet
    have hmain := Plank.localDensity_of_denseBallCover (theta := θ) (b := b)
      ((⋃ i ∈ s, (Y'' i).shade) ∩ B) t hcover x hmeet'
    rw [hU]
    rw [htcoe] at hmain
    refine le_trans hmain (measure_mono (Set.inter_subset_inter_right _ ?_))
    have hrad : ((Kakeya.plankReduction.ballDilation : ℝ) * ((θ * b : ℝ≥0) : ℝ))
        = ((redPlankTube.ballDilation : ℝ) * (θ : ℝ) * (b : ℝ)) := by
      simp [Kakeya.plankReduction.ballDilation, redPlankTube.ballDilation]
      ring
    rw [hrad]

end ShadedPlank

end
