/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Factoring.Step1
public import Kakeya.Factoring.Step4
public import Kakeya.Mathlib.MeasureTheory.Lintegral
public import Kakeya.Mathlib.Topology.CoveringNumber

/-! # Step 5 of the factoring construction

This file formalizes Step 5 of the construction in GWZ Proposition 5.1, the final
bounded-overlap ball refinement (blueprint `subsec:step5`).

Write `G₃ = step3FactorFamily F hu t' Ω hΩ k` for the Step 3 family, with inner index set
`u' = {i ∈ u | F.parent i ∈ t'}` and inner shading `Y₀'`, and `Y_{𝒲',0}` for the Step 4 outer
shading. Step 5 covers the Step 4 outer shaded union `S = U (𝒲', Y_{𝒲',0})` by boundedly
overlapping closed balls of radius `w₁`, selects a subfamily of that cover by a dyadic pigeonholing
over the balls, restricts the Step 3 shades to the union of the selected balls to produce the output
inner shading `Y'`, and re-runs Step 4 for `Y'` to produce the output outer shading `Y_{𝒲'}` and the
shaded factor family the construction returns.

The cover is not an obligation on the caller: `ShadedBody.exists_isStep5Cover` produces one with the
absolute overlap bound `Kakeya.factoringStep5OverlapConstant (finrank ℝ E) = 5 ^ n`. The one input
the caller must supply is the pair of bounds `a`, `b` for the ball masses, exactly as in Step 1.

All balls are closed, matching `ShadedBody.step2Nhd`. The upper bounds on ball masses are stated
with the *open* ball on the left, which is free, and with closed balls on the right, so that they
imply their open-ball form; `ShadedBody.volume_inter_closedBall_le_volume_inter_ball` bridges the
other direction.

## Main definitions and statements

* `ShadedBody.IsStep5Cover`: the ball cover data of Step 5;
* `ShadedBody.exists_isStep5Cover`: such a cover exists, with overlap bound `5 ^ n`;
* `ShadedBody.step5Selection`, `ShadedBody.step5InnerBody`, `ShadedBody.step5FactorFamily`: the
  selection set, the output inner shading `Y'`, and the family it bundles;
* `ShadedBody.exists_isCRefinement_step5FactorFamily`: the mass retained by Step 5, with the
  explicit constant `Kakeya.factoringStep5PigeonholeConstant`, together with the comparability of
  the ball masses across the selected balls;
* `ShadedBody.volume_iUnionShade_step5_inter_closedBall_le_two_mul` and
  `ShadedBody.volume_iUnionShade_step5_inter_ball_le_mul_volume_inter_closedBall`: ball
  comparability for the output shading, on the selected balls and at arbitrary points;
* `ShadedBody.step5OuterBody`, `ShadedBody.step5ShadedFactorFamily`: the re-induced outer shading
  and the shaded factor family produced by Step 5.
-/

@[expose] public section

open MeasureTheory Convexity Kakeya
open scoped NNReal ENNReal

namespace Kakeya

/-- **Constant in `Metric.IsSeparated.card_filter_mem_closedBall_le`** (blueprint
`def:step5OverlapConstant`): the bounded-overlap constant `5 ^ n` of a cover by the closed balls
around a separated set. It depends on the ambient dimension alone; not on the radius, the
configuration being invariant under rescaling. It is Besicovitch's bound and is not claimed to be
optimal. -/
def factoringStep5OverlapConstant (n : ℕ) : ℕ := 5 ^ n

/-- **Constant in `ShadedBody.exists_isCRefinement_step5FactorFamily`** (blueprint
`def:factoringStep5PigeonholeConstant`): `C(K, a, b) = K (1 + log₂ (b / a))₊`, the total Step 5
loss.

The factor `K` is the overlap bound of the cover, and it accounts for a point of the output shaded
union being counted up to `K` times in a sum over the balls. The factor
`factoringStep1FiberPigeonholeConstant a b` is the loss of the dyadic pigeonholing over the balls;
it is the Step 1 constant because it is the loss of the same lemma
`ENNReal.dyadic_pigeonhole₁''`, applied to different data. No positivity of `a` and no relation
between `a` and `b` is assumed. For the cover of `ShadedBody.exists_isStep5Cover` one has
`K = factoringStep5OverlapConstant (finrank ℝ E)`. -/
noncomputable def factoringStep5PigeonholeConstant (K : ℕ) (a b : ℝ≥0) : ℝ≥0 :=
  K * factoringStep1FiberPigeonholeConstant a b

/-- The Step 5 loss is at least the overlap bound of the cover, as soon as `a ≤ b`. This is what
keeps its reciprocal away from `0` once `K ≥ 1`. -/
theorem le_factoringStep5PigeonholeConstant (K : ℕ) {a b : ℝ≥0} (hab : a ≤ b) :
    (K : ℝ≥0) ≤ factoringStep5PigeonholeConstant K a b := by
  rw [factoringStep5PigeonholeConstant]
  exact le_mul_of_one_le_right zero_le (one_le_factoringStep1FiberPigeonholeConstant hab)

end Kakeya

namespace ShadedBody

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {ι κ : Type*} [DecidableEq κ]

/-! ### The ball cover of Step 5 -/

/-- The Step 4 outer shaded union `S = U (𝒲', Y_{𝒲',0})`, the set covered in Step 5 (blueprint
`def:step4OuterUnion`). -/
noncomputable def step4OuterUnion (F : FactorFamily E ι κ) {u : Finset ι}
    (hu : u ⊆ F.innerSet) (t' : Finset κ) (Ω : Set E) (hΩ : MeasurableSet Ω) (k : ℕ) : Set E :=
  iUnionShade t' (step4OuterBody F hu t' Ω hΩ k)

/-- The Step 4 outer shaded union is bounded (blueprint `lem:isBoundedStep4OuterUnion`), each
Step 4 outer shade lying in the compact carrier of its shaded body. -/
theorem isBounded_step4OuterUnion (F : FactorFamily E ι κ) {u : Finset ι}
    (hu : u ⊆ F.innerSet) (t' : Finset κ) (Ω : Set E) (hΩ : MeasurableSet Ω) (k : ℕ) :
    Bornology.IsBounded (step4OuterUnion F hu t' Ω hΩ k) := by
  rw [step4OuterUnion]
  exact isBounded_iUnionShade (s := t') (V := step4OuterBody F hu t' Ω hΩ k)

open Classical in
/-- **The ball cover data of Step 5** (blueprint `def:factoringStep5Cover`): a finite set `T` of
centres whose closed `w₁`-balls cover the Step 4 outer shaded union with pointwise overlap at
most `K`.

Only the covering clause is used in `ShadedBody.sum_volume_shade_step3_le_sum_step5BallMass` and
only the overlap clause in `ShadedBody.sum_step5BallMass_le_mul_sum_volume_shade_step5`. Such a
cover always exists, by `ShadedBody.exists_isStep5Cover`. -/
structure IsStep5Cover (F : FactorFamily E ι κ) {u : Finset ι} (hu : u ⊆ F.innerSet)
    (t' : Finset κ) (Ω : Set E) (hΩ : MeasurableSet Ω) (k : ℕ)
    (T : Finset E) (w₁ : ℝ≥0) (K : ℕ) : Prop where
  /-- The closed `w₁`-balls around `T` cover the Step 4 outer shaded union. -/
  cover : step4OuterUnion F hu t' Ω hΩ k ⊆ ⋃ c ∈ T, Metric.closedBall c (w₁ : ℝ)
  /-- No point lies in more than `K` of those balls. -/
  overlap : ∀ x : E, {c ∈ T | x ∈ Metric.closedBall c (w₁ : ℝ)}.card ≤ K

open Classical in
/-- **The ball cover of Step 5 exists** (blueprint `lem:step5BallCover`): for `w₁ > 0` there is a
finite `w₁`-separated set of centres inside the Step 4 outer shaded union which covers it with
overlap bound `Kakeya.factoringStep5OverlapConstant (finrank ℝ E) = 5 ^ n`.

So Step 5 leaves no cover obligation to its caller. The separation is recorded because
`ShadedBody.volume_iUnionShade_step5_inter_ball_le` needs it. -/
theorem exists_isStep5Cover (F : FactorFamily E ι κ) {u : Finset ι}
    (hu : u ⊆ F.innerSet) (t' : Finset κ) (Ω : Set E) (hΩ : MeasurableSet Ω) (k : ℕ)
    {w₁ : ℝ≥0} (hw₁ : 0 < w₁) :
    ∃ T : Finset E, (T : Set E) ⊆ step4OuterUnion F hu t' Ω hΩ k ∧
      Metric.IsSeparated (w₁ : ℝ≥0∞) (T : Set E) ∧
      IsStep5Cover F hu t' Ω hΩ k T w₁
        (Kakeya.factoringStep5OverlapConstant (Module.finrank ℝ E)) := by
  rcases Bornology.IsBounded.exists_finset_isSeparated_isCover_closedBall
    (hs := isBounded_step4OuterUnion F hu t' Ω hΩ k) (hw := hw₁) with
    ⟨T, hTsub, hTsep, hTcover, hToverlap⟩
  refine ⟨T, hTsub, hTsep, ?_⟩
  refine { cover := hTcover, overlap := fun x ↦ ?_ }
  simpa [Kakeya.factoringStep5OverlapConstant] using hToverlap x

/-! ### The output inner shading of Step 5 -/

/-- **The Step 5 selection set** (blueprint `def:step5Selection`): the union of the closed
`w₁`-balls around the selected centres `T'`. -/
def step5Selection (T' : Finset E) (w₁ : ℝ≥0) : Set E :=
  ⋃ c ∈ T', Metric.closedBall c (w₁ : ℝ)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The Step 5 selection set is closed, being a finite union of closed balls. The choice of closed
balls is what makes Step 5 preserve closedness of the inner shades; see
`ShadedBody.isClosed_shade_step5InnerBody`. -/
theorem isClosed_step5Selection (T' : Finset E) (w₁ : ℝ≥0) :
    IsClosed (step5Selection T' w₁) := by
  rw [step5Selection]
  exact isClosed_biUnion_finset (fun c hc => Metric.isClosed_closedBall)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The Step 5 selection set is measurable, being closed. -/
theorem measurableSet_step5Selection (T' : Finset E) (w₁ : ℝ≥0) :
    MeasurableSet (step5Selection T' w₁) := by
  exact (isClosed_step5Selection T' w₁).measurableSet

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem closedBall_subset_step5Selection {T' : Finset E} {c : E} (hc : c ∈ T') (w₁ : ℝ≥0) :
    Metric.closedBall c (w₁ : ℝ) ⊆ step5Selection T' w₁ := by
  rw [step5Selection]
  exact Set.subset_biUnion_of_mem (u := fun x => Metric.closedBall x (w₁ : ℝ)) hc

/-- **The output inner shaded body of Step 5** (blueprint `def:factoringStep5Family`):
`Y'(Vᵢ) = Y₀'(Vᵢ) ∩ A(T', w₁)`, the Step 3 shade restricted to the selection set.

The definition is stated for an arbitrary finite set of centres `T'`, exactly as Step 3 is stated
for an arbitrary measurable `Ω`: for `T' = ∅` every shade is empty and the family is still
legitimate. -/
noncomputable def step5InnerBody (F : FactorFamily E ι κ) (u : Finset ι)
    (t' : Finset κ) (Ω : Set E) (hΩ : MeasurableSet Ω) (k : ℕ) (T' : Finset E) (w₁ : ℝ≥0)
    (i : ι) : ShadedBody E :=
  (step3InnerBody F u t' Ω hΩ k i).restrictShade (step5Selection T' w₁)
    (measurableSet_step5Selection T' w₁)

omit [FiniteDimensional ℝ E] in
@[simp]
theorem toConvexSpaceBody_step5InnerBody (F : FactorFamily E ι κ) (u : Finset ι)
    (t' : Finset κ) (Ω : Set E) (hΩ : MeasurableSet Ω) (k : ℕ) (T' : Finset E) (w₁ : ℝ≥0)
    (i : ι) :
    (step5InnerBody F u t' Ω hΩ k T' w₁ i).toConvexSpaceBody =
      (F.innerBody i).toConvexSpaceBody := by
  rfl

omit [FiniteDimensional ℝ E] in
@[simp]
theorem shade_step5InnerBody (F : FactorFamily E ι κ) (u : Finset ι)
    (t' : Finset κ) (Ω : Set E) (hΩ : MeasurableSet Ω) (k : ℕ) (T' : Finset E) (w₁ : ℝ≥0)
    (i : ι) :
    (step5InnerBody F u t' Ω hΩ k T' w₁ i).shade =
      (step3InnerBody F u t' Ω hΩ k i).shade ∩ step5Selection T' w₁ := by
  rfl

omit [FiniteDimensional ℝ E] in
/-- **Step 5 preserves closedness of the inner shades**: the selection set is closed, so a closed
Step 3 shade stays closed.

Step 5 does not *establish* closedness: the Step 3 shade
`Y(Vᵢ) ∩ Ω ∩ step3DyadicSet...` need not be closed, both `Ω` and the dyadic set being only
measurable. So the hypothesis `hYclosed` of `ShadedBody.lambdaForInducedShading` reduces for the
Step 5 family exactly to the same hypothesis for the Step 3 family. -/
theorem isClosed_shade_step5InnerBody (F : FactorFamily E ι κ) (u : Finset ι)
    (t' : Finset κ) (Ω : Set E) (hΩ : MeasurableSet Ω) (k : ℕ) (T' : Finset E) (w₁ : ℝ≥0)
    {i : ι} (hY : IsClosed (step3InnerBody F u t' Ω hΩ k i).shade) :
    IsClosed (step5InnerBody F u t' Ω hΩ k T' w₁ i).shade := by
  exact isClosed_shade_restrictShade (measurableSet_step5Selection T' w₁) hY
    (isClosed_step5Selection T' w₁)

/-- The factor family produced by Step 5: the Step 3 family with its inner shades restricted to the
selection set (blueprint `def:factoringStep5Family`). -/
noncomputable def step5FactorFamily (F : FactorFamily E ι κ) {u : Finset ι}
    (hu : u ⊆ F.innerSet) (t' : Finset κ) (Ω : Set E) (hΩ : MeasurableSet Ω)
    (k : ℕ) (T' : Finset E) (w₁ : ℝ≥0) : FactorFamily E ι κ where
  innerSet := {i ∈ u | F.parent i ∈ t'}
  innerBody := step5InnerBody F u t' Ω hΩ k T' w₁
  outerSet := t'
  outerBody := F.outerBody
  parent := F.parent
  parent_mem := fun _ hi ↦ (Finset.mem_filter.mp hi).2
  inner_le_parent := fun i hi ↦ F.inner_le_parent i (hu (Finset.mem_filter.mp hi).1)

omit [FiniteDimensional ℝ E] in
@[simp]
theorem step5FactorFamily_innerSet (F : FactorFamily E ι κ) {u : Finset ι}
    (hu : u ⊆ F.innerSet) (t' : Finset κ) (Ω : Set E) (hΩ : MeasurableSet Ω) (k : ℕ)
    (T' : Finset E) (w₁ : ℝ≥0) :
    (step5FactorFamily F hu t' Ω hΩ k T' w₁).innerSet = {i ∈ u | F.parent i ∈ t'} := by
  rfl

omit [FiniteDimensional ℝ E] in
@[simp]
theorem step5FactorFamily_innerBody (F : FactorFamily E ι κ) {u : Finset ι}
    (hu : u ⊆ F.innerSet) (t' : Finset κ) (Ω : Set E) (hΩ : MeasurableSet Ω) (k : ℕ)
    (T' : Finset E) (w₁ : ℝ≥0) :
    (step5FactorFamily F hu t' Ω hΩ k T' w₁).innerBody =
      step5InnerBody F u t' Ω hΩ k T' w₁ := by
  rfl

omit [FiniteDimensional ℝ E] in
@[simp]
theorem step5FactorFamily_outerSet (F : FactorFamily E ι κ) {u : Finset ι}
    (hu : u ⊆ F.innerSet) (t' : Finset κ) (Ω : Set E) (hΩ : MeasurableSet Ω) (k : ℕ)
    (T' : Finset E) (w₁ : ℝ≥0) :
    (step5FactorFamily F hu t' Ω hΩ k T' w₁).outerSet = t' := by
  rfl

omit [FiniteDimensional ℝ E] in
@[simp]
theorem step5FactorFamily_parent (F : FactorFamily E ι κ) {u : Finset ι}
    (hu : u ⊆ F.innerSet) (t' : Finset κ) (Ω : Set E) (hΩ : MeasurableSet Ω) (k : ℕ)
    (T' : Finset E) (w₁ : ℝ≥0) :
    (step5FactorFamily F hu t' Ω hΩ k T' w₁).parent = F.parent := by
  rfl

omit [FiniteDimensional ℝ E] in
/-- **The fiber of the Step 5 family** (blueprint `lem:step5FactorFamilyFiber`): over a surviving
block it is the fiber of `F` inside `u`, exactly as for Step 3.

As for `ShadedBody.step3FactorFamily_fiber` this is not `rfl`: `FactorFamily.fiber` is defined with
`open Classical`. -/
theorem step5FactorFamily_fiber (F : FactorFamily E ι κ) {u : Finset ι}
    (hu : u ⊆ F.innerSet) (t' : Finset κ) (Ω : Set E) (hΩ : MeasurableSet Ω) (k : ℕ)
    (T' : Finset E) (w₁ : ℝ≥0) {j : κ} (hj : j ∈ t') :
    (step5FactorFamily F hu t' Ω hΩ k T' w₁).fiber j = {i ∈ u | F.parent i = j} := by
  classical
  rw [FactorFamily.fiber, step5FactorFamily_innerSet, step5FactorFamily_parent]
  ext i
  simp only [Finset.mem_filter]
  constructor
  · intro h
    exact ⟨h.1.1, h.2⟩
  · intro h
    exact ⟨⟨h.1, by simpa [h.2] using hj⟩, h.2⟩

omit [FiniteDimensional ℝ E] in
/-- **The Step 5 shaded union** (blueprint `lem:iUnionShadeStep5FactorFamily`):
`U (𝒱', Y') = U (𝒱', Y₀') ∩ A(T', w₁)`. -/
theorem iUnionShade_step5FactorFamily (F : FactorFamily E ι κ) (u : Finset ι)
    (t' : Finset κ) (Ω : Set E) (hΩ : MeasurableSet Ω) (k : ℕ) (T' : Finset E) (w₁ : ℝ≥0)
    (s : Finset ι) :
    iUnionShade s (step5InnerBody F u t' Ω hΩ k T' w₁) =
      iUnionShade s (step3InnerBody F u t' Ω hΩ k) ∩ step5Selection T' w₁ := by
  unfold step5InnerBody
  exact iUnionShade_restrictShade s (step3InnerBody F u t' Ω hΩ k) (step5Selection T' w₁)
    (measurableSet_step5Selection T' w₁)

omit [FiniteDimensional ℝ E] in
/-- **The Step 5 shading refines the Step 3 one** (blueprint `lem:factoringStep5Refinement`): the
structural half of item (5) of the construction. -/
theorem isRefinement_step5FactorFamily (F : FactorFamily E ι κ) (u : Finset ι)
    (t' : Finset κ) (Ω : Set E) (hΩ : MeasurableSet Ω) (k : ℕ) (T' : Finset E) (w₁ : ℝ≥0)
    (s : Finset ι) :
    IsRefinement s (step5InnerBody F u t' Ω hΩ k T' w₁) s (step3InnerBody F u t' Ω hΩ k) := by
  exact isRefinement_restrictShade (s := s) (V := step3InnerBody F u t' Ω hΩ k)
    (S := step5Selection T' w₁) (hS := measurableSet_step5Selection T' w₁)

/-! ### The two mass estimates and the selection -/

/-- The **ball mass** at a centre `c` (blueprint `def:step5BallMass`): the Step 3 shading mass
inside the closed `w₁`-ball at `c`, counted with multiplicity. This is the weight of the dyadic
pigeonholing of Step 5. -/
noncomputable def step5BallMass (F : FactorFamily E ι κ) (u : Finset ι)
    (t' : Finset κ) (Ω : Set E) (hΩ : MeasurableSet Ω) (k : ℕ) (w₁ : ℝ≥0) (c : E) : ℝ≥0∞ :=
  ∑ i ∈ {i ∈ u | F.parent i ∈ t'},
    volume ((step3InnerBody F u t' Ω hΩ k i).shade ∩ Metric.closedBall c (w₁ : ℝ))

open Classical in
/-- The **heavy centres** of a finite set of centres (blueprint `def:step5BallMass`): those whose
ball meets the Step 3 shaded union in a set of positive measure. Unlike the ball mass, this counts
the union without multiplicity; it is the quantity the pigeonholing classifies that is positive
on these centres. -/
noncomputable def step5PositiveBalls (F : FactorFamily E ι κ) (u : Finset ι)
    (t' : Finset κ) (Ω : Set E) (hΩ : MeasurableSet Ω) (k : ℕ) (T : Finset E) (w₁ : ℝ≥0) :
    Finset E :=
  {c ∈ T | volume (iUnionShade {i ∈ u | F.parent i ∈ t'} (step3InnerBody F u t' Ω hΩ k) ∩
    Metric.closedBall c (w₁ : ℝ)) ≠ 0}

/-- **The light balls carry no mass** (blueprint `lem:sumStep5BallMassPositive`): summing the ball
mass over the heavy centres is summing it over all of them. -/
theorem sum_step5BallMass_positiveBalls (F : FactorFamily E ι κ) (u : Finset ι)
    (t' : Finset κ) (Ω : Set E) (hΩ : MeasurableSet Ω) (k : ℕ) (T : Finset E) (w₁ : ℝ≥0) :
    ∑ c ∈ T, step5BallMass F u t' Ω hΩ k w₁ c =
      ∑ c ∈ step5PositiveBalls F u t' Ω hΩ k T w₁, step5BallMass F u t' Ω hΩ k w₁ c := by
  classical
  symm
  refine Finset.sum_subset (Finset.filter_subset _ _) ?_
  intro c hcT hcpos
  rw [step5PositiveBalls] at hcpos
  have hvol : volume (iUnionShade {i ∈ u | F.parent i ∈ t'} (step3InnerBody F u t' Ω hΩ k) ∩
        Metric.closedBall c (w₁ : ℝ)) = 0 := by
    by_contra h
    exact hcpos (Finset.mem_filter.mpr ⟨hcT, h⟩)
  unfold step5BallMass
  refine Finset.sum_eq_zero ?_
  intro i hi
  exact measure_mono_null
    (Set.inter_subset_inter_left (Metric.closedBall c (w₁ : ℝ))
      (Set.subset_iUnion₂
        (s := fun j (_ : j ∈ {i ∈ u | F.parent i ∈ t'}) =>
          (step3InnerBody F u t' Ω hΩ k j).shade) i hi)) hvol

/-- **The cover controls the Step 3 mass from above** (blueprint `lem:factoringStep5CoverMass`).
Only the covering clause of `ShadedBody.IsStep5Cover` is used. -/
theorem sum_volume_shade_step3_le_sum_step5BallMass (F : FactorFamily E ι κ) {u : Finset ι}
    (hu : u ⊆ F.innerSet) (t' : Finset κ) (Ω : Set E) (hΩ : MeasurableSet Ω) (k : ℕ)
    {T : Finset E} {w₁ : ℝ≥0} {K : ℕ} (hT : IsStep5Cover F hu t' Ω hΩ k T w₁ K) :
    ∑ i ∈ {i ∈ u | F.parent i ∈ t'}, volume ((step3InnerBody F u t' Ω hΩ k i).shade) ≤
      ∑ c ∈ step5PositiveBalls F u t' Ω hΩ k T w₁, step5BallMass F u t' Ω hΩ k w₁ c := by
  classical
  let u' : Finset ι := {i ∈ u | F.parent i ∈ t'}
  have hshade_sub : ∀ i ∈ u', (step3InnerBody F u t' Ω hΩ k i).shade ⊆
      ⋃ c ∈ T, Metric.closedBall c (w₁ : ℝ) := by
    intro i hi
    calc
      (step3InnerBody F u t' Ω hΩ k i).shade
          ⊆ iUnionShade u' (step3InnerBody F u t' Ω hΩ k) := by
            exact Set.subset_iUnion₂_of_subset i hi (Set.Subset.refl _)
      _ = iUnionShade (step3FactorFamily F hu t' Ω hΩ k).innerSet
            (step3FactorFamily F hu t' Ω hΩ k).innerBody := by
            simp [u']
      _ ⊆ iUnionShade t' (step4OuterBody F hu t' Ω hΩ k) :=
            iUnionShade_subset_iUnionShade_step4Outer F hu t' Ω hΩ k
      _ = step4OuterUnion F hu t' Ω hΩ k := by rw [step4OuterUnion]
      _ ⊆ ⋃ c ∈ T, Metric.closedBall c (w₁ : ℝ) := hT.cover
  calc
    ∑ i ∈ u', volume ((step3InnerBody F u t' Ω hΩ k i).shade)
        ≤ ∑ i ∈ u', ∑ c ∈ T,
            volume ((step3InnerBody F u t' Ω hΩ k i).shade ∩ Metric.closedBall c (w₁ : ℝ)) := by
          exact Finset.sum_le_sum (fun i hi =>
            MeasureTheory.measure_le_sum_measure_inter_of_subset_biUnion volume T
              (fun c => Metric.closedBall c (w₁ : ℝ)) (hshade_sub i hi))
    _ = ∑ c ∈ T, ∑ i ∈ u',
            volume ((step3InnerBody F u t' Ω hΩ k i).shade ∩ Metric.closedBall c (w₁ : ℝ)) := by
          rw [Finset.sum_comm]
    _ = ∑ c ∈ T, step5BallMass F u t' Ω hΩ k w₁ c := by
          simp [u', step5BallMass]
    _ = ∑ c ∈ step5PositiveBalls F u t' Ω hΩ k T w₁, step5BallMass F u t' Ω hΩ k w₁ c := by
          rw [sum_step5BallMass_positiveBalls F u t' Ω hΩ k T w₁]

/-- **Bounded overlap converts a sum over the cover into a mass** (blueprint
`lem:factoringStep5OverlapMass`). Only the overlap clause of `ShadedBody.IsStep5Cover` is used, and
no hypothesis relating `T'` to the bodies is needed beyond `T' ⊆ T`. -/
theorem sum_step5BallMass_le_mul_sum_volume_shade_step5 (F : FactorFamily E ι κ) {u : Finset ι}
    (hu : u ⊆ F.innerSet) (t' : Finset κ) (Ω : Set E) (hΩ : MeasurableSet Ω) (k : ℕ)
    {T T' : Finset E} {w₁ : ℝ≥0} {K : ℕ} (hT : IsStep5Cover F hu t' Ω hΩ k T w₁ K)
    (hT' : T' ⊆ T) :
    ∑ c ∈ T', step5BallMass F u t' Ω hΩ k w₁ c ≤
      (K : ℝ≥0∞) * ∑ i ∈ {i ∈ u | F.parent i ∈ t'},
        volume ((step5InnerBody F u t' Ω hΩ k T' w₁ i).shade) := by
  simp only [step5BallMass]
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro i hi
  rw [shade_step5InnerBody]
  exact MeasureTheory.sum_measure_inter_le_mul_measure_inter_biUnion
    (μ := volume) hT' (B := fun c => Metric.closedBall c (w₁ : ℝ))
    (hB := fun _ => Metric.isClosed_closedBall.measurableSet)
    (A := (step3InnerBody F u t' Ω hΩ k i).shade)
    (hA := (step3InnerBody F u t' Ω hΩ k i).measurableSet_shade)
    (hK := hT.overlap)

/-- **Ball pigeonholing: the selection of Step 5** (blueprint `lem:factoringStep5Pigeonhole`).

Given a `K`-bounded-overlap cover `T` and bounds `a ≤ |U (𝒱', Y₀') ∩ closedBall c w₁| ≤ b` with
`0 < a` on the heavy centres, a subset `T'` of the heavy centres can be selected so that the
restricted shading `Y'` is a `(factoringStep5PigeonholeConstant K a b)⁻¹` refinement of the Step 3
shading and the ball masses of the selected balls agree up to a factor `2`.

The hypothesis `hballs` is a genuine input, exactly as `hA` is for
`ShadedBody.FactorFamily.step1'`: a centre of the cover lies in the Step 4 outer shaded union,
hence only within `2 r_j` of the Step 3 shaded union, so its ball can meet that union in a null
set, and without a positive lower bound on the nonzero values the number of dyadic classes is not
bounded by any function of the data. It is restricted to the heavy centres, on which such a bound
can hold. -/
theorem exists_isCRefinement_step5FactorFamily (F : FactorFamily E ι κ) {u : Finset ι}
    (hu : u ⊆ F.innerSet) (t' : Finset κ) (Ω : Set E) (hΩ : MeasurableSet Ω) (k : ℕ)
    {T : Finset E} {w₁ : ℝ≥0} {K : ℕ} (hT : IsStep5Cover F hu t' Ω hΩ k T w₁ K)
    {a b : ℝ≥0} (ha : 0 < a)
    (hballs : ∀ c ∈ step5PositiveBalls F u t' Ω hΩ k T w₁,
      volume (iUnionShade {i ∈ u | F.parent i ∈ t'} (step3InnerBody F u t' Ω hΩ k) ∩
          Metric.closedBall c (w₁ : ℝ)) ∈ Set.Icc (a : ℝ≥0∞) (b : ℝ≥0∞)) :
    ∃ T' ⊆ step5PositiveBalls F u t' Ω hΩ k T w₁,
      IsCRefinement {i ∈ u | F.parent i ∈ t'} (step5InnerBody F u t' Ω hΩ k T' w₁)
          {i ∈ u | F.parent i ∈ t'} (step3InnerBody F u t' Ω hΩ k)
          (Kakeya.factoringStep5PigeonholeConstant K a b)⁻¹ ∧
        ∀ c ∈ T', ∀ c' ∈ T',
          volume (iUnionShade {i ∈ u | F.parent i ∈ t'} (step3InnerBody F u t' Ω hΩ k) ∩
              Metric.closedBall c (w₁ : ℝ)) ≤
            2 * volume (iUnionShade {i ∈ u | F.parent i ∈ t'}
              (step3InnerBody F u t' Ω hΩ k) ∩ Metric.closedBall c' (w₁ : ℝ)) := by
  classical
  -- Apply the dyadic pigeonhole lemma over the heavy centres with ball-mass weights and the
  -- classified quantity `f(c) = |U (𝒱', Y₀') ∩ closedBall c w₁|`.
  obtain ⟨T', hT'sub, htotal, hcomp⟩ :=
    ENNReal.dyadic_pigeonhole₁'' (s := step5PositiveBalls F u t' Ω hΩ k T w₁)
      (w := step5BallMass F u t' Ω hΩ k w₁)
      (f := fun c => volume (iUnionShade {i ∈ u | F.parent i ∈ t'}
        (step3InnerBody F u t' Ω hΩ k) ∩ Metric.closedBall c (w₁ : ℝ)))
      ha hballs
  -- `T' ⊆ step5PositiveBalls ⊆ T`.
  have hT'step : T' ⊆ T := hT'sub.trans (by
    rw [step5PositiveBalls]
    exact Finset.filter_subset _ _)
  -- Step 3 shade mass is bounded by the ball mass (the covering clause of `IsStep5Cover`).
  have hshade3leballs :
      ∑ i ∈ {i ∈ u | F.parent i ∈ t'}, volume ((step3InnerBody F u t' Ω hΩ k i).shade)
        ≤ ∑ c ∈ step5PositiveBalls F u t' Ω hΩ k T w₁,
            step5BallMass F u t' Ω hΩ k w₁ c :=
    sum_volume_shade_step3_le_sum_step5BallMass F hu t' Ω hΩ k hT
  -- Pigeonhole: the ball mass over the heavy centres is comparable to that over `T'`.
  have hballsleC1 :
      ∑ c ∈ step5PositiveBalls F u t' Ω hΩ k T w₁,
          step5BallMass F u t' Ω hΩ k w₁ c
        ≤ (factoringStep1FiberPigeonholeConstant a b : ℝ≥0∞) *
            ∑ c ∈ T', step5BallMass F u t' Ω hΩ k w₁ c := by
    simpa [coe_factoringStep1FiberPigeonholeConstant] using htotal
  -- Bounded overlap: ball mass over `T'` is `K` times the Step 5 shade mass.
  have hT'leK :
      ∑ c ∈ T', step5BallMass F u t' Ω hΩ k w₁ c
        ≤ (K : ℝ≥0∞) * ∑ i ∈ {i ∈ u | F.parent i ∈ t'},
            volume ((step5InnerBody F u t' Ω hΩ k T' w₁ i).shade) :=
    sum_step5BallMass_le_mul_sum_volume_shade_step5 F hu t' Ω hΩ k hT hT'step
  -- The factorization of the Step 5 constant.
  have hC5 : (Kakeya.factoringStep5PigeonholeConstant K a b : ℝ≥0∞) =
      (K : ℝ≥0∞) * (factoringStep1FiberPigeonholeConstant a b : ℝ≥0∞) := by
    rw [Kakeya.factoringStep5PigeonholeConstant]
    exact (ENNReal.coe_mul (x := (K : ℝ≥0)) (y := factoringStep1FiberPigeonholeConstant a b)).symm
  -- Chain the two mass estimates around the pigeonhole to get the refinement-mass inequality.
  have hshade3leC :
      ∑ i ∈ {i ∈ u | F.parent i ∈ t'}, volume ((step3InnerBody F u t' Ω hΩ k i).shade)
        ≤ (Kakeya.factoringStep5PigeonholeConstant K a b : ℝ≥0∞) *
            ∑ i ∈ {i ∈ u | F.parent i ∈ t'},
              volume ((step5InnerBody F u t' Ω hΩ k T' w₁ i).shade) := by
    calc
      ∑ i ∈ {i ∈ u | F.parent i ∈ t'}, volume ((step3InnerBody F u t' Ω hΩ k i).shade)
      _ ≤ ∑ c ∈ step5PositiveBalls F u t' Ω hΩ k T w₁,
            step5BallMass F u t' Ω hΩ k w₁ c := hshade3leballs
      _ ≤ (factoringStep1FiberPigeonholeConstant a b : ℝ≥0∞) *
            ∑ c ∈ T', step5BallMass F u t' Ω hΩ k w₁ c := hballsleC1
      _ ≤ (Kakeya.factoringStep5PigeonholeConstant K a b : ℝ≥0∞) *
            ∑ i ∈ {i ∈ u | F.parent i ∈ t'},
              volume ((step5InnerBody F u t' Ω hΩ k T' w₁ i).shade) := by
        calc
          (factoringStep1FiberPigeonholeConstant a b : ℝ≥0∞) *
              ∑ c ∈ T', step5BallMass F u t' Ω hΩ k w₁ c
          _ ≤ (factoringStep1FiberPigeonholeConstant a b : ℝ≥0∞) *
                ((K : ℝ≥0∞) * ∑ i ∈ {i ∈ u | F.parent i ∈ t'},
                  volume ((step5InnerBody F u t' Ω hΩ k T' w₁ i).shade)) := by
            gcongr
          _ = (Kakeya.factoringStep5PigeonholeConstant K a b : ℝ≥0∞) *
                ∑ i ∈ {i ∈ u | F.parent i ∈ t'},
                  volume ((step5InnerBody F u t' Ω hΩ k T' w₁ i).shade) := by
            calc
              (factoringStep1FiberPigeonholeConstant a b : ℝ≥0∞) *
                  ((K : ℝ≥0∞) * ∑ i ∈ {i ∈ u | F.parent i ∈ t'},
                    volume ((step5InnerBody F u t' Ω hΩ k T' w₁ i).shade))
              = ((K : ℝ≥0∞) * (factoringStep1FiberPigeonholeConstant a b : ℝ≥0∞)) *
                  ∑ i ∈ {i ∈ u | F.parent i ∈ t'},
                    volume ((step5InnerBody F u t' Ω hΩ k T' w₁ i).shade) := by
                ac_rfl
              _ = (Kakeya.factoringStep5PigeonholeConstant K a b : ℝ≥0∞) *
                  ∑ i ∈ {i ∈ u | F.parent i ∈ t'},
                    volume ((step5InnerBody F u t' Ω hΩ k T' w₁ i).shade) := by
                rw [← hC5]
  -- Item (i): assemble the refinement-mass inequality into a C-refinement.
  have h_refinement : IsCRefinement {i ∈ u | F.parent i ∈ t'}
      (step5InnerBody F u t' Ω hΩ k T' w₁) {i ∈ u | F.parent i ∈ t'}
      (step3InnerBody F u t' Ω hΩ k) (Kakeya.factoringStep5PigeonholeConstant K a b)⁻¹ := by
    refine isCRefinement_of_isRefinement_of_sum_le
      (s' := {i ∈ u | F.parent i ∈ t'}) (V' := step5InnerBody F u t' Ω hΩ k T' w₁)
      (s := {i ∈ u | F.parent i ∈ t'}) (V := step3InnerBody F u t' Ω hΩ k)
      (C := Kakeya.factoringStep5PigeonholeConstant K a b) ?_ hshade3leC
    exact isRefinement_step5FactorFamily F u t' Ω hΩ k T' w₁ {i ∈ u | F.parent i ∈ t'}
  exact ⟨T', hT'sub, h_refinement, hcomp⟩

/-! ### Ball comparability for the output shading -/

omit [FiniteDimensional ℝ E] in
/-- **The Step 5 shaded union inside a selected ball** (blueprint
`lem:factoringStep5BallIdentity`): on a selected ball the output shaded union and the Step 3 one
agree.

The hypothesis `c ∈ T'` is essential: for `T' = ∅` the left-hand side is empty while the right-hand
side need not be. -/
theorem iUnionShade_step5FactorFamily_inter_closedBall (F : FactorFamily E ι κ) (u : Finset ι)
    (t' : Finset κ) (Ω : Set E) (hΩ : MeasurableSet Ω) (k : ℕ) {T' : Finset E} {w₁ : ℝ≥0}
    (s : Finset ι) {c : E} (hc : c ∈ T') :
    iUnionShade s (step5InnerBody F u t' Ω hΩ k T' w₁) ∩ Metric.closedBall c (w₁ : ℝ) =
      iUnionShade s (step3InnerBody F u t' Ω hΩ k) ∩ Metric.closedBall c (w₁ : ℝ) := by
  rw [iUnionShade_step5FactorFamily F u t' Ω hΩ k T' w₁ s]
  rw [Set.inter_assoc, Set.inter_eq_self_of_subset_right (closedBall_subset_step5Selection hc w₁)]

/-- **Comparable output mass on the selected balls** (blueprint
`cor:factoringStep5AvgMultOnBalls`): the conclusion Step 5 exists to produce, stated for the output
shading `Y'` rather than for `Y₀'`. This is the dyadic reading of "roughly the same", with the
sharp constant `2`. -/
theorem volume_iUnionShade_step5_inter_closedBall_le_two_mul (F : FactorFamily E ι κ)
    (u : Finset ι) (t' : Finset κ) (Ω : Set E) (hΩ : MeasurableSet Ω) (k : ℕ)
    {T' : Finset E} {w₁ : ℝ≥0}
    (hcomp : ∀ c ∈ T', ∀ c' ∈ T',
      volume (iUnionShade {i ∈ u | F.parent i ∈ t'} (step3InnerBody F u t' Ω hΩ k) ∩
          Metric.closedBall c (w₁ : ℝ)) ≤
        2 * volume (iUnionShade {i ∈ u | F.parent i ∈ t'}
          (step3InnerBody F u t' Ω hΩ k) ∩ Metric.closedBall c' (w₁ : ℝ)))
    {c c' : E} (hc : c ∈ T') (hc' : c' ∈ T') :
    volume (iUnionShade {i ∈ u | F.parent i ∈ t'} (step5InnerBody F u t' Ω hΩ k T' w₁) ∩
        Metric.closedBall c (w₁ : ℝ)) ≤
      2 * volume (iUnionShade {i ∈ u | F.parent i ∈ t'}
        (step5InnerBody F u t' Ω hΩ k T' w₁) ∩ Metric.closedBall c' (w₁ : ℝ)) := by
  rw [iUnionShade_step5FactorFamily_inter_closedBall F u t' Ω hΩ k (T' := T') (w₁ := w₁)
      (s := {i ∈ u | F.parent i ∈ t'}) hc,
    iUnionShade_step5FactorFamily_inter_closedBall F u t' Ω hΩ k (T' := T') (w₁ := w₁)
      (s := {i ∈ u | F.parent i ∈ t'}) hc']
  exact hcomp c hc c' hc'

/-- **The output mass at an arbitrary point: upper half** (blueprint
`lem:step5BallComparabilityPoint`): the mass of the output shaded union in the open ball of radius
`w₁ ` about *any* point is at most `2 * 5 ^ n` times its mass in any selected ball.

No hypothesis on `x` is needed. The ball on the left is open, which is free. -/
theorem volume_iUnionShade_step5_inter_ball_le (F : FactorFamily E ι κ) (u : Finset ι)
    (t' : Finset κ) (Ω : Set E) (hΩ : MeasurableSet Ω) (k : ℕ)
    {T' : Finset E} {w₁ : ℝ≥0} (hw₁ : 0 < w₁)
    (hsep : Metric.IsSeparated (w₁ : ℝ≥0∞) (T' : Set E))
    (hcomp : ∀ c ∈ T', ∀ c' ∈ T',
      volume (iUnionShade {i ∈ u | F.parent i ∈ t'} (step5InnerBody F u t' Ω hΩ k T' w₁) ∩
          Metric.closedBall c (w₁ : ℝ)) ≤
        2 * volume (iUnionShade {i ∈ u | F.parent i ∈ t'}
          (step5InnerBody F u t' Ω hΩ k T' w₁) ∩ Metric.closedBall c' (w₁ : ℝ)))
    (x : E) {c₀ : E} (hc₀ : c₀ ∈ T') :
    volume (iUnionShade {i ∈ u | F.parent i ∈ t'} (step5InnerBody F u t' Ω hΩ k T' w₁) ∩
        Metric.ball x (w₁ : ℝ)) ≤
      2 * (Kakeya.factoringStep5OverlapConstant (Module.finrank ℝ E) : ℝ≥0∞) *
        volume (iUnionShade {i ∈ u | F.parent i ∈ t'}
          (step5InnerBody F u t' Ω hΩ k T' w₁) ∩ Metric.closedBall c₀ (w₁ : ℝ)) := by
  classical
  let U : Set E := iUnionShade {i ∈ u | F.parent i ∈ t'} (step5InnerBody F u t' Ω hΩ k T' w₁)
  let S : Finset E := {c ∈ T' | dist c x ≤ 2 * (w₁ : ℝ)}
  have hUiUnion : U =
      iUnionShade {i ∈ u | F.parent i ∈ t'} (step3InnerBody F u t' Ω hΩ k) ∩
        step5Selection T' w₁ := by
    dsimp [U]
    exact iUnionShade_step5FactorFamily F u t' Ω hΩ k T' w₁ {i ∈ u | F.parent i ∈ t'}
  have hcover : U ∩ Metric.ball x (w₁ : ℝ) ⊆ ⋃ c ∈ S, (U ∩ Metric.closedBall c (w₁ : ℝ)) := by
    intro y hy
    have hyU : y ∈ U := hy.1
    have hyball : y ∈ Metric.ball x (w₁ : ℝ) := hy.2
    have hySel : y ∈ step5Selection T' w₁ := by
      exact (hUiUnion ▸ hyU).2
    rcases Set.mem_iUnion₂.mp hySel with ⟨c, hc, hyc⟩
    have hdist : dist c x ≤ 2 * (w₁ : ℝ) := by
      have hcy : dist c y ≤ (w₁ : ℝ) := by
        simpa [dist_comm] using hyc
      have hyx : dist y x < (w₁ : ℝ) := by
        simpa [Metric.mem_ball] using hyball
      calc
        dist c x ≤ dist c y + dist y x := dist_triangle c y x
        _ ≤ (w₁ : ℝ) + (w₁ : ℝ) := by exact add_le_add hcy (le_of_lt hyx)
        _ = 2 * (w₁ : ℝ) := by ring
    refine Set.mem_iUnion₂.mpr ⟨c, ?_, ?_⟩
    · exact (Finset.mem_filter.mpr ⟨hc, hdist⟩)
    · exact ⟨hyU, hyc⟩
  have hS_subset : (S : Set E) ⊆ (T' : Set E) := by
    intro c hc
    exact (Finset.mem_filter.mp hc).1
  have hXdist : ∀ c ∈ S, dist c x ≤ 2 * (w₁ : ℝ) := by
    intro c hc
    exact (Finset.mem_filter.mp hc).2
  have hcard : (S.card : ℝ≥0∞) ≤
      (Kakeya.factoringStep5OverlapConstant (Module.finrank ℝ E) : ℝ≥0∞) := by
    exact_mod_cast (by
      simpa [Kakeya.factoringStep5OverlapConstant] using
        Metric.IsSeparated.card_le_pow_of_dist_le (w := w₁) hw₁ (hsep.subset hS_subset) hXdist)
  calc
    volume (U ∩ Metric.ball x (w₁ : ℝ)) ≤
        ∑ c ∈ S, volume (U ∩ Metric.closedBall c (w₁ : ℝ)) := by
      exact le_trans (measure_mono hcover)
        (measure_biUnion_finset_le S (fun c => U ∩ Metric.closedBall c (w₁ : ℝ)))
    _ ≤ ∑ c ∈ S, 2 * volume (U ∩ Metric.closedBall c₀ (w₁ : ℝ)) := by
      exact Finset.sum_le_sum (fun c hc => hcomp c (Finset.mem_filter.mp hc).1 c₀ hc₀)
    _ = (S.card : ℝ≥0∞) * (2 * volume (U ∩ Metric.closedBall c₀ (w₁ : ℝ))) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Kakeya.factoringStep5OverlapConstant (Module.finrank ℝ E) : ℝ≥0∞) *
        (2 * volume (U ∩ Metric.closedBall c₀ (w₁ : ℝ))) := by
      gcongr
    _ = 2 * (Kakeya.factoringStep5OverlapConstant (Module.finrank ℝ E) : ℝ≥0∞) *
        volume (U ∩ Metric.closedBall c₀ (w₁ : ℝ)) := by
      ring

/-- **The output mass at an arbitrary point: lower half** (blueprint
`lem:step5BallComparabilityLower`): a point within `ρ` of a selected centre sees, at radius
`ρ + w₁`, at least half the output mass of any selected ball.

The parameter `ρ` is what lets a caller plug in `ρ = 6 * w₁` for a point of `U (𝒲', Y_{𝒲'})`,
using `2 r_j ≤ 4 w₁`. The radius must grow: a point near a ball of the cover need not be near the
mass inside it. -/
theorem volume_iUnionShade_step5_inter_closedBall_le_two_mul_of_dist_le (F : FactorFamily E ι κ)
    (u : Finset ι) (t' : Finset κ) (Ω : Set E) (hΩ : MeasurableSet Ω) (k : ℕ)
    {T' : Finset E} {w₁ : ℝ≥0}
    (hcomp : ∀ c ∈ T', ∀ c' ∈ T',
      volume (iUnionShade {i ∈ u | F.parent i ∈ t'} (step5InnerBody F u t' Ω hΩ k T' w₁) ∩
          Metric.closedBall c (w₁ : ℝ)) ≤
        2 * volume (iUnionShade {i ∈ u | F.parent i ∈ t'}
          (step5InnerBody F u t' Ω hΩ k T' w₁) ∩ Metric.closedBall c' (w₁ : ℝ)))
    {ρ : ℝ} {y c₀ c₁ : E} (hc₀ : c₀ ∈ T') (hc₁ : c₁ ∈ T') (hy : dist y c₁ ≤ ρ) :
    volume (iUnionShade {i ∈ u | F.parent i ∈ t'} (step5InnerBody F u t' Ω hΩ k T' w₁) ∩
        Metric.closedBall c₀ (w₁ : ℝ)) ≤
      2 * volume (iUnionShade {i ∈ u | F.parent i ∈ t'}
        (step5InnerBody F u t' Ω hΩ k T' w₁) ∩ Metric.closedBall y (ρ + (w₁ : ℝ))) := by
  have hd : (w₁ : ℝ) + dist c₁ y ≤ ρ + (w₁ : ℝ) := by
    rw [dist_comm c₁ y]
    linarith
  have hball : Metric.closedBall c₁ (w₁ : ℝ) ⊆ Metric.closedBall y (ρ + (w₁ : ℝ)) :=
    Metric.closedBall_subset_closedBall' hd
  exact le_trans (hcomp c₀ hc₀ c₁ hc₁)
    (mul_le_mul_right
      (measure_mono (Set.inter_subset_inter_right
        (iUnionShade {i ∈ u | F.parent i ∈ t'}
          (step5InnerBody F u t' Ω hΩ k T' w₁)) hball)) 2)

/-- The specialization of `volume_iUnionShade_step5_inter_closedBall_le_two_mul_of_dist_le` to a
point of the output shaded union, where `ρ = w₁` may be taken: such a point lies in the selection
set, hence within `w₁` of a selected centre. -/
theorem volume_iUnionShade_step5_inter_closedBall_le_two_mul_of_mem (F : FactorFamily E ι κ)
    (u : Finset ι) (t' : Finset κ) (Ω : Set E) (hΩ : MeasurableSet Ω) (k : ℕ)
    {T' : Finset E} {w₁ : ℝ≥0}
    (hcomp : ∀ c ∈ T', ∀ c' ∈ T',
      volume (iUnionShade {i ∈ u | F.parent i ∈ t'} (step5InnerBody F u t' Ω hΩ k T' w₁) ∩
          Metric.closedBall c (w₁ : ℝ)) ≤
        2 * volume (iUnionShade {i ∈ u | F.parent i ∈ t'}
          (step5InnerBody F u t' Ω hΩ k T' w₁) ∩ Metric.closedBall c' (w₁ : ℝ)))
    {y c₀ : E} (hc₀ : c₀ ∈ T')
    (hy : y ∈ iUnionShade {i ∈ u | F.parent i ∈ t'} (step5InnerBody F u t' Ω hΩ k T' w₁)) :
    volume (iUnionShade {i ∈ u | F.parent i ∈ t'} (step5InnerBody F u t' Ω hΩ k T' w₁) ∩
        Metric.closedBall c₀ (w₁ : ℝ)) ≤
      2 * volume (iUnionShade {i ∈ u | F.parent i ∈ t'}
        (step5InnerBody F u t' Ω hΩ k T' w₁) ∩ Metric.closedBall y (2 * (w₁ : ℝ))) := by
  have hsel : y ∈ step5Selection T' w₁ :=
    (iUnionShade_step5FactorFamily F u t' Ω hΩ k T' w₁ {i ∈ u | F.parent i ∈ t'} ▸ hy).2
  rcases Set.mem_iUnion₂.mp hsel with ⟨c₁, hc₁, hyc₁⟩
  have hgoal := volume_iUnionShade_step5_inter_closedBall_le_two_mul_of_dist_le F u t' Ω hΩ k
    hcomp (ρ := (w₁ : ℝ)) hc₀ hc₁ (Metric.mem_closedBall.mp hyc₁)
  simpa [two_mul] using hgoal

/-- **Comparable output mass across arbitrary points** (blueprint `cor:step5BallComparability`):
for every point `x` and every point `y` of the output shaded union, the mass in `ball x w₁` is at
most `4 * 5 ^ n` times the mass in `closedBall y (2 * w₁)`.

This is the honest form of "the ball mass is the same at every point up to an absolute factor": the
constant depends on the ambient dimension alone, the points are arbitrary, and the price is the
radius `2 * w₁` on the right. -/
theorem volume_iUnionShade_step5_inter_ball_le_mul_volume_inter_closedBall
    (F : FactorFamily E ι κ) (u : Finset ι) (t' : Finset κ) (Ω : Set E) (hΩ : MeasurableSet Ω)
    (k : ℕ) {T' : Finset E} {w₁ : ℝ≥0} (hw₁ : 0 < w₁) (hT' : T'.Nonempty)
    (hsep : Metric.IsSeparated (w₁ : ℝ≥0∞) (T' : Set E))
    (hcomp : ∀ c ∈ T', ∀ c' ∈ T',
      volume (iUnionShade {i ∈ u | F.parent i ∈ t'} (step5InnerBody F u t' Ω hΩ k T' w₁) ∩
          Metric.closedBall c (w₁ : ℝ)) ≤
        2 * volume (iUnionShade {i ∈ u | F.parent i ∈ t'}
          (step5InnerBody F u t' Ω hΩ k T' w₁) ∩ Metric.closedBall c' (w₁ : ℝ)))
    (x : E) {y : E}
    (hy : y ∈ iUnionShade {i ∈ u | F.parent i ∈ t'} (step5InnerBody F u t' Ω hΩ k T' w₁)) :
    volume (iUnionShade {i ∈ u | F.parent i ∈ t'} (step5InnerBody F u t' Ω hΩ k T' w₁) ∩
        Metric.ball x (w₁ : ℝ)) ≤
      4 * (Kakeya.factoringStep5OverlapConstant (Module.finrank ℝ E) : ℝ≥0∞) *
        volume (iUnionShade {i ∈ u | F.parent i ∈ t'}
          (step5InnerBody F u t' Ω hΩ k T' w₁) ∩ Metric.closedBall y (2 * (w₁ : ℝ))) := by
  classical
  obtain ⟨c₀, hc₀⟩ := hT'
  let U : Set E := iUnionShade {i ∈ u | F.parent i ∈ t'} (step5InnerBody F u t' Ω hΩ k T' w₁)
  let M : ℝ≥0∞ := Kakeya.factoringStep5OverlapConstant (Module.finrank ℝ E)
  change volume (U ∩ Metric.ball x (w₁ : ℝ)) ≤
    (4 : ℝ≥0∞) * M * volume (U ∩ Metric.closedBall y (2 * (w₁ : ℝ)))
  have hball : volume (U ∩ Metric.ball x (w₁ : ℝ)) ≤
      (2 : ℝ≥0∞) * M * volume (U ∩ Metric.closedBall c₀ (w₁ : ℝ)) := by
    simpa [U, M] using volume_iUnionShade_step5_inter_ball_le F u t' Ω hΩ k hw₁ hsep hcomp x hc₀
  have hclosed : volume (U ∩ Metric.closedBall c₀ (w₁ : ℝ)) ≤
      (2 : ℝ≥0∞) * volume (U ∩ Metric.closedBall y (2 * (w₁ : ℝ))) := by
    simpa [U] using volume_iUnionShade_step5_inter_closedBall_le_two_mul_of_mem
      F u t' Ω hΩ k hcomp hc₀ hy
  calc
    volume (U ∩ Metric.ball x (w₁ : ℝ)) ≤
        (2 : ℝ≥0∞) * M * volume (U ∩ Metric.closedBall c₀ (w₁ : ℝ)) := hball
    _ ≤ (2 : ℝ≥0∞) * M * ((2 : ℝ≥0∞) * volume (U ∩ Metric.closedBall y (2 * (w₁ : ℝ)))) := by
      exact mul_le_mul_right hclosed ((2 : ℝ≥0∞) * M)
    _ = (4 : ℝ≥0∞) * M * volume (U ∩ Metric.closedBall y (2 * (w₁ : ℝ))) := by
      ring

/-- **Closed to open balls** (blueprint `lem:step5BallBridge`): all the assembly needs to move
between the closed-ball convention used here and the open-ball convention of
`ShadedBody.outerFactoringFamily_avgMultOnBalls`. -/
theorem volume_inter_closedBall_le_volume_inter_ball (U : Set E) (y : E) {r R : ℝ} (hrR : r < R) :
    volume (U ∩ Metric.closedBall y r) ≤ volume (U ∩ Metric.ball y R) := by
  exact measure_mono (Set.inter_subset_inter_right U (Metric.closedBall_subset_ball hrR))

/-! ### The output family of Step 5 -/

/-- **The re-induced outer shading of Step 5** (blueprint `def:factoringStep5OuterBody`): the
shading induced on the enlargement of `F.outerBody j` by the Step 5 inner bodies lying over `j`.

This is `ShadedBody.step4OuterBody` rebuilt verbatim with `Y'` in place of `Y₀'`. As there, no
membership hypothesis on `j` is needed: for `j ∉ t'` the fiber is empty, so the shade is empty,
while the carrier is still the convex body `N_{r j} (F.outerBody j)`. -/
noncomputable def step5OuterBody (F : FactorFamily E ι κ) {u : Finset ι}
    (hu : u ⊆ F.innerSet) (t' : Finset κ) (Ω : Set E) (hΩ : MeasurableSet Ω)
    (k : ℕ) (T' : Finset E) (w₁ : ℝ≥0) (j : κ) : ShadedBody E :=
  inducedShading ((step5FactorFamily F hu t' Ω hΩ k T' w₁).fiber j)
    (step5FactorFamily F hu t' Ω hΩ k T' w₁).innerBody
    ((step5FactorFamily F hu t' Ω hΩ k T' w₁).outerBody j)

/-- The carrier of the Step 5 outer shaded body is the enlargement `N_{r j} (F.outerBody j)`. -/
theorem toConvexSpaceBody_step5OuterBody (F : FactorFamily E ι κ) {u : Finset ι}
    (hu : u ⊆ F.innerSet) (t' : Finset κ) (Ω : Set E) (hΩ : MeasurableSet Ω)
    (k : ℕ) (T' : Finset E) (w₁ : ℝ≥0) (j : κ) :
    (step5OuterBody F hu t' Ω hΩ k T' w₁ j).toConvexSpaceBody =
      (F.outerBody j).cthickening (F.outerBody j).scale := rfl

/-- The shade of the Step 5 outer shaded body. -/
theorem shade_step5OuterBody (F : FactorFamily E ι κ) {u : Finset ι}
    (hu : u ⊆ F.innerSet) (t' : Finset κ) (Ω : Set E) (hΩ : MeasurableSet Ω)
    (k : ℕ) (T' : Finset E) (w₁ : ℝ≥0) (j : κ) :
    (step5OuterBody F hu t' Ω hΩ k T' w₁ j).shade =
      Metric.cthickening (2 * (F.outerBody j).scale)
          (iUnionShade ((step5FactorFamily F hu t' Ω hΩ k T' w₁).fiber j)
            (step5FactorFamily F hu t' Ω hΩ k T' w₁).innerBody) ∩
        Metric.cthickening (F.outerBody j).scale (F.outerBody j).carrier := rfl

/-- **Compatibility of the Step 5 shading with the inner shading** (blueprint
`lem:factoringStep5Compatibility`), the precise form of GWZ Remark 5.4 for the *output* shadings:
over a surviving block the Step 5 outer shade is the enlargement intersected with the
`2 * r j`-thickening of the union of the Step 5 shades over the fiber of `F` inside `u`. -/
theorem shade_step5OuterBody_eq (F : FactorFamily E ι κ) {u : Finset ι}
    (hu : u ⊆ F.innerSet) (t' : Finset κ) (Ω : Set E) (hΩ : MeasurableSet Ω)
    (k : ℕ) (T' : Finset E) (w₁ : ℝ≥0) {j : κ} (hj : j ∈ t') :
    (step5OuterBody F hu t' Ω hΩ k T' w₁ j).shade =
      Metric.cthickening (F.outerBody j).scale (F.outerBody j).carrier ∩
        Metric.cthickening (2 * (F.outerBody j).scale)
          (iUnionShade {i ∈ u | F.parent i = j} (step5InnerBody F u t' Ω hΩ k T' w₁)) := by
  rw [shade_step5OuterBody, step5FactorFamily_fiber F hu t' Ω hΩ k T' w₁ hj,
    step5FactorFamily_innerBody]
  exact Set.inter_comm _ _

/-- **Shading containment for the Step 5 family** (blueprint `lem:factoringStep5Containment`):
`U (𝒱'_j, Y') ⊆ Y_{𝒲'} j`, with no hypothesis on `j`. -/
theorem iUnionShade_fiber_subset_shade_step5OuterBody (F : FactorFamily E ι κ) {u : Finset ι}
    (hu : u ⊆ F.innerSet) (t' : Finset κ) (Ω : Set E) (hΩ : MeasurableSet Ω)
    (k : ℕ) (T' : Finset E) (w₁ : ℝ≥0) (j : κ) :
    iUnionShade ((step5FactorFamily F hu t' Ω hΩ k T' w₁).fiber j)
        (step5FactorFamily F hu t' Ω hΩ k T' w₁).innerBody ⊆
      (step5OuterBody F hu t' Ω hΩ k T' w₁ j).shade := by
  let G := step5FactorFamily F hu t' Ω hΩ k T' w₁
  have hVW : ∀ i ∈ G.fiber j, (G.innerBody i).toConvexSpaceBody ≤ G.outerBody j := by
    intro i hi
    have hi' : i ∈ {i ∈ {i ∈ u | F.parent i ∈ t'} | F.parent i = j} := by
      simpa [FactorFamily.fiber, G, step5FactorFamily] using hi
    have hiu : i ∈ u := (Finset.mem_filter.mp (Finset.mem_filter.mp hi').1).1
    have hparent : F.parent i = j := (Finset.mem_filter.mp hi').2
    have hiF : i ∈ F.innerSet := hu hiu
    calc
      (G.innerBody i).toConvexSpaceBody = (F.innerBody i).toConvexSpaceBody := by
        simp [G, step5FactorFamily, toConvexSpaceBody_step5InnerBody]
      _ ≤ F.outerBody (F.parent i) := F.inner_le_parent i hiF
      _ = F.outerBody j := by rw [hparent]
      _ = G.outerBody j := by simp [G, step5FactorFamily]
  calc
    iUnionShade (G.fiber j) G.innerBody ⊆
        Metric.cthickening (G.outerBody j).scale (iUnionShade (G.fiber j) G.innerBody) :=
      Metric.self_subset_cthickening _
    _ ⊆ (inducedShading (G.fiber j) G.innerBody (G.outerBody j)).shade := by
      exact cthickening_scale_iUnionShade_subset_shade_inducedShading
        (s := G.fiber j) (V := G.innerBody) (W := G.outerBody j) hVW
    _ = (step5OuterBody F hu t' Ω hΩ k T' w₁ j).shade := by
      simp [G, step5OuterBody]

/-- **The Step 5 inner shaded union is dominated by the outer one** (blueprint
`cor:factoringStep5Union`): `U (𝒱', Y') ⊆ U (𝒲', Y_{𝒲'})`. -/
theorem iUnionShade_subset_iUnionShade_step5Outer (F : FactorFamily E ι κ) {u : Finset ι}
    (hu : u ⊆ F.innerSet) (t' : Finset κ) (Ω : Set E) (hΩ : MeasurableSet Ω) (k : ℕ)
    (T' : Finset E) (w₁ : ℝ≥0) :
    iUnionShade (step5FactorFamily F hu t' Ω hΩ k T' w₁).innerSet
        (step5FactorFamily F hu t' Ω hΩ k T' w₁).innerBody ⊆
      iUnionShade t' (step5OuterBody F hu t' Ω hΩ k T' w₁) := by
  unfold iUnionShade
  apply Set.iUnion₂_subset
  intro i hi
  have hmem : i ∈ u ∧ F.parent i ∈ t' := Finset.mem_filter.mp hi
  refine Set.subset_iUnion₂_of_subset (F.parent i) hmem.2 ?_
  have hfib := iUnionShade_fiber_subset_shade_step5OuterBody F hu t' Ω hΩ k T' w₁ (F.parent i)
  refine Set.Subset.trans ?_ hfib
  refine Set.subset_iUnion₂_of_subset i ?_ (Set.Subset.refl _)
  simp [FactorFamily.fiber, hmem]

/-- **The Step 5 outer shading refines the Step 4 one** (blueprint `lem:factoringStep5Mono`), the
comparison *between* the two constructions supplied by
`ShadedBody.shade_inducedShading_mono_of_isRefinement`. -/
theorem shade_step5OuterBody_subset_shade_step4OuterBody (F : FactorFamily E ι κ) {u : Finset ι}
    (hu : u ⊆ F.innerSet) (t' : Finset κ) (Ω : Set E) (hΩ : MeasurableSet Ω)
    (k : ℕ) (T' : Finset E) (w₁ : ℝ≥0) (j : κ) :
    (step5OuterBody F hu t' Ω hΩ k T' w₁ j).shade ⊆
      (step4OuterBody F hu t' Ω hΩ k j).shade := by
  let G5 := step5FactorFamily F hu t' Ω hΩ k T' w₁
  let G3 := step3FactorFamily F hu t' Ω hΩ k
  change (inducedShading (G5.fiber j) G5.innerBody (G5.outerBody j)).shade ⊆
    (inducedShading (G3.fiber j) G3.innerBody (G3.outerBody j)).shade
  refine shade_inducedShading_mono_of_isRefinement (s' := G5.fiber j)
    (V' := G5.innerBody) (s := G3.fiber j) (V := G3.innerBody) (W := G5.outerBody j) ?_
  constructor
  · rfl
  · intro i hi
    constructor
    · rfl
    · rw [show (G5.innerBody i).shade =
          (G3.innerBody i).shade ∩ step5Selection T' w₁ by rfl]
      exact Set.inter_subset_left

/-- The union form of `ShadedBody.shade_step5OuterBody_subset_shade_step4OuterBody`: the Step 5
outer shaded union is contained in the Step 4 one, which is the set the cover of
`ShadedBody.IsStep5Cover` covers. -/
theorem iUnionShade_step5Outer_subset_iUnionShade_step4Outer (F : FactorFamily E ι κ)
    {u : Finset ι} (hu : u ⊆ F.innerSet) (t' : Finset κ) (Ω : Set E) (hΩ : MeasurableSet Ω)
    (k : ℕ) (T' : Finset E) (w₁ : ℝ≥0) :
    iUnionShade t' (step5OuterBody F hu t' Ω hΩ k T' w₁) ⊆
      step4OuterUnion F hu t' Ω hΩ k := by
  rw [step4OuterUnion]
  unfold iUnionShade
  apply Set.iUnion₂_subset
  intro j hj
  refine Set.subset_iUnion₂_of_subset j hj ?_
  exact shade_step5OuterBody_subset_shade_step4OuterBody F hu t' Ω hΩ k T' w₁ j

/-- **The shaded factor family of Step 5** (blueprint `def:factoringStep5ShadedFamily`), the output
of the construction: the Step 5 factor family with its outer bodies shaded by the re-induced
shading `ShadedBody.step5OuterBody`.

Its outer carriers are the enlargements `N_{r j} (F.outerBody j)`, not `F.outerBody j`. -/
noncomputable def step5ShadedFactorFamily (F : FactorFamily E ι κ) {u : Finset ι}
    (hu : u ⊆ F.innerSet) (t' : Finset κ) (Ω : Set E) (hΩ : MeasurableSet Ω)
    (k : ℕ) (T' : Finset E) (w₁ : ℝ≥0) : ShadedFactorFamily E ι κ where
  innerSet := (step5FactorFamily F hu t' Ω hΩ k T' w₁).innerSet
  innerBody := (step5FactorFamily F hu t' Ω hΩ k T' w₁).innerBody
  outerSet := t'
  outerBody := step5OuterBody F hu t' Ω hΩ k T' w₁
  parent := F.parent
  parent_mem := fun i hi ↦ (Finset.mem_filter.mp hi).2
  inner_le_parent := fun i hi ↦
    le_trans ((step5FactorFamily F hu t' Ω hΩ k T' w₁).inner_le_parent i hi)
      (ConvexSpaceBody.self_le_cthickening (F.outerBody (F.parent i))
        (F.outerBody (F.parent i)).scale)
  shade_subset_parent := fun i hi ↦ by
    classical
    have hiFiber : i ∈ (step5FactorFamily F hu t' Ω hΩ k T' w₁).fiber (F.parent i) := by
      simpa [FactorFamily.fiber, step5FactorFamily] using hi
    exact fun x hx ↦
      iUnionShade_fiber_subset_shade_step5OuterBody F hu t' Ω hΩ k T' w₁ (F.parent i)
        (Set.mem_iUnion₂.mpr ⟨i, hiFiber, hx⟩)

@[simp]
theorem step5ShadedFactorFamily_innerSet (F : FactorFamily E ι κ) {u : Finset ι}
    (hu : u ⊆ F.innerSet) (t' : Finset κ) (Ω : Set E) (hΩ : MeasurableSet Ω) (k : ℕ)
    (T' : Finset E) (w₁ : ℝ≥0) :
    (step5ShadedFactorFamily F hu t' Ω hΩ k T' w₁).innerSet =
      {i ∈ u | F.parent i ∈ t'} := rfl

@[simp]
theorem step5ShadedFactorFamily_innerBody (F : FactorFamily E ι κ) {u : Finset ι}
    (hu : u ⊆ F.innerSet) (t' : Finset κ) (Ω : Set E) (hΩ : MeasurableSet Ω) (k : ℕ)
    (T' : Finset E) (w₁ : ℝ≥0) :
    (step5ShadedFactorFamily F hu t' Ω hΩ k T' w₁).innerBody =
      step5InnerBody F u t' Ω hΩ k T' w₁ := rfl

@[simp]
theorem step5ShadedFactorFamily_outerSet (F : FactorFamily E ι κ) {u : Finset ι}
    (hu : u ⊆ F.innerSet) (t' : Finset κ) (Ω : Set E) (hΩ : MeasurableSet Ω) (k : ℕ)
    (T' : Finset E) (w₁ : ℝ≥0) :
    (step5ShadedFactorFamily F hu t' Ω hΩ k T' w₁).outerSet = t' := rfl

@[simp]
theorem step5ShadedFactorFamily_outerBody (F : FactorFamily E ι κ) {u : Finset ι}
    (hu : u ⊆ F.innerSet) (t' : Finset κ) (Ω : Set E) (hΩ : MeasurableSet Ω) (k : ℕ)
    (T' : Finset E) (w₁ : ℝ≥0) :
    (step5ShadedFactorFamily F hu t' Ω hΩ k T' w₁).outerBody =
      step5OuterBody F hu t' Ω hΩ k T' w₁ := rfl

@[simp]
theorem step5ShadedFactorFamily_parent (F : FactorFamily E ι κ) {u : Finset ι}
    (hu : u ⊆ F.innerSet) (t' : Finset κ) (Ω : Set E) (hΩ : MeasurableSet Ω) (k : ℕ)
    (T' : Finset E) (w₁ : ℝ≥0) :
    (step5ShadedFactorFamily F hu t' Ω hΩ k T' w₁).parent = F.parent := rfl

end ShadedBody
