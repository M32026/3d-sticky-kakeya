/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.ThinSetup

/-!
# Parts of `Kakeya.ThinCase.factoringApply`

`Kakeya.ThinCase.factoringApply` (blueprint `lem:ml2thinFactoringApply`) is the thin-case
application of the corrected GWZ Proposition 5.1. Its conclusion is a thirteen-fold conjunction,
and its proof is treated separately. This file isolates the pieces that *are* settled, and records — as
compiler-checked statements rather than prose — exactly where the remaining obstruction lies.

The contents are, in order:

* `Kakeya.ThinCase.Produce.fullness_ne_zero_of_densityBound` and
  `Kakeya.ThinCase.Produce.exists_shade_ne_zero_of_densityBound` — non-degeneracy. Conclusion (i)
  cannot be met by an all-empty output, so the statement is not vacuously satisfiable.
* `Kakeya.ThinCase.Produce.structural_*` — the eight structural conjuncts, proved for the
  canonical outer shaded bodies `Kakeya.ThinCase.blockOuterBody`, together with the bundling
  theorem `Kakeya.ThinCase.Produce.factoringApply_structural`. What is left after these is
  exactly (i), (iii) and (iv).
* `Kakeya.ThinCase.Produce.centredMult_forces_thickening` — the obstruction in (iv), stated
  positively: conclusion (iv) at equal radii *forces* the outer shaded union into the open
  `w₁`-neighbourhood of the inner shaded union. Conclusion (v) only puts it in the closed
  `2 τ₂(Wb j)`-neighbourhood, and `2 τ₂(Wb j)` ranges over `[w₁, 4 w₁]`, so (iv) is strictly
  stronger than (v) at the radius the factoring construction actually delivers.
* `Kakeya.ThinCase.Produce.centredMultOfSubset` and
  `Kakeya.ThinCase.Produce.centredMultTwoRadius` — the repair route. The consumer
  `Kakeya.ThinCase.centredMult` never needs equal radii: it widens the right-hand ball to radius
  `A` at once. The two-radius version proved here has the *same* conclusion and the *same*
  constant, so weakening (iv) to the two-radius form of GWZ Item 7
  (`ShadedBody.outerFactoringFamily_avgMultOnBalls`, radius `7 * w₁` on the right) costs nothing
  downstream except a larger `Kakeya.ThinCase.w1Constant`; `seven_mul_le_sixteen_mul` and
  `rad_too_small_for_seven_mul` say precisely how much larger, and that the present value is
  genuinely too small.

Nothing here changes any existing statement, and nothing here is used by `factoringApply` itself.

**`Kakeya.ThinCase.Produce.volume_carrier_le_of_isFrostmanIn` is no longer here.** The eccentricity
bridge — the Frostman constant `CF` of clause (C4) bounding the volume of a body by the total
carrier volume of its own block — was stated in this file, which sits *above*
`Kakeya.DimensionThree.MainLemma2.ThinSetup` and therefore put it out of reach of `factoringApply`,
whose conjunct (i) is its only consumer. Its proof uses only `Kakeya.densityIn`,
`Kakeya.densityIn_of_all_le` and `ConvexSpaceBody.IsFrostmanIn`, none of which needs anything from
this file, so it now lives in `Kakeya.DimensionThree.MainLemma2.ThinEccentricity` beside the
`Kakeya.ThinCase.exists_eccentricity_exponent` that composes it. The namespace is unchanged.
-/

@[expose] public section

namespace Kakeya.ThinCase

open MeasureTheory Metric Set ShadedBody

namespace Produce

section Nondegenerate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Conclusion (i) of `Kakeya.ThinCase.factoringApply` is not vacuously satisfiable.**

`(δ : ℝ≥0∞) ^ (2 * η)` is strictly positive for every real `η` as soon as `0 < δ`, so the
density bound (i) forces the produced outer family to carry positive shading mass. In
particular `bodies'` is nonempty and the family is not the empty one. -/
theorem fullness_ne_zero_of_densityBound {ω : Type*} {bodies' : Finset ω} {W : ω → ShadedBody E}
    {δ C : NNReal} {η : ℝ} (hδ : 0 < δ)
    (h : (δ : ENNReal) ^ (2 * η) ≤ (C : ENNReal) * (fullness bodies' W : ENNReal)) :
    fullness bodies' W ≠ 0 := by
  have hδ0 : (δ : ENNReal) ≠ 0 := by
    simpa using (ENNReal.coe_pos.mpr hδ).ne'
  have hpos : 0 < (δ : ENNReal) ^ (2 * η) :=
    ENNReal.rpow_pos (by simpa using ENNReal.coe_pos.mpr hδ) ENNReal.coe_ne_top
  intro hzero
  rw [hzero, ENNReal.coe_zero, mul_zero, nonpos_iff_eq_zero] at h
  exact hpos.ne' h

/-- **Conclusion (i) forces a nonnull outer shading.** The same statement as
`Kakeya.ThinCase.Produce.fullness_ne_zero_of_densityBound`, unwound into the form the geometry
uses: some retained body really is shaded. -/
theorem exists_shade_ne_zero_of_densityBound {ω : Type*} {bodies' : Finset ω}
    {W : ω → ShadedBody E} {δ C : NNReal} {η : ℝ} (hδ : 0 < δ)
    (h : (δ : ENNReal) ^ (2 * η) ≤ (C : ENNReal) * (fullness bodies' W : ENNReal)) :
    ∃ j ∈ bodies', volume (W j).shade ≠ 0 := by
  have hne := fullness_ne_zero_of_densityBound (W := W) (C := C) (η := η) hδ h
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  apply hne
  have hsum : ∑ j ∈ bodies', volume (W j).shade = 0 :=
    Finset.sum_eq_zero fun j hj => hcon j hj
  have : (fullness bodies' W : ENNReal) = 0 := by
    rw [fullness_def, hsum, ENNReal.zero_div]
  exact_mod_cast this

end Nondegenerate

section Structural

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

variable {σ ω : Type*} [DecidableEq ω] {segs segs' : Finset σ} {Y Y' : σ → ShadedBody E}
  {bodies bodies' : Finset ω} {Wb : ω → ConvexSpaceBody E} {blk : σ → ω}
  {hle : ∀ p ∈ segs', (Y' p).toConvexSpaceBody ≤ Wb (blk p)}

omit [BorelSpace E] in
/-- **Conclusion (ii) of `Kakeya.ThinCase.factoringApply`** for the canonical outer bodies: a
shaded point of a retained segment lies in the shade of the outer body of its block, and that
block is retained. -/
theorem structural_pointwise_containment (hblk' : ∀ p ∈ segs', blk p ∈ bodies') :
    ∀ p ∈ segs', ∀ x ∈ (Y' p).shade,
      blk p ∈ bodies' ∧ x ∈ (blockOuterBody segs' Y' Wb blk hle (blk p)).shade :=
  fun p hp _ hx => ⟨hblk' p hp, mem_blockOuterBody_shade hp hx⟩

omit [BorelSpace E] in
/-- **The lower half of the enlargement sandwich of `Kakeya.ThinCase.factoringApply`** for the
canonical outer bodies. -/
theorem structural_sandwich_lower :
    ∀ j ∈ bodies', Wb j ≤ (blockOuterBody segs' Y' Wb blk hle j).toConvexSpaceBody :=
  fun j _ => Wb_le_blockOuterBody j

omit [BorelSpace E] in
/-- **The upper half of the enlargement sandwich of `Kakeya.ThinCase.factoringApply`** for the
canonical outer bodies; it holds with equality. -/
theorem structural_sandwich_upper :
    ∀ j ∈ bodies', (blockOuterBody segs' Y' Wb blk hle j).toConvexSpaceBody ≤
      (Wb j).cthickening (Wb j).scale :=
  fun j _ => blockOuterBody_le_cthickening j

omit [BorelSpace E] in
/-- **Conclusion (v) of `Kakeya.ThinCase.factoringApply`** for the canonical outer bodies: the
outer shading lies in the closed neighbourhood of the blockwise shaded union at twice the
per-body radius. For this choice the containment is the trivial one. -/
theorem structural_shade_subset :
    ∀ j ∈ bodies', (blockOuterBody segs' Y' Wb blk hle j).shade ⊆
      cthickening (2 * Metric.thickness ℝ (Wb j).carrier (Module.finrank ℝ E - 1))
        (iUnionShade (segs'.filter fun p => blk p = j) Y') :=
  fun j _ => blockOuterBody_shade_subset_cthickening j

omit [BorelSpace E] in
/-- **The eight structural conjuncts of `Kakeya.ThinCase.factoringApply`, at once.**

Given any subfamily `segs' ⊆ segs` carrying a shading `Y'` with the same carriers as `Y` and
smaller shades, any set of blocks `bodies' ⊆ bodies` containing every retained block, and the
canonical outer shaded bodies `Kakeya.ThinCase.blockOuterBody`, the two subfamily clauses, the
two shading clauses, the two halves of the enlargement sandwich, clause (ii) and clause (v) all
hold.

What is left of `Kakeya.ThinCase.factoringApply` after this is exactly the four quantitative
clauses (i), (iii) — both halves — , (iv) and (vi); and for this particular choice of outer
bodies (iv) is by `Kakeya.ThinCase.blockOuterBody_iUnionShade` the honest centred multiplicity
statement of the *inner* shaded union, since the outer union coincides with it. -/
theorem factoringApply_structural (hsegs' : segs' ⊆ segs) (hbodies' : bodies' ⊆ bodies)
    (hcar : ∀ p ∈ segs, (Y' p).toConvexSpaceBody = (Y p).toConvexSpaceBody)
    (hshade : ∀ p ∈ segs', (Y' p).shade ⊆ (Y p).shade)
    (hblk' : ∀ p ∈ segs', blk p ∈ bodies') :
    segs' ⊆ segs ∧ bodies' ⊆ bodies ∧
      (∀ p ∈ segs, (Y' p).toConvexSpaceBody = (Y p).toConvexSpaceBody) ∧
      (∀ p ∈ segs', (Y' p).shade ⊆ (Y p).shade) ∧
      (∀ j ∈ bodies', Wb j ≤ (blockOuterBody segs' Y' Wb blk hle j).toConvexSpaceBody) ∧
      (∀ j ∈ bodies', (blockOuterBody segs' Y' Wb blk hle j).toConvexSpaceBody ≤
        (Wb j).cthickening (Wb j).scale) ∧
      (∀ p ∈ segs', ∀ x ∈ (Y' p).shade,
        blk p ∈ bodies' ∧ x ∈ (blockOuterBody segs' Y' Wb blk hle (blk p)).shade) ∧
      (∀ j ∈ bodies', (blockOuterBody segs' Y' Wb blk hle j).shade ⊆
        cthickening (2 * Metric.thickness ℝ (Wb j).carrier (Module.finrank ℝ E - 1))
          (iUnionShade (segs'.filter fun p => blk p = j) Y')) :=
  ⟨hsegs', hbodies', hcar, hshade, structural_sandwich_lower, structural_sandwich_upper,
    structural_pointwise_containment hblk', structural_shade_subset⟩

end Structural

section Obstruction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **What conclusion (iv) of `Kakeya.ThinCase.factoringApply` really asks for.**

The centred multiplicity statement at equal radii forces the whole outer shaded union `UW` into
the *open* `w₁`-neighbourhood of the inner shaded union `U`, as soon as `U` is not null: a point
`y ∈ UW` further than `w₁` from `U` has `volume (U ∩ ball y w₁) = 0`, so (iv) makes every
`volume (U ∩ ball x w₁)` vanish, and a set all of whose small balls are null is null.

Conclusion (v) of `factoringApply` puts `(W j).shade` in the *closed* `2 τ₂(Wb j)`-neighbourhood
of the blockwise inner union, and the hypothesis `hw₁` of `factoringApply` allows
`w₁ ≤ 2 τ₂(Wb j) ≤ 4 w₁`. So (iv) is strictly stronger than (v) at the radius the corrected
Proposition 5.1 delivers, and this is the reason its Item 7
(`ShadedBody.outerFactoringFamily_avgMultOnBalls`) is stated with the *unequal* radii
`ball x w₁` versus `closedBall y (7 * w₁)`. -/
theorem centredMult_forces_thickening {U UW : Set E} {w₁ : ℝ} (hw₁ : 0 < w₁) {C : NNReal}
    (hU : volume U ≠ 0)
    (hiv : ∀ x ∈ UW, ∀ y ∈ UW,
      volume (U ∩ ball x w₁) ≤ (C : ENNReal) * volume (U ∩ ball y w₁))
    (hUUW : U ⊆ UW) :
    UW ⊆ Metric.thickening w₁ U := by
  intro y hy
  by_contra hny
  -- a point outside the neighbourhood sees no mass at all
  have hempty : U ∩ ball y w₁ = ∅ := by
    ext z
    simp only [Set.mem_inter_iff, Metric.mem_ball, Set.mem_empty_iff_false, iff_false, not_and]
    intro hzU hz
    exact hny (Metric.mem_thickening_iff.mpr ⟨z, hzU, by rwa [dist_comm]⟩)
  have hzero : volume (U ∩ ball y w₁) = 0 := by rw [hempty]; simp
  -- hence every small ball centred in `U` is null
  have hloc : ∀ x ∈ U, volume (U ∩ ball x w₁) = 0 := by
    intro x hx
    have := hiv x (hUUW hx) y hy
    rw [hzero, mul_zero] at this
    exact le_antisymm this (zero_le)
  -- and a locally null set is null
  exact hU (measure_null_of_locally_null U fun x hx =>
    ⟨U ∩ ball x w₁, inter_mem_nhdsWithin U (Metric.ball_mem_nhds x hw₁), hloc x hx⟩)

end Obstruction

section Repair

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **`Kakeya.ThinCase.centredMult` never needed equal radii.**

The `w₁`-ball on the right of the comparison hypothesis is widened to the `A`-ball at once in the
proof of `Kakeya.ThinCase.centredMult`, so any comparison set `R y ⊆ ball y A` will do, with the
same conclusion and the same constant `Kakeya.ThinCase.centredMultConstant C C₁ n`. -/
theorem centredMultOfSubset {U UW : Set E} (hUUW : U ⊆ UW) {w₁ A : ℝ} (hw₁ : 0 < w₁)
    (hle : w₁ ≤ A) {C₁ : NNReal} (hA : A ≤ C₁ * w₁) {C : NNReal} {R : E → Set E}
    (hR : ∀ y, R y ⊆ ball y A)
    (hcomp : ∀ x ∈ UW, ∀ y ∈ UW,
      volume (U ∩ ball x w₁) ≤ (C : ENNReal) * volume (U ∩ R y)) :
    ∀ x ∈ U, ∀ y ∈ U, volume (U ∩ ball x A) ≤
      (centredMultConstant C C₁ (Module.finrank ℝ E) : ENNReal) * volume (U ∩ ball y A) := by
  intro x hx y hy
  set n : ℕ := Module.finrank ℝ E with hn
  set K : NNReal := (4 * C₁) ^ n with hK
  have hApos : (0 : ℝ) < A := lt_of_lt_of_le hw₁ hle
  have hC₁ : (1 : ℝ) ≤ (C₁ : ℝ) := by
    have hw' : (1 : ℝ) * w₁ ≤ (C₁ : ℝ) * w₁ := by simpa using le_trans hle hA
    exact (mul_le_mul_iff_of_pos_right hw₁).mp hw'
  have hq : (A / w₁ : ℝ) ≤ (C₁ : ℝ) := (div_le_iff₀ hw₁).2 hA
  have hbounded : Bornology.IsBounded (U ∩ ball x A) :=
    Metric.isBounded_ball.subset (inter_subset_right : U ∩ ball x A ⊆ ball x A)
  rcases exists_maximal_separated hbounded hw₁ with ⟨N, hNsub, hsep, hmax⟩
  have hNball : (↑N : Set E) ⊆ ball x A := fun z hz => (hNsub hz).2
  have hcard := finite_and_card_le_of_separated hw₁ hApos.le x (hsep := hsep) (hN := hNball)
  have hcardR : (N.card : ℝ) ≤ (K : ℝ) := by
    have hbase : (1 : ℝ) + 2 * A / w₁ ≤ 4 * (C₁ : ℝ) := by
      have hbase2 : (2 * A / w₁ : ℝ) ≤ 2 * (C₁ : ℝ) := by
        rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_left hq (by norm_num)
      calc
        (1 : ℝ) + 2 * A / w₁ ≤ 1 + 2 * (C₁ : ℝ) := by
          rw [mul_div_assoc]
          gcongr
        _ ≤ 4 * (C₁ : ℝ) := by nlinarith [hC₁]
    have hbase0 : (0 : ℝ) ≤ 1 + 2 * A / w₁ := by
      have hposA : (0 : ℝ) ≤ A / w₁ := le_of_lt (div_pos hApos hw₁)
      have hterm : (0 : ℝ) ≤ (2 * A) / w₁ := by
        rw [mul_div_assoc]
        exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hposA
      linarith
    have hpow : (1 + 2 * A / w₁) ^ n ≤ (4 * (C₁ : ℝ)) ^ n := pow_le_pow_left₀ hbase0 hbase n
    have hKreal : (K : ℝ) = (4 * (C₁ : ℝ)) ^ n := by simp [hK, NNReal.coe_pow]
    simpa [Set.ncard_coe_finset, hKreal] using le_trans hcard.2 hpow
  have hcardNN : (N.card : NNReal) ≤ K := NNReal.coe_le_coe.mp (by simpa using hcardR)
  have hcardE : (N.card : ENNReal) ≤ (K : ENNReal) := by
    simpa using ENNReal.coe_le_coe.mpr hcardNN
  have hcover : U ∩ ball x A ⊆ ⋃ z ∈ N, (U ∩ ball z w₁) := by
    intro u hu
    rcases hmax u hu with ⟨z, hzN, hzdist⟩
    exact Set.mem_iUnion.mpr ⟨z, Set.mem_iUnion.mpr ⟨hzN, ⟨hu.1, hzdist⟩⟩⟩
  have hRy : volume (U ∩ R y) ≤ volume (U ∩ ball y A) :=
    measure_mono (Set.inter_subset_inter (Set.Subset.refl U) (hR y))
  calc
    volume (U ∩ ball x A) ≤ volume (⋃ z ∈ N, (U ∩ ball z w₁)) := measure_mono hcover
    _ ≤ ∑ z ∈ N, volume (U ∩ ball z w₁) := measure_biUnion_finset_le N (fun z => U ∩ ball z w₁)
    _ ≤ (N.card : ENNReal) * ((C : ENNReal) * volume (U ∩ R y)) := by
      have h : ∀ z ∈ N, volume (U ∩ ball z w₁) ≤ (C : ENNReal) * volume (U ∩ R y) := by
        intro z hz
        exact hcomp z (hUUW (hNsub hz).1) y (hUUW hy)
      calc
        (∑ z ∈ N, volume (U ∩ ball z w₁)) ≤ N.card • ((C : ENNReal) * volume (U ∩ R y)) :=
          Finset.sum_le_card_nsmul N (fun z => volume (U ∩ ball z w₁))
            ((C : ENNReal) * volume (U ∩ R y)) h
        _ = (N.card : ENNReal) * ((C : ENNReal) * volume (U ∩ R y)) := by simp
    _ ≤ (N.card : ENNReal) * ((C : ENNReal) * volume (U ∩ ball y A)) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hRy zero_le) zero_le
    _ ≤ (K : ENNReal) * ((C : ENNReal) * volume (U ∩ ball y A)) :=
      mul_le_mul_of_nonneg_right hcardE zero_le
    _ ≤ (centredMultConstant C C₁ n : ENNReal) * volume (U ∩ ball y A) := by
      have hKC : (C * K : NNReal) ≤ centredMultConstant C C₁ n := by
        rw [centredMultConstant]
        change (C * K : NNReal) ≤ max 1 (C * (4 * C₁) ^ n)
        exact le_max_right _ _
      have hKCE : ((C * K : NNReal) : ENNReal) ≤ (centredMultConstant C C₁ n : ENNReal) :=
        ENNReal.coe_le_coe.mpr hKC
      have heq : (K : ENNReal) * ((C : ENNReal) * volume (U ∩ ball y A)) =
          ((C * K : NNReal) : ENNReal) * volume (U ∩ ball y A) := by
        rw [← mul_assoc, mul_comm (K : ENNReal) (C : ENNReal), ← ENNReal.coe_mul]
      rw [heq]
      exact mul_le_mul_of_nonneg_right hKCE zero_le

/-- **The two-radius form of `Kakeya.ThinCase.centredMult`.**

Verbatim `Kakeya.ThinCase.centredMult` with its comparison hypothesis replaced by the unequal
radius form that GWZ Item 7 (`ShadedBody.outerFactoringFamily_avgMultOnBalls`) actually delivers:
an open `w₁`-ball on the left against a closed `s`-ball on the right. The only extra hypothesis is
`s < A`, and the constant is unchanged. -/
theorem centredMultTwoRadius {U UW : Set E} (hUUW : U ⊆ UW) {w₁ A s : ℝ} (hw₁ : 0 < w₁)
    (hle : w₁ ≤ A) {C₁ : NNReal} (hA : A ≤ C₁ * w₁) (hsA : s < A) {C : NNReal}
    (hcomp : ∀ x ∈ UW, ∀ y ∈ UW,
      volume (U ∩ ball x w₁) ≤ (C : ENNReal) * volume (U ∩ closedBall y s)) :
    ∀ x ∈ U, ∀ y ∈ U, volume (U ∩ ball x A) ≤
      (centredMultConstant C C₁ (Module.finrank ℝ E) : ENNReal) * volume (U ∩ ball y A) :=
  centredMultOfSubset hUUW hw₁ hle hA
    (R := fun y => closedBall y s) (fun _ => Metric.closedBall_subset_ball hsA) hcomp

/-- **Constant in `Kakeya.ThinCase.Produce.centredMult_of_ballNet`**: the number of points of a
`w₁/2`-separated set inside a ball of radius `3 w₁ / 2`, namely `(1 + 2 * 3)^n = 7^n`, times the
mass-comparison constant `K` of the net. It depends on the ambient dimension and on `K` only. -/
noncomputable def ballNetMultConstant (K : NNReal) (n : ℕ) : NNReal := K * 7 ^ n

/-- **The construction step that makes conclusion (iv) of `Kakeya.ThinCase.factoringApply`
available at equal radii.**

If the shaded union `U` is covered by the half-radius balls of a `w₁`-separated finite net `T`,
and the masses `|U ∩ B(c, w₁/2)|`, `c ∈ T`, are comparable up to `K`, then the centred
multiplicity statement holds at radius `w₁` on *both* sides, with the dimensional constant
`ballNetMultConstant K n`.

Both halves are elementary. For the lower bound, `y ∈ U` lies in some `B(c₀, w₁/2)`, and that
whole ball is inside `B(y, w₁)`, so `|U ∩ B(y,w₁)| ≥ |U ∩ B(c₀,w₁/2)|` — this is the step that
fails for a general shading, and it is exactly why GWZ Item 7
(`ShadedBody.outerFactoringFamily_avgMultOnBalls`) has to enlarge the right-hand radius. For the
upper bound, `B(x,w₁)` meets only the net balls whose centre is within `3 w₁ / 2` of `x`, and a
`w₁/2`-separated set has at most `7 ^ n` points there.

So conclusion (iv) is *not* unprovable: it is provable for any output whose shading is supported
on a `w₁`-separated net of half-balls of comparable mass. That is an extra construction step —
the analogue for Item 7 of what `ShadedBody.outerFactoringOuterRefined` is for Item 3 — and
neither implementation of Proposition 5.1 in this repository performs it. -/
theorem centredMult_of_ballNet {U : Set E} {T : Finset E} {w₁ : ℝ} (hw₁ : 0 < w₁)
    (hsep : ∀ c ∈ T, ∀ c' ∈ T, c ≠ c' → w₁ / 2 ≤ dist c c')
    (hcover : U ⊆ ⋃ c ∈ T, ball c (w₁ / 2)) {K : NNReal}
    (hmass : ∀ c ∈ T, ∀ c' ∈ T,
      volume (U ∩ ball c (w₁ / 2)) ≤ (K : ENNReal) * volume (U ∩ ball c' (w₁ / 2))) :
    ∀ x ∈ U, ∀ y ∈ U, volume (U ∩ ball x w₁) ≤
      (ballNetMultConstant K (Module.finrank ℝ E) : ENNReal) * volume (U ∩ ball y w₁) := by
  classical
  intro x hx y hy
  set n : ℕ := Module.finrank ℝ E with hn
  -- the net ball containing `y` sits inside `B(y, w₁)`
  obtain ⟨c₀, hc₀T, hc₀y⟩ : ∃ c ∈ T, y ∈ ball c (w₁ / 2) := by
    simpa using Set.mem_iUnion₂.mp (hcover hy)
  have hlow : volume (U ∩ ball c₀ (w₁ / 2)) ≤ volume (U ∩ ball y w₁) := by
    refine measure_mono (Set.inter_subset_inter (Set.Subset.refl U) ?_)
    intro z hz
    have h1 : dist z c₀ < w₁ / 2 := Metric.mem_ball.mp hz
    have h2 : dist c₀ y < w₁ / 2 := by rw [dist_comm]; exact Metric.mem_ball.mp hc₀y
    have : dist z y < w₁ := lt_of_le_of_lt (dist_triangle z c₀ y) (by linarith)
    exact Metric.mem_ball.mpr this
  -- only the net balls with centre within `3 w₁ / 2` of `x` can meet `B(x, w₁)`
  set S : Finset E := T.filter (fun c => dist c x < 3 * w₁ / 2) with hS
  have hup : U ∩ ball x w₁ ⊆ ⋃ c ∈ S, (U ∩ ball c (w₁ / 2)) := by
    rintro z ⟨hzU, hzx⟩
    obtain ⟨c, hcT, hzc⟩ : ∃ c ∈ T, z ∈ ball c (w₁ / 2) := by
      simpa using Set.mem_iUnion₂.mp (hcover hzU)
    have hcx : dist c x < 3 * w₁ / 2 := by
      have h1 : dist c z < w₁ / 2 := by rw [dist_comm]; exact Metric.mem_ball.mp hzc
      have h2 : dist z x < w₁ := Metric.mem_ball.mp hzx
      exact lt_of_le_of_lt (dist_triangle c z x) (by linarith)
    exact Set.mem_iUnion₂.mpr ⟨c, Finset.mem_filter.mpr ⟨hcT, hcx⟩, ⟨hzU, hzc⟩⟩
  -- the number of such centres is at most `4 ^ n`
  have hSsep : ∀ c ∈ (↑S : Set E), ∀ c' ∈ (↑S : Set E), c ≠ c' → w₁ / 2 ≤ dist c c' := by
    intro c hc c' hc' hne
    exact hsep c (Finset.mem_filter.mp hc).1 c' (Finset.mem_filter.mp hc').1 hne
  have hSball : (↑S : Set E) ⊆ ball x (3 * w₁ / 2) := by
    intro c hc
    exact Metric.mem_ball.mpr (Finset.mem_filter.mp hc).2
  have hcard := finite_and_card_le_of_separated (by positivity : (0 : ℝ) < w₁ / 2)
    (by positivity : (0 : ℝ) ≤ 3 * w₁ / 2) x hSsep hSball
  have hcardR : (S.card : ℝ) ≤ (7 : ℝ) ^ n := by
    have hrw : (1 : ℝ) + 2 * (3 * w₁ / 2) / (w₁ / 2) = 7 := by
      field_simp
      ring
    rw [Set.ncard_coe_finset, hrw] at hcard
    exact hcard.2
  have hcardNN : (S.card : NNReal) ≤ (7 : NNReal) ^ n :=
    NNReal.coe_le_coe.mp (by simpa using hcardR)
  have hcardE : (S.card : ENNReal) ≤ ((7 : NNReal) ^ n : ENNReal) := by
    simpa using ENNReal.coe_le_coe.mpr hcardNN
  -- assemble
  calc
    volume (U ∩ ball x w₁) ≤ volume (⋃ c ∈ S, (U ∩ ball c (w₁ / 2))) := measure_mono hup
    _ ≤ ∑ c ∈ S, volume (U ∩ ball c (w₁ / 2)) :=
      measure_biUnion_finset_le S (fun c => U ∩ ball c (w₁ / 2))
    _ ≤ (S.card : ENNReal) * ((K : ENNReal) * volume (U ∩ ball c₀ (w₁ / 2))) := by
      have h : ∀ c ∈ S, volume (U ∩ ball c (w₁ / 2)) ≤
          (K : ENNReal) * volume (U ∩ ball c₀ (w₁ / 2)) :=
        fun c hc => hmass c (Finset.mem_filter.mp hc).1 c₀ hc₀T
      calc
        (∑ c ∈ S, volume (U ∩ ball c (w₁ / 2)))
            ≤ S.card • ((K : ENNReal) * volume (U ∩ ball c₀ (w₁ / 2))) :=
          Finset.sum_le_card_nsmul S (fun c => volume (U ∩ ball c (w₁ / 2)))
            ((K : ENNReal) * volume (U ∩ ball c₀ (w₁ / 2))) h
        _ = (S.card : ENNReal) * ((K : ENNReal) * volume (U ∩ ball c₀ (w₁ / 2))) := by simp
    _ ≤ ((7 : NNReal) ^ n : ENNReal) * ((K : ENNReal) * volume (U ∩ ball y w₁)) := by
      gcongr
    _ = (ballNetMultConstant K n : ENNReal) * volume (U ∩ ball y w₁) := by
      rw [ballNetMultConstant, ENNReal.coe_mul, ENNReal.coe_pow]
      push_cast
      ring

/-- **The ball net of `Kakeya.ThinCase.Produce.centredMult_of_ballNet` always exists.**

A maximal `w₁/2`-separated subset of a bounded shaded union is finite, is contained in the union,
and its half-radius balls cover it. So the only genuinely new input that conclusion (iv) of
`Kakeya.ThinCase.factoringApply` needs, beyond what `Kakeya.ThinCase.Produce.centredMult_of_ballNet`
supplies, is the *mass comparability* `hmass` of the net — a dyadic pigeonhole over the centres,
paid for by the `Ccore` envelope, exactly as Item 3 of Proposition 5.1 pays for its own extra
pigeonhole with `outerFactoringFamily_outerConstMultFat.c`. -/
theorem exists_ballNet {U : Set E} (hU : Bornology.IsBounded U) {w₁ : ℝ} (hw₁ : 0 < w₁) :
    ∃ T : Finset E, (↑T : Set E) ⊆ U ∧
      (∀ c ∈ T, ∀ c' ∈ T, c ≠ c' → w₁ / 2 ≤ dist c c') ∧
      U ⊆ ⋃ c ∈ T, ball c (w₁ / 2) := by
  obtain ⟨T, hTU, hTsep, hTmax⟩ := exists_maximal_separated hU (by positivity : (0 : ℝ) < w₁ / 2)
  refine ⟨T, hTU, hTsep, ?_⟩
  intro z hz
  obtain ⟨c, hcT, hzc⟩ := hTmax z hz
  exact Set.mem_iUnion₂.mpr ⟨c, hcT, Metric.mem_ball.mpr hzc⟩

end Repair

section RadiusBudget

/-- The radius arithmetic the two-radius repair needs: from the thickness comparison
`τ₂ ≤ C₀ * a` of clause (C4) and the width comparison `w₁ ≤ 2 * τ₂` of `hw₁`, the radius
`7 * w₁` of GWZ Item 7 is dominated by `16 * C₀ * a`. So replacing
`Kakeya.ThinCase.w1Constant C₀ = max 1 (4 * C₀)` by `max 1 (16 * C₀)` makes
`7 * w₁ ≤ rad C₀ a`. -/
theorem seven_mul_le_sixteen_mul {C₀ a w₁ τ₂ : ℝ} (hC₀ : 0 ≤ C₀) (ha : 0 ≤ a)
    (hτ : τ₂ ≤ C₀ * a) (hw : w₁ ≤ 2 * τ₂) : 7 * w₁ ≤ 16 * C₀ * a := by
  nlinarith [mul_nonneg hC₀ ha]

/-- **The present value of `Kakeya.ThinCase.w1Constant` is genuinely too small for the
two-radius repair**: the enlargement in `seven_mul_le_sixteen_mul` is not optional.

The data `C₀ = 1`, `a = 1`, `τ₂ = 1`, `w₁ = 2` satisfies every constraint the thin case imposes
on these four quantities — `1 ≤ C₀`, `C₀⁻¹ * a ≤ τ₂ ≤ C₀ * a` from clause (C4),
`τ₂ ≤ 2 * w₁` and `w₁ ≤ 2 * τ₂` from `hw₁` — and yet `7 * w₁ = 14 > 4 = max 1 (4 * C₀) * a`. -/
theorem rad_too_small_for_seven_mul :
    ¬ (∀ C₀ a w₁ τ₂ : ℝ, 1 ≤ C₀ → 0 ≤ a → C₀⁻¹ * a ≤ τ₂ → τ₂ ≤ C₀ * a →
      τ₂ ≤ 2 * w₁ → w₁ ≤ 2 * τ₂ → 7 * w₁ ≤ max 1 (4 * C₀) * a) := by
  intro h
  have := h 1 1 2 1 le_rfl zero_le_one (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num at this

/-- **The radius gap between conclusions (iv) and (v) of `Kakeya.ThinCase.factoringApply`.**

The hypothesis `hw₁` of `factoringApply` says exactly `τ₂ ≤ 2 * w₁` and `w₁ ≤ 2 * τ₂` for the
shortest dimension `τ₂ = Metric.thickness ℝ (Wb j).carrier (finrank ℝ E - 1)` of every body. Hence
the radius `2 * τ₂` at which (v) places the outer shading ranges over `[w₁, 4 * w₁]`: it is never
smaller than `w₁`, and can be four times larger.

Together with `Kakeya.ThinCase.Produce.centredMult_forces_thickening` — which shows that (iv)
confines the outer shaded union to the *open* `w₁`-neighbourhood of the inner one — this says that
(iv) is a strictly stronger localisation of the outer shading than (v) asserts, and that the
factoring construction, whose outer shading genuinely reaches distance `2 * τ₂`, does not supply
it. -/
theorem two_mul_thickness_bounds {w₁ τ₂ : ℝ} (h₁ : τ₂ ≤ 2 * w₁) (h₂ : w₁ ≤ 2 * τ₂) :
    w₁ ≤ 2 * τ₂ ∧ 2 * τ₂ ≤ 4 * w₁ := ⟨h₂, by linarith⟩

end RadiusBudget

end Produce

end Kakeya.ThinCase
