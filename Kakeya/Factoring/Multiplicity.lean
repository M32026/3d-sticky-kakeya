/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.FactorFamily.Predicates
public import Kakeya.LEApprox
public import Kakeya.Multiplicity
public import Kakeya.ConstantMultiplicity
public import Kakeya.Frostman
public import Kakeya.DimensionThree.InducedShading
public import Kakeya.Factoring.OuterPacking
public import Kakeya.Factoring.RhoTubes

/-! # Corrected factoring and multiplicity proposition (GWZ Proposition 5.1)

This file isolates the outer factoring family construction of GWZ Proposition 5.1 and its
property lemmas. The construction is parametrized by the discretization scale `δ` and the outer
scale `w₁`, and every quantitative item has its own loss constant with its dependencies stated
explicitly. There is deliberately no bundled conjunction: downstream results should cite the
individual items.

**The construction is now real.** `ShadedBody.outerFactoringFamily` is defined as the Step 0 -
Step 5 factoring pipeline `ShadedBody.FactorFamily.pipelineFamily` of `Kakeya/Factoring/Pipeline.lean`,
run at ball radius `r = w₁` with the Step 5 selection centres supplied by
`ShadedBody.exists_factoringPipelineSelf`.

Three points about the transition are worth recording, because they change what the items say.

* The construction needs data that `(F, δ)` alone does not determine: a ball radius and a Step 5
  cover. The radius is taken to be the outer scale `w₁`, matching
  `ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate`, where both are the tube radius `ρ`.
  Hence `outerFactoringFamily` takes `δ`, `w₁` with `δ ≤ w₁ ≤ 1`, positivity of `δ`, and the
  inner discretization hypothesis; the items inherit those arguments.
* Step 0 discards the inner bodies of low relative shading, so the output inner set is *not*
  `{i ∈ 𝒱 | parent i ∈ 𝒲'}`. It is that set intersected with the Step 0 survivors. The old
  condition of the second clause of `outerFactoringFamily_carrier` is false for the pipeline
  and has been corrected to name `F.step0.innerSet`.
* The placeholder value `1` for a loss constant is generally *not* a value at which the
  corresponding item is true. Where an item is proved, its constant now carries the real value.
  Where an item is still open, the docstring says explicitly whether the current placeholder
  makes it false.

Status of the seven items of GWZ Proposition 5.1:

| item | statement | status |
| ---- | --------- | ------ |
| structural | `outerFactoringFamily_carrier` | proved |
| 1 | `outerFactoringFamily_refinement` | proved |
| 2 | `outerFactoringFamily_lambda` | proved, `ℝ³`-only, at honest loss, from explicit hypotheses |
| 3 | `outerFactoringFamily_outerConstMultFat` | proved, for the dyadically refined outer shading |
| 4 | `outerFactoringFamily_innerConstMult` | proved |
| 5 | `outerFactoringFamily_multDominated` | proved, at honest loss, from explicit hypotheses |
| 6 | `outerFactoringFamily_shadingContainment` | proved |
| 7 | `outerFactoringFamily_avgMultOnBalls` | proved |

All seven constant comparisons are now proved. In particular
`outerFactoringFamily_refinement.one_leApprox_c` holds: the honest Item 1 loss
`outerFactoringFamily_refinement.c` is subpolynomial in `δ⁻¹` for fixed `n` and `N ≥ 1`. It is
assembled from the lemmas immediately above it (`leApprox_one_mul`,
`leApprox_one_const`, `factoringStep1AtScaleConstant_leApprox_one`,
`factoringStep5SelfPigeonholeConstant_packing_leApprox_one`, `one_le_step5PackingRatio`) through
`Kakeya.one_leApprox_inv`.

No placeholder loss constant remains. `outerFactoringFamily_outerConstMultFat.C` used to be `1`,
a value at which the item was false; it is now `2`, and it is the factor of a dyadic multiplicity
band, exactly as for Item 4. Item 3 asserts constant multiplicity not for `Y_{𝒲'}` itself — for
which no value of `C n δ` is correct, the outer pointwise multiplicity ratio being controlled by
`|𝒲|` and by no per-body geometry — but for the dyadic refinement
`ShadedBody.outerFactoringOuterRefined` of `Y_{𝒲'}` by its own multiplicity level. That extra
pigeonholing is the construction step GWZ performs and Steps 0-5 of
`Kakeya/Factoring/Pipeline.lean` do not; its cost is the new logarithmic loss
`outerFactoringFamily_outerConstMultFat.c`. It touches only the outer shading, so the constants of
Items 1, 2, 4, 5, 6 and 7 are unchanged.

`outerFactoringFamily_multDominated.C` is no longer a placeholder: it is
`4 * (Step 1 · Steps 2-3 · Step 5) * outerShadingPackingLoss n 6`, the assembled pipeline loss
times the general packing loss of `ShadedBody.le_multiplicity_of_local_balls`. Its constant
comparison `outerFactoringFamily_multDominated.C_leApprox_one` — joint subpolynomiality in `δ⁻¹`
and in `|𝒱|` — is proved at that honest value, not at the placeholder.

`outerFactoringFamily_lambda.c` is no longer a placeholder either: it is the reciprocal Córdoba
loss `(max 1 (lambdaForInducedShading.C N))⁻¹`, and its second argument `N` is now the
eccentricity exponent rather than the inner cardinality.

The outer shaded bodies of the construction are exactly the induced shadings of GWZ
Definition 5.7, by `outerFactoringFamily_outerBody_eq_inducedShading`. That identification is the
link to the `ℝ³` density estimates of `Kakeya/DimensionThree/InducedShading.lean`, which are
stated for arbitrary convex outer bodies; see the docstring of `outerFactoringFamily_lambda`. -/

@[expose] public section

open MeasureTheory Convexity Kakeya
open scoped ENNReal NNReal

namespace ShadedBody

section FactoringAndMultiplicity

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι κ : Type*} [DecidableEq κ]

/-- The Step 5 selection centres used by `ShadedBody.outerFactoringFamily`: the second finite set
produced by `ShadedBody.exists_factoringPipelineSelf` at ball radius `w₁`.

This is a `Classical.choice` of an existential, so it has no computational content; its defining
properties are exactly the conclusion of `ShadedBody.exists_factoringPipelineSelf`, reachable by
`Exists.choose_spec` since the definition is a literal `.choose_spec.choose`. -/
noncomputable def outerFactoringCover (F : FactorFamily E ι κ) {δ w₁ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (hw₁ : w₁ ∈ Set.Icc δ 1) :
    Finset E :=
  (exists_factoringPipelineSelf F hδ hdisc (w₁ : ℝ)
    (NNReal.coe_pos.mpr (hδ.trans_le hw₁.1))
    (F.measurableSet_pipelineSet hδ hdisc (w₁ : ℝ)
      (NNReal.coe_pos.mpr (hδ.trans_le hw₁.1)))
    (hδ.trans_le hw₁.1)).choose_spec.choose

/-- **Outer factoring family of shaded convex bodies** (blueprint `def:outerFactoringFamily`),
the construction underlying GWZ Proposition 5.1.

The input `F` packages the shaded inner family `𝒱`, the unshaded outer family `𝒲`, and the
chosen parent in `𝒲` of each member of `𝒱`.

The construction is the complete Step 0 - Step 5 factoring pipeline
`ShadedBody.FactorFamily.pipelineFamily`, run at ball radius `r = w₁` with the Step 5 selection
centres `ShadedBody.outerFactoringCover`. Its outer set is the Step 1 subfamily `𝒲' ⊆ 𝒲`, its
outer bodies package the induced shading `Y_{𝒲'}` on the enlargements `N_{r j} (W j)`, and its
inner bodies package the refinement `(𝒱', Y')`. It uses the same index types and parent map as
`F`, and its inner set consists of the Step 0 survivors whose parents belong to `𝒲'`.

The outer scale `w₁` is genuine data, not a convenience: Steps 2 and 5 both localize at a ball
radius, and the ball estimate `outerFactoringFamily_avgMultOnBalls` is about exactly that radius.
The hypothesis `δ ≤ w₁ ≤ 1` is what makes the Step 5 cover cardinality controllable by
`ShadedBody.step5PackingRatio`, and hence the refinement loss of `outerFactoringFamily_refinement`
explicit. -/
noncomputable def outerFactoringFamily (F : FactorFamily E ι κ) {δ w₁ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (hw₁ : w₁ ∈ Set.Icc δ 1) :
    ShadedFactorFamily E ι κ :=
  F.pipelineFamily hδ hdisc (w₁ : ℝ) (NNReal.coe_pos.mpr (hδ.trans_le hw₁.1))
    (F.measurableSet_pipelineSet hδ hdisc (w₁ : ℝ)
      (NNReal.coe_pos.mpr (hδ.trans_le hw₁.1)))
    (outerFactoringCover F hδ hdisc hw₁) w₁

/-- The outer index subfamily `𝒲' ⊆ 𝒲` produced by `outerFactoringFamily`. -/
noncomputable def outerFactoringIndex (F : FactorFamily E ι κ) {δ w₁ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (hw₁ : w₁ ∈ Set.Icc δ 1) : Finset κ :=
  (outerFactoringFamily F hδ hdisc hw₁).outerSet

/-- The shaded outer family `(𝒲', Y_{𝒲'})` produced by `outerFactoringFamily`. -/
noncomputable def outerFactoringOuterShaded (F : FactorFamily E ι κ) {δ w₁ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (hw₁ : w₁ ∈ Set.Icc δ 1) :
    κ → ShadedBody E :=
  (outerFactoringFamily F hδ hdisc hw₁).outerBody

/-- The refined inner shaded family `(𝒱', Y')` produced by `outerFactoringFamily`. -/
noncomputable def outerFactoringInner (F : FactorFamily E ι κ) {δ w₁ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (hw₁ : w₁ ∈ Set.Icc δ 1) :
    ι → ShadedBody E :=
  (outerFactoringFamily F hδ hdisc hw₁).innerBody

/-- Structural properties of `outerFactoringFamily` (dimension-free): the outer index set is a
subfamily of `𝒲`; the output inner set consists of the Step 0 survivors over that subfamily; the
parent map is unchanged; the output inner shaded bodies carry the original inner convex bodies;
and the output outer shaded bodies carry the *enlargements* `N_{r j} (W j)` of the original outer
convex bodies, with `r j = (W j).scale`.

Two clauses deserve comment.

The inner clause names `F.step0.innerSet`, not `F.innerSet`. Step 0 of the construction discards
the inner bodies whose relative shading is below half the family average
(`ShadedBody.FactorFamily.step0`), so the output inner set is a proper subset of
`{i ∈ 𝒱 | parent i ∈ 𝒲'}` in general and the equality with `F.innerSet` in its place is false.

The outer clause names the enlargement rather than `F.outerBody j` itself. This is forced by the
construction: Step 4 gives the outer shaded body the carrier
`(F.outerBody j).cthickening (F.outerBody j).scale`, because the `shade_subset` field of a
`ShadedBody` fails for the carrier `F.outerBody j` (see `ShadedBody.step4OuterBody` and
`ShadedBody.toConvexSpaceBody_step4OuterBody`), and Step 5 inherits that carrier rather than
undoing it. Stated with `F.outerBody j` on the right the clause is false. -/
theorem outerFactoringFamily_carrier (F : FactorFamily E ι κ) {δ w₁ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (hw₁ : w₁ ∈ Set.Icc δ 1) :
    (outerFactoringFamily F hδ hdisc hw₁).outerSet ⊆ F.outerSet ∧
    (outerFactoringFamily F hδ hdisc hw₁).innerSet ⊆ F.innerSet ∧
    ((outerFactoringFamily F hδ hdisc hw₁).innerSet =
      {i ∈ F.step0.innerSet |
        F.parent i ∈ (outerFactoringFamily F hδ hdisc hw₁).outerSet}) ∧
    (outerFactoringFamily F hδ hdisc hw₁).parent = F.parent ∧
    (∀ j : κ, ((outerFactoringFamily F hδ hdisc hw₁).outerBody j).toConvexSpaceBody =
      (F.outerBody j).cthickening (F.outerBody j).scale) ∧
    (∀ i : ι, ((outerFactoringFamily F hδ hdisc hw₁).innerBody i).toConvexSpaceBody =
      (F.innerBody i).toConvexSpaceBody) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [outerFactoringFamily] using
      F.pipelineFamily_outerSet_subset hδ hdisc (w₁ : ℝ)
        (NNReal.coe_pos.mpr (hδ.trans_le hw₁.1))
        (F.measurableSet_pipelineSet hδ hdisc (w₁ : ℝ)
          (NNReal.coe_pos.mpr (hδ.trans_le hw₁.1)))
        (outerFactoringCover F hδ hdisc hw₁) w₁
  · rw [show (outerFactoringFamily F hδ hdisc hw₁).innerSet = F.pipelineInnerSet hδ hdisc by
        simp [outerFactoringFamily]]
    rw [FactorFamily.pipelineInnerSet]
    exact (Finset.filter_subset (fun i : ι => F.parent i ∈ (F.step1 hδ hdisc).outerSet)
      F.step0.innerSet).trans F.innerSet_step0_subset
  · rfl
  · simp [outerFactoringFamily]
  · simp [outerFactoringFamily]
  · simp [outerFactoringFamily]

/-- The product of two functions that are each `⪅ 1` is `⪅ 1`: split `ε` into `ε / 2 + ε / 2`
and use `ρ ^ (-ε/2) * ρ ^ (-ε/2) = ρ ^ (-ε)`. -/
lemma leApprox_one_mul {X Y : NNReal → NNReal} (hX : X ⪅ fun _ : NNReal => (1 : NNReal))
    (hY : Y ⪅ fun _ : NNReal => (1 : NNReal)) :
    (fun ρ : NNReal => X ρ * Y ρ) ⪅ fun _ : NNReal => (1 : NNReal) := by
  intro ε hε
  have hε2 : 0 < ε / 2 := by positivity
  obtain ⟨C₁, hC₁⟩ := hX (ε / 2) hε2
  obtain ⟨C₂, hC₂⟩ := hY (ε / 2) hε2
  refine ⟨C₁ * C₂, ?_⟩
  intro ρ hρ hρ1
  simp only [mul_one]
  have h₁ : X ρ ≤ C₁ * ρ ^ (-(ε / 2)) := by simpa using hC₁ ρ hρ hρ1
  have h₂ : Y ρ ≤ C₂ * ρ ^ (-(ε / 2)) := by simpa using hC₂ ρ hρ hρ1
  have hstep1 : X ρ * Y ρ ≤ (C₁ * ρ ^ (-(ε / 2))) * Y ρ :=
    mul_le_mul_of_nonneg_right h₁ (by positivity)
  have hstep2 : (C₁ * ρ ^ (-(ε / 2))) * Y ρ ≤
      (C₁ * ρ ^ (-(ε / 2))) * (C₂ * ρ ^ (-(ε / 2))) :=
    mul_le_mul_of_nonneg_left h₂ (by positivity)
  calc
    X ρ * Y ρ ≤ (C₁ * ρ ^ (-(ε / 2))) * (C₂ * ρ ^ (-(ε / 2))) := hstep1.trans hstep2
    _ = C₁ * C₂ * (ρ ^ (-(ε / 2)) * ρ ^ (-(ε / 2))) := by ring
    _ = C₁ * C₂ * ρ ^ (-ε) := by
      congr 1
      rw [← NNReal.rpow_add' (by linarith : -(ε / 2) + -(ε / 2) ≠ (0 : ℝ)) ρ]
      congr 1
      ring
    _ = (C₁ * C₂) * ρ ^ (-ε) := by ring

/-- The logarithm of a ratio bounded by a power of `ρ⁻¹` is `⪅ 1`: the power version of
`Kakeya.toNNReal_logb_div_leApprox_one`, where the hypothesis reads `b ρ / a ρ ≲ (ρ⁻¹) ^ m`
instead of `b ρ / a ρ ≲ ρ⁻¹`. The `m`-fold logarithmic loss splits pointwise into the constant
`log₂ C₀` plus `m * log₂ (1 / ρ)`, and the latter is absorbed by
`Kakeya.toNNReal_logb_inv_leApprox_one` up to the constant factor `(m : ℝ≥0)`. -/
lemma toNNReal_logb_div_leApprox_one_pow {a b : NNReal → NNReal} {m : ℕ}
    (hratio : (fun ρ => b ρ / a ρ) ≲ fun ρ : NNReal => (ρ⁻¹) ^ m) :
    (fun ρ => Real.toNNReal (Real.logb 2 ((b ρ : ℝ) / (a ρ : ℝ)))) ⪅
      fun _ : NNReal => (1 : NNReal) := by
  obtain ⟨C₀, hC₀⟩ := hratio
  refine Kakeya.LEApprox.mono_left
    (X' := fun ρ : NNReal => Real.toNNReal (Real.logb 2 (C₀ : ℝ))
      + (m : NNReal) * Real.toNNReal (Real.logb 2 (1 / (ρ : ℝ))))
    ((Kakeya.toNNReal_logb_inv_leApprox_one.const_mul_one (m : NNReal)).const_add_one
      (Real.toNNReal (Real.logb 2 (C₀ : ℝ))))
    ?_
  intro ρ hρ hρ1
  have hab : b ρ / a ρ ≤ C₀ * (ρ⁻¹) ^ m := hC₀ ρ hρ hρ1
  have hdeg : b ρ / a ρ = 0 ∨ C₀ = 0 →
      Real.toNNReal (Real.logb 2 ((b ρ : ℝ) / (a ρ : ℝ))) = 0 := by
    intro h
    have hba0 : b ρ / a ρ = 0 :=
      h.elim id fun hC₀z => nonpos_iff_eq_zero.mp (by rwa [hC₀z, zero_mul] at hab)
    rw [← NNReal.coe_div (b ρ) (a ρ)]
    simp [hba0]
  rcases eq_or_ne (b ρ / a ρ) 0 with hba | hba
  · simp [hdeg (Or.inl hba)]
  rcases eq_or_ne C₀ 0 with hC₀z | hC₀nz
  · simp [hdeg (Or.inr hC₀z)]
  have hx : 0 < (b ρ : ℝ) / (a ρ : ℝ) := by
    simpa using (NNReal.coe_pos.mpr (pos_of_ne_zero hba) : 0 < ((b ρ / a ρ : NNReal) : ℝ))
  have hC : 0 < (C₀ : ℝ) := NNReal.coe_pos.mpr (pos_of_ne_zero hC₀nz)
  have hρr : 0 < (ρ : ℝ) := by exact_mod_cast hρ
  have hbound : (b ρ : ℝ) / (a ρ : ℝ) ≤ (C₀ : ℝ) * ((ρ : ℝ)⁻¹) ^ m := by
    simpa using (NNReal.coe_le_coe.mpr hab : ((b ρ / a ρ : NNReal) : ℝ) ≤
      ((C₀ * (ρ⁻¹) ^ m : NNReal) : ℝ))
  have hlog : Real.logb 2 ((b ρ : ℝ) / (a ρ : ℝ))
      ≤ Real.logb 2 (C₀ : ℝ) + m * Real.logb 2 (1 / (ρ : ℝ)) := by
    calc
      Real.logb 2 ((b ρ : ℝ) / (a ρ : ℝ))
          ≤ Real.logb 2 ((C₀ : ℝ) * ((ρ : ℝ)⁻¹) ^ m) :=
            Real.logb_le_logb_of_le (by norm_num) hx hbound
      _ = Real.logb 2 (C₀ : ℝ) + Real.logb 2 (((ρ : ℝ)⁻¹) ^ m) := by
            rw [Real.logb_mul hC.ne' (pow_ne_zero m (inv_ne_zero hρr.ne'))]
      _ = Real.logb 2 (C₀ : ℝ) + m * Real.logb 2 ((ρ : ℝ)⁻¹) := by
            rw [Real.logb_pow (2 : ℝ) ((ρ : ℝ)⁻¹) m]
      _ = Real.logb 2 (C₀ : ℝ) + m * Real.logb 2 (1 / (ρ : ℝ)) := by
            rw [one_div]
  have hmul : Real.toNNReal ((m : ℝ) * Real.logb 2 (1 / (ρ : ℝ))) =
      (m : NNReal) * Real.toNNReal (Real.logb 2 (1 / (ρ : ℝ))) := by
    have h := Real.toNNReal_mul (p := (m : ℝ)) (q := Real.logb 2 (1 / (ρ : ℝ)))
      (by positivity : 0 ≤ (m : ℝ))
    simpa using h
  calc
    Real.toNNReal (Real.logb 2 ((b ρ : ℝ) / (a ρ : ℝ)))
        ≤ Real.toNNReal (Real.logb 2 (C₀ : ℝ) + m * Real.logb 2 (1 / (ρ : ℝ))) :=
          Real.toNNReal_mono hlog
    _ ≤ Real.toNNReal (Real.logb 2 (C₀ : ℝ)) +
          Real.toNNReal (m * Real.logb 2 (1 / (ρ : ℝ))) :=
          Real.toNNReal_add_le
    _ = Real.toNNReal (Real.logb 2 (C₀ : ℝ)) +
          (m : NNReal) * Real.toNNReal (Real.logb 2 (1 / (ρ : ℝ))) := by
          rw [hmul]

/-- The Step 1 pigeonhole constant `2 * (1 + log₂ (b ρ / a ρ))₊` is `⪅ 1` when
`b ρ / a ρ ≲ (ρ⁻¹) ^ m`, the power version of `Kakeya.factoringStep1PigeonholeConstant_leApprox_one`.
As there, the two upgrades along the way are `Kakeya.LEApprox.const_add_one` with `c = 1` and
`Kakeya.LEApprox.const_mul_one` with `k = 2`, and the subadditivity of the positive part is
`Real.toNNReal_add_le`. -/
lemma factoringStep1PigeonholeConstant_leApprox_one_pow {a b : NNReal → NNReal} {m : ℕ}
    (hratio : (fun ρ => b ρ / a ρ) ≲ fun ρ : NNReal => (ρ⁻¹) ^ m) :
    (fun ρ => Kakeya.factoringStep1PigeonholeConstant (a ρ) (b ρ)) ⪅
      fun _ : NNReal => (1 : NNReal) := by
  refine Kakeya.LEApprox.mono_left
    (X' := fun ρ : NNReal => 2 * (1 + Real.toNNReal (Real.logb 2 ((b ρ : ℝ) / (a ρ : ℝ)))))
    (((toNNReal_logb_div_leApprox_one_pow hratio).const_add_one 1).const_mul_one 2)
    fun ρ _ _ => ?_
  have hfiber : Kakeya.factoringStep1FiberPigeonholeConstant (a ρ) (b ρ) =
      Real.toNNReal (1 + Real.logb 2 ((b ρ : ℝ) / (a ρ : ℝ))) := by
    rw [← ENNReal.coe_inj]
    rw [Kakeya.coe_factoringStep1FiberPigeonholeConstant]
    rfl
  have hpig : Kakeya.factoringStep1PigeonholeConstant (a ρ) (b ρ) =
      2 * Real.toNNReal (1 + Real.logb 2 ((b ρ : ℝ) / (a ρ : ℝ))) := by
    rw [← inv_inv (Kakeya.factoringStep1PigeonholeConstant (a ρ) (b ρ))]
    rw [← Kakeya.factoringStep1PigeonholeConstant_inv (a ρ) (b ρ)]
    rw [hfiber]
    simp
    ring
  rw [hpig]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : NNReal) ≤ 2)
  simpa using
    Real.toNNReal_add_le (r := (1 : ℝ)) (p := Real.logb 2 ((b ρ : ℝ) / (a ρ : ℝ)))

/-- The constant function `k` is `⪅ 1`: take `C := k` and absorb the `ρ ^ (-ε) ≥ 1` loss. -/
lemma leApprox_one_const (k : NNReal) :
    (fun _ : NNReal => k) ⪅ fun _ : NNReal => (1 : NNReal) := by
  intro ε hε
  exact ⟨k, fun ρ hρ hρ1 => by
    simpa using
      mul_le_mul_of_nonneg_left (Kakeya.one_le_rpow_neg hε.le hρ hρ1)
        (by positivity : (0 : NNReal) ≤ k)⟩

/-- The packing ratio is at least `1` on the intended domain `0 < δ ≤ 1`. -/
private lemma one_le_step5PackingRatio (n N : ℕ) {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (1 : NNReal) ≤ step5PackingRatio n N δ := by
  rw [step5PackingRatio, mul_div_assoc,
    Kakeya.step1UpperBdAtScale_div_step1LowerBdAtScale n (max 1 N) hδ]
  have hfact : (1 : NNReal) ≤ n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hN : (1 : NNReal) ≤ max 1 N := by exact_mod_cast le_max_left 1 N
  have hinv : (1 : NNReal) ≤ (δ ^ n)⁻¹ := by
    rw [one_le_inv₀ (pow_pos hδ n)]
    exact pow_le_one₀ δ.coe_nonneg hδ1
  calc
    1 ≤ (2 : NNReal) ^ n := one_le_pow₀ (by norm_num)
    _ ≤ 2 ^ n * (2 ^ n * 1 * 1 * 1) := by
      simpa using le_mul_of_one_le_right (by positivity : (0 : NNReal) ≤ 2 ^ n)
        (one_le_pow₀ (by norm_num : (1 : NNReal) ≤ 2))
    _ ≤ 2 ^ n * (2 ^ n * n.factorial * max 1 N * (δ ^ n)⁻¹) := by gcongr

/-- The self-pigeonholed Step 5 loss, evaluated at the packing bound for the cover, is
subpolynomial in `δ⁻¹` for fixed `n` and `N`. -/
private lemma factoringStep5SelfPigeonholeConstant_packing_leApprox_one (n N : ℕ) :
    (fun δ : NNReal =>
        ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n (step5PackingRatio n N δ)) ⪅
      fun _ : NNReal => (1 : NNReal) := by
  have hrewrite : ∀ M : NNReal,
      ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n M =
        (4 * (Kakeya.factoringStep5OverlapConstant n : NNReal)) *
          Kakeya.factoringStep1PigeonholeConstant 1 M := by
    intro M
    unfold ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant
    have hpMul : Kakeya.factoringStep1PigeonholeConstant 1 M =
        2 * Kakeya.factoringStep1FiberPigeonholeConstant 1 M := by
      rw [← inv_inv (Kakeya.factoringStep1PigeonholeConstant 1 M)]
      rw [← Kakeya.factoringStep1PigeonholeConstant_inv (1 : NNReal) M]
      rw [mul_inv, inv_inv, inv_inv]
    rw [hpMul]
  have hratio : (fun ρ : NNReal => step5PackingRatio n N ρ / (1 : NNReal))
      ≲ fun ρ : NNReal => (ρ⁻¹) ^ n := by
    let C : NNReal := 2 ^ n * (2 ^ n * (n.factorial : NNReal) * (max 1 N : ℕ))
    refine ⟨C, ?_⟩
    intro ρ hρ hρ1
    change step5PackingRatio n N ρ / 1 ≤ C * (ρ⁻¹) ^ n
    rw [div_one, step5PackingRatio, mul_div_assoc,
      Kakeya.step1UpperBdAtScale_div_step1LowerBdAtScale n (max 1 N) hρ, inv_pow]
    exact le_of_eq (by ring)
  have hpig : (fun ρ : NNReal => Kakeya.factoringStep1PigeonholeConstant 1
      (step5PackingRatio n N ρ)) ⪅ fun _ : NNReal => (1 : NNReal) :=
    factoringStep1PigeonholeConstant_leApprox_one_pow (a := fun _ : NNReal => (1 : NNReal))
      (b := fun ρ : NNReal => step5PackingRatio n N ρ) (m := n) hratio
  exact Kakeya.LEApprox.mono_left
    (hpig.const_mul_one (4 * (Kakeya.factoringStep5OverlapConstant n : NNReal)))
    (fun δ _ _ => le_of_eq (hrewrite (step5PackingRatio n N δ)))

/-- The Step 1 pigeonholing loss at scale `δ` is subpolynomial in `δ⁻¹` for fixed `n` and
`N ≥ 1`. -/
private lemma factoringStep1AtScaleConstant_leApprox_one (n : ℕ) {N : ℕ} (hN : 0 < N) :
    (fun δ : NNReal => Kakeya.factoringStep1AtScaleConstant n N δ) ⪅
      fun _ : NNReal => (1 : NNReal) := by
  have h1 : 1 ≤ N := Nat.succ_le_of_lt hN
  have hratio : (fun ρ : NNReal => Kakeya.step1UpperBdAtScale n N / Kakeya.step1LowerBdAtScale n ρ)
      ≲ fun ρ : NNReal => (ρ⁻¹) ^ n := by
    refine ⟨2 ^ n * (n.factorial : NNReal) * N, ?_⟩
    intro ρ hρ hρ1
    change Kakeya.step1UpperBdAtScale n N / Kakeya.step1LowerBdAtScale n ρ ≤
      2 ^ n * (n.factorial : NNReal) * N * (ρ⁻¹) ^ n
    rw [Kakeya.step1UpperBdAtScale_div_step1LowerBdAtScale n N hρ, inv_pow]
  have hlog : (fun δ : NNReal =>
      Real.toNNReal (Real.logb 2 ((Kakeya.step1UpperBdAtScale n N : ℝ) /
        (Kakeya.step1LowerBdAtScale n δ : ℝ)))) ⪅ fun _ : NNReal => (1 : NNReal) :=
    toNNReal_logb_div_leApprox_one_pow (a := fun ρ : NNReal => Kakeya.step1LowerBdAtScale n ρ)
      (b := fun _ : NNReal => Kakeya.step1UpperBdAtScale n N) (m := n) hratio
  exact Kakeya.LEApprox.mono_left
    ((hlog.const_add_one 1).const_mul_one 2)
    (fun δ hδ hδ1 => by
      rw [Kakeya.factoringStep1AtScaleConstant_eq n h1 hδ]
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : NNReal) ≤ 2)
      calc
        Real.toNNReal (1 + n + Real.logb 2 (n.factorial : ℝ) + Real.logb 2 N
            + n * Real.logb 2 (1 / (δ : ℝ)))
            = Real.toNNReal (1 + (n + Real.logb 2 (n.factorial : ℝ) + Real.logb 2 N
                + n * Real.logb 2 (1 / (δ : ℝ)))) := by
              congr 1
              ring
        _ ≤ 1 + Real.toNNReal (n + Real.logb 2 (n.factorial : ℝ) + Real.logb 2 N
            + n * Real.logb 2 (1 / (δ : ℝ))) := by
              simpa using
                Real.toNNReal_add_le (r := (1 : ℝ))
                  (p := n + Real.logb 2 (n.factorial : ℝ) + Real.logb 2 N
                    + n * Real.logb 2 (1 / (δ : ℝ)))
        _ = 1 + Real.toNNReal (Real.logb 2 ((Kakeya.step1UpperBdAtScale n N : ℝ) /
            (Kakeya.step1LowerBdAtScale n δ : ℝ))) := by
              rw [← Kakeya.logb_step1UpperBdAtScale_div_step1LowerBdAtScale n h1 hδ]
              simp [NNReal.coe_div])

/-- **Small constant in `ShadedBody.outerFactoringFamily_refinement`**: the retained mass
fraction of the complete pipeline, evaluated at the packing bound
`ShadedBody.step5PackingRatio` for the Step 5 cover. Its arguments record that the loss depends
on the ambient dimension, the cardinality of the inner family, and the discretization scale. -/
@[nolint defsWithUnderscore]
noncomputable def outerFactoringFamily_refinement.c (n N : ℕ) (δ : NNReal) : NNReal :=
  ShadedBody.Kakeya.factoringPipelineSelfRefinementConstant n N δ (step5PackingRatio n N δ)

/-- For fixed dimension and family cardinality, the small constant in Item 1 is bounded below by
`1` up to a subpolynomial factor in the discretization scale.

The hypothesis `0 < N` matches the repository convention for these constant comparisons (compare
`outerFactoringFamily_multDominated.C_leApprox_one`) and is not merely decorative here: the
closed form `Kakeya.factoringStep1AtScaleConstant_eq` of the Step 1 loss is stated for `1 ≤ N`,
and the Step 1 constants are not exposed across the module boundary, so the degenerate empty
inner family has no handle. It is also the only case of interest, `N` being `|𝒱|`. -/
theorem outerFactoringFamily_refinement.one_leApprox_c (n : ℕ) {N : ℕ} (hN : 0 < N) :
    (fun _ : NNReal ↦ (1 : NNReal)) ⪅
      fun δ : NNReal ↦ outerFactoringFamily_refinement.c n N δ := by
  let X : NNReal → NNReal := fun δ =>
    Kakeya.factoringStep1AtScaleConstant n N δ *
      ((Kakeya.factoringStep2Step3Constant N : ℕ) : NNReal) *
      ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n (step5PackingRatio n N δ)
  have hceq : ∀ δ : NNReal,
      outerFactoringFamily_refinement.c n N δ = (X δ)⁻¹ := by
    intro δ
    simp [outerFactoringFamily_refinement.c, X,
      ShadedBody.Kakeya.factoringPipelineSelfRefinementConstant]
    ring
  have hXapprox : X ⪅ fun _ : NNReal => (1 : NNReal) := by
    dsimp [X]
    exact leApprox_one_mul
      (leApprox_one_mul (factoringStep1AtScaleConstant_leApprox_one n hN)
        (leApprox_one_const ((Kakeya.factoringStep2Step3Constant N : ℕ) : NNReal)))
      (factoringStep5SelfPigeonholeConstant_packing_leApprox_one n N)
  have hN1 : 1 ≤ N := Nat.succ_le_of_lt hN
  have hB1 : (1 : NNReal) ≤ ((Kakeya.factoringStep2Step3Constant N : ℕ) : NNReal) := by
    rw [Kakeya.factoringStep2Step3Constant_eq]
    exact_mod_cast
      (Nat.succ_le_of_lt (by positivity : 0 < 4 * (Nat.log 2 N + 1) ^ 4))
  have hlow : ∀ δ : NNReal, 0 < δ → δ ≤ 1 → (1 : NNReal) ≤ X δ := by
    intro δ hδ hδ1
    have hA1 : (1 : NNReal) ≤ Kakeya.factoringStep1AtScaleConstant n N δ := by
      rw [Kakeya.factoringStep1AtScaleConstant_eq n hN1 hδ]
      have hfact1 : 1 ≤ n.factorial := Nat.succ_le_of_lt (Nat.factorial_pos n)
      have hfact1r : (1 : ℝ) ≤ (n.factorial : ℝ) := by exact_mod_cast hfact1
      have hN1r : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
      have hδr : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
      have hδr1 : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1
      have h1div : (1 : ℝ) ≤ 1 / (δ : ℝ) := by
        rw [one_le_div hδr]
        exact hδr1
      have hlogfact : 0 ≤ Real.logb 2 (n.factorial : ℝ) :=
        Real.logb_nonneg one_lt_two hfact1r
      have hlogN : 0 ≤ Real.logb 2 (N : ℝ) := Real.logb_nonneg one_lt_two hN1r
      have hloginv : 0 ≤ Real.logb 2 (1 / (δ : ℝ)) := Real.logb_nonneg one_lt_two h1div
      have hn : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.zero_le n
      have hnmul : 0 ≤ (n : ℝ) * Real.logb 2 (1 / (δ : ℝ)) := mul_nonneg hn hloginv
      have hbracket : (1 : ℝ) ≤ 1 + (n : ℝ) + Real.logb 2 (n.factorial : ℝ)
          + Real.logb 2 (N : ℝ) + (n : ℝ) * Real.logb 2 (1 / (δ : ℝ)) := by
        nlinarith
      have ht : (1 : NNReal) ≤ Real.toNNReal (1 + (n : ℝ) + Real.logb 2 (n.factorial : ℝ)
          + Real.logb 2 (N : ℝ) + (n : ℝ) * Real.logb 2 (1 / (δ : ℝ))) := by
        rw [Real.one_le_toNNReal]
        exact hbracket
      exact one_le_mul (by norm_num : (1 : NNReal) ≤ 2) ht
    have hpack1 : (1 : NNReal) ≤ step5PackingRatio n N δ :=
      one_le_step5PackingRatio n N hδ hδ1
    have hFiber : (1 : NNReal) ≤
        Kakeya.factoringStep1FiberPigeonholeConstant 1 (step5PackingRatio n N δ) :=
      Kakeya.one_le_factoringStep1FiberPigeonholeConstant hpack1
    have hOver : (1 : NNReal) ≤ (Kakeya.factoringStep5OverlapConstant n : NNReal) := by
      unfold Kakeya.factoringStep5OverlapConstant
      exact_mod_cast (Nat.succ_le_of_lt (by positivity : 0 < (5 : ℕ) ^ n))
    have hC1 : (1 : NNReal) ≤
        ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n (step5PackingRatio n N δ) := by
      unfold ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant
      exact one_le_mul (one_le_mul (by norm_num : (1 : NNReal) ≤ 4) hOver)
        (one_le_mul (by norm_num : (1 : NNReal) ≤ 2) hFiber)
    dsimp [X]
    exact one_le_mul (one_le_mul hA1 hB1) hC1
  have hfun : (fun δ : NNReal => outerFactoringFamily_refinement.c n N δ) =
      fun δ => (X δ)⁻¹ := funext hceq
  rw [hfun]
  exact Kakeya.one_leApprox_inv (X := X) (c := 1) hXapprox (by norm_num) hlow

/-- The cover cardinality is controlled by the explicit ratio used in the Step 5 loss. -/
private lemma card_le_step5PackingRatio {T : Finset E} {N : ℕ} {δ ρ : NNReal}
    (hδ : 0 < δ) (hρ : ρ ∈ Set.Icc δ 1)
    (hTsub : (T : Set E) ⊆ Metric.closedBall 0 1)
    (hTsep : Metric.IsSeparated (ρ : ENNReal) (T : Set E)) :
    (T.card : NNReal) ≤ step5PackingRatio (Module.finrank ℝ E) N δ := by
  let n := Module.finrank ℝ E
  have hpack := Metric.card_le_of_isSeparated_subset_closedBall (T := T) (hδ.trans_le hρ.1)
    (x := (0 : E)) (R := 1) (by norm_num) hTsub hTsep
  have hρr : (0 : ℝ) < (ρ : ℝ) := by exact_mod_cast hδ.trans_le hρ.1
  have hδr : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  have hbase : 2 * (1 + (ρ : ℝ)) / (ρ : ℝ) ≤ 4 / (δ : ℝ) := by
    rw [div_le_div_iff₀ hρr hδr]
    have hδρ : (δ : ℝ) ≤ (ρ : ℝ) := by exact_mod_cast hρ.1
    have hρ1 : (ρ : ℝ) ≤ 1 := by exact_mod_cast hρ.2
    have hρ0 : (0 : ℝ) ≤ ρ := hρr.le
    nlinarith
  have hcard : (T.card : ℝ) ≤ (4 / (δ : ℝ)) ^ n :=
    hpack.trans (pow_le_pow_left₀ (by positivity) hbase n)
  rw [← NNReal.coe_le_coe]
  push_cast
  calc
    (T.card : ℝ) ≤ (4 / (δ : ℝ)) ^ n := hcard
    _ ≤ (step5PackingRatio n N δ : ℝ) := by
      rw [step5PackingRatio, mul_div_assoc,
        Kakeya.step1UpperBdAtScale_div_step1LowerBdAtScale n (max 1 N) hδ]
      push_cast
      rw [div_pow]
      have hfact : (1 : ℝ) ≤ n.factorial := by exact_mod_cast Nat.factorial_pos n
      have hN : (1 : ℝ) ≤ max 1 (N : ℝ) := le_max_left _ _
      have hinv : 0 ≤ ((δ : ℝ) ^ n)⁻¹ := by positivity
      rw [div_eq_mul_inv]
      calc
        (4 : ℝ) ^ n * ((δ : ℝ) ^ n)⁻¹ =
            ((2 : ℝ) ^ n * 2 ^ n) * ((δ : ℝ) ^ n)⁻¹ := by
              rw [← mul_pow]
              norm_num
        _ ≤ ((2 : ℝ) ^ n * 2 ^ n) *
            ((n.factorial : ℝ) * max 1 (N : ℝ) * ((δ : ℝ) ^ n)⁻¹) := by
              gcongr
              calc
                ((δ : ℝ) ^ n)⁻¹ = 1 * 1 * ((δ : ℝ) ^ n)⁻¹ := by ring
                _ ≤ (n.factorial : ℝ) * max 1 (N : ℝ) * ((δ : ℝ) ^ n)⁻¹ := by
                  gcongr
        _ = (2 : ℝ) ^ n *
            ((2 : ℝ) ^ n * n.factorial * max 1 (N : ℝ) * ((δ : ℝ) ^ n)⁻¹) := by ring

/-- Monotonicity of the self-pigeonholing loss in a cardinality upper bound. -/
private lemma step5SelfPigeonholeConstant_mono {n : ℕ} {M M' : NNReal}
    (hM : M ≤ M') (hM' : 1 ≤ M') :
    ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n M ≤
      ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n M' := by
  unfold ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant
  gcongr
  rw [← ENNReal.coe_le_coe]
  rw [Kakeya.coe_factoringStep1FiberPigeonholeConstant,
    Kakeya.coe_factoringStep1FiberPigeonholeConstant]
  apply ENNReal.ofReal_le_ofReal
  by_cases hM0 : M = 0
  · subst M
    have hlog : 0 ≤ Real.logb 2 (M' : ℝ) :=
      Real.logb_nonneg one_lt_two (by exact_mod_cast hM')
    simp only [NNReal.coe_zero, NNReal.coe_one, div_one, Real.logb_zero, add_zero]
    exact le_add_of_nonneg_right hlog
  · gcongr
    norm_num

omit [Nontrivial E] in
private lemma isCRefinement_mono {s u : Finset ι} {V' V : ι → ShadedBody E} {c c' : NNReal}
    (h : IsCRefinement u V' s V c) (hc : c' ≤ c) :
    IsCRefinement u V' s V c' := by
  refine ⟨h.1, ?_⟩
  calc
    (c' : ENNReal) * ∑ i ∈ s, volume (V i).shade ≤
        (c : ENNReal) * ∑ i ∈ s, volume (V i).shade := by gcongr
    _ ≤ ∑ i ∈ u, volume (V' i).shade := h.2

/-- **Item 1** of GWZ Proposition 5.1
(`propFactoringAndMultPropCombinedRefinementItem`): `(𝒱', Y')` is a `⪆ 1` refinement of `(𝒱, Y)`.
The small refinement constant depends on the ambient dimension, the cardinality of the inner
family, and `δ`. -/
theorem outerFactoringFamily_refinement (F : FactorFamily E ι κ) {δ w₁ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (hw₁ : w₁ ∈ Set.Icc δ 1) :
    IsCRefinement (outerFactoringFamily F hδ hdisc hw₁).innerSet
      (outerFactoringFamily F hδ hdisc hw₁).innerBody F.innerSet F.innerBody
        (outerFactoringFamily_refinement.c
          (Module.finrank ℝ E) F.innerSet.card δ) := by
  let n := Module.finrank ℝ E
  let N := F.innerSet.card
  have hr : 0 < (w₁ : ℝ) := (NNReal.coe_pos.mpr (hδ.trans_le hw₁.1))
  have hΩ : MeasurableSet (F.pipelineSet hδ hdisc (w₁ : ℝ) hr) :=
    F.measurableSet_pipelineSet hδ hdisc (w₁ : ℝ) hr
  set hex := exists_factoringPipelineSelf F hδ hdisc (w₁ : ℝ) hr hΩ (hδ.trans_le hw₁.1)
  let T := hex.choose
  let T' := hex.choose_spec.choose
  obtain ⟨hTsub, hTsep, hTcover, hToverlap, hT'T, hT'pos, hT'sep, href₅, hballcomp⟩ :=
    hex.choose_spec.choose_spec
  have hTball : (T : Set E) ⊆ Metric.closedBall 0 1 := by
    refine hTsub.trans ?_
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
    have hiF : i ∈ F.innerSet := by
      rw [FactorFamily.pipelineInnerSet] at hi
      exact F.innerSet_step0_subset (Finset.mem_filter.mp hi).1
    apply hdisc.subset_unitBall i hiF
    have hxcarrier := (step3InnerBody F F.step0.innerSet (F.step1 hδ hdisc).outerSet
      (F.pipelineSet hδ hdisc (w₁ : ℝ) hr) hΩ
      (F.pipelineExponent hδ hdisc (w₁ : ℝ) hr) i).shade_subset hxi
    simpa using hxcarrier
  have hTcard : (T.card : NNReal) ≤ step5PackingRatio n N δ := by
    exact card_le_step5PackingRatio hδ hw₁ hTball hTsep
  have hratio1 : (1 : NNReal) ≤ step5PackingRatio n N δ := by
    rw [step5PackingRatio, mul_div_assoc,
      Kakeya.step1UpperBdAtScale_div_step1LowerBdAtScale n (max 1 N) hδ]
    have hfact : (1 : NNReal) ≤ n.factorial := by exact_mod_cast Nat.factorial_pos n
    have hN : (1 : NNReal) ≤ max 1 N := by exact_mod_cast le_max_left 1 N
    have hδ1 : δ ≤ 1 := hw₁.1.trans hw₁.2
    have hinv : (1 : NNReal) ≤ (δ ^ n)⁻¹ := by
      rw [one_le_inv₀ (pow_pos hδ n)]
      exact pow_le_one₀ δ.coe_nonneg hδ1
    calc
      1 ≤ (2 : NNReal) ^ n := one_le_pow₀ (by norm_num)
      _ ≤ 2 ^ n * (2 ^ n * 1 * 1 * 1) := by
        simpa using le_mul_of_one_le_right (by positivity : (0 : NNReal) ≤ 2 ^ n)
          (one_le_pow₀ (by norm_num : (1 : NNReal) ≤ 2))
      _ ≤ 2 ^ n * (2 ^ n * n.factorial * max 1 N * (δ ^ n)⁻¹) := by gcongr
  have hselfpos : 0 < ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n T.card := by
    unfold ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant
    have hFpos : 0 < Kakeya.factoringStep1FiberPigeonholeConstant 1 T.card := by
      cases hcard : T.card with
      | zero =>
          have heq : Kakeya.factoringStep1FiberPigeonholeConstant 1 T.card = 1 := by
            rw [← ENNReal.coe_inj]
            rw [Kakeya.coe_factoringStep1FiberPigeonholeConstant]
            simp [hcard]
          simpa [hcard] using congrArg (fun q : NNReal ↦ 0 < q) heq |>.mpr zero_lt_one
      | succ m =>
          exact lt_of_lt_of_le zero_lt_one
            (Kakeya.one_le_factoringStep1FiberPigeonholeConstant
              (show (1 : NNReal) ≤ (m + 1 : ℕ) by exact_mod_cast Nat.succ_pos m))
    have hO : (0 : NNReal) < Kakeya.factoringStep5OverlapConstant n := by
      unfold Kakeya.factoringStep5OverlapConstant
      positivity
    exact mul_pos (mul_pos (by norm_num) hO) (mul_pos (by norm_num) hFpos)
  have hcoef :
      (ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n
        (step5PackingRatio n N δ))⁻¹ ≤
      (ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n T.card)⁻¹ :=
    inv_anti₀ hselfpos (step5SelfPigeonholeConstant_mono hTcard hratio1)
  have href₅' := isCRefinement_mono href₅ hcoef
  simpa [outerFactoringFamily, outerFactoringCover, outerFactoringFamily_refinement.c, n, N,
    hex, hr, hΩ, T, T'] using
    F.pipelineFamily_isCRefinementSelf hδ hdisc (w₁ : ℝ) hr hΩ T' w₁ href₅'

/-- **The outer shaded bodies of `outerFactoringFamily` are induced shadings** (GWZ Definition 5.7).
For every outer index, retained or not, the Step 5 outer shaded body is literally
`ShadedBody.inducedShading` of the output fiber on the *original* outer body `W j`: the carrier is
`N_{r j}(W j)` with `r j = (W j).scale` (compare `outerFactoringFamily_carrier`) and the shade is
`N_{2 r j}(U(𝒱'_W, Y')) ∩ N_{r j}(W j)`. No membership hypothesis on `j` is needed, because for
`j ∉ 𝒲'` both sides have empty fiber and hence empty shade.

This is the bridge to the `ℝ³` density machinery of `Kakeya/DimensionThree/InducedShading.lean`.
`ShadedBody.lambdaForInducedShading_of_measurable` bounds the shading mass of exactly this object
from below, for an *arbitrary* convex outer body, so the planar Córdoba input that Item 2 needs is
not confined to the `ρ`-tube setting. -/
theorem outerFactoringFamily_outerBody_eq_inducedShading (F : FactorFamily E ι κ) {δ w₁ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (hw₁ : w₁ ∈ Set.Icc δ 1) (j : κ) :
    (outerFactoringFamily F hδ hdisc hw₁).outerBody j =
      inducedShading ((outerFactoringFamily F hδ hdisc hw₁).fiber j)
        (outerFactoringFamily F hδ hdisc hw₁).innerBody (F.outerBody j) := by
  rfl

/-- **Small constant in `ShadedBody.outerFactoringFamily_lambda`**: the reciprocal of the
planar Córdoba loss `ShadedBody.lambdaForInducedShading.C N` of GWZ Lemma 5.9, clamped from below
so that the loss is never a gain.

**Signature change.** The second argument `N` is no longer the cardinality of the inner family.
It is the *eccentricity exponent* of the hypothesis `|W j| ≤ 2 ^ N · |V i|` in
`ShadedBody.lambdaForInducedShading_of_measurable`, which is the only place the loss comes from;
that exponent is genuine data of the statement and now appears as the hypothesis `hecc` of
`ShadedBody.outerFactoringFamily_lambda`. The inner cardinality does not enter: Item 2 is a
per-fiber density estimate and pays no pigeonholing loss on top of the density hypothesis it is
handed.

The outer `max 1` makes the constant nonzero with no positivity input about the assembled
absolute constant `lambdaInducedSingleWUniform.C`, exactly as the outer `max 1` of
`ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C` does there. -/
@[nolint defsWithUnderscore]
noncomputable def outerFactoringFamily_lambda.c
    (_n N : ℕ) (_δ : NNReal) : NNReal :=
  (max 1 (lambdaForInducedShading.C N))⁻¹

/-- For fixed dimension and eccentricity exponent, the small constant in Item 2 is bounded below
by `1` up to a subpolynomial factor in the discretization scale. It is in fact independent of the
discretization scale. -/
theorem outerFactoringFamily_lambda.one_leApprox_c (n N : ℕ) :
    (fun _ : NNReal ↦ (1 : NNReal)) ⪅
      fun δ : NNReal ↦ outerFactoringFamily_lambda.c n N δ := by
  intro ε hε
  let b : NNReal := max 1 (lambdaForInducedShading.C N)
  refine ⟨b, ?_⟩
  intro ρ hρ hρ1
  change (1 : NNReal) ≤ b * ρ ^ (-ε) * b⁻¹
  have hb1 : (1 : NNReal) ≤ b := le_max_left _ _
  have hbpos : 0 < b := lt_of_lt_of_le zero_lt_one hb1
  have hb0 : b ≠ 0 := hbpos.ne'
  have hρexp : (1 : NNReal) ≤ ρ ^ (-ε) := Kakeya.one_le_rpow_neg hε.le hρ hρ1
  have hinv_nonneg : (0 : NNReal) ≤ b⁻¹ := by positivity
  calc
    1 = b * b⁻¹ := (mul_inv_cancel₀ hb0).symm
    _ ≤ b * (ρ ^ (-ε) * b⁻¹) := by
      simpa using
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hρexp hinv_nonneg) hbpos.le
    _ = b * ρ ^ (-ε) * b⁻¹ := by rw [mul_assoc]

/-- **Every retained outer index of `outerFactoringFamily` has a nonempty output fiber.**

Step 1 only selects outer indices that occur as parents of Step 0 survivors
(`ShadedBody.FactorFamily.outerSet_step1_subset_image`), and the pipeline's inner set retains
exactly those Step 0 survivors whose parent is selected, so any survivor witnessing `j ∈ 𝒲'` is
itself in the output fiber over `j`. -/
private lemma outerFactoringFamily_fiber_nonempty (F : FactorFamily E ι κ) {δ w₁ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (hw₁ : w₁ ∈ Set.Icc δ 1)
    {j : κ} (hj : j ∈ (outerFactoringFamily F hδ hdisc hw₁).outerSet) :
    ((outerFactoringFamily F hδ hdisc hw₁).fiber j).Nonempty := by
  classical
  change j ∈ (F.step1 hδ hdisc).outerSet at hj
  obtain ⟨i, hi, hpi⟩ := Finset.mem_image.mp (F.outerSet_step1_subset_image hδ hdisc hj)
  refine ⟨i, ?_⟩
  simp [ShadedFactorFamily.fiber, outerFactoringFamily, FactorFamily.pipelineInnerSet, hpi, hj]
  simpa using hi

/-- **Item 2** of GWZ Proposition 5.1 (`propFactoringAndMultPropCombinedLambdaItem`):
`λ(𝒲', Y_{𝒲'}) ⪆ C⁻¹ · λ(𝒱, Y)²`. This is the only item special to `ℝ³` (hypothesis `hdim`);
it uses the planar Córdoba maximal function estimate via `lambdaForInducedShading`
(GWZ Remark 5.2).

The route is the identification `outerFactoringFamily_outerBody_eq_inducedShading`: the outer
shaded bodies of the construction are literally `ShadedBody.inducedShading` of the output fibers
on the original outer bodies, so `ShadedBody.lambdaForInducedShading_of_measurable`
(`Kakeya/DimensionThree/InducedShading.lean`) applies to the auxiliary factor family carrying the
output inner shadings over the *original* outer bodies, and produces the blockwise density bound
`a |W j| ≤ b |Y_{𝒲'} j|` that `ShadedBody.le_fullness_of_forall_mul_volume_carrier_le` turns into
the fullness bound `a / b`. That file imports nothing under `Kakeya/Factoring/`, so there is no
cycle. The nonempty-fiber hypothesis of the `ℝ³` estimate is discharged internally by
`outerFactoringFamily_fiber_nonempty`, and its positive-volume hypothesis by the inner
discretization `hdisc`.

**Statement change relative to the previous, false, condition.** The previous version asserted
the conclusion at the placeholder loss `1` from the hypotheses `hdim`, `hshape` and
`F.HasFrostmanFibers C` alone. That was false, and it was also unprovable for reasons beyond the
constant: three inputs that the `ℝ³` estimate needs are simply not supplied by the pipeline, and
each is now an explicit hypothesis.

* `hdens`, the per-body density of the *output* shades. Step 0 supplies
  `2⁻¹ · λ(𝒱, Y) · |V i| ≤ |Y i|` for the *original* inner shades
  (`ShadedBody.FactorFamily.pipelineFamily_originalDensity`), but Steps 3 and 5 cut those shades
  down and the pipeline then offers only the aggregate retention bound of Item 1, never a
  per-body one. The natural repair — a further `ShadedBody.discardLowShading` pass on the output
  inner family — does *not* work: discarding inner indices can empty an output fiber, and it also
  destroys the Frostman hypothesis, which is a *ratio* condition whose denominator is the total
  fiber mass and which therefore only passes to a subfamily at the extra cost of
  `ConvexSpaceBody.IsFrostmanIn.of_subset` (a mass-comparison input the pipeline does not
  provide). So the density of the output shades is imposed, not derived.
* `hFrostman`, Frostman-ness of the *output* fibers rather than of the fibers of `F`. For the same
  ratio reason the fibers of `F` being `C`-Frostman says nothing about the fibers of the output,
  which are strictly smaller index sets.
* `hecc`, the eccentricity exponent `N`. The loss `ShadedBody.lambdaForInducedShading.C N` is
  indexed by it, and it is now the second argument of `outerFactoringFamily_lambda.c`.

`hnd` is the usual nondegeneracy hypothesis of a fullness bound: with a null outer carrier the
right-hand side is `0` in `ℝ≥0∞` and no constant works. Compare
`ShadedBody.shadingMultiplicityEstimateForRhoTubesUndilated_lam`, which carries the same kind of
hypothesis for the same reason.

The loss is `outerFactoringFamily_lambda.c n N δ = (max 1 (lambdaForInducedShading.C N))⁻¹`, which
is the honest Córdoba loss and not a placeholder. -/
theorem outerFactoringFamily_lambda
    {C : ENNReal} {N : ℕ} (F : FactorFamily E ι κ) {δ w₁ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (hw₁ : w₁ ∈ Set.Icc δ 1)
    (hdim : Module.finrank ℝ E = 3)
    (hshape : F.InnerHasSimilarShape 2)
    (hFrostman : ∀ j ∈ (outerFactoringFamily F hδ hdisc hw₁).outerSet,
      ConvexSpaceBody.IsFrostmanIn ((outerFactoringFamily F hδ hdisc hw₁).fiber j)
        (fun i ↦ (F.innerBody i).toConvexSpaceBody) (F.outerBody j) C)
    (hdens : ∀ i ∈ (outerFactoringFamily F hδ hdisc hw₁).innerSet,
      (2⁻¹ : ENNReal) * (fullness F.innerSet F.innerBody : ENNReal) *
          volume (F.innerBody i).carrier
        ≤ volume ((outerFactoringFamily F hδ hdisc hw₁).innerBody i).shade)
    (hecc : ∀ j ∈ (outerFactoringFamily F hδ hdisc hw₁).outerSet,
      ∀ i ∈ (outerFactoringFamily F hδ hdisc hw₁).fiber j,
        volume (F.outerBody j).carrier ≤ 2 ^ N * volume (F.innerBody i).carrier)
    (hnd : ∑ j ∈ (outerFactoringFamily F hδ hdisc hw₁).outerSet,
        volume ((outerFactoringFamily F hδ hdisc hw₁).outerBody j).carrier ≠ 0) :
    C⁻¹ * (outerFactoringFamily_lambda.c (Module.finrank ℝ E) N δ : ENNReal)
        * (fullness F.innerSet F.innerBody : ENNReal) ^ 2
      ≤ (fullness (outerFactoringFamily F hδ hdisc hw₁).outerSet
          (outerFactoringFamily F hδ hdisc hw₁).outerBody : ENNReal) := by
  classical
  let G : ShadedFactorFamily E ι κ := outerFactoringFamily F hδ hdisc hw₁
  let lam : ENNReal := (fullness F.innerSet F.innerBody : ENNReal)
  let b : NNReal := max 1 (lambdaForInducedShading.C N)
  change C⁻¹ * (outerFactoringFamily_lambda.c (Module.finrank ℝ E) N δ : ENNReal) * lam ^ 2
    ≤ (fullness G.outerSet G.outerBody : ENNReal)
  obtain ⟨hout, hin, hinForm, hpar, houtCSB, hinCSB⟩ := outerFactoringFamily_carrier F hδ hdisc hw₁
  -- The auxiliary factor family with the *original* unshaded outer bodies, carrying the output
  -- inner shadings over the output inner set (GWZ Definition 5.7 identification).
  let H : FactorFamily E ι κ :=
    { innerSet := G.innerSet
      innerBody := G.innerBody
      outerSet := G.outerSet
      outerBody := F.outerBody
      parent := F.parent
      parent_mem := by
        intro i hi
        simpa [G, outerFactoringFamily] using G.parent_mem i hi
      inner_le_parent := by
        intro i hi
        calc
          (G.innerBody i).toConvexSpaceBody = (F.innerBody i).toConvexSpaceBody := by
            simp [G, outerFactoringFamily]
          _ ≤ F.outerBody (F.parent i) := F.inner_le_parent i (hin hi) }
  have hshape' : H.InnerHasSimilarShape 2 := by
    intro i hi i' hi'
    change Metric.thickness ℝ (F.innerBody i).carrier ≤
      (2 : ℝ) • Metric.thickness ℝ (F.innerBody i').carrier
    exact hshape i (hin hi) i' (hin hi')
  have hFrostman' : H.HasFrostmanFibers C := by
    intro j hj
    change ConvexSpaceBody.IsFrostmanIn (G.fiber j)
      (fun i => (F.innerBody i).toConvexSpaceBody) (F.outerBody j) C
    exact hFrostman j hj
  have hne' : ∀ j ∈ H.outerSet, (H.fiber j).Nonempty := by
    intro j hj
    simpa [H, G, outerFactoringFamily, FactorFamily.fiber, ShadedFactorFamily.fiber]
      using outerFactoringFamily_fiber_nonempty F hδ hdisc hw₁ hj
  have hVpos' : ∀ i ∈ H.innerSet, volume (H.innerBody i).carrier ≠ 0 := by
    intro i hi
    have hlb : (Metric.lt_volume_convexHull.c (Module.finrank ℝ E) : ENNReal) *
          (δ : ENNReal) ^ Module.finrank ℝ E ≤ volume (F.innerBody i).carrier := by
      exact Kakeya.le_volume_of_le_scale (V := fun k => (F.innerBody k).toConvexSpaceBody)
        (δ := δ)
        (fun k hk => hdisc.le_scale k (hin hk)) hi
    have hc0 : (Metric.lt_volume_convexHull.c (Module.finrank ℝ E) : ENNReal) ≠ 0 :=
      ENNReal.coe_ne_zero.mpr (Metric.lt_volume_convexHull.c_pos _).ne'
    have hδpow : (δ : ENNReal) ^ Module.finrank ℝ E ≠ 0 :=
      (ENNReal.pow_pos (ENNReal.coe_pos.mpr hδ) (Module.finrank ℝ E)).ne'
    have hprod : 0 < (Metric.lt_volume_convexHull.c (Module.finrank ℝ E) : ENNReal) *
        (δ : ENNReal) ^ Module.finrank ℝ E := ENNReal.mul_pos hc0 hδpow
    have hvol : volume (F.innerBody i).carrier ≠ 0 :=
      ne_of_gt (lt_of_lt_of_le hprod hlb)
    simpa [H, G, outerFactoringFamily] using hvol
  have hlam' : ∀ i ∈ H.innerSet,
      (2⁻¹ : ENNReal) * lam * volume (H.innerBody i).carrier ≤ volume (H.innerBody i).shade := by
    intro i hi
    simpa [H, G, lam, outerFactoringFamily] using hdens i hi
  have hN' : ∀ j ∈ H.outerSet, ∀ i ∈ H.fiber j,
      volume (H.outerBody j).carrier ≤ 2 ^ N * volume (H.innerBody i).carrier := by
    intro j hj i hi
    simpa [H, G, outerFactoringFamily, FactorFamily.fiber, ShadedFactorFamily.fiber]
      using hecc j hj i hi
  -- The ℝ³ estimate (GWZ Lemma 5.9) applied to the auxiliary family.
  have hblock0 : ∀ j ∈ G.outerSet,
      C⁻¹ * lam ^ 2 *
          volume ((F.outerBody j).cthickening (F.outerBody j).scale).carrier
        ≤ (lambdaForInducedShading.C N : ENNReal) *
          volume (inducedShading (s := G.fiber j) (V := G.innerBody) (F.outerBody j)).shade := by
    intro j hj
    have h := lambdaForInducedShading_of_measurable (F := H) (C := C) (lam := lam) (N := N)
      hdim hshape' hFrostman' hne' hVpos' hlam' hN' j hj
    simpa [H, G, outerFactoringFamily, FactorFamily.fiber, ShadedFactorFamily.fiber] using h
  -- Rewrite the carriers and shades through the induced-shading identification.
  have hblock : ∀ j ∈ G.outerSet,
      (C⁻¹ * lam ^ 2) * volume (G.outerBody j).carrier
        ≤ (b : ENNReal) * volume (G.outerBody j).shade := by
    intro j hj
    have hleft : volume ((F.outerBody j).cthickening (F.outerBody j).scale).carrier =
        volume (G.outerBody j).carrier := by
      rw [← houtCSB j]
    have hright : volume (inducedShading (s := G.fiber j) (V := G.innerBody) (F.outerBody j)).shade =
        volume (G.outerBody j).shade := by
      rw [← outerFactoringFamily_outerBody_eq_inducedShading F hδ hdisc hw₁ j]
    calc
      (C⁻¹ * lam ^ 2) * volume (G.outerBody j).carrier
          = C⁻¹ * lam ^ 2 * volume (G.outerBody j).carrier := by ring
      _ = C⁻¹ * lam ^ 2 *
              volume ((F.outerBody j).cthickening (F.outerBody j).scale).carrier := by
            rw [← hleft]
      _ ≤ (lambdaForInducedShading.C N : ENNReal) *
          volume (inducedShading (s := G.fiber j) (V := G.innerBody) (F.outerBody j)).shade :=
            hblock0 j hj
      _ = (lambdaForInducedShading.C N : ENNReal) * volume (G.outerBody j).shade := by
            rw [hright]
      _ ≤ (b : ENNReal) * volume (G.outerBody j).shade := by
            gcongr
            exact le_max_right 1 (lambdaForInducedShading.C N)
  -- Fullness bound from the blockwise density.
  have hb0 : b ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left 1 (lambdaForInducedShading.C N)))
  have hb0' : (b : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hb0
  have hbtop : (b : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hsumTop : (∑ j ∈ G.outerSet, volume (G.outerBody j).carrier) ≠ ⊤ := by
    intro h
    rcases ENNReal.sum_eq_top.1 h with ⟨j, hj, hf⟩
    exact (G.outerBody j).isCompact.measure_ne_top hf
  have hfull := le_fullness_of_forall_mul_volume_carrier_le (t := G.outerSet) (W := G.outerBody)
    (a := C⁻¹ * lam ^ 2) (b := (b : ENNReal)) hb0' hbtop hnd hsumTop hblock
  -- Arithmetic: the constant is the reciprocal of `b`.
  have hc_eq : (outerFactoringFamily_lambda.c (Module.finrank ℝ E) N δ : ENNReal) =
      ((b : NNReal) : ENNReal)⁻¹ := by
    rw [outerFactoringFamily_lambda.c]
    rw [ENNReal.coe_inv hb0]
  have hLHS : C⁻¹ * (outerFactoringFamily_lambda.c (Module.finrank ℝ E) N δ : ENNReal) * lam ^ 2 =
      (C⁻¹ * lam ^ 2) / (b : ENNReal) := by
    rw [hc_eq]
    rw [div_eq_mul_inv]
    ring
  rw [hLHS]
  exact hfull

/-- **Large constant in `ShadedBody.outerFactoringFamily_outerConstMultFat`**: the factor `2` of a
dyadic multiplicity band, exactly as for the inner families in
`ShadedBody.outerFactoringFamily_innerConstMult`.

This is an honest value, not a placeholder. The refined outer shading
`ShadedBody.outerFactoringOuterRefined` restricts `Y_{𝒲'}` to a single dyadic band
`{x | ⌊log₂ μ(𝒲', Y_{𝒲'})(x)⌋ = m}` of its *own* pointwise multiplicity, and on such a band the
multiplicity varies by strictly less than a factor `2`. -/
@[nolint defsWithUnderscore]
noncomputable def outerFactoringFamily_outerConstMultFat.C (_n : ℕ) (_δ : NNReal) : NNReal := 2

/-- The loss in Item 3 is subpolynomial in the discretization scale. -/
theorem outerFactoringFamily_outerConstMultFat.C_leApprox_one (n : ℕ) :
    (fun δ : NNReal ↦ outerFactoringFamily_outerConstMultFat.C n δ) ⪅
      fun _ : NNReal ↦ (1 : NNReal) := by
  intro ε hε
  exact ⟨2, fun ρ hρ hρ1 => by
    simp [outerFactoringFamily_outerConstMultFat.C, Kakeya.one_le_rpow_neg hε.le hρ hρ1]⟩

/-- **Small constant in `ShadedBody.outerFactoringFamily_outerConstMultFat`**: the fraction of the
outer shading mass retained by the extra dyadic pigeonholing of Item 3, namely
`(⌊log₂ |𝒲|⌋ + 1)⁻¹`, one over the number of dyadic multiplicity bands available to the outer
family.

Its arguments record the dependencies: the ambient dimension (not actually used, kept for
uniformity with the other loss constants of this file), the cardinality of the *input* outer family
`𝒲` — an upper bound for that of the Step 1 subfamily `𝒲'`, which is what the pigeonhole is run on
— and the discretization scale (not used: this loss is logarithmic in `|𝒲|` only). -/
@[nolint defsWithUnderscore]
noncomputable def outerFactoringFamily_outerConstMultFat.c (_n : ℕ) (M : ℕ) (_δ : NNReal) :
    NNReal :=
  ((Nat.log 2 M + 1 : ℕ) : NNReal)⁻¹

/-- For a fixed outer family cardinality, the small constant in Item 3 is bounded below by `1` up
to a subpolynomial factor in the discretization scale. It does not depend on `δ` at all, so this is
just positivity of `(⌊log₂ M⌋ + 1)⁻¹` together with `ρ ^ (-ε) ≥ 1` on `(0, 1]`. -/
theorem outerFactoringFamily_outerConstMultFat.one_leApprox_c (n M : ℕ) :
    (fun _ : NNReal ↦ (1 : NNReal)) ⪅
      fun δ : NNReal ↦ outerFactoringFamily_outerConstMultFat.c n M δ := by
  intro ε hε
  have hL : ((Nat.log 2 M + 1 : ℕ) : NNReal) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero (Nat.log 2 M)
  refine ⟨((Nat.log 2 M + 1 : ℕ) : NNReal), fun ρ hρ hρ1 ↦ ?_⟩
  simp only [outerFactoringFamily_outerConstMultFat.c]
  calc
    (1 : NNReal) ≤ ρ ^ (-ε) := Kakeya.one_le_rpow_neg hε.le hρ hρ1
    _ = ((Nat.log 2 M + 1 : ℕ) : NNReal) * ρ ^ (-ε) * ((Nat.log 2 M + 1 : ℕ) : NNReal)⁻¹ := by
        rw [mul_right_comm, mul_inv_cancel₀ hL, one_mul]

/-- **The dyadically refined outer shading of the outer factoring family**, the extra pigeonholing
step that GWZ Item 3 needs and that Steps 0-5 of `Kakeya/Factoring/Pipeline.lean` do not perform.

It is `ShadedBody.exists_constantMultiplicity_refinement` applied to the shaded outer family
`(𝒲', Y_{𝒲'})` of `ShadedBody.outerFactoringFamily`: each outer shade is intersected with a single
dyadic band `{x | ⌊log₂ μ(𝒲', Y_{𝒲'})(x)⌋ = m}` of the outer pointwise multiplicity, `m` chosen to
maximize the retained outer shading mass. The carriers, the outer index set `𝒲'`, the inner family
and the parent map are all unchanged; only the outer shades shrink.

This is a `Classical.choice` of an existential, so it has no computational content; its defining
properties are `ShadedBody.outerFactoringOuterRefined_spec`. -/
noncomputable def outerFactoringOuterRefined (F : FactorFamily E ι κ) {δ w₁ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (hw₁ : w₁ ∈ Set.Icc δ 1) :
    κ → ShadedBody E :=
  (exists_constantMultiplicity_refinement (outerFactoringFamily F hδ hdisc hw₁).outerSet
    (outerFactoringFamily F hδ hdisc hw₁).outerBody).choose

/-- The defining properties of `ShadedBody.outerFactoringOuterRefined`: it refines the outer
shading of `ShadedBody.outerFactoringFamily`, it has `2`-constant multiplicity, and it retains at
least a `(⌊log₂ |𝒲'|⌋ + 1)⁻¹` fraction of the outer shading mass. -/
theorem outerFactoringOuterRefined_spec (F : FactorFamily E ι κ) {δ w₁ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (hw₁ : w₁ ∈ Set.Icc δ 1) :
    IsRefinement (outerFactoringFamily F hδ hdisc hw₁).outerSet
        (outerFactoringOuterRefined F hδ hdisc hw₁)
        (outerFactoringFamily F hδ hdisc hw₁).outerSet
        (outerFactoringFamily F hδ hdisc hw₁).outerBody ∧
      HasCConstantMultiplicity (outerFactoringFamily F hδ hdisc hw₁).outerSet
        (outerFactoringOuterRefined F hδ hdisc hw₁) 2 ∧
      (∑ j ∈ (outerFactoringFamily F hδ hdisc hw₁).outerSet,
          volume ((outerFactoringFamily F hδ hdisc hw₁).outerBody j).shade)
        ≤ (Nat.log 2 (outerFactoringFamily F hδ hdisc hw₁).outerSet.card + 1) •
            ∑ j ∈ (outerFactoringFamily F hδ hdisc hw₁).outerSet,
              volume ((outerFactoringOuterRefined F hδ hdisc hw₁) j).shade :=
  (exists_constantMultiplicity_refinement (outerFactoringFamily F hδ hdisc hw₁).outerSet
    (outerFactoringFamily F hδ hdisc hw₁).outerBody).choose_spec

/-- **Item 3** of GWZ Proposition 5.1 (`propFactoringAndMultPropCombinedWConstMultItem`):
the outer shaded family has constant multiplicity, with loss depending only on the ambient
dimension and `δ`.

**The item is about the dyadically refined outer shading**
`ShadedBody.outerFactoringOuterRefined`, not about `Y_{𝒲'}` itself, and this is not a weakening
but the missing construction step. The conclusion is the conjunction of the two things GWZ asserts
at this point of the proof: `(𝒲', Y^m_{𝒲'})` is a `(⌊log₂ |𝒲|⌋ + 1)⁻¹`-refinement of
`(𝒲', Y_{𝒲'})` — so the extra pigeonholing costs exactly one more logarithmic factor, and nothing
of the outer family is thrown away beyond that — and it has `C`-constant multiplicity at the
honest value `C = 2`.

**Why the unrefined form is false, at `C = 1` and at every `C n δ`.** `HasCConstantMultiplicity`
compares the pointwise multiplicity at two arbitrary points of the outer shaded union; since that
multiplicity is at least `1` everywhere on the union, the statement forces an *upper* bound `C` on
the outer pointwise multiplicity, i.e. bounded overlap of the family `𝒲'`. Nothing in the input
data supplies one, and no hypothesis on the *geometry* of the outer bodies can, because
`FactorFamily.outerBody` is a map `κ → ConvexSpaceBody E` that is not required to be injective:
`M` copies of one body `W₁` under `M` distinct indices, together with one further body `W₂`
meeting `W₁` only in a set of measure zero, satisfy any scale, thickness or fatness hypothesis one
cares to impose on the bodies, while a point of `W₁` lies in `M` shades and a point of `W₂` lies in
one. The ratio is `M`, which is bounded by `|𝒲|` and by nothing depending on `n` and `δ` alone.
An earlier form of this item carried the hypotheses `F.OuterIsAtScale 2 w₁` and a fatness input on
the outer shades for this reason; they do not repair it, and since the statement above needs
neither, they have been dropped rather than left in place unused.

Compare `ShadedBody.outerFactoringFamily_multDominated` (Item 5), which needs the *opposite*
inequality — the average outer multiplicity bounded *below* by the pointwise dyadic level — and is
therefore closed by the packing estimate `ShadedBody.le_multiplicity_of_local_balls` rather than by
a pigeonhole.

**Scope.** Only the outer shading is refined here. The inner shadings of
`ShadedBody.outerFactoringFamily` are untouched, so Items 1, 2, 4, 5, 6 and 7 are unaffected and
keep their constants; in particular the Item 1 loss
`ShadedBody.outerFactoringFamily_refinement.c` is unchanged. Conversely, the shading-containment
Item 6 is *not* claimed for the pair (inner shading, refined outer shading): restoring it requires
intersecting the inner shades with the same dyadic band, which is a separate construction and a
separate loss. -/
theorem outerFactoringFamily_outerConstMultFat (F : FactorFamily E ι κ) {δ w₁ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (hw₁ : w₁ ∈ Set.Icc δ 1) :
    IsCRefinement (outerFactoringFamily F hδ hdisc hw₁).outerSet
        (outerFactoringOuterRefined F hδ hdisc hw₁)
        (outerFactoringFamily F hδ hdisc hw₁).outerSet
        (outerFactoringFamily F hδ hdisc hw₁).outerBody
        (outerFactoringFamily_outerConstMultFat.c
          (Module.finrank ℝ E) F.outerSet.card δ) ∧
      HasCConstantMultiplicity (outerFactoringFamily F hδ hdisc hw₁).outerSet
        (outerFactoringOuterRefined F hδ hdisc hw₁)
        (outerFactoringFamily_outerConstMultFat.C (Module.finrank ℝ E) δ) := by
  classical
  obtain ⟨href, hconst, hmass⟩ := outerFactoringOuterRefined_spec F hδ hdisc hw₁
  refine ⟨?_, ?_⟩
  · -- The extra pigeonholing loses at most the number of dyadic bands, `⌊log₂ |𝒲|⌋ + 1`.
    have hsub : (outerFactoringFamily F hδ hdisc hw₁).outerSet ⊆ F.outerSet :=
      (outerFactoringFamily_carrier F hδ hdisc hw₁).1
    have hcard : Nat.log 2 (outerFactoringFamily F hδ hdisc hw₁).outerSet.card + 1
        ≤ Nat.log 2 F.outerSet.card + 1 :=
      Nat.succ_le_succ (Nat.log_mono_right (Finset.card_le_card hsub))
    have hcast : ((Nat.log 2 (outerFactoringFamily F hδ hdisc hw₁).outerSet.card + 1 : ℕ) :
          ENNReal) ≤ ((Nat.log 2 F.outerSet.card + 1 : ℕ) : ENNReal) := by
      exact_mod_cast hcard
    have hmass' :
        (∑ j ∈ (outerFactoringFamily F hδ hdisc hw₁).outerSet,
            volume ((outerFactoringFamily F hδ hdisc hw₁).outerBody j).shade)
          ≤ ((((Nat.log 2 F.outerSet.card + 1 : ℕ) : NNReal)) : ENNReal) *
              ∑ j ∈ (outerFactoringFamily F hδ hdisc hw₁).outerSet,
                volume ((outerFactoringOuterRefined F hδ hdisc hw₁) j).shade := by
      refine hmass.trans ?_
      rw [nsmul_eq_mul]
      have : ((((Nat.log 2 F.outerSet.card + 1 : ℕ) : NNReal)) : ENNReal)
          = ((Nat.log 2 F.outerSet.card + 1 : ℕ) : ENNReal) := by
        simp
      rw [this]
      gcongr
    simpa [outerFactoringFamily_outerConstMultFat.c] using
      isCRefinement_of_isRefinement_of_sum_le _ _ _ _ href hmass'
  · simpa [outerFactoringFamily_outerConstMultFat.C] using hconst

/-- **Large constant in `ShadedBody.outerFactoringFamily_innerConstMult`**: the factor `2` of the
Step 2 dyadic window, which Steps 3 and 5 preserve. -/
@[nolint defsWithUnderscore]
noncomputable def outerFactoringFamily_innerConstMult.C (_n : ℕ) (_δ : NNReal) : NNReal := 2

/-- The loss in Item 4 is subpolynomial in the discretization scale. -/
theorem outerFactoringFamily_innerConstMult.C_leApprox_one (n : ℕ) :
    (fun δ : NNReal ↦ outerFactoringFamily_innerConstMult.C n δ) ⪅
      fun _ : NNReal ↦ (1 : NNReal) := by
  intro ε hε
  exact ⟨2, fun ρ hρ hρ1 => by
    simp [outerFactoringFamily_innerConstMult.C, Kakeya.one_le_rpow_neg hε.le hρ hρ1]⟩

/-- **Item 4** of GWZ Proposition 5.1 (`propFactoringAndMultPropCombinedVConstMultItem`):
for each `W ∈ 𝒲'`, `(𝒱'_W, Y')` has constant pointwise multiplicity `∼ μinner`, with `μinner`
the same for all `W ∈ 𝒲'`. The loss depends only on the ambient dimension and `δ`.

The witness is the Step 2 dyadic level `μinner = 2 ^ k`, `k` the inner exponent
`ShadedBody.FactorFamily.pipelineExponent`; the pointwise fiber multiplicity lies in
`[2 ^ k, 2 ^ (k + 1))` by `ShadedBody.FactorFamily.pipelineFamily_fiber_multiplicity`. -/
theorem outerFactoringFamily_innerConstMult (F : FactorFamily E ι κ) {δ w₁ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (hw₁ : w₁ ∈ Set.Icc δ 1) :
    ∃ μinner : NNReal, ∀ j ∈ (outerFactoringFamily F hδ hdisc hw₁).outerSet,
      ∀ x ∈ ⋃ i ∈ (outerFactoringFamily F hδ hdisc hw₁).fiber j,
          ((outerFactoringFamily F hδ hdisc hw₁).innerBody i).shade,
        (pointwiseMultiplicity ((outerFactoringFamily F hδ hdisc hw₁).fiber j)
            (outerFactoringFamily F hδ hdisc hw₁).innerBody x : NNReal)
            ≤ outerFactoringFamily_innerConstMult.C (Module.finrank ℝ E) δ * μinner ∧
        μinner ≤ outerFactoringFamily_innerConstMult.C (Module.finrank ℝ E) δ
            * (pointwiseMultiplicity ((outerFactoringFamily F hδ hdisc hw₁).fiber j)
                (outerFactoringFamily F hδ hdisc hw₁).innerBody x : NNReal) := by
  classical
  let G := outerFactoringFamily F hδ hdisc hw₁
  let hr : 0 < (w₁ : ℝ) := NNReal.coe_pos.mpr (hδ.trans_le hw₁.1)
  let hΩ : MeasurableSet (F.pipelineSet hδ hdisc (w₁ : ℝ) hr) :=
    F.measurableSet_pipelineSet hδ hdisc (w₁ : ℝ) hr
  let k := F.pipelineExponent hδ hdisc (w₁ : ℝ) hr
  refine ⟨(2 : NNReal) ^ k, ?_⟩
  intro j hj x hx
  let m := pointwiseMultiplicity (G.fiber j) G.innerBody x
  have hb := FactorFamily.pipelineFamily_fiber_multiplicity F hδ hdisc (w₁ : ℝ) hr hΩ
    (outerFactoringCover F hδ hdisc hw₁) w₁ (j := j) (x := x) hx
  constructor
  · have h1nat : m ≤ 2 ^ (k + 1) := le_of_lt hb.2
    have h1 : (m : NNReal) ≤ (2 : NNReal) ^ (k + 1) := by exact_mod_cast h1nat
    have h1' : (2 : NNReal) ^ (k + 1) = 2 * (2 : NNReal) ^ k := by
      rw [pow_succ, mul_comm]
    simpa [outerFactoringFamily_innerConstMult.C, G, k, m] using h1.trans h1'.le
  · have h2cast : (2 : NNReal) ^ k ≤ (m : NNReal) := by exact_mod_cast hb.1
    have hm2 : (m : NNReal) ≤ 2 * (m : NNReal) := by
      exact le_mul_of_one_le_left (by positivity) (by norm_num)
    have h2 : (2 : NNReal) ^ k ≤ 2 * (m : NNReal) := h2cast.trans hm2
    simpa [outerFactoringFamily_innerConstMult.C, G, k, m] using h2

/-- `Nat.log 2 N + 1` grows more slowly than any positive power of `N`, uniformly in `N ≥ 1`.

A copy of the `private` lemma of the same name in `Kakeya/Factoring/RhoTubes.lean`, which cannot
be cited from here. -/
private lemma natLog_succ_le_rpow : ∀ η : ℝ, 0 < η → ∃ B : NNReal, ∀ N : ℕ, 0 < N →
    ((Nat.log 2 N + 1 : ℕ) : NNReal) ≤ B * (N : NNReal) ^ η := by
  intro η hη
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let q : NNReal := ⟨1 / (η * Real.log 2), by positivity⟩
  refine ⟨1 + q, fun N hN ↦ ?_⟩
  have hN1 : (1 : NNReal) ≤ (N : NNReal) := by exact_mod_cast hN
  have hNpow : (1 : NNReal) ≤ (N : NNReal) ^ η := by
    simpa using NNReal.rpow_le_rpow hN1 hη.le
  have hlog : (Nat.log 2 N : ℝ) ≤ (N : ℝ) ^ η / (η * Real.log 2) := by
    calc
      (Nat.log 2 N : ℝ) ≤ Real.logb 2 N := Real.natLog_le_logb N 2
      _ = Real.log N / Real.log 2 := rfl
      _ ≤ ((N : ℝ) ^ η / η) / Real.log 2 := by
        gcongr
        exact Real.log_natCast_le_rpow_div N hη
      _ = (N : ℝ) ^ η / (η * Real.log 2) := by ring
  rw [← NNReal.coe_le_coe]
  push_cast [q, NNReal.coe_rpow]
  have hNpow' : (1 : ℝ) ≤ (N : ℝ) ^ η := by exact_mod_cast hNpow
  calc
    (Nat.log 2 N : ℝ) + 1 ≤ (N : ℝ) ^ η / (η * Real.log 2) + 1 := by linarith
    _ ≤ (N : ℝ) ^ η / (η * Real.log 2) + (N : ℝ) ^ η := by linarith
    _ = (1 + 1 / (η * Real.log 2)) * (N : ℝ) ^ η := by ring

/-- The Step 1 fiber pigeonholing loss is jointly subpolynomial in `δ⁻¹` and in `N`: one constant
works uniformly for all `N ≥ 1` and all `0 < δ ≤ 1`.

A copy of the `private` lemma of the same name in `Kakeya/Factoring/RhoTubes.lean`, which cannot
be cited from here. -/
private lemma fiberPigeonholeConstant_le_rpow (n : ℕ) :
    ∀ η : ℝ, 0 < η → ∃ A : NNReal, ∀ N : ℕ, 0 < N → ∀ δ : NNReal, 0 < δ → δ ≤ 1 →
      Kakeya.factoringStep1FiberPigeonholeConstant (Kakeya.step1LowerBdAtScale n δ)
          (Kakeya.step1UpperBdAtScale n N) ≤ A * δ ^ (-η) * (N : NNReal) ^ η := by
  intro η hη
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let q : ℝ := 1 / (η * Real.log 2)
  let a₀ : ℝ := 1 + n + Real.logb 2 (n.factorial : ℝ)
  have ha₀ : 0 ≤ a₀ := by
    have hfact : (1 : ℝ) ≤ n.factorial := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hlogfact : 0 ≤ Real.logb 2 (n.factorial : ℝ) :=
      Real.logb_nonneg one_lt_two hfact
    positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hA₀ : (0 : ℝ) ≤ (n : ℝ) * q := mul_nonneg (by positivity) hq
  refine ⟨⟨a₀ + q + n * q, by linarith⟩, fun N hN δ hδ hδ1 ↦ ?_⟩
  have hN1 : (1 : NNReal) ≤ (N : NNReal) := by exact_mod_cast hN
  have hNpow : (1 : NNReal) ≤ (N : NNReal) ^ η := by
    simpa using NNReal.rpow_le_rpow hN1 hη.le
  have hδpow : (1 : NNReal) ≤ δ ^ (-η) := Kakeya.one_le_rpow_neg hη.le hδ hδ1
  have hlogN : Real.logb 2 (N : ℝ) ≤ q * (N : ℝ) ^ η := by
    calc
      Real.logb 2 (N : ℝ) = Real.log N / Real.log 2 := rfl
      _ ≤ ((N : ℝ) ^ η / η) / Real.log 2 := by
        gcongr
        exact Real.log_natCast_le_rpow_div N hη
      _ = q * (N : ℝ) ^ η := by simp only [q]; ring
  have hlogδ : Real.logb 2 (1 / (δ : ℝ)) ≤ q * (δ : ℝ) ^ (-η) := by
    calc
      Real.logb 2 (1 / (δ : ℝ))
          ≤ (δ : ℝ) ^ (-η) / (η * Real.log 2) :=
        Kakeya.logb_inv_le_rpow_neg_div (by exact_mod_cast hδ) hη
      _ = q * (δ : ℝ) ^ (-η) := by simp only [q]; ring
  have hF :
      (Kakeya.factoringStep1FiberPigeonholeConstant (Kakeya.step1LowerBdAtScale n δ)
          (Kakeya.step1UpperBdAtScale n N) : ℝ) =
        a₀ + Real.logb 2 (N : ℝ) + n * Real.logb 2 (1 / (δ : ℝ)) := by
    have hratio := Kakeya.logb_step1UpperBdAtScale_div_step1LowerBdAtScale_nonneg n
      (Nat.one_le_iff_ne_zero.mpr hN.ne') hδ hδ1
    have h := congrArg ENNReal.toReal
      (Kakeya.coe_factoringStep1FiberPigeonholeConstant (Kakeya.step1LowerBdAtScale n δ)
        (Kakeya.step1UpperBdAtScale n N))
    rw [NNReal.coe_div] at hratio
    have hnonneg : 0 ≤ 1 + Real.logb 2
        ((Kakeya.step1UpperBdAtScale n N : ℝ) / (Kakeya.step1LowerBdAtScale n δ : ℝ)) := by
      linarith
    rw [ENNReal.toReal_ofReal hnonneg] at h
    simp only [ENNReal.coe_toReal] at h
    rw [h, ← NNReal.coe_div, Kakeya.logb_step1UpperBdAtScale_div_step1LowerBdAtScale n
      (Nat.one_le_iff_ne_zero.mpr hN.ne') hδ]
    simp only [a₀]
    ring
  rw [← NNReal.coe_le_coe]
  push_cast [NNReal.coe_rpow]
  rw [hF]
  have hNpow' : (1 : ℝ) ≤ (N : ℝ) ^ η := by exact_mod_cast hNpow
  have hδpow' : (1 : ℝ) ≤ (δ : ℝ) ^ (-η) := by exact_mod_cast hδpow
  calc
    a₀ + Real.logb 2 (N : ℝ) + n * Real.logb 2 (1 / (δ : ℝ))
        ≤ a₀ + q * (N : ℝ) ^ η + n * (q * (δ : ℝ) ^ (-η)) := by gcongr
    _ ≤ a₀ * (δ : ℝ) ^ (-η) * (N : ℝ) ^ η +
          q * (δ : ℝ) ^ (-η) * (N : ℝ) ^ η +
          n * q * (δ : ℝ) ^ (-η) * (N : ℝ) ^ η := by
      have ha₀term : a₀ ≤ a₀ * (δ : ℝ) ^ (-η) * (N : ℝ) ^ η := by
        calc
          a₀ = a₀ * 1 * 1 := by ring
          _ ≤ a₀ * (δ : ℝ) ^ (-η) * (N : ℝ) ^ η := by gcongr
      have hNterm : q * (N : ℝ) ^ η ≤
          q * (δ : ℝ) ^ (-η) * (N : ℝ) ^ η := by
        calc
          q * (N : ℝ) ^ η = q * 1 * (N : ℝ) ^ η := by ring
          _ ≤ q * (δ : ℝ) ^ (-η) * (N : ℝ) ^ η := by gcongr
      have hδterm : (n : ℝ) * (q * (δ : ℝ) ^ (-η)) ≤
          n * q * (δ : ℝ) ^ (-η) * (N : ℝ) ^ η := by
        calc
          (n : ℝ) * (q * (δ : ℝ) ^ (-η)) = n * q * (δ : ℝ) ^ (-η) * 1 := by ring
          _ ≤ n * q * (δ : ℝ) ^ (-η) * (N : ℝ) ^ η := by gcongr
      exact add_le_add (add_le_add ha₀term hNterm) hδterm
    _ = (a₀ + q + n * q) * (δ : ℝ) ^ (-η) * (N : ℝ) ^ η := by ring

/-- **Large constant in `ShadedBody.outerFactoringFamily_multDominated`**: the assembled Step 0 -
Step 5 pigeonholing loss of the pipeline, times the general outer packing loss of the
enlargements.

Reading the factors left to right:

* the factor `4` is the Step 2 pointwise window of
  `ShadedBody.FactorFamily.pipelineFamily_multiplicity`, which places the global inner
  multiplicity in `[2 ^ k * 2 ^ l, 4 * 2 ^ k * 2 ^ l)` for the inner exponent `k` and outer
  exponent `l`;
* the bracketed product is the reciprocal of the Item 1 refinement constant
  `ShadedBody.outerFactoringFamily_refinement.c`, i.e. exactly the mass the pipeline may discard;
* `ShadedBody.outerShadingPackingLoss n 6` is the purely dimensional loss of
  `ShadedBody.le_multiplicity_of_local_balls`, which converts the pointwise outer count `2 ^ l`
  into a lower bound for the *average* outer multiplicity. The covering radius is `6 * w₁`: a
  point of an outer shade lies within `2 * (W j).scale ≤ 4 * w₁` of the fiber shaded union, which
  in turn lies in the Step 5 selection, a union of closed `w₁`-balls around the cover centres.

Every factor is either dimensional or logarithmic in `N` and in `δ⁻¹`; this is what
`ShadedBody.outerFactoringFamily_multDominated.C_leApprox_one` records. -/
@[nolint defsWithUnderscore]
noncomputable def outerFactoringFamily_multDominated.C
    (n N : ℕ) (δ : NNReal) : NNReal :=
  4 * (Kakeya.factoringStep1AtScaleConstant n N δ *
      (Kakeya.factoringStep2Step3Constant N : NNReal) *
      ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n (step5PackingRatio n N δ)) *
    outerShadingPackingLoss n 6

/-- Closed form of the Item 5 loss on its intended domain: all four pigeonholing losses of the
pipeline expand into two Step 1 fiber losses, a fourth power of `Nat.log 2 N + 1`, and purely
dimensional factors. This is the analogue of the `private` lemma `factoringLoss_eq` of
`Kakeya/Factoring/RhoTubes.lean`.

The identity uses `Kakeya.step1UpperBdAtScale n K = 2 ^ n * K` to absorb the extra factor `2 ^ n`
of `ShadedBody.step5PackingRatio` into the second Step 1 loss, and `1 ≤ N` to remove the `max 1`
there. -/
private lemma multDominatedConstant_eq (n N : ℕ) (δ : NNReal) (hN : 0 < N) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) :
    outerFactoringFamily_multDominated.C n N δ =
      256 * (Kakeya.factoringStep5OverlapConstant n : NNReal) * outerShadingPackingLoss n 6 *
        Kakeya.factoringStep1FiberPigeonholeConstant (Kakeya.step1LowerBdAtScale n δ)
          (Kakeya.step1UpperBdAtScale n N) *
        Kakeya.factoringStep1FiberPigeonholeConstant (Kakeya.step1LowerBdAtScale n δ)
          (Kakeya.step1UpperBdAtScale n (2 ^ n * N)) *
        ((Nat.log 2 N + 1 : ℕ) : NNReal) ^ 4 := by
  have hN1 : 1 ≤ N := Nat.succ_le_of_lt hN
  have hfiber : Kakeya.factoringStep1FiberPigeonholeConstant 1 (step5PackingRatio n N δ) =
      Kakeya.factoringStep1FiberPigeonholeConstant (Kakeya.step1LowerBdAtScale n δ)
        (Kakeya.step1UpperBdAtScale n (2 ^ n * N)) := by
    have hratio : step5PackingRatio n N δ =
        Kakeya.step1UpperBdAtScale n (2 ^ n * N) / Kakeya.step1LowerBdAtScale n δ := by
      unfold step5PackingRatio
      rw [max_eq_right hN1]
      congr 1
      apply ENNReal.coe_injective
      rw [ENNReal.coe_mul, Kakeya.coe_step1UpperBdAtScale, Kakeya.coe_step1UpperBdAtScale]
      push_cast
      ring
    apply ENNReal.coe_injective
    rw [Kakeya.coe_factoringStep1FiberPigeonholeConstant,
      Kakeya.coe_factoringStep1FiberPigeonholeConstant]
    congr 2
    rw [hratio]
    push_cast
    norm_num
  have hlog₁ : Real.logb 2 ((Kakeya.step1UpperBdAtScale n N : ℝ) /
      (Kakeya.step1LowerBdAtScale n δ : ℝ)) =
      n + Real.logb 2 (n.factorial : ℝ) + Real.logb 2 (N : ℝ) +
        n * Real.logb 2 (1 / (δ : ℝ)) := by
    rw [← NNReal.coe_div]
    exact Kakeya.logb_step1UpperBdAtScale_div_step1LowerBdAtScale n hN1 hδ
  have hlognonneg : 0 ≤ Real.logb 2 ((Kakeya.step1UpperBdAtScale n N : ℝ) /
      (Kakeya.step1LowerBdAtScale n δ : ℝ)) := by
    have h := Kakeya.logb_step1UpperBdAtScale_div_step1LowerBdAtScale_nonneg n hN1 hδ hδ1
    rw [NNReal.coe_div] at h
    exact h
  have hF₁ : (Kakeya.factoringStep1FiberPigeonholeConstant (Kakeya.step1LowerBdAtScale n δ)
      (Kakeya.step1UpperBdAtScale n N) : ℝ) = 1 + Real.logb 2 ((Kakeya.step1UpperBdAtScale n N : ℝ) /
      (Kakeya.step1LowerBdAtScale n δ : ℝ)) := by
    have hF := congrArg ENNReal.toReal
      (Kakeya.coe_factoringStep1FiberPigeonholeConstant (Kakeya.step1LowerBdAtScale n δ)
        (Kakeya.step1UpperBdAtScale n N))
    have hnonneg : 0 ≤ 1 + Real.logb 2 ((Kakeya.step1UpperBdAtScale n N : ℝ) /
      (Kakeya.step1LowerBdAtScale n δ : ℝ)) := by
      linarith [hlognonneg]
    rw [ENNReal.toReal_ofReal hnonneg] at hF
    simpa only [ENNReal.coe_toReal] using hF
  have hWsum : 0 ≤ (n : ℝ) + Real.logb 2 (n.factorial : ℝ) + Real.logb 2 (N : ℝ)
      + (n : ℝ) * Real.logb 2 (1 / (δ : ℝ)) := by
    rw [← hlog₁]
    exact hlognonneg
  have hbracket : 0 ≤ 1 + (n : ℝ) + Real.logb 2 (n.factorial : ℝ) + Real.logb 2 (N : ℝ)
      + (n : ℝ) * Real.logb 2 (1 / (δ : ℝ)) := by
    linarith [hWsum]
  have hstep1 : Kakeya.factoringStep1AtScaleConstant n N δ =
      2 * Kakeya.factoringStep1FiberPigeonholeConstant (Kakeya.step1LowerBdAtScale n δ)
        (Kakeya.step1UpperBdAtScale n N) := by
    rw [Kakeya.factoringStep1AtScaleConstant_eq n hN1 hδ]
    congr 1
    apply NNReal.coe_injective
    rw [Real.coe_toNNReal]
    · rw [hF₁, hlog₁]
      ring
    · exact hbracket
  rw [outerFactoringFamily_multDominated.C]
  rw [ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant]
  rw [hfiber, hstep1, Kakeya.factoringStep2Step3Constant_eq]
  push_cast
  ring

/-- For fixed dimension, the loss in Item 5 is jointly subpolynomial in the inverse
discretization scale and in the inner-family cardinality: for every `ε > 0`, one constant works
uniformly for all `N ≥ 1` and `0 < δ ≤ 1`. -/
theorem outerFactoringFamily_multDominated.C_leApprox_one (n : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∃ Cε : NNReal, ∀ N : ℕ, 0 < N → ∀ δ : NNReal, 0 < δ → δ ≤ 1 →
      outerFactoringFamily_multDominated.C n N δ
        ≤ Cε * δ ^ (-ε) * (N : NNReal) ^ ε := by
  intro ε hε
  let η : ℝ := ε / 6
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨A, hA⟩ := fiberPigeonholeConstant_le_rpow n η hη
  obtain ⟨B, hB⟩ := natLog_succ_le_rpow η hη
  let q : NNReal := ((2 ^ n : ℕ) : NNReal) ^ η
  let Cε : NNReal :=
    256 * (Kakeya.factoringStep5OverlapConstant n : NNReal) * outerShadingPackingLoss n 6 *
      A ^ 2 * B ^ 4 * q
  refine ⟨Cε, ?_⟩
  intro N hN δ hδ hδ1
  rw [multDominatedConstant_eq n N δ hN hδ hδ1]
  have hF : Kakeya.factoringStep1FiberPigeonholeConstant (Kakeya.step1LowerBdAtScale n δ)
      (Kakeya.step1UpperBdAtScale n N) ≤ A * δ ^ (-η) * (N : NNReal) ^ η :=
    hA N hN δ hδ hδ1
  have hN' : 0 < 2 ^ n * N := by positivity
  have hF' : Kakeya.factoringStep1FiberPigeonholeConstant (Kakeya.step1LowerBdAtScale n δ)
      (Kakeya.step1UpperBdAtScale n (2 ^ n * N)) ≤
        A * δ ^ (-η) * ((2 ^ n * N : ℕ) : NNReal) ^ η :=
    hA (2 ^ n * N) hN' δ hδ hδ1
  have hL : ((Nat.log 2 N + 1 : ℕ) : NNReal) ≤ B * (N : NNReal) ^ η := hB N hN
  have hN'pow : (((2 ^ n * N : ℕ) : NNReal) ^ η) = q * (N : NNReal) ^ η := by
    simp only [Nat.cast_mul, q]
    rw [NNReal.mul_rpow]
  have hδexp : (δ ^ (-η)) ^ 2 ≤ δ ^ (-ε) := by
    rw [← NNReal.rpow_natCast, ← NNReal.rpow_mul]
    apply NNReal.rpow_le_rpow_of_exponent_ge hδ hδ1
    dsimp [η]
    linarith
  have hNexp : ((N : NNReal) ^ η) ^ 6 = (N : NNReal) ^ ε := by
    rw [← NNReal.rpow_natCast, ← NNReal.rpow_mul]
    congr 2
    dsimp [η]
    ring
  calc
    256 * (Kakeya.factoringStep5OverlapConstant n : NNReal) * outerShadingPackingLoss n 6 *
        Kakeya.factoringStep1FiberPigeonholeConstant (Kakeya.step1LowerBdAtScale n δ)
          (Kakeya.step1UpperBdAtScale n N) *
        Kakeya.factoringStep1FiberPigeonholeConstant (Kakeya.step1LowerBdAtScale n δ)
          (Kakeya.step1UpperBdAtScale n (2 ^ n * N)) *
        ((Nat.log 2 N + 1 : ℕ) : NNReal) ^ 4
        ≤ 256 * (Kakeya.factoringStep5OverlapConstant n : NNReal) * outerShadingPackingLoss n 6 *
            (A * δ ^ (-η) * (N : NNReal) ^ η) *
            (A * δ ^ (-η) * ((2 ^ n * N : ℕ) : NNReal) ^ η) *
            (B * (N : NNReal) ^ η) ^ 4 := by
          gcongr
    _ = Cε * (δ ^ (-η)) ^ 2 * ((N : NNReal) ^ η) ^ 6 := by
      simp only [Cε, hN'pow]
      ring
    _ ≤ Cε * δ ^ (-ε) * ((N : NNReal) ^ η) ^ 6 := by
      gcongr
    _ = Cε * δ ^ (-ε) * (N : NNReal) ^ ε := by rw [hNexp]

/-- The Step 5 cover of `ShadedBody.outerFactoringFamily` is `w₁`-separated. Second-to-last
conjunct of `ShadedBody.exists_factoringPipelineSelf`, read off the defining `choose_spec`. -/
private lemma outerFactoringCover_isSeparated (F : FactorFamily E ι κ) {δ w₁ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (hw₁ : w₁ ∈ Set.Icc δ 1) :
    Metric.IsSeparated (w₁ : ENNReal)
      ((outerFactoringCover F hδ hdisc hw₁ : Finset E) : Set E) := by
  have hr : 0 < (w₁ : ℝ) := NNReal.coe_pos.mpr (hδ.trans_le hw₁.1)
  have hΩ : MeasurableSet (F.pipelineSet hδ hdisc (w₁ : ℝ) hr) :=
    F.measurableSet_pipelineSet hδ hdisc (w₁ : ℝ) hr
  set hex := exists_factoringPipelineSelf F hδ hdisc (w₁ : ℝ) hr hΩ (hδ.trans_le hw₁.1)
  let T := hex.choose
  let T' := hex.choose_spec.choose
  obtain ⟨_, _, _, _, _, _, hT'sep, _, _⟩ := hex.choose_spec.choose_spec
  simpa [outerFactoringCover] using hT'sep

/-- Every centre of the Step 5 cover of `ShadedBody.outerFactoringFamily` carries positive
selected inner mass in its own `w₁`-ball. Sixth conjunct of
`ShadedBody.exists_factoringPipelineSelf`, read off the defining `choose_spec`. -/
private lemma outerFactoringCover_volume_ne_zero (F : FactorFamily E ι κ) {δ w₁ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (hw₁ : w₁ ∈ Set.Icc δ 1) :
    ∀ c ∈ outerFactoringCover F hδ hdisc hw₁,
      volume (iUnionShade (outerFactoringFamily F hδ hdisc hw₁).innerSet
        (outerFactoringFamily F hδ hdisc hw₁).innerBody ∩ Metric.closedBall c (w₁ : ℝ)) ≠ 0 := by
  have hr : 0 < (w₁ : ℝ) := NNReal.coe_pos.mpr (hδ.trans_le hw₁.1)
  have hΩ : MeasurableSet (F.pipelineSet hδ hdisc (w₁ : ℝ) hr) :=
    F.measurableSet_pipelineSet hδ hdisc (w₁ : ℝ) hr
  set hex := exists_factoringPipelineSelf F hδ hdisc (w₁ : ℝ) hr hΩ (hδ.trans_le hw₁.1)
  obtain ⟨_, _, _, _, _, hT'pos, _, _, _⟩ := hex.choose_spec.choose_spec
  intro c hc
  simpa [outerFactoringFamily, outerFactoringCover] using
    hT'pos c (by simpa [outerFactoringCover] using hc)

/-- The outer shaded union of `ShadedBody.outerFactoringFamily` is covered by the closed
`6 * w₁`-balls around the Step 5 cover centres.

The radius is `6 * w₁ = 4 * w₁ + w₁ + w₁`: a point of an outer shade lies in the
`2 * (W j).scale`-thickening of the fiber shaded union, and `(W j).scale ≤ 2 * w₁` by `hscale`,
so it is within `5 * w₁` of a point of that union, which lies in the Step 5 selection, a union of
closed `w₁`-balls around the cover centres. -/
private lemma outerFactoringFamily_outerShade_subset_cover (F : FactorFamily E ι κ)
    {δ w₁ : NNReal} (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ)
    (hw₁ : w₁ ∈ Set.Icc δ 1) (hscale : F.OuterIsAtScale 2 w₁) :
    iUnionShade (outerFactoringFamily F hδ hdisc hw₁).outerSet
        (outerFactoringFamily F hδ hdisc hw₁).outerBody ⊆
      ⋃ z ∈ outerFactoringCover F hδ hdisc hw₁,
        Metric.closedBall z (((6 : ℕ) : ℝ) * (w₁ : ℝ)) := by
  classical
  let hr : 0 < (w₁ : ℝ) := NNReal.coe_pos.mpr (hδ.trans_le hw₁.1)
  let hΩ : MeasurableSet (F.pipelineSet hδ hdisc (w₁ : ℝ) hr) :=
    F.measurableSet_pipelineSet hδ hdisc (w₁ : ℝ) hr
  let T' : Finset E := outerFactoringCover F hδ hdisc hw₁
  let u : Finset ι := F.step0.innerSet
  let t' : Finset κ := (F.step1 hδ hdisc).outerSet
  let Ω : Set E := F.pipelineSet hδ hdisc (w₁ : ℝ) hr
  let k : ℕ := F.pipelineExponent hδ hdisc (w₁ : ℝ) hr
  intro y hy
  change y ∈ ⋃ j ∈ t', (step5OuterBody F F.innerSet_step0_subset t' Ω hΩ k T' w₁ j).shade at hy
  rcases Set.mem_iUnion₂.mp hy with ⟨j, hjt', hyj⟩
  have hjF : j ∈ F.outerSet :=
    F.pipelineFamily_outerSet_subset hδ hdisc (w₁ : ℝ) hr hΩ T' w₁ hjt'
  let U' : Set E := iUnionShade {i ∈ u | F.parent i = j}
    (step5InnerBody F u t' Ω hΩ k T' w₁)
  rw [shade_step5OuterBody_eq F F.innerSet_step0_subset t' Ω hΩ k T' w₁ hjt'] at hyj
  have hy2 : y ∈ Metric.cthickening (2 * (F.outerBody j).scale) U' := hyj.2
  have hscale_le : (F.outerBody j).scale ≤ 2 * (w₁ : ℝ) := by
    simpa [ConvexSpaceBody.scale] using (hscale j hjF).1
  have hradius : 2 * (F.outerBody j).scale ≤ 4 * (w₁ : ℝ) := by nlinarith
  have hy4 : y ∈ Metric.cthickening (4 * (w₁ : ℝ)) U' :=
    Metric.cthickening_mono hradius U' hy2
  have hthick : y ∈ ⋃ x ∈ U', Metric.closedBall x (5 * (w₁ : ℝ)) :=
    (Metric.cthickening_subset_iUnion_closedBall_of_lt U'
      (show (0 : ℝ) < 5 * (w₁ : ℝ) by positivity)
      (show 4 * (w₁ : ℝ) < 5 * (w₁ : ℝ) by linarith)) hy4
  obtain ⟨z, hzU', hyz⟩ := Set.mem_iUnion₂.mp hthick
  obtain ⟨i, hiU, hzi⟩ := Set.mem_iUnion₂.mp hzU'
  rw [shade_step5InnerBody] at hzi
  obtain ⟨z₀, hz₀, hzz₀⟩ := Set.mem_iUnion₂.mp hzi.2
  refine Set.mem_iUnion₂.mpr ⟨z₀, ?_, Metric.mem_closedBall.mpr ?_⟩
  · exact hz₀
  · calc
      dist y z₀ ≤ dist y z + dist z z₀ := dist_triangle _ _ _
      _ ≤ 5 * (w₁ : ℝ) + (w₁ : ℝ) := by
        gcongr
        · exact Metric.mem_closedBall.mp hyz
        · exact Metric.mem_closedBall.mp hzz₀
      _ = ((6 : ℕ) : ℝ) * (w₁ : ℝ) := by
        norm_num
        ring

/-- **Local fatness of the outer shades at the Step 5 cover centres.**

At every cover centre `z`, at least `2 ^ l` of the outer bodies of `outerFactoringFamily` have a
ball of radius `w₁ / 8` inside their shade and inside `Metric.ball z (2 * w₁)`, where `l` is the
Step 2 outer dyadic exponent `ShadedBody.FactorFamily.pipelineOuterExponent`.

This is the exact hypothesis of `ShadedBody.le_multiplicity_of_local_balls`. The count `2 ^ l`
comes from the third conjunct of `ShadedBody.FactorFamily.bounds_of_mem_pipelineSet`, and the fat
ball from `Kakeya.exists_ball_subset_cthickening_inter_ball` applied to the compact carrier
`(F.outerBody j).carrier`, whose closed `(F.outerBody j).scale`-neighbourhood is the carrier of
the outer body. That application needs `w₁ ≤ 2 * (F.outerBody j).scale`, which is the second
conjunct of `hscale`. -/
private lemma outerFactoringFamily_local_balls (F : FactorFamily E ι κ) {δ w₁ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (hw₁ : w₁ ∈ Set.Icc δ 1)
    (hscale : F.OuterIsAtScale 2 w₁) :
    ∀ z ∈ outerFactoringCover F hδ hdisc hw₁,
      ∃ J : Finset κ, J ⊆ (outerFactoringFamily F hδ hdisc hw₁).outerSet ∧
        2 ^ F.pipelineOuterExponent hδ hdisc (w₁ : ℝ)
            (NNReal.coe_pos.mpr (hδ.trans_le hw₁.1)) ≤ J.card ∧
        ∀ j ∈ J, ∃ p : E, Metric.ball p ((w₁ : ℝ) / 8) ⊆
          ((outerFactoringFamily F hδ hdisc hw₁).outerBody j).shade ∩
            Metric.ball z (2 * (w₁ : ℝ)) := by
  classical
  let hr : 0 < (w₁ : ℝ) := NNReal.coe_pos.mpr (hδ.trans_le hw₁.1)
  let hΩ : MeasurableSet (F.pipelineSet hδ hdisc (w₁ : ℝ) hr) :=
    F.measurableSet_pipelineSet hδ hdisc (w₁ : ℝ) hr
  let T' : Finset E := outerFactoringCover F hδ hdisc hw₁
  let u : Finset ι := F.step0.innerSet
  let t' : Finset κ := (F.step1 hδ hdisc).outerSet
  let Ω : Set E := F.pipelineSet hδ hdisc (w₁ : ℝ) hr
  let k : ℕ := F.pipelineExponent hδ hdisc (w₁ : ℝ) hr
  let l : ℕ := F.pipelineOuterExponent hδ hdisc (w₁ : ℝ) hr
  let G : ShadedFactorFamily E ι κ := outerFactoringFamily F hδ hdisc hw₁
  intro z hz
  let A : Set E := iUnionShade G.innerSet G.innerBody ∩ Metric.closedBall z (w₁ : ℝ)
  have hA0 : volume A ≠ 0 := by
    simpa [A, G, outerFactoringFamily] using outerFactoringCover_volume_ne_zero F hδ hdisc hw₁ z hz
  obtain ⟨y, hyA⟩ := MeasureTheory.nonempty_of_measure_ne_zero hA0
  have hyG : y ∈ iUnionShade G.innerSet G.innerBody := hyA.1
  obtain ⟨i₀, hi₀, hyi₀⟩ := Set.mem_iUnion₂.mp hyG
  have hyi₀' : y ∈ (step5InnerBody F u t' Ω hΩ k T' w₁ i₀).shade := by
    simpa [G, outerFactoringFamily, FactorFamily.pipelineFamily, u, t', Ω, k] using hyi₀
  rw [shade_step5InnerBody, shade_step3InnerBody] at hyi₀'
  have hyΩ : y ∈ F.pipelineSet hδ hdisc (w₁ : ℝ) hr := hyi₀'.1.1.2
  have hySel : y ∈ step5Selection T' w₁ := hyi₀'.2
  let J := MultiplicityFamily.dyadicLevel t'
    (fiberMultiplicity F {i ∈ u | F.parent i ∈ t'}) k y
  refine ⟨J, ?_, ?_, ?_⟩
  · intro q hq
    have hqt' : q ∈ t' := (Finset.mem_filter.mp hq).1
    have hqG : q ∈ G.outerSet := by
      simpa [G, outerFactoringFamily, FactorFamily.pipelineFamily, t'] using hqt'
    exact hqG
  · have hb := F.bounds_of_mem_pipelineSet hδ hdisc (w₁ : ℝ) hr hyΩ
    simpa [J, l, k, t', u, FactorFamily.pipelineInnerSet] using hb.2.2.1
  · intro q hq
    have hqt' : q ∈ t' := (Finset.mem_filter.mp hq).1
    have hpos : 0 < fiberMultiplicity F {i ∈ u | F.parent i ∈ t'} q y :=
      lt_of_lt_of_le (pow_pos (by omega) k) (Finset.mem_filter.mp hq).2.1
    change 0 < ({i ∈ {i ∈ {i ∈ u | F.parent i ∈ t'} | F.parent i = q} |
      y ∈ (F.innerBody i).shade}).card at hpos
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
    have hi' := Finset.mem_filter.mp hi
    have hib := Finset.mem_filter.mp hi'.1
    have hiu := (Finset.mem_filter.mp hib.1).1
    have hip := hib.2
    have hiF : i ∈ F.innerSet := F.innerSet_step0_subset hiu
    have hyK : y ∈ (F.outerBody q).carrier := by
      change y ∈ (F.outerBody q)
      simpa [hip] using (F.inner_le_parent i hiF) ((F.innerBody i).shade_subset hi'.2)
    have hqF : q ∈ F.outerSet := by
      exact F.pipelineFamily_outerSet_subset hδ hdisc (w₁ : ℝ) hr hΩ T' w₁ hqt'
    have hrs : (w₁ : ℝ) ≤ 2 * (F.outerBody q).scale := by
      simpa [ConvexSpaceBody.scale] using (hscale q hqF).2
    obtain ⟨p, hp⟩ := Kakeya.exists_ball_subset_cthickening_inter_ball
      (F.outerBody q).isCompact hr hrs
      (Metric.self_subset_cthickening (F.outerBody q).carrier hyK)
    refine ⟨p, ?_⟩
    intro w hw
    have hwK : w ∈ Metric.cthickening (F.outerBody q).scale (F.outerBody q).carrier := (hp hw).1
    have hyU : y ∈ iUnionShade {i ∈ u | F.parent i = q} (step5InnerBody F u t' Ω hΩ k T' w₁) := by
      refine Set.mem_iUnion₂.mpr ⟨i, ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨hiu, hip⟩
      · rw [shade_step5InnerBody, shade_step3InnerBody]
        refine ⟨⟨⟨hi'.2, hyΩ⟩, ?_⟩, hySel⟩
        simpa [step3DyadicSet, hip] using (Finset.mem_filter.mp hq).2
    have hwthick : w ∈ Metric.cthickening (2 * (F.outerBody q).scale)
        (iUnionShade {i ∈ u | F.parent i = q} (step5InnerBody F u t' Ω hΩ k T' w₁)) := by
      apply Metric.mem_cthickening_of_dist_le w y _ _ hyU
      exact le_trans (le_of_lt (Metric.mem_ball.mp (hp hw).2)) hrs
    constructor
    · change w ∈ (step5OuterBody F F.innerSet_step0_subset t' Ω hΩ k T' w₁ q).shade
      rw [shade_step5OuterBody_eq F F.innerSet_step0_subset t' Ω hΩ k T' w₁ hqt']
      exact ⟨hwK, hwthick⟩
    · apply Metric.mem_ball.mpr
      calc
        dist w z ≤ dist w y + dist y z := dist_triangle _ _ _
        _ < (w₁ : ℝ) + (w₁ : ℝ) := add_lt_add_of_lt_of_le
          (Metric.mem_ball.mp (hp hw).2) (Metric.mem_closedBall.mp hyA.2)
        _ = 2 * (w₁ : ℝ) := by ring

/-- **The outer average multiplicity dominates the Step 2 outer dyadic level.**

The packing step of Item 5: `ShadedBody.le_multiplicity_of_local_balls` applied to the Step 5
cover, at covering ratio `m = 6`. The nonemptiness of the cover is supplied by the caller, where
it follows from the nondegeneracy hypothesis of `outerFactoringFamily_multDominated`. -/
private lemma outerFactoringFamily_le_outerMultiplicity (F : FactorFamily E ι κ)
    {δ w₁ : NNReal} (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ)
    (hw₁ : w₁ ∈ Set.Icc δ 1) (hscale : F.OuterIsAtScale 2 w₁)
    (hne : (outerFactoringCover F hδ hdisc hw₁).Nonempty) :
    ((2 : ENNReal) ^ F.pipelineOuterExponent hδ hdisc (w₁ : ℝ)
        (NNReal.coe_pos.mpr (hδ.trans_le hw₁.1))) ≤
      (outerShadingPackingLoss (Module.finrank ℝ E) 6 : ENNReal) *
        multiplicity (outerFactoringFamily F hδ hdisc hw₁).outerSet
          (outerFactoringFamily F hδ hdisc hw₁).outerBody := by
  let l : ℕ := F.pipelineOuterExponent hδ hdisc (w₁ : ℝ)
    (NNReal.coe_pos.mpr (hδ.trans_le hw₁.1))
  simpa [Nat.cast_pow, l] using
    (le_multiplicity_of_local_balls
      (t := (outerFactoringFamily F hδ hdisc hw₁).outerSet)
      (V := (outerFactoringFamily F hδ hdisc hw₁).outerBody)
      (S := outerFactoringCover F hδ hdisc hw₁)
      (r := w₁)
      (L := 2 ^ l)
      (m := 6)
      (hr := hδ.trans_le hw₁.1)
      (hL := pow_pos (by norm_num) l)
      (hm := by norm_num)
      (hS := hne)
      (hsep := outerFactoringCover_isSeparated F hδ hdisc hw₁)
      (hcover := outerFactoringFamily_outerShade_subset_cover F hδ hdisc hw₁ hscale)
      (hlocal := outerFactoringFamily_local_balls F hδ hdisc hw₁ hscale))

/-- The Step 5 cover is nonempty as soon as one output fiber carries mass: the selected inner
shades all live in the union of the closed `w₁`-balls around the cover centres. -/
private lemma outerFactoringCover_nonempty (F : FactorFamily E ι κ) {δ w₁ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (hw₁ : w₁ ∈ Set.Icc δ 1) {j : κ}
    (hj : volume (⋃ i ∈ (outerFactoringFamily F hδ hdisc hw₁).fiber j,
      ((outerFactoringFamily F hδ hdisc hw₁).innerBody i).shade) ≠ 0) :
    (outerFactoringCover F hδ hdisc hw₁).Nonempty := by
  classical
  let hr : 0 < (w₁ : ℝ) := NNReal.coe_pos.mpr (hδ.trans_le hw₁.1)
  let hΩ : MeasurableSet (F.pipelineSet hδ hdisc (w₁ : ℝ) hr) :=
    F.measurableSet_pipelineSet hδ hdisc (w₁ : ℝ) hr
  let T : Finset E := outerFactoringCover F hδ hdisc hw₁
  obtain ⟨y, hy⟩ := MeasureTheory.nonempty_of_measure_ne_zero hj
  obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.mp hy
  have hyi' : y ∈ (step5InnerBody F F.step0.innerSet (F.step1 hδ hdisc).outerSet
      (F.pipelineSet hδ hdisc (w₁ : ℝ) hr) hΩ
      (F.pipelineExponent hδ hdisc (w₁ : ℝ) hr) T w₁ i).shade := by
    simpa [outerFactoringFamily, FactorFamily.pipelineFamily, T] using hyi
  rw [shade_step5InnerBody] at hyi'
  obtain ⟨z, hz, _⟩ := Set.mem_iUnion₂.mp hyi'.2
  exact ⟨z, hz⟩

/-- **Item 5** of GWZ Proposition 5.1 (`propFactoringAndMultPropCombinedMultDominatedtItem`):
`μ(𝒱, Y) ⪅ μ(𝒲', Y_{𝒲'}) · μ(𝒱'_W, Y')` for each `W ∈ 𝒲'`. The loss depends on the ambient
dimension, the cardinality of the inner family, and `δ`.

The right factor is supplied by
`ShadedBody.FactorFamily.pipelineFamily_fiber_multiplicity` and the global count by
`ShadedBody.FactorFamily.pipelineFamily_multiplicity`. The outer factor
`multiplicity 𝒲' Y_{𝒲'}` has to be bounded *below* by the Step 2 outer dyadic level `2 ^ l` of
`ShadedBody.FactorFamily.bounds_of_mem_pipelineSet`; that is the packing estimate for the
enlargements `N_{r j} (W j)`, and it is now available in the required generality as
`ShadedBody.le_multiplicity_of_local_balls`.

**Why `hscale` is present.** The packing estimate needs the enlargement radii `r j = (W j).scale`
tied to `w₁` from *both* sides. The upper bound `r j ≤ 2 * w₁` is what makes the outer shaded
union lie inside the `6 * w₁`-balls around the Step 5 cover; the lower bound `w₁ ≤ 2 * r j` is the
hypothesis `r ≤ 2 * s` of `Kakeya.exists_ball_subset_cthickening_inter_ball`, which is what
supplies the ball of radius `w₁ / 8` inside each outer shade near a prescribed point of it.
Without a two-sided scale hypothesis no constant depending only on `n`, `|𝒱|` and `δ` can work,
for the same reason as in Item 3. `F.OuterIsAtScale 2 w₁` gives both bounds, and it is the
hypothesis Items 3 and 7 already carry.

**Two structural defects of the previous condition have been repaired, and both diagnoses were
confirmed.**

* In the tube case the outer lower bound comes from a *fatness* input: each outer shade must
  contain a ball of radius comparable to the tube radius. That is the hypothesis of
  `ShadedBody.outerMultiplicity_lower_of_local_balls` in `Kakeya/Factoring/RhoTubes.lean` (the
  general argument was redone as `ShadedBody.le_multiplicity_of_local_balls`, which is what is
  cited here; the tube lemma is the case `m = 4` of it and is no longer `private`).
  It was originally added here as the explicit hypothesis `hfat`. That hypothesis has since been
  *removed*, because it is derivable and, in the shape it had, not even the shape the proof needs.
  The outer carriers of this construction are the enlargements
  `Metric.cthickening (r j) (W j).carrier`, and every point of a closed neighbourhood of a compact
  set has a ball of radius `r / 8` near it inside that neighbourhood
  (`Kakeya.exists_ball_subset_cthickening_inter_ball`). What the proof needs is that *local* form
  of fatness — a fat ball near each prescribed point of the shade, not merely somewhere in it —
  and that form follows from `hscale` alone; see `outerFactoringFamily_local_balls`.
* `ShadedBody.multiplicity` is the quotient `(∑ |Y i|) / |⋃ Y i|`, which is `0` in `ℝ≥0∞` when the
  shaded union is null. Nothing in the construction forbids the Step 5 selection from cutting the
  shading of one retained fiber `j ∈ 𝒲'` down to a null set, and then the right-hand side was `0`
  for every `C` while the left-hand side is at least `1` whenever `(𝒱, Y)` carries any mass. *No*
  constant repaired that. The fix is a nondegeneracy hypothesis, not a larger loss, and it is now
  the per-index premise `volume (⋃ i ∈ 𝒱'_j, Y' i) ≠ 0` inside the conclusion's `∀ j ∈ 𝒲'`.

As for Item 3, these are arguments about the statement rather than formalized counterexamples.

**The placeholder constant `1` is gone.** It asserted the multiplicity factorization with no loss
at all, and Item 5 was false at it. The value now carried by
`outerFactoringFamily_multDominated.C` is the honest one: the assembled Step 0 - Step 5
pigeonholing loss of the pipeline, times `ShadedBody.outerShadingPackingLoss n 6`. The cheap true
value `max 1 |𝒱|` remains inadmissible: it would falsify the constant-quality lemma
`outerFactoringFamily_multDominated.C_leApprox_one`, which is the claim that the Item 5 loss is
jointly subpolynomial in `δ⁻¹` and in `|𝒱|`. The installed value is not of that kind: every one of
its factors is dimensional or logarithmic. -/
theorem outerFactoringFamily_multDominated (F : FactorFamily E ι κ) {δ w₁ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (hw₁ : w₁ ∈ Set.Icc δ 1)
    (hscale : F.OuterIsAtScale 2 w₁) :
    ∀ j ∈ (outerFactoringFamily F hδ hdisc hw₁).outerSet,
      volume (⋃ i ∈ (outerFactoringFamily F hδ hdisc hw₁).fiber j,
        ((outerFactoringFamily F hδ hdisc hw₁).innerBody i).shade) ≠ 0 →
      multiplicity F.innerSet F.innerBody
        ≤ (outerFactoringFamily_multDominated.C
            (Module.finrank ℝ E) F.innerSet.card δ : ENNReal)
          * multiplicity (outerFactoringFamily F hδ hdisc hw₁).outerSet
              (outerFactoringFamily F hδ hdisc hw₁).outerBody
          * multiplicity ((outerFactoringFamily F hδ hdisc hw₁).fiber j)
              (outerFactoringFamily F hδ hdisc hw₁).innerBody := by
  classical
  let n : ℕ := Module.finrank ℝ E
  let N : ℕ := F.innerSet.card
  let hr : 0 < (w₁ : ℝ) := NNReal.coe_pos.mpr (hδ.trans_le hw₁.1)
  let hΩ : MeasurableSet (F.pipelineSet hδ hdisc (w₁ : ℝ) hr) :=
    F.measurableSet_pipelineSet hδ hdisc (w₁ : ℝ) hr
  let G : ShadedFactorFamily E ι κ := outerFactoringFamily F hδ hdisc hw₁
  let k : ℕ := F.pipelineExponent hδ hdisc (w₁ : ℝ) hr
  let l : ℕ := F.pipelineOuterExponent hδ hdisc (w₁ : ℝ) hr
  let P : NNReal := Kakeya.factoringStep1AtScaleConstant n N δ *
      (Kakeya.factoringStep2Step3Constant N : NNReal) *
      ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n (step5PackingRatio n N δ)
  intro j hjOuter hj
  have hglobal : multiplicity G.innerSet G.innerBody ≤ (4 * (2 ^ k * 2 ^ l) : ℕ) := by
    apply multiplicity_le_of_pointwiseMultiplicity_le
    intro x hx
    exact_mod_cast (F.pipelineFamily_multiplicity hδ hdisc (w₁ : ℝ) hr hΩ
      (outerFactoringCover F hδ hdisc hw₁) w₁ hx).2.le
  have hfiberUnion0 : volume (⋃ i ∈ G.fiber j, (G.innerBody i).shade) ≠ 0 := by
    simpa [G] using hj
  have hfiberLower : (2 ^ k : ENNReal) ≤ multiplicity (G.fiber j) G.innerBody := by
    apply le_multiplicity_of_le_pointwiseMultiplicity _ _ hfiberUnion0
    intro x hx
    exact_mod_cast (F.pipelineFamily_fiber_multiplicity hδ hdisc (w₁ : ℝ) hr hΩ
      (outerFactoringCover F hδ hdisc hw₁) w₁ hx).1
  have houterLower : (2 ^ l : ENNReal) ≤
      (outerShadingPackingLoss n 6 : ENNReal) * multiplicity G.outerSet G.outerBody := by
    simpa [G, l, n] using outerFactoringFamily_le_outerMultiplicity F hδ hdisc hw₁ hscale
      (outerFactoringCover_nonempty F hδ hdisc hw₁ hj)
  have hδ1 : δ ≤ 1 := hw₁.1.trans hw₁.2
  have hNpos : 0 < N := by
    have hfiberNe : (G.fiber j).Nonempty := by
      by_contra he
      have he' : G.fiber j = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
      exact hfiberUnion0 (by simp [he'])
    obtain ⟨i, hi⟩ := hfiberNe
    have hiF : i ∈ F.innerSet := by
      have hiG : i ∈ G.innerSet := by
        have hi' : i ∈ {a ∈ G.innerSet | G.parent a = j} := by
          simpa [ShadedFactorFamily.fiber] using hi
        exact (Finset.mem_filter.mp hi').1
      change i ∈ F.pipelineInnerSet hδ hdisc at hiG
      exact F.innerSet_step0_subset (Finset.mem_filter.mp hiG).1
    simpa [N] using F.innerSet.card_pos.mpr ⟨i, hiF⟩
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hNpos.ne'
  have hratio1 : (1 : NNReal) ≤ step5PackingRatio n N δ := one_le_step5PackingRatio n N hδ hδ1
  have hApos' : 0 < Kakeya.factoringStep1AtScaleConstant n N δ := by
    have hl := Kakeya.logb_step1UpperBdAtScale_div_step1LowerBdAtScale_nonneg
      n hN1 hδ hδ1
    rw [Kakeya.logb_step1UpperBdAtScale_div_step1LowerBdAtScale n hN1 hδ] at hl
    rw [Kakeya.factoringStep1AtScaleConstant_eq n hN1 hδ]
    apply mul_pos (by norm_num)
    rw [Real.toNNReal_pos]
    linarith
  have hBpos' : 0 < (Kakeya.factoringStep2Step3Constant N : NNReal) := by
    rw [Kakeya.factoringStep2Step3Constant_eq]
    positivity
  have hDpos' : 0 < ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant n
      (step5PackingRatio n N δ) := by
    unfold ShadedBody.Kakeya.factoringStep5SelfPigeonholeConstant
    have hOpos : (0 : NNReal) < Kakeya.factoringStep5OverlapConstant n := by
      unfold Kakeya.factoringStep5OverlapConstant
      positivity
    have hFpos : 0 < Kakeya.factoringStep1FiberPigeonholeConstant 1
        (step5PackingRatio n N δ) := lt_of_lt_of_le zero_lt_one
      (Kakeya.one_le_factoringStep1FiberPigeonholeConstant hratio1)
    exact mul_pos (mul_pos (by norm_num) hOpos) (mul_pos (by norm_num) hFpos)
  have hP0 : P ≠ 0 := by
    dsimp [P]
    exact (mul_pos (mul_pos hApos' hBpos') hDpos').ne'
  have hceq : outerFactoringFamily_refinement.c n N δ = P⁻¹ := by
    simp [P, outerFactoringFamily_refinement.c,
      ShadedBody.Kakeya.factoringPipelineSelfRefinementConstant]
    ring
  have hPinv : (outerFactoringFamily_refinement.c n N δ : ENNReal)⁻¹ = (P : ENNReal) := by
    rw [hceq]
    rw [ENNReal.coe_inv hP0]
    rw [inv_inv]
  have hrefMu : multiplicity F.innerSet F.innerBody ≤
      (P : ENNReal) * multiplicity G.innerSet G.innerBody := by
    have hbase : multiplicity F.innerSet F.innerBody ≤
        (outerFactoringFamily_refinement.c n N δ : ENNReal)⁻¹ *
          multiplicity G.innerSet G.innerBody := by
      exact multiplicity_le_of_isCRefinement
        (s := F.innerSet) (V := F.innerBody) (s' := G.innerSet) (V' := G.innerBody)
        (c := outerFactoringFamily_refinement.c n N δ)
        (by rw [hceq]; exact inv_ne_zero hP0)
        (outerFactoringFamily_refinement F hδ hdisc hw₁)
    simpa [hPinv] using hbase
  calc
    multiplicity F.innerSet F.innerBody
        ≤ (P : ENNReal) * multiplicity G.innerSet G.innerBody := hrefMu
    _ ≤ (P : ENNReal) * (4 * ((2 ^ k : ENNReal) * (2 ^ l : ENNReal))) := by
      gcongr
      simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] using hglobal
    _ = (4 * (P : ENNReal)) * (2 ^ l : ENNReal) * (2 ^ k : ENNReal) := by
      ring
    _ ≤ (4 * (P : ENNReal)) *
          ((outerShadingPackingLoss n 6 : ENNReal) *
            multiplicity G.outerSet G.outerBody) *
          multiplicity (G.fiber j) G.innerBody := by
      gcongr
    _ = (outerFactoringFamily_multDominated.C n N δ : ENNReal) *
          multiplicity G.outerSet G.outerBody *
          multiplicity (G.fiber j) G.innerBody := by
      rw [outerFactoringFamily_multDominated.C]
      simp only [P]
      push_cast
      ring

/-- **Item 6** of GWZ Proposition 5.1 (`propFactoringAndMultPropCombinedShadingDominatedItem`):
the pointwise shading containment. The output is a fully shaded factor family, so this is exactly
its `shade_subset_parent` field. Dimension-free.

This lemma is the projection `(outerFactoringFamily F hδ hdisc hw₁).shade_subset_parent`. -/
theorem outerFactoringFamily_shadingContainment (F : FactorFamily E ι κ) {δ w₁ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (hw₁ : w₁ ∈ Set.Icc δ 1) :
    ∀ i ∈ (outerFactoringFamily F hδ hdisc hw₁).innerSet,
      ((outerFactoringFamily F hδ hdisc hw₁).innerBody i).shade
        ⊆ ((outerFactoringFamily F hδ hdisc hw₁).outerBody (F.parent i)).shade :=
  (outerFactoringFamily F hδ hdisc hw₁).shade_subset_parent

/-- **Large constant in `ShadedBody.outerFactoringFamily_avgMultOnBalls`**: twice the Step 5
bounded-overlap constant of the `w₁`-cover, twice over -- once to move the left ball to a cover
centre and once to move that centre to the comparison point. -/
@[nolint defsWithUnderscore]
noncomputable def outerFactoringFamily_avgMultOnBalls.C (n : ℕ) (_δ : NNReal) : NNReal :=
  4 * (Kakeya.factoringStep5OverlapConstant n : NNReal)

/-- The loss in Item 7 is subpolynomial in the discretization scale. -/
theorem outerFactoringFamily_avgMultOnBalls.C_leApprox_one (n : ℕ) :
    (fun δ : NNReal ↦ outerFactoringFamily_avgMultOnBalls.C n δ) ⪅
      fun _ : NNReal ↦ (1 : NNReal) := by
  intro ε hε
  refine ⟨outerFactoringFamily_avgMultOnBalls.C n 0, ?_⟩
  intro ρ hρ hρ1
  have h : (1 : NNReal) ≤ ρ ^ (-ε) := Kakeya.one_le_rpow_neg hε.le hρ hρ1
  have hC : 0 ≤ outerFactoringFamily_avgMultOnBalls.C n 0 := by positivity
  simpa [outerFactoringFamily_avgMultOnBalls.C, mul_assoc, mul_one] using
    mul_le_mul_of_nonneg_left h hC

/-- Every point of the outer shaded union of `outerFactoringFamily` is within `5 * w₁` of the
inner shaded union. -/
private lemma exists_mem_iUnionShade_dist_le (F : FactorFamily E ι κ) {δ w₁ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (hw₁ : w₁ ∈ Set.Icc δ 1)
    (hscale : F.OuterIsAtScale 2 w₁) {y : E}
    (hy : y ∈ ⋃ j ∈ (outerFactoringFamily F hδ hdisc hw₁).outerSet,
      ((outerFactoringFamily F hδ hdisc hw₁).outerBody j).shade) :
    ∃ y' ∈ ⋃ i ∈ (outerFactoringFamily F hδ hdisc hw₁).innerSet,
        ((outerFactoringFamily F hδ hdisc hw₁).innerBody i).shade,
      dist y y' ≤ 5 * (w₁ : ℝ) := by
  classical
  let hr : 0 < (w₁ : ℝ) := NNReal.coe_pos.mpr (hδ.trans_le hw₁.1)
  let hΩ : MeasurableSet (F.pipelineSet hδ hdisc (w₁ : ℝ) hr) :=
    F.measurableSet_pipelineSet hδ hdisc (w₁ : ℝ) hr
  let T' : Finset E := outerFactoringCover F hδ hdisc hw₁
  let u : Finset ι := F.step0.innerSet
  let t' : Finset κ := (F.step1 hδ hdisc).outerSet
  let Ω : Set E := F.pipelineSet hδ hdisc (w₁ : ℝ) hr
  let k : ℕ := F.pipelineExponent hδ hdisc (w₁ : ℝ) hr
  change y ∈ ⋃ j ∈ t', (step5OuterBody F F.innerSet_step0_subset t' Ω hΩ k T' w₁ j).shade at hy
  rcases Set.mem_iUnion₂.mp hy with ⟨j, hjt', hyj⟩
  have hjF : j ∈ F.outerSet :=
    F.pipelineFamily_outerSet_subset hδ hdisc (w₁ : ℝ) hr hΩ T' w₁ hjt'
  let U' : Set E := iUnionShade {i ∈ u | F.parent i = j} (step5InnerBody F u t' Ω hΩ k T' w₁)
  rw [shade_step5OuterBody_eq F F.innerSet_step0_subset t' Ω hΩ k T' w₁ hjt'] at hyj
  have hy2 : y ∈ Metric.cthickening (2 * (F.outerBody j).scale) U' := hyj.2
  have hscale_le : (F.outerBody j).scale ≤ 2 * (w₁ : ℝ) := by
    simpa [ConvexSpaceBody.scale] using (hscale j hjF).1
  have hradius : 2 * (F.outerBody j).scale ≤ 4 * (w₁ : ℝ) := by nlinarith
  have hy4 : y ∈ Metric.cthickening (4 * (w₁ : ℝ)) U' :=
    Metric.cthickening_mono hradius U' hy2
  have hinf : Metric.infEDist y U' ≤ ENNReal.ofReal (4 * (w₁ : ℝ)) := by
    simpa using hy4
  have hRpos : 0 < 5 * (w₁ : ℝ) := by nlinarith [hr]
  have hRlt : ENNReal.ofReal (4 * (w₁ : ℝ)) < ENNReal.ofReal (5 * (w₁ : ℝ)) := by
    exact (ENNReal.ofReal_lt_ofReal_iff hRpos).mpr (by nlinarith [hr])
  have hinf_lt : Metric.infEDist y U' < ENNReal.ofReal (5 * (w₁ : ℝ)) :=
    lt_of_le_of_lt hinf hRlt
  rcases Metric.infEDist_lt_iff.mp hinf_lt with ⟨y', hy'U', hed⟩
  refine ⟨y', ?_, ?_⟩
  · change y' ∈ iUnionShade {i ∈ u | F.parent i ∈ t'} (step5InnerBody F u t' Ω hΩ k T' w₁)
    rcases Set.mem_iUnion₂.mp hy'U' with ⟨i, hi, hy'i⟩
    refine Set.mem_iUnion₂.mpr ⟨i, ?_, hy'i⟩
    rcases Finset.mem_filter.mp hi with ⟨hiu, hpi⟩
    exact Finset.mem_filter.mpr ⟨hiu, by simpa [hpi] using hjt'⟩
  · have hed' : ENNReal.ofReal (dist y y') < ENNReal.ofReal (5 * (w₁ : ℝ)) := by
      simpa only [edist_dist] using hed
    have hdist_lt : dist y y' < 5 * (w₁ : ℝ) :=
      (ENNReal.ofReal_lt_ofReal_iff hRpos).mp hed'
    exact le_of_lt hdist_lt

/-- **Item 7** of GWZ Proposition 5.1 (`propFactoringAndMultPropCombinedAvgMultOnBallsItem`),
at radius `7 * w₁`: the ball of radius `w₁` on the left is compared with the closed ball of radius
`7 * w₁` on the right. The loss depends only on the ambient dimension and `δ`.

**`7` is the cost of *this* route, not a lower bound over all routes.**
`Kakeya/Factoring/Step5.lean` gives the estimate with the *inner* shaded union on the right
(`ShadedBody.volume_iUnionShade_step5_inter_ball_le_mul_volume_inter_closedBall`, radius
`2 * w₁`); here the comparison point `y` only lies in the *outer* shaded union, hence within
`2 * (F.outerBody j).scale ≤ 4 * w₁` of the inner union by `hscale`, and `4 + 2 ≤ 7`. That
computes what the present argument achieves; it establishes nothing about what is achievable.

An earlier version of this docstring asserted that *"the equal-radius condition is false for the
constructed family"*. **That assertion was never proved** — no refutation of it exists anywhere in
this development — and it is contradicted twice over. GWZ states item (7) *at* radius `w₁`, on
`U(V′, Y′)`, for every `x ∈ U(W′, Y_{W′})`; and
`ShadedBody.FactoringAndMultPropCombinedAtScale.ball_comparison` already proves the sharper
open-`w₁`-versus-closed-`2 w₁` form on the inner union, so the `7` here is not forced even by our
own construction. `Kakeya.ThinCase.centredMult_of_separatedNet_of_gap` consumes that sharper form.

What is established is only that the `7` is this route's cost and that the falsity claim was
unbacked — **not** that the equal-radius form is true for the constructed family. -/
theorem outerFactoringFamily_avgMultOnBalls (F : FactorFamily E ι κ) {δ w₁ : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (hw₁ : w₁ ∈ Set.Icc δ 1)
    (hscale : F.OuterIsAtScale 2 w₁) :
    ∀ x ∈ ⋃ j ∈ (outerFactoringFamily F hδ hdisc hw₁).outerSet,
        ((outerFactoringFamily F hδ hdisc hw₁).outerBody j).shade,
    ∀ y ∈ ⋃ j ∈ (outerFactoringFamily F hδ hdisc hw₁).outerSet,
        ((outerFactoringFamily F hδ hdisc hw₁).outerBody j).shade,
      volume ((⋃ i ∈ (outerFactoringFamily F hδ hdisc hw₁).innerSet,
          ((outerFactoringFamily F hδ hdisc hw₁).innerBody i).shade) ∩ Metric.ball x (w₁ : ℝ))
        ≤ (outerFactoringFamily_avgMultOnBalls.C (Module.finrank ℝ E) δ : ENNReal)
          * volume ((⋃ i ∈ (outerFactoringFamily F hδ hdisc hw₁).innerSet,
              ((outerFactoringFamily F hδ hdisc hw₁).innerBody i).shade) ∩
                Metric.closedBall y (7 * (w₁ : ℝ))) := by
  classical
  let hr : 0 < (w₁ : ℝ) := NNReal.coe_pos.mpr (hδ.trans_le hw₁.1)
  let hΩ : MeasurableSet (F.pipelineSet hδ hdisc (w₁ : ℝ) hr) :=
    F.measurableSet_pipelineSet hδ hdisc (w₁ : ℝ) hr
  let T' : Finset E :=
    (exists_factoringPipelineSelf F hδ hdisc (w₁ : ℝ) hr hΩ (hδ.trans_le hw₁.1)).choose_spec.choose
  let u : Finset ι := F.step0.innerSet
  let t' : Finset κ := (F.step1 hδ hdisc).outerSet
  let Ω : Set E := F.pipelineSet hδ hdisc (w₁ : ℝ) hr
  let k : ℕ := F.pipelineExponent hδ hdisc (w₁ : ℝ) hr
  let U : Set E := iUnionShade {i ∈ u | F.parent i ∈ t'} (step5InnerBody F u t' Ω hΩ k T' w₁)
  intro x hx y hy
  change volume (U ∩ Metric.ball x (w₁ : ℝ)) ≤
    (outerFactoringFamily_avgMultOnBalls.C (Module.finrank ℝ E) δ : ENNReal) *
      volume (U ∩ Metric.closedBall y (7 * (w₁ : ℝ)))
  rcases Finset.eq_empty_or_nonempty T' with hT'empty | hT'ne
  · have hsel : step5Selection T' w₁ = ∅ := by
      rw [hT'empty]
      simp [step5Selection]
    have hUempty : U = ∅ := by
      dsimp [U]
      simp [hsel]
    rw [hUempty]
    simp
  · obtain ⟨hTsub, hTsep, hTcover, hToverlap, hT'T, hT'pos, hT'sep, href₅, hballcomp⟩ :=
      (exists_factoringPipelineSelf F hδ hdisc (w₁ : ℝ) hr hΩ (hδ.trans_le hw₁.1)).choose_spec.choose_spec
    have hcomp' : ∀ c ∈ T', ∀ c' ∈ T',
        volume (U ∩ Metric.closedBall c (w₁ : ℝ)) ≤
          2 * volume (U ∩ Metric.closedBall c' (w₁ : ℝ)) := by
      intro c hc c' hc'
      simpa [U, T', FactorFamily.pipelineFamily, FactorFamily.pipelineInnerSet, u, t', Ω, k] using
        hballcomp c hc c' hc'
    obtain ⟨y', hy'U', hdist⟩ := exists_mem_iUnionShade_dist_le F hδ hdisc hw₁ hscale hy
    have hy'U : y' ∈ U := by
      change y' ∈ iUnionShade {i ∈ u | F.parent i ∈ t'} (step5InnerBody F u t' Ω hΩ k T' w₁) at hy'U'
      exact hy'U'
    have hcore := volume_iUnionShade_step5_inter_ball_le_mul_volume_inter_closedBall
      F u t' Ω hΩ k (w₁ := w₁) (hδ.trans_le hw₁.1) hT'ne hT'sep hcomp' x hy'U
    have hC : (outerFactoringFamily_avgMultOnBalls.C (Module.finrank ℝ E) δ : ENNReal) =
        (4 : ENNReal) * (Kakeya.factoringStep5OverlapConstant (Module.finrank ℝ E) : ENNReal) := by
      simp [outerFactoringFamily_avgMultOnBalls.C, ENNReal.coe_mul]
    have hmain : volume (U ∩ Metric.ball x (w₁ : ℝ)) ≤
        (outerFactoringFamily_avgMultOnBalls.C (Module.finrank ℝ E) δ : ENNReal) *
          volume (U ∩ Metric.closedBall y' (2 * (w₁ : ℝ))) := by
      calc
        volume (U ∩ Metric.ball x (w₁ : ℝ)) ≤
            (4 : ENNReal) * (Kakeya.factoringStep5OverlapConstant (Module.finrank ℝ E) : ENNReal) *
              volume (U ∩ Metric.closedBall y' (2 * (w₁ : ℝ))) := by
          simpa [U] using hcore
        _ = (outerFactoringFamily_avgMultOnBalls.C (Module.finrank ℝ E) δ : ENNReal) *
              volume (U ∩ Metric.closedBall y' (2 * (w₁ : ℝ))) := by
          rw [hC]
    have hdy : 2 * (w₁ : ℝ) + dist y' y ≤ 7 * (w₁ : ℝ) := by
      have hdist' : dist y' y ≤ 5 * (w₁ : ℝ) := by simpa [dist_comm] using hdist
      nlinarith
    have hballsub : Metric.closedBall y' (2 * (w₁ : ℝ)) ⊆ Metric.closedBall y (7 * (w₁ : ℝ)) :=
      Metric.closedBall_subset_closedBall' hdy
    have hright : volume (U ∩ Metric.closedBall y' (2 * (w₁ : ℝ))) ≤
        volume (U ∩ Metric.closedBall y (7 * (w₁ : ℝ))) :=
      measure_mono (Set.inter_subset_inter (Set.Subset.refl U) hballsub)
    have hfinal : (outerFactoringFamily_avgMultOnBalls.C (Module.finrank ℝ E) δ : ENNReal) *
          volume (U ∩ Metric.closedBall y' (2 * (w₁ : ℝ))) ≤
        (outerFactoringFamily_avgMultOnBalls.C (Module.finrank ℝ E) δ : ENNReal) *
          volume (U ∩ Metric.closedBall y (7 * (w₁ : ℝ))) := by
      gcongr
    exact hmain.trans hfinal

end FactoringAndMultiplicity

end ShadedBody
