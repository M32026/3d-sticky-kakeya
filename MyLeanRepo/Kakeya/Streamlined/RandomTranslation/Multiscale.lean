import MyLeanRepo.Kakeya.Streamlined.Geometry
import MyLeanRepo.Kakeya.Streamlined.Families
import MyLeanRepo.Kakeya.Streamlined.Estimates
import MyLeanRepo.Kakeya.Streamlined.TubeRefinement
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.GeometricProbability
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.TranslatedCopiesBasic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Multiscale random translations

This module separates the geometric multiscale random-translation lemma from
its shading-aware application in GWZ Section 7.

For each requested Frostman exponent `η₁`, choose a sufficiently smaller
Katz--Tao input exponent `η`.  Given a Katz-Tao-at-every-scale tube family
`(F, U)` with error `δ^(-η)`, produce an essentially-distinct subfamily of an
explicit finite union of translated copies that is Frostman at every scale
with error `δ^(-η₁)`, with controlled translation count.  This is the paper's
geometric `lemmasubsticky` output and does not mention a shading.

The subsequent application fixes a shading before selecting the
essentially-distinct subfamily.  That ordering is necessary for bicriteria
selection to retain both tube cardinality and shaded mass.

The selected `η` and constant `C` are **uniform**: they depend only on `η₁`,
not on `δ`, `F`, or `U`.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Streamlined

namespace RandomTranslation

end RandomTranslation

/-- **Random translation lemma (`lemmasubsticky`).**

For the requested output exponent `η₁`, choose a sufficiently small input
exponent `η`. Given a Katz-Tao-at-every-scale tube family `(F, U)` with error
`δ^(-η)`, produce an essentially-distinct subfamily of an explicit finite
union of translated copies that is Frostman at every scale with error
`δ^(-η₁)`, with controlled translation count.

The paper's `\gtrapprox` cardinality conclusion uses the requested output
loss `δ^η₁`.  The smaller exponent `η` controls the input Katz--Tao and
shading hypotheses; using it again for output cardinality would leave no
room to absorb the finite selection losses.

The translated family F' is contained in the ball of radius 10.
-/
def RandomTranslationLemma : Prop :=
  ∀ η₁ : ℝ, 0 < η₁ →
  ∃ η : ℝ, 0 < η ∧ 6 * η ≤ η₁ ∧ 5 * η ≤ 2 ∧
  ∃ (C : ENNReal) (hC_pos : 0 < C) (hC_ne_top : C ≠ ⊤)
    (δ₀ : ℝ) (hδ₀_pos : 0 < δ₀) (hδ₀_le_one : δ₀ ≤ 1),
    ∀ (δ : ℝ), 0 < δ → δ ≤ δ₀ →
    ∀ (F : TubeFamily δ), F.Nonempty → F.IsInUnitBall → F.IsEssentiallyDistinct →
    ∀ (U : UniformTubeStructure F),
      U.uniformity ≤ Kakeya.realRpowENN δ (-η) →
      U.IsKatzTaoAtEveryScale (Kakeya.realRpowENN δ (-η)) →
    ∃ (J : ℕ) (hJ_pos : 0 < J) (shift : Fin J → Point3)
      (S : TubeSubfamily (RandomTranslation.translatedCopies F J shift))
      (U' : UniformTubeStructure S.family),
      (∀ j, ‖shift j‖ ≤ 9) ∧
      S.Nonempty ∧
      (∀ i, (S.family.tube i).carrier ⊆ Metric.closedBall (0 : Point3) 10) ∧
      S.family.IsEssentiallyDistinct ∧
      Kakeya.realRpowENN δ η₁ *
          ((J : ENNReal) * F.enncard) ≤ S.family.enncard ∧
      U'.uniformity ≤ Kakeya.realRpowENN δ (-η₁) ∧
      U'.IsFrostmanAtEveryScale (Kakeya.realRpowENN δ (-η₁)) ∧
      (J : ENNReal) ≤
        C * Kakeya.realRpowENN δ (-η₁) *
          max 1 F.nominalMass⁻¹

/--
The shading-aware version used to deduce the Katz--Tao-at-every-scale
consequence from sticky Kakeya.

Unlike `RandomTranslationLemma`, the shading is fixed before the translated
subfamily is selected.  This permits bounded-conflict bicriteria extraction
to retain both cardinality and shaded mass.  It is a separate dependency, not
part of the geometric `lemmasubsticky` statement.

As in the geometric statement, output cardinality is measured with `δ^η₁`;
input shading density remains `δ^η`.
-/
def RandomTranslationWithShadingStatement : Prop :=
  ∀ η₁ : ℝ, 0 < η₁ →
  ∃ η : ℝ, 0 < η ∧ 6 * η ≤ η₁ ∧ 5 * η ≤ 2 ∧
  ∃ (C : ENNReal) (hC_pos : 0 < C) (hC_ne_top : C ≠ ⊤)
    (δ₀ : ℝ) (hδ₀_pos : 0 < δ₀) (hδ₀_le_one : δ₀ ≤ 1),
    ∀ (δ : ℝ), 0 < δ → δ ≤ δ₀ →
    ∀ (F : TubeFamily δ), F.Nonempty → F.IsInUnitBall → F.IsEssentiallyDistinct →
    ∀ (U : UniformTubeStructure F),
      U.uniformity ≤ Kakeya.realRpowENN δ (-η) →
      U.IsKatzTaoAtEveryScale (Kakeya.realRpowENN δ (-η)) →
    ∀ (Y : TubeShading F),
      Y.IsLambdaDense (Kakeya.realRpowENN δ η) →
    ∃ (J : ℕ) (hJ_pos : 0 < J) (shift : Fin J → Point3)
      (S : TubeSubfamily (RandomTranslation.translatedCopies F J shift))
      (U' : UniformTubeStructure S.family)
      (Y' : TubeShading S.family),
      (∀ j, ‖shift j‖ ≤ 9) ∧
      S.Nonempty ∧
      (∀ i, (S.family.tube i).carrier ⊆ Metric.closedBall (0 : Point3) 10) ∧
      S.family.IsEssentiallyDistinct ∧
      Kakeya.realRpowENN δ η₁ *
          ((J : ENNReal) * F.enncard) ≤ S.family.enncard ∧
      U'.uniformity ≤ Kakeya.realRpowENN δ (-η₁) ∧
      U'.IsFrostmanAtEveryScale (Kakeya.realRpowENN δ (-η₁)) ∧
      (J : ENNReal) ≤
        C * Kakeya.realRpowENN δ (-η₁) *
          max 1 F.nominalMass⁻¹ ∧
      Y'.IsLambdaDense (Kakeya.realRpowENN δ η₁) ∧
      (∀ i,
        let p : Fin J × Fin F.card :=
          finProdFinEquiv.symm (S.embedding i)
        Y'.carrier i =
          RandomTranslation.translateSet
            (Y.carrier p.2) (shift p.1)) ∧
      (J : ENNReal) * volume Y.union ≥ volume Y'.union

namespace RandomTranslation

/-- Complete result of the probabilistic translation argument.

Packages the geometric properties required by `RandomTranslationLemma`. -/
structure GoodTranslationData (δ : ℝ) (F : TubeFamily δ)
    (η₁ η : ℝ) (C : ENNReal) where
  J : ℕ
  hJ_pos : 0 < J
  shift : Fin J → Point3
  hshift : ∀ j, ‖shift j‖ ≤ 9
  subfamily : TubeSubfamily (translatedCopies F J shift)
  U' : UniformTubeStructure subfamily.family
  hF'_nonempty : subfamily.Nonempty
  hF'_in_ball_10 :
    ∀ i, (subfamily.family.tube i).carrier ⊆ Metric.closedBall (0 : Point3) 10
  hF'_distinct : subfamily.family.IsEssentiallyDistinct
  hF'_card :
    Kakeya.realRpowENN δ η₁ * ((J : ENNReal) * F.enncard) ≤
      subfamily.family.enncard
  hU'_uniform : U'.uniformity ≤ Kakeya.realRpowENN δ (-η₁)
  hU'_frost : U'.IsFrostmanAtEveryScale (Kakeya.realRpowENN δ (-η₁))
  h_count_bound :
    (J : ENNReal) ≤
      C * Kakeya.realRpowENN δ (-η₁) *
        max 1 F.nominalMass⁻¹

/--
Packages the stronger shading-aware output.  The selected subfamily may
depend on the supplied shading.
-/
structure GoodTranslationWithShadingData (δ : ℝ) (F : TubeFamily δ)
    (η₁ η : ℝ) (C : ENNReal) (Y : TubeShading F) where
  J : ℕ
  hJ_pos : 0 < J
  shift : Fin J → Point3
  hshift : ∀ j, ‖shift j‖ ≤ 9
  subfamily : TubeSubfamily (translatedCopies F J shift)
  U' : UniformTubeStructure subfamily.family
  hF'_nonempty : subfamily.Nonempty
  hF'_in_ball_10 :
    ∀ i, (subfamily.family.tube i).carrier ⊆ Metric.closedBall (0 : Point3) 10
  hF'_distinct : subfamily.family.IsEssentiallyDistinct
  hF'_card :
    Kakeya.realRpowENN δ η₁ * ((J : ENNReal) * F.enncard) ≤
      subfamily.family.enncard
  hU'_uniform : U'.uniformity ≤ Kakeya.realRpowENN δ (-η₁)
  hU'_frost : U'.IsFrostmanAtEveryScale (Kakeya.realRpowENN δ (-η₁))
  h_count_bound :
    (J : ENNReal) ≤
      C * Kakeya.realRpowENN δ (-η₁) *
        max 1 F.nominalMass⁻¹
  shading : TubeShading subfamily.family
  h_shading_dense :
    shading.IsLambdaDense (Kakeya.realRpowENN δ η₁)
  h_shading_carrier : ∀ i,
    let p : Fin J × Fin F.card :=
      finProdFinEquiv.symm (subfamily.embedding i)
    shading.carrier i = translateSet (Y.carrier p.2) (shift p.1)
  h_shading_union :
    (J : ENNReal) * volume Y.union ≥ volume shading.union

end RandomTranslation

end Kakeya.Streamlined
