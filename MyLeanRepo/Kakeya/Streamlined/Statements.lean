import MyLeanRepo.Kakeya.Streamlined.Estimates
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Paper-level target statements for the streamlined proof

This file contains rigorous propositions and data structures only.  The
individual leaf targets live in
`MyLeanRepo/Kakeya/Streamlined/Targets/`; each such file contains exactly one
theorem and one proof placeholder.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Streamlined

/-- A refinement of a factoring, with compatible fine and coarse identities. -/
structure FactoringRefinement {fine coarse : BodyFamily}
    (P : Factoring fine coarse) (Y : Shading fine) where
  fineRefinement : Refinement Y
  coarseSubfamily : Subfamily coarse
  factoring :
    Factoring fineRefinement.subfamily.family coarseSubfamily.family
  compatible :
    ∀ i,
      coarseSubfamily.embedding (factoring.parent i) =
        P.parent (fineRefinement.subfamily.embedding i)
  coarseShading : Shading coarseSubfamily.family

namespace Factoring

/-- Shaded union of one parent fiber. -/
def fiberShadedUnion {fine coarse : BodyFamily} (P : Factoring fine coarse)
    (Y : Shading fine) (j : Fin coarse.card) : Set Point3 :=
  {x | ∃ i : Fin fine.card, P.parent i = j ∧ x ∈ Y.carrier i}

/-- Average multiplicity in one parent fiber, expressed without division. -/
def FiberAverageMultiplicityLE {fine coarse : BodyFamily}
    (P : Factoring fine coarse) (Y : Shading fine)
    (j : Fin coarse.card) (M : ENNReal) : Prop :=
  P.fiberShadedMass Y j ≤
    M * MeasureTheory.volume (P.fiberShadedUnion Y j)

/-- Pointwise multiplicity of one parent fiber. -/
def fiberPointMultiplicity {fine coarse : BodyFamily}
    (P : Factoring fine coarse) (Y : Shading fine)
    (j : Fin coarse.card) (x : Point3) : ℕ := by
  classical
  exact ((P.fiberIndices j).filter fun i => x ∈ Y.carrier i).card

/-- Pointwise multiplicity in one fiber is between two fixed natural numbers. -/
def FiberHasConstantMultiplicity {fine coarse : BodyFamily}
    (P : Factoring fine coarse) (Y : Shading fine)
    (j : Fin coarse.card) (m M : ℕ) : Prop :=
  ∀ x ∈ P.fiberShadedUnion Y j,
    m ≤ P.fiberPointMultiplicity Y j x ∧
      P.fiberPointMultiplicity Y j x ≤ M

end Factoring

/-- A family of measurable convex `a × b × 1` planks with rigid frames. -/
structure PlankFamily (a b A : ℝ) where
  family : BodyFamily
  frame : Fin family.card → (Point3 ≃ᵃⁱ[ℝ] Point3)
  dimensions :
    ∀ i, (family.body i).HasDimensionsInFrame (frame i) a b 1 A
  measurable : family.IsMeasurable
  convex : family.IsConvex

namespace PlankFamily

/-- Unit normal to the long plane of a framed plank. -/
def normal {a b A : ℝ} (P : PlankFamily a b A)
    (i : Fin P.family.card) : Point3 :=
  (P.frame i).linearIsometryEquiv
    (EuclideanSpace.single (0 : Fin 3) (1 : ℝ))

end PlankFamily

/-- A framed measurable convex `θ × 1 × 1` slab. -/
structure FramedSlab (theta A : ℝ) where
  body : Body
  frame : Point3 ≃ᵃⁱ[ℝ] Point3
  dimensions : body.HasDimensionsInFrame frame theta 1 1 A
  measurable : body.IsMeasurable
  convex : body.IsConvex

namespace FramedSlab

/-- Unit normal to the long plane of a framed slab. -/
def normal {theta A : ℝ} (S : FramedSlab theta A) : Point3 :=
  S.frame.linearIsometryEquiv
    (EuclideanSpace.single (0 : Fin 3) (1 : ℝ))

end FramedSlab

/-- Angle between the long planes, represented by their unit normals. -/
def planeAngle (u v : Point3) : ℝ :=
  Real.arccos |inner ℝ u v|

/-- Planks contained in and aligned with a test slab. -/
def planksInSlab {a b A : ℝ} (P : PlankFamily a b A)
    (theta : ℝ) (S : FramedSlab theta A) : Finset (Fin P.family.card) := by
  classical
  exact Finset.univ.filter fun i =>
    (P.family.body i).carrier ⊆ S.body.carrier ∧
      planeAngle (P.normal i) S.normal ≤ theta

/-- Non-concentration of planks into aligned slabs. -/
def PlankSlabNonconcentration {a b A : ℝ} (P : PlankFamily a b A)
    (eta gamma : ℝ) : Prop :=
  ∀ theta : ℝ, a / b ≤ theta → theta ≤ 1 →
    ∀ S : FramedSlab theta A,
      ((planksInSlab P theta S).card : ENNReal) ≤
        Kakeya.realRpowENN a (-eta) *
          Kakeya.realRpowENN theta gamma * P.family.enncard

/-- Non-concentration into thickened copies of individual planks. -/
def ThickenedPlankNonconcentration {a b A : ℝ} (P : PlankFamily a b A)
    (M : ℝ) : Prop :=
  ∀ theta : ℝ, a / b ≤ theta → theta ≤ 1 →
    ∀ i : Fin P.family.card,
      P.family.containedCount
        (Metric.cthickening (theta * b) (P.family.body i).carrier) ≤
          ENNReal.ofReal (M * theta)

/-- Global factoring of a tube family through planks. -/
def HasGlobalPlankFactoring {δ a b A : ℝ} (F : TubeFamily δ)
    (C : ENNReal) : Prop :=
  ∃ P : PlankFamily a b A,
    ∃ Q : Factoring F.toBodyFamily P.family,
      P.family.IsCKatzTao C ∧ Q.FibersAreCFrostman C

/-- Fine-tube mass assigned to one local plank and contained in `K`. -/
def localPlankContainedMass {δ rho a b A : ℝ}
    {fine : TubeFamily δ} {coarse : TubeFamily rho}
    (P : TubeCover fine coarse) (j : Fin coarse.card)
    (planks : PlankFamily a b A)
    (parentPlank : Fin fine.card → Fin planks.family.card)
    (p : Fin planks.family.card) (K : Set Point3) : ENNReal := by
  classical
  exact ∑ i ∈ Finset.univ.filter
      (fun i : Fin fine.card =>
        P.parent i = j ∧ parentPlank i = p ∧
          (fine.tube i).carrier ⊆ K),
    (fine.toBodyFamily.body i).volume

/-- One fiber of a tube cover factors through a family of planks. -/
def HasFiberPlankFactoring {δ rho a b A : ℝ}
    {fine : TubeFamily δ} {coarse : TubeFamily rho}
    (P : TubeCover fine coarse) (j : Fin coarse.card)
    (C : ENNReal) : Prop :=
  ∃ planks : PlankFamily a b A,
    ∃ parentPlank : Fin fine.card → Fin planks.family.card,
      (∀ i, P.parent i = j →
        (fine.tube i).carrier ⊆
          (planks.family.body (parentPlank i)).carrier) ∧
      (∀ p, (planks.family.body p).carrier ⊆
        (coarse.tube j).carrier) ∧
      planks.family.IsCKatzTao C ∧
      (∀ p, ∀ K : Set Point3, Convex ℝ K →
        K ⊆ (planks.family.body p).carrier →
          localPlankContainedMass P j planks parentPlank p K *
              (planks.family.body p).volume ≤
            C * localPlankContainedMass P j planks parentPlank p
                (planks.family.body p).carrier *
              MeasureTheory.volume K)

/-- Every fiber of a cover factors through planks with the same dimensions. -/
def HasLocalPlankFactoring {δ rho a b A : ℝ}
    {fine : TubeFamily δ} {coarse : TubeFamily rho}
    (P : TubeCover fine coarse) (C : ENNReal) : Prop :=
  ∀ j, HasFiberPlankFactoring (a := a) (b := b) (A := A) P j C

/-- Section 4: maximal-density factoring. -/
def MaximalDensityFactoringStatement : Prop :=
  ∀ A₀ : ℝ, 1 ≤ A₀ →
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ A : ℝ, 1 ≤ A ∧
        ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
          ∀ F : BodyFamily, F.IsMeasurable → F.IsConvex →
          ∀ a b c : ℝ,
            F.HasComparableDimensions a b c A₀ →
            rho ≤ a / c →
            ∃ S : Subfamily F,
              ∃ coarse : BodyFamily,
                ∃ P : Factoring S.family coarse,
                  ∃ w₁ w₂ w₃ : ℝ,
                  Kakeya.realRpowENN rho epsilon *
                      ENNReal.rpow (F.enncard + 1) (-epsilon) *
                      F.mass ≤
                    ENNReal.ofReal A * S.family.mass ∧
                  coarse.IsMeasurable ∧ coarse.IsConvex ∧
                  coarse.HasComparableDimensions w₁ w₂ w₃ A ∧
                  coarse.IsCKatzTao
                    (ENNReal.ofReal A *
                      Kakeya.realRpowENN rho (-epsilon) *
                      ENNReal.rpow (F.enncard + 1) epsilon) ∧
                  P.FibersAreCFrostman
                    (ENNReal.ofReal A *
                      Kakeya.realRpowENN rho (-epsilon) *
                      ENNReal.rpow (F.enncard + 1) epsilon) ∧
                  P.FibersHaveDensity S.family.deltaMax
                    (ENNReal.ofReal A *
                      Kakeya.realRpowENN rho (-epsilon) *
                      ENNReal.rpow (F.enncard + 1) epsilon)

/-- Section 5: density lower bound for an induced coarse shading. -/
def InducedShadingDensityStatement : Prop :=
  ∀ B : ℝ, 1 ≤ B →
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ A : ℝ, 1 ≤ A ∧
        ∀ fine coarse : BodyFamily,
        fine.IsMeasurable → fine.IsConvex →
        coarse.IsMeasurable → coarse.IsConvex →
        0 < fine.mass →
        ∀ u v w r s t : ℝ,
          fine.HasComparableDimensions u v w B →
          coarse.HasComparableDimensions r s t B →
          ∀ P : Factoring fine coarse,
            ∀ Y : Shading fine,
              ∀ Z : Shading coarse,
                0 < r →
                  ∀ C : ENNReal, 1 ≤ C → C ≠ ⊤ →
                    P.FibersAreCFrostman C →
                    P.IsExactInducedShading Y Z r →
                    ∀ j,
                      ENNReal.rpow
                          (P.fiberShadedMass Y j / P.fiberMass j) 2 *
                          (coarse.body j).volume ≤
                        ENNReal.ofReal A *
                          Kakeya.realRpowENN (u / w) (-epsilon) * C *
                          MeasureTheory.volume (Z.carrier j)

/-- Section 5: factoring and multiplicity proposition. -/
def FactoringMultiplicityStatement : Prop :=
  ∀ B : ℝ, 1 ≤ B →
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ A : ℝ, 1 ≤ A ∧
        ∀ fine coarse : BodyFamily,
        ∀ u v w r s t : ℝ,
          fine.HasComparableDimensions u v w B →
          coarse.HasComparableDimensions r s t B →
          ∀ P : Factoring fine coarse,
            ∀ Y : Shading fine,
              0 < r →
              ∀ C : ENNReal, 1 ≤ C →
              C ≠ ⊤ →
              fine.IsMeasurable → fine.IsConvex →
              coarse.IsMeasurable → coarse.IsConvex →
              0 < Y.mass →
              P.FibersAreCFrostman C →
              ∃ R : FactoringRefinement P Y,
                ∃ mcoarse Mcoarse mfiber Mfiber : ℕ,
                  R.fineRefinement.RetainsMass
                    (Kakeya.realRpowENN (u / w) epsilon *
                      ENNReal.rpow (fine.enncard + 1) (-epsilon) *
                      (ENNReal.ofReal A)⁻¹) ∧
                  R.factoring.IsInducedSubshading
                    R.fineRefinement.shading R.coarseShading r ∧
                  ENNReal.rpow (Y.mass / fine.mass) 2 *
                      R.coarseSubfamily.family.mass ≤
                    ENNReal.ofReal A *
                      Kakeya.realRpowENN (u / w) (-epsilon) *
                      ENNReal.rpow (fine.enncard + 1) epsilon *
                      C * R.coarseShading.mass ∧
                  1 ≤ mcoarse ∧
                  (Mcoarse : ENNReal) ≤
                    ENNReal.ofReal A *
                      Kakeya.realRpowENN (u / w) (-epsilon) *
                      ENNReal.rpow (fine.enncard + 1) epsilon *
                      (mcoarse : ENNReal) ∧
                  R.coarseShading.HasConstantMultiplicity
                    mcoarse Mcoarse ∧
                  1 ≤ mfiber ∧
                  (Mfiber : ENNReal) ≤
                    ENNReal.ofReal A *
                      Kakeya.realRpowENN (u / w) (-epsilon) *
                      ENNReal.rpow (fine.enncard + 1) epsilon *
                      (mfiber : ENNReal) ∧
                  (∀ j, R.factoring.FiberHasConstantMultiplicity
                    R.fineRefinement.shading j mfiber Mfiber) ∧
                  R.coarseShading.HasAverageMultiplicityAtMost
                    (Mcoarse : ENNReal) ∧
                  (∀ j, R.factoring.FiberAverageMultiplicityLE
                    R.fineRefinement.shading j (Mfiber : ENNReal)) ∧
                  (∀ x ∈ R.fineRefinement.shading.union,
                    ∀ i, x ∈ R.fineRefinement.shading.carrier i →
                      ∃ j, R.factoring.parent i = j ∧
                        x ∈ R.coarseShading.carrier j) ∧
                  (∀ x ∈ R.coarseShading.union,
                    ∀ y ∈ R.coarseShading.union,
                      MeasureTheory.volume
                          (R.fineRefinement.shading.union ∩
                            Metric.closedBall x r) ≤
                        ENNReal.ofReal A *
                          Kakeya.realRpowENN (u / w) (-epsilon) *
                          ENNReal.rpow (fine.enncard + 1) epsilon *
                          MeasureTheory.volume
                            (R.fineRefinement.shading.union ∩
                              Metric.closedBall y (2 * r))) ∧
                  Y.HasAverageMultiplicityAtMost
                    (ENNReal.ofReal A *
                      Kakeya.realRpowENN (u / w) (-epsilon) *
                      ENNReal.rpow (fine.enncard + 1) epsilon *
                      (Mcoarse : ENNReal) *
                      (Mfiber : ENNReal))

/-- Section 5: two-scale tube multiplicity reduction. -/
def RhoTubeMultiplicityStatement : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ delta rho : ℝ, 0 < delta → delta ≤ rho → rho ≤ 1 →
      ∀ fine : TubeFamily delta,
        fine.IsInUnitBall →
        fine.IsEssentiallyDistinct →
        ∀ coarse : TubeFamily rho,
          ∀ P : TubeCover fine coarse,
            ∀ Y : TubeShading fine,
              ∀ C : ENNReal, C ≠ ⊤ → P.IsCUniform C →
                fine.toBodyFamily.IsMeasurable →
                coarse.toBodyFamily.IsMeasurable →
                0 < Y.mass →
                ∃ R : FactoringRefinement P.toFactoring Y,
                  ∃ mcoarse Mcoarse mfiber Mfiber : ℕ,
                    R.fineRefinement.RetainsMass
                      (Kakeya.realRpowENN delta epsilon *
                        ENNReal.rpow (fine.enncard + 1) (-epsilon) *
                        (ENNReal.ofReal A)⁻¹) ∧
                    R.factoring.IsInducedSubshading
                      R.fineRefinement.shading R.coarseShading rho ∧
                    (Y.mass / fine.toBodyFamily.mass) *
                        R.coarseSubfamily.family.mass ≤
                      ENNReal.ofReal A *
                        Kakeya.realRpowENN delta (-epsilon) *
                        ENNReal.rpow (fine.enncard + 1) epsilon *
                        C *
                        R.coarseShading.mass ∧
                    1 ≤ mcoarse ∧
                    (Mcoarse : ENNReal) ≤
                      ENNReal.ofReal A *
                        Kakeya.realRpowENN delta (-epsilon) *
                        ENNReal.rpow (fine.enncard + 1) epsilon *
                        C *
                        (mcoarse : ENNReal) ∧
                    R.coarseShading.HasConstantMultiplicity
                      mcoarse Mcoarse ∧
                    1 ≤ mfiber ∧
                    (Mfiber : ENNReal) ≤
                      ENNReal.ofReal A *
                        Kakeya.realRpowENN delta (-epsilon) *
                        ENNReal.rpow (fine.enncard + 1) epsilon *
                        C *
                        (mfiber : ENNReal) ∧
                    (∀ j, R.factoring.FiberHasConstantMultiplicity
                      R.fineRefinement.shading j mfiber Mfiber) ∧
                    (∀ x ∈ R.fineRefinement.shading.union,
                      ∀ i, x ∈ R.fineRefinement.shading.carrier i →
                        ∃ j, R.factoring.parent i = j ∧
                          x ∈ R.coarseShading.carrier j) ∧
                    (∀ x ∈ R.coarseShading.union,
                      ∀ y ∈ R.coarseShading.union,
                        MeasureTheory.volume
                            (R.fineRefinement.shading.union ∩
                              Metric.closedBall x rho) ≤
                          ENNReal.ofReal A *
                            Kakeya.realRpowENN delta (-epsilon) *
                            ENNReal.rpow (fine.enncard + 1) epsilon *
                            C *
                            MeasureTheory.volume
                              (R.fineRefinement.shading.union ∩
                                Metric.closedBall y (2 * rho))) ∧
                    (∀ x ∈ R.coarseShading.union,
                      MeasureTheory.volume R.coarseShading.union *
                          MeasureTheory.volume
                            (R.fineRefinement.shading.union ∩
                              Metric.closedBall x rho) ≤
                        ENNReal.ofReal A *
                          Kakeya.realRpowENN delta (-epsilon) *
                          ENNReal.rpow (fine.enncard + 1) epsilon *
                          MeasureTheory.volume
                            R.fineRefinement.shading.union *
                          MeasureTheory.volume (Metric.closedBall x rho)) ∧
                    Y.HasAverageMultiplicityAtMost
                      (ENNReal.ofReal A *
                        Kakeya.realRpowENN delta (-epsilon) *
                        ENNReal.rpow (fine.enncard + 1) epsilon *
                        C *
                        (Mcoarse : ENNReal) *
                        (Mfiber : ENNReal))

/-- Section 6: Katz--Tao multiplicity estimate for planks. -/
def PlankKatzTaoStatement : Prop :=
  ∀ beta : ℝ, KatzTaoEstimate beta →
    ∀ A : ℝ, 1 ≤ A →
      ∀ epsilon : ℝ, 0 < epsilon →
        ∃ eta b₀ : ℝ, 0 < eta ∧ 0 < b₀ ∧
          ∀ a b : ℝ, 0 < a → a ≤ b → b ≤ b₀ →
          ∀ P : PlankFamily a b A,
            0 < P.family.mass →
            P.family.IsInUnitBall →
            ∀ Y : Shading P.family,
              Y.IsLambdaDense (Kakeya.realRpowENN a eta) →
              ∀ gamma : ℝ, 0 ≤ gamma → gamma ≤ 1 →
                PlankSlabNonconcentration P eta gamma →
                Y.HasAverageMultiplicityAtMost
                  (Kakeya.realRpowENN a (-epsilon) *
                    ENNReal.rpow P.family.deltaMax (1 - beta) *
                    Kakeya.realRpowENN (a / b) (gamma * beta) *
                    ENNReal.rpow P.family.enncard beta)

/-- Section 6: Frostman multiplicity estimate for planks. -/
def PlankFrostmanStatement : Prop :=
  ∀ beta : ℝ, FrostmanEstimate beta →
    ∀ A : ℝ, 1 ≤ A →
      ∀ epsilon : ℝ, 0 < epsilon →
        ∃ eta b₀ : ℝ, 0 < eta ∧ 0 < b₀ ∧
          ∀ a b : ℝ, 0 < a → a ≤ b → b ≤ b₀ →
          ∀ P : PlankFamily a b A,
            0 < P.family.mass →
            P.family.IsInUnitBall →
            ∀ Y : Shading P.family,
              Y.IsLambdaDense (Kakeya.realRpowENN a eta) →
              ∀ M : ℝ, 1 ≤ M →
                ThickenedPlankNonconcentration P M →
                Y.HasAverageMultiplicityAtMost
                  (Kakeya.realRpowENN a (-epsilon) *
                    ENNReal.rpow
                      (P.family.frostmanConstantIn unitBall.carrier)
                      (1 - beta / 2) *
                    Kakeya.realRpowENN M (beta / 2) *
                    Kakeya.realRpowENN (a / b) 1 *
                    Kakeya.realRpowENN b (-2 * beta) *
                    ENNReal.rpow
                      (Kakeya.realRpowENN b 2 * P.family.enncard)
                      (1 - beta / 2))

/-- Section 6: the two flat-prism factoring alternatives. -/
def FlatPrismFactoringStatement : Prop :=
  ∀ beta : ℝ, KatzTaoEstimate beta → FrostmanEstimate beta →
    ∀ A : ℝ, 1 ≤ A →
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ eta delta₀ : ℝ, 0 < eta ∧ 0 < delta₀ ∧
        ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
          ∀ F : TubeFamily delta,
            F.IsInUnitBall →
            F.IsEssentiallyDistinct →
            ∀ Y : TubeShading F,
              Y.IsLambdaDense (Kakeya.realRpowENN delta eta) →
              ∀ U : UniformTubeStructure F,
                U.uniformity ≤ Kakeya.realRpowENN delta (-eta) →
              ∀ a b : ℝ, 0 < a → a ≤ b → b ≤ 1 →
                ((∃ rho : AdmissibleScale delta,
                    HasLocalPlankFactoring
                      (a := a) (b := b) (A := A) (U.cover rho)
                      (Kakeya.realRpowENN delta (-eta))) →
                    Y.HasAverageMultiplicityAtMost
                      (Kakeya.realRpowENN delta (-epsilon - 2 * beta) *
                        ENNReal.rpow
                          (F.toBodyFamily.frostmanConstantIn unitBall.carrier)
                          (1 - beta / 2) *
                        Kakeya.realRpowENN (a / b) (3 * beta / 2) *
                        ENNReal.rpow
                          (Kakeya.realRpowENN delta 2 * F.enncard)
                          (1 - beta / 2))) ∧
                  ((∃ rho : AdmissibleScale delta,
                    HasGlobalPlankFactoring
                      (a := a) (b := b) (A := A) (U.coarse rho)
                      (Kakeya.realRpowENN delta (-eta))) →
                    Y.HasAverageMultiplicityAtMost
                      (Kakeya.realRpowENN delta (-epsilon) *
                        ENNReal.rpow F.toBodyFamily.deltaMax (1 - beta) *
                        Kakeya.realRpowENN (a / b) beta *
                        ENNReal.rpow F.enncard beta))

/-- Section 7(B): derive the every-scale Katz--Tao estimate from sticky Kakeya. -/
def KatzTaoEveryScaleFromStickyStatement : Prop :=
  StickyKakeyaHypothesis → KatzTaoEveryScaleEstimate

/-- Cardinality condition defining the very-not-sticky regime in Section 9. -/
def IsVeryNotSticky {δ : ℝ} {F : TubeFamily δ}
    (U : UniformTubeStructure F) (epsilonScale zeta : ℝ) : Prop :=
  ∀ rho : AdmissibleScale δ,
    Kakeya.realRpowENN δ (1 - epsilonScale) ≤ ENNReal.ofReal rho.1 →
    ENNReal.ofReal rho.1 ≤ Kakeya.realRpowENN δ epsilonScale →
      Kakeya.realRpowENN rho.1 (-2 - zeta) ≤ (U.coarse rho).enncard

/-- Section 9: the very-not-sticky case used inside Main Lemma 2. -/
def VeryNotStickyStatement : Prop :=
  ∀ beta : ℝ, 0 < beta → beta ≤ 1 →
    KatzTaoEstimate beta → FrostmanEstimate beta →
      ∃ epsilonScale : ℝ, 0 < epsilonScale ∧
        ∀ zeta : ℝ, 0 < zeta →
          ∃ nu eta delta₀ : ℝ,
            0 < nu ∧ 0 < eta ∧ 0 < delta₀ ∧ delta₀ ≤ 1 ∧
              ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
                ∀ F : TubeFamily delta,
                  F.Nonempty →
                  F.IsInUnitBall →
                  F.IsEssentiallyDistinct →
                  F.toBodyFamily.IsCKatzTao
                    (Kakeya.realRpowENN delta (-eta)) →
                  ∀ U : UniformTubeStructure F,
                    IsVeryNotSticky U epsilonScale zeta →
                    ∀ Y : TubeShading F,
                      Y.IsLambdaDense
                        (Kakeya.realRpowENN delta eta) →
                      Y.HasAverageMultiplicityAtMost
                        (Kakeya.realRpowENN delta nu *
                          ENNReal.rpow F.enncard beta)

/-- Section 8: Main Lemma 1. -/
def MainLemma1Statement : Prop :=
  StickyKakeyaHypothesis →
    ∀ beta : ℝ, 0 ≤ beta → beta ≤ 1 →
      KatzTaoEstimate beta → FrostmanEstimate beta

/--
Section 9: Main Lemma 2, including a positive exponent-drop function that is
monotone on `[0,1]`, as required by the final finite iteration.
-/
def MainLemma2Statement : Prop :=
  StickyKakeyaHypothesis →
    VeryNotStickyStatement →
    ∃ nu : ℝ → ℝ,
      MonotoneOn nu (Set.Icc 0 1) ∧
      ∀ beta : ℝ, 0 < beta → beta ≤ 1 →
        0 < nu beta ∧ nu beta < beta ∧
          (KatzTaoEstimate beta → FrostmanEstimate beta →
            KatzTaoEstimate (beta - nu beta))

/--
Final parameter iteration.  The two Main Lemmas are ordinary proof arguments;
there is no axiom and no imported theorem containing a hidden placeholder.
-/
def StickyImpliesGeneralStatement : Prop :=
  StickyKakeyaHypothesis →
    VeryNotStickyStatement →
    MainLemma1Statement →
    MainLemma2Statement →
    GeneralKakeyaStatement

end Kakeya.Streamlined
