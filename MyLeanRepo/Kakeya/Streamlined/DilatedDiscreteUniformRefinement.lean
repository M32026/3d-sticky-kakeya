import MyLeanRepo.Kakeya.Streamlined.FiniteGridDilatedCoverExistence.Proof
import MyLeanRepo.Kakeya.Streamlined.DilatedCoverUniformization.Proof
import MyLeanRepo.Kakeya.Streamlined.RestrictDistinctDilatedTubeCover.Proof
import MyLeanRepo.Kakeya.Streamlined.SubpolynomialBounds
import MyLeanRepo.Kakeya.Streamlined.DilatedTubeCover.FullContainmentFibers

/-!
# Legacy quantitative grid refinement with dilated tube covers

This historical regularization uses the paper scale grid and the repaired
geometric dilation, but its branching constant is a runtime subpolynomial
quantity. It is internal/legacy data rather than the canonical finite-grid
`∼` interface.
-/

noncomputable section

namespace Kakeya.Streamlined

/-- Legacy quantitative structure on the finite distinguished scale grid. -/
structure DilatedDiscreteUniformTubeStructure
    {delta A : ℝ} (F : TubeFamily delta)
    (hdelta_le_one : delta ≤ 1) where
  coarse :
    ∀ k : UniformScaleIndex delta,
      TubeFamily (uniformScale delta hdelta_le_one k).1
  cover :
    ∀ k, DilatedTubeCover A F (coarse k)
  coarse_distinct :
    ∀ k, (coarse k).IsEssentiallyDistinct
  assignedUniformity : ENNReal
  one_le_assignedUniformity : 1 ≤ assignedUniformity
  assignedUniformity_ne_top : assignedUniformity ≠ ⊤
  assignedUniform :
    ∀ k, (cover k).toFactoring.FibersAreCUniform assignedUniformity
  uniformity : ENNReal
  assignedUniformity_le_uniformity :
    assignedUniformity ≤ uniformity
  one_le_uniformity : 1 ≤ uniformity
  uniformity_ne_top : uniformity ≠ ⊤
  uniform :
    ∀ k, (cover k).FullContainmentFibersAreCUniform uniformity

/--
Every sufficiently small essentially-distinct shaded tube family in the unit
ball has a nonempty subfamily retaining `delta^epsilon` shaded mass and
admitting quantitatively balanced dilated covers on the distinguished grid.
-/
def DilatedDiscreteUniformRefinementStatement : Prop :=
  ∃ A : ℝ, 1 ≤ A ∧
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
        ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
          ∀ F : TubeFamily delta,
            F.Nonempty →
            F.IsInUnitBall →
            F.IsEssentiallyDistinct →
            ∀ Y : TubeShading F, 0 < Y.mass →
              ∃ S : TubeSubfamily F,
                S.Nonempty ∧
                S.RetainsShadedMass Y
                  (Kakeya.realRpowENN delta epsilon) ∧
                ∃ hdelta_le_one : delta ≤ 1,
                  ∃ U : DilatedDiscreteUniformTubeStructure
                      (A := A) S.family hdelta_le_one,
                    U.uniformity ≤
                      Kakeya.realRpowENN delta (-epsilon)

end Kakeya.Streamlined
