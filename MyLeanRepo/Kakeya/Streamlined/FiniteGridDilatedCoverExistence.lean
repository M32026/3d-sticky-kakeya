import MyLeanRepo.Kakeya.Streamlined.SingleScaleTubeCover.Proof
import MyLeanRepo.Kakeya.Streamlined.UniformScaleGrid

/-!
# Dilated covers on the finite paper scale grid

This packages the closed single-scale construction simultaneously at every
distinguished paper scale.  No transition map or cross-scale nesting is
asserted.
-/

noncomputable section

namespace Kakeya.Streamlined

def FiniteGridDilatedCoverExistenceStatement : Prop :=
  ∃ A : ℝ, 1 ≤ A ∧
    ∀ {delta : ℝ}, 0 < delta →
      ∀ hdelta_le_one : delta ≤ 1,
      ∀ F : TubeFamily delta,
        F.Nonempty →
        F.IsInUnitBall →
        F.IsEssentiallyDistinct →
        ∃ coarse : ∀ k : UniformScaleIndex delta,
            TubeFamily (uniformScale delta hdelta_le_one k).1,
          ∃ cover : ∀ k, DilatedTubeCover A F (coarse k),
            ∀ k, (coarse k).IsEssentiallyDistinct

end Kakeya.Streamlined
