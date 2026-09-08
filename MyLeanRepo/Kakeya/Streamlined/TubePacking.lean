import MyLeanRepo.Kakeya.Streamlined.Basic

/-!
# Packing tubes inside a plank

This module states the phase-space packing bound used when plank incidence
problems are reduced to tube incidence problems.
-/

noncomputable section

namespace Kakeya.Streamlined

/--
For each comparability constant `A`, an `a × b × 1` plank contains at most
`O_A((a b / delta²)²)` essentially distinct `delta`-tubes.  One factor
counts transverse positions and the other counts directions.
-/
def TubePackingInPlankStatement : Prop :=
  ∀ A : ℝ, 1 ≤ A →
    ∃ C : ℝ, 0 < C ∧
      ∀ delta a b : ℝ,
        0 < delta → delta ≤ a → a ≤ b → b ≤ 1 →
        ∀ plank : Body,
        ∀ frame : Point3 ≃ᵃⁱ[ℝ] Point3,
          plank.HasDimensionsInFrame frame a b 1 A →
          ∀ F : TubeFamily delta,
            F.IsEssentiallyDistinct →
            (∀ i, (F.tube i).carrier ⊆ plank.carrier) →
            F.enncard ≤
              ENNReal.ofReal
                (C * (a * b / delta ^ 2) ^ 2)

end Kakeya.Streamlined
