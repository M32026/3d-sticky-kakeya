import MyLeanRepo.Kakeya.Streamlined.UniformRefinement.SingleScaleCover

/-!
# Close essentially-distinct one-scale refinement

The raw phase-space grid gives exact parent containment and `O(rho)`
midpoint/direction errors, but its coarse family is not definitionally
essentially distinct.  Reassigning deleted parents to a maximal
essentially-distinct representative can move a chosen unit-segment midpoint
by `O(1)` in its axial direction.  This is harmless for the paper's coaxial
line convention, but it must not destroy transverse or directional
`O(rho)` control.

The faithful output therefore combines a fixed endpoint dilation with
scale-local transverse midpoint and orientation-free direction control.
No fine-tube refinement is needed: the existing maximal-ED reassignment keeps
all fine indices and only changes their coarse parent.
-/

noncomputable section

namespace Kakeya.Streamlined

/--
At one prescribed scale, an essentially-distinct unit-ball fine family admits
a coaxial-local dilated cover by an essentially-distinct coarse family.
-/
def CloseDistinctTubeCoverStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ delta rho : ℝ,
      0 < delta → delta ≤ rho → rho ≤ 1 →
      ∀ F : TubeFamily delta,
        F.Nonempty →
        F.IsInUnitBall →
        F.IsEssentiallyDistinct →
        ∃ coarse : TubeFamily rho,
          ∃ cover : LocalDilatedTubeCover 1000 C F coarse,
            coarse.IsEssentiallyDistinct

end Kakeya.Streamlined
