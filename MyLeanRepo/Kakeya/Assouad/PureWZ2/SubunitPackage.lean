import MyLeanRepo.Kakeya.Assouad.PureWZ2.DirectWolffFloor
import MyLeanRepo.Kakeya.Assouad.PureWZ2.SubunitCeiling
import MyLeanRepo.Kakeya.Assouad.PureWZ2.WolffFloorFromAssertionD

/-!
# Pure WZ2 Node 1 subunit package

The direct complete-full-fiber Wolff floor fills the left branch of the
historical refinement interface.  No refinement record or assigned-fiber
model is needed by this route.
-/

noncomputable section

namespace Kakeya.Assouad

/-- A direct Wolff floor is a valid realization of the frozen refinement
interface through its theorem-sufficient left branch. -/
theorem pure_wz2_full_fiber_refinement_of_wolff_floor
    (hfloor : PureWZ2WolffVolumeFloor) :
    PureWZ2FullFiberAssertionDRefinementStatement := by
  intro outputEpsilon assertionEpsilon kappa assertionEta
    houtputEpsilon _ _ _ _
  rcases hfloor outputEpsilon houtputEpsilon with
    ⟨inputEta, delta₀, hinputEta, hdelta₀,
      hdelta₀One, hmain⟩
  refine
    ⟨inputEta, delta₀, hinputEta, hdelta₀,
      hdelta₀One, ?_⟩
  intro delta hdelta hdeltaBound family hfamilyNonempty
    shading hCWA hdense
  exact Or.inl <|
    hmain delta hdelta hdeltaBound family
      hfamilyNonempty hCWA shading hdense

/-- Complete frozen Node 1 package from the direct literal-full-fiber route. -/
theorem pure_wz2_node01_subunit_package :
    PureWZ2SubunitPackageStatement := by
  let hfloor : PureWZ2WolffVolumeFloor :=
    pure_wz2_direct_wolff_floor
  have hrefinement :
      PureWZ2FullFiberAssertionDRefinementStatement :=
    pure_wz2_full_fiber_refinement_of_wolff_floor hfloor
  have hceiling :
      ∃ ceiling : ℝ,
        ceiling < 1 ∧
        ¬ PureWZ2Admissible ceiling :=
    concrete_ceiling_from_wolff_floor hfloor
  exact
    ⟨hrefinement,
      pure_wz2_wolff_floor_from_assertionD,
      pure_wz2_wolff_floor_implies_subunit_ceiling,
      hfloor,
      hceiling⟩

end Kakeya.Assouad

end
