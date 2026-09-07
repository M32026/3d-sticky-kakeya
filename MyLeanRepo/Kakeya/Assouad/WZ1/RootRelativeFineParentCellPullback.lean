import MyLeanRepo.Kakeya.Assouad.WZ1.RootRelativeFineParentCellPullbackStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.FineParentCellPullback

/-!
# Root-relative fine parent-cell pullback

Expose one root-relative schedule coordinate as its ordinary single-scale
view, then apply the closed fine parent-cell pullback. The output remains on
the original root family.
-/

namespace Kakeya.Assouad

theorem wz1_root_relative_fine_parent_cell_pullback :
    WZ1RootRelativeFineParentCellPullbackStatement := by
  have hmain :
      WZ1Lemma17FineParentCellPullbackStatement :=
    fineParentCellPullback_statement
  intro epsilon₁ epsilon₂
    hepsilon₁ hepsilon₂ hepsilon₁₂ hepsilonSum
  rcases
      hmain epsilon₁ epsilon₂
        hepsilon₁ hepsilon₂ hepsilon₁₂ hepsilonSum with
    ⟨rho₀, hrho₀Pos, hrho₀Upper, hinner⟩
  refine ⟨rho₀, hrho₀Pos, hrho₀Upper, ?_⟩
  intro delta sigma F U Y scaleCount depth schedule
    cover coordinate propertyThree hsigma hsigmaOne
    hschedulePos hscheduleLe habsorb hsub hextremal
  let first := cover.toBalancedCoverData coordinate
  exact
    hinner (first := first) propertyThree
      hsigma hsigmaOne hschedulePos hscheduleLe
      habsorb hsub hextremal

end Kakeya.Assouad
