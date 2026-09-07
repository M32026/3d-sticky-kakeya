import MyLeanRepo.Kakeya.Cinematic.Section5.LevelSetInputs
import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.Clusters

/-!
# Finite ball cover for a localized tangent family
-/

namespace Kakeya.Cinematic

theorem finite_tangent_ball_cover :
    FiniteTangentBallCoverStatement := by
  intro K D diameter radius hD hdiameter hradius family hfamily H hH hdiam
  exact
    finite_family_cluster_cover hfamily hD hH hdiameter hradius hdiam

end Kakeya.Cinematic
