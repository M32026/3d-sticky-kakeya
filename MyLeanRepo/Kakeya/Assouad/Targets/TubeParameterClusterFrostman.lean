import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.CinematicBridge3D
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterClusterFrostmanStatement
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectionFrostmanHelpers
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterClusterFinalAssembly

/-!
WZ2 Section 7: construct the replication-invariant weighted cluster
Frostman package for one positive `c`-window.
-/

namespace Kakeya.Assouad

theorem tube_parameter_cluster_frostman :
    TubeParameterClusterFrostmanStatement := by
  intro delta F hF_nonempty h_params C hC_one hC_top hFrost w hw_pos hw_delta hw100 Y c0 hwindow lambda hlambda_zero hlambda_top hlambda_dense
  exact tube_parameter_cluster_frostman_assembly F hF_nonempty h_params C hC_one hC_top hFrost w hw_pos hw_delta hw100 Y c0 hwindow lambda hlambda_zero hlambda_top hlambda_dense

end Kakeya.Assouad
