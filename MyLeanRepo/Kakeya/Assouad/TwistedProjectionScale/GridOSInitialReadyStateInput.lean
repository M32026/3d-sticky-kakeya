import MyLeanRepo.Kakeya.Assouad.Targets.GridOSInitialParameterAbsorption
import MyLeanRepo.Kakeya.Assouad.Targets.GridOSInitialProjectionContainment
import MyLeanRepo.Kakeya.Assouad.Targets.GridOSInitialReadyState

/-!
# Closed direct initial ready-state input

The two nontrivial initial leaves and their conditional adapter are all
closed.  This module exposes the direct producer consumed by the final finite
iteration.
-/

namespace Kakeya.Assouad

theorem grid_os_initial_ready_state_input :
    GridOSInitialReadyStateInput :=
  grid_os_initial_ready_state
    grid_os_initial_parameter_absorption
    grid_os_initial_projection_containment

end Kakeya.Assouad
