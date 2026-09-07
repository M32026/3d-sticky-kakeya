import MyLeanRepo.Kakeya.Assouad.TubeSegmentProjectionCoveringFromFiber
import MyLeanRepo.Kakeya.Assouad.TubeSegmentProjectionFiberVolume

/-! WZ Lemma 30: projection covering lower bound for a full tube segment. -/

namespace Kakeya.Assouad

theorem tube_segment_projection_covering_lower_bound :
    TubeSegmentProjectionCoveringLowerBoundStatement := by
  exact tube_segment_projection_covering_from_fiber
    tube_segment_projection_fiber_volume

end Kakeya.Assouad
