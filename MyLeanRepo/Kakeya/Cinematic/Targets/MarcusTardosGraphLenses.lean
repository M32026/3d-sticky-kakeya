import MyLeanRepo.Kakeya.Cinematic.MarcusTardos.GraphLensBridge.Bound

/-!
# From intersection-reverse sequences to the graph-lens bound

This target constructs the three Marcus--Tardos cyclic list families
(lens-faces, moon-faces, and inverse-faces) and applies Corollary 6.
-/

namespace Kakeya.Cinematic

theorem graph_lens_bound_from_sequences :
    GraphLensBoundFromSequencesStatement := by
  exact GraphLensBridge.graph_lens_bound_from_sequences_closed

end Kakeya.Cinematic
