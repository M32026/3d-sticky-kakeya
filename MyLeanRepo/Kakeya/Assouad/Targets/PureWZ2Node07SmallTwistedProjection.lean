import MyLeanRepo.Kakeya.Assouad.PureWZ2.Node7FromCritical
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Node7bPreparation

/-!
# Pure WZ2 Node 7: small twisted projection

This module closes Node 7 by assembling the paper-facing projection output
and the provenance-preserving Section-7 preparation.
-/

namespace Kakeya.Assouad

theorem pure_wz2_node07_small_twisted_projection :
    PureWZ2SmallTwistedProjectionStatement := by
  intro h_subunit h_critical h_propsticky h_grains h_c2grains h_largeslope
  exact ⟨
    pure_wz2_node7_from_critical h_subunit h_critical h_propsticky
      h_grains h_c2grains h_largeslope,
    pure_wz2_node7b_preparation h_subunit h_critical h_propsticky
      h_grains h_c2grains h_largeslope⟩

end Kakeya.Assouad
