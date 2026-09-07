import MyLeanRepo.Kakeya.Assouad.PureWZ2.CompleteFiberNormalization
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4DirectUniversal
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4FixedGridBoundaryRemoval
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4OnePassTreeCleanup
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4SynchronizedRealization

/-!
# Pure WZ2 Node 3: prop sticky

This target packages the closed normalization, universal continuation, and
synchronized nonvacuous realization.
-/

namespace Kakeya.Assouad

theorem pure_wz2_node03_prop_sticky :
    PureWZ2PropStickyStatement := by
  intro _subunit _criticalExtraction
  exact
    ⟨{
      normalizationExponent := 0
      logExponent := 61
      normalization :=
        pureWZ2_cropped_critical_normalization_completeFiber
      continuation :=
        Prop62PaperAudit.V4.pureWZ2_cropped_prop_sticky_v4
          Prop62PaperAudit.V4.fixed_grid_boundary_removal
          Prop62PaperAudit.V4.one_pass_tree_cleanup
      realization :=
        Prop62PaperAudit.V4.pureWZ2_prop_sticky_realization_v4
          Prop62PaperAudit.V4.fixed_grid_boundary_removal
          Prop62PaperAudit.V4.one_pass_tree_cleanup
      rootReentrant :=
        Prop62PaperAudit.V4.pureWZ2_prop_sticky_reentrant_realization_v4
          Prop62PaperAudit.V4.fixed_grid_boundary_removal
          Prop62PaperAudit.V4.one_pass_tree_cleanup
      kernel :=
        Prop62PaperAudit.V4.pureWZ2_prop_sticky_reentry_kernel_v4
          Prop62PaperAudit.V4.fixed_grid_boundary_removal
          Prop62PaperAudit.V4.one_pass_tree_cleanup
    }⟩

end Kakeya.Assouad
