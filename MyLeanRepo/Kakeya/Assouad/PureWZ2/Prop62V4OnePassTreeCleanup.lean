import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62PaperAudit.StatementsV4

/-!
# One-pass stability of a finite CWA tree

Closed concept module for the tree-cleanup input used by the reusable
Proposition 6.2 kernel.
-/

namespace Kakeya.Assouad.Prop62PaperAudit.V4

theorem one_pass_tree_cleanup :
    OnePassTreeCleanupStatement := by
  intro Leaf Node instLeaf instLeafDecidable instNode
    instNodeDecidable depth tree selected _hselected
  let coreOutput := tree.coreOutput selected
  exact
    ⟨{
      core := coreOutput.core
      core_subset := coreOutput.core_subset
      global_retention := coreOutput.global_retention
      node_density := coreOutput.node_density
      weighted_retention := by
        intro weight weightLevel hlower hupper
        exact tree.dyadic_weight_retention
          selected weight weightLevel hlower hupper
      local_cwa_transfer := by
        intro level hlevel node hnonempty constant
          volumeFactor count hmono hambient
        exact tree.local_cwa_transfer
          selected hlevel node hnonempty constant volumeFactor
          count hmono hambient
    }⟩

end Kakeya.Assouad.Prop62PaperAudit.V4
