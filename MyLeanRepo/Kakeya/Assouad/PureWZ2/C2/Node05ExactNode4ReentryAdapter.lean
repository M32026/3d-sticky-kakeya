import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains

/-!
# Exact Node 4 re-entry adapter for Node 5

The frozen Node 4 theorem exports only the public conjunction
`PureWZ2PaperADBridgeStatement ∧ PureWZ2GrainsFromCriticalStatement`.
In particular, its existential grain configuration cannot be projected to a
refinement of an arbitrary caller-supplied cropped extremizer.

This Node-5-private module therefore does exactly two things:

* it provides thin projections from the public Node 4 conjunction;
* it appends the dependent same-extremizer theorem only when that theorem is
  supplied as an explicit receipt.

No family, shading, loss schedule, or re-entry provenance is reconstructed by
this adapter.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Node-5-private restoration on one already selected cropped extremizer.

This is intentionally not a conjunct of `PureWZ2GrainsStatement`: the frozen
Node 4 theorem only returns a fresh configuration from a critical package. -/
def PureWZ2Node5SameExtremizerRestorationAt
    (sigma structuralLoss finalLoss delta : ℝ) : Prop :=
  ∀ targetFamily : Kakeya.Streamlined.TubeFamily delta,
    ∀ targetShading : WZ1PaperTubeShading targetFamily,
      WZ1PaperIsLineClass targetFamily →
      WZ2PaperCroppedIsExtremal
          sigma structuralLoss targetFamily targetShading →
        Nonempty
          (PureWZ2GrainRefinementData targetShading sigma finalLoss)

/-- The exact public result obtained after applying the frozen Node 4 theorem
to its three predecessor proofs. -/
def PureWZ2Node05PublicNode4Output :=
  PureWZ2PaperADBridgeStatement ∧
    PureWZ2GrainsFromCriticalStatement

/-- Apply Node 4 and expose its public conjunction without strengthening it. -/
theorem pureWZ2_node05_public_node4_output
    (node4 : PureWZ2GrainsStatement)
    (subunit : PureWZ2SubunitPackageStatement)
    (extraction : PureWZ2CriticalExtractionStatement)
    (sticky : PureWZ2PropStickyStatement) :
    PureWZ2Node05PublicNode4Output :=
  node4 subunit extraction sticky

/-- Thin projection of the paper AD bridge from the public Node 4 output. -/
theorem pureWZ2_node05_ad_bridge_of_node4
    (node4 : PureWZ2GrainsStatement)
    (subunit : PureWZ2SubunitPackageStatement)
    (extraction : PureWZ2CriticalExtractionStatement)
    (sticky : PureWZ2PropStickyStatement) :
    PureWZ2PaperADBridgeStatement :=
  (pureWZ2_node05_public_node4_output
    node4 subunit extraction sticky).1

/-- Thin projection of the paper-facing grain existence theorem from the
public Node 4 output. -/
theorem pureWZ2_node05_grains_from_critical_of_node4
    (node4 : PureWZ2GrainsStatement)
    (subunit : PureWZ2SubunitPackageStatement)
    (extraction : PureWZ2CriticalExtractionStatement)
    (sticky : PureWZ2PropStickyStatement) :
    PureWZ2GrainsFromCriticalStatement :=
  (pureWZ2_node05_public_node4_output
    node4 subunit extraction sticky).2

/-- Explicit receipt for the one Node-5 field that is not present in the
frozen public Node 4 conjunction. -/
structure PureWZ2Node05ExactNode4ReentryReceipt where
  grainsAtExtremizer : PureWZ2GrainsAtExtremizerStatement

/-- The minimal Node-5-private view of Node 4: the two public projections and
one explicitly supplied dependent re-entry receipt. -/
structure PureWZ2Node05ExactNode4ReentryData where
  paperADBridge : PureWZ2PaperADBridgeStatement
  grainsFromCritical : PureWZ2GrainsFromCriticalStatement
  grainsAtExtremizer : PureWZ2GrainsAtExtremizerStatement

/-- The quantifier-ordered private schedule extracted from the explicit
same-extremizer receipt.  The input loss and scale threshold are fixed before
the runtime configuration, exactly as required by hierarchy iteration. -/
structure PureWZ2Node05SameExtremizerSchedule
    (sigma finalLoss : ℝ) where
  inputLoss : ℝ
  delta₀ : ℝ
  inputLoss_pos : 0 < inputLoss
  inputLoss_le_final : inputLoss ≤ finalLoss
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  restore :
    ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
      PureWZ2Node5SameExtremizerRestorationAt
        sigma inputLoss finalLoss delta

/-- Assemble the private Node 5 view without claiming that the dependent
re-entry field follows from the public Node 4 conjunction. -/
theorem PureWZ2Node05ExactNode4ReentryData.ofNode4
    (node4 : PureWZ2GrainsStatement)
    (subunit : PureWZ2SubunitPackageStatement)
    (extraction : PureWZ2CriticalExtractionStatement)
    (sticky : PureWZ2PropStickyStatement)
    (receipt : PureWZ2Node05ExactNode4ReentryReceipt) :
    PureWZ2Node05ExactNode4ReentryData where
  paperADBridge :=
    pureWZ2_node05_ad_bridge_of_node4
      node4 subunit extraction sticky
  grainsFromCritical :=
    pureWZ2_node05_grains_from_critical_of_node4
      node4 subunit extraction sticky
  grainsAtExtremizer := receipt.grainsAtExtremizer

/-- Select the private same-extremizer loss and scale threshold before any
runtime family or shading.  This theorem uses only the explicitly supplied
Node-5 receipt; it does not derive the stronger conclusion from Node 4. -/
theorem PureWZ2Node05ExactNode4ReentryData.sameExtremizerSchedule
    (data : PureWZ2Node05ExactNode4ReentryData)
    {sigma finalLoss : ℝ}
    (critical : PureWZ2CriticalPackage sigma)
    (hfinalLoss : 0 < finalLoss) :
    Nonempty (PureWZ2Node05SameExtremizerSchedule sigma finalLoss) := by
  rcases data.grainsAtExtremizer sigma critical finalLoss hfinalLoss with
    ⟨inputLoss, delta₀, hinputLoss, hinputFinal, hdelta₀, hdelta₀One, restore⟩
  exact ⟨{
    inputLoss := inputLoss
    delta₀ := delta₀
    inputLoss_pos := hinputLoss
    inputLoss_le_final := hinputFinal
    delta₀_pos := hdelta₀
    delta₀_le_one := hdelta₀One
    restore := restore
  }⟩

end Kakeya.Assouad

end
