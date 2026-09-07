import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricPacketProducer

/-!
# Proposition 6.2: pull an ambient final core into the complete packet hull

The metric mesh is constructed on a union of complete `s`-packets.  The one
augmented-tree cleanup is performed on the original ambient leaf family.
Whenever its output lies in that complete packet hull, there is a canonical
finite pullback with exact image equality.  No new tube-family selection is
performed here.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

structure PureWZ2Prop62PacketHullCorePullbackData
    {delta scale rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    {oldData : WZ2PaperPureScaleCoverData fine scale C}
    {width M : ℝ}
    (metric :
      PureWZ2Prop62MetricPacketOutput
        (rho := rho) oldData width M)
    (ambientCore : Finset (Fin fine.card)) where
  ambientCore_subset_hull :
    ambientCore ⊆ metric.mesh.complete.selectedFineIndices
  pulledBack : Finset (Fin metric.selectedFine.card)
  pulledBack_eq :
    pulledBack =
      Finset.univ.filter fun source =>
        metric.mesh.complete.selectedFine.embedding source ∈ ambientCore
  image_eq :
    Finset.image metric.mesh.complete.selectedFine.embedding pulledBack =
      ambientCore

noncomputable def pureWZ2_prop62_packetHull_core_pullback
    {delta scale rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    {oldData : WZ2PaperPureScaleCoverData fine scale C}
    {width M : ℝ}
    (metric :
      PureWZ2Prop62MetricPacketOutput
        (rho := rho) oldData width M)
    (ambientCore : Finset (Fin fine.card))
    (ambientCoreSubset :
      ambientCore ⊆ metric.mesh.complete.selectedFineIndices) :
    PureWZ2Prop62PacketHullCorePullbackData metric ambientCore := by
  let pulledBack : Finset (Fin metric.selectedFine.card) :=
    Finset.univ.filter fun source =>
      metric.mesh.complete.selectedFine.embedding source ∈ ambientCore
  have imageEq :
      Finset.image metric.mesh.complete.selectedFine.embedding pulledBack =
        ambientCore := by
    ext ambientSource
    constructor
    · intro sourceImage
      rcases Finset.mem_image.mp sourceImage with
        ⟨source, sourceMem, sourceEq⟩
      have sourceCore :
          metric.mesh.complete.selectedFine.embedding source ∈ ambientCore :=
        (Finset.mem_filter.mp sourceMem).2
      rwa [sourceEq] at sourceCore
    · intro sourceCore
      have sourceHull :
          ambientSource ∈ metric.mesh.complete.selectedFineIndices :=
        ambientCoreSubset sourceCore
      rcases
          metric.mesh.complete.selectedFine_ambient_surjective
            ambientSource sourceHull
        with
        ⟨source, sourceEq⟩
      exact
        Finset.mem_image.mpr
          ⟨source,
            Finset.mem_filter.mpr
              ⟨Finset.mem_univ source, by
                rwa [sourceEq]⟩,
            sourceEq⟩
  exact
    {
      ambientCore_subset_hull := ambientCoreSubset
      pulledBack := pulledBack
      pulledBack_eq := rfl
      image_eq := imageEq
    }

namespace PureWZ2Prop62PacketHullCorePullbackData

variable
    {delta scale rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    {oldData : WZ2PaperPureScaleCoverData fine scale C}
    {width M : ℝ}
    {metric :
      PureWZ2Prop62MetricPacketOutput
        (rho := rho) oldData width M}
    {ambientCore : Finset (Fin fine.card)}
    (pullback :
      PureWZ2Prop62PacketHullCorePullbackData metric ambientCore)

/-- Ambient fine subfamily enumerating the one final tree core. -/
noncomputable def ambientCoreFine
    (_pullback :
      PureWZ2Prop62PacketHullCorePullbackData metric ambientCore) :
    WZ2PaperPureTubeSubfamily fine :=
  WZ2PaperPureTubeSubfamily.fromFinset fine ambientCore

/-- The same final core, enumerated inside the complete packet hull. -/
noncomputable def packetCoreFine :
    WZ2PaperPureTubeSubfamily metric.selectedFine :=
  WZ2PaperPureTubeSubfamily.fromFinset
    metric.selectedFine pullback.pulledBack

theorem pulledBack_nonempty
    (ambientCoreNonempty : ambientCore.Nonempty) :
    pullback.pulledBack.Nonempty := by
  rcases ambientCoreNonempty with ⟨ambientSource, sourceCore⟩
  have sourceHull :
      ambientSource ∈ metric.mesh.complete.selectedFineIndices :=
    pullback.ambientCore_subset_hull sourceCore
  rcases
      metric.mesh.complete.selectedFine_ambient_surjective
        ambientSource sourceHull
    with
    ⟨source, sourceEq⟩
  exact
    ⟨source, by
      rw [pullback.pulledBack_eq]
      exact
        Finset.mem_filter.mpr
          ⟨Finset.mem_univ source, by
            rwa [sourceEq]⟩⟩

theorem embedding_mem_ambientCore
    (source : Fin metric.selectedFine.card)
    (sourceMem : source ∈ pullback.pulledBack) :
    metric.mesh.complete.selectedFine.embedding source ∈ ambientCore := by
  rw [pullback.pulledBack_eq] at sourceMem
  exact (Finset.mem_filter.mp sourceMem).2

/-- Map one packet-hull core index to its ambient-core index. -/
noncomputable def packetCoreToAmbientCore
    (source : Fin pullback.packetCoreFine.family.card) :
    Fin pullback.ambientCoreFine.family.card := by
  let packetSource :=
    pullback.packetCoreFine.embedding source
  have packetSourceMem :
      packetSource ∈ pullback.pulledBack :=
    Finset.orderEmbOfFin_mem pullback.pulledBack rfl source
  let ambientSource :=
    metric.mesh.complete.selectedFine.embedding packetSource
  have ambientSourceMem :
      ambientSource ∈ ambientCore :=
    pullback.embedding_mem_ambientCore packetSource packetSourceMem
  exact
    (ambientCore.orderIsoOfFin rfl).symm
      ⟨ambientSource, ambientSourceMem⟩

theorem packetCoreToAmbientCore_embedding
    (source : Fin pullback.packetCoreFine.family.card) :
    pullback.ambientCoreFine.embedding
        (pullback.packetCoreToAmbientCore source) =
      metric.mesh.complete.selectedFine.embedding
        (pullback.packetCoreFine.embedding source) := by
  unfold packetCoreToAmbientCore ambientCoreFine packetCoreFine
  change
    ambientCore.orderEmbOfFin rfl
        ((ambientCore.orderIsoOfFin rfl).symm
          ⟨metric.mesh.complete.selectedFine.embedding
              (pullback.pulledBack.orderEmbOfFin rfl source),
            _⟩) =
      metric.mesh.complete.selectedFine.embedding
        (pullback.pulledBack.orderEmbOfFin rfl source)
  exact congrArg Subtype.val <|
    (ambientCore.orderIsoOfFin rfl).apply_symm_apply _

theorem packetCoreToAmbientCore_injective :
    Function.Injective pullback.packetCoreToAmbientCore := by
  intro first second indexEq
  have ambientEq :=
    congrArg pullback.ambientCoreFine.embedding indexEq
  rw [pullback.packetCoreToAmbientCore_embedding,
    pullback.packetCoreToAmbientCore_embedding] at ambientEq
  exact
    pullback.packetCoreFine.embedding.injective <|
      metric.mesh.complete.selectedFine.embedding.injective ambientEq

theorem packetCoreToAmbientCore_surjective :
    Function.Surjective pullback.packetCoreToAmbientCore := by
  intro ambientIndex
  have ambientMem :
      pullback.ambientCoreFine.embedding ambientIndex ∈ ambientCore :=
    Finset.orderEmbOfFin_mem ambientCore rfl ambientIndex
  have ambientImage :
      pullback.ambientCoreFine.embedding ambientIndex ∈
        Finset.image metric.mesh.complete.selectedFine.embedding
          pullback.pulledBack := by
    rw [pullback.image_eq]
    exact ambientMem
  rcases Finset.mem_image.mp ambientImage with
    ⟨packetSource, packetSourceMem, sourceEq⟩
  let source :
      Fin pullback.packetCoreFine.family.card :=
    (pullback.pulledBack.orderIsoOfFin rfl).symm
      ⟨packetSource, packetSourceMem⟩
  refine ⟨source, ?_⟩
  apply pullback.ambientCoreFine.embedding.injective
  rw [pullback.packetCoreToAmbientCore_embedding]
  change
    metric.mesh.complete.selectedFine.embedding
        (pullback.pulledBack.orderEmbOfFin rfl source) =
      pullback.ambientCoreFine.embedding ambientIndex
  have sourceAmbient :
      pullback.pulledBack.orderEmbOfFin rfl source =
        packetSource := by
    exact congrArg Subtype.val <|
      (pullback.pulledBack.orderIsoOfFin rfl).apply_symm_apply
        ⟨packetSource, packetSourceMem⟩
  rw [sourceAmbient, sourceEq]

/-- Exact finite equivalence between the two enumerations of the final core. -/
noncomputable def packetCoreEquiv :
    Fin pullback.packetCoreFine.family.card ≃
      Fin pullback.ambientCoreFine.family.card :=
  Equiv.ofBijective
    pullback.packetCoreToAmbientCore
    ⟨pullback.packetCoreToAmbientCore_injective,
      pullback.packetCoreToAmbientCore_surjective⟩

theorem packetCoreEquiv_embedding
    (source : Fin pullback.packetCoreFine.family.card) :
    pullback.ambientCoreFine.embedding
        (pullback.packetCoreEquiv source) =
      metric.mesh.complete.selectedFine.embedding
        (pullback.packetCoreFine.embedding source) :=
  pullback.packetCoreToAmbientCore_embedding source

theorem packetCoreEquiv_tube
    (source : Fin pullback.packetCoreFine.family.card) :
    pullback.packetCoreFine.family.tube source =
      pullback.ambientCoreFine.family.tube
        (pullback.packetCoreEquiv source) := by
  rw [pullback.packetCoreFine.tube_eq,
    metric.mesh.complete.selectedFine.tube_eq,
    pullback.ambientCoreFine.tube_eq,
    pullback.packetCoreEquiv_embedding]

end PureWZ2Prop62PacketHullCorePullbackData

end Kakeya.Assouad

end
