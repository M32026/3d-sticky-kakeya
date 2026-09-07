import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62TreePureSchedule
import MyLeanRepo.Kakeya.Assouad.PureWZ2.CenteredLineTube
import MyLeanRepo.Kakeya.Assouad.PureWZ2.PropSticky
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Section6CoverParentMap
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12LocalizedDoubledFiber

/-!
# Proposition 6.2 metric parents: geometric packet cover

This is the geometric part of the metric-parent lemma in `WZ2_prop62.tex`.
Whole packets of one old strict ordinary cover are assigned to separated
radius-`rho` line representatives.  The resulting line cover has exactly the
assigned packet unions as its metric fibers.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/--
An ordinary strict fiber member is at line distance `O(M * scale)` from its
old parent when the fine midpoint lies in the radius-`M` window.
-/
theorem pureWZ2_prop62_strictFiber_lineDistance_le
    {delta scale : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily scale}
    (hdelta : 0 < delta)
    (hscale : 0 < scale)
    (fineLine : WZ1PaperIsLineClass fine)
    (coarseLine : WZ1PaperIsLineClass coarse)
    (M : ℝ)
    (fineLocal :
      ∀ source,
        ‖wz2PaperTubeMidpoint (fine.tube source)‖ ≤ M)
    (parent : Fin coarse.card)
    (source : Fin fine.card)
    (hsource :
      source ∈
        wz2PaperOrdinaryFullFiberIndices
          fine coarse parent) :
    wz1PaperLineDistance
        (fine.tube source) (coarse.tube parent) ≤
      (16 * M + 44) * scale := by
  have hstrict :
      (fine.tube source).carrier ⊆
        (coarse.tube parent).carrier :=
    (mem_wz2PaperOrdinaryFullFiberIndices_iff
      parent source).mp hsource
  have hdoubled :
      (fine.tube source).carrier ⊆
        wz2PaperCenteredDilatedCarrier 2
          (coarse.tube parent) :=
    hstrict.trans <|
      wz2_paper_carrier_subset_centeredDilatedTwo
        (coarse.tube parent) hscale.le
  exact
    wz2_paper_bounded_centered_doubled_containment_lineDistance_le
      hdelta hscale (fineLine source) (coarseLine parent)
      M (fineLocal source) hdoubled

/--
The triangle estimate used after assigning one whole old packet to one mesh
cell representative.
-/
theorem pureWZ2_prop62_strictFiber_to_representative_lineDistance_le
    {delta scale representativeScale targetScale : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily scale}
    (hdelta : 0 < delta)
    (hscale : 0 < scale)
    (fineLine : WZ1PaperIsLineClass fine)
    (coarseLine : WZ1PaperIsLineClass coarse)
    (M meshWidth : ℝ)
    (fineLocal :
      ∀ source,
        ‖wz2PaperTubeMidpoint (fine.tube source)‖ ≤ M)
    (parent : Fin coarse.card)
    (source : Fin fine.card)
    (representative : Kakeya.DeltaTube representativeScale)
    (representativeLine :
      WZ1PaperTubeInLineClass representative)
    (hsource :
      source ∈
        wz2PaperOrdinaryFullFiberIndices
          fine coarse parent)
    (parentRepresentative :
      wz1PaperLineDistance
          (coarse.tube parent) representative ≤ meshWidth) :
    wz1PaperLineDistance
        (fine.tube source)
        (wz2PaperCenteredLineTube
          (targetScale := targetScale) representative) ≤
      (16 * M + 44) * scale + meshWidth := by
  have htriangle :=
    wz1PaperLineDistance_triangle
      (fine.tube source)
      (coarse.tube parent)
      (wz2PaperCenteredLineTube
        (targetScale := targetScale) representative)
  rw [
    wz1PaperLineDistance_centeredLineTube_right
      (coarseLine parent) representativeLine
  ] at htriangle
  have hsourceParent :=
    pureWZ2_prop62_strictFiber_lineDistance_le
      hdelta hscale fineLine coarseLine M fineLocal
      parent source hsource
  linarith

/-- Strict line parents are unique inside an essentially-distinct family. -/
theorem pureWZ2_prop62_metricParent_unique
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (coarseDistinct : WZ1PaperIsEssentiallyDistinct coarse)
    (source : Fin fine.card)
    (first second : Fin coarse.card)
    (firstCovers :
      WZ1PaperTubeCovers
        (fine.tube source) (coarse.tube first))
    (secondCovers :
      WZ1PaperTubeCovers
        (fine.tube source) (coarse.tube second)) :
    first = second := by
  by_contra hne
  have hseparated :=
    coarseDistinct first second hne
  have htriangle :=
    wz1PaperLineDistance_triangle
      (coarse.tube first)
      (fine.tube source)
      (coarse.tube second)
  have hsymmetry :
      wz1PaperLineDistance
          (coarse.tube first) (fine.tube source) =
        wz1PaperLineDistance
          (fine.tube source) (coarse.tube first) :=
    wz1PaperLineDistance_symm _ _
  rw [hsymmetry] at htriangle
  unfold WZ1PaperTubeCovers at firstCovers secondCovers
  linarith

/--
Paper-facing input after the four-dimensional mesh and one-colour selection.
Every old strict packet is assigned whole to one exact radius-`rho` parent.
-/
structure PureWZ2Prop62MetricPacketCoverInput
    {delta scale rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant : ENNReal}
    (oldData :
      WZ2PaperPureScaleCoverData fine scale ambientConstant)
    (M meshWidth : ℝ) where
  fine_nonempty : fine.Nonempty
  rho_pos : 0 < rho
  fine_line_class : WZ1PaperIsLineClass fine
  old_line_class : WZ1PaperIsLineClass oldData.coarse
  fine_midpoint_local :
    ∀ source,
      ‖wz2PaperTubeMidpoint (fine.tube source)‖ ≤ M
  coarse : Kakeya.Streamlined.TubeFamily rho
  coarse_line_class : WZ1PaperIsLineClass coarse
  coarse_essentially_distinct :
    WZ1PaperIsEssentiallyDistinct coarse
  packetParent :
    Fin oldData.coarse.card → Fin coarse.card
  packetParent_surjective :
    Function.Surjective packetParent
  parent_representative_close :
    ∀ parent,
      wz1PaperLineDistance
          (oldData.coarse.tube parent)
          (coarse.tube (packetParent parent)) ≤
        meshWidth
  packet_metric_bound :
    (16 * M + 44) * scale + meshWidth ≤ rho / 2

namespace PureWZ2Prop62MetricPacketCoverInput

variable
    {delta scale rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant : ENNReal}
    {oldData :
      WZ2PaperPureScaleCoverData fine scale ambientConstant}
    {M meshWidth : ℝ}
    (data :
      PureWZ2Prop62MetricPacketCoverInput
        (rho := rho) oldData M meshWidth)

/-- Every fine tube is strictly metric-covered by its packet's new parent. -/
theorem packetParent_covers
    (source : Fin fine.card) :
    WZ1PaperTubeCovers
      (fine.tube source)
      (data.coarse.tube
        (data.packetParent (oldData.cover.parent source))) := by
  unfold WZ1PaperTubeCovers
  calc
    wz1PaperLineDistance
        (fine.tube source)
        (data.coarse.tube
          (data.packetParent (oldData.cover.parent source))) ≤
      (16 * M + 44) * scale + meshWidth := by
        have hsource :=
          oldData.cover.parent_mem_fullFiber source
        have htriangle :=
          wz1PaperLineDistance_triangle
            (fine.tube source)
            (oldData.coarse.tube (oldData.cover.parent source))
            (data.coarse.tube
              (data.packetParent (oldData.cover.parent source)))
        have hold :=
          pureWZ2_prop62_strictFiber_lineDistance_le
            oldData.delta_pos oldData.rho_pos
            data.fine_line_class data.old_line_class
            M data.fine_midpoint_local
            (oldData.cover.parent source) source hsource
        exact htriangle.trans <| by
          gcongr
          exact data.parent_representative_close
            (oldData.cover.parent source)
    _ ≤ rho / 2 := data.packet_metric_bound

/-- Every exact metric parent receives at least one whole old packet. -/
theorem parent_hit
    (parent : Fin data.coarse.card) :
    ∃ source : Fin fine.card,
      WZ1PaperTubeCovers
        (fine.tube source) (data.coarse.tube parent) := by
  rcases data.packetParent_surjective parent with
    ⟨oldParent, hparent⟩
  have oldFiberNonempty :
      (wz2PaperOrdinaryFullFiberIndices
        fine oldData.coarse oldParent).Nonempty :=
    oldData.cover.fullFiber_nonempty_of_uniform
      data.fine_nonempty oldData.full_fiber_uniform oldParent
  rcases oldFiberNonempty with
    ⟨source, hsource⟩
  have hderived :
      oldData.cover.parent source = oldParent :=
    (oldData.cover.mem_fullFiber_iff_parent_eq
      oldData.rho_pos.le oldParent source).mp hsource
  refine ⟨source, ?_⟩
  simpa [hderived, hparent] using data.packetParent_covers source

/-- The whole-packet assignment is a genuine frozen Section 6 cover. -/
noncomputable def section6Cover :
    PureWZ2Section6Cover fine data.coarse where
  fine_line_class := data.fine_line_class
  coarse_line_class := data.coarse_line_class
  covers source :=
    ⟨data.packetParent (oldData.cover.parent source),
      data.packetParent_covers source⟩
  parent_hit := data.parent_hit
  coarse_essentially_distinct :=
    data.coarse_essentially_distinct

/--
The metric fiber of a new parent is exactly the union of old strict packets
assigned to that parent.
-/
theorem metricFiber_eq_assignedPackets
    (parent : Fin data.coarse.card) :
    wz2PaperFullFiberIndices fine data.coarse parent =
      Finset.univ.filter fun source =>
        data.packetParent (oldData.cover.parent source) = parent := by
  ext source
  simp only [wz2PaperFullFiberIndices, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · intro hsource
    exact
      pureWZ2_prop62_metricParent_unique
        data.coarse_essentially_distinct source parent
        (data.packetParent (oldData.cover.parent source))
        hsource (data.packetParent_covers source) |>.symm
  · intro hparent
    rw [← hparent]
    exact data.packetParent_covers source

/-- The canonical Section 6 parent map is the whole-packet assignment. -/
theorem section6_parent_eq_packetParent
    (source : Fin fine.card) :
    data.section6Cover.toWZ1PaperTubeCover.parent source =
      data.packetParent (oldData.cover.parent source) := by
  exact
    (data.section6Cover.toWZ1PaperTubeCover.parent_unique
      source
      (data.packetParent (oldData.cover.parent source))
      (data.packetParent_covers source)).symm

end PureWZ2Prop62MetricPacketCoverInput

/--
Paper-faithful metric-parent input with a separate Section 6 proxy axis.

The literal Definition 2.12 family `oldData.coarse` is used only to identify
the complete packets.  It is not required to lie in the WZ line chart.  The
geometric estimate is instead stated directly from every member of one
complete old packet to its assigned new metric parent.
-/
structure PureWZ2Prop62ProxyMetricPacketCoverInput
    {delta scale rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant : ENNReal}
    (oldData :
      WZ2PaperPureScaleCoverData fine scale ambientConstant)
    (packetRadius : ℝ) where
  fine_nonempty : fine.Nonempty
  rho_pos : 0 < rho
  fine_line_class : WZ1PaperIsLineClass fine
  coarse : Kakeya.Streamlined.TubeFamily rho
  coarse_line_class : WZ1PaperIsLineClass coarse
  coarse_essentially_distinct :
    WZ1PaperIsEssentiallyDistinct coarse
  packetParent :
    Fin oldData.coarse.card → Fin coarse.card
  packetParent_surjective :
    Function.Surjective packetParent
  packet_proxy_close :
    ∀ parent source,
      source ∈
          wz2PaperOrdinaryFullFiberIndices
            fine oldData.coarse parent →
        wz1PaperLineDistance
            (fine.tube source)
            (coarse.tube (packetParent parent)) ≤
          packetRadius
  packet_metric_bound :
    packetRadius ≤ rho / 2

namespace PureWZ2Prop62ProxyMetricPacketCoverInput

variable
    {delta scale rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant : ENNReal}
    {oldData :
      WZ2PaperPureScaleCoverData fine scale ambientConstant}
    {packetRadius : ℝ}
    (data :
      PureWZ2Prop62ProxyMetricPacketCoverInput
        (rho := rho) oldData packetRadius)

/-- Every fine tube is covered by the metric parent of its complete packet. -/
theorem packetParent_covers
    (source : Fin fine.card) :
    WZ1PaperTubeCovers
      (fine.tube source)
      (data.coarse.tube
        (data.packetParent (oldData.cover.parent source))) := by
  exact
    (data.packet_proxy_close
      (oldData.cover.parent source) source
      (oldData.cover.parent_mem_fullFiber source)).trans
      data.packet_metric_bound

/-- Every metric parent receives at least one complete old packet. -/
theorem parent_hit
    (parent : Fin data.coarse.card) :
    ∃ source : Fin fine.card,
      WZ1PaperTubeCovers
        (fine.tube source) (data.coarse.tube parent) := by
  rcases data.packetParent_surjective parent with
    ⟨oldParent, hparent⟩
  have oldFiberNonempty :
      (wz2PaperOrdinaryFullFiberIndices
        fine oldData.coarse oldParent).Nonempty :=
    oldData.cover.fullFiber_nonempty_of_uniform
      data.fine_nonempty oldData.full_fiber_uniform oldParent
  rcases oldFiberNonempty with
    ⟨source, hsource⟩
  have hderived :
      oldData.cover.parent source = oldParent :=
    (oldData.cover.mem_fullFiber_iff_parent_eq
      oldData.rho_pos.le oldParent source).mp hsource
  refine ⟨source, ?_⟩
  simpa [hderived, hparent] using data.packetParent_covers source

/-- The proxy-axis assignment is a genuine Section 6 line cover. -/
noncomputable def section6Cover :
    PureWZ2Section6Cover fine data.coarse where
  fine_line_class := data.fine_line_class
  coarse_line_class := data.coarse_line_class
  covers source :=
    ⟨data.packetParent (oldData.cover.parent source),
      data.packetParent_covers source⟩
  parent_hit := data.parent_hit
  coarse_essentially_distinct :=
    data.coarse_essentially_distinct

/--
Each new metric fiber is exactly the union of the complete old packets sent
to that parent.
-/
theorem metricFiber_eq_assignedPackets
    (parent : Fin data.coarse.card) :
    wz2PaperFullFiberIndices fine data.coarse parent =
      Finset.univ.filter fun source =>
        data.packetParent (oldData.cover.parent source) = parent := by
  ext source
  simp only [wz2PaperFullFiberIndices, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · intro hsource
    exact
      pureWZ2_prop62_metricParent_unique
        data.coarse_essentially_distinct source parent
        (data.packetParent (oldData.cover.parent source))
        hsource (data.packetParent_covers source) |>.symm
  · intro hparent
    rw [← hparent]
    exact data.packetParent_covers source

/--
The metric fiber is the literal union of the complete old strict packets
identified by the quotient map.
-/
theorem metricFiber_eq_biUnion_oldPackets
    (parent : Fin data.coarse.card) :
    wz2PaperFullFiberIndices fine data.coarse parent =
      Finset.biUnion
        (Finset.univ.filter fun oldParent =>
          data.packetParent oldParent = parent)
        (wz2PaperOrdinaryFullFiberIndices
          fine oldData.coarse) := by
  rw [data.metricFiber_eq_assignedPackets parent]
  ext source
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_biUnion]
  constructor
  · intro hparent
    refine
      ⟨oldData.cover.parent source, hparent,
        oldData.cover.parent_mem_fullFiber source⟩
  · rintro ⟨oldParent, hparent, hsource⟩
    have sourceParent :
        oldData.cover.parent source = oldParent :=
      (oldData.cover.mem_fullFiber_iff_parent_eq
        oldData.rho_pos.le oldParent source).mp hsource
    rwa [sourceParent]

/-- The derived Section 6 parent map is the whole-packet proxy assignment. -/
theorem section6_parent_eq_packetParent
    (source : Fin fine.card) :
    data.section6Cover.toWZ1PaperTubeCover.parent source =
      data.packetParent (oldData.cover.parent source) := by
  exact
    (data.section6Cover.toWZ1PaperTubeCover.parent_unique
      source
      (data.packetParent (oldData.cover.parent source))
      (data.packetParent_covers source)).symm

end PureWZ2Prop62ProxyMetricPacketCoverInput

end Kakeya.Assouad

end
