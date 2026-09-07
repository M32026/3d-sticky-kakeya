import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalOccupiedCover
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalLocalADNumerics

/-!
# Small-scale exact local AD for the direct half-offset terminal

This module instantiates the finite-cover structural theorem on the actual
terminal.  The only remaining quantitative input is an explicit absorption
of the finite cover cardinality and centered-normal loss into the requested
output constant.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

namespace PureWZ2DirectCommonYSourceAssembly

variable
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    (commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta)

namespace TerminalGeometry

/-- One occupied source piece inherits the source local-grain AD at scale
`25 * rho` once it is contained in the corresponding source ball. -/
theorem source_piece_local_ad
    (terminal : commonSource.TerminalGeometry)
    (sourcePiece : Set Point3)
    (sourceAnchor : {point : Point3 // point ∈
      exactTerminalSourceSet commonSource terminal})
    {rho radius : ℝ}
    (hrho : 0 < rho)
    (hrhoTiny : rho ≤ 1 / 6400)
    (htarget : terminal.targetDelta ≤ rho)
    (hsourceSubset : sourcePiece ⊆
      exactTerminalSourceSet commonSource terminal)
    (hsourceBall : sourcePiece ⊆
      Metric.closedBall (sourceAnchor : Point3) (7 * radius / 2))
    (hsourceRadius : 7 * radius / 2 ≤ Real.sqrt (25 * rho)) :
    PureWZ2PaperADSet1
      (scalarProjection
        (commonSource.halfOffsetAssembly.horizontalSource.sourceLocalGrains
          |>.planeMap (exactSourcePoint commonSource terminal sourceAnchor))
        sourcePiece)
      (25 * rho) (1 - sigma)
      (Kakeya.realRpowENN delta
        (-commonSource.halfOffsetAssembly.technicalLoss)) := by
  let source := commonSource.halfOffsetAssembly.horizontalSource
  have hdeltaTarget : delta ≤ terminal.targetDelta := by
    have hbudget := commonSource.halfOffsetLineClass_incidence_budget
    have herrorNonneg : 0 ≤ (51 / 100 : ℝ) *
        (terminal.targetDelta * Real.sqrt 3) := by
      positivity [commonSource.halfOffsetLineClassTargetDelta_pos]
    linarith
  have hsourceRhoLower : delta ≤ 25 * rho := by
    calc
      delta ≤ terminal.targetDelta := hdeltaTarget
      _ ≤ rho := htarget
      _ ≤ 25 * rho := by nlinarith
  have hsourceRhoOne : 25 * rho ≤ 1 := by nlinarith
  have hlocal := source.sourceLocalGrains.local_ad
    (25 * rho) hsourceRhoLower hsourceRhoOne
    (exactSourcePoint commonSource terminal sourceAnchor)
  apply hlocal.weaken_subset
  apply Set.image_mono
  intro point hpoint
  refine ⟨(exactTerminalSourceSet_subset_sourceShading
    commonSource terminal) (hsourceSubset hpoint), ?_⟩
  apply Metric.mem_closedBall.mpr
  rw [exactSourcePoint_coe]
  exact (Metric.mem_closedBall.mp (hsourceBall hpoint)).trans hsourceRadius

/-- Pointwise source-piece AD, packaged uniformly over a finite index set. -/
theorem source_pieces_local_ad
    (terminal : commonSource.TerminalGeometry)
    {centers : Finset Point3}
    (sourcePieces : Point3 → Set Point3)
    (sourceAnchor : Point3 → {point : Point3 // point ∈
      exactTerminalSourceSet commonSource terminal})
    {rho radius : ℝ}
    (hrho : 0 < rho)
    (hrhoTiny : rho ≤ 1 / 6400)
    (htarget : terminal.targetDelta ≤ rho)
    (hsourceSubset : ∀ center ∈ centers, sourcePieces center ⊆
      exactTerminalSourceSet commonSource terminal)
    (hsourceBall : ∀ center ∈ centers, sourcePieces center ⊆
      Metric.closedBall (sourceAnchor center : Point3) (7 * radius / 2))
    (hsourceRadius : 7 * radius / 2 ≤ Real.sqrt (25 * rho)) :
    ∀ center ∈ centers,
      PureWZ2PaperADSet1
        (scalarProjection
          (commonSource.halfOffsetAssembly.horizontalSource.sourceLocalGrains
            |>.planeMap (exactSourcePoint commonSource terminal
              (sourceAnchor center)))
          (sourcePieces center))
        (25 * rho) (1 - sigma)
        (Kakeya.realRpowENN delta
          (-commonSource.halfOffsetAssembly.technicalLoss)) := by
  intro center hcenter
  exact source_piece_local_ad commonSource terminal
    (sourcePieces center) (sourceAnchor center) hrho hrhoTiny htarget
    (hsourceSubset center hcenter) (hsourceBall center hcenter) hsourceRadius

/-- The exact projection-scale inequality, uniformly over occupied anchors. -/
theorem source_anchor_projection_scales
    (terminal : commonSource.TerminalGeometry)
    {centers : Finset Point3}
    (sourceAnchor : Point3 → {point : Point3 // point ∈
      exactTerminalSourceSet commonSource terminal})
    {rho : ℝ} (hrho : 0 < rho) :
    ∀ center ∈ centers,
      let source := commonSource.halfOffsetAssembly.horizontalSource
      |pureWZ2OffsetProjectiveProjectionScale
          (PureWZ2HalfOffsetHorizontalSourceData.offset source)
          (source.m * (source.d - source.c) / 2)
          (2 / (source.d - source.c))
          pureWZ2DirectHalfOffsetTerminalLambda
          (source.sourceLocalGrains.planeMap
            (exactSourcePoint commonSource terminal (sourceAnchor center)))| *
        (25 * rho) ≤ rho := by
  intro center _
  exact commonSource.halfOffsetTerminal_projectionScale_mul_twentyFive_le
    (exactSourcePoint commonSource terminal (sourceAnchor center)) hrho.le

/-- The exact local-AD proposition with its finite-cover constant exposed. -/
def ExactSmallLocalAD
    (terminal : commonSource.TerminalGeometry)
    (anchor0 : {point : Point3 // point ∈ terminal.exactShading.union})
    (rho : ℝ) (n : ℕ) : Prop :=
  PureWZ2PaperADSet1
    (scalarProjection (exactPlaneMap commonSource terminal anchor0)
      (exactLocalSet commonSource terminal anchor0
        (pureWZ2DirectHalfOffsetTerminalLocalADR rho terminal.targetDelta)))
    rho (1 - sigma)
    ((n : ENNReal) *
      ((2 * (Nat.ceil ((5 * rho) / rho) + 1) : ENNReal) ^ 3 *
        Kakeya.realRpowENN delta
          (-commonSource.halfOffsetAssembly.technicalLoss)))

/-- Uniform source local AD on the occupied pieces. -/
def SourcePiecesAD
    (terminal : commonSource.TerminalGeometry)
    (anchor0 : {point : Point3 // point ∈ terminal.exactShading.union})
    (rho : ℝ)
    (coverData : ExactLocalOccupiedCoverData commonSource terminal anchor0
      (pureWZ2DirectHalfOffsetTerminalLocalADR rho terminal.targetDelta)) : Prop :=
  ∀ center ∈ coverData.centers,
    PureWZ2PaperADSet1
      (scalarProjection
        (commonSource.halfOffsetAssembly.horizontalSource.sourceLocalGrains
          |>.planeMap (exactSourcePoint commonSource terminal
            (coverData.sourceAnchor center)))
        (coverData.sourcePieces center))
      (25 * rho) (1 - sigma)
      (Kakeya.realRpowENN delta
        (-commonSource.halfOffsetAssembly.technicalLoss))

/-- Uniform target-scale control for the exact covariance multipliers. -/
def SourceAnchorScales
    (terminal : commonSource.TerminalGeometry)
    (anchor0 : {point : Point3 // point ∈ terminal.exactShading.union})
    (rho : ℝ)
    (coverData : ExactLocalOccupiedCoverData commonSource terminal anchor0
      (pureWZ2DirectHalfOffsetTerminalLocalADR rho terminal.targetDelta)) : Prop :=
  ∀ center ∈ coverData.centers,
    let source := commonSource.halfOffsetAssembly.horizontalSource
    |pureWZ2OffsetProjectiveProjectionScale
        (PureWZ2HalfOffsetHorizontalSourceData.offset source)
        (source.m * (source.d - source.c) / 2)
        (2 / (source.d - source.c))
        pureWZ2DirectHalfOffsetTerminalLambda
        (source.sourceLocalGrains.planeMap
          (exactSourcePoint commonSource terminal
            (coverData.sourceAnchor center)))| * (25 * rho) ≤ rho

/-- Thin specialization of the structural transfer theorem to the numerical
small-scale parameters. -/
theorem exact_local_ad_small_core
    (terminal : commonSource.TerminalGeometry)
    (anchor0 : {point : Point3 // point ∈ terminal.exactShading.union})
    {rho : ℝ} (hrho : 0 < rho)
    (hrhoTiny : rho ≤ 1 / 6400)
    (htarget : terminal.targetDelta ≤ rho)
    (coverData : ExactLocalOccupiedCoverData commonSource terminal anchor0
      (pureWZ2DirectHalfOffsetTerminalLocalADR rho terminal.targetDelta))
    (hsourceAD : SourcePiecesAD commonSource terminal anchor0 rho coverData)
    (hbase : SourceAnchorScales commonSource terminal anchor0 rho coverData) :
    ExactSmallLocalAD commonSource terminal anchor0 rho
      coverData.centers.card := by
  unfold ExactSmallLocalAD
  refine @exact_local_ad_of_finite_source_cover logExponent sigma epsilon
    delta commonSource terminal anchor0 Point3 coverData.centers
    coverData.sourcePieces coverData.sourceAnchor
    (2 * pureWZ2DirectHalfOffsetTerminalLocalADR rho terminal.targetDelta)
    (pureWZ2DirectHalfOffsetTerminalLocalADR rho terminal.targetDelta)
    (5 * rho) (25 * rho) rho (1 - sigma)
    (Kakeya.realRpowENN delta
      (-commonSource.halfOffsetAssembly.technicalLoss))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · unfold pureWZ2DirectHalfOffsetTerminalLocalADR
    have htargetNonneg := commonSource.halfOffsetLineClassTargetDelta_pos.le
    exact add_nonneg (Real.sqrt_nonneg rho)
      (mul_nonneg (by norm_num)
        (mul_nonneg htargetNonneg (Real.sqrt_nonneg 3)))
  · simpa only using coverData.cover
  · simpa only using coverData.anchor_ball
  · simpa only using coverData.image_ball
  · simpa only [SourcePiecesAD] using hsourceAD
  · simpa only [SourceAnchorScales] using hbase
  · exact hrho
  · have htargetNonneg := commonSource.halfOffsetLineClassTargetDelta_pos.le
    unfold pureWZ2DirectHalfOffsetTerminalLocalADR
    exact mul_nonneg (by norm_num) <| add_nonneg (Real.sqrt_nonneg rho)
      (mul_nonneg (by norm_num)
        (mul_nonneg htargetNonneg (Real.sqrt_nonneg 3)))
  · nlinarith
  · exact pureWZ2DirectHalfOffsetTerminalLocalAD_twice_radius_sq_le
      hrho hrhoTiny commonSource.halfOffsetLineClassTargetDelta_pos.le htarget

/-- Instantiate the structural transfer theorem from an already selected
occupied cover. -/
theorem exact_local_ad_small_of_occupied_cover
    (terminal : commonSource.TerminalGeometry)
    (anchor0 : {point : Point3 // point ∈ terminal.exactShading.union})
    {rho : ℝ} (hrho : 0 < rho)
    (hrhoTiny : rho ≤ 1 / 6400)
    (htarget : terminal.targetDelta ≤ rho)
    (coverData : ExactLocalOccupiedCoverData commonSource terminal anchor0
      (pureWZ2DirectHalfOffsetTerminalLocalADR rho terminal.targetDelta)) :
    ExactSmallLocalAD commonSource terminal anchor0 rho
      coverData.centers.card := by
  let source := commonSource.halfOffsetAssembly.horizontalSource
  let radius := pureWZ2DirectHalfOffsetTerminalLocalADR rho
    terminal.targetDelta
  let sourceC := Kakeya.realRpowENN delta
    (-commonSource.halfOffsetAssembly.technicalLoss)
  have hsourceRadius : 7 * radius / 2 ≤ Real.sqrt (25 * rho) := by
    exact pureWZ2DirectHalfOffsetTerminalLocalAD_reanchor_radius_le
      hrho hrhoTiny htarget
  have hsourceAD := source_pieces_local_ad commonSource terminal
    coverData.sourcePieces coverData.sourceAnchor hrho hrhoTiny htarget
    coverData.source_subset coverData.source_ball hsourceRadius
  have hbase := source_anchor_projection_scales commonSource terminal
    (centers := coverData.centers) coverData.sourceAnchor hrho
  exact exact_local_ad_small_core commonSource terminal anchor0 hrho hrhoTiny
    htarget coverData hsourceAD hbase

/-- Raw small-scale exact local AD, retaining the finite cover cardinality as
an explicit witness. -/
theorem exact_local_ad_small_raw
    (terminal : commonSource.TerminalGeometry)
    (anchor0 : {point : Point3 // point ∈ terminal.exactShading.union})
    {rho : ℝ} (hrho : 0 < rho)
    (hrhoTiny : rho ≤ 1 / 6400)
    (htarget : terminal.targetDelta ≤ rho) :
    ∃ n : ℕ,
      (n : ℝ) ≤ 9 *
        (commonSource.halfOffsetAssembly.horizontalSource.m *
          (commonSource.halfOffsetAssembly.horizontalSource.d -
            commonSource.halfOffsetAssembly.horizontalSource.c) / 2)⁻¹ ∧
      PureWZ2PaperADSet1
        (scalarProjection (exactPlaneMap commonSource terminal anchor0)
          (exactLocalSet commonSource terminal anchor0
            (pureWZ2DirectHalfOffsetTerminalLocalADR rho
              terminal.targetDelta)))
        rho (1 - sigma)
        ((n : ENNReal) *
          ((2 * (Nat.ceil ((5 * rho) / rho) + 1) : ENNReal) ^ 3 *
            Kakeya.realRpowENN delta
              (-commonSource.halfOffsetAssembly.technicalLoss))) := by
  let radius := pureWZ2DirectHalfOffsetTerminalLocalADR rho
    terminal.targetDelta
  have hradius : 0 < radius := by
    dsimp only [radius, pureWZ2DirectHalfOffsetTerminalLocalADR]
    have htargetPos := commonSource.halfOffsetLineClassTargetDelta_pos
    positivity
  obtain ⟨coverData⟩ := toExactLocalOccupiedCoverData
    commonSource terminal anchor0 hradius
  refine ⟨coverData.centers.card, coverData.card_le, ?_⟩
  exact exact_local_ad_small_of_occupied_cover commonSource terminal anchor0
    hrho hrhoTiny htarget coverData

/-- At scales below the fixed cutoff, the actual exact terminal inherits
local paper AD from the source local grains through the occupied finite
preimage cover.  `habsorb` is the intentionally separate scalar layer. -/
theorem exact_local_ad_small
    (terminal : commonSource.TerminalGeometry)
    (anchor0 : {point : Point3 // point ∈ terminal.exactShading.union})
    {rho : ℝ} (hrho : 0 < rho)
    (hrhoTiny : rho ≤ 1 / 6400)
    (htarget : terminal.targetDelta ≤ rho)
    {Ctarget : ENNReal}
    (hCtargetOne : 1 ≤ Ctarget)
    (hCtargetTop : Ctarget ≠ ⊤)
    (habsorb : ∀ n : ℕ,
      (n : ℝ) ≤ 9 *
        (commonSource.halfOffsetAssembly.horizontalSource.m *
          (commonSource.halfOffsetAssembly.horizontalSource.d -
            commonSource.halfOffsetAssembly.horizontalSource.c) / 2)⁻¹ →
      (n : ENNReal) *
          ((2 * (Nat.ceil ((5 * rho) / rho) + 1) : ENNReal) ^ 3 *
            Kakeya.realRpowENN delta
              (-commonSource.halfOffsetAssembly.technicalLoss)) ≤ Ctarget) :
    PureWZ2PaperADSet1
      (scalarProjection (exactPlaneMap commonSource terminal anchor0)
        (exactLocalSet commonSource terminal anchor0
          (pureWZ2DirectHalfOffsetTerminalLocalADR rho
            terminal.targetDelta)))
      rho (1 - sigma) Ctarget := by
  rcases exact_local_ad_small_raw commonSource terminal anchor0 hrho hrhoTiny
      htarget with ⟨n, hn, hAD⟩
  exact hAD.weaken_constant (habsorb n hn) hCtargetOne hCtargetTop

end TerminalGeometry

end PureWZ2DirectCommonYSourceAssembly

end Kakeya.Assouad

end
