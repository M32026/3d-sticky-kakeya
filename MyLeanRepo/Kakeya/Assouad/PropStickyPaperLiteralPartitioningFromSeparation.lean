import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCarrierContainmentLineDistance
import MyLeanRepo.Kakeya.Assouad.PropStickyFullFiberHelpers

/-!
# Literal partitioning from strong parent separation

Carrier containment is the paper-facing cover relation.  If the coarse
parents are strongly separated in the paper line metric, the auxiliary
assigned parent is the unique strict carrier parent and the literal doubled
fibers are disjoint.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- Reinterpret one tube at another radius without changing its axis data. -/
private def relabelPaperTube
    {sourceScale targetScale : ℝ}
    (tube : Kakeya.DeltaTube sourceScale) :
    Kakeya.DeltaTube targetScale where
  base := tube.base
  direction := tube.direction
  direction_unit := tube.direction_unit

private lemma relabelPaperTube_lineDistance
    {firstScale secondScale targetScale : ℝ}
    (first : Kakeya.DeltaTube firstScale)
    (second : Kakeya.DeltaTube secondScale) :
    wz1PaperLineDistance first
        (relabelPaperTube (targetScale := targetScale) second) =
      wz1PaperLineDistance first second := by
  rfl

private lemma relabelPaperTube_lineClass
    {sourceScale targetScale : ℝ}
    {tube : Kakeya.DeltaTube sourceScale}
    (hline : WZ1PaperTubeInLineClass tube) :
    WZ1PaperTubeInLineClass
      (relabelPaperTube (targetScale := targetScale) tube) := by
  exact hline

/--
Containment in the literal doubled carrier of a radius-`rho` tube forces
paper line distance at most `800 * rho`.
-/
theorem wz2_paper_doubled_carrier_containment_lineDistance_le
    {delta rho : ℝ}
    {fine : Kakeya.DeltaTube delta}
    {coarse : Kakeya.DeltaTube rho}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hfine : WZ1PaperTubeInLineClass fine)
    (hcoarse : WZ1PaperTubeInLineClass coarse)
    (hcontained :
      wz1PaperTubeCarrier fine ⊆
        wz2PaperDoubledTubeCarrier coarse) :
    wz1PaperLineDistance fine coarse ≤ 800 * rho := by
  let doubled : Kakeya.DeltaTube (2 * rho) :=
    relabelPaperTube (targetScale := 2 * rho) coarse
  have hdoubledLine : WZ1PaperTubeInLineClass doubled :=
    relabelPaperTube_lineClass hcoarse
  have hcarrierEq :
      wz1PaperTubeCarrier doubled =
        wz2PaperDoubledTubeCarrier coarse := by
    change
      Metric.cthickening (6 * (2 * rho)) (tubeAxisLine doubled) ∩
          Kakeya.Streamlined.axisBox 2 2 2 =
        Metric.cthickening (12 * rho) (tubeAxisLine coarse) ∩
          Kakeya.Streamlined.axisBox 2 2 2
    have haxis : tubeAxisLine doubled = tubeAxisLine coarse := rfl
    rw [haxis]
    ring_nf
  have hcarrier :
      WZ2PaperTubeCarrierCovers fine doubled := by
    intro point hpoint
    rw [hcarrierEq]
    exact hcontained hpoint
  have hdist :=
    wz2_paper_carrier_containment_lineDistance_le
      hdelta (by positivity : 0 < 2 * rho)
      hfine hdoubledLine hcarrier
  rw [relabelPaperTube_lineDistance] at hdist
  nlinarith

/--
An assigned carrier cover whose parents are separated by more than
`1600 * rho` is a literal recursive partitioning cover.
-/
noncomputable def
    WZ2PaperDilatedTubeCover.toLiteralPartitioningOfStrongSeparation
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperDilatedTubeCover 2 fine coarse)
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hfine : WZ1PaperIsLineClass fine)
    (hcoarse : WZ1PaperIsLineClass coarse)
    (hcarrier :
      ∀ source,
        WZ2PaperTubeCarrierCovers
          (fine.tube source) (coarse.tube (cover.parent source)))
    (hseparated :
      ∀ first second, first ≠ second →
        1600 * rho <
          wz1PaperLineDistance
            (coarse.tube first) (coarse.tube second)) :
    WZ2PaperLiteralDilatedPartitioningCover fine coarse where
  toWZ2PaperDilatedTubeCover := cover
  parent_carrier_covers := hcarrier
  literal_parent_unique source candidate hcandidate := by
    by_contra hne
    have hassignedDist :=
      wz2_paper_carrier_containment_lineDistance_le
        hdelta hrho (hfine source) (hcoarse (cover.parent source))
        (hcarrier source)
    have hcandidateDist :=
      wz2_paper_carrier_containment_lineDistance_le
        hdelta hrho (hfine source) (hcoarse candidate) hcandidate
    have htriangle :=
      wz1PaperLineDistance_triangle
        (coarse.tube candidate) (fine.tube source)
        (coarse.tube (cover.parent source))
    have hsymm :
        wz1PaperLineDistance
            (coarse.tube candidate) (fine.tube source) =
          wz1PaperLineDistance
            (fine.tube source) (coarse.tube candidate) :=
      wz1PaperLineDistance_symm _ _
    rw [hsymm] at htriangle
    have hsep :=
      hseparated candidate (cover.parent source) hne
    linarith
  literal_doubled_fibers_disjoint first second hne := by
    rw [Finset.disjoint_left]
    intro source hfirst hsecond
    have hfirstContainment :
        wz1PaperTubeCarrier (fine.tube source) ⊆
          wz2PaperDoubledTubeCarrier (coarse.tube first) := by
      simpa [wz2PaperLiteralDoubledFiberIndices] using hfirst
    have hsecondContainment :
        wz1PaperTubeCarrier (fine.tube source) ⊆
          wz2PaperDoubledTubeCarrier (coarse.tube second) := by
      simpa [wz2PaperLiteralDoubledFiberIndices] using hsecond
    have hfirstDist :=
      wz2_paper_doubled_carrier_containment_lineDistance_le
        hdelta hrho (hfine source) (hcoarse first)
        hfirstContainment
    have hsecondDist :=
      wz2_paper_doubled_carrier_containment_lineDistance_le
        hdelta hrho (hfine source) (hcoarse second)
        hsecondContainment
    have htriangle :=
      wz1PaperLineDistance_triangle
        (coarse.tube first) (fine.tube source)
        (coarse.tube second)
    have hsymm :
        wz1PaperLineDistance
            (coarse.tube first) (fine.tube source) =
          wz1PaperLineDistance
            (fine.tube source) (coarse.tube first) :=
      wz1PaperLineDistance_symm _ _
    rw [hsymm] at htriangle
    have hsep := hseparated first second hne
    linarith

end Kakeya.Assouad

end
