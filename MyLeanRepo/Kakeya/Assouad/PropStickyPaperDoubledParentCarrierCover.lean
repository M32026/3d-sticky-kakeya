import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCoverCarrierContainment
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralPartitioningFromSeparation

/-!
# Literal carrier covers from doubled recursive parents

The proof of `multiScaleWolffLem` uses the enlarged parent `2T_sigma`:

> `2T_sigma ⊃ N_sigma(T) ⊃ T_rho`.

This module realizes that sentence in the cropped full-line model.  A
factor-two line cover by a radius-`sigma` parent becomes strict literal
carrier containment after the same axis is relabelled with radius
`4 * sigma`.  This harmless extra factor absorbs the cropped paper
carrier's own thickness.
-/

noncomputable section

namespace Kakeya.Assouad

/-- The same geometric axis data, viewed at a new paper radius. -/
def wz2PaperRelabelTube
    {sourceScale targetScale : ℝ}
    (tube : Kakeya.DeltaTube sourceScale) :
    Kakeya.DeltaTube targetScale where
  base := tube.base
  direction := tube.direction
  direction_unit := tube.direction_unit

/--
The same axis data and phantom scale, equipped with the fourfold paper
carrier used for a recursive parent.

The underlying `DeltaTube sigma` is unchanged so that the paper unit
rescaling still normalizes by the requested scale `sigma`; only the
paper-facing carrier predicate is widened.
-/
def wz2PaperWideTubeCarrier
    {sigma : ℝ} (tube : Kakeya.DeltaTube sigma) : Set Point3 :=
  Metric.cthickening (24 * sigma) (tubeAxisLine tube) ∩
    Kakeya.Streamlined.axisBox 2 2 2

def WZ2PaperWideTubeCarrierCovers
    {delta sigma : ℝ}
    (source : Kakeya.DeltaTube delta)
    (parent : Kakeya.DeltaTube sigma) : Prop :=
  wz1PaperTubeCarrier source ⊆ wz2PaperWideTubeCarrier parent

@[simp] theorem wz2PaperRelabelTube_axis
    {sourceScale targetScale : ℝ}
    (tube : Kakeya.DeltaTube sourceScale) :
    tubeAxisLine
        (wz2PaperRelabelTube (targetScale := targetScale) tube) =
      tubeAxisLine tube := by
  rfl

@[simp] theorem wz2PaperRelabelTube_lineDistance_right
    {firstScale secondScale targetScale : ℝ}
    (first : Kakeya.DeltaTube firstScale)
    (second : Kakeya.DeltaTube secondScale) :
    wz1PaperLineDistance first
        (wz2PaperRelabelTube (targetScale := targetScale) second) =
      wz1PaperLineDistance first second := by
  rfl

@[simp] theorem wz2PaperRelabelTube_lineDistance_both
    {firstScale secondScale firstTarget secondTarget : ℝ}
    (first : Kakeya.DeltaTube firstScale)
    (second : Kakeya.DeltaTube secondScale) :
    wz1PaperLineDistance
        (wz2PaperRelabelTube (targetScale := firstTarget) first)
        (wz2PaperRelabelTube (targetScale := secondTarget) second) =
      wz1PaperLineDistance first second := by
  rfl

theorem wz2PaperRelabelTube_lineClass
    {sourceScale targetScale : ℝ}
    {tube : Kakeya.DeltaTube sourceScale}
    (hline : WZ1PaperTubeInLineClass tube) :
    WZ1PaperTubeInLineClass
      (wz2PaperRelabelTube (targetScale := targetScale) tube) :=
  hline

/--
Factor-two line cover at scale `sigma` gives strict carrier containment in
the same axis relabelled at radius `4 * sigma`.
-/
theorem wz2_paper_dilated_cover_carrier_covers_doubled_parent
    {delta sigma : ℝ}
    {source : Kakeya.DeltaTube delta}
    {parent : Kakeya.DeltaTube sigma}
    (hdelta : 0 < delta)
    (hsigma : 0 < sigma)
    (hscale : delta ≤ sigma)
    (hsource : WZ1PaperTubeInLineClass source)
    (hparent : WZ1PaperTubeInLineClass parent)
    (hcover : WZ2PaperDilatedTubeCovers 2 source parent) :
    WZ2PaperTubeCarrierCovers source
      (wz2PaperRelabelTube (targetScale := 4 * sigma) parent) := by
  intro point hpoint
  rcases hpoint with ⟨hthick, hbox⟩
  rcases
      exists_dist_le_of_mem_cthickening_closed
        (isClosed_tubeAxisLine source)
        (by positivity : 0 ≤ 6 * delta)
        hthick
    with ⟨sourceAxisPoint, hsourceAxis, hpointSource⟩
  let sourceHeight := point (2 : Fin 3)
  let sourceAtHeight :=
    wz1PaperAxisPointAtHeight source sourceHeight
  let parentAxisPoint :=
    wz1PaperAxisPointAtHeight parent sourceHeight
  have hheight : |sourceHeight| ≤ 1 := by
    simpa [sourceHeight] using hbox.2.2
  have hsourceAtHeight :
      dist sourceAtHeight sourceAxisPoint ≤ 12 * delta := by
    have hcoord :=
      PiLp.dist_apply_le point sourceAxisPoint (2 : Fin 3)
    have hheightAxis :
        |sourceHeight - sourceAxisPoint (2 : Fin 3)| ≤
          6 * delta := by
      simpa [sourceHeight, Real.dist_eq] using
        hcoord.trans hpointSource
    convert
      wz1Paper_axisPointAtHeight_dist_le_of_axis_point
        hsource sourceHeight (6 * delta)
        hsourceAxis hheightAxis using 1 <;> ring
  have hpointSourceAtHeight :
      dist point sourceAtHeight ≤ 18 * delta := by
    calc
      dist point sourceAtHeight ≤
          dist point sourceAxisPoint +
            dist sourceAxisPoint sourceAtHeight :=
        dist_triangle _ _ _
      _ ≤ 6 * delta + 12 * delta := by
        gcongr
        simpa [dist_comm] using hsourceAtHeight
      _ = 18 * delta := by ring
  have haxisDistance :
      dist sourceAtHeight parentAxisPoint ≤
        6 * sigma := by
    have hcommon :=
      wz1PaperAxisPointAtHeight_dist_le
        hsource hparent hheight
    have hlineDistance :
        wz1PaperLineDistance source parent ≤ sigma := by
      simpa [WZ2PaperDilatedTubeCovers] using hcover
    exact hcommon.trans (by nlinarith)
  have hpointParent :
      dist point parentAxisPoint ≤ 24 * sigma := by
    calc
      dist point parentAxisPoint ≤
          dist point sourceAtHeight +
            dist sourceAtHeight parentAxisPoint :=
        dist_triangle _ _ _
      _ ≤ 18 * delta + 6 * sigma := by gcongr
      _ ≤ 24 * sigma := by nlinarith
  constructor
  · have hparentAxis :
        parentAxisPoint ∈
          tubeAxisLine
            (wz2PaperRelabelTube
              (targetScale := 4 * sigma) parent) := by
      rw [wz2PaperRelabelTube_axis]
      exact wz1PaperAxisPointAtHeight_mem_axis parent sourceHeight
    exact
      Metric.mem_cthickening_of_dist_le
        point parentAxisPoint (6 * (4 * sigma))
        _ hparentAxis (by nlinarith)
  · exact hbox

theorem wz2_paper_dilated_cover_wide_carrier_covers
    {delta sigma : ℝ}
    {source : Kakeya.DeltaTube delta}
    {parent : Kakeya.DeltaTube sigma}
    (hdelta : 0 < delta)
    (hsigma : 0 < sigma)
    (hscale : delta ≤ sigma)
    (hsource : WZ1PaperTubeInLineClass source)
    (hparent : WZ1PaperTubeInLineClass parent)
    (hcover : WZ2PaperDilatedTubeCovers 2 source parent) :
    WZ2PaperWideTubeCarrierCovers source parent := by
  have hcontained :=
    wz2_paper_dilated_cover_carrier_covers_doubled_parent
      hdelta hsigma hscale hsource hparent hcover
  intro point hpoint
  have h :=
    hcontained hpoint
  rcases h with ⟨hthick, hbox⟩
  constructor
  · have haxis :
        tubeAxisLine
            (wz2PaperRelabelTube
              (targetScale := 4 * sigma) parent) =
          tubeAxisLine parent := rfl
    rw [haxis] at hthick
    convert hthick using 1 <;> ring_nf
  · exact hbox

/--
Paper `multiScaleWolffLem` nesting in literal carrier form.

Two exact-scale parents sharing one fine child satisfy the sharp line bound
`d(parent_rho,parent_sigma) ≤ rho / 2 + sigma / 2`.  At a common height in
the crop box this costs at most six times the line metric.  Including the
radius-`rho` source carrier therefore gives strict carrier containment once
`5 * rho ≤ sigma`.
-/
theorem WZ2PaperPartitioningCover.parent_carrier_covers_of_common_source
    {delta rho sigma : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarseRho : Kakeya.Streamlined.TubeFamily rho}
    {coarseSigma : Kakeya.Streamlined.TubeFamily sigma}
    (coverRho : WZ2PaperPartitioningCover fine coarseRho)
    (coverSigma : WZ2PaperPartitioningCover fine coarseSigma)
    (hrho : 0 < rho)
    (hsigma : 0 < sigma)
    (hgap : 5 * rho ≤ sigma)
    (hfine : WZ1PaperIsLineClass fine)
    (hcoarseRho : WZ1PaperIsLineClass coarseRho)
    (hcoarseSigma : WZ1PaperIsLineClass coarseSigma)
    (source : Fin fine.card)
    (parentRho : Fin coarseRho.card)
    (parentSigma : Fin coarseSigma.card)
    (hparentRho : coverRho.parent source = parentRho)
    (hparentSigma : coverSigma.parent source = parentSigma) :
    WZ2PaperTubeCarrierCovers
      (coarseRho.tube parentRho)
      (coarseSigma.tube parentSigma) := by
  intro point hpoint
  rcases hpoint with ⟨hpointThick, hpointBox⟩
  rcases
      exists_dist_le_of_mem_cthickening_closed
        (isClosed_tubeAxisLine (coarseRho.tube parentRho))
        (by positivity : 0 ≤ 6 * rho)
        hpointThick
    with ⟨middleAxisPoint, hmiddleAxis, hpointMiddle⟩
  let height := point (2 : Fin 3)
  let middleAtHeight :=
    wz1PaperAxisPointAtHeight (coarseRho.tube parentRho) height
  let coarseAtHeight :=
    wz1PaperAxisPointAtHeight (coarseSigma.tube parentSigma) height
  have hpointMiddleHeight :
      dist point middleAtHeight ≤ 12 * rho := by
    have hprojection :=
      wz1Paper_axisPointAtHeight_dist_point_le_two_mul
        (hcoarseRho parentRho) point middleAxisPoint hmiddleAxis
    simpa [middleAtHeight, dist_comm] using
      hprojection.trans (by nlinarith)
  have hmiddleFine :
      wz1PaperLineDistance
          (coarseRho.tube parentRho) (fine.tube source) ≤
        rho / 2 := by
    rw [wz1PaperLineDistance_symm]
    rw [← hparentRho]
    exact coverRho.parent_covers source
  have hfineCoarse :
      wz1PaperLineDistance
          (fine.tube source) (coarseSigma.tube parentSigma) ≤
        sigma / 2 := by
    rw [← hparentSigma]
    exact coverSigma.parent_covers source
  have hmiddleCoarse :
      wz1PaperLineDistance
          (coarseRho.tube parentRho)
          (coarseSigma.tube parentSigma) ≤
        rho / 2 + sigma / 2 := by
    exact
      (wz1PaperLineDistance_triangle
        (coarseRho.tube parentRho)
        (fine.tube source)
        (coarseSigma.tube parentSigma)).trans
          (add_le_add hmiddleFine hfineCoarse)
  have hheight : |height| ≤ 1 := by
    simpa [height, Kakeya.Streamlined.axisBox] using hpointBox.2.2
  have haxisDistance :
      dist middleAtHeight coarseAtHeight ≤
        3 * rho + 3 * sigma := by
    have h :=
      wz1PaperAxisPointAtHeight_dist_le
        (hcoarseRho parentRho) (hcoarseSigma parentSigma)
        hheight
    dsimp only [middleAtHeight, coarseAtHeight]
    exact h.trans (by nlinarith)
  have hpointCoarse :
      dist point coarseAtHeight ≤ 6 * sigma := by
    calc
      dist point coarseAtHeight ≤
          dist point middleAtHeight +
            dist middleAtHeight coarseAtHeight :=
        dist_triangle _ _ _
      _ ≤ 12 * rho + (3 * rho + 3 * sigma) := by gcongr
      _ ≤ 6 * sigma := by nlinarith
  have hcoarseAxis :
      coarseAtHeight ∈ tubeAxisLine (coarseSigma.tube parentSigma) :=
    wz1PaperAxisPointAtHeight_mem_axis
      (coarseSigma.tube parentSigma) height
  exact
    ⟨Metric.mem_cthickening_of_dist_le
        point coarseAtHeight (6 * sigma)
        _ hcoarseAxis hpointCoarse,
      hpointBox⟩

/-- Relabel every tube in a family by a common radius. -/
def wz2PaperRelabelFamily
    {sourceScale targetScale : ℝ}
    (family : Kakeya.Streamlined.TubeFamily sourceScale) :
    Kakeya.Streamlined.TubeFamily targetScale where
  card := family.card
  tube := fun index =>
    wz2PaperRelabelTube (targetScale := targetScale)
      (family.tube index)

@[simp] theorem wz2PaperRelabelFamily_tube
    {sourceScale targetScale : ℝ}
    (family : Kakeya.Streamlined.TubeFamily sourceScale)
    (index : Fin family.card) :
    (wz2PaperRelabelFamily
        (targetScale := targetScale) family).tube index =
      wz2PaperRelabelTube (targetScale := targetScale)
        (family.tube index) :=
  rfl

theorem WZ1PaperIsLineClass.relabel
    {sourceScale targetScale : ℝ}
    {family : Kakeya.Streamlined.TubeFamily sourceScale}
    (hline : WZ1PaperIsLineClass family) :
    WZ1PaperIsLineClass
      (wz2PaperRelabelFamily
        (targetScale := targetScale) family) := by
  intro index
  exact wz2PaperRelabelTube_lineClass (hline index)

theorem WZ1PaperIsEssentiallyDistinct.relabel_of_factor_le
    {sourceScale targetScale factor : ℝ}
    {family : Kakeya.Streamlined.TubeFamily sourceScale}
    (hdistinct :
      ∀ first second, first ≠ second →
        factor * sourceScale <
          wz1PaperLineDistance
            (family.tube first) (family.tube second))
    (hfactor : targetScale ≤ factor * sourceScale) :
    WZ1PaperIsEssentiallyDistinct
      (wz2PaperRelabelFamily
        (targetScale := targetScale) family) := by
  intro first second hne
  change targetScale <
    wz1PaperLineDistance
      (family.tube first) (family.tube second)
  exact hfactor.trans_lt (hdistinct first second hne)

/--
Repackage a factor-two assigned cover as a strict literal carrier cover after
quadrupling the parent radius.  Strong parent separation is measured at the
original parent radius.
-/
noncomputable def
    WZ2PaperDilatedTubeCover.toLiteralQuadrupledParent
    {delta sigma : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily sigma}
    (cover : WZ2PaperDilatedTubeCover 2 fine coarse)
    (hdelta : 0 < delta)
    (hsigma : 0 < sigma)
    (hscale : delta ≤ sigma)
    (hfine : WZ1PaperIsLineClass fine)
    (hcoarse : WZ1PaperIsLineClass coarse)
    (hseparated :
      ∀ first second, first ≠ second →
        6400 * sigma <
          wz1PaperLineDistance
            (coarse.tube first) (coarse.tube second)) :
    WZ2PaperLiteralDilatedPartitioningCover
      fine
      (wz2PaperRelabelFamily
        (targetScale := 4 * sigma) coarse) := by
  let relabelledCoarse :=
    wz2PaperRelabelFamily (targetScale := 4 * sigma) coarse
  let relabelledAssigned :
      WZ2PaperDilatedTubeCover 2 fine relabelledCoarse :=
    { parent := cover.parent
      parent_surjective := cover.parent_surjective
      parent_covers := by
        intro source
        have h := cover.parent_covers source
        unfold WZ2PaperDilatedTubeCovers at h ⊢
        simpa [relabelledCoarse] using h.trans (by nlinarith) }
  apply
    relabelledAssigned.toLiteralPartitioningOfStrongSeparation
      hdelta (by positivity : 0 < 4 * sigma)
      hfine (hcoarse.relabel)
  · intro source
    exact
      wz2_paper_dilated_cover_carrier_covers_doubled_parent
        hdelta hsigma hscale
        (hfine source) (hcoarse (cover.parent source))
        (cover.parent_covers source)
  · intro first second hne
    have h := hseparated first second hne
    change
      1600 * (4 * sigma) <
        wz1PaperLineDistance
          (coarse.tube first) (coarse.tube second)
    nlinarith

end Kakeya.Assouad

end
