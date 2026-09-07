import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicAffineEquiv
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperCarrierContainmentLineDistance
import MyLeanRepo.Kakeya.Assouad.AnisotropicRescaling.CoaxialCoverGeometry
import MyLeanRepo.Kakeya.Assouad.Targets.BoundedThreeTubeImageCover

/-!
# Height-anchored three-tube cover for the Section 6 affine map

The original three-tube constructor records only that its three children are
coaxial.  Nearby-scale parent transport needs more: the slot labels must use
the same longitudinal anchors for every source tube.  Here slot zero starts at
the affine image of the oriented source axis at height `c - delta`, slot one
starts one image-direction unit later, and slot two ends at the affine image
of the oriented source axis at height `d + delta`.

This is the canonical slot data used by the global slot pigeonhole.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

/-- Positively oriented normalized image direction of one source tube. -/
def anisotropicAnchoredDirection
    (g : SlopeFunction) (c d m : ℝ)
    {delta : ℝ} (source : Kakeya.DeltaTube delta) : Point3 :=
  let image := dPhiLin g c d m (wz1PaperDirection source)
  (‖image‖⁻¹ : ℝ) • image

theorem anisotropicAnchoredDirection_unit
    (g : SlopeFunction) {c d m delta : ℝ}
    (hcd : c < d) (hm : 0 < m)
    (source : Kakeya.DeltaTube delta) :
    ‖anisotropicAnchoredDirection g c d m source‖ = 1 := by
  let direction := wz1PaperDirection source
  let image := dPhiLin g c d m direction
  have hdirection : direction ≠ 0 := by
    intro hzero
    have := congrArg norm hzero
    rw [wz1PaperDirection_norm source, norm_zero] at this
    norm_num at this
  have himage : image ≠ 0 := by
    intro hzero
    have himageZero :
        dPhiLin g c d m direction = dPhiLin g c d m 0 := by
      rw [show dPhiLin g c d m direction = image by rfl, hzero]
      simp [dPhiLin, point3]
    exact hdirection (dPhiLin_injective g c d m hcd hm himageZero)
  have himageNorm : 0 < ‖image‖ := norm_pos_iff.mpr himage
  change ‖(‖image‖⁻¹ : ℝ) • image‖ = 1
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  field_simp [himageNorm.ne']

/-- Lower common-height anchor for one source axis. -/
def anisotropicAnchoredLowerPoint
    (g : SlopeFunction) (c d m padding : ℝ)
    {sourceScale : ℝ} (source : Kakeya.DeltaTube sourceScale) : Point3 :=
  anisotropicRescalingMap g c d m
    (wz1PaperAxisPointAtHeight source (c - padding))

/-- Upper common-height anchor for one source axis. -/
def anisotropicAnchoredUpperPoint
    (g : SlopeFunction) (c d m padding : ℝ)
    {sourceScale : ℝ} (source : Kakeya.DeltaTube sourceScale) : Point3 :=
  anisotropicRescalingMap g c d m
    (wz1PaperAxisPointAtHeight source (d + padding))

/-- Length of the affine image of the oriented axis between the two common
height anchors. -/
def anisotropicAnchoredLength
    (g : SlopeFunction) (c d m padding : ℝ)
    {sourceScale : ℝ} (source : Kakeya.DeltaTube sourceScale) : ℝ :=
  ((d - c + 2 * padding) / (wz1PaperDirection source 2)) *
    ‖dPhiLin g c d m (wz1PaperDirection source)‖

/-- Canonical basepoint for one of the three synchronized child slots. -/
def anisotropicAnchoredChildBase
    (g : SlopeFunction) (c d m padding : ℝ)
    {sourceScale : ℝ} (source : Kakeya.DeltaTube sourceScale)
    (slot : Fin 3) : Point3 :=
  let lower := anisotropicAnchoredLowerPoint g c d m padding source
  let upper := anisotropicAnchoredUpperPoint g c d m padding source
  let direction := anisotropicAnchoredDirection g c d m source
  Fin.cases lower
    (fun remaining : Fin 2 =>
      Fin.cases (lower + direction)
        (fun _ : Fin 1 => upper - direction) remaining) slot

/-- Canonical target child at the exact rescaled fine radius. -/
def anisotropicAnchoredChildTube
    (g : SlopeFunction) (c d m padding rho : ℝ)
    (hcd : c < d) (hm : 0 < m)
    {sourceScale : ℝ} (source : Kakeya.DeltaTube sourceScale) (slot : Fin 3) :
    Kakeya.DeltaTube rho where
  base := anisotropicAnchoredChildBase g c d m padding source slot
  direction := anisotropicAnchoredDirection g c d m source
  direction_unit := anisotropicAnchoredDirection_unit g hcd hm source

@[simp] theorem anisotropicAnchoredChildTube_direction
    (g : SlopeFunction) {c d m delta rho : ℝ}
    (hcd : c < d) (hm : 0 < m)
    (source : Kakeya.DeltaTube delta) (slot : Fin 3) :
    (anisotropicAnchoredChildTube g c d m delta rho hcd hm source slot).direction =
      anisotropicAnchoredDirection g c d m source := rfl

@[simp] theorem anisotropicAnchoredChildBase_zero
    (g : SlopeFunction) (c d m delta : ℝ)
    (source : Kakeya.DeltaTube delta) :
    anisotropicAnchoredChildBase g c d m delta source 0 =
      anisotropicAnchoredLowerPoint g c d m delta source := rfl

@[simp] theorem anisotropicAnchoredChildBase_one
    (g : SlopeFunction) (c d m delta : ℝ)
    (source : Kakeya.DeltaTube delta) :
    anisotropicAnchoredChildBase g c d m delta source 1 =
      anisotropicAnchoredLowerPoint g c d m delta source +
        anisotropicAnchoredDirection g c d m source := rfl

@[simp] theorem anisotropicAnchoredChildBase_two
    (g : SlopeFunction) (c d m delta : ℝ)
    (source : Kakeya.DeltaTube delta) :
    anisotropicAnchoredChildBase g c d m delta source 2 =
      anisotropicAnchoredUpperPoint g c d m delta source -
        anisotropicAnchoredDirection g c d m source := rfl

/-- Affine-line formula for the exact triangular map. -/
theorem anisotropicRescalingMap_add_smul
    (g : SlopeFunction) (c d m : ℝ)
    (point direction : Point3) (parameter : ℝ) :
    anisotropicRescalingMap g c d m (point + parameter • direction) =
      anisotropicRescalingMap g c d m point +
        parameter • dPhiLin g c d m direction := by
  ext coordinate
  fin_cases coordinate <;>
    simp [anisotropicRescalingMap, dPhiLin, point3] <;> ring

theorem anisotropicAnchoredUpper_sub_lower
    (g : SlopeFunction) {c d m delta : ℝ}
    (hcd : c < d) (hm : 0 < m)
    (source : Kakeya.DeltaTube delta)
    (hsource : WZ1PaperTubeInLineClass source) :
    anisotropicAnchoredUpperPoint g c d m delta source -
        anisotropicAnchoredLowerPoint g c d m delta source =
      anisotropicAnchoredLength g c d m delta source •
        anisotropicAnchoredDirection g c d m source := by
  let direction := wz1PaperDirection source
  let vertical := direction 2
  let image := dPhiLin g c d m direction
  have hvertical : vertical ≠ 0 := by
    have : (1 / 2 : ℝ) ≤ vertical := hsource.1
    linarith
  have haxis :
      wz1PaperAxisPointAtHeight source (d + delta) =
        wz1PaperAxisPointAtHeight source (c - delta) +
          ((d - c + 2 * delta) / vertical) • direction := by
    dsimp only [wz1PaperAxisPointAtHeight, vertical, direction]
    module
  rw [anisotropicAnchoredUpperPoint, anisotropicAnchoredLowerPoint, haxis]
  rw [anisotropicRescalingMap_add_smul]
  dsimp only [anisotropicAnchoredLength, anisotropicAnchoredDirection,
    direction, vertical, image]
  have himage : image ≠ 0 := by
    intro hzero
    have hdirection : direction ≠ 0 := by
      intro hdirectionZero
      have := congrArg norm hdirectionZero
      rw [wz1PaperDirection_norm source, norm_zero] at this
      norm_num at this
    have himageZero :
        dPhiLin g c d m direction = dPhiLin g c d m 0 := by
      rw [show dPhiLin g c d m direction = image by rfl, hzero]
      simp [dPhiLin, point3]
    exact hdirection (dPhiLin_injective g c d m hcd hm himageZero)
  have himageNorm : ‖image‖ ≠ 0 := (norm_ne_zero_iff.mpr himage)
  have hvertical' :
      (wz1PaperDirection source).ofLp 2 ≠ 0 := hvertical
  have hleft :
      anisotropicRescalingMap g c d m
            (wz1PaperAxisPointAtHeight source (c - delta)) +
          ((d - c + 2 * delta) / vertical) • image -
        anisotropicRescalingMap g c d m
          (wz1PaperAxisPointAtHeight source (c - delta)) =
        ((d - c + 2 * delta) / vertical) • image := by
    abel
  rw [hleft]
  rw [smul_smul]
  congr 1
  have hcancel : ‖image‖ * ‖image‖⁻¹ = 1 :=
    mul_inv_cancel₀ himageNorm
  rw [show
    (d - c + 2 * delta) / vertical * ‖image‖ * ‖image‖⁻¹ =
      ((d - c + 2 * delta) / vertical) *
        (‖image‖ * ‖image‖⁻¹) by ring,
    hcancel, mul_one]

theorem anisotropicAnchoredLength_nonneg
    (g : SlopeFunction) {c d m delta : ℝ}
    (hcd : c < d) (hdelta : 0 ≤ delta)
    (source : Kakeya.DeltaTube delta)
    (hsource : WZ1PaperTubeInLineClass source) :
    0 ≤ anisotropicAnchoredLength g c d m delta source := by
  have hvertical : 0 < wz1PaperDirection source 2 := by
    linarith [hsource.1]
  exact mul_nonneg
    (div_nonneg (by linarith) hvertical.le) (norm_nonneg _)

theorem anisotropicAnchoredLength_lt_three
    (g : SlopeFunction) {c d m delta : ℝ}
    (hg : g.IsNormalized)
    (hdelta : 0 < delta) (hcd : c < d)
    (hdc : d - c ≤ 1 / 25)
    (hdeltaSmall : delta ≤ 1 / 100)
    (hrhoSmall : 2 * delta / (d - c) ≤ 1 / 4)
    (hm : 0 < m) (hmOne : m ≤ 1)
    (hsub : Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1)
    (source : Kakeya.DeltaTube delta)
    (hsource : WZ1PaperTubeInLineClass source) :
    anisotropicAnchoredLength g c d m delta source < 3 := by
  let direction := wz1PaperDirection source
  let gmid := g (c + (d - c) / 2)
  let K := m * (d - c) / 2
  let S := 2 / (d - c)
  have hmid : c + (d - c) / 2 ∈ Set.Icc (-1 : ℝ) 1 :=
    hsub ⟨by linarith, by linarith⟩
  have hgmid : |gmid| ≤ 1 := (hg _ hmid).1
  have hKnonneg : 0 ≤ K := by
    dsimp only [K]
    positivity
  have hKle : K ≤ 1 := by
    dsimp only [K]
    nlinarith
  have hKabs : |K| ≤ 1 := by
    rw [abs_of_nonneg hKnonneg]
    exact hKle
  have hbound := extended_image_axis_lt_3
    hdelta hcd (wz1PaperDirection_norm source)
    (by simpa [abs_of_nonneg (by linarith [hsource.1] :
        0 ≤ wz1PaperDirection source 2)] using hsource.1)
    hgmid hKabs (show S = 2 / (d - c) from rfl)
    hdc hdeltaSmall hrhoSmall
  have hvertical : 0 ≤ direction 2 := by linarith [hsource.1]
  simpa [anisotropicAnchoredLength, direction, gmid, K, S,
    abs_of_nonneg hvertical, dPhiLin] using hbound

/-- The paper-oriented axis point is the unique point on the supporting line
at its prescribed height. -/
theorem wz1PaperAxisPointAtHeight_eq_of_mem_axis'
    {delta : ℝ} {source : Kakeya.DeltaTube delta}
    (hsource : WZ1PaperTubeInLineClass source)
    {point : Point3} (hpoint : point ∈ tubeAxisLine source) :
    wz1PaperAxisPointAtHeight source (point 2) = point := by
  have hdist := wz1Paper_axisPointAtHeight_dist_le_of_axis_point
    hsource (point 2) 0 hpoint (by simp)
  exact dist_eq_zero.mp (le_antisymm (by simpa using hdist) dist_nonneg)

/-- Every affine image of a source-axis point in the delta-extended slab lies
in the canonical three-slot axis cover. -/
theorem anisotropicAnchored_axis_image_mem_threeSegments
    (g : SlopeFunction) {c d m delta : ℝ}
    (hg : g.IsNormalized)
    (hdelta : 0 < delta) (hcd : c < d)
    (hdc : d - c ≤ 1 / 25)
    (hdeltaSmall : delta ≤ 1 / 100)
    (hrhoSmall : 2 * delta / (d - c) ≤ 1 / 4)
    (hm : 0 < m) (hmOne : m ≤ 1)
    (hsub : Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1)
    (source : Kakeya.DeltaTube delta)
    (hsource : WZ1PaperTubeInLineClass source)
    {point : Point3} (hpointAxis : point ∈ tubeAxisLine source)
    (hpointHeight : point 2 ∈ Set.Icc (c - delta) (d + delta)) :
    anisotropicRescalingMap g c d m point ∈
      Kakeya.unitSegment
          (anisotropicAnchoredChildBase g c d m delta source 0)
          (anisotropicAnchoredDirection g c d m source) ∪
        Kakeya.unitSegment
          (anisotropicAnchoredChildBase g c d m delta source 1)
          (anisotropicAnchoredDirection g c d m source) ∪
        Kakeya.unitSegment
          (anisotropicAnchoredChildBase g c d m delta source 2)
          (anisotropicAnchoredDirection g c d m source) := by
  let direction := wz1PaperDirection source
  let vertical := direction 2
  let image := dPhiLin g c d m direction
  let imageNorm := ‖image‖
  let lowerSource := wz1PaperAxisPointAtHeight source (c - delta)
  let lower := anisotropicAnchoredLowerPoint g c d m delta source
  let upper := anisotropicAnchoredUpperPoint g c d m delta source
  let targetDirection := anisotropicAnchoredDirection g c d m source
  let length := anisotropicAnchoredLength g c d m delta source
  have hvertical : 0 < vertical := by linarith [hsource.1]
  have himage : image ≠ 0 := by
    intro hzero
    have hdirection : direction ≠ 0 := by
      intro hdirectionZero
      have := congrArg norm hdirectionZero
      rw [wz1PaperDirection_norm source, norm_zero] at this
      norm_num at this
    have himageZero :
        dPhiLin g c d m direction = dPhiLin g c d m 0 := by
      rw [show dPhiLin g c d m direction = image by rfl, hzero]
      simp [dPhiLin, point3]
    exact hdirection (dPhiLin_injective g c d m hcd hm himageZero)
  have himageNorm : 0 < imageNorm := norm_pos_iff.mpr himage
  let parameter := ((point 2 - (c - delta)) / vertical) * imageNorm
  have hparameterNonneg : 0 ≤ parameter := by
    exact mul_nonneg
      (div_nonneg (by linarith [hpointHeight.1]) hvertical.le)
      himageNorm.le
  have hparameterLe : parameter ≤ length := by
    dsimp only [parameter, length, anisotropicAnchoredLength, imageNorm,
      image, direction, vertical]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact (div_le_div_iff_of_pos_right hvertical).2 (by
      linarith [hpointHeight.2])
  have hpointFromLower : point = lowerSource +
      ((point 2 - (c - delta)) / vertical) • direction := by
    calc
      point = wz1PaperAxisPointAtHeight source (point 2) :=
        (wz1PaperAxisPointAtHeight_eq_of_mem_axis' hsource hpointAxis).symm
      _ = lowerSource +
          ((point 2 - (c - delta)) / vertical) • direction := by
        dsimp only [lowerSource, wz1PaperAxisPointAtHeight, direction, vertical]
        have hverticalNe : wz1PaperDirection source 2 ≠ 0 := by
          linarith [hsource.1]
        ext coordinate
        simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
        field_simp [hverticalNe]
        ring
  have himagePoint : anisotropicRescalingMap g c d m point =
      lower + parameter • targetDirection := by
    rw [hpointFromLower, anisotropicRescalingMap_add_smul]
    dsimp only [lower, anisotropicAnchoredLowerPoint, parameter,
      targetDirection, anisotropicAnchoredDirection, imageNorm, image,
      direction, vertical]
    rw [smul_smul]
    have hcancel : ‖dPhiLin g c d m (wz1PaperDirection source)‖ *
        ‖dPhiLin g c d m (wz1PaperDirection source)‖⁻¹ = 1 :=
      mul_inv_cancel₀ (by simpa [image, imageNorm] using himageNorm.ne')
    rw [show
      (point 2 - (c - delta)) / wz1PaperDirection source 2 *
            ‖dPhiLin g c d m (wz1PaperDirection source)‖ *
          ‖dPhiLin g c d m (wz1PaperDirection source)‖⁻¹ =
        ((point 2 - (c - delta)) / wz1PaperDirection source 2) *
          (‖dPhiLin g c d m (wz1PaperDirection source)‖ *
            ‖dPhiLin g c d m (wz1PaperDirection source)‖⁻¹) by ring,
      hcancel, mul_one]
  have hupperLower : upper - lower = length • targetDirection := by
    simpa [upper, lower, length, targetDirection] using
      anisotropicAnchoredUpper_sub_lower g hcd hm source hsource
  rw [himagePoint]
  have hthree := three_segment_coverage length
    (anisotropicAnchoredLength_nonneg g hcd hdelta.le source hsource)
    (show length < 3 from by
      simpa [length] using anisotropicAnchoredLength_lt_three
        g hg hdelta hcd hdc hdeltaSmall hrhoSmall hm hmOne hsub
          source hsource) hupperLower
  simpa [anisotropicAnchoredChildBase_zero,
    anisotropicAnchoredChildBase_one, anisotropicAnchoredChildBase_two,
    lower, upper, targetDirection] using
      hthree ⟨parameter, hparameterNonneg, hparameterLe, rfl⟩

/-- The exact triangular map expands distances by at most its vertical factor
under the Section 6 parameter bounds. -/
theorem anisotropicRescalingMap_dist_le_height
    (g : SlopeFunction) {c d m S : ℝ}
    (hg : g.IsNormalized) (hcd : c < d)
    (hdc : d - c ≤ 1 / 25)
    (hm : 0 < m) (hmOne : m ≤ 1)
    (hsub : Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1)
    (hS : S = 2 / (d - c))
    (first second : Point3) :
    dist (anisotropicRescalingMap g c d m first)
        (anisotropicRescalingMap g c d m second) ≤
      S * dist first second := by
  let gmid := g (c + (d - c) / 2)
  let K := m * (d - c) / 2
  have hmid : c + (d - c) / 2 ∈ Set.Icc (-1 : ℝ) 1 :=
    hsub ⟨by linarith, by linarith⟩
  have hgmid : |gmid| ≤ 1 := (hg _ hmid).1
  have hKnonneg : 0 ≤ K := by
    dsimp only [K]
    positivity
  have hKle : K ≤ 1 := by
    dsimp only [K]
    nlinarith
  have hKabs : |K| ≤ 1 := by
    rw [abs_of_nonneg hKnonneg]
    exact hKle
  have hSge : 2 ≤ S := by
    rw [hS]
    have hdcPos : 0 < d - c := by linarith
    have hlarge : 50 ≤ 2 / (d - c) := by
      apply (le_div_iff₀ hdcPos).2
      nlinarith
    linarith
  have hdifference :
      anisotropicRescalingMap g c d m first -
          anisotropicRescalingMap g c d m second =
        point3
          ((first - second) 0 + gmid * (first - second) 1)
          (K * (first - second) 1)
          (S * (first - second) 2) := by
    ext coordinate
    fin_cases coordinate <;>
      simp [anisotropicRescalingMap, gmid, K, point3, hS] <;>
      field_simp [hcd.ne'] <;> ring
  rw [dist_eq_norm, dist_eq_norm, hdifference]
  exact anisotropicMap_opNorm_bound hgmid hKabs hSge (first - second)

theorem anisotropicAnchoredDirection_vertical
    (g : SlopeFunction) {c d m delta : ℝ}
    (hg : g.IsNormalized) (hcd : c < d)
    (hdc : d - c ≤ 1 / 25)
    (hm : 0 < m) (hmOne : m ≤ 1)
    (hsub : Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1)
    (source : Kakeya.DeltaTube delta)
    (hsource : WZ1PaperTubeInLineClass source) :
    (1 / 2 : ℝ) ≤
      |(anisotropicAnchoredDirection g c d m source) 2| := by
  have hraw := anisotropicMap_preservesVerticalChart
    g hg c d m hcd hm hmOne hdc hsub
      (wz1PaperDirection source) (wz1PaperDirection_norm source)
      (by
        simpa [abs_of_nonneg (by linarith [hsource.1] :
          0 ≤ wz1PaperDirection source 2)] using hsource.1)
  simpa [anisotropicAnchoredDirection, dPhiLin, point3,
    abs_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hraw

/-- The canonical three slots cover the affine image of the source tube
restricted to the active slab. -/
theorem anisotropicAnchored_three_child_cover
    (g : SlopeFunction) {c d m delta rho : ℝ}
    (hg : g.IsNormalized) (hdelta : 0 < delta) (hcd : c < d)
    (hdc : d - c ≤ 1 / 25)
    (hdeltaSmall : delta ≤ 1 / 100)
    (hrhoSmall : 2 * delta / (d - c) ≤ 1 / 4)
    (hrho : rho = 2 * delta / (d - c))
    (hm : 0 < m) (hmOne : m ≤ 1)
    (hsub : Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1)
    (source : Kakeya.DeltaTube delta)
    (hsource : WZ1PaperTubeInLineClass source) :
    anisotropicRescalingMap g c d m ''
        (source.carrier ∩ horizontalSlab c d) ⊆
      ⋃ slot : Fin 3,
        (anisotropicAnchoredChildTube
          g c d m delta rho hcd hm source slot).carrier := by
  let axis := Kakeya.unitSegment source.base source.direction
  have haxisCompact : IsCompact axis :=
    isCompact_Icc.image
      (continuous_const.add (continuous_id.smul continuous_const))
  have hsourceCarrier : source.carrier = Metric.cthickening delta axis := rfl
  have hsourceCarrierUnion :
      Metric.cthickening delta axis =
        ⋃ axisPoint ∈ axis, Metric.closedBall axisPoint delta :=
    haxisCompact.cthickening_eq_biUnion_closedBall hdelta.le
  intro imagePoint himagePoint
  rcases himagePoint with ⟨sourcePoint, hsourcePoint, rfl⟩
  have hsourceCarrierPoint : sourcePoint ∈ Metric.cthickening delta axis := by
    rw [← hsourceCarrier]
    exact hsourcePoint.1
  rw [hsourceCarrierUnion] at hsourceCarrierPoint
  rcases Set.mem_iUnion₂.mp hsourceCarrierPoint with
    ⟨axisPoint, haxisPoint, hsourceDistance⟩
  have hsourceDistance' : dist sourcePoint axisPoint ≤ delta := by
    simpa [Metric.mem_closedBall] using hsourceDistance
  have haxisHeight : axisPoint 2 ∈ Set.Icc (c - delta) (d + delta) := by
    have hcoordinate : |axisPoint 2 - sourcePoint 2| ≤ delta := by
      calc
        |axisPoint 2 - sourcePoint 2| ≤ dist axisPoint sourcePoint :=
          coord2_dist_le
        _ = dist sourcePoint axisPoint := dist_comm _ _
        _ ≤ delta := hsourceDistance'
    rw [abs_le] at hcoordinate
    exact ⟨by linarith [hsourcePoint.2.1],
      by linarith [hsourcePoint.2.2]⟩
  have himageAxis : anisotropicRescalingMap g c d m axisPoint ∈
      Kakeya.unitSegment
          (anisotropicAnchoredChildBase g c d m delta source 0)
          (anisotropicAnchoredDirection g c d m source) ∪
        Kakeya.unitSegment
          (anisotropicAnchoredChildBase g c d m delta source 1)
          (anisotropicAnchoredDirection g c d m source) ∪
        Kakeya.unitSegment
          (anisotropicAnchoredChildBase g c d m delta source 2)
          (anisotropicAnchoredDirection g c d m source) :=
    anisotropicAnchored_axis_image_mem_threeSegments
      g hg hdelta hcd hdc hdeltaSmall hrhoSmall hm hmOne hsub
        source hsource (by
          rcases haxisPoint with ⟨parameter, hparameter, rfl⟩
          exact ⟨parameter, rfl⟩) haxisHeight
  have hS : 2 / (d - c) = 2 / (d - c) := rfl
  have himageDistance :
      dist (anisotropicRescalingMap g c d m sourcePoint)
          (anisotropicRescalingMap g c d m axisPoint) ≤
        (2 / (d - c)) * delta := by
    calc
      dist (anisotropicRescalingMap g c d m sourcePoint)
          (anisotropicRescalingMap g c d m axisPoint) ≤
          (2 / (d - c)) * dist sourcePoint axisPoint :=
        anisotropicRescalingMap_dist_le_height
          g hg hcd hdc hm hmOne hsub hS sourcePoint axisPoint
      _ ≤ (2 / (d - c)) * delta := by
        gcongr
  rcases himageAxis with hzeroOrOne | htwo
  · rcases hzeroOrOne with hzero | hone
    · refine Set.mem_iUnion.mpr ⟨(0 : Fin 3), ?_⟩
      exact Metric.mem_cthickening_of_dist_le _
        (anisotropicRescalingMap g c d m axisPoint) rho _ hzero
        (by rw [hrho]; convert himageDistance using 1 <;> ring)
    · refine Set.mem_iUnion.mpr ⟨(1 : Fin 3), ?_⟩
      exact Metric.mem_cthickening_of_dist_le _
        (anisotropicRescalingMap g c d m axisPoint) rho _ hone
        (by rw [hrho]; convert himageDistance using 1 <;> ring)
  · refine Set.mem_iUnion.mpr ⟨(2 : Fin 3), ?_⟩
    exact Metric.mem_cthickening_of_dist_le _
      (anisotropicRescalingMap g c d m axisPoint) rho _ htwo
      (by rw [hrho]; convert himageDistance using 1 <;> ring)

/-- Canonical source-indexed three-tube cover with globally meaningful slot
labels. -/
def anisotropicAnchoredThreeTubeImageCover
    (g : SlopeFunction) {c d m delta rho : ℝ}
    (hg : g.IsNormalized) (hdelta : 0 < delta) (hcd : c < d)
    (hdc : d - c ≤ 1 / 25)
    (hdeltaSmall : delta ≤ 1 / 100)
    (hrhoSmall : 2 * delta / (d - c) ≤ 1 / 4)
    (hrho : rho = 2 * delta / (d - c))
    (hm : 0 < m) (hmOne : m ≤ 1)
    (hsub : Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1)
    (family : Kakeya.Streamlined.TubeFamily delta)
    (hfamily : WZ1PaperIsLineClass family) :
    ThreeTubeImageCover (rho := rho) family
      (anisotropicRescalingMap g c d m)
      (fun source =>
        (family.tube source).carrier ∩ horizontalSlab c d) where
  tube source slot := anisotropicAnchoredChildTube
    g c d m delta rho hcd hm (family.tube source) slot
  covered source := anisotropicAnchored_three_child_cover
    g hg hdelta hcd hdc hdeltaSmall hrhoSmall hrho hm hmOne hsub
      (family.tube source) (hfamily source)
  vertical source _slot := anisotropicAnchoredDirection_vertical
    g hg hcd hdc hm hmOne hsub (family.tube source) (hfamily source)

/-- The synchronized slot cover is coaxial with the exact affine image of the
source supporting line. -/
theorem anisotropicAnchoredChildTube_axis
    (g : SlopeFunction) {c d m delta rho : ℝ}
    (hcd : c < d) (hm : 0 < m)
    (source : Kakeya.DeltaTube delta)
    (hsource : WZ1PaperTubeInLineClass source)
    (slot : Fin 3) :
    tubeAxisLine
        (anisotropicAnchoredChildTube
          g c d m delta rho hcd hm source slot) =
      anisotropicRescalingMap g c d m '' tubeAxisLine source := by
  let sourceAnchor := wz1PaperAxisPointAtHeight source (c - delta)
  let targetAnchor := anisotropicAnchoredLowerPoint g c d m delta source
  let imageDirection := dPhiLin g c d m (wz1PaperDirection source)
  let targetDirection := anisotropicAnchoredDirection g c d m source
  have hsourceAnchor : sourceAnchor ∈ tubeAxisLine source :=
    wz1PaperAxisPointAtHeight_mem_axis source (c - delta)
  have himageDirection : imageDirection ≠ 0 := by
    intro hzero
    have hsourceDirection : wz1PaperDirection source ≠ 0 := by
      intro hsourceZero
      have := congrArg norm hsourceZero
      rw [wz1PaperDirection_norm source, norm_zero] at this
      norm_num at this
    have himageZero :
        dPhiLin g c d m (wz1PaperDirection source) =
          dPhiLin g c d m 0 := by
      rw [show dPhiLin g c d m (wz1PaperDirection source) =
        imageDirection by rfl, hzero]
      simp [dPhiLin, point3]
    exact hsourceDirection
      (dPhiLin_injective g c d m hcd hm himageZero)
  have himageNorm : 0 < ‖imageDirection‖ :=
    norm_pos_iff.mpr himageDirection
  have hsourceLine : tubeAxisLine source =
      {point | ∃ parameter : ℝ,
        point = sourceAnchor + parameter • wz1PaperDirection source} := by
    ext point
    constructor
    · intro hpoint
      rcases wz1Paper_axis_exists_parameter hsource hpoint with
        ⟨parameter, hparameter⟩
      rcases wz1Paper_axis_exists_parameter hsource hsourceAnchor with
        ⟨anchorParameter, hanchorParameter⟩
      refine ⟨parameter - anchorParameter, ?_⟩
      rw [hparameter, hanchorParameter]
      module
    · rintro ⟨parameter, rfl⟩
      rcases hsourceAnchor with ⟨anchorParameter, hanchorParameter⟩
      refine ⟨anchorParameter +
          (if 0 ≤ source.direction 2 then parameter else -parameter), ?_⟩
      unfold wz1PaperDirection
      split_ifs <;> rw [hanchorParameter] <;> module
  have htargetBase :
      (anisotropicAnchoredChildTube
        g c d m delta rho hcd hm source slot).base ∈
        {point | ∃ parameter : ℝ,
          point = targetAnchor + parameter • targetDirection} := by
    fin_cases slot
    · refine ⟨0, ?_⟩
      change anisotropicAnchoredChildBase g c d m delta source 0 = _
      rw [anisotropicAnchoredChildBase_zero]
      simp [targetAnchor]
    · refine ⟨1, ?_⟩
      change anisotropicAnchoredChildBase g c d m delta source 1 = _
      rw [anisotropicAnchoredChildBase_one]
      simp [targetAnchor, targetDirection]
    · let length := anisotropicAnchoredLength g c d m delta source
      have hupper := anisotropicAnchoredUpper_sub_lower
        g hcd hm source hsource
      refine ⟨length - 1, ?_⟩
      change anisotropicAnchoredChildBase g c d m delta source 2 = _
      rw [anisotropicAnchoredChildBase_two]
      have hupperEq :
          anisotropicAnchoredUpperPoint g c d m delta source =
            targetAnchor + length • targetDirection := by
        calc
          anisotropicAnchoredUpperPoint g c d m delta source =
              (anisotropicAnchoredUpperPoint g c d m delta source -
                  anisotropicAnchoredLowerPoint g c d m delta source) +
                anisotropicAnchoredLowerPoint g c d m delta source := by abel
          _ = length • targetDirection + targetAnchor := by
            rw [hupper]
          _ = targetAnchor + length • targetDirection := by abel
      rw [hupperEq]
      module
  have hchildDirection :
      (anisotropicAnchoredChildTube
        g c d m delta rho hcd hm source slot).direction =
        targetDirection := rfl
  have htargetAnchor :
      anisotropicRescalingMap g c d m sourceAnchor = targetAnchor := rfl
  ext point
  constructor
  · rintro ⟨parameter, rfl⟩
    rcases htargetBase with ⟨baseParameter, hbaseParameter⟩
    rw [hsourceLine]
    refine ⟨sourceAnchor +
        ((baseParameter + parameter) / ‖imageDirection‖) •
          wz1PaperDirection source,
      ⟨(baseParameter + parameter) / ‖imageDirection‖, rfl⟩, ?_⟩
    calc
      anisotropicRescalingMap g c d m
          (sourceAnchor +
            ((baseParameter + parameter) / ‖imageDirection‖) •
              wz1PaperDirection source) =
          anisotropicRescalingMap g c d m sourceAnchor +
            ((baseParameter + parameter) / ‖imageDirection‖) •
              dPhiLin g c d m (wz1PaperDirection source) :=
        anisotropicRescalingMap_add_smul _ _ _ _ _ _ _
      _ = targetAnchor + (baseParameter + parameter) •
            targetDirection := by
        rw [htargetAnchor]
        dsimp only [targetDirection, anisotropicAnchoredDirection,
          imageDirection]
        rw [smul_smul]
        congr 1
      _ = (anisotropicAnchoredChildTube
              g c d m delta rho hcd hm source slot).base +
            parameter •
              (anisotropicAnchoredChildTube
                g c d m delta rho hcd hm source slot).direction := by
        rw [hbaseParameter, hchildDirection]
        module
  · rintro ⟨sourcePoint, hsourcePoint, rfl⟩
    rw [hsourceLine] at hsourcePoint
    rcases hsourcePoint with ⟨parameter, rfl⟩
    rcases htargetBase with ⟨baseParameter, hbaseParameter⟩
    refine ⟨parameter * ‖imageDirection‖ - baseParameter, ?_⟩
    calc
      anisotropicRescalingMap g c d m
          (sourceAnchor + parameter • wz1PaperDirection source) =
          anisotropicRescalingMap g c d m sourceAnchor +
            parameter • dPhiLin g c d m (wz1PaperDirection source) :=
        anisotropicRescalingMap_add_smul _ _ _ _ _ _ _
      _ = targetAnchor +
            (parameter * ‖imageDirection‖) • targetDirection := by
        rw [htargetAnchor]
        dsimp only [targetDirection, anisotropicAnchoredDirection,
          imageDirection]
        rw [smul_smul]
        have hcancel : ‖dPhiLin g c d m (wz1PaperDirection source)‖ *
            ‖dPhiLin g c d m (wz1PaperDirection source)‖⁻¹ = 1 :=
          mul_inv_cancel₀ (by simpa [imageDirection] using himageNorm.ne')
        rw [show
          parameter * ‖dPhiLin g c d m (wz1PaperDirection source)‖ *
                ‖dPhiLin g c d m (wz1PaperDirection source)‖⁻¹ =
            parameter *
              (‖dPhiLin g c d m (wz1PaperDirection source)‖ *
                ‖dPhiLin g c d m (wz1PaperDirection source)‖⁻¹) by ring,
          hcancel, mul_one]
      _ = (anisotropicAnchoredChildTube
              g c d m delta rho hcd hm source slot).base +
            (parameter * ‖imageDirection‖ - baseParameter) •
              (anisotropicAnchoredChildTube
                g c d m delta rho hcd hm source slot).direction := by
        rw [hbaseParameter, hchildDirection]
        module

/-- Coaxial strengthening of the canonical synchronized-slot cover. -/
def anisotropicAnchoredCoaxialThreeTubeImageCover
    (g : SlopeFunction) {c d m delta rho : ℝ}
    (hg : g.IsNormalized) (hdelta : 0 < delta) (hcd : c < d)
    (hdc : d - c ≤ 1 / 25)
    (hdeltaSmall : delta ≤ 1 / 100)
    (hrhoSmall : 2 * delta / (d - c) ≤ 1 / 4)
    (hrho : rho = 2 * delta / (d - c))
    (hm : 0 < m) (hmOne : m ≤ 1)
    (hsub : Set.Icc c d ⊆ Set.Icc (-1 : ℝ) 1)
    (family : Kakeya.Streamlined.TubeFamily delta)
    (hfamily : WZ1PaperIsLineClass family) :
    CoaxialThreeTubeImageCover (rho := rho) family
      (anisotropicRescalingMap g c d m)
      (fun source =>
        (family.tube source).carrier ∩ horizontalSlab c d) where
  toThreeTubeImageCover :=
    anisotropicAnchoredThreeTubeImageCover g hg hdelta hcd hdc
      hdeltaSmall hrhoSmall hrho hm hmOne hsub family hfamily
  coaxial source _hsource slot :=
    anisotropicAnchoredChildTube_axis
      g hcd hm (family.tube source) (hfamily source) slot

end Kakeya.Assouad

end
