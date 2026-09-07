import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.AnisotropicADTransfer
import MyLeanRepo.Kakeya.Assouad.WZ1.ADPigeonhole
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23HeavyFiberThreshold

/-!
# Heavy local fibers for the frozen pure-WZ2 plane-map interface

The WZ1 helper uses the older ordinary-tube shading API.  This paper-shading
version keeps the occupied subtype anchor from `PureWZ2LocalGrainData` and
performs the same finite-cover pigeonhole without extending or weakening the
frozen Node-5 record.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Metric Set

/-- One heavy full normal-projection fiber inside an explicit paper source. -/
structure PureWZ2LocalProjectionHeavyFiberInSource
    {delta sigma rho : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (C : ENNReal)
    (localGrains : PureWZ2LocalGrainData shading sigma C)
    (anchor : {point : Point3 // point ∈ shading.union})
    (source : Set Point3) where
  center : ℝ
  grain : Set Point3
  grain_eq :
    grain = source ∩
      (fun point : Point3 =>
        inner ℝ point (localGrains.planeMap anchor)) ⁻¹'
          Metric.closedBall center rho
  grain_measurable : MeasurableSet grain
  grain_finite : volume grain ≠ ⊤
  grain_in_source : grain ⊆ source
  grain_in_shading : grain ⊆ shading.union
  grain_in_anchor_ball :
    grain ⊆ Metric.closedBall (anchor : Point3) (Real.sqrt rho)
  grain_square : ∀ point ∈ grain,
    |point 0 - anchor.1 0| ≤ Real.sqrt rho ∧
      |point 1 - anchor.1 1| ≤ Real.sqrt rho
  grain_local_strip : ∀ point ∈ grain,
    |inner ℝ point (localGrains.planeMap anchor) - center| ≤ rho
  mass_retention :
    volume source ≤
      ((2 * C) * Kakeya.realRpowENN
        (Real.sqrt rho / rho) (1 - sigma)) * volume grain

private lemma pureWZ2_axisBox_norm_le_four
    {point : Point3}
    (hpoint : point ∈ Kakeya.Streamlined.axisBox 2 2 2) :
    ‖point‖ ≤ 4 := by
  have hnorm := point3_coord_norm_sq point
  have hx : |point 0| ≤ 1 := by
    simpa [Kakeya.Streamlined.axisBox] using hpoint.1
  have hy : |point 1| ≤ 1 := by
    simpa [Kakeya.Streamlined.axisBox] using hpoint.2.1
  have hz : |point 2| ≤ 1 := by
    simpa [Kakeya.Streamlined.axisBox] using hpoint.2.2
  have hsq : ‖point‖ ^ 2 ≤ 3 := by
    rw [hnorm]
    nlinarith [sq_abs (point 0), sq_abs (point 1), sq_abs (point 2),
      abs_nonneg (point 0), abs_nonneg (point 1), abs_nonneg (point 2)]
  nlinarith [sq_nonneg (‖point‖ - 4), norm_nonneg point]

/-- Select the paper-local heavy fiber in a supplied genuine coarse source. -/
theorem pureWZ2_local_projection_heavy_fiber_in_source
    {delta sigma rho : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (C : ENNReal)
    (localGrains : PureWZ2LocalGrainData shading sigma C)
    (anchor : {point : Point3 // point ∈ shading.union})
    (source : Set Point3)
    (hsourceMeasurable : MeasurableSet source)
    (hsourceNonempty : source.Nonempty)
    (hsource : source ⊆
      shading.union ∩ Metric.closedBall (anchor : Point3) (Real.sqrt rho))
    (hrho : 0 < rho)
    (hdeltaRho : delta ≤ rho)
    (hrhoOne : rho ≤ 1)
    (hC : C ≠ ⊤) :
    Nonempty (PureWZ2LocalProjectionHeavyFiberInSource
      (rho := rho) shading C localGrains anchor source) := by
  classical
  let normal := localGrains.planeMap anchor
  let projected := scalarProjection normal source
  let projectionCenter := inner ℝ (anchor : Point3) normal
  let rhoNN : NNReal := ⟨rho, hrho.le⟩
  let bound : ENNReal :=
    (2 * C) * Kakeya.realRpowENN
      (Real.sqrt rho / rho) (1 - sigma)
  have hnormal : ‖normal‖ = 1 := localGrains.planeMap_unit anchor
  have hsqrtOne : Real.sqrt rho ≤ 1 := Real.sqrt_le_one.mpr hrhoOne
  have hrhoSqrt : rho ≤ Real.sqrt rho := by
    have hsquare := Real.sq_sqrt hrho.le
    nlinarith [Real.sqrt_nonneg rho]
  have hprojectedBall : projected ⊆
      Metric.closedBall projectionCenter (Real.sqrt rho) := by
    intro value hvalue
    rcases hvalue with ⟨point, hpoint, rfl⟩
    rw [Metric.mem_closedBall, Real.dist_eq]
    have hinner : |inner ℝ (point - (anchor : Point3)) normal| ≤
        ‖point - (anchor : Point3)‖ * ‖normal‖ :=
      abs_real_inner_le_norm (point - (anchor : Point3)) normal
    have hpointDist : ‖point - (anchor : Point3)‖ ≤ Real.sqrt rho := by
      simpa [dist_eq_norm] using Metric.mem_closedBall.mp (hsource hpoint).2
    have heq : inner ℝ point normal - projectionCenter =
        inner ℝ (point - (anchor : Point3)) normal := by
      simp [projectionCenter, inner_sub_left]
    rw [heq]
    exact hinner.trans (by rw [hnormal, mul_one]; exact hpointDist)
  have hpaperFull := localGrains.local_ad rho hdeltaRho hrhoOne anchor
  have hpaper : PureWZ2PaperADSet1 projected rho (1 - sigma) C := by
    exact hpaperFull.weaken_subset (Set.image_mono hsource)
  have hprojectedBounded : projected ⊆ Set.Icc (-4 : ℝ) 4 := by
    intro value hvalue
    rcases hvalue with ⟨point, hpoint, rfl⟩
    rcases (hsource hpoint).1 with ⟨index, hcarrier⟩
    have hpointNorm : ‖point‖ ≤ 4 :=
      pureWZ2_axisBox_norm_le_four
        (shading.subset_body index hcarrier).2
    have hinner := abs_real_inner_le_norm point normal
    rw [hnormal, mul_one] at hinner
    exact abs_le.mp (hinner.trans hpointNorm)
  have hAD : IsADSet1 projected rho (1 - sigma) (2 * C) :=
    hpaper.toIsADSet1 hprojectedBounded
  have hcoverBound :
      (Metric.externalCoveringNumber rhoNN
          (projected ∩ Metric.closedBall projectionCenter (Real.sqrt rho)) :
        ENNReal) ≤ bound := by
    simpa [rhoNN, bound] using
      hAD.2.2.2.2.2 rho hrho.le le_rfl hrhoOne
        projectionCenter (Real.sqrt rho) hrhoSqrt hsqrtOne
  have hboundTop : bound ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) hC) (by
      simp [Kakeya.realRpowENN, ENNReal.ofReal_ne_top])
  have hcoverTop :
      Metric.externalCoveringNumber rhoNN
          (projected ∩ Metric.closedBall projectionCenter (Real.sqrt rho)) ≠
        ⊤ := by
    have hcast :
        (Metric.externalCoveringNumber rhoNN
            (projected ∩ Metric.closedBall projectionCenter (Real.sqrt rho)) :
          ENNReal) ≠ ⊤ :=
      ne_top_of_le_ne_top hboundTop hcoverBound
    exact_mod_cast hcast
  rcases exists_finset_cover_of_externalCoveringNumber_ne_top hcoverTop with
    ⟨centers, hcentersCover, hcentersCard⟩
  have hcentersCardBound : (centers.card : ENNReal) ≤ bound := by
    have hcardEq : (centers.card : ENNReal) =
        (Metric.externalCoveringNumber rhoNN
          (projected ∩ Metric.closedBall projectionCenter (Real.sqrt rho)) :
          ENNReal) := by
      exact_mod_cast hcentersCard
    rw [hcardEq]
    exact hcoverBound
  have hprojectedNonempty : projected.Nonempty := by
    rcases hsourceNonempty with ⟨point, hpoint⟩
    exact ⟨inner ℝ point normal, point, hpoint, rfl⟩
  have hcentersNonempty : centers.Nonempty := by
    rcases hprojectedNonempty with ⟨value, hvalue⟩
    rcases hcentersCover ⟨hvalue, hprojectedBall hvalue⟩ with
      ⟨center, hcenter, _⟩
    exact ⟨center, hcenter⟩
  let grain (center : ℝ) : Set Point3 := source ∩
    (fun point : Point3 => inner ℝ point normal) ⁻¹'
      Metric.closedBall center rho
  rcases Finset.exists_max_image centers (fun center => volume (grain center))
      hcentersNonempty with ⟨best, hbest, hbestMax⟩
  have hsourceCover : source ⊆ ⋃ center ∈ centers, grain center := by
    intro point hpoint
    have hprojection : inner ℝ point normal ∈
        projected ∩ Metric.closedBall projectionCenter (Real.sqrt rho) :=
      ⟨⟨point, hpoint, rfl⟩, hprojectedBall ⟨point, hpoint, rfl⟩⟩
    rcases hcentersCover hprojection with ⟨center, hcenter, hball⟩
    exact Set.mem_iUnion₂.mpr ⟨center, hcenter, hpoint, by
      exact Metric.mem_closedBall.mpr (by exact_mod_cast hball)⟩
  have hsourceVolume : volume source ≤
      ∑ center ∈ centers, volume (grain center) :=
    (measure_mono hsourceCover).trans
      (measure_biUnion_finset_le centers grain)
  have hsumMax : (∑ center ∈ centers, volume (grain center)) ≤
      (centers.card : ENNReal) * volume (grain best) := by
    calc
      _ ≤ ∑ _center ∈ centers, volume (grain best) :=
        Finset.sum_le_sum fun center hcenter => hbestMax center hcenter
      _ = (centers.card : ENNReal) * volume (grain best) := by simp
  have hmass : volume source ≤ bound * volume (grain best) := by
    exact hsourceVolume.trans (hsumMax.trans (by gcongr))
  have hprojectionContinuous : Continuous
      (fun point : Point3 => inner ℝ point normal) :=
    continuous_id.inner continuous_const
  have hgrainMeasurable : MeasurableSet (grain best) :=
    hsourceMeasurable.inter
      (measurableSet_closedBall.preimage hprojectionContinuous.measurable)
  have hgrainSource : grain best ⊆ source := Set.inter_subset_left
  have hgrainShading : grain best ⊆ shading.union :=
    fun _ hpoint => (hsource (hgrainSource hpoint)).1
  have hgrainBall : grain best ⊆
      Metric.closedBall (anchor : Point3) (Real.sqrt rho) :=
    fun _ hpoint => (hsource (hgrainSource hpoint)).2
  have hgrainFinite : volume (grain best) ≠ ⊤ :=
    ne_top_of_le_ne_top
      (isCompact_closedBall (anchor : Point3) (Real.sqrt rho)).measure_ne_top
      (measure_mono hgrainBall)
  exact ⟨{
    center := best
    grain := grain best
    grain_eq := rfl
    grain_measurable := hgrainMeasurable
    grain_finite := hgrainFinite
    grain_in_source := hgrainSource
    grain_in_shading := hgrainShading
    grain_in_anchor_ball := hgrainBall
    grain_square := by
      intro point hpoint
      have hdist : ‖point - (anchor : Point3)‖ ≤ Real.sqrt rho := by
        simpa [dist_eq_norm] using Metric.mem_closedBall.mp (hgrainBall hpoint)
      constructor
      · have hcoord :=
          (PiLp.norm_apply_le (point - (anchor : Point3)) (0 : Fin 3)).trans
            hdist
        simpa [Real.norm_eq_abs] using hcoord
      · have hcoord :=
          (PiLp.norm_apply_le (point - (anchor : Point3)) (1 : Fin 3)).trans
            hdist
        simpa [Real.norm_eq_abs] using hcoord
    grain_local_strip := by
      intro point hpoint
      simpa [Metric.mem_closedBall, Real.dist_eq] using hpoint.2
    mass_retention := by simpa [bound, normal] using hmass
  }⟩

/-- The WZ1 power cancellation for a paper-shading heavy fiber.  The
paper-to-internal AD conversion costs the factor `2` in the constant. -/
lemma PureWZ2LocalProjectionHeavyFiberInSource.grain_volume_of_source_lower
    {delta sigma rho eta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {C : ENNReal}
    {localGrains : PureWZ2LocalGrainData shading sigma C}
    {anchor : {point : Point3 // point ∈ shading.union}}
    {source : Set Point3}
    (fiber : PureWZ2LocalProjectionHeavyFiberInSource
      (rho := rho) shading C localGrains anchor source)
    (hrho : 0 < rho)
    (hTwoCOne : 1 ≤ 2 * C)
    (hTwoCPower : 2 * C ≤ Kakeya.realRpowENN rho (-eta))
    (hsourceLower :
      Kakeya.realRpowENN rho
          (3 / 2 + sigma / 2 + eta) ≤
        volume source) :
    Kakeya.realRpowENN rho (2 + 2 * eta) ≤
      volume fiber.grain :=
  wz1_lemma23_heavy_fiber_power_threshold
    hrho hTwoCOne hTwoCPower hsourceLower fiber.mass_retention

end Kakeya.Assouad

end
