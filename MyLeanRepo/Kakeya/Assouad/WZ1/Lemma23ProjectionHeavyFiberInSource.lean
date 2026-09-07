import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23LocalProjectionHeavyFiber
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23HeavyFiberThreshold

/-!
# Heavy fibers from an explicit source projection AD certificate

This is the carrier-independent core of the Lemma-23 heavy-fiber selection.
The source, unit normal, and projected AD certificate are explicit inputs; no
plane map on the source carrier is manufactured.
-/

namespace Kakeya.Assouad

noncomputable section

open MeasureTheory Metric Set

/-- One heavy normal-projection fiber inside an explicit source. -/
structure WZ1Lemma23ProjectionHeavyFiberInSource
    (rho sigma : ℝ) (C : ENNReal)
    (normal : Point3) (anchor : Point3) (source : Set Point3) where
  center : ℝ
  grain : Set Point3
  grain_eq :
    grain =
      source ∩
        (fun point : Point3 => inner ℝ point normal) ⁻¹'
          Metric.closedBall center rho
  grain_measurable : MeasurableSet grain
  grain_finite : volume grain ≠ ⊤
  grain_in_source : grain ⊆ source
  grain_in_anchor_ball :
    grain ⊆ Metric.closedBall anchor (Real.sqrt rho)
  grain_square :
    ∀ point ∈ grain,
      |point 0 - anchor 0| ≤ Real.sqrt rho ∧
        |point 1 - anchor 1| ≤ Real.sqrt rho
  grain_local_strip :
    ∀ point ∈ grain,
      |inner ℝ point normal - center| ≤ rho
  mass_retention :
    volume source ≤
      (C * Kakeya.realRpowENN
        (Real.sqrt rho / rho) (1 - sigma)) * volume grain

/-- Select a heavy fiber using only the source's projected AD certificate. -/
theorem wz1_lemma23_projection_heavy_fiber_in_source
    {rho sigma : ℝ}
    (C : ENNReal)
    (normal anchor : Point3)
    (source : Set Point3)
    (hnormal : ‖normal‖ = 1)
    (hsourceMeasurable : MeasurableSet source)
    (hsourceNonempty : source.Nonempty)
    (hsourceBall :
      source ⊆ Metric.closedBall anchor (Real.sqrt rho))
    (hAD :
      IsADSet1
        (scalarProjection normal source) rho (1 - sigma) C)
    (hrho : 0 < rho)
    (hrho_one : rho ≤ 1)
    (hC : C ≠ ⊤) :
    Nonempty
      (WZ1Lemma23ProjectionHeavyFiberInSource
        rho sigma C normal anchor source) := by
  classical
  let projected := scalarProjection normal source
  let projectionCenter := inner ℝ anchor normal
  let rhoNN : NNReal := ⟨rho, hrho.le⟩
  let bound : ENNReal :=
    C * Kakeya.realRpowENN
      (Real.sqrt rho / rho) (1 - sigma)
  have hsqrt_one : Real.sqrt rho ≤ 1 :=
    Real.sqrt_le_one.mpr hrho_one
  have hrho_sqrt : rho ≤ Real.sqrt rho := by
    have hsquare := Real.sq_sqrt hrho.le
    nlinarith [Real.sqrt_nonneg rho]
  have hprojected_ball :
      projected ⊆
        Metric.closedBall projectionCenter (Real.sqrt rho) := by
    intro value hvalue
    rcases hvalue with ⟨point, hpoint, rfl⟩
    rw [Metric.mem_closedBall, Real.dist_eq]
    have hinner :
        |inner ℝ (point - anchor) normal| ≤
          ‖point - anchor‖ * ‖normal‖ :=
      abs_real_inner_le_norm (point - anchor) normal
    have hpointDist :
        ‖point - anchor‖ ≤ Real.sqrt rho := by
      simpa [dist_eq_norm] using
        (Metric.mem_closedBall.mp (hsourceBall hpoint))
    have heq :
        inner ℝ point normal - projectionCenter =
          inner ℝ (point - anchor) normal := by
      simp [projectionCenter, inner_sub_left]
    rw [heq]
    exact hinner.trans (by
      rw [hnormal, mul_one]
      exact hpointDist)
  have hcoverBound :
      (Metric.externalCoveringNumber rhoNN
          (projected ∩
            Metric.closedBall projectionCenter (Real.sqrt rho)) :
        ENNReal) ≤ bound := by
    simpa [rhoNN, bound, projected] using
      hAD.2.2.2.2.2 rho hrho.le le_rfl hrho_one
        projectionCenter (Real.sqrt rho) hrho_sqrt hsqrt_one
  have hboundTop : bound ≠ ⊤ :=
    ENNReal.mul_ne_top hC (by
      simp [Kakeya.realRpowENN, ENNReal.ofReal_ne_top])
  have hcoverTop :
      Metric.externalCoveringNumber rhoNN
          (projected ∩
            Metric.closedBall projectionCenter (Real.sqrt rho)) ≠
        ⊤ := by
    have hcastTop :
        (Metric.externalCoveringNumber rhoNN
            (projected ∩
              Metric.closedBall projectionCenter (Real.sqrt rho)) :
          ENNReal) ≠ ⊤ :=
      ne_top_of_le_ne_top hboundTop hcoverBound
    exact_mod_cast hcastTop
  rcases
      exists_finset_cover_of_externalCoveringNumber_ne_top
        hcoverTop with
    ⟨centers, hcentersCover, hcentersCard⟩
  have hcentersCardBound : (centers.card : ENNReal) ≤ bound := by
    have hcardEq :
        (centers.card : ENNReal) =
          (Metric.externalCoveringNumber rhoNN
            (projected ∩
              Metric.closedBall projectionCenter (Real.sqrt rho)) :
            ENNReal) := by
      exact_mod_cast hcentersCard
    rw [hcardEq]
    exact hcoverBound
  have hprojectedNonempty : projected.Nonempty := by
    rcases hsourceNonempty with ⟨point, hpoint⟩
    exact ⟨inner ℝ point normal, point, hpoint, rfl⟩
  have hcentersNonempty : centers.Nonempty := by
    rcases hprojectedNonempty with ⟨value, hvalue⟩
    have hlocalized :
        value ∈ projected ∩
          Metric.closedBall projectionCenter (Real.sqrt rho) :=
      ⟨hvalue, hprojected_ball hvalue⟩
    rcases hcentersCover hlocalized with
      ⟨center, hcenter, _⟩
    exact ⟨center, hcenter⟩
  let grain (center : ℝ) : Set Point3 :=
    source ∩
      (fun point : Point3 => inner ℝ point normal) ⁻¹'
        Metric.closedBall center rho
  rcases
      Finset.exists_max_image centers
        (fun center => volume (grain center))
        hcentersNonempty with
    ⟨best, hbest, hbestMax⟩
  have hsourceCover :
      source ⊆ ⋃ center ∈ centers, grain center := by
    intro point hpoint
    have hprojection :
        inner ℝ point normal ∈
          projected ∩
            Metric.closedBall projectionCenter (Real.sqrt rho) :=
      ⟨⟨point, hpoint, rfl⟩,
        hprojected_ball ⟨point, hpoint, rfl⟩⟩
    rcases hcentersCover hprojection with
      ⟨center, hcenter, hball⟩
    have hdist : dist (inner ℝ point normal) center ≤ rho := by
      exact_mod_cast hball
    exact Set.mem_iUnion₂.mpr
      ⟨center, hcenter,
        ⟨hpoint, Metric.mem_closedBall.mpr hdist⟩⟩
  have hsourceVolume :
      volume source ≤ ∑ center ∈ centers, volume (grain center) :=
    (measure_mono hsourceCover).trans
      (measure_biUnion_finset_le centers grain)
  have hsumMax :
      ∑ center ∈ centers, volume (grain center) ≤
        (centers.card : ENNReal) * volume (grain best) := by
    calc
      ∑ center ∈ centers, volume (grain center)
          ≤ ∑ _center ∈ centers, volume (grain best) :=
        Finset.sum_le_sum fun center hcenter =>
          hbestMax center hcenter
      _ = (centers.card : ENNReal) * volume (grain best) := by
        simp
  have hmass :
      volume source ≤ bound * volume (grain best) := by
    calc
      volume source
          ≤ ∑ center ∈ centers, volume (grain center) :=
        hsourceVolume
      _ ≤ (centers.card : ENNReal) * volume (grain best) :=
        hsumMax
      _ ≤ bound * volume (grain best) := by gcongr
  have hprojectionContinuous :
      Continuous (fun point : Point3 => inner ℝ point normal) :=
    continuous_id.inner continuous_const
  have hgrainMeasurable : MeasurableSet (grain best) :=
    hsourceMeasurable.inter
      (measurableSet_closedBall.preimage
        hprojectionContinuous.measurable)
  have hgrainSource : grain best ⊆ source := Set.inter_subset_left
  have hgrainBall :
      grain best ⊆ Metric.closedBall anchor (Real.sqrt rho) :=
    hgrainSource.trans hsourceBall
  have hgrainFinite : volume (grain best) ≠ ⊤ :=
    ne_top_of_le_ne_top
      (isCompact_closedBall anchor (Real.sqrt rho)).measure_ne_top
      (measure_mono hgrainBall)
  exact
    ⟨{ center := best
       grain := grain best
       grain_eq := rfl
       grain_measurable := hgrainMeasurable
       grain_finite := hgrainFinite
       grain_in_source := hgrainSource
       grain_in_anchor_ball := hgrainBall
       grain_square := by
         intro point hpoint
         have hball := hgrainBall hpoint
         have hdist : ‖point - anchor‖ ≤ Real.sqrt rho := by
           simpa [dist_eq_norm] using
             (Metric.mem_closedBall.mp hball)
         constructor
         · have hcoord :=
             PiLp.norm_apply_le (point - anchor) (0 : Fin 3)
           simpa [Real.norm_eq_abs] using hcoord.trans hdist
         · have hcoord :=
             PiLp.norm_apply_le (point - anchor) (1 : Fin 3)
           simpa [Real.norm_eq_abs] using hcoord.trans hdist
       grain_local_strip := by
         intro point hpoint
         simpa [Metric.mem_closedBall, Real.dist_eq] using hpoint.2
       mass_retention := by
         simpa [bound] using hmass }⟩

/-- The standard Lemma-23 power cancellation for an explicit-normal fiber. -/
lemma WZ1Lemma23ProjectionHeavyFiberInSource.grain_volume_of_source_lower
    {rho sigma eta : ℝ}
    {C : ENNReal}
    {normal anchor : Point3}
    {source : Set Point3}
    (fiber :
      WZ1Lemma23ProjectionHeavyFiberInSource
        rho sigma C normal anchor source)
    (hrho : 0 < rho)
    (hCOne : 1 ≤ C)
    (hCPower : C ≤ Kakeya.realRpowENN rho (-eta))
    (hsourceLower :
      Kakeya.realRpowENN rho
          (3 / 2 + sigma / 2 + eta) ≤
        volume source) :
    Kakeya.realRpowENN rho (2 + 2 * eta) ≤
      volume fiber.grain :=
  wz1_lemma23_heavy_fiber_power_threshold
    hrho hCOne hCPower hsourceLower fiber.mass_retention

end

end Kakeya.Assouad
