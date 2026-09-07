import MyLeanRepo.Kakeya.Assouad.WZ1.ADPigeonhole
import MyLeanRepo.Kakeya.Assouad.WZ1.Definitions

/-!
# Actual local-projection heavy fiber for WZ1 Lemma 23

The local AD input controls the full scalar projection
`q ↦ q · V(anchor)` on the actual source
`Y.union ∩ B(anchor, sqrt rho)`.  A finite scale-`rho` cover of that
projection therefore contains one fiber strip carrying the corresponding
fraction of the source volume.

This is deliberately a full normal-projection statement.  A fixed horizontal
slice turns its level into the translated horizontal level
`w - z * V(anchor)₂`; no common three-dimensional horizontal strip is claimed.
-/

namespace Kakeya.Assouad

noncomputable section

open MeasureTheory Metric Set

/-- One genuine heavy local-projection fiber in an actual anchor ball. -/
structure WZ1Lemma23LocalProjectionHeavyFiber
    {delta sigma rho : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (C : ENNReal)
    (localGrains : WZ1LocalGrainData Y sigma C)
    (anchor : Point3) where
  center : ℝ
  grain : Set Point3
  grain_eq :
    grain =
      (Y.union ∩ Metric.closedBall anchor (Real.sqrt rho)) ∩
        (fun point : Point3 =>
          inner ℝ point (localGrains.planeMap anchor)) ⁻¹'
            Metric.closedBall center rho
  grain_measurable : MeasurableSet grain
  grain_finite : volume grain ≠ ⊤
  grain_in_source : grain ⊆ Y.union
  grain_in_anchor_ball :
    grain ⊆ Metric.closedBall anchor (Real.sqrt rho)
  grain_square :
    ∀ point ∈ grain,
      |point 0 - anchor 0| ≤ Real.sqrt rho ∧
        |point 1 - anchor 1| ≤ Real.sqrt rho
  grain_local_strip :
    ∀ point ∈ grain,
      |inner ℝ point (localGrains.planeMap anchor) - center| ≤ rho
  mass_retention :
    volume (Y.union ∩ Metric.closedBall anchor (Real.sqrt rho)) ≤
      (C * Kakeya.realRpowENN
        (Real.sqrt rho / rho) (1 - sigma)) * volume grain

/--
Select a heavy full normal-projection fiber from the actual local AD source.
-/
theorem wz1_lemma23_local_projection_heavy_fiber
    {delta sigma rho : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (C : ENNReal)
    (localGrains : WZ1LocalGrainData Y sigma C)
    (anchor : Point3)
    (hanchor : anchor ∈ Y.union)
    (hrho : 0 < rho)
    (hdelta_rho : delta ≤ rho)
    (hrho_one : rho ≤ 1)
    (hC : C ≠ ⊤) :
    Nonempty
      (WZ1Lemma23LocalProjectionHeavyFiber
        (rho := rho) Y C localGrains anchor) := by
  classical
  let normal := localGrains.planeMap anchor
  let source :=
    Y.union ∩ Metric.closedBall anchor (Real.sqrt rho)
  let projected := scalarProjection normal source
  let projectionCenter := inner ℝ anchor normal
  let rhoNN : NNReal := ⟨rho, hrho.le⟩
  let bound : ENNReal :=
    C * Kakeya.realRpowENN
      (Real.sqrt rho / rho) (1 - sigma)
  have hnormal : ‖normal‖ = 1 := by
    exact localGrains.unit anchor hanchor
  have hsqrt_nonneg : 0 ≤ Real.sqrt rho :=
    Real.sqrt_nonneg rho
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
    have hpoint_dist :
        ‖point - anchor‖ ≤ Real.sqrt rho := by
      simpa [source, dist_eq_norm] using hpoint.2
    have heq :
        inner ℝ point normal - projectionCenter =
          inner ℝ (point - anchor) normal := by
      simp [projectionCenter, inner_sub_left]
    rw [heq]
    exact hinner.trans (by
      rw [hnormal, mul_one]
      exact hpoint_dist)
  have hAD :
      IsADSet1 projected rho (1 - sigma) C := by
    simpa [projected, source, normal] using
      localGrains.local_ad rho hdelta_rho hrho_one anchor hanchor
  have hcover_bound :
      (Metric.externalCoveringNumber rhoNN
          (projected ∩
            Metric.closedBall projectionCenter (Real.sqrt rho)) :
        ENNReal) ≤ bound := by
    simpa [rhoNN, bound] using
      hAD.2.2.2.2.2 rho hrho.le le_rfl hrho_one
        projectionCenter (Real.sqrt rho) hrho_sqrt hsqrt_one
  have hbound_ne_top : bound ≠ ⊤ := by
    exact ENNReal.mul_ne_top hC (by
      simp [Kakeya.realRpowENN, ENNReal.ofReal_ne_top])
  have hcover_ne_top :
      Metric.externalCoveringNumber rhoNN
          (projected ∩
            Metric.closedBall projectionCenter (Real.sqrt rho)) ≠
        ⊤ := by
    have hcast_ne_top :
        (Metric.externalCoveringNumber rhoNN
            (projected ∩
              Metric.closedBall projectionCenter (Real.sqrt rho)) :
          ENNReal) ≠ ⊤ :=
      ne_top_of_le_ne_top hbound_ne_top hcover_bound
    exact_mod_cast hcast_ne_top
  rcases
      exists_finset_cover_of_externalCoveringNumber_ne_top
        hcover_ne_top with
    ⟨centers, hcenters_cover, hcenters_card⟩
  have hcenters_card_bound :
      (centers.card : ENNReal) ≤ bound := by
    have hcard_eq :
        (centers.card : ENNReal) =
          (Metric.externalCoveringNumber rhoNN
            (projected ∩
              Metric.closedBall projectionCenter (Real.sqrt rho)) :
            ENNReal) := by
      exact_mod_cast hcenters_card
    rw [hcard_eq]
    exact hcover_bound
  have hsource_nonempty : source.Nonempty := by
    refine ⟨anchor, hanchor, ?_⟩
    simp [Metric.mem_closedBall, hsqrt_nonneg]
  have hprojected_nonempty : projected.Nonempty := by
    rcases hsource_nonempty with ⟨point, hpoint⟩
    exact ⟨inner ℝ point normal, point, hpoint, rfl⟩
  have hcenters_nonempty : centers.Nonempty := by
    rcases hprojected_nonempty with ⟨value, hvalue⟩
    have hlocalized :
        value ∈ projected ∩
          Metric.closedBall projectionCenter (Real.sqrt rho) :=
      ⟨hvalue, hprojected_ball hvalue⟩
    rcases hcenters_cover hlocalized with ⟨center, hcenter, _⟩
    exact ⟨center, hcenter⟩
  let grain (center : ℝ) : Set Point3 :=
    source ∩
      (fun point : Point3 => inner ℝ point normal) ⁻¹'
        Metric.closedBall center rho
  rcases
      Finset.exists_max_image centers
        (fun center => volume (grain center))
        hcenters_nonempty with
    ⟨best, hbest, hbest_max⟩
  have hsource_cover :
      source ⊆ ⋃ center ∈ centers, grain center := by
    intro point hpoint
    have hprojection :
        inner ℝ point normal ∈
          projected ∩
            Metric.closedBall projectionCenter (Real.sqrt rho) := by
      refine ⟨⟨point, hpoint, rfl⟩, ?_⟩
      exact hprojected_ball ⟨point, hpoint, rfl⟩
    rcases hcenters_cover hprojection with
      ⟨center, hcenter, hball⟩
    have hdist : dist (inner ℝ point normal) center ≤ rho := by
      exact_mod_cast hball
    have hclosed :
        inner ℝ point normal ∈ Metric.closedBall center rho := by
      exact Metric.mem_closedBall.mpr hdist
    exact Set.mem_iUnion₂.mpr
      ⟨center, hcenter, ⟨hpoint, hclosed⟩⟩
  have hsource_volume :
      volume source ≤ ∑ center ∈ centers, volume (grain center) := by
    exact
      (measure_mono hsource_cover).trans
        (measure_biUnion_finset_le centers grain)
  have hsum_max :
      ∑ center ∈ centers, volume (grain center) ≤
        (centers.card : ENNReal) * volume (grain best) := by
    calc
      ∑ center ∈ centers, volume (grain center)
          ≤ ∑ _center ∈ centers, volume (grain best) :=
        Finset.sum_le_sum fun center hcenter =>
          hbest_max center hcenter
      _ = (centers.card : ENNReal) * volume (grain best) := by
        simp
  have hmass :
      volume source ≤ bound * volume (grain best) := by
    calc
      volume source
          ≤ ∑ center ∈ centers, volume (grain center) :=
        hsource_volume
      _ ≤ (centers.card : ENNReal) * volume (grain best) :=
        hsum_max
      _ ≤ bound * volume (grain best) := by
        gcongr
  have hY_measurable : MeasurableSet Y.union := by
    have hunion :
        Y.union = ⋃ index, Y.carrier index := by
      ext point
      simp [Kakeya.Streamlined.Shading.union]
    rw [hunion]
    exact MeasurableSet.iUnion fun index =>
      Y.measurable_carrier index
  have hsource_measurable : MeasurableSet source := by
    exact hY_measurable.inter measurableSet_closedBall
  have hprojection_continuous :
      Continuous (fun point : Point3 => inner ℝ point normal) :=
    continuous_id.inner continuous_const
  have hgrain_measurable : MeasurableSet (grain best) := by
    exact hsource_measurable.inter
      (measurableSet_closedBall.preimage
        hprojection_continuous.measurable)
  have hgrain_in_source : grain best ⊆ Y.union := by
    intro point hpoint
    exact hpoint.1.1
  have hgrain_in_anchor_ball :
      grain best ⊆ Metric.closedBall anchor (Real.sqrt rho) := by
    intro point hpoint
    exact hpoint.1.2
  have hgrain_finite : volume (grain best) ≠ ⊤ := by
    exact ne_top_of_le_ne_top
      (isCompact_closedBall anchor (Real.sqrt rho)).measure_ne_top
      (measure_mono hgrain_in_anchor_ball)
  let output :
      WZ1Lemma23LocalProjectionHeavyFiber
        (rho := rho) Y C localGrains anchor :=
    { center := best
      grain := grain best
      grain_eq := rfl
      grain_measurable := hgrain_measurable
      grain_finite := hgrain_finite
      grain_in_source := hgrain_in_source
      grain_in_anchor_ball := hgrain_in_anchor_ball
      grain_square := by
        intro point hpoint
        have hball := hgrain_in_anchor_ball hpoint
        have hdist :
            ‖point - anchor‖ ≤ Real.sqrt rho := by
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
        have hball := hpoint.2
        simpa [Metric.mem_closedBall, Real.dist_eq] using hball
      mass_retention := by
        simpa [source, bound, normal] using hmass }
  exact ⟨output⟩

/--
On a fixed horizontal slice, the full normal-projection strip is exactly a
translated horizontal strip.  The center depends on the slice height.
-/
lemma WZ1Lemma23LocalProjectionHeavyFiber.horizontal_strip
    {delta sigma rho : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C : ENNReal}
    {localGrains : WZ1LocalGrainData Y sigma C}
    {anchor : Point3}
    (fiber :
      WZ1Lemma23LocalProjectionHeavyFiber
        (rho := rho) Y C localGrains anchor)
    {point : Point3}
    (hpoint : point ∈ fiber.grain)
    (z : ℝ)
    (hheight : point 2 = z) :
    |localGrains.planeMap anchor 0 * point 0 +
          localGrains.planeMap anchor 1 * point 1 -
        (fiber.center -
          z * localGrains.planeMap anchor 2)| ≤ rho := by
  have hstrip := fiber.grain_local_strip point hpoint
  have hinner :
      inner ℝ point (localGrains.planeMap anchor) =
        point 0 * localGrains.planeMap anchor 0 +
          point 1 * localGrains.planeMap anchor 1 +
            point 2 * localGrains.planeMap anchor 2 := by
    rw [PiLp.inner_apply]
    simp [Fin.sum_univ_succ, mul_comm]
    <;> ring
  rw [hinner, hheight] at hstrip
  convert hstrip using 1 <;> ring_nf

end

end Kakeya.Assouad
