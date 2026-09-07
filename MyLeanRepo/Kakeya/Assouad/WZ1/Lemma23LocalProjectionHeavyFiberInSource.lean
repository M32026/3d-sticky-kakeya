import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23LocalProjectionHeavyFiber

/-!
# Heavy local-projection fibers inside an actual coarse source

The complete local-grain producer first selects a genuine coarse source, such
as the intersection with one actual `sqrt rho` cube.  The local AD certificate
is stated on the larger anchor ball.  Since `IsADSet1` is monotone, the same
finite-cover pigeonhole applies inside any measurable nonempty source subset
of that ball.

This module keeps that source explicit.  It prevents a heavy fiber selected
from the whole anchor ball from being reused as though it belonged to a
previously selected coarse cube.
-/

namespace Kakeya.Assouad

noncomputable section

open MeasureTheory Metric Set

/-- One heavy full normal-projection fiber inside an explicit actual source. -/
structure WZ1Lemma23LocalProjectionHeavyFiberInSource
    {delta sigma rho : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (C : ENNReal)
    (localGrains : WZ1LocalGrainData Y sigma C)
    (anchor : Point3)
    (source : Set Point3) where
  center : ℝ
  grain : Set Point3
  grain_eq :
    grain =
      source ∩
        (fun point : Point3 =>
          inner ℝ point (localGrains.planeMap anchor)) ⁻¹'
            Metric.closedBall center rho
  grain_measurable : MeasurableSet grain
  grain_finite : volume grain ≠ ⊤
  grain_in_source : grain ⊆ source
  grain_in_shading : grain ⊆ Y.union
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
    volume source ≤
      (C * Kakeya.realRpowENN
        (Real.sqrt rho / rho) (1 - sigma)) * volume grain

/--
Select the heavy full normal-projection fiber inside one supplied actual
coarse source.  The source must retain its literal subset relation to the
shading and anchor ball.
-/
theorem wz1_lemma23_local_projection_heavy_fiber_in_source
    {delta sigma rho : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (C : ENNReal)
    (localGrains : WZ1LocalGrainData Y sigma C)
    (anchor : Point3)
    (source : Set Point3)
    (hanchor : anchor ∈ Y.union)
    (hsourceMeasurable : MeasurableSet source)
    (hsourceNonempty : source.Nonempty)
    (hsource :
      source ⊆
        Y.union ∩ Metric.closedBall anchor (Real.sqrt rho))
    (hrho : 0 < rho)
    (hdelta_rho : delta ≤ rho)
    (hrho_one : rho ≤ 1)
    (hC : C ≠ ⊤) :
    Nonempty
      (WZ1Lemma23LocalProjectionHeavyFiberInSource
        (rho := rho) Y C localGrains anchor source) := by
  classical
  let normal := localGrains.planeMap anchor
  let projected := scalarProjection normal source
  let projectionCenter := inner ℝ anchor normal
  let rhoNN : NNReal := ⟨rho, hrho.le⟩
  let bound : ENNReal :=
    C * Kakeya.realRpowENN
      (Real.sqrt rho / rho) (1 - sigma)
  have hnormal : ‖normal‖ = 1 :=
    localGrains.unit anchor hanchor
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
    have hpointBall := (hsource hpoint).2
    rw [Metric.mem_closedBall, Real.dist_eq]
    have hinner :
        |inner ℝ (point - anchor) normal| ≤
          ‖point - anchor‖ * ‖normal‖ :=
      abs_real_inner_le_norm (point - anchor) normal
    have hpoint_dist :
        ‖point - anchor‖ ≤ Real.sqrt rho := by
      simpa [dist_eq_norm] using
        (Metric.mem_closedBall.mp hpointBall)
    have heq :
        inner ℝ point normal - projectionCenter =
          inner ℝ (point - anchor) normal := by
      simp [projectionCenter, inner_sub_left]
    rw [heq]
    exact hinner.trans (by
      rw [hnormal, mul_one]
      exact hpoint_dist)
  have hADFull :
      IsADSet1
        (scalarProjection normal
          (Y.union ∩
            Metric.closedBall anchor (Real.sqrt rho)))
        rho (1 - sigma) C := by
    simpa [normal] using
      localGrains.local_ad rho hdelta_rho hrho_one anchor hanchor
  have hprojected_sub :
      projected ⊆
        scalarProjection normal
          (Y.union ∩
            Metric.closedBall anchor (Real.sqrt rho)) :=
    Set.image_mono hsource
  have hAD : IsADSet1 projected rho (1 - sigma) C :=
    hADFull.mono hprojected_sub
  have hcover_bound :
      (Metric.externalCoveringNumber rhoNN
          (projected ∩
            Metric.closedBall projectionCenter (Real.sqrt rho)) :
        ENNReal) ≤ bound := by
    simpa [rhoNN, bound] using
      hAD.2.2.2.2.2 rho hrho.le le_rfl hrho_one
        projectionCenter (Real.sqrt rho) hrho_sqrt hsqrt_one
  have hbound_ne_top : bound ≠ ⊤ :=
    ENNReal.mul_ne_top hC (by
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
  have hprojected_nonempty : projected.Nonempty := by
    rcases hsourceNonempty with ⟨point, hpoint⟩
    exact ⟨inner ℝ point normal, point, hpoint, rfl⟩
  have hcenters_nonempty : centers.Nonempty := by
    rcases hprojected_nonempty with ⟨value, hvalue⟩
    have hlocalized :
        value ∈ projected ∩
          Metric.closedBall projectionCenter (Real.sqrt rho) :=
      ⟨hvalue, hprojected_ball hvalue⟩
    rcases hcenters_cover hlocalized with
      ⟨center, hcenter, _⟩
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
      exact
        ⟨⟨point, hpoint, rfl⟩,
          hprojected_ball ⟨point, hpoint, rfl⟩⟩
    rcases hcenters_cover hprojection with
      ⟨center, hcenter, hball⟩
    have hdist : dist (inner ℝ point normal) center ≤ rho := by
      exact_mod_cast hball
    have hclosed :
        inner ℝ point normal ∈ Metric.closedBall center rho :=
      Metric.mem_closedBall.mpr hdist
    exact Set.mem_iUnion₂.mpr
      ⟨center, hcenter, ⟨hpoint, hclosed⟩⟩
  have hsource_volume :
      volume source ≤ ∑ center ∈ centers, volume (grain center) :=
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
  have hprojection_continuous :
      Continuous (fun point : Point3 => inner ℝ point normal) :=
    continuous_id.inner continuous_const
  have hgrain_measurable : MeasurableSet (grain best) :=
    hsourceMeasurable.inter
      (measurableSet_closedBall.preimage
        hprojection_continuous.measurable)
  have hgrain_in_source : grain best ⊆ source :=
    Set.inter_subset_left
  have hgrain_in_shading : grain best ⊆ Y.union := by
    intro point hpoint
    exact (hsource (hgrain_in_source hpoint)).1
  have hgrain_in_anchor_ball :
      grain best ⊆ Metric.closedBall anchor (Real.sqrt rho) := by
    intro point hpoint
    exact (hsource (hgrain_in_source hpoint)).2
  have hgrain_finite : volume (grain best) ≠ ⊤ :=
    ne_top_of_le_ne_top
      (isCompact_closedBall anchor (Real.sqrt rho)).measure_ne_top
      (measure_mono hgrain_in_anchor_ball)
  let output :
      WZ1Lemma23LocalProjectionHeavyFiberInSource
        (rho := rho) Y C localGrains anchor source :=
    { center := best
      grain := grain best
      grain_eq := rfl
      grain_measurable := hgrain_measurable
      grain_finite := hgrain_finite
      grain_in_source := hgrain_in_source
      grain_in_shading := hgrain_in_shading
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
        simpa [bound, normal] using hmass }
  exact ⟨output⟩

/-- Fixed-height translation for a heavy fiber in an explicit source. -/
lemma WZ1Lemma23LocalProjectionHeavyFiberInSource.horizontal_strip
    {delta sigma rho : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {C : ENNReal}
    {localGrains : WZ1LocalGrainData Y sigma C}
    {anchor : Point3}
    {source : Set Point3}
    (fiber :
      WZ1Lemma23LocalProjectionHeavyFiberInSource
        (rho := rho) Y C localGrains anchor source)
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
