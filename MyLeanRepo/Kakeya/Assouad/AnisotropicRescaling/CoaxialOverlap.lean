import MyLeanRepo.Kakeya.Assouad.AnisotropicRescaling.TubeEndpointBalls

/-!
# Overlap of separated coaxial tubes

Localize the carrier intersection of ordered coaxial unit tubes near the
earlier segment's endpoint, then compare its volume against the endpoint-ball
lower bound for one whole tube.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

/-- The repository's volume-half essential-distinctness relation is symmetric. -/
lemma essentiallyDistinct_symm
    {rho : ℝ} {T U : Kakeya.DeltaTube rho} :
    T.EssentiallyDistinct U ↔ U.EssentiallyDistinct T := by
  simp [Kakeya.DeltaTube.EssentiallyDistinct,
    Set.inter_comm, max_comm]

/--
If the second coaxial unit segment starts no earlier than the endpoint of the
first, their carrier intersection lies in the radius-`rho` ball about that
endpoint.
-/
lemma coaxial_carrier_intersection_subset_endpoint_ball
    {rho : ℝ} (hrho : 0 ≤ rho)
    (base direction : Point3) (hdir : ‖direction‖ = 1)
    {s t : ℝ} (hsep : s + 1 ≤ t) :
    let T : Kakeya.DeltaTube rho :=
      ⟨base + s • direction, direction, hdir⟩
    let U : Kakeya.DeltaTube rho :=
      ⟨base + t • direction, direction, hdir⟩
    T.carrier ∩ U.carrier ⊆
      Metric.closedBall (base + (s + 1) • direction) rho := by
  dsimp only
  intro point hpoint
  have hcompactT :
      IsCompact
        (Kakeya.unitSegment
          (base + s • direction) direction) := by
    exact isCompact_Icc.image
      (continuous_const.add (continuous_id.smul continuous_const))
  have hcompactU :
      IsCompact
        (Kakeya.unitSegment
          (base + t • direction) direction) := by
    exact isCompact_Icc.image
      (continuous_const.add (continuous_id.smul continuous_const))
  have hT := hpoint.1
  have hU := hpoint.2
  change point ∈ Metric.cthickening rho
    (Kakeya.unitSegment (base + s • direction) direction) at hT
  change point ∈ Metric.cthickening rho
    (Kakeya.unitSegment (base + t • direction) direction) at hU
  rw [hcompactT.cthickening_eq_biUnion_closedBall hrho] at hT
  rw [hcompactU.cthickening_eq_biUnion_closedBall hrho] at hU
  rcases Set.mem_iUnion₂.mp hT with ⟨y, hy_axis, hy_ball⟩
  rcases Set.mem_iUnion₂.mp hU with ⟨z, hz_axis, hz_ball⟩
  rcases hy_axis with ⟨a, ha, rfl⟩
  rcases hz_axis with ⟨b, hb, rfl⟩
  let alpha : ℝ := s + a
  let beta : ℝ := t + b
  have halpha : alpha ≤ s + 1 := by
    dsimp only [alpha]
    linarith [ha.2]
  have hbeta : s + 1 ≤ beta := by
    dsimp only [beta]
    linarith [hb.1]
  have hy_ball' :
      (base + s • direction) + a • direction ∈
        Metric.closedBall point rho := by
    simpa [Metric.mem_closedBall, dist_comm] using hy_ball
  have hz_ball' :
      (base + t • direction) + b • direction ∈
        Metric.closedBall point rho := by
    simpa [Metric.mem_closedBall, dist_comm] using hz_ball
  have hend :
      base + (s + 1) • direction ∈
        Metric.closedBall point rho := by
    by_cases hab : alpha = beta
    · have heq : alpha = s + 1 := by
        linarith
      have hy_eq :
          (base + s • direction) + a • direction =
            base + alpha • direction := by
        dsimp only [alpha]
        rw [add_smul]
        abel
      rw [hy_eq, heq] at hy_ball'
      exact hy_ball'
    · have hab_lt : alpha < beta :=
        lt_of_le_of_ne (halpha.trans hbeta) hab
      let A : ℝ := (beta - (s + 1)) / (beta - alpha)
      let B : ℝ := ((s + 1) - alpha) / (beta - alpha)
      have hden : 0 < beta - alpha := by linarith
      have hA : 0 ≤ A := by
        dsimp only [A]
        positivity
      have hB : 0 ≤ B := by
        dsimp only [B]
        positivity
      have hsum : A + B = 1 := by
        dsimp only [A, B]
        field_simp [hden.ne']
        ring
      have hweighted :
          A * alpha + B * beta = s + 1 := by
        dsimp only [A, B]
        field_simp [hden.ne']
        ring
      have hy_eq :
          (base + s • direction) + a • direction =
            base + alpha • direction := by
        dsimp only [alpha]
        rw [add_smul]
        abel
      have hz_eq :
          (base + t • direction) + b • direction =
            base + beta • direction := by
        dsimp only [beta]
        rw [add_smul]
        abel
      have hcombo :
          A • ((base + s • direction) + a • direction) +
              B • ((base + t • direction) + b • direction) =
            base + (s + 1) • direction := by
        rw [hy_eq, hz_eq]
        calc
          A • (base + alpha • direction) +
                B • (base + beta • direction) =
              (A + B) • base +
                (A * alpha + B * beta) • direction := by
            module
          _ = base + (s + 1) • direction := by
            rw [hsum, hweighted, one_smul]
      rw [← hcombo]
      exact (convex_closedBall point rho)
        hy_ball' hz_ball' hA hB hsum
  simpa [Metric.mem_closedBall, dist_comm] using hend

/--
Ordered separated coaxial tubes satisfy volume-half essential distinctness at
radius at most `1/8`.
-/
lemma coaxial_shifted_ordered_essentiallyDistinct
    {rho : ℝ} (hrho : 0 < rho) (hrho_small : rho ≤ 1 / 8)
    (base direction : Point3) (hdir : ‖direction‖ = 1)
    {s t : ℝ} (hsep : s + 1 ≤ t) :
    let T : Kakeya.DeltaTube rho :=
      ⟨base + s • direction, direction, hdir⟩
    let U : Kakeya.DeltaTube rho :=
      ⟨base + t • direction, direction, hdir⟩
    T.EssentiallyDistinct U := by
  let T : Kakeya.DeltaTube rho :=
    ⟨base + s • direction, direction, hdir⟩
  let U : Kakeya.DeltaTube rho :=
    ⟨base + t • direction, direction, hdir⟩
  let endpoint : Point3 := base + (s + 1) • direction
  have hloc :
      T.carrier ∩ U.carrier ⊆ Metric.closedBall endpoint rho :=
    coaxial_carrier_intersection_subset_endpoint_ball
      hrho.le base direction hdir hsep
  have hinter :
      volume (T.carrier ∩ U.carrier) ≤
        volume (Metric.closedBall endpoint rho) :=
    measure_mono hloc
  have hball_translate :
      volume (Metric.closedBall endpoint rho) =
        volume (Metric.closedBall (0 : Point3) rho) := by
    rw [EuclideanSpace.volume_closedBall_fin_three,
      EuclideanSpace.volume_closedBall_fin_three]
  have htwo_rho : 2 * rho < 1 := by
    linarith
  have hlower :
      2 * volume (Metric.closedBall (0 : Point3) rho) ≤ T.volume :=
    tube_endpoint_balls_volume_lower htwo_rho T
  have hhalf :
      volume (Metric.closedBall (0 : Point3) rho) ≤
        (2 : ENNReal)⁻¹ * T.volume := by
    calc
      volume (Metric.closedBall (0 : Point3) rho) =
          (2 : ENNReal)⁻¹ *
            (2 * volume (Metric.closedBall (0 : Point3) rho)) := by
        rw [← mul_assoc,
          ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
      _ ≤ (2 : ENNReal)⁻¹ * T.volume := by gcongr
  change
    volume (T.carrier ∩ U.carrier) ≤
      (2 : ENNReal)⁻¹ * max T.volume U.volume
  calc
    volume (T.carrier ∩ U.carrier)
        ≤ volume (Metric.closedBall endpoint rho) := hinter
    _ = volume (Metric.closedBall (0 : Point3) rho) := hball_translate
    _ ≤ (2 : ENNReal)⁻¹ * T.volume := hhalf
    _ ≤ (2 : ENNReal)⁻¹ * max T.volume U.volume := by
      gcongr
      exact le_max_left _ _

end Kakeya.Assouad
