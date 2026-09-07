module

/-
  Lemma 4: Apply LegacyRound.snap_sset_transfer to all fibers uniformly.

  Given per-point flat tube families (v0≠0, |slope|≤1), snap each family
  to dyadic tubes through its point and transfer the S-set property.

  Outputs 7 properties:
  1. Set equality (image definition)
  2. S-set transfer with constant K_snap * C_in
  3. Provenance: dist(original ℓ, DyadicCardToNcover.toAffineLine(U)) ≤ 7δ
  4. Intersection: U.toSet ∩ closedBall(p, 2δ_n) nonempty
  5. Slope bound: |U.slope| ≤ 3/2
  6. Intercept bound: |U.intercept| ≤ 3
  7. Strip bound: -2^n ≤ U.a < 2^n (dyadic strip)

  Uses `LegacyRound.snap_sset_transfer` from SnapTubeSSetTransfer.lean.
  Constant: K_snap = 3721 * K_pack^5 * 58^s.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.LegacyRoundSnapTubeSSetTransfer
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ConstructNiceConfiguration
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicCardToNcover
public import MyLeanRepo.DiscretisedFurstenbergEstimate.HCommonWiring
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

attribute [local instance] Classical.propDecidable

open DirecretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral
open DyadicCardToNcover (toAffineLine)

/-- Apply LegacyRound.snap_sset_transfer to all per-point tube families uniformly.

    Produces raw snapped dyadic tube families with S-set constant
    K_snap * C_in, where K_snap = 3721 * K_pack^5 * 58^s.

    Also outputs provenance, intersection, slope (≤3/2), and intercept (≤3) bounds. -/
lemma snap_transfer_all
    {n : ℕ} {δ s C_in : ℝ}
    (hδ_pos : 0 < δ) (hδ_le_one : δ ≤ 1)
    (hδn_pos : 0 < dyadicDelta n)
    (hδn_leδ : dyadicDelta n ≤ δ)
    (hδ_le2δn : δ ≤ 2 * dyadicDelta n)
    (hs_nonneg : 0 ≤ s) (hC_in_pos : 0 < C_in)
    (P' : Set Plane)
    (F' : ∀ (p : Plane), p ∈ P' → Finset AffineLine)
    (hF'_sset : ∀ p hp, IsDeltaSSet δ s C_in (F' p hp : Set AffineLine))
    (hF'_v0 : ∀ p hp, ∀ ℓ ∈ F' p hp, (LemmaE.getDirV ℓ) 0 ≠ 0)
    (hF'_slope : ∀ p hp, ∀ ℓ ∈ F' p hp, |(affineLineSlopeIntercept ℓ).1| ≤ 1)
    (hF'_near : ∀ p hp, ∀ ℓ ∈ F' p hp, p ∈ Metric.cthickening δ ℓ.1)
    (hP'_bdd : P' ⊆ Metric.closedBall 0 1) :
    ∃ (rawTubes : ∀ (p : Plane), p ∈ P' → Finset (DyadicTube n)),
      (∀ p hp, (rawTubes p hp : Set (DyadicTube n)) =
        (fun ℓ => LegacyRound.snapToTubeThroughPoint n ℓ p) '' (F' p hp : Set AffineLine)) ∧
      (∀ p hp, IsDeltaSSet (dyadicDelta n) s
        (3721 * (MainAppendix.affineLine_packing_constant : ℝ)^5 * (58 : ℝ)^s * C_in)
        (rawTubes p hp : Set (DyadicTube n))) ∧
      (∀ p hp (U : DyadicTube n), U ∈ rawTubes p hp →
        ∃ (ℓ : AffineLine), ℓ ∈ F' p hp ∧
          AffineLine.dist ℓ (toAffineLine U) ≤ 7 * δ) ∧
      (∀ p hp (U : DyadicTube n), U ∈ rawTubes p hp →
        (U.toSet ∩ Metric.closedBall p (2 * dyadicDelta n)).Nonempty) ∧
      (∀ p hp (U : DyadicTube n), U ∈ rawTubes p hp → |U.slope| ≤ 3 / 2) ∧
      (∀ p hp (U : DyadicTube n), U ∈ rawTubes p hp → |U.intercept| ≤ 3) ∧
      (∀ p hp (U : DyadicTube n), U ∈ rawTubes p hp →
        -(2 ^ n : ℤ) ≤ U.a ∧ U.a < (2 ^ n : ℤ)) := by
  let K_snap : ℝ := 3721 * (MainAppendix.affineLine_packing_constant : ℝ)^5 * (58 : ℝ)^s
  have hK_snap_pos : 0 < K_snap := by
    have h_pack_pos : 0 < (MainAppendix.affineLine_packing_constant : ℝ) := by
      exact_mod_cast MainAppendix.affineLine_packing_constant_pos
    positivity
  let rawTubes : ∀ (p : Plane), p ∈ P' → Finset (DyadicTube n) := fun p hp =>
    (F' p hp).image (fun ℓ => LegacyRound.snapToTubeThroughPoint n ℓ p)
  have h_image_eq : ∀ (p : Plane) (hp : p ∈ P'),
      (rawTubes p hp : Set (DyadicTube n)) =
        (fun ℓ => LegacyRound.snapToTubeThroughPoint n ℓ p) '' (F' p hp : Set AffineLine) := by
    intro p hp
    simp [rawTubes]
    <;> rfl
  have h_sset : ∀ (p : Plane) (hp : p ∈ P'),
      IsDeltaSSet (dyadicDelta n) s (K_snap * C_in)
        (rawTubes p hp : Set (DyadicTube n)) := by
    intro p hp
    have hp_ball : p ∈ Metric.closedBall 0 1 := hP'_bdd hp
    have h_p0 : |p 0| ≤ 1 := by
      have h : |p 0| ≤ ‖p‖ := by exact TubesAndSlopes.coord_abs_le_norm p 0
      have h2 : ‖p‖ ≤ 1 := by simpa [Metric.mem_closedBall] using hp_ball
      linarith
    have h_p1 : |p 1| ≤ 1 := by
      have h : |p 1| ≤ ‖p‖ := by exact TubesAndSlopes.coord_abs_le_norm p 1
      have h2 : ‖p‖ ≤ 1 := by simpa [Metric.mem_closedBall] using hp_ball
      linarith
    have h_main := LegacyRound.snap_sset_transfer
      (hδ_pos := hδ_pos) (hδ_le_one := hδ_le_one)
      (hδn_pos := hδn_pos) (hδn_eq := rfl)
      (hδn_leδ := hδn_leδ) (hδ_le2δn := hδ_le2δn)
      (hs_nonneg := hs_nonneg) (hC_pos := hC_in_pos)
      (hS := hF'_sset p hp)
      (p := p) (h_p0 := h_p0) (h_p1 := h_p1)
      (h_v0 := hF'_v0 p hp)
      (h_slope := hF'_slope p hp)
      (h_near := hF'_near p hp)
    have h_set_eq : (rawTubes p hp : Set (DyadicTube n)) =
        (fun ℓ => LegacyRound.snapToTubeThroughPoint n ℓ p) '' (F' p hp : Set AffineLine) :=
      h_image_eq p hp
    rw [h_set_eq]
    exact h_main

  -- Per-tube geometric bounds
  have h_geom : ∀ (p : Plane) (hp : p ∈ P') (ℓ : AffineLine), ℓ ∈ F' p hp →
      let T := LegacyRound.snapToTubeThroughPoint n ℓ p
      (AffineLine.dist ℓ (toAffineLine T) ≤ 7 * δ) ∧
      (T.toSet ∩ Metric.closedBall p (2 * dyadicDelta n)).Nonempty ∧
      |T.slope| ≤ 3 / 2 ∧ |T.intercept| ≤ 3 ∧
      (-(2 ^ n : ℤ) ≤ T.a ∧ T.a < (2 ^ n : ℤ)) := by
    intro p hp ℓ hℓ
    let T := LegacyRound.snapToTubeThroughPoint n ℓ p
    have hp_ball : p ∈ Metric.closedBall 0 1 := hP'_bdd hp
    have h_p0 : |p 0| ≤ 1 := by
      have h : |p 0| ≤ ‖p‖ := by exact TubesAndSlopes.coord_abs_le_norm p 0
      have h2 : ‖p‖ ≤ 1 := by simpa [Metric.mem_closedBall] using hp_ball
      linarith
    have h_p1 : |p 1| ≤ 1 := by
      have h : |p 1| ≤ ‖p‖ := by exact TubesAndSlopes.coord_abs_le_norm p 1
      have h2 : ‖p‖ ≤ 1 := by simpa [Metric.mem_closedBall] using hp_ball
      linarith
    have hv0 : (LemmaE.getDirV ℓ) 0 ≠ 0 := hF'_v0 p hp ℓ hℓ
    have hslope : |(affineLineSlopeIntercept ℓ).1| ≤ 1 := hF'_slope p hp ℓ hℓ
    have hnear : p ∈ Metric.cthickening δ ℓ.1 := hF'_near p hp ℓ hℓ

    -- 1. Provenance
    have h_prov : AffineLine.dist ℓ (toAffineLine T) ≤ 7 * δ :=
      LegacyRound.snap_movement_bound hδ_pos hδ_le_one hδn_leδ ℓ p hv0 hslope h_p0 h_p1 hnear

    -- 2. Intersection
    have h_p_in_T : p ∈ T.toSet := LegacyRound.snapToTubeThroughPoint_incidence
    have h_p_in_ball : p ∈ Metric.closedBall p (2 * dyadicDelta n) := by
      simp [Metric.mem_closedBall] <;> linarith [dyadicDelta_pos n]
    have h_intersect : (T.toSet ∩ Metric.closedBall p (2 * dyadicDelta n)).Nonempty :=
      ⟨p, h_p_in_T, h_p_in_ball⟩

    -- 3. Slope bound ≤ 3/2
    let m := (affineLineSlopeIntercept ℓ).1
    let δ_n := dyadicDelta n
    have h1_Ta : T.a = min (roundInt (m / δ_n)) ((2 ^ n : ℤ) - 1) := by
      simp [T, LegacyRound.snapToTubeThroughPoint] <;> rfl
    have h_slope_bound : |T.slope| ≤ 3 / 2 := by
      exact LegacyRound.snap_slope_bound_3_2 hslope T h1_Ta

    -- 4. Intercept bound ≤ 3
    have h_intercept_bound : |T.intercept| ≤ 3 :=
      LegacyRound.snap_intercept_bound hδn_leδ ℓ p hv0 hslope h_p0 h_p1

    have h_strip_bound : -(2 ^ n : ℤ) ≤ T.a ∧ T.a < (2 ^ n : ℤ) :=
      LegacyRound.snapToTubeThroughPoint_a_strip hslope
    exact ⟨h_prov, h_intersect, h_slope_bound, h_intercept_bound, h_strip_bound⟩

  -- Lift per-tube bounds to rawTubes membership
  have h_provenance : ∀ p hp (U : DyadicTube n), U ∈ rawTubes p hp →
      ∃ (ℓ : AffineLine), ℓ ∈ F' p hp ∧ AffineLine.dist ℓ (toAffineLine U) ≤ 7 * δ := by
    intro p hp U hU
    have h_in_image : U ∈ (F' p hp).image (fun ℓ => LegacyRound.snapToTubeThroughPoint n ℓ p) := by
      simpa [rawTubes] using hU
    rcases Finset.mem_image.mp h_in_image with ⟨ℓ, hℓ, rfl⟩
    exact ⟨ℓ, hℓ, (h_geom p hp ℓ hℓ).1⟩

  have h_intersect : ∀ p hp (U : DyadicTube n), U ∈ rawTubes p hp →
      (U.toSet ∩ Metric.closedBall p (2 * dyadicDelta n)).Nonempty := by
    intro p hp U hU
    have h_in_image : U ∈ (F' p hp).image (fun ℓ => LegacyRound.snapToTubeThroughPoint n ℓ p) := by
      simpa [rawTubes] using hU
    rcases Finset.mem_image.mp h_in_image with ⟨ℓ, hℓ, rfl⟩
    exact (h_geom p hp ℓ hℓ).2.1

  have h_slope : ∀ p hp (U : DyadicTube n), U ∈ rawTubes p hp → |U.slope| ≤ 3 / 2 := by
    intro p hp U hU
    have h_in_image : U ∈ (F' p hp).image (fun ℓ => LegacyRound.snapToTubeThroughPoint n ℓ p) := by
      simpa [rawTubes] using hU
    rcases Finset.mem_image.mp h_in_image with ⟨ℓ, hℓ, rfl⟩
    exact (h_geom p hp ℓ hℓ).2.2.1

  have h_intercept : ∀ p hp (U : DyadicTube n), U ∈ rawTubes p hp → |U.intercept| ≤ 3 := by
    intro p hp U hU
    have h_in_image : U ∈ (F' p hp).image (fun ℓ => LegacyRound.snapToTubeThroughPoint n ℓ p) := by
      simpa [rawTubes] using hU
    rcases Finset.mem_image.mp h_in_image with ⟨ℓ, hℓ, rfl⟩
    exact (h_geom p hp ℓ hℓ).2.2.2.1

  have h_strip : ∀ p hp (U : DyadicTube n), U ∈ rawTubes p hp →
      -(2 ^ n : ℤ) ≤ U.a ∧ U.a < (2 ^ n : ℤ) := by
    intro p hp U hU
    have h_in_image : U ∈ (F' p hp).image (fun ℓ => LegacyRound.snapToTubeThroughPoint n ℓ p) := by
      simpa [rawTubes] using hU
    rcases Finset.mem_image.mp h_in_image with ⟨ℓ, hℓ, rfl⟩
    exact (h_geom p hp ℓ hℓ).2.2.2.2

  exact ⟨rawTubes, h_image_eq, h_sset, h_provenance, h_intersect, h_slope, h_intercept, h_strip⟩

end
