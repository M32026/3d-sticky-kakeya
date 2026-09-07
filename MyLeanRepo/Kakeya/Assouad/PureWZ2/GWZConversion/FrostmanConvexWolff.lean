import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12NestedJohnCWATransport
import MyLeanRepo.Kakeya.Streamlined.TubeRefinement
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.TubeVolume
import MyLeanRepo.Kakeya.Streamlined.VolumeHelpers

/-!
# Frostman-to-John-rescaled Convex-Wolff conversion

This module proves the core mathematical conversion from a GWZ-style mass-based
Frostman condition on a fiber of fine tubes to a count-based Convex-Wolff bound
on the John-normalized affine images of those tubes.

Given a fiber of δ-tubes all contained in an A-dilated coarse carrier, and a
Frostman bound
```
containedMass(K) * |A-carrier| ≤ C * mass * |K|
```
for every convex K ⊆ A-carrier, the John-rescaled body family satisfies
```
containedCount(K) ≤ 27 * C * |K| * enmcard
```
for every convex K in normalized space.

The factor 27 comes from John's outer ellipsoid theorem: the outer John
ellipsoid has volume at most 27 times the body volume.

## Main results

* `wz2_unitBall_volume_ge_one`: the 3D unit ball has volume at least 1.
* `gwz_frostman_to_john_rescaled_convex_wolff`: the main conversion theorem.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- The three-dimensional closed unit ball has volume at least 1, because it
contains the axis-aligned cube `[-1/2, 1/2]^3` whose volume is 1. -/
theorem wz2_unitBall_volume_ge_one :
    (1 : ENNReal) ≤ volume (Metric.closedBall (0 : Point3) 1) := by
  have hbox : Kakeya.Streamlined.axisBox 1 1 1 ⊆
      Metric.closedBall (0 : Point3) 1 := by
    intro x hx
    simp only [Kakeya.Streamlined.axisBox, Set.mem_setOf_eq] at hx
    rcases hx with ⟨h0, h1, h2⟩
    have hsq0 : (x 0) ^ 2 ≤ 1 / 4 := by
      have h : |x 0| ≤ 1 / 2 := h0
      have h' : |x 0| ≤ |(1 / 2 : ℝ)| := by simpa using h
      have h'' : (x 0) ^ 2 ≤ ((1 / 2 : ℝ) ^ 2) := sq_le_sq.mpr h'
      linarith
    have hsq1 : (x 1) ^ 2 ≤ 1 / 4 := by
      have h : |x 1| ≤ 1 / 2 := h1
      have h' : |x 1| ≤ |(1 / 2 : ℝ)| := by simpa using h
      have h'' : (x 1) ^ 2 ≤ ((1 / 2 : ℝ) ^ 2) := sq_le_sq.mpr h'
      linarith
    have hsq2 : (x 2) ^ 2 ≤ 1 / 4 := by
      have h : |x 2| ≤ 1 / 2 := h2
      have h' : |x 2| ≤ |(1 / 2 : ℝ)| := by simpa using h
      have h'' : (x 2) ^ 2 ≤ ((1 / 2 : ℝ) ^ 2) := sq_le_sq.mpr h'
      linarith
    have hnorm : ‖x‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2 := by
      have h : ‖x‖ ^ 2 = ∑ i : Fin 3, (x i) ^ 2 := EuclideanSpace.real_norm_sq_eq x
      rw [h]
      simp [Fin.sum_univ_succ]
      ; ring
    have h3 : ‖x‖ ^ 2 ≤ 3 / 4 := by
      rw [hnorm]
      linarith
    have h4 : ‖x‖ ≤ 1 := by
      nlinarith [norm_nonneg x]
    simpa [Metric.mem_closedBall, dist_zero_right] using h4
  have hvol : volume (Kakeya.Streamlined.axisBox 1 1 1) = (1 : ENNReal) := by
    rw [Kakeya.Streamlined.volume_axisBox 1 1 1 (by norm_num) (by norm_num) (by norm_num)]
    ; norm_num
  calc
    (1 : ENNReal) = volume (Kakeya.Streamlined.axisBox 1 1 1) := hvol.symm
    _ ≤ volume (Metric.closedBall (0 : Point3) 1) := measure_mono hbox

/--
Convert a GWZ mass-based Frostman condition on a fiber subfamily to a
count-based Convex-Wolff bound on the John-rescaled body family.

The fiber tubes are all contained in the A-dilated coarse carrier.  The
Frostman condition applies to convex subsets of that carrier.  After John
normalization of the coarse tube, every convex test set in normalized space
is pulled back, intersected with the A-carrier, and fed to Frostman.  The
mass-to-count cancellation uses equal δ-tube volumes, and the geometric loss
is the John factor 27.
-/
theorem gwz_frostman_to_john_rescaled_convex_wolff
    {delta rho A : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hA : 1 ≤ A)
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (parent : Fin coarse.card)
    (sub : Kakeya.Streamlined.TubeSubfamily fine)
    (hfiber : ∀ i : Fin sub.family.card,
      (sub.family.tube i).carrier ⊆
        wz2PaperCenteredDilatedCarrier A (coarse.tube parent))
    (normalization : WZ2PaperAssouadUnitRescalingData (coarse.tube parent))
    (C : ENNReal)
    (hfrost :
      ∀ (K : Set Point3), Convex ℝ K →
        K ⊆ wz2PaperCenteredDilatedCarrier A (coarse.tube parent) →
          sub.family.toBodyFamily.containedMass K *
            volume (wz2PaperCenteredDilatedCarrier A (coarse.tube parent)) ≤
          C * sub.family.toBodyFamily.mass * volume K) :
    WZ2PaperBodyConvexWolffBound
      ({ card := sub.family.card
         body := fun i : Fin sub.family.card =>
           ⟨normalization.map '' (sub.family.tube i).carrier⟩ })
      (27 * C) := by
  let ACarrier : Set Point3 :=
    wz2PaperCenteredDilatedCarrier A (coarse.tube parent)
  let rescaled : Kakeya.Streamlined.BodyFamily :=
    { card := sub.family.card
      body := fun i => ⟨normalization.map '' (sub.family.tube i).carrier⟩ }
  let V : ENNReal := Kakeya.deltaTubeVolume delta

  have hV_pos : 0 < V := by
    have h : ENNReal.ofReal (2 * delta ^ 2) ≤ V :=
      Kakeya.Streamlined.tube_volume_ge_two_delta_sq delta hdelta
    have hpos : 0 < ENNReal.ofReal (2 * delta ^ 2) := by
      apply ENNReal.ofReal_pos.mpr
      positivity
    exact hpos.trans_le h

  have hV_ne_top : V ≠ ⊤ := by
    let canonical : Kakeya.DeltaTube delta :=
      { base := 0
        direction := EuclideanSpace.single (0 : Fin 3) 1
        direction_unit := by simp }
    have h : V = volume canonical.carrier := by
      exact Kakeya.Streamlined.tube_volume_eq canonical canonical
    rw [h]
    exact wz2_paper_ordinary_tube_volume_ne_top canonical hdelta

  have h_all_vol : ∀ i : Fin sub.family.card,
      (sub.family.toBodyFamily.body i).volume = V := by
    intro i
    have h1 : (sub.family.toBodyFamily.body i).volume =
        (sub.family.tube i).volume := by rfl
    rw [h1]
    exact Kakeya.Streamlined.tube_volume_eq (sub.family.tube i)
      { base := 0
        direction := EuclideanSpace.single (0 : Fin 3) 1
        direction_unit := by simp }

  have h_mass : sub.family.toBodyFamily.mass =
      sub.family.toBodyFamily.enncard * V := by
    simp only [Kakeya.Streamlined.BodyFamily.mass,
      Kakeya.Streamlined.BodyFamily.enncard]
    calc
      (∑ i : Fin sub.family.card, (sub.family.toBodyFamily.body i).volume)
        = ∑ i : Fin sub.family.card, V := by
          apply Finset.sum_congr rfl
          intro i _
          exact h_all_vol i
      _ = (sub.family.card : ENNReal) * V := by
        rw [Finset.sum_const]
        ; simp [mul_comm]

  have h_ACarrier_convex : Convex ℝ ACarrier := by
    exact Convex.affine_image (AffineMap.homothety _ _)
      (wz2_paper_ordinary_tube_carrier_convex (coarse.tube parent))

  have h_ACarrier_pos : 0 < volume ACarrier :=
    wz2_paper_centeredDilatedCarrier_volume_pos (coarse.tube parent) hrho
      (by linarith)

  have h_ACarrier_ne_top : volume ACarrier ≠ ⊤ :=
    wz2_paper_centeredDilatedCarrier_volume_ne_top (coarse.tube parent) hrho

  have h_ACarrier_ge_coarse :
      volume (coarse.tube parent).carrier ≤ volume ACarrier := by
    rw [wz2_paper_centeredDilatedCarrier_volume (coarse.tube parent)]
    have hA3 : (1 : ENNReal) ≤ ENNReal.ofReal (|A| ^ 3) := by
      have h2 : 0 ≤ A := by linarith
      have h3 : |A| = A := abs_of_nonneg h2
      have h4 : 1 ≤ A ^ 3 := by
        have h5 : 1 ≤ A := hA
        have h6 : A ^ 3 ≥ 1 ^ 3 := by gcongr
        simpa using h6
      have h7 : 1 ≤ |A| ^ 3 := by
        rw [h3]
        ; exact h4
      have h9 : (1 : ENNReal) ≤ ENNReal.ofReal (|A| ^ 3) := by
        have h10 : (1 : ENNReal) = ENNReal.ofReal (1 : ℝ) := by norm_num
        rw [h10]
        exact (ENNReal.ofReal_le_ofReal_iff (by norm_num)).mpr h7
      exact h9
    have h : ENNReal.ofReal (|A| ^ 3) * volume (coarse.tube parent).carrier ≥
        (1 : ENNReal) * volume (coarse.tube parent).carrier := by
      gcongr
    simpa using h

  let detENN : ENNReal :=
    ENNReal.ofReal
      |LinearMap.det
        (normalization.parent_convex_body.outerJohnEllipsoidMap :
          Point3 →ₗ[ℝ] Point3)|

  have h_ellipsoid_volume :
      volume normalization.parent_convex_body.outerJohnEllipsoid =
        detENN * volume (Metric.closedBall (0 : Point3) 1) :=
    JohnEllipsoid.volume_ellipsoid_eq
      normalization.parent_convex_body.outerJohnEllipsoidCenter
      normalization.parent_convex_body.outerJohnEllipsoidMap

  have h_det_le :
      detENN ≤ (27 : ENNReal) * volume (coarse.tube parent).carrier := by
    have h1 : volume normalization.parent_convex_body.outerJohnEllipsoid ≤
        (27 : ENNReal) * volume (coarse.tube parent).carrier :=
      wz2Paper_outerJohn_volume_le_twentySeven
        normalization.parent_convex_body
    rw [h_ellipsoid_volume] at h1
    have hball : (1 : ENNReal) ≤
        volume (Metric.closedBall (0 : Point3) 1) :=
      wz2_unitBall_volume_ge_one
    have h2 : detENN ≤ detENN *
        volume (Metric.closedBall (0 : Point3) 1) := by
      have h3 : (1 : ENNReal) ≤ volume (Metric.closedBall (0 : Point3) 1) := hball
      have h4 : detENN ≤ detENN * volume (Metric.closedBall (0 : Point3) 1) := by
        calc
          detENN = detENN * 1 := by simp
          _ ≤ detENN * volume (Metric.closedBall (0 : Point3) 1) := by
            exact mul_le_mul_of_nonneg_left h3 (by positivity)
      exact h4
    exact h2.trans h1

  intro K hK_convex
  let K' : Set Point3 := normalization.map.symm '' K
  let K'' : Set Point3 := K' ∩ ACarrier

  have hK'_convex : Convex ℝ K' :=
    Convex.affine_image normalization.map.symm.toAffineMap hK_convex

  have hK''_convex : Convex ℝ K'' :=
    hK'_convex.inter h_ACarrier_convex

  have hK''_subset : K'' ⊆ ACarrier := Set.inter_subset_right

  have h_image_preimage : ∀ (S : Set Point3) (i : Fin sub.family.card),
      normalization.map '' (sub.family.tube i).carrier ⊆ S ↔
        (sub.family.tube i).carrier ⊆ normalization.map.symm '' S := by
    intro S i
    constructor
    · intro h x hx
      exact ⟨normalization.map x, h ⟨x, hx, rfl⟩,
        normalization.map.symm_apply_apply x⟩
    · intro h y hy
      rcases hy with ⟨x, hx, rfl⟩
      have h2 : x ∈ normalization.map.symm '' S := h hx
      rcases h2 with ⟨z, hz, h3⟩
      have h4 : z = normalization.map x := by
        have h5 : normalization.map.symm z = x := h3
        have h6 : normalization.map (normalization.map.symm z) = normalization.map x := by rw [h5]
        simpa using h6
      rw [h4] at hz
      exact hz

  have h_contained_iff : ∀ (i : Fin sub.family.card),
      (rescaled.body i).carrier ⊆ K ↔
        (sub.family.toBodyFamily.body i).carrier ⊆ K'' := by
    intro i
    have h1 : (rescaled.body i).carrier =
        normalization.map '' (sub.family.tube i).carrier := by rfl
    rw [h1]
    have h5 : normalization.map '' (sub.family.tube i).carrier ⊆ K ↔
        (sub.family.tube i).carrier ⊆ K' := h_image_preimage K i
    have h6 : (sub.family.tube i).carrier ⊆ K' ↔
        (sub.family.tube i).carrier ⊆ K'' := by
      constructor
      · intro h
        exact Set.subset_inter h (hfiber i)
      · intro h
        exact h.trans Set.inter_subset_left
    exact h5.trans h6

  have h_indices_eq :
      rescaled.containedIndices K =
        sub.family.toBodyFamily.containedIndices K'' := by
    ext i
    have h_iff : (rescaled.body i).carrier ⊆ K ↔
        i ∈ sub.family.toBodyFamily.containedIndices K'' := by
      have h_a : (rescaled.body i).carrier ⊆ K ↔
          (sub.family.toBodyFamily.body i).carrier ⊆ K'' := h_contained_iff i
      have h_b : (sub.family.toBodyFamily.body i).carrier ⊆ K'' ↔
          i ∈ sub.family.toBodyFamily.containedIndices K'' := by
        exact Kakeya.Streamlined.BodyFamily.mem_containedIndices_iff.symm
      exact h_a.trans h_b
    simp only [Kakeya.Streamlined.BodyFamily.mem_containedIndices_iff]
    exact h_iff

  have h_count_eq :
      rescaled.containedCount K =
        sub.family.toBodyFamily.containedCount K'' := by
    have h3 : (rescaled.containedIndices K).card =
        (sub.family.toBodyFamily.containedIndices K'').card :=
      h_indices_eq ▸ rfl
    have h6 : ((rescaled.containedIndices K).card : ENNReal) =
        ((sub.family.toBodyFamily.containedIndices K'').card : ENNReal) :=
      congr_arg (fun n : Nat => (n : ENNReal)) h3
    have h4 : rescaled.containedCount K = ((rescaled.containedIndices K).card : ENNReal) := by
      rfl
    have h5 : sub.family.toBodyFamily.containedCount K'' = ((sub.family.toBodyFamily.containedIndices K'').card : ENNReal) := by
      rfl
    rw [h4, h5]
    exact h6

  have h_contained_mass :
      sub.family.toBodyFamily.containedMass K'' =
        sub.family.toBodyFamily.containedCount K'' * V := by
    simp only [Kakeya.Streamlined.BodyFamily.containedMass,
      Kakeya.Streamlined.BodyFamily.containedCount]
    have h : (∑ i ∈ sub.family.toBodyFamily.containedIndices K'',
          (sub.family.toBodyFamily.body i).volume) =
        ∑ i ∈ sub.family.toBodyFamily.containedIndices K'', V := by
      apply Finset.sum_congr rfl
      intro i _
      exact h_all_vol i
    rw [h]
    rw [Finset.sum_const]
    ; simp

  have h_frost_count :
      sub.family.toBodyFamily.containedCount K'' * volume ACarrier ≤
        C * sub.family.toBodyFamily.enncard * volume K'' := by
    have h := hfrost K'' hK''_convex hK''_subset
    rw [h_contained_mass, h_mass] at h
    set a := sub.family.toBodyFamily.containedCount K'' with ha
    set e := sub.family.toBodyFamily.enncard with he
    set b := volume ACarrier with hb
    set d := volume K'' with hd
    have h_left : (a * V) * b = (a * b) * V := by
      ac_rfl
    have h_right : C * (e * V) * d = (C * e * d) * V := by
      ac_rfl
    rw [h_left, h_right] at h
    have h' : V * (a * b) ≤ V * (C * e * d) := by
      have h1 : (a * b) * V = V * (a * b) := by
        exact mul_comm (a * b) V
      have h2 : (C * e * d) * V = V * (C * e * d) := by
        exact mul_comm (C * e * d) V
      rw [h1, h2] at h
      exact h
    exact (ENNReal.mul_le_mul_iff_right hV_pos.ne' hV_ne_top).mp h'

  have h_volume_K'' :
      volume K'' ≤ volume K' :=
    measure_mono Set.inter_subset_left

  have h_map_symm_linear :
      (normalization.map.symm.linear : Point3 →ₗ[ℝ] Point3) =
      normalization.parent_convex_body.outerJohnEllipsoidMap := by
    rfl
  have h_det_eq :
      ENNReal.ofReal |LinearMap.det (normalization.map.symm.linear : Point3 →ₗ[ℝ] Point3)| =
      detENN := by
    rw [h_map_symm_linear]
    <;> rfl
  have h_volume_K' :
      volume K' = detENN * volume K := by
    rw [wz2PaperAffineEquiv_volume_image_eq normalization.map.symm K, h_det_eq]

  have h_volume_bound :
      volume K'' ≤ (27 : ENNReal) * volume ACarrier * volume K := by
    calc
      volume K'' ≤ volume K' := h_volume_K''
      _ = detENN * volume K := h_volume_K'
      _ ≤ ((27 : ENNReal) * volume (coarse.tube parent).carrier) * volume K := by
          exact mul_le_mul_of_nonneg_right h_det_le (by positivity)
      _ ≤ (27 : ENNReal) * volume ACarrier * volume K := by
          have h : ((27 : ENNReal) * volume (coarse.tube parent).carrier) * volume K ≤
              (27 : ENNReal) * volume ACarrier * volume K := by
            calc
              ((27 : ENNReal) * volume (coarse.tube parent).carrier) * volume K
                = (27 : ENNReal) * (volume (coarse.tube parent).carrier * volume K) := by
                  rw [mul_assoc]
              _ ≤ (27 : ENNReal) * (volume ACarrier * volume K) := by
                  apply mul_le_mul_of_nonneg_left
                  · exact mul_le_mul_of_nonneg_right h_ACarrier_ge_coarse (by positivity)
                  · positivity
              _ = (27 : ENNReal) * volume ACarrier * volume K := by
                  rw [mul_assoc]
          exact h

  have h_enncard_eq :
      rescaled.enncard = sub.family.toBodyFamily.enncard := by
    dsimp only [rescaled, Kakeya.Streamlined.BodyFamily.enncard,
      Kakeya.Streamlined.TubeFamily.toBodyFamily]

  have h_main :
      sub.family.toBodyFamily.containedCount K'' * volume ACarrier ≤
        (27 * C) * volume K * sub.family.toBodyFamily.enncard * volume ACarrier := by
    calc
      sub.family.toBodyFamily.containedCount K'' * volume ACarrier
        ≤ C * sub.family.toBodyFamily.enncard * volume K'' := h_frost_count
      _ ≤ C * sub.family.toBodyFamily.enncard *
            ((27 : ENNReal) * volume ACarrier * volume K) := by
          exact mul_le_mul_of_nonneg_left h_volume_bound (by positivity)
      _ = (27 * C) * volume K * sub.family.toBodyFamily.enncard * volume ACarrier := by
          have h_eq : C * sub.family.toBodyFamily.enncard * ((27 : ENNReal) * volume ACarrier * volume K) =
              (27 * C) * volume K * sub.family.toBodyFamily.enncard * volume ACarrier := by
            ring
          exact h_eq

  have h_main' : volume ACarrier * sub.family.toBodyFamily.containedCount K'' ≤
      volume ACarrier * ((27 * C) * volume K * sub.family.toBodyFamily.enncard) := by
    have hc1 : volume ACarrier * sub.family.toBodyFamily.containedCount K'' =
        sub.family.toBodyFamily.containedCount K'' * volume ACarrier := by
      simp [mul_comm]
    have hc2 : volume ACarrier * ((27 * C) * volume K * sub.family.toBodyFamily.enncard) =
        (27 * C) * volume K * sub.family.toBodyFamily.enncard * volume ACarrier := by
      ring
    rw [hc1, hc2]
    exact h_main
  have h_final :
      sub.family.toBodyFamily.containedCount K'' ≤
        (27 * C) * volume K * sub.family.toBodyFamily.enncard := by
    exact (ENNReal.mul_le_mul_iff_right h_ACarrier_pos.ne' h_ACarrier_ne_top).mp h_main'

  calc
    rescaled.containedCount K
      = sub.family.toBodyFamily.containedCount K'' := h_count_eq
    _ ≤ (27 * C) * volume K * sub.family.toBodyFamily.enncard := h_final
    _ = (27 * C) * volume K * rescaled.enncard := by
      rw [h_enncard_eq]

end Kakeya.Assouad

end
