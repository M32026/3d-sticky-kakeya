import MyLeanRepo.Kakeya.Assouad.Subunit.HairbrushSelfContainedLeaves
import MyLeanRepo.Kakeya.Assouad.Hairbrush.HomogeneousTwoEndsHelpers
import MyLeanRepo.Kakeya.Assouad.Hairbrush.RadiusPigeonhole
import MyLeanRepo.Kakeya.Assouad.Hairbrush.TubeVolumeLower
import MyLeanRepo.Kakeya.Assouad.Hairbrush.BallVolumeContinuity
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Homogeneous per-hair two-ends refinement

For every hair maximize `r^-zeta` times shaded mass over balls, restrict to
the maximizing ball, and pigeonhole a common dyadic radius.

## Proof route

1. For each tube T, maximize `volume(S ∩ closedBall x r) / r^zeta` over the
   compact domain `closedBall midpoint 3 × [δ, 2]`.
2. The restricted shading is `S ∩ closedBall x_T r_T`.
3. Mass retention follows by comparing with the ball at the tube midpoint.
4. Two-ends follows directly from maximality.
5. Density-radius relation uses slab bound and tube volume lower.
6. Pigeonhole the selected radii using geometric bins of ratio 3/2.
-/

noncomputable section

open MeasureTheory Metric Set Finset Real

namespace Kakeya.Assouad

theorem hairbrush_homogeneous_two_ends_main : HairbrushHomogeneousTwoEndsStatement := by
  intro zeta familyLoss cardExponent hzeta_pos hzeta_lt_one hfl_pos hcard_pos
  rcases radius_log_bound familyLoss hfl_pos with ⟨delta₀, hdelta₀_pos, hdelta₀_le, hlog_bound⟩
  refine ⟨delta₀, hdelta₀_pos, hdelta₀_le, ?_⟩
  intro δ hδ_pos hδ_le H Z hH_nonempty hcard_bound hairDensity hhd_ne_zero hhd_ne_top
    h_lower h_upper
  have hδ_small : δ ≤ 1 / 1000 := by
    calc δ ≤ delta₀ := hδ_le
         _ ≤ 1 / 1000 := hdelta₀_le
  let R : ℝ := 1 / 2 + 2 * δ
  have hR_pos : 0 < R := by positivity
  have hR_le_one : R ≤ 1 := by
    have hR_def : R = 1 / 2 + 2 * δ := by rfl
    rw [hR_def]
    linarith [hδ_small]
  have hR_le_two : R ≤ 2 := by
    have hR_def : R = 1 / 2 + 2 * δ := by rfl
    rw [hR_def]
    linarith [hδ_small]
  have hδ_le_R : δ ≤ R := by
    have hR_def : R = 1 / 2 + 2 * δ := by rfl
    rw [hR_def]
    linarith
  have h_one_minus_zeta_pos : 0 < 1 - zeta := by linarith

  let α : Type _ := {T : Kakeya.DeltaTube δ // T ∈ H}
  haveI hα_fintype : Fintype α := Fintype.ofFinite α
  haveI hα_decEq : DecidableEq α := Classical.decEq α
  haveI h_deltaTube_decEq : DecidableEq (Kakeya.DeltaTube δ) :=
    Classical.decEq (Kakeya.DeltaTube δ)
  have hα_univ_card : (Finset.univ : Finset α).card = H.card := by
    simp [α] <;> rfl

  have h_main : ∀ (i : α), ∃ (xT : Point3) (rT : ℝ),
      δ ≤ rT ∧ rT ≤ 2 ∧
      (volume (Z.carrier i.val ∩ Metric.closedBall xT rT) ≥
        ENNReal.ofReal (Real.rpow (rT / R) zeta) * hairDensity * i.val.volume) ∧
      (∀ (x : Point3) (t : ℝ), δ ≤ t → t ≤ 2 →
        volume (Z.carrier i.val ∩ Metric.closedBall x t) ≤
        ENNReal.ofReal (Real.rpow (t / rT) zeta) *
        volume (Z.carrier i.val ∩ Metric.closedBall xT rT)) ∧
      hairDensity ≤ ENNReal.ofReal (64 * Real.rpow rT (1 - zeta)) := by
    intro i
    let T := i.val
    let hT := i.property
    let S := Z.carrier T
    let midpoint := T.base + (1 / 2 : ℝ) • T.direction
    have hmeas : MeasurableSet S := Z.measurable_carrier hT
    have hS_finite : volume S ≠ ⊤ := by
      have h1 : S ⊆ T.carrier := Z.subset_tube hT
      have h2 : volume T.carrier ≠ ⊤ := by
        have h3 : T.volume = Kakeya.deltaTubeVolume δ := tube_volume_scaling.1 δ T
        rw [Kakeya.DeltaTube.volume] at h3
        rw [h3]
        exact (tube_volume_scaling.2.1 δ hδ_pos (by linarith)).2
      exact ne_top_of_le_ne_top h2 (measure_mono h1)
    have hS_pos : 0 < volume S := by
      have h1 : hairDensity * T.volume ≤ volume S := h_lower T hT
      have h2 : 0 < T.volume := by
        have h3 : T.volume ≥ ENNReal.ofReal (δ^2 / 8) := tube_volume_lower hδ_pos (by linarith) T
        have h4 : 0 < ENNReal.ofReal (δ^2 / 8) := by positivity
        exact h4.trans_le h3
      have h5 : 0 < hairDensity * T.volume := by positivity
      exact h5.trans_le h1
    -- Continuity of volume(S ∩ closedBall x r).toReal using BallVolumeContinuity
    have h_cont_ball : ContinuousOn (fun p : Point3 × ℝ => volume (S ∩ Metric.ball p.1 p.2)) {p | 0 < p.2} :=
      continuousOn_volume_inter_ball hmeas hS_finite
    have h_eq_ball : ∀ (p : Point3 × ℝ), volume (S ∩ Metric.closedBall p.1 p.2) = volume (S ∩ Metric.ball p.1 p.2) :=
      fun p => volume_inter_closedBall_eq_ball hmeas hS_finite p.1 p.2
    have h_cont_closed : ContinuousOn (fun p : Point3 × ℝ => volume (S ∩ Metric.closedBall p.1 p.2)) {p | 0 < p.2} := by
      have h_f : (fun p : Point3 × ℝ => volume (S ∩ Metric.closedBall p.1 p.2)) =
          (fun p => volume (S ∩ Metric.ball p.1 p.2)) := funext h_eq_ball
      rw [h_f]
      exact h_cont_ball
    have hfin_all : ∀ (p : Point3 × ℝ), volume (S ∩ Metric.closedBall p.1 p.2) ≠ ⊤ := by
      intro p
      have h_sub : S ∩ Metric.closedBall p.1 p.2 ⊆ S := by
        intro z hz
        exact hz.1
      exact ne_top_of_le_ne_top hS_finite (measure_mono h_sub)
    have h_toReal_on : ContinuousOn (fun x : ENNReal => x.toReal) {x : ENNReal | x ≠ ⊤} := by
      intro x hx
      exact (ENNReal.continuousAt_toReal hx).continuousWithinAt
    have h_image : ∀ p ∈ ({p : Point3 × ℝ | 0 < p.2} : Set (Point3 × ℝ)),
        volume (S ∩ Metric.closedBall p.1 p.2) ∈ ({x : ENNReal | x ≠ ⊤} : Set ENNReal) := by
      intro p _
      exact hfin_all p
    have h_cont_real : ContinuousOn (fun p : Point3 × ℝ => (volume (S ∩ Metric.closedBall p.1 p.2)).toReal) {p | 0 < p.2} :=
      h_toReal_on.comp h_cont_closed h_image
    let D : Set (Point3 × ℝ) := Metric.closedBall midpoint 3 ×ˢ Set.Icc δ 2
    have hD_sub_Domain : D ⊆ {p : Point3 × ℝ | 0 < p.2} := by
      intro p hp
      have h2 : δ ≤ p.2 := hp.2.1
      exact hδ_pos.trans_le h2
    have hD_compact : IsCompact D :=
      (isCompact_closedBall midpoint 3).prod isCompact_Icc
    have hD_nonempty : D.Nonempty := by
      refine ⟨(midpoint, R), ?_⟩
      exact ⟨by simp, ⟨by linarith, by linarith⟩⟩
    let g : Point3 × ℝ → ℝ := fun p =>
      (volume (S ∩ Metric.closedBall p.1 p.2)).toReal * Real.rpow p.2 (-zeta)
    have h_rpow_pos_domain : ∀ p ∈ D, 0 < p.2 := by
      intro p hp
      have h2 : δ ≤ p.2 := hp.2.1
      linarith [hδ_pos]
    have h_rpow_cont : ContinuousOn (fun x : ℝ => Real.rpow x (-zeta)) {x | 0 < x} := by
      intro x hx
      have h_ne : x ≠ 0 := hx.ne'
      have h : ContinuousAt (fun x : ℝ => Real.rpow x (-zeta)) x :=
        Real.continuousAt_rpow_const x (-zeta) (Or.inl h_ne)
      exact h.continuousWithinAt
    have hg_cont : ContinuousOn g D := by
      have h1 : ContinuousOn (fun p : Point3 × ℝ => (volume (S ∩ Metric.closedBall p.1 p.2)).toReal) D :=
        h_cont_real.mono hD_sub_Domain
      have h2 : ContinuousOn (fun p : Point3 × ℝ => Real.rpow p.2 (-zeta)) D :=
        h_rpow_cont.comp continuous_snd.continuousOn h_rpow_pos_domain
      exact h1.mul h2
    rcases hD_compact.exists_isMaxOn hD_nonempty hg_cont with ⟨p, hp_D, hp_max⟩
    let xT := p.1
    let rT := p.2
    have hxT_in : xT ∈ Metric.closedBall midpoint 3 := hp_D.1
    have hrT_in : rT ∈ Set.Icc δ 2 := hp_D.2
    have hrT_delta : δ ≤ rT := hrT_in.1
    have hrT_two : rT ≤ 2 := hrT_in.2
    have hrT_pos : 0 < rT := by linarith
    let shading := S ∩ Metric.closedBall xT rT
    have hT_sub : T.carrier ⊆ Metric.closedBall midpoint (1 / 2 + δ) :=
      tube_subset_midpoint_closedBall hδ_pos T
    have hS_sub_strict : ∀ z ∈ S, dist z midpoint < R := by
      have h1 : S ⊆ T.carrier := Z.subset_tube hT
      intro z hz
      have h2 : z ∈ T.carrier := h1 hz
      have h3 : dist z midpoint ≤ 1 / 2 + δ := hT_sub h2
      have hR_def : R = 1 / 2 + 2 * δ := by rfl
      rw [hR_def]
      linarith
    have hS_sub : S ⊆ Metric.closedBall midpoint R := by
      intro z hz
      exact (hS_sub_strict z hz).le
    have h_mid_score : g (midpoint, R) ≤ g (xT, rT) :=
      hp_max ⟨by simp, ⟨by linarith, by linarith⟩⟩
    have hS_full : S ∩ Metric.closedBall midpoint R = S := by
      apply Set.inter_eq_left.mpr
      exact hS_sub
    have h_mass1 : (volume shading).toReal * Real.rpow rT (-zeta) ≥
        (volume S).toReal * Real.rpow R (-zeta) := by
      simpa [g, hS_full] using h_mid_score
    have h_rpow_pos1 : 0 < Real.rpow rT zeta := Real.rpow_pos_of_pos hrT_pos zeta
    have h_rpow_pos2 : 0 < Real.rpow R zeta := Real.rpow_pos_of_pos hR_pos zeta
    have h_mass2 : (volume shading).toReal ≥
        (volume S).toReal * Real.rpow (rT / R) zeta := by
      have h1 : (volume shading).toReal * Real.rpow rT (-zeta) ≥
          (volume S).toReal * Real.rpow R (-zeta) := h_mass1
      have h2 : Real.rpow rT (-zeta) = (Real.rpow rT zeta)⁻¹ :=
        Real.rpow_neg (by linarith) zeta
      have h3 : Real.rpow R (-zeta) = (Real.rpow R zeta)⁻¹ :=
        Real.rpow_neg (by linarith) zeta
      rw [h2, h3] at h1
      have h4 : (volume shading).toReal ≥
          (volume S).toReal * (Real.rpow R zeta)⁻¹ * Real.rpow rT zeta := by
        have h5 : (volume shading).toReal =
            ((volume shading).toReal * (Real.rpow rT zeta)⁻¹) * Real.rpow rT zeta := by
          field_simp [h_rpow_pos1.ne'] <;> ring
        rw [h5]
        gcongr
      have h6 : (volume S).toReal * (Real.rpow R zeta)⁻¹ * Real.rpow rT zeta =
          (volume S).toReal * Real.rpow (rT / R) zeta := by
        have h7 : Real.rpow (rT / R) zeta = Real.rpow rT zeta / Real.rpow R zeta :=
          Real.div_rpow (by linarith) (by linarith) zeta
        rw [h7]
        field_simp [h_rpow_pos2.ne'] <;> ring
      rw [h6] at h4
      exact h4
    have hfin1 : volume shading ≠ ⊤ :=
      ne_top_of_le_ne_top hS_finite (measure_mono (fun z hz => hz.1))
    have hfin2 : volume S ≠ ⊤ := hS_finite
    have h_mass_enn : volume shading ≥
        ENNReal.ofReal (Real.rpow (rT / R) zeta) * volume S := by
      have h_rT_R_pos : 0 < rT / R := by positivity
      have h_rpow_nonneg : 0 ≤ Real.rpow (rT / R) zeta := Real.rpow_nonneg (by positivity) zeta
      have h_vol_nonneg : 0 ≤ (volume S).toReal := by positivity
      have h_nonneg : 0 ≤ (volume S).toReal * Real.rpow (rT / R) zeta :=
        mul_nonneg h_vol_nonneg h_rpow_nonneg
      have h : ENNReal.ofReal (volume shading).toReal ≥
          ENNReal.ofReal ((volume S).toReal * Real.rpow (rT / R) zeta) :=
        ENNReal.ofReal_le_ofReal h_mass2
      have h6 : ENNReal.ofReal (volume shading).toReal = volume shading :=
        ENNReal.ofReal_toReal hfin1
      have h8 : 0 ≤ (volume S).toReal := h_vol_nonneg
      have h9 : 0 ≤ Real.rpow (rT / R) zeta := h_rpow_nonneg
      have h7 : ENNReal.ofReal ((volume S).toReal * Real.rpow (rT / R) zeta) =
          ENNReal.ofReal (Real.rpow (rT / R) zeta) * ENNReal.ofReal (volume S).toReal := by
        rw [ENNReal.ofReal_mul h8, mul_comm]
      have h10 : ENNReal.ofReal (volume S).toReal = volume S := ENNReal.ofReal_toReal hfin2
      rw [h6, h7, h10] at h
      exact h
    have h_mass_final : volume shading ≥
        ENNReal.ofReal (Real.rpow (rT / R) zeta) * hairDensity * T.volume := by
      calc volume shading
        ≥ ENNReal.ofReal (Real.rpow (rT / R) zeta) * volume S := h_mass_enn
      _ ≥ ENNReal.ofReal (Real.rpow (rT / R) zeta) * (hairDensity * T.volume) := by
        gcongr
        exact h_lower T hT
      _ = ENNReal.ofReal (Real.rpow (rT / R) zeta) * hairDensity * T.volume := by ring
    -- Two-ends property from maximality
    have h_outside : ∀ (x : Point3), x ∉ Metric.closedBall midpoint 3 →
        ∀ (t : ℝ), δ ≤ t → t ≤ 2 → S ∩ Metric.closedBall x t = ∅ := by
      intro x hx t ht1 ht2
      ext z
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
      intro hz
      have hzS : z ∈ S := hz.1
      have hzball : dist z x ≤ t := hz.2
      have hzmid : dist z midpoint < R := hS_sub_strict z hzS
      have h_sum : dist z x + dist z midpoint ≤ t + R := add_le_add hzball hzmid.le
      have h3 : t + R < 3 := by
        have hR_def : R = 1 / 2 + 2 * δ := by rfl
        rw [hR_def]
        linarith [hδ_small]
      have h_triangle : dist x midpoint ≤ dist z x + dist z midpoint := by
        calc dist x midpoint
          ≤ dist x z + dist z midpoint := dist_triangle x z midpoint
        _ = dist z x + dist z midpoint := by rw [dist_comm x z]
      have h2 : dist x midpoint < 3 := h_triangle.trans_lt (h_sum.trans_lt h3)
      have h_in : x ∈ Metric.closedBall midpoint 3 := h2.le
      exact hx h_in
    have h_two_ends : ∀ (x : Point3) (t : ℝ), δ ≤ t → t ≤ 2 →
        volume (S ∩ Metric.closedBall x t) ≤
        ENNReal.ofReal (Real.rpow (t / rT) zeta) * volume shading := by
      intro x t ht1 ht2
      by_cases hx : x ∈ Metric.closedBall midpoint 3
      · have hmax2 : g (x, t) ≤ g (xT, rT) :=
          hp_max ⟨hx, ⟨ht1, ht2⟩⟩
        have hfin_t : volume (S ∩ Metric.closedBall x t) ≠ ⊤ :=
          ne_top_of_le_ne_top hS_finite (measure_mono (fun z hz => hz.1))
        have hfin_sh : volume shading ≠ ⊤ := hfin1
        have h_pos1 : 0 < Real.rpow t zeta := Real.rpow_pos_of_pos (by linarith) zeta
        have h_pos2 : 0 < Real.rpow rT zeta := h_rpow_pos1
        have h_ineq : (volume (S ∩ Metric.closedBall x t)).toReal * Real.rpow t (-zeta) ≤
            (volume shading).toReal * Real.rpow rT (-zeta) := by
          simpa [g] using hmax2
        have h_final : (volume (S ∩ Metric.closedBall x t)).toReal ≤
            (volume shading).toReal * Real.rpow (t / rT) zeta := by
          have h1 : Real.rpow rT (-zeta) = (Real.rpow rT zeta)⁻¹ :=
            Real.rpow_neg (by linarith) zeta
          have h2 : Real.rpow t (-zeta) = (Real.rpow t zeta)⁻¹ :=
            Real.rpow_neg (by linarith) zeta
          rw [h1, h2] at h_ineq
          have h3 : (volume (S ∩ Metric.closedBall x t)).toReal ≤
              (volume shading).toReal * (Real.rpow rT zeta)⁻¹ * Real.rpow t zeta := by
            have h4 : (volume (S ∩ Metric.closedBall x t)).toReal =
                ((volume (S ∩ Metric.closedBall x t)).toReal * (Real.rpow t zeta)⁻¹) * Real.rpow t zeta := by
              field_simp [h_pos1.ne'] <;> ring
            rw [h4]
            gcongr
          have h5 : (volume shading).toReal * (Real.rpow rT zeta)⁻¹ * Real.rpow t zeta =
              (volume shading).toReal * Real.rpow (t / rT) zeta := by
            have h6 : Real.rpow (t / rT) zeta = Real.rpow t zeta / Real.rpow rT zeta :=
              Real.div_rpow (by linarith) (by linarith) zeta
            rw [h6]
            field_simp [h_pos2.ne'] <;> ring
          rw [h5] at h3
          exact h3
        have h_shading_vol_nonneg : 0 ≤ (volume shading).toReal :=
          ENNReal.toReal_nonneg
        have ht_pos : 0 < t := by linarith [hδ_pos, ht1]
        have h_t_rT_pos : 0 < t / rT := div_pos ht_pos hrT_pos
        have h_rpow_nonneg : 0 ≤ Real.rpow (t / rT) zeta := Real.rpow_nonneg h_t_rT_pos.le zeta
        have h_nonneg : 0 ≤ (volume shading).toReal * Real.rpow (t / rT) zeta :=
          mul_nonneg h_shading_vol_nonneg h_rpow_nonneg
        have h : ENNReal.ofReal (volume (S ∩ Metric.closedBall x t)).toReal ≤
            ENNReal.ofReal ((volume shading).toReal * Real.rpow (t / rT) zeta) :=
          ENNReal.ofReal_le_ofReal h_final
        have h5 : ENNReal.ofReal (volume (S ∩ Metric.closedBall x t)).toReal =
            volume (S ∩ Metric.closedBall x t) := ENNReal.ofReal_toReal hfin_t
        have h6 : ENNReal.ofReal ((volume shading).toReal * Real.rpow (t / rT) zeta) =
            ENNReal.ofReal (Real.rpow (t / rT) zeta) * ENNReal.ofReal (volume shading).toReal := by
          rw [ENNReal.ofReal_mul h_shading_vol_nonneg, mul_comm]
        have h9 : ENNReal.ofReal (volume shading).toReal = volume shading :=
          ENNReal.ofReal_toReal hfin_sh
        rw [h5, h6, h9] at h
        exact h
      · have h_empty : S ∩ Metric.closedBall x t = ∅ := h_outside x hx t ht1 ht2
        rw [h_empty] <;> simp
    -- Density-radius relation using slab bound
    let proj : Point3 → ℝ := fun y => inner ℝ (y - T.base) T.direction
    let a : ℝ := proj xT - rT
    let b : ℝ := proj xT + rT
    have hab : a ≤ b := by linarith
    have h_slab_sub : T.carrier ∩ Metric.closedBall xT rT ⊆ T.carrier ∩ {y | a ≤ proj y ∧ proj y ≤ b} := by
      intro z hz
      have hzT : z ∈ T.carrier := hz.1
      have hzball : dist z xT ≤ rT := hz.2
      have h2 : |inner ℝ (z - xT) T.direction| ≤ ‖z - xT‖ := by
        calc |inner ℝ (z - xT) T.direction|
            ≤ ‖z - xT‖ * ‖T.direction‖ := abs_real_inner_le_norm _ _
          _ = ‖z - xT‖ := by rw [T.direction_unit] <;> ring
      have h3 : |inner ℝ (z - xT) T.direction| ≤ rT := by
        calc |inner ℝ (z - xT) T.direction|
            ≤ ‖z - xT‖ := h2
          _ = dist z xT := by rw [dist_eq_norm]
          _ ≤ rT := hzball
      have h4 : proj z = proj xT + inner ℝ (z - xT) T.direction := by
        simp [proj]
        rw [show z - T.base = (z - xT) + (xT - T.base) by abel]
        rw [inner_add_left] <;> ring
      exact ⟨hzT, by rw [h4] <;> linarith [(abs_le.mp h3).1], by rw [h4] <;> linarith [(abs_le.mp h3).2]⟩
    have h_vol_slab : volume (T.carrier ∩ Metric.closedBall xT rT) ≤
        ENNReal.ofReal (4 * δ^2 * (b - a)) :=
      (measure_mono h_slab_sub).trans (tube_slab_volume_bound hδ_pos T a b hab)
    have h_len : b - a = 2 * rT := by simp [a, b] <;> ring
    have h_vol_bound : volume shading ≤ ENNReal.ofReal (8 * δ^2 * rT) := by
      have h1 : shading ⊆ T.carrier ∩ Metric.closedBall xT rT := by
        intro z hz
        exact ⟨(Z.subset_tube hT) hz.1, hz.2⟩
      calc volume shading
          ≤ volume (T.carrier ∩ Metric.closedBall xT rT) := measure_mono h1
        _ ≤ ENNReal.ofReal (4 * δ^2 * (b - a)) := h_vol_slab
        _ = ENNReal.ofReal (8 * δ^2 * rT) := by rw [h_len] <;> ring
    have hfin_shading : volume shading ≠ ⊤ := hfin1
    have hfin_T : T.volume ≠ ⊤ := by
      have h3 : T.volume = Kakeya.deltaTubeVolume δ := tube_volume_scaling.1 δ T
      rw [h3]
      exact (tube_volume_scaling.2.1 δ hδ_pos (by linarith)).2
    have h_tube_lower_real : T.volume.toReal ≥ δ^2 / 8 := by
      have h : T.volume ≥ ENNReal.ofReal (δ^2 / 8) := tube_volume_lower hδ_pos (by linarith) T
      have h4 : (ENNReal.ofReal (δ^2 / 8)).toReal ≤ T.volume.toReal := ENNReal.toReal_mono hfin_T h
      have h5 : (ENNReal.ofReal (δ^2 / 8)).toReal = δ^2 / 8 := by
        rw [ENNReal.toReal_ofReal] <;> positivity
      rw [h5] at h4
      exact h4
    set c_real : ℝ := Real.rpow (rT / R) zeta with hc_real_def
    have hc_pos : 0 < c_real := Real.rpow_pos_of_pos (by positivity) zeta
    have h_mass_real : (volume shading).toReal ≥ c_real * hairDensity.toReal * T.volume.toReal := by
      have h := h_mass_final
      have hfin_mul : (ENNReal.ofReal (Real.rpow (rT / R) zeta) * hairDensity * T.volume) ≠ ⊤ := by
        apply ENNReal.mul_ne_top
        · apply ENNReal.mul_ne_top
          · exact ENNReal.ofReal_ne_top
          · exact hhd_ne_top
        · exact hfin_T
      have h' := ENNReal.toReal_mono hfin1 h_mass_final
      have h_rpow_nonneg : 0 ≤ Real.rpow (rT / R) zeta := Real.rpow_nonneg (by positivity) zeta
      have h_expand : (ENNReal.ofReal (Real.rpow (rT / R) zeta) * hairDensity * T.volume).toReal =
          Real.rpow (rT / R) zeta * hairDensity.toReal * T.volume.toReal := by
        have h1 : (ENNReal.ofReal (Real.rpow (rT / R) zeta) * hairDensity * T.volume).toReal =
            (ENNReal.ofReal (Real.rpow (rT / R) zeta) * hairDensity).toReal * T.volume.toReal := by
          rw [ENNReal.toReal_mul]
        rw [h1]
        have h2 : (ENNReal.ofReal (Real.rpow (rT / R) zeta) * hairDensity).toReal =
            (ENNReal.ofReal (Real.rpow (rT / R) zeta)).toReal * hairDensity.toReal := by
          rw [ENNReal.toReal_mul]
        rw [h2]
        have h3 : (ENNReal.ofReal (Real.rpow (rT / R) zeta)).toReal = Real.rpow (rT / R) zeta :=
          ENNReal.toReal_ofReal h_rpow_nonneg
        rw [h3] <;> ring
      rw [h_expand] at h'
      exact h'
    have h_vol_real : (volume shading).toReal ≤ 8 * δ^2 * rT := by
      have h : volume shading ≤ ENNReal.ofReal (8 * δ^2 * rT) := h_vol_bound
      have h' := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
      have h6 : (ENNReal.ofReal (8 * δ^2 * rT)).toReal = 8 * δ^2 * rT := by
        rw [ENNReal.toReal_ofReal] <;> positivity
      rw [h6] at h'
      exact h'
    have h_density_real : hairDensity.toReal ≤ 64 * Real.rpow rT (1 - zeta) := by
      have h1 : c_real * hairDensity.toReal * T.volume.toReal ≤ 8 * δ^2 * rT := by
        calc c_real * hairDensity.toReal * T.volume.toReal
            ≤ (volume shading).toReal := h_mass_real
          _ ≤ 8 * δ^2 * rT := h_vol_real
      have h2 : c_real * hairDensity.toReal * (δ^2 / 8) ≤ 8 * δ^2 * rT := by
        calc c_real * hairDensity.toReal * (δ^2 / 8)
            ≤ c_real * hairDensity.toReal * T.volume.toReal := by gcongr <;> linarith
          _ ≤ 8 * δ^2 * rT := h1
      have h3 : 0 < c_real := hc_pos
      have h4 : 0 < δ^2 / 8 := by positivity
      have h_pos : 0 < c_real * (δ^2 / 8) := mul_pos h3 h4
      have h5 : hairDensity.toReal ≤ (8 * δ^2 * rT) / (c_real * (δ^2 / 8)) := by
        have h2' : hairDensity.toReal * (c_real * (δ^2 / 8)) ≤ 8 * δ^2 * rT := by
          have h_comm : hairDensity.toReal * (c_real * (δ^2 / 8)) = c_real * hairDensity.toReal * (δ^2 / 8) := by ring
          rw [h_comm]
          exact h2
        have h_eq : hairDensity.toReal = (hairDensity.toReal * (c_real * (δ^2 / 8))) / (c_real * (δ^2 / 8)) := by
          field_simp [h_pos.ne'] <;> ring
        rw [h_eq]
        gcongr
      have h6 : (8 * δ^2 * rT) / (c_real * (δ^2 / 8)) = 64 * rT / c_real := by
        field_simp [h3.ne', h4.ne'] <;> ring
      rw [h6] at h5
      have h7 : c_real = Real.rpow rT zeta / Real.rpow R zeta := by
        rw [hc_real_def]
        exact Real.div_rpow (by linarith) (by linarith) zeta
      rw [h7] at h5
      have h8 : 64 * rT / (Real.rpow rT zeta / Real.rpow R zeta) =
          64 * Real.rpow R zeta * Real.rpow rT (1 - zeta) := by
        have h9 : Real.rpow rT (1 - zeta) = rT / Real.rpow rT zeta := by
          have h10 : Real.rpow rT (1 - zeta) = Real.rpow rT 1 / Real.rpow rT zeta :=
            Real.rpow_sub (by linarith) 1 zeta
          rw [h10]
          have h11 : Real.rpow rT 1 = rT := by simp
          rw [h11]
        rw [h9]
        field_simp [Real.rpow_pos_of_pos hrT_pos zeta |>.ne', h_rpow_pos2.ne'] <;> ring
      rw [h8] at h5
      have h10 : Real.rpow R zeta ≤ 1 := by
        have h11 : R ≤ 1 := hR_le_one
        have h12 : Real.rpow R zeta ≤ Real.rpow 1 zeta := Real.rpow_le_rpow (by linarith) h11 hzeta_pos.le
        simpa using h12
      have h13 : 0 ≤ Real.rpow rT (1 - zeta) := Real.rpow_nonneg (by linarith) (1 - zeta)
      have h14 : hairDensity.toReal ≤ 64 * Real.rpow R zeta * Real.rpow rT (1 - zeta) := h5
      have h15 : 64 * Real.rpow R zeta * Real.rpow rT (1 - zeta) ≤ 64 * Real.rpow rT (1 - zeta) := by
        have h16 : 64 * Real.rpow R zeta * Real.rpow rT (1 - zeta) ≤ 64 * 1 * Real.rpow rT (1 - zeta) := by
          gcongr
          <;> linarith
        simpa using h16
      linarith
    have h_density_enn : hairDensity ≤ ENNReal.ofReal (64 * Real.rpow rT (1 - zeta)) := by
      have h_nonneg : 0 ≤ hairDensity.toReal := by positivity
      have h : ENNReal.ofReal hairDensity.toReal ≤ ENNReal.ofReal (64 * Real.rpow rT (1 - zeta)) :=
        ENNReal.ofReal_le_ofReal h_density_real
      have h2 : ENNReal.ofReal hairDensity.toReal = hairDensity :=
        ENNReal.ofReal_toReal hhd_ne_top
      rw [h2] at h
      exact h
    exact ⟨xT, rT, hrT_delta, hrT_two, h_mass_final, h_two_ends, h_density_enn⟩
  choose xT rT h_rT_delta h_rT_two h_mass h_two_ends h_density using h_main

  -- Pigeonhole the selected radii
  let f : α → ℝ := fun i => rT i
  have hf_range : ∀ i : α, δ ≤ f i ∧ f i ≤ 2 := by
    intro i
    exact ⟨h_rT_delta i, h_rT_two i⟩
  rcases radius_pigeonhole hδ_pos hδ_small f hf_range familyLoss hfl_pos (hlog_bound δ hδ_pos hδ_le) with
    ⟨radius, sub, hrad_delta, hrad_two, hcard, hbin⟩
  let family : Kakeya.TubeFamily δ := sub.image Subtype.val
  have hfamily_subset : family ⊆ H := by
    intro T hT
    have hT' : T ∈ Finset.image Subtype.val sub := by simpa [family] using hT
    have h_exists : ∃ (i : α), i ∈ sub ∧ i.val = T := Finset.mem_image.mp hT'
    rcases h_exists with ⟨i, hi, h_eq⟩
    have h_goal : T ∈ H := by
      have h_i_in_H : i.val ∈ H := i.property
      rwa [h_eq] at h_i_in_H
    exact h_goal
  have hfamily_nonempty : family.Nonempty := by
    have h1 : (sub.card : ENNReal) ≥
        ENNReal.ofReal (Real.rpow δ familyLoss) * (Finset.univ : Finset α).card := hcard
    have h_univ_nonempty : Nonempty α := by
      rcases hH_nonempty with ⟨T, hT⟩
      exact ⟨⟨T, hT⟩⟩
    have h2 : 0 < (Finset.univ : Finset α).card := Finset.univ_nonempty.card_pos
    have h4 : 0 < ENNReal.ofReal (Real.rpow δ familyLoss) :=
      ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hδ_pos familyLoss)
    have h_card_pos : (0 : ENNReal) < ((Finset.univ : Finset α).card : ENNReal) := by exact_mod_cast h2
    have h6 : (0 : ENNReal) < ENNReal.ofReal (Real.rpow δ familyLoss) * ((Finset.univ : Finset α).card : ENNReal) := by
      apply ENNReal.mul_pos
      · exact h4.ne'
      · exact h_card_pos.ne'
    have h7 : (0 : ENNReal) < (sub.card : ENNReal) := h6.trans_le h1
    have h8 : 0 < sub.card := by exact_mod_cast h7
    have h9 : sub.Nonempty := Finset.card_pos.mp h8
    exact Finset.Nonempty.image h9 Subtype.val
  have hfamily_card : family.enncard ≥ Kakeya.realRpowENN δ familyLoss * H.enncard := by
    have h_inj : Set.InjOn (fun (i : α) => i.val) sub := by
      intro i _ j _ h
      exact Subtype.ext h
    have h_eq : family.card = sub.card := by
      rw [Finset.card_image_of_injOn h_inj]
    have h_goal : (family.card : ENNReal) ≥ Kakeya.realRpowENN δ familyLoss * (H.card : ENNReal) := by
      have h_unfold : Kakeya.realRpowENN δ familyLoss = ENNReal.ofReal (Real.rpow δ familyLoss) := by
        rfl
      rw [h_unfold, h_eq, ←hα_univ_card]
      exact hcard
    simpa [Kakeya.TubeFamily.enncard] using h_goal
  let shading : Kakeya.Shading family :=
    { carrier := fun T =>
        if hT : T ∈ H then
          Z.carrier T ∩ Metric.closedBall (xT ⟨T, hT⟩) (rT ⟨T, hT⟩)
        else ∅
    , measurable_carrier := by
        intro T hT
        have hT_in_H : T ∈ H := hfamily_subset hT
        have h1 : (if hT' : T ∈ H then Z.carrier T ∩ Metric.closedBall (xT ⟨T, hT'⟩) (rT ⟨T, hT'⟩) else ∅) =
            Z.carrier T ∩ Metric.closedBall (xT ⟨T, hT_in_H⟩) (rT ⟨T, hT_in_H⟩) := by
          rw [dif_pos hT_in_H]
        rw [h1]
        exact (Z.measurable_carrier hT_in_H).inter measurableSet_closedBall
    , subset_tube := by
        intro T hT
        have hT_in_H : T ∈ H := hfamily_subset hT
        have h1 : (if hT' : T ∈ H then Z.carrier T ∩ Metric.closedBall (xT ⟨T, hT'⟩) (rT ⟨T, hT'⟩) else ∅) =
            Z.carrier T ∩ Metric.closedBall (xT ⟨T, hT_in_H⟩) (rT ⟨T, hT_in_H⟩) := by
          rw [dif_pos hT_in_H]
        rw [h1]
        intro z hz
        exact (Z.subset_tube hT_in_H) hz.1 }
  have hshading_subset : ∀ T ∈ family, shading.carrier T ⊆ Z.carrier T := by
    intro T hT
    have hT_in_H : T ∈ H := hfamily_subset hT
    have h1 : shading.carrier T = Z.carrier T ∩ Metric.closedBall (xT ⟨T, hT_in_H⟩) (rT ⟨T, hT_in_H⟩) := by
      have h2 : shading.carrier T = (if hT' : T ∈ H then Z.carrier T ∩ Metric.closedBall (xT ⟨T, hT'⟩) (rT ⟨T, hT'⟩) else ∅) := by
        rfl
      rw [h2, dif_pos hT_in_H]
    rw [h1]
    intro z hz
    exact hz.1
  have h_per_hair_mass : ∀ T ∈ family,
      ENNReal.ofReal (Real.rpow radius zeta) * hairDensity * T.volume ≤
      volume (shading.carrier T) := by
    intro T hT
    have hT_in_H : T ∈ H := hfamily_subset hT
    have hT' : T ∈ Finset.image Subtype.val sub := by simpa [family] using hT
    have h_exists : ∃ (i : α), i ∈ sub ∧ i.val = T := Finset.mem_image.mp hT'
    rcases h_exists with ⟨i, hi, h_eq⟩
    subst h_eq
    have h_ge : radius ≤ rT i := (hbin i hi).1
    have h9 : rT i / R ≥ radius := by
      have h10 : R ≤ 1 := hR_le_one
      have h11 : rT i ≥ radius := h_ge
      have h12 : rT i / R ≥ rT i := by
        have h_pos : 0 < R := hR_pos
        have h_nonneg : 0 ≤ rT i := by linarith
        calc rT i
          = (rT i / R) * R := by field_simp [h_pos.ne'] <;> ring
        _ ≤ (rT i / R) * 1 := by gcongr <;> linarith [hR_le_one]
        _ = rT i / R := by ring
      linarith
    have h13 : Real.rpow (rT i / R) zeta ≥ Real.rpow radius zeta :=
      Real.rpow_le_rpow (by linarith) h9 hzeta_pos.le
    have h14 := h_mass i
    have h15 : shading.carrier i.val = Z.carrier i.val ∩ Metric.closedBall (xT i) (rT i) := by
      simp [shading, i.property]
    rw [h15] at *
    simpa using calc
      ENNReal.ofReal (Real.rpow radius zeta) * hairDensity * i.val.volume
        ≤ ENNReal.ofReal (Real.rpow (rT i / R) zeta) * hairDensity * i.val.volume := by
          gcongr <;> exact h13
      _ ≤ volume (Z.carrier i.val ∩ Metric.closedBall (xT i) (rT i)) := h14
  have h_two_ends_final : ∀ T ∈ family, ∀ (x : Point3), ∀ (r : ℝ), δ ≤ r → r ≤ 2 →
      volume (shading.carrier T ∩ Metric.ball x r) ≤
      ENNReal.ofReal 4 * ENNReal.ofReal (Real.rpow (r / radius) zeta) * volume (shading.carrier T) := by
    intro T hT x r hr_delta hr_two
    have hT_in_H : T ∈ H := hfamily_subset hT
    have hT' : T ∈ Finset.image Subtype.val sub := by simpa [family] using hT
    have h_exists : ∃ (i : α), i ∈ sub ∧ i.val = T := Finset.mem_image.mp hT'
    rcases h_exists with ⟨i, hi, h_eq⟩
    subst h_eq
    have h_ge : radius ≤ rT i := (hbin i hi).1
    have hr_pos : 0 < r := by linarith
    have h15 : shading.carrier i.val = Z.carrier i.val ∩ Metric.closedBall (xT i) (rT i) := by
      have hT_in_H : i.val ∈ H := i.property
      have h2 : shading.carrier i.val = (if hT' : i.val ∈ H then Z.carrier i.val ∩ Metric.closedBall (xT ⟨i.val, hT'⟩) (rT ⟨i.val, hT'⟩) else ∅) := by rfl
      rw [h2, dif_pos hT_in_H]
      <;> rfl
    have h1 : shading.carrier i.val ∩ Metric.ball x r ⊆ Z.carrier i.val ∩ Metric.closedBall x r := by
      intro z hz
      have hz1 : z ∈ shading.carrier i.val := hz.1
      rw [h15] at hz1
      exact ⟨hz1.1, Metric.ball_subset_closedBall hz.2⟩
    have h2 : volume (shading.carrier i.val ∩ Metric.ball x r) ≤
        volume (Z.carrier i.val ∩ Metric.closedBall x r) := measure_mono h1
    have h3 : volume (Z.carrier i.val ∩ Metric.closedBall x r) ≤
        ENNReal.ofReal (Real.rpow (r / (rT i)) zeta) *
        volume (Z.carrier i.val ∩ Metric.closedBall (xT i) (rT i)) := h_two_ends i x r hr_delta hr_two
    have h4 : Real.rpow (r / (rT i)) zeta ≤ Real.rpow (r / radius) zeta := by
      have h5 : r / (rT i) ≤ r / radius := by gcongr <;> linarith
      have h_pos1 : 0 ≤ r / (rT i) := by
        have hr_pos' : 0 < r := by linarith [hδ_pos, hr_delta]
        have hrT_pos' : 0 < rT i := by linarith [hrad_delta, h_ge]
        positivity
      exact Real.rpow_le_rpow h_pos1 h5 hzeta_pos.le
    have h5 : volume (Z.carrier i.val ∩ Metric.closedBall x r) ≤
        ENNReal.ofReal (Real.rpow (r / (rT i)) zeta) * volume (shading.carrier i.val) := by
      rw [←h15] at h3
      exact h3
    have h6 : ENNReal.ofReal (Real.rpow (r / (rT i)) zeta) ≤
        ENNReal.ofReal (Real.rpow (r / radius) zeta) := ENNReal.ofReal_le_ofReal h4
    have h7 : ENNReal.ofReal (Real.rpow (r / radius) zeta) * volume (shading.carrier i.val) ≤
        ENNReal.ofReal 4 * ENNReal.ofReal (Real.rpow (r / radius) zeta) * volume (shading.carrier i.val) := by
      have h10 : ENNReal.ofReal 4 = (4 : ENNReal) := by simp
      rw [h10]
      have h12 : (1 : ENNReal) ≤ (4 : ENNReal) := by norm_num
      have h13 : (1 : ENNReal) * (ENNReal.ofReal (Real.rpow (r / radius) zeta) * volume (shading.carrier i.val)) ≤
          (4 : ENNReal) * (ENNReal.ofReal (Real.rpow (r / radius) zeta) * volume (shading.carrier i.val)) :=
        mul_le_mul_right' h12 _
      have h14 : (1 : ENNReal) * (ENNReal.ofReal (Real.rpow (r / radius) zeta) * volume (shading.carrier i.val)) =
          ENNReal.ofReal (Real.rpow (r / radius) zeta) * volume (shading.carrier i.val) := by simp
      have h15 : (4 : ENNReal) * (ENNReal.ofReal (Real.rpow (r / radius) zeta) * volume (shading.carrier i.val)) =
          (4 : ENNReal) * ENNReal.ofReal (Real.rpow (r / radius) zeta) * volume (shading.carrier i.val) := by
        ring
      rw [h14, h15] at h13
      exact h13
    calc volume (shading.carrier i.val ∩ Metric.ball x r)
        ≤ volume (Z.carrier i.val ∩ Metric.closedBall x r) := h2
      _ ≤ ENNReal.ofReal (Real.rpow (r / (rT i)) zeta) * volume (shading.carrier i.val) := h5
      _ ≤ ENNReal.ofReal (Real.rpow (r / radius) zeta) * volume (shading.carrier i.val) := by gcongr
      _ ≤ ENNReal.ofReal 4 * ENNReal.ofReal (Real.rpow (r / radius) zeta) * volume (shading.carrier i.val) := h7
  have h_density_final : hairDensity ≤
      ENNReal.ofReal 100 * ENNReal.ofReal (Real.rpow radius (1 - zeta)) := by
    have h_nonempty : family.Nonempty := hfamily_nonempty
    rcases h_nonempty with ⟨T, hT⟩
    have hT' : T ∈ Finset.image Subtype.val sub := by simpa [family] using hT
    have h_exists : ∃ (i : α), i ∈ sub ∧ i.val = T := Finset.mem_image.mp hT'
    rcases h_exists with ⟨i, hi, h_eq⟩
    subst h_eq
    have h_ge : radius ≤ rT i := (hbin i hi).1
    have h_lt : rT i < (3 / 2 : ℝ) * radius := (hbin i hi).2
    have h1 := h_density i
    have h_rad_nonneg : 0 ≤ radius := by linarith [hrad_delta]
    have h2 : Real.rpow (rT i) (1 - zeta) < Real.rpow ((3 / 2 : ℝ) * radius) (1 - zeta) :=
      Real.rpow_lt_rpow (by linarith [hrad_delta]) h_lt h_one_minus_zeta_pos
    have h3 : Real.rpow ((3 / 2 : ℝ) * radius) (1 - zeta) =
        Real.rpow (3 / 2 : ℝ) (1 - zeta) * Real.rpow radius (1 - zeta) :=
      Real.mul_rpow (by norm_num) h_rad_nonneg
    have h2' : Real.rpow (rT i) (1 - zeta) < Real.rpow (3 / 2 : ℝ) (1 - zeta) * Real.rpow radius (1 - zeta) := by
      rw [h3] at h2
      exact h2
    have h4 : Real.rpow (3 / 2 : ℝ) (1 - zeta) ≤ 3 / 2 := by
      have h5 : 0 < 1 - zeta := h_one_minus_zeta_pos
      have h6 : 1 - zeta ≤ 1 := by linarith
      have h7 : Real.rpow (3 / 2 : ℝ) (1 - zeta) ≤ Real.rpow (3 / 2 : ℝ) 1 :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      have h8 : Real.rpow (3 / 2 : ℝ) 1 = 3 / 2 := by simp
      rw [h8] at h7
      exact h7
    have h_rpow_rad_nonneg : 0 ≤ Real.rpow radius (1 - zeta) := Real.rpow_nonneg h_rad_nonneg (1 - zeta)
    have h_step1 : 64 * Real.rpow (rT i) (1 - zeta) ≤
        64 * (Real.rpow (3 / 2 : ℝ) (1 - zeta) * Real.rpow radius (1 - zeta)) :=
      mul_le_mul_of_nonneg_left h2'.le (by norm_num)
    have h_step2 : (64 * Real.rpow (3 / 2 : ℝ) (1 - zeta)) * Real.rpow radius (1 - zeta) ≤
        (64 * (3 / 2)) * Real.rpow radius (1 - zeta) := by
      have h41 : 64 * Real.rpow (3 / 2 : ℝ) (1 - zeta) ≤ 64 * (3 / 2) :=
        mul_le_mul_of_nonneg_left h4 (by norm_num)
      exact mul_le_mul_of_nonneg_right h41 h_rpow_rad_nonneg
    have h5 : 64 * Real.rpow (rT i) (1 - zeta) ≤ 100 * Real.rpow radius (1 - zeta) := by
      calc 64 * Real.rpow (rT i) (1 - zeta)
        ≤ 64 * (Real.rpow (3 / 2 : ℝ) (1 - zeta) * Real.rpow radius (1 - zeta)) := h_step1
      _ = (64 * Real.rpow (3 / 2 : ℝ) (1 - zeta)) * Real.rpow radius (1 - zeta) := by ring
      _ ≤ (64 * (3 / 2)) * Real.rpow radius (1 - zeta) := h_step2
      _ = 96 * Real.rpow radius (1 - zeta) := by norm_num
      _ ≤ 100 * Real.rpow radius (1 - zeta) := by
        exact mul_le_mul_of_nonneg_right (by norm_num) h_rpow_rad_nonneg
    have h6 : hairDensity ≤ ENNReal.ofReal (64 * Real.rpow (rT i) (1 - zeta)) := h1
    have h7 : ENNReal.ofReal (64 * Real.rpow (rT i) (1 - zeta)) ≤
        ENNReal.ofReal (100 * Real.rpow radius (1 - zeta)) := ENNReal.ofReal_le_ofReal h5
    have h_pos100 : 0 ≤ (100 : ℝ) := by norm_num
    have h8 : ENNReal.ofReal (100 * Real.rpow radius (1 - zeta)) =
        ENNReal.ofReal 100 * ENNReal.ofReal (Real.rpow radius (1 - zeta)) := by
      rw [ENNReal.ofReal_mul h_pos100] <;> ring
    calc hairDensity
        ≤ ENNReal.ofReal (64 * Real.rpow (rT i) (1 - zeta)) := h6
      _ ≤ ENNReal.ofReal (100 * Real.rpow radius (1 - zeta)) := h7
      _ = ENNReal.ofReal 100 * ENNReal.ofReal (Real.rpow radius (1 - zeta)) := h8
  exact ⟨family, hfamily_subset, hfamily_nonempty, hfamily_card, shading,
    hshading_subset, radius, hrad_delta, hrad_two,
    h_per_hair_mass, h_two_ends_final, h_density_final⟩

end Kakeya.Assouad
