import MyLeanRepo.Kakeya.Streamlined.Basic
import MyLeanRepo.Kakeya.Streamlined.Families
import MyLeanRepo.Kakeya.Streamlined.GeneralizedFrostman.RigidMotion
import MyLeanRepo.Kakeya.Streamlined.GeneralizedFrostman.CrossCopyDistinct
import MyLeanRepo.Kakeya.Streamlined.GeneralizedFrostman.DirectionalAntiConcentration
import MyLeanRepo.Kakeya.Streamlined.GeneralizedFrostman.QuaternionDirectionalAntiConcentration.Main
import MyLeanRepo.Kakeya.Streamlined.GeneralizedFrostman.BallTenReduction
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.NonDistinctDilatedContainment
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.TubeVolume
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.TranslateTubeGeometry
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# O(δ⁴) pair-collision composition theorem

Combines directional anti-concentration (O(α²)) with translation anti-concentration
(O(δ²)) to show that the probability of two randomly rigid-moved tubes being
non-essentially-distinct is O(δ⁴).
-/

noncomputable section

open MeasureTheory Metric Classical
open Kakeya.Streamlined
open Kakeya.Streamlined.GeneralizedFrostman
open Kakeya.Streamlined.RandomTranslation
open Kakeya.Streamlined.GeometricLemmas

namespace Kakeya.Streamlined.GeneralizedFrostman

/-- Data bundle for the directional anti-concentration result. -/
structure DirectionalAntiConcData where
  μ : Measure (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)
  hμ_prob : IsProbabilityMeasure μ
  rotation : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 → (Point3 ≃ₗᵢ[ℝ] Point3)
  h_meas : ∀ u : Point3, Measurable fun q => rotation q u
  C_dir : ENNReal
  hC_dir_one : 1 ≤ C_dir
  hC_dir_top : C_dir ≠ ⊤
  h_bound : ∀ u v : Point3, ‖u‖ = 1 → ‖v‖ = 1 →
    ∀ alpha : ℝ, 0 < alpha → alpha ≤ 1 →
      μ {q | ‖rotation q u - v‖ ≤ alpha ∨ ‖rotation q u + v‖ ≤ alpha} ≤
        C_dir * ENNReal.ofReal (alpha ^ 2)

/-- There exists anti-concentration data. -/
lemma exists_directionalAntiConcData : Nonempty DirectionalAntiConcData := by
  rcases quaternion_directional_anti_concentration_main with
    ⟨μ, hμ, rotation, h_meas, C, hC1, hCtop, h_bound⟩
  exact ⟨⟨μ, hμ, rotation, h_meas, C, hC1, hCtop, h_bound⟩⟩

variable (data : DirectionalAntiConcData)

/-- Midpoint of a rotated+translated tube. -/
private lemma rotated_midpoint {δ : ℝ} (T : Kakeya.DeltaTube δ)
    (e : Point3 ≃ₗᵢ[ℝ] Point3) (t : Point3) :
    tubeMidpoint (translateTube (rigidMoveTube T e 0) t) =
      e (tubeMidpoint T) + t := by
  have h1 : (translateTube (rigidMoveTube T e 0) t).base =
      e T.base + t := by
    simp [translateTube, rigidMoveTube]
    <;> abel
  have h2 : (translateTube (rigidMoveTube T e 0) t).direction =
      e T.direction := by
    simp [translateTube, rigidMoveTube]
  rw [tubeMidpoint, h1, h2]
  have h3 : e T.base + t + (1 / 2 : ℝ) • e T.direction =
      e (T.base + (1 / 2 : ℝ) • T.direction) + t := by
    have h41 : e (T.base + (1 / 2 : ℝ) • T.direction) = e T.base + e ((1 / 2 : ℝ) • T.direction) := e.map_add _ _
    have h42 : e ((1 / 2 : ℝ) • T.direction) = (1 / 2 : ℝ) • e T.direction := e.map_smul _ _
    rw [h41, h42] <;> abel
  exact h3

/-- If T is in unit ball, its midpoint has norm ≤ 1. -/
private lemma midpoint_norm_le_one {δ : ℝ} (T : Kakeya.DeltaTube δ)
    (hδ : 0 ≤ δ) (hT_ball : T.carrier ⊆ Kakeya.DeltaTube.unitBall) :
    ‖tubeMidpoint T‖ ≤ 1 := by
  have h1 : tubeMidpoint T ∈ T.carrier := tubeMidpoint_in_carrier T hδ
  have h2 : tubeMidpoint T ∈ Kakeya.DeltaTube.unitBall := hT_ball h1
  have h3 : ‖tubeMidpoint T‖ ≤ 1 := by
    simpa [Kakeya.DeltaTube.unitBall, Metric.mem_closedBall] using h2
  exact h3

/-- Joint measurability of rotation evaluation from pointwise measurability. -/
lemma rotation_joint_measurable
    {Q : Type*} [MeasurableSpace Q]
    (rot : Q → (Point3 ≃ₗᵢ[ℝ] Point3))
    (h_meas : ∀ u : Point3, Measurable fun q => rot q u) :
    Measurable (fun p : Q × Point3 => rot p.1 p.2) := by
  let e0 : Point3 := EuclideanSpace.single 0 1
  let e1 : Point3 := EuclideanSpace.single 1 1
  let e2 : Point3 := EuclideanSpace.single 2 1
  have h_me0 : Measurable fun q : Q => rot q e0 := h_meas e0
  have h_me1 : Measurable fun q : Q => rot q e1 := h_meas e1
  have h_me2 : Measurable fun q : Q => rot q e2 := h_meas e2
  have h_expand : ∀ (q : Q) (x : Point3),
      rot q x = x 0 • rot q e0 + x 1 • rot q e1 + x 2 • rot q e2 := by
    intro q x
    have h_basis : x = x 0 • e0 + x 1 • e1 + x 2 • e2 := by
      ext j
      fin_cases j <;> simp [e0, e1, e2, PiLp.single_apply] <;> norm_num
    have h_lin : ∀ (a b c : ℝ), rot q (a • e0 + b • e1 + c • e2) =
        a • rot q e0 + b • rot q e1 + c • rot q e2 := by
      intro a b c
      have h1 : rot q (a • e0 + b • e1 + c • e2) =
          rot q (a • e0 + b • e1) + rot q (c • e2) :=
        (rot q).map_add (a • e0 + b • e1) (c • e2)
      rw [h1]
      have h2 : rot q (a • e0 + b • e1) = rot q (a • e0) + rot q (b • e1) :=
        (rot q).map_add (a • e0) (b • e1)
      rw [h2]
      have h3 : rot q (a • e0) = a • rot q e0 := (rot q).map_smul a e0
      have h4 : rot q (b • e1) = b • rot q e1 := (rot q).map_smul b e1
      have h5 : rot q (c • e2) = c • rot q e2 := (rot q).map_smul c e2
      rw [h3, h4, h5] <;> rfl
    have h_goal : rot q x = x 0 • rot q e0 + x 1 • rot q e1 + x 2 • rot q e2 := by
      have h9 : rot q x = rot q (x 0 • e0 + x 1 • e1 + x 2 • e2) := by
        apply congr_arg (rot q) h_basis
      rw [h9]
      exact h_lin (x 0) (x 1) (x 2)
    exact h_goal
  have h_eq : (fun p : Q × Point3 => rot p.1 p.2) =
      fun p : Q × Point3 => p.2 0 • rot p.1 e0 + p.2 1 • rot p.1 e1 + p.2 2 • rot p.1 e2 := by
    funext p
    exact h_expand p.1 p.2
  rw [h_eq]
  fun_prop

/-- O(δ⁴) pair-collision bound for a single random rigid motion. -/
lemma pair_collision_single_motion
    {δ : ℝ} (hδ : 0 < δ) (hδ_small : δ ≤ 1 / 1000)
    (T U : Kakeya.DeltaTube δ)
    (hT_ball : T.carrier ⊆ Kakeya.DeltaTube.unitBall)
    (hU_ball : U.carrier ⊆ Kakeya.DeltaTube.unitBall) :
    let B1 := Metric.closedBall (0 : Point3) 1
    let ν := volume.restrict B1
    (data.μ.prod ν) {p : _ × Point3 |
        p.2 ∈ B1 ∧
        ¬ (translateTube (rigidMoveTube T (data.rotation p.1) 0) p.2).EssentiallyDistinct U}
    ≤ 2 * U.volume * data.C_dir * ENNReal.ofReal ((1000 * δ) ^ 2) := by
  let α : ℝ := 1000 * δ
  have hα_pos : 0 < α := by positivity
  have hα_le_one : α ≤ 1 := by linarith
  let B1 := Metric.closedBall (0 : Point3) 1
  let ν := volume.restrict B1
  let rot := data.rotation

  -- Direction conflict set
  let D : Set (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :=
    {q | ‖rot q T.direction - U.direction‖ ≤ α ∨
         ‖rot q T.direction + U.direction‖ ≤ α}

  have h_meas1 : Measurable fun q => rot q T.direction := data.h_meas T.direction
  have hD_meas : MeasurableSet D := by
    have h1 : Measurable fun q => ‖rot q T.direction - U.direction‖ :=
      h_meas1.sub measurable_const |>.norm
    have h2 : Measurable fun q => ‖rot q T.direction + U.direction‖ :=
      h_meas1.add measurable_const |>.norm
    exact (h1 measurableSet_Iic).union (h2 measurableSet_Iic)

  have hμD : data.μ D ≤ data.C_dir * ENNReal.ofReal (α ^ 2) :=
    data.h_bound T.direction U.direction T.direction_unit U.direction_unit α hα_pos hα_le_one

  -- For q ∉ D, all translations give ED
  have h_good_direction : ∀ q ∉ D, ∀ (t : Point3), t ∈ B1 →
      (translateTube (rigidMoveTube T (rot q) 0) t).EssentiallyDistinct U := by
    intro q hq t ht
    have h1 : ¬(‖rot q T.direction - U.direction‖ ≤ α) := by
      exact fun h => hq (Or.inl h)
    have h2 : ¬(‖rot q T.direction + U.direction‖ ≤ α) := by
      exact fun h => hq (Or.inr h)
    have h_not_and : ¬(‖rot q T.direction - U.direction‖ ≤ α) ∧ ¬(‖rot q T.direction + U.direction‖ ≤ α) := ⟨h1, h2⟩
    have h_gt1 : ‖rot q T.direction - U.direction‖ > α := by
      exact lt_of_not_ge h_not_and.1
    have h_gt2 : ‖rot q T.direction + U.direction‖ > α := by
      exact lt_of_not_ge h_not_and.2
    let T1 := translateTube (rigidMoveTube T (rot q) 0) t
    have hdir1 : ‖T1.direction - U.direction‖ > α := by
      have h_eq : T1.direction = rot q T.direction := by
        simp [T1, translateTube, rigidMoveTube]
      rw [h_eq]; exact h_gt1
    have hdir2 : ‖T1.direction + U.direction‖ > α := by
      have h_eq : T1.direction = rot q T.direction := by
        simp [T1, translateTube, rigidMoveTube]
      rw [h_eq]; exact h_gt2
    by_cases h_ed : T1.EssentiallyDistinct U
    · exact h_ed
    · exfalso
      have h_non_ed : ¬T1.EssentiallyDistinct U := h_ed
      have h_m1 : ‖tubeMidpoint T1‖ ≤ 3 := by
        have h4 : tubeMidpoint T1 = rot q (tubeMidpoint T) + t :=
          rotated_midpoint T (rot q) t
        rw [h4]
        have h5 : ‖tubeMidpoint T‖ ≤ 1 := midpoint_norm_le_one T (by linarith) hT_ball
        have h6 : ‖rot q (tubeMidpoint T)‖ = ‖tubeMidpoint T‖ :=
          (rot q).norm_map (tubeMidpoint T)
        have h7 : ‖t‖ ≤ 1 := by simpa [B1, Metric.mem_closedBall] using ht
        have h8 : ‖rot q (tubeMidpoint T) + t‖ ≤ ‖rot q (tubeMidpoint T)‖ + ‖t‖ := norm_add_le _ _
        rw [h6] at h8
        have h9 : ‖rot q (tubeMidpoint T) + t‖ ≤ ‖tubeMidpoint T‖ + ‖t‖ := h8
        have h10 : ‖tubeMidpoint T‖ + ‖t‖ ≤ 3 := by linarith
        exact h9.trans h10
      have h_m2 : ‖tubeMidpoint U‖ ≤ 3 := by
        have h5 : ‖tubeMidpoint U‖ ≤ 1 := midpoint_norm_le_one U (by linarith) hU_ball
        linarith
      have h_result := non_distinct_local_geometry hδ (by linarith) T1 U h_m1 h_m2 h_non_ed
      have h_dir : ‖T1.direction - U.direction‖ ≤ 1000 * δ ∨ ‖T1.direction + U.direction‖ ≤ 1000 * δ := h_result.2.1
      cases h_dir with
      | inl h_dir =>
        have h_eq : ‖T1.direction - U.direction‖ = ‖rot q T.direction - U.direction‖ := by
          have h : T1.direction = rot q T.direction := by simp [T1, translateTube, rigidMoveTube]
          rw [h]
        rw [h_eq] at h_dir
        linarith
      | inr h_dir =>
        have h_eq : ‖T1.direction + U.direction‖ = ‖rot q T.direction + U.direction‖ := by
          have h : T1.direction = rot q T.direction := by simp [T1, translateTube, rigidMoveTube]
          rw [h]
        rw [h_eq] at h_dir
        linarith

  -- For q ∈ D, bad translation volume ≤ 2 * U.volume
  have h_bad_trans : ∀ q ∈ D,
      ν {t : Point3 | t ∈ B1 ∧
          ¬ (translateTube (rigidMoveTube T (rot q) 0) t).EssentiallyDistinct U}
      ≤ 2 * U.volume := by
    intro q _
    let S : Set Point3 := {t | t ∈ B1 ∧ ¬(translateTube (rigidMoveTube T (rot q) 0) t).EssentiallyDistinct U}
    have h1 : S ⊆ {v : Point3 | ¬ (translateTube (rigidMoveTube T (rot q) 0) v).EssentiallyDistinct U} := by
      intro t ht; exact ht.2
    have h_S_sub : S ⊆ B1 := by intro t ht; exact ht.1
    have h3 : ν S ≤ volume S := by
      have h_le : (volume.restrict B1 : Measure Point3) ≤ (volume : Measure Point3) :=
        MeasureTheory.Measure.restrict_le_self (μ := volume) (s := B1)
      exact h_le S
    have h7 : volume S ≤ volume {v : Point3 | ¬ (translateTube (rigidMoveTube T (rot q) 0) v).EssentiallyDistinct U} :=
      measure_mono h1
    calc ν S
      ≤ volume S := h3
    _ ≤ volume {v : Point3 | ¬ (translateTube (rigidMoveTube T (rot q) 0) v).EssentiallyDistinct U} := h7
    _ ≤ 2 * U.volume := transverse_bad_translations_volume hδ (rigidMoveTube T (rot q) 0) U

  -- Define the bad set
  let Bad : Set (_ × Point3) :=
    {p | p.2 ∈ B1 ∧ ¬ (translateTube (rigidMoveTube T (rot p.1) 0) p.2).EssentiallyDistinct U}

  -- Bad set is contained in D × B1
  have h_bad_subset : Bad ⊆ D ×ˢ B1 := by
    rintro ⟨q, t⟩ ⟨ht, h_conflict⟩
    have hq : q ∈ D := by
      by_contra h
      exact h_conflict (h_good_direction q h t ht)
    exact ⟨hq, ht⟩

  -- For q ∉ D, t-section is empty
  have h_section_empty : ∀ q ∉ D,
      (Bad.preimage (Prod.mk q)) = ∅ := by
    intro q hq
    ext t
    simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
    intro h
    have h'' : (q, t) ∈ Bad := h
    have ht : t ∈ B1 := h''.1
    exact h''.2 (h_good_direction q hq t ht)

  -- Measurability of Bad
  have h_bad_meas : MeasurableSet Bad := by
    have hT_meas : MeasurableSet T.carrier :=
      IsClosed.measurableSet Metric.isClosed_cthickening
    have hU_meas : MeasurableSet U.carrier :=
      IsClosed.measurableSet Metric.isClosed_cthickening
    let Q := sphere (0 : EuclideanSpace ℝ (Fin 4)) 1
    let S : Set ((Q × Point3) × Point3) :=
      {y | y.2 ∈ T.carrier ∧ rot y.1.1 y.2 + y.1.2 ∈ U.carrier}
    have h_map : Measurable (fun y : (Q × Point3) × Point3 => (y.1.1, y.2)) := by fun_prop
    have h_rot_joint : Measurable (fun p : (Q × Point3) × Point3 => rot p.1.1 p.2) :=
      (rotation_joint_measurable rot data.h_meas).comp h_map
    have h_add : Measurable (fun y : (Q × Point3) × Point3 => rot y.1.1 y.2 + y.1.2) :=
      h_rot_joint.add (measurable_snd.comp measurable_fst)
    have hS_meas : MeasurableSet S :=
      (hT_meas.preimage measurable_snd).inter (hU_meas.preimage h_add)
    let h_S_indicator : ((Q × Point3) × Point3) → ENNReal :=
      fun y => Set.indicator S (fun _ => (1 : ENNReal)) y
    have hS_ind_meas : Measurable h_S_indicator := by
      exact measurable_const.indicator hS_meas
    let g : (Q × Point3) → ENNReal := fun p =>
      ∫⁻ (x : Point3), h_S_indicator (p, x) ∂volume
    have hg_meas : Measurable g := Measurable.lintegral_prod_right' hS_ind_meas
    have hg_vol : ∀ p, g p = volume {x : Point3 | x ∈ T.carrier ∧ rot p.1 x + p.2 ∈ U.carrier} := by
      intro p
      let Sp : Set Point3 := {x | (p, x) ∈ S}
      have hSp_meas : MeasurableSet Sp := hS_meas.preimage (by fun_prop)
      have h_eq1 : g p = ∫⁻ (x : Point3), Set.indicator Sp (fun _ => (1 : ENNReal)) x ∂volume := by
        rfl
      rw [h_eq1]
      have h_eq2 : ∫⁻ (x : Point3), Set.indicator Sp (fun _ => (1 : ENNReal)) x ∂volume = volume Sp := by
        rw [MeasureTheory.lintegral_indicator_const₀ hSp_meas.nullMeasurableSet (1 : ENNReal)]
        <;> simp
      rw [h_eq2]
      <;> rfl
    let threshold : ENNReal := (2 : ENNReal)⁻¹ * max T.volume U.volume
    have h_bad_eq : Bad = {p | p.2 ∈ B1 ∧ g p > threshold} := by
      ext ⟨q, t⟩
      simp only [Bad, g, Set.mem_setOf_eq]
      let f : Point3 → Point3 := fun x => rot q x + t
      let f_inv : Point3 → Point3 := fun y => (rot q).symm (y - t)
      have h_f_left : ∀ x, f_inv (f x) = x := by
        intro x; simp [f, f_inv] <;> abel
      have h_f_right : ∀ y, f (f_inv y) = y := by
        intro y; simp [f, f_inv] <;> abel
      have h_f_meas : Measurable f := by fun_prop
      have h_finv_meas : Measurable f_inv := by fun_prop
      have hf_apply : ∀ x : Point3, f x = rot q x + t := by
        intro x; rfl
      let A : Set Point3 := {x | x ∈ T.carrier ∧ f x ∈ U.carrier}
      have hA_img : f '' A = (translateTube (rigidMoveTube T (rot q) 0) t).carrier ∩ U.carrier := by
        ext z
        simp only [A, Set.mem_image, Set.mem_inter_iff, Set.mem_setOf_eq]
        constructor
        · rintro ⟨x, ⟨hxT, hxU⟩, rfl⟩
          have h_car : f x ∈ (translateTube (rigidMoveTube T (rot q) 0) t).carrier := by
            rw [translateTube_carrier]
            have h1 : rot q x ∈ (rigidMoveTube T (rot q) 0).carrier := by
              rw [rigidMoveTube_carrier]
              exact ⟨x, hxT, by simp [rigidMoveMap]⟩
            exact ⟨rot q x, h1, by simp [hf_apply, translateSet]⟩
          exact ⟨h_car, hxU⟩
        · rintro ⟨hcar, hU⟩
          rw [translateTube_carrier] at hcar
          rcases hcar with ⟨y, hy_car, h_y_plus_t⟩
          rw [rigidMoveTube_carrier] at hy_car
          rcases hy_car with ⟨x, hxT, h_y_eq⟩
          have h_y_eq' : rot q x = y := by simpa [rigidMoveMap] using h_y_eq
          have h_eq : f x = z := by
            rw [hf_apply]
            have h5 : rot q x + t = y + t := by rw [h_y_eq']
            rw [h5]
            exact h_y_plus_t
          exact ⟨x, ⟨hxT, by rw [h_eq] <;> exact hU⟩, h_eq⟩
      have h_measA : MeasurableSet A := by
        have hT_meas : MeasurableSet T.carrier := IsClosed.measurableSet Metric.isClosed_cthickening
        have hU_meas : MeasurableSet U.carrier := IsClosed.measurableSet Metric.isClosed_cthickening
        exact hT_meas.inter (hU_meas.preimage h_f_meas)
      have h1_mp : MeasurePreserving (rot q) := (rot q).measurePreserving
      have h2_mp : MeasurePreserving (fun y : Point3 => y + t) := measurePreserving_add_right volume t
      have h_mp : MeasurePreserving f := h2_mp.comp h1_mp
      have h3_mp : MeasurePreserving (rot q).symm := (rot q).symm.measurePreserving
      have h4_mp : MeasurePreserving (fun y : Point3 => y - t) := measurePreserving_add_right volume (-t)
      have h_mp_inv : MeasurePreserving f_inv := h3_mp.comp h4_mp
      have h_img_vol : volume (f '' A) = volume A := by
        have h_eq : f '' A = f_inv ⁻¹' A := by
          ext z
          simp only [Set.mem_image, Set.mem_preimage]
          constructor
          · rintro ⟨x, hx, rfl⟩
            simpa [h_f_left] using hx
          · intro h
            exact ⟨f_inv z, h, h_f_right z⟩
        rw [h_eq]
        exact h_mp_inv.measure_preimage h_measA.nullMeasurableSet
      have h_vol1 : volume ((translateTube (rigidMoveTube T (rot q) 0) t).carrier ∩ U.carrier) = g (q, t) := by
        have h_eq1 : volume ((translateTube (rigidMoveTube T (rot q) 0) t).carrier ∩ U.carrier) = volume A := by
          rw [← hA_img, h_img_vol]
        rw [h_eq1]
        exact (hg_vol (q, t)).symm
      have h_vol2 : (translateTube (rigidMoveTube T (rot q) 0) t).volume = T.volume := by
        rw [translateTube_volume, rigidMoveTube_volume]
      have h_main_iff : (¬ (translateTube (rigidMoveTube T (rot q) 0) t).EssentiallyDistinct U) ↔
          g (q, t) > threshold := by
        simp only [Kakeya.DeltaTube.EssentiallyDistinct, h_vol1, h_vol2, threshold, not_le]
        <;> rfl
      constructor
      · rintro ⟨ht, h⟩
        exact ⟨ht, h_main_iff.mp h⟩
      · rintro ⟨ht, h⟩
        exact ⟨ht, h_main_iff.mpr h⟩
    rw [h_bad_eq]
    have hB1_meas : MeasurableSet B1 := isClosed_closedBall.measurableSet
    exact (measurable_snd hB1_meas).inter (hg_meas measurableSet_Ioi)

  -- Fubini
  have h_fubini : (data.μ.prod ν) Bad = ∫⁻ q, ν (Bad.preimage (Prod.mk q)) ∂data.μ := by
    rw [Measure.prod_apply h_bad_meas] <;> rfl

  let f : _ → ENNReal := fun q => ν (Bad.preimage (Prod.mk q))
  let g : _ → ENNReal := Set.indicator D (fun _ => 2 * U.volume)

  have h_le : ∀ q, f q ≤ g q := by
    intro q
    by_cases hq : q ∈ D
    · have h9 : f q ≤ 2 * U.volume := h_bad_trans q hq
      simpa [g, hq, Set.indicator_apply] using h9
    · have h10 : f q = 0 := by
        dsimp only [f]
        have h11 : Bad.preimage (Prod.mk q) = ∅ := h_section_empty q hq
        rw [h11]
        <;> simp
      simpa [g, hq, h10, Set.indicator_apply] using by positivity

  have h_main : ∫⁻ q, f q ∂data.μ ≤ ∫⁻ q, g q ∂data.μ := lintegral_mono h_le

  have h_g_int : ∫⁻ q, g q ∂data.μ = (2 * U.volume) * data.μ D := by
    have h1 : ∫⁻ q, g q ∂data.μ = ∫⁻ q, (2 * U.volume) ∂(data.μ.restrict D) := by
      rw [lintegral_indicator hD_meas]
      <;> rfl
    rw [h1]
    have h2 : ∫⁻ q, (2 * U.volume) ∂(data.μ.restrict D) =
        (2 * U.volume) * (data.μ.restrict D) Set.univ := by
      rw [lintegral_const]
      <;> ring
    rw [h2]
    have h3 : (data.μ.restrict D) Set.univ = data.μ D := by
      simp [Measure.restrict_apply]
      <;> rfl
    rw [h3] <;> ring

  calc (data.μ.prod ν) Bad
    = ∫⁻ q, f q ∂data.μ := h_fubini
  _ ≤ ∫⁻ q, g q ∂data.μ := h_main
  _ = (2 * U.volume) * data.μ D := h_g_int
  _ ≤ (2 * U.volume) * (data.C_dir * ENNReal.ofReal (α ^ 2)) := by
    exact mul_le_mul_left' hμD _
  _ = 2 * U.volume * data.C_dir * ENNReal.ofReal ((1000 * δ) ^ 2) := by
    simp [α] <;> ring_nf <;> rfl

end Kakeya.Streamlined.GeneralizedFrostman
