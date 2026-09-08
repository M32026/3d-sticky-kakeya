import MyLeanRepo.Kakeya.Streamlined.GeneralizedFrostman.RigidMotionNormalizationSelection.MeasureInfrastructure

/-!
# Generalized collision probability without unit-ball condition on target

Proves `non_ed_probability_normalized_general`: the probability that a random
rigid copy of tube `T` is non-ED with arbitrary fixed `T0`, without requiring
`T0.carrier ⊆ unitBall`.

Key trick: translate both tubes by `-tubeMidpoint T0` before applying
`non_distinct_local_geometry`. This makes T0's midpoint 0 and the moved tube's
midpoint close to 0 (when non-ED), satisfying the ≤3 bounds.
-/

noncomputable section

open MeasureTheory Metric Set Classical Finset
open Kakeya.Streamlined
open Kakeya.Streamlined.GeneralizedFrostman
open Kakeya.Streamlined.GeometricLemmas
open Kakeya.Streamlined.RandomTranslation

namespace Kakeya.Streamlined.GeneralizedFrostman

/-- Carrier and volume of rigidMoveTube equal translateTube of rigidMoveTube with 0. -/
lemma rigidMove_vs_translate_carrier {δ : ℝ} (T : Kakeya.DeltaTube δ)
    (e : Point3 ≃ₗᵢ[ℝ] Point3) (t : Point3) :
    (rigidMoveTube T e t).carrier = (translateTube (rigidMoveTube T e 0) t).carrier ∧
    (rigidMoveTube T e t).volume = (translateTube (rigidMoveTube T e 0) t).volume := by
  have h_car : (rigidMoveTube T e t).carrier = (translateTube (rigidMoveTube T e 0) t).carrier := by
    have h1 : rigidMoveMap e t = (fun x : Point3 => x + t) ∘ rigidMoveMap e 0 := by
      funext x
      simp [rigidMoveMap] <;> abel
    rw [rigidMoveTube_carrier T e t, translateTube_carrier, rigidMoveTube_carrier T e 0]
    rw [h1, Set.image_comp]
    <;> rfl
  have h_vol : (rigidMoveTube T e t).volume = (translateTube (rigidMoveTube T e 0) t).volume := by
    rw [rigidMoveTube_volume T e t, translateTube_volume, rigidMoveTube_volume T e 0]
  exact ⟨h_car, h_vol⟩

/-- Non-ED implies carriers intersect, so midpoint distance ≤ 1 + 2δ. -/
lemma non_ed_midpoint_dist_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {T1 T2 : Kakeya.DeltaTube δ}
    (h_non_ed : ¬T1.EssentiallyDistinct T2) :
    dist (tubeMidpoint T1) (tubeMidpoint T2) ≤ 1 + 2 * δ := by
  have hV_pos : 0 < T1.volume := by
    have h : T1.volume = Kakeya.deltaTubeVolume δ :=
      RandomTranslation.tube_volume_eq_deltaTubeVolume T1
    rw [h]
    exact RandomTranslation.deltaTubeVolume_pos hδ
  have h_pos : 0 < volume (T1.carrier ∩ T2.carrier) := by
    simp only [Kakeya.DeltaTube.EssentiallyDistinct] at h_non_ed
    have h' : volume (T1.carrier ∩ T2.carrier) > (2 : ENNReal)⁻¹ * max T1.volume T2.volume :=
      not_le.mp h_non_ed
    have h_max_pos : 0 < max T1.volume T2.volume := by
      apply lt_max_iff.mpr
      exact Or.inl hV_pos
    have h_inv_pos : 0 < (2 : ENNReal)⁻¹ := by norm_num
    have h_pos2 : 0 < (2 : ENNReal)⁻¹ * max T1.volume T2.volume := by
      positivity
    exact lt_trans h_pos2 h'
  have h_nonempty : (T1.carrier ∩ T2.carrier).Nonempty := by
    by_contra h_empty
    have h_eq : T1.carrier ∩ T2.carrier = ∅ := Set.not_nonempty_iff_eq_empty.mp h_empty
    rw [h_eq] at h_pos
    simp at h_pos
  rcases h_nonempty with ⟨x, hx1, hx2⟩
  have h1 : x ∈ closedBall (tubeMidpoint T1) (1 / 2 + δ) :=
    tube_carrier_subset_ball_midpoint T1 (by linarith) hx1
  have h2 : x ∈ closedBall (tubeMidpoint T2) (1 / 2 + δ) :=
    tube_carrier_subset_ball_midpoint T2 (by linarith) hx2
  have h3 : dist (tubeMidpoint T1) x ≤ 1 / 2 + δ := by
    have h4 : dist x (tubeMidpoint T1) ≤ 1 / 2 + δ := Metric.mem_closedBall.mp h1
    simpa [dist_comm] using h4
  have h4 : dist x (tubeMidpoint T2) ≤ 1 / 2 + δ := Metric.mem_closedBall.mp h2
  calc dist (tubeMidpoint T1) (tubeMidpoint T2)
    ≤ dist (tubeMidpoint T1) x + dist x (tubeMidpoint T2) := dist_triangle _ _ _
  _ ≤ (1 / 2 + δ) + (1 / 2 + δ) := by linarith
  _ = 1 + 2 * δ := by ring

/-- If directions differ by > 1000δ, then ALL translations give ED. -/
lemma good_direction_all_translations
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {T U : Kakeya.DeltaTube δ}
    (hT_ball : T.carrier ⊆ unitBall.carrier)
    (rot : Point3 ≃ₗᵢ[ℝ] Point3)
    (h_angle1 : ¬‖rot T.direction - U.direction‖ ≤ 1000 * δ)
    (h_angle2 : ¬‖rot T.direction + U.direction‖ ≤ 1000 * δ) :
    ∀ (t : Point3), (rigidMoveTube T rot t).EssentiallyDistinct U := by
  intro t
  by_contra h_non_ed
  let T1 := rigidMoveTube T rot t
  have h_dist : dist (tubeMidpoint T1) (tubeMidpoint U) ≤ 1 + 2 * δ :=
    non_ed_midpoint_dist_le hδ hδ1 h_non_ed
  let m := tubeMidpoint U
  let T1' := translateTube T1 (-m)
  let U' := translateTube U (-m)
  have h_non_ed' : ¬T1'.EssentiallyDistinct U' := by
    have h_iff : T1.EssentiallyDistinct U ↔ T1'.EssentiallyDistinct U' :=
      rigidMoveTube_essentiallyDistinct T1 U (1 : Point3 ≃ₗᵢ[ℝ] Point3) (-m)
    exact h_iff.not.mp h_non_ed
  have h_m1 : ‖tubeMidpoint T1'‖ ≤ 3 := by
    have h_eq : tubeMidpoint T1' = tubeMidpoint T1 - m := by
      simp [T1', translateTube, tubeMidpoint] <;> abel
    rw [h_eq]
    have h2 : ‖tubeMidpoint T1 - m‖ ≤ 1 + 2 * δ := by
      simpa [dist_eq_norm] using h_dist
    linarith
  have h_m2 : ‖tubeMidpoint U'‖ ≤ 3 := by
    have h_eq : tubeMidpoint U' = tubeMidpoint U - m := by
      simp [U', translateTube, tubeMidpoint] <;> abel
    rw [h_eq]
    have h3 : tubeMidpoint U - m = 0 := by simp [m] <;> abel
    rw [h3] <;> norm_num
  have h_result := non_distinct_local_geometry hδ hδ1 T1' U' h_m1 h_m2 h_non_ed'
  have h_dir : ‖T1'.direction - U'.direction‖ ≤ 1000 * δ ∨
      ‖T1'.direction + U'.direction‖ ≤ 1000 * δ := h_result.2.1
  have h_dir' : ‖rot T.direction - U.direction‖ ≤ 1000 * δ ∨
      ‖rot T.direction + U.direction‖ ≤ 1000 * δ := by
    have h1 : T1'.direction = rot T.direction := by
      simp [T1', T1, translateTube, rigidMoveTube]
    have h2 : U'.direction = U.direction := by
      simp [U', translateTube, rigidMoveTube]
    rw [h1, h2] at h_dir
    exact h_dir
  cases h_dir' with
  | inl h => exact h_angle1 h
  | inr h => exact h_angle2 h

/-- Measurability of inverse rotation evaluation. -/
lemma rotation_symm_joint_measurable
    {Q : Type*} [MeasurableSpace Q]
    (rot : Q → (Point3 ≃ₗᵢ[ℝ] Point3))
    (h_meas : ∀ u : Point3, Measurable fun q => rot q u) :
    Measurable (fun p : Q × Point3 => (rot p.1).symm p.2) := by
  let b : OrthonormalBasis (Fin 3) ℝ Point3 := EuclideanSpace.basisFun (Fin 3) ℝ
  have h_basis : ∀ (v : Point3), v = ∑ i : Fin 3, inner ℝ v (b i) • b i := by
    intro v
    have h : ∑ i : Fin 3, b.repr v i • b i = v := b.sum_repr v
    have h2 : ∀ i, b.repr v i = inner ℝ v (b i) := by
      intro i
      exact Eq.symm (EuclideanSpace.inner_basisFun_real (Fin 3) v i)
    have h3 : ∑ i : Fin 3, b.repr v i • b i = ∑ i : Fin 3, inner ℝ v (b i) • b i := by
      apply Finset.sum_congr rfl; intro i _; rw [h2 i]
    rw [h3] at h; exact h.symm
  have h_inner : ∀ (q : Q) (u : Point3) (i : Fin 3),
      inner ℝ ((rot q).symm u) (b i) = inner ℝ u ((rot q) (b i)) := by
    intro q u i
    have h3 := LinearIsometryEquiv.inner_map_map (rot q) ((rot q).symm u) (b i)
    have h4 : (rot q) ((rot q).symm u) = u := (rot q).apply_symm_apply u
    rw [h4] at h3; exact h3.symm
  have h_main : ∀ (q : Q) (u : Point3), (rot q).symm u =
      ∑ i : Fin 3, inner ℝ u ((rot q) (b i)) • b i := by
    intro q u
    rw [h_basis ((rot q).symm u)]
    apply Finset.sum_congr rfl; intro i _
    have h5 := h_inner q u i; rw [h5]
  have h_meas' : ∀ i : Fin 3, Measurable (fun p : Q × Point3 =>
      inner ℝ p.2 ((rot p.1) (b i))) := by
    intro i
    have h1 : Measurable (fun p : Q × Point3 => p.2) := measurable_snd
    have h2 : Measurable (fun p : Q × Point3 => (rot p.1) (b i)) :=
      (h_meas (b i)).comp measurable_fst
    have h_cont : Continuous (fun x : Point3 × Point3 => inner ℝ x.1 x.2) := continuous_inner
    have h_pair : Measurable (fun p : Q × Point3 => (p.2, (rot p.1) (b i))) := by fun_prop
    exact h_cont.measurable.comp h_pair
  have h3 : Measurable (fun p : Q × Point3 =>
      ∑ i : Fin 3, inner ℝ p.2 ((rot p.1) (b i)) • b i) := by
    apply Finset.measurable_sum; intro i _
    exact (h_meas' i).smul_const (b i)
  have h4 : (fun p : Q × Point3 => (rot p.1).symm p.2) =
      (fun p : Q × Point3 => ∑ i : Fin 3, inner ℝ p.2 ((rot p.1) (b i)) • b i) := by
    funext p; exact h_main p.1 p.2
  rw [h4]; exact h3

/-- The set `{(p, y) | y ∈ carrier of rigidly moved tube T(p)}` is measurable. -/
lemma moved_tube_carrier_graph_measurable
    {δ : ℝ} {Q : Type*} [MeasurableSpace Q]
    (rot : Q → (Point3 ≃ₗᵢ[ℝ] Point3))
    (h_meas : ∀ u : Point3, Measurable fun q => rot q u)
    (T : Kakeya.DeltaTube δ) :
    MeasurableSet {p : (Q × Point3) × Point3 |
      p.2 ∈ (rigidMoveTube T (rot p.1.1) p.1.2).carrier} := by
  have h1 : ∀ (q : Q) (trans : Point3) (y : Point3),
      y ∈ (rigidMoveTube T (rot q) trans).carrier ↔
      (rot q).symm (y - trans) ∈ T.carrier := by
    intro q trans y
    rw [rigidMoveTube_carrier T (rot q) trans]
    simp only [Set.mem_image]
    constructor
    · rintro ⟨x, hx, h_eq⟩
      have h5 : rigidMoveMap (rot q) trans x = y := h_eq
      have h6 : (rot q) x + trans = y := by simpa [rigidMoveMap] using h5
      have h7 : y - trans = (rot q) x := (eq_sub_of_add_eq h6).symm
      have h8 : (rot q).symm (y - trans) = x := by rw [h7]; exact (rot q).symm_apply_apply x
      rw [h8]; exact hx
    · intro hx
      refine ⟨(rot q).symm (y - trans), hx, ?_⟩
      exact rigidMove_right_inv (rot q) trans y
  have h2 : Measurable (fun p : (Q × Point3) × Point3 =>
      (rot p.1.1).symm (p.2 - p.1.2)) := by
    have h3 : Measurable (fun p : (Q × Point3) × Point3 => (p.1.1, p.2 - p.1.2)) := by fun_prop
    exact (rotation_symm_joint_measurable rot h_meas).comp h3
  have h4 : MeasurableSet T.carrier := Metric.isClosed_cthickening.measurableSet
  have h5 : {p : (Q × Point3) × Point3 | p.2 ∈ (rigidMoveTube T (rot p.1.1) p.1.2).carrier} =
      {p | (rot p.1.1).symm (p.2 - p.1.2) ∈ T.carrier} := by
    ext p; exact h1 p.1.1 p.1.2 p.2
  rw [h5]; exact h4.preimage h2

/-- Measurability of ED predicate between a rigidly moved tube and a fixed tube. -/
lemma single_moved_ed_measurable
    {δ : ℝ} {Q : Type*} [MeasurableSpace Q]
    (rot : Q → (Point3 ≃ₗᵢ[ℝ] Point3))
    (h_meas : ∀ u : Point3, Measurable fun q => rot q u)
    (T U : Kakeya.DeltaTube δ) :
    MeasurableSet {p : Q × Point3 |
      (rigidMoveTube T (rot p.1) p.2).EssentiallyDistinct U} := by
  let g : (Q × Point3) → ENNReal := fun p =>
    volume ((rigidMoveTube T (rot p.1) p.2).carrier ∩ U.carrier)
  have hU_meas : MeasurableSet U.carrier :=
    IsClosed.measurableSet Metric.isClosed_cthickening
  let ST : Set ((Q × Point3) × Point3) :=
    {p | p.2 ∈ (rigidMoveTube T (rot p.1.1) p.1.2).carrier}
  have hST_meas : MeasurableSet ST := moved_tube_carrier_graph_measurable rot h_meas T
  let S : Set ((Q × Point3) × Point3) := ST ∩ {p | p.2 ∈ U.carrier}
  have hS_meas : MeasurableSet S := hST_meas.inter (hU_meas.preimage measurable_snd)
  have hg_meas : Measurable g := by
    have h_eq : g = fun p : Q × Point3 =>
        ∫⁻ (x : Point3), Set.indicator S (fun _ => (1 : ENNReal)) (p, x) := by
      funext p
      let Sp : Set Point3 := {x | (p, x) ∈ S}
      have hSp_meas : MeasurableSet Sp := hS_meas.preimage (by fun_prop)
      have h_sec : Sp = (rigidMoveTube T (rot p.1) p.2).carrier ∩ U.carrier := by
        ext x; simp [S, ST] <;> rfl
      have h1 : (fun x : Point3 => Set.indicator S (fun _ => (1 : ENNReal)) (p, x)) =
          Set.indicator Sp (fun _ : Point3 => (1 : ENNReal)) := by
        funext x; simp [Set.indicator_apply, Sp] <;> rfl
      have h2 : ∫⁻ (x : Point3), Set.indicator S (fun _ => (1 : ENNReal)) (p, x) = volume Sp := by
        rw [h1, lintegral_indicator_const₀ hSp_meas.nullMeasurableSet (1 : ENNReal)] <;> simp
      have h3 : g p = volume Sp := by
        dsimp only [g]
        <;> rw [h_sec]
      exact Eq.trans h3 h2.symm
    rw [h_eq]
    exact Measurable.lintegral_prod_right' (measurable_const.indicator hS_meas)
  let threshold : ENNReal := (2 : ENNReal)⁻¹ * max T.volume U.volume
  have h_set_eq : {p : Q × Point3 |
      (rigidMoveTube T (rot p.1) p.2).EssentiallyDistinct U} =
      {p | g p ≤ threshold} := by
    ext p
    have h_volT : (rigidMoveTube T (rot p.1) p.2).volume = T.volume :=
      rigidMoveTube_volume T (rot p.1) p.2
    simp [g, Kakeya.DeltaTube.EssentiallyDistinct, threshold, h_volT] <;> rfl
  rw [h_set_eq]
  exact measurableSet_Iic.preimage hg_meas

/-- Generalized non-ED probability: no unit-ball condition on target T0. -/
lemma non_ed_probability_normalized_general
    {δ : ℝ} (hδ : 0 < δ) (hδ_small : δ ≤ 1 / 1000)
    (data : DirectionalAntiConcData)
    (T T0 : Kakeya.DeltaTube δ)
    (hT_ball : T.carrier ⊆ unitBall.carrier)
    (V : ENNReal) (hV_T0 : T0.volume = V) :
    rigidMotionProbMeasure data
      {p | p.2 ∈ closedBall (0 : Point3) 1 ∧
        ¬(rigidMoveTube T (data.rotation p.1) p.2).EssentiallyDistinct T0}
    ≤ (2 * V * data.C_dir * ENNReal.ofReal ((1000 * δ)^2)) / unitBallVolume := by
  let B1 := closedBall (0 : Point3) 1
  let ν := volume.restrict B1
  let α : ℝ := 1000 * δ
  have hα_pos : 0 < α := by positivity
  have hα_le_one : α ≤ 1 := by linarith
  let Q := sphere (0 : EuclideanSpace ℝ (Fin 4)) 1
  let D : Set Q :=
    {q | ‖data.rotation q T.direction - T0.direction‖ ≤ α ∨
         ‖data.rotation q T.direction + T0.direction‖ ≤ α}
  have hD_meas : MeasurableSet D := by
    have h1 : Measurable fun q : Q => ‖data.rotation q T.direction - T0.direction‖ :=
      (data.h_meas T.direction).sub measurable_const |>.norm
    have h2 : Measurable fun q : Q => ‖data.rotation q T.direction + T0.direction‖ :=
      (data.h_meas T.direction).add measurable_const |>.norm
    exact (h1 measurableSet_Iic).union (h2 measurableSet_Iic)
  have hμD : data.μ D ≤ data.C_dir * ENNReal.ofReal (α ^ 2) :=
    data.h_bound T.direction T0.direction T.direction_unit T0.direction_unit α hα_pos hα_le_one

  let Bad : Set (Q × Point3) :=
    {p | p.2 ∈ B1 ∧
      ¬(rigidMoveTube T (data.rotation p.1) p.2).EssentiallyDistinct T0}

  have hBad_meas : MeasurableSet Bad := by
    have h_ed_set : MeasurableSet {p : Q × Point3 |
        (rigidMoveTube T (data.rotation p.1) p.2).EssentiallyDistinct T0} :=
      single_moved_ed_measurable data.rotation data.h_meas T T0
    have hB1_meas : MeasurableSet B1 := Metric.isClosed_closedBall.measurableSet
    exact (hB1_meas.preimage measurable_snd).inter h_ed_set.compl

  have h_good : ∀ q ∉ D, ∀ (t : Point3),
      (rigidMoveTube T (data.rotation q) t).EssentiallyDistinct T0 := by
    intro q hq
    have h1 : ¬‖data.rotation q T.direction - T0.direction‖ ≤ α := by
      exact fun h => hq (Or.inl h)
    have h2 : ¬‖data.rotation q T.direction + T0.direction‖ ≤ α := by
      exact fun h => hq (Or.inr h)
    exact good_direction_all_translations hδ (by linarith) hT_ball (data.rotation q) h1 h2

  have h_restrict_le : (volume.restrict B1 : Measure Point3) ≤ volume :=
    MeasureTheory.Measure.restrict_le_self (μ := volume) (s := B1)

  have h_section : ∀ q : Q, ν {t : Point3 |
      ¬(rigidMoveTube T (data.rotation q) t).EssentiallyDistinct T0}
      ≤ if q ∈ D then 2 * V else 0 := by
    intro q
    by_cases hq : q ∈ D
    · rw [if_pos hq]
      have h_equiv : ∀ (t : Point3),
          (rigidMoveTube T (data.rotation q) t).EssentiallyDistinct T0 ↔
          (translateTube (rigidMoveTube T (data.rotation q) 0) t).EssentiallyDistinct T0 := by
        intro t
        have hcv := rigidMove_vs_translate_carrier T (data.rotation q) t
        simp only [Kakeya.DeltaTube.EssentiallyDistinct, hcv.1, hcv.2]
      have h_set_eq : {t : Point3 | ¬(rigidMoveTube T (data.rotation q) t).EssentiallyDistinct T0} =
          {t : Point3 | ¬(translateTube (rigidMoveTube T (data.rotation q) 0) t).EssentiallyDistinct T0} := by
        ext t; simp [h_equiv t]
      rw [h_set_eq]
      have h6 : ν {t | ¬(translateTube (rigidMoveTube T (data.rotation q) 0) t).EssentiallyDistinct T0}
          ≤ volume {t | ¬(translateTube (rigidMoveTube T (data.rotation q) 0) t).EssentiallyDistinct T0} :=
        h_restrict_le _
      have h7 : volume {t | ¬(translateTube (rigidMoveTube T (data.rotation q) 0) t).EssentiallyDistinct T0}
          ≤ 2 * T0.volume := transverse_bad_translations_volume hδ (rigidMoveTube T (data.rotation q) 0) T0
      rw [hV_T0] at h7
      exact le_trans h6 h7
    · rw [if_neg hq]
      have h8 : {t : Point3 | ¬(rigidMoveTube T (data.rotation q) t).EssentiallyDistinct T0} = ∅ := by
        ext t
        simp only [Set.mem_empty_iff_false, iff_false]
        intro h
        exact h (h_good q hq t)
      rw [h8] <;> simp

  let f : Q → ENNReal := fun q => ν (Bad.preimage (Prod.mk q))
  let g : Q → ENNReal := Set.indicator D (fun _ => 2 * V)

  have h_fubini : (data.μ.prod ν) Bad = ∫⁻ q, f q ∂data.μ := by
    rw [Measure.prod_apply hBad_meas] <;> rfl

  have h_le : ∀ q, f q ≤ g q := by
    intro q
    by_cases hq : q ∈ D
    · have h9 : f q ≤ 2 * V := by
        dsimp only [f]
        have h10 : ν (Bad.preimage (Prod.mk q)) ≤
            ν {t : Point3 | ¬(rigidMoveTube T (data.rotation q) t).EssentiallyDistinct T0} := by
          apply measure_mono
          intro t ht
          have h11 : (q, t) ∈ Bad := by simpa [Bad, Set.mem_preimage] using ht
          exact h11.2
        have h12 : f q ≤ if q ∈ D then 2 * V else 0 := le_trans h10 (h_section q)
        have h13 : f q ≤ 2 * V := by
          rw [if_pos hq] at h12
          exact h12
        exact h13
      simpa [g, hq, Set.indicator_apply] using h9
    · have h10 : f q = 0 := by
        dsimp only [f]
        have h11 : Bad.preimage (Prod.mk q) = ∅ := by
          ext t
          simp only [Set.mem_empty_iff_false, iff_false, Set.mem_preimage]
          intro h
          exact h.2 (h_good q hq t)
        rw [h11] <;> simp
      simpa [g, hq, h10, Set.indicator_apply] using by positivity

  have h_main : ∫⁻ q, f q ∂data.μ ≤ ∫⁻ q, g q ∂data.μ := lintegral_mono h_le

  have h_g_int : ∫⁻ q, g q ∂data.μ = (2 * V) * data.μ D := by
    have h1 : ∫⁻ q, g q ∂data.μ = ∫⁻ q, (2 * V) ∂(data.μ.restrict D) := by
      rw [lintegral_indicator hD_meas] <;> rfl
    rw [h1]
    have h2 : ∫⁻ q, (2 * V) ∂(data.μ.restrict D) =
        (2 * V) * (data.μ.restrict D) Set.univ := by
      rw [lintegral_const] <;> ring
    rw [h2]
    have h3 : (data.μ.restrict D) Set.univ = data.μ D := by
      simp [Measure.restrict_apply] <;> rfl
    rw [h3] <;> ring

  have h_bound : (data.μ.prod ν) Bad ≤ 2 * V * data.C_dir * ENNReal.ofReal ((1000 * δ)^2) := by
    rw [h_fubini]
    calc ∫⁻ q, f q ∂data.μ
      ≤ ∫⁻ q, g q ∂data.μ := h_main
    _ = (2 * V) * data.μ D := h_g_int
    _ ≤ (2 * V) * (data.C_dir * ENNReal.ofReal (α ^ 2)) := by
      exact mul_le_mul_left' hμD _
    _ = 2 * V * data.C_dir * ENNReal.ofReal ((1000 * δ)^2) := by
      have h9 : α = 1000 * δ := by rfl
      rw [h9] <;> ring

  rw [rigidMotionProbMeasure_apply data Bad]
  gcongr

end Kakeya.Streamlined.GeneralizedFrostman
