import MyLeanRepo.Kakeya.Assouad.Subunit.HairbrushStatements
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.CapsuleBounds
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Topology.MetricSpace.HausdorffDistance

noncomputable section

open Kakeya MeasureTheory Metric Set InnerProductSpace

namespace Kakeya.Assouad

/-- The transverse component of w relative to unit vector v has norm sin(acute angle). -/
private lemma acute_angle_transverse_norm {δ : ℝ} (hdelta : 0 < δ)
    {v w : Point3} (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (h_angle : hairbrushAcuteDirectionAngle v w < δ) :
    ‖w - (inner ℝ w v) • v‖ < δ := by
  set a : ℝ := inner ℝ w v with ha_def
  have a_comm : inner ℝ v w = a := by
    have h : inner ℝ v w = inner ℝ w v := by
      simpa using real_inner_comm w v
    rw [h, ha_def]
  set α : ℝ := hairbrushAcuteDirectionAngle v w with hα_def
  have hα_eq : α = min (Real.arccos a) (Real.pi - Real.arccos a) := by
    rw [hα_def, hairbrushAcuteDirectionAngle, a_comm]
  have hα_lt : α < δ := h_angle
  have h_a_bound1 : -1 ≤ a := by
    have h : |inner ℝ w v| ≤ ‖w‖ * ‖v‖ := abs_real_inner_le_norm w v
    rw [hv, hw] at h; have h' : |a| ≤ 1 := by simpa [ha_def] using h
    exact (abs_le.mp h').1
  have h_a_bound2 : a ≤ 1 := by
    have h : |inner ℝ w v| ≤ ‖w‖ * ‖v‖ := abs_real_inner_le_norm w v
    rw [hv, hw] at h; have h' : |a| ≤ 1 := by simpa [ha_def] using h
    exact (abs_le.mp h').2
  have hα_nonneg : 0 ≤ α := by
    rw [hα_eq]
    have h1 : 0 ≤ Real.arccos a := Real.arccos_nonneg a
    have h2 : 0 ≤ Real.pi - Real.arccos a := by linarith [Real.arccos_le_pi a]
    exact le_min h1 h2
  have h_norm_sq : ‖w - a • v‖ ^ 2 = 1 - a ^ 2 := by
    have h2 : ‖w - a • v‖ ^ 2 = ‖w‖ ^ 2 - 2 * inner ℝ w (a • v) + ‖a • v‖ ^ 2 :=
      norm_sub_sq_real w (a • v)
    have h3 : inner ℝ w (a • v) = a * a := by
      rw [inner_smul_right, ha_def]
    have h4 : ‖a • v‖ ^ 2 = a ^ 2 := by
      have h5 : ‖a • v‖ = |a| * ‖v‖ := by exact norm_smul a v
      rw [h5, hv]
      have h7 : (|a| * (1 : ℝ)) ^ 2 = a ^ 2 := by
        have h8 : (|a| * (1 : ℝ)) ^ 2 = |a| ^ 2 := by ring
        rw [h8]
        have h9 : |a| ^ 2 = a ^ 2 := by simp [sq_abs]
        exact h9
      exact h7
    rw [h2, h3, h4, hw] <;> ring
  have h_sin_sq : (Real.sin α) ^ 2 = 1 - a ^ 2 := by
    rw [hα_eq]
    by_cases h : a ≥ 0
    · have h1 : Real.arccos a ≤ Real.pi / 2 := (Real.arccos_le_pi_div_two).mpr h
      have h2 : min (Real.arccos a) (Real.pi - Real.arccos a) = Real.arccos a := by
        rw [min_eq_left] <;> linarith
      rw [h2]
      have h3 : Real.sin (Real.arccos a) ^ 2 = 1 - a ^ 2 := by
        have h4 : Real.sin (Real.arccos a) ^ 2 + Real.cos (Real.arccos a) ^ 2 = 1 := Real.sin_sq_add_cos_sq _
        have h5 : Real.cos (Real.arccos a) = a := Real.cos_arccos h_a_bound1 h_a_bound2
        rw [h5] at h4; linarith
      exact h3
    · have h1 : a < 0 := by linarith
      have h2 : Real.arccos a > Real.pi / 2 := by
        by_contra h3
        have h4 : Real.arccos a ≤ Real.pi / 2 := by linarith
        have h5 : 0 ≤ a := (Real.arccos_le_pi_div_two).mp h4
        linarith
      have h3 : min (Real.arccos a) (Real.pi - Real.arccos a) = Real.pi - Real.arccos a := by
        rw [min_eq_right] <;> linarith
      rw [h3]
      have h4 : Real.sin (Real.pi - Real.arccos a) = Real.sin (Real.arccos a) := by
        rw [Real.sin_pi_sub]
      rw [h4]
      have h5 : Real.sin (Real.arccos a) ^ 2 = 1 - a ^ 2 := by
        have h6 : Real.sin (Real.arccos a) ^ 2 + Real.cos (Real.arccos a) ^ 2 = 1 := Real.sin_sq_add_cos_sq _
        have h7 : Real.cos (Real.arccos a) = a := Real.cos_arccos h_a_bound1 h_a_bound2
        rw [h7] at h6; linarith
      exact h5
  have h4 : ‖w - a • v‖ ^ 2 = (Real.sin α) ^ 2 := by rw [h_norm_sq, h_sin_sq]
  have h5 : 0 ≤ ‖w - a • v‖ := by positivity
  have h6 : 0 ≤ Real.sin α := by
    have h7 : 0 ≤ α := hα_nonneg
    have h8 : α ≤ Real.pi := by
      rw [hα_eq]
      have h9 : Real.arccos a ≤ Real.pi := Real.arccos_le_pi a
      exact min_le_iff.mpr (Or.inl h9)
    exact Real.sin_nonneg_of_mem_Icc ⟨h7, h8⟩
  have h7 : ‖w - a • v‖ = Real.sin α := by nlinarith
  by_cases hα : α = 0
  · rw [h7, hα]; simp [hdelta]
  · have hα_pos : 0 < α := by
      exact lt_of_le_of_ne hα_nonneg (Ne.symm hα)
    have h8 : Real.sin α < α := Real.sin_lt hα_pos
    rw [h7] <;> linarith

/-- Orthogonal decomposition: x - (inner x v) • v is perpendicular to unit v. -/
private lemma orthogonal_decomp {v x : Point3} (hv : ‖v‖ = 1) :
    inner ℝ (x - (inner ℝ x v) • v) v = 0 := by
  have h1 : inner ℝ (x - (inner ℝ x v) • v) v =
      inner ℝ x v - inner ℝ ((inner ℝ x v) • v) v := by
    rw [inner_sub_left] <;> rfl
  rw [h1]
  have h21 : inner ℝ ((inner ℝ x v) • v) v = (inner ℝ x v) * inner ℝ v v := by
    rw [inner_smul_left] <;> simp <;> ring
  have h22 : inner ℝ v v = ‖v‖ ^ 2 := by
    simpa [inner_self_eq_norm_sq_to_K] using rfl
  have h2 : inner ℝ ((inner ℝ x v) • v) v = inner ℝ x v := by
    rw [h21, h22, hv] <;> ring
  rw [h2] <;> ring

/-- unitSegment is compact. -/
private lemma unitSegment_compact {base direction : Point3} :
    IsCompact (Kakeya.unitSegment base direction) := by
  apply IsCompact.image isCompact_Icc
  exact continuous_const.add (continuous_id.smul continuous_const)

/-- unitSegment is nonempty. -/
private lemma unitSegment_nonempty {base direction : Point3} :
    (Kakeya.unitSegment base direction).Nonempty := by
  refine ⟨base, ?_⟩
  simp [Kakeya.unitSegment]; exact ⟨0, by norm_num, by simp⟩

/-- A point in cthickening of a compact set is within distance r of some point in the set. -/
private lemma exists_dist_le_of_mem_cthickening {x : Point3} {s : Set Point3}
    (hs : IsCompact s) (hne : s.Nonempty) {r : ℝ} (hr : 0 ≤ r)
    (hx : x ∈ Metric.cthickening r s) :
    ∃ y ∈ s, dist x y ≤ r := by
  rcases hs.exists_infEDist_eq_edist hne x with ⟨y, hy, h_eq⟩
  have h1 : infEDist x s ≤ ENNReal.ofReal r := (Metric.mem_cthickening_iff).mp hx
  rw [h_eq] at h1
  have h2 : edist x y = ENNReal.ofReal (dist x y) := by
    simp [edist_dist]
  rw [h2] at h1
  exact ⟨y, hy, (ENNReal.ofReal_le_ofReal_iff hr).mp h1⟩

/-- Linear isometry equiv image commutes with cthickening. -/
private lemma linearIsometryEquiv_image_cthickening (e : Point3 ≃ₗᵢ[ℝ] Point3)
    {r : ℝ} {s : Set Point3} :
    e '' (Metric.cthickening r s) = Metric.cthickening r (e '' s) := by
  ext z
  simp only [Set.mem_image, Metric.mem_cthickening_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have h_inf : infEDist (e x) (e '' s) = infEDist x s :=
      Metric.infEDist_image (hΦ := e.isometry)
    rw [h_inf]; exact hx
  · intro hz
    refine ⟨e.symm z, ?_, e.apply_symm_apply z⟩
    have h_inf : infEDist (e (e.symm z)) (e '' s) = infEDist (e.symm z) s :=
      Metric.infEDist_image (hΦ := e.isometry)
    have h3 : e (e.symm z) = z := e.apply_symm_apply z
    rw [h3] at h_inf
    rw [h_inf] at hz
    exact hz

/-- Translation commutes with cthickening. -/
private lemma translation_image_cthickening (c : Point3) (r : ℝ) (s : Set Point3) :
    Metric.cthickening r ((fun x : Point3 => x + c) '' s) =
    (fun x : Point3 => x + c) '' Metric.cthickening r s := by
  let transl : Point3 → Point3 := fun x => x + c
  have h_iso : Isometry transl := by
    intro x y
    simp [transl, edist_dist, dist_eq_norm] <;> abel
  ext z
  simp only [Set.mem_image, Metric.mem_cthickening_iff]
  constructor
  · intro hz
    have hz' : infEDist z (transl '' s) ≤ ENNReal.ofReal r := by
      simpa [transl] using hz
    have h' : transl (z - c) = z := by
      simp [transl] <;> abel
    have h'' : infEDist (transl (z - c)) (transl '' s) = infEDist (z - c) s :=
      Metric.infEDist_image (hΦ := h_iso) (x := z - c) (t := s)
    have h_goal : infEDist z (transl '' s) = infEDist (z - c) s := by
      rw [h'] at h''; exact h''
    rw [h_goal] at hz'
    exact ⟨z - c, hz', by simp [transl] <;> abel⟩
  · rintro ⟨y, hy, rfl⟩
    have h : infEDist (transl y) (transl '' s) = infEDist y s :=
      Metric.infEDist_image (hΦ := h_iso) (x := y) (t := s)
    have h_goal : infEDist (transl y) (transl '' s) ≤ ENNReal.ofReal r := by
      rw [h]; exact hy
    simpa [transl] using h_goal

/-- Volume is translation-invariant. -/
private lemma translation_volume (c : Point3) (s : Set Point3) :
    MeasureTheory.volume ((fun x : Point3 => x + c) '' s) = MeasureTheory.volume s := by
  let f : Point3 ≃ᵐ Point3 :=
    { toFun := fun x : Point3 => x + c
      invFun := fun x : Point3 => x - c
      left_inv := by intro x; simp
      right_inv := by intro x; simp
      measurable_toFun := (continuous_id.add continuous_const).measurable
      measurable_invFun := (continuous_id.sub continuous_const).measurable }
  have h_mp : MeasurePreserving f volume volume := by
    have h : MeasurePreserving (fun x : Point3 => c + x) volume volume :=
      measurePreserving_add_left volume c
    convert h using 1
    <;> funext x <;> exact add_comm x c
  have h4 : f ⁻¹' (f '' s) = s := by
    ext x; simp [f.injective] <;> tauto
  have h5 : volume (f ⁻¹' (f '' s)) = volume (f '' s) := h_mp.measure_preimage_equiv (f '' s)
  rw [h4] at h5
  have h6 : volume (f '' s) = volume s := h5.symm
  simpa [f] using h6

/-- Volume of δ-thickening of unit segment in direction v equals deltaTubeVolume δ. -/
private lemma volume_unitSegment_eq_deltaTubeVolume {δ : ℝ} (hdelta : 0 < δ)
    {v : Point3} (hv : ‖v‖ = 1) :
    MeasureTheory.volume (Metric.cthickening δ (Kakeya.unitSegment 0 v)) =
    Kakeya.deltaTubeVolume δ := by
  let e0 : Point3 := EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
  have he0 : ‖e0‖ = 1 := by simp [e0]
  have hnorm : ‖v‖ = ‖e0‖ := by rw [hv, he0]
  let A : Point3 ≃ₗᵢ[ℝ] Point3 := Submodule.reflection (ℝ ∙ (v - e0))ᗮ
  have hA1 : A v = e0 := Submodule.reflection_sub hnorm
  have hA2 : A e0 = v := by
    have h_refl : A * A = 1 := Submodule.reflection_mul_reflection (K := (ℝ ∙ (v - e0))ᗮ)
    have h1 : A (A v) = v := by
      have h2 : (A * A) v = v := by rw [h_refl] <;> simp
      exact h2
    have h3 : A (A v) = A e0 := by rw [hA1]
    rw [h3] at h1; exact h1
  have h_seg : A '' (Kakeya.unitSegment 0 v) = Kakeya.unitSegment 0 e0 := by
    ext y
    simp only [Set.mem_image, Kakeya.unitSegment]
    constructor
    · rintro ⟨x, ⟨t, ht, hx⟩, rfl⟩
      have h_x : x = t • v := by simpa using hx.symm
      rw [h_x]
      refine ⟨t, ht, ?_⟩
      have h : A (t • v) = t • e0 := by
        calc A (t • v) = t • A v := A.map_smul t v
          _ = t • e0 := by rw [hA1]
      simpa using h.symm
    · rintro ⟨t, ht, rfl⟩
      refine ⟨t • v, ⟨t, ht, by simp⟩, ?_⟩
      have h : A (t • v) = t • e0 := by
        calc A (t • v) = t • A v := A.map_smul t v
          _ = t • e0 := by rw [hA1]
      simpa using h
  let s : Set Point3 := Metric.cthickening δ (Kakeya.unitSegment 0 v)
  have h_cthick : A '' s = Metric.cthickening δ (Kakeya.unitSegment 0 e0) := by
    rw [linearIsometryEquiv_image_cthickening A, h_seg]
  have h_meas : MeasurableSet s := Metric.isClosed_cthickening.measurableSet
  have h_eq : A '' s = A.symm ⁻¹' s := by
    ext z
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hz
      refine ⟨A.symm z, hz, A.apply_symm_apply z⟩
  have h_map : Measure.map A.symm volume = volume := A.symm.measurePreserving.map_eq
  have h : volume (A '' s) = volume s := by
    rw [h_eq]
    have h2 : Measure.map A.symm volume s = volume (A.symm ⁻¹' s) :=
      Measure.map_apply A.symm.continuous.measurable h_meas
    rw [←h2, h_map]
  rw [h_cthick] at h
  exact h.symm

lemma conflicting_tubes_contained_in_convex_set
    {δ : ℝ} (hdelta : 0 < δ) (hδ_half : δ ≤ 1 / 2)
    (T : Kakeya.DeltaTube δ) (hT_ball : T.IsInUnitBall) :
    ∃ (W : Set Point3),
      Convex ℝ W ∧
      W ⊆ Kakeya.DeltaTube.unitBall ∧
      MeasureTheory.volume W ≤ 125 * Kakeya.deltaTubeVolume δ ∧
      ∀ (U : Kakeya.DeltaTube δ), U.IsInUnitBall →
        T.carrier ∩ U.carrier ≠ ∅ →
        hairbrushAcuteAngle T U < δ →
        U.carrier ⊆ W := by
  let v := T.direction
  have hv : ‖v‖ = 1 := T.direction_unit

  -- Length-5 segment S from T.base - 2v to T.base + 3v
  let c : Point3 := T.base - 2 • v
  let S : Set Point3 := Kakeya.unitSegment c ((5 : ℝ) • v)
  let W : Set Point3 := Kakeya.DeltaTube.unitBall ∩ Metric.cthickening (5 * δ) S

  have hS_nonempty : S.Nonempty := unitSegment_nonempty
  have hS_compact : IsCompact S := unitSegment_compact

  refine' ⟨W, _ , _ , _ , _⟩

  -- 1. Convexity of W
  · have hS_conv : Convex ℝ S := by
      let d : Point3 := (5 : ℝ) • v
      intro x hx y hy a b ha hb hab
      rcases hx with ⟨s, hs, rfl⟩
      rcases hy with ⟨t, ht, rfl⟩
      let u := a * s + b * t
      have hu : u ∈ Set.Icc (0 : ℝ) 1 := (convex_Icc 0 1) hs ht ha hb hab
      refine ⟨u, hu, ?_⟩
      have h1 : a • c + b • c = c := by
        have h2 : a • c + b • c = (a + b) • c := (add_smul a b c).symm
        rw [h2, hab] <;> simp
      have h3 : a • (s • d) = (a * s) • d := by rw [smul_smul] <;> ring
      have h4 : b • (t • d) = (b * t) • d := by rw [smul_smul] <;> ring
      have h5 : (a * s) • d + (b * t) • d = u • d := by
        have h6 : (a * s) • d + (b * t) • d = ((a * s) + (b * t)) • d :=
          (add_smul (a * s) (b * t) d).symm
        rw [h6] <;> rfl
      have hcalc : a • (c + s • d) + b • (c + t • d) = c + u • d := by
        calc
          a • (c + s • d) + b • (c + t • d)
            = a • c + a • (s • d) + (b • c + b • (t • d)) := by
              rw [smul_add, smul_add] <;> abel
          _ = a • c + b • c + ((a * s) • d + (b * t) • d) := by
              rw [h3, h4] <;> abel
          _ = c + u • d := by rw [h1, h5] <;> abel
      exact hcalc.symm
    have hthick_conv : Convex ℝ (Metric.cthickening (5 * δ) S) := hS_conv.cthickening (5 * δ)
    have hball_conv : Convex ℝ Kakeya.DeltaTube.unitBall := convex_closedBall 0 1
    exact hball_conv.inter hthick_conv

  -- 2. W ⊆ unitBall
  · exact Set.inter_subset_left

  -- 3. volume W ≤ 125 * deltaTubeVolume δ
  · let S0 : Set Point3 := Kakeya.unitSegment 0 v
    let scale : Point3 → Point3 := fun x => (5 : ℝ) • x
    let transl : Point3 → Point3 := fun x => x + c

    have hS_eq : S = transl '' (scale '' S0) := by
      ext x
      simp only [S, S0, Kakeya.unitSegment, Set.mem_image, transl, scale]
      constructor
      · rintro ⟨t, ht, rfl⟩
        refine ⟨(5 : ℝ) • (t • v), ⟨t • v, ⟨t, ht, by simp⟩, rfl⟩, ?_⟩
        have h_eq : (5 : ℝ) • (t • v) = t • ((5 : ℝ) • v) := by
          rw [smul_smul, smul_smul] <;> ring
        have h : (5 : ℝ) • (t • v) + c = c + t • ((5 : ℝ) • v) := by
          rw [h_eq] <;> abel
        exact h
      · rintro ⟨z, ⟨y, ⟨s, hs, hy⟩, rfl⟩, rfl⟩
        have h_y : y = s • v := by simpa using hy.symm
        refine ⟨s, hs, ?_⟩
        have h_eq : (5 : ℝ) • y = s • ((5 : ℝ) • v) := by
          rw [h_y, smul_smul, smul_smul] <;> ring
        rw [h_eq] <;> abel

    have hthick_eq : Metric.cthickening (5 * δ) S =
        transl '' (scale '' Metric.cthickening δ S0) := by
      rw [hS_eq]
      rw [translation_image_cthickening c (5 * δ) (scale '' S0)]
      have h_goal : Metric.cthickening (5 * δ) (scale '' S0) = scale '' Metric.cthickening δ S0 := by
        have h_scale := Kakeya.Streamlined.GeometricLemmas.cthickening_smul_point3
          (hL := show (0 : ℝ) < 5 by norm_num) (r := 5 * δ) (s := S0)
        have h_div : (5 * δ) / 5 = δ := by ring
        simpa [scale, h_div] using h_scale
      rw [h_goal]

    have hvol1 : MeasureTheory.volume (Metric.cthickening (5 * δ) S) =
        125 * MeasureTheory.volume (Metric.cthickening δ S0) := by
      rw [hthick_eq]
      have h_trans_vol : MeasureTheory.volume (transl '' (scale '' Metric.cthickening δ S0)) =
          MeasureTheory.volume (scale '' Metric.cthickening δ S0) :=
        translation_volume c (scale '' Metric.cthickening δ S0)
      rw [h_trans_vol]
      have h_smul_vol := Kakeya.Streamlined.GeometricLemmas.volume_smul3
        (hL := show (0 : ℝ) < 5 by norm_num) (s := Metric.cthickening δ S0)
      rw [h_smul_vol] <;> norm_num

    have hvol2 : MeasureTheory.volume (Metric.cthickening δ S0) = Kakeya.deltaTubeVolume δ :=
      volume_unitSegment_eq_deltaTubeVolume hdelta hv

    have hW_sub : W ⊆ Metric.cthickening (5 * δ) S := Set.inter_subset_right
    have h : MeasureTheory.volume W ≤ MeasureTheory.volume (Metric.cthickening (5 * δ) S) :=
      MeasureTheory.measure_mono hW_sub
    rw [hvol1, hvol2] at h
    exact h

  -- 4. ∀ U, ... U.carrier ⊆ W
  · intro U hU_ball h_inter h_angle
    let w := U.direction
    have hw : ‖w‖ = 1 := U.direction_unit
    let a : ℝ := inner ℝ w v
    have htrans : ‖w - a • v‖ < δ :=
      acute_angle_transverse_norm hdelta hv hw h_angle

    rcases Set.nonempty_iff_ne_empty.mpr h_inter with ⟨p, hp⟩

    rcases exists_dist_le_of_mem_cthickening unitSegment_compact unitSegment_nonempty hdelta.le hp.1 with
      ⟨p_T, hpT_seg, hdist_pT⟩
    rcases exists_dist_le_of_mem_cthickening unitSegment_compact unitSegment_nonempty hdelta.le hp.2 with
      ⟨p_U, hpU_seg, hdist_pU⟩

    have h1 : dist p_U p ≤ δ := by rw [dist_comm]; exact hdist_pU
    have h2 : dist p p_T ≤ δ := hdist_pT
    have h_d : dist p_U p_T ≤ 2 * δ := by
      calc dist p_U p_T ≤ dist p_U p + dist p p_T := dist_triangle _ _ _
        _ ≤ δ + δ := by gcongr
        _ = 2 * δ := by ring

    rcases hpT_seg with ⟨s, hs, rfl⟩
    rcases hpU_seg with ⟨t, ht, rfl⟩
    let p_T' := T.base + s • v
    let p_U' := U.base + t • w

    intro x hx
    rcases exists_dist_le_of_mem_cthickening unitSegment_compact unitSegment_nonempty hdelta.le hx with
      ⟨q, hq_seg, hdist_xq⟩
    rcases hq_seg with ⟨u, hu, rfl⟩
    let q' := U.base + u • w
    let r : ℝ := u - t
    have hr_abs : |r| ≤ 1 := by
      have h3 : 0 ≤ t := ht.1; have h4 : t ≤ 1 := ht.2
      have h5 : 0 ≤ u := hu.1; have h6 : u ≤ 1 := hu.2
      simp [r, abs_le] <;> constructor <;> linarith

    let d : Point3 := p_U' - p_T'
    have hd_norm : ‖d‖ ≤ 2 * δ := by simpa [d, dist_eq_norm] using h_d
    let d_axial : ℝ := inner ℝ d v
    let d_perp : Point3 := d - d_axial • v

    have h_d_perp_orth : inner ℝ d_perp v = 0 := orthogonal_decomp hv
    have hd_perp_orth : inner ℝ (d_axial • v) d_perp = 0 := by
      have h1' : inner ℝ v d_perp = 0 := by
        have h_comm : inner ℝ v d_perp = inner ℝ d_perp v := (real_inner_comm v d_perp).symm
        rw [h_comm, h_d_perp_orth]
      rw [inner_smul_left, h1'] <;> ring

    have hd_perp_norm2 : ‖d_perp‖ ^ 2 = ‖d‖ ^ 2 - d_axial ^ 2 := by
      have h5 : d = d_axial • v + d_perp := by simp [d_axial, d_perp] <;> abel
      rw [h5]
      have h6 : ‖d_axial • v + d_perp‖ ^ 2 = ‖d_axial • v‖ ^ 2 + ‖d_perp‖ ^ 2 := by
        have h7 := norm_add_sq_eq_norm_sq_add_norm_sq_real hd_perp_orth
        simpa [sq] using h7
      rw [h6]
      have h8 : ‖d_axial • v‖ ^ 2 = d_axial ^ 2 := by
        rw [norm_smul, hv] <;> simp [sq_abs] <;> ring
      rw [h8] <;> ring

    have hd_axial_abs : |d_axial| ≤ ‖d‖ := by
      have h : |d_axial| ≤ ‖d‖ * ‖v‖ := abs_real_inner_le_norm d v
      rw [hv] at h
      simpa using h
    have hd_perp_le2 : ‖d_perp‖ ≤ 2 * δ := by
      have h1 : ‖d_perp‖ ^ 2 ≤ ‖d‖ ^ 2 := by
        rw [hd_perp_norm2]
        have h2 : d_axial ^ 2 ≥ 0 := by positivity
        linarith
      have h3 : 0 ≤ ‖d_perp‖ := by positivity
      have h4 : 0 ≤ ‖d‖ := by positivity
      have h5 : ‖d_perp‖ ≤ ‖d‖ := by nlinarith
      have h6 : ‖d‖ ≤ 2 * δ := hd_norm
      linarith

    let w_perp : Point3 := w - a • v
    have hw_perp_orth : inner ℝ w_perp v = 0 := orthogonal_decomp hv

    let q_perp : Point3 := d_perp + r • w_perp
    have hq_perp_orth : inner ℝ q_perp v = 0 := by
      have h1 : inner ℝ q_perp v = inner ℝ d_perp v + inner ℝ (r • w_perp) v := by
        rw [inner_add_left] <;> rfl
      rw [h1]
      have h2 : inner ℝ (r • w_perp) v = r * inner ℝ w_perp v := by
        rw [inner_smul_left] <;> simp <;> ring
      rw [h2, h_d_perp_orth, hw_perp_orth] <;> ring

    have hq_perp_norm : ‖q_perp‖ < 3 * δ := by
      have h1 : ‖q_perp‖ ≤ ‖d_perp‖ + ‖r • w_perp‖ := norm_add_le _ _
      have h2 : ‖r • w_perp‖ = |r| * ‖w_perp‖ := by
        rw [norm_smul, Real.norm_eq_abs] <;> ring
      have h3 : ‖d_perp‖ ≤ 2 * δ := hd_perp_le2
      have h4 : |r| ≤ 1 := hr_abs
      have h5 : ‖w_perp‖ < δ := htrans
      have h6 : |r| * ‖w_perp‖ < δ := by
        calc |r| * ‖w_perp‖ ≤ 1 * ‖w_perp‖ := by gcongr
          _ < δ := by linarith
      rw [h2] at h1
      linarith

    let lam : ℝ := s + d_axial + r * a

    have hq_decomp : q' = T.base + lam • v + q_perp := by
      have h11 : p_T' + d + r • w = p_U' + r • w := by
        dsimp only [d, p_T', p_U'] <;> abel
      have h12 : p_U' + r • w = q' := by
        dsimp only [p_U', q', r]
        have h : (U.base + t • w) + (u - t) • w = U.base + u • w := by
          have h2 : (t • w) + (u - t) • w = (t + (u - t)) • w := by rw [← add_smul]
          have h3 : (U.base + t • w) + (u - t) • w = U.base + ((t • w) + (u - t) • w) := by abel
          rw [h3, h2]
          have h4 : t + (u - t) = u := by abel
          rw [h4] <;> abel
        exact h
      have h1 : q' = p_T' + d + r • w := by
        rw [h11, h12]
      have h2 : d = d_axial • v + d_perp := by
        dsimp only [d_axial, d_perp] <;> abel
      have h3 : w = a • v + w_perp := by
        dsimp only [w_perp] <;> abel
      rw [h1, h2, h3]
      have h4 : p_T' + (d_axial • v + d_perp) + r • (a • v + w_perp) =
          T.base + (s + d_axial + r * a) • v + (d_perp + r • w_perp) := by
        have h5 : p_T' = T.base + s • v := by rfl
        rw [h5]
        have h6 : r • (a • v + w_perp) = r • (a • v) + r • w_perp := by rw [smul_add]
        rw [h6]
        have h7 : r • (a • v) = (r * a) • v := by rw [smul_smul]
        rw [h7]
        have h8 : T.base + s • v + (d_axial • v + d_perp) + ((r * a) • v + r • w_perp) =
            T.base + (s + d_axial + r * a) • v + (d_perp + r • w_perp) := by
          have h81 : s • v + d_axial • v + (r * a) • v = (s + d_axial + r * a) • v := by
            have h1 : s • v + d_axial • v = (s + d_axial) • v := by rw [← add_smul]
            rw [h1]
            have h2 : (s + d_axial) • v + (r * a) • v = ((s + d_axial) + (r * a)) • v := by rw [← add_smul]
            rw [h2] <;> ring
          have h_comm : T.base + s • v + (d_axial • v + d_perp) + ((r * a) • v + r • w_perp) =
              T.base + (s • v + d_axial • v + (r * a) • v) + (d_perp + r • w_perp) := by abel
          rw [h_comm, h81] <;> rfl
        exact h8
      simpa [lam, q_perp] using h4

    have hlam_bounds : -1 - 2 * δ ≤ lam ∧ lam ≤ 2 + 2 * δ := by
      have h1 : 0 ≤ s := hs.1; have h2 : s ≤ 1 := hs.2
      have ha_abs : |a| ≤ 1 := by
        have h : |inner ℝ w v| ≤ ‖w‖ * ‖v‖ := abs_real_inner_le_norm w v
        rw [hv, hw] at h
        simpa [a] using h
      have h3 : -2 * δ ≤ d_axial := by
        have h4 : |d_axial| ≤ 2 * δ := by linarith [hd_axial_abs, hd_norm]
        simpa using (abs_le.mp h4).1
      have h4 : d_axial ≤ 2 * δ := by
        have h5 : |d_axial| ≤ 2 * δ := by linarith [hd_axial_abs, hd_norm]
        simpa using (abs_le.mp h5).2
      have h5 : -1 ≤ r * a := by
        have h6 : |r * a| ≤ 1 := by
          calc |r * a| = |r| * |a| := by rw [abs_mul]
            _ ≤ 1 * 1 := by gcongr <;> linarith [hr_abs, ha_abs]
            _ = 1 := by ring
        exact (abs_le.mp h6).1
      have h6 : r * a ≤ 1 := by
        have h7 : |r * a| ≤ 1 := by
          calc |r * a| = |r| * |a| := by rw [abs_mul]
            _ ≤ 1 * 1 := by gcongr <;> linarith [hr_abs, ha_abs]
            _ = 1 := by ring
        exact (abs_le.mp h7).2
      constructor <;> linarith

    -- With δ ≤ 1/2, lam ∈ [-2, 3] exactly matches S axial range
    have hlam_ge_minus2 : -2 ≤ lam := by linarith [hlam_bounds.1, hδ_half]
    have hlam_le_3 : lam ≤ 3 := by linarith [hlam_bounds.2, hδ_half]

    -- y = T.base + lam • v lies on S
    let y : Point3 := T.base + lam • v
    have hy_mem : y ∈ S := by
      simp only [S, Kakeya.unitSegment, y, c]
      refine ⟨(lam + 2) / 5, ?_⟩
      constructor
      · constructor <;> linarith
      · have h1 : ((lam + 2) / 5) • ((5 : ℝ) • v) = (lam + 2) • v := by
          rw [smul_smul]
          have h2 : ((lam + 2) / 5) * (5 : ℝ) = lam + 2 := by ring
          rw [h2]
        have h_goal : T.base + lam • v = (T.base - 2 • v) + ((lam + 2) / 5) • ((5 : ℝ) • v) := by
          rw [h1]
          have h4 : (T.base - 2 • v) + (lam + 2) • v = T.base + ((lam + 2) • v - 2 • v) := by
            simp [sub_eq_add_neg] <;> abel
          rw [h4]
          have h5 : (lam + 2) • v - 2 • v = lam • v := by
            have h51 : (lam + 2) • v = lam • v + 2 • v := by
              rw [add_smul] <;> norm_cast
            rw [h51]
            simp
          rw [h5] <;> rfl
        exact h_goal.symm

    have hdist_y : dist q' y = ‖q_perp‖ := by
      rw [hq_decomp, dist_eq_norm]
      have h5 : (T.base + lam • v + q_perp) - (T.base + lam • v) = q_perp := by abel
      rw [h5]

    have hdist_qS : infDist q' S ≤ 3 * δ := by
      have h6 : infDist q' S ≤ dist q' y := Metric.infDist_le_dist_of_mem hy_mem
      rw [hdist_y] at h6
      linarith [hq_perp_norm]

    have hdist_xS : infDist x S ≤ 5 * δ := by
      have h : infDist x S ≤ infDist q' S + dist x q' := Metric.infDist_le_infDist_add_dist
      have h2 : infDist q' S + dist x q' ≤ 3 * δ + δ := by gcongr
      have h3 : 3 * δ + δ = 4 * δ := by ring
      rw [h3] at h2
      linarith

    have hne : S.Nonempty := hS_nonempty
    have h4 : infEDist x S ≠ ⊤ := Metric.infEDist_ne_top hne
    have h5 : (infEDist x S).toReal = infDist x S := by rfl
    have h6 : infEDist x S = ENNReal.ofReal (infDist x S) := by
      rw [← h5, ENNReal.ofReal_toReal h4]
    have h_infEDist : infEDist x S ≤ ENNReal.ofReal (5 * δ) := by
      rw [h6]
      exact ENNReal.ofReal_le_ofReal_iff (by positivity) |>.mpr (by linarith)

    have h_in_cthick : x ∈ Metric.cthickening (5 * δ) S :=
      (Metric.mem_cthickening_iff).mpr h_infEDist

    have h_in_ball : x ∈ Kakeya.DeltaTube.unitBall := hU_ball hx
    exact ⟨h_in_ball, h_in_cthick⟩

end Kakeya.Assouad
