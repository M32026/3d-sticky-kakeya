import MyLeanRepo.Kakeya.Assouad.LargeSlope.GlobalADVolumeBound
import MyLeanRepo.Kakeya.Assouad.Definitions
import MyLeanRepo.Kakeya.Assouad.MultiplicityRefinement
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod

/-!
# AD-based volume bound for the horizontal slab

Using the global AD projection bound on each horizontal slice, bound the
3D volume of `Y.union ∩ horizontalSlab a b` by `16 C δ^σ (b-a)`.
-/

noncomputable section

open MeasureTheory Set Metric

namespace Kakeya.Assouad

/-- Projection-area bound in a radius-`R` disk for a non-unit projection
vector of norm at least one. -/
lemma area_le_projection_nonunit_radius
    {S : Set (Fin 2 → ℝ)} {w : Fin 2 → ℝ}
    {R : ℝ} (hR : 0 ≤ R)
    (hS : ∀ x ∈ S, x 0 ^ 2 + x 1 ^ 2 ≤ R ^ 2)
    (hnorm : 1 ≤ w 0 ^ 2 + w 1 ^ 2)
    {M : ENNReal}
    (hproj : volume ((fun x : Fin 2 → ℝ => x 0 * w 0 + x 1 * w 1) '' S) ≤ M) :
    volume S ≤ ENNReal.ofReal (2 * R) * M := by
  let norm : ℝ := Real.sqrt (w 0 ^ 2 + w 1 ^ 2)
  have hnorm_pos : 0 < norm := by
    have h : 0 < w 0 ^ 2 + w 1 ^ 2 := by linarith
    exact Real.sqrt_pos.mpr h
  let v : Fin 2 → ℝ := fun i => w i / norm
  have h_norm_sq : norm ^ 2 = w 0 ^ 2 + w 1 ^ 2 := by
    rw [Real.sq_sqrt (by positivity)]
  have hv_unit : v 0 ^ 2 + v 1 ^ 2 = 1 := by
    dsimp only [v]
    field_simp [hnorm_pos.ne', h_norm_sq] <;> nlinarith
  let proj_w : Set ℝ := (fun x : Fin 2 → ℝ => x 0 * w 0 + x 1 * w 1) '' S
  let proj_v : Set ℝ := (fun x : Fin 2 → ℝ => x 0 * v 0 + x 1 * v 1) '' S
  have hscale : proj_v = (fun t : ℝ => t / norm) '' proj_w := by
    ext t
    simp only [proj_v, proj_w, Set.mem_image]
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x 0 * w 0 + x 1 * w 1, ⟨x, hx, rfl⟩, ?_⟩
      dsimp only [v] <;> ring
    · rintro ⟨s, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨x, hx, ?_⟩
      dsimp only [v] <;> ring
  have hne : (norm : ℝ) ≠ 0 := hnorm_pos.ne'
  have hvol_scale : volume proj_v =
      ENNReal.ofReal (1 / norm) * volume proj_w := by
    rw [hscale]
    have h_img : (fun t : ℝ => t / norm) '' proj_w =
        (fun t : ℝ => norm * t) ⁻¹' proj_w := by
      ext y
      constructor
      · intro hy
        have h_exists : ∃ (t : ℝ), t ∈ proj_w ∧ t / norm = y := by
          simpa [Set.mem_image] using hy
        rcases h_exists with ⟨t, ht, h_eq⟩
        have h : norm * y = t := by
          have h' : y = t / norm := h_eq.symm
          rw [h']
          field_simp [hne] <;> ring
        have h_goal : norm * y ∈ proj_w := by
          rw [h] <;> exact ht
        exact Set.mem_preimage.mpr h_goal
      · intro h
        exact ⟨norm * y, h, by field_simp [hne] <;> ring⟩
    rw [h_img]
    rw [Real.volume_preimage_mul_left hne proj_w]
    have habs : |(norm : ℝ)⁻¹| = 1 / norm := by
      rw [abs_of_pos (by positivity : 0 < (norm : ℝ)⁻¹)]
      <;> field_simp [hne] <;> ring
    rw [habs]
  have h1 : volume proj_v ≤ volume proj_w := by
    rw [hvol_scale]
    have h2 : ENNReal.ofReal (1 / norm) ≤ 1 := by
      apply ENNReal.ofReal_le_one.mpr
      have h3 : 1 / norm ≤ 1 := by
        apply (div_le_one (by positivity)).mpr
        have h4 : 1 ≤ norm := by
          have h5 : 1 ≤ w 0 ^ 2 + w 1 ^ 2 := hnorm
          have h6 : 1 ≤ Real.sqrt (w 0 ^ 2 + w 1 ^ 2) := by
            rw [Real.le_sqrt] <;> nlinarith
          exact h6
        linarith
      exact h3
    calc
      ENNReal.ofReal (1 / norm) * volume proj_w
        ≤ (1 : ENNReal) * volume proj_w := by gcongr
      _ = volume proj_w := by simp
  have h4 : volume proj_v ≤ M := h1.trans hproj
  have h5 : volume S ≤ ENNReal.ofReal (2 * R) * volume proj_v :=
    area_le_two_projection hv_unit hR hS
  calc
    volume S
      ≤ ENNReal.ofReal (2 * R) * volume proj_v := h5
    _ ≤ ENNReal.ofReal (2 * R) * M := by gcongr

/-- Unit-disk compatibility wrapper. -/
lemma area_le_projection_nonunit {S : Set (Fin 2 → ℝ)} {w : Fin 2 → ℝ}
    (hS : ∀ x ∈ S, x 0 ^ 2 + x 1 ^ 2 ≤ 1)
    (hnorm : 1 ≤ w 0 ^ 2 + w 1 ^ 2)
    {M : ENNReal}
    (hproj : volume ((fun x : Fin 2 → ℝ => x 0 * w 0 + x 1 * w 1) '' S) ≤ M) :
    volume S ≤ 2 * M := by
  have h := area_le_projection_nonunit_radius (R := (1 : ℝ))
    (by norm_num) (by simpa using hS) hnorm hproj
  simpa using h

/--
Volume of the shaded union inside a horizontal slab, bounded using the
global AD condition on every horizontal slice.
-/
lemma volume_slab_union_le_global_ad
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {sigma : ℝ} {C : ENNReal}
    (G : C2GrainStructure Y sigma C)
    (hdelta : 0 < delta) (hsigma : 0 < sigma) (hsigma_one : sigma < 1)
    (hC_top : C ≠ ⊤)
    (hF_ball : F.IsInUnitBall)
    {a b : ℝ} (ha_left : -1 ≤ a) (ha : a ≤ b) (hb_right : b ≤ 1) :
    MeasureTheory.volume (Y.union ∩ horizontalSlab a b) ≤
      16 * C * Kakeya.realRpowENN delta sigma * ENNReal.ofReal (b - a) := by
  let slice2d (z : ℝ) : Set (Fin 2 → ℝ) :=
    {q | point3 (q 0) (q 1) z ∈ Y.union}

  have hY_union_meas : MeasurableSet Y.union := by
    have h : Y.union = ⋃ i : Fin F.card, Y.carrier i := by
      ext x
      simp only [Kakeya.Streamlined.Shading.union, Set.mem_setOf_eq, Set.mem_iUnion]
      <;> rfl
    rw [h]
    exact MeasurableSet.iUnion (fun i => Y.measurable_carrier i)

  have hY_in_ball : Y.union ⊆ Kakeya.DeltaTube.unitBall := by
    intro p hp
    rcases hp with ⟨i, hpi⟩
    have h1 : Y.carrier i ⊆ (F.tube i).carrier := Y.subset_body i
    have h2 : (F.tube i).carrier ⊆ Kakeya.DeltaTube.unitBall := hF_ball i
    exact h2 (h1 hpi)

  have hpoint3_coord : ∀ (x y z : ℝ) (i : Fin 3),
      (point3 x y z) i =
        x * (if i = 0 then (1 : ℝ) else 0) +
        y * (if i = 1 then (1 : ℝ) else 0) +
        z * (if i = 2 then (1 : ℝ) else 0) := by
    intro x y z i
    simp [point3, PiLp.single_apply]
    <;> ring

  have hpoint3_apply : ∀ (x y z : ℝ),
      (point3 x y z) 0 = x ∧ (point3 x y z) 1 = y ∧ (point3 x y z) 2 = z := by
    intro x y z
    have h0 := hpoint3_coord x y z 0
    have h1 := hpoint3_coord x y z 1
    have h2 := hpoint3_coord x y z 2
    simp at h0 h1 h2
    exact ⟨h0, h1, h2⟩

  have hinner_grain : ∀ (p : Point3) (m : ℝ),
      inner ℝ p (globalGrainDirection m) = p 0 + m * p 1 := by
    intro p m
    have h1 : inner ℝ p (globalGrainDirection m) =
        inner ℝ p (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) +
        inner ℝ p (m • EuclideanSpace.single (1 : Fin 3) (1 : ℝ)) := by
      rw [globalGrainDirection, inner_add_right]
    rw [h1]
    have h2 : inner ℝ p (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) = p 0 := by
      rw [EuclideanSpace.inner_single_right] <;> simp
    have h3 : inner ℝ p (m • EuclideanSpace.single (1 : Fin 3) (1 : ℝ)) = m * p 1 := by
      rw [inner_smul_right, EuclideanSpace.inner_single_right] <;> simp
    rw [h2, h3] <;> ring

  have hproj_eq : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      (fun q : Fin 2 → ℝ => q 0 + G.slope z * q 1) '' slice2d z =
      scalarProjection (globalGrainDirection (G.slope z))
        (horizontalSlice Y.union z) := by
    intro z _
    ext t
    simp only [Set.mem_image, scalarProjection, horizontalSlice,
      slice2d, Set.mem_setOf_eq]
    constructor
    · rintro ⟨q, hq, rfl⟩
      let p : Point3 := point3 (q 0) (q 1) z
      have hp2 : p ∈ Y.union := hq
      have hz2 : p 2 = z := (hpoint3_apply (q 0) (q 1) z).2.2
      refine ⟨p, ⟨hp2, hz2⟩, ?_⟩
      have h : inner ℝ p (globalGrainDirection (G.slope z)) = p 0 + G.slope z * p 1 :=
        hinner_grain p (G.slope z)
      rw [h, (hpoint3_apply (q 0) (q 1) z).1, (hpoint3_apply (q 0) (q 1) z).2.1] <;> ring
    · rintro ⟨p, ⟨hp, hz2⟩, h_eq⟩
      let q : Fin 2 → ℝ := fun i =>
        match i with
        | 0 => p 0
        | 1 => p 1
      have hq2 : point3 (q 0) (q 1) z ∈ Y.union := by
        have h_eq2 : point3 (q 0) (q 1) z = p := by
          ext i
          fin_cases i <;> simp [q, hpoint3_apply, hz2] <;> rfl
        rw [h_eq2]; exact hp
      refine ⟨q, hq2, ?_⟩
      have h6 : p 0 + G.slope z * p 1 = t := by
        have h7 : inner ℝ p (globalGrainDirection (G.slope z)) = t := h_eq
        have h8 : inner ℝ p (globalGrainDirection (G.slope z)) = p 0 + G.slope z * p 1 :=
          hinner_grain p (G.slope z)
        rw [h8] at h7; exact h7
      simpa [q] using h6

  have hslice_area : ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      MeasureTheory.volume (slice2d z) ≤
        16 * C * Kakeya.realRpowENN delta sigma := by
    intro z hz
    have hAD : IsADSet1
        (scalarProjection (globalGrainDirection (G.slope z))
          (horizontalSlice Y.union z))
        delta (1 - sigma) C := G.global_ad z hz

    have hproj_meas : MeasureTheory.volume
        ((fun q : Fin 2 → ℝ => q 0 + G.slope z * q 1) '' slice2d z) ≤
        8 * C * Kakeya.realRpowENN delta sigma := by
      rw [hproj_eq z hz]
      exact IsADSet1.volume_le hdelta hsigma hsigma_one hC_top hAD

    let w : Fin 2 → ℝ := fun i =>
      match i with
      | 0 => 1
      | 1 => G.slope z

    have hnorm_ge_one : (1 : ℝ) ≤ w 0 ^ 2 + w 1 ^ 2 := by
      dsimp only [w] <;> nlinarith

    have hball : ∀ (x : Fin 2 → ℝ), x ∈ slice2d z →
        x 0 ^ 2 + x 1 ^ 2 ≤ 1 := by
      intro x hx
      let p : Point3 := point3 (x 0) (x 1) z
      have h_p_in : p ∈ Y.union := hx
      have h_unit : p ∈ Kakeya.DeltaTube.unitBall := hY_in_ball h_p_in
      have h_norm_le : ‖p‖ ≤ 1 := by
        simpa [Kakeya.DeltaTube.unitBall, Metric.mem_closedBall, dist_zero_right] using h_unit
      have h6 : ‖p‖ ^ 2 = ∑ i : Fin 3, ‖p i‖ ^ 2 :=
        PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => ℝ) p
      have h7 : ∑ i : Fin 3, ‖p i‖ ^ 2 = ∑ i : Fin 3, (p i) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        have h_abs : ‖p i‖ = |p i| := Real.norm_eq_abs _
        rw [h_abs, sq_abs]
      have h8 : ∑ i : Fin 3, (p i) ^ 2 = p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 := by
        simp [Fin.sum_univ_succ] <;> ring
      have h9 : p 0 = x 0 := (hpoint3_apply (x 0) (x 1) z).1
      have h10 : p 1 = x 1 := (hpoint3_apply (x 0) (x 1) z).2.1
      have h11 : p 2 = z := (hpoint3_apply (x 0) (x 1) z).2.2
      have h12 : ‖p‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + z ^ 2 := by
        calc
          ‖p‖ ^ 2 = ∑ i : Fin 3, ‖p i‖ ^ 2 := h6
          _ = ∑ i : Fin 3, (p i) ^ 2 := h7
          _ = p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 := h8
          _ = x 0 ^ 2 + x 1 ^ 2 + z ^ 2 := by rw [h9, h10, h11] <;> ring
      have h13 : ‖p‖ ^ 2 ≤ 1 := by
        have h14 : 0 ≤ ‖p‖ := norm_nonneg p
        nlinarith
      have h15 : x 0 ^ 2 + x 1 ^ 2 + z ^ 2 ≤ 1 := by
        rw [←h12] <;> exact h13
      have h16 : x 0 ^ 2 + x 1 ^ 2 ≤ 1 := by nlinarith [sq_nonneg z]
      exact h16

    have hproj_eq2 : (fun x : Fin 2 → ℝ => x 0 * w 0 + x 1 * w 1) =
        (fun q : Fin 2 → ℝ => q 0 + G.slope z * q 1) := by
      ext x
      dsimp only [w]
      <;> ring
    have hproj_meas' : volume ((fun x : Fin 2 → ℝ => x 0 * w 0 + x 1 * w 1) '' slice2d z) ≤
        8 * C * Kakeya.realRpowENN delta sigma := by
      rw [hproj_eq2]
      exact hproj_meas
    have h_result : volume (slice2d z) ≤ 2 * (8 * C * Kakeya.realRpowENN delta sigma) :=
      area_le_projection_nonunit hball hnorm_ge_one hproj_meas'
    have h_final : volume (slice2d z) ≤ 16 * C * Kakeya.realRpowENN delta sigma := by
      convert h_result using 1
      <;> ring
    exact h_final

  let E : Set Point3 := Y.union ∩ horizontalSlab a b
  have hE_meas : MeasurableSet E :=
    hY_union_meas.inter (measurableSet_horizontalSlab a b)

  let eLp : Point3 ≃ᵐ (Fin 3 → ℝ) :=
    { toFun := WithLp.ofLp
      invFun := WithLp.toLp 2
      left_inv := by intro x; exact WithLp.toLp_ofLp (2 : ENNReal) x
      right_inv := by intro x; exact WithLp.ofLp_toLp (2 : ENNReal) x
      measurable_toFun := (PiLp.continuous_ofLp (p := 2) (β := fun _ : Fin 3 => ℝ)).measurable
      measurable_invFun := (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 => ℝ)).measurable }

  let eSplit : (Fin 3 → ℝ) ≃ᵐ (ℝ × (Fin 2 → ℝ)) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2

  let e : Point3 ≃ᵐ (ℝ × (Fin 2 → ℝ)) := eLp.trans eSplit

  have hms_e : MeasurePreserving e volume volume := by
    have h1 : MeasurePreserving eLp volume volume :=
      PiLp.volume_preserving_ofLp (ι := Fin 3)
    have h2 : MeasurePreserving eSplit volume volume :=
      volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 2
    exact h2.comp h1

  let E'' : Set (ℝ × (Fin 2 → ℝ)) := e '' E
  have hE''_meas : MeasurableSet E'' :=
    e.measurableSet_image.mpr hE_meas

  have hvol : volume E = volume E'' := by
    have hpre : e ⁻¹' E'' = E := Set.preimage_image_eq E e.injective
    have h' : volume (e ⁻¹' E'') = volume E'' :=
      hms_e.measure_preimage_emb e.measurableEmbedding E''
    rw [hpre] at h'; exact h'

  have h_e_apply : ∀ (p : Point3),
      e p = (p 2, fun i : Fin 2 => p ((2 : Fin 3).succAbove i)) := by
    intro p; rfl

  have h_succ_eq : ∀ (j : Fin 2), (2 : Fin 3).succAbove j = j.castSucc := by
    intro j
    fin_cases j <;> simp [Fin.succAbove] <;> decide

  have h_to_eq : ∀ (z : ℝ) (q : Fin 2 → ℝ),
      e (point3 (q 0) (q 1) z) = (z, q) := by
    intro z q
    let p : Point3 := point3 (q 0) (q 1) z
    have h11 : p 2 = z := (hpoint3_apply (q 0) (q 1) z).2.2
    have h12 : (fun i : Fin 2 => p ((2 : Fin 3).succAbove i)) = q := by
      funext i
      have h_i0 : i = 0 ∨ i = 1 := by fin_cases i <;> tauto
      rcases h_i0 with (rfl | rfl)
      · have h_succ : (2 : Fin 3).succAbove (0 : Fin 2) = (0 : Fin 3) := by decide
        rw [h_succ]
        exact (hpoint3_apply (q 0) (q 1) z).1
      · have h_succ : (2 : Fin 3).succAbove (1 : Fin 2) = (1 : Fin 3) := by decide
        rw [h_succ]
        exact (hpoint3_apply (q 0) (q 1) z).2.1
    have h : e p = (p 2, fun i : Fin 2 => p ((2 : Fin 3).succAbove i)) := h_e_apply p
    rw [h, h11, h12]

  have h_from_eq : ∀ (p : Point3) (z : ℝ) (q : Fin 2 → ℝ),
      e p = (z, q) → p = point3 (q 0) (q 1) z := by
    intro p z q h_eq
    have h : e p = e (point3 (q 0) (q 1) z) := by
      rw [h_eq, h_to_eq z q]
    exact e.injective h

  have h_fiber_eq : ∀ (z : ℝ), z ∈ Set.Icc a b →
      {q : Fin 2 → ℝ | (z, q) ∈ E''} = slice2d z := by
    intro z hz
    ext q
    simp only [E'', Set.mem_image, Set.mem_setOf_eq, slice2d]
    constructor
    · rintro ⟨p, hp, h_eq⟩
      have h2 : p = point3 (q 0) (q 1) z := h_from_eq p z q h_eq
      rw [h2] at hp
      exact hp.1
    · intro hq
      have h7 : point3 (q 0) (q 1) z ∈ Y.union := hq
      have h_coord : (point3 (q 0) (q 1) z) 2 = z := (hpoint3_apply (q 0) (q 1) z).2.2
      have h8 : point3 (q 0) (q 1) z ∈ horizontalSlab a b := by
        simp only [horizontalSlab, Set.mem_setOf_eq]
        rw [h_coord]
        exact hz
      let p : Point3 := point3 (q 0) (q 1) z
      have hpE : p ∈ E := ⟨h7, h8⟩
      exact ⟨p, hpE, h_to_eq z q⟩

  have hfiber : ∀ (z : ℝ), z ∈ Set.Icc a b →
      volume {q : Fin 2 → ℝ | (z, q) ∈ E''} ≤
        16 * C * Kakeya.realRpowENN delta sigma := by
    intro z hz
    by_cases hz' : z ∈ Set.Icc (-1 : ℝ) 1
    · rw [h_fiber_eq z hz]
      exact hslice_area z hz'
    · have h_empty : {q : Fin 2 → ℝ | (z, q) ∈ E''} = ∅ := by
        ext q
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        intro h
        rcases h with ⟨p, hp, h_eq⟩
        have h2 : p = point3 (q 0) (q 1) z := h_from_eq p z q h_eq
        rw [h2] at hp
        have h3 : point3 (q 0) (q 1) z ∈ Y.union := hp.1
        have h4 : point3 (q 0) (q 1) z ∈ Kakeya.DeltaTube.unitBall := hY_in_ball h3
        have h5 : ‖point3 (q 0) (q 1) z‖ ≤ 1 := by
          simpa [Kakeya.DeltaTube.unitBall, Metric.mem_closedBall, dist_zero_right] using h4
        have h6 : |z| ≤ 1 := by
          let p' : Point3 := point3 (q 0) (q 1) z
          have h_norm_sq : ‖p'‖ ^ 2 = |p' 0| ^ 2 + |p' 1| ^ 2 + |p' 2| ^ 2 := by
            have h : ‖p'‖ ^ 2 = ∑ i : Fin 3, |p' i| ^ 2 :=
              PiLp.norm_sq_eq_of_L2 (fun _ => ℝ) p'
            rw [h]
            simp [Fin.sum_univ_succ] <;> ring
          have h_coord_sq : |p' 2| ^ 2 ≤ ‖p'‖ ^ 2 := by
            rw [h_norm_sq]
            have h1 : 0 ≤ |p' 0| ^ 2 := by positivity
            have h2 : 0 ≤ |p' 1| ^ 2 := by positivity
            linarith
          have h_coord_abs : |p' 2| ≤ ‖p'‖ := by
            nlinarith [abs_nonneg (p' 2), norm_nonneg p']
          have h8 : p' 2 = z := (hpoint3_apply (q 0) (q 1) z).2.2
          rw [h8] at h_coord_abs
          have h9 : |z| ≤ ‖p'‖ := h_coord_abs
          have h10 : ‖p'‖ ≤ 1 := h5
          linarith [abs_nonneg z]
        have h9 : z ∈ Set.Icc (-1 : ℝ) 1 := by
          exact ⟨by linarith [abs_le.mp h6], by linarith [abs_le.mp h6]⟩
        exact hz' h9
      rw [h_empty] <;> simp

  have hfiber_outside : ∀ (z : ℝ), z ∉ Set.Icc a b →
      volume {q : Fin 2 → ℝ | (z, q) ∈ E''} = 0 := by
    intro z hz
    have h_empty : {q : Fin 2 → ℝ | (z, q) ∈ E''} = ∅ := by
      ext q
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      rcases h with ⟨p, hp, h_eq⟩
      have h7 : p ∈ horizontalSlab a b := hp.2
      have h_coord : p.ofLp 2 = z := by
        have h9 : (e p).1 = p.ofLp 2 := by rfl
        have h10 : (e p).1 = z := by
          rw [h_eq] <;> rfl
        rw [h9] at h10
        exact h10
      have h11 : p.ofLp 2 ∈ Set.Icc a b := by
        simpa [horizontalSlab] using h7
      have h12 : z ∈ Set.Icc a b := by
        rw [←h_coord]; exact h11
      exact hz h12
    rw [h_empty] <;> simp

  have hvol_prod : (volume : Measure (ℝ × (Fin 2 → ℝ))) =
      (volume : Measure ℝ).prod (volume : Measure (Fin 2 → ℝ)) := by
    rfl

  have hmain : volume E'' ≤
      ENNReal.ofReal (b - a) * (16 * C * Kakeya.realRpowENN delta sigma) := by
    rw [hvol_prod]
    rw [MeasureTheory.Measure.prod_apply hE''_meas]
    let g : ℝ → ENNReal := fun z =>
      if z ∈ Set.Icc a b then (16 * C * Kakeya.realRpowENN delta sigma) else 0
    have hcmp : ∀ (z : ℝ), volume {q : Fin 2 → ℝ | (z, q) ∈ E''} ≤ g z := by
      intro z
      by_cases hz : z ∈ Set.Icc a b
      · have hgz : g z = 16 * C * Kakeya.realRpowENN delta sigma := by
          dsimp only [g]; rw [if_pos hz]
        rw [hgz]; exact hfiber z hz
      · have hgz : g z = 0 := by
          dsimp only [g]; rw [if_neg hz]
        rw [hgz]
        exact le_of_eq (hfiber_outside z hz)
    have h : ∫⁻ (z : ℝ), volume {q : Fin 2 → ℝ | (z, q) ∈ E''} ≤ ∫⁻ (z : ℝ), g z :=
      MeasureTheory.lintegral_mono hcmp
    have h2 : ∫⁻ (z : ℝ), g z =
        ENNReal.ofReal (b - a) * (16 * C * Kakeya.realRpowENN delta sigma) := by
      let K : ENNReal := 16 * C * Kakeya.realRpowENN delta sigma
      have hg : g = Set.indicator (Set.Icc a b) (fun _ : ℝ => K) := by
        funext z
        dsimp only [g]
        by_cases hz : z ∈ Set.Icc a b
        · rw [if_pos hz, Set.indicator_apply, if_pos hz]
        · rw [if_neg hz, Set.indicator_apply, if_neg hz]
      rw [hg]
      rw [MeasureTheory.lintegral_indicator measurableSet_Icc]
      rw [MeasureTheory.setLIntegral_const]
      rw [Real.volume_Icc]
      <;> ring
    rw [h2] at h
    exact h

  calc
    MeasureTheory.volume E
      = MeasureTheory.volume E'' := hvol
    _ ≤ ENNReal.ofReal (b - a) * (16 * C * Kakeya.realRpowENN delta sigma) := hmain
    _ = 16 * C * Kakeya.realRpowENN delta sigma * ENNReal.ofReal (b - a) := by ring

end Kakeya.Assouad
