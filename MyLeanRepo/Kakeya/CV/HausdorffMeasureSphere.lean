import MyLeanRepo.Kakeya.CV.HausdorffMeasureSphere.Fubini
import MyLeanRepo.Kakeya.CV.HausdorffMeasureSphere.Finite
import MyLeanRepo.Kakeya.CV.HausdorffMeasureSphere.CapBounds.Basic
import MyLeanRepo.Kakeya.CV.HausdorffMeasureSphere.CapBounds.MuHE


open MeasureTheory Metric Set Filter
open scoped ENNReal Pointwise Topology Pointwise
open Classical

namespace Kakeya.CV

noncomputable section


/-- μHE[2] of unit sphere equals toSphere univ. -/
theorem muHE_two_sphere_eq_toSphere :
    (μHE[2] : Measure (Point 3)) (unitSphere 3) =
    (volume : Measure (Point 3)).toSphere Set.univ := by
  have h_finite : (μHE[2] : Measure (Point 3)) (unitSphere 3) < ⊤ := muHE_two_sphere_finite
  let μ : Measure (Point 3) := (μHE[2] : Measure (Point 3)).restrict (unitSphere 3)
  let ν : Measure (Point 3) := Measure.map Subtype.val (volume.toSphere)
  have hμ_fin : IsFiniteMeasure μ := by
    constructor <;> simpa [μ] using h_finite
  have hν_fin : IsFiniteMeasure ν := by
    constructor
    simp [ν, MeasureTheory.Measure.toSphere_apply_univ]
    <;> exact ENNReal.ofReal_ne_top
  have hμ_support : μ Set.univ = μ (unitSphere 3) := by
    simp [μ, Measure.restrict_apply]
    <;> exact Set.inter_univ _
  have h_us_meas2 : MeasurableSet (unitSphere 3) := by
    simpa [unitSphere] using isClosed_sphere.measurableSet
  have h_preimage : (Subtype.val : {x : Point 3 // x ∈ unitSphere 3} → Point 3) ⁻¹' (unitSphere 3) = Set.univ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_univ, iff_true]
    exact x.prop
  have hν_support : ν Set.univ = ν (unitSphere 3) := by
    have h1 : ν Set.univ = (volume : Measure (Point 3)).toSphere Set.univ := by
      dsimp only [ν]
      rw [Measure.map_apply continuous_subtype_val.measurable] <;> simp
    have h2 : ν (unitSphere 3) = (volume : Measure (Point 3)).toSphere Set.univ := by
      dsimp only [ν]
      have h21 : ν (unitSphere 3) = (volume.toSphere) (Subtype.val ⁻¹' unitSphere 3) := by
        rw [Measure.map_apply continuous_subtype_val.measurable h_us_meas2] <;> rfl
      rw [h21]
      have h_preimage : (Subtype.val : ↥(sphere (0 : Point 3) 1) → Point 3) ⁻¹' (unitSphere 3) = Set.univ := by
        ext z
        simp only [Set.mem_preimage, Set.mem_univ, iff_true]
        simpa [unitSphere] using z.prop
      rw [h_preimage] <;> rfl
    rw [h1, h2]
  have hμ_inv : ∀ (f : Point 3 →ₗᵢ[ℝ] Point 3), ∀ (A : Set (Point 3)), MeasurableSet A → μ (f '' A) = μ A := by
    intro f A hA
    let e : Point 3 ≃ₗᵢ[ℝ] Point 3 := f.toLinearIsometryEquiv (by simp)
    let e_me : Point 3 ≃ᵐ Point 3 :=
      { toEquiv := e.toEquiv
        measurable_toFun := e.continuous.measurable
        measurable_invFun := e.symm.continuous.measurable }
    have h_e_eq_f : ∀ x, e x = f x := LinearIsometry.toLinearIsometryEquiv_apply f (by simp)
    have h_mp : MeasurePreserving e μHE[2] μHE[2] :=
      e.toIsometryEquiv.measurePreserving_euclideanHausdorffMeasure 2
    have h_f_img : f '' A = e '' A := by ext y; simp [h_e_eq_f]
    have hA' : MeasurableSet (f '' A) := by
      rw [h_f_img]
      exact e_me.measurableSet_image.mpr hA
    have h1 : e '' (A ∩ unitSphere 3) = (e '' A) ∩ unitSphere 3 := by
      ext y
      simp only [Set.mem_image, Set.mem_inter_iff]
      constructor
      · rintro ⟨x, ⟨hxA, hxS⟩, rfl⟩
        have h2 : e x ∈ unitSphere 3 := by
          have h3 : ‖e x‖ = ‖x‖ := e.norm_map x
          have h4 : ‖x‖ = 1 := by simpa [unitSphere, Metric.mem_sphere, dist_zero_right] using hxS
          have h5 : ‖e x‖ = 1 := by rw [h3, h4]
          simpa [unitSphere, Metric.mem_sphere, dist_zero_right] using h5
        exact ⟨Set.mem_image_of_mem e hxA, h2⟩
      · rintro ⟨hfyA, hfyS⟩
        rcases e.surjective y with ⟨x, rfl⟩
        have hxS : x ∈ unitSphere 3 := by
          have h3 : ‖e x‖ = ‖x‖ := e.norm_map x
          have h4 : ‖e x‖ = 1 := by simpa [unitSphere, Metric.mem_sphere, dist_zero_right] using hfyS
          have h5 : ‖x‖ = 1 := by rw [← h3, h4]
          simpa [unitSphere, Metric.mem_sphere, dist_zero_right] using h5
        have hxA : x ∈ A := by simpa using hfyA
        exact ⟨x, ⟨hxA, hxS⟩, rfl⟩
    have h2 : μ (f '' A) = μHE[2] ((f '' A) ∩ unitSphere 3) := by
      rw [Measure.restrict_apply hA'] <;> rfl
    have h_meas_set : MeasurableSet (A ∩ unitSphere 3) := hA.inter h_us_meas2
    have h_img_meas : MeasurableSet (e '' (A ∩ unitSphere 3)) :=
      e_me.measurableSet_image.mpr h_meas_set
    have h_goal1 : μHE[2] ((f '' A) ∩ unitSphere 3) = μHE[2] (A ∩ unitSphere 3) := by
      rw [h_f_img, ←h1]
      have h_map_eq : Measure.map e μHE[2] = μHE[2] := h_mp.map_eq
      have h3 : μHE[2] (e '' (A ∩ unitSphere 3)) = Measure.map e μHE[2] (e '' (A ∩ unitSphere 3)) := by rw [h_map_eq]
      rw [h3]
      have h4 : Measure.map e μHE[2] (e '' (A ∩ unitSphere 3)) = μHE[2] (e ⁻¹' (e '' (A ∩ unitSphere 3))) :=
        Measure.map_apply e.continuous.measurable h_img_meas
      rw [h4]
      have h5 : e ⁻¹' (e '' (A ∩ unitSphere 3)) = A ∩ unitSphere 3 :=
        Set.preimage_image_eq _ e.injective
      rw [h5]
    have h_goal2 : μ A = μHE[2] (A ∩ unitSphere 3) := by
      rw [Measure.restrict_apply hA] <;> rfl
    rw [h2, h_goal1, h_goal2]

  have hν_inv : ∀ (f : Point 3 →ₗᵢ[ℝ] Point 3), ∀ (A : Set (Point 3)), MeasurableSet A → ν (f '' A) = ν A := by
    intro f A hA
    let e : Point 3 ≃ₗᵢ[ℝ] Point 3 := f.toLinearIsometryEquiv (by simp)
    have h_e_eq_f : ∀ x, e x = f x := LinearIsometry.toLinearIsometryEquiv_apply f (by simp)
    have h_mp_vol : MeasurePreserving e volume volume := e.measurePreserving
    let SphereType := ↥(sphere (0 : Point 3) 1)
    let eₛ : SphereType ≃ₜ SphereType :=
      { toFun := fun x => ⟨e x, by
          have h2 : ‖e x‖ = ‖(x : Point 3)‖ := e.norm_map x
          have h3 : ‖(x : Point 3)‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using x.prop
          have h4 : ‖e x‖ = 1 := by rw [h2, h3]
          simpa [Metric.mem_sphere, dist_zero_right] using h4⟩
        invFun := fun y => ⟨e.symm (y : Point 3), by
          have h2 : ‖e.symm (y : Point 3)‖ = ‖(y : Point 3)‖ := e.symm.norm_map (y : Point 3)
          have h3 : ‖(y : Point 3)‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using y.prop
          have h4 : ‖e.symm (y : Point 3)‖ = 1 := by rw [h2, h3]
          simpa [Metric.mem_sphere, dist_zero_right] using h4⟩
        left_inv := by intro x; apply Subtype.ext; exact e.left_inv (x : Point 3)
        right_inv := by intro y; apply Subtype.ext; exact e.right_inv (y : Point 3)
        continuous_toFun := by
          apply Continuous.subtype_mk
          exact e.continuous.comp continuous_subtype_val
        continuous_invFun := by
          apply Continuous.subtype_mk
          exact e.symm.continuous.comp continuous_subtype_val }
    have h_comm1 : ∀ (x : SphereType), (eₛ x : Point 3) = e (x : Point 3) := by intro x; rfl
    have h_img_comm : ∀ (S : Set SphereType), Subtype.val '' (eₛ '' S) = e '' (Subtype.val '' S) := by
      intro S
      ext y
      simp only [Set.mem_image]
      constructor
      · rintro ⟨x, ⟨a, haS, h_eq1⟩, h_eq2⟩
        have h_goal : e (a : Point 3) = y := by
          have h9 : (eₛ a : Point 3) = (x : Point 3) := by exact congr_arg Subtype.val h_eq1
          have h10 : e (a : Point 3) = (eₛ a : Point 3) := (h_comm1 a).symm
          rw [h10, h9, h_eq2]
        exact ⟨(a : Point 3), ⟨a, haS, rfl⟩, h_goal⟩
      · rintro ⟨z, ⟨a, haS, h_eq1⟩, h_eq2⟩
        have h_goal : (eₛ a : Point 3) = y := by
          calc (eₛ a : Point 3)
             = e (a : Point 3) := h_comm1 a
           _ = e z := by rw [h_eq1]
           _ = y := h_eq2
        exact ⟨eₛ a, ⟨a, haS, rfl⟩, h_goal⟩
    have h_smul_comm : ∀ (T : Set (Point 3)), (Set.Ioo (0 : ℝ) 1 • e '' T) = e '' (Set.Ioo (0 : ℝ) 1 • T) := by
      intro T
      ext z
      simp only [Set.mem_smul_set, Set.mem_image]
      constructor
      · rintro ⟨t, ht, y, ⟨w, hw, rfl⟩, rfl⟩
        exact ⟨t • w, ⟨t, ht, w, hw, rfl⟩, by simp [e.map_smul]⟩
      · rintro ⟨u, ⟨t, ht, w, hw, rfl⟩, rfl⟩
        exact ⟨t, ht, e w, ⟨w, hw, rfl⟩, by simp [e.map_smul]⟩
    have h_es_img_preimg : ∀ (s : Set SphereType), eₛ '' s = eₛ.symm ⁻¹' s := by
      intro s
      exact eₛ.image_eq_preimage_symm s
    have h_e_img_preimg : ∀ (s : Set (Point 3)), e '' s = e.symm ⁻¹' s := by
      intro s
      exact e.image_eq_preimage_symm s
    have h_main : ∀ (S : Set SphereType), MeasurableSet S → volume.toSphere (eₛ '' S) = volume.toSphere S := by
      intro S hS
      have hS' : MeasurableSet (eₛ '' S) := by
        rw [h_es_img_preimg S]
        exact hS.preimage eₛ.continuous_invFun.measurable
      rw [MeasureTheory.Measure.toSphere_apply' volume hS',
          MeasureTheory.Measure.toSphere_apply' volume hS]
      let cone := Set.Ioo (0 : ℝ) 1 • Subtype.val '' S
      have h4 : (Set.Ioo (0 : ℝ) 1 • Subtype.val '' (eₛ '' S)) = e '' cone := by
        rw [h_img_comm S, h_smul_comm (Subtype.val '' S)]
      rw [h4]
      have h_emb : MeasurableEmbedding e :=
        { measurable := e.continuous.measurable
          injective := e.injective
          measurableSet_image' := fun {s} hs => by
            rw [h_e_img_preimg s]
            exact hs.preimage e.symm.continuous.measurable }
      have h_map_eq : Measure.map e volume = volume := h_mp_vol.map_eq
      have h7 : Measure.map e volume (e '' cone) = volume (e ⁻¹' (e '' cone)) :=
        h_emb.map_apply volume (e '' cone)
      have h8 : e ⁻¹' (e '' cone) = cone := Set.preimage_image_eq _ e.injective
      have h9 : volume (e '' cone) = volume cone := by
        calc volume (e '' cone)
          = Measure.map e volume (e '' cone) := by rw [h_map_eq]
        _ = volume (e ⁻¹' (e '' cone)) := h7
        _ = volume cone := by rw [h8]
      exact congr_arg (fun x : ℝ≥0∞ => (Module.finrank ℝ (Point 3) : ℝ≥0∞) * x) h9
    have h_f_img : f '' A = e '' A := by ext y; simp [h_e_eq_f]
    have hA' : MeasurableSet (f '' A) := by
      rw [h_f_img, h_e_img_preimg A]
      exact hA.preimage e.symm.continuous.measurable
    have h_set_eq : Subtype.val ⁻¹' (f '' A) = eₛ '' (Subtype.val ⁻¹' A) := by
      ext x; simp only [Set.mem_preimage, Set.mem_image]; constructor
      · intro h
        rcases h with ⟨a, haA, hfa⟩
        have haS : a ∈ sphere (0 : Point 3) 1 := by
          have h3 : ‖f a‖ = ‖a‖ := f.norm_map a
          have h4 : ‖f a‖ = 1 := by
            have hfa' : f a = (x : Point 3) := hfa
            rw [hfa']
            have h5 : dist (x : Point 3) 0 = 1 := x.prop
            have h6 : ‖(x : Point 3)‖ = 1 := by
              simpa [dist_zero_right] using h5
            exact h6
          have h5 : ‖a‖ = 1 := by rw [← h3, h4]
          simpa [Metric.mem_sphere, dist_zero_right] using h5
        let y : SphereType := ⟨a, haS⟩
        have hyA : (y : Point 3) ∈ A := haA
        have h_eq : eₛ y = x := by
          apply Subtype.ext
          have h6 : (eₛ y : Point 3) = e a := by rfl
          rw [h6, h_e_eq_f a]; exact hfa
        exact ⟨y, hyA, h_eq⟩
      · rintro ⟨y, hyA, h_eq⟩
        have h9 : (eₛ y : Point 3) = (x : Point 3) := congr_arg Subtype.val h_eq
        have h10 : (eₛ y : Point 3) = e (y : Point 3) := h_comm1 y
        have h11 : e (y : Point 3) = f (y : Point 3) := h_e_eq_f (y : Point 3)
        have h12 : (x : Point 3) = f (y : Point 3) := by
          rw [← h9, h10, h11]
        exact ⟨(y : Point 3), hyA, h12.symm⟩
    have h1 : ν (f '' A) = volume.toSphere (Subtype.val ⁻¹' (f '' A)) := by
      dsimp only [ν]; rw [Measure.map_apply continuous_subtype_val.measurable hA'] <;> rfl
    have h2 : ν A = volume.toSphere (Subtype.val ⁻¹' A) := by
      dsimp only [ν]; rw [Measure.map_apply continuous_subtype_val.measurable hA] <;> rfl
    rw [h1, h2, h_set_eq]
    exact h_main (Subtype.val ⁻¹' A) (continuous_subtype_val.measurable hA)
  -- For any r > 0 small enough, apply Fubini averaging
  have h_main : ∀ (r : ℝ), 0 < r → r < Real.sqrt 2 →
      μ Set.univ * ν (sphereCap northPole r) = ν Set.univ * μ (sphereCap northPole r) := by
    intro r hr hr2
    exact fubini_averaging hμ_support hν_support hμ_inv hν_inv r (by linarith) northPole northPole_sphere
  -- Get bounds for r → 0
  have h_small : ∀ (ε : ℝ), 0 < ε → ε < 1 → ∃ r > 0, r < Real.sqrt 2 ∧
      ENNReal.ofReal (1 - ε) * ν (sphereCap northPole r) ≤ μ (sphereCap northPole r) ∧
      μ (sphereCap northPole r) ≤ ENNReal.ofReal (1 + ε) * ν (sphereCap northPole r) := by
    intro ε hε hε1
    have h_exists : ∃ r0 > 0, ∀ r, 0 < r → r < r0 →
        let a := 1 - r^2 / 2
        a^2 ≥ 1 - ε ∧ 1 / a^3 ≤ 1 + ε := by
      have h1 : Tendsto (fun r : ℝ => (1 - r^2 / 2)^2) (𝓝 0) (𝓝 1) := by
        have h_cont : Continuous (fun r : ℝ => (1 - r^2 / 2)^2) := by fun_prop
        have h_f0 : (1 - (0 : ℝ)^2 / 2)^2 = 1 := by norm_num
        have h_tendsto := h_cont.tendsto 0
        rw [h_f0] at h_tendsto
        exact h_tendsto
      have h2 : Tendsto (fun r : ℝ => 1 / (1 - r^2 / 2)^3) (𝓝 0) (𝓝 1) := by
        have h_cont_at : ContinuousAt (fun r : ℝ => 1 / (1 - r^2 / 2)^3) 0 := by
          apply ContinuousAt.div
          · exact continuous_const.continuousAt
          · exact (by fun_prop : Continuous (fun r : ℝ => (1 - r^2 / 2)^3)).continuousAt
          · norm_num
        have h_f0 : (1 / (1 - (0 : ℝ)^2 / 2)^3) = 1 := by norm_num
        have h_tendsto := h_cont_at.tendsto
        rw [h_f0] at h_tendsto
        exact h_tendsto
      have h3 : ∀ᶠ r in 𝓝 0, (1 - r^2 / 2)^2 ≥ 1 - ε := by
        have h_lt : (1 - ε : ℝ) < 1 := by linarith [hε]
        have h_ev : ∀ᶠ r in 𝓝 0, (1 - r^2 / 2)^2 ∈ Ioi (1 - ε) := h1 (Ioi_mem_nhds h_lt)
        filter_upwards [h_ev] with r hr
        exact le_of_lt hr
      have h4 : ∀ᶠ r in 𝓝 0, 1 / (1 - r^2 / 2)^3 ≤ 1 + ε := by
        have h_gt : (1 : ℝ) < 1 + ε := by linarith [hε]
        have h_ev : ∀ᶠ r in 𝓝 0, (1 / (1 - r^2 / 2)^3) ∈ Iio (1 + ε) := h2 (Iio_mem_nhds h_gt)
        filter_upwards [h_ev] with r hr
        exact le_of_lt hr
      have h5 : ∀ᶠ r in 𝓝 0, (1 - r^2 / 2)^2 ≥ 1 - ε ∧ 1 / (1 - r^2 / 2)^3 ≤ 1 + ε :=
        h3.and h4
      rcases Metric.mem_nhds_iff.mp h5 with ⟨r0, hr0_pos, h⟩
      refine ⟨r0, hr0_pos, fun r hr_pos hr_lt => ?_⟩
      have h6 : dist r 0 < r0 := by
        have h7 : dist r 0 = ‖r‖ := dist_zero_right r
        have h8 : ‖r‖ = r := abs_of_pos hr_pos
        rw [h7, h8]
        exact hr_lt
      exact h h6
    rcases h_exists with ⟨r0, hr0_pos, h⟩
    let r := min (r0 / 2) (Real.sqrt 2 / 2)
    have hr_pos : 0 < r := by positivity
    have hr_lt_r0 : r < r0 := by
      have h1 : r ≤ r0 / 2 := min_le_left _ _
      linarith
    have hr_lt_sqrt2 : r < Real.sqrt 2 := by
      have h1 : r ≤ Real.sqrt 2 / 2 := min_le_right _ _
      linarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)]
    have h2 := h r hr_pos hr_lt_r0
    set a : ℝ := 1 - r^2 / 2 with ha_def
    set R2 : ℝ := r^2 - r^4 / 4 with hR2_def
    have ha_pos : 0 < a := by
      have h1 : r^2 < 2 := by
        have h2 : 0 ≤ r := by linarith
        have h3 : r^2 < (Real.sqrt 2)^2 := by gcongr
        have h4 : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
        rw [h4] at h3; exact h3
      nlinarith
    have hR2_pos : 0 < R2 := by nlinarith [sq_pos_of_pos hr_pos]
    have h_cap_meas : MeasurableSet (sphereCap northPole r) :=
      h_us_meas2.inter isClosed_closedBall.measurableSet
    have h_cap_subset : sphereCap northPole r ⊆ unitSphere 3 := by
      intro x hx; exact hx.1
    have h_μ_eq : μ (sphereCap northPole r) = (μHE[2] : Measure (Point 3)) (sphereCap northPole r) := by
      rw [Measure.restrict_apply h_cap_meas]
      have h_inter : (sphereCap northPole r) ∩ unitSphere 3 = sphereCap northPole r :=
        Set.inter_eq_left.mpr h_cap_subset
      rw [h_inter]
    have h_ν_eq : ν (sphereCap northPole r) =
        (volume : Measure (Point 3)).toSphere (Subtype.val ⁻¹' (sphereCap northPole r)) := by
      dsimp only [ν]
      rw [Measure.map_apply continuous_subtype_val.measurable h_cap_meas] <;> rfl
    have h_μ_bounds := muHE_cap_bounds r hr_pos hr_lt_sqrt2
    have h_ν_bounds := toSphere_cap_bounds r hr_pos hr_lt_sqrt2
    have h_a2 : a^2 ≥ 1 - ε := h2.1
    have h_1a3 : 1 / a^3 ≤ 1 + ε := h2.2
    have h_μ_lower : ENNReal.ofReal (Real.pi * R2) ≤ μ (sphereCap northPole r) := by
      rw [h_μ_eq]; exact h_μ_bounds.1
    have h_μ_upper : μ (sphereCap northPole r) ≤ ENNReal.ofReal (Real.pi * R2 / a^2) := by
      rw [h_μ_eq]; exact h_μ_bounds.2
    have h_ν_lower : ENNReal.ofReal (Real.pi * R2 * a) ≤ ν (sphereCap northPole r) := by
      rw [h_ν_eq]; exact h_ν_bounds.1
    have h_ν_upper : ν (sphereCap northPole r) ≤ ENNReal.ofReal (Real.pi * R2 / a^2) := by
      rw [h_ν_eq]; exact h_ν_bounds.2
    have h1mε_nonneg : 0 ≤ 1 - ε := by linarith
    have h_pi_R2_nonneg : 0 ≤ Real.pi * R2 := by positivity
    have h_pi_R2_pos : 0 < Real.pi * R2 := by positivity
    have h_a2_pos : 0 < a^2 := by positivity
    refine ⟨r, hr_pos, hr_lt_sqrt2, ?_⟩
    constructor
    · -- Lower bound: μ ≥ (1-ε) * ν
      have h_real_ineq : (1 - ε) * (Real.pi * R2 / a^2) ≤ Real.pi * R2 := by
        have h_pos : 0 < a^2 := h_a2_pos
        have h_le : (1 - ε) / a^2 ≤ 1 := by
          rw [div_le_one (by positivity)] <;> linarith
        have h : (1 - ε) * (Real.pi * R2 / a^2) = Real.pi * R2 * ((1 - ε) / a^2) := by ring
        rw [h]
        have h6 : Real.pi * R2 * ((1 - ε) / a^2) ≤ Real.pi * R2 := by
          have h7 : Real.pi * R2 * ((1 - ε) / a^2) ≤ Real.pi * R2 * 1 :=
            mul_le_mul_of_nonneg_left h_le h_pi_R2_nonneg
          have h8 : Real.pi * R2 * 1 = Real.pi * R2 := by ring
          rw [h8] at h7
          exact h7
        exact h6
      calc
        μ (sphereCap northPole r)
          ≥ ENNReal.ofReal (Real.pi * R2) := h_μ_lower
        _ ≥ ENNReal.ofReal ((1 - ε) * (Real.pi * R2 / a^2)) :=
          ENNReal.ofReal_le_ofReal h_real_ineq
        _ = ENNReal.ofReal (1 - ε) * ENNReal.ofReal (Real.pi * R2 / a^2) := by
          rw [← ENNReal.ofReal_mul h1mε_nonneg] <;> ring
        _ ≥ ENNReal.ofReal (1 - ε) * ν (sphereCap northPole r) := by
          gcongr
    · -- Upper bound: μ ≤ (1+ε) * ν
      have h_real_ineq2 : Real.pi * R2 / a^2 ≤ (1 + ε) * (Real.pi * R2 * a) := by
        have h4 : 1 / a^3 ≤ 1 + ε := h_1a3
        have h5 : 0 < a := ha_pos
        have h6 : 0 < Real.pi * R2 := h_pi_R2_pos
        have h7 : Real.pi * R2 / a^2 ≤ (1 + ε) * (Real.pi * R2 * a) := by
          have h_ineq : 1 / a^2 ≤ (1 + ε) * a := by
            have h_pos3 : 0 < a^3 := by positivity
            have h : (1 / a^3) * a ≤ (1 + ε) * a := by gcongr
            have h2 : (1 / a^3) * a = 1 / a^2 := by
              field_simp [ha_pos.ne'] <;> ring
            rw [h2] at h
            exact h
          calc
            Real.pi * R2 / a^2
              = (Real.pi * R2) * (1 / a^2) := by ring
            _ ≤ (Real.pi * R2) * ((1 + ε) * a) := by
              have h9 : (Real.pi * R2) * (1 / a^2) ≤ (Real.pi * R2) * ((1 + ε) * a) :=
                mul_le_mul_of_nonneg_left h_ineq h_pi_R2_nonneg
              exact h9
            _ = (1 + ε) * (Real.pi * R2 * a) := by ring
        exact h7
      calc
        μ (sphereCap northPole r)
          ≤ ENNReal.ofReal (Real.pi * R2 / a^2) := h_μ_upper
        _ ≤ ENNReal.ofReal ((1 + ε) * (Real.pi * R2 * a)) :=
          ENNReal.ofReal_le_ofReal h_real_ineq2
        _ = ENNReal.ofReal (1 + ε) * ENNReal.ofReal (Real.pi * R2 * a) := by
          rw [← ENNReal.ofReal_mul (by linarith)] <;> ring
        _ ≤ ENNReal.ofReal (1 + ε) * ν (sphereCap northPole r) := by
          gcongr
  -- Now use Fubini: μ(univ)/ν(univ) = μ(cap)/ν(cap) for all r
  -- And the ratio tends to 1, so μ(univ) = ν(univ)
  have h_final : ∀ (ε : ℝ), 0 < ε → ε < 1 →
      ENNReal.ofReal (1 - ε) * ν Set.univ ≤ μ Set.univ ∧
      μ Set.univ ≤ ENNReal.ofReal (1 + ε) * ν Set.univ := by
    intro ε hε hε1
    rcases h_small ε hε hε1 with ⟨r, hr_pos, hr_lt_sqrt2, h_lower, h_upper⟩
    have h_fub := h_main r hr_pos hr_lt_sqrt2
    set cap := sphereCap northPole r with hcap_def
    have hν_pos : 0 < ν cap := by
      have h_ν_bounds2 := toSphere_cap_bounds r hr_pos hr_lt_sqrt2
      set a2 : ℝ := 1 - r^2 / 2 with ha2_def
      set R22 : ℝ := r^2 - r^4 / 4 with hR22_def
      have ha2_pos : 0 < a2 := by
        have h1 : r^2 < 2 := by
          have h2 : 0 ≤ r := by linarith
          have h3 : r^2 < (Real.sqrt 2)^2 := by gcongr
          have h4 : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num)
          rw [h4] at h3; exact h3
        dsimp only [a2]
        nlinarith
      have hR22_pos : 0 < R22 := by nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)]
      have h_pos2 : 0 < Real.pi * R22 * a2 := by positivity
      have h_cap_meas2 : MeasurableSet cap := h_us_meas2.inter isClosed_closedBall.measurableSet
      have h_ν_eq2 : ν cap = volume.toSphere (Subtype.val ⁻¹' cap) := by
        dsimp only [ν, cap]
        rw [Measure.map_apply continuous_subtype_val.measurable h_cap_meas2] <;> rfl
      rw [h_ν_eq2]
      have h_lb : ENNReal.ofReal (Real.pi * R22 * a2) ≤ volume.toSphere (Subtype.val ⁻¹' cap) := h_ν_bounds2.1
      have h_pos_ennreal : 0 < ENNReal.ofReal (Real.pi * R22 * a2) := ENNReal.ofReal_pos.mpr h_pos2
      exact lt_of_lt_of_le h_pos_ennreal h_lb
    have hν_ne_zero : ν cap ≠ 0 := hν_pos.ne'
    have hμ_univ_lt_top : μ Set.univ < ⊤ := hμ_fin.measure_univ_lt_top
    have hν_univ_lt_top : ν Set.univ < ⊤ := hν_fin.measure_univ_lt_top
    have hν_cap_lt_top : ν cap < ⊤ := measure_lt_top ν cap
    have h_mul_lt_top : ∀ (a b : ENNReal), a < ⊤ → b < ⊤ → a * b < ⊤ :=
      fun a b ha hb => WithTop.mul_lt_top ha hb
    have h_ofReal_lt_top : ∀ (x : ℝ), ENNReal.ofReal x < ⊤ := fun _ => lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top
    have h_up : μ Set.univ ≤ ENNReal.ofReal (1 + ε) * ν Set.univ := by
      have h : μ Set.univ * ν cap = ν Set.univ * μ cap := h_fub
      have h2 : μ Set.univ * ν cap ≤ ν Set.univ * (ENNReal.ofReal (1 + ε) * ν cap) := by
        rw [h]
        exact mul_le_mul_left' h_upper (ν Set.univ)
      have h3 : μ Set.univ * ν cap ≤ ENNReal.ofReal (1 + ε) * ν Set.univ * ν cap := by
        calc
          μ Set.univ * ν cap
            ≤ ν Set.univ * (ENNReal.ofReal (1 + ε) * ν cap) := h2
          _ = ENNReal.ofReal (1 + ε) * ν Set.univ * ν cap := by
            rw [mul_left_comm, mul_assoc]
      have h_left_lt_top : μ Set.univ * ν cap < ⊤ := h_mul_lt_top (μ Set.univ) (ν cap) hμ_univ_lt_top hν_cap_lt_top
      have h_right_lt_top : ENNReal.ofReal (1 + ε) * ν Set.univ * ν cap < ⊤ :=
        h_mul_lt_top _ _ (h_mul_lt_top _ _ (h_ofReal_lt_top (1 + ε)) hν_univ_lt_top) hν_cap_lt_top
      have h4 : (μ Set.univ).toReal * (ν cap).toReal ≤
          (ENNReal.ofReal (1 + ε) * ν Set.univ).toReal * (ν cap).toReal := by
        have h3' : (μ Set.univ * ν cap).toReal ≤ (ENNReal.ofReal (1 + ε) * ν Set.univ * ν cap).toReal :=
          (ENNReal.toReal_le_toReal h_left_lt_top.ne h_right_lt_top.ne).mpr h3
        simpa [ENNReal.toReal_mul] using h3'
      have hν_real_pos : 0 < (ν cap).toReal := ENNReal.toReal_pos hν_ne_zero hν_cap_lt_top.ne
      have h5 : (μ Set.univ).toReal ≤ (ENNReal.ofReal (1 + ε) * ν Set.univ).toReal := by
        nlinarith
      have h_right2_lt_top : ENNReal.ofReal (1 + ε) * ν Set.univ < ⊤ :=
        h_mul_lt_top _ _ (h_ofReal_lt_top (1 + ε)) hν_univ_lt_top
      exact (ENNReal.toReal_le_toReal hμ_univ_lt_top.ne h_right2_lt_top.ne).mp h5

    have h_low : ENNReal.ofReal (1 - ε) * ν Set.univ ≤ μ Set.univ := by
      have h : ν Set.univ * μ cap = μ Set.univ * ν cap := h_fub.symm
      have h2 : ν Set.univ * (ENNReal.ofReal (1 - ε) * ν cap) ≤ ν Set.univ * μ cap := by
        exact mul_le_mul_left' h_lower (ν Set.univ)
      have h3 : ENNReal.ofReal (1 - ε) * ν Set.univ * ν cap ≤ μ Set.univ * ν cap := by
        calc
          ENNReal.ofReal (1 - ε) * ν Set.univ * ν cap
            = ν Set.univ * (ENNReal.ofReal (1 - ε) * ν cap) := by
              rw [mul_comm (ENNReal.ofReal (1 - ε)) (ν Set.univ), ← mul_assoc]
          _ ≤ ν Set.univ * μ cap := h2
          _ = μ Set.univ * ν cap := h
      have h_left_lt_top : ENNReal.ofReal (1 - ε) * ν Set.univ * ν cap < ⊤ :=
        h_mul_lt_top _ _ (h_mul_lt_top _ _ (h_ofReal_lt_top (1 - ε)) hν_univ_lt_top) hν_cap_lt_top
      have h_right_lt_top : μ Set.univ * ν cap < ⊤ := h_mul_lt_top _ _ hμ_univ_lt_top hν_cap_lt_top
      have h4 : (ENNReal.ofReal (1 - ε) * ν Set.univ).toReal * (ν cap).toReal ≤
          (μ Set.univ).toReal * (ν cap).toReal := by
        have h3' : (ENNReal.ofReal (1 - ε) * ν Set.univ * ν cap).toReal ≤ (μ Set.univ * ν cap).toReal :=
          (ENNReal.toReal_le_toReal h_left_lt_top.ne h_right_lt_top.ne).mpr h3
        simpa [ENNReal.toReal_mul] using h3'
      have hν_real_pos : 0 < (ν cap).toReal := ENNReal.toReal_pos hν_ne_zero hν_cap_lt_top.ne
      have h5 : (ENNReal.ofReal (1 - ε) * ν Set.univ).toReal ≤ (μ Set.univ).toReal := by
        nlinarith
      have h_left2_lt_top : ENNReal.ofReal (1 - ε) * ν Set.univ < ⊤ :=
        h_mul_lt_top _ _ (h_ofReal_lt_top (1 - ε)) hν_univ_lt_top
      exact (ENNReal.toReal_le_toReal h_left2_lt_top.ne hμ_univ_lt_top.ne).mp h5

    exact ⟨h_low, h_up⟩
  have hμ_lt_top : μ Set.univ < ⊤ := hμ_fin.measure_univ_lt_top
  have hν_lt_top : ν Set.univ < ⊤ := hν_fin.measure_univ_lt_top
  let u : ℝ := (μ Set.univ).toReal
  let v : ℝ := (ν Set.univ).toReal
  have hμ_eq : μ Set.univ = ENNReal.ofReal u := by
    rw [ENNReal.ofReal_toReal hμ_lt_top.ne]
  have hν_eq : ν Set.univ = ENNReal.ofReal v := by
    rw [ENNReal.ofReal_toReal hν_lt_top.ne]
  have h_upper_real : ∀ ε : ℝ, 0 < ε → ε < 1 → u ≤ (1 + ε) * v := by
    intro ε hε hε1
    have h := (h_final ε hε hε1).2
    rw [hμ_eq, hν_eq] at h
    have h4 : ENNReal.ofReal (1 + ε) * ENNReal.ofReal v = ENNReal.ofReal ((1 + ε) * v) := by
      rw [ENNReal.ofReal_mul (by linarith)] <;> ring
    rw [h4] at h
    have hv_nonneg : 0 ≤ v := by positivity
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h
  have h_lower_real : ∀ ε : ℝ, 0 < ε → ε < 1 → (1 - ε) * v ≤ u := by
    intro ε hε hε1
    have h := (h_final ε hε hε1).1
    rw [hμ_eq, hν_eq] at h
    have h4 : ENNReal.ofReal (1 - ε) * ENNReal.ofReal v = ENNReal.ofReal ((1 - ε) * v) := by
      rw [ENNReal.ofReal_mul (by linarith)] <;> ring
    rw [h4] at h
    have hu_nonneg : 0 ≤ u := by positivity
    exact (ENNReal.ofReal_le_ofReal_iff hu_nonneg).mp h
  have h_nhds1 : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Ioi (0 : ℝ)), ε < 1 := by
    apply eventually_nhdsWithin_of_eventually_nhds
    exact Iio_mem_nhds (by norm_num)
  have h_upper : u ≤ v := by
    have h_tendsto : Tendsto (fun ε : ℝ => (1 + ε) * v) (nhdsWithin (0 : ℝ) (Ioi (0 : ℝ))) (𝓝 v) := by
      have h : Tendsto (fun ε : ℝ => (1 + ε) * v) (𝓝 0) (𝓝 ((1 + (0 : ℝ)) * v)) :=
        Tendsto.mul (tendsto_const_nhds.add tendsto_id) tendsto_const_nhds
      have h2 : (1 + (0 : ℝ)) * v = v := by ring
      rw [h2] at h
      exact h.mono_left nhdsWithin_le_nhds
    have h_event : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Ioi (0 : ℝ)), u ≤ (1 + ε) * v := by
      filter_upwards [self_mem_nhdsWithin, h_nhds1] with ε hε_pos hε_lt
      exact h_upper_real ε hε_pos hε_lt
    exact ge_of_tendsto h_tendsto h_event
  have h_lower : v ≤ u := by
    have h_tendsto : Tendsto (fun ε : ℝ => (1 - ε) * v) (nhdsWithin (0 : ℝ) (Ioi (0 : ℝ))) (𝓝 v) := by
      have h : Tendsto (fun ε : ℝ => (1 - ε) * v) (𝓝 0) (𝓝 ((1 - (0 : ℝ)) * v)) :=
        Tendsto.mul (tendsto_const_nhds.sub tendsto_id) tendsto_const_nhds
      have h2 : (1 - (0 : ℝ)) * v = v := by ring
      rw [h2] at h
      exact h.mono_left nhdsWithin_le_nhds
    have h_event : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Ioi (0 : ℝ)), (1 - ε) * v ≤ u := by
      filter_upwards [self_mem_nhdsWithin, h_nhds1] with ε hε_pos hε_lt
      exact h_lower_real ε hε_pos hε_lt
    exact le_of_tendsto h_tendsto h_event
  have h_eq : u = v := by linarith
  have h_main_eq : μ Set.univ = ν Set.univ := by
    rw [hμ_eq, hν_eq, h_eq]
  have h_final1 : (μHE[2] : Measure (Point 3)) (unitSphere 3) = μ Set.univ := by
    simpa [μ, Measure.restrict_apply] using rfl
  have h_final2 : ν Set.univ = (volume : Measure (Point 3)).toSphere Set.univ := by
    dsimp only [ν]
    rw [Measure.map_apply continuous_subtype_val.measurable] <;> simp
  rw [h_final1, h_main_eq, h_final2]

end

end Kakeya.CV
