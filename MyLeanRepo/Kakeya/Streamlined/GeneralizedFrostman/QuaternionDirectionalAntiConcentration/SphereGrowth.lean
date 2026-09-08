import MyLeanRepo.Kakeya.Streamlined.Geometry
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# 3-growth bound for surface measure on S³

This module establishes that the normalized surface measure on the unit 3-sphere
satisfies a 3-growth bound: the measure of any ball of radius r ≤ 1 is O(r³).

## Proof route

1. Show `volume.toSphere` is invariant under linear isometries of the ambient space.
2. For any point x on S³, find a linear isometry mapping x to e₀ = (1,0,0,0).
3. Bound the measure of a ball around e₀ via the cone construction:
   `toSphere(s) = 4 · volume(Ioo(0,1) • Subtype.val '' s)`.
4. The cone over a cap around e₀ is contained in the box [0,1] × [-r,r]³,
   whose volume is 8r³.
5. Therefore `toSphere(ball(e₀,r)) ≤ 4 · 8r³ = 32r³`.
6. Normalize by `toSphere(univ)` to get a probability measure.

## Whiteprint node

`sphere_3growth_measure` — 3-growth probability measure on S³.
-/

noncomputable section

open scoped Pointwise

open MeasureTheory Metric Set

namespace Kakeya.Streamlined.GeneralizedFrostman

abbrev Sphere3 := sphere (0 : EuclideanSpace ℝ (Fin 4)) 1

instance : Nonempty Sphere3 :=
  ⟨⟨EuclideanSpace.single 0 1, by
    have h_e0_norm : ‖(EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 4))‖ = 1 := by
      rw [PiLp.norm_single] <;> norm_num
    simpa [dist_zero_right, Metric.mem_sphere] using h_e0_norm⟩⟩

/-- For any two unit vectors, there is a linear isometry mapping one to the other. -/
lemma exists_isometry_map_unit {x y : EuclideanSpace ℝ (Fin 4)}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ∃ (e : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4)), e x = y := by
  by_cases hxy : x = y
  · exact ⟨LinearIsometryEquiv.refl ℝ _, by rw [hxy] <;> simp⟩
  · let e := Submodule.reflection (ℝ ∙ (x - y))ᗮ
    have h_main : e x = y := by
      exact Submodule.reflection_sub (show ‖x‖ = ‖y‖ from by rw [hx, hy])
    exact ⟨e, h_main⟩

/-- Restrict a linear isometry to the unit sphere. -/
noncomputable def restrictToSphere (e : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4)) :
    Sphere3 ≃ₜ Sphere3 :=
  { toFun := fun y => ⟨e (y : EuclideanSpace ℝ (Fin 4)), by
      have h : ‖e (y : EuclideanSpace ℝ (Fin 4))‖ = ‖(y : EuclideanSpace ℝ (Fin 4))‖ := e.norm_map _
      have h' : ‖(y : EuclideanSpace ℝ (Fin 4))‖ = 1 := by simpa [dist_zero_right] using y.property
      simpa [dist_zero_right, Metric.mem_sphere] using h ▸ h'⟩
    invFun := fun y => ⟨e.symm (y : EuclideanSpace ℝ (Fin 4)), by
      have h : ‖e.symm (y : EuclideanSpace ℝ (Fin 4))‖ = ‖(y : EuclideanSpace ℝ (Fin 4))‖ := e.symm.norm_map _
      have h' : ‖(y : EuclideanSpace ℝ (Fin 4))‖ = 1 := by simpa [dist_zero_right] using y.property
      simpa [dist_zero_right, Metric.mem_sphere] using h ▸ h'⟩
    left_inv := by intro y; apply Subtype.ext; simp
    right_inv := by intro y; apply Subtype.ext; simp
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }

/-- `volume.toSphere` is invariant under linear isometries. -/
lemma toSphere_invariant (e : EuclideanSpace ℝ (Fin 4) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 4))
    {s : Set Sphere3} (hs : MeasurableSet s) :
    volume.toSphere ((restrictToSphere e) '' s) = volume.toSphere s := by
  let eS := restrictToSphere e
  let E := EuclideanSpace ℝ (Fin 4)
  let A : Set E := Set.Ioo (0 : ℝ) 1 • (Subtype.val '' s)
  have h1 : (Subtype.val '' (eS '' s)) = e '' (Subtype.val '' s) := by
    ext z
    simp only [Set.mem_image]
    constructor
    · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨(x : E), ⟨x, hx, rfl⟩, ?_⟩
      rfl
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨eS x, ⟨x, hx, rfl⟩, ?_⟩
      rfl
  have h2 : Set.Ioo (0 : ℝ) 1 • (e '' (Subtype.val '' s)) = e '' A := by
    ext z
    simp only [Set.mem_smul_set, Set.mem_image, A]
    constructor
    · rintro ⟨t, ht, w, ⟨u, hu, rfl⟩, rfl⟩
      refine ⟨t • (u : E), ⟨t, ht, u, hu, rfl⟩, ?_⟩
      exact e.map_smul t (u : E)
    · rintro ⟨_, ⟨t, ht, u, hu, rfl⟩, rfl⟩
      refine ⟨t, ht, e (u : E), ⟨u, hu, rfl⟩, ?_⟩
      exact (e.map_smul t (u : E)).symm
  let eM : E ≃ᵐ E := e.toHomeomorph.toMeasurableEquiv
  have h_map : Measure.map eM volume = volume :=
    e.measurePreserving.map_eq
  have h_eM_eq : (eM : E → E) = e := by rfl
  have h42 : eM ⁻¹' (e '' A) = A := by
    rw [h_eM_eq]
    exact e.injective.preimage_image A
  have h3 : volume (e '' A) = volume A := by
    have h41 : Measure.map eM volume (e '' A) = volume (eM ⁻¹' (e '' A)) :=
      MeasurableEquiv.map_apply eM (e '' A)
    rw [h_map] at h41
    rw [h42] at h41
    exact h41
  have h_ms : MeasurableSet (eS '' s) := by
    have h_eq : eS '' s = eS.symm ⁻¹' s := by
      ext y
      simp only [Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨x, hx, rfl⟩
        simpa using hx
      · intro hx
        exact ⟨eS.symm y, hx, eS.apply_symm_apply y⟩
    rw [h_eq]
    exact eS.symm.continuous.measurable hs
  have h_dim : Module.finrank ℝ E = 4 := by
    have h : Module.finrank ℝ E = Fintype.card (Fin 4) := by
      exact finrank_euclideanSpace_fin
    rw [h] <;> decide
  calc
    volume.toSphere (eS '' s)
      = Module.finrank ℝ E * volume (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' (eS '' s))) :=
        (Measure.toSphere_apply' volume h_ms)
    _ = 4 * volume (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' (eS '' s))) := by
      rw [h_dim] <;> ring
    _ = 4 * volume (Set.Ioo (0 : ℝ) 1 • (e '' (Subtype.val '' s))) := by rw [h1]
    _ = 4 * volume (e '' A) := by rw [h2]
    _ = 4 * volume A := by rw [h3]
    _ = volume.toSphere s := by
      have h_last : volume.toSphere s = Module.finrank ℝ E * volume A :=
        Measure.toSphere_apply' volume hs
      rw [h_dim] at h_last
      exact h_last.symm

/-- The surface measure on S³, normalized to a probability measure. -/
noncomputable def sphere3ProbabilityMeasure : Measure Sphere3 :=
  (volume.toSphere (Set.univ : Set Sphere3))⁻¹ • volume.toSphere

lemma sphere3ProbabilityMeasure_isProbability :
    IsProbabilityMeasure sphere3ProbabilityMeasure := by
  dsimp only [sphere3ProbabilityMeasure]
  let e0 : EuclideanSpace ℝ (Fin 4) := EuclideanSpace.single 0 1
  have h_e0_norm : ‖e0‖ = 1 := by
    rw [PiLp.norm_single] <;> norm_num
  let e0' : Sphere3 := ⟨e0, by simpa [dist_zero_right, Metric.mem_sphere] using h_e0_norm⟩
  haveI : Nonempty Sphere3 := ⟨e0'⟩
  have h_pos : 0 < volume.toSphere (Set.univ : Set Sphere3) := by
    have h1 : (volume.toSphere : Measure Sphere3).IsOpenPosMeasure := by
      exact Measure.toSphere.instIsOpenPosMeasure volume
    have h2 : volume.toSphere (Set.univ : Set Sphere3) ≠ 0 :=
      h1.open_pos Set.univ isOpen_univ Set.univ_nonempty
    exact Ne.bot_lt h2
  have h_ne_top : volume.toSphere (Set.univ : Set Sphere3) ≠ ⊤ :=
    measure_ne_top volume.toSphere (Set.univ : Set Sphere3)
  have h : (volume.toSphere (Set.univ : Set Sphere3))⁻¹ *
        volume.toSphere (Set.univ : Set Sphere3) = 1 := by
    apply ENNReal.inv_mul_cancel
    · exact h_pos.ne'
    · exact h_ne_top
  refine' ⟨_⟩
  simpa [Measure.smul_apply] using h

/-- 3-growth bound for the normalized surface measure on S³. -/
lemma sphere3_growth {x : Sphere3} {r : ℝ} (hr : 0 < r) (hr' : r ≤ 1) :
    sphere3ProbabilityMeasure (Metric.closedBall x r) ≤
      ENNReal.ofReal (32 * r ^ 3) * (volume.toSphere (Set.univ : Set Sphere3))⁻¹ := by
  let E := EuclideanSpace ℝ (Fin 4)
  let e0 : E := EuclideanSpace.single 0 1
  have h_e0_norm : ‖e0‖ = 1 := by
    rw [PiLp.norm_single] <;> norm_num
  let e0' : Sphere3 := ⟨e0, by simpa [dist_zero_right, Metric.mem_sphere] using h_e0_norm⟩
  have hx1 : ‖(x : E)‖ = 1 := by simpa [dist_zero_right] using x.property
  rcases exists_isometry_map_unit hx1 h_e0_norm with ⟨e, he⟩
  let eS := restrictToSphere e
  have h_eS_x : eS x = e0' := by
    apply Subtype.ext
    exact he
  have h_dist_eq : ∀ (a b : Sphere3), dist (eS a) (eS b) = dist a b := by
    intro a b
    have h : ‖e ((a : E) - (b : E))‖ = ‖(a : E) - (b : E)‖ := e.norm_map _
    have h' : e ((a : E) - (b : E)) = e (a : E) - e (b : E) := by
      rw [e.map_sub]
    simpa [eS, restrictToSphere, Subtype.dist_eq, dist_eq_norm, h'] using h
  have h_ball : eS '' Metric.closedBall x r = Metric.closedBall e0' r := by
    ext z
    simp only [Set.mem_image, Metric.mem_closedBall]
    constructor
    · rintro ⟨w, hw, rfl⟩
      have h := h_dist_eq w x
      rw [h_eS_x] at h
      exact h ▸ hw
    · intro hz
      refine ⟨eS.symm z, ?_, by simp⟩
      have h_eq : dist (eS (eS.symm z)) (eS x) = dist (eS.symm z) x := h_dist_eq (eS.symm z) x
      have h_goal : dist (eS (eS.symm z)) (eS x) ≤ r := by
        rw [eS.apply_symm_apply z, h_eS_x]
        exact hz
      rw [h_eq] at h_goal
      exact h_goal
  have h_ms_ball : MeasurableSet (Metric.closedBall x r) := by
    exact measurableSet_closedBall
  have h_main : volume.toSphere (Metric.closedBall x r) =
        volume.toSphere (Metric.closedBall e0' r) := by
    have h4 := toSphere_invariant e h_ms_ball
    rw [h_ball] at h4
    exact h4.symm
  let a : Fin 4 → ℝ := ![0, -r, -r, -r]
  let b : Fin 4 → ℝ := ![1, r, r, r]
  let box' : Set (Fin 4 → ℝ) := Set.pi Set.univ (fun i => Set.Icc (a i) (b i))
  let box : Set E := WithLp.ofLp ⁻¹' box'
  have h_cone : volume.toSphere (Metric.closedBall e0' r) =
      4 * volume (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' Metric.closedBall e0' r)) := by
    have h_ms : MeasurableSet (Metric.closedBall e0' r) := by
      exact measurableSet_closedBall
    rw [Measure.toSphere_apply' volume h_ms]
    have h_dim : Module.finrank ℝ E = 4 := by
      have h : Module.finrank ℝ E = Fintype.card (Fin 4) := by
        exact finrank_euclideanSpace_fin
      rw [h] <;> decide
    rw [h_dim] <;> ring
  have h_box : (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' Metric.closedBall e0' r)) ⊆ box := by
    intro z hz
    rcases hz with ⟨t, ht, y, hy, hz_eq⟩
    rcases hy with ⟨y', hy', rfl⟩
    have h_y_sphere : ‖(y' : E)‖ = 1 := by simpa [dist_zero_right] using y'.property
    have h_y_ball : dist (y' : E) e0 ≤ r := hy'
    have h_norm_diff : ‖(y' : E) - e0‖ ≤ r := by simpa [dist_eq_norm] using h_y_ball
    have h_sq : ‖(y' : E) - e0‖ ^ 2 ≤ r ^ 2 := by gcongr
    have h_eq : ‖(y' : E) - e0‖ ^ 2 = ∑ i : Fin 4, ((y' : E) i - e0 i) ^ 2 := by
      have h1 : ‖(y' : E) - e0‖ ^ 2 = ∑ i : Fin 4, (((y' : E) - e0) i) ^ 2 :=
        EuclideanSpace.real_norm_sq_eq ((y' : E) - e0)
      rw [h1]
      apply Finset.sum_congr rfl
      intro i _
      rfl
    have h_coord_sq : ∑ i : Fin 4, ((y' : E) i - e0 i) ^ 2 ≤ r ^ 2 := by
      rw [← h_eq]
      exact h_sq
    have h_y0_lower : (y' : E) 0 ≥ 1 - r := by
      have h0 : ((y' : E) 0 - 1) ^ 2 ≤ r ^ 2 := by
        have h_nonneg : ∀ j ∈ (Finset.univ : Finset (Fin 4)), 0 ≤ ((y' : E) j - e0 j) ^ 2 := by
          intro j _; positivity
        have h : ((y' : E) 0 - e0 0) ^ 2 ≤ ∑ i : Fin 4, ((y' : E) i - e0 i) ^ 2 :=
          Finset.single_le_sum h_nonneg (by simp)
        have h_e00 : e0 0 = 1 := by
          simp [e0, EuclideanSpace.single, PiLp.single_apply]
        rw [h_e00] at h
        linarith
      nlinarith
    have h_coord_bound : ∀ (i : Fin 4), |(y' : E) i| ≤ ‖(y' : E)‖ := by
      intro i
      have h2 : ((y' : E) i) ^ 2 ≤ ‖(y' : E)‖ ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq]
        have h_nonneg : ∀ j ∈ (Finset.univ : Finset (Fin 4)), 0 ≤ ((y' : E) j) ^ 2 := by
          intro j _; positivity
        have h3 : ((y' : E) i) ^ 2 ≤ ∑ j : Fin 4, ((y' : E) j) ^ 2 :=
          Finset.single_le_sum h_nonneg (by simp)
        exact h3
      have h4 : 0 ≤ ‖(y' : E)‖ := by positivity
      have h5 : |(y' : E) i| ^ 2 ≤ ‖(y' : E)‖ ^ 2 := by
        rw [sq_abs] <;> exact h2
      nlinarith [abs_nonneg ((y' : E) i)]
    have h_y0_upper : (y' : E) 0 ≤ 1 := by
      have h5 : |(y' : E) 0| ≤ ‖(y' : E)‖ := h_coord_bound 0
      rw [h_y_sphere] at h5
      have h6 : (y' : E) 0 ≤ |(y' : E) 0| := le_abs_self _
      linarith
    have h_yi_bound : ∀ i : Fin 3, |(y' : E) i.succ| ≤ r := by
      intro i
      have h_nonneg_terms : ∀ j : Fin 4, 0 ≤ ((y' : E) j - e0 j) ^ 2 := by intro j; positivity
      have h : ((y' : E) i.succ - e0 i.succ) ^ 2 ≤ r ^ 2 := by
        have h_nonneg : ∀ j ∈ (Finset.univ : Finset (Fin 4)), 0 ≤ ((y' : E) j - e0 j) ^ 2 := by
          intro j _; positivity
        have h' : ((y' : E) i.succ - e0 i.succ) ^ 2 ≤ ∑ j : Fin 4, ((y' : E) j - e0 j) ^ 2 :=
          Finset.single_le_sum h_nonneg (by simp)
        linarith
      have h_e0_succ : e0 i.succ = 0 := by
        simp [e0, EuclideanSpace.single, PiLp.single_apply]
        <;> fin_cases i <;> simp
      rw [h_e0_succ] at h
      have h_abs : |(y' : E) i.succ| ^ 2 ≤ r ^ 2 := by
        simpa [sq_abs] using h
      have h_r_nonneg : 0 ≤ r := by linarith
      nlinarith [abs_nonneg ((y' : E) i.succ)]
    have h_t_pos : 0 < t := ht.1
    have h_t_lt_one : t < 1 := ht.2
    have h_t_nonneg : 0 ≤ t := by linarith
    have h_t_le_one : t ≤ 1 := by linarith
    have h_z_coord : ∀ i : Fin 4, (WithLp.ofLp z) i = t * (y' : E) i := by
      intro i
      have h_z_eq : z = t • (y' : E) := hz_eq.symm
      rw [h_z_eq]
      have h_smul : WithLp.ofLp (t • (y' : E)) = t • WithLp.ofLp (y' : E) := by
        rw [WithLp.ofLp_smul]
        <;> rfl
      rw [h_smul]
      <;> rfl
    have h_yi_lower : ∀ i : Fin 3, -r ≤ (y' : E) i.succ := by
      intro i
      have h : |(y' : E) i.succ| ≤ r := h_yi_bound i
      exact (abs_le.mp h).1
    have h_yi_upper : ∀ i : Fin 3, (y' : E) i.succ ≤ r := by
      intro i
      have h : |(y' : E) i.succ| ≤ r := h_yi_bound i
      exact (abs_le.mp h).2
    have h_z0_lower : 0 ≤ t * (y' : E) 0 := by
      have h_y0_nonneg : 0 ≤ (y' : E) 0 := by linarith [h_y0_lower]
      exact mul_nonneg h_t_nonneg h_y0_nonneg
    have h_z0_upper : t * (y' : E) 0 ≤ 1 := by
      have h' : (y' : E) 0 ≤ 1 := h_y0_upper
      nlinarith
    have h_zi_lower : ∀ i : Fin 3, -r ≤ t * (y' : E) i.succ := by
      intro i
      nlinarith [h_yi_lower i, h_t_nonneg, h_t_le_one]
    have h_zi_upper : ∀ i : Fin 3, t * (y' : E) i.succ ≤ r := by
      intro i
      nlinarith [h_yi_upper i, h_t_nonneg, h_t_le_one]
    have h_z_ofLp : (WithLp.ofLp z) ∈ box' := by
      apply Set.mem_pi.mpr
      intro i _
      have h_i : (WithLp.ofLp z) i = t * (y' : E) i := h_z_coord i
      rw [h_i]
      fin_cases i
      · exact ⟨h_z0_lower, h_z0_upper⟩
      · exact ⟨h_zi_lower 0, h_zi_upper 0⟩
      · exact ⟨h_zi_lower 1, h_zi_upper 1⟩
      · exact ⟨h_zi_lower 2, h_zi_upper 2⟩
    simpa [box] using h_z_ofLp
  have h_box'_meas : MeasurableSet box' := by
    dsimp only [box']
    have h_count : (Set.univ : Set (Fin 4)).Countable := Set.to_countable _
    exact MeasurableSet.pi h_count (fun i _ => measurableSet_Icc)
  have h_pres : MeasurePreserving (WithLp.ofLp : E → (Fin 4 → ℝ)) :=
    PiLp.volume_preserving_ofLp (ι := Fin 4)
  have h_vol : volume box = ENNReal.ofReal (8 * r ^ 3) := by
    have h1 : volume box = volume box' :=
      h_pres.measure_preimage h_box'_meas.nullMeasurableSet
    rw [h1]
    dsimp only [box']
    rw [MeasureTheory.volume_pi_pi (fun i : Fin 4 => Set.Icc (a i) (b i))]
    have h_nonneg : 0 ≤ r := by linarith
    have h_ab : ∀ i : Fin 4, a i ≤ b i := by
      intro i; fin_cases i <;> simp [a, b] <;> linarith
    have h_vol_Icc : ∀ i : Fin 4, volume (Set.Icc (a i) (b i)) = ENNReal.ofReal (b i - a i) := by
      intro i
      rw [Real.volume_Icc]
      <;> linarith [h_ab i]
    rw [Finset.prod_congr rfl (fun i _ => h_vol_Icc i)]
    rw [Fin.prod_univ_four]
    have ha0 : a 0 = 0 := by simp [a]
    have ha1 : a 1 = -r := by simp [a]
    have ha2 : a 2 = -r := by simp [a]
    have ha3 : a 3 = -r := by simp [a]
    have hb0 : b 0 = 1 := by simp [b]
    have hb1 : b 1 = r := by simp [b]
    have hb2 : b 2 = r := by simp [b]
    have hb3 : b 3 = r := by simp [b]
    rw [ha0, ha1, ha2, ha3, hb0, hb1, hb2, hb3]
    have h_nonneg1 : 0 ≤ (1 - 0 : ℝ) := by norm_num
    have h_nonneg2 : 0 ≤ (r - (-r) : ℝ) := by linarith
    have h_nonneg3 : 0 ≤ ((1 - 0 : ℝ) * (r - (-r))) := by positivity
    have h_nonneg4 : 0 ≤ (((1 - 0 : ℝ) * (r - (-r))) * (r - (-r))) := by positivity
    have h_eq : (1 - 0 : ℝ) * (r - (-r)) * (r - (-r)) * (r - (-r)) = 8 * r ^ 3 := by ring
    calc
      ENNReal.ofReal (1 - 0) * ENNReal.ofReal (r - (-r)) * ENNReal.ofReal (r - (-r)) * ENNReal.ofReal (r - (-r))
        = (ENNReal.ofReal (1 - 0) * ENNReal.ofReal (r - (-r))) * (ENNReal.ofReal (r - (-r)) * ENNReal.ofReal (r - (-r))) := by ring
      _ = ENNReal.ofReal ((1 - 0) * (r - (-r))) * ENNReal.ofReal ((r - (-r)) * (r - (-r))) := by
        rw [← ENNReal.ofReal_mul h_nonneg1, ← ENNReal.ofReal_mul h_nonneg2] <;> ring
      _ = ENNReal.ofReal (((1 - 0) * (r - (-r))) * ((r - (-r)) * (r - (-r)))) := by
        rw [← ENNReal.ofReal_mul h_nonneg3] <;> ring
      _ = ENNReal.ofReal (8 * r ^ 3) := by
        congr 1 <;> ring
  have h4 : volume (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' Metric.closedBall e0' r)) ≤ volume box :=
    measure_mono h_box
  rw [h_vol] at h4
  have h5 : 4 * volume (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' Metric.closedBall e0' r)) ≤
      4 * ENNReal.ofReal (8 * r ^ 3) := by gcongr
  have h6 : 4 * ENNReal.ofReal (8 * r ^ 3) = ENNReal.ofReal (32 * r ^ 3) := by
    have h_cast : (4 : ENNReal) = ENNReal.ofReal (4 : ℝ) := by simp
    rw [h_cast]
    have h_mul : ENNReal.ofReal (4 : ℝ) * ENNReal.ofReal (8 * r ^ 3) =
        ENNReal.ofReal ((4 : ℝ) * (8 * r ^ 3)) := by
      rw [← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 4 by norm_num)]
      <;> ring
    rw [h_mul]
    <;> norm_cast <;> ring
  have h7 : volume.toSphere (Metric.closedBall e0' r) ≤ ENNReal.ofReal (32 * r ^ 3) := by
    rw [h_cone]
    rw [h6] at h5
    exact h5
  have h_norm : sphere3ProbabilityMeasure (Metric.closedBall x r) =
      (volume.toSphere (Set.univ : Set Sphere3))⁻¹ * volume.toSphere (Metric.closedBall x r) := by
    simp [sphere3ProbabilityMeasure, Measure.smul_apply]
  rw [h_norm]
  rw [h_main]
  have h8 : (volume.toSphere (Set.univ : Set Sphere3))⁻¹ * volume.toSphere (Metric.closedBall e0' r) ≤
      (volume.toSphere (Set.univ : Set Sphere3))⁻¹ * ENNReal.ofReal (32 * r ^ 3) := by
    gcongr
  have h9 : (volume.toSphere (Set.univ : Set Sphere3))⁻¹ * ENNReal.ofReal (32 * r ^ 3) =
      ENNReal.ofReal (32 * r ^ 3) * (volume.toSphere (Set.univ : Set Sphere3))⁻¹ := by
    apply mul_comm
  calc
    (volume.toSphere (Set.univ : Set Sphere3))⁻¹ * volume.toSphere (Metric.closedBall e0' r)
      ≤ (volume.toSphere (Set.univ : Set Sphere3))⁻¹ * ENNReal.ofReal (32 * r ^ 3) := h8
    _ = ENNReal.ofReal (32 * r ^ 3) * (volume.toSphere (Set.univ : Set Sphere3))⁻¹ := h9

end Kakeya.Streamlined.GeneralizedFrostman
