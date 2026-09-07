import MyLeanRepo.Kakeya.Assouad.Definitions
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Cylinder volume computation

Computes the volume of a right circular cylinder in R^3 using
product measure decomposition via coordinate rearrangement.
-/

noncomputable section

open MeasureTheory Metric Set

namespace Kakeya.Assouad

/-- Index equivalence: Fin 3 ≃ Fin 1 ⊕ Fin 2. -/
private def e_idx : Fin 3 ≃ Sum (Fin 1) (Fin 2) :=
  { toFun := fun i =>
      match i with
      | 0 => Sum.inl 0
      | 1 => Sum.inr 0
      | 2 => Sum.inr 1
    invFun := fun s =>
      match s with
      | Sum.inl _ => 0
      | Sum.inr 0 => 1
      | Sum.inr 1 => 2
    left_inv := by intro i; fin_cases i <;> simp
    right_inv := by
      intro s; cases s with
      | inl i => fin_cases i <;> simp
      | inr j => fin_cases j <;> simp }

/-- Standard cylinder: disk of radius r in coords 1,2 and length L in coord 0. -/
def stdCylinder (r L : ℝ) : Set Point3 :=
  {x | (x 1)^2 + (x 2)^2 ≤ r^2 ∧ 0 ≤ x 0 ∧ x 0 ≤ L}

/-- Volume of a cylinder of radius `r` and length `L`. -/
lemma volume_stdCylinder (r L : ℝ) (hr : 0 ≤ r) (hL : 0 ≤ L) :
    volume (stdCylinder r L) = ENNReal.ofReal (Real.pi * r^2 * L) := by
  -- WithLp equivalence (Fin 3 → ℝ) ≃ᵐ Point3
  let toLp3 : (Fin 3 → ℝ) ≃ᵐ Point3 :=
    { toFun := @WithLp.toLp (2 : ENNReal) (Fin 3 → ℝ)
      invFun := @WithLp.ofLp (2 : ENNReal) (Fin 3 → ℝ)
      left_inv := WithLp.ofLp_toLp (p := (2 : ENNReal))
      right_inv := WithLp.toLp_ofLp (p := (2 : ENNReal))
      measurable_toFun := (PiLp.continuous_toLp (p := (2 : ENNReal)) (β := fun _ : Fin 3 => ℝ)).measurable
      measurable_invFun := (PiLp.continuous_ofLp (p := (2 : ENNReal)) (β := fun _ : Fin 3 => ℝ)).measurable }
  have hmp_toLp3 : MeasurePreserving toLp3 volume volume :=
    PiLp.volume_preserving_toLp (ι := Fin 3)

  -- Index rearrangement
  let e_rearr : (Fin 3 → ℝ) ≃ᵐ (Sum (Fin 1) (Fin 2) → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : Sum (Fin 1) (Fin 2) => ℝ) e_idx
  have hmp_rearr : MeasurePreserving e_rearr volume volume :=
    MeasureTheory.measurePreserving_piCongrLeft (fun _ => volume) e_idx

  -- Sum to product split
  let e_split : (Sum (Fin 1) (Fin 2) → ℝ) ≃ᵐ ((Fin 1 → ℝ) × (Fin 2 → ℝ)) :=
    MeasurableEquiv.sumPiEquivProdPi (fun _ => ℝ)
  have hmp_split : MeasurePreserving e_split volume volume :=
    MeasureTheory.measurePreserving_sumPiEquivProdPi (fun _ => volume)

  -- Fin 1 → ℝ ≃ᵐ ℝ
  let e_uniq : (Fin 1 → ℝ) ≃ᵐ ℝ :=
    MeasurableEquiv.piUnique (fun _ : Fin 1 => ℝ)
  have hmp_uniq : MeasurePreserving e_uniq volume volume :=
    MeasureTheory.measurePreserving_piUnique (fun _ => volume)

  -- Product map
  let e_prod : ((Fin 1 → ℝ) × (Fin 2 → ℝ)) ≃ᵐ (ℝ × (Fin 2 → ℝ)) :=
    e_uniq.prodCongr (MeasurableEquiv.refl _)
  have hmp_id : MeasurePreserving (id : (Fin 2 → ℝ) → (Fin 2 → ℝ)) volume volume :=
    MeasurePreserving.id volume
  have hmp_prod : MeasurePreserving e_prod volume volume :=
    MeasureTheory.MeasurePreserving.prod hmp_uniq hmp_id

  -- WithLp for Point2
  let toLp2 : (Fin 2 → ℝ) ≃ᵐ Point2 :=
    { toFun := @WithLp.toLp (2 : ENNReal) (Fin 2 → ℝ)
      invFun := @WithLp.ofLp (2 : ENNReal) (Fin 2 → ℝ)
      left_inv := WithLp.ofLp_toLp (p := (2 : ENNReal))
      right_inv := WithLp.toLp_ofLp (p := (2 : ENNReal))
      measurable_toFun := (PiLp.continuous_toLp (p := (2 : ENNReal)) (β := fun _ : Fin 2 => ℝ)).measurable
      measurable_invFun := (PiLp.continuous_ofLp (p := (2 : ENNReal)) (β := fun _ : Fin 2 => ℝ)).measurable }
  have hmp_toLp2 : MeasurePreserving toLp2 volume volume :=
    PiLp.volume_preserving_toLp (ι := Fin 2)

  -- Final product map
  let e_final : (ℝ × (Fin 2 → ℝ)) ≃ᵐ (ℝ × Point2) :=
    (MeasurableEquiv.refl ℝ).prodCongr toLp2
  have hmp_id2 : MeasurePreserving (id : ℝ → ℝ) volume volume :=
    MeasurePreserving.id volume
  have hmp_final : MeasurePreserving e_final volume volume :=
    MeasureTheory.MeasurePreserving.prod hmp_id2 hmp_toLp2

  -- Compose all
  let e_pi : (Fin 3 → ℝ) ≃ᵐ (ℝ × (Fin 2 → ℝ)) :=
    e_rearr.trans (e_split.trans e_prod)
  have hmp_pi : MeasurePreserving e_pi volume volume :=
    hmp_prod.comp (hmp_split.comp hmp_rearr)

  let e : Point3 ≃ᵐ (ℝ × Point2) :=
    toLp3.symm.trans (e_pi.trans e_final)
  have hmp : MeasurePreserving e volume volume :=
    hmp_final.comp (hmp_pi.comp (hmp_toLp3.symm toLp3))

  -- Action of e_pi: prove by extensionality
  have h_rearr_apply : ∀ (f : Fin 3 → ℝ) (s : Sum (Fin 1) (Fin 2)),
      e_rearr f s = f (e_idx.symm s) := by
    intro f s
    cases s with
    | inl j =>
      fin_cases j <;> simp [e_rearr, MeasurableEquiv.piCongrLeft] <;> rfl
    | inr j =>
      fin_cases j <;> simp [e_rearr, MeasurableEquiv.piCongrLeft] <;> rfl
  have h_split_apply : ∀ (g : Sum (Fin 1) (Fin 2) → ℝ),
      e_split g = (g ∘ Sum.inl, g ∘ Sum.inr) := by
    intro g
    exact Prod.ext rfl rfl
  have h_uniq_apply : ∀ (h : Fin 1 → ℝ), e_uniq h = h 0 := by
    intro h
    simp [e_uniq, MeasurableEquiv.piUnique]
    <;> rfl
  have h_pi_apply : ∀ (f : Fin 3 → ℝ), e_pi f = (f 0, ![f 1, f 2]) := by
    intro f
    have h1 : e_split (e_rearr f) = ((e_rearr f) ∘ Sum.inl, (e_rearr f) ∘ Sum.inr) :=
      h_split_apply (e_rearr f)
    have h2 : e_uniq ((e_rearr f) ∘ Sum.inl) = f 0 := by
      rw [h_uniq_apply]
      have h5 : ((e_rearr f) ∘ Sum.inl) 0 = e_rearr f (Sum.inl 0) := by rfl
      rw [h5, h_rearr_apply f (Sum.inl 0)] <;> rfl
    have h3 : (e_rearr f) ∘ Sum.inr = ![f 1, f 2] := by
      ext i
      fin_cases i <;> simp [h_rearr_apply, Function.comp_apply] <;> rfl
    have h41 : e_prod (e_split (e_rearr f)) =
        (e_uniq ((e_rearr f) ∘ Sum.inl), (e_rearr f) ∘ Sum.inr) := by
      rw [h1]
      <;> simp [e_prod, MeasurableEquiv.prodCongr]
      <;> rfl
    have h4 : e_prod (e_split (e_rearr f)) = (f 0, ![f 1, f 2]) := by
      rw [h41, h2, h3] <;> rfl
    simpa [e_pi, MeasurableEquiv.trans_apply] using h4

  -- Action of e
  have h_apply : ∀ (x : Point3),
      e x = (x 0, @WithLp.toLp (2 : ENNReal) (Fin 2 → ℝ) ![x 1, x 2]) := by
    intro x
    have h1 : e x = e_final (e_pi (toLp3.symm x)) := by
      rfl
    rw [h1, h_pi_apply]
    have h2 : (toLp3.symm x) 0 = x 0 := by rfl
    have h3 : (toLp3.symm x) 1 = x 1 := by rfl
    have h4 : (toLp3.symm x) 2 = x 2 := by rfl
    rw [h2, h3, h4]
    <;> rfl

  -- Image of cylinder
  let disk : Set Point2 := Metric.closedBall 0 r
  let interval : Set ℝ := Set.Icc 0 L

  have h_image : e '' stdCylinder r L = interval ×ˢ disk := by
    ext ⟨z, y⟩
    simp only [Set.mem_image, Set.mem_prod]
    constructor
    · rintro ⟨x, hx, h_eq⟩
      have h1 : (x 1)^2 + (x 2)^2 ≤ r^2 := hx.1
      have h2 : 0 ≤ x 0 := hx.2.1
      have h3 : x 0 ≤ L := hx.2.2
      have h_apply_x : e x = (x 0, @WithLp.toLp (2 : ENNReal) (Fin 2 → ℝ) ![x 1, x 2]) := h_apply x
      have hz : (e x).1 = x 0 := by rw [h_apply_x] <;> rfl
      have hy : ‖(e x).2‖ ≤ r := by
        rw [h_apply_x]
        simp [EuclideanSpace.norm_eq]
        have hsqrt : Real.sqrt ((x 1)^2 + (x 2)^2) ≤ Real.sqrt (r^2) := Real.sqrt_le_sqrt h1
        have hsq : Real.sqrt (r^2) = r := Real.sqrt_sq hr
        rw [hsq] at hsqrt
        exact hsqrt
      have h_goal : (e x).1 ∈ interval ∧ (e x).2 ∈ disk := by
        exact ⟨⟨h2, h3⟩, by simpa [disk, Metric.mem_closedBall] using hy⟩
      rw [h_eq] at h_goal
      exact h_goal
    · rintro ⟨h1, h2⟩
      let x : Point3 := e.symm (z, y)
      have h_eq2 : e x = (z, y) := by simp [x]
      have hz : x 0 = z := by
        rw [h_apply x] at h_eq2
        exact congr_arg Prod.fst h_eq2
      have hy : (x 1)^2 + (x 2)^2 ≤ r^2 := by
        rw [h_apply x] at h_eq2
        have h' : @WithLp.toLp (2 : ENNReal) (Fin 2 → ℝ) ![x 1, x 2] = y :=
          congr_arg Prod.snd h_eq2
        have h'' : ‖y‖ ≤ r := by simpa [disk, Metric.mem_closedBall] using h2
        have h3 : (x 1)^2 + (x 2)^2 = ‖y‖ ^ 2 := by
          have h41 : ‖@WithLp.toLp (2 : ENNReal) (Fin 2 → ℝ) ![x 1, x 2]‖ =
              Real.sqrt ((x 1)^2 + (x 2)^2) := by
            simp [EuclideanSpace.norm_eq] <;> rfl
          have h4 : ‖@WithLp.toLp (2 : ENNReal) (Fin 2 → ℝ) ![x 1, x 2]‖ ^ 2 = (x 1)^2 + (x 2)^2 := by
            rw [h41, Real.sq_sqrt (by positivity)]
          rw [h'] at h4
          exact h4.symm
        have h5 : ‖y‖ ^ 2 ≤ r ^ 2 := by gcongr
        linarith
      refine ⟨x, ?_, ?_⟩
      · exact ⟨hy, by linarith [hz, h1.1], by linarith [hz, h1.2]⟩
      · simp [x]

  -- Volume computation
  have h11 : Measurable (fun x : Point3 => (x 1)^2 + (x 2)^2) := by fun_prop
  have h21 : Measurable (fun x : Point3 => x 0) := by fun_prop
  have h_meas : MeasurableSet (stdCylinder r L) := by
    have h1 : MeasurableSet {x : Point3 | (x 1)^2 + (x 2)^2 ≤ r^2} :=
      measurableSet_le h11 (by fun_prop)
    have h2 : MeasurableSet {x : Point3 | 0 ≤ x 0 ∧ x 0 ≤ L} :=
      h21 measurableSet_Icc
    exact h1.inter h2
  have hmp_symm : MeasurePreserving e.symm volume volume := hmp.symm e
  have h_img_eq : e '' stdCylinder r L = e.symm ⁻¹' (stdCylinder r L) := by
    ext z
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨x, hx, h_eq⟩
      rw [←h_eq]
      simpa using hx
    · intro hz
      exact ⟨e.symm z, hz, e.apply_symm_apply z⟩
  have h_vol : volume (e '' stdCylinder r L) = volume (stdCylinder r L) := by
    rw [h_img_eq]
    exact hmp_symm.measure_preimage h_meas.nullMeasurableSet
  rw [←h_vol, h_image]

  have h_prod : volume (interval ×ˢ disk) = volume interval * volume disk := by
    rw [MeasureTheory.Measure.volume_eq_prod ℝ Point2]
    exact Measure.prod_prod interval disk

  rw [h_prod]

  have h_int : volume interval = ENNReal.ofReal L := by
    rw [Real.volume_Icc, sub_zero] <;> simp [hL]

  have h_disk : volume disk = ENNReal.ofReal (Real.pi * r^2) := by
    have h := EuclideanSpace.volume_closedBall_fin_two (0 : Point2) r
    have h2 : volume disk = ENNReal.ofReal r ^ 2 * ENNReal.ofReal Real.pi := by
      simpa [disk] using h
    rw [h2]
    have h3 : ENNReal.ofReal r ^ 2 = ENNReal.ofReal (r^2) := by
      rw [← ENNReal.ofReal_pow hr] <;> ring
    rw [h3]
    rw [← ENNReal.ofReal_mul] <;> ring_nf <;> positivity

  rw [h_int, h_disk]
  have h4 : ENNReal.ofReal L * ENNReal.ofReal (Real.pi * r^2) =
      ENNReal.ofReal (Real.pi * r^2 * L) := by
    rw [← ENNReal.ofReal_mul] <;> ring_nf <;> positivity
  exact h4

end Kakeya.Assouad
