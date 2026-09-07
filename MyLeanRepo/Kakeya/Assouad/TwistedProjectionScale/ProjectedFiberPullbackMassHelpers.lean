import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberMassStatement
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# Helper lemmas for projected_fiber_pullback_mass
-/

noncomputable section

open MeasureTheory Set

namespace Kakeya.Assouad

/-- The shear map on Point3: (x, y, z) ↦ (x - f(z)*y, y, z). -/
private def twistedShear (f : SlopeFunction) (p : Point3) : Point3 :=
  point3 (p 0 - f (p 2) * p 1) (p 1) (p 2)

/-- The inverse shear: (x, y, z) ↦ (x + f(z)*y, y, z). -/
private def twistedShearInv (f : SlopeFunction) (p : Point3) : Point3 :=
  point3 (p 0 + f (p 2) * p 1) (p 1) (p 2)

-- ============================================================================
-- Coordinate-wise simp lemmas for twistedShear
-- ============================================================================

@[simp]
private lemma twistedShear_apply_zero (f : SlopeFunction) (p : Point3) :
    twistedShear f p (0 : Fin 3) = p 0 - f (p 2) * p 1 := by
  simp [twistedShear, point3, EuclideanSpace.single_apply]

@[simp]
private lemma twistedShear_apply_one (f : SlopeFunction) (p : Point3) :
    twistedShear f p (1 : Fin 3) = p 1 := by
  simp [twistedShear, point3, EuclideanSpace.single_apply]

@[simp]
private lemma twistedShear_apply_two (f : SlopeFunction) (p : Point3) :
    twistedShear f p (2 : Fin 3) = p 2 := by
  simp [twistedShear, point3, EuclideanSpace.single_apply]

@[simp]
private lemma twistedShearInv_apply_zero (f : SlopeFunction) (p : Point3) :
    twistedShearInv f p (0 : Fin 3) = p 0 + f (p 2) * p 1 := by
  simp [twistedShearInv, point3, EuclideanSpace.single_apply]

@[simp]
private lemma twistedShearInv_apply_one (f : SlopeFunction) (p : Point3) :
    twistedShearInv f p (1 : Fin 3) = p 1 := by
  simp [twistedShearInv, point3, EuclideanSpace.single_apply]

@[simp]
private lemma twistedShearInv_apply_two (f : SlopeFunction) (p : Point3) :
    twistedShearInv f p (2 : Fin 3) = p 2 := by
  simp [twistedShearInv, point3, EuclideanSpace.single_apply]

private lemma twistedShear_left_inv (f : SlopeFunction) :
    Function.LeftInverse (twistedShearInv f) (twistedShear f) := by
  intro p
  ext i
  fin_cases i <;> simp <;> ring

private lemma twistedShear_right_inv (f : SlopeFunction) :
    Function.RightInverse (twistedShearInv f) (twistedShear f) := by
  intro p
  ext i
  fin_cases i <;> simp <;> ring

-- ============================================================================
-- Coordinate equivalence Point3 ≃ᵐ (ℝ × ℝ) × ℝ
-- ============================================================================

private def point3ToProd : Point3 ≃ᵐ (ℝ × ℝ) × ℝ :=
  let toLp3 : Point3 ≃ᵐ (Fin 3 → ℝ) :=
    { toFun := @WithLp.ofLp (2 : ENNReal) (Fin 3 → ℝ)
      invFun := @WithLp.toLp (2 : ENNReal) (Fin 3 → ℝ)
      left_inv := WithLp.toLp_ofLp (p := (2 : ENNReal))
      right_inv := WithLp.ofLp_toLp (p := (2 : ENNReal))
      measurable_toFun := (PiLp.continuous_ofLp (p := (2 : ENNReal)) (β := fun _ : Fin 3 => ℝ)).measurable
      measurable_invFun := (PiLp.continuous_toLp (p := (2 : ENNReal)) (β := fun _ : Fin 3 => ℝ)).measurable }
  let e1 : (Fin 3 → ℝ) ≃ᵐ ℝ × (Fin 2 → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun (_ : Fin 3) => ℝ) 0
  let e2 : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ :=
    MeasurableEquiv.piFinTwo (fun (_ : Fin 2) => ℝ)
  let e3 : (ℝ × (Fin 2 → ℝ)) ≃ᵐ ℝ × (ℝ × ℝ) :=
    (MeasurableEquiv.refl ℝ).prodCongr e2
  let e4 : (ℝ × (ℝ × ℝ)) ≃ᵐ (ℝ × ℝ) × ℝ :=
    { toFun := Prod.swap
      invFun := Prod.swap
      left_inv := by intro x; simp
      right_inv := by intro x; simp
      measurable_toFun := measurable_snd.prodMk measurable_fst
      measurable_invFun := measurable_snd.prodMk measurable_fst }
  toLp3.trans e1 |>.trans e3 |>.trans e4

private lemma point3ToProd_apply (p : Point3) :
    point3ToProd p = ((p 1, p 2), p 0) := by
  ext <;> simp [point3ToProd, MeasurableEquiv.piFinSuccAbove_apply,
    MeasurableEquiv.piFinTwo_apply, Fin.succAbove] <;> aesop

private lemma point3ToProd_symm_apply (yzx : (ℝ × ℝ) × ℝ) :
    point3ToProd.symm yzx = point3 yzx.2 yzx.1.1 yzx.1.2 := by
  ext i; fin_cases i <;> simp [point3ToProd, point3, EuclideanSpace.single_apply,
    MeasurableEquiv.piFinSuccAbove_apply,
    MeasurableEquiv.piFinTwo_apply, Fin.succAbove] <;> aesop

private lemma point3ToProd_measurePreserving :
    MeasurePreserving point3ToProd volume volume := by
  have h_toLp : MeasurePreserving (@WithLp.ofLp (2 : ENNReal) (Fin 3 → ℝ)) volume volume :=
    PiLp.volume_preserving_ofLp (ι := Fin 3)
  have h_e1 : MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun (_ : Fin 3) => ℝ) 0) volume volume :=
    volume_preserving_piFinSuccAbove (fun (_ : Fin 3) => ℝ) 0
  have h_e2 : MeasurePreserving (MeasurableEquiv.piFinTwo (fun (_ : Fin 2) => ℝ)) volume volume :=
    volume_preserving_piFinTwo (fun (_ : Fin 2) => ℝ)
  have h_e3 : MeasurePreserving ((MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.piFinTwo (fun (_ : Fin 2) => ℝ))) volume volume := by
    have hvol : (volume : Measure (ℝ × (Fin 2 → ℝ))) = volume.prod volume := Measure.volume_eq_prod _ _
    have h : MeasurePreserving (Prod.map (id : ℝ → ℝ) (MeasurableEquiv.piFinTwo (fun (_ : Fin 2) => ℝ))) (volume.prod volume) (volume.prod volume) :=
      MeasurePreserving.prod (MeasurePreserving.id (volume : Measure ℝ)) h_e2
    rw [hvol] at *
    exact h
  have h_e4 : MeasurePreserving (Prod.swap : (ℝ × (ℝ × ℝ)) → (ℝ × ℝ) × ℝ) volume volume := by
    have hvol : (volume : Measure (ℝ × (ℝ × ℝ))) = volume.prod volume := Measure.volume_eq_prod _ _
    refine ⟨measurable_snd.prodMk measurable_fst, ?_⟩
    rw [hvol]
    exact Measure.measurePreserving_swap.map_eq
  exact h_e4.comp (h_e3.comp (h_e1.comp h_toLp))

-- ============================================================================
-- Shear on product space and measure-preserving proof
-- ============================================================================

private def prodShear (f : SlopeFunction) (yzx : (ℝ × ℝ) × ℝ) : (ℝ × ℝ) × ℝ :=
  (yzx.1, yzx.2 - f yzx.1.2 * yzx.1.1)

private lemma prodShear_measurePreserving (f : SlopeFunction) :
    MeasurePreserving (prodShear f) volume volume := by
  let hf_cont : Continuous f := f.contDiff.continuous
  let g : (ℝ × ℝ) → ℝ → ℝ := fun yz x => x - f yz.2 * yz.1
  have hgm : Measurable (Function.uncurry g) := by fun_prop
  have hg : ∀ (yz : ℝ × ℝ), Measure.map (g yz) volume = volume := by
    intro yz
    exact (measurePreserving_add_right volume (-(f yz.2 * yz.1))).map_eq
  exact (MeasurePreserving.id (volume.prod volume)).skew_product hgm
    (Filter.Eventually.of_forall hg)

private lemma twistedShear_measurePreserving (f : SlopeFunction) :
    MeasurePreserving (twistedShear f) volume volume := by
  have h1 : MeasurePreserving point3ToProd volume volume :=
    point3ToProd_measurePreserving
  have h2 : MeasurePreserving (prodShear f) volume volume :=
    prodShear_measurePreserving f
  have h3 : MeasurePreserving point3ToProd.symm volume volume := h1.symm
  have h4 : twistedShear f = point3ToProd.symm ∘ prodShear f ∘ point3ToProd := by
    funext p
    have h5 : point3ToProd p = ((p 1, p 2), p 0) := point3ToProd_apply p
    simp only [h5, Function.comp_apply]
    ext i; fin_cases i <;> simp [twistedShear, prodShear,
      point3ToProd_symm_apply, point3, EuclideanSpace.single_apply] <;> ring
  rw [h4]
  exact h3.comp (h2.comp h1)

-- ============================================================================
-- Coordinate equivalence Point2 × ℝ ≃ᵐ Point3
-- ============================================================================

private def coordEquiv : Point2 × ℝ ≃ᵐ Point3 :=
  let toLp2 : Point2 ≃ᵐ (Fin 2 → ℝ) :=
    { toFun := @WithLp.ofLp (2 : ENNReal) (Fin 2 → ℝ)
      invFun := @WithLp.toLp (2 : ENNReal) (Fin 2 → ℝ)
      left_inv := WithLp.toLp_ofLp (p := (2 : ENNReal))
      right_inv := WithLp.ofLp_toLp (p := (2 : ENNReal))
      measurable_toFun := (PiLp.continuous_ofLp (p := (2 : ENNReal)) (β := fun _ : Fin 2 => ℝ)).measurable
      measurable_invFun := (PiLp.continuous_toLp (p := (2 : ENNReal)) (β := fun _ : Fin 2 => ℝ)).measurable }
  let e_comm : Point2 × ℝ ≃ᵐ ℝ × Point2 :=
    { toFun := Prod.swap
      invFun := Prod.swap
      left_inv := by intro x; simp
      right_inv := by intro x; simp
      measurable_toFun := measurable_snd.prodMk measurable_fst
      measurable_invFun := measurable_snd.prodMk measurable_fst }
  let e_toLp : (ℝ × Point2) ≃ᵐ ℝ × (Fin 2 → ℝ) :=
    (MeasurableEquiv.refl ℝ).prodCongr toLp2
  let e_pi : (ℝ × (Fin 2 → ℝ)) ≃ᵐ (Fin 3 → ℝ) :=
    (MeasurableEquiv.piFinSuccAbove (fun (_ : Fin 3) => ℝ) 1).symm
  let toLp3 : (Fin 3 → ℝ) ≃ᵐ Point3 :=
    { toFun := @WithLp.toLp (2 : ENNReal) (Fin 3 → ℝ)
      invFun := @WithLp.ofLp (2 : ENNReal) (Fin 3 → ℝ)
      left_inv := WithLp.ofLp_toLp (p := (2 : ENNReal))
      right_inv := WithLp.toLp_ofLp (p := (2 : ENNReal))
      measurable_toFun := (PiLp.continuous_toLp (p := (2 : ENNReal)) (β := fun _ : Fin 3 => ℝ)).measurable
      measurable_invFun := (PiLp.continuous_ofLp (p := (2 : ENNReal)) (β := fun _ : Fin 3 => ℝ)).measurable }
  e_comm.trans e_toLp |>.trans e_pi |>.trans toLp3

private lemma coordEquiv_apply (q : Point2) (y : ℝ) :
    coordEquiv (q, y) = point3 (q 0) y (q 1) := by
  ext i; fin_cases i <;> simp [coordEquiv, point3, EuclideanSpace.single_apply,
    MeasurableEquiv.piFinSuccAbove_apply,
    MeasurableEquiv.piFinTwo_apply, Fin.succAbove] <;> aesop

private lemma coordEquiv_measurePreserving :
    MeasurePreserving coordEquiv volume volume := by
  let toLp2_map : Point2 → (Fin 2 → ℝ) := @WithLp.ofLp (2 : ENNReal) (Fin 2 → ℝ)
  have h_comm : MeasurePreserving (Prod.swap : Point2 × ℝ → ℝ × Point2) volume volume := by
    have hvol : (volume : Measure (Point2 × ℝ)) = volume.prod volume := Measure.volume_eq_prod _ _
    refine ⟨measurable_snd.prodMk measurable_fst, ?_⟩
    rw [hvol]
    exact Measure.measurePreserving_swap.map_eq
  have h_toLp2 : MeasurePreserving toLp2_map volume volume :=
    PiLp.volume_preserving_ofLp (ι := Fin 2)
  have h_id : MeasurePreserving (id : ℝ → ℝ) volume volume := MeasurePreserving.id volume
  have h_prod : MeasurePreserving (Prod.map (id : ℝ → ℝ) toLp2_map) (volume.prod volume) (volume.prod volume) :=
    MeasurePreserving.prod h_id h_toLp2
  have h_e_toLp : MeasurePreserving (Prod.map (id : ℝ → ℝ) toLp2_map) volume volume := by
    simpa [Measure.volume_eq_prod] using h_prod
  have h_e1 : MeasurePreserving ((MeasurableEquiv.piFinSuccAbove (fun (_ : Fin 3) => ℝ) 1).symm) volume volume :=
    (volume_preserving_piFinSuccAbove (fun (_ : Fin 3) => ℝ) 1).symm
  have h_toLp3 : MeasurePreserving (@WithLp.toLp (2 : ENNReal) (Fin 3 → ℝ)) volume volume :=
    PiLp.volume_preserving_toLp (ι := Fin 3)
  exact h_toLp3.comp (h_e1.comp (h_e_toLp.comp h_comm))

-- ============================================================================
-- Full fiber equivalence
-- ============================================================================

private def fiberEquiv (f : SlopeFunction) : Point2 × ℝ → Point3 :=
  twistedShear f ∘ coordEquiv

private lemma fiberEquiv_apply (f : SlopeFunction) (q : Point2) (y : ℝ) :
    fiberEquiv f (q, y) = point3 (q 0 - f (q 1) * y) y (q 1) := by
  ext i; fin_cases i <;> simp [fiberEquiv, coordEquiv_apply, twistedShear,
    point3, EuclideanSpace.single_apply] <;> ring

private lemma point3_continuous :
    Continuous (fun t : ℝ × ℝ × ℝ => point3 t.1 t.2.1 t.2.2) := by
  have h1 : Continuous (fun t : ℝ × ℝ × ℝ => t.1 • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) :=
    continuous_fst.smul continuous_const
  have h2 : Continuous (fun t : ℝ × ℝ × ℝ => t.2.1 • EuclideanSpace.single (1 : Fin 3) (1 : ℝ)) :=
    (continuous_snd.fst).smul continuous_const
  have h3 : Continuous (fun t : ℝ × ℝ × ℝ => t.2.2 • EuclideanSpace.single (2 : Fin 3) (1 : ℝ)) :=
    (continuous_snd.snd).smul continuous_const
  convert h1.add (h2.add h3) using 1
  funext t
  simp [point3]
  <;> abel

private lemma twistedShear_continuous (f : SlopeFunction) :
    Continuous (twistedShear f) := by
  have hf : Continuous f := f.contDiff.continuous
  have h0 : Continuous (fun p : Point3 => p (0 : Fin 3)) := PiLp.continuous_apply 2 _ 0
  have h1 : Continuous (fun p : Point3 => p (1 : Fin 3)) := PiLp.continuous_apply 2 _ 1
  have h2 : Continuous (fun p : Point3 => p (2 : Fin 3)) := PiLp.continuous_apply 2 _ 2
  have hx : Continuous (fun p : Point3 => p 0 - f (p 2) * p 1) := by fun_prop
  have h_pair : Continuous (fun p : Point3 => (p 1, p 2)) := h1.prodMk h2
  have h_main : Continuous (fun p : Point3 => (p 0 - f (p 2) * p 1, (p 1, p 2))) :=
    hx.prodMk h_pair
  have h_eq : (twistedShear f) = (fun p => point3 (p 0 - f (p 2) * p 1) (p 1) (p 2)) := by
    funext p
    ext i
    fin_cases i <;> simp [twistedShear, point3, EuclideanSpace.single_apply] <;> ring
  rw [h_eq]
  convert point3_continuous.comp h_main using 1
  funext p
  <;> rfl

private lemma fiberEquiv_measurable (f : SlopeFunction) :
    Measurable (fiberEquiv f) :=
  (twistedShear_continuous f).measurable.comp coordEquiv.measurable

private lemma fiberEquiv_measurePreserving (f : SlopeFunction) :
    MeasurePreserving (fiberEquiv f) volume volume :=
  (twistedShear_measurePreserving f).comp coordEquiv_measurePreserving

private lemma twistedProjection_fiberEquiv
    (f : SlopeFunction) (q : Point2) (y : ℝ) :
    twistedProjection f (fiberEquiv f (q, y)) = q := by
  rw [fiberEquiv_apply]
  ext i
  fin_cases i
  · simp [twistedProjection, point3, EuclideanSpace.single_apply] <;> ring
  · simp [twistedProjection, point3, EuclideanSpace.single_apply]

private lemma fiberEquiv_preimage (f : SlopeFunction) (X : Set Point2) :
    (fiberEquiv f) ⁻¹' (twistedProjection f ⁻¹' X) = X ×ˢ Set.univ := by
  ext ⟨q, y⟩
  simp only [Set.mem_preimage, Set.mem_prod, Set.mem_univ, true_and]
  have h : twistedProjection f (fiberEquiv f (q, y)) = q :=
    twistedProjection_fiberEquiv f q y
  rw [h]
  <;> simp

-- ============================================================================
-- Main identity
-- ============================================================================

lemma projectedFiberPullbackMass_identity
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    (Y : Kakeya.Streamlined.TubeShading F)
    (f : SlopeFunction) (X : Set Point2) (hX : MeasurableSet X) :
    ∫⁻ p in (twistedProjection f ⁻¹' X), (Y.pointMultiplicity p : ENNReal) =
      ∫⁻ q in X, projectedFiberMultiplicity Y f q := by
  let m : Point3 → ENNReal := fun p => (Y.pointMultiplicity p : ENNReal)
  have h_coe : Measurable (fun n : ℕ => (n : ENNReal)) := measurable_from_nat
  have hm : Measurable m := h_coe.comp (measurable_pointMultiplicity Y)
  let e := fiberEquiv f
  have hmp : MeasurePreserving e volume volume :=
    fiberEquiv_measurePreserving f
  have hS : MeasurableSet (twistedProjection f ⁻¹' X) :=
    hX.preimage (continuous_twistedProjection f).measurable
  have hpreimg : e ⁻¹' (twistedProjection f ⁻¹' X) = X ×ˢ Set.univ :=
    fiberEquiv_preimage f X
  let g : Point2 × ℝ → ENNReal := fun z => m (e z)
  have hg : Measurable g := hm.comp (fiberEquiv_measurable f)
  have h1 : ∫⁻ z in e ⁻¹' (twistedProjection f ⁻¹' X), g z =
      ∫⁻ p in (twistedProjection f ⁻¹' X), m p :=
    hmp.setLIntegral_comp_preimage hS hm
  have h3 : ∫⁻ z in (X ×ˢ Set.univ), g z =
      ∫⁻ q in X, ∫⁻ y in (Set.univ : Set ℝ), g (q, y) :=
    MeasureTheory.setLIntegral_prod g hg.aemeasurable
  let f1 : Point2 → ENNReal := fun q => ∫⁻ y in (Set.univ : Set ℝ), g (q, y)
  let f2 : Point2 → ENNReal := fun q => ∫⁻ y : ℝ, g (q, y)
  have h_eq1 : Set.EqOn f1 f2 X := by
    intro q _
    exact MeasureTheory.setLIntegral_univ (f := fun y : ℝ => g (q, y))
  have h4 : ∫⁻ q in X, f1 q = ∫⁻ q in X, f2 q :=
    MeasureTheory.setLIntegral_congr_fun hX h_eq1
  let f3 : Point2 → ENNReal := fun q => ∫⁻ y : ℝ, g (q, y)
  let f4 : Point2 → ENNReal := fun q => projectedFiberMultiplicity Y f q
  have h_eq2 : Set.EqOn f3 f4 X := by
    intro q _
    rfl
  have h6 : ∫⁻ q in X, f3 q = ∫⁻ q in X, f4 q :=
    MeasureTheory.setLIntegral_congr_fun hX h_eq2
  rw [hpreimg] at h1
  rw [h3, h4] at h1
  exact h1.symm.trans h6

end Kakeya.Assouad
