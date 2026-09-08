import MyLeanRepo.Kakeya.Streamlined.FactoringMultiplicityRegularization.Proof
import MyLeanRepo.Kakeya.Streamlined.ExactInducedShadingCompatibility.Proof
import MyLeanRepo.Kakeya.Streamlined.RhoTubeMultiplicity.LogLoss
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Induced coarse shading construction and regularization

Given a tube cover and fine shading, construct the exact induced coarse shading
at radius `rho`, apply simultaneous factoring multiplicity regularization, and
convert the logarithmic mass retention to polynomial form.

Whiteprint node: `rho-tube-induced-shading`.
-/

noncomputable section

namespace Kakeya.Streamlined

/--
Construct the exact induced coarse shading at radius `r` for a fine shading.
-/
def inducedShading {fine coarse : BodyFamily} (P : Factoring fine coarse)
    (Y : Shading fine) (r : ℝ) (hcoarse_meas : coarse.IsMeasurable) :
    Shading coarse where
  carrier j := (coarse.body j).carrier ∩
    Metric.cthickening r {x | ∃ i : Fin fine.card, P.parent i = j ∧ x ∈ Y.carrier i}
  measurable_carrier j := by
    let S : Finset (Fin fine.card) := P.fiberIndices j
    have h_eq : {x | ∃ i : Fin fine.card, P.parent i = j ∧ x ∈ Y.carrier i} =
        ⋃ i ∈ S, Y.carrier i := by
      ext x
      simp [S, Factoring.fiberIndices, Finset.mem_filter]
      <;> tauto
    rw [h_eq]
    have h1 : MeasurableSet (coarse.body j).carrier := by
      exact MeasurableSet.congr (hcoarse_meas j) rfl
    let ι : Type _ := {i : Fin fine.card // i ∈ S}
    have h_eq2 : (⋃ i ∈ S, Y.carrier i) = ⋃ (i : ι), Y.carrier i.val := by
      ext x
      simp only [Set.mem_biUnion, Set.mem_iUnion]
      constructor
      · rintro ⟨i, hi, hx⟩
        exact ⟨⟨i, hi⟩, hx⟩
      · rintro ⟨i, hx⟩
        exact ⟨i.val, i.property, hx⟩
    rw [h_eq2]
    have hS_meas : MeasurableSet (⋃ (i : ι), Y.carrier i.val) :=
      MeasurableSet.iUnion (fun (i : ι) => Y.measurable_carrier i.val)
    have h_cont : Continuous (fun x : Point3 => Metric.infEDist x (⋃ (i : ι), Y.carrier i.val)) :=
      Metric.continuous_infEDist
    have h_closed : IsClosed (Metric.cthickening r (⋃ (i : ι), Y.carrier i.val)) := by
      rw [Metric.cthickening_eq_preimage_infEDist]
      exact IsClosed.preimage h_cont isClosed_Iic
    have h4 : MeasurableSet (Metric.cthickening r (⋃ (i : ι), Y.carrier i.val)) :=
      h_closed.measurableSet
    exact h1.inter h4
  subset_body j := Set.inter_subset_left

/--
The constructed shading is indeed the exact induced shading.
-/
lemma inducedShading_isExact {fine coarse : BodyFamily} (P : Factoring fine coarse)
    (Y : Shading fine) (r : ℝ) (hcoarse_meas : coarse.IsMeasurable) :
    P.IsExactInducedShading Y (inducedShading P Y r hcoarse_meas) r := by
  intro j
  rfl

/--
Given a tube setup, construct the exact induced coarse shading, apply
factoring multiplicity regularization, and convert logarithmic mass retention
to polynomial form.
-/
lemma rho_tube_induced_shading_regularization
    {delta rho : ℝ} (hδ : 0 < delta) (hδρ : delta ≤ rho) (hρ1 : rho ≤ 1)
    {fine : TubeFamily delta} (hfine_meas : fine.toBodyFamily.IsMeasurable)
    {coarse : TubeFamily rho} (hcoarse_meas : coarse.toBodyFamily.IsMeasurable)
    (P : TubeCover fine coarse)
    (Y : TubeShading fine) (hY_pos : 0 < Y.mass)
    (epsilon : ℝ) (hε : 0 < epsilon)
    (A : ℝ) (hA1 : 1 ≤ A)
    (h_log_loss : ∀ (N : ℕ) (delta : ℝ), 0 < delta → delta ≤ 1 →
      ((Nat.log 2 N + 1 : ℕ) : ENNReal) ^ 3 ≤
        ENNReal.ofReal A * Kakeya.realRpowENN delta (-epsilon) *
        ENNReal.rpow (N + 1) epsilon) :
    ∃ R : FactoringRefinement P.toFactoring Y,
      ∃ mcoarse Mcoarse mfiber Mfiber : ℕ,
        R.fineRefinement.RetainsMass
          (Kakeya.realRpowENN delta epsilon *
            ENNReal.rpow (fine.enncard + 1) (-epsilon) *
            (ENNReal.ofReal A)⁻¹) ∧
        (∀ j, R.coarseShading.carrier j ⊆
          (inducedShading P.toFactoring Y rho hcoarse_meas).carrier
            (R.coarseSubfamily.embedding j)) ∧
        1 ≤ mcoarse ∧
        (Mcoarse : ENNReal) ≤ 2 * (mcoarse : ENNReal) ∧
        R.coarseShading.HasConstantMultiplicity mcoarse Mcoarse ∧
        1 ≤ mfiber ∧
        (Mfiber : ENNReal) ≤ 2 * (mfiber : ENNReal) ∧
        (∀ j, R.factoring.FiberHasConstantMultiplicity
          R.fineRefinement.shading j mfiber Mfiber) ∧
        (∀ x ∈ R.fineRefinement.shading.union,
          ∀ i, x ∈ R.fineRefinement.shading.carrier i →
            x ∈ R.coarseShading.carrier (R.factoring.parent i)) := by
  let Z : Shading coarse.toBodyFamily :=
    inducedShading P.toFactoring Y rho hcoarse_meas
  have hZ_exact : P.toFactoring.IsExactInducedShading Y Z rho :=
    inducedShading_isExact P.toFactoring Y rho hcoarse_meas
  have h_compat : ∀ x ∈ Y.union,
      ∀ i, x ∈ Y.carrier i → x ∈ Z.carrier (P.toFactoring.parent i) :=
    (exact_induced_shading_compatibility_main P.toFactoring Y Z rho hZ_exact).1
  rcases factoring_multiplicity_regularization_main
      P.toFactoring Y Z hY_pos h_compat with
    ⟨R, mcoarse, Mcoarse, mfiber, Mfiber, h_retention, h_Z_subset,
      h_mcoarse_pos, h_Mcoarse_le, h_coarse_mult, h_mfiber_pos, h_Mfiber_le,
      h_fiber_mult, h_point_compat⟩
  set L : ENNReal := ((Nat.log 2 fine.card + 1 : ℕ) : ENNReal) ^ 3 with hL
  set a : ENNReal := ENNReal.ofReal A with ha
  set b : ENNReal := Kakeya.realRpowENN delta (-epsilon) with hb
  set c : ENNReal := ENNReal.rpow (fine.enncard + 1) epsilon with hc
  set RHS : ENNReal := a * b * c with hRHS
  set desired : ENNReal := Kakeya.realRpowENN delta epsilon *
      ENNReal.rpow (fine.enncard + 1) (-epsilon) * (ENNReal.ofReal A)⁻¹ with hdesired
  have hδ1 : delta ≤ 1 := by linarith
  have h_enncard_def : fine.enncard = (fine.card : ENNReal) := by
    rfl
  have h_card2 : (fine.enncard + 1 : ENNReal) = (↑fine.card + 1 : ENNReal) := by
    rw [h_enncard_def] <;> ring
  have h_cast : (↑(Nat.log 2 fine.card + 1) : ENNReal) =
      (↑(Nat.log 2 fine.card) + 1 : ENNReal) := by
    simp [Nat.cast_add] <;> norm_cast
  have hL2 : L = (↑(Nat.log 2 fine.card) + 1 : ENNReal) ^ 3 := by
    simp [hL, h_cast] <;> norm_cast
  have h_rpow2 : ENNReal.rpow (fine.enncard + 1) epsilon =
      ENNReal.rpow (↑fine.card + 1) epsilon := by
    rw [h_card2]
  have h2 : L ≤ RHS := by
    rw [hL2, hRHS, ha, hb, hc, h_rpow2]
    have h := h_log_loss fine.card delta hδ hδ1
    rw [h_cast] at h
    exact h
  have hA_pos : 0 < A := by exact lt_of_lt_of_le zero_lt_one hA1
  have hcard_finite : fine.enncard + 1 ≠ ⊤ := by
    rw [h_enncard_def] <;> simp <;> exact ENNReal.coe_ne_top
  have hcard_pos : 0 < fine.enncard + 1 := by
    rw [h_enncard_def] <;> simp <;> positivity
  have h1 : Kakeya.realRpowENN delta epsilon * Kakeya.realRpowENN delta (-epsilon) = 1 := by
    have h_nonneg1 : 0 ≤ Real.rpow delta epsilon := Real.rpow_nonneg hδ.le _
    have h_mul : ENNReal.ofReal (Real.rpow delta epsilon) * ENNReal.ofReal (Real.rpow delta (-epsilon)) =
        ENNReal.ofReal (Real.rpow delta epsilon * Real.rpow delta (-epsilon)) := by
      rw [ENNReal.ofReal_mul h_nonneg1]
    have h_sum : Real.rpow delta epsilon * Real.rpow delta (-epsilon) = 1 := by
      have h_eq : Real.rpow delta epsilon * Real.rpow delta (-epsilon) =
          Real.rpow delta (epsilon + (-epsilon)) :=
        (Real.rpow_add hδ epsilon (-epsilon)).symm
      rw [h_eq]
      have h_zero : epsilon + (-epsilon) = 0 := by ring
      rw [h_zero]
      simp
    have h_main : ENNReal.ofReal (Real.rpow delta epsilon) * ENNReal.ofReal (Real.rpow delta (-epsilon)) = 1 := by
      rw [h_mul, h_sum]
      <;> simp
    have h_goal : Kakeya.realRpowENN delta epsilon * Kakeya.realRpowENN delta (-epsilon) =
        ENNReal.ofReal (Real.rpow delta epsilon) * ENNReal.ofReal (Real.rpow delta (-epsilon)) := by
      rfl
    rw [h_goal]
    exact h_main
  have h2' : ENNReal.rpow (fine.enncard + 1) (-epsilon) * ENNReal.rpow (fine.enncard + 1) epsilon = 1 := by
    have h3 : ENNReal.rpow (fine.enncard + 1) ((-epsilon) + epsilon) =
        ENNReal.rpow (fine.enncard + 1) (-epsilon) * ENNReal.rpow (fine.enncard + 1) epsilon :=
      ENNReal.rpow_add (-epsilon) epsilon hcard_pos.ne' hcard_finite
    have h4 : (-epsilon) + epsilon = 0 := by ring
    have h5 : ENNReal.rpow (fine.enncard + 1) ((-epsilon) + epsilon) = 1 := by
      rw [h4]
      <;> simp
    rw [h5] at h3
    exact h3.symm
  have hA_pos' : 0 < ENNReal.ofReal A := ENNReal.ofReal_pos.mpr hA_pos
  have hA_ne_zero : ENNReal.ofReal A ≠ 0 := hA_pos'.ne'
  have hA_ne_top : ENNReal.ofReal A ≠ ⊤ := by simp
  have h3 : (ENNReal.ofReal A)⁻¹ * ENNReal.ofReal A = 1 := by
    rw [ENNReal.inv_mul_cancel hA_ne_zero hA_ne_top]
  have h_mul : desired * RHS = 1 := by
    rw [hdesired, hRHS, ha, hb, hc]
    set d1 := Kakeya.realRpowENN delta epsilon with hd1
    set d2 := Kakeya.realRpowENN delta (-epsilon) with hd2
    set r1 := ENNReal.rpow (fine.enncard + 1) (-epsilon) with hr1
    set r2 := ENNReal.rpow (fine.enncard + 1) epsilon with hr2
    set a1 := (ENNReal.ofReal A)⁻¹ with ha1
    set a2 := ENNReal.ofReal A with ha2
    have h_eq : (d1 * r1 * a1) * (a2 * d2 * r2) = (d1 * d2) * (r1 * r2) * (a1 * a2) := by
      simp [mul_assoc, mul_comm, mul_left_comm]
    rw [h_eq, h1, h2', h3]
    <;> norm_num
  have hRHS_ne_zero : RHS ≠ 0 := by
    intro h
    rw [h] at h_mul
    simp at h_mul
  have hRHS_ne_top : RHS ≠ ⊤ := by
    intro h
    rw [h] at h_mul
    by_cases hdes : desired = 0
    · rw [hdes] at h_mul; simp at h_mul
    · rw [ENNReal.mul_top hdes] at h_mul; simp at h_mul
  have h_desired_eq_inv : desired = RHS⁻¹ := by
    have h4 : RHS * RHS⁻¹ = 1 := ENNReal.mul_inv_cancel hRHS_ne_zero hRHS_ne_top
    have h5 : (desired * RHS) * RHS⁻¹ = desired * (RHS * RHS⁻¹) := mul_assoc desired RHS RHS⁻¹
    have h6 : (desired * RHS) * RHS⁻¹ = RHS⁻¹ := by
      rw [h_mul, one_mul]
    have h7 : desired * (RHS * RHS⁻¹) = RHS⁻¹ := by
      rw [← h5, h6]
    rw [h4] at h7
    simpa using h7
  have h5 : desired ≤ L⁻¹ := by
    rw [h_desired_eq_inv]
    exact ENNReal.inv_le_inv.mpr h2
  have h_poly_retention : R.fineRefinement.RetainsMass desired := by
    dsimp only [Refinement.RetainsMass] at h_retention ⊢
    have h6 : desired * Y.mass ≤ L⁻¹ * Y.mass := by
      gcongr
    exact h6.trans h_retention
  exact ⟨R, mcoarse, Mcoarse, mfiber, Mfiber, h_poly_retention, h_Z_subset,
    h_mcoarse_pos, h_Mcoarse_le, h_coarse_mult, h_mfiber_pos, h_Mfiber_le,
    h_fiber_mult, h_point_compat⟩

end Kakeya.Streamlined
