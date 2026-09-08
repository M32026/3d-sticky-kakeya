import MyLeanRepo.Kakeya.Streamlined.Estimates

/-!
# Frostman property from maximal-density control

If a body family has bounded `deltaMax` and sufficient mass in a container,
then it is Frostman inside that container with an explicit constant.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Streamlined

namespace BodyFamily

/-- If `deltaMax ≤ C`, then every convex set has density at most `C`. -/
lemma density_le_of_deltaMax_le {F : BodyFamily} {C : ENNReal}
    (h : F.deltaMax ≤ C) {K : Set Point3} (hK : Convex ℝ K) :
    F.density K ≤ C := by
  let S : Set ENNReal :=
    {d | ∃ K : Set Point3, Convex ℝ K ∧ d = F.density K}
  have h_bdd : BddAbove S := ⟨⊤, fun _ _ => le_top⟩
  have hmem : F.density K ∈ S := ⟨K, hK, rfl⟩
  exact (le_csSup h_bdd hmem).trans h

/--
If `F.deltaMax ≤ C`, `F.containedMass U ≥ m > 0`, and
`0 < volume U < ∞`, then `F` is Frostman in `U` with constant
`C * volume U / m`.
-/
theorem frostman_from_deltaMax {F : BodyFamily} {U : Set Point3}
    {C m : ENNReal} (hm_pos : 0 < m) (hm_ne_top : m ≠ ⊤)
    (hU_vol_pos : 0 < volume U)
    (hU_vol_ne_top : volume U ≠ ⊤)
    (h_deltaMax : F.deltaMax ≤ C)
    (h_mass : F.containedMass U ≥ m) :
    F.IsCFrostmanIn U (C * volume U / m) := by
  set v : ENNReal := volume U with hv_def
  set D : ENNReal := C * v / m with hD_def
  have hv_ne_top : v ≠ ⊤ := hU_vol_ne_top
  have hm_ne_zero : m ≠ 0 := hm_pos.ne'
  have hcm_ne_zero : F.containedMass U ≠ 0 :=
    ne_of_gt (hm_pos.trans_le h_mass)
  have h_densityU_ne_zero : F.density U ≠ 0 := by
    dsimp only [BodyFamily.density]
    rw [show volume U = v by rfl]
    intro h_eq
    rcases ENNReal.div_eq_zero_iff.mp h_eq with h0 | h0
    · exact hcm_ne_zero h0
    · exact hv_ne_top h0
  have h_mul_cancel : (C * v / m) * (m / v) = C := by
    have h1 : (C * v / m) * m = C * v := by
      rw [mul_comm (C * v / m) m]
      exact ENNReal.mul_div_cancel hm_ne_zero hm_ne_top
    have h3 : (C * v / m) * (m / v) = ((C * v / m) * m) / v := by
      simp only [div_eq_mul_inv, mul_assoc]
    rw [h3, h1]
    have h4 : (C * v) / v = C := by
      have h5 : (C * v) / v = v * (C / v) := by
        simp [div_eq_mul_inv, mul_comm, mul_assoc, mul_left_comm]
      rw [h5]
      exact ENNReal.mul_div_cancel hU_vol_pos.ne' hv_ne_top
    exact h4
  let S : Set ENNReal :=
    {c | ∃ K : Set Point3, Convex ℝ K ∧ K ⊆ U ∧
      c = F.density K / F.density U}
  have h_main : ∀ c ∈ S, c ≤ D := by
    rintro c ⟨K, hK_conv, _hK_sub, rfl⟩
    have h1 : F.density K ≤ C :=
      density_le_of_deltaMax_le h_deltaMax hK_conv
    have h2 : F.density U ≥ m / v := by
      dsimp only [BodyFamily.density, hv_def]
      gcongr
    by_cases h_top : F.density U = ⊤
    · rw [h_top]
      simp
    · have h_iff :
          F.density K / F.density U ≤ D ↔
            F.density K ≤ D * F.density U :=
        ENNReal.div_le_iff h_densityU_ne_zero h_top
      rw [h_iff]
      calc
        F.density K ≤ C := h1
        _ = D * (m / v) := by rw [h_mul_cancel]
        _ ≤ D * F.density U := by gcongr
  have h_goal : F.frostmanConstantIn U ≤ D := by
    dsimp only [BodyFamily.frostmanConstantIn]
    by_cases hS : Set.Nonempty S
    · exact csSup_le hS h_main
    · have h_sup : sSup S = 0 := by
        rw [Set.not_nonempty_iff_eq_empty] at hS
        rw [hS]
        simp
      rw [h_sup]
      positivity
  exact h_goal

end BodyFamily

namespace Factoring

/--
Fiber Frostman control from a uniform fiber-mass lower bound, a coarse-volume
upper bound, and a contained-mass estimate for convex test sets.
-/
theorem fibers_frostman_from_containedMass
    {fine coarse : BodyFamily}
    {P : Factoring fine coarse} {C m V : ENNReal}
    (hm_pos : 0 < m) (hm_ne_top : m ≠ ⊤)
    (hV_ne_top : V ≠ ⊤)
    (h_contained :
      ∀ j K, Convex ℝ K →
        P.fiberContainedMass j K ≤ C * volume K)
    (h_mass : ∀ j, P.fiberMass j ≥ m)
    (h_vol : ∀ j, (coarse.body j).volume ≤ V) :
    P.FibersAreCFrostman (C * V / m) := by
  intro j K hK_conv _hK_sub
  have hm_ne_zero : m ≠ 0 := hm_pos.ne'
  have h1 : P.fiberContainedMass j K ≤ C * volume K :=
    h_contained j K hK_conv
  have h2 :
      P.fiberContainedMass j K * (coarse.body j).volume ≤
        C * volume K * (coarse.body j).volume := by
    gcongr
  have h_mul_cancel : (C * V / m) * m = C * V := by
    rw [mul_comm (C * V / m) m]
    exact ENNReal.mul_div_cancel hm_ne_zero hm_ne_top
  have h6 : C * V ≤ (C * V / m) * P.fiberMass j := by
    have h7 :
        (C * V / m) * m ≤ (C * V / m) * P.fiberMass j := by
      exact mul_le_mul_left' (h_mass j) _
    rw [h_mul_cancel] at h7
    exact h7
  have h3 :
      C * volume K * (coarse.body j).volume ≤
        (C * V / m) * P.fiberMass j * volume K := by
    calc
      C * volume K * (coarse.body j).volume
          ≤ C * volume K * V := by
            exact mul_le_mul_left' (h_vol j) _
      _ = C * V * volume K := by ring
      _ ≤ ((C * V / m) * P.fiberMass j) * volume K := by
            exact mul_le_mul_right' h6 _
      _ = (C * V / m) * P.fiberMass j * volume K := by ring
  exact h2.trans h3

end Factoring

end Kakeya.Streamlined
