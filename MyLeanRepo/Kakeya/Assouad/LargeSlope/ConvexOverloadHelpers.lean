import MyLeanRepo.Kakeya.Assouad.Statements
import MyLeanRepo.Kakeya.Assouad.LargeSlope.NegativeExponentAbsorption

/-!
# Helper lemmas for the large-slope convex overload proof

Includes:
- Conversion from ENNReal direction bound to real direction bound
- Slab width simplification
-/

namespace Kakeya.Assouad

/--
Convert the ENNReal direction-width bound from `tube_segment_ad_direction_bound`
into a real inequality.
-/
lemma direction_bound_to_real
    {delta rho eta' sigma : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho)
    {direction v : Point3}
    (h : ENNReal.ofReal (|inner ℝ direction v| / Real.sqrt rho) ≤
        Kakeya.realRpowENN delta (-(3 * eta' / sigma))) :
    |inner ℝ direction v| ≤
      Real.sqrt rho * Real.rpow delta (-(3 * eta' / sigma)) := by
  set x : ℝ := |inner ℝ direction v| / Real.sqrt rho with hx_def
  set y : ℝ := Real.rpow delta (-(3 * eta' / sigma)) with hy_def
  have hx_nonneg : 0 ≤ x := by positivity
  have hy_nonneg : 0 ≤ y := Real.rpow_nonneg hdelta.le _
  have h' : ENNReal.ofReal x ≤ ENNReal.ofReal y := by
    simpa [Kakeya.realRpowENN, hy_def] using h
  have h_real : x ≤ y := by
    exact (ENNReal.ofReal_le_ofReal_iff hy_nonneg).mp h'
  have hsqrt_pos : 0 < Real.sqrt rho := Real.sqrt_pos.mpr hrho
  calc
    |inner ℝ direction v|
      = x * Real.sqrt rho := by
        simp [hx_def, hsqrt_pos.ne'] <;> field_simp [hsqrt_pos.ne'] <;> ring
    _ ≤ y * Real.sqrt rho := by gcongr
    _ = Real.sqrt rho * y := by ring
    _ = Real.sqrt rho * Real.rpow delta (-(3 * eta' / sigma)) := by rw [hy_def]

/--
For `0 < delta ≤ 1` and `e > 0`, `Real.rpow delta (-e) ≥ 1`.
-/
lemma rpow_neg_ge_one {delta e : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1) (he : 0 < e) :
    Real.rpow delta (-e) ≥ 1 := by
  have h1 : Real.rpow delta e ≤ 1 := by
    have h2 : Real.rpow delta e ≤ Real.rpow 1 e := Real.rpow_le_rpow hdelta.le hdelta1 he.le
    simpa using h2
  have h3 : 0 < Real.rpow delta e := Real.rpow_pos_of_pos hdelta e
  have h4 : Real.rpow delta (-e) = (Real.rpow delta e)⁻¹ :=
    Real.rpow_neg hdelta.le e
  rw [h4]
  have h5 : (Real.rpow delta e)⁻¹ ≥ 1 := by
    have h6 : Real.rpow delta e ≤ 1 := h1
    have h7 : 0 < Real.rpow delta e := h3
    have h8 : (Real.rpow delta e)⁻¹ ≥ 1 := by
      calc
        (Real.rpow delta e)⁻¹ ≥ 1⁻¹ := by gcongr
        _ = 1 := by norm_num
    exact h8
  exact h5

/--
Slab width bound: `tau + 2*delta + sqrt(rho) ≤ 3*tau`
when `tau = sqrt(rho) * delta^(-e)`, `delta ≤ rho`, `e > 0`, and `2*delta ≤ tau`.
-/
lemma slab_width_bound
    {delta rho e tau : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho)
    (he : 0 < e) (hdelta1 : delta ≤ 1)
    (hdelta_rho : delta ≤ rho)
    (htau_def : tau = Real.sqrt rho * Real.rpow delta (-e))
    (hsmall : 2 * delta ≤ tau) :
    tau + 2 * delta + Real.sqrt rho ≤ 3 * tau := by
  have hsqrt_le_tau : Real.sqrt rho ≤ tau := by
    rw [htau_def]
    have h1 : Real.rpow delta (-e) ≥ 1 := rpow_neg_ge_one hdelta hdelta1 he
    have h4 : 0 ≤ Real.sqrt rho := Real.sqrt_nonneg rho
    calc
      Real.sqrt rho ≤ Real.sqrt rho * 1 := by linarith
      _ ≤ Real.sqrt rho * Real.rpow delta (-e) := by gcongr
  linarith

/--
Existence of `delta₀` ensuring `2*delta ≤ Real.sqrt rho * Real.rpow delta (-e)`
for all `delta ≤ delta₀`, given `delta ≤ rho` and `e > 0`.

Uses `exists_delta_absorb_constant` with exponent `-(1/2 + e)`.
-/
lemma exists_delta_slab_width {e : ℝ} (he : 0 < e) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta rho : ℝ, 0 < delta → delta ≤ delta₀ → delta ≤ rho →
        2 * delta ≤ Real.sqrt rho * Real.rpow delta (-e) := by
  set exp : ℝ := -(1 / 2 + e) with hexp_def
  have hexp_neg : exp < 0 := by linarith
  rcases exists_delta_absorb_constant (show (0 : ℝ) < 2 by norm_num) hexp_neg with
    ⟨delta₀, hdelta₀_pos, hdelta₀_one, hmain⟩
  refine ⟨delta₀, hdelta₀_pos, hdelta₀_one, ?_⟩
  intro delta rho hdelta hdelta_le _hdelta_rho
  have h1 : (2 : ℝ) < Real.rpow delta exp := hmain delta hdelta hdelta_le
  have hsqrt_rho : Real.sqrt rho ≥ Real.sqrt delta := by
    gcongr <;> linarith
  have h_sum : 1 + exp = 1 / 2 - e := by
    simp [hexp_def] <;> ring
  have h_rpow_add1 : Real.rpow delta (1 + exp) = Real.rpow delta 1 * Real.rpow delta exp :=
    Real.rpow_add hdelta 1 exp
  have h2 : delta * Real.rpow delta exp = Real.rpow delta (1 / 2 - e) := by
    have h3 : Real.rpow delta 1 = delta := by simp
    calc
      delta * Real.rpow delta exp
        = Real.rpow delta 1 * Real.rpow delta exp := by rw [h3] <;> ring
      _ = Real.rpow delta (1 + exp) := h_rpow_add1.symm
      _ = Real.rpow delta (1 / 2 - e) := by rw [h_sum]
  have h3 : 2 * delta < delta * Real.rpow delta exp := by
    have h4 : (2 : ℝ) * delta < Real.rpow delta exp * delta :=
      mul_lt_mul_of_pos_right h1 hdelta
    have h5 : Real.rpow delta exp * delta = delta * Real.rpow delta exp := by ring
    rw [h5] at h4
    exact h4
  have h4 : 2 * delta < Real.rpow delta (1 / 2 - e) := by
    rw [h2] at h3
    exact h3
  have h_rpow_add2 : Real.rpow delta ((1 / 2 : ℝ) + (-e)) =
      Real.rpow delta (1 / 2) * Real.rpow delta (-e) :=
    Real.rpow_add hdelta (1 / 2) (-e)
  have h_sum2 : (1 / 2 : ℝ) + (-e) = 1 / 2 - e := by ring
  have h5 : Real.rpow delta (1 / 2 - e) = Real.sqrt delta * Real.rpow delta (-e) := by
    have h6 : Real.rpow delta (1 / 2 - e) = Real.rpow delta ((1 / 2 : ℝ) + (-e)) := by rw [h_sum2]
    have h7 : Real.rpow delta ((1 / 2 : ℝ) + (-e)) =
        Real.rpow delta (1 / 2) * Real.rpow delta (-e) := h_rpow_add2
    have h8 : Real.rpow delta (1 / 2) = Real.sqrt delta :=
      (Real.sqrt_eq_rpow delta).symm
    calc
      Real.rpow delta (1 / 2 - e)
        = Real.rpow delta ((1 / 2 : ℝ) + (-e)) := h6
      _ = Real.rpow delta (1 / 2) * Real.rpow delta (-e) := h7
      _ = Real.sqrt delta * Real.rpow delta (-e) := by rw [h8]
  rw [h5] at h4
  have h_rpow_nonneg : 0 ≤ Real.rpow delta (-e) := Real.rpow_nonneg hdelta.le (-e)
  have h9 : Real.sqrt delta * Real.rpow delta (-e) ≤ Real.sqrt rho * Real.rpow delta (-e) :=
    mul_le_mul_of_nonneg_right hsqrt_rho h_rpow_nonneg
  exact h4.le.trans h9

end Kakeya.Assouad
