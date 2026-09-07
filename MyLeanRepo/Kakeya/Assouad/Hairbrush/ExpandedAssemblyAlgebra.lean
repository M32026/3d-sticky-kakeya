import MyLeanRepo.Kakeya.Assouad.Subunit.HairbrushStatements

/-!
# Algebra for the expanded hairbrush assembly

Closed ENNReal square-root estimates used to sum balanced fibers and cancel
the selected coarse scale with the Frostman lower bound.
-/

namespace Kakeya.Assouad

/-- `ENNReal.ofReal (sqrt x)` is the ENNReal square root when `x ≥ 0`. -/
lemma hairbrush_ofReal_sqrt {x : ℝ} (hx : 0 ≤ x) :
    ENNReal.ofReal (Real.sqrt x) = (ENNReal.ofReal x) ^ (1 / 2 : ℝ) := by
  by_cases hx0 : x = 0
  · rw [hx0]
    simp
  · have hx_pos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    rw [Real.sqrt_eq_rpow, ENNReal.ofReal_rpow_of_pos hx_pos]

/-- Multiplying two ENNReal square roots recovers the original value. -/
lemma hairbrush_ennreal_sqrt_sq
    (x : ENNReal) (hx : x ≠ 0) (hxt : x ≠ ⊤) :
    x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x := by
  have h := ENNReal.rpow_add_of_nonneg
    (x := x) (1 / 2 : ℝ) (1 / 2 : ℝ) (by norm_num) (by norm_num)
  norm_num at h
  simpa using h.symm

/-- Cancel one ENNReal square root from a product. -/
lemma hairbrush_ennreal_mul_div_sqrt
    (x y : ENNReal) (hx0 : x ≠ 0) (hxt : x ≠ ⊤) :
    x * (y * (x ^ (1 / 2 : ℝ))⁻¹) = x ^ (1 / 2 : ℝ) * y := by
  set s : ENNReal := x ^ (1 / 2 : ℝ) with hs
  have hs0 : s ≠ 0 := by
    simp only [hs]
    intro hz
    rw [ENNReal.rpow_eq_zero_iff] at hz
    tauto
  have hstop : s ≠ ⊤ := by
    simp only [hs]
    intro hz
    rw [ENNReal.rpow_eq_top_iff] at hz
    tauto
  have hsq : s * s = x := by
    simpa [hs] using hairbrush_ennreal_sqrt_sq x hx0 hxt
  calc
    x * (y * s⁻¹) = (s * s) * (y * s⁻¹) := by rw [hsq]
    _ = s * (s * s⁻¹) * y := by
      rw [mul_assoc, mul_assoc, mul_comm y s⁻¹, mul_assoc]
    _ = s * 1 * y := by rw [ENNReal.mul_inv_cancel hs0 hstop]
    _ = s * y := by simp
    _ = x ^ (1 / 2 : ℝ) * y := by simp [hs]

/--
If every balanced fiber satisfies `c ≤ N * a j`, then
`sqrt N * sqrt c ≤ sum_j sqrt (a j)`.
-/
lemma hairbrush_balanced_sum_sqrt_lower
    {N : ℕ} (hN : 0 < N)
    (c : ENNReal) (a : Fin N → ENNReal)
    (h : ∀ j : Fin N, c ≤ (N : ENNReal) * a j) :
    (N : ENNReal) ^ (1 / 2 : ℝ) * c ^ (1 / 2 : ℝ) ≤
      ∑ j : Fin N, (a j) ^ (1 / 2 : ℝ) := by
  set N' : ENNReal := (N : ENNReal) with hN'
  have hN0 : N' ≠ 0 := by simpa [hN'] using hN.ne'
  have hNtop : N' ≠ ⊤ := ENNReal.natCast_ne_top N
  set s : ENNReal := N' ^ (1 / 2 : ℝ) with hs
  have hs0 : s ≠ 0 := by
    simp only [hs]
    intro hz
    rw [ENNReal.rpow_eq_zero_iff] at hz
    tauto
  have hstop : s ≠ ⊤ := by
    simp only [hs]
    intro hz
    rw [ENNReal.rpow_eq_top_iff] at hz
    tauto
  have h_each : ∀ j : Fin N,
      c ^ (1 / 2 : ℝ) * s⁻¹ ≤ (a j) ^ (1 / 2 : ℝ) := by
    intro j
    have hroot :
        c ^ (1 / 2 : ℝ) ≤ s * (a j) ^ (1 / 2 : ℝ) := by
      have hrpow := ENNReal.rpow_le_rpow (h j)
        (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      rw [ENNReal.mul_rpow_of_nonneg N' (a j) (by norm_num)] at hrpow
      exact hrpow
    calc
      c ^ (1 / 2 : ℝ) * s⁻¹
          ≤ (s * (a j) ^ (1 / 2 : ℝ)) * s⁻¹ := by gcongr
      _ = s * s⁻¹ * (a j) ^ (1 / 2 : ℝ) := by
        rw [mul_assoc, mul_comm ((a j) ^ (1 / 2 : ℝ)) s⁻¹, ← mul_assoc]
      _ = (a j) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_inv_cancel hs0 hstop]
        simp
  have hsum :
      ∑ j : Fin N, c ^ (1 / 2 : ℝ) * s⁻¹ ≤
        ∑ j : Fin N, (a j) ^ (1 / 2 : ℝ) :=
    Finset.sum_le_sum fun j _ => h_each j
  have hconst :
      ∑ _j : Fin N, c ^ (1 / 2 : ℝ) * s⁻¹ =
        N' * (c ^ (1 / 2 : ℝ) * s⁻¹) := by
    simp [hN', Finset.sum_const]
  rw [hconst] at hsum
  have hcancel :
      N' * (c ^ (1 / 2 : ℝ) * s⁻¹) = s * c ^ (1 / 2 : ℝ) :=
    hairbrush_ennreal_mul_div_sqrt N' (c ^ (1 / 2 : ℝ)) hN0 hNtop
  rw [hcancel] at hsum
  simpa [hs] using hsum

/-- Cancel the coarse scale using a Frostman lower bound. -/
lemma hairbrush_frostman_sqrt_cancellation
    (c theta N : ENNReal)
    (htheta : theta ≠ 0) (h : c ≤ theta * N) :
    c ^ (1 / 2 : ℝ) * (theta ^ (1 / 2 : ℝ))⁻¹ ≤
      N ^ (1 / 2 : ℝ) := by
  by_cases htheta_top : theta = ⊤
  · rw [htheta_top]
    simp
  · set s : ENNReal := theta ^ (1 / 2 : ℝ) with hs
    have hs0 : s ≠ 0 := by
      simp only [hs]
      intro hz
      rw [ENNReal.rpow_eq_zero_iff] at hz
      tauto
    have hstop : s ≠ ⊤ := by
      simp only [hs]
      intro hz
      rw [ENNReal.rpow_eq_top_iff] at hz
      tauto
    have hroot : c ^ (1 / 2 : ℝ) ≤ s * N ^ (1 / 2 : ℝ) := by
      have hrpow := ENNReal.rpow_le_rpow h
        (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      rw [ENNReal.mul_rpow_of_nonneg theta N (by norm_num)] at hrpow
      exact hrpow
    calc
      c ^ (1 / 2 : ℝ) * s⁻¹
          ≤ (s * N ^ (1 / 2 : ℝ)) * s⁻¹ := by gcongr
      _ = s * s⁻¹ * N ^ (1 / 2 : ℝ) := by
        rw [mul_assoc, mul_comm (N ^ (1 / 2 : ℝ)) s⁻¹, ← mul_assoc]
      _ = N ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_inv_cancel hs0 hstop]
        simp

/-- Combine balanced fiber cardinality and the coarse Frostman count. -/
lemma hairbrush_fiber_sum_sqrt_bound
    {N : ℕ} (hN : 0 < N)
    (deltaEta theta familyCard : ENNReal)
    (a : Fin N → ENNReal)
    (hBalanced :
      ∀ j : Fin N, deltaEta * familyCard ≤ (N : ENNReal) * a j)
    (hFrostman : deltaEta ≤ theta * (N : ENNReal))
    (htheta : theta ≠ 0)
    (hdeltaEta : deltaEta ≠ 0)
    (hdeltaEtaTop : deltaEta ≠ ⊤) :
    deltaEta * (theta ^ (1 / 2 : ℝ))⁻¹ *
        familyCard ^ (1 / 2 : ℝ) ≤
      ∑ j : Fin N, (a j) ^ (1 / 2 : ℝ) := by
  set c : ENNReal := deltaEta * familyCard with hc
  have hbalanced :
      (N : ENNReal) ^ (1 / 2 : ℝ) * c ^ (1 / 2 : ℝ) ≤
        ∑ j : Fin N, (a j) ^ (1 / 2 : ℝ) :=
    hairbrush_balanced_sum_sqrt_lower hN c a hBalanced
  have hfrost :
      deltaEta ^ (1 / 2 : ℝ) * (theta ^ (1 / 2 : ℝ))⁻¹ ≤
        (N : ENNReal) ^ (1 / 2 : ℝ) :=
    hairbrush_frostman_sqrt_cancellation
      deltaEta theta (N : ENNReal) htheta hFrostman
  have hmain :
      deltaEta ^ (1 / 2 : ℝ) * c ^ (1 / 2 : ℝ) *
          (theta ^ (1 / 2 : ℝ))⁻¹ ≤
        ∑ j : Fin N, (a j) ^ (1 / 2 : ℝ) := by
    calc
      deltaEta ^ (1 / 2 : ℝ) * c ^ (1 / 2 : ℝ) *
          (theta ^ (1 / 2 : ℝ))⁻¹ =
        (deltaEta ^ (1 / 2 : ℝ) *
          (theta ^ (1 / 2 : ℝ))⁻¹) * c ^ (1 / 2 : ℝ) := by
            simp [mul_assoc, mul_comm, mul_left_comm]
      _ ≤ (N : ENNReal) ^ (1 / 2 : ℝ) * c ^ (1 / 2 : ℝ) := by
        gcongr
      _ ≤ ∑ j : Fin N, (a j) ^ (1 / 2 : ℝ) := hbalanced
  have hsqrt :
      c ^ (1 / 2 : ℝ) =
        deltaEta ^ (1 / 2 : ℝ) * familyCard ^ (1 / 2 : ℝ) := by
    rw [hc, ENNReal.mul_rpow_of_nonneg deltaEta familyCard (by norm_num)]
  have hsquare :
      deltaEta ^ (1 / 2 : ℝ) * deltaEta ^ (1 / 2 : ℝ) = deltaEta :=
    hairbrush_ennreal_sqrt_sq deltaEta hdeltaEta hdeltaEtaTop
  have hrearrange :
      deltaEta ^ (1 / 2 : ℝ) * c ^ (1 / 2 : ℝ) *
          (theta ^ (1 / 2 : ℝ))⁻¹ =
        deltaEta * (theta ^ (1 / 2 : ℝ))⁻¹ *
          familyCard ^ (1 / 2 : ℝ) := by
    rw [hsqrt]
    rw [← mul_assoc, hsquare]
    simp [mul_assoc, mul_comm, mul_left_comm]
  rw [hrearrange] at hmain
  exact hmain

/--
Multiply the coarse-count and total-cardinality lower bounds to cancel
the group count and angular scale.

Given `theta * q ≥ δ^coarseLoss` and `q * M ≥ δ^totalLoss * F`, conclude
`sqrt(δ^totalLoss * δ^coarseLoss) * sqrt(F) ≤ sqrt(theta) * q * sqrt(M)`.
-/
lemma hairbrush_two_bound_sqrt_cancellation
    (deltaEtaTotal deltaEtaCoarse theta q M F_card : ENNReal)
    (hCoarse : deltaEtaCoarse ≤ theta * q)
    (hTotal : deltaEtaTotal * F_card ≤ q * M)
    (_htheta : theta ≠ 0) (_htheta_top : theta ≠ ⊤)
    (_hq0 : q ≠ 0) (_hq_top : q ≠ ⊤)
    (_hdeTotal0 : deltaEtaTotal ≠ 0) (_hdeTotalTop : deltaEtaTotal ≠ ⊤)
    (_hdeCoarse0 : deltaEtaCoarse ≠ 0) (_hdeCoarseTop : deltaEtaCoarse ≠ ⊤) :
    (deltaEtaTotal * deltaEtaCoarse) ^ (1 / 2 : ℝ) * F_card ^ (1 / 2 : ℝ) ≤
      theta ^ (1 / 2 : ℝ) * q * M ^ (1 / 2 : ℝ) := by
  set s : ENNReal := q ^ (1 / 2 : ℝ) with hs
  have hs0 : s ≠ 0 := by
    simp only [hs]
    intro hz
    rw [ENNReal.rpow_eq_zero_iff] at hz
    tauto
  have hstop : s ≠ ⊤ := by
    simp only [hs]
    intro hz
    rw [ENNReal.rpow_eq_top_iff] at hz
    tauto
  have hsq : s * s = q := hairbrush_ennreal_sqrt_sq q _hq0 _hq_top
  have h1 : deltaEtaCoarse ^ (1 / 2 : ℝ) ≤ theta ^ (1 / 2 : ℝ) * s := by
    have hrpow := ENNReal.rpow_le_rpow hCoarse (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    rw [ENNReal.mul_rpow_of_nonneg theta q (by norm_num)] at hrpow
    exact hrpow
  have h2 : deltaEtaTotal ^ (1 / 2 : ℝ) * F_card ^ (1 / 2 : ℝ) ≤ s * M ^ (1 / 2 : ℝ) := by
    have hrpow := ENNReal.rpow_le_rpow hTotal (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    rw [ENNReal.mul_rpow_of_nonneg deltaEtaTotal F_card (by norm_num)] at hrpow
    rw [ENNReal.mul_rpow_of_nonneg q M (by norm_num)] at hrpow
    exact hrpow
  have h3 : (deltaEtaTotal * deltaEtaCoarse) ^ (1 / 2 : ℝ) =
      deltaEtaTotal ^ (1 / 2 : ℝ) * deltaEtaCoarse ^ (1 / 2 : ℝ) := by
    rw [ENNReal.mul_rpow_of_nonneg deltaEtaTotal deltaEtaCoarse (by norm_num)]
  calc
    (deltaEtaTotal * deltaEtaCoarse) ^ (1 / 2 : ℝ) * F_card ^ (1 / 2 : ℝ)
        = (deltaEtaTotal ^ (1 / 2 : ℝ) * deltaEtaCoarse ^ (1 / 2 : ℝ)) *
            F_card ^ (1 / 2 : ℝ) := by rw [h3]
    _ = deltaEtaCoarse ^ (1 / 2 : ℝ) *
          (deltaEtaTotal ^ (1 / 2 : ℝ) * F_card ^ (1 / 2 : ℝ)) := by
        simp [mul_assoc, mul_comm, mul_left_comm]
    _ ≤ deltaEtaCoarse ^ (1 / 2 : ℝ) * (s * M ^ (1 / 2 : ℝ)) := by gcongr
    _ = deltaEtaCoarse ^ (1 / 2 : ℝ) * s * M ^ (1 / 2 : ℝ) := by
        rw [mul_assoc]
    _ ≤ (theta ^ (1 / 2 : ℝ) * s) * s * M ^ (1 / 2 : ℝ) := by gcongr
    _ = theta ^ (1 / 2 : ℝ) * (s * s) * M ^ (1 / 2 : ℝ) := by
        simp [mul_assoc, mul_comm, mul_left_comm]
    _ = theta ^ (1 / 2 : ℝ) * q * M ^ (1 / 2 : ℝ) := by rw [hsq]

/-- Antitone `realRpowENN`: for `0 < δ ≤ 1`, if `a ≤ b` then `δ^b ≤ δ^a`. -/
lemma hairbrush_rpow_antitone {δ a b : ℝ}
    (hδ_pos : 0 < δ) (hδ_one : δ ≤ 1) (h : a ≤ b) :
    Kakeya.realRpowENN δ b ≤ Kakeya.realRpowENN δ a := by
  simp only [Kakeya.realRpowENN]
  apply ENNReal.ofReal_le_ofReal
  exact Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_one h

/-- Strict antitone `realRpowENN`: for `0 < δ < 1`, if `a < b` then `δ^b < δ^a`. -/
lemma hairbrush_rpow_strict_antitone {δ a b : ℝ}
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1) (h : a < b) :
    Kakeya.realRpowENN δ b < Kakeya.realRpowENN δ a := by
  have h_pos : 0 < Real.rpow δ a := Real.rpow_pos_of_pos hδ_pos a
  simp only [Kakeya.realRpowENN]
  rw [ENNReal.ofReal_lt_ofReal_iff h_pos]
  exact Real.rpow_lt_rpow_of_exponent_gt hδ_pos hδ_lt_one h

/-- Multiply two `realRpowENN` terms: `δ^a * δ^b = δ^(a+b)`. -/
lemma hairbrush_realRpowENN_mul {delta a b : ℝ} (hdelta : 0 < delta) :
    Kakeya.realRpowENN delta a * Kakeya.realRpowENN delta b =
    Kakeya.realRpowENN delta (a + b) := by
  simp only [Kakeya.realRpowENN]
  have hnonneg : 0 ≤ Real.rpow delta a := Real.rpow_nonneg (by linarith) a
  have hreal : Real.rpow delta a * Real.rpow delta b = Real.rpow delta (a + b) :=
    (Real.rpow_add hdelta a b).symm
  have h1 : ENNReal.ofReal (Real.rpow delta a) * ENNReal.ofReal (Real.rpow delta b) =
      ENNReal.ofReal (Real.rpow delta a * Real.rpow delta b) := by
    rw [← ENNReal.ofReal_mul hnonneg]
  rw [h1, hreal]

/-- Compose `realRpowENN` with rpow: `(δ^a)^b = δ^(a*b)`. -/
lemma hairbrush_realRpowENN_rpow {delta : ℝ} (hdelta : 0 < delta) (a b : ℝ) :
    ENNReal.rpow (Kakeya.realRpowENN delta a) b =
    Kakeya.realRpowENN delta (a * b) := by
  simp only [Kakeya.realRpowENN]
  have hpos : 0 < Real.rpow delta a := Real.rpow_pos_of_pos hdelta a
  calc
    ENNReal.rpow (ENNReal.ofReal (Real.rpow delta a)) b
      = ENNReal.ofReal (Real.rpow (Real.rpow delta a) b) :=
        ENNReal.ofReal_rpow_of_pos hpos
    _ = ENNReal.ofReal (Real.rpow delta (a * b)) := by
        have hmul : Real.rpow (Real.rpow delta a) b = Real.rpow delta (a * b) := by
          exact (Real.rpow_mul (by linarith) a b).symm
        rw [hmul]

end Kakeya.Assouad
