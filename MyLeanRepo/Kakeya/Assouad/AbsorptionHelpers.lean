import MyLeanRepo.Kakeya.Assouad.Statements
import MyLeanRepo.Kakeya.Assouad.ConstantAbsorption
import MyLeanRepo.Kakeya.Assouad.ExtremalInfrastructure
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.LogAbsorption
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Shared arithmetic helpers for cleaned-target absorption proofs

Provides ENNReal rpow algebra, cardinality-loss bounds, and finite-constant
absorption lemmas used by both the Tube-Wolff and parameter-Frostman cleanup
proofs.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- ENNReal rpow additive law. -/
lemma realRpowENN_add {x : ℝ} (hx : 0 < x) (a b : ℝ) :
    Kakeya.realRpowENN x (a + b) =
      Kakeya.realRpowENN x a * Kakeya.realRpowENN x b := by
  have h : Real.rpow x (a + b) = Real.rpow x a * Real.rpow x b :=
    Real.rpow_add hx a b
  simp only [Kakeya.realRpowENN, h]
  exact ENNReal.ofReal_mul (Real.rpow_nonneg hx.le a)

/-- ENNReal rpow multiplicative law in base. -/
lemma realRpowENN_mul {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (e : ℝ) :
    Kakeya.realRpowENN (x * y) e =
      Kakeya.realRpowENN x e * Kakeya.realRpowENN y e := by
  have h1 : Real.rpow (x * y) e = Real.rpow x e * Real.rpow y e :=
    Real.mul_rpow hx.le hy.le
  have h2 : 0 ≤ Real.rpow x e := Real.rpow_nonneg hx.le e
  simp only [Kakeya.realRpowENN, h1, ENNReal.ofReal_mul h2]

/-- Natural power of a real rpow equals rpow with multiplied exponent. -/
lemma rpow_nat_pow {x : ℝ} (hx : 0 < x) (y : ℝ) (n : ℕ) :
    (Real.rpow x y) ^ n = Real.rpow x ((n : ℝ) * y) := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      (Real.rpow x y) ^ (n + 1)
        = (Real.rpow x y) ^ n * (Real.rpow x y) := by ring
      _ = Real.rpow x ((n : ℝ) * y) * (Real.rpow x y) := by rw [ih]
      _ = Real.rpow x (((n : ℝ) * y) + y) := by
        exact (Real.rpow_add hx ((n : ℝ) * y) y).symm
      _ = Real.rpow x (((n + 1 : ℕ) : ℝ) * y) := by
        simp [add_mul] <;> ring

/-- Real arithmetic core: 4/(m * delta^theta * L^3) ≤ 4*50^3 * delta^(-theta-eta/25). -/
lemma real_cardLoss_core {delta L m theta eta : ℝ}
  (hdelta : 0 < delta) (hL_pos : 0 < L) (hm : 0 < m)
  (hm_ge : m ≥ 50 * L)
  (heta : 0 < eta) (htheta : 0 < theta)
  (hlen : Real.rpow delta (eta / 100) ≤ 50 * L) :
  4 / (m * Real.rpow delta theta * L^3) ≤
  (4 * (50 : ℝ)^3) * Real.rpow delta (-theta - eta / 25) := by
  set rpow_eta : ℝ := Real.rpow delta (eta / 100) with hrpow_eta_def
  have h_rpow_eta_pos : 0 < rpow_eta := Real.rpow_pos_of_pos hdelta _
  set rpow_theta : ℝ := Real.rpow delta theta with hrpow_theta_def
  have h_rpow_theta_pos : 0 < rpow_theta := Real.rpow_pos_of_pos hdelta theta
  have hL_lower : L ≥ rpow_eta / 50 := by linarith [hlen]
  have hL4_lower : L^4 ≥ rpow_eta^4 / (50 : ℝ)^4 := by
    have h1 : L ≥ rpow_eta / 50 := hL_lower
    have h2 : L^4 ≥ (rpow_eta / 50)^4 := by gcongr <;> positivity
    have h3 : (rpow_eta / 50)^4 = rpow_eta^4 / (50 : ℝ)^4 := by ring
    linarith
  have h_rpow4_eq : rpow_eta^4 = Real.rpow delta (eta / 25) := by
    have h4 : rpow_eta^4 = Real.rpow delta ((4 : ℝ) * (eta / 100)) := rpow_nat_pow hdelta (eta / 100) 4
    have h5 : (4 : ℝ) * (eta / 100) = eta / 25 := by ring
    rw [h4, h5]
  have h_denom_ge : m * rpow_theta * L^3 ≥ 50 * rpow_theta * L^4 := by
    have h1 : m ≥ 50 * L := hm_ge
    have h2 : m * rpow_theta * L^3 ≥ (50 * L) * rpow_theta * L^3 := by gcongr
    have h3 : (50 * L) * rpow_theta * L^3 = 50 * rpow_theta * L^4 := by ring
    linarith
  have h6 : 4 / (m * rpow_theta * L^3) ≤ 4 / (50 * rpow_theta * L^4) := by
    have h_pos1 : 0 < m * rpow_theta * L^3 := by positivity
    have h_pos2 : 0 < 50 * rpow_theta * L^4 := by positivity
    have h : 1 / (m * rpow_theta * L^3) ≤ 1 / (50 * rpow_theta * L^4) :=
      one_div_le_one_div_of_le h_pos2 h_denom_ge
    have h4 : 4 / (m * rpow_theta * L^3) = 4 * (1 / (m * rpow_theta * L^3)) := by ring
    have h5 : 4 / (50 * rpow_theta * L^4) = 4 * (1 / (50 * rpow_theta * L^4)) := by ring
    rw [h4, h5]
    gcongr
  have h7 : 4 / (50 * rpow_theta * L^4) ≤
      4 / (50 * rpow_theta * (rpow_eta^4 / (50 : ℝ)^4)) := by
    have h_pos1 : 0 < 50 * rpow_theta * L^4 := by positivity
    have h_pos2 : 0 < 50 * rpow_theta * (rpow_eta^4 / (50 : ℝ)^4) := by positivity
    have h_denom : 50 * rpow_theta * (rpow_eta^4 / (50 : ℝ)^4) ≤ 50 * rpow_theta * L^4 := by gcongr
    have h : 1 / (50 * rpow_theta * L^4) ≤ 1 / (50 * rpow_theta * (rpow_eta^4 / (50 : ℝ)^4)) :=
      one_div_le_one_div_of_le h_pos2 h_denom
    have h4 : 4 / (50 * rpow_theta * L^4) = 4 * (1 / (50 * rpow_theta * L^4)) := by ring
    have h5 : 4 / (50 * rpow_theta * (rpow_eta^4 / (50 : ℝ)^4)) =
        4 * (1 / (50 * rpow_theta * (rpow_eta^4 / (50 : ℝ)^4))) := by ring
    rw [h4, h5]
    gcongr
  have h8 : 4 / (50 * rpow_theta * (rpow_eta^4 / (50 : ℝ)^4)) =
      (4 * (50 : ℝ)^3) * (rpow_theta⁻¹ * (rpow_eta^4)⁻¹) := by
    field_simp [h_rpow_theta_pos.ne', h_rpow_eta_pos.ne'] <;> ring
  have h9 : rpow_theta⁻¹ * (rpow_eta^4)⁻¹ = Real.rpow delta (-theta - eta / 25) := by
    have h10 : rpow_theta⁻¹ = Real.rpow delta (-theta) := by
      simp only [hrpow_theta_def]
      exact (Real.rpow_neg hdelta.le theta).symm
    have h11 : (rpow_eta^4)⁻¹ = Real.rpow delta (-(eta / 25)) := by
      rw [h_rpow4_eq]
      exact (Real.rpow_neg hdelta.le (eta / 25)).symm
    rw [h10, h11]
    have h12 : Real.rpow delta (-theta) * Real.rpow delta (-(eta / 25)) =
        Real.rpow delta (-theta + (-(eta / 25))) := (Real.rpow_add hdelta (-theta) (-(eta / 25))).symm
    rw [h12] <;> ring_nf
  calc
    4 / (m * rpow_theta * L^3)
      ≤ 4 / (50 * rpow_theta * L^4) := h6
    _ ≤ 4 / (50 * rpow_theta * (rpow_eta^4 / (50 : ℝ)^4)) := h7
    _ = (4 * (50 : ℝ)^3) * (rpow_theta⁻¹ * (rpow_eta^4)⁻¹) := h8
    _ = (4 * (50 : ℝ)^3) * Real.rpow delta (-theta - eta / 25) := by rw [h9]

/-- Bound cardLoss by constant * V1 * delta^(-1001*theta/1000 - 7*eta/50). -/
lemma cardLoss_bound {delta rho L m theta eta : ℝ}
  (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
  (hrho : 0 < rho) (hL_pos : 0 < L) (hm : 0 < m)
  (hm_ge : m ≥ 50 * L)
  (hrho_eq : rho = 2 * delta / L)
  (heta : 0 < eta) (htheta : 0 < theta)
  (hlen : Real.rpow delta (eta / 100) ≤ 50 * L)
  (V1 : ENNReal) (hV1_pos : 0 < V1) (hV1_ne_top : V1 ≠ ⊤)
  (massLoss : ENNReal)
  (h_massLoss : massLoss ≤ Kakeya.realRpowENN delta (-(eta / 10))) :
  ((ENNReal.ofReal m * Kakeya.realRpowENN delta theta * ENNReal.ofReal L)⁻¹ *
    (24 * massLoss * Kakeya.realRpowENN rho 2 * V1 *
      Kakeya.realRpowENN delta (-2 - theta / 1000))) ≤
  ENNReal.ofReal (24 / 50 * 4 * (50 : ℝ)^4) * V1 *
    Kakeya.realRpowENN delta (-theta * 1001 / 1000 - 7 * eta / 50) := by
  set rpow_theta : ℝ := Real.rpow delta theta with hrpow_theta_def
  have h_rpow_theta_pos : 0 < rpow_theta := Real.rpow_pos_of_pos hdelta theta
  set prod_real : ℝ := m * rpow_theta * L with hprod_real_def
  have h_prod_pos : 0 < prod_real := by positivity
  have h_prod_eq : ENNReal.ofReal m * Kakeya.realRpowENN delta theta * ENNReal.ofReal L =
      ENNReal.ofReal prod_real := by
    have h1 : Kakeya.realRpowENN delta theta = ENNReal.ofReal rpow_theta := by
      simp [Kakeya.realRpowENN, hrpow_theta_def]
    rw [h1]
    have h2 : ENNReal.ofReal m * ENNReal.ofReal rpow_theta * ENNReal.ofReal L =
        ENNReal.ofReal (m * rpow_theta * L) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)] <;> ring
    rw [h2, hprod_real_def]
  have h_inv_eq : (ENNReal.ofReal m * Kakeya.realRpowENN delta theta * ENNReal.ofReal L)⁻¹ =
      ENNReal.ofReal (prod_real⁻¹) := by
    rw [h_prod_eq, ENNReal.ofReal_inv_of_pos h_prod_pos]
  have h_rho2_delta2 :
      Kakeya.realRpowENN rho 2 * Kakeya.realRpowENN delta (-2) =
        ENNReal.ofReal (4 / L^2) := by
    have h1 : Kakeya.realRpowENN rho 2 = ENNReal.ofReal (rho^2) := by
      simp [Kakeya.realRpowENN] <;> norm_cast
    have h2 : Kakeya.realRpowENN delta (-2) = ENNReal.ofReal (1 / delta^2) := by
      simp only [Kakeya.realRpowENN]
      have h_neg : Real.rpow delta (-2) = 1 / delta^2 := by
        have h1 : Real.rpow delta (-2) = (Real.rpow delta 2)⁻¹ := Real.rpow_neg hdelta.le 2
        have h2 : Real.rpow delta 2 = delta^2 := by simp [Real.rpow_two]
        rw [h1, h2] <;> ring
      rw [h_neg]
    rw [h1, h2]
    have h3 : rho^2 * (1 / delta^2) = 4 / L^2 := by
      rw [hrho_eq]
      field_simp [hL_pos.ne', hdelta.ne'] <;> ring
    have h4 : ENNReal.ofReal (rho^2) * ENNReal.ofReal (1 / delta^2) =
        ENNReal.ofReal (rho^2 * (1 / delta^2)) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
    rw [h4, h3]
  have h_real_core := real_cardLoss_core hdelta hL_pos hm hm_ge heta htheta hlen
  rw [h_inv_eq]
  have h_split : Kakeya.realRpowENN delta (-2 - theta / 1000) =
      Kakeya.realRpowENN delta (-2) * Kakeya.realRpowENN delta (-(theta / 1000)) := by
    have h : (-2 - theta / 1000) = (-2 : ℝ) + (-(theta / 1000)) := by ring
    rw [h]
    exact realRpowENN_add hdelta (-2) (-(theta / 1000))
  have h_lhs_eq : ENNReal.ofReal (prod_real⁻¹) *
      (24 * massLoss * Kakeya.realRpowENN rho 2 * V1 *
        Kakeya.realRpowENN delta (-2 - theta / 1000)) =
      24 * massLoss * V1 *
        (ENNReal.ofReal (prod_real⁻¹ * (4 / L^2))) *
        Kakeya.realRpowENN delta (-(theta / 1000)) := by
    rw [h_split]
    have h_nonneg : 0 ≤ prod_real⁻¹ := by positivity
    have h_combine : ENNReal.ofReal (prod_real⁻¹) * ENNReal.ofReal (4 / L^2) =
        ENNReal.ofReal (prod_real⁻¹ * (4 / L^2)) := by
      rw [← ENNReal.ofReal_mul h_nonneg]
    have h_assoc : ENNReal.ofReal (prod_real⁻¹) *
        (24 * massLoss * Kakeya.realRpowENN rho 2 * V1 *
          (Kakeya.realRpowENN delta (-2) * Kakeya.realRpowENN delta (-(theta / 1000)))) =
        24 * massLoss * V1 *
          (ENNReal.ofReal (prod_real⁻¹) * (Kakeya.realRpowENN rho 2 * Kakeya.realRpowENN delta (-2))) *
          Kakeya.realRpowENN delta (-(theta / 1000)) := by ring
    rw [h_assoc, h_rho2_delta2, h_combine] <;> ring
  rw [h_lhs_eq]
  have h_real_expr : prod_real⁻¹ * (4 / L^2) = 4 / (m * rpow_theta * L^3) := by
    simp [hprod_real_def] <;> field_simp [hm.ne', hL_pos.ne'] <;> ring
  rw [h_real_expr]
  have h_bound : ENNReal.ofReal (4 / (m * rpow_theta * L^3)) ≤
      ENNReal.ofReal ((4 * (50 : ℝ)^3) * Real.rpow delta (-theta - eta / 25)) :=
    ENNReal.ofReal_mono h_real_core
  have h_bound2 : ENNReal.ofReal (4 / (m * rpow_theta * L^3)) ≤
      ENNReal.ofReal (4 * (50 : ℝ)^3) * Kakeya.realRpowENN delta (-theta - eta / 25) := by
    have h_ofReal_mul : ENNReal.ofReal ((4 * (50 : ℝ)^3) * Real.rpow delta (-theta - eta / 25)) =
        ENNReal.ofReal (4 * (50 : ℝ)^3) * Kakeya.realRpowENN delta (-theta - eta / 25) := by
      rw [ENNReal.ofReal_mul (by positivity)] <;> rfl
    rw [← h_ofReal_mul]
    exact h_bound
  have h_const : (24 : ENNReal) * ENNReal.ofReal (4 * (50 : ℝ)^3) =
      ENNReal.ofReal (24 / 50 * 4 * (50 : ℝ)^4) := by
    have h24 : (24 : ENNReal) = ENNReal.ofReal (24 : ℝ) := by simp
    rw [h24]
    have h_mul : ENNReal.ofReal (24 : ℝ) * ENNReal.ofReal (4 * (50 : ℝ)^3) =
        ENNReal.ofReal ((24 : ℝ) * (4 * (50 : ℝ)^3)) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
    rw [h_mul]
    have h_eq : (24 : ℝ) * (4 * (50 : ℝ)^3) = 24 / 50 * 4 * (50 : ℝ)^4 := by ring
    rw [h_eq]
  have h_exp : Kakeya.realRpowENN delta (-(eta / 10)) *
      Kakeya.realRpowENN delta (-theta - eta / 25) *
      Kakeya.realRpowENN delta (-(theta / 1000)) =
      Kakeya.realRpowENN delta (-theta * 1001 / 1000 - 7 * eta / 50) := by
    have h1 : Kakeya.realRpowENN delta (-(eta / 10)) *
        Kakeya.realRpowENN delta (-theta - eta / 25) =
        Kakeya.realRpowENN delta (-(eta / 10) + (-theta - eta / 25)) :=
      (realRpowENN_add hdelta (-(eta / 10)) (-theta - eta / 25)).symm
    rw [h1]
    have h2 : (-(eta / 10) + (-theta - eta / 25)) + (-(theta / 1000)) =
        -theta * 1001 / 1000 - 7 * eta / 50 := by ring
    rw [← realRpowENN_add hdelta (-(eta / 10) + (-theta - eta / 25)) (-(theta / 1000)), h2]
  have h_goal1 : 24 * massLoss * V1 *
      ENNReal.ofReal (4 / (m * rpow_theta * L^3)) *
      Kakeya.realRpowENN delta (-(theta / 1000)) ≤
    24 * (Kakeya.realRpowENN delta (-(eta / 10))) * V1 *
      (ENNReal.ofReal (4 * (50 : ℝ)^3) *
        Kakeya.realRpowENN delta (-theta - eta / 25)) *
      Kakeya.realRpowENN delta (-(theta / 1000)) := by
    have h1 : massLoss ≤ Kakeya.realRpowENN delta (-(eta / 10)) := h_massLoss
    have h2 : ENNReal.ofReal (4 / (m * rpow_theta * L^3)) ≤
        ENNReal.ofReal (4 * (50 : ℝ)^3) * Kakeya.realRpowENN delta (-theta - eta / 25) := h_bound2
    gcongr
  have h_ring : 24 * (Kakeya.realRpowENN delta (-(eta / 10))) * V1 *
      (ENNReal.ofReal (4 * (50 : ℝ)^3) * Kakeya.realRpowENN delta (-theta - eta / 25)) *
      Kakeya.realRpowENN delta (-(theta / 1000)) =
      ((24 : ENNReal) * ENNReal.ofReal (4 * (50 : ℝ)^3)) * V1 *
      (Kakeya.realRpowENN delta (-(eta / 10)) *
        Kakeya.realRpowENN delta (-theta - eta / 25) *
        Kakeya.realRpowENN delta (-(theta / 1000))) := by ring
  have h_goal2 : ((24 : ENNReal) * ENNReal.ofReal (4 * (50 : ℝ)^3)) * V1 *
      (Kakeya.realRpowENN delta (-(eta / 10)) *
        Kakeya.realRpowENN delta (-theta - eta / 25) *
        Kakeya.realRpowENN delta (-(theta / 1000))) =
    ENNReal.ofReal (24 / 50 * 4 * (50 : ℝ)^4) * V1 *
      Kakeya.realRpowENN delta (-theta * 1001 / 1000 - 7 * eta / 50) := by
    rw [h_const, h_exp] <;> ring
  exact h_goal1.trans (le_of_eq (h_ring.trans h_goal2))

/-- Absorb D into gap c < c': D * x^(-c) ≤ x^(-c') for small x. -/
lemma exists_scale_absorb_constant
    (D : ENNReal) (hD : D ≠ ⊤)
    {c c' : ℝ} (_hc : 0 ≤ c) (hgap : c < c') :
    ∃ x₀ : ℝ, 0 < x₀ ∧ x₀ ≤ 1 ∧
      ∀ x : ℝ, 0 < x → x ≤ x₀ →
        D * Kakeya.realRpowENN x (-c) ≤ Kakeya.realRpowENN x (-c') := by
  let gamma := c' - c
  have hgamma : 0 < gamma := by linarith
  rcases exists_delta_realRpowENN_bound D hD hgamma with
    ⟨x₀, hx₀_pos, hx₀_one, hbound⟩
  refine ⟨x₀, hx₀_pos, hx₀_one, ?_⟩
  intro x hx_pos hx_le
  have hD_bound : D ≤ Kakeya.realRpowENN x (-gamma) := hbound x hx_pos hx_le
  have hmul : Kakeya.realRpowENN x (-gamma) * Kakeya.realRpowENN x (-c) =
      Kakeya.realRpowENN x (-c') := by
    have h_eq : Kakeya.realRpowENN x (-gamma) * Kakeya.realRpowENN x (-c) =
        Kakeya.realRpowENN x ((-gamma) + (-c)) := (realRpowENN_add hx_pos (-gamma) (-c)).symm
    rw [h_eq]
    have h_exp : (-gamma) + (-c) = -c' := by simp [gamma] <;> ring
    rw [h_exp]
  calc
    D * Kakeya.realRpowENN x (-c)
      ≤ Kakeya.realRpowENN x (-gamma) * Kakeya.realRpowENN x (-c) := by gcongr
    _ = Kakeya.realRpowENN x (-c') := hmul

/-- Two-term sum absorption with intermediate exponent. -/
lemma exists_scale_absorb_sum2
    {a1 a2 c' : ℝ}
    (ha1_nonneg : 0 ≤ a1) (ha2_nonneg : 0 ≤ a2)
    (ha1 : a1 < c') (ha2 : a2 < c')
    (D1 D2 : ENNReal) (hD1 : D1 ≠ ⊤) (hD2 : D2 ≠ ⊤) :
    ∃ x₀ : ℝ, 0 < x₀ ∧ x₀ ≤ 1 ∧
      ∀ x : ℝ, 0 < x → x ≤ x₀ →
        D1 * Kakeya.realRpowENN x (-a1) +
        D2 * Kakeya.realRpowENN x (-a2) ≤
          Kakeya.realRpowENN x (-c') := by
  let amax := max a1 a2
  have hamax_lt : amax < c' := by
    simp only [amax, max_lt_iff] <;> constructor <;> tauto
  let c'' := (amax + c') / 2
  have h1 : amax < c'' := by dsimp only [c''] <;> linarith
  have h2 : c'' < c' := by dsimp only [c''] <;> linarith
  have hamax_nonneg : 0 ≤ amax := by
    have h : 0 ≤ a1 := ha1_nonneg
    exact le_trans h (le_max_left a1 a2)
  have hc''_nonneg : 0 ≤ c'' := by linarith [hamax_nonneg]
  have ha1_c'' : a1 < c'' := (le_max_left _ _).trans_lt h1
  have ha2_c'' : a2 < c'' := (le_max_right _ _).trans_lt h1
  rcases exists_scale_absorb_constant D1 hD1 ha1_nonneg ha1_c'' with ⟨x1, _, hx1_one, hb1⟩
  rcases exists_scale_absorb_constant D2 hD2 ha2_nonneg ha2_c'' with ⟨x2, _, hx2_one, hb2⟩
  rcases exists_scale_absorb_constant (2 : ENNReal) (by norm_num) hc''_nonneg h2 with
    ⟨x3, _, hx3_one, hb3⟩
  let x₀ := min x1 (min x2 x3)
  have hx₀_pos : 0 < x₀ := by positivity
  have hx₀_one : x₀ ≤ 1 := (min_le_left _ _).trans hx1_one
  refine ⟨x₀, hx₀_pos, hx₀_one, ?_⟩
  intro x hx_pos hx_le
  have hle1 : x ≤ x1 := hx_le.trans (min_le_left _ _)
  have hle2 : x ≤ x2 := hx_le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hle3 : x ≤ x3 := hx_le.trans ((min_le_right _ _).trans (min_le_right _ _))
  have h1' : D1 * Kakeya.realRpowENN x (-a1) ≤ Kakeya.realRpowENN x (-c'') := hb1 x hx_pos hle1
  have h2' : D2 * Kakeya.realRpowENN x (-a2) ≤ Kakeya.realRpowENN x (-c'') := hb2 x hx_pos hle2
  have hsum : D1 * Kakeya.realRpowENN x (-a1) + D2 * Kakeya.realRpowENN x (-a2) ≤
      2 * Kakeya.realRpowENN x (-c'') := by
    calc
      _ ≤ Kakeya.realRpowENN x (-c'') + Kakeya.realRpowENN x (-c'') := by gcongr
      _ = 2 * Kakeya.realRpowENN x (-c'') := by ring
  have hfinal : (2 : ENNReal) * Kakeya.realRpowENN x (-c'') ≤ Kakeya.realRpowENN x (-c') :=
    hb3 x hx_pos hle3
  exact hsum.trans hfinal

/-- Three-term sum absorption with intermediate exponent. -/
lemma exists_scale_absorb_sum3
    {a1 a2 a3 c' : ℝ}
    (ha1_nonneg : 0 ≤ a1) (ha2_nonneg : 0 ≤ a2) (ha3_nonneg : 0 ≤ a3)
    (ha1 : a1 < c') (ha2 : a2 < c') (ha3 : a3 < c')
    (D1 D2 D3 : ENNReal) (hD1 : D1 ≠ ⊤) (hD2 : D2 ≠ ⊤) (hD3 : D3 ≠ ⊤) :
    ∃ x₀ : ℝ, 0 < x₀ ∧ x₀ ≤ 1 ∧
      ∀ x : ℝ, 0 < x → x ≤ x₀ →
        D1 * Kakeya.realRpowENN x (-a1) +
        D2 * Kakeya.realRpowENN x (-a2) +
        D3 * Kakeya.realRpowENN x (-a3) ≤
          Kakeya.realRpowENN x (-c') := by
  let amax := max a1 (max a2 a3)
  have hamax_lt : amax < c' := by
    simp only [amax, max_lt_iff] <;> constructor <;> tauto
  let c'' := (amax + c') / 2
  have h1 : amax < c'' := by dsimp only [c''] <;> linarith
  have h2 : c'' < c' := by dsimp only [c''] <;> linarith
  have hamax_nonneg : 0 ≤ amax := by
    have h : 0 ≤ a1 := ha1_nonneg
    exact le_trans h (le_max_left a1 (max a2 a3))
  have hc''_nonneg : 0 ≤ c'' := by linarith [hamax_nonneg]
  have ha1_c'' : a1 < c'' := (le_max_left _ _).trans_lt h1
  have ha2_c'' : a2 < c'' := by
    exact (le_trans (le_max_left _ _) (le_max_right _ _)).trans_lt h1
  have ha3_c'' : a3 < c'' := by
    exact (le_trans (le_max_right _ _) (le_max_right _ _)).trans_lt h1
  rcases exists_scale_absorb_constant D1 hD1 ha1_nonneg ha1_c'' with ⟨x1, _, hx1_one, hb1⟩
  rcases exists_scale_absorb_constant D2 hD2 ha2_nonneg ha2_c'' with ⟨x2, _, hx2_one, hb2⟩
  rcases exists_scale_absorb_constant D3 hD3 ha3_nonneg ha3_c'' with ⟨x3, _, hx3_one, hb3⟩
  rcases exists_scale_absorb_constant (3 : ENNReal) (by norm_num) hc''_nonneg h2 with
    ⟨x4, _, hx4_one, hb4⟩
  let x₀ := min x1 (min x2 (min x3 x4))
  have hx₀_pos : 0 < x₀ := by positivity
  have hx₀_one : x₀ ≤ 1 := (min_le_left _ _).trans hx1_one
  refine ⟨x₀, hx₀_pos, hx₀_one, ?_⟩
  intro x hx_pos hx_le
  have hle1 : x ≤ x1 := hx_le.trans (min_le_left _ _)
  have hle2 : x ≤ x2 := hx_le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hle3 : x ≤ x3 :=
    hx_le.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hle4 : x ≤ x4 :=
    hx_le.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have h1' : D1 * Kakeya.realRpowENN x (-a1) ≤ Kakeya.realRpowENN x (-c'') := hb1 x hx_pos hle1
  have h2' : D2 * Kakeya.realRpowENN x (-a2) ≤ Kakeya.realRpowENN x (-c'') := hb2 x hx_pos hle2
  have h3' : D3 * Kakeya.realRpowENN x (-a3) ≤ Kakeya.realRpowENN x (-c'') := hb3 x hx_pos hle3
  have hsum : D1 * Kakeya.realRpowENN x (-a1) + D2 * Kakeya.realRpowENN x (-a2) +
      D3 * Kakeya.realRpowENN x (-a3) ≤ 3 * Kakeya.realRpowENN x (-c'') := by
    calc
      _ ≤ Kakeya.realRpowENN x (-c'') + Kakeya.realRpowENN x (-c'') + Kakeya.realRpowENN x (-c'') := by gcongr
      _ = 3 * Kakeya.realRpowENN x (-c'') := by ring
  have hfinal : (3 : ENNReal) * Kakeya.realRpowENN x (-c'') ≤ Kakeya.realRpowENN x (-c') :=
    hb4 x hx_pos hle4
  exact hsum.trans hfinal

/-- Power conversion: if y ≤ C * x^p and a < p*b, then x^(-a) ≤ y^(-b) for small x. -/
lemma exists_scale_power_conversion
    {C p a b : ℝ}
    (hC : 1 ≤ C) (hp : 0 < p) (ha : 0 ≤ a) (h_ab : a < p * b) :
    ∃ x₀ : ℝ, 0 < x₀ ∧ x₀ ≤ 1 ∧
      ∀ (x y : ℝ), 0 < x → x ≤ x₀ → 0 < y → y ≤ 1 →
        y ≤ C * x ^ p →
        Kakeya.realRpowENN x (-a) ≤ Kakeya.realRpowENN y (-b) := by
  have h_ap_lt_b : a / p < b := by
    have h : a / p < b := by
      calc a / p < (p * b) / p := by gcongr
        _ = b := by field_simp [hp.ne'] <;> ring
    exact h
  let b' := (a / p + b) / 2
  have h1 : a / p < b' := by dsimp only [b'] <;> linarith
  have h2 : b' < b := by dsimp only [b'] <;> linarith
  have hb_pos : 0 < b := by
    have h : 0 ≤ a := ha
    have h' : a < p * b := h_ab
    nlinarith
  have h_b'_nonneg : 0 ≤ b' := by
    have h_ap_nonneg : 0 ≤ a / p := by positivity
    dsimp only [b'] <;> linarith [hb_pos, h_ap_nonneg]
  have hCpos : 0 < C := by linarith
  have hCpow_nonneg : 0 ≤ C ^ (a / p) := by positivity
  let D : ENNReal := ENNReal.ofReal (C ^ (a / p))
  have hD_ne_top : D ≠ ⊤ := ENNReal.ofReal_ne_top
  rcases exists_scale_absorb_constant D hD_ne_top h_b'_nonneg h2 with
    ⟨y₀, hy₀_pos, hy₀_one, hbound_absorb⟩
  have h_y0_C_pos : 0 < y₀ / C := by positivity
  let x_cutoff := (y₀ / C) ^ (1 / p)
  have hx_cutoff_pos : 0 < x_cutoff := Real.rpow_pos_of_pos h_y0_C_pos _
  let x₀ := min 1 x_cutoff
  have hx₀_pos : 0 < x₀ := by positivity
  have hx₀_one : x₀ ≤ 1 := min_le_left _ _
  refine ⟨x₀, hx₀_pos, hx₀_one, ?_⟩
  intro x y hx_pos hx_le hy_pos hy_one h_y_bound
  have hx_le_cutoff : x ≤ x_cutoff := hx_le.trans (min_le_right _ _)
  have hxp : x ^ p ≤ y₀ / C := by
    have h : x ^ p ≤ x_cutoff ^ p := Real.rpow_le_rpow hx_pos.le hx_le_cutoff hp.le
    have h2 : x_cutoff ^ p = y₀ / C := by
      simp only [x_cutoff]
      rw [← Real.rpow_mul h_y0_C_pos.le]
      have h3 : (1 / p) * p = 1 := by field_simp [hp.ne'] <;> ring
      rw [h3, Real.rpow_one]
    rw [h2] at h
    exact h
  have h_C_xp : C * x ^ p ≤ y₀ := by
    calc C * x ^ p ≤ C * (y₀ / C) := by gcongr
      _ = y₀ := by field_simp [hCpos.ne'] <;> ring
  have hy_le_y0 : y ≤ y₀ := h_y_bound.trans h_C_xp
  have h_xp_pos : 0 < x ^ p := by positivity
  have h_xpow : Real.rpow x (-a) = Real.rpow (x ^ p) (-(a / p)) := by
    have h : Real.rpow (x ^ p) (-(a / p)) = Real.rpow x (p * (-(a / p))) :=
      (Real.rpow_mul hx_pos.le p (-(a / p))).symm
    have h5 : p * (-(a / p)) = -a := by field_simp [hp.ne'] <;> ring
    rw [h, h5]
  let a_rpow := Real.rpow (x ^ p) (-(a / p))
  let b_rpow := Real.rpow y (-(a / p))
  let b'_rpow := Real.rpow y (-b')
  have h_yC_pos : 0 < y / C := by positivity
  have h_yC_le_xp : y / C ≤ x ^ p := by
    calc y / C ≤ (C * x ^ p) / C := by gcongr
      _ = x ^ p := by field_simp [hCpos.ne'] <;> ring
  have h_ap_nonneg2 : 0 ≤ a / p := by positivity
  have h_neg : -(a / p) ≤ 0 := by linarith [h_ap_nonneg2]
  have h_mono : a_rpow ≤ Real.rpow (y / C) (-(a / p)) :=
    Real.rpow_le_rpow_of_nonpos h_yC_pos h_yC_le_xp h_neg
  have h_yC_rpow : Real.rpow (y / C) (-(a / p)) = C ^ (a / p) * b_rpow := by
    have hdiv : Real.rpow (y / C) (-(a / p)) =
        Real.rpow y (-(a / p)) / Real.rpow C (-(a / p)) :=
      (Real.div_rpow hy_pos.le hCpos.le) _
    rw [hdiv]
    have h_C_neg : Real.rpow C (-(a / p)) = (Real.rpow C (a / p))⁻¹ := by
      simpa using Real.rpow_neg hCpos.le (a / p)
    rw [h_C_neg]
    have h6 : b_rpow / (Real.rpow C (a / p))⁻¹ = Real.rpow C (a / p) * b_rpow := by
      field_simp [hCpos.ne'] <;> ring
    rw [h6] <;> rfl
  have h_anti : b_rpow ≤ b'_rpow := by
    have hlog : Real.log y ≤ 0 := by apply Real.log_nonpos <;> linarith
    have hmul : Real.log y * (-(a / p)) ≤ Real.log y * (-b') := by
      have h : -(a / p) ≥ -b' := by linarith
      nlinarith
    have h_exp : Real.exp (Real.log y * (-(a / p))) ≤ Real.exp (Real.log y * (-b')) :=
      Real.exp_le_exp.mpr hmul
    have h_goal : Real.rpow y (-(a / p)) ≤ Real.rpow y (-b') := by
      simpa [Real.rpow_def_of_pos hy_pos] using h_exp
    exact h_goal
  have h_final : a_rpow ≤ C ^ (a / p) * b'_rpow := by
    calc a_rpow
        ≤ Real.rpow (y / C) (-(a / p)) := h_mono
      _ = C ^ (a / p) * b_rpow := h_yC_rpow
      _ ≤ C ^ (a / p) * b'_rpow := by gcongr <;> positivity
  have h_ennreal : Kakeya.realRpowENN x (-a) ≤ D * Kakeya.realRpowENN y (-b') := by
    simp only [Kakeya.realRpowENN, h_xpow]
    have h_mul : ENNReal.ofReal (C ^ (a / p) * Real.rpow y (-b')) =
        D * ENNReal.ofReal (Real.rpow y (-b')) := by
      rw [ENNReal.ofReal_mul hCpow_nonneg] <;> rfl
    have h : ENNReal.ofReal a_rpow ≤ ENNReal.ofReal (C ^ (a / p) * Real.rpow y (-b')) :=
      ENNReal.ofReal_mono h_final
    rw [h_mul] at *
    exact h
  have h_absorb : D * Kakeya.realRpowENN y (-b') ≤ Kakeya.realRpowENN y (-b) :=
    hbound_absorb y hy_pos hy_le_y0
  exact h_ennreal.trans h_absorb

/-- Absorb `D * (1 + log δ⁻¹)^n` into `δ^(-B)` in `ENNReal`. -/
lemma exists_delta_log_absorbed_ennreal
    (D : ENNReal) (hD : D ≠ ⊤)
    {B : ℝ} (hB : 0 < B)
    {n : ℕ} (hn_pos : 0 < n) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
        D * (ENNReal.ofReal (1 + Real.log δ⁻¹)) ^ n ≤
          Kakeya.realRpowENN δ (-B) := by
  by_cases hD_zero : D = 0
  · rw [hD_zero]
    exact ⟨1, by norm_num, le_rfl, fun _ _ _ => by simp⟩
  have hD_real_pos : 0 < D.toReal :=
    ENNReal.toReal_pos hD_zero hD
  rcases exists_delta_log_absorbed
      D.toReal hD_real_pos hB hn_pos with
    ⟨δ₀, hδ₀_pos, hδ₀_one, hbound⟩
  refine ⟨δ₀, hδ₀_pos, hδ₀_one, ?_⟩
  intro δ hδ hδ_le
  have hδ_one : δ ≤ 1 := hδ_le.trans hδ₀_one
  have hlog_nonneg : 0 ≤ 1 + Real.log δ⁻¹ := by
    have h1 : 0 ≤ Real.log δ⁻¹ := by
      apply Real.log_nonneg
      calc
        (1 : ℝ) ≤ (1 : ℝ)⁻¹ := by norm_num
        _ ≤ δ⁻¹ := by gcongr
    linarith
  have hpow :
      (ENNReal.ofReal (1 + Real.log δ⁻¹)) ^ n =
        ENNReal.ofReal ((1 + Real.log δ⁻¹) ^ n) :=
    (ENNReal.ofReal_pow hlog_nonneg n).symm
  have hD_repr : D = ENNReal.ofReal D.toReal :=
    (ENNReal.ofReal_toReal hD).symm
  rw [hD_repr, hpow]
  have hmul :
      ENNReal.ofReal D.toReal *
          ENNReal.ofReal ((1 + Real.log δ⁻¹) ^ n) =
        ENNReal.ofReal
          (D.toReal * (1 + Real.log δ⁻¹) ^ n) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
  rw [hmul]
  exact ENNReal.ofReal_mono (hbound δ hδ hδ_le)

/--
Absorb `D * (C * (1 + log δ⁻¹))^n` into `δ^(-B)` in `ENNReal`.
-/
lemma exists_delta_C_pow_log_absorbed_ennreal
    (D : ENNReal) (hD : D ≠ ⊤)
    (C : ℝ) (hC : 0 ≤ C)
    {B : ℝ} (hB : 0 < B)
    {n : ℕ} (hn_pos : 0 < n) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
        D *
            (ENNReal.ofReal
              (C * (1 + Real.log δ⁻¹))) ^ n ≤
          Kakeya.realRpowENN δ (-B) := by
  by_cases hC_zero : C = 0
  · refine ⟨1, by norm_num, le_rfl, fun _ _ _ => ?_⟩
    rw [hC_zero]
    simp [hn_pos.ne']
  have hC_pos : 0 < C := lt_of_le_of_ne hC (Ne.symm hC_zero)
  let C_pow : ℝ := C ^ n
  have hC_pow_pos : 0 < C_pow := by positivity
  let D' : ENNReal := D * ENNReal.ofReal C_pow
  have hD'_ne_top : D' ≠ ⊤ :=
    ENNReal.mul_ne_top hD ENNReal.ofReal_ne_top
  rcases exists_delta_log_absorbed_ennreal
      D' hD'_ne_top hB hn_pos with
    ⟨δ₀, hδ₀_pos, hδ₀_one, hbound⟩
  refine ⟨δ₀, hδ₀_pos, hδ₀_one, ?_⟩
  intro δ hδ hδ_le
  have hδ_one : δ ≤ 1 := hδ_le.trans hδ₀_one
  have hlog_nonneg : 0 ≤ 1 + Real.log δ⁻¹ := by
    have h1 : 0 ≤ Real.log δ⁻¹ := by
      apply Real.log_nonneg
      calc
        (1 : ℝ) ≤ (1 : ℝ)⁻¹ := by norm_num
        _ ≤ δ⁻¹ := by gcongr
    linarith
  have hmul :
      ENNReal.ofReal (C * (1 + Real.log δ⁻¹)) =
        ENNReal.ofReal C *
          ENNReal.ofReal (1 + Real.log δ⁻¹) := by
    rw [← ENNReal.ofReal_mul hC_pos.le]
  have hpow :
      (ENNReal.ofReal
          (C * (1 + Real.log δ⁻¹))) ^ n =
        ENNReal.ofReal C_pow *
          (ENNReal.ofReal (1 + Real.log δ⁻¹)) ^ n := by
    rw [hmul, mul_pow]
    have h :
        (ENNReal.ofReal C) ^ n =
          ENNReal.ofReal C_pow :=
      (ENNReal.ofReal_pow hC_pos.le n).symm
    rw [h]
  calc
    D * (ENNReal.ofReal
          (C * (1 + Real.log δ⁻¹))) ^ n
        = D *
            (ENNReal.ofReal C_pow *
              (ENNReal.ofReal
                (1 + Real.log δ⁻¹)) ^ n) := by
          rw [hpow]
    _ = D' *
          (ENNReal.ofReal (1 + Real.log δ⁻¹)) ^ n := by
        simp only [D']
        rw [mul_assoc]
    _ ≤ Kakeya.realRpowENN δ (-B) :=
      hbound δ hδ hδ_le

/--
If `sigma ≥ delta^(1-outputLoss)`, the target-radius constant dominates
`delta^(-outputLoss^2)`.
-/
lemma target_constant_lower_bound
    {outputLoss delta sigma : ℝ}
    (h_outputLoss_pos : 0 < outputLoss)
    (h_delta_pos : 0 < delta)
    (h_sigma_lower :
      Real.rpow delta (1 - outputLoss) ≤ sigma) :
    Kakeya.realRpowENN delta (-(outputLoss ^ 2)) ≤
      Kakeya.realRpowENN (delta / sigma) (-outputLoss) := by
  have h_sigma_pos : 0 < sigma := by
    have h1 : 0 < Real.rpow delta (1 - outputLoss) :=
      Real.rpow_pos_of_pos h_delta_pos _
    linarith
  have h_ds_pos : 0 < delta / sigma := by positivity
  have h_delta_rpow_nonneg :
      0 ≤ Real.rpow delta (-outputLoss) :=
    Real.rpow_nonneg h_delta_pos.le _
  have h_div :
      Real.rpow delta (1 - outputLoss) / delta =
        Real.rpow delta (-outputLoss) := by
    have h1 :
        Real.rpow delta (1 - outputLoss) / delta =
          Real.rpow delta (1 - outputLoss) *
            Real.rpow delta (-1) := by
      have h2 : Real.rpow delta (-1) = delta⁻¹ := by
        simpa [Real.rpow_one] using
          Real.rpow_neg h_delta_pos.le 1
      rw [h2]
      field_simp [h_delta_pos.ne']
    rw [h1]
    have h3 :
        Real.rpow delta (1 - outputLoss) *
            Real.rpow delta (-1) =
          Real.rpow delta
            ((1 - outputLoss) + (-1 : ℝ)) := by
      exact
        (Real.rpow_add h_delta_pos
          (1 - outputLoss) (-1)).symm
    rw [h3]
    have h4 : (1 - outputLoss) + (-1 : ℝ) = -outputLoss := by
      ring
    rw [h4]
  have h1 : Real.rpow delta (-outputLoss) ≤ sigma / delta := by
    have h2 :
        Real.rpow delta (1 - outputLoss) / delta ≤
          sigma / delta := by
      gcongr
    rw [h_div] at h2
    exact h2
  have h2 :
      Real.rpow
          (Real.rpow delta (-outputLoss)) outputLoss ≤
        Real.rpow (sigma / delta) outputLoss := by
    exact
      Real.rpow_le_rpow
        h_delta_rpow_nonneg h1 h_outputLoss_pos.le
  have h3 :
      Real.rpow
          (Real.rpow delta (-outputLoss)) outputLoss =
        Real.rpow delta (-(outputLoss ^ 2)) := by
    have h31 :
        Real.rpow
            (Real.rpow delta (-outputLoss)) outputLoss =
          Real.rpow delta ((-outputLoss) * outputLoss) :=
      (Real.rpow_mul h_delta_pos.le
        (-outputLoss) outputLoss).symm
    rw [h31]
    have h32 :
        (-outputLoss) * outputLoss =
          -(outputLoss ^ 2) := by
      ring
    rw [h32]
  have h4 :
      Real.rpow (delta / sigma) (-outputLoss) =
        Real.rpow (sigma / delta) outputLoss := by
    have h41 :
        Real.rpow (delta / sigma) (-outputLoss) =
          (Real.rpow (delta / sigma) outputLoss)⁻¹ :=
      Real.rpow_neg h_ds_pos.le outputLoss
    have h42 :
        Real.rpow ((delta / sigma)⁻¹) outputLoss =
          (Real.rpow (delta / sigma) outputLoss)⁻¹ :=
      Real.inv_rpow h_ds_pos.le outputLoss
    have h43 : (delta / sigma)⁻¹ = sigma / delta := by
      field_simp [h_delta_pos.ne', h_sigma_pos.ne']
    calc
      Real.rpow (delta / sigma) (-outputLoss) =
          (Real.rpow (delta / sigma) outputLoss)⁻¹ := h41
      _ = Real.rpow ((delta / sigma)⁻¹) outputLoss := h42.symm
      _ = Real.rpow (sigma / delta) outputLoss := by rw [h43]
  have h5 :
      Real.rpow delta (-(outputLoss ^ 2)) ≤
        Real.rpow (delta / sigma) (-outputLoss) := by
    calc
      Real.rpow delta (-(outputLoss ^ 2)) =
          Real.rpow
            (Real.rpow delta (-outputLoss)) outputLoss := h3.symm
      _ ≤ Real.rpow (sigma / delta) outputLoss := h2
      _ = Real.rpow (delta / sigma) (-outputLoss) := h4.symm
  simpa [Kakeya.realRpowENN] using
    ENNReal.ofReal_mono h5

/--
The source geometric ratio is strictly smaller than the target nearby-window
constant when `inputLoss < outputLoss^2`.
-/
lemma ratio_lt_target
    {delta sigma outputLoss inputLoss : ℝ}
    (hdelta_pos : 0 < delta)
    (hdelta_lt_one : delta < 1)
    (houtputLoss_pos : 0 < outputLoss)
    (hinputLoss_lt : inputLoss < outputLoss ^ 2)
    (hsigma_lower :
      Real.rpow delta (1 - outputLoss) ≤ sigma) :
    ENNReal.ofReal (Real.rpow delta (-inputLoss)) <
      Kakeya.realRpowENN (delta / sigma) (-outputLoss) := by
  have h1 : -inputLoss > -(outputLoss ^ 2) := by
    linarith
  have h2 :
      Real.rpow delta (-inputLoss) <
        Real.rpow delta (-(outputLoss ^ 2)) :=
    Real.rpow_lt_rpow_of_exponent_gt
      hdelta_pos hdelta_lt_one h1
  have h_pos2 :
      0 < Real.rpow delta (-(outputLoss ^ 2)) :=
    Real.rpow_pos_of_pos hdelta_pos _
  have h3 :
      ENNReal.ofReal (Real.rpow delta (-inputLoss)) <
        ENNReal.ofReal
          (Real.rpow delta (-(outputLoss ^ 2))) :=
    (ENNReal.ofReal_lt_ofReal_iff h_pos2).mpr h2
  have h4 :
      Kakeya.realRpowENN delta (-(outputLoss ^ 2)) ≤
        Kakeya.realRpowENN (delta / sigma) (-outputLoss) :=
    target_constant_lower_bound
      houtputLoss_pos hdelta_pos hsigma_lower
  have h5 :
      ENNReal.ofReal
          (Real.rpow delta (-(outputLoss ^ 2))) =
        Kakeya.realRpowENN delta (-(outputLoss ^ 2)) := by
    simp [Kakeya.realRpowENN]
  rw [h5] at h3
  exact lt_of_lt_of_le h3 h4

/--
For `0 < delta ≤ 1` and positive `middleLoss`,
`delta^(-middleLoss) ≥ 1`.
-/
lemma middleConstant_ge_one
    {delta middleLoss : ℝ}
    (hdelta_pos : 0 < delta)
    (hdelta_one : delta ≤ 1)
    (hmiddleLoss_pos : 0 < middleLoss) :
    (1 : ENNReal) ≤
      Kakeya.realRpowENN delta (-middleLoss) := by
  have h1 : Real.rpow delta middleLoss ≤ 1 :=
    Real.rpow_le_one
      hdelta_pos.le hdelta_one hmiddleLoss_pos.le
  have h2 : 0 < Real.rpow delta middleLoss :=
    Real.rpow_pos_of_pos hdelta_pos _
  have h3 : (Real.rpow delta middleLoss)⁻¹ ≥ 1 := by
    have h6 :
        (1 : ℝ) / (1 : ℝ) ≤
          (1 : ℝ) / Real.rpow delta middleLoss :=
      one_div_le_one_div_of_le h2 h1
    norm_num at h6 ⊢
    exact h6
  have h6 :
      Real.rpow delta (-middleLoss) =
        (Real.rpow delta middleLoss)⁻¹ :=
    Real.rpow_neg hdelta_pos.le middleLoss
  have h7 : 1 ≤ Real.rpow delta (-middleLoss) := by
    rw [h6]
    exact h3
  have h8 :
      (1 : ENNReal) ≤
        ENNReal.ofReal
          (Real.rpow delta (-middleLoss)) := by
    simpa using ENNReal.ofReal_mono h7
  simpa [Kakeya.realRpowENN] using h8

end Kakeya.Assouad
