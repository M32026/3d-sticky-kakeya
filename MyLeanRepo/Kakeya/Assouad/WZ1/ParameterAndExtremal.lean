import MyLeanRepo.Kakeya.Assouad.WZ1.FineMultiplicityRefinement
import MyLeanRepo.Kakeya.Assouad.ExtremalInfrastructure
import MyLeanRepo.Kakeya.Assouad.Definitions
import MyLeanRepo.Kakeya.Assouad.EssentiallyDistinctCardBound
import Mathlib.Tactic

/-!
# Parameter preparation and refined extremality for WZ1 balanced cover

Implements two key steps:
1. Parameter preparation: choose η, δ₀, derive hypotheses for fine_multiplicity_refinement
2. Refined extremality: prove IsExtremalPair sigma epsilon for the refined shading

## Key strategy

Apply `HasCriticalVolumeFloor` with `loss = ε` → get `(η_floor, δ₀_floor)`.
Let `ε' := min(η_floor, ε)`.
Choose `η_ext := ε' / 4`.
Run `fine_multiplicity_refinement` with target `ε'` (not the outer `ε`).

Since `ε' ≤ ε`:
- Multiplicity: `m ≥ δ^(-σ+ε') ≥ δ^(-σ+ε)` ✓
- Mass: `refined.mass ≥ δ^ε' · F.mass ≥ δ^ε · F.mass` ✓
- Floor density: `δ^ε' ≥ δ^η_floor` (since `ε' ≤ η_floor`), so `refined.mass ≥ δ^η_floor · F.mass` ✓

Thus `HasCriticalVolumeFloor` applies directly to `refined`, giving `volume(refined) ≥ δ^(σ+ε)`.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

/--
Polynomial dominates logarithm: for any `C1, C2 ≥ 0` and `b > 0`, there exists
`0 < δ₀ ≤ 1` such that for all `0 < δ ≤ δ₀`,
`C1 + C2 * log(1/δ) ≤ δ^(-b)`.
-/
lemma log_poly_bound {C1 C2 b : ℝ} (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hb : 0 < b) :
    ∃ (δ₀ : ℝ), 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ (δ : ℝ), 0 < δ → δ ≤ δ₀ →
        C1 + C2 * Real.log (1 / δ) ≤ δ^(-b) := by
  let C : ℝ := max C1 (max C2 1)
  have hC1' : C1 ≤ C := le_max_left _ _
  have hC2' : C2 ≤ C := by
    have h : C2 ≤ max C2 1 := le_max_left _ _
    exact le_trans h (le_max_right _ _)
  have hC_pos : 0 < C := by
    have h1 : 1 ≤ max C2 1 := le_max_right _ _
    have h2 : 1 ≤ C := le_trans h1 (le_max_right _ _)
    linarith
  let K : ℝ := 4 * C / b
  have hK_pos : 0 < K := by positivity
  let X1 : ℝ := Real.exp 1
  let X2 : ℝ := K^(2 / b)
  have hX2_pos : 0 < X2 := Real.rpow_pos_of_pos hK_pos _
  let X : ℝ := max X1 X2
  have hX_pos : 0 < X := by positivity
  have hX_ge_e : X ≥ Real.exp 1 := le_max_left _ _
  have hX_ge_K : X ≥ X2 := le_max_right _ _
  let δ₀ : ℝ := X⁻¹
  have hδ₀_pos : 0 < δ₀ := by positivity
  have hδ₀_le_one : δ₀ ≤ 1 := by
    have h1 : X ≥ 1 := by
      have h2 : Real.exp 1 > 1 := by
        have h3 : Real.exp 1 > Real.exp 0 := Real.exp_strictMono (by norm_num)
        simpa using h3
      linarith [hX_ge_e]
    have h4 : X⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
    exact h4
  refine' ⟨δ₀, hδ₀_pos, hδ₀_le_one, _⟩
  intro δ hδ_pos hδ_le
  set x : ℝ := 1 / δ with hx_def
  have hx_pos : 0 < x := by positivity
  have hx_ge_X : x ≥ X := by
    have h1 : δ ≤ X⁻¹ := hδ_le
    have h2 : 1 / δ ≥ X := by
      calc
        1 / δ ≥ 1 / X⁻¹ := by gcongr
        _ = X := by field_simp [hX_pos.ne'] <;> ring
    exact h2
  have hx_ge_e : x ≥ Real.exp 1 := hX_ge_e.trans hx_ge_X
  have hx_ge_K : x ≥ X2 := hX_ge_K.trans hx_ge_X
  have h_log1 : Real.log x ≥ 1 := by
    have h3 : Real.log x ≥ Real.log (Real.exp 1) := Real.log_le_log (by positivity) hx_ge_e
    have h4 : Real.log (Real.exp 1) = 1 := Real.log_exp 1
    linarith
  have h_log2 : Real.log x ≤ (2 / b) * x^(b / 2) := by
    have h5 : Real.log (x^(b / 2)) ≤ x^(b / 2) - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have h6 : Real.log (x^(b / 2)) = (b / 2) * Real.log x := by
      rw [Real.log_rpow (by positivity)] <;> ring
    rw [h6] at h5
    have h7 : (b / 2) * Real.log x ≤ x^(b / 2) := by linarith
    have h9 : 0 < b / 2 := by positivity
    have h10 : Real.log x ≤ (x^(b / 2)) / (b / 2) := by
      calc
        Real.log x = ((b / 2) * Real.log x) / (b / 2) := by field_simp [h9.ne'] <;> ring
        _ ≤ (x^(b / 2)) / (b / 2) := by gcongr
    have h11 : (x^(b / 2)) / (b / 2) = (2 / b) * x^(b / 2) := by
      field_simp [h9.ne'] <;> ring
    rw [h11] at h10
    exact h10
  have h_x_b2_ge : x^(b / 2) ≥ K := by
    have h12 : x ≥ K^(2 / b) := hx_ge_K
    have h13 : 0 < b / 2 := by positivity
    have h14 : x^(b / 2) ≥ (K^(2 / b))^(b / 2) := Real.rpow_le_rpow (by positivity) h12 h13.le
    have h15 : (K^(2 / b))^(b / 2) = K := by
      rw [← Real.rpow_mul hK_pos.le]
      have h16 : (2 / b) * (b / 2) = 1 := by field_simp [hb.ne'] <;> ring
      rw [h16, Real.rpow_one]
    rw [h15] at h14
    exact h14
  have h_main1 : C1 + C2 * Real.log x ≤ C * (1 + Real.log x) := by
    have h16 : C1 ≤ C := hC1'
    have h17 : C2 * Real.log x ≤ C * Real.log x := by gcongr <;> linarith
    linarith
  have h_main2 : C * (1 + Real.log x) ≤ 2 * C * Real.log x := by
    have h18 : 1 ≤ Real.log x := h_log1
    nlinarith
  have h_main3 : 2 * C * Real.log x ≤ (4 * C / b) * x^(b / 2) := by
    calc
      2 * C * Real.log x ≤ 2 * C * ((2 / b) * x^(b / 2)) := by gcongr
      _ = (4 * C / b) * x^(b / 2) := by ring
  have h_main4 : (4 * C / b) * x^(b / 2) ≤ x^b := by
    have h19 : x^(b / 2) ≥ K := h_x_b2_ge
    have h20 : 0 < x^(b / 2) := by positivity
    have h21 : (4 * C / b) * x^(b / 2) ≤ x^(b / 2) * x^(b / 2) := by gcongr <;> linarith
    have h22 : x^(b / 2) * x^(b / 2) = x^b := by
      have h23 : x^(b / 2) * x^(b / 2) = x^((b / 2) + (b / 2)) := by
        rw [← Real.rpow_add (by positivity)] <;> ring
      rw [h23]
      have h24 : (b / 2) + (b / 2) = b := by ring
      rw [h24]
    rw [h22] at h21
    exact h21
  have h_final : C1 + C2 * Real.log x ≤ x^b := by
    calc
      C1 + C2 * Real.log x ≤ C * (1 + Real.log x) := h_main1
      _ ≤ 2 * C * Real.log x := h_main2
      _ ≤ (4 * C / b) * x^(b / 2) := h_main3
      _ ≤ x^b := h_main4
  have h_rpow : δ^(-b) = x^b := by
    have hx : x = 1 / δ := by rfl
    rw [hx]
    have h_eq : δ^(-b) = (1 / δ)^b := by
      have h1 : δ^(-b) = δ⁻¹^b := Real.rpow_neg_eq_inv_rpow δ b
      have h2 : δ⁻¹ = (1 / δ : ℝ) := by field_simp
      rw [h1, h2]
    exact h_eq
  rw [h_rpow]
  exact h_final

/--
Cardinality bound for fine_multiplicity_refinement.

Uses the geometric packing bound `essentially_distinct_card_bound` to get
`F.card ≤ 35^6 · δ^(-6)`, then converts to a logarithmic bound and uses
`log_poly_bound` to show `2·(log₂ F.card + 1) ≤ δ^(η-ε')`.
-/
lemma cardinality_bound_from_extremal
    {delta sigma eta epsilon' : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    (hdelta_small : delta < 1 / 16)
    (hExt : IsExtremalPair sigma eta F U Y)
    (heta_lt_epsilon' : 3 * eta < epsilon')
    (h_log_bound : 2 * (Real.log ((35 : ℝ)^6 * Real.rpow delta (-6)) / Real.log 2 + 1) ≤
        Real.rpow delta (eta - epsilon')) :
    2 * (Nat.log 2 F.card + 1 : ENNReal) ≤
      Kakeya.realRpowENN delta (eta - epsilon') := by
  rcases hExt with ⟨_, _, hF_nonempty, hF_ball, hF_distinct, _, _, _, _, _⟩
  have h_card_real : (F.card : ℝ) ≤ (35 : ℝ)^6 * Real.rpow delta (-6) :=
    essentially_distinct_card_bound hdelta hdelta_one hdelta_small hF_ball hF_distinct
  have hF_card_pos : 0 < F.card := hF_nonempty
  have hF_card_ne_zero : F.card ≠ 0 := hF_card_pos.ne'
  have h1 : (2 : ℕ) ^ Nat.log 2 F.card ≤ F.card := Nat.pow_log_le_self 2 hF_card_ne_zero
  have h1' : (2 : ℝ) ^ (Nat.log 2 F.card) ≤ (F.card : ℝ) := by exact_mod_cast h1
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h_nat_log_le : (Nat.log 2 F.card : ℝ) ≤ Real.log (F.card : ℝ) / Real.log 2 := by
    have h2 : Real.log ((2 : ℝ) ^ (Nat.log 2 F.card)) ≤ Real.log (F.card : ℝ) :=
      Real.log_le_log (by positivity) h1'
    have h3 : Real.log ((2 : ℝ) ^ (Nat.log 2 F.card)) =
        (Nat.log 2 F.card : ℝ) * Real.log 2 := by
      rw [Real.log_pow] <;> ring
    rw [h3] at h2
    have h4 : (Nat.log 2 F.card : ℝ) * Real.log 2 ≤ Real.log (F.card : ℝ) := h2
    calc
      (Nat.log 2 F.card : ℝ)
        = ((Nat.log 2 F.card : ℝ) * Real.log 2) / Real.log 2 := by field_simp [hlog2_pos.ne'] <;> ring
      _ ≤ Real.log (F.card : ℝ) / Real.log 2 := by gcongr
  have h_log_arg_pos : 0 < (35 : ℝ)^6 * Real.rpow delta (-6) := by
    have h_pos1 : 0 < (35 : ℝ)^6 := by positivity
    have h_pos2 : 0 < Real.rpow delta (-6) := Real.rpow_pos_of_pos hdelta _
    exact mul_pos h_pos1 h_pos2
  have h_log_card_le : Real.log (F.card : ℝ) ≤ Real.log ((35 : ℝ)^6 * Real.rpow delta (-6)) :=
    Real.log_le_log (by exact_mod_cast hF_card_pos) h_card_real
  set L : ℝ := Real.log ((35 : ℝ)^6 * Real.rpow delta (-6)) / Real.log 2 + 1 with hL_def
  have hL_nonneg : 0 ≤ L := by
    have h1 : Real.rpow delta (-6) ≥ 1 := by
      have h2 : Real.rpow delta 6 ≤ 1 := by
        apply Real.rpow_le_one hdelta.le hdelta_one
        <;> norm_num
      have h3 : 0 < Real.rpow delta 6 := Real.rpow_pos_of_pos hdelta 6
      have h4 : Real.rpow delta (-6) = (Real.rpow delta 6)⁻¹ := Real.rpow_neg hdelta.le 6
      rw [h4]
      have h5 : (Real.rpow delta 6)⁻¹ ≥ 1 := by
        have h51 : Real.rpow delta 6 ≤ 1 := h2
        have h52 : 0 < Real.rpow delta 6 := h3
        have h53 : (Real.rpow delta 6)⁻¹ ≥ 1 := by
          calc
            (Real.rpow delta 6)⁻¹ ≥ (1 : ℝ)⁻¹ := by gcongr
            _ = 1 := by simp
        exact h53
      exact h5
    have h6 : (35 : ℝ)^6 ≥ 1 := by norm_num
    have h7 : (35 : ℝ)^6 * Real.rpow delta (-6) ≥ 1 := by nlinarith
    have h8 : 0 ≤ Real.log ((35 : ℝ)^6 * Real.rpow delta (-6)) := Real.log_nonneg h7
    have h9 : 0 ≤ Real.log ((35 : ℝ)^6 * Real.rpow delta (-6)) / Real.log 2 := by
      apply div_nonneg h8 hlog2_pos.le
    linarith
  have h_div_log : Real.log (F.card : ℝ) / Real.log 2 ≤
      Real.log ((35 : ℝ)^6 * Real.rpow delta (-6)) / Real.log 2 := by
    gcongr
  have h_ineq : (Nat.log 2 F.card + 1 : ℝ) ≤ L := by
    dsimp only [L]
    have h7 : (Nat.log 2 F.card : ℝ) ≤ Real.log (F.card : ℝ) / Real.log 2 := h_nat_log_le
    linarith [h_div_log, h7]
  have h_pos_nat : 0 ≤ (Nat.log 2 F.card + 1 : ℝ) := by positivity
  have h_toNNReal : ((Nat.log 2 F.card + 1 : ℝ).toNNReal) = (Nat.log 2 F.card + 1 : NNReal) := by
    apply NNReal.coe_injective
    simp
  have h_coe : ENNReal.ofReal ((Nat.log 2 F.card + 1 : ℝ)) = (Nat.log 2 F.card + 1 : ENNReal) := by
    simpa using ENNReal.ofReal_natCast (Nat.log 2 F.card + 1)
  have h8 : (Nat.log 2 F.card + 1 : ENNReal) ≤ ENNReal.ofReal L := by
    have h_main : ENNReal.ofReal ((Nat.log 2 F.card + 1 : ℝ)) ≤ ENNReal.ofReal L := ENNReal.ofReal_mono h_ineq
    rw [h_coe] at h_main
    exact h_main
  have h9 : (2 : ENNReal) * (Nat.log 2 F.card + 1 : ENNReal) ≤
      (2 : ENNReal) * ENNReal.ofReal L := by gcongr
  have h10 : (2 : ENNReal) * ENNReal.ofReal L = ENNReal.ofReal (2 * L) := by
    have h101 : 0 ≤ (2 : ℝ) := by norm_num
    have h : ENNReal.ofReal (2 * L) = ENNReal.ofReal (2 : ℝ) * ENNReal.ofReal L :=
      ENNReal.ofReal_mul h101
    rw [h]
    have h2 : ENNReal.ofReal (2 : ℝ) = (2 : ENNReal) := by norm_cast
    rw [h2] <;> ring
  rw [h10] at h9
  have h11 : ENNReal.ofReal (2 * L) ≤ Kakeya.realRpowENN delta (eta - epsilon') := by
    dsimp only [Kakeya.realRpowENN]
    exact ENNReal.ofReal_mono h_log_bound
  exact h9.trans h11

/--
Sub-lemma: for any `a < 0` and `C > 1`, there exists `0 < δ₀ ≤ 1` such that
for all `0 < δ ≤ δ₀`, `δ^a ≥ C`.
-/
lemma exists_delta_rpow_ge (a C : ℝ) (ha : a < 0) (hC : 1 < C) :
    ∃ (δ₀ : ℝ), 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ (δ : ℝ), 0 < δ → δ ≤ δ₀ → Real.rpow δ a ≥ C := by
  let b : ℝ := -a
  have hb_pos : 0 < b := by linarith
  have hC_pos : 0 < C := by linarith
  let δ₀ : ℝ := C ^ (-1 / b)
  have hδ₀_pos : 0 < δ₀ := Real.rpow_pos_of_pos hC_pos _
  have h_pos_inv : 0 < 1 / b := by positivity
  have h2 : 1 < C ^ (1 / b) := Real.one_lt_rpow hC h_pos_inv
  have h_neg_eq : -1 / b = -(1 / b) := by ring
  have h3 : C ^ (-1 / b) = (C ^ (1 / b))⁻¹ := by
    rw [h_neg_eq]
    exact Real.rpow_neg hC_pos.le (1 / b)
  have hδ₀_lt_one : δ₀ < 1 := by
    dsimp only [δ₀]
    rw [h3]
    have h_pos2 : 0 < C ^ (1 / b) := Real.rpow_pos_of_pos hC_pos _
    have h4 : (C ^ (1 / b))⁻¹ < 1 := by
      have h5 : 1 ≤ C ^ (1 / b) := h2.le
      have h6 : (C ^ (1 / b))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h5
      have h7 : (C ^ (1 / b))⁻¹ ≠ 1 := by
        intro h8
        have h9 : C ^ (1 / b) = 1 := by
          field_simp [h_pos2.ne'] at h8 <;> linarith
        linarith [h2]
      exact lt_of_le_of_ne h6 h7
    exact h4
  have hδ₀_le_one : δ₀ ≤ 1 := hδ₀_lt_one.le
  have h4 : Real.rpow δ₀ b = C⁻¹ := by
    have h51 : δ₀ = C ^ (-1 / b) := by rfl
    rw [h51]
    have h52 : Real.rpow (C ^ (-1 / b)) b = C ^ ((-1 / b) * b) :=
      (Real.rpow_mul hC_pos.le (-1 / b) b).symm
    rw [h52]
    have h53 : (-1 / b) * b = -1 := by
      field_simp [hb_pos.ne'] <;> ring
    rw [h53]
    have h54 : C ^ (-1 : ℝ) = C⁻¹ := by
      have h55 : C ^ (-1 : ℝ) = (C ^ (1 : ℝ))⁻¹ := Real.rpow_neg hC_pos.le 1
      rw [h55]
      have h56 : C ^ (1 : ℝ) = C := by simp
      rw [h56] <;> ring
    rw [h54]
  refine' ⟨δ₀, hδ₀_pos, hδ₀_le_one, _⟩
  intro δ hδ_pos hδ_le
  have h5 : Real.rpow δ b ≤ Real.rpow δ₀ b :=
    Real.rpow_le_rpow hδ_pos.le hδ_le hb_pos.le
  have h6 : Real.rpow δ b ≤ C⁻¹ := by
    rw [h4] at h5
    exact h5
  have h7 : 0 < Real.rpow δ b := Real.rpow_pos_of_pos hδ_pos b
  have h8 : (Real.rpow δ b)⁻¹ ≥ C := by
    have h9 : (Real.rpow δ b)⁻¹ ≥ (C⁻¹)⁻¹ := by gcongr
    have h10 : (C⁻¹)⁻¹ = C := by simp
    rw [h10] at h9
    exact h9
  have h11 : a = -b := by linarith
  have h12 : Real.rpow δ a = (Real.rpow δ b)⁻¹ := by
    rw [h11]
    exact Real.rpow_neg hδ_pos.le b
  rw [h12]
  exact h8

/--
Sub-lemma: mass inequality for fine_multiplicity_refinement.

`δ^(2η) ≥ 4 * δ^(ε' - η)`.
Since `3η < ε'`, we have `2η - (ε'-η) = 3η-ε' < 0`.
For small enough δ, `δ^(3η-ε') ≥ 4`.
-/
lemma mass_inequality_from_extremal
    {delta eta epsilon' : ℝ}
    (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    (heta : 0 < eta) (heta_3le : 3 * eta < epsilon')
    (hbound : Real.rpow delta (3 * eta - epsilon') ≥ 4) :
    Kakeya.realRpowENN delta (2 * eta) ≥
      4 * Kakeya.realRpowENN delta (epsilon' - eta) := by
  have h1 : 0 < epsilon' - eta := by linarith
  have h_pos1 : 0 < Real.rpow delta (epsilon' - eta) := Real.rpow_pos_of_pos hdelta _
  have h_main_real : Real.rpow delta (2 * eta) ≥ 4 * Real.rpow delta (epsilon' - eta) := by
    have h_sum : (3 * eta - epsilon') + (epsilon' - eta) = 2 * eta := by ring
    have h2 : Real.rpow delta (2 * eta) =
        Real.rpow delta (3 * eta - epsilon') * Real.rpow delta (epsilon' - eta) := by
      have h3 : Real.rpow delta ((3 * eta - epsilon') + (epsilon' - eta)) =
          Real.rpow delta (3 * eta - epsilon') * Real.rpow delta (epsilon' - eta) :=
        Real.rpow_add hdelta (3 * eta - epsilon') (epsilon' - eta)
      have h4 : (3 * eta - epsilon') + (epsilon' - eta) = 2 * eta := by ring
      rw [h4] at h3
      exact h3
    rw [h2]
    have h4 : Real.rpow delta (3 * eta - epsilon') ≥ 4 := hbound
    have h5 : Real.rpow delta (3 * eta - epsilon') * Real.rpow delta (epsilon' - eta) ≥
        4 * Real.rpow delta (epsilon' - eta) := by
      gcongr <;> linarith
    exact h5
  have h6 : 0 ≤ Real.rpow delta (epsilon' - eta) := by positivity
  have h7 : ENNReal.ofReal (Real.rpow delta (2 * eta)) ≥
      ENNReal.ofReal (4 * Real.rpow delta (epsilon' - eta)) := by
    exact ENNReal.ofReal_mono h_main_real
  have h8 : ENNReal.ofReal (4 * Real.rpow delta (epsilon' - eta)) =
      (4 : ENNReal) * ENNReal.ofReal (Real.rpow delta (epsilon' - eta)) := by
    have h9 : 0 ≤ Real.rpow delta (epsilon' - eta) := by positivity
    have h10 : ENNReal.ofReal (4 * Real.rpow delta (epsilon' - eta)) =
        ENNReal.ofReal 4 * ENNReal.ofReal (Real.rpow delta (epsilon' - eta)) := by
      have h101 : 0 ≤ (4 : ℝ) := by norm_num
      exact ENNReal.ofReal_mul h101
    rw [h10]
    have h11 : ENNReal.ofReal 4 = (4 : ENNReal) := by norm_cast
    rw [h11] <;> rfl
  rw [h8] at h7
  simpa [Kakeya.realRpowENN] using h7

/--
Parameter preparation + refined extremality in one unified lemma.

Given the global critical floor and target epsilon, choose eta, delta₀,
and for any extremal pair produce:
- The hypotheses needed by fine_multiplicity_refinement (with target ε')
- The proof that refined is extremal at parameter ε
-/
lemma parameter_and_extremal
    {sigma epsilon : ℝ}
    (hsigma_pos : 0 < sigma)
    (hsigma_lt_one : sigma < 1)
    (hepsilon_pos : 0 < epsilon)
    (hCriticalFloor : HasCriticalVolumeFloor sigma) :
    ∃ (eta delta₀ eta_floor epsilon' delta₀_floor : ℝ)
      (hfloor : ∀ (delta : ℝ), 0 < delta → delta ≤ delta₀_floor →
        ∀ (F : Kakeya.Streamlined.TubeFamily delta),
          F.Nonempty → F.IsInUnitBall → F.IsEssentiallyDistinct →
          ∀ (U : Kakeya.Streamlined.UniformTubeStructure F),
            U.uniformity ≤ Kakeya.realRpowENN delta (-eta_floor) →
            U.IsFrostmanAtEveryScale (Kakeya.realRpowENN delta (-eta_floor)) →
            ∀ (Y : Kakeya.Streamlined.TubeShading F),
              Y.IsLambdaDense (Kakeya.realRpowENN delta eta_floor) →
                Kakeya.realRpowENN delta (sigma + epsilon) ≤ volume Y.union),
      0 < eta ∧ 0 < epsilon' ∧ epsilon' ≤ epsilon ∧ epsilon' ≤ eta_floor ∧
      3 * eta < epsilon' ∧
      0 < delta₀ ∧ delta₀ ≤ 1 ∧ delta₀ ≤ delta₀_floor ∧
      0 < eta_floor ∧ 0 < delta₀_floor ∧ delta₀_floor ≤ 1 ∧
      ∀ (delta : ℝ) (F : Kakeya.Streamlined.TubeFamily delta)
        (U : Kakeya.Streamlined.UniformTubeStructure F)
        (Y : Kakeya.Streamlined.TubeShading F),
        0 < delta → delta ≤ delta₀ →
        IsExtremalPair sigma eta F U Y →
        (2 * (Nat.log 2 F.card + 1 : ENNReal) ≤
            Kakeya.realRpowENN delta (eta - epsilon')) ∧
        (Kakeya.realRpowENN delta (2 * eta) ≥
            4 * Kakeya.realRpowENN delta (epsilon' - eta)) ∧
        ∀ (refined : Kakeya.Streamlined.TubeShading F),
          IsSubshading refined Y →
          refined.mass ≥ Kakeya.realRpowENN delta epsilon' * F.toBodyFamily.mass →
          IsExtremalPair sigma epsilon F U refined := by
  -- Step 1: Apply critical volume floor with loss = epsilon
  rcases hCriticalFloor epsilon hepsilon_pos with
    ⟨eta_floor, delta₀_floor, heta_floor_pos, hdelta₀_floor_pos, hdelta₀_floor_le_one, hfloor⟩
  -- Step 2: Define epsilon' = min(eta_floor, epsilon)
  let epsilon' : ℝ := min eta_floor epsilon
  have hepsilon'_pos : 0 < epsilon' := by positivity
  have hepsilon'_le_epsilon : epsilon' ≤ epsilon := min_le_right _ _
  have hepsilon'_le_eta_floor : epsilon' ≤ eta_floor := min_le_left _ _
  -- Step 3: Choose eta = epsilon' / 4
  let eta : ℝ := epsilon' / 4
  have heta_pos : 0 < eta := by positivity
  have h3eta_lt : 3 * eta < epsilon' := by
    dsimp only [eta] <;> linarith
  -- Step 4: Choose delta₀ small enough for all bounds
  -- 4a: Mass inequality
  rcases exists_delta_rpow_ge (3 * eta - epsilon') 4 (by linarith) (by norm_num) with
    ⟨δ₀_mass, hδ₀_mass_pos, hδ₀_mass_le_one, hmass_bound⟩
  -- 4b: Logarithmic bound
  let b : ℝ := epsilon' - eta
  have hb_pos : 0 < b := by linarith
  let C1 : ℝ := 12 * Real.log 35 / Real.log 2 + 2
  let C2 : ℝ := 12 / Real.log 2
  have hC1_nonneg : 0 ≤ C1 := by positivity
  have hC2_nonneg : 0 ≤ C2 := by positivity
  rcases log_poly_bound hC1_nonneg hC2_nonneg hb_pos with
    ⟨δ₀_log, hδ₀_log_pos, hδ₀_log_le_one, hlog_bound⟩
  -- 4c: delta < 1/16 for cardinality bound
  let δ₀_small : ℝ := 1 / 17
  have hδ₀_small_pos : 0 < δ₀_small := by norm_num
  have hδ₀_small_le_one : δ₀_small ≤ 1 := by norm_num
  -- Combine: delta₀ = min of floor, mass, log, small
  let delta₀ : ℝ := min (min delta₀_floor δ₀_mass) (min δ₀_log δ₀_small)
  have hdelta₀_pos : 0 < delta₀ := by positivity
  have hdelta₀_le_one : delta₀ ≤ 1 := by
    have h1 : delta₀ ≤ δ₀_small := by
      exact le_trans (min_le_right _ _) (min_le_right _ _)
    exact h1.trans hδ₀_small_le_one
  have hdelta₀_le_floor : delta₀ ≤ delta₀_floor := by
    exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hdelta₀_le_mass : delta₀ ≤ δ₀_mass := by
    exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hdelta₀_le_log : delta₀ ≤ δ₀_log := by
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hdelta₀_le_small : delta₀ ≤ δ₀_small := by
    exact le_trans (min_le_right _ _) (min_le_right _ _)
  refine' ⟨eta, delta₀, eta_floor, epsilon', delta₀_floor, hfloor,
    heta_pos, hepsilon'_pos, hepsilon'_le_epsilon, hepsilon'_le_eta_floor,
    h3eta_lt, hdelta₀_pos, hdelta₀_le_one, hdelta₀_le_floor,
    heta_floor_pos, hdelta₀_floor_pos, hdelta₀_floor_le_one, _⟩
  intro delta F U Y hdelta_pos hdelta_le_delta0 hExt
  have hdelta_one : delta ≤ 1 := hdelta_le_delta0.trans hdelta₀_le_one
  have hdelta_le_floor : delta ≤ delta₀_floor :=
    hdelta_le_delta0.trans hdelta₀_le_floor
  have hdelta_le_mass : delta ≤ δ₀_mass :=
    hdelta_le_delta0.trans hdelta₀_le_mass
  have hdelta_le_log : delta ≤ δ₀_log :=
    hdelta_le_delta0.trans hdelta₀_le_log
  have hdelta_small : delta < 1 / 16 := by
    have h1 : delta ≤ δ₀_small := hdelta_le_delta0.trans hdelta₀_le_small
    have h2 : δ₀_small = 1 / 17 := by rfl
    rw [h2] at h1
    have h3 : delta ≤ 1 / 17 := h1
    have h4 : (1 / 17 : ℝ) < 1 / 16 := by norm_num
    exact h3.trans_lt h4
  -- Log bound: C1 + C2 * log(1/delta) ≤ Real.rpow delta (-b)
  have h_log_bound_real : C1 + C2 * Real.log (1 / delta) ≤ Real.rpow delta (-b) :=
    hlog_bound delta hdelta_pos hdelta_le_log
  -- Convert to the form needed by cardinality_bound
  have h_log_bound' : 2 * (Real.log ((35 : ℝ)^6 * Real.rpow delta (-6)) / Real.log 2 + 1) ≤
      Real.rpow delta (eta - epsilon') := by
    have h_exp : eta - epsilon' = -b := by linarith
    rw [h_exp]
    have h_eq : 2 * (Real.log ((35 : ℝ)^6 * Real.rpow delta (-6)) / Real.log 2 + 1) =
        C1 + C2 * Real.log (1 / delta) := by
      have h3 : Real.log ((35 : ℝ)^6 * Real.rpow delta (-6)) =
          6 * Real.log 35 + 6 * Real.log (1 / delta) := by
        have h4 : Real.log ((35 : ℝ)^6 * Real.rpow delta (-6)) =
            Real.log ((35 : ℝ)^6) + Real.log (Real.rpow delta (-6)) := by
          have h_pos1 : 0 < (35 : ℝ)^6 := by positivity
          have h_pos2 : 0 < Real.rpow delta (-6) := Real.rpow_pos_of_pos hdelta_pos (y := (-6 : ℝ))
          exact Real.log_mul (ne_of_gt h_pos1) (ne_of_gt h_pos2)
        rw [h4]
        have h5 : Real.log ((35 : ℝ)^6) = 6 * Real.log 35 := by
          have h51 : Real.log ((35 : ℝ)^6) = (6 : ℝ) * Real.log 35 := Real.log_pow (35 : ℝ) 6
          rw [h51] <;> ring
        have h6 : Real.log (delta ^ (-6 : ℝ)) = 6 * Real.log (1 / delta) := by
          have h7 : Real.log (delta ^ (-6 : ℝ)) = (-6 : ℝ) * Real.log delta := by
            have h : ∀ (y : ℝ), Real.log (delta ^ y) = y * Real.log delta := Real.log_rpow hdelta_pos
            exact h (-6 : ℝ)
          rw [h7]
          have h8 : -6 * Real.log delta = 6 * Real.log (1 / delta) := by
            have h9 : Real.log (1 / delta) = -Real.log delta := by
              rw [Real.log_div (by positivity) (by positivity)] <;> simp
            rw [h9] <;> ring
          exact h8
        have h10 : Real.log (Real.rpow delta (-6)) = 6 * Real.log (1 / delta) := by
          simpa [Real.rpow_neg] using h6
        rw [h5, h10] <;> ring
      rw [h3]
      dsimp only [C1, C2]
      <;> ring
    rw [h_eq]
    exact h_log_bound_real
  constructor
  · -- Cardinality bound
    exact cardinality_bound_from_extremal hdelta_pos hdelta_one hdelta_small
      hExt h3eta_lt h_log_bound'
  constructor
  · -- Mass inequality
    exact mass_inequality_from_extremal hdelta_pos hdelta_one heta_pos h3eta_lt
      (hmass_bound delta hdelta_pos hdelta_le_mass)
  · -- Refined extremality
    intro refined hsub hmass
    rcases hExt with ⟨_, _, hF_nonempty, hF_ball, hF_distinct,
        hU_uniform, hU_frostman, hY_dense, hY_vol_upper, hY_vol_lower⟩
    -- Uniformity: weaken from eta to epsilon
    have h_uniform_power : Kakeya.realRpowENN delta (-eta) ≤ Kakeya.realRpowENN delta (-epsilon) := by
      apply ENNReal.ofReal_mono
      apply Real.rpow_le_rpow_of_exponent_ge hdelta_pos hdelta_one
      <;> linarith
    have hU_uniform' : U.uniformity ≤ Kakeya.realRpowENN delta (-epsilon) :=
      hU_uniform.trans h_uniform_power
    -- Frostman: weaken from eta to epsilon
    have hU_frostman' : U.IsFrostmanAtEveryScale (Kakeya.realRpowENN delta (-epsilon)) := by
      intro rho j K hK_convex hK_subset
      have h_old := hU_frostman rho j K hK_convex hK_subset
      exact h_old.trans (by gcongr)
    -- Lambda density at epsilon: mass ≥ δ^epsilon' * F.mass ≥ δ^epsilon * F.mass
    have h_density_power : Kakeya.realRpowENN delta epsilon ≤ Kakeya.realRpowENN delta epsilon' := by
      apply ENNReal.ofReal_mono
      exact Real.rpow_le_rpow_of_exponent_ge hdelta_pos hdelta_one hepsilon'_le_epsilon
    have hY_dense' : refined.IsLambdaDense (Kakeya.realRpowENN delta epsilon) := by
      have h1 : Kakeya.realRpowENN delta epsilon * F.toBodyFamily.mass ≤
          Kakeya.realRpowENN delta epsilon' * F.toBodyFamily.mass := by gcongr
      exact h1.trans hmass
    -- Volume upper bound: refined ⊆ Y, volume(Y) ≤ δ^(σ-eta) ≤ δ^(σ-epsilon)
    have h_vol_upper_power : Kakeya.realRpowENN delta (sigma - eta) ≤
        Kakeya.realRpowENN delta (sigma - epsilon) := by
      apply ENNReal.ofReal_mono
      apply Real.rpow_le_rpow_of_exponent_ge hdelta_pos hdelta_one
      <;> linarith
    have h_vol_upper : volume refined.union ≤ Kakeya.realRpowENN delta (sigma - epsilon) := by
      have h1 : volume refined.union ≤ volume Y.union := measure_mono hsub.union_subset
      exact h1.trans (hY_vol_upper.trans h_vol_upper_power)
    -- Volume lower bound: apply HasCriticalVolumeFloor to refined
    have h_uniform_floor : U.uniformity ≤ Kakeya.realRpowENN delta (-eta_floor) := by
      have h1 : Kakeya.realRpowENN delta (-eta) ≤ Kakeya.realRpowENN delta (-eta_floor) := by
        apply ENNReal.ofReal_mono
        apply Real.rpow_le_rpow_of_exponent_ge hdelta_pos hdelta_one
        <;> linarith [hepsilon'_le_eta_floor]
      exact hU_uniform.trans h1
    have h_frostman_floor : U.IsFrostmanAtEveryScale (Kakeya.realRpowENN delta (-eta_floor)) := by
      intro rho j K hK_convex hK_subset
      have h_old := hU_frostman rho j K hK_convex hK_subset
      have h2 : Kakeya.realRpowENN delta (-eta) ≤ Kakeya.realRpowENN delta (-eta_floor) := by
        apply ENNReal.ofReal_mono
        apply Real.rpow_le_rpow_of_exponent_ge hdelta_pos hdelta_one
        <;> linarith [hepsilon'_le_eta_floor]
      exact h_old.trans (by gcongr)
    have h_density_floor : refined.IsLambdaDense (Kakeya.realRpowENN delta eta_floor) := by
      have h1 : Kakeya.realRpowENN delta eta_floor ≤ Kakeya.realRpowENN delta epsilon' := by
        apply ENNReal.ofReal_mono
        exact Real.rpow_le_rpow_of_exponent_ge hdelta_pos hdelta_one hepsilon'_le_eta_floor
      have h2 : Kakeya.realRpowENN delta eta_floor * F.toBodyFamily.mass ≤
          Kakeya.realRpowENN delta epsilon' * F.toBodyFamily.mass := by gcongr
      exact h2.trans hmass
    have h_vol_lower : Kakeya.realRpowENN delta (sigma + epsilon) ≤ volume refined.union :=
      hfloor delta hdelta_pos hdelta_le_floor F hF_nonempty hF_ball hF_distinct U
        h_uniform_floor h_frostman_floor refined h_density_floor
    exact ⟨hdelta_pos, hdelta_one, hF_nonempty, hF_ball, hF_distinct,
      hU_uniform', hU_frostman', hY_dense', h_vol_upper, h_vol_lower⟩

end Kakeya.Assouad
