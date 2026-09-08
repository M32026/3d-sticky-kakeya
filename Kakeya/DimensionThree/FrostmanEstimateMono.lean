/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Asymptotics
public import Kakeya.PartialEstimates

/-!
# Monotonicity of `K_F` in the exponent

`Kakeya.FrostmanEstimate.mono`: `K_F(β)` implies `K_F(β')` for `β ≤ β'`, in dimension three.

Unlike `Kakeya.KatzTaoEstimate.mono`, the exponent occurs twice in the conclusion of
`Kakeya.FrostmanEstimate`, so the two occurrences have to be traded against each other. That
trade-off is isolated in the real-number lemma `monoAlgebra` and its `ℝ≥0∞` transport
`monoAlgebraENN`, which is the single place where the two number systems meet. Both, together
with the size bound `kfSizeUpper_of_card` they consume, are private to this file: they carry
no content beyond what `Kakeya.FrostmanEstimate.mono` needs.
-/

@[expose] public section

open MeasureTheory Topology ConvexSpaceBody Filter ShadedBody

namespace Kakeya

universe v

variable
  (E : Type*)
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The algebraic step behind `FrostmanEstimate.mono`.

Raising the exponent from `β` to `β'` gains the factor `δ ^ (-2 * (β' - β))` and loses the
factor `P ^ (-(β' - β) / 2)`, so after cancelling
`δ ^ (-ε / 2) * δ ^ (-2 * β) * P ^ (1 - β' / 2)` the claim reduces to
`P ^ κ ≤ δ ^ (-ε / 2) * δ ^ (-4 * κ)` with `κ = (β' - β) / 2 ≥ 0`. The upper bound
`P ≤ C * δ ^ (-4)` accounts for the factor `δ ^ (-4 * κ)`, and the constant is paid for out
of the available `δ ^ (-ε / 2)` slack, which is what the hypothesis
`C ^ κ ≤ δ ^ (-ε / 2)` records; it holds for all `δ` below a threshold depending on
`C`, `ε`, `β` and `β'` only.

Stated for real numbers: all factors are finite and strictly positive, so the inequality can
be proved by cancellation. -/
private lemma monoAlgebra {δ ε β β' C P : ℝ} (hδ_pos : 0 < δ) (hββ' : β ≤ β') (hC_pos : 0 < C)
    (hC_le : C ^ ((β' - β) / 2) ≤ δ ^ (-ε / 2))
    (hP_pos : 0 < P) (hP_le : P ≤ C * δ ^ (-4 : ℝ)) :
    δ ^ (-ε / 2) * δ ^ (-2 * β) * P ^ (1 - β / 2) ≤
      δ ^ (-ε) * δ ^ (-2 * β') * P ^ (1 - β' / 2) := by
  set κ := (β' - β) / 2 with hκ_def
  have hκ_nonneg : 0 ≤ κ := by nlinarith
  have hδ_nonneg : 0 ≤ δ := le_of_lt hδ_pos
  have hP_κ : P ^ κ ≤ δ ^ (-ε / 2) * δ ^ (-4 * κ) := by
    calc
      P ^ κ ≤ (C * δ ^ (-4 : ℝ)) ^ κ :=
        Real.rpow_le_rpow (le_of_lt hP_pos) hP_le hκ_nonneg
      _ = C ^ κ * (δ ^ (-4 : ℝ)) ^ κ := by
        rw [Real.mul_rpow (le_of_lt hC_pos) (by positivity : 0 ≤ δ ^ (-4 : ℝ))]
      _ = C ^ κ * δ ^ ((-4 : ℝ) * κ) := by
        rw [Real.rpow_mul (le_of_lt hδ_pos) (-4 : ℝ) κ]
      _ = C ^ κ * δ ^ (-4 * κ) := by ring
      _ ≤ δ ^ (-ε / 2) * δ ^ (-4 * κ) := by
        have hC_κ : C ^ κ ≤ δ ^ (-ε / 2) := by
          dsimp [κ]; exact hC_le
        have h_nonneg : 0 ≤ δ ^ (-4 * κ) := by positivity
        exact mul_le_mul_of_nonneg_right hC_κ h_nonneg
  calc
    δ ^ (-ε / 2) * δ ^ (-2 * β) * P ^ (1 - β / 2)
        = δ ^ (-ε / 2) * δ ^ (-2 * β) * (P ^ (1 - β' / 2) * P ^ κ) := by
          rw [show P ^ (1 - β / 2) = P ^ (1 - β' / 2) * P ^ κ by
            calc
              P ^ (1 - β / 2) = P ^ ((1 - β' / 2) + κ) := by
                congr 1
                nlinarith
              _ = P ^ (1 - β' / 2) * P ^ κ := Real.rpow_add hP_pos (1 - β' / 2) κ
          ]
    _ = (δ ^ (-ε / 2) * δ ^ (-2 * β) * P ^ (1 - β' / 2)) * P ^ κ := by ring
    _ ≤ (δ ^ (-ε / 2) * δ ^ (-2 * β) * P ^ (1 - β' / 2)) * (δ ^ (-ε / 2) * δ ^ (-4 * κ)) := by
      have h_nonneg : 0 ≤ δ ^ (-ε / 2) * δ ^ (-2 * β) * P ^ (1 - β' / 2) := by positivity
      exact mul_le_mul_of_nonneg_left hP_κ h_nonneg
    _ = δ ^ (-ε) * δ ^ (-2 * β') * P ^ (1 - β' / 2) := by
      calc
        (δ ^ (-ε / 2) * δ ^ (-2 * β) * P ^ (1 - β' / 2)) * (δ ^ (-ε / 2) * δ ^ (-4 * κ))
            = (δ ^ (-ε / 2) * δ ^ (-ε / 2)) * (δ ^ (-2 * β) * δ ^ (-4 * κ)) *
                P ^ (1 - β' / 2) := by ring
        _ = δ ^ ((-ε / 2) + (-ε / 2)) * (δ ^ (-2 * β) * δ ^ (-4 * κ)) * P ^ (1 - β' / 2) := by
          rw [Real.rpow_add hδ_pos (-ε / 2) (-ε / 2)]
        _ = δ ^ (-ε) * (δ ^ (-2 * β) * δ ^ (-4 * κ)) * P ^ (1 - β' / 2) := by
          ring_nf
        _ = δ ^ (-ε) * δ ^ ((-2 * β) + (-4 * κ)) * P ^ (1 - β' / 2) := by
          rw [Real.rpow_add hδ_pos (-2 * β) (-4 * κ)]
        _ = δ ^ (-ε) * δ ^ (-2 * β - 4 * κ) * P ^ (1 - β' / 2) := by
          ring_nf
        _ = δ ^ (-ε) * δ ^ (-2 * β') * P ^ (1 - β' / 2) := by
          have h_exp : -2 * β - 4 * κ = -2 * β' := by
            dsimp [κ]
            ring
          rw [h_exp]

/-- `monoAlgebra` transported to `ℝ≥0∞`.

`FrostmanEstimate` is an inequality between `ℝ≥0∞`-valued quantities, while the exponent
trade-off is a statement about real numbers. This lemma is the single point where the two
meet, so that `FrostmanEstimate.mono` can be assembled without leaving `ℝ≥0∞`. All the
finiteness hypotheses are what makes the transport along `ENNReal.toReal` reversible. -/
private lemma monoAlgebraENN {δ : NNReal} {ε β β' : ℝ} {C P : ENNReal} (hδ_pos : 0 < δ)
    (hββ' : β ≤ β') (hC_pos : 0 < C) (hC_ne_top : C ≠ ⊤)
    (hC_le : C ^ ((β' - β) / 2) ≤ (δ : ENNReal) ^ (-ε / 2))
    (hP_pos : 0 < P) (hP_ne_top : P ≠ ⊤) (hP_le : P ≤ C * (δ : ENNReal) ^ (-4 : ℝ)) :
    (δ : ENNReal) ^ (-ε / 2) * (δ : ENNReal) ^ (-2 * β) * P ^ (1 - β / 2) ≤
      (δ : ENNReal) ^ (-ε) * (δ : ENNReal) ^ (-2 * β') * P ^ (1 - β' / 2) := by
  -- All factors are finite and nonzero
  have hδ_ne_zero : (δ : ENNReal) ≠ 0 := by exact_mod_cast hδ_pos.ne'
  have hδ_ne_top : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hP_ne_zero : P ≠ 0 := hP_pos.ne'
  have hC_ne_zero : C ≠ 0 := hC_pos.ne'
  have hδ_real_pos : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ_pos
  have hC_real_pos : (0 : ℝ) < C.toReal := ENNReal.toReal_pos hC_ne_zero hC_ne_top
  have hP_real_pos : (0 : ℝ) < P.toReal := ENNReal.toReal_pos hP_ne_zero hP_ne_top
  -- Each factor in the goal is ≠ ⊤
  have h_fin_lhs : (δ : ENNReal) ^ (-ε / 2) * (δ : ENNReal) ^ (-2 * β) * P ^ (1 - β / 2) ≠ ⊤ := by
    refine ENNReal.mul_ne_top ?_ ?_
    · refine ENNReal.mul_ne_top ?_ ?_
      · exact ENNReal.rpow_ne_top_of_ne_zero (y := (-ε / 2)) hδ_ne_zero hδ_ne_top
      · exact ENNReal.rpow_ne_top_of_ne_zero (y := (-2 * β)) hδ_ne_zero hδ_ne_top
    · exact ENNReal.rpow_ne_top_of_ne_zero (y := (1 - β / 2)) hP_ne_zero hP_ne_top
  have h_fin_rhs : (δ : ENNReal) ^ (-ε) * (δ : ENNReal) ^ (-2 * β') * P ^ (1 - β' / 2) ≠ ⊤ := by
    refine ENNReal.mul_ne_top ?_ ?_
    · refine ENNReal.mul_ne_top ?_ ?_
      · exact ENNReal.rpow_ne_top_of_ne_zero (y := (-ε)) hδ_ne_zero hδ_ne_top
      · exact ENNReal.rpow_ne_top_of_ne_zero (y := (-2 * β')) hδ_ne_zero hδ_ne_top
    · exact ENNReal.rpow_ne_top_of_ne_zero (y := (1 - β' / 2)) hP_ne_zero hP_ne_top
  -- Transport hypotheses to ℝ
  have hC_real_le : C.toReal ^ ((β' - β) / 2) ≤ (δ : ℝ) ^ (-ε / 2) := by
    have hCpow_ne_top : C ^ ((β' - β) / 2) ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_ne_zero (y := ((β' - β) / 2)) hC_ne_zero hC_ne_top
    have hδpow_ne_top : (δ : ENNReal) ^ (-ε / 2) ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_ne_zero (y := (-ε / 2)) hδ_ne_zero hδ_ne_top
    have h := (ENNReal.toReal_le_toReal hCpow_ne_top hδpow_ne_top).mpr hC_le
    calc
      C.toReal ^ ((β' - β) / 2) = (C ^ ((β' - β) / 2)).toReal := by
        rw [ENNReal.toReal_rpow]
      _ ≤ ((δ : ENNReal) ^ (-ε / 2)).toReal := h
      _ = (δ : ℝ) ^ (-ε / 2) := by
        rw [← ENNReal.toReal_rpow, ENNReal.coe_toReal]
  have hP_real_le : P.toReal ≤ C.toReal * (δ : ℝ) ^ (-4 : ℝ) := by
    have h_mul_ne_top : C * (δ : ENNReal) ^ (-4 : ℝ) ≠ ⊤ :=
      ENNReal.mul_ne_top hC_ne_top
        (ENNReal.rpow_ne_top_of_ne_zero (y := (-4 : ℝ)) hδ_ne_zero hδ_ne_top)
    have h := (ENNReal.toReal_le_toReal hP_ne_top h_mul_ne_top).mpr hP_le
    calc
      P.toReal ≤ (C * (δ : ENNReal) ^ (-4 : ℝ)).toReal := h
      _ = C.toReal * ((δ : ENNReal) ^ (-4 : ℝ)).toReal := by rw [ENNReal.toReal_mul]
      _ = C.toReal * ((δ : ENNReal).toReal ^ (-4 : ℝ)) := by rw [ENNReal.toReal_rpow]
      _ = C.toReal * (δ : ℝ) ^ (-4 : ℝ) := by rw [ENNReal.coe_toReal]
  -- Apply monoAlgebra on ℝ
  have h_real := monoAlgebra hδ_real_pos hββ' hC_real_pos hC_real_le hP_real_pos hP_real_le
  -- Transport back to ENNReal
  refine (ENNReal.toReal_le_toReal h_fin_lhs h_fin_rhs).mp ?_
  calc
    ((δ : ENNReal) ^ (-ε / 2) * (δ : ENNReal) ^ (-2 * β) * P ^ (1 - β / 2)).toReal
        = ((δ : ENNReal) ^ (-ε / 2) * (δ : ENNReal) ^ (-2 * β)).toReal *
            (P ^ (1 - β / 2)).toReal := by
      rw [ENNReal.toReal_mul]
    _ = ((δ : ENNReal) ^ (-ε / 2)).toReal * ((δ : ENNReal) ^ (-2 * β)).toReal *
        (P ^ (1 - β / 2)).toReal := by
      rw [ENNReal.toReal_mul]
    _ = ((δ : ENNReal).toReal ^ (-ε / 2)) * ((δ : ENNReal).toReal ^ (-2 * β)) *
        (P.toReal ^ (1 - β / 2)) := by
      rw [ENNReal.toReal_rpow, ENNReal.toReal_rpow, ENNReal.toReal_rpow]
    _ = (δ : ℝ) ^ (-ε / 2) * (δ : ℝ) ^ (-2 * β) * P.toReal ^ (1 - β / 2) := by
      simp [ENNReal.coe_toReal]
    _ ≤ (δ : ℝ) ^ (-ε) * (δ : ℝ) ^ (-2 * β') * P.toReal ^ (1 - β' / 2) := h_real
    _ = (δ : ℝ) ^ (-ε) * (δ : ℝ) ^ (-2 * β') * P.toReal ^ (1 - β' / 2) := rfl
    _ = ((δ : ENNReal).toReal ^ (-ε)) * ((δ : ENNReal).toReal ^ (-2 * β')) *
        (P.toReal ^ (1 - β' / 2)) := by
      simp [ENNReal.coe_toReal]
    _ = ((δ : ENNReal) ^ (-ε)).toReal * ((δ : ENNReal) ^ (-2 * β')).toReal *
        (P ^ (1 - β' / 2)).toReal := by
      rw [ENNReal.toReal_rpow, ENNReal.toReal_rpow, ENNReal.toReal_rpow]
    _ = ((δ : ENNReal) ^ (-ε) * (δ : ENNReal) ^ (-2 * β')).toReal * (P ^ (1 - β' / 2)).toReal := by
      rw [ENNReal.toReal_mul]
    _ = ((δ : ENNReal) ^ (-ε) * (δ : ENNReal) ^ (-2 * β') * P ^ (1 - β' / 2)).toReal := by
      rw [← ENNReal.toReal_mul]

section
variable {E}

/-- Upper bound for `P = s.card * δ ^ (n - 1)` from the crude packing bound
`Tube.card_le_of_EssDistinct`, in the form `P ≤ C * δ ^ (-4)` required by `monoAlgebraENN`.

For pairwise essentially distinct `δ`-tubes in `B₁ ⊆ E` the crude count gives
`s.card ≤ C n * δ ^ (-2 * n)`, hence `P ≤ C n * δ ^ (-(n + 1))`, and `n + 1 ≤ 4` exactly when
`n ≤ 3`; this is where the hypothesis `finrank ℝ E = 3` enters `FrostmanEstimate.mono`. No
smallness of `δ` is needed: the packing bound already carries the whole `δ`-dependence.

Both sides are finite, so the inequality is stated in `ℝ≥0` and proved by transporting the
crude count along `NNReal.coe`; `FrostmanEstimate.mono` coerces it to `ℝ≥0∞` at the one
point where it is used. -/
private lemma kfSizeUpper_of_card {δ : NNReal} (hδ_pos : 0 < δ)
    (hE : Module.finrank ℝ E = 3) {ι : Type*} (s : Finset ι) (T : ι → Tube δ E)
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1)
    (hED : (s : Set ι).Pairwise
      fun i j ↦ IsEssentiallyDistinct (T i).carrier (T j).carrier) :
    (s.card : NNReal) * δ ^ (Module.finrank ℝ E - 1) ≤
      (Tube.card_le_of_EssDistinct.C (Module.finrank ℝ E)).toNNReal * δ ^ (-4 : ℝ) := by
  set n := Module.finrank ℝ E with hn
  haveI : Nontrivial E :=
    (Module.finrank_pos_iff (R := ℝ) (M := E)).mp (by
      rw [← hn, hE]; norm_num)
  have hn3 : n = 3 := hE
  set D := Tube.card_le_of_EssDistinct.C n with hD_def
  have hD_pos : 0 < D := Tube.card_le_of_EssDistinct.C_pos
  have hδ_real_pos : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ_pos
  have hcard_real : (s.card : ℝ) ≤ D * (1 / (δ : ℝ)) ^ (2 * n) :=
    Tube.card_le_of_EssDistinct hδ_pos 1 s T hball hED
  have hcard_real' : (s.card : ℝ) ≤ D * (δ : ℝ) ^ (-6 : ℝ) := by
    calc
      (s.card : ℝ) ≤ D * (1 / (δ : ℝ)) ^ (2 * n) := hcard_real
      _ = D * (δ : ℝ) ^ (-((2 : ℝ) * (n : ℝ))) := by
        congr 1; rw [one_div, inv_pow]
        rw [show (2 : ℝ) * (n : ℝ) = ((2 * n : ℕ) : ℝ) by
          push_cast; ring]
        rw [Real.rpow_neg hδ_real_pos.le, Real.rpow_natCast]
      _ = D * (δ : ℝ) ^ (-6 : ℝ) := by
        rw [hn3]; norm_num
  -- Transport to `ℝ≥0`: both sides are finite, so `NNReal.coe` reflects the inequality.
  rw [← NNReal.coe_le_coe]
  push_cast [Real.coe_toNNReal D hD_pos.le]
  calc (s.card : ℝ) * (δ : ℝ) ^ (n - 1)
      = (s.card : ℝ) * (δ : ℝ) ^ (2 : ℝ) := by
        rw [hn3]
        norm_num
    _ ≤ (D * (δ : ℝ) ^ (-6 : ℝ)) * (δ : ℝ) ^ (2 : ℝ) := by
        gcongr
    _ = D * ((δ : ℝ) ^ ((-6 : ℝ) + (2 : ℝ))) := by
        rw [Real.rpow_add hδ_real_pos]; ring
    _ = D * (δ : ℝ) ^ (-4 : ℝ) := by norm_num

/-- [Monotonicity of `K_F`]
The partial Frostman estimate is monotone in `β`: `K_F(β)` for `β ≤ β'` implies `K_F(β')`.

Unlike `KatzTaoEstimate.mono`, the exponent occurs twice in the conclusion of
`FrostmanEstimate`, once in `δ ^ (-2 * β)` and once in the exponent `1 - β / 2`, so the two
have to be traded against each other by `monoAlgebra`. That needs an upper bound of the form
`P = s.card * δ ^ (finrank ℝ E - 1) ≤ C * δ ^ (-4)`, and this is where the hypothesis
`finrank ℝ E = 3` enters: the already available count
`Tube.card_le_of_EssDistinct`, which gives `s.card ≤ C * δ ^ (-2 * n)` for pairwise
essentially distinct `δ`-tubes in `B₁`, yields `P ≤ C * δ ^ (-(n + 1))`, and `n + 1 ≤ 4`
exactly when `n ≤ 3`. (For `n ≥ 4` the bound `P ≤ C * δ ^ (-4)` is false in general, so the
statement really is dimension-restricted; the shape `δ ^ (-2 * β)` of `FrostmanEstimate` is
specific to `ℝ ^ 3` anyway.) The constant `C` is absorbed into the `δ ^ (-ε / 2)` slack by
shrinking the threshold `δ₀`. -/
theorem FrostmanEstimate.mono (hE : Module.finrank ℝ E = 3) {β β' : ℝ} (hββ' : β ≤ β')
    (h : FrostmanEstimate.{v} E β) : FrostmanEstimate.{v} E β' := by
  haveI : Nontrivial E :=
    Module.nontrivial_of_finrank_pos (by rw [hE]; norm_num)
  intro ε hε
  set ε' := ε / 2 with hε'_def
  have hε'_pos : 0 < ε' := by linarith
  obtain ⟨η₁, hη₁, hh⟩ := h ε' hε'_pos
  refine ⟨η₁, hη₁, ?_⟩
  set C_real := Tube.card_le_of_EssDistinct.C (Module.finrank ℝ E) with hC_real_def
  have hC_real_pos : 0 < C_real := Tube.card_le_of_EssDistinct.C_pos
  set C_nn : NNReal := C_real.toNNReal with hC_nn_def
  have hC_nn_pos : 0 < C_nn := Real.toNNReal_pos.mpr hC_real_pos
  set C_enn : ENNReal := (C_nn : ENNReal) with hC_enn_def
  have hC_enn_pos : 0 < C_enn := ENNReal.coe_pos.mpr hC_nn_pos
  have hC_enn_ne_top : C_enn ≠ ⊤ := ENNReal.coe_ne_top
  -- Condition: C_enn ^ ((β' - β) / 2) ≤ (δ : ENNReal) ^ (-ε / 2) for small δ
  have hC_cond : ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      C_enn ^ ((β' - β) / 2) ≤ (δ : ENNReal) ^ (-ε / 2) := by
    have hρ : 0 < ε / 2 := by linarith
    have hC_target : 0 < C_enn ^ (-(β' - β) / 2) :=
      ENNReal.rpow_pos hC_enn_pos (by exact hC_enn_ne_top)
    have h_event : ∀ᶠ (δ : NNReal) in 𝓝[>] (0 : NNReal),
      (δ : ENNReal) ^ (ε / 2) ≤ C_enn ^ (-(β' - β) / 2) :=
      ENNReal.eventually_coe_rpow_le_of_pos hρ hC_target
    filter_upwards [h_event] with δ hδ
    calc
      C_enn ^ ((β' - β) / 2) = C_enn ^ (-(-(β' - β) / 2)) := by
        congr 1; ring
      _ = (C_enn ^ (-(β' - β) / 2))⁻¹ := by rw [ENNReal.rpow_neg]
      _ ≤ ((δ : ENNReal) ^ (ε / 2))⁻¹ := ENNReal.inv_le_inv.mpr hδ
      _ = (δ : ENNReal) ^ (-ε / 2) := by
        rw [← ENNReal.rpow_neg, show -(ε / 2) = (-ε / 2 : ℝ) by ring]
  -- Filter to small δ (δ < 1)
  have hIoo : Set.Ioo (0 : NNReal) 1 ∈ 𝓝[>] (0 : NNReal) :=
    Ioo_mem_nhdsGT (show (0 : NNReal) < 1 from zero_lt_one)
  filter_upwards [hh, hC_cond, hIoo]
    with δ hh_δ hC_cond_δ (hδ_range : δ ∈ Set.Ioo (0 : NNReal) 1)
  have hδ_pos : 0 < δ := hδ_range.1
  have hδ_nonzero : (δ : ENNReal) ≠ 0 := by exact_mod_cast hδ_pos.ne'
  have hδ_ne_top : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  intro ι s T hball hED hFrost hFull
  by_cases hcard : s.card = 0
  · have hs : s = ∅ := Finset.card_eq_zero.mp hcard
    subst hs; simp
  have hcard_pos : 0 < s.card := Finset.card_pos.mpr (Finset.card_ne_zero.mp hcard)
  have hcard_pos_enn : 0 < (s.card : ENNReal) := by exact_mod_cast hcard_pos
  have hcard_ne_top : (s.card : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  set P_enn : ENNReal :=
    (s.card : ENNReal) * (δ : ENNReal) ^ (Module.finrank ℝ E - 1) with hP_enn_def
  have hP_enn_pos : 0 < P_enn := by
    dsimp [P_enn]
    have hpos : 0 < (s.card : ENNReal) * (δ : ENNReal) ^ (2 : ℝ) :=
      ENNReal.mul_pos (by exact hcard_pos_enn.ne') (by
        exact (ENNReal.rpow_pos (by exact_mod_cast hδ_pos) hδ_ne_top).ne')
    simpa [hE] using hpos
  have hP_enn_ne_top : P_enn ≠ ⊤ := by
    dsimp [P_enn]
    have hne_top : (s.card : ENNReal) * (δ : ENNReal) ^ (2 : ℝ) ≠ ⊤ :=
      ENNReal.mul_ne_top hcard_ne_top
        (ENNReal.rpow_ne_top_of_ne_zero (y := (2 : ℝ)) hδ_nonzero hδ_ne_top)
    simpa [hE] using hne_top
  have hP_enn_le : P_enn ≤ C_enn * (δ : ENNReal) ^ (-4 : ℝ) := by
    -- The size bound lives in `ℝ≥0`; coerce it here, which is where `ℝ≥0∞` is needed.
    have h_nn : (s.card : NNReal) * δ ^ (Module.finrank ℝ E - 1) ≤ C_nn * δ ^ (-4 : ℝ) :=
      kfSizeUpper_of_card hδ_pos hE s (fun i => (T i).toTube)
        (fun i hi => hball i hi) hED
    calc
      P_enn = (s.card : ENNReal) * (δ : ENNReal) ^ (Module.finrank ℝ E - 1) := rfl
      _ = (((s.card : NNReal) * δ ^ (Module.finrank ℝ E - 1) : NNReal) : ENNReal) := by
        push_cast
        rfl
      _ ≤ ((C_nn * δ ^ (-4 : ℝ) : NNReal) : ENNReal) := ENNReal.coe_le_coe.mpr h_nn
      _ = C_enn * (δ : ENNReal) ^ (-4 : ℝ) := by
        rw [ENNReal.coe_mul, ENNReal.coe_rpow_of_ne_zero hδ_pos.ne']
  calc
    multiplicity s (fun i ↦ (T i).toShadedBody)
        ≤ (δ : ENNReal) ^ (-ε' - 2 * β) * P_enn ^ (1 - β / 2) := by
          simpa [P_enn, hε'_def] using hh_δ s T hball hED hFrost hFull
    _ = (δ : ENNReal) ^ (-(ε / 2 : ℝ)) * (δ : ENNReal) ^ (-2 * β : ℝ) * P_enn ^ (1 - β / 2) := by
      rw [hε'_def, show (-(ε / 2) - 2 * β : ℝ) = (-(ε / 2 : ℝ)) + (-2 * β : ℝ) by ring,
        ENNReal.rpow_add (-(ε / 2 : ℝ)) (-2 * β : ℝ) hδ_nonzero hδ_ne_top]
    _ = (δ : ENNReal) ^ (-ε / 2) * (δ : ENNReal) ^ (-2 * β) * P_enn ^ (1 - β / 2) := by
      rw [show -(ε / 2 : ℝ) = (-ε / 2 : ℝ) by ring]
    _ ≤ (δ : ENNReal) ^ (-ε) * (δ : ENNReal) ^ (-2 * β') * P_enn ^ (1 - β' / 2) :=
      monoAlgebraENN hδ_pos hββ' hC_enn_pos hC_enn_ne_top hC_cond_δ hP_enn_pos hP_enn_ne_top
        hP_enn_le
    _ = (δ : ENNReal) ^ (-ε - 2 * β') * P_enn ^ (1 - β' / 2) := by
      rw [show (-ε - 2 * β' : ℝ) = (-ε : ℝ) + (-2 * β' : ℝ) by ring,
        ENNReal.rpow_add (-ε : ℝ) (-2 * β' : ℝ) hδ_nonzero hδ_ne_top]

end

end Kakeya
