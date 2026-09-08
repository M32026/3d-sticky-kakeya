/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Prism
public import Kakeya.DimensionN.Volume
public import Kakeya.DimensionThree.Slab.Basic
public import Kakeya.Mathlib.MeasureTheory.Strip2D

/-!
# Volume bounds for three-dimensional prisms and slabs

Exact volume formulas for `Prism3D` and `Slab`, together with the pairwise
slab-intersection estimate used in `Kakeya.DimensionThree.Slab.Incidence`.
-/

@[expose] public section

open MeasureTheory Metric

noncomputable section

/-! ## Volumes of three-dimensional prisms -/

namespace Prism3D

variable {a b c : NNReal} {a_le_b : a ≤ b} {b_le_c : b ≤ c}

/-- A `Prism3D a b c` contains the closed Euclidean ball of radius `a`
(the smallest thickness) centered at `P.center`. -/
theorem closedBall_subset_carrier (P : Prism3D a b c a_le_b b_le_c) :
    Metric.closedBall P.center a ⊆ P.carrier := fun x hx => by
  rw [P.mem_carrier_iff]
  intro i
  rw [P.basis.repr_apply_apply, real_inner_comm]
  refine (abs_real_inner_le_norm _ _).trans ?_
  rw [P.basis.norm_eq_one, mul_one, vsub_eq_sub, ← dist_eq_norm, P.thicknesses_eq]
  refine (Metric.mem_closedBall.mp hx).trans ?_
  fin_cases i <;> simp [a_le_b, a_le_b.trans b_le_c]

/-- The volume of a `Prism3D a b c` dominates the volume of the
inscribed closed ball of radius `a`. -/
theorem volume_closedBall_le_volume (P : Prism3D a b c a_le_b b_le_c) :
    volume (Metric.closedBall P.center (a : ℝ)) ≤ volume P.carrier :=
  measure_mono P.closedBall_subset_carrier

/-- A `Prism3D a b c` with `0 < a` has strictly positive volume. -/
theorem volume_pos_of_pos (P : Prism3D a b c a_le_b b_le_c) (ha : 0 < a) :
    0 < volume P.carrier :=
  (Metric.measure_closedBall_pos volume P.center (NNReal.coe_pos.mpr ha)).trans_le
    P.volume_closedBall_le_volume

/-- The exact Lebesgue volume of a `Prism3D a b c`:
`volume P.carrier = 8 · a · b · c`. -/
theorem volume_carrier (P : Prism3D a b c a_le_b b_le_c) :
    volume P.carrier = 8 * (a : ENNReal) * b * c := by
  rw [P.toPrismNDim.volume_carrier, finrank_euclideanSpace_fin, P.thicknesses_eq,
    Fin.prod_univ_three]
  norm_num [Matrix.cons_val_two, Matrix.tail_cons, mul_assoc]

end Prism3D

/-! ## Slab volume and pairwise-intersection estimates -/

namespace Slab

variable {δ : NNReal} {δ_le_one : δ ≤ 1}

/-- The exact Lebesgue volume of a slab `Slab δ`:
`volume S.carrier = 8 · δ`. -/
theorem volume_carrier (S : Slab δ δ_le_one) :
    volume S.carrier = 8 * (δ : ENNReal) := by
  rw [Prism3D.volume_carrier S, ENNReal.coe_one, mul_one, mul_one]

/-- The slab volume dominates its thickness. -/
theorem delta_le_volume (S : Slab δ δ_le_one) :
    (δ : ENNReal) ≤ volume S.carrier := by
  rw [S.volume_carrier]
  calc (δ : ENNReal) = 1 * δ := (one_mul _).symm
    _ ≤ 8 * δ := by gcongr; norm_num

/-- A convenient uniform constant for `Slab.volume_inter_le`. -/
noncomputable abbrev volume_inter_le.C : NNReal := 32

/-! ### Helpers for `Slab.volume_inter_le` -/

private lemma _angle_max_pos {S₁ S₂ : Slab δ δ_le_one} {θ : ℝ}
    (hθ_pos : 0 < θ) (hθ_le : θ ≤ Slab.angle S₁ S₂) :
    let a₀ : ℝ := inner ℝ (S₁.basis 0) (S₂.basis 0)
    let a₁ : ℝ := inner ℝ (S₁.basis 1) (S₂.basis 0)
    let a₂ : ℝ := inner ℝ (S₁.basis 2) (S₂.basis 0)
    a₀^2 + a₁^2 + a₂^2 = 1 ∧ |a₀| ≤ Real.cos θ ∧
      Real.sqrt 2 * θ / Real.pi ≤ max |a₁| |a₂| := by
  intro a₀ a₁ a₂
  have hθ_le_pi2 : θ ≤ Real.pi / 2 := hθ_le.trans (Prism3D.angle_le_pi_div_two _ _)
  have hParseval : a₀^2 + a₁^2 + a₂^2 = 1 := by
    have key : ∀ i, ‖inner ℝ (S₁.basis i) (S₂.basis 0)‖ ^ 2 =
        (inner ℝ (S₁.basis i) (S₂.basis 0))^2 := by
      intro i; rw [Real.norm_eq_abs, sq_abs]
    have hsum := S₁.basis.sum_sq_norm_inner_right (S₂.basis 0)
    rw [S₂.basis.norm_eq_one] at hsum
    rw [Fin.sum_univ_three] at hsum
    simp only [key] at hsum
    rw [show (1:ℝ)^2 = 1 from by norm_num] at hsum
    exact hsum
  have ha0_le : |a₀| ≤ Real.cos θ := by
    have h_eq : |a₀| = Real.cos (Prism3D.angle S₁ S₂) := (Prism3D.cos_angle _ _).symm
    rw [h_eq]
    have h_in_Icc : Prism3D.angle S₁ S₂ ∈ Set.Icc 0 Real.pi := by
      refine ⟨Prism3D.angle_nonneg _ _, ?_⟩
      exact (Prism3D.angle_le_pi_div_two _ _).trans (by linarith [Real.pi_pos])
    have h_θ_in_Icc : θ ∈ Set.Icc 0 Real.pi := by
      refine ⟨hθ_pos.le, ?_⟩
      exact hθ_le_pi2.trans (by linarith [Real.pi_pos])
    exact (Real.strictAntiOn_cos.antitoneOn h_θ_in_Icc h_in_Icc hθ_le)
  have hsin_le : 2 / Real.pi * θ ≤ Real.sin θ := Real.mul_le_sin hθ_pos.le hθ_le_pi2
  have hcos_nn : 0 ≤ Real.cos θ := Real.cos_nonneg_of_neg_pi_div_two_le_of_le
    (by linarith [Real.pi_pos]) hθ_le_pi2
  have ha0_sq_le : a₀^2 ≤ (Real.cos θ)^2 := by
    have h1 : |a₀|^2 ≤ (Real.cos θ)^2 := by
      nlinarith [abs_nonneg a₀, ha0_le, hcos_nn]
    rw [sq_abs] at h1
    exact h1
  have hsumsq_ge : Real.sin θ ^ 2 ≤ a₁^2 + a₂^2 := by
    have hsin_sq : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := by
      have := Real.sin_sq_add_cos_sq θ
      linarith
    rw [hsin_sq]
    linarith [hParseval]
  have htheta_sq_le : (2 / Real.pi * θ)^2 ≤ a₁^2 + a₂^2 := by
    have hnn : 0 ≤ 2 / Real.pi * θ := by positivity
    have hsq : (2 / Real.pi * θ)^2 ≤ Real.sin θ ^ 2 := by
      nlinarith [hsin_le, hnn]
    exact hsq.trans hsumsq_ge
  have hmax_sq : (a₁^2 + a₂^2) / 2 ≤ (max |a₁| |a₂|)^2 := by
    rcases (le_total |a₁| |a₂|) with h | h
    · rw [max_eq_right h, sq_abs]
      nlinarith [sq_abs a₁, sq_abs a₂, abs_nonneg a₁, abs_nonneg a₂, h]
    · rw [max_eq_left h, sq_abs]
      nlinarith [sq_abs a₁, sq_abs a₂, abs_nonneg a₁, abs_nonneg a₂, h]
  have hmax_lb_sq : (Real.sqrt 2 * θ / Real.pi)^2 ≤ (max |a₁| |a₂|)^2 := by
    have h2pi : (2 / Real.pi * θ)^2 / 2 ≤ (max |a₁| |a₂|)^2 := by
      have h1 : (2 / Real.pi * θ)^2 / 2 ≤ (a₁^2 + a₂^2) / 2 := by linarith
      linarith [hmax_sq, h1]
    have heq : (Real.sqrt 2 * θ / Real.pi)^2 = (2 / Real.pi * θ)^2 / 2 := by
      rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
      ring
    linarith [h2pi, heq.le]
  refine ⟨hParseval, ha0_le, ?_⟩
  have hmax_nn : 0 ≤ max |a₁| |a₂| := le_max_iff.mpr (Or.inl (abs_nonneg _))
  have hlhs_nn : 0 ≤ Real.sqrt 2 * θ / Real.pi := by
    have : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    positivity
  nlinarith [hmax_lb_sq, hmax_nn, hlhs_nn, sq_nonneg (max |a₁| |a₂| - Real.sqrt 2 * θ / Real.pi)]

/-- Pairwise slab intersection bound:
if the angle is at least `θ > 0`, then `|S₁ ∩ S₂| ≤ C δ² / θ`. -/
theorem volume_inter_le (S₁ S₂ : Slab δ δ_le_one) {θ : ℝ}
    (hθ_pos : 0 < θ) (hθ_le : θ ≤ Slab.angle S₁ S₂) :
    volume ((S₁.carrier : Set _) ∩ S₂.carrier) ≤
      (volume_inter_le.C : ENNReal) * (δ : ENNReal) ^ 2 / ENNReal.ofReal θ := by
  classical
  set a₀ : ℝ := inner ℝ (S₁.basis 0) (S₂.basis 0) with ha₀_def
  set a₁ : ℝ := inner ℝ (S₁.basis 1) (S₂.basis 0) with ha₁_def
  set a₂ : ℝ := inner ℝ (S₁.basis 2) (S₂.basis 0) with ha₂_def
  set β : ℝ := inner ℝ (S₂.center - S₁.center) (S₂.basis 0) with hβ_def
  obtain ⟨_hParseval, _ha0_le, hmax_lb⟩ := _angle_max_pos hθ_pos hθ_le
  have hmax_pos : 0 < max |a₁| |a₂| :=
    lt_of_lt_of_le (by positivity : 0 < Real.sqrt 2 * θ / Real.pi) hmax_lb
  have h_inter_subset :
      (S₁.carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩ S₂.carrier ⊆
        S₁.carrier ∩ {x | |inner ℝ (x - S₂.center) (S₂.basis 0)| ≤ (δ : ℝ)} := by
    intro x ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have h := S₂.mem_carrier_iff x |>.mp h2 0
    rw [S₂.basis.repr_apply_apply, real_inner_comm] at h
    simpa [S₂.thicknesses_eq, vsub_eq_sub] using h
  refine (measure_mono h_inter_subset).trans ?_
  have h_inner_chart : ∀ x : EuclideanSpace ℝ (Fin 3),
      inner ℝ (x - S₂.center) (S₂.basis 0) =
        a₀ * (S₁.basis.repr (x - S₁.center)).ofLp 0 +
        a₁ * (S₁.basis.repr (x - S₁.center)).ofLp 1 +
        a₂ * (S₁.basis.repr (x - S₁.center)).ofLp 2 - β := by
    intro x
    have hsum_inner : inner ℝ (x - S₁.center) (S₂.basis 0) =
        a₀ * (S₁.basis.repr (x - S₁.center)).ofLp 0 +
        a₁ * (S₁.basis.repr (x - S₁.center)).ofLp 1 +
        a₂ * (S₁.basis.repr (x - S₁.center)).ofLp 2 := by
      conv_lhs => rw [(S₁.basis.sum_repr (x - S₁.center)).symm]
      rw [sum_inner, Fin.sum_univ_three]
      simp only [inner_smul_left, RCLike.conj_to_real]
      ring
    rw [show x - S₂.center = (x - S₁.center) - (S₂.center - S₁.center) from by abel,
      _root_.inner_sub_left, hsum_inner, hβ_def]
  set B : Set (Fin 3 → ℝ) :=
    Set.Icc (![(-(δ : ℝ)), -1, -1] : Fin 3 → ℝ) (![((δ : ℝ)), 1, 1] : Fin 3 → ℝ) ∩
      {y : Fin 3 → ℝ | |a₀ * y 0 + a₁ * y 1 + a₂ * y 2 - β| ≤ (δ : ℝ)} with hB_def
  have hT₀_eq :
      S₁.carrier ∩ {x : EuclideanSpace ℝ (Fin 3) |
          |inner ℝ (x - S₂.center) (S₂.basis 0)| ≤ (δ : ℝ)} =
        (fun x : EuclideanSpace ℝ (Fin 3) => x + (-S₁.center)) ⁻¹'
          (S₁.basis.repr ⁻¹' (WithLp.ofLp ⁻¹' B)) := by
    ext x
    show x ∈ S₁.toPrismNDim.carrier ∩
        {x : EuclideanSpace ℝ (Fin 3) |
          |inner ℝ (x - S₂.center) (S₂.basis 0)| ≤ (δ : ℝ)} ↔ _
    rw [S₁.toPrismNDim.carrier_eq_preimage_Icc]
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq, hB_def, vsub_eq_sub]
    rw [show x + -S₁.center = x - S₁.center from by abel, h_inner_chart x]
    refine and_congr ?_ Iff.rfl
    rw [S₁.thicknesses_eq]
    simp only [Set.mem_Icc, Pi.le_def]
    refine Iff.and (forall_congr' ?_) (forall_congr' ?_)
    · intro j; fin_cases j <;> simp
    · intro j; fin_cases j <;> simp
  rw [hT₀_eq, measure_preimage_add_right,
    S₁.basis.measurePreserving_repr.measure_preimage_emb
      S₁.basis.repr.toHomeomorph.toMeasurableEquiv.measurableEmbedding,
    (PiLp.volume_preserving_ofLp (ι := Fin 3)).measure_preimage_emb
      (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.measurableEmbedding]
  refine (show volume B ≤ ENNReal.ofReal (8 * (δ : ℝ)^2 / max |a₁| |a₂|) by
    convert MeasureTheory.volume_box_inter_linear_strip_le
      (d := (δ : ℝ)) (r := (δ : ℝ)) δ.coe_nonneg δ.coe_nonneg hmax_pos using 2
    ring).trans ?_
  have h_pi_le_4sqrt2 : Real.pi ≤ 4 * Real.sqrt 2 := by
    have h_sqrt2_ge : Real.sqrt 2 ≥ 1 := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt (by norm_num)
    have : Real.pi ≤ 4 := Real.pi_le_four
    linarith
  have h_step : θ ≤ 4 * max |a₁| |a₂| := by
    have h4 : θ ≤ 4 * Real.sqrt 2 * θ / Real.pi := by
      rw [le_div_iff₀ Real.pi_pos]
      nlinarith [hθ_pos, h_pi_le_4sqrt2]
    rw [show 4 * Real.sqrt 2 * θ / Real.pi = 4 * (Real.sqrt 2 * θ / Real.pi) by ring] at h4
    have h6 : 4 * (Real.sqrt 2 * θ / Real.pi) ≤ 4 * max |a₁| |a₂| := by
      have : Real.sqrt 2 * θ / Real.pi ≤ max |a₁| |a₂| := hmax_lb
      linarith
    linarith
  have hδsq_nn : 0 ≤ (δ : ℝ)^2 := sq_nonneg _
  have h_real_bound : 8 * (δ : ℝ)^2 / max |a₁| |a₂| ≤ 32 * (δ : ℝ)^2 / θ := by
    rw [div_le_iff₀ hmax_pos, div_mul_eq_mul_div, le_div_iff₀ hθ_pos]
    nlinarith [h_step, hδsq_nn, hmax_pos.le, hθ_pos.le]
  have hC_eq : (volume_inter_le.C : ENNReal) = ENNReal.ofReal 32 := by
    change ((32 : NNReal) : ENNReal) = ENNReal.ofReal 32
    rw [show ((32 : NNReal) : ENNReal) = ENNReal.ofReal ((32 : NNReal) : ℝ) from
      (ENNReal.ofReal_coe_nnreal).symm]
    norm_num
  have hδsq_eq : ((δ : ENNReal))^2 = ENNReal.ofReal ((δ : ℝ)^2) := by
    rw [show ((δ : ENNReal)) = ENNReal.ofReal (δ : ℝ) from
      (ENNReal.ofReal_coe_nnreal).symm, ← ENNReal.ofReal_pow δ.coe_nonneg]
  rw [hC_eq, hδsq_eq, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 32),
    ← ENNReal.ofReal_div_of_pos hθ_pos, ENNReal.ofReal_le_ofReal_iff (by positivity)]
  exact h_real_bound

end Slab


end

end
