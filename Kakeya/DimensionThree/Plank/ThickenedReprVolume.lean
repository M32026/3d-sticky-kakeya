/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Prism
public import Kakeya.Mathlib.Analysis.Trigonometric
public import Kakeya.Mathlib.MeasureTheory.Strip2D
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic

/-!
# Volume bounds supporting thickened representatives

Anisotropic pairwise intersection estimates for `Prism3D`, in the plain, weighted, and
midpoint-weighted forms used by the thickened-plank geometry.  The exact volume formulas
themselves live in `Kakeya.DimensionThree.Volume`.

The file keeps the visibility regime it was written with: only its `public` declarations are
exported.
-/

section

open MeasureTheory Metric

noncomputable section

namespace ThickenedReprPrism3D

variable {a b c : NNReal} {a_le_b : a ≤ b} {b_le_c : b ≤ c}

/-- The absolute constant of `Prism3D.volume_inter_le`. -/
public noncomputable abbrev volume_inter_le.C : NNReal := 32

/-- Volume of a three-dimensional box `[-a, -b, -c] × [a, b, c]` intersected with a linear strip
`|a₀·y₀ + a₁·y₁ + a₂·y₂ - β| ≤ a`, bounded by `8·a²·c / max|a₁||a₂|`. -/
lemma volume_box_inter_linear_strip_le_general {a₀ a₁ a₂ β : ℝ} (ha : 0 ≤ (a : ℝ))
    (hb : 0 ≤ (b : ℝ)) (hc : 0 ≤ (c : ℝ)) (hbc : (b : ℝ) ≤ (c : ℝ))
    (hpos : 0 < max |a₁| |a₂|) :
    volume ((Set.Icc (![-(a : ℝ), -(b : ℝ), -(c : ℝ)] : Fin 3 → ℝ) ![a, b, c]) ∩
            {y : Fin 3 → ℝ | |a₀ * y 0 + a₁ * y 1 + a₂ * y 2 - β| ≤ (a : ℝ)}) ≤
      ENNReal.ofReal (8 * (a : ℝ) ^ 2 * (c : ℝ) / max |a₁| |a₂|) := by
  exact (_root_.MeasureTheory.volume_box_inter_linear_strip_le_general ha hb hc hbc ha hpos
      ).trans_eq (congrArg ENNReal.ofReal (by ring))

/-- An `_angle_max_pos` lemma for `Prism3D`, generalizing the `Slab` version. -/
private lemma _angle_max_pos (P₁ P₂ : Prism3D a b c a_le_b b_le_c) {φ : ℝ}
    (hφ_pos : 0 < φ) (hφ_le : φ ≤ Prism3D.angle P₁ P₂) :
    let a₀ : ℝ := inner ℝ (P₁.basis 0) (P₂.basis 0)
    let a₁ : ℝ := inner ℝ (P₁.basis 1) (P₂.basis 0)
    let a₂ : ℝ := inner ℝ (P₁.basis 2) (P₂.basis 0)
    a₀^2 + a₁^2 + a₂^2 = 1 ∧ |a₀| ≤ Real.cos φ ∧
      Real.sqrt 2 * φ / Real.pi ≤ max |a₁| |a₂| := by
  intro a₀ a₁ a₂
  have hφ_le_pi2 : φ ≤ Real.pi / 2 := hφ_le.trans (Prism3D.angle_le_pi_div_two _ _)
  have hParseval : a₀^2 + a₁^2 + a₂^2 = 1 := by
    have hsum := P₁.basis.sum_sq_norm_inner_right (P₂.basis 0)
    rw [P₂.basis.norm_eq_one, Fin.sum_univ_three, one_pow] at hsum
    simp only [Real.norm_eq_abs, sq_abs] at hsum
    exact hsum
  have ha0_le : |a₀| ≤ Real.cos φ :=
    (Prism3D.cos_angle P₁ P₂).ge.trans <| Real.strictAntiOn_cos.antitoneOn
      ⟨hφ_pos.le, by linarith [Real.pi_pos]⟩
      ⟨Prism3D.angle_nonneg _ _, by linarith [Prism3D.angle_le_pi_div_two P₁ P₂, Real.pi_pos]⟩
      hφ_le
  refine ⟨hParseval, ha0_le, ?_⟩
  have hsin_le : 2 / Real.pi * φ ≤ Real.sin φ := Real.mul_le_sin hφ_pos.le hφ_le_pi2
  have hcos_nn : 0 ≤ Real.cos φ := Real.cos_nonneg_of_neg_pi_div_two_le_of_le
    (by linarith [Real.pi_pos]) hφ_le_pi2
  have ha0_sq_le : a₀^2 ≤ (Real.cos φ)^2 := by
    have h1 : |a₀|^2 ≤ (Real.cos φ)^2 := by
      nlinarith [abs_nonneg a₀, ha0_le, hcos_nn]
    rw [sq_abs] at h1
    exact h1
  have hsumsq_ge : Real.sin φ ^ 2 ≤ a₁^2 + a₂^2 := by
    have hsin_sq : Real.sin φ ^ 2 = 1 - Real.cos φ ^ 2 := by
      have := Real.sin_sq_add_cos_sq φ
      linarith
    rw [hsin_sq]
    linarith [hParseval]
  have htheta_sq_le : (2 / Real.pi * φ)^2 ≤ a₁^2 + a₂^2 := by
    have hnn : 0 ≤ 2 / Real.pi * φ := by positivity
    have hsq : (2 / Real.pi * φ)^2 ≤ Real.sin φ ^ 2 := by
      nlinarith [hsin_le, hnn]
    exact hsq.trans hsumsq_ge
  have hmax_sq : (a₁^2 + a₂^2) / 2 ≤ (max |a₁| |a₂|)^2 := by
    rcases (le_total |a₁| |a₂|) with h | h
    · rw [max_eq_right h, sq_abs]
      nlinarith [sq_abs a₁, sq_abs a₂, abs_nonneg a₁, abs_nonneg a₂, h]
    · rw [max_eq_left h, sq_abs]
      nlinarith [sq_abs a₁, sq_abs a₂, abs_nonneg a₁, abs_nonneg a₂, h]
  have hmax_lb_sq : (Real.sqrt 2 * φ / Real.pi)^2 ≤ (max |a₁| |a₂|)^2 := by
    have h2pi : (2 / Real.pi * φ)^2 / 2 ≤ (max |a₁| |a₂|)^2 := by
      have h1 : (2 / Real.pi * φ)^2 / 2 ≤ (a₁^2 + a₂^2) / 2 := by linarith
      linarith [hmax_sq, h1]
    have heq : (Real.sqrt 2 * φ / Real.pi)^2 = (2 / Real.pi * φ)^2 / 2 := by
      rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
      ring
    linarith [h2pi, heq.le]
  have hmax_nn : 0 ≤ max |a₁| |a₂| := le_max_iff.mpr (Or.inl (abs_nonneg _))
  have hlhs_nn : 0 ≤ Real.sqrt 2 * φ / Real.pi := by
    have : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    positivity
  nlinarith [hmax_lb_sq, hmax_nn, hlhs_nn, sq_nonneg (max |a₁| |a₂| - Real.sqrt 2 * φ / Real.pi)]

/-- **Reduction of a pairwise prism intersection to a box–strip volume.** The intersection
`P₁ ∩ P₂` is contained in `P₁` intersected with the slab of `P₂` about its `k`-th normal, and
reading that set in `P₁`'s own orthonormal chart turns it into the axis-aligned box
`[-a,a] × [-b,b] × [-c,c]` cut by the linear strip whose coefficients are the inner products
`⟪P₁.basis j, P₂.basis k⟫` and whose offset is `⟪P₂.center - P₁.center, P₂.basis k⟫`.

The chart computation is identical for every choice of `k`, so it is done once here and reused by
`volume_inter_le`, `volume_inter_le_weighted` and `volume_inter_le_weighted_mid`. -/
lemma volume_inter_le_volume_box_inter_strip (P₁ P₂ : Prism3D a b c a_le_b b_le_c)
    (k : Fin 3) {t : ℝ} (ht : (P₂.thicknesses k : ℝ) = t) :
    volume ((P₁.carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩ P₂.carrier) ≤
      volume ((Set.Icc (![-(a : ℝ), -(b : ℝ), -(c : ℝ)] : Fin 3 → ℝ) ![a, b, c]) ∩
        {y : Fin 3 → ℝ | |inner ℝ (P₁.basis 0) (P₂.basis k) * y 0 +
            inner ℝ (P₁.basis 1) (P₂.basis k) * y 1 +
            inner ℝ (P₁.basis 2) (P₂.basis k) * y 2 -
            inner ℝ (P₂.center - P₁.center) (P₂.basis k)| ≤ t}) := by
  set a₀ : ℝ := inner ℝ (P₁.basis 0) (P₂.basis k)
  set a₁ : ℝ := inner ℝ (P₁.basis 1) (P₂.basis k)
  set a₂ : ℝ := inner ℝ (P₁.basis 2) (P₂.basis k)
  set β : ℝ := inner ℝ (P₂.center - P₁.center) (P₂.basis k) with hβ_def
  set B : Set (Fin 3 → ℝ) :=
    Set.Icc (![-(a : ℝ), -(b : ℝ), -(c : ℝ)] : Fin 3 → ℝ)
        (![(a : ℝ), (b : ℝ), (c : ℝ)] : Fin 3 → ℝ) ∩
      {y : Fin 3 → ℝ | |a₀ * y 0 + a₁ * y 1 + a₂ * y 2 - β| ≤ t} with hB_def
  have h_inter_subset :
      (P₁.carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩ P₂.carrier ⊆
        P₁.carrier ∩ {x | |inner ℝ (x - P₂.center) (P₂.basis k)| ≤ t} := by
    intro x ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have h := P₂.mem_carrier_iff x |>.mp h2 k
    rw [P₂.basis.repr_apply_apply, real_inner_comm, vsub_eq_sub] at h
    rwa [← ht]
  refine (measure_mono h_inter_subset).trans ?_
  have h_inner_chart : ∀ x : EuclideanSpace ℝ (Fin 3),
      inner ℝ (x - P₂.center) (P₂.basis k) =
        a₀ * (P₁.basis.repr (x - P₁.center)).ofLp 0 +
        a₁ * (P₁.basis.repr (x - P₁.center)).ofLp 1 +
        a₂ * (P₁.basis.repr (x - P₁.center)).ofLp 2 - β := by
    intro x
    have hsum_inner : inner ℝ (x - P₁.center) (P₂.basis k) =
        a₀ * (P₁.basis.repr (x - P₁.center)).ofLp 0 +
        a₁ * (P₁.basis.repr (x - P₁.center)).ofLp 1 +
        a₂ * (P₁.basis.repr (x - P₁.center)).ofLp 2 := by
      conv_lhs => rw [(P₁.basis.sum_repr (x - P₁.center)).symm]
      rw [sum_inner, Fin.sum_univ_three]
      simp only [inner_smul_left, RCLike.conj_to_real]
      ring
    rw [show x - P₂.center = (x - P₁.center) - (P₂.center - P₁.center) from by abel,
      _root_.inner_sub_left, hsum_inner, hβ_def]
  have hT₀_eq :
      P₁.carrier ∩ {x : EuclideanSpace ℝ (Fin 3) |
          |inner ℝ (x - P₂.center) (P₂.basis k)| ≤ t} =
        (fun x : EuclideanSpace ℝ (Fin 3) => x + (-P₁.center)) ⁻¹'
          (P₁.basis.repr ⁻¹' (WithLp.ofLp ⁻¹' B)) := by
    ext x
    show x ∈ P₁.toPrismNDim.carrier ∩
        {x : EuclideanSpace ℝ (Fin 3) |
          |inner ℝ (x - P₂.center) (P₂.basis k)| ≤ t} ↔ _
    rw [P₁.toPrismNDim.carrier_eq_preimage_Icc]
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq, hB_def, vsub_eq_sub]
    rw [show x + -P₁.center = x - P₁.center from by abel, h_inner_chart x]
    refine and_congr ?_ Iff.rfl
    rw [P₁.thicknesses_eq]
    simp only [Set.mem_Icc, Pi.le_def]
    exact Iff.and (forall_congr' fun j => by fin_cases j <;> rfl)
      (forall_congr' fun j => by fin_cases j <;> rfl)
  rw [hT₀_eq, measure_preimage_add_right,
    P₁.basis.measurePreserving_repr.measure_preimage_emb
      P₁.basis.repr.toHomeomorph.toMeasurableEquiv.measurableEmbedding,
    (PiLp.volume_preserving_ofLp (ι := Fin 3)).measure_preimage_emb
      (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.measurableEmbedding]

/-- **Pairwise prism intersection bound at the prism's own scale.** For two equal-scale
`a × b × c` prisms making short-normal angle at least `φ > 0`,
`|P₁ ∩ P₂| ≤ 32 · a² · c / φ`.

This is the scale-parameterized generalization of `Slab.volume_inter_le`, which is exactly the case
`a = δ`, `b = c = 1`. The generalization is *needed*, not cosmetic: routing a `θb × b × 1`
thickening through its containing `θ × 1 × 1` slab loses a factor `b³` (the slab has volume `~θ`
while the thickening has volume `~θb³`), so the slab-scale estimate is vacuous for small `b`. Here
the two thin slabs supporting `P₁, P₂` have half-width `a` and the intersection beam has extent at
most the long half-width `c`, giving the cross-section `~a²/φ` times `c`. -/
public theorem volume_inter_le (P₁ P₂ : Prism3D a b c a_le_b b_le_c) {φ : ℝ}
    (hφ_pos : 0 < φ) (hφ_le : φ ≤ Prism3D.angle P₁ P₂) :
    volume ((P₁.carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩ P₂.carrier) ≤
      (volume_inter_le.C : ENNReal) * (a : ENNReal) ^ 2 * (c : ENNReal) /
        ENNReal.ofReal φ := by
  obtain ⟨-, -, hmax_lb⟩ := _angle_max_pos P₁ P₂ hφ_pos hφ_le
  have hmax_pos : 0 < max |inner ℝ (P₁.basis 1) (P₂.basis 0)|
      |inner ℝ (P₁.basis 2) (P₂.basis 0)| :=
    lt_of_lt_of_le (by positivity : 0 < Real.sqrt 2 * φ / Real.pi) hmax_lb
  refine ((volume_inter_le_volume_box_inter_strip P₁ P₂ 0 (by simp [P₂.thicknesses_eq])).trans
    (volume_box_inter_linear_strip_le_general a.coe_nonneg b.coe_nonneg c.coe_nonneg
      (by exact_mod_cast b_le_c) hmax_pos)).trans ?_
  set M : ℝ := max |inner ℝ (P₁.basis 1) (P₂.basis 0)| |inner ℝ (P₁.basis 2) (P₂.basis 0)|
  have h_step : φ ≤ 4 * M := by
    have h1 : (1 : ℝ) ≤ Real.sqrt 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
    nlinarith [(div_le_iff₀ Real.pi_pos).mp hmax_lb, Real.pi_le_four, hmax_pos.le, hφ_pos.le]
  have h_real_bound : 8 * (a : ℝ) ^ 2 * (c : ℝ) / M ≤ 32 * (a : ℝ) ^ 2 * (c : ℝ) / φ := by
    rw [div_le_div_iff₀ hmax_pos hφ_pos]
    linarith [mul_le_mul_of_nonneg_left h_step
      (by positivity : (0 : ℝ) ≤ 8 * (a : ℝ) ^ 2 * (c : ℝ))]
  refine (ENNReal.ofReal_le_ofReal h_real_bound).trans_eq ?_
  rw [ENNReal.ofReal_div_of_pos hφ_pos]
  congr 1
  rw [show (32 : ℝ) * (a : ℝ) ^ 2 * (c : ℝ) = ((32 * a ^ 2 * c : NNReal) : ℝ) from by
      push_cast; ring, ENNReal.ofReal_coe_nnreal]
  push_cast
  ring

/-- Weighted version of `volume_box_inter_linear_strip_le_general`:
bounds `volume(B)` by `8·a²·b·c / max (|a₁|·b) (|a₂|·c)`. -/
lemma volume_box_inter_linear_strip_le_weighted {a₀ a₁ a₂ β : ℝ} (ha : 0 ≤ (a : ℝ))
    (hb : 0 < (b : ℝ)) (hc : 0 < (c : ℝ))
    (hpos : 0 < max (|a₁| * (b : ℝ)) (|a₂| * (c : ℝ))) :
    volume ((Set.Icc (![-(a : ℝ), -(b : ℝ), -(c : ℝ)] : Fin 3 → ℝ) ![a, b, c]) ∩
            {y : Fin 3 → ℝ | |a₀ * y 0 + a₁ * y 1 + a₂ * y 2 - β| ≤ (a : ℝ)}) ≤
      ENNReal.ofReal
        (8 * (a : ℝ) ^ 2 * (b : ℝ) * (c : ℝ) / max (|a₁| * (b : ℝ)) (|a₂| * (c : ℝ))) := by
  refine (volume_box_inter_linear_strip_le_of_slice (i := 0) (j₀ := 1) (j₁ := 2)
    (s := (a : ℝ)) (u := (b : ℝ)) (u' := (c : ℝ)) (d := a₁) (d' := a₂)
    (by decide) (by decide) rfl ha rfl rfl rfl rfl
    fun γ => volume_strip_inter_rectangle_le_max_weighted (C := γ) ha hb hc hpos).trans_eq ?_
  congr 1
  ring

/-- **Weighted (anisotropic) prism intersection bound.** With
`a₁ := ⟪P₁.basis 1, P₂.basis 0⟫` and `a₂ := ⟪P₁.basis 2, P₂.basis 0⟫`,
`|P₁ ∩ P₂| ≤ 8 · a² · b · c / max (|a₁| · b) (|a₂| · c)`.

Unlike `volume_inter_le`, whose denominator is the short-normal *angle*, this version keeps the two
off-thin frame coefficients weighted by *their own* half-widths. That is exactly what is needed to
control the in-plane rotation at scale `b` rather than at scale `a`: for a thickening
(`a = θb`, `b = b`, `c = 1`) it yields `|⟪e₁,e₀'⟫| ≲ θ` **and** `|⟪e₂,e₀'⟫| ≲ θb`, whereas the
angle-based bound only gives `≲ θ` for both, which is too weak for the long direction. -/
public theorem volume_inter_le_weighted (P₁ P₂ : Prism3D a b c a_le_b b_le_c)
    (hb : 0 < b) (hc : 0 < c)
    (hpos : 0 < max (|inner ℝ (P₁.basis 1) (P₂.basis 0)| * (b : ℝ))
      (|inner ℝ (P₁.basis 2) (P₂.basis 0)| * (c : ℝ))) :
    volume ((P₁.carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩ P₂.carrier) ≤
      ENNReal.ofReal (8 * (a : ℝ) ^ 2 * (b : ℝ) * (c : ℝ) /
        max (|inner ℝ (P₁.basis 1) (P₂.basis 0)| * (b : ℝ))
          (|inner ℝ (P₁.basis 2) (P₂.basis 0)| * (c : ℝ))) :=
  (volume_inter_le_volume_box_inter_strip P₁ P₂ 0 (by simp [P₂.thicknesses_eq])).trans
    (volume_box_inter_linear_strip_le_weighted a.coe_nonneg
      (by exact_mod_cast hb) (by exact_mod_cast hc) hpos)

/-- Weighted version of `volume_box_inter_linear_strip_le_general` slicing at coordinate 1:
bounds `volume(B)` by `8·b²·a·c / max (|a₀|·a) (|a₂|·c)`. -/
lemma volume_box_inter_linear_strip_le_weighted_mid {a₀ a₁ a₂ β : ℝ} (ha : 0 < (a : ℝ))
    (hb : 0 ≤ (b : ℝ)) (hc : 0 < (c : ℝ))
    (hpos : 0 < max (|a₀| * (a : ℝ)) (|a₂| * (c : ℝ))) :
    volume ((Set.Icc (![-(a : ℝ), -(b : ℝ), -(c : ℝ)] : Fin 3 → ℝ) ![a, b, c]) ∩
            {y : Fin 3 → ℝ | |a₀ * y 0 + a₁ * y 1 + a₂ * y 2 - β| ≤ (b : ℝ)}) ≤
      ENNReal.ofReal
        (8 * (b : ℝ) ^ 2 * (a : ℝ) * (c : ℝ) / max (|a₀| * (a : ℝ)) (|a₂| * (c : ℝ))) := by
  refine (volume_box_inter_linear_strip_le_of_slice (i := 1) (j₀ := 0) (j₁ := 2)
    (s := (b : ℝ)) (u := (a : ℝ)) (u' := (c : ℝ)) (d := a₀) (d' := a₂)
    (by decide) (by decide) rfl hb rfl rfl rfl rfl
    fun γ => volume_strip_inter_rectangle_le_max_weighted (C := γ) hb ha hc hpos).trans_eq ?_
  congr 1
  ring

/-- **Weighted prism intersection bound about the middle normal.** The analogue of
`volume_inter_le_weighted` in which the confining slab of `P₂` is taken about its *middle* axis
`P₂.basis 1` (half-width `b`) instead of its thin axis. With
`m₀ := ⟪P₁.basis 0, P₂.basis 1⟫` and `m₂ := ⟪P₁.basis 2, P₂.basis 1⟫`,
`|P₁ ∩ P₂| ≤ 8 · b² · a · c / max (|m₀| · a) (|m₂| · c)`.

This supplies the **in-plane** rotation control at scale `b`, which the thin-normal estimates cannot
give: for thickenings (`a = θb`, `c = 1`) it bounds `|⟪e₂, e₁'⟫| ≲ b`, the coefficient governing how
far `P₁`'s long axis tilts out of `P₂`'s middle direction. Both this and `volume_inter_le_weighted`
are needed for the two-sided dilation comparability of non-distinct thickenings. -/
public theorem volume_inter_le_weighted_mid (P₁ P₂ : Prism3D a b c a_le_b b_le_c)
    (ha : 0 < a) (hc : 0 < c)
    (hpos : 0 < max (|inner ℝ (P₁.basis 0) (P₂.basis 1)| * (a : ℝ))
      (|inner ℝ (P₁.basis 2) (P₂.basis 1)| * (c : ℝ))) :
    volume ((P₁.carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩ P₂.carrier) ≤
      ENNReal.ofReal (8 * (b : ℝ) ^ 2 * (a : ℝ) * (c : ℝ) /
        max (|inner ℝ (P₁.basis 0) (P₂.basis 1)| * (a : ℝ))
          (|inner ℝ (P₁.basis 2) (P₂.basis 1)| * (c : ℝ))) :=
  (volume_inter_le_volume_box_inter_strip P₁ P₂ 1 (by simp [P₂.thicknesses_eq])).trans
    (volume_box_inter_linear_strip_le_weighted_mid (by exact_mod_cast ha) b.coe_nonneg
      (by exact_mod_cast hc) hpos)

end ThickenedReprPrism3D

end

end
