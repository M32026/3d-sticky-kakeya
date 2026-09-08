/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Volume
public import Kakeya.Mathlib.MeasureTheory.CauchySchwarz

/-!
# Slab incidence estimates in `ℝ³`

The incidence estimates for shaded slabs, culminating in GWZ Lemma 6.8
(`ShadedSlab.fullness_sq_angle_le_volume_union`).
-/

@[expose] public section

open MeasureTheory

noncomputable section

namespace ShadedSlab

variable {δ : NNReal} {h : δ ≤ 1} {ι : Type*}

/-! ### Shaded-slab mass and incidence estimates -/

/-- Sum of slab carrier volumes equals `|s| · 8δ`. -/
lemma sum_volume_carrier_eq (s : Finset ι) (V : ι → ShadedSlab δ h) :
    ∑ i ∈ s, volume (V i).carrier = (s.card : ENNReal) * (8 * (δ : ENNReal)) := by
  rw [Finset.sum_congr rfl fun i _ => Slab.volume_carrier (V i).toPrism3D,
    Finset.sum_const, nsmul_eq_mul]

/-- The shading-mass identity for slabs. -/
lemma sum_volume_shade_eq (s : Finset ι) (V : ι → ShadedSlab δ h) :
    ∑ i ∈ s, volume (V i).shade =
      (ShadedBody.fullness s (fun i => (V i).toShadedBody) : ENNReal) *
        ((s.card : ENNReal) * (8 * (δ : ENNReal))) := by
  rw [ShadedBody.sum_volumeReal_shade_eq_fullness_mul s (fun i => (V i).toShadedBody),
    sum_volume_carrier_eq s V]

/-! ### GWZ Lemma 6.8 (`fullness_sq_angle_le_volume_union`) -/

/-- The uniform constant for the `θ`-denominator incidence bound
`triAtAngle_le_card_sq_theta`. Its value `40 = Slab.volume_inter_le.C + 8`
is the optimum of the two-case proof: it balances the pairwise bound
(constant `volume_inter_le.C = 32`, at scale `θ - δ`) against the trivial
slab-volume bound (`|carrier| = 8δ`) at the threshold `θ = 5δ`, where both
sides force `40`. -/
noncomputable abbrev triAtAngle_le_card_sq_theta.C : NNReal := 40

/-- The multiplicative constant in `fullness_sq_angle_le_volume_union`. It is exactly the constant
of the pairwise incidence bound `triAtAngle_le_card_sq_theta.C` (`= 40`): the
`(8δ)² = 64` loss sits on the left-hand side and is `≥ 1`, so it does not
enter the right-hand constant. -/
noncomputable abbrev fullness_sq_angle_le_volume_union.C : NNReal :=
  triAtAngle_le_card_sq_theta.C

theorem fullness_sq_angle_le_volume_union.C_pos : 0 < C := by norm_num

theorem fullness_sq_angle_le_volume_union.one_le_C : 1 ≤ C := by norm_num

/-- Cauchy-Schwarz incidence bound after restricting to a typical angle. -/
theorem sum_shade_sq_le_union_mul_triAtAngle
    (s : Finset ι) (V : ι → ShadedSlab δ h)
    (θ : ℝ) (M : ENNReal)
    (h_typ : IsTypicalIntersectionAngle s V θ M) :
    (∑ i ∈ s, volume (V i).shade) ^ 2 ≤
        M * volume (⋃ i ∈ s, (V i).shade) * triAtAngle s V θ := by
  have hmeas : ∀ i ∈ s, MeasurableSet ((V i).shade) :=
    fun i _ => (V i).measurableSet_shade
  exact (MeasureTheory.sq_sum_volume_le hmeas).trans
    ((mul_le_mul_right h_typ.tri_le_smul_triAtAngle _).trans_eq (by ring))

/-- **The pairwise bound in the shading.** If `0 < δ ≤ θ` and two shaded `δ`-slabs make an
angle at least `θ - δ`, then `|Y₁ ∩ Y₂| ≤ 40 δ² / θ`.

The endpoint range `θ ≤ 5δ`, where `Slab.volume_inter_le` is unavailable because `θ - δ` may
vanish, is covered by the trivial bound `|Y₁ ∩ Y₂| ≤ |S₁| = 8δ`; that is what turns the constant
`32` of `Slab.volume_inter_le` into `40`. -/
theorem volume_shade_inter_le (S T : ShadedSlab δ h) {θ : ℝ}
    (hδ_pos : 0 < δ) (hδθ : (δ : ℝ) ≤ θ)
    (hangle : θ - δ ≤ Slab.angle S.toPrism3D T.toPrism3D) :
    volume (S.shade ∩ T.shade) ≤
      (triAtAngle_le_card_sq_theta.C : ENNReal) * (δ : ENNReal) ^ 2 /
        ENNReal.ofReal θ := by
  have hδ_pos' : (0 : ℝ) < δ := by exact_mod_cast hδ_pos
  have hθ_pos : 0 < θ := lt_of_lt_of_le hδ_pos' hδθ
  set B : ENNReal :=
    (triAtAngle_le_card_sq_theta.C : ENNReal) * (δ : ENNReal) ^ 2 /
      ENNReal.ofReal θ with hB
  have hδ2 : (δ : ENNReal) ^ 2 = ENNReal.ofReal ((δ : ℝ) ^ 2) := by
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_pow δ.coe_nonneg]
  have hBeq : B = ENNReal.ofReal (40 * (δ : ℝ) ^ 2 / θ) := by
    have hC : (triAtAngle_le_card_sq_theta.C : ENNReal) = ENNReal.ofReal 40 := by
      rw [← ENNReal.ofReal_coe_nnreal]
      norm_num [triAtAngle_le_card_sq_theta.C]
    rw [hB, hC, hδ2, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 40),
      ← ENNReal.ofReal_div_of_pos hθ_pos]
  have hvol_8 : volume (S.shade ∩ T.shade) ≤ 8 * (δ : ENNReal) := by
    calc
      volume (S.shade ∩ T.shade) ≤ volume S.carrier :=
        measure_mono (Set.inter_subset_left.trans S.shade_subset)
      _ = 8 * (δ : ENNReal) := Slab.volume_carrier S.toPrism3D
  rcases le_or_gt θ (5 * δ) with hcase | hcase
  · refine hvol_8.trans ?_
    have h8 : (8 : ENNReal) * (δ : ENNReal) = ENNReal.ofReal (8 * (δ : ℝ)) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8), ENNReal.ofReal_ofNat,
        ENNReal.ofReal_coe_nnreal]
    rw [h8, hBeq]
    apply ENNReal.ofReal_le_ofReal
    rw [le_div_iff₀ hθ_pos]
    nlinarith [mul_nonneg hδ_pos'.le (by linarith : (0 : ℝ) ≤ 5 * δ - θ)]
  · have hθδ_pos : 0 < θ - δ := by nlinarith [hδ_pos', hcase]
    have h_subset :
        (S.shade ∩ T.shade) ⊆
          ((S.toPrism3D.carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩ T.toPrism3D.carrier) :=
      Set.inter_subset_inter S.shade_subset T.shade_subset
    have h_pair := Slab.volume_inter_le S.toPrism3D T.toPrism3D hθδ_pos hangle
    refine ((measure_mono h_subset).trans h_pair).trans ?_
    have h32 :
        (Slab.volume_inter_le.C : ENNReal) * (δ : ENNReal) ^ 2 /
            ENNReal.ofReal (θ - δ) =
          ENNReal.ofReal (32 * (δ : ℝ) ^ 2 / (θ - δ)) := by
      have hC : (Slab.volume_inter_le.C : ENNReal) = ENNReal.ofReal 32 := by
        rw [← ENNReal.ofReal_coe_nnreal]
        norm_num [Slab.volume_inter_le.C]
      rw [hC, hδ2, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 32),
        ← ENNReal.ofReal_div_of_pos hθδ_pos]
    rw [h32, hBeq]
    apply ENNReal.ofReal_le_ofReal
    rw [div_le_div_iff₀ hθδ_pos hθ_pos]
    nlinarith [mul_nonneg (sq_nonneg (δ : ℝ)) (by linarith : (0 : ℝ) ≤ θ - 5 * δ)]

/-- Bound `Tri_θ` with `θ` in the denominator, valid in the endpoint range
`δ ≤ θ ≤ 1`. This is the refined form used by the endpoint version of
Lemma 6.8 (`slab3`). -/
theorem triAtAngle_le_card_sq_theta
    (s : Finset ι) (V : ι → ShadedSlab δ h) {θ : ℝ}
    (hδθ : (δ : ℝ) ≤ θ) (_hθ1 : θ ≤ 1)
    (hδ_pos : 0 < δ) :
    triAtAngle s V θ ≤
      (s.card : ENNReal) ^ 2 *
        (triAtAngle_le_card_sq_theta.C : ENNReal) *
        (δ : ENNReal) ^ 2 / ENNReal.ofReal θ := by
  classical
  set B : ENNReal :=
    (triAtAngle_le_card_sq_theta.C : ENNReal) * (δ : ENNReal) ^ 2 /
      ENNReal.ofReal θ with hB
  have hpair : ∀ i j,
      θ - δ ≤ Slab.angle (V i).toPrism3D (V j).toPrism3D →
      volume ((V i).shade ∩ (V j).shade) ≤ B := fun i j hangle ↦
    (volume_shade_inter_le (V i) (V j) hδ_pos hδθ hangle).trans_eq hB.symm
  rw [triAtAngle_def]
  refine (Finset.sum_le_sum fun i _ =>
    (Finset.sum_le_sum fun j hj => hpair i j (Finset.mem_filter.mp hj).2.1).trans
      (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _))).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, hB, sq,
    mul_div_assoc' (s.card : ENNReal), mul_div_assoc' (s.card : ENNReal)]
  congr 1
  ring

/-- Geometric form of Lemma 6.8 before cancelling common factors. -/
theorem fullness_mul_carrier_sq_le
    (s : Finset ι) (V : ι → ShadedSlab δ h)
    (θ : ℝ) (M : ENNReal)
    (h_typ : IsTypicalIntersectionAngle s V θ M)
    (hδθ : (δ : ℝ) ≤ θ) (hθ1 : θ ≤ 1) (hδ_pos : 0 < δ) :
    ((ShadedBody.fullness s (fun i => (V i).toShadedBody) : ENNReal) *
        ((s.card : ENNReal) * (8 * (δ : ENNReal)))) ^ 2 ≤
      M * volume (⋃ i ∈ s, (V i).shade) *
        ((s.card : ENNReal) ^ 2 * (triAtAngle_le_card_sq_theta.C : ENNReal) *
          (δ : ENNReal) ^ 2 / ENNReal.ofReal θ) := by
  rw [← sum_volume_shade_eq]
  exact (sum_shade_sq_le_union_mul_triAtAngle s V θ M h_typ).trans
    (mul_le_mul_right (triAtAngle_le_card_sq_theta s V hδθ hθ1 hδ_pos) _)

/-- Algebraic cancellation step in Lemma 6.8. -/
theorem fullness_sq_angle_le_union
    (s : Finset ι) (V : ι → ShadedSlab δ h)
    (θ : ℝ) (M : ENNReal)
    (h_typ : IsTypicalIntersectionAngle s V θ M)
    (hδθ : (δ : ℝ) ≤ θ) (hθ1 : θ ≤ 1)
    (hδ_pos : 0 < δ) (hs : s.Nonempty) :
    (ShadedBody.fullness s (fun i => (V i).toShadedBody) : ENNReal) ^ 2 *
        (64 : ENNReal) * ENNReal.ofReal θ ≤
      M * volume (⋃ i ∈ s, (V i).shade) *
        (triAtAngle_le_card_sq_theta.C : ENNReal) := by
  have hθ_pos : 0 < θ := lt_of_lt_of_le (by exact_mod_cast hδ_pos) hδθ
  have hgeom := fullness_mul_carrier_sq_le s V θ M h_typ hδθ hθ1 hδ_pos
  set lamU : ENNReal := (ShadedBody.fullness s (fun i => (V i).toShadedBody) : ENNReal)
  set U : ENNReal := volume (⋃ i ∈ s, (V i).shade)
  -- the common factor `card² · δ²` is nonzero (cancellation below) and finite
  have hQ_ne_zero : (s.card : ENNReal) ^ 2 * (δ : ENNReal) ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hs.card_pos.ne'))
      (pow_ne_zero _ (ENNReal.coe_ne_zero.mpr hδ_pos.ne'))
  have hQ_ne_top : (s.card : ENNReal) ^ 2 * (δ : ENNReal) ^ 2 ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _))
      (ENNReal.pow_ne_top ENNReal.coe_ne_top)
  rw [show (lamU * ((s.card : ENNReal) * (8 * (δ : ENNReal)))) ^ 2 =
        (s.card : ENNReal) ^ 2 * (δ : ENNReal) ^ 2 * (lamU ^ 2 * 64) from by ring,
    show M * U * ((s.card : ENNReal) ^ 2 * (triAtAngle_le_card_sq_theta.C : ENNReal) *
          (δ : ENNReal) ^ 2 / ENNReal.ofReal θ) =
        (s.card : ENNReal) ^ 2 * (δ : ENNReal) ^ 2 *
          (M * U * (triAtAngle_le_card_sq_theta.C : ENNReal) / ENNReal.ofReal θ) from by
      rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]; ring] at hgeom
  have hcancel := (ENNReal.mul_le_mul_iff_right hQ_ne_zero hQ_ne_top).mp hgeom
  exact (ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.mpr hθ_pos).ne')
    (Or.inl ENNReal.ofReal_ne_top)).mp hcancel

/-- GWZ Lemma 6.8 (`slab3`), stated here before the volume estimates are available.

This blueprint-facing version allows the endpoint `θ = δ`; the strict-angle
estimate with scale `θ - δ` will appear as a technical step in the later
proof. -/
theorem fullness_sq_angle_le_volume_union
    (s : Finset ι) (V : ι → ShadedSlab δ h)
    (θ : ℝ) (M : ENNReal)
    (h_typ : IsTypicalIntersectionAngle s V θ M)
    (hδθ : (δ : ℝ) ≤ θ) (hθ1 : θ ≤ 1)
    (hδ_pos : 0 < δ) (hs : s.Nonempty)
    (a : NNReal)
    (hlam_lb : a ≤ ShadedBody.fullness s (fun i => (V i).toShadedBody)) :
    a ^ 2 * ENNReal.ofReal θ ≤
      M * volume (⋃ i ∈ s, (V i).shade) *
        (fullness_sq_angle_le_volume_union.C : ENNReal) := by
  have hreadoff := fullness_sq_angle_le_union s V θ M h_typ hδθ hθ1 hδ_pos hs
  have hstep : (a : ENNReal) ^ 2 ≤
      (ShadedBody.fullness s (fun i => (V i).toShadedBody) : ENNReal) ^ 2 * 64 :=
    (ENNReal.pow_le_pow_left (by exact_mod_cast hlam_lb)).trans
      (le_mul_of_one_le_right' (by norm_num))
  exact (mul_le_mul_left hstep _).trans hreadoff

end ShadedSlab

end

end
