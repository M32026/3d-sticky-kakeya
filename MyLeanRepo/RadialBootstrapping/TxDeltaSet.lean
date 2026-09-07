module

/-
  T_x Delta-Set Property (OSW lines 491-501)

  Main results:
  1. line_ball_to_tube_general — geometric lemma
  2. tube_ball_to_tube — r-tube ∩ B² ⊆ 5ρ-tube
  3. count_ball_from_mass — mass bounds → line count bound
  4. T_x_isDeltaSet — T_x is a delta-set

  Whiteprint node: bootstrapping (Step 3)
-/

public import MyLeanRepo.RadialBootstrapping.Basic
public import MyLeanRepo.RadialBootstrapping.DiscreteFrostmanIsDeltaSet

@[expose] public section

open MeasureTheory Metric Set Finset Classical
open scoped ENNReal NNReal

noncomputable section

namespace RadialBootstrapping

open Vendored.MeasureTheory.FractalGeometry.FrostmanLemma

/-- r-tube around L' intersected with unit ball is contained in ρ-tube around L. -/
def tubeContainedInTube (L L' : Line2) (r ρ : ℝ) : Prop :=
  tube r L' ∩ Metric.closedBall (0 : Point) 1 ⊆ tube ρ L

-- ============================================================================
-- 1. Geometric Lemma
-- ============================================================================

/-- If dist L₁ L₂ ≤ ρ, any point on L₂ within distance R of origin is
within (R+2)ρ of L₁. -/
lemma line_ball_to_tube_general (L₁ L₂ : Line2) (ρ R : ℝ)
    (hρ : 0 < ρ) (hR : 0 ≤ R) (h : dist L₁ L₂ ≤ ρ) :
    Line2.toSet L₂ ∩ Metric.closedBall (0 : Point) R ⊆
      tube ((R + 2) * ρ) L₁ := by
  let p₁ := Line2.closestPoint L₁
  let p₂ := Line2.closestPoint L₂
  let V₁ := L₁.toAffine.direction
  let V₂ := L₂.toAffine.direction
  let proj₁ := submoduleProj V₁
  let proj₂ := submoduleProj V₂

  have hdir : ‖proj₁ - proj₂‖ ≤ ρ := by
    have h1 : lineDirDist L₁ L₂ ≤ dist L₁ L₂ := by
      dsimp only [lineDist, dist]
      have h_off : 0 ≤ lineOffsetDist L₁ L₂ := by
        dsimp only [lineOffsetDist]; exact dist_nonneg
      linarith
    exact le_trans h1 h

  have hoff : ‖p₁ - p₂‖ ≤ ρ := by
    have h1 : lineOffsetDist L₁ L₂ ≤ dist L₁ L₂ := by
      dsimp only [lineDist, dist]
      have h_dir : 0 ≤ lineDirDist L₁ L₂ := by
        dsimp only [lineDirDist, submoduleDirDist]; positivity
      linarith
    exact le_trans h1 h

  have hp1L1 : p₁ ∈ L₁.toAffine := Line2.closestPoint_mem L₁
  have hp2L2 : p₂ ∈ L₂.toAffine := Line2.closestPoint_mem L₂

  have hp2_in_orth : p₂ ∈ V₂ᗮ := by
    dsimp only [p₂, Line2.closestPoint]
    let p : Point := Classical.choose L₂.exists_point
    have h_eq : submoduleProj V₂ = V₂.starProjection := submoduleProj_eq_starProjection V₂
    have h : p - submoduleProj V₂ p ∈ V₂ᗮ := by
      rw [h_eq]
      have h2 : p - V₂.starProjection p = V₂ᗮ.starProjection p :=
        (Submodule.starProjection_orthogonal_val p).symm
      rw [h2]; exact Submodule.starProjection_apply_mem V₂ᗮ p
    exact h

  intro x hx
  have hxL2 : x ∈ L₂.toAffine := hx.1
  have hxnorm : ‖x‖ ≤ R := by simpa [Metric.mem_closedBall] using hx.2

  let v₂ : Point := x - p₂
  have hv2V2 : v₂ ∈ V₂ := L₂.toAffine.vsub_mem_direction hxL2 hp2L2

  have hv2orth : inner ℝ p₂ v₂ = 0 := by
    have h_orth : ∀ u ∈ V₂, inner ℝ u p₂ = 0 := (V₂.mem_orthogonal p₂).mp hp2_in_orth
    have h1 : inner ℝ v₂ p₂ = 0 := h_orth v₂ hv2V2
    have h2 : inner ℝ p₂ v₂ = inner ℝ v₂ p₂ := by exact real_inner_comm v₂ p₂
    rw [h2, h1]

  have hpyth : ‖x‖ ^ 2 = ‖p₂‖ ^ 2 + ‖v₂‖ ^ 2 := by
    have h_eq : p₂ + v₂ = x := by simp [v₂] <;> abel
    have h_norm := norm_add_sq_eq_norm_sq_add_norm_sq_real (x := p₂) (y := v₂) hv2orth
    have h5 : ‖p₂ + v₂‖ ^ 2 = ‖p₂‖ ^ 2 + ‖v₂‖ ^ 2 := by simpa [pow_two] using h_norm
    rw [h_eq] at h5; exact h5

  have hv2norm : ‖v₂‖ ≤ R := by
    have h1 : ‖v₂‖ ^ 2 ≤ ‖x‖ ^ 2 := by
      rw [hpyth]; exact le_add_of_nonneg_left (sq_nonneg ‖p₂‖)
    have h2 : 0 ≤ ‖v₂‖ := norm_nonneg v₂
    have h3 : 0 ≤ ‖x‖ := norm_nonneg x
    have h4 : |‖v₂‖| ≤ |‖x‖| := sq_le_sq.mp h1
    have h5 : ‖v₂‖ ≤ ‖x‖ := by
      simpa [abs_of_nonneg (norm_nonneg v₂), abs_of_nonneg (norm_nonneg x)] using h4
    linarith [hxnorm]

  have hproj2_v2 : proj₂ v₂ = v₂ := by
    have h_eq : proj₂ = V₂.starProjection := submoduleProj_eq_starProjection V₂
    rw [h_eq]; exact Submodule.starProjection_eq_self_iff.mpr hv2V2

  let w : Point := x - p₁
  let y : Point := p₁ + proj₁ w

  have hproj1_w_in_V1 : proj₁ w ∈ V₁ := by
    have h_eq : proj₁ = V₁.starProjection := submoduleProj_eq_starProjection V₁
    rw [h_eq]; exact Submodule.starProjection_apply_mem V₁ w

  have hyL1 : y ∈ L₁.toAffine := by
    have h_vadd : (proj₁ w) +ᵥ p₁ ∈ L₁.toAffine :=
      L₁.toAffine.vadd_mem_of_mem_direction hproj1_w_in_V1 hp1L1
    have h_eq : (proj₁ w) +ᵥ p₁ = p₁ + proj₁ w := by
      simp [vadd_eq_add] <;> abel
    rw [h_eq] at h_vadd; exact h_vadd

  have hdist : dist x y = ‖w - proj₁ w‖ := by
    simp [y, w, dist_eq_norm] <;> abel_nf

  have h1 : w = v₂ + (p₂ - p₁) := by simp [w, v₂] <;> abel

  have h2 : w - proj₁ w = (proj₂ - proj₁) v₂ + ((p₂ - p₁) - proj₁ (p₂ - p₁)) := by
    rw [h1]
    have h3 : proj₁ (v₂ + (p₂ - p₁)) = proj₁ v₂ + proj₁ (p₂ - p₁) := map_add proj₁ v₂ (p₂ - p₁)
    rw [h3]
    have h4 : (proj₂ - proj₁) v₂ = proj₂ v₂ - proj₁ v₂ := by simp [sub_apply]
    rw [h4, hproj2_v2] <;> abel

  have h4 : ‖(proj₂ - proj₁) v₂‖ ≤ ‖proj₂ - proj₁‖ * ‖v₂‖ :=
    ContinuousLinearMap.le_opNorm (proj₂ - proj₁) v₂

  have h_orth_norm : ∀ (z : Point), ‖z - proj₁ z‖ ≤ ‖z‖ := by
    intro z
    have h_a : z - proj₁ z ∈ V₁ᗮ := by
      have h_eq : proj₁ = V₁.starProjection := submoduleProj_eq_starProjection V₁
      rw [h_eq]
      have h2 : z - V₁.starProjection z = V₁ᗮ.starProjection z :=
        (Submodule.starProjection_orthogonal_val z).symm
      rw [h2]; exact Submodule.starProjection_apply_mem V₁ᗮ z
    have h_b : proj₁ z ∈ V₁ := by
      have h_eq : proj₁ = V₁.starProjection := submoduleProj_eq_starProjection V₁
      rw [h_eq]; exact Submodule.starProjection_apply_mem V₁ z
    have h_inner : inner ℝ (proj₁ z) (z - proj₁ z) = 0 := by
      have h_orth : ∀ u ∈ V₁, inner ℝ u (z - proj₁ z) = 0 :=
        (V₁.mem_orthogonal (z - proj₁ z)).mp h_a
      exact h_orth (proj₁ z) h_b
    have h_pyth : ‖z‖ ^ 2 = ‖proj₁ z‖ ^ 2 + ‖z - proj₁ z‖ ^ 2 := by
      have h_eq : (proj₁ z) + (z - proj₁ z) = z := by abel
      have h_norm := norm_add_sq_eq_norm_sq_add_norm_sq_real (x := proj₁ z) (y := z - proj₁ z) h_inner
      have h5 : ‖(proj₁ z) + (z - proj₁ z)‖ ^ 2 = ‖proj₁ z‖ ^ 2 + ‖z - proj₁ z‖ ^ 2 := by
        simpa [pow_two] using h_norm
      rw [h_eq] at h5; exact h5
    have h6 : ‖z - proj₁ z‖ ^ 2 ≤ ‖z‖ ^ 2 := by
      rw [h_pyth]; exact le_add_of_nonneg_left (sq_nonneg ‖proj₁ z‖)
    have h7 : 0 ≤ ‖z‖ := norm_nonneg z
    have h8 : 0 ≤ ‖z - proj₁ z‖ := norm_nonneg _
    have h9 : |‖z - proj₁ z‖| ≤ |‖z‖| := sq_le_sq.mp h6
    simpa [abs_of_nonneg h8, abs_of_nonneg h7] using h9

  have h5 : ‖(p₂ - p₁) - proj₁ (p₂ - p₁)‖ ≤ ‖p₂ - p₁‖ := h_orth_norm (p₂ - p₁)

  have h6 : ‖w - proj₁ w‖ ≤ ‖(proj₂ - proj₁) v₂‖ + ‖(p₂ - p₁) - proj₁ (p₂ - p₁)‖ := by
    rw [h2]; exact norm_add_le _ _

  have h81 : ‖proj₂ - proj₁‖ ≤ ρ := by
    have h82 : ‖proj₂ - proj₁‖ = ‖proj₁ - proj₂‖ := by rw [norm_sub_rev]
    rw [h82]; exact hdir

  have h7 : ‖w - proj₁ w‖ < (R + 2) * ρ := by
    have h8 : ‖proj₂ - proj₁‖ * ‖v₂‖ ≤ ρ * R := by
      have h82 : ‖v₂‖ ≤ R := hv2norm
      calc ‖proj₂ - proj₁‖ * ‖v₂‖ ≤ ρ * ‖v₂‖ := by gcongr
        _ ≤ ρ * R := by gcongr
    have h9 : ‖p₂ - p₁‖ ≤ ρ := by
      have h10 : ‖p₂ - p₁‖ = ‖p₁ - p₂‖ := by rw [norm_sub_rev]
      rw [h10]; exact hoff
    calc
      ‖w - proj₁ w‖ ≤ ‖(proj₂ - proj₁) v₂‖ + ‖(p₂ - p₁) - proj₁ (p₂ - p₁)‖ := h6
      _ ≤ ‖proj₂ - proj₁‖ * ‖v₂‖ + ‖p₂ - p₁‖ := by gcongr
      _ ≤ ρ * R + ρ := by linarith
      _ = (R + 1) * ρ := by ring
      _ < (R + 2) * ρ := by nlinarith

  have h_main : dist x y < (R + 2) * ρ := by rw [hdist]; exact h7
  simp only [tube, Metric.mem_thickening_iff]
  exact ⟨y, hyL1, h_main⟩

-- ============================================================================
-- 2. Tube-to-tube lemma
-- ============================================================================

/-- If dist L₁ L₂ ≤ ρ, r ≤ ρ ≤ 1, then tube(r, L₂) ∩ B² ⊆ tube(5ρ, L₁). -/
lemma tube_ball_to_tube (L₁ L₂ : Line2) (r ρ : ℝ)
    (hr : 0 < r) (hρ : 0 < ρ) (hr_le : r ≤ ρ) (hρ1 : ρ ≤ 1)
    (h : dist L₁ L₂ ≤ ρ) :
    tubeContainedInTube L₁ L₂ r (5 * ρ) := by
  intro y hy
  have hy_tube : y ∈ tube r L₂ := hy.1
  have hynorm : ‖y‖ ≤ 1 := by simpa [Metric.mem_closedBall] using hy.2

  rcases (Metric.mem_thickening_iff).mp hy_tube with ⟨z, hzL2, hdist_yz⟩
  have hz_norm : ‖z‖ ≤ 2 := by
    have h1 : ‖z‖ ≤ ‖y‖ + ‖z - y‖ := by
      calc ‖z‖ = ‖y + (z - y)‖ := by rw [add_sub_cancel]
        _ ≤ ‖y‖ + ‖z - y‖ := norm_add_le _ _
    have h2 : ‖z - y‖ = dist z y := by simp [dist_eq_norm]
    rw [h2] at h1
    have h3 : dist z y = dist y z := dist_comm z y
    rw [h3] at h1; linarith

  have hz_in : z ∈ Line2.toSet L₂ ∩ Metric.closedBall (0 : Point) 2 :=
    ⟨hzL2, by simpa [Metric.mem_closedBall] using hz_norm⟩

  have hz_tube : z ∈ tube (4 * ρ) L₁ := by
    have h_general := line_ball_to_tube_general L₁ L₂ ρ 2 hρ (by norm_num) h hz_in
    have h_eq : (2 + 2) * ρ = 4 * ρ := by ring
    rw [h_eq] at h_general; exact h_general

  rcases (Metric.mem_thickening_iff).mp hz_tube with ⟨w, hwL1, hdist_zw⟩
  have hdist_yw : dist y w < 5 * ρ := by
    have h1 : dist y w ≤ dist y z + dist z w := dist_triangle y z w
    have h4 : dist y w < r + 4 * ρ := by linarith [hdist_yz, hdist_zw, h1]
    have h5 : r + 4 * ρ ≤ 5 * ρ := by linarith
    linarith

  simp only [tube, Metric.mem_thickening_iff]
  exact ⟨w, hwL1, hdist_yw⟩

-- ============================================================================
-- 3. Count bound from mass bounds
-- ============================================================================

/-- Given mass upper bound on wide tubes, mass lower bound on thin tubes,
and bounded overlap, bound the number of thin tubes contained in a wide tube. -/
lemma count_ball_from_mass
    (r σ : ℝ) (hr : 0 < r) (hσ : 0 ≤ σ)
    (K m ov : ℝ) (hK : 0 ≤ K) (hm : 0 < m) (hov : 0 ≤ ov)
    (ν : Measure Point) (Y_x : Set Point) (T_x : Finset Line2)
    (h_mass_upper : ∀ (L : Line2) (ρ : ℝ), r ≤ ρ → ρ ≤ 1 →
        ν (tube (5 * ρ) L ∩ Y_x) ≤ ENNReal.ofReal (K * Real.rpow ρ σ))
    (h_mass_lower : ∀ L' ∈ T_x,
        ν (tube r L' ∩ Y_x) ≥ ENNReal.ofReal m)
    (h_overlap : ∀ (L : Line2) (ρ : ℝ), r ≤ ρ → ρ ≤ 1 →
        ∑ L' ∈ T_x.filter (fun L' => tubeContainedInTube L L' r (5 * ρ)),
          ν (tube r L' ∩ Y_x) ≤
        ENNReal.ofReal ov * ν (tube (5 * ρ) L ∩ Y_x)) :
    ∀ (L : Line2) (ρ : ℝ), r ≤ ρ → ρ ≤ 1 →
      (T_x.filter (fun L' => tubeContainedInTube L L' r (5 * ρ))).card
      ≤ (ov * K / m) * Real.rpow ρ σ := by
  intro L ρ hρ hρ1
  let S : Finset Line2 := T_x.filter (fun L' => tubeContainedInTube L L' r (5 * ρ))
  let a : ENNReal := ENNReal.ofReal m
  let b : ENNReal := ENNReal.ofReal (ov * K * Real.rpow ρ σ)

  have h_rho_nonneg : 0 ≤ Real.rpow ρ σ := Real.rpow_nonneg (by linarith) _
  have h_b_nonneg : 0 ≤ ov * K * Real.rpow ρ σ := by positivity

  have h_leq : ∀ L' ∈ S, a ≤ ν (tube r L' ∩ Y_x) := by
    intro L' hL'
    have h_in_Tx : L' ∈ T_x := (Finset.mem_filter.mp hL').1
    exact h_mass_lower L' h_in_Tx

  have h_sum_ge : (S.card : ENNReal) * a ≤ ∑ L' ∈ S, ν (tube r L' ∩ Y_x) := by
    calc
      (S.card : ENNReal) * a = ∑ L' ∈ S, a := by simp [Finset.sum_const] <;> ring
      _ ≤ ∑ L' ∈ S, ν (tube r L' ∩ Y_x) := Finset.sum_le_sum h_leq

  have h_sum_le : ∑ L' ∈ S, ν (tube r L' ∩ Y_x) ≤
      ENNReal.ofReal ov * ν (tube (5 * ρ) L ∩ Y_x) := h_overlap L ρ hρ hρ1

  have h_mass : ν (tube (5 * ρ) L ∩ Y_x) ≤ ENNReal.ofReal (K * Real.rpow ρ σ) :=
    h_mass_upper L ρ hρ hρ1

  have h_main : (S.card : ENNReal) * a ≤ b := by
    calc
      (S.card : ENNReal) * a ≤ ∑ L' ∈ S, ν (tube r L' ∩ Y_x) := h_sum_ge
      _ ≤ ENNReal.ofReal ov * ν (tube (5 * ρ) L ∩ Y_x) := h_sum_le
      _ ≤ ENNReal.ofReal ov * ENNReal.ofReal (K * Real.rpow ρ σ) := by gcongr
      _ = b := by
        have h_pos1 : 0 ≤ ov := hov
        have h_mul : ENNReal.ofReal (ov * (K * Real.rpow ρ σ)) =
            ENNReal.ofReal ov * ENNReal.ofReal (K * Real.rpow ρ σ) :=
          ENNReal.ofReal_mul (hp := h_pos1)
        have h_comm : ov * (K * Real.rpow ρ σ) = ov * K * Real.rpow ρ σ := by ring
        rw [h_comm] at h_mul
        exact h_mul.symm

  have h_iff : (S.card : ENNReal) * a ≤ b ↔ (S.card : ℝ) * m ≤ ov * K * Real.rpow ρ σ := by
    have h2 : (S.card : ENNReal) * a = ENNReal.ofReal ((S.card : ℝ) * m) := by
      have h_nat : (S.card : ENNReal) = ENNReal.ofReal (S.card : ℝ) := by simp
      rw [h_nat]
      have h_mul : ENNReal.ofReal ((S.card : ℝ) * m) =
          ENNReal.ofReal (S.card : ℝ) * ENNReal.ofReal m :=
        ENNReal.ofReal_mul (hp := by positivity)
      exact h_mul.symm
    rw [h2]
    constructor
    · intro h
      have h7 : ((S.card : ℝ) * m) ≤ (ENNReal.ofReal (ov * K * Real.rpow ρ σ)).toReal :=
        (ENNReal.ofReal_le_iff_le_toReal ENNReal.ofReal_ne_top).mp h
      have h8 : (ENNReal.ofReal (ov * K * Real.rpow ρ σ)).toReal = ov * K * Real.rpow ρ σ := by
        rw [ENNReal.toReal_ofReal h_b_nonneg]
      rw [h8] at h7
      exact h7
    · intro h
      exact ENNReal.ofReal_le_ofReal h

  have h9 : (S.card : ℝ) * m ≤ ov * K * Real.rpow ρ σ := h_iff.mp h_main

  have h10 : (S.card : ℝ) ≤ (ov * K / m) * Real.rpow ρ σ := by
    have h1 : m ≠ 0 := hm.ne'
    have h_div : ((S.card : ℝ) * m) / m = (S.card : ℝ) := by
      have h2 : ((S.card : ℝ) * m) / m = (S.card : ℝ) := by
        exact MulDivCancelClass.mul_div_cancel (↑(#S)) m h1
      exact h2
    have h_ineq : (S.card : ℝ) ≤ (ov * K * Real.rpow ρ σ) / m := by
      rw [← h_div]
      exact div_le_div_of_nonneg_right h9 (by linarith)
    have h_final : (ov * K * Real.rpow ρ σ) / m = (ov * K / m) * Real.rpow ρ σ := by ring
    rw [h_final] at h_ineq
    exact h_ineq

  exact h10

-- ============================================================================
-- 4. T_x Delta-Set Theorem
-- ============================================================================

/-- T_x is a (r, σ, C)-set, given 2r-separation and a count bound. -/
theorem T_x_isDeltaSet
    (r σ C : ℝ) (hr : 0 < r) (hσ : 0 ≤ σ) (hC : 0 ≤ C) (hC1 : 1 ≤ C)
    (T_x : Finset Line2)
    (h_nonempty : T_x.Nonempty)
    (h_count : ∀ (L : Line2) (ρ : ℝ), r ≤ ρ → ρ ≤ 1 →
        (T_x.filter (fun L' => L' ∈ ball L ρ)).card ≤ C * Real.rpow ρ σ * T_x.card)
    (h_sep : Metric.IsSeparated (ENNReal.ofReal (2 * r)) (T_x : Set Line2)) :
    IsDeltaSet r σ C hr hσ hC (T_x : Set Line2) := by
  let δn : NNReal := ⟨r, hr.le⟩

  have h1 : (δn : ENNReal) = ENNReal.ofReal r := by
    have h2 : (δn : ℝ) = r := by
      dsimp only [δn]
      exact Subtype.coe_mk r hr.le
    have h3 : (δn : ENNReal) = ENNReal.ofReal (δn : ℝ) := by exact ENNReal.coe_nnreal_eq δn
    rw [h3, h2]

  have h_sep' : Metric.IsSeparated (2 * δn) (T_x : Set Line2) := by
    have h_eq : (2 * δn : ENNReal) = ENNReal.ofReal (2 * r) := by
      calc (2 * δn : ENNReal) = 2 * (δn : ENNReal) := by simp
        _ = 2 * ENNReal.ofReal r := by rw [h1]
        _ = ENNReal.ofReal (2 * r) := by
          have h21 : (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) := by simp
          rw [h21]
          have h22 : ENNReal.ofReal ((2 : ℝ) * r) = ENNReal.ofReal (2 : ℝ) * ENNReal.ofReal r :=
            ENNReal.ofReal_mul (hp := by norm_num)
          exact h22.symm
    rw [h_eq]; exact h_sep

  have h_ecard_Tx : (Metric.externalCoveringNumber δn (T_x : Set Line2) : ENNReal) = ↑(T_x.card) := by
    have h := externalCoveringNumber_eq_encard_of_separated (T_x.finite_toSet)
      (by exact_mod_cast hr) h_sep'
    exact_mod_cast h

  intro L ρ' hρ'

  by_cases h_case : ρ' ≥ 1
  · -- Case ρ' ≥ 1
    have h_sub : (T_x : Set Line2) ∩ ball L ρ' ⊆ (T_x : Set Line2) := Set.inter_subset_left
    have h1 : (Metric.externalCoveringNumber δn ((T_x : Set Line2) ∩ ball L ρ') : ENNReal) ≤
        Metric.externalCoveringNumber δn (T_x : Set Line2) :=
      mod_cast Metric.externalCoveringNumber_mono_set h_sub
    have h_card1 : (1 : ℝ) ≤ (T_x.card : ℝ) := by
      exact Nat.one_le_cast.mpr (Finset.one_le_card.mpr h_nonempty)
    have h2 : 1 ≤ C * Real.rpow ρ' σ := by
      have h22 : 1 ≤ Real.rpow ρ' σ := by apply Real.one_le_rpow <;> linarith
      nlinarith
    have h3 : (1 : ENNReal) ≤ ENNReal.ofReal (C * Real.rpow ρ' σ) := by
      rw [ENNReal.one_le_ofReal] <;> linarith
    have h4 : Metric.externalCoveringNumber δn (T_x : Set Line2) ≤
        ENNReal.ofReal (C * Real.rpow ρ' σ) * Metric.externalCoveringNumber δn (T_x : Set Line2) :=
      le_mul_of_one_le_left' h3
    calc
      (Metric.externalCoveringNumber δn ((T_x : Set Line2) ∩ ball L ρ') : ENNReal)
        ≤ Metric.externalCoveringNumber δn (T_x : Set Line2) := h1
      _ ≤ ENNReal.ofReal (C * Real.rpow ρ' σ) * Metric.externalCoveringNumber δn (T_x : Set Line2) := h4

  · -- Case r ≤ ρ' < 1
    have hρ'_lt_one : ρ' < 1 := by linarith
    have hρ'_pos : 0 < ρ' := by linarith

    let S_finset : Finset Line2 := T_x.filter (fun L' => L' ∈ ball L ρ')
    have hS_set : (S_finset : Set Line2) = (T_x : Set Line2) ∩ ball L ρ' := by
      ext L'; simp [S_finset, Set.mem_inter_iff] <;> aesop

    have hS_sep : Metric.IsSeparated (2 * δn) (S_finset : Set Line2) :=
      h_sep'.mono (show (S_finset : Set Line2) ⊆ (T_x : Set Line2) from by
        intro x hx; exact (Finset.mem_filter.mp hx).1)

    have h_ecard_S : (Metric.externalCoveringNumber δn (S_finset : Set Line2) : ENNReal) =
        ↑(S_finset.card) := by
      have h := externalCoveringNumber_eq_encard_of_separated (S_finset.finite_toSet)
        (by exact_mod_cast hr) hS_sep
      exact_mod_cast h

    have h_card : (S_finset.card : ℝ) ≤ C * Real.rpow ρ' σ * T_x.card :=
      h_count L ρ' hρ' (by linarith)

    have h_pos : 0 ≤ C * Real.rpow ρ' σ := by
      have h1 : 0 ≤ C := hC
      have h2 : 0 ≤ Real.rpow ρ' σ := Real.rpow_nonneg (by linarith) _
      exact mul_nonneg h1 h2

    have h_pos2 : 0 ≤ C * Real.rpow ρ' σ * (T_x.card : ℝ) := by positivity

    have h_final : (↑(S_finset.card) : ENNReal) ≤
        ENNReal.ofReal (C * Real.rpow ρ' σ * (T_x.card : ℝ)) := by
      have h5 : (S_finset.card : ℝ) ≤ C * Real.rpow ρ' σ * (T_x.card : ℝ) := h_card
      have h6 : (↑(S_finset.card) : ENNReal) = ENNReal.ofReal (S_finset.card : ℝ) := by simp
      rw [h6]
      exact ENNReal.ofReal_le_ofReal h5

    have h4 : ENNReal.ofReal (C * Real.rpow ρ' σ) * ↑(T_x.card) =
        ENNReal.ofReal (C * Real.rpow ρ' σ * (T_x.card : ℝ)) := by
      have h_mul1 : ENNReal.ofReal (C * Real.rpow ρ' σ) * ↑(T_x.card) =
          ENNReal.ofReal (C * Real.rpow ρ' σ) * ENNReal.ofReal (T_x.card : ℝ) := by simp
      rw [h_mul1]
      have h_mul2 : ENNReal.ofReal (C * Real.rpow ρ' σ) * ENNReal.ofReal (T_x.card : ℝ) =
          ENNReal.ofReal ((C * Real.rpow ρ' σ) * (T_x.card : ℝ)) := by exact Eq.symm (ENNReal.ofReal_mul h_pos)
      rw [h_mul2] <;> ring

    have h_goal : (Metric.externalCoveringNumber δn ((T_x : Set Line2) ∩ ball L ρ') : ENNReal) ≤
        ENNReal.ofReal (C * Real.rpow ρ' σ) * Metric.externalCoveringNumber δn (T_x : Set Line2) := by
      rw [← hS_set, h_ecard_S, h_ecard_Tx]
      rw [h4]
      exact h_final

    exact h_goal

end RadialBootstrapping
