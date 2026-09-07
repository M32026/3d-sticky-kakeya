import MyLeanRepo.Kakeya.Assouad.WZ1.SegmentConstruction
import MyLeanRepo.Kakeya.Assouad.WZ1.ActiveCostBoundsHelpers
import MyLeanRepo.Kakeya.Assouad.WZ1.GlobalSlabADTransport

/-!
# Assembly of budgeted segment conversion from anchored hierarchy

Constructs the `WZ1MultiscaleSlopeCorrectionData` from an anchored
Corollary 26 hierarchy, including active cost bounds and global slab AD.
-/

namespace Kakeya.Assouad

open Real WZ1VerticalTrapezoid

/-- Bound `rho_prev / sqrt(rho)` for level k ≥ 1. -/
lemma rpow_ratio_sqrt_bound {delta : ℝ} {N : ℕ} {h : ℝ}
    (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k < N)
    (hN : 0 < N) (hh : 0 ≤ h) :
    Real.rpow delta ((k : ℝ) / (N : ℝ)) /
      Real.sqrt (Real.rpow delta (((k : ℝ) + 1) / (N : ℝ))) ≤ 1 := by
  have h1 : Real.sqrt (Real.rpow delta (((k : ℝ) + 1) / (N : ℝ))) =
      Real.rpow delta (((k : ℝ) + 1) / (2 * (N : ℝ))) := by
    rw [sqrt_rpow hdelta] <;> ring
  rw [h1]
  have h_exp : (k : ℝ) / (N : ℝ) - ((k : ℝ) + 1) / (2 * (N : ℝ)) =
      ((k : ℝ) - 1) / (2 * (N : ℝ)) := by field_simp <;> ring
  have h2 : Real.rpow delta ((k : ℝ) / (N : ℝ)) /
      Real.rpow delta (((k : ℝ) + 1) / (2 * (N : ℝ))) =
      Real.rpow delta (((k : ℝ) - 1) / (2 * (N : ℝ))) := by
    have h_sub := (Real.rpow_sub hdelta ((k : ℝ) / (N : ℝ)) (((k : ℝ) + 1) / (2 * (N : ℝ)))).symm
    simpa [h_exp] using h_sub
  rw [h2]
  have h4 : 0 ≤ ((k : ℝ) - 1) / (2 * (N : ℝ)) := by
    have h5 : (k : ℝ) - 1 ≥ 0 := by exact_mod_cast (show 0 ≤ k - 1 from by omega)
    positivity
  exact Real.rpow_le_one hdelta.le hdelta_one h4

/-- Bound `rho_prev / rho^(1/2+h)` for level k ≥ 1. -/
lemma rpow_ratio_slope_bound {delta : ℝ} {N : ℕ} {h : ℝ}
    (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k < N)
    (hN : 0 < N) (hh : 0 ≤ h) :
    Real.rpow delta ((k : ℝ) / (N : ℝ)) /
      Real.rpow delta ((((k : ℝ) + 1) / (N : ℝ)) * (1 / 2 + h)) ≤
      Real.rpow delta (-(1 / (N : ℝ) + h)) := by
  set y := (k : ℝ) / (N : ℝ) with hy_def
  set z := (((k : ℝ) + 1) / (N : ℝ)) * (1 / 2 + h) with hz_def
  have h_exp : y - z = ((k : ℝ) - 1 - 2 * h * ((k : ℝ) + 1)) / (2 * (N : ℝ)) := by
    simp only [hy_def, hz_def] <;> field_simp <;> ring
  have h2 : Real.rpow delta y / Real.rpow delta z = Real.rpow delta (y - z) :=
    (Real.rpow_sub hdelta y z).symm
  rw [h2, h_exp]
  apply Real.rpow_le_rpow_of_exponent_ge hdelta hdelta_one
  exact exp_ineq_b hN hh hk1 hk2

/-- Bound `rho_prev / rho` for level k ≥ 1. -/
lemma rpow_ratio_rho_bound {delta : ℝ} {N : ℕ} {h : ℝ}
    (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    {k : ℕ} (hk2 : k < N) (hN : 0 < N) (hh : 0 ≤ h) :
    Real.rpow delta ((k : ℝ) / (N : ℝ)) /
      Real.rpow delta (((k : ℝ) + 1) / (N : ℝ)) ≤
      Real.rpow delta (-(1 / (N : ℝ) + h)) := by
  set y := (k : ℝ) / (N : ℝ) with hy_def
  set z := ((k : ℝ) + 1) / (N : ℝ) with hz_def
  have h_exp : y - z = -(1 / (N : ℝ)) := by
    simp only [hy_def, hz_def] <;> field_simp <;> ring
  have h2 : Real.rpow delta y / Real.rpow delta z = Real.rpow delta (y - z) :=
    (Real.rpow_sub hdelta y z).symm
  rw [h2, h_exp]
  exact rpow_neg_mono hdelta hdelta_one (by linarith)

/-- Bound `rho_prev / rho^(1+h)` for level k ≥ 1. -/
lemma rpow_ratio_second_bound {delta : ℝ} {N : ℕ} {h : ℝ}
    (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    {k : ℕ} (hk2 : k < N) (hN : 0 < N) (hh : 0 ≤ h) :
    Real.rpow delta ((k : ℝ) / (N : ℝ)) /
      Real.rpow delta ((((k : ℝ) + 1) / (N : ℝ)) * (1 + h)) ≤
      Real.rpow delta (-(1 / (N : ℝ) + h)) := by
  set y := (k : ℝ) / (N : ℝ) with hy_def
  set z := (((k : ℝ) + 1) / (N : ℝ)) * (1 + h) with hz_def
  have h_exp : y - z = -((1 + ((k : ℝ) + 1) * h) / (N : ℝ)) := by
    simp only [hy_def, hz_def] <;> field_simp <;> ring
  have h2 : Real.rpow delta y / Real.rpow delta z = Real.rpow delta (y - z) :=
    (Real.rpow_sub hdelta y z).symm
  rw [h2, h_exp]
  apply Real.rpow_le_rpow_of_exponent_ge hdelta hdelta_one
  exact exp_ineq_d hN hh hk2

/-- Per-level cost bound from the carrier-independent hierarchy fields. -/
lemma per_level_cost_bound_of_hierarchy
    {delta hierarchyLoss : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {sourceSlope : ℝ → ℝ}
    (hierarchy :
      WZ1Corollary26AnchoredHierarchyData
        Y sourceSlope hierarchyLoss)
    (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    (hhierarchyLoss : 0 ≤ hierarchyLoss)
    (hlevelZeroEndpoints :
      ∀ level, ∀ trapezoid ∈ hierarchy.trapezoids level,
        (level : ℕ) = 0 →
          |trapezoid.affine trapezoid.left| ≤ 4 ∧
            |trapezoid.affine trapezoid.right| ≤ 4)
    (level : Fin hierarchy.levelCount)
    (trapezoid : WZ1VerticalTrapezoid)
    (htrapezoid : trapezoid ∈ hierarchy.trapezoids level)
    (segment : WZ1SegmentCorrection)
    (hsegment : segment = makeSegment hierarchy hdelta level trapezoid htrapezoid) :
    segment.firstCost ≤ 34 * Real.rpow delta (-(1 / (hierarchy.levelCount : ℝ) + hierarchyLoss)) ∧
    segment.secondCost ≤ 136 * Real.rpow delta (-(1 / (hierarchy.levelCount : ℝ) + hierarchyLoss)) ∧
    segment.valueCost ≤ 85 * Real.rpow delta (-(1 / (hierarchy.levelCount : ℝ) + hierarchyLoss)) := by
  let N := hierarchy.levelCount
  let e := -(1 / (N : ℝ) + hierarchyLoss)
  have hN_pos : 0 < N := by
    have h : 2 ≤ N := hierarchy.levelCount_two
    omega
  have hN_real_pos : 0 < (N : ℝ) := by exact_mod_cast hN_pos
  have hhl : 0 ≤ hierarchyLoss := hhierarchyLoss
  have h_e_arg_pos : 0 ≤ 1 / (N : ℝ) + hierarchyLoss := by
    have h1 : 0 < 1 / (N : ℝ) := by positivity
    linarith
  have h_one_le_rpow : (1 : ℝ) ≤ Real.rpow delta e :=
    one_le_rpow_neg hdelta hdelta_one h_e_arg_pos
  have h_half_le : 1 / (2 * (N : ℝ)) ≤ 1 / (N : ℝ) + hierarchyLoss := by
    have h2 : 1 / (2 * (N : ℝ)) ≤ 1 / (N : ℝ) := by
      apply one_div_le_one_div_of_le
      · positivity
      · have h3 : (N : ℝ) ≤ 2 * (N : ℝ) := by linarith [hN_real_pos]
        exact h3
    have h4 : 1 / (N : ℝ) ≤ 1 / (N : ℝ) + hierarchyLoss := by linarith
    exact le_trans h2 h4
  have h_1_N_le : 1 / (N : ℝ) ≤ 1 / (N : ℝ) + hierarchyLoss := by linarith
  have h_rpow_half : Real.rpow delta (-(1 / (2 * (N : ℝ)))) ≤ Real.rpow delta e :=
    rpow_neg_mono hdelta hdelta_one h_half_le
  have h_rpow_1_N : Real.rpow delta (-(1 / (N : ℝ))) ≤ Real.rpow delta e :=
    rpow_neg_mono hdelta hdelta_one h_1_N_le

  let rho := wz1Corollary26Scale delta N level
  have hrho_pos : 0 < rho := Real.rpow_pos_of_pos hdelta _
  have hrho_le_one : rho ≤ 1 := by
    apply Real.rpow_le_one hdelta.le hdelta_one
    positivity

  let seg := makeSegment hierarchy hdelta level trapezoid htrapezoid
  have h_buf : seg.buffer = Real.sqrt rho / 4 :=
    makeSegment_buffer hierarchy hdelta level trapezoid htrapezoid
  have h_sqrt_le_one : Real.sqrt rho ≤ 1 := by
    have h : Real.sqrt rho ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hrho_le_one
    rwa [Real.sqrt_one] at h
  have hsqrt_pos : 0 < Real.sqrt rho := Real.sqrt_pos.mpr hrho_pos
  have h_inv_rpow : ∀ (a : ℝ), (Real.rpow delta a)⁻¹ = Real.rpow delta (-a) :=
    fun a => (Real.rpow_neg hdelta.le a).symm

  have h_main : seg.firstCost ≤ 34 * Real.rpow delta e ∧
      seg.secondCost ≤ 136 * Real.rpow delta e ∧
      seg.valueCost ≤ 85 * Real.rpow delta e := by
    by_cases hlevel0 : (level : ℕ) = 0
    · -- Level 0 case
      have h_endpoints : |trapezoid.affine trapezoid.left| ≤ 4 ∧
          |trapezoid.affine trapezoid.right| ≤ 4 :=
        hlevelZeroEndpoints level trapezoid htrapezoid hlevel0
      have h_slope_bound : |trapezoid.slope| ≤ 2 :=
        hierarchy.slope_bound level trapezoid htrapezoid

      have h_y1 : seg.y₁ = trapezoid.affine trapezoid.left := by
        dsimp only [seg, makeSegment]
        rw [dif_pos hlevel0] <;> rfl
      have h_y2 : seg.y₂ = trapezoid.affine trapezoid.right := by
        dsimp only [seg, makeSegment]
        rw [dif_pos hlevel0] <;> rfl
      have h_x1 : seg.x₁ = trapezoid.left :=
        makeSegment_x1 hierarchy hdelta level trapezoid htrapezoid
      have h_x2 : seg.x₂ = trapezoid.right :=
        makeSegment_x2 hierarchy hdelta level trapezoid htrapezoid

      have h_len : seg.x₂ - seg.x₁ ≤ Real.sqrt rho := by
        rw [h_x2, h_x1]
        exact (hierarchy.length_bounds level trapezoid htrapezoid).2

      have h_trap_den : trapezoid.right - trapezoid.left ≠ 0 := by
        have h : trapezoid.left < trapezoid.right := trapezoid.left_lt_right
        linarith

      have h_slope_seg : (seg.y₂ - seg.y₁) / (seg.x₂ - seg.x₁) = trapezoid.slope := by
        rw [h_y2, h_y1, h_x2, h_x1]
        have h_eq : trapezoid.affine trapezoid.right - trapezoid.affine trapezoid.left =
            trapezoid.slope * (trapezoid.right - trapezoid.left) := by
          simp [WZ1VerticalTrapezoid.affine] <;> ring
        rw [h_eq]
        field_simp [h_trap_den] <;> ring

      have hA1 : |seg.y₁| ≤ 4 := by rw [h_y1]; exact h_endpoints.1
      have hA2 : |seg.y₂| ≤ 4 := by rw [h_y2]; exact h_endpoints.2
      have hB : |(seg.y₂ - seg.y₁) / (seg.x₂ - seg.x₁)| ≤ 2 := by
        rw [h_slope_seg]; exact h_slope_bound

      have h_costs := segment_cost_bound seg 4 2 (Real.sqrt rho)
        hA1 hA2 hB h_len (by norm_num) (by norm_num) (by positivity)

      have h_rho_eq : rho = Real.rpow delta (1 / (N : ℝ)) := by
        dsimp only [rho, wz1Corollary26Scale]
        rw [hlevel0] <;> norm_num <;> ring
      have h_sqrt_rho : Real.sqrt rho = Real.rpow delta (1 / (2 * (N : ℝ))) := by
        rw [h_rho_eq, sqrt_rpow hdelta] <;> ring
      have h_sqrt_inv : (Real.sqrt rho)⁻¹ = Real.rpow delta (-(1 / (2 * (N : ℝ)))) := by
        rw [h_sqrt_rho, h_inv_rpow]
      have h_rho_inv : rho⁻¹ = Real.rpow delta (-(1 / (N : ℝ))) := by
        rw [h_rho_eq, h_inv_rpow]

      have h_first_bound : 2 * (4 : ℝ) / seg.buffer + 2 ≤ 34 * Real.rpow delta e := by
        rw [h_buf]
        have h_eq : 2 * (4 : ℝ) / (Real.sqrt rho / 4) + 2 =
            32 * (Real.sqrt rho)⁻¹ + 2 := by
          field_simp [hsqrt_pos.ne'] <;> ring
        rw [h_eq, h_sqrt_inv]
        have h_a : 32 * Real.rpow delta (-(1 / (2 * (N : ℝ)))) ≤ 32 * Real.rpow delta e :=
          mul_le_mul_of_nonneg_left h_rpow_half (by norm_num)
        have h_b : (2 : ℝ) ≤ 2 * Real.rpow delta e := by linarith [h_one_le_rpow]
        linarith

      have h_first' : seg.firstCost ≤ 34 * Real.rpow delta e :=
        le_trans h_costs.1 h_first_bound

      have h_second' : seg.secondCost ≤ 136 * Real.rpow delta e := by
        have h11 : seg.secondCost ≤ 2 * (4 : ℝ) / seg.buffer ^ 2 + 2 / seg.buffer := h_costs.2.1
        rw [h_buf] at h11
        have h_buf2 : (Real.sqrt rho / 4) ^ 2 = rho / 16 := by
          calc
            (Real.sqrt rho / 4) ^ 2 = (Real.sqrt rho) ^ 2 / 16 := by ring
            _ = rho / 16 := by rw [Real.sq_sqrt hrho_pos.le] <;> ring
        rw [h_buf2] at h11
        have h_eq : 2 * (4 : ℝ) / (rho / 16) + 2 / (Real.sqrt rho / 4) =
            128 * rho⁻¹ + 8 * (Real.sqrt rho)⁻¹ := by
          field_simp [hrho_pos.ne', hsqrt_pos.ne'] <;> ring
        rw [h_eq] at h11
        rw [h_rho_inv, h_sqrt_inv] at h11
        have h_a : 128 * Real.rpow delta (-(1 / (N : ℝ))) ≤ 128 * Real.rpow delta e :=
          mul_le_mul_of_nonneg_left h_rpow_1_N (by norm_num)
        have h_b : 8 * Real.rpow delta (-(1 / (2 * (N : ℝ)))) ≤ 8 * Real.rpow delta e :=
          mul_le_mul_of_nonneg_left h_rpow_half (by norm_num)
        linarith

      have h_value' : seg.valueCost ≤ 85 * Real.rpow delta e := by
        have h11 : seg.valueCost ≤ (Real.sqrt rho + 2 * seg.buffer + 1) * (2 * (4 : ℝ) / seg.buffer + 2) :=
          h_costs.2.2
        have h12 : Real.sqrt rho + 2 * seg.buffer + 1 ≤ 5 / 2 := by
          rw [h_buf]
          linarith [h_sqrt_le_one]
        have hbuf_pos' : 0 < seg.buffer := seg.buffer_pos
        have h14 : 0 ≤ 2 * (4 : ℝ) / seg.buffer + 2 := by
          have h15 : 0 ≤ 2 * (4 : ℝ) / seg.buffer := by positivity
          linarith
        calc
          seg.valueCost
            ≤ (Real.sqrt rho + 2 * seg.buffer + 1) * (2 * (4 : ℝ) / seg.buffer + 2) := h11
          _ ≤ (5 / 2 : ℝ) * (2 * (4 : ℝ) / seg.buffer + 2) := by
            exact mul_le_mul_of_nonneg_right h12 h14
          _ ≤ (5 / 2 : ℝ) * (34 * Real.rpow delta e) := by
            exact mul_le_mul_of_nonneg_left h_first_bound (by norm_num)
          _ = 85 * Real.rpow delta e := by ring

      exact ⟨h_first', h_second', h_value'⟩

    · -- Level k > 0 case
      have hk_pos : 0 < (level : ℕ) := by omega
      let parentLevel : Fin N := ⟨(level : ℕ) - 1, by omega⟩
      have hpe : (parentLevel : ℕ) + 1 = (level : ℕ) := by
        simp [parentLevel] <;> omega
      let h_unique := hierarchy.unique_parent parentLevel level hpe trapezoid htrapezoid
      let parent := Classical.choose h_unique
      have hspec : parent ∈ hierarchy.trapezoids parentLevel ∧
          trapezoid.IsNumericallyNestedIn parent :=
        (Classical.choose_spec h_unique).1
      have hnest : trapezoid.IsNumericallyNestedIn parent := hspec.2
      have hparent_mem : parent ∈ hierarchy.trapezoids parentLevel := hspec.1

      let rho_prev := wz1Corollary26Scale delta N parentLevel
      have hrho_prev_pos : 0 < rho_prev := Real.rpow_pos_of_pos hdelta _

      have h_height_child : trapezoid.height = rho :=
        hierarchy.height_eq level trapezoid htrapezoid
      have h_height_parent : parent.height = rho_prev :=
        hierarchy.height_eq parentLevel parent hparent_mem

      have h_y1_eq : seg.y₁ = trapezoid.affine trapezoid.left - parent.affine trapezoid.left := by
        dsimp only [seg, makeSegment]
        rw [dif_neg hlevel0]
        dsimp only [makeSegmentAfterFirst] <;> rfl
      have h_y2_eq : seg.y₂ = trapezoid.affine trapezoid.right - parent.affine trapezoid.right := by
        dsimp only [seg, makeSegment]
        rw [dif_neg hlevel0]
        dsimp only [makeSegmentAfterFirst] <;> rfl

      have h_left_in : trapezoid.left ∈ trapezoid.core := by
        simp only [WZ1VerticalTrapezoid.core, Set.mem_Icc]
        exact ⟨le_refl trapezoid.left, le_of_lt trapezoid.left_lt_right⟩
      have h_right_in : trapezoid.right ∈ trapezoid.core := by
        simp only [WZ1VerticalTrapezoid.core, Set.mem_Icc]
        exact ⟨le_of_lt trapezoid.left_lt_right, le_refl trapezoid.right⟩
      have hA1_raw : |trapezoid.affine trapezoid.left - parent.affine trapezoid.left| ≤
          trapezoid.height + parent.height := hnest.2 trapezoid.left h_left_in
      have hA2_raw : |trapezoid.affine trapezoid.right - parent.affine trapezoid.right| ≤
          trapezoid.height + parent.height := hnest.2 trapezoid.right h_right_in

      set A := rho + rho_prev with hA_def
      have hA_nonneg : 0 ≤ A := by
        dsimp only [A]
        have h1 : 0 ≤ rho := by positivity
        have h2 : 0 ≤ rho_prev := by positivity
        linarith

      have hA1 : |seg.y₁| ≤ A := by
        rw [h_y1_eq]
        have h : trapezoid.height + parent.height = A := by
          rw [h_height_child, h_height_parent, hA_def] <;> ring
        rw [h] at hA1_raw
        exact hA1_raw
      have hA2 : |seg.y₂| ≤ A := by
        rw [h_y2_eq]
        have h : trapezoid.height + parent.height = A := by
          rw [h_height_child, h_height_parent, hA_def] <;> ring
        rw [h] at hA2_raw
        exact hA2_raw

      have h_x1 : seg.x₁ = trapezoid.left :=
        makeSegment_x1 hierarchy hdelta level trapezoid htrapezoid
      have h_x2 : seg.x₂ = trapezoid.right :=
        makeSegment_x2 hierarchy hdelta level trapezoid htrapezoid

      have h_len_bounds := hierarchy.length_bounds level trapezoid htrapezoid
      have h_len_lower : Real.rpow rho (1 / 2 + hierarchyLoss) ≤ trapezoid.length := h_len_bounds.1
      have h_len_upper : trapezoid.length ≤ Real.sqrt rho := h_len_bounds.2

      have hW : seg.x₂ - seg.x₁ ≤ Real.sqrt rho := by
        rw [h_x2, h_x1]
        simpa [WZ1VerticalTrapezoid.length] using h_len_upper

      have h_slope_diff : |trapezoid.slope - parent.slope| ≤
          2 * (trapezoid.height + parent.height) / trapezoid.length :=
        slope_diff_bound trapezoid parent hnest

      have h_den : trapezoid.right - trapezoid.left ≠ 0 := by
        have h : trapezoid.left < trapezoid.right := trapezoid.left_lt_right
        linarith

      have h_slope_seg : (seg.y₂ - seg.y₁) / (seg.x₂ - seg.x₁) = trapezoid.slope - parent.slope := by
        rw [h_y2_eq, h_y1_eq, h_x2, h_x1]
        have h_eq : trapezoid.affine trapezoid.right - parent.affine trapezoid.right -
            (trapezoid.affine trapezoid.left - parent.affine trapezoid.left) =
            (trapezoid.slope - parent.slope) * (trapezoid.right - trapezoid.left) := by
          simp [WZ1VerticalTrapezoid.affine] <;> ring
        rw [h_eq]
        field_simp [h_den] <;> ring

      set B := 2 * A / Real.rpow rho (1 / 2 + hierarchyLoss) with hB_def
      have hB_nonneg : 0 ≤ B := by
        dsimp only [B]
        have h1 : 0 < Real.rpow rho (1 / 2 + hierarchyLoss) := Real.rpow_pos_of_pos hrho_pos _
        positivity

      have h_slope_bound2 : |(seg.y₂ - seg.y₁) / (seg.x₂ - seg.x₁)| ≤ B := by
        rw [h_slope_seg]
        have h1 : |trapezoid.slope - parent.slope| ≤
            2 * (trapezoid.height + parent.height) / trapezoid.length := h_slope_diff
        have h2 : trapezoid.height + parent.height = A := by
          rw [h_height_child, h_height_parent, hA_def] <;> ring
        rw [h2] at h1
        have h_pos_len : 0 < trapezoid.length := by
          simp [WZ1VerticalTrapezoid.length, trapezoid.left_lt_right] <;> linarith
        have h_pos_den : 0 < Real.rpow rho (1 / 2 + hierarchyLoss) := Real.rpow_pos_of_pos hrho_pos _
        have h3 : 2 * A / trapezoid.length ≤ B := by
          rw [hB_def]
          have h4 : 1 / trapezoid.length ≤ 1 / Real.rpow rho (1 / 2 + hierarchyLoss) := by
            apply one_div_le_one_div_of_le h_pos_den h_len_lower
          have h5 : 0 ≤ 2 * A := by dsimp only [A]; positivity
          have h6 : 2 * A / trapezoid.length = (2 * A) * (1 / trapezoid.length) := by ring
          rw [h6]
          have h7 : (2 * A) * (1 / trapezoid.length) ≤ (2 * A) * (1 / Real.rpow rho (1 / 2 + hierarchyLoss)) :=
            mul_le_mul_of_nonneg_left h4 h5
          have h8 : (2 * A) * (1 / Real.rpow rho (1 / 2 + hierarchyLoss)) = 2 * A / Real.rpow rho (1 / 2 + hierarchyLoss) := by ring
          rw [h8] at h7
          exact h7
        exact le_trans h1 h3

      have h_costs := segment_cost_bound seg A B (Real.sqrt rho)
        hA1 hA2 h_slope_bound2 hW hA_nonneg hB_nonneg (by positivity)

      have hk1 : 1 ≤ (level : ℕ) := by omega
      have hk2 : (level : ℕ) < N := level.is_lt

      have h_rho_prev_eq : rho_prev = Real.rpow delta ((level : ℝ) / (N : ℝ)) := by
        dsimp only [rho_prev, wz1Corollary26Scale]
        have h_k : (parentLevel : ℕ) + 1 = (level : ℕ) := hpe
        have h' : ((parentLevel : ℕ) + 1 : ℝ) = (level : ℝ) := by exact_mod_cast h_k
        rw [h'] <;> ring

      have h_rho_eq : rho = Real.rpow delta (((level : ℕ) + 1 : ℝ) / (N : ℝ)) := by
        dsimp only [rho, wz1Corollary26Scale] <;> ring

      have h_ratio_sqrt : rho_prev / Real.sqrt rho ≤ 1 := by
        rw [h_rho_prev_eq, h_rho_eq]
        exact rpow_ratio_sqrt_bound hdelta hdelta_one hk1 hk2 hN_pos hhl

      have h_ratio_slope : rho_prev / Real.rpow rho (1 / 2 + hierarchyLoss) ≤ Real.rpow delta e := by
        rw [h_rho_prev_eq]
        have h_rpow_exp : Real.rpow rho (1 / 2 + hierarchyLoss) =
            Real.rpow delta ((((level : ℕ) + 1 : ℝ) / (N : ℝ)) * (1 / 2 + hierarchyLoss)) := by
          rw [h_rho_eq]
          exact (Real.rpow_mul hdelta.le (((level : ℕ) + 1 : ℝ) / (N : ℝ)) (1 / 2 + hierarchyLoss)).symm
        rw [h_rpow_exp]
        exact rpow_ratio_slope_bound hdelta hdelta_one hk1 hk2 hN_pos hhl

      have h_ratio_rho : rho_prev / rho ≤ Real.rpow delta e := by
        rw [h_rho_prev_eq, h_rho_eq]
        exact rpow_ratio_rho_bound hdelta hdelta_one hk2 hN_pos hhl

      have h_ratio_second : rho_prev / Real.rpow rho (1 + hierarchyLoss) ≤ Real.rpow delta e := by
        rw [h_rho_prev_eq]
        have h_rpow_exp : Real.rpow rho (1 + hierarchyLoss) =
            Real.rpow delta ((((level : ℕ) + 1 : ℝ) / (N : ℝ)) * (1 + hierarchyLoss)) := by
          rw [h_rho_eq]
          exact (Real.rpow_mul hdelta.le (((level : ℕ) + 1 : ℝ) / (N : ℝ)) (1 + hierarchyLoss)).symm
        rw [h_rpow_exp]
        exact rpow_ratio_second_bound hdelta hdelta_one hk2 hN_pos hhl

      have h_rho_le_prev : rho ≤ rho_prev := by
        rw [h_rho_eq, h_rho_prev_eq]
        have h_exp_le : (level : ℝ) / (N : ℝ) ≤ (((level : ℕ) + 1 : ℝ) / (N : ℝ)) := by
          have h : (level : ℝ) ≤ ((level : ℕ) + 1 : ℝ) := by simp
          gcongr
        exact Real.rpow_le_rpow_of_exponent_ge hdelta hdelta_one h_exp_le

      have hA_le : A ≤ 2 * rho_prev := by
        rw [hA_def]
        have h : rho ≤ rho_prev := h_rho_le_prev
        linarith

      have h_2A_buf : 2 * A / seg.buffer ≤ 16 * Real.rpow delta e := by
        rw [h_buf]
        have h1 : 2 * A / (Real.sqrt rho / 4) = 8 * A / Real.sqrt rho := by
          field_simp [hsqrt_pos.ne'] <;> ring
        rw [h1]
        have h21 : 8 * A ≤ 16 * rho_prev := by linarith [hA_le]
        have h2 : 8 * A / Real.sqrt rho ≤ 16 * rho_prev / Real.sqrt rho :=
          div_le_div_of_nonneg_right h21 hsqrt_pos.le
        have h4 : rho_prev / Real.sqrt rho ≤ 1 := h_ratio_sqrt
        have h5 : rho_prev / Real.sqrt rho ≤ Real.rpow delta e := le_trans h4 h_one_le_rpow
        have h3 : 16 * (rho_prev / Real.sqrt rho) ≤ 16 * Real.rpow delta e :=
          mul_le_mul_of_nonneg_left h5 (by norm_num)
        have h_eq : 16 * rho_prev / Real.sqrt rho = 16 * (rho_prev / Real.sqrt rho) := by ring
        have h2' : 8 * A / Real.sqrt rho ≤ 16 * (rho_prev / Real.sqrt rho) := by
          rw [← h_eq]
          exact h2
        exact le_trans h2' h3

      have h_B_le : B ≤ 4 * Real.rpow delta e := by
        rw [hB_def]
        have hD_pos : 0 < Real.rpow rho (1 / 2 + hierarchyLoss) := Real.rpow_pos_of_pos hrho_pos _
        have h21 : 2 * A ≤ 4 * rho_prev := by linarith [hA_le]
        have hD_pos2 : 0 < Real.rpow rho (1 / 2 + hierarchyLoss) := Real.rpow_pos_of_pos hrho_pos _
        have h : 2 * A / Real.rpow rho (1 / 2 + hierarchyLoss) ≤
            4 * rho_prev / Real.rpow rho (1 / 2 + hierarchyLoss) :=
          div_le_div_of_nonneg_right h21 hD_pos2.le
        have h2 : 4 * (rho_prev / Real.rpow rho (1 / 2 + hierarchyLoss)) ≤ 4 * Real.rpow delta e :=
          mul_le_mul_of_nonneg_left h_ratio_slope (by norm_num)
        have h_eq : 4 * rho_prev / Real.rpow rho (1 / 2 + hierarchyLoss) =
            4 * (rho_prev / Real.rpow rho (1 / 2 + hierarchyLoss)) := by ring
        have h' : 2 * A / Real.rpow rho (1 / 2 + hierarchyLoss) ≤
            4 * (rho_prev / Real.rpow rho (1 / 2 + hierarchyLoss)) := by
          rw [← h_eq]
          exact h
        exact le_trans h' h2

      have h_first_bound : 2 * A / seg.buffer + B ≤ 20 * Real.rpow delta e := by
        calc
          2 * A / seg.buffer + B
            ≤ 16 * Real.rpow delta e + B := by linarith [h_2A_buf]
          _ ≤ 16 * Real.rpow delta e + 4 * Real.rpow delta e := by linarith [h_B_le]
          _ = 20 * Real.rpow delta e := by ring

      have h_first' : seg.firstCost ≤ 34 * Real.rpow delta e := by
        have h11 : seg.firstCost ≤ 2 * A / seg.buffer + B := h_costs.1
        have h13 : 0 ≤ Real.rpow delta e := by positivity
        exact le_trans h11 (le_trans h_first_bound (by linarith))

      have h_2A_buf2 : 2 * A / seg.buffer ^ 2 ≤ 64 * Real.rpow delta e := by
        rw [h_buf]
        have h_buf2 : (Real.sqrt rho / 4) ^ 2 = rho / 16 := by
          calc
            (Real.sqrt rho / 4) ^ 2 = (Real.sqrt rho) ^ 2 / 16 := by ring
            _ = rho / 16 := by rw [Real.sq_sqrt hrho_pos.le] <;> ring
        rw [h_buf2]
        have h1 : 2 * A / (rho / 16) = 32 * A / rho := by
          field_simp [hrho_pos.ne'] <;> ring
        rw [h1]
        have h21 : 32 * A ≤ 64 * rho_prev := by linarith [hA_le]
        have h2 : 32 * A / rho ≤ 64 * rho_prev / rho :=
          div_le_div_of_nonneg_right h21 hrho_pos.le
        have h3 : 64 * (rho_prev / rho) ≤ 64 * Real.rpow delta e :=
          mul_le_mul_of_nonneg_left h_ratio_rho (by norm_num)
        have h_eq : 64 * rho_prev / rho = 64 * (rho_prev / rho) := by ring
        have h2' : 32 * A / rho ≤ 64 * (rho_prev / rho) := by
          rw [← h_eq]
          exact h2
        exact le_trans h2' h3

      have h_B_buf : B / seg.buffer ≤ 16 * Real.rpow delta e := by
        rw [hB_def, h_buf]
        have hD_pos : 0 < Real.rpow rho (1 / 2 + hierarchyLoss) := Real.rpow_pos_of_pos hrho_pos _
        have h_mul : Real.rpow rho (1 / 2 + hierarchyLoss) * Real.sqrt rho = Real.rpow rho (1 + hierarchyLoss) := by
          have h_sqrt : Real.sqrt rho = Real.rpow rho (1 / 2 : ℝ) := by
            have h : Real.sqrt rho = rho ^ (1 / (2 : ℝ)) := Real.sqrt_eq_rpow rho
            simpa using h
          rw [h_sqrt]
          have h_add : Real.rpow rho ((1 / 2 + hierarchyLoss) + (1 / 2 : ℝ)) =
              Real.rpow rho (1 / 2 + hierarchyLoss) * Real.rpow rho (1 / 2 : ℝ) :=
            Real.rpow_add hrho_pos (1 / 2 + hierarchyLoss) (1 / 2 : ℝ)
          have h_exp : (1 / 2 + hierarchyLoss) + (1 / 2 : ℝ) = 1 + hierarchyLoss := by ring
          rw [h_exp] at h_add
          exact h_add.symm
        have h1 : (2 * A / Real.rpow rho (1 / 2 + hierarchyLoss)) / (Real.sqrt rho / 4) =
            8 * A / (Real.rpow rho (1 / 2 + hierarchyLoss) * Real.sqrt rho) := by
          field_simp [hsqrt_pos.ne', hD_pos.ne'] <;> ring
        rw [h1, h_mul]
        have h21 : 8 * A ≤ 16 * rho_prev := by linarith [hA_le]
        have h_pos1 : 0 < Real.rpow rho (1 + hierarchyLoss) := Real.rpow_pos_of_pos hrho_pos _
        have h2 : 8 * A / Real.rpow rho (1 + hierarchyLoss) ≤
            16 * rho_prev / Real.rpow rho (1 + hierarchyLoss) :=
          div_le_div_of_nonneg_right h21 h_pos1.le
        have h3 : 16 * (rho_prev / Real.rpow rho (1 + hierarchyLoss)) ≤ 16 * Real.rpow delta e :=
          mul_le_mul_of_nonneg_left h_ratio_second (by norm_num)
        have h_eq : 16 * rho_prev / Real.rpow rho (1 + hierarchyLoss) =
            16 * (rho_prev / Real.rpow rho (1 + hierarchyLoss)) := by ring
        have h2' : 8 * A / Real.rpow rho (1 + hierarchyLoss) ≤
            16 * (rho_prev / Real.rpow rho (1 + hierarchyLoss)) := by
          rw [← h_eq]
          exact h2
        exact le_trans h2' h3

      have h_second' : seg.secondCost ≤ 136 * Real.rpow delta e := by
        have h11 : seg.secondCost ≤ 2 * A / seg.buffer ^ 2 + B / seg.buffer := h_costs.2.1
        have h13 : 0 ≤ Real.rpow delta e := by positivity
        calc
          seg.secondCost
            ≤ 2 * A / seg.buffer ^ 2 + B / seg.buffer := h11
          _ ≤ 64 * Real.rpow delta e + 16 * Real.rpow delta e := by
            exact add_le_add h_2A_buf2 h_B_buf
          _ = 80 * Real.rpow delta e := by ring
          _ ≤ 136 * Real.rpow delta e := by linarith

      have h_value' : seg.valueCost ≤ 85 * Real.rpow delta e := by
        have h11 : seg.valueCost ≤ (Real.sqrt rho + 2 * seg.buffer + 1) * (2 * A / seg.buffer + B) :=
          h_costs.2.2
        have h12 : Real.sqrt rho + 2 * seg.buffer + 1 ≤ 5 / 2 := by
          rw [h_buf]
          have h13 : Real.sqrt rho ≤ 1 := h_sqrt_le_one
          linarith
        have hbuf_pos2 : 0 < seg.buffer := seg.buffer_pos
        have h14 : 0 ≤ 2 * A / seg.buffer + B := by
          have h15 : 0 ≤ 2 * A := by dsimp only [A]; positivity
          have h16 : 0 ≤ 2 * A / seg.buffer := div_nonneg h15 hbuf_pos2.le
          exact add_nonneg h16 hB_nonneg
        calc
          seg.valueCost
            ≤ (Real.sqrt rho + 2 * seg.buffer + 1) * (2 * A / seg.buffer + B) := h11
          _ ≤ (5 / 2 : ℝ) * (2 * A / seg.buffer + B) := by
            exact mul_le_mul_of_nonneg_right h12 h14
          _ ≤ (5 / 2 : ℝ) * (20 * Real.rpow delta e) := by
            exact mul_le_mul_of_nonneg_left h_first_bound (by norm_num)
          _ = 50 * Real.rpow delta e := by ring
          _ ≤ 85 * Real.rpow delta e := by linarith [Real.rpow_pos_of_pos hdelta e]

      exact ⟨h_first', h_second', h_value'⟩

  have h_final : segment.firstCost ≤ 34 * Real.rpow delta e ∧
      segment.secondCost ≤ 136 * Real.rpow delta e ∧
      segment.valueCost ≤ 85 * Real.rpow delta e := by
    rw [hsegment]
    exact h_main
  simpa [e] using h_final

/-- Construct the carrier-independent Proposition 27 correction data from an
anchored hierarchy.  The sole analytic absorption input is kept explicit. -/
theorem multiscaleSlopeCorrectionCore_of_hierarchy
    {delta hierarchyLoss : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    {sourceSlope : ℝ → ℝ}
    (hierarchy :
      WZ1Corollary26AnchoredHierarchyData
        Y sourceSlope hierarchyLoss)
    (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    (hhierarchyLoss : 0 ≤ hierarchyLoss)
    (hlevelZeroEndpoints :
      ∀ level, ∀ trapezoid ∈ hierarchy.trapezoids level,
        (level : ℕ) = 0 →
          |trapezoid.affine trapezoid.left| ≤ 4 ∧
            |trapezoid.affine trapezoid.right| ≤ 4)
    (hcostAbsorb :
      (hierarchy.levelCount : ℝ) * 136 ≤
        Real.rpow delta (-hierarchyLoss)) :
    ∃ corrections :
        WZ1MultiscaleSlopeCorrectionCoreData Y
          (1 / (hierarchy.levelCount : ℝ) + 2 * hierarchyLoss),
      ∀ z,
        wz1MultiscaleSegmentValue corrections.levelCount
            corrections.segments z =
          wz1MultiscaleSegmentValue hierarchy.levelCount
            (levelSegments hierarchy hdelta) z := by
  classical
  let rawLoss :=
    1 / (hierarchy.levelCount : ℝ) + 2 * hierarchyLoss
  let exponent :=
    -(1 / (hierarchy.levelCount : ℝ) + hierarchyLoss)
  let segments : Fin hierarchy.levelCount → Finset WZ1SegmentCorrection :=
    levelSegments hierarchy hdelta
  have hdisjoint :
      ∀ level, ∀ segment ∈ segments level,
        ∀ other ∈ segments level, segment ≠ other →
          Disjoint segment.support other.support :=
    disjoint_support_at_level hierarchy hdelta
  have hcore :
      ∀ z ∈ Set.Icc (-1 : ℝ) 1,
        (∀ level, ∀ segment ∈ segments level,
          z ∈ segment.core ∨ z ∉ segment.support) ∨
          horizontalSlice Y.union z = ∅ :=
    core_or_off_support hierarchy hdelta
  have hsurjective :
      ∀ level, ∀ segment ∈ segments level,
        ∃ trapezoid htrapezoid,
          segment =
            makeSegment hierarchy hdelta level trapezoid htrapezoid := by
    intro level segment hsegment
    change segment ∈ levelSegments hierarchy hdelta level at hsegment
    rcases Finset.mem_image.mp hsegment with ⟨trapezoid, _, heq⟩
    exact ⟨trapezoid.1, trapezoid.2, heq.symm⟩
  have hperLevel :
      ∀ level, ∀ segment ∈ segments level,
        segment.firstCost ≤ 34 * Real.rpow delta exponent ∧
          segment.secondCost ≤ 136 * Real.rpow delta exponent ∧
          segment.valueCost ≤ 85 * Real.rpow delta exponent := by
    intro level segment hsegment
    rcases hsurjective level segment hsegment with
      ⟨trapezoid, htrapezoid, rfl⟩
    exact per_level_cost_bound_of_hierarchy hierarchy
      hdelta hdelta_one hhierarchyLoss hlevelZeroEndpoints
      level trapezoid htrapezoid _ rfl
  have hatMostOne :
      ∀ level z,
        ((segments level).filter
          (fun segment => z ∈ segment.support)).card ≤ 1 := by
    intro level z
    let active := (segments level).filter
      (fun segment => z ∈ segment.support)
    by_cases hempty : active = ∅
    · simp [active, hempty]
    · rcases Finset.nonempty_iff_ne_empty.mpr hempty with ⟨first, hfirst⟩
      have hsubset : active ⊆ {first} := by
        intro other hother
        rw [Finset.mem_singleton]
        by_contra hne
        have hfirstSegment : first ∈ segments level :=
          (Finset.mem_filter.mp hfirst).1
        have hotherSegment : other ∈ segments level :=
          (Finset.mem_filter.mp hother).1
        have hzFirst : z ∈ first.support :=
          (Finset.mem_filter.mp hfirst).2
        have hzOther : z ∈ other.support :=
          (Finset.mem_filter.mp hother).2
        exact Set.disjoint_left.mp
          (hdisjoint level first hfirstSegment other hotherSegment
            (fun heq => hne heq.symm))
          hzFirst hzOther
      exact (Finset.card_le_card hsubset).trans (by simp)
  have hsumOne :
      ∀ level z (cost : WZ1SegmentCorrection → ℝ) bound,
        0 ≤ bound →
        (∀ segment ∈ segments level,
          cost segment ≤ bound * Real.rpow delta exponent) →
        ∑ segment ∈ (segments level).filter
            (fun segment => z ∈ segment.support), cost segment ≤
          bound * Real.rpow delta exponent := by
    intro level z cost bound hbound hcost
    let active := (segments level).filter
      (fun segment => z ∈ segment.support)
    have hactive : active.card ≤ 1 := by
      simpa [active] using hatMostOne level z
    by_cases hempty : active = ∅
    · simp [active, hempty, mul_nonneg hbound
        (Real.rpow_nonneg hdelta.le _)]
    · have hcard : active.card = 1 := by
        have hpos := Finset.card_pos.mpr
          (Finset.nonempty_iff_ne_empty.mpr hempty)
        omega
      rcases Finset.card_eq_one.mp hcard with ⟨segment, hsegment⟩
      have hsegmentSource : segment ∈ segments level := by
        have : segment ∈ active := by simp [hsegment]
        exact (Finset.mem_filter.mp this).1
      simpa [active, hsegment] using hcost segment hsegmentSource
  have hexponent :
      -hierarchyLoss + exponent = -rawLoss := by
    dsimp only [exponent, rawLoss]
    ring
  have hrpow :
      Real.rpow delta (-hierarchyLoss) *
          Real.rpow delta exponent =
        Real.rpow delta (-rawLoss) := by
    calc
      Real.rpow delta (-hierarchyLoss) * Real.rpow delta exponent =
          Real.rpow delta (-hierarchyLoss + exponent) :=
        (Real.rpow_add hdelta _ _).symm
      _ = Real.rpow delta (-rawLoss) := by rw [hexponent]
  have hactiveGeneric :
      ∀ (cost : WZ1SegmentCorrection → ℝ) bound,
        0 ≤ bound → bound ≤ 136 →
        (∀ level segment, segment ∈ segments level →
          cost segment ≤ bound * Real.rpow delta exponent) →
        ∀ z : ℝ,
          (∑ level : Fin hierarchy.levelCount,
            ∑ segment ∈ (segments level).filter
                (fun segment => z ∈ segment.support),
              cost segment) ≤
            Real.rpow delta (-rawLoss) := by
    intro cost bound hbound hbound136 hcost z
    calc
      (∑ level : Fin hierarchy.levelCount,
          ∑ segment ∈ (segments level).filter
              (fun segment => z ∈ segment.support), cost segment) ≤
        ∑ _level : Fin hierarchy.levelCount,
          bound * Real.rpow delta exponent := by
            apply Finset.sum_le_sum
            intro level _
            exact hsumOne level z cost bound hbound
              (fun segment hsegment => hcost level segment hsegment)
      _ = (hierarchy.levelCount : ℝ) * bound *
          Real.rpow delta exponent := by
            simp [Finset.sum_const]
            ring
      _ ≤ (hierarchy.levelCount : ℝ) * 136 *
          Real.rpow delta exponent := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hbound136 (by positivity))
              (Real.rpow_nonneg hdelta.le _)
      _ ≤ Real.rpow delta (-hierarchyLoss) *
          Real.rpow delta exponent := by
            exact mul_le_mul_of_nonneg_right hcostAbsorb
              (Real.rpow_nonneg hdelta.le _)
      _ = Real.rpow delta (-rawLoss) := hrpow
  let corrections :
      WZ1MultiscaleSlopeCorrectionCoreData Y rawLoss := {
    levelCount := hierarchy.levelCount
    levelCount_two := hierarchy.levelCount_two
    segments := segments
    disjoint_support_at_level := hdisjoint
    core_or_off_support := hcore
    active_value_cost := ?_
    active_first_cost := ?_
    active_second_cost := by
      exact hactiveGeneric (fun segment => segment.secondCost) 136
        (by norm_num) (by norm_num)
        (fun level segment hsegment =>
          (hperLevel level segment hsegment).2.1) }
  have hvalue : ∀ z,
      wz1MultiscaleSegmentValue corrections.levelCount
          corrections.segments z =
        wz1MultiscaleSegmentValue hierarchy.levelCount
          (levelSegments hierarchy hdelta) z := by
    intro z
    rfl
  exact ⟨corrections, hvalue⟩
  · exact hactiveGeneric (fun segment => segment.valueCost) 85
      (by norm_num) (by norm_num)
      (fun level segment hsegment => (hperLevel level segment hsegment).2.2)
  · exact hactiveGeneric (fun segment => segment.firstCost) 34
      (by norm_num) (by norm_num)
      (fun level segment hsegment => (hperLevel level segment hsegment).1)

/-- Compatibility wrapper for the historical dependent source package. -/
lemma per_level_cost_bound
    {delta sigma inputLoss hierarchyLoss : ℝ}
    {source : WZ1PlaninessGraininessPackage sigma inputLoss delta}
    (hierarchy : WZ1Corollary26AnchoredHierarchyPackage source hierarchyLoss)
    (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    (hhierarchyLoss : 0 ≤ hierarchyLoss)
    (level : Fin hierarchy.hierarchy.levelCount)
    (trapezoid : WZ1VerticalTrapezoid)
    (htrapezoid : trapezoid ∈ hierarchy.hierarchy.trapezoids level)
    (segment : WZ1SegmentCorrection)
    (hsegment : segment =
      makeSegment hierarchy.hierarchy hdelta level trapezoid htrapezoid) :
    segment.firstCost ≤ 34 * Real.rpow delta
        (-(1 / (hierarchy.hierarchy.levelCount : ℝ) + hierarchyLoss)) ∧
    segment.secondCost ≤ 136 * Real.rpow delta
        (-(1 / (hierarchy.hierarchy.levelCount : ℝ) + hierarchyLoss)) ∧
    segment.valueCost ≤ 85 * Real.rpow delta
        (-(1 / (hierarchy.hierarchy.levelCount : ℝ) + hierarchyLoss)) := by
  exact per_level_cost_bound_of_hierarchy hierarchy.hierarchy
    hdelta hdelta_one hhierarchyLoss
    (fun level trapezoid htrapezoid hlevel0 =>
      level0_affine_endpoint_bound
        hierarchy hdelta level trapezoid htrapezoid hlevel0)
    level trapezoid htrapezoid segment hsegment

end Kakeya.Assouad
