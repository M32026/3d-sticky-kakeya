import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PropertyPBase
import MyLeanRepo.Kakeya.Assouad.WZ1.CordobaProjectionCoveringGeometry
import MyLeanRepo.Kakeya.Assouad.WZ1.ImprovedSeparatedPoints
import MyLeanRepo.Kakeya.Assouad.WZ1.CordobaL2
import MyLeanRepo.Kakeya.Assouad.WZ1.CordobaSeparatedCardinality
import MyLeanRepo.Kakeya.Assouad.WZ1.CordobaAssemblyHelpers
import MyLeanRepo.Kakeya.Assouad.WZ1.CrossPerturbation
import MyLeanRepo.Kakeya.Assouad.WZ1.PairwiseIntersection
import MyLeanRepo.Kakeya.Assouad.WZ1.SlabContainment
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma17CordobaSlabLower

set_option maxHeartbeats 0
set_option maxRecDepth 1000

/-!
# Córdoba helper lemmas for paper tubes

Scratch work for correct implementations.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- A paper-tube piece inside a tau-ball is contained in a standard `DeltaTube (6*L)`. -/
lemma paper_tube_piece_in_delta_tube
    {L : ℝ} (hL_pos : 0 < L) (hL_small : L ≤ 1 / 1000)
    {tau : ℝ} (htau_pos : 0 < tau) (htau_sq : tau^2 ≤ 4 * L)
    (T : Kakeya.DeltaTube L) (p : Point3)
    (hp : p ∈ wz1PaperTubeCarrier T) :
    ∃ (T' : Kakeya.DeltaTube (6 * L)),
      T'.direction = T.direction ∧
      (wz1PaperTubeCarrier T ∩ Metric.closedBall p tau) ⊆ T'.carrier := by
  -- Helper: orthogonal projection onto axis line minimizes distance
  have h_projection : ∀ (x : Point3),
      ∃ (x_axis : Point3) (t_x : ℝ),
        x_axis = T.base + t_x • T.direction ∧
        dist x x_axis = Metric.infDist x (tubeAxisLine T) := by
    intro x
    let t_x : ℝ := inner ℝ (x - T.base) T.direction
    let x_axis : Point3 := T.base + t_x • T.direction
    have hx_line : x_axis ∈ tubeAxisLine T := ⟨t_x, rfl⟩
    have h_dir_norm : inner ℝ T.direction T.direction = 1 := by
      have h : inner ℝ T.direction T.direction = ‖T.direction‖ ^ 2 :=
        real_inner_self_eq_norm_sq T.direction
      rw [h, T.direction_unit] <;> norm_num
    have h_perp : inner ℝ (x - x_axis) T.direction = 0 := by
      have h1 : inner ℝ (x - x_axis) T.direction =
          inner ℝ x T.direction - inner ℝ x_axis T.direction := by
        rw [inner_sub_left]
      rw [h1]
      have h21 : x_axis = T.base + t_x • T.direction := by rfl
      have h2 : inner ℝ x_axis T.direction =
          inner ℝ T.base T.direction + t_x * inner ℝ T.direction T.direction := by
        rw [h21]
        have h22 : inner ℝ (T.base + t_x • T.direction) T.direction =
            inner ℝ T.base T.direction + inner ℝ (t_x • T.direction) T.direction := by
          rw [inner_add_left]
        rw [h22]
        have h23 : inner ℝ (t_x • T.direction) T.direction =
            t_x * inner ℝ T.direction T.direction := by
          simp [inner_smul_left]
        rw [h23] <;> ring
      rw [h2, h_dir_norm]
      have h3 : t_x = inner ℝ (x - T.base) T.direction := by rfl
      rw [h3]
      have h4 : inner ℝ (x - T.base) T.direction =
          inner ℝ x T.direction - inner ℝ T.base T.direction := by
        rw [inner_sub_left]
      rw [h4] <;> ring
    have h_min : ∀ (y : Point3), y ∈ tubeAxisLine T → dist x x_axis ≤ dist x y := by
      intro y hy
      rcases hy with ⟨s, hs⟩
      have h_eq : y = T.base + s • T.direction := hs
      rw [h_eq]
      have h5 : x - (T.base + s • T.direction) =
          (x - x_axis) + (t_x - s) • T.direction := by
        have h51 : x_axis = T.base + t_x • T.direction := by rfl
        rw [h51]
        ext i
        simp [sub_smul, add_smul] <;> ring
      have h6 : inner ℝ (x - x_axis) ((t_x - s) • T.direction) = 0 := by
        have h61 : inner ℝ ((t_x - s) • T.direction) (x - x_axis) =
            (t_x - s) * inner ℝ T.direction (x - x_axis) := by
          simp [inner_smul_left]
        have h63 : inner ℝ (x - x_axis) ((t_x - s) • T.direction) =
            inner ℝ ((t_x - s) • T.direction) (x - x_axis) :=
          real_inner_comm _ _
        rw [h63, h61]
        have h64 : inner ℝ T.direction (x - x_axis) =
            inner ℝ (x - x_axis) T.direction :=
          real_inner_comm _ _
        rw [h64, h_perp] <;> ring
      have h7 : ‖x - (T.base + s • T.direction)‖^2 =
          ‖x - x_axis‖^2 + (t_x - s)^2 := by
        rw [h5]
        have h8 := norm_add_sq_real (x - x_axis) ((t_x - s) • T.direction)
        rw [h8, h6]
        have h91 : ‖(t_x - s) • T.direction‖ = |t_x - s| * ‖T.direction‖ := by
          have h := norm_smul (t_x - s) T.direction
          have h' : ‖(t_x - s)‖ = |t_x - s| := by simp
          rw [h, h'] <;> ring
        have h9 : ‖(t_x - s) • T.direction‖^2 = (t_x - s)^2 := by
          rw [h91, T.direction_unit]
          have h92 : |t_x - s| * (1 : ℝ) = |t_x - s| := by ring
          rw [h92, sq_abs]
        rw [h9] <;> ring
      have h10 : ‖x - x_axis‖^2 ≤ ‖x - (T.base + s • T.direction)‖^2 := by
        rw [h7] <;> exact le_add_of_nonneg_right (sq_nonneg _)
      have h11 : 0 ≤ ‖x - x_axis‖ := by positivity
      have h12 : 0 ≤ ‖x - (T.base + s • T.direction)‖ := by positivity
      have h13 : ‖x - x_axis‖ ≤ ‖x - (T.base + s • T.direction)‖ := by
        exact (sq_le_sq₀ h11 h12).mp h10
      simpa [dist_eq_norm] using h13
    have h_infdist_le : Metric.infDist x (tubeAxisLine T) ≤ dist x x_axis :=
      Metric.infDist_le_dist_of_mem hx_line
    have h_le_infdist : dist x x_axis ≤ Metric.infDist x (tubeAxisLine T) := by
      rw [Metric.infDist_eq_iInf]
      have h_nonempty : Nonempty {y // y ∈ tubeAxisLine T} :=
        ⟨⟨x_axis, hx_line⟩⟩
      exact le_ciInf (fun y => h_min y y.prop)
    have h_eq : dist x x_axis = Metric.infDist x (tubeAxisLine T) := by
      linarith
    exact ⟨x_axis, t_x, by rfl, h_eq⟩

  set a : ℝ := tau + 12 * L with ha_def
  have ha_pos : 0 < a := by positivity
  have h2a_le_one : 2 * a ≤ 1 := by
    have htau_le : tau ≤ 2 * Real.sqrt L := by
      nlinarith [Real.sqrt_nonneg L, Real.sq_sqrt (show 0 ≤ L by linarith)]
    have hsqrt_small : Real.sqrt L ≤ 1 / 30 := by
      have h1 : Real.sqrt L ≤ Real.sqrt (1 / 1000) := Real.sqrt_le_sqrt (by linarith)
      have h2 : Real.sqrt (1 / 1000) ≤ 1 / 30 := by
        rw [Real.sqrt_le_left] <;> norm_num
      linarith
    nlinarith

  -- Get projection of p
  rcases h_projection p with ⟨q_axis, t_p, hq_eq_def, hq_eq⟩
  have hp_dist : dist p q_axis ≤ 6 * L := by
    have h1 : p ∈ Metric.cthickening (6 * L) (tubeAxisLine T) := hp.1
    have h2 : Metric.infEDist p (tubeAxisLine T) ≤ ENNReal.ofReal (6 * L) :=
      (Metric.mem_cthickening_iff).mp h1
    have h_nonempty : Set.Nonempty (tubeAxisLine T) :=
      ⟨T.base, ⟨0, by simp⟩⟩
    have h_ne_top : Metric.infEDist p (tubeAxisLine T) ≠ ⊤ :=
      Metric.infEDist_ne_top h_nonempty
    have h_eq : Metric.infEDist p (tubeAxisLine T) =
        ENNReal.ofReal (Metric.infDist p (tubeAxisLine T)) := by
      have h5 : (Metric.infEDist p (tubeAxisLine T)).toReal =
          Metric.infDist p (tubeAxisLine T) := by rfl
      rw [← h5, ENNReal.ofReal_toReal h_ne_top]
    rw [h_eq] at h2
    have h_infdist : Metric.infDist p (tubeAxisLine T) ≤ 6 * L :=
      (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h2
    have h : dist p q_axis = Metric.infDist p (tubeAxisLine T) := hq_eq
    rw [h]
    exact h_infdist

  let T' : Kakeya.DeltaTube (6 * L) :=
    { base := q_axis - a • T.direction
      direction := T.direction
      direction_unit := T.direction_unit }

  refine ⟨T', rfl, ?_⟩
  intro x hx
  have hx_paper : x ∈ wz1PaperTubeCarrier T := hx.1
  have hx_ball : dist x p ≤ tau := hx.2

  rcases h_projection x with ⟨x_axis, t_x, hx_eq_def, hx_eq⟩
  have hx_dist : dist x x_axis ≤ 6 * L := by
    have h1 : x ∈ Metric.cthickening (6 * L) (tubeAxisLine T) := hx_paper.1
    have h2 : Metric.infEDist x (tubeAxisLine T) ≤ ENNReal.ofReal (6 * L) :=
      (Metric.mem_cthickening_iff).mp h1
    have h_nonempty : Set.Nonempty (tubeAxisLine T) :=
      ⟨T.base, ⟨0, by simp⟩⟩
    have h_ne_top : Metric.infEDist x (tubeAxisLine T) ≠ ⊤ :=
      Metric.infEDist_ne_top h_nonempty
    have h_eq : Metric.infEDist x (tubeAxisLine T) =
        ENNReal.ofReal (Metric.infDist x (tubeAxisLine T)) := by
      have h5 : (Metric.infEDist x (tubeAxisLine T)).toReal =
          Metric.infDist x (tubeAxisLine T) := by rfl
      rw [← h5, ENNReal.ofReal_toReal h_ne_top]
    rw [h_eq] at h2
    have h_infdist : Metric.infDist x (tubeAxisLine T) ≤ 6 * L :=
      (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h2
    have h : dist x x_axis = Metric.infDist x (tubeAxisLine T) := hx_eq
    rw [h]
    exact h_infdist

  have h_axis_dist : dist x_axis q_axis ≤ tau + 12 * L := by
    have h1 : dist x_axis q_axis ≤ dist x_axis x + dist x p + dist p q_axis :=
      dist_triangle4 _ _ _ _
    have h2 : dist x_axis x = dist x x_axis := dist_comm _ _
    rw [h2] at h1
    linarith [hx_dist, hx_ball, hp_dist]

  have h_diff : x_axis - q_axis = (t_x - t_p) • T.direction := by
    rw [hx_eq_def, hq_eq_def]
    ext i
    simp [sub_smul, add_smul] <;> ring
  have h_dist_eq : dist x_axis q_axis = |t_x - t_p| := by
    have h : ‖x_axis - q_axis‖ = |t_x - t_p| := by
      have h91 : ‖(t_x - t_p) • T.direction‖ = ‖(t_x - t_p)‖ * ‖T.direction‖ := norm_smul _ _
      have h92 : ‖(t_x - t_p)‖ = |t_x - t_p| := by simp
      calc
        ‖x_axis - q_axis‖ = ‖(t_x - t_p) • T.direction‖ := by rw [h_diff]
        _ = ‖(t_x - t_p)‖ * ‖T.direction‖ := h91
        _ = |t_x - t_p| * ‖T.direction‖ := by rw [h92]
        _ = |t_x - t_p| := by rw [T.direction_unit] <;> ring
    simpa [dist_eq_norm] using h
  have h_s_range : |t_x - t_p| ≤ tau + 12 * L := by
    rw [← h_dist_eq]
    exact h_axis_dist

  have h_s_in_Icc : t_x - t_p + a ∈ Set.Icc (0 : ℝ) 1 := by
    have h1 : 0 ≤ t_x - t_p + a := by
      have h2 : -(tau + 12 * L) ≤ t_x - t_p := (abs_le.mp h_s_range).1
      linarith
    have h3 : t_x - t_p + a ≤ 1 := by
      have h4 : t_x - t_p ≤ tau + 12 * L := (abs_le.mp h_s_range).2
      linarith [h2a_le_one]
    exact ⟨h1, h3⟩

  have h_x_axis_in_seg : x_axis ∈ Kakeya.unitSegment T'.base T'.direction := by
    refine ⟨t_x - t_p + a, h_s_in_Icc, ?_⟩
    have h_base_eq : T'.base = q_axis - a • T.direction := by rfl
    rw [h_base_eq, hx_eq_def, hq_eq_def]
    simp [Kakeya.unitSegment, sub_smul, add_smul] <;> abel

  have h_infdist_seg : Metric.infDist x (Kakeya.unitSegment T'.base T'.direction) ≤ dist x x_axis :=
    Metric.infDist_le_dist_of_mem h_x_axis_in_seg
  have h' : Metric.infDist x (Kakeya.unitSegment T'.base T'.direction) ≤ 6 * L := by
    linarith [hx_dist]
  have h_seg_nonempty : Set.Nonempty (Kakeya.unitSegment T'.base T'.direction) := by
    refine ⟨T'.base, ?_⟩
    exact ⟨0, by norm_num, by simp⟩
  have h_ne_top : Metric.infEDist x (Kakeya.unitSegment T'.base T'.direction) ≠ ⊤ :=
    Metric.infEDist_ne_top h_seg_nonempty
  have h_eq : Metric.infEDist x (Kakeya.unitSegment T'.base T'.direction) =
      ENNReal.ofReal (Metric.infDist x (Kakeya.unitSegment T'.base T'.direction)) := by
    have h5 : (Metric.infEDist x (Kakeya.unitSegment T'.base T'.direction)).toReal =
        Metric.infDist x (Kakeya.unitSegment T'.base T'.direction) := by rfl
    rw [← h5, ENNReal.ofReal_toReal h_ne_top]
  have h_edist : Metric.infEDist x (Kakeya.unitSegment T'.base T'.direction) ≤
      ENNReal.ofReal (6 * L) := by
    rw [h_eq]
    exact ENNReal.ofReal_le_ofReal h'
  exact (Metric.mem_cthickening_iff).mpr h_edist

/-- Perpendicular component bound for two points in a tube. -/
lemma tube_two_point_perp_bound {δ : ℝ} (hδ_pos : 0 < δ)
    (T : Kakeya.DeltaTube δ) (u : Point3) (hu_unit : ‖u‖ = 1)
    (hT_dir : T.direction = u) (x y : Point3)
    (hx_in : x ∈ T.carrier) (hy_in : y ∈ T.carrier) :
    ‖y - x - (inner ℝ (y - x) u) • u‖ ≤ 2 * δ := by
  let proj_x : Point3 := T.base + inner ℝ (x - T.base) T.direction • T.direction
  let proj_y : Point3 := T.base + inner ℝ (y - T.base) T.direction • T.direction
  have h_perp_x : ‖x - proj_x‖ ≤ δ := tube_perp_bound hδ_pos T x hx_in
  have h_perp_y : ‖y - proj_y‖ ≤ δ := tube_perp_bound hδ_pos T y hy_in
  have h_proj_diff : proj_y - proj_x = (inner ℝ (y - x) u) • u := by
    have h1 : proj_y - proj_x =
        (inner ℝ (y - T.base) T.direction - inner ℝ (x - T.base) T.direction) • T.direction := by
      dsimp only [proj_y, proj_x]
      rw [sub_smul] <;> abel
    rw [h1]
    have h2 : inner ℝ (y - T.base) T.direction - inner ℝ (x - T.base) T.direction =
        inner ℝ (y - x) T.direction := by
      have h : inner ℝ (y - T.base) T.direction - inner ℝ (x - T.base) T.direction =
          inner ℝ ((y - T.base) - (x - T.base)) T.direction := by
        rw [← inner_sub_left]
      rw [h]
      have h' : (y - T.base) - (x - T.base) = y - x := by abel
      rw [h']
    rw [h2, hT_dir]
  have h3 : y - x - (inner ℝ (y - x) u) • u = (y - proj_y) - (x - proj_x) := by
    rw [← h_proj_diff] <;> abel
  rw [h3]
  calc ‖(y - proj_y) - (x - proj_x)‖ ≤ ‖y - proj_y‖ + ‖x - proj_x‖ := norm_sub_le _ _
    _ ≤ δ + δ := by gcongr
    _ = 2 * δ := by ring

/-!
## Córdoba arithmetic for paper tubes (6L-thick carriers)

Adapts `cordoba_final_arithmetic_C504` to constants V' = 288·L²·τ,
C = 18144·L²·τ, k ≥ 5/864 · L^(2ε₁-1+ε₃) · τ.
-/

/-- Final arithmetic for paper-tube Córdoba constants. -/
lemma cordoba_final_arithmetic_paper
    {L tau epsilon₁ epsilon₃ : ℝ}
    {k : ℕ}
    (hL_pos : 0 < L)
    (hL_one : L ≤ 1)
    (htau_pos : 0 < tau)
    (heps₁_pos : 0 < epsilon₁)
    (heps₃_pos : 0 < epsilon₃)
    (hk_pos : 0 < k)
    (hk_lower : (k : ℝ) ≥ (5 : ℝ) / 864 * Real.rpow L (2 * epsilon₁ - 1 + epsilon₃) * tau)
    (h_log : Real.rpow L epsilon₁ *
        (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108) :
    ENNReal.ofReal ((k : ℝ)^2 * (Real.rpow L (2 + 2 * epsilon₁) * tau)^2) /
    ENNReal.ofReal ((k : ℝ) * (288 * L^2 * tau) +
      2 * (28224 * L^2 * tau) * (k : ℝ) * (1 + Real.log (k : ℝ))) ≥
    Kakeya.realRpowENN L (1 + 7 * epsilon₁ + epsilon₃) *
      ENNReal.ofReal (tau^2 / 200) := by
  set kR : ℝ := (k : ℝ) with hkR
  have hkR_pos : 0 < kR := Nat.cast_pos.mpr hk_pos
  have hkR_one : 1 ≤ kR := by
    have h1 : 1 ≤ k := hk_pos
    have h2 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast h1
    simpa [hkR] using h2
  have hlog_nonneg : 0 ≤ Real.log kR := Real.log_nonneg hkR_one
  set V : ℝ := Real.rpow L (2 + 2 * epsilon₁) * tau with hV
  set V' : ℝ := 288 * L^2 * tau with hV'
  set C : ℝ := 28224 * L^2 * tau with hC
  have hV_pos : 0 < V := mul_pos (Real.rpow_pos_of_pos hL_pos _) htau_pos
  have hV'_pos : 0 < V' := by dsimp only [V']; positivity
  have hC_pos : 0 < C := by rw [hC] <;> positivity
  set D : ℝ := kR * V' + 2 * C * kR * (1 + Real.log kR) with hD
  have hD_pos : 0 < D := by positivity
  have h_rpow_div : ∀ (a b : ℝ),
      Real.rpow L a / Real.rpow L b = Real.rpow L (a - b) := by
    intro a b
    have h_pos_b : 0 < Real.rpow L b := Real.rpow_pos_of_pos hL_pos _
    have h_add : Real.rpow L ((a - b) + b) =
        Real.rpow L (a - b) * Real.rpow L b := Real.rpow_add hL_pos (a - b) b
    have h_eq : (a - b) + b = a := by ring
    have h9 : Real.rpow L a = Real.rpow L (a - b) * Real.rpow L b := by
      have h10 : Real.rpow L ((a - b) + b) = Real.rpow L a := by rw [h_eq]
      exact h10.symm.trans h_add
    rw [h9] <;> field_simp [h_pos_b.ne'] <;> ring
  have h_rpow_mul : ∀ (a b : ℝ),
      Real.rpow L a * Real.rpow L b = Real.rpow L (a + b) := by
    intro a b; exact (Real.rpow_add hL_pos a b).symm
  have hD_factor : D = kR * L^2 * tau * (288 + 56448 * (1 + Real.log kR)) := by
    dsimp only [D, V', C] <;> ring
  have h_bracket : 288 + 56448 * (1 + Real.log kR) ≤
      (125 / 108 : ℝ) / Real.rpow L epsilon₁ := by
    have h_rpos : 0 < Real.rpow L epsilon₁ := Real.rpow_pos_of_pos hL_pos _
    calc
      288 + 56448 * (1 + Real.log kR)
        = (Real.rpow L epsilon₁ * (288 + 56448 * (1 + Real.log kR))) / Real.rpow L epsilon₁ := by
          field_simp [h_rpos.ne'] <;> ring
      _ ≤ (125 / 108 : ℝ) / Real.rpow L epsilon₁ := by
          exact div_le_div_of_nonneg_right h_log h_rpos.le
  have h_exp2 : L^2 = Real.rpow L 2 := by simp
  have hD_le : D ≤ kR * (125 / 108 : ℝ) * Real.rpow L (2 - epsilon₁) * tau := by
    have hpos : 0 ≤ kR * Real.rpow L 2 * tau := by
      exact mul_nonneg (mul_nonneg hkR_pos.le (Real.rpow_pos_of_pos hL_pos _).le) htau_pos.le
    have h_goal : kR * L^2 * tau * (288 + 56448 * (1 + Real.log kR)) ≤
        kR * (125 / 108 : ℝ) * Real.rpow L (2 - epsilon₁) * tau := by
      calc
        kR * L^2 * tau * (288 + 56448 * (1 + Real.log kR))
          = kR * Real.rpow L 2 * tau * (288 + 56448 * (1 + Real.log kR)) := by rw [h_exp2]
        _ ≤ kR * Real.rpow L 2 * tau * ((125 / 108 : ℝ) / Real.rpow L epsilon₁) := by
            exact mul_le_mul_of_nonneg_left h_bracket hpos
        _ = kR * (125 / 108 : ℝ) * (Real.rpow L 2 / Real.rpow L epsilon₁) * tau := by ring
        _ = kR * (125 / 108 : ℝ) * Real.rpow L (2 - epsilon₁) * tau := by
            rw [h_rpow_div 2 epsilon₁] <;> ring
    rw [hD_factor]; exact h_goal
  set N : ℝ := kR^2 * V^2 with hN
  have hN_pos : 0 < N := by positivity
  have hV2 : V^2 = Real.rpow L (4 + 4 * epsilon₁) * tau^2 := by
    rw [hV]
    have h1 : (Real.rpow L (2 + 2 * epsilon₁) * tau)^2 =
        (Real.rpow L (2 + 2 * epsilon₁))^2 * tau^2 := by ring
    rw [h1]
    have h_sq : (Real.rpow L (2 + 2 * epsilon₁))^2 =
        Real.rpow L (2 + 2 * epsilon₁) * Real.rpow L (2 + 2 * epsilon₁) := by ring
    rw [h_sq, h_rpow_mul (2 + 2 * epsilon₁) (2 + 2 * epsilon₁)] <;> ring
  have h_k_term : kR ≥ (5 : ℝ) / 864 * Real.rpow L (2 * epsilon₁ - 1 + epsilon₃) * tau := hk_lower
  have h_part1 : kR * V^2 / D ≥
      (108 : ℝ) / 125 * Real.rpow L (2 + 5 * epsilon₁) * tau := by
    rw [hV2]
    have h_num_pos : 0 < kR * (Real.rpow L (4 + 4 * epsilon₁) * tau^2) :=
      mul_pos hkR_pos (mul_pos (Real.rpow_pos_of_pos hL_pos _) (pow_pos htau_pos 2))
    have h_rpow2me1_pos : 0 < Real.rpow L (2 - epsilon₁) := Real.rpow_pos_of_pos hL_pos _
    have h_denom'_pos : 0 < kR * (125 / 108 : ℝ) * Real.rpow L (2 - epsilon₁) * tau :=
      mul_pos (mul_pos (mul_pos hkR_pos (by norm_num)) (Real.rpow_pos_of_pos hL_pos _)) htau_pos
    calc
      kR * (Real.rpow L (4 + 4 * epsilon₁) * tau^2) / D
        ≥ kR * (Real.rpow L (4 + 4 * epsilon₁) * tau^2) /
            (kR * (125 / 108 : ℝ) * Real.rpow L (2 - epsilon₁) * tau) := by
          exact div_le_div_of_nonneg_left h_num_pos.le hD_pos hD_le
      _ = (Real.rpow L (4 + 4 * epsilon₁) * tau^2) /
            ((125 / 108 : ℝ) * Real.rpow L (2 - epsilon₁) * tau) := by
          field_simp [hkR_pos.ne'] <;> ring
      _ = (108 : ℝ) / 125 * (Real.rpow L (4 + 4 * epsilon₁) / Real.rpow L (2 - epsilon₁)) * tau := by
          field_simp [h_rpow2me1_pos.ne'] <;> ring
      _ = (108 : ℝ) / 125 * Real.rpow L ((4 + 4 * epsilon₁) - (2 - epsilon₁)) * tau := by
          rw [h_rpow_div (4 + 4 * epsilon₁) (2 - epsilon₁)] <;> ring
      _ = (108 : ℝ) / 125 * Real.rpow L (2 + 5 * epsilon₁) * tau := by
          have h_exp : (4 + 4 * epsilon₁) - (2 - epsilon₁) = 2 + 5 * epsilon₁ := by ring
          rw [h_exp] <;> ring
  have h_main : N / D ≥
      (5 : ℝ) / 864 * Real.rpow L (2 * epsilon₁ - 1 + epsilon₃) * tau *
        ((108 : ℝ) / 125 * Real.rpow L (2 + 5 * epsilon₁) * tau) := by
    have hN2 : N = kR * (kR * V^2) := by ring
    rw [hN2]
    have h1 : kR * (kR * V^2) / D = kR * (kR * V^2 / D) := by
      field_simp [hD_pos.ne'] <;> ring
    rw [h1]
    have h2 : kR * (kR * V^2 / D) ≥
        kR * ((108 : ℝ) / 125 * Real.rpow L (2 + 5 * epsilon₁) * tau) := by
      exact mul_le_mul_of_nonneg_left h_part1 hkR_pos.le
    have h3 : kR * ((108 : ℝ) / 125 * Real.rpow L (2 + 5 * epsilon₁) * tau) ≥
        (5 : ℝ) / 864 * Real.rpow L (2 * epsilon₁ - 1 + epsilon₃) * tau *
          ((108 : ℝ) / 125 * Real.rpow L (2 + 5 * epsilon₁) * tau) := by
      have h41 : 0 ≤ (108 : ℝ) / 125 := by norm_num
      have h42 : 0 < Real.rpow L (2 + 5 * epsilon₁) := Real.rpow_pos_of_pos hL_pos _
      have h4 : 0 ≤ (108 : ℝ) / 125 * Real.rpow L (2 + 5 * epsilon₁) * tau := by
        exact mul_nonneg (mul_nonneg h41 h42.le) htau_pos.le
      exact mul_le_mul_of_nonneg_right h_k_term h4
    exact calc
      kR * (kR * V^2 / D)
        ≥ kR * ((108 : ℝ) / 125 * Real.rpow L (2 + 5 * epsilon₁) * tau) := h2
      _ ≥ (5 : ℝ) / 864 * Real.rpow L (2 * epsilon₁ - 1 + epsilon₃) * tau *
            ((108 : ℝ) / 125 * Real.rpow L (2 + 5 * epsilon₁) * tau) := h3
  have h_ratio : N / D ≥ Real.rpow L (1 + 7 * epsilon₁ + epsilon₃) * tau^2 / 200 := by
    have h_exp_eq : (2 * epsilon₁ - 1 + epsilon₃) + (2 + 5 * epsilon₁) = 1 + 7 * epsilon₁ + epsilon₃ := by ring
    have h_exp_final : Real.rpow L (2 * epsilon₁ - 1 + epsilon₃) * Real.rpow L (2 + 5 * epsilon₁) =
        Real.rpow L (1 + 7 * epsilon₁ + epsilon₃) := by
      rw [h_rpow_mul (2 * epsilon₁ - 1 + epsilon₃) (2 + 5 * epsilon₁)]
      rw [h_exp_eq]
    have h_rhs_rearrange : (5 : ℝ) / 864 * Real.rpow L (2 * epsilon₁ - 1 + epsilon₃) * tau *
          ((108 : ℝ) / 125 * Real.rpow L (2 + 5 * epsilon₁) * tau) =
        ((5 : ℝ) / 864 * (108 : ℝ) / 125) *
          (Real.rpow L (2 * epsilon₁ - 1 + epsilon₃) * Real.rpow L (2 + 5 * epsilon₁)) * tau^2 := by
      ring
    calc
      N / D
        ≥ (5 : ℝ) / 864 * Real.rpow L (2 * epsilon₁ - 1 + epsilon₃) * tau *
              ((108 : ℝ) / 125 * Real.rpow L (2 + 5 * epsilon₁) * tau) := h_main
      _ = ((5 : ℝ) / 864 * (108 : ℝ) / 125) *
            (Real.rpow L (2 * epsilon₁ - 1 + epsilon₃) * Real.rpow L (2 + 5 * epsilon₁)) * tau^2 := h_rhs_rearrange
      _ = ((5 : ℝ) / 864 * (108 : ℝ) / 125) *
            Real.rpow L (1 + 7 * epsilon₁ + epsilon₃) * tau^2 := by rw [h_exp_final]
      _ = Real.rpow L (1 + 7 * epsilon₁ + epsilon₃) * tau^2 / 200 := by norm_num <;> ring
  have hN_nonneg : 0 ≤ N := hN_pos.le
  have hND_nonneg : 0 ≤ N / D := by positivity
  have h_mul : ENNReal.ofReal (N / D) * ENNReal.ofReal D = ENNReal.ofReal N := by
    have h3 : (N / D) * D = N := by field_simp [hD_pos.ne'] <;> ring
    have h4 : ENNReal.ofReal ((N / D) * D) = ENNReal.ofReal (N / D) * ENNReal.ofReal D := by
      rw [ENNReal.ofReal_mul hND_nonneg] <;> rfl
    rw [← h4, h3]
  have h_ennreal_div : ENNReal.ofReal N / ENNReal.ofReal D = ENNReal.ofReal (N / D) := by
    have hD_pos' : 0 < D := hD_pos
    have hN_nonneg' : 0 ≤ N := hN_nonneg
    have h_ne_zero : ENNReal.ofReal D ≠ 0 := by positivity
    have h_ne_top : ENNReal.ofReal D ≠ ⊤ := ENNReal.ofReal_lt_top.ne
    have h_eq : ENNReal.ofReal N = ENNReal.ofReal (N / D) * ENNReal.ofReal D := h_mul.symm
    rw [h_eq]
    have h2 : (ENNReal.ofReal (N / D) * ENNReal.ofReal D) / ENNReal.ofReal D =
        ENNReal.ofReal (N / D) := by
      rw [mul_div_assoc]
      have h3 : ENNReal.ofReal D / ENNReal.ofReal D = 1 := by
        exact ENNReal.div_self h_ne_zero h_ne_top
      rw [h3, mul_one]
    exact h2
  rw [h_ennreal_div]
  have h_rpow_nonneg : 0 ≤ Real.rpow L (1 + 7 * epsilon₁ + epsilon₃) := by
    exact Real.rpow_nonneg hL_pos.le _
  have h_final2 : ENNReal.ofReal (Real.rpow L (1 + 7 * epsilon₁ + epsilon₃) * tau^2 / 200) =
      Kakeya.realRpowENN L (1 + 7 * epsilon₁ + epsilon₃) * ENNReal.ofReal (tau^2 / 200) := by
    simp only [Kakeya.realRpowENN]
    have h_eq : Real.rpow L (1 + 7 * epsilon₁ + epsilon₃) * tau^2 / 200 =
        Real.rpow L (1 + 7 * epsilon₁ + epsilon₃) * (tau^2 / 200) := by ring
    rw [h_eq]
    rw [ENNReal.ofReal_mul h_rpow_nonneg] <;> rfl
  have h_final1 : ENNReal.ofReal (N / D) ≥
      ENNReal.ofReal (Real.rpow L (1 + 7 * epsilon₁ + epsilon₃) * tau^2 / 200) :=
    ENNReal.ofReal_le_ofReal h_ratio
  rw [h_final2] at h_final1
  exact h_final1

/--
Weakened angle-from-separated-intersections lemma for paper tubes.

Requires only `d * alpha ≥ 8 * rho` (instead of `12 * rho`) and gives
`‖cross‖ ≥ d * alpha / (4 * tau)` (instead of `/ (2 * tau)`).
Used when `alpha * sep_scale < rho` (paper-tube thickness is 6L but
transversality scale is L^epsilon₃).
-/
lemma angle_from_separated_intersections_weak
    {rho tau d alpha : ℝ}
    (hrho_pos : 0 < rho) (htau_pos : 0 < tau)
    (halpha_pos : 0 < alpha) (hd_pos : 0 < d)
    (u v_j v_k : Point3)
    (hu_unit : ‖u‖ = 1) (hvj_unit : ‖v_j‖ = 1) (hvk_unit : ‖v_k‖ = 1)
    (p_j p_k x : Point3) (e_j e_k : Point3) (s_j s_k : ℝ)
    (h_sep : ‖p_k - p_j - d • u‖ ≤ 2 * rho)
    (hx_j : x = p_j + s_j • v_j + e_j)
    (hx_k : x = p_k + s_k • v_k + e_k)
    (hej_norm : ‖e_j‖ ≤ 2 * rho) (hek_norm : ‖e_k‖ ≤ 2 * rho)
    (hsj_bound : |s_j| ≤ tau) (hsk_bound : |s_k| ≤ tau)
    (h_trans_j : ‖wz1Cross u v_j‖ ≥ alpha)
    (h_trans_k : ‖wz1Cross u v_k‖ ≥ alpha)
    (h_large : d * alpha ≥ 8 * rho) :
    ‖wz1Cross v_j v_k‖ ≥ d * alpha / (4 * tau) := by
  have h_vec_eq : p_j + s_j • v_j + e_j = p_k + s_k • v_k + e_k := by
    rw [←hx_j, hx_k]
  have h_eq1 : s_j • v_j - s_k • v_k = (p_k - p_j) + (e_k - e_j) := by
    calc
      s_j • v_j - s_k • v_k
        = (p_j + s_j • v_j + e_j) - (p_k + s_k • v_k + e_k) + (p_k - p_j) + (e_k - e_j) := by abel
      _ = (p_k - p_j) + (e_k - e_j) := by rw [h_vec_eq] <;> abel
  set w : Point3 := p_k - p_j - d • u with hw_def
  have hw_norm : ‖w‖ ≤ 2 * rho := h_sep
  have h_pk_pj : p_k - p_j = d • u + w := by
    simp [hw_def] <;> abel
  set E : Point3 := w + (e_k - e_j) with hE_def
  have h_main_eq : s_j • v_j - s_k • v_k = d • u + E := by
    rw [h_eq1, h_pk_pj, hE_def] <;> abel
  have hE_norm : ‖E‖ ≤ 6 * rho := by
    calc
      ‖E‖ ≤ ‖w‖ + ‖e_k - e_j‖ := by simpa [hE_def] using norm_add_le _ _
      _ ≤ ‖w‖ + ‖e_k‖ + ‖e_j‖ := by
        have h : ‖e_k - e_j‖ ≤ ‖e_k‖ + ‖e_j‖ := norm_sub_le _ _
        linarith
      _ ≤ 2 * rho + 2 * rho + 2 * rho := by gcongr <;> linarith
      _ = 6 * rho := by ring
  have h_cross_eq : wz1Cross v_j (s_j • v_j - s_k • v_k) = wz1Cross v_j (d • u + E) := by
    rw [h_main_eq]
  have h_left : wz1Cross v_j (s_j • v_j - s_k • v_k) = -s_k • wz1Cross v_j v_k := by
    have h1 : wz1Cross v_j (s_j • v_j - s_k • v_k) =
        wz1Cross v_j (s_j • v_j) - wz1Cross v_j (s_k • v_k) := by
      have h_sub : s_j • v_j - s_k • v_k = s_j • v_j + -(s_k • v_k) := by
        exact sub_eq_add_neg (s_j • v_j) (s_k • v_k)
      rw [h_sub]
      have h_add : wz1Cross v_j (s_j • v_j + -(s_k • v_k)) =
          wz1Cross v_j (s_j • v_j) + wz1Cross v_j (-(s_k • v_k)) :=
        wz1Cross_add_right v_j (s_j • v_j) (-(s_k • v_k))
      rw [h_add]
      have h_neg : wz1Cross v_j (-(s_k • v_k)) = -wz1Cross v_j (s_k • v_k) := by
        have h5 : -(s_k • v_k) = (-s_k) • v_k := by simp
        rw [h5]
        have h6 : wz1Cross v_j ((-s_k) • v_k) = (-s_k) • wz1Cross v_j v_k :=
          wz1Cross_smul_right (-s_k) v_j v_k
        rw [h6]
        have h7 : (-s_k) • wz1Cross v_j v_k = -(s_k • wz1Cross v_j v_k) := by simp
        rw [h7]
        have h8 : s_k • wz1Cross v_j v_k = wz1Cross v_j (s_k • v_k) :=
          (wz1Cross_smul_right s_k v_j v_k).symm
        rw [h8]
      rw [h_neg] <;> abel
    rw [h1]
    have h2 : wz1Cross v_j (s_j • v_j) = s_j • wz1Cross v_j v_j := wz1Cross_smul_right s_j v_j v_j
    rw [h2, wz1Cross_self v_j]
    have h4 : wz1Cross v_j (s_k • v_k) = s_k • wz1Cross v_j v_k := wz1Cross_smul_right s_k v_j v_k
    rw [h4] <;> simp
  have h_right : wz1Cross v_j (d • u + E) =
      d • wz1Cross v_j u + wz1Cross v_j E := by
    have h_add : wz1Cross v_j (d • u + E) =
        wz1Cross v_j (d • u) + wz1Cross v_j E := wz1Cross_add_right v_j (d • u) E
    rw [h_add]
    have h_smul : wz1Cross v_j (d • u) = d • wz1Cross v_j u :=
      wz1Cross_smul_right d v_j u
    rw [h_smul]
  have h_eq2 : -s_k • wz1Cross v_j v_k = d • wz1Cross v_j u + wz1Cross v_j E := by
    rw [h_left, h_right] at h_cross_eq
    exact h_cross_eq
  have h_anticomm : wz1Cross v_j u = -wz1Cross u v_j := wz1Cross_anticomm v_j u
  rw [h_anticomm] at h_eq2
  have h_eq3 : -s_k • wz1Cross v_j v_k = -d • wz1Cross u v_j + wz1Cross v_j E := by
    simpa [smul_neg] using h_eq2
  have h_final : s_k • wz1Cross v_j v_k = d • wz1Cross u v_j - wz1Cross v_j E := by
    have h' : -(s_k • wz1Cross v_j v_k) = -(d • wz1Cross u v_j) + wz1Cross v_j E := by
      simpa [neg_smul] using h_eq3
    calc
      s_k • wz1Cross v_j v_k
        = -(-(s_k • wz1Cross v_j v_k)) := by simp
      _ = -(-(d • wz1Cross u v_j) + wz1Cross v_j E) := by rw [h']
      _ = d • wz1Cross u v_j - wz1Cross v_j E := by abel
  have h_left_norm : ‖s_k • wz1Cross v_j v_k‖ = |s_k| * ‖wz1Cross v_j v_k‖ := by
    rw [norm_smul] <;> rfl
  have h_d_nonneg : 0 ≤ d := hd_pos.le
  have h_right_lower : ‖d • wz1Cross u v_j - wz1Cross v_j E‖ ≥
      d * ‖wz1Cross u v_j‖ - ‖wz1Cross v_j E‖ := by
    have h1 : ‖d • wz1Cross u v_j‖ = d * ‖wz1Cross u v_j‖ := by
      have h11 : ‖d • wz1Cross u v_j‖ = |d| * ‖wz1Cross u v_j‖ := norm_smul d (wz1Cross u v_j)
      rw [h11]
      have h12 : |d| = d := abs_of_nonneg h_d_nonneg
      rw [h12] <;> ring
    have h_tri1 : ‖d • wz1Cross u v_j‖ ≤ ‖d • wz1Cross u v_j - wz1Cross v_j E‖ + ‖wz1Cross v_j E‖ := by
      calc
        ‖d • wz1Cross u v_j‖
          = ‖(d • wz1Cross u v_j - wz1Cross v_j E) + wz1Cross v_j E‖ := by congr 1; abel
        _ ≤ ‖d • wz1Cross u v_j - wz1Cross v_j E‖ + ‖wz1Cross v_j E‖ := norm_add_le _ _
    linarith [h_tri1, h1]
  have h_cross_E_bound : ‖wz1Cross v_j E‖ ≤ 6 * rho := by
    have h : ‖wz1Cross v_j E‖ ≤ ‖v_j‖ * ‖E‖ := wz1Cross_norm_le v_j E
    rw [hvj_unit] at h
    linarith [hE_norm]
  have h_norm_eq : ‖s_k • wz1Cross v_j v_k‖ = ‖d • wz1Cross u v_j - wz1Cross v_j E‖ := by
    rw [h_final]
  have h_ineq : |s_k| * ‖wz1Cross v_j v_k‖ ≥ d * ‖wz1Cross u v_j‖ - 6 * rho := by
    calc
      |s_k| * ‖wz1Cross v_j v_k‖ = ‖s_k • wz1Cross v_j v_k‖ := h_left_norm.symm
      _ = ‖d • wz1Cross u v_j - wz1Cross v_j E‖ := h_norm_eq
      _ ≥ d * ‖wz1Cross u v_j‖ - ‖wz1Cross v_j E‖ := h_right_lower
      _ ≥ d * ‖wz1Cross u v_j‖ - 6 * rho := by gcongr
  have h_trans_lower : d * ‖wz1Cross u v_j‖ ≥ d * alpha := by
    gcongr <;> linarith
  have h_ineq2 : |s_k| * ‖wz1Cross v_j v_k‖ ≥ d * alpha - 6 * rho := by linarith
  have h_half : d * alpha - 6 * rho ≥ d * alpha / 4 := by linarith
  have h_ineq3 : |s_k| * ‖wz1Cross v_j v_k‖ ≥ d * alpha / 4 := by linarith
  have h_final_result : ‖wz1Cross v_j v_k‖ ≥ d * alpha / (4 * tau) := by
    have h_pos : 0 < tau := htau_pos
    have h6 : tau * ‖wz1Cross v_j v_k‖ ≥ |s_k| * ‖wz1Cross v_j v_k‖ := by
      gcongr <;> linarith
    have h7 : tau * ‖wz1Cross v_j v_k‖ ≥ d * alpha / 4 := by linarith
    calc
      ‖wz1Cross v_j v_k‖
        = (tau * ‖wz1Cross v_j v_k‖) / tau := by field_simp [h_pos.ne'] <;> ring
      _ ≥ (d * alpha / 4) / tau := by gcongr
      _ = d * alpha / (4 * tau) := by ring
  exact h_final_result

/-!
## Pairwise geometric bound helper

Extracts the m ≥ 99 geometric intersection bound into a standalone lemma
to keep the main theorem proof within heartbeat limits.
-/

/-- Geometric pairwise intersection bound for two paper-tube-derived sets.

When two points are axially separated by `d ≥ m * sep_scale / 2` and both
tubes are transverse to `u_ax` with norm ≥ `alpha`, the intersection volume
decays as `L² * tau / m`. -/
lemma pairwise_geometric_bound_paper
    {L tau : ℝ}
    (hL_pos : 0 < L)
    (hrho_small : 6 * L ≤ 1 / 1000)
    (htau_pos : 0 < tau)
    (h_1536_tau_le_98 : 1536 * tau ≤ 98)
    (sep_scale alpha : ℝ)
    (halpha_pos : 0 < alpha)
    (hsep_alpha : sep_scale * alpha = L)
    (u_ax : Point3)
    (hu_ax_unit : ‖u_ax‖ = 1)
    (T_i T_j : Kakeya.DeltaTube (6 * L))
    (p_i p_j : Point3)
    (h_trans_i : ‖wz1Cross u_ax T_i.direction‖ ≥ alpha)
    (h_trans_j : ‖wz1Cross u_ax T_j.direction‖ ≥ alpha)
    (d : ℝ)
    (hd_pos : 0 < d)
    (h_sep_bound : ‖p_j - p_i - d • u_ax‖ ≤ 2 * (6 * L))
    (A_i A_j : Set Point3)
    (hSi_sub : A_i ⊆ T_i.carrier ∩ Metric.closedBall p_i tau)
    (hSj_sub : A_j ⊆ T_j.carrier ∩ Metric.closedBall p_j tau)
    (hpi_Ti : p_i ∈ T_i.carrier)
    (hpj_Tj : p_j ∈ T_j.carrier)
    (m : ℕ)
    (hm_pos : 0 < m)
    (h_m_large : m ≥ 99)
    (hd_lower : d ≥ (m : ℝ) * sep_scale / 2)
    : volume (A_i ∩ A_j) ≤ ENNReal.ofReal (27648 * L^2 * tau / (m : ℝ)) := by
  set c : ℝ := alpha / 4 with hc_def
  have hc_pos : 0 < c := by positivity
  have h_m99 : (m : ℝ) ≥ 99 := by exact_mod_cast h_m_large
  have h_d_alpha2 : d * alpha ≥ (m : ℝ) * L / 2 := by
    have h1 : d * alpha ≥ ((m : ℝ) * sep_scale / 2) * alpha := by gcongr
    have h2 : ((m : ℝ) * sep_scale / 2) * alpha = (m : ℝ) * (sep_scale * alpha) / 2 := by ring
    have h3 : (m : ℝ) * (sep_scale * alpha) / 2 = (m : ℝ) * L / 2 := by rw [hsep_alpha]
    calc d * alpha
      ≥ ((m : ℝ) * sep_scale / 2) * alpha := h1
    _ = (m : ℝ) * (sep_scale * alpha) / 2 := h2
    _ = (m : ℝ) * L / 2 := h3
  have h_d_alpha_large : d * alpha ≥ 8 * (6 * L) := by
    have h4 : (m : ℝ) * L / 2 ≥ 48 * L := by
      have h5 : 0 ≤ L := by linarith
      nlinarith
    have h6 : 48 * L = 8 * (6 * L) := by ring
    linarith
  have h_cross_large : c * d / tau ≥ 32 * (6 * L) := by
    have h1 : c * d / tau = d * alpha / (4 * tau) := by
      rw [hc_def] <;> ring
    rw [h1]
    have h2 : d * alpha / (4 * tau) ≥ (m : ℝ) * L / (8 * tau) := by
      have h_pos : 0 < 4 * tau := by positivity
      have h3 : d * alpha / (4 * tau) ≥ ((m : ℝ) * L / 2) / (4 * tau) :=
        div_le_div_of_nonneg_right h_d_alpha2 h_pos.le
      have h4 : ((m : ℝ) * L / 2) / (4 * tau) = (m : ℝ) * L / (8 * tau) := by ring
      rw [h4] at h3; exact h3
    have h3 : (m : ℝ) * L / (8 * tau) ≥ 99 * L / (8 * tau) := by gcongr
    have h4 : 99 / (8 * tau) ≥ 192 := by
      calc 99 / (8 * tau)
        ≥ 99 / (8 * (98 / 1536)) := by gcongr <;> linarith
      _ ≥ 192 := by norm_num
    have h5 : 0 ≤ L := by linarith
    have h6 : 99 * L / (8 * tau) ≥ 32 * (6 * L) := by
      calc 99 * L / (8 * tau)
        = (99 / (8 * tau)) * L := by ring
      _ ≥ 192 * L := by gcongr
      _ = 32 * (6 * L) := by ring
    linarith
  by_cases h_nonempty : (A_i ∩ A_j).Nonempty
  · rcases h_nonempty with ⟨x, hx⟩
    let s_i : ℝ := inner ℝ (x - p_i) T_i.direction
    let e_i : Point3 := (x - p_i) - s_i • T_i.direction
    have hxi1 : x = p_i + s_i • T_i.direction + e_i := by
      simp [e_i, s_i] <;> abel
    let s_j : ℝ := inner ℝ (x - p_j) T_j.direction
    let e_j : Point3 := (x - p_j) - s_j • T_j.direction
    have hxj1 : x = p_j + s_j • T_j.direction + e_j := by
      simp [e_j, s_j] <;> abel
    have hsi_bound : |s_i| ≤ tau := by
      have h2 : |inner ℝ (x - p_i) T_i.direction| ≤ ‖x - p_i‖ * ‖T_i.direction‖ :=
        abs_real_inner_le_norm _ _
      rw [T_i.direction_unit] at h2
      have h3 : ‖x - p_i‖ ≤ tau := by
        simpa [dist_eq_norm] using (hSi_sub hx.1).2
      linarith
    have hsj_bound : |s_j| ≤ tau := by
      have h2 : |inner ℝ (x - p_j) T_j.direction| ≤ ‖x - p_j‖ * ‖T_j.direction‖ :=
        abs_real_inner_le_norm _ _
      rw [T_j.direction_unit] at h2
      have h3 : ‖x - p_j‖ ≤ tau := by
        simpa [dist_eq_norm] using (hSj_sub hx.2).2
      linarith
    have hei_bound : ‖e_i‖ ≤ 2 * (6 * L) := by
      have h_perp : ‖p_i - x - (inner ℝ (p_i - x) T_i.direction) • T_i.direction‖ ≤ 2 * (6 * L) :=
        tube_two_point_perp_bound (by positivity) T_i T_i.direction T_i.direction_unit rfl
          x p_i (hSi_sub hx.1).1 hpi_Ti
      have h_eq : p_i - x - (inner ℝ (p_i - x) T_i.direction) • T_i.direction = -e_i := by
        have h1 : inner ℝ (p_i - x) T_i.direction = -s_i := by
          simp [s_i, inner_sub_left] <;> ring
        rw [h1]; simp [e_i] <;> abel
      rw [h_eq] at h_perp
      rw [norm_neg] at h_perp; exact h_perp
    have hej_bound : ‖e_j‖ ≤ 2 * (6 * L) := by
      have h_perp : ‖p_j - x - (inner ℝ (p_j - x) T_j.direction) • T_j.direction‖ ≤ 2 * (6 * L) :=
        tube_two_point_perp_bound (by positivity) T_j T_j.direction T_j.direction_unit rfl
          x p_j (hSj_sub hx.2).1 hpj_Tj
      have h_eq : p_j - x - (inner ℝ (p_j - x) T_j.direction) • T_j.direction = -e_j := by
        have h1 : inner ℝ (p_j - x) T_j.direction = -s_j := by
          simp [s_j, inner_sub_left] <;> ring
        rw [h1]; simp [e_j] <;> abel
      rw [h_eq] at h_perp
      rw [norm_neg] at h_perp; exact h_perp
    have h_cross : ‖wz1Cross T_i.direction T_j.direction‖ ≥ d * alpha / (4 * tau) :=
      angle_from_separated_intersections_weak (by positivity) htau_pos
        halpha_pos hd_pos u_ax T_i.direction T_j.direction
        hu_ax_unit T_i.direction_unit T_j.direction_unit
        p_i p_j x e_i e_j s_i s_j
        h_sep_bound hxi1 hxj1 hei_bound hej_bound hsi_bound hsj_bound
        h_trans_i h_trans_j h_d_alpha_large
    have h_cross_lower : ‖wz1Cross T_i.direction T_j.direction‖ ≥ c * d / tau := by
      have h_eq : c * d / tau = d * alpha / (4 * tau) := by
        rw [hc_def] <;> ring
      rw [h_eq]; exact h_cross
    have h_subset : A_i ∩ A_j ⊆ T_i.carrier ∩ T_j.carrier ∩ Metric.ball p_i (3 * tau) := by
      intro y hy
      have h3 : y ∈ T_i.carrier := (hSi_sub hy.1).1
      have h4 : y ∈ T_j.carrier := (hSj_sub hy.2).1
      have h5 : dist y p_i ≤ tau := (hSi_sub hy.1).2
      have h6 : dist y p_i < 3 * tau := by linarith [htau_pos]
      exact ⟨⟨h3, h4⟩, h6⟩
    have h_volume : volume (T_i.carrier ∩ T_j.carrier ∩ Metric.ball p_i (3 * tau)) ≤
        ENNReal.ofReal (16 * (6 * L)^3 * tau / (c * d)) :=
      pairwise_tube_intersection_volume (rho := 6 * L) (tau := tau)
        (by positivity) hrho_small htau_pos
        T_i T_j p_i hc_pos hd_pos h_cross_lower h_cross_large
    have h_cd_lower : c * d ≥ (m : ℝ) * L / 8 := by
      have h1 : c * d = (alpha / 4) * d := by rw [hc_def]
      rw [h1]
      have h2 : (alpha / 4) * d ≥ (alpha / 4) * ((m : ℝ) * sep_scale / 2) := by gcongr
      have h3 : (alpha / 4) * ((m : ℝ) * sep_scale / 2) = (m : ℝ) * (sep_scale * alpha) / 8 := by ring
      have h4 : (m : ℝ) * (sep_scale * alpha) / 8 = (m : ℝ) * L / 8 := by rw [hsep_alpha]
      linarith
    have h_bound : 16 * (6 * L)^3 * tau / (c * d) ≤
        27648 * L^2 * tau / (m : ℝ) := by
      have h_cd_pos : 0 < c * d := mul_pos hc_pos hd_pos
      have h_m_pos' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm_pos
      have h_eq3 : 16 * (6 * L)^3 * tau / ((m : ℝ) * L / 8) =
          27648 * L^2 * tau / (m : ℝ) := by
        field_simp [h_cd_pos.ne', h_m_pos'.ne'] <;> ring
      calc 16 * (6 * L)^3 * tau / (c * d)
        ≤ 16 * (6 * L)^3 * tau / ((m : ℝ) * L / 8) := by gcongr
      _ = 27648 * L^2 * tau / (m : ℝ) := h_eq3
    calc volume (A_i ∩ A_j)
      ≤ volume (T_i.carrier ∩ T_j.carrier ∩ Metric.ball p_i (3 * tau)) :=
        measure_mono h_subset
    _ ≤ ENNReal.ofReal (16 * (6 * L)^3 * tau / (c * d)) := h_volume
    _ ≤ ENNReal.ofReal (27648 * L^2 * tau / (m : ℝ)) :=
      ENNReal.ofReal_mono h_bound
  · have h0 : A_i ∩ A_j = ∅ := by
      simpa [Set.not_nonempty_iff_eq_empty] using h_nonempty
    rw [h0] <;> simp

/-- Derive `6 * L ≤ 1 / 1000` from the log absorption hypothesis with k=1. -/
lemma derive_6L_small
    {L epsilon₁ epsilon₃ : ℝ}
    (hL_pos : 0 < L)
    (hL_small : L ≤ 1 / 1000)
    (heps₁_pos : 0 < epsilon₁)
    (heps₃_pos : 0 < epsilon₃)
    (heps_sum : epsilon₁ + epsilon₃ < 1)
    (h_log_absorption : ∀ (k : ℕ), 0 < k → (k : ℝ) ≤ 100 / L^3 →
        Real.rpow L epsilon₁ * (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108)
    : 6 * L ≤ 1 / 1000 := by
  have h_k1 : ((1 : ℕ) : ℝ) ≤ 100 / L^3 := by
    have h1 : 0 < L^3 := by positivity
    have h2 : L^3 ≤ 100 := by
      have h3 : L^3 ≤ (1 / 1000 : ℝ)^3 := by gcongr <;> linarith
      linarith
    have h4 : (1 : ℝ) * L^3 ≤ 100 := by linarith
    have h5 : (1 : ℝ) ≤ 100 / L^3 := by
      calc (1 : ℝ)
        = (1 : ℝ) * L^3 / L^3 := by field_simp [h1.ne'] <;> ring
      _ ≤ 100 / L^3 := by gcongr
    exact_mod_cast h5
  have h2 := h_log_absorption (1 : ℕ) (by norm_num) h_k1
  have h_log1 : Real.log ((1 : ℕ) : ℝ) = 0 := by simp
  rw [h_log1] at h2
  have h_simp : (288 + 56448 * (1 + (0 : ℝ))) = 56736 := by norm_num
  rw [h_simp] at h2
  have h1 : Real.rpow L epsilon₁ * 56736 ≤ 125 / 108 := h2
  have hL_le_one : L ≤ 1 := by linarith [hL_small]
  have heps_le_one : epsilon₁ ≤ 1 := by linarith [heps_sum, heps₃_pos]
  have h41 : Real.rpow L 1 ≤ Real.rpow L epsilon₁ :=
    Real.rpow_le_rpow_of_exponent_ge hL_pos hL_le_one heps_le_one
  have h_rpow1 : Real.rpow L 1 = L := Real.rpow_one L
  have h4 : L ≤ Real.rpow L epsilon₁ := by
    rw [h_rpow1] at h41
    exact h41
  have h9 : L * 56736 ≤ Real.rpow L epsilon₁ * 56736 :=
    mul_le_mul_of_nonneg_right h4 (by norm_num)
  have h10 : L * 56736 ≤ 125 / 108 := by linarith
  have h11 : L ≤ 125 / (108 * 56736) := by
    calc L
      = L * 56736 / 56736 := by field_simp <;> ring
    _ ≤ (125 / 108) / 56736 := by gcongr
    _ = 125 / (108 * 56736) := by ring
  have h12 : 6 * L ≤ 750 / (108 * 56736) := by linarith [h11]
  have h13 : (750 : ℝ) / (108 * 56736) ≤ 1 / 1000 := by norm_num
  linarith

/-- Pairwise intersection bound for the Córdoba L² inequality.

Given sorted points with axial and transverse separation, and property-(P) data
with transverse witnesses, bound the volume of intersection of any two Córdoba
sets by `C_int / |i - j|`. -/
lemma pairwise_intersection_bound_paper
    {L tau : ℝ}
    {k : ℕ}
    {coarse : Kakeya.Streamlined.TubeFamily L}
    {sigma : ℝ}
    {coarseShading : WZ1PaperTubeShading coarse}
    {epsilon₁ epsilon₃ : ℝ}
    (propP : @PureWZ2CordobaPropertyPData sigma L tau coarse coarseShading
      epsilon₁ epsilon₃)
    (hL_pos : 0 < L)
    (hL_small : L ≤ 1 / 1000)
    (htau_pos : 0 < tau)
    (htau_sq : tau ^ 2 ≤ 4 * L)
    (heps₁_pos : 0 < epsilon₁)
    (heps₃_pos : 0 < epsilon₃)
    (heps_sum : epsilon₁ + epsilon₃ < 1)
    (h_log_absorption : ∀ (k : ℕ), 0 < k → (k : ℝ) ≤ 100 / L^3 →
        Real.rpow L epsilon₁ * (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108)
    (sep_scale : ℝ)
    (hsep_scale : sep_scale = Real.rpow L (1 - epsilon₃))
    (u_ax : Point3)
    (hu_ax_unit : ‖u_ax‖ = 1)
    (p : ℕ → Point3)
    (j_m : ∀ (m : ℕ), m < k → Fin coarse.card)
    (hj1 : ∀ (m : ℕ), (hm : m < k) → p m ∈ propP.propertyOne.carrier (j_m m hm))
    (hj_trans : ∀ (m : ℕ), (hm : m < k) →
        ‖wz1Cross u_ax (coarse.tube (j_m m hm)).direction‖ ≥ Real.rpow L epsilon₃)
    (h_vol_upper : ∀ (i : Fin k), volume (
        propP.propertyOne.carrier (j_m i.val i.is_lt) ∩ Metric.closedBall (p i.val) tau) ≤
        ENNReal.ofReal (288 * L^2 * tau))
    (sorted_idx_fin : Fin k → Fin k)
    (h_trans_sep : ∀ i j,
        ‖(p ((sorted_idx_fin j).val)) - (p ((sorted_idx_fin i).val)) -
          (inner ℝ ((p ((sorted_idx_fin j).val)) - (p ((sorted_idx_fin i).val))) u_ax) • u_ax‖ ≤ 2 * (6 * L))
    (h_axial_gap : ∀ i j, i.val < j.val →
        inner ℝ ((p ((sorted_idx_fin j).val)) - (p ((sorted_idx_fin i).val))) u_ax ≥
          ((j.val : ℝ) - (i.val : ℝ)) * sep_scale / 2)
    (C_int : ℝ)
    (hC_int : C_int = 28224 * L^2 * tau)
    (h_1536_tau_le_98 : 1536 * tau ≤ 98)
    (i j : Fin k) (hne : i ≠ j) :
    volume ((
      propP.propertyOne.carrier (j_m (sorted_idx_fin i).val (sorted_idx_fin i).is_lt) ∩
      Metric.closedBall (p (sorted_idx_fin i).val) tau) ∩ (
      propP.propertyOne.carrier (j_m (sorted_idx_fin j).val (sorted_idx_fin j).is_lt) ∩
      Metric.closedBall (p (sorted_idx_fin j).val) tau)) ≤
      ENNReal.ofReal (C_int / |(i : ℝ) - (j : ℝ)|) := by
  let q_sorted : Fin k → Point3 := fun i => p ((sorted_idx_fin i).val)
  let A : Fin k → Set Point3 := fun i =>
    propP.propertyOne.carrier (j_m i.val i.is_lt) ∩ Metric.closedBall (p i.val) tau
  have hsep_pos : 0 < sep_scale := by
    rw [hsep_scale]
    exact Real.rpow_pos_of_pos hL_pos _
  have h_lt_case : ∀ (i j : Fin k), i.val < j.val →
      volume (A (sorted_idx_fin i) ∩ A (sorted_idx_fin j)) ≤
      ENNReal.ofReal (C_int / |(i : ℝ) - (j : ℝ)|) := by
    intro i j h
    have h1 : (i : ℝ) < (j : ℝ) := by exact_mod_cast h
    have h_abs : |(i : ℝ) - (j : ℝ)| = (j : ℝ) - (i : ℝ) := by
      rw [abs_of_neg (by linarith)] <;> ring
    rw [h_abs]
    let m : ℕ := j.val - i.val
    have hm_pos : 0 < m := by omega
    have h_diff : (j : ℝ) - (i : ℝ) = (m : ℝ) := by
      rw [Nat.cast_sub (by omega)] <;> simp
    rw [h_diff]
    let p_i_pt := q_sorted i
    let p_j_pt := q_sorted j
    let idx_i := (sorted_idx_fin i).val
    let hidx_i := (sorted_idx_fin i).is_lt
    let T_itube_idx := j_m idx_i hidx_i
    have h_paper_i : p_i_pt ∈ wz1PaperTubeCarrier (coarse.tube T_itube_idx) :=
      propP.propertyOne.subset_body T_itube_idx (hj1 idx_i hidx_i)
    rcases paper_tube_piece_in_delta_tube hL_pos hL_small htau_pos htau_sq
        (coarse.tube T_itube_idx) p_i_pt h_paper_i with
      ⟨T_itube, hT_itube_dir, hT_itube_contain⟩
    let T_i := T_itube
    let idx_j := (sorted_idx_fin j).val
    let hidx_j := (sorted_idx_fin j).is_lt
    let T_jtube_idx := j_m idx_j hidx_j
    have h_paper_j : p_j_pt ∈ wz1PaperTubeCarrier (coarse.tube T_jtube_idx) :=
      propP.propertyOne.subset_body T_jtube_idx (hj1 idx_j hidx_j)
    rcases paper_tube_piece_in_delta_tube hL_pos hL_small htau_pos htau_sq
        (coarse.tube T_jtube_idx) p_j_pt h_paper_j with
      ⟨T_jtube, hT_jtube_dir, hT_jtube_contain⟩
    let alpha : ℝ := Real.rpow L epsilon₃
    have halpha_pos : 0 < alpha := Real.rpow_pos_of_pos hL_pos _
    have h_trans_i : ‖wz1Cross u_ax T_i.direction‖ ≥ alpha := by
      have h1 : ‖wz1Cross u_ax (coarse.tube T_itube_idx).direction‖ ≥ alpha :=
        hj_trans idx_i hidx_i
      have h_goal : ‖wz1Cross u_ax T_i.direction‖ = ‖wz1Cross u_ax (coarse.tube T_itube_idx).direction‖ := by
        rw [hT_itube_dir]
      rw [h_goal]
      exact h1
    have h_trans_j : ‖wz1Cross u_ax T_jtube.direction‖ ≥ alpha := by
      have h1 : ‖wz1Cross u_ax (coarse.tube T_jtube_idx).direction‖ ≥ alpha :=
        hj_trans idx_j hidx_j
      have h_goal : ‖wz1Cross u_ax T_jtube.direction‖ = ‖wz1Cross u_ax (coarse.tube T_jtube_idx).direction‖ := by
        rw [hT_jtube_dir]
      rw [h_goal]
      exact h1
    let d : ℝ := inner ℝ (p_j_pt - p_i_pt) u_ax
    have h_gap_main : inner ℝ (q_sorted j - q_sorted i) u_ax ≥ ((j.val : ℝ) - (i.val : ℝ)) * sep_scale / 2 :=
      h_axial_gap i j h
    have h_eq_d : d = inner ℝ (q_sorted j - q_sorted i) u_ax := by
      simp [d, p_i_pt, p_j_pt] <;> rfl
    have h_eq_m : ((j.val : ℝ) - (i.val : ℝ)) = (m : ℝ) := by
      simp [m] <;> omega
    have hd_lower : d ≥ (m : ℝ) * sep_scale / 2 := by
      calc d
        = inner ℝ (q_sorted j - q_sorted i) u_ax := h_eq_d.symm
      _ ≥ ((j.val : ℝ) - (i.val : ℝ)) * sep_scale / 2 := h_gap_main
      _ = (m : ℝ) * sep_scale / 2 := by rw [h_eq_m]
    have hd_pos : 0 < d := by
      have h_pos : 0 < (m : ℝ) * sep_scale / 2 := by positivity
      linarith [hd_lower]
    have h_sep_bound : ‖p_j_pt - p_i_pt - d • u_ax‖ ≤ 2 * (6 * L) := h_trans_sep i j
    have hSi_sub : A (sorted_idx_fin i) ⊆ T_i.carrier ∩ Metric.closedBall p_i_pt tau := by
      intro x hx
      have h2 : x ∈ propP.propertyOne.carrier T_itube_idx := hx.1
      have h3 : x ∈ wz1PaperTubeCarrier (coarse.tube T_itube_idx) :=
        propP.propertyOne.subset_body T_itube_idx h2
      have h4 : x ∈ T_i.carrier := hT_itube_contain ⟨h3, hx.2⟩
      exact ⟨h4, hx.2⟩
    have hSj_sub : A (sorted_idx_fin j) ⊆ T_jtube.carrier ∩ Metric.closedBall p_j_pt tau := by
      intro x hx
      have h2 : x ∈ propP.propertyOne.carrier T_jtube_idx := hx.1
      have h3 : x ∈ wz1PaperTubeCarrier (coarse.tube T_jtube_idx) :=
        propP.propertyOne.subset_body T_jtube_idx h2
      have h4 : x ∈ T_jtube.carrier := hT_jtube_contain ⟨h3, hx.2⟩
      exact ⟨h4, hx.2⟩
    have h6L_small : 6 * L ≤ 1 / 1000 :=
      derive_6L_small hL_pos hL_small heps₁_pos heps₃_pos heps_sum h_log_absorption
    by_cases h_small : m ≤ 98
    · -- Crude bound for m ≤ 98
      have h_m_le_98 : m ≤ 98 := h_small
      have h_sub : A (sorted_idx_fin i) ∩ A (sorted_idx_fin j) ⊆ A (sorted_idx_fin i) := by simp
      have h_vol : volume (A (sorted_idx_fin i) ∩ A (sorted_idx_fin j)) ≤
          ENNReal.ofReal (288 * L^2 * tau) :=
        (measure_mono h_sub).trans (h_vol_upper (sorted_idx_fin i))
      have h_bound : (288 * L^2 * tau) ≤ C_int / (m : ℝ) := by
        have h_m_pos' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm_pos
        have h : (m : ℝ) ≤ 98 := by exact_mod_cast h_m_le_98
        have h5 : 288 * (m : ℝ) ≤ 28224 := by linarith
        have h6 : 0 ≤ L^2 * tau := by positivity
        have h_eq1 : 288 * L^2 * tau = (288 * (m : ℝ)) * (L^2 * tau / (m : ℝ)) := by
          field_simp [h_m_pos'.ne'] <;> ring
        have h_eq2 : (28224 : ℝ) * (L^2 * tau / (m : ℝ)) = C_int / (m : ℝ) := by
          rw [hC_int]
          <;> field_simp [h_m_pos'.ne'] <;> ring
        calc 288 * L^2 * tau
          = (288 * (m : ℝ)) * (L^2 * tau / (m : ℝ)) := h_eq1
        _ ≤ 28224 * (L^2 * tau / (m : ℝ)) := by gcongr
        _ = C_int / (m : ℝ) := h_eq2
      exact h_vol.trans (ENNReal.ofReal_mono h_bound)
    · -- Geometric bound for m ≥ 99
      have h_m_large : m ≥ 99 := by omega
      have hsep_alpha : sep_scale * alpha = L := by
        have h_alpha : alpha = Real.rpow L epsilon₃ := by rfl
        rw [hsep_scale, h_alpha]
        have h4 := Real.rpow_add hL_pos (1 - epsilon₃) epsilon₃
        have h5 : (1 - epsilon₃) + epsilon₃ = 1 := by ring
        rw [h5] at h4; simpa using h4.symm
      have hpi_Ti : p_i_pt ∈ T_i.carrier := hT_itube_contain ⟨h_paper_i,
        show dist p_i_pt p_i_pt ≤ tau by simp [htau_pos.le]⟩
      have hpj_Tj : p_j_pt ∈ T_jtube.carrier := hT_jtube_contain ⟨h_paper_j,
        show dist p_j_pt p_j_pt ≤ tau by simp [htau_pos.le]⟩
      have h_main_bound : volume (A (sorted_idx_fin i) ∩ A (sorted_idx_fin j)) ≤
          ENNReal.ofReal (27648 * L^2 * tau / (m : ℝ)) :=
        pairwise_geometric_bound_paper
          hL_pos h6L_small htau_pos h_1536_tau_le_98 sep_scale alpha halpha_pos hsep_alpha
          u_ax hu_ax_unit T_i T_jtube p_i_pt p_j_pt
          h_trans_i h_trans_j d hd_pos h_sep_bound
          (A (sorted_idx_fin i)) (A (sorted_idx_fin j))
          hSi_sub hSj_sub hpi_Ti hpj_Tj
          m hm_pos h_m_large hd_lower
      have h_final : 27648 * L^2 * tau / (m : ℝ) ≤ C_int / (m : ℝ) := by
        rw [hC_int]
        have h_m_pos' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm_pos
        have h6 : 0 ≤ L^2 * tau := by positivity
        have h7 : 27648 * L^2 * tau ≤ 28224 * L^2 * tau := by
          have h10 : 0 ≤ L^2 * tau := by positivity
          have h11 : (27648 : ℝ) ≤ 28224 := by norm_num
          linarith
        exact div_le_div_of_nonneg_right h7 h_m_pos'.le
      exact h_main_bound.trans (ENNReal.ofReal_mono h_final)
  by_cases h : i.val < j.val
  · exact h_lt_case i j h
  · have h' : j.val < i.val := by omega
    simpa [Set.inter_comm, abs_sub_comm] using h_lt_case j i h'

/-- Cardinality upper bound for separated points in a tube. -/
lemma cordoba_cardinality_bound_paper
    {L tau : ℝ} {k : ℕ} {epsilon₁ epsilon₃ : ℝ}
    (hL_pos : 0 < L)
    (hL_small : L ≤ 1 / 1000)
    (heps₁_pos : 0 < epsilon₁)
    (heps₃_pos : 0 < epsilon₃)
    (heps_sum : epsilon₁ + epsilon₃ < 1)
    (htau_le_one : tau ≤ 1)
    (sep_scale : ℝ)
    (hsep_scale : sep_scale = Real.rpow L (1 - epsilon₃))
    (p : ℕ → Point3)
    (p_mid : Point3)
    (hp_in_S : ∀ m, m < k → p m ∈ Set.univ ∧ dist (p m) p_mid ≤ tau)
    (hp_sep : ∀ m n, m < k → n < k → m ≠ n → dist (p m) (p n) ≥ sep_scale)
    : (k : ℝ) ≤ 100 / L^3 := by
  have h1 : (k : ℝ) ≤ 100 * Real.rpow L (-3) :=
    cordoba_separated_cardinality_of_lt (epsilon := epsilon₃) hL_pos (by linarith [hL_small])
      (by linarith [heps₃_pos]) (by linarith [heps_sum, heps₃_pos])
      p p_mid
      (fun m hm => by
        have h : dist (p m) p_mid ≤ tau := (hp_in_S m hm).2
        have h' : tau ≤ 1 := htau_le_one
        linarith)
      (fun m n hm hn hne => by
        have h : dist (p m) (p n) ≥ sep_scale := hp_sep m n hm hn hne
        have h' : sep_scale = Real.rpow L (1 - epsilon₃) := hsep_scale
        rw [h'] at h; exact h)
  have h2 : Real.rpow L (-3) = 1 / L^3 := by
    have h_pos : 0 < L := hL_pos
    have h_neg : Real.rpow L (-3) = (Real.rpow L (3 : ℝ))⁻¹ := by
      simp [Real.rpow_neg h_pos.le] <;> ring
    rw [h_neg]
    have h4 : Real.rpow L (3 : ℝ) = L^3 := by simp
    rw [h4] <;> ring
  rw [h2] at h1
  have h_eq : 100 * (1 / L ^ 3) = 100 / L ^ 3 := by ring
  rw [h_eq] at h1; exact h1

/-!
## Main Córdoba L² slab lower bound

Takes `PureWZ2PropertyPData` and produces the slab volume lower bound:
  volume(propertyOne ∩ ball(q, 3τ) ∩ slab(width 40L)) ≥
    L^(1 + 7ε₁ + ε₃) * τ² / 200

The slab width records both the paper-tube thickness and the actual Lipschitz
constant of the plane map.
-/

/--
Córdoba L² slab lower bound for PureWZ2 property-(P) data.

Uses paper-tube carriers (6L-thick) with a slab whose width records the
actual incidence and Lipschitz errors. Requires additional hypotheses:
Lipschitz plane map, incidence bound, propertyThree volume lower bound, and
log absorption.

Full proof adapting `wz1_lemma17_cordoba_slab_lower` to 6L-thick paper tubes.

Uses p_mid (realizing t) as the reference center, axial sorting along
the reference tube direction, and a weakened angle lemma to handle
alpha * sep_scale = L < 6L = rho.
-/
theorem pureWz2_cordoba_slab_lower_with_hypotheses
    {sigma L tau : ℝ}
    {coarse : Kakeya.Streamlined.TubeFamily L}
    {coarseShading : WZ1PaperTubeShading coarse}
    (epsilon₁ epsilon₃ : ℝ)
    (propP : PureWZ2CordobaPropertyPData
      (sigma := sigma) (coarseShading := coarseShading)
      (epsilon₁ := epsilon₁) (epsilon₃ := epsilon₃) (tau := tau))
    (planeLipschitzConstant : NNReal)
    (incidenceBound : ℝ)
    (planeMap : {point : Point3 // point ∈ propP.propertyThree.union} → Point3)
    (hplaneMap_unit : ∀ p, ‖planeMap p‖ = 1)
    (hplaneMap_lip : LipschitzWith planeLipschitzConstant planeMap)
    (h_incidence : ∀ (i : Fin coarse.card) (p : Point3)
        (hpu : p ∈ propP.propertyThree.union)
        (hpo : p ∈ propP.propertyOne.carrier i),
        |inner ℝ (coarse.tube i).direction (planeMap ⟨p, hpu⟩)| ≤
          incidenceBound)
    (h_propertyThree_full :
        ∀ (j : Fin coarse.card) (p : Point3),
          p ∈ propP.propertyThree.carrier j →
            Kakeya.realRpowENN L (2 + 2 * epsilon₁) * ENNReal.ofReal tau ≤
              volume (propP.propertyThree.carrier j ∩ Metric.closedBall p tau))
    (h_log_absorption : ∀ (k : ℕ), 0 < k →
        (k : ℝ) ≤ 100 / L^3 →
          Real.rpow L epsilon₁ *
            (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108)
    (h_ax_condition : 4 * (6 * L)^2 ≤ (3 / 4 : ℝ) * (Real.rpow L (1 - epsilon₃))^2)
    (hL_pos : 0 < L) (hL_small : L ≤ 1 / 1000)
    (htau_pos : 0 < tau) (hL_le_tau : L ≤ tau)
    (htau_sq : tau ^ 2 ≤ 4 * L) (htau_le_one : tau ≤ 1)
    (hsigma_pos : 0 < sigma) (hsigma_lt_one : sigma < 1)
    (heps₁_pos : 0 < epsilon₁) (heps₃_pos : 0 < epsilon₃)
    (heps_sum : epsilon₁ + epsilon₃ < 1)
    (q : Point3) (hq : q ∈ propP.propertyThree.union)
    (t : ℝ)
    (ht : t ∈ scalarProjection (planeMap ⟨q, hq⟩)
            (propP.propertyThree.union ∩ Metric.closedBall q tau)) :
    volume (coarseShading.union ∩ Metric.closedBall q (3 * tau) ∩
        {x | |inner ℝ x (planeMap ⟨q, hq⟩) - t| ≤
          (tau + 12 * L) *
              (2 * incidenceBound +
                3 * (planeLipschitzConstant : ℝ) * tau) +
            24 * L}) ≥
      Kakeya.realRpowENN L (1 + 7 * epsilon₁ + epsilon₃) *
        ENNReal.ofReal (tau ^ 2 / 200) := by
  -- Step 1: Extract p_mid realizing t from scalar projection
  have hq' : q ∈ propP.propertyThree.union := hq
  rcases ht with ⟨p_mid, hpmid_in, h_eq_t⟩
  have hpmid_union : p_mid ∈ propP.propertyThree.union := hpmid_in.1
  have hpmid_ball : dist p_mid q ≤ tau := hpmid_in.2
  rcases hpmid_union with ⟨i_ref, hp_mid_prop3⟩
  have hpmid_union' : p_mid ∈ propP.propertyThree.union := ⟨i_ref, hp_mid_prop3⟩
  let T_ref : Kakeya.DeltaTube L := coarse.tube i_ref
  let n : Point3 := planeMap ⟨q, hq'⟩
  have hn_unit : ‖n‖ = 1 := hplaneMap_unit ⟨q, hq'⟩
  let u_ax : Point3 := T_ref.direction
  have hu_ax_unit : ‖u_ax‖ = 1 := T_ref.direction_unit

  -- Step 2: Convert reference paper tube to DeltaTube(6L)
  rcases paper_tube_piece_in_delta_tube hL_pos hL_small htau_pos htau_sq T_ref p_mid
      (propP.propertyThree.subset_body i_ref hp_mid_prop3) with
    ⟨T_ref6, hT_ref6_dir, hT_ref6_contain⟩

  -- Step 3: Extract separated points from propertyThree around p_mid
  let sep_scale : ℝ := Real.rpow L (1 - epsilon₃)
  have hsep_pos : 0 < sep_scale := Real.rpow_pos_of_pos hL_pos _
  let S_ref : Set Point3 := propP.propertyThree.carrier i_ref ∩ Metric.closedBall p_mid tau
  have hS_ref_meas : MeasurableSet S_ref :=
    (propP.propertyThree.measurable_carrier i_ref).inter
      Metric.isClosed_closedBall.measurableSet
  have hS_ref_sub : S_ref ⊆ T_ref6.carrier ∩ Metric.closedBall p_mid tau := by
    intro x hx
    have h1 : x ∈ propP.propertyThree.carrier i_ref := hx.1
    have h2 : x ∈ wz1PaperTubeCarrier T_ref :=
      propP.propertyThree.subset_body i_ref h1
    have h3 : x ∈ T_ref6.carrier := hT_ref6_contain ⟨h2, hx.2⟩
    exact ⟨h3, hx.2⟩
  let V : ℝ := Real.rpow L (2 + 2 * epsilon₁) * tau
  have hV_pos : 0 < V := mul_pos (Real.rpow_pos_of_pos hL_pos _) htau_pos
  have h_vol_S_ref : volume S_ref ≥ ENNReal.ofReal V := by
    have h := h_propertyThree_full i_ref p_mid hp_mid_prop3
    have h_eq : Kakeya.realRpowENN L (2 + 2 * epsilon₁) * ENNReal.ofReal tau =
        ENNReal.ofReal V := by
      unfold Kakeya.realRpowENN
      have h1 : 0 ≤ Real.rpow L (2 + 2 * epsilon₁) := Real.rpow_nonneg hL_pos.le _
      rw [ENNReal.ofReal_mul h1] <;> rfl
    rw [h_eq] at h
    exact h

  obtain ⟨p, k, hk_lower, hp_in_S, hp_sep⟩ := separated_points_from_tube_volume_slab
      (show 0 < 6 * L by positivity)
      T_ref6 p_mid tau htau_pos S_ref hS_ref_meas hS_ref_sub sep_scale hsep_pos V hV_pos
      h_vol_S_ref

  have hk_pos : 0 < k := by
    have h1 : (k : ℝ) ≥ 5 * V / (24 * (6 * L)^2 * sep_scale) := hk_lower
    have h2 : 0 < 5 * V / (24 * (6 * L)^2 * sep_scale) := by positivity
    have h3 : (k : ℝ) > 0 := by linarith
    exact_mod_cast h3

  -- Step 4: Select transverse tubes at each point
  choose j_m hj1 hj_trans using fun (m : ℕ) (hm : m < k) =>
    propP.transverse (p m) (⟨i_ref, (hp_in_S m hm).1⟩) i_ref (hp_in_S m hm).1

  -- Step 5: Define Córdoba sets (without slab)
  let A : Fin k → Set Point3 := fun i =>
    propP.propertyOne.carrier (j_m i.val i.is_lt) ∩
    Metric.closedBall (p i.val) tau

  have hA_meas : ∀ i, MeasurableSet (A i) := by
    intro i
    let idx := j_m i.val i.is_lt
    have h1 : MeasurableSet (propP.propertyOne.carrier idx) :=
      propP.propertyOne.measurable_carrier idx
    have h2 : MeasurableSet (Metric.closedBall (p i.val) tau) :=
      Metric.isClosed_closedBall.measurableSet
    exact h1.inter h2

  -- Step 6: Volume lower bound via propertyOne_full
  have h_vol_lower : ∀ i, volume (A i) ≥ ENNReal.ofReal V := by
    intro i
    let j_i := j_m i.val i.is_lt
    let p_i := p i.val
    have hj1_i : p_i ∈ propP.propertyOne.carrier j_i := hj1 i.val i.is_lt
    have h := propP.propertyOne_full j_i p_i hj1_i
    have h_eq : Kakeya.realRpowENN L (2 + 2 * epsilon₁) * ENNReal.ofReal tau =
        ENNReal.ofReal V := by
      unfold Kakeya.realRpowENN
      have h1 : 0 ≤ Real.rpow L (2 + 2 * epsilon₁) := Real.rpow_nonneg hL_pos.le _
      rw [ENNReal.ofReal_mul h1] <;> rfl
    rw [h_eq] at h
    exact h

  -- Step 7: Volume upper bound via DeltaTube(6L)
  have h_vol_upper : ∀ i, volume (A i) ≤ ENNReal.ofReal (288 * L^2 * tau) := by
    intro i
    let j_i := j_m i.val i.is_lt
    let p_i := p i.val
    have hj1_i : p_i ∈ propP.propertyOne.carrier j_i := hj1 i.val i.is_lt
    have h_paper : p_i ∈ wz1PaperTubeCarrier (coarse.tube j_i) :=
      propP.propertyOne.subset_body j_i hj1_i
    rcases paper_tube_piece_in_delta_tube hL_pos hL_small htau_pos htau_sq
        (coarse.tube j_i) p_i h_paper with
      ⟨T_ji, hT_ji_dir, hT_ji_contain⟩
    have h1 : A i ⊆ T_ji.carrier ∩ Metric.closedBall p_i tau := by
      intro x hx
      have h2 : x ∈ propP.propertyOne.carrier j_i := hx.1
      have h3 : x ∈ wz1PaperTubeCarrier (coarse.tube j_i) :=
        propP.propertyOne.subset_body j_i h2
      have h4 : x ∈ T_ji.carrier := hT_ji_contain ⟨h3, hx.2⟩
      exact ⟨h4, hx.2⟩
    have h5 : volume (A i) ≤ volume (T_ji.carrier ∩ Metric.closedBall p_i tau) :=
      measure_mono h1
    have h6 : volume (T_ji.carrier ∩ Metric.closedBall p_i tau) ≤
        ENNReal.ofReal (8 * (6 * L)^2 * tau) :=
      tube_ball_intersection_volume_simple (hδ := by positivity) (hR := htau_pos.le) T_ji p_i
    have h7 : 8 * (6 * L)^2 * tau = 288 * L^2 * tau := by ring
    rw [h7] at h6
    exact h5.trans h6

  -- Step 8: Slab containment with the actual plane-map Lipschitz constant.
  have h_slab_contain : ∀ i, A i ⊆ {x : Point3 | |inner ℝ x n - t| ≤
      (tau + 12 * L) *
          (2 * incidenceBound +
            3 * (planeLipschitzConstant : ℝ) * tau) + 24 * L} := by
    intro i x hx
    let j_i := j_m i.val i.is_lt
    let p_i := p i.val
    have hx1 : x ∈ propP.propertyOne.carrier j_i := hx.1
    have hx2 : dist x p_i ≤ tau := hx.2
    have hp_i_prop3 : p_i ∈ propP.propertyThree.carrier i_ref := (hp_in_S i.val i.is_lt).1
    have hp_i_ball : dist p_i p_mid ≤ tau := (hp_in_S i.val i.is_lt).2
    have h_paper_i : p_i ∈ wz1PaperTubeCarrier (coarse.tube j_i) :=
      propP.propertyOne.subset_body j_i (hj1 i.val i.is_lt)
    rcases paper_tube_piece_in_delta_tube hL_pos hL_small htau_pos htau_sq
        (coarse.tube j_i) p_i h_paper_i with
      ⟨T_ji, hT_ji_dir, hT_ji_contain⟩
    have hx_Tji : x ∈ T_ji.carrier := hT_ji_contain ⟨
      propP.propertyOne.subset_body j_i hx1, hx2⟩
    have hpi_Tref6 : p_i ∈ T_ref6.carrier := hT_ref6_contain ⟨
      propP.propertyThree.subset_body i_ref hp_i_prop3, hp_i_ball⟩
    have hpmid_Tref6 : p_mid ∈ T_ref6.carrier := hT_ref6_contain ⟨
      propP.propertyThree.subset_body i_ref hp_mid_prop3,
      show dist p_mid p_mid ≤ tau by simp [htau_pos.le]⟩
    have hpi_Tji : p_i ∈ T_ji.carrier := hT_ji_contain ⟨h_paper_i,
      show dist p_i p_i ≤ tau by simp [htau_pos.le]⟩
    have hpi_union : p_i ∈ propP.propertyThree.union := ⟨i_ref, hp_i_prop3⟩
    have hCi : |inner ℝ T_ref6.direction n| ≤
        incidenceBound + (planeLipschitzConstant : ℝ) * tau := by
      let v_mid := planeMap ⟨p_mid, hpmid_union'⟩
      have h1 : |inner ℝ T_ref.direction v_mid| ≤ incidenceBound :=
        h_incidence i_ref p_mid hpmid_union'
          (propP.propertyThree_sub i_ref hp_mid_prop3)
      have h2 : dist n v_mid ≤
          (planeLipschitzConstant : ℝ) * dist q p_mid := by
        have h21 := hplaneMap_lip.dist_le_mul (⟨q, hq'⟩) (⟨p_mid, hpmid_union'⟩)
        have h22 : dist (⟨q, hq'⟩ : {p // p ∈ propP.propertyThree.union})
            (⟨p_mid, hpmid_union'⟩) = dist q p_mid := by
          simp [Subtype.dist_eq]
        simpa [h22] using h21
      have h3 : dist q p_mid ≤ tau := by
        exact dist_comm q p_mid ▸ hpmid_ball
      have h4 : |inner ℝ T_ref.direction (n - v_mid)| ≤ ‖n - v_mid‖ := by
        have h41 : |inner ℝ T_ref.direction (n - v_mid)| ≤
            ‖T_ref.direction‖ * ‖n - v_mid‖ := abs_real_inner_le_norm _ _
        rw [T_ref.direction_unit] at h41
        simpa using h41
      have h5 : ‖n - v_mid‖ ≤
          (planeLipschitzConstant : ℝ) * tau := by
        have h6 : ‖n - v_mid‖ = dist n v_mid := by simp [dist_eq_norm]
        rw [h6]
        exact h2.trans <| mul_le_mul_of_nonneg_left h3 (by positivity)
      have h_sum : inner ℝ T_ref.direction n =
          inner ℝ T_ref.direction v_mid + inner ℝ T_ref.direction (n - v_mid) := by
        have h2 : v_mid + (n - v_mid) = n := by abel
        calc
          inner ℝ T_ref.direction n
            = inner ℝ T_ref.direction (v_mid + (n - v_mid)) := by rw [h2]
          _ = inner ℝ T_ref.direction v_mid +
              inner ℝ T_ref.direction (n - v_mid) :=
            inner_add_right _ _ _
      calc
        |inner ℝ T_ref6.direction n|
          = |inner ℝ T_ref.direction n| := by rw [hT_ref6_dir]
        _ = |inner ℝ T_ref.direction v_mid + inner ℝ T_ref.direction (n - v_mid)| := by
            exact congr_arg abs h_sum
        _ ≤ |inner ℝ T_ref.direction v_mid| + |inner ℝ T_ref.direction (n - v_mid)| :=
            abs_add_le _ _
        _ ≤ incidenceBound + ‖n - v_mid‖ := by linarith
        _ ≤ incidenceBound + (planeLipschitzConstant : ℝ) * tau := by linarith
    have hCj : |inner ℝ T_ji.direction n| ≤
        incidenceBound + 2 * (planeLipschitzConstant : ℝ) * tau := by
      let v_i := planeMap ⟨p_i, hpi_union⟩
      have h1 : |inner ℝ (coarse.tube j_i).direction v_i| ≤ incidenceBound :=
        h_incidence j_i p_i hpi_union (hj1 i.val i.is_lt)
      have h2 : dist n v_i ≤
          (planeLipschitzConstant : ℝ) * dist q p_i := by
        have h21 := hplaneMap_lip.dist_le_mul (⟨q, hq'⟩) (⟨p_i, hpi_union⟩)
        have h22 : dist (⟨q, hq'⟩ : {p // p ∈ propP.propertyThree.union})
            (⟨p_i, hpi_union⟩) = dist q p_i := by
          simp [Subtype.dist_eq]
        simpa [h22] using h21
      have h3 : dist q p_i ≤ dist q p_mid + dist p_mid p_i := dist_triangle _ _ _
      have h41 : dist q p_mid ≤ tau := dist_comm q p_mid ▸ hpmid_ball
      have h42 : dist p_mid p_i ≤ tau := dist_comm p_mid p_i ▸ hp_i_ball
      have h4 : dist q p_i ≤ tau + tau := by linarith
      have h5 : |inner ℝ (coarse.tube j_i).direction (n - v_i)| ≤ ‖n - v_i‖ := by
        have h51 : |inner ℝ (coarse.tube j_i).direction (n - v_i)| ≤
            ‖(coarse.tube j_i).direction‖ * ‖n - v_i‖ := abs_real_inner_le_norm _ _
        rw [(coarse.tube j_i).direction_unit] at h51
        simpa using h51
      have h6 : ‖n - v_i‖ ≤
          2 * (planeLipschitzConstant : ℝ) * tau := by
        have h7 : ‖n - v_i‖ = dist n v_i := by simp [dist_eq_norm]
        rw [h7]
        calc
          dist n v_i ≤ (planeLipschitzConstant : ℝ) * dist q p_i := h2
          _ ≤ (planeLipschitzConstant : ℝ) * (tau + tau) := by
            gcongr
          _ = 2 * (planeLipschitzConstant : ℝ) * tau := by ring
      have h_sum : inner ℝ (coarse.tube j_i).direction n =
          inner ℝ (coarse.tube j_i).direction v_i +
          inner ℝ (coarse.tube j_i).direction (n - v_i) := by
        have h2 : v_i + (n - v_i) = n := by abel
        calc
          inner ℝ (coarse.tube j_i).direction n
            = inner ℝ (coarse.tube j_i).direction (v_i + (n - v_i)) := by rw [h2]
          _ = inner ℝ (coarse.tube j_i).direction v_i +
                inner ℝ (coarse.tube j_i).direction (n - v_i) :=
            inner_add_right _ _ _
      calc
        |inner ℝ T_ji.direction n|
          = |inner ℝ (coarse.tube j_i).direction n| := by rw [hT_ji_dir]
        _ = |inner ℝ (coarse.tube j_i).direction v_i +
              inner ℝ (coarse.tube j_i).direction (n - v_i)| := by
            exact congr_arg abs h_sum
        _ ≤ |inner ℝ (coarse.tube j_i).direction v_i| +
              |inner ℝ (coarse.tube j_i).direction (n - v_i)| := abs_add_le _ _
        _ ≤ incidenceBound + ‖n - v_i‖ := by linarith
        _ ≤ incidenceBound +
            2 * (planeLipschitzConstant : ℝ) * tau := by linarith
    have hCiNonnegative :
        0 ≤ incidenceBound + (planeLipschitzConstant : ℝ) * tau :=
      (abs_nonneg _).trans hCi
    have hCjNonnegative :
        0 ≤ incidenceBound +
          2 * (planeLipschitzConstant : ℝ) * tau :=
      (abs_nonneg _).trans hCj
    have h_core : |inner ℝ (x - p_mid) n| ≤
        (tau + 2 * (6 * L)) *
            ((incidenceBound + (planeLipschitzConstant : ℝ) * tau) +
              (incidenceBound +
                2 * (planeLipschitzConstant : ℝ) * tau)) +
          4 * (6 * L) :=
      slab_containment_core (by positivity) hn_unit hpmid_Tref6 hpi_Tref6 hpi_Tji hx_Tji
        (dist_comm p_i p_mid ▸ hp_i_ball) hx2 hCiNonnegative
        hCjNonnegative hCi hCj
    have h_simplify : (tau + 2 * (6 * L)) *
          ((incidenceBound + (planeLipschitzConstant : ℝ) * tau) +
            (incidenceBound +
              2 * (planeLipschitzConstant : ℝ) * tau)) +
          4 * (6 * L) =
        (tau + 12 * L) *
            (2 * incidenceBound +
              3 * (planeLipschitzConstant : ℝ) * tau) +
          24 * L := by ring
    rw [h_simplify] at h_core
    have h_eq : inner ℝ (x - p_mid) n = inner ℝ x n - t := by
      have h1 : inner ℝ (x - p_mid) n = inner ℝ x n - inner ℝ p_mid n := by
        exact inner_sub_left x p_mid n
      have h_eq_t' : inner ℝ p_mid n = t := by
        simpa [n] using h_eq_t
      rw [h1, h_eq_t']
    rwa [h_eq] at h_core

  -- Step 9: Sort points by axial projection along u_ax
  let s : Fin k → ℝ := fun i => inner ℝ (p i.val) u_ax
  have h_s_inj : Function.Injective s := by
    intro i j h
    by_contra hne
    have hne' : i.val ≠ j.val := by intro h; exact hne (Fin.ext h)
    have h_sep_points : dist (p i.val) (p j.val) ≥ sep_scale :=
      hp_sep i.val j.val i.is_lt j.is_lt hne'
    have hpi_Tref6 : p i.val ∈ T_ref6.carrier := hT_ref6_contain ⟨
      propP.propertyThree.subset_body i_ref (hp_in_S i.val i.is_lt).1,
      (hp_in_S i.val i.is_lt).2⟩
    have hpj_Tref6 : p j.val ∈ T_ref6.carrier := hT_ref6_contain ⟨
      propP.propertyThree.subset_body i_ref (hp_in_S j.val j.is_lt).1,
      (hp_in_S j.val j.is_lt).2⟩
    have h_ax : |inner ℝ (p j.val - p i.val) u_ax| ≥ sep_scale / 2 :=
      axial_separation_two_points (by positivity) hsep_pos u_ax hu_ax_unit
        T_ref6 hT_ref6_dir (p i.val) (p j.val) hpi_Tref6 hpj_Tref6 h_sep_points h_ax_condition
    have h_sub : inner ℝ (p j.val - p i.val) u_ax = inner ℝ (p j.val) u_ax - inner ℝ (p i.val) u_ax := by
      rw [inner_sub_left]
    have h_eq : inner ℝ (p j.val - p i.val) u_ax = 0 := by
      rw [h_sub]
      have h9 : inner ℝ (p i.val) u_ax = inner ℝ (p j.val) u_ax := h
      linarith
    rw [h_eq] at h_ax
    have h_pos : 0 < sep_scale / 2 := by linarith
    linarith
  let S_finset : Finset ℝ := Finset.image s Finset.univ
  have hS_card : S_finset.card = k := by
    rw [Finset.card_image_of_injective _ h_s_inj] <;> simp
  let e_ord : Fin k ≃o S_finset := Finset.orderIsoOfFin S_finset hS_card
  let sorted_idx_fin (i : Fin k) : Fin k :=
    Classical.choose (Finset.mem_image.mp (e_ord i).2)
  have h_choice_spec : ∀ (i : Fin k),
      sorted_idx_fin i ∈ Finset.univ ∧ s (sorted_idx_fin i) = (e_ord i : ℝ) := by
    intro i
    exact Classical.choose_spec (Finset.mem_image.mp (e_ord i).2)
  let sorted_idx (i : Fin k) : ℕ := (sorted_idx_fin i).val
  have hsorted_idx_lt : ∀ (i : Fin k), sorted_idx i < k := by
    intro i; exact (sorted_idx_fin i).is_lt
  have h_s_spec : ∀ (i : Fin k), s ⟨sorted_idx i, hsorted_idx_lt i⟩ = (e_ord i : ℝ) := by
    intro i
    have h_eq : ⟨sorted_idx i, hsorted_idx_lt i⟩ = sorted_idx_fin i := by apply Fin.ext; rfl
    rw [h_eq]; exact (h_choice_spec i).2
  let q_sorted (i : Fin k) : Point3 := p (sorted_idx i)
  have h_sorted_axially : ∀ (i j : Fin k), i ≤ j →
      inner ℝ (q_sorted i) u_ax ≤ inner ℝ (q_sorted j) u_ax := by
    intro i j hij
    have h1 : (e_ord i : ℝ) ≤ (e_ord j : ℝ) := e_ord.monotone hij
    have h2 : inner ℝ (q_sorted i) u_ax = (e_ord i : ℝ) := by simpa [q_sorted, s] using h_s_spec i
    have h3 : inner ℝ (q_sorted j) u_ax = (e_ord j : ℝ) := by simpa [q_sorted, s] using h_s_spec j
    linarith

  -- Consecutive axial gap ≥ sep_scale / 2
  have h_consec_gap : ∀ (a : Fin k), (h : a.val + 1 < k) →
      inner ℝ (q_sorted ⟨a.val + 1, h⟩ - q_sorted a) u_ax ≥ sep_scale / 2 := by
    intro a h
    let i : Fin k := a
    let j : Fin k := ⟨a.val + 1, h⟩
    have hne : i ≠ j := by
      intro h_eq
      have h9 : i.val = j.val := congr_arg Fin.val h_eq
      simp [j] at h9 <;> omega
    have h_idx_ne : sorted_idx i ≠ sorted_idx j := by
      intro h10
      have h10' : sorted_idx_fin i = sorted_idx_fin j := by
        apply Fin.ext
        exact h10
      have h11 : s (sorted_idx_fin i) = s (sorted_idx_fin j) := by rw [h10']
      have h12 : (e_ord i : ℝ) = (e_ord j : ℝ) := by
        calc (e_ord i : ℝ)
          = s (sorted_idx_fin i) := (h_choice_spec i).2.symm
        _ = s (sorted_idx_fin j) := h11
        _ = (e_ord j : ℝ) := (h_choice_spec j).2
      have h13 : i = j := e_ord.injective (Subtype.ext h12)
      exact hne h13
    have h_sep_points : dist (q_sorted i) (q_sorted j) ≥ sep_scale :=
      hp_sep (sorted_idx i) (sorted_idx j) (hsorted_idx_lt i) (hsorted_idx_lt j) h_idx_ne
    have hpi_Tref6 : q_sorted i ∈ T_ref6.carrier := hT_ref6_contain ⟨
      propP.propertyThree.subset_body i_ref (hp_in_S (sorted_idx i) (hsorted_idx_lt i)).1,
      (hp_in_S (sorted_idx i) (hsorted_idx_lt i)).2⟩
    have hpj_Tref6 : q_sorted j ∈ T_ref6.carrier := hT_ref6_contain ⟨
      propP.propertyThree.subset_body i_ref (hp_in_S (sorted_idx j) (hsorted_idx_lt j)).1,
      (hp_in_S (sorted_idx j) (hsorted_idx_lt j)).2⟩
    have h_nonneg : 0 ≤ inner ℝ (q_sorted j - q_sorted i) u_ax := by
      have h_ij : i ≤ j := by
        have h : i.val ≤ j.val := by
          simp [i, j] <;> omega
        exact_mod_cast h
      have h : inner ℝ (q_sorted i) u_ax ≤ inner ℝ (q_sorted j) u_ax :=
        h_sorted_axially i j h_ij
      have h2 : inner ℝ (q_sorted j - q_sorted i) u_ax =
          inner ℝ (q_sorted j) u_ax - inner ℝ (q_sorted i) u_ax := by
        rw [inner_sub_left]
      rw [h2]
      linarith
    have h_ax_abs : |inner ℝ (q_sorted j - q_sorted i) u_ax| ≥ sep_scale / 2 :=
      axial_separation_two_points (by positivity) hsep_pos u_ax hu_ax_unit
        T_ref6 hT_ref6_dir (q_sorted i) (q_sorted j) hpi_Tref6 hpj_Tref6 h_sep_points h_ax_condition
    have h_ax_pos : |inner ℝ (q_sorted j - q_sorted i) u_ax| =
        inner ℝ (q_sorted j - q_sorted i) u_ax := by
      rw [abs_of_nonneg h_nonneg]
    rw [h_ax_pos] at h_ax_abs
    exact h_ax_abs

  -- Total axial gap for i < j
  have h_axial_gap : ∀ (i j : Fin k), i.val < j.val →
      inner ℝ (q_sorted j - q_sorted i) u_ax ≥
        ((j.val : ℝ) - (i.val : ℝ)) * sep_scale / 2 := by
    intro i j hij
    let make_fin : ∀ (n : ℕ), i.val + n ≤ j.val → Fin k :=
      fun n hn => ⟨i.val + n, Nat.lt_of_le_of_lt hn j.is_lt⟩
    have h_main : ∀ (n : ℕ) (hn : i.val + n ≤ j.val),
        inner ℝ (q_sorted (make_fin n hn) - q_sorted i) u_ax ≥
          (n : ℝ) * sep_scale / 2 := by
      intro n hn
      induction n with
      | zero =>
        simp [make_fin]
      | succ n ih =>
        have h_n1_lt_k : i.val + n + 1 < k := by linarith [hn, j.is_lt]
        have h_n_lt_k : i.val + n < k := by linarith
        let a : Fin k := ⟨i.val + n, h_n_lt_k⟩
        let b : Fin k := ⟨i.val + n + 1, h_n1_lt_k⟩
        have h_ih' := ih (by linarith)
        have h_gap : inner ℝ (q_sorted b - q_sorted a) u_ax ≥ sep_scale / 2 :=
          h_consec_gap a h_n1_lt_k
        have h_sum : inner ℝ (q_sorted b - q_sorted i) u_ax =
            inner ℝ (q_sorted b - q_sorted a) u_ax +
            inner ℝ (q_sorted a - q_sorted i) u_ax := by
          have h_eq : q_sorted b - q_sorted i = (q_sorted b - q_sorted a) + (q_sorted a - q_sorted i) := by abel
          rw [h_eq, inner_add_left]
        rw [h_sum]
        have h5 : (n.succ : ℝ) * sep_scale / 2 =
            (n : ℝ) * sep_scale / 2 + sep_scale / 2 := by
          simp [Nat.cast_add, Nat.cast_one] <;> ring
        rw [h5]
        linarith
    have h_ile : i.val ≤ j.val := le_of_lt hij
    have h_add : i.val + (j.val - i.val) = j.val := Nat.add_sub_of_le h_ile
    have h_arg : i.val + (j.val - i.val) ≤ j.val := by rw [h_add]
    have h1 := h_main (j.val - i.val) h_arg
    have h2 : make_fin (j.val - i.val) h_arg = j := by
      apply Fin.ext
      have h4 : (make_fin (j.val - i.val) h_arg).val = j.val := by
        simp [make_fin, h_add]
      exact h4
    have h3 : ((j.val - i.val : ℕ) : ℝ) = (j.val : ℝ) - (i.val : ℝ) := by
      rw [Nat.cast_sub h_ile] <;> simp
    rw [h2, h3] at h1
    exact h1

  -- Transverse separation bound
  have h_trans_sep : ∀ (i j : Fin k),
      ‖q_sorted j - q_sorted i - (inner ℝ (q_sorted j - q_sorted i) u_ax) • u_ax‖ ≤ 2 * (6 * L) := by
    intro i j
    exact tube_two_point_perp_bound (by positivity) T_ref6 u_ax hu_ax_unit hT_ref6_dir
      (q_sorted i) (q_sorted j)
      (hT_ref6_contain ⟨propP.propertyThree.subset_body i_ref
        (hp_in_S (sorted_idx i) (hsorted_idx_lt i)).1,
        (hp_in_S (sorted_idx i) (hsorted_idx_lt i)).2⟩)
      (hT_ref6_contain ⟨propP.propertyThree.subset_body i_ref
        (hp_in_S (sorted_idx j) (hsorted_idx_lt j)).1,
        (hp_in_S (sorted_idx j) (hsorted_idx_lt j)).2⟩)

  -- Step 10: Pairwise intersection bound
  let C_int : ℝ := 28224 * L^2 * tau
  have hC_int_pos : 0 < C_int := by positivity
  have h_1536_tau_le_98 : 1536 * tau ≤ 98 := by
    have h1 : (1536 * tau) ^ 2 ≤ 98 ^ 2 := by
      have h2 : tau ^ 2 ≤ 4 * L := htau_sq
      have h3 : L ≤ 1 / 1000 := hL_small
      nlinarith
    have h4 : 0 ≤ 1536 * tau := by positivity
    nlinarith
  have h_pairwise : ∀ (i j : Fin k), i ≠ j →
      volume (A (sorted_idx_fin i) ∩ A (sorted_idx_fin j)) ≤
        ENNReal.ofReal (C_int / |(i : ℝ) - (j : ℝ)|) :=
    fun i j hne =>
      pairwise_intersection_bound_paper
        propP
        hL_pos hL_small htau_pos htau_sq heps₁_pos heps₃_pos heps_sum h_log_absorption
        sep_scale (by rfl) u_ax hu_ax_unit p j_m hj1 hj_trans
        h_vol_upper sorted_idx_fin
        h_trans_sep h_axial_gap C_int (by rfl) h_1536_tau_le_98 i j hne

  -- Step 11: Apply finite Córdoba L²
  have h_cordoba : volume (⋃ i, A (sorted_idx_fin i)) ≥
      ENNReal.ofReal ((k : ℝ)^2 * V^2) /
      ENNReal.ofReal ((k : ℝ) * (288 * L^2 * tau) +
        2 * C_int * (k : ℝ) * (1 + Real.log (k : ℝ))) :=
    finite_cordoba_l2 hk_pos (fun i => A (sorted_idx_fin i))
      (fun i => hA_meas (sorted_idx_fin i)) V (288 * L^2 * tau) C_int
      hV_pos (by positivity) (by positivity) (fun i => h_vol_lower (sorted_idx_fin i))
      (fun i => h_vol_upper (sorted_idx_fin i)) h_pairwise

  -- Step 12: Log absorption and arithmetic
  have hk_upper : (k : ℝ) ≤ 100 / L^3 :=
    cordoba_cardinality_bound_paper
      hL_pos hL_small heps₁_pos heps₃_pos heps_sum htau_le_one sep_scale (by rfl) p p_mid
      (fun m hm => ⟨trivial, (hp_in_S m hm).2⟩)
      (fun m n hm hn hne => hp_sep m n hm hn hne)
  have h_log_main : Real.rpow L epsilon₁ *
      (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108 :=
    h_log_absorption k hk_pos hk_upper
  have hk_lower' : (k : ℝ) ≥
      (5 : ℝ) / 864 * Real.rpow L (2 * epsilon₁ - 1 + epsilon₃) * tau := by
    let a : ℝ := 2 * epsilon₁ - 1 + epsilon₃
    let b : ℝ := 2
    let c : ℝ := 1 - epsilon₃
    let X := Real.rpow L a
    let Y := Real.rpow L b
    let Z := Real.rpow L c
    have hY_pos : 0 < Y := Real.rpow_pos_of_pos hL_pos b
    have hZ_pos : 0 < Z := Real.rpow_pos_of_pos hL_pos c
    have h_sum : a + b + c = 2 + 2 * epsilon₁ := by ring
    have h_rpow : Real.rpow L (2 + 2 * epsilon₁) = X * Y * Z := by
      have h3 : Real.rpow L (a + b + c) = Real.rpow L (a + b) * Real.rpow L c :=
        Real.rpow_add hL_pos (a + b) c
      have h4 : Real.rpow L (a + b) = Real.rpow L a * Real.rpow L b :=
        Real.rpow_add hL_pos a b
      have h5 : Real.rpow L (2 + 2 * epsilon₁) = Real.rpow L (a + b + c) := by
        rw [←h_sum]
      have h6 : Real.rpow L (a + b + c) = (Real.rpow L a * Real.rpow L b) * Real.rpow L c := by
        rw [h3, h4] <;> ring
      rw [h5, h6]
      <;> rfl
    have h_denom : (24 * (6 * L)^2 * sep_scale) = 864 * Y * Z := by
      have h1 : (6 * L)^2 = 36 * L^2 := by ring
      have hL2 : L^2 = Real.rpow L 2 := by simp
      have hsep : sep_scale = Real.rpow L (1 - epsilon₃) := by rfl
      have hY : Y = Real.rpow L 2 := by rfl
      have hZ : Z = Real.rpow L (1 - epsilon₃) := by rfl
      rw [h1, hL2, hsep, hY, hZ] <;> ring
    have h_expand : 5 * V / (24 * (6 * L)^2 * sep_scale) = (5 : ℝ) / 864 * X * tau := by
      dsimp only [V]
      have h9 : (864 * Y * Z : ℝ) ≠ 0 := by positivity
      have h_cancel : (5 * ((X * Y * Z) * tau)) / (864 * Y * Z) = (5 : ℝ) / 864 * X * tau := by
        rw [div_eq_iff h9] <;> ring
      have h_num : 5 * (Real.rpow L (2 + 2 * epsilon₁) * tau) = 5 * ((X * Y * Z) * tau) := by
        rw [h_rpow] <;> ring
      rw [h_num, h_denom]
      exact h_cancel
    have h : (k : ℝ) ≥ 5 * V / (24 * (6 * L)^2 * sep_scale) := hk_lower
    rw [h_expand] at h
    exact h
  have hL_one : L ≤ 1 := by linarith [hL_small]
  have h_arithmetic := cordoba_final_arithmetic_paper
    hL_pos hL_one htau_pos heps₁_pos heps₃_pos hk_pos hk_lower' h_log_main

  -- Step 13: Union containment
  have h_union_sub : (⋃ i, A (sorted_idx_fin i)) ⊆
      coarseShading.union ∩ Metric.closedBall q (3 * tau) ∩
        {x | |inner ℝ x n - t| ≤
          (tau + 12 * L) *
              (2 * incidenceBound +
                3 * (planeLipschitzConstant : ℝ) * tau) +
            24 * L} := by
    intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
    have h1 : x ∈ coarseShading.union := by
      let j_i := j_m (sorted_idx i) (hsorted_idx_lt i)
      have h2 : x ∈ propP.propertyOne.carrier j_i := hxi.1
      have h2' : x ∈ coarseShading.carrier j_i := propP.propertyOne_sub j_i h2
      exact ⟨j_i, h2'⟩
    have h2 : dist x q ≤ 3 * tau := by
      let p_i := p (sorted_idx i)
      have h3 : dist x p_i ≤ tau := hxi.2
      have h41 : p (sorted_idx i) ∈ S_ref := hp_in_S (sorted_idx i) (hsorted_idx_lt i)
      have h42 : p (sorted_idx i) ∈ T_ref6.carrier ∩ Metric.closedBall p_mid tau := hS_ref_sub h41
      have h4 : dist p_i p_mid ≤ tau := h42.2
      have h5 : dist p_mid q ≤ tau := hpmid_ball
      have h6 : dist x q ≤ dist x p_i + dist p_i q := dist_triangle _ _ _
      have h7 : dist p_i q ≤ dist p_i p_mid + dist p_mid q := dist_triangle _ _ _
      have h8 : dist x q ≤ dist x p_i + dist p_i p_mid + dist p_mid q := by
        calc dist x q
          ≤ dist x p_i + dist p_i q := h6
        _ ≤ dist x p_i + (dist p_i p_mid + dist p_mid q) := by gcongr
        _ = dist x p_i + dist p_i p_mid + dist p_mid q := by ring
      linarith
    have h3 : x ∈ {x : Point3 | |inner ℝ x n - t| ≤
        (tau + 12 * L) *
            (2 * incidenceBound +
              3 * (planeLipschitzConstant : ℝ) * tau) +
          24 * L} := h_slab_contain (sorted_idx_fin i) hxi
    have h12 : x ∈ coarseShading.union ∩ Metric.closedBall q (3 * tau) := Set.mem_inter h1 h2
    exact Set.mem_inter h12 h3

  calc
    volume (coarseShading.union ∩ Metric.closedBall q (3 * tau) ∩
        {x | |inner ℝ x n - t| ≤
          (tau + 12 * L) *
              (2 * incidenceBound +
                3 * (planeLipschitzConstant : ℝ) * tau) +
            24 * L})
      ≥ volume (⋃ i, A (sorted_idx_fin i)) := measure_mono h_union_sub
    _ ≥ _ := h_cordoba
    _ ≥ _ := h_arithmetic

end Kakeya.Assouad

end
