import MyLeanRepo.Kakeya.Cinematic.Section5.CoarseFiberIntervalHelpers
import MyLeanRepo.Kakeya.Cinematic.Section5.CoarseFiberNeighborhoodVolume
import MyLeanRepo.Kakeya.Cinematic.Section5.ComparableRectangleC2Distance
import MyLeanRepo.Kakeya.Cinematic.TangencyIntervalExtension.Calculus

/-!
# Coarse-fiber carrier containment
-/

noncomputable section

open MeasureTheory Set

namespace Kakeya.Cinematic

theorem coarse_fiber_carrier_containment :
    CoarseFiberCarrierContainmentStatement := by
  intro hCommon
  intro h_comp
  intro K D C_shading hK hD hC_shading
  rcases h_comp K D hK hD with ⟨C, hC_pos, h_main⟩
  rcases comparable_rectangles_c2Distance_bound hCommon K D hK hD with
    ⟨C_c2, hC_c2, hC2_main⟩
  let C_graph : ℝ := 1 + C * Real.rpow 100 3
  let C_horizontal : ℝ := 10 + Real.sqrt C_shading / 2
  let C_gap : ℝ := (3 + C_c2) * C_shading * C_graph
  let C_vertical : ℝ := C_shading + C_gap
  let C_out : ℝ := max 1 (max C_horizontal C_vertical)
  have hC_graph : 1 ≤ C_graph := by
    dsimp only [C_graph]
    have hrpow : 0 < Real.rpow 100 3 :=
      Real.rpow_pos_of_pos (by norm_num) 3
    nlinarith [mul_pos hC_pos hrpow]
  have hC_graph_nonneg : 0 ≤ C_graph := by linarith
  have hC_shading_nonneg : 0 ≤ C_shading := by linarith
  have hC_gap_nonneg : 0 ≤ C_gap := by
    dsimp only [C_gap]
    positivity
  have hC_vertical_nonneg : 0 ≤ C_vertical := by
    dsimp only [C_vertical]
    positivity
  have hC_out : 1 ≤ C_out := le_max_left _ _
  have hhorizontal_le : C_horizontal ≤ C_out :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hvertical_le : C_vertical ≤ C_out :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hshading_le_vertical : C_shading ≤ C_vertical := by
    dsimp only [C_vertical]
    linarith
  have hC_out_nonneg : 0 ≤ C_out := by linarith
  refine ⟨C_out, hC_out, ?_⟩
  intro family I delta t Delta C_R hfam hI hdelta hdelta_le_Delta
    hDelta_le_t hC_R
  intro U enlarged parent hU_fun hU_mid henlarged_fam hparent_fam
    henlarged_quarter hparent_quarter h_cases
  have hDelta_pos : 0 < Delta := by linarith
  have hC_R_pos : 0 < C_R := by linarith
  have ht_pos : 0 < t := by linarith
  have hCt_pos : 0 < C_R * t := by positivity
  have hDelta_le_Ct : Delta ≤ C_R * t := by
    calc
      Delta ≤ t := hDelta_le_t
      _ ≤ C_R * t := by nlinarith
  have hsqrt_shading_nonneg : 0 ≤ Real.sqrt C_shading :=
    Real.sqrt_nonneg _
  have hsqrt_shading_one : 1 ≤ Real.sqrt C_shading := by
    have : Real.sqrt 1 ≤ Real.sqrt C_shading :=
      Real.sqrt_le_sqrt hC_shading
    simpa using this
  have h_len_le :
      U.interval.length ≤
        Real.sqrt C_shading * enlarged.interval.length :=
    fine_interval_length_le_sqrt_shading_mul_coarse
      hC_shading hC_R hdelta hdelta_le_Delta hDelta_le_t U enlarged
  have h_enlarged_len_eq :
      enlarged.interval.length = parent.interval.length := by
    rw [enlarged.interval_length, parent.interval_length]
  have hC_out_Delta_nonneg : 0 ≤ C_out * Delta :=
    mul_nonneg hC_out_nonneg (by linarith)
  constructor
  · intro p hp
    have h1 : p.1 ∈ Set.Icc U.interval.left U.interval.right := hp.1
    have h2 :
        |p.2 - U.function.extension p.1| ≤ C_shading * delta := hp.2
    have h_p1_in_unit : p.1 ∈ unitInterval := by
      have h_left_nonneg : 0 ≤ U.interval.left := U.interval.left_mem.1
      have h_right_le_one : U.interval.right ≤ 1 :=
        U.interval.right_mem.2
      exact ⟨by linarith [h1.1], by linarith [h1.2]⟩
    let x : UnitPoint := ⟨p.1, h_p1_in_unit⟩
    have h_abs_U :
        |p.1 - U.interval.midpoint| ≤ U.interval.length / 2 := by
      rw [abs_le]
      constructor <;>
        simp [ParameterInterval.midpoint, ParameterInterval.length] at *
        <;> linarith
    have hx_centered :
        x ∈ enlarged.interval.centeredCarrier
          (Real.sqrt C_shading) := by
      simp only [ParameterInterval.centeredCarrier, Set.mem_setOf_eq]
      rw [← hU_mid]
      exact h_abs_U.trans <| by
        have hhalf :
            U.interval.length / 2 ≤
              (Real.sqrt C_shading * enlarged.interval.length) / 2 := by
          linarith
        convert hhalf using 1 <;> ring
    rcases h_cases with h_eq | h_comp2
    · have h_horiz :
          |p.1 - parent.interval.midpoint| ≤
            C_out * parent.interval.length := by
        have hmid :
            U.interval.midpoint = parent.interval.midpoint := by
          rw [hU_mid, h_eq]
        have hfirst :
            |p.1 - parent.interval.midpoint| ≤
              Real.sqrt C_shading * parent.interval.length / 2 := by
          rw [← hmid, ← h_enlarged_len_eq]
          exact h_abs_U.trans <| by
            linarith
        have hcoefficient :
            Real.sqrt C_shading / 2 ≤ C_out := by
          have : Real.sqrt C_shading / 2 ≤ C_horizontal := by
            dsimp only [C_horizontal]
            linarith
          exact this.trans hhorizontal_le
        calc
          |p.1 - parent.interval.midpoint| ≤
              Real.sqrt C_shading * parent.interval.length / 2 := hfirst
          _ = (Real.sqrt C_shading / 2) *
              parent.interval.length := by ring
          _ ≤ C_out * parent.interval.length :=
            mul_le_mul_of_nonneg_right hcoefficient
              parent.interval.length_nonneg
      have h_vert :
          |p.2 - parent.function.extension p.1| ≤ C_out * Delta := by
        have h_fun : U.function = parent.function := by
          rw [hU_fun, h_eq]
        have h2' :
            |p.2 - parent.function.extension p.1| ≤ C_shading * delta := by
          rw [← h_fun]
          exact h2
        calc
          |p.2 - parent.function.extension p.1| ≤
              C_shading * delta := h2'
          _ ≤ C_shading * Delta := by gcongr
          _ ≤ C_vertical * Delta := by gcongr
          _ ≤ C_out * Delta := by gcongr
      exact ⟨h_horiz, h_vert⟩
    · have h_comp_result :=
        h_main family hfam I hI Delta (C_R * t) 100
          hDelta_pos hDelta_le_Ct (by norm_num)
          enlarged parent henlarged_fam hparent_fam
          henlarged_quarter hparent_quarter h_comp2
      have h_hull_le :
          max enlarged.interval.right parent.interval.right -
              min enlarged.interval.left parent.interval.left ≤
            Real.sqrt (100 * Delta / (C_R * t)) :=
        h_comp_result.1
      have h_graph :
          ∀ y : UnitPoint, y ∈ enlarged.intervalHullCarrier parent →
            |enlarged.function y - parent.function y| ≤
              C * Real.rpow 100 3 * Delta :=
        h_comp_result.2
      have h_sqrt :
          Real.sqrt (100 * Delta / (C_R * t)) =
            10 * parent.interval.length := by
        have hC_R_pos : 0 < C_R := by linarith
        have ht_pos : 0 < t := by linarith
        have hCt_pos : 0 < C_R * t := by positivity
        have h_pos : 0 ≤ Delta / (C_R * t) :=
          div_nonneg hDelta_pos.le hCt_pos.le
        have h :
            Real.sqrt (100 * (Delta / (C_R * t))) =
              10 * Real.sqrt (Delta / (C_R * t)) := by
          have h5 :
              0 ≤ 10 * Real.sqrt (Delta / (C_R * t)) := by positivity
          have h6 :
              (10 * Real.sqrt (Delta / (C_R * t))) ^ 2 =
                100 * (Delta / (C_R * t)) := by
            calc
              (10 * Real.sqrt (Delta / (C_R * t))) ^ 2 =
                  100 * (Real.sqrt (Delta / (C_R * t))) ^ 2 := by ring
              _ = 100 * (Delta / (C_R * t)) := by
                rw [Real.sq_sqrt h_pos]
          rw [← h6, Real.sqrt_sq_eq_abs, abs_of_nonneg h5]
        have h2 :
            100 * Delta / (C_R * t) =
              100 * (Delta / (C_R * t)) := by ring
        rw [h2, h, parent.interval_length]
      let hull_left := min enlarged.interval.left parent.interval.left
      let hull_right := max enlarged.interval.right parent.interval.right
      have h_hull_le' :
          hull_right - hull_left ≤ 10 * parent.interval.length := by
        rw [h_sqrt] at h_hull_le
        exact h_hull_le
      have h_enlarged_mid_in_hull_real :
          hull_left ≤ enlarged.interval.midpoint ∧
            enlarged.interval.midpoint ≤ hull_right := by
        constructor
        · have h :
              enlarged.interval.left ≤ enlarged.interval.midpoint := by
            dsimp only [ParameterInterval.midpoint]
            linarith [enlarged.interval.left_le_right]
          exact (min_le_left _ _).trans h
        · have h :
              enlarged.interval.midpoint ≤ enlarged.interval.right := by
            dsimp only [ParameterInterval.midpoint]
            linarith [enlarged.interval.left_le_right]
          exact h.trans (le_max_left _ _)
      have h_parent_mid_in_hull_real :
          hull_left ≤ parent.interval.midpoint ∧
            parent.interval.midpoint ≤ hull_right := by
        constructor
        · have h :
              parent.interval.left ≤ parent.interval.midpoint := by
            dsimp only [ParameterInterval.midpoint]
            linarith [parent.interval.left_le_right]
          exact (min_le_right _ _).trans h
        · have h :
              parent.interval.midpoint ≤ parent.interval.right := by
            dsimp only [ParameterInterval.midpoint]
            linarith [parent.interval.left_le_right]
          exact h.trans (le_max_right _ _)
      have h_horiz :
          |p.1 - parent.interval.midpoint| ≤
            C_out * parent.interval.length := by
        have h_mid_dist :
            |enlarged.interval.midpoint -
                parent.interval.midpoint| ≤
              hull_right - hull_left := by
          rw [abs_le]
          constructor <;>
            linarith [h_enlarged_mid_in_hull_real,
              h_parent_mid_in_hull_real]
        have h_to_enlarged :
            |p.1 - enlarged.interval.midpoint| ≤
              Real.sqrt C_shading * parent.interval.length / 2 := by
          have hhalf :
              U.interval.length / 2 ≤
                Real.sqrt C_shading * parent.interval.length / 2 := by
            rw [← h_enlarged_len_eq]
            exact div_le_div_of_nonneg_right h_len_le (by norm_num)
          rw [← hU_mid]
          exact h_abs_U.trans hhalf
        have htriangle :
            |p.1 - parent.interval.midpoint| ≤
              |p.1 - enlarged.interval.midpoint| +
                |enlarged.interval.midpoint -
                  parent.interval.midpoint| := by
          have heq :
              p.1 - parent.interval.midpoint =
                (p.1 - enlarged.interval.midpoint) +
                  (enlarged.interval.midpoint -
                    parent.interval.midpoint) := by ring
          rw [heq]
          exact abs_add_le _ _
        have hraw :
            |p.1 - parent.interval.midpoint| ≤
              C_horizontal * parent.interval.length := by
          calc
            |p.1 - parent.interval.midpoint| ≤
                |p.1 - enlarged.interval.midpoint| +
                  |enlarged.interval.midpoint -
                    parent.interval.midpoint| := htriangle
            _ ≤ Real.sqrt C_shading * parent.interval.length / 2 +
                10 * parent.interval.length :=
              add_le_add h_to_enlarged
                (h_mid_dist.trans h_hull_le')
            _ = C_horizontal * parent.interval.length := by
              dsimp only [C_horizontal]
              ring
        exact hraw.trans <|
          mul_le_mul_of_nonneg_right hhorizontal_le
            parent.interval.length_nonneg
      have h_enlarged_length_pos :
          0 < enlarged.interval.length := by
        rw [enlarged.interval_length]
        exact Real.sqrt_pos.mpr (by positivity)
      have hclose_on_enlarged :
          ∀ y ∈ enlarged.interval.carrier,
            |enlarged.function y - parent.function y| ≤
              C_graph * Delta := by
        intro y hy
        have hy_hull :
            y ∈ enlarged.intervalHullCarrier parent := by
          simp only [CurvilinearRectangle.intervalHullCarrier,
            Set.mem_setOf_eq]
          exact ⟨(min_le_left _ _).trans hy.1,
            hy.2.trans (le_max_left _ _)⟩
        have hraw := h_graph y hy_hull
        have hcoefficient :
            C * Real.rpow 100 3 ≤ C_graph := by
          dsimp only [C_graph]
          linarith
        exact hraw.trans <|
          mul_le_mul_of_nonneg_right hcoefficient hDelta_pos.le
      have h_c2 :
          c2Distance enlarged.function parent.function ≤
            C_c2 * (C_R * t) :=
        hC2_main hfam hI hDelta_pos hDelta_le_Ct enlarged parent
          henlarged_fam hparent_fam henlarged_quarter hparent_quarter
          h_comp2
      have hlength_sq :
          enlarged.interval.length ^ 2 = Delta / (C_R * t) := by
        rw [enlarged.interval_length]
        exact Real.sq_sqrt (by positivity)
      have hsquare :
          c2Distance enlarged.function parent.function *
              enlarged.interval.length ^ 2 ≤
            C_c2 * (C_graph * Delta) := by
        calc
          c2Distance enlarged.function parent.function *
                enlarged.interval.length ^ 2
              ≤ (C_c2 * (C_R * t)) *
                  enlarged.interval.length ^ 2 := by
            gcongr
          _ = C_c2 * Delta := by
            rw [hlength_sq]
            field_simp [hCt_pos.ne']
          _ ≤ C_c2 * (C_graph * Delta) := by
            have hC_c2_nonneg : 0 ≤ C_c2 := by linarith
            have : Delta ≤ C_graph * Delta := by nlinarith
            exact mul_le_mul_of_nonneg_left this hC_c2_nonneg
      have h_gap_value :
          |enlarged.function x - parent.function x| ≤
            C_gap * Delta := by
        have hTaylor :=
          value_bound_on_centered_dilation
            enlarged.function parent.function enlarged.interval
            (delta := C_graph * Delta) (A := C_c2)
            (lambda := Real.sqrt C_shading)
            (mul_nonneg hC_graph_nonneg hDelta_pos.le)
            (by linarith) h_enlarged_length_pos hclose_on_enlarged
            hsquare hsqrt_shading_one hx_centered
        have hsqrt_sq :
            (Real.sqrt C_shading) ^ 2 = C_shading :=
          Real.sq_sqrt hC_shading_nonneg
        calc
          |enlarged.function x - parent.function x| ≤
              (3 + C_c2) * (Real.sqrt C_shading) ^ 2 *
                (C_graph * Delta) := hTaylor
          _ = C_gap * Delta := by
            rw [hsqrt_sq]
            dsimp only [C_gap]
            ring
      have h_gap :
          |enlarged.function.extension p.1 -
              parent.function.extension p.1| ≤
            C_gap * Delta := by
        change
          |enlarged.function.extension (x : ℝ) -
              parent.function.extension (x : ℝ)| ≤ C_gap * Delta
        rw [C2Function.extension_eq_value,
          C2Function.extension_eq_value]
        exact h_gap_value
      have h_vert :
          |p.2 - parent.function.extension p.1| ≤ C_out * Delta := by
        have h7 :
            U.function.extension p.1 =
              enlarged.function.extension p.1 := by
          rw [hU_fun]
        have h2' :
            |p.2 - enlarged.function.extension p.1| ≤
              C_shading * delta := by
          rw [← h7]
          exact h2
        calc
          |p.2 - parent.function.extension p.1| ≤
              |p.2 - enlarged.function.extension p.1| +
                |enlarged.function.extension p.1 -
                  parent.function.extension p.1| := by
            simpa [Real.dist_eq] using
              dist_triangle p.2 (enlarged.function.extension p.1)
                (parent.function.extension p.1)
          _ ≤ C_shading * delta + C_gap * Delta :=
            add_le_add h2' h_gap
          _ ≤ C_shading * Delta + C_gap * Delta := by
            gcongr
          _ = C_vertical * Delta := by
            dsimp only [C_vertical]
            ring
          _ ≤ C_out * Delta := by gcongr
      exact ⟨h_horiz, h_vert⟩
  · exact volume_coarseFiberRealNeighborhood parent hC_out_nonneg
      hC_out_Delta_nonneg

end Kakeya.Cinematic
