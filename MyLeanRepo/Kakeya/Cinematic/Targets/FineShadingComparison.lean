import MyLeanRepo.Kakeya.Cinematic.Section5.ShadingInputs

/-!
# Comparable fine rectangles have nested shadings
-/

namespace Kakeya.Cinematic

theorem fine_shading_comparison :
    FineShadingComparisonStatement := by
  intro hComparable hTransitivity K D hK hD
  rcases hComparable K D hK hD with
    ⟨C, hC_pos, hComparable_prop⟩
  rcases hTransitivity K D hK hD 100 100 (by norm_num) (by norm_num) with
    ⟨lambda, hlambda_one, hTransitivity_prop⟩
  let C_s : ℝ :=
    max 100 (max (4 * lambda) (1 + C * lambda ^ 3))
  have hCs_100 : 100 ≤ C_s := by
    exact le_max_left _ _
  have hCs_one : 1 ≤ C_s := by
    linarith
  have hCs_lambda : lambda ≤ C_s := by
    have hfour : lambda ≤ 4 * lambda := by
      nlinarith
    exact hfour.trans (le_trans (le_max_left _ _) (le_max_right _ _))
  have hCs_four_lambda : 4 * lambda ≤ C_s := by
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hCs_vertical : 1 + C * lambda ^ 3 ≤ C_s := by
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨C_s, hCs_100, ?_⟩
  intro family hFamily E₂ delta t Delta C_R hdelta hdeltaDelta
    hDelta_t ht hC_R
  dsimp only
  intro hAdmissible data hbuffer R R' hR_family
    hR'_family hR_central hR'_central hR_midpoint hR'_midpoint hRR'
  have hdelta_nonneg : 0 ≤ delta := hdelta.le
  have hdelta_tFine : delta ≤ C_R * t * Delta / delta := by
    calc
      delta = 1 * delta := by ring
      _ ≤ C_s * delta :=
        mul_le_mul_of_nonneg_right hCs_one hdelta_nonneg
      _ ≤ C_R * t * Delta / delta := hAdmissible.2
  have htFine_pos : 0 < C_R * t * Delta / delta := by
    linarith
  intro p hp
  change ∃ hpE : p ∈ E₂,
    (data.rectangle ⟨p, hpE⟩).AreLambdaComparable R' family 100 ∧
      data.point ⟨p, hpE⟩ ∈ R'.carrier at hp
  rcases hp with ⟨hpE, hpR', hp_point⟩
  let P : CurvilinearRectangle delta (C_R * t * Delta / delta) :=
    data.rectangle ⟨p, hpE⟩
  have hP_family : P.function ∈ family := by
    rw [data.rectangle_function]
    exact data.center_mem ⟨p, hpE⟩
  have hP_central : P.IsOverCentralQuarterOf data.interval :=
    data.rectangle_central ⟨p, hpE⟩
  have hlambda_admissible :
      IsAdmissibleComparisonScale
        delta (C_R * t * Delta / delta) lambda := by
    refine ⟨hlambda_one, ?_⟩
    calc
      lambda * delta ≤ C_s * delta :=
        mul_le_mul_of_nonneg_right hCs_lambda hdelta_nonneg
      _ ≤ C_R * t * Delta / delta := hAdmissible.2
  have hR'R : R'.AreLambdaComparable R family 100 := by
    rcases hRR' with ⟨V, hV_family, hV_cover⟩
    refine ⟨V, hV_family, ?_⟩
    intro q hq
    rcases hq with hq | hq
    · exact hV_cover (Or.inr hq)
    · exact hV_cover (Or.inl hq)
  have hPR : P.AreLambdaComparable R family lambda :=
    hTransitivity_prop family hFamily data.interval
      data.intervalControlled delta (C_R * t * Delta / delta)
      hdelta hdelta_tFine hlambda_admissible
      P R' R hP_family hR'_family hR_family
      hP_central hR'_central hR_central hpR' hR'R
  have hGeometry :=
    hComparable_prop family hFamily data.interval
      data.intervalControlled delta (C_R * t * Delta / delta) lambda
      hdelta hdelta_tFine hlambda_one
      P R hP_family hR_family hP_central hR_central hPR
  have hHull :
      max P.interval.right R.interval.right -
          min P.interval.left R.interval.left ≤
        Real.sqrt (lambda * delta / (C_R * t * Delta / delta)) :=
    hGeometry.1
  have hGraph :
      ∀ x ∈ P.intervalHullCarrier R,
        |P.function x - R.function x| ≤
          C * lambda ^ 3 * delta := by
    intro x hx
    simpa [Real.rpow_natCast] using hGeometry.2 x hx
  let L₀ := Real.sqrt (lambda * delta / (C_R * t * Delta / delta))
  let L := Real.sqrt (C_s * delta / (C_R * t * Delta / delta))
  have hratio_nonneg :
      0 ≤ lambda * delta / (C_R * t * Delta / delta) := by
    positivity
  have hscale :
      4 * (lambda * delta / (C_R * t * Delta / delta)) ≤
        C_s * delta / (C_R * t * Delta / delta) := by
    have hmul :
        (4 * lambda) * delta ≤ C_s * delta :=
      mul_le_mul_of_nonneg_right hCs_four_lambda hdelta_nonneg
    rw [show
      4 * (lambda * delta / (C_R * t * Delta / delta)) =
        (4 * lambda) * delta / (C_R * t * Delta / delta) by ring]
    exact (div_le_div_iff_of_pos_right htFine_pos).2 hmul
  have hL₀_le_half : L₀ ≤ L / 2 := by
    have hsqrt := Real.sqrt_le_sqrt hscale
    have hsqrt_four :
        Real.sqrt
            (4 * (lambda * delta / (C_R * t * Delta / delta))) =
          2 * L₀ := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      have hsqrt_four : Real.sqrt (4 : ℝ) = 2 := by
        rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq] <;>
          norm_num
      rw [hsqrt_four]
    rw [hsqrt_four] at hsqrt
    change 2 * L₀ ≤ L at hsqrt
    linarith
  have hL_nonneg : 0 ≤ L := Real.sqrt_nonneg _
  have hL_buffer : L ≤ data.interval.length / 8 := hbuffer
  have hR_left_mid :
      R.interval.left ≤ R.interval.midpoint := by
    dsimp only [ParameterInterval.midpoint]
    linarith [R.interval.left_le_right]
  have hR_mid_right :
      R.interval.midpoint ≤ R.interval.right := by
    dsimp only [ParameterInterval.midpoint]
    linarith [R.interval.left_le_right]
  have hI_left :
      data.interval.left =
        data.interval.midpoint - data.interval.length / 2 := by
    simp [ParameterInterval.midpoint, ParameterInterval.length]
    ring
  have hI_right :
      data.interval.right =
        data.interval.midpoint + data.interval.length / 2 := by
    simp [ParameterInterval.midpoint, ParameterInterval.length]
    ring
  have hJ_left_lower :
      data.interval.left ≤ R.interval.midpoint - L / 2 := by
    have hmid_lower :
        data.interval.midpoint - data.interval.length / 16 ≤
          R.interval.midpoint := by
      linarith [(abs_le.mp hR_midpoint).1]
    have hlen_nonneg := data.interval.length_nonneg
    rw [hI_left]
    linarith
  have hJ_right_upper :
      R.interval.midpoint + L / 2 ≤ data.interval.right := by
    have hmid_upper :
        R.interval.midpoint ≤
          data.interval.midpoint + data.interval.length / 16 := by
      linarith [(abs_le.mp hR_midpoint).2]
    have hlen_nonneg := data.interval.length_nonneg
    rw [hI_right]
    linarith
  have hJ_left_nonneg :
      0 ≤ R.interval.midpoint - L / 2 :=
    data.interval.left_mem.1.trans hJ_left_lower
  have hJ_right_one :
      R.interval.midpoint + L / 2 ≤ 1 :=
    hJ_right_upper.trans data.interval.right_mem.2
  have hJ_left_right :
      R.interval.midpoint - L / 2 ≤
        R.interval.midpoint + L / 2 := by
    linarith
  let J : ParameterInterval :=
    { left := R.interval.midpoint - L / 2
      right := R.interval.midpoint + L / 2
      left_mem :=
        ⟨hJ_left_nonneg, hJ_left_right.trans hJ_right_one⟩
      right_mem :=
        ⟨hJ_left_nonneg.trans hJ_left_right, hJ_right_one⟩
      left_le_right := hJ_left_right }
  have hJ_length : J.length = L := by
    simp [J, ParameterInterval.length]
  have hJ_midpoint :
      J.midpoint = R.interval.midpoint := by
    simp [J, ParameterInterval.midpoint]
  let U :
      CurvilinearRectangle
        (C_s * delta) (C_R * t * Delta / delta) :=
    { function := R.function
      interval := J
      interval_length := by
        rw [hJ_length] }
  have hP_interval : P.interval.carrier ⊆ J.carrier := by
    intro x hx
    have hmin_x :
        min P.interval.left R.interval.left ≤ (x : ℝ) :=
      (min_le_left _ _).trans hx.1
    have hx_max :
        (x : ℝ) ≤ max P.interval.right R.interval.right :=
      hx.2.trans (le_max_left _ _)
    have hmin_mid :
        min P.interval.left R.interval.left ≤ R.interval.midpoint :=
      (min_le_right _ _).trans hR_left_mid
    have hmid_max :
        R.interval.midpoint ≤ max P.interval.right R.interval.right :=
      hR_mid_right.trans (le_max_right _ _)
    have hleft_distance :
        R.interval.midpoint - (x : ℝ) ≤ L₀ := by
      dsimp only [L₀]
      linarith
    have hright_distance :
        (x : ℝ) - R.interval.midpoint ≤ L₀ := by
      dsimp only [L₀]
      linarith
    change
      R.interval.midpoint - L / 2 ≤ (x : ℝ) ∧
        (x : ℝ) ≤ R.interval.midpoint + L / 2
    constructor <;> linarith
  have hR_interval : R.interval.carrier ⊆ J.carrier := by
    intro x hx
    have hmin_x :
        min P.interval.left R.interval.left ≤ (x : ℝ) :=
      (min_le_right _ _).trans hx.1
    have hx_max :
        (x : ℝ) ≤ max P.interval.right R.interval.right :=
      hx.2.trans (le_max_right _ _)
    have hmin_mid :
        min P.interval.left R.interval.left ≤ R.interval.midpoint :=
      (min_le_right _ _).trans hR_left_mid
    have hmid_max :
        R.interval.midpoint ≤ max P.interval.right R.interval.right :=
      hR_mid_right.trans (le_max_right _ _)
    have hleft_distance :
        R.interval.midpoint - (x : ℝ) ≤ L₀ := by
      dsimp only [L₀]
      linarith
    have hright_distance :
        (x : ℝ) - R.interval.midpoint ≤ L₀ := by
      dsimp only [L₀]
      linarith
    change
      R.interval.midpoint - L / 2 ≤ (x : ℝ) ∧
        (x : ℝ) ≤ R.interval.midpoint + L / 2
    constructor <;> linarith
  have hP_carrier : P.carrier ⊆ U.carrier := by
    intro q hq
    have hq_interval : q.1 ∈ P.interval.carrier := hq.1
    have hq_vertical : |q.2 - P.function q.1| ≤ delta := hq.2
    have hq_hull : q.1 ∈ P.intervalHullCarrier R := by
      exact
        ⟨(min_le_left _ _).trans hq_interval.1,
          hq_interval.2.trans (le_max_left _ _)⟩
    have hq_graph :
        |P.function q.1 - R.function q.1| ≤
          C * lambda ^ 3 * delta :=
      hGraph q.1 hq_hull
    have hq_triangle :
        |q.2 - R.function q.1| ≤
          |q.2 - P.function q.1| +
            |P.function q.1 - R.function q.1| := by
      have heq :
          q.2 - R.function q.1 =
            (q.2 - P.function q.1) +
              (P.function q.1 - R.function q.1) := by
        ring
      rw [heq]
      exact abs_add_le _ _
    have hq_bound :
        |q.2 - R.function q.1| ≤ C_s * delta := by
      calc
        |q.2 - R.function q.1|
            ≤ |q.2 - P.function q.1| +
                |P.function q.1 - R.function q.1| :=
          hq_triangle
        _ ≤ delta + C * lambda ^ 3 * delta :=
          add_le_add hq_vertical hq_graph
        _ = (1 + C * lambda ^ 3) * delta := by ring
        _ ≤ C_s * delta :=
          mul_le_mul_of_nonneg_right hCs_vertical hdelta_nonneg
    exact ⟨hP_interval hq_interval, hq_bound⟩
  have hR_carrier : R.carrier ⊆ U.carrier := by
    intro q hq
    have hq_bound : |q.2 - R.function q.1| ≤ C_s * delta := by
      calc
        |q.2 - R.function q.1| ≤ delta := hq.2
        _ = 1 * delta := by ring
        _ ≤ C_s * delta :=
          mul_le_mul_of_nonneg_right hCs_one hdelta_nonneg
    exact ⟨hR_interval hq.1, hq_bound⟩
  have hP_comparable : P.AreLambdaComparable R family C_s := by
    refine ⟨U, ?_, ?_⟩
    · exact hR_family
    · intro q hq
      rcases hq with hq | hq
      · exact hP_carrier hq
      · exact hR_carrier hq
  change ∃ hpE : p ∈ E₂,
    (data.rectangle ⟨p, hpE⟩).AreLambdaComparable R family C_s ∧
      ∃ U :
          CurvilinearRectangle
            (C_s * delta) (C_R * t * Delta / delta),
        U.function = R.function ∧
          U.interval.midpoint = R.interval.midpoint ∧
          R.carrier ⊆ U.carrier ∧
          data.point ⟨p, hpE⟩ ∈ U.carrier
  refine ⟨hpE, hP_comparable, U, rfl, ?_, hR_carrier, ?_⟩
  · exact hJ_midpoint
  · exact hP_carrier (data.point_mem_rectangle ⟨p, hpE⟩)

end Kakeya.Cinematic
