module

/-
# Absolute Count Bound for Grid Tube Families

Prove absolute count bounds for grid-mapped tube families and convert to
`IsDeltaSet`, with and without requiring metric separation.

## Main results

1. `grid_family_overlap_bound` — Integrated mass overlap bound via near/far
   decomposition, non-concentration, and `tubeFamily_overlap_bound`.
2. `grid_family_absolute_count` — `|S_x ∩ ball(L,ρ)| ≤ C_abs · ρ^σ` using
   `count_ball_from_mass`.
3. `grid_family_isDeltaSet_no_sep` — `IsDeltaSet` for the grid family **without**
   requiring 2r-separation, using `externalCoveringNumber ≤ cardinality`.
4. `grid_family_isDeltaSet` — `IsDeltaSet` with 2r-separation (tighter constant).

## Proof route

- Split `Y_x` at radius `r^κ`: near contribution ≤ 1/3 total via non-concentration.
- Far contribution bounded pointwise by `20000/r^κ` via `tubeFamily_overlap_bound`,
  then integrated via `bounded_overlap_sum_bound`.
- Combine: total ≤ (3/2)·(20000/r^κ)·ν(wide_tube) = (30000/r^κ)·ν(wide_tube).
- Use `count_ball_from_mass` to convert mass overlap + mass lower/upper bounds
  to an absolute tube count bound.
- Convert count bound to `IsDeltaSet` either via separation (cardinality = covering
  number) or without separation (covering number ≤ cardinality).

Whiteprint node: non-concentrated-absolute-count.
-/

public import MyLeanRepo.RadialBootstrapping.Basic
public import MyLeanRepo.RadialBootstrapping.TxDeltaSet
public import MyLeanRepo.RadialBootstrapping.FullMetricOverlap
public import MyLeanRepo.RadialBootstrapping.TubeFamilies

@[expose] public section

open MeasureTheory Metric Set Finset Classical
open scoped ENNReal NNReal

noncomputable section

namespace RadialBootstrapping

lemma grid_family_overlap_bound_gen
    (r κ : ℝ) (hr : 0 < r) (hκ : 0 < κ) (hκ_lt_one : κ < 1)
    (hr_small : 4 * r^(1 - κ) ≤ 1)
    (x : Point) (hxBall : x ∈ Metric.closedBall (0 : Point) 1)
    (S_x : Finset Line2) (hS_sub : S_x ⊆ tubeFamily r)
    (hS_through_x : ∀ L ∈ S_x, x ∈ tube (2 * r) L)
    (Y_x : Set Point) (hY_meas : MeasurableSet Y_x)
    (hY_sub : Y_x ⊆ Metric.closedBall (0 : Point) 1)
    (ν : Measure Point) [IsProbabilityMeasure ν]
    (A : Line2 → Set Point)
    (hA_meas : ∀ L' ∈ S_x, MeasurableSet (A L'))
    (hA_sub : ∀ L' ∈ S_x, A L' ⊆ tube (2 * r) L')
    (hA_Y : ∀ L' ∈ S_x, A L' ⊆ Y_x)
    (h_nonconc : ∀ L' ∈ S_x,
        ν (A L' ∩ Metric.ball x (Real.rpow r κ)) ≤
          (1 / 3 : ENNReal) * ν (A L'))
    (L : Line2) (ρ : ℝ) (hρ : r ≤ ρ) (hρ1 : ρ ≤ 1) :
    ∑ L' ∈ S_x.filter (fun L' =>
        (A L' ⊆ tube (2 * r + 4 * ρ) L)),
        ν (A L') ≤
      ENNReal.ofReal (30000 / Real.rpow r κ) *
        ν (tube (2 * r + 4 * ρ) L ∩ Y_x) := by
  classical
  let ξ : ℝ := Real.rpow r κ
  have hξ_pos : 0 < ξ := Real.rpow_pos_of_pos hr κ

  have h_small : 4 * r / ξ ≤ 1 := by
    set a : ℝ := Real.rpow r (1 - κ) with ha
    set b : ℝ := Real.rpow r κ with hb
    have hb_pos : 0 < b := Real.rpow_pos_of_pos hr κ
    have h_mul : a * b = r := by
      calc a * b = Real.rpow r (1 - κ) * Real.rpow r κ := by simp [ha, hb]
        _ = Real.rpow r ((1 - κ) + κ) := (Real.rpow_add hr (1 - κ) κ).symm
        _ = r := by simp
    have h23 : 4 * r / b = 4 * a := by
      have h : 4 * r / b = 4 * (a * b) / b := by rw [h_mul]
      rw [h]; field_simp [hb_pos.ne'] <;> ring
    rw [h23]; exact hr_small

  let S_filt : Finset Line2 := S_x.filter (fun L' => A L' ⊆ tube (2 * r + 4 * ρ) L)
  let W : Set Point := tube (2 * r + 4 * ρ) L ∩ Y_x
  have hW_meas : MeasurableSet W := (tube_measurableSet (2 * r + 4 * ρ) L).inter hY_meas

  let Bx : Set Point := Metric.ball x ξ
  have hBx_meas : MeasurableSet Bx := Metric.isOpen_ball.measurableSet
  let Y_far : Set Point := Y_x \ Bx
  have hY_far_meas : MeasurableSet Y_far := hY_meas.diff hBx_meas

  let one_third : ENNReal := ENNReal.ofReal (1 / 3 : ℝ)
  let two_thirds : ENNReal := ENNReal.ofReal (2 / 3 : ℝ)
  let three_halves : ENNReal := ENNReal.ofReal (3 / 2 : ℝ)
  have h13_pos : 0 ≤ (1 / 3 : ℝ) := by norm_num
  have h23_pos : 0 ≤ (2 / 3 : ℝ) := by norm_num
  have h32_pos : 0 ≤ (3 / 2 : ℝ) := by norm_num
  have h_add13 : one_third + two_thirds = 1 := by
    have h : one_third + two_thirds = ENNReal.ofReal ((1 / 3 : ℝ) + (2 / 3 : ℝ)) := by
      rw [ENNReal.ofReal_add h13_pos h23_pos] <;> rfl
    rw [h]; have h2 : (1 / 3 : ℝ) + (2 / 3 : ℝ) = 1 := by norm_num
    rw [h2] <;> simp
  have h_mul32 : three_halves * two_thirds = 1 := by
    have h : three_halves * two_thirds = ENNReal.ofReal ((3 / 2 : ℝ) * (2 / 3 : ℝ)) := by
      rw [ENNReal.ofReal_mul h32_pos] <;> rfl
    rw [h]; have h2 : (3 / 2 : ℝ) * (2 / 3 : ℝ) = 1 := by norm_num
    rw [h2] <;> simp

  have hBx_eq : Bx = Metric.ball x (Real.rpow r κ) := by rfl

  have h_near : ∑ L' ∈ S_filt, ν (A L' ∩ Bx) ≤
      one_third * ∑ L' ∈ S_filt, ν (A L') := by
    have h1 : ∀ L' ∈ S_filt, ν (A L' ∩ Bx) ≤ one_third * ν (A L') := by
      intro L' hL'
      have hL'_Sx : L' ∈ S_x := (Finset.mem_filter.mp hL').1
      have h_orig := h_nonconc L' hL'_Sx
      have h_eq : Bx = Metric.ball x (Real.rpow r κ) := by rfl
      rw [h_eq]
      simpa [one_third] using h_orig
    calc
      ∑ L' ∈ S_filt, ν (A L' ∩ Bx)
        ≤ ∑ L' ∈ S_filt, one_third * ν (A L') := Finset.sum_le_sum h1
    _ = one_third * ∑ L' ∈ S_filt, ν (A L') := by rw [Finset.mul_sum] <;> ring

  let B_nat : ℕ := Nat.floor (20000 / ξ)
  have hB_nat_pos : 0 < B_nat := by
    apply Nat.floor_pos.mpr
    have h6 : ξ ≤ 1 := Real.rpow_le_one hr.le (by linarith) hκ.le
    have h8 : 1 ≤ 20000 / ξ := by
      have h9 : 20000 / ξ ≥ 20000 / 1 := by gcongr <;> linarith
      norm_num at h9 ⊢ <;> linarith
    exact h8

  have h_overlap_far : ∀ y ∈ Y_far,
      (S_filt.filter (fun L' => y ∈ A L')).card ≤ B_nat := by
    intro y hy
    have hyY : y ∈ Y_x := hy.1
    have hy_far : y ∉ Bx := hy.2
    have hdist : ξ ≤ dist x y := by
      have h' : ¬(dist y x < ξ) := by
        intro hlt; have h_in : y ∈ Bx := by simpa [Bx, Metric.mem_ball] using hlt
        exact hy_far h_in
      have h_comm : dist x y = dist y x := dist_comm x y
      linarith
    have hyBall : y ∈ Metric.closedBall (0 : Point) 1 := hY_sub hyY
    have h1 : ((tubeFamily r).filter (fun L' =>
          x ∈ tube (2 * r) L' ∧ y ∈ tube (2 * r) L')).card ≤ B_nat := by
      have h2 : ((tubeFamily r).filter (fun L' =>
          x ∈ tube (2 * r) L' ∧ y ∈ tube (2 * r) L')).card ≤ (20000 / ξ : ℝ) :=
        tubeFamily_overlap_bound r hr (by linarith) (hξ := hξ_pos) h_small x y hdist hxBall hyBall
      exact Nat.le_floor h2
    have h3 : S_filt.filter (fun L' => y ∈ A L') ⊆
        (tubeFamily r).filter (fun L' => x ∈ tube (2 * r) L' ∧ y ∈ tube (2 * r) L') := by
      intro L' hL'
      have h4 : L' ∈ S_filt := (Finset.mem_filter.mp hL').1
      have h5 : L' ∈ S_x := (Finset.mem_filter.mp h4).1
      have h6 : L' ∈ tubeFamily r := hS_sub h5
      have h7 : y ∈ A L' := (Finset.mem_filter.mp hL').2
      have h8 : y ∈ tube (2 * r) L' := hA_sub L' h5 h7
      have h9 : x ∈ tube (2 * r) L' := hS_through_x L' h5
      exact Finset.mem_filter.mpr ⟨h6, ⟨h9, h8⟩⟩
    exact Nat.le_trans (Finset.card_le_card h3) h1

  have h_pointwise : ∀ (y : Point),
      ∑ L' ∈ S_filt, Set.indicator (A L' ∩ Y_far) (fun (_ : Point) => (1 : ENNReal)) y ≤
        (B_nat : ENNReal) * Set.indicator W (fun (_ : Point) => (1 : ENNReal)) y := by
    intro y
    by_cases hyW : y ∈ W
    · have h_indW : Set.indicator W (fun (_ : Point) => (1 : ENNReal)) y = 1 := by
        simp [Set.indicator_apply, hyW]
      rw [h_indW]
      by_cases hyfar : y ∈ Y_far
      · have h_filter : (S_filt.filter (fun L' => y ∈ A L' ∩ Y_far)).card ≤ B_nat := by
          have h_sub : S_filt.filter (fun L' => y ∈ A L' ∩ Y_far) ⊆
              S_filt.filter (fun L' => y ∈ A L') := by
            intro L' hL'
            have h1 : L' ∈ S_filt := (Finset.mem_filter.mp hL').1
            have h2 : y ∈ A L' := (Finset.mem_filter.mp hL').2.1
            exact Finset.mem_filter.mpr ⟨h1, h2⟩
          have h3 : (S_filt.filter (fun L' => y ∈ A L')).card ≤ B_nat := h_overlap_far y hyfar
          exact Nat.le_trans (Finset.card_le_card h_sub) h3
        have h_sum_eq : ∑ L' ∈ S_filt, Set.indicator (A L' ∩ Y_far) (fun (_ : Point) => (1 : ENNReal)) y =
            ((S_filt.filter (fun L' => y ∈ A L' ∩ Y_far)).card : ENNReal) := by
          have h_step1 : ∑ L' ∈ S_filt, Set.indicator (A L' ∩ Y_far) (fun (_ : Point) => (1 : ENNReal)) y =
              ∑ L' ∈ S_filt, (if y ∈ A L' ∩ Y_far then (1 : ENNReal) else 0) := by
            apply Finset.sum_congr rfl
            intro L' _
            simp [Set.indicator_apply]
          rw [h_step1]
          have h_step2 : ∑ L' ∈ S_filt, (if y ∈ A L' ∩ Y_far then (1 : ENNReal) else 0) =
              (S_filt.filter (fun L' => y ∈ A L' ∩ Y_far)).card := by
            rw [Finset.sum_ite] <;> simp
          rw [h_step2] <;> norm_cast
        rw [h_sum_eq]
        have h_goal : ((S_filt.filter (fun L' => y ∈ A L' ∩ Y_far)).card : ENNReal) ≤ (B_nat : ENNReal) := by
          exact_mod_cast h_filter
        simpa using h_goal
      · have h_all : ∀ L' ∈ S_filt, y ∉ A L' ∩ Y_far := by
          intro L' _ hz; exact hyfar hz.2
        have h_sum_zero : ∑ L' ∈ S_filt, Set.indicator (A L' ∩ Y_far) (fun (_ : Point) => (1 : ENNReal)) y = 0 := by
          apply Finset.sum_eq_zero
          intro L' hL'
          have h6 : y ∉ A L' ∩ Y_far := h_all L' hL'
          simp [Set.indicator_apply, h6]
        rw [h_sum_zero] <;> simp
    · have h_all : ∀ L' ∈ S_filt, y ∉ A L' ∩ Y_far := by
        intro L' hL' hz
        have h_cont : A L' ⊆ tube (2 * r + 4 * ρ) L := (Finset.mem_filter.mp hL').2
        have hy_A : y ∈ A L' := hz.1
        have hy_Yx : y ∈ Y_x := hz.2.1
        have hy_W1 : y ∈ tube (2 * r + 4 * ρ) L := h_cont hy_A
        exact hyW ⟨hy_W1, hy_Yx⟩
      have h_indW : Set.indicator W (fun (_ : Point) => (1 : ENNReal)) y = 0 := by
        simp [Set.indicator_apply, hyW]
      rw [h_indW]
      have h_sum_zero : ∑ L' ∈ S_filt, Set.indicator (A L' ∩ Y_far) (fun (_ : Point) => (1 : ENNReal)) y = 0 := by
        apply Finset.sum_eq_zero
        intro L' hL'
        have h6 : y ∉ A L' ∩ Y_far := h_all L' hL'
        simp [Set.indicator_apply, h6]
      rw [h_sum_zero] <;> simp

  have h_far_sum : ∑ L' ∈ S_filt, ν (A L' ∩ Y_far) ≤
      (B_nat : ENNReal) * ν W := by
    have h_meas' : ∀ L' ∈ S_filt, Measurable (Set.indicator (A L' ∩ Y_far) (fun (_ : Point) => (1 : ENNReal))) := by
      intro L' hL'
      have hL'_Sx : L' ∈ S_x := (Finset.mem_filter.mp hL').1
      exact Measurable.indicator measurable_const ((hA_meas L' hL'_Sx).inter hY_far_meas)
    have h1 : ∑ L' ∈ S_filt, ν (A L' ∩ Y_far) =
        ∫⁻ y, ∑ L' ∈ S_filt, Set.indicator (A L' ∩ Y_far) (fun (_ : Point) => (1 : ENNReal)) y ∂ν := by
      rw [lintegral_finsetSum S_filt h_meas']
      apply Finset.sum_congr rfl
      intro L' hL'
      have hL'_Sx : L' ∈ S_x := (Finset.mem_filter.mp hL').1
      have h_meas_set : MeasurableSet (A L' ∩ Y_far) := (hA_meas L' hL'_Sx).inter hY_far_meas
      have h' := MeasureTheory.lintegral_indicator_const₀ (μ := ν) h_meas_set.nullMeasurableSet (1 : ENNReal)
      simpa using h'.symm
    rw [h1]
    have h2 : ∫⁻ y, ∑ L' ∈ S_filt, Set.indicator (A L' ∩ Y_far) (fun (_ : Point) => (1 : ENNReal)) y ∂ν ≤
        ∫⁻ y, (B_nat : ENNReal) * Set.indicator W (fun (_ : Point) => (1 : ENNReal)) y ∂ν :=
      lintegral_mono h_pointwise
    have h3 : ∫⁻ y, (B_nat : ENNReal) * Set.indicator W (fun (_ : Point) => (1 : ENNReal)) y ∂ν =
        (B_nat : ENNReal) * ν W := by
      have h_eq : (fun y : Point => (B_nat : ENNReal) * Set.indicator W (fun (_ : Point) => (1 : ENNReal)) y) =
          Set.indicator W (fun (_ : Point) => (B_nat : ENNReal)) := by
        funext y
        by_cases hy : y ∈ W
        · have h_left : (B_nat : ENNReal) * Set.indicator W (fun (_ : Point) => (1 : ENNReal)) y = (B_nat : ENNReal) := by
            simp [Set.indicator_apply, hy]
          have h_right : Set.indicator W (fun (_ : Point) => (B_nat : ENNReal)) y = (B_nat : ENNReal) := by
            simp [Set.indicator_apply, hy]
          rw [h_left, h_right]
        · have h_left : (B_nat : ENNReal) * Set.indicator W (fun (_ : Point) => (1 : ENNReal)) y = 0 := by
            simp [Set.indicator_apply, hy]
          have h_right : Set.indicator W (fun (_ : Point) => (B_nat : ENNReal)) y = 0 := by
            simp [Set.indicator_apply, hy]
          rw [h_left, h_right]
      rw [h_eq]
      exact MeasureTheory.lintegral_indicator_const₀ hW_meas.nullMeasurableSet (B_nat : ENNReal)
    rw [h3] at h2
    exact h2

  have h_decomp : ∀ L' ∈ S_filt,
      ν (A L') = ν (A L' ∩ Bx) + ν (A L' ∩ Y_far) := by
    intro L' hL'
    have hL'_Sx : L' ∈ S_x := (Finset.mem_filter.mp hL').1
    have h_disj : Disjoint (A L' ∩ Bx) (A L' ∩ Y_far) := by
      rw [Set.disjoint_left]
      intro z hz1 hz2
      have hz_in_Bx : z ∈ Bx := hz1.2
      have hz_in_Yfar : z ∈ Y_far := hz2.2
      exact hz_in_Yfar.2 hz_in_Bx
    have hz_Yx : ∀ z ∈ A L', z ∈ Y_x := fun z hz => hA_Y L' hL'_Sx hz
    have h_union : (A L' ∩ Bx) ∪ (A L' ∩ Y_far) = A L' := by
      ext z
      simp only [Y_far, Set.mem_union, Set.mem_inter_iff, Set.mem_diff]
      constructor
      · rintro (h | h) <;> exact h.1
      · intro hz
        by_cases h : z ∈ Bx
        · exact Or.inl ⟨hz, h⟩
        · exact Or.inr ⟨hz, hz_Yx z hz, h⟩
    have h_meas1 : MeasurableSet (A L' ∩ Bx) := (hA_meas L' hL'_Sx).inter hBx_meas
    have h_meas2 : MeasurableSet (A L' ∩ Y_far) := (hA_meas L' hL'_Sx).inter hY_far_meas
    have h : ν ((A L' ∩ Bx) ∪ (A L' ∩ Y_far)) =
        ν (A L' ∩ Bx) + ν (A L' ∩ Y_far) := by
      exact measure_union h_disj h_meas2
    have h4 : ν (A L') = ν ((A L' ∩ Bx) ∪ (A L' ∩ Y_far)) := by rw [h_union]
    rw [h4, h]

  have h_total : ∑ L' ∈ S_filt, ν (A L') =
      ∑ L' ∈ S_filt, ν (A L' ∩ Bx) + ∑ L' ∈ S_filt, ν (A L' ∩ Y_far) := by
    rw [Finset.sum_congr rfl h_decomp, Finset.sum_add_distrib]

  let S_total : ENNReal := ∑ L' ∈ S_filt, ν (A L')
  have hS_finite : S_total ≠ ⊤ := by
    have h_le1 : ∀ L' ∈ S_filt, ν (A L') ≤ 1 := by
      intro L' _
      have h1 : ν (A L') ≤ ν Set.univ := measure_mono (Set.subset_univ _)
      have h2 : ν Set.univ = 1 := by simpa using IsProbabilityMeasure.measure_univ ν
      rw [h2] at h1; exact h1
    have h : S_total ≤ (S_filt.card : ENNReal) := by
      calc S_total ≤ ∑ L' ∈ S_filt, (1 : ENNReal) := Finset.sum_le_sum h_le1
        _ = (S_filt.card : ENNReal) := by simp
    exact ne_top_of_le_ne_top (by exact ENNReal.natCast_ne_top #S_filt) h

  have h_decomp3 : S_total = one_third * S_total + two_thirds * S_total := by
    calc S_total = 1 * S_total := by ring
      _ = (one_third + two_thirds) * S_total := by rw [h_add13]
      _ = one_third * S_total + two_thirds * S_total := by rw [add_mul]

  have h_main2 : S_total ≤ one_third * S_total + (B_nat : ENNReal) * ν W := by
    rw [show S_total = ∑ L' ∈ S_filt, ν (A L') from rfl, h_total]
    have h_near2 : ∑ L' ∈ S_filt, ν (A L' ∩ Bx) ≤
        one_third * (∑ L' ∈ S_filt, ν (A L' ∩ Bx) + ∑ L' ∈ S_filt, ν (A L' ∩ Y_far)) := by
      rw [←h_total]; exact h_near
    exact add_le_add h_near2 h_far_sum

  have h_final : two_thirds * S_total ≤ (B_nat : ENNReal) * ν W := by
    have h_main3 : one_third * S_total + two_thirds * S_total ≤
        one_third * S_total + (B_nat : ENNReal) * ν W := by
      have h_eq : one_third * S_total + two_thirds * S_total = S_total := h_decomp3.symm
      rw [h_eq]; exact h_main2
    have h13_ne_top : one_third ≠ ⊤ := by simp [one_third, ENNReal.ofReal_ne_top]
    have h13_finite : one_third * S_total ≠ ⊤ := ENNReal.mul_ne_top h13_ne_top hS_finite
    exact ENNReal.add_le_add_iff_left h13_finite |>.mp h_main3

  have h_result : S_total ≤ three_halves * (B_nat : ENNReal) * ν W := by
    calc S_total = (three_halves * two_thirds) * S_total := by rw [h_mul32] <;> ring
      _ = three_halves * (two_thirds * S_total) := by ring
      _ ≤ three_halves * ((B_nat : ENNReal) * ν W) := by gcongr
      _ = three_halves * (B_nat : ENNReal) * ν W := by ring

  have h_B_bound : (B_nat : ℝ) ≤ 20000 / ξ := Nat.floor_le (by positivity)
  have h_ov_bound : three_halves * (B_nat : ENNReal) ≤ ENNReal.ofReal (30000 / ξ) := by
    have h_pos : 0 ≤ (3 / 2 : ℝ) * (B_nat : ℝ) := by positivity
    have h2 : (B_nat : ENNReal) = ENNReal.ofReal (B_nat : ℝ) := by simp
    have h1 : three_halves * (B_nat : ENNReal) =
        ENNReal.ofReal ((3 / 2 : ℝ) * (B_nat : ℝ)) := by
      rw [h2, ENNReal.ofReal_mul h32_pos] <;> rfl
    rw [h1]
    have h3 : (3 / 2 : ℝ) * (B_nat : ℝ) ≤ (3 / 2 : ℝ) * (20000 / ξ) := by gcongr
    have h4 : (3 / 2 : ℝ) * (20000 / ξ) = 30000 / ξ := by ring
    rw [h4] at h3
    exact ENNReal.ofReal_le_ofReal h3

  calc S_total ≤ three_halves * (B_nat : ENNReal) * ν W := h_result
    _ ≤ ENNReal.ofReal (30000 / ξ) * ν W := by gcongr

end RadialBootstrapping
