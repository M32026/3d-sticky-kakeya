import MyLeanRepo.Kakeya.Assouad.WZ1.PaperPackingRefinement
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Cardinality of an essentially distinct paper line family
-/

noncomputable section

namespace Kakeya.Assouad

open Set Finset

attribute [local instance] Classical.propDecidable

/-- Axis zero points of two line-class tubes are less than one unit apart. -/
lemma paper_axis_dist_lt_one
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (hline : WZ1PaperIsLineClass family)
    (first second : Fin family.card) :
    dist
        (wz1TubeAxisZeroPoint (family.tube second))
        (wz1TubeAxisZeroPoint (family.tube first)) <
      1 := by
  let difference :=
    wz1TubeAxisZeroPoint (family.tube second) -
      wz1TubeAxisZeroPoint (family.tube first)
  have hposition :
      ∀ index,
        |wz1TubeAxisZeroPoint
            (family.tube index) (0 : Fin 3)| ≤ 1 / 3 ∧
          |wz1TubeAxisZeroPoint
            (family.tube index) (1 : Fin 3)| ≤ 1 / 3 := by
    intro index
    exact ⟨(hline index).2.1, (hline index).2.2⟩
  have hzero :
      ∀ index,
        wz1TubeAxisZeroPoint
            (family.tube index) (2 : Fin 3) =
          0 := by
    intro index
    exact
      wz1TubeAxisZeroPoint_coord_two
        (family.tube index) (hline index).vertical
  have hcoord_zero : |difference (0 : Fin 3)| ≤ 2 / 3 := by
    calc
      |difference (0 : Fin 3)| =
          |wz1TubeAxisZeroPoint
              (family.tube second) (0 : Fin 3) -
            wz1TubeAxisZeroPoint
              (family.tube first) (0 : Fin 3)| := by
        simp [difference]
      _ ≤
          |wz1TubeAxisZeroPoint
            (family.tube second) (0 : Fin 3)| +
          |wz1TubeAxisZeroPoint
            (family.tube first) (0 : Fin 3)| :=
        abs_sub _ _
      _ ≤ 1 / 3 + 1 / 3 := by
        linarith [(hposition second).1, (hposition first).1]
      _ = 2 / 3 := by norm_num
  have hcoord_one : |difference (1 : Fin 3)| ≤ 2 / 3 := by
    calc
      |difference (1 : Fin 3)| =
          |wz1TubeAxisZeroPoint
              (family.tube second) (1 : Fin 3) -
            wz1TubeAxisZeroPoint
              (family.tube first) (1 : Fin 3)| := by
        simp [difference]
      _ ≤
          |wz1TubeAxisZeroPoint
            (family.tube second) (1 : Fin 3)| +
          |wz1TubeAxisZeroPoint
            (family.tube first) (1 : Fin 3)| :=
        abs_sub _ _
      _ ≤ 1 / 3 + 1 / 3 := by
        linarith [(hposition second).2, (hposition first).2]
      _ = 2 / 3 := by norm_num
  have hcoord_two : difference (2 : Fin 3) = 0 := by
    simp [difference, hzero second, hzero first]
  have hnorm_sq : ‖difference‖ ^ 2 ≤ 8 / 9 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    have hsum :
        ∑ coordinate : Fin 3, difference coordinate ^ 2 =
          difference 0 ^ 2 + difference 1 ^ 2 +
            difference 2 ^ 2 := by
      simp [Fin.sum_univ_succ]
      ring
    rw [hsum, hcoord_two]
    have hzero_sq : |difference 0| ^ 2 ≤ (2 / 3 : ℝ) ^ 2 := by
      gcongr
    have hone_sq : |difference 1| ^ 2 ≤ (2 / 3 : ℝ) ^ 2 := by
      gcongr
    rw [sq_abs] at hzero_sq hone_sq
    nlinarith
  have hnorm : ‖difference‖ < 1 := by
    nlinarith [norm_nonneg difference]
  simpa [dist_eq_norm, difference] using hnorm

/-- Polynomial cardinality bound for an essentially distinct line family. -/
lemma paper_essentially_distinct_card_bound_nat
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (hed : WZ1PaperIsEssentiallyDistinct family)
    (hline : WZ1PaperIsLineClass family)
    (hdelta : 0 < delta)
    (_hdelta_one : delta ≤ 1) :
    family.card ≤ (2 * Nat.ceil (80 / delta) + 1) ^ 5 := by
  by_cases hempty : family.card = 0
  · simp [hempty]
  · let reference : Fin family.card :=
      ⟨0, Nat.pos_of_ne_zero hempty⟩
    have hall :
        (Finset.univ.filter fun index : Fin family.card =>
          wz1PaperLineDistance
              (family.tube index)
              (family.tube reference) ≤
            10) =
          Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro index
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hdistance :=
        paper_axis_dist_lt_one hline reference index
      have hangle :=
        InnerProductGeometry.angle_le_pi
          (wz1PaperDirection (family.tube index))
          (wz1PaperDirection (family.tube reference))
      have hpi : Real.pi < 4 := Real.pi_lt_four
      dsimp only [wz1PaperLineDistance]
      linarith
    have hbound :=
      tube_packing_bound_general
        hed hline hdelta 10 (by norm_num) reference
    rw [hall] at hbound
    have hscale : 8 * (10 : ℝ) / delta = 80 / delta := by
      ring
    rw [hscale] at hbound
    simpa using hbound

/-- Logarithmic consequence of the polynomial paper-line packing bound. -/
lemma paper_log_card_bound
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (hed : WZ1PaperIsEssentiallyDistinct family)
    (hline : WZ1PaperIsLineClass family)
    (hdelta : 0 < delta)
    (hdelta_one : delta ≤ 1)
    (h_nonempty : 0 < family.card) :
    (Nat.log 2 family.card + 1 : ℝ) ≤
      (5 / Real.log 2) * Real.log (1 / delta) +
        (5 * Real.log 163 / Real.log 2 + 1) := by
  have hcard :=
    paper_essentially_distinct_card_bound_nat
      hed hline hdelta hdelta_one
  let bound : ℕ := 2 * Nat.ceil (80 / delta) + 1
  have hbound_pos : 0 < bound := by positivity
  have hlog_two : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hceil_pos : 0 < Nat.ceil (80 / delta) := by
    apply Nat.ceil_pos.mpr
    positivity
  have hceil_lt :
      (Nat.ceil (80 / delta) : ℝ) < 80 / delta + 1 := by
    have hpred :
        Nat.ceil (80 / delta) - 1 <
          Nat.ceil (80 / delta) := by omega
    have hlt :
        ((Nat.ceil (80 / delta) - 1 : ℕ) : ℝ) <
          80 / delta :=
      Nat.lt_ceil.mp hpred
    have hcast :
        ((Nat.ceil (80 / delta) - 1 : ℕ) : ℝ) =
          (Nat.ceil (80 / delta) : ℝ) - 1 := by
      simp [hceil_pos]
    rw [hcast] at hlt
    linarith
  have hbound_le : (bound : ℝ) ≤ 163 / delta := by
    have hbound_cast :
        (bound : ℝ) =
          2 * (Nat.ceil (80 / delta) : ℝ) + 1 := by
      simp [bound]
    rw [hbound_cast]
    have hthree : 3 ≤ 3 / delta := by
      calc
        3 = 3 / 1 := by norm_num
        _ ≤ 3 / delta := by gcongr
    have hmiddle :
        2 * (Nat.ceil (80 / delta) : ℝ) + 1 <
          160 / delta + 3 := by
      have hscaled :
          2 * (Nat.ceil (80 / delta) : ℝ) + 1 <
            2 * (80 / delta + 1) + 1 := by
        gcongr
      have hrearrange :
          2 * (80 / delta + 1) + 1 =
            160 / delta + 3 := by ring
      rwa [hrearrange] at hscaled
    calc
      2 * (Nat.ceil (80 / delta) : ℝ) + 1
          ≤ 160 / delta + 3 := hmiddle.le
      _ ≤ 160 / delta + 3 / delta := by gcongr
      _ = 163 / delta := by
        field_simp [hdelta.ne']
        ring
  have hnat_log :
      (Nat.log 2 family.card : ℝ) ≤
        Real.log (family.card : ℝ) / Real.log 2 := by
    have hpow :
        (2 : ℕ) ^ Nat.log 2 family.card ≤ family.card :=
      Nat.pow_log_le_self 2 h_nonempty.ne'
    have hpow_real :
        (2 : ℝ) ^ Nat.log 2 family.card ≤
          (family.card : ℝ) := by
      exact_mod_cast hpow
    have hlog :=
      Real.log_le_log (by positivity) hpow_real
    rw [Real.log_pow] at hlog
    exact (le_div_iff₀ hlog_two).mpr (by simpa using hlog)
  have hfamily_log :
      Real.log (family.card : ℝ) ≤
        Real.log ((bound : ℝ) ^ 5) :=
    Real.log_le_log
      (by exact_mod_cast h_nonempty)
      (by exact_mod_cast hcard)
  have hbound_log :
      Real.log (bound : ℝ) ≤ Real.log (163 / delta) :=
    Real.log_le_log (by exact_mod_cast hbound_pos) hbound_le
  have hquotient_log :
      Real.log (163 / delta) =
        Real.log 163 + Real.log (1 / delta) := by
    rw [Real.log_div (by norm_num) hdelta.ne',
      Real.log_div (by norm_num) hdelta.ne', Real.log_one]
    ring
  calc
    (Nat.log 2 family.card + 1 : ℝ)
        ≤ Real.log (family.card : ℝ) / Real.log 2 + 1 := by
      linarith
    _ ≤ Real.log ((bound : ℝ) ^ 5) / Real.log 2 + 1 := by
      gcongr
    _ = 5 * Real.log (bound : ℝ) / Real.log 2 + 1 := by
      rw [Real.log_pow]
      ring
    _ ≤ 5 * Real.log (163 / delta) / Real.log 2 + 1 := by
      gcongr
    _ = (5 / Real.log 2) * Real.log (1 / delta) +
          (5 * Real.log 163 / Real.log 2 + 1) := by
      rw [hquotient_log]
      ring

/-- Explicit log-cardinality bound from the five-dimensional line packing. -/
lemma explicit_card_log_bound
    {delta : ℝ}
    (hdelta : 0 < delta)
    (hdelta_one : delta ≤ 1)
    {cardinality : ℕ}
    (hcard :
      cardinality ≤
        (2 * Nat.ceil (80 / delta) + 1) ^ 5) :
    (Nat.log 2 (2 * cardinality) + 1 : ℝ) ≤
      (5 / Real.log 2) * Real.log (1 / delta) +
        (5 * Real.log 163 / Real.log 2 + 2) := by
  let bound : ℕ := 2 * Nat.ceil (80 / delta) + 1
  have hbound_pos : 0 < bound := by positivity
  have hlog_two : 0 < Real.log 2 :=
    Real.log_pos (by norm_num)
  have hceil_pos : 0 < Nat.ceil (80 / delta) := by
    apply Nat.ceil_pos.mpr
    positivity
  have hceil_lt :
      (Nat.ceil (80 / delta) : ℝ) < 80 / delta + 1 := by
    have hpred :
        Nat.ceil (80 / delta) - 1 <
          Nat.ceil (80 / delta) := by
      omega
    have hlt :
        ((Nat.ceil (80 / delta) - 1 : ℕ) : ℝ) <
          80 / delta :=
      Nat.lt_ceil.mp hpred
    have hcast :
        ((Nat.ceil (80 / delta) - 1 : ℕ) : ℝ) =
          (Nat.ceil (80 / delta) : ℝ) - 1 := by
      simp [hceil_pos]
    rw [hcast] at hlt
    linarith
  have hbound_le : (bound : ℝ) ≤ 163 / delta := by
    have hbound_cast :
        (bound : ℝ) =
          2 * (Nat.ceil (80 / delta) : ℝ) + 1 := by
      simp [bound]
    rw [hbound_cast]
    have hthree : 3 ≤ 3 / delta := by
      calc
        (3 : ℝ) = 3 / 1 := by norm_num
        _ ≤ 3 / delta := by gcongr
    have hmiddle :
        2 * (Nat.ceil (80 / delta) : ℝ) + 1 <
          160 / delta + 3 := by
      have hscaled :
          2 * (Nat.ceil (80 / delta) : ℝ) + 1 <
            2 * (80 / delta + 1) + 1 := by
        gcongr
      have hrearrange :
          2 * (80 / delta + 1) + 1 =
            160 / delta + 3 := by
        ring
      rwa [hrearrange] at hscaled
    calc
      2 * (Nat.ceil (80 / delta) : ℝ) + 1
          ≤ 160 / delta + 3 := hmiddle.le
      _ ≤ 160 / delta + 3 / delta := by gcongr
      _ = 163 / delta := by
        field_simp [hdelta.ne'] <;> ring
  by_cases hcard0 : cardinality = 0
  · have h_log_nonneg : 0 ≤ Real.log (1 / delta) := by
      apply Real.log_nonneg
      apply one_le_one_div
      · exact hdelta
      · exact hdelta_one
    have h_goal :
        (1 : ℝ) ≤
          (5 / Real.log 2) * Real.log (1 / delta) +
            (5 * Real.log 163 / Real.log 2 + 2) := by
      have h6 :
          0 ≤
            (5 / Real.log 2) * Real.log (1 / delta) := by
        positivity
      have h7 :
          (1 : ℝ) ≤
            5 * Real.log 163 / Real.log 2 + 2 := by
        have h8 : 0 < Real.log 163 :=
          Real.log_pos (by norm_num)
        have h10 :
            0 < 5 * Real.log 163 / Real.log 2 := by
          positivity
        linarith
      linarith
    have h9 :
        (Nat.log 2 (2 * cardinality) + 1 : ℝ) = 1 := by
      rw [hcard0]
      simp
    rw [h9]
    exact h_goal
  · have hcard_pos : 0 < cardinality :=
      Nat.pos_of_ne_zero hcard0
    have h2card_pos : 0 < 2 * cardinality := by positivity
    have h_nat_log :
        (Nat.log 2 (2 * cardinality) : ℝ) ≤
          Real.log ((2 * cardinality : ℕ) : ℝ) /
            Real.log 2 := by
      have hpow :
          (2 : ℕ) ^ Nat.log 2 (2 * cardinality) ≤
            2 * cardinality :=
        Nat.pow_log_le_self 2 h2card_pos.ne'
      have hpow_real :
          (2 : ℝ) ^ Nat.log 2 (2 * cardinality) ≤
            ((2 * cardinality : ℕ) : ℝ) := by
        exact_mod_cast hpow
      have hlog :=
        Real.log_le_log (by positivity) hpow_real
      rw [Real.log_pow] at hlog
      exact (le_div_iff₀ hlog_two).mpr (by simpa using hlog)
    have hcard_real_le :
        (cardinality : ℝ) ≤ (bound : ℝ) ^ 5 := by
      exact_mod_cast hcard
    have h2card_real_le :
        ((2 * cardinality : ℕ) : ℝ) ≤
          2 * ((bound : ℝ) ^ 5) := by
      have h :
          2 * (cardinality : ℝ) ≤
            2 * ((bound : ℝ) ^ 5) :=
        mul_le_mul_of_nonneg_left hcard_real_le (by norm_num)
      exact_mod_cast h
    have hlog_bound :
        Real.log ((2 * cardinality : ℕ) : ℝ) ≤
          Real.log (2 * ((bound : ℝ) ^ 5)) :=
      Real.log_le_log
        (by exact_mod_cast h2card_pos) h2card_real_le
    have hlog_bound2 :
        Real.log (2 * ((bound : ℝ) ^ 5)) =
          Real.log 2 + 5 * Real.log (bound : ℝ) := by
      rw [Real.log_mul (by norm_num) (by positivity),
        Real.log_pow] <;> ring
    have hbound_log :
        Real.log (bound : ℝ) ≤ Real.log (163 / delta) :=
      Real.log_le_log (by exact_mod_cast hbound_pos) hbound_le
    have hquotient_log :
        Real.log (163 / delta) =
          Real.log 163 + Real.log (1 / delta) := by
      rw [Real.log_div (by norm_num) hdelta.ne',
        Real.log_div (by norm_num) hdelta.ne',
        Real.log_one] <;> ring
    calc
      (Nat.log 2 (2 * cardinality) + 1 : ℝ)
          ≤ Real.log ((2 * cardinality : ℕ) : ℝ) /
              Real.log 2 + 1 := by
        linarith
      _ ≤ Real.log (2 * ((bound : ℝ) ^ 5)) /
              Real.log 2 + 1 := by
        gcongr
      _ =
          (Real.log 2 + 5 * Real.log (bound : ℝ)) /
              Real.log 2 + 1 := by
        rw [hlog_bound2]
      _ ≤
          (Real.log 2 + 5 * Real.log (163 / delta)) /
              Real.log 2 + 1 := by
        gcongr
      _ =
          (5 / Real.log 2) * Real.log (1 / delta) +
            (5 * Real.log 163 / Real.log 2 + 2) := by
        rw [hquotient_log]
        field_simp [hlog_two.ne'] <;> ring

end Kakeya.Assouad

end
