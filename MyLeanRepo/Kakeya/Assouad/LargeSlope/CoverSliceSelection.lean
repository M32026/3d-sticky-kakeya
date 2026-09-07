import MyLeanRepo.Kakeya.Assouad.Definitions
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Tactic

/-!
# Fubini/Markov cover-slice selection

Given finitely many cover centers and a positive width, this module selects
one horizontal slice that meets only a controlled number of the corresponding
vertical windows.  It is the independent counting input used before the
same-slice incidence construction in the large-slope argument.
-/

noncomputable section

open MeasureTheory Set Metric Finset

attribute [local instance] Classical.propDecidable

namespace Kakeya.Assouad

/--
Given a finite set of cover centers in `Point3` and a width `W > 0`, there is
a measurable set of y-values of measure at least one such that every selected
height satisfies

`3 * |{c : |c 1 - y₀| ≤ W}| ≤ 8 * W * |coverCenters|`.

The proof integrates the number of windows meeting a height over `[-1, 1]`
and applies Markov's inequality.  Returning the whole good set, rather than an
arbitrary one of its points, lets the later Fubini argument select a high-mass
slice at the same height.
-/
lemma exists_many_cover_slices_y
    {W : ℝ} (hW_pos : 0 < W)
    (coverCenters : Finset Point3) :
    ∃ good : Set ℝ,
      MeasurableSet good ∧
      (1 : ENNReal) ≤ MeasureTheory.volume good ∧
      good ⊆ Set.Icc (-1 : ℝ) 1 ∧
      ∀ y ∈ good,
        (3 : ENNReal) *
            ↑(coverCenters.filter (fun c => |c 1 - y| ≤ W)).card ≤
          (8 : ENNReal) * ENNReal.ofReal W *
            (coverCenters.card : ENNReal) := by
  let N := coverCenters.card
  by_cases hN : N = 0
  · have h_empty : coverCenters = ∅ := Finset.card_eq_zero.mp hN
    refine ⟨Set.Icc (-1 : ℝ) 1, measurableSet_Icc, ?_,
      Set.Subset.rfl, ?_⟩
    · norm_num [Real.volume_Icc]
    · intro y _
      rw [h_empty]
      simp
  · have hN_pos : 0 < N := Nat.pos_of_ne_zero hN
    let I : Set ℝ := Set.Icc (-1) 1
    let S (c : Point3) : Set ℝ := Set.Icc (c 1 - W) (c 1 + W)
    have hS : ∀ (c : Point3), {z : ℝ | |c 1 - z| ≤ W} = S c := by
      intro c
      ext z
      simp only [Set.mem_setOf_eq, S, Set.mem_Icc]
      rw [abs_le] <;> constructor <;> intro h <;> constructor <;> linarith
    let h_c (c : Point3) : ℝ → ENNReal := fun y =>
      if y ∈ S c then 1 else 0
    let f : ℝ → ENNReal := fun y => ∑ c ∈ coverCenters, h_c c y
    let g : ℝ → ENNReal := fun y => 3 * f y
    have h_ind_eq : ∀ (c : Point3), h_c c = (S c).indicator (1 : ℝ → ENNReal) := by
      intro c
      funext y
      simp [h_c, Set.indicator_apply]
      <;> split_ifs <;> tauto
    have hf_card : ∀ y, f y = ↑(coverCenters.filter (fun c => |c 1 - y| ≤ W)).card := by
      intro y
      have h1 : ∀ c ∈ coverCenters,
          h_c c y = (if |c 1 - y| ≤ W then (1 : ENNReal) else 0) := by
        intro c _
        have h_mem : y ∈ S c ↔ |c 1 - y| ≤ W := by
          have h_set_eq : {z : ℝ | |c 1 - z| ≤ W} = S c := hS c
          have h : y ∈ S c ↔ y ∈ {z : ℝ | |c 1 - z| ≤ W} := by
            rw [← h_set_eq]
          simpa using h
        simp [h_c, h_mem]
      have h2 : f y =
          ∑ c ∈ coverCenters, (if |c 1 - y| ≤ W then (1 : ENNReal) else 0) := by
        apply Finset.sum_congr rfl
        intro c _
        exact h1 c ‹_›
      rw [h2, Finset.sum_ite]
      <;> simp [Finset.sum_const] <;> norm_cast
    have h_ind_meas : ∀ c ∈ coverCenters, Measurable (h_c c) := by
      intro c _
      rw [h_ind_eq c]
      exact Measurable.indicator measurable_const measurableSet_Icc
    have hf_meas : Measurable f := by
      apply Finset.measurable_sum
      exact h_ind_meas
    have hg_meas : Measurable g := by fun_prop
    have h_integral_ind : ∀ c ∈ coverCenters,
        ∫⁻ y in I, h_c c y ≤ ENNReal.ofReal (2 * W) := by
      intro c _
      have h3 : ∫⁻ y in I, h_c c y = MeasureTheory.volume (S c ∩ I) := by
        rw [h_ind_eq c]
        have h4 :
            ∫⁻ (y : ℝ), (S c).indicator (1 : ℝ → ENNReal) y ∂(volume.restrict I) =
              (volume.restrict I) (S c) :=
          lintegral_indicator_one measurableSet_Icc
        rw [h4]
        have h5 : (volume.restrict I) (S c) = MeasureTheory.volume (S c ∩ I) := by
          rw [MeasureTheory.Measure.restrict_apply measurableSet_Icc]
          <;> rfl
        rw [h5]
      rw [h3]
      have h41 : (S c ∩ I) ⊆ S c := by simp
      have h4 : MeasureTheory.volume (S c ∩ I) ≤ MeasureTheory.volume (S c) :=
        MeasureTheory.measure_mono h41
      have h5 : MeasureTheory.volume (S c) = ENNReal.ofReal (2 * W) := by
        have h51 : S c = Set.Icc (c 1 - W) (c 1 + W) := by rfl
        rw [h51, Real.volume_Icc]
        have h52 : (c 1 + W) - (c 1 - W) = 2 * W := by ring
        rw [h52] <;> rfl
      rw [h5] at h4
      exact h4
    let X : ENNReal := ENNReal.ofReal W * ↑N
    have hX_ne_zero : X ≠ 0 := by
      simp [X, hW_pos.ne', hN_pos.ne'] <;> positivity
    have hX_ne_top : X ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top
    have h_integral_f : ∫⁻ y in I, f y ≤ 2 * X := by
      have h_sum :
          ∫⁻ y in I, f y = ∑ c ∈ coverCenters, ∫⁻ y in I, h_c c y := by
        rw [lintegral_finsetSum _ h_ind_meas]
      rw [h_sum]
      have h1 :
          ∑ c ∈ coverCenters, ∫⁻ y in I, h_c c y ≤
            ∑ c ∈ coverCenters, ENNReal.ofReal (2 * W) :=
        Finset.sum_le_sum h_integral_ind
      have h2 : ∑ c ∈ coverCenters, ENNReal.ofReal (2 * W) = 2 * X := by
        have h_sum2 :
            ∑ c ∈ coverCenters, ENNReal.ofReal (2 * W) =
              ↑N * ENNReal.ofReal (2 * W) := by
          simp [Finset.sum_const] <;> ring
        rw [h_sum2]
        have h6 : ENNReal.ofReal (2 * W) = (2 : ENNReal) * ENNReal.ofReal W := by
          have h7 :
              ENNReal.ofReal (2 * W) =
                ENNReal.ofReal (2 : ℝ) * ENNReal.ofReal W := by
            have h71 : (2 * W : ℝ) = (2 : ℝ) * W := by ring
            simpa [h71] using ENNReal.ofReal_mul (x := (2 : ℝ)) (y := W)
          rw [h7]
          simp
        rw [h6]
        simp [X, mul_assoc, mul_comm, mul_left_comm]
      exact h1.trans (le_of_eq h2)
    have h_integral_g : ∫⁻ y in I, g y ≤ 6 * X := by
      have h : ∫⁻ y in I, g y = 3 * ∫⁻ y in I, f y := by
        simp [g, lintegral_const_mul'] <;> rfl
      rw [h]
      have h' : 3 * ∫⁻ y in I, f y ≤ 3 * (2 * X) :=
        mul_le_mul_of_nonneg_left h_integral_f (by norm_num)
      rw [show (3 : ENNReal) * (2 * X) = 6 * X by ring] at h'
      exact h'
    let ε : ENNReal := 8 * X
    let B : Set ℝ := {y ∈ I | ε ≤ g y}
    have hB_meas : MeasurableSet B :=
      measurableSet_Icc.inter (hg_meas measurableSet_Ici)
    have h_set_eq : {x : ℝ | ε ≤ g x} ∩ I = B := by
      ext x
      simp [B] <;> tauto
    have h_ae : AEMeasurable g (volume.restrict I) := hg_meas.aemeasurable
    have h_markov_raw :
        ε * (volume.restrict I) {x : ℝ | ε ≤ g x} ≤ ∫⁻ y in I, g y :=
      MeasureTheory.mul_meas_ge_le_lintegral₀ h_ae ε
    have h_vol_eq :
        (volume.restrict I) {x : ℝ | ε ≤ g x} = MeasureTheory.volume B := by
      have h_meas_set : MeasurableSet {x : ℝ | ε ≤ g x} :=
        hg_meas measurableSet_Ici
      have h :
          (volume.restrict I) {x : ℝ | ε ≤ g x} =
            MeasureTheory.volume ({x : ℝ | ε ≤ g x} ∩ I) := by
        rw [MeasureTheory.Measure.restrict_apply h_meas_set]
        <;> rfl
      rw [h, h_set_eq]
    have h_markov : ε * MeasureTheory.volume B ≤ ∫⁻ y in I, g y := by
      rw [h_vol_eq] at h_markov_raw
      exact h_markov_raw
    have hB_le_one : MeasureTheory.volume B ≤ 1 := by
      have h : ε * MeasureTheory.volume B ≤ 6 * X :=
        h_markov.trans h_integral_g
      have h' :
          (8 : ENNReal) * X * MeasureTheory.volume B ≤ (6 : ENNReal) * X := by
        simpa [ε, mul_assoc] using h
      have h9 : (8 : ENNReal) * X ≠ 0 := mul_ne_zero (by norm_num) hX_ne_zero
      have h10 : (8 : ENNReal) * X ≠ ⊤ :=
        ENNReal.mul_ne_top (by norm_num) hX_ne_top
      have h6 :
          (8 : ENNReal) * X * MeasureTheory.volume B ≤
            (8 : ENNReal) * X * (1 : ENNReal) := by
        have h7 : (6 : ENNReal) * X ≤ (8 : ENNReal) * X := by
          gcongr <;> norm_num
        have h8 : (8 : ENNReal) * X * (1 : ENNReal) = (8 : ENNReal) * X := by
          ring
        rw [h8]
        exact h'.trans h7
      exact (ENNReal.mul_le_mul_iff_right h9 h10).mp h6
    let G : Set ℝ := I \ B
    have hG_meas : MeasurableSet G :=
      measurableSet_Icc.diff hB_meas
    have hI_vol : MeasureTheory.volume I = 2 := by
      simp [I, Real.volume_Icc] <;> norm_num
    have hG_vol : MeasureTheory.volume G ≥ 1 := by
      have hB_sub_I : B ⊆ I := by
        intro x hx
        exact hx.1
      have h_union : G ∪ B = I := Set.sdiff_union_of_subset hB_sub_I
      have h_disj : Disjoint G B :=
        Set.disjoint_left.mpr (fun x hxG hxB => hxG.2 hxB)
      have h_vol_union :
          MeasureTheory.volume (G ∪ B) =
            MeasureTheory.volume G + MeasureTheory.volume B :=
        MeasureTheory.measure_union h_disj hB_meas
      have h : MeasureTheory.volume I =
          MeasureTheory.volume G + MeasureTheory.volume B := by
        rw [← h_union]
        exact h_vol_union
      rw [hI_vol] at h
      by_contra h11
      have h12 : MeasureTheory.volume G < 1 := lt_of_not_ge h11
      have h13 :
          MeasureTheory.volume G + MeasureTheory.volume B ≤
            MeasureTheory.volume G + 1 := by
        gcongr
      have h14 : MeasureTheory.volume G + (1 : ENNReal) <
          (1 : ENNReal) + (1 : ENNReal) :=
        ENNReal.add_lt_add_right (by norm_num) h12
      have h15 : (1 : ENNReal) + (1 : ENNReal) = (2 : ENNReal) := by
        norm_num
      rw [h15] at h14
      have h16 : MeasureTheory.volume G + MeasureTheory.volume B < 2 :=
        h13.trans_lt h14
      rw [h] at h16
      norm_num at h16
    refine ⟨G, hG_meas, hG_vol, ?_, ?_⟩
    · intro y hy
      exact hy.1
    · intro y hy
      have hy_I : y ∈ I := hy.1
      have hy_not_B : y ∉ B := hy.2
      have h_lt : g y < ε := by
        by_contra h
        have h' : ε ≤ g y := le_of_not_gt h
        exact hy_not_B ⟨hy_I, h'⟩
      have h10 : (3 : ENNReal) * f y ≤ (8 : ENNReal) * X := by
        have h11 : g y = (3 : ENNReal) * f y := by simp [g]
        rw [h11] at h_lt
        exact le_of_lt h_lt
      have h12 :
          f y = ↑(coverCenters.filter (fun c => |c 1 - y| ≤ W)).card :=
        hf_card y
      rw [← h12]
      simpa [X, N, mul_assoc] using h10

/-- Select one controlled cover slice from the positive-measure good set. -/
lemma exists_cover_slice_y
    {W : ℝ} (hW_pos : 0 < W)
    (coverCenters : Finset Point3) :
    ∃ (y₀ : ℝ), y₀ ∈ Set.Icc (-1 : ℝ) 1 ∧
      (3 : ENNReal) * ↑(coverCenters.filter (fun c => |c 1 - y₀| ≤ W)).card ≤
      (8 : ENNReal) * ENNReal.ofReal W * (coverCenters.card : ENNReal) := by
  rcases exists_many_cover_slices_y hW_pos coverCenters with
    ⟨good, _, hgood_volume, hgood_subset, hgood_count⟩
  have hgood_nonempty : good.Nonempty := by
    by_contra h
    have hempty : good = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    rw [hempty] at hgood_volume
    simpa using hgood_volume
  rcases hgood_nonempty with ⟨y₀, hy₀⟩
  exact ⟨y₀, hgood_subset hy₀, hgood_count y₀ hy₀⟩

end Kakeya.Assouad
