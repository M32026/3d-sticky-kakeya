import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.WZ1.IntervalADHelpers

/-!
# Bridge between paper-literal AD predicate and internal IsADSet1

Proves `PureWZ2PaperADBridgeStatement` by elementary covering geometry in `ℝ`.

The factor `10` is generous: direction 1 needs at most factor `2`, and
direction 2 needs at most factor `5` (from covering `[-4,4]` by five unit balls).
-/

noncomputable section

open Metric Set

namespace Kakeya.Assouad

/-- The interval `[-4,4]` is covered by five balls of radius `r ≥ 1`
centered at `-4, -2, 0, 2, 4`. -/
lemma Icc_four_subset_five_balls (r : ℝ) (hr : 1 ≤ r) :
    Set.Icc (-4 : ℝ) 4 ⊆
      ⋃ c ∈ ({-4, -2, 0, 2, 4} : Finset ℝ), closedBall c r := by
  intro x hx
  have h1 : -4 ≤ x := hx.1
  have h2 : x ≤ 4 := hx.2
  have h_main : ∃ (c : ℝ), c ∈ ({-4, -2, 0, 2, 4} : Finset ℝ) ∧ dist x c ≤ 1 := by
    by_cases h3 : x ≤ -3
    · refine ⟨-4, by simp, ?_⟩
      simp only [Real.dist_eq, sub_neg_eq_add]
      have h4 : 0 ≤ x + 4 := by linarith
      rw [abs_of_nonneg h4] <;> linarith
    · by_cases h4 : x ≤ -1
      · refine ⟨-2, by simp, ?_⟩
        rw [Real.dist_eq]
        have h5 : -1 ≤ x + 2 := by linarith
        have h6 : x + 2 ≤ 1 := by linarith
        exact abs_le.mpr ⟨by linarith, by linarith⟩
      · by_cases h5 : x ≤ 1
        · refine ⟨0, by simp, ?_⟩
          rw [Real.dist_eq]
          exact abs_le.mpr ⟨by linarith, by linarith⟩
        · by_cases h6 : x ≤ 3
          · refine ⟨2, by simp, ?_⟩
            rw [Real.dist_eq]
            exact abs_le.mpr ⟨by linarith, by linarith⟩
          · refine ⟨4, by simp, ?_⟩
            rw [Real.dist_eq]
            have h7 : x - 4 ≤ 0 := by linarith
            rw [abs_of_nonpos h7] <;> linarith
  rcases h_main with ⟨c, hc, hdist1⟩
  have hdist : dist x c ≤ r := hdist1.trans hr
  exact Set.mem_iUnion₂.mpr ⟨c, hc, hdist⟩

/-- Covering number of `[-4,4]` at radius `r ≥ 1` is at most `5`. -/
lemma covering_Icc_four_le_five {r : ℝ} (hr : 1 ≤ r) :
    (Metric.externalCoveringNumber ⟨r, by linarith⟩ (Set.Icc (-4 : ℝ) 4) : ENNReal) ≤ 5 := by
  let centers : Finset ℝ := {-4, -2, 0, 2, 4}
  have h1 : Metric.IsCover ⟨r, by linarith⟩ (Set.Icc (-4 : ℝ) 4) (centers : Set ℝ) := by
    intro x hx
    have h2 : x ∈ ⋃ c ∈ centers, closedBall c r := Icc_four_subset_five_balls r hr hx
    rcases Set.mem_iUnion₂.mp h2 with ⟨c, hc, hball⟩
    refine ⟨c, hc, ?_⟩
    simpa [Set.mem_setOf_eq] using dist_le_coe.mp hball
  have h3 := h1.externalCoveringNumber_le_encard
  have h4 : (Metric.externalCoveringNumber ⟨r, by linarith⟩ (Set.Icc (-4 : ℝ) 4) : ENNReal) ≤
      ((centers : Set ℝ).encard : ENNReal) := by
    exact_mod_cast h3
  have h5 : ((centers : Set ℝ).encard : ENNReal) = (centers.card : ENNReal) := by
    simp
  have h6 : centers.card = 5 := by
    simp [centers]
    <;> norm_num
  rw [h5, h6] at h4
  <;> norm_num at h4 ⊢ <;> exact h4

/-- `realRpowENN` is multiplicative for nonnegative bases. -/
private lemma realRpowENN_mul_nonneg
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (alpha : ℝ) :
    Kakeya.realRpowENN (a * b) alpha =
    Kakeya.realRpowENN a alpha * Kakeya.realRpowENN b alpha := by
  simp only [Kakeya.realRpowENN]
  have h : Real.rpow (a * b) alpha = Real.rpow a alpha * Real.rpow b alpha :=
    Real.mul_rpow ha hb
  rw [h]
  have h_nonneg : 0 ≤ Real.rpow a alpha := Real.rpow_nonneg ha _
  exact ENNReal.ofReal_mul h_nonneg

/-- `realRpowENN` is monotone in the base for nonnegative exponent. -/
lemma realRpowENN_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (alpha : ℝ) (halpha : 0 ≤ alpha) :
    Kakeya.realRpowENN a alpha ≤ Kakeya.realRpowENN b alpha := by
  simp only [Kakeya.realRpowENN]
  exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow ha hab halpha)

/-- `realRpowENN 1 alpha = 1`. -/
lemma realRpowENN_one (alpha : ℝ) :
    Kakeya.realRpowENN 1 alpha = 1 := by
  simp [Kakeya.realRpowENN]

/-- In `ℝ`, `closedBall x r = Icc (x-r) (x+r)`. -/
lemma real_closedBall_eq_Icc (x r : ℝ) :
    Metric.closedBall x r = Set.Icc (x - r) (x + r) := by
  ext y
  simp only [Metric.mem_closedBall, Set.mem_Icc, Real.dist_eq]
  constructor
  · intro h
    have h' : |y - x| ≤ r := h
    have h1 : -r ≤ y - x := (abs_le.mp h').1
    have h2 : y - x ≤ r := (abs_le.mp h').2
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    have h3 : -r ≤ y - x := by linarith
    have h4 : y - x ≤ r := by linarith
    exact abs_le.mpr ⟨h3, h4⟩

/-- Direction 1: paper-literal AD implies internal IsADSet1 with factor 10. -/
lemma paper_ad_to_internal {set : Set ℝ} {delta alpha : ℝ} {C : ENNReal}
    (hset : set ⊆ Set.Icc (-4 : ℝ) 4)
    (h : PureWZ2PaperADSet1 set delta alpha C) :
    IsADSet1 set delta alpha (10 * C) := by
  rcases h with ⟨hδ, hα, hα1, hC, hCtop, hcover⟩
  have h10C : (1 : ENNReal) ≤ 10 * C := by
    have h1 : (1 : ENNReal) ≤ C := hC
    have h2 : (1 : ENNReal) ≤ 10 := by norm_num
    calc (1 : ENNReal) ≤ C := h1
         _ ≤ (10 : ENNReal) * C := le_mul_of_one_le_left' h2
  refine ⟨hδ, hα, hα1, h10C, hset, ?_⟩
  intro rho hrho hδrho hrho1 x r hrhox hr1
  have hrho_pos : 0 < rho := by linarith
  have hr_pos : 0 < r := by linarith
  have hball : Metric.closedBall x r = Set.Icc (x - r) (x + r) :=
    real_closedBall_eq_Icc x r
  rw [hball]
  have hlen : rho ≤ 2 * r := by linarith
  have h4 := hcover rho hrho hδrho (x - r) (2 * r) hlen
  have h_interval : Set.Icc (x - r) ((x - r) + 2 * r) = Set.Icc (x - r) (x + r) := by
    have h : (x - r) + 2 * r = x + r := by ring
    rw [h]
  rw [h_interval] at h4
  have h5 : Kakeya.realRpowENN ((2 * r) / rho) alpha =
      Kakeya.realRpowENN 2 alpha * Kakeya.realRpowENN (r / rho) alpha := by
    have h6 : (2 * r) / rho = 2 * (r / rho) := by ring
    rw [h6]
    exact realRpowENN_mul_nonneg (by norm_num) (by positivity) alpha
  rw [h5] at h4
  have h8 : Kakeya.realRpowENN 2 alpha ≤ (2 : ENNReal) := by
    have h9 : Real.rpow 2 alpha ≤ 2 := by
      have h10 : Real.rpow 2 alpha ≤ Real.rpow 2 1 :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hα1
      simpa using h10
    simpa [Kakeya.realRpowENN] using ENNReal.ofReal_le_ofReal h9
  calc
    (↑(Metric.externalCoveringNumber ⟨rho, hrho⟩
        (set ∩ Set.Icc (x - r) (x + r))) : ENNReal)
      ≤ C * (Kakeya.realRpowENN 2 alpha * Kakeya.realRpowENN (r / rho) alpha) := h4
    _ = C * Kakeya.realRpowENN 2 alpha * Kakeya.realRpowENN (r / rho) alpha := by
      rw [mul_assoc]
    _ ≤ C * (2 : ENNReal) * Kakeya.realRpowENN (r / rho) alpha := by
      gcongr
      <;> exact h8
    _ ≤ (10 : ENNReal) * C * Kakeya.realRpowENN (r / rho) alpha := by
      have h11 : C * (2 : ENNReal) ≤ (10 : ENNReal) * C := by
        have h12 : C * (2 : ENNReal) = (2 : ENNReal) * C := by ring
        rw [h12]
        gcongr <;> norm_num
      gcongr
    _ = (10 * C) * Kakeya.realRpowENN (r / rho) alpha := by
      rw [mul_assoc]

/-- Direction 2: internal IsADSet1 implies paper-literal AD with factor 10. -/
lemma internal_to_paper_ad {set : Set ℝ} {delta alpha : ℝ} {C : ENNReal}
    (hδ : 0 < delta) (hδ1 : delta ≤ 1) (hCtop : C ≠ ⊤)
    (h : IsADSet1 set delta alpha C) :
    PureWZ2PaperADSet1 set delta alpha (10 * C) := by
  rcases h with ⟨_, hα, hα1, hC, hbounded, hcover⟩
  have h10C : (1 : ENNReal) ≤ 10 * C := by
    have h1 : (1 : ENNReal) ≤ C := hC
    have h2 : (1 : ENNReal) ≤ 10 := by norm_num
    calc (1 : ENNReal) ≤ C := h1
         _ ≤ (10 : ENNReal) * C := le_mul_of_one_le_left' h2
  have h10Ctop : (10 * C) ≠ ⊤ := by
    have h : (10 : ENNReal) * C ≠ ⊤ := ENNReal.mul_ne_top (by simp) hCtop
    simpa [mul_comm] using h
  refine ⟨hδ, hα, hα1, h10C, h10Ctop, ?_⟩
  intro rho hrho hδrho left length hlen
  have hrho_pos : 0 < rho := by linarith
  have hlen_pos : 0 < length := by linarith
  set S : Set ℝ := set ∩ Set.Icc left (left + length) with hS_def
  have hS_sub : S ⊆ Set.Icc (-4 : ℝ) 4 := by
    intro x hx
    exact hbounded hx.1
  by_cases h_caseA : 1 < rho
  · -- Case A: rho > 1
    have h9 : (Metric.externalCoveringNumber ⟨rho, hrho⟩ S : ENNReal) ≤ 5 := by
      have h10 : S ⊆ Set.Icc (-4 : ℝ) 4 := hS_sub
      have h11 : (Metric.externalCoveringNumber ⟨rho, hrho⟩ S : ENNReal) ≤
          (Metric.externalCoveringNumber ⟨rho, hrho⟩ (Set.Icc (-4 : ℝ) 4) : ENNReal) := by
        simpa using Metric.externalCoveringNumber_mono_set h10
      exact h11.trans (covering_Icc_four_le_five (by linarith))
    have h13 : 1 ≤ length / rho := by
      calc (1 : ℝ) = rho / rho := by field_simp [hrho_pos.ne']
           _ ≤ length / rho := by gcongr
    have h14 : (1 : ENNReal) ≤ Kakeya.realRpowENN (length / rho) alpha := by
      have h15 : (1 : ℝ) ≤ Real.rpow (length / rho) alpha := Real.one_le_rpow h13 hα.le
      simpa [Kakeya.realRpowENN] using ENNReal.ofReal_le_ofReal h15
    have h16 : (10 : ENNReal) ≤ (10 * C) := by
      have h17 : (1 : ENNReal) ≤ C := hC
      have h18 : (10 : ENNReal) ≤ (10 : ENNReal) * C := le_mul_of_one_le_right' hC
      simpa [mul_comm] using h18
    have h12 : (5 : ENNReal) ≤ (10 * C) * Kakeya.realRpowENN (length / rho) alpha := by
      calc (5 : ENNReal) ≤ (10 : ENNReal) := by norm_num
           _ ≤ (10 * C) := h16
           _ ≤ (10 * C) * Kakeya.realRpowENN (length / rho) alpha :=
             le_mul_of_one_le_right' h14
    exact h9.trans h12
  · -- Case rho ≤ 1
    have hrho1 : rho ≤ 1 := by linarith
    by_cases h_caseC : 2 < length
    · -- Case C: length > 2
      let centers : Finset ℝ := {-4, -2, 0, 2, 4}
      let A : ℝ → Set ℝ := fun c => set ∩ Metric.closedBall c 1
      have hcover1 : Set.Icc (-4 : ℝ) 4 ⊆ ⋃ c ∈ centers, Metric.closedBall c 1 :=
        Icc_four_subset_five_balls 1 (by norm_num)
      have hS_union : S ⊆ ⋃ c ∈ centers, A c := by
        intro x hx
        have hx_set : x ∈ set := hx.1
        have hx4 : x ∈ Set.Icc (-4 : ℝ) 4 := hbounded hx_set
        have h2 : x ∈ ⋃ c ∈ centers, Metric.closedBall c 1 := hcover1 hx4
        rcases Set.mem_iUnion₂.mp h2 with ⟨c, hc, hball⟩
        exact Set.mem_iUnion₂.mpr ⟨c, hc, ⟨hx_set, hball⟩⟩
      have hpiece : ∀ c ∈ centers,
          (Metric.externalCoveringNumber ⟨rho, hrho⟩ (A c) : ENNReal) ≤
          C * Kakeya.realRpowENN (1 / rho) alpha := by
        intro c _
        exact hcover rho hrho hδrho hrho1 c 1 (by linarith) (by norm_num)
      have hunion : (Metric.externalCoveringNumber ⟨rho, hrho⟩ (⋃ c ∈ centers, A c) : ENNReal) ≤
          (centers.card : ENNReal) * (C * Kakeya.realRpowENN (1 / rho) alpha) :=
        externalCoveringNumber_biUnion_le_card hpiece
      have hcard : centers.card = 5 := by
        simp [centers] <;> norm_num
      rw [hcard] at hunion
      have hmono : (Metric.externalCoveringNumber ⟨rho, hrho⟩ S : ENNReal) ≤
          (Metric.externalCoveringNumber ⟨rho, hrho⟩ (⋃ c ∈ centers, A c) : ENNReal) := by
        exact_mod_cast Metric.externalCoveringNumber_mono_set hS_union
      have h10 : Kakeya.realRpowENN (length / rho) alpha =
          Kakeya.realRpowENN length alpha * Kakeya.realRpowENN (1 / rho) alpha := by
        have h11 : length / rho = length * (1 / rho) := by ring
        rw [h11]
        exact realRpowENN_mul_nonneg (by linarith) (by positivity) alpha
      have h12 : (1 : ENNReal) ≤ Kakeya.realRpowENN length alpha := by
        have h13 : (1 : ℝ) ≤ length := by linarith
        have h14 : (1 : ℝ) ≤ Real.rpow length alpha := Real.one_le_rpow h13 hα.le
        simpa [Kakeya.realRpowENN] using ENNReal.ofReal_le_ofReal h14
      have h15 : (5 : ENNReal) ≤ (10 : ENNReal) * Kakeya.realRpowENN length alpha := by
        calc (5 : ENNReal) ≤ (10 : ENNReal) := by norm_num
             _ ≤ (10 : ENNReal) * Kakeya.realRpowENN length alpha :=
               le_mul_of_one_le_right' h12
      have h16 : (5 : ENNReal) * (C * Kakeya.realRpowENN (1 / rho) alpha) ≤
          ((10 : ENNReal) * Kakeya.realRpowENN length alpha) * (C * Kakeya.realRpowENN (1 / rho) alpha) := by
        gcongr
      have h17 : ((10 : ENNReal) * Kakeya.realRpowENN length alpha) * (C * Kakeya.realRpowENN (1 / rho) alpha) =
          (10 * C) * Kakeya.realRpowENN (length / rho) alpha := by
        rw [h10]
        simp [mul_assoc, mul_comm, mul_left_comm]
      rw [h17] at h16
      exact (hmono.trans hunion).trans h16
    · -- Case B: length ≤ 2
      have hlen2 : length ≤ 2 := by linarith
      by_cases h_caseB1 : 2 * rho ≤ length
      · -- Subcase B1: length ≥ 2*rho
        set r : ℝ := length / 2 with hr_def
        set x : ℝ := left + length / 2 with hx_def
        have hr_ge_rho : rho ≤ r := by linarith
        have hr_le1 : r ≤ 1 := by linarith
        have hball1 : Metric.closedBall x r = Set.Icc (x - r) (x + r) :=
          real_closedBall_eq_Icc x r
        have h_eq : Set.Icc (x - r) (x + r) = Set.Icc left (left + length) := by
          have h1 : x - r = left := by
            simp [hx_def, hr_def] <;> linarith
          have h2 : x + r = left + length := by
            simp [hx_def, hr_def] <;> linarith
          rw [h1, h2]
        have hball : Metric.closedBall x r = Set.Icc left (left + length) := by
          rw [hball1, h_eq]
        have h4 := hcover rho hrho hδrho hrho1 x r hr_ge_rho hr_le1
        rw [hball] at h4
        have h5 : Kakeya.realRpowENN (r / rho) alpha ≤ Kakeya.realRpowENN (length / rho) alpha := by
          have h6 : r / rho ≤ length / rho := by
            simp [hr_def] <;> gcongr <;> linarith
          exact realRpowENN_mono (by positivity) h6 alpha hα.le
        have h7 : C * Kakeya.realRpowENN (r / rho) alpha ≤
            C * Kakeya.realRpowENN (length / rho) alpha := by
          gcongr
        have h8 : C * Kakeya.realRpowENN (length / rho) alpha ≤
            (10 * C) * Kakeya.realRpowENN (length / rho) alpha := by
          have h9 : C ≤ 10 * C := by
            have h10 : (1 : ENNReal) ≤ 10 := by norm_num
            exact le_mul_of_one_le_left' h10
          gcongr
        exact h4.trans h7 |>.trans h8
      · -- Subcase B2: length < 2*rho
        have h_caseB2' : length < 2 * rho := by linarith
        set x : ℝ := left + length / 2 with hx_def
        have hIcc_sub : Set.Icc left (left + length) ⊆ Metric.closedBall x rho := by
          intro y hy
          have h1 : left ≤ y := hy.1
          have h2 : y ≤ left + length := hy.2
          have h3 : dist y x ≤ rho := by
            simp only [Real.dist_eq, hx_def]
            have h4 : |y - (left + length / 2)| ≤ rho := by
              have h5 : -(rho) ≤ y - (left + length / 2) := by linarith
              have h6 : y - (left + length / 2) ≤ rho := by linarith
              exact abs_le.mpr ⟨h5, h6⟩
            exact h4
          exact h3
        have hS_sub2 : S ⊆ set ∩ Metric.closedBall x rho := by
          intro y hy
          exact ⟨hy.1, hIcc_sub hy.2⟩
        have h4 := hcover rho hrho hδrho hrho1 x rho (by linarith) hrho1
        have h5 : (Metric.externalCoveringNumber ⟨rho, hrho⟩ S : ENNReal) ≤
            (Metric.externalCoveringNumber ⟨rho, hrho⟩ (set ∩ Metric.closedBall x rho) : ENNReal) := by
          exact_mod_cast Metric.externalCoveringNumber_mono_set hS_sub2
        have h6 : Kakeya.realRpowENN (rho / rho) alpha = 1 := by
          have h7 : rho / rho = 1 := by field_simp [hrho_pos.ne']
          rw [h7]
          exact realRpowENN_one alpha
        rw [h6] at h4
        have h7 : (Metric.externalCoveringNumber ⟨rho, hrho⟩ S : ENNReal) ≤ C := by
          simpa using h5.trans h4
        have h8 : 1 ≤ length / rho := by
          calc (1 : ℝ) = rho / rho := by field_simp [hrho_pos.ne']
               _ ≤ length / rho := by gcongr
        have h9 : (1 : ENNReal) ≤ Kakeya.realRpowENN (length / rho) alpha := by
          have h10 : (1 : ℝ) ≤ Real.rpow (length / rho) alpha := Real.one_le_rpow h8 hα.le
          simpa [Kakeya.realRpowENN] using ENNReal.ofReal_le_ofReal h10
        have h10 : C ≤ (10 * C) * Kakeya.realRpowENN (length / rho) alpha := by
          have h11 : C ≤ 10 * C := by
            have h12 : (1 : ENNReal) ≤ 10 := by norm_num
            exact le_mul_of_one_le_left' h12
          calc C ≤ 10 * C := h11
               _ ≤ (10 * C) * Kakeya.realRpowENN (length / rho) alpha :=
                 le_mul_of_one_le_right' h9
        exact h7.trans h10

theorem pure_wz2_paper_ad_bridge : PureWZ2PaperADBridgeStatement := by
  constructor
  · intro set delta alpha C hset h
    exact paper_ad_to_internal hset h
  · intro set delta alpha C hδ hδ1 hCtop h
    exact internal_to_paper_ad hδ hδ1 hCtop h

end Kakeya.Assouad
