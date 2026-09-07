import MyLeanRepo.Kakeya.CV.Isoperimetric.Statements
import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.BrunnMinkowski.Isodiametric
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Geometry.Euclidean.Volume.Measure

/-!
# 2D Hausdorff measure normalization

Proves `addHaarScalarFactor (volume : Measure (E 2)) μH[2] = ENNReal.ofReal (π / 4)`
using the Vitali covering theorem to show `μH[2](ball) ≤ 4`.
-/

noncomputable section

open MeasureTheory Metric Set ENNReal Real Filter
open scoped ENNReal

namespace Geometry

-- ======================================================================
-- Key lemma: μH[2](unit ball) ≤ 4
-- ======================================================================

/-- The 2D Hausdorff measure of the unit ball is at most 4. -/
lemma hausdorff_twoDim_ball_le_four :
    μH[2] (ball (0 : E 2) 1) ≤ 4 := by
  let s : Set (E 2) := ball 0 1

  -- For each k : ℕ, construct a covering with diam ≤ 1/(k+1) and sum ≤ 4 + 1/(k+1)
  have h_main : ∀ (k : ℕ),
      ∃ (u : Set (E 2 × ℝ)) (v : Set (E 2))
        (hu : u.Countable) (hv : v.Countable)
        (B : {a // a ∈ u} → Set (E 2))
        (C : {y // y ∈ v} → Set (E 2)),
        (s ⊆ (⋃ a : {a // a ∈ u}, B a) ∪ (⋃ y : {y // y ∈ v}, C y)) ∧
        (∀ a : {a // a ∈ u}, ediam (B a) ≤ ENNReal.ofReal (1 / (k + 1 : ℝ))) ∧
        (∀ y : {y // y ∈ v}, ediam (C y) ≤ ENNReal.ofReal (1 / (k + 1 : ℝ))) ∧
        (∑' a : {a // a ∈ u}, ediam (B a) ^ 2 ≤ 4) ∧
        (∑' y : {y // y ∈ v}, ediam (C y) ^ 2 ≤ ENNReal.ofReal (1 / (k + 1 : ℝ))) := by
    intro k
    set δ : ℝ := 1 / (k + 1 : ℝ) with hδ_def
    set ε : ℝ := 1 / (k + 1 : ℝ) with hε_def
    have hδ_pos : 0 < δ := by positivity
    have hε_pos : 0 < ε := by positivity
    set ε' : ℝ := Real.pi * ε / 100 with hε'_def
    have hε'_pos : 0 < ε' := by positivity

    -- Step 1: Vitali covering of s by balls contained in s.
    let ι := E 2 × ℝ
    let t : Set ι := {p | p.1 ∈ s ∧ 0 < p.2 ∧ p.2 ≤ δ / 2 ∧ p.2 ≤ (1 - ‖p.1‖) / 2}
    let c : ι → E 2 := Prod.fst
    let r : ι → ℝ := Prod.snd
    let B : ι → Set (E 2) := fun p => closedBall p.1 p.2
    have hB : ∀ a ∈ t, B a ⊆ closedBall (c a) (r a) := by
      intro a _; rfl
    have hμB : ∀ a ∈ t, volume (closedBall (c a) (3 * r a)) ≤ (9 : NNReal) * volume (B a) := by
      intro a ha
      have hr_nonneg : 0 ≤ r a := by linarith [ha.2.1]
      have h_eq1 : volume (closedBall (c a) (3 * r a)) =
          ENNReal.ofReal (3 * r a) ^ 2 * ENNReal.ofReal Real.pi :=
        EuclideanSpace.volume_closedBall_fin_two (c a) (3 * r a)
      have h_eq2 : volume (B a) =
          ENNReal.ofReal (r a) ^ 2 * ENNReal.ofReal Real.pi :=
        EuclideanSpace.volume_closedBall_fin_two (c a) (r a)
      rw [h_eq1, h_eq2]
      have h4 : ENNReal.ofReal (3 * r a) = 3 * ENNReal.ofReal (r a) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
        <;> norm_cast
      rw [h4]
      have h5 : (3 * ENNReal.ofReal (r a)) ^ 2 * ENNReal.ofReal Real.pi =
          (9 : NNReal) * (ENNReal.ofReal (r a) ^ 2 * ENNReal.ofReal Real.pi) := by
        simp [pow_two, mul_assoc] <;> ring
      rw [h5]
    have ht : ∀ a ∈ t, (interior (B a)).Nonempty := by
      intro a ha
      have hr : 0 < r a := ha.2.1
      have h : c a ∈ ball (c a) (r a) := by simp [hr]
      have h' : ball (c a) (r a) ⊆ interior (B a) := Metric.ball_subset_interior_closedBall
      exact ⟨c a, h' h⟩
    have h't : ∀ a ∈ t, IsClosed (B a) := by
      intro a _; exact isClosed_closedBall
    have hf : ∀ x ∈ s, ∀ (e : ℝ), 0 < e → ∃ a ∈ t, r a ≤ e ∧ c a = x := by
      intro x hx e he
      let r0 : ℝ := min e (min (δ / 2) ((1 - ‖x‖) / 2))
      have hr0_pos : 0 < r0 := by
        have h1 : 0 < 1 - ‖x‖ := by simpa [s] using hx
        positivity
      have hr0_le_e : r0 ≤ e := min_le_left _ _
      have hr0_le_d2 : r0 ≤ δ / 2 := by
        calc r0 ≤ min (δ / 2) ((1 - ‖x‖) / 2) := min_le_right _ _
             _ ≤ δ / 2 := min_le_left _ _
      have hr0_le_half : r0 ≤ (1 - ‖x‖) / 2 := by
        calc r0 ≤ min (δ / 2) ((1 - ‖x‖) / 2) := min_le_right _ _
             _ ≤ (1 - ‖x‖) / 2 := min_le_right _ _
      refine ⟨(x, r0), ?_, hr0_le_e, rfl⟩
      exact ⟨hx, hr0_pos, hr0_le_d2, hr0_le_half⟩
    obtain ⟨u, hu_sub, hu_count, h_disj, h_null⟩ :=
      Vitali.exists_disjoint_covering_ae volume s t (9 : NNReal) r c B hB hμB ht h't hf
    let R : Set (E 2) := s \ ⋃ a ∈ u, B a
    have hR_null : volume R = 0 := h_null

    -- u must be nonempty
    have h_vol_s : volume s = ENNReal.ofReal Real.pi := by
      simpa [s] using EuclideanSpace.volume_ball_fin_two (0 : E 2) 1
    have h_u_nonempty : u.Nonempty := by
      by_contra h
      have h' : u = ∅ := Set.not_nonempty_iff_eq_empty.mp h
      have hR : R = s := by
        simp [R, h']
      rw [hR] at hR_null
      rw [h_vol_s] at hR_null
      have h_cont : (ENNReal.ofReal Real.pi) = 0 := hR_null
      have h_eq : (ENNReal.ofReal Real.pi) = 0 ↔ Real.pi ≤ 0 := ENNReal.ofReal_eq_zero
      have h_le : Real.pi ≤ 0 := h_eq.mp h_cont
      have h_pos : 0 < Real.pi := Real.pi_pos
      linarith

    -- Define B on subtype
    let Bsub : {a // a ∈ u} → Set (E 2) := fun a => B a
    have hBsub_sub : ∀ (a : {a // a ∈ u}), Bsub a ⊆ s := by
      intro a
      have h2 : (a : ι) ∈ t := hu_sub a.prop
      have h3 : B (a : ι) ⊆ s := by
        intro y hy
        have h4 : dist y (c (a : ι)) ≤ r (a : ι) := by simpa [B] using hy
        have hca_in_s : c (a : ι) ∈ s := h2.1
        have h_norm_c : ‖c (a : ι)‖ < 1 := by simpa [s] using hca_in_s
        have h5 : ‖y‖ ≤ ‖c (a : ι)‖ + r (a : ι) := by
          have h51 : dist y 0 ≤ dist y (c (a : ι)) + dist (c (a : ι)) 0 := dist_triangle y (c (a : ι)) 0
          have h52 : dist y 0 = ‖y‖ := by simp
          have h53 : dist (c (a : ι)) 0 = ‖c (a : ι)‖ := by simp
          rw [h52, h53] at h51
          linarith [h4]
        have h6 : r (a : ι) ≤ (1 - ‖c (a : ι)‖) / 2 := h2.2.2.2
        have h7 : ‖y‖ < 1 := by linarith
        simpa [s] using h7
      exact h3
    haveI huc : Countable u := hu_count
    have hBsum : ∑' a : {a // a ∈ u}, volume (Bsub a) ≤ volume s := by
      have h : volume (⋃ a ∈ u, B a) = ∑' a : {a // a ∈ u}, volume (Bsub a) := by
        rw [measure_biUnion hu_count h_disj (fun b _ => isClosed_closedBall.measurableSet)] <;> rfl
      rw [←h]
      have h_sub : (⋃ a ∈ u, B a) ⊆ s := by
        intro x hx
        have h_exists : ∃ (a : ι), a ∈ u ∧ x ∈ B a := by
          simpa [Set.mem_iUnion] using hx
        rcases h_exists with ⟨a, ha, hxa⟩
        exact hBsub_sub ⟨a, ha⟩ hxa
      exact measure_mono h_sub
    have h_diam_B : ∀ (a : {a // a ∈ u}), Metric.diam (Bsub a) ≤ δ := by
      intro a
      have h2 : r (a : ι) ≤ δ / 2 := (hu_sub a.prop).2.2.1
      have h3 : Metric.diam (Bsub a) = 2 * r (a : ι) := by
        have h4 : Bsub a = closedBall (c (a : ι)) (r (a : ι)) := by rfl
        rw [h4, Metric.diam_closedBall_eq (c (a : ι)) (by linarith [(hu_sub a.prop).2.1])]
        <;> ring
      rw [h3]; linarith
    have h_sum_diam_B : ∑' a : {a // a ∈ u}, ENNReal.ofReal (Metric.diam (Bsub a)) ^ 2 ≤ 4 := by
      have h1 : ∀ (a : {a // a ∈ u}), ENNReal.ofReal (Metric.diam (Bsub a)) ^ 2 =
          ENNReal.ofReal (4 / Real.pi) * volume (Bsub a) := by
        intro a
        have h2 : Metric.diam (Bsub a) = 2 * r (a : ι) := by
          have h3 : Bsub a = closedBall (c (a : ι)) (r (a : ι)) := by rfl
          rw [h3, Metric.diam_closedBall_eq (c (a : ι)) (by linarith [(hu_sub a.prop).2.1])]
          <;> ring
        rw [h2]
        set ra : ℝ := r (a : ι) with hra_def
        have hr_nonneg : 0 ≤ ra := by linarith [(hu_sub a.prop).2.1]
        have h4 : volume (Bsub a) = ENNReal.ofReal (Real.pi * ra ^ 2) := by
          have h5 : Bsub a = closedBall (c (a : ι)) ra := by rfl
          rw [h5]
          have h6 := EuclideanSpace.volume_closedBall_fin_two (c (a : ι)) ra
          rw [h6]
          have h7 : ENNReal.ofReal ra ^ 2 * ENNReal.ofReal Real.pi = ENNReal.ofReal (Real.pi * ra ^ 2) := by
            have h8 : ENNReal.ofReal ra ^ 2 = ENNReal.ofReal (ra ^ 2) := by
              have h9 : ENNReal.ofReal ra * ENNReal.ofReal ra = ENNReal.ofReal (ra * ra) := by
                rw [← ENNReal.ofReal_mul hr_nonneg]
              simpa [pow_two] using h9
            rw [h8]
            have h10 : ENNReal.ofReal (ra ^ 2) * ENNReal.ofReal Real.pi = ENNReal.ofReal (ra ^ 2 * Real.pi) := by
              rw [← ENNReal.ofReal_mul (by positivity)]
            rw [h10] <;> ring_nf
          exact h7
        rw [h4]
        have h_goal : ENNReal.ofReal (2 * ra) ^ 2 = ENNReal.ofReal (4 / Real.pi) * ENNReal.ofReal (Real.pi * ra ^ 2) := by
          have h11 : ENNReal.ofReal (2 * ra) = 2 * ENNReal.ofReal ra := by
            rw [ENNReal.ofReal_mul (by norm_num)] <;> norm_cast
          have h12 : ENNReal.ofReal (4 / Real.pi) * ENNReal.ofReal (Real.pi * ra ^ 2) = ENNReal.ofReal ((4 / Real.pi) * (Real.pi * ra ^ 2)) := by
            rw [← ENNReal.ofReal_mul (by positivity)]
          rw [h12]
          have h13 : (4 / Real.pi) * (Real.pi * ra ^ 2) = 4 * ra ^ 2 := by
            field_simp [Real.pi_ne_zero] <;> ring
          rw [h13]
          have h14 : ENNReal.ofReal (4 * ra ^ 2) = 4 * ENNReal.ofReal (ra ^ 2) := by
            rw [ENNReal.ofReal_mul (by norm_num)] <;> norm_cast
          rw [h14]
          have h15 : ENNReal.ofReal (ra ^ 2) = ENNReal.ofReal ra ^ 2 := by
            have h16 : ENNReal.ofReal (ra * ra) = ENNReal.ofReal ra * ENNReal.ofReal ra := by
              exact ENNReal.ofReal_mul hr_nonneg
            have h17 : ra ^ 2 = ra * ra := by ring
            rw [h17]
            simpa [pow_two] using h16
          rw [h15, h11] <;> simp [pow_two] <;> ring
        exact h_goal
      calc
        ∑' a, ENNReal.ofReal (Metric.diam (Bsub a)) ^ 2
          = ∑' a, ENNReal.ofReal (4 / Real.pi) * volume (Bsub a) := by
            congr with a; exact h1 a
        _ = ENNReal.ofReal (4 / Real.pi) * ∑' a, volume (Bsub a) := by
            rw [ENNReal.tsum_mul_left]
        _ ≤ ENNReal.ofReal (4 / Real.pi) * volume s := by gcongr
        _ = 4 := by
          rw [h_vol_s]
          have h9 : ENNReal.ofReal (4 / Real.pi) * ENNReal.ofReal Real.pi = ENNReal.ofReal ((4 / Real.pi) * Real.pi) := by
            rw [← ENNReal.ofReal_mul (by positivity)]
          rw [h9]
          have h10 : (4 / Real.pi) * Real.pi = 4 := by
            field_simp [Real.pi_ne_zero] <;> ring
          rw [h10] <;> norm_cast

    -- Step 2: Cover R by 5-fold enlargements of small balls.
    have h_outer : ∃ (U : Set (E 2)), U ⊇ R ∧ IsOpen U ∧ volume U < ENNReal.ofReal ε' :=
      R.exists_isOpen_lt_of_lt (ENNReal.ofReal ε') (by rw [hR_null] <;> positivity)
    rcases h_outer with ⟨U, hR_sub_U, hU_open, hVol_U⟩
    let X : Type := {x // x ∈ R}
    have hP : ∀ (x : X), ∃ (r0 : ℝ), 0 < r0 ∧ closedBall (x : E 2) r0 ⊆ U ∧ r0 ≤ δ / 10 := by
      intro x
      have h1 : (x : E 2) ∈ U := hR_sub_U x.prop
      have h2 : ∃ r > 0, ball (x : E 2) r ⊆ U := by
        have h_nhds : U ∈ nhds (x : E 2) := hU_open.mem_nhds h1
        exact Metric.nhds_basis_ball.mem_iff.mp h_nhds
      let r : ℝ := Classical.choose h2
      have hr_pos : 0 < r := (Classical.choose_spec h2).1
      have hball_sub : ball (x : E 2) r ⊆ U := (Classical.choose_spec h2).2
      let r0 := min (r / 2) (δ / 10)
      have hr0_pos : 0 < r0 := by positivity
      have hr0_le : r0 ≤ δ / 10 := min_le_right _ _
      have hball : closedBall (x : E 2) r0 ⊆ U := by
        have h_sub1 : closedBall (x : E 2) r0 ⊆ ball (x : E 2) r := by
          intro y hy
          have h_dist : dist y (x : E 2) ≤ r0 := by simpa [closedBall] using hy
          have h_r0 : r0 ≤ r / 2 := min_le_left _ _
          have h : dist y (x : E 2) < r := by linarith
          simpa [ball] using h
        exact h_sub1.trans hball_sub
      exact ⟨r0, hr0_pos, hball, hr0_le⟩
    choose r_x hr_x1 hr_x2 hr_x3 using hP
    let t' : Set (E 2) := R
    let x' : E 2 → E 2 := id
    classical
    let r' : E 2 → ℝ := fun y => if h : y ∈ R then r_x ⟨y, h⟩ else 1
    have hr'_pos : ∀ y ∈ t', 0 < r' y := by
      intro y hy
      have h_eq : r' y = r_x ⟨y, hy⟩ := by
        dsimp only [r']
        exact dif_pos hy
      rw [h_eq]
      exact hr_x1 ⟨y, hy⟩
    have hr'_le : ∀ y ∈ t', r' y ≤ δ / 10 := by
      intro y hy
      have h_eq : r' y = r_x ⟨y, hy⟩ := by
        dsimp only [r']
        exact dif_pos hy
      rw [h_eq]
      exact hr_x3 ⟨y, hy⟩
    have h5r := Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall
      t' x' r' (δ / 10) hr'_le 5 (by norm_num)
    rcases h5r with ⟨v, hv_sub, hv_disj, hcover⟩
    have hv_count : v.Countable := by
      let f : {y // y ∈ v} → Set (E 2) := fun y => interior (closedBall (y : E 2) (r' (y : E 2)))
      have h_open : ∀ (y : {y // y ∈ v}), IsOpen (f y) := fun _ => isOpen_interior
      have h_nonempty : ∀ (y : {y // y ∈ v}), (f y).Nonempty := by
        intro y
        have hpos : 0 < r' (y : E 2) := hr'_pos (y : E 2) (hv_sub y.prop)
        exact ⟨(y : E 2), Metric.ball_subset_interior_closedBall (mem_ball_self hpos)⟩
      have h_disj : Pairwise (Function.onFun Disjoint f) := by
        intro y z hyz
        have hne : (y : E 2) ≠ (z : E 2) := Subtype.coe_injective.ne hyz
        have h : Disjoint (closedBall (y : E 2) (r' (y : E 2))) (closedBall (z : E 2) (r' (z : E 2))) :=
          hv_disj y.prop z.prop hne
        exact h.mono interior_subset interior_subset
      haveI : Countable {y // y ∈ v} := Pairwise.countable_of_isOpen_disjoint h_disj h_open h_nonempty
      exact Set.countable_coe_iff.mp ‹Countable {y // y ∈ v}›
    have hR_cover : R ⊆ ⋃ y ∈ v, closedBall y (5 * r' y) := by
      intro z hz
      have h1 : z ∈ t' := hz
      have h2 : ∃ y ∈ v, closedBall z (r' z) ⊆ closedBall y (5 * r' y) := hcover z h1
      rcases h2 with ⟨y, hy, hsub⟩
      have h3 : z ∈ closedBall z (r' z) := by
        have h4 : 0 ≤ r' z := by linarith [hr'_pos z hz]
        exact mem_closedBall_self h4
      exact Set.mem_iUnion₂.mpr ⟨y, hy, hsub h3⟩
    have hC_sub_U : ∀ y ∈ v, closedBall y (r' y) ⊆ U := by
      intro y hy
      have h_y_in_R : y ∈ R := hv_sub hy
      have h_r'_eq : r' y = r_x ⟨y, h_y_in_R⟩ := by
        simp [r', h_y_in_R]
      rw [h_r'_eq]
      exact hr_x2 ⟨y, h_y_in_R⟩
    let Csmall : {y // y ∈ v} → Set (E 2) := fun y => closedBall (y : E 2) (r' (y : E 2))
    have hCsum : ∑' y : {y // y ∈ v}, volume (Csmall y) ≤ volume U := by
      have h_disj2 : Set.PairwiseDisjoint v (fun y : E 2 => closedBall y (r' y)) := hv_disj
      have h : volume (⋃ y ∈ v, closedBall y (r' y)) = ∑' y : {y // y ∈ v}, volume (Csmall y) := by
        rw [measure_biUnion hv_count h_disj2 (fun y _ => isClosed_closedBall.measurableSet)] <;> rfl
      rw [←h]
      have h_sub : (⋃ y ∈ v, closedBall y (r' y)) ⊆ U := by
        intro x hx
        rcases Set.mem_iUnion₂.mp hx with ⟨y, hy, hxy⟩
        exact hC_sub_U y hy hxy
      exact measure_mono h_sub
    let Ccover : {y // y ∈ v} → Set (E 2) := fun y => closedBall (y : E 2) (5 * r' (y : E 2))
    have hC_diam : ∀ (y : {y // y ∈ v}), Metric.diam (Ccover y) ≤ δ := by
      intro y
      have h1 : (y : E 2) ∈ v := y.prop
      have h2 : r' (y : E 2) ≤ δ / 10 := hr'_le (y : E 2) (hv_sub h1)
      have hpos : 0 ≤ r' (y : E 2) := by linarith [hr'_pos (y : E 2) (hv_sub h1)]
      have h3 : Metric.diam (Ccover y) = 2 * (5 * r' (y : E 2)) := by
        have h4 : Ccover y = closedBall (y : E 2) (5 * r' (y : E 2)) := by rfl
        rw [h4, Metric.diam_closedBall_eq (y : E 2) (by linarith)] <;> ring
      rw [h3]; linarith
    have h_sum_diam_C : ∑' y : {y // y ∈ v}, ENNReal.ofReal (Metric.diam (Ccover y)) ^ 2 ≤ ENNReal.ofReal ε := by
      have h1 : ∀ (y : {y // y ∈ v}), ENNReal.ofReal (Metric.diam (Ccover y)) ^ 2 =
          ENNReal.ofReal (100 / Real.pi) * volume (Csmall y) := by
        intro y
        have hpos : 0 < r' (y : E 2) := hr'_pos (y : E 2) (hv_sub y.prop)
        have hnonneg : 0 ≤ r' (y : E 2) := by linarith
        have h2 : Metric.diam (Ccover y) = 10 * r' (y : E 2) := by
          have h4 : Ccover y = closedBall (y : E 2) (5 * r' (y : E 2)) := by rfl
          have h5 : 0 ≤ 5 * r' (y : E 2) := by positivity
          rw [h4, Metric.diam_closedBall_eq (y : E 2) h5] <;> ring
        rw [h2]
        have h4 : volume (Csmall y) = ENNReal.ofReal (r' (y : E 2)) ^ 2 * ENNReal.ofReal Real.pi :=
          EuclideanSpace.volume_closedBall_fin_two (y : E 2) (r' (y : E 2))
        rw [h4]
        have h_goal : ENNReal.ofReal (10 * r' (y : E 2)) ^ 2 =
            ENNReal.ofReal (100 / Real.pi) * (ENNReal.ofReal (r' (y : E 2)) ^ 2 * ENNReal.ofReal Real.pi) := by
          have h6 : ENNReal.ofReal (10 * r' (y : E 2)) = 10 * ENNReal.ofReal (r' (y : E 2)) := by
            rw [ENNReal.ofReal_mul (by norm_num)] <;> norm_cast
          rw [h6]
          have h7 : ENNReal.ofReal (100 / Real.pi) * (ENNReal.ofReal (r' (y : E 2)) ^ 2 * ENNReal.ofReal Real.pi) =
              ENNReal.ofReal ((100 / Real.pi) * Real.pi) * ENNReal.ofReal (r' (y : E 2)) ^ 2 := by
            have h8 : ENNReal.ofReal (100 / Real.pi) * ENNReal.ofReal Real.pi = ENNReal.ofReal ((100 / Real.pi) * Real.pi) := by
              rw [← ENNReal.ofReal_mul (by positivity)]
            have h9 : ENNReal.ofReal (100 / Real.pi) * (ENNReal.ofReal (r' (y : E 2)) ^ 2 * ENNReal.ofReal Real.pi) =
                (ENNReal.ofReal (100 / Real.pi) * ENNReal.ofReal Real.pi) * ENNReal.ofReal (r' (y : E 2)) ^ 2 := by
              ring
            rw [h9, h8]
          rw [h7]
          have h9 : (100 / Real.pi) * Real.pi = 100 := by
            field_simp [Real.pi_ne_zero] <;> ring
          rw [h9]
          simp [pow_two] <;> ring
        exact h_goal
      calc
        ∑' y, ENNReal.ofReal (Metric.diam (Ccover y)) ^ 2
          = ∑' y, ENNReal.ofReal (100 / Real.pi) * volume (Csmall y) := by
            congr with y; exact h1 y
        _ = ENNReal.ofReal (100 / Real.pi) * ∑' y, volume (Csmall y) := by
            rw [ENNReal.tsum_mul_left]
        _ ≤ ENNReal.ofReal (100 / Real.pi) * volume U := by gcongr
        _ ≤ ENNReal.ofReal (100 / Real.pi) * ENNReal.ofReal ε' := by gcongr
        _ = ENNReal.ofReal ε := by
          have h10 : ENNReal.ofReal (100 / Real.pi) * ENNReal.ofReal ε' = ENNReal.ofReal ((100 / Real.pi) * ε') := by
            rw [← ENNReal.ofReal_mul (by positivity)]
          rw [h10]
          have h11 : (100 / Real.pi) * ε' = ε := by
            rw [hε'_def, hε_def]
            field_simp [Real.pi_ne_zero] <;> ring
          rw [h11]

    have hcover_all : s ⊆ (⋃ a : {a // a ∈ u}, Bsub a) ∪ (⋃ y : {y // y ∈ v}, Ccover y) := by
      intro x hx
      by_cases hR : x ∈ R
      · have h4 : x ∈ ⋃ y ∈ v, closedBall y (5 * r' y) := hR_cover hR
        have h5 : ∃ (y : E 2), y ∈ v ∧ x ∈ closedBall y (5 * r' y) := by
          simpa [Set.mem_biUnion] using h4
        rcases h5 with ⟨y, hy, hxy⟩
        let y' : {y // y ∈ v} := ⟨y, hy⟩
        have h6 : x ∈ Ccover y' := hxy
        have h_goal : x ∈ ⋃ (y' : {y // y ∈ v}), Ccover y' := by
          rw [Set.mem_iUnion]; exact ⟨y', h6⟩
        exact Or.inr h_goal
      · have h_notin : x ∉ R := hR
        have h4 : x ∈ ⋃ a ∈ u, B a := by
          by_contra h
          exact h_notin ⟨hx, h⟩
        have h5 : ∃ (a : ι), a ∈ u ∧ x ∈ B a := by
          simpa [Set.mem_biUnion] using h4
        rcases h5 with ⟨a, ha, hxa⟩
        let a' : {a // a ∈ u} := ⟨a, ha⟩
        have h6 : x ∈ Bsub a' := by
          have h7 : Bsub a' = B a := by rfl
          rw [h7]
          exact hxa
        have h_goal : x ∈ ⋃ (a' : {a // a ∈ u}), Bsub a' := by
          rw [Set.mem_iUnion]; exact ⟨a', h6⟩
        exact Or.inl h_goal

    -- Convert Metric.diam bounds to ediam bounds using boundedness of closed balls
    have h_ediam_B_eq : ∀ (a : {a // a ∈ u}), ediam (Bsub a) = ENNReal.ofReal (Metric.diam (Bsub a)) := by
      intro a
      have h_b : Bornology.IsBounded (Bsub a) := Metric.isBounded_closedBall
      have h_ne_top : ediam (Bsub a) ≠ ⊤ := h_b.ediam_ne_top
      have h : ENNReal.ofReal (Metric.diam (Bsub a)) = ediam (Bsub a) := by
        simp [Metric.diam, ENNReal.ofReal_toReal h_ne_top]
      exact h.symm
    have h_ediam_B : ∀ (a : {a // a ∈ u}), ediam (Bsub a) ≤ ENNReal.ofReal δ := by
      intro a
      rw [h_ediam_B_eq a]
      exact ENNReal.ofReal_le_ofReal (h_diam_B a)
    have h_sum_ediam_B : ∑' a : {a // a ∈ u}, ediam (Bsub a) ^ 2 ≤ 4 := by
      have h_eq : ∑' a, ediam (Bsub a) ^ 2 = ∑' a, ENNReal.ofReal (Metric.diam (Bsub a)) ^ 2 := by
        congr with a; rw [h_ediam_B_eq a]
      rw [h_eq]
      exact h_sum_diam_B
    have h_ediam_C_eq : ∀ (y : {y // y ∈ v}), ediam (Ccover y) = ENNReal.ofReal (Metric.diam (Ccover y)) := by
      intro y
      have h_b : Bornology.IsBounded (Ccover y) := Metric.isBounded_closedBall
      have h_ne_top : ediam (Ccover y) ≠ ⊤ := h_b.ediam_ne_top
      have h : ENNReal.ofReal (Metric.diam (Ccover y)) = ediam (Ccover y) := by
        simp [Metric.diam, ENNReal.ofReal_toReal h_ne_top]
      exact h.symm
    have h_ediam_C : ∀ (y : {y // y ∈ v}), ediam (Ccover y) ≤ ENNReal.ofReal δ := by
      intro y
      rw [h_ediam_C_eq y]
      exact ENNReal.ofReal_le_ofReal (hC_diam y)
    have h_sum_ediam_C : ∑' y : {y // y ∈ v}, ediam (Ccover y) ^ 2 ≤ ENNReal.ofReal ε := by
      have h_eq : ∑' y, ediam (Ccover y) ^ 2 = ∑' y, ENNReal.ofReal (Metric.diam (Ccover y)) ^ 2 := by
        congr with y; rw [h_ediam_C_eq y]
      rw [h_eq]
      exact h_sum_diam_C

    exact ⟨u, v, hu_count, hv_count, Bsub, Ccover, hcover_all, h_ediam_B, h_ediam_C, h_sum_ediam_B, h_sum_ediam_C⟩

  -- Now use hausdorffMeasure_le_liminf_tsum
  let r : ℕ → ENNReal := fun k => (k + 1 : ENNReal)⁻¹
  have hr : Tendsto r atTop (nhds (0 : ENNReal)) := by
    have h_shift : Tendsto (fun k : ℕ => k + 1) atTop atTop := tendsto_add_atTop_nat 1
    have h_main_tendsto : Tendsto (fun k : ℕ => ((k + 1 : ℕ) : ENNReal)⁻¹) atTop (nhds (0 : ENNReal)) :=
      ENNReal.tendsto_inv_nat_nhds_zero.comp h_shift
    simpa [r] using h_main_tendsto
  have h_r_eq : ∀ k : ℕ, r k = ENNReal.ofReal (1 / (k + 1 : ℝ)) := by
    intro k
    have h_pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    have h5 : ((k + 1 : ℕ) : ENNReal)⁻¹ = ENNReal.ofReal (1 / ((k + 1 : ℕ) : ℝ)) := by
      have h6 : ENNReal.ofReal (1 / ((k + 1 : ℕ) : ℝ)) = (ENNReal.ofReal ((k + 1 : ℕ) : ℝ))⁻¹ := by
        rw [← ENNReal.ofReal_inv_of_pos h_pos] <;> ring_nf
      rw [h6] <;> norm_cast
    simpa [r] using h5

  -- Extract data from h_main using Classical.choose at each level
  let u_k : ℕ → Set (E 2 × ℝ) := fun k => Classical.choose (h_main k)
  have h1_k : ∀ k, ∃ (v : Set (E 2)) (hu : (u_k k).Countable) (hv : v.Countable)
      (B : {a // a ∈ u_k k} → Set (E 2))
      (C : {y // y ∈ v} → Set (E 2)), _ :=
    fun k => Classical.choose_spec (h_main k)
  let v_k : ℕ → Set (E 2) := fun k => Classical.choose (h1_k k)
  have h2_k : ∀ k, ∃ (hu : (u_k k).Countable) (hv : (v_k k).Countable)
      (B : {a // a ∈ u_k k} → Set (E 2))
      (C : {y // y ∈ v_k k} → Set (E 2)), _ :=
    fun k => Classical.choose_spec (h1_k k)
  let hu_k : ∀ k, (u_k k).Countable := fun k => Classical.choose (h2_k k)
  have h3_k : ∀ k, ∃ (hv : (v_k k).Countable)
      (B : {a // a ∈ u_k k} → Set (E 2))
      (C : {y // y ∈ v_k k} → Set (E 2)), _ :=
    fun k => Classical.choose_spec (h2_k k)
  let hv_k : ∀ k, (v_k k).Countable := fun k => Classical.choose (h3_k k)
  have h4_k : ∀ k, ∃ (B : {a // a ∈ u_k k} → Set (E 2))
      (C : {y // y ∈ v_k k} → Set (E 2)), _ :=
    fun k => Classical.choose_spec (h3_k k)
  let B_k : ∀ k, {a // a ∈ u_k k} → Set (E 2) := fun k => Classical.choose (h4_k k)
  have h5_k : ∀ k, ∃ (C : {y // y ∈ v_k k} → Set (E 2)), _ :=
    fun k => Classical.choose_spec (h4_k k)
  let C_k : ∀ k, {y // y ∈ v_k k} → Set (E 2) := fun k => Classical.choose (h5_k k)
  have h6_k : ∀ k, _ := fun k => Classical.choose_spec (h5_k k)

  let ι : ℕ → Type := fun k => {a // a ∈ u_k k} ⊕ {y // y ∈ v_k k}
  let t : ∀ k, ι k → Set (E 2) := fun k => Sum.elim (B_k k) (C_k k)

  haveI h_countable : ∀ k, Countable (ι k) := by
    intro k
    letI : Countable {a // a ∈ u_k k} := Set.countable_coe_iff.mpr (hu_k k)
    letI : Countable {y // y ∈ v_k k} := Set.countable_coe_iff.mpr (hv_k k)
    exact inferInstance

  -- Projection order: h6_k k = cover ∧ ediam_B ∧ ediam_C ∧ sum_B ∧ sum_C
  have hcover_all : ∀ k, s ⊆ (⋃ a : {a // a ∈ u_k k}, B_k k a) ∪ (⋃ y : {y // y ∈ v_k k}, C_k k y) :=
    fun k => (h6_k k).1
  have hB_ediam : ∀ k, ∀ (a : {a // a ∈ u_k k}), ediam (B_k k a) ≤ r k :=
    fun k a => by
      have h : ediam (B_k k a) ≤ ENNReal.ofReal (1 / (k + 1 : ℝ)) := (h6_k k).2.1 a
      rw [h_r_eq k] at *
      exact h
  have hC_ediam : ∀ k, ∀ (y : {y // y ∈ v_k k}), ediam (C_k k y) ≤ r k :=
    fun k y => by
      have h : ediam (C_k k y) ≤ ENNReal.ofReal (1 / (k + 1 : ℝ)) := (h6_k k).2.2.1 y
      rw [h_r_eq k] at *
      exact h
  have hB_sum : ∀ k, ∑' a : {a // a ∈ u_k k}, ediam (B_k k a) ^ 2 ≤ 4 :=
    fun k => (h6_k k).2.2.2.1
  have hC_sum : ∀ k, ∑' y : {y // y ∈ v_k k}, ediam (C_k k y) ^ 2 ≤ r k :=
    fun k => by
      have h : ∑' y, ediam (C_k k y) ^ 2 ≤ ENNReal.ofReal (1 / (k + 1 : ℝ)) := (h6_k k).2.2.2.2
      rw [h_r_eq k] at *
      exact h

  have ht : ∀ᶠ n in atTop, ∀ (i : ι n), ediam (t n i) ≤ r n := by
    filter_upwards with k
    intro i
    cases i with
    | inl a => exact hB_ediam k a
    | inr y => exact hC_ediam k y
  have hst : ∀ᶠ n in atTop, s ⊆ ⋃ (i : ι n), t n i := by
    filter_upwards with k
    have hcover := hcover_all k
    intro x hx
    have h : x ∈ (⋃ a : {a // a ∈ u_k k}, B_k k a) ∪ (⋃ y : {y // y ∈ v_k k}, C_k k y) := hcover hx
    cases h with
    | inl hleft =>
      have h' : ∃ (a : {a // a ∈ u_k k}), x ∈ B_k k a := by
        simpa [Set.mem_iUnion] using hleft
      rcases h' with ⟨a, ha⟩
      let i : ι k := Sum.inl a
      have h_t : t k i = B_k k a := by
        simp [t, i]
        <;> rfl
      have h_i : x ∈ t k i := by
        rw [h_t]
        exact ha
      exact Set.mem_iUnion.mpr ⟨i, h_i⟩
    | inr hright =>
      have h' : ∃ (y : {y // y ∈ v_k k}), x ∈ C_k k y := by
        simpa [Set.mem_iUnion] using hright
      rcases h' with ⟨y, hy⟩
      let i : ι k := Sum.inr y
      have h_t : t k i = C_k k y := by
        simp [t, i]
        <;> rfl
      have h_i : x ∈ t k i := by
        rw [h_t]
        exact hy
      exact Set.mem_iUnion.mpr ⟨i, h_i⟩
  have hsum : ∀ k, ∑' (i : ι k), ediam (t k i) ^ 2 ≤ 4 + r k := by
    intro k
    let f : ι k → ENNReal := fun i => ediam (t k i) ^ 2
    have h_eq : ∑' (i : ι k), f i = (∑' a, f (Sum.inl a)) + (∑' y, f (Sum.inr y)) := by
      exact Summable.tsum_sum (f := f) ENNReal.summable ENNReal.summable
    rw [h_eq]
    have h1 : (∑' a, f (Sum.inl a)) = ∑' a, ediam (B_k k a) ^ 2 := by rfl
    have h2 : (∑' y, f (Sum.inr y)) = ∑' y, ediam (C_k k y) ^ 2 := by rfl
    rw [h1, h2]
    exact add_le_add (hB_sum k) (hC_sum k)
  have h_pow_eq : ∀ (x : ENNReal), x ^ (2 : ℝ) = x ^ (2 : ℕ) := by
    intro x
    exact ENNReal.rpow_natCast x 2
  have h_main2_raw : μH[2] s ≤ liminf (fun k : ℕ => ∑' (i : ι k), ediam (t k i) ^ (2 : ℝ)) atTop :=
    MeasureTheory.Measure.hausdorffMeasure_le_liminf_tsum 2 s r hr t ht hst
  have h_congr : (fun k : ℕ => ∑' (i : ι k), ediam (t k i) ^ (2 : ℝ)) =
      (fun k : ℕ => ∑' (i : ι k), ediam (t k i) ^ (2 : ℕ)) := by
    funext k
    congr with i
    exact h_pow_eq (ediam (t k i))
  have h_main2 : μH[2] s ≤ liminf (fun k : ℕ => ∑' (i : ι k), ediam (t k i) ^ 2) atTop := by
    rw [h_congr] at h_main2_raw
    exact h_main2_raw
  have hsum_eventually : ∀ᶠ (k : ℕ) in atTop, ∑' (i : ι k), ediam (t k i) ^ 2 ≤ 4 + r k := by
    filter_upwards with k
    exact hsum k
  have h_liminf_le : liminf (fun k : ℕ => ∑' (i : ι k), ediam (t k i) ^ 2) atTop ≤
      liminf (fun k : ℕ => 4 + r k) atTop :=
    Filter.liminf_le_liminf hsum_eventually
  have h_main3 : μH[2] s ≤ liminf (fun k : ℕ => 4 + r k) atTop :=
    le_trans h_main2 h_liminf_le
  have h_tendsto : Tendsto (fun k : ℕ => (4 : ENNReal) + r k) atTop (nhds (4 : ENNReal)) := by
    have h : Tendsto (fun k : ℕ => (4 : ENNReal) + r k) atTop (nhds ((4 : ENNReal) + (0 : ENNReal))) :=
      tendsto_const_nhds.add hr
    simpa using h
  have h_liminf : liminf (fun k : ℕ => 4 + r k) atTop = 4 :=
    h_tendsto.liminf_eq
  rw [h_liminf] at h_main3
  exact h_main3

/-- The scalar factor relating `volume` and `μH[2]` on `E 2` is `π / 4`.

That is, `volume = (π / 4) • μH[2]`, equivalently `μH[2] = (4 / π) • volume`. -/
theorem addHaarScalarFactor_twoDim_eq_pi_div_four :
    (volume : Measure (E 2)) = ENNReal.ofReal (Real.pi / 4) • μH[2] := by
  have h_finrank_nat : Module.finrank ℝ (E 2) = 2 := by
    have h : Module.finrank ℝ (E 2) = Fintype.card (Fin 2) := by
      exact finrank_euclideanSpace_fin
    rw [h]
    <;> decide
  have h_finrank : (↑(Module.finrank ℝ (E 2)) : ℝ) = (2 : ℝ) := by
    rw [h_finrank_nat] <;> norm_num
  letI : (MeasureTheory.Measure.hausdorffMeasure (2 : ℝ) : Measure (E 2)).IsAddHaarMeasure := by
    have h : (MeasureTheory.Measure.hausdorffMeasure (↑(Module.finrank ℝ (E 2)))).IsAddHaarMeasure :=
      MeasureTheory.isAddHaarMeasure_hausdorffMeasure (E := E 2)
    exact h_finrank ▸ h
  have h_def : (μHE[2] : Measure (E 2)) =
      MeasureTheory.Measure.addHaarScalarFactor (volume : Measure (E 2)) μH[2] • μH[2] :=
    MeasureTheory.Measure.euclideanHausdorffMeasure_def 2
  have h_eq_vol : (μHE[2] : Measure (E 2)) = volume :=
    EuclideanSpace.euclideanHausdorffMeasure_eq_volume 2
  have h_upper : μH[2] (ball (0 : E 2) 1) ≤ 4 := hausdorff_twoDim_ball_le_four
  have h_lower : (ENNReal.ofReal (4 / Real.pi)) * volume (ball (0 : E 2) 1) ≤ μH[2] (ball (0 : E 2) 1) :=
    hausdorff_ge_area_two_dim (ball (0 : E 2) 1)
  have h_vol : volume (ball (0 : E 2) 1) = ENNReal.ofReal Real.pi := by
    simpa using EuclideanSpace.volume_ball_fin_two 0 1
  have h_eq : μH[2] (ball (0 : E 2) 1) = 4 := by
    rw [h_vol] at h_lower
    have h3 : (ENNReal.ofReal (4 / Real.pi)) * ENNReal.ofReal Real.pi = 4 := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      have h4 : (4 / Real.pi) * Real.pi = 4 := by field_simp [Real.pi_ne_zero] <;> ring
      rw [h4] <;> norm_cast
    rw [h3] at h_lower
    exact le_antisymm h_upper h_lower
  have h5 : (μHE[2] : Measure (E 2)) (ball (0 : E 2) 1) = volume (ball (0 : E 2) 1) := by
    rw [h_eq_vol]
  let c_nn : NNReal := MeasureTheory.Measure.addHaarScalarFactor (volume : Measure (E 2)) μH[2]
  have h7 : (μHE[2] : Measure (E 2)) (ball (0 : E 2) 1) = (c_nn : ENNReal) * μH[2] (ball (0 : E 2) 1) := by
    rw [h_def] <;> rfl
  have h6 : (c_nn : ENNReal) * μH[2] (ball (0 : E 2) 1) = ENNReal.ofReal Real.pi := by
    rw [← h7, h5, h_vol]
  rw [h_eq] at h6
  have h_cancel : (c_nn : ENNReal) = ENNReal.ofReal (Real.pi / 4) := by
    have h13 : ENNReal.ofReal (Real.pi / 4) * (4 : ENNReal) = ENNReal.ofReal Real.pi := by
      have h_pos1 : 0 ≤ (Real.pi / 4) := by positivity
      have h_pos2 : 0 ≤ (4 : ℝ) := by norm_num
      calc
        ENNReal.ofReal (Real.pi / 4) * (4 : ENNReal)
          = ENNReal.ofReal (Real.pi / 4) * ENNReal.ofReal (4 : ℝ) := by norm_cast
        _ = ENNReal.ofReal ((Real.pi / 4) * (4 : ℝ)) := by
          rw [ENNReal.ofReal_mul h_pos1]
        _ = ENNReal.ofReal Real.pi := by
          have h : (Real.pi / 4) * (4 : ℝ) = Real.pi := by ring
          rw [h]
    have h14 : (c_nn : ENNReal) * (4 : ENNReal) = ENNReal.ofReal (Real.pi / 4) * (4 : ENNReal) := by
      exact h6.trans h13.symm
    have h15 : (4 : ENNReal) ≠ 0 := by norm_num
    have h16 : (4 : ENNReal) ≠ ⊤ := by norm_num
    exact (ENNReal.mul_left_inj h15 h16).mp h14
  have h_final : (μHE[2] : Measure (E 2)) = c_nn • μH[2] := h_def
  let d : NNReal := NNReal.mk (Real.pi / 4) (by positivity)
  have hd : (d : ENNReal) = ENNReal.ofReal (Real.pi / 4) := by
    exact (ENNReal.ofReal_eq_coe_nnreal (by positivity)).symm
  have h_cancel_nn : c_nn = d := by
    apply ENNReal.coe_injective
    rw [h_cancel, ←hd]
  have h_goal : (c_nn • μH[2] : Measure (E 2)) = (d • μH[2] : Measure (E 2)) := by
    exact congr_arg (fun x : NNReal => (x • μH[2] : Measure (E 2))) h_cancel_nn
  have h_smul_compat : (d • μH[2] : Measure (E 2)) = ((d : ENNReal) • μH[2] : Measure (E 2)) := by
    ext s
    simp [Measure.smul_apply]
    <;> rfl
  have h_goal2 : (d • μH[2] : Measure (E 2)) = (ENNReal.ofReal (Real.pi / 4) • μH[2] : Measure (E 2)) := by
    rw [h_smul_compat, hd]
  calc
    (volume : Measure (E 2))
      = (μHE[2] : Measure (E 2)) := h_eq_vol.symm
    _ = (c_nn • μH[2] : Measure (E 2)) := h_final
    _ = (d • μH[2] : Measure (E 2)) := h_goal
    _ = (ENNReal.ofReal (Real.pi / 4) • μH[2] : Measure (E 2)) := h_goal2

end Geometry
