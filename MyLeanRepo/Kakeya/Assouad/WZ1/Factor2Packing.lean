import MyLeanRepo.Kakeya.Assouad.TubeAlignmentGeometry
import MyLeanRepo.Kakeya.Assouad.EssentiallyDistinctCardBound
import MyLeanRepo.Kakeya.Assouad.WZ1.CoarseDirectionPacking.GridCounting
import MyLeanRepo.Kakeya.Streamlined.Families
import Mathlib.Tactic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Local six-parameter packing for nested tubes

This module bounds a family of essentially distinct `sigma`-tubes when each
member contains a fine tube lying in one fixed `rho`-tube.  The local estimate
retains all three base and all three direction parameters and therefore has
the genuine exponent six.
-/

noncomputable section

open MeasureTheory Metric Set Finset
open Kakeya.Streamlined

namespace Kakeya.Assouad

/-- If two `sigma`-tubes have base and direction differences at most
`sigma / 16`, they are not essentially distinct. -/
lemma close_tubes_not_ed_general
    {sigma : ℝ} (hsigma : 0 < sigma) (hsigma_small : sigma ≤ 1 / 8)
    {T U : Kakeya.DeltaTube sigma}
    (hbase : ‖T.base - U.base‖ ≤ sigma / 16)
    (hdir : ‖T.direction - U.direction‖ ≤ sigma / 16) :
    ¬ T.EssentiallyDistinct U := by
  set d : ℝ := sigma / 16 with hd_def
  set r : ℝ := sigma - 2 * d with hr_def
  have hr_pos : 0 < r := by linarith
  have hr_eq : r = 7 * sigma / 8 := by linarith
  let T' : Kakeya.DeltaTube r :=
    ⟨T.base, T.direction, T.direction_unit⟩
  have h_seg_compact :
      IsCompact (Kakeya.unitSegment T'.base T'.direction) := by
    apply IsCompact.image isCompact_Icc
    fun_prop
  have h1 : T'.carrier ⊆ T.carrier := by
    intro x hx
    have h_eq :
        T'.carrier =
          ⋃ y ∈ Kakeya.unitSegment T'.base T'.direction,
            Metric.closedBall y r :=
      h_seg_compact.cthickening_eq_biUnion_closedBall hr_pos.le
    rw [h_eq] at hx
    rcases Set.mem_iUnion₂.mp hx with ⟨y, hy, hxy⟩
    rcases hy with ⟨t, ht, rfl⟩
    have hdist :
        dist x (T.base + t • T.direction) ≤ r := by
      simpa [Metric.mem_closedBall] using hxy
    exact Metric.mem_cthickening_of_dist_le
      x (T.base + t • T.direction) sigma
      (Kakeya.unitSegment T.base T.direction) ⟨t, ht, rfl⟩
      (by linarith)
  have h2 : T'.carrier ⊆ U.carrier := by
    intro x hx
    have h_eq :
        T'.carrier =
          ⋃ y ∈ Kakeya.unitSegment T'.base T'.direction,
            Metric.closedBall y r :=
      h_seg_compact.cthickening_eq_biUnion_closedBall hr_pos.le
    rw [h_eq] at hx
    rcases Set.mem_iUnion₂.mp hx with ⟨y, hy, hxy⟩
    rcases hy with ⟨t, ht, rfl⟩
    have hdist_xp :
        dist x (T.base + t • T.direction) ≤ r := by
      simpa [Metric.mem_closedBall] using hxy
    let p := T.base + t • T.direction
    let q := U.base + t • U.direction
    have h_t_nonneg : 0 ≤ t := ht.1
    have h_t_le_one : t ≤ 1 := ht.2
    have h_eq_pq :
        p - q =
          T.base - U.base + t • (T.direction - U.direction) := by
      have h1 :
          p - q =
            (T.base + t • T.direction) -
              (U.base + t • U.direction) := by
        rfl
      rw [h1]
      ext i
      simp [smul_sub] <;> ring
    have h_pq : dist p q ≤ 2 * d := by
      dsimp only [dist, p, q]
      calc
        ‖p - q‖ =
            ‖T.base - U.base +
              t • (T.direction - U.direction)‖ := by rw [h_eq_pq]
        _ ≤ ‖T.base - U.base‖ +
              ‖t • (T.direction - U.direction)‖ := norm_add_le _ _
        _ = ‖T.base - U.base‖ +
              |t| * ‖T.direction - U.direction‖ := by
          rw [norm_smul, Real.norm_eq_abs]
        _ = ‖T.base - U.base‖ +
              t * ‖T.direction - U.direction‖ := by
          rw [abs_of_nonneg h_t_nonneg]
        _ ≤ d + t * d := by
          have hmul :
              t * ‖T.direction - U.direction‖ ≤ t * d :=
            mul_le_mul_of_nonneg_left hdir h_t_nonneg
          linarith
        _ ≤ 2 * d := by
          have hd_nonneg : 0 ≤ d := by linarith
          have hmul : t * d ≤ d := by
            rw [mul_comm]
            exact mul_le_of_le_one_right hd_nonneg h_t_le_one
          linarith
    have h_xq : dist x q ≤ sigma := by
      calc
        dist x q ≤ dist x p + dist p q := dist_triangle _ _ _
        _ ≤ r + 2 * d := by gcongr
        _ = sigma := by linarith
    exact Metric.mem_cthickening_of_dist_le
      x q sigma (Kakeya.unitSegment U.base U.direction)
      ⟨t, ht, rfl⟩ h_xq
  have h3 : T'.carrier ⊆ T.carrier ∩ U.carrier := by
    intro x hx
    exact ⟨h1 hx, h2 hx⟩
  have h4 : T'.volume ≤ volume (T.carrier ∩ U.carrier) :=
    measure_mono h3
  have h_lower : ENNReal.ofReal (Real.pi * r ^ 2) ≤ T'.volume :=
    tube_volume_lower_pi hr_pos T'
  have h_upper_T :
      T.volume ≤
        ENNReal.ofReal
          (Real.pi * sigma ^ 2 * (1 + 2 * sigma)) :=
    tube_volume_upper_pi hsigma T
  have h_upper_U :
      U.volume ≤
        ENNReal.ofReal
          (Real.pi * sigma ^ 2 * (1 + 2 * sigma)) :=
    tube_volume_upper_pi hsigma U
  have h_upper_max :
      max T.volume U.volume ≤
        ENNReal.ofReal
          (Real.pi * sigma ^ 2 * (1 + 2 * sigma)) :=
    max_le h_upper_T h_upper_U
  have h_real1 :
      Real.pi * r ^ 2 >
        Real.pi * sigma ^ 2 * (1 + 2 * sigma) / 2 := by
    rw [hr_eq]
    have h7 :
        (7 * sigma / 8) ^ 2 >
          sigma ^ 2 * (1 + 2 * sigma) / 2 := by
      nlinarith [hsigma_small]
    nlinarith [mul_lt_mul_of_pos_left h7 Real.pi_pos]
  have h_pos_r : 0 < Real.pi * r ^ 2 := by positivity
  have h_enn1 :
      ENNReal.ofReal
          (Real.pi * sigma ^ 2 * (1 + 2 * sigma) / 2) <
        ENNReal.ofReal (Real.pi * r ^ 2) :=
    (ENNReal.ofReal_lt_ofReal_iff h_pos_r).mpr h_real1
  have h_step1 :
      (1 / 2 : ENNReal) * max T.volume U.volume ≤
        (1 / 2 : ENNReal) *
          ENNReal.ofReal
            (Real.pi * sigma ^ 2 * (1 + 2 * sigma)) :=
    mul_le_mul' le_rfl h_upper_max
  have h_step2 :
      (1 / 2 : ENNReal) *
          ENNReal.ofReal
            (Real.pi * sigma ^ 2 * (1 + 2 * sigma)) =
        ENNReal.ofReal
          (Real.pi * sigma ^ 2 * (1 + 2 * sigma) / 2) := by
    have h_coe :
        (1 / 2 : ENNReal) = ENNReal.ofReal (1 / 2 : ℝ) := by simp
    rw [h_coe, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    congr 1
    ring
  have h_contra :
      (1 / 2 : ENNReal) * max T.volume U.volume < T'.volume := by
    calc
      (1 / 2 : ENNReal) * max T.volume U.volume
          ≤ (1 / 2 : ENNReal) *
              ENNReal.ofReal
                (Real.pi * sigma ^ 2 * (1 + 2 * sigma)) := h_step1
      _ = ENNReal.ofReal
            (Real.pi * sigma ^ 2 * (1 + 2 * sigma) / 2) := h_step2
      _ < ENNReal.ofReal (Real.pi * r ^ 2) := h_enn1
      _ ≤ T'.volume := h_lower
  intro h_ed
  have h9 :
      volume (T.carrier ∩ U.carrier) ≤
        (1 / 2 : ENNReal) * max T.volume U.volume := by
    simpa [Kakeya.DeltaTube.EssentiallyDistinct] using h_ed
  exact not_le.mpr h_contra (h4.trans h9)

/-- If `D.carrier ⊆ T.carrier`, then the oriented parameters of `T` are
within `O(sigma)` of one of the two orientations of `D`. -/
lemma containment_alignment_bound
    {delta sigma : ℝ} (hdelta : 0 ≤ delta) (hsigma : 0 < sigma)
    (D : Kakeya.DeltaTube delta) (T : Kakeya.DeltaTube sigma)
    (h_cont : D.carrier ⊆ T.carrier) :
    (‖D.direction - T.direction‖ ≤ 4 * sigma ∧
      ‖T.base - D.base‖ ≤ 3 * sigma) ∨
    (‖D.direction + T.direction‖ ≤ 4 * sigma ∧
      ‖T.base - (D.base + D.direction)‖ ≤ 3 * sigma) := by
  have h1 : D.base ∈ D.carrier := by
    exact Metric.mem_cthickening_of_dist_le
      D.base D.base delta
      (Kakeya.unitSegment D.base D.direction)
      ⟨0, by norm_num, by simp⟩ (by simp [hdelta])
  have h2 : D.base + D.direction ∈ D.carrier := by
    exact Metric.mem_cthickening_of_dist_le
      (D.base + D.direction) (D.base + D.direction) delta
      (Kakeya.unitSegment D.base D.direction)
      ⟨1, by norm_num, by simp⟩ (by simp [hdelta])
  rcases exists_closest_on_axis hsigma.le T D.base (h_cont h1) with
    ⟨s0, hs0, hd0⟩
  rcases exists_closest_on_axis hsigma.le T
      (D.base + D.direction) (h_cont h2) with
    ⟨s1, hs1, hd1⟩
  set p0 : Point3 := T.base + s0 • T.direction with hp0
  set p1 : Point3 := T.base + s1 • T.direction with hp1
  have h_diff :
      ‖D.direction - (s1 - s0) • T.direction‖ ≤ 2 * sigma := by
    have h_main :
        D.direction - (s1 - s0) • T.direction =
          ((D.base + D.direction) - p1) - (D.base - p0) := by
      simp [hp0, hp1, sub_smul]
      abel
    rw [h_main]
    have h1' : ‖(D.base + D.direction) - p1‖ ≤ sigma := by
      simpa [dist_eq_norm] using hd1
    have h2' : ‖D.base - p0‖ ≤ sigma := by
      simpa [dist_eq_norm] using hd0
    exact (norm_sub_le _ _).trans (by linarith)
  by_cases h : s0 ≤ s1
  · have hpos : 0 ≤ s1 - s0 := by linarith
    have hle : s1 - s0 ≤ 1 := by linarith [hs0.1, hs0.2, hs1.1, hs1.2]
    have hnorm :
        ‖(s1 - s0) • T.direction‖ = s1 - s0 := by
      rw [norm_smul, T.direction_unit, Real.norm_eq_abs,
        abs_of_nonneg hpos]
      ring
    have habs : |1 - (s1 - s0)| ≤ 2 * sigma := by
      have h4 :=
        abs_norm_sub_norm_le D.direction
          ((s1 - s0) • T.direction)
      rw [D.direction_unit, hnorm] at h4
      exact h4.trans h_diff
    have hs0_bound : s0 ≤ 2 * sigma := by
      have hgap : 1 - (s1 - s0) ≤ 2 * sigma := by
        exact (le_abs_self _).trans habs
      linarith [hs1.2]
    have hdir : ‖D.direction - T.direction‖ ≤ 4 * sigma := by
      have htail :
          ‖(s1 - s0) • T.direction - T.direction‖ =
            |1 - (s1 - s0)| := by
        rw [show
          (s1 - s0) • T.direction - T.direction =
            (s1 - s0 - 1) • T.direction by
              ext i
              simp [smul_eq_mul]
              ring]
        rw [norm_smul, T.direction_unit, Real.norm_eq_abs]
        have heq : |s1 - s0 - 1| = |1 - (s1 - s0)| := by
          rw [show s1 - s0 - 1 = -(1 - (s1 - s0)) by ring, abs_neg]
        rw [heq]
        ring
      have htri :
          ‖D.direction - T.direction‖ ≤
            ‖D.direction - (s1 - s0) • T.direction‖ +
              ‖(s1 - s0) • T.direction - T.direction‖ := by
        exact (by
          have heq :
              D.direction - T.direction =
                (D.direction - (s1 - s0) • T.direction) +
                  ((s1 - s0) • T.direction - T.direction) := by abel
          rw [heq]
          exact norm_add_le _ _)
      rw [htail] at htri
      linarith
    have hbase : ‖T.base - D.base‖ ≤ 3 * sigma := by
      have hb0 : ‖T.base - p0‖ = s0 := by
        rw [show T.base - p0 = (-s0) • T.direction by
          simp [hp0] <;> abel]
        rw [norm_smul, T.direction_unit, Real.norm_eq_abs,
          abs_neg, abs_of_nonneg hs0.1]
        ring
      have hdp : ‖p0 - D.base‖ ≤ sigma := by
        simpa [norm_sub_rev, dist_eq_norm] using hd0
      calc
        ‖T.base - D.base‖ ≤ ‖T.base - p0‖ + ‖p0 - D.base‖ := by
          rw [show T.base - D.base =
            (T.base - p0) + (p0 - D.base) by abel]
          exact norm_add_le _ _
        _ ≤ 3 * sigma := by rw [hb0]; linarith
    exact Or.inl ⟨hdir, hbase⟩
  · have hpos : 0 ≤ s0 - s1 := by linarith
    have hle : s0 - s1 ≤ 1 := by linarith [hs0.1, hs0.2, hs1.1, hs1.2]
    have hnorm :
        ‖(s0 - s1) • T.direction‖ = s0 - s1 := by
      rw [norm_smul, T.direction_unit, Real.norm_eq_abs,
        abs_of_nonneg hpos]
      ring
    have hdiff' :
        ‖D.direction + (s0 - s1) • T.direction‖ ≤ 2 * sigma := by
      have h_eq :
          D.direction + (s0 - s1) • T.direction =
            D.direction - (s1 - s0) • T.direction := by
        ext i
        simp [smul_eq_mul] <;> ring
      rw [h_eq]
      exact h_diff
    have habs : |1 - (s0 - s1)| ≤ 2 * sigma := by
      have h4 :=
        abs_norm_sub_norm_le D.direction
          (-((s0 - s1) • T.direction))
      rw [D.direction_unit, norm_neg, hnorm] at h4
      have hright :
          ‖D.direction - -((s0 - s1) • T.direction)‖ =
            ‖D.direction + (s0 - s1) • T.direction‖ := by
        congr 1
        abel
      rw [hright] at h4
      exact h4.trans hdiff'
    have hs1_bound : s1 ≤ 2 * sigma := by
      have hgap : 1 - (s0 - s1) ≤ 2 * sigma :=
        (le_abs_self _).trans habs
      linarith [hs0.2]
    have hdir : ‖D.direction + T.direction‖ ≤ 4 * sigma := by
      have htail :
          ‖T.direction - (s0 - s1) • T.direction‖ =
            |1 - (s0 - s1)| := by
        rw [show
          T.direction - (s0 - s1) • T.direction =
            (1 - (s0 - s1)) • T.direction by
              ext i
              simp [smul_eq_mul]
              ring]
        rw [norm_smul, T.direction_unit, Real.norm_eq_abs]
        ring
      have htri :
          ‖D.direction + T.direction‖ ≤
            ‖D.direction + (s0 - s1) • T.direction‖ +
              ‖T.direction - (s0 - s1) • T.direction‖ := by
        rw [show D.direction + T.direction =
          (D.direction + (s0 - s1) • T.direction) +
            (T.direction - (s0 - s1) • T.direction) by abel]
        exact norm_add_le _ _
      rw [htail] at htri
      linarith
    have hbase :
        ‖T.base - (D.base + D.direction)‖ ≤ 3 * sigma := by
      have hb1 : ‖T.base - p1‖ = s1 := by
        rw [show T.base - p1 = (-s1) • T.direction by
          simp [hp1] <;> abel]
        rw [norm_smul, T.direction_unit, Real.norm_eq_abs,
          abs_neg, abs_of_nonneg hs1.1]
        ring
      have hdp :
          ‖p1 - (D.base + D.direction)‖ ≤ sigma := by
        simpa [norm_sub_rev, dist_eq_norm] using hd1
      calc
        ‖T.base - (D.base + D.direction)‖ ≤
            ‖T.base - p1‖ + ‖p1 - (D.base + D.direction)‖ := by
          rw [show T.base - (D.base + D.direction) =
            (T.base - p1) + (p1 - (D.base + D.direction)) by abel]
          exact norm_add_le _ _
        _ ≤ 3 * sigma := by rw [hb1]; linarith
    exact Or.inr ⟨hdir, hbase⟩

/-- A three-dimensional integer grid cell. -/
def Grid3 : Type := ℤ × ℤ × ℤ

/-- The grid cell containing a point. -/
def grid3 (h : ℝ) (p : Point3) : Grid3 :=
  (Int.floor (p 0 / h), Int.floor (p 1 / h), Int.floor (p 2 / h))

/-- Points in one three-dimensional grid cell are close. -/
lemma grid3_close
    {h : ℝ} (hh : 0 < h) {p q : Point3}
    (hcell : grid3 h p = grid3 h q) :
    ‖p - q‖ < Real.sqrt 3 * h := by
  have h_eq :
      (Int.floor (p 0 / h), Int.floor (p 1 / h), Int.floor (p 2 / h)) =
        (Int.floor (q 0 / h), Int.floor (q 1 / h), Int.floor (q 2 / h)) :=
    hcell
  have hd0 : |p 0 - q 0| < h :=
    grid1d_close hh (by simp [Prod.ext_iff] at h_eq <;> tauto)
  have hd1 : |p 1 - q 1| < h :=
    grid1d_close hh (by simp [Prod.ext_iff] at h_eq <;> tauto)
  have hd2 : |p 2 - q 2| < h :=
    grid1d_close hh (by simp [Prod.ext_iff] at h_eq <;> tauto)
  have hnorm2 :
      ‖p - q‖ ^ 2 =
        (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 + (p 2 - q 2) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
    simp [Fin.sum_univ_succ]
    ring
  have hsq : ‖p - q‖ ^ 2 < 3 * h ^ 2 := by
    rw [hnorm2]
    have h0 : (p 0 - q 0) ^ 2 < h ^ 2 := by nlinarith [abs_lt.mp hd0]
    have h1 : (p 1 - q 1) ^ 2 < h ^ 2 := by nlinarith [abs_lt.mp hd1]
    have h2 : (p 2 - q 2) ^ 2 < h ^ 2 := by nlinarith [abs_lt.mp hd2]
    nlinarith
  have h_sqrt3_sq : (Real.sqrt 3) ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num)
  have h_pos1 : 0 ≤ ‖p - q‖ := by positivity
  have h_pos2 : 0 ≤ Real.sqrt 3 * h := by positivity
  nlinarith [Real.sqrt_nonneg 3, h_sqrt3_sq]

private lemma factor2_coord_le_norm (x : Point3) (i : Fin 3) :
    |x i| ≤ ‖x‖ := by
  have h_norm2 :
      ‖x‖ ^ 2 = ∑ j : Fin 3, (x j) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro j _
    simpa [real_inner_self_eq_norm_sq] using rfl
  have h2 : (x i) ^ 2 ≤ ∑ j : Fin 3, (x j) ^ 2 := by
    exact Finset.single_le_sum
      (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
  have h4 : |x i| ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [sq_abs, h_norm2]
    exact h2
  nlinarith [abs_nonneg (x i), norm_nonneg x]

/-- A finite bounding set for all grid cells meeting a Euclidean ball. -/
lemma grid3_finset
    (n : ℕ) {R h : ℝ} (hR : 0 ≤ R) (hh : 0 < h)
    (hn : R / h ≤ (n : ℝ)) :
    ∃ S : Finset Grid3,
      (∀ p : Point3, ‖p‖ ≤ R → grid3 h p ∈ S) ∧
      S.card = (2 * n + 1) ^ 3 := by
  let I : Finset ℤ := Finset.Icc (-(n : ℤ)) (n : ℤ)
  let S : Finset Grid3 := I ×ˢ (I ×ˢ I)
  have h1 : ∀ p : Point3, ‖p‖ ≤ R → grid3 h p ∈ S := by
    intro p hp
    have hcoord : ∀ i : Fin 3, Int.floor (p i / h) ∈ I := by
      intro i
      have habs : |p i| ≤ R := (factor2_coord_le_norm p i).trans hp
      have h3 : -R ≤ p i := (abs_le.mp habs).1
      have h4 : p i ≤ R := (abs_le.mp habs).2
      have hlower : (-(n : ℤ)) ≤ Int.floor (p i / h) := by
        apply Int.le_floor.mpr
        have hdiv : -(n : ℝ) ≤ p i / h := by
          have hA : -R / h ≤ p i / h := by gcongr
          have hB : -(n : ℝ) ≤ -R / h := by
            have := hn
            rw [show -R / h = -(R / h) by ring]
            linarith
          linarith
        simpa using hdiv
      have hupper : Int.floor (p i / h) ≤ (n : ℤ) := by
        apply (Int.floor_le_iff (a := p i / h) (z := (n : ℤ))).mpr
        have hdiv : p i / h ≤ (n : ℝ) := by
          have : p i / h ≤ R / h := by gcongr
          linarith
        have hcast : ((n : ℤ) : ℝ) = (n : ℝ) := by simp
        rw [hcast]
        linarith
      exact Finset.mem_Icc.mpr ⟨hlower, hupper⟩
    exact Finset.mem_product.mpr
      ⟨hcoord 0, Finset.mem_product.mpr ⟨hcoord 1, hcoord 2⟩⟩
  have h2 : S.card = (2 * n + 1) ^ 3 := by
    have hI : I.card = 2 * n + 1 := by
      simp [I, int_interval_card] <;> omega
    have h_card1 : S.card = I.card * (I ×ˢ I).card := by
      have hS : S = I ×ˢ (I ×ˢ I) := by rfl
      rw [hS]
      exact Finset.card_product I (I ×ˢ I)
    have h_card2 : (I ×ˢ I).card = I.card * I.card :=
      Finset.card_product I I
    rw [h_card1, h_card2, hI]
    simp [pow_succ]
    ring
  exact ⟨S, h1, h2⟩

private lemma inner_add_formula_factor2
    {x y : Point3} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    inner ℝ x y = (‖x + y‖ ^ 2 - 2) / 2 := by
  have h :
      ‖x + y‖ ^ 2 =
        ‖x‖ ^ 2 + 2 * inner ℝ x y + ‖y‖ ^ 2 :=
    norm_add_sq_real x y
  rw [h, hx, hy]
  ring

private lemma inner_sub_formula_factor2
    {x y : Point3} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    inner ℝ x y = 1 - ‖x - y‖ ^ 2 / 2 := by
  have h :
      ‖x - y‖ ^ 2 =
        ‖x‖ ^ 2 - 2 * inner ℝ x y + ‖y‖ ^ 2 :=
    norm_sub_sq_real x y
  rw [h, hx, hy]
  ring

private lemma local_six_grid_card_bound
    {sigma : ℝ} (hsigma : 0 < sigma) (hsigma_small : sigma ≤ 1 / 8)
    {F : Kakeya.Streamlined.TubeFamily sigma}
    (hF_distinct : F.IsEssentiallyDistinct)
    (indices : Finset (Fin F.card))
    (orientationCells : Finset Bool)
    (orientation : Fin F.card → Bool)
    (horientation : ∀ i ∈ indices, orientation i ∈ orientationCells)
    (baseOffset dirOffset : Fin F.card → Point3)
    (baseRadius dirRadius : ℝ)
    (hbaseRadius : 0 ≤ baseRadius) (hdirRadius : 0 ≤ dirRadius)
    (hbase_bound : ∀ i ∈ indices, ‖baseOffset i‖ ≤ baseRadius)
    (hdir_bound : ∀ i ∈ indices, ‖dirOffset i‖ ≤ dirRadius)
    (hbase_recover : ∀ i k,
      orientation i = orientation k →
        baseOffset i - baseOffset k =
          (F.tube i).base - (F.tube k).base)
    (hdir_recover : ∀ i k,
      orientation i = orientation k →
        dirOffset i - dirOffset k =
          (F.tube i).direction - (F.tube k).direction) :
    indices.card ≤
      orientationCells.card *
        (2 * Nat.ceil (baseRadius / (sigma / 32)) + 1) ^ 3 *
        (2 * Nat.ceil (dirRadius / (sigma / 32)) + 1) ^ 3 := by
  classical
  let mesh : ℝ := sigma / 32
  have hmesh : 0 < mesh := by positivity
  have hsqrt : Real.sqrt 3 * mesh < sigma / 16 := by
    have hroot : Real.sqrt 3 < 2 := by
      have h8 : Real.sqrt 3 < Real.sqrt 4 :=
        Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      have h9 : Real.sqrt 4 = 2 := by
        rw [Real.sqrt_eq_cases] <;> norm_num
      rw [h9] at h8
      exact h8
    dsimp only [mesh]
    nlinarith
  let nBase : ℕ := Nat.ceil (baseRadius / mesh)
  let nDir : ℕ := Nat.ceil (dirRadius / mesh)
  have hnBase : baseRadius / mesh ≤ (nBase : ℝ) := by
    exact Nat.le_ceil _
  have hnDir : dirRadius / mesh ≤ (nDir : ℝ) := by
    exact Nat.le_ceil _
  rcases grid3_finset nBase hbaseRadius hmesh hnBase with
    ⟨baseCells, hbaseCells, hbaseCard⟩
  rcases grid3_finset nDir hdirRadius hmesh hnDir with
    ⟨dirCells, hdirCells, hdirCard⟩
  let cellRange : Finset (Bool × Grid3 × Grid3) :=
    orientationCells ×ˢ baseCells ×ˢ dirCells
  let cell (i : Fin F.card) : Bool × Grid3 × Grid3 :=
    (orientation i, grid3 mesh (baseOffset i), grid3 mesh (dirOffset i))
  have hcell_mem : ∀ i ∈ indices, cell i ∈ cellRange := by
    intro i hi
    have h0 : (cell i).1 ∈ orientationCells :=
      horientation i hi
    have h1 : (cell i).2.1 ∈ baseCells :=
      hbaseCells (baseOffset i) (hbase_bound i hi)
    have h2 : (cell i).2.2 ∈ dirCells :=
      hdirCells (dirOffset i) (hdir_bound i hi)
    simp [cellRange, h0, h1, h2]
  have hinj : Set.InjOn cell indices := by
    intro i hi k hk hcell
    by_cases hik : i = k
    · exact hik
    · have horient : orientation i = orientation k := by
        exact congr_arg Prod.fst hcell
      have hbaseCell :
          grid3 mesh (baseOffset i) = grid3 mesh (baseOffset k) := by
        exact congr_arg (fun c => c.2.1) hcell
      have hdirCell :
          grid3 mesh (dirOffset i) = grid3 mesh (dirOffset k) := by
        exact congr_arg (fun c => c.2.2) hcell
      have hbaseClose :
          ‖(F.tube i).base - (F.tube k).base‖ < sigma / 16 := by
        rw [← hbase_recover i k horient]
        exact (grid3_close hmesh hbaseCell).trans hsqrt
      have hdirClose :
          ‖(F.tube i).direction - (F.tube k).direction‖ < sigma / 16 := by
        rw [← hdir_recover i k horient]
        exact (grid3_close hmesh hdirCell).trans hsqrt
      have hnot :
          ¬(F.tube i).EssentiallyDistinct (F.tube k) :=
        close_tubes_not_ed_general
          hsigma hsigma_small hbaseClose.le hdirClose.le
      exact False.elim (hnot (hF_distinct i k hik))
  have himageCard : (indices.image cell).card = indices.card := by
    rw [Finset.card_image_of_injOn hinj]
  have himage : indices.image cell ⊆ cellRange := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    exact hcell_mem i hi
  have hcard : indices.card ≤ cellRange.card := by
    rw [← himageCard]
    exact Finset.card_le_card himage
  have hrange :
      cellRange.card =
        orientationCells.card *
          (2 * nBase + 1) ^ 3 * (2 * nDir + 1) ^ 3 := by
    simp [cellRange, hbaseCard, hdirCard,
      Finset.card_product]
    ring
  rw [hrange] at hcard
  simpa [mesh, nBase, nDir] using hcard

private lemma nested_tube_parameter_bounds
    {delta sigma rho : ℝ}
    (hdelta : 0 ≤ delta) (hsigma : 0 < sigma) (hrho : 0 < rho)
    (D : Kakeya.DeltaTube delta)
    (T : Kakeya.DeltaTube sigma)
    (parent : Kakeya.DeltaTube rho)
    (hDT : D.carrier ⊆ T.carrier)
    (hDP : D.carrier ⊆ parent.carrier) :
    (‖T.direction - parent.direction‖ ≤ 4 * sigma + 4 * rho ∧
      ‖T.base - parent.base‖ ≤ 3 * sigma + 3 * rho) ∨
    (‖T.direction + parent.direction‖ ≤ 4 * sigma + 4 * rho ∧
      ‖T.base - (parent.base + parent.direction)‖ ≤
        3 * sigma + 7 * rho) := by
  rcases containment_alignment_bound hdelta hsigma D T hDT with
    hTpar | hTanti
  · rcases containment_alignment_bound hdelta hrho D parent hDP with
      hPpar | hPanti
    · have hdir :
          ‖T.direction - parent.direction‖ ≤ 4 * sigma + 4 * rho := by
        rw [show T.direction - parent.direction =
          (T.direction - D.direction) +
            (D.direction - parent.direction) by abel]
        exact (norm_add_le _ _).trans
          (by
            have hTD :
                ‖T.direction - D.direction‖ ≤ 4 * sigma := by
              simpa [norm_sub_rev] using hTpar.1
            linarith)
      have hbase :
          ‖T.base - parent.base‖ ≤ 3 * sigma + 3 * rho := by
        rw [show T.base - parent.base =
          (T.base - D.base) + (D.base - parent.base) by abel]
        exact (norm_add_le _ _).trans
          (by
            have hDPbase :
                ‖D.base - parent.base‖ ≤ 3 * rho := by
              simpa [norm_sub_rev] using hPpar.2
            linarith)
      exact Or.inl ⟨hdir, hbase⟩
    · have hdir :
          ‖T.direction + parent.direction‖ ≤ 4 * sigma + 4 * rho := by
        rw [show T.direction + parent.direction =
          (T.direction - D.direction) +
            (D.direction + parent.direction) by abel]
        exact (norm_add_le _ _).trans
          (by
            have hTD :
                ‖T.direction - D.direction‖ ≤ 4 * sigma := by
              simpa [norm_sub_rev] using hTpar.1
            linarith)
      have hbase :
          ‖T.base - (parent.base + parent.direction)‖ ≤
            3 * sigma + 7 * rho := by
        rw [show
          T.base - (parent.base + parent.direction) =
            (T.base - D.base) +
              ((D.base + D.direction) - parent.base) -
              (D.direction + parent.direction) by abel]
        have htri :
            ‖(T.base - D.base) +
                ((D.base + D.direction) - parent.base) -
                (D.direction + parent.direction)‖ ≤
              ‖T.base - D.base‖ +
                ‖(D.base + D.direction) - parent.base‖ +
                ‖D.direction + parent.direction‖ := by
          calc
            ‖(T.base - D.base) +
                ((D.base + D.direction) - parent.base) -
                (D.direction + parent.direction)‖
                ≤ ‖(T.base - D.base) +
                    ((D.base + D.direction) - parent.base)‖ +
                    ‖D.direction + parent.direction‖ :=
              norm_sub_le _ _
            _ ≤
                (‖T.base - D.base‖ +
                    ‖(D.base + D.direction) - parent.base‖) +
                  ‖D.direction + parent.direction‖ := by
              gcongr
              exact norm_add_le _ _
        have hmid :
            ‖(D.base + D.direction) - parent.base‖ ≤ 3 * rho := by
          simpa [norm_sub_rev] using hPanti.2
        linarith
      exact Or.inr ⟨hdir, hbase⟩
  · rcases containment_alignment_bound hdelta hrho D parent hDP with
      hPpar | hPanti
    · have hdir :
          ‖T.direction + parent.direction‖ ≤ 4 * sigma + 4 * rho := by
        rw [show T.direction + parent.direction =
          (T.direction + D.direction) +
            (parent.direction - D.direction) by abel]
        exact (norm_add_le _ _).trans
          (by
            have hPD :
                ‖parent.direction - D.direction‖ ≤ 4 * rho := by
              simpa [norm_sub_rev] using hPpar.1
            have hTD :
                ‖T.direction + D.direction‖ ≤ 4 * sigma := by
              simpa [add_comm] using hTanti.1
            linarith)
      have hbase :
          ‖T.base - (parent.base + parent.direction)‖ ≤
            3 * sigma + 7 * rho := by
        rw [show
          T.base - (parent.base + parent.direction) =
            (T.base - (D.base + D.direction)) +
              (D.base - parent.base) +
              (D.direction - parent.direction) by abel]
        have htri :
            ‖(T.base - (D.base + D.direction)) +
                (D.base - parent.base) +
                (D.direction - parent.direction)‖ ≤
              ‖T.base - (D.base + D.direction)‖ +
                ‖D.base - parent.base‖ +
                ‖D.direction - parent.direction‖ := by
          calc
            ‖(T.base - (D.base + D.direction)) +
                (D.base - parent.base) +
                (D.direction - parent.direction)‖
                ≤ ‖(T.base - (D.base + D.direction)) +
                    (D.base - parent.base)‖ +
                    ‖D.direction - parent.direction‖ :=
              norm_add_le _ _
            _ ≤
                (‖T.base - (D.base + D.direction)‖ +
                    ‖D.base - parent.base‖) +
                  ‖D.direction - parent.direction‖ := by
              gcongr
              exact norm_add_le _ _
        have hDb :
            ‖D.base - parent.base‖ ≤ 3 * rho := by
          simpa [norm_sub_rev] using hPpar.2
        linarith
      exact Or.inr ⟨hdir, hbase⟩
    · have hdir :
          ‖T.direction - parent.direction‖ ≤ 4 * sigma + 4 * rho := by
        rw [show T.direction - parent.direction =
          (T.direction + D.direction) -
            (D.direction + parent.direction) by abel]
        exact (norm_sub_le _ _).trans
          (by
            have hTD :
                ‖T.direction + D.direction‖ ≤ 4 * sigma := by
              simpa [add_comm] using hTanti.1
            linarith)
      have hbase :
          ‖T.base - parent.base‖ ≤ 3 * sigma + 3 * rho := by
        rw [show T.base - parent.base =
          (T.base - (D.base + D.direction)) +
            ((D.base + D.direction) - parent.base) by abel]
        exact (norm_add_le _ _).trans
          (by
            have hmid :
                ‖(D.base + D.direction) - parent.base‖ ≤ 3 * rho := by
              simpa [norm_sub_rev] using hPanti.2
            linarith)
      exact Or.inl ⟨hdir, hbase⟩

/-- On scales differing by at most a factor two, the local six-parameter
packing number is an absolute constant. -/
lemma factor2_packing_bound
    {delta sigma sigmaK : ℝ}
    (hdelta : 0 ≤ delta) (hsigma : 0 < sigma) (hsigmaK : 0 < sigmaK)
    (hsigmaK_small : sigmaK ≤ 1 / 8)
    (hfactor2 : sigmaK / 2 ≤ sigma) (hsigma_le : sigma ≤ sigmaK)
    {F : Kakeya.Streamlined.TubeFamily sigma}
    (hF_distinct : F.IsEssentiallyDistinct)
    (parent : Kakeya.DeltaTube sigmaK)
    (indices : Finset (Fin F.card))
    (h_containment : ∀ i ∈ indices,
      ∃ D : Kakeya.DeltaTube delta,
        D.carrier ⊆ (F.tube i).carrier ∧
        D.carrier ⊆ parent.carrier) :
    indices.card ≤ 2 ^ 63 := by
  classical
  let e0 : Point3 := EuclideanSpace.single 0 1
  let dummy : Kakeya.DeltaTube delta :=
    ⟨0, e0, by simp [e0, PiLp.norm_eq_of_L2]⟩
  let witness (i : Fin F.card) : Kakeya.DeltaTube delta :=
    if hi : i ∈ indices then Classical.choose (h_containment i hi) else dummy
  have hw1 : ∀ i ∈ indices,
      (witness i).carrier ⊆ (F.tube i).carrier := by
    intro i hi
    simp only [witness, dif_pos hi]
    exact (Classical.choose_spec (h_containment i hi)).1
  have hw2 : ∀ i ∈ indices,
      (witness i).carrier ⊆ parent.carrier := by
    intro i hi
    simp only [witness, dif_pos hi]
    exact (Classical.choose_spec (h_containment i hi)).2
  have hbounds : ∀ i ∈ indices,
      (‖(F.tube i).direction - parent.direction‖ ≤ 8 * sigmaK ∧
        ‖(F.tube i).base - parent.base‖ ≤ 6 * sigmaK) ∨
      (‖(F.tube i).direction + parent.direction‖ ≤ 8 * sigmaK ∧
        ‖(F.tube i).base - (parent.base + parent.direction)‖ ≤
          10 * sigmaK) := by
    intro i hi
    rcases nested_tube_parameter_bounds hdelta hsigma hsigmaK
        (witness i) (F.tube i) parent (hw1 i hi) (hw2 i hi) with
      h | h
    · exact Or.inl ⟨h.1.trans (by linarith),
        h.2.trans (by linarith)⟩
    · exact Or.inr ⟨h.1.trans (by linarith),
        h.2.trans (by linarith)⟩
  let orientation (i : Fin F.card) : Bool :=
    0 ≤ inner ℝ (F.tube i).direction parent.direction
  have hpos : ∀ i ∈ indices,
      ‖(F.tube i).direction - parent.direction‖ ≤ 8 * sigmaK →
        0 < inner ℝ (F.tube i).direction parent.direction := by
    intro i _ h
    rw [inner_sub_formula_factor2
      (F.tube i).direction_unit parent.direction_unit]
    have hsquare :
        ‖(F.tube i).direction - parent.direction‖ ^ 2 ≤
          (8 * sigmaK) ^ 2 := by gcongr
    nlinarith [hsigmaK_small]
  have hneg : ∀ i ∈ indices,
      ‖(F.tube i).direction + parent.direction‖ ≤ 8 * sigmaK →
        inner ℝ (F.tube i).direction parent.direction < 0 := by
    intro i _ h
    rw [inner_add_formula_factor2
      (F.tube i).direction_unit parent.direction_unit]
    have hsquare :
        ‖(F.tube i).direction + parent.direction‖ ^ 2 ≤
          (8 * sigmaK) ^ 2 := by gcongr
    nlinarith [hsigmaK_small]
  let baseOffset (i : Fin F.card) : Point3 :=
    if orientation i then
      (F.tube i).base - parent.base
    else
      (F.tube i).base - (parent.base + parent.direction)
  let dirOffset (i : Fin F.card) : Point3 :=
    if orientation i then
      (F.tube i).direction - parent.direction
    else
      (F.tube i).direction + parent.direction
  have hbase : ∀ i ∈ indices, ‖baseOffset i‖ ≤ 10 * sigmaK := by
    intro i hi
    by_cases hp : orientation i
    · rcases hbounds i hi with h | h
      · simpa [baseOffset, hp] using h.2.trans (by linarith)
      · have hnonneg :
            0 ≤ inner ℝ (F.tube i).direction parent.direction := by
          simpa [orientation] using hp
        exact False.elim ((not_lt_of_ge hnonneg) (hneg i hi h.1))
    · rcases hbounds i hi with h | h
      · have hnonneg :
            0 ≤ inner ℝ (F.tube i).direction parent.direction :=
          (hpos i hi h.1).le
        exact False.elim (hp (by simpa [orientation] using hnonneg))
      · simpa [baseOffset, hp] using h.2
  have hdir : ∀ i ∈ indices, ‖dirOffset i‖ ≤ 8 * sigmaK := by
    intro i hi
    by_cases hp : orientation i
    · rcases hbounds i hi with h | h
      · simpa [dirOffset, hp] using h.1
      · have hnonneg :
            0 ≤ inner ℝ (F.tube i).direction parent.direction := by
          simpa [orientation] using hp
        exact False.elim ((not_lt_of_ge hnonneg) (hneg i hi h.1))
    · rcases hbounds i hi with h | h
      · have hnonneg :
            0 ≤ inner ℝ (F.tube i).direction parent.direction :=
          (hpos i hi h.1).le
        exact False.elim (hp (by simpa [orientation] using hnonneg))
      · simpa [dirOffset, hp] using h.1
  have hbaseRecover : ∀ i k,
      orientation i = orientation k →
        baseOffset i - baseOffset k =
          (F.tube i).base - (F.tube k).base := by
    intro i k h
    by_cases hp : orientation i
    · have hk : orientation k := by rwa [← h]
      simp [baseOffset, hp, hk] <;> abel
    · have hk : ¬orientation k := by rwa [← h]
      simp [baseOffset, hp, hk] <;> abel
  have hdirRecover : ∀ i k,
      orientation i = orientation k →
        dirOffset i - dirOffset k =
          (F.tube i).direction - (F.tube k).direction := by
    intro i k h
    by_cases hp : orientation i
    · have hk : orientation k := by rwa [← h]
      simp [dirOffset, hp, hk] <;> abel
    · have hk : ¬orientation k := by rwa [← h]
      simp [dirOffset, hp, hk] <;> abel
  have hlocal := local_six_grid_card_bound
    hsigma (hsigma_le.trans hsigmaK_small) hF_distinct indices
    Finset.univ orientation (by simp) baseOffset dirOffset
    (10 * sigmaK) (8 * sigmaK)
    (by positivity) (by positivity)
    hbase hdir hbaseRecover hdirRecover
  have hbaseCeil :
      Nat.ceil ((10 * sigmaK) / (sigma / 32)) ≤ 640 := by
    apply (Nat.ceil_le).mpr
    have hratio : sigmaK / sigma ≤ 2 := by
      calc
        sigmaK / sigma ≤ sigmaK / (sigmaK / 2) := by gcongr
        _ = 2 := by field_simp [hsigmaK.ne'] <;> ring
    have heq :
        (10 * sigmaK) / (sigma / 32) =
          320 * (sigmaK / sigma) := by
      field_simp [hsigma.ne'] <;> ring
    rw [heq]
    linarith
  have hdirCeil :
      Nat.ceil ((8 * sigmaK) / (sigma / 32)) ≤ 512 := by
    apply (Nat.ceil_le).mpr
    have hratio : sigmaK / sigma ≤ 2 := by
      calc
        sigmaK / sigma ≤ sigmaK / (sigmaK / 2) := by gcongr
        _ = 2 := by field_simp [hsigmaK.ne'] <;> ring
    have heq :
        (8 * sigmaK) / (sigma / 32) =
          256 * (sigmaK / sigma) := by
      field_simp [hsigma.ne'] <;> ring
    rw [heq]
    linarith
  have hcount :
      2 *
          (2 * Nat.ceil ((10 * sigmaK) / (sigma / 32)) + 1) ^ 3 *
          (2 * Nat.ceil ((8 * sigmaK) / (sigma / 32)) + 1) ^ 3 ≤
        2 * (2 * 640 + 1) ^ 3 * (2 * 512 + 1) ^ 3 := by
    gcongr
  exact hlocal.trans (hcount.trans (by norm_num))

/-- Local six-parameter packing at arbitrary relative scales. -/
lemma general_packing_bound
    {delta rho sigma : ℝ}
    (hdelta : 0 ≤ delta) (hsigma : 0 < sigma) (hrho : 0 < rho)
    (hsigma_small : sigma ≤ 1 / 8) (hrho_le : rho ≤ 1)
    {F : Kakeya.Streamlined.TubeFamily sigma}
    (hF_distinct : F.IsEssentiallyDistinct)
    (parent : Kakeya.DeltaTube rho)
    (indices : Finset (Fin F.card))
    (h_containment : ∀ i ∈ indices,
      ∃ D : Kakeya.DeltaTube delta,
        D.carrier ⊆ (F.tube i).carrier ∧
        D.carrier ⊆ parent.carrier) :
    (indices.card : ℝ) ≤ 10 ^ 19 * ((rho / sigma) ^ 6 + 1) := by
  classical
  by_cases hempty : indices = ∅
  · rw [hempty]
    simp
    positivity
  let e0 : Point3 := EuclideanSpace.single 0 1
  let dummy : Kakeya.DeltaTube delta :=
    ⟨0, e0, by simp [e0, PiLp.norm_eq_of_L2]⟩
  let witness (i : Fin F.card) : Kakeya.DeltaTube delta :=
    if hi : i ∈ indices then Classical.choose (h_containment i hi) else dummy
  have hw1 : ∀ i ∈ indices,
      (witness i).carrier ⊆ (F.tube i).carrier := by
    intro i hi
    simp only [witness, dif_pos hi]
    exact (Classical.choose_spec (h_containment i hi)).1
  have hw2 : ∀ i ∈ indices,
      (witness i).carrier ⊆ parent.carrier := by
    intro i hi
    simp only [witness, dif_pos hi]
    exact (Classical.choose_spec (h_containment i hi)).2
  have hbounds : ∀ i ∈ indices,
      (‖(F.tube i).direction - parent.direction‖ ≤ 4 * sigma + 4 * rho ∧
        ‖(F.tube i).base - parent.base‖ ≤ 3 * sigma + 3 * rho) ∨
      (‖(F.tube i).direction + parent.direction‖ ≤ 4 * sigma + 4 * rho ∧
        ‖(F.tube i).base - (parent.base + parent.direction)‖ ≤
          3 * sigma + 7 * rho) := by
    intro i hi
    exact nested_tube_parameter_bounds hdelta hsigma hrho
      (witness i) (F.tube i) parent (hw1 i hi) (hw2 i hi)
  let ratio : ℝ := rho / sigma
  have hratio_nonneg : 0 ≤ ratio := by positivity
  by_cases hsmall : rho ≤ 1 / 8
  · have hsum_small : 4 * sigma + 4 * rho ≤ 1 := by
      linarith
    let orientation (i : Fin F.card) : Bool :=
      0 ≤ inner ℝ (F.tube i).direction parent.direction
    have hpos : ∀ i ∈ indices,
        ‖(F.tube i).direction - parent.direction‖ ≤
            4 * sigma + 4 * rho →
          0 < inner ℝ (F.tube i).direction parent.direction := by
      intro i _ h
      rw [inner_sub_formula_factor2
        (F.tube i).direction_unit parent.direction_unit]
      have hsquare :
          ‖(F.tube i).direction - parent.direction‖ ^ 2 ≤
            (4 * sigma + 4 * rho) ^ 2 := by gcongr
      nlinarith [hsum_small]
    have hneg : ∀ i ∈ indices,
        ‖(F.tube i).direction + parent.direction‖ ≤
            4 * sigma + 4 * rho →
          inner ℝ (F.tube i).direction parent.direction < 0 := by
      intro i _ h
      rw [inner_add_formula_factor2
        (F.tube i).direction_unit parent.direction_unit]
      have hsquare :
          ‖(F.tube i).direction + parent.direction‖ ^ 2 ≤
            (4 * sigma + 4 * rho) ^ 2 := by gcongr
      nlinarith [hsum_small]
    let baseOffset (i : Fin F.card) : Point3 :=
      if orientation i then
        (F.tube i).base - parent.base
      else
        (F.tube i).base - (parent.base + parent.direction)
    let dirOffset (i : Fin F.card) : Point3 :=
      if orientation i then
        (F.tube i).direction - parent.direction
      else
        (F.tube i).direction + parent.direction
    have hbase : ∀ i ∈ indices,
        ‖baseOffset i‖ ≤ 10 * (sigma + rho) := by
      intro i hi
      by_cases hp : orientation i
      · rcases hbounds i hi with h | h
        · simpa [baseOffset, hp] using
            h.2.trans (by nlinarith [hsigma.le, hrho.le])
        · have hnonneg :
              0 ≤ inner ℝ (F.tube i).direction parent.direction := by
            simpa [orientation] using hp
          exact False.elim ((not_lt_of_ge hnonneg) (hneg i hi h.1))
      · rcases hbounds i hi with h | h
        · have hnonneg :
              0 ≤ inner ℝ (F.tube i).direction parent.direction :=
            (hpos i hi h.1).le
          exact False.elim (hp (by simpa [orientation] using hnonneg))
        · simpa [baseOffset, hp] using
            h.2.trans (by nlinarith [hsigma.le, hrho.le])
    have hdir : ∀ i ∈ indices,
        ‖dirOffset i‖ ≤ 4 * (sigma + rho) := by
      intro i hi
      by_cases hp : orientation i
      · rcases hbounds i hi with h | h
        · have h' :
              ‖(F.tube i).direction - parent.direction‖ ≤
                4 * (sigma + rho) := by
            rw [show 4 * (sigma + rho) = 4 * sigma + 4 * rho by ring]
            exact h.1
          simpa [dirOffset, hp] using h'
        · have hnonneg :
              0 ≤ inner ℝ (F.tube i).direction parent.direction := by
            simpa [orientation] using hp
          exact False.elim ((not_lt_of_ge hnonneg) (hneg i hi h.1))
      · rcases hbounds i hi with h | h
        · have hnonneg :
              0 ≤ inner ℝ (F.tube i).direction parent.direction :=
            (hpos i hi h.1).le
          exact False.elim (hp (by simpa [orientation] using hnonneg))
        · have h' :
              ‖(F.tube i).direction + parent.direction‖ ≤
                4 * (sigma + rho) := by
            rw [show 4 * (sigma + rho) = 4 * sigma + 4 * rho by ring]
            exact h.1
          simpa [dirOffset, hp] using h'
    have hbaseRecover : ∀ i k,
        orientation i = orientation k →
          baseOffset i - baseOffset k =
            (F.tube i).base - (F.tube k).base := by
      intro i k h
      by_cases hp : orientation i
      · have hk : orientation k := by rwa [← h]
        simp [baseOffset, hp, hk] <;> abel
      · have hk : ¬orientation k := by rwa [← h]
        simp [baseOffset, hp, hk] <;> abel
    have hdirRecover : ∀ i k,
        orientation i = orientation k →
          dirOffset i - dirOffset k =
            (F.tube i).direction - (F.tube k).direction := by
      intro i k h
      by_cases hp : orientation i
      · have hk : orientation k := by rwa [← h]
        simp [dirOffset, hp, hk] <;> abel
      · have hk : ¬orientation k := by rwa [← h]
        simp [dirOffset, hp, hk] <;> abel
    have hlocal := local_six_grid_card_bound
      hsigma hsigma_small hF_distinct indices
      Finset.univ orientation (by simp) baseOffset dirOffset
      (10 * (sigma + rho)) (4 * (sigma + rho))
      (by positivity) (by positivity)
      hbase hdir hbaseRecover hdirRecover
    let nBase : ℕ := Nat.ceil (320 * (1 + ratio))
    let nDir : ℕ := Nat.ceil (128 * (1 + ratio))
    have hbaseCeil :
        Nat.ceil ((10 * (sigma + rho)) / (sigma / 32)) ≤ nBase := by
      apply (Nat.ceil_mono)
      have heq :
          (10 * (sigma + rho)) / (sigma / 32) =
            320 * (1 + ratio) := by
        dsimp only [ratio]
        field_simp [hsigma.ne'] <;> ring
      rw [heq]
    have hdirCeil :
        Nat.ceil ((4 * (sigma + rho)) / (sigma / 32)) ≤ nDir := by
      apply (Nat.ceil_mono)
      have heq :
          (4 * (sigma + rho)) / (sigma / 32) =
            128 * (1 + ratio) := by
        dsimp only [ratio]
        field_simp [hsigma.ne'] <;> ring
      rw [heq]
    have hcount :
        indices.card ≤
          2 * (2 * nBase + 1) ^ 3 * (2 * nDir + 1) ^ 3 := by
      have hlocal' :
          indices.card ≤
            2 *
              (2 * Nat.ceil
                ((10 * (sigma + rho)) / (sigma / 32)) + 1) ^ 3 *
              (2 * Nat.ceil
                ((4 * (sigma + rho)) / (sigma / 32)) + 1) ^ 3 := by
        simpa using hlocal
      exact hlocal'.trans (by gcongr)
    have hnBase :
        (nBase : ℝ) ≤ 320 * (1 + ratio) + 1 := by
      exact (Nat.ceil_lt_add_one (by positivity)).le
    have hnDir :
        (nDir : ℝ) ≤ 128 * (1 + ratio) + 1 := by
      exact (Nat.ceil_lt_add_one (by positivity)).le
    have hbaseReal :
        ((2 * nBase + 1 : ℕ) : ℝ) ≤ 643 * (1 + ratio) := by
      have hcast :
          ((2 * nBase + 1 : ℕ) : ℝ) = 2 * (nBase : ℝ) + 1 := by
        norm_num
      rw [hcast]
      nlinarith [hratio_nonneg]
    have hdirReal :
        ((2 * nDir + 1 : ℕ) : ℝ) ≤ 259 * (1 + ratio) := by
      have hcast :
          ((2 * nDir + 1 : ℕ) : ℝ) = 2 * (nDir : ℝ) + 1 := by
        norm_num
      rw [hcast]
      nlinarith [hratio_nonneg]
    have hcardReal :
        (indices.card : ℝ) ≤
          2 * (643 * (1 + ratio)) ^ 3 *
            (259 * (1 + ratio)) ^ 3 := by
      have hcast : (indices.card : ℝ) ≤
          (2 * (2 * nBase + 1) ^ 3 * (2 * nDir + 1) ^ 3 : ℕ) := by
        exact_mod_cast hcount
      calc
        (indices.card : ℝ)
            ≤ (2 * (2 * nBase + 1) ^ 3 *
                (2 * nDir + 1) ^ 3 : ℕ) := hcast
        _ ≤ 2 * (643 * (1 + ratio)) ^ 3 *
              (259 * (1 + ratio)) ^ 3 := by
          have hbasePow :
              (((2 * nBase + 1 : ℕ) : ℝ) ^ 3) ≤
                (643 * (1 + ratio)) ^ 3 := by
            gcongr
          have hdirPow :
              (((2 * nDir + 1 : ℕ) : ℝ) ^ 3) ≤
                (259 * (1 + ratio)) ^ 3 := by
            gcongr
          norm_num
          have hdirNonneg :
              0 ≤ (((2 * nDir + 1 : ℕ) : ℝ) ^ 3) := by positivity
          have hbaseTargetNonneg :
              0 ≤ (643 * (1 + ratio)) ^ 3 := by positivity
          have hbaseCast :
              (((2 * nBase + 1 : ℕ) : ℝ) ^ 3) =
                (2 * (nBase : ℝ) + 1) ^ 3 := by norm_num
          have hdirCast :
              (((2 * nDir + 1 : ℕ) : ℝ) ^ 3) =
                (2 * (nDir : ℝ) + 1) ^ 3 := by norm_num
          rw [← hbaseCast, ← hdirCast]
          calc
            2 * (((2 * nBase + 1 : ℕ) : ℝ) ^ 3) *
                  (((2 * nDir + 1 : ℕ) : ℝ) ^ 3)
                ≤
              2 * (643 * (1 + ratio)) ^ 3 *
                  (((2 * nDir + 1 : ℕ) : ℝ) ^ 3) := by
                gcongr
            _ ≤ 2 * (643 * (1 + ratio)) ^ 3 *
                  (259 * (1 + ratio)) ^ 3 := by
                gcongr
    have hpoly :
        (1 + ratio) ^ 6 ≤ 64 * (ratio ^ 6 + 1) := by
      by_cases hratio : ratio ≤ 1
      · have h : (1 + ratio) ^ 6 ≤ (2 : ℝ) ^ 6 := by gcongr <;> linarith
        nlinarith [sq_nonneg (ratio ^ 3)]
      · have h : (1 + ratio) ^ 6 ≤ (2 * ratio) ^ 6 := by
          gcongr <;> linarith
        nlinarith [sq_nonneg (ratio ^ 3)]
    have hconstant :
        2 * (643 * (1 + ratio)) ^ 3 *
            (259 * (1 + ratio)) ^ 3 ≤
          10 ^ 19 * (ratio ^ 6 + 1) := by
      have hnum :
          (2 * (643 : ℝ) ^ 3 * (259 : ℝ) ^ 3) * 64 ≤ 10 ^ 19 := by
        norm_num
      have hexpand :
          2 * (643 * (1 + ratio)) ^ 3 *
              (259 * (1 + ratio)) ^ 3 =
            (2 * (643 : ℝ) ^ 3 * (259 : ℝ) ^ 3) *
              (1 + ratio) ^ 6 := by ring
      rw [hexpand]
      have hnonneg : 0 ≤ ratio ^ 6 + 1 := by positivity
      calc
        (2 * (643 : ℝ) ^ 3 * (259 : ℝ) ^ 3) *
              (1 + ratio) ^ 6
            ≤ (2 * (643 : ℝ) ^ 3 * (259 : ℝ) ^ 3) *
                (64 * (ratio ^ 6 + 1)) := by gcongr
        _ ≤ 10 ^ 19 * (ratio ^ 6 + 1) := by
          nlinarith
    simpa [ratio] using hcardReal.trans (hconstant)
  · have hrho_large : 1 / 8 < rho := by linarith
    have hsigma_lt_rho : sigma < rho := by linarith
    have hratio_gt : 1 < ratio := by
      dsimp only [ratio]
      exact (one_lt_div hsigma).mpr hsigma_lt_rho
    let orientation (_i : Fin F.card) : Bool := false
    let baseOffset (i : Fin F.card) : Point3 :=
      (F.tube i).base - parent.base
    let dirOffset (i : Fin F.card) : Point3 :=
      (F.tube i).direction - parent.direction
    have hbase : ∀ i ∈ indices, ‖baseOffset i‖ ≤ 18 * rho := by
      intro i hi
      rcases hbounds i hi with h | h
      · dsimp only [baseOffset]
        nlinarith
      · have htri :
            ‖(F.tube i).base - parent.base‖ ≤
              ‖(F.tube i).base - (parent.base + parent.direction)‖ +
                ‖parent.direction‖ := by
          rw [show (F.tube i).base - parent.base =
            ((F.tube i).base - (parent.base + parent.direction)) +
              parent.direction by abel]
          exact norm_add_le _ _
        rw [parent.direction_unit] at htri
        dsimp only [baseOffset]
        linarith
    have hdir : ∀ i ∈ indices, ‖dirOffset i‖ ≤ 24 * rho := by
      intro i hi
      rcases hbounds i hi with h | h
      · dsimp only [dirOffset]
        nlinarith
      · have htri :
            ‖(F.tube i).direction - parent.direction‖ ≤
              ‖(F.tube i).direction + parent.direction‖ + 2 := by
          rw [show (F.tube i).direction - parent.direction =
            (F.tube i).direction + parent.direction -
              (2 : ℝ) • parent.direction by
                ext j
                simp [smul_eq_mul]
                ring]
          have hnorm : ‖(2 : ℝ) • parent.direction‖ = 2 := by
            rw [norm_smul, parent.direction_unit]
            norm_num
          exact (norm_sub_le _ _).trans (by rw [hnorm])
        dsimp only [dirOffset]
        linarith
    have hbaseRecover : ∀ i k,
        orientation i = orientation k →
          baseOffset i - baseOffset k =
            (F.tube i).base - (F.tube k).base := by
      intro i k _
      simp [baseOffset]
    have hdirRecover : ∀ i k,
        orientation i = orientation k →
          dirOffset i - dirOffset k =
            (F.tube i).direction - (F.tube k).direction := by
      intro i k _
      simp [dirOffset]
    let singletonOrientation : Finset Bool := {false}
    have hlocal := local_six_grid_card_bound
      hsigma hsigma_small hF_distinct indices
      singletonOrientation orientation (by simp [singletonOrientation, orientation])
      baseOffset dirOffset
      (18 * rho) (24 * rho)
      (by positivity) (by positivity)
      hbase hdir hbaseRecover hdirRecover
    let nBase : ℕ := Nat.ceil (576 * ratio)
    let nDir : ℕ := Nat.ceil (768 * ratio)
    have hbaseCeil :
        Nat.ceil ((18 * rho) / (sigma / 32)) ≤ nBase := by
      apply Nat.ceil_mono
      have heq :
          (18 * rho) / (sigma / 32) = 576 * ratio := by
        dsimp only [ratio]
        field_simp [hsigma.ne'] <;> ring
      rw [heq]
    have hdirCeil :
        Nat.ceil ((24 * rho) / (sigma / 32)) ≤ nDir := by
      apply Nat.ceil_mono
      have heq :
          (24 * rho) / (sigma / 32) = 768 * ratio := by
        dsimp only [ratio]
        field_simp [hsigma.ne'] <;> ring
      rw [heq]
    have hcount :
        indices.card ≤
          (2 * nBase + 1) ^ 3 * (2 * nDir + 1) ^ 3 := by
      have hlocal' :
          indices.card ≤
            (2 * Nat.ceil ((18 * rho) / (sigma / 32)) + 1) ^ 3 *
              (2 * Nat.ceil ((24 * rho) / (sigma / 32)) + 1) ^ 3 := by
        simpa [singletonOrientation] using hlocal
      exact hlocal'.trans (by gcongr)
    have hnBase :
        (nBase : ℝ) ≤ 576 * ratio + 1 :=
      (Nat.ceil_lt_add_one (by positivity)).le
    have hnDir :
        (nDir : ℝ) ≤ 768 * ratio + 1 :=
      (Nat.ceil_lt_add_one (by positivity)).le
    have hbaseReal :
        ((2 * nBase + 1 : ℕ) : ℝ) ≤ 1155 * ratio := by
      have hcast :
          ((2 * nBase + 1 : ℕ) : ℝ) = 2 * (nBase : ℝ) + 1 := by
        norm_num
      rw [hcast]
      nlinarith
    have hdirReal :
        ((2 * nDir + 1 : ℕ) : ℝ) ≤ 1539 * ratio := by
      have hcast :
          ((2 * nDir + 1 : ℕ) : ℝ) = 2 * (nDir : ℝ) + 1 := by
        norm_num
      rw [hcast]
      nlinarith
    have hcardReal :
        (indices.card : ℝ) ≤
          (1155 * ratio) ^ 3 * (1539 * ratio) ^ 3 := by
      have hcast : (indices.card : ℝ) ≤
          ((2 * nBase + 1) ^ 3 * (2 * nDir + 1) ^ 3 : ℕ) := by
        exact_mod_cast hcount
      calc
        (indices.card : ℝ)
            ≤ ((2 * nBase + 1) ^ 3 *
                (2 * nDir + 1) ^ 3 : ℕ) := hcast
        _ ≤ (1155 * ratio) ^ 3 * (1539 * ratio) ^ 3 := by
          have hbasePow :
              (((2 * nBase + 1 : ℕ) : ℝ) ^ 3) ≤
                (1155 * ratio) ^ 3 := by
            gcongr
          have hdirPow :
              (((2 * nDir + 1 : ℕ) : ℝ) ^ 3) ≤
                (1539 * ratio) ^ 3 := by
            gcongr
          norm_num
          have hdirNonneg :
              0 ≤ (((2 * nDir + 1 : ℕ) : ℝ) ^ 3) := by positivity
          have hbaseTargetNonneg : 0 ≤ (1155 * ratio) ^ 3 := by
            positivity
          have hbaseCast :
              (((2 * nBase + 1 : ℕ) : ℝ) ^ 3) =
                (2 * (nBase : ℝ) + 1) ^ 3 := by norm_num
          have hdirCast :
              (((2 * nDir + 1 : ℕ) : ℝ) ^ 3) =
                (2 * (nDir : ℝ) + 1) ^ 3 := by norm_num
          rw [← hbaseCast, ← hdirCast]
          calc
            (((2 * nBase + 1 : ℕ) : ℝ) ^ 3) *
                  (((2 * nDir + 1 : ℕ) : ℝ) ^ 3)
                ≤
              (1155 * ratio) ^ 3 *
                  (((2 * nDir + 1 : ℕ) : ℝ) ^ 3) := by
                gcongr
            _ ≤ (1155 * ratio) ^ 3 * (1539 * ratio) ^ 3 := by
                gcongr
    have hconstant :
        (1155 * ratio) ^ 3 * (1539 * ratio) ^ 3 ≤
          10 ^ 19 * (ratio ^ 6 + 1) := by
      have hnum : (1155 ^ 3 * 1539 ^ 3 : ℝ) ≤ 10 ^ 19 := by
        norm_num
      have hexpand :
          (1155 * ratio) ^ 3 * (1539 * ratio) ^ 3 =
            (1155 ^ 3 * 1539 ^ 3 : ℝ) * ratio ^ 6 := by ring
      rw [hexpand]
      nlinarith [sq_nonneg (ratio ^ 3)]
    simpa [ratio] using hcardReal.trans hconstant

end Kakeya.Assouad
