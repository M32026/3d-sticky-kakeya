import MyLeanRepo.Kakeya.CV.HausdorffMeasureSphere.Regions

local notation "graphMap" => Kakeya.CV.northSphereGraphMap


open MeasureTheory Metric Set Filter
open scoped ENNReal

namespace Kakeya.CV

noncomputable section

-- ======================================================================
-- Finiteness
-- ======================================================================

/-- Helper: if a^2 ≥ b^2 and a, b ≥ 0, then a ≥ b. -/
lemma abs_ge_from_sq_ge (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a^2 ≥ b^2) : a ≥ b := by
  by_contra h'
  have h'' : a < b := by linarith
  have h3 : a^2 < b^2 := by nlinarith
  linarith

/-- Finiteness of μHE[2] on the sphere via 6 graph regions. -/
lemma muHE_two_sphere_finite :
    (μHE[2] : Measure (Point 3)) (unitSphere 3) < ⊤ := by
  let ρ : ℝ := Real.sqrt (2 / 3)
  have hρ2 : ρ^2 = 2 / 3 := by rw [Real.sq_sqrt] <;> norm_num
  have hρ_pos : 0 ≤ ρ := by positivity
  have hρ1 : ρ < 1 := by nlinarith
  have hK_pos : 0 ≤ 1 / Real.sqrt (1 - ρ^2) := by
    have h : 0 < 1 - ρ^2 := by nlinarith
    have h2 : 0 < Real.sqrt (1 - ρ^2) := Real.sqrt_pos.mpr h
    positivity
  let K : NNReal := ⟨1 / Real.sqrt (1 - ρ^2), hK_pos⟩
  let disk : Set (Point 2) := closedBall 0 ρ
  let thr : ℝ := 1 / Real.sqrt 3
  have h_thr_pos : 0 < thr := by positivity
  have h_thr2 : thr^2 = 1 / 3 := by
    simp [thr] <;> field_simp <;> norm_num
  let A : Fin 3 → Bool → Set (Point 3) := fun i pos => sphereRegion i pos thr
  -- A 0 true ⊆ graphMap '' disk
  have hA0p_sub : A 0 true ⊆ graphMap '' disk := by
    intro p hp
    have h_sphere : p ∈ unitSphere 3 := hp.1
    have h_p0 : p 0 ≥ thr := by simpa [A, sphereRegion] using hp.2
    have h_p0_pos : 0 < p 0 := by linarith [h_thr_pos]
    set y := p 1 with hy
    set z := p 2 with hz
    have h_norm2 : (p 0)^2 + y^2 + z^2 = 1 := by
      have h := norm_sq_point3 p
      have h' : ‖p‖ = 1 := by simpa [unitSphere, Metric.mem_sphere, dist_zero_right] using h_sphere
      rw [h'] at h <;> linarith
    have h_p02 : (p 0)^2 ≥ thr^2 := by gcongr
    have h_yz : y^2 + z^2 ≤ ρ^2 := by
      nlinarith [hρ2, h_thr2, h_norm2, h_p02]
    let f2 : Fin 2 → ℝ := fun i => if i = 0 then y else z
    let q : Point 2 := mkPoint2 f2
    have hq0 : q 0 = y := by rw [mkPoint2_apply]; simp [f2]
    have hq1 : q 1 = z := by rw [mkPoint2_apply]; simp [f2]
    have hq_norm2 : ‖q‖^2 = y^2 + z^2 := by
      rw [norm_sq_point2, hq0, hq1] <;> ring
    have hq_norm : ‖q‖ ≤ ρ := by
      nlinarith [h_yz, hq_norm2, hρ_pos]
    have hq_in : q ∈ disk := by
      simpa [disk, dist_zero_right] using hq_norm
    have h1 : graphMap q 0 = p 0 := by
      rw [graphMap_apply0, hq0, hq1]
      have h_sq : 1 - y^2 - z^2 = (p 0)^2 := by linarith [h_norm2]
      rw [h_sq, Real.sqrt_sq_eq_abs, abs_of_nonneg h_p0_pos.le]
    have h2 : graphMap q 1 = p 1 := by rw [graphMap_apply1, hq0]
    have h3 : graphMap q 2 = p 2 := by rw [graphMap_apply2, hq1]
    have h_eq : graphMap q = p := by
      ext i; fin_cases i <;> tauto
    exact ⟨q, hq_in, h_eq⟩
  -- μHE[2](A 0 true) < ∞
  have h_disk_eq : disk = {q : Point 2 | (q 0)^2 + (q 1)^2 ≤ ρ^2} := by
    ext q
    have h2 : ‖q‖^2 = (q 0)^2 + (q 1)^2 := norm_sq_point2 q
    have h3 : 0 ≤ ‖q‖ := by positivity
    have h4 : dist q 0 = ‖q‖ := by
      rw [dist_eq_norm, sub_zero]
    simp only [disk, closedBall, h4, Set.mem_setOf_eq]
    constructor
    · intro h
      have h5 : ‖q‖^2 ≤ ρ^2 := by gcongr
      rw [h2] at h5
      exact h5
    · intro h
      have h5 : ‖q‖^2 ≤ ρ^2 := by
        rw [h2] <;> exact h
      have h6 : ‖q‖ ≤ ρ := by
        nlinarith [hρ_pos, h3]
      exact h6
  have h_lip : LipschitzOnWith K graphMap disk := by
    rw [h_disk_eq]
    exact graphMap_lipschitzOnWith hρ_pos hρ1
  have h_bound : (μHE[2] : Measure (Point 3)) (graphMap '' disk) ≤
      (K : ENNReal)^2 * (μHE[2] : Measure (Point 2)) disk :=
    lipschitzOnWith_muHE2_image_le h_lip
  have h_vol : (μHE[2] : Measure (Point 2)) disk = ENNReal.ofReal (Real.pi * ρ^2) := by
    rw [EuclideanSpace.euclideanHausdorffMeasure_eq_volume 2]
    rw [EuclideanSpace.volume_closedBall_fin_two 0 ρ]
    have h_nonneg1 : 0 ≤ ρ^2 := by positivity
    have h : ENNReal.ofReal ρ ^ 2 * ENNReal.ofReal Real.pi = ENNReal.ofReal (Real.pi * ρ^2) := by
      calc
        ENNReal.ofReal ρ ^ 2 * ENNReal.ofReal Real.pi
          = ENNReal.ofReal (ρ^2) * ENNReal.ofReal Real.pi := by
            rw [ENNReal.ofReal_pow hρ_pos]
        _ = ENNReal.ofReal (ρ^2 * Real.pi) := by
            rw [← ENNReal.ofReal_mul h_nonneg1] <;> ring
        _ = ENNReal.ofReal (Real.pi * ρ^2) := by ring_nf
    exact h
  have hK2 : (K : ENNReal)^2 = 3 := by
    have h1 : (K : ℝ) = 1 / Real.sqrt (1 - ρ^2) := by rfl
    have h2 : 1 - ρ^2 = 1 / 3 := by linarith [hρ2]
    have h3 : (K : ℝ)^2 = 3 := by
      rw [h1, h2]
      have h4 : Real.sqrt (1 / 3 : ℝ) = 1 / Real.sqrt 3 := by
        rw [Real.sqrt_div (by norm_num)] <;> norm_num
      rw [h4]
      field_simp
      <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    exact_mod_cast h3
  have h_finite : (μHE[2] : Measure (Point 3)) (A 0 true) < ⊤ := by
    have h1 : (μHE[2] : Measure (Point 3)) (A 0 true) ≤ (μHE[2] : Measure (Point 3)) (graphMap '' disk) :=
      measure_mono hA0p_sub
    have h4 : (K : ENNReal)^2 * (μHE[2] : Measure (Point 2)) disk = (3 : ENNReal) * ENNReal.ofReal (Real.pi * ρ^2) := by
      rw [hK2, h_vol]
    have h2 : (μHE[2] : Measure (Point 3)) (graphMap '' disk) < ⊤ := by
      calc
        (μHE[2] : Measure (Point 3)) (graphMap '' disk)
          ≤ (K : ENNReal)^2 * (μHE[2] : Measure (Point 2)) disk := h_bound
        _ = (3 : ENNReal) * ENNReal.ofReal (Real.pi * ρ^2) := h4
        _ < ⊤ := ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top
    exact lt_of_le_of_lt h1 h2
  -- All 6 regions finite by symmetry
  have h_main : ∀ (i : Fin 3) (pos : Bool), (μHE[2] : Measure (Point 3)) (A i pos) < ⊤ :=
    fun i pos => sphereRegion_finite i pos thr h_finite
  -- Covering
  let idx : Type := Fin 3 × Bool
  let S : idx → Set (Point 3) := fun p => A p.1 p.2
  have h_cover : unitSphere 3 ⊆ ⋃ p : idx, S p := by
    intro p hp
    have h_sum : (p 0)^2 + (p 1)^2 + (p 2)^2 = 1 := by
      have h := norm_sq_point3 p
      have h' : ‖p‖ = 1 := by simpa [unitSphere, Metric.mem_sphere, dist_zero_right] using hp
      rw [h'] at h <;> linarith
    have h_exists : ∃ (i : Fin 3), (p i)^2 ≥ 1 / 3 := by
      by_contra h
      push Not at h
      have h0 := h 0
      have h1 := h 1
      have h2 := h 2
      linarith
    rcases h_exists with ⟨i, hi⟩
    have h3 : (|p i|)^2 ≥ thr^2 := by
      have h4 : (|p i|)^2 = (p i)^2 := by simp
      rw [h4]; linarith [h_thr2]
    have h5 : |p i| ≥ thr :=
      abs_ge_from_sq_ge (|p i|) thr (by positivity) (by positivity) h3
    by_cases h7 : 0 ≤ p i
    · have h8 : p i ≥ thr := by
        have h9 : |p i| = p i := abs_of_nonneg h7
        rw [h9] at h5
        exact h5
      have h_cond : (if true then p i ≥ thr else p i ≤ -thr) := by
        simp
        exact h8
      have h_mem : p ∈ S (i, true) := by
        exact ⟨hp, h_cond⟩
      exact Set.mem_iUnion.mpr ⟨(i, true), h_mem⟩
    · have h9 : p i < 0 := by linarith
      have h10 : p i ≤ -thr := by
        have h11 : |p i| = -p i := abs_of_neg h9
        rw [h11] at h5
        have h12 : -p i ≥ thr := h5
        have h13 : p i ≤ -thr := by
          calc
            p i = -(-p i) := by ring
            _ ≤ -thr := neg_le_neg h12
        exact h13
      have h_cond : (if false then p i ≥ thr else p i ≤ -thr) := by
        simp
        exact h10
      have h_mem : p ∈ S (i, false) := by
        exact ⟨hp, h_cond⟩
      exact Set.mem_iUnion.mpr ⟨(i, false), h_mem⟩
  have h_sum_lt_top : (∑ p : idx, (μHE[2] : Measure (Point 3)) (S p)) < ⊤ := by
    have h_all : ∀ (p : idx), (μHE[2] : Measure (Point 3)) (S p) < ⊤ := fun p => h_main p.1 p.2
    have h_ind : ∀ (s : Finset idx), (∑ p ∈ s, (μHE[2] : Measure (Point 3)) (S p)) < ⊤ := by
      intro s
      induction s using Finset.induction with
      | empty => simp
      | @insert a s ha ih =>
        rw [Finset.sum_insert ha]
        exact ENNReal.add_lt_top.mpr ⟨h_all a, ih⟩
    exact h_ind Finset.univ
  have h_le : (μHE[2] : Measure (Point 3)) (unitSphere 3) ≤ ∑ p : idx, (μHE[2] : Measure (Point 3)) (S p) := by
    calc
      (μHE[2] : Measure (Point 3)) (unitSphere 3)
        ≤ (μHE[2] : Measure (Point 3)) (⋃ p : idx, S p) := measure_mono h_cover
      _ = (μHE[2] : Measure (Point 3)) (⋃ p ∈ (Finset.univ : Finset idx), S p) := by
        congr with x
        simp only [Set.mem_iUnion, Finset.mem_univ]
        <;> tauto
      _ ≤ ∑ p ∈ (Finset.univ : Finset idx), (μHE[2] : Measure (Point 3)) (S p) :=
        MeasureTheory.measure_biUnion_finset_le _ _
      _ = ∑ p : idx, (μHE[2] : Measure (Point 3)) (S p) := by simp
  exact lt_of_le_of_lt h_le h_sum_lt_top

end

end Kakeya.CV
