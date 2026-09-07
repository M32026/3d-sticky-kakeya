module

/-
  ConcentratedHPrime.lean

  Definitions and lemmas for the concentrated H' set and bounded overlap.

  Main results:
  - `ConcentratedH'` — strict concentration set
  - `ConcentratedH'_measurable` — Borel measurability
  - `source_tubes_bounded_overlap_general` — ≤66 overlap for separation r/(4R)
  - `concentrated_H'_fiber_lower_general` — H' fiber lower bound

  Whiteprint node: concentrated-case
-/

public import MyLeanRepo.RadialBootstrapping.Basic
public import MyLeanRepo.RadialBootstrapping.HBarMeasurable
public import MyLeanRepo.RadialBootstrapping.BoundedOverlapHelpers
public import MyLeanRepo.RadialBootstrapping.GreedySelection
public import MyLeanRepo.OSWPrelude

@[expose] public section

open MeasureTheory Metric Set Finset Classical
open scoped ENNReal NNReal


noncomputable section

namespace RadialBootstrapping

/-! ============================================================================
   1. Openness of concentrated condition in (normal, center)
   ============================================================================ -/

/-- For fixed x, the set of (n,c) such that
    `ν₂(tubeOfNormal r x n ∩ ball c R ∩ G_x) > threshold` is open. -/
lemma concentrated_normal_center_open
    (x : Point) (r R threshold : ℝ)
    (hr : 0 < r) (hR : 0 < R) (hthreshold : 0 ≤ threshold)
    (G : Set (Point × Point)) (hG_meas : MeasurableSet G)
    (ν₂ : Measure Point) [IsProbabilityMeasure ν₂] :
    IsOpen {p : UnitSphere' × Point |
      ν₂ (tubeOfNormal r x p.1 ∩ Metric.ball p.2 R ∩ {b₂ | (x, b₂) ∈ G}) >
        ENNReal.ofReal threshold} := by
  let G_x : Set Point := {b₂ | (x, b₂) ∈ G}
  have h_f : Measurable (fun (y : Point) => (x, y)) := by exact measurable_prodMk_left
  have hGx_meas : MeasurableSet G_x := hG_meas.preimage h_f
  rw [isOpen_iff_mem_nhds]
  intro p hp
  let n0 := p.1
  let c0 := p.2
  let A : Set Point := tubeOfNormal r x n0 ∩ Metric.ball c0 R ∩ G_x
  have hA_open : IsOpen (tubeOfNormal r x n0 ∩ Metric.ball c0 R) :=
    (tubeOfNormal_open r hr x n0).inter isOpen_ball
  have hA_meas : MeasurableSet A :=
    hA_open.measurableSet.inter hGx_meas
  have hA_lt_top : ν₂ A ≠ ⊤ := ne_top_of_le_ne_top (by simp) (measure_mono (subset_univ A))
  have h_gt : ENNReal.ofReal threshold < ν₂ A := hp
  have hreg : ν₂.InnerRegularCompactLTTop := by infer_instance
  have h_inner : ∃ (K : Set Point), K ⊆ A ∧ IsCompact K ∧ ENNReal.ofReal threshold < ν₂ K :=
    hreg.innerRegular (U := A) ⟨hA_meas, hA_lt_top⟩ (ENNReal.ofReal threshold) h_gt
  rcases h_inner with ⟨K, hK_sub_A, hK_comp, hK_gt⟩
  let W : Set (Point × (UnitSphere' × Point)) :=
    {zp | |dot (zp.1 - x) (zp.2.1 : Point)| < r ∧ dist zp.1 zp.2.2 < R}
  have hW_open : IsOpen W := by
    have h1 : Continuous (fun zp : Point × (UnitSphere' × Point) =>
        dot (zp.1 - x) (zp.2.1 : Point)) := by fun_prop
    have h2 : Continuous (fun zp : Point × (UnitSphere' × Point) => dist zp.1 zp.2.2) := by fun_prop
    have hc_r : Continuous (fun (_ : Point × (UnitSphere' × Point)) => r) := continuous_const
    have hc_R : Continuous (fun (_ : Point × (UnitSphere' × Point)) => R) := continuous_const
    exact (isOpen_lt (Continuous.abs h1) hc_r).inter (isOpen_lt h2 hc_R)
  have hKxp : K ×ˢ ({p} : Set (UnitSphere' × Point)) ⊆ W := by
    rintro ⟨z, q⟩ ⟨hz, hq⟩
    have hq' : q = p := by simpa using hq
    rw [hq']
    have hzA : z ∈ A := hK_sub_A hz
    have h1 : z ∈ tubeOfNormal r x n0 := hzA.1.1
    have h2 : z ∈ Metric.ball c0 R := hzA.1.2
    simpa [W, tubeOfNormal] using ⟨h1, h2⟩
  have h_singleton : IsCompact ({p} : Set (UnitSphere' × Point)) := isCompact_singleton
  have h := generalized_tube_lemma hK_comp h_singleton hW_open hKxp
  rcases h with ⟨V, U, hV_open, hU_open, hK_sub_V, hp_sub_U, h_box⟩
  have hpU : p ∈ U := by simpa using hp_sub_U
  have hU_nhds : U ∈ nhds p := hU_open.mem_nhds hpU
  have hU_sub : U ⊆ {p : UnitSphere' × Point |
      ν₂ (tubeOfNormal r x p.1 ∩ Metric.ball p.2 R ∩ G_x) > ENNReal.ofReal threshold} := by
    intro q hq
    have h5 : K ⊆ tubeOfNormal r x q.1 ∩ Metric.ball q.2 R := by
      intro z hz
      have h6 : (z, q) ∈ W := h_box ⟨hK_sub_V hz, hq⟩
      exact h6
    have h7 : K ⊆ tubeOfNormal r x q.1 ∩ Metric.ball q.2 R ∩ G_x := by
      intro z hz
      have h8 : z ∈ K := hz
      have h9 : z ∈ tubeOfNormal r x q.1 ∩ Metric.ball q.2 R := h5 h8
      have h10 : z ∈ G_x := (hK_sub_A h8).2
      exact ⟨h9, h10⟩
    have h11 : ν₂ K ≤ ν₂ (tubeOfNormal r x q.1 ∩ Metric.ball q.2 R ∩ G_x) :=
      measure_mono h7
    exact hK_gt.trans_le h11
  exact Filter.mem_of_superset hU_nhds hU_sub

/-! ============================================================================
   2. Measurability of concentrated H'
   ============================================================================ -/

/-- Strict concentrated H': pairs (x,y) where there exists a line through x
    with direction n and center c such that the tube has concentrated mass
    above threshold and y is in both the tube and the concentration ball. -/
def ConcentratedH' (ν₂ : Measure Point)
    (G : Set (Point × Point)) (r κ threshold : ℝ) : Set (Point × Point) :=
  {p | ∃ (n : UnitSphere') (c : Point),
    ν₂ (tubeOfNormal r p.1 n ∩ Metric.ball c (Real.rpow r κ) ∩
        {b₂ | (p.1, b₂) ∈ G}) > ENNReal.ofReal threshold ∧
    p.2 ∈ tubeOfNormal r p.1 n ∩ Metric.ball c (Real.rpow r κ)}

/-- ConcentratedH' is Borel measurable. -/
lemma ConcentratedH'_measurable
    (ν₂ : Measure Point) [IsProbabilityMeasure ν₂]
    (G : Set (Point × Point)) (hG_meas : MeasurableSet G)
    (r κ threshold : ℝ) (hr : 0 < r) (hκ_pos : 0 < Real.rpow r κ)
    (hthreshold_nonneg : 0 ≤ threshold) :
    MeasurableSet (ConcentratedH' ν₂ G r κ threshold) := by
  have h_sep : TopologicalSpace.SeparableSpace (UnitSphere' × Point) := by infer_instance
  rcases TopologicalSpace.exists_countable_dense (UnitSphere' × Point) with ⟨D, hD_count, hD_dense⟩
  let S : UnitSphere' × Point → Set (Point × Point) := fun nc =>
    {p | ν₂ (tubeOfNormal r p.1 nc.1 ∩ Metric.ball nc.2 (Real.rpow r κ) ∩
            {b₂ | (p.1, b₂) ∈ G}) > ENNReal.ofReal threshold ∧
      p.2 ∈ tubeOfNormal r p.1 nc.1 ∩ Metric.ball nc.2 (Real.rpow r κ)}
  have hS_meas : ∀ nc : UnitSphere' × Point, MeasurableSet (S nc) := by
    intro nc
    let n := nc.1
    let c := nc.2
    let A_nc : Set (Point × Point) :=
      {p | p.2 ∈ tubeOfNormal r p.1 n ∩ Metric.ball c (Real.rpow r κ) ∧ p ∈ G}
    have h1_open : IsOpen {p : Point × Point | p.2 ∈ tubeOfNormal r p.1 n} := by
      have h_cont : Continuous (fun p : Point × Point => |dot (p.2 - p.1) (n : Point)|) := by fun_prop
      have hc : Continuous (fun (_ : Point × Point) => r) := continuous_const
      exact isOpen_lt h_cont hc
    have h2_open : IsOpen {p : Point × Point | p.2 ∈ Metric.ball c (Real.rpow r κ)} := by
      have h_cont : Continuous (fun p : Point × Point => dist p.2 c) := by fun_prop
      have hc : Continuous (fun (_ : Point × Point) => Real.rpow r κ) := continuous_const
      exact isOpen_lt h_cont hc
    have hA_nc_open : IsOpen {p : Point × Point | p.2 ∈ tubeOfNormal r p.1 n ∩ Metric.ball c (Real.rpow r κ)} :=
      h1_open.inter h2_open
    have hA_nc_meas : MeasurableSet A_nc :=
      hA_nc_open.measurableSet.inter hG_meas
    have h_f_meas : Measurable (fun x : Point => ν₂ (Prod.mk x ⁻¹' A_nc)) :=
      measurable_measure_prodMk_left_finite hA_nc_meas
    have h_meas1 : MeasurableSet {x : Point |
        ENNReal.ofReal threshold < ν₂ (tubeOfNormal r x n ∩ Metric.ball c (Real.rpow r κ) ∩
          {b₂ | (x, b₂) ∈ G})} := by
      have h_eq : {x : Point | ENNReal.ofReal threshold < ν₂ (Prod.mk x ⁻¹' A_nc)} =
          {x : Point | ENNReal.ofReal threshold < ν₂ (tubeOfNormal r x n ∩ Metric.ball c (Real.rpow r κ) ∩
            {b₂ | (x, b₂) ∈ G})} := by
        ext x; simp [A_nc, Prod.mk] <;> rfl
      rw [←h_eq]
      exact measurableSet_lt measurable_const h_f_meas
    have h3 : ({x : Point | ENNReal.ofReal threshold < ν₂ (tubeOfNormal r x n ∩ Metric.ball c (Real.rpow r κ) ∩
              {b₂ | (x, b₂) ∈ G})} ×ˢ Set.univ) ∩
            {p : Point × Point | p.2 ∈ tubeOfNormal r p.1 n ∩ Metric.ball c (Real.rpow r κ)} = S nc := by
      ext p; simp [S] <;> tauto
    rw [←h3]
    exact h_meas1.prod MeasurableSet.univ |>.inter hA_nc_open.measurableSet
  have h_eq : ConcentratedH' ν₂ G r κ threshold = ⋃ nc ∈ D, S nc := by
    ext ⟨x, y⟩
    simp only [ConcentratedH', S, Set.mem_iUnion₂, Set.mem_setOf_eq]
    constructor
    · rintro ⟨n, c, hmass, hytube⟩
      let BadSet := {p : UnitSphere' × Point |
        ν₂ (tubeOfNormal r x p.1 ∩ Metric.ball p.2 (Real.rpow r κ) ∩ {b₂ | (x, b₂) ∈ G}) >
          ENNReal.ofReal threshold}
      let TubeSet := {p : UnitSphere' × Point |
        y ∈ tubeOfNormal r x p.1 ∩ Metric.ball p.2 (Real.rpow r κ)}
      have hBad_open : IsOpen BadSet :=
        concentrated_normal_center_open x r (Real.rpow r κ) threshold hr hκ_pos hthreshold_nonneg G hG_meas ν₂
      have hTube_open : IsOpen TubeSet := by
        have h1 : Continuous (fun p : UnitSphere' × Point => |dot (y - x) (p.1 : Point)|) := by fun_prop
        have h2 : Continuous (fun p : UnitSphere' × Point => dist y p.2) := by fun_prop
        have hc1 : Continuous (fun (_ : UnitSphere' × Point) => r) := continuous_const
        have hc2 : Continuous (fun (_ : UnitSphere' × Point) => Real.rpow r κ) := continuous_const
        have h_set1 : IsOpen {p : UnitSphere' × Point | |dot (y - x) (p.1 : Point)| < r} :=
          isOpen_lt h1 hc1
        have h_set2 : IsOpen {p : UnitSphere' × Point | dist y p.2 < Real.rpow r κ} :=
          isOpen_lt h2 hc2
        have h_eq : TubeSet = {p | |dot (y - x) (p.1 : Point)| < r} ∩ {p | dist y p.2 < Real.rpow r κ} := by
          ext p; simp [TubeSet, tubeOfNormal] <;> rfl
        rw [h_eq]
        exact h_set1.inter h_set2
      have h_inter_open : IsOpen (BadSet ∩ TubeSet) := hBad_open.inter hTube_open
      have hn_inter : (n, c) ∈ BadSet ∩ TubeSet := ⟨hmass, hytube⟩
      have h_nonempty : (BadSet ∩ TubeSet).Nonempty := ⟨(n, c), hn_inter⟩
      have hD_inter' : (BadSet ∩ TubeSet ∩ D).Nonempty :=
        hD_dense.inter_open_nonempty (BadSet ∩ TubeSet) h_inter_open h_nonempty
      rcases hD_inter' with ⟨nc, hnc⟩
      have h_break : nc ∈ BadSet ∩ TubeSet ∧ nc ∈ D := by
        simpa [Set.mem_inter_iff] using hnc
      rcases h_break with ⟨hnc_inter, hncD⟩
      exact ⟨nc, hncD, hnc_inter.1, hnc_inter.2⟩
    · rintro ⟨nc, hncD, hmass, hytube⟩
      exact ⟨nc.1, nc.2, hmass, hytube⟩
  rw [h_eq]
  exact MeasurableSet.biUnion hD_count (fun nc _ => hS_meas nc)

/-! ============================================================================
   2b. Exposed S_nc definition and union equality
   ============================================================================ -/

/-- The fiber of ConcentratedH' corresponding to a fixed (normal, center) pair. -/
def ConcentratedH'_S (ν₂ : Measure Point)
    (G : Set (Point × Point)) (r κ threshold : ℝ)
    (nc : UnitSphere' × Point) : Set (Point × Point) :=
  {p | ν₂ (tubeOfNormal r p.1 nc.1 ∩ Metric.ball nc.2 (Real.rpow r κ) ∩
          {b₂ | (p.1, b₂) ∈ G}) > ENNReal.ofReal threshold ∧
    p.2 ∈ tubeOfNormal r p.1 nc.1 ∩ Metric.ball nc.2 (Real.rpow r κ)}

/-- Each ConcentratedH'_S fiber is measurable. -/
lemma ConcentratedH'_S_meas
    (ν₂ : Measure Point) [IsProbabilityMeasure ν₂]
    (G : Set (Point × Point)) (hG_meas : MeasurableSet G)
    (r κ threshold : ℝ) (hr : 0 < r) (hκ_pos : 0 < Real.rpow r κ)
    (hthreshold_nonneg : 0 ≤ threshold)
    (nc : UnitSphere' × Point) :
    MeasurableSet (ConcentratedH'_S ν₂ G r κ threshold nc) := by
  let n := nc.1
  let c := nc.2
  let A_nc : Set (Point × Point) :=
    {p | p.2 ∈ tubeOfNormal r p.1 n ∩ Metric.ball c (Real.rpow r κ) ∧ p ∈ G}
  have h1_open : IsOpen {p : Point × Point | p.2 ∈ tubeOfNormal r p.1 n} := by
    have h_cont : Continuous (fun p : Point × Point => |dot (p.2 - p.1) (n : Point)|) := by fun_prop
    have hc : Continuous (fun (_ : Point × Point) => r) := continuous_const
    exact isOpen_lt h_cont hc
  have h2_open : IsOpen {p : Point × Point | p.2 ∈ Metric.ball c (Real.rpow r κ)} := by
    have h_cont : Continuous (fun p : Point × Point => dist p.2 c) := by fun_prop
    have hc : Continuous (fun (_ : Point × Point) => Real.rpow r κ) := continuous_const
    exact isOpen_lt h_cont hc
  have hA_nc_open : IsOpen {p : Point × Point | p.2 ∈ tubeOfNormal r p.1 n ∩ Metric.ball c (Real.rpow r κ)} :=
    h1_open.inter h2_open
  have hA_nc_meas : MeasurableSet A_nc := hA_nc_open.measurableSet.inter hG_meas
  have h_f_meas : Measurable (fun x : Point => ν₂ (Prod.mk x ⁻¹' A_nc)) :=
    measurable_measure_prodMk_left_finite hA_nc_meas
  have h_meas1 : MeasurableSet {x : Point |
      ENNReal.ofReal threshold < ν₂ (tubeOfNormal r x n ∩ Metric.ball c (Real.rpow r κ) ∩
        {b₂ | (x, b₂) ∈ G})} := by
    have h_eq : {x : Point | ENNReal.ofReal threshold < ν₂ (Prod.mk x ⁻¹' A_nc)} =
        {x : Point | ENNReal.ofReal threshold < ν₂ (tubeOfNormal r x n ∩ Metric.ball c (Real.rpow r κ) ∩
          {b₂ | (x, b₂) ∈ G})} := by
      ext x; simp [A_nc, Prod.mk] <;> rfl
    rw [←h_eq]
    exact measurableSet_lt measurable_const h_f_meas
  have h3 : ({x : Point | ENNReal.ofReal threshold < ν₂ (tubeOfNormal r x n ∩ Metric.ball c (Real.rpow r κ) ∩
            {b₂ | (x, b₂) ∈ G})} ×ˢ Set.univ) ∩
      {p : Point × Point | p.2 ∈ tubeOfNormal r p.1 n ∩ Metric.ball c (Real.rpow r κ)} =
      ConcentratedH'_S ν₂ G r κ threshold nc := by
    ext p; simp [ConcentratedH'_S, A_nc] <;> tauto
  rw [←h3]
  exact h_meas1.prod MeasurableSet.univ |>.inter hA_nc_open.measurableSet

/-- ConcentratedH' equals the union over a countable dense set of its fibers. -/
lemma ConcentratedH'_eq_union
    (ν₂ : Measure Point) [IsProbabilityMeasure ν₂]
    (G : Set (Point × Point)) (hG_meas : MeasurableSet G)
    (r κ threshold : ℝ) (hr : 0 < r) (hκ_pos : 0 < Real.rpow r κ)
    (hthreshold_nonneg : 0 ≤ threshold)
    {D : Set (UnitSphere' × Point)} (hD_count : Set.Countable D)
    (hD_dense : Dense D) :
    ConcentratedH' ν₂ G r κ threshold = ⋃ nc ∈ D, ConcentratedH'_S ν₂ G r κ threshold nc := by
  let BadSet (x : Point) : Set (UnitSphere' × Point) :=
    {p | ν₂ (tubeOfNormal r x p.1 ∩ Metric.ball p.2 (Real.rpow r κ) ∩ {b₂ | (x, b₂) ∈ G}) >
      ENNReal.ofReal threshold}
  let TubeSet (x y : Point) : Set (UnitSphere' × Point) :=
    {p | y ∈ tubeOfNormal r x p.1 ∩ Metric.ball p.2 (Real.rpow r κ)}
  ext ⟨x, y⟩
  simp only [ConcentratedH', ConcentratedH'_S, Set.mem_iUnion₂, Set.mem_setOf_eq]
  constructor
  · rintro ⟨n, c, hmass, hytube⟩
    have hBad_open : IsOpen (BadSet x) :=
      concentrated_normal_center_open x r (Real.rpow r κ) threshold hr hκ_pos hthreshold_nonneg G hG_meas ν₂
    have hTube_open : IsOpen (TubeSet x y) := by
      have h1 : Continuous (fun p : UnitSphere' × Point => |dot (y - x) (p.1 : Point)|) := by fun_prop
      have h2 : Continuous (fun p : UnitSphere' × Point => dist y p.2) := by fun_prop
      have hc1 : Continuous (fun (_ : UnitSphere' × Point) => r) := continuous_const
      have hc2 : Continuous (fun (_ : UnitSphere' × Point) => Real.rpow r κ) := continuous_const
      have h_set1 : IsOpen {p : UnitSphere' × Point | |dot (y - x) (p.1 : Point)| < r} := isOpen_lt h1 hc1
      have h_set2 : IsOpen {p : UnitSphere' × Point | dist y p.2 < Real.rpow r κ} := isOpen_lt h2 hc2
      have h_eq : TubeSet x y = {p | |dot (y - x) (p.1 : Point)| < r} ∩ {p | dist y p.2 < Real.rpow r κ} := by
        ext p; simp [TubeSet, tubeOfNormal] <;> rfl
      rw [h_eq]; exact h_set1.inter h_set2
    have h_inter_open : IsOpen (BadSet x ∩ TubeSet x y) := hBad_open.inter hTube_open
    have hn_inter : (n, c) ∈ BadSet x ∩ TubeSet x y := ⟨hmass, hytube⟩
    have h_nonempty : (BadSet x ∩ TubeSet x y).Nonempty := ⟨(n, c), hn_inter⟩
    have hD_inter' : (BadSet x ∩ TubeSet x y ∩ D).Nonempty :=
      hD_dense.inter_open_nonempty (BadSet x ∩ TubeSet x y) h_inter_open h_nonempty
    rcases hD_inter' with ⟨nc, hnc⟩
    have h_break : nc ∈ BadSet x ∩ TubeSet x y ∧ nc ∈ D := by
      simpa [Set.mem_inter_iff] using hnc
    rcases h_break with ⟨hnc_inter, hncD⟩
    exact ⟨nc, hncD, hnc_inter.1, hnc_inter.2⟩
  · rintro ⟨nc, hncD, hmass, hytube⟩
    exact ⟨nc.1, nc.2, hmass, hytube⟩

/-! ============================================================================
   3. Angle adjustment helpers
   ============================================================================ -/

/-- Adjust a real number to lie in [-π/2, π/2] by subtracting an integer
multiple of π. -/
def modPiHalf (t : ℝ) : ℝ :=
  t - (Int.floor (t / Real.pi + 1 / 2) : ℝ) * Real.pi

lemma modPiHalf_bounds (t : ℝ) :
    -Real.pi / 2 ≤ modPiHalf t ∧ modPiHalf t ≤ Real.pi / 2 := by
  let n : ℤ := Int.floor (t / Real.pi + 1 / 2)
  have h1 : (n : ℝ) ≤ t / Real.pi + 1 / 2 := Int.floor_le _
  have h2 : t / Real.pi + 1 / 2 < (n : ℝ) + 1 := Int.lt_floor_add_one _
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have h3 : (n : ℝ) - 1 / 2 ≤ t / Real.pi := by linarith
  have h4 : t / Real.pi < (n : ℝ) + 1 / 2 := by linarith
  have h5 : ((n : ℝ) - 1 / 2) * Real.pi ≤ t := by
    have h51 : ((n : ℝ) - 1 / 2) ≤ t / Real.pi := h3
    have h : ((n : ℝ) - 1 / 2) * Real.pi ≤ (t / Real.pi) * Real.pi :=
      mul_le_mul_of_nonneg_right h51 (by linarith)
    have h6 : (t / Real.pi) * Real.pi = t := by
      field_simp [hpi_pos.ne'] <;> ring
    rw [h6] at h; exact h
  have h6 : t < ((n : ℝ) + 1 / 2) * Real.pi := by
    have h61 : t / Real.pi < (n : ℝ) + 1 / 2 := h4
    have h : (t / Real.pi) * Real.pi < ((n : ℝ) + 1 / 2) * Real.pi :=
      mul_lt_mul_of_pos_right h61 hpi_pos
    have h7 : (t / Real.pi) * Real.pi = t := by
      field_simp [hpi_pos.ne'] <;> ring
    rw [h7] at h; exact h
  have h7 : -Real.pi / 2 ≤ t - (n : ℝ) * Real.pi := by linarith
  have h8 : t - (n : ℝ) * Real.pi < Real.pi / 2 := by linarith
  have h9 : modPiHalf t = t - (n : ℝ) * Real.pi := by
    simp [modPiHalf, n] <;> rfl
  rw [h9]; exact ⟨h7, by linarith⟩

lemma modPiHalf_abs_bounds (t : ℝ) : |modPiHalf t| ≤ Real.pi / 2 := by
  have h1 := modPiHalf_bounds t
  have h2 : -(Real.pi / 2) ≤ modPiHalf t := by linarith
  have h3 : modPiHalf t ≤ Real.pi / 2 := by linarith
  exact abs_le.mpr ⟨h2, h3⟩

lemma modPiHalf_eq_sub_int_mul_pi (t : ℝ) :
    ∃ (n : ℤ), modPiHalf t = t - (n : ℝ) * Real.pi := by
  refine ⟨Int.floor (t / Real.pi + 1 / 2), ?_⟩
  simp [modPiHalf] <;> rfl

lemma abs_sin_modPiHalf (t : ℝ) :
    |Real.sin (modPiHalf t)| = |Real.sin t| := by
  rcases modPiHalf_eq_sub_int_mul_pi t with ⟨n, hn⟩
  have h : Real.sin (modPiHalf t) = (-1 : ℝ)^n * Real.sin t := by
    rw [hn]
    have h1 : Real.sin ((n : ℝ) * Real.pi - t) = -((-1 : ℝ)^n * Real.sin t) :=
      Real.sin_int_mul_pi_sub t n
    have h2 : Real.sin (t - (n : ℝ) * Real.pi) = -Real.sin ((n : ℝ) * Real.pi - t) := by
      rw [show t - (n : ℝ) * Real.pi = -((n : ℝ) * Real.pi - t) by ring]
      rw [Real.sin_neg] <;> ring
    rw [h2, h1] <;> ring
  rw [h]
  have h3 : |((-1 : ℝ)^n * Real.sin t)| = |Real.sin t| := by
    have h4 : |((-1 : ℝ)^n)| = 1 := by simp [abs_pow] <;> norm_num
    rw [abs_mul, h4] <;> ring
  exact h3

lemma abs_sin_sub_modPiHalf (t1 t2 : ℝ) :
    |Real.sin (modPiHalf t1 - modPiHalf t2)| = |Real.sin (t1 - t2)| := by
  rcases modPiHalf_eq_sub_int_mul_pi t1 with ⟨n1, h1⟩
  rcases modPiHalf_eq_sub_int_mul_pi t2 with ⟨n2, h2⟩
  let k : ℤ := n1 - n2
  have h3 : modPiHalf t1 - modPiHalf t2 = (t1 - t2) - (k : ℝ) * Real.pi := by
    rw [h1, h2]; simp [k, sub_eq_add_neg] <;> ring
  rw [h3]
  have h4 : Real.sin ((t1 - t2) - (k : ℝ) * Real.pi) =
      (-1 : ℝ)^k * Real.sin (t1 - t2) := by
    have h5 : Real.sin ((k : ℝ) * Real.pi - (t1 - t2)) =
        -((-1 : ℝ)^k * Real.sin (t1 - t2)) :=
      Real.sin_int_mul_pi_sub (t1 - t2) k
    have h6 : Real.sin ((t1 - t2) - (k : ℝ) * Real.pi) =
        -Real.sin ((k : ℝ) * Real.pi - (t1 - t2)) := by
      rw [show (t1 - t2) - (k : ℝ) * Real.pi = -((k : ℝ) * Real.pi - (t1 - t2)) by ring]
      rw [Real.sin_neg] <;> ring
    rw [h6, h5] <;> ring
  rw [h4]
  have h7 : |((-1 : ℝ)^k * Real.sin (t1 - t2))| = |Real.sin (t1 - t2)| := by
    have h8 : |((-1 : ℝ)^k)| = 1 := by simp [abs_pow] <;> norm_num
    rw [abs_mul, h8] <;> ring
  exact h7

/-! ============================================================================
   4. Generalized bounded overlap for direction grid (separation r/(4R))
   ============================================================================ -/

/-- Generalized version: at most 66 tubes through `x`, with direction separation
    `r/(4*R)`, can have a point `y` at distance `≥ R` from `x` in their
    `r`-neighborhood. -/
lemma source_tubes_bounded_overlap_general
    (x : Point) (r R : ℝ) (hr : 0 < r) (hR : 0 < R)
    (T : Finset (AffineSubspace ℝ Point))
    (h_lines : ∀ ℓ ∈ T, x ∈ (ℓ : Set Point) ∧ Module.finrank ℝ ℓ.direction = 1)
    (h_sep : ∀ ℓ1 ∈ T, ∀ ℓ2 ∈ T, ℓ1 ≠ ℓ2 →
      submoduleDirDist ℓ1.direction ℓ2.direction ≥ r / (4 * R))
    (y : Point) (hyd : dist x y ≥ R) :
    (T.filter (fun (ℓ : AffineSubspace ℝ Point) => y ∈ Metric.thickening r (ℓ : Set Point))).card ≤ 66 := by
  classical
  let T' : Finset (AffineSubspace ℝ Point) :=
    T.filter (fun ℓ => y ∈ Metric.thickening r (ℓ : Set Point))
  have hT'_sub : T' ⊆ T := Finset.filter_subset _ _
  have h_y_ne_x : y ≠ x := by
    intro h
    have h9 : dist x y = 0 := by rw [h] <;> simp
    linarith [hR, hyd]
  let V0 := Submodule.span ℝ {y - x}
  have hV0 : Module.finrank ℝ V0 = 1 :=
    finrank_span_singleton (show y - x ≠ 0 from sub_ne_zero.mpr h_y_ne_x)
  let θ0 := directionAngle V0 hV0
  have h_bound : ∀ ℓ ∈ T', submoduleDirDist ℓ.direction V0 ≤ 4 * r / R := by
    intro ℓ hℓ
    have hℓT : ℓ ∈ T := hT'_sub hℓ
    have h_y_in : y ∈ Metric.thickening r (ℓ : Set Point) := (Finset.mem_filter.mp hℓ).2
    let L : Line2 := ⟨ℓ, (h_lines ℓ hℓT).2⟩
    have h_x_on : x ∈ (ℓ : Set Point) := (h_lines ℓ hℓT).1
    have h_x_in_2tube : x ∈ tube (2 * r) L := by
      have h : x ∈ (L.toSet) := h_x_on
      exact Metric.mem_thickening_iff.mpr ⟨x, h, by simp [infDist_lt_iff, hr]⟩
    have h_y_in_2tube : y ∈ tube (2 * r) L := by
      rcases Metric.mem_thickening_iff.mp h_y_in with ⟨z, hz, hdist⟩
      exact Metric.mem_thickening_iff.mpr ⟨z, hz, by linarith⟩
    have h_main := direction_closeness r hr L x y h_y_ne_x h_x_in_2tube h_y_in_2tube
    have h_norm : ‖y - x‖ ≥ R := by
      have h10 : dist x y = ‖x - y‖ := by rfl
      have h11 : ‖y - x‖ = ‖x - y‖ := by rw [norm_sub_rev]
      linarith
    calc
      submoduleDirDist ℓ.direction V0
        = submoduleDirDist L.toAffine.direction V0 := by rfl
      _ ≤ 4 * r / ‖y - x‖ := h_main
      _ ≤ 4 * r / R := by gcongr
  let ψ : {ℓ // ℓ ∈ T'} → ℝ := fun p =>
    modPiHalf (directionAngle p.val.direction (h_lines p.val (hT'_sub p.property)).2 - θ0)
  have h_abs_sin : ∀ p, |Real.sin (ψ p)| = submoduleDirDist p.val.direction V0 := by
    intro p
    have h1 : |Real.sin (ψ p)| =
        |Real.sin (directionAngle p.val.direction (h_lines p.val (hT'_sub p.property)).2 - θ0)| := by
      simp [ψ, abs_sin_modPiHalf]
    rw [h1, dirDist_eq_abs_sin p.val.direction V0
      (h_lines p.val (hT'_sub p.property)).2 hV0] <;> rfl
  have hψ_abs_pi2 : ∀ p, |ψ p| ≤ Real.pi / 2 := fun p => modPiHalf_abs_bounds _
  have h_inj : Set.InjOn ψ (T'.attach : Set {ℓ // ℓ ∈ T'}) := by
    intro p1 hp1 p2 hp2 h_eq
    by_contra hne
    have hne_val : p1.val ≠ p2.val := by intro h; apply hne; exact Subtype.ext h
    have hℓ1T : p1.val ∈ T := hT'_sub p1.property
    have hℓ2T : p2.val ∈ T := hT'_sub p2.property
    have h_sep' : submoduleDirDist p1.val.direction p2.val.direction ≥ r / (4 * R) :=
      h_sep p1.val hℓ1T p2.val hℓ2T hne_val
    have h11 : |Real.sin (ψ p1 - ψ p2)| =
        |Real.sin (directionAngle p1.val.direction (h_lines p1.val hℓ1T).2 -
          directionAngle p2.val.direction (h_lines p2.val hℓ2T).2)| := by
      have h_simp : ψ p1 - ψ p2 =
          modPiHalf (directionAngle p1.val.direction (h_lines p1.val hℓ1T).2 - θ0) -
          modPiHalf (directionAngle p2.val.direction (h_lines p2.val hℓ2T).2 - θ0) := by rfl
      rw [h_simp]
      have h := abs_sin_sub_modPiHalf
        (directionAngle p1.val.direction (h_lines p1.val hℓ1T).2 - θ0)
        (directionAngle p2.val.direction (h_lines p2.val hℓ2T).2 - θ0)
      have h_alg : (directionAngle p1.val.direction (h_lines p1.val hℓ1T).2 - θ0) -
          (directionAngle p2.val.direction (h_lines p2.val hℓ2T).2 - θ0) =
          directionAngle p1.val.direction (h_lines p1.val hℓ1T).2 -
          directionAngle p2.val.direction (h_lines p2.val hℓ2T).2 := by ring
      rw [h_alg] at h; exact h
    have h12 : |Real.sin (directionAngle p1.val.direction (h_lines p1.val hℓ1T).2 -
        directionAngle p2.val.direction (h_lines p2.val hℓ2T).2)| =
        submoduleDirDist p1.val.direction p2.val.direction := by
      rw [dirDist_eq_abs_sin p1.val.direction p2.val.direction
        (h_lines p1.val hℓ1T).2 (h_lines p2.val hℓ2T).2] <;> rfl
    have h13 : |Real.sin (ψ p1 - ψ p2)| = 0 := by rw [h_eq] <;> simp
    rw [h11, h12] at h13
    have h14 : submoduleDirDist p1.val.direction p2.val.direction = 0 := by simpa using h13
    have h_pos : 0 < r / (4 * R) := by positivity
    rw [h14] at h_sep'
    have h_contra : (0 : ℝ) ≥ r / (4 * R) := h_sep'
    exact False.elim (not_le.mpr h_pos h_contra)
  have h_card_attach : T'.attach.card = T'.card := by simp
  let s : Finset ℝ := T'.attach.image ψ
  have h_card_s : s.card = T'.card := by
    rw [Finset.card_image_of_injOn h_inj, h_card_attach]
  by_cases h_case : r ≤ R / 4
  · -- Case 1: r ≤ R/4
    have h_r_div_R : r / R ≤ 1 / 4 := by
      have h1 : r ≤ R / 4 := h_case
      have h2 : 0 < R := hR
      calc r / R ≤ (R / 4) / R := by gcongr
           _ = 1 / 4 := by field_simp [h2.ne'] <;> ring
    have hψ_bounds : ∀ p, -(2 * Real.pi * r / R) ≤ ψ p ∧ ψ p ≤ 2 * Real.pi * r / R := by
      intro p
      have h1 : |Real.sin (ψ p)| ≤ 4 * r / R := by
        rw [h_abs_sin p] <;> exact h_bound p.val p.property
      have h2 : |ψ p| ≤ Real.pi / 2 := hψ_abs_pi2 p
      have h3 : (2 / Real.pi) * |ψ p| ≤ |Real.sin (ψ p)| := Real.mul_abs_le_abs_sin h2
      have hpi_ne : Real.pi ≠ 0 := Real.pi_ne_zero
      have h4 : |ψ p| ≤ 2 * Real.pi * r / R := by
        have h5 : |ψ p| = (Real.pi / 2) * ((2 / Real.pi) * |ψ p|) := by
          field_simp [hpi_ne] <;> ring
        rw [h5]
        have h6 : (Real.pi / 2) * ((2 / Real.pi) * |ψ p|) ≤ (Real.pi / 2) * |Real.sin (ψ p)| :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
        have h7 : (Real.pi / 2) * |Real.sin (ψ p)| ≤ (Real.pi / 2) * (4 * r / R) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
        have h8 : (Real.pi / 2) * (4 * r / R) = 2 * Real.pi * r / R := by ring
        rw [h8] at h7
        exact le_trans h6 h7
      exact ⟨by linarith [abs_le.mp h4], by linarith [abs_le.mp h4]⟩
    let φ : ℝ → ℝ := fun z => z + 2 * Real.pi * r / R
    let s' : Finset ℝ := s.image φ
    have hφ_inj : Set.InjOn φ (s : Set ℝ) := by intro z1 _ z2 _ h; simpa [φ] using h
    have h_card_s' : s'.card = s.card := by rw [Finset.card_image_of_injOn hφ_inj]
    have h_lo : ∀ z ∈ s', 0 ≤ z := by
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨w, hw, rfl⟩
      rcases Finset.mem_image.mp hw with ⟨p, _, rfl⟩
      have h7 : -(2 * Real.pi * r / R) ≤ ψ p := (hψ_bounds p).1
      have h9 : 0 ≤ ψ p + 2 * Real.pi * r / R := by linarith
      simpa [φ] using h9
    have h_hi : ∀ z ∈ s', z ≤ 4 * Real.pi * r / R := by
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨w, hw, rfl⟩
      rcases Finset.mem_image.mp hw with ⟨p, _, rfl⟩
      have h7 : ψ p ≤ 2 * Real.pi * r / R := (hψ_bounds p).2
      have h_nonneg : 0 ≤ 2 * Real.pi * r / R := by positivity
      have h9 : ψ p + 2 * Real.pi * r / R ≤ 4 * Real.pi * r / R := by
        calc ψ p + 2 * Real.pi * r / R
          ≤ 2 * Real.pi * r / R + 2 * Real.pi * r / R := by gcongr
        _ = 4 * Real.pi * r / R := by ring
      simpa [φ] using h9
    have h_sep_s' : ∀ z1 ∈ s', ∀ z2 ∈ s', z1 ≠ z2 → |z1 - z2| ≥ r / (4 * R) := by
      intro z1 hz1 z2 hz2 hne
      rcases Finset.mem_image.mp hz1 with ⟨w1, hw1, rfl⟩
      rcases Finset.mem_image.mp hz2 with ⟨w2, hw2, rfl⟩
      have hne2 : w1 ≠ w2 := by intro h; apply hne; simp [h]
      rcases Finset.mem_image.mp hw1 with ⟨p1, _, rfl⟩
      rcases Finset.mem_image.mp hw2 with ⟨p2, _, rfl⟩
      have hne3 : p1 ≠ p2 := by intro h; apply hne2; rw [h]
      have hℓ1T : p1.val ∈ T := hT'_sub p1.property
      have hℓ2T : p2.val ∈ T := hT'_sub p2.property
      have h_sep' : submoduleDirDist p1.val.direction p2.val.direction ≥ r / (4 * R) :=
        h_sep p1.val hℓ1T p2.val hℓ2T (by exact_mod_cast hne3)
      have h11 : |Real.sin (ψ p1 - ψ p2)| =
          |Real.sin (directionAngle p1.val.direction (h_lines p1.val hℓ1T).2 -
            directionAngle p2.val.direction (h_lines p2.val hℓ2T).2)| := by
        have h_simp : ψ p1 - ψ p2 =
            modPiHalf (directionAngle p1.val.direction (h_lines p1.val hℓ1T).2 - θ0) -
            modPiHalf (directionAngle p2.val.direction (h_lines p2.val hℓ2T).2 - θ0) := by rfl
        rw [h_simp]
        have h := abs_sin_sub_modPiHalf
          (directionAngle p1.val.direction (h_lines p1.val hℓ1T).2 - θ0)
          (directionAngle p2.val.direction (h_lines p2.val hℓ2T).2 - θ0)
        have h_alg : (directionAngle p1.val.direction (h_lines p1.val hℓ1T).2 - θ0) -
            (directionAngle p2.val.direction (h_lines p2.val hℓ2T).2 - θ0) =
            directionAngle p1.val.direction (h_lines p1.val hℓ1T).2 -
            directionAngle p2.val.direction (h_lines p2.val hℓ2T).2 := by ring
        rw [h_alg] at h; exact h
      have h12 : |Real.sin (directionAngle p1.val.direction (h_lines p1.val hℓ1T).2 -
          directionAngle p2.val.direction (h_lines p2.val hℓ2T).2)| =
          submoduleDirDist p1.val.direction p2.val.direction := by
        rw [dirDist_eq_abs_sin p1.val.direction p2.val.direction
          (h_lines p1.val hℓ1T).2 (h_lines p2.val hℓ2T).2] <;> rfl
      have h13 : |Real.sin (ψ p1 - ψ p2)| ≥ r / (4 * R) := by
        rw [h11, h12] <;> exact h_sep'
      have h14 : |ψ p1 - ψ p2| ≤ Real.pi := by
        have h15 : |ψ p1| ≤ 2 * Real.pi * r / R :=
          abs_le.mpr ⟨(hψ_bounds p1).1, (hψ_bounds p1).2⟩
        have h16 : |ψ p2| ≤ 2 * Real.pi * r / R :=
          abs_le.mpr ⟨(hψ_bounds p2).1, (hψ_bounds p2).2⟩
        calc |ψ p1 - ψ p2|
          ≤ |ψ p1| + |ψ p2| := abs_sub _ _
        _ ≤ 2 * Real.pi * r / R + |ψ p2| := by gcongr
        _ ≤ 2 * Real.pi * r / R + 2 * Real.pi * r / R := by gcongr
        _ = 4 * Real.pi * r / R := by ring
        _ ≤ Real.pi := by
          have h17 : 4 * Real.pi * r / R ≤ Real.pi := by
            have h18 : r / R ≤ 1 / 4 := h_r_div_R
            calc 4 * Real.pi * r / R
              = 4 * Real.pi * (r / R) := by ring
            _ ≤ 4 * Real.pi * (1 / 4) := by gcongr
            _ = Real.pi := by ring
          exact h17
      have h17 : |Real.sin (ψ p1 - ψ p2)| ≤ |ψ p1 - ψ p2| := Real.abs_sin_le_abs
      have h21 : |φ (ψ p1) - φ (ψ p2)| = |ψ p1 - ψ p2| := by simp [φ] <;> abel
      rw [h21]; exact le_trans h13 h17
    have h_pack := real_packing_simple (show 0 < r / (4 * R) by positivity)
      (show 0 ≤ 4 * Real.pi * r / R by positivity) h_lo h_hi h_sep_s'
    rw [h_card_s', h_card_s] at h_pack
    have h_final : (T'.card : ℝ) ≤ 16 * Real.pi + 1 := by
      have h22 : (T'.card : ℝ) ≤ (4 * Real.pi * r / R) / (r / (4 * R)) + 1 := by
        have h23 : T'.card ≤ Nat.floor ((4 * Real.pi * r / R) / (r / (4 * R))) + 1 := h_pack
        have h241 : 0 ≤ (4 * Real.pi * r / R) / (r / (4 * R)) := by positivity
        have h24 : (Nat.floor ((4 * Real.pi * r / R) / (r / (4 * R))) : ℝ) ≤
            (4 * Real.pi * r / R) / (r / (4 * R)) := Nat.floor_le h241
        have h23' : (T'.card : ℝ) ≤ (Nat.floor ((4 * Real.pi * r / R) / (r / (4 * R))) : ℝ) + 1 := by
          exact_mod_cast h23
        calc (T'.card : ℝ)
          ≤ (Nat.floor ((4 * Real.pi * r / R) / (r / (4 * R))) : ℝ) + 1 := h23'
        _ ≤ (4 * Real.pi * r / R) / (r / (4 * R)) + 1 := by gcongr
      have h25 : (4 * Real.pi * r / R) / (r / (4 * R)) = 16 * Real.pi := by
        field_simp [hr.ne', hR.ne'] <;> ring
      rw [h25] at h22; exact h22
    have h_pi_le_four : Real.pi ≤ 4 := Real.pi_le_four
    have h26 : (T'.card : ℝ) ≤ 65 := by linarith
    have h27 : T'.card ≤ 65 := by exact_mod_cast h26
    exact le_trans h27 (by norm_num)
  · -- Case 2: r > R/4
    have hR4_lt : 1 / 16 < r / (4 * R) := by
      have h1 : R / 4 < r := by linarith
      have h2 : (R / 4) / (4 * R) < r / (4 * R) := by gcongr
      have h3 : (R / 4) / (4 * R) = 1 / 16 := by
        field_simp [hR.ne'] <;> ring
      rw [h3] at h2; exact h2
    let φ : ℝ → ℝ := fun z => z + Real.pi / 2
    let s' : Finset ℝ := s.image φ
    have hφ_inj : Set.InjOn φ (s : Set ℝ) := by intro z1 _ z2 _ h; simpa [φ] using h
    have h_card_s' : s'.card = s.card := by rw [Finset.card_image_of_injOn hφ_inj]
    have h_lo : ∀ z ∈ s', 0 ≤ z := by
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨w, hw, rfl⟩
      rcases Finset.mem_image.mp hw with ⟨p, _, rfl⟩
      have h7 : -(Real.pi / 2) ≤ ψ p := by
        have h8 : |ψ p| ≤ Real.pi / 2 := hψ_abs_pi2 p
        exact (abs_le.mp h8).1
      have h9 : 0 ≤ ψ p + Real.pi / 2 := by linarith
      simpa [φ] using h9
    have h_hi : ∀ z ∈ s', z ≤ Real.pi := by
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨w, hw, rfl⟩
      rcases Finset.mem_image.mp hw with ⟨p, _, rfl⟩
      have h7 : ψ p ≤ Real.pi / 2 := by
        have h8 : |ψ p| ≤ Real.pi / 2 := hψ_abs_pi2 p
        exact (abs_le.mp h8).2
      simpa [φ] using by linarith
    have h_sep_s' : ∀ z1 ∈ s', ∀ z2 ∈ s', z1 ≠ z2 → |z1 - z2| ≥ 1 / 16 := by
      intro z1 hz1 z2 hz2 hne
      rcases Finset.mem_image.mp hz1 with ⟨w1, hw1, rfl⟩
      rcases Finset.mem_image.mp hz2 with ⟨w2, hw2, rfl⟩
      have hne2 : w1 ≠ w2 := by intro h; apply hne; simp [h]
      rcases Finset.mem_image.mp hw1 with ⟨p1, _, rfl⟩
      rcases Finset.mem_image.mp hw2 with ⟨p2, _, rfl⟩
      have hne3 : p1 ≠ p2 := by intro h; apply hne2; rw [h]
      have hℓ1T : p1.val ∈ T := hT'_sub p1.property
      have hℓ2T : p2.val ∈ T := hT'_sub p2.property
      have h_sep' : submoduleDirDist p1.val.direction p2.val.direction ≥ r / (4 * R) :=
        h_sep p1.val hℓ1T p2.val hℓ2T (by exact_mod_cast hne3)
      have h11 : |Real.sin (ψ p1 - ψ p2)| =
          |Real.sin (directionAngle p1.val.direction (h_lines p1.val hℓ1T).2 -
            directionAngle p2.val.direction (h_lines p2.val hℓ2T).2)| := by
        have h_simp : ψ p1 - ψ p2 =
            modPiHalf (directionAngle p1.val.direction (h_lines p1.val hℓ1T).2 - θ0) -
            modPiHalf (directionAngle p2.val.direction (h_lines p2.val hℓ2T).2 - θ0) := by rfl
        rw [h_simp]
        have h := abs_sin_sub_modPiHalf
          (directionAngle p1.val.direction (h_lines p1.val hℓ1T).2 - θ0)
          (directionAngle p2.val.direction (h_lines p2.val hℓ2T).2 - θ0)
        have h_alg : (directionAngle p1.val.direction (h_lines p1.val hℓ1T).2 - θ0) -
            (directionAngle p2.val.direction (h_lines p2.val hℓ2T).2 - θ0) =
            directionAngle p1.val.direction (h_lines p1.val hℓ1T).2 -
            directionAngle p2.val.direction (h_lines p2.val hℓ2T).2 := by ring
        rw [h_alg] at h; exact h
      have h12 : |Real.sin (directionAngle p1.val.direction (h_lines p1.val hℓ1T).2 -
          directionAngle p2.val.direction (h_lines p2.val hℓ2T).2)| =
          submoduleDirDist p1.val.direction p2.val.direction := by
        rw [dirDist_eq_abs_sin p1.val.direction p2.val.direction
          (h_lines p1.val hℓ1T).2 (h_lines p2.val hℓ2T).2] <;> rfl
      have h13 : |Real.sin (ψ p1 - ψ p2)| ≥ r / (4 * R) := by
        rw [h11, h12] <;> exact h_sep'
      have h17 : |Real.sin (ψ p1 - ψ p2)| ≤ |ψ p1 - ψ p2| := Real.abs_sin_le_abs
      have h21 : |φ (ψ p1) - φ (ψ p2)| = |ψ p1 - ψ p2| := by simp [φ] <;> abel
      have h22 : |φ (ψ p1) - φ (ψ p2)| ≥ r / (4 * R) := by
        rw [h21]; exact le_trans h13 h17
      have h23 : r / (4 * R) > 1 / 16 := hR4_lt
      have h24 : 1 / 16 ≤ |φ (ψ p1) - φ (ψ p2)| := le_of_lt (lt_of_lt_of_le h23 h22)
      exact h24
    have h_pack := real_packing_simple (show (0 : ℝ) < 1 / 16 by norm_num)
      (show (0 : ℝ) ≤ Real.pi by positivity) h_lo h_hi h_sep_s'
    rw [h_card_s', h_card_s] at h_pack
    have h_final : (T'.card : ℝ) ≤ 16 * Real.pi + 1 := by
      have h22 : (T'.card : ℝ) ≤ Real.pi / (1 / 16 : ℝ) + 1 := by
        have h23 : T'.card ≤ Nat.floor (Real.pi / (1 / 16 : ℝ)) + 1 := h_pack
        have h241 : 0 ≤ Real.pi / (1 / 16 : ℝ) := by positivity
        have h24 : (Nat.floor (Real.pi / (1 / 16 : ℝ)) : ℝ) ≤ Real.pi / (1 / 16 : ℝ) :=
          Nat.floor_le h241
        have h23' : (T'.card : ℝ) ≤ (Nat.floor (Real.pi / (1 / 16 : ℝ)) : ℝ) + 1 := by
          exact_mod_cast h23
        calc (T'.card : ℝ)
          ≤ (Nat.floor (Real.pi / (1 / 16 : ℝ)) : ℝ) + 1 := h23'
        _ ≤ Real.pi / (1 / 16 : ℝ) + 1 := by gcongr
      have h25 : Real.pi / (1 / 16 : ℝ) = 16 * Real.pi := by ring
      rw [h25] at h22; exact h22
    have h_pi_le_four : Real.pi ≤ 4 := Real.pi_le_four
    have h26 : (T'.card : ℝ) ≤ 65 := by linarith
    have h27 : T'.card ≤ 65 := by exact_mod_cast h26
    exact le_trans h27 (by norm_num)

/-- Generalized version of `concentrated_H'_fiber_lower`: works with direction
    separation `r/(4*R)` and minimum distance `R`, using the generalized overlap lemma. -/
lemma concentrated_H'_fiber_lower_general
    (ν₂ : Measure Point) [IsProbabilityMeasure ν₂]
    (G : Set (Point × Point)) (hG_meas : MeasurableSet G)
    (r R κ σ τ threshold : ℝ)
    (hr : 0 < r) (hR : 0 < R) (hκ_pos : 0 < Real.rpow r κ) (hthreshold_nonneg : 0 ≤ threshold)
    (hthreshold_lt : threshold < (1 / 3 : ℝ) * Real.rpow r (σ + 3 * τ))
    (x : Point) (T_x T_conc : Finset (AffineSubspace ℝ Point))
    (Y_x : Set Point) (hY_meas : MeasurableSet Y_x)
    (h_lines : ∀ ℓ ∈ T_x, x ∈ (ℓ : Set Point) ∧ Module.finrank ℝ ℓ.direction = 1)
    (hY_sub_G : Y_x ⊆ {b₂ | (x, b₂) ∈ G})
    (h_mass_lower : ∀ ℓ ∈ T_x,
      ENNReal.ofReal (Real.rpow r (σ + 3 * τ)) ≤ ν₂ (Metric.thickening r (ℓ : Set Point) ∩ Y_x))
    (h_sep : ∀ ℓ1 ∈ T_x, ∀ ℓ2 ∈ T_x, ℓ1 ≠ ℓ2 →
      submoduleDirDist ℓ1.direction ℓ2.direction ≥ r / (4 * R))
    (hTconc_sub : T_conc ⊆ T_x)
    (h_half : 2 * T_conc.card ≥ T_x.card)
    (h_conc : ∀ ℓ ∈ T_conc, IsConcentrated ν₂ Y_x (Metric.thickening r (ℓ : Set Point)) r κ)
    (hY_sub_G : Y_x ⊆ {b₂ | (x, b₂) ∈ G})
    (y_dist : ∀ (z : Point), z ∈ Y_x → dist x z ≥ R) :
    ν₂ ({y : Point | (x, y) ∈ ConcentratedH' ν₂ G r κ threshold} ∩ {b₂ | (x, b₂) ∈ G}) ≥
      ENNReal.ofReal ((T_conc.card : ℝ) * Real.rpow r (σ + 3 * τ) / 198) := by
  classical
  choose c hc using fun ℓ hℓ => h_conc ℓ hℓ
  let c_total (ℓ : AffineSubspace ℝ Point) : Point :=
    if h : ℓ ∈ T_conc then c ℓ h else (0 : Point)
  let A (ℓ : AffineSubspace ℝ Point) : Set Point :=
    Metric.thickening r (ℓ : Set Point) ∩ Metric.ball (c_total ℓ) (Real.rpow r κ) ∩ Y_x
  have hc_total : ∀ (ℓ : AffineSubspace ℝ Point), ∀ (hℓ : ℓ ∈ T_conc),
      c_total ℓ = c ℓ hℓ := by
    intro ℓ hℓ
    simp [c_total, hℓ]
  have hA_meas : ∀ ℓ ∈ T_conc, MeasurableSet (A ℓ) := by
    intro ℓ _
    exact (Metric.isOpen_thickening.measurableSet).inter
      (isOpen_ball.measurableSet) |>.inter hY_meas
  have hA_mass : ∀ ℓ ∈ T_conc,
      ν₂ (A ℓ) ≥ ENNReal.ofReal ((1 / 3 : ℝ) * Real.rpow r (σ + 3 * τ)) := by
    intro ℓ hℓ
    have hct : c_total ℓ = c ℓ hℓ := hc_total ℓ hℓ
    have hA_eq : A ℓ = Metric.thickening r (ℓ : Set Point) ∩
        Metric.ball (c ℓ hℓ) (Real.rpow r κ) ∩ Y_x := by
      unfold A
      rw [hct] <;> rfl
    rw [hA_eq]
    have h2 : ν₂ (Metric.thickening r (ℓ : Set Point) ∩
          Metric.ball (c ℓ hℓ) (Real.rpow r κ) ∩ Y_x) ≥
        (1 / 3 : ENNReal) * ν₂ (Metric.thickening r (ℓ : Set Point) ∩ Y_x) :=
      hc ℓ hℓ
    have h1 : ν₂ (Metric.thickening r (ℓ : Set Point) ∩ Y_x) ≥
        ENNReal.ofReal (Real.rpow r (σ + 3 * τ)) := h_mass_lower ℓ (hTconc_sub hℓ)
    have h3 : (1 / 3 : ENNReal) * ν₂ (Metric.thickening r (ℓ : Set Point) ∩ Y_x) ≥
        (1 / 3 : ENNReal) * ENNReal.ofReal (Real.rpow r (σ + 3 * τ)) := by
      gcongr
    have h4 : (1 / 3 : ENNReal) * ENNReal.ofReal (Real.rpow r (σ + 3 * τ)) =
        ENNReal.ofReal ((1 / 3 : ℝ) * Real.rpow r (σ + 3 * τ)) := by
      have h41 : ENNReal.ofReal ((1 / 3 : ℝ) * Real.rpow r (σ + 3 * τ)) =
          ENNReal.ofReal (1 / 3 : ℝ) * ENNReal.ofReal (Real.rpow r (σ + 3 * τ)) := by
        rw [ENNReal.ofReal_mul (by positivity)]
      rw [h41]
      have h42 : ENNReal.ofReal (1 / 3 : ℝ) = (1 / 3 : ENNReal) := by
        have h : ENNReal.ofReal ((1 : ℝ) / 3) = ENNReal.ofReal (1 : ℝ) / ENNReal.ofReal (3 : ℝ) :=
          ENNReal.ofReal_div_of_pos (by norm_num)
        rw [h]
        have h2 : ENNReal.ofReal (1 : ℝ) = (1 : ENNReal) := by simp
        have h3 : ENNReal.ofReal (3 : ℝ) = (3 : ENNReal) := by simp
        rw [h2, h3] <;> rfl
      rw [h42] <;> ring
    rw [h4] at h3
    exact le_trans h3 h2
  have hA_sub_H' : ∀ ℓ ∈ T_conc, A ℓ ⊆ {y : Point | (x, y) ∈ ConcentratedH' ν₂ G r κ threshold} := by
    intro ℓ hℓ y hy
    have h6 : y ∈ Metric.thickening r (ℓ : Set Point) ∩ Metric.ball (c_total ℓ) (Real.rpow r κ) := hy.1
    have h7 : y ∈ Y_x := hy.2
    rcases exists_normal_of_affineSubspace x ℓ (h_lines ℓ (hTconc_sub hℓ)).1
        (h_lines ℓ (hTconc_sub hℓ)).2 with ⟨n, hℓ_eq⟩
    have h10 : tubeOfNormal r x n = Metric.thickening r (ℓ : Set Point) := by
      rw [hℓ_eq]
      exact tubeOfNormal_eq_thickening r hr x n
    have h11 : A ℓ ⊆ Metric.thickening r (ℓ : Set Point) ∩ Metric.ball (c_total ℓ) (Real.rpow r κ) ∩
          {b₂ | (x, b₂) ∈ G} := by
      intro z hz
      exact ⟨⟨hz.1.1, hz.1.2⟩, hY_sub_G hz.2⟩
    have h12 : ν₂ (Metric.thickening r (ℓ : Set Point) ∩ Metric.ball (c_total ℓ) (Real.rpow r κ) ∩
          {b₂ | (x, b₂) ∈ G}) ≥ ν₂ (A ℓ) := measure_mono h11
    have h13 : ν₂ (A ℓ) ≥ ENNReal.ofReal ((1 / 3 : ℝ) * Real.rpow r (σ + 3 * τ)) := hA_mass ℓ hℓ
    have h14 : ENNReal.ofReal ((1 / 3 : ℝ) * Real.rpow r (σ + 3 * τ)) > ENNReal.ofReal threshold := by
      have h141 : 0 ≤ threshold := hthreshold_nonneg
      have h142 : 0 ≤ (1 / 3 : ℝ) * Real.rpow r (σ + 3 * τ) := by
        have h : 0 ≤ Real.rpow r (σ + 3 * τ) := Real.rpow_nonneg (by linarith) _
        exact mul_nonneg (by norm_num) h
      have h_iff : ENNReal.ofReal threshold ≤ ENNReal.ofReal ((1 / 3 : ℝ) * Real.rpow r (σ + 3 * τ)) ↔
          threshold ≤ (1 / 3 : ℝ) * Real.rpow r (σ + 3 * τ) :=
        ENNReal.ofReal_le_ofReal_iff h142
      have h_le : threshold ≤ (1 / 3 : ℝ) * Real.rpow r (σ + 3 * τ) := by linarith
      have h_ne : ENNReal.ofReal threshold ≠ ENNReal.ofReal ((1 / 3 : ℝ) * Real.rpow r (σ + 3 * τ)) := by
        intro h
        have h_iff2 : ENNReal.ofReal threshold = ENNReal.ofReal ((1 / 3 : ℝ) * Real.rpow r (σ + 3 * τ)) ↔
            threshold = (1 / 3 : ℝ) * Real.rpow r (σ + 3 * τ) :=
          ENNReal.ofReal_eq_ofReal_iff h141 h142
        have h_eq : threshold = (1 / 3 : ℝ) * Real.rpow r (σ + 3 * τ) := h_iff2.mp h
        linarith
      exact (h_iff.mpr h_le).lt_of_ne h_ne
    have h15 : ν₂ (Metric.thickening r (ℓ : Set Point) ∩ Metric.ball (c_total ℓ) (Real.rpow r κ) ∩
          {b₂ | (x, b₂) ∈ G}) > ENNReal.ofReal threshold :=
      lt_of_lt_of_le h14 (le_trans h13 h12)
    have h15' : ν₂ (tubeOfNormal r x n ∩ Metric.ball (c_total ℓ) (Real.rpow r κ) ∩
          {b₂ | (x, b₂) ∈ G}) > ENNReal.ofReal threshold := by
      rw [h10]
      exact h15
    have h18 : y ∈ tubeOfNormal r x n := by
      rw [h10]
      exact h6.1
    have h16 : y ∈ tubeOfNormal r x n ∩ Metric.ball (c_total ℓ) (Real.rpow r κ) :=
      ⟨h18, h6.2⟩
    exact ⟨n, c_total ℓ, h15', h16⟩
  let U : Set Point := ⋃ ℓ ∈ T_conc, A ℓ
  have hU_meas : MeasurableSet U :=
    Finset.measurableSet_biUnion T_conc hA_meas
  have hU_sub : U ⊆ {y : Point | (x, y) ∈ ConcentratedH' ν₂ G r κ threshold} := by
    intro y hy
    rcases Set.mem_iUnion₂.mp hy with ⟨ℓ, hℓ, hyA⟩
    exact hA_sub_H' ℓ hℓ hyA
  have h_overlap : ∀ y : Point, (T_conc.filter (fun ℓ => y ∈ A ℓ)).card ≤ 66 := by
    intro y
    by_cases hyY : y ∈ Y_x
    · let S : Finset (AffineSubspace ℝ Point) :=
        T_conc.filter (fun (ℓ : AffineSubspace ℝ Point) => y ∈ Metric.thickening r (ℓ : Set Point))
      have hS1 : (T_conc.filter (fun ℓ => y ∈ A ℓ)) ⊆ S := by
        intro ℓ hℓ
        have h3 : ℓ ∈ T_conc := (Finset.mem_filter.mp hℓ).1
        have h2 : y ∈ A ℓ := (Finset.mem_filter.mp hℓ).2
        have h4 : y ∈ Metric.thickening r (ℓ : Set Point) := h2.1.1
        exact Finset.mem_filter.mpr ⟨h3, h4⟩
      have hS2 : S.card ≤ 66 := by
        dsimp only [S]
        exact source_tubes_bounded_overlap_general x r R hr hR T_conc
          (fun ℓ hℓ => h_lines ℓ (hTconc_sub hℓ))
          (fun ℓ1 hℓ1 ℓ2 hℓ2 hne => h_sep ℓ1 (hTconc_sub hℓ1) ℓ2 (hTconc_sub hℓ2) hne)
          y (y_dist y hyY)
      exact le_trans (Finset.card_le_card hS1) hS2
    · have h5 : (T_conc.filter (fun ℓ => y ∈ A ℓ)) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro ℓ _ h6
        exact hyY h6.2
      rw [h5] <;> simp
  have h_sum_eq : ∑ ℓ ∈ T_conc, ν₂ (A ℓ) =
      ∫⁻ y, ↑((T_conc.filter (fun ℓ => y ∈ A ℓ)).card) ∂ν₂ := by
    have h1 : ∀ ℓ ∈ T_conc, ν₂ (A ℓ) =
        ∫⁻ y, Set.indicator (A ℓ) (fun _ : Point => (1 : ENNReal)) y ∂ν₂ := by
      intro ℓ hℓ
      have h2 : ∫⁻ y, Set.indicator (A ℓ) (fun _ : Point => (1 : ENNReal)) y ∂ν₂ = ν₂ (A ℓ) := by
        rw [MeasureTheory.lintegral_indicator (hA_meas ℓ hℓ)]
        have h3 : ∫⁻ y, (1 : ENNReal) ∂(ν₂.restrict (A ℓ)) = ν₂ (A ℓ) := by simp
        exact h3
      exact h2.symm
    calc
      ∑ ℓ ∈ T_conc, ν₂ (A ℓ)
        = ∑ ℓ ∈ T_conc, ∫⁻ y, Set.indicator (A ℓ) (fun _ : Point => (1 : ENNReal)) y ∂ν₂ := by
          apply Finset.sum_congr rfl; intro ℓ hℓ; exact h1 ℓ hℓ
      _ = ∫⁻ y, ∑ ℓ ∈ T_conc, Set.indicator (A ℓ) (fun _ : Point => (1 : ENNReal)) y ∂ν₂ := by
          have h_ind_meas : ∀ ℓ ∈ T_conc, Measurable (Set.indicator (A ℓ) (fun _ : Point => (1 : ENNReal))) :=
            fun ℓ hℓ => measurable_const.indicator (hA_meas ℓ hℓ)
          exact (MeasureTheory.lintegral_finsetSum T_conc h_ind_meas).symm
      _ = ∫⁻ y, ↑((T_conc.filter (fun ℓ => y ∈ A ℓ)).card) ∂ν₂ := by
          have h_pointwise : ∀ (y : Point), ∑ ℓ ∈ T_conc, Set.indicator (A ℓ) (fun _ : Point => (1 : ENNReal)) y =
              ↑((T_conc.filter (fun ℓ => y ∈ A ℓ)).card) := by
            intro y
            have h_eq1 : ∑ ℓ ∈ T_conc, Set.indicator (A ℓ) (fun _ : Point => (1 : ENNReal)) y =
                ∑ ℓ ∈ T_conc, (if y ∈ A ℓ then (1 : ENNReal) else 0) := by
              apply Finset.sum_congr rfl
              intro ℓ _
              simp [Set.indicator_apply] <;> split_ifs <;> simp
            rw [h_eq1, Finset.sum_boole]
            <;> simp
          congr with y
          exact h_pointwise y
  have h_overlap_indicator : ∀ (y : Point),
      ↑((T_conc.filter (fun ℓ => y ∈ A ℓ)).card) ≤
      (66 : ENNReal) * Set.indicator U (fun _ => (1 : ENNReal)) y := by
    intro y
    by_cases hyU : y ∈ U
    · have h3 : ↑((T_conc.filter (fun ℓ => y ∈ A ℓ)).card) ≤ (66 : ENNReal) := by
        exact_mod_cast h_overlap y
      have h4 : Set.indicator U (fun _ => (1 : ENNReal)) y = 1 := by
        rw [Set.indicator_of_mem hyU] <;> simp
      rw [h4] <;> simpa using h3
    · have h5 : (T_conc.filter (fun ℓ => y ∈ A ℓ)) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro ℓ hℓ h6
        have h7 : y ∈ U := Set.mem_iUnion₂.mpr ⟨ℓ, hℓ, h6⟩
        exact hyU h7
      rw [h5]
      <;> simp [Set.indicator_apply, hyU] <;> norm_num
  have h_sum : ∑ ℓ ∈ T_conc, ν₂ (A ℓ) ≤ (66 : ENNReal) * ν₂ U := by
    calc
      ∑ ℓ ∈ T_conc, ν₂ (A ℓ)
        = ∫⁻ y, ↑((T_conc.filter (fun ℓ => y ∈ A ℓ)).card) ∂ν₂ := h_sum_eq
      _ ≤ ∫⁻ y, (66 : ENNReal) * Set.indicator U (fun _ => (1 : ENNReal)) y ∂ν₂ := by
          apply lintegral_mono; exact h_overlap_indicator
      _ = (66 : ENNReal) * ν₂ U := by
          have h_cmul : ∫⁻ y, (66 : ENNReal) * Set.indicator U (fun _ => (1 : ENNReal)) y ∂ν₂ =
              (66 : ENNReal) * ∫⁻ y, Set.indicator U (fun _ => (1 : ENNReal)) y ∂ν₂ := by
            apply MeasureTheory.lintegral_const_mul (66 : ENNReal) (hf := measurable_const.indicator hU_meas)
          rw [h_cmul]
          have h_ind_U : ∫⁻ a, Set.indicator U (fun _ => (1 : ENNReal)) a ∂ν₂ = ν₂ U := by
            rw [MeasureTheory.lintegral_indicator hU_meas]
            have h : ∫⁻ a, (1 : ENNReal) ∂(ν₂.restrict U) = ν₂ U := by simp
            exact h
          rw [h_ind_U]
  have h_lower_sum : ∑ ℓ ∈ T_conc, ν₂ (A ℓ) ≥
      (T_conc.card : ENNReal) * ENNReal.ofReal ((1 / 3 : ℝ) * Real.rpow r (σ + 3 * τ)) := by
    calc
      ∑ ℓ ∈ T_conc, ν₂ (A ℓ)
        ≥ ∑ ℓ ∈ T_conc, ENNReal.ofReal ((1 / 3 : ℝ) * Real.rpow r (σ + 3 * τ)) :=
          Finset.sum_le_sum fun ℓ hℓ => hA_mass ℓ hℓ
      _ = (T_conc.card : ENNReal) * ENNReal.ofReal ((1 / 3 : ℝ) * Real.rpow r (σ + 3 * τ)) := by
        simp [Finset.sum_const] <;> ring
  have h_main : ν₂ U ≥
      (T_conc.card : ENNReal) * ENNReal.ofReal ((1 / 3 : ℝ) * Real.rpow r (σ + 3 * τ)) / 66 := by
    have h_div : (∑ ℓ ∈ T_conc, ν₂ (A ℓ)) ≤ (66 : ENNReal) * ν₂ U := h_sum
    have h : (∑ ℓ ∈ T_conc, ν₂ (A ℓ)) / 66 ≤ ν₂ U := by
      have h9 : (∑ ℓ ∈ T_conc, ν₂ (A ℓ)) / 66 ≤ ((66 : ENNReal) * ν₂ U) / 66 := by gcongr
      have h10 : ((66 : ENNReal) * ν₂ U) / 66 = ν₂ U := by
        rw [mul_comm (66 : ENNReal) (ν₂ U)]
        have h66_ne_zero : (66 : ENNReal) ≠ 0 := by simp
        have h66_ne_top : (66 : ENNReal) ≠ ⊤ := by simp
        exact ENNReal.mul_div_cancel_right h66_ne_zero h66_ne_top
      rw [h10] at h9
      exact h9
    calc
      ν₂ U
        ≥ (∑ ℓ ∈ T_conc, ν₂ (A ℓ)) / 66 := h
      _ ≥ ((T_conc.card : ENNReal) * ENNReal.ofReal ((1 / 3 : ℝ) * Real.rpow r (σ + 3 * τ))) / 66 := by
          gcongr
  have h_ennreal_eq : ((T_conc.card : ENNReal) * ENNReal.ofReal ((1 / 3 : ℝ) * Real.rpow r (σ + 3 * τ))) / 66 =
      ENNReal.ofReal ((T_conc.card : ℝ) * Real.rpow r (σ + 3 * τ) / 198) := by
    have h_rpow_nonneg : 0 ≤ Real.rpow r (σ + 3 * τ) :=
      Real.rpow_nonneg hr.le (σ + 3 * τ)
    have h_card_nonneg : 0 ≤ (T_conc.card : ℝ) := by positivity
    set a : ℝ := (1 / 3 : ℝ) * Real.rpow r (σ + 3 * τ) with ha_def
    have ha_nonneg : 0 ≤ a := by positivity
    set b : ℝ := (T_conc.card : ℝ) * a with hb_def
    have hb_nonneg : 0 ≤ b := by positivity
    have h1 : (T_conc.card : ENNReal) * ENNReal.ofReal a = ENNReal.ofReal ((T_conc.card : ℝ) * a) := by
      have h : ENNReal.ofReal ((T_conc.card : ℝ) * a) =
          ENNReal.ofReal (T_conc.card : ℝ) * ENNReal.ofReal a := by
        rw [ENNReal.ofReal_mul] <;> positivity
      rw [h] <;> simp
    have h2 : ENNReal.ofReal b / 66 = ENNReal.ofReal (b / 66) := by
      rw [ENNReal.ofReal_div_of_pos (x := b) (by norm_num)] <;> simp
    have h_real_eq : b / 66 = (T_conc.card : ℝ) * Real.rpow r (σ + 3 * τ) / 198 := by
      simp only [b, a, ha_def] <;> ring
    calc
      ((T_conc.card : ENNReal) * ENNReal.ofReal a) / 66
        = ENNReal.ofReal b / 66 := by rw [h1, hb_def]
      _ = ENNReal.ofReal (b / 66) := h2
      _ = ENNReal.ofReal ((T_conc.card : ℝ) * Real.rpow r (σ + 3 * τ) / 198) := by rw [h_real_eq]
  have h_final : ν₂ U ≥ ENNReal.ofReal ((T_conc.card : ℝ) * Real.rpow r (σ + 3 * τ) / 198) := by
    rw [h_ennreal_eq] at h_main
    exact h_main
  have hU_sub_G : U ⊆ {b₂ | (x, b₂) ∈ G} := by
    intro y hy
    rcases Set.mem_iUnion₂.mp hy with ⟨ℓ, _, hyA⟩
    have h_in_Y : y ∈ Y_x := hyA.2
    exact hY_sub_G h_in_Y
  have hU_sub' : U ⊆ {y : Point | (x, y) ∈ ConcentratedH' ν₂ G r κ threshold} ∩ {b₂ | (x, b₂) ∈ G} := by
    intro y hy
    exact ⟨hU_sub hy, hU_sub_G hy⟩
  exact le_trans h_final (measure_mono hU_sub')

/-- Mass-based H' fiber lower bound.

    Uses `HalfMassConcentrated` (mass-based) instead of cardinality-based half.
    Outputs `ν₂(H' fiber ∩ G_x) ≥ r^(2τ)/396`, which is stronger than `r^(6τ)/396`
    since `r < 1` and `2τ < 6τ`. -/
lemma concentrated_H'_fiber_lower_mass
    (ν₂ : Measure Point) [IsProbabilityMeasure ν₂]
    (G : Set (Point × Point)) (hG_meas : MeasurableSet G)
    (r R κ σ τ threshold : ℝ)
    (hr : 0 < r) (hR : 0 < R) (hκ_pos : 0 < Real.rpow r κ) (hthreshold_nonneg : 0 ≤ threshold)
    (hthreshold_lt : threshold < (1 / 3 : ℝ) * Real.rpow r (σ + 3 * τ))
    (x : Point) (T_x T_conc : Finset (AffineSubspace ℝ Point))
    (Y_x : Set Point) (hY_meas : MeasurableSet Y_x)
    (h_lines : ∀ ℓ ∈ T_x, x ∈ (ℓ : Set Point) ∧ Module.finrank ℝ ℓ.direction = 1)
    (hY_sub_G : Y_x ⊆ {b₂ | (x, b₂) ∈ G})
    (hY_sub_tubes : Y_x ⊆ ⋃ ℓ ∈ T_x, Metric.thickening r (ℓ : Set Point))
    (h_mass_lower : ∀ ℓ ∈ T_x,
      ENNReal.ofReal (Real.rpow r (σ + 3 * τ)) ≤ ν₂ (Metric.thickening r (ℓ : Set Point) ∩ Y_x))
    (h_sep : ∀ ℓ1 ∈ T_conc, ∀ ℓ2 ∈ T_conc, ℓ1 ≠ ℓ2 →
      submoduleDirDist ℓ1.direction ℓ2.direction ≥ r / (4 * R))
    (hTconc_sub : T_conc ⊆ T_x)
    (h_mass_half : 2 * ∑ ℓ ∈ T_conc, ν₂ (Metric.thickening r (ℓ : Set Point) ∩ Y_x) ≥
      ∑ ℓ ∈ T_x, ν₂ (Metric.thickening r (ℓ : Set Point) ∩ Y_x))
    (h_conc : ∀ ℓ ∈ T_conc, IsConcentrated ν₂ Y_x (Metric.thickening r (ℓ : Set Point)) r κ)
    (hY_mass : ν₂ Y_x ≥ ENNReal.ofReal (Real.rpow r (2 * τ)))
    (y_dist : ∀ (z : Point), z ∈ Y_x → dist x z ≥ R) :
    ν₂ ({y : Point | (x, y) ∈ ConcentratedH' ν₂ G r κ threshold} ∩ {b₂ | (x, b₂) ∈ G}) ≥
      ENNReal.ofReal (Real.rpow r (2 * τ) / 396) := by
  classical
  choose c hc using fun ℓ hℓ => h_conc ℓ hℓ
  let c_total (ℓ : AffineSubspace ℝ Point) : Point :=
    if h : ℓ ∈ T_conc then c ℓ h else (0 : Point)
  let A (ℓ : AffineSubspace ℝ Point) : Set Point :=
    Metric.thickening r (ℓ : Set Point) ∩ Metric.ball (c_total ℓ) (Real.rpow r κ) ∩ Y_x
  have hc_total : ∀ (ℓ : AffineSubspace ℝ Point), ∀ (hℓ : ℓ ∈ T_conc),
      c_total ℓ = c ℓ hℓ := by
    intro ℓ hℓ
    simp [c_total, hℓ]
  have hA_meas : ∀ ℓ ∈ T_conc, MeasurableSet (A ℓ) := by
    intro ℓ _
    exact (Metric.isOpen_thickening.measurableSet).inter
      (isOpen_ball.measurableSet) |>.inter hY_meas
  have hA_mass_actual : ∀ ℓ ∈ T_conc,
      ν₂ (A ℓ) ≥ (1 / 3 : ENNReal) * ν₂ (Metric.thickening r (ℓ : Set Point) ∩ Y_x) := by
    intro ℓ hℓ
    have hct : c_total ℓ = c ℓ hℓ := hc_total ℓ hℓ
    have hA_eq : A ℓ = Metric.thickening r (ℓ : Set Point) ∩
        Metric.ball (c ℓ hℓ) (Real.rpow r κ) ∩ Y_x := by
      unfold A
      rw [hct] <;> rfl
    rw [hA_eq]
    exact hc ℓ hℓ
  have hA_mass : ∀ ℓ ∈ T_conc,
      ν₂ (A ℓ) ≥ ENNReal.ofReal ((1 / 3 : ℝ) * Real.rpow r (σ + 3 * τ)) := by
    intro ℓ hℓ
    have h1 : ν₂ (A ℓ) ≥ (1 / 3 : ENNReal) * ν₂ (Metric.thickening r (ℓ : Set Point) ∩ Y_x) :=
      hA_mass_actual ℓ hℓ
    have h2 : ν₂ (Metric.thickening r (ℓ : Set Point) ∩ Y_x) ≥
        ENNReal.ofReal (Real.rpow r (σ + 3 * τ)) := h_mass_lower ℓ (hTconc_sub hℓ)
    have h3 : (1 / 3 : ENNReal) * ν₂ (Metric.thickening r (ℓ : Set Point) ∩ Y_x) ≥
        (1 / 3 : ENNReal) * ENNReal.ofReal (Real.rpow r (σ + 3 * τ)) := by gcongr
    have h4 : (1 / 3 : ENNReal) * ENNReal.ofReal (Real.rpow r (σ + 3 * τ)) =
        ENNReal.ofReal ((1 / 3 : ℝ) * Real.rpow r (σ + 3 * τ)) := by
      have h41 : ENNReal.ofReal ((1 / 3 : ℝ) * Real.rpow r (σ + 3 * τ)) =
          ENNReal.ofReal (1 / 3 : ℝ) * ENNReal.ofReal (Real.rpow r (σ + 3 * τ)) := by
        rw [ENNReal.ofReal_mul (by positivity)]
      rw [h41]
      have h42 : ENNReal.ofReal (1 / 3 : ℝ) = (1 / 3 : ENNReal) := by
        have h : ENNReal.ofReal ((1 : ℝ) / 3) = ENNReal.ofReal (1 : ℝ) / ENNReal.ofReal (3 : ℝ) :=
          ENNReal.ofReal_div_of_pos (by norm_num)
        rw [h]
        have h2 : ENNReal.ofReal (1 : ℝ) = (1 : ENNReal) := by simp
        have h3 : ENNReal.ofReal (3 : ℝ) = (3 : ENNReal) := by simp
        rw [h2, h3] <;> rfl
      rw [h42] <;> ring
    rw [h4] at h3
    exact le_trans h3 h1
  have hA_sub_H' : ∀ ℓ ∈ T_conc, A ℓ ⊆ {y : Point | (x, y) ∈ ConcentratedH' ν₂ G r κ threshold} := by
    intro ℓ hℓ y hy
    have h6 : y ∈ Metric.thickening r (ℓ : Set Point) ∩ Metric.ball (c_total ℓ) (Real.rpow r κ) := hy.1
    have h7 : y ∈ Y_x := hy.2
    rcases exists_normal_of_affineSubspace x ℓ (h_lines ℓ (hTconc_sub hℓ)).1
        (h_lines ℓ (hTconc_sub hℓ)).2 with ⟨n, hℓ_eq⟩
    have h10 : tubeOfNormal r x n = Metric.thickening r (ℓ : Set Point) := by
      rw [hℓ_eq]
      exact tubeOfNormal_eq_thickening r hr x n
    have h11 : A ℓ ⊆ Metric.thickening r (ℓ : Set Point) ∩ Metric.ball (c_total ℓ) (Real.rpow r κ) ∩
          {b₂ | (x, b₂) ∈ G} := by
      intro z hz
      exact ⟨⟨hz.1.1, hz.1.2⟩, hY_sub_G hz.2⟩
    have h12 : ν₂ (Metric.thickening r (ℓ : Set Point) ∩ Metric.ball (c_total ℓ) (Real.rpow r κ) ∩
          {b₂ | (x, b₂) ∈ G}) ≥ ν₂ (A ℓ) := measure_mono h11
    have h13 : ν₂ (A ℓ) ≥ ENNReal.ofReal ((1 / 3 : ℝ) * Real.rpow r (σ + 3 * τ)) := hA_mass ℓ hℓ
    have h14 : ENNReal.ofReal ((1 / 3 : ℝ) * Real.rpow r (σ + 3 * τ)) > ENNReal.ofReal threshold := by
      have h141 : 0 ≤ threshold := hthreshold_nonneg
      have h142 : 0 ≤ (1 / 3 : ℝ) * Real.rpow r (σ + 3 * τ) := by
        have h : 0 ≤ Real.rpow r (σ + 3 * τ) := Real.rpow_nonneg (by linarith) _
        exact mul_nonneg (by norm_num) h
      have h_iff : ENNReal.ofReal threshold ≤ ENNReal.ofReal ((1 / 3 : ℝ) * Real.rpow r (σ + 3 * τ)) ↔
          threshold ≤ (1 / 3 : ℝ) * Real.rpow r (σ + 3 * τ) :=
        ENNReal.ofReal_le_ofReal_iff h142
      have h_le : threshold ≤ (1 / 3 : ℝ) * Real.rpow r (σ + 3 * τ) := by linarith
      have h_ne : ENNReal.ofReal threshold ≠ ENNReal.ofReal ((1 / 3 : ℝ) * Real.rpow r (σ + 3 * τ)) := by
        intro h
        have h_iff2 : ENNReal.ofReal threshold = ENNReal.ofReal ((1 / 3 : ℝ) * Real.rpow r (σ + 3 * τ)) ↔
            threshold = (1 / 3 : ℝ) * Real.rpow r (σ + 3 * τ) :=
          ENNReal.ofReal_eq_ofReal_iff h141 h142
        have h_eq : threshold = (1 / 3 : ℝ) * Real.rpow r (σ + 3 * τ) := h_iff2.mp h
        linarith
      exact (h_iff.mpr h_le).lt_of_ne h_ne
    have h15 : ν₂ (Metric.thickening r (ℓ : Set Point) ∩ Metric.ball (c_total ℓ) (Real.rpow r κ) ∩
          {b₂ | (x, b₂) ∈ G}) > ENNReal.ofReal threshold :=
      lt_of_lt_of_le h14 (le_trans h13 h12)
    have h15' : ν₂ (tubeOfNormal r x n ∩ Metric.ball (c_total ℓ) (Real.rpow r κ) ∩
          {b₂ | (x, b₂) ∈ G}) > ENNReal.ofReal threshold := by
      rw [h10]; exact h15
    have h18 : y ∈ tubeOfNormal r x n := by rw [h10]; exact h6.1
    have h16 : y ∈ tubeOfNormal r x n ∩ Metric.ball (c_total ℓ) (Real.rpow r κ) :=
      ⟨h18, h6.2⟩
    exact ⟨n, c_total ℓ, h15', h16⟩
  let U : Set Point := ⋃ ℓ ∈ T_conc, A ℓ
  have hU_meas : MeasurableSet U :=
    Finset.measurableSet_biUnion T_conc hA_meas
  have hU_sub : U ⊆ {y : Point | (x, y) ∈ ConcentratedH' ν₂ G r κ threshold} := by
    intro y hy
    rcases Set.mem_iUnion₂.mp hy with ⟨ℓ, hℓ, hyA⟩
    exact hA_sub_H' ℓ hℓ hyA
  have h_overlap : ∀ y : Point, (T_conc.filter (fun ℓ => y ∈ A ℓ)).card ≤ 66 := by
    intro y
    by_cases hyY : y ∈ Y_x
    · let S : Finset (AffineSubspace ℝ Point) :=
        T_conc.filter (fun (ℓ : AffineSubspace ℝ Point) => y ∈ Metric.thickening r (ℓ : Set Point))
      have hS1 : (T_conc.filter (fun ℓ => y ∈ A ℓ)) ⊆ S := by
        intro ℓ hℓ
        have h3 : ℓ ∈ T_conc := (Finset.mem_filter.mp hℓ).1
        have h2 : y ∈ A ℓ := (Finset.mem_filter.mp hℓ).2
        have h4 : y ∈ Metric.thickening r (ℓ : Set Point) := h2.1.1
        exact Finset.mem_filter.mpr ⟨h3, h4⟩
      have hS2 : S.card ≤ 66 := by
        dsimp only [S]
        exact source_tubes_bounded_overlap_general x r R hr hR T_conc
          (fun ℓ hℓ => h_lines ℓ (hTconc_sub hℓ))
          (fun ℓ1 hℓ1 ℓ2 hℓ2 hne => h_sep ℓ1 hℓ1 ℓ2 hℓ2 hne)
          y (y_dist y hyY)
      exact le_trans (Finset.card_le_card hS1) hS2
    · have h5 : (T_conc.filter (fun ℓ => y ∈ A ℓ)) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro ℓ _ h6
        exact hyY h6.2
      rw [h5] <;> simp
  have h_sum_eq : ∑ ℓ ∈ T_conc, ν₂ (A ℓ) =
      ∫⁻ y, ↑((T_conc.filter (fun ℓ => y ∈ A ℓ)).card) ∂ν₂ := by
    have h1 : ∀ ℓ ∈ T_conc, ν₂ (A ℓ) =
        ∫⁻ y, Set.indicator (A ℓ) (fun _ : Point => (1 : ENNReal)) y ∂ν₂ := by
      intro ℓ hℓ
      have h2 : ∫⁻ y, Set.indicator (A ℓ) (fun _ : Point => (1 : ENNReal)) y ∂ν₂ = ν₂ (A ℓ) := by
        rw [MeasureTheory.lintegral_indicator (hA_meas ℓ hℓ)]
        have h3 : ∫⁻ y, (1 : ENNReal) ∂(ν₂.restrict (A ℓ)) = ν₂ (A ℓ) := by simp
        exact h3
      exact h2.symm
    calc
      ∑ ℓ ∈ T_conc, ν₂ (A ℓ)
        = ∑ ℓ ∈ T_conc, ∫⁻ y, Set.indicator (A ℓ) (fun _ : Point => (1 : ENNReal)) y ∂ν₂ := by
          apply Finset.sum_congr rfl; intro ℓ hℓ; exact h1 ℓ hℓ
      _ = ∫⁻ y, ∑ ℓ ∈ T_conc, Set.indicator (A ℓ) (fun _ : Point => (1 : ENNReal)) y ∂ν₂ := by
          have h_ind_meas : ∀ ℓ ∈ T_conc, Measurable (Set.indicator (A ℓ) (fun _ : Point => (1 : ENNReal))) :=
            fun ℓ hℓ => measurable_const.indicator (hA_meas ℓ hℓ)
          exact (MeasureTheory.lintegral_finsetSum T_conc h_ind_meas).symm
      _ = ∫⁻ y, ↑((T_conc.filter (fun ℓ => y ∈ A ℓ)).card) ∂ν₂ := by
          have h_pointwise : ∀ (y : Point), ∑ ℓ ∈ T_conc, Set.indicator (A ℓ) (fun _ : Point => (1 : ENNReal)) y =
              ↑((T_conc.filter (fun ℓ => y ∈ A ℓ)).card) := by
            intro y
            have h_eq1 : ∑ ℓ ∈ T_conc, Set.indicator (A ℓ) (fun _ : Point => (1 : ENNReal)) y =
                ∑ ℓ ∈ T_conc, (if y ∈ A ℓ then (1 : ENNReal) else 0) := by
              apply Finset.sum_congr rfl
              intro ℓ _
              simp [Set.indicator_apply] <;> split_ifs <;> simp
            rw [h_eq1, Finset.sum_boole] <;> simp
          congr with y
          exact h_pointwise y
  have h_overlap_indicator : ∀ (y : Point),
      ↑((T_conc.filter (fun ℓ => y ∈ A ℓ)).card) ≤
      (66 : ENNReal) * Set.indicator U (fun _ => (1 : ENNReal)) y := by
    intro y
    by_cases hyU : y ∈ U
    · have h3 : ↑((T_conc.filter (fun ℓ => y ∈ A ℓ)).card) ≤ (66 : ENNReal) := by
        exact_mod_cast h_overlap y
      have h4 : Set.indicator U (fun _ => (1 : ENNReal)) y = 1 := by
        rw [Set.indicator_of_mem hyU] <;> simp
      rw [h4] <;> simpa using h3
    · have h5 : (T_conc.filter (fun ℓ => y ∈ A ℓ)) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro ℓ hℓ h6
        have h7 : y ∈ U := Set.mem_iUnion₂.mpr ⟨ℓ, hℓ, h6⟩
        exact hyU h7
      rw [h5] <;> simp [Set.indicator_apply, hyU] <;> norm_num
  have h_sum : ∑ ℓ ∈ T_conc, ν₂ (A ℓ) ≤ (66 : ENNReal) * ν₂ U := by
    calc
      ∑ ℓ ∈ T_conc, ν₂ (A ℓ)
        = ∫⁻ y, ↑((T_conc.filter (fun ℓ => y ∈ A ℓ)).card) ∂ν₂ := h_sum_eq
      _ ≤ ∫⁻ y, (66 : ENNReal) * Set.indicator U (fun _ => (1 : ENNReal)) y ∂ν₂ := by
          apply lintegral_mono; exact h_overlap_indicator
      _ = (66 : ENNReal) * ν₂ U := by
          have h_cmul : ∫⁻ y, (66 : ENNReal) * Set.indicator U (fun _ => (1 : ENNReal)) y ∂ν₂ =
              (66 : ENNReal) * ∫⁻ y, Set.indicator U (fun _ => (1 : ENNReal)) y ∂ν₂ := by
            apply MeasureTheory.lintegral_const_mul (66 : ENNReal) (hf := measurable_const.indicator hU_meas)
          rw [h_cmul]
          have h_ind_U : ∫⁻ a, Set.indicator U (fun _ => (1 : ENNReal)) a ∂ν₂ = ν₂ U := by
            rw [MeasureTheory.lintegral_indicator hU_meas]
            have h : ∫⁻ a, (1 : ENNReal) ∂(ν₂.restrict U) = ν₂ U := by simp
            exact h
          rw [h_ind_U]
  -- Mass-based lower bound on the sum
  let tube_mass (ℓ : AffineSubspace ℝ Point) : ENNReal := ν₂ (Metric.thickening r (ℓ : Set Point) ∩ Y_x)
  have h_sum_lower1 : ∑ ℓ ∈ T_conc, ν₂ (A ℓ) ≥ (1 / 3 : ENNReal) * ∑ ℓ ∈ T_conc, tube_mass ℓ := by
    calc
      ∑ ℓ ∈ T_conc, ν₂ (A ℓ)
        ≥ ∑ ℓ ∈ T_conc, ((1 / 3 : ENNReal) * tube_mass ℓ) :=
          Finset.sum_le_sum fun ℓ hℓ => hA_mass_actual ℓ hℓ
      _ = (1 / 3 : ENNReal) * ∑ ℓ ∈ T_conc, tube_mass ℓ := by
        rw [Finset.mul_sum]
  have hY_cover : Y_x ⊆ ⋃ ℓ ∈ T_x, (Metric.thickening r (ℓ : Set Point) ∩ Y_x) := by
    intro y hy
    have h1 : y ∈ ⋃ ℓ ∈ T_x, Metric.thickening r (ℓ : Set Point) := hY_sub_tubes hy
    rcases Set.mem_iUnion₂.mp h1 with ⟨ℓ, hℓ, hy_tube⟩
    exact Set.mem_iUnion₂.mpr ⟨ℓ, hℓ, ⟨hy_tube, hy⟩⟩
  have h_sum_total : ∑ ℓ ∈ T_x, tube_mass ℓ ≥ ν₂ Y_x := by
    have h1 : ν₂ Y_x ≤ ν₂ (⋃ ℓ ∈ T_x, (Metric.thickening r (ℓ : Set Point) ∩ Y_x)) :=
      measure_mono hY_cover
    have h2 : ν₂ (⋃ ℓ ∈ T_x, (Metric.thickening r (ℓ : Set Point) ∩ Y_x)) ≤
        ∑ ℓ ∈ T_x, ν₂ (Metric.thickening r (ℓ : Set Point) ∩ Y_x) :=
      measure_biUnion_finset_le _ _
    exact le_trans h1 h2
  have h_sum_conc : ∑ ℓ ∈ T_conc, tube_mass ℓ ≥ (∑ ℓ ∈ T_x, tube_mass ℓ) / 2 := by
    have h : 2 * ∑ ℓ ∈ T_conc, tube_mass ℓ ≥ ∑ ℓ ∈ T_x, tube_mass ℓ := h_mass_half
    have h2 : (∑ ℓ ∈ T_x, tube_mass ℓ) / 2 ≤ (2 * ∑ ℓ ∈ T_conc, tube_mass ℓ) / 2 := by gcongr
    have h3 : (2 * ∑ ℓ ∈ T_conc, tube_mass ℓ) / 2 = ∑ ℓ ∈ T_conc, tube_mass ℓ := by
      have h4 : (2 : ENNReal) ≠ 0 := by simp
      have h5 : (2 : ENNReal) ≠ ⊤ := by simp
      have h6 : (2 * ∑ ℓ ∈ T_conc, tube_mass ℓ) / 2 = (∑ ℓ ∈ T_conc, tube_mass ℓ) * (2 : ENNReal) / 2 := by
        rw [mul_comm]
      rw [h6]
      exact ENNReal.mul_div_cancel_right h4 h5
    rw [h3] at h2
    exact h2
  have h_rpow2_pos : 0 < Real.rpow r (2 * τ) := Real.rpow_pos_of_pos hr (2 * τ)
  have h_sum_final : ∑ ℓ ∈ T_conc, ν₂ (A ℓ) ≥
      ENNReal.ofReal (Real.rpow r (2 * τ) / 6) := by
    have h_div6 : ∀ (x : ENNReal), (1 / 3 : ENNReal) * (x / 2) = x / 6 := by
      intro x
      have h_frac : (1 / 3 : ENNReal) * (1 / 2 : ENNReal) = (1 / 6 : ENNReal) := by
        have h1 : (1 / 3 : ENNReal) = ENNReal.ofReal (1 / 3 : ℝ) := by simp
        have h2 : (1 / 2 : ENNReal) = ENNReal.ofReal (1 / 2 : ℝ) := by simp
        have h3 : (1 / 6 : ENNReal) = ENNReal.ofReal (1 / 6 : ℝ) := by simp
        rw [h1, h2, h3]
        have h4 : ENNReal.ofReal (1 / 3 : ℝ) * ENNReal.ofReal (1 / 2 : ℝ) =
            ENNReal.ofReal ((1 / 3 : ℝ) * (1 / 2 : ℝ)) := by
          rw [← ENNReal.ofReal_mul (by norm_num)] <;> rfl
        rw [h4]
        have h5 : (1 / 3 : ℝ) * (1 / 2 : ℝ) = (1 / 6 : ℝ) := by norm_num
        rw [h5]
      have h1 : (1 / 3 : ENNReal) * (x / 2) = ((1 / 3 : ENNReal) * (1 / 2 : ENNReal)) * x := by
        simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] <;> ac_rfl
      rw [h1, h_frac]
      simp [div_eq_mul_inv, mul_comm]
    calc
      ∑ ℓ ∈ T_conc, ν₂ (A ℓ)
        ≥ (1 / 3 : ENNReal) * ∑ ℓ ∈ T_conc, tube_mass ℓ := h_sum_lower1
      _ ≥ (1 / 3 : ENNReal) * ((∑ ℓ ∈ T_x, tube_mass ℓ) / 2) := by gcongr
      _ = (∑ ℓ ∈ T_x, tube_mass ℓ) / 6 := h_div6 _
      _ ≥ ν₂ Y_x / 6 := by gcongr
      _ ≥ ENNReal.ofReal (Real.rpow r (2 * τ)) / 6 := by gcongr
      _ = ENNReal.ofReal (Real.rpow r (2 * τ) / 6) := by
        have h5 : ENNReal.ofReal (Real.rpow r (2 * τ)) / 6 =
            ENNReal.ofReal (Real.rpow r (2 * τ) / 6) := by
          rw [ENNReal.ofReal_div_of_pos (x := Real.rpow r (2 * τ)) (by norm_num)] <;> simp
        exact h5
  have h_main : ν₂ U ≥ ENNReal.ofReal (Real.rpow r (2 * τ) / 396) := by
    have h_div : (∑ ℓ ∈ T_conc, ν₂ (A ℓ)) / 66 ≤ ν₂ U := by
      have h9 : (∑ ℓ ∈ T_conc, ν₂ (A ℓ)) / 66 ≤ ((66 : ENNReal) * ν₂ U) / 66 := by gcongr
      have h10 : ((66 : ENNReal) * ν₂ U) / 66 = ν₂ U := by
        rw [mul_comm (66 : ENNReal) (ν₂ U)]
        have h66_ne_zero : (66 : ENNReal) ≠ 0 := by simp
        have h66_ne_top : (66 : ENNReal) ≠ ⊤ := by simp
        exact ENNReal.mul_div_cancel_right h66_ne_zero h66_ne_top
      rw [h10] at h9
      exact h9
    calc
      ν₂ U
        ≥ (∑ ℓ ∈ T_conc, ν₂ (A ℓ)) / 66 := h_div
      _ ≥ ENNReal.ofReal (Real.rpow r (2 * τ) / 6) / 66 := by gcongr
      _ = ENNReal.ofReal (Real.rpow r (2 * τ) / 396) := by
        have h_pos : 0 < Real.rpow r (2 * τ) / 6 := by positivity
        have h6 : ENNReal.ofReal (Real.rpow r (2 * τ) / 6) / (66 : ENNReal) =
            ENNReal.ofReal ((Real.rpow r (2 * τ) / 6) / 66) := by
          have h_pos66 : (0 : ℝ) < 66 := by norm_num
          have h_eq : ENNReal.ofReal ((Real.rpow r (2 * τ) / 6) / 66) =
              ENNReal.ofReal (Real.rpow r (2 * τ) / 6) / ENNReal.ofReal (66 : ℝ) :=
            ENNReal.ofReal_div_of_pos (x := Real.rpow r (2 * τ) / 6) h_pos66
          simpa using h_eq.symm
        rw [h6]
        have h7 : (Real.rpow r (2 * τ) / 6) / 66 = Real.rpow r (2 * τ) / 396 := by ring
        rw [h7]
  have hU_sub_G : U ⊆ {b₂ | (x, b₂) ∈ G} := by
    intro y hy
    rcases Set.mem_iUnion₂.mp hy with ⟨ℓ, _, hyA⟩
    have h_in_Y : y ∈ Y_x := hyA.2
    exact hY_sub_G h_in_Y
  have hU_sub' : U ⊆ {y : Point | (x, y) ∈ ConcentratedH' ν₂ G r κ threshold} ∩ {b₂ | (x, b₂) ∈ G} := by
    intro y hy
    exact ⟨hU_sub hy, hU_sub_G hy⟩
  exact le_trans h_main (measure_mono hU_sub')

end RadialBootstrapping
