import MyLeanRepo.Kakeya.Assouad.PropStickyPaperTubeCarrierGeometryStatements
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Thickening
import MyLeanRepo.Kakeya.Streamlined.VolumeHelpers

/-!
# Helper lemmas for paper tube carrier geometry

Reparameterization lemmas for `tubeAxisLine` and `wz2PaperAxisCoreSegment`
in terms of `wz1TubeAxisZeroPoint` and `wz1PaperDirection`.
-/

noncomputable section

namespace Kakeya.Assouad

/--
The full coaxial line equals the affine line through `wz1TubeAxisZeroPoint`
in direction `wz1PaperDirection`.
-/
lemma tubeAxisLine_eq_affineSpan {delta : ℝ} (tube : Kakeya.DeltaTube delta)
    (hvertical : (1 / 2 : ℝ) ≤ |tube.direction (2 : Fin 3)|) :
    tubeAxisLine tube =
    {p | ∃ t : ℝ, p = wz1TubeAxisZeroPoint tube + t • wz1PaperDirection tube} := by
  set z := wz1TubeAxisZeroPoint tube with hz_def
  set d := wz1PaperDirection tube with hd_def
  set v := tube.direction with hv_def
  set b := tube.base with hb_def
  have hne : v (2 : Fin 3) ≠ 0 := by
    intro h
    rw [h, abs_zero] at hvertical
    norm_num at hvertical
  let t0 : ℝ := -b (2 : Fin 3) / v (2 : Fin 3)
  have hz_eq : z = b + t0 • v := by
    have h1 : z = b - (b (2 : Fin 3) / v (2 : Fin 3)) • v := rfl
    rw [h1]
    have h3 : t0 = -(b (2 : Fin 3) / v (2 : Fin 3)) := by
      simp [t0]
      ring
    rw [h3]
    have h4 : b + (-(b (2 : Fin 3) / v (2 : Fin 3))) • v =
        b - (b (2 : Fin 3) / v (2 : Fin 3)) • v := by
      have h5 : (-(b (2 : Fin 3) / v (2 : Fin 3))) • v =
          -((b (2 : Fin 3) / v (2 : Fin 3)) • v) := by
        rw [neg_smul]
      rw [h5]
      rfl
    exact h4.symm
  have hd_cases : d = v ∨ d = -v := by
    simp [hd_def, wz1PaperDirection]
    split_ifs <;> tauto
  ext p
  simp only [Set.mem_setOf_eq, tubeAxisLine]
  constructor
  · rintro ⟨t, rfl⟩
    rcases hd_cases with h_d | h_d
    · refine ⟨t - t0, ?_⟩
      have h : b + t • v = z + (t - t0) • d := by
        rw [h_d, hz_eq]
        simp [sub_smul]
      exact h
    · refine ⟨t0 - t, ?_⟩
      have h : b + t • v = z + (t0 - t) • d := by
        rw [h_d, hz_eq]
        simp [sub_smul, smul_neg]
      exact h
  · rintro ⟨t, rfl⟩
    rcases hd_cases with h_d | h_d
    · refine ⟨t0 + t, ?_⟩
      have h : z + t • d = b + (t0 + t) • v := by
        rw [h_d, hz_eq]
        simp [add_smul]
        abel
      exact h
    · refine ⟨t0 - t, ?_⟩
      have h : z + t • d = b + (t0 - t) • v := by
        rw [h_d, hz_eq]
        simp [sub_smul, smul_neg]
        abel
      exact h

/--
The length-four axis segment is equivalently parameterized by `t ∈ [-2, 2]`
starting from `wz1TubeAxisZeroPoint` in direction `wz1PaperDirection`.
-/
lemma wz2PaperAxisCoreSegment_eq {delta : ℝ} (tube : Kakeya.DeltaTube delta) :
    wz2PaperAxisCoreSegment tube =
    {p | ∃ t : ℝ, t ∈ Set.Icc (-2) 2 ∧
      p = wz1TubeAxisZeroPoint tube + t • wz1PaperDirection tube} := by
  ext p
  simp only [wz2PaperAxisCoreSegment, Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨parameter, hparam, rfl⟩
    have h1 : parameter ∈ Set.Icc (0 : ℝ) 4 := hparam
    have h2 : parameter - 2 ∈ Set.Icc (-2 : ℝ) 2 := by
      exact ⟨by linarith [h1.1], by linarith [h1.2]⟩
    exact ⟨parameter - 2, h2, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    have h1 : t ∈ Set.Icc (-2 : ℝ) 2 := ht
    refine ⟨t + 2, ?_, ?_⟩
    · exact ⟨by linarith [h1.1], by linarith [h1.2]⟩
    · ring_nf

/-- The full affine line coaxial with a tube is convex. -/
lemma convex_tubeAxisLine {delta : ℝ} (tube : Kakeya.DeltaTube delta) :
    Convex ℝ (tubeAxisLine tube) := by
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨tx, rfl⟩
  rcases hy with ⟨ty, rfl⟩
  refine ⟨a * tx + b * ty, ?_⟩
  have hbase : a • tube.base + b • tube.base = tube.base := by
    rw [← add_smul, hab, one_smul]
  have hdir : (a * tx) • tube.direction + (b * ty) • tube.direction =
      (a * tx + b * ty) • tube.direction := by
    rw [← add_smul]
  calc
    a • (tube.base + tx • tube.direction) +
        b • (tube.base + ty • tube.direction) =
        (a • tube.base + (a * tx) • tube.direction) +
          (b • tube.base + (b * ty) • tube.direction) := by
      simp [smul_add, smul_smul]
    _ = (a • tube.base + b • tube.base) +
          ((a * tx) • tube.direction + (b * ty) • tube.direction) := by
      abel
    _ = tube.base + (a * tx + b * ty) • tube.direction := by
      rw [hbase, hdir]

/-- The cropped paper tube carrier is convex. -/
lemma convex_wz1PaperTubeCarrier {delta : ℝ} (tube : Kakeya.DeltaTube delta) :
    Convex ℝ (wz1PaperTubeCarrier tube) := by
  have h1 : Convex ℝ (tubeAxisLine tube) := convex_tubeAxisLine tube
  have h2 : Convex ℝ (Metric.cthickening (6 * delta) (tubeAxisLine tube)) :=
    h1.cthickening (6 * delta)
  have h3 : Convex ℝ (Kakeya.Streamlined.axisBox 2 2 2) :=
    Kakeya.Streamlined.convex_axisBox 2 2 2
  exact h2.inter h3

/-- The tube axis line is a closed subset of `Point3`. -/
lemma isClosed_tubeAxisLine {delta : ℝ} (tube : Kakeya.DeltaTube delta) :
    IsClosed (tubeAxisLine tube) := by
  let directionSubmodule : Submodule ℝ Point3 :=
    Submodule.span ℝ {tube.direction}
  let affineLine : AffineSubspace ℝ Point3 :=
    AffineSubspace.mk' tube.base directionSubmodule
  have h1 : (affineLine : Set Point3) = tubeAxisLine tube := by
    ext p
    have h_iff : p ∈ (affineLine : Set Point3) ↔
        ∃ (t : ℝ), p = tube.base + t • tube.direction := by
      have h_mem : p ∈ (affineLine : Set Point3) ↔
          p -ᵥ tube.base ∈ directionSubmodule :=
        AffineSubspace.mem_mk'
      have h_span : p -ᵥ tube.base ∈ directionSubmodule ↔
          ∃ (a : ℝ), a • tube.direction = p -ᵥ tube.base := by
        simp [directionSubmodule, Submodule.mem_span_singleton]
      constructor
      · intro h
        have h' : p -ᵥ tube.base ∈ directionSubmodule := h_mem.mp h
        rcases h_span.mp h' with ⟨a, ha⟩
        refine ⟨a, ?_⟩
        have h_eq : (a • tube.direction) +ᵥ tube.base = p := by
          rw [ha]
          exact vsub_vadd p tube.base
        have h_add : (a • tube.direction) +ᵥ tube.base =
            tube.base + a • tube.direction := by
          simp
          exact add_comm _ _
        rw [h_add] at h_eq
        exact h_eq.symm
      · rintro ⟨t, ht⟩
        have h_eq : p -ᵥ tube.base = t • tube.direction := by
          have h4 : p = tube.base + t • tube.direction := ht
          rw [h4]
          simp
        have h' : p -ᵥ tube.base ∈ directionSubmodule :=
          h_span.mpr ⟨t, h_eq.symm⟩
        exact h_mem.mpr h'
    simpa [tubeAxisLine, Set.mem_setOf_eq] using h_iff
  rw [← h1]
  exact AffineSubspace.closed_of_finiteDimensional affineLine

/--
If `x` is in the closed `r`-thickening of a closed set `s` in a proper space,
there exists `y ∈ s` with `dist x y ≤ r`.
-/
lemma exists_dist_le_of_mem_cthickening_closed
    {α : Type*} [PseudoMetricSpace α] [ProperSpace α]
    {s : Set α} (hs : IsClosed s) {x : α} {r : ℝ} (hr : 0 ≤ r)
    (h : x ∈ Metric.cthickening r s) :
    ∃ y ∈ s, dist x y ≤ r := by
  have h_eq : Metric.cthickening r s =
      ⋃ y ∈ closure s, Metric.closedBall y r :=
    Metric.cthickening_eq_biUnion_closedBall s hr
  rw [h_eq] at h
  rcases Set.mem_iUnion₂.mp h with ⟨y, hy_closure, hy_ball⟩
  have hys : y ∈ s := by
    have hcl : closure s = s := hs.closure_eq
    rw [hcl] at hy_closure
    exact hy_closure
  exact ⟨y, hys, by simpa [Metric.mem_closedBall] using hy_ball⟩

/-- The absolute difference of each coordinate is bounded by Euclidean distance. -/
lemma abs_coord_sub_le_dist {x y : Point3} (i : Fin 3) :
    |x i - y i| ≤ dist x y := by
  have h1 : |x i - y i| = ‖(x - y) i‖ := by
    have h11 : (x - y) i = x i - y i := by
      simp [PiLp.sub_apply]
    rw [h11]
    rfl
  rw [h1]
  have h2 : ‖(x - y) i‖ ≤ ‖x - y‖ := PiLp.norm_apply_le (x - y) i
  have h3 : dist x y = ‖x - y‖ := dist_eq_norm x y
  rw [h3]
  exact h2

end Kakeya.Assouad

end
