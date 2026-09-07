import MyLeanRepo.Kakeya.Assouad.Definitions
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameters
import MyLeanRepo.Kakeya.Streamlined.Families
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Bounds for the twisted projection scale-selection proof

Two auxiliary lemmas:
1. `twisted_union_bounded`: the twisted union of a slope-window shading lies in
   a fixed bounded rectangle, so its 1-neighborhood has finite volume.
2. `frostman_exponent_reduction`: a Frostman bound at exponent `s₂` implies one
   at any smaller exponent `s₁` (since `r^s₂ ≤ r^s₁` for `0 < r ≤ 1`).

Whiteprint node: `lemma_d_bounded` and `lemma_e_frostman_reduction`.
-/

noncomputable section

open MeasureTheory Set

namespace Kakeya.Assouad

/-- Each coordinate of a Euclidean vector is bounded by its norm. -/
private lemma coord_abs_le_norm {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) (k : Fin n) :
    |x k| ≤ ‖x‖ := by
  have h1 : (x k)^2 ≤ ‖x‖^2 := by
    have h2 : ‖x‖^2 = ∑ i : Fin n, (x i)^2 := EuclideanSpace.real_norm_sq_eq x
    rw [h2]
    apply Finset.single_le_sum (fun i _ => sq_nonneg (x i)) (Finset.mem_univ k)
  have h4 : |x k|^2 = (x k)^2 := by rw [sq_abs]
  have h5 : |x k|^2 ≤ ‖x‖^2 := by rw [h4]; exact h1
  have h8 : |(|x k|)| ≤ |‖x‖| := sq_le_sq.mp h5
  simpa using h8

/-- The unit line segment is compact. -/
private lemma unitSegment_compact {base dir : Point3} :
    IsCompact (Kakeya.unitSegment base dir) := by
  apply IsCompact.image
  · exact isCompact_Icc
  · continuity

/-- Axis identity: a point on the tube axis satisfies `r 0 = a + c * r 2`. -/
private lemma tube_axis0 {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    (hvert : IsInVerticalChart F) (i : Fin F.card) (t : ℝ)
    (r : Point3) (hr : r = (F.tube i).base + t • (F.tube i).direction) :
    r 0 = (tubeParams i).a + (tubeParams i).c * r 2 := by
  let T := F.tube i
  have hdz_ne_zero : T.direction (2 : Fin 3) ≠ 0 := by
    have h : (1 / 2 : ℝ) ≤ |T.direction (2 : Fin 3)| := hvert i
    have h' : |T.direction (2 : Fin 3)| ≠ 0 := by linarith
    exact abs_ne_zero.mp h'
  have hr2 : r 2 = T.base 2 + t * T.direction 2 := by
    rw [hr]
    <;> rfl
  have hr0 : r 0 = T.base 0 + t * T.direction 0 := by
    rw [hr]
    <;> rfl
  rw [hr0, hr2]
  simp only [tubeParams, tubeParamsOfTube]
  simp [T]
  have hdz : (F.tube i).direction (2 : Fin 3) ≠ 0 := by
    simpa [T] using hdz_ne_zero
  field_simp [hdz] <;> ring

/-- Axis identity: a point on the tube axis satisfies `r 1 = b + d * r 2`. -/
private lemma tube_axis1 {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    (hvert : IsInVerticalChart F) (i : Fin F.card) (t : ℝ)
    (r : Point3) (hr : r = (F.tube i).base + t • (F.tube i).direction) :
    r 1 = (tubeParams i).b + (tubeParams i).d * r 2 := by
  let T := F.tube i
  have hdz_ne_zero : T.direction (2 : Fin 3) ≠ 0 := by
    have h : (1 / 2 : ℝ) ≤ |T.direction (2 : Fin 3)| := hvert i
    have h' : |T.direction (2 : Fin 3)| ≠ 0 := by linarith
    exact abs_ne_zero.mp h'
  have hr2 : r 2 = T.base 2 + t * T.direction 2 := by
    rw [hr]
    <;> rfl
  have hr1 : r 1 = T.base 1 + t * T.direction 1 := by
    rw [hr]
    <;> rfl
  rw [hr1, hr2]
  simp only [tubeParams, tubeParamsOfTube]
  simp [T]
  have hdz : (F.tube i).direction (2 : Fin 3) ≠ 0 := by
    simpa [T] using hdz_ne_zero
  field_simp [hdz] <;> ring

/--
For a point `q` in a tube carrier at height `z ∈ [-1,1]`, explicit
vertical-chart parameter bounds control its horizontal coordinates by `17`.
-/
lemma tube_point_bounds_of_params
    {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    (hparams : ∀ i : Fin F.card,
      |(tubeParams i).a| ≤ 12 ∧ |(tubeParams i).b| ≤ 12 ∧
        |(tubeParams i).c| ≤ 2 ∧ |(tubeParams i).d| ≤ 2)
    (hvert : IsInVerticalChart F)
    (hδ_pos : 0 < δ) (hδ_one : δ ≤ 1)
    (i : Fin F.card) {q : Point3} (hq : q ∈ (F.tube i).carrier)
    (hz : q 2 ∈ Set.Icc (-1 : ℝ) 1) :
    |q 0| ≤ 17 ∧ |q 1| ≤ 17 := by
  let seg := Kakeya.unitSegment (F.tube i).base (F.tube i).direction
  have h_seg_compact : IsCompact seg := unitSegment_compact
  have h_union : Metric.cthickening δ seg = ⋃ r ∈ seg, Metric.closedBall r δ :=
    h_seg_compact.cthickening_eq_biUnion_closedBall (by linarith)
  have hq' : q ∈ Metric.cthickening δ seg := hq
  rw [h_union] at hq'
  rcases Set.mem_iUnion₂.mp hq' with ⟨r, hr_seg, hqr⟩
  have hdist : dist q r ≤ δ := by
    simpa [Metric.mem_closedBall] using hqr
  have h_seg_eq : seg =
      (fun t : ℝ => (F.tube i).base + t • (F.tube i).direction) ''
        Set.Icc 0 1 := by
    rfl
  rw [h_seg_eq] at hr_seg
  rcases hr_seg with ⟨t, _ht, h_eq⟩
  have hr_eq : r = (F.tube i).base + t • (F.tube i).direction := h_eq.symm
  have h_coord_diff0 : |q 0 - r 0| ≤ δ := by
    calc
      |q 0 - r 0| ≤ ‖q - r‖ := coord_abs_le_norm (q - r) 0
      _ = dist q r := by rfl
      _ ≤ δ := hdist
  have h_coord_diff1 : |q 1 - r 1| ≤ δ := by
    calc
      |q 1 - r 1| ≤ ‖q - r‖ := coord_abs_le_norm (q - r) 1
      _ = dist q r := by rfl
      _ ≤ δ := hdist
  have h_coord_diff2 : |q 2 - r 2| ≤ δ := by
    calc
      |q 2 - r 2| ≤ ‖q - r‖ := coord_abs_le_norm (q - r) 2
      _ = dist q r := by rfl
      _ ≤ δ := hdist
  have hq2_ge : -1 ≤ q 2 := hz.1
  have hq2_le : q 2 ≤ 1 := hz.2
  have h_abs2 : -δ ≤ q 2 - r 2 := (abs_le.mp h_coord_diff2).1
  have h_abs3 : q 2 - r 2 ≤ δ := (abs_le.mp h_coord_diff2).2
  have hr2_ge : -(1 + δ) ≤ r 2 := by linarith
  have hr2_le : r 2 ≤ 1 + δ := by linarith
  have hr2_abs : |r 2| ≤ 1 + δ := abs_le.mpr ⟨hr2_ge, hr2_le⟩
  let p := tubeParams i
  have h_axis0 : r 0 = p.a + p.c * r 2 := tube_axis0 hvert i t r hr_eq
  have h_axis1 : r 1 = p.b + p.d * r 2 := tube_axis1 hvert i t r hr_eq
  have h_bounds := hparams i
  have h_ha : |p.a| ≤ 12 := h_bounds.1
  have h_hb : |p.b| ≤ 12 := h_bounds.2.1
  have h_hc : |p.c| ≤ 2 := h_bounds.2.2.1
  have h_hd : |p.d| ≤ 2 := h_bounds.2.2.2
  have h_r0_abs : |r 0| ≤ 12 + 2 * (1 + δ) := by
    rw [h_axis0]
    have h1 : |p.a + p.c * r 2| ≤ |p.a| + |p.c * r 2| :=
      abs_add_le _ _
    have h2 : |p.c * r 2| = |p.c| * |r 2| := abs_mul _ _
    rw [h2] at h1
    have h_prod : |p.c| * |r 2| ≤ 2 * (1 + δ) := by
      gcongr <;> linarith
    linarith [h_ha, h_prod]
  have h_r1_abs : |r 1| ≤ 12 + 2 * (1 + δ) := by
    rw [h_axis1]
    have h1 : |p.b + p.d * r 2| ≤ |p.b| + |p.d * r 2| :=
      abs_add_le _ _
    have h2 : |p.d * r 2| = |p.d| * |r 2| := abs_mul _ _
    rw [h2] at h1
    have h_prod : |p.d| * |r 2| ≤ 2 * (1 + δ) := by
      gcongr <;> linarith
    linarith [h_hb, h_prod]
  have h_q0 : |q 0| ≤ 17 := by
    have h1 : |q 0| ≤ |r 0| + |q 0 - r 0| := by
      calc
        |q 0| = |r 0 + (q 0 - r 0)| := by ring_nf
        _ ≤ |r 0| + |q 0 - r 0| := abs_add_le _ _
    linarith [h_r0_abs, h_coord_diff0, hδ_one]
  have h_q1 : |q 1| ≤ 17 := by
    have h1 : |q 1| ≤ |r 1| + |q 1 - r 1| := by
      calc
        |q 1| = |r 1 + (q 1 - r 1)| := by ring_nf
        _ ≤ |r 1| + |q 1 - r 1| := abs_add_le _ _
    linarith [h_r1_abs, h_coord_diff1, hδ_one]
  exact ⟨h_q0, h_q1⟩

/-- Basepoint radius four supplies the explicit parameter bounds above. -/
lemma tube_point_bounds {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    (hbase : HasBoundedBase F 4) (hvert : IsInVerticalChart F)
    (hδ_pos : 0 < δ) (hδ_one : δ ≤ 1)
    (i : Fin F.card) {q : Point3} (hq : q ∈ (F.tube i).carrier)
    (hz : q 2 ∈ Set.Icc (-1 : ℝ) 1) :
    |q 0| ≤ 17 ∧ |q 1| ≤ 17 :=
  tube_point_bounds_of_params
    (fun j => tubeParams_bounds hbase hvert j)
    hvert hδ_pos hδ_one i hq hz

/--
For `f` nonsingular with `f 0 = 0`, we have `|f z| ≤ 2` on `[-1,1]`.
-/
lemma nonsingular_f_bound {f : SlopeFunction} (h_ns : f.IsNonsingular)
    (h0 : f 0 = 0) {z : ℝ} (hz : z ∈ Set.Icc (-1 : ℝ) 1) :
    |f z| ≤ 2 := by
  have hderiv : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ‖deriv f x‖ ≤ 2 := by
    intro x hx
    have h : |deriv f x| ≤ 2 := (h_ns x hx).2.1
    simpa using h
  have h_conv : Convex ℝ (Set.Icc (-1 : ℝ) 1) := convex_Icc (-1 : ℝ) 1
  have h0_in : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by norm_num
  have h_diff_on : ∀ x ∈ Set.Icc (-1 : ℝ) 1, DifferentiableAt ℝ f x := by
    intro x hx
    have h1 : 1 ≤ |deriv f x| := (h_ns x hx).1
    have h2 : deriv f x ≠ 0 := by
      have h3 : 0 < |deriv f x| := by linarith
      have h4 : |deriv f x| ≠ 0 := ne_of_gt h3
      exact abs_ne_zero.mp h4
    by_cases h4 : DifferentiableAt ℝ f x
    · exact h4
    · have h5 : deriv f x = 0 := deriv_zero_of_not_differentiableAt h4
      contradiction
  have hft : ‖f z - f 0‖ ≤ 2 * ‖z - (0 : ℝ)‖ :=
    h_conv.norm_image_sub_le_of_norm_deriv_le h_diff_on hderiv h0_in hz
  have h_abs : |f z - f 0| ≤ 2 * |z| := by
    have h9 : ‖f z - f 0‖ = |f z - f 0| := by simp
    have h10 : ‖z - (0 : ℝ)‖ = |z| := by simp
    rw [h9, h10] at hft
    exact hft
  have h0' : f 0 = 0 := h0
  have h_main : |f z| ≤ 2 * |z| := by
    have h11 : f z = f z - f 0 := by rw [h0'] <;> ring
    rw [h11]
    exact h_abs
  have hz' : |z| ≤ 1 := abs_le.mpr ⟨hz.1, hz.2⟩
  calc
    |f z| ≤ 2 * |z| := h_main
    _ ≤ 2 * 1 := by gcongr
    _ = 2 := by norm_num

/--
The twisted union of a slope-window shading is contained in the rectangle
`[-51, 51] × [-1, 1]`.
-/
lemma twisted_union_contained_of_params {δ : ℝ}
    {F : Kakeya.Streamlined.TubeFamily δ}
    (hparams : ∀ i : Fin F.card,
      |(tubeParams i).a| ≤ 12 ∧ |(tubeParams i).b| ≤ 12 ∧
        |(tubeParams i).c| ≤ 2 ∧ |(tubeParams i).d| ≤ 2)
    (hvert : IsInVerticalChart F)
    (hδ_pos : 0 < δ) (hδ_one : δ ≤ 1)
    {Y : Kakeya.Streamlined.TubeShading F} (hY : IsInSlopeWindow Y)
    {f : SlopeFunction} (h_ns : f.IsNonsingular) (h0 : f 0 = 0) :
    twistedUnion Y f ⊆ {p : Point2 | |p 0| ≤ 51 ∧ |p 1| ≤ 1} := by
  intro p hp
  rcases (Set.mem_image _ _ _).mp hp with ⟨q, hq, rfl⟩
  have hq_union : q ∈ Y.union := hq
  rcases (Set.mem_setOf_eq.mp hq_union) with ⟨i, hi⟩
  have hq_body : q ∈ (F.tube i).carrier := Y.subset_body i hi
  have hq_slab : q ∈ horizontalSlab (-1) 1 := hY hq_union
  have hz : q 2 ∈ Set.Icc (-1 : ℝ) 1 := by
    simpa [horizontalSlab] using hq_slab
  have h_bounds :=
    tube_point_bounds_of_params hparams hvert
      hδ_pos hδ_one i hq_body hz
  have h_fz : |f (q 2)| ≤ 2 := nonsingular_f_bound h_ns h0 hz
  have h_p0 : |(twistedProjection f q) 0| ≤ 51 := by
    have h_eq : (twistedProjection f q) 0 = q 0 + f (q 2) * q 1 := by
      simp [twistedProjection]
    rw [h_eq]
    have h_tri : |q 0 + f (q 2) * q 1| ≤
        |q 0| + |f (q 2) * q 1| := abs_add_le _ _
    have h_mul : |f (q 2) * q 1| = |f (q 2)| * |q 1| := abs_mul _ _
    rw [h_mul] at h_tri
    have h_prod : |f (q 2)| * |q 1| ≤ 34 := by
      calc
        |f (q 2)| * |q 1| ≤ 2 * 17 := by gcongr <;> linarith
        _ = 34 := by norm_num
    have h_total : |q 0| + |f (q 2)| * |q 1| ≤ 51 := by
      linarith [h_bounds.1, h_prod]
    linarith [h_tri, h_total]
  have h_p1 : |(twistedProjection f q) 1| ≤ 1 := by
    have h_eq : (twistedProjection f q) 1 = q 2 := by
      simp [twistedProjection]
    rw [h_eq]
    exact abs_le.mpr ⟨hz.1, hz.2⟩
  exact ⟨h_p0, h_p1⟩

/-- Basepoint radius four supplies the explicit parameter certificate. -/
lemma twisted_union_contained {δ : ℝ}
    {F : Kakeya.Streamlined.TubeFamily δ}
    (hbase : HasBoundedBase F 4) (hvert : IsInVerticalChart F)
    (hδ_pos : 0 < δ) (hδ_one : δ ≤ 1)
    {Y : Kakeya.Streamlined.TubeShading F} (hY : IsInSlopeWindow Y)
    {f : SlopeFunction} (h_ns : f.IsNonsingular) (h0 : f 0 = 0) :
    twistedUnion Y f ⊆ {p : Point2 | |p 0| ≤ 51 ∧ |p 1| ≤ 1} :=
  twisted_union_contained_of_params
    (fun i => tubeParams_bounds hbase hvert i)
    hvert hδ_pos hδ_one hY h_ns h0

/--
The 1-neighborhood of the twisted union has volume bounded by an absolute
constant. This feeds into `scale_selection_neighborhood_ratio`.
-/
lemma twisted_union_one_neighborhood_bounded_of_params {δ : ℝ}
    {F : Kakeya.Streamlined.TubeFamily δ}
    (hparams : ∀ i : Fin F.card,
      |(tubeParams i).a| ≤ 12 ∧ |(tubeParams i).b| ≤ 12 ∧
        |(tubeParams i).c| ≤ 2 ∧ |(tubeParams i).d| ≤ 2)
    (hvert : IsInVerticalChart F)
    (hδ_pos : 0 < δ) (hδ_one : δ ≤ 1)
    {Y : Kakeya.Streamlined.TubeShading F} (hY : IsInSlopeWindow Y)
    {f : SlopeFunction} (h_ns : f.IsNonsingular) (h0 : f 0 = 0) :
    ∃ (C : ENNReal), C ≠ ⊤ ∧
      MeasureTheory.volume (Metric.cthickening 1 (twistedUnion Y f)) ≤ C := by
  let R : Set Point2 := {p | |p 0| ≤ 51 ∧ |p 1| ≤ 1}
  have h1 : twistedUnion Y f ⊆ R :=
    twisted_union_contained_of_params
      hparams hvert hδ_pos hδ_one hY h_ns h0
  have hR_sub : R ⊆ Metric.closedBall (0 : Point2) 52 := by
    intro p hp
    have h4 : |p 0| ≤ 51 := hp.1
    have h5 : |p 1| ≤ 1 := hp.2
    have h6 : ‖p‖ ≤ 52 := by
      have h7 : ‖p‖ ^ 2 = (p 0)^2 + (p 1)^2 := by
        simp [EuclideanSpace.real_norm_sq_eq]
      nlinarith [abs_le.mp h4, abs_le.mp h5]
    simpa [Metric.mem_closedBall] using h6
  have hR_bdd : Bornology.IsBounded R :=
    Metric.isBounded_closedBall.subset hR_sub
  have hthick_bdd : Bornology.IsBounded (Metric.cthickening 1 R) :=
    hR_bdd.cthickening
  have h2 : Metric.cthickening 1 (twistedUnion Y f) ⊆
      Metric.cthickening 1 R := by
    intro p hp
    have h_inf : Metric.infEDist p (twistedUnion Y f) ≤ 1 := by
      simpa [Metric.cthickening] using hp
    have h_anti : Metric.infEDist p R ≤
        Metric.infEDist p (twistedUnion Y f) :=
      Metric.infEDist_anti h1
    have h' : Metric.infEDist p R ≤ 1 := le_trans h_anti h_inf
    simpa [Metric.cthickening] using h'
  have h3 : MeasureTheory.volume
      (Metric.cthickening 1 (twistedUnion Y f)) ≤
      MeasureTheory.volume (Metric.cthickening 1 R) :=
    measure_mono h2
  have h_ne_top : MeasureTheory.volume (Metric.cthickening 1 R) ≠ ⊤ :=
    hthick_bdd.measure_lt_top.ne
  refine ⟨MeasureTheory.volume (Metric.cthickening 1 R), h_ne_top, h3⟩

/-- Basepoint radius four supplies the explicit parameter certificate. -/
lemma twisted_union_one_neighborhood_bounded {δ : ℝ}
    {F : Kakeya.Streamlined.TubeFamily δ}
    (hbase : HasBoundedBase F 4) (hvert : IsInVerticalChart F)
    (hδ_pos : 0 < δ) (hδ_one : δ ≤ 1)
    {Y : Kakeya.Streamlined.TubeShading F} (hY : IsInSlopeWindow Y)
    {f : SlopeFunction} (h_ns : f.IsNonsingular) (h0 : f 0 = 0) :
    ∃ (C : ENNReal), C ≠ ⊤ ∧
      MeasureTheory.volume (Metric.cthickening 1 (twistedUnion Y f)) ≤ C :=
  twisted_union_one_neighborhood_bounded_of_params
    (fun i => tubeParams_bounds hbase hvert i)
    hvert hδ_pos hδ_one hY h_ns h0

/--
Frostman exponent reduction: if `A` satisfies the Frostman condition at
exponent `s2`, it also satisfies it at any smaller exponent `s1 ≥ 0`,
because `r^s2 ≤ r^s1` for `0 < r ≤ 1` and `s1 ≤ s2`.
-/
lemma frostman_exponent_reduction {n : ℕ} {A : DiscreteSet n}
    {w s1 s2 : ℝ} {C : ENNReal}
    (h : A.IsFrostman w s2 C)
    (hw_pos : 0 < w) (_hs1 : 0 ≤ s1) (h_le : s1 ≤ s2) :
    A.IsFrostman w s1 C := by
  intro x r hw hr1
  have h4 := h x r hw hr1
  have h6 : 0 < r := lt_of_lt_of_le hw_pos hw
  have h8 : r ≤ 1 := hr1
  have h9 : r ^ s2 ≤ r ^ s1 :=
    Real.rpow_le_rpow_of_exponent_ge h6 h8 h_le
  have h5 : Kakeya.realRpowENN r s2 ≤ Kakeya.realRpowENN r s1 := by
    simp only [Kakeya.realRpowENN]
    exact ENNReal.ofReal_le_ofReal h9
  calc
    A.ballCount x r
      ≤ C * Kakeya.realRpowENN r s2 * A.enncard := h4
    _ ≤ C * Kakeya.realRpowENN r s1 * A.enncard := by gcongr

end Kakeya.Assouad
