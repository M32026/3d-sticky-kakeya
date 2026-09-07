import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.TrivialCovering
import MyLeanRepo.Kakeya.Assouad.WZ1.IntervalADHelpers
import Mathlib.Tactic

/-!
# Global slice geometry lemmas

Layer 1 of the global AD construction for `outputLoss ≤ sigma`.

Provides geometric bounds on horizontal slices of paper tubes:

1. `tube_axis_x_at_height`: x-coordinate of a tube axis at height z.
2. `tube_slice_projection_interval`: projection of one tube's horizontal slice
   onto `e0` is contained in an interval of length `42*δ`.
3. `externalCoveringNumber_finset_biUnion`: finite-union covering number bound.
4. `slice_projection_subset_tube_union`: shading projection is contained in
   the union of tube-carrier projections.
5. `tube_slice_projection_pairwise_disjoint`: sufficient condition for
   disjointness of two tube slice projections.

These lemmas are the geometric foundation for the multiscale Córdoba L²
argument that establishes global AD when `outputLoss ≤ sigma`.

## Whiteprint node
`PureWZ2/Grains/GlobalSliceGeometry`
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

/-- The x-coordinate equals the inner product with `e0 = single 0 1`. -/
lemma inner_e0_eq_coord0 (p : Point3) :
    inner ℝ p (EuclideanSpace.single (0 : Fin 3) 1) = p (0 : Fin 3) := by
  have h : inner ℝ p (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) =
      (1 : ℝ) * p (0 : Fin 3) :=
    EuclideanSpace.inner_single_right (0 : Fin 3) (1 : ℝ) p
  rw [h] <;> ring

/-- The x-coordinate of a tube's axis line at height `z`. -/
def tube_axis_x_at_height {δ : ℝ} (T : Kakeya.DeltaTube δ) (z : ℝ) : ℝ :=
  let t_z := (z - T.base (2 : Fin 3)) / T.direction (2 : Fin 3)
  (T.base + t_z • T.direction) (0 : Fin 3)

/-- Given `infEDist p L < ENNReal.ofReal r`, there exists `q ∈ L` with
`dist p q < r`.

Uses the fact that `infEDist` is the greatest lower bound of `edist p '' L`. -/
lemma tube_axis_exists_point
    {δ : ℝ} (T : Kakeya.DeltaTube δ) (p : Point3) {r : ℝ} (hr : 0 < r)
    (h : Metric.infEDist p (tubeAxisLine T) < ENNReal.ofReal r) :
    ∃ (q : Point3), q ∈ tubeAxisLine T ∧ dist p q < r := by
  have h_nonempty : (tubeAxisLine T).Nonempty :=
    ⟨T.base, ⟨0, by simp⟩⟩
  have h_image_nonempty : (edist p '' (tubeAxisLine T)).Nonempty :=
    h_nonempty.image (edist p)
  have h1 : ∃ d ∈ (edist p '' (tubeAxisLine T)), d < ENNReal.ofReal r := by
    by_contra h2
    push Not at h2
    have h3 : ∀ d ∈ (edist p '' (tubeAxisLine T)), ENNReal.ofReal r ≤ d := h2
    have h4 : ENNReal.ofReal r ≤ Metric.infEDist p (tubeAxisLine T) := by
      simpa [Metric.infEDist] using le_csInf h_image_nonempty h3
    exact False.elim (not_le.mpr h h4)
  rcases h1 with ⟨d, hd_in, hd_lt⟩
  rcases hd_in with ⟨q, hq, rfl⟩
  have h_dist : dist p q < r := by
    have h_iff : edist p q < ENNReal.ofReal r ↔ dist p q < r := by
      exact edist_lt_ofReal (x := p) (y := q) (r := r)
    exact h_iff.mp hd_lt
  exact ⟨q, hq, h_dist⟩

/-- Projection of a horizontal slice of a paper tube onto `e0` is contained
in an interval of length `42*δ`, centered at `tube_axis_x_at_height T z`.

Given a tube in line class `L₃` (`|direction 2| ≥ 1/2`), any point `p` in the
`6δ`-tube at height `z` satisfies `|p 0 - tube_axis_x_at_height T z| ≤ 21*δ`.

We use `7δ` instead of `6δ` for the distance to the axis (since the infimum
may not be achieved), giving a total bound of `21δ`. -/
lemma tube_slice_projection_interval
    {δ : ℝ} (hδ : 0 < δ)
    (T : Kakeya.DeltaTube δ)
    (hdir : 1 / 2 ≤ |T.direction (2 : Fin 3)|)
    (z : ℝ) :
    scalarProjection (EuclideanSpace.single (0 : Fin 3) 1)
      (horizontalSlice (wz1PaperTubeCarrier T) z)
    ⊆ Set.Icc (tube_axis_x_at_height T z - 21 * δ)
        (tube_axis_x_at_height T z + 21 * δ) := by
  have hdir2_ne_zero : T.direction (2 : Fin 3) ≠ 0 := by
    intro h
    rw [h] at hdir
    norm_num at hdir <;> linarith
  let t_z : ℝ := (z - T.base (2 : Fin 3)) / T.direction (2 : Fin 3)
  let q_z : Point3 := T.base + t_z • T.direction
  have hc : tube_axis_x_at_height T z = q_z (0 : Fin 3) := by
    rfl
  intro x hx
  rcases hx with ⟨p, hp, rfl⟩
  have h_p2 : p (2 : Fin 3) = z := hp.2
  have h_in_tube : p ∈ wz1PaperTubeCarrier T := hp.1
  have h_edist : Metric.infEDist p (tubeAxisLine T) ≤ ENNReal.ofReal (6 * δ) := by
    have h : p ∈ Metric.cthickening (6 * δ) (tubeAxisLine T) := h_in_tube.1
    have h' := Metric.cthickening_eq_preimage_infEDist (6 * δ) (tubeAxisLine T)
    rw [h'] at h
    exact h
  have h7 : Metric.infEDist p (tubeAxisLine T) < ENNReal.ofReal (7 * δ) := by
    have h8 : (6 * δ : ℝ) < (7 * δ : ℝ) := by linarith
    have h12 : ENNReal.ofReal (6 * δ) < ENNReal.ofReal (7 * δ) := by
      rw [ENNReal.ofReal_lt_ofReal_iff (by linarith)]
      <;> linarith
    exact h_edist.trans_lt h12
  rcases tube_axis_exists_point T p (by linarith) h7 with ⟨q, hq_line, hdist_lt⟩
  have hdist : dist p q < 7 * δ := hdist_lt
  have hnorm : ‖p - q‖ < 7 * δ := by
    simpa [dist_eq_norm] using hdist
  rcases hq_line with ⟨t, rfl⟩
  set qt : Point3 := T.base + t • T.direction with hqt_def
  have h1 : ‖p - qt‖ < 7 * δ := hnorm
  have h3 : |(p - qt) (2 : Fin 3)| ≤ ‖p - qt‖ := PiLp.norm_apply_le (p - qt) (2 : Fin 3)
  have h4 : |p (2 : Fin 3) - qt (2 : Fin 3)| ≤ ‖p - qt‖ := by
    have h5 : (p - qt) (2 : Fin 3) = p (2 : Fin 3) - qt (2 : Fin 3) := by
      simp [Pi.sub_apply]
    rw [h5] at h3
    exact h3
  have h5 : |qt (2 : Fin 3) - z| ≤ 7 * δ := by
    have h6 : |p (2 : Fin 3) - qt (2 : Fin 3)| ≤ ‖p - qt‖ := h4
    have h7 : |p (2 : Fin 3) - qt (2 : Fin 3)| < 7 * δ := h6.trans_lt h1
    rw [h_p2] at h7
    have h8 : |z - qt (2 : Fin 3)| < 7 * δ := h7
    have h9 : |qt (2 : Fin 3) - z| = |z - qt (2 : Fin 3)| := by rw [abs_sub_comm]
    rw [h9]
    exact h8.le
  have h7 : |t - t_z| ≤ 14 * δ := by
    have h8 : t - (z - T.base (2 : Fin 3)) / T.direction (2 : Fin 3) =
        (qt (2 : Fin 3) - z) / T.direction (2 : Fin 3) := by
      have h9 : qt (2 : Fin 3) = T.base (2 : Fin 3) + t * T.direction (2 : Fin 3) := by
        simp [qt, Pi.add_apply, Pi.smul_apply] <;> ring
      rw [h9]
      field_simp [hdir2_ne_zero] <;> ring
    have h_tz : t - t_z = t - (z - T.base (2 : Fin 3)) / T.direction (2 : Fin 3) := by
      rfl
    rw [h_tz, h8]
    have h9 : |(qt (2 : Fin 3) - z) / T.direction (2 : Fin 3)| =
        |qt (2 : Fin 3) - z| / |T.direction (2 : Fin 3)| := by rw [abs_div]
    rw [h9]
    have h10 : |T.direction (2 : Fin 3)| ≥ 1 / 2 := hdir
    calc |qt (2 : Fin 3) - z| / |T.direction (2 : Fin 3)|
      ≤ (7 * δ) / (1 / 2 : ℝ) := by gcongr
    _ = 14 * δ := by ring
  have h11 : |qt (0 : Fin 3) - q_z (0 : Fin 3)| ≤ 14 * δ := by
    have h12 : qt (0 : Fin 3) - q_z (0 : Fin 3) =
        (t - t_z) * T.direction (0 : Fin 3) := by
      simp [q_z, qt, Pi.add_apply, Pi.smul_apply] <;> ring
    rw [h12]
    have h13 : |(t - t_z) * T.direction (0 : Fin 3)| =
        |t - t_z| * |T.direction (0 : Fin 3)| := by rw [abs_mul]
    rw [h13]
    have h14 : |T.direction (0 : Fin 3)| ≤ ‖T.direction‖ := PiLp.norm_apply_le (T.direction) (0 : Fin 3)
    have h15 : ‖T.direction‖ = 1 := T.direction_unit
    have h16 : |T.direction (0 : Fin 3)| ≤ 1 := by
      rw [h15] at h14 <;> exact h14
    calc |t - t_z| * |T.direction (0 : Fin 3)|
      ≤ |t - t_z| * 1 := by gcongr
    _ = |t - t_z| := by ring
    _ ≤ 14 * δ := h7
  have h17 : |p (0 : Fin 3) - qt (0 : Fin 3)| ≤ ‖p - qt‖ :=
    PiLp.norm_apply_le (p - qt) (0 : Fin 3)
  have h18 : |p (0 : Fin 3) - qt (0 : Fin 3)| < 7 * δ := h17.trans_lt h1
  have h19 : |p (0 : Fin 3) - q_z (0 : Fin 3)| ≤ 21 * δ := by
    have h18 : |p (0 : Fin 3) - qt (0 : Fin 3)| ≤ 7 * δ := h17.trans h1.le
    calc |p (0 : Fin 3) - q_z (0 : Fin 3)|
      ≤ |p (0 : Fin 3) - qt (0 : Fin 3)| + |qt (0 : Fin 3) - q_z (0 : Fin 3)| :=
        abs_sub_le (p 0) (qt 0) (q_z 0)
    _ ≤ 7 * δ + 14 * δ := by linarith
    _ = 21 * δ := by ring
  have h20 : inner ℝ p (EuclideanSpace.single (0 : Fin 3) 1) = p (0 : Fin 3) :=
    inner_e0_eq_coord0 p
  simpa [h20, hc] using ⟨by linarith [abs_le.mp h19], by linarith [abs_le.mp h19]⟩

/-- Finite-union bound for external covering numbers. -/
lemma externalCoveringNumber_finset_biUnion
    {ι : Type*} (s : Finset ι) {ε : NNReal} (f : ι → Set ℝ) :
    (Metric.externalCoveringNumber ε (⋃ i ∈ s, f i) : ENNReal) ≤
      ∑ i ∈ s, (Metric.externalCoveringNumber ε (f i) : ENNReal) := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp
  | @insert i s hi ih =>
    have h_union : (⋃ j ∈ insert i s, f j) = f i ∪ (⋃ j ∈ s, f j) := by
      ext x; simp [Finset.mem_insert] <;> tauto
    rw [h_union]
    have h_bin : (Metric.externalCoveringNumber ε (f i ∪ (⋃ j ∈ s, f j)) : ENNReal) ≤
        (Metric.externalCoveringNumber ε (f i) : ENNReal) +
        (Metric.externalCoveringNumber ε (⋃ j ∈ s, f j) : ENNReal) := by
      exact_mod_cast externalCoveringNumber_union_le (ε := ε) (A := f i) (B := (⋃ j ∈ s, f j))
    rw [Finset.sum_insert hi]
    exact h_bin.trans (add_le_add_right ih _)

/-- The projection of a shading slice onto `e0` is contained in the union
of the projections of the individual paper tube carriers. -/
lemma slice_projection_subset_tube_union
    {δ : ℝ} {family : Kakeya.Streamlined.TubeFamily δ}
    {shading : WZ1PaperTubeShading family}
    (z : ℝ) :
    scalarProjection (EuclideanSpace.single (0 : Fin 3) 1)
      (horizontalSlice shading.union z)
    ⊆ ⋃ (i : Fin family.card),
      scalarProjection (EuclideanSpace.single (0 : Fin 3) 1)
        (horizontalSlice (wz1PaperTubeCarrier (family.tube i)) z) := by
  intro x hx
  rcases hx with ⟨p, hp, rfl⟩
  have h_p_in_union : p ∈ shading.union := hp.1
  rcases h_p_in_union with ⟨i, hi⟩
  have h_sub : shading.carrier i ⊆ wz1PaperTubeCarrier (family.tube i) :=
    shading.subset_body i
  have h_p_in_tube : p ∈ wz1PaperTubeCarrier (family.tube i) := h_sub hi
  have h_p_in_slice : p ∈ horizontalSlice (wz1PaperTubeCarrier (family.tube i)) z :=
    ⟨h_p_in_tube, hp.2⟩
  exact Set.mem_iUnion.mpr ⟨i, ⟨p, h_p_in_slice, rfl⟩⟩

/-- If two tubes' axis lines at height `z` have x-coordinates separated by at
least `42*δ`, then their horizontal slice projections onto `e0` are disjoint. -/
lemma tube_slice_projection_pairwise_disjoint
    {δ : ℝ} (hδ : 0 < δ)
    (T1 T2 : Kakeya.DeltaTube δ)
    (hdir1 : 1 / 2 ≤ |T1.direction (2 : Fin 3)|)
    (hdir2 : 1 / 2 ≤ |T2.direction (2 : Fin 3)|)
    (z : ℝ)
    (h_sep : 42 * δ < |tube_axis_x_at_height T1 z - tube_axis_x_at_height T2 z|) :
    Disjoint
      (scalarProjection (EuclideanSpace.single (0 : Fin 3) 1)
        (horizontalSlice (wz1PaperTubeCarrier T1) z))
      (scalarProjection (EuclideanSpace.single (0 : Fin 3) 1)
        (horizontalSlice (wz1PaperTubeCarrier T2) z)) := by
  let c1 := tube_axis_x_at_height T1 z
  let c2 := tube_axis_x_at_height T2 z
  have h1 := tube_slice_projection_interval hδ T1 hdir1 z
  have h2 := tube_slice_projection_interval hδ T2 hdir2 z
  have h_disj : Disjoint (Set.Icc (c1 - 21 * δ) (c1 + 21 * δ))
      (Set.Icc (c2 - 21 * δ) (c2 + 21 * δ)) := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    have h11 : |x - c1| ≤ 21 * δ := by
      apply abs_le.mpr
      constructor <;> linarith [hx1.1, hx1.2]
    have h22 : |x - c2| ≤ 21 * δ := by
      apply abs_le.mpr
      constructor <;> linarith [hx2.1, hx2.2]
    have h33 : |c1 - c2| ≤ 42 * δ := by
      calc |c1 - c2|
        ≤ |c1 - x| + |x - c2| := abs_sub_le c1 x c2
      _ = |x - c1| + |x - c2| := by rw [abs_sub_comm]
      _ ≤ 21 * δ + 21 * δ := by linarith
      _ = 42 * δ := by ring
    have h44 : 42 * δ < |c1 - c2| := h_sep
    linarith
  exact h_disj.mono h1 h2

/-- The scalar projection of a paper tube slice onto `e0` is bounded in `[-1, 1]`,
because the paper tube is cropped to `axisBox 2 2 2`. -/
lemma tube_slice_projection_bounded
    {δ : ℝ} (T : Kakeya.DeltaTube δ) (z : ℝ) :
    scalarProjection (EuclideanSpace.single (0 : Fin 3) 1)
      (horizontalSlice (wz1PaperTubeCarrier T) z)
    ⊆ Set.Icc (-1 : ℝ) 1 := by
  intro x hx
  rcases hx with ⟨p, hp, hx_eq⟩
  have h_box : p ∈ Kakeya.Streamlined.axisBox 2 2 2 := hp.1.2
  have h1 : |p (0 : Fin 3)| ≤ 1 := by
    simpa [Kakeya.Streamlined.axisBox] using h_box.1
  have h2 : inner ℝ p (EuclideanSpace.single (0 : Fin 3) 1) = p (0 : Fin 3) :=
    inner_e0_eq_coord0 p
  have h3 : x = p (0 : Fin 3) :=
    hx_eq.symm.trans h2
  rw [h3]
  exact ⟨by linarith [abs_le.mp h1], by linarith [abs_le.mp h1]⟩

/-- Covering number of a single tube's horizontal slice projection at scale `rho`.

Since the projection is contained in an interval of length `42*δ`, the covering
number at scale `rho ≥ δ` is at most `42*δ/rho + 2 ≤ 44`. -/
lemma tube_slice_projection_covering_number
    {δ : ℝ} (hδ : 0 < δ)
    (T : Kakeya.DeltaTube δ)
    (hdir : 1 / 2 ≤ |T.direction (2 : Fin 3)|)
    (z rho : ℝ) (hrho : 0 ≤ rho) (hδrho : δ ≤ rho) :
    (Metric.externalCoveringNumber ⟨rho, hrho⟩
      (scalarProjection (EuclideanSpace.single (0 : Fin 3) 1)
        (horizontalSlice (wz1PaperTubeCarrier T) z)) : ENNReal)
    ≤ ENNReal.ofReal (42 * δ / rho) + 2 := by
  have h_interval := tube_slice_projection_interval hδ T hdir z
  set c := tube_axis_x_at_height T z with hc
  have h_eq : (c - 21 * δ) + 42 * δ = c + 21 * δ := by ring
  have h_interval' : scalarProjection (EuclideanSpace.single (0 : Fin 3) 1)
        (horizontalSlice (wz1PaperTubeCarrier T) z)
      ⊆ Set.Icc (c - 21 * δ) ((c - 21 * δ) + 42 * δ) := by
    simpa [h_eq] using h_interval
  exact externalCoveringNumber_subset_interval
    (show 0 < rho from by linarith)
    (show 0 ≤ 42 * δ by linarith)
    h_interval'

/-- The scalar projection of the full shading slice onto `e0` is bounded in `[-1, 1]`. -/
lemma shading_slice_projection_bounded
    {δ : ℝ} {family : Kakeya.Streamlined.TubeFamily δ}
    {shading : WZ1PaperTubeShading family}
    (z : ℝ) :
    scalarProjection (EuclideanSpace.single (0 : Fin 3) 1)
      (horizontalSlice shading.union z)
    ⊆ Set.Icc (-1 : ℝ) 1 := by
  have h_sub := slice_projection_subset_tube_union (δ := δ) (family := family) (shading := shading) z
  have h_each : ∀ (i : Fin family.card),
      scalarProjection (EuclideanSpace.single (0 : Fin 3) 1)
        (horizontalSlice (wz1PaperTubeCarrier (family.tube i)) z)
      ⊆ Set.Icc (-1 : ℝ) 1 :=
    fun i => tube_slice_projection_bounded (family.tube i) z
  calc scalarProjection (EuclideanSpace.single (0 : Fin 3) 1)
         (horizontalSlice shading.union z)
       ⊆ ⋃ (i : Fin family.card), _ := h_sub
     _ ⊆ Set.Icc (-1 : ℝ) 1 := by
       intro x hx
       rcases Set.mem_iUnion.mp hx with ⟨i, hi⟩
       exact h_each i hi

end Kakeya.Assouad

end
