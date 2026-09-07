import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.SameHeightDiameter
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.WindowParameterCellFourBlockStatement

/-!
# Geometric helpers for the windowed parameter-cell four-block

These declarations isolate the shaded-piece coverage calculation from the
coarse-family construction so both elaborate under the default proof budget.
-/

noncomputable section

namespace Kakeya.Assouad

lemma window_parameter_axis_diff_norm_bound
    (a b c d ia ib ic id z mesh : ℝ)
    (hz_abs : |z| ≤ 1)
    (hmesh_nonneg : 0 ≤ mesh)
    (hclose_a : |ia - a| ≤ mesh)
    (hclose_b : |ib - b| ≤ mesh)
    (hclose_c : |ic - c| ≤ mesh)
    (hclose_d : |id - d| ≤ mesh) :
    ‖point3 (ia + ic * z) (ib + id * z) z -
        point3 (a + c * z) (b + d * z) z‖ ≤
      3 * mesh := by
  set v : Point3 :=
    point3 (ia + ic * z) (ib + id * z) z -
      point3 (a + c * z) (b + d * z) z with hv
  have h0 : |v 0| ≤ 2 * mesh := by
    have h_eq : v 0 = (ia - a) + (ic - c) * z := by
      simp [hv, point3, Pi.add_apply, Pi.sub_apply, Pi.smul_apply] <;> ring
    rw [h_eq]
    calc
      |(ia - a) + (ic - c) * z|
          ≤ |ia - a| + |(ic - c) * z| := abs_add_le _ _
      _ = |ia - a| + |ic - c| * |z| := by rw [abs_mul]
      _ ≤ mesh + mesh * 1 := by gcongr <;> linarith
      _ = 2 * mesh := by ring
  have h1 : |v 1| ≤ 2 * mesh := by
    have h_eq : v 1 = (ib - b) + (id - d) * z := by
      simp [hv, point3, Pi.add_apply, Pi.sub_apply, Pi.smul_apply] <;> ring
    rw [h_eq]
    calc
      |(ib - b) + (id - d) * z|
          ≤ |ib - b| + |(id - d) * z| := abs_add_le _ _
      _ = |ib - b| + |id - d| * |z| := by rw [abs_mul]
      _ ≤ mesh + mesh * 1 := by gcongr <;> linarith
      _ = 2 * mesh := by ring
  have h2 : v 2 = 0 := by
    simp [hv, point3, Pi.add_apply, Pi.sub_apply, Pi.smul_apply] <;> ring
  have hsum : ‖v‖ ^ 2 = ∑ i : Fin 3, (v i) ^ 2 :=
    EuclideanSpace.real_norm_sq_eq v
  have h0sq : (v 0) ^ 2 ≤ (2 * mesh) ^ 2 := by
    nlinarith [abs_le.mp h0]
  have h1sq : (v 1) ^ 2 ≤ (2 * mesh) ^ 2 := by
    nlinarith [abs_le.mp h1]
  have h2sq : (v 2) ^ 2 = 0 := by rw [h2] <;> ring
  have h_sum_sq : ∑ i : Fin 3, (v i) ^ 2 ≤ 8 * mesh ^ 2 := by
    have h_expand :
        ∑ i : Fin 3, (v i) ^ 2 =
          (v 0) ^ 2 + (v 1) ^ 2 + (v 2) ^ 2 := by
      simp [Fin.sum_univ_succ] <;> ring
    rw [h_expand]
    nlinarith [hmesh_nonneg]
  have h_norm_sq : ‖v‖ ^ 2 ≤ 8 * mesh ^ 2 := by
    rw [hsum]
    exact h_sum_sq
  have h_pos : 0 ≤ ‖v‖ := by positivity
  have h9 : ‖v‖ ^ 2 ≤ (3 * mesh) ^ 2 := by
    calc
      ‖v‖ ^ 2 ≤ 8 * mesh ^ 2 := h_norm_sq
      _ ≤ 9 * mesh ^ 2 := by nlinarith [hmesh_nonneg]
      _ = (3 * mesh) ^ 2 := by ring
  have h10 : 0 ≤ 3 * mesh := by positivity
  nlinarith [h_pos, h10]

lemma window_parameter_point3_coord (x y z : ℝ) :
    (point3 x y z) 0 = x ∧
      (point3 x y z) 1 = y ∧
      (point3 x y z) 2 = z := by
  constructor
  · simp [point3, EuclideanSpace.single_apply] <;> ring
  · constructor
    · simp [point3, EuclideanSpace.single_apply] <;> ring
    · simp [point3, EuclideanSpace.single_apply] <;> ring

lemma window_parameter_refAxis_on_segment
    (base0 dirPos refAxis : Point3)
    (t kreal s : ℝ)
    (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1)
    (h_t_formula : refAxis = base0 + t • dirPos)
    (h2 : kreal + s = t) :
    refAxis ∈
      Kakeya.unitSegment (base0 + kreal • dirPos) dirPos := by
  refine ⟨s, ⟨hs0, hs1⟩, ?_⟩
  have h_assoc :
      (base0 + kreal • dirPos) + s • dirPos =
        base0 + (kreal • dirPos + s • dirPos) :=
    add_assoc base0 (kreal • dirPos) (s • dirPos)
  have h_smul :
      kreal • dirPos + s • dirPos =
        (kreal + s) • dirPos :=
    (add_smul kreal s dirPos).symm
  change base0 + kreal • dirPos + s • dirPos = refAxis
  calc
    base0 + kreal • dirPos + s • dirPos
        = base0 + (kreal • dirPos + s • dirPos) := h_assoc
    _ = base0 + (kreal + s) • dirPos := by rw [h_smul]
    _ = base0 + t • dirPos := by rw [h2]
    _ = refAxis := h_t_formula.symm

lemma window_parameter_s_bounds
    (t kreal : ℝ)
    (hk1 : kreal ≤ t)
    (hk2 : t ≤ kreal + 1) :
    0 ≤ t - kreal ∧ t - kreal ≤ 1 := by
  constructor
  · exact sub_nonneg.mpr hk1
  · linarith

lemma window_parameter_exists_fin4_interval
    (t : ℝ)
    (ht0 : 0 ≤ t)
    (ht4 : t ≤ 4) :
    ∃ k : Fin 4, (k : ℝ) ≤ t ∧ t ≤ (k : ℝ) + 1 := by
  by_cases h1 : t ≤ 1
  · exact ⟨0, by simpa, by simpa using h1⟩
  · have h1le : (1 : ℝ) ≤ t := by linarith
    by_cases h2 : t ≤ 2
    · refine ⟨1, by simpa, ?_⟩
      norm_num
      exact h2
    · have h2le : (2 : ℝ) ≤ t := by linarith
      by_cases h3 : t ≤ 3
      · refine ⟨2, by simpa, ?_⟩
        norm_num
        exact h3
      · have h3le : (3 : ℝ) ≤ t := by linarith
        refine ⟨3, by simpa, ?_⟩
        norm_num
        exact ht4

lemma window_parameter_cell_shading_cover
    {delta rho : ℝ}
    (hdelta : 0 < delta)
    {family : Kakeya.Streamlined.TubeFamily delta}
    (hvertical : IsInVerticalChart family)
    (shading : Kakeya.Streamlined.TubeShading family)
    (hslope : IsInSlopeWindow shading)
    (indices : Finset (Fin family.card))
    (reference : Fin family.card)
    (mesh : ℝ)
    (hmesh_nonneg : 0 ≤ mesh)
    (hbudget : 3 * delta + 3 * mesh ≤ rho)
    (hclose :
      ∀ index ∈ indices,
        |(tubeParams index).a - (tubeParams reference).a| ≤ mesh ∧
          |(tubeParams index).b - (tubeParams reference).b| ≤ mesh ∧
          |(tubeParams index).c - (tubeParams reference).c| ≤ mesh ∧
          |(tubeParams index).d - (tubeParams reference).d| ≤ mesh)
    (norm : ℝ)
    (hnorm_pos : 0 < norm)
    (hnorm_le_two : norm ≤ 2)
    (dirPos base0 : Point3)
    (hdirPos :
      dirPos =
        point3
          ((tubeParams reference).c / norm)
          ((tubeParams reference).d / norm)
          (1 / norm))
    (hbase0 :
      base0 =
        point3
          ((tubeParams reference).a - (tubeParams reference).c)
          ((tubeParams reference).b - (tubeParams reference).d)
          (-1))
    (coarseTube : Fin 4 → Kakeya.DeltaTube rho)
    (hcoarseBase :
      ∀ k,
        (coarseTube k).base =
          base0 + (k : ℝ) • dirPos)
    (hcoarseDirection :
      ∀ k, (coarseTube k).direction = dirPos) :
    ∀ index ∈ indices,
      shading.carrier index ⊆
        (Kakeya.Streamlined.TubeFamily.toBodyFamily
          { card := 4, tube := coarseTube }).union := by
  intro index hindex p hp
  let params := tubeParams reference
  let a := params.a
  let b := params.b
  let c := params.c
  let d := params.d
  have h_p_in_tube : p ∈ (family.tube index).carrier :=
    shading.subset_body index hp
  let z : ℝ := p (2 : Fin 3)
  have hz_in_window : z ∈ Set.Icc (-1 : ℝ) 1 := by
    have h : p ∈ shading.union := ⟨index, hp⟩
    simpa [horizontalSlab] using hslope h
  let indexParams := tubeParams index
  have hclose_a : |indexParams.a - a| ≤ mesh :=
    (hclose index hindex).1
  have hclose_b : |indexParams.b - b| ≤ mesh :=
    (hclose index hindex).2.1
  have hclose_c : |indexParams.c - c| ≤ mesh :=
    (hclose index hindex).2.2.1
  have hclose_d : |indexParams.d - d| ≤ mesh :=
    (hclose index hindex).2.2.2
  have h_axis_dist :
      ‖p -
          point3
            (indexParams.a + indexParams.c * z)
            (indexParams.b + indexParams.d * z)
            z‖ ≤
        3 * delta :=
    tubeCarrier_axisDistance
      hdelta.le hvertical index p h_p_in_tube z rfl
  let refAxis : Point3 :=
    point3 (a + c * z) (b + d * z) z
  let sourceAxis : Point3 :=
    point3
      (indexParams.a + indexParams.c * z)
      (indexParams.b + indexParams.d * z)
      z
  have hz_abs : |z| ≤ 1 :=
    abs_le.mpr hz_in_window
  have h_axis_diff_norm :
      ‖sourceAxis - refAxis‖ ≤ 3 * mesh :=
    window_parameter_axis_diff_norm_bound
      a b c d
      indexParams.a indexParams.b indexParams.c indexParams.d
      z mesh hz_abs hmesh_nonneg
      hclose_a hclose_b hclose_c hclose_d
  have h_dist_to_refAxis : ‖p - refAxis‖ ≤ rho := by
    have h_eq :
        p - refAxis =
          (p - sourceAxis) + (sourceAxis - refAxis) := by
      abel
    rw [h_eq]
    exact
      (norm_add_le _ _).trans
        (by linarith [h_axis_dist, h_axis_diff_norm, hbudget])
  let t : ℝ := (z + 1) * norm
  have h_ref0 : refAxis 0 = a + c * z :=
    (window_parameter_point3_coord
      (a + c * z) (b + d * z) z).1
  have h_ref1 : refAxis 1 = b + d * z :=
    (window_parameter_point3_coord
      (a + c * z) (b + d * z) z).2.1
  have h_ref2 : refAxis 2 = z :=
    (window_parameter_point3_coord
      (a + c * z) (b + d * z) z).2.2
  have h_base0_0 : base0 0 = a - c := by
    rw [hbase0]
    exact (window_parameter_point3_coord (a - c) (b - d) (-1)).1
  have h_base0_1 : base0 1 = b - d := by
    rw [hbase0]
    exact (window_parameter_point3_coord (a - c) (b - d) (-1)).2.1
  have h_base0_2 : base0 2 = -1 := by
    rw [hbase0]
    exact (window_parameter_point3_coord (a - c) (b - d) (-1)).2.2
  have h_dir0 : dirPos 0 = c / norm := by
    rw [hdirPos]
    exact (window_parameter_point3_coord (c / norm) (d / norm) (1 / norm)).1
  have h_dir1 : dirPos 1 = d / norm := by
    rw [hdirPos]
    exact
      (window_parameter_point3_coord
        (c / norm) (d / norm) (1 / norm)).2.1
  have h_dir2 : dirPos 2 = 1 / norm := by
    rw [hdirPos]
    exact
      (window_parameter_point3_coord
        (c / norm) (d / norm) (1 / norm)).2.2
  have h_sum0 : (base0 + t • dirPos) 0 = a + c * z := by
    change base0 0 + t * dirPos 0 = a + c * z
    rw [h_base0_0, h_dir0]
    dsimp only [t]
    field_simp [hnorm_pos.ne'] <;> ring
  have h_sum1 : (base0 + t • dirPos) 1 = b + d * z := by
    change base0 1 + t * dirPos 1 = b + d * z
    rw [h_base0_1, h_dir1]
    dsimp only [t]
    field_simp [hnorm_pos.ne'] <;> ring
  have h_sum2 : (base0 + t • dirPos) 2 = z := by
    change base0 2 + t * dirPos 2 = z
    rw [h_base0_2, h_dir2]
    dsimp only [t]
    field_simp [hnorm_pos.ne'] <;> ring
  have h_t_formula : refAxis = base0 + t • dirPos := by
    ext i
    fin_cases i
    · exact h_ref0.trans h_sum0.symm
    · exact h_ref1.trans h_sum1.symm
    · exact h_ref2.trans h_sum2.symm
  have ht0 : 0 ≤ t := by
    dsimp only [t]
    exact mul_nonneg (by linarith [hz_in_window.1]) hnorm_pos.le
  have ht4 : t ≤ 4 := by
    dsimp only [t]
    have h4 :
        (z + 1) * norm ≤ 2 * norm :=
      mul_le_mul_of_nonneg_right
        (by linarith [hz_in_window.2]) hnorm_pos.le
    linarith
  rcases window_parameter_exists_fin4_interval t ht0 ht4 with
    ⟨k, hk1, hk2⟩
  let kreal : ℝ := k
  let s : ℝ := t - kreal
  have hs :=
    window_parameter_s_bounds t kreal hk1 hk2
  have h2 : kreal + s = t := by
    dsimp only [s]
    ring
  have h_refAxis_in_segment :
      refAxis ∈
        Kakeya.unitSegment (coarseTube k).base
          (coarseTube k).direction := by
    rw [hcoarseBase k, hcoarseDirection k]
    exact
      window_parameter_refAxis_on_segment
        base0 dirPos refAxis t kreal s
        hs.1 hs.2 h_t_formula h2
  have h_p_in_coarse : p ∈ (coarseTube k).carrier := by
    exact
      Metric.mem_cthickening_of_dist_le
        p refAxis rho
        (Kakeya.unitSegment
          (coarseTube k).base (coarseTube k).direction)
        h_refAxis_in_segment h_dist_to_refAxis
  exact ⟨k, h_p_in_coarse⟩

end Kakeya.Assouad
