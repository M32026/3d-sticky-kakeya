import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition3_2PaperStatements
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PlaneMap
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import Mathlib.Tactic

/-!
# Finest-cell plane map selector

Constructs a plane map constant on `delta`-grid cubes, picking a unit normal
orthogonal to the selected tube direction in each cube.

## Properties

- Constant on `delta`-grid cubes
- Unit norm on the shading union
- Orthogonal to the selected tube direction (incidence 0 for that tube)
- Measurable (factors through the grid index)
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set InnerProductGeometry

attribute [local instance] Classical.propDecidable

/-- First standard basis vector. -/
private def e0 : Point3 := EuclideanSpace.single 0 1

/-- Second standard basis vector. -/
private def e1 : Point3 := EuclideanSpace.single 1 1

/-- Pick a unit vector orthogonal to `v`. -/
def orthogonalNormal (v : Point3) : Point3 :=
  if h : ‖wz1Cross v e0‖ = 0 then e1
  else (‖wz1Cross v e0‖)⁻¹ • wz1Cross v e0

lemma orthogonalNormal_unit (v : Point3) : ‖orthogonalNormal v‖ = 1 := by
  dsimp only [orthogonalNormal]
  by_cases h : ‖wz1Cross v e0‖ = 0
  · rw [dif_pos h]
    rw [EuclideanSpace.norm_eq]
    simp [e1, EuclideanSpace.single, Fin.sum_univ_succ] <;> norm_num
  · rw [dif_neg h]
    have hpos : 0 < ‖wz1Cross v e0‖ := by
      exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm h)
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hpos]
    field_simp [hpos.ne'] <;> ring

lemma orthogonalNormal_orthogonal (v : Point3) :
    inner ℝ v (orthogonalNormal v) = 0 := by
  dsimp only [orthogonalNormal]
  by_cases h : ‖wz1Cross v e0‖ = 0
  · -- Fallback: cross(v, e0) = 0 means v ∥ e0, so inner(v, e1) = 0
    rw [dif_pos h]
    have hcross : wz1Cross v e0 = 0 := by simpa [norm_eq_zero] using h
    have h_v1 : v 1 = 0 := by
      have h4 : (wz1Cross v e0) 2 = 0 := by
        rw [hcross] <;> simp
      have h6 : (wz1Cross v e0) 2 = -(v 1) := by
        simp [wz1Cross, cross_apply, e0, EuclideanSpace.single]
        <;> ring
      rw [h6] at h4
      linarith
    have h_inner : inner ℝ v e1 = v 1 := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simp [e1, EuclideanSpace.single, dotProduct, Fin.sum_univ_succ] <;> ring
    rw [h_inner, h_v1] <;> ring
  · rw [dif_neg h]
    have hinner : inner ℝ v ((‖wz1Cross v e0‖)⁻¹ • wz1Cross v e0) =
        (‖wz1Cross v e0‖)⁻¹ * inner ℝ v (wz1Cross v e0) := by
      rw [inner_smul_right]
    rw [hinner]
    have h_zero : inner ℝ v (wz1Cross v e0) = 0 :=
      PureWZ2PlaneMap.inner_cross_self_left v e0
    rw [h_zero] <;> ring

/-- Lower-left corner of a grid cell. -/
private def gridCorner (delta : ℝ) (cell : ℤ × ℤ × ℤ) : Point3 :=
  WithLp.toLp 2 fun i : Fin 3 =>
    delta * match i with
      | 0 => cell.1
      | 1 => cell.2.1
      | 2 => cell.2.2

/-- The corner belongs to its grid cube. -/
private lemma gridCorner_mem_cube {delta : ℝ} (hdelta_pos : 0 < delta)
    (cell : ℤ × ℤ × ℤ) :
    gridCorner delta cell ∈ wz1PaperGridCube delta cell := by
  rw [mem_wz1PaperGridCube]
  simp only [gridCorner, wz1PaperGridIndex, gridIndex]
  have h0 : ⌊(delta * (cell.1 : ℝ)) / delta⌋ = cell.1 := by
    have h : (delta * (cell.1 : ℝ)) / delta = (cell.1 : ℝ) := by
      field_simp [hdelta_pos.ne'] <;> ring
    rw [h] <;> simp
  have h1 : ⌊(delta * (cell.2.1 : ℝ)) / delta⌋ = cell.2.1 := by
    have h : (delta * (cell.2.1 : ℝ)) / delta = (cell.2.1 : ℝ) := by
      field_simp [hdelta_pos.ne'] <;> ring
    rw [h] <;> simp
  have h2 : ⌊(delta * (cell.2.2 : ℝ)) / delta⌋ = cell.2.2 := by
    have h : (delta * (cell.2.2 : ℝ)) / delta = (cell.2.2 : ℝ) := by
      field_simp [hdelta_pos.ne'] <;> ring
    rw [h] <;> simp
  exact Prod.ext h0 (Prod.ext h1 h2)

/-- Set of tube indices whose carrier contains `p`. -/
def carrierIndices
    {delta : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (p : Point3) :
    Finset (Fin (wz1PaperBodyFamily family).card) :=
  Finset.univ.filter fun i => p ∈ shading.carrier i

/-- Canonical equivalence between paper body index and tube family index. -/
private def paperIndexEquiv
    {delta : ℝ} {family : Kakeya.Streamlined.TubeFamily delta} :
    Equiv (Fin (wz1PaperBodyFamily family).card) (Fin family.card) :=
  have h : (wz1PaperBodyFamily family).card = family.card := by
    simp [wz1PaperBodyFamily]
  Equiv.cast (by rw [h])

/-- Finest-cell plane map: constant on each `delta`-cube. -/
def finestCellPlaneMap
    {delta : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading family)
    (p : Point3) : Point3 :=
  let cell := wz1PaperGridIndex delta p
  let corner := gridCorner delta cell
  let indices := carrierIndices shading corner
  if hnonempty : indices.Nonempty then
    let j := paperIndexEquiv (indices.min' hnonempty)
    orthogonalNormal (family.tube j).direction
  else
    e0

/-- The plane map is measurable. -/
lemma finestCellPlaneMap_measurable
    {delta : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family} :
    Measurable (finestCellPlaneMap shading) := by
  let f : (ℤ × ℤ × ℤ) → Point3 := fun cell =>
    let corner := gridCorner delta cell
    let indices := carrierIndices shading corner
    if hnonempty : indices.Nonempty then
      let j := paperIndexEquiv (indices.min' hnonempty)
      orthogonalNormal (family.tube j).direction
    else
      e0
  have h_eq : (finestCellPlaneMap shading) = f ∘ wz1PaperGridIndex delta := by
    funext p
    rfl
  rw [h_eq]
  have h2 : Measurable (fun p : Point3 =>
      (⌊p 0 / delta⌋, ⌊p 1 / delta⌋, ⌊p 2 / delta⌋)) := by fun_prop
  have h1 : Measurable (wz1PaperGridIndex delta) := by
    convert h2 using 1
    <;> funext p <;> simp [wz1PaperGridIndex, gridIndex]
  have h_f : Measurable f := by fun_prop
  exact h_f.comp h1

/-- The plane map is constant on each `delta`-grid cube. -/
lemma finestCellPlaneMap_const_on_cubes
    {delta : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    {p q : Point3}
    (h : wz1PaperGridIndex delta p = wz1PaperGridIndex delta q) :
    finestCellPlaneMap shading p = finestCellPlaneMap shading q := by
  dsimp only [finestCellPlaneMap]
  rw [h]

/-- The plane map has unit norm on the shading union. -/
lemma finestCellPlaneMap_unit
    {delta : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (hcubical : WZ1PaperIsCubicalShading shading)
    (hdelta_pos : 0 < delta)
    {p : Point3} (hp : p ∈ shading.union) :
    ‖finestCellPlaneMap shading p‖ = 1 := by
  rcases hp with ⟨i, hi⟩
  let cell := wz1PaperGridIndex delta p
  let corner := gridCorner delta cell
  let indices := carrierIndices shading corner
  have h_corner_in_carrier : corner ∈ shading.carrier i := by
    have hcube : wz1PaperGridCube delta cell ⊆ shading.carrier i :=
      hcubical i p hi
    have hcorner_in_cube : corner ∈ wz1PaperGridCube delta cell :=
      gridCorner_mem_cube hdelta_pos cell
    exact hcube hcorner_in_cube
  have hnonempty : indices.Nonempty := by
    refine ⟨i, ?_⟩
    simp only [indices, carrierIndices, Finset.mem_filter, Finset.mem_univ, true_and]
    exact h_corner_in_carrier
  have h_main : (if hnonempty : indices.Nonempty then
      let j := paperIndexEquiv (indices.min' hnonempty)
      orthogonalNormal (family.tube j).direction
    else e0) =
      (let j := paperIndexEquiv (indices.min' hnonempty)
       orthogonalNormal (family.tube j).direction) := by
    rw [dif_pos hnonempty]
  have h_eq : finestCellPlaneMap shading p =
      orthogonalNormal (family.tube (paperIndexEquiv (indices.min' hnonempty))).direction := by
    dsimp only [finestCellPlaneMap]
    rw [h_main]
  rw [h_eq]
  exact orthogonalNormal_unit _

/-- There exists a selected tube index `j` such that `p ∈ shading.carrier j`
and the plane map is orthogonal to `family.tube j`.direction. -/
lemma finestCellPlaneMap_orthogonal_to_selected
    {delta : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (hcubical : WZ1PaperIsCubicalShading shading)
    (hdelta_pos : 0 < delta)
    {p : Point3} (hp : p ∈ shading.union) :
    ∃ (j : Fin (wz1PaperBodyFamily family).card),
      p ∈ shading.carrier j ∧
      inner ℝ (family.tube (paperIndexEquiv j)).direction
          (finestCellPlaneMap shading p) = 0 := by
  rcases hp with ⟨i, hi⟩
  let cell := wz1PaperGridIndex delta p
  let corner := gridCorner delta cell
  let indices := carrierIndices shading corner
  have h_corner_in_carrier : corner ∈ shading.carrier i := by
    have hcube : wz1PaperGridCube delta cell ⊆ shading.carrier i :=
      hcubical i p hi
    have hcorner_in_cube : corner ∈ wz1PaperGridCube delta cell :=
      gridCorner_mem_cube hdelta_pos cell
    exact hcube hcorner_in_cube
  have hnonempty : indices.Nonempty := by
    refine ⟨i, ?_⟩
    simp only [indices, carrierIndices, Finset.mem_filter, Finset.mem_univ, true_and]
    exact h_corner_in_carrier
  let j_paper := indices.min' hnonempty
  have hj_in : j_paper ∈ indices := Finset.min'_mem indices hnonempty
  have hj_carrier : corner ∈ shading.carrier j_paper := by
    simp only [indices, carrierIndices, Finset.mem_filter, Finset.mem_univ, true_and] at hj_in
    exact hj_in
  have hcell_eq : wz1PaperGridIndex delta corner = cell :=
    gridCorner_mem_cube hdelta_pos cell
  have h_j_cube : wz1PaperGridCube delta cell ⊆ shading.carrier j_paper := by
    have h_tmp := hcubical j_paper corner hj_carrier
    rw [hcell_eq] at h_tmp
    exact h_tmp
  have h_p_in_j : p ∈ shading.carrier j_paper := by
    have h_p_in_cube : p ∈ wz1PaperGridCube delta cell := by
      rw [mem_wz1PaperGridCube]
    exact h_j_cube h_p_in_cube
  have h_main : (if hnonempty : indices.Nonempty then
      let j := paperIndexEquiv (indices.min' hnonempty)
      orthogonalNormal (family.tube j).direction
    else e0) =
      orthogonalNormal (family.tube (paperIndexEquiv j_paper)).direction := by
    rw [dif_pos hnonempty]
    <;> rfl
  have h_eq : finestCellPlaneMap shading p =
      orthogonalNormal (family.tube (paperIndexEquiv j_paper)).direction := by
    dsimp only [finestCellPlaneMap]
    rw [h_main]
  refine ⟨j_paper, h_p_in_j, ?_⟩
  rw [h_eq]
  exact orthogonalNormal_orthogonal _

/-- The normalization map `x ↦ ‖x‖⁻¹ • x` is `2/r`-Lipschitz on `{x | r ≤ ‖x‖}`. -/
lemma normalize_point3_lipschitz_on {r : ℝ} (hr : 0 < r) :
    LipschitzOnWith ⟨2 / r, by positivity⟩
      (fun x : Point3 => ‖x‖⁻¹ • x) {x | r ≤ ‖x‖} := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  have hx' : r ≤ ‖x‖ := hx
  have hy' : r ≤ ‖y‖ := hy
  have hnx : 0 < ‖x‖ := lt_of_lt_of_le hr hx'
  have hny : 0 < ‖y‖ := lt_of_lt_of_le hr hy'
  set nx := ‖x‖⁻¹ • x with hnx_def
  set ny := ‖y‖⁻¹ • y with hny_def
  have h_eq : nx - ny = ‖x‖⁻¹ • (x - y) + (‖x‖⁻¹ - ‖y‖⁻¹) • y := by
    simp [hnx_def, hny_def, sub_smul, smul_sub]
  have h_bound1 : ‖nx - ny‖ ≤ ‖x - y‖ / ‖x‖ + |‖x‖⁻¹ - ‖y‖⁻¹| * ‖y‖ := by
    rw [h_eq]
    calc
      ‖‖x‖⁻¹ • (x - y) + (‖x‖⁻¹ - ‖y‖⁻¹) • y‖
        ≤ ‖‖x‖⁻¹ • (x - y)‖ + ‖(‖x‖⁻¹ - ‖y‖⁻¹) • y‖ := norm_add_le _ _
      _ = ‖x - y‖ / ‖x‖ + |‖x‖⁻¹ - ‖y‖⁻¹| * ‖y‖ := by
        rw [norm_smul, norm_smul] <;> simp [Real.norm_eq_abs] <;> ring
  have h_pos : 0 < ‖x‖ * ‖y‖ := mul_pos hnx hny
  have h_abs : |‖x‖⁻¹ - ‖y‖⁻¹| = |‖x‖ - ‖y‖| / (‖x‖ * ‖y‖) := by
    have h : ‖x‖⁻¹ - ‖y‖⁻¹ = (‖y‖ - ‖x‖) / (‖x‖ * ‖y‖) := by
      field_simp [hnx.ne', hny.ne'] <;> ring
    rw [h]
    have h2 : |(‖y‖ - ‖x‖) / (‖x‖ * ‖y‖)| = |‖y‖ - ‖x‖| / |‖x‖ * ‖y‖| := by rw [abs_div]
    rw [h2]
    have h3 : |‖x‖ * ‖y‖| = ‖x‖ * ‖y‖ := abs_of_pos h_pos
    rw [h3]
    have h4 : |‖y‖ - ‖x‖| = |‖x‖ - ‖y‖| := by
      have h5 : ‖y‖ - ‖x‖ = -(‖x‖ - ‖y‖) := by ring
      rw [h5, abs_neg]
    rw [h4]
  rw [h_abs] at h_bound1
  have h_simp : |‖x‖ - ‖y‖| / (‖x‖ * ‖y‖) * ‖y‖ = |‖x‖ - ‖y‖| / ‖x‖ := by
    field_simp [hnx.ne', hny.ne'] <;> ring
  rw [h_simp] at h_bound1
  have h_rev : |‖x‖ - ‖y‖| ≤ ‖x - y‖ := abs_norm_sub_norm_le x y
  have h_final : ‖x - y‖ / ‖x‖ + |‖x‖ - ‖y‖| / ‖x‖ ≤ (2 / r) * ‖x - y‖ := by
    have h1 : ‖x - y‖ / ‖x‖ + |‖x‖ - ‖y‖| / ‖x‖ =
        (‖x - y‖ + |‖x‖ - ‖y‖|) / ‖x‖ := by ring
    rw [h1]
    have h2 : ‖x - y‖ + |‖x‖ - ‖y‖| ≤ 2 * ‖x - y‖ := by linarith [h_rev]
    have h3 : (‖x - y‖ + |‖x‖ - ‖y‖|) / ‖x‖ ≤ (2 * ‖x - y‖) / ‖x‖ := by gcongr
    have h4 : (2 * ‖x - y‖) / ‖x‖ ≤ (2 / r) * ‖x - y‖ := by
      calc
        (2 * ‖x - y‖) / ‖x‖ ≤ (2 * ‖x - y‖) / r := by gcongr
        _ = (2 / r) * ‖x - y‖ := by ring
    exact h3.trans h4
  exact h_bound1.trans h_final

/-- `orthogonalNormal` is 4-Lipschitz on line-class directions `{v | ‖v‖ = 1 ∧ v 2 ≥ 1/2}`.

This enables direction-alignment-based Lipschitz plane map construction. -/
lemma orthogonalNormal_lipschitz_on_lineclass :
    LipschitzOnWith 4 orthogonalNormal
      {v : Point3 | ‖v‖ = 1 ∧ v 2 ≥ 1 / 2} := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro v hv w hw
  have hv_z : v 2 ≥ 1 / 2 := hv.2
  have hw_z : w 2 ≥ 1 / 2 := hw.2

  have hcross_v_norm : ‖wz1Cross v e0‖ ≥ 1 / 2 := by
    have h1 : (wz1Cross v e0) 1 = v 2 := by
      simp [wz1Cross, e0, EuclideanSpace.single, cross_apply] <;> ring
    have h3 : ‖wz1Cross v e0‖ ≥ |(wz1Cross v e0) 1| := PiLp.norm_apply_le (wz1Cross v e0) 1
    rw [h1] at h3
    have h4 : |v 2| = v 2 := abs_of_nonneg (by linarith)
    rw [h4] at h3
    linarith
  have hcross_w_norm : ‖wz1Cross w e0‖ ≥ 1 / 2 := by
    have h1 : (wz1Cross w e0) 1 = w 2 := by
      simp [wz1Cross, e0, EuclideanSpace.single, cross_apply] <;> ring
    have h3 : ‖wz1Cross w e0‖ ≥ |(wz1Cross w e0) 1| := PiLp.norm_apply_le (wz1Cross w e0) 1
    rw [h1] at h3
    have h4 : |w 2| = w 2 := abs_of_nonneg (by linarith)
    rw [h4] at h3
    linarith

  have hnv : ‖wz1Cross v e0‖ ≠ 0 := by linarith
  have hnw : ‖wz1Cross w e0‖ ≠ 0 := by linarith

  have hcross_lip : ‖wz1Cross v e0 - wz1Cross w e0‖ ≤ ‖v - w‖ := by
    have h : wz1Cross v e0 - wz1Cross w e0 = wz1Cross (v - w) e0 := by
      ext i
      fin_cases i <;> simp [wz1Cross, cross_apply, Fin.sum_univ_succ] <;> ring
    have hcross_norm : ∀ (a b : Point3), ‖wz1Cross a b‖ ≤ ‖a‖ * ‖b‖ := by
      intro a b
      have h_eq : ‖wz1Cross a b‖ = ‖a‖ * ‖b‖ * Real.sin (InnerProductGeometry.angle a b) := by
        exact InnerProductGeometry.norm_toLp_symm_crossProduct (a : Fin 3 → ℝ) (b : Fin 3 → ℝ)
      rw [h_eq]
      have hsin : Real.sin (InnerProductGeometry.angle a b) ≤ 1 := Real.sin_le_one _
      have hpos : 0 ≤ ‖a‖ * ‖b‖ := by positivity
      nlinarith
    rw [h]
    have h5 : ‖wz1Cross (v - w) e0‖ ≤ ‖v - w‖ * ‖e0‖ := hcross_norm (v - w) e0
    have h9 : ‖e0‖ = 1 := by
      rw [EuclideanSpace.norm_eq]
      simp [e0, EuclideanSpace.single, Fin.sum_univ_succ] <;> norm_num
    rw [h9] at h5
    <;> linarith

  let X := wz1Cross v e0
  let Y := wz1Cross w e0
  have hX_in : X ∈ {x : Point3 | (1 / 2 : ℝ) ≤ ‖x‖} := hcross_v_norm
  have hY_in : Y ∈ {x : Point3 | (1 / 2 : ℝ) ≤ ‖x‖} := hcross_w_norm
  have hnorm_lip : dist (‖X‖⁻¹ • X) (‖Y‖⁻¹ • Y) ≤ (4 : ℝ) * dist X Y := by
    have h := normalize_point3_lipschitz_on
      (r := (1 / 2 : ℝ)) (by norm_num)
    rw [lipschitzOnWith_iff_dist_le_mul] at h
    have h4 := h X hX_in Y hY_in
    simp [NNReal.coe_mk] at h4
    norm_num at h4
    exact h4

  have h_orth_v : orthogonalNormal v = ‖X‖⁻¹ • X := by
    unfold orthogonalNormal
    rw [dif_neg hnv]
  have h_orth_w : orthogonalNormal w = ‖Y‖⁻¹ • Y := by
    unfold orthogonalNormal
    rw [dif_neg hnw]

  rw [h_orth_v, h_orth_w]
  rw [dist_eq_norm] at hnorm_lip
  rw [dist_eq_norm]
  exact hnorm_lip.trans (mul_le_mul_of_nonneg_left hcross_lip (by norm_num))

/-- Incidence bound from direction alignment.

If `normal = orthogonalNormal(coarse_dir)` and `fine_dir` is within `ρ/2` of
`coarse_dir`, then `|inner(fine_dir, normal)| ≤ ρ/2`. -/
lemma direction_alignment_incidence
    {rho : ℝ}
    {fine_dir coarse_dir normal : Point3}
    (hcoarse_unit : ‖coarse_dir‖ = 1)
    (hcoarse_z : coarse_dir 2 ≥ 1 / 2)
    (hnormal : normal = orthogonalNormal coarse_dir)
    (halign : ‖fine_dir - coarse_dir‖ ≤ rho / 2)
    (hrho_nonneg : 0 ≤ rho) :
    |inner ℝ fine_dir normal| ≤ rho / 2 := by
  have hperp : inner ℝ coarse_dir normal = 0 := by
    rw [hnormal]
    exact orthogonalNormal_orthogonal coarse_dir
  have h1 : inner ℝ fine_dir normal = inner ℝ (fine_dir - coarse_dir) normal := by
    have h2 : inner ℝ fine_dir normal =
        inner ℝ (fine_dir - coarse_dir) normal + inner ℝ coarse_dir normal := by
      simp [inner_sub_left] <;> ring
    rw [h2, hperp] <;> ring
  rw [h1]
  have h3 : |inner ℝ (fine_dir - coarse_dir) normal| ≤
      ‖fine_dir - coarse_dir‖ * ‖normal‖ :=
    abs_real_inner_le_norm (fine_dir - coarse_dir) normal
  have h4 : ‖normal‖ = 1 := by
    rw [hnormal]
    exact orthogonalNormal_unit coarse_dir
  rw [h4] at h3
  linarith

end Kakeya.Assouad

end
