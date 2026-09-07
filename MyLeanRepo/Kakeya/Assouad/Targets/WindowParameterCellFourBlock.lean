import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.WindowParameterCellFourBlockHelpers


/-!
WZ2 Proposition 7.1: realize one occupied four-parameter cell by four
canonical coarse tubes covering the current slope-window shading.
-/

namespace Kakeya.Assouad

theorem window_parameter_cell_four_block :
    WindowParameterCellFourBlockStatement := by
  dsimp only [WindowParameterCellFourBlockStatement]
  intro _coaxialStatement
  intros delta rho hdelta hrho hrho_small hdelta_le_one mesh hmesh_nonneg hbudget
    family hvert hparams shading hslope indices hindices_nonempty reference href_in_indices hclose

  let refTube := family.tube reference
  let refDir := refTube.direction
  let dz := refDir (2 : Fin 3)
  let params := tubeParams reference
  let a := params.a
  let b := params.b
  let c := params.c
  let d := params.d

  have hdz_abs : (1 / 2 : ℝ) ≤ |dz| := hvert reference
  have hdz_ne_zero : dz ≠ 0 := by
    have h : 0 < |dz| := by linarith
    exact abs_ne_zero.mp h.ne'
  have hdir_unit : ‖refDir‖ = 1 := refTube.direction_unit
  have hdz_le_one : |dz| ≤ 1 := by
    have h : |dz| ≤ ‖refDir‖ := euclidean_coord_le_norm refDir (2 : Fin 3)
    rw [hdir_unit] at h; exact h

  have ha : |a| ≤ 12 := (hparams reference).1
  have hb : |b| ≤ 12 := (hparams reference).2.1
  have hc : |c| ≤ 2 := (hparams reference).2.2.1
  have hd : |d| ≤ 2 := (hparams reference).2.2.2

  have hc_def : c = refDir 0 / dz := by
    dsimp only [c, params, tubeParams, tubeParamsOfTube] <;> rfl
  have hd_def : d = refDir 1 / dz := by
    dsimp only [d, params, tubeParams, tubeParamsOfTube] <;> rfl

  have hdir_sq : (refDir 0)^2 + (refDir 1)^2 + dz^2 = 1 := by
    have h_pos : 0 ≤ ∑ i : Fin 3, (refDir i)^2 := by positivity
    have h_eq : ‖refDir‖ = Real.sqrt (∑ i : Fin 3, (refDir i)^2) := by
      simp [EuclideanSpace.norm_eq]
    have h1 : ‖refDir‖^2 = ∑ i : Fin 3, (refDir i)^2 := by
      rw [h_eq]
      rw [Real.sq_sqrt h_pos]
    have h2 : ‖refDir‖^2 = 1 := by rw [hdir_unit] <;> norm_num
    have h3 : ∑ i : Fin 3, (refDir i)^2 = (refDir 0)^2 + (refDir 1)^2 + dz^2 := by
      simp [Fin.sum_univ_succ] <;> ring
    linarith

  let norm : ℝ := Real.sqrt (1 + c^2 + d^2)

  have hnorm_pos : 0 < norm := by positivity
  have hnorm_sq : norm^2 = 1 + c^2 + d^2 := Real.sq_sqrt (by positivity)

  have h1_cd : c^2 + d^2 + 1 = 1 / dz^2 := by
    rw [hc_def, hd_def]
    field_simp [hdz_ne_zero] <;> linarith
  have hnorm_eq : norm = 1 / |dz| := by
    have h2 : 1 + c^2 + d^2 = 1 / dz^2 := by linarith
    have h4 : Real.sqrt (1 / dz^2) = 1 / |dz| := by
      have h_abs_sq : |dz|^2 = dz^2 := by rw [sq_abs]
      have h5 : 1 / dz^2 = (1 / |dz|)^2 := by
        rw [← h_abs_sq]
        <;> field_simp <;> ring
      rw [h5]
      rw [Real.sqrt_sq_eq_abs]
      <;> simp [abs_of_pos (show (0 : ℝ) < 1 / |dz| from by positivity)]
    have h6 : Real.sqrt (1 + c^2 + d^2) = Real.sqrt (1 / dz^2) := by rw [h2]
    have h7 : norm = Real.sqrt (1 + c^2 + d^2) := by rfl
    rw [h7, h6, h4]

  have hnorm1 : 1 ≤ norm := by
    rw [hnorm_eq]
    have h : |dz| ≤ 1 := hdz_le_one
    have h' : 0 < |dz| := by linarith
    rw [one_le_div h'] <;> linarith
  have hnorm2 : norm ≤ 2 := by
    rw [hnorm_eq]
    have h : (1 / 2 : ℝ) ≤ |dz| := hdz_abs
    have h' : 0 < |dz| := by linarith
    have h'' : 1 / |dz| ≤ 2 := by
      calc 1 / |dz| ≤ 1 / (1 / 2 : ℝ) := by gcongr
        _ = 2 := by norm_num
    exact h''

  let dir_pos : Point3 := point3 (c / norm) (d / norm) (1 / norm)

  have hdir_pos_unit : ‖dir_pos‖ = 1 := by
    have hsum1 : ∑ i : Fin 3, (dir_pos i)^2 = (c^2 + d^2 + 1) / norm^2 := by
      simp [dir_pos, point3, Fin.sum_univ_succ]
      <;> field_simp [hnorm_pos.ne'] <;> ring
    have hsum2 : (c^2 + d^2 + 1) / norm^2 = 1 := by
      have h3 : c^2 + d^2 + 1 = norm^2 := by linarith [hnorm_sq]
      rw [h3]
      field_simp [hnorm_pos.ne']
    have hsum : ∑ i : Fin 3, (dir_pos i)^2 = 1 := by
      rw [hsum1, hsum2]
    have h_pos : 0 ≤ ∑ i : Fin 3, (dir_pos i)^2 := by positivity
    have h_eq : ‖dir_pos‖ = Real.sqrt (∑ i : Fin 3, (dir_pos i)^2) := by
      simp [EuclideanSpace.norm_eq]
    have h : ‖dir_pos‖^2 = ∑ i : Fin 3, (dir_pos i)^2 := by
      rw [h_eq, Real.sq_sqrt h_pos]
    have h5 : ‖dir_pos‖^2 = 1 := by rw [h, hsum]
    have h6 : 0 ≤ ‖dir_pos‖ := by positivity
    nlinarith

  have hdir_pos2 : dir_pos 2 = 1 / norm := by
    simp [dir_pos, point3]
  have hdir_pos0 : dir_pos 0 = c / norm := by
    simp [dir_pos, point3]
  have hdir_pos1 : dir_pos 1 = d / norm := by
    simp [dir_pos, point3]

  let base0 : Point3 := point3 (a - c) (b - d) (-1)

  let coarseTube (k : Fin 4) : Kakeya.DeltaTube rho :=
    ⟨base0 + (k : ℝ) • dir_pos, dir_pos, hdir_pos_unit⟩

  let coarse : Kakeya.Streamlined.TubeFamily rho :=
    ⟨4, coarseTube⟩

  have h_base_k_coords : ∀ (k : Fin 4),
      (coarseTube k).base 0 = a + c * ((coarseTube k).base 2) ∧
      (coarseTube k).base 1 = b + d * ((coarseTube k).base 2) := by
    intro k
    have h2 : (coarseTube k).base 2 = -1 + (k : ℝ) / norm := by
      simp [coarseTube, base0, point3, dir_pos, Pi.add_apply, Pi.smul_apply] <;> ring
    have h0 : (coarseTube k).base 0 = a - c + (k : ℝ) * (c / norm) := by
      simp [coarseTube, base0, point3, dir_pos, Pi.add_apply, Pi.smul_apply] <;> ring
    have h1 : (coarseTube k).base 1 = b - d + (k : ℝ) * (d / norm) := by
      simp [coarseTube, base0, point3, dir_pos, Pi.add_apply, Pi.smul_apply] <;> ring
    constructor
    · rw [h0, h2] <;> field_simp [hnorm_pos.ne'] <;> ring
    · rw [h1, h2] <;> field_simp [hnorm_pos.ne'] <;> ring

  have h_base0_bound : ‖base0‖ < 20 := by
    have h_tri1 : |a - c| ≤ |a| + |c| := by
      have h : |a + (-c)| ≤ |a| + |(-c)| := abs_add_le a (-c)
      have h2 : |(-c)| = |c| := abs_neg c
      have h3 : a + (-c) = a - c := by ring
      rw [h3, h2] at h
      exact h
    have h_tri2 : |b - d| ≤ |b| + |d| := by
      have h : |b + (-d)| ≤ |b| + |(-d)| := abs_add_le b (-d)
      have h2 : |(-d)| = |d| := abs_neg d
      have h3 : b + (-d) = b - d := by ring
      rw [h3, h2] at h
      exact h
    have h0 : |base0 0| ≤ 14 := by
      simp [base0, point3] <;> linarith
    have h1 : |base0 1| ≤ 14 := by
      simp [base0, point3] <;> linarith
    have h2 : |base0 2| = 1 := by
      simp [base0, point3] <;> norm_num
    have h_norm_sq : ‖base0‖^2 ≤ 393 := by
      have h_pos : 0 ≤ ∑ i : Fin 3, (base0 i)^2 := by positivity
      have h_eq : ‖base0‖ = Real.sqrt (∑ i : Fin 3, (base0 i)^2) := by
        simp [EuclideanSpace.norm_eq]
      have hsum : ‖base0‖^2 = ∑ i : Fin 3, (base0 i)^2 := by
        rw [h_eq, Real.sq_sqrt h_pos]
      rw [hsum]
      have h0' : (base0 0)^2 ≤ 14^2 := by
        have h4 : (base0 0)^2 = |base0 0|^2 := by rw [sq_abs]
        rw [h4]
        gcongr
      have h1' : (base0 1)^2 ≤ 14^2 := by
        have h4 : (base0 1)^2 = |base0 1|^2 := by rw [sq_abs]
        rw [h4]
        gcongr
      have h2' : (base0 2)^2 = 1 := by
        have h4 : (base0 2)^2 = |base0 2|^2 := by rw [sq_abs]
        rw [h4, h2] <;> norm_num
      have h_sum2 : (base0 0)^2 + ((base0 1)^2 + (base0 2)^2) ≤ 393 := by
        have h_eq : (base0 0)^2 + ((base0 1)^2 + (base0 2)^2) = (base0 0)^2 + (base0 1)^2 + (base0 2)^2 := by ring
        rw [h_eq]
        linarith
      simpa [Fin.sum_univ_succ] using h_sum2
    have h_pos : 0 ≤ ‖base0‖ := by positivity
    have h_lt : ‖base0‖^2 < 20^2 := by linarith
    by_cases h10 : ‖base0‖ < 20
    · exact h10
    · have h11 : 20 ≤ ‖base0‖ := by linarith
      have h12 : (20 : ℝ)^2 ≤ ‖base0‖^2 := by gcongr
      linarith

  have h_base_bound : ∀ (k : Fin 4), ‖(coarseTube k).base‖ ≤ 23 := by
    intro k
    have hk3 : (k : ℝ) ≤ 3 := by exact_mod_cast Fin.le_last k
    calc
      ‖(coarseTube k).base‖
        = ‖base0 + (k : ℝ) • dir_pos‖ := by rfl
      _ ≤ ‖base0‖ + ‖(k : ℝ) • dir_pos‖ := norm_add_le _ _
      _ = ‖base0‖ + (k : ℝ) * ‖dir_pos‖ := by
        rw [norm_smul] <;> simp [Real.norm_eq_abs] <;> ring
      _ = ‖base0‖ + (k : ℝ) := by rw [hdir_pos_unit] <;> ring
      _ ≤ 23 := by
        have h_k3 : (k : ℝ) ≤ 3 := by exact_mod_cast Fin.le_last k
        have h : ‖base0‖ + (k : ℝ) ≤ 23 := by
          have h2 : ‖base0‖ < 20 := h_base0_bound
          linarith
        exact h

  have h_params_eq : ∀ (k : Fin 4),
      tubeParamsOfTube (coarseTube k) = tubeParams reference := by
    intro k
    have hbase0 : (coarseTube k).base 0 = a + c * (coarseTube k).base 2 := (h_base_k_coords k).1
    have hbase1 : (coarseTube k).base 1 = b + d * (coarseTube k).base 2 := (h_base_k_coords k).2
    have hdir0 : (coarseTube k).direction 0 = c / norm := by
      simp [coarseTube, dir_pos, point3]
    have hdir1 : (coarseTube k).direction 1 = d / norm := by
      simp [coarseTube, dir_pos, point3]
    have hdir2 : (coarseTube k).direction 2 = 1 / norm := by
      simp [coarseTube, dir_pos, point3]
    have hdir2_ne : (coarseTube k).direction 2 ≠ 0 := by
      rw [hdir2] <;> positivity
    apply TubeParams.ext
    · simp [tubeParamsOfTube, hbase0, hdir0, hdir2]
      <;> field_simp [hdir2_ne] <;> ring
    · simp [tubeParamsOfTube, hbase1, hdir1, hdir2]
      <;> field_simp [hdir2_ne] <;> ring
    · simp [tubeParamsOfTube, hdir0, hdir2]
      <;> field_simp [hdir2_ne] <;> ring
    · simp [tubeParamsOfTube, hdir1, hdir2]
      <;> field_simp [hdir2_ne] <;> ring

  have h_vertical : IsInVerticalChart coarse := by
    intro i
    have h : (1 / 2 : ℝ) ≤ |dir_pos 2| := by
      rw [hdir_pos2]
      have h' : 0 < 1 / norm := by positivity
      rw [abs_of_pos h']
      have h'' : 1 / norm ≥ 1 / 2 := by
        gcongr <;> linarith
      exact h''
    exact h

  have h_base23 : HasBoundedBase coarse 23 := h_base_bound

  have h_distinct : coarse.IsEssentiallyDistinct := by
    intro i j hne
    by_cases hlt : i < j
    · have hsep : (i : ℝ) + 1 ≤ (j : ℝ) := by
        exact_mod_cast Nat.succ_le_iff.mpr hlt
      exact coaxial_shifted_ordered_essentiallyDistinct hrho hrho_small base0 dir_pos hdir_pos_unit hsep
    · have hgt : j < i := by
        exact lt_of_le_of_ne (Nat.le_of_not_gt hlt) hne.symm
      have hsep : (j : ℝ) + 1 ≤ (i : ℝ) := by
        exact_mod_cast Nat.succ_le_iff.mpr hgt
      have h := coaxial_shifted_ordered_essentiallyDistinct hrho hrho_small base0 dir_pos hdir_pos_unit hsep
      exact essentiallyDistinct_symm.mp h

  have h_cover : ∀ (index : Fin family.card), index ∈ indices →
      shading.carrier index ⊆ coarse.toBodyFamily.union := by
    simpa only [coarse] using
      window_parameter_cell_shading_cover
        hdelta hvert shading hslope indices reference mesh
        hmesh_nonneg hbudget hclose norm hnorm_pos hnorm2
        dir_pos base0 rfl rfl coarseTube
        (fun _ => rfl) (fun _ => rfl)

  refine ⟨coarse, rfl, h_distinct, h_vertical, h_base23, h_params_eq, h_cover⟩

end Kakeya.Assouad
