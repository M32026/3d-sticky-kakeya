import MyLeanRepo.Kakeya.Assouad.WZ1.UnitRescaling

/-!
# Geometric bounds for the inverse-transpose transported normal

Helper lemmas for the anchored global-grain transport:
- `householder_reflected_coord2`: coordinate 2 of a Householder-reflected vector
- `transported_normal_geometric_bounds`: norm and vertical-component bounds
  for the inverse-transpose normal under the anchored unit rescaling.
-/

noncomputable section

namespace Kakeya.Assouad

/-- Coordinate 2 of Householder-reflected vector equals inner with original direction. -/
lemma householder_reflected_coord2
    {lineDir : Point3} (hd : ‖lineDir‖ = 1) (v : Point3) :
    (householderToE3 lineDir hd v) 2 = inner ℝ v lineDir := by
  have h1 : (householderToE3 lineDir hd v) 2 =
    inner ℝ (householderToE3 lineDir hd v) e3 := by
    have h := EuclideanSpace.inner_single_right (2 : Fin 3) (1 : ℝ)
        (householderToE3 lineDir hd v)
    simpa [e3] using h.symm
  rw [h1]
  have h2 : inner ℝ (householderToE3 lineDir hd v) e3 =
    inner ℝ v (householderToE3 lineDir hd e3) :=
    householderToE3_symmetric lineDir hd v e3
  rw [h2, householderToE3_sends_e3_to_d lineDir hd]

private lemma norm_sq_coord {w : Point3} :
    ‖w‖ ^ 2 = (w 0) ^ 2 + (w 1) ^ 2 + (w 2) ^ 2 := by
  have h1 : ‖w‖ ^ 2 = inner ℝ w w := by rw [← real_inner_self_eq_norm_sq]
  rw [h1]
  have h2 : inner ℝ w w = ∑ i : Fin 3, w i ^ 2 := by
    rw [EuclideanSpace.inner_eq_star_dotProduct] <;> simp [pow_two] <;> rfl
  rw [h2]
  simp [Fin.sum_univ_succ] <;> ring

/-- Geometric bounds for the transported normal. -/
lemma transported_normal_geometric_bounds
    {sourceDelta rho incidenceScale : ℝ}
    (anchor : Kakeya.DeltaTube sourceDelta)
    (v : Point3)
    (hv_norm : ‖v‖ = 1)
    (h_incidence : |inner ℝ v anchor.direction| ≤ incidenceScale)
    (h_rho_small : 100 * rho ≤ 1)
    (h_incidence_small : incidenceScale ≤ rho / 10)
    (h_incidence_nonneg : 0 ≤ incidenceScale)
    (hrho : 0 < rho) :
    ‖wz1AnchoredUnitRescalingNormalLinear anchor rho v‖ ≤ 1 ∧
    rho ≤ ‖wz1AnchoredUnitRescalingNormalLinear anchor rho v‖ ∧
    |((1 / ‖wz1AnchoredUnitRescalingNormalLinear anchor rho v‖) •
      wz1AnchoredUnitRescalingNormalLinear anchor rho v) 2| ≤ 1 / 10 := by
  let R := householderToE3 anchor.direction anchor.direction_unit
  let w : Point3 := R v
  let a : ℝ := 100 * rho
  have ha_pos : 0 < a := by positivity
  have ha_le_one : a ≤ 1 := h_rho_small
  set Nv : Point3 := wz1AnchoredUnitRescalingNormalLinear anchor rho v with hNv_def
  have hNv_eq : Nv = transverseScaleLin (1 / a) w := by rfl
  have h_coord0 : Nv 0 = a * w 0 := by
    rw [hNv_eq, transverseScaleLin_coord0] <;> field_simp [ha_pos.ne'] <;> ring
  have h_coord1 : Nv 1 = a * w 1 := by
    rw [hNv_eq, transverseScaleLin_coord1] <;> field_simp [ha_pos.ne'] <;> ring
  have h_coord2 : Nv 2 = w 2 := by
    rw [hNv_eq, transverseScaleLin_coord2]
  have h_w2 : w 2 = inner ℝ v anchor.direction :=
    householder_reflected_coord2 anchor.direction_unit v
  have h_abs_w2 : |w 2| ≤ incidenceScale := by
    rw [h_w2] <;> exact h_incidence
  have hR_norm : ‖w‖ = 1 := by
    have h := householderToE3_norm anchor.direction anchor.direction_unit v
    rw [hv_norm] at h
    exact h
  have h_sum_sq : (w 0) ^ 2 + (w 1) ^ 2 + (w 2) ^ 2 = 1 := by
    have h : ‖w‖ ^ 2 = (w 0) ^ 2 + (w 1) ^ 2 + (w 2) ^ 2 := norm_sq_coord
    rw [hR_norm] at h
    norm_num at h ⊢ <;> linarith
  have h_horiz_sq : (w 0) ^ 2 + (w 1) ^ 2 = 1 - (w 2) ^ 2 := by linarith
  have h_norm_sq : ‖Nv‖ ^ 2 = a ^ 2 * ((w 0) ^ 2 + (w 1) ^ 2) + (w 2) ^ 2 := by
    have h : ‖Nv‖ ^ 2 = (Nv 0) ^ 2 + (Nv 1) ^ 2 + (Nv 2) ^ 2 := norm_sq_coord
    rw [h, h_coord0, h_coord1, h_coord2] <;> ring
  have h_main : ‖Nv‖ ^ 2 = a ^ 2 + (1 - a ^ 2) * (w 2) ^ 2 := by
    rw [h_norm_sq, h_horiz_sq] <;> ring
  have h1 : ‖Nv‖ ^ 2 ≤ 1 := by
    rw [h_main]
    have h1a : 0 ≤ 1 - a ^ 2 := by nlinarith
    have h1b : (w 2) ^ 2 ≤ 1 := by nlinarith [h_sum_sq]
    nlinarith
  have hNv_nonneg : 0 ≤ ‖Nv‖ := by positivity
  have h_le_one : ‖Nv‖ ≤ 1 := by nlinarith
  have h2 : a ^ 2 ≤ ‖Nv‖ ^ 2 := by
    rw [h_main]
    have h2a : 0 ≤ 1 - a ^ 2 := by nlinarith
    have h2b : 0 ≤ (w 2) ^ 2 := by positivity
    nlinarith
  have h_ge_a : a ≤ ‖Nv‖ := by nlinarith
  have h_ge_rho : rho ≤ ‖Nv‖ := by
    have h5 : rho ≤ a := by dsimp only [a] <;> linarith
    exact h5.trans h_ge_a
  have hNv_pos : 0 < ‖Nv‖ := by
    have h6 : 0 < a := ha_pos
    exact h6.trans_le h_ge_a
  let n : Point3 := (1 / ‖Nv‖) • Nv
  have h_n2 : n 2 = (w 2) / ‖Nv‖ := by
    simp [n, h_coord2] <;> ring
  have h_abs_n2 : |n 2| ≤ 1 / 10 := by
    rw [h_n2]
    have h7 : |(w 2) / ‖Nv‖| = |w 2| / ‖Nv‖ := by
      rw [abs_div, abs_of_nonneg (show 0 ≤ ‖Nv‖ by positivity)]
    rw [h7]
    have h8 : |w 2| / ‖Nv‖ ≤ incidenceScale / a := by
      have h81 : |w 2| ≤ incidenceScale := h_abs_w2
      have h82 : 0 < ‖Nv‖ := hNv_pos
      have h83 : 0 < a := ha_pos
      calc
        |w 2| / ‖Nv‖ ≤ incidenceScale / ‖Nv‖ := by gcongr
        _ ≤ incidenceScale / a := by gcongr <;> linarith
    have h9 : incidenceScale / a ≤ 1 / 10 := by
      dsimp only [a]
      have h10 : incidenceScale ≤ rho / 10 := h_incidence_small
      have h11 : incidenceScale / (100 * rho) ≤ (rho / 10) / (100 * rho) := by gcongr
      have h12 : (rho / 10) / (100 * rho) = 1 / 1000 := by
        field_simp [hrho.ne'] <;> ring
      rw [h12] at h11
      linarith
    exact h8.trans h9
  exact ⟨h_le_one, h_ge_rho, h_abs_n2⟩

/--
Weakened geometric bounds for the transported normal.

Same conclusion as `transported_normal_geometric_bounds`, but only requires
`incidenceScale ≤ 10 * rho` instead of `incidenceScale ≤ rho / 10`.
The vertical bound calculation becomes `incidenceScale / (100*rho) ≤ (10*rho)/(100*rho) = 1/10`.
-/
lemma transported_normal_geometric_bounds_weak
    {sourceDelta rho incidenceScale : ℝ}
    (anchor : Kakeya.DeltaTube sourceDelta)
    (v : Point3)
    (hv_norm : ‖v‖ = 1)
    (h_incidence : |inner ℝ v anchor.direction| ≤ incidenceScale)
    (h_rho_small : 100 * rho ≤ 1)
    (h_incidence_small : incidenceScale ≤ 10 * rho)
    (h_incidence_nonneg : 0 ≤ incidenceScale)
    (hrho : 0 < rho) :
    ‖wz1AnchoredUnitRescalingNormalLinear anchor rho v‖ ≤ 1 ∧
    rho ≤ ‖wz1AnchoredUnitRescalingNormalLinear anchor rho v‖ ∧
    |((1 / ‖wz1AnchoredUnitRescalingNormalLinear anchor rho v‖) •
      wz1AnchoredUnitRescalingNormalLinear anchor rho v) 2| ≤ 1 / 10 := by
  let R := householderToE3 anchor.direction anchor.direction_unit
  let w : Point3 := R v
  let a : ℝ := 100 * rho
  have ha_pos : 0 < a := by positivity
  have ha_le_one : a ≤ 1 := h_rho_small
  set Nv : Point3 := wz1AnchoredUnitRescalingNormalLinear anchor rho v with hNv_def
  have hNv_eq : Nv = transverseScaleLin (1 / a) w := by rfl
  have h_coord0 : Nv 0 = a * w 0 := by
    rw [hNv_eq, transverseScaleLin_coord0] <;> field_simp [ha_pos.ne'] <;> ring
  have h_coord1 : Nv 1 = a * w 1 := by
    rw [hNv_eq, transverseScaleLin_coord1] <;> field_simp [ha_pos.ne'] <;> ring
  have h_coord2 : Nv 2 = w 2 := by
    rw [hNv_eq, transverseScaleLin_coord2]
  have h_w2 : w 2 = inner ℝ v anchor.direction :=
    householder_reflected_coord2 anchor.direction_unit v
  have h_abs_w2 : |w 2| ≤ incidenceScale := by
    rw [h_w2] <;> exact h_incidence
  have hR_norm : ‖w‖ = 1 := by
    have h := householderToE3_norm anchor.direction anchor.direction_unit v
    rw [hv_norm] at h
    exact h
  have h_sum_sq : (w 0) ^ 2 + (w 1) ^ 2 + (w 2) ^ 2 = 1 := by
    have h : ‖w‖ ^ 2 = (w 0) ^ 2 + (w 1) ^ 2 + (w 2) ^ 2 := norm_sq_coord
    rw [hR_norm] at h
    norm_num at h ⊢ <;> linarith
  have h_norm_sq : ‖Nv‖ ^ 2 = a ^ 2 * ((w 0) ^ 2 + (w 1) ^ 2) + (w 2) ^ 2 := by
    have h : ‖Nv‖ ^ 2 = (Nv 0) ^ 2 + (Nv 1) ^ 2 + (Nv 2) ^ 2 := norm_sq_coord
    rw [h, h_coord0, h_coord1, h_coord2] <;> ring
  have h_horiz_sq : (w 0) ^ 2 + (w 1) ^ 2 = 1 - (w 2) ^ 2 := by linarith
  have h_main : ‖Nv‖ ^ 2 = a ^ 2 + (1 - a ^ 2) * (w 2) ^ 2 := by
    rw [h_norm_sq, h_horiz_sq] <;> ring
  have h1 : ‖Nv‖ ^ 2 ≤ 1 := by
    rw [h_main]
    have h1a : 0 ≤ 1 - a ^ 2 := by nlinarith
    have h1b : (w 2) ^ 2 ≤ 1 := by nlinarith [h_sum_sq]
    nlinarith
  have hNv_nonneg : 0 ≤ ‖Nv‖ := by positivity
  have h_le_one : ‖Nv‖ ≤ 1 := by nlinarith
  have h2 : a ^ 2 ≤ ‖Nv‖ ^ 2 := by
    rw [h_main]
    have h2a : 0 ≤ 1 - a ^ 2 := by nlinarith
    have h2b : 0 ≤ (w 2) ^ 2 := by positivity
    nlinarith
  have h_ge_a : a ≤ ‖Nv‖ := by nlinarith
  have h_ge_rho : rho ≤ ‖Nv‖ := by
    have h5 : rho ≤ a := by dsimp only [a] <;> linarith
    exact h5.trans h_ge_a
  have hNv_pos : 0 < ‖Nv‖ := by
    have h6 : 0 < a := ha_pos
    exact h6.trans_le h_ge_a
  let n : Point3 := (1 / ‖Nv‖) • Nv
  have h_n2 : n 2 = (w 2) / ‖Nv‖ := by
    simp [n, h_coord2] <;> ring
  have h_abs_n2 : |n 2| ≤ 1 / 10 := by
    rw [h_n2]
    have h7 : |(w 2) / ‖Nv‖| = |w 2| / ‖Nv‖ := by
      rw [abs_div, abs_of_nonneg (show 0 ≤ ‖Nv‖ by positivity)]
    rw [h7]
    have h8 : |w 2| / ‖Nv‖ ≤ incidenceScale / a := by
      have h81 : |w 2| ≤ incidenceScale := h_abs_w2
      have h82 : 0 < ‖Nv‖ := hNv_pos
      have h83 : 0 < a := ha_pos
      calc
        |w 2| / ‖Nv‖ ≤ incidenceScale / ‖Nv‖ := by gcongr
        _ ≤ incidenceScale / a := by gcongr <;> linarith
    have h9 : incidenceScale / a ≤ 1 / 10 := by
      dsimp only [a]
      have h10 : incidenceScale ≤ 10 * rho := h_incidence_small
      have h11 : incidenceScale / (100 * rho) ≤ (10 * rho) / (100 * rho) := by gcongr
      have h12 : (10 * rho) / (100 * rho) = 1 / 10 := by
        field_simp [hrho.ne'] <;> ring
      rw [h12] at h11
      exact h11
    exact h8.trans h9
  exact ⟨h_le_one, h_ge_rho, h_abs_n2⟩

end Kakeya.Assouad
