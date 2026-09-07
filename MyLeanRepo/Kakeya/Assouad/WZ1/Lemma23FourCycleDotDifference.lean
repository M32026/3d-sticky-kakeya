import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23DotDifferenceStatements

/-!
# Telescope the WZ1 Lemma 23 four-cycle dot difference

The three local/global grain errors and the base global-grain error telescope
to the dot difference used by the projection theorem.
-/

namespace Kakeya.Assouad

theorem wz1_lemma23_four_cycle_dot_difference :
    WZ1Lemma23FourCycleDotDifferenceStatement := by
  intro rho w f g p₁ p₂ p₃ p₄ h_rho
    h_p1_z h_p4_z h_p2_y1 h_p4_y3 h_p3_z
    h_base h_local12 h_global23 h_local34

  set z : ℝ := p₂ 2 with hz
  set y₁ : ℝ := p₁ 1 with hy₁
  set y₃ : ℝ := p₃ 1 with hy₃

  have h_p3_z' : p₃ 2 = z := by
    simpa [hz] using h_p3_z
  have h_p2_y1' : p₂ 1 = y₁ := by
    simpa [hy₁] using h_p2_y1
  have h_p4_y3' : p₄ 1 = y₃ := by
    simpa [hy₃] using h_p4_y3

  let dot := inner ℝ (wz1Lemma23HeightGraphPoint f z)
      (wz1Lemma23LocalGraphPoint g y₁ - wz1Lemma23LocalGraphPoint g y₃)

  have h_dot : dot = -z * (g y₁ - g y₃) + (y₁ - y₃) * f z := by
    simp [dot, wz1Lemma23HeightGraphPoint, wz1Lemma23LocalGraphPoint,
      PiLp.inner_apply, Fin.sum_univ_two]
    ring

  let local12 :=
    wz1Lemma23LocalCoordinate g p₁ - wz1Lemma23LocalCoordinate g p₂
  let global23 :=
    wz1Lemma23GlobalCoordinate f p₂ - wz1Lemma23GlobalCoordinate f p₃
  let local34 :=
    wz1Lemma23LocalCoordinate g p₃ - wz1Lemma23LocalCoordinate g p₄

  have h_telescope :
      local12 + global23 + local34 = p₁ 0 - p₄ 0 + dot := by
    simp [local12, global23, local34,
      wz1Lemma23LocalCoordinate, wz1Lemma23GlobalCoordinate,
      h_p1_z, h_p4_z, hz, h_p3_z', h_p2_y1', h_p4_y3', h_dot]
    ring

  have h_main :
      dot - (p₄ 0 - w) =
        local12 + global23 + local34 - (p₁ 0 - w) := by
    linarith [h_telescope]

  rw [h_main]

  have h1 : -rho ≤ local12 := by linarith [abs_le.mp h_local12]
  have h2 : local12 ≤ rho := by linarith [abs_le.mp h_local12]
  have h3 : -rho ≤ global23 := by linarith [abs_le.mp h_global23]
  have h4 : global23 ≤ rho := by linarith [abs_le.mp h_global23]
  have h5 : -rho ≤ local34 := by linarith [abs_le.mp h_local34]
  have h6 : local34 ≤ rho := by linarith [abs_le.mp h_local34]
  have h7 : -rho ≤ p₁ 0 - w := by linarith [abs_le.mp h_base]
  have h8 : p₁ 0 - w ≤ rho := by linarith [abs_le.mp h_base]

  have h_upper :
      local12 + global23 + local34 - (p₁ 0 - w) ≤ 4 * rho := by
    linarith
  have h_lower :
      -(4 * rho) ≤ local12 + global23 + local34 - (p₁ 0 - w) := by
    linarith

  exact abs_le.mpr ⟨h_lower, h_upper⟩

end Kakeya.Assouad
