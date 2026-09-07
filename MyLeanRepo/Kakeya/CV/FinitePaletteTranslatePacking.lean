import MyLeanRepo.Kakeya.CV.UnitCubeEllipsoidPacking

/-!
# Uniform translate packings for a finite ellipsoid palette

The finitely many palette shapes share one common sufficiently small scale.
At that scale, the unit-cube packing theorem supplies a finite translate
family for every palette element and every cube center.
-/

noncomputable section

namespace Kakeya.CV

theorem finite_palette_translate_packing
    (hPacking : UnitCubeEllipsoidPackingStatement) :
    FinitePaletteTranslatePackingStatement := by
  classical
  rcases hPacking with ⟨C, hC, hpack⟩
  refine ⟨C, hC, ?_⟩
  intro palette _hpalette hcenter R ηMax hR hηMax houter
  let R' : ℝ := max R 1
  have hR'_pos : 0 < R' := lt_of_lt_of_le (by norm_num) (le_max_right R 1)
  have hR_le : R ≤ R' := le_max_left R 1
  have hR'_one : 1 ≤ R' := le_max_right R 1
  let η : ℝ := min ηMax 1 / (8 * R')
  have hη : 0 < η := by positivity
  have hη_le : η ≤ ηMax := by
    have hmin_pos : 0 < min ηMax 1 := lt_min hηMax (by norm_num)
    have hden : 1 ≤ 8 * R' := by nlinarith
    calc
      η ≤ min ηMax 1 := by
        dsimp [η]
        exact div_le_self hmin_pos.le hden
      _ ≤ ηMax := min_le_left _ _
  have hcontain : ∀ E ∈ palette,
      scaledEllipsoid E.2 (4 * η) 0 ⊆ unitBall 3 := by
    intro E hE z hz
    rcases (mem_scaledEllipsoid_iff E.2 (4 * η) 0 z).mp hz with
      ⟨y, hy, rfl⟩
    have hEcenter : E.1 = 0 := hcenter E hE
    have hA_bound : ∀ x : Point 3, ‖E.2 x‖ ≤ R * ‖x‖ := by
      intro x
      by_cases hx : x = 0
      · simp [hx]
      · have hx_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx
        let u : Point 3 := ‖x‖⁻¹ • x
        have hu_norm : ‖u‖ = 1 := by
          simp [u, norm_smul, hx_pos.ne']
        have hAu_mem : E.2 u ∈ ellipsoidCarrier E := by
          simp [ellipsoidCarrier, hEcenter, JohnEllipsoid.ellipsoid_mem_iff,
            hu_norm]
        have hAu : ‖E.2 u‖ ≤ R := by
          simpa [Metric.mem_closedBall] using houter E hE hAu_mem
        have hscale : E.2 u = ‖x‖⁻¹ • E.2 x := by
          simp [u, E.2.map_smul]
        rw [hscale, norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr hx_pos)] at hAu
        calc
          ‖E.2 x‖ = ‖x‖ * (‖x‖⁻¹ * ‖E.2 x‖) := by
            field_simp [hx_pos.ne']
          _ ≤ ‖x‖ * R := by gcongr
          _ = R * ‖x‖ := by ring
    have hscale_bound : 4 * η * R' ≤ 1 / 2 := by
      dsimp [η, R']
      have hmin : min ηMax 1 ≤ 1 := min_le_right _ _
      have hmax_pos : 0 < max R 1 := hR'_pos
      field_simp [hmax_pos.ne']
      nlinarith
    have hz_norm : ‖E.2 y‖ ≤ 1 := by
      calc
        ‖E.2 y‖ ≤ R * ‖y‖ := hA_bound y
        _ ≤ R * (4 * η) := by gcongr
        _ ≤ R' * (4 * η) := by gcongr
        _ = 4 * η * R' := by ring
        _ ≤ 1 / 2 := hscale_bound
        _ ≤ 1 := by norm_num
    simpa [unitBall, Metric.mem_closedBall] using hz_norm
  change 0 < min ηMax 1 / (8 * max R 1) ∧
      min ηMax 1 / (8 * max R 1) ≤ ηMax ∧ _
  refine ⟨hη, hη_le, ?_⟩
  intro E hE c
  exact hpack E.2 η c hη (hcontain E hE)

end Kakeya.CV
