import MyLeanRepo.Kakeya.Assouad.Subunit.HairbrushSelfContainedLeaves
import MyLeanRepo.Kakeya.Assouad.Hairbrush.CrossSectionBound

/-!
# Hard-branch fixed-proportion far radius

This is the quantitative step after (B.20).  The density lower bound forces
the homogeneous two-ends radius to be much larger than `δ`; choose a small
fixed proportion of `sigma * radius` as the far-cylinder radius and use the
absolute two-ends estimate to make the containing-ball mass at most one
quarter.

No inverse power of `δ` belongs in this proof.
-/

noncomputable section

open MeasureTheory Metric Set Real

namespace Kakeya.Assouad

theorem hairbrush_homogeneous_far_radius :
    HairbrushHomogeneousFarRadiusStatement := by
  intro zeta familyLoss hzeta_pos hzeta_lt_one
  set q : ℝ := (1 / 64 : ℝ) ^ (1 / zeta) with hq_def
  have hq_pos : 0 < q := by positivity
  have hq_lt_one : q < 1 := by
    have h1 : (1 / 64 : ℝ) < (1 : ℝ) := by norm_num
    have h2 : 0 < 1 / zeta := by positivity
    have h3 : (1 / 64 : ℝ) ^ (1 / zeta) < (1 : ℝ) ^ (1 / zeta) :=
      Real.rpow_lt_rpow (by norm_num) h1 h2
    have h4 : (1 : ℝ) ^ (1 / zeta) = 1 := by simp
    rw [h4] at h3
    exact h3
  have hq_rpow : Real.rpow q zeta = 1 / 64 := by
    have h_pos : (0 : ℝ) ≤ 1 / 64 := by norm_num
    have h_mul : Real.rpow (1 / 64 : ℝ) ((1 / zeta) * zeta) =
        Real.rpow (Real.rpow (1 / 64 : ℝ) (1 / zeta)) zeta :=
      Real.rpow_mul h_pos (1 / zeta) zeta
    have h3 : (1 / zeta) * zeta = 1 := by
      field_simp [hzeta_pos.ne']
    have h4 : Real.rpow (1 / 64 : ℝ) ((1 / zeta) * zeta) = 1 / 64 := by
      rw [h3]; simp
    have h5 : Real.rpow (Real.rpow (1 / 64 : ℝ) (1 / zeta)) zeta = 1 / 64 := by
      rw [← h_mul, h4]
    simpa [hq_def] using h5
  set farFraction : ℝ := q / (4 * Real.pi) with hff_def
  have hff_pos : 0 < farFraction := by positivity
  have hff_le_one : farFraction ≤ 1 := by
    have h1 : q < 1 := hq_lt_one
    have h2 : q / (4 * Real.pi) < 1 := by
      calc
        q / (4 * Real.pi) < 1 / (4 * Real.pi) := by gcongr
        _ ≤ 1 := by
          have h3 : 1 ≤ 4 * Real.pi := by linarith [Real.pi_gt_three]
          exact (div_le_one (by positivity)).mpr h3
    exact h2.le
  set separation : ℝ := max 1000 ((16 + 12 * Real.pi) / q + 1) with hsep_def
  have hsep_ge : 1000 ≤ separation := le_max_left _ _
  have hsep_gt : (16 + 12 * Real.pi) / q < separation := by
    have h1 : (16 + 12 * Real.pi) / q + 1 ≤ separation := le_max_right _ _
    linarith
  have hsep_pos : 0 < separation := by positivity
  have hsep_gt_inv : 1 / separation < q := by
    have h2 : 1 < (16 + 12 * Real.pi) := by linarith [Real.pi_pos]
    have h3 : 1 / q < (16 + 12 * Real.pi) / q := by gcongr
    have h4 : 1 / q < separation := lt_trans h3 hsep_gt
    have h5 : 0 < q := hq_pos
    calc
      1 / separation < 1 / (1 / q) := by gcongr
      _ = q := by field_simp [h5.ne']
  refine' ⟨separation, farFraction, hsep_ge, hff_pos, hff_le_one, _⟩
  intro δ hδ sigma hsigma hsigma_le_one H Z hairDensity twoEnds h
  set farRadius : ℝ := farFraction * sigma * twoEnds.radius with hfar_def
  set nearRadius : ℝ := q * twoEnds.radius with hnear_def
  have hradius_pos : 0 < twoEnds.radius := by
    have h1 : 0 < δ := hδ
    have h2 : δ ≤ twoEnds.radius := twoEnds.delta_le_radius
    linarith
  have hfar_pos : 0 < farRadius := by positivity
  have hnear_pos : 0 < nearRadius := by positivity
  have hdelta_le_near : δ ≤ nearRadius := by
    have h1 : separation * δ ≤ sigma * twoEnds.radius := h
    have h2 : sigma * twoEnds.radius ≤ twoEnds.radius := by
      have h21 : sigma ≤ 1 := hsigma_le_one
      nlinarith
    have h3 : separation * δ ≤ twoEnds.radius := le_trans h1 h2
    have h4 : δ ≤ twoEnds.radius / separation := by
      calc
        δ = (separation * δ) / separation := by field_simp [hsep_pos.ne']
        _ ≤ twoEnds.radius / separation := by gcongr
    have h5 : twoEnds.radius / separation < q * twoEnds.radius := by
      have h6 : 0 < twoEnds.radius := hradius_pos
      have h7 : 1 / separation < q := hsep_gt_inv
      have h8 : twoEnds.radius / separation = twoEnds.radius * (1 / separation) := by
        field_simp
      rw [h8]
      nlinarith
    linarith
  have hnear_le_two : nearRadius ≤ 2 := by
    have h1 : q < 1 := hq_lt_one
    have h2 : twoEnds.radius ≤ 2 := twoEnds.radius_le_two
    nlinarith
  have hnear_ball_mass : ∀ U ∈ twoEnds.family, ∀ x : Point3,
      volume (twoEnds.shading.carrier U ∩ Metric.ball x nearRadius) ≤
        (1 / 4 : ENNReal) * volume (twoEnds.shading.carrier U) := by
    intro U hU x
    have h1 : volume (twoEnds.shading.carrier U ∩ Metric.ball x nearRadius) ≤
        ENNReal.ofReal 4 * ENNReal.ofReal (Real.rpow (nearRadius / twoEnds.radius) zeta) *
          volume (twoEnds.shading.carrier U) :=
      twoEnds.two_ends U hU x nearRadius hdelta_le_near hnear_le_two
    have h2 : nearRadius / twoEnds.radius = q := by
      simp only [hnear_def]
      field_simp [hradius_pos.ne']
    rw [h2] at h1
    rw [hq_rpow] at h1
    have hcoeff : ENNReal.ofReal 4 * ENNReal.ofReal (1 / 64 : ℝ) = ENNReal.ofReal (1 / 16 : ℝ) := by
      have h : ENNReal.ofReal 4 * ENNReal.ofReal (1 / 64 : ℝ) = ENNReal.ofReal (4 * (1 / 64 : ℝ)) := by
        rw [← ENNReal.ofReal_mul (by norm_num)]
      rw [h]; norm_num
    rw [hcoeff] at h1
    have hle : ENNReal.ofReal (1 / 16 : ℝ) ≤ ENNReal.ofReal (1 / 4 : ℝ) :=
      ENNReal.ofReal_le_ofReal (by norm_num)
    have hfinal : ENNReal.ofReal (1 / 16 : ℝ) * volume (twoEnds.shading.carrier U) ≤
        ENNReal.ofReal (1 / 4 : ℝ) * volume (twoEnds.shading.carrier U) :=
      mul_le_mul_of_nonneg_right hle (by positivity)
    have hquarter : (1 / 4 : ENNReal) = ENNReal.ofReal (1 / 4 : ℝ) := by simp
    rw [hquarter]
    exact le_trans h1 hfinal
  have hgeom : 2 * δ + Real.pi * (farRadius + 3 * δ) / (2 * sigma) < nearRadius := by
    have h1 : δ ≤ sigma * twoEnds.radius / separation := by
      calc
        δ = (separation * δ) / separation := by field_simp [hsep_pos.ne']
        _ ≤ (sigma * twoEnds.radius) / separation := by gcongr
    have h3 : 2 * δ ≤ 2 * twoEnds.radius / separation := by
      calc
        2 * δ ≤ 2 * (sigma * twoEnds.radius / separation) := by gcongr
        _ = 2 * sigma * twoEnds.radius / separation := by ring
        _ ≤ 2 * twoEnds.radius / separation := by
          have h4 : 2 * sigma ≤ 2 := by linarith
          gcongr
    have h4 : 3 * Real.pi * δ / (2 * sigma) ≤ 3 * Real.pi * twoEnds.radius / (2 * separation) := by
      calc
        3 * Real.pi * δ / (2 * sigma)
          ≤ 3 * Real.pi * (sigma * twoEnds.radius / separation) / (2 * sigma) := by gcongr
        _ = 3 * Real.pi * twoEnds.radius / (2 * separation) := by
          field_simp [hsigma.ne']
    have h5 : Real.pi * farRadius / (2 * sigma) = q * twoEnds.radius / 8 := by
      simp only [hfar_def, hff_def]
      field_simp [hsigma.ne', Real.pi_ne_zero]; ring
    have h6 : 2 * δ + Real.pi * (farRadius + 3 * δ) / (2 * sigma) ≤
        twoEnds.radius * (q / 8 + (2 + 3 * Real.pi / 2) / separation) := by
      have h7 : Real.pi * (farRadius + 3 * δ) / (2 * sigma) =
          Real.pi * farRadius / (2 * sigma) + 3 * Real.pi * δ / (2 * sigma) := by ring
      calc
        2 * δ + Real.pi * (farRadius + 3 * δ) / (2 * sigma)
          = 2 * δ + (Real.pi * farRadius / (2 * sigma) + 3 * Real.pi * δ / (2 * sigma)) := by rw [h7]
        _ ≤ 2 * twoEnds.radius / separation + (q * twoEnds.radius / 8 + 3 * Real.pi * twoEnds.radius / (2 * separation)) := by
          linarith [h3, h4, h5]
        _ = twoEnds.radius * (q / 8 + (2 + 3 * Real.pi / 2) / separation) := by ring
    have h8 : (2 + 3 * Real.pi / 2) / separation < q / 8 := by
      have h9 : (16 + 12 * Real.pi) = 8 * (2 + 3 * Real.pi / 2) := by ring
      have h10 : 8 * (2 + 3 * Real.pi / 2) / q < separation := by
        rw [← h9]; exact hsep_gt
      have h11 : 0 < 2 + 3 * Real.pi / 2 := by positivity
      have h12 : 0 < q := hq_pos
      calc
        (2 + 3 * Real.pi / 2) / separation
          < (2 + 3 * Real.pi / 2) / (8 * (2 + 3 * Real.pi / 2) / q) := by gcongr
        _ = q / 8 := by field_simp [h11.ne', h12.ne']
    have h9 : twoEnds.radius * (q / 8 + (2 + 3 * Real.pi / 2) / separation) <
        twoEnds.radius * (q / 8 + q / 8) := by
      gcongr
    have h10 : twoEnds.radius * (q / 8 + q / 8) = twoEnds.radius * (q / 4) := by ring
    have h11 : twoEnds.radius * (q / 4) < q * twoEnds.radius := by
      have h12 : 0 < twoEnds.radius := hradius_pos
      have h13 : 0 < q := hq_pos
      nlinarith
    calc
      2 * δ + Real.pi * (farRadius + 3 * δ) / (2 * sigma)
        ≤ twoEnds.radius * (q / 8 + (2 + 3 * Real.pi / 2) / separation) := h6
      _ < twoEnds.radius * (q / 8 + q / 8) := h9
      _ = twoEnds.radius * (q / 4) := h10
      _ < q * twoEnds.radius := h11
      _ = nearRadius := by simp [hnear_def]
  exact ⟨farRadius, nearRadius, hfar_pos, hnear_pos, rfl, hnear_ball_mass, hgeom⟩

end Kakeya.Assouad
