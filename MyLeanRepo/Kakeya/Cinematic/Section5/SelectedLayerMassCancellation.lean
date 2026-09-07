import MyLeanRepo.Kakeya.Cinematic.Section5.SelectedLayerMassCancellationInputs

/-!
# Cancel the selected dyadic-layer mass
-/

namespace Kakeya.Cinematic

theorem selected_layer_mass_cancellation :
    SelectedLayerMassCancellationStatement := by
  intro coefficient parentArea fineArea layerMass hcoeff hparent hfine hlayer hle
  by_cases hc : coefficient = 0
  · rw [hc]
    simp
  · have hcoeff_pos : 0 < coefficient := lt_of_le_of_ne hcoeff (Ne.symm hc)
    have h_main : (parentArea / layerMass) ^ (1 / 4 : ℝ) * layerMass ≤
        parentArea ^ (1 / 4 : ℝ) * fineArea ^ (3 / 4 : ℝ) := by
      by_cases hp : parentArea = 0
      · have h1 : parentArea / layerMass = 0 := by rw [hp]; simp
        rw [h1]
        have h2 : (0 : ℝ) ^ (1 / 4 : ℝ) = 0 := Real.zero_rpow (by norm_num)
        rw [h2]
        simp
        positivity
      · have hparent_pos : 0 < parentArea := lt_of_le_of_ne hparent (Ne.symm hp)
        have h1 : (parentArea / layerMass) ^ (1 / 4 : ℝ) =
            parentArea ^ (1 / 4 : ℝ) / layerMass ^ (1 / 4 : ℝ) :=
          Real.div_rpow hparent (by linarith) (1 / 4 : ℝ)
        rw [h1]
        have h_add : layerMass ^ (3 / 4 : ℝ) * layerMass ^ (1 / 4 : ℝ) = layerMass := by
          have h5 := Real.rpow_add hlayer (3 / 4 : ℝ) (1 / 4 : ℝ)
          have h6 : (3 / 4 : ℝ) + (1 / 4 : ℝ) = 1 := by norm_num
          rw [h6] at h5
          simpa using h5.symm
        have h_pos1 : 0 < layerMass ^ (1 / 4 : ℝ) := by positivity
        have h_div : layerMass / layerMass ^ (1 / 4 : ℝ) = layerMass ^ (3 / 4 : ℝ) := by
          field_simp [h_pos1.ne']
          rw [mul_comm]
          exact h_add.symm
        have h3 : (parentArea ^ (1 / 4 : ℝ) / layerMass ^ (1 / 4 : ℝ)) * layerMass =
            parentArea ^ (1 / 4 : ℝ) * layerMass ^ (3 / 4 : ℝ) := by
          calc
            (parentArea ^ (1 / 4 : ℝ) / layerMass ^ (1 / 4 : ℝ)) * layerMass
              = parentArea ^ (1 / 4 : ℝ) * (layerMass / layerMass ^ (1 / 4 : ℝ)) := by ring
            _ = parentArea ^ (1 / 4 : ℝ) * layerMass ^ (3 / 4 : ℝ) := by rw [h_div]
        rw [h3]
        have h4 : layerMass ^ (3 / 4 : ℝ) ≤ fineArea ^ (3 / 4 : ℝ) :=
          Real.rpow_le_rpow (by linarith) hle (by norm_num)
        have h5 : 0 ≤ parentArea ^ (1 / 4 : ℝ) := by positivity
        exact mul_le_mul_of_nonneg_left h4 h5
    have h_final : coefficient * ((parentArea / layerMass) ^ (1 / 4 : ℝ) * layerMass) ≤
        coefficient * (parentArea ^ (1 / 4 : ℝ) * fineArea ^ (3 / 4 : ℝ)) :=
      mul_le_mul_of_nonneg_left h_main hcoeff
    simpa [mul_assoc] using h_final

end Kakeya.Cinematic
