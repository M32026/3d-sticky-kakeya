import MyLeanRepo.Kakeya.Cinematic.Section5.LinearAmbientFineVolumeAssemblyInputs

/-!
# Linear fixed-ambient fine-volume assembly
-/

open MeasureTheory

namespace Kakeya.Cinematic

theorem linear_ambient_fine_volume_assembly :
    LinearAmbientFineVolumeAssemblyStatement := by
  intro E fineCard ambientCard cardCoefficient area hcc ha hcard hvol
  have h1 :
      (fineCard : ENNReal) ≤
        (ambientCard : ENNReal) *
          ENNReal.ofReal cardCoefficient := by
    have h1a :
        (fineCard : ENNReal) =
          ENNReal.ofReal (fineCard : ℝ) := by
      simp
    rw [h1a]
    have h1b :
        ENNReal.ofReal (fineCard : ℝ) ≤
          ENNReal.ofReal
            ((ambientCard : ℝ) * cardCoefficient) :=
      ENNReal.ofReal_le_ofReal hcard
    have h1c :
        ENNReal.ofReal
            ((ambientCard : ℝ) * cardCoefficient) =
          (ambientCard : ENNReal) *
            ENNReal.ofReal cardCoefficient := by
      have h_eq1 :
          ENNReal.ofReal
              ((ambientCard : ℝ) * cardCoefficient) =
            ENNReal.ofReal (ambientCard : ℝ) *
              ENNReal.ofReal cardCoefficient :=
        ENNReal.ofReal_mul
          (show 0 ≤ (ambientCard : ℝ) from by positivity)
      have h_eq2 :
          ENNReal.ofReal (ambientCard : ℝ) =
            (ambientCard : ENNReal) := by
        simp
      rw [h_eq1, h_eq2]
    exact h1c ▸ h1b
  have h2 :
      (fineCard : ENNReal) * ENNReal.ofReal area ≤
        ENNReal.ofReal (cardCoefficient * area) *
          (ambientCard : ENNReal) := by
    calc
      (fineCard : ENNReal) * ENNReal.ofReal area ≤
          ((ambientCard : ENNReal) *
            ENNReal.ofReal cardCoefficient) *
              ENNReal.ofReal area := by
        have h := mul_le_mul_right h1 (ENNReal.ofReal area)
        simpa [mul_comm] using h
      _ =
          (ambientCard : ENNReal) *
            (ENNReal.ofReal cardCoefficient *
              ENNReal.ofReal area) := by
        ring
      _ =
          (ambientCard : ENNReal) *
            ENNReal.ofReal (cardCoefficient * area) := by
        have hmul :
            ENNReal.ofReal cardCoefficient *
                ENNReal.ofReal area =
              ENNReal.ofReal (cardCoefficient * area) := by
          rw [← ENNReal.ofReal_mul hcc]
        rw [hmul]
      _ =
          ENNReal.ofReal (cardCoefficient * area) *
            (ambientCard : ENNReal) := by
        ring
  exact le_trans hvol h2

end Kakeya.Cinematic
