import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedSelectedLocalVolumeBranchesInputs

/-!
# Absorb both fixed-bin volume branches into one local target
-/

open MeasureTheory

namespace Kakeya.Cinematic

theorem ambient_restricted_local_target_branches
    {bin : Set (ℝ × ℝ)}
    {ambientCard : ℕ}
    {positiveCoefficient singletonCoefficient localTarget : ℝ}
    (hresult :
      AmbientRestrictedSelectedLocalVolumeResult
        bin ambientCard positiveCoefficient singletonCoefficient)
    (hpositive : positiveCoefficient ≤ localTarget)
    (hsingleton : singletonCoefficient ≤ localTarget) :
    volume bin ≤ ENNReal.ofReal localTarget * ambientCard := by
  cases hresult with
  | positive hvolume =>
      exact hvolume.trans <|
        mul_le_mul_right'
          (ENNReal.ofReal_le_ofReal hpositive)
          (ambientCard : ENNReal)
  | singleton hvolume =>
      exact hvolume.trans <|
        mul_le_mul_right'
          (ENNReal.ofReal_le_ofReal hsingleton)
          (ambientCard : ENNReal)

theorem ambient_restricted_scaled_local_target_branches
    {bin : Set (ℝ × ℝ)}
    {ambientCard : ℕ}
    {positiveCoefficient singletonCoefficient outerLoss localTarget : ℝ}
    (hresult :
      AmbientRestrictedSelectedLocalVolumeResult
        bin ambientCard positiveCoefficient singletonCoefficient)
    (houterLoss : 0 ≤ outerLoss)
    (hpositive :
      outerLoss * positiveCoefficient ≤ localTarget)
    (hsingleton :
      outerLoss * singletonCoefficient ≤ localTarget) :
    ENNReal.ofReal outerLoss * volume bin ≤
      ENNReal.ofReal localTarget * ambientCard := by
  cases hresult with
  | positive hvolume =>
      calc
        ENNReal.ofReal outerLoss * volume bin ≤
            ENNReal.ofReal outerLoss *
              (ENNReal.ofReal positiveCoefficient * ambientCard) := by
          gcongr
        _ =
            ENNReal.ofReal (outerLoss * positiveCoefficient) *
              ambientCard := by
          calc
            ENNReal.ofReal outerLoss *
                  (ENNReal.ofReal positiveCoefficient * ambientCard) =
                (ENNReal.ofReal outerLoss *
                    ENNReal.ofReal positiveCoefficient) * ambientCard := by
              ring
            _ =
                ENNReal.ofReal (outerLoss * positiveCoefficient) *
                  ambientCard := by
              rw [← ENNReal.ofReal_mul houterLoss]
        _ ≤ ENNReal.ofReal localTarget * ambientCard := by
          gcongr
  | singleton hvolume =>
      calc
        ENNReal.ofReal outerLoss * volume bin ≤
            ENNReal.ofReal outerLoss *
              (ENNReal.ofReal singletonCoefficient * ambientCard) := by
          gcongr
        _ =
            ENNReal.ofReal (outerLoss * singletonCoefficient) *
              ambientCard := by
          calc
            ENNReal.ofReal outerLoss *
                  (ENNReal.ofReal singletonCoefficient * ambientCard) =
                (ENNReal.ofReal outerLoss *
                    ENNReal.ofReal singletonCoefficient) * ambientCard := by
              ring
            _ =
                ENNReal.ofReal (outerLoss * singletonCoefficient) *
                  ambientCard := by
              rw [← ENNReal.ofReal_mul houterLoss]
        _ ≤ ENNReal.ofReal localTarget * ambientCard := by
          gcongr

end Kakeya.Cinematic
