import MyLeanRepo.Kakeya.Streamlined.Families
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.GeometricProbability

/-!
# Basic tube translation

This lightweight module defines translation of one tube.  It has no uniform
cover, Frostman, or multiscale theorem dependencies.
-/

noncomputable section

namespace Kakeya.Streamlined.RandomTranslation

/-- Translate one tube by moving its base point. -/
def translateTube {delta : ℝ}
    (tube : Kakeya.DeltaTube delta) (shift : Point3) :
    Kakeya.DeltaTube delta where
  base := tube.base + shift
  direction := tube.direction
  direction_unit := tube.direction_unit

end Kakeya.Streamlined.RandomTranslation
