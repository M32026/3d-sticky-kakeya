import MyLeanRepo.Kakeya.Cinematic.Section5.ShadingVolume

/-!
# Linear fixed-ambient fine-volume assembly

Once the total number of selected fine rectangles is linear in the cardinality
of one fixed ambient family, the uniform fine-shading area bound yields a
volume estimate with the same linear ambient-cardinality factor.  This is the
local form needed before bounded-overlap summation across ambient bins.
-/

open MeasureTheory

namespace Kakeya.Cinematic

def LinearAmbientFineVolumeAssemblyStatement : Prop :=
  ∀ {E : Set (ℝ × ℝ)}
    (fineCard ambientCard : ℕ)
    (cardCoefficient area : ℝ),
    0 ≤ cardCoefficient →
    0 ≤ area →
    (fineCard : ℝ) ≤
      (ambientCard : ℝ) * cardCoefficient →
    volume E ≤
      (fineCard : ENNReal) * ENNReal.ofReal area →
    volume E ≤
      ENNReal.ofReal (cardCoefficient * area) * ambientCard

end Kakeya.Cinematic
