import MyLeanRepo.Kakeya.Streamlined.DividingScales.ReferenceDensity
import MyLeanRepo.Kakeya.Streamlined.IndependentDilatedCoverContainmentFibers

/-!
# Full containment-fiber profiles

These are the profiles appearing in repaired Definition 2.1(iv).  They use
all geometrically contained fine tubes, not the fiber of an auxiliary parent
assignment.
-/

noncomputable section

namespace Kakeya.Streamlined

namespace DilatedDiscreteUniformTubeStructure

variable {delta A : ℝ} {F : TubeFamily delta}
variable {hdelta_le_one : delta ≤ 1}

/-- Maximal density of the full fine containment fiber at one scale. -/
def fineFiberDeltaMax
    (U : DilatedDiscreteUniformTubeStructure
      (A := A) F hdelta_le_one)
    (r : UniformScaleIndex delta)
    (j : Fin (U.coarse r).card) : ENNReal :=
  (U.containedFineSubfamily r j).family.toBodyFamily.deltaMax

end DilatedDiscreteUniformTubeStructure

end Kakeya.Streamlined
