import Comparator.Statements.AssertionD

noncomputable section

open MeasureTheory

namespace Kakeya.Streamlined

abbrev Point3 := Kakeya.Point3

structure Body where
  carrier : Set Point3

namespace Body

def IsMeasurable (K : Body) : Prop :=
  MeasurableSet K.carrier

def IsConvex (K : Body) : Prop :=
  Convex ℝ K.carrier

def volume (K : Body) : ENNReal :=
  MeasureTheory.volume K.carrier

end Body

def tubeBody {δ : ℝ} (T : Kakeya.DeltaTube δ) : Body :=
  ⟨T.carrier⟩

def unitBall : Body :=
  ⟨Kakeya.DeltaTube.unitBall⟩

end Kakeya.Streamlined
