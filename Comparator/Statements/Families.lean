import Comparator.Statements.Geometry

noncomputable section

open MeasureTheory

namespace Kakeya.Streamlined

structure BodyFamily where
  card : ℕ
  body : Fin card → Body

namespace BodyFamily

def union (F : BodyFamily) : Set Point3 :=
  {x | ∃ i : Fin F.card, x ∈ (F.body i).carrier}

def mass (F : BodyFamily) : ENNReal :=
  ∑ i : Fin F.card, (F.body i).volume

def enncard (F : BodyFamily) : ENNReal :=
  F.card

def containedIndices (F : BodyFamily) (K : Set Point3) :
    Finset (Fin F.card) := by
  classical
  exact Finset.univ.filter fun i => (F.body i).carrier ⊆ K

def containedCount (F : BodyFamily) (K : Set Point3) : ENNReal :=
  (F.containedIndices K).card

end BodyFamily

structure Shading (F : BodyFamily) where
  carrier : Fin F.card → Set Point3
  measurable_carrier : ∀ i, MeasurableSet (carrier i)
  subset_body : ∀ i, carrier i ⊆ (F.body i).carrier

namespace Shading

def union {F : BodyFamily} (Y : Shading F) : Set Point3 :=
  {x | ∃ i : Fin F.card, x ∈ Y.carrier i}

def mass {F : BodyFamily} (Y : Shading F) : ENNReal :=
  ∑ i : Fin F.card, MeasureTheory.volume (Y.carrier i)

def IsLambdaDense {F : BodyFamily} (Y : Shading F)
    (lambda : ENNReal) : Prop :=
  lambda * F.mass ≤ Y.mass

end Shading

structure TubeFamily (δ : ℝ) where
  card : ℕ
  tube : Fin card → Kakeya.DeltaTube δ

namespace TubeFamily

def toBodyFamily {δ : ℝ} (F : TubeFamily δ) : BodyFamily where
  card := F.card
  body i := tubeBody (F.tube i)

def Nonempty {δ : ℝ} (F : TubeFamily δ) : Prop :=
  0 < F.card

end TubeFamily

abbrev TubeShading {δ : ℝ} (F : TubeFamily δ) :=
  Shading F.toBodyFamily

end Kakeya.Streamlined
