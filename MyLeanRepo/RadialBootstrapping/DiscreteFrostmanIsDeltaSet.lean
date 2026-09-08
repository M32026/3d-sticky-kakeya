module

/-
  Discrete Frostman Lemma with IsDeltaSet conclusion
-/
public import MyLeanRepo.OSWPrelude
public import MyLeanRepo.RadialBootstrapping.Basic
public import MyLeanRepo.RadialBootstrapping.DiscreteFrostman

@[expose] public section

section

open MeasureTheory Metric Set Finset Classical
open scoped ENNReal NNReal

namespace SeedMathlib.MeasureTheory.FractalGeometry.FrostmanLemma

variable {n : ℕ} {s : ℝ}

local notation "Euc" => EuclideanSpace ℝ (Fin n)

/-- For a finite `(2δ)`-separated set `P`, external `δ`-covering = cardinality. -/
lemma externalCoveringNumber_eq_encard_of_separated
    {X : Type*} [PseudoMetricSpace X] {P : Set X} (hP : P.Finite)
    {δ : NNReal} (hδ_pos : 0 < δ)
    (hsep : Metric.IsSeparated (2 * δ) P) :
    Metric.externalCoveringNumber δ P = P.encard := by
  have h1 : Metric.externalCoveringNumber δ P ≤ P.encard :=
    Metric.externalCoveringNumber_le_encard_self P
  have h2 : P.encard ≤ Metric.packingNumber (2 * δ) P :=
    Metric.IsSeparated.encard_le_packingNumber (Set.Subset.refl P) hsep
  have h3 : Metric.packingNumber (2 * δ) P ≤ Metric.externalCoveringNumber δ P :=
    Metric.packingNumber_two_mul_le_externalCoveringNumber δ P
  exact le_antisymm h1 (h2.trans h3)

end SeedMathlib.MeasureTheory.FractalGeometry.FrostmanLemma
end
