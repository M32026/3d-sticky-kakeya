import MyLeanRepo.Kakeya.Assouad.Definitions
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.Support

/-!
# External inputs used while migrating WZ1

These are ordinary propositions supplied as hypotheses to WZ1 proof targets.
They are not axioms and do not hide any WZ1-owned transition.
-/

noncomputable section

open MeasureTheory

open scoped ENNReal NNReal

namespace Kakeya.Assouad

def HasMeasureThinTubes (β K c : ℝ)
    (ν₁ ν₂ : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2))) : Prop :=
  0 ≤ β ∧
  1 ≤ K ∧
    c ∈ Set.Ico (0 : ℝ) 1 ∧
    ∃ E : Set (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)),
    MeasurableSet E ∧
        E ⊆ (ν₁ : Measure (EuclideanSpace ℝ (Fin 2))).support ×ˢ
          (ν₂ : Measure (EuclideanSpace ℝ (Fin 2))).support ∧
      (1 - ENNReal.ofReal c ≤ (ν₁.prod ν₂) E) ∧
        ∀ b₁ ∈ (ν₁ : Measure (EuclideanSpace ℝ (Fin 2))).support,
          ∀ ℓ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)),
            b₁ ∈ (ℓ : Set (EuclideanSpace ℝ (Fin 2))) →
              Module.finrank ℝ ℓ.direction = 1 →
                ∀ r : ℝ, 0 < r →
                  ν₂ {b₂ |
                    b₂ ∈ Metric.thickening r
                      (ℓ : Set (EuclideanSpace ℝ (Fin 2))) ∧
                    (b₁, b₂) ∈ E} ≤
                      Real.toNNReal (K * r ^ β)

/--
OSW radial-projection bootstrap in the exact measure-thin-tubes form supplied
for the WZ1 migration.
-/
def RadialBootstrappingMeasureThinTubesInput : Prop :=
  ∀ β ε : ℝ, 0 < β → 0 < ε →
    ∃ τ : ℝ, 0 < τ ∧
      ∃ M : ℝ, 1 ≤ M ∧
        ∀ (σ c K C : ℝ)
            (ν₁ ν₂ : ProbabilityMeasure (EuclideanSpace ℝ (Fin 2))),
          (ν₁ : Measure (EuclideanSpace ℝ (Fin 2))).support ⊆
              Metric.closedBall 0 1 →
            (ν₂ : Measure (EuclideanSpace ℝ (Fin 2))).support ⊆
                Metric.closedBall 0 1 →
              σ ∈ Set.Icc β (1 - ε) →
              c ∈ Set.Ioo (0 : ℝ) (1 / 10) →
              1 ≤ K →
              1 ≤ C →
              (1 : ℝ) / 2 ≤
                  sInf {d : ℝ |
                    ∃ x ∈
                        (ν₁ : Measure
                          (EuclideanSpace ℝ (Fin 2))).support,
                      ∃ y ∈
                          (ν₂ : Measure
                            (EuclideanSpace ℝ (Fin 2))).support,
                        dist x y = d} →
              (∀ (x : EuclideanSpace ℝ (Fin 2)) (r : ℝ), 0 < r →
                ν₁ (Metric.ball x r) ≤ Real.toNNReal (C * r)) →
              (∀ (x : EuclideanSpace ℝ (Fin 2)) (r : ℝ), 0 < r →
                ν₂ (Metric.ball x r) ≤ Real.toNNReal (C * r)) →
              HasMeasureThinTubes σ K c ν₁ ν₂ →
              HasMeasureThinTubes σ K c ν₂ ν₁ →
                let K' : ℝ :=
                  Real.rpow (max K (C ^ 2 * M / c)) M
                HasMeasureThinTubes (σ + τ) K' (3 * c) ν₁ ν₂ ∧
                  HasMeasureThinTubes (σ + τ) K' (3 * c) ν₂ ν₁

end Kakeya.Assouad
