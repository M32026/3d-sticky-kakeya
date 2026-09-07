module

/-
  HasMeasureThinTubes.lean

  Definition of the "measure thin tubes" property for pairs of Borel
  probability measures on ℝ².

  Extracted from radial_bootstrapping_measure_thin_tubes.lean to break
  the circular import dependency in the final proof assembly.
-/

public import MyLeanRepo.OSWPrelude

@[expose] public section

open MeasureTheory

open scoped ENNReal NNReal

noncomputable section

/-- [def.measure_thin_tubes.2503] Let `β ≥ 0`, `K ≥ 1`, and `c ∈ [0,1)`. Let
`ν₁, ν₂` be Borel probability measures on `ℝ²`. The pair `(ν₁, ν₂)` has
`(β, K, 1 - c)`-thin tubes if there exists a Borel set
`E ⊆ supp(ν₁) × supp(ν₂)` with `(ν₁ × ν₂)(E) ≥ 1 - c` such that, for all
`b₁ ∈ supp(ν₁)`, all lines `ℓ ⊆ ℝ²` containing `b₁`, and all `r > 0`,
`ν₂({b₂ ∈ N_r(ℓ) : (b₁, b₂) ∈ E}) ≤ K r^β`.

Here `ℝ²` is formalized as `EuclideanSpace ℝ (Fin 2)`, lines are affine
subspaces whose direction has real finrank `1`, and `N_r(ℓ)` is the metric
open `r`-thickening of the underlying set of `ℓ`.
-/
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
                  ν₂ {b₂ | b₂ ∈ Metric.thickening r (ℓ : Set (EuclideanSpace ℝ (Fin 2))) ∧
                    (b₁, b₂) ∈ E} ≤ Real.toNNReal (K * r ^ β)

end
