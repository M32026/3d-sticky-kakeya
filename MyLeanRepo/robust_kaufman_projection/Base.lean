module

public import MyLeanRepo.DiscretisedFurstenbergEstimate.ProductStructureRescaling.Basics
public import MyLeanRepo.RobustKaufmanProjection.Basics
public import MyLeanRepo.OSWPrelude

@[expose] public section

/-!
# Base definitions for the robust Kaufman projection theorem

This module contains the shared definitions used by the projection theorem
and its helper lemmas.

NOTE: `IsDeltaSSet`, `EuclideanPlane`, and `Ncover` are imported from
the main project's `ProductStructureRescaling.Basics` to avoid
environment-level collisions.
-/

noncomputable section

open scoped ENNReal NNReal

def InUnitSquare (P : Set EuclideanPlane) : Prop :=
  P ⊆ {p | p 0 ∈ Set.Icc (0 : ℝ) 1 ∧ p 1 ∈ Set.Icc (0 : ℝ) 1}

end
