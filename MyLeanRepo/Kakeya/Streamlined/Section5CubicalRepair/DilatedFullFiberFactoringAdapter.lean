import MyLeanRepo.Kakeya.Streamlined.ProfileUniformRefinement.GeometricFullContainmentFibers
import MyLeanRepo.Kakeya.Streamlined.UniformRefinement.SingleScaleCover

/-!
# Section 5 factoring from a dilated full-fiber partition

A fixed-dilation cover cannot be converted to a strict `TubeCover`: its fine
tubes need not lie in the undilated unit-length coarse tubes.  The legal
Section 5 parent family is instead the body family whose carriers are the
actual dilated coarse tubes.
-/

noncomputable section

namespace Kakeya.Streamlined

/--
A legal Section 5 factoring whose assigned fibers are exactly the retained
geometric full-containment fibers.

This is the output of the unique-owner selection.  The carrier side is the
actual dilated coarse body family, while `fiber_eq_full` records that no
geometric child was lost or duplicated inside the retained partition.
-/
structure DilatedFullFiberFactoringAdapter
    {delta rho A : ℝ}
    (fine : TubeFamily delta) (coarse : TubeFamily rho) where
  cover : DilatedTubeCover A fine coarse
  fiber_eq_full :
    ∀ j : Fin coarse.card,
      cover.toFactoring.fiberIndices j =
        restrictedContainedFineIndices
          (A := A) (fine := fine) (coarse := coarse) j

namespace DilatedFullFiberFactoringAdapter

variable {delta rho A : ℝ}
variable {fine : TubeFamily delta} {coarse : TubeFamily rho}

/-- The exact Section 5 factoring carried by the adapter. -/
abbrev factoring
    (adapter : DilatedFullFiberFactoringAdapter
      (A := A) fine coarse) :
    Factoring fine.toBodyFamily (dilatedTubeBodyFamily A coarse) :=
  adapter.cover.toFactoring

/-- Every adapter fiber is the corresponding complete geometric full fiber. -/
lemma factoring_fiber_eq_full
    (adapter : DilatedFullFiberFactoringAdapter
      (A := A) fine coarse)
    (j : Fin coarse.card) :
    adapter.factoring.fiberIndices j =
      restrictedContainedFineIndices
        (A := A) (fine := fine) (coarse := coarse) j :=
  adapter.fiber_eq_full j

/--
The adapter's partition fibers inherit geometric full-fiber uniformity because
`fiber_eq_full` identifies them exactly. This implication is specific to the
adapter and is false for an arbitrary dilated cover.
-/
lemma factoring_fibersAreCUniform_of_geometricFull
    (adapter : DilatedFullFiberFactoringAdapter
      (A := A) fine coarse)
    {C : ENNReal}
    (huniform :
      GeometricFullContainmentFibersAreCUniform
        (A := A) fine coarse C) :
    adapter.factoring.FibersAreCUniform C := by
  refine ⟨huniform.1, ?_⟩
  intro first second
  change
    ((adapter.factoring.fiberIndices first).card : ENNReal) ≤
      C * ((adapter.factoring.fiberIndices second).card : ENNReal)
  rw [adapter.factoring_fiber_eq_full first,
    adapter.factoring_fiber_eq_full second]
  exact huniform.2 first second

/--
The cover-valued public predicate is exactly the parent-map-free geometric
full-fiber predicate.  The adapter's factoring equality is irrelevant here
and is used only by later partition arguments.
-/
lemma cover_isCUniform_of_geometricFull
    (adapter : DilatedFullFiberFactoringAdapter
      (A := A) fine coarse)
    {C : ENNReal}
    (huniform :
      GeometricFullContainmentFibersAreCUniform
        (A := A) fine coarse C) :
    adapter.cover.IsCUniform C := by
  exact
    (geometricFullContainmentFibersAreCUniform_iff_cover
      adapter.cover C).mp huniform

end DilatedFullFiberFactoringAdapter

end Kakeya.Streamlined
