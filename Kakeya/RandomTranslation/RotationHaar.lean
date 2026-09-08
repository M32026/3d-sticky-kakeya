/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.RandomTranslation.SphereCap
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Topology.Algebra.Star.Unitary

/-!
# The rotation group as a compact group

The rotational half of GWZ Appendix A equation (106) needs a random rotation, i.e. a probability
measure on the group of linear isometries of `E`. Mathlib has Haar measure for compact groups but no
compactness instance for any orthogonal/unitary group, so this file supplies it.

The group is realised as `unitary (E →L[ℝ] E)`, the unitary group of the C⋆-algebra of bounded
operators. This is preferable to `Matrix.orthogonalGroup` for our purposes: it carries the operator
norm topology out of the box, it acts on `E` by plain function application (so measurability of the
action is trivial), and it is dimension-generic.

Compactness is Heine–Borel:

* **closed** — `isClosed_unitary`, which needs only `T1Space`, `ContinuousStar`, `ContinuousMul`;
* **bounded** — a unitary is an isometry (`Kakeya.norm_apply_of_mem_unitary`), hence has operator
  norm at most `1`;
* `E →L[ℝ] E` is finite-dimensional when `E` is.

Downstream this yields a Haar probability measure on the rotation group, whose pushforward along
`u ↦ u d` is a rotation-invariant probability measure on the unit sphere; combined with
`Kakeya.toSphere_projectiveCap_le` that gives the projective direction-cap estimate.
-/

@[expose] public section

open MeasureTheory Metric Set

namespace Kakeya

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **A unitary operator is an isometry.** Immediate from `star u * u = 1` and the defining
property of the adjoint. -/
theorem norm_apply_of_mem_unitary {u : E →L[ℝ] E} (hu : u ∈ unitary (E →L[ℝ] E)) (x : E) :
    ‖u x‖ = ‖x‖ := by
  exact ContinuousLinearMap.norm_map_of_mem_unitary hu x

/-- **A unitary operator has operator norm at most `1`.** -/
theorem opNorm_le_one_of_mem_unitary {u : E →L[ℝ] E} (hu : u ∈ unitary (E →L[ℝ] E)) :
    ‖u‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound u zero_le_one (fun x => ?_)
  rw [norm_apply_of_mem_unitary hu x, one_mul]

/-- **The rotation group is compact.** Heine–Borel applied to the closed, norm-bounded set of
unitary operators inside the finite-dimensional space `E →L[ℝ] E`. -/
theorem isCompact_unitary : IsCompact (unitary (E →L[ℝ] E) : Set (E →L[ℝ] E)) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · exact isClosed_unitary
  · rw [isBounded_iff_forall_norm_le]
    exact ⟨1, fun u hu => opNorm_le_one_of_mem_unitary hu⟩

instance instCompactSpaceUnitary : CompactSpace (unitary (E →L[ℝ] E)) :=
  isCompact_iff_compactSpace.mp isCompact_unitary

/-- The Borel σ-algebra on the rotation group. `Mathlib` provides no `MeasurableSpace` instance for
a subtype of a normed space, so we install the Borel one, as `borelize` would. -/
noncomputable instance instMeasurableSpaceUnitary :
    MeasurableSpace (unitary (E →L[ℝ] E)) :=
  borel _

instance instBorelSpaceUnitary : BorelSpace (unitary (E →L[ℝ] E)) := ⟨rfl⟩

/-- **Haar probability measure on the rotation group.** The group is compact
(`Kakeya.instCompactSpaceUnitary`), so the Haar measure normalised on the whole group is a
probability measure. This is the law of the rotational component of a random rigid motion. -/
noncomputable def rotHaar : Measure (unitary (E →L[ℝ] E)) :=
  Measure.haarMeasure ⊤

instance instIsProbabilityMeasureRotHaar :
    IsProbabilityMeasure (rotHaar (E := E)) := by
  constructor
  have h := MeasureTheory.Measure.haarMeasure_self
    (K₀ := (⊤ : TopologicalSpace.PositiveCompacts (unitary (E →L[ℝ] E))))
  rwa [TopologicalSpace.PositiveCompacts.coe_top] at h

instance instIsMulLeftInvariantRotHaar :
    (rotHaar (E := E)).IsMulLeftInvariant := by
  exact Measure.isMulLeftInvariant_haarMeasure ⊤

/-- **The rotation group acts transitively on the unit sphere.** Together with left invariance of
`Kakeya.rotHaar` this forces all projective caps of a given radius to have the same measure under
the pushforward `u ↦ u d`, which is the step converting the geometric cap bound
`Kakeya.toSphere_projectiveCap_le` into a probability bound. -/
theorem exists_mem_unitary_apply_eq {w w' : E} (hw : ‖w‖ = 1) (hw' : ‖w'‖ = 1) :
    ∃ u : unitary (E →L[ℝ] E), (u : E →L[ℝ] E) w = w' := by
  by_cases h : w = w'
  · subst h
    refine ⟨Unitary.linearIsometryEquiv.symm (LinearIsometryEquiv.refl ℝ E), ?_⟩
    rw [Unitary.coe_symm_linearIsometryEquiv_apply]
    rfl
  · let v : E := w - w'
    have hv : v ≠ 0 := by
      intro hv0
      exact h (sub_eq_zero.mp hv0)
    have hvne : ‖v‖ ^ 2 ≠ 0 := by
      exact pow_ne_zero 2 (ne_of_gt (norm_pos_iff.mpr hv))
    have hunit : ‖w‖ ^ 2 = 1 := by
      simp [hw]
    have hunit' : ‖w'‖ ^ 2 = 1 := by
      simp [hw']
    have hinner : inner ℝ v w = 1 - inner ℝ w w' := by
      dsimp [v]
      rw [inner_sub_left, real_inner_self_eq_norm_sq, real_inner_comm w w', hunit]
    have hnorm : ‖v‖ ^ 2 = 2 - 2 * inner ℝ w w' := by
      dsimp [v]
      rw [norm_sub_sq_real, hunit, hunit']
      ring
    have hmain : 2 * inner ℝ v w = ‖v‖ ^ 2 := by
      rw [hinner, hnorm]
      ring
    have hscalar : (2 : ℝ) * (inner ℝ v w / ‖v‖ ^ 2) = 1 := by
      rw [show (2 : ℝ) * (inner ℝ v w / ‖v‖ ^ 2) = (2 * inner ℝ v w) / ‖v‖ ^ 2 by ring]
      rw [hmain]
      exact div_self hvne
    let K : Submodule ℝ E := (Submodule.span ℝ {v})ᗮ
    haveI : K.HasOrthogonalProjection := by
      exact Submodule.HasOrthogonalProjection.ofCompleteSpace (K := K)
    refine ⟨Unitary.linearIsometryEquiv.symm K.reflection, ?_⟩
    rw [Unitary.coe_symm_linearIsometryEquiv_apply]
    change K.reflection w = w'
    dsimp [K]
    rw [Submodule.reflection_orthogonal_apply]
    rw [Submodule.reflection_apply, Submodule.starProjection_singleton (𝕜 := ℝ)]
    change -((2 : ℕ) • (inner ℝ v w / (‖v‖ ^ 2)) • v - w) = w'
    have hvv : (2 : ℕ) • ((inner ℝ v w / ‖v‖ ^ 2) • v) = v := by
      rw [two_nsmul]
      rw [← add_smul]
      rw [show inner ℝ v w / ‖v‖ ^ 2 + inner ℝ v w / ‖v‖ ^ 2 =
          2 * (inner ℝ v w / ‖v‖ ^ 2) by ring]
      rw [hscalar, one_smul]
    rw [hvv]
    rw [neg_sub]
    rw [show v = w - w' from rfl]
    abel

end Kakeya

end
