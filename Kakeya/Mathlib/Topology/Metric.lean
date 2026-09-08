/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Topology.MetricSpace.Thickening

/-!
Lemmas related to Metric
-/

@[expose] public section

namespace Metric

variable
  {α : Type u} [PseudoEMetricSpace α]

theorem lt_infEDist_of_not_mem_cthickening
    {r : ENNReal} {s : Set α} {x : α} (hr : r ≠ ⊤)
    (hx : x ∉ Metric.cthickening r.toReal s) :
    r < Metric.infEDist x s := by
  simpa [ENNReal.ofReal_toReal_eq_iff.2 hr] using hx

variable
  {α : Type u} [PseudoMetricSpace α]

theorem mul_diam_le_of_forall_mul_dist_le {s : Set α} {C u : ℝ} (hu : 0 < u)
    (hC : 0 ≤ C) (h : ∀ x ∈ s, ∀ y ∈ s, dist x y * u ≤ C) :
    diam s * u ≤ C := by
  rw [← le_div_iff₀ hu]
  apply diam_le_of_forall_dist_le (div_nonneg hC hu.le)
  intro x hx y hy
  exact (le_div_iff₀ hu).mpr (h x hx y hy)

/-- **A surjective isometry carries a closed neighbourhood to a closed neighbourhood**
(blueprint `lem:cthickeningIsometry`).

This is the isometric sibling of `Metric.image_cthickening_homothety` (ratio `1`): a surjective
isometry preserves `Metric.infEDist`, and `Metric.cthickening` is a sublevel set of it.  Mathlib
has `IsometryEquiv.image_ball`, `IsometryEquiv.image_closedBall` and `IsometryEquiv.image_sphere`
but no `IsometryEquiv.image_cthickening`. -/
theorem image_cthickening_isometryEquiv {α β : Type*} [PseudoEMetricSpace α]
    [PseudoEMetricSpace β] (Φ : α ≃ᵢ β) (r : ℝ) (A : Set α) :
    Φ '' cthickening r A = cthickening r (Φ '' A) := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    change infEDist (Φ a) (Φ '' A) ≤ ENNReal.ofReal r
    rw [Metric.infEDist_image Φ.isometry]
    simpa using ha
  · intro hx
    refine ⟨Φ.symm x, ?_, by simp⟩
    change infEDist (Φ.symm x) A ≤ ENNReal.ofReal r
    rw [← Metric.infEDist_image Φ.isometry]
    simpa using hx

end Metric

namespace Kakeya

variable {E : Type*} [PseudoMetricSpace E] [ProperSpace E]

/-- In a proper metric space, a closed ball admits a finite cover by closed balls of any
positive radius. -/
lemma closedBall_finite_closedBall_cover (R : ℝ) {r : ℝ} (hr : 0 < r) (x : E) :
    ∃ (t : Finset E),
      (∀ y ∈ t, y ∈ Metric.closedBall x R) ∧
      (Metric.closedBall x R : Set E) ⊆ ⋃ y ∈ t, Metric.closedBall y r := by
  have hcompact : IsCompact (Metric.closedBall x R : Set E) :=
    ProperSpace.isCompact_closedBall x R
  obtain ⟨u, hu_sub, hufin, hsub⟩ :=
    Metric.finite_approx_of_totallyBounded hcompact.totallyBounded r hr
  refine ⟨hufin.toFinset, ?_, ?_⟩
  · intro y hy
    exact hu_sub (by simpa using hy)
  · intro p hp
    obtain ⟨y, hy, hyp⟩ := by simpa [Set.mem_iUnion] using hsub hp
    exact Set.mem_biUnion (by simpa using hy) (Metric.ball_subset_closedBall hyp)

end Kakeya
