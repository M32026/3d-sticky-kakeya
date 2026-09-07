import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.LocalAD

/-!
# Slab extension lemma for local AD conversion

Extends a Córdoba slab volume lower bound from a subset of projection values
to the full projection of a set S, by doubling the slab width.

Given slab bounds for t ∈ P, and that every t ∈ proj(S) is within W0 of some t' ∈ P,
then slab bounds hold for all t ∈ proj(S) with width 2*W0.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set ENNReal

/-- Extend slab bounds by doubling the width.

Given a measurable set `S`, a unit direction `v`, a set `P` of "good" projection
values, slab width `W0`, and volume lower bound `V_min` for all slabs centered at
`t ∈ P`, if every `t ∈ scalarProjection v S` is within `W0` of some `t' ∈ P`,
then `volume(S ∩ slab(t, 2*W0)) ≥ V_min` for all `t ∈ scalarProjection v S`. -/
lemma extend_slab_bounds
    {S : Set Point3}
    {v : Point3}
    {P : Set ℝ}
    {W0 V_min : ℝ}
    (hS_meas : MeasurableSet S)
    (hW0_pos : 0 < W0)
    (hVmin_pos : 0 < V_min)
    (h_slab_P : ∀ t ∈ P,
        volume (S ∩ {x | |inner ℝ x v - t| ≤ W0}) ≥ ENNReal.ofReal V_min)
    (h_cover : ∀ t ∈ scalarProjection v S, ∃ t' ∈ P, |t - t'| ≤ W0) :
    ∀ t ∈ scalarProjection v S,
      volume (S ∩ {x | |inner ℝ x v - t| ≤ 2 * W0}) ≥ ENNReal.ofReal V_min := by
  let proj : Point3 → ℝ := fun x => inner ℝ x v
  intro t ht
  have h4 : ∃ t' ∈ P, |t - t'| ≤ W0 := h_cover t ht
  rcases h4 with ⟨t', ht', hdist⟩
  have h5 : {y : Point3 | |proj y - t'| ≤ W0} ⊆ {y : Point3 | |proj y - t| ≤ 2 * W0} := by
    intro y hy
    have h10 : |proj y - t'| ≤ W0 := hy
    have h_ineq : |proj y - t| ≤ |proj y - t'| + |t - t'| := by
      have h_eq : proj y - t = (proj y - t') + (t' - t) := by ring
      rw [h_eq]
      have h : |(proj y - t') + (t' - t)| ≤ |proj y - t'| + |t' - t| := abs_add_le _ _
      have h2 : |t' - t| = |t - t'| := by rw [abs_sub_comm]
      rw [h2] at h
      exact h
    have h_final : |proj y - t| ≤ 2 * W0 := by
      calc
        |proj y - t| ≤ |proj y - t'| + |t - t'| := h_ineq
        _ ≤ W0 + W0 := by
          exact add_le_add h10 hdist
        _ = 2 * W0 := by ring
    exact h_final
  have h9 : S ∩ {y | |proj y - t'| ≤ W0} ⊆ S ∩ {y | |proj y - t| ≤ 2 * W0} := by
    intro y hy
    exact ⟨hy.1, h5 hy.2⟩
  have h10 : volume (S ∩ {y | |proj y - t'| ≤ W0}) ≥ ENNReal.ofReal V_min :=
    h_slab_P t' ht'
  exact le_trans h10 (measure_mono h9)

end Kakeya.Assouad.PureWZ2

end
