import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.RobustCloseCountPhase3

/-!
# Phase 4: Transverse condition from robust close count

Derives the transverse direction condition needed by
`per_cell_plane_map_from_transverse` from the robust close-direction count bound
plus a pointwise multiplicity lower bound.

Given:
- Close direction count ≤ R (from robust close count, Phase 3)
- Pointwise multiplicity ≥ m (from PropertyP or h_avg pruning)
- R < m

Then for every tube i at point p, there exists another tube j at p with
`kappa ≤ ‖cross(dir_i, dir_j)‖`. This is the transverse condition.

This is the paper-shading version of `transverse_from_close_count_lt_multiplicity`
from WZ1, simplified to not require constant multiplicity.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set Finset

attribute [local instance] Classical.propDecidable

/-- Derive transverse condition from close count < multiplicity.

For a paper tube shading `S`, if the close-direction count at threshold `kappa`
is strictly less than the pointwise multiplicity, then every active tube has a
transverse partner at the same point.

This is the key bridge between robust close count (Phase 3) and the per-cell
plane map selector (`per_cell_plane_map_from_transverse`).
-/
lemma paper_transverse_from_close_count_lt_multiplicity
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading F}
    {m : ℕ}
    (kappa : ℝ)
    (hmult : ∀ p ∈ S.union, m ≤ S.pointMultiplicity p)
    (hclose : ∀ p ∈ S.union, ∀ i, p ∈ S.carrier i →
      paperCloseDirectionCount S p i kappa < m) :
    ∀ p ∈ S.union, ∀ i, p ∈ S.carrier i →
      ∃ j, p ∈ S.carrier j ∧
        kappa ≤ ‖wz1Cross (F.tube i).direction (F.tube j).direction‖ := by
  intro p hp i hi
  classical
  let active : Finset (Fin F.card) :=
    Finset.univ.filter fun j => p ∈ S.carrier j
  let close : Finset (Fin F.card) :=
    Finset.univ.filter fun j =>
      p ∈ S.carrier j ∧
        ‖wz1Cross (F.tube i).direction (F.tube j).direction‖ < kappa
  have hactiveCard : active.card = S.pointMultiplicity p := by rfl
  have hmActive : m ≤ active.card := by
    rw [hactiveCard]
    exact hmult p hp
  have hcloseSubset : close ⊆ active := by
    intro j hj
    have h : p ∈ S.carrier j := (Finset.mem_filter.mp hj).2.1
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, h⟩
  have hcloseCard : close.card = paperCloseDirectionCount S p i kappa := by rfl
  have hcloseLt : close.card < m := by
    rw [hcloseCard]
    exact hclose p hp i hi
  have hcard : close.card < active.card := by
    exact hcloseLt.trans_le hmActive
  have h_exists : ∃ j, j ∈ active ∧ j ∉ close := by
    by_contra h
    push Not at h
    have hsub : active ⊆ close := by
      intro j hj
      exact h j hj
    have hle : active.card ≤ close.card := Finset.card_le_card hsub
    linarith
  rcases h_exists with ⟨j, hjActive, hjNotClose⟩
  have hjp : p ∈ S.carrier j := by
    simp only [active, Finset.mem_filter, Finset.mem_univ, true_and] at hjActive
    exact hjActive
  have hjTransverse : kappa ≤ ‖wz1Cross (F.tube i).direction (F.tube j).direction‖ := by
    have h_cross_not_lt : ¬(‖wz1Cross (F.tube i).direction (F.tube j).direction‖ < kappa) := by
      intro h
      have h_contra : j ∈ close := by
        simp only [close, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hjp, h⟩
      exact hjNotClose h_contra
    exact not_lt.mp h_cross_not_lt
  exact ⟨j, hjp, hjTransverse⟩

/-- Combine robust close count with multiplicity lower bound to get transverse.

Given:
- Robust close count bound: `paperCloseDirectionCount ≤ R_enn`
- Multiplicity lower bound: `m ≤ pointMultiplicity`
- Strict inequality: `R_enn < (m : ENNReal)`

Produces the transverse condition for `per_cell_plane_map_from_transverse`.
-/
lemma transverse_from_robust_count_and_multiplicity
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {S : WZ1PaperTubeShading F}
    {m : ℕ}
    {R_enn : ENNReal}
    (kappa : ℝ)
    (hrobust : ∀ p ∈ S.union, ∀ i, p ∈ S.carrier i →
      (paperCloseDirectionCount S p i kappa : ENNReal) ≤ R_enn)
    (hmult : ∀ p ∈ S.union, (m : ENNReal) ≤ (S.pointMultiplicity p : ENNReal))
    (hstrict : R_enn < (m : ENNReal)) :
    ∀ p ∈ S.union, ∀ i, p ∈ S.carrier i →
      ∃ j, p ∈ S.carrier j ∧
        kappa ≤ ‖wz1Cross (F.tube i).direction (F.tube j).direction‖ := by
  have hclose_nat : ∀ p ∈ S.union, ∀ i, p ∈ S.carrier i →
      paperCloseDirectionCount S p i kappa < m := by
    intro p hp i hi
    have h1 : (paperCloseDirectionCount S p i kappa : ENNReal) ≤ R_enn :=
      hrobust p hp i hi
    have h2 : (paperCloseDirectionCount S p i kappa : ENNReal) < (m : ENNReal) :=
      h1.trans_lt hstrict
    exact_mod_cast h2
  have hmult_nat : ∀ p ∈ S.union, m ≤ S.pointMultiplicity p := by
    intro p hp
    have h : (m : ENNReal) ≤ (S.pointMultiplicity p : ENNReal) := hmult p hp
    exact_mod_cast h
  exact paper_transverse_from_close_count_lt_multiplicity kappa hmult_nat hclose_nat

end Kakeya.Assouad.PureWZ2
