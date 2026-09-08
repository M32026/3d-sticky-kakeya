/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCountFloorObstruction

/-!
# Tripwires for the window twin `IsKatzTaoDividingWindowLevels`

Two controls on `Kakeya.ML2Reduction.IsKatzTaoDividingWindowLevels`, the window twin
carrying the source's multiplicity-free level clause and the two-level density band.

* **T1** (`not_levelClause_gridModel`): the sticky grid family of
  `Reduction/SpineCountFloorObstruction.lean` — which satisfies the parent window
  (`gridModel_window`) and refutes the count floor on it (`not_countFloor_hypothesis`) — does
  **not**
  satisfy the level clause: at any window level `c` with `δ^{-(c/N) η₁} > C²`, the level-`c` cells
  under a coarse node number at most `C` while the clause demands `(ρ₀/ρ_c)^{η₁} ≤ C · Δ_max`.  So
  the
  re-cut is not a patch around the refutation but the source's own exclusion of that family, which
  is Katz–Tao at every scale and belongs to alternative (i) of GWZ 7.7(B).
* **T2** (`singletonWindowLevels`): the one-tube hierarchy of `Kakeya.ML2Core.singletonUniform`
  extends to the twin at `η ≡ 0`, `ε_d = 0`, `C⋆ = 1`, `a = 0`, `b = 1`, `m = 0`.  This is a
  regression guard: the model of `Kakeya.ML2Core.not_middleFactor_hypothesis` survives the re-cut,
  so
  the count binder in the middle factor is still needed.  It is not a non-vacuity certificate; that
  is `StickyKakeya.dividingScalesKatzTao` itself returning the twin.
-/

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody
open Tube ShadedTube
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## T1: the sticky grid family does NOT satisfy the level clause -/

/-- **T1.**  On the grid model of `SpineCountFloorObstruction.lean`, at the parameters at which
`gridModel_window` holds (`a = 0`, `b = ssfGridLen δ`, `m = 0`, `C⋆ = C`), the level clause of
`IsKatzTaoDividingWindowLevels` FAILS as soon as the window has a level `c` in its ceiling range
and `δ^{-(c/N)·η 1} > C²`: every level-`c` node meets the central `ρ_c`-tube, so there are at most
`C` of them and `Δ_max ≤ C`, while the clause demands `(ρ_0/ρ_c)^{η 1} ≤ C · Δ_max`.  So the
family that refutes the un-strengthened floor is excluded by the source's own clause, which is the
honest exclusion: the grid is Katz–Tao at every scale and belongs to alternative (i). -/
theorem not_levelClause_gridModel {δ : NNReal} {K : ℕ}
    {C : NNReal} {s' : Finset (ULift.{u} ℕ)} (hs' : s' ⊆ gridIndex.{u} K) (hne : s'.Nonempty)
    (𝒰 : Tube.UniformTubeSet s' (fun n => (gridShaded.{u} δ K n).toTube) (Tube.ssfGridLen δ) C)
    {η₁ : ℝ} {c : ℕ} (hc : c ≤ Tube.ssfGridLen δ)
    (hRc : (δ : ℝ) + 6 * δ * K ≤ Tube.gridScale δ (Tube.ssfGridLen δ) c)
    (hbig : (C : ℝ) * C < ((1 : ℝ) / (Tube.gridScale δ (Tube.ssfGridLen δ) c : ℝ)) ^ η₁) :
    ¬ ∀ j ∈ 𝒰.cover.indexSet 0,
      ENNReal.ofReal (((Tube.gridScale δ (Tube.ssfGridLen δ) 0 : ℝ)
          / (Tube.gridScale δ (Tube.ssfGridLen δ) c : ℝ)) ^ η₁)
        ≤ (C : ENNReal) * Kakeya.maxDensity (𝒰.nodesUnder c 0 j)
            (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) := by
  classical
  intro hall
  obtain ⟨i₀, hi₀⟩ := hne
  have hj : 𝒰.cover.assign 0 i₀ ∈ 𝒰.cover.indexSet 0 := 𝒰.cover.assign_mem 0 (Nat.zero_le _) i₀ hi₀
  have h := hall _ hj
  have hcnt : ((𝒰.cover.indexSet c).card : NNReal) ≤ C :=
    gridModel_card_indexSet_le hs' ⟨i₀, hi₀⟩ 𝒰 hc hRc
  have hmax : Kakeya.maxDensity (𝒰.nodesUnder c 0 (𝒰.cover.assign 0 i₀))
      (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) ≤ (C : ENNReal) := by
    refine (Kakeya.maxDensity_le_card _ _).trans ?_
    have h1 : (𝒰.nodesUnder c 0 (𝒰.cover.assign 0 i₀)).card ≤ (𝒰.cover.indexSet c).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    have h2 : ((𝒰.cover.indexSet c).card : ENNReal) ≤ (C : ENNReal) := by exact_mod_cast hcnt
    exact (by exact_mod_cast h1 : ((𝒰.nodesUnder c 0 (𝒰.cover.assign 0 i₀)).card : ENNReal)
      ≤ (𝒰.cover.indexSet c).card).trans h2
  have hg0 : ((Tube.gridScale δ (Tube.ssfGridLen δ) 0 : NNReal) : ℝ) = 1 := by
    rw [Tube.gridScale_zero]; simp
  rw [hg0] at h
  have hCC : ENNReal.ofReal (((1 : ℝ) / (Tube.gridScale δ (Tube.ssfGridLen δ) c : ℝ)) ^ η₁)
      ≤ ((C : NNReal) * C : NNReal) := by
    calc ENNReal.ofReal (((1 : ℝ) / (Tube.gridScale δ (Tube.ssfGridLen δ) c : ℝ)) ^ η₁)
        ≤ (C : ENNReal) * Kakeya.maxDensity (𝒰.nodesUnder c 0 (𝒰.cover.assign 0 i₀))
            (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) := h
      _ ≤ (C : ENNReal) * (C : ENNReal) := by gcongr
      _ = ((C * C : NNReal) : ENNReal) := by push_cast; rfl
  have hCC' : ((1 : ℝ) / (Tube.gridScale δ (Tube.ssfGridLen δ) c : ℝ)) ^ η₁
      ≤ ((C * C : NNReal) : ℝ) := by
    have hnn : 0 ≤ ((1 : ℝ) / (Tube.gridScale δ (Tube.ssfGridLen δ) c : ℝ)) ^ η₁ := by positivity
    have := (ENNReal.ofReal_le_iff_le_toReal ENNReal.coe_ne_top).mp hCC
    simpa using this
  push_cast at hCC'
  exact absurd hCC' (not_le.mpr hbig)

/-! ## T2: the singleton window extends to the twin -/

/-- **T2 (non-vacuity).**  The one-tube hierarchy of `Kakeya.ML2Core.singletonUniform` carries the
twin at `η ≡ 0`, `ε_d = 0`, `C⋆ = 1`, `a = 0`, `b = 1`, `m = 0`: the level clause reads
`1 ≤ 1 · Δ_max(one node)`, and the band is the trivial profile `Φ a c := Δ_max(one node)`.  So
the re-cut has not destroyed the model of `not_middleFactor_hypothesis`. -/
theorem singletonWindowLevels {ι : Type*} (i₀ : ι) {δ : NNReal}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hN : 1 ≤ Tube.ssfGridLen δ) (T : ι → Tube δ E3)
    (hvol : 0 < volume (T i₀).carrier) :
    ML2Reduction.IsKatzTaoDividingWindowLevels
      (singletonUniform i₀ hδ0 hδ1 (Tube.ssfGridLen δ) T) 1 (fun _ => (0:ℝ)) 0
      (Tube.ssfGridLen δ) 0 1 0 := by
  classical
  set N := Tube.ssfGridLen δ with hNdef
  set 𝒰 := singletonUniform i₀ hδ0 hδ1 N T with h𝒰
  have hidx : ∀ k, 𝒰.cover.indexSet k = ({i₀} : Finset ι) := fun k => rfl
  refine ⟨singletonWindow i₀ hδ0 hδ1 hN T hvol, ?_, ?_⟩
  · intro c _ _ j hj
    rw [hidx 0, Finset.mem_singleton] at hj
    simp only [Real.rpow_zero, ENNReal.ofReal_one, one_mul]
    -- the single node `i₀` lies under `j = i₀` at level `c`
    have hnodes : i₀ ∈ 𝒰.nodesUnder c 0 j := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_singleton_self i₀, ?_⟩
      rw [hj]
      exact Tube.rescale_le_rescale_of_radius_le (T i₀)
        (Tube.gridScale_antitone hδ0 hδ1 N (Nat.zero_le c))
    have hpos : 0 < volume (𝒰.cover.tube c i₀).carrier :=
      lt_of_lt_of_le hvol (measure_mono ((T i₀).le_rescale (delta_le_gridScale hδ0 hδ1 (by omega))))
    exact Kakeya.one_le_maxDensity ⟨i₀, hnodes, hpos⟩
  · refine ⟨fun a c => Kakeya.maxDensity ((coverClass ({i₀} : Finset ι) (𝒰.cover.assign a) i₀).image
        (𝒰.cover.assign c)) (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody), ?_⟩
    intro p _ c _ j hj
    rw [hidx p, Finset.mem_singleton] at hj
    subst hj
    exact ⟨le_rfl, by simp⟩

end Kakeya.ML2Core

end
