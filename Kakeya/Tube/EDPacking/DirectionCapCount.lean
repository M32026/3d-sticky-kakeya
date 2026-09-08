/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Mathlib.Analysis.EuclideanNetLocal
public import Kakeya.Tube.EDPacking.PositionCount

/-!
# Counting ED `δ`-tubes in a direction cap of radius `A · δ`

`Kakeya.position_count_le_of_bad_directionClass'` counts pairwise-ED `δ`-tubes
whose directions lie in *one* cap of radius `c_slide · δ`, and returns the
absolute bound `C · M / c`. The ED conflict-degree route of
`Kakeya/DimensionThree/Plank/EDDegree.lean` needs the same count for a cap of
radius `A · δ`, where `A` is whatever constant the plank-overlap step produces.

This file supplies that widening, which is pure bookkeeping: by
`Kakeya.EuclideanNet.exists_projective_cap_net_scaled` the `A · δ` cap is covered
by at most `4 ^ n · (A / c_slide) ^ n` caps of radius `c_slide · δ` — an absolute
number, because both radii are proportional to `δ` and the net cardinality sees
them only through the ratio `A / c_slide`. Summing the single-cap count over the
net multiplies the bound by that absolute number and nothing else. In
particular no factor `δ ^ (-(n-1))` appears, which is the whole point: the global
net `Kakeya.EuclideanNet.exists_sphere_net` would contribute exactly that factor
and make the conflict degree `δ ^ (-2)` in `ℝ³`.

* `exists_ED_directionCap_card_bound` — the real-valued bound `|s| ≤ D · M / c`
  with `D` absolute.
* `exists_ED_directionCap_degree_bound` — the same with `M` and `c` fixed in
  advance, so the conclusion is a bare `s.card ≤ d` with `d : ℕ`. This is the
  shape `Kakeya.exists_inner_plank_ED_subfamily_of_bounded_conflict_degree`
  consumes as `edConflictDegree q U i ≤ d`.

Neither statement contains any overlap geometry: the direction cap and the
badness of the tubes against `K` are hypotheses, supplied by steps 1--3 of the
route (`Kakeya.Tube.direction_projective_cap_of_subset_cthickening` and the
plank-overlap step).
-/

@[expose] public section

open MeasureTheory Metric

namespace Kakeya

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E]

/-- **Absolute count of ED `δ`-tubes in a direction cap of radius `A · δ`.**

Fix `A > 0`. There are an absolute `D : ℕ` and a threshold `δ₀ > 0` such that
for every `δ ≤ δ₀`, any finite family of pairwise essentially distinct
`δ`-tubes whose directions all lie in the *projective* cap of radius `A · δ`
about a unit vector `e`, and which are all bad against a compact set `K` with
density `c` and thin-box volume `vol K ≤ M · δ ^ (n-1)`, satisfies

`|s| ≤ D · M / c`.

The bound is free of `δ`. The `A · δ` cap is split into at most
`4 ^ n · (max A c_slide / c_slide) ^ n` caps of radius `c_slide · δ` by
`Kakeya.EuclideanNet.exists_projective_cap_net_scaled`, and each piece is
counted by `Kakeya.position_count_le_of_bad_directionClass'`; both factors are
absolute. -/
theorem exists_ED_directionCap_card_bound (hn : 1 < Module.finrank ℝ E)
    {A : ℝ} (hA : 0 < A) :
    ∃ (D : ℕ) (δ₀ : ℝ), 0 < D ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {δ : NNReal} (_hδ : 0 < δ) (_hδ_le : (δ : ℝ) ≤ δ₀)
        {ι : Type*} (s : Finset ι) (T : ι → Tube δ E)
        (_hED : (s : Set ι).Pairwise
            (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier))
        {e : E} (_he_unit : ‖e‖ = 1)
        (_h_cap : ∀ i ∈ s,
            min ‖(T i).direction - e‖ ‖(T i).direction + e‖ ≤ A * (δ : ℝ))
        {K : Set E}
        (_hK_meas : MeasurableSet K) (_hK_cpt : IsCompact K)
        {M : ℝ} (_hM_pos : 0 < M)
        (_hK_vol : volume K ≤ ENNReal.ofReal M *
          (δ : ENNReal) ^ (Module.finrank ℝ E - 1))
        {c : ℝ} (_hc : 0 < c)
        (_hbad : ∀ i ∈ s,
            volume ((T i).carrier ∩ K) ≥ ENNReal.ofReal c * volume (T i).carrier),
        (s.card : ℝ) ≤ (D : ℝ) * M / c := by
  classical
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos (by linarith)
  obtain ⟨c_slide, C, δ₀', hc_slide_pos, hC_pos, hδ₀'_pos, hδ₀'_le1, hcount⟩ :=
    position_count_le_of_bad_directionClass' (E := E) hn
  let A' : ℝ := max A c_slide
  have hA'_pos : 0 < A' := lt_max_iff.mpr (Or.inl hA)
  have hA_le_A' : A ≤ A' := le_max_left A c_slide
  have hc_slide_le_A' : c_slide ≤ A' := le_max_right A c_slide
  let δ₀ : ℝ := min δ₀' (1 / (2 * A'))
  have hδ₀_pos : 0 < δ₀ := by
    dsimp [δ₀]
    exact lt_min hδ₀'_pos (by positivity)
  have hδ₀_le1 : δ₀ ≤ 1 := by
    dsimp [δ₀]
    exact le_trans (min_le_left δ₀' (1 / (2 * A'))) hδ₀'_le1
  let L : ℝ := EuclideanNet.localNetConstant E * (A' / c_slide) ^ Module.finrank ℝ E
  let D : ℕ := ⌈L * (C : ℝ)⌉₊ + 1
  have hD_pos : 0 < D := by
    dsimp [D]
    exact Nat.succ_pos _
  have hD_ge : L * (C : ℝ) ≤ (D : ℝ) := by
    have h1 : L * (C : ℝ) ≤ (⌈L * (C : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
    dsimp [D]
    push_cast
    linarith
  refine ⟨D, δ₀, hD_pos, hδ₀_pos, hδ₀_le1, ?_⟩
  intro δ hδ hδ_le ι s T hED e he_unit h_cap K hK_meas hK_cpt M hM_pos hK_vol c hc hbad
  have hδ_real_pos : (0 : ℝ) < (δ : ℝ) := NNReal.coe_pos.mpr hδ
  have hδ_le_δ₀' : (δ : ℝ) ≤ δ₀' :=
    le_trans hδ_le (min_le_left δ₀' (1 / (2 * A')))
  have hδ_le_inv : (δ : ℝ) ≤ 1 / (2 * A') :=
    le_trans hδ_le (min_le_right δ₀' (1 / (2 * A')))
  have hA'_δ_le : A' * (δ : ℝ) ≤ 1 / 2 := by
    have hδ_le2 : A' * (δ : ℝ) ≤ A' * (1 / (2 * A')) :=
      mul_le_mul_of_nonneg_left hδ_le_inv hA'_pos.le
    have hcancel : A' * (1 / (2 * A')) = 1 / 2 := by
      field_simp [hA'_pos.ne']
    rw [hcancel] at hδ_le2
    exact hδ_le2
  have hA_le_A'_δ : A * (δ : ℝ) ≤ A' * (δ : ℝ) :=
    mul_le_mul_of_nonneg_right hA_le_A' hδ_real_pos.le
  obtain ⟨N, hN_unit, hN_cover, hN_sep, hNcard⟩ :=
    EuclideanNet.exists_projective_cap_net_scaled e he_unit (A := A') (a := c_slide) (δ := (δ : ℝ))
      hc_slide_pos hc_slide_le_A' hδ_real_pos hA'_δ_le
  choose! g hgN hgcap using fun i (hi : i ∈ s) =>
    hN_cover (T i).direction (T i).norm_direction (le_trans (h_cap i hi) hA_le_A'_δ)
  have hfibre_bound : ∀ b ∈ N,
      (((s.filter (fun i => g i = b)).card : ℕ) : ℝ) ≤ (C : ℝ) * M / c := by
    intro b hbN
    have hED_fibre : ((s.filter (fun i => g i = b) : Finset ι) : Set ι).Pairwise
        (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) := by
      exact Set.Pairwise.mono
        (Finset.coe_subset.mpr (Finset.filter_subset (fun i => g i = b) s)) hED
    have hdir_fibre : ∀ i ∈ s.filter (fun i => g i = b),
        min ‖(T i).direction - b‖ ‖(T i).direction + b‖ ≤ c_slide * (δ : ℝ) := by
      intro i hi
      have hmem := Finset.mem_filter.mp hi
      have hgcap_i : min ‖(T i).direction - g i‖ ‖(T i).direction + g i‖ ≤ c_slide * (δ : ℝ) :=
        hgcap i hmem.1
      rwa [hmem.2] at hgcap_i
    have hbad_fibre : ∀ i ∈ s.filter (fun i => g i = b),
        volume ((T i).carrier ∩ K) ≥ ENNReal.ofReal c * volume (T i).carrier := by
      intro i hi
      exact hbad i (Finset.mem_filter.mp hi).1
    exact hcount (δ := δ) hδ hδ_le_δ₀' (s := s.filter (fun i => g i = b)) (T := T)
      hED_fibre (e := b) (hN_unit b hbN) hdir_fibre (K := K) hK_meas hK_cpt
      (M := M) hM_pos hK_vol (c := c) hc hbad_fibre
  have hsum_card : (s.card : ℝ) = ∑ b ∈ N, (((s.filter (fun i => g i = b)).card : ℕ) : ℝ) := by
    norm_cast
    exact Finset.card_eq_sum_card_fiberwise (M := E) (f := g) (t := N) hgN
  have hmass_nonneg : 0 ≤ (C : ℝ) * M / c := by positivity
  have hMc_nonneg : 0 ≤ M / c := div_nonneg hM_pos.le hc.le
  calc
    (s.card : ℝ) ≤ (D : ℝ) * M / c := by
      calc
        (s.card : ℝ) = ∑ b ∈ N, ((s.filter (fun i => g i = b)).card : ℝ) := hsum_card
        _ ≤ ∑ b ∈ N, (C : ℝ) * M / c := Finset.sum_le_sum (fun b hb => hfibre_bound b hb)
        _ = (N.card : ℝ) * ((C : ℝ) * M / c) := by
            simp
        _ ≤ L * ((C : ℝ) * M / c) := mul_le_mul_of_nonneg_right hNcard hmass_nonneg
        _ = (L * (C : ℝ)) * (M / c) := by ring
        _ ≤ (D : ℝ) * (M / c) := mul_le_mul_of_nonneg_right hD_ge hMc_nonneg
        _ = (D : ℝ) * M / c := by ring

/-- **The conflict-degree form.**

Same statement as `Kakeya.exists_ED_directionCap_card_bound` with the thin-box
constant `M` and the density `c` fixed in advance, so that the conclusion is a
bare natural-number bound `s.card ≤ d`.

This is exactly the numerical input of
`Kakeya.exists_inner_plank_ED_subfamily_of_bounded_conflict_degree`: taking `s`
to be the conflict set `{j ∈ q | ¬ IsEssentiallyDistinct (U i) (U j)}` of a
fixed member turns the conclusion into `edConflictDegree q U i ≤ d`, with `d`
absolute rather than a power of `δ`. -/
theorem exists_ED_directionCap_degree_bound (hn : 1 < Module.finrank ℝ E)
    {A M c : ℝ} (hA : 0 < A) (hM : 0 < M) (hc : 0 < c) :
    ∃ (d : ℕ) (δ₀ : ℝ), 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {δ : NNReal} (_hδ : 0 < δ) (_hδ_le : (δ : ℝ) ≤ δ₀)
        {ι : Type*} (s : Finset ι) (T : ι → Tube δ E)
        (_hED : (s : Set ι).Pairwise
            (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier))
        {e : E} (_he_unit : ‖e‖ = 1)
        (_h_cap : ∀ i ∈ s,
            min ‖(T i).direction - e‖ ‖(T i).direction + e‖ ≤ A * (δ : ℝ))
        {K : Set E}
        (_hK_meas : MeasurableSet K) (_hK_cpt : IsCompact K)
        (_hK_vol : volume K ≤ ENNReal.ofReal M *
          (δ : ENNReal) ^ (Module.finrank ℝ E - 1))
        (_hbad : ∀ i ∈ s,
            volume ((T i).carrier ∩ K) ≥ ENNReal.ofReal c * volume (T i).carrier),
        s.card ≤ d := by
  obtain ⟨D, δ₀, _hD_pos, hδ₀_pos, hδ₀_le1, hbound⟩ :=
    exists_ED_directionCap_card_bound (E := E) (A := A) hn hA
  refine ⟨⌈(D : ℝ) * M / c⌉₊, δ₀, hδ₀_pos, hδ₀_le1, ?_⟩
  intro δ hδ hδ_le ι s T hED e he_unit h_cap K hK_meas hK_cpt hK_vol hbad
  have hb : (s.card : ℝ) ≤ (D : ℝ) * M / c :=
    hbound hδ hδ_le s T hED he_unit h_cap hK_meas hK_cpt hM hK_vol hc hbad
  exact_mod_cast (le_trans hb (Nat.le_ceil ((D : ℝ) * M / c)))

end -- close noncomputable section

end Kakeya
