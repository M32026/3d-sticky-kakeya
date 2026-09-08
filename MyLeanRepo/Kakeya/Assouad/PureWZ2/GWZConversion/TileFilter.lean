import MyLeanRepo.Kakeya.Streamlined.Families
import MyLeanRepo.Kakeya.Streamlined.TubeRefinement
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZBridge

/-!
# Tile filtering: per-tile Frostman bounds, uniformity, and retention

Given a GWZ Frostman condition on an A-fiber (a family of δ-tubes all contained
in an A-dilated coarse carrier), these lemmas derive:

1. Per-tile count upper bound from Frostman.
2. Pairwise uniformity among tiles filtered by a substantiality threshold.
3. Mass bound for unfiltered tiles.
4. Parameter algebra confirming the uniformity constant `C_in / δ^η = C_out`.

These feed the construction of a `WZ2PaperPureScaleCoverData` from GWZ data.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

open Kakeya.Streamlined

/--
Per-tile count upper bound from a GWZ Frostman condition.

If every body in the fiber has volume `V`, and Frostman gives
`containedMass(K) * volume(ACarrier) ≤ C * mass * volume(K)` for every convex
`K ⊆ ACarrier`, then for any convex tile `K ⊆ ACarrier`:

`containedCount(K) * volume(ACarrier) ≤ C * enncard * volume(K)`.
-/
theorem gwz_frostman_perTile_count_bound
    {F : BodyFamily} {V : ENNReal}
    (hV_pos : 0 < V)
    (hV_ne_top : V ≠ ⊤)
    (h_all_vol : ∀ i, (F.body i).volume = V)
    {C : ENNReal} {ACarrier : Set Point3}
    (_h_ACarrier_pos : 0 < volume ACarrier)
    (_h_ACarrier_ne_top : volume ACarrier ≠ ⊤)
    (hfrost : ∀ (K : Set Point3), Convex ℝ K → K ⊆ ACarrier →
      F.containedMass K * volume ACarrier ≤ C * F.mass * volume K)
    {K : Set Point3}
    (hK_convex : Convex ℝ K)
    (hK_subset : K ⊆ ACarrier) :
    F.containedCount K * volume ACarrier ≤ C * F.enncard * volume K := by
  have h_mass : F.mass = F.enncard * V := by
    simp only [BodyFamily.mass, BodyFamily.enncard]
    have h : (∑ i : Fin F.card, (F.body i).volume) = ∑ i : Fin F.card, V := by
      apply Finset.sum_congr rfl
      intro i _
      exact h_all_vol i
    rw [h, Finset.sum_const]
    simp [mul_comm]
  have h_contained : F.containedMass K = F.containedCount K * V := by
    simp only [BodyFamily.containedMass, BodyFamily.containedCount]
    have h : (∑ i ∈ F.containedIndices K, (F.body i).volume) =
        ∑ i ∈ F.containedIndices K, V := by
      apply Finset.sum_congr rfl
      intro i _
      exact h_all_vol i
    rw [h, Finset.sum_const]
    simp
  have h := hfrost K hK_convex hK_subset
  rw [h_contained, h_mass] at h
  have h_left : (F.containedCount K * V) * volume ACarrier =
      V * (F.containedCount K * volume ACarrier) := by
    ac_rfl
  have h_right : C * (F.enncard * V) * volume K =
      V * (C * F.enncard * volume K) := by
    ac_rfl
  rw [h_left, h_right] at h
  exact (ENNReal.mul_le_mul_iff_right hV_pos.ne' hV_ne_top).mp h

/--
Pairwise uniformity among filtered tiles.

Given tiles that are convex subsets of `ACarrier`, filter by
`containedCount(tile) ≥ threshold * enncard`. Then for any two filtered tiles:

`containedCount(t1) * threshold ≤ C * containedCount(t2)`.

Equivalently, when `threshold ≠ 0, ⊤`:
`containedCount(t1) ≤ C * threshold⁻¹ * containedCount(t2)`.
-/
theorem gwz_filtered_tile_uniformity
    {F : BodyFamily} {V : ENNReal}
    (hV_pos : 0 < V)
    (hV_ne_top : V ≠ ⊤)
    (h_all_vol : ∀ i, (F.body i).volume = V)
    {C threshold : ENNReal}
    {ACarrier : Set Point3}
    (h_ACarrier_pos : 0 < volume ACarrier)
    (h_ACarrier_ne_top : volume ACarrier ≠ ⊤)
    (hfrost : ∀ (K : Set Point3), Convex ℝ K → K ⊆ ACarrier →
      F.containedMass K * volume ACarrier ≤ C * F.mass * volume K)
    {tiles : Finset (Set Point3)}
    (htiles_convex : ∀ t ∈ tiles, Convex ℝ t)
    (htiles_subset : ∀ t ∈ tiles, t ⊆ ACarrier)
    (filtered : Finset (Set Point3))
    (hfiltered_subset : filtered ⊆ tiles)
    (hsubstantial : ∀ t ∈ filtered, threshold * F.enncard ≤ F.containedCount t)
    {t1 t2 : Set Point3}
    (ht1 : t1 ∈ filtered)
    (ht2 : t2 ∈ filtered) :
    F.containedCount t1 * threshold ≤ C * F.containedCount t2 := by
  have h1 : t1 ∈ tiles := hfiltered_subset ht1
  have h2 : t2 ∈ tiles := hfiltered_subset ht2
  have h_upper1 : F.containedCount t1 * volume ACarrier ≤
      C * F.enncard * volume t1 :=
    gwz_frostman_perTile_count_bound hV_pos hV_ne_top h_all_vol
      h_ACarrier_pos h_ACarrier_ne_top hfrost
      (htiles_convex t1 h1) (htiles_subset t1 h1)
  have h_vol_t1 : volume t1 ≤ volume ACarrier :=
    measure_mono (htiles_subset t1 h1)
  have h_count1 : F.containedCount t1 ≤ C * F.enncard := by
    have h : F.containedCount t1 * volume ACarrier ≤ C * F.enncard * volume ACarrier := by
      calc
        F.containedCount t1 * volume ACarrier
          ≤ C * F.enncard * volume t1 := h_upper1
        _ ≤ C * F.enncard * volume ACarrier := by gcongr
    have h' : volume ACarrier * F.containedCount t1 ≤ volume ACarrier * (C * F.enncard) := by
      have h1 : volume ACarrier * F.containedCount t1 = F.containedCount t1 * volume ACarrier := by ac_rfl
      have h2 : volume ACarrier * (C * F.enncard) = C * F.enncard * volume ACarrier := by ac_rfl
      rw [h1, h2]
      exact h
    exact (ENNReal.mul_le_mul_iff_right h_ACarrier_pos.ne' h_ACarrier_ne_top).mp h'
  have h_lower2 : threshold * F.enncard ≤ F.containedCount t2 :=
    hsubstantial t2 ht2
  calc
    F.containedCount t1 * threshold
      ≤ (C * F.enncard) * threshold := by gcongr
    _ = C * (threshold * F.enncard) := by ac_rfl
    _ ≤ C * F.containedCount t2 := by gcongr

/--
Mass bound for unfiltered tiles.

Each unfiltered tile has `containedCount ≤ threshold * enncard`. Summing over
all unfiltered tiles gives:

`∑_{t unfiltered} containedCount(t) * V ≤ N_unfiltered * threshold * enncard * V`.
-/
theorem gwz_unfiltered_tiles_mass_bound
    {F : BodyFamily} {V : ENNReal}
    {threshold : ENNReal}
    {tiles : Finset (Set Point3)}
    (filtered : Finset (Set Point3))
    (_hfiltered_subset : filtered ⊆ tiles)
    (hnotsubstantial : ∀ t ∈ tiles \ filtered, F.containedCount t ≤ threshold * F.enncard) :
    ∑ t ∈ tiles \ filtered, F.containedCount t * V ≤
      (tiles \ filtered).card * threshold * F.enncard * V := by
  have h : ∀ t ∈ tiles \ filtered, F.containedCount t * V ≤ threshold * F.enncard * V := by
    intro t ht
    have h' : F.containedCount t ≤ threshold * F.enncard := hnotsubstantial t ht
    gcongr
  calc
    ∑ t ∈ tiles \ filtered, F.containedCount t * V
      ≤ ∑ t ∈ tiles \ filtered, threshold * F.enncard * V :=
        Finset.sum_le_sum h
    _ = (tiles \ filtered).card * (threshold * F.enncard * V) := by
      rw [Finset.sum_const]
      ring_nf
    _ = (tiles \ filtered).card * threshold * F.enncard * V := by
      ring

/--
Parameter algebra: the uniformity constant after filtering.

Given `C_in = δ^{-inputLoss}` and `threshold = δ^η` with
`η = outputLoss - inputLoss`, we have:

`C_in * threshold⁻¹ = δ^{-outputLoss} = C_out`.

This requires `0 < δ`.
-/
theorem gwz_uniformity_constant_algebra
    {δ inputLoss outputLoss : ℝ}
    (hδ : 0 < δ)
    (_hδ1 : δ ≤ 1)
    (_h_in_pos : 0 < inputLoss)
    (_h_eta_pos : 0 < outputLoss - inputLoss)
    (_h_eta : outputLoss - inputLoss = outputLoss / 2) :
    Kakeya.realRpowENN δ (-inputLoss) * (Kakeya.realRpowENN δ (outputLoss - inputLoss))⁻¹ =
    Kakeya.realRpowENN δ (-outputLoss) := by
  simp only [Kakeya.realRpowENN]
  have hpos2 : 0 < Real.rpow δ (outputLoss - inputLoss) := Real.rpow_pos_of_pos hδ _
  have hdiv : Real.rpow δ (-inputLoss) / Real.rpow δ (outputLoss - inputLoss) =
      Real.rpow δ (-outputLoss) := by
    have h8 : Real.rpow δ (-inputLoss - (outputLoss - inputLoss)) =
        Real.rpow δ (-inputLoss) / Real.rpow δ (outputLoss - inputLoss) :=
      Real.rpow_sub hδ (-inputLoss) (outputLoss - inputLoss)
    have h9 : -inputLoss - (outputLoss - inputLoss) = -outputLoss := by ring
    rw [h9] at h8
    exact h8.symm
  have h6 : (ENNReal.ofReal (Real.rpow δ (-inputLoss)) *
      (ENNReal.ofReal (Real.rpow δ (outputLoss - inputLoss)))⁻¹) =
      ENNReal.ofReal (Real.rpow δ (-inputLoss) / Real.rpow δ (outputLoss - inputLoss)) := by
    set x := Real.rpow δ (-inputLoss) with hx
    set y := Real.rpow δ (outputLoss - inputLoss) with hy
    have hx_pos : 0 < x := Real.rpow_pos_of_pos hδ _
    have hy_pos : 0 < y := hpos2
    have h1 : ENNReal.ofReal x / ENNReal.ofReal y = ENNReal.ofReal (x / y) :=
      (ENNReal.ofReal_div_of_pos hy_pos).symm
    have h2 : ENNReal.ofReal x * (ENNReal.ofReal y)⁻¹ = ENNReal.ofReal x / ENNReal.ofReal y := by
      rw [div_eq_mul_inv]
    rw [h2, h1]
  rw [h6, hdiv]

/--
Package pairwise uniformity on a (restricted) coarse family as the official
`WZ2PaperPureFullFibersAreCUniform` structure.

This is the bridge between the filtered-tile pairwise bound (from
`gwz_filtered_tile_uniformity`) and the `WZ2PaperPureScaleCoverData`
requirement.  It is logically a tautology, but named for clarity in the
GWZ-to-WZ2 assembly.
-/
theorem gwz_restrict_coarse_uniformity
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {C : ENNReal}
    (hPairwise :
      ∀ (j1 j2 : Fin coarse.card),
        (wz2PaperOrdinaryFullFiberCount fine coarse j1 : ENNReal) ≤
          C * (wz2PaperOrdinaryFullFiberCount fine coarse j2 : ENNReal))
    :
    WZ2PaperPureFullFibersAreCUniform fine coarse C :=
  hPairwise

/--
Corrected pairwise uniformity of strict fiber counts across filtered tiles.

The original statement (without `hFiberUniform`) is false: take two tiles with
`fiberCount(1) = 100`, `fiberCount(2) = 1`, and all other parameters equal to 1;
then `count(1) = 100`, `count(2) = 1`, but the conclusion demands `100 ≤ 1`.

With the GWZ full-fiber uniformity hypothesis
`fiberCount(j1) ≤ C_in * fiberCount(j2)`, the uniformity constant becomes
`C_in² * K_vol / δ^η`.  Here `K_vol` is an upper bound on the tile-to-A-carrier
volume ratio (conservatively `A³`, since the A-carrier is a homothety by `A`).

## Parameter viability

Choose `inputLoss = outputLoss / 4` and `η = outputLoss / 4`.  Then
`C_in = δ^{-outputLoss/4}` and

```
C_in² * A³ / δ^η = A³ * δ^{-outputLoss/4} ≤ δ^{-outputLoss} = C_out
```

for sufficiently small `δ` (since `A³ ≤ δ^{-3outputLoss/4}` eventually).
The same parameter choice also satisfies the filtering-retention condition
`A³ * δ^η ≤ 1/2` and the CWB bound `27 * C_in / δ^η = 27 ≤ C_out`.
-/
theorem gwz_tile_pairwise_uniformity
    {delta rho₀ : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho₀}
    {C_in C_out K_vol : ENNReal}
    {eta : ℝ}
    (hdelta : 0 < delta)
    (selectedCoarse : Kakeya.Streamlined.TubeSubfamily coarse)
    (fiberCount : Fin selectedCoarse.family.card → ENNReal)
    (hFiberUniform :
      ∀ (j1 j2 : Fin selectedCoarse.family.card),
        fiberCount j1 ≤ C_in * fiberCount j2)
    (hUpper :
      ∀ (j : Fin selectedCoarse.family.card),
        (wz2PaperOrdinaryFullFiberCount fine selectedCoarse.family j : ENNReal) ≤
          C_in * K_vol * fiberCount j)
    (hLower :
      ∀ (j : Fin selectedCoarse.family.card),
        (wz2PaperOrdinaryFullFiberCount fine selectedCoarse.family j : ENNReal) ≥
          Kakeya.realRpowENN delta eta * fiberCount j)
    (hParam :
      C_in * C_in * K_vol ≤
      C_out * Kakeya.realRpowENN delta eta)
    :
    ∀ (j1 j2 : Fin selectedCoarse.family.card),
      (wz2PaperOrdinaryFullFiberCount fine selectedCoarse.family j1 : ENNReal) ≤
        C_out * (wz2PaperOrdinaryFullFiberCount fine selectedCoarse.family j2 : ENNReal) := by
  let count : Fin selectedCoarse.family.card → ENNReal := fun j =>
    (wz2PaperOrdinaryFullFiberCount fine selectedCoarse.family j : ENNReal)
  let threshold : ENNReal := Kakeya.realRpowENN delta eta
  have hthreshold_pos : 0 < threshold := by
    simp [threshold, Kakeya.realRpowENN, Real.rpow_pos_of_pos hdelta]
  have hthreshold_ne_zero : threshold ≠ 0 := hthreshold_pos.ne'
  have hthreshold_ne_top : threshold ≠ ⊤ := by
    simp [threshold, Kakeya.realRpowENN, ENNReal.ofReal_ne_top]
  intro j1 j2
  have h1 : count j1 ≤ C_in * K_vol * fiberCount j1 := hUpper j1
  have h2 : fiberCount j1 ≤ C_in * fiberCount j2 := hFiberUniform j1 j2
  have h3 : count j1 ≤ (C_in * C_in * K_vol) * fiberCount j2 := by
    calc
      count j1 ≤ C_in * K_vol * fiberCount j1 := h1
      _ ≤ C_in * K_vol * (C_in * fiberCount j2) := by gcongr
      _ = (C_in * C_in * K_vol) * fiberCount j2 := by ac_rfl
  have h4 : threshold * fiberCount j2 ≤ count j2 := hLower j2
  have h5 : fiberCount j2 ≤ threshold⁻¹ * count j2 := by
    calc
      fiberCount j2
        = threshold⁻¹ * (threshold * fiberCount j2) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hthreshold_ne_zero hthreshold_ne_top]; ring
      _ ≤ threshold⁻¹ * count j2 := by gcongr
  have h6 : (C_in * C_in * K_vol) * threshold⁻¹ ≤ C_out := by
    have h7 : (C_in * C_in * K_vol) * threshold⁻¹ ≤
        (C_out * threshold) * threshold⁻¹ := by gcongr
    have h8 : (C_out * threshold) * threshold⁻¹ = C_out := by
      rw [mul_assoc, ENNReal.mul_inv_cancel hthreshold_ne_zero hthreshold_ne_top]; ring
    rw [h8] at h7
    exact h7
  calc
    count j1 ≤ (C_in * C_in * K_vol) * fiberCount j2 := h3
    _ ≤ (C_in * C_in * K_vol) * (threshold⁻¹ * count j2) := by gcongr
    _ = ((C_in * C_in * K_vol) * threshold⁻¹) * count j2 := by ac_rfl
    _ ≤ C_out * count j2 := by gcongr

/-- ENNReal retention: total = kept + lost, lost ≤ c * total, c ≤ 1/2, total ≠ ⊤
    implies total ≤ 2 * kept. -/
lemma gwz_retention_half {total kept lost c : ENNReal}
    (h_sum : total = kept + lost)
    (h_lost : lost ≤ c * total)
    (hc : c ≤ 1 / 2)
    (h_total_ne_top : total ≠ ⊤) :
    total ≤ 2 * kept := by
  have h1 : lost ≤ (2 : ENNReal)⁻¹ * total := by
    calc lost ≤ c * total := h_lost
         _ ≤ (1 / 2 : ENNReal) * total := by gcongr
         _ = (2 : ENNReal)⁻¹ * total := by simp
  have h2_ne_zero : (2 : ENNReal) ≠ 0 := by simp
  have h2_ne_top : (2 : ENNReal) ≠ ⊤ := by simp
  have h_two_half : (2 : ENNReal) * (2 : ENNReal)⁻¹ = 1 :=
    ENNReal.mul_inv_cancel h2_ne_zero h2_ne_top
  have h_2lost : 2 * lost ≤ total := by
    calc
      2 * lost ≤ 2 * ((2 : ENNReal)⁻¹ * total) := by gcongr
      _ = ((2 : ENNReal) * (2 : ENNReal)⁻¹) * total := by rw [mul_assoc]
      _ = (1 : ENNReal) * total := by rw [h_two_half]
      _ = total := by ring
  have h_main : 2 * total ≤ 2 * kept + total := by
    calc
      2 * total = 2 * (kept + lost) := by rw [h_sum]
      _ = 2 * kept + 2 * lost := by rw [mul_add]
      _ ≤ 2 * kept + total := by gcongr
  have h_cancel : total + total ≤ total + 2 * kept := by
    have h_eq1 : 2 * total = total + total := by ring
    have h_eq2 : 2 * kept + total = total + 2 * kept := by ac_rfl
    rw [h_eq1, h_eq2] at h_main
    exact h_main
  exact (ENNReal.add_le_add_iff_left h_total_ne_top).mp h_cancel

abbrev STubeFamily (δ : ℝ) := Kakeya.Streamlined.TubeFamily δ
abbrev STubeSubfamily {δ : ℝ} (F : STubeFamily δ) := Kakeya.Streamlined.TubeSubfamily F

/--
Corrected substantiality filtering (full source, before coloring).

The original statement (with `fine : STubeSubfamily source`) is FALSE:
when `fineFiberCount ≪ fiberCount`, the threshold exceeds every tile count,
so all tiles are unfiltered and nothing is retained.

FIX: Apply filtering to the FULL source family (before coloring), so
`fineFiberCount = fiberCount` and the substantiality threshold is meaningful.

Given a partitioning cover with at most `K` coarse tiles per GWZ parent and
at most `L` parents per source tube, filter coarse tiles by
`count(j) ≥ δ^η · fiberCount(parentOf j)`. Then:
- Unfiltered mass ≤ K·L·δ^η · source ≤ source/2
- Retention: `source.enncard ≤ 2 · filteredSource.enncard`
- The filtered family inherits the partitioning cover (covers + doubled-fiber disjointness)
- Filtered fibers are substantial: count ≥ δ^η · fullFiberCount
-/
theorem gwz_tile_filter_substantiality
    {δ : ℝ} (_hδ : 0 < δ)
    {A : ℝ} (_hA : 1 ≤ A)
    {C_in : ENNReal}
    {source : STubeFamily δ}
    {rho₀ : ℝ} {coarse : STubeFamily rho₀}
    {K L : ℕ}
    (cover : WZ2PaperPurePartitioningCover source coarse)
    (gwzScale : Kakeya.Streamlined.AdmissibleScale δ)
    (scaleData : PureWZ2GWZScaleData (A := A) source gwzScale C_in)
    (parentOf : Fin coarse.card → Fin scaleData.coarse.card)
    (hTilesPerParent :
      ∀ (p : Fin scaleData.coarse.card),
        (Finset.univ.filter (fun j => parentOf j = p)).card ≤ K)
    (hOverlap :
      ∀ (i : Fin source.card),
        (Finset.univ.filter (fun p => i ∈ scaleData.fullFiberIndices p)).card ≤ L)
    (η : ℝ) (_hη : 0 < η)
    (hδ_small :
      ((K * L : ℕ) : ENNReal) * Kakeya.realRpowENN δ η ≤ (1 : ENNReal) / 2)
    :
    ∃ (filteredCoarse : STubeSubfamily coarse)
      (filteredSource : STubeSubfamily source)
      (_ : WZ2PaperPurePartitioningCover filteredSource.family filteredCoarse.family)
      (_ :
        ∀ (j : Fin filteredCoarse.family.card),
          (wz2PaperOrdinaryFullFiberCount filteredSource.family filteredCoarse.family j : ENNReal) ≥
            Kakeya.realRpowENN δ η *
              ↑(scaleData.fullFiberIndices (parentOf (filteredCoarse.embedding j))).card)
      (_ : source.enncard ≤ 2 * filteredSource.family.enncard),
      True := by
  let threshold : ENNReal := Kakeya.realRpowENN δ η
  let strictFiber (j : Fin coarse.card) : Finset (Fin source.card) :=
    wz2PaperOrdinaryFullFiberIndices source coarse j
  let fiberCount (p : Fin scaleData.coarse.card) : ENNReal :=
    (scaleData.fullFiberIndices p).card
  let substantial (j : Fin coarse.card) : Prop :=
    threshold * fiberCount (parentOf j) ≤ (strictFiber j).card
  let filteredCoarseIdx : Finset (Fin coarse.card) :=
    Finset.univ.filter substantial
  let unfilteredIdx : Finset (Fin coarse.card) :=
    Finset.univ \ filteredCoarseIdx
  let filteredCoarse : STubeSubfamily coarse :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset coarse filteredCoarseIdx
  let filteredSourceIdx : Finset (Fin source.card) :=
    Finset.univ.filter fun i => ∃ j ∈ filteredCoarseIdx, i ∈ strictFiber j
  let filteredSource : STubeSubfamily source :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset source filteredSourceIdx
  let lostIdx : Finset (Fin source.card) :=
    Finset.univ \ filteredSourceIdx

  have h_source_ne_top : source.enncard ≠ ⊤ := ENNReal.coe_ne_top

  have h_embedding_mem :
      ∀ {δ : ℝ} {F : STubeFamily δ} {I : Finset (Fin F.card)}
        (i : Fin (Kakeya.Streamlined.TubeSubfamily.fromFinset F I).family.card),
        (Kakeya.Streamlined.TubeSubfamily.fromFinset F I).embedding i ∈ I := by
    intro δ F I i
    dsimp only [Kakeya.Streamlined.TubeSubfamily.fromFinset]
    exact Finset.orderEmbOfFin_mem I rfl i

  have h_embedding_surjective :
      ∀ {δ : ℝ} {F : STubeFamily δ} {I : Finset (Fin F.card)}
        (k : Fin F.card), k ∈ I →
        ∃ i : Fin (Kakeya.Streamlined.TubeSubfamily.fromFinset F I).family.card,
          (Kakeya.Streamlined.TubeSubfamily.fromFinset F I).embedding i = k := by
    intro δ F I k hk
    have h_image : Finset.map (I.orderEmbOfFin rfl).toEmbedding Finset.univ = I :=
      Finset.map_orderEmbOfFin_univ I rfl
    have h_k_in_image : k ∈ Finset.map (I.orderEmbOfFin rfl).toEmbedding Finset.univ := by
      rw [h_image]; exact hk
    rcases Finset.mem_map.mp h_k_in_image with ⟨i, _, rfl⟩
    exact ⟨i, rfl⟩

  have h_unfiltered_bound :
      ∀ j ∈ unfilteredIdx, ((strictFiber j).card : ENNReal) ≤ threshold * fiberCount (parentOf j) := by
    intro j hj
    have h_not : ¬(threshold * fiberCount (parentOf j) ≤ (strictFiber j).card) := by
      simpa [unfilteredIdx, filteredCoarseIdx, substantial, Finset.mem_filter] using hj
    exact Std.le_of_not_ge h_not

  have h1_sum : ∑ j ∈ unfilteredIdx, ((strictFiber j).card : ENNReal) ≤
      ∑ j ∈ unfilteredIdx, threshold * fiberCount (parentOf j) := by
    apply Finset.sum_le_sum
    intro j hj
    exact h_unfiltered_bound j hj

  have h2_sum : ∑ j ∈ unfilteredIdx, threshold * fiberCount (parentOf j) =
      threshold * ∑ j ∈ unfilteredIdx, fiberCount (parentOf j) := by
    rw [Finset.mul_sum]

  let fiberOfParent (p : Fin scaleData.coarse.card) : Finset (Fin coarse.card) :=
    unfilteredIdx.filter (fun j => parentOf j = p)

  have h_group_final : ∑ j ∈ unfilteredIdx, fiberCount (parentOf j) =
      ∑ p : Fin scaleData.coarse.card, ((fiberOfParent p).card : ENNReal) * fiberCount p := by
    have h4 : ∀ (j : Fin coarse.card),
        ∑ p : Fin scaleData.coarse.card, (if parentOf j = p then fiberCount p else 0) =
        fiberCount (parentOf j) := by
      intro j
      let P : Fin scaleData.coarse.card → Prop := fun p => parentOf j = p
      have h_filter : (Finset.univ.filter P) = {parentOf j} := by
        ext p; simp [P]; tauto
      rw [Finset.sum_ite, h_filter]
      simp
    have h5 : ∑ j ∈ unfilteredIdx, fiberCount (parentOf j) =
        ∑ j ∈ unfilteredIdx, ∑ p : Fin scaleData.coarse.card,
          (if parentOf j = p then fiberCount p else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      exact (h4 j).symm
    rw [h5, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.sum_ite]
    simp [fiberOfParent, Finset.sum_const]

  have h_fiber_card_le_K : ∀ p : Fin scaleData.coarse.card,
      (fiberOfParent p).card ≤ K := by
    intro p
    have h6 : (fiberOfParent p).card ≤ (Finset.univ.filter (fun j => parentOf j = p)).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ unfilteredIdx))
    have h7 : (Finset.univ.filter (fun j => parentOf j = p)).card ≤ K := hTilesPerParent p
    exact le_trans h6 h7

  have h6_sum : ∑ p : Fin scaleData.coarse.card, ((fiberOfParent p).card : ENNReal) * fiberCount p ≤
      (K : ENNReal) * ∑ p : Fin scaleData.coarse.card, fiberCount p := by
    calc
      ∑ p, _ ≤ ∑ p, (K : ENNReal) * fiberCount p := by
        apply Finset.sum_le_sum; intro p _; gcongr; exact h_fiber_card_le_K p
      _ = (K : ENNReal) * ∑ p, fiberCount p := by rw [Finset.mul_sum]

  have h_sum_bound : ∑ j ∈ unfilteredIdx, ((strictFiber j).card : ENNReal) ≤
      threshold * (K : ENNReal) * ∑ p : Fin scaleData.coarse.card, fiberCount p := by
    calc
      ∑ j ∈ unfilteredIdx, ((strictFiber j).card : ENNReal)
        ≤ ∑ j ∈ unfilteredIdx, threshold * fiberCount (parentOf j) := h1_sum
      _ = threshold * ∑ j ∈ unfilteredIdx, fiberCount (parentOf j) := h2_sum
      _ = threshold * (∑ p, ((fiberOfParent p).card : ENNReal) * fiberCount p) := by
          rw [h_group_final]
      _ ≤ threshold * ((K : ENNReal) * ∑ p, fiberCount p) := by gcongr
      _ = threshold * (K : ENNReal) * ∑ p, fiberCount p := by ring

  let indicator (p : Fin scaleData.coarse.card) (i : Fin source.card) : ENNReal :=
    if i ∈ scaleData.fullFiberIndices p then 1 else 0

  have h1_indicator : ∀ p, fiberCount p = ∑ i : Fin source.card, indicator p i := by
    intro p
    dsimp only [fiberCount, indicator]
    rw [Finset.sum_ite]
    simp [Finset.sum_const]

  have h2_indicator : ∀ i, ∑ p : Fin scaleData.coarse.card, indicator p i =
      ((Finset.univ.filter (fun p : Fin scaleData.coarse.card => i ∈ scaleData.fullFiberIndices p)).card : ENNReal) := by
    intro i
    dsimp only [indicator]
    rw [Finset.sum_ite]
    simp [Finset.sum_const]

  have h_double_count :
      ∑ p : Fin scaleData.coarse.card, fiberCount p =
      ∑ i : Fin source.card,
        ((Finset.univ.filter (fun p : Fin scaleData.coarse.card => i ∈ scaleData.fullFiberIndices p)).card : ENNReal) := by
    calc
      ∑ p, fiberCount p
        = ∑ p, ∑ i : Fin source.card, indicator p i := by
          apply Finset.sum_congr rfl; intro p _; exact h1_indicator p
      _ = ∑ i : Fin source.card, ∑ p : Fin scaleData.coarse.card, indicator p i := by
          rw [Finset.sum_comm]
      _ = ∑ i : Fin source.card, _ := by
          apply Finset.sum_congr rfl; intro i _; exact h2_indicator i

  have h_overlap_bound :
      ∀ i : Fin source.card,
        ((Finset.univ.filter (fun p : Fin scaleData.coarse.card => i ∈ scaleData.fullFiberIndices p)).card : ENNReal) ≤ (L : ENNReal) := by
    intro i
    exact Nat.cast_le.mpr (hOverlap i)

  have h_fiber_sum : ∑ p : Fin scaleData.coarse.card, fiberCount p ≤ (L : ENNReal) * source.enncard := by
    calc
      ∑ p, fiberCount p
        = ∑ i : Fin source.card, _ := h_double_count
      _ ≤ ∑ i : Fin source.card, (L : ENNReal) := by
          apply Finset.sum_le_sum; intro i _; exact h_overlap_bound i
      _ = (source.card : ENNReal) * (L : ENNReal) := by
          have h_univ : (Finset.univ : Finset (Fin source.card)).card = source.card := by
            simp [Finset.card_univ]
          rw [Finset.sum_const, h_univ]; ring
      _ = (L : ENNReal) * source.enncard := by
          have h : source.enncard = (source.card : ENNReal) := by rfl
          rw [h]; ring

  have h_lost_subset : lostIdx ⊆ Finset.biUnion unfilteredIdx strictFiber := by
    intro i hi
    have h_not : i ∉ filteredSourceIdx := by simpa [lostIdx] using hi
    rcases cover.covers i with ⟨j, hj⟩
    have h_in : i ∈ strictFiber j := by
      simpa [strictFiber, wz2PaperOrdinaryFullFiberIndices] using hj
    by_cases hf : j ∈ filteredCoarseIdx
    · exfalso
      have h_goal : i ∈ filteredSourceIdx := by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ i, ⟨j, hf, h_in⟩⟩
      exact h_not h_goal
    · have h_uf : j ∈ unfilteredIdx := by
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, hf⟩
      exact Finset.mem_biUnion.mpr ⟨j, h_uf, h_in⟩

  have h_lost_le_sum : (lostIdx.card : ENNReal) ≤ ∑ j ∈ unfilteredIdx, ((strictFiber j).card : ENNReal) := by
    have h1 : lostIdx.card ≤ (Finset.biUnion unfilteredIdx strictFiber).card :=
      Finset.card_le_card h_lost_subset
    have h2 : (Finset.biUnion unfilteredIdx strictFiber).card ≤
        ∑ j ∈ unfilteredIdx, (strictFiber j).card := Finset.card_biUnion_le
    have h3 : (lostIdx.card : ENNReal) ≤ (↑(∑ j ∈ unfilteredIdx, (strictFiber j).card) : ENNReal) :=
      Nat.cast_le.mpr (le_trans h1 h2)
    have h4 : (↑(∑ j ∈ unfilteredIdx, (strictFiber j).card) : ENNReal) =
        ∑ j ∈ unfilteredIdx, ((strictFiber j).card : ENNReal) := by
      rw [Nat.cast_sum]
    rw [h4] at h3
    exact h3

  have h_lost_le_half :
      (lostIdx.card : ENNReal) ≤ (1 : ENNReal) / 2 * source.enncard := by
    calc
      (lostIdx.card : ENNReal)
        ≤ ∑ j ∈ unfilteredIdx, ((strictFiber j).card : ENNReal) := h_lost_le_sum
      _ ≤ threshold * (K : ENNReal) * ∑ p, fiberCount p := h_sum_bound
      _ ≤ threshold * (K : ENNReal) * ((L : ENNReal) * source.enncard) := by gcongr
      _ = (((K * L : ℕ) : ENNReal) * threshold) * source.enncard := by
          have h_KL : (K : ENNReal) * (L : ENNReal) = ((K * L : ℕ) : ENNReal) := by
            exact Eq.symm (Nat.cast_mul K L)
          calc
            threshold * (K : ENNReal) * ((L : ENNReal) * source.enncard)
              = threshold * ((K : ENNReal) * (L : ENNReal)) * source.enncard := by ring
            _ = threshold * (((K * L : ℕ) : ENNReal)) * source.enncard := by rw [h_KL]
            _ = (((K * L : ℕ) : ENNReal) * threshold) * source.enncard := by ring
      _ ≤ ((1 : ENNReal) / 2) * source.enncard := by gcongr

  have h_disj : Disjoint filteredSourceIdx lostIdx := by
    simp [filteredSourceIdx, lostIdx, Finset.disjoint_left]
  have h_union : filteredSourceIdx ∪ lostIdx = Finset.univ :=
    Finset.union_sdiff_of_subset (Finset.subset_univ filteredSourceIdx)
  have h_card_nat :
      filteredSourceIdx.card + lostIdx.card = source.card := by
    have h : filteredSourceIdx.card + lostIdx.card = (Finset.univ : Finset (Fin source.card)).card := by
      rw [← Finset.card_union_of_disjoint h_disj, h_union]
    simpa [Finset.card_univ] using h
  have h_card_sum :
      source.enncard = filteredSource.family.enncard + (lostIdx.card : ENNReal) := by
    have h' : (filteredSourceIdx.card : ENNReal) + (lostIdx.card : ENNReal) = (source.card : ENNReal) := by
      exact_mod_cast h_card_nat
    have h1 : source.enncard = (source.card : ENNReal) := by rfl
    have h2 : filteredSource.family.enncard = (filteredSourceIdx.card : ENNReal) := by
      have h21 : filteredSource.family.card = filteredSourceIdx.card := by
        dsimp only [filteredSource, Kakeya.Streamlined.TubeSubfamily.fromFinset]
      exact congr_arg (fun n : ℕ => (n : ENNReal)) h21
    rw [h1, h2]
    exact h'.symm

  have h_retention : source.enncard ≤ 2 * filteredSource.family.enncard :=
    gwz_retention_half h_card_sum h_lost_le_half (by simp) h_source_ne_top

  have h_filtered_cover :
      WZ2PaperPurePartitioningCover filteredSource.family filteredCoarse.family := by
    refine' {
      covers := fun i => _,
      doubled_fibers_disjoint := fun j1 j2 hne => _
    }
    · let i₀ := filteredSource.embedding i
      have hi₀ : i₀ ∈ filteredSourceIdx := h_embedding_mem i
      have h_exists : ∃ (j₀ : Fin coarse.card), j₀ ∈ filteredCoarseIdx ∧ i₀ ∈ strictFiber j₀ := by
        simpa [filteredSourceIdx, Finset.mem_filter] using hi₀
      rcases h_exists with ⟨j₀, hj₀, hi₀_in⟩
      rcases h_embedding_surjective j₀ hj₀ with ⟨j, h_j_eq⟩
      refine ⟨j, ?_⟩
      rw [mem_wz2PaperOrdinaryFullFiberIndices_iff]
      have h_tube1 : filteredSource.family.tube i = source.tube i₀ := filteredSource.tube_eq i
      have h_tube2 : filteredCoarse.family.tube j = coarse.tube (filteredCoarse.embedding j) := filteredCoarse.tube_eq j
      rw [h_tube1, h_tube2, h_j_eq]
      exact (mem_wz2PaperOrdinaryFullFiberIndices_iff j₀ i₀).mp hi₀_in
    · let j1₀ := filteredCoarse.embedding j1
      let j2₀ := filteredCoarse.embedding j2
      have h_j10_ne_j20 : j1₀ ≠ j2₀ :=
        fun h => hne (filteredCoarse.embedding.injective h)
      have h_original_disjoint := cover.doubled_fibers_disjoint j1₀ j2₀ h_j10_ne_j20
      apply Finset.disjoint_left.mpr
      intro i hi1 hi2
      let i₀ := filteredSource.embedding i
      have h_contain1 : (filteredSource.family.tube i).carrier ⊆ wz2PaperCenteredDilatedCarrier 2 (filteredCoarse.family.tube j1) :=
        (mem_wz2PaperOrdinaryDilatedFiberIndices_iff j1 i).mp hi1
      have h_contain2 : (filteredSource.family.tube i).carrier ⊆ wz2PaperCenteredDilatedCarrier 2 (filteredCoarse.family.tube j2) :=
        (mem_wz2PaperOrdinaryDilatedFiberIndices_iff j2 i).mp hi2
      have h1 : i₀ ∈ wz2PaperOrdinaryDilatedFiberIndices 2 source coarse j1₀ := by
        rw [mem_wz2PaperOrdinaryDilatedFiberIndices_iff]
        have h_tube1 : filteredSource.family.tube i = source.tube i₀ := filteredSource.tube_eq i
        have h_tube2 : filteredCoarse.family.tube j1 = coarse.tube j1₀ := filteredCoarse.tube_eq j1
        rw [h_tube1, h_tube2] at h_contain1
        exact h_contain1
      have h2 : i₀ ∈ wz2PaperOrdinaryDilatedFiberIndices 2 source coarse j2₀ := by
        rw [mem_wz2PaperOrdinaryDilatedFiberIndices_iff]
        have h_tube1 : filteredSource.family.tube i = source.tube i₀ := filteredSource.tube_eq i
        have h_tube2 : filteredCoarse.family.tube j2 = coarse.tube j2₀ := filteredCoarse.tube_eq j2
        rw [h_tube1, h_tube2] at h_contain2
        exact h_contain2
      exact Finset.disjoint_left.mp h_original_disjoint h1 h2

  have h_substantial :
      ∀ (j : Fin filteredCoarse.family.card),
        (wz2PaperOrdinaryFullFiberCount filteredSource.family filteredCoarse.family j : ENNReal) ≥
          threshold * fiberCount (parentOf (filteredCoarse.embedding j)) := by
    intro j
    let j₀ := filteredCoarse.embedding j
    have hj₀ : j₀ ∈ filteredCoarseIdx := h_embedding_mem j
    have h_substantial_j₀ : substantial j₀ := by
      simpa [filteredCoarseIdx, Finset.mem_filter] using hj₀
    have h_threshold : threshold * fiberCount (parentOf j₀) ≤ (strictFiber j₀).card := h_substantial_j₀

    let F_filtered := wz2PaperOrdinaryFullFiberIndices filteredSource.family filteredCoarse.family j

    have h_image : Finset.image filteredSource.embedding F_filtered = strictFiber j₀ := by
      ext k
      simp only [Finset.mem_image, F_filtered, mem_wz2PaperOrdinaryFullFiberIndices_iff]
      constructor
      · rintro ⟨i, hi, rfl⟩
        have h_tube1 : filteredSource.family.tube i = source.tube (filteredSource.embedding i) := filteredSource.tube_eq i
        have h_tube2 : filteredCoarse.family.tube j = coarse.tube j₀ := filteredCoarse.tube_eq j
        rw [h_tube1, h_tube2] at hi
        exact (mem_wz2PaperOrdinaryFullFiberIndices_iff j₀ (filteredSource.embedding i)).mpr hi
      · intro hk
        have hk_in_sourceIdx : k ∈ filteredSourceIdx := by
          apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_univ k, ⟨j₀, hj₀, hk⟩⟩
        rcases h_embedding_surjective k hk_in_sourceIdx with ⟨i, h_i_eq⟩
        have h_contain : (source.tube k).carrier ⊆ (coarse.tube j₀).carrier :=
          (mem_wz2PaperOrdinaryFullFiberIndices_iff j₀ k).mp hk
        have h_tube1 : filteredSource.family.tube i = source.tube k := by
          rw [filteredSource.tube_eq i, h_i_eq]
        have h_tube2 : filteredCoarse.family.tube j = coarse.tube j₀ := filteredCoarse.tube_eq j
        have h_goal : (filteredSource.family.tube i).carrier ⊆ (filteredCoarse.family.tube j).carrier := by
          rw [h_tube1, h_tube2]
          exact h_contain
        exact ⟨i, h_goal, h_i_eq⟩

    have h_card : F_filtered.card = (strictFiber j₀).card := by
      have h_inj : Set.InjOn filteredSource.embedding F_filtered :=
        fun _ _ _ _ h => filteredSource.embedding.injective h
      have h : (Finset.image filteredSource.embedding F_filtered).card = F_filtered.card :=
        Finset.card_image_of_injOn h_inj
      rw [h_image] at h
      exact h.symm

    have h_main : (wz2PaperOrdinaryFullFiberCount filteredSource.family filteredCoarse.family j : ENNReal) =
        ((strictFiber j₀).card : ENNReal) := by
      have h_count_def : wz2PaperOrdinaryFullFiberCount filteredSource.family filteredCoarse.family j =
          (F_filtered.card : ENNReal) := by
        simp [wz2PaperOrdinaryFullFiberCount]
        rfl
      rw [h_count_def]
      exact congr_arg (fun n : ℕ => (n : ENNReal)) h_card
    rw [h_main]
    exact h_threshold

  exact ⟨filteredCoarse, filteredSource, h_filtered_cover, h_substantial, h_retention, trivial⟩

/--
Variant of `gwz_tile_filter_substantiality` with an external fiber count function.

Instead of reading fiber counts from `scaleData`, this accepts `fiberCount`
and a sum bound `hFiberSum`. This allows using original GWZ fiber counts
while the cover operates on a restricted subfamily, enabling uniformity
transfer from the original scale data.

The substantiality threshold is `count(j) ≥ δ^η * fiberCount(parentOf j)`.
-/
theorem gwz_tile_filter_substantiality_external
    {δ : ℝ} (_hδ : 0 < δ)
    {source : STubeFamily δ}
    {rho₀ : ℝ} {coarse : STubeFamily rho₀}
    {N : ℕ} {K L : ℕ}
    (cover : WZ2PaperPurePartitioningCover source coarse)
    (parentOf : Fin coarse.card → Fin N)
    (hTilesPerParent :
      ∀ (p : Fin N),
        (Finset.univ.filter (fun j => parentOf j = p)).card ≤ K)
    (fiberCount : Fin N → ENNReal)
    (hFiberSum :
      ∑ p : Fin N, fiberCount p ≤ (L : ENNReal) * source.enncard)
    (η : ℝ) (_hη : 0 < η)
    (hδ_small :
      ((K * L : ℕ) : ENNReal) * Kakeya.realRpowENN δ η ≤ (1 : ENNReal) / 2)
    :
    ∃ (filteredCoarse : STubeSubfamily coarse)
      (filteredSource : STubeSubfamily source)
      (_ : WZ2PaperPurePartitioningCover filteredSource.family filteredCoarse.family)
      (_ :
        ∀ (j : Fin filteredCoarse.family.card),
          (wz2PaperOrdinaryFullFiberCount filteredSource.family filteredCoarse.family j : ENNReal) ≥
            Kakeya.realRpowENN δ η *
              fiberCount (parentOf (filteredCoarse.embedding j)))
      (_ : source.enncard ≤ 2 * filteredSource.family.enncard),
      True := by
  let threshold : ENNReal := Kakeya.realRpowENN δ η
  let strictFiber (j : Fin coarse.card) : Finset (Fin source.card) :=
    wz2PaperOrdinaryFullFiberIndices source coarse j
  let substantial (j : Fin coarse.card) : Prop :=
    threshold * fiberCount (parentOf j) ≤ (strictFiber j).card
  let filteredCoarseIdx : Finset (Fin coarse.card) :=
    Finset.univ.filter substantial
  let unfilteredIdx : Finset (Fin coarse.card) :=
    Finset.univ \ filteredCoarseIdx
  let filteredCoarse : STubeSubfamily coarse :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset coarse filteredCoarseIdx
  let filteredSourceIdx : Finset (Fin source.card) :=
    Finset.univ.filter fun i => ∃ j ∈ filteredCoarseIdx, i ∈ strictFiber j
  let filteredSource : STubeSubfamily source :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset source filteredSourceIdx
  let lostIdx : Finset (Fin source.card) :=
    Finset.univ \ filteredSourceIdx

  have h_source_ne_top : source.enncard ≠ ⊤ := ENNReal.coe_ne_top

  have h_embedding_mem :
      ∀ {δ : ℝ} {F : STubeFamily δ} {I : Finset (Fin F.card)}
        (i : Fin (Kakeya.Streamlined.TubeSubfamily.fromFinset F I).family.card),
        (Kakeya.Streamlined.TubeSubfamily.fromFinset F I).embedding i ∈ I := by
    intro δ F I i
    dsimp only [Kakeya.Streamlined.TubeSubfamily.fromFinset]
    exact Finset.orderEmbOfFin_mem I rfl i

  have h_embedding_surjective :
      ∀ {δ : ℝ} {F : STubeFamily δ} {I : Finset (Fin F.card)}
        (k : Fin F.card), k ∈ I →
        ∃ i : Fin (Kakeya.Streamlined.TubeSubfamily.fromFinset F I).family.card,
          (Kakeya.Streamlined.TubeSubfamily.fromFinset F I).embedding i = k := by
    intro δ F I k hk
    have h_image : Finset.map (I.orderEmbOfFin rfl).toEmbedding Finset.univ = I :=
      Finset.map_orderEmbOfFin_univ I rfl
    have h_k_in_image : k ∈ Finset.map (I.orderEmbOfFin rfl).toEmbedding Finset.univ := by
      rw [h_image]; exact hk
    rcases Finset.mem_map.mp h_k_in_image with ⟨i, _, rfl⟩
    exact ⟨i, rfl⟩

  have h_unfiltered_bound :
      ∀ j ∈ unfilteredIdx, ((strictFiber j).card : ENNReal) ≤ threshold * fiberCount (parentOf j) := by
    intro j hj
    have h_not : ¬(threshold * fiberCount (parentOf j) ≤ (strictFiber j).card) := by
      simpa [unfilteredIdx, filteredCoarseIdx, substantial, Finset.mem_filter] using hj
    exact Std.le_of_not_ge h_not

  have h1_sum : ∑ j ∈ unfilteredIdx, ((strictFiber j).card : ENNReal) ≤
      ∑ j ∈ unfilteredIdx, threshold * fiberCount (parentOf j) := by
    apply Finset.sum_le_sum
    intro j hj
    exact h_unfiltered_bound j hj

  have h2_sum : ∑ j ∈ unfilteredIdx, threshold * fiberCount (parentOf j) =
      threshold * ∑ j ∈ unfilteredIdx, fiberCount (parentOf j) := by
    rw [Finset.mul_sum]

  let fiberOfParent (p : Fin N) : Finset (Fin coarse.card) :=
    unfilteredIdx.filter (fun j => parentOf j = p)

  have h_group_final : ∑ j ∈ unfilteredIdx, fiberCount (parentOf j) =
      ∑ p : Fin N, ((fiberOfParent p).card : ENNReal) * fiberCount p := by
    have h4 : ∀ (j : Fin coarse.card),
        ∑ p : Fin N, (if parentOf j = p then fiberCount p else 0) =
        fiberCount (parentOf j) := by
      intro j
      let P : Fin N → Prop := fun p => parentOf j = p
      have h_filter : (Finset.univ.filter P) = {parentOf j} := by
        ext p; simp [P]; tauto
      rw [Finset.sum_ite, h_filter]
      simp
    have h5 : ∑ j ∈ unfilteredIdx, fiberCount (parentOf j) =
        ∑ j ∈ unfilteredIdx, ∑ p : Fin N,
          (if parentOf j = p then fiberCount p else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      exact (h4 j).symm
    rw [h5, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.sum_ite]
    simp [fiberOfParent, Finset.sum_const]

  have h_fiber_card_le_K : ∀ p : Fin N,
      (fiberOfParent p).card ≤ K := by
    intro p
    have h6 : (fiberOfParent p).card ≤ (Finset.univ.filter (fun j => parentOf j = p)).card :=
      Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ unfilteredIdx))
    have h7 : (Finset.univ.filter (fun j => parentOf j = p)).card ≤ K := hTilesPerParent p
    exact le_trans h6 h7

  have h6_sum : ∑ p : Fin N, ((fiberOfParent p).card : ENNReal) * fiberCount p ≤
      (K : ENNReal) * ∑ p : Fin N, fiberCount p := by
    calc
      ∑ p, _ ≤ ∑ p, (K : ENNReal) * fiberCount p := by
        apply Finset.sum_le_sum; intro p _; gcongr; exact h_fiber_card_le_K p
      _ = (K : ENNReal) * ∑ p, fiberCount p := by rw [Finset.mul_sum]

  have h_sum_bound : ∑ j ∈ unfilteredIdx, ((strictFiber j).card : ENNReal) ≤
      threshold * (K : ENNReal) * ∑ p : Fin N, fiberCount p := by
    calc
      ∑ j ∈ unfilteredIdx, ((strictFiber j).card : ENNReal)
        ≤ ∑ j ∈ unfilteredIdx, threshold * fiberCount (parentOf j) := h1_sum
      _ = threshold * ∑ j ∈ unfilteredIdx, fiberCount (parentOf j) := h2_sum
      _ = threshold * (∑ p, ((fiberOfParent p).card : ENNReal) * fiberCount p) := by
          rw [h_group_final]
      _ ≤ threshold * ((K : ENNReal) * ∑ p, fiberCount p) := by gcongr
      _ = threshold * (K : ENNReal) * ∑ p, fiberCount p := by ring

  have h_lost_subset : lostIdx ⊆ Finset.biUnion unfilteredIdx strictFiber := by
    intro i hi
    have h_not : i ∉ filteredSourceIdx := by simpa [lostIdx] using hi
    rcases cover.covers i with ⟨j, hj⟩
    have h_in : i ∈ strictFiber j := by
      simpa [strictFiber, wz2PaperOrdinaryFullFiberIndices] using hj
    by_cases hf : j ∈ filteredCoarseIdx
    · exfalso
      have h_goal : i ∈ filteredSourceIdx := by
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ i, ⟨j, hf, h_in⟩⟩
      exact h_not h_goal
    · have h_uf : j ∈ unfilteredIdx := by
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, hf⟩
      exact Finset.mem_biUnion.mpr ⟨j, h_uf, h_in⟩

  have h_lost_le_sum : (lostIdx.card : ENNReal) ≤ ∑ j ∈ unfilteredIdx, ((strictFiber j).card : ENNReal) := by
    have h1 : lostIdx.card ≤ (Finset.biUnion unfilteredIdx strictFiber).card :=
      Finset.card_le_card h_lost_subset
    have h2 : (Finset.biUnion unfilteredIdx strictFiber).card ≤
        ∑ j ∈ unfilteredIdx, (strictFiber j).card := Finset.card_biUnion_le
    have h3 : (lostIdx.card : ENNReal) ≤ (↑(∑ j ∈ unfilteredIdx, (strictFiber j).card) : ENNReal) :=
      Nat.cast_le.mpr (le_trans h1 h2)
    have h4 : (↑(∑ j ∈ unfilteredIdx, (strictFiber j).card) : ENNReal) =
        ∑ j ∈ unfilteredIdx, ((strictFiber j).card : ENNReal) := by
      rw [Nat.cast_sum]
    rw [h4] at h3
    exact h3

  have h_lost_le_half :
      (lostIdx.card : ENNReal) ≤ (1 : ENNReal) / 2 * source.enncard := by
    calc
      (lostIdx.card : ENNReal)
        ≤ ∑ j ∈ unfilteredIdx, ((strictFiber j).card : ENNReal) := h_lost_le_sum
      _ ≤ threshold * (K : ENNReal) * ∑ p : Fin N, fiberCount p := h_sum_bound
      _ ≤ threshold * (K : ENNReal) * ((L : ENNReal) * source.enncard) := by gcongr
      _ = (((K * L : ℕ) : ENNReal) * threshold) * source.enncard := by
          have h_KL : (K : ENNReal) * (L : ENNReal) = ((K * L : ℕ) : ENNReal) := by
            exact Eq.symm (Nat.cast_mul K L)
          calc
            threshold * (K : ENNReal) * ((L : ENNReal) * source.enncard)
              = threshold * ((K : ENNReal) * (L : ENNReal)) * source.enncard := by ring
            _ = threshold * (((K * L : ℕ) : ENNReal)) * source.enncard := by rw [h_KL]
            _ = (((K * L : ℕ) : ENNReal) * threshold) * source.enncard := by ring
      _ ≤ ((1 : ENNReal) / 2) * source.enncard := by gcongr

  have h_disj : Disjoint filteredSourceIdx lostIdx := by
    simp [filteredSourceIdx, lostIdx, Finset.disjoint_left]
  have h_union : filteredSourceIdx ∪ lostIdx = Finset.univ :=
    Finset.union_sdiff_of_subset (Finset.subset_univ filteredSourceIdx)
  have h_card_nat :
      filteredSourceIdx.card + lostIdx.card = source.card := by
    have h : filteredSourceIdx.card + lostIdx.card = (Finset.univ : Finset (Fin source.card)).card := by
      rw [← Finset.card_union_of_disjoint h_disj, h_union]
    simpa [Finset.card_univ] using h
  have h_card_sum :
      source.enncard = filteredSource.family.enncard + (lostIdx.card : ENNReal) := by
    have h' : (filteredSourceIdx.card : ENNReal) + (lostIdx.card : ENNReal) = (source.card : ENNReal) := by
      exact_mod_cast h_card_nat
    have h1 : source.enncard = (source.card : ENNReal) := by rfl
    have h2 : filteredSource.family.enncard = (filteredSourceIdx.card : ENNReal) := by
      have h21 : filteredSource.family.card = filteredSourceIdx.card := by
        dsimp only [filteredSource, Kakeya.Streamlined.TubeSubfamily.fromFinset]
      exact congr_arg (fun n : ℕ => (n : ENNReal)) h21
    rw [h1, h2]
    exact h'.symm

  have h_retention : source.enncard ≤ 2 * filteredSource.family.enncard :=
    gwz_retention_half h_card_sum h_lost_le_half (by simp) h_source_ne_top

  have h_filtered_cover :
      WZ2PaperPurePartitioningCover filteredSource.family filteredCoarse.family := by
    refine' {
      covers := fun i => _,
      doubled_fibers_disjoint := fun j1 j2 hne => _
    }
    · let i₀ := filteredSource.embedding i
      have hi₀ : i₀ ∈ filteredSourceIdx := h_embedding_mem i
      have h_exists : ∃ (j₀ : Fin coarse.card), j₀ ∈ filteredCoarseIdx ∧ i₀ ∈ strictFiber j₀ := by
        simpa [filteredSourceIdx, Finset.mem_filter] using hi₀
      rcases h_exists with ⟨j₀, hj₀, hi₀_in⟩
      rcases h_embedding_surjective j₀ hj₀ with ⟨j, h_j_eq⟩
      refine ⟨j, ?_⟩
      rw [mem_wz2PaperOrdinaryFullFiberIndices_iff]
      have h_tube1 : filteredSource.family.tube i = source.tube i₀ := filteredSource.tube_eq i
      have h_tube2 : filteredCoarse.family.tube j = coarse.tube (filteredCoarse.embedding j) := filteredCoarse.tube_eq j
      rw [h_tube1, h_tube2, h_j_eq]
      exact (mem_wz2PaperOrdinaryFullFiberIndices_iff j₀ i₀).mp hi₀_in
    · let j1₀ := filteredCoarse.embedding j1
      let j2₀ := filteredCoarse.embedding j2
      have h_j10_ne_j20 : j1₀ ≠ j2₀ :=
        fun h => hne (filteredCoarse.embedding.injective h)
      have h_original_disjoint := cover.doubled_fibers_disjoint j1₀ j2₀ h_j10_ne_j20
      apply Finset.disjoint_left.mpr
      intro i hi1 hi2
      let i₀ := filteredSource.embedding i
      have h_contain1 : (filteredSource.family.tube i).carrier ⊆ wz2PaperCenteredDilatedCarrier 2 (filteredCoarse.family.tube j1) :=
        (mem_wz2PaperOrdinaryDilatedFiberIndices_iff j1 i).mp hi1
      have h_contain2 : (filteredSource.family.tube i).carrier ⊆ wz2PaperCenteredDilatedCarrier 2 (filteredCoarse.family.tube j2) :=
        (mem_wz2PaperOrdinaryDilatedFiberIndices_iff j2 i).mp hi2
      have h1 : i₀ ∈ wz2PaperOrdinaryDilatedFiberIndices 2 source coarse j1₀ := by
        rw [mem_wz2PaperOrdinaryDilatedFiberIndices_iff]
        have h_tube1 : filteredSource.family.tube i = source.tube i₀ := filteredSource.tube_eq i
        have h_tube2 : filteredCoarse.family.tube j1 = coarse.tube j1₀ := filteredCoarse.tube_eq j1
        rw [h_tube1, h_tube2] at h_contain1
        exact h_contain1
      have h2 : i₀ ∈ wz2PaperOrdinaryDilatedFiberIndices 2 source coarse j2₀ := by
        rw [mem_wz2PaperOrdinaryDilatedFiberIndices_iff]
        have h_tube1 : filteredSource.family.tube i = source.tube i₀ := filteredSource.tube_eq i
        have h_tube2 : filteredCoarse.family.tube j2 = coarse.tube j2₀ := filteredCoarse.tube_eq j2
        rw [h_tube1, h_tube2] at h_contain2
        exact h_contain2
      exact Finset.disjoint_left.mp h_original_disjoint h1 h2

  have h_substantial :
      ∀ (j : Fin filteredCoarse.family.card),
        (wz2PaperOrdinaryFullFiberCount filteredSource.family filteredCoarse.family j : ENNReal) ≥
          threshold * fiberCount (parentOf (filteredCoarse.embedding j)) := by
    intro j
    let j₀ := filteredCoarse.embedding j
    have hj₀ : j₀ ∈ filteredCoarseIdx := h_embedding_mem j
    have h_substantial_j₀ : substantial j₀ := by
      simpa [filteredCoarseIdx, Finset.mem_filter] using hj₀
    have h_threshold : threshold * fiberCount (parentOf j₀) ≤ (strictFiber j₀).card := h_substantial_j₀

    let F_filtered := wz2PaperOrdinaryFullFiberIndices filteredSource.family filteredCoarse.family j

    have h_image : Finset.image filteredSource.embedding F_filtered = strictFiber j₀ := by
      ext k
      simp only [Finset.mem_image, F_filtered, mem_wz2PaperOrdinaryFullFiberIndices_iff]
      constructor
      · rintro ⟨i, hi, rfl⟩
        have h_tube1 : filteredSource.family.tube i = source.tube (filteredSource.embedding i) := filteredSource.tube_eq i
        have h_tube2 : filteredCoarse.family.tube j = coarse.tube j₀ := filteredCoarse.tube_eq j
        rw [h_tube1, h_tube2] at hi
        exact (mem_wz2PaperOrdinaryFullFiberIndices_iff j₀ (filteredSource.embedding i)).mpr hi
      · intro hk
        have hk_in_sourceIdx : k ∈ filteredSourceIdx := by
          apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_univ k, ⟨j₀, hj₀, hk⟩⟩
        rcases h_embedding_surjective k hk_in_sourceIdx with ⟨i, h_i_eq⟩
        have h_contain : (source.tube k).carrier ⊆ (coarse.tube j₀).carrier :=
          (mem_wz2PaperOrdinaryFullFiberIndices_iff j₀ k).mp hk
        have h_tube1 : filteredSource.family.tube i = source.tube k := by
          rw [filteredSource.tube_eq i, h_i_eq]
        have h_tube2 : filteredCoarse.family.tube j = coarse.tube j₀ := filteredCoarse.tube_eq j
        have h_goal : (filteredSource.family.tube i).carrier ⊆ (filteredCoarse.family.tube j).carrier := by
          rw [h_tube1, h_tube2]
          exact h_contain
        exact ⟨i, h_goal, h_i_eq⟩

    have h_card : F_filtered.card = (strictFiber j₀).card := by
      have h_inj : Set.InjOn filteredSource.embedding F_filtered :=
        fun _ _ _ _ h => filteredSource.embedding.injective h
      have h : (Finset.image filteredSource.embedding F_filtered).card = F_filtered.card :=
        Finset.card_image_of_injOn h_inj
      rw [h_image] at h
      exact h.symm

    have h_main : (wz2PaperOrdinaryFullFiberCount filteredSource.family filteredCoarse.family j : ENNReal) =
        ((strictFiber j₀).card : ENNReal) := by
      have h_count_def : wz2PaperOrdinaryFullFiberCount filteredSource.family filteredCoarse.family j =
          (F_filtered.card : ENNReal) := by
        simp [wz2PaperOrdinaryFullFiberCount]
        <;> rfl
      rw [h_count_def]
      exact congr_arg (fun n : ℕ => (n : ENNReal)) h_card
    rw [h_main]
    exact h_threshold

  exact ⟨filteredCoarse, filteredSource, h_filtered_cover, h_substantial, h_retention, trivial⟩

end Kakeya.Assouad

end
