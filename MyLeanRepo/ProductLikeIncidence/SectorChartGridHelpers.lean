module

/-
# Sector Chart Grid Helpers

Small lemmas that combine production `FourSectorChart` with grid-aligned
covering number facts. These bridge the gap between:
- `FourSectorChart.chartSectorCoordPoint` (correct sector transform)
- `ProductLikeSetBasics.grid_set_coveringNumber_eq_encard` (grid covering = encard)
- `FourSectorChart.four_sector_projection_preservation` (factor-2 projection bound)

## CRITICAL Convention Note — B-set swap

Phase8 coordinates: point p has p0 ∈ B1 (first coord = U), p1 ∈ B2 (second = V).
Production chart internally passes U=p1, V=p0 to `chartSectorCoord`.
This means the chart's U is Phase8's B2, and chart's V is Phase8's B1 — **SWAPPED**.

Output B-sets of `chartSectorCoordPoint i p` (where p0 ∈ B1, p1 ∈ B2):
- Sector 0: (p0, p1)      → B1_out = B1,      B2_out = B2
- Sector 1: (p1, p0)      → B1_out = B2,      B2_out = B1
- Sector 2: (-p0, p1)     → B1_out = -B1,     B2_out = B2
- Sector 3: (-p1, p0)     → B1_out = -B2,     B2_out = B1

Projection identity:
  affineProjection (chartSectorT i x) (chartSectorCoordPoint i '' G)
  = scaleSet (chartSectorScalar i x) (affineProjection x G)

This is WHY the production chart preserves the affineProjection bound:
it maps affineProjection to (scalar * affineProjection), NOT to rawProjection.

Do NOT confuse with Phase8's inline sec_map (swap for sector 0), which maps
affineProjection to rawProjection and loses the smallness bound.

## Whiteprint node
Helper for `DirectionFailureComposition`
-/

public import MyLeanRepo.ProductLikeIncidence.FourSectorChart
public import MyLeanRepo.ProductLikeSetBasics
public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open Set ENNReal Bornology Classical

namespace ProductLikeIncidence.ProductReduction

/-- Each sector coordinate point map is injective (signed permutation). -/
lemma chartSectorCoordPoint_injective (i : Fin 4) :
    Function.Injective (FourSectorChart.chartSectorCoordPoint i) := by
  intro p q h
  have h0 : (FourSectorChart.chartSectorCoordPoint i p) 0 =
           (FourSectorChart.chartSectorCoordPoint i q) 0 := by rw [h]
  have h1 : (FourSectorChart.chartSectorCoordPoint i p) 1 =
           (FourSectorChart.chartSectorCoordPoint i q) 1 := by rw [h]
  have h_eq0 : p 0 = q 0 := by
    fin_cases i <;> simp [FourSectorChart.chartSectorCoordPoint,
      FourSectorChart.chartSectorCoord] at h0 h1 <;> linarith
  have h_eq1 : p 1 = q 1 := by
    fin_cases i <;> simp [FourSectorChart.chartSectorCoordPoint,
      FourSectorChart.chartSectorCoord] at h0 h1 <;> linarith
  ext j
  fin_cases j <;> tauto

/-- Grid-aligned 2D covering number is preserved exactly by sector transforms.

For any set `S` on the δ-grid, `chartSectorCoordPoint i` maps grid points to
grid points, so both covering numbers equal the respective encards, and
injectivity gives encard equality. -/
lemma chartSector_grid_covering_preservation {δ : ℝ} (hδ : 0 < δ)
    {i : Fin 4} {S : Set (EuclideanSpace ℝ (Fin 2))}
    (hS_grid : ∀ p ∈ S, ∀ j : Fin 2, ∃ k : ℤ, p j = δ * (k : ℝ)) :
    dyadicCoveringNumber δ (FourSectorChart.chartSectorCoordPoint i '' S) =
    dyadicCoveringNumber δ S := by
  have h_inj := chartSectorCoordPoint_injective i
  have hS_grid' : ∀ p ∈ S, (∃ k : ℤ, p 0 = δ * (k : ℝ)) ∧ (∃ k : ℤ, p 1 = δ * (k : ℝ)) := by
    intro p hp
    exact ⟨hS_grid p hp 0, hS_grid p hp 1⟩
  have h_image_grid : ∀ p ∈ (FourSectorChart.chartSectorCoordPoint i '' S),
      ∀ j : Fin 2, ∃ k : ℤ, p j = δ * (k : ℝ) := by
    intro p hp j
    rcases hp with ⟨q, hq, rfl⟩
    have hq0 : ∃ k : ℤ, q 0 = δ * (k : ℝ) := (hS_grid' q hq).1
    have hq1 : ∃ k : ℤ, q 1 = δ * (k : ℝ) := (hS_grid' q hq).2
    fin_cases i <;> fin_cases j
    · -- sector 0, coord 0: q 0
      simpa [FourSectorChart.chartSectorCoordPoint, FourSectorChart.chartSectorCoord] using hq0
    · -- sector 0, coord 1: q 1
      simpa [FourSectorChart.chartSectorCoordPoint, FourSectorChart.chartSectorCoord] using hq1
    · -- sector 1, coord 0: q 1
      simpa [FourSectorChart.chartSectorCoordPoint, FourSectorChart.chartSectorCoord] using hq1
    · -- sector 1, coord 1: q 0
      simpa [FourSectorChart.chartSectorCoordPoint, FourSectorChart.chartSectorCoord] using hq0
    · -- sector 2, coord 0: -q 0
      rcases hq0 with ⟨k, hk⟩
      have h_goal : -(q 0) = δ * ((-k : ℤ) : ℝ) := by
        have h : -(δ * (k : ℝ)) = δ * ((-k : ℤ) : ℝ) := by
          simp [Int.cast_neg]
        rw [hk]
        exact h
      simpa [FourSectorChart.chartSectorCoordPoint, FourSectorChart.chartSectorCoord] using ⟨-k, h_goal⟩
    · -- sector 2, coord 1: q 1
      simpa [FourSectorChart.chartSectorCoordPoint, FourSectorChart.chartSectorCoord] using hq1
    · -- sector 3, coord 0: -q 1
      rcases hq1 with ⟨k, hk⟩
      have h_goal : -(q 1) = δ * ((-k : ℤ) : ℝ) := by
        have h : -(δ * (k : ℝ)) = δ * ((-k : ℤ) : ℝ) := by
          simp [Int.cast_neg]
        rw [hk]
        exact h
      simpa [FourSectorChart.chartSectorCoordPoint, FourSectorChart.chartSectorCoord] using ⟨-k, h_goal⟩
    · -- sector 3, coord 1: q 0
      simpa [FourSectorChart.chartSectorCoordPoint, FourSectorChart.chartSectorCoord] using hq0
  have h1 : dyadicCoveringNumber δ (FourSectorChart.chartSectorCoordPoint i '' S) =
      (FourSectorChart.chartSectorCoordPoint i '' S).encard :=
    grid_set_coveringNumber_eq_encard hδ h_image_grid
  have h2 : dyadicCoveringNumber δ S = S.encard :=
    grid_set_coveringNumber_eq_encard hδ hS_grid
  have h3 : (FourSectorChart.chartSectorCoordPoint i '' S).encard = S.encard :=
    h_inj.encard_image S
  rw [h1, h2, h3]

/-- Sector direction `chartSectorT i x` is in [0,1] when `chartSectorPred i x`. -/
lemma chartSectorT_in_unit (i : Fin 4) (x : ℝ)
    (h : FourSectorChart.chartSectorPred i x) :
    FourSectorChart.chartSectorT i x ∈ Set.Icc (0 : ℝ) 1 := by
  fin_cases i
  · -- sector 0: x ∈ [0,1]
    simp only [FourSectorChart.chartSectorT, FourSectorChart.chartSectorPred] at h ⊢
    exact ⟨h.1, h.2⟩
  · -- sector 1: x > 1, so 0 < 1/x ≤ 1
    simp only [FourSectorChart.chartSectorPred] at h
    have hx_pos : 0 < x := by linarith
    have h1 : 0 < 1 / x := by positivity
    have h2 : 1 / x ≤ 1 := by
      have h3 : 1 ≤ x := by linarith
      have h4 : 1 / x ≤ 1 / 1 := by gcongr
      simpa using h4
    simp only [FourSectorChart.chartSectorT]
    exact ⟨by linarith, h2⟩
  · -- sector 2: x ∈ [-1,0), so -x ∈ (0,1]
    simp only [FourSectorChart.chartSectorT, FourSectorChart.chartSectorPred] at h ⊢
    have h1 : 0 ≤ -x := by linarith
    have h2 : -x ≤ 1 := by linarith
    exact ⟨h1, h2⟩
  · -- sector 3: x < -1, so 0 < -1/x ≤ 1
    simp only [FourSectorChart.chartSectorPred] at h
    have hx_neg : x < 0 := by linarith
    have h1 : 0 < -1 / x := by
      have h2 : 0 < -x := by linarith
      have h3 : -1 / x = 1 / (-x) := by
        field_simp [hx_neg.ne]
      rw [h3]
      positivity
    have h2 : -1 / x ≤ 1 := by
      have h3 : -1 / x = 1 / (-x) := by
        field_simp [hx_neg.ne]
      rw [h3]
      have h4 : 1 ≤ -x := by linarith
      have h5 : 1 / (-x) ≤ 1 / 1 := by gcongr
      simpa using h5
    simp only [FourSectorChart.chartSectorT]
    exact ⟨by linarith, h2⟩

/-! ### B-set swap convention

**CRITICAL CONVENTION NOTE**:

Production `FourSectorChart.chartSectorCoordPoint i p` internally passes
`U = p 1` (second coordinate) and `V = p 0` (first coordinate) to
`chartSectorCoord i U V`.

This means for a point `p ∈ B1 × B2` (where `p 0 ∈ B1`, `p 1 ∈ B2`):
- The chart's `U` comes from `B2`
- The chart's `V` comes from `B1`

Therefore the output coordinate sets are:

| Sector | First coord (ring) | Second coord (coord) | Scalar |
|--------|-------------------|----------------------|--------|
| 0      | B1                | B2                   | 1      |
| 1      | B2                | B1                   | 1/x    |
| 2      | -B1               | B2                   | 1      |
| 3      | -B2               | B1                   | 1/x    |

This differs from the Phase8 table (which uses rawProjection U+xV with U=p0, V=p1).
When using FourSectorChart, always use `chartRingSet`/`chartCoordSet` below,
NOT `Phase8SectorTranslation.sectorRingBaseSet`/`sectorCoordSet`.
-/

/-- First-coordinate (ring) set after FourSectorChart transform. -/
def chartRingSet (i : Fin 4) (B1 B2 : Set ℝ) : Set ℝ :=
  match i with
  | 0 => B1
  | 1 => B2
  | 2 => Set.image (fun x => -x) B1
  | 3 => Set.image (fun x => -x) B2

/-- Second-coordinate (coord) set after FourSectorChart transform. -/
def chartCoordSet (i : Fin 4) (B1 B2 : Set ℝ) : Set ℝ :=
  match i with
  | 0 => B2
  | 1 => B1
  | 2 => B2
  | 3 => B1

/-- **phase8_to_chart_sector**: Given a point in B1×B2, the FourSectorChart
    transformed point lands in `chartRingSet i B1 B2 × chartCoordSet i B1 B2`.

This lemma documents and verifies the B-set swap. -/
lemma phase8_to_chart_sector (i : Fin 4) {B1 B2 : Set ℝ}
    {p : EuclideanSpace ℝ (Fin 2)} (hp0 : p 0 ∈ B1) (hp1 : p 1 ∈ B2) :
    (FourSectorChart.chartSectorCoordPoint i p) 0 ∈ chartRingSet i B1 B2 ∧
    (FourSectorChart.chartSectorCoordPoint i p) 1 ∈ chartCoordSet i B1 B2 := by
  fin_cases i <;> simp [chartRingSet, chartCoordSet,
    FourSectorChart.chartSectorCoordPoint, FourSectorChart.chartSectorCoord,
    hp0, hp1] <;> tauto

/-- Projection scalar bound: |chartSectorScalar i x| ≤ 1.
    Re-export of production `chart_sector_scalar_bound`. -/
lemma chartSectorScalar_bound' (i : Fin 4) (x : ℝ)
    (h : FourSectorChart.chartSectorPred i x) :
    |FourSectorChart.chartSectorScalar i x| ≤ 1 :=
  FourSectorChart.chart_sector_scalar_bound i x h

/-- **Sector projection bound transformation**.

Given `G ⊆ B1 × B2` and `x` in sector `i`, let `G' = chartSectorCoordPoint i '' G`
and `t = chartSectorT i x`. Then:

- Sectors 0,2 (scalar = 1): `N(π_t(G')) = N(π_x(G))`
- Sectors 1,3 (|scalar| ≤ 1): `N(π_t(G')) ≤ 2 * N(π_x(G))`

Thus if the input projection bound is:
- `< (1/2) * base * N(chartCoordSet i B1 B2)` for sectors 0,2
- `< (1/4) * base * N(chartCoordSet i B1 B2)` for sectors 1,3

then the output bound is `< (1/2) * base * N(chartCoordSet i B1 B2)`.

Note: `chartCoordSet i B1 B2` is B2 for sectors 0,2 and B1 for sectors 1,3.
The input bound MUST use the correct coord set for the sector. -/
lemma sector_projection_bound_transform
    {δ : ℝ} (hδ_pos : 0 < δ)
    (i : Fin 4) {x : ℝ} (hx : FourSectorChart.chartSectorPred i x)
    {G : Set (EuclideanSpace ℝ (Fin 2))}
    (hG_bdd : IsBounded G)
    {base : ENNReal}
    (h_input : ENat.toENNReal (dyadicCoveringNumber δ (projectionSet1D x G)) <
      (match i with
       | 0 => (1 / 2 : ENNReal)
       | 1 => (1 / 4 : ENNReal)
       | 2 => (1 / 2 : ENNReal)
       | 3 => (1 / 4 : ENNReal)) * base) :
    ENat.toENNReal (dyadicCoveringNumber δ
      (projectionSet1D (FourSectorChart.chartSectorT i x)
        (FourSectorChart.chartSectorCoordPoint i '' G))) <
      (1 / 2 : ENNReal) * base := by
  have h_conv : ENat.toENNReal (dyadicCoveringNumber δ (projectionSet1D x G)) =
      Nreal δ (affineProjection x G) := by rfl
  have h_conv' : ENat.toENNReal (dyadicCoveringNumber δ (projectionSet1D (FourSectorChart.chartSectorT i x)
        (FourSectorChart.chartSectorCoordPoint i '' G))) =
      Nreal δ (affineProjection (FourSectorChart.chartSectorT i x)
        (FourSectorChart.chartSectorCoordPoint i '' G)) := by rfl
  rw [h_conv']
  have h_factor2 : (2 : ENNReal) * (1 / 4 : ENNReal) = (1 / 2 : ENNReal) := by
    have h4 : (2 : ℝ) * (1 / 4 : ℝ) = (1 / 2 : ℝ) := by norm_num
    have h5 : ENNReal.ofReal ((2 : ℝ) * (1 / 4 : ℝ)) = ENNReal.ofReal (1 / 2 : ℝ) := by rw [h4]
    have h6 : ENNReal.ofReal ((2 : ℝ) * (1 / 4 : ℝ)) =
        ENNReal.ofReal (2 : ℝ) * ENNReal.ofReal (1 / 4 : ℝ) :=
      ENNReal.ofReal_mul (by positivity)
    have h7 : ENNReal.ofReal (2 : ℝ) * ENNReal.ofReal (1 / 4 : ℝ) = ENNReal.ofReal (1 / 2 : ℝ) := by
      rw [←h6, h5]
    simpa using h7
  have h_arith : (2 : ENNReal) * ((1 / 4 : ENNReal) * base) = (1 / 2 : ENNReal) * base := by
    rw [← mul_assoc, h_factor2]
  have h2_pos : (2 : ENNReal) ≠ 0 := by norm_num
  have h2_ne_top : (2 : ENNReal) ≠ ⊤ := by norm_num
  have h_cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by fin_cases i <;> tauto
  rcases h_cases with (rfl | rfl | rfl | rfl)
  · -- Sector 0
    have h_proj_eq : affineProjection (FourSectorChart.chartSectorT 0 x)
          (FourSectorChart.chartSectorCoordPoint 0 '' G) = affineProjection x G := by
      have h_s : FourSectorChart.chartSectorScalar 0 x = 1 := by
        simp [FourSectorChart.chartSectorScalar] <;> norm_num
      rw [FourSectorChart.chart_sector_projection_set 0 x hx G, h_s]
      ext z; simp [scaleSet]
    have h_in : Nreal δ (affineProjection x G) < (1 / 2 : ENNReal) * base := by
      rw [←h_conv]; simpa using h_input
    rw [h_proj_eq]
    exact h_in
  · -- Sector 1
    have h_in : Nreal δ (affineProjection x G) < (1 / 4 : ENNReal) * base := by
      rw [←h_conv]; simpa using h_input
    have h_bound : Nreal δ (affineProjection (FourSectorChart.chartSectorT 1 x)
          (FourSectorChart.chartSectorCoordPoint 1 '' G)) ≤
        (2 : ENNReal) * Nreal δ (affineProjection x G) :=
      FourSectorChart.four_sector_projection_preservation hδ_pos hx hG_bdd
    have h_lt1 : Nreal δ (affineProjection x G) * (2 : ENNReal) <
        ((1 / 4 : ENNReal) * base) * (2 : ENNReal) :=
      (ENNReal.mul_lt_mul_iff_left h2_pos h2_ne_top).mpr h_in
    have h_lt : (2 : ENNReal) * Nreal δ (affineProjection x G) <
        (2 : ENNReal) * ((1 / 4 : ENNReal) * base) := by
      simpa [mul_comm] using h_lt1
    calc Nreal δ (affineProjection (FourSectorChart.chartSectorT 1 x)
          (FourSectorChart.chartSectorCoordPoint 1 '' G))
      ≤ (2 : ENNReal) * Nreal δ (affineProjection x G) := h_bound
    _ < (2 : ENNReal) * ((1 / 4 : ENNReal) * base) := h_lt
    _ = (1 / 2 : ENNReal) * base := h_arith
  · -- Sector 2
    have h_proj_eq : affineProjection (FourSectorChart.chartSectorT 2 x)
          (FourSectorChart.chartSectorCoordPoint 2 '' G) = affineProjection x G := by
      have h_s : FourSectorChart.chartSectorScalar 2 x = 1 := by
        simp [FourSectorChart.chartSectorScalar] <;> norm_num
      rw [FourSectorChart.chart_sector_projection_set 2 x hx G, h_s]
      ext z; simp [scaleSet]
    have h_in : Nreal δ (affineProjection x G) < (1 / 2 : ENNReal) * base := by
      rw [←h_conv]; simpa using h_input
    rw [h_proj_eq]
    exact h_in
  · -- Sector 3
    have h_in : Nreal δ (affineProjection x G) < (1 / 4 : ENNReal) * base := by
      rw [←h_conv]; simpa using h_input
    have h_bound : Nreal δ (affineProjection (FourSectorChart.chartSectorT 3 x)
          (FourSectorChart.chartSectorCoordPoint 3 '' G)) ≤
        (2 : ENNReal) * Nreal δ (affineProjection x G) :=
      FourSectorChart.four_sector_projection_preservation hδ_pos hx hG_bdd
    have h_lt1 : Nreal δ (affineProjection x G) * (2 : ENNReal) <
        ((1 / 4 : ENNReal) * base) * (2 : ENNReal) :=
      (ENNReal.mul_lt_mul_iff_left h2_pos h2_ne_top).mpr h_in
    have h_lt : (2 : ENNReal) * Nreal δ (affineProjection x G) <
        (2 : ENNReal) * ((1 / 4 : ENNReal) * base) := by
      simpa [mul_comm] using h_lt1
    calc Nreal δ (affineProjection (FourSectorChart.chartSectorT 3 x)
          (FourSectorChart.chartSectorCoordPoint 3 '' G))
      ≤ (2 : ENNReal) * Nreal δ (affineProjection x G) := h_bound
    _ < (2 : ENNReal) * ((1 / 4 : ENNReal) * base) := h_lt
    _ = (1 / 2 : ENNReal) * base := h_arith

end ProductLikeIncidence.ProductReduction
