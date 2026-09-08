/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.ThinCentredMult

/-!
# The cell/collar volume comparison

Conjunct (i) of `Kakeya.ThinCase.factoringApply` and conjunct (iv) compete for the same net
cells, and this file is the estimate that reconciles them.

## The competition

At cell scale `r = w₁ / 8` the Córdoba fattening radius of GWZ Item 2 is
`2 τ₂(Wb j) ∈ [w₁, 4 w₁] = [8 r, 32 r]`, so the induced shade of a block reaches **32 cells**
beyond that block's inner union. Conjunct (iv) — through
`Kakeya.ThinCase.exists_comparableNet` and `Kakeya.ThinCase.centredMult_of_separatedNet` — keeps a
dyadic band of the *inner* ball masses and discards the light cells, and a discarded cell can
carry a full ball's worth of the *outer* volume that conjunct (i) needs. None of the `Ccore`
binders of `factoringApply` bounds the discarded outer volume by the retained inner mass.

## The reconciliation

`Kakeya.ThinCase.sum_volume_cthickening_le_mul_sum_volume_cellShade` shows that the outer *cell*
shading — the one conjunct (iv) forces, built from whole cells by
`Kakeya.ThinCase.exists_cellOuterShading` — is, in total volume, not smaller than the `2 r`-collar
of the retained blocks, up to the dimensional constant
`Kakeya.ThinCase.cellCollarConstant n = 2 · 20 ^ n`. Three steps:

* `Kakeya.ThinCase.two_pow_mul_volume_region_le_sum_volume_cellShade` — the outer shades are
  unions of whole cells and the cells are disjoint, so their total volume is the **block count**
  integrated against the cells, hence at least `2 ^ m` times the volume of the retained region;
* `Kakeya.ThinCase.card_mul_volume_closedBall_le` — packing: an `r`-separated net's balls have
  total volume at most `5 ^ n` times the volume of their union;
* `Kakeya.ThinCase.sum_volume_cthickening_le` — covering: the `2 r`-collar of a block's retained
  part sits inside the `4 r`-balls of the cells that block meets, so the total collar volume is
  the block count integrated against one ball volume.

The **dyadic band of the block count** along the retained cells — which
`Kakeya.ThinCase.exists_cellOuterShading` produces for conjunct (iii)(a), and which is a function
of the *cell* rather than of the point — is what lets the same `2 ^ m` cancel between the first
step and the third. That is the second time that band pays for itself.

Finally `Kakeya.ThinCase.volume_inducedShading_le_mul_volume_cthickening` lifts the `2 r`-collar
to the `2 τ₂`-collar in which `ShadedBody.lambdaForInducedShading_of_measurable` — and hence
`Kakeya.ThinCase.fullness_ge_three_eta` — states its lower bound, at the purely dimensional cost
of `Kakeya.ThinCase.volume_cthickening_le_mul_volume_cthickening`.

## What is still missing for the assembly

The loss of the finer ball-net pigeonhole, `Kakeya.ThinCase.ballNetLoss`, is bounded by none of
the seven `Ccore` binders of `Kakeya.ThinCase.factoringApply`; conjunct (vi) needs an eighth,
`ballNetLoss 3 (w₁ / 8) 2 ≤ Ccore`. It is a *binder*, not a structure field.
-/

@[expose] public section

open MeasureTheory Metric Set ShadedBody
open scoped ENNReal NNReal

namespace Kakeya.ThinCase

section CellVolume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The volume of a closed ball does not depend on its centre. -/
lemma volume_closedBall_center_eq (c : E) {r : ℝ} (hr : 0 ≤ r) :
    volume (Metric.closedBall c r) = volume (Metric.closedBall (0 : E) r) := by
  rw [MeasureTheory.Measure.addHaar_closedBall' volume c hr,
    MeasureTheory.Measure.addHaar_closedBall' volume (0 : E) hr]

/-- **Packing.** An `r`-separated finset has total ball volume at most a dimensional multiple of
the volume of the union of its balls. -/
lemma card_mul_volume_closedBall_le {r : NNReal} (hr : 0 < r) {T : Finset E}
    (hsep : Metric.IsSeparated (r : ENNReal) (T : Set E)) :
    (T.card : ENNReal) * volume (Metric.closedBall (0 : E) (r : ℝ))
      ≤ ((5 ^ Module.finrank ℝ E : ℕ) : ENNReal) *
        volume (⋃ c ∈ T, Metric.closedBall c (r : ℝ)) := by
  classical
  set n := Module.finrank ℝ E with hn
  set F : Set E := ⋃ c ∈ T, Metric.closedBall c (r : ℝ) with hF
  have hFmeas : MeasurableSet F :=
    Finset.measurableSet_biUnion _ fun c _ => measurableSet_closedBall
  have hoverlap : ∀ x : E, {c ∈ T | x ∈ Metric.ball c (2 * (r : ℝ))}.card ≤ 5 ^ n := by
    intro x
    refine Metric.IsSeparated.card_le_pow_of_dist_le (x := x) hr (hsep.subset ?_) ?_
    · exact_mod_cast Finset.filter_subset _ _
    · intro c hc
      have hb := (Finset.mem_filter.mp hc).2
      rw [Metric.mem_ball, dist_comm] at hb
      exact hb.le
  have hstep : ∀ c ∈ T, volume (Metric.closedBall (0 : E) (r : ℝ))
      ≤ volume (F ∩ Metric.ball c (2 * (r : ℝ))) := by
    intro c hc
    rw [← volume_closedBall_center_eq c r.coe_nonneg]
    refine measure_mono fun w hw => ⟨Set.mem_biUnion hc hw, ?_⟩
    exact Metric.closedBall_subset_ball (by
      have : (0:ℝ) < (r:ℝ) := hr
      linarith) hw
  calc (T.card : ENNReal) * volume (Metric.closedBall (0 : E) (r : ℝ))
      = ∑ _c ∈ T, volume (Metric.closedBall (0 : E) (r : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ c ∈ T, volume (F ∩ Metric.ball c (2 * (r : ℝ))) := Finset.sum_le_sum hstep
    _ ≤ ((5 ^ n : ℕ) : ENNReal) * volume F :=
        Kakeya.sum_volume_inter_ball_le T (fun c => c) (fun _ => 2 * (r : ℝ)) hoverlap hFmeas


open Classical in
/-- **The double-counting swap**: summing a cell weight over the cells that meet each block is the
same as summing, over the cells, the block count times the weight. -/
lemma sum_bodies_sum_cells {ω : Type*} (bodies' : Finset ω) (A : ω → Set E) (T'' : Finset E)
    (r : ℝ) (g : E → ENNReal) :
    ∑ j ∈ bodies', ∑ c ∈ {c ∈ T'' | (A j ∩ Metric.closedBall c r).Nonempty}, g c
      = ∑ c ∈ T'', (cellBlockCount bodies' A r c : ENNReal) * g c := by
  classical
  calc ∑ j ∈ bodies', ∑ c ∈ {c ∈ T'' | (A j ∩ Metric.closedBall c r).Nonempty}, g c
      = ∑ j ∈ bodies', ∑ c ∈ T'',
          (if (A j ∩ Metric.closedBall c r).Nonempty then g c else 0) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_filter]
    _ = ∑ c ∈ T'', ∑ j ∈ bodies',
          (if (A j ∩ Metric.closedBall c r).Nonempty then g c else 0) := Finset.sum_comm
    _ = ∑ c ∈ T'', (cellBlockCount bodies' A r c : ENNReal) * g c := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, cellBlockCount]

open Classical in
/-- **Step 1 of the cell/collar comparison.** The outer cell shades are unions of whole cells, so
their total volume is the block count integrated against the cells, hence at least `2 ^ m` times
the volume of the retained region. -/
lemma two_pow_mul_volume_region_le_sum_volume_cellShade
    {ω : Type*} (bodies' : Finset ω) (A : ω → Set E) (T'' : Finset E) (P : E → Set E)
    (m : ℕ) (Sh : ω → Set E) (r : ℝ)
    (hPmeas : ∀ c ∈ T'', MeasurableSet (P c))
    (hPdisj : (T'' : Set E).PairwiseDisjoint P)
    (hband : ∀ c ∈ T'', 2 ^ m ≤ cellBlockCount bodies' A r c)
    (hSh : ∀ j, Sh j = ⋃ c ∈ {c ∈ T'' | (A j ∩ Metric.closedBall c r).Nonempty}, P c) :
    ((2 ^ m : ℕ) : ENNReal) * volume (⋃ c ∈ T'', P c) ≤ ∑ j ∈ bodies', volume (Sh j) := by
  classical
  have hShvol : ∀ j, volume (Sh j)
      = ∑ c ∈ {c ∈ T'' | (A j ∩ Metric.closedBall c r).Nonempty}, volume (P c) := by
    intro j
    rw [hSh j]
    refine measure_biUnion_finset ?_ ?_
    · exact hPdisj.subset (by exact_mod_cast Finset.filter_subset _ _)
    · exact fun c hc => hPmeas c (Finset.mem_filter.mp hc).1
  have hregion : volume (⋃ c ∈ T'', P c) = ∑ c ∈ T'', volume (P c) :=
    measure_biUnion_finset hPdisj hPmeas
  calc ((2 ^ m : ℕ) : ENNReal) * volume (⋃ c ∈ T'', P c)
      = ∑ c ∈ T'', ((2 ^ m : ℕ) : ENNReal) * volume (P c) := by
        rw [hregion, Finset.mul_sum]
    _ ≤ ∑ c ∈ T'', (cellBlockCount bodies' A r c : ENNReal) * volume (P c) := by
        refine Finset.sum_le_sum fun c hc => ?_
        exact mul_le_mul' (by exact_mod_cast hband c hc) le_rfl
    _ = ∑ j ∈ bodies', ∑ c ∈ {c ∈ T'' | (A j ∩ Metric.closedBall c r).Nonempty}, volume (P c) :=
        (sum_bodies_sum_cells bodies' A T'' r (fun c => volume (P c))).symm
    _ = ∑ j ∈ bodies', volume (Sh j) := (Finset.sum_congr rfl fun j _ => (hShvol j).symm)

open Classical in
/-- **Step 3 of the cell/collar comparison.** The `2 r`-collar of the retained part of a block is
covered by the `4 r`-balls of the cells that block meets, so the total collar volume is at most
the block count integrated against a single ball volume. -/
lemma sum_volume_cthickening_le {ω : Type*} (bodies' : Finset ω) (A : ω → Set E)
    (T'' : Finset E) {r : ℝ} (hr : 0 < r) :
    ∑ j ∈ bodies', volume (Metric.cthickening (2 * r)
        (A j ∩ ⋃ c ∈ T'', Metric.closedBall c r))
      ≤ (∑ c ∈ T'', (cellBlockCount bodies' A r c : ENNReal)) *
          volume (Metric.closedBall (0 : E) (4 * r)) := by
  classical
  have hcov : ∀ j, Metric.cthickening (2 * r) (A j ∩ ⋃ c ∈ T'', Metric.closedBall c r)
      ⊆ ⋃ c ∈ {c ∈ T'' | (A j ∩ Metric.closedBall c r).Nonempty},
          Metric.closedBall c (4 * r) := by
    intro j x hx
    have hxth : x ∈ Metric.thickening (3 * r) (A j ∩ ⋃ c ∈ T'', Metric.closedBall c r) :=
      Metric.cthickening_subset_thickening' (by linarith) (by linarith) _ hx
    obtain ⟨u, hu, hdu⟩ := Metric.mem_thickening_iff.mp hxth
    obtain ⟨c, hc, huc⟩ := Set.mem_iUnion₂.mp hu.2
    have huc' : dist u c ≤ r := by simpa [Metric.mem_closedBall] using huc
    refine Set.mem_biUnion (Finset.mem_filter.mpr ⟨hc, ⟨u, hu.1, huc⟩⟩) ?_
    rw [Metric.mem_closedBall]
    calc dist x c ≤ dist x u + dist u c := dist_triangle x u c
      _ ≤ 3 * r + r := by linarith
      _ ≤ 4 * r := by linarith
  have hper : ∀ j, volume (Metric.cthickening (2 * r)
      (A j ∩ ⋃ c ∈ T'', Metric.closedBall c r))
      ≤ ∑ c ∈ {c ∈ T'' | (A j ∩ Metric.closedBall c r).Nonempty},
          volume (Metric.closedBall (0 : E) (4 * r)) := by
    intro j
    refine le_trans (measure_mono (hcov j)) ?_
    refine le_trans (measure_biUnion_finset_le _ _) ?_
    refine Finset.sum_le_sum fun c _ => ?_
    exact le_of_eq (volume_closedBall_center_eq c (by linarith))
  calc ∑ j ∈ bodies', volume (Metric.cthickening (2 * r)
        (A j ∩ ⋃ c ∈ T'', Metric.closedBall c r))
      ≤ ∑ j ∈ bodies', ∑ c ∈ {c ∈ T'' | (A j ∩ Metric.closedBall c r).Nonempty},
          volume (Metric.closedBall (0 : E) (4 * r)) := Finset.sum_le_sum fun j _ => hper j
    _ = ∑ c ∈ T'', (cellBlockCount bodies' A r c : ENNReal) *
          volume (Metric.closedBall (0 : E) (4 * r)) :=
        sum_bodies_sum_cells bodies' A T'' r _
    _ = (∑ c ∈ T'', (cellBlockCount bodies' A r c : ENNReal)) *
          volume (Metric.closedBall (0 : E) (4 * r)) := by rw [Finset.sum_mul]

/-- The `4 r`-ball has `4 ^ n` times the volume of the `r`-ball. -/
lemma volume_closedBall_four_mul {r : ℝ} (hr : 0 < r) :
    volume (Metric.closedBall (0 : E) (4 * r))
      = ((4 ^ Module.finrank ℝ E : ℕ) : ENNReal) * volume (Metric.closedBall (0 : E) r) := by
  rw [MeasureTheory.Measure.addHaar_closedBall' volume (0 : E) (by linarith : (0:ℝ) ≤ 4 * r),
    MeasureTheory.Measure.addHaar_closedBall' volume (0 : E) hr.le, ← mul_assoc]
  congr 1
  rw [show (4 * r) ^ Module.finrank ℝ E
      = (4 : ℝ) ^ Module.finrank ℝ E * r ^ Module.finrank ℝ E from mul_pow 4 r _,
    ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [← ENNReal.ofReal_natCast]
  norm_num


/-- The dimensional constant of the cell/collar comparison. -/
def cellCollarConstant (n : ℕ) : ℕ := 2 * 20 ^ n

open Classical in
/-- **The cell/collar comparison: the outer cell shading is not smaller than the `2 r`-collar of
the retained inner blocks, up to a dimensional constant.**

This is the inequality conjunct (i) needs once conjunct (iv) has forced the outer shading down to
whole net cells. Its three steps are
`Kakeya.ThinCase.two_pow_mul_volume_region_le_sum_volume_cellShade` (the outer shades are unions
of whole cells, so their total volume is the block count integrated against the cells),
`Kakeya.ThinCase.card_mul_volume_closedBall_le` (packing: a separated net's balls have total
volume at most `5 ^ n` times the volume of their union) and
`Kakeya.ThinCase.sum_volume_cthickening_le` (covering: the `2 r`-collar of a block sits in the
`4 r`-balls of the cells that block meets). The dyadic band of the block count along the retained
cells, which `Kakeya.ThinCase.exists_cellOuterShading` produces for conjunct (iii)(a), is what
lets the same `2 ^ m` cancel between the first and the third. -/
theorem sum_volume_cthickening_le_mul_sum_volume_cellShade
    {ω : Type*} (bodies' : Finset ω) (A : ω → Set E) (T'' : Finset E) (P : E → Set E)
    (m : ℕ) (Sh : ω → Set E) {r : NNReal} (hr : 0 < r)
    (hsep : Metric.IsSeparated (r : ENNReal) (T'' : Set E))
    (hPmeas : ∀ c ∈ T'', MeasurableSet (P c))
    (hPdisj : (T'' : Set E).PairwiseDisjoint P)
    (hPunion : (⋃ c ∈ T'', P c) = ⋃ c ∈ T'', Metric.closedBall c (r : ℝ))
    (hband : ∀ c ∈ T'', 2 ^ m ≤ cellBlockCount bodies' A (r : ℝ) c ∧
      cellBlockCount bodies' A (r : ℝ) c < 2 ^ (m + 1))
    (hSh : ∀ j, Sh j = ⋃ c ∈ {c ∈ T'' | (A j ∩ Metric.closedBall c (r : ℝ)).Nonempty}, P c) :
    ∑ j ∈ bodies', volume (Metric.cthickening (2 * (r : ℝ))
        (A j ∩ ⋃ c ∈ T'', Metric.closedBall c (r : ℝ)))
      ≤ ((cellCollarConstant (Module.finrank ℝ E) : ℕ) : ENNReal) *
          ∑ j ∈ bodies', volume (Sh j) := by
  classical
  set n := Module.finrank ℝ E with hn
  have hrR : (0:ℝ) < (r:ℝ) := hr
  set vr : ENNReal := volume (Metric.closedBall (0 : E) (r : ℝ)) with hvr
  have hbetaSum : ∑ c ∈ T'', (cellBlockCount bodies' A (r : ℝ) c : ENNReal)
      ≤ (T''.card : ENNReal) * ((2 ^ (m + 1) : ℕ) : ENNReal) := by
    calc ∑ c ∈ T'', (cellBlockCount bodies' A (r : ℝ) c : ENNReal)
        ≤ ∑ _c ∈ T'', ((2 ^ (m + 1) : ℕ) : ENNReal) := by
          refine Finset.sum_le_sum fun c hc => ?_
          exact_mod_cast (hband c hc).2.le
      _ = (T''.card : ENNReal) * ((2 ^ (m + 1) : ℕ) : ENNReal) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  calc ∑ j ∈ bodies', volume (Metric.cthickening (2 * (r : ℝ))
        (A j ∩ ⋃ c ∈ T'', Metric.closedBall c (r : ℝ)))
      ≤ (∑ c ∈ T'', (cellBlockCount bodies' A (r : ℝ) c : ENNReal)) *
          volume (Metric.closedBall (0 : E) (4 * (r : ℝ))) :=
        sum_volume_cthickening_le bodies' A T'' hrR
    _ = (∑ c ∈ T'', (cellBlockCount bodies' A (r : ℝ) c : ENNReal)) *
          (((4 ^ n : ℕ) : ENNReal) * vr) := by rw [volume_closedBall_four_mul hrR]
    _ ≤ ((T''.card : ENNReal) * ((2 ^ (m + 1) : ℕ) : ENNReal)) *
          (((4 ^ n : ℕ) : ENNReal) * vr) := mul_le_mul' hbetaSum le_rfl
    _ = (((2 * 4 ^ n : ℕ) : ENNReal) * ((2 ^ m : ℕ) : ENNReal)) *
          ((T''.card : ENNReal) * vr) := by
        push_cast
        ring
    _ ≤ (((2 * 4 ^ n : ℕ) : ENNReal) * ((2 ^ m : ℕ) : ENNReal)) *
          (((5 ^ n : ℕ) : ENNReal) * volume (⋃ c ∈ T'', Metric.closedBall c (r : ℝ))) :=
        mul_le_mul' le_rfl (card_mul_volume_closedBall_le hr hsep)
    _ = ((cellCollarConstant n : ℕ) : ENNReal) *
          (((2 ^ m : ℕ) : ENNReal) * volume (⋃ c ∈ T'', P c)) := by
        rw [hPunion, cellCollarConstant]
        push_cast
        rw [show ((20 : ENNReal)) = 4 * 5 by norm_num, mul_pow]
        ring
    _ ≤ ((cellCollarConstant n : ℕ) : ENNReal) * ∑ j ∈ bodies', volume (Sh j) :=
        mul_le_mul' le_rfl (two_pow_mul_volume_region_le_sum_volume_cellShade bodies' A T'' P m
          Sh (r : ℝ) hPmeas hPdisj (fun c hc => (hband c hc).1) hSh)


/-- **From the Córdoba collar to the `2 r`-collar.**

`ShadedBody.lambdaForInducedShading_of_measurable` — and hence
`Kakeya.ThinCase.fullness_ge_three_eta` — bounds the volume of the induced shading, whose collar
radius is `2 τ₂(K)`. Conjunct (iv) forces the outer shading down to the `2 r`-collar,
`r = w₁ / 8`. The two are comparable at a purely dimensional cost, which is
`Kakeya.ThinCase.volume_cthickening_le_mul_volume_cthickening`. -/
theorem volume_inducedShading_le_mul_volume_cthickening
    {ι : Type*} (s : Finset ι) (V : ι → ShadedBody E) (K : ConvexSpaceBody E)
    {r : ℝ} (hr : 0 < r) {Z : Set E} (hZne : Z.Nonempty) (hZbdd : Bornology.IsBounded Z)
    (hZ : iUnionShade s V ⊆ Z) (hrK : 2 * r ≤ 2 * K.scale) :
    volume (ShadedBody.inducedShading s V K).shade
      ≤ (collarCompareConstant (Module.finrank ℝ E) (2 * r) (2 * K.scale) : ENNReal) *
          volume (Metric.cthickening (2 * r) Z) := by
  have hsub : (ShadedBody.inducedShading s V K).shade
      ⊆ Metric.cthickening (2 * K.scale) Z := by
    rw [ShadedBody.shade_inducedShading]
    exact Set.inter_subset_left.trans (Metric.cthickening_subset_of_subset _ hZ)
  refine le_trans (measure_mono hsub) ?_
  exact volume_cthickening_le_mul_volume_cthickening hZne hZbdd (by linarith) hrK


/-! ### Conjunct (i) for the cell shading

The Córdoba bound of `Kakeya.ThinCase.fullness_ge_three_eta` is stated for the *induced* shading;
conjunct (iv) forces the *cell* shading. The three lemmas below carry the bound across, using
the cell/collar comparison above: `Kakeya.ThinCase.fullness_le_mul_fullness_of_sum_shade_le`
transfers a fullness bound along a shade-mass comparison at equal carriers,
`Kakeya.ThinCase.sum_volume_inducedShading_le_mul_sum_volume_cellShade` supplies that comparison,
and `Kakeya.ThinCase.fullness_cellShading_ge` is the composition. -/

/-- **Transferring a fullness bound along a shade-mass comparison at equal carriers.**

If two shaded families over the same index set have the same carriers and the shade mass of the
first is at most `K` times that of the second, then the fullness of the first is at most `K`
times that of the second. This is what carries the Córdoba bound of
`Kakeya.ThinCase.fullness_ge_three_eta`, stated for the *induced* shading, over to the *cell*
shading that conjunct (iv) forces. -/
theorem fullness_le_mul_fullness_of_sum_shade_le {κ : Type*} (t : Finset κ)
    (W W' : κ → ShadedBody E) {K : ENNReal}
    (hcar : ∀ j ∈ t, volume (W' j).carrier = volume (W j).carrier)
    (hshade : ∑ j ∈ t, volume (W' j).shade ≤ K * ∑ j ∈ t, volume (W j).shade) :
    (ShadedBody.fullness t W' : ENNReal) ≤ K * (ShadedBody.fullness t W : ENNReal) := by
  rw [ShadedBody.fullness_def, ShadedBody.fullness_def]
  rw [Finset.sum_congr rfl hcar]
  calc (∑ j ∈ t, volume (W' j).shade) / (∑ j ∈ t, volume (W j).carrier)
      ≤ (K * ∑ j ∈ t, volume (W j).shade) / (∑ j ∈ t, volume (W j).carrier) := by
        exact ENNReal.div_le_div_right hshade _
    _ = K * ((∑ j ∈ t, volume (W j).shade) / (∑ j ∈ t, volume (W j).carrier)) := by
        rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
        ring


omit [MeasurableSpace E] [BorelSpace E] in
/-- The collar-comparison constant is monotone in the larger radius. -/
lemma collarCompareConstant_mono {n : ℕ} {s S S' : ℝ} (hs : 0 < s) (hS : 0 ≤ S)
    (hSS' : S ≤ S') : collarCompareConstant n s S ≤ collarCompareConstant n s S' := by
  rw [collarCompareConstant, collarCompareConstant]
  refine Real.toNNReal_le_toNNReal_iff'.mpr (Or.inl ?_)
  have h0 : (0:ℝ) ≤ 2 * (S + 2 * s) / s := by positivity
  have hbase : 2 * (S + 2 * s) / s ≤ 2 * (S' + 2 * s) / s := by
    apply div_le_div_of_nonneg_right _ hs.le
    linarith
  gcongr

open Classical in
/-- **The induced (Córdoba) shading is dominated by the cell shading**, summed over the bodies:
the composition of `Kakeya.ThinCase.volume_inducedShading_le_mul_volume_cthickening` with
`Kakeya.ThinCase.sum_volume_cthickening_le_mul_sum_volume_cellShade`. -/
theorem sum_volume_inducedShading_le_mul_sum_volume_cellShade
    {ι κ : Type*} (bodies' : Finset κ) (fib : κ → Finset ι) (V : ι → ShadedBody E)
    (Wb : κ → ConvexSpaceBody E) (T'' : Finset E) (P : E → Set E) (m : ℕ) (Sh : κ → Set E)
    {r : NNReal} (hr : 0 < r) {S₀ : ℝ}
    (A : κ → Set E)
    (hsep : Metric.IsSeparated (r : ENNReal) (T'' : Set E))
    (hPmeas : ∀ c ∈ T'', MeasurableSet (P c))
    (hPdisj : (T'' : Set E).PairwiseDisjoint P)
    (hPunion : (⋃ c ∈ T'', P c) = ⋃ c ∈ T'', Metric.closedBall c (r : ℝ))
    (hband : ∀ c ∈ T'', 2 ^ m ≤ cellBlockCount bodies' A (r : ℝ) c ∧
      cellBlockCount bodies' A (r : ℝ) c < 2 ^ (m + 1))
    (hSh : ∀ j, Sh j = ⋃ c ∈ {c ∈ T'' | (A j ∩ Metric.closedBall c (r : ℝ)).Nonempty}, P c)
    (hZne : ∀ j ∈ bodies', (A j ∩ ⋃ c ∈ T'', Metric.closedBall c (r : ℝ)).Nonempty)
    (hZbdd : ∀ j ∈ bodies', Bornology.IsBounded (A j ∩ ⋃ c ∈ T'', Metric.closedBall c (r : ℝ)))
    (hZsub : ∀ j ∈ bodies', iUnionShade (fib j) V ⊆ A j ∩ ⋃ c ∈ T'', Metric.closedBall c (r : ℝ))
    (hrK : ∀ j ∈ bodies', 2 * (r : ℝ) ≤ 2 * (Wb j).scale)
    (hSbd : ∀ j ∈ bodies', 2 * (Wb j).scale ≤ S₀) :
    ∑ j ∈ bodies', volume (ShadedBody.inducedShading (fib j) V (Wb j)).shade
      ≤ ((collarCompareConstant (Module.finrank ℝ E) (2 * (r : ℝ)) S₀ : NNReal) : ENNReal) *
          (((cellCollarConstant (Module.finrank ℝ E) : ℕ) : ENNReal) *
            ∑ j ∈ bodies', volume (Sh j)) := by
  have hper : ∀ j ∈ bodies',
      volume (ShadedBody.inducedShading (fib j) V (Wb j)).shade
        ≤ ((collarCompareConstant (Module.finrank ℝ E) (2 * (r : ℝ)) S₀ : NNReal) : ENNReal) *
            volume (Metric.cthickening (2 * (r : ℝ))
              (A j ∩ ⋃ c ∈ T'', Metric.closedBall c (r : ℝ))) := by
    intro j hj
    refine le_trans (volume_inducedShading_le_mul_volume_cthickening (fib j) V (Wb j)
      (r := (r : ℝ)) hr (hZne j hj) (hZbdd j hj) (hZsub j hj) (hrK j hj)) ?_
    refine mul_le_mul' ?_ le_rfl
    have hrpos : (0:ℝ) < (r : ℝ) := hr
    exact_mod_cast collarCompareConstant_mono (n := Module.finrank ℝ E)
      (by linarith : (0:ℝ) < 2 * (r : ℝ))
      (by linarith [hrK j hj] : (0:ℝ) ≤ 2 * (Wb j).scale) (hSbd j hj)
  calc ∑ j ∈ bodies', volume (ShadedBody.inducedShading (fib j) V (Wb j)).shade
      ≤ ∑ j ∈ bodies',
          ((collarCompareConstant (Module.finrank ℝ E) (2 * (r : ℝ)) S₀ : NNReal) : ENNReal) *
            volume (Metric.cthickening (2 * (r : ℝ))
              (A j ∩ ⋃ c ∈ T'', Metric.closedBall c (r : ℝ))) := Finset.sum_le_sum hper
    _ = ((collarCompareConstant (Module.finrank ℝ E) (2 * (r : ℝ)) S₀ : NNReal) : ENNReal) *
          ∑ j ∈ bodies', volume (Metric.cthickening (2 * (r : ℝ))
            (A j ∩ ⋃ c ∈ T'', Metric.closedBall c (r : ℝ))) := by rw [Finset.mul_sum]
    _ ≤ ((collarCompareConstant (Module.finrank ℝ E) (2 * (r : ℝ)) S₀ : NNReal) : ENNReal) *
          (((cellCollarConstant (Module.finrank ℝ E) : ℕ) : ENNReal) *
            ∑ j ∈ bodies', volume (Sh j)) :=
        mul_le_mul' le_rfl (sum_volume_cthickening_le_mul_sum_volume_cellShade bodies' A T'' P m
          Sh hr hsep hPmeas hPdisj hPunion hband hSh)

/-- **Conjunct (i) for the cell shading.** -/
theorem fullness_cellShading_ge {κ : Type*} (bodies' : Finset κ)
    (Wind Wcell : κ → ShadedBody E) {δ : NNReal} {η : ℝ} {K₁ K₂ : ENNReal}
    (hind : (δ : ENNReal) ^ (3 * η) ≤ K₁ * (ShadedBody.fullness bodies' Wind : ENNReal))
    (hcar : ∀ j ∈ bodies', volume (Wind j).carrier = volume (Wcell j).carrier)
    (hshade : ∑ j ∈ bodies', volume (Wind j).shade
      ≤ K₂ * ∑ j ∈ bodies', volume (Wcell j).shade) :
    (δ : ENNReal) ^ (3 * η) ≤ (K₁ * K₂) * (ShadedBody.fullness bodies' Wcell : ENNReal) := by
  calc (δ : ENNReal) ^ (3 * η) ≤ K₁ * (ShadedBody.fullness bodies' Wind : ENNReal) := hind
    _ ≤ K₁ * (K₂ * (ShadedBody.fullness bodies' Wcell : ENNReal)) :=
        mul_le_mul' le_rfl (fullness_le_mul_fullness_of_sum_shade_le bodies' Wcell Wind hcar hshade)
    _ = (K₁ * K₂) * (ShadedBody.fullness bodies' Wcell : ENNReal) := by ring


end CellVolume

end Kakeya.ThinCase
