/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.LocalAngleConcentration

/-!
# The middle-half captured mass

`Plank.exists_goodCover_saturated_aggregate` asks for a lower bound on the shading mass inside the
*middle halves* `Plank.halfSlabBox` of the grid boxes, because tangentiality is automatic there
(`Plank.comparableScalars_of_mem_halfBox`) while a plank merely meeting a box need not be tangential
to it.  A full-box mass bound would be useless for this: `B_q^{(1/2)} ⊆ B_q` runs the wrong way for
transporting a mass lower bound.

The route is a *fixed-shift* covering argument, not a collar estimate.  The eight shifts of
`Plank.gridShiftSet` are exactly `{0, ½}³`, and `Plank.exists_shift_middle_half` says that for any
point one of them puts that point in the **middle half** of its round-index box.  So the middle
halves of the eight shifted grids *cover*, and averaging over the eight shifts loses only the
absolute factor `#gridShiftSet = 8`:

* the covering, with the box index inside the finite window `Plank.slabBoxIndexFor b ⌈Cset⌉`
  (private);
* `Plank.shade_subset_iUnion_halfSlabBox` — the same, as a subset statement for a plank of the
  controlled slab family;
* the averaging, giving one shift with
  `∑ᵢ |Yᵢ| ≤ #gridShiftSet · ∑_q ∑ᵢ |Yᵢ ∩ B_q^{(1/2)}|` (private);
* `Plank.sum_halfBox_eq_sum_saturated` — the terms outside the saturated family vanish, so the sum
  over `s` *is* the sum over `T q = {i ∈ s | Yᵢ meets B_q^{(1/2)}}`, which is the shape
  `Plank.exists_goodCover_saturated_aggregate` asks for;
* `Plank.exists_shift_halfBox_capture_of_fullness` — the packaged form, from a fullness lower bound
  and the plank volume, i.e. exactly the `hcap` hypothesis of
  `Plank.exists_goodCover_saturated_aggregate`.

Tangentiality is *automatic* on the middle half (`Plank.comparableScalars_of_mem_halfBox`), so no
tangential filter has to be carried through the capture.  **The cost is the single absolute constant
`#gridShiftSet = 8`**, bound before every geometric datum.
-/

@[expose] public section

open MeasureTheory Convexity
open scoped NNReal Real ENNReal

noncomputable section

namespace Plank

variable {ι : Type*}

/-! ## The middle halves of the shifted grids cover -/

/-- **The middle halves of the eight shifted grids cover the dilated slab.**  For a point `x` of the
`Cset`-dilation of `S` there is a shift `sh ∈ Plank.gridShiftSet` and a box index `q` in the finite
window `Plank.slabBoxIndexFor b ⌈Cset⌉` with `x` in the *middle half* of `B_q^{sh}`.

This is `Plank.exists_shift_middle_half` (which produces the coordinate bounds `|·| ≤ w_j/2`, i.e.
membership in the `2⁻¹`-dilation) together with `Plank.shiftedSlabRoundIndex_mem_dilation` (which
places the round index in the window). -/
private theorem exists_shift_mem_halfSlabBox {θ b : ℝ≥0} {hθ1 : θ ≤ 1} (S : Slab θ hθ1)
    (Cset : ℝ≥0)
    (hCset : 1 ≤ Cset) (hθ : 0 < θ) (hb : 0 < b) (hb1 : b ≤ 1)
    {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ ((S.toPrismNDim.dilation Cset).carrier : Set (EuclideanSpace ℝ (Fin 3)))) :
    ∃ sh ∈ gridShiftSet, ∃ q ∈ slabBoxIndexFor b ⌈(Cset : ℝ)⌉₊,
      x ∈ halfSlabBox S b sh q := by
  obtain ⟨sh, hsh, hmid⟩ := exists_shift_middle_half S hθ hb x
  refine ⟨sh, hsh, _,
    shiftedSlabRoundIndex_mem_dilation S hb hb1 hsh hCset (Nat.le_ceil _) hx, ?_⟩
  exact (PrismNDim.mem_carrier_iff _ x).mpr fun j => (hmid j).trans_eq
    (by simp [shiftedSlabBox, PrismNDim.thicknesses_mk', div_eq_mul_inv, mul_comm])

/-- **The shading of a plank of the controlled slab family is covered by the middle halves.**  The
subset form of `Plank.exists_shift_mem_halfSlabBox`: a plank of
`Plank.inSlabFamilyC Cset Cang s V S` sits in the `Cset`-dilation of `S`, so its shading does
too. -/
theorem shade_subset_iUnion_halfSlabBox {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    {θ : ℝ≥0} {hθ1 : θ ≤ 1} (S : Slab θ hθ1) (Cset Cang : ℝ≥0) (hCset : 1 ≤ Cset)
    (s : Finset ι) (V : ι → Plank a b hab hb1)
    (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (hθ : 0 < θ) (hb : 0 < b) (hb1' : b ≤ 1)
    (hshade : ∀ i ∈ s, (Y i).shade ⊆ ((V i).carrier : Set (EuclideanSpace ℝ (Fin 3))))
    (hfam : ∀ i ∈ s, i ∈ inSlabFamilyC Cset Cang s V S) {i : ι} (hi : i ∈ s) :
    (Y i).shade ⊆ ⋃ sh ∈ gridShiftSet, ⋃ q ∈ slabBoxIndexFor b ⌈(Cset : ℝ)⌉₊,
      halfSlabBox S b sh q := by
  intro y hy
  obtain ⟨sh, hsh, q, hq, hyHalf⟩ := exists_shift_mem_halfSlabBox S Cset hCset hθ hb hb1'
    ((mem_inSlabFamilyC.mp (hfam i hi)).2.1 (hshade i hi hy))
  exact Set.mem_biUnion hsh (Set.mem_biUnion hq hyHalf)

/-! ## The shifted-grid average on the middle halves -/

open scoped Classical in
/-- **The middle-half captured mass, by shift averaging.**  One shift `sh` of the eight retains, in
the *middle halves* of its boxes, at least a `(#gridShiftSet)⁻¹` fraction of the total shading mass
of the controlled slab family.

This is the captured-mass inequality in the form that
`Plank.exists_goodCover_saturated_aggregate` consumes.  The proof is the covering
`Plank.shade_subset_iUnion_halfSlabBox` — which bounds `|Yᵢ|` by the double sum over shifts and
boxes — summed over `i ∈ s` and then pigeonholed over the finite shift set.  Stated
multiplicatively, with no division in `ℝ≥0∞`.

No tangential filter appears, because tangentiality on the middle half is automatic
(`Plank.comparableScalars_of_mem_halfBox`). -/
private theorem exists_shift_halfBox_massCapture {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    {θ : ℝ≥0} {hθ1 : θ ≤ 1} (S : Slab θ hθ1) (Cset Cang : ℝ≥0) (hCset : 1 ≤ Cset)
    (s : Finset ι) (V : ι → Plank a b hab hb1)
    (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (hθ : 0 < θ) (hb : 0 < b) (hb1' : b ≤ 1)
    (hshade : ∀ i ∈ s, (Y i).shade ⊆ ((V i).carrier : Set (EuclideanSpace ℝ (Fin 3))))
    (hfam : ∀ i ∈ s, i ∈ inSlabFamilyC Cset Cang s V S) :
    ∃ sh ∈ gridShiftSet,
      ∑ i ∈ s, volume (Y i).shade
        ≤ (gridShiftSet.card : ENNReal) *
          ∑ q ∈ slabBoxIndexFor b ⌈(Cset : ℝ)⌉₊, ∑ i ∈ s,
            volume ((Y i).shade ∩ halfSlabBox S b sh q) := by
  set W := slabBoxIndexFor b ⌈(Cset : ℝ)⌉₊
  set f : (Fin 3 → ℝ) → ENNReal :=
    fun sh => ∑ q ∈ W, ∑ i ∈ s, volume ((Y i).shade ∩ halfSlabBox S b sh q)
  obtain ⟨sh, hsh, hsup⟩ := Finset.exists_mem_eq_sup gridShiftSet gridShiftSet_nonempty f
  refine ⟨sh, hsh, ?_⟩
  -- Bound each `|Yᵢ|` by the double sum over shifts and boxes, sum over `i`, swap the order,
  -- then pigeonhole over the eight shifts.
  calc ∑ i ∈ s, volume (Y i).shade
      ≤ ∑ i ∈ s, ∑ sh' ∈ gridShiftSet, ∑ q ∈ W,
          volume ((Y i).shade ∩ halfSlabBox S b sh' q) := Finset.sum_le_sum fun i hi => by
        refine (measure_mono (fun y hy => ?_)).trans
          ((measure_biUnion_finset_le _ _).trans
            (Finset.sum_le_sum fun sh' _ => measure_biUnion_finset_le _ _))
        obtain ⟨sh', hsh', hy'⟩ := Set.mem_iUnion₂.mp
          (shade_subset_iUnion_halfSlabBox S Cset Cang hCset s V Y hθ hb hb1' hshade hfam hi hy)
        obtain ⟨q, hq, hyh⟩ := Set.mem_iUnion₂.mp hy'
        exact Set.mem_biUnion hsh' (Set.mem_biUnion hq ⟨hy, hyh⟩)
    _ = ∑ sh' ∈ gridShiftSet, f sh' := Finset.sum_comm_cycle.symm
    _ ≤ gridShiftSet.card • f sh :=
        Finset.sum_le_card_nsmul _ _ _ fun _ h => (Finset.le_sup h).trans_eq hsup
    _ = (gridShiftSet.card : ENNReal) * ∑ q ∈ W, ∑ i ∈ s,
          volume ((Y i).shade ∩ halfSlabBox S b sh q) := nsmul_eq_mul _ _

open scoped Classical in
/-- **The sum over the family is the sum over the saturated family.**  A plank whose shading misses
`B_q^{(1/2)}` contributes nothing, so restricting the inner sum to the *saturated* local family
`T_q = {i ∈ s | Yᵢ meets B_q^{(1/2)}}` changes nothing.  This is what turns
`Plank.exists_shift_halfBox_massCapture` into the shape of the `hcap` hypothesis of
`Plank.exists_goodCover_saturated_aggregate`, whose inner sum ranges over `T q`. -/
theorem sum_halfBox_eq_sum_saturated {b : ℝ≥0} {θ : ℝ≥0} {hθ1 : θ ≤ 1} (S : Slab θ hθ1)
    (sh : Fin 3 → ℝ) (q : Fin 3 → ℤ) (s : Finset ι)
    (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))) :
    ∑ i ∈ s, volume ((Y i).shade ∩ halfSlabBox S b sh q)
      = ∑ i ∈ s.filter (fun i => ((Y i).shade ∩ halfSlabBox S b sh q).Nonempty),
          volume ((Y i).shade ∩ halfSlabBox S b sh q) :=
  (Finset.sum_filter_of_ne fun i _ hi =>
    Set.nonempty_iff_ne_empty.mpr fun he => hi (by simp [he])).symm

open scoped Classical in
/-- **The `hcap` hypothesis of `Plank.exists_goodCover_saturated_aggregate`, from a fullness
lower bound.**
The packaged middle-half capture: with `μ` a lower bound for the fullness of the controlled slab
family and `8ab` a lower bound for each plank's carrier volume, one shift of the eight captures

`(#gridShiftSet)⁻¹ · μ · #s · 8ab`

of mass in the middle halves of its boxes, restricted to the saturated local families.  Written
multiplicatively as `μ · #s · 8ab ≤ #gridShiftSet · (captured)`, so no division occurs.

Composing with `Plank.exists_goodCover_saturated_aggregate` at
`8 · c_good · c_stb · a ^ η = μ / #gridShiftSet` discharges its `hcap`, and the whole cost of the
conversion is the absolute constant `#gridShiftSet = 8`, fixed before every geometric datum. -/
theorem exists_shift_halfBox_capture_of_fullness {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    {θ : ℝ≥0} {hθ1 : θ ≤ 1} (S : Slab θ hθ1) (Cset Cang μ : ℝ≥0) (hCset : 1 ≤ Cset)
    (s : Finset ι) (V : ι → Plank a b hab hb1)
    (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (hθ : 0 < θ) (hb : 0 < b) (hb1' : b ≤ 1)
    (hshade : ∀ i ∈ s, (Y i).shade ⊆ ((V i).carrier : Set (EuclideanSpace ℝ (Fin 3))))
    (hfam : ∀ i ∈ s, i ∈ inSlabFamilyC Cset Cang s V S)
    (hfull : μ ≤ ShadedBody.fullness s Y)
    (hcarvol : ∀ i ∈ s, 8 * (a : ENNReal) * (b : ENNReal) ≤ volume (Y i).carrier) :
    ∃ sh ∈ gridShiftSet,
      (μ : ENNReal) * ((s.card : ENNReal) * (8 * (a : ENNReal) * (b : ENNReal)))
        ≤ (gridShiftSet.card : ENNReal) *
          ∑ q ∈ slabBoxIndexFor b ⌈(Cset : ℝ)⌉₊,
            ∑ i ∈ s.filter (fun i => ((Y i).shade ∩ halfSlabBox S b sh q).Nonempty),
              volume ((Y i).shade ∩ halfSlabBox S b sh q) := by
  obtain ⟨sh, hsh, hcap⟩ :=
    exists_shift_halfBox_massCapture S Cset Cang hCset s V Y hθ hb hb1' hshade hfam
  refine ⟨sh, hsh, (ShadedBody.coe_fullness_mul_le_sum_volume_shade s Y hfull hcarvol).trans
    (hcap.trans_eq (congrArg _ (Finset.sum_congr rfl fun q _ =>
      sum_halfBox_eq_sum_saturated S sh q s Y)))⟩

end Plank

end
