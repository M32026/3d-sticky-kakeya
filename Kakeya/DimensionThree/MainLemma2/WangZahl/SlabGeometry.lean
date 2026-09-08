/-
Slab geometry for the Wang--Zahl route: the two facts about `SlabTestSet` that
the source uses without comment whenever it puts a tube inside a slab.

Source: `blueprint/src/WZ2/250224e_K3.tex`, the paragraph preceding Definition
`defnCDE` (a slab is the intersection of the unit ball with a thickened
hyperplane, and `|W| ~ thickness`).

* `exists_slabTestSet_containing_tube` -- a `SlabTestSet` of any prescribed
  thickness `t >= delta` containing a given `delta`-tube of the unit ball.
  Its geometric core is `exists_hyperplane3_segment_subset`: every unit segment
  of `R^3` lies in a plane, so the tube, being the `delta`-thickening of its
  axis segment, lies in the `delta`-thickening of that plane.
* `volume_slabTestSet_le` -- the volume upper bound
  `|W| <= W.thickness * |B(0,2)|`.

Both are stated for the bare `Tube`/`SlabTestSet` data so that any consumer
(the currency lower bound, the Wolff hairbrush slab count) can use them
directly.
-/
module

public import Kakeya.DimensionThree.MainLemma2.WangZahl.Definitions
public import Kakeya.Projection

@[expose] public section

open MeasureTheory Metric EuclideanGeometry Module

namespace Kakeya.WangZahl

noncomputable section

/-! ### The volume of a slab -/

/-- A subset of the unit ball lying in the closed `t`-neighbourhood of a plane
has volume at most `t * |B(0,2)|`.

Both directions of the projection comparison of `Kakeya.Projection` are used:
the shadow bounds the volume from above with a factor `2t`, and the shadow's own
`2`-dimensional Hausdorff measure is at most `|B(0,2)|/2`, because the full unit
normal fibre over the shadow sits inside `B(0,2)`. -/
theorem volume_le_of_subset_slab {P : AffineSubspace ℝ Space3} [Nonempty ↥P]
    (hcodim : finrank ℝ Space3 = finrank ℝ ↥P.direction + 1)
    {t : NNReal} {s : Set Space3} (hs1 : s ⊆ closedBall 0 1)
    (hst : s ⊆ cthickening (t : ℝ) (P : Set Space3))
    (hmeas : MeasurableSet ((orthogonalProjection P) '' s)) :
    volume s ≤ (t : ENNReal) * volume (closedBall (0 : Space3) 2) := by
  letI : MeasureSpace ↥P := instMeasureSpaceAffineSubspace
  have h1 : volume s ≤ 2 * (t : ENNReal) *
      μHE[finrank ℝ ↥P.direction] ((orthogonalProjection P) '' s) :=
    volume_image_orthogonalProjection hcodim hst
  have h2 : 2 * ENNReal.ofReal 1 * volume ((orthogonalProjection P) '' s) ≤
      volume (cthickening (1 : ℝ) s) :=
    two_mul_ofReal_mul_volume_orthogonalProjection_image_le_volume_cthickening
      P hcodim zero_le_one hmeas
  have h3 : cthickening (1 : ℝ) s ⊆ closedBall (0 : Space3) 2 := by
    refine (cthickening_subset_of_subset 1 hs1).trans ?_
    rw [cthickening_closedBall (by norm_num : (0:ℝ) ≤ 1) (by norm_num : (0:ℝ) ≤ 1)]
    norm_num
  have h4 : 2 * μHE[finrank ℝ ↥P.direction] ((orthogonalProjection P) '' s) ≤
      volume (closedBall (0 : Space3) 2) := by
    rw [← volume_affineSubspace]
    calc 2 * volume ((orthogonalProjection P) '' s)
        = 2 * ENNReal.ofReal 1 * volume ((orthogonalProjection P) '' s) := by
          simp
      _ ≤ volume (cthickening (1 : ℝ) s) := h2
      _ ≤ _ := measure_mono h3
  calc volume s ≤ 2 * (t : ENNReal) *
        μHE[finrank ℝ ↥P.direction] ((orthogonalProjection P) '' s) := h1
    _ = (t : ENNReal) * (2 * μHE[finrank ℝ ↥P.direction]
          ((orthogonalProjection P) '' s)) := by ring
    _ ≤ (t : ENNReal) * volume (closedBall (0 : Space3) 2) := by gcongr

/-- **Volume bound for a Wang--Zahl slab**: `|W| <= W.thickness * |B(0,2)|`. -/
theorem volume_slabTestSet_le (W : SlabTestSet) :
    volume W.carrier ≤ (W.thickness : ENNReal) * volume (closedBall (0 : Space3) 2) := by
  haveI : Nonempty ↥W.plane.carrier := W.plane.nonempty_carrier.to_subtype
  have hcodim : finrank ℝ Space3 = finrank ℝ ↥W.plane.carrier.direction + 1 := by
    rw [W.plane.finrank_direction]
    simp
  have hcpt : IsCompact W.carrier :=
    IsCompact.inter_right (isCompact_closedBall _ _) isClosed_cthickening
  have hmeas : MeasurableSet ((orthogonalProjection W.plane.carrier) '' W.carrier) :=
    (hcpt.image (orthogonalProjection W.plane.carrier).cont).isClosed.measurableSet
  exact volume_le_of_subset_slab hcodim Set.inter_subset_left Set.inter_subset_right hmeas

/-! ### A slab through a prescribed tube -/

open Submodule in
/-- Every unit segment of `R^3` lies in a plane. -/
theorem exists_hyperplane3_segment_subset (x y : Space3) (h : dist x y = 1) :
    ∃ H : Hyperplane3, segment ℝ x y ⊆ (H.carrier : Set Space3) := by
  have hd : y - x ≠ 0 := sub_ne_zero.mpr (by
    intro he; rw [he] at h; simp at h)
  have key : ∀ v : Space3, v ≠ 0 → finrank ℝ ((ℝ ∙ v)ᗮ : Submodule ℝ Space3) = 2 := by
    intro v hv
    have := Submodule.finrank_add_finrank_orthogonal (K := (ℝ ∙ v : Submodule ℝ Space3))
    rw [finrank_span_singleton hv] at this
    have h3 : finrank ℝ Space3 = 3 := by simp
    omega
  have hfr : finrank ℝ ((ℝ ∙ (y - x))ᗮ : Submodule ℝ Space3) = 2 := key _ hd
  have hne : ((ℝ ∙ (y - x))ᗮ : Submodule ℝ Space3) ≠ ⊥ := by
    intro hb; rw [hb] at hfr; simp at hfr
  obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hinner : (inner ℝ n (y - x) : ℝ) = 0 := by
    have := hn (y - x) (Submodule.mem_span_singleton_self _)
    simpa [real_inner_comm] using this
  set P : AffineSubspace ℝ Space3 := AffineSubspace.mk' x ((ℝ ∙ n)ᗮ) with hP
  have hdir : P.direction = ((ℝ ∙ n)ᗮ : Submodule ℝ Space3) := AffineSubspace.direction_mk' _ _
  have hxP : x ∈ P := AffineSubspace.self_mem_mk' _ _
  have hyP : y ∈ P := by
    rw [hP, AffineSubspace.mem_mk']
    have hvs : (y -ᵥ x : Space3) = y - x := rfl
    rw [hvs, Submodule.mem_orthogonal_singleton_iff_inner_left]
    simpa [real_inner_comm] using hinner
  have hPfr : finrank ℝ ↥P.direction = 2 := by rw [hdir]; exact key _ hn0
  exact ⟨⟨P, ⟨x, hxP⟩, hPfr⟩, (P.convex).segment_subset hxP hyP⟩

/-- **A slab of any prescribed thickness `t >= delta` containing a given
`delta`-tube of the unit ball.**

The plane is any plane through the axis of the tube; the tube is the
`delta`-thickening of that axis, hence lies in the `t`-thickening of the
plane. -/
theorem exists_slabTestSet_containing_tube {δ : NNReal} (T : Tube δ Space3)
    (hball : T.carrier ⊆ closedBall 0 1) {t : NNReal} (hδt : δ ≤ t) :
    ∃ W : SlabTestSet, W.thickness = t ∧ T.carrier ⊆ W.carrier := by
  obtain ⟨H, hH⟩ := exists_hyperplane3_segment_subset T.x T.y T.dist_eq_one
  refine ⟨⟨H, t⟩, rfl, Set.subset_inter hball ?_⟩
  rw [T.carrier_eq_cthickening]
  refine (cthickening_mono (by exact_mod_cast hδt) _).trans ?_
  exact cthickening_subset_of_subset _ hH

/-- **A slab swallowing the part of a tube that lies in the unit ball.**

Unlike `exists_slabTestSet_containing_tube` the tube `R` itself need not be
contained in the unit ball: only the sets one wants to place inside the slab
must be.  This is the form needed by the slab-count step of the Wolff hairbrush
argument, where `R` is a `theta`-tube produced by a partitioning cover and only
the `delta`-tubes of the family are known to lie in the unit ball. -/
theorem exists_slabTestSet_swallowing_tube {θ : NNReal} (R : Tube θ Space3)
    {t : NNReal} (hθt : θ ≤ t) :
    ∃ W : SlabTestSet, W.thickness = t ∧
      ∀ A : Set Space3, A ⊆ closedBall 0 1 → A ⊆ R.carrier → A ⊆ W.carrier := by
  obtain ⟨H, hH⟩ := exists_hyperplane3_segment_subset R.x R.y R.dist_eq_one
  refine ⟨⟨H, t⟩, rfl, fun A hA1 hAR => Set.subset_inter hA1 (hAR.trans ?_)⟩
  rw [R.carrier_eq_cthickening]
  refine (cthickening_mono (by exact_mod_cast hθt) _).trans ?_
  exact cthickening_subset_of_subset _ hH

/-- The `ShadedTube` form of `exists_slabTestSet_containing_tube` at the tube's
own scale. -/
theorem exists_slabTestSet_containing {δ : NNReal} (T : ShadedTube δ Space3)
    (hball : T.carrier ⊆ closedBall 0 1) :
    ∃ W : SlabTestSet, W.thickness = δ ∧ T.carrier ⊆ W.carrier :=
  exists_slabTestSet_containing_tube T.toTube hball le_rfl

end

end Kakeya.WangZahl
