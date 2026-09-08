/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.SlabTubeSelection
public import Kakeya.DimensionThree.Plank.SlabFibreTubes

/-!
# The pairwise essentially distinct sub-fibre, packaged for the Frostman tube estimate

`Kakeya.FrostmanEstimate.multiplicity_bound` (GWZ Lemma 3.9) demands a *pairwise* essentially
distinct tube family. The normalised tube family of a slab fibre is only essentially distinct up to
the bounded multiplicity `MED` of `Plank.exists_isEDUpToMult_slabTube`, so the estimate has to be
run on a sub-fibre. This module extracts that sub-fibre once and for all, with the two quantitative
consequences the estimate needs:

* **mass retention** `∑_{fibre} |Y Q| ≤ (MED + 1) · ∑_{sub} |Y Q|`, from
  `Kakeya.IsEDUpToMult.exists_pairwise_subset_with_weight` at the weight `w Q = |Y Q|`;
* **fullness retention** `λ(fibre, T) ≤ (MED + 1) · λ(sub, T)`.

The second does *not* follow from the first by itself — fullness is a quotient and the index set
shrinks in both numerator and denominator. It does follow because the denominator only *shrinks*
when passing to a subfamily, which helps: that is `ShadedBody.fullness'_le_of_subset_of_sum_shade_le`
below. No comparison of the individual tube volumes is needed.
-/

@[expose] public section

open MeasureTheory Kakeya
open scoped NNReal Real Classical

noncomputable section

namespace ShadedBody

/-- **Fullness passes to a heavy subfamily at the same loss.** If `t ⊆ s` retains a
`C⁻¹`-fraction of the shade mass then it retains a `C⁻¹`-fraction of the fullness: the numerator
loses at most `C`, and the denominator — the total carrier volume — only shrinks. -/
theorem fullness'_le_of_subset_of_sum_shade_le {E : Type*} [TopologicalSpace E]
    [Convexity.ConvexSpace ℝ E] [MeasureSpace E] {ι : Type*} (s t : Finset ι)
    (V : ι → ShadedBody E) (hts : t ⊆ s) {C : ENNReal}
    (hmass : ∑ i ∈ s, volume (V i).shade ≤ C * ∑ i ∈ t, volume (V i).shade) :
    fullness' s V ≤ C * fullness' t V := by
  change
    (∑ i ∈ s, volume (V i).shade) / (∑ i ∈ s, volume (V i).carrier)
      ≤ C * ((∑ i ∈ t, volume (V i).shade) / (∑ i ∈ t, volume (V i).carrier))
  have hD : (∑ i ∈ t, volume (V i).carrier) ≤ ∑ i ∈ s, volume (V i).carrier := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hts (fun _ _ _ => zero_le)
  calc
    (∑ i ∈ s, volume (V i).shade) / (∑ i ∈ s, volume (V i).carrier)
        ≤ (C * ∑ i ∈ t, volume (V i).shade) / (∑ i ∈ t, volume (V i).carrier) := by
          exact ENNReal.div_le_div hmass hD
    _ = C * ((∑ i ∈ t, volume (V i).shade) / (∑ i ∈ t, volume (V i).carrier)) := by
          rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc]

/-- **Fullness times total carrier volume is total shade volume.** The defining quotient, cleared.

This is how the Section 6 fullness hypothesis becomes the shade *mass* that
`Plank.sum_shade_le_of_multiplicity_le` consumes: a lower bound on `fullness'` plus the exact total
carrier volume of the family gives a lower bound on `∑ |shade|`. -/
theorem sum_shade_eq_fullness'_mul {E : Type*} [TopologicalSpace E]
    [Convexity.ConvexSpace ℝ E] [MeasureSpace E] {ι : Type*} (s : Finset ι)
    (V : ι → ShadedBody E) (h0 : ∑ i ∈ s, volume (V i).carrier ≠ 0)
    (htop : ∑ i ∈ s, volume (V i).carrier ≠ ⊤) :
    ∑ i ∈ s, volume (V i).shade
      = fullness' s V * ∑ i ∈ s, volume (V i).carrier := by
  change ∑ i ∈ s, volume (V i).shade
    = ((∑ i ∈ s, volume (V i).shade) / (∑ i ∈ s, volume (V i).carrier))
      * ∑ i ∈ s, volume (V i).carrier
  rw [ENNReal.div_mul_cancel h0 htop]

end ShadedBody

namespace Plank

variable {θ b : ℝ≥0} {hθ1 : θ ≤ 1} {hb1 : b ≤ 1}

/-- Transfer of a real-valued weight comparison to `ENNReal`, for finite weights. -/
private theorem sum_le_of_toReal_sum_le {ι : Type*} (s t : Finset ι) (f : ι → ENNReal)
    (hts : t ⊆ s) (hfin : ∀ i ∈ s, f i ≠ ⊤) {M : ℕ}
    (h : (∑ i ∈ s, (f i).toReal) ≤ ((M : ℝ) + 1) * ∑ i ∈ t, (f i).toReal) :
    (∑ i ∈ s, f i) ≤ ((M : ENNReal) + 1) * ∑ i ∈ t, f i := by
  have hTfin : (∑ i ∈ t, f i) ≠ ⊤ := by
    exact (ENNReal.sum_ne_top).mpr (fun i hi => hfin i (hts hi))
  have hSfin : (∑ i ∈ s, f i) ≠ ⊤ := by
    exact (ENNReal.sum_ne_top).mpr hfin
  have hSreal : (∑ i ∈ s, f i).toReal = ∑ i ∈ s, (f i).toReal :=
    ENNReal.toReal_sum hfin
  have hTreal : (∑ i ∈ t, f i).toReal = ∑ i ∈ t, (f i).toReal :=
    ENNReal.toReal_sum (fun i hi => hfin i (hts hi))
  have hfactor : ((M : ENNReal) + 1).toReal = (M : ℝ) + 1 := by
    simp [ENNReal.toReal_add]
  have hprodfin : ((M : ENNReal) + 1) * (∑ i ∈ t, f i) ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by simp) hTfin
  rw [← ENNReal.toReal_le_toReal hSfin hprodfin]
  rw [hSreal, ENNReal.toReal_mul, hfactor, hTreal]
  exact h

/-- The shade volumes of the normalised tubes are the Jacobian multiple of the shade volumes of the
fibre's own shading bodies, summed over any subset of the fibre. -/
theorem sum_volume_shade_slabFibreTubes {fibre : Finset (ThickenedPlank θ b hθ1 hb1)}
    {Yθ : ThickenedPlank θ b hθ1 hb1 → ShadedBody (EuclideanSpace ℝ (Fin 3))}
    {S : Slab θ hθ1} {Cfib : ℝ≥0} (h : SlabFibreGeometry fibre Yθ S Cfib) (hCfib : 1 ≤ Cfib)
    (hθ0 : 0 < θ) {t : Finset (ThickenedPlank θ b hθ1 hb1)} (hts : t ⊆ fibre) :
    ∑ Q ∈ t, volume (slabFibreTubes Cfib fibre Yθ S hθ0 Q).shade
      = Kakeya.affineJacobian (slabFibreNormalisation Cfib S hθ0)
          * ∑ Q ∈ t, volume (Yθ Q).shade := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun Q hQ => ?_
  rw [slabFibreTubes_shade h hCfib hθ0 (hts hQ), Kakeya.volume_image_affineEquiv]

/-- **The pairwise essentially distinct sub-fibre, with its two retention bounds.**

For a fixed slab-fibre loss `Cfib ≥ 1` there is an absolute `MED : ℕ` such that every slab fibre
with the geometry of `Plank.SlabFibreGeometry` has a subfamily `sub ⊆ fibre` whose normalised
`b/8`-tubes are *genuinely* pairwise essentially distinct — the hypothesis of
`Kakeya.FrostmanEstimate.multiplicity_bound` — and which retains both the shade mass and the
fullness up to the single absolute factor `MED + 1`.

`MED` is the multiplicity of `Plank.exists_isEDUpToMult_slabTube`: it depends only on `Cfib` and on
the dimensional constants, not on `a`, `b`, `θ`, the slab, or the cardinality of the fibre. -/
theorem exists_pairwiseED_subfibre_package (Cfib : ℝ≥0) (hCfib : 1 ≤ Cfib) :
    ∃ MED : ℕ,
      ∀ {b : ℝ≥0} {hb1 : b ≤ 1} {θ : ℝ≥0} {hθ1 : θ ≤ 1}
        (fibre : Finset (ThickenedPlank θ b hθ1 hb1))
        (Yθ : ThickenedPlank θ b hθ1 hb1 → ShadedBody (EuclideanSpace ℝ (Fin 3)))
        (S : Slab θ hθ1) (hb0 : 0 < b) (hθ0 : 0 < θ),
        SlabFibreGeometry fibre Yθ S Cfib →
        ∃ sub : Finset (ThickenedPlank θ b hθ1 hb1), sub ⊆ fibre ∧
          (↑sub : Set (ThickenedPlank θ b hθ1 hb1)).Pairwise
            (fun Q Q' => _root_.IsEssentiallyDistinct
              ((slabFibreTubes Cfib fibre Yθ S hθ0 Q).carrier :
                Set (EuclideanSpace ℝ (Fin 3)))
              ((slabFibreTubes Cfib fibre Yθ S hθ0 Q').carrier :
                Set (EuclideanSpace ℝ (Fin 3)))) ∧
          (∑ Q ∈ fibre, volume (Yθ Q).shade)
            ≤ ((MED : ENNReal) + 1) * ∑ Q ∈ sub, volume (Yθ Q).shade ∧
          ShadedBody.fullness' fibre
              (fun Q => (slabFibreTubes Cfib fibre Yθ S hθ0 Q).toShadedBody)
            ≤ ((MED : ENNReal) + 1) * ShadedBody.fullness' sub
              (fun Q => (slabFibreTubes Cfib fibre Yθ S hθ0 Q).toShadedBody) := by
  obtain ⟨MED, hMED⟩ := exists_isEDUpToMult_slabTube Cfib hCfib
  refine ⟨MED, ?_⟩
  intro b hb1 θ hθ1 fibre Yθ S hb0 hθ0 h
  classical
  -- finiteness of the shade volumes
  have hfin : ∀ Q ∈ fibre, volume (Yθ Q).shade ≠ ⊤ := fun Q _ =>
    ne_top_of_le_ne_top ((Yθ Q).isCompact.measure_ne_top) (measure_mono (Yθ Q).shade_subset)
  -- the ED-up-to-multiplicity input
  have hED := hMED hθ0 hb0 fibre Yθ S h
  obtain ⟨sub, hsub, hpair, hwt⟩ :=
    hED.exists_pairwise_subset_with_weight (fun Q => (volume (Yθ Q).shade).toReal)
      (fun Q _ => ENNReal.toReal_nonneg)
  refine ⟨sub, hsub, ?_, ?_, ?_⟩
  · -- pairwise ED, rewritten onto `slabFibreTubes`
    intro Q hQ Q' hQ' hne
    rw [slabFibreTubes_carrier hθ0 (hsub hQ), slabFibreTubes_carrier hθ0 (hsub hQ')]
    exact hpair hQ hQ' hne
  · -- mass retention in ENNReal
    exact sum_le_of_toReal_sum_le fibre sub (fun Q => volume (Yθ Q).shade) hsub hfin hwt
  · -- fullness retention
    refine ShadedBody.fullness'_le_of_subset_of_sum_shade_le fibre sub _ hsub ?_
    rw [sum_volume_shade_slabFibreTubes h hCfib hθ0 (Finset.Subset.refl fibre),
      sum_volume_shade_slabFibreTubes h hCfib hθ0 hsub]
    -- goal: J * ∑_fibre ≤ (MED+1) * (J * ∑_sub)
    have hmass := sum_le_of_toReal_sum_le fibre sub (fun Q => volume (Yθ Q).shade) hsub hfin hwt
    calc _ ≤ Kakeya.affineJacobian (slabFibreNormalisation Cfib S hθ0) *
            (((MED : ENNReal) + 1) * ∑ Q ∈ sub, volume (Yθ Q).shade) := by gcongr
      _ = ((MED : ENNReal) + 1) * (Kakeya.affineJacobian (slabFibreNormalisation Cfib S hθ0) *
            ∑ Q ∈ sub, volume (Yθ Q).shade) := by ring

/-- **Pulling a union-volume lower bound back from the extracted subfamily to the fibre.**

The shade union of any sub-fibre's tubes is contained in the shade union of the whole fibre's
tubes, which is the exact affine image of the fibre's own shade union
(`Plank.slabFibreTubes_volume_iUnion_shade`). So a lower bound for
`volume (⋃_{sub} (T Q).shade)` — which is what GWZ Lemma 3.9 produces, through
`ShadedBody.multiplicity` — divides by the Jacobian into a lower bound for
`volume (⋃_{fibre} (Yθ Q).shade)`, the quantity
`Plank.frostmanSlabUnionVolumeLowerBound` is about. -/
theorem volume_iUnion_shade_sub_le {fibre : Finset (ThickenedPlank θ b hθ1 hb1)}
    {Yθ : ThickenedPlank θ b hθ1 hb1 → ShadedBody (EuclideanSpace ℝ (Fin 3))}
    {S : Slab θ hθ1} {Cfib : ℝ≥0} (h : SlabFibreGeometry fibre Yθ S Cfib) (hCfib : 1 ≤ Cfib)
    (hθ0 : 0 < θ) {sub : Finset (ThickenedPlank θ b hθ1 hb1)} (hsub : sub ⊆ fibre) :
    volume (⋃ Q ∈ sub, (slabFibreTubes Cfib fibre Yθ S hθ0 Q).shade)
      ≤ Kakeya.affineJacobian (slabFibreNormalisation Cfib S hθ0)
          * volume (⋃ Q ∈ fibre, (Yθ Q).shade) := by
  calc volume (⋃ Q ∈ sub, (slabFibreTubes Cfib fibre Yθ S hθ0 Q).shade)
      ≤ volume (⋃ Q ∈ fibre, (slabFibreTubes Cfib fibre Yθ S hθ0 Q).shade) := by
        refine measure_mono ?_
        exact Set.iUnion₂_subset fun Q hQ =>
          Set.subset_biUnion_of_mem (u := fun Q => (slabFibreTubes Cfib fibre Yθ S hθ0 Q).shade)
            (hsub hQ)
    _ = Kakeya.affineJacobian (slabFibreNormalisation Cfib S hθ0) *
          volume (⋃ Q ∈ fibre, (Yθ Q).shade) :=
        slabFibreTubes_volume_iUnion_shade h hCfib hθ0

/-- **From a multiplicity upper bound on the extracted tube subfamily to a union-volume lower bound
on the original fibre — with the affine Jacobian cancelling.**

This is the whole of steps 2 and 3 of the per-slab argument in one statement, and the point is that
no Jacobian survives. Writing `J` for `Kakeya.affineJacobian (slabFibreNormalisation Cfib S hθ0)`:

* `∑_{sub} |T Q| = multiplicity(sub, T) · |⋃_{sub} (T Q).shade|`
  (`ShadedBody.multiplicity_mul_union`, an identity, not an inequality);
* `|⋃_{sub} (T Q).shade| ≤ J · |⋃_{fibre} (Yθ Q).shade|`
  (`Plank.volume_iUnion_shade_sub_le`, which uses the *exact* affine union-volume identity of
  `Plank.normaliseSlabFamilyToTubes`);
* `∑_{sub} |T Q| = J · ∑_{sub} |Yθ Q|` (`Plank.sum_volume_shade_slabFibreTubes`).

Combining and cancelling the single factor `J` on both sides leaves a statement with no
normalisation constants at all. The weighted shade-mass retention `M` from
`Plank.exists_pairwiseED_subfibre_package` is then the only extraction loss — in particular the
comparison between the sub-fibre union and the full union is *never* made through cardinality. -/
theorem sum_shade_le_of_multiplicity_le {fibre : Finset (ThickenedPlank θ b hθ1 hb1)}
    {Yθ : ThickenedPlank θ b hθ1 hb1 → ShadedBody (EuclideanSpace ℝ (Fin 3))}
    {S : Slab θ hθ1} {Cfib : ℝ≥0} (h : SlabFibreGeometry fibre Yθ S Cfib) (hCfib : 1 ≤ Cfib)
    (hθ0 : 0 < θ) {sub : Finset (ThickenedPlank θ b hθ1 hb1)} (hsub : sub ⊆ fibre)
    {M B : ENNReal}
    (hmass : (∑ Q ∈ fibre, volume (Yθ Q).shade) ≤ M * ∑ Q ∈ sub, volume (Yθ Q).shade)
    (hmult : ShadedBody.multiplicity sub
        (fun Q => (slabFibreTubes Cfib fibre Yθ S hθ0 Q).toShadedBody) ≤ B) :
    (∑ Q ∈ fibre, volume (Yθ Q).shade)
      ≤ M * B * volume (⋃ Q ∈ fibre, (Yθ Q).shade) := by
  have hJ : Kakeya.affineJacobian (slabFibreNormalisation Cfib S hθ0) ≠ 0 :=
    Kakeya.affineJacobian_ne_zero _
  have hJtop : Kakeya.affineJacobian (slabFibreNormalisation Cfib S hθ0) ≠ ⊤ :=
    Kakeya.affineJacobian_ne_top _
  have hid := ShadedBody.multiplicity_mul_union sub
    (fun Q => (slabFibreTubes Cfib fibre Yθ S hθ0 Q).toShadedBody)
  have hstep : (∑ Q ∈ sub, volume (slabFibreTubes Cfib fibre Yθ S hθ0 Q).shade)
      ≤ B * (Kakeya.affineJacobian (slabFibreNormalisation Cfib S hθ0)
          * volume (⋃ Q ∈ fibre, (Yθ Q).shade)) := by
    rw [← hid]
    exact mul_le_mul' hmult (volume_iUnion_shade_sub_le h hCfib hθ0 hsub)
  rw [sum_volume_shade_slabFibreTubes h hCfib hθ0 hsub] at hstep
  have hcancel : (∑ Q ∈ sub, volume (Yθ Q).shade)
      ≤ B * volume (⋃ Q ∈ fibre, (Yθ Q).shade) := by
    have hcom :
        (∑ Q ∈ sub, volume (Yθ Q).shade) *
            Kakeya.affineJacobian (slabFibreNormalisation Cfib S hθ0)
          ≤ (B * volume (⋃ Q ∈ fibre, (Yθ Q).shade)) *
            Kakeya.affineJacobian (slabFibreNormalisation Cfib S hθ0) := by
      calc
        (∑ Q ∈ sub, volume (Yθ Q).shade) *
            Kakeya.affineJacobian (slabFibreNormalisation Cfib S hθ0)
            = Kakeya.affineJacobian (slabFibreNormalisation Cfib S hθ0) *
                (∑ Q ∈ sub, volume (Yθ Q).shade) := by
              ac_rfl
        _ ≤ B * (Kakeya.affineJacobian (slabFibreNormalisation Cfib S hθ0) *
            volume (⋃ Q ∈ fibre, (Yθ Q).shade)) := hstep
        _ = (B * volume (⋃ Q ∈ fibre, (Yθ Q).shade)) *
            Kakeya.affineJacobian (slabFibreNormalisation Cfib S hθ0) := by
              ac_rfl
    exact (ENNReal.mul_le_mul_iff_left hJ hJtop).mp hcom
  calc
    (∑ Q ∈ fibre, volume (Yθ Q).shade)
        ≤ M * (∑ Q ∈ sub, volume (Yθ Q).shade) := hmass
    _ ≤ M * (B * volume (⋃ Q ∈ fibre, (Yθ Q).shade)) := by
      exact mul_le_mul' (le_rfl : M ≤ M) hcancel
    _ = M * B * volume (⋃ Q ∈ fibre, (Yθ Q).shade) := by
      ac_rfl

end Plank

end
