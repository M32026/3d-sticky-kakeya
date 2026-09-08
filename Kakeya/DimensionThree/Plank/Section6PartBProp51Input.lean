/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.Section6FactorInterface
public import Kakeya.DimensionThree.Plank.Section6PartBProp51
public import Kakeya.Tube.Basic
public import Kakeya.CThickening

/-!
# The Proposition-5.1 *input* of GWZ Part (B), constructed

`Kakeya.Section6PartBData.prop51CoreAtScaleOfRemark53` and its scale-selecting sibling
`Kakeya.Section6PartBData.prop51CoreSelectScaleOfRemark53` are the tree's unconditional
Proposition 5.1 for the Part-(B) fine family.  They take two inputs:

* `ShadedBody.Section6FactoringAtScaleInput D.toFineProp51Family δ w₁` (or its `SelectScale`
  variant), the geometric/scale data; and
* `D.toFineProp51Family.HasThickenedFrostmanFibers CF`, GWZ Remark 5.3's Frostman datum.

This file constructs the **first** of the two from the Part-(B) datum together with the two
hypotheses Proposition 6.6(B) already carries (`(T i).carrier ⊆ B₁` and positive shading mass).
Nothing here is assumed: every field is discharged.

## What each field costs

| field | source |
|---|---|
| `hdisc` | `Tube.le_ethickness_scale` plus the unit-ball hypothesis of 6.6(B) |
| `volumeRatio` | outer bodies sit in `B(0, plankWindowRadius)` via `body_le_repr` + `repr_window`; inner bodies have volume `≥ c₃ δ³` by discretization |
| `hupper` | `Kakeya.Prism3D.ethickness_two_le`: a cell body lies in an `a × b × 1` plank, so its shortest thickness is at most `a` |
| `hmass` | hypothesis (in 6.6(B) it follows from `δ ^ η ≤ λ(𝒯, Y)`) |
| `hdim` | `finrank_euclideanSpace_fin` |
| `hshape` | `Kakeya.Section6PartBData.innerHasSimilarShape` |

The remaining Proposition-5.1 obligation is therefore exactly
`HasThickenedFrostmanFibers`, which is the genuinely mathematical Remark-5.3 leaf.
-/

@[expose] public section

open MeasureTheory Convexity
open scoped NNReal ENNReal Classical

noncomputable section

/-! ## A doubling estimate for closed neighbourhoods -/

namespace ConvexSpaceBody

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-- **Two doublings.**  `Kakeya`'s `ConvexSpaceBody.volume_cthickening_le` inflates the volume by
the dimensional constant only for radii below the body's own scale.  Taking the collar in two
equal steps extends it to radii up to *twice* the scale, at the square of the constant: the
intermediate body `K + B_r` has scale `r + scale K`, so the second step is again admissible. -/
theorem volume_cthickening_two_le (K : ConvexSpaceBody E) (r : ℝ≥0) (hr : (r : ℝ) ≤ K.scale) :
    volume (K.cthickening ((2 * r : ℝ≥0) : ℝ)).carrier
      ≤ ((Metric.volume_comparison.C (Module.finrank ℝ E) : ENNReal)) ^ 2
        * volume K.carrier := by
  have hsplit : (K.cthickening ((2 * r : ℝ≥0) : ℝ)).carrier
      = ((K.cthickening (r : ℝ)).cthickening (r : ℝ)).carrier := by
    show Metric.cthickening ((2 * r : ℝ≥0) : ℝ) K.carrier
      = Metric.cthickening (r : ℝ) (Metric.cthickening (r : ℝ) K.carrier)
    rw [cthickening_cthickening r.coe_nonneg r.coe_nonneg]
    congr 1
    push_cast
    ring
  have hr2 : (r : ℝ) ≤ (K.cthickening (r : ℝ)).scale := by
    refine hr.trans ?_
    exact Metric.thickness_monotone (K.cthickening (r : ℝ)).isCompact'.isBounded
      (Metric.self_subset_cthickening _) _
  calc volume (K.cthickening ((2 * r : ℝ≥0) : ℝ)).carrier
      = volume ((K.cthickening (r : ℝ)).cthickening (r : ℝ)).carrier := by rw [hsplit]
    _ ≤ (Metric.volume_comparison.C (Module.finrank ℝ E) : ENNReal)
          * volume (K.cthickening (r : ℝ)).carrier :=
        volume_cthickening_le (K.cthickening (r : ℝ)) r hr2
    _ ≤ (Metric.volume_comparison.C (Module.finrank ℝ E) : ENNReal)
          * ((Metric.volume_comparison.C (Module.finrank ℝ E) : ENNReal) * volume K.carrier) := by
        gcongr
        exact volume_cthickening_le K r hr
    _ = ((Metric.volume_comparison.C (Module.finrank ℝ E) : ENNReal)) ^ 2 * volume K.carrier := by
        rw [← mul_assoc, sq]

end ConvexSpaceBody

namespace Kakeya

/-! ## The real-valued scale of a tube -/

namespace Tube

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] {δ' : ℝ≥0}

/-- **A `δ`-tube has real-valued scale at least `δ`.**  The `ℝ`-valued sibling of
`Tube.le_ethickness_scale`. -/
theorem le_scale (T : Tube δ' E) : (δ' : ℝ) ≤ T.toConvexSpaceBody.scale := by
  have hb : Bornology.IsBounded (T.carrier) := T.isCompact.isBounded
  have h := T.le_ethickness_scale
  rw [Metric.ethickness.scale_eq] at h
  rw [Metric.ethickness_thickness' (𝕜 := ℝ) hb (Module.finrank ℝ E - 1)] at h
  rw [show ((δ' : ℝ≥0) : ENNReal) = ENNReal.ofReal (δ' : ℝ) by
    simp [ENNReal.ofReal_coe_nnreal]] at h
  have := (ENNReal.ofReal_le_ofReal_iff (Metric.thickness_nonneg _ _)).mp h
  exact this

end Tube



namespace Section6PartBData

variable {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
  {ι : Type*} {q : Finset ι} {δ : ℝ≥0} {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
  {κ : Type*} {coarseSet : Finset κ} {ρ : ℝ≥0} {R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))}
  {m Cfib CF C₀ : ℝ≥0}
  (D : Section6PartBData a b hab hb1 q T coarseSet R m Cfib CF C₀)

/-! ## The two views of the fine family agree -/

/-- `Kakeya.Section6PartBData.toFineProp51Family` and
`Kakeya.Section6PartBData.toFineFactorFamily` are the same family; they were introduced
independently in two sibling files. -/
theorem toFineProp51Family_eq_toFineFactorFamily :
    D.toFineProp51Family = D.toFineFactorFamily := rfl

@[simp] theorem toFineProp51Family_innerSet : D.toFineProp51Family.innerSet = q := rfl

@[simp] theorem toFineProp51Family_outerSet :
    D.toFineProp51Family.outerSet = D.factor.cells := rfl

@[simp] theorem toFineProp51Family_outerBody :
    D.toFineProp51Family.outerBody = D.factor.body := rfl

@[simp] theorem toFineProp51Family_parent : D.toFineProp51Family.parent = D.cellOfFine := rfl

theorem toFineProp51Family_fiber (x : D.factor.Cell) :
    D.toFineProp51Family.fiber x = D.fineFibre x := rfl

theorem toFineProp51Family_innerBody_toConvexSpaceBody (i : ι) :
    (D.toFineProp51Family.innerBody i).toConvexSpaceBody = (T i).toConvexSpaceBody := rfl

/-! ## `hdisc`: the fine family is discretized at the master scale -/

/-- **The inner discretization datum.**  A `δ`-tube has shortest affine thickness at least `δ`
(`Tube.le_ethickness_scale`); the unit-ball containment is Proposition 6.6(B)'s own
hypothesis on the fine family. -/
theorem innerIsDiscretizedAtScale
    (hball : ∀ i ∈ q, ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ Metric.closedBall 0 1) :
    D.toFineProp51Family.InnerIsDiscretizedAtScale δ where
  subset_unitBall := hball
  le_scale := fun i _ => Tube.le_ethickness_scale (T i).toTube

/-! ## `hupper`: the cell bodies have shortest thickness at most the thin half-width -/

/-- **A cell body is at most `a`-thin.**  It lies in its representative `a × b × 1` plank, whose
rank-`2` `ethickness` is at most `a` (`Kakeya.Prism3D.ethickness_two_le`). -/
theorem ethickness_two_body_le {x : D.factor.Cell} (hx : x ∈ D.factor.cells) :
    Metric.ethickness ℝ (D.factor.body x).carrier 2 ≤ (a : ENNReal) := by
  refine le_trans ?_ (Prism3D.ethickness_two_le (D.factor.repr x))
  exact Metric.ethickness_monotone
    (SetLike.coe_subset_coe.mpr (D.factor.body_le_repr x hx)) 2

/-- **The rank-`2` real thickness of a `Prism3D` is at most its smallest half-width.**
The `ℝ`-valued sibling of `Kakeya.Prism3D.ethickness_two_le`, with the same proof. -/
theorem _root_.Kakeya.Prism3D.thickness_two_le {a' b' c' : ℝ≥0} {ha'b' : a' ≤ b'} {hb'c' : b' ≤ c'}
    (P : Prism3D a' b' c' ha'b' hb'c') :
    Metric.thickness ℝ (P.carrier : Set (EuclideanSpace ℝ (Fin 3))) 2 ≤ (a' : ℝ) := by
  refine Metric.thickness_le_of_cthickening (r := (a' : ℝ)) a'.coe_nonneg
    (A := P.tangentPlane) ?_ ?_
  · rw [AffineSubspace.direction_mk']
    rw [← Module.finrank_eq_rank, P.finrank_longPlane]
  · exact P.carrier_subset_cthickening_tangentPlane

/-- **`hupper`: a cell body is at most `a`-thin.**  It lies in its representative `a × b × 1`
plank, whose rank-`2` thickness is at most `a`. -/
theorem body_scale_le {x : D.factor.Cell} (hx : x ∈ D.factor.cells) :
    (D.factor.body x).scale ≤ (a : ℝ) := by
  have hmono : Metric.thickness ℝ ((D.factor.body x).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ≤ Metric.thickness ℝ ((D.factor.repr x).carrier : Set (EuclideanSpace ℝ (Fin 3))) :=
    Metric.thickness_monotone (D.factor.repr x).isCompact.isBounded
      (SetLike.coe_subset_coe.mpr (D.factor.body_le_repr x hx))
  calc (D.factor.body x).scale
      = Metric.thickness ℝ ((D.factor.body x).carrier : Set (EuclideanSpace ℝ (Fin 3))) 2 := by
        simp [ConvexSpaceBody.scale]
    _ ≤ Metric.thickness ℝ ((D.factor.repr x).carrier : Set (EuclideanSpace ℝ (Fin 3))) 2 :=
        hmono 2
    _ ≤ (a : ℝ) := Prism3D.thickness_two_le (D.factor.repr x)


/-! ## `volumeRatio`: the outer/inner carrier-volume ratio -/

/-- Every cell body lies in the Section-6 working window `B(0, 4)`. -/
theorem body_carrier_subset_window {x : D.factor.Cell} (hx : x ∈ D.factor.cells) :
    ((D.factor.body x).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ Metric.closedBall 0 (plankWindowRadius : ℝ) :=
  subset_trans (SetLike.coe_subset_coe.mpr (D.factor.body_le_repr x hx))
    (D.factor.repr_window x hx)

open Classical in
/-- **The outer/inner volume-ratio datum for the Part-(B) fine family.**

The outer bound is the volume of the working window `B(0, plankWindowRadius)`, which every cell
body meets by `Kakeya.Section6PartBData.body_carrier_subset_window`.  The inner bound is the
discretization bound `c₃ · δ³` of `Kakeya.Tube`-sized bodies.  The exponent produced is the binary
ceiling of the ratio; it is *logarithmic* in `1/δ`, which is what
`Kakeya.PartBLoss.fineVolumeRatio_exponent_spec`
(`Kakeya/DimensionThree/Plank/PartBVolumeRatioExponent.lean`) records.

Until steps  this sentence cited `Kakeya.Section6PartBData.fineVolumeRatio_exponent_spec`,
which never existed and could not have: the exponent was opaque to every `module` file, because
`ShadedBody.OuterInnerVolumeRatio.ofFiniteVolumeBounds` lacked `@[expose]` (its sibling
`ofVolumeBounds` had it).  With that attribute added the claim is now a theorem. -/
def fineVolumeRatio (hδ0 : 0 < δ)
    (hball : ∀ i ∈ q, ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ Metric.closedBall 0 1) :
    ShadedBody.OuterInnerVolumeRatio D.toFineProp51Family := by
  classical
  refine ShadedBody.OuterInnerVolumeRatio.ofFiniteVolumeBounds D.toFineProp51Family
    (volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (plankWindowRadius : ℝ)))
    ((Metric.lt_volume_convexHull.c 3 : ENNReal) * (δ : ENNReal) ^ 3)
    ?_ ?_ (measure_closedBall_lt_top).ne ?_ ?_
  · intro j hj
    exact measure_mono (D.body_carrier_subset_window hj)
  · intro j _ i hi
    have hiq : i ∈ q := (Finset.mem_filter.mp hi).1
    have := (D.innerIsDiscretizedAtScale hball).volume_innerBody_mem_Icc hiq
    simpa [finrank_euclideanSpace_fin] using this.1
  · refine zero_lt_iff.mpr (mul_ne_zero ?_ ?_)
    · exact ENNReal.coe_ne_zero.mpr (Metric.lt_volume_convexHull.c_pos 3).ne'
    · exact pow_ne_zero 3 (ENNReal.coe_ne_zero.mpr hδ0.ne')
  · exact ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)

/-! ## The complete Proposition-5.1 input -/

open Classical in
/-- **GWZ Proposition 5.1's geometric input for Part (B), constructed.**

Every field is discharged from the Part-(B) datum plus the three hypotheses Proposition 6.6(B)
already carries: `0 < δ`, the unit-ball containment of the fine tubes, and positive fine shading
mass.  `B` is any common upper bound for `δ` and the thin half-width `a`; in 6.6(B) one may take
`B := a`, since `δ ≤ ρ ≤ a`.

This is one of the two inputs of `Kakeya.Section6PartBData.prop51CoreSelectScaleOfRemark53`.
The other, `HasThickenedFrostmanFibers`, is the Remark-5.3 leaf. -/
def section6SelectScaleInput (hδ0 : 0 < δ) (hδhalf : (δ : ℝ) ≤ 1 / 2) {B : ℝ≥0}
    (hδB : δ ≤ B) (haB : a ≤ B)
    (hball : ∀ i ∈ q, ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ Metric.closedBall 0 1)
    (hmass : 0 < ∑ i ∈ q, volume (T i).shade) :
    ShadedBody.Section6FactoringSelectScaleInput D.toFineProp51Family δ B where
  hδ := hδ0
  hdisc := D.innerIsDiscretizedAtScale hball
  volumeRatio := D.fineVolumeRatio hδ0 hball
  hδB := hδB
  hupper := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact le_trans (D.body_scale_le (D.factor.cellOf_mem _ (D.decomp.assign_mem i hi)))
      (by exact_mod_cast haB)
  hmass := hmass
  hdim := by simp
  hshape := D.innerHasSimilarShape hδhalf


/-! ## `HasThickenedFrostmanFibers`: GWZ Remark 5.3, constructed -/

/-- **The effective constant of the constructed Remark-5.3 datum.**

`Cfib² · ratio · CF` is the constant of `Kakeya.Section6PartBData.remark53_card_fine_le`; the second
`ratio` converts a count of thickened fine tubes into a volume, and `volume_comparison.C 3 ^ 2` is
the price of replacing the test body `K` by its `4ρ`-collar, which is where the coarse containers of
the counted fine tubes live. -/
def remark53ThickConst (Cfib CF : ℝ≥0) : ℝ≥0 :=
  Cfib ^ 2 * coarseTubeVolumeRatio ^ 2 * CF * Metric.volume_comparison.C 3 ^ 2

open Classical in
/-- **GWZ Remark 5.3 for Part (B), as Proposition 5.1 consumes it.**

`ShadedBody.FactorFamily.HasThickenedFrostmanFibers` for the Part-(B) fine family
`Kakeya.Section6PartBData.toFineProp51Family`.  Together with
`Kakeya.Section6PartBData.section6SelectScaleInput` this discharges *both* inputs of
`Kakeya.Section6PartBData.prop51CoreSelectScaleOfRemark53`, so the Proposition-5.1 output for
Part (B) becomes a theorem of the datum.

**The argument.**  Fix a cell `x`, write `W` for its actual body, `s = W.scale` and
`σ = δ + 2s`.  The thickened fine bodies are exactly the `σ`-rescales of the fine tubes
(`Tube.toConvexBody_cthickening_eq`), so they all have volume comparable to `σ²` and the statement
reduces to a *count*: for every convex test body `K`,

`#{i ∈ 𝒯_x : (T i)^{2s} ⊆ K} ≲ (|K| / |W|) · |𝒯_x|`.

A counted fine tube lies in `K`, so its coarse container lies in the `4ρ`-collar of `K`
(`Tube.rescale_le_of_le`, the absolute constant `4` of GWZ-note Lemma 3.1).  That collar has volume
at most `volume_comparison.C 3 ^ 2 · |K|`, because `K` contains a thickened fine tube and hence has
scale at least `σ ≥ 2ρ` — this is `Kakeya.ConvexSpaceBody.volume_cthickening_two_le`, and it is why
the collar has to be taken in two steps.  Replacing that collar by the convex hull of the counted
coarse tubes keeps it inside the representative plank, and
`Kakeya.Section6PartBData.remark53_card_fine_le` then gives the count from the *coarse* Frostman
datum alone.  No fine Frostman hypothesis is used anywhere, which is the whole point of Remark 5.3. -/
theorem hasThickenedFrostmanFibers
    (hδ0 : 0 < δ) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hsmall : δ + 2 * a ≤ 1)
    (hcfne : ∀ x ∈ D.factor.cells, (D.factor.coarseFibre x).Nonempty) :
    D.toFineProp51Family.HasThickenedFrostmanFibers
      ((remark53ThickConst Cfib CF : ℝ≥0) : ENNReal) := by
  classical
  intro x hx
  set W : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) := D.factor.body x with hWdef
  set P : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) := (D.factor.repr x).toConvexSpaceBody
    with hPdef
  set S : Finset ι := D.fineFibre x with hSdef
  have hscale_nonneg : (0 : ℝ) ≤ W.scale := Metric.thickness_nonneg _ _
  set sN : ℝ≥0 := Real.toNNReal W.scale with hsNdef
  have hsNr : (sN : ℝ) = W.scale := Real.coe_toNNReal _ hscale_nonneg
  set σ : ℝ≥0 := δ + 2 * sN with hσdef
  set V : ι → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) :=
    fun i => (T i).toConvexSpaceBody.cthickening (2 * W.scale) with hVdef
  have hVeq : ∀ i, V i = ((T i).toTube.rescale σ).toConvexSpaceBody := by
    intro i
    have h2 : (2 * W.scale) = ((2 * sN : ℝ≥0) : ℝ) := by
      rw [NNReal.coe_mul, hsNr]; norm_num
    show (T i).toConvexSpaceBody.cthickening (2 * W.scale) = _
    rw [h2]
    exact Tube.toConvexBody_cthickening_eq (T i).toTube (2 * sN)
  obtain ⟨k₀, hk₀⟩ := hcfne x hx
  have hk₀mem := D.factor.mem_coarseFibre_iff.mp hk₀
  have hRk₀ : (R k₀).toConvexSpaceBody ≤ W := by
    rw [hWdef, ← hk₀mem.2]
    exact D.factor.le_body k₀ hk₀mem.1
  have hρsN : (ρ : ℝ) ≤ (sN : ℝ) := by
    rw [hsNr]
    refine le_trans (Tube.le_scale (R k₀)) ?_
    exact Metric.thickness_monotone W.isCompact'.isBounded
      (SetLike.coe_subset_coe.mpr hRk₀) _
  have hsNa : sN ≤ a := by
    have hle : (sN : ℝ) ≤ (a : ℝ) := by rw [hsNr]; exact D.body_scale_le hx
    exact_mod_cast hle
  have hσρ : 2 * ρ ≤ σ := by
    have hρsN' : ρ ≤ sN := by exact_mod_cast hρsN
    rw [hσdef]
    calc 2 * ρ ≤ 2 * sN := by gcongr
      _ ≤ δ + 2 * sN := le_add_self
  have hσ1 : σ ≤ 1 := by
    rw [hσdef]
    calc δ + 2 * sN ≤ δ + 2 * a := by gcongr
      _ ≤ 1 := hsmall
  set c3 : ENNReal := ((Tube.le_volume.c 3 : ℝ≥0) : ENNReal) * (σ : ENNReal) ^ 2 with hc3def
  have hVlow : ∀ i, c3 ≤ volume (V i).carrier := by
    intro i
    rw [hVeq i]
    exact (Tube.volume_comparable_three hσ1 ((T i).toTube.rescale σ)).1
  have hVhigh : ∀ i, volume (V i).carrier ≤ (coarseTubeVolumeRatio : ENNReal) * c3 := by
    intro i
    rw [hVeq i]
    exact (Tube.volume_comparable_three hσ1 ((T i).toTube.rescale σ)).2
  have hWP : volume W.carrier ≤ volume P.carrier :=
    measure_mono (SetLike.coe_subset_coe.mpr (D.factor.body_le_repr x hx))
  have hWtop : volume W.carrier ≠ ⊤ := W.isCompact'.measure_ne_top
  have hPtop : volume P.carrier ≠ ⊤ := (D.factor.repr x).isCompact.measure_ne_top
  have hW0 : volume W.carrier ≠ 0 := by
    have hlow : ((Tube.le_volume.c 3 : ℝ≥0) : ENNReal) * (ρ : ENNReal) ^ 2
        ≤ volume (R k₀).carrier := (Tube.volume_comparable_three hρ1 (R k₀)).1
    have hpos : ((Tube.le_volume.c 3 : ℝ≥0) : ENNReal) * (ρ : ENNReal) ^ 2 ≠ 0 :=
      mul_ne_zero (ENNReal.coe_ne_zero.mpr (Tube.le_volume.c_pos 3).ne')
        (pow_ne_zero 2 (ENNReal.coe_ne_zero.mpr hρ0.ne'))
    have hmono : volume (R k₀).carrier ≤ volume W.carrier :=
      measure_mono (SetLike.coe_subset_coe.mpr hRk₀)
    intro h
    exact hpos (le_antisymm ((hlow.trans hmono).trans h.le) bot_le)
  have hP0 : volume P.carrier ≠ 0 := by
    intro h
    exact hW0 (le_antisymm (h ▸ hWP) bot_le)
  set Sg : ENNReal := ∑ i ∈ S, volume (V i).carrier with hSgdef
  have hSglow : c3 * (S.card : ENNReal) ≤ Sg := by
    rw [hSgdef, mul_comm]
    calc (S.card : ENNReal) * c3 = ∑ _i ∈ S, c3 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ S, volume (V i).carrier := Finset.sum_le_sum fun i _ => hVlow i
  have hkey : ∀ K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)),
      Kakeya.densityIn S V K * volume W.carrier
        ≤ ((remark53ThickConst Cfib CF : ℝ≥0) : ENNReal) * Sg := by
    intro K
    by_cases hK0 : volume K.carrier = 0
    · rw [Kakeya.densityIn_eq_zero_of_volume_eq_zero hK0]
      simp
    have hKtop : volume K.carrier ≠ ⊤ := K.isCompact'.measure_ne_top
    set qS : Finset ι := {i ∈ S | V i ≤ K} with hqSdef
    have hqSsub : qS ⊆ S := Finset.filter_subset _ _
    have hsumeq : Kakeya.densityIn S V K * volume K.carrier
        = ∑ i ∈ qS, volume (V i).carrier :=
      (Kakeya.sum_volume_eq_densityIn_mul_volume S V K).symm
    rcases qS.eq_empty_or_nonempty with hqe | hqne
    · have hz : Kakeya.densityIn S V K * volume K.carrier = 0 := by
        rw [hsumeq, hqe]; simp
      have hd0 : Kakeya.densityIn S V K = 0 := by
        rcases mul_eq_zero.mp hz with h | h
        · exact h
        · exact absurd h hK0
      rw [hd0]; simp
    obtain ⟨i₀, hi₀⟩ := hqne
    have hi₀K : V i₀ ≤ K := (Finset.mem_filter.mp hi₀).2
    have hKscale : ((2 * ρ : ℝ≥0) : ℝ) ≤ K.scale := by
      have h1 : (σ : ℝ) ≤ (V i₀).scale := by
        rw [hVeq i₀]; exact Tube.le_scale _
      have h2 : (V i₀).scale ≤ K.scale :=
        Metric.thickness_monotone K.isCompact'.isBounded
          (SetLike.coe_subset_coe.mpr hi₀K) _
      have h3 : ((2 * ρ : ℝ≥0) : ℝ) ≤ (σ : ℝ) := by exact_mod_cast hσρ
      linarith
    have hKbigvol : volume (K.cthickening ((2 * (2 * ρ) : ℝ≥0) : ℝ)).carrier
        ≤ ((Metric.volume_comparison.C 3 : ℝ≥0) : ENNReal) ^ 2 * volume K.carrier := by
      have h := ConvexSpaceBody.volume_cthickening_two_le K (2 * ρ) hKscale
      simpa [finrank_euclideanSpace_fin] using h
    have hcoarse : ∀ i ∈ qS,
        (R (D.decomp.assign i)).toConvexSpaceBody
          ≤ K.cthickening ((2 * (2 * ρ) : ℝ≥0) : ℝ) := by
      intro i hi
      have hiS : i ∈ S := hqSsub hi
      have hiq : i ∈ q := D.fineFibre_subset x hiS
      have hVK : V i ≤ K := (Finset.mem_filter.mp hi).2
      have hTK : (T i).toConvexSpaceBody ≤ K :=
        le_trans (ConvexSpaceBody.self_le_cthickening _ _) hVK
      have h1 : (R (D.decomp.assign i)).toConvexSpaceBody
          ≤ ((T i).toTube.rescale (4 * ρ)).toConvexSpaceBody :=
        Tube.rescale_le_of_le (T i).toTube (R (D.decomp.assign i))
          (D.decomp.leaf_le_parent i hiq)
      refine le_trans h1 ?_
      have h2 : ((T i).toTube.rescale (4 * ρ)).toConvexSpaceBody
          ≤ ((T i).toTube.rescale (δ + 4 * ρ)).toConvexSpaceBody :=
        Tube.rescale_le_rescale_of_radius_le _ le_add_self
      refine le_trans h2 ?_
      have h3 : ((T i).toTube.rescale (δ + 4 * ρ)).toConvexSpaceBody
          = (T i).toConvexSpaceBody.cthickening ((4 * ρ : ℝ≥0) : ℝ) :=
        (Tube.toConvexBody_cthickening_eq (T i).toTube (4 * ρ)).symm
      rw [h3]
      have hrad : ((2 * (2 * ρ) : ℝ≥0) : ℝ) = ((4 * ρ : ℝ≥0) : ℝ) := by
        push_cast; ring
      rw [hrad]
      intro z hz
      exact Metric.cthickening_subset_of_subset _ (SetLike.coe_subset_coe.mpr hTK) hz
    set Kh : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) :=
      Finset.convexHull_biUnion qS (fun i => (R (D.decomp.assign i)).toConvexSpaceBody)
      with hKhdef
    have hqne : qS.Nonempty := ⟨i₀, hi₀⟩
    have hKhP : Kh ≤ P := by
      rw [hKhdef]
      refine (Finset.Nonempty.convexHull_biUnion_le_iff hqne _ _).mpr ?_
      intro i hi
      have hiS : i ∈ S := hqSsub hi
      have hcell : D.decomp.assign i ∈ D.factor.coarseFibre x := D.assign_mem_coarseFibre hiS
      have hmem := D.factor.mem_coarseFibre_iff.mp hcell
      rw [hPdef, ← hmem.2]
      exact Section6PartBFactorisation.le_repr (F := D.factor) hmem.1
    have hKhbig : Kh ≤ K.cthickening ((2 * (2 * ρ) : ℝ≥0) : ℝ) := by
      rw [hKhdef]
      exact (Finset.Nonempty.convexHull_biUnion_le_iff hqne _ _).mpr hcoarse
    have hKhK : volume Kh.carrier
        ≤ ((Metric.volume_comparison.C 3 : ℝ≥0) : ENNReal) ^ 2 * volume K.carrier :=
      le_trans (measure_mono (SetLike.coe_subset_coe.mpr hKhbig)) hKbigvol
    have hmemKh : ∀ i ∈ qS, (R (D.decomp.assign i)).toConvexSpaceBody ≤ Kh := by
      intro i hi
      rw [hKhdef]
      exact Finset.le_convexHull_biUnion
        (fun i => (R (D.decomp.assign i)).toConvexSpaceBody) hi
    set θ : ℝ≥0 := (volume Kh.carrier / volume P.carrier).toNNReal with hθdef
    have hθe : ((θ : ℝ≥0) : ENNReal) = volume Kh.carrier / volume P.carrier := by
      rw [hθdef]
      exact ENNReal.coe_toNNReal (ENNReal.div_ne_top Kh.isCompact'.measure_ne_top hP0)
    have hθP : ((θ : ℝ≥0) : ENNReal) * volume P.carrier = volume Kh.carrier := by
      rw [hθe]
      exact ENNReal.div_mul_cancel hP0 hPtop
    have hcount := D.remark53_card_fine_le hρ0 hρ1 hx (hcfne x hx) hKhP hP0
      (θ := θ) (le_of_eq hθP.symm) hqSsub hmemKh
    have hcountE : (qS.card : ENNReal) * volume P.carrier
        ≤ ((Cfib ^ 2 * coarseTubeVolumeRatio * CF : ℝ≥0) : ENNReal) * volume Kh.carrier
          * (S.card : ENNReal) := by
      have h1 : ((qS.card : ℝ≥0) : ENNReal)
          ≤ ((Cfib ^ 2 * (coarseTubeVolumeRatio * CF * θ) * (S.card : ℝ≥0) : ℝ≥0) : ENNReal) :=
        ENNReal.coe_le_coe.mpr hcount
      calc (qS.card : ENNReal) * volume P.carrier
          ≤ ((Cfib ^ 2 * (coarseTubeVolumeRatio * CF * θ) * (S.card : ℝ≥0) : ℝ≥0) : ENNReal)
              * volume P.carrier := by
            gcongr
            simpa using h1
        _ = ((Cfib ^ 2 * coarseTubeVolumeRatio * CF : ℝ≥0) : ENNReal)
              * (((θ : ℝ≥0) : ENNReal) * volume P.carrier) * (S.card : ENNReal) := by
            push_cast
            ring
        _ = ((Cfib ^ 2 * coarseTubeVolumeRatio * CF : ℝ≥0) : ENNReal) * volume Kh.carrier
              * (S.card : ENNReal) := by rw [hθP]
    have hmain : volume K.carrier * (Kakeya.densityIn S V K * volume W.carrier)
        ≤ volume K.carrier * (((remark53ThickConst Cfib CF : ℝ≥0) : ENNReal) * Sg) := by
      have hstep : (∑ i ∈ qS, volume (V i).carrier) * volume W.carrier
          ≤ (((remark53ThickConst Cfib CF : ℝ≥0) : ENNReal) * Sg) * volume K.carrier := by
        calc (∑ i ∈ qS, volume (V i).carrier) * volume W.carrier
            ≤ ((qS.card : ENNReal) * ((coarseTubeVolumeRatio : ENNReal) * c3))
                * volume P.carrier := by
              gcongr
              calc (∑ i ∈ qS, volume (V i).carrier)
                  ≤ ∑ _i ∈ qS, (coarseTubeVolumeRatio : ENNReal) * c3 :=
                    Finset.sum_le_sum fun i _ => hVhigh i
                _ = (qS.card : ENNReal) * ((coarseTubeVolumeRatio : ENNReal) * c3) := by
                    rw [Finset.sum_const, nsmul_eq_mul]
          _ = ((coarseTubeVolumeRatio : ENNReal) * c3)
                * ((qS.card : ENNReal) * volume P.carrier) := by ring
          _ ≤ ((coarseTubeVolumeRatio : ENNReal) * c3)
                * (((Cfib ^ 2 * coarseTubeVolumeRatio * CF : ℝ≥0) : ENNReal) * volume Kh.carrier
                  * (S.card : ENNReal)) := by gcongr
          _ ≤ ((coarseTubeVolumeRatio : ENNReal) * c3)
                * (((Cfib ^ 2 * coarseTubeVolumeRatio * CF : ℝ≥0) : ENNReal)
                    * (((Metric.volume_comparison.C 3 : ℝ≥0) : ENNReal) ^ 2 * volume K.carrier)
                  * (S.card : ENNReal)) := by gcongr
          _ = ((remark53ThickConst Cfib CF : ℝ≥0) : ENNReal) * (c3 * (S.card : ENNReal))
                * volume K.carrier := by
              rw [remark53ThickConst]
              push_cast
              ring
          _ ≤ (((remark53ThickConst Cfib CF : ℝ≥0) : ENNReal) * Sg) * volume K.carrier := by
              gcongr
      calc volume K.carrier * (Kakeya.densityIn S V K * volume W.carrier)
          = (Kakeya.densityIn S V K * volume K.carrier) * volume W.carrier := by ring
        _ = (∑ i ∈ qS, volume (V i).carrier) * volume W.carrier := by rw [hsumeq]
        _ ≤ (((remark53ThickConst Cfib CF : ℝ≥0) : ENNReal) * Sg) * volume K.carrier := hstep
        _ = volume K.carrier * (((remark53ThickConst Cfib CF : ℝ≥0) : ENNReal) * Sg) := by ring
    exact (ENNReal.mul_le_mul_iff_right hK0 hKtop).mp hmain
  have hmax : Kakeya.maxDensity S V
      ≤ (((remark53ThickConst Cfib CF : ℝ≥0) : ENNReal) * Sg) / volume W.carrier := by
    rw [Kakeya.maxDensity_le_iff]
    intro K
    exact (ENNReal.le_div_iff_mul_le (Or.inl hW0) (Or.inl hWtop)).mpr (hkey K)
  show Kakeya.maxDensity S V * volume W.carrier
    ≤ ((remark53ThickConst Cfib CF : ℝ≥0) : ENNReal) * Sg
  calc Kakeya.maxDensity S V * volume W.carrier
      ≤ ((((remark53ThickConst Cfib CF : ℝ≥0) : ENNReal) * Sg) / volume W.carrier)
          * volume W.carrier := by gcongr
    _ = ((remark53ThickConst Cfib CF : ℝ≥0) : ENNReal) * Sg :=
        ENNReal.div_mul_cancel hW0 hWtop


/-! ## The Proposition-5.1 output for Part (B), unconditionally -/

open Classical in
/-- **GWZ Proposition 5.1 for the Part-(B) fine family, from the datum alone.**

Both inputs of `ShadedBody.section6GlobalFactorisationSelectScale` are now theorems of the
Part-(B) datum: the geometric/scale package is
`Kakeya.Section6PartBData.section6SelectScaleInput` and the Remark-5.3 Frostman datum is
`Kakeya.Section6PartBData.hasThickenedFrostmanFibers`.  So the *constructed* Proposition-5.1
output — the thick outer family `ShadedBody.outerThickFamilyAtScale` over the selected outer
scale, together with its refinement, aggregate fullness, constant inner multiplicity and
multiplicity split — is available for Part (B) with **no** `Kakeya.Section6PartBData.Remark53Prop51`
hypothesis anywhere.

This is what supersedes `Kakeya.tubeMultiplicityOfGlobalPlankFactorisation_of_partBData`: that
theorem consumes `Remark53Prop51`, which asserts the Proposition-5.1 items of the *unrefined*
families `Kakeya.Section6PartBData.fineOutput` (whose `innerSet` is `q` and whose `outerSet` is all
of `D.factor.cells`) with a constant fixed before the configuration.  Here the same items hold for
the family the construction actually produces.

The hypotheses are exactly those Proposition 6.6(B) already carries, plus `δ + 2a ≤ 1` (a
consequence of the small-`b` branch of the assembly) and nonemptiness of the coarse fibres. -/
theorem prop51SelectScaleOfDatum {δ₀ B : NNReal}
    (input : ShadedBody.Section6FactoringSelectScaleInput D.toFineProp51Family δ₀ B)
    (hδ0 : 0 < δ) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hsmall : δ + 2 * a ≤ 1)
    (hcfne : ∀ x ∈ D.factor.cells, (D.factor.coarseFibre x).Nonempty) :
    ShadedBody.FactoringAndMultPropCoreSelectScaleResult
      (C := ((remark53ThickConst Cfib CF : ℝ≥0) : ENNReal))
      D.toFineProp51Family input.hδ input.hdisc input.volumeRatio input.hδB input.hupper
        input.hmass :=
  ShadedBody.section6GlobalFactorisationSelectScale D.toFineProp51Family input
    (D.hasThickenedFrostmanFibers hδ0 hρ0 hρ1 hsmall hcfne)

open Classical in
/-- **The same, with the input constructed too: Proposition 5.1 for Part (B) is a theorem.**

Every hypothesis below is one Proposition 6.6(B) already has (`0 < δ`, `δ ≤ ρ ≤ a`, the fine tubes
in the unit ball, positive fine shading mass), except `δ + 2a ≤ 1` and the nonemptiness of the
coarse fibres.  Nothing is assumed about Proposition 5.1 itself. -/
theorem exists_prop51SelectScale
    (hδ0 : 0 < δ) (hδhalf : (δ : ℝ) ≤ 1 / 2) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hδa : δ ≤ a)
    (hball : ∀ i ∈ q, ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ Metric.closedBall 0 1)
    (hmass : 0 < ∑ i ∈ q, volume (T i).shade)
    (hsmall : δ + 2 * a ≤ 1)
    (hcfne : ∀ x ∈ D.factor.cells, (D.factor.coarseFibre x).Nonempty) :
    ∃ input : ShadedBody.Section6FactoringSelectScaleInput D.toFineProp51Family δ a,
      ShadedBody.FactoringAndMultPropCoreSelectScaleResult
        (C := ((remark53ThickConst Cfib CF : ℝ≥0) : ENNReal))
        D.toFineProp51Family input.hδ input.hdisc input.volumeRatio input.hδB input.hupper
          input.hmass :=
  ⟨D.section6SelectScaleInput hδ0 hδhalf hδa le_rfl hball hmass,
    D.prop51SelectScaleOfDatum _ hδ0 hρ0 hρ1 hsmall hcfne⟩


/-! ## Why `Remark53Prop51` is not the Proposition-5.1 output, mechanically -/

/-- `Kakeya.Section6PartBData.fineOutput` keeps *all* the fine indices. -/
@[simp] theorem fineOutput_innerSet : D.fineOutput.innerSet = q := rfl

/-- `Kakeya.Section6PartBData.fineOutput` keeps *all* the cells. -/
@[simp] theorem fineOutput_outerSet : D.fineOutput.outerSet = D.factor.cells := rfl

/-- `Kakeya.Section6PartBData.fineOutput`'s fibres are the datum's own fine fibres. -/
theorem fineOutput_fiber (x : D.factor.Cell) : D.fineOutput.fiber x = D.fineFibre x := rfl

/-- `Kakeya.Section6PartBData.fineOutput` keeps the fine shades verbatim. -/
theorem fineOutput_innerBody (i : ι) : D.fineOutput.innerBody i = (T i).toShadedBody := rfl

/-- **`Kakeya.Section6PartBData.Remark53Prop51`'s refinement clause is the identity refinement.**

Compiler-checked form of the diagnosis: `fineOutput` performs no refinement at all, so the clause
`refinement` relates `(q, T)` to itself.  The three substantive clauses — `outerConstMult`,
`innerConstMult`, `fiber_card_comparable` — are therefore asserted of the *unrefined* families,
with a constant `Cprop` fixed before the configuration.  That is strictly stronger than anything
Proposition 5.1 produces, which is why `Remark53Prop51` has no constructor and why the honest route
is `Kakeya.Section6PartBData.exists_prop51SelectScale`, whose output family is the constructed
`ShadedBody.outerThickFamilyAtScale`. -/
theorem remark53Prop51_refinement_identity {Cprop : ℝ≥0} (hR : D.Remark53Prop51 Cprop) :
    ShadedBody.IsCRefinement q (fun i => (T i).toShadedBody) q (fun i => (T i).toShadedBody)
      Cprop⁻¹ :=
  hR.refinement

/-- **`Remark53Prop51.split` is the multiplicity split for the whole fine family.**

Not for a refinement of it: the inner factor on the right is the multiplicity of the *entire* fine
fibre `Kakeya.Section6PartBData.fineFibre x`, and the outer factor ranges over *all* cells. -/
theorem remark53Prop51_split_unrefined {Cprop : ℝ≥0} (hR : D.Remark53Prop51 Cprop)
    {x : D.factor.Cell} (hx : x ∈ D.factor.cells) :
    ShadedBody.multiplicity q (fun i => (T i).toShadedBody)
      ≤ (Cprop : ENNReal)
        * ShadedBody.multiplicity D.factor.cells (fun y => (D.outerPlanks y).toShadedBody)
        * ShadedBody.multiplicity (D.fineFibre x) (fun i => (T i).toShadedBody) :=
  hR.split x hx


/-! ## The Part-(B) multiplicity split, over the *constructed* Proposition-5.1 output -/

/-- Reassociation used once in the split below; stated separately so that `ring` sees no
metavariables. -/
private theorem ennrealMulReassoc (c c' A B : ENNReal) :
    c * (c' * A * B) = (c * c') * A * B := by ring

open Classical in
/-- **The GWZ Proposition 5.1 multiplicity split for Part (B), from the datum alone.**

This is the clause `Kakeya.Section6PartBData.Remark53Prop51.split` and the clause
`Kakeya.Section6PartBData.Remark53Prop51.refinement` — but for the family Proposition 5.1 actually
*constructs*, and with no `Remark53Prop51` hypothesis:

* `O` is the thick outer family produced by
  `ShadedBody.outerThickFamilyAtScale` over the outer scale selected by shading mass;
* `O.innerSet ⊆ q` with the fine convex bodies unchanged and the fine shades shrunk — the honest
  refinement that `Kakeya.Section6PartBData.fineOutput` does *not* perform
  (`Kakeya.Section6PartBData.remark53Prop51_refinement_identity`);
* the split `μ(𝒯, Y) ≤ Cs · μ(𝒲', Y_{𝒲'}) · μ(𝒯'_W, Y')` holds on every retained cell, with
  `Cs` the product of the logarithmic outer-scale selection constant and Proposition 5.1's own
  product constant.

**What is still missing between this and `Kakeya.Section6PartBData.OuterPackage`**: `O.outerBody j`
is the `scale`-collar of the cell body, not the cell's `a × b × 1` representative plank.  Part (A)
crosses that gap with the field `Kakeya.Section6CoreFactorData.cthickening_le_repr`; Part (B)'s
`Kakeya.Section6PartBFactorisation` has only `body_le_repr`, and the collar overflows the plank
along its long axis by the collar radius.  See the module docstring. -/
theorem exists_prop51_split_over_constructed_output
    (hδ0 : 0 < δ) (hδhalf : (δ : ℝ) ≤ 1 / 2) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hδa : δ ≤ a)
    (hball : ∀ i ∈ q, ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ Metric.closedBall 0 1)
    (hmass : 0 < ∑ i ∈ q, volume (T i).shade)
    (hsmall : δ + 2 * a ≤ 1)
    (hcfne : ∀ x ∈ D.factor.cells, (D.factor.coarseFibre x).Nonempty) :
    ∃ (Cs : ℝ≥0) (O : ShadedBody.ShadedFactorFamily (EuclideanSpace ℝ (Fin 3)) ι D.factor.Cell),
      1 ≤ Cs ∧
      O.outerSet ⊆ D.factor.cells ∧
      ShadedBody.IsRefinement O.innerSet O.innerBody q (fun i => (T i).toShadedBody) ∧
      (∀ i ∈ O.innerSet, (O.innerBody i).shade ⊆ (O.outerBody (O.parent i)).shade) ∧
      (∀ j ∈ O.outerSet,
        ShadedBody.multiplicity q (fun i => (T i).toShadedBody)
          ≤ (Cs : ENNReal) * ShadedBody.multiplicity O.outerSet O.outerBody
              * ShadedBody.multiplicity (O.fiber j) O.innerBody) := by
  classical
  set input := D.section6SelectScaleInput hδ0 hδhalf hδa le_rfl hball hmass with hinput
  have Q : ShadedBody.FactoringAndMultPropCoreSelectScaleResult
      (C := ((remark53ThickConst Cfib CF : ℝ≥0) : ENNReal))
      D.toFineProp51Family input.hδ input.hdisc input.volumeRatio input.hδB input.hupper
        input.hmass :=
    D.prop51SelectScaleOfDatum input hδ0 hρ0 hρ1 hsmall hcfne
  have href1 := Q.selection_refinement D.toFineProp51Family input.hδ input.hdisc
    input.volumeRatio input.hδB input.hupper input.hmass
  have hcore := Q.core
  have href2 := hcore.refinement
  have hsplit := hcore.multiplicity_product
  have houtsub := hcore.outerSet_subset
  have hshade := hcore.shading_containment
  -- the outer-scale selection constant is nonzero
  set selC : ℝ≥0 := ShadedBody.outerScaleSelectionConstant δ a with hselC
  have hselpos : 0 < (selC : ENNReal) * ∑ i ∈ (ShadedBody.selectedOuterScaleFamily
      D.toFineProp51Family input.hδ input.hdisc input.hδB input.hupper input.hmass).innerSet,
      volume ((ShadedBody.selectedOuterScaleFamily D.toFineProp51Family input.hδ input.hdisc
        input.hδB input.hupper input.hmass).innerBody i).shade :=
    input.hmass.trans_le Q.selection_mass
  have hsel0 : (selC : ENNReal) ≠ 0 := (pos_of_mul_pos_left hselpos (by positivity)).ne'
  have hsel0' : selC ≠ 0 := by
    intro h
    exact hsel0 (by rw [h]; simp)
  have hseltop : (selC : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  -- the selected family's outer indices are cells of the datum
  have hsubSelected : (ShadedBody.selectedOuterScaleFamily D.toFineProp51Family input.hδ
      input.hdisc input.hδB input.hupper input.hmass).outerSet ⊆ D.factor.cells := by
    simpa [ShadedBody.selectedOuterScaleFamily,
      ShadedBody.FactorFamily.restrictOuter_outerSet] using
      ((ShadedBody.outerScaleSelection D.toFineProp51Family input.hδ input.hdisc
        input.hδB input.hupper input.hmass).selected_subset.trans
          D.toFineProp51Family.innerSet_image_parent_subset_outerSet)
  set prodC : ℝ≥0 := ShadedBody.factoringCoreAtScaleUniformProductConstant
    (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))
    (ShadedBody.selectedOuterScaleFamily D.toFineProp51Family input.hδ input.hdisc
      input.hδB input.hupper input.hmass).innerSet.card
    (input.volumeRatio.restrictOuter _
      ((ShadedBody.outerScaleSelection D.toFineProp51Family input.hδ input.hdisc
        input.hδB input.hupper input.hmass).selected_subset.trans
          D.toFineProp51Family.innerSet_image_parent_subset_outerSet)).exponent
    (ShadedBody.selectedOuterScale D.toFineProp51Family input.hδ input.hdisc
      input.hδB input.hupper input.hmass) with hprodC
  refine ⟨max 1 (selC * prodC), _, le_max_left _ _, houtsub.trans hsubSelected,
    href2.1.trans href1.1, hshade, ?_⟩
  intro j hj
  have hstep1 : ((selC : ENNReal))⁻¹ * ShadedBody.multiplicity q (fun i => (T i).toShadedBody)
      ≤ ShadedBody.multiplicity (ShadedBody.selectedOuterScaleFamily D.toFineProp51Family
          input.hδ input.hdisc input.hδB input.hupper input.hmass).innerSet
        (ShadedBody.selectedOuterScaleFamily D.toFineProp51Family input.hδ input.hdisc
          input.hδB input.hupper input.hmass).innerBody := by
    have h := href1.mul_multiplicity_le
    rwa [ENNReal.coe_inv hsel0'] at h
  have hstep2 := hsplit j hj
  have hcancel : (selC : ENNReal) * ((selC : ENNReal))⁻¹ = 1 :=
    ENNReal.mul_inv_cancel hsel0 hseltop
  calc ShadedBody.multiplicity q (fun i => (T i).toShadedBody)
      = (selC : ENNReal) * (((selC : ENNReal))⁻¹
          * ShadedBody.multiplicity q (fun i => (T i).toShadedBody)) := by
        rw [← mul_assoc, hcancel, one_mul]
    _ ≤ (selC : ENNReal) * ((prodC : ENNReal)
          * ShadedBody.multiplicity _ _ * ShadedBody.multiplicity _ _) := by
        exact mul_le_mul_left' (le_trans hstep1 hstep2) _
    _ = ((selC : ENNReal) * (prodC : ENNReal))
          * ShadedBody.multiplicity _ _ * ShadedBody.multiplicity _ _ :=
        ennrealMulReassoc _ _ _ _
    _ ≤ ((max 1 (selC * prodC) : ℝ≥0) : ENNReal)
          * ShadedBody.multiplicity _ _ * ShadedBody.multiplicity _ _ := by
        gcongr
        rw [← ENNReal.coe_mul]
        exact ENNReal.coe_le_coe.mpr (le_max_right _ _)

end Section6PartBData

end Kakeya

end

end
