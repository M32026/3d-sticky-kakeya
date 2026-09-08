/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.DenseBoxCover
public import Kakeya.DimensionThree.Plank.SlabTypicalAngle
public import Kakeya.DimensionThree.Plank.DenseBoxSlabTransport

/-!
# Item 1 of GWZ Lemma 6.13: the outer dilation, and the whole local dense-ball chain

This module carries Item 1 of GWZ Lemma 6.13 from the outer ball-dilation constant through to the
two outputs the final assembly needs, in five sections:

1. the outer dilation constant `Kakeya.plankReduction.ballDilation = 3`;
2. angular concentration on the selected boxes of one slab;
3. the dense-`θb`-ball certificate of one selected good box;
4. Item 1 from an aggregated family of local dense-ball certificates;
5. the assembled Item 1, from the local dense-ball certificates.

The final section contains the whole of Item 1 downstream of the per-good-box work: it takes
the local dense-ball certificates produced by `Plank.denseBall_of_goodBox`, builds the global
retained set `Gtot`, and produces both outputs the final assembly needs — the quantitative
refinement of the
restricted shading, and the arbitrary-centre ball density at dilation
`Kakeya.plankReduction.ballDilation = 3`.

Everything is stated abstractly in the per-box data `(Dg, Gbox)`, so this file is independent of the
preassembly and of the good-box selection; the caller supplies

* the slab-local unions `Uloc S` with their `Nov` pointwise overlap,
* the localized capture `|U| ≤ 2 |U ∩ Wloc|` of
  `Plank.goodBoxes_unionLocal_capture_of_trimmedSlabFamilies`,
* per selected box, the four conclusions of `Plank.denseBall_of_goodBox`.

The two constants that appear are the ones already fixed upstream: the capture constant
`256 · Nov = 2 · 2 · 8 · 8 · Nov` of `Plank.volume_le_mul_volume_inter_of_localCapture`, and the
ball threshold `t` of `Plank.denseBall_of_goodBox`.  No factor `#𝒮` occurs, and no
configuration-dependent constant is introduced.

The pointwise cover feeding `Plank.localDensity_of_denseBallCover` is assembled directly, rather
than through a generic aggregation lemma indexed by a `Finset` of triples `(S, sh, q)`: building
that index as a dependent sigma adds bookkeeping without changing the argument, which is three
lines of `Set.mem_iUnion₂` plus one `measure_mono`.
-/

@[expose] public section

open MeasureTheory Convexity
open scoped NNReal Real ENNReal

/-!
## The outer ball-dilation constant of Item 1

`Kakeya.plankReduction.ballDilation = 3` is the factor by which the outer ball of Item 1 is dilated
relative to the inner one.  It is *not* an existential parameter: it is the literal `3` that
`Plank.denseBall_arbitraryCentre_fullness` produces from the triangle inequality
`B(c, r) ⊆ B(x, 3r)` for a retained dense ball `B(c, r)` meeting `B(x, r)`.

Naming it keeps the Item 1 statements readable and makes the fixedness visible.  The public
statement of GWZ Lemma 6.13 has its own copy in the `ShadedPlank` namespace
(`ShadedPlank.redPlankTube.ballDilation`, in `Kakeya/DimensionThree/Plank/Reduction.lean`); the two
are definitionally equal, which is what lets the final assembly bridge them by `rfl`.
-/

namespace Kakeya

/-- The dilation factor of the outer ball in Item 1 of `Kakeya.plankReduction`.  It is the literal
constant `3` produced by `Plank.denseBall_arbitraryCentre_fullness`, where it comes from the
triangle inequality `B(c,r) ⊆ B(x,3r)` for a retained dense ball `B(c,r)` meeting `B(x,r)`.  Naming
it keeps the statement readable while making clear that it is fixed and not an existential
parameter. -/
def plankReduction.ballDilation : ℝ≥0 := 3

end Kakeya

noncomputable section

namespace Plank

variable {ι : Type*}

/-! ## Angular concentration on the selected boxes of one slab

The good-box layer selects, slab by slab, boxes of the shifted grid on which the trimmed local
families are dense (`Plank.goodBoxes_unionLocal_capture_of_trimmedSlabFamilies`).  To turn that
density
into a *dense-box* estimate one needs hypothesis (5) of the dense-box chain — the
typical-intersection angle concentration — on exactly those local families.  This section
supplies it.

The only work is instantiating `Plank.localAngleConcentration_of_saturated` on the slab-local data,
and the point is that all three of its non-formal hypotheses are available at *no cost*:

* the max-angle bound, by `Plank.hasMaxPlankAngleBound_trimmed_inSlabFamilyC`;
* the angular-stability clause at the *global* scale `A`, by
  `Plank.localStability_trimmed_inSlabFamilyC`;
* saturation of `T sh q` in the enlarged family, which holds by the definition of `T` as a filter.

Both transfers are rewritings along `Plank.shadeFibre_trimmed_inSlabFamilyC_eq`, so the retained
fraction is `1`: no reserve stability scale, no extra `a^ε`, and the *same* `θ` throughout — Lemma
6.11 is emphatically not rerun per slab.

`Ceta` is produced once, before every geometric datum, and is uniform in the slab, the shift and the
box.  The statement is per-slab because `Plank.localAngleConcentration_of_saturated` fixes one base
family, and the base family here is the enlarged controlled slab family of that slab; the shift
index plays the role of its `𝒯'`, which is why the conclusion is over `Plank.gridShiftSet`.
-/

open scoped Classical in
/-- **Hypothesis (5) on the selected boxes of one slab, at retention one.**

`Plank.localAngleConcentration_of_saturated` run on the enlarged controlled slab family
`inSlabFamilyC Cset' Cang' s' V S` with the trimmed shadings `YS`, its `𝒯'` being
`Plank.gridShiftSet` and its regions the middle halves `Plank.halfSlabBox S b sh q`.

The three inputs are the global max-angle bound `hmax`, the global angular-stability clause `hstab`
at scale `A`, and the definition of `T` as the saturated filter; the first two transfer to the
slab-local family with the *same* constants because the trimmed enlarged family's shade fibre is
literally the global one.

`Ceta` depends only on `C` and `η` and is fixed before `a`, `b`, `θ`, the slab, the shift and the
box. -/
theorem localAngleConcentration_trimmed_of_slabLocal (C : ℝ≥0) (hC : 1 ≤ C) {η : ℝ} (hη : 0 < η) :
    ∃ Ceta : ℝ≥0, 0 < Ceta ∧
      ∀ {a b θ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {hθ1 : θ ≤ 1} {ι : Type*}
        (Cset Cang Cset' Cang' : ℝ≥0) (S : Slab θ hθ1)
        (s' : Finset ι) (V : ι → Plank a b hab hb1)
        (Y' YS : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
        (T : (Fin 3 → ℝ) → (Fin 3 → ℤ) → Finset ι)
        (Z : (Fin 3 → ℝ) → (Fin 3 → ℤ) → ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
        (Dg : (Fin 3 → ℝ) → Finset (Fin 3 → ℤ)) (A : ℝ),
        0 < a → a < 1 → 0 < b → 0 < θ → a ≤ θ * b → 2 ≤ A →
        Cset + 4 * (2 * Cang + 4 * C) + 8 ≤ Cset' →
        2 * Cang + 4 * C ≤ Cang' →
        (∀ i ∈ s', (Y' i).shade ⊆ ((V i).carrier : Set (EuclideanSpace ℝ (Fin 3)))) →
        Kakeya.HasMaxPlankAngleBound s' Y' V θ C →
        (∀ x ∈ ⋃ i ∈ s', (Y' i).shade, ∀ t ⊆ Kakeya.shadeFibre s' Y' x,
          A⁻¹ * ((Kakeya.shadeFibre s' Y' x).card : ℝ) ≤ (t.card : ℝ) →
            (θ : ℝ) / Kakeya.plankAngleScaleB a
              ≤ ((Kakeya.maxPlankAngle V t : ℝ≥0) : ℝ)) →
        (∀ i, (YS i).shade
          = (Y' i).shade ∩ ⋃ i' ∈ inSlabFamilyC Cset Cang s' V S, (Y' i').shade) →
        (∀ sh q, T sh q = (inSlabFamilyC Cset' Cang' s' V S).filter
          (fun i => ((YS i).shade ∩ halfSlabBox S b sh q).Nonempty)) →
        (∀ sh q, ∀ i ∈ T sh q, (Z sh q i).shade = (YS i).shade ∩ halfSlabBox S b sh q) →
        LocalAngleConcentration V θ gridShiftSet Dg T Z Ceta η := by
  classical
  obtain ⟨Ceta, hCetapos, hLAC⟩ := localAngleConcentration_of_saturated C hC hη
  refine ⟨Ceta, hCetapos, ?_⟩
  intro a b θ hab hb1 hθ1 ι Cset Cang Cset' Cang' S s' V Y' YS T Z Dg A
    ha ha1 hb hθ haθb hA hCset' hCang' hshV hmax hstab hYS hT hZsh
  refine hLAC (inSlabFamilyC Cset' Cang' s' V S) V YS gridShiftSet Dg
    (fun sh q => halfSlabBox S b sh q) T Z A ha ha1 hb hθ hθ1 hA ?_ ?_ ?_ ?_ ?_
  · exact hasMaxPlankAngleBound_trimmed_inSlabFamilyC s' V Y' YS S Cset Cang C Cset' Cang'
      haθb hCset' hCang' hshV hmax hYS
  · intro sh _ q _
    rw [hT sh q]
    exact Finset.filter_subset _ _
  · intro sh _ q _ i hi
    exact hZsh sh q i hi
  · intro sh _ q _ i hi x hx hxR
    rw [hT sh q]
    exact Finset.mem_filter.mpr ⟨hi, ⟨x, hx, hxR⟩⟩
  · exact localStability_trimmed_inSlabFamilyC s' V Y' YS S Cset Cang C Cset' Cang' A
      (Kakeya.plankAngleScaleB a) haθb hCset' hCang' hshV hmax hYS hstab

/-! ## From a selected good box to a dense `θb`-ball certificate

One selected good box `(S, sh, q)` of `Plank.goodBoxUnionLocal` carries three pieces of data: the
box-normalised fullness `b · lamScale ≤ λ(T, Z)` of
`Plank.goodBoxes_unionLocal_capture_of_trimmedSlabFamilies`, the angular concentration
`Plank.LocalAngleConcentration` of `Plank.localAngleConcentration_trimmed_of_slabLocal`, and the
tangency/carrier facts of the saturated family.  This section turns that into a dense-ball
certificate.

**The certificates are stated for the slab-local union**

`U_S = ⋃ i ∈ Large S, (YS S i).shade`,

not for the global union `⋃ i ∈ s', (Y' i).shade`.  That is forced by the aggregation: the slab
overlap constant `Nov` of `Plank.slab_index_overlap_le` bounds how many *slab-local* families an
index lies in, and hence controls a sum of slab-local unions; it says nothing about a global point
that happens to lie in the boxes of many slabs.  Enlarging to the global union is legitimate only
*after* the slab/shift/box aggregation has been performed, and doing it earlier would silently cost
a factor `#𝒮`.

The exponent bookkeeping is `Kakeya.denseBall_exponent_budget`, run at the shrunk rate `ε'`:

* `ηL = η + 5ε'/4` is both the fullness exponent of `lamScale`
  (`Kakeya.lamScale_eq`, an equality) and the angular-concentration exponent at which
  `Plank.localAngleConcentration_trimmed_of_slabLocal` is instantiated;
* `Plank.denseBoxUnionEstimate_shiftedBox` contributes `a^{2 ηL} · lamScale`, so the box density has
  exponent `3 ηL`;
* `3 ηL ≤ 4η + ε'` and `a ≤ 1` weaken that to the Item 1 shape `a^{4η + ε'}`;
* `Plank.denseBallCapture_of_denseBoxEstimate` costs one absolute constant and no power of `a`.

The union density is obtained through the dense-box (L²/angular) argument throughout; at no point is
a union volume replaced by a sum of shading volumes, and no pointwise multiplicity upper bound is
used.
-/

/-- **The density of one selected good box, already in Item 1's exponent shape.**

`Plank.denseBoxUnionEstimate_shiftedBox` at the single exponent `ηL`, with its `cLam · a^{ηL} ≤ lam`
hypothesis discharged by the closed form of the threshold, and its output weakened from `a^{3 ηL}`
to `a^{4η + ε'}` using `3 ηL ≤ 4η + ε'` and `a ≤ 1`.

The conclusion is about the **slab-local** union `⋃ i ∈ Large, (YS i).shade`; see the section
introduction for why it must not be the global one.

The angular data `θ0, Cstar, Mtyp` is passed unpacked, exactly as
`Plank.LocalAngleConcentration` supplies it for the pair `(sh, q)`. -/
theorem goodBox_density_of_concentration (cTan Ceta : ℝ≥0) (hCeta : 0 < Ceta) :
    ∃ cDense : ℝ≥0, 0 < cDense ∧
      ∀ {a b θ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {hθ1 : θ ≤ 1} {ι : Type*}
        (η ε' ηL : ℝ) (cLamBox lamScale : ℝ≥0)
        (S : Slab θ hθ1) (sh : Fin 3 → ℝ) (q : Fin 3 → ℤ)
        (Large : Finset ι) (V : ι → Plank a b hab hb1)
        (YS : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
        (Tq : Finset ι) (Z : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
        (θ0 : ℝ) (Mtyp Cstar : ℝ≥0),
        0 < a → a ≤ 1 → 0 < b → 0 < θ → 0 < ηL → 0 < cLamBox → a / b ≤ θ →
        3 * ηL ≤ 4 * η + ε' →
        cLamBox * a ^ ηL ≤ lamScale →
        ((a / b : ℝ≥0) : ℝ) ≤ θ0 → θ0 ≤ 1 → (θ : ℝ) ≤ (Cstar : ℝ) * θ0 →
        (Cstar : ENNReal) * (Mtyp : ENNReal) ≤ (Ceta : ENNReal) * (a : ENNReal) ^ (-ηL) →
        Tq ⊆ Large →
        (∀ i ∈ Large, (YS i).shade ⊆ ((V i).carrier : Set (EuclideanSpace ℝ (Fin 3)))) →
        (∀ i ∈ Tq, (Z i).shade ⊆ (YS i).shade ∩
          ((shiftedSlabBox S b sh q).carrier : Set (EuclideanSpace ℝ (Fin 3)))) →
        (∀ i ∈ Tq, (Z i).carrier = (V i).carrier) →
        (∀ i ∈ Tq, Kakeya.ComparableScalars cTan
          (volume (((V i).carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩
            (shiftedSlabBox S b sh q).carrier)).toNNReal (a * b ^ 2)) →
        b * lamScale ≤ ShadedBody.fullness Tq Z →
        ((∑ i ∈ Tq, ∑ j ∈ Tq, volume ((Z i).shade ∩ (Z j).shade))
          ≤ (Mtyp : ENNReal) * (∑ i ∈ Tq, ∑ j ∈ Tq with
              (θ0 - ((a / b : ℝ≥0) : ℝ) ≤ Prism3D.angle (V i) (V j) ∧
                Prism3D.angle (V i) (V j) ≤ 2 * θ0),
            volume ((Z i).shade ∩ (Z j).shade))) →
        ((cDense * cLamBox * cLamBox * a ^ (4 * η + ε') : ℝ≥0) : ENNReal) *
            volume ((shiftedSlabBox S b sh q).carrier)
          ≤ volume ((⋃ i ∈ Large, (YS i).shade) ∩
              ((shiftedSlabBox S b sh q).carrier : Set (EuclideanSpace ℝ (Fin 3)))) := by
  obtain ⟨cDense, hcDense, hdensebox⟩ := denseBoxUnionEstimate_shiftedBox cTan Ceta hCeta
  refine ⟨cDense, hcDense, ?_⟩
  intro a b θ hab hb1 hθ1 ι η ε' ηL cLamBox lamScale S sh q Large V YS Tq Z θ0 Mtyp Cstar
    ha ha1 hb hθ hηL hcLamBox habθ h3ηL hlam_lb habθ0 hθ01 hθθ0 hMtyp hTq hshV
    hZsh hZcar htan hlam hconc
  have hkey := hdensebox Large V YS S sh q Tq Z ηL θ0 Mtyp Cstar cLamBox lamScale
    ha hb hθ hηL hcLamBox habθ habθ0 hθ01 hθθ0 hMtyp hlam_lb hTq hshV hZsh hZcar htan hlam hconc
  have hconst : (cDense * cLamBox * cLamBox * a ^ (4 * η + ε') : ℝ≥0)
      ≤ cDense * cLamBox * a ^ (2 * ηL) * lamScale := by
    have hrp : a ^ (4 * η + ε') ≤ a ^ (3 * ηL) :=
      NNReal.rpow_le_rpow_of_exponent_ge ha ha1 h3ηL
    have h3 : (3 : ℝ) * ηL = 2 * ηL + ηL := by ring
    have hsplit : a ^ (3 * ηL) = a ^ (2 * ηL) * a ^ ηL := by
      rw [h3, NNReal.rpow_add ha.ne']
    calc
      (cDense * cLamBox * cLamBox * a ^ (4 * η + ε') : ℝ≥0)
          ≤ cDense * cLamBox * cLamBox * a ^ (3 * ηL) := mul_le_mul_right hrp _
      _ = cDense * cLamBox * a ^ (2 * ηL) * (cLamBox * a ^ ηL) := by rw [hsplit]; ring
      _ ≤ cDense * cLamBox * a ^ (2 * ηL) * lamScale := mul_le_mul_right hlam_lb _
  calc
    ((cDense * cLamBox * cLamBox * a ^ (4 * η + ε') : ℝ≥0) : ENNReal) *
        volume ((shiftedSlabBox S b sh q).carrier)
        ≤ ((cDense * cLamBox * a ^ (2 * ηL) * lamScale : ℝ≥0) : ENNReal) *
            volume ((shiftedSlabBox S b sh q).carrier) :=
          mul_le_mul_left (ENNReal.coe_le_coe.mpr hconst) _
    _ ≤ volume ((⋃ i ∈ Large, (YS i).shade) ∩
          ((shiftedSlabBox S b sh q).carrier : Set (EuclideanSpace ℝ (Fin 3)))) := hkey

/-- The shading union of a finite family is measurable. -/
theorem measurableSet_biUnion_shade (s : Finset ι)
    (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))) :
    MeasurableSet (⋃ i ∈ s, (Y i).shade) :=
  MeasurableSet.biUnion (Finset.countable_toSet s) fun i _ => (Y i).measurableSet_shade

/-- **The dense-ball certificate of one selected good box, on the slab-local union.**

`Plank.goodBox_density_of_concentration` fed into `Plank.denseBallCapture_of_denseBoxEstimate`, with
the returned region cut down to the box (which is free: the retained set is intersected with
`U_S ∩ Q` throughout, and `U_S ∩ Q ⊆ Q`).

The four conclusions are the ones the slab/shift/box aggregation consumes: measurability,
containment in the box, the absolute half-retention of `U_S` inside the box, and the
arbitrary-centre `θb`-ball density at the single threshold `cBall · cLamBox² · a^{4η + ε'}`, whose
constant is fixed before every geometric datum and whose exponent is exactly Item 1's.

Everything is relative to `U_S = ⋃ i ∈ Large, (YS i).shade`; the passage to the global union happens
only after aggregation. -/
theorem denseBall_of_goodBox (cTan Ceta : ℝ≥0) (hCeta : 0 < Ceta) :
    ∃ cBall : ℝ≥0, 0 < cBall ∧
      ∀ {a b θ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {hθ1 : θ ≤ 1} {ι : Type*}
        (η ε' ηL : ℝ) (cLamBox lamScale : ℝ≥0)
        (S : Slab θ hθ1) (sh : Fin 3 → ℝ) (q : Fin 3 → ℤ)
        (Large : Finset ι) (V : ι → Plank a b hab hb1)
        (YS : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
        (Tq : Finset ι) (Z : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
        (θ0 : ℝ) (Mtyp Cstar : ℝ≥0),
        0 < a → a ≤ 1 → 0 < b → 0 < θ → 0 < ηL → 0 < cLamBox → a / b ≤ θ →
        3 * ηL ≤ 4 * η + ε' →
        cLamBox * a ^ ηL ≤ lamScale →
        ((a / b : ℝ≥0) : ℝ) ≤ θ0 → θ0 ≤ 1 → (θ : ℝ) ≤ (Cstar : ℝ) * θ0 →
        (Cstar : ENNReal) * (Mtyp : ENNReal) ≤ (Ceta : ENNReal) * (a : ENNReal) ^ (-ηL) →
        Tq ⊆ Large →
        (∀ i ∈ Large, (YS i).shade ⊆ ((V i).carrier : Set (EuclideanSpace ℝ (Fin 3)))) →
        (∀ i ∈ Tq, (Z i).shade ⊆ (YS i).shade ∩
          ((shiftedSlabBox S b sh q).carrier : Set (EuclideanSpace ℝ (Fin 3)))) →
        (∀ i ∈ Tq, (Z i).carrier = (V i).carrier) →
        (∀ i ∈ Tq, Kakeya.ComparableScalars cTan
          (volume (((V i).carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩
            (shiftedSlabBox S b sh q).carrier)).toNNReal (a * b ^ 2)) →
        b * lamScale ≤ ShadedBody.fullness Tq Z →
        ((∑ i ∈ Tq, ∑ j ∈ Tq, volume ((Z i).shade ∩ (Z j).shade))
          ≤ (Mtyp : ENNReal) * (∑ i ∈ Tq, ∑ j ∈ Tq with
              (θ0 - ((a / b : ℝ≥0) : ℝ) ≤ Prism3D.angle (V i) (V j) ∧
                Prism3D.angle (V i) (V j) ≤ 2 * θ0),
            volume ((Z i).shade ∩ (Z j).shade))) →
        ∃ G : Set (EuclideanSpace ℝ (Fin 3)), MeasurableSet G ∧
          G ⊆ ((shiftedSlabBox S b sh q).carrier : Set (EuclideanSpace ℝ (Fin 3))) ∧
          volume ((⋃ i ∈ Large, (YS i).shade) ∩
              ((shiftedSlabBox S b sh q).carrier : Set (EuclideanSpace ℝ (Fin 3))))
            ≤ 2 * volume (((⋃ i ∈ Large, (YS i).shade) ∩
              ((shiftedSlabBox S b sh q).carrier :
                Set (EuclideanSpace ℝ (Fin 3)))) ∩ G) ∧
          (∀ y ∈ G, ∃ c : EuclideanSpace ℝ (Fin 3), y ∈ thetaBall θ b c ∧
            ((cBall * cLamBox * cLamBox * a ^ (4 * η + ε') : ℝ≥0) : ENNReal) *
                volume (thetaBall θ b c)
              ≤ volume ((((⋃ i ∈ Large, (YS i).shade) ∩
                  ((shiftedSlabBox S b sh q).carrier :
                    Set (EuclideanSpace ℝ (Fin 3)))) ∩ G) ∩ thetaBall θ b c)) := by
  obtain ⟨cDense, hcDense, hdensity⟩ := goodBox_density_of_concentration cTan Ceta hCeta
  obtain ⟨cThr, hcThr, hball⟩ := denseBallCapture_of_denseBoxEstimate
  refine ⟨cThr * cDense, by positivity, ?_⟩
  intro a b θ hab hb1 hθ1 ι η ε' ηL cLamBox lamScale S sh q Large V YS Tq Z θ0 Mtyp Cstar
    ha ha1 hb hθ hηL hcLamBox habθ h3ηL hlam_lb habθ0 hθ01 hθθ0 hMtyp hTq hshV
    hZsh hZcar htan hlam hconc
  have hlow := hdensity η ε' ηL cLamBox lamScale S sh q Large V YS Tq Z θ0 Mtyp Cstar
    ha ha1 hb hθ hηL hcLamBox habθ h3ηL hlam_lb habθ0 hθ01 hθθ0 hMtyp hTq hshV
    hZsh hZcar htan hlam hconc
  obtain ⟨GQ, hGQmeas, hGQret, hGQball⟩ := hball (shiftedSlabBox S b sh q) hθ hb
    (⋃ i ∈ Large, (YS i).shade) (measurableSet_biUnion_shade Large YS)
    (cDense * cLamBox * cLamBox * a ^ (4 * η + ε')) hlow
  have hrw : ((⋃ i ∈ Large, (YS i).shade) ∩
      ((shiftedSlabBox S b sh q).carrier : Set (EuclideanSpace ℝ (Fin 3)))) ∩
        (GQ ∩ ((shiftedSlabBox S b sh q).carrier : Set (EuclideanSpace ℝ (Fin 3))))
      = ((⋃ i ∈ Large, (YS i).shade) ∩
          ((shiftedSlabBox S b sh q).carrier : Set (EuclideanSpace ℝ (Fin 3)))) ∩ GQ := by
    ext x
    simp only [Set.mem_inter_iff]
    tauto
  refine ⟨GQ ∩ ((shiftedSlabBox S b sh q).carrier : Set (EuclideanSpace ℝ (Fin 3))),
    hGQmeas.inter (shiftedSlabBox S b sh q).measurableSet_carrier, Set.inter_subset_right, ?_, ?_⟩
  · rw [hrw]
    exact hGQret
  · intro y hy
    obtain ⟨c, hyc, hdens⟩ := hGQball y hy.1
    refine ⟨c, hyc, ?_⟩
    rw [hrw]
    have hcoe : ((cThr * cDense * cLamBox * cLamBox * a ^ (4 * η + ε') : ℝ≥0) : ENNReal)
        = ((cThr * (cDense * cLamBox * cLamBox * a ^ (4 * η + ε')) : ℝ≥0) : ENNReal) := by
      push_cast
      ring
    rw [hcoe]
    exact hdens

/-! ## Item 1 from an aggregated family of local dense-ball certificates

This section performs the last two steps of the local route for item 1 of GWZ Lemma 6.13:
aggregating the per-box dense-ball certificates of
`Plank.denseBallCapture_of_denseBoxEstimate` into a single certificate for the globally
restricted shading, and then feeding that certificate to
`Plank.denseBall_arbitraryCentre_fullness`.

Two small points make the aggregation work, and both are worth stating explicitly because they are
where a careless argument breaks.

*The local certificate must be quantified over `G_p`, not over `U_p ∩ G_p`.*  After aggregation, a
point of the globally retained shading `U ∩ G` may well lie in the retained set `G_p` of a box `p`
whose own local union `U_p` it does not belong to — it got into `U` through a plank of a different
slab.  Such a point still has to be handed a dense ball, so the local statement has to cover it.
`Plank.denseBallCapture_of_denseBoxEstimate` is stated that way.

*The local density transfers upward for free.*  The ball produced at `p` is dense for the local
retained set `U_p ∩ G_p`, not for the global one; but `U_p ∩ G_p ⊆ U ∩ G`, so monotonicity of the
measure upgrades the local density to a global one with no loss of constant.  In particular the
local sets are allowed to overlap arbitrarily, and no disjointness or bounded-overlap input is
needed *for item 1*.  (Bounded overlap is needed for the refinement estimate, which is a different
statement and is not proved here.)

The outer radius is the literal `Kakeya.plankReduction.ballDilation = 3` of
`Plank.denseBall_arbitraryCentre_fullness`, coming from `B(c, r) ⊆ B(x, 3r)`.
-/

/-- The shading union of a family restricted to a common set `G` is the original union cut by
`G`. -/
theorem biUnion_restrictShade_shade (s' : Finset ι)
    (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (G : Set (EuclideanSpace ℝ (Fin 3))) (hG : MeasurableSet G) :
    (⋃ i ∈ s', (ShadedBody.restrictShade (Y' i) G hG).shade)
      = (⋃ i ∈ s', (Y' i).shade) ∩ G := by
  simp [Set.iUnion_inter]

/-- **Item 1 from a global dense-ball certificate**, at the literal outer dilation
`Kakeya.plankReduction.ballDilation = 3`.

This is `Plank.denseBall_arbitraryCentre_fullness` with the threshold left as a bare `t` rather
than presented as `cdb · a ^ (4η)`; the caller supplies whichever power of `a` its dense-box
estimate produced. -/
theorem localDensity_of_denseBallCover {theta b : ℝ≥0}
    (Ufinal : Set (EuclideanSpace ℝ (Fin 3))) (t : ℝ≥0)
    (hcover : ∀ y ∈ Ufinal, ∃ c : EuclideanSpace ℝ (Fin 3),
      y ∈ thetaBall theta b c ∧
      (t : ENNReal) * volume (thetaBall theta b c)
        ≤ volume (Ufinal ∩ thetaBall theta b c))
    (x : EuclideanSpace ℝ (Fin 3))
    (hmeet : (Ufinal ∩ Metric.closedBall x ((theta * b : ℝ≥0) : ℝ)).Nonempty) :
    (t : ENNReal) * volume (Metric.closedBall x ((theta * b : ℝ≥0) : ℝ))
      ≤ volume (Ufinal ∩ Metric.closedBall x
          ((Kakeya.plankReduction.ballDilation : ℝ) * ((theta * b : ℝ≥0) : ℝ))) := by
  simpa [Plank.thetaBall, Kakeya.plankReduction.ballDilation] using
    Plank.denseBall_arbitraryCentre_fullness (a := (1 : ℝ≥0)) (cdb := t) (η := 0)
      (r := ((theta * b : ℝ≥0) : ℝ)) (U := Ufinal)
      (by
        intro y hy
        rcases hcover y hy with ⟨c, hyc, hdens⟩
        exact ⟨c, hyc, by simpa [Plank.thetaBall] using hdens⟩)
      x hmeet

/-! ## The assembled Item 1, from the local dense-ball certificates -/

/-- **The global retained set.**  The union of the per-box dense-ball regions over every used slab,
every one of the eight grid shifts, and every selected good box. -/
def denseBallUnion {θ : ℝ≥0} {hθ1 : θ ≤ 1} (𝒮 : Finset (Slab θ hθ1))
    (Dg : Slab θ hθ1 → (Fin 3 → ℝ) → Finset (Fin 3 → ℤ))
    (Gbox : Slab θ hθ1 → (Fin 3 → ℝ) → (Fin 3 → ℤ) → Set (EuclideanSpace ℝ (Fin 3))) :
    Set (EuclideanSpace ℝ (Fin 3)) :=
  ⋃ S ∈ 𝒮, ⋃ sh ∈ gridShiftSet, ⋃ q ∈ Dg S sh, Gbox S sh q

theorem measurableSet_denseBallUnion {θ : ℝ≥0} {hθ1 : θ ≤ 1} (𝒮 : Finset (Slab θ hθ1))
    (Dg : Slab θ hθ1 → (Fin 3 → ℝ) → Finset (Fin 3 → ℤ))
    (Gbox : Slab θ hθ1 → (Fin 3 → ℝ) → (Fin 3 → ℤ) → Set (EuclideanSpace ℝ (Fin 3)))
    (hGmeas : ∀ S sh q, MeasurableSet (Gbox S sh q)) :
    MeasurableSet (denseBallUnion 𝒮 Dg Gbox) := by
  classical
  refine MeasurableSet.biUnion (Finset.countable_toSet 𝒮) fun S _ => ?_
  refine MeasurableSet.biUnion (Finset.countable_toSet gridShiftSet) fun sh _ => ?_
  refine MeasurableSet.biUnion (Finset.countable_toSet (Dg S sh)) fun q _ => ?_
  exact hGmeas S sh q

theorem subset_denseBallUnion {θ : ℝ≥0} {hθ1 : θ ≤ 1} {𝒮 : Finset (Slab θ hθ1)}
    {Dg : Slab θ hθ1 → (Fin 3 → ℝ) → Finset (Fin 3 → ℤ)}
    {Gbox : Slab θ hθ1 → (Fin 3 → ℝ) → (Fin 3 → ℤ) → Set (EuclideanSpace ℝ (Fin 3))}
    {S : Slab θ hθ1} (hS : S ∈ 𝒮) {sh : Fin 3 → ℝ} (hsh : sh ∈ gridShiftSet)
    {q : Fin 3 → ℤ} (hq : q ∈ Dg S sh) :
    Gbox S sh q ⊆ denseBallUnion 𝒮 Dg Gbox := by
  intro x hx
  exact Set.mem_iUnion₂.mpr ⟨S, hS, Set.mem_iUnion₂.mpr ⟨sh, hsh,
    Set.mem_iUnion₂.mpr ⟨q, hq, hx⟩⟩⟩

/-- **The pointwise dense-ball cover of the retained shading union.**

Every point of `U ∩ Gtot` lies in one of the selected `Gbox`, whose own certificate exhibits a
`θb`-ball capturing a `t`-fraction of a set contained in `U ∩ Gtot`.  This is the `hcover` input of
`Plank.localDensity_of_denseBallCover`. -/
theorem denseBallCover_of_localDenseBalls {b θ : ℝ≥0} {hθ1 : θ ≤ 1}
    (s' : Finset ι) (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (𝒮 : Finset (Slab θ hθ1))
    (Uloc : Slab θ hθ1 → Set (EuclideanSpace ℝ (Fin 3)))
    (Dg : Slab θ hθ1 → (Fin 3 → ℝ) → Finset (Fin 3 → ℤ))
    (Gbox : Slab θ hθ1 → (Fin 3 → ℝ) → (Fin 3 → ℤ) → Set (EuclideanSpace ℝ (Fin 3)))
    (t : ℝ≥0)
    (hUlocU : ∀ S ∈ 𝒮, Uloc S ⊆ ⋃ i ∈ s', (Y' i).shade)
    (hball : ∀ S ∈ 𝒮, ∀ sh ∈ gridShiftSet, ∀ q ∈ Dg S sh, ∀ y ∈ Gbox S sh q,
      ∃ c : EuclideanSpace ℝ (Fin 3), y ∈ thetaBall θ b c ∧
        (t : ENNReal) * volume (thetaBall θ b c)
          ≤ volume (((Uloc S ∩ ((shiftedSlabBox S b sh q).carrier :
              Set (EuclideanSpace ℝ (Fin 3)))) ∩ Gbox S sh q) ∩ thetaBall θ b c)) :
    ∀ y ∈ (⋃ i ∈ s', (Y' i).shade) ∩ denseBallUnion 𝒮 Dg Gbox,
      ∃ c : EuclideanSpace ℝ (Fin 3), y ∈ thetaBall θ b c ∧
        (t : ENNReal) * volume (thetaBall θ b c)
          ≤ volume (((⋃ i ∈ s', (Y' i).shade) ∩ denseBallUnion 𝒮 Dg Gbox) ∩
              thetaBall θ b c) := by
  intro y hy
  obtain ⟨S, hS, hy1⟩ := Set.mem_iUnion₂.mp hy.2
  obtain ⟨sh, hsh, hy2⟩ := Set.mem_iUnion₂.mp hy1
  obtain ⟨q, hq, hy3⟩ := Set.mem_iUnion₂.mp hy2
  obtain ⟨c, hyc, hdens⟩ := hball S hS sh hsh q hq y hy3
  refine ⟨c, hyc, hdens.trans (measure_mono ?_)⟩
  refine Set.inter_subset_inter_left _ ?_
  intro x hx
  exact ⟨hUlocU S hS hx.1.1, subset_denseBallUnion hS hsh hq hx.2⟩

open scoped Classical in
/-- **Item 1, from the local dense-ball certificates.**

The global retained set is `Gtot = Plank.denseBallUnion 𝒮 Dg Gbox`, and the two outputs are:

* the quantitative refinement `IsCRefinement s' (ShadedBody.restrictShade Y' Gtot) s' Y'` at
  the coefficient
  `((256 · Nov) · C_mult)⁻¹ · a^{ε_int}`, obtained from
  `Plank.volume_le_mul_volume_inter_of_localCapture` and
  `Plank.isCRefinement_restrictShade_of_localCapture`;
* the arbitrary-centre ball density at threshold `t` and dilation
  `Kakeya.plankReduction.ballDilation = 3`, obtained from
  `Plank.denseBallCover_of_localDenseBalls` and `Plank.localDensity_of_denseBallCover`.

Both are stated for the *same* restricted family, which is the one the final theorem returns. -/
theorem localDensity_of_denseBalls {a b θ : ℝ≥0} {hθ1 : θ ≤ 1}
    (s' : Finset ι) (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (𝒮 : Finset (Slab θ hθ1))
    (Uloc : Slab θ hθ1 → Set (EuclideanSpace ℝ (Fin 3)))
    (Dg : Slab θ hθ1 → (Fin 3 → ℝ) → Finset (Fin 3 → ℤ))
    (Gbox : Slab θ hθ1 → (Fin 3 → ℝ) → (Fin 3 → ℤ) → Set (EuclideanSpace ℝ (Fin 3)))
    (Cmult t : ℝ≥0) (εint : ℝ) (Nov : ℕ)
    (hb : 0 < b) (hθ : 0 < θ) (ha : 0 < a) (hCmult : 0 < Cmult) (hNov : 1 ≤ Nov)
    (hUlocMeas : ∀ S ∈ 𝒮, MeasurableSet (Uloc S))
    (hUlocU : ∀ S ∈ 𝒮, Uloc S ⊆ ⋃ i ∈ s', (Y' i).shade)
    (hoverlap : ∀ x, (𝒮.filter fun S => x ∈ Uloc S).card ≤ Nov)
    (hGmeas : ∀ S sh q, MeasurableSet (Gbox S sh q))
    (hret : ∀ S ∈ 𝒮, ∀ sh ∈ gridShiftSet, ∀ q ∈ Dg S sh,
      volume (Uloc S ∩ ((shiftedSlabBox S b sh q).carrier :
          Set (EuclideanSpace ℝ (Fin 3))))
        ≤ 2 * volume ((Uloc S ∩ ((shiftedSlabBox S b sh q).carrier :
            Set (EuclideanSpace ℝ (Fin 3)))) ∩ Gbox S sh q))
    (hball : ∀ S ∈ 𝒮, ∀ sh ∈ gridShiftSet, ∀ q ∈ Dg S sh, ∀ y ∈ Gbox S sh q,
      ∃ c : EuclideanSpace ℝ (Fin 3), y ∈ thetaBall θ b c ∧
        (t : ENNReal) * volume (thetaBall θ b c)
          ≤ volume (((Uloc S ∩ ((shiftedSlabBox S b sh q).carrier :
              Set (EuclideanSpace ℝ (Fin 3)))) ∩ Gbox S sh q) ∩ thetaBall θ b c))
    (hC : ShadedBody.HasCConstantMultiplicity s' Y' (Cmult * a ^ (-εint)))
    (hcap : volume (⋃ i ∈ s', (Y' i).shade)
      ≤ 2 * volume ((⋃ i ∈ s', (Y' i).shade) ∩ goodBoxUnionLocal 𝒮 b Uloc Dg)) :
    ShadedBody.IsCRefinement s'
        (fun i => ShadedBody.restrictShade (Y' i) (denseBallUnion 𝒮 Dg Gbox)
          (measurableSet_denseBallUnion 𝒮 Dg Gbox hGmeas)) s' Y'
        ((256 * (Nov : ℝ≥0) * Cmult)⁻¹ * a ^ εint) ∧
      ∀ x : EuclideanSpace ℝ (Fin 3),
        ((⋃ i ∈ s', (ShadedBody.restrictShade (Y' i) (denseBallUnion 𝒮 Dg Gbox)
            (measurableSet_denseBallUnion 𝒮 Dg Gbox hGmeas)).shade) ∩
          Metric.closedBall x ((θ * b : ℝ≥0) : ℝ)).Nonempty →
          (t : ENNReal) * volume (Metric.closedBall x ((θ * b : ℝ≥0) : ℝ))
            ≤ volume ((⋃ i ∈ s', (ShadedBody.restrictShade (Y' i) (denseBallUnion 𝒮 Dg Gbox)
                (measurableSet_denseBallUnion 𝒮 Dg Gbox hGmeas)).shade) ∩
              Metric.closedBall x
                ((Kakeya.plankReduction.ballDilation : ℝ) * ((θ * b : ℝ≥0) : ℝ))) := by
  classical
  set Gtot := denseBallUnion 𝒮 Dg Gbox with hGtotDef
  have hGtotMeas : MeasurableSet Gtot := measurableSet_denseBallUnion 𝒮 Dg Gbox hGmeas
  have hKpos : (0 : ℝ≥0) < 256 * (Nov : ℝ≥0) := by
    have : (0 : ℝ≥0) < (Nov : ℝ≥0) := by
      exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hNov
    positivity
  -- the aggregated capture
  have hagg : volume (⋃ i ∈ s', (Y' i).shade)
      ≤ (256 * (Nov : ENNReal)) * volume ((⋃ i ∈ s', (Y' i).shade) ∩ Gtot) := by
    refine volume_le_mul_volume_inter_of_localCapture 𝒮 b Uloc Dg Gbox
      (⋃ i ∈ s', (Y' i).shade) Gtot Nov hb hθ hUlocMeas hGtotMeas hUlocU ?_ hoverlap hret hcap
    intro S hS sh hsh q hq
    exact subset_denseBallUnion hS hsh hq
  have haggK : volume (⋃ i ∈ s', (Y' i).shade)
      ≤ ((256 * (Nov : ℝ≥0) : ℝ≥0) : ENNReal) *
          volume ((⋃ i ∈ s', (Y' i).shade) ∩ Gtot) := by
    have hcoe : ((256 * (Nov : ℝ≥0) : ℝ≥0) : ENNReal) = 256 * (Nov : ENNReal) := by
      push_cast
      ring
    rw [hcoe]
    exact hagg
  -- the refinement
  have href := isCRefinement_restrictShade_of_localCapture s' Y' Cmult εint
    (256 * (Nov : ℝ≥0)) hCmult ha hKpos Gtot hGtotMeas hC haggK
  refine ⟨href, ?_⟩
  -- the arbitrary-centre ball density
  have hcover := denseBallCover_of_localDenseBalls s' Y' 𝒮 Uloc Dg Gbox t hUlocU hball
  intro x hmeet
  have hrw : (⋃ i ∈ s', (ShadedBody.restrictShade (Y' i) Gtot hGtotMeas).shade)
      = (⋃ i ∈ s', (Y' i).shade) ∩ Gtot := biUnion_restrictShade_shade s' Y' Gtot hGtotMeas
  rw [hrw] at hmeet ⊢
  exact localDensity_of_denseBallCover (theta := θ) (b := b)
    ((⋃ i ∈ s', (Y' i).shade) ∩ Gtot) t hcover x hmeet

end Plank

end
