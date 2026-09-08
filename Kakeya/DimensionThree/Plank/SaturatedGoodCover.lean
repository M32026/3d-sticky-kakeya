/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.LocalAngleConcentration
public import Kakeya.DimensionThree.Plank.DenseBox

/-!
# The good-cover selection for *saturated* local families

The retired fibre-local good-cover layer built a cover whose local families were
`repr`-fibre-local, `T_q^u ⊆ F_u`.  Hypothesis (5) of the dense-box chain cannot be asked of those
(`Plank.not_localAngleConcentration_of_singleton`), and the repair is to test the boxes against the
*saturated* families instead: `T_q = {i ∈ s | (Y i).shade ∩ B_q^{(1/2)} ≠ ∅}`, for which (5) is a
theorem (`Plank.localAngleConcentration_of_saturated`) and tangentiality is automatic
(`Plank.comparableScalars_of_mem_halfBox`).

This file carries out the selection steps of that route.  Each is stated over an abstract
per-box region `R q ⊆ B_q` — the intended instance is the middle half `Plank.halfSlabBox` — so that
the region-dependence is a parameter rather than a repeated construction.

* `Plank.goodBoxes_saturated_retainedMass` — Step 1: the box-level Markov step on the captured
  mass, returning the good boxes at `cLam = c_good c_stb / (128 c_tan)` together with half the mass.
* `Plank.fibreLocalScore_ne_top` — Step 2: finiteness of the fibre-local good-box score, which is
  what lets the C-linear route divide it by its normalisation.
* `Plank.boxCount_of_goodBoxScore_saturated_var` — Step 3: the covering fraction of the undilated
  representative prism at an arbitrary cover fraction `κ`, with the cut region an arbitrary set.
* `Plank.cover_dilatedPrism_of_boxesMeeting` — Step 4: the covering fraction of the fixed dilation,
  at `κ / C_box³`, `C_box = 4 C_ang + 8 + C_c`.

The shading of a plank is cut against a fixed dilation `(Pr (rep i))^{(C_c)}` of its representative
rather than against `Pr (rep i)`: a thickened representative is the thickening of the *selected*
plank of the fibre, comparable to the plank's own only up to a fixed constant, so the undilated
containment is not available.  Steps 3 and 4 are stated accordingly — Step 3 for an arbitrary cut
region, Step 4 for boxes selected by meeting the dilation — and the whole cost is the enlargement of
the output dilation from `4 C_ang + 8` to `4 C_ang + 8 + C_c`.

Step 1 is `Plank.markov_retained_half` at explicit constants, and its numeric side condition
`1024 c_tan cLam ≤ 8 c_good c_stb` holds with equality, so nothing is wasted.

Both `c_good` (from the middle-half mass capture) and `c_stb` (the refinement loss of the stable
refinement) enter only as parameters, so every constant produced here is fixed before the geometric
data, exactly as in the good-cover section of
`Kakeya/DimensionThree/Plank/LocalAngleConcentration.lean`.
-/

@[expose] public section

open MeasureTheory Convexity
open scoped NNReal Real ENNReal

noncomputable section

namespace Plank

variable {ι : Type*}

/-! ## Step 1: the good boxes of the captured window -/

/-- A box failing the box-normalised threshold carries at most the threshold weight: either its
local family is empty, and then it carries no mass at all, or the threshold inequality simply
fails. -/
private lemma localMass_le_of_not_goodBox (T : Finset ι) (m : ι → ENNReal) (t w : ENNReal)
    (hg : ¬ (T.Nonempty ∧ t * ((T.card : ENNReal) * w) ≤ ∑ i ∈ T, m i)) :
    ∑ i ∈ T, m i ≤ t * ((T.card : ENNReal) * w) := by
  -- (extracted by Fuse golfer)
  by_cases hne : T.Nonempty
  · exact (not_le.mp fun h => hg ⟨hne, h⟩).le
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty]
    exact zero_le

/-- **Step 1: the box-level Markov step for the saturated families.**  `T q` is any local family
inside `s` whose members are tangential to `B_q` at `c_tan`, and `Z q` is its shading restricted to
an arbitrary region `R q` (the intended instance being the middle half `Plank.halfSlabBox`).  If the
window `𝒦` captures `8 c_good c_stb a^η · ab · |s|` of the region-restricted mass, then the boxes
clearing the box-normalised threshold

`b · (c_good c_stb / (128 c_tan) · a^η) ≤ λ(T q, Z q)`

still carry half of it.  This is the box-level Markov step run over the whole family `s`
rather than one `repr`-fibre, with the region allowed to depend on the box and the refinement loss
`c_stb` carried; the bad-box charge is `Plank.badBoxes_localMass_le`, which is region-free, and the
numeric condition `1024 c_tan · cLam ≤ 8 c_good c_stb` holds with equality at the stated `cLam`.
The fullness conversion is `Plank.localFullness_of_goodBox`. -/
theorem goodBoxes_saturated_retainedMass {a b θ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {hθ1 : θ ≤ 1}
    (cTan cGood cStb : ℝ≥0) (hcTan : 1 ≤ cTan) (S : Slab θ hθ1) (sh : Fin 3 → ℝ)
    (𝒦 : Finset (Fin 3 → ℤ)) (s : Finset ι) (V : ι → Plank a b hab hb1)
    (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (T : (Fin 3 → ℤ) → Finset ι)
    (Z : (Fin 3 → ℤ) → ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (R : (Fin 3 → ℤ) → Set (EuclideanSpace ℝ (Fin 3))) (η : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hθ : 0 < θ)
    (hTs : ∀ q, T q ⊆ s)
    (hZsh : ∀ q, ∀ i ∈ T q, (Z q i).shade = (Y i).shade ∩ R q)
    (hZcar : ∀ q, ∀ i ∈ T q, (Z q i).carrier = (V i).carrier)
    (htan : ∀ q, ∀ i ∈ T q, Kakeya.ComparableScalars cTan
      (volume (((V i).carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩
        (shiftedSlabBox S b sh q).carrier)).toNNReal (a * b ^ 2))
    (hcap : ((8 * cGood * cStb * a ^ η * (a * b) : ℝ≥0) : ENNReal) * (s.card : ENNReal)
      ≤ ∑ q ∈ 𝒦, ∑ i ∈ T q, volume ((Y i).shade ∩ R q)) :
    ∃ Dg ⊆ 𝒦,
      (∀ q ∈ Dg, b * (cGood * cStb / (128 * cTan) * a ^ η)
          ≤ ShadedBody.fullness (T q) (Z q)) ∧
        ((4 * cGood * cStb * a ^ η * (a * b) : ℝ≥0) : ENNReal) * (s.card : ENNReal)
          ≤ ∑ q ∈ Dg, ∑ i ∈ T q, volume ((Y i).shade ∩ R q) := by
  classical
  have h128 : (128 * cTan : ℝ≥0) ≠ 0 :=
    mul_ne_zero (by norm_num) (zero_lt_one.trans_le hcTan).ne'
  -- The good boxes: a nonempty local family clearing the box-normalised threshold.
  let good : (Fin 3 → ℤ) → Prop := fun q => (T q).Nonempty ∧
    ((b * (cGood * cStb / (128 * cTan) * a ^ η) : ℝ≥0) : ENNReal) *
        (((T q).card : ENNReal) * ((8 * a * b : ℝ≥0) : ENNReal))
      ≤ ∑ i ∈ T q, volume ((Y i).shade ∩ R q)
  -- The numeric side condition, which holds with equality at this threshold.
  have hτw : 2 * (((b * (cGood * cStb / (128 * cTan) * a ^ η) : ℝ≥0) : ENNReal) *
        ∑ q ∈ 𝒦, (((T q).card : ENNReal) * ((8 * a * b : ℝ≥0) : ENNReal)))
      ≤ ((8 * cGood * cStb * a ^ η * (a * b) : ℝ≥0) : ENNReal) * (s.card : ENNReal) := by
    have hnn : (2 : ℝ≥0) * (512 * cTan * (cGood * cStb / (128 * cTan) * a ^ η) * (a * b))
        = 8 * cGood * cStb * a ^ η * (a * b) :=
      calc (2 : ℝ≥0) * (512 * cTan * (cGood * cStb / (128 * cTan) * a ^ η) * (a * b))
          = 8 * (cGood * cStb / (128 * cTan) * (128 * cTan)) * a ^ η * (a * b) := by ring
        _ = 8 * cGood * cStb * a ^ η * (a * b) := by rw [div_mul_cancel₀ _ h128]; ring
    refine (mul_le_mul_right (badBoxes_localMass_le cTan
      (cGood * cStb / (128 * cTan) * a ^ η) S hb hθ sh 𝒦 s V T hTs htan) 2).trans_eq ?_
    rw [← hnn]
    push_cast
    ring
  have hkey := markov_retained_half 𝒦 (fun q => ∑ i ∈ T q, volume ((Y i).shade ∩ R q))
    (fun q => ((T q).card : ENNReal) * ((8 * a * b : ℝ≥0) : ENNReal))
    (((b * (cGood * cStb / (128 * cTan) * a ^ η) : ℝ≥0) : ENNReal))
    (((8 * cGood * cStb * a ^ η * (a * b) : ℝ≥0) : ENNReal) * (s.card : ENNReal))
    hcap hτw (ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.natCast_ne_top _)) good
    fun q _ hg => localMass_le_of_not_goodBox _ _ _ _ hg
  refine ⟨𝒦.filter good, Finset.filter_subset _ _, ?_,
    (ENNReal.mul_le_mul_iff_right (by norm_num : (2 : ENNReal) ≠ 0)
      (by norm_num : (2 : ENNReal) ≠ ⊤)).mp (le_of_eq_of_le (by push_cast; ring) hkey)⟩
  rintro q hq
  obtain ⟨-, hne, hg⟩ := Finset.mem_filter.mp hq
  exact localFullness_of_goodBox (cGood * cStb / (128 * cTan) * a ^ η) (T q) V (Z q) ha hb hne
    (hZcar q) (hg.trans_eq (Finset.sum_congr rfl fun i hi => by rw [hZsh q i hi]))

/-- **Step 1 at a free threshold scale, in discarded-mass form.**  The same box-level Markov
selection as `Plank.goodBoxes_saturated_retainedMass`, but with the box-normalised threshold scale
`lamScale` left free and the conclusion stated on the *discarded* boxes rather than on the retained
ones.

No captured-mass hypothesis is needed: the statement only charges the boxes that fail the threshold,
which is `Plank.markov_discarded_le` composed with the region-free bad-box estimate
`Plank.badBoxes_localMass_le`.  That is what a caller composing with
`Plank.union_capture_of_sum_capture` needs, since the admissible discard fraction there is dictated
by the constant multiplicity and is not `1/2`.

Both forms of the discarded bound are returned: the raw weight-sum form
`b · lamScale · ∑_q #(T q) · 8ab`, which is what a further Markov step consumes, and the normalised
form `512 c_tan · lamScale · ab · #s`, in which the extra factor `b` of the threshold has cancelled
the `1/b` of the incidence count. -/
theorem goodBoxes_saturated_discarded {a b θ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {hθ1 : θ ≤ 1}
    (cTan lamScale : ℝ≥0) (S : Slab θ hθ1) (sh : Fin 3 → ℝ)
    (𝒦 : Finset (Fin 3 → ℤ)) (s : Finset ι) (V : ι → Plank a b hab hb1)
    (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (T : (Fin 3 → ℤ) → Finset ι)
    (Z : (Fin 3 → ℤ) → ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (R : (Fin 3 → ℤ) → Set (EuclideanSpace ℝ (Fin 3)))
    (ha : 0 < a) (hb : 0 < b) (hθ : 0 < θ)
    (hTs : ∀ q, T q ⊆ s)
    (hZsh : ∀ q, ∀ i ∈ T q, (Z q i).shade = (Y i).shade ∩ R q)
    (hZcar : ∀ q, ∀ i ∈ T q, (Z q i).carrier = (V i).carrier)
    (htan : ∀ q, ∀ i ∈ T q, Kakeya.ComparableScalars cTan
      (volume (((V i).carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩
        (shiftedSlabBox S b sh q).carrier)).toNNReal (a * b ^ 2)) :
    ∃ Dg ⊆ 𝒦,
      (∀ q ∈ Dg, b * lamScale ≤ ShadedBody.fullness (T q) (Z q)) ∧
      (∑ q ∈ 𝒦 \ Dg, ∑ i ∈ T q, volume ((Y i).shade ∩ R q)
        ≤ ((b * lamScale : ℝ≥0) : ENNReal) *
            ∑ q ∈ 𝒦, (((T q).card : ENNReal) * ((8 * a * b : ℝ≥0) : ENNReal))) ∧
      (∑ q ∈ 𝒦 \ Dg, ∑ i ∈ T q, volume ((Y i).shade ∩ R q)
        ≤ ((512 * cTan * lamScale * (a * b) : ℝ≥0) : ENNReal) * (s.card : ENNReal)) := by
  classical
  -- The good boxes: a nonempty local family clearing the box-normalised threshold.
  let good : (Fin 3 → ℤ) → Prop := fun q => (T q).Nonempty ∧
    ((b * lamScale : ℝ≥0) : ENNReal) * (((T q).card : ENNReal) * ((8 * a * b : ℝ≥0) : ENNReal))
      ≤ ∑ i ∈ T q, volume ((Y i).shade ∩ R q)
  have hdisc := markov_discarded_le 𝒦 (fun q => ∑ i ∈ T q, volume ((Y i).shade ∩ R q))
    (fun q => ((T q).card : ENNReal) * ((8 * a * b : ℝ≥0) : ENNReal))
    (((b * lamScale : ℝ≥0) : ENNReal)) good
    fun q _ hg => localMass_le_of_not_goodBox _ _ _ _ hg
  rw [Finset.filter_not] at hdisc
  refine ⟨𝒦.filter good, Finset.filter_subset _ _, ?_, hdisc,
    hdisc.trans (badBoxes_localMass_le cTan lamScale S hb hθ sh 𝒦 s V T hTs htan)⟩
  rintro q hq
  obtain ⟨-, hne, hg⟩ := Finset.mem_filter.mp hq
  exact localFullness_of_goodBox lamScale (T q) V (Z q) ha hb hne (hZcar q)
    (hg.trans_eq (Finset.sum_congr rfl fun i hi => by rw [hZsh q i hi]))

/-! ## Step 2: finiteness of the fibre-local good-box score -/

/-- **The fibre-local good-box score is finite.**  Needed only by the C-linear route, where the
score is divided by its normalisation to produce a `ℝ≥0`-valued cover fraction: the passage
`ENNReal → ℝ≥0` is faithful exactly when the score is not `⊤`.

The bound is crude and absolute — every summand sits inside a single box, of volume `8θb³` — which
is all that is wanted; no tangentiality is used. -/
theorem fibreLocalScore_ne_top {b θ : ℝ≥0} {hθ1 : θ ≤ 1} (S : Slab θ hθ1) (sh : Fin 3 → ℝ)
    (Dg : Finset (Fin 3 → ℤ)) (Tl : (Fin 3 → ℤ) → Finset ι)
    (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (R : (Fin 3 → ℤ) → Set (EuclideanSpace ℝ (Fin 3)))
    (Pset : Set (EuclideanSpace ℝ (Fin 3)))
    (hR : ∀ q, R q ⊆ ((shiftedSlabBox S b sh q).carrier : Set (EuclideanSpace ℝ (Fin 3)))) :
    ∑ q ∈ Dg, ∑ i ∈ Tl q, volume ((Y i).shade ∩ R q ∩ Pset) ≠ ⊤ := by
  -- Every summand sits inside a single box, of volume `8θb³ < ⊤`.
  refine (ENNReal.sum_lt_top.mpr fun q _ => ENNReal.sum_lt_top.mpr fun i _ =>
    (measure_mono fun x hx => hR q hx.1.2).trans_lt
      ((shiftedSlabBox_volume S b sh q).trans_lt (by finiteness))).ne

/-! ## Step 3: the covering fraction of the undilated prism -/

open scoped Classical in
/-- **Step 3: from the retained score to the covering fraction.**  A representative whose
fibre-local good-box score clears `2 c_good c_stb a^η · ab · |F|` has, among the good boxes, at
least `κ₀ a^η / b` that meet its prism, i.e.

`κ₀ a^η · |Pr| ≤ ∑_{q ∈ D} |B_q|`,  `κ₀ = 2 c_good c_stb / c_tan`,

where `D` is the set of good boxes meeting the cut region `P_set`.  This is
`Plank.boxVolumeSum_of_goodBoxMass` fed with the *retained score* rather than with the good-box
threshold, which is what makes `κ₀` carry `c_good` and not `cLam`.  Two monotonicity steps are used,
both in the favourable direction: the score is collected on `R q ⊆ B_q` whereas that lemma measures
it on `B_q`, and the boxes not meeting `P_set` carry no score at all, so restricting the sum to `D`
loses nothing.

The cut region is an arbitrary set, not the carrier of a typed prism: the saturated route cuts
against a fixed *dilation* of the representative, and the conclusion is therefore stated at the
numeric prism volume `8θb²`. -/
theorem boxCount_of_goodBoxScore_saturated_var {a b θ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
    {hθ1 : θ ≤ 1}
    (cTan κ : ℝ≥0) (hcTan : 1 ≤ cTan) (S : Slab θ hθ1) (sh : Fin 3 → ℝ)
    (Dg : Finset (Fin 3 → ℤ)) (F : Finset ι) (V : ι → Plank a b hab hb1)
    (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (Tl : (Fin 3 → ℤ) → Finset ι)
    (R : (Fin 3 → ℤ) → Set (EuclideanSpace ℝ (Fin 3)))
    (Pset : Set (EuclideanSpace ℝ (Fin 3)))
    (ha : 0 < a) (hb : 0 < b) (hFne : F.Nonempty)
    (hTl : ∀ q, Tl q ⊆ F)
    (hR : ∀ q, R q ⊆ ((shiftedSlabBox S b sh q).carrier : Set (EuclideanSpace ℝ (Fin 3))))
    (hshV : ∀ i ∈ F, (Y i).shade ⊆ ((V i).carrier : Set (EuclideanSpace ℝ (Fin 3))))
    (htan : ∀ q, ∀ i ∈ Tl q, Kakeya.ComparableScalars cTan
      (volume (((V i).carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩
        (shiftedSlabBox S b sh q).carrier)).toNNReal (a * b ^ 2))
    (hscore : ((κ * cTan * (a * b) : ℝ≥0) : ENNReal) * (F.card : ENNReal)
      ≤ ∑ q ∈ Dg, ∑ i ∈ Tl q, volume ((Y i).shade ∩ R q ∩ Pset)) :
    (κ : ENNReal) * ((8 * θ * b * b : ℝ≥0) : ENNReal)
      ≤ ∑ q ∈ Dg with (((shiftedSlabBox S b sh q).carrier :
            Set (EuclideanSpace ℝ (Fin 3))) ∩ Pset).Nonempty,
          volume ((shiftedSlabBox S b sh q).carrier) := by
  classical
  -- Boxes not meeting `Pset` carry no score, and the score on `R q ⊆ B q` is at most that on `B q`.
  refine boxVolumeSum_of_goodBoxMass cTan κ hcTan S sh _ F V Y Tl Pset ha hb hFne hTl hshV htan ?_
  refine hscore.trans ((Finset.sum_subset (Finset.filter_subset _ _)
    fun q hq hq' => Finset.sum_eq_zero fun i _ => measure_mono_null
      (fun x hx => hq' (Finset.mem_filter.mpr ⟨hq, x, hR q hx.1.2, hx.2⟩)) measure_empty).ge.trans
    (Finset.sum_le_sum fun q _ => Finset.sum_le_sum fun i _ =>
      measure_mono (Set.inter_subset_inter_left _ (Set.inter_subset_inter_right _ (hR q)))))

/-! ## Step 4: the covering fraction of the dilated prism -/

/-- Volume of the scaled prism: dilating a `PrismNDim` by `C` multiplies its volume by `C^3` in
dimension 3. -/
lemma volume_dilation (P : PrismNDim 3 (EuclideanSpace ℝ (Fin 3)) (EuclideanSpace ℝ (Fin 3)))
    (C : ℝ≥0) : volume (P.dilation C).carrier = ((C : ℝ≥0) ^ 3 : ENNReal) * volume P.carrier := by
  rw [PrismNDim.volume_carrier, PrismNDim.volume_carrier, finrank_euclideanSpace_fin]
  simp only [PrismNDim.dilation_thicknesses, ENNReal.coe_mul, Fin.prod_univ_three]
  ring

/-- **Step 4: the covering fraction survives a fixed dilation, at a fixed price.**  Every box
meeting the fixed dilation `Pr^{(C_c)}` of the representative prism lies in the larger dilation
`Pr^{(4 Cang + 8 + C_c)}` (`Plank.shiftedSlabBox_subset_dilation_of_meet_dilation`), and since a
dilation multiplies the three half-widths, `|Pr^{(C)}| = C³ |Pr|`; so a covering fraction `κ` for
`Pr` is a covering fraction `κ / C³` for `Pr^{(C)}`.  The price is paid once, in a constant fixed
before every geometric datum, and is invisible in the exponent of `a`.

A covering fraction for a prism is *not* one for its dilation, which is why this step exists: the
dilated form is what the saturated route needs, because the region its local families are saturated
for is the middle half of a box, not the box intersected with the prism.

The boxes are selected by meeting `Pr^{(C_c)}` rather than `Pr` itself because the shading of a
plank is only known to sit in a fixed dilation of its representative, never in the representative;
`C_c = 1` recovers the undilated selection up to the harmless enlargement of the output constant
from `4 Cang + 8` to `4 Cang + 9`. -/
theorem cover_dilatedPrism_of_boxesMeeting {θ b : ℝ≥0} {hθb : θ * b ≤ b} {hb1 : b ≤ 1}
    {hθ1 : θ ≤ 1} (S : Slab θ hθ1) (sh : Fin 3 → ℝ) (D : Finset (Fin 3 → ℤ))
    (Pr : Prism3D (θ * b) b 1 hθb hb1) (Cang Cc κ : ℝ≥0) (hCang : 1 ≤ Cang) (hCc : 1 ≤ Cc)
    (hθ0 : 0 < θ) (hb0 : 0 < b)
    (hang : Prism3D.angle Pr S ≤ (Cang : ℝ) * (θ : ℝ))
    (hmeet : ∀ q ∈ D, (((shiftedSlabBox S b sh q).carrier :
        Set (EuclideanSpace ℝ (Fin 3))) ∩
      ((Pr.toPrismNDim.dilation Cc).carrier : Set (EuclideanSpace ℝ (Fin 3)))).Nonempty)
    (hcov : (κ : ENNReal) * volume ((Pr.carrier : Set (EuclideanSpace ℝ (Fin 3))))
      ≤ ∑ q ∈ D, volume ((shiftedSlabBox S b sh q).carrier)) :
    (∀ q ∈ D, ((shiftedSlabBox S b sh q).carrier : Set (EuclideanSpace ℝ (Fin 3)))
        ⊆ ((Pr.toPrismNDim.dilation (4 * Cang + 8 + Cc)).carrier :
            Set (EuclideanSpace ℝ (Fin 3)))) ∧
      ((κ / (4 * Cang + 8 + Cc) ^ 3 : ℝ≥0) : ENNReal) *
          volume ((Pr.toPrismNDim.dilation (4 * Cang + 8 + Cc)).carrier :
            Set (EuclideanSpace ℝ (Fin 3)))
        ≤ ∑ q ∈ D, volume ((shiftedSlabBox S b sh q).carrier) := by
  have hC3 : ((4 * Cang + 8 + Cc : ℝ≥0) ^ 3) ≠ 0 := by positivity
  refine ⟨fun q hq => shiftedSlabBox_subset_dilation_of_meet_dilation S sh q Pr Cang Cc hCang hCc
    hθ0 hb0 hang (hmeet q hq), ?_⟩
  rw [volume_dilation, ← mul_assoc, ← ENNReal.coe_pow, ← ENNReal.coe_mul, div_mul_cancel₀ _ hC3]
  exact hcov

/-! ## Item 2 on the dilated representative

The four steps above are assembled into a good cover by
`Plank.exists_goodCover_saturated_aggregate` in
`Kakeya/DimensionThree/Plank/LinearCoverRoute.lean`, which keeps every representative rather than
Markov-selecting a subfamily; it is downstream both of this file and of
`Kakeya/DimensionThree/Plank/ShadingAggregation.lean`.
-/

/-- **`(♦)` on the dilated prism, from a saturated good cover.**
The retired per-representative density with the representative prism `P`
replaced by a fixed dilation `Q = P^{(C_box)}` and with the containment form
`Plank.density_transfer_of_boxes` in place of the intersected form.

The change is forced by the saturation.  The intersected transfer wants a per-box density relative
to `U ∩ P`, i.e. for local shades already restricted to the representative prism; saturating for the
middle half of a box *alone* is precisely the decision not to restrict them, so the local
shades here are only asked to satisfy `(Z q i).shade ⊆ (Y i).shade ∩ B_q`.  What replaces the
restriction is the hypothesis `hbox : B_q ⊆ Q` for `q ∈ D`, which turns `U ∩ B_q` into `(U ∩ Q)
∩ B_q` and is exactly
what `Plank.shiftedSlabBox_subset_dilation_of_meet` supplies.  The overlap constant is the absolute
`8` of `Plank.shiftedSlabBox_sum_inter_volume_le`, so `cDia = cDense / 8` is unchanged. -/
theorem perRepresentativeDensity_saturated_dilated (cTan Ceta : ℝ≥0) (hCeta : 0 < Ceta) :
    ∃ cDia : ℝ≥0, 0 < cDia ∧
      ∀ {a b θ : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {hθb : θ * b ≤ b} {hθ1 : θ ≤ 1} {ι : Type*}
        (s : Finset ι) (V : ι → Plank a b hab hb1)
        (Y : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
        (S : Slab θ hθ1) (t : Fin 3 → ℝ) (P : Prism3D (θ * b) b 1 hθb hb1) (Cbox : ℝ≥0)
        (D : Finset (Fin 3 → ℤ))
        (Tq : (Fin 3 → ℤ) → Finset ι)
        (Z : (Fin 3 → ℤ) → ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
        (η : ℝ) (θ0 : (Fin 3 → ℤ) → ℝ) (Mtyp Cstar cLam lam κ : ℝ≥0),
        0 < a → 0 < b → 0 < θ → 0 < η → 0 < cLam → a / b ≤ θ →
        (∀ q ∈ D, ((a / b : ℝ≥0) : ℝ) ≤ θ0 q) →
        (∀ q ∈ D, θ0 q ≤ 1) →
        (∀ q ∈ D, (θ : ℝ) ≤ (Cstar : ℝ) * θ0 q) →
        (Cstar : ENNReal) * (Mtyp : ENNReal) ≤ (Ceta : ENNReal) * (a : ENNReal) ^ (-η) →
        cLam * a ^ η ≤ lam →
        (∀ q, Tq q ⊆ s) →
        (∀ i ∈ s, (Y i).shade ⊆ ((V i).carrier : Set (EuclideanSpace ℝ (Fin 3)))) →
        (∀ q, ∀ i ∈ Tq q, (Z q i).shade
          ⊆ (Y i).shade ∩ ((shiftedSlabBox S b t q).carrier :
              Set (EuclideanSpace ℝ (Fin 3)))) →
        (∀ q, ∀ i ∈ Tq q, (Z q i).carrier = (V i).carrier) →
        (∀ q ∈ D, ∀ i ∈ Tq q, Kakeya.ComparableScalars cTan
          (volume (((V i).carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩
            (shiftedSlabBox S b t q).carrier)).toNNReal (a * b ^ 2)) →
        (∀ q ∈ D, b * lam ≤ ShadedBody.fullness (Tq q) (Z q)) →
        (∀ q ∈ D,
          (∑ i ∈ Tq q, ∑ j ∈ Tq q, volume ((Z q i).shade ∩ (Z q j).shade))
            ≤ (Mtyp : ENNReal) * (∑ i ∈ Tq q, ∑ j ∈ Tq q with
                (θ0 q - ((a / b : ℝ≥0) : ℝ) ≤ Prism3D.angle (V i) (V j) ∧
                  Prism3D.angle (V i) (V j) ≤ 2 * θ0 q),
              volume ((Z q i).shade ∩ (Z q j).shade))) →
        (∀ q ∈ D, ((shiftedSlabBox S b t q).carrier : Set (EuclideanSpace ℝ (Fin 3)))
          ⊆ ((P.toPrismNDim.dilation Cbox).carrier : Set (EuclideanSpace ℝ (Fin 3)))) →
        ((κ : ENNReal) *
            volume ((P.toPrismNDim.dilation Cbox).carrier :
              Set (EuclideanSpace ℝ (Fin 3)))
          ≤ ∑ q ∈ D, volume ((shiftedSlabBox S b t q).carrier)) →
        ((cDia * cLam * a ^ (2 * η) * lam * κ : ℝ≥0) : ENNReal) *
            volume ((P.toPrismNDim.dilation Cbox).carrier :
              Set (EuclideanSpace ℝ (Fin 3)))
          ≤ volume ((⋃ i ∈ s, (Y i).shade) ∩
              ((P.toPrismNDim.dilation Cbox).carrier :
                Set (EuclideanSpace ℝ (Fin 3)))) := by
  obtain ⟨cDense, hcDense, hdensebox⟩ := denseBoxEstimate_boxNormalised_combined cTan Ceta hCeta
  refine ⟨cDense / 8, div_pos hcDense (by norm_num), ?_⟩
  intro a b θ hab hb1 hθb hθ1 ι s V Y S t P Cbox D Tq Z η θ0 Mtyp Cstar cLam lam κ ha hb hθ hη
    hcLam habθ habθ0 hθ01 hθθ0 hMtyp_combined hlam_lb hTsub hsh hZsh hZcar htan hlam hconc hbox
    hcover
  set Qset := ((P.toPrismNDim.dilation Cbox).carrier : Set (EuclideanSpace ℝ (Fin 3)))
  have hmeas : MeasurableSet ((⋃ i ∈ s, (Y i).shade) ∩ Qset) :=
    (Finset.measurableSet_biUnion s fun i _ => (Y i).measurableSet_shade).inter
      (P.toPrismNDim.dilation Cbox).measurableSet_carrier
  have hdense : ∀ q ∈ D,
      ((cDense * cLam * a ^ (2 * η) * lam : ℝ≥0) : ENNReal) *
          volume ((shiftedSlabBox S b t q).carrier)
        ≤ volume ((⋃ i ∈ s, (Y i).shade) ∩ (shiftedSlabBox S b t q).carrier) := fun q hq =>
    (hdensebox (Tq q) V (Z q) θ hθ1 (shiftedSlabBox S b t q) η (θ0 q) Mtyp Cstar cLam lam
        ha hb hη habθ
        (nonempty_of_pos_le_fullness (Tq q) (Z q)
          (mul_pos hb ((mul_pos hcLam (NNReal.rpow_pos ha)).trans_le hlam_lb)) (hlam q hq))
        (fun i hi => (hZsh q i hi).trans (Set.inter_subset_inter_left _ (hsh i (hTsub q hi))))
        (htan q hq) (hZcar q) (habθ0 q hq) (hθ01 q hq) (hθθ0 q hq) hMtyp_combined hlam_lb
        (hlam q hq) (hconc q hq)).trans
      (measure_mono (Set.iUnion₂_subset fun i hi x hx =>
        (hZsh q i hi hx).imp_left (Set.mem_biUnion (hTsub q hi))))
  have htrans := density_transfer_of_boxes D
    (fun q => ((shiftedSlabBox S b t q).carrier : Set (EuclideanSpace ℝ (Fin 3))))
    Qset (⋃ i ∈ s, (Y i).shade)
    ((cDense * cLam * a ^ (2 * η) * lam : ℝ≥0) : ENNReal) (κ : ENNReal) 8
    hbox hdense hcover (shiftedSlabBox_sum_inter_volume_le S hb hθ t D hmeas)
  have hnn : (8 : ℝ≥0) * (cDense / 8 * cLam * a ^ (2 * η) * lam * κ)
      = cDense * cLam * a ^ (2 * η) * lam * κ :=
    calc (8 : ℝ≥0) * (cDense / 8 * cLam * a ^ (2 * η) * lam * κ)
        = cDense / 8 * 8 * (cLam * a ^ (2 * η) * lam * κ) := by ring
      _ = cDense * cLam * a ^ (2 * η) * lam * κ := by
          rw [div_mul_cancel₀ _ (by norm_num : (8 : ℝ≥0) ≠ 0)]; ring
  have hrw : (8 : ENNReal) * ((cDense / 8 * cLam * a ^ (2 * η) * lam * κ : ℝ≥0) : ENNReal)
      = ((cDense * cLam * a ^ (2 * η) * lam : ℝ≥0) : ENNReal) * (κ : ENNReal) := by
    rw [show (8 : ENNReal) = ((8 : ℝ≥0) : ENNReal) by norm_num, ← ENNReal.coe_mul, hnn,
      ← ENNReal.coe_mul]
  refine (ENNReal.mul_le_mul_iff_right (a := (8 : ENNReal)) (by norm_num) (by norm_num)).mp ?_
  rw [← mul_assoc, hrw]
  exact htrans

end Plank

end
