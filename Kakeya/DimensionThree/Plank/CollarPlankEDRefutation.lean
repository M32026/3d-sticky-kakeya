/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.CollarPlankPresentation
public import Kakeya.DimensionThree.Plank.GlobalPlankDatumBridge
public import Kakeya.DimensionThree.Volume

/-!
# The plank-presented outer family of GWZ 6.6(B) is not the representative family

GWZ Proposition 5.1 returns its outer shading on the `scale`-collar of the cell body, never on the
cell's representative plank (`ShadedBody.FactoringAndMultPropCoreAtScale.outer_carrier`).  The
collar does not fit inside an `a × b × 1` `Plank`: the long half-width of a plank is pinned at
`1` and the collar of a body reaching the working window reaches `1 + s`.  So the Section-6 outer
family has to be *presented*, and the presentation on this branch is the single common homothety
`Kakeya.collarPlank`, whose underlying plank is
`Kakeya.comparablePlankEnvelope.plank (windowConst R Cw) a b hab hb1 K` — the exact envelope of the
**shrunk** collar of the body `K` (`Kakeya.collarPlank_toPrism3D`).

Before steps, the small-`b` branch of Proposition 6.6(B)
(`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation_of_masterScaleLemma61`) obtained the pairwise
essential distinctness that its `γ = 0` application of Lemma 6.1 needs from the exported clause

`∀ x, (W x).toPrism3D = D.factor.repr x`

through `Kakeya.pairwise_isEssentiallyDistinct_of_toPrism3D_eq`.  That route is unavailable for a
presented family, and this file is the machine-checked reason.

## What is refuted, and why one witness does both

`Kakeya.collarPlank hR hCw hab hb1 K Y`'s plank depends on the body `K` **only** — the shading `Y`
enters the shade and not the prism, and the representative plank `D.factor.repr x` does not enter at
all.  Hence any two cells with the same body have the *same* presented plank, whatever their
representatives are.  The witness is exactly that configuration, and it is legal at every scale:

* the common body is `Kakeya.CollarPlankRefute.cellBody`, the quarter-scale prism with half-widths
  `(a/4, b/4, 1/4)`.  It has plank-comparable dimensions `Kakeya.IsPlankOfDimensions Cw a b` for
  every `Cw ≥ 4` — in particular for the `Cw = 128` of the Main-Lemma-2 call site
  (`Kakeya.ML2Reduction.PlankFactoringData.toGlobalPlankFactorization`) — and it lies in the working
  window at every radius `R ≥ 1`, so in the radius-`4` window of
  `Kakeya.Section6PartBFactorisation.repr_window`;
* the two representatives are `Kakeya.CollarPlankRefute.refPlank` at centres `± (a/2) e₀`.  Both
  contain the body, they are **distinct** planks, and they are **essentially distinct**: their
  intersection lies in the prism of half-widths `(a/2, b, 1)`, of volume `4ab`, exactly half of
  `8ab`.

Both refutations follow:

* `not_statement_of_universal_presentedPlank_eq_repr` — the identification cannot hold, since it
  would identify the two distinct representatives with the one presented plank;
* `not_statement_of_universal_presentedPlank_ED` — neither can the transport
  `ED(representatives) ⟹ ED(presented planks)`, since the two presented planks are *equal*, and a
  set of positive finite volume is never essentially distinct from itself
  (`not_isEssentiallyDistinct_self`).

The second is the sharper statement: it says that the clause the consumer actually needs is not
recoverable from the datum's own essential-distinctness hypothesis by any argument, so a presented
outer family owes that clause an **extraction** (the tree's tool is
`Kakeya.exists_pairwise_plank_subset_of_isThickeningNonconcentrated`, whose non-concentration input
is not supplied by `Kakeya.Section6PartBData`), not a transport.

Nothing here is specific to the ratio `Kakeya.comparablePlankEnvelope.shrink (windowConst R Cw)`:
the witness never computes the homothety.  It only uses that the presentation is a function of the
body.  The quantitative statement — that *every* position-shrinking presentation breaks essential
distinctness, because the borderline pair at transverse separation exactly `a` is essentially
distinct before the shrink and not after — is not needed for the refutation and is not claimed here.

## What the presented family owes instead, and with what

The clause `Kakeya.factoringAndMultPropGlobal` now exports is the outer family's own pairwise
essential distinctness.  For a homothety-presented family that is an **extraction**, and every step
of it except one is already proved on this branch:

* the extraction itself — `Kakeya.exists_pairwise_plank_subset_of_isThickeningNonconcentrated`, or
  its refinement form `Kakeya.exists_pairwise_plank_CRefinement_of_isThickeningNonconcentrated`,
  which returns the retained subfamily together with a
  `ShadedBody.IsCRefinement` of coefficient `(d + 1)⁻¹`;
* the fullness of the retained subfamily — `Kakeya.mul_fullness_le_of_isCRefinement`;
* the multiplicity comparison back to the full family —
  `ShadedBody.multiplicity_le_of_isCRefinement`;
* Katz--Tao, the window containment and the cardinality clause restrict to a subset for free.

What is **missing** is the extraction's own hypothesis,
`Plank.IsThickeningNonconcentrated ts (fun x => (W x).toPrism3D) C_NC (C * (b / a))`: a
conflict-degree count for the presented planks.  `Kakeya.Section6PartBData` carries no such datum —
its cell data are `body`, `cellOf`, `repr`, `body_le_repr`, `repr_window`,
`coarse_fibre_frostman`, `isKatzTao`, and nothing that separates two cells — and the refutations
below say the count cannot be manufactured from the datum's essential distinctness of the
representatives.  The tree's engine for such counts,
`Kakeya.exists_ED_directionCap_degree_bound` (used by
`Kakeya.exists_inner_plank_conflict_degree_bound` for the *inner* family), is stated for a family of
`Tube δ E`s at a single radius `δ`, with a direction cap of radius `A · δ` and a container of
volume at most `M · δ ^ (finrank - 1)`; an `a × b × 1` plank family has two transverse widths and is
not an instance of it.  Part (A) faced the same obstruction and resolved it by making the count an
explicit hypothesis of its proposition, `Kakeya.ParentOverlapAtDilatedPlanks`, converted by
`Kakeya.isThickeningNonconcentrated_of_parentOverlapAtDilatedPlanks`; that is the precedent for what
Part (B) will need, and whether the Main-Lemma-2 call site
(`Kakeya.ML2Reduction.exists_threshold_eccentric`) can supply it is not settled here.

## Fidelity

The clause that replaced the identification in `Kakeya.factoringAndMultPropGlobal` is the pairwise
essential distinctness of the outer family itself.  It is **weaker**:
`Kakeya.pairwise_isEssentiallyDistinct_of_toPrism3D_eq` derives it from the identification together
with the datum's hypothesis on the representatives, so every producer of the old form produces the
new one, and the top-level statements of Proposition 6.6(B)
(`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation` and
`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation_of_masterScaleLemma61`) are unchanged.
-/

@[expose] public section

open MeasureTheory Metric
open scoped ENNReal NNReal

noncomputable section

namespace Kakeya

/-! ### The witness family, and the two refutations -/

namespace CollarPlankRefute


abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-! ### The mechanism: the presented plank sees the body and nothing else -/

/-- **The presented plank does not depend on the shading.** -/
theorem toPrism3D_collarPlank_shade_irrelevant {R Cw a b : ℝ≥0} (hR : 1 ≤ R) (hCw : 1 ≤ Cw)
    (hab : a ≤ b) (hb1 : b ≤ 1) (K : ConvexSpaceBody E3) (Y₁ Y₂ : ShadedBody E3) :
    (collarPlank hR hCw hab hb1 K Y₁).toPrism3D
      = (collarPlank hR hCw hab hb1 K Y₂).toPrism3D := rfl

/-- **Equal bodies give the same presented plank**, whatever the two cells' representative planks
are.  This is the whole mechanism of the refutations below: the representative never enters
`Kakeya.collarPlank`. -/
theorem carrier_collarPlank_eq_of_body_eq {R Cw a b : ℝ≥0} (hR : 1 ≤ R) (hCw : 1 ≤ Cw)
    (hab : a ≤ b) (hb1 : b ≤ 1) {K₁ K₂ : ConvexSpaceBody E3} (hK : K₁ = K₂)
    (Y₁ Y₂ : ShadedBody E3) :
    ((collarPlank hR hCw hab hb1 K₁ Y₁).carrier : Set E3)
      = ((collarPlank hR hCw hab hb1 K₂ Y₂).carrier : Set E3) := by
  subst hK
  rfl

/-- An explicit `a × b × 1` plank: the standard orthonormal frame, centre `c`. -/
def refPlank (a b : ℝ≥0) (hab : a ≤ b) (hb1 : b ≤ 1) (c : E3) : Plank a b hab hb1 where
  toPrismNDim := PrismNDim.mk' c (EuclideanSpace.basisFun (Fin 3) ℝ) ![a, b, 1]
  thicknesses_eq := rfl

theorem mem_refPlank_iff {a b : ℝ≥0} (hab : a ≤ b) (hb1 : b ≤ 1) (c x : E3) :
    x ∈ (refPlank a b hab hb1 c).carrier ↔
      ∀ i, |x i - c i| ≤ ((![a, b, 1] i : ℝ≥0) : ℝ) := by
  rw [(refPlank a b hab hb1 c).mem_carrier_iff]
  simp [refPlank, PrismNDim.mk']

theorem center_refPlank {a b : ℝ≥0} (hab : a ≤ b) (hb1 : b ≤ 1) (c : E3) :
    (refPlank a b hab hb1 c).center = c := rfl

/-- The common cell body: the quarter-scale prism with the same frame, centred at the origin. -/
def cellBody (a b : ℝ≥0) (hab : a ≤ b) (hb1 : b ≤ 1) :
    Prism3D (a / 4) (b / 4) (1 / 4)
      (by exact div_le_div_of_nonneg_right hab (by norm_num))
      (by exact div_le_div_of_nonneg_right hb1 (by norm_num)) where
  toPrismNDim := PrismNDim.mk' (0 : E3) (EuclideanSpace.basisFun (Fin 3) ℝ) ![a / 4, b / 4, 1 / 4]
  thicknesses_eq := rfl

theorem mem_cellBody_iff {a b : ℝ≥0} (hab : a ≤ b) (hb1 : b ≤ 1) (x : E3) :
    x ∈ (cellBody a b hab hb1).carrier ↔
      ∀ i, |x i| ≤ ((![a / 4, b / 4, 1 / 4] i : ℝ≥0) : ℝ) := by
  rw [(cellBody a b hab hb1).mem_carrier_iff]
  simp [cellBody, PrismNDim.mk']


variable {a b : ℝ≥0}

/-- The two representative planks are the standard-frame `a × b × 1` planks centred at
`± (a / 2) e₀`. -/
def refCentre (t : ℝ) : E3 := EuclideanSpace.single (0 : Fin 3) t

@[simp] theorem refCentre_apply_zero (t : ℝ) : refCentre t 0 = t := by
  simp [refCentre]

@[simp] theorem refCentre_apply_one (t : ℝ) : refCentre t 1 = 0 := by
  simp [refCentre]

@[simp] theorem refCentre_apply_two (t : ℝ) : refCentre t 2 = 0 := by
  simp [refCentre]

/-- The cell body sits in both representative planks. -/
theorem cellBody_le_refPlank (hab : a ≤ b) (hb1 : b ≤ 1) {t : ℝ} (ht : |t| ≤ (a : ℝ) / 2) :
    (cellBody a b hab hb1).toConvexSpaceBody ≤
      (refPlank a b hab hb1 (refCentre t)).toConvexSpaceBody := by
  intro x hx
  have hx' := (mem_cellBody_iff hab hb1 x).mp hx
  have h0 : |x 0| ≤ (a : ℝ) / 4 := by simpa using hx' 0
  have h1 : |x 1| ≤ (b : ℝ) / 4 := by simpa using hx' 1
  have h2 : |x 2| ≤ (1 : ℝ) / 4 := by simpa using hx' 2
  have ha0 : (0 : ℝ) ≤ (a : ℝ) := (a : ℝ≥0).coe_nonneg
  have hb0 : (0 : ℝ) ≤ (b : ℝ) := (b : ℝ≥0).coe_nonneg
  refine (mem_refPlank_iff hab hb1 _ x).mpr ?_
  intro i
  fin_cases i
  · have hgoal : |x 0 - t| ≤ (a : ℝ) := by
      calc |x 0 - t| ≤ |x 0| + |t| := abs_sub _ _
        _ ≤ (a : ℝ) / 4 + (a : ℝ) / 2 := by linarith
        _ ≤ (a : ℝ) := by linarith
    simpa using hgoal
  · have hgoal : |x 1| ≤ (b : ℝ) := by linarith
    simpa using hgoal
  · have hgoal : |x 2| ≤ (1 : ℝ) := by linarith
    simpa using hgoal



/-- The intersection container: half the thin width, full `b` and `1`. -/
def thinPrism (a b : ℝ≥0) (hab : a ≤ b) (hb1 : b ≤ 1) :
    Prism3D (a / 2) b 1 (le_trans (half_le_self (by positivity)) hab) hb1 where
  toPrismNDim := PrismNDim.mk' (0 : E3) (EuclideanSpace.basisFun (Fin 3) ℝ) ![a / 2, b, 1]
  thicknesses_eq := rfl

theorem mem_thinPrism_iff (hab : a ≤ b) (hb1 : b ≤ 1) (x : E3) :
    x ∈ (thinPrism a b hab hb1).carrier ↔
      ∀ i, |x i| ≤ ((![a / 2, b, 1] i : ℝ≥0) : ℝ) := by
  rw [(thinPrism a b hab hb1).mem_carrier_iff]
  simp [thinPrism, PrismNDim.mk']

/-- The two representative planks meet only in the thin container. -/
theorem inter_refPlank_subset_thinPrism (hab : a ≤ b) (hb1 : b ≤ 1) :
    ((refPlank a b hab hb1 (refCentre ((a : ℝ) / 2))).carrier : Set E3)
        ∩ ((refPlank a b hab hb1 (refCentre (-((a : ℝ) / 2)))).carrier : Set E3)
      ⊆ ((thinPrism a b hab hb1).carrier : Set E3) := by
  rintro x ⟨hx1, hx2⟩
  have h1 := (mem_refPlank_iff hab hb1 _ x).mp hx1
  have h2 := (mem_refPlank_iff hab hb1 _ x).mp hx2
  have h10 : |x 0 - (a : ℝ) / 2| ≤ (a : ℝ) := by simpa using h1 0
  have h20 : |x 0 + (a : ℝ) / 2| ≤ (a : ℝ) := by
    have := h2 0
    simp only [Matrix.cons_val_zero, refCentre_apply_zero, sub_neg_eq_add] at this
    simpa using this
  have h11 : |x 1| ≤ (b : ℝ) := by simpa using h1 1
  have h12 : |x 2| ≤ (1 : ℝ) := by simpa using h1 2
  refine (mem_thinPrism_iff hab hb1 x).mpr ?_
  intro i
  fin_cases i
  · have hgoal : |x 0| ≤ (a : ℝ) / 2 := by
      rw [abs_le] at h10 h20 ⊢
      constructor <;> [linarith [h20.1]; linarith [h10.2]]
    simpa using hgoal
  · simpa using h11
  · simpa using h12



/-- **The two representative planks are essentially distinct.** -/
theorem isEssentiallyDistinct_refPlank (hab : a ≤ b) (hb1 : b ≤ 1) :
    IsEssentiallyDistinct
      ((refPlank a b hab hb1 (refCentre ((a : ℝ) / 2))).carrier : Set E3)
      ((refPlank a b hab hb1 (refCentre (-((a : ℝ) / 2)))).carrier : Set E3) := by
  have hv1 : volume ((refPlank a b hab hb1 (refCentre ((a : ℝ) / 2))).carrier : Set E3)
      = ((8 * a * b * 1 : ℝ≥0) : ENNReal) := by
    rw [Prism3D.volume_carrier]; push_cast; ring
  have hv2 : volume ((refPlank a b hab hb1 (refCentre (-((a : ℝ) / 2)))).carrier : Set E3)
      = ((8 * a * b * 1 : ℝ≥0) : ENNReal) := by
    rw [Prism3D.volume_carrier]; push_cast; ring
  have hvt : volume ((thinPrism a b hab hb1).carrier : Set E3)
      = ((8 * (a / 2) * b * 1 : ℝ≥0) : ENNReal) := by
    rw [Prism3D.volume_carrier]; push_cast; ring
  rw [IsEssentiallyDistinct, hv1, hv2, max_self, one_div, ← ENNReal.div_eq_inv_mul,
    ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)]
  calc
    volume (((refPlank a b hab hb1 (refCentre ((a : ℝ) / 2))).carrier : Set E3)
        ∩ ((refPlank a b hab hb1 (refCentre (-((a : ℝ) / 2)))).carrier : Set E3)) * 2
        ≤ volume ((thinPrism a b hab hb1).carrier : Set E3) * 2 := by
          gcongr
          exact inter_refPlank_subset_thinPrism hab hb1
    _ = ((8 * (a / 2) * b * 1 * 2 : ℝ≥0) : ENNReal) := by rw [hvt]; push_cast; ring
    _ ≤ ((8 * a * b * 1 : ℝ≥0) : ENNReal) := by
          rw [ENNReal.coe_le_coe]
          ring_nf
          exact le_rfl



/-- **The common cell body has plank-comparable dimensions**, with any comparability constant
`Cw ≥ 4`. -/
theorem isPlankOfDimensions_cellBody {Cw : ℝ≥0} (hCw : 4 ≤ Cw) (hab : a ≤ b) (hb1 : b ≤ 1) :
    IsPlankOfDimensions Cw a b (cellBody a b hab hb1).toConvexSpaceBody := by
  have hCw0 : Cw ≠ 0 := by
    intro h; rw [h] at hCw; exact absurd hCw (by norm_num)
  have hinv : ((Cw : ENNReal))⁻¹ = ((Cw⁻¹ : ℝ≥0) : ENNReal) := (ENNReal.coe_inv hCw0).symm
  have hCwR : (4 : ℝ) ≤ (Cw : ℝ) := by exact_mod_cast hCw
  have haR : (0 : ℝ) ≤ (a : ℝ) := (a : ℝ≥0).coe_nonneg
  have hbR : (0 : ℝ) ≤ (b : ℝ) := (b : ℝ≥0).coe_nonneg
  have habR : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  have hb1R : (b : ℝ) ≤ 1 := by exact_mod_cast hb1
  have hCwinvR : (Cw : ℝ)⁻¹ ≤ 1 / 4 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  have hball : Metric.closedBall (0 : E3) ((a / 4 : ℝ≥0) : ℝ) ⊆
      ((cellBody a b hab hb1).carrier : Set E3) := by
    have hc : (cellBody a b hab hb1).center = (0 : E3) := rfl
    simpa [hc] using (cellBody a b hab hb1).closedBall_subset_carrier
  have heth2 : ((a / 4 : ℝ≥0) : ENNReal) ≤
      Metric.ethickness ℝ ((cellBody a b hab hb1).carrier : Set E3) 2 := by
    refine le_trans ?_ (Metric.ethickness_monotone hball 2)
    exact le_ethickness_closedBall (a / 4) (by rw [finrank_euclideanSpace_fin]; norm_num)
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · refine le_trans ?_ (Prism3D.c_le_ethickness_zero (cellBody a b hab hb1))
    rw [hinv, ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
    push_cast
    linarith
  · refine le_trans (Prism3D.ethickness_zero_le (cellBody a b hab hb1)) ?_
    rw [← ENNReal.coe_add, ← ENNReal.coe_add, ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
    push_cast
    linarith
  · refine le_trans ?_ (Prism3D.b_le_ethickness_one (cellBody a b hab hb1))
    rw [hinv, ← ENNReal.coe_mul, ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
    push_cast
    nlinarith
  · refine le_trans (Prism3D.ethickness_one_le (cellBody a b hab hb1)) ?_
    rw [← ENNReal.coe_add, ← ENNReal.coe_mul, ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
    push_cast
    nlinarith
  · refine le_trans ?_ heth2
    rw [hinv, ← ENNReal.coe_mul, ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
    push_cast
    nlinarith
  · refine le_trans (Prism3D.ethickness_two_le (cellBody a b hab hb1)) ?_
    rw [← ENNReal.coe_mul, ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
    push_cast
    nlinarith



/-- The common cell body lies in the working window, at every radius `R ≥ 1`. -/
theorem cellBody_subset_window {R : ℝ≥0} (hR : 1 ≤ R) (hab : a ≤ b) (hb1 : b ≤ 1) :
    ((cellBody a b hab hb1).carrier : Set E3) ⊆ Metric.closedBall 0 (R : ℝ) := by
  have hc : (cellBody a b hab hb1).center = (0 : E3) := rfl
  have h := (cellBody a b hab hb1).carrier_subset_closedBall_center
  rw [hc] at h
  refine h.trans (Metric.closedBall_subset_closedBall ?_)
  have haR : (0 : ℝ) ≤ (a : ℝ) := (a : ℝ≥0).coe_nonneg
  have hb1R : (b : ℝ) ≤ 1 := by exact_mod_cast hb1
  have habR : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  have hRR : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  push_cast
  linarith

/-- The two representative planks are **different** planks: the cells are distinct. -/
theorem refPlank_ne (ha : 0 < a) (hab : a ≤ b) (hb1 : b ≤ 1) :
    refPlank a b hab hb1 (refCentre ((a : ℝ) / 2))
      ≠ refPlank a b hab hb1 (refCentre (-((a : ℝ) / 2))) := by
  intro hEq
  have hc : refCentre ((a : ℝ) / 2) = refCentre (-((a : ℝ) / 2)) := by
    have := congrArg (fun P : Plank a b hab hb1 => P.center) hEq
    simpa [center_refPlank] using this
  have h0 := congrArg (fun v : E3 => v 0) hc
  simp only [refCentre_apply_zero] at h0
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  linarith

/-- A presented plank is never essentially distinct from itself: it has positive finite volume. -/
theorem not_isEssentiallyDistinct_self_collarPlank {R Cw : ℝ≥0} (hR : 1 ≤ R) (hCw : 1 ≤ Cw)
    (ha : 0 < a) (hb : 0 < b) (hab : a ≤ b) (hb1 : b ≤ 1)
    (K : ConvexSpaceBody E3) (Y : ShadedBody E3) :
    ¬ IsEssentiallyDistinct
        ((collarPlank hR hCw hab hb1 K Y).carrier : Set E3)
        ((collarPlank hR hCw hab hb1 K Y).carrier : Set E3) := by
  have hvol : volume ((collarPlank hR hCw hab hb1 K Y).carrier : Set E3)
      = 8 * (a : ENNReal) * (b : ENNReal) * ((1 : ℝ≥0) : ENNReal) :=
    Prism3D.volume_carrier (collarPlank hR hCw hab hb1 K Y).toPrism3D
  refine not_isEssentiallyDistinct_self ?_ ?_
  · rw [hvol]
    have ha' : (a : ENNReal) ≠ 0 := by simpa using ha.ne'
    have hb' : (b : ENNReal) ≠ 0 := by simpa using hb.ne'
    simp [ha', hb']
  · rw [hvol]
    simp [ENNReal.mul_ne_top]


/-- A body with the empty shading: enough to instantiate the presentation, whose plank does not
depend on the shading at all. -/
def unshaded (K : ConvexSpaceBody E3) : ShadedBody E3 where
  toConvexSpaceBody := K
  shade := ∅
  measurableSet_shade := MeasurableSet.empty
  shade_subset := Set.empty_subset _


/-- **The counterexample family, at every plank scale.** -/
theorem exists_ED_reprs_common_body {Cw R : ℝ≥0} (hR : 1 ≤ R) (hCw : 4 ≤ Cw)
    (a b : ℝ≥0) (ha : 0 < a) (hab : a ≤ b) (hb1 : b ≤ 1) :
    ∃ (K : ConvexSpaceBody E3) (P₁ P₂ : Plank a b hab hb1),
      IsPlankOfDimensions Cw a b K ∧
      ((K.carrier : Set E3) ⊆ Metric.closedBall 0 (R : ℝ)) ∧
      K ≤ P₁.toConvexSpaceBody ∧ K ≤ P₂.toConvexSpaceBody ∧
      P₁ ≠ P₂ ∧
      IsEssentiallyDistinct (P₁.carrier : Set E3) (P₂.carrier : Set E3) := by
  refine ⟨(cellBody a b hab hb1).toConvexSpaceBody,
    refPlank a b hab hb1 (refCentre ((a : ℝ) / 2)),
    refPlank a b hab hb1 (refCentre (-((a : ℝ) / 2))),
    isPlankOfDimensions_cellBody hCw hab hb1, cellBody_subset_window hR hab hb1,
    cellBody_le_refPlank hab hb1 ?_, cellBody_le_refPlank hab hb1 ?_,
    refPlank_ne ha hab hb1, isEssentiallyDistinct_refPlank hab hb1⟩
  · rw [abs_of_nonneg (by positivity)]
  · rw [abs_of_nonpos (by simp; positivity)]
    simp


/-- **The clause the small-`b` branch of GWZ 6.6(B) consumes at
`GlobalPlankFactorizationEstimate.lean:1977`, read for the plank-presented outer family**: the
presented plank of a cell *is* the cell's representative plank. -/
def statement_of_universal_presentedPlank_eq_repr
    (R Cw : ℝ≥0) (hR : 1 ≤ R) (hCw : 1 ≤ Cw) : Prop :=
  ∀ (a b : ℝ≥0) (hab : a ≤ b) (hb1 : b ≤ 1), 0 < a →
    ∀ (K : ConvexSpaceBody E3) (Y : ShadedBody E3) (P : Plank a b hab hb1),
      IsPlankOfDimensions Cw a b K →
      ((K.carrier : Set E3) ⊆ Metric.closedBall 0 (R : ℝ)) →
      K ≤ P.toConvexSpaceBody →
      (collarPlank hR hCw hab hb1 K Y).toPrism3D = P

/-- **The repaired clause, read as a transport from the datum's own hypothesis**: pairwise
essential distinctness of the *representative* planks gives pairwise essential distinctness of the
*presented* planks. -/
def statement_of_universal_presentedPlank_ED
    (R Cw : ℝ≥0) (hR : 1 ≤ R) (hCw : 1 ≤ Cw) : Prop :=
  ∀ (a b : ℝ≥0) (hab : a ≤ b) (hb1 : b ≤ 1), 0 < a →
    ∀ (K₁ K₂ : ConvexSpaceBody E3) (Y₁ Y₂ : ShadedBody E3) (P₁ P₂ : Plank a b hab hb1),
      IsPlankOfDimensions Cw a b K₁ → IsPlankOfDimensions Cw a b K₂ →
      ((K₁.carrier : Set E3) ⊆ Metric.closedBall 0 (R : ℝ)) →
      ((K₂.carrier : Set E3) ⊆ Metric.closedBall 0 (R : ℝ)) →
      K₁ ≤ P₁.toConvexSpaceBody → K₂ ≤ P₂.toConvexSpaceBody →
      P₁ ≠ P₂ →
      IsEssentiallyDistinct (P₁.carrier : Set E3) (P₂.carrier : Set E3) →
      IsEssentiallyDistinct
        ((collarPlank hR hCw hab hb1 K₁ Y₁).carrier : Set E3)
        ((collarPlank hR hCw hab hb1 K₂ Y₂).carrier : Set E3)

/-- **REFUTED.** -/
theorem not_statement_of_universal_presentedPlank_eq_repr {R Cw : ℝ≥0}
    (hR : 1 ≤ R) (hCw1 : 1 ≤ Cw) (hCw4 : 4 ≤ Cw) :
    ¬ statement_of_universal_presentedPlank_eq_repr R Cw hR hCw1 := by
  intro h
  obtain ⟨K, P₁, P₂, hdim, hwin, h1, h2, hne, -⟩ :=
    exists_ED_reprs_common_body hR hCw4 (1 / 2) (1 / 2) (by norm_num) le_rfl (by norm_num)
  have e1 := h (1 / 2) (1 / 2) le_rfl (by norm_num) (by norm_num) K (unshaded K) P₁ hdim hwin h1
  have e2 := h (1 / 2) (1 / 2) le_rfl (by norm_num) (by norm_num) K (unshaded K) P₂ hdim hwin h2
  exact hne (e1.symm.trans e2)

/-- **REFUTED.** -/
theorem not_statement_of_universal_presentedPlank_ED {R Cw : ℝ≥0}
    (hR : 1 ≤ R) (hCw1 : 1 ≤ Cw) (hCw4 : 4 ≤ Cw) :
    ¬ statement_of_universal_presentedPlank_ED R Cw hR hCw1 := by
  intro h
  obtain ⟨K, P₁, P₂, hdim, hwin, h1, h2, hne, hED⟩ :=
    exists_ED_reprs_common_body hR hCw4 (1 / 2) (1 / 2) (by norm_num) le_rfl (by norm_num)
  have hself := h (1 / 2) (1 / 2) le_rfl (by norm_num) (by norm_num) K K (unshaded K) (unshaded K)
    P₁ P₂ hdim hdim hwin hwin h1 h2 hne hED
  exact not_isEssentiallyDistinct_self_collarPlank hR hCw1 (by norm_num) (by norm_num)
    le_rfl (by norm_num) K (unshaded K) hself

end CollarPlankRefute
end Kakeya

end

end
