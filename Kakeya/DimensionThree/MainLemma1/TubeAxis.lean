/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Tube.Dilate
public import Kakeya.Mathlib.Topology.CoveringNumber
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# The axis parametrisation of a tube, and the sharp count in the unit ball

This file formalizes the subsection *Counting essentially distinct tubes in `ℝ³`* of the
adapted blueprint (`GWZAdapted/section8_setup.tex`).  Its purpose is to supply the machinery
behind `Kakeya.ml1Boot.card_le` (blueprint `lem:ml1bootCardBound`), the count
`|s| ≤ C δ ^ (-4)` for essentially distinct `δ`-tubes in `B₁ ⊆ ℝ³`, which is strictly sharper
than the general packing bound `Tube.card_le_of_EssDistinct` (`δ ^ (-2n)`).

## The parametrisation

A `δ`-tube `T` contained in `B̄(0, 1)` is described by

* its direction `ω(T) = T.direction = T.y - T.x`, a unit vector;
* its *axial coordinate* `t(T) = ⟪T.x, ω(T)⟫` (`Kakeya.ml1Boot.axialCoord`);
* its *foot* `p(T) = T.x - t(T) • ω(T)` (`Kakeya.ml1Boot.axisFoot`), the foot of the
  perpendicular dropped from the origin to the core line of `T`.

The pair `(ω(T), p(T))` is the *axis parameter* `Kakeya.ml1Boot.axisParam`, a point of the `L²`
product `WithLp 2 (E × E)`.  It ranges over the *axis parameter set*
`Kakeya.ml1Boot.axisParamSet`, which has **codimension two** in `WithLp 2 (E × E)`: one equation
fixes `‖ω‖ = 1` and one fixes `⟪ω, p⟫ = 0`.  The two powers of `δ` that the crude endpoint-pair
count wastes are recovered from that codimension, through the thickening estimate
`Kakeya.ml1Boot.volume_cthickening_axisParamSet_le`.

The axial coordinate is *not* a parameter separated at scale `δ`: by
`Tube.not_essDistinct_of_axial_slide` a slide along the core by `|α| ≤ c_*` produces a tube that
is not essentially distinct from the original.  It is therefore paid for by the bounded factor
`8 n + 1` of `Kakeya.ml1Boot.card_axisCell_le` rather than by a power of `δ`.

## Blueprint correspondence

* `Kakeya.ml1Boot.axialCoord`, `Kakeya.ml1Boot.axisFoot`, `Kakeya.ml1Boot.axisParam` ↔
  `def:ml1bootTubeAxis`;
* `Kakeya.ml1Boot.inner_direction_axisFoot`, `Kakeya.ml1Boot.norm_axisFoot_le_one`,
  `Kakeya.ml1Boot.abs_axialCoord_le_one` ↔ `lem:ml1bootTubeAxisBounds`;
* `Kakeya.ml1Boot.axialSlide_x`, `Kakeya.ml1Boot.axialSlide_y` ↔
  `lem:ml1bootTubeAxisSlideIdentity`;
* `Kakeya.ml1Boot.not_essDistinct_of_axis_close` ↔ `lem:ml1bootTubeAxisSlideOverlap`;
* `Kakeya.ml1Boot.cStar_lt_abs_axialCoord_sub` ↔ `lem:ml1bootTubeAxisSeparation`;
* `Kakeya.ml1Boot.card_le_of_separated_Icc` ↔ `lem:ml1bootAxialCellCount`;
* `Kakeya.ml1Boot.axisParamSet` ↔ `def:ml1bootAxisParamSet`;
* `Kakeya.ml1Boot.pow_sub_pow_le_of_le_two` ↔ `lem:ml1bootPowDiffBound`;
* `Kakeya.ml1Boot.volume_annulus_le` ↔ `lem:ml1bootAnnulusVolume`;
* `Kakeya.ml1Boot.volume_slab_inter_ball_le` ↔ `lem:ml1bootSlabBallVolume`;
* `Kakeya.ml1Boot.cthickening_axisParamSet_subset` ↔ `lem:ml1bootAxisThickeningSubset`;
* `Kakeya.ml1Boot.volume_le_of_forall_section_le` ↔ `lem:ml1bootProductSectionVolume`;
* `Kakeya.ml1Boot.axisThickening.C` ↔ `def:ml1bootAxisThickeningConstant`;
* `Kakeya.ml1Boot.volume_cthickening_axisParamSet_le` ↔ `lem:ml1bootAxisThickeningVolume`;
* `Kakeya.ml1Boot.card_axisCell_le` ↔ `lem:ml1bootAxisCellCard`.

Everything is stated for a general ambient dimension `n = dim E ≥ 1`; only the assembly
`Kakeya.ml1Boot.card_le` specialises to `n = 3`.
-/

@[expose] public section

open MeasureTheory Metric

namespace Kakeya.ml1Boot

variable {δ : NNReal} {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ### The axis parametrisation -/

/-- **The axial-slide constant** `c_* = 1 / (4 n)`, `n = dim E` (blueprint
`def:essDistinctTubeEndpointSeparation_constant`).  It is the range of axial slides forbidden by
`Tube.not_essDistinct_of_axial_slide`, which spells it out inline; this reducible abbreviation
only gives it a name, so that the statements below stay readable. -/
noncomputable abbrev cStar (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] : ℝ :=
  1 / (4 * (Module.finrank ℝ E : ℝ))

/-- **The axial coordinate** `t(T) = ⟪T.x, ω(T)⟫` of a `δ`-tube (blueprint
`def:ml1bootTubeAxis`).  It locates `T.x` along the core line of `T`, measured from the foot of
the perpendicular dropped from the origin to that line. -/
noncomputable def axialCoord (T : Tube δ E) : ℝ := inner ℝ T.x T.direction

/-- **The foot** `p(T) = T.x - t(T) • ω(T)` of a `δ`-tube (blueprint `def:ml1bootTubeAxis`): the
foot of the perpendicular dropped from the origin to the core line of `T`.  By construction
`T.x = p(T) + t(T) • ω(T)` is the orthogonal decomposition of `T.x` into a component along
`ω(T)` and a component perpendicular to it. -/
noncomputable def axisFoot (T : Tube δ E) : E := T.x - axialCoord T • T.direction

/-- **The axis parameter** `(ω(T), p(T))` of a `δ`-tube (blueprint `def:ml1bootTubeAxis`), a point
of the `L²` product `E ×₂ E = WithLp 2 (E × E)`.  Unlike the endpoint pair `(T.x, T.y)` of
`Tube.endpoint_separated_of_ed`, it does not record the axial degree of freedom, which is not
separated at scale `δ`. -/
noncomputable def axisParam (T : Tube δ E) : WithLp 2 (E × E) :=
  WithLp.toLp 2 (T.direction, axisFoot T)

/-- The orthogonal decomposition `T.x = p(T) + t(T) • ω(T)` defining the foot (blueprint
`def:ml1bootTubeAxis`). -/
theorem axisFoot_add_smul_direction (T : Tube δ E) :
    axisFoot T + axialCoord T • T.direction = T.x := by
  simp [axisFoot]

omit [MeasurableSpace E] [BorelSpace E] in
/-- **The axis parameter of a tube in the unit ball, orthogonality** (blueprint
`lem:ml1bootTubeAxisBounds`): the foot is perpendicular to the direction.  No containment
hypothesis is needed for this clause. -/
theorem inner_direction_axisFoot (T : Tube δ E) :
    (inner ℝ T.direction (axisFoot T) : ℝ) = 0 := by
  rw [axisFoot, axialCoord, inner_sub_right, real_inner_smul_right,
    real_inner_comm T.x T.direction, real_inner_self_eq_norm_sq, Tube.norm_direction]
  ring

/-- **The axis parameter of a tube in the unit ball, size of the foot** (blueprint
`lem:ml1bootTubeAxisBounds`).  Together with `Tube.norm_direction` (`‖ω(T)‖ = 1`) and
`Kakeya.ml1Boot.inner_direction_axisFoot`, this places `axisParam T` in
`Kakeya.ml1Boot.axisParamSet`. -/
theorem norm_axisFoot_le_one (T : Tube δ E) (hT : T.carrier ⊆ closedBall 0 1) :
    ‖axisFoot T‖ ≤ 1 := by
  have hx_mem : T.x ∈ T.carrier := T.x_mem_carrier
  have hx_ball : T.x ∈ closedBall (0 : E) 1 := hT hx_mem
  have hnorm_x : ‖T.x‖ ≤ 1 := by
    rwa [mem_closedBall_zero_iff] at hx_ball
  have horth : (inner ℝ (axisFoot T) (axialCoord T • T.direction) : ℝ) = 0 := by
    rw [real_inner_smul_right, real_inner_comm, inner_direction_axisFoot T, mul_zero]
  have hsq : ‖axisFoot T‖ * ‖axisFoot T‖ ≤ ‖T.x‖ * ‖T.x‖ := by
    calc
      ‖axisFoot T‖ * ‖axisFoot T‖
          ≤ ‖axisFoot T‖ * ‖axisFoot T‖
            + ‖axialCoord T • T.direction‖ * ‖axialCoord T • T.direction‖ := by
              exact le_add_of_nonneg_right (mul_self_nonneg _)
      _ = ‖T.x‖ * ‖T.x‖ := by
        rw [← norm_add_sq_eq_norm_sq_add_norm_sq_real horth, axisFoot_add_smul_direction]
  have hle : ‖axisFoot T‖ ≤ ‖T.x‖ := by
    have h' : |‖axisFoot T‖| ≤ ‖T.x‖ :=
      abs_le_of_sq_le_sq (by simpa [pow_two] using hsq) (norm_nonneg T.x)
    rwa [abs_of_nonneg (norm_nonneg (axisFoot T))] at h'
  exact le_trans hle hnorm_x

/-- **The axis parameter of a tube in the unit ball, size of the axial coordinate** (blueprint
`lem:ml1bootTubeAxisBounds`).  This is what confines the axial coordinates of a family of tubes
in `B̄(0, 1)` to `[-1, 1]`, so that `Kakeya.ml1Boot.card_le_of_separated_Icc` applies. -/
theorem abs_axialCoord_le_one (T : Tube δ E) (hT : T.carrier ⊆ closedBall 0 1) :
    |axialCoord T| ≤ 1 := by
  have hx_mem : T.x ∈ T.carrier := T.x_mem_carrier
  have hx_ball : T.x ∈ closedBall (0 : E) 1 := hT hx_mem
  have hnorm_x : ‖T.x‖ ≤ 1 := by
    rwa [mem_closedBall_zero_iff] at hx_ball
  calc
    |axialCoord T| = |inner ℝ T.x T.direction| := rfl
    _ ≤ ‖T.x‖ * ‖T.direction‖ := abs_real_inner_le_norm T.x T.direction
    _ = ‖T.x‖ := by rw [Tube.norm_direction, mul_one]
    _ ≤ 1 := hnorm_x

/-- **The slide identity at the endpoint `x`** (blueprint `lem:ml1bootTubeAxisSlideIdentity`,
equation `eq:ml1bootSlideX`): sliding `T` along its own core by `α = t(T') - t(T)` moves `T.x`
to within `(p(T') - p(T)) + t(T') • (ω(T') - ω(T))` of `T'.x`. -/
theorem axialSlide_x (T T' : Tube δ E) :
    T'.x - (T.x + (axialCoord T' - axialCoord T) • T.direction)
      = (axisFoot T' - axisFoot T) + axialCoord T' • (T'.direction - T.direction) := by
  simp [axisFoot]
  module

/-- **The slide identity at the endpoint `y`** (blueprint `lem:ml1bootTubeAxisSlideIdentity`,
equation `eq:ml1bootSlideY`).  It differs from `Kakeya.ml1Boot.axialSlide_x` by the single extra
summand `ω(T') - ω(T)`, because `T.y = T.x + ω(T)` by definition of `Tube.direction`. -/
theorem axialSlide_y (T T' : Tube δ E) :
    T'.y - (T.y + (axialCoord T' - axialCoord T) • T.direction)
      = (axisFoot T' - axisFoot T) + axialCoord T' • (T'.direction - T.direction)
        + (T'.direction - T.direction) := by
  rw [show T.y = T.x + T.direction by simp [Tube.direction]]
  rw [show T'.y = T'.x + T'.direction by simp [Tube.direction]]
  simp [axisFoot]
  module

/-- **Nearby axis parameters and nearby axial coordinates defeat essential distinctness**
(blueprint `lem:ml1bootTubeAxisSlideOverlap`).

This is `Tube.not_essDistinct_of_axial_slide` at the axial slide `α = t(T') - t(T)`, whose two
endpoint hypotheses are supplied by the slide identities `Kakeya.ml1Boot.axialSlide_x` and
`Kakeya.ml1Boot.axialSlide_y`.  The hypothesis `|t(T) - t(T')| ≤ c_*` is the slide range
permitted by that lemma and may not be enlarged.  No positivity hypothesis on `ε` is stated:
`hω` already forces `0 ≤ ε`. -/
theorem not_essDistinct_of_axis_close [Nontrivial E] (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (T T' : Tube δ E) {ε : ℝ}
    (hω : ‖T.direction - T'.direction‖ ≤ ε)
    (hp : ‖axisFoot T - axisFoot T'‖ ≤ ε)
    (hε : 3 * ε ≤ cStar E * (δ : ℝ))
    (ht : |axialCoord T| ≤ 1) (ht' : |axialCoord T'| ≤ 1)
    (htt : |axialCoord T - axialCoord T'| ≤ cStar E) :
    ¬ IsEssentiallyDistinct T.carrier T'.carrier := by
  have hε0 : 0 ≤ ε := le_trans (norm_nonneg _) hω
  have hdir' : ‖T'.direction - T.direction‖ ≤ ε := by
    simpa [norm_sub_rev] using hω
  have hfoot' : ‖axisFoot T' - axisFoot T‖ ≤ ε := by
    simpa [norm_sub_rev] using hp
  -- the error of the slide-affine part of the core, common to both endpoint estimates
  have hslide : ‖axialCoord T' • (T'.direction - T.direction)‖ ≤ ε := by
    calc
      ‖axialCoord T' • (T'.direction - T.direction)‖
          = |axialCoord T'| * ‖T'.direction - T.direction‖ := by
            rw [norm_smul, Real.norm_eq_abs]
      _ ≤ 1 * ‖T'.direction - T.direction‖ :=
            mul_le_mul ht' le_rfl (norm_nonneg _) (by norm_num)
      _ ≤ 1 * ε := mul_le_mul le_rfl hdir' (norm_nonneg _) (by norm_num)
      _ = ε := by rw [one_mul]
  have hx : dist T'.x (T.x + (axialCoord T' - axialCoord T) • T.direction)
      ≤ cStar E * (δ : ℝ) := by
    rw [dist_eq_norm]
    have hb : ‖T'.x - (T.x + (axialCoord T' - axialCoord T) • T.direction)‖ ≤ 3 * ε := by
      calc
        ‖T'.x - (T.x + (axialCoord T' - axialCoord T) • T.direction)‖
            = ‖(axisFoot T' - axisFoot T) + axialCoord T' • (T'.direction - T.direction)‖ := by
              rw [axialSlide_x]
        _ ≤ ‖axisFoot T' - axisFoot T‖ + ‖axialCoord T' • (T'.direction - T.direction)‖ := by
              exact norm_add_le _ _
        _ ≤ ε + ε := by
              exact add_le_add hfoot' hslide
        _ = 2 * ε := by ring
        _ ≤ 3 * ε := by linarith
    exact le_trans hb hε
  have hy : dist T'.y (T.y + (axialCoord T' - axialCoord T) • T.direction)
      ≤ cStar E * (δ : ℝ) := by
    rw [dist_eq_norm]
    have hb :
        ‖T'.y - (T.y + (axialCoord T' - axialCoord T) • T.direction)‖ ≤ 3 * ε := by
      calc
        ‖T'.y - (T.y + (axialCoord T' - axialCoord T) • T.direction)‖
            ≤ ‖(axisFoot T' - axisFoot T) + axialCoord T' • (T'.direction - T.direction)‖
                + ‖T'.direction - T.direction‖ := by
                rw [axialSlide_y]
                exact norm_add_le _ _
        _ ≤ (‖axisFoot T' - axisFoot T‖ + ‖axialCoord T' • (T'.direction - T.direction)‖)
                + ‖T'.direction - T.direction‖ := by
          exact add_le_add_left
            (norm_add_le (axisFoot T' - axisFoot T)
              (axialCoord T' • (T'.direction - T.direction))) _
        _ ≤ (ε + ε) + ε := by
          exact add_le_add (add_le_add hfoot' hslide) hdir'
        _ = 3 * ε := by ring
    exact le_trans hb hε
  have hα : |axialCoord T' - axialCoord T| ≤ cStar E := by
    simpa [abs_sub_comm] using htt
  exact Tube.not_essDistinct_of_axial_slide hδ0 hδ1 T T' hα hx hy

/-- **Essentially distinct tubes with nearby axis parameters have separated axial coordinates**
(blueprint `lem:ml1bootTubeAxisSeparation`): the contrapositive of
`Kakeya.ml1Boot.not_essDistinct_of_axis_close` at `ε = c_* δ / 3`, whose remaining hypotheses
`|t(T)| ≤ 1`, `|t(T')| ≤ 1` come from `Kakeya.ml1Boot.abs_axialCoord_le_one`. -/
theorem cStar_lt_abs_axialCoord_sub [Nontrivial E] (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (T T' : Tube δ E)
    (hT : T.carrier ⊆ closedBall 0 1) (hT' : T'.carrier ⊆ closedBall 0 1)
    (hED : IsEssentiallyDistinct T.carrier T'.carrier)
    (hω : ‖T.direction - T'.direction‖ ≤ cStar E * (δ : ℝ) / 3)
    (hp : ‖axisFoot T - axisFoot T'‖ ≤ cStar E * (δ : ℝ) / 3) :
    cStar E < |axialCoord T - axialCoord T'| := by
  by_contra h
  have htt : |axialCoord T - axialCoord T'| ≤ cStar E := not_lt.mp h
  have ht : |axialCoord T| ≤ 1 := abs_axialCoord_le_one T hT
  have ht' : |axialCoord T'| ≤ 1 := abs_axialCoord_le_one T' hT'
  have hε : 3 * (cStar E * (δ : ℝ) / 3) ≤ cStar E * (δ : ℝ) := by
    linarith
  exact (not_essDistinct_of_axis_close hδ0 hδ1 T T' hω hp hε ht ht' htt) hED

/-! ### The parameter set and its thickening -/

/-- **Separated points of a bounded interval** (blueprint `lem:ml1bootAxialCellCount`): a finite
subset of `[-1, 1]` whose points are pairwise more than `c` apart has at most `2 / c + 1`
elements.  At `c = c_* = 1 / (4 n)` this reads `#F ≤ 8 n + 1`, the per-cell count of
`Kakeya.ml1Boot.card_axisCell_le`. -/
theorem card_le_of_separated_Icc {c : ℝ} (hc : 0 < c) (F : Finset ℝ)
    (hF : ∀ a ∈ F, a ∈ Set.Icc (-1 : ℝ) 1)
    (hsep : (F : Set ℝ).Pairwise fun a b => c < |a - b|) :
    (F.card : ℝ) ≤ 2 / c + 1 := by
  let f : ℝ → ℕ := fun a => ⌊(a + 1) / c⌋₊
  have hmap : Set.MapsTo f (F : Set ℝ) (Finset.range (⌊2 / c⌋₊ + 1) : Set ℕ) := by
    intro a ha
    rw [Finset.mem_coe] at ha
    have haIcc : a ∈ Set.Icc (-1 : ℝ) 1 := hF a ha
    have hsum_le : a + 1 ≤ 2 := by linarith [haIcc.2]
    have hdiv_le : (a + 1) / c ≤ 2 / c :=
      div_le_div_of_nonneg_right hsum_le (le_of_lt hc)
    simpa using (Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.floor_mono hdiv_le)))
  have hinj : (F : Set ℝ).InjOn f := by
    intro a ha b hb hf_eq
    by_contra hne
    have hlt : c < |a - b| := hsep ha hb hne
    rw [Finset.mem_coe] at ha hb
    have haIcc : a ∈ Set.Icc (-1 : ℝ) 1 := hF a ha
    have hbIcc : b ∈ Set.Icc (-1 : ℝ) 1 := hF b hb
    have hu0 : 0 ≤ (a + 1) / c := div_nonneg (by linarith [haIcc.1]) (le_of_lt hc)
    have hv0 : 0 ≤ (b + 1) / c := div_nonneg (by linarith [hbIcc.1]) (le_of_lt hc)
    have hf_eq' : ⌊(a + 1) / c⌋₊ = ⌊(b + 1) / c⌋₊ := by
      simpa [f] using hf_eq
    have hu_lt : (a + 1) / c < (b + 1) / c + 1 := by
      calc
        (a + 1) / c < (⌊(a + 1) / c⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one ((a + 1) / c)
        _ = (⌊(b + 1) / c⌋₊ : ℝ) + 1 := by rw [hf_eq']
        _ ≤ (b + 1) / c + 1 := by linarith [Nat.floor_le hv0]
    have hv_lt : (b + 1) / c < (a + 1) / c + 1 := by
      calc
        (b + 1) / c < (⌊(b + 1) / c⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one ((b + 1) / c)
        _ = (⌊(a + 1) / c⌋₊ : ℝ) + 1 := by rw [hf_eq']
        _ ≤ (a + 1) / c + 1 := by linarith [Nat.floor_le hu0]
    have hdiff : |(a + 1) / c - (b + 1) / c| < 1 := by
      rw [abs_lt]
      constructor
      · nlinarith [hv_lt]
      · nlinarith [hu_lt]
    have hsub : (a + 1) / c - (b + 1) / c = (a - b) / c := by
      rw [← sub_div, add_sub_add_right_eq_sub]
    have hdiff' : |(a - b) / c| < 1 := by
      simpa [← hsub] using hdiff
    have habs : |a - b| < c := by
      rw [abs_div, abs_of_nonneg (le_of_lt hc)] at hdiff'
      rw [div_lt_iff₀ hc] at hdiff'
      simpa using hdiff'
    exact (not_lt_of_ge (le_of_lt habs)) hlt
  have hcard_nat : F.card ≤ ⌊2 / c⌋₊ + 1 := by
    have h := Finset.card_le_card_of_injOn f hmap hinj
    rwa [Finset.card_range] at h
  have hcard_real : (F.card : ℝ) ≤ (⌊2 / c⌋₊ : ℝ) + 1 := by
    exact_mod_cast hcard_nat
  have hfloor_le : (⌊2 / c⌋₊ : ℝ) ≤ 2 / c :=
    Nat.floor_le (div_nonneg (by norm_num) (le_of_lt hc))
  calc
    (F.card : ℝ) ≤ (⌊2 / c⌋₊ : ℝ) + 1 := hcard_real
    _ ≤ 2 / c + 1 := by linarith [hfloor_le]

/-- **The axis parameter set** `𝒜` (blueprint `def:ml1bootAxisParamSet`): the pairs `(ω, p)` in
the `L²` product `E ×₂ E` with `‖ω‖ = 1`, `⟪ω, p⟫ = 0` and `‖p‖ ≤ 1`.  It has codimension two in
`E ×₂ E`, which is the whole of the gain of `Kakeya.ml1Boot.card_le` over the crude count. -/
def axisParamSet (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    Set (WithLp 2 (E × E)) :=
  {q | ‖(WithLp.ofLp q).1‖ = 1 ∧ (inner ℝ (WithLp.ofLp q).1 (WithLp.ofLp q).2 : ℝ) = 0 ∧
    ‖(WithLp.ofLp q).2‖ ≤ 1}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The axis parameter set is closed: its three defining conditions are closed conditions on
continuous functions (blueprint `def:ml1bootAxisParamSet`). -/
theorem isClosed_axisParamSet : IsClosed (axisParamSet E) := by
  have hf : Continuous (fun q : WithLp 2 (E × E) => ‖(WithLp.ofLp q).1‖) :=
    continuous_norm.comp (WithLp.continuous_fst (p := 2) (α := E) (β := E))
  have hg :
      Continuous (fun q : WithLp 2 (E × E) => (inner ℝ (WithLp.ofLp q).1 (WithLp.ofLp q).2 : ℝ)) :=
    continuous_inner.comp ((WithLp.continuous_fst (p := 2) (α := E) (β := E)).prodMk
      (WithLp.continuous_snd (p := 2) (α := E) (β := E)))
  have hh : Continuous (fun q : WithLp 2 (E × E) => ‖(WithLp.ofLp q).2‖) :=
    continuous_norm.comp (WithLp.continuous_snd (p := 2) (α := E) (β := E))
  rw [show axisParamSet E =
      {q : WithLp 2 (E × E) | ‖(WithLp.ofLp q).1‖ = 1} ∩
        ({q : WithLp 2 (E × E) | (inner ℝ (WithLp.ofLp q).1 (WithLp.ofLp q).2 : ℝ) = 0} ∩
          {q : WithLp 2 (E × E) | ‖(WithLp.ofLp q).2‖ ≤ 1}) by
    ext q
    simp [axisParamSet]]
  exact (isClosed_eq hf continuous_const).inter
    ((isClosed_eq hg continuous_const).inter (isClosed_le hh continuous_const))

omit [MeasurableSpace E] [BorelSpace E] in
/-- The axis parameter set is compact, being closed and bounded in a finite-dimensional space
(blueprint `def:ml1bootAxisParamSet`). -/
theorem isCompact_axisParamSet : IsCompact (axisParamSet E) := by
  have hsub : axisParamSet E ⊆ Metric.closedBall (0 : WithLp 2 (E × E)) 2 := by
    intro q hq
    rw [axisParamSet] at hq
    rcases hq with ⟨hω, _hin, hp⟩
    have hnormsq : ‖(WithLp.ofLp q).1‖ ^ 2 + ‖(WithLp.ofLp q).2‖ ^ 2 ≤ 2 := by
      have hωsq : ‖(WithLp.ofLp q).1‖ ^ 2 = 1 := by rw [hω, one_pow]
      have hpsq : ‖(WithLp.ofLp q).2‖ ^ 2 ≤ 1 := by
        simpa using (pow_le_pow_left₀ (norm_nonneg _) hp 2 : ‖(WithLp.ofLp q).2‖ ^ 2 ≤ 1 ^ 2)
      nlinarith
    have hnorm_le_two : ‖q‖ ≤ 2 := by
      rw [WithLp.prod_norm_eq_of_L2]
      suffices ‖(WithLp.ofLp q).1‖ ^ 2 + ‖(WithLp.ofLp q).2‖ ^ 2 ≤ 2 ^ 2 by
        exact (Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 2)).mpr this
      nlinarith [hnormsq]
    exact (mem_closedBall_zero_iff).mpr hnorm_le_two
  have hbounded : Bornology.IsBounded (axisParamSet E) :=
    (Metric.isBounded_closedBall (x := (0 : WithLp 2 (E × E))) (r := 2)).subset hsub
  exact Metric.isCompact_of_isClosed_isBounded isClosed_axisParamSet hbounded

/-- The axis parameter set contains the axis parameter of every `δ`-tube contained in `B̄(0, 1)`
(blueprint `def:ml1bootAxisParamSet`, via `lem:ml1bootTubeAxisBounds`). -/
theorem axisParam_mem_axisParamSet (T : Tube δ E) (hT : T.carrier ⊆ closedBall 0 1) :
    axisParam T ∈ axisParamSet E := by
  rw [axisParam, axisParamSet]
  exact ⟨Tube.norm_direction T, inner_direction_axisFoot T, norm_axisFoot_le_one T hT⟩

/-- **A difference of powers** (blueprint `lem:ml1bootPowDiffBound`): for `0 ≤ y ≤ x ≤ 2`,
`x ^ n - y ^ n ≤ n · 2 ^ (n - 1) · (x - y)`.  The `private` lemma
`Kakeya.EuclideanNet.pow_shell_diff_le` is the special case `x, y = 1 ± ε / 2`. -/
theorem pow_sub_pow_le_of_le_two {n : ℕ} (hn : 1 ≤ n) {x y : ℝ} (hy : 0 ≤ y) (hyx : y ≤ x)
    (hx : x ≤ 2) :
    x ^ n - y ^ n ≤ (n : ℝ) * 2 ^ (n - 1) * (x - y) := by
  have hx0 : 0 ≤ x := by linarith
  have hsum : (∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i)) ≤ (n : ℝ) * (2 : ℝ) ^ (n - 1) := by
    have hterm : ∀ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i) ≤ (2 : ℝ) ^ (n - 1) := by
      intro i hi
      have hi' : i < n := Finset.mem_range.mp hi
      calc
        x ^ i * y ^ (n - 1 - i) ≤ x ^ i * x ^ (n - 1 - i) := by
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hy hyx (n - 1 - i)) (pow_nonneg hx0 i)
        _ = (x : ℝ) ^ (n - 1) := by
          rw [← pow_add]
          congr 1
          omega
        _ ≤ (2 : ℝ) ^ (n - 1) := by
          exact pow_le_pow_left₀ hx0 hx (n - 1)
    simpa [Finset.card_range] using
      Finset.sum_le_card_nsmul (Finset.range n) (fun i => x ^ i * y ^ (n - 1 - i))
        ((2 : ℝ) ^ (n - 1)) hterm
  calc
    x ^ n - y ^ n = (∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i)) * (x - y) := by
      rw [geom_sum₂_mul_of_ge hyx n]
    _ ≤ (n : ℝ) * (2 : ℝ) ^ (n - 1) * (x - y) := by
      exact mul_le_mul_of_nonneg_right hsum (by linarith)

/-- `ω_d = 2 ^ d · C_cov(d)`, the volume of the unit ball of a `d`-dimensional Euclidean space
(blueprint `lem:closedBallVolumeCcov`, Lean `Metric.volume_closedBall_eq_ccov_mul_pow`).  It is
written as a function of the dimension rather than as `volume (closedBall (0 : E) 1)` because
the estimates below use it at `d = n` *and* at `d = n - 1`, the latter in the hyperplane
`(ℝ ∙ u)ᗮ`. -/
noncomputable def unitBallVolume (d : ℕ) : NNReal :=
  2 ^ d * Metric.coveringNumber_mul_pow_le_volume_cthickening.C d

/-- **Volume of a thin annulus** (blueprint `lem:ml1bootAnnulusVolume`): the set of `ω` with
`|‖ω‖ - 1| ≤ r` is the shell `B̄(0, 1 + r) \ B(0, 1 - r)`, of volume at most
`n · 2 ^ n · ω_n · r`.  The hypothesis `r ≤ 1` is what makes it a shell rather than a ball, and
`Nontrivial E` (i.e. `n ≥ 1`) is needed: in dimension `0` the left side is a point of unit mass
while the right side vanishes. -/
theorem volume_annulus_le [Nontrivial E] {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    volume {ω : E | |‖ω‖ - 1| ≤ r}
      ≤ ENNReal.ofReal ((Module.finrank ℝ E : ℝ) * 2 ^ Module.finrank ℝ E
          * (unitBallVolume (Module.finrank ℝ E) : ℝ) * r) := by
  set n := Module.finrank ℝ E with hn_eq
  set u : ℝ := (unitBallVolume n : ℝ)
  have hn : 1 ≤ n := Module.finrank_pos (R := ℝ) (M := E)
  have hC : (0 : ℝ) ≤ (coveringNumber_mul_pow_le_volume_cthickening.C n : ℝ) :=
    (coveringNumber_mul_pow_le_volume_cthickening.C n).property
  have hu : u = (2 : ℝ) ^ n * (coveringNumber_mul_pow_le_volume_cthickening.C n : ℝ) := rfl
  have hu0 : 0 ≤ u := by
    rw [hu]
    exact mul_nonneg (pow_nonneg (by norm_num) n) hC
  have h1r0 : 0 ≤ 1 - r := by linarith
  have h1r1 : 0 ≤ 1 + r := by linarith
  have hle : 1 - r ≤ 1 + r := by linarith
  have hx2 : 1 + r ≤ 2 := by linarith
  have hvol : ∀ s : ℝ, 0 ≤ s →
      volume (Metric.closedBall (0 : E) s) = ENNReal.ofReal (u * s ^ n) := by
    intro s hs
    rw [volume_closedBall_eq_ccov_mul_pow (E := E) (r := s) hs]
    congr 1
  have hballs : Metric.ball (0 : E) (1 - r) ⊆ Metric.closedBall (0 : E) (1 + r) := by
    intro x hx
    rw [mem_closedBall_zero_iff]
    have hlt : ‖x‖ < 1 - r := mem_ball_zero_iff.mp hx
    exact le_trans (le_of_lt hlt) hle
  have hsub : {ω : E | |‖ω‖ - 1| ≤ r} ⊆
      Metric.closedBall (0 : E) (1 + r) \ Metric.ball (0 : E) (1 - r) := by
    intro ω hω
    have hω' : |‖ω‖ - 1| ≤ r := by simpa using hω
    constructor
    · rw [mem_closedBall_zero_iff]
      have h := abs_le.mp hω'
      linarith
    · intro hωball
      have hlt : ‖ω‖ < 1 - r := mem_ball_zero_iff.mp hωball
      have hge : 1 - r ≤ ‖ω‖ := by
        have h := (abs_le.mp hω').1
        linarith
      exact not_lt_of_ge hge hlt
  have hdiff :
      volume (Metric.closedBall (0 : E) (1 + r) \ Metric.ball (0 : E) (1 - r))
        = ENNReal.ofReal (u * ((1 + r) ^ n - (1 - r) ^ n)) := by
    have hfin : volume (Metric.ball (0 : E) (1 - r)) ≠ ⊤ := by
      have hlt : volume (Metric.closedBall (0 : E) (1 - r)) < ⊤ := by
        rw [hvol (1 - r) h1r0]
        exact ENNReal.ofReal_lt_top
      exact ne_of_lt (lt_of_le_of_lt (measure_mono (Metric.ball_subset_closedBall)) hlt)
    rw [MeasureTheory.measure_sdiff (μ := volume) hballs
      (measurableSet_ball.nullMeasurableSet) hfin]
    rw [hvol (1 + r) h1r1]
    rw [← MeasureTheory.Measure.addHaar_closedBall_eq_addHaar_ball (μ := volume) (0 : E) (1 - r)]
    rw [hvol (1 - r) h1r0]
    rw [← ENNReal.ofReal_sub (u * (1 + r) ^ n) (mul_nonneg hu0 (pow_nonneg h1r0 n))]
    congr 1
    ring
  have hpow : (1 + r) ^ n - (1 - r) ^ n ≤ (n : ℝ) * 2 ^ (n - 1) * (2 * r) := by
    calc
      (1 + r) ^ n - (1 - r) ^ n
          ≤ (n : ℝ) * 2 ^ (n - 1) * ((1 + r) - (1 - r)) :=
            pow_sub_pow_le_of_le_two (n := n) hn h1r0 hle hx2
      _ = (n : ℝ) * 2 ^ (n - 1) * (2 * r) := by ring
  have h2p : (2 : ℝ) ^ (n - 1) * 2 = (2 : ℝ) ^ n := by
    rw [← pow_succ, Nat.sub_add_cancel hn]
  have hmain : u * ((n : ℝ) * 2 ^ (n - 1) * (2 * r)) = (n : ℝ) * 2 ^ n * u * r := by
    calc
      u * ((n : ℝ) * 2 ^ (n - 1) * (2 * r))
          = (n : ℝ) * u * (2 ^ (n - 1) * 2) * r := by ring
      _ = (n : ℝ) * 2 ^ n * u * r := by
        rw [h2p]
        ring
  calc
    volume {ω : E | |‖ω‖ - 1| ≤ r}
        ≤ volume (Metric.closedBall (0 : E) (1 + r) \ Metric.ball (0 : E) (1 - r)) := by
          exact measure_mono hsub
    _ = ENNReal.ofReal (u * ((1 + r) ^ n - (1 - r) ^ n)) := hdiff
    _ ≤ ENNReal.ofReal (u * ((n : ℝ) * 2 ^ (n - 1) * (2 * r))) := by
          apply ENNReal.ofReal_le_ofReal
          exact mul_le_mul_of_nonneg_left hpow hu0
    _ = ENNReal.ofReal ((n : ℝ) * 2 ^ n * u * r) := by
          rw [hmain]

omit [MeasurableSpace E] [BorelSpace E] in
/-- **The orthogonal complement of a unit vector** (blueprint `lem:ml1bootPerpFinrank`):
`dim (ℝ ∙ u)ᗮ = n - 1`.  This is what identifies the cross-sectional factor of
`Kakeya.ml1Boot.volume_slab_inter_ball_le` as `ω_{n-1}`. -/
theorem finrank_orthogonal_span_singleton_of_norm_one {u : E} (hu : ‖u‖ = 1) :
    Module.finrank ℝ ((ℝ ∙ u)ᗮ : Submodule ℝ E) = Module.finrank ℝ E - 1 := by
  have hu_ne : u ≠ 0 := norm_ne_zero_iff.mp (by rw [hu]; exact one_ne_zero)
  have hspan : Module.finrank ℝ (ℝ ∙ u) = 1 := finrank_span_singleton hu_ne
  have hsum : Module.finrank ℝ (ℝ ∙ u) + Module.finrank ℝ ((ℝ ∙ u)ᗮ : Submodule ℝ E)
      = Module.finrank ℝ E :=
    Submodule.finrank_add_finrank_orthogonal (K := ℝ ∙ u)
  omega

/-- **Volume of a ball intersected with a slab** (blueprint `lem:ml1bootSlabBallVolume`): the
set `{p : ‖p‖ ≤ R, |⟪u, p⟫| ≤ h}` is contained in the cylinder `cylinder 0 u (-h) h R`, whose
volume `volume_cylinder_zero` evaluates as `2 h · ω_{n-1} · R ^ (n-1)`. -/
theorem volume_slab_inter_ball_le [Nontrivial E] {u : E} (hu : ‖u‖ = 1) {h R : ℝ}
    (hh : 0 ≤ h) (hR : 0 ≤ R) :
    volume {p : E | ‖p‖ ≤ R ∧ |(inner ℝ u p : ℝ)| ≤ h}
      ≤ ENNReal.ofReal (2 * h * (unitBallVolume (Module.finrank ℝ E - 1) : ℝ)
          * R ^ (Module.finrank ℝ E - 1)) := by
  -- The ball ∩ slab is contained in the cylinder `cylinder 0 u (-h) h R`.
  have hsub :
      {p : E | ‖p‖ ≤ R ∧ |(inner ℝ u p : ℝ)| ≤ h} ⊆ cylinder (0 : E) u (-h) h R := by
    intro p hp
    rw [mem_cylinder]
    rcases hp with ⟨hpR, habs⟩
    -- The component of `p` orthogonal to `u` is the orthogonal projection onto `(ℝ ∙ u)ᗮ`,
    -- whose norm is at most `‖p‖`; by the hypothesis `‖p‖ ≤ R`.
    have hperp_le : ‖p - (inner ℝ u p : ℝ) • u‖ ≤ R := by
      have hpp := Submodule.norm_orthogonalProjectionOnto_perp_span_singleton hu p
      have hle : ‖((ℝ ∙ u)ᗮ : Submodule ℝ E).orthogonalProjectionOnto p‖ ≤ ‖p‖ :=
        Submodule.norm_orthogonalProjectionOnto_apply_le ((ℝ ∙ u)ᗮ : Submodule ℝ E) p
      rw [hpp.2] at hle
      exact le_trans hle hpR
    constructor
    · have hIcc : (inner ℝ u p : ℝ) ∈ Set.Icc (-h) h := by
        rw [Set.mem_Icc]
        exact abs_le.mp habs
      rw [show inner ℝ (p - 0) u = inner ℝ u p by rw [sub_zero, real_inner_comm]]
      exact hIcc
    · rw [show (p - 0) - (inner ℝ (p - 0) u : ℝ) • u = p - (inner ℝ u p : ℝ) • u
        by rw [sub_zero, real_inner_comm]]
      exact hperp_le
  -- Step 2: the measure of the containing cylinder.
  have hmono : volume {p : E | ‖p‖ ≤ R ∧ |(inner ℝ u p : ℝ)| ≤ h}
      ≤ volume (cylinder (0 : E) u (-h) h R) := measure_mono hsub
  have hfact : h - (-h) = 2 * h := by ring
  have hvolCyl : volume (cylinder (0 : E) u (-h) h R)
      = ENNReal.ofReal (2 * h) *
          volume (Metric.closedBall (0 : ((ℝ ∙ u)ᗮ : Submodule ℝ E)) R) := by
    simpa [hfact] using volume_cylinder_zero hu (-h) h R
  rw [hvolCyl] at hmono
  -- Step 3: the cross-section ball in the perpendicular space, splitting on `dim (ℝ ∙ u)ᗮ`
  -- (which is `n - 1`): positive dimension from `Metric.volume_closedBall_eq_ccov_mul_pow`,
  -- zero dimension from `Metric.volume_closedBall_of_finrank_eq_zero`.
  have hxvol : volume (Metric.closedBall (0 : ((ℝ ∙ u)ᗮ : Submodule ℝ E)) R)
      = ENNReal.ofReal ((unitBallVolume (Module.finrank ℝ E - 1) : ℝ)
          * R ^ (Module.finrank ℝ E - 1)) := by
    set n : ℕ := Module.finrank ℝ E with hn_def
    have hperp : Module.finrank ℝ ((ℝ ∙ u)ᗮ : Submodule ℝ E) = n - 1 := by
      simpa [hn_def] using finrank_orthogonal_span_singleton_of_norm_one hu
    by_cases h2 : 2 ≤ n
    · have hperp_pos : 0 < Module.finrank ℝ ((ℝ ∙ u)ᗮ : Submodule ℝ E) := by
        rw [hperp]
        omega
      haveI : Nontrivial ((ℝ ∙ u)ᗮ : Submodule ℝ E) :=
        Module.nontrivial_of_finrank_pos hperp_pos
      have hvol := Metric.volume_closedBall_eq_ccov_mul_pow (E := ((ℝ ∙ u)ᗮ : Submodule ℝ E))
        (r := R) hR
      rw [hperp] at hvol
      rw [hvol]
      have hUB : (unitBallVolume (n - 1) : ℝ) =
          (2 : ℝ) ^ (n - 1) *
            (Metric.coveringNumber_mul_pow_le_volume_cthickening.C (n - 1) : ℝ) := by
        rw [unitBallVolume]
        push_cast
        rfl
      rw [← hUB]
    · have hn_pos : 0 < n := by
        rw [hn_def]
        exact Module.finrank_pos (R := ℝ) (M := E)
      have hperp0 : Module.finrank ℝ ((ℝ ∙ u)ᗮ : Submodule ℝ E) = 0 := by
        rw [hperp]
        omega
      have hv0 : volume (Metric.closedBall (0 : ((ℝ ∙ u)ᗮ : Submodule ℝ E)) R) = 1 :=
        Metric.volume_closedBall_of_finrank_eq_zero hperp0 hR
      have hC0 : (unitBallVolume 0 : ℝ) = 1 := by
        have hC0nn : unitBallVolume 0 = (1 : NNReal) := by
          rw [unitBallVolume, pow_zero, one_mul]
          rw [Metric.coveringNumber_mul_pow_le_volume_cthickening.C]
          congr 1
          norm_num [Real.Gamma_one]
        exact_mod_cast hC0nn
      have hRHS : ENNReal.ofReal ((unitBallVolume (n - 1) : ℝ) * R ^ (n - 1)) = 1 := by
        rw [show n - 1 = 0 by omega, hC0, pow_zero]
        norm_num
      rw [hv0, hRHS]
  rw [hxvol] at hmono
  -- Step 4: `ofReal (2h) * ofReal (ω_{n-1} R^{n-1}) = ofReal (2h ω_{n-1} R^{n-1})`.
  have h2m : 0 ≤ 2 * h := mul_nonneg (by norm_num) hh
  have hprod : ENNReal.ofReal (2 * h) *
        ENNReal.ofReal ((unitBallVolume (Module.finrank ℝ E - 1) : ℝ)
          * R ^ (Module.finrank ℝ E - 1)) =
      ENNReal.ofReal (2 * h * (unitBallVolume (Module.finrank ℝ E - 1) : ℝ)
          * R ^ (Module.finrank ℝ E - 1)) := by
    rw [← ENNReal.ofReal_mul h2m]
    congr 1
    ring
  rwa [hprod] at hmono

/-- **The slab `S_r`** containing the `r`-thickening of the axis parameter set (blueprint
`lem:ml1bootAxisThickeningSubset`).  Two of its three defining inequalities are the relaxations
of the two equations cutting out `Kakeya.ml1Boot.axisParamSet`, and they are what carry the
codimension-two gain. -/
def axisParamSlab (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (r : ℝ) :
    Set (WithLp 2 (E × E)) :=
  {q | |‖(WithLp.ofLp q).1‖ - 1| ≤ r ∧ ‖(WithLp.ofLp q).2‖ ≤ 1 + r ∧
    |(inner ℝ (WithLp.ofLp q).1 (WithLp.ofLp q).2 : ℝ)| ≤ 3 * r}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The slab is closed, hence measurable (blueprint `lem:ml1bootAxisThickeningSubset`). -/
theorem isClosed_axisParamSlab (r : ℝ) : IsClosed (axisParamSlab E r) := by
  have hf : Continuous (fun q : WithLp 2 (E × E) => |‖(WithLp.ofLp q).1‖ - 1|) :=
    continuous_abs.comp
      ((continuous_norm.comp (WithLp.continuous_fst (p := 2) (α := E) (β := E))).sub
        continuous_const)
  have hg :
      Continuous (fun q : WithLp 2 (E × E) =>
        |(inner ℝ (WithLp.ofLp q).1 (WithLp.ofLp q).2 : ℝ)|) :=
    continuous_abs.comp (continuous_inner.comp
      ((WithLp.continuous_fst (p := 2) (α := E) (β := E)).prodMk
        (WithLp.continuous_snd (p := 2) (α := E) (β := E))))
  have hh : Continuous (fun q : WithLp 2 (E × E) => ‖(WithLp.ofLp q).2‖) :=
    continuous_norm.comp (WithLp.continuous_snd (p := 2) (α := E) (β := E))
  rw [show axisParamSlab E r =
      {q : WithLp 2 (E × E) | |‖(WithLp.ofLp q).1‖ - 1| ≤ r} ∩
        ({q : WithLp 2 (E × E) | ‖(WithLp.ofLp q).2‖ ≤ 1 + r} ∩
          {q : WithLp 2 (E × E) | |(inner ℝ (WithLp.ofLp q).1 (WithLp.ofLp q).2 : ℝ)| ≤ 3 * r}) by
    ext q
    simp [axisParamSlab]]
  exact (isClosed_le hf continuous_const).inter
    ((isClosed_le hh continuous_const).inter (isClosed_le hg continuous_const))

/-- **The thickening of the parameter set, described by inequalities** (blueprint
`lem:ml1bootAxisThickeningSubset`): `𝒜 ^ (r) ⊆ S_r` for `0 < r ≤ 1`.  The factor `3` in the third
inequality comes from expanding `⟪ω, p⟫` about a nearest point of `𝒜` and using `r ≤ 1`. -/
theorem cthickening_axisParamSet_subset {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    cthickening r (axisParamSet E) ⊆ axisParamSlab E r := by
  have hcthick : cthickening r (axisParamSet E) =
      ⋃ x ∈ axisParamSet E, closedBall x r :=
    IsCompact.cthickening_eq_biUnion_closedBall isCompact_axisParamSet (le_of_lt hr0)
  -- Step A: each coordinate of a difference in the `L²` product is no larger than the full
  -- distance, `‖x.fst - y.fst‖ ≤ dist x y` and `‖x.snd - y.snd‖ ≤ dist x y`.
  have hfst_le : ∀ q q' : WithLp 2 (E × E),
      ‖(WithLp.ofLp q).1 - (WithLp.ofLp q').1‖ ≤ dist q q' := by
    intro q q'
    have hdist : dist q.fst q'.fst = ‖(WithLp.ofLp q).1 - (WithLp.ofLp q').1‖ := by
      rw [dist_eq_norm]
      congr 1
    rw [← hdist]
    exact WithLp.dist_fst_le q q'
  have hsnd_le : ∀ q q' : WithLp 2 (E × E),
      ‖(WithLp.ofLp q).2 - (WithLp.ofLp q').2‖ ≤ dist q q' := by
    intro q q'
    have hdist : dist q.snd q'.snd = ‖(WithLp.ofLp q).2 - (WithLp.ofLp q').2‖ := by
      rw [dist_eq_norm]
      congr 1
    rw [← hdist]
    exact WithLp.dist_snd_le q q'
  intro q hq
  rw [hcthick] at hq
  rw [Set.mem_iUnion₂] at hq
  rcases hq with ⟨q0, hq0, hqball⟩
  rw [axisParamSet] at hq0
  rcases hq0 with ⟨hw0norm, hw0p0, hp0⟩
  have hdistqq0 : dist q q0 ≤ r := mem_closedBall.mp hqball
  let w : E := (WithLp.ofLp q).1
  let p : E := (WithLp.ofLp q).2
  let w0 : E := (WithLp.ofLp q0).1
  let p0 : E := (WithLp.ofLp q0).2
  change ‖w0‖ = 1 at hw0norm
  change (inner ℝ w0 p0 : ℝ) = 0 at hw0p0
  change ‖p0‖ ≤ 1 at hp0
  have hw_dist : ‖w - w0‖ ≤ r := by
    change ‖(WithLp.ofLp q).1 - (WithLp.ofLp q0).1‖ ≤ r
    exact le_trans (hfst_le q q0) hdistqq0
  have hp_dist : ‖p - p0‖ ≤ r := by
    change ‖(WithLp.ofLp q).2 - (WithLp.ofLp q0).2‖ ≤ r
    exact le_trans (hsnd_le q q0) hdistqq0
  have hr0' : 0 ≤ r := le_of_lt hr0
  have hw1 : |‖w‖ - 1| ≤ r := by
    calc
      |‖w‖ - 1| = |‖w‖ - ‖w0‖| := by rw [← hw0norm]
      _ ≤ ‖w - w0‖ := abs_norm_sub_norm_le w w0
      _ ≤ r := hw_dist
  have hpr : ‖p‖ ≤ 1 + r := by
    have h := norm_sub_norm_le p p0
    linarith [h, hp0, hp_dist]
  have hinner : |(inner ℝ w p : ℝ)| ≤ 3 * r := by
    have hin_expand : (inner ℝ w p : ℝ) =
        (inner ℝ w0 p0 : ℝ) + (inner ℝ w0 (p - p0) : ℝ) + (inner ℝ (w - w0) p : ℝ) := by
      calc
        (inner ℝ w p : ℝ) = (inner ℝ (w0 + (w - w0)) p : ℝ) := by
          nth_rewrite 1 [show w = w0 + (w - w0) by abel]
          rfl
        _ = (inner ℝ w0 p : ℝ) + (inner ℝ (w - w0) p : ℝ) := by
          rw [inner_add_left]
        _ = (inner ℝ w0 (p0 + (p - p0)) : ℝ) + (inner ℝ (w - w0) p : ℝ) := by
          nth_rewrite 1 [show p = p0 + (p - p0) by abel]
          rfl
        _ = (inner ℝ w0 p0 : ℝ) + (inner ℝ w0 (p - p0) : ℝ) + (inner ℝ (w - w0) p : ℝ) := by
          rw [inner_add_right]
    have hcs1 : |(inner ℝ (w - w0) p : ℝ)| ≤ ‖w - w0‖ * ‖p‖ :=
      abs_real_inner_le_norm (w - w0) p
    have hcs2 : |(inner ℝ w0 (p - p0) : ℝ)| ≤ ‖w0‖ * ‖p - p0‖ :=
      abs_real_inner_le_norm w0 (p - p0)
    have hcs1' : |(inner ℝ (w - w0) p : ℝ)| ≤ r * (1 + r) := by
      calc
        |(inner ℝ (w - w0) p : ℝ)| ≤ ‖w - w0‖ * ‖p‖ := hcs1
        _ ≤ r * (1 + r) := mul_le_mul hw_dist hpr (norm_nonneg p) hr0'
    have hcs2' : |(inner ℝ w0 (p - p0) : ℝ)| ≤ r := by
      calc
        |(inner ℝ w0 (p - p0) : ℝ)| ≤ ‖w0‖ * ‖p - p0‖ := hcs2
        _ = ‖p - p0‖ := by rw [hw0norm, one_mul]
        _ ≤ r := hp_dist
    have hzero : |(inner ℝ w0 p0 : ℝ)| = 0 := by rw [hw0p0, abs_zero]
    calc
      |(inner ℝ w p : ℝ)|
          = |(inner ℝ w0 p0 : ℝ) + (inner ℝ w0 (p - p0) : ℝ) + (inner ℝ (w - w0) p : ℝ)| := by
            rw [hin_expand]
      _ ≤ |(inner ℝ w0 p0 : ℝ)| + |(inner ℝ w0 (p - p0) : ℝ)| + |(inner ℝ (w - w0) p : ℝ)| := by
        have h1 := abs_add_le ((inner ℝ w0 p0 : ℝ)) ((inner ℝ w0 (p - p0) : ℝ))
        have h2 := abs_add_le (((inner ℝ w0 p0 : ℝ) + (inner ℝ w0 (p - p0) : ℝ)))
          ((inner ℝ (w - w0) p : ℝ))
        linarith
      _ ≤ r * (1 + r) + r := by linarith [hcs1', hcs2', hzero]
      _ ≤ 3 * r := by nlinarith [mul_nonneg hr0' (sub_nonneg.mpr hr1)]
  change |‖w‖ - 1| ≤ r ∧ ‖p‖ ≤ 1 + r ∧ |(inner ℝ w p : ℝ)| ≤ 3 * r
  exact ⟨hw1, hpr, hinner⟩

/-- **A product set with uniformly small sections** (blueprint
`lem:ml1bootProductSectionVolume`): a measurable subset of `Ω × E` all of whose sections have
measure at most `M` has measure at most `M · |Ω|`.  This is Tonelli in the form
`MeasureTheory.Measure.prod_apply_le`, transported across `WithLp.volume_preserving_ofLp`. -/
theorem volume_le_of_forall_section_le {Ω : Set E} (hΩ : MeasurableSet Ω) {M : ENNReal}
    {S : Set (WithLp 2 (E × E))} (hS : MeasurableSet S)
    (hsub : ∀ q ∈ S, (WithLp.ofLp q).1 ∈ Ω)
    (hsec : ∀ ω ∈ Ω, volume {p : E | (WithLp.toLp 2 (ω, p)) ∈ S} ≤ M) :
    volume S ≤ M * volume Ω := by
  let S' : Set (E × E) := (WithLp.toLp 2) ⁻¹' S
  have hmp : MeasurePreserving (@WithLp.ofLp 2 (E × E)) :=
    WithLp.volume_preserving_ofLp E E
  have hS'meas : MeasurableSet S' := by
    dsimp [S']
    exact hS.preimage (WithLp.measurable_toLp (p := 2) (X := E × E))
  have hS_eq : S = (@WithLp.ofLp 2 (E × E)) ⁻¹' S' := by
    ext q
    simp [S']
  have hvol : volume S = (volume : Measure (E × E)) S' := by
    rw [hS_eq]
    exact hmp.measure_preimage hS'meas.nullMeasurableSet
  have hle : (volume : Measure (E × E)) S' ≤
      ∫⁻ ω, (volume : Measure E) (Prod.mk ω ⁻¹' S') ∂(volume : Measure E) := by
    rw [MeasureTheory.Measure.volume_eq_prod E E]
    exact MeasureTheory.Measure.prod_apply_le hS'meas
  have hsec_eq : ∀ ω : E, Prod.mk ω ⁻¹' S' = {p : E | (WithLp.toLp 2 (ω, p)) ∈ S} := by
    intro ω
    ext p
    simp [S']
  have hmono : (∫⁻ ω, (volume : Measure E) (Prod.mk ω ⁻¹' S') ∂(volume : Measure E)) ≤
      ∫⁻ ω, Ω.indicator (fun _ => M) ω ∂(volume : Measure E) := by
    apply MeasureTheory.lintegral_mono
    intro ω
    change volume (Prod.mk ω ⁻¹' S') ≤ Ω.indicator (fun _ => M) ω
    rw [hsec_eq ω]
    by_cases hω : ω ∈ Ω
    · rw [Set.indicator_of_mem hω]
      exact hsec ω hω
    · rw [Set.indicator_of_notMem hω]
      have hsec_empty : {p : E | (WithLp.toLp 2 (ω, p)) ∈ S} = ∅ := by
        ext p
        exact iff_false_intro (fun hp => hω
          (by simpa [WithLp.ofLp_toLp] using hsub (WithLp.toLp 2 (ω, p)) hp))
      rw [hsec_empty]
      simp
  have hfinal : (∫⁻ ω, Ω.indicator (fun _ => M) ω ∂(volume : Measure E)) = M * volume Ω := by
    exact MeasureTheory.lintegral_indicator_const hΩ M
  calc
    volume S = (volume : Measure (E × E)) S' := hvol
    _ ≤ ∫⁻ ω, (volume : Measure E) (Prod.mk ω ⁻¹' S') ∂(volume : Measure E) := hle
    _ ≤ ∫⁻ ω, Ω.indicator (fun _ => M) ω ∂(volume : Measure E) := hmono
    _ = M * volume Ω := hfinal

/-- **The constant `C_{lem:ml1bootAxisThickeningVolume}(n) = 24 n 3 ^ (n-1) ω_n ω_{n-1}`**
(blueprint `def:ml1bootAxisThickeningConstant`).  It is the product of the two factors produced
by `Kakeya.ml1Boot.volume_annulus_le` (namely `n 2 ^ n ω_n`) and
`Kakeya.ml1Boot.volume_slab_inter_ball_le` (namely `12 ω_{n-1} (3/2) ^ (n-1)`), and depends only
on the ambient dimension. -/
noncomputable def axisThickening.C (n : ℕ) : NNReal :=
  24 * n * 3 ^ (n - 1) * unitBallVolume n * unitBallVolume (n - 1)

/-- **The codimension-two thickening estimate** (blueprint `lem:ml1bootAxisThickeningVolume`):
`|𝒜 ^ (r)| ≤ C(n) r ^ 2` for `0 < r ≤ 1/2`.  The exponent `2` — not `1` — is the whole gain of
`Kakeya.ml1Boot.card_le` over the crude count, and it is where the two defining equations of
`Kakeya.ml1Boot.axisParamSet` are spent.  The hypothesis `r ≤ 1/2`, rather than merely `r ≤ 1`,
is needed for the section estimate: at `r = 1` the annulus contains `ω = 0`, whose section is
the whole ball. -/
theorem volume_cthickening_axisParamSet_le [Nontrivial E] {r : ℝ} (hr0 : 0 < r) (hr : r ≤ 1 / 2) :
    volume (cthickening r (axisParamSet E))
      ≤ ENNReal.ofReal ((axisThickening.C (Module.finrank ℝ E) : ℝ) * r ^ 2) := by
  set n : ℕ := Module.finrank ℝ E
  let Ω : Set E := {ω : E | |‖ω‖ - 1| ≤ r}
  let ωn : NNReal := unitBallVolume n
  let ωnm : NNReal := unitBallVolume (n - 1)
  let A : ℝ := 2 * (6 * r) * (ωnm : ℝ) * (1 + r) ^ (n - 1)
  let B : ℝ := (n : ℝ) * (2 : ℝ) ^ n * (ωn : ℝ) * r
  let Cℝ : ℝ := 24 * (n : ℝ) * (3 : ℝ) ^ (n - 1) * (ωn : ℝ) * (ωnm : ℝ)
  let M : ENNReal := ENNReal.ofReal A
  have hn1 : 1 ≤ n := Module.finrank_pos (R := ℝ) (M := E)
  have hr_nonneg : 0 ≤ r := le_of_lt hr0
  have hωn0 : 0 ≤ (ωn : ℝ) := (ωn : NNReal).property
  have hωnm0 : 0 ≤ (ωnm : ℝ) := (ωnm : NNReal).property
  -- Ω is closed, hence measurable
  have hΩ_closed : IsClosed Ω := by
    unfold Ω
    have hf : Continuous (fun ω : E => |‖ω‖ - 1|) :=
      continuous_abs.comp (continuous_norm.sub continuous_const)
    exact isClosed_le hf continuous_const
  have hΩmeas : MeasurableSet Ω := hΩ_closed.measurableSet
  -- Step 1: the thickening is contained in the slab
  have hsubset : cthickening r (axisParamSet E) ⊆ axisParamSlab E r :=
    cthickening_axisParamSet_subset hr0 (by linarith)
  have hvol_cthick : volume (cthickening r (axisParamSet E)) ≤ volume (axisParamSlab E r) :=
    measure_mono hsubset
  -- Section web for the slab
  have hsub_Ω : ∀ q ∈ axisParamSlab E r, (WithLp.ofLp q).1 ∈ Ω := by
    intro q hq
    have hq1 : |‖(WithLp.ofLp q).1‖ - 1| ≤ r := by
      have hfull : |‖(WithLp.ofLp q).1‖ - 1| ≤ r ∧ ‖(WithLp.ofLp q).2‖ ≤ 1 + r ∧
          |(inner ℝ (WithLp.ofLp q).1 (WithLp.ofLp q).2 : ℝ)| ≤ 3 * r := by
        simpa [axisParamSlab] using hq
      exact hfull.1
    simpa [Ω] using hq1
  have hsec : ∀ ω ∈ Ω, volume {p : E | (WithLp.toLp 2 (ω, p)) ∈ axisParamSlab E r} ≤ M := by
    intro ω hω
    have hωsat : |‖ω‖ - 1| ≤ r := by simpa [Ω] using hω
    have hwge : 1 - r ≤ ‖ω‖ := by
      have h := (abs_le.mp hωsat).1
      linarith
    have h1r_gt0 : 0 < 1 - r := by linarith
    have hwgt0 : 0 < ‖ω‖ := lt_of_lt_of_le h1r_gt0 hwge
    let u : E := ‖ω‖⁻¹ • ω
    have hu : ‖u‖ = 1 := by
      have hne : ‖ω‖ ≠ 0 := ne_of_gt hwgt0
      have hnonneg : 0 ≤ ‖ω‖⁻¹ := inv_nonneg.mpr (norm_nonneg ω)
      change ‖‖ω‖⁻¹ • ω‖ = 1
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hnonneg, inv_mul_cancel₀ hne]
    have hsec_sub :
        {p : E | (WithLp.toLp 2 (ω, p)) ∈ axisParamSlab E r} ⊆
          {p : E | ‖p‖ ≤ 1 + r ∧ |(inner ℝ u p : ℝ)| ≤ 6 * r} := by
      intro p hp
      simp only [axisParamSlab] at hp
      rcases hp with ⟨_, hpnorm, hinner⟩
      constructor
      · exact hpnorm
      · have h_inner_u : (inner ℝ u p : ℝ) = ‖ω‖⁻¹ * (inner ℝ ω p : ℝ) := by
          change (inner ℝ (‖ω‖⁻¹ • ω) p : ℝ) = ‖ω‖⁻¹ * (inner ℝ ω p : ℝ)
          rw [real_inner_smul_left]
        have hwinv_le : ‖ω‖⁻¹ ≤ (1 - r)⁻¹ := (inv_le_inv₀ hwgt0 h1r_gt0).mpr hwge
        have hfrac : 3 / (1 - r) ≤ 6 := by
          rw [div_le_iff₀ h1r_gt0]
          nlinarith [hr]
        calc
          |(inner ℝ u p : ℝ)| = |‖ω‖⁻¹ * (inner ℝ ω p : ℝ)| := by rw [h_inner_u]
          _ = ‖ω‖⁻¹ * |(inner ℝ ω p : ℝ)| := by
            rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg ω))]
          _ ≤ ‖ω‖⁻¹ * (3 * r) := by
            exact mul_le_mul_of_nonneg_left hinner (inv_nonneg.mpr (norm_nonneg ω))
          _ ≤ (1 - r)⁻¹ * (3 * r) := by
            exact mul_le_mul_of_nonneg_right hwinv_le (mul_nonneg (by norm_num) hr_nonneg)
          _ = (3 * r) / (1 - r) := by ring
          _ = (3 / (1 - r)) * r := by ring
          _ ≤ 6 * r := by
            exact mul_le_mul_of_nonneg_right hfrac hr_nonneg
    have hvol_u : volume {p : E | ‖p‖ ≤ 1 + r ∧ |(inner ℝ u p : ℝ)| ≤ 6 * r} ≤ M := by
      simpa [M, A, ωnm] using
        (volume_slab_inter_ball_le (u := u) hu (h := 6 * r) (R := 1 + r)
          (mul_nonneg (by norm_num) hr_nonneg) (by linarith : 0 ≤ 1 + r))
    exact (measure_mono hsec_sub).trans hvol_u
  -- Step 2: the slab measure is bounded by M·|Ω|
  have hslab : volume (axisParamSlab E r) ≤ M * volume Ω := by
    exact volume_le_of_forall_section_le (Ω := Ω) hΩmeas (M := M)
      (S := axisParamSlab E r) (isClosed_axisParamSlab r).measurableSet hsub_Ω hsec
  -- Step 3: |Ω| ≤ B
  have hΩvol : volume Ω ≤ ENNReal.ofReal B := by
    simpa [Ω, B, n, ωn] using (volume_annulus_le (E := E) hr0 (by linarith : r ≤ 1))
  -- algebra: Cℝ equals the coerced constant
  have hCℝ_eq : (axisThickening.C n : ℝ) * r ^ 2 = Cℝ * r ^ 2 := by
    simp [axisThickening.C, Cℝ, ωn, ωnm]
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  have hmain_enn : M * volume Ω ≤ ENNReal.ofReal (A * B) := by
    calc
      M * volume Ω ≤ M * ENNReal.ofReal B := mul_le_mul' le_rfl hΩvol
      _ = ENNReal.ofReal A * ENNReal.ofReal B := by simp [M]
      _ = ENNReal.ofReal (A * B) := by rw [← ENNReal.ofReal_mul hA_nonneg]
  -- Step 4: A·B ≤ Cℝ r²
  have h2pow : (2 : ℝ) ^ n = (2 : ℝ) ^ (n - 1) * 2 := by
    rw [← pow_succ, Nat.sub_add_cancel hn1]
  have hpow_id : (2 : ℝ) ^ n * ((3 : ℝ) / 2) ^ (n - 1) = 2 * (3 : ℝ) ^ (n - 1) := by
    calc
      (2 : ℝ) ^ n * ((3 : ℝ) / 2) ^ (n - 1)
          = (2 ^ (n - 1) * 2) * ((3 : ℝ) / 2) ^ (n - 1) := by rw [h2pow]
      _ = 2 * (2 ^ (n - 1) * ((3 : ℝ) / 2) ^ (n - 1)) := by ring
      _ = 2 * (2 * ((3 : ℝ) / 2)) ^ (n - 1) := by rw [← mul_pow]
      _ = 2 * (3 : ℝ) ^ (n - 1) := by
        have h23 : (2 : ℝ) * (3 / 2) = 3 := by ring
        rw [h23]
  have hA_le' : A ≤ 12 * r * (ωnm : ℝ) * ((3 : ℝ) / 2) ^ (n - 1) := by
    have h16 : 2 * (6 * r) = 12 * r := by ring
    have hpow_le : (1 + r) ^ (n - 1) ≤ ((3 : ℝ) / 2) ^ (n - 1) :=
      pow_le_pow_left₀ (by linarith : 0 ≤ 1 + r) (by linarith : 1 + r ≤ (3 : ℝ) / 2) (n - 1)
    calc
      A = 2 * (6 * r) * (ωnm : ℝ) * (1 + r) ^ (n - 1) := by simp [A]
      _ = 12 * r * (ωnm : ℝ) * (1 + r) ^ (n - 1) := by rw [h16]
      _ ≤ 12 * r * (ωnm : ℝ) * ((3 : ℝ) / 2) ^ (n - 1) := by
        exact mul_le_mul_of_nonneg_left hpow_le
          (mul_nonneg (mul_nonneg (by norm_num) hr_nonneg) hωnm0)
  have hAB_main : A * B ≤ Cℝ * r ^ 2 := by
    calc
      A * B = A * ((n : ℝ) * (2 : ℝ) ^ n * (ωn : ℝ) * r) := by simp [B]
      _ ≤ (12 * r * (ωnm : ℝ) * ((3 : ℝ) / 2) ^ (n - 1))
          * ((n : ℝ) * (2 : ℝ) ^ n * (ωn : ℝ) * r) := by
            exact mul_le_mul_of_nonneg_right hA_le' hB_nonneg
      _ = 12 * (n : ℝ) * ((2 : ℝ) ^ n * ((3 : ℝ) / 2) ^ (n - 1))
          * (ωn : ℝ) * (ωnm : ℝ) * r * r := by ring
      _ = 12 * (n : ℝ) * (2 * (3 : ℝ) ^ (n - 1)) * (ωn : ℝ) * (ωnm : ℝ) * r * r := by
            rw [hpow_id]
      _ = Cℝ * r ^ 2 := by
        dsimp [Cℝ]
        ring
  have hfinal : ENNReal.ofReal (A * B) ≤ ENNReal.ofReal ((axisThickening.C n : ℝ) * r ^ 2) := by
    apply ENNReal.ofReal_le_ofReal
    rwa [hCℝ_eq]
  calc
    volume (cthickening r (axisParamSet E)) ≤ volume (axisParamSlab E r) := hvol_cthick
    _ ≤ M * volume Ω := hslab
    _ ≤ ENNReal.ofReal (A * B) := hmain_enn
    _ ≤ ENNReal.ofReal ((axisThickening.C n : ℝ) * r ^ 2) := hfinal

/-! ### The assembly -/

/-- **At most `8 n + 1` tubes per axis cell** (blueprint `lem:ml1bootAxisCellCard`): a family of
pairwise essentially distinct `δ`-tubes in `B̄(0, 1)` whose axis parameters all lie within
`ρ = c_* δ / 6` of one point `g` has at most `8 n + 1` members.

The cell radius is `c_* δ / 6` and not `c_* δ / 3` because the triangle inequality doubles it
when comparing two members of the cell; `Kakeya.ml1Boot.cStar_lt_abs_axialCoord_sub` then
separates their axial coordinates by more than `c_*`, and
`Kakeya.ml1Boot.card_le_of_separated_Icc` at `c = c_*` counts them.

The cell is presented as *any* finite family lying in it rather than as a `Finset.filter`, which
would need a decidability instance; the two readings are equivalent. -/
theorem card_axisCell_le [Nontrivial E] {ι : Type*} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (s : Finset ι) (T : ι → Tube δ E)
    (hball : ∀ i ∈ s, (T i).carrier ⊆ closedBall 0 1)
    (hED : (s : Set ι).Pairwise fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier)
    (g : WithLp 2 (E × E)) (hcell : ∀ i ∈ s, dist (axisParam (T i)) g ≤ cStar E * (δ : ℝ) / 6) :
    s.card ≤ 8 * Module.finrank ℝ E + 1 := by
  let F : Finset ℝ := s.image fun i => axialCoord (T i)
  have hfin_nat_pos : 0 < Module.finrank ℝ E := Module.finrank_pos (R := ℝ) (M := E)
  have hfin_real_pos : (0 : ℝ) < (Module.finrank ℝ E : ℝ) := by exact_mod_cast hfin_nat_pos
  have hcstar_pos : 0 < cStar E := by
    rw [cStar]
    exact one_div_pos.mpr (mul_pos (by norm_num) hfin_real_pos)
  -- Step A: each coordinate of a difference in the `L²` product is no larger than the full
  -- distance, `‖x.fst - y.fst‖ ≤ dist x y` and `‖x.snd - y.snd‖ ≤ dist x y`.
  have hfst_le : ∀ q q' : WithLp 2 (E × E),
      ‖(WithLp.ofLp q).1 - (WithLp.ofLp q').1‖ ≤ dist q q' := by
    intro q q'
    have hdist : dist q.fst q'.fst = ‖(WithLp.ofLp q).1 - (WithLp.ofLp q').1‖ := by
      rw [dist_eq_norm]
      congr 1
    rw [← hdist]
    exact WithLp.dist_fst_le q q'
  have hsnd_le : ∀ q q' : WithLp 2 (E × E),
      ‖(WithLp.ofLp q).2 - (WithLp.ofLp q').2‖ ≤ dist q q' := by
    intro q q'
    have hdist : dist q.snd q'.snd = ‖(WithLp.ofLp q).2 - (WithLp.ofLp q').2‖ := by
      rw [dist_eq_norm]
      congr 1
    rw [← hdist]
    exact WithLp.dist_snd_le q q'
  have hfst_axis : ∀ i : ι, (WithLp.ofLp (axisParam (T i))).1 = (T i).direction := by
    intro i
    rw [axisParam, WithLp.ofLp_toLp]
  have hsnd_axis : ∀ i : ι, (WithLp.ofLp (axisParam (T i))).2 = axisFoot (T i) := by
    intro i
    rw [axisParam, WithLp.ofLp_toLp]
  have hsep_pair : ∀ ⦃i j : ι⦄, i ∈ s → j ∈ s → i ≠ j →
      cStar E < |axialCoord (T i) - axialCoord (T j)| := by
    intro i j hi hj hij
    have hed : IsEssentiallyDistinct (T i).carrier (T j).carrier := hED hi hj hij
    have hd_total : dist (axisParam (T i)) (axisParam (T j)) ≤ cStar E * (δ : ℝ) / 3 := by
      calc
        dist (axisParam (T i)) (axisParam (T j))
            ≤ dist (axisParam (T i)) g + dist (axisParam (T j)) g := by
              simpa [dist_comm] using dist_triangle (axisParam (T i)) g (axisParam (T j))
        _ ≤ cStar E * (δ : ℝ) / 6 + cStar E * (δ : ℝ) / 6 := by
          exact add_le_add (hcell i hi) (hcell j hj)
        _ = cStar E * (δ : ℝ) / 3 := by ring
    have hω : ‖(T i).direction - (T j).direction‖ ≤ cStar E * (δ : ℝ) / 3 := by
      calc
        ‖(T i).direction - (T j).direction‖
            = ‖(WithLp.ofLp (axisParam (T i))).1 - (WithLp.ofLp (axisParam (T j))).1‖ := by
              rw [← hfst_axis i, ← hfst_axis j]
        _ ≤ dist (axisParam (T i)) (axisParam (T j)) := hfst_le (axisParam (T i)) (axisParam (T j))
        _ ≤ cStar E * (δ : ℝ) / 3 := hd_total
    have hp : ‖axisFoot (T i) - axisFoot (T j)‖ ≤ cStar E * (δ : ℝ) / 3 := by
      calc
        ‖axisFoot (T i) - axisFoot (T j)‖
            = ‖(WithLp.ofLp (axisParam (T i))).2 - (WithLp.ofLp (axisParam (T j))).2‖ := by
              rw [← hsnd_axis i, ← hsnd_axis j]
        _ ≤ dist (axisParam (T i)) (axisParam (T j)) := hsnd_le (axisParam (T i)) (axisParam (T j))
        _ ≤ cStar E * (δ : ℝ) / 3 := hd_total
    exact cStar_lt_abs_axialCoord_sub hδ0 hδ1 (T i) (T j) (hball i hi) (hball j hj) hed hω hp
  have hinj : (s : Set ι).InjOn fun i => axialCoord (T i) := by
    intro i hi j hj hcoord
    by_contra hne
    have hlt : cStar E < |axialCoord (T i) - axialCoord (T j)| := hsep_pair hi hj hne
    have hzero : |axialCoord (T i) - axialCoord (T j)| = 0 := by
      have hcoord' : axialCoord (T i) = axialCoord (T j) := hcoord
      rw [hcoord', sub_self, abs_zero]
    rw [hzero] at hlt
    linarith [hcstar_pos]
  have hFcard : F.card = s.card := by
    simpa [F] using (Finset.card_image_of_injOn hinj)
  have hF_icc : ∀ a ∈ F, a ∈ Set.Icc (-1 : ℝ) 1 := by
    intro a ha
    rcases Finset.mem_image.mp ha with ⟨i, hi, rfl⟩
    have habs : |axialCoord (T i)| ≤ 1 := abs_axialCoord_le_one (T i) (hball i hi)
    exact (abs_le.mp habs)
  have hF_sep : (F : Set ℝ).Pairwise fun a b => cStar E < |a - b| := by
    intro a ha b hb hne
    rcases Finset.mem_image.mp ha with ⟨i, hi, rfl⟩
    rcases Finset.mem_image.mp hb with ⟨j, hj, rfl⟩
    have hij : i ≠ j := by
      intro hij
      exact hne (by rw [hij])
    exact hsep_pair hi hj hij
  have hconst : (2 : ℝ) / cStar E = 8 * (Module.finrank ℝ E : ℝ) := by
    rw [cStar]
    have hfin_ne : (4 * (Module.finrank ℝ E : ℝ)) ≠ 0 := by nlinarith [hfin_real_pos]
    field_simp [hfin_ne]
    ring
  have hcard_real : (s.card : ℝ) ≤ 8 * (Module.finrank ℝ E : ℝ) + 1 := by
    calc
      (s.card : ℝ) = (F.card : ℝ) := by rw [hFcard]
      _ ≤ 2 / cStar E + 1 := card_le_of_separated_Icc hcstar_pos F hF_icc hF_sep
      _ = 8 * (Module.finrank ℝ E : ℝ) + 1 := by rw [hconst]
  exact_mod_cast hcard_real

end Kakeya.ml1Boot
