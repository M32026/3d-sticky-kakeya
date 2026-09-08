/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Uniform
public import Kakeya.ShadedUniform
public import Kakeya.Tube.Nets
public import Kakeya.Mathlib.Analysis.IsSeparated
public import Kakeya.DimensionThree.MainLemma2.LineEssDistinct

/-!
# The canonical centred cover — the geometric keystone of the centred-net route (U1)

Source of record: the professor's refined proof
`260115_kakeyadetailedproofv3_revised_detailed.tex` , mapped ; this leaf is the keystone of row **U1** of its §4.1, cut as
 records.

## What is here

* **Centred tubes** (refined l.4852–4855): `Tube.IsCentred T` says `⟪midpoint, direction⟫ = 0`,
  "this removes the otherwise uncontrolled axial slide of the core along its supporting line". For a centred unit tube the pair `(midpoint, direction)` *is* the line parameter `(p, d)`,
  `p ⊥ d`, `‖d‖ = 1`, of `lemcanonicalcover` (l.4786–4787). * **Line geometry.** `Tube.lineDist o d z = ‖(z - o) - ⟪z - o, d⟫ d‖` is the distance from `z`
  to the line `t ↦ o + t d` (`‖d‖ = 1`), and `Tube.mem_cthickening_line_iff` identifies the
  closed neighbourhood `N_r(L)` of refined l.153–157 with `{lineDist ≤ r}`. Then, for a tube
  whose carrier lies in `N_{Kρ}(L)`: its core lies in `N_{Kρ-δ}(L)`
  (`Tube.lineDist_le_of_carrier_subset`), its direction is within `4(Kρ-δ)` of `±d`
  (`Tube.exists_sign_norm_direction_sub_le`), and — the centring step — a **centred** tube's
  midpoint is within `(Kρ-δ)(1 + 4‖midpoint‖)` of the foot `o - ⟪o, d⟫ d` of the line
  (`Tube.norm_midpoint_sub_foot_le_of_isCentred`). Without centring the midpoint slides freely
  along `L` — the "fifth axial parameter" of refined l.159–163, and the reason the existing grid-net
  nodes are not line-essentially distinct. * **Packing** (refined l.4790–4800, "the disjoint balls of radius `r/2` about the net points lie
  in balls of radius `(111+1/2)r`; volume comparison"): `Tube.card_filter_line_le_of_centred_sep`
  bounds the members of an `ε`-separated (in the `L¹` metric on `(midpoint, direction)`) family of
  centred tubes lying in `N_{Kρ}(L)` by `2 · ((Rx + ε/4)/(ε/4))ⁿ · ((Ry + ε/4)/(ε/4))ⁿ`, with
  `Rx`, `Ry` the two radii above and the factor `2` the two orientations of `L` (the refined text's
  "one of two balls of radius `111r`"). The volume comparison is the existing
  `Tube.card_le_of_L1_separated_in_rectangle`. * **The centred net** (refined l.4786–4789, "Take a maximal `r`-separated subset of this compact
  subset of `ℝ⁶`"): `Tube.exists_centred_net` — a finite family of centred `ρ`-tubes whose
  parameters are `ε`-separated and `2ε`-cover every centred line parameter with `‖p‖ ≤ R₀`. * **Exact containment** (refined l.4789–4791, "take the `4r`-neighbourhood of the centred unit
  segment on the corresponding line … give the asserted containment"):
  `Tube.le_of_params_close`, the existing `Tube.tube_le_rescale_of_close` read at the node's own
  radius.

## The E0 definitions

`Kakeya.VeryNotSticky.lineSet`, `lineNbhd`, `IsLineEssDistinct`, `IsLineEssDistinctAt` are
imported from the existing E0 leaf `LineEssDistinct.lean` (base `844735815`).  Since  existing `LineEDLevelsAt`, this leaf states its
per-level outputs both flat (`∀ k, k < N → …`) and as E0's `LineEDLevelsAt K` / `LineEDLevels`
(`lineEDLevelsAt_activeRestrict_of_centred`, `lineEDLevelsAt_C3_activeRestrict_of_centred`,
`lineEDLevels_activeRestrict_of_centred`; ).
`Tube.IsCentred` is defined in `Kakeya/Tube/Basic.lean`.

## What is *not* here, and why

The refined text's `lemcanonicalcover` is stated for sets `X_i ⊂ B̄(0, 2/5)` that need not be
centred; its exact containment uses the shortness of the `X_i`.  In the tree every family on
Lemma 9.1's path consists of unit tubes (`Tube`), and a non-centred unit member is not inside any
centred unit node (its axial position is off by up to `1/2`).  So the cover here is for
**centred** members — the object the refined text actually uses at every level of its towers
(`propthreadedtower`, l.4900–4907: "If the original tubes are centred, the coarse levels may be
chosen centred"); how a family becomes centred (the refined text's caller-side step,
l.5990–6013) is the statement question , §6, not this leaf's.
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped NNReal ENNReal RealInnerProductSpace

/-! ## The E0 definitions (`LineEssDistinct.lean`) — two spellings of the same line, for this leaf -/

namespace Kakeya.VeryNotSticky

/-- The line as a range (this leaf's spelling of `lineSet`). -/
theorem lineSet_eq_range {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (p d : F) :
    lineSet p d = Set.range (fun t : ℝ ↦ p + t • d) := by
  ext y
  simp only [lineSet, Set.mem_setOf_eq, Set.mem_range]
  exact ⟨fun ⟨t, h⟩ ↦ ⟨t, h.symm⟩, fun ⟨t, h⟩ ↦ ⟨t, h.symm⟩⟩

/-- The closed line neighbourhood, in this leaf's spelling. -/
theorem lineNbhd_eq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (p d : F) (r : ℝ) :
    lineNbhd p d r = Metric.cthickening r (Set.range (fun t : ℝ ↦ p + t • d)) := by
  unfold lineNbhd; rw [lineSet_eq_range]

end Kakeya.VeryNotSticky

/-! ## Centred tubes and the geometry of line parameters -/

namespace Tube

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E]

/-! `Tube.IsCentred` is D0 , defined once in `Kakeya/Tube/Basic.lean`. -/

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- The canonical tube with a prescribed midpoint and unit direction is centred iff the two are
orthogonal. -/
theorem isCentred_ofMidpointDirection {δ : NNReal} {m u : E} (hu : ‖u‖ = 1)
    (h : ⟪m, u⟫ = 0) : (ofMidpointDirection δ m u hu).IsCentred := by
  unfold IsCentred
  have hm : (ofMidpointDirection δ m u hu).midpoint = m := by
    simp only [Tube.midpoint, ofMidpointDirection_x, ofMidpointDirection_y]
    module
  have hd : (ofMidpointDirection δ m u hu).direction = u := by
    simp only [Tube.direction, ofMidpointDirection_x, ofMidpointDirection_y]
    module
  rw [hm, hd, h]

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
theorem midpoint_ofMidpointDirection' {δ : NNReal} (m u : E) (hu : ‖u‖ = 1) :
    (ofMidpointDirection δ m u hu).midpoint = m := by
  simp only [Tube.midpoint, ofMidpointDirection_x, ofMidpointDirection_y]
  module

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
theorem direction_ofMidpointDirection' {δ : NNReal} (m u : E) (hu : ‖u‖ = 1) :
    (ofMidpointDirection δ m u hu).direction = u := by
  simp only [Tube.direction, ofMidpointDirection_x, ofMidpointDirection_y]
  module

/-! ### The core of a tube in midpoint–direction coordinates -/

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- The endpoints in midpoint–direction coordinates. -/
theorem x_eq_midpoint_sub {δ : NNReal} (T : Tube δ E) :
    T.x = T.midpoint - (1 / 2 : ℝ) • T.direction := by
  simp only [Tube.midpoint, Tube.direction]; module

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
theorem y_eq_midpoint_add {δ : NNReal} (T : Tube δ E) :
    T.y = T.midpoint + (1 / 2 : ℝ) • T.direction := by
  simp only [Tube.midpoint, Tube.direction]; module

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- A point of the core segment is `midpoint + t • direction` with `|t| ≤ 1/2`. -/
theorem exists_param_of_mem_segment {δ : NNReal} (T : Tube δ E) {z : E}
    (hz : z ∈ segment ℝ T.x T.y) :
    ∃ t : ℝ, |t| ≤ 1 / 2 ∧ z = T.midpoint + t • T.direction := by
  rw [segment_eq_image'] at hz
  obtain ⟨θ, hθ, rfl⟩ := hz
  refine ⟨θ - 1 / 2, ?_, ?_⟩
  · rw [abs_le]; constructor <;> linarith [hθ.1, hθ.2]
  · rw [x_eq_midpoint_sub, Tube.direction]
    simp only [Tube.midpoint] at *
    module

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- Conversely every such point lies on the core. -/
theorem midpoint_add_smul_mem_segment {δ : NNReal} (T : Tube δ E) {t : ℝ} (ht : |t| ≤ 1 / 2) :
    T.midpoint + t • T.direction ∈ segment ℝ T.x T.y := by
  rw [segment_eq_image']
  refine ⟨t + 1 / 2, ⟨by linarith [(abs_le.mp ht).1], by linarith [(abs_le.mp ht).2]⟩, ?_⟩
  simp only [Tube.midpoint, Tube.direction]
  module

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- Core points belong to the carrier. -/
theorem mem_carrier_of_mem_segment {δ : NNReal} (T : Tube δ E) {z : E}
    (hz : z ∈ segment ℝ T.x T.y) : z ∈ T.carrier := by
  rw [T.carrier_eq]
  exact Set.mem_biUnion hz (Metric.mem_closedBall_self δ.coe_nonneg)

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- A point within `δ` of a core point belongs to the carrier. -/
theorem mem_carrier_of_dist_le {δ : NNReal} (T : Tube δ E) {z w : E}
    (hz : z ∈ segment ℝ T.x T.y) (hw : dist w z ≤ δ) : w ∈ T.carrier := by
  rw [T.carrier_eq]
  exact Set.mem_biUnion hz (Metric.mem_closedBall.mpr hw)

/-! ### Distance to a line -/

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E] in
/-- The distance from `z` to the line `t ↦ o + t • d` (for `‖d‖ = 1`), as the norm of the
component of `z - o` orthogonal to `d`. -/
noncomputable def lineDist (o d z : E) : ℝ := ‖(z - o) - ⟪z - o, d⟫ • d‖

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E] in
/-- The orthogonal component is orthogonal to `d`. -/
theorem inner_perp_eq_zero (o d z : E) (hd : ‖d‖ = 1) :
    ⟪(z - o) - ⟪z - o, d⟫ • d, d⟫ = 0 := by
  rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hd]
  ring

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E] in
/-- Pythagoras along the line: `‖z - (o + t d)‖² = lineDist² + (⟪z - o, d⟫ - t)²`. -/
theorem norm_sub_line_point_sq (o d z : E) (hd : ‖d‖ = 1) (t : ℝ) :
    ‖z - (o + t • d)‖ ^ 2 = lineDist o d z ^ 2 + (⟪z - o, d⟫ - t) ^ 2 := by
  have hsplit : z - (o + t • d) = ((z - o) - ⟪z - o, d⟫ • d) + (⟪z - o, d⟫ - t) • d := by
    module
  rw [hsplit, norm_add_sq_real, real_inner_smul_right, inner_perp_eq_zero o d z hd, norm_smul,
    hd, Real.norm_eq_abs]
  simp only [lineDist, mul_zero, add_zero, mul_one, sq_abs]

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E] in
/-- The orthogonal component is a lower bound for the distance to every point of the line. -/
theorem lineDist_le_norm_sub (o d z : E) (hd : ‖d‖ = 1) (t : ℝ) :
    lineDist o d z ≤ ‖z - (o + t • d)‖ := by
  have h := norm_sub_line_point_sq o d z hd t
  have h0 : 0 ≤ lineDist o d z := norm_nonneg _
  nlinarith [sq_nonneg (⟪z - o, d⟫ - t), norm_nonneg (z - (o + t • d))]

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E] in
/-- …and it is attained at the foot of the perpendicular. -/
theorem norm_sub_foot_eq (o d z : E) (hd : ‖d‖ = 1) :
    ‖z - (o + ⟪z - o, d⟫ • d)‖ = lineDist o d z := by
  have h := norm_sub_line_point_sq o d z hd ⟪z - o, d⟫
  simp only [sub_self, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, add_zero] at h
  have h0 : 0 ≤ lineDist o d z := norm_nonneg _
  nlinarith [norm_nonneg (z - (o + ⟪z - o, d⟫ • d))]

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E] in
/-- **The closed neighbourhood of a line is a level set of `lineDist`.** This identifies the
`N_{5δ}(L)` of refined l.153–157 (as `Metric.cthickening`) with an explicit inequality. -/
theorem mem_cthickening_line_iff {o d z : E} (hd : ‖d‖ = 1) {r : ℝ} (hr : 0 ≤ r) :
    z ∈ Metric.cthickening r (Set.range fun t : ℝ ↦ o + t • d) ↔ lineDist o d z ≤ r := by
  constructor
  · intro hz
    rw [Metric.mem_cthickening_iff] at hz
    have hle : ENNReal.ofReal (lineDist o d z) ≤
        Metric.infEDist z (Set.range fun t : ℝ ↦ o + t • d) := by
      rw [Metric.le_infEDist]
      rintro y ⟨t, rfl⟩
      rw [edist_dist, dist_eq_norm]
      exact ENNReal.ofReal_le_ofReal (lineDist_le_norm_sub o d z hd t)
    have := hle.trans hz
    rwa [ENNReal.ofReal_le_ofReal_iff hr] at this
  · intro hz
    refine Metric.mem_cthickening_of_dist_le z (o + ⟪z - o, d⟫ • d) r _ ⟨_, rfl⟩ ?_
    rw [dist_eq_norm, norm_sub_foot_eq o d z hd]
    exact hz

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E] in
/-- The orthogonal component is linear in the point (the line's own direction is invisible). -/
theorem perp_sub_perp (o d z w : E) :
    ((z - o) - ⟪z - o, d⟫ • d) - ((w - o) - ⟪w - o, d⟫ • d) =
      (z - w) - ⟪z - w, d⟫ • d := by
  have h : ⟪z - o, d⟫ - ⟪w - o, d⟫ = ⟪z - w, d⟫ := by
    rw [← inner_sub_left]; congr 1; abel
  rw [← h]; module

/-! ### Tubes inside a line neighbourhood: core, direction, and — for centred tubes — midpoint -/

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **The core of a tube in `N_r(L)` lies in `N_{r-δ}(L)`.** Pushing a core point away from the
line by `δ` stays in the carrier, and `lineDist` grows by exactly `δ` along that push. -/
theorem lineDist_le_of_carrier_subset {δ : NNReal} (T : Tube δ E) {o d : E} (hd : ‖d‖ = 1)
    {r : ℝ} (hr : (δ : ℝ) ≤ r)
    (hT : T.carrier ⊆ Metric.cthickening r (Set.range fun t : ℝ ↦ o + t • d))
    {z : E} (hz : z ∈ segment ℝ T.x T.y) : lineDist o d z ≤ r - δ := by
  set v : E := (z - o) - ⟪z - o, d⟫ • d with hv
  have hL : lineDist o d z = ‖v‖ := rfl
  have hvd : ⟪v, d⟫ = 0 := inner_perp_eq_zero o d z hd
  rcases eq_or_lt_of_le (norm_nonneg v) with h0 | hpos
  · rw [hL, ← h0]; linarith
  · set w : E := z + ((δ : ℝ) / ‖v‖) • v with hw
    have hwz : dist w z ≤ δ := by
      rw [hw, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg δ.coe_nonneg (norm_nonneg _)), div_mul_cancel₀ _ hpos.ne']
    have hwmem : w ∈ T.carrier := T.mem_carrier_of_dist_le hz hwz
    have hwline := (mem_cthickening_line_iff hd (le_trans δ.coe_nonneg hr)).mp (hT hwmem)
    -- `lineDist w = ‖v‖ + δ`
    have hwperp : (w - o) - ⟪w - o, d⟫ • d = (1 + (δ : ℝ) / ‖v‖) • v := by
      have h1 : w - o = (z - o) + ((δ : ℝ) / ‖v‖) • v := by rw [hw]; abel
      rw [h1, inner_add_left, real_inner_smul_left, hvd, mul_zero, add_zero]
      rw [hv]; module
    have hwL : lineDist o d w = ‖v‖ + δ := by
      unfold lineDist
      rw [hwperp, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 + (δ : ℝ) / ‖v‖), add_mul, one_mul,
        div_mul_cancel₀ _ hpos.ne']
    rw [hL]; linarith [hwL ▸ hwline]

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E] in
/-- A unit vector whose orthogonal component along `d` is at most `2R` is within `4R` of `d` or
of `-d` (the two orientations of the line; refined l.4794–4795, "one of two balls"). -/
theorem exists_sign_norm_sub_le_of_perp_le {u d : E} (hu : ‖u‖ = 1) (hd : ‖d‖ = 1) {R : ℝ}
    (hperp : ‖u - ⟪u, d⟫ • d‖ ≤ 2 * R) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ‖u - s • d‖ ≤ 4 * R := by
  set c : ℝ := ⟪u, d⟫ with hc
  have hc1 : |c| ≤ 1 := by
    have := abs_real_inner_le_norm u d; rwa [hu, hd, one_mul] at this
  have hR0 : 0 ≤ R := by
    have := norm_nonneg (u - c • d); linarith
  have hlow : 1 - 2 * R ≤ |c| := by
    have h1 : ‖u‖ ≤ ‖u - c • d‖ + ‖c • d‖ := by
      have := norm_add_le (u - c • d) (c • d); rwa [sub_add_cancel] at this
    rw [hu, norm_smul, hd, mul_one, Real.norm_eq_abs] at h1
    linarith
  rcases le_or_gt 0 c with hc0 | hc0
  · refine ⟨1, Or.inl rfl, ?_⟩
    have h1 : ‖u - (1 : ℝ) • d‖ ≤ ‖u - c • d‖ + ‖c • d - (1 : ℝ) • d‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    have h2 : ‖c • d - (1 : ℝ) • d‖ = 1 - c := by
      rw [← sub_smul, norm_smul, hd, mul_one, Real.norm_eq_abs,
        abs_of_nonpos (by linarith [abs_le.mp hc1])]
      ring
    rw [abs_of_nonneg hc0] at hlow
    linarith
  · refine ⟨-1, Or.inr rfl, ?_⟩
    have h1 : ‖u - (-1 : ℝ) • d‖ ≤ ‖u - c • d‖ + ‖c • d - (-1 : ℝ) • d‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    have h2 : ‖c • d - (-1 : ℝ) • d‖ = 1 + c := by
      rw [← sub_smul, norm_smul, hd, mul_one, Real.norm_eq_abs,
        abs_of_nonneg (by linarith [abs_le.mp hc1])]
      ring
    rw [abs_of_neg hc0] at hlow
    linarith

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **Direction from core closeness.** If both endpoints of the core lie within `R` of the line
`L`, the direction is within `4R` of one of the two unit directions of `L`. -/
theorem exists_sign_norm_direction_sub_le {δ : NNReal} (T : Tube δ E) {o d : E} (hd : ‖d‖ = 1)
    {R : ℝ} (hx : lineDist o d T.x ≤ R) (hy : lineDist o d T.y ≤ R) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ‖T.direction - s • d‖ ≤ 4 * R := by
  apply exists_sign_norm_sub_le_of_perp_le T.norm_direction hd
  have h := perp_sub_perp o d T.y T.x
  have hdir : T.y - T.x = T.direction := rfl
  rw [hdir] at h
  calc ‖T.direction - ⟪T.direction, d⟫ • d‖
      = ‖((T.y - o) - ⟪T.y - o, d⟫ • d) - ((T.x - o) - ⟪T.x - o, d⟫ • d)‖ := by rw [h]
    _ ≤ ‖(T.y - o) - ⟪T.y - o, d⟫ • d‖ + ‖(T.x - o) - ⟪T.x - o, d⟫ • d‖ := norm_sub_le _ _
    _ ≤ R + R := add_le_add hy hx
    _ = 2 * R := by ring

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E] in
/-- The foot of the perpendicular from the origin to the line `t ↦ o + t • d`. -/
noncomputable def lineFoot (o d : E) : E := o - ⟪o, d⟫ • d

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E] in
/-- `m - foot = (orthogonal component of `m - o`) + ⟪m, d⟫ d`. -/
theorem sub_lineFoot_eq (o d m : E) :
    m - lineFoot o d = ((m - o) - ⟪m - o, d⟫ • d) + ⟪m, d⟫ • d := by
  unfold lineFoot
  have : ⟪m - o, d⟫ = ⟪m, d⟫ - ⟪o, d⟫ := inner_sub_left m o d
  rw [this]; module

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **The centring step** (refined l.4852–4855): for a centred tube whose midpoint lies within
`R` of the line and whose direction is within `b` of `±d`, the midpoint is within
`R + ‖midpoint‖ · b` of the foot of the line.  The axial coordinate `⟪m, d⟫` is controlled by
`⟪m, direction⟫ = 0`; without centring it is free. -/
theorem norm_midpoint_sub_lineFoot_le_of_isCentred {δ : NNReal} (T : Tube δ E)
    (hcen : T.IsCentred) {o d : E} (hd : ‖d‖ = 1) {R : ℝ} (hm : lineDist o d T.midpoint ≤ R)
    {s b : ℝ} (hs : s = 1 ∨ s = -1) (hdir : ‖T.direction - s • d‖ ≤ b) :
    ‖T.midpoint - lineFoot o d‖ ≤ R + ‖T.midpoint‖ * b := by
  rw [sub_lineFoot_eq o d T.midpoint]
  refine (norm_add_le _ _).trans (add_le_add hm ?_)
  rw [norm_smul, hd, mul_one, Real.norm_eq_abs]
  have hss : s * s = 1 := by rcases hs with rfl | rfl <;> norm_num
  have hkey : ⟪T.midpoint, d⟫ = ⟪T.midpoint, d - s • T.direction⟫ := by
    rw [inner_sub_right, real_inner_smul_right, hcen, mul_zero, sub_zero]
  have hnorm : ‖d - s • T.direction‖ = ‖T.direction - s • d‖ := by
    have : d - s • T.direction = -(s • (T.direction - s • d)) := by
      rw [smul_sub s T.direction (s • d), smul_smul, hss, one_smul, neg_sub]
    rw [this, norm_neg, norm_smul, Real.norm_eq_abs]
    rcases hs with rfl | rfl <;> simp
  calc |⟪T.midpoint, d⟫| = |⟪T.midpoint, d - s • T.direction⟫| := by rw [hkey]
    _ ≤ ‖T.midpoint‖ * ‖d - s • T.direction‖ := abs_real_inner_le_norm _ _
    _ = ‖T.midpoint‖ * ‖T.direction - s • d‖ := by rw [hnorm]
    _ ≤ ‖T.midpoint‖ * b := by gcongr

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **A centred tube inside `N_{Kρ}(L)` has line parameters near `L`'s** — the two boxes of the
packing argument (refined l.4794–4797): direction within `4(K-1)ρ` of `±d`, midpoint within
`(K-1)ρ · (1 + 4 R₀)` of the foot, for `‖midpoint‖ ≤ R₀`. -/
theorem params_close_of_carrier_subset_line {ρ : NNReal} (W : Tube ρ E) (hcen : W.IsCentred)
    {R₀ : ℝ} (hmid : ‖W.midpoint‖ ≤ R₀) {o d : E} (hd : ‖d‖ = 1) {K : ℝ} (hK : 1 ≤ K)
    (hW : W.carrier ⊆ Metric.cthickening (K * ρ) (Set.range fun t : ℝ ↦ o + t • d)) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ‖W.direction - s • d‖ ≤ 4 * ((K - 1) * ρ) ∧
      ‖W.midpoint - lineFoot o d‖ ≤ (K - 1) * ρ * (1 + 4 * R₀) := by
  have hρ0 : (0 : ℝ) ≤ ρ := ρ.coe_nonneg
  have hr : (ρ : ℝ) ≤ K * ρ := by nlinarith
  have hcore : ∀ z ∈ segment ℝ W.x W.y, lineDist o d z ≤ (K - 1) * ρ := by
    intro z hz
    have := lineDist_le_of_carrier_subset W hd hr hW hz
    linarith
  obtain ⟨s, hs, hdir⟩ := exists_sign_norm_direction_sub_le W hd
    (hcore _ (left_mem_segment ℝ _ _)) (hcore _ (right_mem_segment ℝ _ _))
  refine ⟨s, hs, hdir, ?_⟩
  have hmidcore : lineDist o d W.midpoint ≤ (K - 1) * ρ :=
    hcore _ (by simpa using W.midpoint_add_smul_mem_segment (t := 0) (by norm_num))
  have h := norm_midpoint_sub_lineFoot_le_of_isCentred W hcen hd hmidcore hs hdir
  have hR0 : 0 ≤ (K - 1) * ρ := by nlinarith
  calc ‖W.midpoint - lineFoot o d‖ ≤ (K - 1) * ρ + ‖W.midpoint‖ * (4 * ((K - 1) * ρ)) := h
    _ ≤ (K - 1) * ρ + R₀ * (4 * ((K - 1) * ρ)) := by gcongr
    _ = (K - 1) * ρ * (1 + 4 * R₀) := by ring

/-! ### Packing separated centred tubes inside a line neighbourhood -/

/-- The packing constant: the members of an `ε`-separated (L¹ on `(midpoint, direction)`) family
of centred `ρ`-tubes with `‖midpoint‖ ≤ R₀` lying inside `N_{Kρ}(L)` number at most
`2 · ((Rx + ε/4)/(ε/4))ⁿ · ((Ry + ε/4)/(ε/4))ⁿ`, `Rx = (K-1)ρ(1 + 4R₀)`, `Ry = 4(K-1)ρ`;
stated with the spacing as a fraction `ε = ρ / m` so the constant is `ρ`-free. -/
noncomputable def linePackingConstant (n : ℕ) (R₀ K m : ℝ) : ℝ :=
  2 * ((K - 1) * (1 + 4 * R₀) * (4 * m) + 1) ^ n * (4 * (K - 1) * (4 * m) + 1) ^ n

open Classical in
/-- **Line-based packing of a separated centred family** (refined l.4794–4800, in the tree's
volume-comparison form `Tube.card_le_of_L1_separated_in_rectangle`). -/
theorem card_filter_line_le_of_centred_sep {α : Type*} (G : Finset α) {ρ : NNReal} (hρ : 0 < ρ)
    (W : α → Tube ρ E) (hcen : ∀ a ∈ G, (W a).IsCentred) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (hmid : ∀ a ∈ G, ‖(W a).midpoint‖ ≤ R₀) {m : ℝ} (hm : 0 < m)
    (hsep : ∀ a ∈ G, ∀ b ∈ G, a ≠ b →
      (ρ : ℝ) / m ≤ ‖(W a).midpoint - (W b).midpoint‖ + ‖(W a).direction - (W b).direction‖)
    {K : ℝ} (hK : 1 ≤ K) (o d : E) (hd : ‖d‖ = 1) :
    ((G.filter fun a ↦ (W a).carrier ⊆
        Metric.cthickening (K * ρ) (Set.range fun t : ℝ ↦ o + t • d)).card : ℝ)
      ≤ linePackingConstant (Module.finrank ℝ E) R₀ K m := by
  classical
  have hρr : (0 : ℝ) < ρ := by exact_mod_cast hρ
  set r : ℝ := (ρ : ℝ) / m with hr_def
  have hr : 0 < r := div_pos hρr hm
  set Rx : ℝ := (K - 1) * ρ * (1 + 4 * R₀) with hRx
  set Ry : ℝ := 4 * ((K - 1) * ρ) with hRy
  have hRx0 : 0 ≤ Rx := by rw [hRx]; have := ρ.coe_nonneg; positivity
  have hRy0 : 0 ≤ Ry := by rw [hRy]; have := ρ.coe_nonneg; positivity
  set F := G.filter fun a ↦ (W a).carrier ⊆
    Metric.cthickening (K * ρ) (Set.range fun t : ℝ ↦ o + t • d) with hF
  set Fp := F.filter fun a ↦ ‖(W a).direction - (1 : ℝ) • d‖ ≤ Ry with hFp
  set Fm := F.filter fun a ↦ ‖(W a).direction - (-1 : ℝ) • d‖ ≤ Ry with hFm
  have hsub : F ⊆ Fp ∪ Fm := by
    intro a ha
    have haG : a ∈ G := (Finset.mem_filter.mp ha).1
    have haW := (Finset.mem_filter.mp ha).2
    obtain ⟨s, hs, hdir, -⟩ :=
      params_close_of_carrier_subset_line (W a) (hcen a haG) (hmid a haG) hd hK haW
    rcases hs with rfl | rfl
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨ha, hdir⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨ha, hdir⟩))
  have hbound : ∀ (σ : ℝ), (σ = 1 ∨ σ = -1) →
      ∀ H : Finset α, H ⊆ F → (∀ a ∈ H, ‖(W a).direction - σ • d‖ ≤ Ry) →
      (H.card : ℝ) ≤ ((Rx + r / 4) / (r / 4)) ^ Module.finrank ℝ E *
        ((Ry + r / 4) / (r / 4)) ^ Module.finrank ℝ E := by
    intro σ hσ H hHF hHdir
    refine card_le_of_L1_separated_in_rectangle H (fun a ↦ (W a).midpoint)
      (fun a ↦ (W a).direction) (lineFoot o d) (σ • d) hr hRx0 hRy0 ?_ ?_ hHdir
    · intro a ha b hb hab
      exact hsep a (Finset.mem_filter.mp (hHF ha)).1 b (Finset.mem_filter.mp (hHF hb)).1 hab
    · intro a ha
      have haF := hHF ha
      have haG : a ∈ G := (Finset.mem_filter.mp haF).1
      obtain ⟨s, hs, -, hmidc⟩ :=
        params_close_of_carrier_subset_line (W a) (hcen a haG) (hmid a haG) hd hK
          (Finset.mem_filter.mp haF).2
      rw [hRx]; exact hmidc
  have hp₁ := hbound 1 (Or.inl rfl) Fp (Finset.filter_subset _ _)
    (fun a ha ↦ (Finset.mem_filter.mp ha).2)
  have hm₁ := hbound (-1) (Or.inr rfl) Fm (Finset.filter_subset _ _)
    (fun a ha ↦ (Finset.mem_filter.mp ha).2)
  have hcard : (F.card : ℝ) ≤ (Fp.card : ℝ) + (Fm.card : ℝ) := by
    have h1 : F.card ≤ (Fp ∪ Fm).card := Finset.card_le_card hsub
    have h2 : (Fp ∪ Fm).card ≤ Fp.card + Fm.card := Finset.card_union_le _ _
    exact_mod_cast h1.trans h2
  -- the box ratios in `ρ`-free form
  have hratio_x : (Rx + r / 4) / (r / 4) = (K - 1) * (1 + 4 * R₀) * (4 * m) + 1 := by
    rw [hRx, hr_def]; field_simp
  have hratio_y : (Ry + r / 4) / (r / 4) = 4 * (K - 1) * (4 * m) + 1 := by
    rw [hRy, hr_def]; field_simp
  unfold linePackingConstant
  rw [← hratio_x, ← hratio_y]
  linarith

/-! ### The centred net -/

omit [MeasurableSpace E] [BorelSpace E] in
/-- **A maximal separated net of centred line parameters** (refined l.4786–4789: "Write an
oriented line as `(p, d)` with `p ⊥ d`, `|d| = 1`, and `|p| ≤ 0.42`. Take a maximal
`r`-separated subset of this compact subset of `ℝ⁶`.").  The net points are realised as centred
`ρ`-tubes; separation is in the `L¹` metric on `(midpoint, direction)`, covering is coordinatewise
within `2ε`. -/
theorem exists_centred_net (ρ : NNReal) (R₀ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ G : Finset (Tube ρ E),
      (∀ W ∈ G, W.IsCentred) ∧
      (∀ W ∈ G, ‖W.midpoint‖ ≤ R₀) ∧
      (∀ a ∈ G, ∀ b ∈ G, a ≠ b → ε ≤ ‖a.midpoint - b.midpoint‖ + ‖a.direction - b.direction‖) ∧
      (∀ p d : E, ⟪p, d⟫ = 0 → ‖d‖ = 1 → ‖p‖ ≤ R₀ →
        ∃ W ∈ G, ‖p - W.midpoint‖ ≤ 2 * ε ∧ ‖d - W.direction‖ ≤ 2 * ε) := by
  classical
  -- the compact parameter set
  set K : Set (E × E) :=
    ({q | ⟪q.1, q.2⟫ = 0} ∩ {q | ‖q.2‖ = 1}) ∩ {q | ‖q.1‖ ≤ R₀} with hK
  have hKclosed : IsClosed K := by
    have h1 : IsClosed {q : E × E | ⟪q.1, q.2⟫ = 0} :=
      isClosed_eq (Continuous.inner continuous_fst continuous_snd) continuous_const
    have h2 : IsClosed {q : E × E | ‖q.2‖ = 1} :=
      isClosed_eq (continuous_snd.norm) continuous_const
    have h3 : IsClosed {q : E × E | ‖q.1‖ ≤ R₀} :=
      isClosed_le (continuous_fst.norm) continuous_const
    exact (h1.inter h2).inter h3
  have hKbdd : Bornology.IsBounded K := by
    rw [Metric.isBounded_iff_subset_closedBall (0 : E × E)]
    refine ⟨max R₀ 1, fun q hq ↦ ?_⟩
    obtain ⟨⟨-, hq2⟩, hq1⟩ := hq
    rw [Metric.mem_closedBall, Prod.dist_eq, Prod.fst_zero, Prod.snd_zero, dist_zero_right,
      dist_zero_right]
    simp only [Set.mem_setOf_eq] at hq1 hq2
    rw [hq2]
    exact max_le_max hq1 le_rfl
  have hKcpt : IsCompact K := Metric.isCompact_of_isClosed_isBounded hKclosed hKbdd
  obtain ⟨t, ht_sub, ht_fin, ht_cover⟩ :=
    Metric.finite_approx_of_totallyBounded hKcpt.totallyBounded ε hε
  set tF : Finset (E × E) := ht_fin.toFinset with htF
  have htF_mem : ∀ q, q ∈ tF ↔ q ∈ t := fun q ↦ Set.Finite.mem_toFinset ht_fin
  obtain ⟨P, hP_sub, hP_sep, hP_cover⟩ :=
    exists_maximal_separated_finset tF (fun a b : E × E ↦ ‖a.1 - b.1‖ + ‖a.2 - b.2‖)
      (fun a ↦ by simp only [sub_self, norm_zero, add_zero]; exact hε)
      (fun a b ↦ by rw [norm_sub_rev a.1, norm_sub_rev a.2])
  have hP_K : ∀ q ∈ P, q ∈ K := fun q hq ↦ ht_sub ((htF_mem q).mp (hP_sub hq))
  -- the fallback direction and the node map
  obtain ⟨x₀, hx₀⟩ := exists_ne (0 : E)
  set u₀ : E := ‖x₀‖⁻¹ • x₀ with hu₀_def
  have hu₀ : ‖u₀‖ = 1 := by
    rw [hu₀_def, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx₀)]
  set tubeAt : E × E → Tube ρ E := fun q ↦
    if h : ‖q.2‖ = 1 then ofMidpointDirection ρ q.1 q.2 h
    else ofMidpointDirection ρ q.1 u₀ hu₀ with htubeAt
  have htube_mid : ∀ q ∈ P, (tubeAt q).midpoint = q.1 := by
    intro q hq
    have h : ‖q.2‖ = 1 := (hP_K q hq).1.2
    simp only [htubeAt, dif_pos h]
    exact midpoint_ofMidpointDirection' _ _ _
  have htube_dir : ∀ q ∈ P, (tubeAt q).direction = q.2 := by
    intro q hq
    have h : ‖q.2‖ = 1 := (hP_K q hq).1.2
    simp only [htubeAt, dif_pos h]
    exact direction_ofMidpointDirection' _ _ _
  refine ⟨P.image tubeAt, ?_, ?_, ?_, ?_⟩
  · intro W hW
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hW
    unfold IsCentred
    rw [htube_mid q hq, htube_dir q hq]
    exact (hP_K q hq).1.1
  · intro W hW
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hW
    rw [htube_mid q hq]
    exact (hP_K q hq).2
  · intro a ha b hb hab
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hb
    have hqq' : q ≠ q' := fun h ↦ hab (by rw [h])
    have := hP_sep q hq q' hq' hqq'
    rwa [htube_mid q hq, htube_dir q hq, htube_mid q' hq', htube_dir q' hq']
  · intro p d hpd hd hp
    have hmemK : (p, d) ∈ K := ⟨⟨hpd, hd⟩, hp⟩
    obtain ⟨y, hy_t, hy_ball⟩ := Set.mem_iUnion₂.mp (ht_cover hmemK)
    have hyF : y ∈ tF := (htF_mem y).mpr hy_t
    obtain ⟨w, hw_P, hw_close⟩ := hP_cover y hyF
    have hdist : dist (p, d) y < ε := Metric.mem_ball.mp hy_ball
    rw [Prod.dist_eq, max_lt_iff, dist_eq_norm, dist_eq_norm] at hdist
    refine ⟨tubeAt w, Finset.mem_image_of_mem _ hw_P, ?_, ?_⟩
    · rw [htube_mid w hw_P]
      calc ‖p - w.1‖ ≤ ‖p - y.1‖ + ‖y.1 - w.1‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ ε + ε := by
          have := norm_nonneg (y.2 - w.2)
          linarith [hdist.1, hw_close]
        _ = 2 * ε := by ring
    · rw [htube_dir w hw_P]
      calc ‖d - w.2‖ ≤ ‖d - y.2‖ + ‖y.2 - w.2‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ ε + ε := by
          have := norm_nonneg (y.1 - w.1)
          linarith [hdist.2, hw_close]
        _ = 2 * ε := by ring

/-! ### Exact containment from parameter closeness -/

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **Exact containment** (refined l.4789–4791): a `σ`-tube whose midpoint and direction are
within `a`, `b` of a `ρ`-tube's is inside it once `a + b/2 + σ ≤ ρ`.  This is the existing
`Tube.tube_le_rescale_of_close` read at the node's own radius. -/
theorem le_of_params_close {σ ρ : NNReal} (U : Tube σ E) (W : Tube ρ E) {a b : ℝ}
    (hmid : ‖U.midpoint - W.midpoint‖ ≤ a) (hdir : ‖U.direction - W.direction‖ ≤ b)
    (hcond : a + b / 2 + (σ : ℝ) ≤ (ρ : ℝ)) :
    U.toConvexSpaceBody ≤ W.toConvexSpaceBody := by
  have h := tube_le_rescale_of_close U W hmid hdir hcond (r := ρ)
  rwa [toConvexSpaceBody_rescale_self] at h

/-! ### The one-scale canonical centred cover (`lemcanonicalcover`) -/

/-- The line-ED constant of the canonical centred cover at spacing `ρ/8` and thickness `5ρ`:
`linePackingConstant n R₀ 5 8 = 2 · (128(1 + 4R₀) + 1)ⁿ · 513ⁿ`.  At `R₀ = 1`, `n = 3` this is
`2 · 641³ · 513³` (compare the refined `2 · 223⁶`, l.4784, and the `641` of l.4900). -/
noncomputable def canonicalCoverEDConstant (n : ℕ) (R₀ : ℝ) : ℝ := linePackingConstant n R₀ 5 8

theorem canonicalCoverEDConstant_eq (n : ℕ) (R₀ : ℝ) :
    canonicalCoverEDConstant n R₀ = 2 * (128 * (1 + 4 * R₀) + 1) ^ n * 513 ^ n := by
  unfold canonicalCoverEDConstant linePackingConstant
  norm_num
  ring

open Classical in
/-- **The canonical centred cover at one scale** (`lemcanonicalcover`, refined l.4774–4800, for
centred members): every centred `δ`-tube with `‖midpoint‖ ≤ R₀` is assigned a centred `ρ`-node
containing it exactly (`4δ ≤ ρ`); the node family is the image of the assignment (every node is
used), its members are pairwise separated by `ρ/8` in the `L¹` parameter metric, and it is
line-essentially distinct at thickness `5ρ` with the absolute constant
`canonicalCoverEDConstant (finrank E) R₀`. -/
theorem exists_canonicalCentredCover {δ ρ : NNReal} (hρ : 0 < ρ) (h4 : 4 * (δ : ℝ) ≤ ρ)
    {R₀ : ℝ} (hR₀ : 0 ≤ R₀) {ι : Type*} (s : Finset ι) (T : ι → Tube δ E)
    (hcen : ∀ i ∈ s, (T i).IsCentred) (hmid : ∀ i ∈ s, ‖(T i).midpoint‖ ≤ R₀) :
    ∃ (G : Finset (Tube ρ E)) (ϖ : ι → Tube ρ E),
      (∀ i ∈ s, ϖ i ∈ G) ∧
      (∀ W ∈ G, ∃ i ∈ s, ϖ i = W) ∧
      (∀ i ∈ s, (T i).toConvexSpaceBody ≤ (ϖ i).toConvexSpaceBody) ∧
      (∀ i ∈ s, ‖(T i).midpoint - (ϖ i).midpoint‖ ≤ (ρ : ℝ) / 4 ∧
        ‖(T i).direction - (ϖ i).direction‖ ≤ (ρ : ℝ) / 4) ∧
      (∀ W ∈ G, W.IsCentred) ∧
      (∀ W ∈ G, ‖W.midpoint‖ ≤ R₀) ∧
      (∀ a ∈ G, ∀ b ∈ G, a ≠ b →
        (ρ : ℝ) / 8 ≤ ‖a.midpoint - b.midpoint‖ + ‖a.direction - b.direction‖) ∧
      (∀ o d : E, ‖d‖ = 1 →
        ((G.filter fun W : Tube ρ E ↦ W.carrier ⊆
            Metric.cthickening (5 * ρ) (Set.range fun t : ℝ ↦ o + t • d)).card : ℝ)
          ≤ canonicalCoverEDConstant (Module.finrank ℝ E) R₀) := by
  classical
  have hρr : (0 : ℝ) < ρ := by exact_mod_cast hρ
  obtain ⟨G₀, hG₀cen, hG₀mid, hG₀sep, hG₀cover⟩ :=
    exists_centred_net (E := E) ρ R₀ (ε := (ρ : ℝ) / 8) (by positivity)
  -- the assignment: a nearest net node, chosen by the covering clause
  have hchoice : ∀ i, ∃ W : Tube ρ E, i ∈ s →
      W ∈ G₀ ∧ ‖(T i).midpoint - W.midpoint‖ ≤ 2 * ((ρ : ℝ) / 8) ∧
        ‖(T i).direction - W.direction‖ ≤ 2 * ((ρ : ℝ) / 8) := by
    intro i
    by_cases hi : i ∈ s
    · obtain ⟨W, hW, h1, h2⟩ := hG₀cover (T i).midpoint (T i).direction (hcen i hi)
        (T i).norm_direction (hmid i hi)
      exact ⟨W, fun _ ↦ ⟨hW, h1, h2⟩⟩
    · exact ⟨ofMidpointDirection ρ 0 (T i).direction (T i).norm_direction, fun h ↦ (hi h).elim⟩
  choose ϖ hϖ using hchoice
  set G : Finset (Tube ρ E) := s.image ϖ with hG
  have hGsub : G ⊆ G₀ := by
    intro W hW
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hW
    exact (hϖ i hi).1
  have hq : 2 * ((ρ : ℝ) / 8) = (ρ : ℝ) / 4 := by ring
  refine ⟨G, ϖ, fun i hi ↦ Finset.mem_image_of_mem _ hi, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro W hW
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hW
    exact ⟨i, hi, rfl⟩
  · intro i hi
    obtain ⟨-, h1, h2⟩ := hϖ i hi
    refine le_of_params_close (T i) (ϖ i) h1 h2 ?_
    rw [hq]; linarith
  · intro i hi
    obtain ⟨-, h1, h2⟩ := hϖ i hi
    rw [hq] at h1 h2
    exact ⟨h1, h2⟩
  · intro W hW; exact hG₀cen W (hGsub hW)
  · intro W hW; exact hG₀mid W (hGsub hW)
  · intro a ha b hb hab; exact hG₀sep a (hGsub ha) b (hGsub hb) hab
  · intro o d hd
    have h := card_filter_line_le_of_centred_sep G hρ (fun W : Tube ρ E ↦ W)
      (fun W hW ↦ hG₀cen W (hGsub hW)) hR₀ (fun W hW ↦ hG₀mid W (hGsub hW))
      (m := 8) (by norm_num)
      (fun a ha b hb hab ↦ hG₀sep a (hGsub ha) b (hGsub hb) hab) (K := 5) (by norm_num) o d hd
    exact h

/-! ## Restricting a hierarchy to its active nodes -/

section ActiveRestrict

variable {ι : Type*}

open Classical in
/-- The **active** nodes of a cover system at level `k`: those with a nonempty class. -/
noncomputable def GridCoverSystem.activeIndexSet {δ : NNReal} {t : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} (G : GridCoverSystem t T N) (k : ℕ) : Finset ι :=
  (G.indexSet k).filter fun j ↦ ∃ i ∈ t, G.assign k i = j

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
open Classical in
theorem GridCoverSystem.activeIndexSet_subset {δ : NNReal} {t : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} (G : GridCoverSystem t T N) (k : ℕ) : G.activeIndexSet k ⊆ G.indexSet k :=
  Finset.filter_subset _ _

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
open Classical in
theorem GridCoverSystem.mem_activeIndexSet {δ : NNReal} {t : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} (G : GridCoverSystem t T N) {k : ℕ} {j : ι} :
    j ∈ G.activeIndexSet k ↔ j ∈ G.indexSet k ∧ ∃ i ∈ t, G.assign k i = j := by
  unfold GridCoverSystem.activeIndexSet
  exact Finset.mem_filter

/-- The cover system with every index set cut to its active nodes.  Assignments, node tubes,
containment and nestedness are unchanged. -/
noncomputable def GridCoverSystem.activeRestrict {δ : NNReal} {t : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} (G : GridCoverSystem t T N) : GridCoverSystem t T N where
  indexSet := G.activeIndexSet
  assign := G.assign
  tube := G.tube
  assign_mem k hk i hi := G.mem_activeIndexSet.mpr ⟨G.assign_mem k hk i hi, i, hi, rfl⟩
  le_tube_assign := G.le_tube_assign
  nested := G.nested
  tube_nested := G.tube_nested

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
@[simp] theorem GridCoverSystem.activeRestrict_indexSet {δ : NNReal} {t : Finset ι}
    {T : ι → Tube δ E} {N : ℕ} (G : GridCoverSystem t T N) :
    G.activeRestrict.indexSet = G.activeIndexSet := rfl

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
@[simp] theorem GridCoverSystem.activeRestrict_assign {δ : NNReal} {t : Finset ι}
    {T : ι → Tube δ E} {N : ℕ} (G : GridCoverSystem t T N) :
    G.activeRestrict.assign = G.assign := rfl

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
@[simp] theorem GridCoverSystem.activeRestrict_tube {δ : NNReal} {t : Finset ι}
    {T : ι → Tube δ E} {N : ℕ} (G : GridCoverSystem t T N) :
    G.activeRestrict.tube = G.tube := rfl

/-- **A uniform set of tubes restricted to its active nodes.**  Every field survives: the
assignment lands in active nodes, node injectivity and the overlap bound pass to a subset, and the
class brackets are quantified over fewer nodes.  The Section-9 consumers (`pbActiveTubeNodes`)
read the active nodes anyway. -/
noncomputable def UniformTubeSet.activeRestrict {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} {C : NNReal} (𝒰 : UniformTubeSet s T N C) : UniformTubeSet s T N C where
  cover := 𝒰.cover.activeRestrict
  branchingN := 𝒰.branchingN
  tube_injOn k hk :=
    (𝒰.tube_injOn k hk).mono (Finset.coe_subset.mpr (𝒰.cover.activeIndexSet_subset k))
  boundedOverlap k hk V := by
    classical
    refine le_trans ?_ (𝒰.boundedOverlap k hk V)
    exact_mod_cast Finset.card_le_card
      (Finset.filter_subset_filter _ (𝒰.cover.activeIndexSet_subset k))
  card_class_le k hk j hj := 𝒰.card_class_le k hk j (𝒰.cover.activeIndexSet_subset k hj)
  le_card_class k hk j hj := 𝒰.le_card_class k hk j (𝒰.cover.activeIndexSet_subset k hj)

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
@[simp] theorem UniformTubeSet.activeRestrict_cover {δ : NNReal} {s : Finset ι}
    {T : ι → Tube δ E} {N : ℕ} {C : NNReal} (𝒰 : UniformTubeSet s T N C) :
    𝒰.activeRestrict.cover = 𝒰.cover.activeRestrict := rfl

end ActiveRestrict

/-! ## Packing in the two parameter boxes -/

omit [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E] in
/-- The two orientations: `‖u - d‖ ≤ R` or `‖u + d‖ ≤ R`, written with `±1` scalars. -/
theorem norm_sub_neg_one_smul (u d : E) : ‖u - (-1 : ℝ) • d‖ = ‖u + d‖ := by
  rw [neg_one_smul, sub_neg_eq_add]

open Classical in
/-- **Box packing of a separated family of tubes**: the members whose midpoint lies within `Rx`
of `c` and whose direction lies within `Ry` of `d` or of `-d` number at most
`2 · ((Rx + ε/4)/(ε/4))ⁿ · ((Ry + ε/4)/(ε/4))ⁿ` for an `ε`-separated (L¹) family.  No centring is
needed here; centring is what puts a family inside these boxes
(`params_close_of_carrier_subset_line`). -/
theorem card_filter_boxes_le_of_sep {α : Type*} (G : Finset α) {ρ : NNReal} (W : α → Tube ρ E)
    {ε : ℝ} (hε : 0 < ε)
    (hsep : ∀ a ∈ G, ∀ b ∈ G, a ≠ b →
      ε ≤ ‖(W a).midpoint - (W b).midpoint‖ + ‖(W a).direction - (W b).direction‖)
    (c d : E) {Rx Ry : ℝ} (hRx : 0 ≤ Rx) (hRy : 0 ≤ Ry) :
    ((G.filter fun a ↦ ‖(W a).midpoint - c‖ ≤ Rx ∧
        (‖(W a).direction - (1 : ℝ) • d‖ ≤ Ry ∨
          ‖(W a).direction - (-1 : ℝ) • d‖ ≤ Ry)).card : ℝ)
      ≤ 2 * ((Rx + ε / 4) / (ε / 4)) ^ Module.finrank ℝ E *
          ((Ry + ε / 4) / (ε / 4)) ^ Module.finrank ℝ E := by
  classical
  set F := G.filter fun a ↦ ‖(W a).midpoint - c‖ ≤ Rx ∧
    (‖(W a).direction - (1 : ℝ) • d‖ ≤ Ry ∨ ‖(W a).direction - (-1 : ℝ) • d‖ ≤ Ry) with hF
  set Fp := F.filter fun a ↦ ‖(W a).direction - (1 : ℝ) • d‖ ≤ Ry with hFp
  set Fm := F.filter fun a ↦ ‖(W a).direction - (-1 : ℝ) • d‖ ≤ Ry with hFm
  have hsub : F ⊆ Fp ∪ Fm := by
    intro a ha
    rcases (Finset.mem_filter.mp ha).2.2 with h | h
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨ha, h⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨ha, h⟩))
  have hbound : ∀ (σ : ℝ), ∀ H : Finset α, H ⊆ F → (∀ a ∈ H, ‖(W a).direction - σ • d‖ ≤ Ry) →
      (H.card : ℝ) ≤ ((Rx + ε / 4) / (ε / 4)) ^ Module.finrank ℝ E *
        ((Ry + ε / 4) / (ε / 4)) ^ Module.finrank ℝ E := by
    intro σ H hHF hHdir
    refine card_le_of_L1_separated_in_rectangle H (fun a ↦ (W a).midpoint)
      (fun a ↦ (W a).direction) c (σ • d) hε hRx hRy ?_ ?_ hHdir
    · intro a ha b hb hab
      exact hsep a (Finset.mem_filter.mp (hHF ha)).1 b (Finset.mem_filter.mp (hHF hb)).1 hab
    · intro a ha
      exact (Finset.mem_filter.mp (hHF ha)).2.1
  have hp := hbound 1 Fp (Finset.filter_subset _ _) (fun a ha ↦ (Finset.mem_filter.mp ha).2)
  have hm := hbound (-1) Fm (Finset.filter_subset _ _) (fun a ha ↦ (Finset.mem_filter.mp ha).2)
  have hcard : (F.card : ℝ) ≤ (Fp.card : ℝ) + (Fm.card : ℝ) := by
    have h1 : F.card ≤ (Fp ∪ Fm).card := Finset.card_le_card hsub
    have h2 : (Fp ∪ Fm).card ≤ Fp.card + Fm.card := Finset.card_union_le _ _
    exact_mod_cast h1.trans h2
  linarith

/-! ## Any exact hierarchy of a centred family has line-ED active nodes -/

/-- The absolute constant of `card_activeIndexSet_filter_line_le_of_centred`: the centred net at
spacing `ρ/8` has at most this many points whose midpoint is within `5ρ(1+4R₀) + ρ/4` of the
foot of a line and whose direction is within `20ρ + ρ/4` of `±d`. -/
noncomputable def activeLineConstant (n : ℕ) (R₀ : ℝ) : ℝ :=
  2 * (160 * (1 + 4 * R₀) + 9) ^ n * 649 ^ n

open Classical in
/-- **The active nodes of *any* exact hierarchy of a centred family are line-essentially
distinct above the bottom level, at a constant `C · activeLineConstant`.**

Every active node `W` at level `k` inside `N_{5ρ_k}(L)` contains a *centred* member `T` with
`T ⊆ W ⊆ N_{5ρ_k}(L)`; `T`'s line parameters are then within `O(ρ_k)` of `L`'s
(`params_close_of_carrier_subset_line` — the centring step), so `T` lies inside one of `O(1)`
nodes `V` of the centred net at spacing `ρ_k/8` near `L` (`le_of_params_close`), and
`UniformTubeSet.boundedOverlap` allows at most `C` nodes to meet a given `V` through a member.
This is the body of the map's datum (E0's `LineEDLevels`) produced **without** a new uniformiser, from centredness
of the members alone . -/
theorem card_activeIndexSet_filter_line_le_of_centred {δ : NNReal} (hδ : 0 < δ) {ι : Type*}
    {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {C : NNReal} (𝒰 : UniformTubeSet s T N C)
    (hcen : ∀ i ∈ s, (T i).IsCentred) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (hmid : ∀ i ∈ s, ‖(T i).midpoint‖ ≤ R₀) {k : ℕ} (hk : k ≤ N)
    (h4 : 4 * (δ : ℝ) ≤ gridScale δ N k) (o d : E) (hd : ‖d‖ = 1) :
    (((𝒰.cover.activeIndexSet k).filter fun j ↦ (𝒰.cover.tube k j).carrier ⊆
        Metric.cthickening (5 * ((gridScale δ N k : NNReal) : ℝ))
          (Set.range fun t : ℝ ↦ o + t • d)).card : ℝ)
      ≤ (C : ℝ) * activeLineConstant (Module.finrank ℝ E) R₀ := by
  classical
  set ρ : NNReal := gridScale δ N k with hρdef
  have hρ : 0 < ρ := gridScale_pos hδ N k
  have hρr : (0 : ℝ) < ρ := by exact_mod_cast hρ
  have hδr : (0 : ℝ) < δ := by exact_mod_cast hδ
  set L : Set E := Set.range fun t : ℝ ↦ o + t • d with hL
  set A := (𝒰.cover.activeIndexSet k).filter fun j ↦ (𝒰.cover.tube k j).carrier ⊆
    Metric.cthickening (5 * (ρ : ℝ)) L with hA
  have hC0 : (0 : ℝ) ≤ C := C.coe_nonneg
  have hconst0 : 0 ≤ activeLineConstant (Module.finrank ℝ E) R₀ := by
    unfold activeLineConstant; positivity
  rcases A.eq_empty_or_nonempty with hAe | ⟨j₀, hj₀⟩
  · rw [hAe]; simp only [Finset.card_empty, Nat.cast_zero]; positivity
  -- a member in each active node
  have hpick : ∀ j ∈ A, ∃ i ∈ s, 𝒰.cover.assign k i = j :=
    fun j hj ↦ ((𝒰.cover.mem_activeIndexSet).mp (Finset.mem_filter.mp hj).1).2
  obtain ⟨i₀, -, -⟩ := hpick j₀ hj₀
  haveI : Nonempty ι := ⟨i₀⟩
  choose! pick hpick_mem hpick_eq using hpick
  have hmemT : ∀ j ∈ A, (T (pick j)).carrier ⊆ Metric.cthickening (5 * (ρ : ℝ)) L := by
    intro j hj
    have h1 := 𝒰.cover.le_tube_assign k hk (pick j) (hpick_mem j hj)
    rw [hpick_eq j hj] at h1
    exact fun x hx ↦ (Finset.mem_filter.mp hj).2 (h1 hx)
  -- the centred net at spacing `ρ/8`
  obtain ⟨G₀, hG₀cen, hG₀mid, hG₀sep, hG₀cover⟩ :=
    exists_centred_net (E := E) ρ R₀ (ε := (ρ : ℝ) / 8) (by positivity)
  have hnode : ∀ j ∈ A, ∃ V ∈ G₀, ‖(T (pick j)).midpoint - V.midpoint‖ ≤ 2 * ((ρ : ℝ) / 8) ∧
      ‖(T (pick j)).direction - V.direction‖ ≤ 2 * ((ρ : ℝ) / 8) :=
    fun j hj ↦ hG₀cover _ _ (hcen _ (hpick_mem j hj)) (T _).norm_direction (hmid _ (hpick_mem j hj))
  haveI : Nonempty (Tube ρ E) := ⟨ofMidpointDirection ρ 0 d hd⟩
  choose! Vmap hV_mem hV_mid hV_dir using hnode
  -- the member lies inside its net node
  have hle : ∀ j ∈ A, (T (pick j)).toConvexSpaceBody ≤ (Vmap j).toConvexSpaceBody := by
    intro j hj
    refine le_of_params_close _ _ (hV_mid j hj) (hV_dir j hj) ?_
    linarith
  -- the net node's parameters are in the two boxes
  set Rx : ℝ := 5 * ρ * (1 + 4 * R₀) + ρ / 4 with hRx
  set Ry : ℝ := 20 * ρ + ρ / 4 with hRy
  have hRx0 : 0 ≤ Rx := by rw [hRx]; positivity
  have hRy0 : 0 ≤ Ry := by rw [hRy]; positivity
  have hbox : ∀ j ∈ A, ‖(Vmap j).midpoint - lineFoot o d‖ ≤ Rx ∧
      (‖(Vmap j).direction - (1 : ℝ) • d‖ ≤ Ry ∨ ‖(Vmap j).direction - (-1 : ℝ) • d‖ ≤ Ry) := by
    intro j hj
    have hK : (1 : ℝ) ≤ 5 * ρ / δ := by rw [le_div_iff₀ hδr]; linarith
    have hKδ : (5 * (ρ : ℝ) / δ) * δ = 5 * ρ := by field_simp
    have hKm : (5 * (ρ : ℝ) / δ - 1) * δ = 5 * ρ - δ := by field_simp
    obtain ⟨sgn, hsgn, hdir, hmidc⟩ := params_close_of_carrier_subset_line (T (pick j))
      (hcen _ (hpick_mem j hj)) (hmid _ (hpick_mem j hj)) hd hK (by rw [hKδ]; exact hmemT j hj)
    rw [hKm] at hdir hmidc
    have hmid' : ‖(Vmap j).midpoint - (T (pick j)).midpoint‖ ≤ 2 * ((ρ : ℝ) / 8) := by
      rw [norm_sub_rev]; exact hV_mid j hj
    have hdir' : ‖(Vmap j).direction - (T (pick j)).direction‖ ≤ 2 * ((ρ : ℝ) / 8) := by
      rw [norm_sub_rev]; exact hV_dir j hj
    refine ⟨?_, ?_⟩
    · calc ‖(Vmap j).midpoint - lineFoot o d‖
          ≤ ‖(Vmap j).midpoint - (T (pick j)).midpoint‖ +
            ‖(T (pick j)).midpoint - lineFoot o d‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ 2 * ((ρ : ℝ) / 8) + (5 * ρ - δ) * (1 + 4 * R₀) := add_le_add hmid' hmidc
        _ ≤ Rx := by rw [hRx]; nlinarith [hδr.le, hR₀]
    · have hcalc : ‖(Vmap j).direction - sgn • d‖ ≤ Ry := by
        calc ‖(Vmap j).direction - sgn • d‖
            ≤ ‖(Vmap j).direction - (T (pick j)).direction‖ +
              ‖(T (pick j)).direction - sgn • d‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ ≤ 2 * ((ρ : ℝ) / 8) + 4 * (5 * ρ - δ) := add_le_add hdir' hdir
          _ ≤ Ry := by rw [hRy]; linarith
      rcases hsgn with rfl | rfl
      · exact Or.inl hcalc
      · exact Or.inr hcalc
  -- the image of `A` in the net lies in the box-filtered net
  set G₁ := G₀.filter fun V ↦ ‖V.midpoint - lineFoot o d‖ ≤ Rx ∧
    (‖V.direction - (1 : ℝ) • d‖ ≤ Ry ∨ ‖V.direction - (-1 : ℝ) • d‖ ≤ Ry) with hG₁
  have himg : A.image Vmap ⊆ G₁ := by
    intro V hV
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hV
    exact Finset.mem_filter.mpr ⟨hV_mem j hj, hbox j hj⟩
  -- each fibre of `Vmap` is bounded by `C` through `boundedOverlap`
  have hfibre : ∀ V ∈ A.image Vmap, ((A.filter fun j ↦ Vmap j = V).card : ℝ) ≤ C := by
    intro V _
    have hsub : A.filter (fun j ↦ Vmap j = V) ⊆
        (𝒰.cover.indexSet k).filter (fun j ↦ ∃ i ∈ s,
          (T i).toConvexSpaceBody ≤ (𝒰.cover.tube k j).toConvexSpaceBody ∧
          (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody) := by
      intro j hj
      obtain ⟨hjA, hjV⟩ := Finset.mem_filter.mp hj
      refine Finset.mem_filter.mpr ⟨𝒰.cover.activeIndexSet_subset k (Finset.mem_filter.mp hjA).1,
        pick j, hpick_mem j hjA, ?_, ?_⟩
      · have h1 := 𝒰.cover.le_tube_assign k hk (pick j) (hpick_mem j hjA)
        rwa [hpick_eq j hjA] at h1
      · rw [← hjV]; exact hle j hjA
    have h := 𝒰.boundedOverlap k hk V
    calc ((A.filter fun j ↦ Vmap j = V).card : ℝ)
        ≤ (((𝒰.cover.indexSet k).filter (fun j ↦ ∃ i ∈ s,
          (T i).toConvexSpaceBody ≤ (𝒰.cover.tube k j).toConvexSpaceBody ∧
          (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ C := by exact_mod_cast h
  have hcardA : (A.card : ℝ) ≤ ((A.image Vmap).card : ℝ) * C := by
    rw [Finset.card_eq_sum_card_image Vmap A]
    push_cast
    calc ∑ V ∈ A.image Vmap, ((A.filter fun j ↦ Vmap j = V).card : ℝ)
        ≤ ∑ V ∈ A.image Vmap, (C : ℝ) := Finset.sum_le_sum hfibre
      _ = ((A.image Vmap).card : ℝ) * C := by rw [Finset.sum_const, nsmul_eq_mul]
  have hG₁card : ((A.image Vmap).card : ℝ) ≤ (G₁.card : ℝ) := by
    exact_mod_cast Finset.card_le_card himg
  -- the box packing of the net
  have hpack : (G₁.card : ℝ) ≤ activeLineConstant (Module.finrank ℝ E) R₀ := by
    have h := card_filter_boxes_le_of_sep G₀ (fun V : Tube ρ E ↦ V) (ε := (ρ : ℝ) / 8)
      (by positivity) hG₀sep (lineFoot o d) d hRx0 hRy0
    have hx : (Rx + (ρ : ℝ) / 8 / 4) / ((ρ : ℝ) / 8 / 4) = 160 * (1 + 4 * R₀) + 9 := by
      rw [hRx]; field_simp; ring
    have hy : (Ry + (ρ : ℝ) / 8 / 4) / ((ρ : ℝ) / 8 / 4) = 649 := by
      rw [hRy]; field_simp; ring
    rw [hx, hy] at h
    exact h
  calc (A.card : ℝ) ≤ ((A.image Vmap).card : ℝ) * C := hcardA
    _ ≤ (G₁.card : ℝ) * C := by gcongr
    _ ≤ activeLineConstant (Module.finrank ℝ E) R₀ * C := by gcongr
    _ = (C : ℝ) * activeLineConstant (Module.finrank ℝ E) R₀ := mul_comm _ _

/-- **Every level above the bottom is line-essentially distinct, in the E0/C6-a spelling**, for
the active restriction of *any* exact hierarchy of a centred family, at the constant
`⌈C · activeLineConstant⌉₊`. -/
theorem isLineEssDistinct_activeIndexSet_of_centred {δ : NNReal} (hδ : 0 < δ) {ι : Type*}
    {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {C : NNReal} (𝒰 : UniformTubeSet s T N C)
    (hcen : ∀ i ∈ s, (T i).IsCentred) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (hmid : ∀ i ∈ s, ‖(T i).midpoint‖ ≤ R₀) {k : ℕ} (hk : k ≤ N)
    (h4 : 4 * (δ : ℝ) ≤ gridScale δ N k) :
    Kakeya.VeryNotSticky.IsLineEssDistinct
      ⌈(C : ℝ) * activeLineConstant (Module.finrank ℝ E) R₀⌉₊
      (𝒰.cover.activeIndexSet k) (𝒰.cover.tube k) := by
  classical
  intro p d hd
  have h := card_activeIndexSet_filter_line_le_of_centred hδ 𝒰 hcen hR₀ hmid hk h4 p d hd
  simp only [Kakeya.VeryNotSticky.lineNbhd_eq]
  have h' : (((𝒰.cover.activeIndexSet k).filter fun j ↦ (𝒰.cover.tube k j).carrier ⊆
      Metric.cthickening (5 * ((gridScale δ N k : NNReal) : ℝ))
        (Set.range fun t : ℝ ↦ p + t • d)).card : ℝ) ≤
      (⌈(C : ℝ) * activeLineConstant (Module.finrank ℝ E) R₀⌉₊ : ℝ) :=
    h.trans (Nat.le_ceil _)
  exact_mod_cast h'

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **The bottom level**: the nodes have the members' radius and each active node contains a
member inside it, so the count is that of the family's own line-based essential distinctness
`A₀` (refined l.5996–6002: the bottom family is `100δ^{-q}`-ED by the density bound — that
constant is the caller's, not absolute, which is why it enters as a hypothesis here and why the
refined text states (iii) for `k < M` only, l.3308). -/
theorem isLineEssDistinct_activeIndexSet_bottom {δ : NNReal} {ι : Type*}
    {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} (hN : 0 < N) {C : NNReal}
    (𝒰 : UniformTubeSet s T N C) {A₀ : ℕ}
    (hleaf : Kakeya.VeryNotSticky.IsLineEssDistinct A₀ s T) :
    Kakeya.VeryNotSticky.IsLineEssDistinct A₀ (𝒰.cover.activeIndexSet N) (𝒰.cover.tube N) := by
  classical
  intro p d hd
  have hρ : gridScale δ N N = δ := gridScale_self δ hN
  have hpick : ∀ j ∈ 𝒰.cover.activeIndexSet N, ∃ i ∈ s, 𝒰.cover.assign N i = j :=
    fun j hj ↦ ((𝒰.cover.mem_activeIndexSet).mp hj).2
  set A := (𝒰.cover.activeIndexSet N).filter fun j ↦ (𝒰.cover.tube N j).carrier ⊆
    Kakeya.VeryNotSticky.lineNbhd p d (5 * ((gridScale δ N N : NNReal) : ℝ)) with hA
  rcases A.eq_empty_or_nonempty with hAe | ⟨j₀, hj₀⟩
  · rw [hAe, Finset.card_empty]; exact Nat.zero_le _
  obtain ⟨i₀, -, -⟩ := hpick j₀ (Finset.mem_filter.mp hj₀).1
  haveI : Nonempty ι := ⟨i₀⟩
  choose! pick hpick_mem hpick_eq using hpick
  refine le_trans (Finset.card_le_card_of_injOn pick ?_ ?_) (hleaf p d hd)
  · intro j hj
    have hjact := (Finset.mem_filter.mp hj).1
    refine Finset.mem_filter.mpr ⟨hpick_mem j hjact, ?_⟩
    have h1 := 𝒰.cover.le_tube_assign N le_rfl (pick j) (hpick_mem j hjact)
    rw [hpick_eq j hjact] at h1
    have h2 := (Finset.mem_filter.mp hj).2
    have hρ' : (5 : ℝ) * ((gridScale δ N N : NNReal) : ℝ) = 5 * (δ : ℝ) := by rw [hρ]
    rw [hρ'] at h2
    exact fun x hx ↦ h2 (h1 hx)
  · intro j hj j' hj' hjj'
    have hjact := (Finset.mem_filter.mp hj).1
    have hj'act := (Finset.mem_filter.mp hj').1
    rw [← hpick_eq j hjact, ← hpick_eq j' hj'act, hjj']

/-- **Per-level line-ED at every level below the bottom (the body of E0's `LineEDLevels`
once its (b) re-cut `k < N` lands; stated flat so this leaf does not depend on (b)) for the active
restriction of any exact hierarchy of a centred family in `ℝ³`**, at
`⌈C · activeLineConstant 3 R₀⌉₊`.  The bottom level, exempted by (b), is
`isLineEssDistinct_activeIndexSet_bottom` at the family's own constant. -/
theorem forall_isLineEssDistinct_activeRestrict_of_centred {δ : NNReal} (hδ : 0 < δ) {ι : Type*}
    {s : Finset ι} {T : ι → Tube δ (EuclideanSpace ℝ (Fin 3))} {N : ℕ}
    {C : NNReal} (𝒰 : UniformTubeSet s T N C) (hcen : ∀ i ∈ s, (T i).IsCentred) {R₀ : ℝ}
    (hR₀ : 0 ≤ R₀) (hmid : ∀ i ∈ s, ‖(T i).midpoint‖ ≤ R₀)
    (h4 : ∀ k, k < N → 4 * (δ : ℝ) ≤ gridScale δ N k) :
    ∀ k, k < N → Kakeya.VeryNotSticky.IsLineEssDistinct
      ⌈(C : ℝ) * activeLineConstant (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) R₀⌉₊
      (𝒰.activeRestrict.cover.indexSet k) (𝒰.activeRestrict.cover.tube k) := by
  intro k hk
  change Kakeya.VeryNotSticky.IsLineEssDistinct _ (𝒰.cover.activeIndexSet k) (𝒰.cover.tube k)
  exact isLineEssDistinct_activeIndexSet_of_centred hδ 𝒰 hcen hR₀ hmid hk.le (h4 k hk)

/-! ## The same, at an arbitrary neighbourhood radius `K · ρ_k`  -/

/-- The absolute constant of `card_activeIndexSet_filter_line_le_of_centred_at`: the centred net
at spacing `ρ/8` has at most this many points whose midpoint is within `Kρ(1+4R₀) + ρ/4` of the
foot of a line and whose direction is within `4Kρ + ρ/4` of `±d`.  At `K = 5` it is
`activeLineConstant`. -/
noncomputable def activeLineConstantAt (n : ℕ) (R₀ K : ℝ) : ℝ :=
  2 * (32 * K * (1 + 4 * R₀) + 9) ^ n * (128 * K + 9) ^ n

theorem activeLineConstant_eq_at (n : ℕ) (R₀ : ℝ) :
    activeLineConstant n R₀ = activeLineConstantAt n R₀ 5 := by
  unfold activeLineConstant activeLineConstantAt
  norm_num

/-- The defining equation of `activeLineConstantAt`, exposed ; its radius-`5`
relation to `activeLineConstant` is `activeLineConstant_eq_at` above. -/
theorem activeLineConstantAt_eq (n : ℕ) (R₀ K : ℝ) :
    activeLineConstantAt n R₀ K = 2 * (32 * K * (1 + 4 * R₀) + 9) ^ n * (128 * K + 9) ^ n := rfl

open Classical in
/-- `card_activeIndexSet_filter_line_le_of_centred` at thickness `K ρ_k`, `1 ≤ K`. -/
theorem card_activeIndexSet_filter_line_le_of_centred_at {δ : NNReal} (hδ : 0 < δ) {ι : Type*}
    {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {C : NNReal} (𝒰 : UniformTubeSet s T N C)
    (hcen : ∀ i ∈ s, (T i).IsCentred) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (hmid : ∀ i ∈ s, ‖(T i).midpoint‖ ≤ R₀) {K : ℝ} (hK : 1 ≤ K) {k : ℕ} (hk : k ≤ N)
    (h4 : 4 * (δ : ℝ) ≤ gridScale δ N k) (o d : E) (hd : ‖d‖ = 1) :
    (((𝒰.cover.activeIndexSet k).filter fun j ↦ (𝒰.cover.tube k j).carrier ⊆
        Metric.cthickening (K * ((gridScale δ N k : NNReal) : ℝ))
          (Set.range fun t : ℝ ↦ o + t • d)).card : ℝ)
      ≤ (C : ℝ) * activeLineConstantAt (Module.finrank ℝ E) R₀ K := by
  classical
  set ρ : NNReal := gridScale δ N k with hρdef
  have hρ : 0 < ρ := gridScale_pos hδ N k
  have hρr : (0 : ℝ) < ρ := by exact_mod_cast hρ
  have hδr : (0 : ℝ) < δ := by exact_mod_cast hδ
  set L : Set E := Set.range fun t : ℝ ↦ o + t • d with hL
  set A := (𝒰.cover.activeIndexSet k).filter fun j ↦ (𝒰.cover.tube k j).carrier ⊆
    Metric.cthickening (K * (ρ : ℝ)) L with hA
  have hC0 : (0 : ℝ) ≤ C := C.coe_nonneg
  have hconst0 : 0 ≤ activeLineConstantAt (Module.finrank ℝ E) R₀ K := by
    unfold activeLineConstantAt
    have : (0:ℝ) ≤ 32 * K * (1 + 4 * R₀) + 9 := by positivity
    have : (0:ℝ) ≤ 128 * K + 9 := by positivity
    positivity
  rcases A.eq_empty_or_nonempty with hAe | ⟨j₀, hj₀⟩
  · rw [hAe]; simp only [Finset.card_empty, Nat.cast_zero]; positivity
  have hpick : ∀ j ∈ A, ∃ i ∈ s, 𝒰.cover.assign k i = j :=
    fun j hj ↦ ((𝒰.cover.mem_activeIndexSet).mp (Finset.mem_filter.mp hj).1).2
  obtain ⟨i₀, -, -⟩ := hpick j₀ hj₀
  haveI : Nonempty ι := ⟨i₀⟩
  choose! pick hpick_mem hpick_eq using hpick
  have hmemT : ∀ j ∈ A, (T (pick j)).carrier ⊆ Metric.cthickening (K * (ρ : ℝ)) L := by
    intro j hj
    have h1 := 𝒰.cover.le_tube_assign k hk (pick j) (hpick_mem j hj)
    rw [hpick_eq j hj] at h1
    exact fun x hx ↦ (Finset.mem_filter.mp hj).2 (h1 hx)
  obtain ⟨G₀, hG₀cen, hG₀mid, hG₀sep, hG₀cover⟩ :=
    exists_centred_net (E := E) ρ R₀ (ε := (ρ : ℝ) / 8) (by positivity)
  have hnode : ∀ j ∈ A, ∃ V ∈ G₀, ‖(T (pick j)).midpoint - V.midpoint‖ ≤ 2 * ((ρ : ℝ) / 8) ∧
      ‖(T (pick j)).direction - V.direction‖ ≤ 2 * ((ρ : ℝ) / 8) :=
    fun j hj ↦ hG₀cover _ _ (hcen _ (hpick_mem j hj)) (T _).norm_direction (hmid _ (hpick_mem j hj))
  haveI : Nonempty (Tube ρ E) := ⟨ofMidpointDirection ρ 0 d hd⟩
  choose! Vmap hV_mem hV_mid hV_dir using hnode
  have hle : ∀ j ∈ A, (T (pick j)).toConvexSpaceBody ≤ (Vmap j).toConvexSpaceBody := by
    intro j hj
    refine le_of_params_close _ _ (hV_mid j hj) (hV_dir j hj) ?_
    linarith
  set Rx : ℝ := K * ρ * (1 + 4 * R₀) + ρ / 4 with hRx
  set Ry : ℝ := 4 * (K * ρ) + ρ / 4 with hRy
  have hK0 : (0:ℝ) ≤ K := le_trans zero_le_one hK
  have hRx0 : 0 ≤ Rx := by rw [hRx]; positivity
  have hRy0 : 0 ≤ Ry := by rw [hRy]; positivity
  have hbox : ∀ j ∈ A, ‖(Vmap j).midpoint - lineFoot o d‖ ≤ Rx ∧
      (‖(Vmap j).direction - (1 : ℝ) • d‖ ≤ Ry ∨ ‖(Vmap j).direction - (-1 : ℝ) • d‖ ≤ Ry) := by
    intro j hj
    have hKρ : (ρ : ℝ) ≤ K * ρ := by nlinarith
    have hK' : (1 : ℝ) ≤ K * ρ / δ := by rw [le_div_iff₀ hδr]; linarith
    have hKδ : (K * (ρ : ℝ) / δ) * δ = K * ρ := by field_simp
    have hKm : (K * (ρ : ℝ) / δ - 1) * δ = K * ρ - δ := by field_simp
    obtain ⟨sgn, hsgn, hdir, hmidc⟩ := params_close_of_carrier_subset_line (T (pick j))
      (hcen _ (hpick_mem j hj)) (hmid _ (hpick_mem j hj)) hd hK' (by rw [hKδ]; exact hmemT j hj)
    rw [hKm] at hdir hmidc
    have hmid' : ‖(Vmap j).midpoint - (T (pick j)).midpoint‖ ≤ 2 * ((ρ : ℝ) / 8) := by
      rw [norm_sub_rev]; exact hV_mid j hj
    have hdir' : ‖(Vmap j).direction - (T (pick j)).direction‖ ≤ 2 * ((ρ : ℝ) / 8) := by
      rw [norm_sub_rev]; exact hV_dir j hj
    refine ⟨?_, ?_⟩
    · calc ‖(Vmap j).midpoint - lineFoot o d‖
          ≤ ‖(Vmap j).midpoint - (T (pick j)).midpoint‖ +
            ‖(T (pick j)).midpoint - lineFoot o d‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ 2 * ((ρ : ℝ) / 8) + (K * ρ - δ) * (1 + 4 * R₀) := add_le_add hmid' hmidc
        _ ≤ Rx := by rw [hRx]; nlinarith [hδr.le, hR₀]
    · have hcalc : ‖(Vmap j).direction - sgn • d‖ ≤ Ry := by
        calc ‖(Vmap j).direction - sgn • d‖
            ≤ ‖(Vmap j).direction - (T (pick j)).direction‖ +
              ‖(T (pick j)).direction - sgn • d‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ ≤ 2 * ((ρ : ℝ) / 8) + 4 * (K * ρ - δ) := add_le_add hdir' hdir
          _ ≤ Ry := by rw [hRy]; linarith
      rcases hsgn with rfl | rfl
      · exact Or.inl hcalc
      · exact Or.inr hcalc
  set G₁ := G₀.filter fun V ↦ ‖V.midpoint - lineFoot o d‖ ≤ Rx ∧
    (‖V.direction - (1 : ℝ) • d‖ ≤ Ry ∨ ‖V.direction - (-1 : ℝ) • d‖ ≤ Ry) with hG₁
  have himg : A.image Vmap ⊆ G₁ := by
    intro V hV
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hV
    exact Finset.mem_filter.mpr ⟨hV_mem j hj, hbox j hj⟩
  have hfibre : ∀ V ∈ A.image Vmap, ((A.filter fun j ↦ Vmap j = V).card : ℝ) ≤ C := by
    intro V _
    have hsub : A.filter (fun j ↦ Vmap j = V) ⊆
        (𝒰.cover.indexSet k).filter (fun j ↦ ∃ i ∈ s,
          (T i).toConvexSpaceBody ≤ (𝒰.cover.tube k j).toConvexSpaceBody ∧
          (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody) := by
      intro j hj
      obtain ⟨hjA, hjV⟩ := Finset.mem_filter.mp hj
      refine Finset.mem_filter.mpr ⟨𝒰.cover.activeIndexSet_subset k (Finset.mem_filter.mp hjA).1,
        pick j, hpick_mem j hjA, ?_, ?_⟩
      · have h1 := 𝒰.cover.le_tube_assign k hk (pick j) (hpick_mem j hjA)
        rwa [hpick_eq j hjA] at h1
      · rw [← hjV]; exact hle j hjA
    have h := 𝒰.boundedOverlap k hk V
    calc ((A.filter fun j ↦ Vmap j = V).card : ℝ)
        ≤ (((𝒰.cover.indexSet k).filter (fun j ↦ ∃ i ∈ s,
          (T i).toConvexSpaceBody ≤ (𝒰.cover.tube k j).toConvexSpaceBody ∧
          (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ C := by exact_mod_cast h
  have hcardA : (A.card : ℝ) ≤ ((A.image Vmap).card : ℝ) * C := by
    rw [Finset.card_eq_sum_card_image Vmap A]
    push_cast
    calc ∑ V ∈ A.image Vmap, ((A.filter fun j ↦ Vmap j = V).card : ℝ)
        ≤ ∑ V ∈ A.image Vmap, (C : ℝ) := Finset.sum_le_sum hfibre
      _ = ((A.image Vmap).card : ℝ) * C := by rw [Finset.sum_const, nsmul_eq_mul]
  have hG₁card : ((A.image Vmap).card : ℝ) ≤ (G₁.card : ℝ) := by
    exact_mod_cast Finset.card_le_card himg
  have hpack : (G₁.card : ℝ) ≤ activeLineConstantAt (Module.finrank ℝ E) R₀ K := by
    have h := card_filter_boxes_le_of_sep G₀ (fun V : Tube ρ E ↦ V) (ε := (ρ : ℝ) / 8)
      (by positivity) hG₀sep (lineFoot o d) d hRx0 hRy0
    have hx : (Rx + (ρ : ℝ) / 8 / 4) / ((ρ : ℝ) / 8 / 4) = 32 * K * (1 + 4 * R₀) + 9 := by
      rw [hRx]; field_simp; ring
    have hy : (Ry + (ρ : ℝ) / 8 / 4) / ((ρ : ℝ) / 8 / 4) = 128 * K + 9 := by
      rw [hRy]; field_simp; ring
    rw [hx, hy] at h
    exact h
  calc (A.card : ℝ) ≤ ((A.image Vmap).card : ℝ) * C := hcardA
    _ ≤ (G₁.card : ℝ) * C := by gcongr
    _ ≤ activeLineConstantAt (Module.finrank ℝ E) R₀ K * C := by gcongr
    _ = (C : ℝ) * activeLineConstantAt (Module.finrank ℝ E) R₀ K := mul_comm _ _

/-- **E0's `IsLineEssDistinctAt K` for the active nodes above the bottom level**, from centredness
alone, at `⌈C · activeLineConstantAt n R₀ K⌉₊`. -/
theorem isLineEssDistinctAt_activeIndexSet_of_centred {δ : NNReal} (hδ : 0 < δ) {ι : Type*}
    {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {C : NNReal} (𝒰 : UniformTubeSet s T N C)
    (hcen : ∀ i ∈ s, (T i).IsCentred) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (hmid : ∀ i ∈ s, ‖(T i).midpoint‖ ≤ R₀) {K : ℝ} (hK : 1 ≤ K) {k : ℕ} (hk : k ≤ N)
    (h4 : 4 * (δ : ℝ) ≤ gridScale δ N k) :
    Kakeya.VeryNotSticky.IsLineEssDistinctAt K
      ⌈(C : ℝ) * activeLineConstantAt (Module.finrank ℝ E) R₀ K⌉₊
      (𝒰.cover.activeIndexSet k) (𝒰.cover.tube k) := by
  classical
  intro p d hd
  have h := card_activeIndexSet_filter_line_le_of_centred_at hδ 𝒰 hcen hR₀ hmid hK hk h4 p d hd
  simp only [Kakeya.VeryNotSticky.lineNbhd_eq]
  have h' : (((𝒰.cover.activeIndexSet k).filter fun j ↦ (𝒰.cover.tube k j).carrier ⊆
      Metric.cthickening (K * ((gridScale δ N k : NNReal) : ℝ))
        (Set.range fun t : ℝ ↦ p + t • d)).card : ℝ) ≤
      (⌈(C : ℝ) * activeLineConstantAt (Module.finrank ℝ E) R₀ K⌉₊ : ℝ) :=
    h.trans (Nat.le_ceil _)
  exact_mod_cast h'

/-- **The per-level datum names**, on the active restriction, flat: every level below the
bottom is `IsLineEssDistinctAt K`-distinct at `⌈C · activeLineConstantAt n R₀ K⌉₊`.  The same fact
under E0's `LineEDLevelsAt` is `lineEDLevelsAt_activeRestrict_of_centred` below. -/
theorem forall_isLineEssDistinctAt_activeRestrict_of_centred {δ : NNReal} (hδ : 0 < δ)
    {ι : Type*} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {C : NNReal}
    (𝒰 : UniformTubeSet s T N C) (hcen : ∀ i ∈ s, (T i).IsCentred) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (hmid : ∀ i ∈ s, ‖(T i).midpoint‖ ≤ R₀) {K : ℝ} (hK : 1 ≤ K)
    (h4 : ∀ k, k < N → 4 * (δ : ℝ) ≤ gridScale δ N k) :
    ∀ k, k < N → Kakeya.VeryNotSticky.IsLineEssDistinctAt K
      ⌈(C : ℝ) * activeLineConstantAt (Module.finrank ℝ E) R₀ K⌉₊
      (𝒰.activeRestrict.cover.indexSet k) (𝒰.activeRestrict.cover.tube k) := by
  intro k hk
  change Kakeya.VeryNotSticky.IsLineEssDistinctAt K _ (𝒰.cover.activeIndexSet k) (𝒰.cover.tube k)
  exact isLineEssDistinctAt_activeIndexSet_of_centred hδ 𝒰 hcen hR₀ hmid hK hk.le (h4 k hk)

/-- **producer side:** E0's `LineEDLevelsAt K` for the active
restriction of any exact hierarchy of a centred family, at `⌈C · activeLineConstantAt n R₀ K⌉₊`,
`1 ≤ K`.  Definitionally the flat form above. -/
theorem lineEDLevelsAt_activeRestrict_of_centred {δ : NNReal} (hδ : 0 < δ)
    {ι : Type*} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {C : NNReal}
    (𝒰 : UniformTubeSet s T N C) (hcen : ∀ i ∈ s, (T i).IsCentred) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (hmid : ∀ i ∈ s, ‖(T i).midpoint‖ ≤ R₀) {K : ℝ} (hK : 1 ≤ K)
    (h4 : ∀ k, k < N → 4 * (δ : ℝ) ≤ gridScale δ N k) :
    Kakeya.VeryNotSticky.LineEDLevelsAt K
      ⌈(C : ℝ) * activeLineConstantAt (Module.finrank ℝ E) R₀ K⌉₊ 𝒰.activeRestrict :=
  forall_isLineEssDistinctAt_activeRestrict_of_centred hδ 𝒰 hcen hR₀ hmid hK h4

/-- **The meeting point of the chain , at `C₃ = Kakeya.Tube.tubeOverlapCoreClose.C 3`:**
`LineEDLevelsAt C₃ A₁ 𝒰.activeRestrict` with `A₁ = ⌈C · activeLineConstantAt n R₀ C₃⌉₊`. -/
theorem lineEDLevelsAt_C3_activeRestrict_of_centred {δ : NNReal} (hδ : 0 < δ)
    {ι : Type*} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {C : NNReal}
    (𝒰 : UniformTubeSet s T N C) (hcen : ∀ i ∈ s, (T i).IsCentred) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (hmid : ∀ i ∈ s, ‖(T i).midpoint‖ ≤ R₀)
    (h4 : ∀ k, k < N → 4 * (δ : ℝ) ≤ gridScale δ N k) :
    Kakeya.VeryNotSticky.LineEDLevelsAt (Kakeya.Tube.tubeOverlapCoreClose.C 3)
      ⌈(C : ℝ) * activeLineConstantAt (Module.finrank ℝ E) R₀
        (Kakeya.Tube.tubeOverlapCoreClose.C 3)⌉₊
      𝒰.activeRestrict :=
  lineEDLevelsAt_activeRestrict_of_centred hδ 𝒰 hcen hR₀ hmid
    (le_of_lt (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C 3)) h4

/-- The flat form of the `C₃` instance, kept as a corollary (additive; no consumer in the tree at
`a8683a7e4`). -/
theorem forall_isLineEssDistinctAt_C3_activeRestrict_of_centred {δ : NNReal} (hδ : 0 < δ)
    {ι : Type*} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {C : NNReal}
    (𝒰 : UniformTubeSet s T N C) (hcen : ∀ i ∈ s, (T i).IsCentred) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (hmid : ∀ i ∈ s, ‖(T i).midpoint‖ ≤ R₀)
    (h4 : ∀ k, k < N → 4 * (δ : ℝ) ≤ gridScale δ N k) :
    ∀ k, k < N → Kakeya.VeryNotSticky.IsLineEssDistinctAt (Kakeya.Tube.tubeOverlapCoreClose.C 3)
      ⌈(C : ℝ) * activeLineConstantAt (Module.finrank ℝ E) R₀
        (Kakeya.Tube.tubeOverlapCoreClose.C 3)⌉₊
      (𝒰.activeRestrict.cover.indexSet k) (𝒰.activeRestrict.cover.tube k) :=
  lineEDLevelsAt_C3_activeRestrict_of_centred hδ 𝒰 hcen hR₀ hmid h4

/-- **The refined-radius datum itself**, E0's `LineEDLevels` (= `LineEDLevelsAt 5`), for the active
restriction, at `⌈C · activeLineConstant n R₀⌉₊` (`activeLineConstant_eq_at`). -/
theorem lineEDLevels_activeRestrict_of_centred {δ : NNReal} (hδ : 0 < δ)
    {ι : Type*} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {C : NNReal}
    (𝒰 : UniformTubeSet s T N C) (hcen : ∀ i ∈ s, (T i).IsCentred) {R₀ : ℝ} (hR₀ : 0 ≤ R₀)
    (hmid : ∀ i ∈ s, ‖(T i).midpoint‖ ≤ R₀)
    (h4 : ∀ k, k < N → 4 * (δ : ℝ) ≤ gridScale δ N k) :
    Kakeya.VeryNotSticky.LineEDLevels
      ⌈(C : ℝ) * activeLineConstant (Module.finrank ℝ E) R₀⌉₊ 𝒰.activeRestrict := by
  rw [activeLineConstant_eq_at]
  exact lineEDLevelsAt_activeRestrict_of_centred hδ 𝒰 hcen hR₀ hmid (by norm_num) h4

end Tube

namespace ShadedTube

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E] {ι : Type*}

/-- **A shaded uniform set restricted to the active nodes of its tube hierarchy.**  The Def 2.2
brackets are quantified over the nodes a point's fibre meets — all of them active — and read the
unchanged assignment, so they transfer verbatim. -/
noncomputable def ShadedUniformTubeSet.activeRestrict {δ : NNReal} {s : Finset ι}
    {V : ι → ShadedTube δ E} {N : ℕ} {C : NNReal} (𝒱 : ShadedUniformTubeSet s V N C) :
    ShadedUniformTubeSet s V N C where
  tubeUniform := 𝒱.tubeUniform.activeRestrict
  branchingN := 𝒱.branchingN
  localN := 𝒱.localN
  card_shadeClass_le := 𝒱.card_shadeClass_le
  le_card_shadeClass := 𝒱.le_card_shadeClass
  branchingN_le := 𝒱.branchingN_le
  le_branchingN := 𝒱.le_branchingN

omit [Nontrivial E] in
@[simp] theorem ShadedUniformTubeSet.activeRestrict_tubeUniform {δ : NNReal} {s : Finset ι}
    {V : ι → ShadedTube δ E} {N : ℕ} {C : NNReal} (𝒱 : ShadedUniformTubeSet s V N C) :
    𝒱.activeRestrict.tubeUniform = 𝒱.tubeUniform.activeRestrict := rfl

end ShadedTube
