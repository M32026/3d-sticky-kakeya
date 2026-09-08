/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.BallConstruction
public import Kakeya.DimensionThree.MainLemma2.LineEssDistinct
public import Kakeya.Mathlib.Analysis.IsSeparated

/-!
# C7-b, the geometry: canonical capsules on centred net lines

Source of record: the professor's refined proof
`260115_kakeyadetailedproofv3_revised_detailed.tex` , l.3700–3724 and
l.5354–5473 (`propvnslocalization`), mapped  and row
C7-b of its §4.1; status and the two contract pins that block the *producer* 

## The object

The refined local family: "for each tube meeting a retained cube, choose on its core line a
segment … and thicken it by `4δ`" (l.3701–3704); "a grazing set `T ∩ B_c` itself is never
declared to be a plank" (l.5370–5371); the capsule of a tube is on a **net** line and contains
`T ∩ B_c` by construction (l.5368).  In the tree the pieces are `P B ⊆ ball (ctr B) (r₁/16)`
(`BallDataGeneralTarget`'s binder), so the capsule is the closed `ρ`-neighbourhood of the segment
of half-length `L` on the net line **centred at the foot of `ctr B`** — which is exactly the tree's
`Kakeya.VeryNotSticky.segCarrierSet` of an auxiliary unit `ρ`-tube on that line centred at the
foot (`Kakeya.VeryNotSticky.centredTube`).  Every T3 lemma about `segCarrierSet` (thickness
profile, containment in the ball, containment in a line neighbourhood, thickness scale, `δ`-ball
covers, volume) therefore applies verbatim to the capsules; this leaf adds what the refined
construction needs beyond T3:

* `Kakeya.VeryNotSticky.tube_inter_ball_subset_capsuleAt_of_close` — the part of a tube inside the
  piece lies in the capsule of **any** tube whose centred line parameters are `ε`-close, at capsule
  radius `δ + ε` (refined "`T ∩ B_c ⊂ S`", the `into` field of `BallDataCore` after assignment);
* `Kakeya.VeryNotSticky.capsuleAt_subset_cthickening_line_of_close` — the capsule lies in the
  `(ρ + ε)`-neighbourhood of the core line of any `ε`-close parent (the `segs_core` field);
* `Kakeya.VeryNotSticky.capsuleAt_subset_closedBall` — the capsule lies in
  `B̄(c, ‖foot − c‖ + L + ρ)` (the `segs_subset_ball` field, **at radius `r₁`** for the tree's
  pieces: `‖foot − c‖ ≤ r₁/16 + δ`, `L = r₁/8`, `ρ = 4δ`);
* `Kakeya.HasThicknesses.of_profile_le` — the profile `![4L, ρ, ρ]` at constant `4` that T3
  gives becomes `![r₁, δ, δ]` at a `δ`-free constant (the `segs_thickness` field).

The parameters of a tube relative to the centre `c` are the pair `(foot T c − c, T.direction)`
with `foot T c ⊥`-projection of `c` onto the core line (`Kakeya.VeryNotSticky.foot`); the
closeness of two tubes is measured by `‖Δfoot‖ + L·‖Δdirection‖`, the metric in which the net
of l.4778–4784 is `δ`-separated (the direction term is scaled by the capsule half-length so that
a direction error contributes at most its lateral effect along the capsule).

Everything here is proved; nothing is left as an obligation.  The net, the assignment, the
fibre bound and the degree bound (refined eqvnsfibresize, `propvnslocalization`'s
`A₀`-essential distinctness) are the next increments of this leaf.
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

namespace Kakeya.VeryNotSticky

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {δ : NNReal}

/-! ### The foot of the centre on the core line, and Pythagoras -/

/-- The parameter of the point of `T`'s core **line** (not segment) nearest to `c`. -/
noncomputable def footParam (T : Tube δ E3) (c : E3) : ℝ := inner ℝ (c - T.x) T.direction

/-- The foot of `c` on `T`'s core line: the orthogonal projection of `c`. -/
noncomputable def foot (T : Tube δ E3) (c : E3) : E3 := T.x + footParam T c • T.direction

theorem foot_eq_corePt (T : Tube δ E3) (c : E3) : foot T c = corePt T (footParam T c) := rfl

/-- `foot T c − c` is orthogonal to the direction. -/
theorem inner_foot_sub_direction (T : Tube δ E3) (c : E3) :
    inner ℝ (foot T c - c) T.direction = 0 := by
  have h1 : foot T c - c = (T.x - c) + footParam T c • T.direction := by
    simp only [foot]; abel
  rw [h1, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, T.norm_direction]
  simp only [footParam, one_pow, mul_one]
  rw [← inner_add_left]
  simp

/-- Every core point is `foot + s • direction`. -/
theorem corePt_eq_foot_add (T : Tube δ E3) (c : E3) (t : ℝ) :
    corePt T t = foot T c + (t - footParam T c) • T.direction := by
  simp only [corePt, foot]; module

/-- **Pythagoras along the core line**: `‖foot + s•d − c‖² = s² + ‖foot − c‖²`. -/
theorem norm_foot_add_smul_sub_sq (T : Tube δ E3) (c : E3) (s : ℝ) :
    ‖foot T c + s • T.direction - c‖ ^ 2 = s ^ 2 + ‖foot T c - c‖ ^ 2 := by
  have h : foot T c + s • T.direction - c = s • T.direction + (foot T c - c) := by abel
  have hin : inner ℝ T.direction (foot T c - c) = 0 := by
    rw [real_inner_comm]; exact inner_foot_sub_direction T c
  rw [h, norm_add_sq_real, norm_smul, T.norm_direction, mul_one, Real.norm_eq_abs, sq_abs,
    real_inner_smul_left, hin, mul_zero, mul_zero, add_zero]

/-- The axial offset of a line point from the foot is at most its distance to `c`. -/
theorem abs_le_norm_foot_add_smul_sub (T : Tube δ E3) (c : E3) (s : ℝ) :
    |s| ≤ ‖foot T c + s • T.direction - c‖ := by
  have h := norm_foot_add_smul_sub_sq T c s
  have hsq : s ^ 2 ≤ ‖foot T c + s • T.direction - c‖ ^ 2 := by
    rw [h]; nlinarith [sq_nonneg ‖foot T c - c‖]
  have := sq_le_sq.mp hsq
  rwa [abs_of_nonneg (norm_nonneg _)] at this

/-- The foot is at least as close to `c` as any line point. -/
theorem norm_foot_sub_le (T : Tube δ E3) (c : E3) (s : ℝ) :
    ‖foot T c - c‖ ≤ ‖foot T c + s • T.direction - c‖ := by
  have h := norm_foot_add_smul_sub_sq T c s
  have hsq : ‖foot T c - c‖ ^ 2 ≤ ‖foot T c + s • T.direction - c‖ ^ 2 := by
    rw [h]; nlinarith [sq_nonneg s]
  have := sq_le_sq.mp hsq
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] at this

/-- A core point of `T` is `foot + s • direction` with `|s| ≤ dist z c`. -/
theorem exists_foot_param_of_mem_core (T : Tube δ E3) (c : E3) {z : E3}
    (hz : z ∈ segment ℝ T.x T.y) :
    ∃ s : ℝ, z = foot T c + s • T.direction ∧ |s| ≤ dist z c := by
  obtain ⟨t, -, rfl⟩ := exists_corePt_of_mem_core T hz
  refine ⟨t - footParam T c, corePt_eq_foot_add T c t, ?_⟩
  rw [dist_eq_norm, corePt_eq_foot_add]
  exact abs_le_norm_foot_add_smul_sub T c _

/-- If `T` meets `ball c r`, its foot is within `r + δ` of `c`. -/
theorem norm_foot_sub_le_of_meets (T : Tube δ E3) (c : E3) {r : ℝ}
    (hmeet : (T.carrier ∩ ball c r).Nonempty) : ‖foot T c - c‖ ≤ r + (δ : ℝ) := by
  obtain ⟨x, hxT, hxc⟩ := hmeet
  rw [T.carrier_eq] at hxT
  obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.mp hxT
  obtain ⟨s, hzs, -⟩ := exists_foot_param_of_mem_core T c hz
  have hzc : dist z c ≤ r + δ := by
    calc dist z c ≤ dist z x + dist x c := dist_triangle _ _ _
      _ ≤ δ + r := add_le_add (by rw [dist_comm]; exact hxz) (le_of_lt hxc)
      _ = r + δ := add_comm _ _
  calc ‖foot T c - c‖ ≤ ‖foot T c + s • T.direction - c‖ := norm_foot_sub_le T c s
    _ = dist z c := by rw [hzs, dist_eq_norm]
    _ ≤ r + δ := hzc

/-! ### The centred auxiliary tube and the capsule -/

theorem dist_foot_sub_add (T : Tube δ E3) (c : E3) :
    dist (foot T c - (1 / 2 : ℝ) • T.direction) (foot T c + (1 / 2 : ℝ) • T.direction) = 1 := by
  rw [dist_eq_norm]
  have h : foot T c - (1 / 2 : ℝ) • T.direction - (foot T c + (1 / 2 : ℝ) • T.direction)
      = -T.direction := by module
  rw [h, norm_neg, T.norm_direction]

/-- **The centred auxiliary tube**: the unit `ρ`-tube on `T`'s core line whose midpoint is the
foot of `c`.  Its `segCarrierSet` at `c` is the capsule. -/
noncomputable def centredTube (T : Tube δ E3) (c : E3) (ρ : NNReal) : Tube ρ E3 :=
  Tube.mk' ρ (dist_foot_sub_add T c)

theorem centredTube_x (T : Tube δ E3) (c : E3) (ρ : NNReal) :
    (centredTube T c ρ).x = foot T c - (1 / 2 : ℝ) • T.direction := rfl

theorem centredTube_y (T : Tube δ E3) (c : E3) (ρ : NNReal) :
    (centredTube T c ρ).y = foot T c + (1 / 2 : ℝ) • T.direction := rfl

theorem centredTube_direction (T : Tube δ E3) (c : E3) (ρ : NNReal) :
    (centredTube T c ρ).direction = T.direction := by
  simp only [Tube.direction, centredTube_x, centredTube_y]; module

theorem corePt_centredTube (T : Tube δ E3) (c : E3) (ρ : NNReal) (t : ℝ) :
    corePt (centredTube T c ρ) t = foot T c + (t - 1 / 2) • T.direction := by
  simp only [corePt, centredTube_x, centredTube_direction]; module

/-- The nearest core point of the centred tube to `c` is its midpoint. -/
theorem coreParam_centredTube (T : Tube δ E3) (c : E3) (ρ : NNReal) :
    coreParam (centredTube T c ρ) c = 1 / 2 := by
  set U := centredTube T c ρ with hU
  have hmin := coreParam_min U c (u := 1 / 2) ⟨by norm_num, by norm_num⟩
  rw [dist_eq_norm, dist_eq_norm, hU, corePt_centredTube, corePt_centredTube] at hmin
  have hsq : ‖foot T c + (coreParam U c - 1 / 2) • T.direction - c‖ ^ 2 ≤
      ‖foot T c + ((1 : ℝ) / 2 - 1 / 2) • T.direction - c‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hmin 2
  rw [norm_foot_add_smul_sub_sq, norm_foot_add_smul_sub_sq] at hsq
  have h0 : (coreParam U c - 1 / 2) ^ 2 = 0 :=
    le_antisymm (by nlinarith [hsq]) (sq_nonneg _)
  have := pow_eq_zero_iff (two_ne_zero) |>.mp h0
  linarith

theorem segStart_centredTube (T : Tube δ E3) (c : E3) (ρ : NNReal) {L : ℝ}
    (hL1 : L ≤ 1 / 2) : segStart (centredTube T c ρ) c L = 1 / 2 - L := by
  simp only [segStart, coreParam_centredTube]
  rw [max_eq_left (by linarith [hL1]), min_eq_left (by linarith [hL1])]

/-- **The capsule** of `T` at centre `c`, radius `ρ`, half-length `L`: the tree's
`segCarrierSet` of the centred auxiliary tube — the closed `ρ`-neighbourhood of the segment of
half-length `L` on `T`'s core line centred at the foot of `c`. -/
noncomputable def capsuleAt (T : Tube δ E3) (c : E3) (ρ : NNReal) (L : ℝ) : Set E3 :=
  segCarrierSet (centredTube T c ρ) c L

/-- The capsule, explicitly. -/
theorem capsuleAt_eq (T : Tube δ E3) (c : E3) (ρ : NNReal) {L : ℝ}
    (hL1 : L ≤ 1 / 2) :
    capsuleAt T c ρ L = cthickening (ρ : ℝ)
      (segment ℝ (foot T c - L • T.direction) (foot T c + L • T.direction)) := by
  simp only [capsuleAt, segCarrierSet, segStart_centredTube T c ρ hL1, corePt_centredTube]
  rw [show foot T c + ((1 : ℝ) / 2 - L - 1 / 2) • T.direction = foot T c - L • T.direction by
      module,
    show foot T c + ((1 : ℝ) / 2 - L + 2 * L - 1 / 2) • T.direction
      = foot T c + L • T.direction by module]

/-- A point within `ρ` of a core point `foot + s • d`, `|s| ≤ L`, lies in the capsule. -/
theorem mem_capsuleAt_of_dist_le (T : Tube δ E3) (c : E3) (ρ : NNReal) {L s : ℝ} (hL : 0 ≤ L)
    (hL1 : L ≤ 1 / 2) (hs : |s| ≤ L) {x : E3}
    (hx : dist x (foot T c + s • T.direction) ≤ ρ) : x ∈ capsuleAt T c ρ L := by
  have hs' := abs_le.mp hs
  have hseg : foot T c + s • T.direction ∈
      segment ℝ (corePt (centredTube T c ρ) (segStart (centredTube T c ρ) c L))
        (corePt (centredTube T c ρ) (segStart (centredTube T c ρ) c L + 2 * L)) := by
    rw [segStart_centredTube T c ρ hL1]
    refine corePt_image_subset_segment (centredTube T c ρ) (by linarith)
      ⟨1 / 2 + s, ⟨by linarith, by linarith⟩, ?_⟩
    rw [corePt_centredTube]
    congr 1
    ring_nf
  exact mem_cthickening_of_dist_le x _ _ _ hseg hx

/-- A point of the capsule is within `ρ` of a core point `foot + s • d` with `|s| ≤ L`. -/
theorem exists_core_of_mem_capsuleAt (T : Tube δ E3) (c : E3) (ρ : NNReal) {L : ℝ} (hL : 0 ≤ L)
    (hL1 : L ≤ 1 / 2) {x : E3} (hx : x ∈ capsuleAt T c ρ L) :
    ∃ s : ℝ, |s| ≤ L ∧ dist x (foot T c + s • T.direction) ≤ ρ := by
  rw [capsuleAt, segCarrierSet_eq_biUnion] at hx
  obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.mp hx
  rw [segStart_centredTube T c ρ hL1] at hw
  obtain ⟨u, hu, rfl⟩ := segment_subset_corePt_image (centredTube T c ρ) (by linarith) hw
  refine ⟨u - 1 / 2, ?_, ?_⟩
  · rw [abs_le]; constructor <;> linarith [hu.1, hu.2]
  · rw [← corePt_centredTube]; exact hxw

/-! ### Containments -/

/-- **The part of `T` inside `ball c r` lies in the capsule of any `ε`-close tube `T'`**, at
capsule radius `≥ δ + ε` and half-length `L ≥ r + δ`.  Closeness is `‖Δfoot‖ + L‖Δdir‖ ≤ ε`.
With `T' = T`, `ε = 0` this is the refined "`T ∩ B_c ⊂ S`"; with `T'` the assigned net tube it
is the `into` field of `BallDataCore` after assignment. -/
theorem tube_inter_ball_subset_capsuleAt_of_close (T T' : Tube δ E3) (c : E3) {L r ε : ℝ}
    {ρ : NNReal} (hL : 0 ≤ L) (hL1 : L ≤ 1 / 2) (hr : r + (δ : ℝ) ≤ L)
    (hclose : ‖foot T c - foot T' c‖ + L * ‖T.direction - T'.direction‖ ≤ ε)
    (hρ : (δ : ℝ) + ε ≤ ρ) :
    T.carrier ∩ ball c r ⊆ capsuleAt T' c ρ L := by
  rintro x ⟨hxT, hxc⟩
  rw [T.carrier_eq] at hxT
  obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.mp hxT
  rw [Metric.mem_closedBall] at hxz
  obtain ⟨s, hzs, hs⟩ := exists_foot_param_of_mem_core T c hz
  have hzc : dist z c ≤ r + δ := by
    calc dist z c ≤ dist z x + dist x c := dist_triangle _ _ _
      _ ≤ δ + r := add_le_add (by rw [dist_comm]; exact hxz) (le_of_lt hxc)
      _ = r + δ := add_comm _ _
  have hsL : |s| ≤ L := le_trans hs (hzc.trans hr)
  refine mem_capsuleAt_of_dist_le T' c ρ hL hL1 hsL ?_
  calc dist x (foot T' c + s • T'.direction)
      ≤ dist x z + dist z (foot T' c + s • T'.direction) := dist_triangle _ _ _
    _ ≤ δ + ε := by
        refine add_le_add hxz ?_
        rw [hzs, dist_eq_norm]
        have h : foot T c + s • T.direction - (foot T' c + s • T'.direction)
            = (foot T c - foot T' c) + s • (T.direction - T'.direction) := by module
        rw [h]
        calc ‖(foot T c - foot T' c) + s • (T.direction - T'.direction)‖
            ≤ ‖foot T c - foot T' c‖ + ‖s • (T.direction - T'.direction)‖ := norm_add_le _ _
          _ = ‖foot T c - foot T' c‖ + |s| * ‖T.direction - T'.direction‖ := by
              rw [norm_smul, Real.norm_eq_abs]
          _ ≤ ‖foot T c - foot T' c‖ + L * ‖T.direction - T'.direction‖ := by gcongr
          _ ≤ ε := hclose
    _ ≤ ρ := hρ

/-- The part of `T` inside `ball c r` lies in its own capsule (radius `≥ δ`, half-length
`≥ r + δ`). -/
theorem tube_inter_ball_subset_capsuleAt (T : Tube δ E3) (c : E3) {L r : ℝ} {ρ : NNReal}
    (hL : 0 ≤ L) (hL1 : L ≤ 1 / 2) (hr : r + (δ : ℝ) ≤ L) (hρ : δ ≤ ρ) :
    T.carrier ∩ ball c r ⊆ capsuleAt T c ρ L :=
  tube_inter_ball_subset_capsuleAt_of_close T T c hL hL1 hr (ε := 0) (by simp) (by simpa using hρ)

/-- **The capsule of `T'` lies in the `(ρ + ε)`-neighbourhood of the core line of any `ε`-close
`T`** — the `segs_core` field of `BallDataCore` for every parent of the capsule's fibre. -/
theorem capsuleAt_subset_cthickening_line_of_close (T T' : Tube δ E3) (c : E3) {L ε C : ℝ}
    {ρ : NNReal} (hL : 0 ≤ L) (hL1 : L ≤ 1 / 2)
    (hclose : ‖foot T' c - foot T c‖ + L * ‖T'.direction - T.direction‖ ≤ ε)
    (hC : (ρ : ℝ) + ε ≤ C) :
    capsuleAt T' c ρ L ⊆ cthickening C
      (AffineSubspace.mk' (foot T c) (Submodule.span ℝ {T.direction}) : Set E3) := by
  intro x hx
  obtain ⟨s, hs, hxs⟩ := exists_core_of_mem_capsuleAt T' c ρ hL hL1 hx
  have hq : foot T c + s • T.direction ∈
      (AffineSubspace.mk' (foot T c) (Submodule.span ℝ {T.direction}) : Set E3) := by
    rw [SetLike.mem_coe, AffineSubspace.mem_mk', vsub_eq_sub, add_sub_cancel_left]
    exact Submodule.mem_span_singleton.mpr ⟨s, rfl⟩
  refine mem_cthickening_of_dist_le x _ _ _ hq ?_
  calc dist x (foot T c + s • T.direction)
      ≤ dist x (foot T' c + s • T'.direction)
        + dist (foot T' c + s • T'.direction) (foot T c + s • T.direction) := dist_triangle _ _ _
    _ ≤ ρ + ε := by
        refine add_le_add hxs ?_
        rw [dist_eq_norm]
        have h : foot T' c + s • T'.direction - (foot T c + s • T.direction)
            = (foot T' c - foot T c) + s • (T'.direction - T.direction) := by module
        rw [h]
        calc ‖(foot T' c - foot T c) + s • (T'.direction - T.direction)‖
            ≤ ‖foot T' c - foot T c‖ + ‖s • (T'.direction - T.direction)‖ := norm_add_le _ _
          _ = ‖foot T' c - foot T c‖ + |s| * ‖T'.direction - T.direction‖ := by
              rw [norm_smul, Real.norm_eq_abs]
          _ ≤ ‖foot T' c - foot T c‖ + L * ‖T'.direction - T.direction‖ := by gcongr
          _ ≤ ε := hclose
    _ ≤ C := hC

/-- **The capsule lies in the ball** `B̄(c, ‖foot − c‖ + L + ρ)` — the `segs_subset_ball` field,
at radius `r₁` when `‖foot − c‖ ≤ r₁/16 + δ`, `L = r₁/8`, `ρ = 4δ`, `δ ≤ r₁/16`. -/
theorem capsuleAt_subset_closedBall (T : Tube δ E3) (c : E3) (ρ : NNReal) {L R : ℝ} (hL : 0 ≤ L)
    (hL1 : L ≤ 1 / 2) (hR : ‖foot T c - c‖ + L + (ρ : ℝ) ≤ R) :
    capsuleAt T c ρ L ⊆ closedBall c R := by
  intro x hx
  obtain ⟨s, hs, hxs⟩ := exists_core_of_mem_capsuleAt T c ρ hL hL1 hx
  rw [Metric.mem_closedBall]
  calc dist x c ≤ dist x (foot T c + s • T.direction) + dist (foot T c + s • T.direction) c :=
        dist_triangle _ _ _
    _ ≤ ρ + (‖foot T c - c‖ + L) := by
        refine add_le_add hxs ?_
        rw [dist_eq_norm]
        have h : foot T c + s • T.direction - c = (foot T c - c) + s • T.direction := by abel
        rw [h]
        calc ‖(foot T c - c) + s • T.direction‖ ≤ ‖foot T c - c‖ + ‖s • T.direction‖ :=
              norm_add_le _ _
          _ = ‖foot T c - c‖ + |s| := by rw [norm_smul, T.norm_direction, mul_one, Real.norm_eq_abs]
          _ ≤ ‖foot T c - c‖ + L := by gcongr
    _ ≤ R := by linarith

/-- The thickness profile of the capsule, from T3's `hasThicknesses_segCarrierSet`. -/
theorem hasThicknesses_capsuleAt (T : Tube δ E3) (c : E3) (ρ : NNReal) {L : ℝ} (hL : 0 ≤ L)
    (hL1 : 2 * L ≤ 1) (hρL : (ρ : ℝ) ≤ L) :
    Kakeya.HasThicknesses (capsuleAt T c ρ L) 4 ![4 * L, (ρ : ℝ), (ρ : ℝ)] :=
  hasThicknesses_segCarrierSet (centredTube T c ρ) c hL hL1 hρL

/-- The thickness scale of the capsule is at least `ρ`. -/
theorem le_ethickness_scale_capsuleAt (T : Tube δ E3) (c : E3) (ρ : NNReal) {L : ℝ} (hL : 0 ≤ L) :
    (ρ : ENNReal) ≤ Metric.ethickness.scale ℝ (capsuleAt T c ρ L) :=
  le_ethickness_scale_segCarrierSet (centredTube T c ρ) c (L := L) hL

/-! ### Centred line parameters, the parameter metric, the net and the assignment -/

/-- The centred line parameters of `T` relative to `c`: `(foot T c − c, T.direction)` — the
refined "`(p, d)` with `p ⊥ d`" (l.4778). -/
noncomputable def lineParam (T : Tube δ E3) (c : E3) : E3 × E3 := (foot T c - c, T.direction)

/-- The parameter metric at half-length `L`: `‖Δp‖ + L·‖Δd‖`.  A direction error `‖Δd‖`
contributes at most `L·‖Δd‖` laterally along a capsule of half-length `L`. -/
noncomputable def paramDist (L : ℝ) (a b : E3 × E3) : ℝ := ‖a.1 - b.1‖ + L * ‖a.2 - b.2‖

theorem paramDist_self (L : ℝ) (a : E3 × E3) : paramDist L a a = 0 := by
  simp [paramDist]

theorem paramDist_comm (L : ℝ) (a b : E3 × E3) : paramDist L a b = paramDist L b a := by
  simp only [paramDist, norm_sub_rev]

theorem paramDist_nonneg {L : ℝ} (hL : 0 ≤ L) (a b : E3 × E3) : 0 ≤ paramDist L a b := by
  unfold paramDist; positivity

theorem paramDist_lineParam (T T' : Tube δ E3) (c : E3) (L : ℝ) :
    paramDist L (lineParam T c) (lineParam T' c) =
      ‖foot T c - foot T' c‖ + L * ‖T.direction - T'.direction‖ := by
  simp only [paramDist, lineParam, sub_sub_sub_cancel_right]

/-- **A capsule net** on the family `I`: a maximal `ε`-separated subfamily in the parameter
metric and an assignment of every member of `I` to a net member within `ε` — the refined
canonical cover's net and its surjection `ϖ_c` (l.3705–3707, l.4778–4784).  Net members are
assigned to themselves. -/
structure CapsuleNet {ι : Type*} (I : Finset ι) (T : ι → Tube δ E3) (c : E3) (L ε : ℝ) where
  /-- The net. -/
  net : Finset ι
  net_subset : net ⊆ I
  /-- Distinct net members are `ε`-separated in the parameter metric. -/
  separated : ∀ a ∈ net, ∀ b ∈ net, a ≠ b →
    ε ≤ paramDist L (lineParam (T a) c) (lineParam (T b) c)
  /-- The assignment `ϖ`. -/
  assign : ι → ι
  assign_mem : ∀ i ∈ I, assign i ∈ net
  assign_close : ∀ i ∈ I, paramDist L (lineParam (T i) c) (lineParam (T (assign i)) c) < ε
  assign_self : ∀ ν ∈ net, assign ν = ν

/-- **Existence of a capsule net** — `exists_maximal_separated_finset` in the parameter metric,
with the assignment chosen among the net members within `ε` (maximality) and net members
assigned to themselves (separation). -/
theorem exists_capsuleNet {ι : Type*} (I : Finset ι) (T : ι → Tube δ E3) (c : E3) (L : ℝ)
    {ε : ℝ} (hε : 0 < ε) : Nonempty (CapsuleNet I T c L ε) := by
  classical
  obtain ⟨P, hPI, hsep, hcov⟩ := exists_maximal_separated_finset I
    (fun i j => paramDist L (lineParam (T i) c) (lineParam (T j) c))
    (fun a => by rw [paramDist_self]; exact hε)
    (fun a b => paramDist_comm L _ _)
  have hpick : ∀ i, i ∈ I →
      ∃ w ∈ P, paramDist L (lineParam (T i) c) (lineParam (T w) c) < ε :=
    fun i hi => hcov i hi
  let assign : ι → ι := fun i => if h : i ∈ I then (hpick i h).choose else i
  refine ⟨⟨P, hPI, hsep, assign, ?_, ?_, ?_⟩⟩
  · intro i hi
    simp only [assign, dif_pos hi]
    exact (hpick i hi).choose_spec.1
  · intro i hi
    simp only [assign, dif_pos hi]
    exact (hpick i hi).choose_spec.2
  · intro ν hν
    have hνI : ν ∈ I := hPI hν
    simp only [assign, dif_pos hνI]
    by_contra hne
    have h1 := (hpick ν hνI).choose_spec
    have h2 := hsep ν hν _ h1.1 (Ne.symm hne)
    linarith [h1.2]

namespace CapsuleNet

variable {ι : Type*} {I : Finset ι} {T : ι → Tube δ E3} {c : E3} {L ε : ℝ}

/-- The fibre of a net member: the members of `I` assigned to it (`ϖ_c⁻¹(S)`). -/
noncomputable def fibre [DecidableEq ι] (𝒩 : CapsuleNet I T c L ε) (ν : ι) : Finset ι :=
  I.filter fun i => 𝒩.assign i = ν

theorem fibre_subset [DecidableEq ι] (𝒩 : CapsuleNet I T c L ε) (ν : ι) : 𝒩.fibre ν ⊆ I :=
  Finset.filter_subset _ _

theorem mem_fibre_iff [DecidableEq ι] (𝒩 : CapsuleNet I T c L ε) {i ν : ι} :
    i ∈ 𝒩.fibre ν ↔ i ∈ I ∧ 𝒩.assign i = ν := by
  simp [fibre]

theorem mem_fibre_assign [DecidableEq ι] (𝒩 : CapsuleNet I T c L ε) {i : ι} (hi : i ∈ I) :
    i ∈ 𝒩.fibre (𝒩.assign i) := by
  simp [fibre, hi]

/-- **`parent`**: every member of `I` lies in the fibre of some net member. -/
theorem exists_mem_fibre [DecidableEq ι] (𝒩 : CapsuleNet I T c L ε) {i : ι} (hi : i ∈ I) :
    ∃ ν ∈ 𝒩.net, i ∈ 𝒩.fibre ν :=
  ⟨𝒩.assign i, 𝒩.assign_mem i hi, 𝒩.mem_fibre_assign hi⟩

/-- **`fam_disjoint`**: fibres of distinct net members are disjoint. -/
theorem fibre_disjoint [DecidableEq ι] (𝒩 : CapsuleNet I T c L ε) :
    (𝒩.net : Set ι).Pairwise fun ν μ => Disjoint (𝒩.fibre ν) (𝒩.fibre μ) := by
  intro ν _ μ _ hne
  rw [Finset.disjoint_left]
  intro i hiν hiμ
  rw [mem_fibre_iff] at hiν hiμ
  exact hne (hiν.2.symm.trans hiμ.2)

/-- A net member lies in its own fibre. -/
theorem mem_fibre_self [DecidableEq ι] (𝒩 : CapsuleNet I T c L ε) {ν : ι} (hν : ν ∈ 𝒩.net) :
    ν ∈ 𝒩.fibre ν := by
  rw [mem_fibre_iff]
  exact ⟨𝒩.net_subset hν, 𝒩.assign_self ν hν⟩

theorem close_of_mem_fibre [DecidableEq ι] (𝒩 : CapsuleNet I T c L ε) {i ν : ι}
    (hi : i ∈ 𝒩.fibre ν) :
    ‖foot (T i) c - foot (T ν) c‖ + L * ‖(T i).direction - (T ν).direction‖ < ε := by
  rw [mem_fibre_iff] at hi
  have h := 𝒩.assign_close i hi.1
  rwa [hi.2, paramDist_lineParam] at h

theorem close_of_mem_fibre' [DecidableEq ι] (𝒩 : CapsuleNet I T c L ε) {i ν : ι}
    (hi : i ∈ 𝒩.fibre ν) :
    ‖foot (T ν) c - foot (T i) c‖ + L * ‖(T ν).direction - (T i).direction‖ < ε := by
  have h := 𝒩.close_of_mem_fibre hi
  rwa [norm_sub_rev (foot (T ν) c), norm_sub_rev (T ν).direction]

/-- **`into`**: the part of a fibre member inside `ball c r` lies in the net member's capsule
(radius `≥ δ + ε`, half-length `≥ r + δ`). -/
theorem tube_inter_ball_subset_capsuleAt_of_mem_fibre [DecidableEq ι] (𝒩 : CapsuleNet I T c L ε)
    {i ν : ι} (hi : i ∈ 𝒩.fibre ν) {r : ℝ} {ρ : NNReal} (hL : 0 ≤ L) (hL1 : L ≤ 1 / 2)
    (hr : r + (δ : ℝ) ≤ L) (hρ : (δ : ℝ) + ε ≤ ρ) :
    (T i).carrier ∩ ball c r ⊆ capsuleAt (T ν) c ρ L :=
  tube_inter_ball_subset_capsuleAt_of_close (T i) (T ν) c hL hL1 hr
    (le_of_lt (𝒩.close_of_mem_fibre hi)) hρ

/-- **`segs_core`**: the net member's capsule lies in the `(ρ + ε)`-neighbourhood of every fibre
member's core line. -/
theorem capsuleAt_subset_cthickening_line_of_mem_fibre [DecidableEq ι]
    (𝒩 : CapsuleNet I T c L ε) {i ν : ι} (hi : i ∈ 𝒩.fibre ν) {ρ : NNReal} {C : ℝ}
    (hL : 0 ≤ L) (hL1 : L ≤ 1 / 2) (hC : (ρ : ℝ) + ε ≤ C) :
    capsuleAt (T ν) c ρ L ⊆ cthickening C
      (AffineSubspace.mk' (foot (T i) c) (Submodule.span ℝ {(T i).direction}) : Set E3) :=
  capsuleAt_subset_cthickening_line_of_close (T i) (T ν) c hL hL1
    (le_of_lt (𝒩.close_of_mem_fibre' hi)) hC

end CapsuleNet

/-! ### Non-essentially-distinct capsules: the second lies near the first's core line

The refined family is `A₀`-essentially distinct in the **line-based** sense (l.5381), i.e. its
non-ED degree is bounded (E0).  Here is the geometric heart of that bound for the capsules:
two capsules that are not essentially distinct are, after the homothety of ratio `1/(2L)` about
`c`, two unit tubes of radius `ρ/(2L)` that are not essentially distinct, so by
`Tube.carrier_subset_cthickening_line_of_not_essDistinct` (E0, the existing
`tubeOverlapCoreClose`) the second lies in the `C₃ · ρ/(2L)`-neighbourhood of the first's line;
pulled back, every point of the second capsule is within `C₃ ρ` of the first's core line,
measured by the component orthogonal to its direction. -/

/-- The component of `v` orthogonal to the unit vector `d`. -/
noncomputable def perpComp (d v : E3) : E3 := v - (inner ℝ v d) • d

theorem inner_perpComp (d v : E3) (hd : ‖d‖ = 1) : inner ℝ (perpComp d v) d = 0 := by
  simp only [perpComp, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hd]
  ring

theorem perpComp_add_smul (d v : E3) (hd : ‖d‖ = 1) (s : ℝ) :
    perpComp d (v + s • d) = perpComp d v := by
  simp only [perpComp, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq, hd,
    one_pow, mul_one]
  module

theorem perpComp_smul (d v : E3) (k : ℝ) : perpComp d (k • v) = k • perpComp d v := by
  simp only [perpComp, real_inner_smul_left]
  module

theorem perpComp_sub (d v w : E3) : perpComp d (v - w) = perpComp d v - perpComp d w := by
  simp only [perpComp, inner_sub_left]
  module

/-- The perpendicular component bounds the distance to every point of the line. -/
theorem norm_perpComp_le_dist_line (a d : E3) (hd : ‖d‖ = 1) (x : E3) (t : ℝ) :
    ‖perpComp d (x - a)‖ ≤ dist x (a + t • d) := by
  rw [dist_eq_norm]
  have h : x - (a + t • d) = perpComp d (x - a) + (inner ℝ (x - a) d - t) • d := by
    simp only [perpComp]; module
  rw [h]
  have hperp : inner ℝ (perpComp d (x - a)) d = 0 := inner_perpComp d _ hd
  have hsq : ‖perpComp d (x - a) + (inner ℝ (x - a) d - t) • d‖ ^ 2 =
      ‖perpComp d (x - a)‖ ^ 2 + (inner ℝ (x - a) d - t) ^ 2 := by
    rw [norm_add_sq_real, real_inner_smul_right, hperp, mul_zero, mul_zero, add_zero,
      norm_smul, hd, mul_one, Real.norm_eq_abs, sq_abs]
  have hle : ‖perpComp d (x - a)‖ ^ 2 ≤
      ‖perpComp d (x - a) + (inner ℝ (x - a) d - t) • d‖ ^ 2 := by
    rw [hsq]; nlinarith [sq_nonneg (inner ℝ (x - a) d - t)]
  have := sq_le_sq.mp hle
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] at this

/-- Inside the closed `r`-neighbourhood of the line `t ↦ a + t • d` means: perpendicular
component `≤ r`. -/
theorem norm_perpComp_le_of_mem_cthickening_line {a d : E3} (hd : ‖d‖ = 1) {r : ℝ} (hr : 0 ≤ r)
    {x : E3} (hx : x ∈ cthickening r (Set.range fun t : ℝ ↦ a + t • d)) :
    ‖perpComp d (x - a)‖ ≤ r := by
  rw [Metric.mem_cthickening_iff] at hx
  refine (ENNReal.ofReal_le_ofReal_iff hr).mp (le_trans ?_ hx)
  rw [Metric.le_infEDist]
  rintro y ⟨t, rfl⟩
  rw [edist_dist]
  exact ENNReal.ofReal_le_ofReal (norm_perpComp_le_dist_line a d hd x t)

theorem dist_sub_half_add_half {f d : E3} (hd : ‖d‖ = 1) :
    dist (f - (1 / 2 : ℝ) • d) (f + (1 / 2 : ℝ) • d) = 1 := by
  rw [dist_eq_norm]
  have h : f - (1 / 2 : ℝ) • d - (f + (1 / 2 : ℝ) • d) = -d := by module
  rw [h, norm_neg, hd]

/-- **The rescaled capsule as a unit tube**: the unit `ρ'`-tube on `T`'s line centred at the
homothety image (ratio `k`, centre `c`) of the foot. -/
noncomputable def capsuleUnitTube (T : Tube δ E3) (c : E3) (ρ' : NNReal) (k : ℝ) :
    Tube ρ' E3 :=
  Tube.mk' ρ' (dist_sub_half_add_half (f := AffineMap.homothety c k (foot T c)) T.norm_direction)

theorem capsuleUnitTube_x (T : Tube δ E3) (c : E3) (ρ' : NNReal) (k : ℝ) :
    (capsuleUnitTube T c ρ' k).x =
      AffineMap.homothety c k (foot T c) - (1 / 2 : ℝ) • T.direction := rfl

theorem capsuleUnitTube_y (T : Tube δ E3) (c : E3) (ρ' : NNReal) (k : ℝ) :
    (capsuleUnitTube T c ρ' k).y =
      AffineMap.homothety c k (foot T c) + (1 / 2 : ℝ) • T.direction := rfl

theorem capsuleUnitTube_direction (T : Tube δ E3) (c : E3) (ρ' : NNReal) (k : ℝ) :
    (capsuleUnitTube T c ρ' k).direction = T.direction := by
  simp only [Tube.direction, capsuleUnitTube_x, capsuleUnitTube_y]; module

theorem homothety_sub_smul (c f d : E3) (k s : ℝ) :
    AffineMap.homothety c k (f - s • d) = AffineMap.homothety c k f - (k * s) • d := by
  simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]; module

theorem homothety_add_smul (c f d : E3) (k s : ℝ) :
    AffineMap.homothety c k (f + s • d) = AffineMap.homothety c k f + (k * s) • d := by
  simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]; module

/-- The homothety of ratio `1/(2L)` about `c` maps the capsule onto the unit tube's carrier. -/
theorem image_homothety_capsuleAt (T : Tube δ E3) (c : E3) (ρ : NNReal) {L : ℝ} (hL : 0 < L)
    (hL1 : L ≤ 1 / 2) {ρ' : NNReal} (hρ' : (ρ' : ℝ) = (1 / (2 * L)) * ρ) :
    AffineMap.homothety c (1 / (2 * L)) '' capsuleAt T c ρ L =
      (capsuleUnitTube T c ρ' (1 / (2 * L))).carrier := by
  have hk : (1 / (2 * L)) * L = (1 / 2 : ℝ) := by field_simp
  rw [capsuleAt_eq T c ρ hL1,
    Metric.image_cthickening_homothety c (by positivity) ρ.coe_nonneg, image_segment,
    homothety_sub_smul, homothety_add_smul, hk,
    (capsuleUnitTube T c ρ' (1 / (2 * L))).carrier_eq_cthickening, hρ',
    capsuleUnitTube_x, capsuleUnitTube_y]

/-- **Two capsules that are not essentially distinct: every point of the second is within
`C₃ ρ` of the first's core line** (`C₃ = Kakeya.Tube.tubeOverlapCoreClose.C 3`), in the
perpendicular-component form.  Hypotheses: `0 < ρ ≤ 2L ≤ 1`. -/
theorem norm_perpComp_le_of_not_essDistinct_capsuleAt (T T' : Tube δ E3) (c : E3) (ρ : NNReal)
    {L : ℝ} (hL : 0 < L) (hL1 : L ≤ 1 / 2) (hρ0 : 0 < ρ) (hρL : (ρ : ℝ) ≤ 2 * L)
    (h : ¬ _root_.IsEssentiallyDistinct (capsuleAt T c ρ L) (capsuleAt T' c ρ L))
    {x : E3} (hx : x ∈ capsuleAt T' c ρ L) :
    ‖perpComp T.direction (x - foot T c)‖ ≤ Kakeya.Tube.tubeOverlapCoreClose.C 3 * ρ := by
  set k : ℝ := 1 / (2 * L) with hk
  have hk0 : 0 < k := by positivity
  set ρ' : NNReal := ⟨k * ρ, by positivity⟩ with hρ'def
  have hρ'coe : (ρ' : ℝ) = k * ρ := rfl
  have hρ'0 : 0 < ρ' := by
    rw [← NNReal.coe_pos, hρ'coe]; positivity
  have hρ'1 : ρ' ≤ 1 := by
    rw [← NNReal.coe_le_coe, hρ'coe, NNReal.coe_one, hk, one_div, inv_mul_le_iff₀ (by positivity),
      mul_one]
    exact hρL
  set Φ : E3 ≃ᵃ[ℝ] E3 := AffineEquiv.homothetyUnitsMulHom c (Units.mk0 k hk0.ne') with hΦ
  have hΦapp : (Φ : E3 → E3) = AffineMap.homothety c k := by
    rw [hΦ, AffineEquiv.coe_homothetyUnitsMulHom_apply]
    rfl
  have hV : (Φ : E3 → E3) '' capsuleAt T c ρ L = (capsuleUnitTube T c ρ' k).carrier := by
    rw [hΦapp]; exact image_homothety_capsuleAt T c ρ hL hL1 hρ'coe
  have hV' : (Φ : E3 → E3) '' capsuleAt T' c ρ L = (capsuleUnitTube T' c ρ' k).carrier := by
    rw [hΦapp]; exact image_homothety_capsuleAt T' c ρ hL hL1 hρ'coe
  have hED' : ¬ _root_.IsEssentiallyDistinct (capsuleUnitTube T c ρ' k).carrier
      (capsuleUnitTube T' c ρ' k).carrier := by
    rw [← hV, ← hV']
    intro hed
    exact h ((IsEssentiallyDistinct.image_affineEquiv_iff Φ).mp hed)
  have hsub := _root_.Tube.carrier_subset_cthickening_line_of_not_essDistinct hρ'0 hρ'1
    (capsuleUnitTube T c ρ' k) (capsuleUnitTube T' c ρ' k) hED'
  have hx' : (Φ : E3 → E3) x ∈ (capsuleUnitTube T' c ρ' k).carrier := by
    rw [← hV']; exact ⟨x, hx, rfl⟩
  have hmem := hsub hx'
  rw [finrank_euclideanSpace_fin] at hmem
  have hC0 : 0 ≤ Kakeya.Tube.tubeOverlapCoreClose.C 3 :=
    (lt_trans zero_lt_one (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C 3)).le
  have hperp := norm_perpComp_le_of_mem_cthickening_line
    (capsuleUnitTube T c ρ' k).norm_direction (by positivity) hmem
  rw [capsuleUnitTube_direction] at hperp
  have hdiff : (Φ : E3 → E3) x - (capsuleUnitTube T c ρ' k).x
      = k • (x - foot T c) + (1 / 2 : ℝ) • T.direction := by
    rw [hΦapp, capsuleUnitTube_x]
    simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
    module
  rw [hdiff, perpComp_add_smul _ _ T.norm_direction, perpComp_smul, norm_smul, Real.norm_eq_abs,
    abs_of_pos hk0, hρ'coe] at hperp
  have h2 : k * ‖perpComp T.direction (x - foot T c)‖ ≤
      k * (Kakeya.Tube.tubeOverlapCoreClose.C 3 * ρ) := by
    calc k * ‖perpComp T.direction (x - foot T c)‖
        ≤ Kakeya.Tube.tubeOverlapCoreClose.C 3 * (k * ρ) := hperp
      _ = k * (Kakeya.Tube.tubeOverlapCoreClose.C 3 * ρ) := by ring
  exact le_of_mul_le_mul_left h2 hk0

/-! ### From the perpendicular bounds at the two endpoints to parameter closeness, up to orientation

The two orientations of one line are two parameters `(p, d)` and `(p, −d)`; two capsules on
nearby lines with opposite orientations are not essentially distinct although their parameters
are far apart.  The refined text's "one of two balls" (l.4795–4796) is this case split. -/

/-- Reverse the direction of a line parameter. -/
def flipParam (a : E3 × E3) : E3 × E3 := (a.1, -a.2)

theorem paramDist_lineParam_flip (T T' : Tube δ E3) (c : E3) (L : ℝ) :
    paramDist L (lineParam T c) (flipParam (lineParam T' c)) =
      ‖foot T c - foot T' c‖ + L * ‖T.direction + T'.direction‖ := by
  simp only [paramDist, lineParam, flipParam, sub_sub_sub_cancel_right, sub_neg_eq_add]

theorem perpComp_add (d v w : E3) : perpComp d (v + w) = perpComp d v + perpComp d w := by
  simp only [perpComp, inner_add_left]
  module

/-- Pythagoras for the perpendicular component. -/
theorem norm_perpComp_sq (d v : E3) (hd : ‖d‖ = 1) :
    ‖perpComp d v‖ ^ 2 = ‖v‖ ^ 2 - (inner ℝ v d) ^ 2 := by
  simp only [perpComp]
  rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, hd, mul_one, Real.norm_eq_abs, sq_abs]
  ring

/-- **Two unit vectors with a small mutual perpendicular component are close up to sign.** -/
theorem norm_sub_le_or_norm_add_le_of_perpComp {d d' : E3} (hd : ‖d‖ = 1) (hd' : ‖d'‖ = 1)
    {η : ℝ} (hη : 0 ≤ η) (h : ‖perpComp d d'‖ ≤ η) :
    ‖d' - d‖ ≤ 2 * η ∨ ‖d' + d‖ ≤ 2 * η := by
  have hsq := norm_perpComp_sq d d' hd
  rw [hd'] at hsq
  have hperp2 : ‖perpComp d d'‖ ^ 2 ≤ η ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  have hnn : 0 ≤ ‖perpComp d d'‖ ^ 2 := sq_nonneg _
  have ht1 : (inner ℝ d' d) ^ 2 ≤ 1 := by nlinarith
  have habs : |inner ℝ d' d| ≤ 1 := by
    have := sq_le_sq.mp (by simpa using ht1 : (inner ℝ d' d) ^ 2 ≤ (1 : ℝ) ^ 2)
    simpa using this
  have hab := abs_le.mp habs
  rcases le_or_gt 0 (inner ℝ d' d) with hpos | hneg
  · left
    have h2 : ‖d' - d‖ ^ 2 ≤ (2 * η) ^ 2 := by
      rw [norm_sub_sq_real, hd', hd]
      nlinarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h2
  · right
    have h2 : ‖d' + d‖ ^ 2 ≤ (2 * η) ^ 2 := by
      rw [norm_add_sq_real, hd', hd]
      nlinarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h2

/-- **Position closeness from the perpendicular bound and direction closeness**: with
`p ⊥ d`, `p' ⊥ d'`, `‖perpComp d (p' − p)‖ ≤ β` and `‖d' − d‖ ≤ γ`, `‖p' − p‖ ≤ β + ‖p'‖ γ`. -/
theorem norm_sub_le_of_perpComp_of_dir {d d' p p' : E3} (hd : ‖d‖ = 1)
    (hp : inner ℝ p d = 0) (hp' : inner ℝ p' d' = 0) {β γ : ℝ}
    (hβ : ‖perpComp d (p' - p)‖ ≤ β) (hdir : ‖d' - d‖ ≤ γ) : ‖p' - p‖ ≤ β + ‖p'‖ * γ := by
  have hdecomp : p' - p = perpComp d (p' - p) + (inner ℝ (p' - p) d) • d := by
    simp only [perpComp]; module
  have hin : inner ℝ (p' - p) d = inner ℝ p' (d - d') := by
    rw [inner_sub_left, hp, sub_zero, inner_sub_right, hp', sub_zero]
  have hγ : ‖d - d'‖ ≤ γ := by rw [norm_sub_rev]; exact hdir
  calc ‖p' - p‖ = ‖perpComp d (p' - p) + (inner ℝ (p' - p) d) • d‖ := by rw [← hdecomp]
    _ ≤ ‖perpComp d (p' - p)‖ + ‖(inner ℝ (p' - p) d) • d‖ := norm_add_le _ _
    _ = ‖perpComp d (p' - p)‖ + |inner ℝ (p' - p) d| := by
        rw [norm_smul, hd, mul_one, Real.norm_eq_abs]
    _ ≤ β + ‖p'‖ * γ := by
        refine add_le_add hβ ?_
        rw [hin]
        calc |inner ℝ p' (d - d')| ≤ ‖p'‖ * ‖d - d'‖ := abs_real_inner_le_norm _ _
          _ ≤ ‖p'‖ * γ := by gcongr

/-- The flipped-orientation variant: `‖d' + d‖ ≤ γ`. -/
theorem norm_sub_le_of_perpComp_of_dir' {d d' p p' : E3} (hd : ‖d‖ = 1)
    (hp : inner ℝ p d = 0) (hp' : inner ℝ p' d' = 0) {β γ : ℝ}
    (hβ : ‖perpComp d (p' - p)‖ ≤ β) (hdir : ‖d' + d‖ ≤ γ) : ‖p' - p‖ ≤ β + ‖p'‖ * γ := by
  have hdecomp : p' - p = perpComp d (p' - p) + (inner ℝ (p' - p) d) • d := by
    simp only [perpComp]; module
  have hin : inner ℝ (p' - p) d = inner ℝ p' (d + d') := by
    rw [inner_sub_left, hp, sub_zero, inner_add_right, hp', add_zero]
  have hγ : ‖d + d'‖ ≤ γ := by rw [add_comm]; exact hdir
  calc ‖p' - p‖ = ‖perpComp d (p' - p) + (inner ℝ (p' - p) d) • d‖ := by rw [← hdecomp]
    _ ≤ ‖perpComp d (p' - p)‖ + ‖(inner ℝ (p' - p) d) • d‖ := norm_add_le _ _
    _ = ‖perpComp d (p' - p)‖ + |inner ℝ (p' - p) d| := by
        rw [norm_smul, hd, mul_one, Real.norm_eq_abs]
    _ ≤ β + ‖p'‖ * γ := by
        refine add_le_add hβ ?_
        rw [hin]
        calc |inner ℝ p' (d + d')| ≤ ‖p'‖ * ‖d + d'‖ := abs_real_inner_le_norm _ _
          _ ≤ ‖p'‖ * γ := by gcongr

/-- **Non-essentially-distinct capsules have close parameters, up to orientation**: with
`0 < ρ ≤ 2L ≤ 1` and the second foot within `L` of `c`,
`paramDist L (Π T) (Π T') ≤ 5 C₃ ρ` or `paramDist L (Π T) (flip (Π T')) ≤ 5 C₃ ρ`.
(The two endpoints of the second capsule's core give the direction bound `‖perpComp d d'‖ ≤ C₃ρ/L`
and the position bound `‖perpComp d (f' − a)‖ ≤ C₃ρ`; then `norm_sub_le_or_norm_add_le_of_perpComp`
and `norm_sub_le_of_perpComp_of_dir`.) -/
theorem paramDist_le_or_flip_of_not_essDistinct_capsuleAt (T T' : Tube δ E3) (c : E3)
    (ρ : NNReal) {L : ℝ} (hL : 0 < L) (hL1 : L ≤ 1 / 2) (hρ0 : 0 < ρ) (hρL : (ρ : ℝ) ≤ 2 * L)
    (hfoot' : ‖foot T' c - c‖ ≤ L)
    (h : ¬ _root_.IsEssentiallyDistinct (capsuleAt T c ρ L) (capsuleAt T' c ρ L)) :
    paramDist L (lineParam T c) (lineParam T' c) ≤ 5 * (Kakeya.Tube.tubeOverlapCoreClose.C 3 * ρ) ∨
    paramDist L (lineParam T c) (flipParam (lineParam T' c)) ≤
      5 * (Kakeya.Tube.tubeOverlapCoreClose.C 3 * ρ) := by
  have hC0 : 0 < Kakeya.Tube.tubeOverlapCoreClose.C 3 :=
    lt_trans zero_lt_one (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C 3)
  have hβ0 : 0 ≤ Kakeya.Tube.tubeOverlapCoreClose.C 3 * ρ := by positivity
  have hd := T.norm_direction
  have hd' := T'.norm_direction
  -- the two endpoints of the second capsuleAt's core lie in it
  have hePlus : foot T' c + L • T'.direction ∈ capsuleAt T' c ρ L :=
    mem_capsuleAt_of_dist_le T' c ρ hL.le hL1 (by rw [abs_of_pos hL])
      (by rw [dist_self]; exact ρ.coe_nonneg)
  have heMinus : foot T' c + (-L) • T'.direction ∈ capsuleAt T' c ρ L :=
    mem_capsuleAt_of_dist_le T' c ρ hL.le hL1 (by rw [abs_neg, abs_of_pos hL])
      (by rw [dist_self]; exact ρ.coe_nonneg)
  have hbPlus := norm_perpComp_le_of_not_essDistinct_capsuleAt T T' c ρ hL hL1 hρ0 hρL h hePlus
  have hbMinus := norm_perpComp_le_of_not_essDistinct_capsuleAt T T' c ρ hL hL1 hρ0 hρL h heMinus
  -- direction
  have hdirperp : ‖perpComp T.direction T'.direction‖ ≤
      Kakeya.Tube.tubeOverlapCoreClose.C 3 * ρ / L := by
    have h1 : perpComp T.direction T'.direction = (1 / (2 * L)) •
        (perpComp T.direction (foot T' c + L • T'.direction - foot T c) -
          perpComp T.direction (foot T' c + (-L) • T'.direction - foot T c)) := by
      rw [← perpComp_sub]
      have h2 : (foot T' c + L • T'.direction - foot T c) -
          (foot T' c + (-L) • T'.direction - foot T c) = (2 * L) • T'.direction := by module
      rw [h2, perpComp_smul, smul_smul]
      have h3 : (1 / (2 * L)) * (2 * L) = (1 : ℝ) := by field_simp
      rw [h3, one_smul]
    rw [h1, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    calc (1 / (2 * L)) * ‖perpComp T.direction (foot T' c + L • T'.direction - foot T c) -
          perpComp T.direction (foot T' c + (-L) • T'.direction - foot T c)‖
        ≤ (1 / (2 * L)) * (Kakeya.Tube.tubeOverlapCoreClose.C 3 * ρ +
            Kakeya.Tube.tubeOverlapCoreClose.C 3 * ρ) := by
          gcongr
          exact (norm_sub_le _ _).trans (add_le_add hbPlus hbMinus)
      _ = Kakeya.Tube.tubeOverlapCoreClose.C 3 * ρ / L := by field_simp; ring
  -- position
  have hposperp : ‖perpComp T.direction (foot T' c - foot T c)‖ ≤
      Kakeya.Tube.tubeOverlapCoreClose.C 3 * ρ := by
    have h1 : perpComp T.direction (foot T' c - foot T c) = (1 / 2 : ℝ) •
        (perpComp T.direction (foot T' c + L • T'.direction - foot T c) +
          perpComp T.direction (foot T' c + (-L) • T'.direction - foot T c)) := by
      rw [← perpComp_add]
      have h2 : (foot T' c + L • T'.direction - foot T c) +
          (foot T' c + (-L) • T'.direction - foot T c) = (2 : ℝ) • (foot T' c - foot T c) := by
        module
      rw [h2, perpComp_smul, smul_smul]
      norm_num
    rw [h1, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    calc (1 / 2 : ℝ) * ‖perpComp T.direction (foot T' c + L • T'.direction - foot T c) +
          perpComp T.direction (foot T' c + (-L) • T'.direction - foot T c)‖
        ≤ (1 / 2 : ℝ) * (Kakeya.Tube.tubeOverlapCoreClose.C 3 * ρ +
            Kakeya.Tube.tubeOverlapCoreClose.C 3 * ρ) := by
          gcongr
          exact (norm_add_le _ _).trans (add_le_add hbPlus hbMinus)
      _ = Kakeya.Tube.tubeOverlapCoreClose.C 3 * ρ := by ring
  -- the feet relative to `c`
  have hp : inner ℝ (foot T c - c) T.direction = 0 := inner_foot_sub_direction T c
  have hp' : inner ℝ (foot T' c - c) T'.direction = 0 := inner_foot_sub_direction T' c
  have hff : (foot T' c - c) - (foot T c - c) = foot T' c - foot T c := by abel
  have hη0 : 0 ≤ Kakeya.Tube.tubeOverlapCoreClose.C 3 * ρ / L := by positivity
  have hLη : L * (2 * (Kakeya.Tube.tubeOverlapCoreClose.C 3 * ρ / L)) =
      2 * (Kakeya.Tube.tubeOverlapCoreClose.C 3 * ρ) := by field_simp
  rcases norm_sub_le_or_norm_add_le_of_perpComp hd hd' hη0 hdirperp with hdir | hdir
  · left
    rw [paramDist_lineParam]
    have hpos := norm_sub_le_of_perpComp_of_dir hd hp hp' (hff ▸ hposperp) hdir
    rw [hff] at hpos
    rw [norm_sub_rev (foot T c), norm_sub_rev T.direction]
    have hp'L : ‖foot T' c - c‖ * (2 * (Kakeya.Tube.tubeOverlapCoreClose.C 3 * ρ / L)) ≤
        2 * (Kakeya.Tube.tubeOverlapCoreClose.C 3 * ρ) := by
      rw [← hLη]; gcongr
    calc ‖foot T' c - foot T c‖ + L * ‖T'.direction - T.direction‖
        ≤ (Kakeya.Tube.tubeOverlapCoreClose.C 3 * ρ +
            ‖foot T' c - c‖ * (2 * (Kakeya.Tube.tubeOverlapCoreClose.C 3 * ρ / L))) +
          L * (2 * (Kakeya.Tube.tubeOverlapCoreClose.C 3 * ρ / L)) :=
          add_le_add hpos (mul_le_mul_of_nonneg_left hdir hL.le)
      _ ≤ (Kakeya.Tube.tubeOverlapCoreClose.C 3 * ρ +
            2 * (Kakeya.Tube.tubeOverlapCoreClose.C 3 * ρ)) +
          2 * (Kakeya.Tube.tubeOverlapCoreClose.C 3 * ρ) := by
          rw [hLη]; gcongr
      _ = 5 * (Kakeya.Tube.tubeOverlapCoreClose.C 3 * ρ) := by ring
  · right
    rw [paramDist_lineParam_flip]
    have hpos := norm_sub_le_of_perpComp_of_dir' hd hp hp' (hff ▸ hposperp) hdir
    rw [hff] at hpos
    rw [norm_sub_rev (foot T c), add_comm T.direction]
    have hp'L : ‖foot T' c - c‖ * (2 * (Kakeya.Tube.tubeOverlapCoreClose.C 3 * ρ / L)) ≤
        2 * (Kakeya.Tube.tubeOverlapCoreClose.C 3 * ρ) := by
      rw [← hLη]; gcongr
    calc ‖foot T' c - foot T c‖ + L * ‖T'.direction + T.direction‖
        ≤ (Kakeya.Tube.tubeOverlapCoreClose.C 3 * ρ +
            ‖foot T' c - c‖ * (2 * (Kakeya.Tube.tubeOverlapCoreClose.C 3 * ρ / L))) +
          L * (2 * (Kakeya.Tube.tubeOverlapCoreClose.C 3 * ρ / L)) :=
          add_le_add hpos (mul_le_mul_of_nonneg_left hdir hL.le)
      _ ≤ (Kakeya.Tube.tubeOverlapCoreClose.C 3 * ρ +
            2 * (Kakeya.Tube.tubeOverlapCoreClose.C 3 * ρ)) +
          2 * (Kakeya.Tube.tubeOverlapCoreClose.C 3 * ρ) := by
          rw [hLη]; gcongr
      _ = 5 * (Kakeya.Tube.tubeOverlapCoreClose.C 3 * ρ) := by ring

/-! ### Packing in `E3 × E3`, and the non-ED degree of a capsule net

The net is `ε`-separated in the parameter metric; non-essentially-distinct capsules have parameters
within `5 C₃ ρ` of each other up to orientation
(`paramDist_le_or_flip_of_not_essDistinct_capsuleAt`).
Carrying the parameters `(p, L•d)` into `E3 × E3` with the sup norm, the net points are
`ε/2`-separated and the offending ones lie in a ball of radius `5 C₃ ρ`; a volume count gives at
most `(20 C₃ ρ / ε + 1)⁶` per orientation.  This is the refined `propvnslocalization`'s
"`Φ_c(𝕋_c)` is `A₀`-essentially distinct" (l.5381) in the tree's degree form, with the tree's
two-tube constant `C₃ ≈ 101` in place of the refined `5` (E0 §1.3). -/

section Packing

/-- The unit-ball volume of `E3`, `√π³ / Γ(5/2)`, in the spelling of
`EuclideanSpace.volume_ball`. -/
noncomputable def ballConst3 : ℝ :=
  Real.sqrt Real.pi ^ Fintype.card (Fin 3) / Real.Gamma ((Fintype.card (Fin 3) : ℝ) / 2 + 1)

theorem ballConst3_pos : 0 < ballConst3 := by
  unfold ballConst3
  exact div_pos (pow_pos (Real.sqrt_pos.mpr Real.pi_pos) _)
    (Real.Gamma_pos_of_pos (by positivity))

theorem volume_ball_prod (y : E3 × E3) {r : ℝ} (hr : 0 ≤ r) :
    volume (ball y r) = ENNReal.ofReal
      ((r ^ Fintype.card (Fin 3) * ballConst3) * (r ^ Fintype.card (Fin 3) * ballConst3)) := by
  obtain ⟨y1, y2⟩ := y
  have hw := ballConst3_pos
  have h0 : 0 ≤ r ^ Fintype.card (Fin 3) * ballConst3 := mul_nonneg (pow_nonneg hr _) hw.le
  rw [← ball_prod_same, Measure.volume_eq_prod, Measure.prod_prod, EuclideanSpace.volume_ball,
    EuclideanSpace.volume_ball, ENNReal.ofReal_mul h0, ENNReal.ofReal_mul (pow_nonneg hr _),
    ENNReal.ofReal_pow hr]
  rfl

theorem volume_closedBall_prod (y : E3 × E3) {r : ℝ} (hr : 0 ≤ r) :
    volume (closedBall y r) = ENNReal.ofReal
      ((r ^ Fintype.card (Fin 3) * ballConst3) * (r ^ Fintype.card (Fin 3) * ballConst3)) := by
  obtain ⟨y1, y2⟩ := y
  have hw := ballConst3_pos
  have h0 : 0 ≤ r ^ Fintype.card (Fin 3) * ballConst3 := mul_nonneg (pow_nonneg hr _) hw.le
  rw [← closedBall_prod_same, Measure.volume_eq_prod, Measure.prod_prod,
    EuclideanSpace.volume_closedBall, EuclideanSpace.volume_closedBall, ENNReal.ofReal_mul h0,
    ENNReal.ofReal_mul (pow_nonneg hr _), ENNReal.ofReal_pow hr]
  rfl

/-- **Packing in `E3 × E3` (sup norm)**: an `s`-separated finite family inside `closedBall x R`
has at most `(2R/s + 1)⁶` members. -/
theorem card_le_of_separated_prod {ι : Type*} (G : Finset ι) (Ψ : ι → E3 × E3) {x : E3 × E3}
    {R s : ℝ} (hs : 0 < s) (hR : 0 ≤ R) (hGA : ∀ a ∈ G, Ψ a ∈ closedBall x R)
    (hsep : ∀ a ∈ G, ∀ b ∈ G, a ≠ b → s ≤ dist (Ψ a) (Ψ b)) :
    (G.card : ℝ) ≤ (2 * R / s + 1) ^ (2 * Fintype.card (Fin 3)) := by
  classical
  have hdisj : (G : Set ι).PairwiseDisjoint fun a => ball (Ψ a) (s / 2) := by
    intro a ha b hb hab
    rw [Function.onFun, Set.disjoint_left]
    intro z hza hzb
    rw [mem_ball] at hza hzb
    have h1 := dist_triangle_left (Ψ a) (Ψ b) z
    linarith [hsep a ha b hb hab]
  have hsub : (⋃ a ∈ G, ball (Ψ a) (s / 2)) ⊆ closedBall x (R + s / 2) := by
    intro z hz
    rw [Set.mem_iUnion₂] at hz
    obtain ⟨a, ha, hza⟩ := hz
    rw [mem_ball] at hza
    rw [mem_closedBall]
    calc dist z x ≤ dist z (Ψ a) + dist (Ψ a) x := dist_triangle _ _ _
      _ ≤ s / 2 + R := add_le_add hza.le (hGA a ha)
      _ = R + s / 2 := add_comm _ _
  have hvol : ∑ a ∈ G, volume (ball (Ψ a) (s / 2)) ≤ volume (closedBall x (R + s / 2)) := by
    rw [← measure_biUnion_finset hdisj (fun a _ => measurableSet_ball)]
    exact measure_mono hsub
  have hw := ballConst3_pos
  have hs2 : 0 ≤ s / 2 := by positivity
  have hRs : 0 ≤ R + s / 2 := by positivity
  simp_rw [volume_ball_prod _ hs2] at hvol
  rw [Finset.sum_const, nsmul_eq_mul, volume_closedBall_prod _ hRs, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _)] at hvol
  have hA : 0 ≤ ((s / 2) ^ Fintype.card (Fin 3) * ballConst3) *
      ((s / 2) ^ Fintype.card (Fin 3) * ballConst3) := by positivity
  have hB : 0 ≤ ((R + s / 2) ^ Fintype.card (Fin 3) * ballConst3) *
      ((R + s / 2) ^ Fintype.card (Fin 3) * ballConst3) := by positivity
  have hreal := (ENNReal.ofReal_le_ofReal_iff hB).mp hvol
  -- cancel the ball constant
  have hw2 : 0 < ballConst3 * ballConst3 := by positivity
  have hkey : (G.card : ℝ) * ((s / 2) ^ Fintype.card (Fin 3)) ^ 2 ≤
      ((R + s / 2) ^ Fintype.card (Fin 3)) ^ 2 := by
    have h := hreal
    have hrew : (G.card : ℝ) * ((s / 2) ^ Fintype.card (Fin 3) * ballConst3 *
        ((s / 2) ^ Fintype.card (Fin 3) * ballConst3)) =
        (G.card : ℝ) * ((s / 2) ^ Fintype.card (Fin 3)) ^ 2 * (ballConst3 * ballConst3) := by ring
    have hrew' : (R + s / 2) ^ Fintype.card (Fin 3) * ballConst3 *
        ((R + s / 2) ^ Fintype.card (Fin 3) * ballConst3) =
        ((R + s / 2) ^ Fintype.card (Fin 3)) ^ 2 * (ballConst3 * ballConst3) := by ring
    rw [hrew, hrew'] at h
    exact le_of_mul_le_mul_right h hw2
  have hspos : 0 < ((s / 2) ^ Fintype.card (Fin 3)) ^ 2 := by positivity
  rw [← le_div_iff₀ hspos] at hkey
  calc (G.card : ℝ) ≤ ((R + s / 2) ^ Fintype.card (Fin 3)) ^ 2 /
        ((s / 2) ^ Fintype.card (Fin 3)) ^ 2 := hkey
    _ = ((R + s / 2) / (s / 2)) ^ (2 * Fintype.card (Fin 3)) := by
        rw [← div_pow, ← div_pow, ← pow_mul, mul_comm]
    _ = (2 * R / s + 1) ^ (2 * Fintype.card (Fin 3)) := by
        congr 1
        field_simp

end Packing

/-- The parameters of `T` at half-length `L`, as a point of `E3 × E3` (sup norm). -/
noncomputable def paramPoint (T : Tube δ E3) (c : E3) (L : ℝ) : E3 × E3 :=
  (foot T c - c, L • T.direction)

/-- The same with the orientation reversed. -/
noncomputable def paramPointFlip (T : Tube δ E3) (c : E3) (L : ℝ) : E3 × E3 :=
  (foot T c - c, -(L • T.direction))

theorem dist_paramPoint_le (T T' : Tube δ E3) (c : E3) {L : ℝ} (hL : 0 ≤ L) :
    dist (paramPoint T c L) (paramPoint T' c L) ≤
      paramDist L (lineParam T c) (lineParam T' c) := by
  rw [Prod.dist_eq, paramDist_lineParam]
  simp only [paramPoint, dist_eq_norm, sub_sub_sub_cancel_right, ← smul_sub, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg hL]
  exact max_le_add_of_nonneg (norm_nonneg _) (by positivity)

theorem paramDist_le_two_mul_dist_paramPoint (T T' : Tube δ E3) (c : E3) {L : ℝ} (hL : 0 ≤ L) :
    paramDist L (lineParam T c) (lineParam T' c) ≤
      2 * dist (paramPoint T c L) (paramPoint T' c L) := by
  rw [Prod.dist_eq, paramDist_lineParam]
  simp only [paramPoint, dist_eq_norm, sub_sub_sub_cancel_right, ← smul_sub, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg hL]
  linarith [le_max_left ‖foot T c - foot T' c‖ (L * ‖T.direction - T'.direction‖),
    le_max_right ‖foot T c - foot T' c‖ (L * ‖T.direction - T'.direction‖)]

theorem dist_paramPoint_paramPointFlip_le (T T' : Tube δ E3) (c : E3) {L : ℝ} (hL : 0 ≤ L) :
    dist (paramPoint T c L) (paramPointFlip T' c L) ≤
      paramDist L (lineParam T c) (flipParam (lineParam T' c)) := by
  rw [Prod.dist_eq, paramDist_lineParam_flip]
  simp only [paramPoint, paramPointFlip, dist_eq_norm, sub_sub_sub_cancel_right, sub_neg_eq_add,
    ← smul_add, norm_smul, Real.norm_eq_abs, abs_of_nonneg hL]
  exact max_le_add_of_nonneg (norm_nonneg _) (by positivity)

theorem dist_paramPointFlip (T T' : Tube δ E3) (c : E3) (L : ℝ) :
    dist (paramPointFlip T c L) (paramPointFlip T' c L) =
      dist (paramPoint T c L) (paramPoint T' c L) := by
  simp only [Prod.dist_eq, paramPoint, paramPointFlip, dist_neg_neg]

namespace CapsuleNet

variable {ι : Type*} {I : Finset ι} {T : ι → Tube δ E3} {c : E3} {L ε : ℝ}

/-- **The non-ED degree of the capsule family of a net is bounded by an absolute constant.**
For a capsule net at spacing `ε > 0`, capsules of radius `ρ` and half-length `L` with
`0 < ρ ≤ 2L ≤ 1`, and all feet within `L` of `c`, every net member has at most
`2 · (20 C₃ ρ / ε + 1)⁶` other net members whose capsule is not essentially distinct from its
own.  At the producer's values `ρ = 2δ`, `ε = δ` this is `2 · (40 C₃ + 1)⁶`, a `δ`-free number —
the value `edMultiplicityConstant` is to carry (E0, provisional). -/
theorem edDegree_capsuleAt_le (𝒩 : CapsuleNet I T c L ε) (hε : 0 < ε) (hL : 0 < L)
    (hL1 : L ≤ 1 / 2) {ρ : NNReal} (hρ0 : 0 < ρ) (hρL : (ρ : ℝ) ≤ 2 * L)
    (hfeet : ∀ i ∈ I, ‖foot (T i) c - c‖ ≤ L) (ν : ι) :
    (edDegree 𝒩.net (fun μ => capsuleAt (T μ) c ρ L) ν : ℝ) ≤
      2 * (2 * (5 * (Kakeya.Tube.tubeOverlapCoreClose.C 3 * ρ)) / (ε / 2) + 1) ^
        (2 * Fintype.card (Fin 3)) := by
  classical
  have hC0 : 0 < Kakeya.Tube.tubeOverlapCoreClose.C 3 :=
    lt_trans zero_lt_one (Kakeya.Tube.tubeOverlapCoreClose.one_lt_C 3)
  set R : ℝ := 5 * (Kakeya.Tube.tubeOverlapCoreClose.C 3 * ρ) with hR
  have hR0 : 0 ≤ R := by positivity
  set G₁ : Finset ι := 𝒩.net.filter fun μ =>
    paramDist L (lineParam (T ν) c) (lineParam (T μ) c) ≤ R with hG₁
  set G₂ : Finset ι := 𝒩.net.filter fun μ =>
    paramDist L (lineParam (T ν) c) (flipParam (lineParam (T μ) c)) ≤ R with hG₂
  have hsub : {μ ∈ (𝒩.net : Set ι) | μ ≠ ν ∧
      ¬ _root_.IsEssentiallyDistinct (capsuleAt (T ν) c ρ L) (capsuleAt (T μ) c ρ L)} ⊆
        ((G₁ ∪ G₂ : Finset ι) : Set ι) := by
    rintro μ ⟨hμ, -, hn⟩
    rw [Finset.coe_union, Set.mem_union, Finset.mem_coe, Finset.mem_coe, hG₁, hG₂,
      Finset.mem_filter, Finset.mem_filter]
    rcases paramDist_le_or_flip_of_not_essDistinct_capsuleAt (T ν) (T μ) c ρ hL hL1 hρ0 hρL
      (hfeet μ (𝒩.net_subset hμ)) hn with h | h
    · exact Or.inl ⟨hμ, h⟩
    · exact Or.inr ⟨hμ, h⟩
  have hdeg : edDegree 𝒩.net (fun μ => capsuleAt (T μ) c ρ L) ν ≤ G₁.card + G₂.card := by
    unfold edDegree
    calc {μ ∈ (𝒩.net : Set ι) | μ ≠ ν ∧
          ¬ _root_.IsEssentiallyDistinct (capsuleAt (T ν) c ρ L) (capsuleAt (T μ) c ρ L)}.ncard
        ≤ ((G₁ ∪ G₂ : Finset ι) : Set ι).ncard :=
          Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      _ = (G₁ ∪ G₂).card := Set.ncard_coe_finset _
      _ ≤ G₁.card + G₂.card := Finset.card_union_le _ _
  have hsε : 0 < ε / 2 := by positivity
  have h1 : (G₁.card : ℝ) ≤ (2 * R / (ε / 2) + 1) ^ (2 * Fintype.card (Fin 3)) := by
    refine card_le_of_separated_prod G₁ (fun μ => paramPoint (T μ) c L)
      (x := paramPoint (T ν) c L) hsε hR0 ?_ ?_
    · intro μ hμ
      rw [hG₁, Finset.mem_filter] at hμ
      rw [mem_closedBall, dist_comm]
      exact (dist_paramPoint_le (T ν) (T μ) c hL.le).trans hμ.2
    · intro a ha b hb hab
      rw [hG₁, Finset.mem_filter] at ha hb
      have hs := 𝒩.separated a ha.1 b hb.1 hab
      have h2 := paramDist_le_two_mul_dist_paramPoint (T a) (T b) c hL.le
      linarith
  have h2 : (G₂.card : ℝ) ≤ (2 * R / (ε / 2) + 1) ^ (2 * Fintype.card (Fin 3)) := by
    refine card_le_of_separated_prod G₂ (fun μ => paramPointFlip (T μ) c L)
      (x := paramPoint (T ν) c L) hsε hR0 ?_ ?_
    · intro μ hμ
      rw [hG₂, Finset.mem_filter] at hμ
      rw [mem_closedBall, dist_comm]
      exact (dist_paramPoint_paramPointFlip_le (T ν) (T μ) c hL.le).trans hμ.2
    · intro a ha b hb hab
      rw [hG₂, Finset.mem_filter] at ha hb
      have hs := 𝒩.separated a ha.1 b hb.1 hab
      have h2 := paramDist_le_two_mul_dist_paramPoint (T a) (T b) c hL.le
      rw [dist_paramPointFlip]
      linarith
  calc (edDegree 𝒩.net (fun μ => capsuleAt (T μ) c ρ L) ν : ℝ)
      ≤ (G₁.card : ℝ) + G₂.card := by exact_mod_cast hdeg
    _ ≤ (2 * R / (ε / 2) + 1) ^ (2 * Fintype.card (Fin 3)) +
        (2 * R / (ε / 2) + 1) ^ (2 * Fintype.card (Fin 3)) := add_le_add h1 h2
    _ = 2 * (2 * (5 * (Kakeya.Tube.tubeOverlapCoreClose.C 3 * ρ)) / (ε / 2) + 1) ^
        (2 * Fintype.card (Fin 3)) := by rw [hR]; ring

end CapsuleNet

end Kakeya.VeryNotSticky

namespace Kakeya

/-- **A thickness profile survives a termwise comparable change of the target profile**: if
`t' k ≤ K₁ t k` and `t k ≤ K₁ t' k` for every `k`, then `HasThicknesses K C t` gives
`HasThicknesses K (C * K₁) t'`.  Used to read the capsule profile `![4L, ρ, ρ]` at the
`BallDataCore` profile `![r₁, δ, δ]`. -/
theorem HasThicknesses.of_profile_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {K : Set E} {C K₁ : NNReal} {t t' : Fin n → ℝ} (h : HasThicknesses K C t)
    (hC : 0 < C) (hK₁ : 1 ≤ K₁)
    (ht : ∀ k, t' k ≤ (K₁ : ℝ) * t k ∧ t k ≤ (K₁ : ℝ) * t' k) :
    HasThicknesses K (C * K₁) t' := by
  intro k
  obtain ⟨hlo, hhi⟩ := h k
  obtain ⟨h1, h2⟩ := ht k
  have hCr : (0 : ℝ) < (C : ℝ) := by exact_mod_cast hC
  have hK1r : (1 : ℝ) ≤ (K₁ : ℝ) := by exact_mod_cast hK₁
  have hK1pos : (0 : ℝ) < (K₁ : ℝ) := lt_of_lt_of_le zero_lt_one hK1r
  have hCK : ((C * K₁ : NNReal) : ℝ) = (C : ℝ) * (K₁ : ℝ) := by push_cast; ring
  constructor
  · rw [hCK]
    calc ((C : ℝ) * (K₁ : ℝ))⁻¹ * t' k ≤ ((C : ℝ) * (K₁ : ℝ))⁻¹ * ((K₁ : ℝ) * t k) := by
          gcongr
      _ = (C : ℝ)⁻¹ * t k := by field_simp
      _ ≤ Metric.thickness ℝ K (k : ℕ) := hlo
  · rw [hCK]
    calc Metric.thickness ℝ K (k : ℕ) ≤ (C : ℝ) * t k := hhi
      _ ≤ (C : ℝ) * ((K₁ : ℝ) * t' k) := by gcongr
      _ = (C : ℝ) * (K₁ : ℝ) * t' k := by ring

end Kakeya

end
