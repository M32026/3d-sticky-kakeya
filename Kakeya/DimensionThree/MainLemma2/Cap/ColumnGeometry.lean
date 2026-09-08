/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Cap.NarrowMass
public import Kakeya.Tube.Param
public import Mathlib.MeasureTheory.Function.Floor

/-!
# The geometric columns of the Cap Lemma: the A4/A5 seam

Band item A4 (`Cap/NarrowMass.lean`) localises a cap to a *column* through an abstract
pigeonhole: `Kakeya.CapBroadNarrow.mult_cap_le_max_columns` takes **any** family of pairwise
disjoint measurable sets `A c` covering the shades, with a per-tube incidence bound as the
caller's data. Band item A5 (`Cap/Rescale.lean`) rescales a *geometric* column: its
`Kakeya.CapRescale.IsCapColumn` hypothesis asks for a transverse bound on the tube
**midpoints** relative to a base point. Nothing connected the two, and the band plan lists the
connection as nobody's deliverable. This file is that connection.

## What is produced

Fix a unit vector `p` and a transverse frame `e₁, e₂` (`IsTransverseFrame`, which exists
whenever `finrank ℝ E = 3` — `exists_isTransverseFrame`). The *columns* are the fibres of

`columnIndex e₁ e₂ θ x = (⌊⟪e₁, x⟫ / (3θ/4)⌋, ⌊⟪e₂, x⟫ / (3θ/4)⌋)`,

i.e. the half-open squares of side `columnSide θ = 3θ/4` in the two transverse coordinates,
extruded along the `p`-axis. Being fibres of a function they are **automatically** pairwise
disjoint and they cover *everything*; the four facts A4 needs are

* measurability — `measurableSet_columnSet`;
* pairwise disjointness — `pairwiseDisjoint_columnSet`;
* covering of the unit ball by the finite index box — `subset_iUnion_columnSet_of_ball`;
* the per-tube incidence count `K = 9` — `card_filter_columnSub_le`.

and the geometric bridge is `norm_perpAxis_midpoint_sub_columnRef_le`: if the shade of a cap
tube meets a column, its midpoint is transversally within `2θ` of that column's base point.

## The two constants, and the hypothesis that forces each

Write `s = columnSide θ` and `ρ = θ/2 + δ` for the transverse radius of a cap tube's carrier
about its own midpoint (`norm_perpAxis_sub_midpoint_le`: a tilt of `θ` over half a unit core
gives `θ/2`, the thickness gives `δ`).

* **The incidence count is `K = 9 = 3²`**, three values per transverse coordinate times the
  two transverse dimensions of `ℝ³`. Three per coordinate needs `ρ ≤ s`, i.e.
  `θ/2 + δ ≤ 3θ/4`, i.e. **`4δ ≤ θ`** — the hypothesis `hδθ` of `card_filter_columnSub_le`,
  and the only thing that forces the count. At `ρ = 2s` four values occur per coordinate and
  the count degrades to `25`; `floor_count_needs_radius_le_side` is the compiled refutation of
  the three-value statement at that radius, so the hypothesis is not decoration.
* **The transverse bound is `2θ`**, from `ρ + (3/2)s ≤ 2θ`: the midpoint is within `ρ` of any
  carrier point transversally, and two points of one column are within `(3/2)s` of each other
  transversally (`3/2` is the rational surrogate for the diagonal `√2` of the square). At
  `s = 3θ/4` this reads `θ/2 + δ + 9θ/8 ≤ 2θ`, i.e. `8δ ≤ 3θ` — the hypothesis of
  `norm_perpAxis_midpoint_sub_columnRef_le`, strictly weaker than the count's `4δ ≤ θ`.

**The side `s = 3θ/4` is pinned, not chosen.** The count forces `s ≥ ρ` and the bridge forces
`ρ + (3/2)s ≤ 2θ`; at the worst admissible `δ = θ/4` these read `3θ/4 ≤ s ≤ 5θ/6`, and
`columnSide_window` records that window as a compiled inequality. A narrower column breaks the
count; a wider one breaks the `2θ` bound, and at four times the cap radius it breaks it
irreparably (`column_side_four_theta_is_refuted`).

## Units: which `4θ` is which

`θ` here is the **cap radius**, equal to A5's reference-tube thickness, i.e. `4 θ_ang` in the
net-separation units . Nothing in this file revisits the cap radius:
that it is `4 θ_ang` and not the plan's `3 θ_ang` was measured by A2 (the sign branch of
`Tube.sphere_sep_net`) and confirmed independently by A3 and A4, and the hypothesis `hdir`
below is literally cap membership at that radius. What this file does revisit is the **column
side**, a different quantity:

* the side proved here is `3θ/4 = 3 θ_ang` — three quarters of the cap radius;
*  asks for a column "of side `4θ`" with `θ` its own reference thickness,
  i.e. `16 θ_ang`. That is **refuted**: `column_side_four_theta_is_refuted` exhibits two points
  of one such column whose transverse separation exceeds `2 · 2θ + 2ρ`, the most two carrier
  points can be separated when both midpoints lie transversally within `2θ` of one base point;
* the plan's own side `4 θ_ang` (= `θ`, the cap radius) is **not** refuted — no pair
  obstruction arises there — but it exceeds the window `[3θ/4, 5θ/6]` that the base-point route
  of `norm_perpAxis_midpoint_sub_columnRef_le` admits, because that route measures from a point
  *of* the column (forced: A5's clause needs `‖b‖ ≤ 1`, which a column centre need not satisfy)
  rather than from its centre. So `4 θ_ang` is outside this proof's reach, not shown false.

## Why `2θ` and not something else

`2θ` is not free: it is exactly the constant in A5's column clause, with `θ` the *cap radius*
`4 θ_ang` (equal to A5's reference-tube thickness). The conclusion of
`exists_column_localisation` is written in the elementary form
`‖(m - b) - ⟪p, m - b⟫ • p‖ ≤ 2 * θ`, which is literally A5's `hcolumn` hypothesis, so this
file does **not** import A5 and A5's file need not change.

## Relation to A4's constants

`exists_column_localisation` calls `Kakeya.CapBroadNarrow.mult_cap_le_max_columns` at `K = 9`,
so its fullness threshold is A4's `λ / (2K) = λ / 18` and its multiplicity factor is A4's `2`.
The `72 = 8 · 9`  is the product of A4's narrow factor `8` with the
`9` proved here; the `9` is confirmed, the `72` is not needed, and A4's better factor `2`
stands.
-/

@[expose] public section

open MeasureTheory Metric Set Module

namespace Kakeya.CapColumn

open Kakeya.CapBroadNarrow

/-! ## 1. The transverse component of a vector relative to a unit axis

Nothing in this section needs a frame, a measure, or finite dimensionality. -/

section PerpAxis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p : E}

/-- The component of `x` orthogonal to the unit axis `p`. -/
noncomputable def perpAxis (p x : E) : E := x - (inner ℝ p x : ℝ) • p

theorem perpAxis_def (p x : E) : perpAxis p x = x - (inner ℝ p x : ℝ) • p := rfl

theorem perpAxis_add (p x y : E) : perpAxis p (x + y) = perpAxis p x + perpAxis p y := by
  simp only [perpAxis, inner_add_right]; module

theorem perpAxis_sub (p x y : E) : perpAxis p (x - y) = perpAxis p x - perpAxis p y := by
  simp only [perpAxis, inner_sub_right]; module

theorem perpAxis_smul (p : E) (a : ℝ) (x : E) : perpAxis p (a • x) = a • perpAxis p x := by
  simp only [perpAxis, real_inner_smul_right]; module

theorem perpAxis_self (hp : ‖p‖ = 1) : perpAxis p p = 0 := by
  simp only [perpAxis, real_inner_self_eq_norm_sq, hp]
  simp

/-- Orthogonal projection is a contraction. -/
theorem norm_perpAxis_le (hp : ‖p‖ = 1) (x : E) : ‖perpAxis p x‖ ≤ ‖x‖ := by
  have hsq : ‖perpAxis p x‖ ^ 2 = ‖x‖ ^ 2 - (inner ℝ p x : ℝ) ^ 2 := by
    rw [perpAxis_def, norm_sub_sq_real, norm_smul, real_inner_smul_right, real_inner_comm x p]
    simp only [hp, Real.norm_eq_abs, sq_abs, mul_one]
    ring
  nlinarith [norm_nonneg (perpAxis p x), norm_nonneg x, sq_nonneg (inner ℝ p x : ℝ)]

/-- **A `Kakeya.CapBroadNarrow.dirDist` bound on a direction bounds its transverse component,
with no factor `2`.** `perpAxis p` kills both `p` and `-p`, so the sign ambiguity in `dirDist`
(A2's sign-blind angular distance) costs nothing here.
(This is the axis-only form of the same observation A5 records for its own reference-tube
projection.) -/
theorem norm_perpAxis_le_dirDist (hp : ‖p‖ = 1) (v : E) : ‖perpAxis p v‖ ≤ dirDist v p := by
  have h1 : perpAxis p (v - p) = perpAxis p v := by
    rw [perpAxis_sub, perpAxis_self hp, sub_zero]
  have h2 : perpAxis p (v + p) = perpAxis p v := by
    rw [perpAxis_add, perpAxis_self hp, add_zero]
  refine le_min ?_ ?_
  · rw [← h1]; exact norm_perpAxis_le hp _
  · rw [← h2]; exact norm_perpAxis_le hp _

/-- A coordinate orthogonal to the axis reads only the transverse component. -/
theorem abs_inner_le_norm_perpAxis {e : E} (he : ‖e‖ = 1) (hpe : (inner ℝ p e : ℝ) = 0)
    (x : E) : |(inner ℝ e x : ℝ)| ≤ ‖perpAxis p x‖ := by
  have hep : (inner ℝ e p : ℝ) = 0 := by rw [real_inner_comm]; exact hpe
  have : (inner ℝ e x : ℝ) = inner ℝ e (perpAxis p x) := by
    rw [perpAxis_def, inner_sub_right, real_inner_smul_right, hep]
    ring
  rw [this]
  calc |(inner ℝ e (perpAxis p x) : ℝ)| ≤ ‖e‖ * ‖perpAxis p x‖ := abs_real_inner_le_norm _ _
    _ = ‖perpAxis p x‖ := by rw [he, one_mul]

/-- A transverse coordinate of a direction is bounded by its sign-blind angular distance to
the axis — again with no factor `2`. -/
theorem abs_inner_le_dirDist {e : E} (he : ‖e‖ = 1) (hpe : (inner ℝ p e : ℝ) = 0) (v : E) :
    |(inner ℝ e v : ℝ)| ≤ dirDist v p := by
  have hep : (inner ℝ e p : ℝ) = 0 := by rw [real_inner_comm]; exact hpe
  refine le_min ?_ ?_
  · have h : (inner ℝ e v : ℝ) = inner ℝ e (v - p) := by rw [inner_sub_right, hep, sub_zero]
    rw [h]
    calc |(inner ℝ e (v - p) : ℝ)| ≤ ‖e‖ * ‖v - p‖ := abs_real_inner_le_norm _ _
      _ = ‖v - p‖ := by rw [he, one_mul]
  · have h : (inner ℝ e v : ℝ) = inner ℝ e (v + p) := by rw [inner_add_right, hep, add_zero]
    rw [h]
    calc |(inner ℝ e (v + p) : ℝ)| ≤ ‖e‖ * ‖v + p‖ := abs_real_inner_le_norm _ _
      _ = ‖v + p‖ := by rw [he, one_mul]

end PerpAxis

/-! ## 2. The transverse frame -/

section Frame

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p e₁ e₂ : E}

/-- A unit axis `p` together with an orthonormal pair spanning its orthogonal complement,
presented as a resolution of the identity. In `ℝ³` this is exactly an orthonormal basis whose
first vector is `p`; the `decomp` clause is the only completeness fact used downstream. -/
structure IsTransverseFrame (p e₁ e₂ : E) : Prop where
  /-- The axis is a unit vector. -/
  norm_axis : ‖p‖ = 1
  /-- The first transverse vector is a unit vector. -/
  norm_fst : ‖e₁‖ = 1
  /-- The second transverse vector is a unit vector. -/
  norm_snd : ‖e₂‖ = 1
  /-- The first transverse vector is orthogonal to the axis. -/
  inner_axis_fst : (inner ℝ p e₁ : ℝ) = 0
  /-- The second transverse vector is orthogonal to the axis. -/
  inner_axis_snd : (inner ℝ p e₂ : ℝ) = 0
  /-- The two transverse vectors are orthogonal to each other. -/
  inner_fst_snd : (inner ℝ e₁ e₂ : ℝ) = 0
  /-- Completeness: every vector is the sum of its three coordinates. -/
  decomp : ∀ x : E, x = (inner ℝ p x : ℝ) • p + (inner ℝ e₁ x : ℝ) • e₁ + (inner ℝ e₂ x : ℝ) • e₂

/-- The transverse component resolved in the frame. -/
theorem perpAxis_eq (hf : IsTransverseFrame p e₁ e₂) (x : E) :
    perpAxis p x = (inner ℝ e₁ x : ℝ) • e₁ + (inner ℝ e₂ x : ℝ) • e₂ := by
  have hd := hf.decomp x
  rw [perpAxis]
  nth_rewrite 1 [hd]
  module

/-- Pythagoras in the transverse plane. -/
theorem norm_perpAxis_sq (hf : IsTransverseFrame p e₁ e₂) (x : E) :
    ‖perpAxis p x‖ ^ 2 = (inner ℝ e₁ x : ℝ) ^ 2 + (inner ℝ e₂ x : ℝ) ^ 2 := by
  rw [perpAxis_eq hf, norm_add_sq_real, real_inner_smul_left, real_inner_smul_right,
    hf.inner_fst_snd, norm_smul, norm_smul, hf.norm_fst, hf.norm_snd]
  simp [Real.norm_eq_abs, sq_abs]

/-- A bound on both transverse coordinates bounds the transverse component. The factor `3/2`
is the rational surrogate for the diagonal `√2` of a square, kept rational so that no
`Real.sqrt` enters any downstream constant. -/
theorem norm_perpAxis_le_of_abs_inner_le (hf : IsTransverseFrame p e₁ e₂) {x : E} {a : ℝ}
    (h₁ : |(inner ℝ e₁ x : ℝ)| ≤ a) (h₂ : |(inner ℝ e₂ x : ℝ)| ≤ a) :
    ‖perpAxis p x‖ ≤ 3 / 2 * a := by
  have ha : 0 ≤ a := le_trans (abs_nonneg _) h₁
  have hsq := norm_perpAxis_sq hf x
  have hb₁ : (inner ℝ e₁ x : ℝ) ^ 2 ≤ a ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h₁ 2
  have hb₂ : (inner ℝ e₂ x : ℝ) ^ 2 ≤ a ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h₂ 2
  nlinarith [norm_nonneg (perpAxis p x)]

variable [FiniteDimensional ℝ E]

/-- **A transverse frame exists in `ℝ³` about every unit vector.** This is what keeps
`IsTransverseFrame` from being a hypothesis no call site can supply. -/
theorem exists_isTransverseFrame (hn : finrank ℝ E = 3) {p : E} (hp : ‖p‖ = 1) :
    ∃ e₁ e₂ : E, IsTransverseFrame p e₁ e₂ := by
  have hcard : finrank ℝ E = Fintype.card (Fin 3) := by simp [hn]
  have horth : Orthonormal ℝ (({0} : Set (Fin 3)).restrict (fun _ : Fin 3 => p)) := by
    constructor
    · intro i; exact hp
    · intro i j hij
      exact absurd (Subtype.ext
        ((Set.eq_of_mem_singleton i.2).trans (Set.eq_of_mem_singleton j.2).symm)) hij
  obtain ⟨b, hb⟩ := horth.exists_orthonormalBasis_extension_of_card_eq hcard
  have hb0 : b 0 = p := hb 0 rfl
  subst hb0
  refine ⟨b 1, b 2, hp, b.orthonormal.1 1, b.orthonormal.1 2,
    b.orthonormal.2 (by decide : (0 : Fin 3) ≠ 1),
    b.orthonormal.2 (by decide : (0 : Fin 3) ≠ 2),
    b.orthonormal.2 (by decide : (1 : Fin 3) ≠ 2), ?_⟩
  intro x
  have h := b.sum_repr x
  rw [Fin.sum_univ_three] at h
  simp only [b.repr_apply_apply] at h
  exact h.symm

end Frame

/-! ## 3. The transverse footprint of a cap tube -/

section Footprint

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {δ : NNReal} {θ : ℝ} {p : E}

/-- **The transverse radius of a cap tube about its own midpoint is `θ/2 + δ`**: a tilt of at
most `θ` from the axis, over half a unit core, contributes `θ/2`, and the thickness
contributes `δ`. This is 's "a tube of `𝕋_p` stays within transverse
distance `3θ/2 + δ_k` of the line through its centre parallel to `p`" in its sharp form: the
tilt term is `θ/2`, not `3θ/2`. -/
theorem norm_perpAxis_sub_midpoint_le (hp : ‖p‖ = 1) (T : Tube δ E)
    (hdir : dirDist T.direction p ≤ θ) {z : E} (hz : z ∈ T.carrier) :
    ‖perpAxis p (z - T.midpoint)‖ ≤ θ / 2 + (δ : ℝ) := by
  obtain ⟨t, ht, hnorm⟩ := T.exists_param_of_mem_carrier hz
  have hsplit : perpAxis p (z - T.midpoint)
      = t • perpAxis p T.direction + perpAxis p (z - T.midpoint - t • T.direction) := by
    rw [← perpAxis_smul, ← perpAxis_add]
    congr 1
    abel
  have hdirθ : ‖perpAxis p T.direction‖ ≤ θ :=
    le_trans (norm_perpAxis_le_dirDist hp _) hdir
  have hoff : ‖perpAxis p (z - T.midpoint - t • T.direction)‖ ≤ (δ : ℝ) :=
    le_trans (norm_perpAxis_le hp _) hnorm
  have habs : |t| ≤ 1 / 2 := ht
  calc ‖perpAxis p (z - T.midpoint)‖
      = ‖t • perpAxis p T.direction + perpAxis p (z - T.midpoint - t • T.direction)‖ := by
        rw [hsplit]
    _ ≤ ‖t • perpAxis p T.direction‖
          + ‖perpAxis p (z - T.midpoint - t • T.direction)‖ := norm_add_le _ _
    _ = |t| * ‖perpAxis p T.direction‖
          + ‖perpAxis p (z - T.midpoint - t • T.direction)‖ := by
        rw [norm_smul, Real.norm_eq_abs]
    _ ≤ 1 / 2 * θ + (δ : ℝ) := by
        have hθ0 : 0 ≤ θ := le_trans (dirDist_nonneg _ _) hdir
        have := mul_le_mul habs hdirθ (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1/2)
        linarith
    _ = θ / 2 + (δ : ℝ) := by ring

end Footprint

/-! ## 3b. Floor arithmetic

Two facts about `⌊·/s⌋`, both used with `s = columnSide θ`: same floor forces closeness, and
a radius-`s` interval meets at most three floor classes. -/

section FloorArith

/-- If two reals have the same floor after division by `s > 0` they differ by less than `s`. -/
theorem abs_sub_lt_of_floor_div_eq {s a b : ℝ} (hs : 0 < s) (h : ⌊a / s⌋ = ⌊b / s⌋) :
    |a - b| < s := by
  have ha1 : ((⌊a / s⌋ : ℤ) : ℝ) ≤ a / s := Int.floor_le _
  have ha2 : a / s < (⌊a / s⌋ : ℤ) + 1 := Int.lt_floor_add_one _
  have hb1 : ((⌊b / s⌋ : ℤ) : ℝ) ≤ b / s := Int.floor_le _
  have hb2 : b / s < (⌊b / s⌋ : ℤ) + 1 := Int.lt_floor_add_one _
  rw [h] at ha1 ha2
  rw [abs_sub_lt_iff]
  refine ⟨?_, ?_⟩
  · have key : (a - b) / s < 1 := by rw [sub_div]; linarith
    have := (div_lt_one hs).mp key
    linarith
  · have key : (b - a) / s < 1 := by rw [sub_div]; linarith
    have := (div_lt_one hs).mp key
    linarith

/-- **Three floor classes per coordinate.** A closed interval of radius `s` about `m` meets
only the floor classes `⌊m/s⌋ - 1, ⌊m/s⌋, ⌊m/s⌋ + 1`. This is the source of the `3` in
`K = 9 = 3²`, and it is exactly where the hypothesis "radius at most the side" is spent. -/
theorem floor_div_mem_Icc {s m t : ℝ} (hs : 0 < s) (h : |t - m| ≤ s) :
    ⌊t / s⌋ ∈ Finset.Icc (⌊m / s⌋ - 1) (⌊m / s⌋ + 1) := by
  rw [abs_sub_le_iff] at h
  obtain ⟨h1, h2⟩ := h
  have hup : t / s ≤ m / s + 1 := by
    rw [div_le_iff₀ hs, add_mul, div_mul_cancel₀ _ (ne_of_gt hs), one_mul]
    linarith
  have hlow : m / s - 1 ≤ t / s := by
    rw [sub_le_iff_le_add, div_add' _ _ _ (ne_of_gt hs), div_le_div_iff_of_pos_right hs]
    linarith
  have hupf : ⌊t / s⌋ ≤ ⌊m / s⌋ + 1 := by
    have := Int.floor_le_floor hup
    simpa using this
  have hlowf : ⌊m / s⌋ - 1 ≤ ⌊t / s⌋ := by
    have := Int.floor_le_floor hlow
    simpa using this
  exact Finset.mem_Icc.mpr ⟨hlowf, hupf⟩

/-- **Negative control for the count.** Three floor classes per coordinate is *not* free: at
radius `2s` about `m` the interval already meets five, so the hypothesis `ρ ≤ s` — i.e.
`4δ ≤ θ` at `s = columnSide θ` — is doing the work, not decorating the statement. -/
theorem floor_count_needs_radius_le_side :
    ∃ (s m t : ℝ), 0 < s ∧ |t - m| ≤ 2 * s ∧
      ⌊t / s⌋ ∉ Finset.Icc (⌊m / s⌋ - 1) (⌊m / s⌋ + 1) := by
  refine ⟨1, 0, 2, by norm_num, by norm_num, ?_⟩
  norm_num

end FloorArith

/-! ## 4. The columns

The columns are the fibres of a `ℤ × ℤ`-valued index map, which is what makes pairwise
disjointness and covering free and measurability a two-line argument. -/

section Columns

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {θ : ℝ} {p e₁ e₂ : E}

/-- The side of a column, `3θ/4`. See the module docstring for why this value is pinned
between the incidence count and the transverse bound. -/
noncomputable def columnSide (θ : ℝ) : ℝ := 3 / 4 * θ

theorem columnSide_pos (hθ : 0 < θ) : 0 < columnSide θ := by
  rw [columnSide]; linarith

/-- **The admissible window for the column side**, at the worst admissible thickness
`δ = θ/4`: the incidence count needs `ρ ≤ s` and the transverse bound needs
`ρ + (3/2)s ≤ 2θ`, where `ρ = θ/2 + δ`. Both endpoints are attained, and `columnSide θ` is
the lower one. -/
theorem columnSide_window (hθ : 0 < θ) :
    3 / 4 * θ ≤ columnSide θ ∧ columnSide θ ≤ 5 / 6 * θ ∧
      (θ / 2 + θ / 4) + 3 / 2 * columnSide θ ≤ 2 * θ := by
  rw [columnSide]; refine ⟨le_refl _, by linarith, by linarith⟩

/-- The transverse index of a point: the pair of floors of its two transverse coordinates in
units of the column side. -/
noncomputable def columnIndex (e₁ e₂ : E) (θ : ℝ) (x : E) : ℤ × ℤ :=
  (⌊(inner ℝ e₁ x : ℝ) / columnSide θ⌋, ⌊(inner ℝ e₂ x : ℝ) / columnSide θ⌋)

/-- **A column**: the fibre of `columnIndex` over `c`. Geometrically the half-open square of
side `columnSide θ` in the transverse coordinates, extruded along the `p`-axis. -/
noncomputable def columnSet (e₁ e₂ : E) (θ : ℝ) (c : ℤ × ℤ) : Set E :=
  columnIndex e₁ e₂ θ ⁻¹' {c}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem mem_columnSet {c : ℤ × ℤ} {x : E} :
    x ∈ columnSet e₁ e₂ θ c ↔ columnIndex e₁ e₂ θ x = c := Iff.rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem mem_columnSet_self (x : E) : x ∈ columnSet e₁ e₂ θ (columnIndex e₁ e₂ θ x) := rfl

omit [FiniteDimensional ℝ E] in
theorem measurable_columnIndex : Measurable (columnIndex e₁ e₂ θ) := by
  refine Measurable.prodMk ?_ ?_ <;>
    exact Measurable.floor (by fun_prop)

omit [FiniteDimensional ℝ E] in
theorem measurableSet_columnSet (c : ℤ × ℤ) : MeasurableSet (columnSet e₁ e₂ θ c) :=
  measurable_columnIndex (measurableSet_singleton c)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **The columns are pairwise disjoint** — they are fibres of a function. -/
theorem pairwiseDisjoint_columnSet :
    Pairwise (Function.onFun Disjoint (columnSet e₁ e₂ θ)) := by
  intro c c' hcc'
  refine Set.disjoint_left.mpr fun x hx hx' => hcc' ?_
  rw [← mem_columnSet.mp hx, ← mem_columnSet.mp hx']

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Two points of one column differ by less than the side in each transverse coordinate. -/
theorem abs_inner_sub_lt_of_mem_columnSet (hθ : 0 < θ) {c : ℤ × ℤ} {x y : E}
    (hx : x ∈ columnSet e₁ e₂ θ c) (hy : y ∈ columnSet e₁ e₂ θ c) :
    |(inner ℝ e₁ x : ℝ) - inner ℝ e₁ y| < columnSide θ ∧
      |(inner ℝ e₂ x : ℝ) - inner ℝ e₂ y| < columnSide θ := by
  have hs := columnSide_pos (θ := θ) hθ
  have hidx : columnIndex e₁ e₂ θ x = columnIndex e₁ e₂ θ y := by
    rw [mem_columnSet.mp hx, mem_columnSet.mp hy]
  have h1 : (⌊(inner ℝ e₁ x : ℝ) / columnSide θ⌋ : ℤ) = ⌊(inner ℝ e₁ y : ℝ) / columnSide θ⌋ := by
    have := congrArg Prod.fst hidx
    simpa [columnIndex] using this
  have h2 : (⌊(inner ℝ e₂ x : ℝ) / columnSide θ⌋ : ℤ) = ⌊(inner ℝ e₂ y : ℝ) / columnSide θ⌋ := by
    have := congrArg Prod.snd hidx
    simpa [columnIndex] using this
  constructor
  · exact abs_sub_lt_of_floor_div_eq hs h1
  · exact abs_sub_lt_of_floor_div_eq hs h2

end Columns

/-! ## 5. The finite index box, and the covering of the unit ball -/

section Box

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {θ : ℝ} {p e₁ e₂ : E}

/-- A floor class of a coordinate of a point of the unit ball lies in `[-⌈1/s⌉, ⌈1/s⌉]`. -/
theorem floor_div_mem_Icc_of_abs_le {s a : ℝ} (hs : 0 < s) (h : |a| ≤ 1) :
    ⌊a / s⌋ ∈ Finset.Icc (-⌈1 / s⌉) (⌈(1 : ℝ) / s⌉) := by
  rw [abs_le] at h
  refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
  · have hle : -(1 / s) ≤ a / s := by
      rw [neg_div', div_le_div_iff_of_pos_right hs]
      linarith
    have := Int.floor_le_floor hle
    rwa [Int.floor_neg] at this
  · have hle : a / s ≤ 1 / s := by
      rw [div_le_div_iff_of_pos_right hs]; linarith
    have h2 : (1 : ℝ) / s ≤ ((⌈(1 : ℝ) / s⌉ : ℤ) : ℝ) := Int.le_ceil _
    have := Int.floor_le_floor (hle.trans h2)
    simpa using this

/-- The radius of the finite box of columns that covers the unit ball. -/
noncomputable def columnRadius (θ : ℝ) : ℤ := ⌈(1 : ℝ) / columnSide θ⌉

/-- The finite set of columns that covers the unit ball. -/
noncomputable def columnBox (θ : ℝ) : Finset (ℤ × ℤ) :=
  Finset.Icc (-columnRadius θ, -columnRadius θ) (columnRadius θ, columnRadius θ)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem columnIndex_mem_columnBox (hf : IsTransverseFrame p e₁ e₂) (hθ : 0 < θ) {x : E}
    (hx : ‖x‖ ≤ 1) : columnIndex e₁ e₂ θ x ∈ columnBox θ := by
  have hs := columnSide_pos (θ := θ) hθ
  have key : ∀ e : E, ‖e‖ = 1 → |(inner ℝ e x : ℝ)| ≤ 1 := by
    intro e he
    calc |(inner ℝ e x : ℝ)| ≤ ‖e‖ * ‖x‖ := abs_real_inner_le_norm _ _
      _ ≤ 1 := by rw [he, one_mul]; exact hx
  have h₁ := floor_div_mem_Icc_of_abs_le (s := columnSide θ) hs (key e₁ hf.norm_fst)
  have h₂ := floor_div_mem_Icc_of_abs_le (s := columnSide θ) hs (key e₂ hf.norm_snd)
  rw [Finset.mem_Icc] at h₁ h₂
  simp only [columnBox, Finset.mem_Icc, Prod.le_def, columnIndex, columnRadius]
  exact ⟨⟨h₁.1, h₂.1⟩, ⟨h₁.2, h₂.2⟩⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **The columns of the box cover the unit ball.** This is A4's `hcover`, and it is a genuine
positive statement: every point of `B̄(0,1)` lies in a column of the finite index box. -/
theorem subset_iUnion_columnSet_of_ball (hf : IsTransverseFrame p e₁ e₂) (hθ : 0 < θ) {Y : Set E}
    (hY : Y ⊆ closedBall (0 : E) 1) : Y ⊆ ⋃ c ∈ columnBox θ, columnSet e₁ e₂ θ c := by
  intro x hx
  have hxb : ‖x‖ ≤ 1 := by simpa using hY hx
  exact Set.mem_biUnion (columnIndex_mem_columnBox hf hθ hxb) (mem_columnSet_self x)

/-! ## 6. The base point of a column

A5's column clause is stated relative to a base point `b` with `‖b‖ ≤ 1`, so the base point
cannot be the geometric centre of the column (which may leave the unit ball). It is instead a
point of the column *inside* the unit ball, chosen once and for all; every column that a shade
of the family meets has one, because shades lie in the unit ball. -/

open Classical in
/-- The base point of a column: a point of the column inside the unit ball when there is one,
and `0` otherwise. Total by construction, so `norm_columnRef_le_one` needs no hypothesis. -/
noncomputable def columnRef (e₁ e₂ : E) (θ : ℝ) (c : ℤ × ℤ) : E :=
  if h : (columnSet e₁ e₂ θ c ∩ closedBall (0 : E) 1).Nonempty then h.choose else 0

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem norm_columnRef_le_one (c : ℤ × ℤ) : ‖columnRef e₁ e₂ θ c‖ ≤ 1 := by
  classical
  rw [columnRef]
  split_ifs with h
  · simpa using h.choose_spec.2
  · simp

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem columnRef_mem_columnSet {c : ℤ × ℤ}
    (h : (columnSet e₁ e₂ θ c ∩ closedBall (0 : E) 1).Nonempty) :
    columnRef e₁ e₂ θ c ∈ columnSet e₁ e₂ θ c := by
  classical
  rw [columnRef, dif_pos h]
  exact h.choose_spec.1

end Box

/-! ## 7. The bridge: a shade meeting a column pins the midpoint transversally -/

section Bridge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {δ : NNReal} {θ : ℝ} {p e₁ e₂ : E}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Two points of one column are transversally within `(3/2) · columnSide θ` of each other. -/
theorem norm_perpAxis_sub_le_of_mem_columnSet (hf : IsTransverseFrame p e₁ e₂) (hθ : 0 < θ)
    {c : ℤ × ℤ} {x y : E} (hx : x ∈ columnSet e₁ e₂ θ c) (hy : y ∈ columnSet e₁ e₂ θ c) :
    ‖perpAxis p (x - y)‖ ≤ 3 / 2 * columnSide θ := by
  obtain ⟨h₁, h₂⟩ := abs_inner_sub_lt_of_mem_columnSet hθ hx hy
  refine norm_perpAxis_le_of_abs_inner_le hf ?_ ?_
  · rw [inner_sub_right]; exact le_of_lt h₁
  · rw [inner_sub_right]; exact le_of_lt h₂

omit [BorelSpace E] in
/-- **THE A4/A5 SEAM.** If the shade of a cap tube meets a column, the tube's midpoint is
transversally within `2θ` of that column's base point — which is exactly the `column` clause of
A5's `Kakeya.CapRescale.IsCapColumn`, written in the elementary form A5's producer consumes.

The `2θ` decomposes as `(θ/2 + δ) + (3/2)(3θ/4)`: the midpoint is transversally within
`θ/2 + δ` of any point of the carrier (`norm_perpAxis_sub_midpoint_le`), and the meeting point
and the base point share a column. The hypothesis `8δ ≤ 3θ` is exactly what makes the sum fit
inside `2θ` and is used for nothing else. -/
theorem norm_perpAxis_midpoint_sub_columnRef_le (hf : IsTransverseFrame p e₁ e₂) (hθ : 0 < θ)
    (hδθ : 8 * (δ : ℝ) ≤ 3 * θ) {T : ShadedTube δ E} (hdir : dirDist T.direction p ≤ θ)
    (hcar : T.carrier ⊆ closedBall (0 : E) 1) {c : ℤ × ℤ}
    (hne : (T.shade ∩ columnSet e₁ e₂ θ c).Nonempty) :
    ‖(T.midpoint - columnRef e₁ e₂ θ c)
        - (inner ℝ p (T.midpoint - columnRef e₁ e₂ θ c) : ℝ) • p‖ ≤ 2 * θ := by
  obtain ⟨x, hxs, hxc⟩ := hne
  have hxcar : x ∈ T.carrier := T.shade_subset hxs
  have hxball : x ∈ closedBall (0 : E) 1 := hcar hxcar
  have hnonempty : (columnSet e₁ e₂ θ c ∩ closedBall (0 : E) 1).Nonempty := ⟨x, hxc, hxball⟩
  have hbc : columnRef e₁ e₂ θ c ∈ columnSet e₁ e₂ θ c := columnRef_mem_columnSet hnonempty
  have hmid : ‖perpAxis p (T.midpoint - x)‖ ≤ θ / 2 + (δ : ℝ) := by
    have h := norm_perpAxis_sub_midpoint_le (θ := θ) hf.norm_axis T.toTube hdir hxcar
    have hneg : perpAxis p (T.midpoint - x) = -perpAxis p (x - T.midpoint) := by
      rw [perpAxis_sub, perpAxis_sub]
      abel
    rw [hneg, norm_neg]
    exact h
  have hcol : ‖perpAxis p (x - columnRef e₁ e₂ θ c)‖ ≤ 3 / 2 * columnSide θ :=
    norm_perpAxis_sub_le_of_mem_columnSet hf hθ hxc hbc
  have hsplit : perpAxis p (T.midpoint - columnRef e₁ e₂ θ c)
      = perpAxis p (T.midpoint - x) + perpAxis p (x - columnRef e₁ e₂ θ c) := by
    rw [← perpAxis_add]
    congr 1
    abel
  rw [← perpAxis_def]
  calc ‖perpAxis p (T.midpoint - columnRef e₁ e₂ θ c)‖
      ≤ ‖perpAxis p (T.midpoint - x)‖ + ‖perpAxis p (x - columnRef e₁ e₂ θ c)‖ := by
        rw [hsplit]; exact norm_add_le _ _
    _ ≤ (θ / 2 + (δ : ℝ)) + 3 / 2 * columnSide θ := add_le_add hmid hcol
    _ ≤ 2 * θ := by rw [columnSide]; linarith

end Bridge

/-! ## 8. The subfamilies, and the incidence count `K = 9` -/

section Incidence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*} {δ : NNReal} {θ : ℝ} {p e₁ e₂ : E}

open Classical in
/-- The subfamily attached to a column: the members of `u` whose shade meets it. Defined as
the *largest* legal choice, which is what makes A4's `hsupp` hold by definition and the
incidence count as small as it can be. -/
noncomputable def columnSub (e₁ e₂ : E) (θ : ℝ) (u : Finset ι) (T : ι → ShadedTube δ E)
    (c : ℤ × ℤ) : Finset ι :=
  u.filter fun i => ((T i).shade ∩ columnSet e₁ e₂ θ c).Nonempty

omit [BorelSpace E] in
theorem mem_columnSub {u : Finset ι} {T : ι → ShadedTube δ E} {c : ℤ × ℤ} {i : ι} :
    i ∈ columnSub e₁ e₂ θ u T c ↔
      i ∈ u ∧ ((T i).shade ∩ columnSet e₁ e₂ θ c).Nonempty := by
  classical
  rw [columnSub, Finset.mem_filter]

omit [BorelSpace E] in
theorem columnSub_subset (u : Finset ι) (T : ι → ShadedTube δ E) (c : ℤ × ℤ) :
    columnSub e₁ e₂ θ u T c ⊆ u := fun _ hi => (mem_columnSub.mp hi).1

omit [BorelSpace E] in
/-- **The incidence count: a cap tube meets at most `9` columns.**

`9 = 3²`: three floor classes per transverse coordinate (`floor_div_mem_Icc`), squared over the
two transverse dimensions of `ℝ³`. The hypothesis that forces it is `hδθ : 4δ ≤ θ`, and it is
forced through exactly one inequality — the transverse radius `θ/2 + δ` of the carrier about
the midpoint must not exceed the column side `3θ/4`. `floor_count_needs_radius_le_side`
refutes the three-class statement once that fails, so this is not a count that holds for
trivial reasons.

This is precisely A4's `hcount` at `K = 9`, the `9` 's `72 = 8 · 9`. -/
theorem card_filter_columnSub_le (hf : IsTransverseFrame p e₁ e₂) (hθ : 0 < θ)
    (hδθ : 4 * (δ : ℝ) ≤ θ) (u : Finset ι) (T : ι → ShadedTube δ E) {i : ι}
    (hdir : dirDist (T i).direction p ≤ θ) :
    ((columnBox θ).filter fun c => i ∈ columnSub e₁ e₂ θ u T c).card ≤ 9 := by
  have hs := columnSide_pos (θ := θ) hθ
  set m₁ : ℝ := inner ℝ e₁ (T i).midpoint with hm₁
  set m₂ : ℝ := inner ℝ e₂ (T i).midpoint with hm₂
  set n₁ : ℤ := ⌊m₁ / columnSide θ⌋ with hn₁
  set n₂ : ℤ := ⌊m₂ / columnSide θ⌋ with hn₂
  have hsub : ((columnBox θ).filter fun c => i ∈ columnSub e₁ e₂ θ u T c)
      ⊆ Finset.Icc ((n₁ - 1, n₂ - 1) : ℤ × ℤ) (n₁ + 1, n₂ + 1) := by
    intro c hc
    obtain ⟨-, hci⟩ := Finset.mem_filter.mp hc
    obtain ⟨x, hxs, hxc⟩ := (mem_columnSub.mp hci).2
    have hxcar : x ∈ (T i).carrier := (T i).shade_subset hxs
    have hrad : ‖perpAxis p (x - (T i).midpoint)‖ ≤ columnSide θ := by
      have h := norm_perpAxis_sub_midpoint_le (θ := θ) hf.norm_axis (T i).toTube hdir hxcar
      have : θ / 2 + (δ : ℝ) ≤ columnSide θ := by rw [columnSide]; linarith
      exact h.trans this
    have hc₁ : |(inner ℝ e₁ x : ℝ) - m₁| ≤ columnSide θ := by
      have := abs_inner_le_norm_perpAxis (p := p) hf.norm_fst hf.inner_axis_fst
        (x - (T i).midpoint)
      rw [inner_sub_right] at this
      exact this.trans hrad
    have hc₂ : |(inner ℝ e₂ x : ℝ) - m₂| ≤ columnSide θ := by
      have := abs_inner_le_norm_perpAxis (p := p) hf.norm_snd hf.inner_axis_snd
        (x - (T i).midpoint)
      rw [inner_sub_right] at this
      exact this.trans hrad
    have h₁ := floor_div_mem_Icc hs hc₁
    have h₂ := floor_div_mem_Icc hs hc₂
    rw [Finset.mem_Icc] at h₁ h₂
    have hcx : c = columnIndex e₁ e₂ θ x := (mem_columnSet.mp hxc).symm
    subst hcx
    simp only [Finset.mem_Icc, Prod.le_def, columnIndex]
    exact ⟨⟨h₁.1, h₂.1⟩, ⟨h₁.2, h₂.2⟩⟩
  have h3 : ∀ n : ℤ, (Finset.Icc (n - 1) (n + 1)).card = 3 := by
    intro n; rw [Int.card_Icc]; omega
  have hcard : (Finset.Icc ((n₁ - 1, n₂ - 1) : ℤ × ℤ) (n₁ + 1, n₂ + 1)).card = 9 := by
    simp [Finset.card_Icc_prod, h3]
  exact (Finset.card_le_card hsub).trans (le_of_eq hcard)

/-- **Negative control: the incidence count is not sign-blind slack.** Without the cap
hypothesis `hdir` there is no bound at all — a tube transverse to `p` crosses arbitrarily many
columns — and without `hδθ` the three-class step fails (`floor_count_needs_radius_le_side`).
The statement recorded here is the arithmetic core: at transverse radius `2 · columnSide θ` a
carrier already meets five classes in one coordinate, hence up to `25` columns, so `9` is not
available from the hypotheses with `4δ ≤ θ` removed. -/
theorem incidence_nine_needs_thickness_bound (hθ : 0 < θ) :
    ∃ (m t : ℝ), |t - m| ≤ 2 * columnSide θ ∧
      ⌊t / columnSide θ⌋ ∉ Finset.Icc (⌊m / columnSide θ⌋ - 1) (⌊m / columnSide θ⌋ + 1) := by
  have hs := columnSide_pos (θ := θ) hθ
  refine ⟨0, 2 * columnSide θ, ?_, ?_⟩
  · rw [sub_zero, abs_of_nonneg (by positivity)]
  · have h1 : (2 : ℝ) * columnSide θ / columnSide θ = 2 := by
      field_simp
    rw [h1, zero_div]
    norm_num

end Incidence

/-! ## 9. The seam, packaged: from a cap to a geometric column -/

section Seam

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*} {δ : NNReal} {θ : ℝ}

/-- **A4 ⇒ A5, in one call.**

Given a family all of whose directions lie within `θ` of the axis `p` (a *cap* of radius `θ`),
all of whose carriers lie in the unit ball, at a scale `4δ ≤ θ`, and with fullness at least
`18 t`, there is a **geometric column** `Y` — a half-open square of side `3θ/4` transverse to
`p`, extruded along the axis — and a base point `b ∈ B̄(0,1)` such that the subfamily `v` of
tubes meeting `Y`, shaded down to `Y`, satisfies

* the three clauses of A5's `Kakeya.CapRescale.IsCapColumn` about `b` (cap condition,
  unit-ball containment, and the transverse midpoint bound `2θ`), the last of which is the
  content of this file;
* A4's two conclusions: the fullness survives at `t = λ/18`, and the multiplicity of the whole
  family is at most `2` times the multiplicity of the column subfamily.

The `18 = 2 · 9` is A4's `2K` at the `K = 9` proved in `card_filter_columnSub_le`. The column
clause is stated in elementary form, so A5's producer consumes it with no conversion, and this
file imports nothing of A5. -/
theorem exists_column_localisation (hn : finrank ℝ E = 3) (hθ : 0 < θ) {p : E} (hp : ‖p‖ = 1)
    (hδθ : 4 * (δ : ℝ) ≤ θ) (u : Finset ι) (T : ι → ShadedTube δ E)
    (hdir : ∀ i ∈ u, dirDist (T i).direction p ≤ θ)
    (hball : ∀ i ∈ u, (T i).carrier ⊆ closedBall (0 : E) 1) {t : ENNReal}
    (hthr : 18 * t ≤ (ShadedBody.fullness u fun i => (T i).toShadedBody : ENNReal))
    (hM : ∑ i ∈ u, volume (T i).shade ≠ 0) :
    ∃ (v : Finset ι) (b : E) (Y : Set E) (hY : MeasurableSet Y),
      v ⊆ u ∧ ‖b‖ ≤ 1 ∧
      (∀ i ∈ v, dirDist (capShadeFam T Y hY i).direction p ≤ θ) ∧
      (∀ i ∈ v, (capShadeFam T Y hY i).carrier ⊆ closedBall (0 : E) 1) ∧
      (∀ i ∈ v, ‖((capShadeFam T Y hY i).midpoint - b)
          - (inner ℝ p ((capShadeFam T Y hY i).midpoint - b) : ℝ) • p‖ ≤ 2 * θ) ∧
      t ≤ (ShadedBody.fullness v fun i => (capShadeFam T Y hY i).toShadedBody : ENNReal) ∧
      (ShadedBody.multiplicity u fun i => (T i).toShadedBody)
        ≤ 2 * ShadedBody.multiplicity v fun i => (capShadeFam T Y hY i).toShadedBody := by
  obtain ⟨e₁, e₂, hf⟩ := exists_isTransverseFrame hn hp
  have hAdisj :
      ((columnBox θ : Finset (ℤ × ℤ)) : Set (ℤ × ℤ)).PairwiseDisjoint (columnSet e₁ e₂ θ) :=
    (pairwiseDisjoint_columnSet).set_pairwise _
  have hcover : ∀ i ∈ u, (T i).shade ⊆ ⋃ c ∈ columnBox θ, columnSet e₁ e₂ θ c := fun i hi =>
    subset_iUnion_columnSet_of_ball hf hθ (((T i).shade_subset).trans (hball i hi))
  have hcount : ∀ i ∈ u,
      ((((columnBox θ).filter fun c => i ∈ columnSub e₁ e₂ θ u T c).card : ℕ) : ENNReal)
        ≤ 9 := by
    intro i hi
    have h := card_filter_columnSub_le hf hθ hδθ u T (hdir i hi)
    exact_mod_cast h
  have hthr' : 2 * (9 : ENNReal) * t
      ≤ (ShadedBody.fullness u fun i => (T i).toShadedBody : ENNReal) := by
    have h : (2 : ENNReal) * 9 = 18 := by norm_num
    rw [h]; exact hthr
  obtain ⟨c, -, hfull, hmult⟩ :=
    mult_cap_le_max_columns (columnBox θ) (columnSet e₁ e₂ θ)
      (fun c => measurableSet_columnSet c) hAdisj u T (columnSub e₁ e₂ θ u T)
      (fun c _ => columnSub_subset u T c) hcover
      (fun _ _ i hi hne => mem_columnSub.mpr ⟨hi, hne⟩) hcount hthr' hM
  refine ⟨columnSub e₁ e₂ θ u T c, columnRef e₁ e₂ θ c, columnSet e₁ e₂ θ c,
    measurableSet_columnSet c, columnSub_subset u T c, norm_columnRef_le_one c, ?_, ?_, ?_,
    hfull, hmult⟩
  · intro i hi
    simp only [capShadeFam_apply, capShade_toTube]
    exact hdir i (columnSub_subset u T c hi)
  · intro i hi
    simp only [capShadeFam_apply, capShade_carrier]
    exact hball i (columnSub_subset u T c hi)
  · intro i hi
    simp only [capShadeFam_apply, capShade_toTube]
    obtain ⟨hiu, hne⟩ := mem_columnSub.mp hi
    exact norm_perpAxis_midpoint_sub_columnRef_le hf hθ (by linarith) (hdir i hiu)
      (hball i hiu) hne

end Seam

/-! ## 10. Sharpness: the column side is pinned from above too

 writes the column side as `4θ` with `θ` A5's own reference thickness, i.e.
**four times the cap radius**. That reading is **refuted** here, in the same style as A5's
`Kakeya.CapRescale.fullness_loss_is_forced`: at four times the cap radius a single column has
more transverse extent than the whole `2θ` midpoint budget can absorb, so no choice of base
point makes A5's `column` clause true for every tube meeting the column.

's own `θ' := 4θ` is a **different number** — `4 θ_ang`, i.e. exactly the
cap radius, one quarter of the above. That one is **not** refuted: it merely lies outside the
window `[3θ/4, 5θ/6]` that this file's base-point route admits (module docstring, units
section). And nothing here touches the **cap radius** `4 θ_ang` itself, whose `3 θ_ang`
alternative A2, A3 and A4 refuted independently; the cap radius is this file's `θ`.

The column side that works is `columnSide θ = 3θ/4 = 3 θ_ang`, pinned from below by the
incidence count and from above by the midpoint budget. -/

section Sharpness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {θ : ℝ} {p e₁ e₂ : E}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **The transverse extent of a column is exactly its diagonal**: for every `a` below the
side, one column contains two points whose transverse separation has square `2a²`. So the
`(3/2)`-surrogate of `norm_perpAxis_sub_le_of_mem_columnSet` is off the truth `√2` by less than
`6%`, and no bound below `√2 ·` side is available. -/
theorem exists_mem_columnSet_norm_perpAxis_sq_eq (hf : IsTransverseFrame p e₁ e₂) (hθ : 0 < θ)
    {a : ℝ} (ha : 0 ≤ a) (has : a < columnSide θ) :
    ∃ x y : E, x ∈ columnSet e₁ e₂ θ (0, 0) ∧ y ∈ columnSet e₁ e₂ θ (0, 0) ∧
      ‖perpAxis p (x - y)‖ ^ 2 = 2 * a ^ 2 := by
  have hs := columnSide_pos (θ := θ) hθ
  refine ⟨a • e₁ + a • e₂, 0, ?_, ?_, ?_⟩
  · have h₁ : (inner ℝ e₁ (a • e₁ + a • e₂) : ℝ) = a := by
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, hf.inner_fst_snd,
        real_inner_self_eq_norm_sq, hf.norm_fst]
      ring
    have h21 : (inner ℝ e₂ e₁ : ℝ) = 0 := by rw [real_inner_comm]; exact hf.inner_fst_snd
    have h₂ : (inner ℝ e₂ (a • e₁ + a • e₂) : ℝ) = a := by
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, h21,
        real_inner_self_eq_norm_sq, hf.norm_snd]
      ring
    have hfl : ⌊a / columnSide θ⌋ = 0 := by
      rw [Int.floor_eq_zero_iff]
      constructor
      · positivity
      · rw [div_lt_one hs]; exact has
    simp only [mem_columnSet, columnIndex, h₁, h₂, hfl]
  · simp only [mem_columnSet, columnIndex, inner_zero_right, zero_div, Int.floor_zero]
  · have hx : (a • e₁ + a • e₂ : E) - 0 = a • e₁ + a • e₂ := by abel
    rw [hx, norm_perpAxis_sq hf]
    have h₁ : (inner ℝ e₁ (a • e₁ + a • e₂) : ℝ) = a := by
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, hf.inner_fst_snd,
        real_inner_self_eq_norm_sq, hf.norm_fst]
      ring
    have h21 : (inner ℝ e₂ e₁ : ℝ) = 0 := by rw [real_inner_comm]; exact hf.inner_fst_snd
    have h₂ : (inner ℝ e₂ (a • e₁ + a • e₂) : ℝ) = a := by
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, h21,
        real_inner_self_eq_norm_sq, hf.norm_snd]
      ring
    rw [h₁, h₂]
    ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- **The band plan's column side `4θ` is refuted.** `columnSet e₁ e₂ (16θ/3)` is the column
family of side `4θ`. It contains two points whose transverse separation exceeds
`2 · 2θ + 2 · (θ/2 + θ/4)` — the largest separation two carrier points can have when both
midpoints are transversally within `2θ` of one base point. So at side `4θ`, A5's `column`
clause cannot hold about **any** base point for a pair of tubes whose shades meet the column at
these two points; only the realisability of that pair by actual `ShadedTube`s is left
uncompiled, and the transverse geometry alone already excludes it.

`4θ` is `4` times the **cap radius** here, which is what  asks for; the
`3θ` refutation of A2/A3/A4 concerns the cap radius itself and is untouched — see the module
docstring's units section. -/
theorem column_side_four_theta_is_refuted (hf : IsTransverseFrame p e₁ e₂) (hθ : 0 < θ) :
    ∃ x y : E, x ∈ columnSet e₁ e₂ (16 / 3 * θ) (0, 0) ∧
      y ∈ columnSet e₁ e₂ (16 / 3 * θ) (0, 0) ∧
      2 * (2 * θ) + 2 * (θ / 2 + θ / 4) < ‖perpAxis p (x - y)‖ := by
  have hθ' : 0 < 16 / 3 * θ := by linarith
  have hside : columnSide (16 / 3 * θ) = 4 * θ := by rw [columnSide]; ring
  obtain ⟨x, y, hx, hy, hsq⟩ :=
    exists_mem_columnSet_norm_perpAxis_sq_eq (θ := 16 / 3 * θ) hf hθ'
      (a := 63 / 16 * θ) (by linarith) (by rw [hside]; linarith)
  refine ⟨x, y, hx, hy, ?_⟩
  nlinarith [norm_nonneg (perpAxis p (x - y)), hsq, sq_nonneg θ]

end Sharpness

end Kakeya.CapColumn
