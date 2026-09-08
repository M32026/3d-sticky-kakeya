/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Sticky
public import Kakeya.FibreCommon

/-!
  # Fibre counts and node-reading Frostman for shaded families

  The first half of the reduction that moves a shaded family into the unit ball.  Two independent
  ingredients are prepared here.

  *Translation.*  A `δ`-tube, its fullness, and its leaf-anchored Frostman condition are all carried
  across a translation, and a `1/4`-net of `B_R` is fixed before `δ` so that pigeonholing the tube
  midpoints over it costs only a `δ`-independent constant.

  *Fibre counts.*  Leaf-anchored Frostman at every scale forces the fibres of a family over its node
  index to have comparable cardinalities, both in the ambient family and in a uniformized subfamily,
  and that comparability converts the ambient reading of Frostman into the node reading demanded by
  part (A).
-/

@[expose] public section

open MeasureTheory
open Tube

namespace Kakeya

open MultiScaleFac

namespace StickyKakeya

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*}

/-! ### Translating a single tube -/

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- Translating by `v` and then by `-v` is the identity on `δ`-tubes.  The `ConvexSpaceBody`
counterpart `ConvexSpaceBody.neg_translate_cancel` is already available; what is needed here is the
tube-level statement, since the bounded-overlap clauses quantify over `Tube ρ E` and have to be
reindexed along `V ↦ V.translate (-v)`. -/
theorem tube_translate_neg_cancel {δ : NNReal} (T : Tube δ E) (v : E) :
    (T.translate v).translate (-v) = T := by
  refine Tube.ext ?_ ?_ ?_
  · ext x
    simp [Tube.translate, Tube.vadd]
  · simp
  · simp

/-! ### The unit-ball assignment at an arbitrary radius

`Kakeya.exists_unit_ball_assignment` is this statement at `R = 2`; the radius is generalized here
because the radius the consumer needs, `gridLen n η₁ ε + 1`, is a `δ`-independent constant but not
`2`.  The net is quantified *before* `δ`, which is what makes its cardinality a constant that a
positive power of `1/δ` absorbs. -/
omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
theorem exists_ball_assignment (R : ℝ) (hR : 1 ≤ R) :
    ∃ xs : Finset E, xs.Nonempty ∧ (∀ x ∈ xs, ‖x‖ ≤ R) ∧
      ∀ {δ : NNReal}, (δ : ℝ) ≤ 1 / 4 →
        ∀ T : Tube δ E, T.carrier ⊆ Metric.closedBall (0 : E) R →
          ∃ x ∈ xs, T.carrier ⊆ Metric.closedBall x 1 := by
  obtain ⟨xs, hxs_norm, hcover⟩ :=
    closedBall_finite_closedBall_cover (E := E) R (by norm_num : (0 : ℝ) < 1 / 4) (0 : E)
  have h0in : (0 : E) ∈ Metric.closedBall (0 : E) R := by
    rw [Metric.mem_closedBall, dist_self]
    linarith
  have hxs_nonempty : xs.Nonempty := by
    obtain ⟨x, hx, _⟩ := Set.mem_iUnion₂.mp (hcover h0in)
    exact ⟨x, hx⟩
  refine ⟨xs, hxs_nonempty,
    fun x hx => by simpa [Metric.mem_closedBall, dist_zero_right] using hxs_norm x hx, ?_⟩
  intro δ hδ_le T hsub
  have hδ_pos : (0 : ℝ) ≤ (δ : ℝ) := NNReal.coe_nonneg _
  have hmid_in_carrier : midpoint ℝ T.x T.y ∈ T.carrier := by
    rw [T.carrier_eq]
    exact Set.mem_iUnion₂.mpr
      ⟨midpoint ℝ T.x T.y, midpoint_mem_segment (𝕜 := ℝ) T.x T.y,
        Metric.mem_closedBall_self hδ_pos⟩
  have hmid_cov : midpoint ℝ T.x T.y ∈ ⋃ x ∈ xs, Metric.closedBall x (1 / 4) :=
    hcover (hsub hmid_in_carrier)
  obtain ⟨x, hx, hmid_close⟩ := Set.mem_iUnion₂.mp hmid_cov
  refine ⟨x, hx, ?_⟩
  intro p hp
  have hcarrier_sub : p ∈ Metric.closedBall (midpoint ℝ T.x T.y) (1 / 2 + (δ : ℝ)) :=
    Tube.carrier_subset_closedBall_midpoint (E := E) T hp
  rw [Metric.mem_closedBall] at hcarrier_sub hmid_close
  rw [Metric.mem_closedBall]
  calc dist p x
      ≤ dist p (midpoint ℝ T.x T.y) + dist (midpoint ℝ T.x T.y) x := dist_triangle _ _ _
    _ ≤ (1 / 2 + (δ : ℝ)) + (1 / 4) := add_le_add hcarrier_sub hmid_close
    _ ≤ 1 := by linarith

/-! ### The hypotheses of (A) are translation invariant -/

/-! ### Frostman read at the grid scales only

The chain that carries a shaded family into the unit ball never tests the leaf-anchored Frostman
condition at an arbitrary real scale: every one of its consumers evaluates it at a grid scale
`gridScale δ N k`.  The predicate below is exactly that restriction, phrased in the fibre notation
that `MultiScaleFac.isFrostmanIn_coverClass_of_fibre_grid` and
`Kakeya/MultiScaleFac/Ports.lean` already speak.  Taking it as the hypothesis instead of the
environment-level `StickyKakeya.IsFrostmanAtEveryScale` costs a producer nothing — the implication
`MultiScaleFac.isFrostmanAtGridScales_of_isFrostmanAtEveryScale` is immediate — and it is what
allows the environment-level predicate to be retired from this chain. -/

/-- **Frostman at every grid scale.**  For every grid index `k ≤ N` and every anchor `i₀ ∈ s`, the
fibre family `𝕋_{δ∣gridScale δ N k}[i₀]` is `A`-Frostman in `T_{i₀}^{(gridScale δ N k)}`.

This is `StickyKakeya.IsFrostmanAtEveryScale` restricted to the grid, in the fibre reading of
`StickyKakeya.isFrostmanAtEveryScale_iff_fibre`. -/
def IsFrostmanAtGridScales {ι : Type*} {δ : NNReal} (s : Finset ι) (T : ι → Tube δ E) (N : ℕ)
    (A : ENNReal) : Prop :=
  ∀ k ≤ N, ∀ i₀ ∈ s, ConvexSpaceBody.IsFrostmanIn (fibreIndex s T δ (gridScale δ N k) i₀)
    (fibreBodies T δ) ((T i₀).rescale (gridScale δ N k)).toConvexSpaceBody A

omit [Nontrivial E] in
/-- A family Frostman at every scale is Frostman at every grid scale: the grid scales lie in
`[δ, 1]`. -/
theorem isFrostmanAtGridScales_of_isFrostmanAtEveryScale {ι : Type*} {δ : NNReal} {s : Finset ι}
    {T : ι → Tube δ E} {A : ENNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (N : ℕ)
    (hFro : IsFrostmanAtEveryScale s T A) : IsFrostmanAtGridScales s T N A := by
  intro k hk i0 hi0
  have hd : δ ≤ gridScale δ N k := by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · have hk0 : k = 0 := by omega
      subst k
      simpa [gridScale_zero] using hδ1
    · have hδN : gridScale δ N N = δ := gridScale_self δ hN
      calc
        δ = gridScale δ N N := hδN.symm
        _ ≤ gridScale δ N k := gridScale_antitone hδ hδ1 N hk
  exact (isFrostmanAtEveryScale_iff_fibre s T A).mp hFro (gridScale δ N k) hd
    (gridScale_le_one hδ1 N k) i0 hi0

omit [Nontrivial E] in
/-- The grid reading, evaluated with the bodies written as `fun i => (T i).toConvexSpaceBody`, the
form the node-reading lemmas of `Kakeya/MultiScaleFac/Bridge.lean` consume. -/
theorem IsFrostmanAtGridScales.isFrostmanIn_fibre {ι : Type*} {δ : NNReal} {s : Finset ι}
    {T : ι → Tube δ E} {N : ℕ} {A : ENNReal} (hFro : IsFrostmanAtGridScales s T N A)
    {k : ℕ} (hk : k ≤ N) {i₀ : ι} (hi₀ : i₀ ∈ s) :
    ConvexSpaceBody.IsFrostmanIn (fibreIndex s T δ (gridScale δ N k) i₀)
      (fun i => (T i).toConvexSpaceBody)
      ((T i₀).rescale (gridScale δ N k)).toConvexSpaceBody A := by
  simpa using hFro k hk i₀ hi₀

omit [Nontrivial E] in
/-- Being Frostman at every grid scale is invariant under a common translation.  Both the fibre
index sets and the anchors translate, while the grid scales themselves do not depend on the family:
`Tube.translate_rescale_swap` moves the translation past the rescaling of the anchor,
`translate_le_translate_iff` identifies the two fibres, and
`ConvexSpaceBody.IsFrostmanIn.translate_iff` finishes. -/
theorem isFrostmanAtGridScales_translate {ι : Type*} {δ : NNReal} (s : Finset ι) (T : ι → Tube δ E)
    (N : ℕ) (A : ENNReal) (v : E) :
    IsFrostmanAtGridScales s (fun i => (T i).translate v) N A
      ↔ IsFrostmanAtGridScales s T N A := by
  classical
  simp only [IsFrostmanAtGridScales, fibreIndex_self, fibreBodies_self]
  have key : ∀ (ρ : NNReal) (i₀ : ι),
      s.filter (fun i => ((T i).translate v).toConvexSpaceBody ≤
          (Tube.rescale ((T i₀).translate v) ρ).toConvexSpaceBody)
        = s.filter (fun i =>
          (T i).toConvexSpaceBody ≤ (Tube.rescale (T i₀) ρ).toConvexSpaceBody) := by
    intro ρ i₀
    refine Finset.filter_congr (fun x hx => ?_)
    rw [Tube.translate_rescale_swap]
    change ConvexSpaceBody.translate (T x).toConvexSpaceBody v ≤
        ConvexSpaceBody.translate ((T i₀).rescale ρ).toConvexSpaceBody v ↔
      (T x).toConvexSpaceBody ≤ (Tube.rescale (T i₀) ρ).toConvexSpaceBody
    simp only [translate_le_translate_iff]
  constructor
  · intro h k hk i₀ hi₀
    have hh := h k hk i₀ hi₀
    rw [← key (gridScale δ N k) i₀]
    rw [Tube.translate_rescale_swap] at hh ⊢
    exact (ConvexSpaceBody.IsFrostmanIn.translate_iff (v := v)).mp hh
  · intro h k hk i₀ hi₀
    have hh := h k hk i₀ hi₀
    rw [key (gridScale δ N k) i₀, Tube.translate_rescale_swap]
    exact (ConvexSpaceBody.IsFrostmanIn.translate_iff (v := v)).mpr hh

/-! ## Comparable fibre counts from Frostman at every scale

Frostman at every scale, in its leaf-anchored form `StickyKakeya.IsFrostmanAtEveryScale`, pins the
`ρ`-fibre count of *every* anchor between two multiples of the full value `(ρ/δ)^{n-1}`, and it does
so with **no pigeonholing and no passage to a subfamily**.  The two halves are independent:

* the **lower** bound is Frostman itself, tested at `K'` a single member tube.  Its density in its
  own body is at least `1`, so Definition 3.2 forces the density of the whole fibre in the anchor to
  be at least `1/A`, and a fibre of small cardinality cannot achieve that;
* the **upper** bound is the ambient `Δ_max ≤ D` hypothesis, which caps the number of `δ`-tubes that
  fit inside a `ρ`-tube at `D` times the volume ratio.

Dividing the two at two different anchors gives `Kakeya.MultiScaleFac.ComparableFibreCounts` and its
`4`-inflated strengthening `Kakeya.MultiScaleFac.ComparableFibreCountsInflated` on the whole grid,
with constant `5·4^{n-1}·(C_n/c_n)^2·A·D`, i.e. `δ^{-2η}` up to a dimensional factor when both
inputs are `δ^{-η}`.

**What this does not give.**  It is *not* a `Tube.UniformTubeSet` on `s`.  That structure
asks for a nested *partition* of `s` whose classes are two-sided comparable at every grid index, and
comparability of the fibres does not produce one: the classes of a cover are pieces of a partition,
and a piece meeting the boundary of the family can be arbitrarily small while every fibre stays
full.  Every construction of a `UniformTubeSet` in this development therefore discards part of the
index set (`Tube.exists_uniformTubeSet_subfamily`,
`MultiScaleFac.exists_gridUniform_subfamily`), and the comparability proved here is exactly the
datum that lets a Frostman bound be carried across such a discard
(`MultiScaleFac.card_fibreIndex_le_mul_of_card_le`). -/

/-- The dimensional constant of `MultiScaleFac.card_fibreIndex_four_mul_le_of_frostman`: the square
of the tube volume comparison ratio `C_n/c_n`, inflated by `5·4^{n-1}` to pay for the four-fold
thickening of the anchor on the larger side. -/
noncomputable def frostmanFibreConst (n : ℕ) : NNReal :=
  5 * 4 ^ (n - 1) * (Tube.volume_le.C n / Tube.le_volume.c n) ^ 2

omit [Nontrivial E] in
/-- The anchor density of a fibre is the ambient density at that anchor: filtering `s` by
containment in the anchor is what produces the fibre in the first place, so filtering the fibre
again changes nothing. -/
theorem densityIn_fibreIndex_eq_densityIn {ι : Type*} {δ : NNReal} (s : Finset ι)
    (T : ι → Tube δ E) (ρ : NNReal) (i₀ : ι) :
    Kakeya.densityIn (fibreIndex s T δ ρ i₀) (fibreBodies T δ)
        ((T i₀).rescale ρ).toConvexSpaceBody
      = Kakeya.densityIn s (fun i => (T i).toConvexSpaceBody)
        ((T i₀).rescale ρ).toConvexSpaceBody := by
  classical
  simp [Kakeya.densityIn, fibreIndex, Kakeya.familyIn, fibreBodies, Finset.filter_filter]

/-- **The Frostman lower bound on a fibre count.**  Testing Definition 3.2 at `K' = T_{i₁}` — a
single member of the fibre, which lies in the anchor — gives
`1 ≤ A · Δ(𝕋_{δ∣ρ}[i₁], T_{i₁}^{(ρ)})`; weighting by the minimal anchor volume `c_n ρ^{n-1}` and
applying `MultiScaleFac.densityIn_fibre_mul_le_card` turns the density into the count. -/
theorem le_card_fibreIndex_mul_of_frostman {ι : Type*} {δ ρ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {s : Finset ι} {T : ι → Tube δ E} {A : ENNReal}
    (hδρ : δ ≤ ρ) {i₁ : ι} (hi₁ : i₁ ∈ s)
    (hF : ConvexSpaceBody.IsFrostmanIn (fibreIndex s T δ ρ i₁) (fibreBodies T δ)
      ((T i₁).rescale ρ).toConvexSpaceBody A) :
    ((Tube.le_volume.c (Module.finrank ℝ E) : NNReal) : ENNReal)
        * ((ρ : ENNReal) ^ (Module.finrank ℝ E - 1))
      ≤ A * (((fibreIndex s T δ ρ i₁).card : ENNReal)
          * (((Tube.volume_le.C (Module.finrank ℝ E) : NNReal) : ENNReal)
              * ((δ : ENNReal) ^ (Module.finrank ℝ E - 1)))) := by
  set n := Module.finrank ℝ E with hn
  have hK' : (T i₁).toConvexSpaceBody ≤ ((T i₁).rescale ρ).toConvexSpaceBody :=
    Tube.le_rescale (T i₁) hδρ
  have hdensity : Kakeya.densityIn (fibreIndex s T δ ρ i₁) (fibreBodies T δ)
        ((T i₁).toConvexSpaceBody)
      ≤ A * Kakeya.densityIn (fibreIndex s T δ ρ i₁) (fibreBodies T δ)
        ((T i₁).rescale ρ).toConvexSpaceBody :=
    hF ((T i₁).toConvexSpaceBody) hK'
  have hvol_ne : volume (T i₁).carrier ≠ 0 := by
    have hpos : 0 < ((Tube.le_volume.c (Module.finrank ℝ E) * δ ^ (Module.finrank ℝ E - 1)
        : NNReal) : ENNReal) :=
      ENNReal.coe_pos.mpr (mul_pos (Tube.le_volume.c_pos (Module.finrank ℝ E))
        (pow_pos hδ (Module.finrank ℝ E - 1)))
    exact (lt_of_lt_of_le hpos (by simpa using (Tube.le_volume (T i₁)))).ne'
  have hvol_top : volume (T i₁).carrier ≠ ⊤ := (T i₁).toConvexSpaceBody.3.measure_ne_top
  have hself : 1 ≤ Kakeya.densityIn (fibreIndex s T δ ρ i₁) (fibreBodies T δ)
      ((T i₁).toConvexSpaceBody) := by
    have hi : i₁ ∈ fibreIndex s T δ ρ i₁ := mem_fibreIndex_self hδρ hi₁
    have hle := Kakeya.le_densityIn (fibreIndex s T δ ρ i₁) (fibreBodies T δ)
      ((T i₁).toConvexSpaceBody) hi (by simp [fibreBodies_self])
    calc
      1 = volume (T i₁).carrier / volume (T i₁).carrier := by
        rw [ENNReal.div_self hvol_ne hvol_top]
      _ ≤ Kakeya.densityIn (fibreIndex s T δ ρ i₁) (fibreBodies T δ)
          ((T i₁).toConvexSpaceBody) := by
        simpa [fibreBodies_self] using hle
  have h1 : 1 ≤ A * Kakeya.densityIn (fibreIndex s T δ ρ i₁) (fibreBodies T δ)
      ((T i₁).rescale ρ).toConvexSpaceBody := hself.trans hdensity
  calc
    ((Tube.le_volume.c n : NNReal) : ENNReal) * ((ρ : ENNReal) ^ (n - 1))
        ≤ A * Kakeya.densityIn (fibreIndex s T δ ρ i₁) (fibreBodies T δ)
            ((T i₁).rescale ρ).toConvexSpaceBody
          * (((Tube.le_volume.c n : NNReal) : ENNReal) * ((ρ : ENNReal) ^ (n - 1))) := by
      simpa [one_mul] using (mul_le_mul_left h1
        (((Tube.le_volume.c n : NNReal) : ENNReal) * ((ρ : ENNReal) ^ (n - 1))))
    _ = A * (Kakeya.densityIn (fibreIndex s T δ ρ i₁) (fibreBodies T δ)
            ((T i₁).rescale ρ).toConvexSpaceBody
          * (((Tube.le_volume.c n : NNReal) : ENNReal) * ((ρ : ENNReal) ^ (n - 1)))) := by
      rw [mul_assoc]
    _ ≤ A * (((fibreIndex s T δ ρ i₁).card : ENNReal)
          * (((Tube.volume_le.C n : NNReal) : ENNReal) * ((δ : ENNReal) ^ (n - 1)))) := by
      exact mul_le_mul_right (densityIn_fibre_mul_le_card hδ1 ρ i₁) A

/-- **The ambient-density upper bound on a fibre count.**

`MultiScaleFac.card_mul_le_densityIn_fibre` weights the count by the minimal member volume and
bounds it by the anchor density, which is at most `Δ_max(𝕋) ≤ D`.  The anchor scale is allowed to be
any `ρ ≤ 4`, which is what lets the consumer take the four-fold inflated anchor. -/
theorem card_fibreIndex_mul_le_of_maxDensity {ι : Type*} {δ ρ : NNReal}
    {s : Finset ι} {T : ι → Tube δ E} {D : ENNReal}
    (hD : Kakeya.maxDensity s (fun i => (T i).toConvexSpaceBody) ≤ D)
    (hρ4 : ρ ≤ 4) (i₀ : ι) :
    ((fibreIndex s T δ ρ i₀).card : ENNReal)
        * (((Tube.le_volume.c (Module.finrank ℝ E) : NNReal) : ENNReal)
            * ((δ : ENNReal) ^ (Module.finrank ℝ E - 1)))
      ≤ D * ((((5 : NNReal) * Tube.volume_le.C (Module.finrank ℝ E) : NNReal) : ENNReal)
          * ((ρ : ENNReal) ^ (Module.finrank ℝ E - 1))) := by
  have hfibre :
      Kakeya.densityIn (fibreIndex s T δ ρ i₀) (fibreBodies T δ)
          ((T i₀).rescale ρ).toConvexSpaceBody ≤ D := by
    rw [densityIn_fibreIndex_eq_densityIn s T ρ i₀]
    exact le_trans
      (Kakeya.le_maxDensity s (fun i => (T i).toConvexSpaceBody)
        ((T i₀).rescale ρ).toConvexSpaceBody)
      hD
  have h5 : (1 + 4 : NNReal) = (5 : NNReal) := by norm_num
  calc
    ((fibreIndex s T δ ρ i₀).card : ENNReal)
        * (((Tube.le_volume.c (Module.finrank ℝ E) : NNReal) : ENNReal)
            * ((δ : ENNReal) ^ (Module.finrank ℝ E - 1)))
      ≤ Kakeya.densityIn (fibreIndex s T δ ρ i₀) (fibreBodies T δ)
            ((T i₀).rescale ρ).toConvexSpaceBody
          * ((((1 + 4 : NNReal) * Tube.volume_le.C (Module.finrank ℝ E) : NNReal) : ENNReal)
              * ((ρ : ENNReal) ^ (Module.finrank ℝ E - 1))) := by
        exact card_mul_le_densityIn_fibre (b := 4) hρ4 i₀
      _ ≤ D * ((((1 + 4 : NNReal) * Tube.volume_le.C (Module.finrank ℝ E) : NNReal) : ENNReal)
              * ((ρ : ENNReal) ^ (Module.finrank ℝ E - 1))) := by
        exact mul_le_mul_left hfibre _
      _ = D * ((((5 : NNReal) * Tube.volume_le.C (Module.finrank ℝ E) : NNReal) : ENNReal)
              * ((ρ : ENNReal) ^ (Module.finrank ℝ E - 1))) := by
        rw [h5]

private theorem frostman_fibre_arith {m : ℕ} {F4 F1 A D c C d r : NNReal}
    (hc : 0 < c) (hd : 0 < d)
    (h1 : F4 * (c * d ^ m) ≤ D * (5 * C * (4 * r) ^ m))
    (h2 : c * r ^ m ≤ A * (F1 * (C * d ^ m))) :
    F4 ≤ 5 * 4 ^ m * (C / c) ^ 2 * A * D * F1 := by
  have hdm : 0 < d ^ m := pow_pos hd m
  have hc2 : 0 < c ^ 2 := pow_pos hc 2
  have hmain : F4 * c ^ 2 * d ^ m ≤ 5 * 4 ^ m * C ^ 2 * A * D * F1 * d ^ m := by
    calc
      F4 * c ^ 2 * d ^ m = F4 * (c * d ^ m) * c := by ring
      _ ≤ D * (5 * C * (4 * r) ^ m) * c := mul_le_mul_left h1 c
      _ = 5 * 4 ^ m * C * D * (c * r ^ m) := by
        rw [mul_pow]
        ring
      _ ≤ 5 * 4 ^ m * C * D * (A * F1 * C * d ^ m) := by
        refine mul_le_mul_right ?_ (5 * 4 ^ m * C * D)
        calc
          c * r ^ m ≤ A * (F1 * (C * d ^ m)) := h2
          _ = A * F1 * C * d ^ m := by ring
      _ = 5 * 4 ^ m * C ^ 2 * A * D * F1 * d ^ m := by ring
  have hcancel : F4 * c ^ 2 ≤ 5 * 4 ^ m * C ^ 2 * A * D * F1 := by
    exact (mul_le_mul_iff_right₀ hdm).mp (by simpa [mul_assoc, mul_left_comm, mul_comm] using hmain)
  have hdiv : F4 ≤ (5 * 4 ^ m * C ^ 2 * A * D * F1) / c ^ 2 := by
    exact (le_div_iff₀ hc2).mpr hcancel
  have hrewrite : (5 * 4 ^ m * C ^ 2 * A * D * F1) / c ^ 2 =
      5 * 4 ^ m * (C / c) ^ 2 * A * D * F1 := by
    field_simp [hc2.ne']
  simpa [hrewrite] using hdiv

/-- **Two-sided comparability of fibre counts, at one scale.**

Divide the Frostman lower bound at the anchor `i₁` and scale `ρ` by the `Δ_max` upper bound at the
anchor `i₀` and the inflated scale `4ρ`.  The two volume weights `c_n δ^{n-1}` and `ρ^{n-1}` cancel,
leaving `5·4^{n-1}·(C_n/c_n)^2·A·D`. -/
theorem card_fibreIndex_four_mul_le_of_frostman {ι : Type*} {δ ρ : NNReal}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) {s : Finset ι} {T : ι → Tube δ E} {A D : NNReal}
    (hD : Kakeya.maxDensity s (fun i => (T i).toConvexSpaceBody) ≤ (D : ENNReal))
    (hδρ : δ ≤ ρ) (hρ1 : ρ ≤ 1) (i₀ : ι) {i₁ : ι} (hi₁ : i₁ ∈ s)
    (hF : ConvexSpaceBody.IsFrostmanIn (fibreIndex s T δ ρ i₁) (fibreBodies T δ)
      ((T i₁).rescale ρ).toConvexSpaceBody (A : ENNReal)) :
    ((fibreIndex s T δ (4 * ρ) i₀).card : NNReal)
      ≤ frostmanFibreConst (Module.finrank ℝ E) * A * D
          * ((fibreIndex s T δ ρ i₁).card : NNReal) := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn_def
  set j₀ : NNReal := ((fibreIndex s T δ (4 * ρ) i₀).card : NNReal) with hj₀_def
  set j₁ : NNReal := ((fibreIndex s T δ ρ i₁).card : NNReal) with hj₁_def
  have hρ4 : 4 * ρ ≤ 4 := by
    calc
      4 * ρ ≤ 4 * 1 := mul_le_mul_of_nonneg_left hρ1 (by norm_num)
      _ = 4 := by norm_num
  have hA := card_fibreIndex_mul_le_of_maxDensity (s := s) (T := T) (D := (D : ENNReal))
    hD hρ4 i₀
  have hB := le_card_fibreIndex_mul_of_frostman (A := (A : ENNReal)) hδ hδ1 hδρ hi₁ hF
  have hA_nn :
      j₀ * (Tube.le_volume.c n * δ ^ (n - 1))
        ≤ D * ((5 * Tube.volume_le.C n) * (4 * ρ) ^ (n - 1)) := by
    exact_mod_cast hA
  have hB_nn :
      Tube.le_volume.c n * ρ ^ (n - 1)
        ≤ A * (j₁ * (Tube.volume_le.C n * δ ^ (n - 1))) := by
    exact_mod_cast hB
  simpa [frostmanFibreConst, hn_def, hj₀_def, hj₁_def] using
    frostman_fibre_arith (m := n - 1) (F4 := j₀) (F1 := j₁) (A := A) (D := D)
      (c := Tube.le_volume.c n) (C := Tube.volume_le.C n) (d := δ) (r := ρ)
      (Tube.le_volume.c_pos n) hδ hA_nn hB_nn

/-- **Frostman at every scale implies comparable fibre counts, on the whole index set.**

No pigeonholing, no subfamily, no essential distinctness: both halves of the comparability are read
directly off the two hypotheses at each grid scale.  The constant is
`5·4^{n-1}·(C_n/c_n)^2·A·D`. -/
theorem comparableFibreCountsInflated_of_isFrostmanAtEveryScale {ι : Type*} {δ : NNReal}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (N : ℕ) {s : Finset ι} {T : ι → Tube δ E} {A D : NNReal}
    (hFro : IsFrostmanAtGridScales s T N (A : ENNReal))
    (hD : Kakeya.maxDensity s (fun i => (T i).toConvexSpaceBody) ≤ (D : ENNReal)) :
    ComparableFibreCounts s T (gridScales δ N)
        (frostmanFibreConst (Module.finrank ℝ E) * A * D) ∧
      ComparableFibreCountsInflated s T (gridScales δ N)
        (frostmanFibreConst (Module.finrank ℝ E) * A * D) := by
  constructor
  · intro ρ hρ i₀ hi₀ i₁ hi₁
    rcases hρ with ⟨k, hk, rfl⟩
    have hδρ' : δ ≤ gridScale δ N k := by
      rcases Nat.eq_zero_or_pos N with rfl | hN
      · have hk0 : k = 0 := by omega
        subst k
        simpa [gridScale_zero] using hδ1
      · have hδN : gridScale δ N N = δ := gridScale_self δ hN
        calc
          δ = gridScale δ N N := hδN.symm
          _ ≤ gridScale δ N k := gridScale_antitone hδ hδ1 N hk
    have hρ1' : gridScale δ N k ≤ 1 := gridScale_le_one hδ1 N k
    have hinf :
        ((fibreIndex s T δ (4 * gridScale δ N k) i₀).card : NNReal) ≤
          frostmanFibreConst (Module.finrank ℝ E) * A * D *
            ((fibreIndex s T δ (gridScale δ N k) i₁).card : NNReal) := by
      exact card_fibreIndex_four_mul_le_of_frostman hδ hδ1 hD hδρ' hρ1' i₀ hi₁ (hFro k hk i₁ hi₁)
    have hρle4ρ : gridScale δ N k ≤ 4 * gridScale δ N k := by
      calc
        gridScale δ N k = 1 * gridScale δ N k := by rw [one_mul]
        _ ≤ 4 * gridScale δ N k :=
          mul_le_mul_left (by norm_num : (1 : NNReal) ≤ 4) (gridScale δ N k)
    have hsubset :
        fibreIndex s T δ (gridScale δ N k) i₀ ⊆ fibreIndex s T δ (4 * gridScale δ N k) i₀ := by
      exact fibreIndex_subset_of_anchor_le (s := s) (T := T) (σ := δ)
        (ρ := gridScale δ N k) (ρ' := 4 * gridScale δ N k) hρle4ρ i₀
    have hcard_le : ((fibreIndex s T δ (gridScale δ N k) i₀).card : NNReal) ≤
        (fibreIndex s T δ (4 * gridScale δ N k) i₀).card := by
      exact_mod_cast (Finset.card_le_card hsubset)
    exact le_trans hcard_le hinf
  · intro ρ hρ i₀ hi₀ i₁ hi₁
    rcases hρ with ⟨k, hk, rfl⟩
    have hδρ' : δ ≤ gridScale δ N k := by
      rcases Nat.eq_zero_or_pos N with rfl | hN
      · have hk0 : k = 0 := by omega
        subst k
        simpa [gridScale_zero] using hδ1
      · have hδN : gridScale δ N N = δ := gridScale_self δ hN
        calc
          δ = gridScale δ N N := hδN.symm
          _ ≤ gridScale δ N k := gridScale_antitone hδ hδ1 N hk
    have hρ1' : gridScale δ N k ≤ 1 := gridScale_le_one hδ1 N k
    exact card_fibreIndex_four_mul_le_of_frostman hδ hδ1 hD hδρ' hρ1' i₀ hi₁ (hFro k hk i₁ hi₁)

/-! ### Node-reading Frostman for a uniformized subfamily

The Frostman datum available to the sticky assembly is *leaf-anchored* and lives on the **ambient**
family `s`, while the uniform hierarchy `𝒰` produced by `exists_shadedUniformTubeSet_subfamily_ssf`
lives on a pruned subfamily `t ⊆ s`, and Theorem 7.3(A) consumes the **node-reading** condition
`𝒰.IsFrostmanAtEveryScale`.  Neither existing bridge closes that gap:
`isFrostmanAtEveryScale_nodes_of_fibre` needs the hierarchy's own index set to carry the
leaf-anchored bound, and `card_fibreIndex_le_mul_of_card_le` needs a cover of the ambient family,
which is the same partition problem one level up.

The route taken here is a dual count that needs no ambient cover.  Writing `𝕋[i;ρ]` for the
`ρ`-fibre, the pair set `{(j, i) ∈ s × t : T_j ⊆ T_i^{(ρ)}}` is counted twice: along `t` it is the
sum of the ambient fibres, which comparability on `s` makes uniformly large, and along `s` each
slice sits inside the retained fibre `𝕋_t[j; 4ρ]`, which the uniform hierarchy makes uniformly
small.  The global proportion `|s| ≤ Λ|t|` converts one into the other.  The outcome
(`card_fibreIndex_le_mul_card_coverClass_of_proportion`) is an **ambient fibre against a retained
class**, which is precisely the input that the node-reading Frostman argument of
`Kakeya/MultiScaleFac/Bridge.lean` consumes; the two remaining lemmas replay that argument with the
ambient family on the fibre side and the retained family on the class side.

Note that the descent is *not* available at the exact-scale leaf-anchored level: bounding
`𝕋_t[j; 4ρ_k]` below by an exact-scale retained fibre would need the branching numbers at two
adjacent grid indices to be comparable, which a `16`-separated grid does not provide.  Routing
through the class count avoids that entirely. -/

/-- The size of the covering of a `4ρ`-fibre by exact-scale `ρ`-fibres supplied by
`MultiScaleFac.exists_gapFibre_cover_of_ratio`.  It is `MultiScaleFac.nodeClassConst` with its two
tube-volume ratio factors stripped off. -/
noncomputable def fibreCoverConst : NNReal :=
  2 * (25 : NNReal) ^ (2 * Module.finrank ℝ E) * (4 : NNReal) ^ (2 * Module.finrank ℝ E)

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **The dual count.**  Comparability of the ambient fibres at the scale `ρ`, a uniform bound `M`
on the retained fibres at the four-fold inflated anchor, and the global proportion `|s| ≤ Λ|t|`
together bound every ambient fibre by `C₁ · Λ · M`.  No cover of the ambient family is needed, which
is what makes this usable where `MultiScaleFac.card_fibreIndex_le_mul_of_card_le` is not. -/
theorem card_fibreIndex_le_of_global_proportion {ι : Type*} {δ ρ : NNReal} {s t : Finset ι}
    {T : ι → Tube δ E} {C₁ M Λ : NNReal} (hts : t ⊆ s) (hδρ : δ ≤ ρ) (htne : t.Nonempty)
    (hcomp : ∀ i₀ ∈ s, ∀ i₁ ∈ s,
      ((fibreIndex s T δ ρ i₀).card : NNReal) ≤ C₁ * ((fibreIndex s T δ ρ i₁).card : NNReal))
    (hM : ∀ j ∈ s, ((fibreIndex t T δ (4 * ρ) j).card : NNReal) ≤ M)
    (hprop : (s.card : NNReal) ≤ Λ * (t.card : NNReal))
    {a : ι} (ha : a ∈ s) :
    ((fibreIndex s T δ ρ a).card : NNReal) ≤ C₁ * Λ * M := by
  classical
  let Q : ι → ι → Prop := fun j i => (T j).toConvexSpaceBody ≤ ((T i).rescale ρ).toConvexSpaceBody
  have hswap : (∑ i ∈ t, ((fibreIndex s T δ ρ i).card : NNReal))
      = (∑ j ∈ s, ((t.filter (fun i => Q j i)).card : NNReal)) := by
    calc
      (∑ i ∈ t, ((fibreIndex s T δ ρ i).card : NNReal))
          = (∑ i ∈ t, ((s.filter (fun j => Q j i)).card : NNReal)) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [fibreIndex_self]
      _ = (∑ j ∈ s, ((t.filter (fun i => Q j i)).card : NNReal)) := by
            rw [← Nat.cast_sum, ← Nat.cast_sum]
            congr 1
            simp_rw [Finset.card_filter]
            rw [Finset.sum_comm]
  have hlow : (t.card : NNReal) * ((fibreIndex s T δ ρ a).card : NNReal)
      ≤ C₁ * (∑ i ∈ t, ((fibreIndex s T δ ρ i).card : NNReal)) := by
    rw [Finset.mul_sum,
      show (t.card : NNReal) * ((fibreIndex s T δ ρ a).card : NNReal)
          = ∑ _i ∈ t, ((fibreIndex s T δ ρ a).card : NNReal) by
        rw [Finset.sum_const, nsmul_eq_mul]]
    exact Finset.sum_le_sum (fun i hi => hcomp a ha i (hts hi))
  have hinner : ∀ j, t.filter (fun i => Q j i) ⊆ fibreIndex t T δ (4 * ρ) j := by
    intro j x hx
    rw [fibreIndex_self]
    rw [Finset.mem_filter] at hx ⊢
    rcases hx with ⟨hx_t, hQ⟩
    refine ⟨hx_t, ?_⟩
    have hQ' : ((T x).rescale ρ).toConvexSpaceBody ≤ ((T j).rescale (4 * ρ)).toConvexSpaceBody :=
      Tube.rescale_le_of_le (T j) ((T x).rescale ρ) hQ
    exact le_trans ((T x).le_rescale hδρ) hQ'
  have hup : (∑ j ∈ s, ((t.filter (fun i => Q j i)).card : NNReal)) ≤ (s.card : NNReal) * M := by
    calc
      (∑ j ∈ s, ((t.filter (fun i => Q j i)).card : NNReal))
          ≤ ∑ j ∈ s, (M : NNReal) := Finset.sum_le_sum (fun j hj =>
              le_trans (Nat.cast_le.mpr (Finset.card_le_card (hinner j))) (hM j hj))
      _ = (s.card : NNReal) * M := by rw [Finset.sum_const, nsmul_eq_mul]
  have hup2 : (∑ j ∈ s, ((t.filter (fun i => Q j i)).card : NNReal))
      ≤ (Λ * (t.card : NNReal)) * M := le_trans hup (mul_le_mul_left hprop M)
  have hchain : (t.card : NNReal) * ((fibreIndex s T δ ρ a).card : NNReal)
      ≤ (t.card : NNReal) * (C₁ * Λ * M) := by
    calc
      (t.card : NNReal) * ((fibreIndex s T δ ρ a).card : NNReal)
          ≤ C₁ * (∑ i ∈ t, ((fibreIndex s T δ ρ i).card : NNReal)) := hlow
      _ = C₁ * (∑ j ∈ s, ((t.filter (fun i => Q j i)).card : NNReal)) := by rw [hswap]
      _ ≤ C₁ * ((Λ * (t.card : NNReal)) * M) := mul_le_mul_right hup2 C₁
      _ = (t.card : NNReal) * (C₁ * Λ * M) := by ring
  have hc : (0 : NNReal) < (t.card : NNReal) := by
    exact_mod_cast Finset.card_pos.mpr htne
  exact le_of_mul_le_mul_left hchain hc

/-- **A uniform bound on the inflated fibres of a uniform family.**  The `4ρ_k`-fibre of an
*arbitrary* anchor is covered by boundedly many exact-scale `ρ_k`-fibres anchored in `t`
(`exists_gapFibre_cover_of_ratio`), and each of those is at most `C ^ 2 · N_k`
(`card_fibreIndex_le_of_uniformTubeSet`).  The anchor `j` is unconstrained, which is what the dual
count needs: there the anchor ranges over the *ambient* family. -/
theorem card_fibreIndex_four_mul_le_of_uniformTubeSet {ι : Type*} {δ : NNReal} {t : Finset ι}
    {T : ι → Tube δ E} {N : ℕ} {Cu : NNReal} (hδ : 0 < δ) (𝒰 : UniformTubeSet t T N Cu)
    {k : ℕ} (hk : k ≤ N) (h2δ : 2 * δ ≤ gridScale δ N k) (j : ι) :
    ((fibreIndex t T δ (4 * gridScale δ N k) j).card : NNReal)
      ≤ fibreCoverConst (E := E) * (Cu ^ 2 * 𝒰.branchingN k) := by
  classical
  let n := Module.finrank ℝ E
  let ρ : NNReal := gridScale δ N k
  have hρpos : 0 < ρ := by
    dsimp [ρ]
    exact gridScale_pos hδ N k
  obtain ⟨A, hAsub, hAcard, hcover⟩ :=
    exists_gapFibre_cover_of_ratio (s := t) (T := T) (δ := δ) (σ := δ) (ρ := ρ)
      (ρ' := 4 * ρ) hρpos le_rfl h2δ (by
        exact le_mul_of_one_le_left (le_of_lt hρpos) (by norm_num : (1 : NNReal) ≤ 4)) j
  have h4 : ((4 * ρ : NNReal) : ℝ) / ((ρ : NNReal) : ℝ) = (4 : ℝ) := by
    have hne : ((ρ : NNReal) : ℝ) ≠ 0 := by
      exact_mod_cast hρpos.ne'
    push_cast
    field_simp
  have hAcardR : (A.card : ℝ) ≤ 2 * (25 : ℝ) ^ (2 * n) * (4 : ℝ) ^ (2 * n) := by
    calc
      (A.card : ℝ)
          ≤ 2 * (25 : ℝ) ^ (2 * n) * (((4 * ρ : NNReal) : ℝ) / ((ρ : NNReal) : ℝ)) ^ (2 * n) := by
              simpa [n] using hAcard
      _ = 2 * (25 : ℝ) ^ (2 * n) * (4 : ℝ) ^ (2 * n) := by rw [h4]
  have hAcardN : (A.card : NNReal) ≤ 2 * (25 : NNReal) ^ (2 * n) * (4 : NNReal) ^ (2 * n) := by
    have := hAcardR
    exact_mod_cast this
  have hAcard_le : (A.card : NNReal) ≤ fibreCoverConst (E := E) := by
    simpa [fibreCoverConst, n] using hAcardN
  have hsub : fibreIndex t T δ (4 * ρ) j ⊆ A.biUnion (fun i₂ => fibreIndex t T δ ρ i₂) := by
    intro i hi
    obtain ⟨i₂, hi₂A, hii₂⟩ := hcover i hi
    exact Finset.mem_biUnion.mpr ⟨i₂, hi₂A, hii₂⟩
  have hcntN : ((fibreIndex t T δ (4 * ρ) j).card : NNReal) ≤
      (∑ i₂ ∈ A, ((fibreIndex t T δ ρ i₂).card : NNReal)) := by
    exact_mod_cast (le_trans (Finset.card_le_card hsub) (Finset.card_biUnion_le
      (s := A) (t := (fun i₂ => fibreIndex t T δ ρ i₂))))
  have hterm : ∀ i₂ ∈ A, ((fibreIndex t T δ ρ i₂).card : NNReal) ≤ Cu ^ 2 * 𝒰.branchingN k := by
    intro i₂ hi₂A
    have hi₂t : i₂ ∈ t := hAsub hi₂A
    simpa [ρ] using (card_fibreIndex_le_of_uniformTubeSet 𝒰 hk hi₂t)
  have hsumle : (∑ i₂ ∈ A, ((fibreIndex t T δ ρ i₂).card : NNReal)) ≤
      (A.card : NNReal) * (Cu ^ 2 * 𝒰.branchingN k) := by
    calc
      (∑ i₂ ∈ A, ((fibreIndex t T δ ρ i₂).card : NNReal))
          ≤ ∑ i₂ ∈ A, (Cu ^ 2 * 𝒰.branchingN k) := Finset.sum_le_sum hterm
      _ = (A.card : NNReal) * (Cu ^ 2 * 𝒰.branchingN k) := by
        rw [Finset.sum_const]
        simp
  calc
    ((fibreIndex t T δ (4 * ρ) j).card : NNReal)
        ≤ (∑ i₂ ∈ A, ((fibreIndex t T δ ρ i₂).card : NNReal)) := hcntN
    _ ≤ (A.card : NNReal) * (Cu ^ 2 * 𝒰.branchingN k) := hsumle
    _ ≤ fibreCoverConst (E := E) * (Cu ^ 2 * 𝒰.branchingN k) := by
        have hnon : (0 : NNReal) ≤ Cu ^ 2 * 𝒰.branchingN k := by positivity
        exact mul_le_mul_of_nonneg_right hAcard_le hnon

/-- **The ambient fibre against the retained class.**  The dual count with the uniform bound of
`card_fibreIndex_four_mul_le_of_uniformTubeSet` inserted for `M`, the comparability of
`comparableFibreCountsInflated_of_isFrostmanAtEveryScale` inserted for `C₁`, and the class lower
bound `𝒰.le_card_class` converting the branching number into a class count. -/
theorem card_fibreIndex_le_mul_card_coverClass_of_proportion {ι : Type*} {δ : NNReal}
    {s t : Finset ι} {T : ι → Tube δ E} {N : ℕ} {Cu A D Λ : NNReal}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδN : δ ≤ (16 : NNReal) ^ (-(N : ℝ)))
    (hts : t ⊆ s) (htne : t.Nonempty) (𝒰 : UniformTubeSet t T N Cu)
    (hFro : IsFrostmanAtGridScales s T N (A : ENNReal))
    (hD : Kakeya.maxDensity s (fun i => (T i).toConvexSpaceBody) ≤ (D : ENNReal))
    (hprop : (s.card : NNReal) ≤ Λ * (t.card : NNReal))
    {k : ℕ} (hk : k < N) {j : ι} (hj : j ∈ 𝒰.cover.indexSet k) {a : ι} (ha : a ∈ s) :
    ((fibreIndex s T δ (gridScale δ N k) a).card : NNReal)
      ≤ (frostmanFibreConst (Module.finrank ℝ E) * A * D * Λ * fibreCoverConst (E := E) * Cu ^ 3)
          * ((coverClass t (𝒰.cover.assign k) j).card : NNReal) := by
  classical
  let ρ := gridScale δ N k
  let n := Module.finrank ℝ E
  let C₁ := frostmanFibreConst n * A * D
  let c := ((coverClass t (𝒰.cover.assign k) j).card : NNReal)
  have hk_le_N : k ≤ N := le_of_lt hk
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le k) hk
  have hδρ : δ ≤ ρ := by
    calc
      δ = gridScale δ N N := (gridScale_self δ hN).symm
      _ ≤ gridScale δ N k := gridScale_antitone hδ hδ1 N hk_le_N
  have h8δ : 8 * δ ≤ ρ := eight_delta_le_gridScale hδ hδ1 hk hδN
  have h2δ : 2 * δ ≤ ρ := by
    refine le_trans (mul_le_mul_of_nonneg_right (by norm_num : (2 : NNReal) ≤ 8) ?_) h8δ
    exact le_of_lt hδ
  have hcomp : ∀ i₀ ∈ s, ∀ i₁ ∈ s,
      ((fibreIndex s T δ ρ i₀).card : NNReal) ≤ C₁ * ((fibreIndex s T δ ρ i₁).card : NNReal) := by
    intro i₀ hi₀ i₁ hi₁
    exact (comparableFibreCountsInflated_of_isFrostmanAtEveryScale hδ hδ1 N hFro hD).1 ρ
      (gridScale_mem_gridScales δ hk_le_N) i₀ hi₀ i₁ hi₁
  have hM : ∀ j ∈ s, ((fibreIndex t T δ (4 * ρ) j).card : NNReal)
      ≤ fibreCoverConst (E := E) * (Cu ^ 2 * 𝒰.branchingN k) := by
    intro j' _
    exact card_fibreIndex_four_mul_le_of_uniformTubeSet hδ 𝒰 hk_le_N h2δ j'
  have h1 : ((fibreIndex s T δ ρ a).card : NNReal)
      ≤ C₁ * Λ * (fibreCoverConst (E := E) * (Cu ^ 2 * 𝒰.branchingN k)) :=
    card_fibreIndex_le_of_global_proportion (hts := hts) (hδρ := hδρ) (htne := htne)
      (hcomp := hcomp) (hM := hM) (hprop := hprop) ha
  have hb : Cu ^ 2 * 𝒰.branchingN k ≤ Cu ^ 3 * c := by
    calc
      Cu ^ 2 * 𝒰.branchingN k ≤ Cu ^ 2 * (Cu * c) := by
        gcongr
        exact 𝒰.le_card_class k hk_le_N j hj
      _ = Cu ^ 3 * c := by ring
  have hring : C₁ * Λ * (fibreCoverConst (E := E) * (Cu ^ 3 * c)) =
      (frostmanFibreConst (Module.finrank ℝ E) * A * D * Λ * fibreCoverConst (E := E) * Cu ^ 3)
        * c := by
    simp only [C₁, c, n]
    ring
  calc
    ((fibreIndex s T δ ρ a).card : NNReal)
        ≤ C₁ * Λ * (fibreCoverConst (E := E) * (Cu ^ 2 * 𝒰.branchingN k)) := h1
    _ ≤ C₁ * Λ * (fibreCoverConst (E := E) * (Cu ^ 3 * c)) := by
      gcongr
    _ = (frostmanFibreConst (Module.finrank ℝ E) * A * D * Λ * fibreCoverConst (E := E) * Cu ^ 3)
          * c := hring

/-- **A mixed fibre density against the node density.**  Verbatim the argument of
`MultiScaleFac.densityIn_fibre_le_mul_densityIn_node`, except that the fibre is taken in the ambient
family and the count hypothesis relating it to the retained class is supplied as `hcard` rather than
read off `card_fibreIndex_le_card_coverClass`. -/
theorem densityIn_fibre_le_mul_densityIn_node_of_card {ι : Type*} {δ : NNReal} {s t : Finset ι}
    {T : ι → Tube δ E} {N : ℕ} {Cu Q : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (𝒰 : UniformTubeSet t T N Cu) {k : ℕ} (hk : k ≤ N) {a j : ι} (hj : j ∈ 𝒰.cover.indexSet k)
    (hcard : ((fibreIndex s T δ (gridScale δ N k) a).card : NNReal)
      ≤ Q * ((coverClass t (𝒰.cover.assign k) j).card : NNReal)) :
    Kakeya.densityIn (fibreIndex s T δ (gridScale δ N k) a)
        (fun i => (T i).toConvexSpaceBody)
        ((T a).rescale (gridScale δ N k)).toConvexSpaceBody
      ≤ (tubeVolRatio (E := E) : ENNReal) ^ 2 * (Q : ENNReal)
          * Kakeya.densityIn (coverClass t (𝒰.cover.assign k) j)
              (fun i => (T i).toConvexSpaceBody) (𝒰.cover.tube k j).toConvexSpaceBody := by
  classical
  set n := Module.finrank ℝ E with hn
  set p := n - 1 with hp
  set ρ : NNReal := gridScale δ N k with hρ_def
  set c : NNReal := Tube.le_volume.c n with hc_def
  set Cn : NNReal := Tube.volume_le.C n with hCn_def
  set r : NNReal := Cn / c with hr_def
  set W : ι → ConvexSpaceBody E := fun i => (T i).toConvexSpaceBody with hW_def
  set cls : Finset ι := coverClass t (𝒰.cover.assign k) j with hcls_def
  set Da : ENNReal := Kakeya.densityIn (fibreIndex s T δ ρ a) W ((T a).rescale ρ).toConvexSpaceBody
    with hDa_def
  set D : ENNReal := Kakeya.densityIn cls W (𝒰.cover.tube k j).toConvexSpaceBody with hD_def
  set X : ENNReal := (c : ENNReal) * (ρ : ENNReal) ^ p with hX_def
  set Y : ENNReal := (c : ENNReal) * (δ : ENNReal) ^ p with hY_def
  set Cρn : ENNReal := (Cn : ENNReal) * (ρ : ENNReal) ^ p with hCρn_def
  set Cδn : ENNReal := (Cn : ENNReal) * (δ : ENNReal) ^ p with hCδn_def
  have hρpos : 0 < ρ := gridScale_pos hδ N k
  have hc_pos : 0 < c := Tube.le_volume.c_pos n
  have hc_ne : c ≠ 0 := ne_of_gt hc_pos
  have hρ_ne_top : (ρ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hδ_ne_top : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hρpn_top : (ρ : ENNReal) ^ p ≠ ⊤ := ENNReal.pow_ne_top hρ_ne_top
  have hδpn_top : (δ : ENNReal) ^ p ≠ ⊤ := ENNReal.pow_ne_top hδ_ne_top
  have hX0 : X ≠ 0 := by
    rw [hX_def]
    exact mul_ne_zero (by exact_mod_cast hc_ne) (pow_ne_zero p (by exact_mod_cast hρpos.ne'))
  have hY0 : Y ≠ 0 := by
    rw [hY_def]
    exact mul_ne_zero (by exact_mod_cast hc_ne) (pow_ne_zero p (by exact_mod_cast hδ.ne'))
  have hX_top : X ≠ ⊤ := by
    rw [hX_def]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top hρpn_top
  have hY_top : Y ≠ ⊤ := by
    rw [hY_def]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top hδpn_top
  have hXY0 : X * Y ≠ 0 := mul_ne_zero hX0 hY0
  have hXY_top : X * Y ≠ ⊤ := ENNReal.mul_ne_top hX_top hY_top
  have hband_f : Da * X ≤ ((fibreIndex s T δ ρ a).card : ENNReal) * Cδn := by
    have hb := densityIn_fibre_mul_le_card (s := s) (T := T) (σ := δ) hδ1 ρ a
    simpa [W, X, Cδn, fibreBodies_self, hc_def, hCn_def, hρ_def]
      using hb
  have h_ka : ((fibreIndex s T δ ρ a).card : ENNReal) ≤ (Q : ENNReal) * (cls.card : ENNReal) := by
    exact_mod_cast hcard
  have hband_g : Da * X ≤ (Q : ENNReal) * (cls.card : ENNReal) * Cδn := by
    calc
      Da * X ≤ ((fibreIndex s T δ ρ a).card : ENNReal) * Cδn := hband_f
      _ ≤ ((Q : ENNReal) * (cls.card : ENNReal)) * Cδn :=
          mul_le_mul_left h_ka Cδn
      _ = (Q : ENNReal) * (cls.card : ENNReal) * Cδn := by
          ring
  have hband_h : (cls.card : ENNReal) * Y ≤ D * Cρn := by
    have hb := card_coverClass_mul_le_densityIn_node hδ hδ1 𝒰 hk hj
    simpa [W, Y, Cρn, hc_def, hCn_def, hρ_def, hD_def, hcls_def] using hb
  have hchain : Da * (X * Y) ≤ (Q : ENNReal) * D * (Cρn * Cδn) := by
    calc
      Da * (X * Y) = (Da * X) * Y := by ring
      _ ≤ ((Q : ENNReal) * (cls.card : ENNReal) * Cδn) * Y :=
          mul_le_mul_left hband_g Y
      _ = (Q : ENNReal) * (cls.card : ENNReal) * (Cδn * Y) := by
          ring
      _ = (Q : ENNReal) * ((cls.card : ENNReal) * Y) * Cδn := by
          ring
      _ ≤ (Q : ENNReal) * (D * Cρn) * Cδn := by
          exact mul_le_mul_left (mul_le_mul_right hband_h ((Q : ENNReal))) Cδn
      _ = (Q : ENNReal) * D * (Cρn * Cδn) := by ring
  have hq : r * c = Cn := by
    dsimp [r]
    exact div_mul_cancel₀ Cn hc_ne
  have hscale : (Cn * ρ ^ p) * (Cn * δ ^ p)
      = r ^ 2 * (c * ρ ^ p) * (c * δ ^ p) := by
    calc
      (Cn * ρ ^ p) * (Cn * δ ^ p) = Cn ^ 2 * (ρ ^ p * δ ^ p) := by ring
      _ = (r * c) ^ 2 * (ρ ^ p * δ ^ p) := by rw [hq]
      _ = r ^ 2 * (c * ρ ^ p) * (c * δ ^ p) := by ring
  have hcast : Cρn * Cδn = (r : ENNReal) ^ 2 * (X * Y) := by
    dsimp [Cρn, Cδn, X, Y]
    simpa [mul_assoc, mul_left_comm, mul_comm]
      using congrArg (fun z : NNReal => (z : ENNReal)) hscale
  have hstep : Da * (X * Y) ≤ ((r : ENNReal) ^ 2 * (Q : ENNReal) * D) * (X * Y) := by
    calc
      Da * (X * Y) ≤ (Q : ENNReal) * D * (Cρn * Cδn) := hchain
      _ = (Q : ENNReal) * D * ((r : ENNReal) ^ 2 * (X * Y)) := by rw [hcast]
      _ = (r : ENNReal) ^ 2 * (Q : ENNReal) * D * (X * Y) := by ring
  have hcancel : Da ≤ (r : ENNReal) ^ 2 * (Q : ENNReal) * D := by
    exact (ENNReal.mul_le_mul_iff_right hXY0 hXY_top).mp
      (by simpa [mul_assoc, mul_left_comm, mul_comm] using hstep)
  simpa [tubeVolRatio, W, Da, D, hn, hp, hr_def, hρ_def] using hcancel

/-- **The mixed workhorse.**  Leaf-anchored Frostman on the *ambient* family, plus the ambient
fibre/retained class count bound, give node-reading Frostman for the classes of a hierarchy carried
by the subfamily.  This is `MultiScaleFac.isFrostmanIn_coverClass_of_fibre` with the fibre side
moved to `s`; the class still sits inside a `4ρ_k`-fibre of one of its members, and that fibre is
covered by boundedly many ambient exact-scale fibres. -/
theorem isFrostmanIn_coverClass_of_ambient_fibre {ι : Type*} {δ : NNReal} {s t : Finset ι}
    {T : ι → Tube δ E} {N : ℕ} {Cu Q : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hts : t ⊆ s)
    (𝒰 : UniformTubeSet t T N Cu) {k : ℕ} (hk : k ≤ N) (h2δ : 2 * δ ≤ gridScale δ N k)
    {j : ι} (hj : j ∈ 𝒰.cover.indexSet k) (htne : t.Nonempty) {B : ENNReal}
    (hB : ∀ a ∈ s, ConvexSpaceBody.IsFrostmanIn (fibreIndex s T δ (gridScale δ N k) a)
      (fun i => (T i).toConvexSpaceBody)
      ((T a).rescale (gridScale δ N k)).toConvexSpaceBody B)
    (hQ : ∀ a ∈ s, ((fibreIndex s T δ (gridScale δ N k) a).card : NNReal)
      ≤ Q * ((coverClass t (𝒰.cover.assign k) j).card : NNReal)) :
    ConvexSpaceBody.IsFrostmanIn (coverClass t (𝒰.cover.assign k) j)
      (fun i => (T i).toConvexSpaceBody) (𝒰.cover.tube k j).toConvexSpaceBody
      ((nodeClassConst (E := E) : ENNReal) * (Q : ENNReal) * B) := by
  classical
  set n := Module.finrank ℝ E with hn
  set D : ENNReal := Kakeya.densityIn (coverClass t (𝒰.cover.assign k) j)
    (fun i => (T i).toConvexSpaceBody) (𝒰.cover.tube k j).toConvexSpaceBody with hD
  intro K' _
  refine le_trans (Kakeya.le_maxDensity _ _ K') ?_
  obtain ⟨i₀, hi₀cls⟩ := coverClass_nonempty_of_mem_parent 𝒰 hk htne hj
  have hi₀t : i₀ ∈ t := by
    simp only [coverClass, Finset.mem_filter] at hi₀cls
    exact hi₀cls.1
  have hassign : 𝒰.cover.assign k i₀ = j := by
    simp only [coverClass, Finset.mem_filter] at hi₀cls
    exact hi₀cls.2
  have hclsSub : coverClass t (𝒰.cover.assign k) j
      ⊆ fibreIndex s T δ (4 * gridScale δ N k) i₀ := by
    have h1 : coverClass t (𝒰.cover.assign k) (𝒰.cover.assign k i₀)
        ⊆ fibreIndex t T δ (4 * gridScale δ N k) i₀ :=
      coverClass_subset_fibreIndex 𝒰 hk hi₀t
    have h2 : coverClass t (𝒰.cover.assign k) j
        ⊆ fibreIndex t T δ (4 * gridScale δ N k) i₀ := by
      rwa [hassign] at h1
    exact h2.trans (by
      rw [fibreIndex_self, fibreIndex_self]
      exact Finset.filter_subset_filter
        (fun i => (T i).toConvexSpaceBody
          ≤ ((T i₀).rescale (4 * gridScale δ N k)).toConvexSpaceBody)
        hts)
  have hρpos : 0 < gridScale δ N k := gridScale_pos hδ N k
  obtain ⟨A, hAs, hAcard, hAcov⟩ :=
    exists_gapFibre_cover_of_ratio (s := s) (T := T) (δ := δ) (σ := δ)
      (ρ := gridScale δ N k) (ρ' := 4 * gridScale δ N k) hρpos le_rfl h2δ
      (by
        have h0 : (0 : NNReal) ≤ gridScale δ N k := le_of_lt hρpos
        exact le_mul_of_one_le_left h0 (by norm_num : (1 : NNReal) ≤ 4)) i₀
  have hsubBi : coverClass t (𝒰.cover.assign k) j
      ⊆ A.biUnion (fun a => fibreIndex s T δ (gridScale δ N k) a) := by
    intro i hi
    obtain ⟨i₂, hi₂A, hi₂⟩ := hAcov i (hclsSub hi)
    exact Finset.mem_biUnion.mpr ⟨i₂, hi₂A, hi₂⟩
  have hmax := maxDensity_le_sum_of_subset_biUnion
    (W := fun i => (T i).toConvexSpaceBody) hsubBi
  have hterm : ∀ a ∈ A,
      Kakeya.maxDensity (fibreIndex s T δ (gridScale δ N k) a)
          (fun i => (T i).toConvexSpaceBody)
        ≤ B * ((tubeVolRatio (E := E) : ENNReal) ^ 2 * (Q : ENNReal) * D) := by
    intro a haA
    have has : a ∈ s := hAs haA
    have hmem : ∀ i ∈ fibreIndex s T δ (gridScale δ N k) a,
        (fun i => (T i).toConvexSpaceBody) i
          ≤ ((T a).rescale (gridScale δ N k)).toConvexSpaceBody := by
      intro i hi
      rw [fibreIndex_self] at hi
      exact (Finset.mem_filter.mp hi).2
    have h1 := ConvexSpaceBody.IsFrostmanIn.maxDensity_le_of_carrier_subset (hB a has) hmem
    have h2 := densityIn_fibre_le_mul_densityIn_node_of_card hδ hδ1 𝒰 hk hj (hQ a has)
    exact h1.trans (mul_le_mul_right h2 B)
  have hsum : (∑ a ∈ A, Kakeya.maxDensity (fibreIndex s T δ (gridScale δ N k) a)
        (fun i => (T i).toConvexSpaceBody))
      ≤ (A.card : ENNReal) * (B * ((tubeVolRatio (E := E) : ENNReal) ^ 2 * (Q : ENNReal) * D)) := by
    calc (∑ a ∈ A, Kakeya.maxDensity (fibreIndex s T δ (gridScale δ N k) a)
            (fun i => (T i).toConvexSpaceBody))
        ≤ ∑ _a ∈ A, B * ((tubeVolRatio (E := E) : ENNReal) ^ 2 * (Q : ENNReal) * D) :=
          Finset.sum_le_sum hterm
      _ = (A.card : ENNReal)
            * (B * ((tubeVolRatio (E := E) : ENNReal) ^ 2 * (Q : ENNReal) * D)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hAcardE : (A.card : ENNReal)
      ≤ ((2 * (25 : NNReal) ^ (2 * n) * (4 : NNReal) ^ (2 * n) : NNReal) : ENNReal) := by
    have hAcardR : (A.card : ℝ) ≤ 2 * (25 : ℝ) ^ (2 * n) * (4 : ℝ) ^ (2 * n) := by
      have h4 : ((4 * gridScale δ N k : NNReal) : ℝ) / ((gridScale δ N k : NNReal) : ℝ)
          = (4 : ℝ) := by
        have hne : ((gridScale δ N k : NNReal) : ℝ) ≠ 0 := by
          exact_mod_cast hρpos.ne'
        push_cast
        field_simp
      calc (A.card : ℝ)
          ≤ 2 * (25 : ℝ) ^ (2 * n)
              * (((4 * gridScale δ N k : NNReal) : ℝ) / ((gridScale δ N k : NNReal) : ℝ))
                ^ (2 * n) := by simpa [hn] using hAcard
        _ = 2 * (25 : ℝ) ^ (2 * n) * (4 : ℝ) ^ (2 * n) := by rw [h4]
    have hAcardN : (A.card : NNReal) ≤ 2 * (25 : NNReal) ^ (2 * n) * (4 : NNReal) ^ (2 * n) := by
      have := hAcardR
      exact_mod_cast this
    exact_mod_cast hAcardN
  refine hmax.trans (hsum.trans ?_)
  have hunfold : (nodeClassConst (E := E) : ENNReal)
      = ((2 * (25 : NNReal) ^ (2 * n) * (4 : NNReal) ^ (2 * n) : NNReal) : ENNReal)
          * ((tubeVolRatio (E := E) : NNReal) : ENNReal) ^ 2 := by
    simp only [nodeClassConst, tubeVolRatio]
    push_cast
    ring
  rw [hunfold]
  calc (A.card : ENNReal) * (B * ((tubeVolRatio (E := E) : ENNReal) ^ 2 * (Q : ENNReal) * D))
      ≤ ((2 * (25 : NNReal) ^ (2 * n) * (4 : NNReal) ^ (2 * n) : NNReal) : ENNReal)
          * (B * ((tubeVolRatio (E := E) : ENNReal) ^ 2 * (Q : ENNReal) * D)) := by
        exact mul_le_mul_left hAcardE _
    _ = ((2 * (25 : NNReal) ^ (2 * n) * (4 : NNReal) ^ (2 * n) : NNReal) : ENNReal)
          * ((tubeVolRatio (E := E) : ENNReal) ^ 2) * (Q : ENNReal) * B * D := by
        ring

/-- **Node-reading Frostman for a uniformized subfamily.**  If ambient `s` is Frostman at every
scale with constant `A` and has `maxDensity ≤ D`, and `t ⊆ s` carries a uniform hierarchy `𝒰`
retaining a `Λ`-proportion of `s`, then the *nodes* of `𝒰` are Frostman with the explicit constant
`nodeClassConst · fibreCoverConst · frostmanFibreConst n · Cu ^ 3 · Λ · A ^ 2 · D`, capped below by
`tubeVolRatio`.  The ambient constant `A` appears squared because it is spent twice. -/
theorem isFrostmanAtEveryScale_nodes_of_ambient_fibre {ι : Type*} {δ : NNReal} {s t : Finset ι}
    {T : ι → Tube δ E} {N : ℕ} {Cu A D Λ : NNReal}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hN : 0 < N) (hδN : δ ≤ (16 : NNReal) ^ (-(N : ℝ)))
    (hts : t ⊆ s) (htne : t.Nonempty) (𝒰 : UniformTubeSet t T N Cu)
    (hFro : IsFrostmanAtGridScales s T N (A : ENNReal))
    (hD : Kakeya.maxDensity s (fun i => (T i).toConvexSpaceBody) ≤ (D : ENNReal))
    (hprop : (s.card : ℝ) ≤ (Λ : ℝ) * (t.card : ℝ)) :
    𝒰.IsFrostmanAtEveryScale
      (max ((nodeClassConst (E := E) * fibreCoverConst (E := E)
              * frostmanFibreConst (Module.finrank ℝ E) * Cu ^ 3 * Λ * A ^ 2 * D : NNReal) :
            ENNReal)
        (tubeVolRatio (E := E) : ENNReal)) := by
  have hpropN : (s.card : NNReal) ≤ Λ * (t.card : NNReal) := by
    exact_mod_cast hprop
  intro k hk j hj
  rcases Nat.lt_or_ge k N with hkN | hkN
  · have h8 : 8 * δ ≤ gridScale δ N k := eight_delta_le_gridScale hδ hδ1 hkN hδN
    have h2 : 2 * δ ≤ gridScale δ N k := by
      refine le_trans (mul_le_mul_of_nonneg_right (by norm_num : (2 : NNReal) ≤ 8) ?_) h8
      exact le_of_lt hδ
    have hB : ∀ a ∈ s, ConvexSpaceBody.IsFrostmanIn (fibreIndex s T δ (gridScale δ N k) a)
        (fun i => (T i).toConvexSpaceBody)
        ((T a).rescale (gridScale δ N k)).toConvexSpaceBody (A : ENNReal) :=
      fun a ha => hFro.isFrostmanIn_fibre hk ha
    set Q : NNReal := frostmanFibreConst (Module.finrank ℝ E) * A * D * Λ
      * fibreCoverConst (E := E) * Cu ^ 3
    have hQ : ∀ a ∈ s, ((fibreIndex s T δ (gridScale δ N k) a).card : NNReal)
        ≤ Q * ((coverClass t (𝒰.cover.assign k) j).card : NNReal) := by
      intro a ha
      simpa [Q] using
        (card_fibreIndex_le_mul_card_coverClass_of_proportion (hδ := hδ) (hδ1 := hδ1)
          (hδN := hδN) (hts := hts) (htne := htne) (𝒰 := 𝒰) (hFro := hFro) (hD := hD)
          (hprop := hpropN) (hk := hkN) (hj := hj) (ha := ha))
    have hQeq : nodeClassConst (E := E) * Q * A =
        nodeClassConst (E := E) * fibreCoverConst (E := E)
          * frostmanFibreConst (Module.finrank ℝ E) * Cu ^ 3 * Λ * A ^ 2 * D := by
      dsimp [Q]
      ring
    have hconst : (nodeClassConst (E := E) : ENNReal) * (Q : ENNReal) * (A : ENNReal) =
        (nodeClassConst (E := E) * fibreCoverConst (E := E)
          * frostmanFibreConst (Module.finrank ℝ E) * Cu ^ 3 * Λ * A ^ 2 * D : NNReal) := by
      exact_mod_cast hQeq
    exact isFrostmanIn_mono_helper (E := E)
      (isFrostmanIn_coverClass_of_ambient_fibre hδ hδ1 hts 𝒰 hk h2 hj htne hB hQ)
      (by
        calc
          (nodeClassConst (E := E) : ENNReal) * (Q : ENNReal) * (A : ENNReal)
              = (nodeClassConst (E := E) * fibreCoverConst (E := E)
                  * frostmanFibreConst (Module.finrank ℝ E) * Cu ^ 3 * Λ * A ^ 2 * D :
                  NNReal) := hconst
          _ ≤ max ((nodeClassConst (E := E) * fibreCoverConst (E := E)
                    * frostmanFibreConst (Module.finrank ℝ E) * Cu ^ 3 * Λ * A ^ 2 * D : NNReal) :
                  ENNReal)
                (tubeVolRatio (E := E) : ENNReal) := le_max_left _ _)
  · have hkcreq : k = N := le_antisymm hk hkN
    subst hkcreq
    exact isFrostmanIn_mono_helper (E := E)
      (isFrostmanIn_coverClass_bottom hδ hδ1 hN 𝒰 hj) (le_max_right _ _)

end StickyKakeya

end Kakeya
