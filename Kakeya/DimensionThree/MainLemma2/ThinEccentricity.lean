/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Frostman
public import Kakeya.Thickness.ConvexSpaceBody

/-!
# The eccentricity exponent of GWZ Item 2

`ShadedBody.lambdaForInducedShading_of_measurable`, and hence
`Kakeya.ThinCase.fullness_ge_three_eta`, asks for an exponent `N` with
`|W_j| ≤ 2 ^ N · |Y_p|` for every `p` in the fibre over `j` — the *eccentricity* hypothesis
`hecc`. It was the last input of conjunct (i) of `Kakeya.ThinCase.factoringApply` with no
supplier, and it is not an extra assumption: both halves are already in the tree and had simply
never been composed.

* `Kakeya.ThinCase.Produce.volume_carrier_le_of_isFrostmanIn` turns clause (C4), the Frostman
  hypothesis `hFr`, into `|W_j| ≤ C_F · ∑_{q ∈ fibre} |Y_q|`;
* `ConvexSpaceBody.volume_le_of_thickness_le` turns clause (C3) — which is `hdims` **verbatim**,
  `thickness ℝ (Y p).carrier ≤ 2 • thickness ℝ (Y q).carrier` — into
  `|Y_q| ≤ volume_comparison.C n · |Y_p|`.

So `N ≈ log₂ (C_F · |segs| · volume_comparison.C n)`, which is exactly the shape the `hCcoreFrost`
and `hCcoreRef` binders of `factoringApply` are sized for: `log₂ C_F` is what `hCcoreFrost` pays
for and `log₂ |segs|` is what `hCcoreRef` already forces.

**Position in the import graph.** This file sits *below*
`Kakeya.DimensionThree.MainLemma2.ThinSetup`, which is what lets `factoringApply` use
`exists_eccentricity_exponent` in its own proof. That required relocating
`Kakeya.ThinCase.Produce.volume_carrier_le_of_isFrostmanIn`, which was stated in
`ThinProduceParts`: that file genuinely depends on `ThinSetup` (`blockOuterBody`,
`centredMultConstant` — checked by building it with the import removed), so the declaration, not
the file, had to move. It moved here rather than into a new file because this is its only
consumer, and it brought no new dependency with it: its proof uses only `Kakeya.densityIn`,
`Kakeya.densityIn_of_all_le` and `ConvexSpaceBody.IsFrostmanIn`, so `Kakeya.Frostman` replaces the
`ThinProduceParts` import outright. The namespace `Kakeya.ThinCase.Produce` is unchanged, so every
reference to it reads the same.
-/

@[expose] public section

open MeasureTheory Metric Set ShadedBody
open scoped ENNReal NNReal

namespace Kakeya.ThinCase

namespace Produce

section Frostman

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **The eccentricity bridge of the Frostman constant.**

If every member of the family `V` sits inside the test body `K`, if the family is `CF`-Frostman
in `K`, and if some member has positive volume, then `K` itself is no larger than `CF` times the
total carrier volume of the family.

This is what the Frostman clause (C4) of Configuration `hyp:ml2setup` buys in
`Kakeya.ThinCase.factoringApply`: it is applied with `V = fun p => (Y p).toConvexSpaceBody`,
`s = segs.filter (blk · = j)` and `K = Wb j`, and it converts the input fullness hypothesis
`δ^η ≤ Cfull * fullness segs Y`, which is a statement about the segments, into control of the
denominator `∑ j ∈ bodies', volume (W j).carrier` of conclusion (i), which is a statement about
the bodies. Without a hypothesis of this kind conclusion (i) is false: a single fully shaded
segment inside an arbitrarily large body has `fullness segs Y = 1` and
`fullness bodies' W` arbitrarily small.

The test body used is the member `V p` itself, which is legitimate because `V p ≤ K`; the density
of the family in it is at least `1`. -/
theorem volume_carrier_le_of_isFrostmanIn {ι : Type*} {s : Finset ι} {V : ι → ConvexSpaceBody E}
    {K : ConvexSpaceBody E} {CF : ENNReal} (hFr : ConvexSpaceBody.IsFrostmanIn s V K CF)
    (hVK : ∀ i ∈ s, V i ≤ K) {p : ι} (hp : p ∈ s) (hpos : volume (V p).carrier ≠ 0) :
    volume K.carrier ≤ CF * ∑ i ∈ s, volume (V i).carrier := by
  classical
  have hptop : volume (V p).carrier ≠ ⊤ := (V p).isCompact.measure_ne_top
  -- the density of the family in the test body `V p` is at least one
  have hone : (1 : ENNReal) ≤ Kakeya.densityIn s V (V p) := by
    have hmem : p ∈ {i ∈ s | V i ≤ V p} := Finset.mem_filter.mpr ⟨hp, le_rfl⟩
    have hsum : volume (V p).carrier ≤ ∑ i ∈ s with V i ≤ V p, volume (V i).carrier :=
      Finset.single_le_sum (f := fun i => volume (V i).carrier) (fun _ _ => zero_le) hmem
    rw [Kakeya.densityIn, ENNReal.le_div_iff_mul_le (Or.inl hpos) (Or.inl hptop),
      one_mul]
    exact hsum
  -- Frostman compares it with the density in `K`
  have hK : Kakeya.densityIn s V K =
      (∑ i ∈ s, volume (V i).carrier) / volume K.carrier :=
    Kakeya.densityIn_of_all_le hVK
  have hFr' := hFr (V p) (hVK p hp)
  rw [hK] at hFr'
  have hchain : (1 : ENNReal) ≤ CF * ((∑ i ∈ s, volume (V i).carrier) / volume K.carrier) :=
    le_trans hone hFr'
  rcases eq_or_ne (volume K.carrier) 0 with hK0 | hK0
  · simp [hK0]
  · have hKtop : volume K.carrier ≠ ⊤ := K.isCompact.measure_ne_top
    rw [← mul_div_assoc] at hchain
    rw [ENNReal.le_div_iff_mul_le (Or.inl hK0) (Or.inl hKtop), one_mul] at hchain
    exact hchain

end Frostman

end Produce

section Eccentricity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **An explicit power-of-two dominator, logarithmic in its argument.** `N = ⌊log₂ ⌈x⌉₊⌋ + 1`
bits suffice, because `x ≤ ⌈x⌉₊ < 2 ^ (⌊log₂ ⌈x⌉₊⌋ + 1)` (`Nat.lt_pow_succ_log_self`), and no more
are spent: `2 ^ N ≤ 2 (x + 1)` (`Kakeya.ThinCase.two_pow_twoPowExponent_le`). The logarithmic size
is load-bearing: `N` is the eccentricity exponent of GWZ Item 2 — the number of dyadic classes of
the volume ratio `|W_j| / |Y_p| ∈ [1, C_F · |segs| · C_vol]` — and it enters
`Kakeya.ThinCase.thinEnvelopeTerm` as the explicit factor `N + 1` and through the carrier-weighted
Step 1 loss `log₂ (|segs| · C_vol · 2 ^ N)`. The earlier body `⌈x⌉₊` made that envelope, and with it
the constant of `Kakeya.VeryNotSticky.exists_thinConfig`, *linear* in `|segs|`; GWZ's thin configuration is an `≈ 1` refinement.

The explicit form matters downstream: `Kakeya.ThinCase.thinVolumeRatio` feeds this exponent to
`ShadedBody.OuterInnerVolumeRatio`, and every `AtScale` loss constant is a function of
`D.exponent`. A `Exists.choose` exponent is not nameable in the statement of
`Kakeya.ThinCase.factoringApply`, so its `Ccore` envelope could not mention the pipeline's own
retention constant at all. -/
noncomputable def twoPowExponent (x : NNReal) : ℕ := Nat.log 2 ⌈(x : ℝ)⌉₊ + 1

lemma le_two_pow_twoPowExponent (x : NNReal) : x ≤ 2 ^ twoPowExponent x := by
  have h0 : (x : ℝ) ≤ (⌈(x : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
  have h1 : ⌈(x : ℝ)⌉₊ < 2 ^ (Nat.log 2 ⌈(x : ℝ)⌉₊ + 1) :=
    Nat.lt_pow_succ_log_self one_lt_two _
  have h1' : ((⌈(x : ℝ)⌉₊ : ℕ) : ℝ) < 2 ^ twoPowExponent x := by
    unfold twoPowExponent; exact_mod_cast h1
  have : (x : ℝ) ≤ 2 ^ twoPowExponent x := le_of_lt (lt_of_le_of_lt h0 h1')
  exact_mod_cast this

/-- The exponent is logarithmic: `2 ^ N ≤ 2 (x + 1)`, i.e. `N ≤ log₂ (x + 1) + 1`. This is the upper
bound the polylog sizing of `Kakeya.ThinCase.thinEnvelopeTerm` reads. -/
lemma two_pow_twoPowExponent_le (x : NNReal) :
    (2 : NNReal) ^ twoPowExponent x ≤ 2 * (x + 1) := by
  unfold twoPowExponent
  rcases Nat.eq_zero_or_pos ⌈(x : ℝ)⌉₊ with h0 | hpos
  · rw [h0]; simp
  · have hpow : 2 ^ Nat.log 2 ⌈(x : ℝ)⌉₊ ≤ ⌈(x : ℝ)⌉₊ := Nat.pow_log_le_self 2 hpos.ne'
    have hceil : (⌈(x : ℝ)⌉₊ : ℝ) < (x : ℝ) + 1 := Nat.ceil_lt_add_one x.coe_nonneg
    have hceil' : ((⌈(x : ℝ)⌉₊ : ℕ) : NNReal) ≤ x + 1 := by
      rw [← NNReal.coe_le_coe]; push_cast; exact hceil.le
    calc (2 : NNReal) ^ (Nat.log 2 ⌈(x : ℝ)⌉₊ + 1)
        = 2 * ((2 ^ Nat.log 2 ⌈(x : ℝ)⌉₊ : ℕ) : NNReal) := by push_cast; ring
      _ ≤ 2 * ((⌈(x : ℝ)⌉₊ : ℕ) : NNReal) := by gcongr
      _ ≤ 2 * (x + 1) := by gcongr

/-- Monotone in its argument (for `Finset.sup`-style envelopes). -/
lemma twoPowExponent_mono : Monotone twoPowExponent := by
  intro x y hxy
  unfold twoPowExponent
  exact Nat.succ_le_succ (Nat.log_mono_right (Nat.ceil_mono (NNReal.coe_le_coe.mpr hxy)))

/-- The `⌊log₂ ·⌋₊ + 1` form read by `Tube.exists_threshold_polylog_pow_ssfGridLen_le`, at
`c = ⌈x⌉₊`. -/
lemma twoPowExponent_eq_natFloor_logb (x : NNReal) :
    twoPowExponent x = ⌊Real.logb 2 ((⌈(x : ℝ)⌉₊ : ℕ) : ℝ)⌋₊ + 1 := by
  unfold twoPowExponent
  have h := Real.natFloor_logb_natCast 2 ⌈(x : ℝ)⌉₊
  push_cast at h
  rw [h]

/-- Every `NNReal` is dominated by a power of two. -/
lemma exists_two_pow_ge (x : NNReal) : ∃ N : ℕ, x ≤ 2 ^ N :=
  ⟨twoPowExponent x, le_two_pow_twoPowExponent x⟩

open Classical in
/-- **The eccentricity bound of GWZ Item 2, from the hypotheses `factoringApply` already
carries.**

`ShadedBody.lambdaForInducedShading_of_measurable` — and so
`Kakeya.ThinCase.fullness_ge_three_eta` — asks for an exponent `N` with
`|W_j| ≤ 2 ^ N |Y_p|` for every `p` in the fibre over `j`. The two halves are both in the tree
and neither was previously composed: `Kakeya.ThinCase.Produce.volume_carrier_le_of_isFrostmanIn`
turns the Frostman clause (C4) into `|W_j| ≤ C_F ∑_{q ∈ fibre} |Y_q|`, and
`ConvexSpaceBody.volume_le_of_thickness_le` turns the comparable-thickness clause (C3) — which is
`hdims` verbatim — into `|Y_q| ≤ volume_comparison.C n · |Y_p|`. So
`N ≈ log₂ (C_F · |segs| · volume_comparison.C n)`, which is the shape
`Kakeya.ThinCase.factoringApply`'s `hCcoreFrost` and `hCcoreRef` binders are sized for. -/
theorem eccentricity_exponent_bound [Nontrivial E] {ι κ : Type*} (segs : Finset ι)
    (Y : ι → ShadedBody E)
    (bodies : Finset κ) (Wb : κ → ConvexSpaceBody E) (blk : ι → κ) {CF : NNReal}
    (hle : ∀ p ∈ segs, (Y p).toConvexSpaceBody ≤ Wb (blk p))
    (hdims : ∀ p ∈ segs, ∀ q ∈ segs,
      Metric.thickness ℝ (Y p).carrier ≤ 2 • Metric.thickness ℝ (Y q).carrier)
    (hFr : ∀ j ∈ bodies, ConvexSpaceBody.IsFrostmanIn {p ∈ segs | blk p = j}
      (fun p => (Y p).toConvexSpaceBody) (Wb j) (CF : ENNReal))
    (hVpos : ∀ p ∈ segs, volume (Y p).carrier ≠ 0) :
    ∀ j ∈ bodies, ∀ p ∈ segs, blk p = j →
      volume (Wb j).carrier ≤
        2 ^ twoPowExponent
            (CF * (segs.card : NNReal) * Metric.volume_comparison.C (Module.finrank ℝ E)) *
          volume (Y p).carrier := by
  classical
  set N : ℕ := twoPowExponent
    (CF * (segs.card : NNReal) * Metric.volume_comparison.C (Module.finrank ℝ E)) with hNdef
  have hN : CF * (segs.card : NNReal) * Metric.volume_comparison.C (Module.finrank ℝ E) ≤ 2 ^ N :=
    le_two_pow_twoPowExponent _
  refine fun j hj p hp hpj => ?_
  set t : Finset ι := {q ∈ segs | blk q = j} with ht
  have hpt : p ∈ t := Finset.mem_filter.mpr ⟨hp, hpj⟩
  have hVK : ∀ q ∈ t, (Y q).toConvexSpaceBody ≤ Wb j := by
    intro q hq
    obtain ⟨hqs, hqj⟩ := Finset.mem_filter.mp hq
    rw [← hqj]
    exact hle q hqs
  have hfrost := Produce.volume_carrier_le_of_isFrostmanIn (hFr j hj) hVK hpt (hVpos p hp)
  have hper : ∀ q ∈ t, volume (Y q).carrier
      ≤ (Metric.volume_comparison.C (Module.finrank ℝ E) : ENNReal) * volume (Y p).carrier := by
    intro q hq
    have hqs : q ∈ segs := (Finset.mem_filter.mp hq).1
    exact ConvexSpaceBody.volume_le_of_thickness_le (W := (Y q).toConvexSpaceBody)
      (W' := (Y p).toConvexSpaceBody) (hdims q hqs p hp)
  have hsum : ∑ q ∈ t, volume (Y q).carrier
      ≤ (t.card : ENNReal) *
        ((Metric.volume_comparison.C (Module.finrank ℝ E) : ENNReal) * volume (Y p).carrier) := by
    calc ∑ q ∈ t, volume (Y q).carrier
        ≤ ∑ _q ∈ t, (Metric.volume_comparison.C (Module.finrank ℝ E) : ENNReal) *
            volume (Y p).carrier := Finset.sum_le_sum hper
      _ = (t.card : ENNReal) *
            ((Metric.volume_comparison.C (Module.finrank ℝ E) : ENNReal) *
              volume (Y p).carrier) := by rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : (t.card : ENNReal) ≤ ((segs.card : ℕ) : ENNReal) := by
    exact_mod_cast Finset.card_le_card (ht ▸ Finset.filter_subset _ _)
  have hNE : ((CF : ENNReal) * ((segs.card : ℕ) : ENNReal) *
      (Metric.volume_comparison.C (Module.finrank ℝ E) : ENNReal)) ≤ 2 ^ N := by
    have := hN
    calc (CF : ENNReal) * ((segs.card : ℕ) : ENNReal) *
          (Metric.volume_comparison.C (Module.finrank ℝ E) : ENNReal)
        = ((CF * (segs.card : NNReal) *
            Metric.volume_comparison.C (Module.finrank ℝ E) : NNReal) : ENNReal) := by
          push_cast; ring
      _ ≤ ((2 ^ N : NNReal) : ENNReal) := by exact_mod_cast this
      _ = 2 ^ N := by push_cast; ring
  calc volume (Wb j).carrier
      ≤ (CF : ENNReal) * ∑ q ∈ t, volume (Y q).carrier := hfrost
    _ ≤ (CF : ENNReal) * ((t.card : ENNReal) *
          ((Metric.volume_comparison.C (Module.finrank ℝ E) : ENNReal) *
            volume (Y p).carrier)) := mul_le_mul' le_rfl hsum
    _ ≤ (CF : ENNReal) * (((segs.card : ℕ) : ENNReal) *
          ((Metric.volume_comparison.C (Module.finrank ℝ E) : ENNReal) *
            volume (Y p).carrier)) := mul_le_mul' le_rfl (mul_le_mul' hcard le_rfl)
    _ = ((CF : ENNReal) * ((segs.card : ℕ) : ENNReal) *
          (Metric.volume_comparison.C (Module.finrank ℝ E) : ENNReal)) *
            volume (Y p).carrier := by ring
    _ ≤ 2 ^ N * volume (Y p).carrier := mul_le_mul' hNE le_rfl

open Classical in
/-- The existential form, kept for callers that do not need the exponent by name. -/
theorem exists_eccentricity_exponent [Nontrivial E] {ι κ : Type*} (segs : Finset ι)
    (Y : ι → ShadedBody E)
    (bodies : Finset κ) (Wb : κ → ConvexSpaceBody E) (blk : ι → κ) {CF : NNReal}
    (hle : ∀ p ∈ segs, (Y p).toConvexSpaceBody ≤ Wb (blk p))
    (hdims : ∀ p ∈ segs, ∀ q ∈ segs,
      Metric.thickness ℝ (Y p).carrier ≤ 2 • Metric.thickness ℝ (Y q).carrier)
    (hFr : ∀ j ∈ bodies, ConvexSpaceBody.IsFrostmanIn {p ∈ segs | blk p = j}
      (fun p => (Y p).toConvexSpaceBody) (Wb j) (CF : ENNReal))
    (hVpos : ∀ p ∈ segs, volume (Y p).carrier ≠ 0) :
    ∃ N : ℕ, ∀ j ∈ bodies, ∀ p ∈ segs, blk p = j →
      volume (Wb j).carrier ≤ 2 ^ N * volume (Y p).carrier :=
  ⟨_, eccentricity_exponent_bound segs Y bodies Wb blk hle hdims hFr hVpos⟩

end Eccentricity

end Kakeya.ThinCase
