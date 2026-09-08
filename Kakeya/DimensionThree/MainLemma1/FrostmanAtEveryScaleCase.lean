/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.ShadedUniform
public import Kakeya.Sticky
public import Kakeya.Multiplicity
public import Kakeya.StickyKakeya.FibreCounts

/-!
# GWZ Lemma 8.1, case (i): the Frostman-at-every-scale case

The bootstrapping lemma [GWZ, Lemma 8.1] splits according to the two conclusions of
[GWZ, Lemma 7.7(A)].  This file treats the first conclusion, in which the family of
`δ`-tubes is Frostman at every scale.  In that case sticky Kakeya
([GWZ, Theorem 7.3(A)], stated here as
`StickyKakeya.volume_iUnionShade_ge_of_isFrostmanAtEveryScale`) gives an almost
maximal shaded union, and the Frostman estimate `K_F(γ/2)` follows at once, i.e.
[GWZ, Lemma 8.1] holds with `ν = γ/2`.

The one adaptation relative to GWZ: the paper uses the sharp packing bound
`|𝕋| ≤ δ⁻⁴` for essentially distinct `δ`-tubes in `B₁ ⊆ ℝ³`, whereas the bound
available here is the crude `Tube.card_le_of_EssDistinct`, which only gives
`|𝕋| ≲ δ⁻⁶`.  We therefore apply [GWZ, Theorem 7.3(A)] with `ε / 2` in place of
`γ / 2` and retain an explicit `δ ^ (-ε)` factor.  This changes only constants; the
conclusion is the same `K_F(γ/2)` bound.
-/

@[expose] public section

open MeasureTheory Topology Filter ShadedBody Tube ShadedTube

universe v

namespace Kakeya

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-- Blueprint `lem:constLeRpowNeg`: a constant `C ≥ 1` is absorbed by `δ ^ (-α)` as
soon as `δ ≤ C ^ (-1 / α)`.  The threshold is exhibited explicitly, so no limiting
argument is needed. -/
theorem const_le_rpow_neg {C : ENNReal} (_hC1 : 1 ≤ C) (_hCtop : C ≠ ⊤) {α : ℝ} (hα : 0 < α)
    {δ : NNReal} (_hδ0 : 0 < δ) (hδ : (δ : ENNReal) ≤ C ^ (-1 / α)) :
    C ≤ (δ : ENNReal) ^ (-α) := by
  have h := ENNReal.rpow_le_rpow hδ hα.le
  rw [← ENNReal.rpow_mul, div_mul_cancel₀ _ hα.ne', ENNReal.rpow_neg_one] at h
  rw [ENNReal.rpow_neg]
  exact ENNReal.le_inv_iff_le_inv.mp h

/-- Eventual form of `const_le_rpow_neg`: as `δ → 0⁺`, every finite constant `C ≥ 1` is
dominated by `δ ^ (-α)`, and `δ ≤ 1`. -- (extracted by Fuse golfer) -/
private lemma eventually_const_le_rpow_neg {C : ENNReal} (hC1 : 1 ≤ C) (hCtop : C ≠ ⊤)
    {α : ℝ} (hα : 0 < α) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0, 0 < δ ∧ δ ≤ 1 ∧ C ≤ (δ : ENNReal) ^ (-α) := by
  have hCpos : (0 : ENNReal) < C := zero_lt_one.trans_le hC1
  have htop : C ^ (-1 / α) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg' hCpos hCtop
  have hδ₁ : (0 : NNReal) < min 1 (C ^ (-1 / α)).toNNReal :=
    lt_min zero_lt_one (by
      rw [← ENNReal.coe_pos, ENNReal.coe_toNNReal htop]
      exact ENNReal.rpow_pos hCpos hCtop)
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hδ₁)]
    with δ (hδ_pos : 0 < δ) hδ_lt
  refine ⟨hδ_pos, hδ_lt.le.trans (min_le_left _ _),
    const_le_rpow_neg hC1 hCtop hα hδ_pos ?_⟩
  calc
    (δ : ENNReal) ≤ ((C ^ (-1 / α)).toNNReal : ENNReal) :=
      ENNReal.coe_le_coe.mpr (hδ_lt.le.trans (min_le_right _ _))
    _ = C ^ (-1 / α) := ENNReal.coe_toNNReal htop

/-- Blueprint `lem:splitPowerBound`: if `0 ≤ X ≤ A * δ ^ (-4)` with `1 ≤ A` and
`0 < γ ≤ 2`, then splitting `X = X ^ (γ/4) * X ^ (1 - γ/4)` and bounding the first
factor gives `X ≤ A * δ ^ (-γ) * X ^ (1 - γ/4)`. -/
theorem split_power_bound {A : ENNReal} (hA1 : 1 ≤ A) (hAtop : A ≠ ⊤) {δ : NNReal}
    (hδ0 : 0 < δ) (_hδ1 : δ ≤ 1) {γ : ℝ} (hγ : 0 < γ) (hγ' : γ ≤ 2) {X : ENNReal}
    (hX : X ≤ A * (δ : ENNReal) ^ (-4 : ℝ)) :
    X ≤ A * (δ : ENNReal) ^ (-γ) * X ^ (1 - γ / 4) := by
  have hγ4 : (0 : ℝ) ≤ γ / 4 := by linarith
  rcases eq_or_ne X 0 with rfl | hXne0
  · exact zero_le
  have hδne : (δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr (ne_of_gt hδ0)
  have hXtop : X ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top hAtop (by simp [hδne])) hX
  have hXγ4 : X ^ (γ / 4) ≤ A * (δ : ENNReal) ^ (-γ) := by
    calc
      X ^ (γ / 4) ≤ (A * (δ : ENNReal) ^ (-4 : ℝ)) ^ (γ / 4) := ENNReal.rpow_le_rpow hX hγ4
      _ = A ^ (γ / 4) * (δ : ENNReal) ^ (-γ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hγ4, ← ENNReal.rpow_mul,
          show (-4 : ℝ) * (γ / 4) = -γ by ring]
      _ ≤ A * (δ : ENNReal) ^ (-γ) :=
        mul_le_mul_left
          (by simpa using ENNReal.rpow_le_rpow_of_exponent_le hA1 (by linarith : γ / 4 ≤ 1)) _
  calc
    X = X ^ (γ / 4) * X ^ (1 - γ / 4) := by
      rw [← ENNReal.rpow_add _ _ hXne0 hXtop,
        show γ / 4 + (1 - γ / 4) = (1 : ℝ) by ring, ENNReal.rpow_one]
    _ ≤ A * (δ : ENNReal) ^ (-γ) * X ^ (1 - γ / 4) := mul_le_mul_left hXγ4 _

/-- Blueprint `lem:multBoundFromUnionLower`: a lower bound `u` for the shaded union
turns into an upper bound for the multiplicity, using only `|T| ≲ δ ^ (n-1)` for a
`δ`-tube (`Tube.volume_le`). -/
theorem multiplicity_le_div_of_le_volume_iUnionShade {δ : NNReal} (hδ1 : δ ≤ 1)
    {ι : Type*} (s : Finset ι) (T : ι → ShadedTube δ E)
    {u : ENNReal} (_hu : 0 < u) (hU : u ≤ volume (⋃ i ∈ s, (T i).shade)) :
    multiplicity s (fun i ↦ (T i).toShadedBody) ≤
      (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal) *
        ((s.card : ENNReal) * (δ : ENNReal) ^ (Module.finrank ℝ E - 1)) / u := by
  rw [ShadedBody.multiplicity_eq_div]
  refine ENNReal.div_le_div ?_ hU
  calc
    (∑ i ∈ s, volume ((T i).toShadedBody).shade)
      ≤ ∑ _ ∈ s, (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal) *
          (δ : ENNReal) ^ (Module.finrank ℝ E - 1) :=
        Finset.sum_le_sum fun i _ =>
          (measure_mono (T i).toShadedBody.shade_subset).trans
            (by simpa using Tube.volume_le hδ1 (T i).toTube)
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- The packing constant of `Tube.card_le_of_EssDistinct` is at least `1`, hence may be
absorbed into any other constant. -- (extracted by Fuse golfer) -/
private lemma one_le_card_le_of_EssDistinct_C (n : ℕ) :
    (1 : ℝ) ≤ Tube.card_le_of_EssDistinct.C n :=
  le_add_of_nonneg_left (by positivity)

/-- `ENNReal` form of `one_le_card_le_of_EssDistinct_C`. -- (extracted by Fuse golfer) -/
private lemma one_le_ofReal_card_le_of_EssDistinct_C (n : ℕ) :
    (1 : ENNReal) ≤ ENNReal.ofReal (Tube.card_le_of_EssDistinct.C n) :=
  ENNReal.one_le_ofReal.mpr (one_le_card_le_of_EssDistinct_C n)

/-- Blueprint `lem:multBoundEssDistinctSplit`: for pairwise essentially distinct
`δ`-tubes in `B₁ ⊆ ℝ³`, a lower bound `u` for the shaded union gives the multiplicity
bound already in the split form required by `K_F`.  This combines
`multiplicity_le_div_of_le_volume_iUnionShade`, the packing bound
`Tube.card_le_of_EssDistinct`, and `split_power_bound`. -/
theorem multiplicity_le_of_essentiallyDistinct_split (hE : Module.finrank ℝ E = 3)
    {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {γ : ℝ} (hγ : 0 < γ) (hγ' : γ ≤ 2)
    {ι : Type*} (s : Finset ι) (T : ι → ShadedTube δ E)
    (hB : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1)
    (hED : (s : Set ι).Pairwise (fun i j ↦ IsEssentiallyDistinct ((T i).carrier) ((T j).carrier)))
    {u : ENNReal} (hu : 0 < u) (hU : u ≤ volume (⋃ i ∈ s, (T i).shade)) :
    multiplicity s (fun i ↦ (T i).toShadedBody) ≤
      (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal) *
          ENNReal.ofReal (Tube.card_le_of_EssDistinct.C (Module.finrank ℝ E)) / u *
        (δ : ENNReal) ^ (-γ) *
        ((s.card : ENNReal) * (δ : ENNReal) ^ (Module.finrank ℝ E - 1)) ^ (1 - γ / 4) := by
  have hδR : (0 : ℝ) < (δ : ℝ) := NNReal.coe_pos.mpr hδ0
  have hδ_ne : (δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hδ0.ne'
  set C₂ : ENNReal := ENNReal.ofReal (Tube.card_le_of_EssDistinct.C (Module.finrank ℝ E)) with hC₂
  set X : ENNReal := (s.card : ENNReal) * (δ : ENNReal) ^ (Module.finrank ℝ E - 1) with hX
  have hcard : (s.card : ENNReal) ≤ C₂ * (δ : ENNReal) ^ (-6 : ℝ) := by
    have h := Tube.card_le_of_EssDistinct hδ0 1 s (fun i => (T i).toTube)
      (fun i hi => hB i hi) hED
    rw [show (1 / (δ : ℝ)) ^ (2 * Module.finrank ℝ E) = (δ : ℝ) ^ (-6 : ℝ) by
      rw [hE, show (-6 : ℝ) = -((6 : ℕ) : ℝ) by norm_num, Real.rpow_neg hδR.le,
        Real.rpow_natCast, one_div, inv_pow]] at h
    calc
      (s.card : ENNReal) = ENNReal.ofReal (s.card : ℝ) := (ENNReal.ofReal_natCast _).symm
      _ ≤ ENNReal.ofReal
            (Tube.card_le_of_EssDistinct.C (Module.finrank ℝ E) * (δ : ℝ) ^ (-6 : ℝ)) :=
        ENNReal.ofReal_le_ofReal h
      _ = C₂ * (δ : ENNReal) ^ (-6 : ℝ) := by
        rw [hC₂, ENNReal.ofReal_mul Tube.card_le_of_EssDistinct.C_pos.le,
          ← ENNReal.ofReal_rpow_of_pos hδR, ENNReal.ofReal_coe_nnreal]
  have hX_le : X ≤ C₂ * (δ : ENNReal) ^ (-4 : ℝ) := by
    rw [hX, show (δ : ENNReal) ^ (Module.finrank ℝ E - 1) = (δ : ENNReal) ^ (2 : ℕ) by rw [hE]]
    calc
      (s.card : ENNReal) * (δ : ENNReal) ^ (2 : ℕ)
          ≤ C₂ * (δ : ENNReal) ^ (-6 : ℝ) * (δ : ENNReal) ^ (2 : ℕ) := mul_le_mul_left hcard _
      _ = C₂ * (δ : ENNReal) ^ (-4 : ℝ) := by
        rw [mul_assoc, ← ENNReal.rpow_natCast (δ : ENNReal) 2,
          ← ENNReal.rpow_add _ _ hδ_ne ENNReal.coe_ne_top]
        norm_num
  have hX_split : X ≤ C₂ * (δ : ENNReal) ^ (-γ) * X ^ (1 - γ / 4) :=
    split_power_bound (hC₂ ▸ one_le_ofReal_card_le_of_EssDistinct_C _)
      (hC₂ ▸ ENNReal.ofReal_ne_top) hδ0 hδ1 hγ hγ' hX_le
  refine (multiplicity_le_div_of_le_volume_iUnionShade hδ1 s T hu hU).trans
    ((ENNReal.div_le_div_right (mul_le_mul_right hX_split _) u).trans_eq ?_)
  simp only [div_eq_mul_inv]
  ring

end Kakeya

namespace StickyKakeya

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

omit [Nontrivial E] in
/-- [GWZ, Theorem 7.3(A)] (sticky Kakeya, union form), in the filter form Section 8 uses.
For every `ε > 0` there is `η > 0` such that, for all small `δ`, every family of `δ`-tubes
in `B₁` carrying a uniform hierarchy along the grid of `Tube.ssfGridLen δ`, a
shading of fullness at least `δ ^ η`, and the every-scale Frostman bound `δ ^ (-η)` on the
classes of that hierarchy, has shaded union of volume at least `δ ^ ε`.

No dimension hypothesis is needed: `StickyKakeya.StickyFrostmanEstimate` is itself stated
dimension-free, so only its `B_R`-to-`B_1` specialisation and the passage from the explicit
threshold to the filter are used here.  The consumer
`Kakeya.multiplicity_le_of_isFrostmanAtEveryScale` supplies `Module.finrank ℝ E = 3` on its
own, where it is genuinely needed for the tube-packing count.

This is not a second assumption: it is the hypothesis `StickyKakeya.StickyFrostmanEstimate`
— the explicit sticky Kakeya assumption of the development — restated with
its explicit threshold `δ₀` replaced by the `𝓝[>] 0` filter, which is the form
`Kakeya.multiplicity_le_of_isFrostmanAtEveryScale` consumes.  Sticky Kakeya is now a `Prop`
*definition* rather than a theorem, so it is threaded through as the hypothesis `hSFE`
instead of being invoked by name.

**Both hypotheses are read off one hierarchy.**  Uniformity and the every-scale condition
share the single bundle `𝒯 : ShadedTube.ShadedUniformTubeSet s T (ssfGridLen δ) Cunif`:
the Frostman bound is imposed on the class of each node of `𝒯.tubeUniform` by
`Tube.UniformTubeSet.IsFrostmanAtEveryScale`.  This replaces the earlier pair
"per-scale shaded uniformity on `Set.Icc δ 1`" plus the leaf-anchored
`Tube.IsFrostmanAtEveryScale`, in which nothing tied the family witnessing
uniformity to the anchors carrying the Frostman bound.  The bundle is quantified inside the
`∀ᶠ δ`, as in `StickyKakeya.StickyFrostmanEstimate`; only its constant `Cunif` is fixed
before `η`, which is what lets `Kakeya.ml1Boot.multiplicity_le_of_frostmanAtEveryScale`
choose `η⋆` after `Cunif`.

The grid length is `Tube.ssfGridLen δ` and no change-of-grid lemma is needed at the
call sites: `ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf` produces a bundle at
exactly this length. -/
theorem volume_iUnionShade_ge_of_isFrostmanAtEveryScale
    (hSFE : StickyFrostmanEstimate.{_, v} (E := E))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η > (0 : ℝ), ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
    ∀ {ι : Type v} (s : Finset ι) (T : ι → ShadedTube δ E),
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
      (s : Set ι).Pairwise
        (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) →
      ∀ {Cunif : NNReal}, Cunif ≤ ssfUniformConst (Module.finrank ℝ E) →
      ∀ 𝒯 : ShadedUniformTubeSet s T (ssfGridLen δ) Cunif,
      ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
      𝒯.tubeUniform.IsFrostmanAtEveryScale ((δ : ENNReal) ^ (-η)) →
      (δ : ENNReal) ^ ε ≤ volume (⋃ i ∈ s, (T i).shade) := by
  obtain ⟨η, δ₀, hη, hδ₀, H⟩ := hSFE ε hε
  refine ⟨η, hη, ?_⟩
  have hpos : ∀ᶠ δ : NNReal in 𝓝[>] (0 : NNReal), 0 < δ := by
    simpa [Set.Ioi] using
      (eventually_mem_nhdsWithin : ∀ᶠ δ in 𝓝[>] (0 : NNReal), δ ∈ Set.Ioi (0 : NNReal))
  have hcoe : Tendsto (fun δ : NNReal => (δ : ℝ)) (𝓝[>] (0 : NNReal)) (𝓝 (0 : ℝ)) :=
    NNReal.continuous_coe.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hle : ∀ᶠ δ : NNReal in 𝓝[>] (0 : NNReal), (δ : ℝ) ≤ δ₀ :=
    hcoe.eventually (eventually_le_nhds hδ₀)
  filter_upwards [hpos, hle] with δ hδpos hδle
  intro ι s T hB hED Cunif hCunif 𝒯 hfull hfrost
  have hδR : (0 : ℝ) < (δ : ℝ) := NNReal.coe_pos.mpr hδpos
  have hfull' : ENNReal.ofReal ((δ : ℝ) ^ η) ≤
      ShadedBody.fullness' s (fun i ↦ (T i).toShadedBody) := by
    rw [← ENNReal.ofReal_rpow_of_pos hδR, ENNReal.ofReal_coe_nnreal,
      ENNReal.rpow_ofNNReal hη.le, ← coe_fullness]
    exact ENNReal.coe_le_coe.mpr hfull
  have hfrost' : 𝒯.tubeUniform.IsFrostmanAtEveryScale (ENNReal.ofReal ((δ : ℝ) ^ (-η))) := by
    rw [← ENNReal.ofReal_rpow_of_pos hδR, ENNReal.ofReal_coe_nnreal]
    exact hfrost
  have hconc := H hδpos hδle s T hB hED hCunif 𝒯 hfull' hfrost'
  rw [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_rpow_of_pos hδR]
  exact hconc

end StickyKakeya

namespace Kakeya

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-- [GWZ, Lemma 8.1], case (i): the Frostman-at-every-scale case.

Let `0 < γ ≤ 2`.  For every `ε > 0` there is `η > 0` such that, for all small `δ`,
every family of pairwise essentially distinct `δ`-tubes in `B₁ ⊆ ℝ³` which carries a uniform
hierarchy along the grid of `Tube.ssfGridLen δ`, a shading of fullness at least
`δ ^ η`, and the every-scale Frostman bound `δ ^ (-η)` on the classes of that hierarchy,
satisfies the multiplicity bound of `K_F(γ/2)`.  Thus in this case the bootstrapping lemma
holds with `ν = γ / 2`.

Sticky Kakeya is a `Prop` definition, not a theorem, so it is taken as the hypothesis `hSFE`
and passed to `StickyKakeya.volume_iUnionShade_ge_of_isFrostmanAtEveryScale`; the uniformity
and every-scale hypotheses are read off the same bundle `𝒯` as there. -/
theorem multiplicity_le_of_isFrostmanAtEveryScale
    (hSFE : StickyKakeya.StickyFrostmanEstimate.{_, v} (E := E))
    (hE : Module.finrank ℝ E = 3)
    {γ : ℝ} (hγ : 0 < γ) (hγ' : γ ≤ 2)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η > (0 : ℝ), ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
    ∀ {ι : Type v} (s : Finset ι) (T : ι → ShadedTube δ E),
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
      (s : Set ι).Pairwise (fun i j ↦ IsEssentiallyDistinct ((T i).carrier) ((T j).carrier)) →
      ∀ {Cunif : NNReal}, Cunif ≤ ShadedTube.ssfUniformConst (Module.finrank ℝ E) →
      ∀ 𝒯 : ShadedTube.ShadedUniformTubeSet s T (Tube.ssfGridLen δ) Cunif,
      ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
      𝒯.tubeUniform.IsFrostmanAtEveryScale ((δ : ENNReal) ^ (-η)) →
      multiplicity s (fun i ↦ (T i).toShadedBody) ≤
        (δ : ENNReal) ^ (-ε - 2 * (γ / 2)) *
          ((s.card : ENNReal) * (δ : ENNReal) ^ (Module.finrank ℝ E - 1)) ^ (1 - γ / 2 / 2) := by
  obtain ⟨η, hη_pos, hη_ev⟩ := StickyKakeya.volume_iUnionShade_ge_of_isFrostmanAtEveryScale
    (E := E) hSFE (ε := ε / 2) (by linarith)
  refine ⟨η, hη_pos, ?_⟩
  have hA1 : (1 : ENNReal) ≤ (Tube.volume_le.C (Module.finrank ℝ E) : ENNReal) *
      ENNReal.ofReal (Tube.card_le_of_EssDistinct.C (Module.finrank ℝ E)) := by
    rw [← one_mul (1 : ENNReal)]
    exact mul_le_mul' (ENNReal.one_le_coe_iff.mpr (one_le_pow₀ one_le_two))
      (one_le_ofReal_card_le_of_EssDistinct_C _)
  filter_upwards [hη_ev, eventually_const_le_rpow_neg hA1
      (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top) (by linarith : (0:ℝ) < ε / 2)]
    with δ hδ_sticky ⟨hδ_pos, hδ_le1, hC_le⟩
  have hδ_ne : (δ : ENNReal) ≠ 0 := (ENNReal.coe_pos.mpr hδ_pos).ne'
  -- absorbing the constant and the volume lower bound `δ ^ (ε / 2)` into `δ ^ (-ε)`
  have key : ∀ A : ENNReal, A ≤ (δ : ENNReal) ^ (-(ε / 2)) →
      A / (δ : ENNReal) ^ (ε / 2) * (δ : ENNReal) ^ (-γ)
        ≤ (δ : ENNReal) ^ (-ε - 2 * (γ / 2)) := fun A hA =>
    calc
      A / (δ : ENNReal) ^ (ε / 2) * (δ : ENNReal) ^ (-γ)
          ≤ (δ : ENNReal) ^ (-ε) * (δ : ENNReal) ^ (-γ) :=
        mul_le_mul_left (by
          rw [show (-ε : ℝ) = -(ε / 2) - ε / 2 by ring,
            ENNReal.rpow_sub _ _ hδ_ne ENNReal.coe_ne_top]
          exact ENNReal.div_le_div_right hA _) _
      _ = (δ : ENNReal) ^ (-ε - 2 * (γ / 2)) := by
        rw [show (-ε - 2 * (γ / 2) : ℝ) = -ε + -γ by ring,
          ENNReal.rpow_add _ _ hδ_ne ENNReal.coe_ne_top]
  intro ι s T hB hED Cunif hCunif 𝒯 hfull hfros
  have hsplit := multiplicity_le_of_essentiallyDistinct_split hE hδ_pos hδ_le1 hγ hγ' s T hB hED
    (u := (δ : ENNReal) ^ (ε / 2))
    (ENNReal.rpow_pos (ENNReal.coe_pos.mpr hδ_pos) ENNReal.coe_ne_top)
    (hδ_sticky s T hB hED hCunif 𝒯 hfull hfros)
  rw [show (1 - γ / 2 / 2 : ℝ) = 1 - γ / 4 by ring]
  exact hsplit.trans (mul_le_mul_left (key _ hC_le) _)


/-! ### Discharging the uniformity cap

Case (i) caps the uniformity constant of the bundle it is applied to by the dimension-only
`ShadedTube.ssfUniformConst (Module.finrank ℝ E)`, inherited from
`StickyKakeya.StickyFrostmanEstimate`.  The dichotomy
`StickyKakeya.dividingScalesFrostman` returns its hierarchy at a constant that is *provably
larger* than that cap — it is at least `comparableCuOf (gridUniformBandConst …)`, a square of a
band constant — so its node-anchored alternative (i) cannot be read on a capped bundle.

Its **leaf-anchored** alternative (i) can.  `StickyKakeya.IsFrostmanAtEveryScale` mentions no
hierarchy at all, and `StickyKakeya.isFrostmanAtEveryScale_nodes_of_ambient_fibre` converts it
into the node-anchored condition on *any* hierarchy carried by a subfamily retaining a
`Λ`-proportion.  Instantiated at a bundle produced by
`ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf` or by
`Kakeya.ml1Boot.exists_caseFamily` — both of which land at exactly
`ShadedTube.ssfUniformConst (Module.finrank ℝ E)` — this is the theorem below, and the cap is
discharged with no change to `StickyKakeya.StickyFrostmanEstimate`. -/

/-- **The uniformity cap of Case (i) is dischargeable from the leaf-anchored datum.**

If the ambient family `s` is Frostman at every real scale with constant `A` and has
`Kakeya.maxDensity ≤ D`, and `t ⊆ s` retains a `Λ`-proportion of it and carries a *shaded*
hierarchy at any constant `Cunif` below the dimension-only cap
`ShadedTube.ssfUniformConst (Module.finrank ℝ E)`, then the tube hierarchy of that bundle
satisfies the node-anchored every-scale condition that
`Kakeya.multiplicity_le_of_isFrostmanAtEveryScale` and
`Kakeya.ml1Boot.multiplicity_le_of_frostmanAtEveryScale` consume.

Every constant in the conclusion is either dimension-only
(`Kakeya.MultiScaleFac.nodeClassConst`, `Kakeya.StickyKakeya.fibreCoverConst`,
`Kakeya.StickyKakeya.frostmanFibreConst`, `ShadedTube.ssfUniformConst`,
`Kakeya.MultiScaleFac.tubeVolRatio`) or one of the three transport parameters `A`, `D`, `Λ`.
The uniformity constant of the hierarchy the dichotomy returns does **not** occur. -/
theorem isFrostmanAtEveryScale_capped_of_ambient_leaf {δ : NNReal}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hN : 0 < Tube.ssfGridLen δ)
    (hδN : δ ≤ (16 : NNReal) ^ (-(Tube.ssfGridLen δ : ℝ)))
    {ι : Type*} {s t : Finset ι} {T : ι → ShadedTube δ E} {Cunif A D Λ : NNReal}
    (hts : t ⊆ s) (htne : t.Nonempty)
    (hCunif : Cunif ≤ ShadedTube.ssfUniformConst (Module.finrank ℝ E))
    (𝒯 : ShadedTube.ShadedUniformTubeSet t T (Tube.ssfGridLen δ) Cunif)
    (hleaf : StickyKakeya.IsFrostmanAtEveryScale s (fun i => (T i).toTube) (A : ENNReal))
    (hD : Kakeya.maxDensity s (fun i => ((T i).toTube).toConvexSpaceBody) ≤ (D : ENNReal))
    (hprop : (s.card : ℝ) ≤ (Λ : ℝ) * (t.card : ℝ)) :
    𝒯.tubeUniform.IsFrostmanAtEveryScale
      (max ((MultiScaleFac.nodeClassConst (E := E) * StickyKakeya.fibreCoverConst (E := E)
                * StickyKakeya.frostmanFibreConst (Module.finrank ℝ E)
                * ShadedTube.ssfUniformConst (Module.finrank ℝ E) ^ 3
                * Λ * A ^ 2 * D : NNReal) : ENNReal)
        (MultiScaleFac.tubeVolRatio (E := E) : ENNReal)) := by
  have hgrid : StickyKakeya.IsFrostmanAtGridScales s (fun i => (T i).toTube)
      (Tube.ssfGridLen δ) (A : ENNReal) :=
    StickyKakeya.isFrostmanAtGridScales_of_isFrostmanAtEveryScale hδ hδ1 _ hleaf
  have hmain := StickyKakeya.isFrostmanAtEveryScale_nodes_of_ambient_fibre
    (E := E) hδ hδ1 hN hδN hts htne 𝒯.tubeUniform hgrid hD hprop
  refine hmain.mono ?_
  refine max_le_max ?_ le_rfl
  refine ENNReal.coe_le_coe.mpr ?_
  gcongr

end Kakeya
