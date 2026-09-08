/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.InducedShading
public import Kakeya.Factoring.Pipeline

/-!
# Conjunct (i) of the thin-case factoring step, at the exponent `3 η`

Conjunct (i) of `Kakeya.ThinCase.factoringApply` asserts `δ^{2η} ≤ C · λ(𝕎'_B, Y_{𝕎'_B})`. This
file proves the same statement at the exponent **`3 η`**, from the binders `factoringApply`
already carries together with the side conditions of the Córdoba estimate
`ShadedBody.lambdaForInducedShading_of_measurable` itself.

## Why `3 η` and not `2 η`

GWZ's Item 2 reads `λ(𝒲', Y_{𝒲'}) ⪆ C_F^{-1} λ(𝒱, Y)²`, and the `C_F` there is the Frostman
constant of the **output** fibres. The formalized pipeline does not deliver
`O(C_F)`-Frostman output fibres: `ShadedBody.outerFactoringFamily_refinement` retains a fraction
of the *total* shade mass, and the only transport of the Frostman property to a subfibre,
`ConvexSpaceBody.IsFrostmanIn.of_le_of_subset`, charges the fibre's **carrier**-mass retention
ratio. The only bridge from a shade-mass retention to a carrier-mass retention is the pointwise
density binder `hdens` of `factoringApply`, and its price is exactly one factor `δ^{-η}`.

Concretely, with `θ` the per-fibre retention:

* the Frostman constant of the output fibre is `C = C_F · 2 C_full / (θ δ^η)`
  (`ConvexSpaceBody.IsFrostmanIn.of_le_of_subset`);
* the density parameter of the Córdoba estimate is `λ = θ δ^η / C_full`;
* hence `C⁻¹ λ² = θ³ δ^{3η} / (2 C_F C_full³)`,

which is `Kakeya.ThinCase.fullness_ge_three_eta`. The gap is one clean factor `δ^η`, with a
subpolynomial constant `Kakeya.ThinCase.thinFullnessConstant` — not a defect of the proof but of
what the pipeline hands over.

## What this file assumes, and what supplies it

Every hypothesis of `Kakeya.ThinCase.fullness_ge_three_eta` is one of:

* a binder of `factoringApply` — `hcar`, `hblk`, `hle`, `hdims`, `hFr`, `hdens`;
* a side condition of `ShadedBody.lambdaForInducedShading_of_measurable` itself — `hne`, `hVpos`,
  `hecc`, `hnd`; or
* the **per-fibre** mass retention `hret`, which `Kakeya.ThinCase.exists_denseBodies` produces
  from the pipeline's aggregate retention at the cost of a factor `2` and of the bodies it
  discards.

The two Markov selections — over the bodies (`exists_denseBodies`) and over the segments of a
fibre (`denseSegs`) — are the same lemma `Kakeya.ThinCase.sum_markovSet_ge` run twice.

## The statement change this licenses, which is NOT made here

`Kakeya.ThinCase.ThinBall.fullness_bodies` is the field `δ^{3 η} ≤ C · λ(𝕎'_B, Y_{𝕎'_B})`
(`MainLemma2/ThinSetup.lean`; in the structure's own index `η`, which
`Kakeya.VeryNotSticky.ThinConfig.tb` reads at `2 · cfg.η` since F8). Nothing in the development
bounds `η` from below — every field of
`Kakeya.VeryNotSticky.CaseParams` is an upper bound on it, and `η` is chosen last, as a minimum of
eight such bounds, by `Kakeya.VeryNotSticky.exists_caseParams`; the same docstring records two
earlier coefficient raisings (`η + ϱ ↝ 2η + ϱ`, `3τ + 9η ↝ 3τ + 12η`) as free for exactly this
reason. So the exponent may be raised. That edit is a *structure field* edit and is deliberately
not made in this file.
-/

@[expose] public section

open MeasureTheory Metric Set ShadedBody Convexity
open scoped ENNReal NNReal

namespace Kakeya.ThinCase

section Fullness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

lemma lambdaForInducedShading_C_pos (N : ℕ) : 0 < ShadedBody.lambdaForInducedShading.C N := by
  rw [ShadedBody.lambdaForInducedShading.C]
  have := ShadedBody.lambdaInducedSingleWUniform.C_pos
  positivity

/-- **The Córdoba estimate, read as a fullness bound.**

`ShadedBody.lambdaForInducedShading_of_measurable` is a per-body volume comparison; this turns it
into the fullness lower bound conjunct (i) of `Kakeya.ThinCase.factoringApply` asks for, on the
family of induced shadings of the outer bodies. -/
theorem fullness_ge_of_cordoba [Nontrivial E] {ι κ : Type*}
    (F : ShadedBody.FactorFamily E ι κ) {C lam : ENNReal} {N : ℕ}
    (hdim : Module.finrank ℝ E = 3)
    (hshape : F.InnerHasSimilarShape 2)
    (hFrostman : F.HasFrostmanFibers C)
    (hne : ∀ j ∈ F.outerSet, (F.fiber j).Nonempty)
    (hVpos : ∀ i ∈ F.innerSet, volume (F.innerBody i).carrier ≠ 0)
    (hlam : ∀ i ∈ F.innerSet,
      (2⁻¹ : ENNReal) * lam * volume (F.innerBody i).carrier ≤ volume (F.innerBody i).shade)
    (hecc : ∀ j ∈ F.outerSet, ∀ i ∈ F.fiber j,
      volume (F.outerBody j).carrier ≤ 2 ^ N * volume (F.innerBody i).carrier)
    (hnd : ∑ j ∈ F.outerSet,
      volume (ShadedBody.inducedShading (F.fiber j) F.innerBody (F.outerBody j)).carrier ≠ 0) :
    C⁻¹ * lam ^ 2 ≤ (ShadedBody.lambdaForInducedShading.C N : ENNReal) *
      (ShadedBody.fullness F.outerSet
        (fun j => ShadedBody.inducedShading (F.fiber j) F.innerBody (F.outerBody j)) :
          ENNReal) := by
  classical
  set W : κ → ShadedBody E :=
    fun j => ShadedBody.inducedShading (F.fiber j) F.innerBody (F.outerBody j) with hW
  have hcord := ShadedBody.lambdaForInducedShading_of_measurable F hdim hshape hFrostman hne
    hVpos hlam hecc
  have hbne : ((ShadedBody.lambdaForInducedShading.C N : NNReal) : ENNReal) ≠ 0 := by
    simpa using (lambdaForInducedShading_C_pos N).ne'
  have hbtop : ((ShadedBody.lambdaForInducedShading.C N : NNReal) : ENNReal) ≠ ⊤ :=
    ENNReal.coe_ne_top
  have hcartop : ∑ j ∈ F.outerSet, volume (W j).carrier ≠ ⊤ := by
    refine (ENNReal.sum_lt_top.mpr fun j _ => ?_).ne
    exact ((W j).isCompact'.measure_lt_top)
  have hdiv : C⁻¹ * lam ^ 2 / ((ShadedBody.lambdaForInducedShading.C N : NNReal) : ENNReal)
      ≤ (ShadedBody.fullness F.outerSet W : ENNReal) := by
    refine ShadedBody.le_fullness_of_forall_mul_volume_carrier_le hbne hbtop hnd hcartop ?_
    intro j hj
    have h := hcord j hj
    have hcar : (W j).carrier =
        (ConvexSpaceBody.cthickening
          (Metric.thickness ℝ (F.outerBody j).carrier (Module.finrank ℝ E - 1))
          (F.outerBody j)).carrier := rfl
    rw [hcar]
    exact h
  calc C⁻¹ * lam ^ 2
      ≤ (ShadedBody.fullness F.outerSet W : ENNReal) *
          ((ShadedBody.lambdaForInducedShading.C N : NNReal) : ENNReal) :=
        (ENNReal.div_le_iff_le_mul (Or.inl hbne) (Or.inl hbtop)).mp hdiv
    _ = ((ShadedBody.lambdaForInducedShading.C N : NNReal) : ENNReal) *
          (ShadedBody.fullness F.outerSet W : ENNReal) := mul_comm _ _


/-! ### The Markov selection

Conjunct (i) needs a *per-segment* density on the refined shading, and a *per-fibre* mass
retention; the factoring pipeline supplies neither, retaining a fraction of the *total* mass only
(`ShadedBody.outerFactoringFamily_refinement` is an `IsCRefinement`, an aggregate statement).
Both are recovered by the same Markov selection, run twice: once over the bodies, to turn the
aggregate retention into a per-fibre one at the cost of a factor `2` and of the bodies it
discards, and once over the segments of a fibre, to turn the per-fibre retention into a termwise
one. The termwise half is the `hlam` of
`ShadedBody.lambdaForInducedShading_of_measurable`; the aggregate half is what bounds the
transport cost of `ConvexSpaceBody.IsFrostmanIn.of_le_of_subset`. -/

open Classical in
/-- The indices on which `g` retains at least a `θ/2` fraction of `f`. -/
noncomputable def markovSet {α : Type*} (s : Finset α) (f g : α → ENNReal) (θ : ENNReal) :
    Finset α :=
  {i ∈ s | θ / 2 * f i ≤ g i}

lemma markovSet_subset {α : Type*} {s : Finset α} {f g : α → ENNReal} {θ : ENNReal} :
    markovSet s f g θ ⊆ s := by
  classical
  rw [markovSet]
  exact Finset.filter_subset _ s

lemma markovSet_spec {α : Type*} {s : Finset α} {f g : α → ENNReal} {θ : ENNReal} {i : α}
    (hi : i ∈ markovSet s f g θ) : θ / 2 * f i ≤ g i := by
  classical
  simpa [markovSet] using (Finset.mem_filter.mp hi).2

lemma mem_markovSet {α : Type*} {s : Finset α} {f g : α → ENNReal} {θ : ENNReal} {i : α}
    (hi : i ∈ s) (h : θ / 2 * f i ≤ g i) : i ∈ markovSet s f g θ := by
  classical
  rw [markovSet]
  exact Finset.mem_filter.mpr ⟨hi, h⟩

open Classical in
/-- **The Markov selection keeps half of the retained mass.** -/
lemma sum_markovSet_ge {α : Type*} (s : Finset α) (f g : α → ENNReal) {θ : ENNReal}
    (hθtop : θ ≠ ⊤) (hftop : ∑ i ∈ s, f i ≠ ⊤)
    (hret : θ * ∑ i ∈ s, f i ≤ ∑ i ∈ s, g i) :
    θ / 2 * ∑ i ∈ s, f i ≤ ∑ i ∈ markovSet s f g θ, g i := by
  classical
  set P : α → Prop := fun i => θ / 2 * f i ≤ g i with hP
  set S : ENNReal := ∑ i ∈ s, f i with hS
  have hsplit : ∑ i ∈ s, g i
      = ∑ i ∈ {i ∈ s | P i}, g i + ∑ i ∈ {i ∈ s | ¬ P i}, g i :=
    (Finset.sum_filter_add_sum_filter_not s P _).symm
  have hlight : ∑ i ∈ {i ∈ s | ¬ P i}, g i ≤ θ / 2 * S := by
    calc ∑ i ∈ {i ∈ s | ¬ P i}, g i
        ≤ ∑ i ∈ {i ∈ s | ¬ P i}, θ / 2 * f i := by
          refine Finset.sum_le_sum fun i hi => ?_
          have := (Finset.mem_filter.mp hi).2
          rw [hP] at this
          exact le_of_lt (lt_of_not_ge this)
      _ = θ / 2 * ∑ i ∈ {i ∈ s | ¬ P i}, f i := by rw [← Finset.mul_sum]
      _ ≤ θ / 2 * S := by
          gcongr
          exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have hhalf : θ / 2 * S + θ / 2 * S = θ * S := by rw [← add_mul, ENNReal.add_halves]
  have hfin : θ / 2 * S ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.div_ne_top hθtop (by norm_num)) hftop
  have hchain : θ / 2 * S + θ / 2 * S ≤ (∑ i ∈ {i ∈ s | P i}, g i) + θ / 2 * S := by
    rw [hhalf]
    calc θ * S ≤ ∑ i ∈ s, g i := hret
      _ = ∑ i ∈ {i ∈ s | P i}, g i + ∑ i ∈ {i ∈ s | ¬ P i}, g i := hsplit
      _ ≤ (∑ i ∈ {i ∈ s | P i}, g i) + θ / 2 * S := by gcongr
  have := (ENNReal.add_le_add_iff_right hfin).mp hchain
  simp only [markovSet, hP] at this ⊢
  exact this

open Classical in
/-- The segments on which the refinement `Y'` keeps at least a `θ/2` fraction of the shade mass. -/
noncomputable def denseSegs {ι : Type*} (segs : Finset ι) (Y Y' : ι → ShadedBody E)
    (θ : ENNReal) : Finset ι :=
  markovSet segs (fun p => volume (Y p).shade) (fun p => volume (Y' p).shade) θ

lemma denseSegs_subset {ι : Type*} {segs : Finset ι} {Y Y' : ι → ShadedBody E} {θ : ENNReal} :
    denseSegs segs Y Y' θ ⊆ segs := markovSet_subset

lemma denseSegs_spec {ι : Type*} {segs : Finset ι} {Y Y' : ι → ShadedBody E} {θ : ENNReal}
    {p : ι} (hp : p ∈ denseSegs segs Y Y' θ) :
    θ / 2 * volume (Y p).shade ≤ volume (Y' p).shade := markovSet_spec hp

open Classical in
/-- The Markov selection commutes with restriction to a fibre. -/
lemma denseSegs_filter {ι : Type*} (segs : Finset ι) (Y Y' : ι → ShadedBody E) (θ : ENNReal)
    (Q : ι → Prop) [DecidablePred Q] :
    denseSegs {p ∈ segs | Q p} Y Y' θ = {p ∈ denseSegs segs Y Y' θ | Q p} := by
  classical
  ext p
  simp only [denseSegs, markovSet, Finset.mem_filter]
  tauto

/-- A finite sum of shade volumes over a family of shaded bodies is finite. -/
lemma sum_volume_shade_finite {ι : Type*} (s : Finset ι) (Y : ι → ShadedBody E) :
    ∑ p ∈ s, volume (Y p).shade ≠ ⊤ := by
  refine (ENNReal.sum_lt_top.mpr fun p _ => ?_).ne
  exact lt_of_le_of_lt (measure_mono (Y p).shade_subset) ((Y p).isCompact'.measure_lt_top)


/-- `ConvexSpaceBody.IsFrostmanIn` depends on the family only through its values on the index
set. -/
lemma isFrostmanIn_congr_of_eqOn {ι : Type*} {s : Finset ι} {W W' : ι → ConvexSpaceBody E}
    {K : ConvexSpaceBody E} {C : ENNReal} (h : ∀ i ∈ s, W i = W' i)
    (hF : ConvexSpaceBody.IsFrostmanIn s W K C) : ConvexSpaceBody.IsFrostmanIn s W' K C := by
  intro K' hK'
  rw [← Kakeya.densityIn_congr h, ← Kakeya.densityIn_congr h]
  exact hF K' hK'

/-- **The output constant of conjunct (i) at the exponent `3 η`.** -/
noncomputable def thinFullnessConstant (CF Cfull θ : NNReal) (N : ℕ) : NNReal :=
  2 * CF * Cfull ^ 3 * ShadedBody.lambdaForInducedShading.C N / θ ^ 3

open Classical in
/-- **Conjunct (i) of `Kakeya.ThinCase.factoringApply`, at the exponent `3 η`.**

Every hypothesis is either a binder of `factoringApply` (`hcar`, `hblk`, `hle`, `hdims`, `hFr`,
`hdens`), a side condition of `ShadedBody.lambdaForInducedShading_of_measurable` itself (`hne`,
`hVpos`, `hecc`, `hnd`), or the *per-fibre* mass retention `hret` of the refinement — which the
factoring pipeline supplies only in the aggregate, and which
`Kakeya.ThinCase.sum_markovSet_ge` converts from the aggregate at the cost of a factor `2` and of
the bodies it discards.

**Why `3 η` and not `2 η`.** The Córdoba estimate produces `C⁻¹ λ²` with `C` the Frostman
constant of the *output* fibres. The only transport to a subfibre,
`ConvexSpaceBody.IsFrostmanIn.of_le_of_subset`, charges the fibre's carrier-mass retention ratio,
and the only bridge from a *shade*-mass retention to a *carrier*-mass retention is the density
hypothesis `hdens`, whose price is exactly one factor `δ^{-η}`. So
`C ≍ CF · Cfull · δ^{-η} / θ` while `λ ≍ θ δ^η / Cfull`, and
`C⁻¹ λ² ≍ θ³ δ^{3η} / (CF Cfull³)`: the exponent is `3 η`, with a subpolynomial constant. There
is no slack to recover — GWZ's Item 2 is `λ(𝒲',Y) ⪆ C_F^{-1} λ(𝒱,Y)²` and the formalized
pipeline does not deliver `O(C_F)`-Frostman output fibres. -/
theorem fullness_ge_three_eta [Nontrivial E] {ι κ : Type*}
    (hdim : Module.finrank ℝ E = 3)
    (segs : Finset ι) (Y Y' : ι → ShadedBody E)
    (bodies : Finset κ) (Wb : κ → ConvexSpaceBody E) (blk : ι → κ)
    {δ θ CF Cfull : NNReal} {η : ℝ} {N : ℕ}
    (hδ : 0 < δ) (hθ : 0 < θ) (hCF : 0 < CF) (hCfull : 0 < Cfull)
    (hcar : ∀ p ∈ segs, (Y' p).toConvexSpaceBody = (Y p).toConvexSpaceBody)
    (hblk : ∀ p ∈ segs, blk p ∈ bodies)
    (hle : ∀ p ∈ segs, (Y p).toConvexSpaceBody ≤ Wb (blk p))
    (hdims : ∀ p ∈ segs, ∀ q ∈ segs,
      Metric.thickness ℝ (Y p).carrier ≤ (2 : NNReal) • Metric.thickness ℝ (Y q).carrier)
    (hFr : ∀ j ∈ bodies, ConvexSpaceBody.IsFrostmanIn {p ∈ segs | blk p = j}
      (fun p => (Y p).toConvexSpaceBody) (Wb j) (CF : ENNReal))
    (hdens : ∀ p ∈ segs,
      (δ : ENNReal) ^ η * volume (Y p).carrier ≤ (Cfull : ENNReal) * volume (Y p).shade)
    (hVpos : ∀ p ∈ segs, volume (Y p).carrier ≠ 0)
    (hret : ∀ j ∈ bodies,
      (θ : ENNReal) * ∑ p ∈ {p ∈ segs | blk p = j}, volume (Y p).shade
        ≤ ∑ p ∈ {p ∈ segs | blk p = j}, volume (Y' p).shade)
    (hne : ∀ j ∈ bodies, ({p ∈ denseSegs segs Y Y' (θ : ENNReal) | blk p = j}).Nonempty)
    (hecc : ∀ j ∈ bodies, ∀ p ∈ {p ∈ denseSegs segs Y Y' (θ : ENNReal) | blk p = j},
      volume (Wb j).carrier ≤ 2 ^ N * volume (Y p).carrier)
    (hnd : ∑ j ∈ bodies, volume (ShadedBody.inducedShading
      {p ∈ denseSegs segs Y Y' (θ : ENNReal) | blk p = j} Y' (Wb j)).carrier ≠ 0) :
    (δ : ENNReal) ^ (3 * η) ≤ (thinFullnessConstant CF Cfull θ N : ENNReal) *
      (ShadedBody.fullness bodies (fun j => ShadedBody.inducedShading
        {p ∈ denseSegs segs Y Y' (θ : ENNReal) | blk p = j} Y' (Wb j)) : ENNReal) := by
  classical
  set Θ : ENNReal := (θ : ENNReal) with hΘ
  set Cf : ENNReal := (Cfull : ENNReal) with hCf
  set CFe : ENNReal := (CF : ENNReal) with hCFe
  set d : ENNReal := (δ : ENNReal) ^ η with hd
  set t : Finset ι := denseSegs segs Y Y' Θ with ht
  -- basic nonvanishing / finiteness
  have hΘ0 : Θ ≠ 0 := by simpa [hΘ] using hθ.ne'
  have hΘtop : Θ ≠ ⊤ := ENNReal.coe_ne_top
  have hCf0 : Cf ≠ 0 := by simpa [hCf] using hCfull.ne'
  have hCftop : Cf ≠ ⊤ := ENNReal.coe_ne_top
  have hCFe0 : CFe ≠ 0 := by simpa [hCFe] using hCF.ne'
  have hCFetop : CFe ≠ ⊤ := ENNReal.coe_ne_top
  have hdeq : d = ((δ ^ η : NNReal) : ENNReal) := by
    rw [hd, ENNReal.coe_rpow_of_ne_zero hδ.ne']
  have hd0 : d ≠ 0 := by
    rw [hdeq]
    simpa using (NNReal.rpow_pos hδ).ne'
  have hdtop : d ≠ ⊤ := by rw [hdeq]; exact ENNReal.coe_ne_top
  have hΘd0 : Θ * d ≠ 0 := mul_ne_zero hΘ0 hd0
  have hΘdtop : Θ * d ≠ ⊤ := ENNReal.mul_ne_top hΘtop hdtop
  -- the two scalar parameters
  set lam : ENNReal := Θ * d / Cf with hlamdef
  set C' : ENNReal := 2 * Cf / (Θ * d) with hC'def
  set C : ENNReal := CFe * C' with hCdef
  have hlamC : lam * Cf = Θ * d := by
    rw [hlamdef]; exact ENNReal.div_mul_cancel hCf0 hCftop
  have hC'Θd : C' * (Θ * d) = 2 * Cf := by
    rw [hC'def]; exact ENNReal.div_mul_cancel hΘd0 hΘdtop
  have hC'0 : C' ≠ 0 := by
    rw [hC'def]
    exact (ENNReal.div_ne_zero).mpr ⟨mul_ne_zero (by norm_num) hCf0, hΘdtop⟩
  have hC'top : C' ≠ ⊤ := by
    rw [hC'def]
    exact ENNReal.div_ne_top (ENNReal.mul_ne_top (by norm_num) hCftop) hΘd0
  have hC0 : C ≠ 0 := mul_ne_zero hCFe0 hC'0
  have hCtop : C ≠ ⊤ := ENNReal.mul_ne_top hCFetop hC'top
  have hts : t ⊆ segs := by rw [ht]; exact denseSegs_subset
  have htspec : ∀ p ∈ t, Θ / 2 * volume (Y p).shade ≤ volume (Y' p).shade := by
    intro p hp
    rw [ht] at hp
    exact denseSegs_spec hp
  have htwo : (2 : ENNReal) * (Θ / 2) = Θ := by rw [two_mul, ENNReal.add_halves]
  have hcarY : ∀ p ∈ segs, volume (Y' p).carrier = volume (Y p).carrier := fun p hp => by
    rw [show (Y' p).carrier = (Y p).carrier from congrArg ConvexSpaceBody.carrier (hcar p hp)]
  -- the Markov selection, fibre by fibre
  have hmk : ∀ j ∈ bodies,
      Θ / 2 * ∑ p ∈ {p ∈ segs | blk p = j}, volume (Y p).shade
        ≤ ∑ p ∈ {p ∈ t | blk p = j}, volume (Y' p).shade := by
    intro j hj
    have h := sum_markovSet_ge {p ∈ segs | blk p = j}
      (fun p => volume (Y p).shade) (fun p => volume (Y' p).shade) hΘtop
      (sum_volume_shade_finite _ _) (hret j hj)
    have hset : markovSet {p ∈ segs | blk p = j}
        (fun p => volume (Y p).shade) (fun p => volume (Y' p).shade) Θ
          = {p ∈ t | blk p = j} := by
      rw [ht, ← denseSegs_filter segs Y Y' Θ (fun p => blk p = j)]
      rfl
    rwa [hset] at h
  -- termwise density on the Markov subfamily: the `hlam` of the Córdoba estimate
  have hlam : ∀ p ∈ t, 2⁻¹ * lam * volume (Y' p).carrier ≤ volume (Y' p).shade := by
    intro p hp
    have hps : p ∈ segs := hts hp
    have hmark : Θ / 2 * volume (Y p).shade ≤ volume (Y' p).shade := htspec p hp
    have hstep : (2⁻¹ * lam * volume (Y' p).carrier) * Cf ≤ volume (Y' p).shade * Cf := by
      calc (2⁻¹ * lam * volume (Y' p).carrier) * Cf
          = 2⁻¹ * (lam * Cf) * volume (Y' p).carrier := by ring
        _ = 2⁻¹ * Θ * (d * volume (Y p).carrier) := by
            rw [hlamC, hcarY p hps]; ring
        _ ≤ 2⁻¹ * Θ * (Cf * volume (Y p).shade) := mul_le_mul' le_rfl (hdens p hps)
        _ = Cf * (Θ / 2 * volume (Y p).shade) := by
            rw [ENNReal.div_eq_inv_mul]; ring
        _ ≤ Cf * volume (Y' p).shade := mul_le_mul' le_rfl hmark
        _ = volume (Y' p).shade * Cf := mul_comm _ _
    exact (ENNReal.mul_le_mul_iff_left hCf0 hCftop).mp hstep
  -- carrier-mass retention on each fibre: the transport cost of the Frostman property
  have hvol : ∀ j ∈ bodies,
      ∑ p ∈ {p ∈ segs | blk p = j}, volume ((Y p).toConvexSpaceBody).carrier
        ≤ C' * ∑ p ∈ {p ∈ t | blk p = j}, volume ((Y p).toConvexSpaceBody).carrier := by
    intro j hj
    have hstep : (∑ p ∈ {p ∈ segs | blk p = j}, volume (Y p).carrier) * (Θ * d)
        ≤ (C' * ∑ p ∈ {p ∈ t | blk p = j}, volume (Y p).carrier) * (Θ * d) := by
      calc (∑ p ∈ {p ∈ segs | blk p = j}, volume (Y p).carrier) * (Θ * d)
          = Θ * (d * ∑ p ∈ {p ∈ segs | blk p = j}, volume (Y p).carrier) := by ring
        _ = Θ * ∑ p ∈ {p ∈ segs | blk p = j}, d * volume (Y p).carrier := by
            rw [← Finset.mul_sum]
        _ ≤ Θ * ∑ p ∈ {p ∈ segs | blk p = j}, Cf * volume (Y p).shade :=
            mul_le_mul' le_rfl
              (Finset.sum_le_sum fun p hp => hdens p (Finset.mem_filter.mp hp).1)
        _ = Θ * (Cf * ∑ p ∈ {p ∈ segs | blk p = j}, volume (Y p).shade) := by
            rw [← Finset.mul_sum]
        _ = Cf * (2 * (Θ / 2 * ∑ p ∈ {p ∈ segs | blk p = j}, volume (Y p).shade)) := by
            conv_lhs => rw [← htwo]
            ring
        _ ≤ Cf * (2 * ∑ p ∈ {p ∈ t | blk p = j}, volume (Y' p).shade) :=
            mul_le_mul' le_rfl (mul_le_mul' le_rfl (hmk j hj))
        _ ≤ Cf * (2 * ∑ p ∈ {p ∈ t | blk p = j}, volume (Y p).carrier) := by
            refine mul_le_mul' le_rfl (mul_le_mul' le_rfl (Finset.sum_le_sum fun p hp => ?_))
            have hpt : p ∈ t := (Finset.mem_filter.mp hp).1
            calc volume (Y' p).shade ≤ volume (Y' p).carrier :=
                  measure_mono (Y' p).shade_subset
              _ = volume (Y p).carrier := hcarY p (hts hpt)
        _ = (C' * (Θ * d)) * ∑ p ∈ {p ∈ t | blk p = j}, volume (Y p).carrier := by
            rw [hC'Θd]; ring
        _ = (C' * ∑ p ∈ {p ∈ t | blk p = j}, volume (Y p).carrier) * (Θ * d) := by ring
    exact (ENNReal.mul_le_mul_iff_left hΘd0 hΘdtop).mp hstep
  -- the factor family fed to the Córdoba estimate
  let F : ShadedBody.FactorFamily E ι κ :=
    { innerSet := t
      innerBody := Y'
      outerSet := bodies
      outerBody := Wb
      parent := blk
      parent_mem := fun i hi => hblk i (hts hi)
      inner_le_parent := fun i hi => by
        rw [hcar i (hts hi)]; exact hle i (hts hi) }
  have hfiber : ∀ j, F.fiber j = {p ∈ t | blk p = j} := fun j => rfl
  have hshape : F.InnerHasSimilarShape 2 := by
    intro i hi i' hi'
    have h := hdims i (hts hi) i' (hts hi')
    have hci : (Y' i).carrier = (Y i).carrier :=
      congrArg ConvexSpaceBody.carrier (hcar i (hts hi))
    have hci' : (Y' i').carrier = (Y i').carrier :=
      congrArg ConvexSpaceBody.carrier (hcar i' (hts hi'))
    show Metric.thickness ℝ (Y' i).carrier ≤ ((2 : NNReal) : ℝ) • Metric.thickness ℝ (Y' i').carrier
    rw [hci, hci']
    exact h
  have hFrostman : F.HasFrostmanFibers C := by
    intro j hj
    have hWK : ∀ p ∈ {p ∈ segs | blk p = j}, (Y p).toConvexSpaceBody ≤ Wb j := by
      intro p hp
      obtain ⟨hps, hpj⟩ := Finset.mem_filter.mp hp
      rw [← hpj]
      exact hle p hps
    have hfibsub : {p ∈ t | blk p = j} ⊆ {p ∈ segs | blk p = j} := by
      intro p hp
      obtain ⟨hpt, hpj⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨hts hpt, hpj⟩
    have hbase := (hFr j hj).of_le_of_subset hWK hfibsub (hvol j hj)
    have : ConvexSpaceBody.IsFrostmanIn {p ∈ t | blk p = j}
        (fun p => (Y' p).toConvexSpaceBody) (Wb j) (CFe * C') := by
      refine isFrostmanIn_congr_of_eqOn (fun p hp => ?_) hbase
      exact (hcar p (hts (Finset.mem_filter.mp hp).1)).symm
    rw [hfiber j]
    exact this
  have hne' : ∀ j ∈ F.outerSet, (F.fiber j).Nonempty := by
    intro j hj
    rw [hfiber j]
    exact hne j hj
  have hVpos' : ∀ i ∈ F.innerSet, volume (F.innerBody i).carrier ≠ 0 := by
    intro i hi
    show volume (Y' i).carrier ≠ 0
    rw [hcarY i (hts hi)]
    exact hVpos i (hts hi)
  have hecc' : ∀ j ∈ F.outerSet, ∀ i ∈ F.fiber j,
      volume (F.outerBody j).carrier ≤ 2 ^ N * volume (F.innerBody i).carrier := by
    intro j hj i hi
    rw [hfiber j] at hi
    show volume (Wb j).carrier ≤ 2 ^ N * volume (Y' i).carrier
    rw [hcarY i (hts (Finset.mem_filter.mp hi).1)]
    exact hecc j hj i hi
  have hnd' : ∑ j ∈ F.outerSet,
      volume (ShadedBody.inducedShading (F.fiber j) F.innerBody (F.outerBody j)).carrier ≠ 0 := by
    simpa [hfiber, ht] using hnd
  have hbridge := fullness_ge_of_cordoba F hdim hshape hFrostman hne' hVpos' hlam hecc' hnd'
  -- the scalar identity behind the exponent `3 η`
  have hkey : Θ ^ 3 * d ^ 3 * C = 2 * CFe * Cf ^ 3 * lam ^ 2 := by
    have h1 : Θ ^ 3 * d ^ 3 * C = CFe * (C' * (Θ * d)) * (Θ * d) ^ 2 := by
      rw [hCdef]; ring
    have h2 : 2 * CFe * Cf ^ 3 * lam ^ 2 = 2 * CFe * Cf * (lam * Cf) ^ 2 := by ring
    rw [h1, h2, hC'Θd, hlamC]
    ring
  have hstep : Θ ^ 3 * d ^ 3
      = 2 * CFe * Cf ^ 3 * (C⁻¹ * lam ^ 2) := by
    have hcc : C * C⁻¹ = 1 := ENNReal.mul_inv_cancel hC0 hCtop
    calc Θ ^ 3 * d ^ 3 = Θ ^ 3 * d ^ 3 * (C * C⁻¹) := by rw [hcc, mul_one]
      _ = (Θ ^ 3 * d ^ 3 * C) * C⁻¹ := by ring
      _ = (2 * CFe * Cf ^ 3 * lam ^ 2) * C⁻¹ := by rw [hkey]
      _ = 2 * CFe * Cf ^ 3 * (C⁻¹ * lam ^ 2) := by ring
  set M : ENNReal := 2 * CFe * Cf ^ 3 * ((ShadedBody.lambdaForInducedShading.C N : NNReal) :
    ENNReal) with hM
  set Ful : ENNReal := (ShadedBody.fullness bodies (fun j => ShadedBody.inducedShading
    {p ∈ t | blk p = j} Y' (Wb j)) : ENNReal) with hFul
  have hbridge' : Θ ^ 3 * d ^ 3 ≤ M * Ful := by
    have hb : C⁻¹ * lam ^ 2
        ≤ ((ShadedBody.lambdaForInducedShading.C N : NNReal) : ENNReal) * Ful := by
      simpa [hFul, hfiber, ht] using hbridge
    calc Θ ^ 3 * d ^ 3 = 2 * CFe * Cf ^ 3 * (C⁻¹ * lam ^ 2) := hstep
      _ ≤ 2 * CFe * Cf ^ 3 *
            (((ShadedBody.lambdaForInducedShading.C N : NNReal) : ENNReal) * Ful) := by gcongr
      _ = M * Ful := by rw [hM]; ring
  -- divide by `Θ ^ 3`
  have hΘ30 : Θ ^ 3 ≠ 0 := pow_ne_zero _ hΘ0
  have hΘ3top : Θ ^ 3 ≠ ⊤ := ENNReal.pow_ne_top hΘtop
  have hfinal : d ^ 3 ≤ (Θ ^ 3)⁻¹ * M * Ful := by
    calc d ^ 3 = (Θ ^ 3)⁻¹ * (Θ ^ 3 * d ^ 3) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hΘ30 hΘ3top, one_mul]
      _ ≤ (Θ ^ 3)⁻¹ * (M * Ful) := mul_le_mul' le_rfl hbridge'
      _ = (Θ ^ 3)⁻¹ * M * Ful := by ring
  have hK : ((thinFullnessConstant CF Cfull θ N : NNReal) : ENNReal) = (Θ ^ 3)⁻¹ * M := by
    rw [thinFullnessConstant, hM, hΘ, hCf, hCFe]
    rw [ENNReal.coe_div (by positivity)]
    push_cast
    rw [ENNReal.div_eq_inv_mul]
  have hpow : (δ : ENNReal) ^ (3 * η) = d ^ 3 := by
    rw [hd, mul_comm (3 : ℝ) η, ENNReal.rpow_mul, ← ENNReal.rpow_natCast ((δ : ENNReal) ^ η) 3]
    norm_num
  rw [hpow, hK, hFul]
  exact hfinal


open Classical in
/-- **From the pipeline's aggregate retention to the per-fibre retention.**

`ShadedBody.outerFactoringFamily_refinement` is an `ShadedBody.IsCRefinement`: it retains a
fraction `θ` of the *total* shade mass and says nothing about any single fibre. The same Markov
selection, run over the *bodies*, upgrades that to a per-fibre retention at `θ / 2` on a
subfamily of bodies which still carries a `θ / 2` fraction of the total mass. The cost is a
factor `2` and the discarded bodies — not a logarithm — so this step is free against the `Ccore`
budget; the discarded bodies are what conjunct (vi) has to pay for.

The output is exactly the hypothesis `hret` of `Kakeya.ThinCase.fullness_ge_three_eta`, read at
`θ / 2`. -/
theorem exists_denseBodies {ι κ : Type*} (segs : Finset ι) (Y Y' : ι → ShadedBody E)
    (bodies : Finset κ) (blk : ι → κ) {θ : ENNReal} (hθtop : θ ≠ ⊤)
    (hblk : ∀ p ∈ segs, blk p ∈ bodies)
    (hret : θ * ∑ p ∈ segs, volume (Y p).shade ≤ ∑ p ∈ segs, volume (Y' p).shade) :
    ∃ bodies' ⊆ bodies,
      (∀ j ∈ bodies', θ / 2 * ∑ p ∈ {p ∈ segs | blk p = j}, volume (Y p).shade
          ≤ ∑ p ∈ {p ∈ segs | blk p = j}, volume (Y' p).shade) ∧
        θ / 2 * ∑ p ∈ segs, volume (Y p).shade
          ≤ ∑ j ∈ bodies', ∑ p ∈ {p ∈ segs | blk p = j}, volume (Y' p).shade := by
  classical
  set F : κ → ENNReal := fun j => ∑ p ∈ {p ∈ segs | blk p = j}, volume (Y p).shade with hF
  set G : κ → ENNReal := fun j => ∑ p ∈ {p ∈ segs | blk p = j}, volume (Y' p).shade with hG
  have hFsum : ∑ j ∈ bodies, F j = ∑ p ∈ segs, volume (Y p).shade :=
    Finset.sum_fiberwise_of_maps_to hblk _
  have hGsum : ∑ j ∈ bodies, G j = ∑ p ∈ segs, volume (Y' p).shade :=
    Finset.sum_fiberwise_of_maps_to hblk _
  have hFtop : ∑ j ∈ bodies, F j ≠ ⊤ := by
    rw [hFsum]; exact sum_volume_shade_finite segs Y
  have hret' : θ * ∑ j ∈ bodies, F j ≤ ∑ j ∈ bodies, G j := by
    rw [hFsum, hGsum]; exact hret
  refine ⟨markovSet bodies F G θ, markovSet_subset, fun j hj => markovSet_spec hj, ?_⟩
  have := sum_markovSet_ge bodies F G hθtop hFtop hret'
  rwa [hFsum] at this

end Fullness

end Kakeya.ThinCase
