/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Covers
public import Kakeya.Mathlib.MeasureTheory.Lintegral
public import Kakeya.Thickness.HasThicknesses
public import Kakeya.Thickness.Volume

/-!
# Bookkeeping lemmas for the thin case of Main Lemma 2

This file collects the parts of blueprint Subsection `subsec:thincase` that involve no
tube-specific structure and are therefore stated here for general finite families of sets:

* `Kakeya.ThinCase.massMarkovUpgrade` and `Kakeya.ThinCase.massMarkovUpgrade_card` (both
  blueprint `lem:massMarkovUpgrade`, the latter its final sentence): a refinement that loses
  a factor `κ` only *in the sum* carries a large-mass subfamily on which it loses a factor
  `κ / 2` *termwise*, and that subfamily is also large in cardinality when the masses are
  comparable;
* `Kakeya.ThinCase.volume_cthickening_le_mul` (blueprint `lem:tubeSegmentNbhdVolume`): the
  `2δ`-neighbourhood of a tube segment has volume at most a constant multiple of the
  volume of the segment;
* `Kakeya.ThinCase.exists_ball_volume_inter_ge` (blueprint `lem:ml2thinDeltaBallSingle`) and
  `Kakeya.ThinCase.exists_ball_volume_inter_ge_of_subset` (blueprint `lem:ml2thinDeltaBall`):
  a dense `δ`-ball inside a tube segment, obtained by *averaging* over a boundedly
  overlapping cover;
* `Kakeya.ThinCase.liftFibre`, `Kakeya.ThinCase.lift` (blueprint `lem:ml2thinLiftFibre`,
  `lem:ml2thinLift`): passing from a shading on the tube segments `𝕋_B` back to the global
  shading on `𝕋`;
* `Kakeya.ThinCase.amalgamateContainment`, `Kakeya.ThinCase.amalgamateCost` (blueprint
  `lem:ml2thinAmalgamateContainment`, `lem:ml2thinAmalgamateCost`): amalgamating the
  per-ball refinements over all balls of the cover, using the subordinate partition.

Throughout, every implicit constant of the blueprint (`∼`, `≈`, `⪆`, `⪅`) is made explicit.
-/

@[expose] public section

namespace Kakeya.ThinCase

open MeasureTheory Metric Set

section General

variable {E : Type*} [MeasureSpace E]

open scoped Classical in
/-- **From a summed refinement to a large subfamily** (blueprint `lem:massMarkovUpgrade`).

Let `(V i)_{i ∈ I}` be a finite family carrying two shadings `Y` and `Y'` with
`Y' i ⊆ Y i`, and suppose `∑ |Y' i| ≥ κ ∑ |Y i|`. Then the subfamily
`𝒮 = {i ∈ I | |Y' i| ≥ (κ / 2) |Y i|}` carries at least a `κ / 2` fraction of the mass. -/
theorem massMarkovUpgrade {ι : Type*} (I : Finset ι) (Y Y' : ι → Set E)
    (hsub : ∀ i ∈ I, Y' i ⊆ Y i)
    (hfin : ∀ i ∈ I, volume (Y i) ≠ ⊤)
    {κ : NNReal}
    (hsum : (κ : ENNReal) * ∑ i ∈ I, volume (Y i) ≤ ∑ i ∈ I, volume (Y' i)) :
    ((κ / 2 : NNReal) : ENNReal) * ∑ i ∈ I, volume (Y i) ≤
      ∑ i ∈ {i ∈ I | ((κ / 2 : NNReal) : ENNReal) * volume (Y i) ≤ volume (Y' i)},
        volume (Y i) := by
  classical
  let p : ι → Prop := fun i => ((κ / 2 : NNReal) : ENNReal) * volume (Y i) ≤ volume (Y' i)
  let S : Finset ι := I.filter p
  let T : Finset ι := I.filter fun i => ¬ p i
  let M : ENNReal := ∑ i ∈ I, volume (Y i)
  let Ssum : ENNReal := ∑ i ∈ S, volume (Y i)
  -- on `S`, `Y' i ⊆ Y i`, so `volume (Y' i) ≤ volume (Y i)`
  have hS_le : ∑ i ∈ S, volume (Y' i) ≤ Ssum := by
    dsimp [Ssum]
    refine Finset.sum_le_sum ?_
    intro i hi
    have hmem : i ∈ I ∧ p i := by simpa [S] using hi
    exact measure_mono (hsub i hmem.1)
  -- on `I \ S` the defining inequality fails, so `volume (Y' i) ≤ (κ / 2) * volume (Y i)`
  have hT_le : ∑ i ∈ T, volume (Y' i) ≤ (κ / 2 : NNReal) * (∑ i ∈ T, volume (Y i)) := by
    calc
      ∑ i ∈ T, volume (Y' i) ≤ ∑ i ∈ T, ((κ / 2 : NNReal) : ENNReal) * volume (Y i) := by
        refine Finset.sum_le_sum ?_
        intro i hi
        have hmem : i ∈ I ∧ ¬ p i := by simpa [T] using hi
        exact le_of_lt (lt_of_not_ge (by simpa [p] using hmem.2))
      _ = (κ / 2 : NNReal) * (∑ i ∈ T, volume (Y i)) := by
        rw [Finset.mul_sum]
  -- split `∑ i ∈ I, volume (Y' i)` along `S` and `T`
  have hsplit : ∑ i ∈ I, volume (Y' i) ≤ Ssum + (κ / 2 : NNReal) * (∑ i ∈ T, volume (Y i)) := by
    calc
      ∑ i ∈ I, volume (Y' i) = (∑ i ∈ S, volume (Y' i)) + (∑ i ∈ T, volume (Y' i)) := by
        have hfs := Finset.sum_filter_add_sum_filter_not I p (fun i => volume (Y' i))
        simpa [S, T] using hfs.symm
      _ ≤ Ssum + (κ / 2 : NNReal) * (∑ i ∈ T, volume (Y i)) := add_le_add hS_le hT_le
  have hmain : (κ : ENNReal) * M ≤ Ssum + (κ / 2 : NNReal) * (∑ i ∈ T, volume (Y i)) := by
    dsimp [M, Ssum]
    exact le_trans hsum hsplit
  -- `∑ i ∈ T, volume (Y i) ≤ M` since `T ⊆ I` and the terms are non-negative
  have hTsum_le : (∑ i ∈ T, volume (Y i)) ≤ M := by
    dsimp [M]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro i hi
      exact (by simpa [T] using hi : i ∈ I ∧ ¬ p i).1
    · intro i _
      simp
  have hT_le_M : (κ / 2 : NNReal) * (∑ i ∈ T, volume (Y i)) ≤ (κ / 2 : NNReal) * M :=
    mul_le_mul_of_nonneg_left hTsum_le (by positivity)
  have hmain2 : (κ : ENNReal) * M ≤ Ssum + (κ / 2 : NNReal) * M :=
    le_trans hmain (add_le_add_right hT_le_M Ssum)
  -- `κ = κ / 2 + κ / 2`, so subtracting the finite quantity `(κ / 2) * M` from `hmain2`
  have hκhalf : (κ : NNReal) = κ / 2 + κ / 2 := by norm_num
  have hκ2 : (κ : ENNReal) = ((κ / 2 : NNReal) : ENNReal) + ((κ / 2 : NNReal) : ENNReal) := by
    rw [← ENNReal.coe_add]
    exact congrArg (fun q : NNReal => (q : ENNReal)) hκhalf
  have hMtop : M ≠ ⊤ := by
    dsimp [M]
    exact ENNReal.sum_ne_top.2 (fun i hi => hfin i hi)
  have hfin2 : (κ / 2 : NNReal) * M ≠ ⊤ :=
    ENNReal.mul_ne_top
      (ENNReal.coe_ne_top : ((κ / 2 : NNReal) : ENNReal) ≠ ⊤) hMtop
  change ((κ / 2 : NNReal) : ENNReal) * M ≤ Ssum
  exact (ENNReal.add_le_add_iff_right hfin2).mp (by
    calc
      ((κ / 2 : NNReal) : ENNReal) * M + ((κ / 2 : NNReal) : ENNReal) * M
          = (((κ / 2 : NNReal) : ENNReal) + ((κ / 2 : NNReal) : ENNReal)) * M := by
        rw [add_mul]
      _ = (κ : ENNReal) * M := by rw [hκ2]
      _ ≤ Ssum + (κ / 2 : NNReal) * M := hmain2)

open scoped Classical in
/-- **The cardinality half of the mass–Markov upgrade** (blueprint `lem:massMarkovUpgrade`,
final sentence): if in addition the masses
`|Y i|` are all comparable to a single value `m` up to a factor `C`, then the subfamily
`𝒮` is also a `⪆ κ / 2` fraction of `I` in cardinality.

Finiteness of the masses is not assumed: `hcomp` bounds `volume (Y i)` by `C * m` and `m ≠ ⊤`,
so `volume (Y i) ≠ ⊤` follows and `massMarkovUpgrade` can be applied. -/
theorem massMarkovUpgrade_card {ι : Type*} (I : Finset ι) (Y Y' : ι → Set E)
    (hsub : ∀ i ∈ I, Y' i ⊆ Y i)
    {κ C : NNReal}
    (hsum : (κ : ENNReal) * ∑ i ∈ I, volume (Y i) ≤ ∑ i ∈ I, volume (Y' i))
    {m : ENNReal} (hm0 : m ≠ 0) (hmtop : m ≠ ⊤)
    (hcomp : ∀ i ∈ I, volume (Y i) ≤ C * m ∧ m ≤ C * volume (Y i)) :
    ((κ / 2 : NNReal) : ENNReal) * I.card ≤
      (C : ENNReal) ^ 2 *
        {i ∈ I | ((κ / 2 : NNReal) : ENNReal) * volume (Y i) ≤ volume (Y' i)}.card := by
  let c : ENNReal := (C : ENNReal)
  let ka : ENNReal := ((κ / 2 : NNReal) : ENNReal)
  let S : Finset ι := {i ∈ I | ka * volume (Y i) ≤ volume (Y' i)}
  have hcomp' : ∀ i ∈ I, volume (Y i) ≤ c * m ∧ m ≤ c * volume (Y i) := by
    intro i hi
    simpa [c] using hcomp i hi
  -- Finiteness of the masses follows from `volume (Y i) ≤ C * m` and `m ≠ ⊤`.
  have hCtop : c * m ≠ ⊤ := by
    have hcm : c * m < ⊤ :=
      ENNReal.mul_lt_top (ENNReal.coe_lt_top : (C : ENNReal) < ⊤)
        (lt_top_iff_ne_top.mpr hmtop)
    exact ne_of_lt hcm
  have hfin : ∀ i ∈ I, volume (Y i) ≠ ⊤ := by
    intro i hi
    exact ne_of_lt (lt_of_le_of_lt (hcomp' i hi).1 (lt_top_iff_ne_top.mpr hCtop))
  -- The mass–Markov upgrade restricted to the counting subfamily.
  have hmas : ka * ∑ i ∈ I, volume (Y i) ≤ ∑ i ∈ S, volume (Y i) := by
    simpa [S, ka] using
      (massMarkovUpgrade (I := I) (Y := Y) (Y' := Y') hsub hfin (κ := κ) hsum)
  -- `|I| • m ≤ ∑_I |Y i|` termwise.
  have hlower : (I.card : ENNReal) * m ≤ c * ∑ i ∈ I, volume (Y i) := by
    have h1 : (I.card : ℕ) • m ≤ ∑ i ∈ I, c * volume (Y i) :=
      Finset.card_nsmul_le_sum (s := I) (f := fun i => c * volume (Y i)) (n := m)
        (fun i hi => (hcomp' i hi).2)
    calc
      (I.card : ENNReal) * m = (I.card : ℕ) • m := by
        rw [nsmul_eq_mul, mul_comm]
      _ ≤ ∑ i ∈ I, c * volume (Y i) := h1
      _ = c * ∑ i ∈ I, volume (Y i) := by rw [Finset.mul_sum]
  -- `∑_S |Y i| ≤ |S| • (C * m)` termwise.
  have hupper : ∑ i ∈ S, volume (Y i) ≤ (S.card : ENNReal) * (c * m) := by
    have hterm : ∀ i ∈ S, volume (Y i) ≤ c * m :=
      fun i hi => (hcomp' i (Finset.mem_filter.mp hi).1).1
    have h1 : ∑ i ∈ S, volume (Y i) ≤ (S.card : ℕ) • (c * m) :=
      Finset.sum_le_card_nsmul (s := S) (f := fun i => volume (Y i)) (n := c * m) hterm
    calc
      ∑ i ∈ S, volume (Y i) ≤ (S.card : ℕ) • (c * m) := h1
      _ = (S.card : ENNReal) * (c * m) := by
        rw [nsmul_eq_mul, mul_comm]
  -- Chain the two cardinality bounds through the mass–Markov inequality.
  have hmain : ka * I.card * m ≤ c ^ 2 * S.card * m := by
    calc
      ka * (I.card : ENNReal) * m = ka * ((I.card : ENNReal) * m) := by
        rw [mul_assoc]
      _ ≤ ka * (c * ∑ i ∈ I, volume (Y i)) := by
        gcongr
      _ = c * (ka * ∑ i ∈ I, volume (Y i)) := by
        ring
      _ ≤ c * ∑ i ∈ S, volume (Y i) := by
        gcongr
      _ ≤ c * ((S.card : ENNReal) * (c * m)) := by
        gcongr
      _ = c ^ 2 * (S.card : ENNReal) * m := by
        ring
  exact (ENNReal.mul_le_mul_iff_left hm0 hmtop).1 hmain

end General

section Thickness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Constant in Lemma `lem:tubeSegmentNbhdVolume`** (blueprint
`def:tubeSegmentNbhdConstant`).

For a thickness comparison constant `C₀ ≥ 1` as in (C3), this is an absolute constant
`≥ 1` such that every tube segment with `τ₀ ∼ r₁`, `τ₁ ∼ τ₂ ∼ δ` and `δ ≤ r₁` satisfies
`|N_{2δ}(T_B)| ≤ C |T_B|`. It depends only on `C₀`, and in particular not on `δ`, on the
ball, or on the segment. The displayed value is provisional; the exact value comes out of
the proof of `Kakeya.ThinCase.volume_cthickening_le_mul`. -/
noncomputable def tubeSegmentNbhdConstant (C₀ : NNReal) : NNReal := max 1 (2 ^ 12 * C₀ ^ 6)

lemma one_le_tubeSegmentNbhdConstant {C₀ : NNReal} : 1 ≤ tubeSegmentNbhdConstant C₀ :=
  le_max_left _ _

/-- **The `2δ`-neighbourhood of a tube segment has comparable volume** (blueprint
`lem:tubeSegmentNbhdVolume`).

If the convex body `K` has affine thicknesses `∼ (r₁, δ, δ)` with constant `C₀`, and
`δ ≤ r₁`, then `|N_{2δ}(K)| ≤ C |K|` with `C = tubeSegmentNbhdConstant C₀`. Only the upper
bound is recorded: the matching lower bound `|K| ≤ |N_{2δ}(K)|` is `measure_mono` applied to
`self_subset_cthickening`, and carrying it as a conjunct would leave a hypothesis-free
statement bundled with a hypothesis-laden one. -/
theorem volume_cthickening_le_mul (hdim : Module.finrank ℝ E = 3)
    {C₀ : NNReal} (hC₀ : 1 ≤ C₀) {δ r₁ : ℝ} (hδ : 0 < δ) (hδr₁ : δ ≤ r₁)
    (K : ConvexSpaceBody E) (hthick : HasThicknesses K.carrier C₀ ![r₁, δ, δ]) :
    volume (cthickening (2 * δ) K.carrier) ≤ tubeSegmentNbhdConstant C₀ * volume K.carrier := by
  let s : Set E := K.carrier
  have hconv : Convex ℝ s := K.convex
  have hbdd : Bornology.IsBounded s := K.isBounded
  have hδ0 : 0 ≤ δ := le_of_lt hδ
  have h2δ0 : 0 ≤ 2 * δ := by positivity
  have hr10 : 0 ≤ r₁ := le_trans hδ0 hδr₁
  have hC0pos : 0 < (C₀ : ℝ) := by
    have : (1 : ℝ) ≤ (C₀ : ℝ) := by exact_mod_cast hC₀
    linarith
  have hC0nonneg : 0 ≤ (C₀ : ℝ) := by positivity
  have hNtriv : 0 < Module.finrank ℝ E := by rw [hdim]; norm_num
  haveI : Nontrivial E := Module.nontrivial_of_finrank_pos hNtriv
  let t : Fin 3 → ℝ := ![r₁, δ, δ]
  have hthick_vals : ∀ k : Fin 3,
      (C₀ : ℝ)⁻¹ * t k ≤ Metric.thickness ℝ s (k : ℕ) ∧
      Metric.thickness ℝ s (k : ℕ) ≤ (C₀ : ℝ) * t k := by
    simpa [HasThicknesses, t, s] using hthick
  let hi0 : Fin 3 := 0
  let hi1 : Fin 3 := 1
  let hi2 : Fin 3 := 2
  rcases hthick_vals hi0 with ⟨h0_low, h0_up⟩
  rcases hthick_vals hi1 with ⟨h1_low, h1_up⟩
  rcases hthick_vals hi2 with ⟨h2_low, h2_up⟩
  have h0val : (hi0 : ℕ) = 0 := rfl
  have h1val : (hi1 : ℕ) = 1 := rfl
  have h2val : (hi2 : ℕ) = 2 := rfl
  have h0t : t hi0 = r₁ := by simp [t, hi0]
  have h1t : t hi1 = δ := by simp [t, hi1]
  have h2t : t hi2 = δ := by simp [t, hi2]
  let C : ENNReal := (C₀ : ENNReal)
  let R₁ : ENNReal := ENNReal.ofReal r₁
  let Δ : ENNReal := ENNReal.ofReal δ
  have hCtop : C ≠ ⊤ := by simp [C]
  have hCne0 : C ≠ 0 := by
    have : (0 : NNReal) < C₀ := lt_of_lt_of_le (by norm_num) hC₀
    exact ENNReal.coe_ne_zero.mpr (ne_of_gt this)
  have hC1 : (1 : ENNReal) ≤ C := by
    simpa [C] using (show (1 : ENNReal) ≤ (C₀ : ENNReal) from by exact_mod_cast hC₀)
  have he0 : Metric.ethickness ℝ s 0 = ENNReal.ofReal (Metric.thickness ℝ s 0) :=
    Metric.ethickness_thickness' hbdd 0
  have he1 : Metric.ethickness ℝ s 1 = ENNReal.ofReal (Metric.thickness ℝ s 1) :=
    Metric.ethickness_thickness' hbdd 1
  have he2 : Metric.ethickness ℝ s 2 = ENNReal.ofReal (Metric.thickness ℝ s 2) :=
    Metric.ethickness_thickness' hbdd 2
  -- upper bounds on the ethicknesses
  have hup0 : Metric.ethickness ℝ s 0 ≤ C * R₁ := by
    rw [he0]
    calc
      ENNReal.ofReal (Metric.thickness ℝ s 0) ≤ ENNReal.ofReal ((C₀ : ℝ) * r₁) :=
        ENNReal.ofReal_le_ofReal (by simpa [h0val, h0t] using h0_up)
      _ = C * R₁ := by
        simp [C, R₁, ENNReal.ofReal_mul hC0nonneg]
  have hup1 : Metric.ethickness ℝ s 1 ≤ C * Δ := by
    rw [he1]
    calc
      ENNReal.ofReal (Metric.thickness ℝ s 1) ≤ ENNReal.ofReal ((C₀ : ℝ) * δ) :=
        ENNReal.ofReal_le_ofReal (by simpa [h1val, h1t] using h1_up)
      _ = C * Δ := by
        simp [C, Δ, ENNReal.ofReal_mul hC0nonneg]
  have hup2 : Metric.ethickness ℝ s 2 ≤ C * Δ := by
    rw [he2]
    calc
      ENNReal.ofReal (Metric.thickness ℝ s 2) ≤ ENNReal.ofReal ((C₀ : ℝ) * δ) :=
        ENNReal.ofReal_le_ofReal (by simpa [h2val, h2t] using h2_up)
      _ = C * Δ := by
        simp [C, Δ, ENNReal.ofReal_mul hC0nonneg]
  -- lower bounds on the ethicknesses
  have hCinv : C⁻¹ = ENNReal.ofReal ((C₀ : ℝ)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos hC0pos]
    simp [C]
  have hlow0 : C⁻¹ * R₁ ≤ Metric.ethickness ℝ s 0 := by
    rw [he0]
    calc
      C⁻¹ * R₁ = ENNReal.ofReal ((C₀ : ℝ)⁻¹) * ENNReal.ofReal r₁ := by
        simp [hCinv, R₁]
      _ = ENNReal.ofReal ((C₀ : ℝ)⁻¹ * r₁) := by
        rw [ENNReal.ofReal_mul (show 0 ≤ (C₀ : ℝ)⁻¹ from by positivity)]
      _ ≤ ENNReal.ofReal (Metric.thickness ℝ s 0) :=
        ENNReal.ofReal_le_ofReal (by simpa [h0val, h0t] using h0_low)
  have hlow1 : C⁻¹ * Δ ≤ Metric.ethickness ℝ s 1 := by
    rw [he1]
    calc
      C⁻¹ * Δ = ENNReal.ofReal ((C₀ : ℝ)⁻¹) * ENNReal.ofReal δ := by
        simp [hCinv, Δ]
      _ = ENNReal.ofReal ((C₀ : ℝ)⁻¹ * δ) := by
        rw [ENNReal.ofReal_mul (show 0 ≤ (C₀ : ℝ)⁻¹ from by positivity)]
      _ ≤ ENNReal.ofReal (Metric.thickness ℝ s 1) :=
        ENNReal.ofReal_le_ofReal (by simpa [h1val, h1t] using h1_low)
  have hlow2 : C⁻¹ * Δ ≤ Metric.ethickness ℝ s 2 := by
    rw [he2]
    calc
      C⁻¹ * Δ = ENNReal.ofReal ((C₀ : ℝ)⁻¹) * ENNReal.ofReal δ := by
        simp [hCinv, Δ]
      _ = ENNReal.ofReal ((C₀ : ℝ)⁻¹ * δ) := by
        rw [ENNReal.ofReal_mul (show 0 ≤ (C₀ : ℝ)⁻¹ from by positivity)]
      _ ≤ ENNReal.ofReal (Metric.thickness ℝ s 2) :=
        ENNReal.ofReal_le_ofReal (by simpa [h2val, h2t] using h2_low)
  -- Convex lower bound on volume via the ethickness product
  have hEthprod : ((6 : NNReal)⁻¹ : ENNReal) *
      (Metric.ethickness ℝ s 0 * Metric.ethickness ℝ s 1 * Metric.ethickness ℝ s 2) ≤ volume s := by
    have hv := Convex.ethickness_prod_le_volume (s := s) hconv
    rw [hdim] at hv
    have hc3 : (Metric.lt_volume_convexHull.c 3 : ENNReal) = ((6 : NNReal)⁻¹ : ENNReal) := by
      simp [Metric.lt_volume_convexHull.c, show (Nat.factorial 3 : ℕ) = 6 by norm_num]
    rw [hc3] at hv
    have hprod : ∏ i ∈ Finset.range 3, Metric.ethickness ℝ s i =
        Metric.ethickness ℝ s 0 * Metric.ethickness ℝ s 1 * Metric.ethickness ℝ s 2 := by
      simp [Finset.prod_range_succ]
    simpa [hprod] using hv
  have hLowProd : ((6 : NNReal)⁻¹ : ENNReal) *
      ((C⁻¹ * R₁) * (C⁻¹ * Δ) * (C⁻¹ * Δ)) ≤ volume s :=
    le_trans (by gcongr) hEthprod
  -- volume lower bound in divided-clear form
  have hCC : C * C⁻¹ = 1 := ENNReal.mul_inv_cancel hCne0 hCtop
  have hC3 : C ^ 3 * C⁻¹ ^ 3 = 1 := by
    rw [← mul_pow]
    rw [hCC]
    norm_num
  have hsix : (6 : ENNReal) * ((6 : NNReal)⁻¹ : ENNReal) = 1 := by
    simpa using (ENNReal.mul_inv_cancel (by norm_num : (6 : ENNReal) ≠ 0)
      (by norm_num : (6 : ENNReal) ≠ ⊤) :
      (6 : ENNReal) * (6 : ENNReal)⁻¹ = 1)
  have hLowProdEq : ((C⁻¹ * R₁) * (C⁻¹ * Δ) * (C⁻¹ * Δ)) = C⁻¹ ^ 3 * (R₁ * Δ ^ 2) := by
    ring
  have hMainEq : (6 : ENNReal) * C ^ 3 *
      (((6 : NNReal)⁻¹ : ENNReal) * ((C⁻¹ * R₁) * (C⁻¹ * Δ) * (C⁻¹ * Δ))) = R₁ * Δ ^ 2 := by
    rw [hLowProdEq]
    calc
      (6 : ENNReal) * C ^ 3 * (((6 : NNReal)⁻¹ : ENNReal) * (C⁻¹ ^ 3 * (R₁ * Δ ^ 2)))
          = (6 : ENNReal) * C ^ 3 * ((6 : NNReal)⁻¹ : ENNReal) * (C⁻¹ ^ 3 * (R₁ * Δ ^ 2)) := by
                ring
      _ = ((6 : ENNReal) * ((6 : NNReal)⁻¹ : ENNReal)) * (C ^ 3 * C⁻¹ ^ 3) * (R₁ * Δ ^ 2) := by
                ring
      _ = 1 * 1 * (R₁ * Δ ^ 2) := by rw [hsix, hC3]
      _ = R₁ * Δ ^ 2 := by simp
  have hLower : R₁ * Δ ^ 2 ≤ (6 : ENNReal) * C ^ 3 * volume s := by
    calc
      R₁ * Δ ^ 2 = (6 : ENNReal) * C ^ 3 *
          (((6 : NNReal)⁻¹ : ENNReal) * ((C⁻¹ * R₁) * (C⁻¹ * Δ) * (C⁻¹ * Δ))) :=
        hMainEq.symm
      _ ≤ (6 : ENNReal) * C ^ 3 * volume s := by
        gcongr
  -- 2δ = ρ used by the standard upper bound
  have hρ : (((2 * δ).toNNReal : NNReal) : ℝ) = 2 * δ := Real.coe_toNNReal (2 * δ) h2δ0
  have hρ2 : (((2 * δ).toNNReal : NNReal) : ENNReal) = 2 * Δ := by
    have hof : (((2 * δ).toNNReal : NNReal) : ENNReal) = ENNReal.ofReal (2 * δ) := by
      rfl
    rw [hof]
    rw [ENNReal.ofReal_mul (show 0 ≤ (2 : ℝ) by norm_num)]
    simp [Δ]
  have hΔleR : Δ ≤ R₁ := by simpa [Δ, R₁] using ENNReal.ofReal_le_ofReal hδr₁
  have hRleCR : R₁ ≤ C * R₁ := by
    calc
      R₁ = 1 * R₁ := by simp
      _ ≤ C * R₁ := by gcongr
  have hΔleCR : Δ ≤ C * R₁ := le_trans hΔleR hRleCR
  have hΔleCΔ : Δ ≤ C * Δ := by
    calc
      Δ = 1 * Δ := by simp
      _ ≤ C * Δ := by gcongr
  have hf0 : 2 * Δ + Metric.ethickness ℝ s 0 ≤ (3 : ENNReal) * C * R₁ := by
    calc
      2 * Δ + Metric.ethickness ℝ s 0 ≤ 2 * (C * R₁) + C * R₁ :=
        add_le_add (by gcongr) hup0
      _ = (3 : ENNReal) * C * R₁ := by ring
  have hf1 : 2 * Δ + Metric.ethickness ℝ s 1 ≤ (3 : ENNReal) * C * Δ := by
    calc
      2 * Δ + Metric.ethickness ℝ s 1 ≤ 2 * (C * Δ) + C * Δ :=
        add_le_add (by gcongr) hup1
      _ = (3 : ENNReal) * C * Δ := by ring
  have hf2 : 2 * Δ + Metric.ethickness ℝ s 2 ≤ (3 : ENNReal) * C * Δ := by
    calc
      2 * Δ + Metric.ethickness ℝ s 2 ≤ 2 * (C * Δ) + C * Δ :=
        add_le_add (by gcongr) hup2
      _ = (3 : ENNReal) * C * Δ := by ring
  have hvol_raw := volume_cthickening_le_prod_add (X := s) ((2 * δ).toNNReal)
  have hvol : volume (cthickening (2 * δ) s) ≤ (2 : ENNReal) ^ 3 *
      ((2 * Δ + Metric.ethickness ℝ s 0) * (2 * Δ + Metric.ethickness ℝ s 1) *
        (2 * Δ + Metric.ethickness ℝ s 2)) := by
    simpa [hdim, hρ, hρ2, Finset.prod_range_succ] using hvol_raw
  have h_up : volume (cthickening (2 * δ) s) ≤ 216 * C ^ 3 * R₁ * Δ ^ 2 := by
    calc
      volume (cthickening (2 * δ) s)
          ≤ (2 : ENNReal) ^ 3 * ((2 * Δ + Metric.ethickness ℝ s 0) *
              (2 * Δ + Metric.ethickness ℝ s 1) * (2 * Δ + Metric.ethickness ℝ s 2)) := hvol
      _ ≤ (2 : ENNReal) ^ 3 * (((3 : ENNReal) * C * R₁) * ((3 : ENNReal) * C * Δ) *
            ((3 : ENNReal) * C * Δ)) := by
            gcongr
      _ = 216 * C ^ 3 * R₁ * Δ ^ 2 := by
            ring_nf
  -- assemble
  have hcoeff : (4096 : ENNReal) * C ^ 6 ≤ (tubeSegmentNbhdConstant C₀ : ENNReal) := by
    have hnn : (4096 : NNReal) * C₀ ^ 6 ≤ tubeSegmentNbhdConstant C₀ := by
      dsimp [tubeSegmentNbhdConstant]
      have hpow : (4096 : NNReal) = 2 ^ 12 := by norm_num
      rw [hpow]
      exact le_max_right _ _
    have hE : (4096 : ENNReal) * C ^ 6 = ((4096 * C₀ ^ 6 : NNReal) : ENNReal) := by
      simp [C, ENNReal.coe_mul, ENNReal.coe_pow]
    rw [hE]
    exact_mod_cast hnn
  have h_final : 216 * C ^ 3 * R₁ * Δ ^ 2 ≤ (tubeSegmentNbhdConstant C₀ : ENNReal) * volume s := by
    calc
      216 * C ^ 3 * R₁ * Δ ^ 2 = 216 * C ^ 3 * (R₁ * Δ ^ 2) := by ring
      _ ≤ 216 * C ^ 3 * ((6 : ENNReal) * C ^ 3 * volume s) := by
            gcongr
      _ = (1296 : ENNReal) * C ^ 6 * volume s := by
            ring_nf
      _ ≤ (4096 : ENNReal) * C ^ 6 * volume s := by
            gcongr
            norm_num
      _ = (2 : ENNReal) ^ 12 * C ^ 6 * volume s := by
            norm_num
      _ ≤ (tubeSegmentNbhdConstant C₀ : ENNReal) * volume s := by
            have hc : (2 : ENNReal) ^ 12 * C ^ 6 ≤ (tubeSegmentNbhdConstant C₀ : ENNReal) := by
              rw [show (2 : ENNReal) ^ 12 = (4096 : ENNReal) by norm_num]
              exact hcoeff
            exact mul_le_mul_left hc (volume s)
  exact le_trans h_up h_final

end Thickness

section DeltaBall

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Constant in Lemma `lem:ml2thinDeltaBallSingle`** (blueprint
`def:ml2thinDeltaBallSingleConstant`).

For an overlap constant `D ≥ 1` of the `δ`-ball covers and a thickness comparison
constant `C₀`, this is `c = (D · C_{tubeSegmentNbhd})⁻¹`. It depends only on `D`
and `C₀`; in particular not on `δ`, on the ball `B`, or on the segment `T_B`. For `1 ≤ D` it
lies in `(0, 1]`, which is why the lemmas using it carry that hypothesis. -/
noncomputable def deltaBallSingleConstant (D : ℕ) (C₀ : NNReal) : NNReal :=
  ((D : NNReal) * tubeSegmentNbhdConstant C₀)⁻¹

/-- **A dense `δ`-ball in one tube segment** (blueprint `lem:ml2thinDeltaBallSingle`).

Let `K` be a tube segment (affine thicknesses `∼ (r₁, δ, δ)`), let `Z ⊆ K` be a shading of
it with `|Z| ≥ c₀ δ^η |K|`, and let `(ball (ctr i) δ)_{i ∈ cov}` be a `D`-boundedly
overlapping cover of `K` by `δ`-balls each of which meets `K`. Then one of the balls of the
cover satisfies `|B_δ ∩ Z| ≥ c_{single}(D, C₀) c₀ δ^η |B_δ|`.

This is pure averaging over the cover: no refinement is involved, so the conclusion is
available for *any* shading obeying the displayed lower bound. -/
theorem exists_ball_volume_inter_ge (hdim : Module.finrank ℝ E = 3)
    {C₀ : NNReal} (hC₀ : 1 ≤ C₀) {δ : NNReal} (hδ : 0 < δ) {r₁ : ℝ} (hδr₁ : (δ : ℝ) ≤ r₁)
    (η : ℝ) (K : ConvexSpaceBody E) (hthick : HasThicknesses K.carrier C₀ ![r₁, δ, δ])
    {ι : Type*} {D : ℕ} (hD : 1 ≤ D) (cov : Finset ι) (ctr : ι → E)
    (hcover : IsBoundedlyOverlappingCover cov ctr (fun _ => (δ : ℝ)) D K.carrier)
    (hmeets : ∀ i ∈ cov, (ball (ctr i) (δ : ℝ) ∩ K.carrier).Nonempty)
    (Z : Set E) (hZK : Z ⊆ K.carrier)
    {c₀ : NNReal} (hZ : (c₀ : ENNReal) * (δ : ENNReal) ^ η * volume K.carrier ≤ volume Z) :
    ∃ i ∈ cov, ((deltaBallSingleConstant D C₀ * c₀ : NNReal) : ENNReal) * (δ : ENNReal) ^ η *
      volume (ball (ctr i) (δ : ℝ)) ≤ volume (Z ∩ ball (ctr i) (δ : ℝ)) := by
  -- The cover of the nonempty convex body `K` is nonempty.
  have hcov : cov.Nonempty := by
    obtain ⟨x, hx⟩ := K.nonempty'
    obtain ⟨i, hi, _⟩ := Set.mem_iUnion₂.mp (hcover.subset_iUnion hx)
    exact ⟨i, hi⟩
  -- `∑ i ∈ cov, |B_i| ≤ D |N_{2δ}(K)|` by the boundedly-overlapping cover bound.
  have hsum : ∑ i ∈ cov, volume (ball (ctr i) (δ : ℝ)) ≤
      (D : ENNReal) * volume (cthickening (2 * (δ : ℝ)) K.carrier) :=
    IsBoundedlyOverlappingCover.sum_volume_le_mul_volume_cthickening
      (show 0 ≤ (δ : ℝ) from le_of_lt (by exact_mod_cast hδ)) hcover hmeets
  -- `|N_{2δ}(K)| ≤ C₀-constant · |K|` (`lem:tubeSegmentNbhdVolume`).
  have hcv : volume (cthickening (2 * (δ : ℝ)) K.carrier) ≤
      (tubeSegmentNbhdConstant C₀ : ENNReal) * volume K.carrier :=
    volume_cthickening_le_mul hdim hC₀ (by exact_mod_cast hδ) hδr₁ K hthick
  -- The defining cancellation `c_single(D, C₀) · D · C_{tube} = 1`, from `1 ≤ D`
  -- and `1 ≤ tubeSegmentNbhdConstant C₀` (hence both factors nonzero).
  have hsingle : (deltaBallSingleConstant D C₀ : ENNReal) * (D : ENNReal) *
      (tubeSegmentNbhdConstant C₀ : ENNReal) = 1 := by
    have hDnn : (D : NNReal) ≠ 0 :=
      ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : NNReal) < (1 : NNReal))
        (by exact_mod_cast hD))
    have ht : tubeSegmentNbhdConstant C₀ ≠ 0 :=
      ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : NNReal) < (1 : NNReal))
        one_le_tubeSegmentNbhdConstant)
    have hmul : (D : NNReal) * tubeSegmentNbhdConstant C₀ ≠ 0 := mul_ne_zero hDnn ht
    have hnn : deltaBallSingleConstant D C₀ * (D : NNReal) * tubeSegmentNbhdConstant C₀ = 1 := by
      dsimp [deltaBallSingleConstant]
      rw [mul_assoc]
      exact inv_mul_cancel₀ hmul
    exact_mod_cast hnn
  -- Total-mass bound for the pigeonhole: `c_single · c₀ · δ^η · ∑ |B_i| ≤ |Z|`.
  have hvol : ((deltaBallSingleConstant D C₀ * c₀ : NNReal) : ENNReal) * (δ : ENNReal) ^ η *
      (∑ i ∈ cov, volume (ball (ctr i) (δ : ℝ))) ≤ volume Z := by
    calc
      ((deltaBallSingleConstant D C₀ * c₀ : NNReal) : ENNReal) * (δ : ENNReal) ^ η *
          (∑ i ∈ cov, volume (ball (ctr i) (δ : ℝ)))
          = (deltaBallSingleConstant D C₀ : ENNReal) * (c₀ : ENNReal) * (δ : ENNReal) ^ η *
              (∑ i ∈ cov, volume (ball (ctr i) (δ : ℝ))) := by
              rw [ENNReal.coe_mul]
      _ ≤ (deltaBallSingleConstant D C₀ : ENNReal) * (c₀ : ENNReal) * (δ : ENNReal) ^ η *
              ((D : ENNReal) * volume (cthickening (2 * (δ : ℝ)) K.carrier)) := by
              gcongr
      _ ≤ (deltaBallSingleConstant D C₀ : ENNReal) * (c₀ : ENNReal) * (δ : ENNReal) ^ η *
              ((D : ENNReal) * ((tubeSegmentNbhdConstant C₀ : ENNReal) *
                  volume K.carrier)) := by
              gcongr
      _ = (deltaBallSingleConstant D C₀ : ENNReal) * (D : ENNReal) *
              (tubeSegmentNbhdConstant C₀ : ENNReal) *
              ((c₀ : ENNReal) * (δ : ENNReal) ^ η * volume K.carrier) := by
              ring
      _ = 1 * ((c₀ : ENNReal) * (δ : ENNReal) ^ η * volume K.carrier) := by
              rw [hsingle]
      _ = (c₀ : ENNReal) * (δ : ENNReal) ^ η * volume K.carrier := by
              simp
      _ ≤ volume Z := hZ
  -- Averaging over the cover (`lem:coverAveragePigeonhole`).
  exact exists_volume_inter_ball_ge hcov ctr (fun _ => (δ : ℝ))
    (hZK.trans hcover.subset_iUnion) hvol

/-- **Constant in Lemma `lem:ml2thinDeltaBall`** (blueprint `def:ml2thinDeltaBallConstant`).

For an overlap constant `D`, a thickness comparison constant `C₀`, the per-segment
refinement constant `c` and the density constant `c₁` of (C5), this is
`c_{single}(D, C₀) · c · c₁`; it lies in `(0, 1]` when `1 ≤ D` and `c, c₁ ≤ 1`. -/
noncomputable def deltaBallConstant (D : ℕ) (C₀ c c₁ : NNReal) : NNReal :=
  deltaBallSingleConstant D C₀ * c * c₁

/-- **Density in a typical `δ`-ball** (blueprint `lem:ml2thinDeltaBall`).

The same statement as `exists_ball_volume_inter_ge`, but with the hypothesis on the shading
split into the (C5) density bound `|Y_B(T_B)| ≥ c₁ δ^η |T_B|` and the per-segment
refinement bound `|Z_B(T_B)| ≥ c |Y_B(T_B)|`. Because the hypothesis is a bound on
`|Z_B(T_B)|` for each segment separately, the conclusion applies to any shading obtained
from `Y_B` by a refinement losing at most a fixed factor `c` on each segment; in particular
to the final shading of the thin case. -/
theorem exists_ball_volume_inter_ge_of_subset (hdim : Module.finrank ℝ E = 3)
    {C₀ : NNReal} (hC₀ : 1 ≤ C₀) {δ : NNReal} (hδ : 0 < δ) {r₁ : ℝ} (hδr₁ : (δ : ℝ) ≤ r₁)
    (η : ℝ) (K : ConvexSpaceBody E) (hthick : HasThicknesses K.carrier C₀ ![r₁, δ, δ])
    {ι : Type*} {D : ℕ} (hD : 1 ≤ D) (cov : Finset ι) (ctr : ι → E)
    (hcover : IsBoundedlyOverlappingCover cov ctr (fun _ => (δ : ℝ)) D K.carrier)
    (hmeets : ∀ i ∈ cov, (ball (ctr i) (δ : ℝ) ∩ K.carrier).Nonempty)
    (Y Z : Set E) (hZY : Z ⊆ Y) (hYK : Y ⊆ K.carrier)
    {c c₁ : NNReal}
    (hY : (c₁ : ENNReal) * (δ : ENNReal) ^ η * volume K.carrier ≤ volume Y)
    (hZ : (c : ENNReal) * volume Y ≤ volume Z) :
    ∃ i ∈ cov, ((deltaBallConstant D C₀ c c₁ : NNReal) : ENNReal) * (δ : ENNReal) ^ η *
      volume (ball (ctr i) (δ : ℝ)) ≤ volume (Z ∩ ball (ctr i) (δ : ℝ)) := by
  have hZK : Z ⊆ K.carrier := hZY.trans hYK
  have hZhy : ((c * c₁ : NNReal) : ENNReal) * (δ : ENNReal) ^ η * volume K.carrier ≤
      volume Z := by
    calc
      ((c * c₁ : NNReal) : ENNReal) * (δ : ENNReal) ^ η * volume K.carrier
          = (c : ENNReal) * ((c₁ : ENNReal) * (δ : ENNReal) ^ η * volume K.carrier) := by
            rw [ENNReal.coe_mul]
            ring
      _ ≤ (c : ENNReal) * volume Y := by
        gcongr
      _ ≤ volume Z := hZ
  simpa [deltaBallConstant, mul_assoc] using
    exists_ball_volume_inter_ge hdim hC₀ hδ hδr₁ η K hthick hD cov ctr hcover hmeets Z hZK hZhy

end DeltaBall

section Lift

variable {E : Type*} [MeasureSpace E]

open scoped Classical in
/-- **The fibre count in a single ball** (blueprint `lem:ml2thinLiftFibre`).

Here `I` indexes the global tube family `𝕋` with shading `Y`, `P` is the partition piece
`B̂` of the ball `B`, `segs` indexes the segments `𝕋_B` with shadings `Yb = Y_B` and
`Zb = Z_B ⊆ Y_B`, and `fam p = 𝕋(T_B)` are the (pairwise disjoint) families of parent
tubes. The map `Y2` is the lifted shading `Y^{(B)}(T) = Y(T) ∩ Z_B(T_B)`, extended by `∅`
on tubes with no parent segment. The fibre count `|𝕋(T_B)_Y(x)|` is comparable to `m` on
`Y_B(T_B)`, with comparison constant `C`.

The conclusion is the pair of identities
`∑_T |Y(T) ∩ B̂| ≈ m ∑_{T_B} |Y_B(T_B)|` and `∑_T |Y^{(B)}(T)| ≈ m ∑_{T_B} |Z_B(T_B)|`.

Measurability of all the sets involved is not a technicality here: both identities are proved
by integrating the fibre count, and for non-measurable shadings they are false (split `[0,1]`
into two complementary non-measurable halves). -/
theorem liftFibre {ι σ : Type*} (I : Finset ι) (Y : ι → Set E) (P : Set E)
    (segs : Finset σ) (Yb Zb : σ → Set E) (fam : σ → Finset ι) (Y2 : ι → Set E)
    (hPmeas : MeasurableSet P) (hYmeas : ∀ T ∈ I, MeasurableSet (Y T))
    (hYbmeas : ∀ p ∈ segs, MeasurableSet (Yb p)) (hZbmeas : ∀ p ∈ segs, MeasurableSet (Zb p))
    (hfam : ∀ p ∈ segs, fam p ⊆ I)
    (hfam_disj : (segs : Set σ).Pairwise fun p q => Disjoint (fam p) (fam q))
    (hZb : ∀ p ∈ segs, Zb p ⊆ Yb p)
    (hYb_subset : ∀ p ∈ segs, Yb p ⊆ P)
    (hparent : ∀ T ∈ I, (Y T ∩ P).Nonempty → ∃ p ∈ segs, T ∈ fam p)
    (hinto : ∀ p ∈ segs, ∀ T ∈ fam p, Y T ∩ P ⊆ Yb p)
    (hY2 : ∀ p ∈ segs, ∀ T ∈ fam p, Y2 T = Y T ∩ Zb p)
    (hY2_empty : ∀ T ∈ I, (∀ p ∈ segs, T ∉ fam p) → Y2 T = ∅)
    {C m : NNReal} (_hC : 1 ≤ C)
    (hfibre : ∀ p ∈ segs, ∀ x ∈ Yb p,
      (m : ENNReal) ≤ C * {T ∈ fam p | x ∈ Y T}.card ∧
        ({T ∈ fam p | x ∈ Y T}.card : ENNReal) ≤ C * m) :
    (∑ T ∈ I, volume (Y T ∩ P) ≤ (C : ENNReal) * (m * ∑ p ∈ segs, volume (Yb p)) ∧
        (m : ENNReal) * ∑ p ∈ segs, volume (Yb p) ≤ C * ∑ T ∈ I, volume (Y T ∩ P)) ∧
      (∑ T ∈ I, volume (Y2 T) ≤ (C : ENNReal) * (m * ∑ p ∈ segs, volume (Zb p)) ∧
        (m : ENNReal) * ∑ p ∈ segs, volume (Zb p) ≤ C * ∑ T ∈ I, volume (Y2 T)) := by
  classical
  -- Discarded contribution of the tubes with no parent segment.
  have hresid_a : ∀ T ∈ I, (∀ p ∈ segs, T ∉ fam p) → Y T ∩ P = ∅ := by
    intro T hT hnone
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    rcases hparent T hT ⟨x, hx⟩ with ⟨p, hp, hTp⟩
    exact hnone p hp hTp
  -- Regroup the global sum over `I` into the per-segment sums, discarding residual mass.
  have regroup (A : ι → Set E)
      (hAresid : ∀ T ∈ I, (∀ p ∈ segs, T ∉ fam p) → A T = ∅) :
      (∑ T ∈ I, volume (A T)) = ∑ p ∈ segs, ∑ T ∈ fam p, volume (A T) := by
    have hsub : segs.biUnion fam ⊆ I := Finset.biUnion_subset.mpr hfam
    have hfull : (∑ T ∈ I, volume (A T)) = ∑ T ∈ segs.biUnion fam, volume (A T) := by
      symm
      refine Finset.sum_subset hsub ?_
      intro T hT hnot
      have hres : ∀ p ∈ segs, T ∉ fam p := by
        intro p hp hTp
        exact hnot (Finset.mem_biUnion.mpr ⟨p, hp, hTp⟩)
      simp [hAresid T hT hres]
    rw [hfull]
    exact Finset.sum_biUnion hfam_disj
  -- Measurability of the fibre-count function (useful for the integral lower bounds).
  have hcard_meas (p : σ) (hp : p ∈ segs) :
      Measurable fun x => ({T ∈ fam p | x ∈ Y T}.card : ENNReal) := by
    have hcard : (fun x => ({T ∈ fam p | x ∈ Y T}.card : ENNReal))
        = fun x => ∑ T ∈ fam p, (Y T).indicator (fun _ => (1 : ENNReal)) x := by
      funext x
      rw [Finset.natCast_card_filter]
      simp only [Set.indicator_apply]
    rw [hcard]
    exact Finset.measurable_sum (s := fam p)
      (fun T hT => measurable_const.indicator (hYmeas T (hfam p hp hT)))
  -- Per-segment fibre identity for the first family `T ↦ Y T ∩ P` over `E = Yb p`.
  have hfibre1_id (p : σ) (hp : p ∈ segs) :
      ∑ T ∈ fam p, volume (Y T ∩ P) =
        ∫⁻ x in Yb p, ({T ∈ fam p | x ∈ Y T}.card : ENNReal) := by
    calc
      ∑ T ∈ fam p, volume (Y T ∩ P)
          = ∑ T ∈ fam p, volume ((Y T ∩ P) ∩ Yb p) := by
            refine Finset.sum_congr rfl fun T hT => ?_
            rw [Set.inter_eq_self_of_subset_left (hinto p hp T hT)]
      _ = ∫⁻ x in Yb p, ({T ∈ fam p | x ∈ Y T ∩ P}.card : ENNReal) := by
            rw [← lintegral_indicator (hYbmeas p hp)]
            calc
              ∑ T ∈ fam p, volume ((Y T ∩ P) ∩ Yb p) =
                  ∑ T ∈ fam p, volume (Yb p ∩ (Y T ∩ P)) := by
                    apply Finset.sum_congr rfl
                    intro T hT
                    rw [Set.inter_comm]
              _ = ∫⁻ x, ({T ∈ fam p | x ∈ Yb p ∩ (Y T ∩ P)}.card : ENNReal) := by
                simpa using
                  (sum_measure_inter_eq_lintegral_card_filter volume (fam p)
                    (fun T ↦ Y T ∩ P) (Yb p) (fun T hT ↦
                      (hYbmeas p hp).inter ((hYmeas T (hfam p hp hT)).inter hPmeas)))
              _ = ∫⁻ x, (Yb p).indicator
                  (fun x ↦ ({T ∈ fam p | x ∈ Y T ∩ P}.card : ENNReal)) x := by
                    refine lintegral_congr fun x ↦ ?_
                    by_cases hx : x ∈ Yb p
                    · rw [Set.indicator_of_mem hx]
                      congr 2
                      ext T
                      simp [hx]
                    · rw [Set.indicator_of_notMem hx]
                      simp [hx]
      _ = ∫⁻ x in Yb p, ({T ∈ fam p | x ∈ Y T}.card : ENNReal) := by
            refine setLIntegral_congr_fun (hYbmeas p hp) ?_
            intro x hx
            have hxP : x ∈ P := hYb_subset p hp hx
            have hEqFinset : {T ∈ fam p | x ∈ Y T ∧ x ∈ P} = {T ∈ fam p | x ∈ Y T} := by
              ext T
              simp [hxP]
            simp [hEqFinset]
  have hup1 (p : σ) (hp : p ∈ segs) :
      ∑ T ∈ fam p, volume (Y T ∩ P) ≤ (C : ENNReal) * (m * volume (Yb p)) := by
    calc
      ∑ T ∈ fam p, volume (Y T ∩ P)
          = ∫⁻ x in Yb p, ({T ∈ fam p | x ∈ Y T}.card : ENNReal) := hfibre1_id p hp
      _ ≤ ∫⁻ x in Yb p, ((C : ENNReal) * m) :=
            setLIntegral_mono measurable_const (fun x hx => (hfibre p hp x hx).2)
      _ = (C : ENNReal) * (m * volume (Yb p)) := by
            rw [setLIntegral_const, mul_assoc]
  -- Per-segment first lower bound.
  have hlo1 (p : σ) (hp : p ∈ segs) :
      (m : ENNReal) * volume (Yb p) ≤ C * ∑ T ∈ fam p, volume (Y T ∩ P) := by
    calc
      (m : ENNReal) * volume (Yb p) = ∫⁻ x in Yb p, (m : ENNReal) :=
        (setLIntegral_const (Yb p) (m : ENNReal)).symm
      _ ≤ ∫⁻ x in Yb p, ((C : ENNReal) * ({T ∈ fam p | x ∈ Y T}.card : ENNReal)) :=
            setLIntegral_mono (measurable_const.mul (hcard_meas p hp))
              (fun x hx => (hfibre p hp x hx).1)
      _ = (C : ENNReal) * ∫⁻ x in Yb p, ({T ∈ fam p | x ∈ Y T}.card : ENNReal) := by
            rw [lintegral_const_mul (C : ENNReal)]
            exact hcard_meas p hp
      _ = (C : ENNReal) * ∑ T ∈ fam p, volume (Y T ∩ P) := by
            rw [hfibre1_id p hp]
  -- Per-segment fibre identity for the second family `Y2` over `E = Zb p`.
  have hfibre2_id (p : σ) (hp : p ∈ segs) :
      ∑ T ∈ fam p, volume (Y2 T) =
        ∫⁻ x in Zb p, ({T ∈ fam p | x ∈ Y T}.card : ENNReal) := by
    calc
      ∑ T ∈ fam p, volume (Y2 T)
          = ∑ T ∈ fam p, volume (Y T ∩ Zb p) := by
            refine Finset.sum_congr rfl fun T hT => ?_
            rw [hY2 p hp T hT]
      _ = ∑ T ∈ fam p, volume ((Y T ∩ Zb p) ∩ Zb p) := by
            refine Finset.sum_congr rfl fun T hT => ?_
            rw [Set.inter_eq_self_of_subset_left (Set.inter_subset_right : Y T ∩ Zb p ⊆ Zb p)]
      _ = ∫⁻ x in Zb p, ({T ∈ fam p | x ∈ Y T ∩ Zb p}.card : ENNReal) := by
            rw [← lintegral_indicator (hZbmeas p hp)]
            calc
              ∑ T ∈ fam p, volume ((Y T ∩ Zb p) ∩ Zb p) =
                  ∑ T ∈ fam p, volume (Zb p ∩ (Y T ∩ Zb p)) := by
                    apply Finset.sum_congr rfl
                    intro T hT
                    rw [Set.inter_comm]
              _ = ∫⁻ x, ({T ∈ fam p | x ∈ Zb p ∩ (Y T ∩ Zb p)}.card : ENNReal) := by
                simpa using
                  (sum_measure_inter_eq_lintegral_card_filter volume (fam p)
                    (fun T ↦ Y T ∩ Zb p) (Zb p) (fun T hT ↦
                      (hZbmeas p hp).inter ((hYmeas T (hfam p hp hT)).inter (hZbmeas p hp))))
              _ = ∫⁻ x, (Zb p).indicator
                  (fun x ↦ ({T ∈ fam p | x ∈ Y T ∩ Zb p}.card : ENNReal)) x := by
                    refine lintegral_congr fun x ↦ ?_
                    by_cases hx : x ∈ Zb p
                    · rw [Set.indicator_of_mem hx]
                      congr 2
                      ext T
                      simp [hx]
                    · rw [Set.indicator_of_notMem hx]
                      simp [hx]
      _ = ∫⁻ x in Zb p, ({T ∈ fam p | x ∈ Y T}.card : ENNReal) := by
            refine setLIntegral_congr_fun (hZbmeas p hp) ?_
            intro x hx
            have hEqFinset : {T ∈ fam p | x ∈ Y T ∧ x ∈ Zb p} = {T ∈ fam p | x ∈ Y T} := by
              ext T
              simp [hx]
            simp [hEqFinset]
  -- Per-segment second upper bound.
  have hup2 (p : σ) (hp : p ∈ segs) :
      ∑ T ∈ fam p, volume (Y2 T) ≤ (C : ENNReal) * (m * volume (Zb p)) := by
    calc
      ∑ T ∈ fam p, volume (Y2 T)
          = ∫⁻ x in Zb p, ({T ∈ fam p | x ∈ Y T}.card : ENNReal) := hfibre2_id p hp
      _ ≤ ∫⁻ x in Zb p, ((C : ENNReal) * m) :=
            setLIntegral_mono measurable_const (fun x hx => (hfibre p hp x (hZb p hp hx)).2)
      _ = (C : ENNReal) * (m * volume (Zb p)) := by
            rw [setLIntegral_const, mul_assoc]
  -- Per-segment second lower bound.
  have hlo2 (p : σ) (hp : p ∈ segs) :
      (m : ENNReal) * volume (Zb p) ≤ C * ∑ T ∈ fam p, volume (Y2 T) := by
    calc
      (m : ENNReal) * volume (Zb p) = ∫⁻ x in Zb p, (m : ENNReal) :=
        (setLIntegral_const (Zb p) (m : ENNReal)).symm
      _ ≤ ∫⁻ x in Zb p, ((C : ENNReal) * ({T ∈ fam p | x ∈ Y T}.card : ENNReal)) :=
            setLIntegral_mono (measurable_const.mul (hcard_meas p hp))
              (fun x hx => (hfibre p hp x (hZb p hp hx)).1)
      _ = (C : ENNReal) * ∫⁻ x in Zb p, ({T ∈ fam p | x ∈ Y T}.card : ENNReal) := by
            rw [lintegral_const_mul (C : ENNReal)]
            exact hcard_meas p hp
      _ = (C : ENNReal) * ∑ T ∈ fam p, volume (Y2 T) := by
            rw [hfibre2_id p hp]
  constructor
  · constructor
    · calc
        (∑ T ∈ I, volume (Y T ∩ P))
            = ∑ p ∈ segs, ∑ T ∈ fam p, volume (Y T ∩ P) := regroup (fun T => Y T ∩ P) hresid_a
        _ ≤ ∑ p ∈ segs, (C : ENNReal) * (m * volume (Yb p)) :=
              Finset.sum_le_sum (fun p hp => hup1 p hp)
        _ = (C : ENNReal) * (m * ∑ p ∈ segs, volume (Yb p)) := by
              rw [← Finset.mul_sum, ← Finset.mul_sum]
    · calc
        (m : ENNReal) * ∑ p ∈ segs, volume (Yb p)
            = ∑ p ∈ segs, (m : ENNReal) * volume (Yb p) := by rw [Finset.mul_sum]
        _ ≤ ∑ p ∈ segs, C * ∑ T ∈ fam p, volume (Y T ∩ P) :=
              Finset.sum_le_sum (fun p hp => hlo1 p hp)
        _ = C * ∑ p ∈ segs, ∑ T ∈ fam p, volume (Y T ∩ P) := by rw [← Finset.mul_sum]
        _ = C * ∑ T ∈ I, volume (Y T ∩ P) := by
              rw [← regroup (fun T => Y T ∩ P) hresid_a]
  · constructor
    · calc
        (∑ T ∈ I, volume (Y2 T))
            = ∑ p ∈ segs, ∑ T ∈ fam p, volume (Y2 T) := regroup (fun T => Y2 T) hY2_empty
        _ ≤ ∑ p ∈ segs, (C : ENNReal) * (m * volume (Zb p)) :=
              Finset.sum_le_sum (fun p hp => hup2 p hp)
        _ = (C : ENNReal) * (m * ∑ p ∈ segs, volume (Zb p)) := by
              rw [← Finset.mul_sum, ← Finset.mul_sum]
    · calc
        (m : ENNReal) * ∑ p ∈ segs, volume (Zb p)
            = ∑ p ∈ segs, (m : ENNReal) * volume (Zb p) := by rw [Finset.mul_sum]
        _ ≤ ∑ p ∈ segs, C * ∑ T ∈ fam p, volume (Y2 T) :=
              Finset.sum_le_sum (fun p hp => hlo2 p hp)
        _ = C * ∑ p ∈ segs, ∑ T ∈ fam p, volume (Y2 T) := by rw [← Finset.mul_sum]
        _ = C * ∑ T ∈ I, volume (Y2 T) := by
              rw [← regroup (fun T => Y2 T) hY2_empty]

open scoped Classical in
/-- **Lifting a shading on `𝕋_B` to the global shading** (blueprint `lem:ml2thinLift`).

In the situation of `liftFibre`, suppose there is a subfamily `S ⊆ segs` carrying a `κ`
fraction of the mass of `Y_B` and on which `|Z_B(T_B)| ≥ c |Y_B(T_B)|`. Then the lifted
shading `Y^{(B)}` carries a `⪆ c κ` fraction of the mass of `Y` on the piece `B̂`.

Nothing is discarded: the index family is all of `segs`, and the segments outside `S`
simply contribute nothing to the left-hand side. -/
theorem lift {ι σ : Type*} (I : Finset ι) (Y : ι → Set E) (P : Set E)
    (segs : Finset σ) (Yb Zb : σ → Set E) (fam : σ → Finset ι) (Y2 : ι → Set E)
    (hPmeas : MeasurableSet P) (hYmeas : ∀ T ∈ I, MeasurableSet (Y T))
    (hYbmeas : ∀ p ∈ segs, MeasurableSet (Yb p)) (hZbmeas : ∀ p ∈ segs, MeasurableSet (Zb p))
    (hfam : ∀ p ∈ segs, fam p ⊆ I)
    (hfam_disj : (segs : Set σ).Pairwise fun p q => Disjoint (fam p) (fam q))
    (hZb : ∀ p ∈ segs, Zb p ⊆ Yb p)
    (hYb_subset : ∀ p ∈ segs, Yb p ⊆ P)
    (hparent : ∀ T ∈ I, (Y T ∩ P).Nonempty → ∃ p ∈ segs, T ∈ fam p)
    (hinto : ∀ p ∈ segs, ∀ T ∈ fam p, Y T ∩ P ⊆ Yb p)
    (hY2 : ∀ p ∈ segs, ∀ T ∈ fam p, Y2 T = Y T ∩ Zb p)
    (hY2_empty : ∀ T ∈ I, (∀ p ∈ segs, T ∉ fam p) → Y2 T = ∅)
    {C m : NNReal} (hC : 1 ≤ C)
    (hfibre : ∀ p ∈ segs, ∀ x ∈ Yb p,
      (m : ENNReal) ≤ C * {T ∈ fam p | x ∈ Y T}.card ∧
        ({T ∈ fam p | x ∈ Y T}.card : ENNReal) ≤ C * m)
    {c κ : NNReal} (S : Finset σ) (hS : S ⊆ segs)
    (hmass : (κ : ENNReal) * ∑ p ∈ segs, volume (Yb p) ≤ ∑ p ∈ S, volume (Yb p))
    (hterm : ∀ p ∈ S, (c : ENNReal) * volume (Yb p) ≤ volume (Zb p)) :
    ((c * κ : NNReal) : ENNReal) * ∑ T ∈ I, volume (Y T ∩ P) ≤
      (C : ENNReal) ^ 2 * ∑ T ∈ I, volume (Y2 T) := by
  obtain ⟨⟨hLF1, -⟩, -, hLF2⟩ :=
    liftFibre I Y P segs Yb Zb fam Y2 hPmeas hYmeas hYbmeas hZbmeas
      hfam hfam_disj hZb hYb_subset hparent hinto hY2 hY2_empty hC hfibre
  -- `c · κ · ∑_{segs} |Y_B| ≤ c · ∑_S |Y_B| ≤ ∑_S |Z_B| ≤ ∑_{segs} |Z_B|`.
  have key : (c : ENNReal) * ((κ : ENNReal) * ∑ p ∈ segs, volume (Yb p)) ≤
      ∑ p ∈ segs, volume (Zb p) :=
    (mul_le_mul_right hmass _).trans <| ((Finset.mul_sum ..).le.trans
      (Finset.sum_le_sum hterm)).trans (Finset.sum_le_sum_of_subset hS)
  calc
    ((c * κ : NNReal) : ENNReal) * ∑ T ∈ I, volume (Y T ∩ P)
        ≤ (c : ENNReal) * (κ : ENNReal) * ((C : ENNReal) * (m * ∑ p ∈ segs, volume (Yb p))) := by
          rw [ENNReal.coe_mul]; exact mul_le_mul_right hLF1 _
    _ = (C : ENNReal) * ((m : ENNReal) *
          ((c : ENNReal) * ((κ : ENNReal) * ∑ p ∈ segs, volume (Yb p)))) := by ring
    _ ≤ (C : ENNReal) * ((m : ENNReal) * ∑ p ∈ segs, volume (Zb p)) :=
          mul_le_mul_right (mul_le_mul_right key _) _
    _ ≤ (C : ENNReal) * ((C : ENNReal) * ∑ T ∈ I, volume (Y2 T)) := mul_le_mul_right hLF2 _
    _ = (C : ENNReal) ^ 2 * ∑ T ∈ I, volume (Y2 T) := by rw [← mul_assoc, ← pow_two]

end Lift

section Amalgamate

/-- **Amalgamating per-ball refinements: the containment** (blueprint
`lem:ml2thinAmalgamateContainment`).

Let `(P B)_{B ∈ bs}` be the pairwise disjoint pieces of the partition subordinate to the
cover `𝔅`, and for each `B` let `Z B` be the `B`-th per-ball shading of a fixed tube `T`.
Writing `A = Y(T)`, the amalgamated shading is `Y'(T) = ⨆_B (A ∩ Z B ∩ P B)`. Then the union
is disjoint and `Y'(T) ∩ P B ⊆ Z B`.

Restricting the `B`-th term to the partition piece `P B` (and not to the ball `B` itself)
is what removes the interference between overlapping balls; in the application the per-ball
shadings are supported in `P B` to begin with, so the restriction costs nothing, but that is
not needed here: disjointness of the pieces already forces `B' = B` in the term of the union
meeting `P B`.

The statement is purely set-theoretic: no measure on `E` is involved. -/
theorem amalgamateContainment {E β : Type*} (bs : Finset β) (P : β → Set E)
    (hdisj : (bs : Set β).PairwiseDisjoint P) (Z : β → Set E) (A : Set E) :
    ((bs : Set β).PairwiseDisjoint fun B => A ∩ Z B ∩ P B) ∧
      ∀ B ∈ bs, (⋃ B' ∈ bs, A ∩ Z B' ∩ P B') ∩ P B ⊆ Z B := by
  refine ⟨hdisj.mono fun B => Set.inter_subset_right, fun B hB x ⟨hxU, hxP⟩ => ?_⟩
  simp only [Set.mem_iUnion, exists_prop] at hxU
  obtain ⟨B', hB', ⟨-, hxZ⟩, hxP'⟩ := hxU
  rwa [hdisj.elim_set hB hB' x hxP hxP']

/-- **Amalgamating per-ball refinements: the refinement cost** (blueprint
`lem:ml2thinAmalgamateCost`).

With the pieces `P B` pairwise disjoint and covering every `Y T`, and with *one and the
same* constant `c` for every ball `B` (this is essential: `B`-dependent constants would
compound), the amalgamated shading `Y'` is a `⪆ c` refinement of `Y`.

The step summing over `B` is an *equality* by the mass identity for a partition
(blueprint `lem:partitionMassIdentity`), which is where the subordinate partition, rather
than the cover itself, pays for itself. -/
theorem amalgamateCost {E : Type*} [MeasureSpace E]
    {ι β : Type*} (I : Finset ι) (bs : Finset β) (P : β → Set E)
    (hdisj : (bs : Set β).PairwiseDisjoint P) (hPmeas : ∀ B ∈ bs, MeasurableSet (P B))
    (Y : ι → Set E)
    (hcov : ∀ T ∈ I, Y T ⊆ ⋃ B ∈ bs, P B)
    (Y2 : β → ι → Set E) (hsub : ∀ B ∈ bs, ∀ T ∈ I, Y2 B T ⊆ Y T ∩ P B)
    {c : NNReal}
    (hlift : ∀ B ∈ bs, (c : ENNReal) * ∑ T ∈ I, volume (Y T ∩ P B) ≤ ∑ T ∈ I, volume (Y2 B T))
    (Y' : ι → Set E) (hY' : ∀ T ∈ I, Y' T = ⋃ B ∈ bs, Y2 B T) :
    (c : ENNReal) * ∑ T ∈ I, volume (Y T) ≤ ∑ T ∈ I, volume (Y' T) := by
  -- Inline proof of the partition mass identity (blueprint `lem:partitionMassIdentity`):
  -- the sum of the masses of the pieces `F ∩ P B` equals `volume F` for any (a fortiori
  -- non-measurable) `F` covered by the pairwise disjoint, measurable pieces `P B`.
  -- No measurability of `F` is needed: each `volume (F ∩ P B)` is the restriction
  -- `volume.restrict (P B) F`, and restricted measures are finitely additive along the
  -- partition (via the outer measure).
  classical
  have hres_sum : ∀ s ⊆ bs, volume.restrict (⋃ B ∈ s, P B) =
      ∑ B ∈ s, volume.restrict (P B) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert b t hbt ih =>
        intro hs
        have hsubt : t ⊆ bs := fun x hx => hs (by simp [hx])
        have hbdisj : Disjoint (P b) (⋃ B ∈ t, P B) := by
          rw [Set.disjoint_iUnion₂_right]
          exact fun B hB => hdisj (hs (by simp)) (hsubt hB) fun h => hbt (h ▸ hB)
        rw [Finset.set_biUnion_insert, Finset.sum_insert hbt, ← ih hsubt,
          MeasureTheory.Measure.restrict_union hbdisj
            (Finset.measurableSet_biUnion t fun B hB => hPmeas B (hsubt hB))]
  have hbsmeas : MeasurableSet (⋃ B ∈ bs, P B) :=
    Finset.measurableSet_biUnion bs hPmeas
  have mass_id (F : Set E) (hF : F ⊆ ⋃ B ∈ bs, P B) :
      ∑ B ∈ bs, volume (F ∩ P B) = volume F := by
    calc
      ∑ B ∈ bs, volume (F ∩ P B)
          = (∑ B ∈ bs, volume.restrict (P B) : Measure E) F := by
              rw [MeasureTheory.Measure.finsetSum_apply]
              exact Finset.sum_congr rfl fun B hB =>
                (MeasureTheory.Measure.restrict_apply' (hPmeas B hB)).symm
      _ = volume F := by
              rw [← hres_sum bs Finset.Subset.rfl,
                MeasureTheory.Measure.restrict_apply' hbsmeas,
                Set.inter_eq_self_of_subset_left hF]
  -- The pieces `Y2 B T` restrict cleanly: each lies inside `Y' T ∩ P B`.
  have hsub' : ∀ B ∈ bs, ∀ T ∈ I, Y2 B T ⊆ Y' T ∩ P B := by
    intro B hB T hT
    rw [hY' T hT]
    exact Set.subset_inter (Set.subset_iUnion₂ (s := fun B (_ : B ∈ bs) => Y2 B T) B hB)
      ((hsub B hB T hT).trans Set.inter_subset_right)
  -- `Y' T` is covered by the partition pieces.
  have hcov' : ∀ T ∈ I, Y' T ⊆ ⋃ B ∈ bs, P B := fun T hT => by
    rw [hY' T hT]
    exact Set.iUnion₂_subset fun B hB =>
      ((hsub B hB T hT).trans Set.inter_subset_right).trans
        (Set.subset_iUnion₂ (s := fun B (_ : B ∈ bs) => P B) B hB)
  -- Lower bound: pull `c` through the partition mass identity on `Y`, apply the per-ball
  -- `hlift` termwise, and re-assemble by the mass identity for `Y'`.
  calc
    (c : ENNReal) * ∑ T ∈ I, volume (Y T)
        = ∑ B ∈ bs, (c : ENNReal) * ∑ T ∈ I, volume (Y T ∩ P B) := by
          rw [← Finset.sum_congr rfl fun T hT => mass_id (Y T) (hcov T hT), Finset.sum_comm,
            Finset.mul_sum]
    _ ≤ ∑ B ∈ bs, ∑ T ∈ I, volume (Y2 B T) := Finset.sum_le_sum hlift
    _ ≤ ∑ B ∈ bs, ∑ T ∈ I, volume (Y' T ∩ P B) :=
          Finset.sum_le_sum fun B hB =>
            Finset.sum_le_sum fun T hT => measure_mono (hsub' B hB T hT)
    _ = ∑ T ∈ I, ∑ B ∈ bs, volume (Y' T ∩ P B) := Finset.sum_comm
    _ = ∑ T ∈ I, volume (Y' T) := Finset.sum_congr rfl fun T hT => mass_id (Y' T) (hcov' T hT)

end Amalgamate

end Kakeya.ThinCase
