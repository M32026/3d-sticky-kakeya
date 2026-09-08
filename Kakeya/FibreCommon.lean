/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Tube.Nets
public import Kakeya.ChainUniform
public import Kakeya.Density
public import Kakeya.Frostman
public import Kakeya.Tube.Basic
public import Kakeya.Uniform
public import Kakeya.Mathlib.Finset
public import Mathlib.Tactic.Linarith.NNRealPreprocessor -- for `linarith` over `NNReal`
public import Kakeya.Sticky

/-!
# Shared fibre and node facilities

The part of the fibre/node machinery that is consumed from *outside* GWZ Lemma 7.7 -- by the shaded
uniform bridge, by the Katz-Tao bridge, and by the estimates that read a hierarchy without running
the dividing-scales dichotomy.

It is separated out so that the rest of those files can sit inside `Kakeya/MultiScaleFac/` with the
dichotomy they serve: without the split, the seven files holding this material would have to stay
below 7.7 for their outside consumers, and the 7.7 development could not be gathered in one place.

Everything here is about the *fibres* of a family over its node index and about the *classes* of a
cover -- the two index sets the estimates read a hierarchy through.  Facts that mention neither, and
that were once collected here for want of a home, now live in the layer they belong to: the tube
volume and rescale bounds in `Kakeya.Tube.Basic`, the grid-scale arithmetic in `Kakeya.GridScale`, the
`densityIn`/`maxDensity` bands in `Kakeya.Density`, and the greedy separated-net lemma in
`Kakeya.Mathlib.Finset`.

Declarations keep the namespace they are consumed under: the fibre notation is
`Kakeya.StickyKakeya`, everything else is `Kakeya.MultiScaleFac`.
-/

/-! ### The fibre notation

The fibre notation, split off from `Kakeya/Sticky.lean`.  These are implementation-level:
they are the shape every proof below is written in, but they are not part of the statement of
GWZ Theorem 7.3, which is why they live here
and not in `Kakeya.Sticky`. -/

@[expose] public section

open MeasureTheory Real Metric ConvexSpaceBody
open Tube

namespace Kakeya

namespace StickyKakeya

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*}

/-- The members of the fibre family: `i ↦ T_i^{(σ)}`, viewed as convex bodies.  Together with
`fibreIndex` this is the blueprint's
`𝕋_{σ∣ρ}[i₀] = (T_i^{(σ)})_{i ∈ s_{σ∣ρ}(i₀)}`; the *members* depend only on `σ`, the *index
set* is what depends on `ρ` and `i₀`. -/
def fibreBodies {δ : NNReal} (T : ι → Tube δ E) (σ : NNReal) : ι → ConvexSpaceBody E :=
  fun i => ((T i).rescale σ).toConvexSpaceBody

/-- The fibre index set `s_{σ∣ρ}(i₀) = {i ∈ s : T_i^{(σ)} ⊆ T_{i₀}^{(ρ)}}` of the blueprint's
notation paragraph.  Containment is compared at the level of convex bodies because
`T_i^{(σ)} : Tube σ E` and `T_{i₀}^{(ρ)} : Tube ρ E` have different types. -/
noncomputable def fibreIndex {δ : NNReal} (s : Finset ι) (T : ι → Tube δ E) (σ ρ : NNReal)
    (i₀ : ι) : Finset ι :=
  Kakeya.familyIn s (fibreBodies T σ) ((T i₀).rescale ρ).toConvexSpaceBody

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
@[simp]
theorem fibreBodies_self {δ : NNReal} (T : ι → Tube δ E) :
    fibreBodies T δ = fun i => (T i).toConvexSpaceBody := by
  funext i
  simp [fibreBodies]

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- At the finest scale `σ = δ` the fibre index set is exactly the `Finset.filter` that
`IsFrostmanAtEveryScale` uses. -/
theorem fibreIndex_self {δ : NNReal} (s : Finset ι) (T : ι → Tube δ E) (ρ : NNReal) (i₀ : ι) :
    fibreIndex s T δ ρ i₀ =
      s.filter (fun i => (T i).toConvexSpaceBody ≤ ((T i₀).rescale ρ).toConvexSpaceBody) := by
  classical
  simp [fibreIndex, Kakeya.familyIn]

/-- Definition 7.1(A): `T` is `C`-Frostman at every scale, i.e. for every `ρ ∈ [δ, 1]` and every
`i₀ ∈ s` the subfamily of tubes contained in the `ρ`-rescaling of `T i₀` is `C`-Frostman inside
that rescaling.  (`MultiScaleFac.isFrostmanAtGridScales_of_isFrostmanAtEveryScale` passes from
here to the grid reading of the same condition.) -/
def IsFrostmanAtEveryScale {δ : NNReal} (s : Finset ι) (T : ι → Tube δ E) (C : ENNReal) : Prop :=
  ∀ ρ : NNReal, δ ≤ ρ → ρ ≤ 1 → ∀ i₀ ∈ s,
        ConvexSpaceBody.IsFrostmanIn (s.filter (fun i =>
            (T i).toConvexSpaceBody ≤ (Tube.rescale (T i₀) ρ).toConvexSpaceBody))
          (fun i => (T i).toConvexSpaceBody)
          (Tube.rescale (T i₀) ρ).toConvexSpaceBody C

omit [Nontrivial E] in
lemma IsFrostmanAtEveryScale_def {δ : NNReal} (s : Finset ι) (T : ι → Tube δ E) (C : ENNReal) :
    IsFrostmanAtEveryScale s T C ↔
      ∀ ρ : NNReal, δ ≤ ρ → ρ ≤ 1 → ∀ i₀ ∈ s,
        ConvexSpaceBody.IsFrostmanIn (E := E)
          (s.filter (fun i =>
            (T i).toConvexSpaceBody ≤ (Tube.rescale (T i₀) ρ).toConvexSpaceBody))
          (fun i => (T i).toConvexSpaceBody)
          (Tube.rescale (T i₀) ρ).toConvexSpaceBody C := Iff.rfl

omit [Nontrivial E] in
/-- `IsFrostmanAtEveryScale` is monotone in the Frostman constant: increasing
the constant only weakens the assertion. -/
lemma IsFrostmanAtEveryScale.mono_constant {δ : NNReal} {s : Finset ι}
    {T : ι → Tube δ E} {C C' : ENNReal}
    (h : IsFrostmanAtEveryScale s T C) (hC : C ≤ C') :
    IsFrostmanAtEveryScale s T C' :=
  fun ρ hρ_lb hρ_ub i₀ hi₀ K' hK' =>
    (h ρ hρ_lb hρ_ub i₀ hi₀ K' hK').trans
      (mul_le_mul_of_nonneg_right hC bot_le)

omit [Nontrivial E] in
/-- `IsFrostmanAtEveryScale` read through the fibre-family notation: being Frostman at every
scale is exactly the statement that every fibre family `𝕋_{δ∣ρ}[i₀] = 𝕋[i₀;ρ]` is
`C`-Frostman in `T_{i₀}^{(ρ)}`. -/
theorem isFrostmanAtEveryScale_iff_fibre {δ : NNReal} (s : Finset ι) (T : ι → Tube δ E)
    (C : ENNReal) :
    IsFrostmanAtEveryScale s T C ↔
      ∀ ρ : NNReal, δ ≤ ρ → ρ ≤ 1 → ∀ i₀ ∈ s,
        ConvexSpaceBody.IsFrostmanIn (fibreIndex s T δ ρ i₀) (fibreBodies T δ)
          ((T i₀).rescale ρ).toConvexSpaceBody C := by
  simp only [IsFrostmanAtEveryScale, fibreIndex_self, fibreBodies_self]

end StickyKakeya
end Kakeya

end

/-! ### Reading a hierarchy through its gap nodes

The node of the coarser grid scale that a leaf is charged to, in the two forms the estimates
below need: along a chain (`gapNodeIndex`) and at a single scale (`gapNodeIndexAtScale`). -/

@[expose] public section

open MeasureTheory Real Metric
open Tube

namespace Kakeya

open StickyKakeya

namespace MultiScaleFac

universe u

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

variable {ι : Type*} {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E} {Cu : NNReal}



/-- The level-`k` nodes of a `Cu`-uniform hierarchy `𝒰` that are contained in the `θ`-thickening
of `T i₀`.  For a gap `(σ ka, σ kb)` of the chain of scales this is the "how many fine nodes fit
into one coarse tube" count that multiplies across gaps. -/
noncomputable def gapNodeIndex {N : ℕ} {σ : ℕ → NNReal} (𝒰 : ChainUniformTubeSet s T N σ Cu)
    (k : ℕ) (i₀ : ι) (θ : NNReal) : Finset ι :=
  Kakeya.familyIn (𝒰.cover.indexSet k) (fun j => (𝒰.cover.tube k j).toConvexSpaceBody)
    ((T i₀).rescale θ).toConvexSpaceBody


/-- The nodes of a `Cu`-uniform structure at scale `σ` that are contained in the `θ`-thickening of
`T i₀`.  For a gap `(σa, σb)` of a chain of scales this is the "how many fine nodes fit into one
coarse tube" count that multiplies across gaps; per-scale form of `gapNodeIndex`. -/
noncomputable def gapNodeIndexAtScale {σ : NNReal} (h : Tube.IsUniformAtScale s T σ Cu)
    (i₀ : ι) (θ : NNReal) : Finset ι :=
  Kakeya.familyIn h.parent (fun j => (h.parentTube j).toConvexSpaceBody)
    ((T i₀).rescale θ).toConvexSpaceBody


end MultiScaleFac
end Kakeya

end

/-! ### Fibre cardinality against density

The two-sided band between the cardinality of a fibre and the density of its members in the
anchor body, obtained from the tube volume bounds `Tube.le_volume` and `Tube.volume_le_of_le`
through `le_densityIn_mul_of_volume_band`. -/

@[expose] public section

open MeasureTheory Real Metric
open Tube

namespace Kakeya

open StickyKakeya

namespace MultiScaleFac

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E}

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- Every member of a fibre is contained in the anchor body of that fibre, so selecting the
members contained in the anchor changes nothing.  This is what lets the volume-band lemmas
`Kakeya.MultiScaleFac.densityIn_mul_le_of_volume_band` and
`Kakeya.MultiScaleFac.le_densityIn_mul_of_volume_band` be read as statements about the fibre
count. -/
theorem familyIn_fibreIndex_eq_self (σ ρ : NNReal) (i₀ : ι) :
    Kakeya.familyIn (fibreIndex s T σ ρ i₀) (fibreBodies T σ)
        ((T i₀).rescale ρ).toConvexSpaceBody = fibreIndex s T σ ρ i₀ := by
  simp [fibreIndex, Kakeya.familyIn, Finset.filter_filter]


omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- The anchor index belongs to its own fibre, as soon as the member scale does not exceed the
anchor scale.  This is what makes every fibre nonempty and hence every anchor density positive. -/
theorem mem_fibreIndex_self {σ ρ : NNReal} (hσρ : σ ≤ ρ) {i₀ : ι} (hi₀ : i₀ ∈ s) :
    i₀ ∈ fibreIndex s T σ ρ i₀ := by
  classical
  simp only [fibreIndex, Kakeya.familyIn, Finset.mem_filter, fibreBodies]
  exact ⟨hi₀, Tube.rescale_le_rescale_of_radius_le (T i₀) hσρ⟩


/-- **From density to count.**  The anchor density of a fibre, weighted by the minimal volume
`c_n ρ^{n-1}` of the anchor tube, is at most the fibre count weighted by the maximal volume
`C_n σ^{n-1}` of a member. -/
theorem densityIn_fibre_mul_le_card {σ : NNReal} (hσ1 : σ ≤ 1) (ρ : NNReal) (i₀ : ι) :
    Kakeya.densityIn (fibreIndex s T σ ρ i₀) (fibreBodies T σ)
          ((T i₀).rescale ρ).toConvexSpaceBody
        * (((Tube.le_volume.c (Module.finrank ℝ E) : NNReal) : ENNReal)
            * ((ρ : ENNReal) ^ (Module.finrank ℝ E - 1)))
      ≤ ((fibreIndex s T σ ρ i₀).card : ENNReal)
          * (((Tube.volume_le.C (Module.finrank ℝ E) : NNReal) : ENNReal)
              * ((σ : ENNReal) ^ (Module.finrank ℝ E - 1))) := by
  set n := Module.finrank ℝ E with hn
  set vlo := ((Tube.le_volume.c n : NNReal) : ENNReal) * ((ρ : ENNReal) ^ (n - 1)) with hvlo
  set vhi := ((Tube.volume_le.C n : NNReal) : ENNReal) * ((σ : ENNReal) ^ (n - 1)) with hvhi
  have hW : ∀ i ∈ fibreIndex s T σ ρ i₀, volume ((fibreBodies T σ) i).carrier ≤ vhi := by
    intro i hi
    have hvol := Tube.volume_le hσ1 ((T i).rescale σ)
    calc
      volume ((fibreBodies T σ) i).carrier = volume ((T i).rescale σ).carrier := rfl
      _ ≤ ((Tube.volume_le.C n * σ ^ (n - 1) : NNReal) : ENNReal) := by
        simpa [hn] using hvol
      _ = ((Tube.volume_le.C n : NNReal) : ENNReal) * ((σ : ENNReal) ^ (n - 1)) := by
        simp [ENNReal.coe_mul, ENNReal.coe_pow]
      _ = vhi := rfl
  have hK : vlo ≤ volume (((T i₀).rescale ρ).toConvexSpaceBody).carrier := by
    have hvol := Tube.le_volume ((T i₀).rescale ρ)
    calc
      vlo = ((Tube.le_volume.c n : NNReal) : ENNReal) * ((ρ : ENNReal) ^ (n - 1)) := rfl
      _ = (Tube.le_volume.c n * ρ ^ (n - 1) : NNReal) := by simp
      _ ≤ volume ((T i₀).rescale ρ).carrier := hvol
      _ = volume (((T i₀).rescale ρ).toConvexSpaceBody).carrier := rfl
  have h_band := densityIn_mul_le_of_volume_band (fibreIndex s T σ ρ i₀) (fibreBodies T σ)
    ((T i₀).rescale ρ).toConvexSpaceBody hW hK
  calc
    Kakeya.densityIn (fibreIndex s T σ ρ i₀) (fibreBodies T σ)
          ((T i₀).rescale ρ).toConvexSpaceBody
        * (((Tube.le_volume.c (Module.finrank ℝ E) : NNReal) : ENNReal)
            * ((ρ : ENNReal) ^ (Module.finrank ℝ E - 1)))
        = Kakeya.densityIn (fibreIndex s T σ ρ i₀) (fibreBodies T σ)
            ((T i₀).rescale ρ).toConvexSpaceBody * vlo := by
      simp [vlo, hn]
    _ ≤ ((Kakeya.familyIn (fibreIndex s T σ ρ i₀) (fibreBodies T σ)
          ((T i₀).rescale ρ).toConvexSpaceBody).card : ENNReal) * vhi := h_band
    _ = ((fibreIndex s T σ ρ i₀).card : ENNReal) * vhi := by
      rw [familyIn_fibreIndex_eq_self σ ρ i₀]
    _ = ((fibreIndex s T σ ρ i₀).card : ENNReal)
        * (((Tube.volume_le.C (Module.finrank ℝ E) : NNReal) : ENNReal)
            * ((σ : ENNReal) ^ (Module.finrank ℝ E - 1))) := by
      simp [vhi, hn]


/-- **From count to density.**  The reverse band of `densityIn_fibre_mul_le_card`: the fibre
count weighted by the minimal member volume `c_n σ^{n-1}` is at most the anchor density weighted
by the maximal anchor volume.  The anchor scale is allowed to exceed `1` (bounded by `b`), since
the multiscale argument inflates anchors by fixed factors. -/
theorem card_mul_le_densityIn_fibre {σ ρ b : NNReal} (hρb : ρ ≤ b) (i₀ : ι) :
    ((fibreIndex s T σ ρ i₀).card : ENNReal)
        * (((Tube.le_volume.c (Module.finrank ℝ E) : NNReal) : ENNReal)
            * ((σ : ENNReal) ^ (Module.finrank ℝ E - 1)))
      ≤ Kakeya.densityIn (fibreIndex s T σ ρ i₀) (fibreBodies T σ)
            ((T i₀).rescale ρ).toConvexSpaceBody
          * ((((1 + b) * Tube.volume_le.C (Module.finrank ℝ E) : NNReal) : ENNReal)
              * ((ρ : ENNReal) ^ (Module.finrank ℝ E - 1))) := by
  set n := Module.finrank ℝ E with hn
  set vlo := ((Tube.le_volume.c n : NNReal) : ENNReal) * ((σ : ENNReal) ^ (n - 1)) with hvlo
  set vhi :=
    ((((1 + b) * Tube.volume_le.C n : NNReal) : ENNReal) * ((ρ : ENNReal) ^ (n - 1))) with hvhi
  have hW : ∀ i ∈ fibreIndex s T σ ρ i₀, vlo ≤ volume ((fibreBodies T σ) i).carrier := by
    intro i hi
    have hvol := Tube.le_volume ((T i).rescale σ)
    calc
      vlo = ((Tube.le_volume.c n : NNReal) : ENNReal) * ((σ : ENNReal) ^ (n - 1)) := rfl
      _ = (Tube.le_volume.c n * σ ^ (n - 1) : NNReal) := by simp
      _ ≤ volume ((T i).rescale σ).carrier := hvol
      _ = volume ((fibreBodies T σ) i).carrier := rfl
  have hK : volume (((T i₀).rescale ρ).toConvexSpaceBody).carrier ≤ vhi := by
    have hvol := Tube.volume_le_of_le hρb ((T i₀).rescale ρ)
    have hconst : ((2 : NNReal) ^ n * (1 + b) : NNReal) ≤ (1 + b) * Tube.volume_le.C n := by
      unfold Tube.volume_le.C
      rw [pow_succ]
      calc (2 : NNReal) ^ n * (1 + b) = (1 + b) * 2 ^ n := by ring
        _ ≤ (1 + b) * (2 ^ n * 2) := by
            gcongr
            exact le_mul_of_one_le_right zero_le one_le_two
    calc
      volume (((T i₀).rescale ρ).toConvexSpaceBody).carrier = volume ((T i₀).rescale ρ).carrier :=
        rfl
      _ ≤ (((2 : NNReal) ^ n * (1 + b) * ρ ^ (n - 1) : NNReal) : ENNReal) := by
        simpa [hn] using hvol
      _ ≤ (((1 + b) * Tube.volume_le.C n * ρ ^ (n - 1) : NNReal) : ENNReal) :=
        ENNReal.coe_le_coe.mpr (mul_le_mul_left hconst _)
      _ = ((((1 + b) * Tube.volume_le.C n : NNReal) : ENNReal) * ((ρ : ENNReal) ^ (n - 1))) := by
        simp [ENNReal.coe_mul, ENNReal.coe_pow]
      _ = vhi := rfl
  have h_band := le_densityIn_mul_of_volume_band (fibreIndex s T σ ρ i₀) (fibreBodies T σ)
    ((T i₀).rescale ρ).toConvexSpaceBody hW hK
  calc
    ((fibreIndex s T σ ρ i₀).card : ENNReal)
        * (((Tube.le_volume.c (Module.finrank ℝ E) : NNReal) : ENNReal)
            * ((σ : ENNReal) ^ (Module.finrank ℝ E - 1)))
        = ((fibreIndex s T σ ρ i₀).card : ENNReal) * vlo := by
      simp [vlo, hn]
    _ = ((Kakeya.familyIn (fibreIndex s T σ ρ i₀) (fibreBodies T σ)
          ((T i₀).rescale ρ).toConvexSpaceBody).card : ENNReal) * vlo := by
      rw [familyIn_fibreIndex_eq_self σ ρ i₀]
    _ ≤ Kakeya.densityIn (fibreIndex s T σ ρ i₀) (fibreBodies T σ)
            ((T i₀).rescale ρ).toConvexSpaceBody * vhi := h_band
    _ = Kakeya.densityIn (fibreIndex s T σ ρ i₀) (fibreBodies T σ)
            ((T i₀).rescale ρ).toConvexSpaceBody
        * ((((1 + b) * Tube.volume_le.C (Module.finrank ℝ E) : NNReal) : ENNReal)
            * ((ρ : ENNReal) ^ (Module.finrank ℝ E - 1))) := by
      simp [vhi, hn]


end MultiScaleFac
end Kakeya

end

/-! ### Packing a fibre by fibres of a finer anchor

A fibre at an inflated anchor is covered by boundedly many fibres at the exact anchor, the
count being the dimensional packing constant `fibrePackConst`.  This is what converts a
statement read at one anchor into the same statement read at a neighbouring one. -/

@[expose] public section

open MeasureTheory Real Metric
open Tube

namespace Kakeya

open StickyKakeya

namespace MultiScaleFac

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-- The dimensional constant of the inflated-container fibre comparisons.  It is the `L¹`-box
packing count `2 · ((R + ε/4)/(ε/4)) ^ (2n)` at `R = 18ρ` and `ε = ρ/2`, the largest ratio
needed by `card_fibreIndex_le_of_inflated`; the factor `2` is the two orientations of
`Tube.endpoints_close_of_body_le`. -/
abbrev fibrePackConst (n : ℕ) : NNReal := 2 * 145 ^ (2 * n)


/-- **A dimensional net inside a common container tube.**  If every tube of a finite family lies
inside a single `r`-tube `W`, then for every `ε > 0` the family has an `ε`-net in the `L¹`
endpoint metric whose cardinality is bounded by the `L¹`-box packing count at radius `3r`. -/
theorem exists_net_of_le_common_tube {ι : Type*} {δ r : NNReal} (F : Finset ι)
    (T : ι → Tube δ E) (W : Tube r E)
    (hFW : ∀ i ∈ F, (T i).toConvexSpaceBody ≤ W.toConvexSpaceBody)
    {ε B : ℝ} (hε : 0 < ε)
    (hB : 2 * ((3 * (r : ℝ) + ε / 4) / (ε / 4)) ^ (2 * Module.finrank ℝ E) ≤ B) :
    ∃ F' ⊆ F,
      (∀ i ∈ F, ∃ a ∈ F', ‖(T i).x - (T a).x‖ + ‖(T i).y - (T a).y‖ ≤ ε) ∧
      (F'.card : ℝ) ≤ B := by
  classical
  set d : ι → ι → ℝ := fun i j => ‖(T i).x - (T j).x‖ + ‖(T i).y - (T j).y‖ with hd_def
  have hd_self : ∀ a, d a a = 0 := by
    intro a
    simp [hd_def]
  have hd_symm : ∀ a b, d a b = d b a := by
    intro a b
    simp [hd_def, norm_sub_rev]
  obtain ⟨F', hF'sub, hsep, hdense⟩ := Finset.exists_separated_net F d hε.le hd_self hd_symm
  refine ⟨F', hF'sub, hdense, ?_⟩
  set p : ι → Prop :=
    fun a => ‖(T a).x - W.x‖ ≤ 3 * (r : ℝ) ∧ ‖(T a).y - W.y‖ ≤ 3 * (r : ℝ) with hp_def
  set F₁ := F'.filter p with hF₁_def
  set F₂ := F'.filter (fun a => ¬ p a) with hF₂_def
  have hcard_sum : (F₁.card : ℝ) + (F₂.card : ℝ) = (F'.card : ℝ) := by
    have hcard_sum' : F₁.card + F₂.card = F'.card :=
      Finset.card_filter_add_card_filter_not (s := F') p
    exact_mod_cast hcard_sum'
  have hsep_F₁ : ∀ a ∈ F₁, ∀ b ∈ F₁, a ≠ b → ε ≤ ‖(T a).x - (T b).x‖ + ‖(T a).y - (T b).y‖ := by
    intro a ha b hb hne
    have ha' : a ∈ F' := (Finset.mem_filter.mp ha).1
    have hb' : b ∈ F' := (Finset.mem_filter.mp hb).1
    have h := hsep a ha' b hb' hne
    dsimp [d] at h
    linarith
  have hsep_F₂ : ∀ a ∈ F₂, ∀ b ∈ F₂, a ≠ b → ε ≤ ‖(T a).x - (T b).x‖ + ‖(T a).y - (T b).y‖ := by
    intro a ha b hb hne
    have ha' : a ∈ F' := (Finset.mem_filter.mp ha).1
    have hb' : b ∈ F' := (Finset.mem_filter.mp hb).1
    have h := hsep a ha' b hb' hne
    dsimp [d] at h
    linarith
  have hFW_sub : ∀ a ∈ F', (T a).toConvexSpaceBody ≤ W.toConvexSpaceBody := by
    intro a ha
    exact hFW a (hF'sub ha)
  have hinx₁ : ∀ a ∈ F₁, ‖(T a).x - W.x‖ ≤ 3 * (r : ℝ) := by
    intro a ha
    rcases Finset.mem_filter.mp ha with ⟨haF', hp_a⟩
    dsimp [p] at hp_a
    exact hp_a.1
  have hiny₁ : ∀ a ∈ F₁, ‖(T a).y - W.y‖ ≤ 3 * (r : ℝ) := by
    intro a ha
    rcases Finset.mem_filter.mp ha with ⟨haF', hp_a⟩
    dsimp [p] at hp_a
    exact hp_a.2
  have hcard_F₁_bound :
      (F₁.card : ℝ) ≤ ((3 * (r : ℝ) + ε / 4) / (ε / 4)) ^ (2 * Module.finrank ℝ E) := by
    have := Tube.card_le_of_L1_separated_in_box F₁ (fun a => (T a).x) (fun a => (T a).y) W.x W.y
      hε hsep_F₁ hinx₁ hiny₁
    exact this
  have h_second_orient :
      ∀ a ∈ F₂, ‖(T a).x - W.y‖ ≤ 3 * (r : ℝ) ∧ ‖(T a).y - W.x‖ ≤ 3 * (r : ℝ) := by
    intro a ha
    rcases Finset.mem_filter.mp ha with ⟨haF', hnot_p⟩
    have haFW : (T a).toConvexSpaceBody ≤ W.toConvexSpaceBody := hFW_sub a haF'
    have horient := Tube.endpoints_close_of_body_le (T a) W haFW
    dsimp [p] at hnot_p
    have hnot_p' : ¬ (‖(T a).x - W.x‖ ≤ 3 * (r : ℝ) ∧ ‖(T a).y - W.y‖ ≤ 3 * (r : ℝ)) := hnot_p
    rcases horient with (h | h)
    · exfalso; exact hnot_p' h
    · exact h
  have hinx₂ : ∀ a ∈ F₂, ‖(T a).x - W.y‖ ≤ 3 * (r : ℝ) := by
    intro a ha
    exact (h_second_orient a ha).1
  have hiny₂ : ∀ a ∈ F₂, ‖(T a).y - W.x‖ ≤ 3 * (r : ℝ) := by
    intro a ha
    exact (h_second_orient a ha).2
  have hcard_F₂_bound :
      (F₂.card : ℝ) ≤ ((3 * (r : ℝ) + ε / 4) / (ε / 4)) ^ (2 * Module.finrank ℝ E) := by
    have := Tube.card_le_of_L1_separated_in_box F₂ (fun a => (T a).x) (fun a => (T a).y) W.y W.x
      hε hsep_F₂ hinx₂ hiny₂
    exact this
  have hcard_F'_bound :
      (F'.card : ℝ) ≤ 2 * ((3 * (r : ℝ) + ε / 4) / (ε / 4)) ^ (2 * Module.finrank ℝ E) := by
    calc
      (F'.card : ℝ) = (F₁.card : ℝ) + (F₂.card : ℝ) := by
        linarith
      _ ≤ ((3 * (r : ℝ) + ε / 4) / (ε / 4)) ^ (2 * Module.finrank ℝ E) +
          ((3 * (r : ℝ) + ε / 4) / (ε / 4)) ^ (2 * Module.finrank ℝ E) := by
        nlinarith
      _ = 2 * ((3 * (r : ℝ) + ε / 4) / (ε / 4)) ^ (2 * Module.finrank ℝ E) := by ring
  linarith


/-- **An inflated fibre is covered by dimensionally many tight gap fibres.**  If the container
radius `θ` is at most `6 σa`, then the leaves of `𝕋_{δ∣θ}[i₁]` are distributed among at most
`C(n)` of the gap fibres `s_{σb∣σa}(i₂)`, `i₂ ∈ s`. -/
theorem exists_gapFibre_cover_of_inflated {ι : Type*} {δ σa σb θ : NNReal}
    {s : Finset ι} {T : ι → Tube δ E}
    (hσa : 0 < σa) (_hδσb : δ ≤ σb) (hσb : 2 * σb ≤ σa) (hθ : θ ≤ 6 * σa) (i₁ : ι) :
    ∃ A ⊆ s, (A.card : ℝ) ≤ (fibrePackConst (Module.finrank ℝ E) : ℝ) ∧
      ∀ i ∈ fibreIndex s T δ θ i₁, ∃ i₂ ∈ A, i ∈ fibreIndex s T σb σa i₂ := by
  classical
  let F := fibreIndex s T δ θ i₁
  have hF_sub_s : F ⊆ s := by
    dsimp [F]
    rw [fibreIndex_self s T θ i₁]
    exact Finset.filter_subset _ _
  have hFW : ∀ i ∈ F, (T i).toConvexSpaceBody ≤ ((T i₁).rescale θ).toConvexSpaceBody := by
    intro i hi
    dsimp [F] at hi
    rw [fibreIndex_self s T θ i₁] at hi
    exact (Finset.mem_filter.mp hi).2
  let W := (T i₁).rescale θ
  have hεpos : 0 < (σa : ℝ)/2 := by linarith
  have hB_ineq : 2 * ((3*(θ : ℝ) + ((σa : ℝ)/2)/4) / (((σa : ℝ)/2)/4)) ^ (2 * Module.finrank ℝ E)
      ≤ (fibrePackConst (Module.finrank ℝ E) : ℝ) := by
    calc
      2 * ((3*(θ : ℝ) + ((σa : ℝ)/2)/4) / (((σa : ℝ)/2)/4)) ^ (2 * Module.finrank ℝ E)
          = 2 * ((3*(θ : ℝ) + (σa : ℝ)/8) / ((σa : ℝ)/8)) ^ (2 * Module.finrank ℝ E) := by ring
      _ ≤ 2 * 145 ^ (2 * Module.finrank ℝ E) := by
        have h_nonneg : 0 ≤ (3*(θ : ℝ) + (σa : ℝ)/8) / ((σa : ℝ)/8) := by
          apply div_nonneg
          · have hθ_nonneg : 0 ≤ (θ : ℝ) := NNReal.coe_nonneg _
            have hσa_nonneg : 0 ≤ (σa : ℝ) := NNReal.coe_nonneg _
            nlinarith
          · have hσa_nonneg : 0 ≤ (σa : ℝ) := NNReal.coe_nonneg _
            nlinarith
        have h_ratio : (3*(θ : ℝ) + (σa : ℝ)/8) / ((σa : ℝ)/8) ≤ 145 := by
          have h_sa8_pos : 0 < (σa : ℝ)/8 := by
            have hpos : 0 < (σa : ℝ) := by exact_mod_cast hσa
            linarith
          field_simp [h_sa8_pos.ne']
          nlinarith
        have h_pow : ((3*(θ : ℝ) + (σa : ℝ)/8) / ((σa : ℝ)/8)) ^ (2 * Module.finrank ℝ E)
            ≤ 145 ^ (2 * Module.finrank ℝ E) :=
          by gcongr
        nlinarith
      _ = (fibrePackConst (Module.finrank ℝ E) : ℝ) := by
        simp [fibrePackConst]
  rcases exists_net_of_le_common_tube F T W hFW hεpos hB_ineq with ⟨F', hF'sub_F, hnet, hcard⟩
  have hF'sub_s : F' ⊆ s := Finset.Subset.trans hF'sub_F hF_sub_s
  refine ⟨F', hF'sub_s, ?_, ?_⟩
  · simpa [fibrePackConst] using hcard
  · intro i hi
    have hi_F : i ∈ F := hi
    rcases hnet i hi_F with ⟨a, haF', hdist⟩
    have hi_s : i ∈ s := hF_sub_s hi_F
    have ha_s : a ∈ s := hF'sub_s haF'
    have hi_in_fibre_a : i ∈ fibreIndex s T σb σa a := by
      rw [fibreIndex, Kakeya.familyIn]
      apply Finset.mem_filter.mpr
      refine ⟨hi_s, ?_⟩
      have h_endpoint_dist : ‖(T i).x - (T a).x‖ + ‖(T i).y - (T a).y‖ + (σb : ℝ) ≤ (σa : ℝ) := by
        have h_2σb_le_σa : (2 : ℝ) * (σb : ℝ) ≤ (σa : ℝ) := by exact_mod_cast hσb
        linarith
      have h_body_ineq :
          ((T i).rescale σb).toConvexSpaceBody ≤ ((T a).rescale σa).toConvexSpaceBody :=
        Tube.rescale_le_rescale_of_endpoint_dist (T i) (T a) h_endpoint_dist
      simpa [fibreBodies]
    exact ⟨a, haF', hi_in_fibre_a⟩


/-- **A fibre at an arbitrarily inflated container is covered by `(ρ'/ρ)^{2n}` tight fibres.**
The unbounded-ratio companion of `exists_gapFibre_cover_of_inflated`: for any `ρ ≤ ρ'`, the leaves
of `𝕋_{δ∣ρ'}[i₀]` are distributed among at most `2 · (25 ρ'/ρ)^{2n}` of the tight fibres
`s_{σ∣ρ}(i₂)`, `i₂ ∈ s`. -/
theorem exists_gapFibre_cover_of_ratio {ι : Type*} {δ σ ρ ρ' : NNReal}
    {s : Finset ι} {T : ι → Tube δ E}
    (hρ : 0 < ρ) (_hδσ : δ ≤ σ) (hσρ : 2 * σ ≤ ρ) (hρρ' : ρ ≤ ρ') (i₀ : ι) :
    ∃ A ⊆ s,
      (A.card : ℝ) ≤ 2 * (25 : ℝ) ^ (2 * Module.finrank ℝ E)
          * ((ρ' : ℝ) / (ρ : ℝ)) ^ (2 * Module.finrank ℝ E) ∧
      ∀ i ∈ fibreIndex s T δ ρ' i₀, ∃ i₂ ∈ A, i ∈ fibreIndex s T σ ρ i₂ := by
  classical
  let F := fibreIndex s T δ ρ' i₀
  have hF_sub_s : F ⊆ s := by
    dsimp [F]
    rw [fibreIndex_self s T ρ' i₀]
    exact Finset.filter_subset _ _
  have hFW : ∀ i ∈ F, (T i).toConvexSpaceBody ≤ ((T i₀).rescale ρ').toConvexSpaceBody := by
    intro i hi
    dsimp [F] at hi
    rw [fibreIndex_self s T ρ' i₀] at hi
    exact (Finset.mem_filter.mp hi).2
  let W := (T i₀).rescale ρ'
  have hεpos : 0 < (ρ : ℝ)/2 := by
    have hρpos : 0 < (ρ : ℝ) := by exact_mod_cast hρ
    linarith
  have hB_ineq : 2 * ((3*(ρ' : ℝ) + ((ρ : ℝ)/2)/4) / (((ρ : ℝ)/2)/4)) ^ (2 * Module.finrank ℝ E)
      ≤ 2 * (25 : ℝ) ^ (2 * Module.finrank ℝ E)
        * ((ρ' : ℝ) / (ρ : ℝ)) ^ (2 * Module.finrank ℝ E) := by
    have hρ0 : (ρ : ℝ) ≠ 0 := by
      have hpos : 0 < (ρ : ℝ) := by exact_mod_cast hρ
      linarith
    have hρpos : 0 < (ρ : ℝ) := by exact_mod_cast hρ
    have hratio_eq : ((3 * (ρ' : ℝ) + (ρ : ℝ) / 8) / ((ρ : ℝ) / 8))
        = (24 * ((ρ' : ℝ) / (ρ : ℝ)) + 1) := by
      field_simp [hρ0]
      ring
    have h_one_le : (1 : ℝ) ≤ (ρ' : ℝ) / (ρ : ℝ) := by
      exact (one_le_div hρpos).mpr (by exact_mod_cast hρρ')
    have hratio_le : 24 * ((ρ' : ℝ) / (ρ : ℝ)) + 1 ≤ 25 * ((ρ' : ℝ) / (ρ : ℝ)) := by
      nlinarith
    have hratio_nonneg : 0 ≤ 24 * ((ρ' : ℝ) / (ρ : ℝ)) + 1 := by
      have hρ'nonneg : 0 ≤ (ρ' : ℝ) := NNReal.coe_nonneg _
      have hdivnonneg : 0 ≤ (ρ' : ℝ) / (ρ : ℝ) := div_nonneg hρ'nonneg (le_of_lt hρpos)
      nlinarith
    calc
      2 * ((3 * (ρ' : ℝ) + ((ρ : ℝ) / 2) / 4) / (((ρ : ℝ) / 2) / 4)) ^ (2 * Module.finrank ℝ E)
          = 2 * ((3 * (ρ' : ℝ) + (ρ : ℝ) / 8) / ((ρ : ℝ) / 8)) ^ (2 * Module.finrank ℝ E) := by ring
      _ = 2 * (24 * ((ρ' : ℝ) / (ρ : ℝ)) + 1) ^ (2 * Module.finrank ℝ E) := by
        rw [hratio_eq]
      _ ≤ 2 * (25 * ((ρ' : ℝ) / (ρ : ℝ))) ^ (2 * Module.finrank ℝ E) := by
        have hpow_le : (24 * ((ρ' : ℝ) / (ρ : ℝ)) + 1) ^ (2 * Module.finrank ℝ E)
            ≤ (25 * ((ρ' : ℝ) / (ρ : ℝ))) ^ (2 * Module.finrank ℝ E) :=
          pow_le_pow_left₀ hratio_nonneg hratio_le _
        nlinarith
      _ = 2 * (25 : ℝ) ^ (2 * Module.finrank ℝ E)
            * ((ρ' : ℝ) / (ρ : ℝ)) ^ (2 * Module.finrank ℝ E) := by
        rw [mul_pow]
        ring
  rcases exists_net_of_le_common_tube F T W hFW hεpos hB_ineq with ⟨F', hF'sub_F, hnet, hcard⟩
  have hF'sub_s : F' ⊆ s := Finset.Subset.trans hF'sub_F hF_sub_s
  refine ⟨F', hF'sub_s, hcard, ?_⟩
  · intro i hi
    have hi_F : i ∈ F := hi
    rcases hnet i hi_F with ⟨a, haF', hdist⟩
    have hi_s : i ∈ s := hF_sub_s hi_F
    have ha_s : a ∈ s := hF'sub_s haF'
    have hi_in_fibre_a : i ∈ fibreIndex s T σ ρ a := by
      rw [fibreIndex, Kakeya.familyIn]
      apply Finset.mem_filter.mpr
      refine ⟨hi_s, ?_⟩
      have h_endpoint_dist : ‖(T i).x - (T a).x‖ + ‖(T i).y - (T a).y‖ + (σ : ℝ) ≤ (ρ : ℝ) := by
        have h_2σ_le_ρ : (2 : ℝ) * (σ : ℝ) ≤ (ρ : ℝ) := by exact_mod_cast hσρ
        linarith
      have h_body_ineq :
          ((T i).rescale σ).toConvexSpaceBody ≤ ((T a).rescale ρ).toConvexSpaceBody :=
        Tube.rescale_le_rescale_of_endpoint_dist (T i) (T a) h_endpoint_dist
      simpa [fibreBodies]
    exact ⟨a, haF', hi_in_fibre_a⟩


end MultiScaleFac
end Kakeya

end

/-! ### Comparable fibre counts

`ComparableFibreCounts` is the branching hypothesis: the fibres of a family over its node
index all have comparable cardinality.  Monotonicity of `fibreIndex` in the anchor is what
makes the comparison stable under coarsening. -/

@[expose] public section

open MeasureTheory Real Metric
open Tube

namespace Kakeya

open StickyKakeya

namespace MultiScaleFac

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

variable {ι : Type*} {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E} {ρ Cu : NNReal}

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **Anchor monotonicity.**  Enlarging the anchor scale can only enlarge the fibre. -/
theorem fibreIndex_subset_of_anchor_le {σ ρ' : NNReal} (hρ : ρ ≤ ρ') (i₀ : ι) :
    fibreIndex s T σ ρ i₀ ⊆ fibreIndex s T σ ρ' i₀ := by
  classical
  have hrescale : ((T i₀).rescale ρ).toConvexSpaceBody
      ≤ ((T i₀).rescale ρ').toConvexSpaceBody :=
    Tube.rescale_le_rescale_of_radius_le (T i₀) hρ
  intro i hi
  simp only [fibreIndex, Kakeya.familyIn, Finset.mem_filter] at hi ⊢
  exact ⟨hi.1, hi.2.trans hrescale⟩


/-- **GWZ Definition 2.1(iii), read in the thickening convention of GWZ §7.**

The `δ`-fibres of the `ρ`-thickenings, `ρ ∈ scales`, are comparable to each other up to the factor
`C`.  This is what makes the fibres at the exact scale `ρ` as full as the parents of a uniform
structure at that scale. -/
def ComparableFibreCounts {ι : Type*} {δ : NNReal} (s : Finset ι) (T : ι → Tube δ E)
    (scales : Set NNReal) (C : NNReal) : Prop :=
  ∀ ρ ∈ scales, ∀ i₀ ∈ s, ∀ i₁ ∈ s,
    ((fibreIndex s T δ ρ i₀).card : NNReal) ≤ C * ((fibreIndex s T δ ρ i₁).card : NNReal)


omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- Comparability of the fibre counts is monotone in its constant. -/
theorem ComparableFibreCounts.mono {ι : Type*} {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E}
    {scales : Set NNReal} {C C' : NNReal} (h : ComparableFibreCounts s T scales C) (hC : C ≤ C') :
    ComparableFibreCounts s T scales C' :=
  fun ρ hρ i₀ hi₀ i₁ hi₁ => (h ρ hρ i₀ hi₀ i₁ hi₁).trans (mul_le_mul_left hC _)


end MultiScaleFac
end Kakeya

end

/-! ### Grid-uniform families

`GridUniform` is the grid-indexed reading of uniformity used by the estimates that do not run
the dividing-scales dichotomy, together with its conversion to a `UniformTubeSet`. -/

@[expose] public section

open MeasureTheory Real Metric

universe u
open Tube

namespace Kakeya

open StickyKakeya

namespace MultiScaleFac


variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

variable {ι : Type*}

/-- **Comparable thickening counts, `4`-inflated form** (blueprint
`def:comparableFibreCounts_inflated`).  The strengthening of
`Kakeya.MultiScaleFac.ComparableFibreCounts` in which the anchor of the larger side is inflated by
`4`; it implies the uninflated form with the same constant. -/
def ComparableFibreCountsInflated {ι : Type*} {δ : NNReal} (s : Finset ι) (T : ι → Tube δ E)
    (scales : Set NNReal) (C : NNReal) : Prop :=
  ∀ ρ ∈ scales, ∀ i₀ ∈ s, ∀ i₁ ∈ s,
    ((fibreIndex s T δ (4 * ρ) i₀).card : NNReal) ≤ C * ((fibreIndex s T δ ρ i₁).card : NNReal)


omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- The inflated comparability is monotone in its constant. -/
theorem ComparableFibreCountsInflated.mono {ι : Type*} {δ : NNReal} {s : Finset ι}
    {T : ι → Tube δ E} {scales : Set NNReal} {C C' : NNReal}
    (h : ComparableFibreCountsInflated s T scales C) (hC : C ≤ C') :
    ComparableFibreCountsInflated s T scales C' :=
  fun ρ hρ i₀ hi₀ i₁ hi₁ => (h ρ hρ i₀ hi₀ i₁ hi₁).trans (mul_le_mul_left hC _)


/-- **A grid-uniform system** (blueprint `def:gridUniform`).

A nested system of covers along the grid, together with a uniform structure at every grid scale
`k ≤ N` whose parent family *is* the node set of that system.  The structures are carried as data,
not merely asserted to exist, so a family and a subfamily can be compared node by node. -/
structure GridUniformCore {δ : NNReal} (t : Finset ι) (T : ι → Tube δ E) (N : ℕ)
    (C : NNReal) where
  /-- The underlying nested system of covers along the grid. -/
  cover : GridCoverSystem t T N
  /-- The uniform structure at the grid scale `ρ_k`, supplied only on the grid range `k ≤ N` (the
  scales below `δ` carry no uniform structure for a nonempty family). -/
  uniformAt : ∀ k ≤ N, Tube.IsUniformAtScale t T (gridScale δ N k) C
  /-- The parents of the uniform structure are exactly the nodes of the cover system. -/
  parent_eq : ∀ k (hk : k ≤ N), (uniformAt k hk).parent = cover.indexSet k
  /-- …and they carry the same tubes.  Without this the two halves of the bundle would speak about
  different geometric objects: the branching bracket of `uniformAt` would constrain
  `(uniformAt k hk).parentTube j` while the every-scale conditions are stated against
  `cover.tube k j`. -/
  tube_eq : ∀ k (hk : k ≤ N), ∀ P ∈ cover.indexSet k,
    (uniformAt k hk).parentTube P = cover.tube k P
  /-- **The branching lower bound on the class**, not merely on the set of members contained in
  the node: the branching number of every grid scale is at most the cardinality of the class of
  each of its nodes. -/
  le_card_class : ∀ k (hk : k ≤ N), ∀ P ∈ cover.indexSet k,
    (uniformAt k hk).branchingN ≤ ((coverClass t (cover.assign k) P).card : NNReal)

/-- **`GridUniform` is `GridUniformCore` plus the two fields that are not consequences of
uniformity.**  : the Katz-Tao alternatives of `MultiScaleFac/GapsKT.lean` do
not project `clumped` or `nice` — neither of the five files that do is in `Ports.lean`'s import
closure — so they are restated over `GridUniformCore`, which a bare `Tube.UniformTubeSet` can
supply.  Splitting rather than weakening keeps **every existing consumer untouched**: `extends`
makes the core fields available under their old names, so `𝒢.uniformAt`, `𝒢.cover`,
`𝒢.parent_eq`, `𝒢.tube_eq` and `𝒢.le_card_class` continue to elaborate verbatim. -/
structure GridUniform {δ : NNReal} (t : Finset ι) (T : ι → Tube δ E) (N : ℕ) (C : NNReal)
    extends GridUniformCore t T N C where
  /-- **Clumping**: at every grid scale above the bottom one, the class of a node lies inside a
  single tube of a *quarter* of that radius.  Carried as a field because it is not a consequence
  of uniformity.  The bottom scale `k = N` is excluded: there `ρ_N = δ` and there is nothing to
  clump into, the substitute being essential distinctness. -/
  clumped : ∀ k, k < N → ∀ P ∈ cover.indexSet k, ∃ i₂ : ι,
    coverClass t (cover.assign k) P ⊆ fibreIndex t T δ (gridScale δ N k / 4) i₂
  /-- The nodes of the cover form a *tight* net at every grid scale: the node tubes are distinct,
  and only boundedly many of them meet a common tube of the same radius, with the tight constant
  `Tube.overlapConstBOTight`. -/
  nice : ∀ k ≤ N,
    Set.InjOn (cover.tube k) (cover.indexSet k : Set ι) ∧
    ∀ V : Tube (gridScale δ N k) E,
      ((cover.indexSet k).filter (fun v => ∃ i ∈ t,
        (T i).toConvexSpaceBody ≤ (cover.tube k v).toConvexSpaceBody ∧
        (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody)).card ≤
          Tube.overlapConstBOTight (Module.finrank ℝ E)


omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- A grid-uniform system is monotone in its constant, keeping the same cover system and the same
parents at every grid scale. -/
noncomputable def GridUniform.mono {δ : NNReal} {t : Finset ι} {T : ι → Tube δ E} {N : ℕ}
    {C C' : NNReal}
    (𝒢 : GridUniform t T N C) (hC : C ≤ C') : GridUniform t T N C' where
  cover := 𝒢.cover
  uniformAt k hk := (𝒢.uniformAt k hk).mono hC hC
  parent_eq k hk := by simpa using 𝒢.parent_eq k hk
  tube_eq k hk P hP := by simpa using 𝒢.tube_eq k hk P hP
  le_card_class k hk P hP := by simpa using 𝒢.le_card_class k hk P hP
  clumped := 𝒢.clumped
  nice := 𝒢.nice


/-- The constant of `Kakeya.MultiScaleFac.GridUniform.toUniformTubeSet`: the ambient uniformity
constant, bumped so that it also dominates the tight net multiplicity carried by the `nice`
field. -/
noncomputable def uniformTubeSetCuOf (C : NNReal) : NNReal :=
  max C ((Tube.overlapConstBOTight (Module.finrank ℝ E) : ℕ) : NNReal)


/-- **A grid-uniform system is a uniform set of tubes** (blueprint
`lem:uniformTubeSet_of_gridUniform`).  Bounded overlap comes from the tight-net field `nice`, the
class upper bound from `Tube.IsUniformAtScale.card_filter_le`, and the class lower bound from the
field `le_card_class`. -/
noncomputable def GridUniform.toUniformTubeSet {δ : NNReal} {t : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} {C : NNReal} (𝒢 : GridUniform t T N C) :
    UniformTubeSet t T N (uniformTubeSetCuOf (E := E) C) where
  cover := 𝒢.cover
  branchingN k := if hk : k ≤ N then (𝒢.uniformAt k hk).branchingN else 1
  tube_injOn k hk := (𝒢.nice k hk).1
  boundedOverlap k hk V := by
    have h := (𝒢.nice k hk).2 V
    have h' : (((𝒢.cover.indexSet k).filter (fun v => ∃ i ∈ t,
        (T i).toConvexSpaceBody ≤ (𝒢.cover.tube k v).toConvexSpaceBody ∧
        (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody)).card : NNReal)
          ≤ ((Tube.overlapConstBOTight (Module.finrank ℝ E) : ℕ) : NNReal) := by
      exact_mod_cast h
    exact h'.trans (le_max_right _ _)
  card_class_le k hk P hP := by
    classical
    have hsub : coverClass t (𝒢.cover.assign k) P ⊆
        {i ∈ t |
          (T i).toConvexSpaceBody ≤ ((𝒢.uniformAt k hk).parentTube P).toConvexSpaceBody} := by
      intro i hi
      simp only [coverClass, Finset.mem_filter] at hi
      rw [Finset.mem_filter]
      refine ⟨hi.1, ?_⟩
      have hle := 𝒢.cover.le_tube_assign k hk i hi.1
      rw [hi.2] at hle
      rw [𝒢.tube_eq k hk P hP]
      exact hle
    have hPu : P ∈ (𝒢.uniformAt k hk).parent := by rw [𝒢.parent_eq k hk]; exact hP
    have hcard := (𝒢.uniformAt k hk).card_filter_le hPu
    have hmain :
        ((coverClass t (𝒢.cover.assign k) P).card : NNReal) ≤ C * (𝒢.uniformAt k hk).branchingN :=
      le_trans (by exact_mod_cast Finset.card_le_card hsub) hcard
    rw [dif_pos hk]
    exact hmain.trans (mul_le_mul_left (le_max_left _ _) _)
  le_card_class k hk P hP := by
    have hone : (1 : ℕ) ≤ Tube.overlapConstBOTight (Module.finrank ℝ E) :=
      Nat.one_le_iff_ne_zero.mpr (by simp [Tube.overlapConstBOTight])
    have hone' :
        (1 : NNReal) ≤ ((Tube.overlapConstBOTight (Module.finrank ℝ E) : ℕ) : NNReal) := by
      exact_mod_cast hone
    have h1 : (1 : NNReal) ≤ uniformTubeSetCuOf (E := E) C :=
      hone'.trans (le_max_right _ _)
    rw [dif_pos hk]
    exact (𝒢.le_card_class k hk P hP).trans
      (le_mul_of_one_le_left (by positivity) h1)


end MultiScaleFac
end Kakeya

end

/-! ### From fibres to node classes

The bridge between the leaf-anchored reading of a hypothesis (on fibres) and its node reading
(on the classes of a cover): the two index sets are compared by `coverClass_subset_fibreIndex`
and its converse count, and the Frostman condition is transported along that comparison. -/

@[expose] public section

open MeasureTheory Real Metric

universe u
open Tube

namespace Kakeya

open StickyKakeya

namespace MultiScaleFac

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E]
  {ι : Type*}

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **Bridge 2, the easy inclusion.**  The class of a node is contained in the `4ρ_k`-fibre of any
of its members: a leaf `i` of the class lies in the node, and the node lies in the `4ρ_k`-thickening
of the member `i₀` by `Tube.rescale_le_of_le`; containment is then transitive.

The factor `4` here is the one the grid is `16`-separated to absorb. -/
theorem coverClass_subset_fibreIndex {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ}
    {C : NNReal} (𝒰 : UniformTubeSet s T N C) {k : ℕ} (hk : k ≤ N) {i₀ : ι} (hi₀ : i₀ ∈ s) :
    coverClass s (𝒰.cover.assign k) (𝒰.cover.assign k i₀)
      ⊆ Kakeya.StickyKakeya.fibreIndex s T δ (4 * gridScale δ N k) i₀ := by
  classical
  intro i hi
  rw [Kakeya.StickyKakeya.fibreIndex_self]
  rw [coverClass, Finset.mem_filter] at hi
  rcases hi with ⟨hi, hassign⟩
  refine Finset.mem_filter.mpr ⟨hi, ?_⟩
  have h1 : (T i).toConvexSpaceBody ≤
      (𝒰.cover.tube k (𝒰.cover.assign k i)).toConvexSpaceBody :=
    𝒰.cover.le_tube_assign k hk i hi
  have h1' : (T i).toConvexSpaceBody ≤
      (𝒰.cover.tube k (𝒰.cover.assign k i₀)).toConvexSpaceBody := hassign ▸ h1
  have h2 : (𝒰.cover.tube k (𝒰.cover.assign k i₀)).toConvexSpaceBody ≤
      ((T i₀).rescale (4 * gridScale δ N k)).toConvexSpaceBody :=
    Tube.rescale_le_of_le (T i₀) (𝒰.cover.tube k (𝒰.cover.assign k i₀))
      (𝒰.cover.le_tube_assign k hk i₀ hi₀)
  exact le_trans h1' h2


omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **Bridge 2, the counting converse.**  The `ρ_k`-fibre of a leaf `i₀` is covered by the classes
of the boundedly many nodes that meet the anchor `T_{i₀}^{(ρ_k)}` through `s`, so its cardinality
is at most `C` times the largest class, hence at most `C ^ 2` times the branching number. -/
theorem card_fibreIndex_le_of_uniformTubeSet {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ}
    {C : NNReal} (𝒰 : UniformTubeSet s T N C) {k : ℕ} (hk : k ≤ N) {i₀ : ι} (_hi₀ : i₀ ∈ s) :
    ((Kakeya.StickyKakeya.fibreIndex s T δ (gridScale δ N k) i₀).card : NNReal)
      ≤ C ^ 2 * 𝒰.branchingN k := by
  classical
  let V : Tube (gridScale δ N k) E := (T i₀).rescale (gridScale δ N k)
  let F : Finset ι := s.filter (fun i => (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody)
  let A := F.image (𝒰.cover.assign k)
  have hF : ((Kakeya.StickyKakeya.fibreIndex s T δ (gridScale δ N k) i₀).card : NNReal) =
      (F.card : NNReal) := by
    simp [F, V, Kakeya.StickyKakeya.fibreIndex_self]
  have hF_sub : F ⊆ s := by
    intro i hi
    exact (Finset.mem_filter.mp hi).1
  have hA_mem_parent : ∀ v ∈ A, v ∈ 𝒰.cover.indexSet k := by
    intro v hv
    obtain ⟨i, hiF, rfl⟩ := Finset.mem_image.mp hv
    exact 𝒰.cover.assign_mem k hk i (hF_sub hiF)
  have hF_le :
      (F.card : NNReal) ≤ ∑ v ∈ A, ((coverClass s (𝒰.cover.assign k) v).card : NNReal) := by
    have hsubF : F ⊆ A.biUnion (fun v => coverClass s (𝒰.cover.assign k) v) := by
      intro i hiF
      refine Finset.mem_biUnion.mpr ?_
      refine ⟨𝒰.cover.assign k i, ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨i, hiF, rfl⟩
      · rw [coverClass, Finset.mem_filter]
        exact ⟨hF_sub hiF, rfl⟩
    have hnat₁ : F.card ≤ (A.biUnion (fun v => coverClass s (𝒰.cover.assign k) v)).card :=
      Finset.card_le_card hsubF
    have hnat₂ :
        (A.biUnion (fun v => coverClass s (𝒰.cover.assign k) v)).card ≤
          ∑ v ∈ A, (coverClass s (𝒰.cover.assign k) v).card :=
      Finset.card_biUnion_le
    exact_mod_cast le_trans hnat₁ hnat₂
  have hsum_le :
      (∑ v ∈ A, ((coverClass s (𝒰.cover.assign k) v).card : NNReal)) ≤
        A.card * (C * 𝒰.branchingN k) := by
    calc
      (∑ v ∈ A, ((coverClass s (𝒰.cover.assign k) v).card : NNReal))
          ≤ ∑ v ∈ A, (C * 𝒰.branchingN k) :=
            Finset.sum_le_sum (fun v hv => 𝒰.card_class_le k hk v (hA_mem_parent v hv))
      _ = A.card * (C * 𝒰.branchingN k) := by
        rw [Finset.sum_const]
        simp
  have hA_bd : (A.card : NNReal) ≤ C := by
    have hsub : A ⊆ (𝒰.cover.indexSet k).filter (fun j => ∃ i ∈ s,
        (T i).toConvexSpaceBody ≤ (𝒰.cover.tube k j).toConvexSpaceBody ∧
        (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody) := by
      intro v hv
      obtain ⟨i, hiF, rfl⟩ := Finset.mem_image.mp hv
      exact Finset.mem_filter.mpr
        ⟨hA_mem_parent (𝒰.cover.assign k i) (Finset.mem_image.mpr ⟨i, hiF, rfl⟩),
          i, hF_sub hiF, 𝒰.cover.le_tube_assign k hk i (hF_sub hiF),
          (Finset.mem_filter.mp hiF).2⟩
    have hnat : A.card ≤
        ((𝒰.cover.indexSet k).filter (fun j => ∃ i ∈ s,
          (T i).toConvexSpaceBody ≤ (𝒰.cover.tube k j).toConvexSpaceBody ∧
          (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody)).card :=
      Finset.card_le_card hsub
    exact le_trans (by exact_mod_cast hnat) (𝒰.boundedOverlap k hk V)
  calc
    ((Kakeya.StickyKakeya.fibreIndex s T δ (gridScale δ N k) i₀).card : NNReal)
        = (F.card : NNReal) := hF
    _ ≤ ∑ v ∈ A, ((coverClass s (𝒰.cover.assign k) v).card : NNReal) := hF_le
    _ ≤ A.card * (C * 𝒰.branchingN k) := hsum_le
    _ ≤ C * (C * 𝒰.branchingN k) := mul_le_mul_of_nonneg_right hA_bd (by positivity)
    _ = C ^ 2 * 𝒰.branchingN k := by ring


omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- Every node of the hierarchy has a nonempty class as soon as the family is nonempty.

Both halves of the branching bracket are used: an empty class forces `branchingN k = 0` by
`le_card_class`, and then `card_class_le` makes *every* class empty, so no leaf could be assigned
anywhere. -/
theorem coverClass_nonempty_of_mem_parent {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ}
    {C : NNReal} (𝒰 : UniformTubeSet s T N C) {k : ℕ} (hk : k ≤ N) (hs : s.Nonempty)
    {j : ι} (hj : j ∈ 𝒰.cover.indexSet k) :
    (coverClass s (𝒰.cover.assign k) j).Nonempty := by
  classical
  by_contra hne
  have hempty : coverClass s (𝒰.cover.assign k) j = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hne
  have hle := 𝒰.le_card_class k hk j hj
  have hcard0 : (coverClass s (𝒰.cover.assign k) j).card = 0 := by
    rw [hempty]
    simp
  have hb_le : 𝒰.branchingN k ≤ 0 := by
    simpa [hcard0] using hle
  have hb0 : 𝒰.branchingN k = 0 :=
    le_antisymm hb_le (by positivity)
  obtain ⟨i, hi⟩ := hs
  let j' : ι := 𝒰.cover.assign k i
  have hj' : j' ∈ 𝒰.cover.indexSet k := by
    exact 𝒰.cover.assign_mem k hk i hi
  have hcle := 𝒰.card_class_le k hk j' hj'
  have hcard0' : (coverClass s (𝒰.cover.assign k) j').card = 0 := by
    have h0le : (coverClass s (𝒰.cover.assign k) j').card ≤ 0 := by
      simpa [hb0] using hcle
    exact le_antisymm h0le (Nat.zero_le _)
  have hmem : i ∈ coverClass s (𝒰.cover.assign k) j' := by
    simp only [coverClass, Finset.mem_filter]
    exact ⟨hi, rfl⟩
  have hemp' : coverClass s (𝒰.cover.assign k) j' = ∅ :=
    Finset.card_eq_zero.mp hcard0'
  simp [hemp'] at hmem


omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- An exact-scale fibre is no larger than a class, up to `C ^ 3`: `C ^ 2` for the bounded-overlap
count of `card_fibreIndex_le_of_uniformTubeSet` and one more `C` for the class lower bound. -/
theorem card_fibreIndex_le_card_coverClass {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ}
    {C : NNReal} (𝒰 : UniformTubeSet s T N C) {k : ℕ} (hk : k ≤ N) {a : ι} (ha : a ∈ s)
    {j : ι} (hj : j ∈ 𝒰.cover.indexSet k) :
    ((fibreIndex s T δ (gridScale δ N k) a).card : NNReal)
      ≤ C ^ 3 * ((coverClass s (𝒰.cover.assign k) j).card : NNReal) := by
  have h1 := card_fibreIndex_le_of_uniformTubeSet 𝒰 hk ha
  have h2 := 𝒰.le_card_class k hk j hj
  calc ((fibreIndex s T δ (gridScale δ N k) a).card : NNReal)
      ≤ C ^ 2 * 𝒰.branchingN k := h1
    _ ≤ C ^ 2 * (C * ((coverClass s (𝒰.cover.assign k) j).card : NNReal)) :=
        mul_le_mul_right h2 _
    _ = C ^ 3 * ((coverClass s (𝒰.cover.assign k) j).card : NNReal) := by ring


/-- **The class count against the node density.**  The class of a node lies inside the node, so its
count weighted by the minimal member volume is at most the node density weighted by the maximal
volume of a `ρ_k`-tube. -/
theorem card_coverClass_mul_le_densityIn_node {δ : NNReal} {s : Finset ι}
    {T : ι → Tube δ E} {N : ℕ} {C : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (𝒰 : UniformTubeSet s T N C) {k : ℕ}
    (hk : k ≤ N) {j : ι} (_hj : j ∈ 𝒰.cover.indexSet k) :
    ((coverClass s (𝒰.cover.assign k) j).card : ENNReal)
        * (((Tube.le_volume.c (Module.finrank ℝ E) : NNReal) : ENNReal)
            * ((δ : ENNReal) ^ (Module.finrank ℝ E - 1)))
      ≤ Kakeya.densityIn (coverClass s (𝒰.cover.assign k) j)
            (fun i => (T i).toConvexSpaceBody) (𝒰.cover.tube k j).toConvexSpaceBody
          * (((Tube.volume_le.C (Module.finrank ℝ E) : NNReal) : ENNReal)
              * ((gridScale δ N k : ENNReal) ^ (Module.finrank ℝ E - 1))) := by
  classical
  set n : ℕ := Module.finrank ℝ E
  set p : ℕ := n - 1
  set c : NNReal := Tube.le_volume.c n
  set Cn : NNReal := Tube.volume_le.C n
  set ρ : NNReal := gridScale δ N k
  set cls : Finset ι := coverClass s (𝒰.cover.assign k) j
  set W : ι → ConvexSpaceBody E := fun i => (T i).toConvexSpaceBody
  set Kj : ConvexSpaceBody E := (𝒰.cover.tube k j).toConvexSpaceBody
  have hρpos : 0 < ρ := gridScale_pos hδ N k
  have hρ1 : ρ ≤ 1 := gridScale_le_one hδ1 N k
  have hmem : ∀ i ∈ cls, W i ≤ Kj := by
    intro i hicls
    have hf : i ∈ s ∧ 𝒰.cover.assign k i = j := by
      simpa [cls, coverClass] using hicls
    have hle := 𝒰.cover.le_tube_assign k hk i hf.1
    rw [hf.2] at hle
    simpa [W, Kj] using hle
  have hvmin : ∀ i ∈ cls, (↑c * (δ : ENNReal) ^ p) ≤ volume (W i).carrier := by
    intro i hicls
    simpa [c, p, n, W, ENNReal.coe_mul, ENNReal.coe_pow] using Tube.le_volume (T i)
  have hge := densityIn_ge_of_count_volume (s := cls) (W := W) (K := Kj)
    (Finset.Subset.refl cls) hmem hvmin
  have hvol_lb : ((Tube.le_volume.c n * ρ ^ p : NNReal) : ENNReal) ≤ volume Kj.carrier := by
    simpa [Kj, ρ, p, n] using Tube.le_volume (𝒰.cover.tube k j)
  have hvol_ne_zero : volume Kj.carrier ≠ 0 := by
    have hpos : 0 < (Tube.le_volume.c n * ρ ^ p : NNReal) := by
      exact mul_pos (Tube.le_volume.c_pos n) (pow_pos hρpos p)
    exact ne_of_gt (lt_of_lt_of_le (ENNReal.coe_pos.mpr hpos) hvol_lb)
  have hvol_ne_top : volume Kj.carrier ≠ ⊤ := Kj.isCompact.measure_ne_top
  have hcount : (cls.card : ENNReal) * (↑c * (δ : ENNReal) ^ p) ≤
      densityIn cls W Kj * volume Kj.carrier := by
    rw [ENNReal.div_le_iff hvol_ne_zero hvol_ne_top] at hge
    exact hge
  have hvol_le : volume Kj.carrier ≤ ↑Cn * (ρ : ENNReal) ^ p := by
    simpa [Kj, Cn, ρ, p, n, ENNReal.coe_mul, ENNReal.coe_pow] using
      Tube.volume_le hρ1 (𝒰.cover.tube k j)
  calc
    (cls.card : ENNReal) * (↑c * (δ : ENNReal) ^ p)
        ≤ densityIn cls W Kj * volume Kj.carrier := hcount
    _ ≤ densityIn cls W Kj * (↑Cn * (ρ : ENNReal) ^ p) :=
        mul_le_mul_right hvol_le (densityIn cls W Kj)


/-- **A fibre density against the node density.**  Combining
`densityIn_fibre_mul_le_card`, `card_fibreIndex_le_card_coverClass` and
`card_coverClass_mul_le_densityIn_node`, and cancelling the two volume weights, whose ratio is
`(C_n / c_n) ^ 2`. -/
theorem densityIn_fibre_le_mul_densityIn_node {δ : NNReal} {s : Finset ι}
    {T : ι → Tube δ E} {N : ℕ} {C : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (𝒰 : UniformTubeSet s T N C) {k : ℕ} (hk : k ≤ N) {a : ι} (ha : a ∈ s)
    {j : ι} (hj : j ∈ 𝒰.cover.indexSet k) :
    Kakeya.densityIn (fibreIndex s T δ (gridScale δ N k) a)
        (fun i => (T i).toConvexSpaceBody)
        ((T a).rescale (gridScale δ N k)).toConvexSpaceBody
      ≤ (((Tube.volume_le.C (Module.finrank ℝ E)
              / Tube.le_volume.c (Module.finrank ℝ E) : NNReal) : ENNReal)) ^ 2
          * (C : ENNReal) ^ 3
          * Kakeya.densityIn (coverClass s (𝒰.cover.assign k) j)
              (fun i => (T i).toConvexSpaceBody) (𝒰.cover.tube k j).toConvexSpaceBody := by
  classical
  set n := Module.finrank ℝ E with hn
  set p := n - 1 with hp
  set ρ : NNReal := gridScale δ N k with hρ_def
  set c : NNReal := Tube.le_volume.c n with hc_def
  set Cn : NNReal := Tube.volume_le.C n with hCn_def
  set r : NNReal := Cn / c with hr_def
  set W : ι → ConvexSpaceBody E := fun i => (T i).toConvexSpaceBody with hW_def
  set cls : Finset ι := coverClass s (𝒰.cover.assign k) j with hcls_def
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
  have h_ka : ((fibreIndex s T δ ρ a).card : ENNReal) ≤
      (C : ENNReal) ^ 3 * (cls.card : ENNReal) := by
    have hnn' : ((fibreIndex s T δ ρ a).card : NNReal) ≤
        C ^ 3 * (cls.card : NNReal) := by
      simpa [hρ_def, hcls_def] using card_fibreIndex_le_card_coverClass 𝒰 hk ha hj
    exact_mod_cast hnn'
  have hband_g : Da * X ≤ (C : ENNReal) ^ 3 * (cls.card : ENNReal) * Cδn := by
    calc
      Da * X ≤ ((fibreIndex s T δ ρ a).card : ENNReal) * Cδn := hband_f
      _ ≤ ((C : ENNReal) ^ 3 * (cls.card : ENNReal)) * Cδn :=
          mul_le_mul_left h_ka Cδn
      _ = (C : ENNReal) ^ 3 * (cls.card : ENNReal) * Cδn := by
          ring
  have hband_h : (cls.card : ENNReal) * Y ≤ D * Cρn := by
    have hb := card_coverClass_mul_le_densityIn_node hδ hδ1 𝒰 hk hj
    simpa [W, Y, Cρn, hc_def, hCn_def, hρ_def, hD_def, hcls_def] using hb
  have hchain : Da * (X * Y) ≤ (C : ENNReal) ^ 3 * D * (Cρn * Cδn) := by
    calc
      Da * (X * Y) = (Da * X) * Y := by ring
      _ ≤ ((C : ENNReal) ^ 3 * (cls.card : ENNReal) * Cδn) * Y :=
          mul_le_mul_left hband_g Y
      _ = (C : ENNReal) ^ 3 * (cls.card : ENNReal) * (Cδn * Y) := by
          ring
      _ = (C : ENNReal) ^ 3 * ((cls.card : ENNReal) * Y) * Cδn := by
          ring
      _ ≤ (C : ENNReal) ^ 3 * (D * Cρn) * Cδn := by
          exact mul_le_mul_left (mul_le_mul_right hband_h ((C : ENNReal) ^ 3)) Cδn
      _ = (C : ENNReal) ^ 3 * D * (Cρn * Cδn) := by ring
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
  have hstep : Da * (X * Y) ≤ ((r : ENNReal) ^ 2 * (C : ENNReal) ^ 3 * D) * (X * Y) := by
    calc
      Da * (X * Y) ≤ (C : ENNReal) ^ 3 * D * (Cρn * Cδn) := hchain
      _ = (C : ENNReal) ^ 3 * D * ((r : ENNReal) ^ 2 * (X * Y)) := by rw [hcast]
      _ = (r : ENNReal) ^ 2 * (C : ENNReal) ^ 3 * D * (X * Y) := by ring
  have hcancel : Da ≤ (r : ENNReal) ^ 2 * (C : ENNReal) ^ 3 * D := by
    exact (ENNReal.mul_le_mul_iff_right hXY0 hXY_top).mp
      (by simpa [mul_assoc, mul_left_comm, mul_comm] using hstep)
  simpa [W, Da, D, hn, hp, hr_def, hρ_def] using hcancel


/-- The dimensional constant of `isFrostmanIn_coverClass_of_fibre`: the size of the covering of an
inflated fibre by exact-scale fibres, times the square of the tube-volume comparison ratio. -/
noncomputable def nodeClassConst : NNReal :=
  2 * (25 : NNReal) ^ (2 * Module.finrank ℝ E) * (4 : NNReal) ^ (2 * Module.finrank ℝ E)
    * (Tube.volume_le.C (Module.finrank ℝ E) / Tube.le_volume.c (Module.finrank ℝ E)) ^ 2


/-- **The workhorse of the translation.**  If every leaf-anchored fibre at the grid scale `ρ_k` is
`B`-Frostman in its anchor, then every class of a node at grid index `k` is Frostman in that node,
with the constant multiplied by `nodeClassConst * C ^ 3`. -/
theorem isFrostmanIn_coverClass_of_fibre {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ}
    {C : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (𝒰 : UniformTubeSet s T N C) {k : ℕ} (hk : k ≤ N)
    (h2δ : 2 * δ ≤ gridScale δ N k) {j : ι} (hj : j ∈ 𝒰.cover.indexSet k)
    (hs : s.Nonempty) {B : ENNReal}
    (hB : ∀ a ∈ s, ConvexSpaceBody.IsFrostmanIn (fibreIndex s T δ (gridScale δ N k) a)
      (fun i => (T i).toConvexSpaceBody)
      ((T a).rescale (gridScale δ N k)).toConvexSpaceBody B) :
    ConvexSpaceBody.IsFrostmanIn (coverClass s (𝒰.cover.assign k) j)
      (fun i => (T i).toConvexSpaceBody) (𝒰.cover.tube k j).toConvexSpaceBody
      ((nodeClassConst (E := E) : ENNReal) * (C : ENNReal) ^ 3 * B) := by
  classical
  set n := Module.finrank ℝ E with hn
  set r : NNReal := Tube.volume_le.C n / Tube.le_volume.c n with hr
  set D : ENNReal := Kakeya.densityIn (coverClass s (𝒰.cover.assign k) j)
    (fun i => (T i).toConvexSpaceBody) (𝒰.cover.tube k j).toConvexSpaceBody with hD
  intro K' _
  refine le_trans (Kakeya.le_maxDensity _ _ K') ?_
  obtain ⟨i₀, hi₀cls⟩ := coverClass_nonempty_of_mem_parent 𝒰 hk hs hj
  have hi₀s : i₀ ∈ s := by
    simp only [coverClass, Finset.mem_filter] at hi₀cls
    exact hi₀cls.1
  have hassign : 𝒰.cover.assign k i₀ = j := by
    simp only [coverClass, Finset.mem_filter] at hi₀cls
    exact hi₀cls.2
  have hclsSub : coverClass s (𝒰.cover.assign k) j
      ⊆ fibreIndex s T δ (4 * gridScale δ N k) i₀ := by
    have h := coverClass_subset_fibreIndex 𝒰 hk hi₀s
    rwa [hassign] at h
  have hρpos : 0 < gridScale δ N k := gridScale_pos hδ N k
  obtain ⟨A, hAs, hAcard, hAcov⟩ :=
    exists_gapFibre_cover_of_ratio (s := s) (T := T) (δ := δ) (σ := δ)
      (ρ := gridScale δ N k) (ρ' := 4 * gridScale δ N k) hρpos le_rfl h2δ
      (by
        have h0 : (0 : NNReal) ≤ gridScale δ N k := le_of_lt hρpos
        exact le_mul_of_one_le_left h0 (by norm_num : (1 : NNReal) ≤ 4)) i₀
  have hsubBi : coverClass s (𝒰.cover.assign k) j
      ⊆ A.biUnion (fun a => fibreIndex s T δ (gridScale δ N k) a) := by
    intro i hi
    obtain ⟨i₂, hi₂A, hi₂⟩ := hAcov i (hclsSub hi)
    exact Finset.mem_biUnion.mpr ⟨i₂, hi₂A, hi₂⟩
  have hmax := maxDensity_le_sum_of_subset_biUnion
    (W := fun i => (T i).toConvexSpaceBody) hsubBi
  have hterm : ∀ a ∈ A,
      Kakeya.maxDensity (fibreIndex s T δ (gridScale δ N k) a)
          (fun i => (T i).toConvexSpaceBody)
        ≤ B * ((r : ENNReal) ^ 2 * (C : ENNReal) ^ 3 * D) := by
    intro a haA
    have has : a ∈ s := hAs haA
    have hmem : ∀ i ∈ fibreIndex s T δ (gridScale δ N k) a,
        (fun i => (T i).toConvexSpaceBody) i
          ≤ ((T a).rescale (gridScale δ N k)).toConvexSpaceBody := by
      intro i hi
      rw [fibreIndex_self] at hi
      exact (Finset.mem_filter.mp hi).2
    have h1 := ConvexSpaceBody.IsFrostmanIn.maxDensity_le_of_carrier_subset (hB a has) hmem
    have h2 := densityIn_fibre_le_mul_densityIn_node hδ hδ1 𝒰 hk has hj
    exact h1.trans (mul_le_mul_right h2 B)
  have hsum : (∑ a ∈ A, Kakeya.maxDensity (fibreIndex s T δ (gridScale δ N k) a)
        (fun i => (T i).toConvexSpaceBody))
      ≤ (A.card : ENNReal) * (B * ((r : ENNReal) ^ 2 * (C : ENNReal) ^ 3 * D)) := by
    calc (∑ a ∈ A, Kakeya.maxDensity (fibreIndex s T δ (gridScale δ N k) a)
            (fun i => (T i).toConvexSpaceBody))
        ≤ ∑ _a ∈ A, B * ((r : ENNReal) ^ 2 * (C : ENNReal) ^ 3 * D) :=
          Finset.sum_le_sum hterm
      _ = (A.card : ENNReal) * (B * ((r : ENNReal) ^ 2 * (C : ENNReal) ^ 3 * D)) := by
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
          * ((r : NNReal) : ENNReal) ^ 2 := by
    simp only [nodeClassConst, hn, hr]
    push_cast
    ring
  rw [hunfold]
  calc (A.card : ENNReal) * (B * ((r : ENNReal) ^ 2 * (C : ENNReal) ^ 3 * D))
      ≤ ((2 * (25 : NNReal) ^ (2 * n) * (4 : NNReal) ^ (2 * n) : NNReal) : ENNReal)
          * (B * ((r : ENNReal) ^ 2 * (C : ENNReal) ^ 3 * D)) := by
        exact mul_le_mul_left hAcardE _
    _ = ((2 * (25 : NNReal) ^ (2 * n) * (4 : NNReal) ^ (2 * n) : NNReal) : ENNReal)
          * ((r : ENNReal) ^ 2) * (C : ENNReal) ^ 3 * B * D := by ring


/-- The tube-volume comparison ratio `C_n / c_n`. -/
noncomputable def tubeVolRatio : NNReal :=
  Tube.volume_le.C (Module.finrank ℝ E) / Tube.le_volume.c (Module.finrank ℝ E)


/-- **The two tube-volume comparison constants are ordered**, so the ratio is at least `1`. -/
theorem one_le_tubeVolRatio : (1 : NNReal) ≤ tubeVolRatio (E := E) := by
  obtain ⟨u, hu⟩ := exists_ne (0 : E)
  have hdist : dist (0 : E) (‖u‖⁻¹ • u) = 1 := by
    rw [dist_zero_left]; exact norm_smul_inv_norm hu
  set T : Tube (1 : NNReal) E := Tube.mk' (1 : NNReal) hdist
  have hle : (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal) ≤ volume T.carrier := by
    simpa [one_pow] using Tube.le_volume T
  rw [tubeVolRatio, le_div_iff₀ (Tube.le_volume.c_pos _), one_mul]
  exact ENNReal.coe_le_coe.mp
    (hle.trans (by simpa [one_pow] using Tube.volume_le (le_refl (1 : NNReal)) T))

/-- `Kakeya.MultiScaleFac.nodeClassConst` is at least `1`. -/
theorem one_le_nodeClassConst : (1 : NNReal) ≤ nodeClassConst (E := E) := by
  rw [nodeClassConst]
  refine one_le_mul_of_one_le_of_one_le ?_
    (one_le_pow₀ (by simpa [tubeVolRatio] using one_le_tubeVolRatio (E := E)))
  refine one_le_mul_of_one_le_of_one_le ?_ (one_le_pow₀ (by norm_num))
  exact one_le_mul_of_one_le_of_one_le (by norm_num) (one_le_pow₀ (by norm_num))


/-- **The bottom grid scale.**  At `ρ_N = δ` the node is itself a `δ`-tube, so the class is
`tubeVolRatio`-Frostman in it for purely dimensional reasons, with no hypothesis on the family.
This covers the index `k = N`, where the grid separation `2δ ≤ ρ_k` that
`isFrostmanIn_coverClass_of_fibre` needs fails outright. -/
theorem isFrostmanIn_coverClass_bottom {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ}
    {C : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hN : 0 < N) (𝒰 : UniformTubeSet s T N C)
    {j : ι} (hj : j ∈ 𝒰.cover.indexSet N) :
    ConvexSpaceBody.IsFrostmanIn (coverClass s (𝒰.cover.assign N) j)
      (fun i => (T i).toConvexSpaceBody) (𝒰.cover.tube N j).toConvexSpaceBody
      ((tubeVolRatio (E := E) : ENNReal)) := by
  classical
  set n : ℕ := Module.finrank ℝ E
  set p : ℕ := n - 1
  set c : NNReal := Tube.le_volume.c n
  set Cn : NNReal := Tube.volume_le.C n
  set cls : Finset ι := coverClass s (𝒰.cover.assign N) j
  set W : ι → ConvexSpaceBody E := fun i => (T i).toConvexSpaceBody
  set Kj : ConvexSpaceBody E := (𝒰.cover.tube N j).toConvexSpaceBody
  set D : ENNReal := Kakeya.densityIn cls W Kj
  set Q : ENNReal := (cls.card : ENNReal)
  set v : ENNReal := (δ : ENNReal) ^ p
  set r : NNReal := Cn / c with hr
  have hband : Q * (↑c * v) ≤ D * (↑Cn * v) := by
    have hb := card_coverClass_mul_le_densityIn_node hδ hδ1 𝒰 (le_refl N) hj
    simpa [cls, W, Kj, D, Q, v, c, Cn, n, p, gridScale_self δ hN] using hb
  have hv0 : v ≠ 0 := by
    dsimp [v]
    exact pow_ne_zero p (by exact_mod_cast hδ.ne')
  have hv_top : v ≠ ⊤ := by
    dsimp [v]
    exact ENNReal.pow_ne_top ENNReal.coe_ne_top
  have hband' : Q * ↑c ≤ D * ↑Cn := by
    apply (ENNReal.mul_le_mul_iff_right hv0 hv_top).mp
    simpa [mul_assoc, mul_comm, mul_left_comm] using hband
  have hc_ne : c ≠ 0 := (Tube.le_volume.c_pos n).ne'
  have hnn : (r * c : NNReal) = Cn := by
    dsimp [r]
    exact div_mul_cancel₀ Cn hc_ne
  have hrc : (r : ENNReal) * (c : ENNReal) = (Cn : ENNReal) := by
    rw [← ENNReal.coe_mul, hnn]
  have hband'' : Q * (c : ENNReal) ≤ (↑r * D) * (c : ENNReal) := by
    calc
      Q * (c : ENNReal) ≤ D * (Cn : ENNReal) := hband'
      _ = (↑r * D) * (c : ENNReal) := by
          rw [← hrc]
          ring
  have hc0 : (c : ENNReal) ≠ 0 := by exact_mod_cast hc_ne
  have hc_top : (c : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hQ : Q ≤ ↑r * D := by
    apply (ENNReal.mul_le_mul_iff_right hc0 hc_top).mp
    simpa [mul_comm, mul_left_comm, mul_assoc] using hband''
  intro K' hK'
  refine le_trans (Kakeya.le_maxDensity (s := cls) W K') ?_
  refine le_trans (Kakeya.maxDensity_le_card cls W) ?_
  simpa [tubeVolRatio, r, Cn, c, n, p, cls, W, D, Q] using hQ


/-- **The translation of a fibre bound, at every grid index.**  Combines
`isFrostmanIn_coverClass_of_fibre`, whose covering step needs the grid separation `2δ ≤ ρ_k` and
hence `k < N`, with `isFrostmanIn_coverClass_bottom`, which covers `k = N` unconditionally. -/
theorem isFrostmanIn_coverClass_of_fibre_grid {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} {C : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hN : 0 < N)
    (hδN : δ ≤ (16 : NNReal) ^ (-(N : ℝ))) (𝒰 : UniformTubeSet s T N C) {k : ℕ} (hk : k ≤ N)
    {j : ι} (hj : j ∈ 𝒰.cover.indexSet k) (hs : s.Nonempty) {B : ENNReal}
    (hB : ∀ a ∈ s, ConvexSpaceBody.IsFrostmanIn (fibreIndex s T δ (gridScale δ N k) a)
      (fun i => (T i).toConvexSpaceBody)
      ((T a).rescale (gridScale δ N k)).toConvexSpaceBody B) :
    ConvexSpaceBody.IsFrostmanIn (coverClass s (𝒰.cover.assign k) j)
      (fun i => (T i).toConvexSpaceBody) (𝒰.cover.tube k j).toConvexSpaceBody
      (max ((nodeClassConst (E := E) : ENNReal) * (C : ENNReal) ^ 3 * B)
        (tubeVolRatio (E := E) : ENNReal)) := by
  rcases Nat.lt_or_ge k N with hkN | hkN
  · have h8 : 8 * δ ≤ gridScale δ N k := eight_delta_le_gridScale hδ hδ1 hkN hδN
    have h2 : 2 * δ ≤ gridScale δ N k := by
      refine le_trans (mul_le_mul_of_nonneg_right (by norm_num : (2 : NNReal) ≤ 8) ?_) h8
      exact le_of_lt hδ
    exact isFrostmanIn_mono_helper (E := E)
      (isFrostmanIn_coverClass_of_fibre hδ hδ1 𝒰 hk h2 hj hs hB) (le_max_left _ _)
  · have hkeq : k = N := le_antisymm hk hkN
    subst hkeq
    exact isFrostmanIn_mono_helper (E := E)
      (isFrostmanIn_coverClass_bottom hδ hδ1 hN 𝒰 hj) (le_max_right _ _)

/-- **Alternative (i), translated.**  A family that is Frostman at every real scale in the
leaf-anchored sense is Frostman at every grid index in the node-anchored sense of
`StickyKakeya.UniformTubeSet.IsFrostmanAtEveryScale`, at the cost of a dimensional constant and
`C ^ 3`. -/
theorem isFrostmanAtEveryScale_nodes_of_fibre {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} {C : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hN : 0 < N)
    (hδN : δ ≤ (16 : NNReal) ^ (-(N : ℝ))) (𝒰 : UniformTubeSet s T N C) (hs : s.Nonempty)
    {A : ENNReal} (hA : StickyKakeya.IsFrostmanAtEveryScale s T A) :
    𝒰.IsFrostmanAtEveryScale
      (max ((nodeClassConst (E := E) : ENNReal) * (C : ENNReal) ^ 3 * A)
        (tubeVolRatio (E := E) : ENNReal)) := by
  intro k hk j hj
  refine isFrostmanIn_coverClass_of_fibre_grid hδ hδ1 hN hδN 𝒰 hk hj hs ?_
  intro a ha
  have hδρ : δ ≤ gridScale δ N k := by
    have h := gridScale_antitone hδ hδ1 N hk
    rwa [gridScale_self δ hN] at h
  have hρ1 : gridScale δ N k ≤ 1 := gridScale_le_one hδ1 N k
  have h := hA (gridScale δ N k) hδρ hρ1 a ha
  rw [fibreIndex_self]
  exact h

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **The nodes of a member nest over any range of grid indices**, not just consecutive ones. -/
theorem tube_assign_le_of_le {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ}
    (𝒢 : GridCoverSystem s T N) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ N) {i : ι} (hi : i ∈ s) :
    (𝒢.tube b (𝒢.assign b i)).toConvexSpaceBody ≤ (𝒢.tube a (𝒢.assign a i)).toConvexSpaceBody := by
  have hmain : ∀ d : ℕ, a + d ≤ N →
      (𝒢.tube (a + d) (𝒢.assign (a + d) i)).toConvexSpaceBody
        ≤ (𝒢.tube a (𝒢.assign a i)).toConvexSpaceBody := by
    intro d
    induction d with
    | zero =>
        intro _
        rfl
    | succ d ih =>
        intro h
        have hk1 : (a + d) + 1 ≤ N := by omega
        have hn : a + (d + 1) = (a + d) + 1 := by omega
        have h1 : (𝒢.tube (a + (d + 1)) (𝒢.assign (a + (d + 1)) i)).toConvexSpaceBody
            ≤ (𝒢.tube (a + d) (𝒢.assign (a + d) i)).toConvexSpaceBody := by
          rw [hn]
          exact 𝒢.tube_nested (a + d) hk1 i hi
        have h2 : (𝒢.tube (a + d) (𝒢.assign (a + d) i)).toConvexSpaceBody
            ≤ (𝒢.tube a (𝒢.assign a i)).toConvexSpaceBody := ih (by omega)
        exact h1.trans h2
  have hbd : a + (b - a) = b := Nat.add_sub_cancel' hab
  have hbNA : a + (b - a) ≤ N := by
    rw [hbd]
    exact hb
  rw [← hbd]
  exact hmain (b - a) hbNA

/-- **The count of nodes under a node against their density in it**, the analogue of
`card_coverClass_mul_le_densityIn_node` one level up: the nodes at index `b` under a node at index
`a` lie inside it by definition of `nodesUnder`, so their count weighted by the minimal `ρ_b`-tube
volume is at most their density weighted by the maximal `ρ_a`-tube volume. -/
theorem card_nodesUnder_mul_le_densityIn {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} {C : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (𝒰 : UniformTubeSet s T N C)
    {a b : ℕ} (_ha : a ≤ N) {j : ι} :
    ((𝒰.nodesUnder b a j).card : ENNReal)
        * (((Tube.le_volume.c (Module.finrank ℝ E) : NNReal) : ENNReal)
            * ((gridScale δ N b : ENNReal) ^ (Module.finrank ℝ E - 1)))
      ≤ Kakeya.densityIn (𝒰.nodesUnder b a j)
            (fun j' => (𝒰.cover.tube b j').toConvexSpaceBody)
            (𝒰.cover.tube a j).toConvexSpaceBody
          * (((Tube.volume_le.C (Module.finrank ℝ E) : NNReal) : ENNReal)
              * ((gridScale δ N a : ENNReal) ^ (Module.finrank ℝ E - 1))) := by
  classical
  set n : ℕ := Module.finrank ℝ E
  set p : ℕ := n - 1
  set c : NNReal := Tube.le_volume.c n
  set Cn : NNReal := Tube.volume_le.C n
  set ρ : NNReal := gridScale δ N b
  set τ : NNReal := gridScale δ N a
  set nds : Finset ι := 𝒰.nodesUnder b a j
  set W : ι → ConvexSpaceBody E := fun j' => (𝒰.cover.tube b j').toConvexSpaceBody
  set Kj : ConvexSpaceBody E := (𝒰.cover.tube a j).toConvexSpaceBody
  have hτpos : 0 < τ := gridScale_pos hδ N a
  have hτ1 : τ ≤ 1 := gridScale_le_one hδ1 N a
  have hmem : ∀ j' ∈ nds, W j' ≤ Kj := by
    intro j' hj'
    have hf : j' ∈ 𝒰.cover.indexSet b ∧
        (𝒰.cover.tube b j').toConvexSpaceBody ≤ (𝒰.cover.tube a j).toConvexSpaceBody := by
      simpa [nds, UniformTubeSet.nodesUnder, UniformTubeSet.nodesIn, Finset.mem_filter] using hj'
    simpa [W, Kj] using hf.2
  have hvmin : ∀ j' ∈ nds, (↑c * (ρ : ENNReal) ^ p) ≤ volume (W j').carrier := by
    intro j' hj'
    simpa [c, p, n, ρ, W, ENNReal.coe_mul, ENNReal.coe_pow] using Tube.le_volume (𝒰.cover.tube b j')
  have hge := densityIn_ge_of_count_volume (s := nds) (W := W) (K := Kj)
    (Finset.Subset.refl nds) hmem hvmin
  have hvol_lb : ((Tube.le_volume.c n * τ ^ p : NNReal) : ENNReal) ≤ volume Kj.carrier := by
    simpa [Kj, τ, p, n] using Tube.le_volume (𝒰.cover.tube a j)
  have hvol_ne_zero : volume Kj.carrier ≠ 0 := by
    have hpos : 0 < (Tube.le_volume.c n * τ ^ p : NNReal) := by
      exact mul_pos (Tube.le_volume.c_pos n) (pow_pos hτpos p)
    exact ne_of_gt (lt_of_lt_of_le (ENNReal.coe_pos.mpr hpos) hvol_lb)
  have hvol_ne_top : volume Kj.carrier ≠ ⊤ := Kj.isCompact.measure_ne_top
  have hcount : (nds.card : ENNReal) * (↑c * (ρ : ENNReal) ^ p) ≤
      densityIn nds W Kj * volume Kj.carrier := by
    rw [ENNReal.div_le_iff hvol_ne_zero hvol_ne_top] at hge
    exact hge
  have hvol_le : volume Kj.carrier ≤ ↑Cn * (τ : ENNReal) ^ p := by
    simpa [Kj, Cn, τ, p, n, ENNReal.coe_mul, ENNReal.coe_pow] using
      Tube.volume_le hτ1 (𝒰.cover.tube a j)
  calc
    (nds.card : ENNReal) * (↑c * (ρ : ENNReal) ^ p)
        ≤ densityIn nds W Kj * volume Kj.carrier := hcount
    _ ≤ densityIn nds W Kj * (↑Cn * (τ : ENNReal) ^ p) :=
        mul_le_mul_right hvol_le (densityIn nds W Kj)


end MultiScaleFac
end Kakeya

end
