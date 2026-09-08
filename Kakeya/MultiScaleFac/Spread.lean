/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Frostman
public import Kakeya.MultiScaleFac.Loss
public import Kakeya.MultiScaleFac.Stopping

/-!
# Spreading one witness across a grid level, half (A)

The witness extracted from a lower bound at one node, the two-sided band that carries it to every
node of the level, and the loss arithmetic that keeps the price subpolynomial.

This module is the merge of the former `Bullet3SpreadA`, `Bullet3Witness`, `Bullet3Accounting`.
Each keeps its own section, so its file-level `open`s and `variable`s stay confined to it.

## Spreading a Frostman lower bound over a grid level

The third bullet of alternative (ii) of GWZ Lemma 7.7(A) is reduced, by
`Kakeya.MultiScaleFac.le_frostmanConstant_nodesIn_rescale_of_grid_dilate`, to a lower bound on
`ConvexSpaceBody.frostmanConstant (𝒰.nodesIn b (8ρ_c-dilate of p))` holding at **every** level-`c`
node `p`.  The stopping time delivers that bound at a *single* node — the level-`c` node carrying a
leaf of the majority set.  This section contains the step that turns the single node into every
node.

The input is the two-sided band `Φ ≤ Δ_max(class image) ≤ C_b Φ` of the paired homogenizing pass,
which is the band component of `Kakeya.MultiScaleFac.BandedSuper`.  Its two halves are used in
different places, and that is the whole content of the argument:

* at the witness node the *upper* half converts the witness into the band value `Φ`;
* at an arbitrary node the *lower* half converts `Φ` back into a maximal density, which is a lower
  bound for the Frostman constant of the node family once the density of that family in its own
  container is bounded above.

The last ingredient is the hypothesis `hdens`.  It is not a band: it is the statement that the
level-`b` nodes inside a `8ρ_c`-dilate occupy a bounded fraction of it, which is bounded overlap of
the hierarchy and carries no power of `δ`.

## The witness of the half-(A) third bullet, and the alignment of the band

`Kakeya.MultiScaleFac.le_frostmanConstant_nodesIn_dilate_of_band` spreads a lower bound from one
level-`c` node to every level-`c` node, and it asks for two things that the stopping time does not
hand over in that shape:

* a **witness** of the form `X ≤ D · Δ_max(class image of p₀)`, where the stopping time, through
  `Kakeya.MultiScaleFac.frostmanConstant_fibre_le_mul_frostmanConstant_nodesIn`, produces
  `X ≤ D · C_F(level-`b` nodes of the `8ρ_c`-dilate of `p₀`)`;
* a **band** read on the cover of the family `𝒰` that the third bullet quantifies over, where
  `Kakeya.MultiScaleFac.BandedSuper` carries a band on a *superfamily* `u ⊇ t` and on a grid-uniform
  system `𝒢` of its own.

This section closes both gaps as far as they can be closed with no power of `δ`.

## The witness

`Kakeya.MultiScaleFac.exists_classImage_witness_of_le_mul_frostmanConstant_nodesIn` is the half-(A)
analogue of `Kakeya.MultiScaleFac.exists_undilated_of_dilated`.  Two inputs beyond the witness
itself:

* the Katz-Tao covering of a dilated node by boundedly many class images of its own level, which is
  the conclusion of `Kakeya.MultiScaleFac.exists_coarseNeighbours`;
* a **lower** bound `dm` for the density of the node family of the dilate in the dilate.  It is
  needed because the witness speaks about a Frostman constant, which is a *ratio*
  `Δ_max / Δ` (`ConvexSpaceBody.frostmanConstant_eq_maxDensity_div`), while the band speaks about
  `Δ_max` alone: turning the ratio into its numerator is exactly division by the anchor density.
  This is the mirror of the density *upper* bound `hdens` of
  `Kakeya.MultiScaleFac.le_frostmanConstant_nodesIn_dilate_of_band`, and like it, it is bounded
  overlap of the hierarchy and carries no power of `δ`.

## The band

`Kakeya.StickyKakeya.band_of_alignedSuper` transports a band from the superfamily of
`Kakeya.MultiScaleFac.BandedSuper` to the subfamily and to the subfamily's own cover.  It is stated
for a destructured `BandedSuper`, since its hypotheses talk about the superfamily and about the
system carrying the band, both of which are bound existentially inside that definition.

The transport is free of constants, and it is conditional on the two alignments that the invariant
does not by itself provide: that the two covers agree at every grid level, and that the subfamily
still meets every level-`b` node that the superfamily meets inside a level-`c` class
(*node survival*).  Node survival is what the *lower* half of the band needs and cannot get from
the cardinality proportion `|u| ≤ Λ |t|`: that proportion is global, and `Kakeya.maxDensity` of a
node family is not bounded below by that of a superfamily whose extra nodes are unaccounted for.
The *upper* half needs neither hypothesis beyond the cover alignment, being monotonicity of
`Kakeya.maxDensity` along `t ⊆ u`.

## The window and loss accounting of the half-(A) third bullet

The third bullet of half (A) reaches its conclusion through four transports, each of which displays
its own coefficient: the stopping time's own `δ^{-27/⌈\log\log 1/δ⌉}`, the number `K_n` of coarse
neighbours covering a dilated node, the band constant `C_b`, the two node-density constants, and
the volume constants of the grid rounding.  This section collects the arithmetic that turns such a
product into the single displayed `Kakeya.MultiScaleFac.totalLoss` of the amended statement, and the
one composite step of the chain that can be stated below `Kakeya/MultiScaleFac/GapsA.lean`.

## The arithmetic

`Kakeya/MultiScaleFac/GapsKT.lean` proves the same `Kakeya.MultiScaleFac.scaleGapLoss` identities,
but that file sits *above* `Kakeya/MultiScaleFac/GapsA.lean`, whose third bullet is the consumer
here, so the three identities are reproved rather than imported.  They are one `Real.rpow`
computation each.

## The composite step

`Kakeya.MultiScaleFac.A.hgrid_of_witness` joins
`Kakeya.MultiScaleFac.exists_classImage_witness_of_le_mul_frostmanConstant_nodesIn` to
`Kakeya.MultiScaleFac.le_frostmanConstant_nodesIn_dilate_of_band`: a lower bound at the
`8ρ_c`-dilate of *one* level-`c` node becomes a lower bound at the `8ρ_c`-dilate of *every*
level-`c` node.  That is exactly the universal-in-the-node hypothesis `hgrid` of
`Kakeya.MultiScaleFac.le_frostmanConstant_nodesIn_rescale_of_grid_dilate`, which is where the rest
of the third bullet takes over.
-/

@[expose] public section

open MeasureTheory Real Metric

universe u
open Tube

namespace Kakeya

open StickyKakeya

namespace MultiScaleFac

open _root_.StickyKakeya

variable {ι : Type u}
variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
open scoped Classical in
/-- **The class image of a level-`c` node sits among the level-`b` nodes of its `8ρ_c`-dilate.**

Each member of the class lies in its own level-`b` node, that node lies in the level-`c` node by
nestedness of the cover, and the level-`c` node lies in its own dilate. -/
theorem classImage_subset_nodesIn_rescale_implicit {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} {Cu : NNReal} (𝒰 : UniformTubeSet s T N Cu) {c b : ℕ} (hcb : c ≤ b) (hb : b ≤ N)
    {p : ι} :
    (coverClass s (𝒰.cover.assign c) p).image (𝒰.cover.assign b)
      ⊆ 𝒰.nodesIn b (((𝒰.cover.tube c p).rescale
          (8 * gridScale δ N c)).toConvexSpaceBody) := by
  classical
  letI : ProperSpace E := FiniteDimensional.proper_real E
  rw [Finset.image_subset_iff]
  intro i hi
  obtain ⟨hi_s, hi_p⟩ := by simpa [coverClass] using hi
  have h := tube_assign_le_of_le 𝒰.cover hcb hb hi_s
  rw [hi_p] at h
  exact (𝒰.mem_nodesIn_iff _ _ _).mpr ⟨𝒰.cover.assign_mem b hb i hi_s,
    h.trans (Tube.le_rescale _ (le_mul_of_one_le_left zero_le (by norm_num : (1 : NNReal) ≤ 8)))⟩

omit [Nontrivial E] in
open scoped Classical in
/-- **One witness node plus the band gives every node** (blueprint `lem:bullet3SpreadA`).  The
half-(A) analogue of `Kakeya.MultiScaleFac.le_maxDensity_nodesUnder_of_band`: the band brackets the
maximal density of the level-`b` image of a level-`c` class between `Φ` and `C_b Φ` uniformly in the
node, so a lower bound at a single node `p₀` becomes a lower bound at an arbitrary node `p`. -/
theorem le_frostmanConstant_nodesIn_dilate_of_band {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} {Cu : NNReal} (𝒰 : UniformTubeSet s T N Cu) {c b : ℕ} (hcb : c ≤ b) (hb : b ≤ N)
    {X D Φ Dm : ENNReal} {Cb : NNReal}
    (hband : ∀ p ∈ 𝒰.cover.indexSet c,
      Φ ≤ Kakeya.maxDensity ((coverClass s (𝒰.cover.assign c) p).image (𝒰.cover.assign b))
            (fun j' => (𝒰.cover.tube b j').toConvexSpaceBody) ∧
        Kakeya.maxDensity ((coverClass s (𝒰.cover.assign c) p).image (𝒰.cover.assign b))
            (fun j' => (𝒰.cover.tube b j').toConvexSpaceBody) ≤ (Cb : ENNReal) * Φ)
    (hdens : ∀ p ∈ 𝒰.cover.indexSet c,
      Kakeya.densityIn
          (𝒰.nodesIn b (((𝒰.cover.tube c p).rescale
            (8 * gridScale δ N c)).toConvexSpaceBody))
          (fun j' => (𝒰.cover.tube b j').toConvexSpaceBody)
          (((𝒰.cover.tube c p).rescale (8 * gridScale δ N c)).toConvexSpaceBody) ≤ Dm)
    (hwit : ∃ p₀ ∈ 𝒰.cover.indexSet c,
      X ≤ D * Kakeya.maxDensity
            ((coverClass s (𝒰.cover.assign c) p₀).image (𝒰.cover.assign b))
            (fun j' => (𝒰.cover.tube b j').toConvexSpaceBody)) :
    ∀ p ∈ 𝒰.cover.indexSet c,
      X ≤ D * (Cb : ENNReal) * Dm * ConvexSpaceBody.frostmanConstant
          (𝒰.nodesIn b (((𝒰.cover.tube c p).rescale
            (8 * gridScale δ N c)).toConvexSpaceBody))
          (fun j' => (𝒰.cover.tube b j').toConvexSpaceBody)
          (((𝒰.cover.tube c p).rescale (8 * gridScale δ N c)).toConvexSpaceBody) := by
  obtain ⟨p₀, hp₀, hX⟩ := hwit
  have h1 : X ≤ D * (Cb : ENNReal) * Φ :=
    hX.trans (by rw [mul_assoc]; exact mul_le_mul_right (hband p₀ hp₀).2 D)
  intro p hp
  refine (h1.trans (mul_le_mul_right ?_ _)).trans_eq
    ((mul_assoc _ _ _).symm.trans (mul_right_comm _ _ _))
  exact ((hband p hp).1.trans <| (Kakeya.maxDensity_mono _
      (classImage_subset_nodesIn_rescale_implicit 𝒰 hcb hb (p := p))).trans <|
    ConvexSpaceBody.isFrostmanIn_frostmanConstant.maxDensity_le_of_carrier_subset
      fun i hi => ((𝒰.mem_nodesIn_iff _ _ i).mp hi).2).trans
    (mul_le_mul_right (hdens p hp) _)

/-! ### From a Frostman constant to a maximal density -/

omit [Nontrivial E] in
/-- **A lower bound for the anchor density turns a Frostman constant into a maximal density.**

`ConvexSpaceBody.frostmanConstant_eq_maxDensity_div` reads the Frostman constant as
`Δ_max(𝕎) / Δ(𝕎, K)` whenever the anchor body contains the family, so a lower bound `dm` for the
anchor density is exactly what converts a lower bound on the constant into one on `Δ_max`. -/
theorem mul_frostmanConstant_le_maxDensity_of_le_densityIn {S : Finset ι}
    {W : ι → ConvexSpaceBody E} {K : ConvexSpaceBody E} {dm : ENNReal} (hdm : dm ≠ 0)
    (hlow : dm ≤ Kakeya.densityIn S W K) (hWK : ∀ i ∈ S, W i ≤ K) :
    dm * ConvexSpaceBody.frostmanConstant S W K ≤ Kakeya.maxDensity S W := by
  have hd : 0 < Kakeya.densityIn S W K := lt_of_lt_of_le (pos_iff_ne_zero.mpr hdm) hlow
  rw [ConvexSpaceBody.frostmanConstant_eq_maxDensity_div hd hWK]
  exact (mul_le_mul_left hlow _).trans_eq
    (ENNReal.mul_div_cancel hd.ne' (Kakeya.densityIn_ne_top S W K))

/-! ### The witness, moved onto a class image -/

omit [Nontrivial E] in
open scoped Classical in
/-- **From the anchored lower bound to a lower bound at one class image** (blueprint
`lem:bullet3WitnessA`).  The half-(A) analogue of
`Kakeya.MultiScaleFac.exists_undilated_of_dilated`: dividing the stopping time's Frostman lower
bound by the anchor density and covering the `8ρ_c`-dilate by boundedly many level-`c` class images
moves the bound onto one of them, for the pair `(c, b)` at hand. -/
theorem exists_classImage_witness_of_le_mul_frostmanConstant_nodesIn {δ : NNReal} {s : Finset ι}
    {T : ι → Tube δ E} {N : ℕ} {Cu : NNReal} (𝒰 : UniformTubeSet s T N Cu) {c b Kn : ℕ}
    {X D dm : ENNReal} (hdm : dm ≠ 0) {j : ι} (hj : j ∈ 𝒰.cover.indexSet c)
    (hP : ∃ P ⊆ 𝒰.cover.indexSet c, P.card ≤ Kn ∧
      𝒰.nodesIn b ((𝒰.cover.tube c j).rescale (8 * gridScale δ N c)).toConvexSpaceBody
        ⊆ P.biUnion (fun p =>
            (coverClass s (𝒰.cover.assign c) p).image (𝒰.cover.assign b)))
    (hlow : dm ≤ Kakeya.densityIn
        (𝒰.nodesIn b ((𝒰.cover.tube c j).rescale (8 * gridScale δ N c)).toConvexSpaceBody)
        (fun j' => (𝒰.cover.tube b j').toConvexSpaceBody)
        ((𝒰.cover.tube c j).rescale (8 * gridScale δ N c)).toConvexSpaceBody)
    (hX : X ≤ D * ConvexSpaceBody.frostmanConstant
        (𝒰.nodesIn b ((𝒰.cover.tube c j).rescale (8 * gridScale δ N c)).toConvexSpaceBody)
        (fun j' => (𝒰.cover.tube b j').toConvexSpaceBody)
        ((𝒰.cover.tube c j).rescale (8 * gridScale δ N c)).toConvexSpaceBody) :
    ∃ p ∈ 𝒰.cover.indexSet c,
      X ≤ D * (Kn : ENNReal) / dm * Kakeya.maxDensity
          ((coverClass s (𝒰.cover.assign c) p).image (𝒰.cover.assign b))
          (fun j' => (𝒰.cover.tube b j').toConvexSpaceBody) := by
  set K : ConvexSpaceBody E :=
    ((𝒰.cover.tube c j).rescale (8 * gridScale δ N c)).toConvexSpaceBody
  set W : ι → ConvexSpaceBody E := fun x => (𝒰.cover.tube b x).toConvexSpaceBody
  set Nod : Finset ι := 𝒰.nodesIn b K
  set G : ι → Finset ι := fun p =>
    (coverClass s (𝒰.cover.assign c) p).image (𝒰.cover.assign b)
  have hWK : ∀ i ∈ Nod, W i ≤ K := fun i hi => ((𝒰.mem_nodesIn_iff b K i).mp hi).2
  have hmul : dm * ConvexSpaceBody.frostmanConstant Nod W K ≤ Kakeya.maxDensity Nod W :=
    mul_frostmanConstant_le_maxDensity_of_le_densityIn hdm hlow hWK
  obtain ⟨P, hPsub, hPcard, hcov⟩ := hP
  have hsum : Kakeya.maxDensity Nod W ≤ ∑ q ∈ P, Kakeya.maxDensity (G q) W :=
    maxDensity_le_sum_of_subset_biUnion (W := W) hcov
  have hdmTop : dm ≠ ⊤ := ne_top_of_le_ne_top (densityIn_ne_top Nod W K) hlow
  by_cases hPe : P = ∅
  · rw [hPe, Finset.biUnion_empty] at hcov
    have hNodempty : Nod = ∅ := Finset.subset_empty.mp hcov
    rw [hNodempty, Kakeya.maxDensity_empty, nonpos_iff_eq_zero, mul_eq_zero] at hmul
    rw [hNodempty, hmul.resolve_left hdm, mul_zero, nonpos_iff_eq_zero] at hX
    exact ⟨j, hj, hX.le.trans zero_le⟩
  · obtain ⟨p, hpP, hpmax⟩ := Finset.exists_max_image (s := P)
      (f := fun q => Kakeya.maxDensity (G q) W) (Finset.nonempty_iff_ne_empty.mpr hPe)
    have hNod_le : Kakeya.maxDensity Nod W ≤ (Kn : ENNReal) * Kakeya.maxDensity (G p) W := by
      refine hsum.trans ((Finset.sum_le_card_nsmul P _ (Kakeya.maxDensity (G p) W)
        fun q hq => hpmax q hq).trans ?_)
      rw [nsmul_eq_mul]
      exact mul_le_mul_left (by exact_mod_cast hPcard) _
    have hchain : X * dm ≤ D * (Kn : ENNReal) * Kakeya.maxDensity (G p) W := by
      calc X * dm = dm * X := mul_comm _ _
        _ ≤ dm * (D * ConvexSpaceBody.frostmanConstant Nod W K) := mul_le_mul_right hX dm
        _ = D * (dm * ConvexSpaceBody.frostmanConstant Nod W K) := mul_left_comm _ _ _
        _ ≤ D * ((Kn : ENNReal) * Kakeya.maxDensity (G p) W) :=
          mul_le_mul_right (hmul.trans hNod_le) D
        _ = D * (Kn : ENNReal) * Kakeya.maxDensity (G p) W := (mul_assoc _ _ _).symm
    refine ⟨p, hPsub hpP, ?_⟩
    rw [div_eq_mul_inv, mul_right_comm, ← div_eq_mul_inv]
    exact (ENNReal.le_div_iff_mul_le (Or.inl hdm) (Or.inl hdmTop)).mpr hchain

/-! ### The band, moved onto the family's own cover -/

/-! ### The arithmetic of the gap loss -/

/-! ### Raising and combining displayed losses -/

/-- **A bare constant and a gap loss make a displayed loss.**  This is the shape in which every
absolute constant of the third bullet -- the number of coarse neighbours, the band constant, the
two node-density constants, the volume constants of the grid rounding -- is absorbed. -/
theorem A.const_scaleGapLoss_le {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {A C : NNReal}
    (hA : 1 ≤ A) (hAC : A ≤ C) {c₀ K c : ℕ} (hc : c₀ ≤ c) :
    (A : ENNReal) * ENNReal.ofReal (scaleGapLoss c₀ δ)
      ≤ (C : ENNReal) * totalLoss C K c δ := by
  have hE : ENNReal.ofReal (scaleGapLoss c₀ δ) ≤ totalLoss C K c δ := by
    rw [totalLoss_eq_ofReal]
    exact ENNReal.ofReal_le_ofReal ((MultiScaleFac.A.scaleGapLoss_mono hδ hδ1 hc).trans
      (le_mul_of_one_le_left (zero_le_one.trans (one_le_scaleGapLoss c hδ hδ1))
        (one_le_gridLoss C (hA.trans hAC) K hδ1)))
  exact mul_le_mul' (ENNReal.coe_le_coe.mpr hAC) hE

/-- **A bare constant and two displayed losses make one displayed loss.**  The product of two losses
is the loss at the product of the bases and the sum of the two exponents
(`Kakeya.MultiScaleFac.gridLoss_mul`, `Kakeya.MultiScaleFac.A.scaleGapLoss_add`), raised to a common
one by `Kakeya.MultiScaleFac.loss_raise`. -/
theorem A.prod_le {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {A B₁ B₂ C : NNReal}
    (hA : 1 ≤ A) (hB₁ : 1 ≤ B₁) (hB₂ : 1 ≤ B₂) {K₁ K₂ K c₁ c₂ c : ℕ}
    (hC : A * B₁ * B₂ ≤ C) (hK : K₁ + K₂ ≤ K) (hc : c₁ + c₂ ≤ c) {X Y : ENNReal}
    (h : X ≤ (A : ENNReal) * ((B₁ : ENNReal) * totalLoss B₁ K₁ c₁ δ) *
        ((B₂ : ENNReal) * totalLoss B₂ K₂ c₂ δ) * Y) :
    X ≤ (C : ENNReal) * totalLoss C K c δ * Y := by
  have hBBP : B₁ * B₂ ≤ A * B₁ * B₂ := by
    rw [mul_assoc]; exact le_mul_of_one_le_left zero_le hA
  refine h.trans (mul_le_mul_left ?_ Y)
  calc
    (A : ENNReal) * ((B₁ : ENNReal) * totalLoss B₁ K₁ c₁ δ) *
          ((B₂ : ENNReal) * totalLoss B₂ K₂ c₂ δ)
        = ((A * B₁ * B₂ : NNReal) : ENNReal) *
            (totalLoss B₁ K₁ c₁ δ * totalLoss B₂ K₂ c₂ δ) := by push_cast; ring
    _ = ((A * B₁ * B₂ : NNReal) : ENNReal) * totalLoss (B₁ * B₂) (K₁ + K₂) (c₁ + c₂) δ := by
          rw [totalLoss_mul hB₁ hB₂ K₁ K₂ c₁ c₂ hδ hδ1]
    _ ≤ ((A * B₁ * B₂ : NNReal) : ENNReal) *
          totalLoss (A * B₁ * B₂) (K₁ + K₂) (c₁ + c₂) δ :=
          mul_le_mul_right (totalLoss_mono (one_le_mul_of_one_le_of_one_le hB₁ hB₂) hBBP
            le_rfl le_rfl hδ hδ1) _
    _ ≤ (C : ENNReal) * totalLoss C K c δ :=
          MultiScaleFac.loss_raise
            (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hA hB₁) hB₂)
            hC hK hc hδ hδ1

/-! ### From one witness node to every node of the level -/

omit [Nontrivial E] in
open scoped Classical in
/-- **The two steps that remove the majority set, in one** (blueprint `lem:bullet3GridA`).  The
witness step moves the terminal alternative's lower bound at the `8ρ_c`-dilate of a single level-`c`
node onto one class image, and `le_frostmanConstant_nodesIn_dilate_of_band` spreads it over the
whole level.  The composite is the hypothesis `hgrid` of
`le_frostmanConstant_nodesIn_rescale_of_grid_dilate`, with no majority set left. -/
theorem A.hgrid_of_witness {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} {Cu : NNReal} (𝒰 : UniformTubeSet s T N Cu) {c b Kn : ℕ}
    (hcb : c ≤ b) (hb : b ≤ N) {X D dm Dm Φ : ENNReal} {Cb : NNReal} (hdm : dm ≠ 0)
    (hP : ∀ p ∈ 𝒰.cover.indexSet c, ∃ P ⊆ 𝒰.cover.indexSet c, P.card ≤ Kn ∧
      𝒰.nodesIn b ((𝒰.cover.tube c p).rescale (8 * gridScale δ N c)).toConvexSpaceBody
        ⊆ P.biUnion (fun q =>
            (coverClass s (𝒰.cover.assign c) q).image (𝒰.cover.assign b)))
    (hdmlow : ∀ p ∈ 𝒰.cover.indexSet c, dm ≤ Kakeya.densityIn
        (𝒰.nodesIn b ((𝒰.cover.tube c p).rescale (8 * gridScale δ N c)).toConvexSpaceBody)
        (fun j' => (𝒰.cover.tube b j').toConvexSpaceBody)
        ((𝒰.cover.tube c p).rescale (8 * gridScale δ N c)).toConvexSpaceBody)
    (hdens : ∀ p ∈ 𝒰.cover.indexSet c, Kakeya.densityIn
        (𝒰.nodesIn b ((𝒰.cover.tube c p).rescale (8 * gridScale δ N c)).toConvexSpaceBody)
        (fun j' => (𝒰.cover.tube b j').toConvexSpaceBody)
        ((𝒰.cover.tube c p).rescale (8 * gridScale δ N c)).toConvexSpaceBody ≤ Dm)
    (hband : ∀ p ∈ 𝒰.cover.indexSet c,
      Φ ≤ Kakeya.maxDensity ((coverClass s (𝒰.cover.assign c) p).image (𝒰.cover.assign b))
            (fun j' => (𝒰.cover.tube b j').toConvexSpaceBody) ∧
        Kakeya.maxDensity ((coverClass s (𝒰.cover.assign c) p).image (𝒰.cover.assign b))
            (fun j' => (𝒰.cover.tube b j').toConvexSpaceBody) ≤ (Cb : ENNReal) * Φ)
    {j₀ : ι} (hj₀ : j₀ ∈ 𝒰.cover.indexSet c)
    (hX : X ≤ D * ConvexSpaceBody.frostmanConstant
        (𝒰.nodesIn b ((𝒰.cover.tube c j₀).rescale (8 * gridScale δ N c)).toConvexSpaceBody)
        (fun j' => (𝒰.cover.tube b j').toConvexSpaceBody)
        ((𝒰.cover.tube c j₀).rescale (8 * gridScale δ N c)).toConvexSpaceBody) :
    ∀ p ∈ 𝒰.cover.indexSet c,
      X ≤ D * (Kn : ENNReal) / dm * (Cb : ENNReal) * Dm * ConvexSpaceBody.frostmanConstant
          (𝒰.nodesIn b ((𝒰.cover.tube c p).rescale (8 * gridScale δ N c)).toConvexSpaceBody)
          (fun j' => (𝒰.cover.tube b j').toConvexSpaceBody)
          ((𝒰.cover.tube c p).rescale (8 * gridScale δ N c)).toConvexSpaceBody := by
  exact le_frostmanConstant_nodesIn_dilate_of_band 𝒰 hcb hb hband hdens
    (exists_classImage_witness_of_le_mul_frostmanConstant_nodesIn 𝒰 hdm hj₀
      (hP j₀ hj₀) (hdmlow j₀ hj₀) hX)

/-! ### The window rounding -/

/-- **A long block spans at least `3/ε` grid steps** (blueprint `lem:bullet3LongBlockA`).  Since
`Kakeya.MultiScaleFac.IsLongBlock` reads `⌈εM⌉ + a < b`, with `3N ≤ M` and `1 ≤ ε²N` one gets
`ε (b - a) ≥ ε² M ≥ 3 ε² N ≥ 3`: three grid steps of slack, one to move off the fine endpoint `b`
and two to pay the factor `32`. -/
theorem A.three_le_eps_mul_block {N : ℕ} {δ : NNReal} {ε : ℝ} (hεpos : 0 < ε)
    (hNM : 3 * N ≤ ssfGridLen δ) (hεN : 1 ≤ ε ^ 2 * (N : ℝ))
    {a b : ℕ} (hlong : IsLongBlock (ssfGridLen δ) ε a b) :
    3 ≤ ε * ((b : ℝ) - (a : ℝ)) := by
  have hM3 : (3 : ℝ) * (N : ℝ) ≤ (ssfGridLen δ : ℝ) := by exact_mod_cast hNM
  have hlongR : (⌈ε * (ssfGridLen δ : ℝ)⌉₊ : ℝ) + (a : ℝ) ≤ (b : ℝ) := by
    exact_mod_cast (by simpa [IsLongBlock] using hlong : ⌈ε * (ssfGridLen δ : ℝ)⌉₊ + a < b).le
  linarith [mul_le_mul_of_nonneg_left (Nat.le_ceil (ε * (ssfGridLen δ : ℝ))) hεpos.le,
    mul_le_mul_of_nonneg_left hlongR hεpos.le,
    mul_le_mul_of_nonneg_left hM3 (sq_nonneg ε)]

/-- **Rounding a real window scale to a grid index** (blueprint `lem:bullet3WindowRoundA`).  The
grid rounding of `le_frostmanConstant_nodesIn_rescale_of_grid_dilate` asks for an index `c ≤ b`
whose scale is both *below* `ρ/32` and *above* `2δ`; `c = min b (M - 1)` meets both, the window's
three grid steps of slack absorbing the factor `32`. -/
theorem A.exists_round_index {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδlt : δ < 1)
    (hδ16 : δ ≤ (16 : NNReal) ^ (-(ssfGridLen δ : ℝ))) (hM : 0 < ssfGridLen δ)
    {ε : ℝ} {a b : ℕ} (hab : a < b) (hbM : b ≤ ssfGridLen δ)
    (hεba : 3 ≤ ε * ((b : ℝ) - (a : ℝ))) {ρ : NNReal}
    (hlo : (gridScale δ (ssfGridLen δ) b : ℝ)
        * ((gridScale δ (ssfGridLen δ) a : ℝ)
            / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ ε ≤ (ρ : ℝ)) :
    ∃ c : ℕ, c ≤ b ∧ c ≤ ssfGridLen δ ∧
      2 * δ ≤ gridScale δ (ssfGridLen δ) c ∧
      32 * gridScale δ (ssfGridLen δ) c ≤ ρ := by
  let M := ssfGridLen δ
  let c := min b (M - 1)
  have hdR : (0 : ℝ) < (δ : ℝ) := NNReal.coe_pos.mpr hδ
  have hd1R : (δ : ℝ) < 1 := by exact_mod_cast hδlt
  have hδnonneg : 0 ≤ (δ : ℝ) := le_of_lt hdR
  have hMpos : 0 < M := hM
  have hMR : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hMpos
  have hMne : (M : ℝ) ≠ 0 := ne_of_gt hMR
  have hbM' : b ≤ M := hbM
  have hbpos : 0 < b := Nat.zero_lt_of_lt hab
  have hcbb : c ≤ b := min_le_left _ _
  have hcbM : c ≤ M := (min_le_right b (M - 1)).trans (Nat.sub_le M 1)
  have hcM : c < M := lt_of_le_of_lt (min_le_right b (M - 1)) (by omega)
  have hbcR : (b : ℝ) - 1 ≤ (c : ℝ) := by
    have hbc : b ≤ c + 1 := by dsimp only [c]; omega
    have : (b : ℝ) ≤ (c : ℝ) + 1 := by exact_mod_cast hbc
    linarith
  have hwin : (δ : ℝ) ^ (((b : ℝ) - ε * ((b : ℝ) - (a : ℝ))) / (M : ℝ)) ≤ (ρ : ℝ) := by
    rwa [gridScale_mul_ratio_rpow hδ M a b ε] at hlo
  have hstep1 : (δ : ℝ) ^ (((b : ℝ) - 3) / (M : ℝ)) ≤
      (δ : ℝ) ^ (((b : ℝ) - ε * ((b : ℝ) - (a : ℝ))) / (M : ℝ)) :=
    (rpow_div_le_rpow_div_iff (N := M) hδ hd1R hMpos _ _).mpr (by linarith)
  have hstep2 : (δ : ℝ) ^ ((c : ℝ) / (M : ℝ)) ≤ (δ : ℝ) ^ (((b : ℝ) - 1) / (M : ℝ)) :=
    (rpow_div_le_rpow_div_iff (N := M) hδ hd1R hMpos _ _).mpr hbcR
  have hcoe : (gridScale δ M c : ℝ) = (δ : ℝ) ^ ((c : ℝ) / (M : ℝ)) :=
    NNReal.coe_rpow δ ((c : ℝ) / (M : ℝ))
  have hposScale : 0 < (δ : ℝ) ^ (1 / (M : ℝ)) := Real.rpow_pos_of_pos hdR _
  have hind : (δ : ℝ) ^ (1 / (M : ℝ)) ≤ (16 : ℝ)⁻¹ := by
    have hδ16R : (δ : ℝ) ≤ (16 : ℝ) ^ (-(M : ℝ)) := by
      have h := NNReal.coe_le_coe.mpr hδ16
      rwa [NNReal.coe_rpow, NNReal.coe_ofNat] at h
    calc (δ : ℝ) ^ (1 / (M : ℝ)) ≤ ((16 : ℝ) ^ (-(M : ℝ))) ^ (1 / (M : ℝ)) :=
          Real.rpow_le_rpow hδnonneg hδ16R (one_div_nonneg.mpr hMR.le)
      _ = (16 : ℝ)⁻¹ := by
          rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 16),
            show (-(M : ℝ)) * (1 / (M : ℝ)) = -1 by
              rw [mul_one_div, neg_div, div_self hMne]]
          exact Real.rpow_neg_one 16
  have ht16 : (16 : ℝ) ≤ (δ : ℝ) ^ ((-1 : ℝ) / (M : ℝ)) := by
    rw [neg_div, Real.rpow_neg hδnonneg]
    exact (le_inv_comm₀ hposScale (by norm_num : (0 : ℝ) < 16)).mp hind
  have hgap : (32 : ℝ) * (δ : ℝ) ^ (((b : ℝ) - 1) / (M : ℝ)) ≤
      (δ : ℝ) ^ (((b : ℝ) - 3) / (M : ℝ)) := by
    have hsq : (32 : ℝ) ≤ ((δ : ℝ) ^ ((-1 : ℝ) / (M : ℝ))) ^ (2 : ℕ) :=
      le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 16) ht16 2)
    rw [show (δ : ℝ) ^ (((b : ℝ) - 3) / (M : ℝ)) =
        (δ : ℝ) ^ (((b : ℝ) - 1) / (M : ℝ)) * ((δ : ℝ) ^ ((-1 : ℝ) / (M : ℝ))) ^ (2 : ℕ) by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hδnonneg, ← Real.rpow_add hdR]
      congr 1
      push_cast
      ring]
    exact (mul_le_mul_of_nonneg_right hsq (Real.rpow_pos_of_pos hdR _).le).trans_eq (mul_comm _ _)
  have hc32 : 32 * (gridScale δ M c : ℝ) ≤ (ρ : ℝ) := by
    rw [hcoe]
    exact ((mul_le_mul_of_nonneg_left hstep2 (by norm_num)).trans hgap).trans (hstep1.trans hwin)
  have hc2 : 2 * δ ≤ gridScale δ M c := by
    have h16 := sixteen_mul_gridScale_le (N := M) (a := c) (b := M) hδ hδ1 hδ16 hcM le_rfl
    rw [gridScale_self δ hMpos] at h16
    exact (mul_le_mul_of_nonneg_right (by norm_num : (2 : NNReal) ≤ 16) hδ.le).trans h16
  exact ⟨c, hcbb, hcbM, hc2, NNReal.coe_le_coe.mp hc32⟩

open scoped Classical in
/-- **Rounding a window scale to the grid index just below it** (blueprint
`lem:bullet3WindowRoundSharpA`).  `Kakeya.MultiScaleFac.A.exists_round_index` produces *some*
admissible index, but the packing count displays `(4ρ/σ_c)^{2n}`; taking the *coarsest* admissible
index — the least `c` with `32 σ_c ≤ ρ` — keeps `ρ/σ_c` inside a single grid step, making the count
a `Kakeya.MultiScaleFac.scaleGapLoss (2n) δ` up to an absolute constant. -/
theorem A.exists_round_index_sharp {δ : NNReal} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδlt : δ < 1)
    (hδ16 : δ ≤ (16 : NNReal) ^ (-(ssfGridLen δ : ℝ))) (hM : 0 < ssfGridLen δ)
    {ε : ℝ} {a b : ℕ} (hab : a < b) (hbM : b ≤ ssfGridLen δ)
    (hεba : 3 ≤ ε * ((b : ℝ) - (a : ℝ))) {ρ : NNReal} (hρ1 : ρ ≤ 1)
    (hlo : (gridScale δ (ssfGridLen δ) b : ℝ)
        * ((gridScale δ (ssfGridLen δ) a : ℝ)
            / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ ε ≤ (ρ : ℝ)) :
    ∃ c : ℕ, c ≤ b ∧ c ≤ ssfGridLen δ ∧
      2 * δ ≤ gridScale δ (ssfGridLen δ) c ∧
      32 * gridScale δ (ssfGridLen δ) c ≤ ρ ∧
      (ρ : ℝ) ≤ 32 * scaleGapLoss 1 δ * (gridScale δ (ssfGridLen δ) c : ℝ) := by
  obtain ⟨c₀, hc₀b, hc₀M, hc₀d, hc₀r⟩ :=
    MultiScaleFac.A.exists_round_index hδ hδ1 hδlt hδ16 hM hab hbM hεba hlo
  have hex : ∃ k : ℕ, 32 * gridScale δ (ssfGridLen δ) k ≤ ρ := ⟨c₀, hc₀r⟩
  have hcle : Nat.find hex ≤ c₀ := Nat.find_le hc₀r
  have hdR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  refine ⟨Nat.find hex, hcle.trans hc₀b, hcle.trans hc₀M,
    hc₀d.trans (gridScale_antitone hδ hδ1 (ssfGridLen δ) hcle), Nat.find_spec hex, ?_⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with hz | hp
  · have hr1 : (ρ : ℝ) ≤ 1 := by exact_mod_cast hρ1
    rw [hz, gridScale_zero]
    push_cast
    linarith [one_le_scaleGapLoss 1 hδ hδ1]
  · obtain ⟨d, hd⟩ : ∃ d, Nat.find hex = d + 1 := ⟨Nat.find hex - 1, by omega⟩
    have hlt : (ρ : ℝ) ≤ 32 * (gridScale δ (ssfGridLen δ) d : ℝ) := by
      exact_mod_cast (not_le.mp (Nat.find_min hex (by omega : d < Nat.find hex))).le
    have hstepEq :
        (gridScale δ (ssfGridLen δ) d : ℝ)
          = scaleGapLoss 1 δ * (gridScale δ (ssfGridLen δ) (d + 1) : ℝ) := by
      unfold gridScale scaleGapLoss
      rw [NNReal.coe_rpow, NNReal.coe_rpow, ← Real.rpow_add hdR]
      congr 1
      push_cast
      ring
    rw [hstepEq, ← mul_assoc] at hlt
    rwa [hd]

end MultiScaleFac
end Kakeya

end
