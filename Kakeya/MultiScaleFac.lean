/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.MultiScaleFac.Band
public import Kakeya.MultiScaleFac.BulletThree
public import Kakeya.MultiScaleFac.BulletThreeKT
public import Kakeya.MultiScaleFac.GapsA
public import Kakeya.MultiScaleFac.GapsKT
public import Kakeya.MultiScaleFac.Loss
public import Kakeya.MultiScaleLoss
public import Kakeya.Sticky

/-!
# GWZ Lemma 7.7, the dividing-scales dichotomy

The two statements that Sections 8 and 9 consume.  Only the statements are here; the machinery
they are assembled from is `Kakeya/MultiScaleFac/`.

Three conventions are shared by both halves.  The hierarchy is carried on GWZ's own grid of length
`Tube.ssfGridLen δ = ⌈log log 1/δ⌉`, leaving `N` its single role of bounding the number of
stopping-time steps.  Every loss is the displayed `StickyKakeya.totalLoss`, absorbed by the consumer
at whatever accuracy it can afford (`StickyKakeya.exists_threshold_totalLoss_le`).  And every bullet
of alternative (ii) is universal and computed in the returned hierarchy: the upper bounds at the
grid indices of a block `a < b`, the lower bound at every real scale `ρ` in the window.  The halves
take that last bullet in opposite directions — (A) fixes the fine family and runs the container over
the concentric `ρ`-rescales of a level-`b` node, GWZ's `T_ρ ∈ 𝕋_ρ` and not an arbitrary container,
against which it would be false (blueprint `note:ssfIsolatedFineNode`); (B) fixes the coarse node
and runs the family over `ρ` — which the inheritance asymmetry of GWZ Remark 3.3 forces rather than
merely suggests.

## Two forms of (A), and which one to consume

`StickyKakeya.dividingScalesFrostman_unbundled` is the statement as the proof produces it, with
alternative (ii) spelled out as a chain of conjunctions.  `StickyKakeya.dividingScalesFrostman` is
the same theorem with that chain bundled into the named predicate
`StickyKakeya.IsFrostmanDividingBlock`, and is derived from the unbundled form by
destructuring alone — the two can therefore never drift apart.  Section 8 consumes the bundled
form: it names the predicate in its own hypotheses instead of transcribing the conjunction, and
reads the individual bullets through the structure's field names.

(B) is left unbundled; nothing yet consumes it through a named predicate.
-/

@[expose] public section

open MeasureTheory Real Metric
open scoped Topology
open Tube
open Kakeya.StickyKakeya
open Kakeya.MultiScaleFac

universe u

namespace StickyKakeya

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

/-- **Alternative (ii) of GWZ Lemma 7.7(A), as a named predicate** (blueprint
`dividingScalesLemmaA`, Conclusion (ii)).

This is *literally* the second disjunct of `StickyKakeya.dividingScalesFrostman_unbundled`,
extracted so that the consumers in Section 8 can name it instead of transcribing it; the bundled
form of the dichotomy, `StickyKakeya.dividingScalesFrostman`, is obtained from the unbundled one by
destructuring alone, so the two cannot drift apart.  `𝒰'` is the hierarchy the dichotomy returns,
`a < b ≤ ssfGridLen δ` are the two grid indices of the block (`a` the coarse end, `b` the fine end)
and `m < N` is the exponent index.  `Cb` is the constant of the three bounds, `K` the
polylogarithmic exponent and `c` the grid-gap exponent; the dichotomy instantiates `Cb` at the same
constant `C` that governs the hierarchy, but a consumer holding an already-absorbed constant may
use a different one.

**Everything is computed in `𝒰'`.**  The classes and node families are those of the returned
hierarchy, never of the input family.

**The losses are subpolynomial.**  All three bounds carry `StickyKakeya.totalLoss Cb K c δ`,
which covers both the per-level re-uniformizations and the transports across grid gaps, and
which a consumer may absorb into a `∀ᶠ δ in 𝓝[>] 0` at any fixed power it can afford
(`StickyKakeya.exists_threshold_totalLoss_le`).

**The container of the lower bound is the concentric rescale.**  It is GWZ's `T_ρ ∈ 𝕋_ρ`, not an
arbitrary `ρ`-tube containing the node: read against an arbitrary container the bullet is false,
since a container meeting a single level-`b` node pins the Frostman constant to `O(1)` against a
left-hand side that is a genuine power of `δ⁻¹` (blueprint `note:ssfIsolatedFineNode`).  The
arbitrary-container reading §8 consumes is a consequence of this sharper one, obtained by enlarging
the container at the cost of a further `scaleGapLoss` factor, so nothing is lost by stating the
sharper form here.

`N` is not the grid length; the hierarchy lives on the grid of length `ssfGridLen δ`, and `N`
bounds the exponent index `m` alone. -/
structure IsFrostmanDividingBlock {ι : Type u} {δ : NNReal} {s' : Finset ι} {T : ι → Tube δ E}
    {C : NNReal} (𝒰' : UniformTubeSet s' T (ssfGridLen δ) C) (Cb : NNReal) (K c : ℕ) (η : ℕ → ℝ)
    (ε : ℝ) (a b m N : ℕ) : Prop where
  /-- The exponent index lies in the ladder. -/
  exponent_lt : m < N
  /-- The block runs from the coarse index `a` to the strictly finer index `b`. -/
  coarse_lt_fine : a < b
  /-- The fine index is a grid index of the `⌈log log 1/δ⌉`-grid. -/
  fine_le : b ≤ ssfGridLen δ
  /-- The two ends of the block are separated by at least `δ ^ ε`. -/
  separated : (gridScale δ (ssfGridLen δ) b : ℝ)
    ≤ (δ : ℝ) ^ ε * (gridScale δ (ssfGridLen δ) a : ℝ)
  /-- First bullet: the leaves assigned to a fine node are Frostman in it. -/
  frostman_leaves : ∀ j ∈ 𝒰'.cover.indexSet b,
    ConvexSpaceBody.frostmanConstant (coverClass s' (𝒰'.cover.assign b) j)
        (fun i => (T i).toConvexSpaceBody) (𝒰'.cover.tube b j).toConvexSpaceBody
      ≤ (Cb : ENNReal) * totalLoss Cb K c δ *
          ENNReal.ofReal (((gridScale δ (ssfGridLen δ) b : ℝ) / (δ : ℝ)) ^ η m)
  /-- Second bullet: the fine nodes under a coarse node are Frostman in it. -/
  frostman_nodes : ∀ j ∈ 𝒰'.cover.indexSet a,
    ConvexSpaceBody.frostmanConstant (𝒰'.nodesUnder b a j)
        (fun j' => (𝒰'.cover.tube b j').toConvexSpaceBody)
        (𝒰'.cover.tube a j).toConvexSpaceBody
      ≤ (Cb : ENNReal) * totalLoss Cb K c δ *
          ENNReal.ofReal (((gridScale δ (ssfGridLen δ) a : ℝ)
            / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ η m)
  /-- Third bullet: at every real scale `ρ` of the `ε`-window and at *every* node of level `b`,
  the matching lower bound holds inside the concentric `ρ`-rescale of that node, with the
  subpolynomial loss `StickyKakeya.totalLoss`. -/
  frostman_lower : ∀ ρ : NNReal,
    (gridScale δ (ssfGridLen δ) b : ℝ)
        * ((gridScale δ (ssfGridLen δ) a : ℝ)
            / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ ε ≤ (ρ : ℝ) →
    (ρ : ℝ) ≤ (gridScale δ (ssfGridLen δ) a : ℝ)
        * ((gridScale δ (ssfGridLen δ) b : ℝ)
            / (gridScale δ (ssfGridLen δ) a : ℝ)) ^ ε →
    ∀ j ∈ 𝒰'.cover.indexSet b,
      ENNReal.ofReal (((ρ : ℝ) / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ η (m + 1))
        ≤ (Cb : ENNReal) * totalLoss Cb K c δ *
            ConvexSpaceBody.frostmanConstant
              (𝒰'.nodesIn b ((𝒰'.cover.tube b j).rescale ρ).toConvexSpaceBody)
              (fun j' => (𝒰'.cover.tube b j').toConvexSpaceBody)
              ((𝒰'.cover.tube b j).rescale ρ).toConvexSpaceBody
/-- **GWZ Lemma 7.7(A), unbundled** (blueprint `dividingScalesLemmaA`).

For `N ≥ 4096`, `ε = 1/√N` and a geometrically growing `η`: an essentially distinct family of
`δ`-tubes in `B_1` with `C_F(𝕋, B_1) ≤ δ^{-η₀}`, uniform on the grid of length `ssfGridLen δ`, has a
subfamily retaining all but a `totalLoss` share that is either Frostman at every scale, or Frostman
on the nodes of some block `a < b` at exponent `η_m`, with the matching `η_{m+1}` lower bound at
every real scale in the window.

This is the shape the proof produces, with alternative (ii) written out as a chain of conjunctions.
Consumers should take `StickyKakeya.dividingScalesFrostman` instead, which is this statement with
that chain bundled into `StickyKakeya.IsFrostmanDividingBlock`. -/
theorem dividingScalesFrostman_unbundled (hn : Module.finrank ℝ E = 3)
    (N : ℕ) (hN : 4096 ≤ N) {ε : ℝ} (hε : ε = 1 / Real.sqrt (N : ℝ)) (Cu : NNReal) :
    ∃ (C δ₀ : NNReal) (K c : ℕ), 1 ≤ C ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → δ ≤ δ₀ →
      ∀ (η : ℕ → ℝ), 0 ≤ η 0 → (∀ k < N, η k ≤ ε * η (k + 1)) → η N ≤ ε →
      ∀ (s : Finset ι) (T : ι → Tube δ E),
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      (s : Set ι).Pairwise (fun i j ↦ IsEssentiallyDistinct ((T i).carrier) ((T j).carrier)) →
      UniformTubeSet s T (ssfGridLen δ) Cu →
      ConvexSpaceBody.frostmanConstant s (fun i => (T i).toConvexSpaceBody)
          ConvexSpaceBody.closedUnitBall
          ≤ ENNReal.ofReal ((δ : ℝ) ^ (-η 0)) →
      ∃ s' ⊆ s,
        (s.card : ENNReal) ≤ totalLoss C K c δ * (s'.card : ENNReal) ∧
        ∃ 𝒰' : UniformTubeSet s' T (ssfGridLen δ) C,
          𝒰'.Nice ∧
          ((_root_.Kakeya.StickyKakeya.IsFrostmanAtEveryScale s' T
                  ((C : ENNReal) * totalLoss C K c δ
                    * ENNReal.ofReal ((δ : ℝ) ^ (-(5 * ε)))) ∧
                𝒰'.IsFrostmanAtEveryScale
                  ((C : ENNReal) * totalLoss C K c δ
                    * ENNReal.ofReal ((δ : ℝ) ^ (-(5 * ε))))) ∨
            ∃ a b m : ℕ,
              m < N ∧ a < b ∧ b ≤ ssfGridLen δ ∧
              ((gridScale δ (ssfGridLen δ) b : ℝ)
                ≤ (δ : ℝ) ^ ε * (gridScale δ (ssfGridLen δ) a : ℝ)) ∧
              (∀ j ∈ 𝒰'.cover.indexSet b,
                ConvexSpaceBody.frostmanConstant
                    (coverClass s' (𝒰'.cover.assign b) j)
                    (fun i => (T i).toConvexSpaceBody)
                    (𝒰'.cover.tube b j).toConvexSpaceBody
                  ≤ (C : ENNReal) * totalLoss C K c δ *
                      ENNReal.ofReal
                        (((gridScale δ (ssfGridLen δ) b : ℝ) / (δ : ℝ)) ^ η m)) ∧
              (∀ j ∈ 𝒰'.cover.indexSet a,
                ConvexSpaceBody.frostmanConstant (𝒰'.nodesUnder b a j)
                    (fun j' => (𝒰'.cover.tube b j').toConvexSpaceBody)
                    (𝒰'.cover.tube a j).toConvexSpaceBody
                  ≤ (C : ENNReal) * totalLoss C K c δ *
                      ENNReal.ofReal
                        (((gridScale δ (ssfGridLen δ) a : ℝ)
                            / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ η m)) ∧
              (∀ ρ : NNReal,
                (gridScale δ (ssfGridLen δ) b : ℝ)
                    * ((gridScale δ (ssfGridLen δ) a : ℝ)
                        / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ ε ≤ (ρ : ℝ) →
                (ρ : ℝ) ≤ (gridScale δ (ssfGridLen δ) a : ℝ)
                    * ((gridScale δ (ssfGridLen δ) b : ℝ)
                        / (gridScale δ (ssfGridLen δ) a : ℝ)) ^ ε →
                ∀ j ∈ 𝒰'.cover.indexSet b,
                  ENNReal.ofReal
                      (((ρ : ℝ) / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ η (m + 1))
                    ≤ (C : ENNReal) * totalLoss C K c δ *
                        ConvexSpaceBody.frostmanConstant
                          (𝒰'.nodesIn b ((𝒰'.cover.tube b j).rescale ρ).toConvexSpaceBody)
                          (fun j' => (𝒰'.cover.tube b j').toConvexSpaceBody)
                          ((𝒰'.cover.tube b j).rescale ρ).toConvexSpaceBody)) := by
  classical
  have hNpos : 0 < N := by omega
  have hεpos : 0 < ε := eps_pos_of_eq_one_div_sqrt (by omega : 16 ≤ N) hε
  have hε64 : ε ≤ 1 / 64 := eps_le_one_div_64_of_eq_one_div_sqrt hN hε
  have hε1 : ε ≤ 1 := by linarith
  obtain ⟨Ast, _Apass, Ka, K₁, _Kpass, Cv, C₁, δst, hAst1, _hApass1, hCv1, hC₁1, hδstpos,
      _hδstle1, HSTOP⟩ :=
    exists_maximal_cuts_banded_hoisted_selfBand.{u, _} (E := E) hn
  have hCvCq : Cv ≤ uniformTubeSetCuOf (E := E) Cv := le_uniformTubeSetCuOf Cv
  have hCq1 : (1 : NNReal) ≤ uniformTubeSetCuOf (E := E) Cv := le_trans hCv1 hCvCq
  have hC₁1R : (1 : ℝ) ≤ (C₁ : ℝ) := NNReal.one_le_coe.mpr hC₁1
  obtain ⟨B₀, Kb₀, hB₀1, hCqB₀, HG0⟩ :=
    alternativeOne_of_cuts.{u, _} (E := E) hn N hN hε (uniformTubeSetCuOf (E := E) Cv) C₁
      hCq1 hC₁1 (3 + (N + 1) * (3 * K₁)) 2
  obtain ⟨B₁, Kb₁, hB₁1, hCqB₁, hKgB₁, HG1⟩ :=
    bulletOne_of_cuts.{u, _} (E := E) hn N (uniformTubeSetCuOf (E := E) Cv) C₁ hCq1 hC₁1
      (3 + (N + 1) * (3 * K₁)) 2
  obtain ⟨B₂, Kb₂, hB₂1, hCqB₂, hKgB₂, HG2⟩ :=
    bulletTwo_of_blockFrostman.{u, _} (E := E) hn (uniformTubeSetCuOf (E := E) Cv) C₁ hCq1
      hC₁1 (3 + (N + 1) * (3 * K₁)) 2
  obtain ⟨C₂, hC₂1, HALT2⟩ :=
    alternative_two_of_terminal_block_sharp.{u, _} (E := E) hn
      (uniformTubeSetCuOf (E := E) Cv) hCq1
  obtain ⟨B₃, Kb₃, cB₃, hB₃1, _hCvB₃, hKgB₃, hcB₃, HG3⟩ :=
    bulletThree_of_alternativeTwo_banded.{u, _} (E := E) hn N
      Cv C₁ C₂ B₂ hCv1 hC₁1 hC₂1 hB₂1 (3 + (N + 1) * (3 * K₁)) 2 Kb₂
      hεpos hε64 hN hε
  obtain ⟨Cbig, hCbig1, hB₀C, hB₁C, hB₂C, hB₃C, hCqC⟩ :=
    exists_common_const B₀ B₁ B₂ B₃ (uniformTubeSetCuOf (E := E) Cv) hCq1
  obtain ⟨Kbig, hK₀K, hK₁K, hK₂K, hK₃K, hKaK⟩ :=
    exists_common_deg Kb₀ Kb₁ Kb₂ Kb₃ (3 + (N + 1) * (3 * Ka))
  obtain ⟨δ₁, hδ₁pos, hδ₁le1, HTHR1⟩ := exists_threshold_ssfGridLen_hypotheses (3 * N) hεpos
  obtain ⟨δ₂, hδ₂pos, hδ₂le1, HTHR2⟩ :=
    exists_threshold_selfBandStoppingLoss_le_gridLoss hAst1 Ka N hCbig1
  obtain ⟨δ₃, hδ₃pos, hδ₃le1, HTHR3⟩ :=
    exists_threshold_selfBandStoppingLoss_le_gridLoss hC₁1R K₁ N hC₁1
  obtain ⟨δ₄, hδ₄pos, hδ₄le1, he₁, he₂, he₃⟩ :=
    exists_common_threshold hδ₁pos hδ₁le1 hδ₂pos hδ₃pos
  obtain ⟨δ₀, hδ₀pos, hδ₀le1, hd₄', hd₄, _hd₄''⟩ :=
    exists_common_threshold hδ₄pos hδ₄le1 hδstpos hδstpos
  have hd₁ : δ₀ ≤ δ₁ := le_trans hd₄' he₁
  have hd₂ : δ₀ ≤ δ₂ := le_trans hd₄' he₂
  have hd₃ : δ₀ ≤ δ₃ := le_trans hd₄' he₃
  refine ⟨Cbig, δ₀, Kbig, cB₃, hCbig1, hδ₀pos, hδ₀le1, ?_⟩
  intro ι δ hδpos hδδ₀ η hη0 hηgap hηN s T hball hED _hU hFrost
  have hδ₁' : δ ≤ δ₁ := le_trans hδδ₀ hd₁
  have hδ₂' : δ ≤ δ₂ := le_trans hδδ₀ hd₂
  have hδ₃' : δ ≤ δ₃ := le_trans hδδ₀ hd₃
  have hδst' : δ ≤ δst := le_trans hδδ₀ hd₄
  have hδ1 : δ ≤ 1 := le_trans hδδ₀ hδ₀le1
  have hδ1R : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1
  obtain ⟨h16M, hNM3, hεM, hδ16⟩ := HTHR1 hδpos hδ₁'
  have hMpos : 0 < ssfGridLen δ := by omega
  have hFrost' : ConvexSpaceBody.frostmanConstant s (fibreBodies T δ)
      ConvexSpaceBody.closedUnitBall ≤ ENNReal.ofReal ((δ : ℝ) ^ (-η 0)) := by
    rw [fibreBodies_self]
    exact hFrost
  obtain ⟨S, m, L, Ct, tL, hm, hLN, hLM, hCt1, hCtub, htLs, hcardstop, _hGU, hCF, _hCFI, hband,
    h0S, hMS, hSsub, hScard, hunit, hAll⟩ :=
    HSTOP N hN hε (ssfGridLen δ) h16M hδpos hδst' hδ1R hδ16 s T hball hED η hη0 hηgap hηN hFrost'
  obtain ⟨𝒢, Φ, hPBO, _hBS⟩ := hband
  have htLball : ∀ i ∈ tL, (T i).carrier ⊆ Metric.closedBall (0 : E) 1 :=
    fun i hi => hball i (htLs hi)
  have hCtG : (Ct : ENNReal) ≤ ENNReal.ofReal (gridLoss C₁ (3 + (N + 1) * (3 * K₁)) δ) :=
    selfBand_ct_le_gridLoss hδ1 (HTHR3 δ hδpos hδ₃' (ssfGridLen δ) L le_rfl hLN hLM) hCtub
  refine ⟨tL, htLs, ?_, (𝒢.toUniformTubeSet).mono hCqC,
    (fun k hk V => (𝒢.nice k hk).2 V), ?_⟩
  · exact natCast_le_mul_natCast_of_ofReal_natCast_le
      (selfBand_card_le_totalLoss hδpos hδ1 hCbig1 hKaK
        (HTHR2 δ hδpos hδ₂' (ssfGridLen δ) L le_rfl hLN hLM) (Nat.cast_nonneg _) hcardstop)
  by_cases htL : tL.Nonempty
  case neg =>
    exact Or.inl ⟨Kakeya.MultiScaleFac.leaf_isFrostmanAtEveryScale_of_not_nonempty htL _,
      isFrostmanAtEveryScale_of_not_nonempty _ htL _⟩
  by_cases hlongex : ∃ a ∈ S, ∃ b ∈ S, a < b ∧ (∀ x ∈ S, ¬(a < x ∧ x < b)) ∧
      IsLongBlock (ssfGridLen δ) ε a b
  case neg =>
    refine Or.inl ?_
    have hshort : ∀ a ∈ S, ∀ b ∈ S, a < b → (∀ x ∈ S, ¬(a < x ∧ x < b)) →
        BlockFrostman tL T (ssfGridLen δ) Ct (η m) a b ∧
          ¬ IsLongBlock (ssfGridLen δ) ε a b := by
      intro a haS b hbS hab hadj
      refine ⟨(hAll a haS b hbS hab hadj).1, fun hL => ?_⟩
      exact hlongex ⟨a, haS, b, hbS, hab, hadj, hL⟩
    have hG0 :=
      HG0 hδpos hδ1 hδ16 h16M hεM tL T htL htLball (𝒢.toUniformTubeSet) (hCF.mono hCvCq)
        Ct hCt1 hCtG η m hm hη0 hηgap hηN S h0S hMS hSsub hScard hshort hunit
    have hraise := (mul_le_mul_left
      (Kakeya.MultiScaleFac.loss_raise hB₀1 hB₀C hK₀K hcB₃ hδpos hδ1)
      (ENNReal.ofReal ((δ : ℝ) ^ (-(5 * ε)))))
    exact ⟨_root_.Kakeya.StickyKakeya.IsFrostmanAtEveryScale.mono_constant hG0.1 hraise,
      UniformTubeSet.IsFrostmanAtEveryScale.mono hG0.2 hraise⟩
  case pos =>
    obtain ⟨a, haS, b, hbS, hab, hadj, hlong⟩ := hlongex
    have hbM : b ≤ ssfGridLen δ := Nat.lt_succ_iff.mp (Finset.mem_range.mp (hSsub hbS))
    have hblock : BlockFrostman tL T (ssfGridLen δ) Ct (η m) a b :=
      (hAll a haS b hbS hab hadj).1
    have hnotpass :
        ¬ (tL.card ≤ 2 * (passingNodes tL T (ssfGridLen δ) Ct ε (η (m + 1)) a b).card) :=
      Or.resolve_left (hAll a haS b hbS hab hadj).2 (not_not_intro hlong)
    have hηm : 0 ≤ η m := eta_nonneg_of_gap N hNpos hε η hη0 hηgap m (le_of_lt hm)
    have hηgapm : η m ≤ ε * η (m + 1) := hηgap m hm
    have hηm1 : η (m + 1) ≤ ε := eta_succ_le_eps hNpos hε η hη0 hηgap hηN hm
    obtain ⟨F, hFsub, hFcard, hsep, hlow⟩ :=
      HALT2 (ssfGridLen δ) N h16M hNpos (three_mul_cast_le hNM3) hε
        (kappa_pos hNpos hMpos) (le_kappa_mul hMpos) hδpos
        (delta_lt_one hδpos h16M hδ16) hδ16 tL T htLball
        (𝒢.toUniformTubeSet) Ct hCt1 η m hηm hηgapm hηm1 a b hab hbM hlong hnotpass
    have hbul2raw : ∀ j ∈ (𝒢.toUniformTubeSet).cover.indexSet a,
        ConvexSpaceBody.frostmanConstant ((𝒢.toUniformTubeSet).nodesUnder b a j)
            (fun j' => ((𝒢.toUniformTubeSet).cover.tube b j').toConvexSpaceBody)
            ((𝒢.toUniformTubeSet).cover.tube a j).toConvexSpaceBody
          ≤ (B₂ : ENNReal) * totalLoss B₂ Kb₂ 2 δ *
              ENNReal.ofReal (((gridScale δ (ssfGridLen δ) a : ℝ)
                  / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ η m) := by
      intro j hj
      exact HG2 hδpos hδ1 hδ16 hMpos tL T htL (𝒢.toUniformTubeSet) Ct hCtG (η m) hηm a b hab hbM
        hblock j hj
    have hbul2 : ∀ j ∈ (𝒢.toUniformTubeSet).cover.indexSet a,
        ConvexSpaceBody.frostmanConstant ((𝒢.toUniformTubeSet).nodesUnder b a j)
            (fun j' => ((𝒢.toUniformTubeSet).cover.tube b j').toConvexSpaceBody)
            ((𝒢.toUniformTubeSet).cover.tube a j).toConvexSpaceBody
          ≤ (Cbig : ENNReal) * totalLoss Cbig Kbig cB₃ δ *
              ENNReal.ofReal (((gridScale δ (ssfGridLen δ) a : ℝ)
                  / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ η m) := by
      intro j hj
      exact le_trans (hbul2raw j hj)
        (mul_le_mul_left (Kakeya.MultiScaleFac.loss_raise hB₂1 hB₂C hK₂K hcB₃ hδpos hδ1) _)
    refine Or.inr ⟨a, b, m, hm, hab, hbM, hsep, ?_, hbul2, ?_⟩
    · intro j hj
      exact le_trans
        (HG1 hδpos hδ1 hδ16 hMpos tL T htL htLball (𝒢.toUniformTubeSet) (hCF.mono hCvCq) Ct hCt1
          hCtG (η m) hηm S h0S hMS hSsub (by omega)
          (fun x hx y hy hxy hadj' => (hAll x hx y hy hxy hadj').1) b hbS (by omega) j hj)
        (mul_le_mul_left (Kakeya.MultiScaleFac.loss_raise hB₁1 hB₁C hK₁K hcB₃ hδpos hδ1) _)
    · intro ρ hρl hρr j hj
      exact le_trans
        (HG3 hδpos hδ1 hδ16 h16M hNM3 tL T htL htLball 𝒢 hPBO (η m) (η (m + 1)) hηm
          hηgapm hηm1 a b hab hbM hlong hbul2raw F hFsub hFcard hlow ρ hρl hρr j hj)
        (mul_le_mul_left (Kakeya.MultiScaleFac.loss_raise hB₃1 hB₃C hK₃K le_rfl hδpos hδ1) _)

/-- **GWZ Lemma 7.7(A)** (blueprint `dividingScalesLemmaA`), with alternative (ii) named.

The statement Sections 8 and 9 are written against.  It is
`StickyKakeya.dividingScalesFrostman_unbundled` with the second disjunct replaced by
`StickyKakeya.IsFrostmanDividingBlock`, which is by definition that same conjunction; the proof
below is destructuring and nothing else, so no content is added here and the two forms cannot drift
apart.

What a consumer needs to know:

* **Alternative (i) is returned in both readings, and the leaf one is the useful one.**  The
  conjunct `StickyKakeya.IsFrostmanAtEveryScale s' T …` is the leaf-anchored condition at every
  *real* scale in `[δ, 1]`; the conjunct `𝒰'.IsFrostmanAtEveryScale …` is its node-anchored image
  on the returned hierarchy.  The proof produces the first and derives the second
  (`Kakeya.MultiScaleFac.isFrostmanAtEveryScale_nodes_of_fibre`), so the two are at the same
  displayed constant and cannot drift.  The leaf reading mentions no hierarchy, so a consumer may
  transport it to *any* hierarchy — in particular to a bundle whose uniformity constant is the
  dimension-only `ShadedTube.ssfUniformConst (Module.finrank ℝ E)` — via
  `Kakeya.StickyKakeya.isFrostmanAtEveryScale_nodes_of_ambient_fibre`, at the cost of the
  retention proportion and a `Kakeya.maxDensity` bound on the ambient family.  This is what the
  Section 8 consumers need and what the node reading cannot give them: `C` here is at least
  `Kakeya.MultiScaleFac.comparableCuOf (Kakeya.MultiScaleFac.gridUniformBandConst …)`, hence
  strictly above that cap, so no restatement of this theorem can put `𝒰'` under it.
* **Both alternatives are about a refinement.**  The printed form of Lemma 7.7 asserts its dichotomy
  for the family `𝕋` itself, and in that form it is false — a product family with one exceptional
  slab fibre satisfies neither conclusion.  The repair is to return a subfamily `s' ⊆ s` retaining
  all but a `totalLoss` share, with a fresh hierarchy `𝒰'` on it, and to state the three bullets
  universally in `𝒰'`.  The refinement is what buys the universal quantifiers.
* **Everything is computed in the returned hierarchy.**  In alternative (ii) the classes and node
  families are those of `𝒰'`, never of the input.
* **Both alternatives are stated on nodes, at grid indices.**  A block is a pair of grid indices
  `a < b`, with `a` the coarse end and `b` the fine end; the anchors are nodes of the hierarchy and
  the members are either the leaves assigned to a node or the nodes of a finer level inside it
  (`Tube.UniformTubeSet.nodesUnder`).  No leaf is ever thickened, so no anchor is ever
  inflated, and the separation and window conditions are plain scale inequalities.
* **The loss cannot be replaced by a fixed power of `δ`.**  Each level of the stopping time
  re-uniformizes the retained subfamily and each transport across a grid gap costs a further
  factor; on a grid of length `ssfGridLen δ` both are paid a `δ`-dependent number of times, so the
  exponent of any power absorbing them would grow with `δ`.  `StickyKakeya.totalLoss` is displayed
  instead, and is subpolynomial (`StickyKakeya.exists_threshold_totalLoss_le`), so a consumer
  absorbs it into a `∀ᶠ δ in 𝓝[>] 0` at whatever accuracy it can afford.  The exponent `η m` is
  *not* the place to absorb it, since it may be `0`. -/
theorem dividingScalesFrostman (hn : Module.finrank ℝ E = 3)
    (N : ℕ) (hN : 4096 ≤ N) {ε : ℝ} (hε : ε = 1 / Real.sqrt (N : ℝ)) (Cu : NNReal) :
    ∃ (C δ₀ : NNReal) (K c : ℕ), 1 ≤ C ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → δ ≤ δ₀ →
      ∀ (η : ℕ → ℝ), 0 ≤ η 0 → (∀ k < N, η k ≤ ε * η (k + 1)) → η N ≤ ε →
      ∀ (s : Finset ι) (T : ι → Tube δ E),
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      (s : Set ι).Pairwise (fun i j ↦ IsEssentiallyDistinct ((T i).carrier) ((T j).carrier)) →
      UniformTubeSet s T (ssfGridLen δ) Cu →
      ConvexSpaceBody.frostmanConstant s (fun i => (T i).toConvexSpaceBody)
          ConvexSpaceBody.closedUnitBall
          ≤ ENNReal.ofReal ((δ : ℝ) ^ (-η 0)) →
      ∃ s' ⊆ s,
        (s.card : ENNReal) ≤ totalLoss C K c δ * (s'.card : ENNReal) ∧
        ∃ 𝒰' : UniformTubeSet s' T (ssfGridLen δ) C,
          𝒰'.Nice ∧
          ((_root_.Kakeya.StickyKakeya.IsFrostmanAtEveryScale s' T
                  ((C : ENNReal) * totalLoss C K c δ
                    * ENNReal.ofReal ((δ : ℝ) ^ (-(5 * ε)))) ∧
                𝒰'.IsFrostmanAtEveryScale
                  ((C : ENNReal) * totalLoss C K c δ
                    * ENNReal.ofReal ((δ : ℝ) ^ (-(5 * ε))))) ∨
            ∃ a b m : ℕ, IsFrostmanDividingBlock 𝒰' C K c η ε a b m N) := by
  obtain ⟨C, δ₀, K, c, hC, hδ₀pos, hδ₀le, hmain⟩ :=
    dividingScalesFrostman_unbundled (E := E) hn N hN hε Cu
  refine ⟨C, δ₀, K, c, hC, hδ₀pos, hδ₀le, ?_⟩
  intro ι δ hδpos hδle η hη₀ hηstep hηN s T hball hED hunif hfrost
  obtain ⟨s', hs's, hcard, 𝒰', hnice, halt⟩ :=
    hmain (ι := ι) (δ := δ) hδpos hδle η hη₀ hηstep hηN s T hball hED hunif hfrost
  refine ⟨s', hs's, hcard, 𝒰', hnice, ?_⟩
  rcases halt with hevery | ⟨a, b, m, hm, hab, hb, hsep, hleaves, hnodes, hlower⟩
  · exact Or.inl hevery
  · exact Or.inr ⟨a, b, m, hm, hab, hb, hsep, hleaves, hnodes, hlower⟩

open scoped Classical in
/-- **GWZ Lemma 7.7(B)** (blueprint `dividingScalesLemmaB`).

The Katz–Tao counterpart of `Kakeya.MultiScaleFac.dividingScalesFrostman`: the same dichotomy under
the same hypotheses, with `Kakeya.maxDensity` in place of `C_F` throughout, read on the *node*
families of the hierarchy.  Its third bullet runs opposite to (A)'s. -/
theorem dividingScalesKatzTao (hn : Module.finrank ℝ E = 3)
    (N : ℕ) (hN : 4096 ≤ N) {ε : ℝ} (hε : ε = 1 / Real.sqrt (N : ℝ)) (Cu : NNReal) :
    ∃ (C δ₀ : NNReal) (K c : ℕ), 1 ≤ C ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ {ι : Type u} {δ : NNReal}, 0 < δ → δ ≤ δ₀ →
      ∀ (η : ℕ → ℝ), 0 ≤ η 0 → (∀ k < N, η k ≤ ε * η (k + 1)) → η N ≤ ε →
      ∀ (s : Finset ι) (T : ι → Tube δ E),
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : E) 1) →
      (s : Set ι).Pairwise (fun i j ↦ IsEssentiallyDistinct ((T i).carrier) ((T j).carrier)) →
      UniformTubeSet s T (ssfGridLen δ) Cu →
      Kakeya.maxDensity s (fun i => (T i).toConvexSpaceBody)
          ≤ ENNReal.ofReal ((δ : ℝ) ^ (-η 0)) →
      ∃ s' ⊆ s,
        (s.card : ENNReal) ≤ totalLoss C K c δ * (s'.card : ENNReal) ∧
        ∃ 𝒰' : UniformTubeSet s' T (ssfGridLen δ) C,
          (𝒰'.IsKatzTaoAtEveryScale
                ((C : ENNReal) * totalLoss C K c δ
                  * ENNReal.ofReal ((δ : ℝ) ^ (-(5 * ε)))) ∨
            ∃ a b m : ℕ,
              m < N ∧ a < b ∧ b ≤ ssfGridLen δ ∧
              ((gridScale δ (ssfGridLen δ) b : ℝ)
                ≤ (δ : ℝ) ^ ε * (gridScale δ (ssfGridLen δ) a : ℝ)) ∧
              Kakeya.maxDensity (𝒰'.cover.indexSet a)
                  (fun j => (𝒰'.cover.tube a j).toConvexSpaceBody)
                ≤ (C : ENNReal) * totalLoss C K c δ *
                    ENNReal.ofReal ((gridScale δ (ssfGridLen δ) a : ℝ) ^ (-η m)) ∧
              (∀ j ∈ 𝒰'.cover.indexSet a,
                Kakeya.maxDensity (𝒰'.nodesUnder b a j)
                    (fun j' => (𝒰'.cover.tube b j').toConvexSpaceBody)
                  ≤ (C : ENNReal) * totalLoss C K c δ *
                      ENNReal.ofReal
                        (((gridScale δ (ssfGridLen δ) a : ℝ)
                            / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ η m)) ∧
              (∀ ρ : NNReal,
                (gridScale δ (ssfGridLen δ) b : ℝ)
                    * ((gridScale δ (ssfGridLen δ) a : ℝ)
                        / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ ε ≤ (ρ : ℝ) →
                (ρ : ℝ) ≤ (gridScale δ (ssfGridLen δ) a : ℝ)
                    * ((gridScale δ (ssfGridLen δ) b : ℝ)
                        / (gridScale δ (ssfGridLen δ) a : ℝ)) ^ ε →
                ∀ j ∈ 𝒰'.cover.indexSet a,
                  ENNReal.ofReal
                      (((gridScale δ (ssfGridLen δ) a : ℝ) / (ρ : ℝ)) ^ η (m + 1))
                    ≤ (C : ENNReal) * totalLoss C K c δ *
                        Kakeya.maxDensity (𝒰'.nodesUnder b a j)
                          (fun j' =>
                            ((𝒰'.cover.tube b j').rescale ρ).toConvexSpaceBody)) ∧
              (∀ k : ℕ,
                a + ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ ≤ k → k + ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊ ≤ b →
                ∀ j ∈ 𝒰'.cover.indexSet a,
                  ENNReal.ofReal (((gridScale δ (ssfGridLen δ) a : ℝ)
                      / (gridScale δ (ssfGridLen δ) k : ℝ)) ^ η (m + 1))
                    ≤ (C : ENNReal) * totalLoss C K c δ *
                        Kakeya.maxDensity (𝒰'.nodesUnder k a j)
                          (fun j' => (𝒰'.cover.tube k j').toConvexSpaceBody)) ∧
              (∃ Φ : ℕ → ℕ → ENNReal, ∀ p ≤ ssfGridLen δ, ∀ k ≤ ssfGridLen δ,
                ∀ j ∈ 𝒰'.cover.indexSet p,
                Φ p k ≤ Kakeya.maxDensity
                    ((coverClass s' (𝒰'.cover.assign p) j).image (𝒰'.cover.assign k))
                    (fun j' => (𝒰'.cover.tube k j').toConvexSpaceBody) ∧
                  Kakeya.maxDensity
                    ((coverClass s' (𝒰'.cover.assign p) j).image (𝒰'.cover.assign k))
                    (fun j' => (𝒰'.cover.tube k j').toConvexSpaceBody)
                    ≤ (C : ENNReal) * totalLoss C K c δ * Φ p k)) := by
  classical
  have hNpos : 0 < N := Nat.lt_of_lt_of_le (by decide) hN
  have hepspos : 0 < ε := eps_pos_of_eq_one_div_sqrt (Nat.le_trans (by decide) hN) hε
  have heps64 : ε ≤ 1 / 64 := eps_le_one_div_64_of_eq_one_div_sqrt hN hε
  have heps1 : ε ≤ 1 := heps64.trans (by norm_num)
  obtain ⟨Cv, C1, hCv1, hC11, hcuts⟩ := exists_maximal_cutsKT_hoisted_blocks hn
  obtain ⟨Cl, δb, Kt, cg, hCl1, hδbpos, hδble1, hstop⟩ := hcuts N hN
  obtain ⟨B0, K0, c0, hB01, hC1B0, hG0⟩ := alternativeOneKT_of_cutsKT hn Cv C1 hCv1 hC11
  obtain ⟨B2, K2, c2, hB21, hC1B2, hG2⟩ := alternativeTwoKT_of_terminal_block hn Cv C1 hCv1 hC11
  let C3 : NNReal := max 1 (KT.gapDensityConstCmp (E := E))
  let cL3 : ℕ := 2 + 4 * Module.finrank ℝ E
  have hC31 : 1 ≤ C3 := le_max_left 1 (KT.gapDensityConstCmp (E := E))
  have hC3cmp : KT.gapDensityConstCmp (E := E) ≤ C3 := le_max_right _ _
  let Cu0 : NNReal := uniformTubeSetCuOf (E := E) Cv
  have hCu01 : 1 ≤ Cu0 := hCv1.trans (le_uniformTubeSetCuOf Cv)
  obtain ⟨Kn, hKn1, hNB⟩ := exists_coarseNeighbours.{u, _} (E := E) Cu0 hCu01
  obtain ⟨d1, hd1pos, hd1le, hd1prop⟩ := exists_threshold_ssfGridLen_hypotheses N hepspos
  obtain ⟨Cbig, hCbig1, hB0Cbig, hB2Cbig, hPCbig, hClCbig, hCvCbig⟩ :=
    KT.exists_common_const B0 B2 ((Kn : NNReal) * C1 * B2 * C3) Cl Cu0 hCu01
  obtain ⟨Kbig, hK0Kbig, hK2Kbig, _, hKtKbig, _⟩ := KT.exists_common_deg K0 K2 K2 Kt 0
  obtain ⟨cbig, hc0cbig, hc2cbig, hc2cL3cbig, hcgcbig, _⟩ :=
    KT.exists_common_deg c0 c2 (c2 + cL3) cg 0
  obtain ⟨δ0, hδ0pos, hδ0le1, hδ0d1, hδ0δb, _⟩ :=
    KT.exists_common_threshold hd1pos hd1le hδbpos hδbpos
  refine ⟨Cbig, δ0, Kbig, cbig, hCbig1, hδ0pos, hδ0le1, ?_⟩
  intro ι δ hδ hδδ0 η hη0 hηgap hηN s T hball hED hU hDens
  have hδ1 : δ ≤ 1 := hδδ0.trans hδ0le1
  have hδd1 : δ ≤ d1 := hδδ0.trans hδ0d1
  have hδδb : δ ≤ δb := hδδ0.trans hδ0δb
  obtain ⟨h16M, hNM, hMge, hδ16⟩ := hd1prop hδ hδd1
  have hMpos : 0 < ssfGridLen δ := Nat.lt_of_lt_of_le (by decide) h16M
  have hetann : ∀ k ≤ N, 0 ≤ η k := eta_nonneg_of_gap N hNpos hε η hη0 hηgap
  have hetamono : ∀ k l, k ≤ l → l ≤ N → η k ≤ η l := fun k l hkl => by
    induction l, hkl using Nat.le_induction with
    | base => exact fun _ => le_rfl
    | succ n _ ih =>
      exact fun hnN => (ih (Nat.le_of_succ_le hnN)).trans
        ((hηgap n hnN).trans (mul_le_of_le_one_left (hetann (n + 1) hnN) heps1))
  by_cases hsne : s.Nonempty
  · obtain ⟨S, m, tL, 𝒢L, Φ, hmN, htLs, hcard, hS0, hSM, hSrange, hband, hterm⟩ :=
      hstop hε (ssfGridLen δ) h16M hNM hδ hδδb hδ16 le_rfl s T hball hED η hetann hetamono
        hηgap hDens
    have hball' : ∀ i ∈ tL, (T i).carrier ⊆ Metric.closedBall (0 : E) 1 :=
      fun i hi => hball i (htLs hi)
    have htLne : tL.Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero fun hc => hsne.ne_empty
        (by simpa only [hc, Nat.cast_zero, mul_zero, nonpos_iff_eq_zero, Nat.cast_eq_zero,
          Finset.card_eq_zero] using hcard))
    refine ⟨tL, htLs, KT.card_le hδ hδ1 hCl1 hClCbig hKtKbig hcgcbig hcard,
      (𝒢L.toUniformTubeSet).mono hCvCbig, ?_⟩
    by_cases hlongex : ∃ a ∈ S, ∃ b ∈ S, a < b ∧ (∀ x ∈ S, ¬(a < x ∧ x < b)) ∧
        IsLongBlock (ssfGridLen δ) ε a b
    · obtain ⟨a, haS, ⟨b, hbS, hab, hadj, hlong⟩⟩ := hlongex
      have hbM : b ≤ ssfGridLen δ := Nat.lt_succ_iff.mp (Finset.mem_range.mp (hSrange hbS))
      have haM : a ≤ ssfGridLen δ := hab.le.trans hbM
      have ha_lt : a < ssfGridLen δ := hab.trans_le hbM
      have hfail := Or.resolve_left (hterm a haS b hbS hab hadj).2 (not_not_intro hlong)
      have hζ'nn : 0 ≤ η (m + 1) := hetann (m + 1) hmN
      have hζ'1 := (KT.eta_succ_le_eps hNpos hε η hη0 hηgap hηN hmN).trans heps1
      obtain ⟨F, hFsub, hprop, hb1, hb2, hb3⟩ :=
        hG2 N hN hε (ssfGridLen δ) h16M hNM hδ hδ1 hδ16 le_rfl tL T htLne hball' 𝒢L (η m)
          (η (m + 1)) (hetann m hmN.le) hζ'nn S hS0 hSM
          (fun a' ha' b' hb' h' hadj' => (hterm a' ha' b' hb' h' hadj').1)
          a b haS hbS hab hadj hlong hbM hfail
      have hIdxNe : (𝒢L.cover.indexSet a).Nonempty :=
        ⟨_, 𝒢L.cover.assign_mem a haM _ htLne.choose_spec⟩
      have hFne : F.Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero fun hc => hIdxNe.ne_empty
        (by simpa only [hc, Nat.cast_zero, mul_zero, nonpos_iff_eq_zero, Nat.cast_eq_zero,
          Finset.card_eq_zero] using hprop))
      have hsep := gridScale_le_rpow_mul_gridScale_of_isLongBlock hδ hδ1 hMpos hlong
      let m' : ℕ := ⌈ε * ((b : ℝ) - (a : ℝ))⌉₊
      have hmlo : ε * ((b : ℝ) - (a : ℝ)) ≤ (m' : ℝ) := Nat.le_ceil _
      have hmhi : (m' : ℝ) ≤ ε * ((b : ℝ) - (a : ℝ)) + 1 := (Nat.ceil_lt_add_one
        (mul_nonneg hepspos.le (sub_nonneg.mpr (Nat.cast_le.mpr hab.le)))).le
      have h4M : (4 : ℝ) ≤ ε * (ssfGridLen δ : ℝ) := le_of_mul_le_mul_left
        (by linarith only [hMge, heps64] : ε * 4 ≤ ε * (ε * (ssfGridLen δ : ℝ))) hepspos
      have hroom : a + 2 * m' ≤ b :=
        two_mul_ceil_add_le_of_isLongBlock hepspos (heps64.trans (by norm_num)) h4M hbM hlong
      have hnbb := fun (c : ℕ) (hac : a ≤ c) (hcM : c ≤ ssfGridLen δ) =>
        hNB hδ hδ1 𝒢L.toUniformTubeSet htLne hac hcM
          (A.clamp_two_delta_le_gridScale hδ hδ1 hδ16 hMpos ha_lt)
      have hgridAll := KT.hgrid_of_alternativeTwo hδ hδ1 (𝒰 := 𝒢L.toUniformTubeSet) hKn1
        (m' := m') hab hbM hnbb hB21 (hband a haM) hFsub hFne (ζ' := η (m + 1)) hb3
      let D : ENNReal := (Kn : ENNReal) * ((B2 : ENNReal) * totalLoss B2 K2 c2 δ) * (C1 : ENNReal)
      have hbt3 := KT.bulletThreeGen hδ hδ1 (C := C3) hC31 hC3cmp 0 cL3 le_rfl
        (𝒰 := 𝒢L.toUniformTubeSet) htLne (a := a) (b := b) (m' := m') hab hbM hζ'nn hζ'1 hmlo
        hmhi hroom D hgridAll
      have hDeq : D * ((C3 : ENNReal) * totalLoss C3 0 cL3 δ)
          = (((Kn : NNReal) * C1 : NNReal) : ENNReal) * ((B2 : ENNReal) * totalLoss B2 K2 c2 δ)
              * ((C3 : ENNReal) * totalLoss C3 0 cL3 δ) := by
        simp only [D, ENNReal.coe_mul, ENNReal.coe_natCast]; ring
      have hraise := loss_raise hB21 hB2Cbig hK2Kbig hc2cbig hδ hδ1
      have hL3 : (1 : ENNReal) ≤ (C3 : ENNReal) * totalLoss C3 0 cL3 δ :=
        one_le_mul (by exact_mod_cast hC31) (one_le_totalLoss C3 hC31 0 cL3 hδ hδ1)
      refine Or.inr ⟨a, b, m, hmN, hab, hbM, hsep, hb1.trans (mul_le_mul_left hraise _), ?_, ?_,
        ?_, ?_⟩
      · exact fun j hj => (hb2 j hj).trans (mul_le_mul_left hraise _)
      · intro ρ hρlo hρhi j hj
        refine KT.prod_le hδ hδ1 (A := (Kn : NNReal) * C1) (B₁ := B2) (B₂ := C3) (C := Cbig)
          (one_le_mul (Nat.one_le_cast.mpr hKn1) hC11) hB21 hC31 (K₁ := K2) (K₂ := 0)
          (K := Kbig) (c₁ := c2) (c₂ := cL3) (c := cbig) hPCbig
          (le_of_eq_of_le (Nat.add_zero K2) hK2Kbig) hc2cL3cbig ?_
        rw [← hDeq]
        exact hbt3 ρ hρlo hρhi j hj
      · -- the source's level clause: `hgridAll`, threaded out at the common constant
        intro k hk1 hk2 j hj
        refine KT.prod_le hδ hδ1 (A := (Kn : NNReal) * C1) (B₁ := B2) (B₂ := C3) (C := Cbig)
          (one_le_mul (Nat.one_le_cast.mpr hKn1) hC11) hB21 hC31 (K₁ := K2) (K₂ := 0)
          (K := Kbig) (c₁ := c2) (c₂ := cL3) (c := cbig) hPCbig
          (le_of_eq_of_le (Nat.add_zero K2) hK2Kbig) hc2cL3cbig ?_
        rw [← hDeq]
        calc ENNReal.ofReal (((gridScale δ (ssfGridLen δ) a : ℝ)
                / (gridScale δ (ssfGridLen δ) k : ℝ)) ^ η (m + 1))
            ≤ D * Kakeya.maxDensity (𝒢L.toUniformTubeSet.nodesUnder k a j)
                (fun j' => (𝒢L.toUniformTubeSet.cover.tube k j').toConvexSpaceBody) :=
              hgridAll k hk1 hk2 j hj
          _ = D * 1 * Kakeya.maxDensity (𝒢L.toUniformTubeSet.nodesUnder k a j)
                (fun j' => (𝒢L.toUniformTubeSet.cover.tube k j').toConvexSpaceBody) := by
              rw [mul_one]
          _ ≤ D * ((C3 : ENNReal) * totalLoss C3 0 cL3 δ)
                * Kakeya.maxDensity (𝒢L.toUniformTubeSet.nodesUnder k a j)
                  (fun j' => (𝒢L.toUniformTubeSet.cover.tube k j').toConvexSpaceBody) := by
              gcongr
      · -- the two-level homogenization band: `hband`, at the common constant
        refine ⟨Φ, fun p hp k hk j hj => ?_⟩
        obtain ⟨h1, h2⟩ := hband p hp k hk j hj
        refine ⟨h1, h2.trans ?_⟩
        have hC1big : (C1 : ENNReal) ≤ (Cbig : ENNReal) * totalLoss Cbig Kbig cbig δ :=
          calc (C1 : ENNReal) ≤ (Cbig : ENNReal) := by exact_mod_cast hC1B2.trans hB2Cbig
            _ = (Cbig : ENNReal) * 1 := (mul_one _).symm
            _ ≤ (Cbig : ENNReal) * totalLoss Cbig Kbig cbig δ :=
                mul_le_mul_right (one_le_totalLoss Cbig hCbig1 Kbig cbig hδ hδ1) _
        exact mul_le_mul_left hC1big _
    · refine Or.inl ?_
      have hshort : ∀ a ∈ S, ∀ b ∈ S, a < b → (∀ x ∈ S, ¬(a < x ∧ x < b)) →
          BlockKatzTaoOn tL 𝒢L.uniformAt C1 (η m) a b ∧ ¬ IsLongBlock (ssfGridLen δ) ε a b :=
        fun a haS b hbS hab hadj => ⟨(hterm a haS b hbS hab hadj).1,
          fun hL => hlongex ⟨a, haS, b, hbS, hab, hadj, hL⟩⟩
      exact (hG0 N hN hε (ssfGridLen δ) h16M hNM hδ hδ1 hδ16 le_rfl tL T htLne hball' 𝒢L
        (η m) (hetann m hmN.le) ((hetamono m N hmN.le le_rfl).trans hηN) S hS0 hSM hshort).mono
        (mul_le_mul_left (loss_raise hB01 hB0Cbig hK0Kbig hc0cbig hδ hδ1) _)
  · have hse : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hsne
    exact ⟨s, Finset.Subset.refl s, by simp only [hse, Finset.card_empty, Nat.cast_zero,
        mul_zero, le_refl],
      emptyUniformTubeSet hse T (ssfGridLen δ) Cbig (hU.cover.tube),
      Or.inl (isKatzTaoAtEveryScale_emptyUniformTubeSet hse T (ssfGridLen δ) Cbig _ _)⟩

end StickyKakeya
