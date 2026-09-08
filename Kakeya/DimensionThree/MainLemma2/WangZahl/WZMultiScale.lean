/-
The multi-scale analysis behind Wang--Zahl Proposition 1.7 (`improvingProp`).

Source: `blueprint/src/WZ2/250224e_K3.tex`.

  * Proposition `improvingProp`                  line  292 (statement)
  * Section "Multi-scale analysis"               line 5066 (proof)
  * Lemma `bigVolumeOrFineDivisions`             line 5069
  * Lemma `bigVolumeOrKatzTaoAllScales`          line 5171
  * Theorem `katzTaoEveryScaleStickyKakeyaThm`   line 4745
  * Proposition `refinedInductionOnScaleProp`    line 4552
  * Proposition `grainsDecomposition`            line 2718
  * Moves #1, #2, #3                             line 3299

This file carries out the *bookkeeping* half of the source's proof of
Proposition 1.7 and isolates the geometry into named leaves.
-/
module

public import Kakeya.DimensionThree.MainLemma2.WangZahl.SigmaCalculus
public import Kakeya.DimensionThree.MainLemma2.WangZahl.WZBalancedCover
public import Kakeya.DimensionThree.MainLemma2.WangZahl.WZKatzTaoNodes
public import Kakeya.StickyKakeya.TubeInTubePacking
public import Kakeya.StickyKakeya
public import Kakeya.StickyKakeya.Reindex
public import Kakeya.StickyKakeya.MultiplicityTransfer

@[expose] public section

open MeasureTheory

namespace Kakeya.WangZahl

noncomputable section

universe u

/-! ### `delta^t` as a density / error parameter -/

/-- `delta^t` as a nonnegative real; the density and error parameters of the
source are always of this shape.  It is *definitionally* the anonymous
constructor `⟨(delta:R)^t, _⟩` used in `Kakeya.WangZahl.AssertionD`. -/
def rpowNN (δ : NNReal) (t : ℝ) : NNReal := δ ^ t

theorem rpowNN_eq_mk (δ : NNReal) (t : ℝ) :
    rpowNN δ t = ⟨(δ : ℝ) ^ t, Real.rpow_nonneg δ.coe_nonneg t⟩ := rfl

theorem coe_rpowNN (δ : NNReal) (t : ℝ) : ((rpowNN δ t : NNReal) : ℝ) = (δ : ℝ) ^ t := rfl

theorem coe_rpowNN_ennreal {δ : NNReal} (hδ : 0 < δ) (t : ℝ) :
    ((rpowNN δ t : NNReal) : ENNReal) = (δ : ENNReal) ^ t :=
  ENNReal.coe_rpow_of_ne_zero hδ.ne' t

theorem rpowNN_add {δ : NNReal} (hδ : 0 < δ) (a b : ℝ) :
    rpowNN δ (a + b) = rpowNN δ a * rpowNN δ b :=
  NNReal.eq (by
    simp only [coe_rpowNN, NNReal.coe_mul, coe_rpowNN]
    exact Real.rpow_add (by exact_mod_cast hδ) a b)

/-- `delta^t` is antitone in `t` for `delta <= 1`. -/
theorem rpowNN_le_rpowNN {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {t t' : ℝ}
    (h : t' ≤ t) : rpowNN δ t ≤ rpowNN δ t' :=
  NNReal.coe_le_coe.mp (Real.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hδ0)
    (by exact_mod_cast hδ1) h)

/-- Density is monotone: a smaller density parameter is a weaker hypothesis. -/
theorem IsDense.mono {δ : NNReal} {ι : Type u} {s : Finset ι}
    {T : ι → ShadedTube δ Space3} {lam lam' : NNReal} (h : lam' ≤ lam)
    (hd : IsDense s T lam) : IsDense s T lam' :=
  le_trans (by gcongr) hd

/-! ### The hypothesis bundle shared by the source's multi-scale lemmas -/

/-- The hypotheses carried by every family appearing in Assertion `D` and in
the source's multi-scale lemmas (:2723, :4556, :5072): the pair
`(T, Y)_delta` is a tube-shading family, is `delta^eta` dense, and obeys the
Katz--Tao Convex Wolff and Frostman Slab Wolff Axioms with error at most
`delta^{-eta}`. -/
def WZAdmissible {δ : NNReal} {ι : Type u} (s : Finset ι)
    (T : ι → ShadedTube δ Space3) (η : ℝ) : Prop :=
  IsTubeShadingFamily s T ∧
    IsDense s T (rpowNN δ η) ∧
      katzTaoConvexWolffConstant s T ≤ (δ : ENNReal) ^ (-η) ∧
        frostmanSlabWolffConstant s T ≤ (δ : ENNReal) ^ (-η)

/-- Admissibility is *antitone* in `eta`: a smaller `eta` is a stronger
hypothesis (denser shading, smaller Wolff errors), so it implies admissibility
at every larger `eta`.  This is the mechanism by which the source is free to
"choose `eta` sufficiently small". -/
theorem WZAdmissible.mono {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {ι : Type u}
    {s : Finset ι} {T : ι → ShadedTube δ Space3} {η η' : ℝ} (hle : η' ≤ η)
    (h : WZAdmissible.{u} s T η') : WZAdmissible.{u} s T η := by
  obtain ⟨hfam, hdense, hm, hell⟩ := h
  have hδ0' : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
  have hδ1' : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ1
  have hdens := ENNReal.coe_le_coe.mpr (rpowNN_le_rpowNN hδ0 hδ1 hle)
  have hpow : (δ : ENNReal) ^ (-η') ≤ (δ : ENNReal) ^ (-η) :=
    ENNReal.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hδ1) (by linarith)
  refine ⟨hfam, ?_, hm.trans hpow, hell.trans hpow⟩
  exact le_trans (by gcongr) hdense

/-! ### The two volume bounds appearing in the source's dichotomies -/

/-- Conclusion (A) of the source's multi-scale lemmas: the "large volume"
alternative, with a *gain* `alpha` over the exponent `omega` of Assertion `D`.
Source: :2724 (Prop `grainsDecomposition`), :4561 (Prop
`refinedInductionOnScaleProp`), :5074 and :5174. -/
def WZGainBound (σ ω α : ℝ) (κ : NNReal) {δ : NNReal} {ι : Type u}
    (s : Finset ι) (T : ι → ShadedTube δ Space3) : Prop :=
  (κ : ENNReal) * (δ : ENNReal) ^ (ω - α) * (s.card : ENNReal) * tubeVolume δ *
      (wzCurrency δ s.card) ^ (-σ) ≤
    volume (ShadedBody.iUnionShade s fun i => (T i).toShadedBody)

/-- The conclusion of Theorem `katzTaoEveryScaleStickyKakeyaThm` (:4750): the
union of the shadings has essentially full volume `(#T)|T|`, with only a
`delta^beta` loss.  This is the output of the sticky-Kakeya branch. -/
def WZFullBound (β : ℝ) (κ : NNReal) {δ : NNReal} {ι : Type u}
    (s : Finset ι) (T : ι → ShadedTube δ Space3) : Prop :=
  (κ : ENNReal) * (δ : ENNReal) ^ β * (s.card : ENNReal) * tubeVolume δ ≤
    volume (ShadedBody.iUnionShade s fun i => (T i).toShadedBody)

/-- The dichotomy actually used in the source's proof of Proposition 1.7
(:5197--5210): every admissible family either satisfies the improved bound
of Conclusion (A) of Lemma `bigVolumeOrKatzTaoAllScales` (:5174), or --- via
Conclusion (B) of that lemma (:5179) fed into Theorem
`katzTaoEveryScaleStickyKakeyaThm` (:4745) applied with `eps = omega/2` ---
satisfies the near-full volume bound. -/
def WZDichotomy (σ ω α : ℝ) (κ : NNReal) (η : ℝ) : Prop :=
  ∀ (δ : NNReal), 0 < δ → δ ≤ 1 →
    ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ Space3),
      WZAdmissible.{u} s T η →
      WZGainBound σ ω α κ s T ∨ WZFullBound (ω / 2) κ s T

/-- The dichotomy is monotone in `eta` in the same (antitone) sense as
`WZAdmissible`. -/
theorem WZDichotomy.mono {σ ω α : ℝ} {κ : NNReal} {η η' : ℝ} (hle : η' ≤ η)
    (h : WZDichotomy.{u} σ ω α κ η) : WZDichotomy.{u} σ ω α κ η' := by
  intro δ hδ0 hδ1 ι s T hadm
  exact h δ hδ0 hδ1 s T (hadm.mono hδ0 hδ1 hle)

/-! ### Refinements, and the Katz--Tao Convex Wolff Axioms at every scale -/

/-- The total carrier mass of a tube family. -/
theorem sum_volume_carrier {δ : NNReal} {ι : Type u} (s : Finset ι)
    (T : ι → ShadedTube δ Space3) :
    ∑ i ∈ s, volume (T i).carrier = (s.card : ENNReal) * tubeVolume δ := by
  simp [volume_carrier_eq_tubeVolume, Finset.sum_const, nsmul_eq_mul]

/-- The source's notion of a `t`-refinement (:826): a sub-family, with shrunk
shadings, retaining a `t` fraction of the total shading mass. -/
def IsWZRefinement {δ : NNReal} {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ Space3)
    (s' : Finset ι) (T' : ι → ShadedTube δ Space3) (t : NNReal) : Prop :=
  s' ⊆ s ∧ (∀ i ∈ s', (T' i).carrier = (T i).carrier) ∧
    (∀ i ∈ s', (T' i).shade ⊆ (T i).shade) ∧
      (t : ENNReal) * ∑ i ∈ s, volume (T i).shade ≤ ∑ i ∈ s', volume (T' i).shade

namespace IsWZRefinement

variable {δ : NNReal} {ι : Type u} {s s' : Finset ι} {T T' : ι → ShadedTube δ Space3}
  {t lam : NNReal}

theorem isTubeShadingFamily (href : IsWZRefinement s T s' T' t)
    (hfam : IsTubeShadingFamily s T) : IsTubeShadingFamily s' T' := by
  obtain ⟨hsub, hcar, _, _⟩ := href
  refine ⟨fun i hi => ?_, fun i hi j hj hij => ?_⟩
  · rw [hcar i hi]; exact hfam.1 i (hsub hi)
  · change IsEssentiallyDistinct (T' i).carrier (T' j).carrier
    rw [hcar i hi, hcar j hj]
    exact hfam.2 (hsub hi) (hsub hj) hij

/-- The shaded union of a refinement is contained in that of the original. -/
theorem volume_iUnionShade_le (href : IsWZRefinement s T s' T' t) :
    volume (ShadedBody.iUnionShade s' fun i => (T' i).toShadedBody) ≤
      volume (ShadedBody.iUnionShade s fun i => (T i).toShadedBody) := by
  obtain ⟨hsub, _, hshade, _⟩ := href
  refine measure_mono ?_
  refine Set.iUnion₂_subset fun i hi => ?_
  exact fun x hx => Set.mem_biUnion (hsub hi) (hshade i hi hx)

/-- The source's remark after :826: a `t`-refinement of a `lam`-dense family is
`t * lam`-dense. -/
theorem isDense (href : IsWZRefinement s T s' T' t) (hdense : IsDense s T lam) :
    IsDense s' T' (t * lam) := by
  obtain ⟨hsub, _, _, hmass⟩ := href
  have hcard : (s'.card : ENNReal) ≤ (s.card : ENNReal) := by
    exact_mod_cast Finset.card_le_card hsub
  calc ((t * lam : NNReal) : ENNReal) * ∑ i ∈ s', volume (T' i).carrier
      = (t : ENNReal) * ((lam : ENNReal) * ((s'.card : ENNReal) * tubeVolume δ)) := by
        rw [sum_volume_carrier]; push_cast; ring
    _ ≤ (t : ENNReal) * ((lam : ENNReal) * ((s.card : ENNReal) * tubeVolume δ)) := by gcongr
    _ = (t : ENNReal) * ((lam : ENNReal) * ∑ i ∈ s, volume (T i).carrier) := by
        rw [sum_volume_carrier]
    _ ≤ (t : ENNReal) * ∑ i ∈ s, volume (T i).shade := by gcongr; exact hdense
    _ ≤ ∑ i ∈ s', volume (T' i).shade := hmass

/-- The source's remark after :826: `#T' >= lam t (#T)`. -/
theorem card_ge (hδ0 : 0 < δ) (href : IsWZRefinement s T s' T' t)
    (hdense : IsDense s T lam) :
    (t : ENNReal) * (lam : ENNReal) * (s.card : ENNReal) ≤ (s'.card : ENNReal) := by
  obtain ⟨_, _, _, hmass⟩ := href
  have hV := tubeVolume_pos_and_ne_top hδ0
  have h1 : (t : ENNReal) * (lam : ENNReal) * (s.card : ENNReal) * tubeVolume δ ≤
      (s'.card : ENNReal) * tubeVolume δ := by
    calc (t : ENNReal) * (lam : ENNReal) * (s.card : ENNReal) * tubeVolume δ
        = (t : ENNReal) * ((lam : ENNReal) * ∑ i ∈ s, volume (T i).carrier) := by
          rw [sum_volume_carrier]; ring
      _ ≤ (t : ENNReal) * ∑ i ∈ s, volume (T i).shade := by gcongr; exact hdense
      _ ≤ ∑ i ∈ s', volume (T' i).shade := hmass
      _ ≤ ∑ i ∈ s', volume (T' i).carrier :=
          Finset.sum_le_sum fun i _ => measure_mono (T' i).shade_subset
      _ = (s'.card : ENNReal) * tubeVolume δ := sum_volume_carrier _ _
  exact (ENNReal.mul_le_mul_iff_left hV.1.ne' hV.2).mp h1

end IsWZRefinement

/-- Weakening the balance constant of a balanced partitioning cover. -/
def BalancedNodeCover.monoBalance {ι : Type u} {δ ρ : NNReal} {s : Finset ι}
    {T : ι → Tube δ Space3} {K K' : NNReal} (h : K ≤ K')
    (B : BalancedNodeCover (rho := ρ) s T K) : BalancedNodeCover (rho := ρ) s T K' :=
  { B with
    card_class_le := fun j hj => (B.card_class_le j hj).trans (by gcongr)
    le_card_class := fun j hj => (B.le_card_class j hj).trans (by gcongr) }

/-- Wang--Zahl Definition :4734: the family `T` satisfies the *Katz--Tao Convex
Wolff Axioms at every scale with error `K`* if for every `rho_0` in `[delta,1]`
there is a scale `rho` in `[rho_0, K rho_0)` and a `K`-balanced partitioning
cover of `T` by `rho`-tubes whose own Katz--Tao constant is at most `K`.

The auxiliary shading `P` carries no information (`katzTaoConvexWolffConstant`
depends only on the carriers); it is present because the project's Katz--Tao
constant is defined for *shaded* tube families. -/
def KatzTaoEveryScale {δ : NNReal} {ι : Type u} (s : Finset ι)
    (T : ι → ShadedTube δ Space3) (K : NNReal) : Prop :=
  ∀ ρ₀ : NNReal, δ ≤ ρ₀ → ρ₀ ≤ 1 →
    ∃ ρ : NNReal, ρ₀ ≤ ρ ∧ ρ < K * ρ₀ ∧
      ∃ (P : ι → ShadedTube ρ Space3)
        (B : BalancedNodeCover (rho := ρ) s (fun i => (T i).toTube) K),
        (∀ j, B.parentTube j = (P j).toTube) ∧
          katzTaoConvexWolffConstant B.parent P ≤ (K : ENNReal)

theorem KatzTaoEveryScale.mono {δ : NNReal} {ι : Type u} {s : Finset ι}
    {T : ι → ShadedTube δ Space3} {K K' : NNReal} (hK : K ≤ K')
    (h : KatzTaoEveryScale.{u} s T K) : KatzTaoEveryScale.{u} s T K' := by
  intro ρ₀ hρδ hρ1
  obtain ⟨ρ, hρ0, hρK, P, B, hPB, hCKT⟩ := h ρ₀ hρδ hρ1
  refine ⟨ρ, hρ0, lt_of_lt_of_le hρK (by gcongr), P, B.monoBalance hK, hPB, ?_⟩
  exact hCKT.trans (by exact_mod_cast hK)

/-! ### From the source's every-scale hypothesis to the project's node reading -/

/-- **The Wang--Zahl every-scale hypothesis gives the project's node reading.**

Let `t ⊆ s` carry a uniform hierarchy `𝒰` along the grid of length `N`, let the ambient family
`s` satisfy the Katz--Tao Convex Wolff Axioms at every scale with error `K ≥ 1`
(`KatzTaoEveryScale`, Wang--Zahl Definition `:4734`), and let the *leaf* density of `s` be at
most `D`.  Then `𝒰` satisfies `Tube.UniformTubeSet.IsKatzTaoAtEveryScale` with the explicit
error `max (ktNodeCmpConst · Cu · K ^ {3n+1}) (tubeVolRatio · D)`.

This is the translation of hypotheses named as the whole remaining debt in the docstring of
`katzTaoEveryScale_multiplicity_le`, and the Katz--Tao counterpart of
`Kakeya.isFrostmanAtEveryScale_capped_of_ambient_leaf`.  Its two halves are

* the *scale* half: `KatzTaoEveryScale` is applied at `ρ₀ = ρ_k`, and its bracket
  `ρ ∈ [ρ_k, K ρ_k)` is exactly the comparability the node comparison needs; the *balance*
  clauses of the cover it returns are not used at all;
* the *density* half: `Kakeya.StickyKakeya.isKatzTaoAtEveryScale_nodes_of_ambient_covers`,
  which transfers a maximal-density bound from a cover of the ambient family at a comparable
  scale to the hierarchy's own nodes, by thickening the convex test body by `4ρ` and counting
  the nodes lying over one parent.

The leaf-scale datum `D` is a genuine second hypothesis and not an oversight: at the bottom
grid index `ρ_N = δ` the source's covers say nothing, since a node may bunch essentially
identical leaves, and the node density there is bounded from the leaf density instead. -/
theorem isKatzTaoAtEveryScale_of_katzTaoEveryScale
    {δ : NNReal} {ι : Type u} {s t : Finset ι} {T : ι → ShadedTube δ Space3}
    {N : ℕ} {Cu : NNReal}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hN : 0 < N) (hδN : δ ≤ (16 : NNReal) ^ (-(N : ℝ)))
    (hts : t ⊆ s) (htne : t.Nonempty)
    (𝒰 : Tube.UniformTubeSet t (fun i => (T i).toTube) N Cu)
    {K D : NNReal} (hK : 1 ≤ K)
    (hKT : KatzTaoEveryScale.{u} s T K)
    (hD : maxDensity s (fun i => ((T i).toTube).toConvexSpaceBody) ≤ (D : ENNReal)) :
    𝒰.IsKatzTaoAtEveryScale
      (max ((StickyKakeya.ktNodeCmpConst (E := Space3) * Cu
              * K ^ (3 * Module.finrank ℝ Space3) * K : NNReal) : ENNReal)
        ((MultiScaleFac.tubeVolRatio (E := Space3) * D : NNReal) : ENNReal)) := by
  classical
  refine StickyKakeya.isKatzTaoAtEveryScale_nodes_of_ambient_covers
    hδ hδ1 hN hδN hts htne 𝒰 hK ?_ hD
  intro k hk
  have hσδ : δ ≤ Tube.gridScale δ N k := by
    have hmono : Tube.gridScale δ N N ≤ Tube.gridScale δ N k :=
      Tube.gridScale_antitone hδ hδ1 N (Nat.le_of_lt hk)
    rwa [Tube.gridScale_self δ hN] at hmono
  have hσ1 : Tube.gridScale δ N k ≤ 1 := Tube.gridScale_le_one hδ1 N k
  obtain ⟨ρ, hρ0, hρK, P, B, hPB, hCKT⟩ := hKT (Tube.gridScale δ N k) hσδ hσ1
  refine ⟨ρ, hρ0, le_of_lt hρK, B.parent, fun j => (P j).toTube, B.assign,
    B.assign_mem, ?_, ?_⟩
  · intro i hi
    have hle := B.leaf_le_parent i hi
    rwa [hPB (B.assign i)] at hle
  · have hρpos : 0 < ρ := lt_of_lt_of_le (Tube.gridScale_pos hδ N k) hρ0
    exact (maxDensity_le_katzTaoConvexWolffConstant hρpos B.parent P).trans hCKT

/-- **The leaf-scale density from the every-scale hypothesis, modulo one packing count.**

`KatzTaoEveryScale` applied at `ρ₀ = δ` returns a cover of `s` by `ρ`-tubes, `ρ ∈ [δ, K δ)`, of
maximal density at most `K`.  Given in addition a bound `M` on the number of members of `s`
lying inside *any* single tube of a scale in that window, the leaves themselves have maximal
density at most `ktLeafCmpConst · M · K ^ n · K`.

The hypothesis `hpack` is the only place where essential distinctness of the family has to be
spent, and it is the sole remaining input of this route: for a pairwise essentially distinct
family of `δ`-tubes one expects `M ≲ (ρ/δ)^{2(n-1)} ≤ K^4` in `ℝ³`, but the tree's packing count
`Tube.card_le_of_EssDistinct` counts inside a *ball* (with the crude exponent `2n` and no
direction restriction), and there is no count inside a *tube*.

The conclusion is the datum `hD` of `isKatzTaoAtEveryScale_of_katzTaoEveryScale` and the
hypothesis `ConvexSpaceBody.IsKatzTao s _ δ^{-η}` of `StickyKakeya.StickyKatzTaoEstimate`. -/
theorem maxDensity_leaves_le_of_katzTaoEveryScale
    {δ : NNReal} {ι : Type u} [DecidableEq ι] {s : Finset ι} {T : ι → ShadedTube δ Space3}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) {K M : NNReal} (hK : 1 ≤ K)
    (hKT : KatzTaoEveryScale.{u} s T K)
    (hpack : ∀ (ρ : NNReal), δ ≤ ρ → ρ < K * δ → ∀ V : Tube ρ Space3,
      (((s.filter (fun i => ((T i).toTube).toConvexSpaceBody ≤ V.toConvexSpaceBody)).card : ℕ)
        : NNReal) ≤ M) :
    maxDensity s (fun i => ((T i).toTube).toConvexSpaceBody)
      ≤ ((StickyKakeya.ktLeafCmpConst (E := Space3) * M
            * K ^ Module.finrank ℝ Space3 * K : NNReal) : ENNReal) := by
  classical
  obtain ⟨ρ, hρ0, hρK, P, B, hPB, hCKT⟩ := hKT δ le_rfl hδ1
  have hρpos : 0 < ρ := lt_of_lt_of_le hδ hρ0
  have hGρ : ρ ≤ K * δ := le_of_lt hρK
  have hmult : ∀ j' : ι, (((s.filter (fun i => B.assign i = j')).card : ℕ) : NNReal) ≤ M := by
    intro j'
    refine le_trans ?_ (hpack ρ hρ0 hρK (B.parentTube j'))
    have hsub : s.filter (fun i => B.assign i = j')
        ⊆ s.filter (fun i => ((T i).toTube).toConvexSpaceBody
            ≤ (B.parentTube j').toConvexSpaceBody) := by
      intro i hi
      obtain ⟨his, hij⟩ := Finset.mem_filter.mp hi
      refine Finset.mem_filter.mpr ⟨his, ?_⟩
      have hle := B.leaf_le_parent i his
      rwa [hij] at hle
    exact_mod_cast Finset.card_le_card hsub
  refine le_trans (StickyKakeya.maxDensity_leaves_le_of_ambient_cover
    (T := fun i => (T i).toTube) (P := fun j => (P j).toTube) (assign := B.assign)
    hδ hδ1 hρ0 hK hGρ B.assign_mem ?_ hmult
    ((maxDensity_le_katzTaoConvexWolffConstant hρpos B.parent P).trans hCKT)) ?_
  · intro i hi
    have hle := B.leaf_le_parent i hi
    rwa [hPB (B.assign i)] at hle
  · rw [← ENNReal.coe_mul]

/-! ### The two geometric leaves -/


/-- The crude packing bound of `Tube.card_le_of_EssDistinct`, packaged as an
`NNReal` cap valid on `[delta_0, 1]`, and at least `1`. -/
noncomputable def wzPackCap (δ₀ : NNReal) : NNReal :=
  Real.toNNReal (Tube.card_le_of_EssDistinct.C (Module.finrank ℝ Space3)
    * (1 / (δ₀ : ℝ)) ^ (2 * Module.finrank ℝ Space3)) + 1

theorem one_le_wzPackCap (δ₀ : NNReal) : 1 ≤ wzPackCap δ₀ := by
  simp [wzPackCap]

theorem wzPackCap_pos (δ₀ : NNReal) : 0 < wzPackCap δ₀ :=
  lt_of_lt_of_le zero_lt_one (one_le_wzPackCap δ₀)

/-- On `[delta_0, 1]` the cardinality of an essentially distinct family of
`delta`-tubes in the unit ball is at most `wzPackCap delta_0`. -/
theorem card_le_wzPackCap {δ₀ δ : NNReal} (hδ₀ : 0 < δ₀) (hδ : δ₀ ≤ δ)
    {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ Space3)
    (hδ0 : 0 < δ) (hfam : IsTubeShadingFamily s T) :
    (s.card : NNReal) ≤ wzPackCap δ₀ := by
  have hcard : (s.card : ℝ) ≤ Tube.card_le_of_EssDistinct.C (Module.finrank ℝ Space3)
      * (1 / (δ : ℝ)) ^ (2 * Module.finrank ℝ Space3) :=
    Tube.card_le_of_EssDistinct hδ0 1 s (fun i => (T i).toTube) hfam.1 hfam.2
  have hδ₀R : (0 : ℝ) < (δ₀ : ℝ) := by exact_mod_cast hδ₀
  have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
  have hmono : (1 / (δ : ℝ)) ^ (2 * Module.finrank ℝ Space3)
      ≤ (1 / (δ₀ : ℝ)) ^ (2 * Module.finrank ℝ Space3) := by
    have : (1 / (δ : ℝ)) ≤ 1 / (δ₀ : ℝ) :=
      one_div_le_one_div_of_le hδ₀R (by exact_mod_cast hδ)
    exact pow_le_pow_left₀ (by positivity) this _
  have hC : (0 : ℝ) ≤ Tube.card_le_of_EssDistinct.C (Module.finrank ℝ Space3) :=
    Tube.card_le_of_EssDistinct.C_pos.le
  have hcard' : (s.card : ℝ) ≤ Tube.card_le_of_EssDistinct.C (Module.finrank ℝ Space3)
      * (1 / (δ₀ : ℝ)) ^ (2 * Module.finrank ℝ Space3) :=
    hcard.trans (by gcongr)
  have : ((s.card : NNReal) : ℝ) ≤ ((wzPackCap δ₀ : NNReal) : ℝ) := by
    rw [wzPackCap]
    push_cast
    have := Real.coe_toNNReal' (Tube.card_le_of_EssDistinct.C (Module.finrank ℝ Space3)
      * (1 / (δ₀ : ℝ)) ^ (2 * Module.finrank ℝ Space3))
    rw [this]
    have hle : (s.card : ℝ) ≤ max (Tube.card_le_of_EssDistinct.C (Module.finrank ℝ Space3)
        * (1 / (δ₀ : ℝ)) ^ (2 * Module.finrank ℝ Space3)) 0 :=
      hcard'.trans (le_max_left _ _)
    linarith
  exact_mod_cast this

/-! ### The packing cap supplied by the in-tube count -/

/-- The `hpack` cap of `Kakeya.WangZahl.maxDensity_leaves_le_of_katzTaoEveryScale`, as delivered
by `Kakeya.card_le_of_EssDistinct_in_tube_six`: at scales `ρ < K δ` the count of members of an
essentially distinct family lying in one `ρ`-tube is at most `edInTubeConst · K ^ 6`. -/
noncomputable def wzInTubeCap (K : NNReal) : NNReal :=
  Real.toNNReal Kakeya.edInTubeConst * K ^ 6

open Classical in
/-- **The packing input of the leaf-density route, discharged.**

This is `hpack` of `Kakeya.WangZahl.maxDensity_leaves_le_of_katzTaoEveryScale`: for an
essentially distinct family of `δ`-tubes of the unit ball and any tube of radius
`ρ ∈ [δ, K δ)`, at most `wzInTubeCap K` members lie inside it.  The constant is absolute and
the whole `δ`-dependence is the factor `K ^ 6`. -/
theorem card_le_wzInTubeCap {δ ρ K : NNReal} (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hρK : ρ < K * δ)
    {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ Space3)
    (hfam : IsTubeShadingFamily s T) (V : Tube ρ Space3) :
    (((s.filter (fun i => ((T i).toTube).toConvexSpaceBody ≤ V.toConvexSpaceBody)).card : ℕ)
      : NNReal) ≤ wzInTubeCap K := by
  have hδ0 : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  have hcount := Kakeya.card_le_of_EssDistinct_in_tube_six (ι := ι) hδ hδρ
    s (fun i => (T i).toTube) hfam.1 hfam.2 V
  have hratio : (ρ : ℝ) / (δ : ℝ) ≤ (K : ℝ) := by
    rw [div_le_iff₀ hδ0]
    have : (ρ : ℝ) < (K : ℝ) * (δ : ℝ) := by exact_mod_cast hρK
    linarith
  have hpow : ((ρ : ℝ) / (δ : ℝ)) ^ 6 ≤ (K : ℝ) ^ 6 :=
    pow_le_pow_left₀ (by positivity) hratio 6
  have hCnn : (0 : ℝ) ≤ Kakeya.edInTubeConst := Kakeya.edInTubeConst_pos.le
  have hfinal : (((s.filter
      (fun i => ((T i).toTube).toConvexSpaceBody ≤ V.toConvexSpaceBody)).card : ℕ) : ℝ)
      ≤ Kakeya.edInTubeConst * (K : ℝ) ^ 6 :=
    hcount.trans (mul_le_mul_of_nonneg_left hpow hCnn)
  have hcast : ((wzInTubeCap K : NNReal) : ℝ) = Kakeya.edInTubeConst * (K : ℝ) ^ 6 := by
    rw [wzInTubeCap]
    push_cast
    rw [Real.coe_toNNReal _ hCnn]
  rw [← NNReal.coe_le_coe]
  push_cast
  rw [hcast]
  exact hfinal

/-- **The leaf-scale density from the every-scale hypothesis, unconditionally.**

`Kakeya.WangZahl.maxDensity_leaves_le_of_katzTaoEveryScale` with its packing hypothesis
discharged by `Kakeya.WangZahl.card_le_wzInTubeCap`.  This is the datum `hD` of
`Kakeya.WangZahl.isKatzTaoAtEveryScale_of_katzTaoEveryScale` and the leaf-scale hypothesis
`ConvexSpaceBody.IsKatzTao` of `StickyKakeya.StickyKatzTaoEstimate`. -/
theorem maxDensity_leaves_le_of_katzTaoEveryScale_of_family
    {δ : NNReal} {ι : Type u} [DecidableEq ι] {s : Finset ι} {T : ι → ShadedTube δ Space3}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) {K : NNReal} (hK : 1 ≤ K)
    (hfam : IsTubeShadingFamily s T)
    (hKT : KatzTaoEveryScale.{u} s T K) :
    maxDensity s (fun i => ((T i).toTube).toConvexSpaceBody)
      ≤ ((StickyKakeya.ktLeafCmpConst (E := Space3) * wzInTubeCap K
            * K ^ Module.finrank ℝ Space3 * K : NNReal) : ENNReal) :=
  maxDensity_leaves_le_of_katzTaoEveryScale hδ hδ1 hK hKT
    (fun ρ hρ0 hρK V => card_le_wzInTubeCap hδ hρ0 hρK s T hfam V)

theorem katzTaoEveryScale_congr {δ : NNReal} {ι : Type u} {s : Finset ι}
    {T T' : ι → ShadedTube δ Space3} {K : NNReal}
    (h : ∀ i, (T' i).toTube = (T i).toTube) (hKT : KatzTaoEveryScale.{u} s T K) :
    KatzTaoEveryScale.{u} s T' K := by
  unfold KatzTaoEveryScale at hKT ⊢
  rw [show (fun i => (T' i).toTube) = (fun i => (T i).toTube) from funext h]
  exact hKT

/-- the constant absorbing every dimensional factor of the two density bounds. -/
def ktBridgeConst : NNReal :=
  max (StickyKakeya.ktNodeCmpConst (E := Space3)
        * ShadedTube.ssfUniformConst (Module.finrank ℝ Space3))
    (max (StickyKakeya.ktLeafCmpConst (E := Space3) * Real.toNNReal Kakeya.edInTubeConst)
      (Kakeya.MultiScaleFac.tubeVolRatio (E := Space3)
        * (StickyKakeya.ktLeafCmpConst (E := Space3) * Real.toNNReal Kakeya.edInTubeConst)))

set_option maxHeartbeats 2000000 in
/-- **Leaf 1** = Wang--Zahl Theorem `katzTaoEveryScaleStickyKakeyaThm` (:4745)
in *multiplicity* form, which is [GWZ, Theorem 7.3(B)].

For every `eps > 0` there are `eta, delta_0 > 0` so that every
`delta^eta`-dense family of essentially distinct `delta`-tubes in the unit ball
satisfying the Katz--Tao Convex Wolff Axioms at every scale with error
`delta^{-eta}` (Definition `KatzTaoConvexWolffAtEveryScaleDefn`, :4734) has
multiplicity at most `delta^{-eps}`.

**Why the leaf is stated in this form.**  The volume statement of the source
(:4750) follows from this one by the elementary counting
`|U Y(T)| >= (sum_T |Y(T)|)/mu >= delta^eta (#T)|T| / delta^{-eps}`, which is
what `stickyKakeyaEveryScale` below carries out; no geometry is left in that
passage. So no new mathematics is owed here; what is owed is a translation of
hypotheses between two encodings of "Katz--Tao at every scale":

* the source's, used here, quantifies over `rho_0 in [delta,1]` and asks for
  *some* `K`-balanced partitioning cover by `rho`-tubes, `rho in [rho_0,K rho_0)`,
  with `C_KT` at most `K` (`KatzTaoEveryScale`);
* the project's, used by `StickyKakeya.StickyKatzTaoEstimate`, reads
  `Kakeya.maxDensity` off the node families of *one* nested hierarchy
  `ShadedTube.ShadedUniformTubeSet` along the grid `Tube.ssfGridLen delta`
  (`Tube.UniformTubeSet.IsKatzTaoAtEveryScale`), and additionally carries the
  leaf-scale bound `ConvexSpaceBody.IsKatzTao`.

Closing the leaf therefore needs (i) a hierarchy for the family --- available,
`ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf`, at the cost of a
`delta^{-alpha}` refinement --- and (ii) the Katz--Tao analogue of
`Kakeya.StickyKakeya.isFrostmanAtEveryScale_nodes_of_ambient_fibre`, i.e. the
comparison of the node density of the hierarchy's own cover with the source's
`C_KT` bound on a balanced cover at a comparable scale.  Piece (ii) has no
counterpart in the tree; it is the whole of the remaining debt.

The source instead proves :4750 from Theorem `WZThm52` and the
Nikishin--Stein--Pisier factorization Proposition `factorizationProp` (:4762);
that route is *not* the cheapest one available here, because the project has
already paid for `7.3(A) => 7.3(B)`. -/
theorem katzTaoEveryScale_multiplicity_le (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, ∃ δ₀ : NNReal, 0 < η ∧ η ≤ ε ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ (δ : NNReal), 0 < δ → δ ≤ δ₀ →
        ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ Space3),
          IsTubeShadingFamily s T →
          IsDense s T (rpowNN δ η) →
          KatzTaoEveryScale.{u} s T (rpowNN δ (-η)) →
          ShadedBody.multiplicity s (fun i => (T i).toShadedBody)
            ≤ (δ : ENNReal) ^ (-ε) := by
  classical
  obtain ⟨ηB, δB, hηB, hδB, hSKT⟩ :=
    StickyKakeya.stickyKatzTaoEstimate_apply.{u, 0}
      (StickyKakeya.stickyKatzTaoEstimate_of_stickyFrostmanEstimate (E := Space3)
        (StickyKakeya.stickyFrostmanEstimate (E := Space3) finrank_euclideanSpace_fin))
      (ε / 2) (by linarith)
  set n : ℕ := Module.finrank ℝ Space3 with hn
  set p : ℕ := 4 * n + 8 with hp
  have hp8 : (8:ℝ) ≤ (p:ℝ) := by
    rw [hp]; push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hpR : (0:ℝ) < (p:ℝ) := by linarith
  set η : ℝ := min (ηB / (2 * ((p:ℝ) + 1))) (ε / 16) with hηdef
  have hη : 0 < η := lt_min (by positivity) (by linarith)
  have hηε : η ≤ ε := le_trans (min_le_right _ _) (by linarith)
  have hηp : (p:ℝ) * η < ηB := by
    have h1 : η ≤ ηB / (2 * ((p:ℝ) + 1)) := min_le_left _ _
    have h2 : (p:ℝ) * η ≤ (p:ℝ) * (ηB / (2 * ((p:ℝ) + 1))) := by nlinarith
    have h3 : (p:ℝ) * (ηB / (2 * ((p:ℝ) + 1))) < ηB := by
      rw [mul_div_assoc'] at *
      rw [div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  have hη3 : 3 * η ≤ ηB := by nlinarith [hηp, hη.le, hp8]
  have hη6 : 6 * η ≤ ε / 2 := by
    have : η ≤ ε / 16 := min_le_right _ _
    linarith
  -- thresholds
  obtain ⟨δR, hδR0, hδR1, hrefine⟩ :=
    ShadedTube.exists_shadedUniformTubeSet_subfamily_ssf.{u, 0} (E := Space3) (2 * n + 1) η η hη hη
  obtain ⟨δG, hδG0, hδG1, hG⟩ :=
    Tube.exists_threshold_polylog_pow_ssfGridLen_le 1 le_rfl 0 1 1 one_pos
  obtain ⟨δA, hδA0, hδA⟩ :=
    Kakeya.StickyKakeya.const_absorb_threshold ktBridgeConst ((p:ℝ) * η) ηB hηp
  set Cpack : ℝ := Tube.card_le_of_EssDistinct.C n with hCpack
  have hCpack0 : 0 < Cpack := Tube.card_le_of_EssDistinct.C_pos
  set δ₀ : NNReal := min (min (min (Real.toNNReal δB) δR) (min δG (Real.toNNReal δA)))
      (min (min (Real.toNNReal ((1/2 : ℝ) ^ (1/η))) (Real.toNNReal (1 / Cpack))) 1) with hδ₀
  refine ⟨η, δ₀, hη, hηε, ?_, ?_, ?_⟩
  · refine lt_min (lt_min (lt_min ?_ hδR0) (lt_min hδG0 ?_)) (lt_min (lt_min ?_ ?_) one_pos)
    · exact Real.toNNReal_pos.mpr hδB
    · exact Real.toNNReal_pos.mpr hδA0
    · exact Real.toNNReal_pos.mpr (Real.rpow_pos_of_pos (by norm_num) _)
    · exact Real.toNNReal_pos.mpr (by positivity)
  · exact le_trans (min_le_right _ _) (min_le_right _ _)
  intro δ hδ0 hδδ₀ ι s T hfam hdense hKT
  have hδR0 : (0:ℝ) < (δ:ℝ) := by exact_mod_cast hδ0
  have hδ1 : δ ≤ 1 := le_trans hδδ₀ (le_trans (min_le_right _ _) (min_le_right _ _))
  have hδ1R : (δ:ℝ) ≤ 1 := by exact_mod_cast hδ1
  have hstep1 : δ ≤ min (min (Real.toNNReal δB) δR) (min δG (Real.toNNReal δA)) :=
    le_trans hδδ₀ (min_le_left _ _)
  have hstep2 : δ ≤ min (Real.toNNReal ((1/2 : ℝ) ^ (1/η))) (Real.toNNReal (1 / Cpack)) :=
    le_trans hδδ₀ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδB' : (δ:ℝ) ≤ δB := by
    have : δ ≤ Real.toNNReal δB := le_trans hstep1 (le_trans (min_le_left _ _) (min_le_left _ _))
    have := NNReal.coe_le_coe.mpr this
    rwa [Real.coe_toNNReal _ hδB.le] at this
  have hδδR : δ ≤ δR := le_trans hstep1 (le_trans (min_le_left _ _) (min_le_right _ _))
  have hδδG : δ ≤ δG := le_trans hstep1 (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδA' : (δ:ℝ) ≤ δA := by
    have : δ ≤ Real.toNNReal δA := le_trans hstep1 (le_trans (min_le_right _ _) (min_le_right _ _))
    have := NNReal.coe_le_coe.mpr this
    rwa [Real.coe_toNNReal _ hδA0.le] at this
  have hhalf : (δ:ℝ) ^ η ≤ 1/2 := by
    have hle : (δ:ℝ) ≤ (1/2 : ℝ) ^ (1/η) := by
      have : δ ≤ Real.toNNReal ((1/2 : ℝ) ^ (1/η)) := le_trans hstep2 (min_le_left _ _)
      have := NNReal.coe_le_coe.mpr this
      rwa [Real.coe_toNNReal _ (Real.rpow_nonneg (by norm_num) _)] at this
    calc (δ:ℝ) ^ η ≤ ((1/2 : ℝ) ^ (1/η)) ^ η :=
          Real.rpow_le_rpow hδR0.le hle hη.le
      _ = 1/2 := by
          rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 1/2), one_div_mul_cancel hη.ne',
            Real.rpow_one]
  have hCp : Cpack ≤ (δ:ℝ) ^ (-(1:ℝ)) := by
    have hle : (δ:ℝ) ≤ 1 / Cpack := by
      have : δ ≤ Real.toNNReal (1 / Cpack) := le_trans hstep2 (min_le_right _ _)
      have := NNReal.coe_le_coe.mpr this
      rwa [Real.coe_toNNReal _ (by positivity)] at this
    rw [Real.rpow_neg_one]
    rw [le_inv_comm₀ hCpack0 hδR0]
    rwa [one_div] at hle
  rcases s.eq_empty_or_nonempty with rfl | hsne
  · simp [ShadedBody.multiplicity]
  obtain ⟨hvol0, hvoltop⟩ := tubeVolume_pos_and_ne_top hδ0
  have hcar : ∀ i ∈ s, volume ((T i).toShadedBody).carrier = tubeVolume δ :=
    fun i _ => volume_carrier_eq_tubeVolume T i
  have hcoeη : ((rpowNN δ η : NNReal) : ENNReal) = ENNReal.ofReal ((δ:ℝ)^η) := by
    rw [← ENNReal.ofReal_coe_nnreal, coe_rpowNN]
  have hlampos : (0:ℝ) < (δ:ℝ) ^ η := Real.rpow_pos_of_pos hδR0 η
  have hlam0 : ENNReal.ofReal ((δ:ℝ)^η) ≠ 0 := (ENNReal.ofReal_pos.mpr hlampos).ne'
  have hcardpos : 0 < s.card := Finset.card_pos.mpr hsne
  have hcardne : (s.card : ENNReal) ≠ 0 := by exact_mod_cast hcardpos.ne'
  have hprod0 : (s.card : ENNReal) * tubeVolume δ ≠ 0 := mul_ne_zero hcardne hvol0.ne'
  have hprodtop : (s.card : ENNReal) * tubeVolume δ ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hvoltop
  have hfull_s : ENNReal.ofReal ((δ:ℝ)^η)
      ≤ ShadedBody.fullness' s (fun i => (T i).toShadedBody) := by
    rw [ShadedBody.fullness', sum_volume_carrier s T,
      ENNReal.le_div_iff_mul_le (Or.inl hprod0) (Or.inl hprodtop)]
    have h := hdense
    rw [IsDense, sum_volume_carrier] at h
    rwa [hcoeη] at h
  obtain ⟨s₀, hs₀s, hband₀, hcard₀⟩ :=
    ShadedBody.exists_shade_threshold_subfamily (fun i => (T i).toShadedBody)
      hvol0.ne' hvoltop hcar hlam0 ENNReal.ofReal_ne_top hfull_s
  have hcards₀ : ((s₀.card : ℕ) : ℝ) ≤ (δ:ℝ) ^ (-((2 * n + 1 : ℕ) : ℝ)) := by
    have h1 : ((s.card : ℕ) : ℝ) ≤ Cpack * (1/(δ:ℝ)) ^ (2 * n) :=
      Tube.card_le_of_EssDistinct hδ0 1 s (fun i => (T i).toTube) hfam.1 hfam.2
    have h2 : ((s₀.card : ℕ):ℝ) ≤ ((s.card:ℕ):ℝ) := by exact_mod_cast Finset.card_le_card hs₀s
    have h3 : (1/(δ:ℝ)) ^ (2 * n) = (δ:ℝ) ^ (-((2*n : ℕ) : ℝ)) := by
      rw [Real.rpow_neg hδR0.le, Real.rpow_natCast, one_div, inv_pow]
    have h4 : (δ:ℝ) ^ (-(1:ℝ)) * (δ:ℝ) ^ (-((2*n : ℕ) : ℝ))
        = (δ:ℝ) ^ (-((2 * n + 1 : ℕ) : ℝ)) := by
      rw [← Real.rpow_add hδR0]
      congr 1
      push_cast
      ring
    calc ((s₀.card : ℕ):ℝ) ≤ Cpack * (1/(δ:ℝ)) ^ (2 * n) := le_trans h2 h1
      _ = Cpack * (δ:ℝ) ^ (-((2*n : ℕ) : ℝ)) := by rw [h3]
      _ ≤ (δ:ℝ) ^ (-(1:ℝ)) * (δ:ℝ) ^ (-((2*n : ℕ) : ℝ)) := by
          gcongr
      _ = (δ:ℝ) ^ (-((2 * n + 1 : ℕ) : ℝ)) := h4
  obtain ⟨s', hs's₀, V', hVto, hVshade, hcardR, hfullR, h𝒱⟩ :=
    hrefine hδ0 hδδR s₀ T (fun i hi => hfam.1 i (hs₀s hi)) hcards₀
  obtain ⟨𝒱⟩ := h𝒱
  have hs's : s' ⊆ s := hs's₀.trans hs₀s
  -- both refinements are nonempty
  have hs₀ne : s₀.Nonempty := by
    rcases s₀.eq_empty_or_nonempty with rfl | h
    · exact absurd (le_antisymm (by simpa using hcard₀) bot_le) hcardne
    · exact h
  have hs'ne : s'.Nonempty := by
    rcases s'.eq_empty_or_nonempty with rfl | h
    · exfalso
      have h0 : ((s₀.card : ℕ) : ℝ) ≤ 0 := by simpa using hcardR
      have : s₀.card = 0 := by
        have : ((s₀.card : ℕ) : ℝ) = 0 := le_antisymm h0 (by positivity)
        exact_mod_cast this
      exact absurd (Finset.card_eq_zero.mp this) (Finset.nonempty_iff_ne_empty.mp hs₀ne)
    · exact h
  -- the shade band survives to `s'`
  have hcarV' : ∀ i ∈ s', volume ((V' i).toShadedBody).carrier = tubeVolume δ :=
    fun i _ => volume_carrier_eq_tubeVolume V' i
  have hfull_s'T : ENNReal.ofReal ((δ:ℝ)^η) / 2
      ≤ ShadedBody.fullness' s' (fun i => (T i).toShadedBody) :=
    ShadedBody.le_fullness'_of_shade_band (fun i => (T i).toShadedBody) hvol0.ne' hvoltop hs'ne
      (fun i hi => hcar i (hs's hi)) (fun i hi => hband₀ i (hs's₀ hi))
  -- and passes to the refined shadings, at the price of the refinement loss
  have hmulpow : ∀ a b : ℝ, ENNReal.ofReal ((δ:ℝ)^a) * ENNReal.ofReal ((δ:ℝ)^b)
      = ENNReal.ofReal ((δ:ℝ)^(a+b)) := by
    intro a b
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hδR0.le _), ← Real.rpow_add hδR0]
  have hstep : ENNReal.ofReal ((δ:ℝ)^(-η)) * ENNReal.ofReal ((δ:ℝ)^(3*η))
      ≤ ENNReal.ofReal ((δ:ℝ)^η) / 2 := by
    rw [hmulpow]
    rw [ENNReal.le_div_iff_mul_le (Or.inl two_ne_zero) (Or.inl (by norm_num))]
    rw [show ((2:ENNReal)) = ENNReal.ofReal 2 by simp,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hδR0.le _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : (δ:ℝ)^(-η + 3*η) = (δ:ℝ)^(2*η) := by ring_nf
    rw [h1]
    have h2 : (δ:ℝ)^(2*η) = (δ:ℝ)^η * (δ:ℝ)^η := by
      rw [← Real.rpow_add hδR0]; ring_nf
    rw [h2]
    nlinarith [hlampos, hhalf]
  have hfull_V' : ENNReal.ofReal ((δ:ℝ)^(3*η))
      ≤ ShadedBody.fullness' s' (fun i => (V' i).toShadedBody) := by
    have hc0 : ENNReal.ofReal ((δ:ℝ)^(-η)) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hδR0 _)).ne'
    have hchain : ENNReal.ofReal ((δ:ℝ)^(-η)) * ENNReal.ofReal ((δ:ℝ)^(3*η))
        ≤ ENNReal.ofReal ((δ:ℝ)^(-η)) * ShadedBody.fullness' s' (fun i => (V' i).toShadedBody) :=
      le_trans (le_trans hstep hfull_s'T) hfullR
    refine (ENNReal.mul_le_mul_iff_left hc0 ENNReal.ofReal_ne_top).mp ?_
    rw [mul_comm _ (ENNReal.ofReal ((δ:ℝ)^(-η))), mul_comm _ (ENNReal.ofReal ((δ:ℝ)^(-η)))]
    exact hchain
  -- the Katz--Tao data
  have hδlt1 : (δ:ℝ) < 1 := by
    rcases lt_or_eq_of_le hδ1R with h | h
    · exact h
    · exfalso; rw [h, Real.one_rpow] at hhalf; norm_num at hhalf
  set K : NNReal := rpowNN δ (-η) with hKdef
  have hK1 : (1:NNReal) ≤ K := by
    have : (1:ℝ) ≤ (δ:ℝ) ^ (-η) := by
      rw [show (1:ℝ) = (δ:ℝ) ^ (0:ℝ) from (Real.rpow_zero _).symm]
      exact Real.rpow_le_rpow_of_exponent_ge hδR0 hδ1R (by linarith)
    rw [hKdef]
    exact_mod_cast this
  have hKpow : ∀ m : ℕ, ((K ^ m : NNReal) : ENNReal) = ENNReal.ofReal ((δ:ℝ) ^ (-((m:ℝ) * η))) := by
    intro m
    rw [← ENNReal.ofReal_coe_nnreal]
    congr 1
    push_cast [hKdef, coe_rpowNN]
    rw [← Real.rpow_natCast ((δ:ℝ) ^ (-η)) m, ← Real.rpow_mul hδR0.le]
    congr 1
    ring
  have habsorb : ∀ Q : NNReal, Q ≤ ktBridgeConst →
      ((Q * K ^ p : NNReal) : ENNReal) ≤ ENNReal.ofReal ((δ:ℝ) ^ (-ηB)) := by
    intro Q hQ
    have h1 : ((Q * K ^ p : NNReal) : ENNReal)
        = (Q : ENNReal) * ENNReal.ofReal ((δ:ℝ) ^ (-((p:ℝ) * η))) := by
      rw [ENNReal.coe_mul, hKpow p]
    rw [h1]
    refine le_trans (?_ : _ ≤ (ktBridgeConst : ENNReal) * ENNReal.ofReal ((δ:ℝ) ^ (-((p:ℝ) * η))))
      (hδA hδ0 hδA' hδlt1)
    gcongr
  -- leaf density
  have hleaf := maxDensity_leaves_le_of_katzTaoEveryScale_of_family hδ0 hδ1 hK1 hfam hKT
  rw [← hn] at hleaf
  set QL : NNReal :=
    StickyKakeya.ktLeafCmpConst (E := Space3) * Real.toNNReal Kakeya.edInTubeConst with hQLdef
  have hDeq : StickyKakeya.ktLeafCmpConst (E := Space3) * wzInTubeCap K * K ^ n * K
      = QL * K ^ (n + 7) := by
    rw [hQLdef, wzInTubeCap]; ring
  have hleafQ : StickyKakeya.ktLeafCmpConst (E := Space3) * wzInTubeCap K * K ^ n * K
      ≤ ktBridgeConst * K ^ p := by
    rw [hDeq]
    exact mul_le_mul' (le_trans (le_max_left _ _) (le_max_right _ _))
      (pow_le_pow_right₀ hK1 (by omega))
  have hDens : Kakeya.maxDensity s (fun i => ((T i).toTube).toConvexSpaceBody)
      ≤ ENNReal.ofReal ((δ:ℝ)^(-ηB)) :=
    le_trans hleaf (le_trans (ENNReal.coe_le_coe.mpr hleafQ) (habsorb ktBridgeConst le_rfl))
  -- node density
  obtain ⟨hNpos, hδ16, -⟩ := hG hδ0 hδδG
  have hKTV' : KatzTaoEveryScale.{u} s V' K := katzTaoEveryScale_congr hVto hKT
  have hcongrbody : ∀ i, ((V' i).toTube).toConvexSpaceBody = ((T i).toTube).toConvexSpaceBody :=
    fun i => by rw [hVto i]
  have hDensV' : Kakeya.maxDensity s (fun i => ((V' i).toTube).toConvexSpaceBody)
      ≤ ((StickyKakeya.ktLeafCmpConst (E := Space3) * wzInTubeCap K * K ^ n * K : NNReal)
          : ENNReal) := by
    rw [Kakeya.maxDensity_congr (fun i _ => hcongrbody i)]
    exact hleaf
  have hNodes := isKatzTaoAtEveryScale_of_katzTaoEveryScale hδ0 hδ1 hNpos hδ16 hs's hs'ne
    𝒱.tubeUniform hK1 hKTV' hDensV'
  have hNodeQ : StickyKakeya.ktNodeCmpConst (E := Space3)
        * ShadedTube.ssfUniformConst n * K ^ (3 * n) * K ≤ ktBridgeConst * K ^ p := by
    have heq : StickyKakeya.ktNodeCmpConst (E := Space3)
          * ShadedTube.ssfUniformConst n * K ^ (3 * n) * K
        = (StickyKakeya.ktNodeCmpConst (E := Space3) * ShadedTube.ssfUniformConst n)
            * K ^ (3 * n + 1) := by
      rw [pow_succ]; ring
    rw [heq]
    exact mul_le_mul' (le_max_left _ _) (pow_le_pow_right₀ hK1 (by omega))
  have hNode2Q : Kakeya.MultiScaleFac.tubeVolRatio (E := Space3)
        * (StickyKakeya.ktLeafCmpConst (E := Space3) * wzInTubeCap K * K ^ n * K)
      ≤ ktBridgeConst * K ^ p := by
    rw [hDeq, ← mul_assoc]
    exact mul_le_mul' (le_trans (le_max_right _ _) (le_max_right _ _))
      (pow_le_pow_right₀ hK1 (by omega))
  have hNodes' : 𝒱.tubeUniform.IsKatzTaoAtEveryScale (ENNReal.ofReal ((δ:ℝ)^(-ηB))) :=
    hNodes.mono (max_le
      (le_trans (ENNReal.coe_le_coe.mpr hNodeQ) (habsorb ktBridgeConst le_rfl))
      (le_trans (ENNReal.coe_le_coe.mpr hNode2Q) (habsorb ktBridgeConst le_rfl)))
  -- the leaf-scale Katz--Tao hypothesis of the estimate
  have hIsKT : ConvexSpaceBody.IsKatzTao s' (fun i => (V' i).toConvexSpaceBody)
      (ENNReal.ofReal ((δ:ℝ)^(-ηB))) := by
    have h1 : Kakeya.maxDensity s' (fun i => (V' i).toConvexSpaceBody)
        = Kakeya.maxDensity s' (fun i => ((T i).toTube).toConvexSpaceBody) :=
      Kakeya.maxDensity_congr (fun i _ => hcongrbody i)
    rw [ConvexSpaceBody.IsKatzTao_def, h1]
    exact le_trans (Kakeya.maxDensity_mono _ hs's) hDens
  have hball' : ∀ i ∈ s', (V' i).carrier ⊆ Metric.closedBall (0:Space3) 1 := by
    intro i hi
    have h2 : (V' i).carrier = (T i).carrier := by
      show ((V' i).toTube).carrier = ((T i).toTube).carrier
      rw [hVto i]
    rw [h2]
    exact hfam.1 i (hs's hi)
  have hfullB : ENNReal.ofReal ((δ:ℝ)^ηB)
      ≤ ShadedBody.fullness' s' (fun i => (V' i).toShadedBody) :=
    le_trans (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_ge hδR0 hδ1R hη3)) hfull_V'
  have hmulti := hSKT hδ0 hδB' s' V' hball' 𝒱 hfullB hIsKT hNodes'
  -- transfer the multiplicity back to the whole family
  have hinv : (ENNReal.ofReal ((δ:ℝ)^η))⁻¹ = ENNReal.ofReal ((δ:ℝ)^(-η)) := by
    rw [← ENNReal.ofReal_inv_of_pos hlampos, ← Real.rpow_neg hδR0.le]
  have hK2 : (2:ℝ) ≤ (δ:ℝ)^(-η) := by
    rw [Real.rpow_neg hδR0.le]
    rw [le_inv_comm₀ (by norm_num) hlampos]
    simpa using hhalf
  have hcardR' : (s₀.card : ENNReal) ≤ ENNReal.ofReal ((δ:ℝ)^(-η)) * (s'.card : ENNReal) := by
    have h1 : ENNReal.ofReal ((s₀.card : ℝ))
        ≤ ENNReal.ofReal ((δ:ℝ)^(-η) * (s'.card:ℝ)) := ENNReal.ofReal_le_ofReal hcardR
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg hδR0.le _)] at h1
    simpa using h1
  have h2div : (2:ENNReal) / ENNReal.ofReal ((δ:ℝ)^η)
      = 2 * ENNReal.ofReal ((δ:ℝ)^(-η)) := by
    rw [ENNReal.div_eq_inv_mul, hinv, mul_comm]
  have hcoef : (2:ENNReal) * ENNReal.ofReal ((δ:ℝ)^(-η)) * ENNReal.ofReal ((δ:ℝ)^(-η))
      ≤ ENNReal.ofReal ((δ:ℝ)^(-(3*η))) := by
    rw [mul_assoc, hmulpow]
    rw [show ((2:ENNReal)) = ENNReal.ofReal 2 by simp,
      ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hb : (δ:ℝ)^(-η + -η) = (δ:ℝ)^(-(3*η)) * (δ:ℝ)^(η) := by
      rw [← Real.rpow_add hδR0]; congr 1; ring
    have hc : (δ:ℝ)^(-(3*η)) = (δ:ℝ)^(-η) * (δ:ℝ)^(-η + -η) := by
      rw [← Real.rpow_add hδR0]; congr 1; ring
    rw [hc]
    have hpos : (0:ℝ) < (δ:ℝ)^(-η + -η) := Real.rpow_pos_of_pos hδR0 _
    nlinarith [hK2, hpos]
  have hcardFinal : (s.card : ENNReal)
      ≤ ENNReal.ofReal ((δ:ℝ)^(-(3*η))) * (s'.card : ENNReal) := by
    calc (s.card : ENNReal) ≤ 2 / ENNReal.ofReal ((δ:ℝ)^η) * (s₀.card : ENNReal) := hcard₀
      _ = 2 * ENNReal.ofReal ((δ:ℝ)^(-η)) * (s₀.card : ENNReal) := by rw [h2div]
      _ ≤ 2 * ENNReal.ofReal ((δ:ℝ)^(-η))
            * (ENNReal.ofReal ((δ:ℝ)^(-η)) * (s'.card : ENNReal)) := by gcongr
      _ = 2 * ENNReal.ofReal ((δ:ℝ)^(-η)) * ENNReal.ofReal ((δ:ℝ)^(-η))
            * (s'.card : ENNReal) := by ring
      _ ≤ ENNReal.ofReal ((δ:ℝ)^(-(3*η))) * (s'.card : ENNReal) := by gcongr
  have hlam3 : ENNReal.ofReal ((δ:ℝ)^(3*η)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hδR0 _)).ne'
  have htrans := ShadedBody.multiplicity_le_of_subfamily_of_fullness
    (fun i => (T i).toShadedBody) (fun i => (V' i).toShadedBody) hs's
    (fun i _ => hVshade i) hvoltop hcar hcarV'
    (C := ENNReal.ofReal ((δ:ℝ)^(-(3*η)))) (lam := ENNReal.ofReal ((δ:ℝ)^(3*η)))
    hlam3 ENNReal.ofReal_ne_top hcardFinal hfull_V'
  have hdivC : ENNReal.ofReal ((δ:ℝ)^(-(3*η))) / ENNReal.ofReal ((δ:ℝ)^(3*η))
      = ENNReal.ofReal ((δ:ℝ)^(-(6*η))) := by
    rw [← ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos hδR0 _)]
    congr 1
    rw [div_eq_mul_inv, ← Real.rpow_neg hδR0.le, ← Real.rpow_add hδR0]
    congr 1
    ring
  rw [hdivC] at htrans
  refine le_trans htrans (le_trans (mul_le_mul_left' hmulti _) ?_)
  rw [hmulpow]
  rw [← coe_rpowNN_ennreal hδ0 (-ε), ← ENNReal.ofReal_coe_nnreal, coe_rpowNN]
  exact ENNReal.ofReal_le_ofReal
    (Real.rpow_le_rpow_of_exponent_ge hδR0 hδ1R (by linarith))

/-- **Wang--Zahl Theorem `katzTaoEveryScaleStickyKakeyaThm` (:4745)**, the
volume form printed by the source at :4750.

Sticky Kakeya for tubes satisfying the Katz--Tao Convex Wolff Axioms at every
scale: such a family has essentially full shaded volume `(#T)|T|`.

Derived here from the multiplicity form
`katzTaoEveryScale_multiplicity_le` ([GWZ, Theorem 7.3(B)]) by the two
elementary steps the source's own proof leaves implicit:

* *small `delta`.*  `mu = (sum_T |Y(T)|)/|U Y(T)|` and `delta^eta`-density give
  `|U Y(T)| >= delta^{eta} (#T)|T| / delta^{-eps/2} >= delta^{eps} (#T)|T|`,
  using `eta <= eps/2`;
* *`delta` bounded away from `0`.*  This is the corner the source dispatches at
  :5195 ("provided we select `kappa > 0` sufficiently small").  Here it is
  proved rather than assumed: `|U Y(T)| >= delta^{eta}|T|` always (each shading
  lies in the union, so `sum_T |Y(T)| <= (#T)|U Y(T)|`), while `#T` is capped by
  the crude packing bound `wzPackCap delta_0` on `[delta_0,1]`, so a single
  `kappa` depending on `(delta_0, eta)` serves the whole corner. -/
theorem stickyKakeyaEveryScale (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, ∃ κ : NNReal, 0 < η ∧ 0 < κ ∧
      ∀ (δ : NNReal), 0 < δ → δ ≤ 1 →
        ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ Space3),
          IsTubeShadingFamily s T →
          IsDense s T (rpowNN δ η) →
          KatzTaoEveryScale.{u} s T (rpowNN δ (-η)) →
          WZFullBound ε κ s T := by
  obtain ⟨η, δ₀, hη, hηε, hδ₀0, hδ₀1, hmult⟩ :=
    katzTaoEveryScale_multiplicity_le.{u} (ε / 2) (by linarith)
  have hcapne : (wzPackCap δ₀) ≠ 0 := (wzPackCap_pos δ₀).ne'
  refine ⟨η, min 1 (rpowNN δ₀ η / wzPackCap δ₀), hη, ?_, ?_⟩
  · refine lt_min zero_lt_one ?_
    exact div_pos (by
      have : (0 : ℝ) < (δ₀ : ℝ) ^ η := Real.rpow_pos_of_pos (by exact_mod_cast hδ₀0) η
      exact_mod_cast this) (wzPackCap_pos δ₀)
  intro δ hδ0 hδ1 ι s T hfam hdense hKT
  have hδ0E : (δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hδ0.ne'
  have hδtE : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hδ1E : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
  have hdenseE : (δ : ENNReal) ^ η * ((s.card : ENNReal) * tubeVolume δ)
      ≤ ∑ i ∈ s, volume (T i).shade := by
    have := hdense
    rw [IsDense, sum_volume_carrier] at this
    rwa [coe_rpowNN_ennreal hδ0 η] at this
  have hκ1 : ((min 1 (rpowNN δ₀ η / wzPackCap δ₀) : NNReal) : ENNReal) ≤ 1 := by
    exact_mod_cast min_le_left (1 : NNReal) _
  by_cases hsmall : δ ≤ δ₀
  · -- the main regime
    have hmul := hmult δ hδ0 hsmall s T hfam hdense hKT
    rw [ShadedBody.multiplicity_le_iff] at hmul
    have hkey : (δ : ENNReal) ^ (ε / 2) * ((δ : ENNReal) ^ η *
        ((s.card : ENNReal) * tubeVolume δ))
        ≤ volume (ShadedBody.iUnionShade s fun i => (T i).toShadedBody) := by
      calc (δ : ENNReal) ^ (ε / 2) * ((δ : ENNReal) ^ η *
              ((s.card : ENNReal) * tubeVolume δ))
          ≤ (δ : ENNReal) ^ (ε / 2) * ∑ i ∈ s, volume (T i).shade := by gcongr
        _ ≤ (δ : ENNReal) ^ (ε / 2) *
              ((δ : ENNReal) ^ (-(ε / 2)) *
                volume (ShadedBody.iUnionShade s fun i => (T i).toShadedBody)) := by gcongr
        _ = volume (ShadedBody.iUnionShade s fun i => (T i).toShadedBody) := by
            rw [← mul_assoc, ← ENNReal.rpow_add _ _ hδ0E hδtE]
            simp
    refine le_trans ?_ hkey
    have hpow : ((min 1 (rpowNN δ₀ η / wzPackCap δ₀) : NNReal) : ENNReal) *
        (δ : ENNReal) ^ ε ≤ (δ : ENNReal) ^ (ε / 2) * (δ : ENNReal) ^ η := by
      rw [← ENNReal.rpow_add _ _ hδ0E hδtE]
      calc ((min 1 (rpowNN δ₀ η / wzPackCap δ₀) : NNReal) : ENNReal) * (δ : ENNReal) ^ ε
          ≤ 1 * (δ : ENNReal) ^ ε := by gcongr
        _ = (δ : ENNReal) ^ ε := one_mul _
        _ ≤ (δ : ENNReal) ^ (ε / 2 + η) :=
            ENNReal.rpow_le_rpow_of_exponent_ge hδ1E (by linarith)
    calc ((min 1 (rpowNN δ₀ η / wzPackCap δ₀) : NNReal) : ENNReal) * (δ : ENNReal) ^ ε *
            (s.card : ENNReal) * tubeVolume δ
        = (((min 1 (rpowNN δ₀ η / wzPackCap δ₀) : NNReal) : ENNReal) * (δ : ENNReal) ^ ε) *
            ((s.card : ENNReal) * tubeVolume δ) := by ring
      _ ≤ ((δ : ENNReal) ^ (ε / 2) * (δ : ENNReal) ^ η) *
            ((s.card : ENNReal) * tubeVolume δ) := by gcongr
      _ = (δ : ENNReal) ^ (ε / 2) * ((δ : ENNReal) ^ η *
            ((s.card : ENNReal) * tubeVolume δ)) := by ring
  · -- the corner `delta_0 < delta <= 1`
    rcases Finset.eq_empty_or_nonempty s with rfl | hs
    · simp [WZFullBound]
    have hδ₀δ : δ₀ ≤ δ := le_of_lt (lt_of_not_ge hsmall)
    have hcard : (s.card : NNReal) ≤ wzPackCap δ₀ :=
      card_le_wzPackCap hδ₀0 hδ₀δ s T hδ0 hfam
    have hcardE : (s.card : ENNReal) ≤ (wzPackCap δ₀ : ENNReal) := by exact_mod_cast hcard
    have hcard0 : (s.card : ENNReal) ≠ 0 := by
      simpa using (Finset.card_pos.mpr hs).ne'
    have hcardt : (s.card : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
    -- each shading lies in the union
    have hsum : ∑ i ∈ s, volume (T i).shade
        ≤ (s.card : ENNReal) *
            volume (ShadedBody.iUnionShade s fun i => (T i).toShadedBody) := by
      calc ∑ i ∈ s, volume (T i).shade
          ≤ ∑ _i ∈ s, volume (ShadedBody.iUnionShade s fun i => (T i).toShadedBody) :=
            Finset.sum_le_sum fun i hi =>
              measure_mono fun x hx => Set.mem_biUnion hi hx
        _ = (s.card : ENNReal) *
              volume (ShadedBody.iUnionShade s fun i => (T i).toShadedBody) := by
            simp [Finset.sum_const, nsmul_eq_mul]
    have hcancel : (δ : ENNReal) ^ η * tubeVolume δ
        ≤ volume (ShadedBody.iUnionShade s fun i => (T i).toShadedBody) := by
      have h1 : ((δ : ENNReal) ^ η * tubeVolume δ) * (s.card : ENNReal)
          ≤ volume (ShadedBody.iUnionShade s fun i => (T i).toShadedBody) *
              (s.card : ENNReal) := by
        calc ((δ : ENNReal) ^ η * tubeVolume δ) * (s.card : ENNReal)
            = (δ : ENNReal) ^ η * ((s.card : ENNReal) * tubeVolume δ) := by ring
          _ ≤ ∑ i ∈ s, volume (T i).shade := hdenseE
          _ ≤ (s.card : ENNReal) *
                volume (ShadedBody.iUnionShade s fun i => (T i).toShadedBody) := hsum
          _ = volume (ShadedBody.iUnionShade s fun i => (T i).toShadedBody) *
                (s.card : ENNReal) := by ring
      exact (ENNReal.mul_le_mul_iff_left hcard0 hcardt).mp h1
    have hδ₀η : ((rpowNN δ₀ η : NNReal) : ENNReal) ≤ (δ : ENNReal) ^ η := by
      rw [coe_rpowNN_ennreal hδ₀0 η]
      exact ENNReal.rpow_le_rpow (by exact_mod_cast hδ₀δ) hη.le
    have hkapcap : ((min 1 (rpowNN δ₀ η / wzPackCap δ₀) : NNReal) : ENNReal) *
        (wzPackCap δ₀ : ENNReal) ≤ ((rpowNN δ₀ η : NNReal) : ENNReal) := by
      have : (min 1 (rpowNN δ₀ η / wzPackCap δ₀) : NNReal) * wzPackCap δ₀
          ≤ rpowNN δ₀ η := by
        calc (min 1 (rpowNN δ₀ η / wzPackCap δ₀) : NNReal) * wzPackCap δ₀
            ≤ (rpowNN δ₀ η / wzPackCap δ₀) * wzPackCap δ₀ := by
              gcongr
              exact min_le_right _ _
          _ = rpowNN δ₀ η := div_mul_cancel₀ _ hcapne
      exact_mod_cast this
    have hδε : (δ : ENNReal) ^ ε ≤ 1 :=
      ENNReal.rpow_le_one hδ1E hε.le
    calc ((min 1 (rpowNN δ₀ η / wzPackCap δ₀) : NNReal) : ENNReal) * (δ : ENNReal) ^ ε *
            (s.card : ENNReal) * tubeVolume δ
        ≤ ((min 1 (rpowNN δ₀ η / wzPackCap δ₀) : NNReal) : ENNReal) * 1 *
            (wzPackCap δ₀ : ENNReal) * tubeVolume δ := by gcongr
      _ = (((min 1 (rpowNN δ₀ η / wzPackCap δ₀) : NNReal) : ENNReal) *
            (wzPackCap δ₀ : ENNReal)) * tubeVolume δ := by ring
      _ ≤ ((rpowNN δ₀ η : NNReal) : ENNReal) * tubeVolume δ := by gcongr
      _ ≤ (δ : ENNReal) ^ η * tubeVolume δ := by gcongr
      _ ≤ volume (ShadedBody.iUnionShade s fun i => (T i).toShadedBody) := hcancel






/-! ### A defect in the source's final display -/

/-- The tube volume `|T|` is at most its own square root exactly when `|T| <= 1`,
which holds for every scale small enough that a `delta`-tube has volume at most
one. -/
theorem tubeVolume_le_sqrt_tubeVolume {δ : NNReal} (h : tubeVolume δ ≤ 1) :
    tubeVolume δ ≤ (tubeVolume δ) ^ (1 / 2 : ℝ) := by
  conv_lhs => rw [← ENNReal.rpow_one (tubeVolume δ)]
  exact ENNReal.rpow_le_rpow_of_exponent_ge h (by norm_num)

/-- **Source defect, `250224e_K3.tex:5204`.**

The final display of the proof of Proposition `improvingProp` prints

  `|U Y(T)| >~ delta^{omega - min(alpha_2, omega/2)} (#T)|T| ((#T)|T|)^{-sigma}`,

with `((#T)|T|)^{-sigma}` as the last factor.  Assertion `D(sigma, omega')`
(Definition :200) and both lemmas that feed this display --- Conclusion (A) of
`bigVolumeOrKatzTaoAllScales` (:5174) and Conclusion (A) of
`refinedInductionOnScaleProp` (:4561) --- carry `((#T)|T|^{1/2})^{-sigma}`
instead.

The two are not interchangeable, and the printed one is the *stronger*
assertion: `x |-> x^{-sigma}` is antitone and `(#T)|T| <= (#T)|T|^{1/2}`
whenever `|T| <= 1`.  So as printed the display claims a bound the cited
lemmas do not supply --- it is off by a factor `|T|^{-sigma/2} ~ delta^{-sigma}`.
The intended factor is the Wang--Zahl currency `wzCurrency = (#T)|T|^{1/2}`,
and with that correction the deduction of `D(sigma, omega - g)` goes through;
this file uses the corrected form throughout.

The lemma below is the mechanical witness: the printed factor dominates the
correct one. -/
theorem source_display_5204_overclaims {δ : NNReal} (hV : tubeVolume δ ≤ 1)
    {σ : ℝ} (hσ : 0 ≤ σ) (n : ℕ) :
    (wzCurrency δ n) ^ (-σ) ≤ ((n : ENNReal) * tubeVolume δ) ^ (-σ) := by
  refine rpow_le_rpow_of_nonpos ?_ (by linarith)
  rw [wzCurrency]
  gcongr
  exact tubeVolume_le_sqrt_tubeVolume hV

/-! ### The gain bookkeeping: from the dichotomy to Assertion `D` -/

/-- The source's proof of Proposition 1.7 (:5197--5210), in full.

Given the dichotomy (Lemma `bigVolumeOrKatzTaoAllScales` composed with the
sticky Kakeya theorem at every scale), Assertion `D` holds at the improved
exponent `omega - min alpha (omega/4)`.

The only nonformal step of the source's display is the passage from the
sticky branch, whose bound `delta^{omega/2}(#T)|T|` carries no factor
`((#T)|T|^{1/2})^{-sigma}`, to the shape of Assertion `D`.  That is exactly
where the *lower* currency bound `(#T)|T|^{1/2} >= C^{-1} delta^{eta}`
(the observation at :225 of the source) enters: it converts the missing
factor into a `delta^{-eta sigma}` loss, which the hypothesis
`eta * sigma <= omega / 4` pays for out of the gain. -/
theorem assertionD_of_dichotomy {C : NNReal} (hC1 : 1 ≤ C)
    (hlow : CurrencyLowerBound.{u} C) {σ ω α : ℝ} {κ : NNReal} {η : ℝ}
    (hσ0 : 0 ≤ σ) (hω0 : 0 < ω) (hα0 : 0 < α) (hκ0 : 0 < κ) (hη0 : 0 < η)
    (hησ : η * σ ≤ ω / 4) (hdich : WZDichotomy.{u} σ ω α κ η) :
    AssertionD.{u} σ (ω - min α (ω / 4)) := by
  have hC0 : (C : NNReal) ≠ 0 := by
    intro h; rw [h] at hC1; exact absurd hC1 (by norm_num)
  have hCe0 : (C : ENNReal) ≠ 0 := by exact_mod_cast hC0
  have hCetop : (C : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hCs0 : ((C : ENNReal) ^ σ) ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hCe0) hCetop).ne'
  have hCstop : ((C : ENNReal) ^ σ) ≠ ⊤ := ENNReal.rpow_ne_top_of_ne_zero hCe0 hCetop
  have hCs1 : (1 : NNReal) ≤ C ^ σ := NNReal.one_le_rpow hC1 hσ0
  set g : ℝ := min α (ω / 4) with hgdef
  have hg0 : 0 < g := lt_min hα0 (by linarith)
  have hgα : g ≤ α := min_le_left _ _
  have hgω : g ≤ ω / 4 := min_le_right _ _
  set κ' : NNReal := κ / C ^ σ with hκ'def
  have hκ'0 : 0 < κ' := div_pos hκ0 (lt_of_lt_of_le zero_lt_one hCs1)
  have hκ'le : κ' ≤ κ := div_le_self (le_of_lt hκ0) hCs1
  have hcoe : ((κ' : NNReal) : ENNReal) * (C : ENNReal) ^ σ = (κ : ENNReal) := by
    rw [hκ'def, ENNReal.coe_div (by positivity), ENNReal.coe_rpow_of_ne_zero hC0]
    exact ENNReal.div_mul_cancel hCs0 hCstop
  intro ε hε
  refine ⟨κ', η, hκ'0, hη0, ?_⟩
  intro δ hδ0 ι s T hfam hdense hm hell
  by_cases hs : s.Nonempty
  · by_cases hδ1 : δ ≤ 1
    · have hδe0 : (δ : ENNReal) ≠ 0 := by
        simpa using hδ0.ne'
      have hδetop : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
      have hδe1 : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
      have hadm : WZAdmissible.{u} s T η := ⟨hfam, hdense, hm, hell⟩
      rcases hdich δ hδ0 hδ1 s T hadm with hA | hB
      · -- Conclusion (A): the improved bound already has the right shape.
        rw [WZGainBound, wzCurrency] at hA
        refine le_trans ?_ hA
        have hexp : (δ : ENNReal) ^ (ω - g + ε) ≤ (δ : ENNReal) ^ (ω - α) :=
          ENNReal.rpow_le_rpow_of_exponent_ge hδe1 (by linarith)
        have : ((κ' : NNReal) : ENNReal) ≤ ((κ : NNReal) : ENNReal) := by
          exact_mod_cast hκ'le
        gcongr
      · -- Conclusion (B): the sticky Kakeya branch, paid for by the currency bound.
        rw [WZFullBound] at hB
        refine le_trans ?_ hB
        have hXlow : ((C : ENNReal))⁻¹ * (δ : ENNReal) ^ η ≤ wzCurrency δ s.card :=
          hlow hδ0 hδ1 hη0 s T hs hfam hm hell
        have hdpow_ne : (δ : ENNReal) ^ η ≠ ⊤ :=
          ENNReal.rpow_ne_top_of_ne_zero hδe0 hδetop
        have hXbound : (wzCurrency δ s.card) ^ (-σ) ≤
            (C : ENNReal) ^ σ * (δ : ENNReal) ^ (-(η * σ)) := by
          refine le_trans (rpow_le_rpow_of_nonpos hXlow (by linarith)) ?_
          rw [ENNReal.mul_rpow_of_ne_top (by simp [hCe0]) hdpow_ne]
          have h1 : ((C : ENNReal))⁻¹ ^ (-σ) = (C : ENNReal) ^ σ := by
            rw [ENNReal.inv_rpow, ENNReal.rpow_neg, inv_inv]
          have h2 : ((δ : ENNReal) ^ η) ^ (-σ) = (δ : ENNReal) ^ (-(η * σ)) := by
            rw [← ENNReal.rpow_mul]
            ring_nf
          rw [h1, h2]
        calc
          ((κ' : NNReal) : ENNReal) * (δ : ENNReal) ^ (ω - g + ε) * (s.card : ENNReal) *
                tubeVolume δ *
                (((s.card : ENNReal) * tubeVolume δ ^ (1 / 2 : ℝ)) ^ (-σ))
              ≤ ((κ' : NNReal) : ENNReal) * (δ : ENNReal) ^ (ω - g + ε) * (s.card : ENNReal) *
                tubeVolume δ * ((C : ENNReal) ^ σ * (δ : ENNReal) ^ (-(η * σ))) := by
                have := hXbound
                rw [wzCurrency] at this
                gcongr
          _ = (((κ' : NNReal) : ENNReal) * (C : ENNReal) ^ σ) *
                ((δ : ENNReal) ^ (ω - g + ε) * (δ : ENNReal) ^ (-(η * σ))) *
                (s.card : ENNReal) * tubeVolume δ := by
                ring
          _ ≤ (κ : ENNReal) * (δ : ENNReal) ^ (ω / 2) * (s.card : ENNReal) * tubeVolume δ := by
                rw [← ENNReal.rpow_add _ _ hδe0 hδetop, hcoe]
                have hexp : (δ : ENNReal) ^ (ω - g + ε + -(η * σ)) ≤ (δ : ENNReal) ^ (ω / 2) :=
                  ENNReal.rpow_le_rpow_of_exponent_ge hδe1 (by linarith)
                gcongr
    · -- `delta > 1` is vacuous: the Katz--Tao constant of a nonempty family is at least one.
      have hm1 : 1 ≤ katzTaoConvexWolffConstant s T :=
        one_le_katzTaoConvexWolffConstant_of_nonempty hδ0 s T hs
      have hdelta_gt : (1 : ENNReal) < (δ : ENNReal) := by
        exact_mod_cast lt_of_not_ge hδ1
      have hpow_lt : (δ : ENNReal) ^ (-η) < 1 :=
        ENNReal.rpow_lt_one_of_one_lt_of_neg hdelta_gt (by linarith)
      exact ((not_lt_of_ge (hm1.trans hm)) hpow_lt).elim
  · have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    subst hs0
    simp [iUnionShade_empty]

/-! ### Assembling the dichotomy from the two leaves -/





end

end Kakeya.WangZahl

#print axioms Kakeya.WangZahl.wzPackCap_pos
#print axioms Kakeya.WangZahl.card_le_wzPackCap
#print axioms Kakeya.WangZahl.WZAdmissible.mono
#print axioms Kakeya.WangZahl.WZDichotomy.mono
#print axioms Kakeya.WangZahl.IsWZRefinement.isDense
#print axioms Kakeya.WangZahl.IsWZRefinement.card_ge
#print axioms Kakeya.WangZahl.IsWZRefinement.volume_iUnionShade_le
#print axioms Kakeya.WangZahl.IsWZRefinement.isTubeShadingFamily
#print axioms Kakeya.WangZahl.KatzTaoEveryScale.mono
#print axioms Kakeya.WangZahl.assertionD_of_dichotomy
#print axioms Kakeya.WangZahl.source_display_5204_overclaims
