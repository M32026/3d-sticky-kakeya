/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineHfacProducer
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineLevelBandDescent
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorShapeRoute
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineHfacFourProducer
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFourWayClosure
public import Kakeya.DimensionThree.MainLemma2.Reduction.LargeFamilyRewire
public import Kakeya.DimensionThree.MainLemma2.Reduction.Assembly
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineEveryScale

/-!
# The final assembly: `ML2Assembly.GeometricCoreAt` from `RefinedFloorSupplyAt`


-/

@[expose] public section

open MeasureTheory Metric ConvexSpaceBody ShadedBody
open scoped NNReal ENNReal Topology

namespace Kakeya.ML2Core

universe u v w

section RefinedPayload

variable {ι : Type*} {δ Cu : NNReal} {u : Finset ι}
  {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}

/-- **The payload row, over the whole filter.**  `Kakeya.ML2Core.RefinedFloorSupplyAt` at every
scale and every ambient family: the single row this assembly takes as a hypothesis. -/
def RefinedFloorPayload.{w'} (β ϖ ε₁ η' : ℝ) (gain dens : ℝ → ℝ) {C : NNReal} {Kl cl : ℕ}
    (Λf : NNReal → ℝ≥0∞) : Prop :=
  ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
    ∀ {ι : Type w'} (u : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (Cu : NNReal)
      (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu),
      RefinedFloorSupplyAt (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ η' gain dens (Λf δ) 𝒰

/-- Route (b)'s payload from the refined supply, pointwise in `δ`. -/
theorem floorPayloadTrichotomy_of_refinedFloorPayload.{w'} {β ϖ ε₁ η' h : ℝ} {gain dens : ℝ → ℝ}
    {C : NNReal} {Kl cl : ℕ} {Λf : NNReal → ℝ≥0∞}
    (hp : RefinedFloorPayload.{w'} (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ η' gain dens Λf) :
    FloorPayloadTrichotomy.{w'} (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ η' h gain dens Λf := by
  filter_upwards [hp] with δ hδ
  intro ι u T Cu 𝒰
  exact floorDataAtTrichotomy_of_refinedFloorSupply (hδ u T Cu 𝒰)

end RefinedPayload

/-! ## The restricted chain: the split must run on the leaves retained by `t₁` -/

section RestrictedChain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

variable {ι : Type u} {δ : NNReal} {t : Finset ι} {T : ι → Tube δ E} {N : ℕ} {σ : ℕ → NNReal}

/-- **A hierarchy restricts to any subfamily.**  Same nodes, same assignment, same tubes; only the
family shrinks.  This is the object the four-way split must run on: `Kakeya.ML2Core.HfacPostDropFour`
asks for `tτ' ⊆ t₁`, and `Kakeya.ML2Reduction.activeNodes` of the *ambient* chain is not inside `t₁`
— it is inside `t₁` exactly for the chain over the retained leaves. -/
def chainRestrictFamily (𝒞 : Tube.ChainCoverSystem t T N σ) {t' : Finset ι} (ht' : t' ⊆ t) :
    Tube.ChainCoverSystem t' T N σ where
  indexSet := 𝒞.indexSet
  assign := 𝒞.assign
  tube := 𝒞.tube
  assign_mem k hk i hi := 𝒞.assign_mem k hk i (ht' hi)
  le_tube_assign k hk i hi := 𝒞.le_tube_assign k hk i (ht' hi)
  nested k hk i hi j hj := 𝒞.nested k hk i (ht' hi) j (ht' hj)
  tube_nested k hk i hi := 𝒞.tube_nested k hk i (ht' hi)

@[simp] theorem chainRestrictFamily_indexSet (𝒞 : Tube.ChainCoverSystem t T N σ) {t' : Finset ι}
    (ht' : t' ⊆ t) (k : ℕ) : (chainRestrictFamily 𝒞 ht').indexSet k = 𝒞.indexSet k := rfl

@[simp] theorem chainRestrictFamily_assign (𝒞 : Tube.ChainCoverSystem t T N σ) {t' : Finset ι}
    (ht' : t' ⊆ t) (k : ℕ) : (chainRestrictFamily 𝒞 ht').assign k = 𝒞.assign k := rfl

@[simp] theorem chainRestrictFamily_tube (𝒞 : Tube.ChainCoverSystem t T N σ) {t' : Finset ι}
    (ht' : t' ⊆ t) (k : ℕ) : (chainRestrictFamily 𝒞 ht').tube k = 𝒞.tube k := rfl

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
/-- Active nodes of the restricted chain are active nodes of the ambient one. -/
theorem activeNodes_chainRestrictFamily_subset (𝒞 : Tube.ChainCoverSystem t T N σ)
    {t' : Finset ι} (ht' : t' ⊆ t) (k : ℕ) :
    ML2Reduction.activeNodes (chainRestrictFamily 𝒞 ht') k ⊆ ML2Reduction.activeNodes 𝒞 k := by
  classical
  intro j hj
  simp only [ML2Reduction.activeNodes, Finset.mem_filter] at hj ⊢
  refine ⟨hj.1, ?_⟩
  obtain ⟨i, hi⟩ := hj.2
  simp only [Tube.coverClass, Finset.mem_filter] at hi
  exact ⟨i, by simp only [Tube.coverClass, Finset.mem_filter]; exact ⟨ht' hi.1, hi.2⟩⟩

open Classical in
omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
/-- **The point of the restriction.**  With `t' = {i ∈ t | 𝒞.assign b i ∈ t₁}` the restricted
chain's level-`b` active nodes lie inside `t₁`, which is the containment
`Kakeya.ML2Core.HfacPostDropFour` demands of `tτ'`. -/
theorem activeNodes_chainRestrictFamily_subset_of_filter (𝒞 : Tube.ChainCoverSystem t T N σ)
    {t₁ : Finset ι} {b : ℕ}
    (ht' : ({i ∈ t | 𝒞.assign b i ∈ t₁} : Finset ι) ⊆ t) :
    ML2Reduction.activeNodes (chainRestrictFamily 𝒞 ht') b ⊆ t₁ := by
  classical
  intro j hj
  simp only [ML2Reduction.activeNodes, Finset.mem_filter] at hj
  obtain ⟨i, hi⟩ := hj.2
  simp only [Tube.coverClass, Finset.mem_filter] at hi
  obtain ⟨hit, hib⟩ := hi.1
  have : 𝒞.assign b i = j := hi.2
  exact this ▸ hib

omit [MeasurableSpace E] [BorelSpace E] in
/-- **The ancestor map does not see the restriction.**  On the restricted chain's active nodes,
`Kakeya.ML2Reduction.coarseNode` of the restriction agrees with that of the ambient chain: both
read `assign a` off a member of the class, and `Tube.ChainCoverSystem.assign_eq_of_le` makes the
reading member-independent. -/
theorem coarseNode_chainRestrictFamily (𝒞 : Tube.ChainCoverSystem t T N σ)
    {t' : Finset ι} (ht' : t' ⊆ t) {a b : ℕ} (hab : a ≤ b) (hbN : b ≤ N)
    {j : ι} (hj : j ∈ ML2Reduction.activeNodes (chainRestrictFamily 𝒞 ht') b) :
    ML2Reduction.coarseNode (chainRestrictFamily 𝒞 ht') a b j
      = ML2Reduction.coarseNode 𝒞 a b j := by
  classical
  simp only [ML2Reduction.activeNodes, Finset.mem_filter] at hj
  obtain ⟨i, hi⟩ := hj.2
  simp only [Tube.coverClass, Finset.mem_filter] at hi
  obtain ⟨hit', hij⟩ := hi
  subst hij
  exact (coarseNode_assign (chainRestrictFamily 𝒞 ht') hab hbN hit').trans
    (coarseNode_assign 𝒞 hab hbN (ht' hit')).symm

end RestrictedChain

/-! ## The `hfac` side: `HfacPostDropFour` from the four factor rows -/

section HfacProducer

open Tube

variable {ι : Type u} {δ Cu : NNReal} {u : Finset ι}
  {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}

open Classical in
/-- **The chain the split must run on**: the ambient hierarchy restricted to the leaves whose
level-`b` node is retained by `t₁`.  Its level-`b` active nodes lie inside `t₁`, which is what
`Kakeya.ML2Core.HfacPostDropFour` asks of `tτ'`. -/
noncomputable def retainedLeafChain
    (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
    (t₁ : Finset ι) (b : ℕ) :
    Tube.ChainCoverSystem ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)
      (fun i => (T i).toTube) (Tube.ssfGridLen δ) (Tube.gridScale δ (Tube.ssfGridLen δ)) :=
  chainRestrictFamily 𝒰.cover.toChain (Finset.filter_subset _ _)

open Classical in
/-- `Kakeya.ML2Core.coarseNode_chainRestrictFamily` at the retained-leaf chain, in the form the
rewrites need (the `def` is not unfolded by `rw`). -/
theorem coarseNode_retainedLeafChain
    (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
    (t₁ : Finset ι) {b c k : ℕ} (hck : c ≤ k) (hkN : k ≤ Tube.ssfGridLen δ)
    {j : ι} (hj : j ∈ ML2Reduction.activeNodes (retainedLeafChain 𝒰 t₁ b) k) :
    ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) c k j
      = ML2Reduction.coarseNode 𝒰.cover.toChain c k j :=
  coarseNode_chainRestrictFamily _ _ hck hkN hj

open Classical in
/-- **The four factor rows and the level-`p` ball row, at one instance of the split.**

These are the site side's obligations, in exactly the shape the translated three-scale split
consumes: `hballπ` (level `p`), `hfine` (leaf → `b`), `hmid` (`(p, b)`), `hpar` (`(a, p)`),
`hcoarse` (level `a`).  Everything is on `Kakeya.ML2Core.retainedLeafChain` and on the tubes
translated by the seam's `v`.

**Family:** `{i ∈ u | assign b i ∈ t₁}` under `retainedLeafChain 𝒰 t₁ b`.
**Shadings:** as the split produces them.  **Level pairs:** leaf → `b`, `(p, b)`, `(a, p)`, `a`. -/
def FourFactorRowsAt
    (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
    (v : EuclideanSpace ℝ (Fin 3)) (t₁ : Finset ι) (a p b : ℕ) (β εf gmv εp εc : ℝ) : Prop :=
  (∀ k ∈ ML2Reduction.activeNodes (retainedLeafChain 𝒰 t₁ b) p,
    (((retainedLeafChain 𝒰 t₁ b).tube p k).translate v).carrier
      ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) ∧
  (∀ (Y' : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
    (∀ i, (Y' i).toTube = ((T i).translate v).toTube) → ∀ jτ : ι,
    ShadedBody.multiplicity
        ({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
          (retainedLeafChain 𝒰 t₁ b).assign b i = jτ} : Finset ι)
        (fun i => (Y' i).toShadedBody)
      ≤ (δ : ENNReal) ^ (-εf)
        * ((({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
            (retainedLeafChain 𝒰 t₁ b).assign b i = jτ} : Finset ι).card : ENNReal)) ^ β) ∧
  (∀ (tτ' : Finset ι), tτ' ⊆ ML2Reduction.activeNodes (retainedLeafChain 𝒰 t₁ b) b →
    ∀ (Yτ' : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) b)
        (EuclideanSpace ℝ (Fin 3))),
    (∀ j, (Yτ' j).toTube = ((retainedLeafChain 𝒰 t₁ b).tube b j).translate v) → ∀ jp : ι,
    ShadedBody.multiplicity
        ({j ∈ tτ' | ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) p b j = jp} : Finset ι)
        (fun j => (Yτ' j).toShadedBody)
      ≤ (δ : ENNReal) ^ gmv
        * ((({j ∈ tτ' | ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) p b j = jp} :
            Finset ι).card : ENNReal)) ^ β) ∧
  (∀ (tp' : Finset ι), tp' ⊆ ML2Reduction.activeNodes (retainedLeafChain 𝒰 t₁ b) p →
    ∀ (Yp : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) p)
        (EuclideanSpace ℝ (Fin 3))),
    (∀ k, (Yp k).toTube = ((retainedLeafChain 𝒰 t₁ b).tube p k).translate v) → ∀ jθ : ι,
    ShadedBody.multiplicity
        ({k ∈ tp' | ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) a p k = jθ} : Finset ι)
        (fun k => (Yp k).toShadedBody)
      ≤ (δ : ENNReal) ^ (-εp)
        * ((({k ∈ tp' | ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) a p k = jθ} :
            Finset ι).card : ENNReal)) ^ β) ∧
  (∀ (tθ' : Finset ι), tθ' ⊆ (retainedLeafChain 𝒰 t₁ b).indexSet a →
    ∀ (Yθ : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) a)
        (EuclideanSpace ℝ (Fin 3))),
    (∀ l, (Yθ l).toTube = ((retainedLeafChain 𝒰 t₁ b).tube a l).translate v) →
    ShadedBody.multiplicity tθ' (fun l => (Yθ l).toShadedBody)
      ≤ (δ : ENNReal) ^ (-εc) * ((tθ'.card : ℕ) : ENNReal) ^ β)

set_option maxHeartbeats 4000000 in
open Classical in
/-- **`Kakeya.ML2Core.HfacPostDropFour`, produced.**

The three-scale split runs on `Kakeya.ML2Core.retainedLeafChain` — the ambient hierarchy restricted
to the leaves `t₁` retains — and on the tubes translated by the seam's `v`; its `hprod` is on the
untranslated leaf family, which is the form `HfacPostDropFour` reads.  Every remaining input is a
factor row of `Kakeya.ML2Core.FourFactorRowsAt`, i.e. the sites'.

**No `a ≠ 0` guard is used**: the three `a ≠ 0 →` antecedents of `HfacPostDropFour` are not read,
and neither is the window's analytic content — only `fine_le_gridLen` and `coarse_lt_fine`. -/
theorem hfacPostDropFour_of_fourFactorRows.{u'} {β ϖ ε₁ ηin η' εf εp εc κc : ℝ}
    {gm gain dens : ℝ → ℝ} {Cu₀ : NNReal}
    (hrows : ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u'} (u : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
        (Cu : NNReal)
        (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
        (v : EuclideanSpace ℝ (Fin 3)) (t₁ : Finset ι) (a p b m : ℕ),
        FourFactorRowsAt 𝒰 v t₁ a p b β εf (gm (ML2Spine.spineRung β ϖ ε₁ gain dens m)) εp
          (εc + ML2Spine.spineRung β ϖ ε₁ gain dens m)) :
    HfacPostDropFour.{u'} β ϖ ε₁ ηin η' εf εp εc κc gm gain dens Cu₀ := by
  have hpos : ∀ᶠ (δ : NNReal) in 𝓝[>] 0, (0 : NNReal) < δ := self_mem_nhdsWithin
  have hle1 : ∀ᶠ (δ : NNReal) in 𝓝[>] 0, δ ≤ 1 := Kakeya.ml1Boot.eventually_le_one_nhdsGT
  filter_upwards [hrows, hpos, hle1] with δ hrow hδ0 hδ1
  intro ι u T Cu lam 𝒰 Cstar a b m hwin v t₀ t₁ ht₁ hballt₁ hballleaf _hz1 _hz2 _hz3 _hballu
    _hune _hmax _hdense _hcomp _hlam _hcard _hCstar _hCu hmass hδb hba ha1 p hap hpb _hF1 _hF2 _hF3
  obtain ⟨hballπ, hfine, hmid, hpar, hcoarse⟩ := hrow u T Cu 𝒰 v t₁ a p b m
  have hbN : b ≤ Tube.ssfGridLen δ := hwin.fine_le_gridLen
  have hpN : p ≤ Tube.ssfGridLen δ := le_trans hpb hbN
  have haN : a ≤ Tube.ssfGridLen δ := le_trans (le_trans hap hpb) hbN
  have hτπ : Tube.gridScale δ (Tube.ssfGridLen δ) b
      ≤ Tube.gridScale δ (Tube.ssfGridLen δ) p := Tube.gridScale_antitone hδ0 hδ1 _ hpb
  have hπθ : Tube.gridScale δ (Tube.ssfGridLen δ) p
      ≤ Tube.gridScale δ (Tube.ssfGridLen δ) a := Tube.gridScale_antitone hδ0 hδ1 _ hap
  have hactb : ML2Reduction.activeNodes (retainedLeafChain 𝒰 t₁ b) b ⊆ t₁ :=
    activeNodes_chainRestrictFamily_subset_of_filter _ _
  have hactp : ML2Reduction.activeNodes (retainedLeafChain 𝒰 t₁ b) p
      ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain p :=
    activeNodes_chainRestrictFamily_subset _ _ _
  have hvol : ∀ i : ι, volume (((T i).translate v).shade) = volume ((T i).shade) := by
    intro i
    show volume ((v + ·) '' (T i).shade) = _
    simpa using measure_vadd (μ := (volume : Measure (EuclideanSpace ℝ (Fin 3)))) v (T i).shade
  have hmass' : 0 < ∑ i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι),
      volume (((T i).translate v).shade) := by
    simpa [hvol] using hmass
  obtain ⟨tτ', htτ', tp', htp', tθ', htθ', Yτ', _Ypo, Yp, Yθ, Y', hYτ'tube, _hYpotube,
      hYptube, hYθtube, hY'tube, hne, hprod⟩ :=
    exists_spineThreeScale_ofChain_translated (E := EuclideanSpace ℝ (Fin 3)) hδ0
      (retainedLeafChain 𝒰 t₁ b) hap hpb haN hpN hbN hδb hτπ hπθ ha1 v
      (fun i => (T i).translate v) (fun i => rfl) (fun i => rfl) hballleaf
      (fun j hj => hballt₁ j (hactb hj)) hballπ
  obtain ⟨hτne, hpne, hθne⟩ := hne hmass'
  obtain ⟨jτ, hjτ⟩ := hτne
  obtain ⟨jp, hjp⟩ := hpne
  obtain ⟨jθ, hjθ⟩ := hθne
  have hE1 : ({j ∈ tτ' | ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) p b j = jp} :
        Finset ι)
      = ({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain p b j = jp} : Finset ι) := by
    refine Finset.filter_congr ?_
    intro j hj
    rw [coarseNode_retainedLeafChain 𝒰 t₁ hpb hbN (htτ' hj)]
  have hE2 : ({k ∈ tp' | ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) a p k = jθ} :
        Finset ι)
      = ({k ∈ tp' | ML2Reduction.coarseNode 𝒰.cover.toChain a p k = jθ} : Finset ι) := by
    refine Finset.filter_congr ?_
    intro k hk
    rw [coarseNode_retainedLeafChain 𝒰 t₁ hap hpN (htp' hk)]
  have hprodx := hprod jτ hjτ jp hjp jθ hjθ
  rw [hE1, hE2] at hprodx
  have hfinex := hfine Y' hY'tube jτ
  have hmidx := hmid tτ' htτ' Yτ' hYτ'tube jp
  rw [hE1] at hmidx
  have hparx := hpar tp' htp' Yp hYptube jθ
  rw [hE2] at hparx
  have hcoarsex := hcoarse tθ' htθ' Yθ hYθtube
  exact ⟨tτ', tp', tθ', Yτ', Yp, Yθ, Y', jτ, jp, jθ,
    fun j hj => hactb (htτ' hj), fun k hk => hactp (htp' hk), htθ', hactb (htτ' hjτ), hjθ,
    ⟨jτ, hjτ⟩, ⟨jp, hjp⟩, hprodx, hfinex, hmidx, hparx, hcoarsex⟩

end HfacProducer

/-! ## The spine, retargeted at the refined payload -/

/-- **`ML2Assembly.GeometricCoreAt` from `hfac`, the site witness and the REFINED floor payload.**

`Kakeya.ML2Core.geometricCoreAt_of_hfac_witness_payload` with its third row replaced by
`Kakeya.ML2Core.RefinedFloorPayload`, through route (b)
(`Kakeya.ML2Core.trialSupplier_of_floorRouteTrichotomy`).  The `hF7` slot is between
the two routes, so this is a drop-in and the only change is which payload is asked for. -/
theorem geometricCoreAt_of_hfac_witness_refinedFloor.{v'} (K' : ℕ)
    (hsup : ∀ (β ϖ : ℝ) (gain dens : ℝ → ℝ), 0 < β → β ≤ 1 →
      ML2Assembly.Lemma91ParamsAt.{v'} β ϖ gain dens →
      KatzTaoEstimate.{v'} (EuclideanSpace ℝ (Fin 3)) β →
      FrostmanEstimate.{v'} (EuclideanSpace ℝ (Fin 3)) β →
      0 < ϖ ∧ (∀ ζ, 0 < ζ → 0 < gain ζ) ∧ (∀ ζ, 0 < ζ → 0 < dens ζ) ∧
      ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧
      ∃ (Cu₀ C : NNReal) (Kl cl : ℕ) (ηin aL η' εf εp εc κc κ' θ₂ : ℝ) (gm : ℝ → ℝ),
        0 < aL ∧ 1 ≤ C ∧ 1 ≤ Cu₀ ∧ 0 < κc ∧ 0 < κ' ∧ 0 < θ₂ ∧ 0 < εp ∧
        (∀ k : ℕ, k < ML2Spine.spineCount ϖ ε₁ →
          κc + ML2Spine.spineRung β ϖ ε₁ gain dens k ≤ 2 * η') ∧
        (∀ X : ℝ, ML2Spine.spineNu β ϖ ε₁ gain dens ≤ X →
          6 * ML2Spine.spineNu β ϖ ε₁ gain dens + θ₂ + ηin
            ≤ gm X - εf - εp - (εc + X) - κ') ∧
        HfacPostDropFour.{v'} β ϖ ε₁ ηin η' εf εp εc κc gm gain dens Cu₀ ∧
        SiteWitness.{v'} η ηin (defectMargin β ϖ ε₁ gain dens) aL Cu₀ ∧
        RefinedFloorPayload.{v'} (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ η' gain dens
          (polylogLoss K')) :
    ML2Assembly.GeometricCoreAt.{v'} := by
  refine geometricCoreAt_of_witness_and_trial K' (fun β ϖ gain dens hβ0 hβ1 hp hKT hF => ?_)
  obtain ⟨hϖ, hgain, hdens, ε₁, hε₁, η, hη0, hη1, Cu₀, C, Kl, cl, ηin, aL, η', εf, εp, εc, κc, κ',
    θ₂, gm, haL, hC, hCu₀, hκc, hκ', hθ₂, hεp, hres, hexp, hfac, hwit, hfloor⟩ :=
    hsup β ϖ gain dens hβ0 hβ1 hp hKT hF
  exact ⟨hϖ, hgain, hdens, ε₁, hε₁, η, hη0, hη1, Cu₀, ηin, aL, haL, hwit,
    trialSupplier_of_floorRouteTrichotomy
      (trialOutcome_middle_of_floorFactors_alpha (Kl := Kl) (cl := cl)
        (h := defectH β ϖ ε₁ gain dens) (η' := η')
        hβ0 hβ1 hϖ hgain hdens hε₁ hC hCu₀ hκc hκ' hθ₂ hεp hres (polylogLoss K') hexp hfac)
      (eventually_hΛf_polylogLoss K' hβ0 hϖ hε₁ hgain hdens)
      (floorPayloadTrichotomy_of_refinedFloorPayload hfloor)⟩

/-! ## The final assembly -/

/-- **The whole supply the run still owes, in one named package.**

Read off the composition, and every conjunct is a row of the residual list:

* the scalar ledger — `0 < aL`, `1 ≤ C`, `1 ≤ Cu₀`, `0 < κc`, `0 < κ'`, `0 < θ₂`, `0 < εp`, C1's
  residual row `κc + η_k ≤ 2 η'`, and the budget `hexp` (satisfiable at `12 ν / 5`,
  `Kakeya.ML2Core.hexp_of_sharp_gain`);
* the **site side** — `Kakeya.ML2Core.FourFactorRowsAt`, i.e. `hballπ`, `hfine` (sites 1-2),
  `hmid` (sites 3-6), `hpar` (the new parent at `(a, p)`), `hcoarse` (the outer factor at `a`);
* the **witness side** — `Kakeya.ML2Core.SiteWitness` at `Cu₀`;
* the **payload side** — `Kakeya.ML2Core.RefinedFloorPayload`, i.e.
  `Kakeya.ML2Core.RefinedFloorSupplyAt` over the filter. -/
def GeometricCoreSupply.{v'} (K' : ℕ) : Prop :=
  ∀ (β ϖ : ℝ) (gain dens : ℝ → ℝ), 0 < β → β ≤ 1 →
    ML2Assembly.Lemma91ParamsAt.{v'} β ϖ gain dens →
    KatzTaoEstimate.{v'} (EuclideanSpace ℝ (Fin 3)) β →
    FrostmanEstimate.{v'} (EuclideanSpace ℝ (Fin 3)) β →
    0 < ϖ ∧ (∀ ζ, 0 < ζ → 0 < gain ζ) ∧ (∀ ζ, 0 < ζ → 0 < dens ζ) ∧
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧
    ∃ (Cu₀ C : NNReal) (Kl cl : ℕ) (ηin aL η' εf εp εc κc κ' θ₂ : ℝ) (gm : ℝ → ℝ),
      0 < aL ∧ 1 ≤ C ∧ 1 ≤ Cu₀ ∧ 0 < κc ∧ 0 < κ' ∧ 0 < θ₂ ∧ 0 < εp ∧
      (∀ k : ℕ, k < ML2Spine.spineCount ϖ ε₁ →
        κc + ML2Spine.spineRung β ϖ ε₁ gain dens k ≤ 2 * η') ∧
      (∀ X : ℝ, ML2Spine.spineNu β ϖ ε₁ gain dens ≤ X →
        6 * ML2Spine.spineNu β ϖ ε₁ gain dens + θ₂ + ηin
          ≤ gm X - εf - εp - (εc + X) - κ') ∧
      (∀ᶠ (δ : NNReal) in 𝓝[>] 0,
        ∀ {ι : Type v'} (u : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
          (Cu : NNReal)
          (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
          (v : EuclideanSpace ℝ (Fin 3)) (t₁ : Finset ι) (a p b m : ℕ),
          FourFactorRowsAt 𝒰 v t₁ a p b β εf (gm (ML2Spine.spineRung β ϖ ε₁ gain dens m)) εp
            (εc + ML2Spine.spineRung β ϖ ε₁ gain dens m)) ∧
      SiteWitness.{v'} η ηin (defectMargin β ϖ ε₁ gain dens) aL Cu₀ ∧
      RefinedFloorPayload.{v'} (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ η' gain dens
        (polylogLoss K')

/-- **The final assembly: `ML2Assembly.GeometricCoreAt`.**

Spine ← `Kakeya.ML2Core.HfacPostDropFour` ← `Kakeya.ML2Core.hfacPostDropFour_of_fourFactorRows`
← the four factor rows; `Kakeya.ML2Core.SiteWitness` unchanged; and the payload through
`Kakeya.ML2Core.RefinedFloorPayload` — i.e. `Kakeya.ML2Core.RefinedFloorSupplyAt`, taken as a
hypothesis. -/
theorem geometricCoreAt_of_refinedFloorSupply.{v'} (K' : ℕ)
    (hsup : GeometricCoreSupply.{v'} K') : ML2Assembly.GeometricCoreAt.{v'} := by
  refine geometricCoreAt_of_hfac_witness_refinedFloor K'
    (fun β ϖ gain dens hβ0 hβ1 hp hKT hF => ?_)
  obtain ⟨hϖ, hgain, hdens, ε₁, hε₁, η, hη0, hη1, Cu₀, C, Kl, cl, ηin, aL, η', εf, εp, εc, κc, κ',
    θ₂, gm, haL, hC, hCu₀, hκc, hκ', hθ₂, hεp, hres, hexp, hrows, hwit, hfloor⟩ :=
    hsup β ϖ gain dens hβ0 hβ1 hp hKT hF
  exact ⟨hϖ, hgain, hdens, ε₁, hε₁, η, hη0, hη1, Cu₀, C, Kl, cl, ηin, aL, η', εf, εp, εc, κc, κ',
    θ₂, gm, haL, hC, hCu₀, hκc, hκ', hθ₂, hεp, hres, hexp,
    hfacPostDropFour_of_fourFactorRows hrows, hwit, hfloor⟩

/-! ## The every-scale side: the `S' → S` step, measured

's left disjunct is `IsKatzTaoAtEveryScale` on the **refined** tower,
while `Kakeya.ML2Assembly.Dichotomy`'s first disjunct is a **mass** bound on the **original**
family.  The chain, by name:

`IsKatzTaoAtEveryScale (refinedHierarchy 𝒰 hS' hhom hW)`
→ `Kakeya.ML2Reduction.isKatzTaoAtEveryScale_of_cover_eq` (transport across the cover equality)
→ `Kakeya.ML2Reduction.exists_everyScale_multiplicity_le` (GWZ Theorem 7.3(B) at the sticky
  interface — **this is where `StickyKakeya.stickyFrostmanEstimate` enters, and it is the only
  place**)
→ `Kakeya.ML2Assembly.dichotomy_everyScale_branch` (multiplicity → mass)
→ **the `S' → S` step**, which is the theorem below.

The step is **not** a gap: it is `Kakeya.ML2Core.IsShadedRefinementOf.retention`, existing, and its
price is exactly the refinement's own loss `Λ` — the same `Λf δ` the `(F)` route already absorbs
through `Kakeya.ML2Core.eventually_hΛf_polylogLoss`.  Source l.4098-4104, l.4355-4362. -/

section EveryScaleSide

variable {ι : Type*} {δ Cu : NNReal} {u : Finset ι}
  {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
  {𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu}

/-- **The `S' → S` retention step of the every-scale side,.**

From the multiplicity bound on the refined family `S'` (what Theorem 7.3(B) returns) to the mass
bound on the original family `S` (what `Kakeya.ML2Assembly.Dichotomy`'s first disjunct asks), at
the refinement's own loss `Λ` and nothing more.

**Family:** `S` with shading `Z`; refined to `S'` with shading `W`.  **Level pair:** none — this
step is level-free. -/
theorem dichotomyLeft_of_refinement_of_multiplicity {Λ : ℝ≥0∞} {S S' : Finset ι}
    {Z W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))} (hδ0 : 0 < δ)
    (href : IsShadedRefinementOf 𝒰 Λ S Z S' W) {ε₀ : ℝ}
    (h : ShadedBody.multiplicity S' (fun i => (W i).toShadedBody)
      ≤ ENNReal.ofReal ((δ : ℝ) ^ (-ε₀))) :
    (∑ i ∈ S, volume (Z i).shade)
      ≤ Λ * (δ : ENNReal) ^ (-ε₀) * volume (⋃ i ∈ S, (Z i).shade) := by
  have h1 := ML2Assembly.dichotomy_everyScale_branch (δ := δ) hδ0 W h
  have hmono : volume (⋃ i ∈ S', (W i).shade) ≤ volume (⋃ i ∈ S, (Z i).shade) := by
    refine measure_mono ?_
    intro x hx
    simp only [Set.mem_iUnion, exists_prop] at hx ⊢
    obtain ⟨i, hi, hx⟩ := hx
    exact ⟨i, href.subset hi, href.shade_subset i hx⟩
  calc (∑ i ∈ S, volume (Z i).shade)
      ≤ Λ * ∑ i ∈ S', volume (W i).shade := href.retention
    _ ≤ Λ * ((δ : ENNReal) ^ (-ε₀) * volume (⋃ i ∈ S', (W i).shade)) := by gcongr
    _ ≤ Λ * ((δ : ENNReal) ^ (-ε₀) * volume (⋃ i ∈ S, (Z i).shade)) := by gcongr
    _ = Λ * (δ : ENNReal) ^ (-ε₀) * volume (⋃ i ∈ S, (Z i).shade) := by rw [mul_assoc]

end EveryScaleSide

/-! ## T4 — the shape check -/

/-- **T4.**  The assembled `ML2Assembly.GeometricCoreAt` is accepted by
`Kakeya.ML2Large.strict_drop_of_geometricCoreAt`, the existing large-family export.  The check is a
full application, so the elaborator adjudicates the match. -/
example (K' : ℕ) (hsup : GeometricCoreSupply.{v} K') : True := by
  have := ML2Large.strict_drop_of_geometricCoreAt (geometricCoreAt_of_refinedFloorSupply K' hsup)
  trivial

end Kakeya.ML2Core

end
