/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineGeometricCoreAssembly
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorShapeSelfHierarchy
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineWindowFieldsFromArrays

/-!
# The site side of `Kakeya.ML2Core.FourFactorRowsAt`


-/

@[expose] public section

open MeasureTheory Metric ConvexSpaceBody ShadedBody
open scoped NNReal ENNReal Topology

namespace Kakeya.ML2Core

section Refutation

/-- A unit vector of `EuclideanSpace ℝ (Fin 3)`. -/
noncomputable def siteAxis : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single (0 : Fin 3) (1 : ℝ)

theorem norm_siteAxis : ‖siteAxis‖ = 1 := by
  simp [siteAxis]

theorem dist_zero_siteAxis : dist (0 : EuclideanSpace ℝ (Fin 3)) siteAxis = 1 := by
  rw [dist_zero_left, norm_siteAxis]

/-- The one-leaf shaded family used by the refutation: a single `δ`-tube from `0` to `siteAxis`,
with empty shading (no row of the site block reads the shade). -/
noncomputable def siteBadTube (δ : NNReal) : ShadedTube δ (EuclideanSpace ℝ (Fin 3)) where
  toTube := Tube.mk' δ dist_zero_siteAxis
  shade := ∅
  measurableSet_shade := MeasurableSet.empty
  shade_subset := Set.empty_subset _


/-- The one-point index set. -/
def siteIdx : Finset PUnit.{1} := {PUnit.unit}

theorem siteIdx_mem : PUnit.unit ∈ siteIdx := by simp [siteIdx]

theorem siteInj (δ : NNReal) (N : ℕ) :
    ∀ k ≤ N, Set.InjOn (fun _i : PUnit.{1} =>
      ((siteBadTube δ).toTube).rescale (Tube.gridScale δ N k))
      (siteIdx : Set PUnit.{1}) := by
  intro k _ a _ b _ _
  exact Subsingleton.elim a b

/-- The one-leaf self-hierarchy the refutation runs on. -/
noncomputable def siteBadHierarchy {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    Tube.UniformTubeSet siteIdx (fun _ : PUnit.{1} => (siteBadTube δ).toTube)
      (Tube.ssfGridLen δ) (max 1 ((siteIdx.card : ℕ) : NNReal)) :=
  Tube.UniformTubeSet.self hδ0 hδ1 siteIdx (fun _ => (siteBadTube δ).toTube)
    (siteInj δ (Tube.ssfGridLen δ))

open Classical in
theorem site_unit_mem_activeNodes {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (p b : ℕ) :
    PUnit.unit ∈ ML2Reduction.activeNodes
      (retainedLeafChain (siteBadHierarchy hδ0 hδ1) siteIdx b) p := by
  classical
  simp only [ML2Reduction.activeNodes, Finset.mem_filter]
  constructor
  · show PUnit.unit ∈ siteIdx
    exact siteIdx_mem
  · refine ⟨PUnit.unit, ?_⟩
    simp only [Tube.coverClass, Finset.mem_filter]
    refine ⟨?_, by trivial⟩
    simp [siteIdx]


open Classical in
theorem not_supplyRow_fourFactorRows {β ϖ ε₁ εf εp εc : ℝ} {gain dens gm : ℝ → ℝ}
    (hrows : ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type} (u : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
        (Cu : NNReal)
        (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
        (v : EuclideanSpace ℝ (Fin 3)) (t₁ : Finset ι) (a p b m : ℕ),
        FourFactorRowsAt 𝒰 v t₁ a p b β εf (gm (ML2Spine.spineRung β ϖ ε₁ gain dens m)) εp
          (εc + ML2Spine.spineRung β ϖ ε₁ gain dens m)) : False := by
  classical
  have hpos : ∀ᶠ (δ : NNReal) in 𝓝[>] 0, (0 : NNReal) < δ := self_mem_nhdsWithin
  have hle1 : ∀ᶠ (δ : NNReal) in 𝓝[>] 0, δ ≤ 1 := Kakeya.ml1Boot.eventually_le_one_nhdsGT
  obtain ⟨δ, ⟨hrow, hδ0⟩, hδ1⟩ := ((hrows.and hpos).and hle1).exists
  set v : EuclideanSpace ℝ (Fin 3) := (2 : ℝ) • siteAxis with hv
  have hball := (hrow siteIdx (fun _ => siteBadTube δ) _ (siteBadHierarchy hδ0 hδ1) v
    siteIdx 0 0 0 0).1
  have hx := hball PUnit.unit (site_unit_mem_activeNodes hδ0 hδ1 0 0) (Tube.x_mem_carrier _)
  rw [Metric.mem_closedBall, dist_eq_norm] at hx
  have hxv : ((((retainedLeafChain (siteBadHierarchy hδ0 hδ1) siteIdx 0).tube 0
      PUnit.unit).translate v)).x = v := by
    show v + (0 : EuclideanSpace ℝ (Fin 3)) = v
    exact add_zero v
  rw [hxv, sub_zero, hv, norm_smul] at hx
  rw [norm_siteAxis] at hx
  norm_num at hx

end Refutation

section CorrectedSupply

open Classical in
/-- **The site row, under the site's own antecedents.**

`Kakeya.ML2Core.HfacPostDropFour`'s antecedent block verbatim (`SpineHfacWire.lean:235-294`),
with its existential conclusion replaced by `Kakeya.ML2Core.FourFactorRowsAt`.

This is the shape the site row must have.  The row as `Kakeya.ML2Core.GeometricCoreSupply`
states it -- the same `FourFactorRowsAt`, but under **no** antecedents at all -- is refuted by
`Kakeya.ML2Core.not_supplyRow_fourFactorRows`: with `v` free of the seam's ball rows the first
conjunct fails on a one-leaf self-hierarchy.  Nothing is weakened here; the antecedents are the
ones the consumer already has in scope and discards. -/
def FourFactorRowsSupply.{u'} (β ϖ ε₁ ηin η' εf εp εc κc : ℝ) (gm gain dens : ℝ → ℝ)
    (Cu₀ : NNReal) : Prop :=
  ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u'} (u : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (Cu lam :
          NNReal)
        (𝒰 : Tube.UniformTubeSet u (fun i ↦ (T i).toTube) (Tube.ssfGridLen δ) Cu)
        (Cstar : ENNReal) (a b m : ℕ),
        ML2Reduction.IsKatzTaoDividingWindowLevels 𝒰 Cstar (ML2Spine.spineRung β ϖ ε₁ gain dens)
          (ML2Spine.spineDiv ϖ ε₁) (ML2Spine.spineCount ϖ ε₁) a b m →
      ∀ (v : (EuclideanSpace ℝ (Fin 3))) (t₀ t₁ : Finset ι),
        t₁ ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain b →
        (∀ j ∈ t₁, ((𝒰.cover.tube b j).translate v).carrier ⊆ Metric.closedBall (0 :
            (EuclideanSpace ℝ (Fin 3))) 1) →
        (∀ i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι), ((T i).translate v).carrier ⊆
            Metric.closedBall (0 : (EuclideanSpace ℝ (Fin 3))) 1) →
        (a ≠ 0 → t₀ ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain a) →
        (a ≠ 0 → ∀ j ∈ t₁, ML2Reduction.coarseNode 𝒰.cover.toChain a b j ∈ t₀) →
        (a ≠ 0 → ∀ k ∈ t₀,
          ((𝒰.cover.tube a k).translate v).carrier ⊆ Metric.closedBall (0 : (EuclideanSpace ℝ (Fin
              3))) 1) →
        (∀ i ∈ u, (T i).carrier ⊆ Metric.closedBall (0 : (EuclideanSpace ℝ (Fin 3))) 1) →
        u.Nonempty →
        Kakeya.maxDensity u (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-ηin) →
        ML2Shaded.HasDenseShading lam u (fun i ↦ (T i).toShadedBody) →
        ML2Shaded.HasComparableDensities lam⁻¹ u (fun i ↦ (T i).toShadedBody) →
        (δ : NNReal) ^ ηin / 2 ≤ lam →
        (u.card : NNReal) ≤ δ ^ (-(4 : ℝ)) →
        Cstar ≤ (δ : ENNReal) ^ (-κc) →
        Cu ≤ Cu₀ →
        0 < ∑ i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι), volume (T i).shade →
        δ ≤ Tube.gridScale δ (Tube.ssfGridLen δ) b →
        Tube.gridScale δ (Tube.ssfGridLen δ) b ≤ Tube.gridScale δ (Tube.ssfGridLen δ) a →
        Tube.gridScale δ (Tube.ssfGridLen δ) a ≤ 1 →
        -- the refined (F): the genuine parent level, its density, and the count floor
        ∀ p : ℕ, a ≤ p → p ≤ b →
          (∀ m' : ℕ, a < m' → m' < b →
            ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ (1 - ML2Spine.spineDiv ϖ ε₁)
              ≤ (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ) →
            (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ)
              ≤ ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ ML2Spine.spineDiv ϖ ε₁ →
            p < m') →
          (∀ jθ ∈ 𝒰.cover.indexSet a,
            Kakeya.maxDensity (𝒰.nodesUnder p a jθ) (fun j ↦ (𝒰.cover.tube p j).toConvexSpaceBody)
              ≤ (δ : ENNReal) ^ (-(2 * η'))) →
          (∀ jθ ∈ 𝒰.cover.indexSet a, ∀ jp ∈ 𝒰.nodesUnder p a jθ, ∀ m' : ℕ, a < m' → m' < b →
            ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ (1 - ML2Spine.spineDiv ϖ ε₁)
              ≤ (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ) →
            (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ)
              ≤ ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ ML2Spine.spineDiv ϖ ε₁ →
            p < m' →
            ((Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ))
                  ^ (2 + 4 * (ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1) / 16))
              ≤ ((𝒰.nodesUnder m' p jp).card : ℝ)) →
        FourFactorRowsAt 𝒰 v t₁ a p b β εf (gm (ML2Spine.spineRung β ϖ ε₁ gain dens m)) εp
          (εc + ML2Spine.spineRung β ϖ ε₁ gain dens m)

-- The elaboration budget is the existing `hfacPostDropFour_of_fourFactorRows`'s own: the
-- antecedent block is ~60 lines of dependent binders and the split's output is a 21-tuple.
set_option maxHeartbeats 4000000 in
open Classical in
/-- **`Kakeya.ML2Core.HfacPostDropFour`, produced from the corrected site row.**

`Kakeya.ML2Core.hfacPostDropFour_of_fourFactorRows` with its site row replaced by
`Kakeya.ML2Core.FourFactorRowsSupply` -- the same `FourFactorRowsAt`, quantified under the
antecedents the consumer already has.  The proof is the same one; the only change is that the
site's own hypotheses are passed to the row instead of being discarded. -/
theorem hfacPostDropFour_of_fourFactorRowsSupply.{u'} {β ϖ ε₁ ηin η' εf εp εc κc : ℝ}
    {gm gain dens : ℝ → ℝ} {Cu₀ : NNReal}
    (hrows : FourFactorRowsSupply.{u'} β ϖ ε₁ ηin η' εf εp εc κc gm gain dens Cu₀) :
    HfacPostDropFour.{u'} β ϖ ε₁ ηin η' εf εp εc κc gm gain dens Cu₀ := by
  have hpos : ∀ᶠ (δ : NNReal) in 𝓝[>] 0, (0 : NNReal) < δ := self_mem_nhdsWithin
  have hle1 : ∀ᶠ (δ : NNReal) in 𝓝[>] 0, δ ≤ 1 := Kakeya.ml1Boot.eventually_le_one_nhdsGT
  filter_upwards [hrows, hpos, hle1] with δ hrow hδ0 hδ1
  intro ι u T Cu lam 𝒰 Cstar a b m hwin v t₀ t₁ ht₁ hballt₁ hballleaf hz1 hz2 hz3 hballu
    hune hmax hdense hcomp hlam hcard hCstar hCu hmass hδb hba ha1 p hap hpb hF1 hF2 hF3
  obtain ⟨hballπ, hfine, hmid, hpar, hcoarse⟩ :=
    hrow u T Cu lam 𝒰 Cstar a b m hwin v t₀ t₁ ht₁ hballt₁ hballleaf hz1 hz2 hz3 hballu
      hune hmax hdense hcomp hlam hcard hCstar hCu hmass hδb hba ha1 p hap hpb hF1 hF2 hF3
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

/-- **The whole supply the run still owes, with the site row at the site.**

`Kakeya.ML2Core.GeometricCoreSupply` with its site conjunct replaced by
`Kakeya.ML2Core.FourFactorRowsSupply`.  Every other conjunct is.  The replaced
conjunct is refuted as stated (`Kakeya.ML2Core.not_supplyRow_fourFactorRows`), so this is the
form in which the closure is not vacuous. -/
def GeometricCoreSupplySited.{v'} (K' : ℕ) : Prop :=
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
      FourFactorRowsSupply.{v'} β ϖ ε₁ ηin η' εf εp εc κc gm gain dens Cu₀ ∧
      SiteWitness.{v'} η ηin (defectMargin β ϖ ε₁ gain dens) aL Cu₀ ∧
      RefinedFloorPayload.{v'} (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ η' gain dens
        (polylogLoss K')

/-- **The final assembly, from the sited supply.**

`Kakeya.ML2Core.geometricCoreAt_of_refinedFloorSupply` with
`Kakeya.ML2Core.hfacPostDropFour_of_fourFactorRowsSupply` in place of
`Kakeya.ML2Core.hfacPostDropFour_of_fourFactorRows`.  The conclusion is unchanged. -/
theorem geometricCoreAt_of_refinedFloorSupplySited.{v'} (K' : ℕ)
    (hsup : GeometricCoreSupplySited.{v'} K') : ML2Assembly.GeometricCoreAt.{v'} := by
  refine geometricCoreAt_of_hfac_witness_refinedFloor K'
    (fun β ϖ gain dens hβ0 hβ1 hp hKT hF => ?_)
  obtain ⟨hϖ, hgain, hdens, ε₁, hε₁, η, hη0, hη1, Cu₀, C, Kl, cl, ηin, aL, η', εf, εp, εc, κc, κ',
    θ₂, gm, haL, hC, hCu₀, hκc, hκ', hθ₂, hεp, hres, hexp, hrows, hwit, hfloor⟩ :=
    hsup β ϖ gain dens hβ0 hβ1 hp hKT hF
  exact ⟨hϖ, hgain, hdens, ε₁, hε₁, η, hη0, hη1, Cu₀, C, Kl, cl, ηin, aL, η', εf, εp, εc, κc, κ',
    θ₂, gm, haL, hC, hCu₀, hκc, hκ', hθ₂, hεp, hres, hexp,
    hfacPostDropFour_of_fourFactorRowsSupply hrows, hwit, hfloor⟩

end CorrectedSupply

section BallPi

open Classical in
/-- **The level-`p` node of an active node of the retained-leaf chain has its `(a,p)`-parent in
the seam's `t₀`.**

An active level-`p` node of `Kakeya.ML2Core.retainedLeafChain` carries a leaf whose level-`b` node
is retained by `t₁`; `Kakeya.ML2Core.coarseNode_assign` reads both ancestors off that leaf, and the
seam's own row `hz2` puts the level-`a` one in `t₀`. -/
theorem coarseNode_parent_mem_of_retained {ι : Type*} {δ Cu : NNReal} {u : Finset ι}
    {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
    {t₀ t₁ : Finset ι} {a p b : ℕ} (hap : a ≤ p) (hpb : p ≤ b)
    (hbN : b ≤ Tube.ssfGridLen δ)
    (hz2 : ∀ j ∈ t₁, ML2Reduction.coarseNode 𝒰.cover.toChain a b j ∈ t₀) :
    ∀ k ∈ ML2Reduction.activeNodes (retainedLeafChain 𝒰 t₁ b) p,
      ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) a p k ∈ t₀ := by
  classical
  intro k hk
  have hpN : p ≤ Tube.ssfGridLen δ := le_trans hpb hbN
  simp only [ML2Reduction.activeNodes, Finset.mem_filter] at hk
  obtain ⟨i, hi⟩ := hk.2
  simp only [Tube.coverClass, Finset.mem_filter] at hi
  obtain ⟨hif, hik⟩ := hi
  have hiu : i ∈ u := hif.1
  have hit₁ : 𝒰.cover.assign b i ∈ t₁ := hif.2
  have h1 : ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) a p k
      = (retainedLeafChain 𝒰 t₁ b).assign a i := by
    rw [← hik]
    refine coarseNode_assign (retainedLeafChain 𝒰 t₁ b) hap hpN ?_
    simp only [Finset.mem_filter]
    exact ⟨hif.1, hif.2⟩
  have h2 : ML2Reduction.coarseNode 𝒰.cover.toChain a b (𝒰.cover.assign b i)
      = 𝒰.cover.assign a i :=
    coarseNode_assign 𝒰.cover.toChain (le_trans hap hpb) hbN hiu
  have h3 := hz2 _ hit₁
  rw [h2] at h3
  rw [h1]
  exact h3

open Classical in
/-- **Conjunct 1 (`hballπ`) of `Kakeya.ML2Core.FourFactorRowsAt`, discharged at `a ≠ 0`.**

`Kakeya.ML2Core.ballRow_at_parent_of_coarse` at the retained-leaf chain, with its `hcn` supplied by
`Kakeya.ML2Core.coarseNode_parent_mem_of_retained` from the seam's own `hz2`, and its `hball₀`
being the seam's `hz3` verbatim.  No new geometric input.

**This is the row `Kakeya.ML2Core.not_supplyRow_fourFactorRows` refutes when the antecedents are
dropped**; here it is proved from exactly the two the consumer already has.  The `a ≠ 0` guard is
`hz2`/`hz3`'s own — at `a = 0` the seam supplies no level-`a` ball row and the level-`p` row has no
supplier in the antecedent block. -/
theorem ballRow_pi_of_seam {ι : Type*} {δ Cu : NNReal} {u : Finset ι}
    {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
    {t₀ t₁ : Finset ι} {a p b : ℕ} {v : EuclideanSpace ℝ (Fin 3)} (hap : a ≤ p) (hpb : p ≤ b)
    (hbN : b ≤ Tube.ssfGridLen δ)
    (hz2 : ∀ j ∈ t₁, ML2Reduction.coarseNode 𝒰.cover.toChain a b j ∈ t₀)
    (hz3 : ∀ l ∈ t₀, ((𝒰.cover.tube a l).translate v).carrier
      ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    ∀ k ∈ ML2Reduction.activeNodes (retainedLeafChain 𝒰 t₁ b) p,
      (((retainedLeafChain 𝒰 t₁ b).tube p k).translate v).carrier
        ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  ballRow_at_parent_of_coarse (retainedLeafChain 𝒰 t₁ b) hap (le_trans hpb hbN)
    (fun _ hk => hk) (coarseNode_parent_mem_of_retained 𝒰 hap hpb hbN hz2) hz3

end BallPi

section ParRow

open Classical in
/-- **Conjunct 4 (`hpar`, the new-parent factor at `(a,p)`) of
`Kakeya.ML2Core.FourFactorRowsAt`, discharged.**

`Kakeya.ML2Core.exists_newParent_factor_at` read on `Kakeya.ML2Core.retainedLeafChain`.  Three of
its four inputs come from the site's own antecedent block:

* the ball row on the fibre -- `Kakeya.ML2Core.ballRow_pi_of_seam`, i.e. the seam's `hz2`/`hz3`;
* the parent-density row -- `hF2`, the (F) payload's `:125-127` row, verbatim from the block;
* the level-`p` threshold `gridScale δ N p ≤ θ₀` -- a scale condition on `p` alone, live at `p ≠ 0`
  whatever `a` is (`Kakeya.ML2Core.outer_threshold_fails_at_zero_newParent_lives`).

The fourth, `hfullpar`, is the **named residual**: a fullness lower bound on the `(a,p)` fibre of
the split's own level-`p` shading.  It is not in the antecedent block and the split does not return
it (`Kakeya.ML2Reduction.exists_spineThreeScale` returns fullness for `tp'` only, not for its
fibres) -- the vehicle is `Kakeya.ML2Core.hfullPi_of_handBack_at_parent` or
`Kakeya.ML2Core.fullness_newParentFibre_ge`.

The loss is `Kakeya.ML2Core.exists_newParent_factor_at`'s own.  **It is not a source display**
: the source constrains the four losses only in TOTAL (l.4455-4457,
l.4678-4681).  `ε` is the defect estimate's accuracy and `2 η'` is the (F) parent-density row's
exponent (l.4068-4069); the allocation `εp := ε + 2 η'` is the tree's, and the budget it must
respect is stated at `Kakeya.ML2Core.exists_fourFactorRowsAt_of_site`.

**Family:** `{i ∈ u | assign b i ∈ t₁}` under `retainedLeafChain`; **shading:** the split's `Yp`,
translated by the seam's `v`.  **Level pair:** `(a, p)`. -/
theorem exists_parRow_of_site {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hKT : Kakeya.KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > (0 : ℝ), ∃ θ₀ : NNReal, 0 < θ₀ ∧ θ₀ ≤ 1 ∧
      ∀ {δ Cu : NNReal} {ι : Type u} {u : Finset ι}
        {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
        (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
        {t₀ t₁ : Finset ι} {a p b : ℕ} {v : EuclideanSpace ℝ (Fin 3)} {η' : ℝ},
        0 < δ → δ ≤ 1 → a ≤ p → p ≤ b → b ≤ Tube.ssfGridLen δ →
        Tube.gridScale δ (Tube.ssfGridLen δ) p ≤ θ₀ → 0 ≤ η' →
        (∀ j ∈ t₁, ML2Reduction.coarseNode 𝒰.cover.toChain a b j ∈ t₀) →
        (∀ l ∈ t₀, ((𝒰.cover.tube a l).translate v).carrier
          ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
        (∀ jθ ∈ 𝒰.cover.indexSet a,
          Kakeya.maxDensity (𝒰.nodesUnder p a jθ)
              (fun k => (𝒰.cover.tube p k).toConvexSpaceBody)
            ≤ (δ : ENNReal) ^ (-(2 * η'))) →
        (∀ (tp' : Finset ι), tp' ⊆ ML2Reduction.activeNodes (retainedLeafChain 𝒰 t₁ b) p →
          ∀ (Yp : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) p)
              (EuclideanSpace ℝ (Fin 3))),
          (∀ k, (Yp k).toTube = ((retainedLeafChain 𝒰 t₁ b).tube p k).translate v) → ∀ jθ : ι,
          (δ : NNReal) ^ η ≤ ShadedBody.fullness
              ({k ∈ tp' | ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) a p k = jθ}
                : Finset ι)
              (fun k => (Yp k).toShadedBody)) →
        (∀ (tp' : Finset ι), tp' ⊆ ML2Reduction.activeNodes (retainedLeafChain 𝒰 t₁ b) p →
          ∀ (Yp : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) p)
              (EuclideanSpace ℝ (Fin 3))),
          (∀ k, (Yp k).toTube = ((retainedLeafChain 𝒰 t₁ b).tube p k).translate v) → ∀ jθ : ι,
          ShadedBody.multiplicity
              ({k ∈ tp' | ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) a p k = jθ}
                : Finset ι)
              (fun k => (Yp k).toShadedBody)
            ≤ (δ : ENNReal) ^ (-(ε + 2 * η'))
              * ((({k ∈ tp' | ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) a p k = jθ} :
                  Finset ι).card : ENNReal)) ^ β) := by
  classical
  obtain ⟨η, hη, θ₀, hθ₀0, hθ₀1, hcore⟩ := exists_newParent_factor_at.{u}
    (E := EuclideanSpace ℝ (Fin 3)) hβ0 hβ1 hKT hε
  refine ⟨η, hη, θ₀, hθ₀0, hθ₀1, ?_⟩
  intro δ Cu ι u T 𝒰 t₀ t₁ a p b v η' hδ0 hδ1 hap hpb hbN hθ hη' hz2 hz3 hF2 hfullpar
  intro tp' htp' Yp hYp jθ
  have hpN : p ≤ Tube.ssfGridLen δ := le_trans hpb hbN
  have hsub : tp' ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain p :=
    fun k hk => activeNodes_chainRestrictFamily_subset _ _ _ (htp' hk)
  -- the two fibres are the same set
  have hE : ({k ∈ tp' | ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) a p k = jθ}
        : Finset ι)
      = ({k ∈ tp' | ML2Reduction.coarseNode 𝒰.cover.toChain a p k = jθ} : Finset ι) := by
    refine Finset.filter_congr ?_
    intro k hk
    rw [coarseNode_retainedLeafChain 𝒰 t₁ hap hpN (htp' hk)]
  by_cases hjθ : jθ ∈ 𝒰.cover.indexSet a
  · have hball : ∀ k ∈ ({k ∈ tp' | ML2Reduction.coarseNode 𝒰.cover.toChain a p k = jθ}
        : Finset ι), (Yp k).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
      intro k hk
      have hk' : k ∈ tp' := (Finset.mem_filter.mp hk).1
      have hc : (Yp k).carrier
          = (((retainedLeafChain 𝒰 t₁ b).tube p k).translate v).carrier :=
        congrArg (fun A : Tube (Tube.gridScale δ (Tube.ssfGridLen δ) p)
          (EuclideanSpace ℝ (Fin 3)) => A.carrier) (hYp k)
      rw [hc]
      exact ballRow_pi_of_seam 𝒰 hap hpb hbN hz2 hz3 k (htp' hk')
    have hfull := hfullpar tp' htp' Yp hYp jθ
    rw [hE] at hfull
    have := hcore (𝒰 := 𝒰) (tp' := tp') (Yp := Yp) (v := v) (η' := η') (jθ := jθ)
      hδ0 hδ1 hap hpN hθ hη' hsub (fun k => (hYp k)) hball hfull (hF2 jθ hjθ)
    rw [hE]
    exact this
  · have hempty : ({k ∈ tp' | ML2Reduction.coarseNode 𝒰.cover.toChain a p k = jθ} : Finset ι)
        = ∅ := by
      refine Finset.eq_empty_of_forall_notMem ?_
      intro k hk
      obtain ⟨hk', hkeq⟩ := Finset.mem_filter.mp hk
      exact hjθ (hkeq ▸ ML2Reduction.coarseNode_mem 𝒰.cover.toChain
        (le_trans hap hpN) (hsub hk'))
    rw [hE, hempty, ShadedBody.multiplicity_empty]
    simp

end ParRow

section FineRow

open Classical in
/-- `Kakeya.ShadedTube.translate` and `Tube.translate` agree on the underlying tube. -/
theorem shadedTube_translate_toTube {δ : NNReal} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (S : ShadedTube δ E) (v : E) : (S.translate v).toTube = (S.toTube).translate v := rfl

open Classical in
/-- **Conjunct 2 (`hfine`, the inner factor at the leaf scale) of
`Kakeya.ML2Core.FourFactorRowsAt`, discharged.**

`Kakeya.ML2Core.exists_fine_factor` (`K_KT(β)` on a fibre at the leaf scale) with

* the ball row from the block's `hballleaf` through the shading's tube identity;
* the `Δ_max` row from the block's `hmax` by `Kakeya.ML2Core.maxDensity_le_of_translate_subset`
  (translation invariance and monotonicity), at the cost of the one scalar `ηin ≤ η`;
* `hfullfine` the **named residual**: a fullness lower bound on the leaf fibre of the split's own
  leaf shading `Y'`.  It is not in the antecedent block: `hdense`/`hlam` bound the fullness of
  `(u, T)`, and `Y'`'s shades are a refinement of `T`'s that the row does not mention.

**Family:** the leaf fibre `{i ∈ {i ∈ u | assign b i ∈ t₁} | assign b i = jτ}`;
**shading:** `Y'`, translated by the seam's `v`.  **Level pair:** `b` → leaf. -/
theorem exists_fineRow_of_site {β : ℝ} (hβ0 : 0 ≤ β)
    (hKT : Kakeya.KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β) {εf : ℝ} (hεf : 0 < εf) :
    ∃ η > (0 : ℝ), ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} {u : Finset ι} {Cu : NNReal}
        {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
        (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
        {t₁ : Finset ι} {b : ℕ} {v : EuclideanSpace ℝ (Fin 3)} {ηin : ℝ},
        δ ≤ 1 → ηin ≤ η →
        (∀ i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι),
          ((T i).translate v).carrier
            ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
        Kakeya.maxDensity u (fun i => (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-ηin) →
        (∀ (Y' : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
          (∀ i, (Y' i).toTube = ((T i).translate v).toTube) → ∀ jτ : ι,
          (δ : NNReal) ^ η ≤ ShadedBody.fullness
            ({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
              𝒰.cover.assign b i = jτ} : Finset ι) (fun i => (Y' i).toShadedBody)) →
        (∀ (Y' : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
          (∀ i, (Y' i).toTube = ((T i).translate v).toTube) → ∀ jτ : ι,
          ShadedBody.multiplicity
              ({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
                𝒰.cover.assign b i = jτ} : Finset ι) (fun i => (Y' i).toShadedBody)
            ≤ (δ : ENNReal) ^ (-εf)
              * ((({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
                  𝒰.cover.assign b i = jτ} : Finset ι).card : ENNReal)) ^ β) := by
  classical
  obtain ⟨η, hη, hev⟩ := exists_fine_factor.{u} (E := EuclideanSpace ℝ (Fin 3)) hβ0 hKT hεf
  refine ⟨η, hη, ?_⟩
  filter_upwards [hev] with δ hδ
  intro ι u Cu T 𝒰 t₁ b v ηin hδ1 hηin hballleaf hmax hfullfine Y' hY' jτ
  set f : Finset ι := ({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
    𝒰.cover.assign b i = jτ} : Finset ι) with hf
  have hfu : f ⊆ u := by
    intro i hi
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).1
  have hY'tube : ∀ i, (Y' i).toTube = ((T i).toTube).translate v := fun i =>
    (hY' i).trans (shadedTube_translate_toTube (T i) v)
  have hball : ∀ i ∈ f, (Y' i).carrier
      ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
    intro i hi
    have hc : (Y' i).carrier = ((T i).translate v).carrier :=
      congrArg (fun A : Tube δ (EuclideanSpace ℝ (Fin 3)) => A.carrier) (hY' i)
    rw [hc]
    exact hballleaf i (Finset.mem_filter.mp hi).1
  have hmaxf : Kakeya.maxDensity f (fun i => (Y' i).toConvexSpaceBody)
      ≤ (δ : ENNReal) ^ (-η) := by
    refine le_trans (le_trans (maxDensity_le_of_translate_subset hfu hY'tube) hmax) ?_
    exact ENNReal.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hδ1) (by linarith)
  exact hδ f Y' hball hmaxf (hfullfine Y' hY' jτ)

end FineRow

section CoarseRow

open Classical in
/-- **Conjunct 5 (`hcoarse`, the outer factor at level `a`) of
`Kakeya.ML2Core.FourFactorRowsAt`, discharged -- with its residuals named.**

`Kakeya.ML2Core.exists_coarse_factor` (GWZ Lemma 3.7 with the two scales decoupled) at the tube
scale `ρ_a` and the auxiliary scale `δ`.  Its loss is `εc = ε + ηc`.

**Three named residuals, and none of them is in the antecedent block.**  The split returns only
`tθ' ⊆ 𝒞.indexSet a` (`Kakeya.ML2Reduction.exists_spineThreeScale`), so the row is quantified over
*every* subset of the level-`a` index set, while the seam's `hz3` supplies a ball row on `t₀` only:

* `hballcoarse` -- the translated level-`a` nodes of `tθ'` lie in `B₁`.  For `tθ' ⊆ t₀` this is
  `hz3`; for an arbitrary `tθ' ⊆ indexSet a` it is **false** (a distant level-`a` node translated
  by the seam's `v` leaves `B₁`), which is the same defect
  `Kakeya.ML2Core.not_supplyRow_fourFactorRows` exhibits at conjunct 1.  Closing this row therefore
  wants the split's `tθ'` containment strengthened to `t₀`, not a new estimate.
* `hmaxcoarse` -- `Δ_max` of the level-`a` family.  **CORRECTION.**  B15
  first recorded this as absent from the block.  That was wrong:
  `Kakeya.ML2Reduction.IsKatzTaoDividingWindowLevels` **extends**
  `Kakeya.ML2Reduction.IsKatzTaoDividingWindow` (`SpineEveryScale.lean:252-255`), so
  `coarse_maxDensity_le` is in the block through `.toIsKatzTaoDividingWindow` -- the projection
  three existing consumers already use (`SpineRungWiring.lean:547/1221/2140`).  The row is therefore
  NOT a residual: `Kakeya.ML2Core.exists_coarseRow_of_window` below takes it from the window, and
  this abstract variant is kept only for a caller that has the density directly.  Source bound
  l.4045-4047 for `a > 0`; the standing `Δ_max ≤ δ^{-η₀}` (l.5814) at `a = 0`.
* `hfullcoarse` -- the outer family's fullness, the split's own but not returned by the
  translated wrapper.

**Family:** `tθ'` inside the level-`a` index set; **shading:** the split's `Yθ`, translated by the
seam's `v`.  **Level:** `a`. -/
theorem exists_coarseRow_of_site {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hKT : Kakeya.KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > (0 : ℝ), ∃ θ₀ : NNReal, 0 < θ₀ ∧ θ₀ ≤ 1 ∧
      ∀ {δ Cu : NNReal} {ι : Type u} {u : Finset ι}
        {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
        (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
        {t₁ : Finset ι} {a b : ℕ} {v : EuclideanSpace ℝ (Fin 3)} {ηc : ℝ},
        0 < δ → δ ≤ 1 → 0 ≤ ηc →
        Tube.gridScale δ (Tube.ssfGridLen δ) a ≤ θ₀ →
        a ≤ Tube.ssfGridLen δ →
        (∀ (tθ' : Finset ι), tθ' ⊆ (retainedLeafChain 𝒰 t₁ b).indexSet a →
          ∀ (Yθ : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) a)
              (EuclideanSpace ℝ (Fin 3))),
          (∀ l, (Yθ l).toTube = ((retainedLeafChain 𝒰 t₁ b).tube a l).translate v) →
          ∀ l ∈ tθ', (Yθ l).carrier
            ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
        (∀ (tθ' : Finset ι), tθ' ⊆ (retainedLeafChain 𝒰 t₁ b).indexSet a →
          ∀ (Yθ : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) a)
              (EuclideanSpace ℝ (Fin 3))),
          (∀ l, (Yθ l).toTube = ((retainedLeafChain 𝒰 t₁ b).tube a l).translate v) →
          Kakeya.maxDensity tθ' (fun l => (Yθ l).toConvexSpaceBody)
            ≤ (δ : ENNReal) ^ (-ηc)) →
        (∀ (tθ' : Finset ι), tθ' ⊆ (retainedLeafChain 𝒰 t₁ b).indexSet a →
          ∀ (Yθ : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) a)
              (EuclideanSpace ℝ (Fin 3))),
          (∀ l, (Yθ l).toTube = ((retainedLeafChain 𝒰 t₁ b).tube a l).translate v) →
          (δ : NNReal) ^ η ≤ ShadedBody.fullness tθ' (fun l => (Yθ l).toShadedBody)) →
        (∀ (tθ' : Finset ι), tθ' ⊆ (retainedLeafChain 𝒰 t₁ b).indexSet a →
          ∀ (Yθ : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) a)
              (EuclideanSpace ℝ (Fin 3))),
          (∀ l, (Yθ l).toTube = ((retainedLeafChain 𝒰 t₁ b).tube a l).translate v) →
          ShadedBody.multiplicity tθ' (fun l => (Yθ l).toShadedBody)
            ≤ (δ : ENNReal) ^ (-(ε + ηc)) * ((tθ'.card : ℕ) : ENNReal) ^ β) := by
  classical
  obtain ⟨η, hη, θ₀, hθ₀0, hθ₀1, hcore⟩ := exists_coarse_factor.{u}
    (E := EuclideanSpace ℝ (Fin 3)) hβ0 hβ1 hKT hε
  refine ⟨η, hη, θ₀, hθ₀0, hθ₀1, ?_⟩
  intro δ Cu ι u T 𝒰 t₁ a b v ηc hδ0 hδ1 hηc hθ haN hball hmaxc hfullc tθ' htθ' Yθ hYθ
  have hρa0 : 0 < Tube.gridScale δ (Tube.ssfGridLen δ) a := Tube.gridScale_pos hδ0 _ _
  have hδρa : δ ≤ Tube.gridScale δ (Tube.ssfGridLen δ) a :=
    ML2Core.delta_le_gridScale hδ0 hδ1 haN
  exact hcore hρa0 hθ δ hδ0 hδρa hηc tθ' Yθ (hball tθ' htθ' Yθ hYθ)
    (hfullc tθ' htθ' Yθ hYθ) (hmaxc tθ' htθ' Yθ hYθ)

end CoarseRow

section Assembly

open Classical in
/-- **`Kakeya.ML2Core.FourFactorRowsAt`, assembled: four of the five conjuncts discharged.**

The composition of `Kakeya.ML2Core.ballRow_pi_of_seam`, `Kakeya.ML2Core.exists_fineRow_of_site`,
`Kakeya.ML2Core.exists_parRow_of_site` and `Kakeya.ML2Core.exists_coarseRow_of_site`, with the
middle (VNS) factor `hmid` taken as a hypothesis.  The elaborator adjudicates that each producer's
conclusion is, verbatim, the conjunct it fills.

**What is left, by name.**  `hmid` -- the VNS middle factor at `(p, b)`, the only conjunct that is
not a defect estimate (l.4663-4664) -- and four fullness/ball/density residuals:
`hfullfine`, `hfullpar`, `hballcoarse`, `hmaxcoarse`, `hfullcoarse`.  The exponents are the
producers' own: `εf` free, `εp = ε + 2 η'`, `εc = ε' + ηcc`. -/
theorem exists_fourFactorRowsAt_of_site {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hKT : Kakeya.KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β)
    {εf ε ε' : ℝ} (hεf : 0 < εf) (hε : 0 < ε) (hε' : 0 < ε') :
    ∃ ηf ηp ηa : ℝ, 0 < ηf ∧ 0 < ηp ∧ 0 < ηa ∧
    ∃ θp θa : NNReal, 0 < θp ∧ θp ≤ 1 ∧ 0 < θa ∧ θa ≤ 1 ∧
      ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} {u : Finset ι} {Cu : NNReal}
        {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
        (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
        {t₀ t₁ : Finset ι} {a p b : ℕ} {v : EuclideanSpace ℝ (Fin 3)} {gmv ηin η' ηcc : ℝ},
        0 < δ → δ ≤ 1 → a ≤ p → p ≤ b → b ≤ Tube.ssfGridLen δ →
        Tube.gridScale δ (Tube.ssfGridLen δ) p ≤ θp →
        Tube.gridScale δ (Tube.ssfGridLen δ) a ≤ θa →
        0 ≤ η' → 0 ≤ ηcc → ηin ≤ ηf →
        -- the seam's own rows, from the antecedent block
        (∀ j ∈ t₁, ML2Reduction.coarseNode 𝒰.cover.toChain a b j ∈ t₀) →
        (∀ l ∈ t₀, ((𝒰.cover.tube a l).translate v).carrier
          ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
        (∀ i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι),
          ((T i).translate v).carrier
            ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
        Kakeya.maxDensity u (fun i => (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-ηin) →
        (∀ jθ ∈ 𝒰.cover.indexSet a,
          Kakeya.maxDensity (𝒰.nodesUnder p a jθ)
              (fun k => (𝒰.cover.tube p k).toConvexSpaceBody)
            ≤ (δ : ENNReal) ^ (-(2 * η'))) →
        -- the named residuals
        (∀ (Y' : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
          (∀ i, (Y' i).toTube = ((T i).translate v).toTube) → ∀ jτ : ι,
          (δ : NNReal) ^ ηf ≤ ShadedBody.fullness
            ({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
              𝒰.cover.assign b i = jτ} : Finset ι) (fun i => (Y' i).toShadedBody)) →
        (∀ (tp' : Finset ι), tp' ⊆ ML2Reduction.activeNodes (retainedLeafChain 𝒰 t₁ b) p →
          ∀ (Yp : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) p)
              (EuclideanSpace ℝ (Fin 3))),
          (∀ k, (Yp k).toTube = ((retainedLeafChain 𝒰 t₁ b).tube p k).translate v) → ∀ jθ : ι,
          (δ : NNReal) ^ ηp ≤ ShadedBody.fullness
              ({k ∈ tp' | ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) a p k = jθ}
                : Finset ι)
              (fun k => (Yp k).toShadedBody)) →
        (∀ (tθ' : Finset ι), tθ' ⊆ (retainedLeafChain 𝒰 t₁ b).indexSet a →
          ∀ (Yθ : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) a)
              (EuclideanSpace ℝ (Fin 3))),
          (∀ l, (Yθ l).toTube = ((retainedLeafChain 𝒰 t₁ b).tube a l).translate v) →
          ∀ l ∈ tθ', (Yθ l).carrier
            ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
        (∀ (tθ' : Finset ι), tθ' ⊆ (retainedLeafChain 𝒰 t₁ b).indexSet a →
          ∀ (Yθ : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) a)
              (EuclideanSpace ℝ (Fin 3))),
          (∀ l, (Yθ l).toTube = ((retainedLeafChain 𝒰 t₁ b).tube a l).translate v) →
          Kakeya.maxDensity tθ' (fun l => (Yθ l).toConvexSpaceBody)
            ≤ (δ : ENNReal) ^ (-ηcc)) →
        (∀ (tθ' : Finset ι), tθ' ⊆ (retainedLeafChain 𝒰 t₁ b).indexSet a →
          ∀ (Yθ : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) a)
              (EuclideanSpace ℝ (Fin 3))),
          (∀ l, (Yθ l).toTube = ((retainedLeafChain 𝒰 t₁ b).tube a l).translate v) →
          (δ : NNReal) ^ ηa ≤ ShadedBody.fullness tθ' (fun l => (Yθ l).toShadedBody)) →
        -- the VNS middle factor, the one conjunct this block does not produce
        (∀ (tτ' : Finset ι), tτ' ⊆ ML2Reduction.activeNodes (retainedLeafChain 𝒰 t₁ b) b →
          ∀ (Yτ' : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) b)
              (EuclideanSpace ℝ (Fin 3))),
          (∀ j, (Yτ' j).toTube = ((retainedLeafChain 𝒰 t₁ b).tube b j).translate v) → ∀ jp : ι,
          ShadedBody.multiplicity
              ({j ∈ tτ' | ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) p b j = jp}
                : Finset ι)
              (fun j => (Yτ' j).toShadedBody)
            ≤ (δ : ENNReal) ^ gmv
              * ((({j ∈ tτ' | ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) p b j = jp} :
                  Finset ι).card : ENNReal)) ^ β) →
        FourFactorRowsAt 𝒰 v t₁ a p b β εf gmv (ε + 2 * η') (ε' + ηcc) := by
  classical
  obtain ⟨ηf, hηf, hfineRow⟩ := exists_fineRow_of_site.{u} hβ0 hKT hεf
  obtain ⟨ηp, hηp, θp, hθp0, hθp1, hparRow⟩ := exists_parRow_of_site.{u} hβ0 hβ1 hKT hε
  obtain ⟨ηa, hηa, θa, hθa0, hθa1, hcoarseRow⟩ := exists_coarseRow_of_site.{u} hβ0 hβ1 hKT hε'
  refine ⟨ηf, ηp, ηa, hηf, hηp, hηa, θp, θa, hθp0, hθp1, hθa0, hθa1, ?_⟩
  filter_upwards [hfineRow] with δ hfine
  intro ι u Cu T 𝒰 t₀ t₁ a p b v gmv ηin η' ηcc hδ0 hδ1 hap hpb hbN hθpδ hθaδ hη' hηcc hηin
    hz2 hz3 hballleaf hmax hF2 hfullfine hfullpar hballcoarse hmaxcoarse hfullcoarse hmid
  have haN : a ≤ Tube.ssfGridLen δ := le_trans (le_trans hap hpb) hbN
  exact ⟨ballRow_pi_of_seam 𝒰 hap hpb hbN hz2 hz3,
    hfine 𝒰 hδ1 hηin hballleaf hmax hfullfine,
    hmid,
    hparRow 𝒰 hδ0 hδ1 hap hpb hbN hθpδ hη' hz2 hz3 hF2 hfullpar,
    hcoarseRow 𝒰 hδ0 hδ1 hηcc hθaδ haN hballcoarse hmaxcoarse hfullcoarse⟩

end Assembly

section MidRow

open Classical in
/-- **The level-`b` nodes of one `(p,b)`-fibre sit inside their level-`p` ancestor, after the
seam's translate.**  `Kakeya.ML2Reduction.tube_le_coarseNode` read at the fibre's own `jp`. -/
theorem fibre_subset_parentTube {ι : Type u} {δ Cu : NNReal} {u : Finset ι}
    {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
    {t₁ tτ' : Finset ι} {p b : ℕ} {v : EuclideanSpace ℝ (Fin 3)} (hpb : p ≤ b)
    (hbN : b ≤ Tube.ssfGridLen δ)
    (htτ' : tτ' ⊆ ML2Reduction.activeNodes (retainedLeafChain 𝒰 t₁ b) b)
    {Yτ' : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) b)
      (EuclideanSpace ℝ (Fin 3))}
    (hYτ' : ∀ j, (Yτ' j).toTube = ((retainedLeafChain 𝒰 t₁ b).tube b j).translate v)
    (jp : ι) :
    ∀ j ∈ ({j ∈ tτ' | ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) p b j = jp}
        : Finset ι),
      (Yτ' j).carrier
        ⊆ (((retainedLeafChain 𝒰 t₁ b).tube p jp).translate v).carrier := by
  classical
  intro j hj
  obtain ⟨hjt, hjp⟩ := Finset.mem_filter.mp hj
  have hc : (Yτ' j).carrier
      = (((retainedLeafChain 𝒰 t₁ b).tube b j).translate v).carrier :=
    congrArg (fun A : Tube (Tube.gridScale δ (Tube.ssfGridLen δ) b)
      (EuclideanSpace ℝ (Fin 3)) => A.carrier) (hYτ' j)
  rw [hc]
  refine translate_carrier_subset_of_le _ _ v ?_
  have h := ML2Reduction.tube_le_coarseNode (retainedLeafChain 𝒰 t₁ b) hpb hbN (htτ' hjt)
  rwa [hjp] at h

open Classical in
/-- **Conjunct 3 (`hmid`, the VNS middle factor at `(p, b)`), produced.**

This is the shape bridge the site side owed.  The existing middle factor
`Kakeya.ML2Reduction.fine_factor_of_lemma91At_of_canonicalCover` runs at the **rescaled** scale
`δ'` of a `Tube.IsRescalingSituation`, on one family and one shading; the row wants a bound at
the ambient `δ`, on **every** `(p,b)`-node fibre and every shading the split hands back.  Four
steps close it, and each is a existing device:

1. the rescaling situation is at `(ρ_p, ρ_b, δ')` -- ambient tube scale `ρ_p`, inner scale `ρ_b`,
   output `δ̃ = ρ_b/(2ρ_p)` (l.4506).  It is a hypothesis here and is CONSTRUCTED by
   `Kakeya.ML2Core.midRescalingSituation` below, from grid-scale facts alone;
2. `hsub` -- `Kakeya.ML2Core.fibre_subset_parentTube`, i.e. `tube_le_coarseNode` at the fibre's
   own `jp`, so `T₀` is the translated level-`p` node tube;
3. `hcb`/`hcnt`/`huni` come from ONE object per fibre, the hand-back
   `Kakeya.VeryNotSticky.exists_centredHandBack_uniform_and_countTransport`;
4. `Kakeya.ML2Reduction.outerFamily_multiplicity` -- an EQUALITY, no loss -- moves the bound off
   the normalised family back onto the split's own `Yτ'`.

**The one scalar this costs**, and it is named rather than absorbed: `hscale`,
`(δ')^ν ≤ δ^{gmv}`.  The source is explicit that the middle factor's gain is re-expressed at the
ambient scale and that it is `δ^G`, **not** `δ^{ν_{J+1}}` (l.4655-4658); `hscale` is exactly that
re-expression and nothing more.  It is a relation between two scales, carries no geometry, and is
the only place where `δ̃` and `δ` meet.

**Family:** the `(p,b)` fibre `{j ∈ tτ' | coarseNode 𝒞 p b j = jp}`; **shading:** the split's
`Yτ'`, translated by the seam's `v`.  **Level pair:** `(p, b)`. -/
theorem midRow_of_handBack {ι : Type u} {δ δ' Cu : NNReal} {u : Finset ι}
    {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
    {t₁ : Finset ι} {p b : ℕ} {v : EuclideanSpace ℝ (Fin 3)}
    {R β ϖ ζ ν ν₀ ηd cst qc gmv : ℝ}
    (hpb : p ≤ b) (hbN : b ≤ Tube.ssfGridLen δ)
    (hsit : Tube.IsRescalingSituation (Tube.gridScale δ (Tube.ssfGridLen δ) p)
      (Tube.gridScale δ (Tube.ssfGridLen δ) b) δ' R 3)
    (hR : 0 < R) (hR1 : 1 ≤ R)
    (hτσ : ((Tube.gridScale δ (Tube.ssfGridLen δ) b : NNReal) : ℝ)
        / ((Tube.gridScale δ (Tube.ssfGridLen δ) p : NNReal) : ℝ) ≤ 4 * (δ' : ℝ))
    (hδ'0 : 0 < δ') (hϖ0 : 0 ≤ ϖ) (hβ0 : 0 ≤ β) (hqc0 : 0 < qc)
    (hνqc : ν + 3 * qc ≤ ν₀) (h3qc : 3 * qc ≤ ηd)
    (hL : ML2Reduction.Lemma91At.{u} β ϖ ζ ν₀ ηd δ')
    (hζ : ζ * (1 - ϖ) ≤ ηd + 2 * ϖ)
    (hloss : ML2Reduction.outerLoss R ≤ δ' ^ (-cst))
    -- l.4655-4658: the middle factor's gain is read at the ambient scale, and it is `δ^G`
    (hscale : (δ' : ENNReal) ^ ν ≤ (δ : ENNReal) ^ gmv)
    -- the per-fibre hand-back: ONE object supplying `hcb`, `hcnt` and `huni`
    (hhb : ∀ (tτ' : Finset ι),
      tτ' ⊆ ML2Reduction.activeNodes (retainedLeafChain 𝒰 t₁ b) b →
      ∀ (Yτ' : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) b)
          (EuclideanSpace ℝ (Fin 3))),
      (∀ j, (Yτ' j).toTube = ((retainedLeafChain 𝒰 t₁ b).tube b j).translate v) →
      ∀ jp : ι,
      ({j ∈ tτ' | ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) p b j = jp}
        : Finset ι).Nonempty →
      ∃ (s'' : Finset ι) (U'' : ι → ShadedTube δ' (EuclideanSpace ℝ (Fin 3))),
        s'' ⊆ ({j ∈ tτ' | ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) p b j = jp}
          : Finset ι) ∧
        Kakeya.VeryNotSticky.CentredHandBack hsit hR
            (((retainedLeafChain 𝒰 t₁ b).tube p jp).translate v) 0 qc
            ({j ∈ tτ' | ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) p b j = jp}
              : Finset ι) s'' Yτ' U'' ∧
        (∃ C : NNReal, 1 ≤ C ∧ (C : ENNReal) ≤ (δ' : ENNReal) ^ (-ηd) ∧
          Nonempty (ShadedTube.ShadedUniformTubeSet s'' U'' (Tube.ssfGridLen δ') C)) ∧
        (∀ ρ : NNReal, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
          ∃ (κ : Type u) (tρ : Finset κ) (Tρ : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
            (tρ : Set κ).Pairwise
              (fun j k ↦ _root_.IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) ∧
            (∀ j ∈ tρ, ∃ i ∈ s'', (U'' i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) ∧
            (ρ : ℝ) ^ (-2 - ζ) ≤ (tρ.card : ℝ))) :
    ∀ (tτ' : Finset ι), tτ' ⊆ ML2Reduction.activeNodes (retainedLeafChain 𝒰 t₁ b) b →
      ∀ (Yτ' : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) b)
          (EuclideanSpace ℝ (Fin 3))),
      (∀ j, (Yτ' j).toTube = ((retainedLeafChain 𝒰 t₁ b).tube b j).translate v) → ∀ jp : ι,
      ShadedBody.multiplicity
          ({j ∈ tτ' | ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) p b j = jp} : Finset ι)
          (fun j => (Yτ' j).toShadedBody)
        ≤ (δ : ENNReal) ^ gmv
          * ((({j ∈ tτ' | ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) p b j = jp} :
              Finset ι).card : ENNReal)) ^ β := by
  classical
  intro tτ' htτ' Yτ' hYτ' jp
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  rcases Finset.eq_empty_or_nonempty
      ({j ∈ tτ' | ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) p b j = jp} : Finset ι)
    with hemp | hfne
  · rw [hemp, ShadedBody.multiplicity_empty]
    simp
  obtain ⟨s'', U'', hs''sub, hcb, huni, hcnt⟩ := hhb tτ' htτ' Yτ' hYτ' jp hfne
  have hsub := fibre_subset_parentTube 𝒰 hpb hbN htτ' hYτ' jp
  have h10 := ML2Reduction.fine_factor_of_lemma91At_of_canonicalCover
    (ν := ν) hL hζ hsit hR hR1 hτσ hδ'0 hϖ0 hβ0 hqc0 hνqc h3qc
    (((retainedLeafChain 𝒰 t₁ b).tube p jp).translate v) 0 hs''sub Yτ' U'' hcb hsub hloss
    huni hcnt
  rw [ML2Reduction.outerFamily_multiplicity hn hsit hR hτσ hsub] at h10
  exact h10.trans (mul_le_mul' hscale le_rfl)

/-- **The source's middle-factor scale** `δ̃ = ρ_b/(2 ρ_p)` (l.4506). -/
noncomputable def midScale (δ : NNReal) (N p b : ℕ) : NNReal :=
  Tube.gridScale δ N b / (2 * Tube.gridScale δ N p)

/-- **The `(p,b)` rescaling situation, CONSTRUCTED** -- ambient tube scale `ρ_p`, inner scale
`ρ_b`, output the source's own `δ̃ = ρ_b/(2ρ_p)` (l.4506).  Every field is a grid-scale fact
except the two named scalars: `hgap`, the source's own requirement that the middle family be at a
scale below `1/2` of its parent (without it `δ̃ > 1/4` and the outer tube leaves `B₁`), and
`hRC`, the normalisation constant's threshold on the ambient radius.

So step 1 of `Kakeya.ML2Core.midRow_of_handBack` is not an assumption: it is built here. -/
theorem midRescalingSituation {δ : NNReal} {N p b : ℕ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hpb : p ≤ b)
    {R : ℝ} (hRC : (Tube.normalization.C 3 : ℝ) ≤ R)
    (hgap : ((Tube.gridScale δ N b : NNReal) : ℝ)
      ≤ ((Tube.gridScale δ N p : NNReal) : ℝ) / 2) :
    Tube.IsRescalingSituation (Tube.gridScale δ N p) (Tube.gridScale δ N b)
      (midScale δ N p b) R 3 := by
  have hp0 : 0 < Tube.gridScale δ N p := Tube.gridScale_pos hδ0 _ _
  have hb0 : 0 < Tube.gridScale δ N b := Tube.gridScale_pos hδ0 _ _
  have hp0R : (0 : ℝ) < ((Tube.gridScale δ N p : NNReal) : ℝ) := by exact_mod_cast hp0
  have hb0R : (0 : ℝ) < ((Tube.gridScale δ N b : NNReal) : ℝ) := by exact_mod_cast hb0
  have hcoe : ((midScale δ N p b : NNReal) : ℝ)
      = ((Tube.gridScale δ N b : NNReal) : ℝ) / (2 * ((Tube.gridScale δ N p : NNReal) : ℝ)) := by
    simp [midScale]
  refine ⟨hp0, Tube.gridScale_antitone hδ0 hδ1 N hpb, Tube.gridScale_le_one hδ1 _ _, ?_, ?_, ?_,
    hRC⟩
  · have : (0 : ℝ) < ((midScale δ N p b : NNReal) : ℝ) := by rw [hcoe]; positivity
    exact_mod_cast this
  · rw [hcoe]
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  · rw [hcoe]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith

/-- The `hτσ` row at the constructed scale: it is an equality up to the factor `2`, so it costs
nothing. -/
theorem midScale_hτσ {δ : NNReal} {N p b : ℕ} (hδ0 : 0 < δ) :
    ((Tube.gridScale δ N b : NNReal) : ℝ) / ((Tube.gridScale δ N p : NNReal) : ℝ)
      ≤ 4 * ((midScale δ N p b : NNReal) : ℝ) := by
  have hp0 : 0 < Tube.gridScale δ N p := Tube.gridScale_pos hδ0 _ _
  have hp0R : (0 : ℝ) < ((Tube.gridScale δ N p : NNReal) : ℝ) := by exact_mod_cast hp0
  have hcoe : ((midScale δ N p b : NNReal) : ℝ)
      = ((Tube.gridScale δ N b : NNReal) : ℝ) / (2 * ((Tube.gridScale δ N p : NNReal) : ℝ)) := by
    simp [midScale]
  rw [hcoe]
  rw [div_le_iff₀ hp0R]
  have hb0R : (0 : ℝ) ≤ ((Tube.gridScale δ N b : NNReal) : ℝ) := by positivity
  field_simp
  nlinarith

/-- **The normalised ambient radius is a CHOICE, not an assumption.**  `hRC`, `hR` and `hR1` --
the three rows `Kakeya.ML2Core.midRescalingSituation` and `Kakeya.ML2Core.midRow_of_handBack` ask
of `R` -- are all met by the canonical value `R := max 1 (Tube.normalization.C 3)`.  So the
middle-factor block carries no scalar assumption about `R`. -/
theorem midRadius_spec :
    (0 : ℝ) < max 1 (Tube.normalization.C 3 : ℝ) ∧ (1 : ℝ) ≤ max 1 (Tube.normalization.C 3 : ℝ) ∧
      (Tube.normalization.C 3 : ℝ) ≤ max 1 (Tube.normalization.C 3 : ℝ) :=
  ⟨lt_of_lt_of_le zero_lt_one (le_max_left _ _), le_max_left _ _, le_max_right _ _⟩

end MidRow


section CoarseDensity

open Classical in
/-- **`hmaxcoarse` MEASURED: it is not a missing window field, it is one scalar on the tower's own
fibre array.**

**CORRECTION : the field is NOT missing.**
`Kakeya.ML2Reduction.IsKatzTaoDividingWindowLevels` extends
`Kakeya.ML2Reduction.IsKatzTaoDividingWindow`, so `coarse_maxDensity_le` reaches the block through
`.toIsKatzTaoDividingWindow`, and `Kakeya.ML2Core.exists_coarseRow_of_window` is the route of
record.  What follows is a second, independent supply, kept because it needs no window at all:
`Kakeya.ML2Core.maxDensity_indexSet_le_mul_towerDensityArrayFibre` (`eqdividingKfirst`,
l.2695-2696): the level-`a` family's maximal density is at most `Cu` times the **fibre** array at
`(0, a)` -- Condition R's permissive half, and `Cu` is the hierarchy's own `δ`-free constant.

Both of its inputs are already in the antecedent block: `hball` is the block's
`∀ i ∈ u, (T i).carrier ⊆ B₁` row and `hs` is its `u.Nonempty`.  So the residual is the single
scalar `hband : Cu * towerDensityArrayFibre 𝒰 0 a ≤ δ^{-ηcc}` -- a bound on the tower's own
two-level density profile, which is what `level_density_band` bands.

**Family:** the level-`a` index set; **shading:** the split's `Yθ`, translated.  **Level:** `a`. -/
theorem maxCoarseRow_of_block {ι : Type u} {δ Cu : NNReal} {u : Finset ι}
    {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
    {t₁ : Finset ι} {a b : ℕ} {v : EuclideanSpace ℝ (Fin 3)} {ηcc : ℝ}
    (hune : u.Nonempty)
    (hballu : ∀ i ∈ u, (T i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (haN : a ≤ Tube.ssfGridLen δ)
    (hband : (Cu : ENNReal) * ML2Core.towerDensityArrayFibre 𝒰 0 a
      ≤ (δ : ENNReal) ^ (-ηcc)) :
    ∀ (tθ' : Finset ι), tθ' ⊆ (retainedLeafChain 𝒰 t₁ b).indexSet a →
      ∀ (Yθ : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) a)
          (EuclideanSpace ℝ (Fin 3))),
      (∀ l, (Yθ l).toTube = ((retainedLeafChain 𝒰 t₁ b).tube a l).translate v) →
      Kakeya.maxDensity tθ' (fun l => (Yθ l).toConvexSpaceBody)
        ≤ (δ : ENNReal) ^ (-ηcc) := by
  classical
  intro tθ' htθ' Yθ hYθ
  refine le_trans (le_trans (ML2Core.maxDensity_le_of_translate_subset
    (t := tθ') (u := 𝒰.cover.indexSet a) htθ' hYθ) ?_) hband
  exact ML2Core.maxDensity_indexSet_le_mul_towerDensityArrayFibre 𝒰 hune hballu haN

end CoarseDensity

section SplitFull

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

open Classical in
/-- **The three-scale split, with the fullness clauses KEPT** (l.4675-4677: *"the four
lower-fullness estimates refer to the same mass-coupled refinements"*).

`Kakeya.ML2Reduction.exists_spineThreeScale` is the same three applications of
`Kakeya.ML2Reduction.exists_spineOneScale`; it returns the level-`p` fullness clause and discards
the other four, and `Kakeya.ML2Core.exists_spineThreeScale_ofChain_translated` discards even that
one.  This variant returns, in addition:

* `hfullθ` -- the outer family's fullness, at the three-fold `spineScaleLoss`;
* `href1` -- the first application's `ShadedBody.IsCRefinement`, from which the **leaf fibre's**
  fullness follows by the mediant (`Kakeya.ML2Core.exists_fibre_fullness_le'`);
* `href3` -- the third application's, likewise for the **`(a,p)` fibre**.

Nothing new is proved: every clause is already in `exists_spineOneScale`'s conclusion, and this is
the source's own remark that the four estimates are one object.  The outer index set is a
**parameter** `u`, so a caller may run the outer level on the seam's `t₀` -- which is what makes
the outer ball row (`hballcoarse`) suppliable. -/
theorem exists_spineThreeScale_full
    {δ τ π θ : ℝ≥0} (hδ : 0 < δ) (hδτ : δ ≤ τ) (hτπ : τ ≤ π) (hπθ : π ≤ θ) (hθ1 : θ ≤ 1)
    {ιf ιm ιp ιc : Type u} {s : Finset ιf} {t : Finset ιm} {tp : Finset ιp} {u : Finset ιc}
    (V : ιf → ShadedTube δ E) (Tτ : ιm → Tube τ E) (Tπ : ιp → Tube π E) (Tθ : ιc → Tube θ E)
    (pτ : ιf → ιm) (pπ : ιm → ιp) (pθ : ιp → ιc)
    (hball : ∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall (0 : E) 1)
    (hballτ : ∀ j ∈ t, (Tτ j).carrier ⊆ Metric.closedBall (0 : E) 1)
    (hballπ : ∀ k ∈ tp, (Tπ k).carrier ⊆ Metric.closedBall (0 : E) 1)
    (hmapsτ : ∀ i ∈ s, pτ i ∈ t)
    (hleτ : ∀ i ∈ s, (V i).toConvexSpaceBody ≤ (Tτ (pτ i)).toConvexSpaceBody)
    (hmapsπ : ∀ j ∈ t, pπ j ∈ tp)
    (hleπ : ∀ j ∈ t, (Tτ j).toConvexSpaceBody ≤ (Tπ (pπ j)).toConvexSpaceBody)
    (hmapsθ : ∀ k ∈ tp, pθ k ∈ u)
    (hleθ : ∀ k ∈ tp, (Tπ k).toConvexSpaceBody ≤ (Tθ (pθ k)).toConvexSpaceBody) :
    ∃ tτ' ⊆ t, ∃ tπ' ⊆ tp, ∃ tθ' ⊆ u,
      ∃ (Yτ' : ιm → ShadedTube τ E) (Yπ Yπ' : ιp → ShadedTube π E) (Yθ : ιc → ShadedTube θ E)
        (Y' : ιf → ShadedTube δ E),
        (∀ j, (Yτ' j).toTube = Tτ j) ∧
        (∀ k, (Yπ k).toTube = Tπ k) ∧
        (∀ k, (Yπ' k).toTube = Tπ k) ∧
        (∀ l, (Yθ l).toTube = Tθ l) ∧
        (∀ i, (Y' i).toTube = (V i).toTube) ∧
        (∀ i, (Y' i).shade ⊆ (V i).shade) ∧
        (∀ k, (Yπ' k).shade ⊆ (Yπ k).shade) ∧
        (0 < ∑ i ∈ s, volume (V i).shade → tτ'.Nonempty ∧ tπ'.Nonempty ∧ tθ'.Nonempty) ∧
        -- the level-`p` fullness (the existing clause)
        (ML2Reduction.spineScaleLoss (Module.finrank ℝ E) s.card δ *
              ML2Reduction.spineScaleLoss (Module.finrank ℝ E) tτ'.card τ)⁻¹ *
            ShadedBody.fullness s (fun i => (V i).toShadedBody)
          ≤ ShadedBody.fullness tπ' (fun k => (Yπ k).toShadedBody) ∧
        -- KEPT (1): the outer family's fullness
        (ML2Reduction.spineScaleLoss (Module.finrank ℝ E) s.card δ *
              ML2Reduction.spineScaleLoss (Module.finrank ℝ E) tτ'.card τ *
              ML2Reduction.spineScaleLoss (Module.finrank ℝ E) tπ'.card π)⁻¹ *
            ShadedBody.fullness s (fun i => (V i).toShadedBody)
          ≤ ShadedBody.fullness tθ' (fun l => (Yθ l).toShadedBody) ∧
        -- KEPT (2): the leaf refinement, for the fine fibre's mediant
        ShadedBody.IsCRefinement ({i ∈ s | pτ i ∈ tτ'} : Finset ιf)
            (fun i => (Y' i).toShadedBody) s (fun i => (V i).toShadedBody)
            (ML2Reduction.spineScaleLoss (Module.finrank ℝ E) s.card δ)⁻¹ ∧
        -- KEPT (3): the level-`p` refinement, for the `(a,p)` fibre's mediant
        ShadedBody.IsCRefinement ({k ∈ tπ' | pθ k ∈ tθ'} : Finset ιp)
            (fun k => (Yπ' k).toShadedBody) tπ' (fun k => (Yπ k).toShadedBody)
            (ML2Reduction.spineScaleLoss (Module.finrank ℝ E) tπ'.card π)⁻¹ ∧
        (∀ jτ ∈ tτ', ∀ jπ ∈ tπ', ∀ jθ ∈ tθ',
          ShadedBody.multiplicity s (fun i => (V i).toShadedBody)
            ≤ ((ML2Reduction.spineScaleLoss (Module.finrank ℝ E) s.card δ *
                  ML2Reduction.spineScaleLoss (Module.finrank ℝ E) tτ'.card τ *
                  ML2Reduction.spineScaleLoss (Module.finrank ℝ E) tπ'.card π : ℝ≥0) : ENNReal)
              * ShadedBody.multiplicity {i ∈ s | pτ i = jτ} (fun i => (Y' i).toShadedBody)
              * ShadedBody.multiplicity {j ∈ tτ' | pπ j = jπ} (fun j => (Yτ' j).toShadedBody)
              * ShadedBody.multiplicity {k ∈ tπ' | pθ k = jθ} (fun k => (Yπ' k).toShadedBody)
              * ShadedBody.multiplicity tθ' (fun l => (Yθ l).toShadedBody)) := by
  classical
  have hτ0 : 0 < τ := lt_of_lt_of_le hδ hδτ
  have hπ0 : 0 < π := lt_of_lt_of_le hτ0 hτπ
  have hτ1 : τ ≤ 1 := hτπ.trans (hπθ.trans hθ1)
  have hπ1 : π ≤ 1 := hπθ.trans hθ1
  obtain ⟨tτ', htτ', Yτ, Y', hYτtube, hY'tube, hY'shade, hτne, hτmass, _hc1, hf1, hr1,
      hprod1⟩ :=
    ML2Reduction.exists_spineOneScale (E := E) hδ hδτ hτ1 V Tτ pτ hball hmapsτ hleτ
  have hYτbody : ∀ j, (Yτ j).toConvexSpaceBody = (Tτ j).toConvexSpaceBody := fun j =>
    congrArg (fun T : Tube τ E => T.toConvexSpaceBody) (hYτtube j)
  have hballYτ : ∀ j ∈ tτ', (Yτ j).carrier ⊆ Metric.closedBall (0 : E) 1 := by
    intro j hj
    have hc : (Yτ j).carrier = (Tτ j).carrier :=
      congrArg (fun B : ConvexSpaceBody E => B.carrier) (hYτbody j)
    rw [hc]
    exact hballτ j (htτ' hj)
  obtain ⟨tπ', htπ', Yπ, Yτ', hYπtube, hYτ'tube, _hYτ'shade, hπne, hπmass, _hc2, hf2, _hr2,
      hprod2⟩ :=
    ML2Reduction.exists_spineOneScale (E := E) hτ0 hτπ hπ1 Yτ Tπ pπ hballYτ
      (fun j hj => hmapsπ j (htτ' hj))
      (fun j hj => by rw [hYτbody j]; exact hleπ j (htτ' hj))
  have hYπbody : ∀ k, (Yπ k).toConvexSpaceBody = (Tπ k).toConvexSpaceBody := fun k =>
    congrArg (fun T : Tube π E => T.toConvexSpaceBody) (hYπtube k)
  have hballYπ : ∀ k ∈ tπ', (Yπ k).carrier ⊆ Metric.closedBall (0 : E) 1 := by
    intro k hk
    have hc : (Yπ k).carrier = (Tπ k).carrier :=
      congrArg (fun B : ConvexSpaceBody E => B.carrier) (hYπbody k)
    rw [hc]
    exact hballπ k (htπ' hk)
  obtain ⟨tθ', htθ', Yθ, Yπ', hYθtube, hYπ'tube, hYπ'shade, hθne, _hθmass, _hc3, hf3, hr3,
      hprod3⟩ :=
    ML2Reduction.exists_spineOneScale (E := E) hπ0 hπθ hθ1 Yπ Tθ pθ hballYπ
      (fun k hk => hmapsθ k (htπ' hk))
      (fun k hk => by rw [hYπbody k]; exact hleθ k (htπ' hk))
  refine ⟨tτ', htτ', tπ', htπ', tθ', htθ', Yτ', Yπ, Yπ', Yθ, Y',
    fun j => (hYτ'tube j).trans (hYτtube j), hYπtube,
    fun k => (hYπ'tube k).trans (hYπtube k),
    hYθtube, hY'tube, hY'shade, hYπ'shade, ?_, ?_, ?_, hr1, hr3, ?_⟩
  · intro hmass
    exact ⟨hτne hmass, hπne (hτmass hmass), hθne (hπmass (hτmass hmass))⟩
  · calc (ML2Reduction.spineScaleLoss (Module.finrank ℝ E) s.card δ *
            ML2Reduction.spineScaleLoss (Module.finrank ℝ E) tτ'.card τ)⁻¹ *
            ShadedBody.fullness s (fun i => (V i).toShadedBody)
        = (ML2Reduction.spineScaleLoss (Module.finrank ℝ E) tτ'.card τ)⁻¹ *
            ((ML2Reduction.spineScaleLoss (Module.finrank ℝ E) s.card δ)⁻¹ *
              ShadedBody.fullness s (fun i => (V i).toShadedBody)) := by
          rw [mul_inv]; ring
      _ ≤ (ML2Reduction.spineScaleLoss (Module.finrank ℝ E) tτ'.card τ)⁻¹ *
            ShadedBody.fullness tτ' (fun j => (Yτ j).toShadedBody) := by gcongr
      _ ≤ ShadedBody.fullness tπ' (fun k => (Yπ k).toShadedBody) := hf2
  · calc (ML2Reduction.spineScaleLoss (Module.finrank ℝ E) s.card δ *
            ML2Reduction.spineScaleLoss (Module.finrank ℝ E) tτ'.card τ *
            ML2Reduction.spineScaleLoss (Module.finrank ℝ E) tπ'.card π)⁻¹ *
            ShadedBody.fullness s (fun i => (V i).toShadedBody)
        = (ML2Reduction.spineScaleLoss (Module.finrank ℝ E) tπ'.card π)⁻¹ *
            ((ML2Reduction.spineScaleLoss (Module.finrank ℝ E) tτ'.card τ)⁻¹ *
              ((ML2Reduction.spineScaleLoss (Module.finrank ℝ E) s.card δ)⁻¹ *
                ShadedBody.fullness s (fun i => (V i).toShadedBody))) := by
          rw [mul_inv, mul_inv]; ring
      _ ≤ (ML2Reduction.spineScaleLoss (Module.finrank ℝ E) tπ'.card π)⁻¹ *
            ((ML2Reduction.spineScaleLoss (Module.finrank ℝ E) tτ'.card τ)⁻¹ *
              ShadedBody.fullness tτ' (fun j => (Yτ j).toShadedBody)) := by gcongr
      _ ≤ (ML2Reduction.spineScaleLoss (Module.finrank ℝ E) tπ'.card π)⁻¹ *
            ShadedBody.fullness tπ' (fun k => (Yπ k).toShadedBody) := by gcongr
      _ ≤ ShadedBody.fullness tθ' (fun l => (Yθ l).toShadedBody) := hf3
  · intro jτ hjτ jπ hjπ jθ hjθ
    calc ShadedBody.multiplicity s (fun i => (V i).toShadedBody)
        ≤ ((ML2Reduction.spineScaleLoss (Module.finrank ℝ E) s.card δ : ℝ≥0) : ENNReal)
            * ShadedBody.multiplicity tτ' (fun j => (Yτ j).toShadedBody)
            * ShadedBody.multiplicity {i ∈ s | pτ i = jτ} (fun i => (Y' i).toShadedBody) :=
          hprod1 jτ hjτ
      _ ≤ ((ML2Reduction.spineScaleLoss (Module.finrank ℝ E) s.card δ : ℝ≥0) : ENNReal)
            * (((ML2Reduction.spineScaleLoss (Module.finrank ℝ E) tτ'.card τ : ℝ≥0) : ENNReal)
                * ShadedBody.multiplicity tπ' (fun k => (Yπ k).toShadedBody)
                * ShadedBody.multiplicity {j ∈ tτ' | pπ j = jπ} (fun j => (Yτ' j).toShadedBody))
            * ShadedBody.multiplicity {i ∈ s | pτ i = jτ} (fun i => (Y' i).toShadedBody) := by
          gcongr
          exact hprod2 jπ hjπ
      _ ≤ ((ML2Reduction.spineScaleLoss (Module.finrank ℝ E) s.card δ : ℝ≥0) : ENNReal)
            * (((ML2Reduction.spineScaleLoss (Module.finrank ℝ E) tτ'.card τ : ℝ≥0) : ENNReal)
                * (((ML2Reduction.spineScaleLoss (Module.finrank ℝ E) tπ'.card π : ℝ≥0) : ENNReal)
                    * ShadedBody.multiplicity tθ' (fun l => (Yθ l).toShadedBody)
                    * ShadedBody.multiplicity {k ∈ tπ' | pθ k = jθ}
                        (fun k => (Yπ' k).toShadedBody))
                * ShadedBody.multiplicity {j ∈ tτ' | pπ j = jπ} (fun j => (Yτ' j).toShadedBody))
            * ShadedBody.multiplicity {i ∈ s | pτ i = jτ} (fun i => (Y' i).toShadedBody) := by
          gcongr
          exact hprod3 jθ hjθ
      _ = ((ML2Reduction.spineScaleLoss (Module.finrank ℝ E) s.card δ *
              ML2Reduction.spineScaleLoss (Module.finrank ℝ E) tτ'.card τ *
              ML2Reduction.spineScaleLoss (Module.finrank ℝ E) tπ'.card π : ℝ≥0) : ENNReal)
            * ShadedBody.multiplicity {i ∈ s | pτ i = jτ} (fun i => (Y' i).toShadedBody)
            * ShadedBody.multiplicity {j ∈ tτ' | pπ j = jπ} (fun j => (Yτ' j).toShadedBody)
            * ShadedBody.multiplicity {k ∈ tπ' | pθ k = jθ} (fun k => (Yπ' k).toShadedBody)
            * ShadedBody.multiplicity tθ' (fun l => (Yθ l).toShadedBody) := by
          rw [ENNReal.coe_mul, ENNReal.coe_mul]; ring

end SplitFull

section SeamSplit

open Classical in
/-- **The seam split: `Kakeya.ML2Core.exists_spineThreeScale_full` at the retained-leaf chain, on
the translated tubes, with the OUTER level run on the seam's `t₀`.**

Two changes from `Kakeya.ML2Core.exists_spineThreeScale_ofChain_translated`, both
re-quantifications and neither an estimate:

* the outer index set is `t₀`, not `𝒞.indexSet a`.  `exists_spineThreeScale`'s `u` was always a
  parameter; the existing wrapper hard-codes the whole index set, and that is what made the outer
  ball row unsuppliable (B12's `hballcoarse`).  With `tθ' ⊆ t₀` the seam's own `hz3` **is** the
  row.  The side condition is `hmapsθ`, which is `Kakeya.ML2Core.coarseNode_parent_mem_of_retained`
  -- the seam's `hz2` again.
* the fullness clauses are kept (l.4675-4677).

`hprod` is on the **untranslated** leaf family, by
`Kakeya.ML2Core.multiplicity_eq_of_shade_translate`, which is the form
`Kakeya.ML2Core.HfacPostDropFour` reads. -/
theorem exists_seamSplit_translated {ι : Type u} {δ Cu : NNReal} {u : Finset ι}
    {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
    {t₀ t₁ : Finset ι} {a p b : ℕ} {v : EuclideanSpace ℝ (Fin 3)}
    (hδ0 : 0 < δ) (hap : a ≤ p) (hpb : p ≤ b) (hbN : b ≤ Tube.ssfGridLen δ)
    (hδτ : δ ≤ Tube.gridScale δ (Tube.ssfGridLen δ) b)
    (hτπ : Tube.gridScale δ (Tube.ssfGridLen δ) b
      ≤ Tube.gridScale δ (Tube.ssfGridLen δ) p)
    (hπθ : Tube.gridScale δ (Tube.ssfGridLen δ) p
      ≤ Tube.gridScale δ (Tube.ssfGridLen δ) a)
    (hθ1 : Tube.gridScale δ (Tube.ssfGridLen δ) a ≤ 1)
    (hball : ∀ i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι),
      ((T i).translate v).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (hballτ : ∀ j ∈ ML2Reduction.activeNodes (retainedLeafChain 𝒰 t₁ b) b,
      (((retainedLeafChain 𝒰 t₁ b).tube b j).translate v).carrier
        ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (hballπ : ∀ k ∈ ML2Reduction.activeNodes (retainedLeafChain 𝒰 t₁ b) p,
      (((retainedLeafChain 𝒰 t₁ b).tube p k).translate v).carrier
        ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (hmapsθ : ∀ k ∈ ML2Reduction.activeNodes (retainedLeafChain 𝒰 t₁ b) p,
      ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) a p k ∈ t₀) :
    ∃ tτ' ⊆ ML2Reduction.activeNodes (retainedLeafChain 𝒰 t₁ b) b,
      ∃ tp' ⊆ ML2Reduction.activeNodes (retainedLeafChain 𝒰 t₁ b) p, ∃ tθ' ⊆ t₀,
      ∃ (Yτ' : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) b)
          (EuclideanSpace ℝ (Fin 3)))
        (Ypo Yp : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) p)
          (EuclideanSpace ℝ (Fin 3)))
        (Yθ : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) a)
          (EuclideanSpace ℝ (Fin 3)))
        (Y' : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
        (∀ j, (Yτ' j).toTube = ((retainedLeafChain 𝒰 t₁ b).tube b j).translate v) ∧
        (∀ k, (Ypo k).toTube = ((retainedLeafChain 𝒰 t₁ b).tube p k).translate v) ∧
        (∀ k, (Yp k).toTube = ((retainedLeafChain 𝒰 t₁ b).tube p k).translate v) ∧
        (∀ l, (Yθ l).toTube = ((retainedLeafChain 𝒰 t₁ b).tube a l).translate v) ∧
        (∀ i, (Y' i).toTube = ((T i).translate v).toTube) ∧
        (0 < ∑ i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι),
            volume ((T i).translate v).shade →
          tτ'.Nonempty ∧ tp'.Nonempty ∧ tθ'.Nonempty) ∧
        (ML2Reduction.spineScaleLoss 3
              ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι).card δ *
            ML2Reduction.spineScaleLoss 3 tτ'.card
              (Tube.gridScale δ (Tube.ssfGridLen δ) b))⁻¹ *
            ShadedBody.fullness ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)
              (fun i => ((T i).translate v).toShadedBody)
          ≤ ShadedBody.fullness tp' (fun k => (Ypo k).toShadedBody) ∧
        (ML2Reduction.spineScaleLoss 3
              ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι).card δ *
            ML2Reduction.spineScaleLoss 3 tτ'.card
              (Tube.gridScale δ (Tube.ssfGridLen δ) b) *
            ML2Reduction.spineScaleLoss 3 tp'.card
              (Tube.gridScale δ (Tube.ssfGridLen δ) p))⁻¹ *
            ShadedBody.fullness ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)
              (fun i => ((T i).translate v).toShadedBody)
          ≤ ShadedBody.fullness tθ' (fun l => (Yθ l).toShadedBody) ∧
        ShadedBody.IsCRefinement
            ({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
              (retainedLeafChain 𝒰 t₁ b).assign b i ∈ tτ'} : Finset ι)
            (fun i => (Y' i).toShadedBody)
            ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)
            (fun i => ((T i).translate v).toShadedBody)
            (ML2Reduction.spineScaleLoss 3
              ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι).card δ)⁻¹ ∧
        ShadedBody.IsCRefinement
            ({k ∈ tp' | ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) a p k ∈ tθ'}
              : Finset ι)
            (fun k => (Yp k).toShadedBody) tp' (fun k => (Ypo k).toShadedBody)
            (ML2Reduction.spineScaleLoss 3 tp'.card
              (Tube.gridScale δ (Tube.ssfGridLen δ) p))⁻¹ ∧
        (∀ jτ ∈ tτ', ∀ jp ∈ tp', ∀ jθ ∈ tθ',
          ShadedBody.multiplicity ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)
              (fun i => (T i).toShadedBody)
            ≤ ((ML2Reduction.spineScaleLoss 3
                    ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι).card δ *
                  ML2Reduction.spineScaleLoss 3 tτ'.card
                    (Tube.gridScale δ (Tube.ssfGridLen δ) b) *
                  ML2Reduction.spineScaleLoss 3 tp'.card
                    (Tube.gridScale δ (Tube.ssfGridLen δ) p) : ℝ≥0) : ENNReal)
              * ShadedBody.multiplicity
                  ({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
                    (retainedLeafChain 𝒰 t₁ b).assign b i = jτ} : Finset ι)
                  (fun i => (Y' i).toShadedBody)
              * ShadedBody.multiplicity
                  ({j ∈ tτ' | ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) p b j = jp}
                    : Finset ι) (fun j => (Yτ' j).toShadedBody)
              * ShadedBody.multiplicity
                  ({k ∈ tp' | ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) a p k = jθ}
                    : Finset ι) (fun k => (Yp k).toShadedBody)
              * ShadedBody.multiplicity tθ' (fun l => (Yθ l).toShadedBody)) := by
  classical
  let 𝒞 := retainedLeafChain 𝒰 t₁ b
  let fam : Finset ι := ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)
  show ∃ tτ' ⊆ ML2Reduction.activeNodes 𝒞 b, _
  have hn3 : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have hpN : p ≤ Tube.ssfGridLen δ := le_trans hpb hbN
  have haN : a ≤ Tube.ssfGridLen δ := le_trans hap hpN
  have hbody : ∀ i, ((T i).translate v).toConvexSpaceBody
      = (((T i).toTube).translate v).toConvexSpaceBody := fun _ => rfl
  obtain ⟨tτ', htτ', tp', htp', tθ', htθ', Yτ', Ypo, Yp, Yθ, Y', hYτ', hYpo, hYp, hYθ,
      hY'tube, _hY'shade, _hYpshade, hne, hfullπ, hfullθ, hr1, hr3, hprod⟩ :=
    exists_spineThreeScale_full (E := EuclideanSpace ℝ (Fin 3)) hδ0 hδτ hτπ hπθ hθ1
      (fun i => (T i).translate v)
      (fun j => (𝒞.tube b j).translate v) (fun k => (𝒞.tube p k).translate v)
      (fun l => (𝒞.tube a l).translate v)
      (𝒞.assign b) (ML2Reduction.coarseNode 𝒞 p b) (ML2Reduction.coarseNode 𝒞 a p)
      hball hballτ hballπ
      (fun i hi => ML2Reduction.assign_mem_activeNodes 𝒞 hbN hi)
      (fun i hi => by
        rw [hbody i]
        exact tube_translate_le_translate _ _ v (𝒞.le_tube_assign b hbN i hi))
      (fun j hj => coarseNode_mem_activeNodes 𝒞 hpb hbN hj)
      (fun j hj => tube_translate_le_translate _ _ v
        (ML2Reduction.tube_le_coarseNode 𝒞 hpb hbN hj))
      hmapsθ
      (fun k hk => tube_translate_le_translate _ _ v
        (ML2Reduction.tube_le_coarseNode 𝒞 hap hpN hk))
  rw [hn3] at hfullπ hfullθ hr1 hr3 hprod
  refine ⟨tτ', htτ', tp', htp', tθ', htθ', Yτ', Ypo, Yp, Yθ, Y', hYτ', hYpo, hYp, hYθ, hY'tube,
    hne, hfullπ, hfullθ, hr1, hr3, ?_⟩
  intro jτ hjτ jp hjp jθ hjθ
  have hbridge : ShadedBody.multiplicity fam (fun i => ((T i).translate v).toShadedBody)
      = ShadedBody.multiplicity fam (fun i => (T i).toShadedBody) :=
    multiplicity_eq_of_shade_translate fam (fun i => (T i).toShadedBody)
      (fun i => ((T i).translate v).toShadedBody) v (fun _ => rfl)
  rw [← hbridge]
  exact hprod jτ hjτ jp hjp jθ hjθ

end SeamSplit

section FibreMediant

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

open Classical in
/-- **The mediant at any level: a refinement's fullness is attained on one fibre.**

`Kakeya.ML2Core.exists_fine_fibre_fullness` is this at the leaf level, phrased through a translate;
this is the same two steps -- `ShadedBody.IsCRefinement.coe_mul_fullness_le` then
`Kakeya.ML2Core.exists_fibre_fullness_le'` -- with the ambient family taken as it is, which is what
the `(a,p)` level needs (there the ambient shading is the split's own `Ypo`, not a translate). -/
theorem exists_fibre_fullness_of_refinement {ρ : NNReal} (hρ0 : 0 < ρ) {ι : Type*}
    {s₁ t : Finset ι} {Yamb Y : ι → ShadedTube ρ E} {pmap : ι → ι} {c : NNReal}
    (href : ShadedBody.IsCRefinement ({k ∈ s₁ | pmap k ∈ t} : Finset ι)
        (fun k => (Y k).toShadedBody) s₁ (fun k => (Yamb k).toShadedBody) c)
    (htne : t.Nonempty)
    (hpos : 0 < c * ShadedBody.fullness s₁ (fun k => (Yamb k).toShadedBody)) :
    ∃ jθ ∈ t, c * ShadedBody.fullness s₁ (fun k => (Yamb k).toShadedBody)
      ≤ ShadedBody.fullness ({k ∈ s₁ | pmap k = jθ} : Finset ι)
          (fun k => (Y k).toShadedBody) := by
  classical
  set s₁' : Finset ι := {k ∈ s₁ | pmap k ∈ t} with hs₁'
  have h1 : c * ShadedBody.fullness s₁ (fun k => (Yamb k).toShadedBody)
      ≤ ShadedBody.fullness s₁' (fun k => (Y k).toShadedBody) := by
    have h := href.coe_mul_fullness_le
    exact_mod_cast h
  have hposS : 0 < ShadedBody.fullness s₁' (fun k => (Y k).toShadedBody) :=
    lt_of_lt_of_le hpos h1
  have hne : s₁'.Nonempty := by
    rcases Finset.eq_empty_or_nonempty s₁' with h | h
    · rw [h] at hposS; simp [ShadedBody.fullness, ShadedBody.fullness'] at hposS
    · exact h
  obtain ⟨hB0, hBtop⟩ := Kakeya.StickyKakeya.sum_volume_carrier_pos_ne_top hρ0 s₁' Y hne
  obtain ⟨jθ, hjθ, hfib⟩ :=
    ML2Core.exists_fibre_fullness_le' (E := E) s₁' (fun k => (Y k).toShadedBody) t pmap
      (fun k hk => (Finset.mem_filter.mp hk).2) htne hB0.ne' hBtop
  refine ⟨jθ, hjθ, h1.trans ?_⟩
  have heq : ({k ∈ s₁' | pmap k = jθ} : Finset ι) = ({k ∈ s₁ | pmap k = jθ} : Finset ι) := by
    ext k
    simp only [hs₁', Finset.mem_filter]
    constructor
    · rintro ⟨⟨hk, _⟩, h⟩; exact ⟨hk, h⟩
    · rintro ⟨hk, h⟩; exact ⟨⟨hk, h ▸ hjθ⟩, h⟩
  rw [← heq]
  exact hfib

end FibreMediant

section CoarseWindow

open Classical in
/-- **Conjunct 5 (`hcoarse`) from the block's OWN window**.

`Kakeya.ML2Core.exists_coarse_factor_at_window` needs no change and the block needs no new field:
`Kakeya.ML2Reduction.IsKatzTaoDividingWindowLevels` extends
`Kakeya.ML2Reduction.IsKatzTaoDividingWindow`, so `hwin.toIsKatzTaoDividingWindow` is the coarse
density.  With the outer level run on the seam's `t₀` (`Kakeya.ML2Core.exists_seamSplit_translated`)
the ball row is `hz3`, and the fullness is the split's own.  So all three of B12's coarse residuals
close, and the outer loss is the window's own `ε + (κc + η_m)` -- the shape
`Kakeya.ML2Core.FourFactorRowsAt` already prints as `εc + spineRung m`.

**Family:** `tθ' ⊆ t₀`; **shading:** the split's `Yθ`, translated.  **Level:** `a`. -/
theorem exists_coarseRow_of_window {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hKT : Kakeya.KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β) {ε : ℝ} (hε : 0 < ε) :
    ∃ η > (0 : ℝ), ∃ θ₀ : NNReal, 0 < θ₀ ∧ θ₀ ≤ 1 ∧
      ∀ {δ Cu : NNReal} {ι : Type u} {u : Finset ι}
        {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
        {𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu}
        {Cstar : ENNReal} {ηl : ℕ → ℝ} {εd : ℝ} {N a b m : ℕ} {κc : ℝ}
        {t₀ tθ' : Finset ι}
        {Yθ : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) a)
          (EuclideanSpace ℝ (Fin 3))}
        {v : EuclideanSpace ℝ (Fin 3)},
        0 < δ → δ ≤ 1 →
        Tube.gridScale δ (Tube.ssfGridLen δ) a ≤ θ₀ →
        ML2Reduction.IsKatzTaoDividingWindowLevels 𝒰 Cstar ηl εd N a b m →
        0 ≤ ηl m → 0 ≤ κc → Cstar ≤ (δ : ENNReal) ^ (-κc) →
        t₀ ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain a →
        tθ' ⊆ t₀ →
        (∀ l, (Yθ l).toTube = (𝒰.cover.tube a l).translate v) →
        (∀ l ∈ t₀, ((𝒰.cover.tube a l).translate v).carrier
          ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
        (δ : NNReal) ^ η ≤ ShadedBody.fullness tθ' (fun l => (Yθ l).toShadedBody) →
        ShadedBody.multiplicity tθ' (fun l => (Yθ l).toShadedBody)
          ≤ (δ : ENNReal) ^ (-(ε + (κc + ηl m))) * ((tθ'.card : ℕ) : ENNReal) ^ β := by
  classical
  obtain ⟨η, hη, θ₀, hθ₀0, hθ₀1, hcore⟩ := ML2Core.exists_coarse_factor_at_window.{u}
    (E := EuclideanSpace ℝ (Fin 3)) hβ0 hβ1 hKT hε
  refine ⟨η, hη, θ₀, hθ₀0, hθ₀1, ?_⟩
  intro δ Cu ι u T 𝒰 Cstar ηl εd N a b m κc t₀ tθ' Yθ v hδ0 hδ1 hθ hwin hηm hκc hCstar ht₀ htθ'
    hYθ hball hfull
  have hsubidx : tθ' ⊆ 𝒰.cover.indexSet a :=
    fun l hl => ML2Reduction.activeNodes_subset _ _ (ht₀ (htθ' hl))
  have hballθ : ∀ l ∈ tθ', (Yθ l).carrier
      ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
    intro l hl
    have hc : (Yθ l).carrier = ((𝒰.cover.tube a l).translate v).carrier :=
      congrArg (fun A : Tube (Tube.gridScale δ (Tube.ssfGridLen δ) a)
        (EuclideanSpace ℝ (Fin 3)) => A.carrier) (hYθ l)
    rw [hc]
    exact hball l (htθ' hl)
  exact hcore hδ0 hδ1 hθ hwin.toIsKatzTaoDividingWindow hηm hκc hCstar hsubidx hYθ hballθ hfull

end CoarseWindow

section CardCeilings

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
open Classical in
/-- **Active nodes are at most as many as the leaves.**  Every active node is the level-`k`
assignment of some member, so `Kakeya.ML2Reduction.activeNodes 𝒞 k ⊆ s.image (𝒞.assign k)`.  This
is what puts the split's two node cardinalities under the block's own `δ^{-4}` ceiling. -/
theorem card_activeNodes_le {ι : Type*} {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ}
    {σ : ℕ → NNReal} (𝒞 : Tube.ChainCoverSystem s T N σ) (k : ℕ) :
    (ML2Reduction.activeNodes 𝒞 k).card ≤ s.card := by
  classical
  refine le_trans (Finset.card_le_card ?_) (Finset.card_image_le (s := s) (f := 𝒞.assign k))
  intro j hj
  simp only [ML2Reduction.activeNodes, Finset.mem_filter] at hj
  obtain ⟨i, hi⟩ := hj.2
  simp only [Tube.coverClass, Finset.mem_filter] at hi
  exact Finset.mem_image.mpr ⟨i, hi.1, hi.2⟩

end CardCeilings

section Producer

open Classical in
/-- **`Kakeya.ML2Core.HfacPostDropFour`'s conclusion, PRODUCED at one instance of the block.**

B12 took the four factor rows as a hypothesis (`Kakeya.ML2Core.FourFactorRowsSupply`); this
produces them.  The route:

`Kakeya.ML2Core.exists_seamSplit_translated` runs the three-scale split on
`Kakeya.ML2Core.retainedLeafChain` with the **outer level on the seam's `tA`** and keeps the
fullness clauses; the witnesses `jτ` and `jθ` are then chosen **by mass**
(`Kakeya.ML2Core.exists_fine_fibre_fullness`,
`Kakeya.ML2Core.exists_fibre_fullness_of_refinement`).  That is what makes the fibre fullness rows
theorems rather than assumptions, and it is the source's own device -- *"the pigeonholing retained
complete tagged fibres and used their shaded masses as weights"* (l.4482-4483), *"the four
lower-fullness estimates refer to the same mass-coupled refinements"* (l.4675-4677), one joint
selection producing one family (l.5860-5871).

`hlead` is the single ledger row those four estimates collapse to: the leaf family's fullness
survives the split's three `spineScaleLoss` factors.  `houter`, `hfineCore`, `hparCore`, `hmid`
are the four factor estimates, in the shape their existing producers deliver.

**The loss budget, before and after the four-way allocation**.  The
source constrains the losses only in TOTAL: l.4455-4457 charges *"the losses from roundness,
normalization, and the four fullness refinements"* against a positive fraction of `η'β`, and
l.4678-4681 collapses the four defect contributions to `8^ω δ^{-ω}`, a single defect.  Before, the
three-way `hexp` spent `εf + (εc + X) + κ'`; after, `εf + εp + (εc + X) + κ'`.  No line here is a
source display -- the sum is, and it is `hexp` that must carry it. -/
theorem hfacConclusion_of_rows {ι : Type u} {δ Cu : NNReal} {u : Finset ι}
    {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
    {t₁ tA : Finset ι} {a p b : ℕ} {v : EuclideanSpace ℝ (Fin 3)}
    {β εf εp εcm gmv ηL ηin : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (_hβ0 : 0 ≤ β)
    (hap : a ≤ p) (hpb : p ≤ b) (hbN : b ≤ Tube.ssfGridLen δ)
    (hδb : δ ≤ Tube.gridScale δ (Tube.ssfGridLen δ) b)
    (_hba : Tube.gridScale δ (Tube.ssfGridLen δ) b
      ≤ Tube.gridScale δ (Tube.ssfGridLen δ) a)
    (ha1 : Tube.gridScale δ (Tube.ssfGridLen δ) a ≤ 1)
    (_ht₁ : t₁ ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain b)
    (hballt₁ : ∀ j ∈ t₁, ((𝒰.cover.tube b j).translate v).carrier
      ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (hballleaf : ∀ i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι),
      ((T i).translate v).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (hmass : 0 < ∑ i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι), volume (T i).shade)
    (hmaxu : Kakeya.maxDensity u (fun i => (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-ηin))
    (hηin : ηin ≤ ηL)
    -- the outer package: the `a = 0` / `a ≠ 0` fork, factored into three rows
    (htAidx : tA ⊆ 𝒰.cover.indexSet a)
    (hballπ : ∀ k ∈ ML2Reduction.activeNodes (retainedLeafChain 𝒰 t₁ b) p,
      (((retainedLeafChain 𝒰 t₁ b).tube p k).translate v).carrier
        ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (hmapsθ : ∀ k ∈ ML2Reduction.activeNodes (retainedLeafChain 𝒰 t₁ b) p,
      ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) a p k ∈ tA)
    (houter : ∀ (tθ' : Finset ι), tθ' ⊆ tA →
      ∀ (Yθ : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) a)
          (EuclideanSpace ℝ (Fin 3))),
      (∀ l, (Yθ l).toTube = ((retainedLeafChain 𝒰 t₁ b).tube a l).translate v) →
      (δ : NNReal) ^ ηL ≤ ShadedBody.fullness tθ' (fun l => (Yθ l).toShadedBody) →
      ShadedBody.multiplicity tθ' (fun l => (Yθ l).toShadedBody)
        ≤ (δ : ENNReal) ^ (-εcm) * ((tθ'.card : ℕ) : ENNReal) ^ β)
    -- the inner (leaf) factor, in `Kakeya.ML2Core.exists_fine_factor`'s own shape
    (hfineCore : ∀ (f : Finset ι) (Y : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
      (∀ i ∈ f, (Y i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
      Kakeya.maxDensity f (fun i => (Y i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-ηL) →
      (δ : NNReal) ^ ηL ≤ ShadedBody.fullness f (fun i => (Y i).toShadedBody) →
      ShadedBody.multiplicity f (fun i => (Y i).toShadedBody)
        ≤ (δ : ENNReal) ^ (-εf) * (f.card : ENNReal) ^ β)
    -- the new-parent factor at `(a,p)`, in `Kakeya.ML2Core.exists_newParent_factor_at`'s shape
    (hparCore : ∀ (tp' : Finset ι), tp' ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain p →
      ∀ (Yp : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) p)
          (EuclideanSpace ℝ (Fin 3))),
      (∀ k, (Yp k).toTube = (𝒰.cover.tube p k).translate v) → ∀ jθ : ι,
      (∀ k ∈ ({k ∈ tp' | ML2Reduction.coarseNode 𝒰.cover.toChain a p k = jθ} : Finset ι),
        (Yp k).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
      (δ : NNReal) ^ ηL ≤ ShadedBody.fullness
        ({k ∈ tp' | ML2Reduction.coarseNode 𝒰.cover.toChain a p k = jθ} : Finset ι)
        (fun k => (Yp k).toShadedBody) →
      ShadedBody.multiplicity
          ({k ∈ tp' | ML2Reduction.coarseNode 𝒰.cover.toChain a p k = jθ} : Finset ι)
          (fun k => (Yp k).toShadedBody)
        ≤ (δ : ENNReal) ^ (-εp)
          * ((({k ∈ tp' | ML2Reduction.coarseNode 𝒰.cover.toChain a p k = jθ} :
              Finset ι).card : ENNReal)) ^ β)
    -- the VNS middle factor at `(p,b)`, from `Kakeya.ML2Core.midRow_of_handBack`
    (hmid : ∀ (tτ' : Finset ι), tτ' ⊆ ML2Reduction.activeNodes (retainedLeafChain 𝒰 t₁ b) b →
      ∀ (Yτ' : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) b)
          (EuclideanSpace ℝ (Fin 3))),
      (∀ j, (Yτ' j).toTube = ((retainedLeafChain 𝒰 t₁ b).tube b j).translate v) → ∀ jp : ι,
      ShadedBody.multiplicity
          ({j ∈ tτ' | ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) p b j = jp} : Finset ι)
          (fun j => (Yτ' j).toShadedBody)
        ≤ (δ : ENNReal) ^ gmv
          * ((({j ∈ tτ' | ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) p b j = jp} :
              Finset ι).card : ENNReal)) ^ β)
    -- the ONE ledger row the four lower-fullness estimates collapse to (l.4675-4677)
    (hcardu : ((u.card : ℕ) : NNReal) ≤ δ ^ (-(4 : ℝ)))
    -- CORRECTED in B20: the three cardinalities are bounded, and must be.  `spineScaleLoss` grows
    -- with the family size (`factoringStep3Constant N`, `Nat.log 2 N`), so the unrestricted
    -- `∀ n₁ n₂ n₃` of B15 is not satisfiable; the existing ledger lemma
    -- `Kakeya.ML2Core.spineScaleLoss_prod_le` carries exactly these ceilings on its own two
    -- factors.  Weakening a hypothesis strengthens the theorem, so this is the safe direction.
    (hlead : ∀ n₁ n₂ n₃ : ℕ, ((n₁ : ℕ) : NNReal) ≤ δ ^ (-(4 : ℝ)) →
      ((n₂ : ℕ) : NNReal) ≤ δ ^ (-(4 : ℝ)) → ((n₃ : ℕ) : NNReal) ≤ δ ^ (-(4 : ℝ)) →
      (δ : NNReal) ^ ηL
      ≤ (ML2Reduction.spineScaleLoss 3 n₁ δ *
          ML2Reduction.spineScaleLoss 3 n₂ (Tube.gridScale δ (Tube.ssfGridLen δ) b) *
          ML2Reduction.spineScaleLoss 3 n₃ (Tube.gridScale δ (Tube.ssfGridLen δ) p))⁻¹ *
        ShadedBody.fullness ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)
          (fun i => ((T i).translate v).toShadedBody)) :
    ∃ (tτ' tp' tθ' : Finset ι)
      (Yτ' : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) b)
        (EuclideanSpace ℝ (Fin 3)))
      (Yp : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) p)
        (EuclideanSpace ℝ (Fin 3)))
      (Yθ : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) a)
        (EuclideanSpace ℝ (Fin 3)))
      (Y' : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (jτ jp jθ : ι),
      tτ' ⊆ t₁ ∧ tp' ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain p ∧
        tθ' ⊆ 𝒰.cover.indexSet a ∧ jτ ∈ t₁ ∧ jθ ∈ tθ' ∧ tτ'.Nonempty ∧ tp'.Nonempty ∧
      ShadedBody.multiplicity ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)
          (fun i => (T i).toShadedBody)
          ≤ ((ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))
                ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι).card δ *
              ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))
                tτ'.card (Tube.gridScale δ (Tube.ssfGridLen δ) b) *
              ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))
                tp'.card (Tube.gridScale δ (Tube.ssfGridLen δ) p) : NNReal) : ENNReal)
            * ShadedBody.multiplicity ({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
                𝒰.cover.assign b i = jτ} : Finset ι) (fun i => (Y' i).toShadedBody)
            * ShadedBody.multiplicity ({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain p b j
                = jp} : Finset ι) (fun j => (Yτ' j).toShadedBody)
            * ShadedBody.multiplicity ({k ∈ tp' | ML2Reduction.coarseNode 𝒰.cover.toChain a p k
                = jθ} : Finset ι) (fun k => (Yp k).toShadedBody)
            * ShadedBody.multiplicity tθ' (fun k => (Yθ k).toShadedBody) ∧
      ShadedBody.multiplicity ({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
          𝒰.cover.assign b i = jτ} : Finset ι) (fun i => (Y' i).toShadedBody)
          ≤ (δ : ENNReal) ^ (-(εf)) * ((({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
              𝒰.cover.assign b i = jτ} : Finset ι)).card : ENNReal) ^ β ∧
      ShadedBody.multiplicity ({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain p b j = jp} :
          Finset ι) (fun j => (Yτ' j).toShadedBody)
          ≤ (δ : ENNReal) ^ gmv
            * ((({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain p b j = jp} : Finset
                ι)).card : ENNReal) ^ β ∧
      ShadedBody.multiplicity ({k ∈ tp' | ML2Reduction.coarseNode 𝒰.cover.toChain a p k = jθ} :
          Finset ι) (fun k => (Yp k).toShadedBody)
          ≤ (δ : ENNReal) ^ (-(εp))
            * ((({k ∈ tp' | ML2Reduction.coarseNode 𝒰.cover.toChain a p k = jθ} : Finset
                ι)).card : ENNReal) ^ β ∧
      ShadedBody.multiplicity tθ' (fun k => (Yθ k).toShadedBody)
          ≤ (δ : ENNReal) ^ (-εcm) * ((tθ'.card : ℕ) : ENNReal) ^ β := by
  classical
  have hpN : p ≤ Tube.ssfGridLen δ := le_trans hpb hbN
  have hτπ : Tube.gridScale δ (Tube.ssfGridLen δ) b
      ≤ Tube.gridScale δ (Tube.ssfGridLen δ) p := Tube.gridScale_antitone hδ0 hδ1 _ hpb
  have hπθ : Tube.gridScale δ (Tube.ssfGridLen δ) p
      ≤ Tube.gridScale δ (Tube.ssfGridLen δ) a := Tube.gridScale_antitone hδ0 hδ1 _ hap
  have hρp0 : 0 < Tube.gridScale δ (Tube.ssfGridLen δ) p := Tube.gridScale_pos hδ0 _ _
  have hactb : ML2Reduction.activeNodes (retainedLeafChain 𝒰 t₁ b) b ⊆ t₁ :=
    activeNodes_chainRestrictFamily_subset_of_filter _ _
  have hballτ : ∀ j ∈ ML2Reduction.activeNodes (retainedLeafChain 𝒰 t₁ b) b,
      (((retainedLeafChain 𝒰 t₁ b).tube b j).translate v).carrier
        ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    fun j hj => hballt₁ j (hactb hj)
  obtain ⟨tτ', htτ', tp', htp', tθ', htθ', Yτ', Ypo, Yp, Yθ, Y', hYτ', hYpo, hYp, hYθ, hY'tube,
      hne, hfullπ, hfullθ, hr1, hr3, hprod⟩ :=
    exists_seamSplit_translated 𝒰 hδ0 hap hpb hbN hδb hτπ hπθ ha1 hballleaf hballτ hballπ hmapsθ
  have hvol : ∀ i : ι, volume (((T i).translate v).shade) = volume ((T i).shade) := by
    intro i
    show volume ((v + ·) '' (T i).shade) = _
    simpa using measure_vadd (μ := (volume : Measure (EuclideanSpace ℝ (Fin 3)))) v (T i).shade
  have hmass' : 0 < ∑ i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι),
      volume (((T i).translate v).shade) := by simpa [hvol] using hmass
  obtain ⟨hτne, hpne, hθne⟩ := hne hmass'
  have hcardfam : ((({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι).card : ℕ) : NNReal)
      ≤ δ ^ (-(4 : ℝ)) :=
    le_trans (by exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)) hcardu
  have hcardτ : ((tτ'.card : ℕ) : NNReal) ≤ δ ^ (-(4 : ℝ)) :=
    le_trans (by
      exact_mod_cast le_trans (Finset.card_le_card htτ')
        (card_activeNodes_le (retainedLeafChain 𝒰 t₁ b) b)) hcardfam
  have hcardp : ((tp'.card : ℕ) : NNReal) ≤ δ ^ (-(4 : ℝ)) :=
    le_trans (by
      exact_mod_cast le_trans (Finset.card_le_card htp')
        (card_activeNodes_le (retainedLeafChain 𝒰 t₁ b) p)) hcardfam
  have hleadx := hlead ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι).card tτ'.card tp'.card
    hcardfam hcardτ hcardp
  have hδpow0 : (0 : NNReal) < (δ : NNReal) ^ ηL := NNReal.rpow_pos hδ0
  have hL1 : (1 : NNReal) ≤ ML2Reduction.spineScaleLoss 3
      ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι).card δ :=
    ML2Reduction.one_le_spineScaleLoss _ _ _
  have hL2 : (1 : NNReal) ≤ ML2Reduction.spineScaleLoss 3 tτ'.card
      (Tube.gridScale δ (Tube.ssfGridLen δ) b) := ML2Reduction.one_le_spineScaleLoss _ _ _
  have hL3 : (1 : NNReal) ≤ ML2Reduction.spineScaleLoss 3 tp'.card
      (Tube.gridScale δ (Tube.ssfGridLen δ) p) := ML2Reduction.one_le_spineScaleLoss _ _ _
  have hfullEq : ShadedBody.fullness ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)
        (fun i => ((T i).translate v).toShadedBody)
      = ShadedBody.fullness ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)
        (fun i => (T i).toShadedBody) :=
    ShadedBody.fullness_translate_const _ (fun i => (T i).toShadedBody) v
  -- (1) the leaf fibre's witness, chosen by mass
  have hleadf : (δ : NNReal) ^ ηL ≤ (ML2Reduction.spineScaleLoss 3
        ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι).card δ)⁻¹ *
      ShadedBody.fullness ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)
        (fun i => (T i).toShadedBody) := by
    refine hleadx.trans ?_
    rw [hfullEq]
    refine mul_le_mul_right' ?_ _
    have h12 : ML2Reduction.spineScaleLoss 3
        ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι).card δ
        ≤ ML2Reduction.spineScaleLoss 3
            ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι).card δ *
          ML2Reduction.spineScaleLoss 3 tτ'.card
            (Tube.gridScale δ (Tube.ssfGridLen δ) b) :=
      le_mul_of_one_le_right (by positivity) hL2
    have h123 : ML2Reduction.spineScaleLoss 3
        ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι).card δ
        ≤ ML2Reduction.spineScaleLoss 3
            ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι).card δ *
          ML2Reduction.spineScaleLoss 3 tτ'.card
            (Tube.gridScale δ (Tube.ssfGridLen δ) b) *
          ML2Reduction.spineScaleLoss 3 tp'.card
            (Tube.gridScale δ (Tube.ssfGridLen δ) p) :=
      h12.trans (le_mul_of_one_le_right (by positivity) hL3)
    exact inv_anti₀ (lt_of_lt_of_le zero_lt_one hL1) h123
  have hposf : 0 < (ML2Reduction.spineScaleLoss 3
        ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι).card δ)⁻¹ *
      ShadedBody.fullness ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)
        (fun i => (T i).toShadedBody) := lt_of_lt_of_le hδpow0 hleadf
  obtain ⟨jτ, hjτ, hfullfine⟩ := ML2Core.exists_fine_fibre_fullness hδ0 hr1 hτne hposf
  -- (2) the `(a,p)` fibre's witness, chosen by mass
  have hchain : (δ : NNReal) ^ ηL
      ≤ (ML2Reduction.spineScaleLoss 3 tp'.card
          (Tube.gridScale δ (Tube.ssfGridLen δ) p))⁻¹ *
        ShadedBody.fullness tp' (fun k => (Ypo k).toShadedBody) := by
    refine hleadx.trans ?_
    have h1 : (ML2Reduction.spineScaleLoss 3
            ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι).card δ *
          ML2Reduction.spineScaleLoss 3 tτ'.card
            (Tube.gridScale δ (Tube.ssfGridLen δ) b) *
          ML2Reduction.spineScaleLoss 3 tp'.card
            (Tube.gridScale δ (Tube.ssfGridLen δ) p))⁻¹ *
        ShadedBody.fullness ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)
          (fun i => ((T i).translate v).toShadedBody)
        = (ML2Reduction.spineScaleLoss 3 tp'.card
            (Tube.gridScale δ (Tube.ssfGridLen δ) p))⁻¹ *
          ((ML2Reduction.spineScaleLoss 3
              ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι).card δ *
            ML2Reduction.spineScaleLoss 3 tτ'.card
              (Tube.gridScale δ (Tube.ssfGridLen δ) b))⁻¹ *
            ShadedBody.fullness ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)
              (fun i => ((T i).translate v).toShadedBody)) := by
      rw [mul_inv]; ring
    rw [h1]
    exact mul_le_mul_left' hfullπ _
  have hposp : 0 < (ML2Reduction.spineScaleLoss 3 tp'.card
      (Tube.gridScale δ (Tube.ssfGridLen δ) p))⁻¹ *
      ShadedBody.fullness tp' (fun k => (Ypo k).toShadedBody) := lt_of_lt_of_le hδpow0 hchain
  obtain ⟨jθ, hjθ, hfullpar⟩ :=
    exists_fibre_fullness_of_refinement (E := EuclideanSpace ℝ (Fin 3)) hρp0 hr3 hθne hposp
  obtain ⟨jp, hjp⟩ := hpne
  have hE1 : ({j ∈ tτ' | ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) p b j = jp}
        : Finset ι)
      = ({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain p b j = jp} : Finset ι) := by
    refine Finset.filter_congr ?_
    intro j hj
    rw [coarseNode_retainedLeafChain 𝒰 t₁ hpb hbN (htτ' hj)]
  have hE2 : ({k ∈ tp' | ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) a p k = jθ}
        : Finset ι)
      = ({k ∈ tp' | ML2Reduction.coarseNode 𝒰.cover.toChain a p k = jθ} : Finset ι) := by
    refine Finset.filter_congr ?_
    intro k hk
    rw [coarseNode_retainedLeafChain 𝒰 t₁ hap hpN (htp' hk)]
  -- the four factor rows
  have hY'tube' : ∀ i, (Y' i).toTube = ((T i).toTube).translate v := fun i =>
    (hY'tube i).trans (shadedTube_translate_toTube (T i) v)
  have hfinex := hfineCore
    ({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
      𝒰.cover.assign b i = jτ} : Finset ι) Y'
    (by
      intro i hi
      have hc : (Y' i).carrier = ((T i).translate v).carrier :=
        congrArg (fun A : Tube δ (EuclideanSpace ℝ (Fin 3)) => A.carrier) (hY'tube i)
      rw [hc]
      exact hballleaf i (Finset.mem_filter.mp hi).1)
    (by
      refine le_trans (le_trans (ML2Core.maxDensity_le_of_translate_subset
        (t := ({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
          𝒰.cover.assign b i = jτ} : Finset ι)) (u := u)
        (fun i hi => (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).1) hY'tube') hmaxu) ?_
      exact ENNReal.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hδ1) (by linarith))
    (le_trans hleadf hfullfine)
  have hmidx := hmid tτ' htτ' Yτ' hYτ' jp
  rw [hE1] at hmidx
  have hparx := hparCore tp'
    (fun k hk => activeNodes_chainRestrictFamily_subset _ _ _ (htp' hk)) Yp hYp jθ
    (by
      intro k hk
      rw [← hE2] at hk
      have hkp : k ∈ tp' := (Finset.mem_filter.mp hk).1
      have hc : (Yp k).carrier
          = (((retainedLeafChain 𝒰 t₁ b).tube p k).translate v).carrier :=
        congrArg (fun A : Tube (Tube.gridScale δ (Tube.ssfGridLen δ) p)
          (EuclideanSpace ℝ (Fin 3)) => A.carrier) (hYp k)
      rw [hc]
      exact hballπ k (htp' hkp))
    (by rw [← hE2]; exact le_trans hchain hfullpar)
  have hcoarsex := houter tθ' htθ' Yθ hYθ (le_trans hleadx hfullθ)
  have hprodx := hprod jτ hjτ jp hjp jθ hjθ
  rw [hE1, hE2] at hprodx
  refine ⟨tτ', tp', tθ', Yτ', Yp, Yθ, Y', jτ, jp, jθ,
    fun j hj => hactb (htτ' hj),
    fun k hk => activeNodes_chainRestrictFamily_subset _ _ _ (htp' hk),
    fun l hl => htAidx (htθ' hl), hactb (htτ' hjτ), hjθ, ⟨jτ, hjτ⟩, ⟨jp, hjp⟩, ?_,
    hfinex, hmidx, hparx, hcoarsex⟩
  rw [show Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 from by simp]
  exact hprodx

end Producer

section AnalyticSupply

open Classical in
/-- **The site's residual bundle, under the block's own antecedents.**

`Kakeya.ML2Core.FourFactorRowsSupply`'s antecedent block, with the conclusion replaced by the five
rows `Kakeya.ML2Core.hfacConclusion_of_rows` consumes: the outer package (`tA`, the level-`p` ball
row, the `(a,p)` parent map and the outer factor), the inner factor, the new-parent factor, the VNS
middle factor, and the one ledger row `hlead`.

Against B12 this drops `FourFactorRowsAt` entirely.  That Prop quantifies its four multiplicity
rows over **every** shading with the right tube, and a shading is free to put a common shade on
every member of a fibre, which makes the multiplicity the fibre's cardinality; the rows are
therefore not suppliable in that shape for the same reason conjunct 1 was not
(`Kakeya.ML2Core.not_supplyRow_fourFactorRows`).  Here the shadings are the split's own and the
witnesses are chosen by mass, which is the source's device (l.4482-4483, l.4675-4677). -/
def SiteAnalyticRows.{u'} (β ϖ ε₁ ηin η' εf εp εc κc ηL : ℝ) (gm gain dens : ℝ → ℝ)
    (Cu₀ : NNReal) : Prop :=
  ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u'} (u : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (Cu lam :
          NNReal)
        (𝒰 : Tube.UniformTubeSet u (fun i ↦ (T i).toTube) (Tube.ssfGridLen δ) Cu)
        (Cstar : ENNReal) (a b m : ℕ),
        ML2Reduction.IsKatzTaoDividingWindowLevels 𝒰 Cstar (ML2Spine.spineRung β ϖ ε₁ gain dens)
          (ML2Spine.spineDiv ϖ ε₁) (ML2Spine.spineCount ϖ ε₁) a b m →
      ∀ (v : (EuclideanSpace ℝ (Fin 3))) (t₀ t₁ : Finset ι),
        t₁ ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain b →
        (∀ j ∈ t₁, ((𝒰.cover.tube b j).translate v).carrier ⊆ Metric.closedBall (0 :
            (EuclideanSpace ℝ (Fin 3))) 1) →
        (∀ i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι), ((T i).translate v).carrier ⊆
            Metric.closedBall (0 : (EuclideanSpace ℝ (Fin 3))) 1) →
        (a ≠ 0 → t₀ ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain a) →
        (a ≠ 0 → ∀ j ∈ t₁, ML2Reduction.coarseNode 𝒰.cover.toChain a b j ∈ t₀) →
        (a ≠ 0 → ∀ k ∈ t₀,
          ((𝒰.cover.tube a k).translate v).carrier ⊆ Metric.closedBall (0 : (EuclideanSpace ℝ (Fin
              3))) 1) →
        (∀ i ∈ u, (T i).carrier ⊆ Metric.closedBall (0 : (EuclideanSpace ℝ (Fin 3))) 1) →
        u.Nonempty →
        Kakeya.maxDensity u (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-ηin) →
        ML2Shaded.HasDenseShading lam u (fun i ↦ (T i).toShadedBody) →
        ML2Shaded.HasComparableDensities lam⁻¹ u (fun i ↦ (T i).toShadedBody) →
        (δ : NNReal) ^ ηin / 2 ≤ lam →
        (u.card : NNReal) ≤ δ ^ (-(4 : ℝ)) →
        Cstar ≤ (δ : ENNReal) ^ (-κc) →
        Cu ≤ Cu₀ →
        0 < ∑ i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι), volume (T i).shade →
        δ ≤ Tube.gridScale δ (Tube.ssfGridLen δ) b →
        Tube.gridScale δ (Tube.ssfGridLen δ) b ≤ Tube.gridScale δ (Tube.ssfGridLen δ) a →
        Tube.gridScale δ (Tube.ssfGridLen δ) a ≤ 1 →
        -- the refined (F): the genuine parent level, its density, and the count floor
        ∀ p : ℕ, a ≤ p → p ≤ b →
          (∀ m' : ℕ, a < m' → m' < b →
            ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ (1 - ML2Spine.spineDiv ϖ ε₁)
              ≤ (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ) →
            (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ)
              ≤ ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ ML2Spine.spineDiv ϖ ε₁ →
            p < m') →
          (∀ jθ ∈ 𝒰.cover.indexSet a,
            Kakeya.maxDensity (𝒰.nodesUnder p a jθ) (fun j ↦ (𝒰.cover.tube p j).toConvexSpaceBody)
              ≤ (δ : ENNReal) ^ (-(2 * η'))) →
          (∀ jθ ∈ 𝒰.cover.indexSet a, ∀ jp ∈ 𝒰.nodesUnder p a jθ, ∀ m' : ℕ, a < m' → m' < b →
            ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ (1 - ML2Spine.spineDiv ϖ ε₁)
              ≤ (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ) →
            (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ)
              ≤ ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ ML2Spine.spineDiv ϖ ε₁ →
            p < m' →
            ((Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ))
                  ^ (2 + 4 * (ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1) / 16))
              ≤ ((𝒰.nodesUnder m' p jp).card : ℝ)) →
        (∃ tA : Finset ι, tA ⊆ 𝒰.cover.indexSet a ∧
          (∀ k ∈ ML2Reduction.activeNodes (retainedLeafChain 𝒰 t₁ b) p,
            (((retainedLeafChain 𝒰 t₁ b).tube p k).translate v).carrier
              ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) ∧
          (∀ k ∈ ML2Reduction.activeNodes (retainedLeafChain 𝒰 t₁ b) p,
            ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) a p k ∈ tA) ∧
          (∀ (tθ' : Finset ι), tθ' ⊆ tA →
            ∀ (Yθ : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) a)
                (EuclideanSpace ℝ (Fin 3))),
            (∀ l, (Yθ l).toTube = ((retainedLeafChain 𝒰 t₁ b).tube a l).translate v) →
            (δ : NNReal) ^ ηL ≤ ShadedBody.fullness tθ' (fun l => (Yθ l).toShadedBody) →
            ShadedBody.multiplicity tθ' (fun l => (Yθ l).toShadedBody)
              ≤ (δ : ENNReal) ^ (-(εc + ML2Spine.spineRung β ϖ ε₁ gain dens m))
                * ((tθ'.card : ℕ) : ENNReal) ^ β)) ∧
        (∀ (f : Finset ι) (Y : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
          (∀ i ∈ f, (Y i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
          Kakeya.maxDensity f (fun i => (Y i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-ηL) →
          (δ : NNReal) ^ ηL ≤ ShadedBody.fullness f (fun i => (Y i).toShadedBody) →
          ShadedBody.multiplicity f (fun i => (Y i).toShadedBody)
            ≤ (δ : ENNReal) ^ (-εf) * (f.card : ENNReal) ^ β) ∧
        (∀ (tp' : Finset ι), tp' ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain p →
          ∀ (Yp : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) p)
              (EuclideanSpace ℝ (Fin 3))),
          (∀ k, (Yp k).toTube = (𝒰.cover.tube p k).translate v) → ∀ jθ : ι,
          (∀ k ∈ ({k ∈ tp' | ML2Reduction.coarseNode 𝒰.cover.toChain a p k = jθ} : Finset ι),
            (Yp k).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
          (δ : NNReal) ^ ηL ≤ ShadedBody.fullness
            ({k ∈ tp' | ML2Reduction.coarseNode 𝒰.cover.toChain a p k = jθ} : Finset ι)
            (fun k => (Yp k).toShadedBody) →
          ShadedBody.multiplicity
              ({k ∈ tp' | ML2Reduction.coarseNode 𝒰.cover.toChain a p k = jθ} : Finset ι)
              (fun k => (Yp k).toShadedBody)
            ≤ (δ : ENNReal) ^ (-εp)
              * ((({k ∈ tp' | ML2Reduction.coarseNode 𝒰.cover.toChain a p k = jθ} :
                  Finset ι).card : ENNReal)) ^ β) ∧
        (∀ (tτ' : Finset ι), tτ' ⊆ ML2Reduction.activeNodes (retainedLeafChain 𝒰 t₁ b) b →
          ∀ (Yτ' : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) b)
              (EuclideanSpace ℝ (Fin 3))),
          (∀ j, (Yτ' j).toTube = ((retainedLeafChain 𝒰 t₁ b).tube b j).translate v) → ∀ jp : ι,
          ShadedBody.multiplicity
              ({j ∈ tτ' | ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) p b j = jp}
                : Finset ι) (fun j => (Yτ' j).toShadedBody)
            ≤ (δ : ENNReal) ^ (gm (ML2Spine.spineRung β ϖ ε₁ gain dens m))
              * ((({j ∈ tτ' | ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) p b j = jp} :
                  Finset ι).card : ENNReal)) ^ β) ∧
        (∀ n₁ n₂ n₃ : ℕ, ((n₁ : ℕ) : NNReal) ≤ δ ^ (-(4 : ℝ)) →
          ((n₂ : ℕ) : NNReal) ≤ δ ^ (-(4 : ℝ)) → ((n₃ : ℕ) : NNReal) ≤ δ ^ (-(4 : ℝ)) →
          (δ : NNReal) ^ ηL
          ≤ (ML2Reduction.spineScaleLoss 3 n₁ δ *
              ML2Reduction.spineScaleLoss 3 n₂ (Tube.gridScale δ (Tube.ssfGridLen δ) b) *
              ML2Reduction.spineScaleLoss 3 n₃ (Tube.gridScale δ (Tube.ssfGridLen δ) p))⁻¹ *
            ShadedBody.fullness ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)
              (fun i => ((T i).translate v).toShadedBody))

set_option maxHeartbeats 4000000 in
open Classical in
/-- **`Kakeya.ML2Core.HfacPostDropFour` from the analytic rows.**  The wrapper of
`Kakeya.ML2Core.hfacConclusion_of_rows` over the filter and the block's binders. -/
theorem hfacPostDropFour_of_analytic.{u'} {β ϖ ε₁ ηin η' εf εp εc κc ηL : ℝ}
    {gm gain dens : ℝ → ℝ} {Cu₀ : NNReal} (hβ0 : 0 ≤ β) (hηin : ηin ≤ ηL)
    (hres : SiteAnalyticRows.{u'} β ϖ ε₁ ηin η' εf εp εc κc ηL gm gain dens Cu₀) :
    HfacPostDropFour.{u'} β ϖ ε₁ ηin η' εf εp εc κc gm gain dens Cu₀ := by
  have hpos : ∀ᶠ (δ : NNReal) in 𝓝[>] 0, (0 : NNReal) < δ := self_mem_nhdsWithin
  have hle1 : ∀ᶠ (δ : NNReal) in 𝓝[>] 0, δ ≤ 1 := Kakeya.ml1Boot.eventually_le_one_nhdsGT
  filter_upwards [hres, hpos, hle1] with δ hrow hδ0 hδ1
  intro ι u T Cu lam 𝒰 Cstar a b m hwin v t₀ t₁ ht₁ hballt₁ hballleaf hz1 hz2 hz3 hballu
    hune hmax hdense hcomp hlam hcard hCstar hCu hmass hδb hba ha1 p hap hpb hF1 hF2 hF3
  obtain ⟨⟨tA, htAidx, hballπ, hmapsθ, houter⟩, hfineCore, hparCore, hmid, hlead⟩ :=
    hrow u T Cu lam 𝒰 Cstar a b m hwin v t₀ t₁ ht₁ hballt₁ hballleaf hz1 hz2 hz3 hballu
      hune hmax hdense hcomp hlam hcard hCstar hCu hmass hδb hba ha1 p hap hpb hF1 hF2 hF3
  exact hfacConclusion_of_rows 𝒰 hδ0 hδ1 hβ0 hap hpb hwin.fine_le_gridLen hδb hba ha1 ht₁
    hballt₁ hballleaf hmass hmax hηin htAidx hballπ hmapsθ houter hfineCore hparCore hmid hcard
    hlead

/-- **The whole supply the run still owes, with the site row REDUCED to the analytic rows.**

`Kakeya.ML2Core.GeometricCoreSupplySited` with its site conjunct replaced by
`Kakeya.ML2Core.SiteAnalyticRows`.  Every other conjunct is apart from the one new
scalar `ηin ≤ ηL`.  This is the end state of B15: the four factor rows are no longer assumed as a
block, they are the four existing estimates plus one ledger row. -/
def GeometricCoreSupplyAnalytic.{v'} (K' : ℕ) : Prop :=
  ∀ (β ϖ : ℝ) (gain dens : ℝ → ℝ), 0 < β → β ≤ 1 →
    ML2Assembly.Lemma91ParamsAt.{v'} β ϖ gain dens →
    KatzTaoEstimate.{v'} (EuclideanSpace ℝ (Fin 3)) β →
    FrostmanEstimate.{v'} (EuclideanSpace ℝ (Fin 3)) β →
    0 < ϖ ∧ (∀ ζ, 0 < ζ → 0 < gain ζ) ∧ (∀ ζ, 0 < ζ → 0 < dens ζ) ∧
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧
    ∃ (Cu₀ C : NNReal) (Kl cl : ℕ) (ηin aL η' εf εp εc κc κ' θ₂ ηL : ℝ) (gm : ℝ → ℝ),
      0 < aL ∧ 1 ≤ C ∧ 1 ≤ Cu₀ ∧ 0 < κc ∧ 0 < κ' ∧ 0 < θ₂ ∧ 0 < εp ∧ ηin ≤ ηL ∧
      (∀ k : ℕ, k < ML2Spine.spineCount ϖ ε₁ →
        κc + ML2Spine.spineRung β ϖ ε₁ gain dens k ≤ 2 * η') ∧
      (∀ X : ℝ, ML2Spine.spineNu β ϖ ε₁ gain dens ≤ X →
        6 * ML2Spine.spineNu β ϖ ε₁ gain dens + θ₂ + ηin
          ≤ gm X - εf - εp - (εc + X) - κ') ∧
      SiteAnalyticRows.{v'} β ϖ ε₁ ηin η' εf εp εc κc ηL gm gain dens Cu₀ ∧
      SiteWitness.{v'} η ηin (defectMargin β ϖ ε₁ gain dens) aL Cu₀ ∧
      RefinedFloorPayload.{v'} (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ η' gain dens
        (polylogLoss K')

/-- **The final assembly, from the analytic supply.**  `Kakeya.ML2Core.GeometricCoreSupply`'s site
conjunct is now `Kakeya.ML2Core.SiteAnalyticRows`, and the conclusion is unchanged. -/
theorem geometricCoreAt_of_analyticSupply.{v'} (K' : ℕ)
    (hsup : GeometricCoreSupplyAnalytic.{v'} K') : ML2Assembly.GeometricCoreAt.{v'} := by
  refine geometricCoreAt_of_hfac_witness_refinedFloor K'
    (fun β ϖ gain dens hβ0 hβ1 hp hKT hF => ?_)
  obtain ⟨hϖ, hgain, hdens, ε₁, hε₁, η, hη0, hη1, Cu₀, C, Kl, cl, ηin, aL, η', εf, εp, εc, κc, κ',
    θ₂, ηL, gm, haL, hC, hCu₀, hκc, hκ', hθ₂, hεp, hηin, hres, hexp, hrows, hwit, hfloor⟩ :=
    hsup β ϖ gain dens hβ0 hβ1 hp hKT hF
  exact ⟨hϖ, hgain, hdens, ε₁, hε₁, η, hη0, hη1, Cu₀, C, Kl, cl, ηin, aL, η', εf, εp, εc, κc, κ',
    θ₂, gm, haL, hC, hCu₀, hκc, hκ', hθ₂, hεp, hres, hexp,
    hfacPostDropFour_of_analytic hβ0.le hηin hrows, hwit, hfloor⟩

end AnalyticSupply

section OuterFork

open Classical in
/-- **The outer package at `a ≠ 0`: it IS the seam.**  `tA := t₀`, the level-`p` ball row is
`Kakeya.ML2Core.ballRow_pi_of_seam`, the parent map is
`Kakeya.ML2Core.coarseNode_parent_mem_of_retained`, and the outer factor is the caller's coarse
row on `t₀` -- suppliable because `tθ' ⊆ t₀` and the seam's `hz3` is exactly the ball row
(`Kakeya.ML2Core.exists_coarseRow_of_window`). -/
theorem outerPackage_of_seam {ι : Type u} {δ Cu : NNReal} {u : Finset ι}
    {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
    {t₀ t₁ : Finset ι} {a p b : ℕ} {v : EuclideanSpace ℝ (Fin 3)} {β ηL εcm : ℝ}
    (hap : a ≤ p) (hpb : p ≤ b) (hbN : b ≤ Tube.ssfGridLen δ)
    (hz1 : t₀ ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain a)
    (hz2 : ∀ j ∈ t₁, ML2Reduction.coarseNode 𝒰.cover.toChain a b j ∈ t₀)
    (hz3 : ∀ l ∈ t₀, ((𝒰.cover.tube a l).translate v).carrier
      ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (hcoarse : ∀ (tθ' : Finset ι), tθ' ⊆ t₀ →
      ∀ (Yθ : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) a)
          (EuclideanSpace ℝ (Fin 3))),
      (∀ l, (Yθ l).toTube = ((retainedLeafChain 𝒰 t₁ b).tube a l).translate v) →
      (δ : NNReal) ^ ηL ≤ ShadedBody.fullness tθ' (fun l => (Yθ l).toShadedBody) →
      ShadedBody.multiplicity tθ' (fun l => (Yθ l).toShadedBody)
        ≤ (δ : ENNReal) ^ (-εcm) * ((tθ'.card : ℕ) : ENNReal) ^ β) :
    ∃ tA : Finset ι, tA ⊆ 𝒰.cover.indexSet a ∧
      (∀ k ∈ ML2Reduction.activeNodes (retainedLeafChain 𝒰 t₁ b) p,
        (((retainedLeafChain 𝒰 t₁ b).tube p k).translate v).carrier
          ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) ∧
      (∀ k ∈ ML2Reduction.activeNodes (retainedLeafChain 𝒰 t₁ b) p,
        ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) a p k ∈ tA) ∧
      (∀ (tθ' : Finset ι), tθ' ⊆ tA →
        ∀ (Yθ : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) a)
            (EuclideanSpace ℝ (Fin 3))),
        (∀ l, (Yθ l).toTube = ((retainedLeafChain 𝒰 t₁ b).tube a l).translate v) →
        (δ : NNReal) ^ ηL ≤ ShadedBody.fullness tθ' (fun l => (Yθ l).toShadedBody) →
        ShadedBody.multiplicity tθ' (fun l => (Yθ l).toShadedBody)
          ≤ (δ : ENNReal) ^ (-εcm) * ((tθ'.card : ℕ) : ENNReal) ^ β) :=
  ⟨t₀, fun _l hl => ML2Reduction.activeNodes_subset _ _ (hz1 hl),
    ballRow_pi_of_seam 𝒰 hap hpb hbN hz2 hz3,
    coarseNode_parent_mem_of_retained 𝒰 hap hpb hbN hz2, hcoarse⟩

open Classical in
/-- **The outer package at `a = 0`: the source's `n_a = 1`** (l.4447 -- *"an outer `ρ_a`-family"*
with a single ambient cell), and (ii): the new rows are guarded on `p ≠ 0`, not
on `a ≠ 0`, and the two guards come apart.

`tA := 𝒰.cover.indexSet 0`, and the outer factor is
`Kakeya.ML2Core.outer_factor_at_zero_of_card_le_one` -- **no defect estimate and no threshold**,
which is what makes `a = 0` a branch in the producer rather than a condition on the window.

**Two named inputs, and they are the honest cost of the branch.**  `hcard1` is the source's
`n_a = 1`; it is a property of the canonical cover, not of every hierarchy
(`Tube.GridCoverSystem` has no field constraining `indexSet 0`), and the tree has a existing witness
for it (`Kakeya.ML2Reduction.wShaded`).  `hballπ` is the level-`p` ball row: at `a = 0` the seam
supplies none, and `gridScale δ N 0 = 1` means the ambient cell is not inside `B₁` after an
arbitrary translate, so it cannot be derived -- exactly the gap
`Kakeya.ML2Core.not_supplyRow_fourFactorRows` exhibits, surviving at this one level. -/
theorem outerPackage_at_zero {ι : Type u} {δ Cu : NNReal} {u : Finset ι}
    {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
    {t₁ : Finset ι} {a p b : ℕ} {v : EuclideanSpace ℝ (Fin 3)} {β ηL εcm : ℝ}
    (ha : a = 0) (hεcm : 0 ≤ εcm) (hδ1 : (δ : ENNReal) ≤ 1)
    (hcard1 : (𝒰.cover.indexSet a).card ≤ 1)
    (hballπ : ∀ k ∈ ML2Reduction.activeNodes (retainedLeafChain 𝒰 t₁ b) p,
      (((retainedLeafChain 𝒰 t₁ b).tube p k).translate v).carrier
        ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    ∃ tA : Finset ι, tA ⊆ 𝒰.cover.indexSet a ∧
      (∀ k ∈ ML2Reduction.activeNodes (retainedLeafChain 𝒰 t₁ b) p,
        (((retainedLeafChain 𝒰 t₁ b).tube p k).translate v).carrier
          ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) ∧
      (∀ k ∈ ML2Reduction.activeNodes (retainedLeafChain 𝒰 t₁ b) p,
        ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) a p k ∈ tA) ∧
      (∀ (tθ' : Finset ι), tθ' ⊆ tA →
        ∀ (Yθ : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) a)
            (EuclideanSpace ℝ (Fin 3))),
        (∀ l, (Yθ l).toTube = ((retainedLeafChain 𝒰 t₁ b).tube a l).translate v) →
        (δ : NNReal) ^ ηL ≤ ShadedBody.fullness tθ' (fun l => (Yθ l).toShadedBody) →
        ShadedBody.multiplicity tθ' (fun l => (Yθ l).toShadedBody)
          ≤ (δ : ENNReal) ^ (-εcm) * ((tθ'.card : ℕ) : ENNReal) ^ β) := by
  classical
  subst ha
  refine ⟨𝒰.cover.indexSet 0, Finset.Subset.refl _, hballπ, ?_, ?_⟩
  · intro k hk
    exact ML2Reduction.coarseNode_mem (retainedLeafChain 𝒰 t₁ b) (Nat.zero_le _) hk
  · intro tθ' htθ' Yθ _hYθ hfull
    rcases Finset.eq_empty_or_nonempty tθ' with hemp | hne
    · rw [hemp]
      simp
    · -- the source's `n_a = 1`: one cell, multiplicity at most one, no defect estimate
      have hcard1' : tθ'.card = 1 :=
        le_antisymm (le_trans (Finset.card_le_card htθ') hcard1)
          (Finset.card_pos.mpr hne)
      have h1 : ShadedBody.multiplicity tθ' (fun l => (Yθ l).toShadedBody) ≤ 1 := by
        refine le_trans (ShadedBody.multiplicity_le_card tθ' _) ?_
        rw [hcard1']
        simp
      refine h1.trans ?_
      have hpow : (1 : ENNReal) ≤ (δ : ENNReal) ^ (-εcm) := by
        simpa using ENNReal.rpow_le_rpow_of_exponent_ge hδ1 (by linarith : -εcm ≤ 0)
      have hcardE : (((tθ'.card : ℕ) : ENNReal)) ^ β = 1 := by rw [hcard1']; simp
      rw [hcardE, mul_one]
      exact hpow

end OuterFork

section Lead

open Classical in
/-- **`hlead` PRODUCED from the block, and the single scalar it reduces to.**

The row is the source's *"four lower-fullness estimates refer to the same mass-coupled
refinements"* (l.4675-4677) in ledger form.  Two of its three inputs are in the block:

* `hdense` -- `ML2Shaded.HasDenseShading lam u`, which is a **memberwise** clause, so it passes to
  every subfamily (`Kakeya.ML2Shaded.HasDenseShading.subset`) and gives
  `lam ≤ fullness` on the retained leaves (`…le_fullness_tube`);
* translation invariance -- `ShadedBody.fullness_translate_const`, so the seam's `v` costs nothing.

What is left is **one scalar inequality and nothing else**:

`hscal :  L₁ L₂ L₃ · δ^{ηL}  ≤  lam`

with `L₁ L₂ L₃` the split's own three `spineScaleLoss` factors at cardinalities under the block's
`δ^{-4}` ceiling.  The block supplies `lam ≥ δ^{ηin}/2`, so `hscal` is the statement that the three
polylogarithmic split losses are absorbed by `δ^{ηin - ηL}/2` -- exactly the budget line
l.4680-4681 (*"all density, cutoff, grid, and polylogarithmic losses use less than half of the
power"*), inside the total the source fixes at l.4455-4457 and l.4678-4681.  It is a threshold on
`δ` for `ηL > ηin` and it is the only place the ledger enters this block. -/
theorem lead_of_denseShading {ι : Type u} {δ Cu : NNReal} {u : Finset ι}
    {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
    {t₁ : Finset ι} {b : ℕ} {v : EuclideanSpace ℝ (Fin 3)} {lam : NNReal} {ηL : ℝ}
    (hδ0 : 0 < δ)
    (hfamne : ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι).Nonempty)
    (hdense : ML2Shaded.HasDenseShading lam u (fun i => (T i).toShadedBody))
    (hscal : ∀ n₁ n₂ n₃ : ℕ, ((n₁ : ℕ) : NNReal) ≤ δ ^ (-(4 : ℝ)) →
      ((n₂ : ℕ) : NNReal) ≤ δ ^ (-(4 : ℝ)) → ((n₃ : ℕ) : NNReal) ≤ δ ^ (-(4 : ℝ)) →
      ML2Reduction.spineScaleLoss 3 n₁ δ *
          ML2Reduction.spineScaleLoss 3 n₂ (Tube.gridScale δ (Tube.ssfGridLen δ) b) *
          ML2Reduction.spineScaleLoss 3 n₃ (Tube.gridScale δ (Tube.ssfGridLen δ) p) *
        (δ : NNReal) ^ ηL ≤ lam) :
    ∀ n₁ n₂ n₃ : ℕ, ((n₁ : ℕ) : NNReal) ≤ δ ^ (-(4 : ℝ)) →
      ((n₂ : ℕ) : NNReal) ≤ δ ^ (-(4 : ℝ)) → ((n₃ : ℕ) : NNReal) ≤ δ ^ (-(4 : ℝ)) →
      (δ : NNReal) ^ ηL
      ≤ (ML2Reduction.spineScaleLoss 3 n₁ δ *
          ML2Reduction.spineScaleLoss 3 n₂ (Tube.gridScale δ (Tube.ssfGridLen δ) b) *
          ML2Reduction.spineScaleLoss 3 n₃ (Tube.gridScale δ (Tube.ssfGridLen δ) p))⁻¹ *
        ShadedBody.fullness ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)
          (fun i => ((T i).translate v).toShadedBody) := by
  classical
  intro n₁ n₂ n₃ h1 h2 h3
  set L : NNReal := ML2Reduction.spineScaleLoss 3 n₁ δ *
      ML2Reduction.spineScaleLoss 3 n₂ (Tube.gridScale δ (Tube.ssfGridLen δ) b) *
      ML2Reduction.spineScaleLoss 3 n₃ (Tube.gridScale δ (Tube.ssfGridLen δ) p) with hL
  have hL0 : L ≠ 0 := by
    rw [hL]
    exact mul_ne_zero (mul_ne_zero (ML2Reduction.spineScaleLoss_ne_zero _ _ _)
      (ML2Reduction.spineScaleLoss_ne_zero _ _ _)) (ML2Reduction.spineScaleLoss_ne_zero _ _ _)
  -- the dense shading gives `lam ≤ fullness` on the retained leaves, and the translate is free
  have hlamfull : lam ≤ ShadedBody.fullness
      ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)
      (fun i => ((T i).translate v).toShadedBody) := by
    have hsub : ML2Shaded.HasDenseShading lam
        ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) (fun i => (T i).toShadedBody) :=
      hdense.subset (Finset.filter_subset _ _)
    have h := ML2Shaded.HasDenseShading.le_fullness_tube (E := EuclideanSpace ℝ (Fin 3)) hδ0
      hsub hfamne
    rw [← ShadedBody.coe_fullness] at h
    have h' : lam ≤ ShadedBody.fullness ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)
        (fun i => (T i).toShadedBody) := by exact_mod_cast h
    have heq : ShadedBody.fullness ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)
        (fun i => ((T i).translate v).toShadedBody)
        = ShadedBody.fullness ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)
          (fun i => (T i).toShadedBody) :=
      ShadedBody.fullness_translate_const _ (fun i => (T i).toShadedBody) v
    rw [heq]
    exact h'
  refine le_trans ?_ (mul_le_mul_left' hlamfull _)
  have hs := hscal n₁ n₂ n₃ h1 h2 h3
  rw [← hL] at hs
  calc (δ : NNReal) ^ ηL = L⁻¹ * (L * (δ : NNReal) ^ ηL) := by
        rw [← mul_assoc, inv_mul_cancel₀ hL0, one_mul]
    _ ≤ L⁻¹ * lam := by gcongr

end Lead

section HandBack

open Classical in
/-- **`hhb` PRODUCED: the per-fibre hand-back, from the existing producer.**

`Kakeya.VeryNotSticky.exists_centredHandBack_uniform_and_countTransport` is **scale-generic** --
its `δ'` is a parameter of a `Tube.IsRescalingSituation`, not a site's own scale -- so it applies
at the `(p,b)` situation `Kakeya.ML2Core.midRescalingSituation` builds, with `T₀` the translated
level-`p` node tube and `Z'` the split's own `Yτ'`.  What this theorem does is discharge the two
inputs the block gives and name the rest:

**Derived here, from the block:** `hsub` (the fibre's tubes lie in their level-`p` ancestor) is
`Kakeya.ML2Core.fibre_subset_parentTube`, i.e. `tube_le_coarseNode` at the fibre's own `jp`; and
the three conclusions are repackaged into `Kakeya.ML2Core.midRow_of_handBack`'s slots -- `huni` at
`C := ShadedTube.ssfUniformConst 3` with `1 ≤ C` the existing
`ShadedTube.one_le_ssfUniformConst`, and `hcnt` as `CountTransport` **applied** to the geometric
supplier `hsupp`.

**Named, with where the source supplies each:**

* `hunithr` -- `ssfUniformConst 3 ≤ δ'^{-ηd}`.  The folded `huni` conjunct; it is the loose bracket's pre-existing cost made visible, a threshold
  on `δ'` and no more.
* `hcardfib` -- the fibre's cardinality ceiling `#fib ≤ δ'^{-K₀}`.  The block bounds
  `#u ≤ δ^{-4}` and `Kakeya.ML2Core.card_activeNodes_le` carries it to the fibre; what is named
  here is the passage from the ambient `δ` to the rescaled `δ'`.
* `hdensfib` -- `Δ_max` of the rescaled fibre.  The source's upper bound at the middle pair,
  l.4048-4050; the tree's `IsKatzTaoDividingWindow.middle_maxDensity_le` is at `(a,b)`, not
  `(p,b)`, so this is not the block's field.
* `hfullfib` -- the rescaled fibre's fullness, l.5860-5871 (one joint selection, one family).
* `hretfull`, `hretmult` -- the two retention rows, the mass-coupled choice of l.4482-4483
  (*"the pigeonholing retained complete tagged fibres and used their shaded masses as weights"*).
* `hsupp` -- the geometric ED supplier at the contracted radius, i.e. the antecedent of
  `Kakeya.VeryNotSticky.CountTransport`; its route is
  `hED_of_geometricSupplier_of_bridge ∘ defectCoveringBridge'` at `F₀ = 5000⁶`
, l.4811-4826.

**Family:** the `(p,b)` fibre; **shading:** the split's `Yτ'`.  **Level pair:** `(p,b)`. -/
theorem exists_handBack_at_fibre.{w} (K₀ : ℕ) {α α' : ℝ} (hα0 : 0 < α) (hα'0 : 0 < α') :
    ∃ δ₀ : NNReal, 0 < δ₀ ∧
      ∀ {ι : Type w} {δ δ' Cu : NNReal} {u : Finset ι}
        {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
        (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
        {t₁ : Finset ι} {p b : ℕ} {v : EuclideanSpace ℝ (Fin 3)} {R ϖ ζ ηd qc : ℝ}
        (hsit : Tube.IsRescalingSituation (Tube.gridScale δ (Tube.ssfGridLen δ) p)
          (Tube.gridScale δ (Tube.ssfGridLen δ) b) δ' R 3) (hR : 0 < R),
        ((Tube.gridScale δ (Tube.ssfGridLen δ) b : NNReal) : ℝ)
            / ((Tube.gridScale δ (Tube.ssfGridLen δ) p : NNReal) : ℝ) ≤ 4 * (δ' : ℝ) →
        0 < δ' → δ' ≤ δ₀ → (δ' : ℝ) ≤ 1 / 20 →
        0 < qc → α' ≤ qc → (512 : ENNReal) ≤ (δ' : ENNReal) ^ (-qc) →
        0 ≤ ϖ → 0 ≤ 2 + ζ → δ' ^ ϖ ≤ 1 / 2 →
        ((ShadedTube.ssfUniformConst 3 : NNReal) : ENNReal) ≤ (δ' : ENNReal) ^ (-ηd) →
        p ≤ b → b ≤ Tube.ssfGridLen δ →
        ∀ (tτ' : Finset ι),
        tτ' ⊆ ML2Reduction.activeNodes (retainedLeafChain 𝒰 t₁ b) b →
        ∀ (Yτ' : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) b)
            (EuclideanSpace ℝ (Fin 3))),
        (∀ j, (Yτ' j).toTube = ((retainedLeafChain 𝒰 t₁ b).tube b j).translate v) →
        ∀ jp : ι,
        ({j ∈ tτ' | ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) p b j = jp}
          : Finset ι).Nonempty →
        ((({j ∈ tτ' | ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) p b j = jp}
            : Finset ι).card : ℝ) ≤ (δ' : ℝ) ^ (-(K₀ : ℝ))) →
        (Kakeya.maxDensity
            ({j ∈ tτ' | ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) p b j = jp}
              : Finset ι)
            (fun i ↦ (ML2Reduction.outerFamily hsit.pos_ambient
              (((retainedLeafChain 𝒰 t₁ b).tube p jp).translate v) hR δ' Yτ'
              i).toConvexSpaceBody) ≤ (δ' : ENNReal) ^ (-qc)) →
        ((δ' : ENNReal) ^ qc ≤ ShadedBody.fullness
            ({j ∈ tτ' | ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) p b j = jp}
              : Finset ι)
            (fun i ↦ (ML2Reduction.outerFamily hsit.pos_ambient
              (((retainedLeafChain 𝒰 t₁ b).tube p jp).translate v) hR δ' Yτ'
              i).toShadedBody)) →
        (∀ t ⊆ ({j ∈ tτ' | ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) p b j = jp}
            : Finset ι),
          ((({j ∈ tτ' | ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) p b j = jp}
              : Finset ι).card : ℝ) ≤ (δ' : ℝ) ^ (-α) * (t.card : ℝ)) →
          (δ' : ENNReal) ^ qc ≤ ShadedBody.fullness t
            (fun i ↦ (ML2Reduction.outerFamily hsit.pos_ambient
              (((retainedLeafChain 𝒰 t₁ b).tube p jp).translate v) hR δ' Yτ'
              i).toShadedBody)) →
        (∀ t ⊆ ({j ∈ tτ' | ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) p b j = jp}
            : Finset ι),
          ((({j ∈ tτ' | ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) p b j = jp}
              : Finset ι).card : ℝ) ≤ (δ' : ℝ) ^ (-α) * (t.card : ℝ)) →
          ShadedBody.multiplicity
              ({j ∈ tτ' | ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) p b j = jp}
                : Finset ι)
              (fun i ↦ (ML2Reduction.outerFamily hsit.pos_ambient
                (((retainedLeafChain 𝒰 t₁ b).tube p jp).translate v) hR δ' Yτ'
                i).toShadedBody)
            ≤ (δ' : ENNReal) ^ (-(3 * qc - α')) * ShadedBody.multiplicity t
              (fun i ↦ (ML2Reduction.outerFamily hsit.pos_ambient
                (((retainedLeafChain 𝒰 t₁ b).tube p jp).translate v) hR δ' Yτ'
                i).toShadedBody)) →
        -- the geometric ED supplier: `CountTransport`'s own antecedent, at any retained subfamily
        (∀ (s'' : Finset ι),
          s'' ⊆ ({j ∈ tτ' | ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) p b j = jp}
            : Finset ι) →
          ∀ ρ : NNReal, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
          ∃ (κ₀ : Type w) (t : Finset κ₀)
            (W : κ₀ → Tube (ρ / Kakeya.VeryNotSticky.centringCoverRadiusConstant)
              (EuclideanSpace ℝ (Fin 3))),
            ((t : Set κ₀).Pairwise
              fun j k ↦ _root_.IsEssentiallyDistinct (W j).carrier (W k).carrier) ∧
            (∀ j ∈ t, ∃ i ∈ s'',
              (ML2Reduction.spineFamily (ML2Reduction.spineRescaleUnit hsit.pos_ambient
                  (((retainedLeafChain 𝒰 t₁ b).tube p jp).translate v) hR) Yτ'
                i).toConvexSpaceBody ≤ (W j).toConvexSpaceBody) ∧
            (Kakeya.VeryNotSticky.centringCountLossConstant R : ℝ)
              * ((ρ / Kakeya.VeryNotSticky.centringCoverRadiusConstant : NNReal) : ℝ) ^ (-2 - ζ)
                ≤ (t.card : ℝ)) →
        ∃ (s'' : Finset ι) (U'' : ι → ShadedTube δ' (EuclideanSpace ℝ (Fin 3))),
          s'' ⊆ ({j ∈ tτ' | ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) p b j = jp}
            : Finset ι) ∧
          Kakeya.VeryNotSticky.CentredHandBack hsit hR
              (((retainedLeafChain 𝒰 t₁ b).tube p jp).translate v) 0 qc
              ({j ∈ tτ' | ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) p b j = jp}
                : Finset ι) s'' Yτ' U'' ∧
          (∃ C : NNReal, 1 ≤ C ∧ (C : ENNReal) ≤ (δ' : ENNReal) ^ (-ηd) ∧
            Nonempty (ShadedTube.ShadedUniformTubeSet s'' U'' (Tube.ssfGridLen δ') C)) ∧
          (∀ ρ : NNReal, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
            ∃ (κ : Type w) (tρ : Finset κ) (Tρ : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
              (tρ : Set κ).Pairwise
                (fun j k ↦ _root_.IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) ∧
              (∀ j ∈ tρ, ∃ i ∈ s'', (U'' i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) ∧
              (ρ : ℝ) ^ (-2 - ζ) ≤ (tρ.card : ℝ)) := by
  classical
  obtain ⟨δ₀, hδ₀0, hcore⟩ :=
    Kakeya.VeryNotSticky.exists_centredHandBack_uniform_and_countTransport.{w} K₀ hα0 hα'0
  refine ⟨δ₀, hδ₀0, ?_⟩
  intro ι δ δ' Cu u T 𝒰 t₁ p b v R ϖ ζ ηd qc hsit hR hτσ hδ'0 hδle hδ'20 hqc0 hα'qc hthr512
    hϖ hζ hthr hunithr hpb hbN tτ' htτ' Yτ' hYτ' jp hfne hcardfib hdensfib hfullfib hretfull
    hretmult hsupp
  obtain ⟨s'', hs''sub, U'', _hcardret, hcb, hct, hstruct⟩ :=
    hcore hsit hR hτσ hδ'0 hδle hδ'20
      (((retainedLeafChain 𝒰 t₁ b).tube p jp).translate v) hqc0 hα'qc hthr512 hϖ hζ hthr
      ({j ∈ tτ' | ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) p b j = jp} : Finset ι)
      Yτ' hfne (fibre_subset_parentTube 𝒰 hpb hbN htτ' hYτ' jp) hcardfib hdensfib hfullfib
      hretfull hretmult
  refine ⟨s'', U'', hs''sub, hcb,
    ⟨ShadedTube.ssfUniformConst 3, ShadedTube.one_le_ssfUniformConst 3, hunithr, hstruct⟩,
    fun ρ hρ => hct ρ hρ (hsupp s'' hs''sub ρ hρ)⟩

end HandBack

section RowsTie

open Classical in
/-- **`Kakeya.ML2Core.SiteAnalyticRows`'s five conjuncts, assembled from the producers.**

The elaborator adjudicates the fit: each slot is filled by *applying* the producer, not by a
transcription of its conclusion.

* the outer package -- `Kakeya.ML2Core.outerPackage_of_seam` at `a ≠ 0` (`tA := t₀`, so the ball
  row is the seam's `hz3` and the parent map its `hz2`); the `a = 0` branch is
  `Kakeya.ML2Core.outerPackage_at_zero`;
* the inner factor -- `Kakeya.ML2Core.exists_fine_factor`'s own body, at `ε := εf`;
* the new-parent factor -- `Kakeya.ML2Core.exists_newParent_factor_at`'s own body;
* the middle factor -- `Kakeya.ML2Core.midRow_of_handBack`, whose `hhb` is
  `Kakeya.ML2Core.exists_handBack_at_fibre`;
* the ledger row -- `Kakeya.ML2Core.lead_of_denseShading`, i.e. the block's `hdense` plus the one
  scalar `hscal`.

**Loss allocation.**  `εcm = εc + η_m` is the window's own outer line and `gmv = gm(η_m)` the VNS
gain; `εp` is `exists_newParent_factor_at`'s.  As  records, none of these is a
source display -- the source fixes only the total (l.4455-4457, l.4678-4681), and it is `hexp`
that carries it. -/
theorem siteAnalyticRowsAt_of_producers {ι : Type u} {δ δ' Cu : NNReal} {u : Finset ι}
    {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
    {t₀ t₁ : Finset ι} {a p b : ℕ} {v : EuclideanSpace ℝ (Fin 3)} {lam : NNReal}
    {β ηL εf εp εcm gmv R ϖ ζ ν ν₀ ηd cst qc : ℝ}
    (hδ0 : 0 < δ) (hap : a ≤ p) (hpb : p ≤ b) (hbN : b ≤ Tube.ssfGridLen δ)
    -- the seam rows, from the block (`a ≠ 0` branch)
    (hz1 : t₀ ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain a)
    (hz2 : ∀ j ∈ t₁, ML2Reduction.coarseNode 𝒰.cover.toChain a b j ∈ t₀)
    (hz3 : ∀ l ∈ t₀, ((𝒰.cover.tube a l).translate v).carrier
      ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (hcoarse : ∀ (tθ' : Finset ι), tθ' ⊆ t₀ →
      ∀ (Yθ : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) a)
          (EuclideanSpace ℝ (Fin 3))),
      (∀ l, (Yθ l).toTube = ((retainedLeafChain 𝒰 t₁ b).tube a l).translate v) →
      (δ : NNReal) ^ ηL ≤ ShadedBody.fullness tθ' (fun l => (Yθ l).toShadedBody) →
      ShadedBody.multiplicity tθ' (fun l => (Yθ l).toShadedBody)
        ≤ (δ : ENNReal) ^ (-εcm) * ((tθ'.card : ℕ) : ENNReal) ^ β)
    -- the two analytic cores, in their producers' own shapes
    (hfineCore : ∀ (f : Finset ι) (Y : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
      (∀ i ∈ f, (Y i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
      Kakeya.maxDensity f (fun i => (Y i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-ηL) →
      (δ : NNReal) ^ ηL ≤ ShadedBody.fullness f (fun i => (Y i).toShadedBody) →
      ShadedBody.multiplicity f (fun i => (Y i).toShadedBody)
        ≤ (δ : ENNReal) ^ (-εf) * (f.card : ENNReal) ^ β)
    (hparCore : ∀ (tp' : Finset ι), tp' ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain p →
      ∀ (Yp : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) p)
          (EuclideanSpace ℝ (Fin 3))),
      (∀ k, (Yp k).toTube = (𝒰.cover.tube p k).translate v) → ∀ jθ : ι,
      (∀ k ∈ ({k ∈ tp' | ML2Reduction.coarseNode 𝒰.cover.toChain a p k = jθ} : Finset ι),
        (Yp k).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
      (δ : NNReal) ^ ηL ≤ ShadedBody.fullness
        ({k ∈ tp' | ML2Reduction.coarseNode 𝒰.cover.toChain a p k = jθ} : Finset ι)
        (fun k => (Yp k).toShadedBody) →
      ShadedBody.multiplicity
          ({k ∈ tp' | ML2Reduction.coarseNode 𝒰.cover.toChain a p k = jθ} : Finset ι)
          (fun k => (Yp k).toShadedBody)
        ≤ (δ : ENNReal) ^ (-εp)
          * ((({k ∈ tp' | ML2Reduction.coarseNode 𝒰.cover.toChain a p k = jθ} :
              Finset ι).card : ENNReal)) ^ β)
    -- the middle factor's inputs
    (hsit : Tube.IsRescalingSituation (Tube.gridScale δ (Tube.ssfGridLen δ) p)
      (Tube.gridScale δ (Tube.ssfGridLen δ) b) δ' R 3)
    (hR : 0 < R) (hR1 : 1 ≤ R)
    (hτσ : ((Tube.gridScale δ (Tube.ssfGridLen δ) b : NNReal) : ℝ)
        / ((Tube.gridScale δ (Tube.ssfGridLen δ) p : NNReal) : ℝ) ≤ 4 * (δ' : ℝ))
    (hδ'0 : 0 < δ') (hϖ0 : 0 ≤ ϖ) (hβ0 : 0 ≤ β) (hqc0 : 0 < qc)
    (hνqc : ν + 3 * qc ≤ ν₀) (h3qc : 3 * qc ≤ ηd)
    (hL : ML2Reduction.Lemma91At.{u} β ϖ ζ ν₀ ηd δ')
    (hζ : ζ * (1 - ϖ) ≤ ηd + 2 * ϖ)
    (hloss : ML2Reduction.outerLoss R ≤ δ' ^ (-cst))
    (hscale : (δ' : ENNReal) ^ ν ≤ (δ : ENNReal) ^ gmv)
    (hhb : ∀ (tτ' : Finset ι),
      tτ' ⊆ ML2Reduction.activeNodes (retainedLeafChain 𝒰 t₁ b) b →
      ∀ (Yτ' : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) b)
          (EuclideanSpace ℝ (Fin 3))),
      (∀ j, (Yτ' j).toTube = ((retainedLeafChain 𝒰 t₁ b).tube b j).translate v) →
      ∀ jp : ι,
      ({j ∈ tτ' | ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) p b j = jp}
        : Finset ι).Nonempty →
      ∃ (s'' : Finset ι) (U'' : ι → ShadedTube δ' (EuclideanSpace ℝ (Fin 3))),
        s'' ⊆ ({j ∈ tτ' | ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) p b j = jp}
          : Finset ι) ∧
        Kakeya.VeryNotSticky.CentredHandBack hsit hR
            (((retainedLeafChain 𝒰 t₁ b).tube p jp).translate v) 0 qc
            ({j ∈ tτ' | ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) p b j = jp}
              : Finset ι) s'' Yτ' U'' ∧
        (∃ C : NNReal, 1 ≤ C ∧ (C : ENNReal) ≤ (δ' : ENNReal) ^ (-ηd) ∧
          Nonempty (ShadedTube.ShadedUniformTubeSet s'' U'' (Tube.ssfGridLen δ') C)) ∧
        (∀ ρ : NNReal, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
          ∃ (κ : Type u) (tρ : Finset κ) (Tρ : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
            (tρ : Set κ).Pairwise
              (fun j k ↦ _root_.IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) ∧
            (∀ j ∈ tρ, ∃ i ∈ s'', (U'' i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) ∧
            (ρ : ℝ) ^ (-2 - ζ) ≤ (tρ.card : ℝ)))
    -- the ledger row's inputs
    (hfamne : ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι).Nonempty)
    (hdense : ML2Shaded.HasDenseShading lam u (fun i => (T i).toShadedBody))
    (hscal : ∀ n₁ n₂ n₃ : ℕ, ((n₁ : ℕ) : NNReal) ≤ δ ^ (-(4 : ℝ)) →
      ((n₂ : ℕ) : NNReal) ≤ δ ^ (-(4 : ℝ)) → ((n₃ : ℕ) : NNReal) ≤ δ ^ (-(4 : ℝ)) →
      ML2Reduction.spineScaleLoss 3 n₁ δ *
          ML2Reduction.spineScaleLoss 3 n₂ (Tube.gridScale δ (Tube.ssfGridLen δ) b) *
          ML2Reduction.spineScaleLoss 3 n₃ (Tube.gridScale δ (Tube.ssfGridLen δ) p) *
        (δ : NNReal) ^ ηL ≤ lam) :
    (∃ tA : Finset ι, tA ⊆ 𝒰.cover.indexSet a ∧
      (∀ k ∈ ML2Reduction.activeNodes (retainedLeafChain 𝒰 t₁ b) p,
        (((retainedLeafChain 𝒰 t₁ b).tube p k).translate v).carrier
          ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) ∧
      (∀ k ∈ ML2Reduction.activeNodes (retainedLeafChain 𝒰 t₁ b) p,
        ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) a p k ∈ tA) ∧
      (∀ (tθ' : Finset ι), tθ' ⊆ tA →
        ∀ (Yθ : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) a)
            (EuclideanSpace ℝ (Fin 3))),
        (∀ l, (Yθ l).toTube = ((retainedLeafChain 𝒰 t₁ b).tube a l).translate v) →
        (δ : NNReal) ^ ηL ≤ ShadedBody.fullness tθ' (fun l => (Yθ l).toShadedBody) →
        ShadedBody.multiplicity tθ' (fun l => (Yθ l).toShadedBody)
          ≤ (δ : ENNReal) ^ (-εcm) * ((tθ'.card : ℕ) : ENNReal) ^ β)) ∧
    (∀ (f : Finset ι) (Y : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
      (∀ i ∈ f, (Y i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
      Kakeya.maxDensity f (fun i => (Y i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-ηL) →
      (δ : NNReal) ^ ηL ≤ ShadedBody.fullness f (fun i => (Y i).toShadedBody) →
      ShadedBody.multiplicity f (fun i => (Y i).toShadedBody)
        ≤ (δ : ENNReal) ^ (-εf) * (f.card : ENNReal) ^ β) ∧
    (∀ (tp' : Finset ι), tp' ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain p →
      ∀ (Yp : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) p)
          (EuclideanSpace ℝ (Fin 3))),
      (∀ k, (Yp k).toTube = (𝒰.cover.tube p k).translate v) → ∀ jθ : ι,
      (∀ k ∈ ({k ∈ tp' | ML2Reduction.coarseNode 𝒰.cover.toChain a p k = jθ} : Finset ι),
        (Yp k).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) →
      (δ : NNReal) ^ ηL ≤ ShadedBody.fullness
        ({k ∈ tp' | ML2Reduction.coarseNode 𝒰.cover.toChain a p k = jθ} : Finset ι)
        (fun k => (Yp k).toShadedBody) →
      ShadedBody.multiplicity
          ({k ∈ tp' | ML2Reduction.coarseNode 𝒰.cover.toChain a p k = jθ} : Finset ι)
          (fun k => (Yp k).toShadedBody)
        ≤ (δ : ENNReal) ^ (-εp)
          * ((({k ∈ tp' | ML2Reduction.coarseNode 𝒰.cover.toChain a p k = jθ} :
              Finset ι).card : ENNReal)) ^ β) ∧
    (∀ (tτ' : Finset ι), tτ' ⊆ ML2Reduction.activeNodes (retainedLeafChain 𝒰 t₁ b) b →
      ∀ (Yτ' : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) b)
          (EuclideanSpace ℝ (Fin 3))),
      (∀ j, (Yτ' j).toTube = ((retainedLeafChain 𝒰 t₁ b).tube b j).translate v) → ∀ jp : ι,
      ShadedBody.multiplicity
          ({j ∈ tτ' | ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) p b j = jp}
            : Finset ι) (fun j => (Yτ' j).toShadedBody)
        ≤ (δ : ENNReal) ^ gmv
          * ((({j ∈ tτ' | ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) p b j = jp} :
              Finset ι).card : ENNReal)) ^ β) ∧
    (∀ n₁ n₂ n₃ : ℕ, ((n₁ : ℕ) : NNReal) ≤ δ ^ (-(4 : ℝ)) →
      ((n₂ : ℕ) : NNReal) ≤ δ ^ (-(4 : ℝ)) → ((n₃ : ℕ) : NNReal) ≤ δ ^ (-(4 : ℝ)) →
      (δ : NNReal) ^ ηL
      ≤ (ML2Reduction.spineScaleLoss 3 n₁ δ *
          ML2Reduction.spineScaleLoss 3 n₂ (Tube.gridScale δ (Tube.ssfGridLen δ) b) *
          ML2Reduction.spineScaleLoss 3 n₃ (Tube.gridScale δ (Tube.ssfGridLen δ) p))⁻¹ *
        ShadedBody.fullness ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)
          (fun i => ((T i).translate v).toShadedBody)) :=
  ⟨outerPackage_of_seam 𝒰 hap hpb hbN hz1 hz2 hz3 hcoarse,
   hfineCore, hparCore,
   midRow_of_handBack 𝒰 hpb hbN hsit hR hR1 hτσ hδ'0 hϖ0 hβ0 hqc0 hνqc h3qc hL hζ hloss hscale
     hhb,
   lead_of_denseShading 𝒰 hδ0 hfamne hdense hscal⟩

end RowsTie

section ZeroBallGap

/-- A leaf tube centred at the origin: core the unit segment from `-e₀/2` to `e₀/2`. -/
noncomputable def siteCentredTube (δ : NNReal) : Tube δ (EuclideanSpace ℝ (Fin 3)) :=
  Tube.mk' δ (x := (-(1/2 : ℝ)) • siteAxis) (y := (1/2 : ℝ) • siteAxis)
    (by
      rw [dist_eq_norm, ← sub_smul]
      norm_num [norm_smul, norm_siteAxis])

/-- **The `a = 0` gap, measured: the block's ball rows do NOT give the level-`0` one.**

At `a = 0` the seam supplies no level-`a` ball row (`hz1`-`hz3` are guarded on `a ≠ 0`), so the
only candidates are the block's own `hballu` (the LEAVES lie in `B₁`) and `hballleaf` (they lie in
`B₁` after the seam's translate).  Neither gives the level-`0` node row, and this is why:
`Tube.gridScale δ N 0 = 1`, so a level-`0` node is a **radius-one** tube, and a radius-one tube
around a core that sits inside `B₁` reaches norm `3/2`.

The witness is a leaf entirely inside `B₁` -- core the unit segment centred at the origin, radius
`δ ≤ 1/2` -- whose level-`0` node in the tree's own self-hierarchy shape
(`Tube.UniformTubeSet.self`: `tube k i = (T i).rescale (gridScale δ N k)`) leaves `B₁` **even at
the best possible translate `v = 0`**.

So `hballπ` at `a = 0` is a genuine obligation and not a derivation, and
`Kakeya.ML2Core.outerPackage_at_zero` is right to name it.  The source's `a = 0` case has the
single ambient cell equal to the ball itself (l.4447); the tree's radius-one `gridScale δ N 0`
tube is a different object, and that difference is exactly this gap. -/
theorem ballRow_at_zero_fails {δ : NNReal} (hδ : (δ : ℝ) ≤ 1 / 2) :
    (siteCentredTube δ).carrier
        ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 ∧
      ¬ (((siteCentredTube δ).rescale 1).translate (0 : EuclideanSpace ℝ (Fin 3))).carrier
        ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  constructor
  · -- the leaf: core in `B_{1/2}`, radius `δ ≤ 1/2`
    intro z hz
    rw [Tube.carrier_eq] at hz
    simp only [Set.mem_iUnion, exists_prop] at hz
    obtain ⟨w, hw, hzw⟩ := hz
    rw [Metric.mem_closedBall] at hzw ⊢
    have hwnorm : ‖w‖ ≤ 1 / 2 := by
      obtain ⟨s, t, hs, ht, hst, rfl⟩ := hw
      have hxy : s • (siteCentredTube δ).x + t • (siteCentredTube δ).y
          = ((t - s) / 2) • siteAxis := by
        show s • (-(1/2 : ℝ)) • siteAxis + t • (1/2 : ℝ) • siteAxis = _
        rw [smul_smul, smul_smul, ← add_smul]
        congr 1
        ring
      rw [hxy, norm_smul, norm_siteAxis, mul_one, Real.norm_eq_abs]
      rw [abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
      have h1 : |t - s| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith
      linarith
    have hzw' : dist z w ≤ (δ : ℝ) := hzw
    have hw0 : dist w 0 ≤ 1 / 2 := by rwa [dist_zero_right]
    calc dist z 0 ≤ dist z w + dist w 0 := dist_triangle z w 0
      _ ≤ (δ : ℝ) + 1 / 2 := add_le_add hzw' hw0
      _ ≤ 1 := by linarith
  · -- the level-`0` node: radius one, so it reaches norm `3/2`
    intro hsub
    have hmem : ((-(3/2 : ℝ)) • siteAxis)
        ∈ (((siteCentredTube δ).rescale 1).translate
          (0 : EuclideanSpace ℝ (Fin 3))).carrier := by
      show ((0 : EuclideanSpace ℝ (Fin 3)) + ·) ''
        ((siteCentredTube δ).rescale 1).carrier |>.Mem _
      refine ⟨(-(3/2 : ℝ)) • siteAxis, ?_, by simp⟩
      rw [Tube.carrier_eq]
      refine Set.mem_biUnion (left_mem_segment ℝ _ _) ?_
      rw [Metric.mem_closedBall, dist_eq_norm]
      show ‖(-(3/2 : ℝ)) • siteAxis - (-(1/2 : ℝ)) • siteAxis‖ ≤ ((1 : NNReal) : ℝ)
      rw [← sub_smul]
      norm_num [norm_smul, norm_siteAxis]
    have := hsub hmem
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, norm_siteAxis] at this
    norm_num at this

end ZeroBallGap

end Kakeya.ML2Core

end
