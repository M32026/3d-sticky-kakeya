module

public import Kakeya.DimensionThree.MainLemma1.BlockSkeleton
public import Kakeya.DimensionThree.MainLemma1.ThreePass
public import Kakeya.DimensionThree.MainLemma1.TwoScaleProductOnlyBallRichW49

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology
open scoped NNReal ENNReal

namespace Kakeya.ml1Boot.W50Upstream

noncomputable section
set_option maxHeartbeats 12000000

universe u v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [FiniteDimensional Real E]
  [MeasurableSpace E] [BorelSpace E]


/-! ## A counted deduplication -/

omit [MeasurableSpace E] [BorelSpace E] in
/-- Deduplicate a parent carrier by its convex bodies, retaining the representative map.

Besides the `IsParentFamily` certificate, this version records that every original active
parent has a representative with the same body and that the representative map is onto the
deduplicated carrier.  Thus no injectivity of the original body indexing is assumed. -/
theorem exists_dedupParentFamily_counted_upstream_w50 {ι κ : Type*} {σ ρ : NNReal}
    {s : Finset ι} {V : ι → Tube σ E} {t : Finset κ} {W : κ → Tube ρ E} {p : ι → κ}
    (ht : t.Nonempty) (hmaps : ∀ i ∈ s, p i ∈ t)
    (hle : ∀ i ∈ s, (V i).toConvexSpaceBody ≤ (W (p i)).toConvexSpaceBody) :
    ∃ (t' : Finset κ) (p' : ι → κ) (rep : κ → κ),
      t' ⊆ t ∧
      (∀ i, p' i ∈ t') ∧
      (∀ i ∈ s, p' i = rep (p i)) ∧
      (∀ j ∈ t, rep j ∈ t' ∧
        (W (rep j)).toConvexSpaceBody = (W j).toConvexSpaceBody) ∧
      (∀ j' ∈ t', ∃ j ∈ t, rep j = j') ∧
      (∀ i ∈ s,
        (W (p' i)).toConvexSpaceBody = (W (p i)).toConvexSpaceBody) ∧
      IsParentFamily s V t' W p' := by
  classical
  obtain ⟨j₀, hj₀⟩ := ht
  let f : κ → ConvexSpaceBody E := fun k => (W k).toConvexSpaceBody
  let repOf : ConvexSpaceBody E → κ := fun B =>
    if h : ∃ j, j ∈ t ∧ f j = B then h.choose else j₀
  have hrepOf_mem : ∀ B, repOf B ∈ t := by
    intro B
    by_cases h : ∃ j, j ∈ t ∧ f j = B
    · simp only [repOf, dif_pos h]
      exact h.choose_spec.1
    · simp only [repOf, dif_neg h]
      exact hj₀
  have hrepOf_eq : ∀ j ∈ t, f (repOf (f j)) = f j := by
    intro j hj
    have h : ∃ j', j' ∈ t ∧ f j' = f j := ⟨j, hj, rfl⟩
    simp only [repOf, dif_pos h]
    exact h.choose_spec.2
  let rep : κ → κ := fun k => repOf (f k)
  let t' : Finset κ := t.image rep
  let p' : ι → κ := fun i => if p i ∈ t then rep (p i) else rep j₀
  have ht'sub : t' ⊆ t := by
    intro k hk
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hk
    exact hrepOf_mem _
  have hp'tot : ∀ i, p' i ∈ t' := by
    intro i
    by_cases h : p i ∈ t
    · simp only [p', if_pos h, t']
      exact Finset.mem_image_of_mem rep h
    · simp only [p', if_neg h, t']
      exact Finset.mem_image_of_mem rep hj₀
  have hp'rep : ∀ i ∈ s, p' i = rep (p i) := by
    intro i hi
    simp only [p', if_pos (hmaps i hi)]
  have hrep : ∀ j ∈ t, rep j ∈ t' ∧
      (W (rep j)).toConvexSpaceBody = (W j).toConvexSpaceBody := by
    intro j hj
    refine ⟨Finset.mem_image_of_mem rep hj, ?_⟩
    exact hrepOf_eq j hj
  have honto : ∀ j' ∈ t', ∃ j ∈ t, rep j = j' := by
    intro j' hj'
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hj'
    exact ⟨j, hj, rfl⟩
  have hp'body : ∀ i ∈ s,
      (W (p' i)).toConvexSpaceBody = (W (p i)).toConvexSpaceBody := by
    intro i hi
    rw [hp'rep i hi]
    exact hrepOf_eq (p i) (hmaps i hi)
  refine ⟨t', p', rep, ht'sub, hp'tot, hp'rep, hrep, honto, hp'body, ?_⟩
  refine
    { mapsTo := fun i _ => hp'tot i
      injOn := ?_
      le_parent := ?_ }
  · intro x hx y hy hxy
    obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨y₀, hy₀, rfl⟩ := Finset.mem_image.mp hy
    have hxbody := hrepOf_eq x₀ hx₀
    have hybody := hrepOf_eq y₀ hy₀
    have hbody : f x₀ = f y₀ := by
      rw [← hxbody, ← hybody]
      exact hxy
    change rep x₀ = rep y₀
    exact congrArg repOf hbody
  · intro i hi
    calc
      (V i).toConvexSpaceBody ≤ (W (p i)).toConvexSpaceBody := hle i hi
      _ = (W (p' i)).toConvexSpaceBody := (hp'body i hi).symm

/-- The product-only certificate, duplicated upstream of `CaseTwo` so that the raw producer
does not import any Case-Two consumer or the `MainLemma1` umbrella. -/
structure IsCaseTwoDirectFactorsUpstreamW50
    {delta tau theta : NNReal} {iota kappa : Type u} [DecidableEq kappa]
    (s : Finset iota) (T : iota -> ShadedTube delta E)
    (tTau : Finset kappa) (TTau : kappa -> Tube tau E) (pTau : iota -> kappa)
    (tTheta : Finset kappa) (TTheta : kappa -> Tube theta E) (pTheta : kappa -> kappa)
    (M : Nat) (tm : Finset kappa) (sf : Finset iota)
    (ZTau : kappa -> ShadedTube tau E) (Zf : iota -> ShadedTube delta E)
    (uCell : Finset kappa) (v0 : E) (tc sm : Finset kappa)
    (Zc : kappa -> ShadedTube theta E) (Zm : kappa -> ShadedTube tau E)
    (kF lM : kappa) : Prop where
  fine_nonempty : (fibre sf pTau kF).Nonempty
  middle_nonempty : (fibre sm pTheta lM).Nonempty
  coarse_nonempty : tc.Nonempty
  mid_subset : tm ⊆ tTau
  fine_subset : sf ⊆ s
  cell_subset : uCell ⊆ tm
  middle_subset : sm ⊆ uCell
  coarse_subset : tc ⊆ tTheta
  fine_mem : kF ∈ tm
  middle_mem : lM ∈ tc
  fine_maps : ∀ i ∈ sf, pTau i ∈ tm
  fine_card_band : ∀ k ∈ tm, ∀ k' ∈ tm,
    ((fibre sf pTau k).card : ENNReal) <=
      2 * ((fibre sf pTau k').card : ENNReal)
  middle_maps : ∀ k ∈ sm, pTheta k ∈ tc
  middle_card_band : ∀ l ∈ tc, ∀ l' ∈ tc,
    ((fibre sm pTheta l).card : ENNReal) <=
      2 * ((fibre sm pTheta l').card : ENNReal)
  fine_tube : ∀ i, (Zf i).toTube = (T i).toTube
  outer_tube : ∀ k, (ZTau k).toTube = TTau k
  coarse_tube : ∀ l, (Zc l).toTube = TTheta l
  middle_tube : ∀ k, (Zm k).toTube = (TTau k).translate v0
  middle_ball : ∀ k ∈ uCell, (Zm k).carrier ⊆ Metric.closedBall 0 1
  cell_fullness : ((1 / 2 : NNReal) : ENNReal) *
      ShadedBody.fullness tm (fun k => (ZTau k).toShadedBody) <=
    ShadedBody.fullness uCell (fun k => ((ZTau k).translate v0).toShadedBody)
  cell_mass : (∑ k ∈ tm, volume (ZTau k).shade) <=
    4 * (M : ENNReal) * ∑ k ∈ uCell, volume ((ZTau k).translate v0).shade
  outer_fullness : (factorOneScale.C s.card delta)⁻¹ *
      ShadedBody.fullness s (fun i => (T i).toShadedBody) <=
    ShadedBody.fullness tm (fun k => (ZTau k).toShadedBody)
  fine_refinement : ShadedBody.IsCRefinement sf
    (fun i => (Zf i).toShadedBody) s (fun i => (T i).toShadedBody)
    (factorOneScale.C s.card delta)⁻¹
  coarse_fullness : (factorOneScale.C uCell.card tau)⁻¹ *
      (((1 / 2 : NNReal) : ENNReal) *
        ShadedBody.fullness tm (fun k => (ZTau k).toShadedBody)) <=
    ShadedBody.fullness tc (fun l => (Zc l).toShadedBody)
  middle_refinement : ShadedBody.IsCRefinement sm
    (fun k => (Zm k).toShadedBody) uCell
    (fun k => ((ZTau k).translate v0).toShadedBody)
    (factorOneScale.C uCell.card tau)⁻¹
  fine_fullness : ShadedBody.fullness sf (fun i => (Zf i).toShadedBody) <=
    ShadedBody.fullness (fibre sf pTau kF) (fun i => (Zf i).toShadedBody)
  middle_fullness : ShadedBody.fullness sm (fun k => (Zm k).toShadedBody) <=
    ShadedBody.fullness (fibre sm pTheta lM) (fun k => (Zm k).toShadedBody)
  card_product : ((fibre sf pTau kF).card : ENNReal) *
      ((fibre sm pTheta lM).card : ENNReal) * (tc.card : ENNReal) <=
    4 * (s.card : ENNReal)
  product : ShadedBody.multiplicity s (fun i => (T i).toShadedBody) <=
    (4 * (M : ENNReal)) *
      (factorTwoScales.C s.card delta uCell.card tau : ENNReal) *
      ShadedBody.multiplicity tc (fun j => (Zc j).toShadedBody) *
      ShadedBody.multiplicity (fibre sm pTheta lM)
        (fun j => (Zm j).toShadedBody) *
      ShadedBody.multiplicity (fibre sf pTau kF)
        (fun i => (Zf i).toShadedBody)

omit [MeasurableSpace E] [BorelSpace E] in
/-- Every node of a nonempty uniform hierarchy carries a leaf. -/
theorem raw_nodes_carry_leaf_upstream_w50 [Nontrivial E]
    {iota : Type u} {delta : NNReal} {s : Finset iota}
    {T : iota -> Tube delta E} {N : Nat} {C : NNReal}
    (U : Tube.UniformTubeSet s T N C) {k : Nat} (hk : k <= N)
    (hs : s.Nonempty) :
    ∀ j ∈ U.cover.indexSet k, ∃ i ∈ s, U.cover.assign k i = j := by
  intro j hj
  obtain ⟨i, hi⟩ := MultiScaleFac.coverClass_nonempty_of_mem_parent U hk hs hj
  have hi' : i ∈ s ∧ U.cover.assign k i = j := by
    simpa [Tube.coverClass] using hi
  exact ⟨i, hi'.1, hi'.2⟩

/-- Counted two-level skeleton with both body representative maps retained. -/
theorem exists_blockSkeleton_counted_upstream_w50 [Nontrivial E]
    {iota : Type u} [DecidableEq iota] {delta : NNReal}
    {s : Finset iota} {T : iota -> Tube delta E} {N a b : Nat} {C : NNReal}
    (U : Tube.UniformTubeSet s T N C) (hab : a <= b) (hb : b <= N)
    (hs : s.Nonempty) :
    ∃ (tTau tTheta : Finset iota)
      (pTau pTheta repTau repTheta pTheta0 : iota -> iota),
      tTau ⊆ U.cover.indexSet b ∧
      tTheta ⊆ U.cover.indexSet a ∧
      (∀ i, pTau i ∈ tTau) ∧
      (∀ k, pTheta k ∈ tTheta) ∧
      (∀ i ∈ s, pTau i = repTau (U.cover.assign b i)) ∧
      (∀ j ∈ U.cover.indexSet b,
        repTau j ∈ tTau ∧
          (U.cover.tube b (repTau j)).toConvexSpaceBody =
            (U.cover.tube b j).toConvexSpaceBody) ∧
      (∀ j' ∈ tTau, ∃ j ∈ U.cover.indexSet b, repTau j = j') ∧
      (∀ i ∈ s,
        (U.cover.tube b (pTau i)).toConvexSpaceBody =
          (U.cover.tube b (U.cover.assign b i)).toConvexSpaceBody) ∧
      (∀ i ∈ s, pTheta0 (U.cover.assign b i) = U.cover.assign a i) ∧
      (∀ k ∈ U.cover.indexSet b, pTheta0 k ∈ U.cover.indexSet a) ∧
      (∀ k ∈ U.cover.indexSet b,
        (U.cover.tube b k).toConvexSpaceBody <=
          (U.cover.tube a (pTheta0 k)).toConvexSpaceBody) ∧
      (∀ k ∈ tTau, pTheta k = repTheta (pTheta0 k)) ∧
      (∀ l ∈ U.cover.indexSet a,
        repTheta l ∈ tTheta ∧
          (U.cover.tube a (repTheta l)).toConvexSpaceBody =
            (U.cover.tube a l).toConvexSpaceBody) ∧
      (∀ l' ∈ tTheta, ∃ l ∈ U.cover.indexSet a, repTheta l = l') ∧
      (∀ k ∈ tTau,
        (U.cover.tube a (pTheta k)).toConvexSpaceBody =
          (U.cover.tube a (pTheta0 k)).toConvexSpaceBody) ∧
      IsParentFamily s T tTau (U.cover.tube b) pTau ∧
      IsParentFamily tTau (U.cover.tube b) tTheta (U.cover.tube a) pTheta := by
  classical
  obtain ⟨i0, hi0⟩ := hs
  have hbNe : (U.cover.indexSet b).Nonempty :=
    ⟨U.cover.assign b i0, U.cover.assign_mem b hb i0 hi0⟩
  obtain ⟨tTau, pTau, repTau, htTau, hpTau, hpTauRep,
      hrepTau, hontoTau, hpTauBody, hparentFine⟩ :=
    exists_dedupParentFamily_counted_upstream_w50
      (V := T) (W := U.cover.tube b) (p := U.cover.assign b)
      hbNe (U.cover.assign_mem b hb) (U.cover.le_tube_assign b hb)
  have hcarry : ∀ k ∈ U.cover.indexSet b,
      ∃ i ∈ s, U.cover.assign b i = k :=
    raw_nodes_carry_leaf_upstream_w50 U hb ⟨i0, hi0⟩
  obtain ⟨pTheta0, hcompTheta, hpTheta0, hleTheta0⟩ :=
    exists_coarseNodeMap U hab hb (U.cover.indexSet b) hcarry
  have haN : a <= N := hab.trans hb
  have haNe : (U.cover.indexSet a).Nonempty :=
    ⟨U.cover.assign a i0, U.cover.assign_mem a haN i0 hi0⟩
  obtain ⟨tTheta, pTheta, repTheta, htTheta, hpTheta, hpThetaRep,
      hrepTheta, hontoTheta, hpThetaBody, hparentTheta⟩ :=
    exists_dedupParentFamily_counted_upstream_w50
      (s := tTau) (V := U.cover.tube b) (t := U.cover.indexSet a)
      (W := U.cover.tube a) (p := pTheta0) haNe
      (fun k hk => hpTheta0 k (htTau hk))
      (fun k hk => hleTheta0 k (htTau hk))
  exact ⟨tTau, tTheta, pTau, pTheta, repTau, repTheta, pTheta0,
    htTau, htTheta, hpTau, hpTheta, hpTauRep, hrepTau, hontoTau,
    hpTauBody, hcompTheta, hpTheta0, hleTheta0, hpThetaRep,
    hrepTheta, hontoTheta, hpThetaBody, hparentFine, hparentTheta⟩

omit [MeasurableSpace E] [BorelSpace E] in
/-- A fibre of any genuine parent family injects by inclusion into the corresponding
containment family.  This is the fine-fibre comparison used after deduplication. -/
theorem fibre_subset_familyIn_of_parentFamily_upstream_w50 {ι κ : Type*} [DecidableEq κ]
    {σ ρ : NNReal} {s : Finset ι} {V : ι → Tube σ E}
    {t : Finset κ} {W : κ → Tube ρ E} {p : ι → κ}
    (hparent : IsParentFamily s V t W p) (k : κ) :
    fibre s p k ⊆
      Kakeya.familyIn s (fun i => (V i).toConvexSpaceBody) (W k).toConvexSpaceBody := by
  classical
  intro i hi
  have hi' : i ∈ s ∧ p i = k := by
    simpa [fibre, Finset.mem_filter] using hi
  simp only [Kakeya.familyIn, Finset.mem_filter]
  exact ⟨hi'.1, by simpa [hi'.2] using hparent.le_parent i hi'.1⟩

omit [MeasurableSpace E] [BorelSpace E] in
/-- The corresponding explicit cardinal bridge for a fine fibre. -/
theorem fibre_card_le_familyIn_of_parentFamily_upstream_w50 {ι κ : Type*} [DecidableEq κ]
    {σ ρ : NNReal} {s : Finset ι} {V : ι → Tube σ E}
    {t : Finset κ} {W : κ → Tube ρ E} {p : ι → κ}
    (hparent : IsParentFamily s V t W p) (k : κ) :
    (fibre s p k).card ≤
      (Kakeya.familyIn s (fun i => (V i).toConvexSpaceBody)
        (W k).toConvexSpaceBody).card := by
  exact Finset.card_le_card (fibre_subset_familyIn_of_parentFamily_upstream_w50 hparent k)

omit [MeasurableSpace E] [BorelSpace E] in
/-- A fibre of the deduplicated middle parent map injects by inclusion into the original
full-hierarchy body class `nodesIn`.  The deduplicated map need not equal the hierarchy's
assignment map. -/
theorem dedup_middle_fibre_subset_nodesIn_upstream_w50
    {ι : Type*} [Nontrivial E] [DecidableEq ι] {δ : NNReal}
    {s' : Finset ι} {T : ι → Tube δ E} {N a b : ℕ} {C : NNReal}
    (U : Tube.UniformTubeSet s' T N C)
    {tτ tθ : Finset ι} {pθ : ι → ι}
    (htτ : tτ ⊆ U.cover.indexSet b)
    (hparent : IsParentFamily tτ (U.cover.tube b) tθ (U.cover.tube a) pθ)
    (l : ι) :
    fibre tτ pθ l ⊆ U.nodesIn b (U.cover.tube a l).toConvexSpaceBody := by
  classical
  intro k hk
  have hk' : k ∈ tτ ∧ pθ k = l := by
    simpa [fibre, Finset.mem_filter] using hk
  rw [Tube.UniformTubeSet.mem_nodesIn_iff]
  exact ⟨htτ hk'.1, by simpa [hk'.2] using hparent.le_parent k hk'.1⟩

omit [MeasurableSpace E] [BorelSpace E] in
/-- The corresponding explicit cardinal bridge for a deduplicated middle fibre. -/
theorem dedup_middle_fibre_card_le_nodesIn_upstream_w50
    {ι : Type*} [Nontrivial E] [DecidableEq ι] {δ : NNReal}
    {s' : Finset ι} {T : ι → Tube δ E} {N a b : ℕ} {C : NNReal}
    (U : Tube.UniformTubeSet s' T N C)
    {tτ tθ : Finset ι} {pθ : ι → ι}
    (htτ : tτ ⊆ U.cover.indexSet b)
    (hparent : IsParentFamily tτ (U.cover.tube b) tθ (U.cover.tube a) pθ)
    (l : ι) :
    (fibre tτ pθ l).card ≤
      (U.nodesIn b (U.cover.tube a l).toConvexSpaceBody).card := by
  exact Finset.card_le_card (dedup_middle_fibre_subset_nodesIn_upstream_w50 U htτ hparent l)

/-! ## The B3 count on a deduplicated fixed skeleton -/


/-- The selected three B3 carriers on a deduplicated hierarchy skeleton satisfy the fixed
polynomial branch bound `C^6 |s'|`.

The three payments are respectively `C^2 N_b`, `C^3 N_a / N_b`, and
`C |s'| / N_a`; the proof stays division-free. -/
theorem b3_branch_card_of_dedup_hierarchy_upstream_w50 [Nontrivial E]
    {ι : Type*} [DecidableEq ι] {δ : NNReal}
    {s' : Finset ι} {V : ι → ShadedTube δ E} {N a b : ℕ} {C : NNReal}
    (U : Tube.UniformTubeSet s' (fun i => (V i).toTube) N C)
    (hab : a ≤ b) (hb : b ≤ N)
    {tτ tθ : Finset ι} {pτ pθ : ι → ι}
    (htτ : tτ ⊆ U.cover.indexSet b) (htθ : tθ ⊆ U.cover.indexSet a)
    (hparentFine : IsParentFamily s' (fun i => (V i).toTube)
      tτ (U.cover.tube b) pτ)
    (hparentCoarse : IsParentFamily tτ (U.cover.tube b)
      tθ (U.cover.tube a) pθ)
    {kF lM : ι} (hkF : kF ∈ tτ) (hlM : lM ∈ tθ)
    {tθAct : Finset ι} (htθAct : tθAct ⊆ tθ) :
    ((fibre s' pτ kF).card : ENNReal) *
        ((fibre tτ pθ lM).card : ENNReal) *
        (tθAct.card : ENNReal)
      ≤ (C : ENNReal) ^ 6 * (s'.card : ENNReal) := by
  classical
  let Nb : NNReal := U.branchingN b
  let Na : NNReal := U.branchingN a
  let P1 : NNReal := (fibre s' pτ kF).card
  let P2 : NNReal := (fibre tτ pθ lM).card
  let P3 : NNReal := tθAct.card
  have haN : a ≤ N := hab.trans hb
  have hkFnode : kF ∈ U.cover.indexSet b := htτ hkF
  have hlMnode : lM ∈ U.cover.indexSet a := htθ hlM
  have hP1 : P1 ≤ C ^ 2 * Nb := by
    have hsub := fibre_subset_familyIn_of_parentFamily_upstream_w50 hparentFine kF
    have hcard : P1 ≤
        ((Kakeya.familyIn s' (fun i => ((V i).toTube).toConvexSpaceBody)
          (U.cover.tube b kF).toConvexSpaceBody).card : NNReal) := by
      dsimp only [P1]
      exact_mod_cast Finset.card_le_card hsub
    exact hcard.trans (U.card_familyIn_le hb kF)
  have hP2R : (Nb : ℝ) * (P2 : ℝ) ≤ (C : ℝ) ^ 3 * (Na : ℝ) := by
    have hsub := dedup_middle_fibre_subset_nodesIn_upstream_w50 U htτ hparentCoarse lM
    have hcard : (P2 : ℝ) ≤
        ((U.nodesIn b (U.cover.tube a lM).toConvexSpaceBody).card : ℝ) := by
      dsimp only [P2]
      exact_mod_cast Finset.card_le_card hsub
    calc
      (Nb : ℝ) * (P2 : ℝ) ≤
          (Nb : ℝ) *
            ((U.nodesIn b (U.cover.tube a lM).toConvexSpaceBody).card : ℝ) := by
              gcongr
      _ ≤ (C : ℝ) ^ 3 * (Na : ℝ) := by
        simpa [Nb, Na] using branching_mul_card_nodesIn_le U hab hb lM
  have hP2 : Nb * P2 ≤ C ^ 3 * Na := by
    exact_mod_cast hP2R
  have hP3 : Na * P3 ≤ C * (s'.card : NNReal) := by
    have hcard : P3 ≤ ((U.cover.indexSet a).card : NNReal) := by
      dsimp only [P3]
      exact_mod_cast Finset.card_le_card (htθAct.trans htθ)
    calc
      Na * P3 ≤ Na * ((U.cover.indexSet a).card : NNReal) := by gcongr
      _ ≤ C * (s'.card : NNReal) := by
        simpa [Na] using branchingN_mul_card_indexSet_le U haN
  have hP1E : (P1 : ENNReal) ≤ (C : ENNReal) ^ 2 * (Nb : ENNReal) := by
    exact_mod_cast hP1
  have hP2E : (Nb : ENNReal) * (P2 : ENNReal) ≤
      (C : ENNReal) ^ 3 * (Na : ENNReal) := by
    exact_mod_cast hP2
  have hP3E : (Na : ENNReal) * (P3 : ENNReal) ≤
      (C : ENNReal) * (s'.card : ENNReal) := by
    exact_mod_cast hP3
  change (P1 : ENNReal) * (P2 : ENNReal) * (P3 : ENNReal) ≤ _
  calc
    (P1 : ENNReal) * (P2 : ENNReal) * (P3 : ENNReal)
        ≤ ((C : ENNReal) ^ 2 * (Nb : ENNReal)) *
            (P2 : ENNReal) * (P3 : ENNReal) := by gcongr
    _ = (C : ENNReal) ^ 2 * ((Nb : ENNReal) * (P2 : ENNReal)) *
          (P3 : ENNReal) := by ring
    _ ≤ (C : ENNReal) ^ 2 * ((C : ENNReal) ^ 3 * (Na : ENNReal)) *
          (P3 : ENNReal) := by gcongr
    _ = (C : ENNReal) ^ 5 * ((Na : ENNReal) * (P3 : ENNReal)) := by ring
    _ ≤ (C : ENNReal) ^ 5 * ((C : ENNReal) * (s'.card : ENNReal)) := by gcongr
    _ = (C : ENNReal) ^ 6 * (s'.card : ENNReal) := by ring

/-- Raw dividing-block inputs produce a counted, same-witness product-only packet using only
modules which can be imported before `CaseTwo`. -/
theorem exists_caseTwoDirectFactors_counted_raw_block_upstream_w50 [Nontrivial E]
    (hdim : Module.finrank Real E = 3)
    {beta gamma0 : Real} {p : Params} (hspec : p.Spec beta gamma0)
    (Cd : NNReal) (Kd cd : Nat) :
    ∃ M : Nat, 0 < M ∧
      ∀ᶠ (delta : NNReal) in nhdsWithin 0 (Set.Ioi 0),
        ∀ {iota : Type u} [DecidableEq iota]
          (s s2 sPrime : Finset iota) (V : iota -> ShadedTube delta E)
          (U : Tube.UniformTubeSet sPrime (fun i => (V i).toTube)
            (Tube.ssfGridLen delta) Cd)
          (a b m : Nat),
          (∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 1) ->
          s2 ⊆ s -> sPrime ⊆ s2 -> sPrime.Nonempty ->
          (∀ t ⊆ s2, t.Nonempty ->
            (delta : ENNReal) ^ p.η 0 <=
              (ShadedBody.fullness t (fun i => (V i).toShadedBody) : ENNReal)) ->
          StickyKakeya.IsFrostmanDividingBlock U Cd Kd cd
            p.η p.ε a b m p.N ->
          ∃ (tTau tTheta : Finset iota)
            (pTau pTheta repTau repTheta pTheta0 : iota -> iota)
            (tm sf : Finset iota)
            (ZTau : iota -> ShadedTube
              (Tube.gridScale delta (Tube.ssfGridLen delta) b) E)
            (Zf : iota -> ShadedTube delta E)
            (uCell : Finset iota) (v0 : E) (tc sm : Finset iota)
            (Zc : iota -> ShadedTube
              (Tube.gridScale delta (Tube.ssfGridLen delta) a) E)
            (Zm : iota -> ShadedTube
              (Tube.gridScale delta (Tube.ssfGridLen delta) b) E)
            (kF lM : iota),
            tTau ⊆ U.cover.indexSet b ∧
            tTheta ⊆ U.cover.indexSet a ∧
            (∀ i, pTau i ∈ tTau) ∧
            (∀ k, pTheta k ∈ tTheta) ∧
            (∀ i ∈ sPrime,
              pTau i = repTau (U.cover.assign b i)) ∧
            (∀ j ∈ U.cover.indexSet b,
              repTau j ∈ tTau ∧
                (U.cover.tube b (repTau j)).toConvexSpaceBody =
                  (U.cover.tube b j).toConvexSpaceBody) ∧
            (∀ j' ∈ tTau,
              ∃ j ∈ U.cover.indexSet b, repTau j = j') ∧
            (∀ i ∈ sPrime,
              (U.cover.tube b (pTau i)).toConvexSpaceBody =
                (U.cover.tube b (U.cover.assign b i)).toConvexSpaceBody) ∧
            (∀ i ∈ sPrime,
              pTheta0 (U.cover.assign b i) = U.cover.assign a i) ∧
            (∀ k ∈ U.cover.indexSet b,
              pTheta0 k ∈ U.cover.indexSet a) ∧
            (∀ k ∈ U.cover.indexSet b,
              (U.cover.tube b k).toConvexSpaceBody <=
                (U.cover.tube a (pTheta0 k)).toConvexSpaceBody) ∧
            (∀ k ∈ tTau, pTheta k = repTheta (pTheta0 k)) ∧
            (∀ l ∈ U.cover.indexSet a,
              repTheta l ∈ tTheta ∧
                (U.cover.tube a (repTheta l)).toConvexSpaceBody =
                  (U.cover.tube a l).toConvexSpaceBody) ∧
            (∀ l' ∈ tTheta,
              ∃ l ∈ U.cover.indexSet a, repTheta l = l') ∧
            (∀ k ∈ tTau,
              (U.cover.tube a (pTheta k)).toConvexSpaceBody =
                (U.cover.tube a (pTheta0 k)).toConvexSpaceBody) ∧
            IsParentFamily sPrime (fun i => (V i).toTube)
              tTau (U.cover.tube b) pTau ∧
            IsParentFamily tTau (U.cover.tube b)
              tTheta (U.cover.tube a) pTheta ∧
            IsCaseTwoDirectFactorsUpstreamW50 sPrime V
              tTau (U.cover.tube b) pTau
              tTheta (U.cover.tube a) pTheta
              M tm sf ZTau Zf uCell v0 tc sm Zc Zm kF lM := by
  obtain ⟨M, hM, hproduct⟩ :=
    exists_twoScaleProductOnly_ball_rich_w49 (E := E) 4 (by norm_num) hdim
  refine ⟨M, hM, ?_⟩
  filter_upwards [eventually_rpow_le_quarter hspec.epsPos,
      eventually_le_one_nhdsGT, self_mem_nhdsWithin]
    with delta hsmall hdelta1 hdelta0
  intro iota _ s s2 sPrime V U a b m hball hs2s hsPrimeSub hsPrimeNe hhered hblock
  have hballPrime : ∀ i ∈ sPrime,
      (V i).carrier ⊆ Metric.closedBall (0 : E) 1 := by
    intro i hi
    exact hball i (hs2s (hsPrimeSub hi))
  have hfullPrime : (delta : ENNReal) ^ p.η 0 <=
      (ShadedBody.fullness sPrime (fun i => (V i).toShadedBody) : ENNReal) :=
    hhered sPrime hsPrimeSub hsPrimeNe
  have hmass : 0 < ∑ i ∈ sPrime, volume (V i).shade :=
    sum_shade_pos_of_fullness_ge hdelta0 V hfullPrime
  have hscales := caseTwoThreePassScales hdelta1 U
    hblock.coarse_lt_fine.le hblock.fine_le
  have hdeltaTau : delta <= Tube.gridScale delta (Tube.ssfGridLen delta) b :=
    hscales.1.1
  have hTauTheta : Tube.gridScale delta (Tube.ssfGridLen delta) b <=
      Tube.gridScale delta (Tube.ssfGridLen delta) a := hscales.1.2.1
  have hThetaOne : Tube.gridScale delta (Tube.ssfGridLen delta) a <= 1 :=
    hscales.1.2.2
  have hsep : Tube.gridScale delta (Tube.ssfGridLen delta) b <=
      delta ^ p.ε * Tube.gridScale delta (Tube.ssfGridLen delta) a := by
    exact NNReal.coe_le_coe.mp (by
      rw [NNReal.coe_mul, NNReal.coe_rpow]
      exact hblock.separated)
  have hTauQuarter : Tube.gridScale delta (Tube.ssfGridLen delta) b <=
      (1 / 4 : NNReal) := by
    calc
      Tube.gridScale delta (Tube.ssfGridLen delta) b <=
          delta ^ p.ε * Tube.gridScale delta (Tube.ssfGridLen delta) a := hsep
      _ <= delta ^ p.ε * 1 := by gcongr
      _ = delta ^ p.ε := by rw [mul_one]
      _ <= (1 / 4 : NNReal) := by exact_mod_cast hsmall.2
  have hTauQuarterReal :
      ((Tube.gridScale delta (Tube.ssfGridLen delta) b : NNReal) : Real) <=
        1 / 4 := by
    exact_mod_cast hTauQuarter
  obtain ⟨tTau, tTheta, pTau, pTheta, repTau, repTheta, pTheta0,
      htTau, htTheta, hpTau, hpTheta, hpTauRep, hrepTau, hontoTau,
      hpTauBody, hcompTheta, hpTheta0, hleTheta0, hpThetaRep,
      hrepTheta, hontoTheta, hpThetaBody, hparentFine, hparentTheta⟩ :=
    exists_blockSkeleton_counted_upstream_w50 U hblock.coarse_lt_fine.le
      hblock.fine_le hsPrimeNe
  have hballTau : ∀ k ∈ tTau,
      (U.cover.tube b k).carrier ⊆ Metric.closedBall (0 : E) 4 := by
    intro k hk
    exact MultiScaleFac.node_carrier_subset_ball hdelta0 hsmall.1 U hsPrimeNe
      hballPrime hblock.fine_le (htTau hk)
  obtain ⟨tm, sf, ZTau, Zf, uCell, v0, tc, sm, Zc, Zm, kF, lM,
      _htmNe, _huNe, htcNe, hkF, hlM, htm, hsf, hu, hsm, htc,
      hsfMaps, htmFibreNe, hfineCard, hsmMaps, htcFibreNe, hmiddleCard,
      _hmassFine, _hmassMiddle, hZTau, hZf, hZc, hZm, hmiddleBall,
      hcellFullness, hcellMass, houterFullness, hrefFine, hcoarseFullness,
      hrefMiddle, hfineFullness, hmiddleFullness, hcardProduct, hproductOut⟩ :=
    hproduct hdelta0 hdeltaTau hTauTheta hThetaOne hTauQuarterReal
      V (U.cover.tube b) pTau (U.cover.tube a) pTheta
      hballPrime hparentFine hmass hballTau hparentTheta
  refine ⟨tTau, tTheta, pTau, pTheta, repTau, repTheta, pTheta0,
    tm, sf, ZTau, Zf, uCell, v0, tc, sm, Zc, Zm, kF, lM,
    htTau, htTheta, hpTau, hpTheta, hpTauRep, hrepTau, hontoTau,
    hpTauBody, hcompTheta, hpTheta0, hleTheta0, hpThetaRep,
    hrepTheta, hontoTheta, hpThetaBody, hparentFine, hparentTheta, ?_⟩
  exact
    { fine_nonempty := htmFibreNe kF hkF
      middle_nonempty := htcFibreNe lM hlM
      coarse_nonempty := htcNe
      mid_subset := htm
      fine_subset := hsf
      cell_subset := hu
      middle_subset := hsm
      coarse_subset := htc
      fine_mem := hkF
      middle_mem := hlM
      fine_maps := hsfMaps
      fine_card_band := hfineCard
      middle_maps := hsmMaps
      middle_card_band := hmiddleCard
      fine_tube := hZf
      outer_tube := hZTau
      coarse_tube := hZc
      middle_tube := hZm
      middle_ball := hmiddleBall
      cell_fullness := hcellFullness
      cell_mass := hcellMass
      outer_fullness := houterFullness
      fine_refinement := hrefFine
      coarse_fullness := hcoarseFullness
      middle_refinement := hrefMiddle
      fine_fullness := hfineFullness
      middle_fullness := hmiddleFullness
      card_product := hcardProduct kF hkF lM hlM
      product := hproductOut kF hkF lM hlM }

#print axioms raw_nodes_carry_leaf_upstream_w50
#print axioms exists_blockSkeleton_counted_upstream_w50
#print axioms b3_branch_card_of_dedup_hierarchy_upstream_w50
#print axioms exists_caseTwoDirectFactors_counted_raw_block_upstream_w50

end
end Kakeya.ml1Boot.W50Upstream
