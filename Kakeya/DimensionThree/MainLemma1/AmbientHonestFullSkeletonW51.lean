module

public import Kakeya.DimensionThree.MainLemma1.CountedHonestTwoScaleAdapterW50

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology
open scoped NNReal ENNReal

namespace Kakeya.ml1Boot.W51AmbientHonestFullSkeleton

noncomputable section
set_option maxHeartbeats 18000000

universe u

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]

/-!
The selected first-scale parent set may be a strict subset of the fixed middle
skeleton.  This adapter retains that fixed skeleton in `IsTwoScaleFactors`.
The honest fine shading is zero-extended on the full middle fibre, while the
first-scale selected shading remains exactly the `h1` witness.  Thus the
second product can be performed on a retained source without changing either
selected witness or paying an ambient cardinality bridge.
-/
theorem exists_isTwoScaleFactors_of_countedHonestProduct_fullSkeleton_w51
    {iota kappa : Type u} [DecidableEq iota] [DecidableEq kappa]
    {delta tau theta c : NNReal}
    {c1 L1 Lreg Lcard : ENNReal}
    {amb act act' : Finset iota} {V Z' : iota -> ShadedTube delta E}
    {tTauOld tAct1 : Finset kappa} {VTau : kappa -> Tube tau E}
    {pTau : iota -> kappa} {ZTau : kappa -> ShadedTube tau E}
    {kF : kappa} {lamP1 lamF : NNReal}
    {F : ShadedBody.FactorFamily E kappa kappa}
    {T : kappa -> ShadedTube tau E} {TTheta : kappa -> Tube theta E}
    {fineSet coarseSet : Finset kappa}
    {fineShade : kappa -> ShadedTube tau E}
    {coarseShade : kappa -> ShadedTube theta E}
    {parent : kappa -> kappa} {productConstant branchN : NNReal}
    (h1 : IsOneScaleSelected c1 L1 amb act V tTauOld VTau pTau
      act' Z' tAct1 ZTau kF lamP1 lamF)
    (hskFine : forall i, i ∈ amb -> pTau i ∈ tTauOld)
    (hactiveSub : tAct1 ⊆ tTauOld)
    (hinnerSub : F.innerSet ⊆ tAct1)
    (hskMiddle : forall k, k ∈ tTauOld -> F.parent k ∈ F.outerSet)
    (hOut : Kakeya.ml1CoarseHonestW45.HonestDilateProductOutput
      (c := c) F T TTheta fineSet coarseSet fineShade coarseShade parent
        productConstant)
    (hTtube : forall k, k ∈ fineSet ->
      (fineShade k).toTube = VTau k)
    (hcoarseED : (coarseSet : Set kappa).Pairwise fun q q' =>
      IsEssentiallyDistinct (coarseShade q).carrier (coarseShade q').carrier)
    (hproductConstant : 0 < productConstant) (hbranchN : 0 < branchN)
    (hsourceMass : 0 < ∑ k ∈ F.innerSet, volume (F.innerBody k).shade)
    {deltaBand : NNReal} (hdeltaBand1 : deltaBand <= 1)
    {epsBand : Real} (hepsBand : 0 <= epsBand)
    (hband : forall l, l ∈ F.outerSet ->
      (branchN : ENNReal) <= ((F.fiber l).card : ENNReal) /\
      ((F.fiber l).card : ENNReal) <= 2 * (branchN : ENNReal))
    (hbridge : ShadedBody.multiplicity tAct1
        (fun k => (ZTau k).toShadedBody) <=
      Lreg * ShadedBody.multiplicity F.innerSet F.innerBody)
    (hcard : forall good, good ∈ coarseSet ->
      ((fibre amb pTau kF).card : ENNReal) *
        ((fibre tTauOld F.parent good).card : ENNReal) *
          (coarseSet.card : ENNReal) <= Lcard * (amb.card : ENNReal)) :
    exists good : kappa,
      IsTwoScaleFactors (L1 * Lreg * (productConstant : ENNReal)) Lcard amb V
        tTauOld VTau pTau
        F.outerSet (fun l => Tube.undilateAtZero (c : Real) (TTheta l)) F.parent
        kF (selectedShade act' V Z') lamF
        good (zeroExtend fineSet VTau fineShade) 0
          coarseSet coarseShade 0 /\
      (coarseSet : Set kappa).Pairwise (fun q q' =>
        IsEssentiallyDistinct (coarseShade q).carrier
          (coarseShade q').carrier) := by
  obtain ⟨good, hgood, hgoodFull, hgoodBranch⟩ :=
    hOut.exists_fullness_and_branch_card hproductConstant hsourceMass
      hdeltaBand1 hepsBand hband
  have hparentEq : parent = F.parent := hOut.parent_eq
  have hactiveEq : Kakeya.ml1CoarseHonestW45.activeFibre fineSet parent good = F.fiber good := by
    exact hOut.activeFibre_eq_factorFiber hgood
  have hgoodNe : (fibre tTauOld F.parent good).Nonempty := by
    have hactiveNe :
        (Kakeya.ml1CoarseHonestW45.activeFibre fineSet parent good).Nonempty := by
      have hbranchPos : (0 : ENNReal) < (branchN : ENNReal) := by
        exact_mod_cast hbranchN
      have hcardPos : (0 : ENNReal) <
          ((Kakeya.ml1CoarseHonestW45.activeFibre fineSet parent good).card : ENNReal) :=
        hbranchPos.trans_le hgoodBranch.1
      exact Finset.card_pos.mp (by exact_mod_cast hcardPos)
    have hsub :
        Kakeya.ml1CoarseHonestW45.activeFibre fineSet parent good ⊆
          fibre tTauOld F.parent good := by
      rw [hactiveEq]
      exact (show F.fiber good ⊆ fibre tTauOld F.parent good from by
        intro k hk
        have hk' : k ∈ F.innerSet ∧ F.parent k = good := by
          simpa [ShadedBody.FactorFamily.fiber] using hk
        exact Finset.mem_filter.mpr ⟨hactiveSub (hinnerSub hk'.1), hk'.2⟩)
    exact hactiveNe.mono hsub
  let Ym : kappa -> ShadedTube tau E := zeroExtend fineSet VTau fineShade
  have hYmTube : forall k, (Ym k).toTube = VTau k := by
    intro k
    simpa [Ym] using zeroExtend_toTube hTtube k
  have hYmMult :
      ShadedBody.multiplicity (fibre tTauOld F.parent good)
          (fun k => (Ym k).toShadedBody) =
        ShadedBody.multiplicity
          (Kakeya.ml1CoarseHonestW45.activeFibre fineSet parent good)
            (fun k => (fineShade k).toShadedBody) := by
    have hsub : fibre tTauOld F.parent good ∩ fineSet =
        Kakeya.ml1CoarseHonestW45.activeFibre fineSet parent good := by
      ext k
      simp only [Finset.mem_inter, Kakeya.ml1Boot.fibre, Finset.mem_filter,
        Kakeya.ml1CoarseHonestW45.activeFibre]
      constructor
      · intro hk
        exact ⟨hk.2, by simpa [hparentEq] using hk.1.2⟩
      · intro hk
        exact ⟨⟨hactiveSub (hinnerSub (hOut.fine_subset hk.1)),
          by simpa [hparentEq] using hk.2⟩, hk.1⟩
    rw [multiplicity_zeroExtend]
    rw [hsub]
  have hproduct :
      ShadedBody.multiplicity amb (fun i => (V i).toShadedBody) <=
        (L1 * Lreg * (productConstant : ENNReal)) *
          ShadedBody.multiplicity (fibre amb pTau kF)
            (fun i => (selectedShade act' V Z' i).toShadedBody) *
          ShadedBody.multiplicity (fibre tTauOld F.parent good)
            (fun k => (Ym k).toShadedBody) *
          ShadedBody.multiplicity coarseSet
            (fun l => (coarseShade l).toShadedBody) := by
    calc
      ShadedBody.multiplicity amb (fun i => (V i).toShadedBody)
          <= L1 * ShadedBody.multiplicity tAct1
              (fun k => (ZTau k).toShadedBody) *
            ShadedBody.multiplicity (fibre amb pTau kF)
              (fun i => (selectedShade act' V Z' i).toShadedBody) := h1.sel_scalar
      _ <= L1 * (Lreg * ShadedBody.multiplicity F.innerSet F.innerBody) *
            ShadedBody.multiplicity (fibre amb pTau kF)
              (fun i => (selectedShade act' V Z' i).toShadedBody) := by
        gcongr
      _ <= L1 * (Lreg * ((productConstant : ENNReal) *
              ShadedBody.multiplicity coarseSet
                (fun l => (coarseShade l).toShadedBody) *
              ShadedBody.multiplicity
                (Kakeya.ml1CoarseHonestW45.activeFibre fineSet parent good)
                (fun k => (fineShade k).toShadedBody))) *
            ShadedBody.multiplicity (fibre amb pTau kF)
              (fun i => (selectedShade act' V Z' i).toShadedBody) := by
        gcongr
        exact hOut.product good hgood
      _ = (L1 * Lreg * (productConstant : ENNReal)) *
            ShadedBody.multiplicity (fibre amb pTau kF)
              (fun i => (selectedShade act' V Z' i).toShadedBody) *
            ShadedBody.multiplicity (fibre tTauOld F.parent good)
              (fun k => (Ym k).toShadedBody) *
            ShadedBody.multiplicity coarseSet
              (fun l => (coarseShade l).toShadedBody) := by
        rw [hYmMult]
        ring
  refine ⟨good, ?_, hcoarseED⟩
  refine
    { skeleton_fine := hskFine
      skeleton_mid := hskMiddle
      fine_mem := hactiveSub h1.sel_mem
      fine_nonempty := h1.sel_nonempty
      fine_tube := fun i _ => selectedShade_toTube
        (fun j hj => (h1.child_shade j hj).1) i
      fine_fullness := h1.sel_fullness
      mid_mem := hOut.coarse_subset hgood
      mid_nonempty := hgoodNe
      mid_tube := fun k _ => hYmTube k
      mid_fullness := bot_le
      coarse_subset := hOut.coarse_subset
      coarse_nonempty := hOut.coarse_nonempty
      coarse_tube := fun l _ => hOut.coarse_tube l
      coarse_fullness := bot_le
      branch_card := ?_
      product := hproduct }
  exact hcard good hgood

end
end Kakeya.ml1Boot.W51AmbientHonestFullSkeleton

#print axioms Kakeya.ml1Boot.W51AmbientHonestFullSkeleton.exists_isTwoScaleFactors_of_countedHonestProduct_fullSkeleton_w51

end
