module

public import Kakeya.DimensionThree.MainLemma1.ScalarFactorization
public import Kakeya.Factoring.HonestFibreBridge

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology
open scoped NNReal ENNReal

namespace Kakeya.ml1Boot.W50CountedHonestTwoScaleAdapter

noncomputable section

universe u v w

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]

/-- A common fibre-cardinality band controls the selected middle fibre times
the number of retained coarse parents. -/
theorem activeFibre_card_mul_coarse_le_w50
    {iota : Type v} {kappa : Type w} [DecidableEq kappa]
    {delta theta c : NNReal}
    {F : ShadedBody.FactorFamily E iota kappa}
    {T : iota -> ShadedTube delta E} {TTheta : kappa -> Tube theta E}
    {fineSet : Finset iota} {coarseSet : Finset kappa}
    {fineShade : iota -> ShadedTube delta E}
    {coarseShade : kappa -> ShadedTube theta E}
    {parent : iota -> kappa} {productConstant branchN : NNReal}
    (hOut : Kakeya.ml1CoarseHonestW45.HonestDilateProductOutput
      (c := c) F T TTheta fineSet coarseSet fineShade coarseShade parent
        productConstant)
    (hband : forall l, l ∈ F.outerSet ->
      (branchN : ENNReal) <= ((F.fiber l).card : ENNReal) /\
      ((F.fiber l).card : ENNReal) <= 2 * (branchN : ENNReal))
    (l : kappa) (hl : l ∈ coarseSet) :
    ((Kakeya.ml1CoarseHonestW45.activeFibre fineSet parent l).card : ENNReal) *
        (coarseSet.card : ENNReal) <=
      2 * (F.innerSet.card : ENNReal) := by
  classical
  have hmaps : (F.innerSet : Set iota).MapsTo F.parent (F.outerSet : Set kappa) := by
    intro i hi
    exact F.parent_mem i hi
  have hcardSum : (F.innerSet.card : ENNReal) =
      ∑ q ∈ F.outerSet, ((F.fiber q).card : ENNReal) := by
    calc
      (F.innerSet.card : ENNReal) =
          ∑ q ∈ F.outerSet,
            ((F.innerSet.filter fun i => F.parent i = q).card : ENNReal) := by
              rw [← Nat.cast_sum]
              congr 1
              exact Finset.card_eq_sum_card_fiberwise hmaps
      _ = ∑ q ∈ F.outerSet, ((F.fiber q).card : ENNReal) := by
        apply Finset.sum_congr rfl
        intro q _
        have hset : F.innerSet.filter (fun i => F.parent i = q) = F.fiber q := by
          ext i
          simp only [ShadedBody.FactorFamily.fiber, Finset.mem_filter]
        rw [hset]
  have hcoarseN : (coarseSet.card : ENNReal) * (branchN : ENNReal) <=
      (F.innerSet.card : ENNReal) := by
    calc
      (coarseSet.card : ENNReal) * (branchN : ENNReal) =
          ∑ q ∈ coarseSet, (branchN : ENNReal) := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ <= ∑ q ∈ coarseSet, ((F.fiber q).card : ENNReal) :=
        Finset.sum_le_sum (fun q hq => (hband q (hOut.coarse_subset hq)).1)
      _ <= ∑ q ∈ F.outerSet, ((F.fiber q).card : ENNReal) :=
        Finset.sum_le_sum_of_subset_of_nonneg hOut.coarse_subset
          (fun _ _ _ => bot_le)
      _ = (F.innerSet.card : ENNReal) := hcardSum.symm
  have hactiveLe :
      ((Kakeya.ml1CoarseHonestW45.activeFibre fineSet parent l).card : ENNReal) <=
        2 * (branchN : ENNReal) := by
    rw [hOut.activeFibre_eq_factorFiber hl]
    exact (hband l (hOut.coarse_subset hl)).2
  calc
    ((Kakeya.ml1CoarseHonestW45.activeFibre fineSet parent l).card : ENNReal) *
          (coarseSet.card : ENNReal)
        <= (2 * (branchN : ENNReal)) * (coarseSet.card : ENNReal) := by gcongr
    _ = 2 * ((coarseSet.card : ENNReal) * (branchN : ENNReal)) := by ring
    _ <= 2 * (F.innerSet.card : ENNReal) := by gcongr

/-- Assemble the first one-scale factor with the final honest counted coarse
product.  The coarse family in the returned `IsTwoScaleFactors` is literally
the pairwise-ED family in `hcoarseED`; it is never selected after the product. -/
theorem exists_isTwoScaleFactors_of_countedHonestProduct_w50
    {iota : Type v} {kappa : Type w}
    [DecidableEq iota] [DecidableEq kappa]
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
    (hskFine : forall i, pTau i ∈ F.innerSet)
    (hOut : Kakeya.ml1CoarseHonestW45.HonestDilateProductOutput
      (c := c) F T TTheta fineSet coarseSet fineShade coarseShade parent
        productConstant)
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
    (hcard : ((fibre amb pTau kF).card : ENNReal) *
        (2 * (F.innerSet.card : ENNReal)) <=
      Lcard * (amb.card : ENNReal)) :
    exists good : kappa,
      IsTwoScaleFactors (L1 * Lreg * (productConstant : ENNReal)) Lcard amb V
        F.innerSet (fun k => (T k).toTube) pTau
        F.outerSet (fun l => Tube.undilateAtZero (c : Real) (TTheta l)) parent
        kF (selectedShade act' V Z') lamF
        good fineShade
          (ShadedBody.fullness fineSet (fun k => (fineShade k).toShadedBody))
        coarseSet coarseShade
          (productConstant⁻¹ * ShadedBody.fullness F.innerSet F.innerBody) /\
      (coarseSet : Set kappa).Pairwise (fun q q' =>
        IsEssentiallyDistinct (coarseShade q).carrier
          (coarseShade q').carrier) := by
  classical
  obtain ⟨good, hgood, hgoodFull, hgoodBranch⟩ :=
    hOut.exists_fullness_and_branch_card hproductConstant hsourceMass
      hdeltaBand1 hepsBand hband
  have hfibre : fibre F.innerSet parent good =
      Kakeya.ml1CoarseHonestW45.activeFibre fineSet parent good := by
    rw [hOut.activeFibre_eq_factorFiber hgood]
    ext k
    simp only [fibre, ShadedBody.FactorFamily.fiber, Finset.mem_filter]
    simpa [hOut.parent_eq]
  have hgoodNe :
      (Kakeya.ml1CoarseHonestW45.activeFibre fineSet parent good).Nonempty := by
    have hbranchPos : (0 : ENNReal) < (branchN : ENNReal) := by
      exact_mod_cast hbranchN
    have hcardPos : (0 : ENNReal) <
        ((Kakeya.ml1CoarseHonestW45.activeFibre fineSet parent good).card : ENNReal) :=
      hbranchPos.trans_le hgoodBranch.1
    exact Finset.card_pos.mp (by exact_mod_cast hcardPos)
  have hgoodCard := activeFibre_card_mul_coarse_le_w50 hOut hband good hgood
  have hkF : kF ∈ F.innerSet := by
    obtain ⟨i, hi⟩ := h1.sel_nonempty
    have hip : pTau i = kF := (Finset.mem_filter.mp hi).2
    rw [← hip]
    exact hskFine i
  refine ⟨good, ?_, hcoarseED⟩
  refine
    { skeleton_fine := fun i _ => hskFine i
      skeleton_mid := ?_
      fine_mem := hkF
      fine_nonempty := h1.sel_nonempty
      fine_tube := fun i _ => selectedShade_toTube
        (fun j hj => (h1.child_shade j hj).1) i
      fine_fullness := h1.sel_fullness
      mid_mem := hOut.coarse_subset hgood
      mid_nonempty := by rw [hfibre]; exact hgoodNe
      mid_tube := fun k _ => hOut.fine_tube k
      mid_fullness := by rw [hfibre]; exact hgoodFull
      coarse_subset := hOut.coarse_subset
      coarse_nonempty := hOut.coarse_nonempty
      coarse_tube := fun l _ => hOut.coarse_tube l
      coarse_fullness := by exact_mod_cast hOut.coarse_fullness
      branch_card := ?_
      product := ?_ }
  · intro k hk
    rw [hOut.parent_eq]
    exact F.parent_mem k hk
  · rw [hfibre]
    calc
      ((fibre amb pTau kF).card : ENNReal) *
            ((Kakeya.ml1CoarseHonestW45.activeFibre fineSet parent good).card : ENNReal) *
            (coarseSet.card : ENNReal)
          = ((fibre amb pTau kF).card : ENNReal) *
              (((Kakeya.ml1CoarseHonestW45.activeFibre fineSet parent good).card : ENNReal) *
                (coarseSet.card : ENNReal)) := by ring
      _ <= ((fibre amb pTau kF).card : ENNReal) *
            (2 * (F.innerSet.card : ENNReal)) := by gcongr
      _ <= Lcard * (amb.card : ENNReal) := hcard
  · calc
      ShadedBody.multiplicity amb (fun i => (V i).toShadedBody)
          <= L1 * ShadedBody.multiplicity tAct1
              (fun k => (ZTau k).toShadedBody) *
            ShadedBody.multiplicity (fibre amb pTau kF)
              (fun i => (selectedShade act' V Z' i).toShadedBody) := h1.sel_scalar
      _ <= L1 * (Lreg * ShadedBody.multiplicity F.innerSet F.innerBody) *
            ShadedBody.multiplicity (fibre amb pTau kF)
              (fun i => (selectedShade act' V Z' i).toShadedBody) := by gcongr
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
            ShadedBody.multiplicity (fibre F.innerSet parent good)
              (fun k => (fineShade k).toShadedBody) *
            ShadedBody.multiplicity coarseSet
              (fun l => (coarseShade l).toShadedBody) := by
        rw [hfibre]
        ring

end
end Kakeya.ml1Boot.W50CountedHonestTwoScaleAdapter

#print axioms Kakeya.ml1Boot.W50CountedHonestTwoScaleAdapter.exists_isTwoScaleFactors_of_countedHonestProduct_w50
