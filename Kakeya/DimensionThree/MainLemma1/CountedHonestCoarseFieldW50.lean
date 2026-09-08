module

public import Kakeya.DimensionThree.MainLemma1.Rescaling.KatzTao
public import Kakeya.Factoring.HonestFibreBridge
public import Kakeya.DimensionThree.MainLemma1.CountedExactCoarseAnalyticW50

@[expose] public section

open MeasureTheory Convexity ConvexSpaceBody ShadedBody Filter Topology
open scoped NNReal ENNReal

namespace Kakeya.ml1Boot.W50CountedHonestCoarseField

noncomputable section

universe u v w

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]

/-- Uniform complete fibres transfer Frostman control from the retained fine
family to all dilated parents.  This is the all-parent counting step and does
not select the parent family after the product. -/
theorem frostmanConstIn_dilate_parent_le_counted_w50
    {iota : Type w} {kappa : Type u} [DecidableEq kappa]
    {sigma rho : NNReal} {c : Real}
    {s : Finset iota} {V : iota -> Tube sigma E}
    {t : Finset kappa} {Vrho : kappa -> Tube rho E}
    {p : iota -> kappa} {K : ConvexSpaceBody E} {N : ENNReal}
    (hsigma0 : 0 < sigma) (hsigma1 : sigma <= 1)
    (hc0 : 0 < c) (hN : 0 < N)
    (hpar : IsParentFamilyDilate c s V t Vrho p)
    (hcard : forall k, k ∈ t ->
      N <= ((fibre s p k).card : ENNReal) /\
      ((fibre s p k).card : ENNReal) <= 2 * N)
    (hVrhoK : forall k, k ∈ t -> Tube.dilate (Vrho k) c <= K) :
    frostmanConstIn t (fun k => Tube.dilate (Vrho k) c) K <=
      2 * frostmanConstIn s (fun i => (V i).toConvexSpaceBody) K := by
  classical
  apply frostmanConstIn_le
  apply ConvexSpaceBody.isFrostmanIn_parents_of_uniform_fibres
    (q := s) (out := t) (V := fun i => (V i).toConvexSpaceBody)
    (W := fun k => Tube.dilate (Vrho k) c) (par := p)
    (fib := fun k => fibre s p k)
    (K := K) (C := frostmanConstIn s (fun i => (V i).toConvexSpaceBody) K)
    (Cmass := 2)
  · exact isFrostmanIn_frostmanConstIn s (fun i => (V i).toConvexSpaceBody) K
  · intro i hi
    exact (Tube.volume_pos_and_lt_top hsigma0 hsigma1 (V i)).1
  · exact hpar.mapsTo
  · exact hpar.le_parent_dilate
  · exact hVrhoK
  · intro k
    rfl
  · intro k hk
    have hkpos : 0 < (fibre s p k).card := by
      exact_mod_cast lt_of_lt_of_le hN (hcard k hk).1
    exact Finset.card_pos.mp hkpos
  · intro k hk k' hk'
    obtain ⟨i, hi⟩ := Finset.card_pos.mp (by
      exact_mod_cast lt_of_lt_of_le hN (hcard k hk).1)
    have hsub (j : kappa) (hj : j ∈ t) :
        forall a, a ∈ fibre s p j ->
          (V a).toConvexSpaceBody <= Tube.dilate (Vrho j) c := by
      intro a ha
      have hpa := (Finset.mem_filter.mp ha).2
      simpa [hpa] using hpar.le_parent_dilate a (Finset.mem_filter.mp ha).1
    have hvolDil (T : Tube rho E) :
        volume (Tube.dilate T c).carrier =
          ENNReal.ofReal (c ^ Module.finrank Real E) * volume T.carrier := by
      rw [Tube.dilate_carrier, MeasureTheory.Measure.addHaar_image_homothety,
        abs_of_pos (pow_pos hc0 (Module.finrank Real E))]
    simp only [densityIn]
    rw [Finset.filter_eq_self.2 (hsub k hk),
      Finset.filter_eq_self.2 (hsub k' hk')]
    rw [Tube.sum_volume_carrier_eq_card_mul V (V i) (fibre s p k)]
    rw [Tube.sum_volume_carrier_eq_card_mul V (V i) (fibre s p k')]
    have hcards : ((fibre s p k).card : ENNReal) <=
        2 * ((fibre s p k').card : ENNReal) :=
      (hcard k hk).2.trans (mul_le_mul_right (hcard k' hk').1 2)
    have hparentVol : volume (Tube.dilate (Vrho k) c).carrier =
        volume (Tube.dilate (Vrho k') c).carrier := by
      rw [hvolDil, hvolDil,
        Tube.volume_carrier_eq_volume_carrier (Vrho k) (Vrho k')]
    rw [hparentVol]
    calc
      _ <= (2 * ((fibre s p k').card : ENNReal)) * volume (V i).carrier /
          volume (Tube.dilate (Vrho k') c).carrier := by gcongr
      _ = 2 * (((fibre s p k').card : ENNReal) * volume (V i).carrier /
          volume (Tube.dilate (Vrho k') c).carrier) := by
        simp only [div_eq_mul_inv]
        ring

set_option maxHeartbeats 6000000 in
/-- The exact coarse witness of an honest counted product inherits a Frostman
bound from its retained source.  All-parent counting and the common inverse
homothety are performed on the literal `coarseSet/coarseShade` in `hOut`. -/
theorem HonestDilateProductOutput.coarse_frostman_from_retained_source_w50
    {iota : Type w} {kappa : Type u} [DecidableEq kappa]
    {sigma rho c branchN productConstant : NNReal}
    {F : ShadedBody.FactorFamily E iota kappa}
    {T : iota -> ShadedTube sigma E} {Trho : kappa -> Tube rho E}
    {fineSet : Finset iota} {coarseSet : Finset kappa}
    {fineShade : iota -> ShadedTube sigma E}
    {coarseShade : kappa -> ShadedTube rho E} {parent : iota -> kappa}
    (hOut : Kakeya.ml1CoarseHonestW45.HonestDilateProductOutput
      (c := c) F T Trho fineSet coarseSet fineShade coarseShade parent
        productConstant)
    (hsigma0 : 0 < sigma) (hsigma1 : sigma <= 1)
    (hc : 1 < (c : Real)) (hbranchN : 0 < branchN)
    (hparent : IsParentFamilyDilate (c : Real) F.innerSet
      (fun i => (T i).toTube) F.outerSet Trho F.parent)
    (hband : forall k, k ∈ F.outerSet ->
      (branchN : ENNReal) <= ((F.fiber k).card : ENNReal) /\
      ((F.fiber k).card : ENNReal) <= 2 * (branchN : ENNReal))
    (hinner : forall i, i ∈ F.innerSet ->
      F.innerBody i = (T i).toShadedBody)
    {eRef aFull g : Real} (heRef0 : 0 <= eRef)
    (heg : eRef + aFull <= g)
    (hsourceNe : F.innerSet.Nonempty)
    (hsourceBall : forall i, i ∈ F.innerSet ->
      (T i).carrier ⊆ Metric.closedBall 0 1)
    (hsourceFull : (sigma : ENNReal) ^ aFull <=
      ShadedBody.fullness F.innerSet (fun i => (T i).toShadedBody))
    (hrefAbsorb : (sigma : ENNReal) ^ eRef <=
      (((productConstant⁻¹ : NNReal) : ENNReal)))
    {Bsrc : ENNReal}
    (hsourceFrost : frostmanConstIn F.innerSet
      (fun i => (T i).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall <= Bsrc)
    (L : ConvexSpaceBody E)
    (hunitL : (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E) <= L)
    (hrawL : forall k, k ∈ coarseSet ->
      Tube.dilate (Trho k) (c : Real) <= L) :
    frostmanConstIn coarseSet
        (fun k => (coarseShade k).toConvexSpaceBody)
        (L.homothety 0 ((c : Real)⁻¹)) <=
      2 * (volume L.carrier /
        volume (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E).carrier *
          ((sigma : ENNReal) ^ (-g) * Bsrc)) := by
  classical
  have hrefT : IsCRefinement fineSet (fun i => (T i).toShadedBody)
      F.innerSet (fun i => (T i).toShadedBody) (sigma ^ eRef) := by
    refine ⟨⟨hOut.fine_subset, fun _ _ => ⟨rfl, Set.Subset.rfl⟩⟩, ?_⟩
    have hsourceSum :
        ∑ i ∈ F.innerSet, volume (F.innerBody i).shade =
          ∑ i ∈ F.innerSet, volume (T i).shade := by
      apply Finset.sum_congr rfl
      intro i hi
      exact congrArg (fun W : ShadedBody E => volume W.shade) (hinner i hi)
    have hfineMass : ∑ i ∈ fineSet, volume (fineShade i).shade <=
        ∑ i ∈ fineSet, volume (T i).shade := by
      apply Finset.sum_le_sum
      intro i hi
      apply measure_mono
      exact (hOut.fine_refinement.1.2 i hi).2.trans_eq
        (congrArg ShadedBody.shade (hinner i (hOut.fine_subset hi)))
    calc
      (((sigma ^ eRef : NNReal) : ENNReal)) *
          ∑ i ∈ F.innerSet, volume (T i).shade =
          (sigma : ENNReal) ^ eRef *
            ∑ i ∈ F.innerSet, volume (T i).shade := by
              rw [ENNReal.coe_rpow_of_ne_zero hsigma0.ne']
      _ <= (((productConstant⁻¹ : NNReal) : ENNReal)) *
            ∑ i ∈ F.innerSet, volume (T i).shade := by gcongr
      _ = (((productConstant⁻¹ : NNReal) : ENNReal)) *
            ∑ i ∈ F.innerSet, volume (F.innerBody i).shade := by rw [hsourceSum]
      _ <= ∑ i ∈ fineSet, volume (fineShade i).shade := hOut.fine_refinement.2
      _ <= ∑ i ∈ fineSet, volume (T i).shade := hfineMass
  have hselectedFrost :=
    (frostmanConstIn_le_of_cRefinement_of_fullness hsigma0 hsigma1
      (e := eRef) (f := aFull) (g := g) heg T hsourceNe hOut.fine_subset
      hsourceBall hrefT hsourceFull).2
  have hselectedFrostB1 : frostmanConstIn fineSet
      (fun i => (T i).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall <=
      (sigma : ENNReal) ^ (-g) * Bsrc :=
    hselectedFrost.trans (mul_le_mul_of_nonneg_left hsourceFrost bot_le)
  have hvolB1 :
      Not (volume (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E).carrier = 0) :=
    (Metric.measure_closedBall_pos volume (0 : E) one_pos).ne'
  have hmembersB1 : forall i, i ∈ fineSet ->
      (T i).toConvexSpaceBody <=
        (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E) := by
    intro i hi
    exact SetLike.coe_subset_coe.mpr (hsourceBall i (hOut.fine_subset hi))
  have hselectedFrostL : frostmanConstIn fineSet
      (fun i => (T i).toConvexSpaceBody) L <=
      volume L.carrier /
          volume (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E).carrier *
        ((sigma : ENNReal) ^ (-g) * Bsrc) := by
    calc
      frostmanConstIn fineSet (fun i => (T i).toConvexSpaceBody) L <=
          volume L.carrier /
              volume (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E).carrier *
            frostmanConstIn fineSet (fun i => (T i).toConvexSpaceBody)
              ConvexSpaceBody.closedUnitBall :=
        frostmanConstIn_ambient_mono hunitL hvolB1 hmembersB1
      _ <= volume L.carrier /
              volume (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E).carrier *
            ((sigma : ENNReal) ^ (-g) * Bsrc) := by gcongr
  have hbranchParent : forall k, k ∈ coarseSet ->
      (branchN : ENNReal) <= ((fibre F.innerSet parent k).card : ENNReal) /\
      ((fibre F.innerSet parent k).card : ENNReal) <=
        2 * (branchN : ENNReal) := by
    intro k hk
    have hkband := hband k (hOut.coarse_subset hk)
    have hfibreEq : fibre F.innerSet F.parent k = F.fiber k := by
      ext i
      simp only [fibre, ShadedBody.FactorFamily.fiber, Finset.mem_filter]
    simpa only [hOut.parent_eq, hfibreEq] using hkband
  have hbranchFiltered := branch_card_filter_parent hsigma1 heRef0
    F.innerSet parent coarseSet branchN hbranchParent
  have hbranchFine : forall k, k ∈ coarseSet ->
      (branchN : ENNReal) <= ((fibre fineSet parent k).card : ENNReal) /\
      ((fibre fineSet parent k).card : ENNReal) <=
        2 * (branchN : ENNReal) := by
    intro k hk
    have hk' := hbranchFiltered k hk
    rw [hOut.fine_eq_filter]
    exact ⟨hk'.1, hk'.2.1⟩
  have hparentFine : IsParentFamilyDilate (c : Real) fineSet
      (fun i => (T i).toTube) coarseSet Trho parent :=
    { one_le := hc.le
      mapsTo := hOut.parent_mem
      injOn := hparent.injOn.mono
        (Finset.coe_subset.mpr hOut.coarse_subset)
      le_parent_dilate := hOut.raw_parent_containment }
  have hparentFrost : frostmanConstIn coarseSet
      (fun k => Tube.dilate (Trho k) (c : Real)) L <=
      2 * frostmanConstIn fineSet
        (fun i => (T i).toConvexSpaceBody) L :=
    frostmanConstIn_dilate_parent_le_counted_w50
      hsigma0 hsigma1 (zero_lt_one.trans hc) (by exact_mod_cast hbranchN)
      hparentFine hbranchFine hrawL
  have hbody : forall k, k ∈ coarseSet ->
      (coarseShade k).toConvexSpaceBody =
        (Tube.dilate (Trho k) (c : Real)).homothety 0 ((c : Real)⁻¹) := by
    intro k _
    calc
      (coarseShade k).toConvexSpaceBody =
          (Tube.undilateAtZero (c : Real) (Trho k)).toConvexSpaceBody :=
        congrArg (fun U : Tube rho E => U.toConvexSpaceBody)
          (hOut.coarse_tube k)
      _ = (Tube.dilate (Trho k) (c : Real)).homothety 0 ((c : Real)⁻¹) :=
        (Tube.homothety_dilate_eq_undilateAtZero
          (zero_lt_one.trans hc).ne' (Trho k)).symm
  rw [frostmanConstIn_congr coarseSet hbody
    (L.homothety 0 ((c : Real)⁻¹))]
  rw [frostmanConstIn_homothety coarseSet
    (fun k => Tube.dilate (Trho k) (c : Real)) L 0
      (inv_ne_zero (zero_lt_one.trans hc).ne')]
  exact hparentFrost.trans (by
    calc
      2 * frostmanConstIn fineSet (fun i => (T i).toConvexSpaceBody) L <=
          2 * (volume L.carrier /
            volume (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E).carrier *
              ((sigma : ENNReal) ^ (-g) * Bsrc)) := by gcongr
      _ = 2 * (volume L.carrier /
            volume (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E).carrier *
              ((sigma : ENNReal) ^ (-g) * Bsrc)) := rfl)

set_option maxHeartbeats 12000000 in
/-- Literal arbitrary-exponent coarse field for the same counted honest
product witness.  Final ED, Frostman, fullness, and ball premises are all
constructed from `hOut`, its pre-product parent certificate, and retained
source data; none is supplied as a post-factor callback. -/
theorem eventually_coarse_actualA_of_countedHonestOutput_w50
    (hdim : Module.finrank Real E = 3) {gamma : Real}
    (hgamma0 : 0 <= gamma) (hgamma1 : gamma <= 1)
    (hKF : FrostmanEstimate.{u} E gamma) (R : Real) (hR : 1 <= R) :
    forall A : Real, 0 < A -> forall Lf : NNReal, 1 <= Lf ->
      exists etaS : Real, 0 < etaS /\
      ∀ᶠ (sigma : NNReal) in nhdsWithin 0 (Set.Ioi 0),
        sigma <= 1 ->
        forall rho : NNReal, sigma <= rho -> rho <= 1 ->
        forall {iota : Type w} {kappa : Type u} [DecidableEq kappa]
          {c branchN productConstant : NNReal}
          {F : ShadedBody.FactorFamily E iota kappa}
          {T : iota -> ShadedTube sigma E} {Trho : kappa -> Tube rho E}
          {fineSet : Finset iota} {coarseSet : Finset kappa}
          {fineShade : iota -> ShadedTube sigma E}
          {coarseShade : kappa -> ShadedTube rho E} {parent : iota -> kappa},
          Kakeya.ml1CoarseHonestW45.HonestDilateProductOutput
            (c := c) F T Trho fineSet coarseSet fineShade coarseShade parent
              productConstant ->
          (coarseSet : Set kappa).Pairwise (fun q q' =>
            IsEssentiallyDistinct (coarseShade q).carrier
              (coarseShade q').carrier) ->
          1 < (c : Real) -> 0 < branchN ->
          IsParentFamilyDilate (c : Real) F.innerSet
            (fun i => (T i).toTube) F.outerSet Trho F.parent ->
          (forall k, k ∈ F.outerSet ->
            (branchN : ENNReal) <= ((F.fiber k).card : ENNReal) /\
            ((F.fiber k).card : ENNReal) <= 2 * (branchN : ENNReal)) ->
          (forall i, i ∈ F.innerSet ->
            F.innerBody i = (T i).toShadedBody) ->
          forall eRef aFull g : Real, 0 <= eRef -> eRef + aFull <= g ->
          F.innerSet.Nonempty ->
          (forall i, i ∈ F.innerSet ->
            (T i).carrier ⊆ Metric.closedBall 0 1) ->
          (sigma : ENNReal) ^ aFull <=
            ShadedBody.fullness F.innerSet (fun i => (T i).toShadedBody) ->
          (sigma : ENNReal) ^ eRef <=
            (((productConstant⁻¹ : NNReal) : ENNReal)) ->
          forall Bsrc : ENNReal,
          frostmanConstIn F.innerSet (fun i => (T i).toConvexSpaceBody)
              ConvexSpaceBody.closedUnitBall <= Bsrc ->
          forall L : ConvexSpaceBody E,
          (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E) <= L ->
          (forall k, k ∈ coarseSet ->
            Tube.dilate (Trho k) (c : Real) <= L) ->
          L.homothety 0 ((c : Real)⁻¹) =
            ConvexSpaceBody.closedBall (0 : E) R
              (le_trans zero_le_one hR) ->
          (forall k, k ∈ coarseSet ->
            (Trho k).carrier ⊆ Metric.closedBall 0 (R / 2)) ->
          2 * (sigma : ENNReal) ^ etaS <=
            (((productConstant⁻¹ : NNReal) : ENNReal)) *
              (sigma : ENNReal) ^ aFull ->
          2 * (volume L.carrier /
            volume (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E).carrier *
              ((sigma : ENNReal) ^ (-g) * Bsrc)) <=
            (Lf : ENNReal) * (sigma : ENNReal) ^ (-A) ->
          ShadedBody.multiplicity coarseSet
              (fun k => (coarseShade k).toShadedBody) <=
            (sigma : ENNReal) ^ (-4 * A) * (rho : ENNReal) ^ (-2 * gamma) *
              ((coarseSet.card : ENNReal) * (rho : ENNReal) ^ (2 : Nat)) ^
                (1 - gamma / 2) := by
  intro A hA Lf hLf
  obtain ⟨etaS, hetaS, hcoarse⟩ :=
    Kakeya.ml1Boot.W50CountedExactCoarseAnalytic.eventually_coarse_actualA_radius_upstream_w50
      (E := E) hdim hgamma0 hgamma1 hKF R hR A hA Lf hLf
  refine ⟨etaS, hetaS, ?_⟩
  filter_upwards [hcoarse, self_mem_nhdsWithin] with sigma hcoarseSigma hsigma0
  intro hsigma1 rho hsigmaRho hrho1 iota kappa _ c branchN productConstant
    F T Trho fineSet coarseSet fineShade coarseShade parent hOut hcoarseED
    hc hbranchN hparent hband hinner eRef aFull g heRef0 heg hsourceNe
    hsourceBall hsourceFull hrefAbsorb Bsrc hsourceFrost L hunitL hrawL
    hLhom hbaseBall hfullAbsorb hFrostAbsorb
  have hFrost :=
    HonestDilateProductOutput.coarse_frostman_from_retained_source_w50
      hOut hsigma0 hsigma1 hc hbranchN hparent hband hinner heRef0 heg
      hsourceNe hsourceBall hsourceFull hrefAbsorb hsourceFrost L hunitL hrawL
  rw [hLhom] at hFrost
  have hball : forall k, k ∈ coarseSet ->
      (coarseShade k).carrier ⊆ Metric.closedBall 0 R := by
    intro k hk
    exact (hOut.coarse_carrier_subset_closedBall hc.le hbaseBall k hk).trans
      (Metric.closedBall_subset_closedBall (by linarith))
  have houtFull :
      ((((productConstant⁻¹ : NNReal) *
        ShadedBody.fullness F.innerSet F.innerBody : NNReal) : ENNReal)) <=
      ((ShadedBody.fullness coarseSet
        (fun k => (coarseShade k).toShadedBody) : NNReal) : ENNReal) := by
    exact_mod_cast hOut.coarse_fullness
  have hfull : 2 * (sigma : ENNReal) ^ etaS <=
      (ShadedBody.fullness coarseSet
        (fun k => (coarseShade k).toShadedBody) : ENNReal) := by
    calc
      2 * (sigma : ENNReal) ^ etaS <=
          (((productConstant⁻¹ : NNReal) : ENNReal)) *
            (sigma : ENNReal) ^ aFull := hfullAbsorb
      _ <= (((productConstant⁻¹ : NNReal) : ENNReal)) *
          ((ShadedBody.fullness F.innerSet
            (fun i => (T i).toShadedBody) : NNReal) : ENNReal) := by gcongr
      _ = ((((productConstant⁻¹ : NNReal) *
            ShadedBody.fullness F.innerSet F.innerBody : NNReal) : ENNReal)) := by
        have hfullEq : ShadedBody.fullness F.innerSet
            (fun i => (T i).toShadedBody) =
            ShadedBody.fullness F.innerSet F.innerBody := by
          unfold ShadedBody.fullness ShadedBody.fullness'
          congr 2
          · apply Finset.sum_congr rfl
            intro i hi
            exact congrArg (fun W : ShadedBody E => volume W.shade)
              (hinner i hi).symm
          · apply Finset.sum_congr rfl
            intro i hi
            exact congrArg (fun W : ShadedBody E => volume W.carrier)
              (hinner i hi).symm
        rw [hfullEq, ENNReal.coe_mul]
      _ <= ((ShadedBody.fullness coarseSet
          (fun k => (coarseShade k).toShadedBody) : NNReal) : ENNReal) := houtFull
  exact hcoarseSigma hsigma1 rho hsigmaRho hrho1 coarseShade
    hOut.coarse_nonempty hball hcoarseED (hFrost.trans hFrostAbsorb) hfull

end

end Kakeya.ml1Boot.W50CountedHonestCoarseField

#print axioms Kakeya.ml1Boot.W50CountedHonestCoarseField.frostmanConstIn_dilate_parent_le_counted_w50
#print axioms Kakeya.ml1Boot.W50CountedHonestCoarseField.HonestDilateProductOutput.coarse_frostman_from_retained_source_w50
#print axioms Kakeya.ml1Boot.W50CountedHonestCoarseField.eventually_coarse_actualA_of_countedHonestOutput_w50
