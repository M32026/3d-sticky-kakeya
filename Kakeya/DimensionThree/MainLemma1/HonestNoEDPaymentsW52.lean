module

public import Kakeya.DimensionThree.MainLemma1.WZBalancedNormalization
public import Kakeya.Factoring.DilatedTubePresentation
public import Kakeya.DimensionThree.MainLemma1.CountedHonestCoarseFieldW50

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology
open scoped NNReal ENNReal

namespace Kakeya.ml1Boot.W52HonestNoEDPayments

noncomputable section

universe u v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]

/-- The elementary `rho^2 card` density bound is unchanged when the common
ambient ball is enlarged from radius one to any fixed radius at least one.
No essential-distinctness or overlap hypothesis is used. -/
theorem densityIn_closedBall_le_four_rhosq_card_w52
    (hdim : Module.finrank Real E = 3)
    {kappa : Type u} {t : Finset kappa} {rho R : NNReal}
    (hrho1 : rho <= 1) (hR : 1 <= R) (T : kappa -> Tube rho E)
    (hball : forall k, k ∈ t ->
      (T k).carrier ⊆ Metric.closedBall 0 (R : Real)) :
    densityIn t (fun k => (T k).toConvexSpaceBody)
        (ConvexSpaceBody.closedBall (0 : E) (R : Real) R.coe_nonneg) <=
      4 * ((rho : ENNReal) ^ (2 : Nat) * (t.card : ENNReal)) := by
  let BR : ConvexSpaceBody E :=
    ConvexSpaceBody.closedBall (0 : E) (R : Real) R.coe_nonneg
  have hbody : forall k, k ∈ t ->
      (T k).toConvexSpaceBody <= BR := by
    intro k hk
    exact SetLike.coe_subset_coe.mpr (hball k hk)
  have hsum : ∑ k ∈ t, volume (T k).carrier <=
      (t.card : ENNReal) *
        ((_root_.Tube.volume_le.C 3 : NNReal) : ENNReal) *
          (rho : ENNReal) ^ (2 : Nat) := by
    calc
      ∑ k ∈ t, volume (T k).carrier <=
          ∑ _k ∈ t, ((_root_.Tube.volume_le.C 3 : NNReal) : ENNReal) *
            (rho : ENNReal) ^ (2 : Nat) := by
              apply Finset.sum_le_sum
              intro k _hk
              simpa [hdim] using (_root_.Tube.volume_le hrho1 (T k))
      _ = (t.card : ENNReal) *
          ((_root_.Tube.volume_le.C 3 : NNReal) : ENNReal) *
            (rho : ENNReal) ^ (2 : Nat) := by
              rw [Finset.sum_const, nsmul_eq_mul]
              ring
  have hvol :
      volume (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E).carrier <=
        volume BR.carrier := by
    apply measure_mono
    exact Metric.closedBall_subset_closedBall (by exact_mod_cast hR)
  rw [densityIn_of_all_le hbody]
  calc
    (∑ k ∈ t, volume (T k).carrier) / volume BR.carrier <=
        (∑ k ∈ t, volume (T k).carrier) /
          volume (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E).carrier :=
      ENNReal.div_le_div_left hvol _
    _ <= ((t.card : ENNReal) *
          ((_root_.Tube.volume_le.C 3 : NNReal) : ENNReal) *
            (rho : ENNReal) ^ (2 : Nat)) /
          volume (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E).carrier :=
      ENNReal.div_le_div_right hsum _
    _ = (Kakeya.ml1Boot.wzNormalizedTubeDensityC : ENNReal) *
        ((rho : ENNReal) ^ (2 : Nat) * (t.card : ENNReal)) := by
      rw [volume_closedUnitBall_eq (E := E), hdim]
      change _ =
        ((_root_.Tube.volume_le.C 3 /
            (3 * _root_.Tube.le_volume.c 3) : NNReal) : ENNReal) *
          ((rho : ENNReal) ^ (2 : Nat) * (t.card : ENNReal))
      rw [ENNReal.coe_div (mul_ne_zero (by norm_num)
        (_root_.Tube.le_volume.c_pos 3).ne')]
      simp only [ENNReal.coe_mul, ENNReal.coe_ofNat]
      rw [div_eq_mul_inv, div_eq_mul_inv]
      ring
    _ <= 4 * ((rho : ENNReal) ^ (2 : Nat) * (t.card : ENNReal)) := by
      gcongr
      exact_mod_cast Kakeya.ml1Boot.wzNormalizedTubeDensityC_le_four

/-- On the literal coarse family, Frostman control and the upper Q-band pay
the maximal-density premise of the no-ED Katz--Tao consumer.  This avoids any
post-product ED selection and does not use `Tube.HasBoundedOverlap`. -/
theorem maxDensity_le_of_frostman_qUpper_closedBall_w52
    (hdim : Module.finrank Real E = 3)
    {kappa : Type u} {t : Finset kappa}
    {delta rho R CF CQ : NNReal} {zF zQ : Real}
    (hdelta0 : 0 < delta) (hrho1 : rho <= 1) (hR : 1 <= R)
    (T : kappa -> ShadedTube rho E)
    (hball : forall k, k ∈ t ->
      (T k).carrier ⊆ Metric.closedBall 0 (R : Real))
    (hFrost : frostmanConstIn t (fun k => (T k).toConvexSpaceBody)
        (ConvexSpaceBody.closedBall (0 : E) (R : Real) R.coe_nonneg) <=
      (CF : ENNReal) * (delta : ENNReal) ^ (-zF))
    (hQhi : (rho : ENNReal) ^ (2 : Nat) * (t.card : ENNReal) <=
      (CQ : ENNReal) * (delta : ENNReal) ^ (-zQ)) :
    maxDensity t (fun k => (T k).toConvexSpaceBody) <=
      ((4 * CF * CQ : NNReal) : ENNReal) *
        (delta : ENNReal) ^ (-(zF + zQ)) := by
  have hbody : forall k, k ∈ t ->
      (T k).toConvexSpaceBody <=
        (ConvexSpaceBody.closedBall (0 : E) (R : Real) R.coe_nonneg) := by
    intro k hk
    exact SetLike.coe_subset_coe.mpr (hball k hk)
  have hFr := isFrostmanIn_of_frostmanConstIn_le hFrost
  have hmax := hFr.maxDensity_le_of_carrier_subset hbody
  have hdens := densityIn_closedBall_le_four_rhosq_card_w52
    hdim hrho1 hR (fun k => (T k).toTube) hball
  have hdeltaE0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hdelta0.ne'
  have hdeltaEtop : (delta : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  calc
    maxDensity t (fun k => (T k).toConvexSpaceBody) <=
        ((CF : ENNReal) * (delta : ENNReal) ^ (-zF)) *
          densityIn t (fun k => (T k).toConvexSpaceBody)
            (ConvexSpaceBody.closedBall (0 : E) (R : Real) R.coe_nonneg) := hmax
    _ <= ((CF : ENNReal) * (delta : ENNReal) ^ (-zF)) *
        (4 * ((rho : ENNReal) ^ (2 : Nat) * (t.card : ENNReal))) := by
          gcongr
    _ <= ((CF : ENNReal) * (delta : ENNReal) ^ (-zF)) *
        (4 * ((CQ : ENNReal) * (delta : ENNReal) ^ (-zQ))) := by
          gcongr
    _ = ((4 * CF * CQ : NNReal) : ENNReal) *
        (delta : ENNReal) ^ (-(zF + zQ)) := by
      rw [show -(zF + zQ) = -zF + -zQ by ring,
        ENNReal.rpow_add (-zF) (-zQ) hdeltaE0 hdeltaEtop]
      push_cast
      ring

/-! The producer-facing payment packet.  The reference family is the protected
Frostman family (typically `s₂`) and `source` is the literal family emitted by
the honest product.  Once the producer supplies `source ⊆ reference` and its
card-retention ratio, the hereditary fullness clause and the scalar Frostman
bound transfer without any ED or overlap hypothesis. -/
theorem source_fullness_frostman_of_hereditary_w52
    {delta : NNReal}
    {ι : Type u} [DecidableEq ι]
    {reference source : Finset ι}
    {V : ι -> ShadedTube delta E}
    (hsourceSub : source ⊆ reference)
    (hsourceNe : source.Nonempty)
    (hball : forall i, i ∈ reference ->
      (V i).carrier ⊆ Metric.closedBall (0 : E) 1)
    {etaRef : Real}
    (hhered : forall t, t ⊆ reference -> t.Nonempty ->
      (delta : ENNReal) ^ etaRef <=
        (ShadedBody.fullness t
          (fun i => (V i).toShadedBody) : ENNReal))
    {Bsrc : ENNReal}
    (hFrost : ConvexSpaceBody.frostmanConstant reference
      (fun i => (V i).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall <= Bsrc)
    {kappa : ENNReal} (hkappa : kappa ≠ 0)
    (hcard : kappa * (reference.card : ENNReal) <=
      (source.card : ENNReal)) :
    (delta : ENNReal) ^ etaRef <=
        (ShadedBody.fullness source
          (fun i => (V i).toShadedBody) : ENNReal) /\
      frostmanConstIn source
          (fun i => (V i).toConvexSpaceBody)
          ConvexSpaceBody.closedUnitBall <=
        kappa⁻¹ * Bsrc := by
  have hrefNe : reference.Nonempty := hsourceNe.mono hsourceSub
  have hfull := hhered source hsourceSub hsourceNe
  have hvol : forall i, i ∈ reference ->
      volume (V i).carrier = volume (V hrefNe.choose).carrier := by
    intro i hi
    exact Tube.volume_carrier_eq_volume_carrier
      (V i).toTube (V hrefNe.choose).toTube
  have hWK : forall i, i ∈ reference ->
      (V i).toConvexSpaceBody <=
        (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E) := by
    intro i hi
    exact SetLike.coe_subset_coe.mpr (hball i hi)
  have hFrostIn : frostmanConstIn reference
      (fun i => (V i).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall <= Bsrc := by
    simpa only [ConvexSpaceBody.frostmanConstIn_eq_frostmanConstant] using hFrost
  have hsourceFrost :=
    ConvexSpaceBody.frostmanConstIn_subfamily_le
      (s := reference) (s' := source)
      (W := fun i => (V i).toConvexSpaceBody)
      (K := ConvexSpaceBody.closedUnitBall)
      hrefNe hvol hWK hsourceSub hkappa hcard
  exact ⟨hfull, hsourceFrost.trans (mul_le_mul_right hFrostIn _ )⟩

/-! Pay the literal coarse fullness from the product inverse.  This is the
small algebraic step that used to be exposed as `hfullAbsorb` at the consumer:
the producer supplies the inverse-product bound and the source fullness, while
the output's `coarse_fullness` supplies the comparison to the displayed coarse
family. -/
theorem product_fullness_payment_w52
    {delta productConstant : NNReal} (hdelta0 : 0 < delta)
    (hdelta1 : delta <= 1)
    {source target : ENNReal} {eRef aFull q : Real}
    (hsource : (delta : ENNReal) ^ aFull <= source)
    (hproduct : (delta : ENNReal) ^ eRef <=
      (productConstant : ENNReal)⁻¹)
    (hbudget : eRef + aFull <= q)
    (hcompare : (productConstant : ENNReal)⁻¹ * source <= target) :
    (delta : ENNReal) ^ q <= target := by
  have hdeltaE0 : (delta : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr hdelta0.ne'
  have hdeltaEtop : (delta : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  calc
    (delta : ENNReal) ^ q <= (delta : ENNReal) ^ (eRef + aFull) :=
      ENNReal.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hdelta1) hbudget
    _ = (delta : ENNReal) ^ eRef * (delta : ENNReal) ^ aFull := by
      rw [ENNReal.rpow_add _ _ hdeltaE0 hdeltaEtop]
    _ <= (delta : ENNReal) ^ eRef * source := by
      gcongr
    _ <= (productConstant : ENNReal)⁻¹ * source := by
      gcongr
    _ <= target := hcompare

/-! Attach the preceding algebra to the exact `HonestDilateProductOutput`
record.  The comparison is the record's own `coarse_fullness` field, so no
post-product family or overlap estimate enters. -/
theorem honestOutput_coarse_fullness_of_source_w52
    {ι : Type u} {κ : Type u} [DecidableEq ι] [DecidableEq κ]
    {delta rho c : NNReal}
    {F : ShadedBody.FactorFamily E ι κ}
    {T : ι -> ShadedTube delta E} {Tb : κ -> Tube rho E}
    {fineSet : Finset ι} {coarseSet : Finset κ}
    {fineShade : ι -> ShadedTube delta E}
    {coarseShade : κ -> ShadedTube rho E}
    {parent : ι -> κ} {productConstant : NNReal}
    (hOut : Kakeya.ml1CoarseHonestW45.HonestDilateProductOutput
      (c := c) F T Tb fineSet coarseSet fineShade coarseShade parent productConstant)
    {aFull eRef q : Real} (hdelta0 : 0 < delta) (hdelta1 : delta <= 1)
    (hproduct1 : 1 <= productConstant)
    (hsource : (delta : ENNReal) ^ aFull <=
      (ShadedBody.fullness F.innerSet F.innerBody : ENNReal))
    (hproduct : (delta : ENNReal) ^ eRef <=
      (productConstant : ENNReal)⁻¹)
    (hbudget : eRef + aFull <= q) :
    (delta : ENNReal) ^ q <=
      (ShadedBody.fullness coarseSet
        (fun k => (coarseShade k).toShadedBody) : ENNReal) := by
  have hproduct0 : productConstant ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one hproduct1)
  have hcompare :
      (productConstant : ENNReal)⁻¹ *
          (ShadedBody.fullness F.innerSet F.innerBody : ENNReal) <=
        (ShadedBody.fullness coarseSet
          (fun k => (coarseShade k).toShadedBody) : ENNReal) := by
    rw [← ENNReal.coe_inv hproduct0, ← ENNReal.coe_mul]
    exact_mod_cast hOut.coarse_fullness
  exact product_fullness_payment_w52 hdelta0 hdelta1 hsource
    hproduct hbudget hcompare

/-! All-parent Frostman transport for an honest dilated parent family.  This
is the no-ED Katz--Tao bridge: the only loss is the factor-two fibre-card
band. -/
theorem frostmanConstIn_dilate_parent_le_honest_w52
    {ι κ : Type*} [DecidableEq κ]
    {sigma rho : NNReal} {c : Real}
    {s : Finset ι} {V : ι -> Tube sigma E}
    {t : Finset κ} {Vrho : κ -> Tube rho E} {p : ι -> κ}
    {K : ConvexSpaceBody E} {N : ENNReal}
    (hsigma0 : 0 < sigma) (hsigma1 : sigma <= 1)
    (hc0 : 0 < c) (hN : 0 < N)
    (hpar : Kakeya.ml1Boot.IsParentFamilyDilate c s V t Vrho p)
    (hcard : forall k, k ∈ t ->
      N <= ((Kakeya.ml1Boot.fibre s p k).card : ENNReal) /\
      ((Kakeya.ml1Boot.fibre s p k).card : ENNReal) <= 2 * N)
    (hVrhoK : forall k, k ∈ t ->
      Tube.dilate (Vrho k) c <= K) :
    frostmanConstIn t (fun k => Tube.dilate (Vrho k) c) K <=
      2 * frostmanConstIn s (fun i => (V i).toConvexSpaceBody) K := by
  classical
  apply frostmanConstIn_le
  apply ConvexSpaceBody.isFrostmanIn_parents_of_uniform_fibres
    (q := s) (out := t) (V := fun i => (V i).toConvexSpaceBody)
    (W := fun k => Tube.dilate (Vrho k) c) (par := p)
    (fib := fun k => Kakeya.ml1Boot.fibre s p k)
    (K := K) (C := frostmanConstIn s (fun i => (V i).toConvexSpaceBody) K)
    (Cmass := 2)
  · exact isFrostmanIn_frostmanConstIn s
      (fun i => (V i).toConvexSpaceBody) K
  · intro i hi
    exact (Tube.volume_pos_and_lt_top hsigma0 hsigma1 (V i)).1
  · exact hpar.mapsTo
  · exact hpar.le_parent_dilate
  · exact hVrhoK
  · intro k
    rfl
  · intro k hk
    have hkpos : 0 < (Kakeya.ml1Boot.fibre s p k).card := by
      exact_mod_cast lt_of_lt_of_le hN (hcard k hk).1
    exact Finset.card_pos.mp hkpos
  · intro k hk k' hk'
    obtain ⟨i, hi⟩ := Finset.card_pos.mp (by
      exact_mod_cast lt_of_lt_of_le hN (hcard k hk).1)
    have hsub (j : κ) (hj : j ∈ t) :
        forall a, a ∈ Kakeya.ml1Boot.fibre s p j ->
          (V a).toConvexSpaceBody <= Tube.dilate (Vrho j) c := by
      intro a ha
      have hpa := (Finset.mem_filter.mp ha).2
      simpa [hpa] using hpar.le_parent_dilate a
        (Finset.mem_filter.mp ha).1
    have hvolDil (T : Tube rho E) :
        volume (Tube.dilate T c).carrier =
          ENNReal.ofReal (c ^ Module.finrank Real E) * volume T.carrier := by
      rw [Tube.dilate_carrier,
        MeasureTheory.Measure.addHaar_image_homothety,
        abs_of_pos (pow_pos hc0 (Module.finrank Real E))]
    simp only [densityIn]
    rw [Finset.filter_eq_self.2 (hsub k hk),
      Finset.filter_eq_self.2 (hsub k' hk')]
    rw [Tube.sum_volume_carrier_eq_card_mul V (V i)
      (Kakeya.ml1Boot.fibre s p k)]
    rw [Tube.sum_volume_carrier_eq_card_mul V (V i)
      (Kakeya.ml1Boot.fibre s p k')]
    have hcards :
        ((Kakeya.ml1Boot.fibre s p k).card : ENNReal) <=
          2 * ((Kakeya.ml1Boot.fibre s p k').card : ENNReal) :=
      (hcard k hk).2.trans
        (mul_le_mul_right (hcard k' hk').1 2)
    have hparentVol :
        volume (Tube.dilate (Vrho k) c).carrier =
          volume (Tube.dilate (Vrho k') c).carrier := by
      rw [hvolDil, hvolDil,
        Tube.volume_carrier_eq_volume_carrier (Vrho k) (Vrho k')]
    rw [hparentVol]
    calc
      _ <= (2 * ((Kakeya.ml1Boot.fibre s p k').card : ENNReal)) *
          volume (V i).carrier /
          volume (Tube.dilate (Vrho k') c).carrier := by gcongr
      _ = 2 * (((Kakeya.ml1Boot.fibre s p k').card : ENNReal) *
          volume (V i).carrier /
          volume (Tube.dilate (Vrho k') c).carrier) := by
        simp only [div_eq_mul_inv]
        ac_rfl

/-! Combine the all-parent bridge with the honest presentation transport.
The parent-family map and its fibre band are required on the *same* `fineSet`
and `coarseSet` carried by `hOut`; no post-product family is introduced. -/
theorem honestOutput_coarse_frostman_from_fine_w52
    {ι : Type u} {κ : Type u} [DecidableEq κ]
    {delta rho c : NNReal}
    {F : ShadedBody.FactorFamily E ι κ}
    {T : ι -> ShadedTube delta E} {Tb : κ -> Tube rho E}
    {fineSet : Finset ι} {coarseSet : Finset κ}
    {fineShade : ι -> ShadedTube delta E}
    {coarseShade : κ -> ShadedTube rho E}
    {parent : ι -> κ} {productConstant : NNReal}
    (hOut : Kakeya.ml1CoarseHonestW45.HonestDilateProductOutput
      (c := c) F T Tb fineSet coarseSet fineShade coarseShade parent productConstant)
    {L : ConvexSpaceBody E} {Bsrc N : ENNReal}
    (hdelta0 : 0 < delta) (hdelta1 : delta <= 1)
    (hc : 1 < (c : Real)) (hN : 0 < N)
    (hinj : Set.InjOn (fun k => (Tb k).toConvexSpaceBody)
      (coarseSet : Set κ))
    (hbranch : forall k, k ∈ coarseSet ->
      N <= ((Kakeya.ml1Boot.fibre fineSet parent k).card : ENNReal) /\
      ((Kakeya.ml1Boot.fibre fineSet parent k).card : ENNReal) <= 2 * N)
    (hTL : forall j, j ∈ coarseSet ->
      Tube.dilate (Tb j) (c : Real) <= L)
    (hfineFrost : frostmanConstIn fineSet
      (fun i => (T i).toConvexSpaceBody) L <= Bsrc) :
    frostmanConstIn coarseSet
        (fun j => (coarseShade j).toConvexSpaceBody)
        (L.homothety 0 ((c : Real)⁻¹)) <= 2 * Bsrc := by
  let hparent : Kakeya.ml1Boot.IsParentFamilyDilate (c : Real) fineSet
      (fun i => (T i).toTube) coarseSet Tb parent := {
    one_le := by exact_mod_cast hc.le
    mapsTo := hOut.parent_mem
    injOn := hinj
    le_parent_dilate := hOut.raw_parent_containment }
  have hparentFrost := frostmanConstIn_dilate_parent_le_honest_w52
    (E := E) hdelta0 hdelta1 (zero_lt_one.trans hc) hN hparent hbranch hTL
  have hc0 : (c : Real) ≠ 0 := (zero_lt_one.trans hc).ne'
  have hbody : forall k, k ∈ coarseSet ->
      (coarseShade k).toConvexSpaceBody =
        (Tube.dilate (Tb k) (c : Real)).homothety 0 ((c : Real)⁻¹) := by
    intro k hk
    calc
      (coarseShade k).toConvexSpaceBody =
          (Tube.undilateAtZero (c : Real) (Tb k)).toConvexSpaceBody :=
        congrArg (fun U : Tube rho E => U.toConvexSpaceBody)
          (hOut.coarse_tube k)
      _ = (Tube.dilate (Tb k) (c : Real)).homothety 0 ((c : Real)⁻¹) :=
        (Tube.homothety_dilate_eq_undilateAtZero hc0 (Tb k)).symm
  rw [Kakeya.ml1Boot.frostmanConstIn_congr coarseSet hbody
    (L.homothety 0 ((c : Real)⁻¹))]
  rw [ConvexSpaceBody.frostmanConstIn_homothety coarseSet
    (fun k => Tube.dilate (Tb k) (c : Real)) L 0
    (inv_ne_zero hc0)]
  exact hparentFrost.trans (mul_le_mul_right hfineFrost 2)

/-! Full source-to-output packet.  This is the form consumed by a CaseTwo
caller: the protected reference family supplies hereditary fullness and
Frostman control, while the output's own fine subset and card retention pay the
only subfamily loss. -/
theorem honestOutput_coarse_frostman_from_reference_w52
    {ι : Type u} {κ : Type u} [DecidableEq ι] [DecidableEq κ]
    {delta rho c : NNReal}
    {F : ShadedBody.FactorFamily E ι κ}
    {T : ι -> ShadedTube delta E} {Tb : κ -> Tube rho E}
    {fineSet : Finset ι} {coarseSet : Finset κ}
    {fineShade : ι -> ShadedTube delta E}
    {coarseShade : κ -> ShadedTube rho E}
    {parent : ι -> κ} {productConstant : NNReal}
    (hOut : Kakeya.ml1CoarseHonestW45.HonestDilateProductOutput
      (c := c) F T Tb fineSet coarseSet fineShade coarseShade parent productConstant)
    {reference : Finset ι} {L : ConvexSpaceBody E}
    {Bsrc kappa N : ENNReal} {etaRef : Real}
    (hsourceSub : fineSet ⊆ reference)
    (hsourceNe : fineSet.Nonempty)
    (hball : forall i, i ∈ reference ->
      (T i).carrier ⊆ Metric.closedBall (0 : E) 1)
    (hhered : forall t, t ⊆ reference -> t.Nonempty ->
      (delta : ENNReal) ^ etaRef <=
        (ShadedBody.fullness t
          (fun i => (T i).toShadedBody) : ENNReal))
    (hFrost : ConvexSpaceBody.frostmanConstant reference
      (fun i => (T i).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall <= Bsrc)
    (hkappa : kappa ≠ 0)
    (hcard : kappa * (reference.card : ENNReal) <=
      (fineSet.card : ENNReal))
    (hdelta0 : 0 < delta) (hdelta1 : delta <= 1)
    (hc : 1 < (c : Real)) (hN : 0 < N)
    (hinj : Set.InjOn (fun k => (Tb k).toConvexSpaceBody)
      (coarseSet : Set κ))
    (hbranch : forall k, k ∈ coarseSet ->
      N <= ((Kakeya.ml1Boot.fibre fineSet parent k).card : ENNReal) /\
      ((Kakeya.ml1Boot.fibre fineSet parent k).card : ENNReal) <= 2 * N)
    (hTL : forall j, j ∈ coarseSet ->
      Tube.dilate (Tb j) (c : Real) <= L)
    (hunitL : (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E) <= L)
    (hB10 : volume (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E).carrier ≠ 0) :
    (delta : ENNReal) ^ etaRef <=
        (ShadedBody.fullness fineSet
          (fun i => (T i).toShadedBody) : ENNReal) /\
      frostmanConstIn coarseSet
          (fun j => (coarseShade j).toConvexSpaceBody)
          (L.homothety 0 ((c : Real)⁻¹)) <=
        2 * (volume L.carrier /
          volume (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E).carrier *
          (kappa⁻¹ * Bsrc)) := by
  obtain ⟨hfull, hfineB1⟩ :=
    source_fullness_frostman_of_hereditary_w52
      (E := E) hsourceSub hsourceNe hball hhered hFrost hkappa hcard
  have hfineBody : forall i, i ∈ fineSet ->
      (T i).toConvexSpaceBody <=
        (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E) := by
    intro i hi
    exact SetLike.coe_subset_coe.mpr (hball i (hsourceSub hi))
  have hfineL : frostmanConstIn fineSet
      (fun i => (T i).toConvexSpaceBody) L <=
      volume L.carrier /
        volume (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E).carrier *
        (kappa⁻¹ * Bsrc) := by
    calc
      frostmanConstIn fineSet (fun i => (T i).toConvexSpaceBody) L <=
          volume L.carrier /
            volume (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E).carrier *
              frostmanConstIn fineSet
                (fun i => (T i).toConvexSpaceBody)
                ConvexSpaceBody.closedUnitBall :=
        ConvexSpaceBody.frostmanConstIn_ambient_mono
          hunitL hB10 hfineBody
      _ <= volume L.carrier /
            volume (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E).carrier *
              (kappa⁻¹ * Bsrc) := by
        gcongr
  have hcoarse := honestOutput_coarse_frostman_from_fine_w52
    (E := E) hOut hdelta0 hdelta1 hc hN hinj hbranch hTL
      hfineL
  exact ⟨hfull, hcoarse⟩

/-! Counted-product specialization of the reference packet.  It replaces the
consumer-facing source obligations by the protected reference facts and the
single retention inequality; all fields of the counted honest producer remain
unchanged. -/
set_option maxHeartbeats 6000000 in
theorem honestOutput_coarse_frostman_from_reference_counted_w52
    {ι : Type u} {κ : Type v} [DecidableEq ι] [DecidableEq κ]
    {delta rho c branchN productConstant : NNReal}
    {F : ShadedBody.FactorFamily E ι κ}
    {T : ι -> ShadedTube delta E} {Tb : κ -> Tube rho E}
    {fineSet : Finset ι} {coarseSet : Finset κ}
    {fineShade : ι -> ShadedTube delta E}
    {coarseShade : κ -> ShadedTube rho E} {parent : ι -> κ}
    (hOut : Kakeya.ml1CoarseHonestW45.HonestDilateProductOutput
      (c := c) F T Tb fineSet coarseSet fineShade coarseShade parent productConstant)
    (hdelta0 : 0 < delta) (hdelta1 : delta <= 1)
    (hc : 1 < (c : Real)) (hbranchN : 0 < branchN)
    (hparent : Kakeya.ml1Boot.IsParentFamilyDilate (c : Real) F.innerSet
      (fun i => (T i).toTube) F.outerSet Tb F.parent)
    (hband : forall k, k ∈ F.outerSet ->
      (branchN : ENNReal) <= ((F.fiber k).card : ENNReal) /\
      ((F.fiber k).card : ENNReal) <= 2 * (branchN : ENNReal))
    (hinner : forall i, i ∈ F.innerSet ->
      F.innerBody i = (T i).toShadedBody)
    {reference : Finset ι} {BRef kappa : ENNReal}
    (hsourceSub : F.innerSet ⊆ reference)
    (hsourceNe : F.innerSet.Nonempty)
    (hballRef : forall i, i ∈ reference ->
      (T i).carrier ⊆ Metric.closedBall (0 : E) 1)
    {aFull : Real}
    (hhered : forall t, t ⊆ reference -> t.Nonempty ->
      (delta : ENNReal) ^ aFull <=
        (ShadedBody.fullness t
          (fun i => (T i).toShadedBody) : ENNReal))
    (hFrostRef : ConvexSpaceBody.frostmanConstant reference
      (fun i => (T i).toConvexSpaceBody)
      ConvexSpaceBody.closedUnitBall <= BRef)
    (hkappa : kappa ≠ 0)
    (hcard : kappa * (reference.card : ENNReal) <=
      (F.innerSet.card : ENNReal))
    {eRef g : Real} (heRef0 : 0 <= eRef)
    (heg : eRef + aFull <= g)
    (hrefAbsorb : (delta : ENNReal) ^ eRef <=
      (((productConstant⁻¹ : NNReal) : ENNReal)))
    (L : ConvexSpaceBody E)
    (hunitL : (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E) <= L)
    (hrawL : forall k, k ∈ coarseSet ->
      Tube.dilate (Tb k) (c : Real) <= L) :
    frostmanConstIn coarseSet
        (fun k => (coarseShade k).toConvexSpaceBody)
        (L.homothety 0 ((c : Real)⁻¹)) <=
      2 * (volume L.carrier /
        volume (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E).carrier *
        ((delta : ENNReal) ^ (-g) * (kappa⁻¹ * BRef))) := by
  obtain ⟨hsourceFull, hsourceFrost⟩ :=
    source_fullness_frostman_of_hereditary_w52
      (E := E) hsourceSub hsourceNe hballRef hhered hFrostRef hkappa hcard
  have hsourceBall : forall i, i ∈ F.innerSet ->
      (T i).carrier ⊆ Metric.closedBall (0 : E) 1 := by
    intro i hi
    exact hballRef i (hsourceSub hi)
  have hraw :=
    Kakeya.ml1Boot.W50CountedHonestCoarseField.HonestDilateProductOutput.coarse_frostman_from_retained_source_w50
      hOut hdelta0 hdelta1 hc hbranchN hparent hband hinner heRef0 heg
      hsourceNe hsourceBall hsourceFull hrefAbsorb L hunitL hrawL
      (hsourceFrost := hsourceFrost)
  exact hraw

end

end Kakeya.ml1Boot.W52HonestNoEDPayments

#print axioms Kakeya.ml1Boot.W52HonestNoEDPayments.densityIn_closedBall_le_four_rhosq_card_w52
#print axioms Kakeya.ml1Boot.W52HonestNoEDPayments.maxDensity_le_of_frostman_qUpper_closedBall_w52
#print axioms Kakeya.ml1Boot.W52HonestNoEDPayments.source_fullness_frostman_of_hereditary_w52
#print axioms Kakeya.ml1Boot.W52HonestNoEDPayments.product_fullness_payment_w52
#print axioms Kakeya.ml1Boot.W52HonestNoEDPayments.honestOutput_coarse_fullness_of_source_w52
#print axioms Kakeya.ml1Boot.W52HonestNoEDPayments.frostmanConstIn_dilate_parent_le_honest_w52
#print axioms Kakeya.ml1Boot.W52HonestNoEDPayments.honestOutput_coarse_frostman_from_fine_w52
#print axioms Kakeya.ml1Boot.W52HonestNoEDPayments.honestOutput_coarse_frostman_from_reference_w52
#print axioms Kakeya.ml1Boot.W52HonestNoEDPayments.honestOutput_coarse_frostman_from_reference_counted_w52

end
