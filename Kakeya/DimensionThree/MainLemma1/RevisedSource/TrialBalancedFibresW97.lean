module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.TrialGeometryEntryW96
public import Kakeya.Factoring.RhoTubesUndilated
public import Kakeya.Factoring.WeightedFullness
public import Kakeya.Pigeonhole

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody
open scoped ENNReal NNReal

namespace Kakeya.ml1Boot.TrialRestartW94

noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

universe uE uI uP

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]

/-- S2: a shade-weighted dyadic class keeps whole actual merged fibres. -/
theorem exists_balanced_whole_fibres_factorFamily_w97
    {iota : Type uI} {pi : Type uP} [DecidableEq iota] [DecidableEq pi]
    {d R : NNReal} (F H : Finset iota) (Y : iota -> ShadedTube d E)
    (hHF : H ⊆ F) (hmass : 0 < ∑ i ∈ H, volume (Y i).shade)
    (J : Finset pi) (B : pi -> Tube R E) (parent : iota -> pi)
    (himage : H.image parent = J)
    (hcontain : ∀ i ∈ H, (Y i).toConvexSpaceBody <= (B (parent i)).toConvexSpaceBody)
    (P : ENNReal) (hP : P < ⊤)
    (hpaid : (∑ i ∈ F, volume (Y i).shade) <= P * ∑ i ∈ H, volume (Y i).shade) :
    let Lc := dyadicPigeonholeNatConstant H.card
    ∃ (k : Nat) (Jb : Finset pi) (Hb : Finset iota)
      (FF : ShadedBody.FactorFamily E iota pi),
      k <= Nat.log 2 H.card ∧
      Jb = J.filter (fun j => 2 ^ k <= (completeFibreW94 H parent j).card ∧
        (completeFibreW94 H parent j).card < 2 ^ (k + 1)) ∧
      Jb.Nonempty ∧ Jb ⊆ J ∧ Hb = H.filter (fun i => parent i ∈ Jb) ∧
      Hb.Nonempty ∧ Hb ⊆ H ∧ Hb.image parent = Jb ∧
      (∀ j ∈ Jb, completeFibreW94 Hb parent j = completeFibreW94 H parent j) ∧
      FF.innerSet = Hb ∧ FF.outerSet = Jb ∧ FF.parent = parent ∧
      FF.innerBody = (fun i => (Y i).toShadedBody) ∧
      FF.outerBody = (fun j => (B j).toConvexSpaceBody) ∧
      (∀ j ∈ Jb, FF.fiber j = completeFibreW94 H parent j) ∧
      (∑ i ∈ H, volume (Y i).shade) <= (Lc : ENNReal) * ∑ i ∈ Hb, volume (Y i).shade ∧
      (∑ i ∈ F, volume (Y i).shade) <= P * (Lc : ENNReal) * ∑ i ∈ Hb, volume (Y i).shade := by
  dsimp only
  have hmap : ∀ i ∈ H, parent i ∈ J := by
    intro i hi
    rw [← himage]
    exact Finset.mem_image_of_mem parent hi
  have hfibre : ∀ j ∈ J, (completeFibreW94 H parent j).Nonempty := by
    intro j hj
    rw [← himage] at hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact ⟨i, by simp [completeFibreW94, hi]⟩
  have hsum : (∑ j ∈ J, ∑ i ∈ completeFibreW94 H parent j, volume (Y i).shade) =
      ∑ i ∈ H, volume (Y i).shade := by
    simpa [completeFibreW94] using
      Finset.sum_fiberwise_of_maps_to hmap (fun i => volume (Y i).shade)
  obtain ⟨k, hk, hbandmass⟩ := Nat.dyadic_pigeonhole_ennreal J
    (fun j => ∑ i ∈ completeFibreW94 H parent j, volume (Y i).shade)
    (fun j => (completeFibreW94 H parent j).card)
    (N := H.card) (fun j hj => ⟨(hfibre j hj).card_pos,
      Finset.card_le_card (Finset.filter_subset _ _)⟩)
  rw [hsum] at hbandmass
  let Jb := J.filter (fun j => 2 ^ k <= (completeFibreW94 H parent j).card ∧
    (completeFibreW94 H parent j).card < 2 ^ (k + 1))
  let Hb := H.filter (fun i => parent i ∈ Jb)
  have hJb : Jb ⊆ J := Finset.filter_subset _ _
  have hJbne : Jb.Nonempty := by
    by_contra hnone
    have hempty : Jb = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnone
    change (∑ i ∈ H, volume (Y i).shade) ≤
      (dyadicPigeonholeNatConstant H.card : ENNReal) *
        ∑ j ∈ Jb, ∑ i ∈ completeFibreW94 H parent j, volume (Y i).shade at hbandmass
    simp only [hempty, Finset.sum_empty, mul_zero] at hbandmass
    exact (not_le_of_gt hmass) hbandmass
  have hHb : Hb ⊆ H := Finset.filter_subset _ _
  have hwhole : ∀ j ∈ Jb, completeFibreW94 Hb parent j = completeFibreW94 H parent j := by
    intro j hj
    ext i
    simp only [Hb, completeFibreW94, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hi, _⟩, heq⟩
      exact ⟨hi, heq⟩
    · rintro ⟨hi, heq⟩
      exact ⟨⟨hi, heq ▸ hj⟩, heq⟩
  have hHbimage : Hb.image parent = Jb := by
    apply Finset.Subset.antisymm
    · intro j hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      exact (Finset.mem_filter.mp hi).2
    · intro j hj
      obtain ⟨i, hi⟩ := hfibre j (hJb hj)
      obtain ⟨hiH, hij⟩ := Finset.mem_filter.mp hi
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hiH, hij ▸ hj⟩, hij⟩
  have hHbne : Hb.Nonempty := by
    have : (Hb.image parent).Nonempty := hHbimage ▸ hJbne
    exact Finset.Nonempty.of_image this
  let FF : ShadedBody.FactorFamily E iota pi :=
    { innerSet := Hb
      innerBody := fun i => (Y i).toShadedBody
      outerSet := Jb
      outerBody := fun j => (B j).toConvexSpaceBody
      parent := parent
      parent_mem := fun i hi => (Finset.mem_filter.mp hi).2
      inner_le_parent := fun i hi => hcontain i (hHb hi) }
  have hsumHb : (∑ j ∈ Jb, ∑ i ∈ completeFibreW94 H parent j, volume (Y i).shade) =
      ∑ i ∈ Hb, volume (Y i).shade := by
    calc
      _ = ∑ j ∈ Jb, ∑ i ∈ completeFibreW94 Hb parent j, volume (Y i).shade :=
        Finset.sum_congr rfl fun j hj => by rw [hwhole j hj]
      _ = _ := by
        simpa [completeFibreW94] using Finset.sum_fiberwise_of_maps_to
          (fun i (hi : i ∈ Hb) => (Finset.mem_filter.mp hi).2) (fun i => volume (Y i).shade)
  change (∑ i ∈ H, volume (Y i).shade) ≤
    (dyadicPigeonholeNatConstant H.card : ENNReal) *
      ∑ j ∈ Jb, ∑ i ∈ completeFibreW94 H parent j, volume (Y i).shade at hbandmass
  rw [hsumHb] at hbandmass
  refine ⟨k, Jb, Hb, FF, hk, rfl, hJbne, hJb, rfl, hHbne, hHb, hHbimage,
    hwhole, rfl, rfl, rfl, rfl, rfl, ?_, hbandmass, ?_⟩
  · intro j hj
    simpa only [FF, ShadedBody.FactorFamily.fiber, completeFibreW94] using hwhole j hj
  · exact hpaid.trans (by simpa [mul_assoc] using mul_le_mul_left' hbandmass P)

/-- S3a: coarse density and CF are compared directly to ORIGINAL F by the
same balanced, disjoint, assigned fine fibres. No geometric cell is substituted. -/
theorem balanced_fibres_maxDensity_and_original_frostman_w97
    {iota : Type uI} {pi : Type uP} [DecidableEq iota] [DecidableEq pi]
    (F H : Finset iota) (Y : iota -> ShadedBody E) (hF : F.Nonempty) (hHF : H ⊆ F)
    (J : Finset pi) (B : pi -> ConvexSpaceBody E) (parent : iota -> pi)
    (himage : H.image parent = J)
    (hcontain : ∀ i ∈ H, (Y i).toConvexSpaceBody <= B (parent i))
    (Kfine Kcoarse : ConvexSpaceBody E)
    (hfine : ∀ i ∈ F, (Y i).toConvexSpaceBody <= Kfine)
    (hcoarse : ∀ j ∈ J, B j <= Kcoarse)
    (hKfine : 0 < volume Kfine.carrier) (hKfinefinite : volume Kfine.carrier < ⊤)
    (hKcoarse : 0 < volume Kcoarse.carrier) (hKcoarsefinite : volume Kcoarse.carrier < ⊤)
    (v vR lambda P : ENNReal) (hv : 0 < v) (hvfinite : v < ⊤)
    (hvR : 0 < vR) (hvRfinite : vR < ⊤)
    (hlambda : 0 < lambda) (hlambdafinite : lambda < ⊤)
    (hP : 0 < P) (hPfinite : P < ⊤)
    (hvol : ∀ i ∈ F, volume (Y i).carrier = v)
    (hvolR : ∀ j ∈ J, volume (B j).carrier = vR)
    (hfull : lambda <= fullness' F Y)
    (hpaid : (∑ i ∈ F, volume (Y i).shade) <= P * ∑ i ∈ H, volume (Y i).shade)
    (m : Nat) (hm : 1 <= m)
    (hband : ∀ j ∈ J, m <= (completeFibreW94 H parent j).card ∧
      (completeFibreW94 H parent j).card < 2 * m) :
    H.Nonempty ∧ J.Nonempty ∧
      maxDensity J B <= vR / ((m : ENNReal) * v) *
        maxDensity F (fun i => (Y i).toConvexSpaceBody) ∧
      frostmanConstIn J B Kcoarse <=
        (2 * P / lambda) * (volume Kcoarse.carrier / volume Kfine.carrier) *
          frostmanConstIn F (fun i => (Y i).toConvexSpaceBody) Kfine ∧
      (∀ j ∈ J, ((completeFibreW94 H parent j).card : ENNReal) * (J.card : ENNReal) <=
        2 * (F.card : ENNReal)) := by
  have hsumF (t : Finset iota) (ht : t ⊆ F) :
      (∑ i ∈ t, volume (Y i).carrier) = (t.card : ENNReal) * v := by
    rw [Finset.sum_congr rfl (fun i hi => hvol i (ht hi)), Finset.sum_const, nsmul_eq_mul]
  have hsumJ (t : Finset pi) (ht : t ⊆ J) :
      (∑ j ∈ t, volume (B j).carrier) = (t.card : ENNReal) * vR := by
    rw [Finset.sum_congr rfl (fun j hj => hvolR j (ht hj)), Finset.sum_const, nsmul_eq_mul]
  have hF0 : (F.card : ENNReal) ≠ 0 := by exact_mod_cast hF.card_pos.ne'
  have hcarF0 : (∑ i ∈ F, volume (Y i).carrier) ≠ 0 := by
    rw [hsumF F Finset.Subset.rfl]
    exact mul_ne_zero hF0 hv.ne'
  have hcarFfin : (∑ i ∈ F, volume (Y i).carrier) ≠ ⊤ := by
    rw [hsumF F Finset.Subset.rfl]
    exact ENNReal.mul_ne_top (by simp) hvfinite.ne
  have hfullmass : lambda * ((F.card : ENNReal) * v) ≤ ∑ i ∈ F, volume (Y i).shade := by
    have := mul_le_mul_right' hfull (∑ i ∈ F, volume (Y i).carrier)
    rw [fullness', ENNReal.div_mul_cancel hcarF0 hcarFfin,
      hsumF F Finset.Subset.rfl] at this
    exact this
  have hmassF : 0 < ∑ i ∈ F, volume (Y i).shade :=
    (ENNReal.mul_pos hlambda.ne' (mul_ne_zero hF0 hv.ne')).trans_le hfullmass
  have hmassH : 0 < ∑ i ∈ H, volume (Y i).shade := by
    by_contra hnot
    have hz := nonpos_iff_eq_zero.mp (not_lt.mp hnot)
    rw [hz, mul_zero] at hpaid
    exact (not_le_of_gt hmassF) hpaid
  have hH : H.Nonempty := by
    by_contra hn
    simp [Finset.not_nonempty_iff_eq_empty.mp hn] at hmassH
  have hJ : J.Nonempty := himage ▸ hH.image parent
  have hmap : ∀ i ∈ H, parent i ∈ J := fun i hi => himage ▸ Finset.mem_image_of_mem parent hi
  have hm0 : (m : ENNReal) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  have hJ0 : (J.card : ENNReal) ≠ 0 := by exact_mod_cast hJ.card_pos.ne'
  have hcounts (K : ConvexSpaceBody E) :
      m * (J.filter (fun j => B j ≤ K)).card ≤
        (F.filter (fun i => (Y i).toConvexSpaceBody ≤ K)).card := by
    calc
      _ = ∑ j ∈ J.filter (fun j => B j ≤ K), m := by simp [Nat.mul_comm]
      _ ≤ ∑ j ∈ J.filter (fun j => B j ≤ K), (completeFibreW94 H parent j).card :=
        Finset.sum_le_sum fun j hj => (hband j (Finset.mem_filter.mp hj).1).1
      _ = (H.filter (fun i => parent i ∈ J.filter (fun j => B j ≤ K))).card := by
        simpa [completeFibreW94] using Finset.sum_card_fiberwise_eq_card_filter
          H (J.filter (fun j => B j ≤ K)) parent
      _ ≤ _ := Finset.card_le_card (by
        intro i hi
        obtain ⟨hiH, hj⟩ := Finset.mem_filter.mp hi
        exact Finset.mem_filter.mpr ⟨hHF hiH,
          (hcontain i hiH).trans (Finset.mem_filter.mp hj).2⟩)
  have hmax : maxDensity J B ≤ vR / ((m : ENNReal) * v) *
      maxDensity F (fun i => (Y i).toConvexSpaceBody) := by
    apply maxDensity_le_of_forall_sum_le
    intro K
    calc
      _ = ((J.filter (fun j => B j ≤ K)).card : ENNReal) * vR :=
        hsumJ _ (Finset.filter_subset _ _)
      _ = (vR / ((m : ENNReal) * v)) *
          (((m : ENNReal) * (J.filter (fun j => B j ≤ K)).card) * v) := by
        calc
          _ = (vR / ((m : ENNReal) * v) * ((m : ENNReal) * v)) *
              (J.filter (fun j => B j ≤ K)).card := by
            rw [ENNReal.div_mul_cancel (mul_ne_zero hm0 hv.ne')
              (ENNReal.mul_ne_top (by simp) hvfinite.ne)]
            ring
          _ = _ := by ring
      _ ≤ (vR / ((m : ENNReal) * v)) *
          ((F.filter (fun i => (Y i).toConvexSpaceBody ≤ K)).card * v) := by
        gcongr
        exact_mod_cast hcounts K
      _ = (vR / ((m : ENNReal) * v)) *
          ∑ i ∈ F.filter (fun i => (Y i).toConvexSpaceBody ≤ K), volume (Y i).carrier := by
        rw [hsumF _ (Finset.filter_subset _ _)]
      _ ≤ _ := by
        simpa [mul_assoc] using mul_le_mul_left'
          (sum_volume_le_maxDensity_mul_volume F (fun i => (Y i).toConvexSpaceBody) K)
          (vR / ((m : ENNReal) * v))
  have hcardH : H.card = ∑ j ∈ J, (completeFibreW94 H parent j).card := by
    simpa [completeFibreW94] using Finset.card_eq_sum_card_fiberwise hmap
  have hbandLower : m * J.card ≤ H.card := by
    rw [hcardH]
    simpa [Nat.mul_comm] using Finset.sum_le_sum
      (fun j (hj : j ∈ J) => (hband j hj).1)
  have hbandUpper : H.card ≤ 2 * m * J.card := by
    rw [hcardH]
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using Finset.sum_le_sum
      (fun j (hj : j ∈ J) => (hband j hj).2.le)
  have hcardPayment : lambda * (F.card : ENNReal) ≤ P * (2 * m * J.card : ENNReal) := by
    apply (ENNReal.mul_le_mul_iff_right hv.ne' hvfinite.ne).mp
    calc
      _ ≤ _ := by simpa [mul_assoc, mul_left_comm, mul_comm] using hfullmass.trans hpaid
      _ ≤ P * ∑ i ∈ H, volume (Y i).carrier := by
        exact mul_le_mul_left' (Finset.sum_le_sum fun i _ => measure_mono (Y i).shade_subset) P
      _ ≤ _ := by
        rw [hsumF H hHF]
        have hc : (H.card : ENNReal) ≤ (2 * m * J.card : ENNReal) := by exact_mod_cast hbandUpper
        simpa [mul_assoc, mul_left_comm, mul_comm] using mul_le_mul_left' (mul_le_mul_right' hc v) P
  have hdFine : densityIn F (fun i => (Y i).toConvexSpaceBody) Kfine =
      (F.card : ENNReal) * v / volume Kfine.carrier := by
    unfold densityIn
    rw [Finset.filter_eq_self.mpr hfine, hsumF F Finset.Subset.rfl]
  have hdCoarse : densityIn J B Kcoarse = (J.card : ENNReal) * vR / volume Kcoarse.carrier := by
    unfold densityIn
    rw [Finset.filter_eq_self.mpr hcoarse, hsumJ J Finset.Subset.rfl]
  have hdFine0 : 0 < densityIn F (fun i => (Y i).toConvexSpaceBody) Kfine := by
    rw [hdFine]
    exact ENNReal.div_pos (mul_ne_zero hF0 hv.ne') hKfinefinite.ne
  have hdCoarse0 : 0 < densityIn J B Kcoarse := by
    rw [hdCoarse]
    exact ENNReal.div_pos (mul_ne_zero hJ0 hvR.ne') hKcoarsefinite.ne
  have hcf : frostmanConstIn J B Kcoarse ≤
      (2 * P / lambda) * (volume Kcoarse.carrier / volume Kfine.carrier) *
        frostmanConstIn F (fun i => (Y i).toConvexSpaceBody) Kfine := by
    rw [frostmanConstIn_eq_frostmanConstant, frostmanConstant_eq_maxDensity_div hdCoarse0 hcoarse,
      frostmanConstIn_eq_frostmanConstant, frostmanConstant_eq_maxDensity_div hdFine0 hfine,
      hdFine, hdCoarse]
    refine (ENNReal.div_le_div_right hmax _).trans ?_
    have hscalar : (vR / ((m : ENNReal) * v)) /
        ((J.card : ENNReal) * vR / volume Kcoarse.carrier) ≤
        (2 * P / lambda) * (volume Kcoarse.carrier / volume Kfine.carrier) /
          ((F.card : ENNReal) * v / volume Kfine.carrier) := by
      have hleftfin : vR / ((m : ENNReal) * v) /
          ((J.card : ENNReal) * vR / volume Kcoarse.carrier) ≠ ⊤ :=
        ENNReal.div_ne_top (ENNReal.div_ne_top hvRfinite.ne (mul_ne_zero hm0 hv.ne'))
          (ENNReal.div_pos (mul_ne_zero hJ0 hvR.ne') hKcoarsefinite.ne).ne'
      have hrightfin : (2 * P / lambda) * (volume Kcoarse.carrier / volume Kfine.carrier) /
          ((F.card : ENNReal) * v / volume Kfine.carrier) ≠ ⊤ :=
        ENNReal.div_ne_top
          (ENNReal.mul_ne_top
            (ENNReal.div_ne_top (ENNReal.mul_ne_top (by norm_num) hPfinite.ne) hlambda.ne')
            (ENNReal.div_ne_top hKcoarsefinite.ne hKfine.ne'))
          (ENNReal.div_pos (mul_ne_zero hF0 hv.ne') hKfinefinite.ne).ne'
      rw [← ENNReal.toReal_le_toReal hleftfin hrightfin]
      simp only [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_natCast,
        ENNReal.toReal_ofNat]
      have hvReal : 0 < v.toReal := ENNReal.toReal_pos hv.ne' hvfinite.ne
      have hvRReal : 0 < vR.toReal := ENNReal.toReal_pos hvR.ne' hvRfinite.ne
      have hKfReal : 0 < (volume Kfine.carrier).toReal :=
        ENNReal.toReal_pos hKfine.ne' hKfinefinite.ne
      have hKcReal : 0 < (volume Kcoarse.carrier).toReal :=
        ENNReal.toReal_pos hKcoarse.ne' hKcoarsefinite.ne
      have hlReal : 0 < lambda.toReal := ENNReal.toReal_pos hlambda.ne' hlambdafinite.ne
      have hmReal : 0 < (m : Real) := by exact_mod_cast hm
      have hFReal : 0 < (F.card : Real) := by exact_mod_cast hF.card_pos
      have hJReal : 0 < (J.card : Real) := by exact_mod_cast hJ.card_pos
      have hpReal := (ENNReal.toReal_le_toReal
        (ENNReal.mul_ne_top hlambdafinite.ne (by simp))
        (ENNReal.mul_ne_top hPfinite.ne (by finiteness))).mpr hcardPayment
      simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofNat] at hpReal
      field_simp
      nlinarith
    calc
      _ = ((vR / ((m : ENNReal) * v)) /
          ((J.card : ENNReal) * vR / volume Kcoarse.carrier)) *
          maxDensity F (fun i => (Y i).toConvexSpaceBody) := by
        simp only [div_eq_mul_inv]; ring
      _ ≤ _ := by simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_right' hscalar (maxDensity F (fun i => (Y i).toConvexSpaceBody))
  refine ⟨hH, hJ, hmax, hcf, ?_⟩
  intro j hj
  have hcardF := Finset.card_le_card hHF
  have : (completeFibreW94 H parent j).card * J.card ≤ 2 * F.card := by
    calc
      _ ≤ (2 * m) * J.card := Nat.mul_le_mul_right _ (hband j hj).2.le
      _ = 2 * (m * J.card) := by ring
      _ ≤ _ := Nat.mul_le_mul_left 2 (hbandLower.trans hcardF)
  exact_mod_cast this

def trialTubeProductCostW97 (d : NNReal) (n : Nat) : NNReal :=
  ShadedBody.shadingMultiplicityEstimateForRhoTubesDilate.C 3 n d 1

/-- S3b: invoke the undilated tube product on the actual balanced factor
family, retain its actual shades, and derive all original-F payments. -/
theorem exists_actual_tube_product_with_original_frostman_w97
    (hdim : Module.finrank Real E = 3)
    {iota : Type uI} {pi : Type uP} [DecidableEq iota] [DecidableEq pi]
    {d R : NNReal} (hd : 0 < d) (hdR : d <= R) (hR : R <= 1)
    (F H Hb : Finset iota) (Y : iota -> ShadedTube d E)
    (hF : F.Nonempty) (hHF : H ⊆ F) (hHbH : Hb ⊆ H)
    (hfine_ball : ∀ i ∈ F, (Y i).carrier ⊆ Metric.closedBall 0 1)
    (Jb : Finset pi) (B : pi -> Tube R E) (parent : iota -> pi)
    (himage : Hb.image parent = Jb)
    (hwhole : ∀ j ∈ Jb, completeFibreW94 Hb parent j = completeFibreW94 H parent j)
    (hcoarse_ball : ∀ j ∈ Jb, (B j).carrier ⊆ Metric.closedBall 0 2)
    (FF : ShadedBody.FactorFamily E iota pi)
    (hFFinner : FF.innerSet = Hb) (hFFouter : FF.outerSet = Jb)
    (hFFparent : FF.parent = parent)
    (hFFY : FF.innerBody = fun i => (Y i).toShadedBody)
    (hFFB : FF.outerBody = fun j => (B j).toConvexSpaceBody)
    (P Lc lambda : ENNReal) (hP : 0 < P) (hPfinite : P < ⊤)
    (hLc : 0 < Lc) (hLcfinite : Lc < ⊤)
    (hlambda : 0 < lambda) (hlambdafinite : lambda < ⊤)
    (hfull : lambda <= fullness' F (fun i => (Y i).toShadedBody))
    (hpaid : (∑ i ∈ F, volume (Y i).shade) <= P * Lc * ∑ i ∈ Hb, volume (Y i).shade)
    (m : Nat) (hm : 1 <= m)
    (hband : ∀ j ∈ Jb, m <= (completeFibreW94 H parent j).card ∧
      (completeFibreW94 H parent j).card < 2 * m) :
    let C := trialTubeProductCostW97 d Hb.card
    ∃ (G : ShadedBody.ShadedFactorFamily E iota pi)
      (Yi : iota -> ShadedTube d E) (Yo : pi -> ShadedTube R E),
      G.outerSet.Nonempty ∧ G.outerSet ⊆ Jb ∧
      G.innerSet = Hb.filter (fun i => parent i ∈ G.outerSet) ∧
      G.innerSet.Nonempty ∧ G.parent = parent ∧ G.innerSet.image parent = G.outerSet ∧
      (∀ i ∈ Hb, (G.innerBody i).toConvexSpaceBody = (Y i).toConvexSpaceBody) ∧
      (∀ j ∈ G.outerSet, (G.outerBody j).toConvexSpaceBody = (B j).toConvexSpaceBody) ∧
      (∀ j ∈ G.outerSet, G.fiber j = completeFibreW94 H parent j) ∧
      (∀ i ∈ Hb, (Yi i).toTube = (Y i).toTube ∧ (Yi i).toShadedBody = G.innerBody i) ∧
      (∀ j ∈ G.outerSet, (Yo j).toTube = B j ∧ (Yo j).toShadedBody = G.outerBody j) ∧
      (∀ i ∈ G.innerSet, (Yi i).shade ⊆ (Y i).shade) ∧
      lambda / (P * Lc * (C : ENNReal)) <= fullness' G.outerSet G.outerBody ∧
      lambda / (P * Lc * (C : ENNReal)) <= fullness' G.innerSet G.innerBody ∧
      (∑ i ∈ F, volume (Y i).shade) <=
        P * Lc * (C : ENNReal) * ∑ i ∈ G.innerSet, volume (G.innerBody i).shade ∧
      (∀ j ∈ G.outerSet, ShadedBody.multiplicity Hb (fun i => (Y i).toShadedBody) <=
        (C : ENNReal) * ShadedBody.multiplicity G.outerSet G.outerBody *
          ShadedBody.multiplicity (G.fiber j) G.innerBody) ∧
      (∀ j ∈ G.outerSet, ((G.fiber j).card : ENNReal) * (G.outerSet.card : ENNReal) <=
        2 * (F.card : ENNReal)) ∧
      frostmanConstIn G.outerSet (fun j => (B j).toConvexSpaceBody)
        (ConvexSpaceBody.closedBall (0 : E) 2 zero_le_two) <=
          (16 * P * Lc * (C : ENNReal) / lambda) *
            frostmanConstIn F (fun i => (Y i).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall ∧
      (∀ j ∈ G.outerSet, frostmanConstIn (G.fiber j)
        (fun i => (G.innerBody i).toConvexSpaceBody) (B j).toConvexSpaceBody =
          frostmanConstIn (completeFibreW94 H parent j)
            (fun i => (Y i).toConvexSpaceBody) (B j).toConvexSpaceBody) ∧
      (∃ j ∈ G.outerSet, fullness' G.innerSet G.innerBody <= fullness' (G.fiber j) G.innerBody) := by
  dsimp only
  let C := trialTubeProductCostW97 d Hb.card
  have hC1 : 1 ≤ C := shadingMultiplicityEstimateForRhoTubesDilate.one_le_C 3 Hb.card d 1
  have hC0 : C ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hC1)
  have hCe0 : (C : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hC0
  have hPL0 : P * Lc ≠ 0 := mul_ne_zero hP.ne' hLc.ne'
  have hPLfin : P * Lc ≠ ⊤ := ENNReal.mul_ne_top hPfinite.ne hLcfinite.ne
  have hHbF := hHbH.trans hHF
  have hmassF : 0 < ∑ i ∈ F, volume (Y i).shade := by
    have hpos : 0 < fullness' F (fun i => (Y i).toShadedBody) := hlambda.trans_le hfull
    by_contra hnone
    have hz := nonpos_iff_eq_zero.mp (not_lt.mp hnone)
    simpa only [fullness', hz, ENNReal.zero_div, lt_self_iff_false] using hpos
  have hmassHb : 0 < ∑ i ∈ Hb, volume (Y i).shade := by
    by_contra hnone
    have hz := nonpos_iff_eq_zero.mp (not_lt.mp hnone)
    rw [hz, mul_zero] at hpaid
    exact (not_le_of_gt hmassF) hpaid
  have hHbne : Hb.Nonempty := by
    by_contra hnone
    simp [Finset.not_nonempty_iff_eq_empty.mp hnone] at hmassHb
  have hcarrierHb : 0 < ∑ i ∈ Hb, volume (Y i).carrier :=
    hmassHb.trans_le (Finset.sum_le_sum fun i _ => measure_mono (Y i).shade_subset)
  have hfullHb : lambda / (P * Lc) ≤ fullness' Hb (fun i => (Y i).toShadedBody) := by
    apply (ENNReal.div_le_iff' hPL0 hPLfin).mpr
    refine hfull.trans ?_
    unfold fullness'
    calc
      _ ≤ (P * Lc * ∑ i ∈ Hb, volume (Y i).shade) /
          (∑ i ∈ Hb, volume (Y i).carrier) :=
        ENNReal.div_le_div hpaid (Finset.sum_le_sum_of_subset hHbF)
      _ = _ := by rw [mul_div_assoc]
  obtain ⟨G, hGsub, hGin, hGp, hGouter, hGinner, hGnonempty, hGfull, hGref,
    hGproduct, hGshadeparent, hGunions, hGthicken⟩ :=
    shadingMultiplicityEstimateForRhoTubesUndilated hd ⟨hdR, hR⟩ FF Y B
      (fun i hi => congrFun hFFY i) (fun j hj => congrFun hFFB j)
      (fun i hi => by simpa only [hFFY] using hfine_ball i (hHbF (hFFinner ▸ hi)))
  simp only [hFFinner, hFFouter, hFFparent] at hGsub hGin hGp
  have hGout : G.outerSet.Nonempty := hGnonempty (by simpa only [hFFinner, hFFY] using hmassHb)
  have hGi : ∀ i ∈ Hb, (G.innerBody i).toConvexSpaceBody = (Y i).toConvexSpaceBody := by
    intro i hi
    simpa only [hFFY] using hGinner i (hFFinner.symm ▸ hi)
  have hGo : ∀ j ∈ G.outerSet, (G.outerBody j).toConvexSpaceBody = (B j).toConvexSpaceBody := by
    intro j hj
    simpa only [hFFB] using hGouter j hj
  have hGinsub : G.innerSet ⊆ Hb := by rw [hGin]; exact Finset.filter_subset _ _
  have hGimage : G.innerSet.image parent = G.outerSet := by
    apply Finset.Subset.antisymm
    · intro j hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
      rw [hGin] at hi
      exact (Finset.mem_filter.mp hi).2
    · intro j hj
      have hjb := hGsub hj
      rw [← himage] at hjb
      obtain ⟨i, hi, hij⟩ := Finset.mem_image.mp hjb
      exact Finset.mem_image.mpr ⟨i, by rw [hGin]; exact Finset.mem_filter.mpr ⟨hi, hij ▸ hj⟩, hij⟩
  have hGinne : G.innerSet.Nonempty := Finset.Nonempty.of_image (hGimage.symm ▸ hGout)
  have hGfib : ∀ j ∈ G.outerSet, G.fiber j = completeFibreW94 H parent j := by
    intro j hj
    rw [← hwhole j (hGsub hj)]
    ext i
    simp only [ShadedFactorFamily.fiber, completeFibreW94, hGin, hGp, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hi, _⟩, hij⟩; exact ⟨hi, hij⟩
    · rintro ⟨hi, hij⟩; exact ⟨⟨hi, hij ▸ hj⟩, hij⟩
  have hBodyExt {A Z : ShadedBody E}
      (hbody : A.toConvexSpaceBody = Z.toConvexSpaceBody) (hshade : A.shade = Z.shade) : A = Z := by
    cases A
    cases Z
    cases hbody
    cases hshade
    rfl
  let Yi : iota → ShadedTube d E := fun i => if hi : i ∈ Hb then
    { toTube := (Y i).toTube
      shade := (G.innerBody i).shade
      measurableSet_shade := (G.innerBody i).measurableSet_shade
      shade_subset := by
        rw [← show (G.innerBody i).carrier = (Y i).carrier from congrArg ConvexSpaceBody.carrier (hGi i hi)]
        exact (G.innerBody i).shade_subset }
    else Y i
  let Yo : pi → ShadedTube R E := fun j => if hj : j ∈ G.outerSet then
    { toTube := B j
      shade := (G.outerBody j).shade
      measurableSet_shade := (G.outerBody j).measurableSet_shade
      shade_subset := by
        rw [← show (G.outerBody j).carrier = (B j).carrier from congrArg ConvexSpaceBody.carrier (hGo j hj)]
        exact (G.outerBody j).shade_subset }
    else { toTube := B j
           shade := ∅
           measurableSet_shade := MeasurableSet.empty
           shade_subset := Set.empty_subset _ }
  have hYi : ∀ i ∈ Hb, (Yi i).toTube = (Y i).toTube ∧ (Yi i).toShadedBody = G.innerBody i := by
    intro i hi
    dsimp only [Yi]
    rw [dif_pos hi]
    exact ⟨rfl, hBodyExt (hGi i hi).symm rfl⟩
  have hYo : ∀ j ∈ G.outerSet, (Yo j).toTube = B j ∧ (Yo j).toShadedBody = G.outerBody j := by
    intro j hj
    dsimp only [Yo]
    rw [dif_pos hj]
    exact ⟨rfl, hBodyExt (hGo j hj).symm rfl⟩
  have hGref' : IsCRefinement G.innerSet G.innerBody Hb (fun i => (Y i).toShadedBody) C⁻¹ := by
    simpa only [hFFinner, hFFY, hdim, C, trialTubeProductCostW97] using hGref
  have hGshade : ∀ i ∈ G.innerSet, (Yi i).shade ⊆ (Y i).shade := by
    intro i hi
    change ((Yi i).toShadedBody).shade ⊆ (Y i).shade
    rw [(hYi i (hGinsub hi)).2]
    exact (hGref'.1.2 i hi).2
  have hGfullOut : lambda / (P * Lc * (C : ENNReal)) ≤ fullness' G.outerSet G.outerBody := by
    have hGfull' : C⁻¹ * fullness Hb (fun i => (Y i).toShadedBody) ≤
        fullness G.outerSet G.outerBody := by
      simpa only [hFFinner, hFFY, hdim, C, trialTubeProductCostW97] using hGfull
    have hh : (C : ENNReal)⁻¹ * fullness' Hb (fun i => (Y i).toShadedBody) ≤
        fullness' G.outerSet G.outerBody := by
      simpa only [ENNReal.coe_mul, ENNReal.coe_inv hC0, ShadedBody.coe_fullness] using
        (ENNReal.coe_le_coe.mpr hGfull')
    calc
      _ = (C : ENNReal)⁻¹ * (lambda / (P * Lc)) := by
        simp only [div_eq_mul_inv]
        rw [ENNReal.mul_inv (.inl hPL0) (.inl hPLfin)]
        ring
      _ ≤ _ := (mul_le_mul_left' hfullHb _).trans hh
  have hGfullIn : lambda / (P * Lc * (C : ENNReal)) ≤ fullness' G.innerSet G.innerBody := by
    have hh := ShadedBody.IsCRefinement.mul_fullness_le _ _ _ _ hcarrierHb hGref'
    have hh' : (C : ENNReal)⁻¹ * fullness' Hb (fun i => (Y i).toShadedBody) ≤
        fullness' G.innerSet G.innerBody := by
      simpa only [ENNReal.coe_mul, ENNReal.coe_inv hC0, ShadedBody.coe_fullness] using
        (ENNReal.coe_le_coe.mpr hh)
    calc
      _ = (C : ENNReal)⁻¹ * (lambda / (P * Lc)) := by
        simp only [div_eq_mul_inv]
        rw [ENNReal.mul_inv (.inl hPL0) (.inl hPLfin)]
        ring
      _ ≤ _ := (mul_le_mul_left' hfullHb _).trans hh'
  have hmassG : (∑ i ∈ F, volume (Y i).shade) ≤
      P * Lc * (C : ENNReal) * ∑ i ∈ G.innerSet, volume (G.innerBody i).shade := by
    have hh := hGref'.2
    rw [ENNReal.coe_inv hC0] at hh
    have hpaidG := (ENNReal.inv_mul_le_iff hCe0 ENNReal.coe_ne_top).mp hh
    exact hpaid.trans (by simpa [mul_assoc] using mul_le_mul_left' hpaidG (P * Lc))
  have hproduct : ∀ j ∈ G.outerSet, ShadedBody.multiplicity Hb (fun i => (Y i).toShadedBody) ≤
      (C : ENNReal) * ShadedBody.multiplicity G.outerSet G.outerBody *
        ShadedBody.multiplicity (G.fiber j) G.innerBody := by
    simpa only [hFFinner, hFFY, hdim, C, trialTubeProductCostW97] using hGproduct
  have hGF : G.innerSet ⊆ F := hGinsub.trans hHbF
  have hGcontains : ∀ i ∈ G.innerSet,
      (Y i).toConvexSpaceBody ≤ (B (parent i)).toConvexSpaceBody := by
    intro i hi
    simpa only [hFFY, hFFB, hFFparent] using FF.inner_le_parent i (hFFinner.symm ▸ hGinsub hi)
  have hGoriginalmass : (∑ i ∈ F, volume (Y i).shade) ≤
      P * Lc * (C : ENNReal) * ∑ i ∈ G.innerSet, volume (Y i).shade :=
    hmassG.trans (mul_le_mul_left' (Finset.sum_le_sum fun i hi =>
      measure_mono (hGref'.1.2 i hi).2) _)
  obtain ⟨iF, hiF⟩ := hF
  obtain ⟨jG, hjG⟩ := hGout
  let v := volume (Y iF).carrier
  let vR := volume (B jG).carrier
  have hv := Tube.volume_pos_and_lt_top hd (hdR.trans hR) (Y iF).toTube
  have hvR := Tube.volume_pos_and_lt_top (hd.trans_le hdR) hR (B jG)
  have hKf : 0 < volume (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E).carrier :=
    Metric.measure_closedBall_pos volume (0 : E) (by norm_num : (0 : Real) < 1)
  have hKc : 0 < volume (ConvexSpaceBody.closedBall (0 : E) 2 zero_le_two).carrier :=
    Metric.measure_closedBall_pos volume (0 : E) (by norm_num : (0 : Real) < 2)
  have hbandG : ∀ j ∈ G.outerSet, m ≤ (completeFibreW94 G.innerSet parent j).card ∧
      (completeFibreW94 G.innerSet parent j).card < 2 * m := by
    intro j hj
    have heq : completeFibreW94 G.innerSet parent j = G.fiber j := by
      simp [completeFibreW94, ShadedFactorFamily.fiber, hGp]
    rw [heq, hGfib j hj]
    exact hband j (hGsub hj)
  obtain ⟨_, _, hmaxG, hcfG, hcardG⟩ := balanced_fibres_maxDensity_and_original_frostman_w97
    F G.innerSet (fun i => (Y i).toShadedBody) ⟨iF, hiF⟩ hGF G.outerSet
    (fun j => (B j).toConvexSpaceBody) parent hGimage hGcontains
    ConvexSpaceBody.closedUnitBall (ConvexSpaceBody.closedBall (0 : E) 2 zero_le_two)
    hfine_ball (fun j hj => hcoarse_ball j (hGsub hj))
    hKf ConvexSpaceBody.closedUnitBall.isCompact.measure_lt_top
    hKc (ConvexSpaceBody.closedBall (0 : E) 2 zero_le_two).isCompact.measure_lt_top
    v vR lambda (P * Lc * (C : ENNReal)) hv.1 hv.2 hvR.1 hvR.2 hlambda hlambdafinite
    (ENNReal.mul_pos hPL0 hCe0) (ENNReal.mul_ne_top hPLfin ENNReal.coe_ne_top).lt_top
    (fun i _ => Tube.volume_carrier_eq_volume_carrier (Y i).toTube (Y iF).toTube)
    (fun j _ => Tube.volume_carrier_eq_volume_carrier (B j) (B jG))
    hfull hGoriginalmass m hm hbandG
  have hballRatio : volume (ConvexSpaceBody.closedBall (0 : E) 2 zero_le_two).carrier /
      volume (ConvexSpaceBody.closedUnitBall : ConvexSpaceBody E).carrier = 8 := by
    change volume (Metric.closedBall (0 : E) 2) / volume (Metric.closedBall (0 : E) 1) = 8
    have hvball := volume.addHaar_closedBall_mul (0 : E)
      (by norm_num : (0 : Real) ≤ 2) (by norm_num : (0 : Real) ≤ 1)
    norm_num [hdim] at hvball
    rw [hvball]
    exact ENNReal.mul_div_cancel_right hKf.ne'
      ConvexSpaceBody.closedUnitBall.isCompact.measure_ne_top
  have hCF : frostmanConstIn G.outerSet (fun j => (B j).toConvexSpaceBody)
      (ConvexSpaceBody.closedBall (0 : E) 2 zero_le_two) ≤
      (16 * P * Lc * (C : ENNReal) / lambda) *
        frostmanConstIn F (fun i => (Y i).toConvexSpaceBody) ConvexSpaceBody.closedUnitBall := by
    rw [hballRatio] at hcfG
    convert hcfG using 1 <;> simp only [div_eq_mul_inv] <;> ring
  have hcarrierG : (∑ i ∈ G.innerSet, volume (G.innerBody i).carrier) ≠ 0 := by
    have hmassGpos : 0 < ∑ i ∈ G.innerSet, volume (G.innerBody i).shade := by
      by_contra hnone
      have hz := nonpos_iff_eq_zero.mp (not_lt.mp hnone)
      rw [hz, mul_zero] at hmassG
      exact (not_le_of_gt hmassF) hmassG
    exact (hmassGpos.trans_le
      (Finset.sum_le_sum fun i _ => measure_mono (G.innerBody i).shade_subset)).ne'
  obtain ⟨j, hj, hfullj⟩ := exists_fullness_le_fiber G.toFactorFamily ⟨jG, hjG⟩ hcarrierG
  refine ⟨G, Yi, Yo, ⟨jG, hjG⟩, hGsub, hGin, hGinne, hGp, hGimage, hGi, hGo,
    hGfib, hYi, hYo, hGshade, hGfullOut, hGfullIn, hmassG, hproduct, ?_, hCF, ?_, ?_⟩
  · intro j hj
    have heq : completeFibreW94 G.innerSet parent j = G.fiber j := by
      simp [completeFibreW94, ShadedFactorFamily.fiber, hGp]
    simpa only [heq] using hcardG j hj
  · intro j hj
    have hbody : ∀ i ∈ G.fiber j,
        (G.innerBody i).toConvexSpaceBody = (Y i).toConvexSpaceBody := by
      intro i hi
      have hi' : i ∈ G.innerSet ∧ G.parent i = j := by
        simpa only [ShadedFactorFamily.fiber, Finset.mem_filter] using hi
      exact hGi i (hGinsub hi'.1)
    rw [frostmanConstIn_congr (G.fiber j) hbody, hGfib j hj]
  · refine ⟨j, hj, ?_⟩
    have hfibF : G.toFactorFamily.fiber j = G.fiber j := by
      ext i
      simp only [ShadedBody.FactorFamily.fiber, ShadedBody.ShadedFactorFamily.fiber,
        ShadedBody.ShadedFactorFamily.toFactorFamily, Finset.mem_filter]
    rw [hfibF] at hfullj
    simpa only [ShadedBody.ShadedFactorFamily.toFactorFamily, ShadedBody.coe_fullness] using hfullj

end

end Kakeya.ml1Boot.TrialRestartW94
