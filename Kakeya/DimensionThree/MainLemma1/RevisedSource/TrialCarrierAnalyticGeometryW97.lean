module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.ActualTrialGeometryW96
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.TrialWeightedFactoringW96
public import Kakeya.Tube.CardEssentiallyDistinct
public import Kakeya.Factoring.RhoTubesUndilated

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

def trialCentralParentCardConstantW97 : NNReal :=
  Real.toNNReal (Tube.card_le_of_EssDistinct.C 3 * 2 ^ (6 : Nat))

def trialOuterCarrierConstantW97 : NNReal :=
  2 * Tube.volume_le.C 3 * (trialComparableCarrierScaleW96 plankPigeonhole.C) ^ (2 : Nat) *
    plankPigeonhole.C_vol * trialCentralParentCardConstantW97

def trialInnerCarrierConstantW97 (Ctw : NNReal) : NNReal :=
  4 * (trialNearbyParentCountW96 Ctw : NNReal) * plankPigeonhole.C_vol * Tube.volume_le.C 3 *
    (trialComparableCarrierScaleW96 plankPigeonhole.C) ^ (8 : Nat)

/-- S1: construct the actual attached B2 carriers and merge all block
preimages. The local inner CF uses common-fine parents, not their global count. -/
theorem exists_actual_carriers_outer_density_and_local_frostman_w97
    (hdim : Module.finrank Real E = 3)
    {iota : Type uI} {pi : Type uP} [DecidableEq iota] [DecidableEq pi]
    {d a b rho : NNReal} (hd : 0 < d) (hda : d <= a) (hab : a <= b)
    (hbrho : b <= rho) (hrho : rho <= 1)
    (hR : trialComparableCarrierScaleW96 plankPigeonhole.C * b <= 1)
    (H : Finset iota) (Y : iota -> ShadedTube d E) (hH : H.Nonempty)
    (hball : ∀ i ∈ H, (Y i).carrier ⊆ Metric.closedBall 0 1)
    (hcentred : ∀ i ∈ H, (Y i).toTube.IsCentred)
    (J0 : Finset pi) (Tcentral : pi -> Tube rho E) (pcentral : iota -> pi)
    (himage : H.image pcentral = J0)
    (hparent : FlatPrismParentPresentation (D := 1) H Y J0 Tcentral pcentral)
    (hparent_ball : ∀ S ∈ J0, (Tcentral S).carrier ⊆ Metric.closedBall 0 2)
    (Ctw : NNReal) (hCtw : 1 <= Ctw)
    (hline : lineEssentiallyDistinctW94 J0 Tcentral Ctw)
    (U : pi -> Finset iota) (D0 : ENNReal) (hD0 : 0 < D0) (hD0finite : D0 < ⊤)
    (hreference : ∀ i ∈ H, i ∈ U (pcentral i))
    (hUparent : ∀ S ∈ J0, ∀ i ∈ U S,
      (Y i).toConvexSpaceBody <= (Tcentral S).toConvexSpaceBody)
    (hUdensity : ∀ S ∈ J0, maxDensity (U S) (fun i => (Y i).toConvexSpaceBody) <= 2 * D0)
    (Fz : (S : pi) -> ConvexSpaceBody.Factorization (completeFibreW94 H pcentral S)
      (fun i => (Y i).toConvexSpaceBody) 2)
    (hdims : ∀ S ∈ J0, IsPlankFamilyOfDimensions plankPigeonhole.C a b (Fz S).parts
      (fun q => q.convexHull_biUnion (fun i => (Y i).toConvexSpaceBody)))
    (hblockmass : ∀ S ∈ J0, ∀ q ∈ (Fz S).parts,
      (D0 / 2) * volume (q.convexHull_biUnion (fun i => (Y i).toConvexSpaceBody)).carrier <=
        ∑ i ∈ q, volume (Y i).carrier) :
    let R := trialComparableCarrierScaleW96 plankPigeonhole.C * b
    let Q := J0.biUnion (fun S => (Fz S).parts)
    ∃ (B : Finset iota -> Tube R E) (attached : Finset iota -> iota)
      (label : iota -> Finset iota) (rep : Finset iota -> Finset iota)
      (J : Finset (Finset iota)) (pB : iota -> Finset iota)
      (FF : ShadedBody.FactorFamily E iota (Finset iota)),
      Q.Nonempty ∧
      (∀ q ∈ Q, attached q ∈ q ∧ B q = (Y (attached q)).toTube.rescale R ∧
        (B q).IsCentred ∧ (B q).carrier ⊆ Metric.closedBall 0 2 ∧
        q.convexHull_biUnion (fun i => (Y i).toConvexSpaceBody) <= (B q).toConvexSpaceBody) ∧
      H.image label = Q ∧ (∀ q ∈ Q, completeFibreW94 H label q = q) ∧
      J.Nonempty ∧ J ⊆ Q ∧ Q.image rep = J ∧
      (∀ q ∈ Q, (B (rep q)).toConvexSpaceBody = (B q).toConvexSpaceBody) ∧
      Set.InjOn (fun j => (B j).toConvexSpaceBody) (J : Set (Finset iota)) ∧
      pB = rep ∘ label ∧ H.image pB = J ∧
      FF.innerSet = H ∧ FF.outerSet = J ∧ FF.parent = pB ∧
      FF.innerBody = (fun i => (Y i).toShadedBody) ∧
      FF.outerBody = (fun j => (B j).toConvexSpaceBody) ∧
      (∀ j ∈ J, FF.fiber j = (Q.filter (fun q => rep q = j)).biUnion id) ∧
      (∑ j ∈ J, ∑ i ∈ FF.fiber j, volume (Y i).shade) = ∑ i ∈ H, volume (Y i).shade ∧
      maxDensity J (fun j => (B j).toConvexSpaceBody) <=
        (trialOuterCarrierConstantW97 : ENNReal) * (rho : ENNReal) ^ (-6 : Real) *
          ((b : ENNReal) / (a : ENNReal)) ∧
      (∀ j ∈ J, (FF.fiber j).Nonempty ∧
        frostmanConstIn (FF.fiber j) (fun i => (Y i).toConvexSpaceBody) (B j).toConvexSpaceBody <=
          (trialInnerCarrierConstantW97 Ctw : ENNReal) * ((b : ENNReal) / (a : ENNReal))) := by
  classical
  let kB := trialComparableCarrierScaleW96 plankPigeonhole.C
  let R := kB * b
  let Q := J0.biUnion (fun S => (Fz S).parts)
  let W := fun q : Finset iota => q.convexHull_biUnion (fun i => (Y i).toConvexSpaceBody)
  have ha : 0 < a := hd.trans_le hda
  have hb : 0 < b := ha.trans_le hab
  have hrho0 : 0 < rho := hb.trans_le hbrho
  have hd1 : d <= 1 := hda.trans (hab.trans (hbrho.trans hrho))
  have hCw : 1 <= plankPigeonhole.C := by
    norm_num [plankPigeonhole.C, Metric.volume_comparison.C, Metric.lt_volume_convexHull.c]
  have hkB : 1 <= kB := by
    dsimp [kB, trialComparableCarrierScaleW96]
    exact le_add_of_nonneg_left (by positivity)
  have hbR : b <= R := by simpa [R] using mul_le_mul_right' hkB b
  have hdR : d <= R := hda.trans (hab.trans hbR)
  have hR0 : 0 < R := hb.trans_le hbR
  have hR1 : R <= 1 := hR
  have hCV : 0 < plankPigeonhole.C_vol := by
    dsimp [plankPigeonhole.C_vol, plankPigeonhole.C, Metric.volume_comparison.C,
      Metric.lt_volume_convexHull.c]
    positivity
  have hCv : 0 < Tube.volume_le.C 3 := by
    dsimp [Tube.volume_le.C]
    positivity
  have hQinfo : ∀ q ∈ Q, q.Nonempty ∧ q ⊆ H ∧
      IsPlankOfDimensions plankPigeonhole.C a b (W q) := by
    intro q hq
    obtain ⟨S, hS, hqS⟩ := Finset.mem_biUnion.mp hq
    refine ⟨(Fz S).toFinpartition.nonempty_of_mem_parts hqS, ?_, hdims S hS q hqS⟩
    exact ((Fz S).toFinpartition.subset hqS).trans (Finset.filter_subset _ _)
  let label := fun i => (Fz (pcentral i)).toFinpartition.part i
  have hlabel : ∀ i ∈ H, label i ∈ Q ∧ i ∈ label i := by
    intro i hi
    have hiF : i ∈ completeFibreW94 H pcentral (pcentral i) :=
      Finset.mem_filter.mpr ⟨hi, rfl⟩
    exact ⟨Finset.mem_biUnion.mpr ⟨pcentral i, hparent.mapsTo i hi,
      (Fz (pcentral i)).toFinpartition.part_mem.mpr hiF⟩,
      (Fz (pcentral i)).toFinpartition.mem_part hiF⟩
  have hfibre : ∀ q ∈ Q, completeFibreW94 H label q = q := by
    intro q hq
    obtain ⟨S, hS, hqS⟩ := Finset.mem_biUnion.mp hq
    have hqsub := (Fz S).toFinpartition.subset hqS
    ext i
    constructor
    · intro hi
      obtain ⟨hiH, hil⟩ := Finset.mem_filter.mp hi
      exact hil ▸ (hlabel i hiH).2
    · intro hi
      obtain ⟨hiH, hiS⟩ := Finset.mem_filter.mp (hqsub hi)
      refine Finset.mem_filter.mpr ⟨hiH, ?_⟩
      dsimp only [label]
      rw [hiS]
      exact (Fz S).toFinpartition.part_eq_of_mem hqS hi
  have himageLabel : H.image label = Q := by
    apply Finset.Subset.antisymm
    · exact Finset.image_subset_iff.mpr fun i hi => (hlabel i hi).1
    · intro q hq
      obtain ⟨i, hi⟩ := (hQinfo q hq).1
      have hi' : i ∈ completeFibreW94 H label q := by rwa [hfibre q hq]
      obtain ⟨hiH, hil⟩ := Finset.mem_filter.mp hi'
      exact Finset.mem_image.mpr ⟨i, hiH, hil⟩
  have hQ : Q.Nonempty := himageLabel ▸ hH.image label
  have hcarrier : ∀ q ∈ Q, ∃ i0 ∈ q,
      ((Y i0).toTube.rescale R).IsCentred ∧
      W q <= ((Y i0).toTube.rescale R).toConvexSpaceBody ∧
      volume ((Y i0).toTube.rescale R).carrier <=
        (Tube.volume_le.C 3 : ENNReal) * ((kB : ENNReal) * (b : ENNReal)) ^ (2 : Nat) := by
    intro q hq
    obtain ⟨o, u, hu, hlineq, i0, hi0, hc, hx, hy, hW, hv⟩ :=
      exists_comparable_centred_attached_carrier_w96 hdim hd hda hab
        plankPigeonhole.C hCw hR q (fun i => (Y i).toTube) (hQinfo q hq).1
        (fun i hi => hcentred i ((hQinfo q hq).2.1 hi))
        (fun i hi => hball i ((hQinfo q hq).2.1 hi)) (hQinfo q hq).2.2
    exact ⟨i0, hi0, hc, hW, hv⟩
  let attached : Finset iota -> iota := fun q =>
    if hq : q ∈ Q then (hcarrier q hq).choose else hH.choose
  let B := fun q => (Y (attached q)).toTube.rescale R
  have hB : ∀ q ∈ Q, attached q ∈ q ∧ (B q).IsCentred ∧
      W q <= (B q).toConvexSpaceBody ∧
      volume (B q).carrier <= (Tube.volume_le.C 3 : ENNReal) *
        ((kB : ENNReal) * (b : ENNReal)) ^ (2 : Nat) := by
    intro q hq
    simpa only [B, attached, dif_pos hq] using (hcarrier q hq).choose_spec
  have hBball : ∀ q ∈ Q, (B q).carrier ⊆ Metric.closedBall 0 2 := by
    intro q hq x hx
    rw [(B q).carrier_eq] at hx
    obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.mp hx
    have hzY : z ∈ (Y (attached q)).carrier :=
      (Y (attached q)).toTube.mem_carrier_of_mem_segment hz
    have hz1 := hball (attached q) ((hQinfo q hq).2.1 (hB q hq).1) hzY
    have hRreal : (R : Real) <= 1 := by exact_mod_cast hR1
    rw [Metric.mem_closedBall] at hxz hz1 ⊢
    exact (dist_triangle x z 0).trans (by linarith)
  let lower : ENNReal := (plankPigeonhole.C_vol : ENNReal)⁻¹ * (a : ENNReal) * (b : ENNReal)
  have hlower : ∀ q ∈ Q, lower <= volume (W q).carrier :=
    fun q hq => (volume_bounds_of_isPlankOfDimensions_vol hdim (hQinfo q hq).2.2).1
  have hlower0 : 0 < lower := by
    exact ENNReal.mul_pos (ENNReal.mul_pos
      (ENNReal.inv_pos.mpr ENNReal.coe_ne_top).ne'
      (by exact_mod_cast ha.ne')).ne' (by exact_mod_cast hb.ne')
  have hlowerfin : lower < ⊤ := by dsimp [lower]; finiteness
  let Avol : ENNReal := (Tube.volume_le.C 3 : ENNReal) * (kB : ENNReal) ^ (2 : Nat) *
    (plankPigeonhole.C_vol : ENNReal) * ((b : ENNReal) / (a : ENNReal))
  have hAvfin : Avol < ⊤ := by dsimp [Avol]; finiteness
  have hAvid : Avol * lower = (Tube.volume_le.C 3 : ENNReal) *
      ((kB : ENNReal) * (b : ENNReal)) ^ (2 : Nat) := by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    have ha' : (a : Real) ≠ 0 := by exact_mod_cast ha.ne'
    have hCV' : (plankPigeonhole.C_vol : Real) ≠ 0 := by exact_mod_cast hCV.ne'
    dsimp [Avol, lower]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_div,
      ENNReal.toReal_pow, ENNReal.coe_toReal]
    field_simp
    <;> ring
  have hBvolume : ∀ q ∈ Q, volume (B q).carrier <= Avol * volume (W q).carrier := by
    intro q hq
    exact (hB q hq).2.2.2.trans (hAvid ▸ mul_le_mul_left' (hlower q hq) Avol)
  obtain ⟨J, rep, hJQ, hrepimage, hrepJ, hrepB, hBinj, hmaxJ, hmerge, hsum⟩ :=
    exists_deduplicated_envelopes_and_merged_fibres_w96 Q W B Avol hAvfin
      (fun q hq => (hB q hq).2.2.1) hBvolume H (fun i => (Y i).toShadedBody)
      label himageLabel.le
  let pB := rep ∘ label
  have himageB : H.image pB = J := by rw [Finset.image_comp, himageLabel, hrepimage]
  have hJ : J.Nonempty := hrepimage ▸ hQ.image rep
  have hcontain : ∀ i ∈ H, (Y i).toConvexSpaceBody <= (B (pB i)).toConvexSpaceBody := by
    intro i hi
    rw [show (B (pB i)).toConvexSpaceBody = (B (label i)).toConvexSpaceBody from
      hrepB (label i) (hlabel i hi).1]
    exact (Finset.le_convexHull_biUnion (fun i => (Y i).toConvexSpaceBody)
      (hlabel i hi).2).trans (hB (label i) (hlabel i hi).1).2.2.1
  let FF : ShadedBody.FactorFamily E iota (Finset iota) := {
    innerSet := H
    innerBody := fun i => (Y i).toShadedBody
    outerSet := J
    outerBody := fun j => (B j).toConvexSpaceBody
    parent := pB
    parent_mem := fun i hi => himageB ▸ Finset.mem_image_of_mem pB hi
    inner_le_parent := hcontain }
  have hFF : ∀ j, FF.fiber j = completeFibreW94 H pB j := by
    intro j
    ext i
    simp only [ShadedBody.FactorFamily.fiber, completeFibreW94, FF, Finset.mem_filter]
  have hmerged : ∀ j ∈ J, FF.fiber j = (Q.filter (fun q => rep q = j)).biUnion id := by
    intro j hj
    rw [hFF j, hmerge j hj]
    exact Finset.biUnion_congr rfl fun q hq => hfibre q (Finset.mem_filter.mp hq).1
  have houter : maxDensity J (fun j => (B j).toConvexSpaceBody) <=
      (trialOuterCarrierConstantW97 : ENNReal) * (rho : ENNReal) ^ (-6 : Real) *
        ((b : ENNReal) / (a : ENNReal)) := by
    have hmaxQ : maxDensity Q W <= 2 * (J0.card : ENNReal) := by
      calc
        _ <= ∑ S ∈ J0, maxDensity (Fz S).parts W :=
          maxDensity_le_sum_of_subset_biUnion _ Finset.Subset.rfl
        _ <= ∑ _S ∈ J0, (2 : ENNReal) :=
          Finset.sum_le_sum fun S _ => (Fz S).isKatzTao
        _ = _ := by simp [mul_comm]
    have hcount : (J0.card : ENNReal) <=
        (trialCentralParentCardConstantW97 : ENNReal) * (rho : ENNReal) ^ (-6 : Real) := by
      have hc := Tube.card_le_of_EssDistinct hrho0 2 J0 Tcentral hparent_ball hparent.pairwise
      rw [hdim] at hc
      have hcE := ENNReal.ofReal_le_ofReal hc
      have hCr : 0 <= Tube.card_le_of_EssDistinct.C 3 := Tube.card_le_of_EssDistinct.C_pos.le
      have hrhor : 0 < (rho : Real) := by exact_mod_cast hrho0
      rw [ENNReal.ofReal_natCast] at hcE
      convert hcE using 1
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) ENNReal.ofReal_ne_top).mp
      simp only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.coe_toReal,
        ENNReal.toReal_ofReal (by positivity : 0 <=
          Tube.card_le_of_EssDistinct.C 3 * (2 / (rho : Real)) ^ (2 * 3))]
      rw [show (trialCentralParentCardConstantW97 : Real) =
        Tube.card_le_of_EssDistinct.C 3 * 2 ^ (6 : Nat) from
          Real.coe_toNNReal _ (by positivity)]
      norm_num [Real.rpow_neg, Real.rpow_natCast]
      field_simp
      <;> norm_num
    calc
      _ <= Avol * (2 * (J0.card : ENNReal)) := hmaxJ.trans (mul_le_mul_left' hmaxQ Avol)
      _ <= Avol * (2 * ((trialCentralParentCardConstantW97 : ENNReal) *
          (rho : ENNReal) ^ (-6 : Real))) := by gcongr
      _ = _ := by
        dsimp [Avol, trialOuterCarrierConstantW97, kB]
        push_cast
        ring
  have hinner : ∀ j ∈ J, (FF.fiber j).Nonempty ∧
      frostmanConstIn (FF.fiber j) (fun i => (Y i).toConvexSpaceBody) (B j).toConvexSpaceBody <=
        (trialInnerCarrierConstantW97 Ctw : ENNReal) * ((b : ENNReal) / (a : ENNReal)) := by
    intro j hj
    obtain ⟨q, hq, hrepq⟩ := Finset.mem_image.mp (hrepimage.symm ▸ hj)
    have hqsub : q ⊆ FF.fiber j := by
      rw [hmerged j hj]
      exact fun i hi => Finset.mem_biUnion.mpr ⟨q, Finset.mem_filter.mpr ⟨hq, hrepq⟩, hi⟩
    have hA : (FF.fiber j).Nonempty := (hQinfo q hq).1.mono hqsub
    have hAsub : FF.fiber j ⊆ H := by rw [hFF]; exact Finset.filter_subset _ _
    have hcontained : ∀ i ∈ FF.fiber j, (Y i).toConvexSpaceBody <= (B j).toConvexSpaceBody := by
      intro i hi
      have hi' : i ∈ completeFibreW94 H pB j := by rwa [hFF] at hi
      obtain ⟨hiH, hij⟩ := Finset.mem_filter.mp hi'
      simpa only [hij] using hcontain i hiH
    have hApos : 0 < ∑ i ∈ FF.fiber j, volume (Y i).carrier := by
      obtain ⟨i, hi⟩ := hA
      exact (Tube.volume_pos_and_lt_top hd hd1 (Y i).toTube).1.trans_le
        (Finset.single_le_sum (f := fun i => volume (Y i).carrier) (fun _ _ => zero_le) hi)
    have hAfin : (∑ i ∈ FF.fiber j, volume (Y i).carrier) < ⊤ :=
      ENNReal.sum_lt_top.mpr fun i _ => (Y i).toConvexSpaceBody.isCompact.measure_lt_top
    have hmass : (D0 / 2) * lower <= ∑ i ∈ FF.fiber j, volume (Y i).carrier := by
      obtain ⟨S, hS, hqS⟩ := Finset.mem_biUnion.mp hq
      exact ((mul_le_mul_left' (hlower q hq) (D0 / 2)).trans
        (hblockmass S hS q hqS)).trans (Finset.sum_le_sum_of_subset hqsub)
    let meeting := commonFineMeetingParentsW96 H (fun i => (Y i).toTube) J0 Tcentral (B j)
    have hcover : FF.fiber j ⊆ meeting.biUnion U := by
      intro i hi
      have hiH := hAsub hi
      have hS := hparent.mapsTo i hiH
      have hiU := hreference i hiH
      exact Finset.mem_biUnion.mpr ⟨pcentral i,
        Finset.mem_filter.mpr ⟨hS, i, hiH, hUparent _ hS i hiU, hcontained i hi⟩, hiU⟩
    have hcount : (meeting.card : ENNReal) <=
        (trialNearbyParentCountW96 Ctw : ENNReal) * (kB : ENNReal) ^ (6 : Nat) := by
      have hc := card_assigned_parents_meeting_exact_cell_w96 hdim hd
        (hda.trans (hab.trans hbrho)) hdR hrho H (fun i => (Y i).toTube)
        J0 Tcentral (B j) Ctw hCtw hball hparent_ball hline
      have hratio : max 1 ((R : Real) / (rho : Real)) <= (kB : Real) := by
        apply max_le (by exact_mod_cast hkB)
        apply (div_le_iff₀ (by exact_mod_cast hrho0)).mpr
        exact_mod_cast mul_le_mul_left' hbrho kB
      have hc' : (meeting.card : Real) <=
          (trialNearbyParentCountW96 Ctw : Real) * (kB : Real) ^ (6 : Nat) :=
        hc.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hratio _)
          (Nat.cast_nonneg _))
      exact_mod_cast hc'
    have hmax : maxDensity (FF.fiber j) (fun i => (Y i).toConvexSpaceBody) <=
        2 * (trialNearbyParentCountW96 Ctw : ENNReal) * (kB : ENNReal) ^ (6 : Nat) * D0 := by
      calc
        _ <= ∑ S ∈ meeting, maxDensity (U S) (fun i => (Y i).toConvexSpaceBody) :=
          maxDensity_le_sum_of_subset_biUnion _ hcover
        _ <= ∑ _S ∈ meeting, 2 * D0 :=
          Finset.sum_le_sum fun S hS => hUdensity S (Finset.mem_filter.mp hS).1
        _ = (meeting.card : ENNReal) * (2 * D0) := by simp
        _ <= ((trialNearbyParentCountW96 Ctw : ENNReal) * (kB : ENNReal) ^ (6 : Nat)) *
            (2 * D0) := mul_le_mul' hcount le_rfl
        _ = _ := by ring
    refine ⟨hA, ?_⟩
    have hBfin : volume (B j).carrier < ⊤ := (B j).toConvexSpaceBody.isCompact.measure_lt_top
    have hdensity : 0 < densityIn (FF.fiber j) (fun i => (Y i).toConvexSpaceBody)
        (B j).toConvexSpaceBody := by
      rw [densityIn_of_all_le hcontained]
      exact ENNReal.div_pos hApos.ne' hBfin.ne
    let upper : ENNReal := (Tube.volume_le.C 3 : ENNReal) *
      ((kB : ENNReal) * (b : ENNReal)) ^ (2 : Nat)
    have hupper0 : 0 < upper := by dsimp [upper]; positivity
    have hupperfin : upper < ⊤ := by dsimp [upper]; finiteness
    have hdenom : (D0 / 2) * lower / upper <=
        densityIn (FF.fiber j) (fun i => (Y i).toConvexSpaceBody) (B j).toConvexSpaceBody := by
      rw [densityIn_of_all_le hcontained]
      exact ENNReal.div_le_div hmass (hB j (hJQ hj)).2.2.2
    rw [frostmanConstIn_eq_frostmanConstant,
      frostmanConstant_eq_maxDensity_div hdensity hcontained]
    apply (ENNReal.div_le_div hmax hdenom).trans
    have hpaid0 : 0 < (D0 / 2) * lower / upper :=
      ENNReal.div_pos (ENNReal.mul_pos
        (ENNReal.div_pos hD0.ne' (by norm_num : (2 : ENNReal) ≠ ⊤)).ne'
        hlower0.ne').ne' hupperfin.ne
    have hleftfin : 2 * (trialNearbyParentCountW96 Ctw : ENNReal) *
        (kB : ENNReal) ^ (6 : Nat) * D0 / ((D0 / 2) * lower / upper) ≠ ⊤ := by
      apply ENNReal.div_ne_top _ hpaid0.ne'
      finiteness
    apply le_of_eq
    apply (ENNReal.toReal_eq_toReal_iff' hleftfin (by finiteness)).mp
    have hD' : D0.toReal ≠ 0 := (ENNReal.toReal_pos hD0.ne' hD0finite.ne).ne'
    have ha' : (a : Real) ≠ 0 := by exact_mod_cast ha.ne'
    have hb' : (b : Real) ≠ 0 := by exact_mod_cast hb.ne'
    have hkB' : (kB : Real) ≠ 0 := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hkB).ne'
    have hCV' : (plankPigeonhole.C_vol : Real) ≠ 0 := by exact_mod_cast hCV.ne'
    have hCv' : (Tube.volume_le.C 3 : Real) ≠ 0 := by exact_mod_cast hCv.ne'
    dsimp [lower, upper, trialInnerCarrierConstantW97]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow,
      ENNReal.toReal_inv, ENNReal.toReal_ofNat, ENNReal.toReal_natCast, ENNReal.coe_toReal,
      NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_natCast, NNReal.coe_ofNat]
    change _ = 4 * (trialNearbyParentCountW96 Ctw : Real) * (plankPigeonhole.C_vol : Real) *
      (Tube.volume_le.C 3 : Real) * (kB : Real) ^ (8 : Nat) * ((b : Real) / (a : Real))
    field_simp
    <;> norm_num
    <;> ring
  refine ⟨B, attached, label, rep, J, pB, FF, hQ, ?_, himageLabel, hfibre,
    hJ, hJQ, hrepimage, hrepB, hBinj, rfl, himageB, rfl, rfl, rfl, rfl, rfl,
    hmerged, ?_, houter, hinner⟩
  · intro q hq
    exact ⟨(hB q hq).1, rfl, (hB q hq).2.1, hBball q hq, (hB q hq).2.2.1⟩
  · simpa only [hFF] using hsum

end

end Kakeya.ml1Boot.TrialRestartW94
