module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceWindowTrialW98
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceCanonicalTransportW97

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody
open scoped ENNReal NNReal

namespace Kakeya.ml1Boot.TrialRestartW94

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
attribute [local instance] Classical.propDecidable

universe uE uI

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

open RevisedLiteralProfileInterfaceFormalizerW87

theorem exists_synchronized_window_fine_lift_w101
    {p : Params} {beta gammaZero xiMin : Real} {xi : Fin (p.N + 1) -> Real}
    {M : Nat} (hp : SourcePassNumericsW95 p beta gammaZero xi xiMin M)
    (gamma : Real) (Cwork Ctw Ccell BF : NNReal)
    {delta : NNReal} (hd : 0 < delta) (hd1 : delta < 1)
    {iota : Type uI} [DecidableEq iota] {A : Finset iota}
    {Y : iota -> ShadedTube delta E}
    (U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Cwork)
    (Uext : CanonicalProfileNetW87 A (fun i => (Y i).toTube) (M * M) Cwork)
    (hA : A.Nonempty) (reg : SourceRegularizedWorkingTowerW95 U Ctw Ccell)
    (block : ActualSourceDividingBlockW95 U p BF) (loss : NNReal)
    (selections : ActualSameMassSelectionsW95 block loss)
    (Rnorm Cext Cnorm CtwNorm CcellNorm : NNReal)
    (aux : AuxiliaryHalfEtaThresholdsW97.{uE, uI} (E := E) p xi gamma CtwNorm CcellNorm M)
    (calls : ActualEligibleTrialCallsW97 Uext block selections xi gamma
      Rnorm Cext Cnorm CtwNorm CcellNorm aux)
    (drops : ∀ R (hR : R ∈ actualEligibleThetaParentsW97 selections Cext (aux.inner block.label)),
      WindowDetailedTrialDropW98 (calls.normalization R hR).cells p.ε
        (p.η (block.label.val + 1) / 2) (aux.Ktr block.label))
    (hpos : 0 < ∑ i ∈ selections.fineFamily, volume (selections.fineShading i).shade) :
    ∃ (level : Fin (M + 1)) (middle F : Finset iota)
      (Z : iota -> ShadedTube (Tube.gridScale delta M block.b.val) E)
      (W : iota -> ShadedTube delta E),
      F.Nonempty ∧ F ⊆ selections.fineFamily ∧
      (∀ i ∈ F, (W i).toTube = (Y i).toTube ∧
        (W i).shade ⊆ (selections.fineShading i).shade ∧ 0 < volume (W i).shade) ∧
      middle = F.image (U.cover.assign block.b.val) ∧ middle ⊆ selections.secondFamily ∧
      (∀ Q ∈ middle, (Z Q).toTube = U.cover.tube block.b.val Q ∧
        (Z Q).shade ⊆ (selections.secondShading Q).shade ∧
        ∃ R, ∃ hR : R ∈ actualEligibleThetaParentsW97 selections Cext (aux.inner block.label),
          Q ∈ (drops R hR).Fplus ∧ (drops R hR).level = level ∧
          (Z Q).shade ⊆ ((U.cover.tube block.a.val R).rescaleMap (Rnorm : Real)) ⁻¹'
            ((drops R hR).Yplus Q).shade) ∧
      (∀ Q ∈ middle,
        (∑ i ∈ completeFibreW94 F (U.cover.assign block.b.val) Q, volume (W i).shade) =
          (selections.commonMass : ENNReal)⁻¹ * volume (Z Q).shade) ∧
      ((M + 1 : Nat) : ENNReal)⁻¹ * (1 / 2 : ENNReal) *
        trialRetainedFractionW94
          (Tube.gridScale delta M block.b.val / Tube.gridScale delta M block.a.val)
            (aux.Ktr block.label) *
        (∑ i ∈ selections.fineFamily, volume (selections.fineShading i).shade) <=
          ∑ i ∈ F, volume (W i).shade := by
  let ordinary := fun R hR => (drops R hR).toDetailedTrialDropW94
  obtain ⟨middle0, F0, Z0, W0, hmiddle0, hmiddleSub, hZ0, hAll, hOrigin,
    hF0eq, hF0, hF0sub, hF0image, hW0, hF0mass, hret0⟩ :=
    exists_actual_trial_drop_fine_lift_w97 Uext block selections xi gamma
      Rnorm Cext Cnorm CtwNorm CcellNorm aux calls ordinary hd hd1 hp.M_pos hA reg hpos
  choose origin originMem originF originPos originVol using hOrigin
  let parent := U.cover.assign block.b.val
  let levelOf : iota -> Fin (M + 1) := fun Q =>
    if hQ : Q ∈ middle0 then (drops (origin Q hQ) (originMem Q hQ)).level else 0
  let positive := F0.filter (fun i => 0 < volume (W0 i).shade)
  let weight := fun l : Fin (M + 1) =>
    ∑ i ∈ positive.filter (fun i => levelOf (parent i) = l), volume (W0 i).shade
  obtain ⟨level, hlevel, hmax⟩ := Finset.exists_max_image Finset.univ weight Finset.univ_nonempty
  let F := positive.filter (fun i => levelOf (parent i) = level)
  let middle := F.image parent
  have hFF0 : F ⊆ F0 := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have hFsub : F ⊆ selections.fineFamily := hFF0.trans hF0sub
  have hmiddle : middle ⊆ middle0 := by
    rw [← hF0image]
    exact Finset.image_subset_image hFF0
  have hpositiveSum : (∑ i ∈ positive, volume (W0 i).shade) =
      ∑ i ∈ F0, volume (W0 i).shade := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i hi hin
    apply le_antisymm _ bot_le
    exact le_of_not_gt (fun h => hin (Finset.mem_filter.mpr ⟨hi, h⟩))
  have hsumWeight : (∑ l : Fin (M + 1), weight l) = ∑ i ∈ F0, volume (W0 i).shade := by
    rw [← hpositiveSum]
    exact Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) _
  have hmaxMass : (∑ i ∈ F0, volume (W0 i).shade) <=
      ((M + 1 : Nat) : ENNReal) * weight level := by
    rw [← hsumWeight]
    calc
      (∑ l : Fin (M + 1), weight l) <= ∑ _l : Fin (M + 1), weight level :=
        Finset.sum_le_sum (fun l hl => hmax l hl)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hret : ((M + 1 : Nat) : ENNReal)⁻¹ * (1 / 2 : ENNReal) *
      trialRetainedFractionW94
        (Tube.gridScale delta M block.b.val / Tube.gridScale delta M block.a.val)
          (aux.Ktr block.label) *
      (∑ i ∈ selections.fineFamily, volume (selections.fineShading i).shade) <=
        ∑ i ∈ F, volume (W0 i).shade := by
    have hNzero : ((M + 1 : Nat) : ENNReal) ≠ 0 := by norm_num
    have hNtop : ((M + 1 : Nat) : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
    have h := (ENNReal.inv_mul_le_iff hNzero hNtop).mpr (hret0.trans hmaxMass)
    simpa only [mul_assoc] using h
  have hretPos : 0 < ((M + 1 : Nat) : ENNReal)⁻¹ * (1 / 2 : ENNReal) *
      trialRetainedFractionW94
        (Tube.gridScale delta M block.b.val / Tube.gridScale delta M block.a.val)
          (aux.Ktr block.label) *
      (∑ i ∈ selections.fineFamily, volume (selections.fineShading i).shade) := by
    have hdpos : 0 < Tube.gridScale delta M block.b.val / Tube.gridScale delta M block.a.val :=
      div_pos (Tube.gridScale_pos hd M _) (Tube.gridScale_pos hd M _)
    have hdsmall : Tube.gridScale delta M block.b.val / Tube.gridScale delta M block.a.val < 1 := by
      apply block.block_long.trans_lt
      simpa only [NNReal.one_rpow] using NNReal.rpow_lt_rpow hd1 hp.epsilon_pos
    have hlog : 0 < 1 + Real.log
        (1 / ((Tube.gridScale delta M block.b.val / Tube.gridScale delta M block.a.val : NNReal) : Real)) := by
      have hratio : (1 : Real) <= 1 /
          ((Tube.gridScale delta M block.b.val / Tube.gridScale delta M block.a.val : NNReal) : Real) :=
        (le_div_iff₀ (by exact_mod_cast hdpos)).mpr (by
          rw [one_mul]
          exact_mod_cast hdsmall.le)
      exact add_pos_of_pos_of_nonneg zero_lt_one (Real.log_nonneg hratio)
    have htrial : 0 < trialRetainedFractionW94
        (Tube.gridScale delta M block.b.val / Tube.gridScale delta M block.a.val) (aux.Ktr block.label) :=
      ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hlog _)
    exact ENNReal.mul_pos
      (ENNReal.mul_pos
        (ENNReal.mul_pos (by simp) (by norm_num)).ne' htrial.ne').ne' hpos.ne'
  have hF : F.Nonempty := by
    by_contra hn
    have hz : ∑ i ∈ F, volume (W0 i).shade = 0 := by
      rw [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.sum_empty]
    exact (not_le_of_gt hretPos) (hz ▸ hret)
  refine ⟨level, middle, F, Z0, W0, hF, hFsub, ?_, rfl,
    hmiddle.trans hmiddleSub, ?_, ?_, hret⟩
  · intro i hi
    exact ⟨((hW0 i (hFF0 hi)).1).trans (selections.fine_same_tube i (hFsub hi)),
      (hW0 i (hFF0 hi)).2, (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2⟩
  · intro Q hQ
    have hQ0 := hmiddle hQ
    have hlevelQ : levelOf Q = level := by
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hQ
      exact (Finset.mem_filter.mp hi).2
    have hlevelDrop : (drops (origin Q hQ0) (originMem Q hQ0)).level = level := by
      simpa only [levelOf, dif_pos hQ0] using hlevelQ
    have hshade := (hAll (origin Q hQ0) (originMem Q hQ0) Q
      (originF Q hQ0) (originPos Q hQ0)).2
    refine ⟨(hZ0 Q hQ0).1, (hZ0 Q hQ0).2,
      origin Q hQ0, originMem Q hQ0, originF Q hQ0, hlevelDrop, ?_⟩
    rw [hshade]
    exact Set.inter_subset_right
  · intro Q hQ
    rw [← hF0mass Q (hmiddle hQ)]
    apply Finset.sum_subset (Finset.filter_subset_filter _ hFF0)
    intro i hi hin
    obtain ⟨hi0, hiparent⟩ := Finset.mem_filter.mp hi
    apply le_antisymm _ bot_le
    apply le_of_not_gt
    intro hposi
    have hlevelQ : levelOf Q = level := by
      obtain ⟨j, hj, hjQ⟩ := Finset.mem_image.mp hQ
      exact hjQ ▸ (Finset.mem_filter.mp hj).2
    have hiF : i ∈ F := Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨hi0, hposi⟩, by simpa only [parent, hiparent] using hlevelQ⟩
    exact hin (Finset.mem_filter.mpr ⟨hiF, hiparent⟩)
theorem exists_drop_working_grid_rounding_w101
    (M : Nat) (hM : 1 <= M) {delta working : NNReal} (hd : 0 < delta) (hd1 : delta < 1)
    (hdw : delta <= working) (hw1 : working < 1) :
    ∃ ell : Fin (M + 1), ell.val < M ∧
      Tube.gridScale delta M (ell.val + 1) <= working ∧
      working < Tube.gridScale delta M ell.val := by
  let eligible := (Finset.univ : Finset (Fin (M + 1))).filter
    (fun ell => working < Tube.gridScale delta M ell.val)
  have hzero : (0 : Fin (M + 1)) ∈ eligible := by
    simp only [eligible, Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_zero,
      Tube.gridScale_zero]
    exact hw1
  obtain ⟨ell, hell, hmax⟩ := Finset.exists_max_image eligible Fin.val ⟨0, hzero⟩
  have hupper := (Finset.mem_filter.mp hell).2
  have hellM : ell.val < M := by
    have he : ell.val <= M := Nat.le_of_lt_succ ell.isLt
    by_contra hn
    have heq : ell.val = M := by omega
    rw [heq, Tube.gridScale_self delta hM] at hupper
    exact (not_lt_of_ge hdw) hupper
  refine ⟨ell, hellM, ?_, hupper⟩
  by_contra hn
  let next : Fin (M + 1) := ⟨ell.val + 1, by omega⟩
  have hnext : next ∈ eligible := Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, lt_of_not_ge hn⟩
  have h := hmax next hnext
  change ell.val + 1 <= ell.val at h
  omega
theorem exists_drop_working_scale_funding_w101
    {p : Params} {beta gammaZero xiMin : Real} {xi : Fin (p.N + 1) -> Real}
    {M : Nat} (hp : SourcePassNumericsW95 p beta gammaZero xi xiMin M)
    (Lgeom : NNReal) (hLgeom : 2 <= Lgeom) :
    ∃ cutoff : NNReal, 0 < cutoff ∧ cutoff < 1 ∧
      ∀ {delta theta tau r : NNReal}, 0 < delta -> delta < cutoff ->
        0 < theta -> theta <= 1 -> delta <= tau -> tau <= theta ->
        tau / theta <= delta ^ p.ε ->
        ((tau / theta : NNReal) : ENNReal) ^ (1 - 3 * p.ε / 2) <= (r : ENNReal) ->
        (r : ENNReal) <= ((tau / theta : NNReal) : ENNReal) ^ (3 * p.ε / 2) ->
        0 < Lgeom * theta * r ∧ Lgeom * theta * r < 1 ∧
        2 * tau <= Lgeom * theta * r ∧
        theta * r <= Lgeom * theta * r ∧
        (∃ ell : Fin (M + 1), ell.val < M ∧
          Tube.gridScale delta M (ell.val + 1) <= Lgeom * theta * r ∧
          Lgeom * theta * r < Tube.gridScale delta M ell.val) := by
  let e : Real := 3 * p.ε ^ 2 / 2
  have he : 0 < e := by
    dsimp [e]
    exact div_pos (mul_pos (by norm_num) (sq_pos_of_pos hp.epsilon_pos)) (by norm_num)
  have hsmall : ∀ᶠ delta : NNReal in nhdsWithin 0 (Set.Ioi 0),
      delta < 1 ∧ (2 * (Lgeom : ENNReal)) <= (delta : ENNReal) ^ (-e) := by
    filter_upwards [eventually_le_nhdsGT (c := (1 / 2 : NNReal)) (by norm_num),
      eventually_finite_const_le_rpow_neg (c := 2 * (Lgeom : ENNReal)) (by finiteness) he]
      with delta hd1 hpay
    exact ⟨hd1.trans_lt (by norm_num), hpay⟩
  obtain ⟨c, hc, hcut⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hsmall
  let cutoff := min c (1 / 2)
  refine ⟨cutoff, lt_min hc (by norm_num), (min_le_right _ _).trans_lt (by norm_num), ?_⟩
  intro delta theta tau r hd hdcut htheta htheta1 hdtau htautheta hblock hlow hupp
  obtain ⟨hd1, hpayE⟩ := hcut ⟨hd, hdcut.trans_le (min_le_left _ _)⟩
  have htau : 0 < tau := hd.trans_le hdtau
  have hdpos : 0 < tau / theta := div_pos htau htheta
  have hdsmall : tau / theta <= 1 := (div_le_one htheta).mpr htautheta
  have hlow' : (tau / theta) ^ (1 - 3 * p.ε / 2) <= r := by
    rw [← ENNReal.coe_rpow_of_ne_zero hdpos.ne'] at hlow
    exact ENNReal.coe_le_coe.mp hlow
  have hupp' : r <= (tau / theta) ^ (3 * p.ε / 2) := by
    rw [← ENNReal.coe_rpow_of_ne_zero hdpos.ne'] at hupp
    exact ENNReal.coe_le_coe.mp hupp
  have hratio : tau / theta <= r := by
    calc
      tau / theta = (tau / theta) ^ (1 : Real) := (NNReal.rpow_one _).symm
      _ <= (tau / theta) ^ (1 - 3 * p.ε / 2) :=
        NNReal.rpow_le_rpow_of_exponent_ge hdpos hdsmall (by linarith only [hp.epsilon_pos])
      _ <= r := hlow'
  have hr : 0 < r := hdpos.trans_le hratio
  have hL : 0 < Lgeom := (by norm_num : (0 : NNReal) < 2).trans_le hLgeom
  have hpower : r <= delta ^ e := by
    calc
      r <= (tau / theta) ^ (3 * p.ε / 2) := hupp'
      _ <= (delta ^ p.ε) ^ (3 * p.ε / 2) :=
        NNReal.rpow_le_rpow hblock (by linarith only [hp.epsilon_pos])
      _ = delta ^ e := by rw [← NNReal.rpow_mul]; congr 1; dsimp [e]; ring
  have hpay : 2 * Lgeom <= delta ^ (-e) := by
    rw [← ENNReal.coe_rpow_of_ne_zero hd.ne'] at hpayE
    exact_mod_cast hpayE
  have hpaid : Lgeom * delta ^ e <= 1 / 2 := by
    have h := mul_le_mul_of_nonneg_right hpay (delta ^ e).coe_nonneg
    rw [← NNReal.rpow_add hd.ne'] at h
    simp only [neg_add_cancel, NNReal.rpow_zero] at h
    nlinarith
  have hworkSmall : Lgeom * theta * r < 1 := by
    have h : Lgeom * theta * r <= Lgeom * delta ^ e := by
      calc
        _ <= Lgeom * 1 * delta ^ e := by gcongr
        _ = _ := by rw [mul_one]
    exact (h.trans hpaid).trans_lt (by norm_num)
  have htwice : 2 * tau <= Lgeom * theta * r := by
    have hbase : tau <= theta * r := (div_le_iff₀ htheta).mp hratio |>.trans_eq (mul_comm _ _)
    calc
      2 * tau <= 2 * (theta * r) := mul_le_mul_left' hbase _
      _ <= Lgeom * (theta * r) := mul_le_mul_right' hLgeom _
      _ = _ := by ring
  have hworkLower : theta * r <= Lgeom * theta * r := by
    have hL1 : 1 <= Lgeom := (by norm_num : (1 : NNReal) <= 2).trans hLgeom
    calc theta * r = 1 * (theta * r) := (one_mul _).symm
      _ <= Lgeom * (theta * r) := mul_le_mul_right' hL1 _
      _ = _ := by ring
  refine ⟨mul_pos (mul_pos hL htheta) hr, hworkSmall, htwice, hworkLower, ?_⟩
  apply exists_drop_working_grid_rounding_w101 M hp.M_pos hd hd1 _ hworkSmall
  exact hdtau.trans ((by nlinarith : tau <= 2 * tau).trans htwice)
theorem exists_canonical_assignment_refinement_w101
    {M : Nat} (Ccan CbaseTw CbaseCell Cwork Ctw Ccell : NNReal)
    (hCbaseTw : 1 <= CbaseTw) (hCtw : 1 <= Ctw) :
    ∃ Cdegree : NNReal, 1 <= Cdegree ∧
      ∀ {delta : NNReal}, 0 < delta -> delta <= 1 ->
      ∀ {iota : Type uI} [DecidableEq iota]
        {B : Finset iota} {V : iota -> ShadedTube delta E}
        (U0 : CanonicalProfileNetW87 B (fun i => (V i).toTube) M Ccan)
        (current : RetainedStateW94 B V) (A : Finset iota)
        (U : CanonicalProfileNetW87 A (fun i => (current.shading i).toTube) M Cwork),
        A ⊆ current.active ->
        SourceRegularizedWorkingTowerW95 U0 CbaseTw CbaseCell ->
        SourceRegularizedWorkingTowerW95 U Ctw Ccell ->
      ∀ (q : Fin (M + 1)) (F : Finset iota) (weight : iota -> ENNReal)
        (parent : iota -> iota), F ⊆ A -> (0 < ∑ i ∈ F, weight i) ->
        ∃ G : Finset iota, G.Nonempty ∧ G ⊆ F ∧
          (Cdegree : ENNReal)⁻¹ * (∑ i ∈ F, weight i) <= ∑ i ∈ G, weight i ∧
          (∀ i ∈ G, ∀ j ∈ G, U0.cover.assign q.val i = U0.cover.assign q.val j ->
            parent (U.cover.assign q.val i) = parent (U.cover.assign q.val j)) := by
  obtain ⟨Cdegree, hCdegree, hincidence⟩ :=
    actual_working_canonical_incidence_w97 (E := E) CbaseTw Ctw hCbaseTw hCtw
  refine ⟨Cdegree, hCdegree, ?_⟩
  intro delta hd hd1 iota inst B V U0 current A U hA reg0 reg q F weight parent hFA hmass
  obtain ⟨hdegreeLeft, hdegreeRight, hparts⟩ := hincidence hd hd1 U0 current A U hA reg0 reg q
  let edges := A.image (fun i => (U.cover.assign q.val i, U0.cover.assign q.val i))
  let nodes := F.image (U0.cover.assign q.val)
  let fibre := fun w => F.filter (fun i => U0.cover.assign q.val i = w)
  let parents := fun w => (fibre w).image (fun i => parent (U.cover.assign q.val i))
  have hnodesMap : ∀ i ∈ F, U0.cover.assign q.val i ∈ nodes := fun i hi =>
    Finset.mem_image_of_mem _ hi
  have hparentsNonempty : ∀ w ∈ nodes, (parents w).Nonempty := by
    intro w hw
    obtain ⟨i, hi, hiw⟩ := Finset.mem_image.mp hw
    exact ⟨parent (U.cover.assign q.val i), Finset.mem_image_of_mem _
      (Finset.mem_filter.mpr ⟨hi, hiw⟩)⟩
  have hparentsCard : ∀ w ∈ nodes, ((parents w).card : ENNReal) <= Cdegree := by
    intro w hw
    let es := edges.filter (fun e => e.2 = w)
    have hsub : parents w ⊆ es.image (fun e => parent e.1) := by
      intro S hS
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hS
      obtain ⟨hiF, hiw⟩ := Finset.mem_filter.mp hi
      exact Finset.mem_image.mpr ⟨(U.cover.assign q.val i, U0.cover.assign q.val i),
        Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ (hFA hiF), hiw⟩, rfl⟩
    have hwcan : w ∈ canonicalAncestorFamilyW87 U0 current.active q := by
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
      exact Finset.mem_image_of_mem _ (hA (hFA hi))
    have hcard : (parents w).card <= es.card :=
      (Finset.card_le_card hsub).trans (Finset.card_image_le)
    calc
      ((parents w).card : ENNReal) <= (es.card : ENNReal) := by exact_mod_cast hcard
      _ <= (Cdegree : ENNReal) := by exact_mod_cast hdegreeRight w hwcan
  let contribution := fun w S =>
    ∑ i ∈ (fibre w).filter (fun i => parent (U.cover.assign q.val i) = S), weight i
  have hbest : ∀ w ∈ nodes, ∃ S ∈ parents w,
      (∑ i ∈ fibre w, weight i) <= (Cdegree : ENNReal) * contribution w S := by
    intro w hw
    obtain ⟨S, hS, hmax⟩ := Finset.exists_max_image (parents w) (contribution w)
      (hparentsNonempty w hw)
    refine ⟨S, hS, ?_⟩
    have hsum : (∑ S ∈ parents w, contribution w S) = ∑ i ∈ fibre w, weight i :=
      Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem _ hi) weight
    calc
      _ = ∑ S ∈ parents w, contribution w S := hsum.symm
      _ <= ∑ _S ∈ parents w, contribution w S :=
        Finset.sum_le_sum (fun T hT => hmax T hT)
      _ = ((parents w).card : ENNReal) * contribution w S := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ <= (Cdegree : ENNReal) * contribution w S :=
        mul_le_mul_right' (hparentsCard w hw) _
  have hFnonempty : F.Nonempty := by
    by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.sum_empty] at hmass
    exact (lt_irrefl _ hmass)
  obtain ⟨default, hdefault⟩ := hFnonempty
  choose selected selectedMem selectedMass using hbest
  let choice := fun w => if hw : w ∈ nodes then selected w hw else default
  let G := F.filter (fun i => parent (U.cover.assign q.val i) = choice (U0.cover.assign q.val i))
  have hGsub : G ⊆ F := Finset.filter_subset _ _
  have hGfibre : ∀ w,
      G.filter (fun i => U0.cover.assign q.val i = w) =
        (fibre w).filter (fun i => parent (U.cover.assign q.val i) = choice w) := by
    intro w
    ext i
    simp only [G, fibre, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hi, his⟩, hiw⟩
      rw [hiw] at his
      exact ⟨⟨hi, hiw⟩, his⟩
    · rintro ⟨⟨hi, hiw⟩, his⟩
      refine ⟨⟨hi, ?_⟩, hiw⟩
      simpa only [hiw] using his
  have hGmass : (∑ i ∈ F, weight i) <= (Cdegree : ENNReal) * ∑ i ∈ G, weight i := by
    have hsumF := Finset.sum_fiberwise_of_maps_to hnodesMap weight
    have hsumG := Finset.sum_fiberwise_of_maps_to
      (fun i hi => hnodesMap i (hGsub hi)) weight
    calc
      _ = ∑ w ∈ nodes, ∑ i ∈ fibre w, weight i := hsumF.symm
      _ <= ∑ w ∈ nodes, (Cdegree : ENNReal) * contribution w (choice w) := by
        apply Finset.sum_le_sum
        intro w hw
        simpa only [choice, dif_pos hw] using selectedMass w hw
      _ = (Cdegree : ENNReal) * ∑ i ∈ G, weight i := by
        rw [← hsumG, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro w hw
        congr 1
        dsimp only [contribution]
        rw [hGfibre w]
  have hGnonempty : G.Nonempty := by
    by_contra hn
    rw [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.sum_empty, mul_zero] at hGmass
    exact (not_le_of_gt hmass) hGmass
  refine ⟨G, hGnonempty, hGsub, ?_, ?_⟩
  · exact (ENNReal.inv_mul_le_iff
      (by exact_mod_cast (zero_lt_one.trans_le hCdegree).ne') ENNReal.coe_ne_top).mpr hGmass
  · intro i hi j hj hij
    obtain ⟨_, hiChoice⟩ := Finset.mem_filter.mp hi
    obtain ⟨_, hjChoice⟩ := Finset.mem_filter.mp hj
    exact hiChoice.trans ((congrArg choice hij).trans hjChoice.symm)
theorem exists_drop_middle_recut_w101
    {delta tau : NNReal} {iota : Type uI} [DecidableEq iota]
    (F G : Finset iota) (hGF : G ⊆ F) (parent : iota -> iota)
    (Z : iota -> ShadedTube tau E) (W : iota -> ShadedTube delta E)
    (common : NNReal) (hc : 0 < common)
    (hfibre : ∀ Q ∈ F.image parent,
      (∑ i ∈ completeFibreW94 F parent Q, volume (W i).shade) =
        (common : ENNReal)⁻¹ * volume (Z Q).shade) :
    ∃ Znew : iota -> ShadedTube tau E,
      (∀ Q, (Znew Q).toTube = (Z Q).toTube ∧ (Znew Q).shade ⊆ (Z Q).shade) ∧
      (∀ Q ∈ G.image parent,
        (∑ i ∈ completeFibreW94 G parent Q, volume (W i).shade) =
          (common : ENNReal)⁻¹ * volume (Znew Q).shade) := by
  let target := fun Q => (common : ENNReal) *
    ∑ i ∈ completeFibreW94 G parent Q, volume (W i).shade
  have htarget : ∀ Q ∈ G.image parent, target Q <= volume (Z Q).shade := by
    intro Q hQ
    have hQF : Q ∈ F.image parent := Finset.image_mono parent hGF hQ
    have hf : completeFibreW94 G parent Q ⊆ completeFibreW94 F parent Q := by
      intro i hi
      obtain ⟨hiG, hiQ⟩ := Finset.mem_filter.mp hi
      exact Finset.mem_filter.mpr ⟨hGF hiG, hiQ⟩
    calc
      target Q <= (common : ENNReal) *
          ∑ i ∈ completeFibreW94 F parent Q, volume (W i).shade :=
        mul_le_mul_left' (Finset.sum_le_sum_of_subset hf) _
      _ = volume (Z Q).shade := by
        rw [hfibre Q hQF, ← mul_assoc,
          ENNReal.mul_inv_cancel (ENNReal.coe_ne_zero.mpr hc.ne') ENNReal.coe_ne_top, one_mul]
  have hcut : ∀ Q ∈ G.image parent, ∃ S : Set E,
      S ⊆ (Z Q).shade ∧ MeasurableSet S ∧ volume S = target Q := by
    intro Q hQ
    exact exists_volume_cut_w97 (Z Q).shade (Z Q).measurableSet_shade
      ((measure_mono (Z Q).shade_subset).trans_lt (Z Q).isCompact.measure_lt_top)
      (target Q) (htarget Q hQ)
  choose cut cutSub cutMeas cutVolume using hcut
  let Znew : iota -> ShadedTube tau E := fun Q =>
    if hQ : Q ∈ G.image parent then
      (ShadedTube.mk (Z Q).toTube (cut Q hQ) (cutMeas Q hQ)
        ((cutSub Q hQ).trans (Z Q).shade_subset))
    else Z Q
  refine ⟨Znew, ?_, ?_⟩
  · intro Q
    by_cases hQ : Q ∈ G.image parent
    · dsimp [Znew]
      rw [dif_pos hQ]
      exact ⟨rfl, cutSub Q hQ⟩
    · simp only [Znew, dif_neg hQ, and_self, Set.Subset.refl]
  · intro Q hQ
    change _ = (common : ENNReal)⁻¹ *
      volume ((if h : Q ∈ G.image parent then
        (ShadedTube.mk (Z Q).toTube (cut Q h) (cutMeas Q h)
          ((cutSub Q h).trans (Z Q).shade_subset)) else Z Q).shade)
    rw [dif_pos hQ, cutVolume Q hQ]
    dsimp only [target]
    rw [← mul_assoc, ENNReal.inv_mul_cancel (ENNReal.coe_ne_zero.mpr hc.ne')
      ENNReal.coe_ne_top, one_mul]
theorem exists_drop_fixed_density_payment_w101
    {p : Params} {beta gammaZero xiMin : Real} {xi : Fin (p.N + 1) -> Real}
    {M : Nat} (hp : SourcePassNumericsW95 p beta gammaZero xi xiMin M)
    (C : NNReal) :
    ∃ cutoff : NNReal, 0 < cutoff ∧ cutoff < 1 ∧
      ∀ {delta d : NNReal}, 0 < delta -> delta < cutoff ->
        0 < d -> d <= 1 -> d <= delta ^ p.ε ->
      ∀ m : Fin (p.N + 1), m.val < p.N ->
        (C : ENNReal) * (d : ENNReal) ^ (p.ε * (p.η (m.val + 1) / 2) / 2) <=
          (d : ENNReal) ^ (p.ε * (p.η (m.val + 1) / 2) / 4) := by
  let e : Real := p.ε ^ 2 * p.η 0 / 8
  have he : 0 < e := div_pos (mul_pos (sq_pos_of_pos hp.epsilon_pos)
    (hp.zeta_pos 0 (Nat.zero_le _))) (by norm_num)
  have hsmall : ∀ᶠ delta : NNReal in nhdsWithin 0 (Set.Ioi 0),
      delta < 1 ∧ (C : ENNReal) <= (delta : ENNReal) ^ (-e) := by
    filter_upwards [eventually_le_nhdsGT (c := (1 / 2 : NNReal)) (by norm_num),
      eventually_finite_const_le_rpow_neg (c := (C : ENNReal)) ENNReal.coe_ne_top he]
      with delta hd hpay
    exact ⟨hd.trans_lt (by norm_num), hpay⟩
  obtain ⟨cutoff, hc, hcut⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hsmall
  refine ⟨min cutoff (1 / 2), lt_min hc (by norm_num),
    (min_le_right _ _).trans_lt (by norm_num), ?_⟩
  intro delta d hd hdc hdp hd1 hdd m hm
  obtain ⟨hdlt, hpay⟩ := hcut ⟨hd, hdc.trans_le (min_le_left _ _)⟩
  have hdpE : (d : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hdp.ne'
  have hdE : (delta : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hd.ne'
  let a : Real := p.ε * (p.η (m.val + 1) / 2) / 4
  have ha : 0 < a := by
    dsimp [a]
    have hmN : m.val + 1 <= p.N := Nat.succ_le_iff.mpr hm
    have hmpos : 0 < p.η (m.val + 1) := hp.zeta_pos (m.val + 1) hmN
    exact div_pos (mul_pos hp.epsilon_pos (by positivity : 0 < p.η (m.val + 1) / 2)) (by norm_num)
  have hη : p.η 0 <= p.η (m.val + 1) := hp.zeta_mono 0 _ (Nat.zero_le _) (Nat.succ_le_iff.mpr hm)
  have hea : e <= p.ε * a := by
    dsimp [e, a]
    nlinarith [mul_le_mul_of_nonneg_left hη (sq_nonneg p.ε)]
  have hpow : (d : ENNReal) ^ a <= (delta : ENNReal) ^ e := by
    calc
      _ <= ((delta : ENNReal) ^ p.ε) ^ a := by
        apply ENNReal.rpow_le_rpow _ ha.le
        rw [← ENNReal.coe_rpow_of_ne_zero hd.ne']
        exact_mod_cast hdd
      _ = (delta : ENNReal) ^ (p.ε * a) := (ENNReal.rpow_mul _ _ _).symm
      _ <= (delta : ENNReal) ^ e :=
        ENNReal.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hdlt.le) hea
  have hCa : (C : ENNReal) * (d : ENNReal) ^ a <= 1 := by
    calc
      _ <= (delta : ENNReal) ^ (-e) * (delta : ENNReal) ^ e :=
        mul_le_mul' hpay hpow
      _ = 1 := by rw [← ENNReal.rpow_add _ _ hdE ENNReal.coe_ne_top]; simp
  have hexp : p.ε * (p.η (m.val + 1) / 2) / 2 = a + a := by dsimp [a]; ring
  rw [hexp, ENNReal.rpow_add _ _ hdpE ENNReal.coe_ne_top, ← mul_assoc]
  exact (mul_le_mul_right' hCa _).trans_eq (one_mul _)


end

end Kakeya.ml1Boot.TrialRestartW94

