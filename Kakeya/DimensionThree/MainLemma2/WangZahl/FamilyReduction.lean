module

public import Kakeya.DimensionThree.MainLemma2.WangZahl.EToD
public import Kakeya.Tube.EssentiallyDistinctReduction
public import Kakeya.Tube.EDUpToMult

@[expose] public section

open MeasureTheory Convexity

namespace Kakeya.WangZahl

noncomputable section

universe u


/-- The project's maximal convex density controls the source-faithful
canonical convex Wolff constant.  The apparent mismatch between compact
`ConvexSpaceBody` tests and arbitrary convex Wang--Zahl tests is removed by
taking the compact convex hull of the finite subfamily contained in the test
set. -/
theorem katzTaoConvexWolffConstant_le_maxDensity
    {delta : NNReal} (hdelta : 0 < delta) {iota : Type u}
    (s : Finset iota) (T : iota -> ShadedTube delta Space3) (hs : s.Nonempty) :
    katzTaoConvexWolffConstant s T <=
      maxDensity s (fun i => (T i).toConvexSpaceBody) := by
  classical
  let D := maxDensity s (fun i => (T i).toConvexSpaceBody)
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one
    (one_le_maxDensity ⟨hs.choose, hs.choose_spec,
      (tubeVolume_pos_and_ne_top hdelta).1.trans_eq
        (volume_carrier_eq_tubeVolume T hs.choose).symm⟩)
  apply katzTaoConvexWolffConstant_le s T hDpos
  intro W
  let t : Finset iota := s.filter (fun i => (T i).carrier ⊆ W.carrier)
  by_cases ht : t.Nonempty
  · let K : ConvexSpaceBody Space3 :=
        t.convexHull_biUnion (fun i => (T i).toConvexSpaceBody)
    have hKsub : K.carrier ⊆ W.carrier := by
      apply (ht.convexHull_biUnion_subset_iff
        (fun i => (T i).toConvexSpaceBody) W.convex_carrier.isConvexSet).2
      intro i hi
      exact (Finset.mem_filter.mp hi).2
    have hsum : (t.card : ENNReal) * tubeVolume delta =
        ∑ i ∈ t, volume (T i).carrier := by
      calc
        (t.card : ENNReal) * tubeVolume delta = ∑ _i ∈ t, tubeVolume delta := by
          rw [Finset.sum_const, nsmul_eq_mul]
        _ = ∑ i ∈ t, volume (T i).carrier :=
          Finset.sum_congr rfl fun i hi => (volume_carrier_eq_tubeVolume T i).symm
    have hinside : ∀ i ∈ t, (T i).toConvexSpaceBody <= K := by
      intro i hi
      simpa [K] using
        (Finset.le_convexHull_biUnion (s := t)
          (fun i => (T i).toConvexSpaceBody) hi)
    have hmass : (t.card : ENNReal) * tubeVolume delta <=
        D * volume W.carrier := by
      rw [hsum]
      calc
        (∑ i ∈ t, volume (T i).carrier) <=
            maxDensity t (fun i => (T i).toConvexSpaceBody) * volume K.carrier :=
          sum_volume_le_maxDensity_mul_volume' hinside
        _ <= D * volume K.carrier := by
          gcongr
          exact maxDensity_mono _ (fun i hi => (Finset.mem_filter.mp hi).1)
        _ <= D * volume W.carrier := by
          gcongr
    have hvol := tubeVolume_pos_and_ne_top hdelta
    change (t.card : ENNReal) <= D * volume W.carrier * (tubeVolume delta)⁻¹
    calc
      (t.card : ENNReal) =
          ((t.card : ENNReal) * tubeVolume delta) * (tubeVolume delta)⁻¹ := by
        rw [mul_assoc, ENNReal.mul_inv_cancel hvol.1.ne' hvol.2, mul_one]
      _ <= (D * volume W.carrier) * (tubeVolume delta)⁻¹ := by gcongr
  · have ht0 : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
    change (t.card : ENNReal) <= D * volume W.carrier * (tubeVolume delta)⁻¹
    simp [ht0]

/-- A project `IsKatzTao` hypothesis is therefore directly usable as the
convex-Wolff hypothesis of Assertion D, with no constant loss. -/
theorem katzTaoConvexWolffConstant_le_of_isKatzTao
    {delta : NNReal} (hdelta : 0 < delta) {iota : Type u}
    (s : Finset iota) (T : iota -> ShadedTube delta Space3) (hs : s.Nonempty)
    {C : ENNReal}
    (hKT : ConvexSpaceBody.IsKatzTao s (fun i => (T i).toConvexSpaceBody) C) :
    katzTaoConvexWolffConstant s T <= C :=
  (katzTaoConvexWolffConstant_le_maxDensity hdelta s T hs).trans hKT

/-- A maximal-density bound gives the bounded non-ED degree needed by the
shade-weighted essentially-distinct selection.  The natural cap is explicit;
later asymptotic bookkeeping may choose any `M` above the displayed
dimension-dependent density bound. -/
theorem isEDUpToMult_of_maxDensity
    {delta : NNReal} (hdelta : 0 < delta) (hdelta1 : delta <= 1)
    {iota : Type u} (s : Finset iota) (T : iota -> ShadedTube delta Space3)
    {D : ENNReal}
    (hD : maxDensity s (fun i => (T i).toConvexSpaceBody) <= D)
    {M : Nat}
    (hM : Tube.refineToEssDistinctLeaves.C 3 * D <= (M : ENNReal)) :
    IsEDUpToMult s (fun i => (T i).carrier) M := by
  classical
  intro i hi
  let bad := notEssDistinctSet s (fun j => (T j).carrier) (T i).carrier
  let K : ConvexSpaceBody Space3 :=
    (Tube.overlapContainment hdelta hdelta1 (T i).toTube).choose
  have hKvol : volume K.carrier <=
      Tube.overlapContainment.C 3 * volume (T i).carrier := by
    simpa [K] using
      (Tube.overlapContainment hdelta hdelta1 (T i).toTube).choose_spec.1
  have hbadsub : bad ⊆ familyIn s (fun j => (T j).toConvexSpaceBody) K := by
    intro j hj
    have hj' := hj
    simp only [bad, notEssDistinctSet, Finset.mem_filter] at hj'
    have hnot : ¬ IsEssentiallyDistinct (T j).carrier (T i).carrier := hj'.2
    have hover : (1 / 2 : ENNReal) * volume (T i).carrier <
        volume ((T i).carrier ∩ (T j).carrier) := by
      have hu : (1 / 2 : ENNReal) *
          max (volume (T j).carrier) (volume (T i).carrier) <
            volume ((T j).carrier ∩ (T i).carrier) := lt_of_not_ge hnot
      calc
        (1 / 2 : ENNReal) * volume (T i).carrier <=
            (1 / 2 : ENNReal) *
              max (volume (T j).carrier) (volume (T i).carrier) := by
          gcongr
          exact le_max_right _ _
        _ < volume ((T j).carrier ∩ (T i).carrier) := hu
        _ = volume ((T i).carrier ∩ (T j).carrier) := by rw [Set.inter_comm]
    have hcont : (T j).carrier ⊆ K.carrier := by
      simpa [K] using
        (Tube.overlapContainment hdelta hdelta1 (T i).toTube).choose_spec.2
          (T j).toTube hover
    simp only [familyIn, Finset.mem_filter]
    exact ⟨hj'.1, hcont⟩
  have hcardLower : (bad.card : ENNReal) *
      ((Tube.le_volume.c 3 : ENNReal) * (delta : ENNReal) ^ (3 - 1)) <=
      maxDensity s (fun j => (T j).toConvexSpaceBody) * volume K.carrier := by
    calc
      (bad.card : ENNReal) *
          ((Tube.le_volume.c 3 : ENNReal) * (delta : ENNReal) ^ (3 - 1)) <=
          ((familyIn s (fun j => (T j).toConvexSpaceBody) K).card : ENNReal) *
            ((Tube.le_volume.c 3 : ENNReal) * (delta : ENNReal) ^ (3 - 1)) := by
        gcongr
      _ <= maxDensity s (fun j => (T j).toConvexSpaceBody) * volume K.carrier :=
        by simpa using card_familyIn_le s (fun j => (T j).toTube) K
  have hcardBound : (bad.card : ENNReal) <=
      Tube.refineToEssDistinctLeaves.C 3 * D := by
    have hL0 : (Tube.le_volume.c 3 : ENNReal) *
        (delta : ENNReal) ^ (3 - 1) ≠ 0 := by
      exact mul_ne_zero (by exact_mod_cast (Tube.le_volume.c_pos 3).ne')
        (pow_ne_zero _ (ENNReal.coe_ne_zero.mpr hdelta.ne'))
    have hLtop : (Tube.le_volume.c 3 : ENNReal) *
        (delta : ENNReal) ^ (3 - 1) ≠ ⊤ := by
      exact ENNReal.mul_ne_top ENNReal.coe_ne_top
        (ENNReal.pow_ne_top ENNReal.coe_ne_top)
    obtain ⟨oc, hoc⟩ : ∃ x, Tube.overlapContainment.C 3 = x := ⟨_, rfl⟩
    obtain ⟨Cn, hCn⟩ : ∃ x, Tube.refineToEssDistinctLeaves.C 3 = x := ⟨_, rfl⟩
    have hCc : Cn * (Tube.le_volume.c 3 : ENNReal) =
        oc * (Tube.volume_le.C 3 : ENNReal) := by
      rw [<- hCn]
      dsimp only [Tube.refineToEssDistinctLeaves.C]
      rw [hoc]
      exact ENNReal.div_mul_cancel
        (by exact_mod_cast (Tube.le_volume.c_pos 3).ne') ENNReal.coe_ne_top
    have hmul : (bad.card : ENNReal) *
        ((Tube.le_volume.c 3 : ENNReal) * (delta : ENNReal) ^ (3 - 1)) <=
        Tube.refineToEssDistinctLeaves.C 3 * D *
          ((Tube.le_volume.c 3 : ENNReal) * (delta : ENNReal) ^ (3 - 1)) := by
      calc
        (bad.card : ENNReal) *
          ((Tube.le_volume.c 3 : ENNReal) * (delta : ENNReal) ^ (3 - 1)) <=
          maxDensity s (fun j => (T j).toConvexSpaceBody) * volume K.carrier := hcardLower
        _ <= D * (Tube.overlapContainment.C 3 * volume (T i).carrier) := by gcongr
        _ <= D * (Tube.overlapContainment.C 3 *
          ((Tube.volume_le.C 3 : ENNReal) * (delta : ENNReal) ^ (3 - 1))) := by
          gcongr
          simpa using Tube.volume_le hdelta1 (T i).toTube
        _ = Tube.refineToEssDistinctLeaves.C 3 * D *
          ((Tube.le_volume.c 3 : ENNReal) * (delta : ENNReal) ^ (3 - 1)) := by
          rw [hCn, hoc]
          rw [show D * (oc * ((Tube.volume_le.C 3 : ENNReal) *
              (delta : ENNReal) ^ (3 - 1))) =
            (oc * (Tube.volume_le.C 3 : ENNReal)) * D *
              (delta : ENNReal) ^ (3 - 1) by ring,
            <- hCc]
          ring
    have hcomm :
        ((Tube.le_volume.c 3 : ENNReal) * (delta : ENNReal) ^ (3 - 1)) *
            (bad.card : ENNReal) <=
          ((Tube.le_volume.c 3 : ENNReal) * (delta : ENNReal) ^ (3 - 1)) *
            (Tube.refineToEssDistinctLeaves.C 3 * D) := by
      rw [mul_comm _ (bad.card : ENNReal),
        mul_comm _ (Tube.refineToEssDistinctLeaves.C 3 * D)]
      exact hmul
    exact (ENNReal.mul_le_mul_iff_right hL0 hLtop).mp hcomm
  exact_mod_cast hcardBound.trans hM

/-- Transfer the real-valued output of the weighted ED selection to finite
`ENNReal` shade masses. -/
private theorem sum_le_of_toReal_sum_le_v2 {iota : Type*}
    (s t : Finset iota) (f : iota -> ENNReal)
    (hts : t ⊆ s) (hfin : ∀ i ∈ s, f i ≠ ⊤) {M : Nat}
    (h : (∑ i ∈ s, (f i).toReal) <=
      ((M : Real) + 1) * ∑ i ∈ t, (f i).toReal) :
    (∑ i ∈ s, f i) <= ((M : ENNReal) + 1) * ∑ i ∈ t, f i := by
  have hTfin : (∑ i ∈ t, f i) ≠ ⊤ :=
    (ENNReal.sum_ne_top).mpr fun i hi => hfin i (hts hi)
  have hSfin : (∑ i ∈ s, f i) ≠ ⊤ :=
    (ENNReal.sum_ne_top).mpr hfin
  have hfactor : ((M : ENNReal) + 1).toReal = (M : Real) + 1 := by
    simp [ENNReal.toReal_add]
  have hprodfin : ((M : ENNReal) + 1) * (∑ i ∈ t, f i) ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) hTfin
  rw [<- ENNReal.toReal_le_toReal hSfin hprodfin,
    ENNReal.toReal_sum hfin, ENNReal.toReal_mul, hfactor,
    ENNReal.toReal_sum (fun i hi => hfin i (hts hi))]
  exact h

/-- Maximal convex density yields a strictly essentially-distinct subfamily
which retains the total shade mass up to the explicit bounded-degree loss. -/
theorem exists_pairwise_subset_with_shade_mass_of_maxDensity
    {delta : NNReal} (hdelta : 0 < delta) (hdelta1 : delta <= 1)
    {iota : Type u} (s : Finset iota) (T : iota -> ShadedTube delta Space3)
    {D : ENNReal}
    (hD : maxDensity s (fun i => (T i).toConvexSpaceBody) <= D)
    {M : Nat}
    (hM : Tube.refineToEssDistinctLeaves.C 3 * D <= (M : ENNReal)) :
    ∃ s' : Finset iota, s' ⊆ s ∧
      (↑s' : Set iota).Pairwise
        (fun i j => IsEssentiallyDistinct (T i).carrier (T j).carrier) ∧
      (∑ i ∈ s, volume (T i).shade) <=
        ((M : ENNReal) + 1) * ∑ i ∈ s', volume (T i).shade := by
  classical
  have hED := isEDUpToMult_of_maxDensity hdelta hdelta1 s T hD hM
  obtain ⟨s', hs', hpair, hweight⟩ :=
    hED.exists_pairwise_subset_with_weight
      (fun i => (volume (T i).shade).toReal)
      (fun _ _ => ENNReal.toReal_nonneg)
  refine ⟨s', hs', hpair, ?_⟩
  apply sum_le_of_toReal_sum_le_v2 s s' (fun i => volume (T i).shade) hs'
  · intro i hi
    exact ne_top_of_le_ne_top (T i).isCompact.measure_ne_top
      (measure_mono (T i).shade_subset)
  · exact hweight

end

end Kakeya.WangZahl

#print axioms Kakeya.WangZahl.katzTaoConvexWolffConstant_le_maxDensity
#print axioms Kakeya.WangZahl.katzTaoConvexWolffConstant_le_of_isKatzTao
#print axioms Kakeya.WangZahl.isEDUpToMult_of_maxDensity
#print axioms Kakeya.WangZahl.exists_pairwise_subset_with_shade_mass_of_maxDensity
