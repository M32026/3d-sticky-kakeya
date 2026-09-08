module

public import Kakeya.DimensionThree.MainLemma2.WangZahl.FamilyReduction
public import Kakeya.DimensionThree.MainLemma2.WangZahl.SlabWolff
public import Kakeya.DimensionThree.MainLemma2.WangZahl.SelectedFamilyTransfer

@[expose] public section

open MeasureTheory Convexity

namespace Kakeya.WangZahl

noncomputable section

universe u

/-- The complete family-production bundle: maximal density gives a strict ED
shade-heavy subfamily; density and unit-ball Frostman control descend with
explicit losses; both canonical Wang--Zahl Wolff constants are then available. -/
theorem exists_assertionD_input_subfamily
    {delta : NNReal} (hdelta : 0 < delta) (hdelta1 : delta <= 1)
    {iota : Type u} (s : Finset iota) (T : iota -> ShadedTube delta Space3)
    (hs : s.Nonempty)
    {D K C lambda : ENNReal}
    (hD : maxDensity s (fun i => (T i).toConvexSpaceBody) <= D)
    {M : Nat}
    (hM : Tube.refineToEssDistinctLeaves.C 3 * D <= (M : ENNReal))
    (hKT : ConvexSpaceBody.IsKatzTao s
      (fun i => (T i).toConvexSpaceBody) K)
    (hC : 0 < C) (hlambda : 0 < lambda) (hlambdatop : lambda ≠ ⊤)
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1)
    (hF : ConvexSpaceBody.IsFrostmanIn s
      (fun i => (T i).toConvexSpaceBody)
      (ConvexSpaceBody.closedUnitBall (E := Space3)) C)
    (hdense : lambda * (∑ i ∈ s, volume (T i).carrier) <=
      ∑ i ∈ s, volume (T i).shade) :
    ∃ t : Finset iota, t ⊆ s ∧
      IsTubeShadingFamily t T ∧
      (∑ i ∈ s, volume (T i).shade) <=
        (((M : ENNReal) + 1) * ∑ i ∈ t, volume (T i).shade) ∧
      (lambda * ((M : ENNReal) + 1)⁻¹) *
          (∑ i ∈ t, volume (T i).carrier) <=
        ∑ i ∈ t, volume (T i).shade ∧
      ConvexSpaceBody.IsFrostmanIn t
        (fun i => (T i).toConvexSpaceBody)
        (ConvexSpaceBody.closedUnitBall (E := Space3))
        (C * (lambda⁻¹ * ((M : ENNReal) + 1))) ∧
      katzTaoConvexWolffConstant t T <= K ∧
      frostmanSlabWolffConstant t T <=
        C * (lambda⁻¹ * ((M : ENNReal) + 1)) := by
  classical
  obtain ⟨t, ht, hpair, hshade⟩ :=
    exists_pairwise_subset_with_shade_mass_of_maxDensity
      hdelta hdelta1 s T hD hM
  let L : ENNReal := (M : ENNReal) + 1
  have hL0 : L ≠ 0 := by simp [L]
  have hLtop : L ≠ ⊤ := by simp [L]
  have hTB : ∀ i ∈ s,
      (T i).toConvexSpaceBody <=
        (ConvexSpaceBody.closedUnitBall (E := Space3)) := by
    intro i hi
    exact hball i hi
  obtain ⟨hdense_t, hF_t⟩ := selected_dense_and_frostman T ht
    (ConvexSpaceBody.closedUnitBall (E := Space3)) hlambda.ne' hlambdatop
    hL0 hLtop hTB hF hdense (by simpa [L] using hshade)
  have hfamily : IsTubeShadingFamily t T := by
    constructor
    · intro i hi
      exact hball i (ht hi)
    · exact hpair
  have hsumcar : 0 < ∑ i ∈ s, volume (T i).carrier := by
    obtain ⟨i, hi⟩ := hs
    have hivol : 0 < volume (T i).carrier := by
      rw [volume_carrier_eq_tubeVolume T i]
      exact (tubeVolume_pos_and_ne_top hdelta).1
    exact hivol.trans_le
      (Finset.single_le_sum (s := s) (f := fun j => volume (T j).carrier)
        (fun _ _ => bot_le) hi)
  have hsumshade : 0 < ∑ i ∈ s, volume (T i).shade :=
    (pos_iff_ne_zero.mpr (mul_ne_zero hlambda.ne' hsumcar.ne')).trans_le hdense
  have htne : t.Nonempty := by
    by_contra ht0
    have htzero : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht0
    rw [htzero] at hshade
    exact (not_le_of_gt hsumshade) (by simpa using hshade)
  have hKT_t : katzTaoConvexWolffConstant t T <= K := by
    apply katzTaoConvexWolffConstant_le_of_isKatzTao hdelta t T htne
    exact ConvexSpaceBody.IsKatzTao.subset hKT ht
  have hnewC : 0 < C * (lambda⁻¹ * L) := by
    apply pos_iff_ne_zero.mpr
    exact mul_ne_zero hC.ne'
      (mul_ne_zero (ENNReal.inv_ne_zero.mpr hlambdatop) hL0)
  have hslab : frostmanSlabWolffConstant t T <= C * (lambda⁻¹ * L) :=
    frostmanSlabWolffConstant_le_of_isFrostmanIn_unitBall_sameConstant
      hdelta t T hnewC (fun i hi => hball i (ht hi)) hF_t
  refine ⟨t, ht, hfamily, hshade, ?_, ?_, hKT_t, ?_⟩
  · simpa [L] using hdense_t
  · simpa [L] using hF_t
  · simpa [L] using hslab

end

end Kakeya.WangZahl

#print axioms Kakeya.WangZahl.exists_assertionD_input_subfamily
