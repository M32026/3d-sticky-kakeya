module

public import Kakeya.DimensionThree.MainLemma2.WangZahl.EToD
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

open MeasureTheory Convexity

namespace Kakeya.WangZahl

noncomputable section

universe u

/-- A Frostman bound in the unit ball controls the source-faithful slab Wolff
constant.  Equal tube volumes cancel, so there is no scale-dependent loss. -/
theorem frostmanSlabWolffConstant_le_of_isFrostmanIn_unitBall
    {delta : NNReal} (hdelta : 0 < delta) {iota : Type u}
    (s : Finset iota) (T : iota -> ShadedTube delta Space3) {C : ENNReal}
    (hC : 0 < C)
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1)
    (hF : ConvexSpaceBody.IsFrostmanIn s
      (fun i => (T i).toConvexSpaceBody)
      (ConvexSpaceBody.closedUnitBall (E := Space3)) C) :
    frostmanSlabWolffConstant s T <=
      C * (volume (ConvexSpaceBody.closedUnitBall (E := Space3)).carrier)⁻¹ := by
  classical
  let B : ConvexSpaceBody Space3 := ConvexSpaceBody.closedUnitBall
  have hB0 : volume B.carrier ≠ 0 :=
    (ConvexSpaceBody.closedUnitBall_volume_pos (E := Space3)).ne'
  have hBtop : volume B.carrier ≠ ⊤ := B.isCompact.measure_ne_top
  have hconstpos : 0 < C * (volume B.carrier)⁻¹ :=
    pos_iff_ne_zero.mpr (mul_ne_zero hC.ne' (ENNReal.inv_ne_zero.mpr hBtop))
  apply frostmanSlabWolffConstant_le s T hconstpos
  intro W
  let t : Finset iota :=
    s.filter (fun i => (T i).carrier ⊆ W.carrier)
  by_cases hWne : W.carrier.Nonempty
  · let K : ConvexSpaceBody Space3 :=
      { carrier := W.carrier
        convex' := ((convex_closedBall (0 : Space3) 1).inter
          (W.plane.carrier.convex.cthickening (W.thickness : Real))).isConvexSet
        isCompact' := (isCompact_closedBall (0 : Space3) 1).inter_right
          Metric.isClosed_cthickening
        nonempty' := hWne }
    have hKB : K <= B := by
      intro x hx
      exact hx.1
    have hbodyB : ∀ i ∈ s, (T i).toConvexSpaceBody <= B := by
      intro i hi
      exact hball i hi
    have hfilter :
        s.filter (fun i => (T i).toConvexSpaceBody <= K) = t := by
      ext i
      simp only [Finset.mem_filter, t]
      rfl
    have hdB : densityIn s (fun i => (T i).toConvexSpaceBody) B =
        (s.card : ENNReal) * tubeVolume delta / volume B.carrier := by
      rw [densityIn_of_all_le hbodyB]
      congr 1
      calc
        (∑ i ∈ s, volume (T i).toConvexSpaceBody.carrier) =
            ∑ _i ∈ s, tubeVolume delta :=
          Finset.sum_congr rfl fun i hi => volume_carrier_eq_tubeVolume T i
        _ = (s.card : ENNReal) * tubeVolume delta := by
          rw [Finset.sum_const, nsmul_eq_mul]
    have hd := hF K hKB
    have hmass :=
      (densityIn_le_iff s (fun i => (T i).toConvexSpaceBody) K
        (C * densityIn s (fun i => (T i).toConvexSpaceBody) B)).mp hd
    have hsumt :
        (∑ i ∈ t, volume (T i).toConvexSpaceBody.carrier) =
          (t.card : ENNReal) * tubeVolume delta := by
      calc
        (∑ i ∈ t, volume (T i).toConvexSpaceBody.carrier) =
            ∑ _i ∈ t, tubeVolume delta :=
          Finset.sum_congr rfl fun i hi => volume_carrier_eq_tubeVolume T i
        _ = (t.card : ENNReal) * tubeVolume delta := by
          rw [Finset.sum_const, nsmul_eq_mul]
    rw [hfilter, hsumt, hdB] at hmass
    have hvol := tubeVolume_pos_and_ne_top hdelta
    change (t.card : ENNReal) <=
      (C * (volume B.carrier)⁻¹) * volume W.carrier * (s.card : ENNReal)
    have hmul : (t.card : ENNReal) * tubeVolume delta <=
        ((C * (volume B.carrier)⁻¹) * volume W.carrier * (s.card : ENNReal)) *
          tubeVolume delta := by
      calc
        (t.card : ENNReal) * tubeVolume delta <=
            (C * ((s.card : ENNReal) * tubeVolume delta / volume B.carrier)) *
              volume K.carrier := hmass
        _ = ((C * (volume B.carrier)⁻¹) * volume W.carrier *
              (s.card : ENNReal)) * tubeVolume delta := by
          simp only [K, ENNReal.div_eq_inv_mul]
          ring
    have hcomm : tubeVolume delta * (t.card : ENNReal) <=
        tubeVolume delta *
          ((C * (volume B.carrier)⁻¹) * volume W.carrier * (s.card : ENNReal)) := by
      simpa [mul_comm] using hmul
    exact (ENNReal.mul_le_mul_iff_right hvol.1.ne' hvol.2).mp hcomm
  · have ht0 : t = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      intro ht
      obtain ⟨i, hi⟩ := ht
      have hi' := (Finset.mem_filter.mp hi).2
      exact hWne ((T i).toConvexSpaceBody.nonempty.mono hi')
    change (t.card : ENNReal) <=
      (C * (volume B.carrier)⁻¹) * volume W.carrier * (s.card : ENNReal)
    simp [ht0]

/-- In dimension three the fixed unit-ball normalization costs at most one. -/
lemma unitBall_volume_inv_le_one_space3 :
    (volume (ConvexSpaceBody.closedUnitBall (E := Space3)).carrier)⁻¹ <= 1 := by
  apply ENNReal.inv_le_one.mpr
  rw [ConvexSpaceBody.closedUnitBall_carrier,
    EuclideanSpace.volume_closedBall_fin_three]
  simp only [ENNReal.ofReal_one, one_pow, one_mul, ENNReal.one_le_ofReal]
  nlinarith [Real.pi_gt_three]

/-- Unit-ball Frostman control therefore implies the slab Wolff bound with
the same constant in three dimensions. -/
theorem frostmanSlabWolffConstant_le_of_isFrostmanIn_unitBall_sameConstant
    {delta : NNReal} (hdelta : 0 < delta) {iota : Type u}
    (s : Finset iota) (T : iota -> ShadedTube delta Space3) {C : ENNReal}
    (hC : 0 < C)
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1)
    (hF : ConvexSpaceBody.IsFrostmanIn s
      (fun i => (T i).toConvexSpaceBody)
      (ConvexSpaceBody.closedUnitBall (E := Space3)) C) :
    frostmanSlabWolffConstant s T <= C := by
  calc
    frostmanSlabWolffConstant s T <=
        C * (volume (ConvexSpaceBody.closedUnitBall (E := Space3)).carrier)⁻¹ :=
      frostmanSlabWolffConstant_le_of_isFrostmanIn_unitBall
        hdelta s T hC hball hF
    _ <= C * 1 := by gcongr; exact unitBall_volume_inv_le_one_space3
    _ = C := mul_one C

end

end Kakeya.WangZahl

#print axioms Kakeya.WangZahl.frostmanSlabWolffConstant_le_of_isFrostmanIn_unitBall
#print axioms Kakeya.WangZahl.unitBall_volume_inv_le_one_space3
#print axioms Kakeya.WangZahl.frostmanSlabWolffConstant_le_of_isFrostmanIn_unitBall_sameConstant
