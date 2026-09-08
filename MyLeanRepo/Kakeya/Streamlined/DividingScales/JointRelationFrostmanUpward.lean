import MyLeanRepo.Kakeya.Streamlined.DividingScales.JointUniformLocalCover
import MyLeanRepo.Kakeya.Streamlined.DividingScales.UniformCoverRatios
import MyLeanRepo.Kakeya.Streamlined.DividingScales.ParentEnvelope
import MyLeanRepo.Kakeya.Streamlined.DividingScales.ReferenceDensity
import MyLeanRepo.Kakeya.Streamlined.DividingScales.FrostmanInequalities
import MyLeanRepo.Kakeya.Streamlined.DividingScales.FullFiberRestriction
import MyLeanRepo.Kakeya.Streamlined.DividingScales.ParentEnvelopeCounting

/-!
# Upward Frostman transfer inside one relation fiber

Fix one scale-`s` parent.  The assigned scale-`r` and scale-`q` relation
families are two independent parent images of the same assigned fine fiber.
Joint parent-cell uniformity compares their normalized cardinalities with a
loss `uniformity^2`.

For a convex test set containing some scale-`q` parents, every related
scale-`r` parent lies in a common difference-body envelope.  Applying the
scale-`r` relation Frostman bound in that envelope gives the scale-`q`
relation Frostman bound.
-/

noncomputable section

open MeasureTheory Set

namespace Kakeya.Streamlined

namespace JointUniformLocalDilatedDiscreteUniformTubeStructure

variable {delta A C : ℝ} {F : TubeFamily delta}
variable {hdelta_le_one : delta ≤ 1}
variable (U : JointUniformLocalDilatedDiscreteUniformTubeStructure
  (A := A) (C := C) F hdelta_le_one)

/--
Assigned relation Frostman control is inherited upward from scale `r` to
scale `q`, inside one fixed scale-`s` parent.
-/
lemma assignedRelationFrostmanConstant_upward
    (hA : 1 ≤ A) (hdelta : 0 < delta)
    (hF_ball : F.IsInUnitBall)
    (r q s : UniformScaleIndex delta)
    (hrq :
      (uniformScale delta hdelta_le_one r).1 ≤
        (uniformScale delta hdelta_le_one q).1)
    (hqs :
      (uniformScale delta hdelta_le_one q).1 ≤
        (uniformScale delta hdelta_le_one s).1)
    (k : Fin (U.coarse s).card) :
    U.toDilated.assignedRelationFrostmanConstant q s k ≤
      U.uniformity ^ 2 * parentEnvelopeVolumeFactor A *
        U.toDilated.assignedRelationFrostmanConstant r s k := by
  classical
  let D := U.toDilated
  let fineS := D.fineFiberSubfamily s k
  let R := D.relatedSubfamily r s k
  let Q := D.relatedSubfamily q s k
  let V :=
    dilatedTubeCarrier (independentCoverParentDilation A)
      ((U.coarse s).tube k)
  rcases U.exists_fineFiber_relatedCover_isCUniform r s k with
    ⟨Pr, _hPr, hPr_uniform⟩
  rcases U.exists_fineFiber_relatedCover_isCUniform q s k with
    ⟨Pq, _hPq, hPq_uniform⟩
  have hrs :
      (uniformScale delta hdelta_le_one r).1 ≤
        (uniformScale delta hdelta_le_one s).1 :=
    hrq.trans hqs
  have hfineS : fineS.family.Nonempty :=
    D.fineFiberSubfamily_nonempty s k
  have hfineS_ball : fineS.family.IsInUnitBall := by
    intro i
    rw [fineS.tube_eq i]
    exact hF_ball (fineS.embedding i)
  have hrho :
      0 < (uniformScale delta hdelta_le_one r).1 :=
    lt_of_lt_of_le hdelta
      (uniformScale delta hdelta_le_one r).property.1
  have hxi :
      0 < (uniformScale delta hdelta_le_one q).1 :=
    hrho.trans_le hrq
  have hsigma :
      0 < (uniformScale delta hdelta_le_one s).1 :=
    hxi.trans_le hqs
  have hD :
      1 ≤ independentCoverParentDilation A := by
    dsimp only [independentCoverParentDilation]
    nlinarith [sq_nonneg A]
  have hV_zero : volume V ≠ 0 :=
    (GeometricLemmas.dilatedTubeCarrier_volume_pos
      hsigma hD ((U.coarse s).tube k)).ne'
  have hV_top : volume V ≠ ⊤ :=
    GeometricLemmas.dilatedTubeCarrier_volume_ne_top
      hsigma hD ((U.coarse s).tube k)
  have hQ_mass_zero :
      Q.family.toBodyFamily.containedMass V ≠ 0 :=
    (D.assignedRelationReferenceMass_pos
      hA hdelta hF_ball q s hqs k).ne'
  have hQ_mass_top :
      Q.family.toBodyFamily.containedMass V ≠ ⊤ :=
    D.assignedRelationReferenceMass_ne_top
      hA hdelta hF_ball q s hqs k
  apply Q.family.toBodyFamily
    |>.frostmanConstantIn_le_of_containedMass_mul_volume_le
      hV_zero hV_top hQ_mass_zero hQ_mass_top
  intro K hK hKV
  let I := Q.family.indicesIn K
  by_cases hI : I = ∅
  · have hmassK : Q.family.toBodyFamily.containedMass K = 0 := by
      rw [Q.family.containedMass_eq_card_mul_deltaTubeVolume]
      change (I.card : ENNReal) *
          Kakeya.deltaTubeVolume
            (uniformScale delta hdelta_le_one q).1 = 0
      rw [hI]
      simp
    simp [hmassK]
  · have hI_nonempty : I.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hI
    rcases hI_nonempty with ⟨q₀, hq₀⟩
    have hq₀K :
        (Q.family.tube q₀).carrier ⊆ K :=
      (Q.family.mem_indicesIn_iff K q₀).mp hq₀
    have hK_pos : 0 < volume K := by
      have htube : 0 < (Q.family.tube q₀).volume := by
        rw [RandomTranslation.tube_volume_eq_deltaTubeVolume]
        exact RandomTranslation.deltaTubeVolume_pos hxi
      exact htube.trans_le (measure_mono hq₀K)
    have hK_top : volume K ≠ ⊤ :=
      ne_top_of_le_ne_top hV_top (measure_mono hKV)
    let X := Pq.toFactoring.fiberIndicesOver I
    let J := X.image Pr.parent
    have hratioAssigned :
        (I.card : ENNReal) * (R.family.card : ENNReal) ≤
          U.assignedUniformity ^ 2 * (Q.family.card : ENNReal) *
            (J.card : ENNReal) := by
      have h :=
        Pr.parentCard_mul_leftCard_le_twoUniformity_mul_rightCard_mul_imageCard
          Pq hfineS hPr_uniform hPq_uniform I
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm, X, J] using h
    have hratio :
        (I.card : ENNReal) * (R.family.card : ENNReal) ≤
          U.uniformity ^ 2 * (Q.family.card : ENNReal) *
            (J.card : ENNReal) := by
      exact hratioAssigned.trans <| by
        gcongr
        exact U.assignedUniformity_le_uniformity
    let p := GeometricLemmas.tubeMidpoint (Q.family.tube q₀)
    let W := parentEnvelope (independentCoverParentDilation A) p K
    let L := W ∩ V
    have hpK : p ∈ K :=
      hq₀K (GeometricLemmas.tubeMidpoint_mem_carrier
        (Q.family.tube q₀))
    have hW_convex : Convex ℝ W :=
      parentEnvelope_convex hK (independentCoverParentDilation A) p
    have hL_convex : Convex ℝ L :=
      hW_convex.inter
        (GeometricLemmas.dilatedTubeCarrier_convex
          ((U.coarse s).tube k))
    have hL_V : L ⊆ V := Set.inter_subset_right
    have hW_volume :
        volume W ≤ parentEnvelopeVolumeFactor A * volume K := by
      have hvolume :=
        parentEnvelope_volume_le hK hK_pos hK_top hD p
      calc
        volume W
            ≤ ENNReal.ofReal
                ((2 * independentCoverParentDilation A - 1) ^ 3) *
              (64 * volume K) := hvolume
        _ = parentEnvelopeVolumeFactor A * volume K := by
          dsimp only [parentEnvelopeVolumeFactor]
          ring
    have hL_volume :
        volume L ≤ parentEnvelopeVolumeFactor A * volume K :=
      (measure_mono Set.inter_subset_left).trans hW_volume
    have hJ_L :
        ∀ j ∈ J, (R.family.tube j).carrier ⊆ L := by
      intro j hj
      rcases Finset.mem_image.mp hj with ⟨x, hx, hxj⟩
      have hqI : Pq.parent x ∈ I :=
        (Pq.toFactoring.mem_fiberIndicesOver_iff I x).mp hx
      have hqK :
          (Q.family.tube (Pq.parent x)).carrier ⊆ K :=
        (Q.family.mem_indicesIn_iff K (Pq.parent x)).mp hqI
      have hparent :
          (R.family.tube (Pr.parent x)).carrier ⊆
            dilatedTubeCarrier (independentCoverParentDilation A)
              (Q.family.tube (Pq.parent x)) :=
        DilatedDiscreteUniformTubeStructure.common_child_parent_containment
          hA hrho
          (uniformScale delta hdelta_le_one q).property.2
          hrq (fineS.family.tube x) (hfineS_ball x)
          (R.family.tube (Pr.parent x))
          (Q.family.tube (Pq.parent x))
          (Pr.nested x) (Pq.nested x)
      have hmidK :
          GeometricLemmas.tubeMidpoint
              (Q.family.tube (Pq.parent x)) ∈ K :=
        hqK (GeometricLemmas.tubeMidpoint_mem_carrier
          (Q.family.tube (Pq.parent x)))
      have hW :
          (R.family.tube (Pr.parent x)).carrier ⊆ W := by
        exact hparent.trans <|
          (Set.image_mono hqK).trans <|
            homothety_image_subset_parentEnvelope
              hK hpK hmidK hD
      have hrelV :
          (R.family.tube (Pr.parent x)).carrier ⊆ V :=
        D.relatedSubfamily_all_contained
          hA hdelta hF_ball r s hrs k (Pr.parent x)
      rw [← hxj]
      exact fun y hy => ⟨hW hy, hrelV hy⟩
    have hJ_mass :
        (J.card : ENNReal) *
            Kakeya.deltaTubeVolume
              (uniformScale delta hdelta_le_one r).1 ≤
          R.family.toBodyFamily.containedMass L := by
      rw [R.family.containedMass_eq_card_mul_deltaTubeVolume L]
      have hsubset : J ⊆ R.family.indicesIn L := by
        intro j hj
        exact (R.family.mem_indicesIn_iff L j).mpr (hJ_L j hj)
      exact mul_le_mul_right'
        (by exact_mod_cast Finset.card_le_card hsubset) _
    have hR_frostman :
        R.family.toBodyFamily.containedMass L * volume V ≤
          D.assignedRelationFrostmanConstant r s k *
            R.family.toBodyFamily.containedMass V * volume L :=
      R.family.toBodyFamily
        |>.containedMass_mul_volume_le_of_frostmanConstantIn_le
          hV_zero hV_top
          (D.assignedRelationReferenceMass_pos
            hA hdelta hF_ball r s hrs k).ne'
          (D.assignedRelationReferenceMass_ne_top
            hA hdelta hF_ball r s hrs k)
          le_rfl hL_convex hL_V
    have hR_reference :
        R.family.toBodyFamily.containedMass V =
          (R.family.card : ENNReal) *
            Kakeya.deltaTubeVolume
              (uniformScale delta hdelta_le_one r).1 := by
      rw [BodyFamily.containedMass_eq_mass_of_all_contained _ _
        (D.relatedSubfamily_all_contained
          hA hdelta hF_ball r s hrs k)]
      rw [R.family.bodyMass_eq_nominalMass]
      rfl
    have hJ_cross :
        (J.card : ENNReal) *
              Kakeya.deltaTubeVolume
                (uniformScale delta hdelta_le_one r).1 *
              volume V ≤
          D.assignedRelationFrostmanConstant r s k *
            ((R.family.card : ENNReal) *
              Kakeya.deltaTubeVolume
                (uniformScale delta hdelta_le_one r).1) *
            (parentEnvelopeVolumeFactor A * volume K) := by
      calc
        (J.card : ENNReal) *
              Kakeya.deltaTubeVolume
                (uniformScale delta hdelta_le_one r).1 *
              volume V
            ≤ R.family.toBodyFamily.containedMass L * volume V := by
          exact mul_le_mul_right' hJ_mass _
        _ ≤ D.assignedRelationFrostmanConstant r s k *
              R.family.toBodyFamily.containedMass V * volume L :=
          hR_frostman
        _ ≤ D.assignedRelationFrostmanConstant r s k *
              ((R.family.card : ENNReal) *
                Kakeya.deltaTubeVolume
                  (uniformScale delta hdelta_le_one r).1) *
              (parentEnvelopeVolumeFactor A * volume K) := by
          rw [hR_reference]
          gcongr
    have hRmass_zero :
        (R.family.card : ENNReal) *
            Kakeya.deltaTubeVolume
              (uniformScale delta hdelta_le_one r).1 ≠ 0 := by
      rw [← hR_reference]
      exact (D.assignedRelationReferenceMass_pos
        hA hdelta hF_ball r s hrs k).ne'
    have hRmass_top :
        (R.family.card : ENNReal) *
            Kakeya.deltaTubeVolume
              (uniformScale delta hdelta_le_one r).1 ≠ ⊤ := by
      rw [← hR_reference]
      exact D.assignedRelationReferenceMass_ne_top
        hA hdelta hF_ball r s hrs k
    have hcount_cross :
        (I.card : ENNReal) * volume V ≤
          (U.uniformity ^ 2 * parentEnvelopeVolumeFactor A *
            D.assignedRelationFrostmanConstant r s k) *
            (Q.family.card : ENNReal) * volume K := by
      apply (ENNReal.mul_le_mul_iff_left hRmass_zero hRmass_top).mp
      calc
        (I.card : ENNReal) * volume V *
              ((R.family.card : ENNReal) *
                Kakeya.deltaTubeVolume
                  (uniformScale delta hdelta_le_one r).1)
            =
          ((I.card : ENNReal) * (R.family.card : ENNReal)) *
            (Kakeya.deltaTubeVolume
              (uniformScale delta hdelta_le_one r).1 * volume V) := by
              ring
        _ ≤
          (U.uniformity ^ 2 * (Q.family.card : ENNReal) *
            (J.card : ENNReal)) *
            (Kakeya.deltaTubeVolume
              (uniformScale delta hdelta_le_one r).1 * volume V) := by
          exact mul_le_mul_right' hratio _
        _ =
          U.uniformity ^ 2 * (Q.family.card : ENNReal) *
            ((J.card : ENNReal) *
              Kakeya.deltaTubeVolume
                (uniformScale delta hdelta_le_one r).1 * volume V) := by
              ring
        _ ≤
          U.uniformity ^ 2 * (Q.family.card : ENNReal) *
            (D.assignedRelationFrostmanConstant r s k *
              ((R.family.card : ENNReal) *
                Kakeya.deltaTubeVolume
                  (uniformScale delta hdelta_le_one r).1) *
              (parentEnvelopeVolumeFactor A * volume K)) := by
          exact mul_le_mul_left' hJ_cross _
        _ =
          ((U.uniformity ^ 2 * parentEnvelopeVolumeFactor A *
              D.assignedRelationFrostmanConstant r s k) *
            (Q.family.card : ENNReal) * volume K) *
            ((R.family.card : ENNReal) *
              Kakeya.deltaTubeVolume
                (uniformScale delta hdelta_le_one r).1) := by
          ring
    have hQ_mass_K :
        Q.family.toBodyFamily.containedMass K =
          (I.card : ENNReal) *
            Kakeya.deltaTubeVolume
              (uniformScale delta hdelta_le_one q).1 := by
      rw [Q.family.containedMass_eq_card_mul_deltaTubeVolume K]
      rfl
    have hQ_reference :
        Q.family.toBodyFamily.containedMass V =
          (Q.family.card : ENNReal) *
            Kakeya.deltaTubeVolume
              (uniformScale delta hdelta_le_one q).1 := by
      rw [BodyFamily.containedMass_eq_mass_of_all_contained _ _
        (D.relatedSubfamily_all_contained
          hA hdelta hF_ball q s hqs k)]
      rw [Q.family.bodyMass_eq_nominalMass]
      rfl
    rw [hQ_mass_K, hQ_reference]
    calc
      (I.card : ENNReal) *
            Kakeya.deltaTubeVolume
              (uniformScale delta hdelta_le_one q).1 *
            volume V
          =
        ((I.card : ENNReal) * volume V) *
          Kakeya.deltaTubeVolume
            (uniformScale delta hdelta_le_one q).1 := by ring
      _ ≤
        ((U.uniformity ^ 2 * parentEnvelopeVolumeFactor A *
            D.assignedRelationFrostmanConstant r s k) *
          (Q.family.card : ENNReal) * volume K) *
          Kakeya.deltaTubeVolume
            (uniformScale delta hdelta_le_one q).1 := by
        exact mul_le_mul_right' hcount_cross _
      _ =
        (U.uniformity ^ 2 * parentEnvelopeVolumeFactor A *
            D.assignedRelationFrostmanConstant r s k) *
          ((Q.family.card : ENNReal) *
            Kakeya.deltaTubeVolume
              (uniformScale delta hdelta_le_one q).1) *
          volume K := by ring

end JointUniformLocalDilatedDiscreteUniformTubeStructure

end Kakeya.Streamlined
