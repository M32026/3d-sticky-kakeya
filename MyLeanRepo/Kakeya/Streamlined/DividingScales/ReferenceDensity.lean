import MyLeanRepo.Kakeya.Streamlined.IndependentDilatedCoverFullFiberMass
import MyLeanRepo.Kakeya.Streamlined.DividingScales.FrostmanInequalities
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.SelfDilatedContainment
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.DeterministicHelpers

/-!
# Reference densities for dividing-scales fibers

The pointwise Frostman interface divides by the density of a fiber in its
reference dilated parent.  This module proves that all reference densities
used by the finite-grid dividing-scales statements are positive and finite.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Streamlined

namespace TubeFamily

/-- A nonempty positive-radius tube family has positive mass in any set
containing all of its tubes. -/
lemma containedMass_pos_of_nonempty_of_all_contained
    {delta : ℝ} (G : TubeFamily delta)
    (hdelta : 0 < delta) (hG : G.Nonempty)
    {V : Set Point3}
    (hcontained : ∀ i, (G.tube i).carrier ⊆ V) :
    0 < G.toBodyFamily.containedMass V := by
  rw [BodyFamily.containedMass_eq_mass_of_all_contained
    G.toBodyFamily V hcontained]
  rw [G.bodyMass_eq_nominalMass]
  exact RandomTranslation.nominalMass_pos hdelta hG

/-- A tube family has finite mass in any set containing all of its tubes. -/
lemma containedMass_ne_top_of_all_contained
    {delta : ℝ} (G : TubeFamily delta)
    {V : Set Point3}
    (hcontained : ∀ i, (G.tube i).carrier ⊆ V) :
    G.toBodyFamily.containedMass V ≠ ⊤ := by
  rw [BodyFamily.containedMass_eq_mass_of_all_contained
    G.toBodyFamily V hcontained]
  rw [G.bodyMass_eq_nominalMass]
  exact RandomTranslation.nominalMass_ne_top

end TubeFamily

namespace GeometricLemmas

/-- A positive-radius tube has positive volume after any dilation by at least
one. -/
lemma dilatedTubeCarrier_volume_pos
    {rho A : ℝ} (hrho : 0 < rho) (hA : 1 ≤ A)
    (T : Kakeya.DeltaTube rho) :
    0 < volume (dilatedTubeCarrier A T) := by
  have htube : 0 < T.volume := by
    rw [RandomTranslation.tube_volume_eq_deltaTubeVolume]
    exact RandomTranslation.deltaTubeVolume_pos hrho
  exact lt_of_lt_of_le htube
    (measure_mono (self_dilated_containment A hA T))

/-- Every homothetic dilation of a tube carrier has finite volume. -/
lemma dilatedTubeCarrier_volume_ne_top
    {rho A : ℝ} (hrho : 0 < rho) (hA : 1 ≤ A)
    (T : Kakeya.DeltaTube rho) :
    volume (dilatedTubeCarrier A T) ≠ ⊤ := by
  have hsegment :
      IsCompact (Kakeya.unitSegment T.base T.direction) := by
    apply IsCompact.image
    · exact isCompact_Icc
    · fun_prop
  have hextended :
      IsCompact (extendedSegment A T) :=
    hsegment.image (AffineMap.homothety_continuous _ _)
  have hbounded :
      Bornology.IsBounded
        (Metric.cthickening (A * rho) (extendedSegment A T)) :=
    hextended.isBounded.cthickening
  rw [dilatedTubeCarrier_eq_cthickening
    (lt_of_lt_of_le zero_lt_one hA) hrho.le T]
  exact hbounded.measure_lt_top.ne

/-- A dilated tube carrier is convex. -/
lemma dilatedTubeCarrier_convex
    {rho A : ℝ} (T : Kakeya.DeltaTube rho) :
    Convex ℝ (dilatedTubeCarrier A T) :=
  (deltaTube_carrier_convex' T).affine_image
    (AffineMap.homothety (tubeMidpoint T) A)

end GeometricLemmas

namespace DilatedDiscreteUniformTubeStructure

variable {delta A : ℝ} {F : TubeFamily delta}
variable {hdelta_le_one : delta ≤ 1}
variable (U : DilatedDiscreteUniformTubeStructure
  (A := A) F hdelta_le_one)

/--
Frostman constant of the original fine tubes contained in one parent at a
distinguished scale, measured in that parent's cover dilation.
-/
def fineFiberFrostmanConstant
    (r : UniformScaleIndex delta)
    (j : Fin (U.coarse r).card) : ENNReal :=
  (U.containedFineSubfamily r j).family.toBodyFamily.frostmanConstantIn
    (dilatedTubeCarrier A ((U.coarse r).tube j))

/-- Frostman constant of the assigned fine fiber in its selected parent. -/
def assignedFineFiberFrostmanConstant
    (r : UniformScaleIndex delta)
    (j : Fin (U.coarse r).card) : ENNReal :=
  (U.fineFiberSubfamily r j).family.toBodyFamily.frostmanConstantIn
    (dilatedTubeCarrier A ((U.coarse r).tube j))

/--
Frostman constant of the scale-`r` parents contained in the universal
dilation of one scale-`s` parent.
-/
def relationFrostmanConstant
    (r s : UniformScaleIndex delta)
    (k : Fin (U.coarse s).card) : ENNReal :=
  (U.containedParentSubfamily r s k).family.toBodyFamily.frostmanConstantIn
    (dilatedTubeCarrier (independentCoverParentDilation A)
      ((U.coarse s).tube k))

/-- Frostman constant of the common-child relation subfamily. -/
def assignedRelationFrostmanConstant
    (r s : UniformScaleIndex delta)
    (k : Fin (U.coarse s).card) : ENNReal :=
  (U.relatedSubfamily r s k).family.toBodyFamily.frostmanConstantIn
    (dilatedTubeCarrier (independentCoverParentDilation A)
      ((U.coarse s).tube k))

/-- Katz--Tao concentration constant of one full relation fiber. -/
def relationDeltaMax
    (r s : UniformScaleIndex delta)
    (k : Fin (U.coarse s).card) : ENNReal :=
  (U.containedParentSubfamily r s k).family.toBodyFamily.deltaMax

/-- Katz--Tao concentration constant of one assigned common-child relation. -/
def assignedRelationDeltaMax
    (r s : UniformScaleIndex delta)
    (k : Fin (U.coarse s).card) : ENNReal :=
  (U.relatedSubfamily r s k).family.toBodyFamily.deltaMax

/--
An assigned common-child relation has no larger `deltaMax` than the full
geometric containment relation over the same parent.
-/
lemma assignedRelationDeltaMax_le_relationDeltaMax
    (hA : 1 ≤ A) (hdelta : 0 < delta)
    (hF_ball : F.IsInUnitBall)
    (r s : UniformScaleIndex delta)
    (hrs :
      (uniformScale delta hdelta_le_one r).1 ≤
        (uniformScale delta hdelta_le_one s).1)
    (k : Fin (U.coarse s).card) :
    U.assignedRelationDeltaMax r s k ≤
      U.relationDeltaMax r s k := by
  let inclusion :=
    TubeSubfamily.fromFinsetInclusion (U.coarse r)
      (U.relatedIndices r s k)
      (U.containedParentIndices r s k)
      (U.relatedIndices_subset_containedParentIndices
        hA hdelta hF_ball r s hrs k)
  exact BodyFamily.subfamily_deltaMax_le
    inclusion.injective
    (fun i => by
      change
        ((U.relatedSubfamily r s k).family.tube i).carrier =
          ((U.containedParentSubfamily r s k).family.tube
            (inclusion i)).carrier
      rw [(U.relatedSubfamily r s k).tube_eq i,
        (U.containedParentSubfamily r s k).tube_eq (inclusion i)]
      exact congrArg
        (fun j => ((U.coarse r).tube j).carrier)
        (TubeSubfamily.fromFinsetInclusion_ambient
          (U.coarse r)
          (U.relatedIndices r s k)
          (U.containedParentIndices r s k)
          (U.relatedIndices_subset_containedParentIndices
            hA hdelta hF_ball r s hrs k) i).symm)

/-- Every fine-to-grid fiber is Frostman with one common error. -/
def IsFrostmanAtEveryGridScale (bound : ENNReal) : Prop :=
  ∀ r : UniformScaleIndex delta,
    ∀ j : Fin (U.coarse r).card,
      U.fineFiberFrostmanConstant r j ≤ bound

/-- Every assigned fine-to-grid fiber is Frostman with one common error. -/
def AssignedIsFrostmanAtEveryGridScale (bound : ENNReal) : Prop :=
  ∀ r : UniformScaleIndex delta,
    ∀ j : Fin (U.coarse r).card,
      U.assignedFineFiberFrostmanConstant r j ≤ bound

/-- Every selected coarse family on the paper grid is Katz--Tao. -/
def IsKatzTaoAtEveryGridScale (bound : ENNReal) : Prop :=
  ∀ r : UniformScaleIndex delta,
    (U.coarse r).toBodyFamily.deltaMax ≤ bound

/-- The full fine fiber has positive mass in its dilated parent. -/
lemma containedFineReferenceMass_pos
    (hdelta : 0 < delta)
    (r : UniformScaleIndex delta)
    (j : Fin (U.coarse r).card) :
    0 <
      (U.containedFineSubfamily r j).family.toBodyFamily.containedMass
        (dilatedTubeCarrier A ((U.coarse r).tube j)) := by
  exact TubeFamily.containedMass_pos_of_nonempty_of_all_contained
    (U.containedFineSubfamily r j).family hdelta
    (U.containedFineSubfamily_nonempty r j)
    (U.containedFineSubfamily_all_contained r j)

/-- The full fine fiber has finite mass in its dilated parent. -/
lemma containedFineReferenceMass_ne_top
    (r : UniformScaleIndex delta)
    (j : Fin (U.coarse r).card) :
    (U.containedFineSubfamily r j).family.toBodyFamily.containedMass
        (dilatedTubeCarrier A ((U.coarse r).tube j)) ≠ ⊤ := by
  exact TubeFamily.containedMass_ne_top_of_all_contained
    (U.containedFineSubfamily r j).family
    (U.containedFineSubfamily_all_contained r j)

/-- The assigned fine fiber has positive mass in its selected parent. -/
lemma assignedFineReferenceMass_pos
    (hdelta : 0 < delta)
    (r : UniformScaleIndex delta)
    (j : Fin (U.coarse r).card) :
    0 <
      (U.fineFiberSubfamily r j).family.toBodyFamily.containedMass
        (dilatedTubeCarrier A ((U.coarse r).tube j)) := by
  exact TubeFamily.containedMass_pos_of_nonempty_of_all_contained
    (U.fineFiberSubfamily r j).family hdelta
    (U.fineFiberSubfamily_nonempty r j)
    (U.fineFiberSubfamily_all_contained r j)

/-- The assigned fine fiber has finite mass in its selected parent. -/
lemma assignedFineReferenceMass_ne_top
    (r : UniformScaleIndex delta)
    (j : Fin (U.coarse r).card) :
    (U.fineFiberSubfamily r j).family.toBodyFamily.containedMass
        (dilatedTubeCarrier A ((U.coarse r).tube j)) ≠ ⊤ := by
  exact TubeFamily.containedMass_ne_top_of_all_contained
    (U.fineFiberSubfamily r j).family
    (U.fineFiberSubfamily_all_contained r j)

/-- Assigned fine reference density is nonzero. -/
lemma assignedFineReferenceDensity_ne_zero
    (hA : 1 ≤ A) (hdelta : 0 < delta)
    (r : UniformScaleIndex delta)
    (j : Fin (U.coarse r).card) :
    (U.fineFiberSubfamily r j).family.toBodyFamily.density
        (dilatedTubeCarrier A ((U.coarse r).tube j)) ≠ 0 := by
  have hrho :
      0 < (uniformScale delta hdelta_le_one r).1 :=
    lt_of_lt_of_le hdelta
      (uniformScale delta hdelta_le_one r).property.1
  exact ENNReal.div_ne_zero.mpr
    ⟨(U.assignedFineReferenceMass_pos hdelta r j).ne',
      GeometricLemmas.dilatedTubeCarrier_volume_ne_top
        hrho hA ((U.coarse r).tube j)⟩

/-- Assigned fine reference density is finite. -/
lemma assignedFineReferenceDensity_ne_top
    (hA : 1 ≤ A) (hdelta : 0 < delta)
    (r : UniformScaleIndex delta)
    (j : Fin (U.coarse r).card) :
    (U.fineFiberSubfamily r j).family.toBodyFamily.density
        (dilatedTubeCarrier A ((U.coarse r).tube j)) ≠ ⊤ := by
  have hrho :
      0 < (uniformScale delta hdelta_le_one r).1 :=
    lt_of_lt_of_le hdelta
      (uniformScale delta hdelta_le_one r).property.1
  exact ENNReal.div_ne_top
    (U.assignedFineReferenceMass_ne_top r j)
    (GeometricLemmas.dilatedTubeCarrier_volume_pos
      hrho hA ((U.coarse r).tube j)).ne'

/-- The reference density of every full fine fiber is nonzero. -/
lemma fineFiberReferenceDensity_ne_zero
    (hA : 1 ≤ A) (hdelta : 0 < delta)
    (r : UniformScaleIndex delta)
    (j : Fin (U.coarse r).card) :
    (U.containedFineSubfamily r j).family.toBodyFamily.density
        (dilatedTubeCarrier A ((U.coarse r).tube j)) ≠ 0 := by
  have hrho :
      0 < (uniformScale delta hdelta_le_one r).1 :=
    lt_of_lt_of_le hdelta
      (uniformScale delta hdelta_le_one r).property.1
  exact ENNReal.div_ne_zero.mpr
    ⟨(U.containedFineReferenceMass_pos hdelta r j).ne',
      GeometricLemmas.dilatedTubeCarrier_volume_ne_top
        hrho hA ((U.coarse r).tube j)⟩

/-- The reference density of every full fine fiber is finite. -/
lemma fineFiberReferenceDensity_ne_top
    (hA : 1 ≤ A) (hdelta : 0 < delta)
    (r : UniformScaleIndex delta)
    (j : Fin (U.coarse r).card) :
    (U.containedFineSubfamily r j).family.toBodyFamily.density
        (dilatedTubeCarrier A ((U.coarse r).tube j)) ≠ ⊤ := by
  have hrho :
      0 < (uniformScale delta hdelta_le_one r).1 :=
    lt_of_lt_of_le hdelta
      (uniformScale delta hdelta_le_one r).property.1
  exact ENNReal.div_ne_top
    (U.containedFineReferenceMass_ne_top r j)
    (GeometricLemmas.dilatedTubeCarrier_volume_pos
      hrho hA ((U.coarse r).tube j)).ne'

/-- Every full fine-fiber Frostman constant is at least one. -/
lemma one_le_fineFiberFrostmanConstant
    (hA : 1 ≤ A) (hdelta : 0 < delta)
    (r : UniformScaleIndex delta)
    (j : Fin (U.coarse r).card) :
    1 ≤ U.fineFiberFrostmanConstant r j := by
  have hrho :
      0 < (uniformScale delta hdelta_le_one r).1 :=
    lt_of_lt_of_le hdelta
      (uniformScale delta hdelta_le_one r).property.1
  exact frostmanConstantIn_ge_one
    (GeometricLemmas.dilatedTubeCarrier_convex
      ((U.coarse r).tube j))
    (GeometricLemmas.dilatedTubeCarrier_volume_pos
      hrho hA ((U.coarse r).tube j)).ne'
    (GeometricLemmas.dilatedTubeCarrier_volume_ne_top
      hrho hA ((U.coarse r).tube j))
    (U.containedFineReferenceMass_pos hdelta r j).ne'
    (U.containedFineReferenceMass_ne_top r j)

/--
Fine-fiber Frostman control is equivalent to the pointwise density
inequality on convex subsets of the dilated parent.
-/
lemma fineFiberFrostmanConstant_le_iff
    (hA : 1 ≤ A) (hdelta : 0 < delta)
    (r : UniformScaleIndex delta)
    (j : Fin (U.coarse r).card)
    (bound : ENNReal) :
    U.fineFiberFrostmanConstant r j ≤ bound ↔
      ∀ K : Set Point3, Convex ℝ K →
        K ⊆ dilatedTubeCarrier A ((U.coarse r).tube j) →
          (U.containedFineSubfamily r j).family.toBodyFamily.density K ≤
            bound *
              (U.containedFineSubfamily r j).family.toBodyFamily.density
                (dilatedTubeCarrier A ((U.coarse r).tube j)) := by
  exact
    (U.containedFineSubfamily r j).family.toBodyFamily
      |>.isCFrostmanIn_iff_density_le_mul
        (U.fineFiberReferenceDensity_ne_zero hA hdelta r j)
        (U.fineFiberReferenceDensity_ne_top hA hdelta r j)

/--
There is one `A`-dependent finite constant comparing each full fine-fiber
reference density with the assigned uniform-fiber reference density.
-/
lemma exists_fullFineReferenceDensityComparison
    (hA : 1 ≤ A) (hdelta : 0 < delta)
    (hF_ball : F.IsInUnitBall) :
    ∃ M : ENNReal, 0 < M ∧ M ≠ ⊤ ∧
      ∀ r : UniformScaleIndex delta,
      ∀ j : Fin (U.coarse r).card,
        (U.containedFineSubfamily r j).family.toBodyFamily.density
            (dilatedTubeCarrier A ((U.coarse r).tube j)) ≤
          M * U.assignedUniformity *
            (U.fineFiberSubfamily r j).family.toBodyFamily.density
              (dilatedTubeCarrier A ((U.coarse r).tube j)) := by
  rcases
      DilatedDiscreteUniformTubeStructure.contained_parent_packing
        A hA with
    ⟨C, hC, hpacking⟩
  let M : ENNReal := ENNReal.ofReal C
  have hM : 0 < M := ENNReal.ofReal_pos.mpr hC
  have hM_top : M ≠ ⊤ := ENNReal.ofReal_ne_top
  refine ⟨M, hM, hM_top, ?_⟩
  intro r j
  have hscale :
      0 < (uniformScale delta hdelta_le_one r).1 :=
    lt_of_lt_of_le hdelta
      (uniformScale delta hdelta_le_one r).property.1
  have hpack_real :
      ((U.containedParentIndices r r j).card : ℝ) ≤ C := by
    have h :=
      hpacking delta hdelta hdelta_le_one F U r r le_rfl j
    simpa [div_self hscale.ne'] using h
  have hpack_enn :
      ((U.containedParentIndices r r j).card : ENNReal) ≤ M := by
    have h := ENNReal.ofReal_le_ofReal hpack_real
    simpa [M] using h
  exact U.containedFineDensity_le_of_parentCount_le
    hA hdelta hF_ball r j M hpack_enn

/-- Every tube in a full parent relation fiber lies in its reference
dilated parent. -/
lemma containedParentSubfamily_all_contained
    (r s : UniformScaleIndex delta)
    (k : Fin (U.coarse s).card) :
    ∀ i,
      ((U.containedParentSubfamily r s k).family.tube i).carrier ⊆
        dilatedTubeCarrier (independentCoverParentDilation A)
          ((U.coarse s).tube k) := by
  intro i
  rw [(U.containedParentSubfamily r s k).tube_eq i]
  have hi :
      (U.containedParentSubfamily r s k).embedding i ∈
        U.containedParentIndices r s k :=
    Finset.orderEmbOfFin_mem
      (U.containedParentIndices r s k) rfl i
  exact (U.mem_containedParentIndices_iff r s k
    ((U.containedParentSubfamily r s k).embedding i)).mp hi

/-- The full parent relation fiber has positive mass in its reference
dilated parent. -/
lemma containedParentReferenceMass_pos
    (hA : 1 ≤ A) (hdelta : 0 < delta)
    (hF_ball : F.IsInUnitBall)
    (r s : UniformScaleIndex delta)
    (hrs :
      (uniformScale delta hdelta_le_one r).1 ≤
        (uniformScale delta hdelta_le_one s).1)
    (k : Fin (U.coarse s).card) :
    0 <
      (U.containedParentSubfamily r s k).family.toBodyFamily.containedMass
        (dilatedTubeCarrier (independentCoverParentDilation A)
          ((U.coarse s).tube k)) := by
  have hrho :
      0 < (uniformScale delta hdelta_le_one r).1 :=
    lt_of_lt_of_le hdelta
      (uniformScale delta hdelta_le_one r).property.1
  exact TubeFamily.containedMass_pos_of_nonempty_of_all_contained
    (U.containedParentSubfamily r s k).family hrho
    (U.containedParentSubfamily_nonempty
      hA hdelta hF_ball r s hrs k)
    (U.containedParentSubfamily_all_contained r s k)

/-- The full parent relation fiber has finite mass in its reference
dilated parent. -/
lemma containedParentReferenceMass_ne_top
    (r s : UniformScaleIndex delta)
    (k : Fin (U.coarse s).card) :
    (U.containedParentSubfamily r s k).family.toBodyFamily.containedMass
        (dilatedTubeCarrier (independentCoverParentDilation A)
          ((U.coarse s).tube k)) ≠ ⊤ := by
  exact TubeFamily.containedMass_ne_top_of_all_contained
    (U.containedParentSubfamily r s k).family
    (U.containedParentSubfamily_all_contained r s k)

/-- Every common-child related parent lies in the relation reference parent. -/
lemma relatedSubfamily_all_contained
    (hA : 1 ≤ A) (hdelta : 0 < delta)
    (hF_ball : F.IsInUnitBall)
    (r s : UniformScaleIndex delta)
    (hrs :
      (uniformScale delta hdelta_le_one r).1 ≤
        (uniformScale delta hdelta_le_one s).1)
    (k : Fin (U.coarse s).card) :
    ∀ i,
      ((U.relatedSubfamily r s k).family.tube i).carrier ⊆
        dilatedTubeCarrier (independentCoverParentDilation A)
          ((U.coarse s).tube k) := by
  intro i
  rw [(U.relatedSubfamily r s k).tube_eq i]
  have hi :
      (U.relatedSubfamily r s k).embedding i ∈
        U.relatedIndices r s k :=
    Finset.orderEmbOfFin_mem (U.relatedIndices r s k) rfl i
  exact U.related_parent_containment hA hdelta hF_ball r s hrs
    ((U.relatedSubfamily r s k).embedding i) k
    ((U.mem_relatedIndices_iff r s k
      ((U.relatedSubfamily r s k).embedding i)).mp hi)

/-- The assigned relation fiber has positive reference mass. -/
lemma assignedRelationReferenceMass_pos
    (hA : 1 ≤ A) (hdelta : 0 < delta)
    (hF_ball : F.IsInUnitBall)
    (r s : UniformScaleIndex delta)
    (hrs :
      (uniformScale delta hdelta_le_one r).1 ≤
        (uniformScale delta hdelta_le_one s).1)
    (k : Fin (U.coarse s).card) :
    0 <
      (U.relatedSubfamily r s k).family.toBodyFamily.containedMass
        (dilatedTubeCarrier (independentCoverParentDilation A)
          ((U.coarse s).tube k)) := by
  have hrho :
      0 < (uniformScale delta hdelta_le_one r).1 :=
    lt_of_lt_of_le hdelta
      (uniformScale delta hdelta_le_one r).property.1
  exact TubeFamily.containedMass_pos_of_nonempty_of_all_contained
    (U.relatedSubfamily r s k).family hrho
    (U.relatedSubfamily_nonempty r s k)
    (U.relatedSubfamily_all_contained
      hA hdelta hF_ball r s hrs k)

/-- The assigned relation fiber has finite reference mass. -/
lemma assignedRelationReferenceMass_ne_top
    (hA : 1 ≤ A) (hdelta : 0 < delta)
    (hF_ball : F.IsInUnitBall)
    (r s : UniformScaleIndex delta)
    (hrs :
      (uniformScale delta hdelta_le_one r).1 ≤
        (uniformScale delta hdelta_le_one s).1)
    (k : Fin (U.coarse s).card) :
    (U.relatedSubfamily r s k).family.toBodyFamily.containedMass
        (dilatedTubeCarrier (independentCoverParentDilation A)
          ((U.coarse s).tube k)) ≠ ⊤ := by
  exact TubeFamily.containedMass_ne_top_of_all_contained
    (U.relatedSubfamily r s k).family
    (U.relatedSubfamily_all_contained
      hA hdelta hF_ball r s hrs k)

/-- Assigned relation reference density is nonzero. -/
lemma assignedRelationReferenceDensity_ne_zero
    (hA : 1 ≤ A) (hdelta : 0 < delta)
    (hF_ball : F.IsInUnitBall)
    (r s : UniformScaleIndex delta)
    (hrs :
      (uniformScale delta hdelta_le_one r).1 ≤
        (uniformScale delta hdelta_le_one s).1)
    (k : Fin (U.coarse s).card) :
    (U.relatedSubfamily r s k).family.toBodyFamily.density
        (dilatedTubeCarrier (independentCoverParentDilation A)
          ((U.coarse s).tube k)) ≠ 0 := by
  have hsigma :
      0 < (uniformScale delta hdelta_le_one s).1 :=
    lt_of_lt_of_le hdelta
      (uniformScale delta hdelta_le_one s).property.1
  have hD : 1 ≤ independentCoverParentDilation A := by
    dsimp only [independentCoverParentDilation]
    nlinarith [sq_nonneg A]
  exact ENNReal.div_ne_zero.mpr
    ⟨(U.assignedRelationReferenceMass_pos
      hA hdelta hF_ball r s hrs k).ne',
      GeometricLemmas.dilatedTubeCarrier_volume_ne_top
        hsigma hD ((U.coarse s).tube k)⟩

/-- Assigned relation reference density is finite. -/
lemma assignedRelationReferenceDensity_ne_top
    (hA : 1 ≤ A) (hdelta : 0 < delta)
    (hF_ball : F.IsInUnitBall)
    (r s : UniformScaleIndex delta)
    (hrs :
      (uniformScale delta hdelta_le_one r).1 ≤
        (uniformScale delta hdelta_le_one s).1)
    (k : Fin (U.coarse s).card) :
    (U.relatedSubfamily r s k).family.toBodyFamily.density
        (dilatedTubeCarrier (independentCoverParentDilation A)
          ((U.coarse s).tube k)) ≠ ⊤ := by
  have hsigma :
      0 < (uniformScale delta hdelta_le_one s).1 :=
    lt_of_lt_of_le hdelta
      (uniformScale delta hdelta_le_one s).property.1
  have hD : 1 ≤ independentCoverParentDilation A := by
    dsimp only [independentCoverParentDilation]
    nlinarith [sq_nonneg A]
  exact ENNReal.div_ne_top
    (U.assignedRelationReferenceMass_ne_top
      hA hdelta hF_ball r s hrs k)
    (GeometricLemmas.dilatedTubeCarrier_volume_pos
      hsigma hD ((U.coarse s).tube k)).ne'

/-- The reference density of a nonempty full parent relation fiber is
nonzero. -/
lemma relationReferenceDensity_ne_zero
    (hA : 1 ≤ A) (hdelta : 0 < delta)
    (hF_ball : F.IsInUnitBall)
    (r s : UniformScaleIndex delta)
    (hrs :
      (uniformScale delta hdelta_le_one r).1 ≤
        (uniformScale delta hdelta_le_one s).1)
    (k : Fin (U.coarse s).card) :
    (U.containedParentSubfamily r s k).family.toBodyFamily.density
        (dilatedTubeCarrier (independentCoverParentDilation A)
          ((U.coarse s).tube k)) ≠ 0 := by
  have hsigma :
      0 < (uniformScale delta hdelta_le_one s).1 :=
    lt_of_lt_of_le hdelta
      (uniformScale delta hdelta_le_one s).property.1
  have hD :
      1 ≤ independentCoverParentDilation A := by
    dsimp only [independentCoverParentDilation]
    nlinarith [sq_nonneg A]
  exact ENNReal.div_ne_zero.mpr
    ⟨(U.containedParentReferenceMass_pos
      hA hdelta hF_ball r s hrs k).ne',
      GeometricLemmas.dilatedTubeCarrier_volume_ne_top
        hsigma hD ((U.coarse s).tube k)⟩

/-- The reference density of every full parent relation fiber is finite. -/
lemma relationReferenceDensity_ne_top
    (hA : 1 ≤ A) (hdelta : 0 < delta)
    (r s : UniformScaleIndex delta)
    (k : Fin (U.coarse s).card) :
    (U.containedParentSubfamily r s k).family.toBodyFamily.density
        (dilatedTubeCarrier (independentCoverParentDilation A)
          ((U.coarse s).tube k)) ≠ ⊤ := by
  have hsigma :
      0 < (uniformScale delta hdelta_le_one s).1 :=
    lt_of_lt_of_le hdelta
      (uniformScale delta hdelta_le_one s).property.1
  have hD :
      1 ≤ independentCoverParentDilation A := by
    dsimp only [independentCoverParentDilation]
    nlinarith [sq_nonneg A]
  exact ENNReal.div_ne_top
    (U.containedParentReferenceMass_ne_top r s k)
    (GeometricLemmas.dilatedTubeCarrier_volume_pos
      hsigma hD ((U.coarse s).tube k)).ne'

/-- Every nonempty full parent-relation Frostman constant is at least one. -/
lemma one_le_relationFrostmanConstant
    (hA : 1 ≤ A) (hdelta : 0 < delta)
    (hF_ball : F.IsInUnitBall)
    (r s : UniformScaleIndex delta)
    (hrs :
      (uniformScale delta hdelta_le_one r).1 ≤
        (uniformScale delta hdelta_le_one s).1)
    (k : Fin (U.coarse s).card) :
    1 ≤ U.relationFrostmanConstant r s k := by
  have hsigma :
      0 < (uniformScale delta hdelta_le_one s).1 :=
    lt_of_lt_of_le hdelta
      (uniformScale delta hdelta_le_one s).property.1
  have hD :
      1 ≤ independentCoverParentDilation A := by
    dsimp only [independentCoverParentDilation]
    nlinarith [sq_nonneg A]
  exact frostmanConstantIn_ge_one
    (GeometricLemmas.dilatedTubeCarrier_convex
      ((U.coarse s).tube k))
    (GeometricLemmas.dilatedTubeCarrier_volume_pos
      hsigma hD ((U.coarse s).tube k)).ne'
    (GeometricLemmas.dilatedTubeCarrier_volume_ne_top
      hsigma hD ((U.coarse s).tube k))
    (U.containedParentReferenceMass_pos
      hA hdelta hF_ball r s hrs k).ne'
    (U.containedParentReferenceMass_ne_top r s k)

/--
Relation-fiber Frostman control is equivalent to the pointwise density
inequality on convex subsets of the universal parent dilation.
-/
lemma relationFrostmanConstant_le_iff
    (hA : 1 ≤ A) (hdelta : 0 < delta)
    (hF_ball : F.IsInUnitBall)
    (r s : UniformScaleIndex delta)
    (hrs :
      (uniformScale delta hdelta_le_one r).1 ≤
        (uniformScale delta hdelta_le_one s).1)
    (k : Fin (U.coarse s).card)
    (bound : ENNReal) :
    U.relationFrostmanConstant r s k ≤ bound ↔
      ∀ K : Set Point3, Convex ℝ K →
        K ⊆
          dilatedTubeCarrier (independentCoverParentDilation A)
            ((U.coarse s).tube k) →
          (U.containedParentSubfamily r s k).family.toBodyFamily.density K ≤
            bound *
              (U.containedParentSubfamily r s k).family.toBodyFamily.density
                (dilatedTubeCarrier (independentCoverParentDilation A)
                  ((U.coarse s).tube k)) := by
  exact
    (U.containedParentSubfamily r s k).family.toBodyFamily
      |>.isCFrostmanIn_iff_density_le_mul
        (U.relationReferenceDensity_ne_zero
          hA hdelta hF_ball r s hrs k)
        (U.relationReferenceDensity_ne_top hA hdelta r s k)

/--
Relation maximal density is controlled by the relation Frostman constant
times its positive finite reference density.
-/
lemma relationDeltaMax_le_frostmanConstant_mul_referenceDensity
    (hA : 1 ≤ A) (hdelta : 0 < delta)
    (hF_ball : F.IsInUnitBall)
    (r s : UniformScaleIndex delta)
    (hrs :
      (uniformScale delta hdelta_le_one r).1 ≤
        (uniformScale delta hdelta_le_one s).1)
    (k : Fin (U.coarse s).card) :
    U.relationDeltaMax r s k ≤
      U.relationFrostmanConstant r s k *
        (U.containedParentSubfamily r s k).family.toBodyFamily.density
          (dilatedTubeCarrier (independentCoverParentDilation A)
            ((U.coarse s).tube k)) := by
  exact
    (U.containedParentSubfamily r s k).family.toBodyFamily
      |>.deltaMax_le_frostmanConstantIn_mul_density
        (GeometricLemmas.dilatedTubeCarrier_convex
          ((U.coarse s).tube k))
        (U.containedParentSubfamily_all_contained r s k)
        (U.relationReferenceDensity_ne_zero
          hA hdelta hF_ball r s hrs k)
        (U.relationReferenceDensity_ne_top hA hdelta r s k)

end DilatedDiscreteUniformTubeStructure

end Kakeya.Streamlined
