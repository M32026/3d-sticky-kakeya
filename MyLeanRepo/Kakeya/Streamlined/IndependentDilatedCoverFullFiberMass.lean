import MyLeanRepo.Kakeya.Streamlined.IndependentDilatedCoverFullFiberCount
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.TubeVolume

/-!
# Mass and density comparison for full containment fibers

All fine tubes have the same radius and hence the same volume.  Therefore the
cardinality comparison between full and assigned fibers immediately yields a
mass comparison.  Since both fibers lie in the same dilated parent, it also
yields a comparison of their densities in that parent.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Streamlined

namespace TubeFamily

/-- Every indexed tube family has actual body mass equal to its nominal mass. -/
theorem bodyMass_eq_nominalMass
    {delta : ℝ} (F : TubeFamily delta) :
    F.toBodyFamily.mass = F.nominalMass := by
  let canonical : Kakeya.DeltaTube delta :=
    { base := 0
      direction := EuclideanSpace.single (0 : Fin 3) 1
      direction_unit := by
        simp [EuclideanSpace.norm_eq]
        <;> norm_num }
  have hvolume :
      ∀ i : Fin F.card,
        (F.tube i).volume = Kakeya.deltaTubeVolume delta := by
    intro i
    calc
      (F.tube i).volume = canonical.volume :=
        tube_volume_eq (F.tube i) canonical
      _ = Kakeya.deltaTubeVolume delta := rfl
  calc
    F.toBodyFamily.mass
        = ∑ i : Fin F.card, (F.tube i).volume := by
          rfl
    _ = ∑ _i : Fin F.card, Kakeya.deltaTubeVolume delta := by
      apply Finset.sum_congr rfl
      intro i _
      exact hvolume i
    _ = (F.card : ENNReal) * Kakeya.deltaTubeVolume delta := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ = F.nominalMass := rfl

end TubeFamily

namespace BodyFamily

/-- If every body lies in `U`, then the mass contained in `U` is total mass. -/
lemma containedMass_eq_mass_of_all_contained
    (F : BodyFamily) (U : Set Point3)
    (hcontained : ∀ i, (F.body i).carrier ⊆ U) :
    F.containedMass U = F.mass := by
  have hindices : F.containedIndices U = Finset.univ := by
    ext i
    simp [BodyFamily.containedIndices, hcontained i]
  rw [BodyFamily.containedMass, hindices]
  rfl

end BodyFamily

namespace DilatedDiscreteUniformTubeStructure

variable {delta A : ℝ} {F : TubeFamily delta}
variable {hdelta_le_one : delta ≤ 1}
variable (U : DilatedDiscreteUniformTubeStructure
  (A := A) F hdelta_le_one)

/-- Mass of the assigned parent fiber. -/
lemma fineFiberSubfamily_mass
    (r : UniformScaleIndex delta)
    (j : Fin (U.coarse r).card) :
    (U.fineFiberSubfamily r j).family.toBodyFamily.mass =
      (U.cover r).toFactoring.fiberCount j *
        Kakeya.deltaTubeVolume delta := by
  rw [TubeFamily.bodyMass_eq_nominalMass]
  change
    ((U.fineFiberIndices r j).card : ENNReal) *
        Kakeya.deltaTubeVolume delta =
      (U.cover r).toFactoring.fiberCount j *
        Kakeya.deltaTubeVolume delta
  have hcount :
      ((U.fineFiberIndices r j).card : ENNReal) =
        (U.cover r).toFactoring.fiberCount j := by
    rfl
  rw [hcount]

/-- Mass of the full containment fiber. -/
lemma containedFineSubfamily_mass
    (r : UniformScaleIndex delta)
    (j : Fin (U.coarse r).card) :
    (U.containedFineSubfamily r j).family.toBodyFamily.mass =
      ((U.containedFineIndices r j).card : ENNReal) *
        Kakeya.deltaTubeVolume delta := by
  rw [TubeFamily.bodyMass_eq_nominalMass]
  simp [TubeFamily.nominalMass, TubeFamily.enncard,
    containedFineSubfamily, containedFineIndices,
    DilatedTubeCover.fullContainmentFiberSubfamily,
    TubeSubfamily.fromFinset]

/-- Every assigned-fiber tube lies in the dilated parent. -/
lemma fineFiberSubfamily_all_contained
    (r : UniformScaleIndex delta)
    (j : Fin (U.coarse r).card) :
    ∀ i,
      ((U.fineFiberSubfamily r j).family.tube i).carrier ⊆
        dilatedTubeCarrier A ((U.coarse r).tube j) := by
  intro i
  rw [(U.fineFiberSubfamily r j).tube_eq i]
  have hi :
      (U.fineFiberSubfamily r j).embedding i ∈
        U.fineFiberIndices r j :=
    Finset.orderEmbOfFin_mem (U.fineFiberIndices r j) rfl i
  have hparent :
      (U.cover r).parent
          ((U.fineFiberSubfamily r j).embedding i) = j :=
    (U.mem_fineFiberIndices_iff r j
      ((U.fineFiberSubfamily r j).embedding i)).mp hi
  have h := (U.cover r).nested
    ((U.fineFiberSubfamily r j).embedding i)
  simpa [hparent] using h

/-- Every full-fiber tube lies in the dilated parent by definition. -/
lemma containedFineSubfamily_all_contained
    (r : UniformScaleIndex delta)
    (j : Fin (U.coarse r).card) :
    ∀ i,
      ((U.containedFineSubfamily r j).family.tube i).carrier ⊆
        dilatedTubeCarrier A ((U.coarse r).tube j) := by
  intro i
  rw [(U.containedFineSubfamily r j).tube_eq i]
  have hi :
      (U.containedFineSubfamily r j).embedding i ∈
        U.containedFineIndices r j :=
    Finset.orderEmbOfFin_mem (U.containedFineIndices r j) rfl i
  exact (U.mem_containedFineIndices_iff r j
    ((U.containedFineSubfamily r j).embedding i)).mp hi

/-- Cardinality comparison upgraded to a tube-mass comparison. -/
lemma containedFineMass_le_of_parentCount_le
    (hA : 1 ≤ A) (hdelta : 0 < delta)
    (hF_ball : F.IsInUnitBall)
    (r : UniformScaleIndex delta)
    (j : Fin (U.coarse r).card)
    (M : ENNReal)
    (hparent :
      ((U.containedParentIndices r r j).card : ENNReal) ≤ M) :
    (U.containedFineSubfamily r j).family.toBodyFamily.mass ≤
      M * U.assignedUniformity *
        (U.fineFiberSubfamily r j).family.toBodyFamily.mass := by
  rw [U.containedFineSubfamily_mass r j,
    U.fineFiberSubfamily_mass r j]
  have hcount := U.containedFineCount_le_of_parentCount_le
    hA hdelta hF_ball r j M hparent
  calc
    ((U.containedFineIndices r j).card : ENNReal) *
        Kakeya.deltaTubeVolume delta
        ≤ (M * U.assignedUniformity *
            (U.cover r).toFactoring.fiberCount j) *
          Kakeya.deltaTubeVolume delta := by
      exact mul_le_mul_right' hcount _
    _ = M * U.assignedUniformity *
        ((U.cover r).toFactoring.fiberCount j *
          Kakeya.deltaTubeVolume delta) := by
      ring

/-- Density comparison in the common dilated parent. -/
lemma containedFineDensity_le_of_parentCount_le
    (hA : 1 ≤ A) (hdelta : 0 < delta)
    (hF_ball : F.IsInUnitBall)
    (r : UniformScaleIndex delta)
    (j : Fin (U.coarse r).card)
    (M : ENNReal)
    (hparent :
      ((U.containedParentIndices r r j).card : ENNReal) ≤ M) :
    (U.containedFineSubfamily r j).family.toBodyFamily.density
        (dilatedTubeCarrier A ((U.coarse r).tube j)) ≤
      M * U.assignedUniformity *
        (U.fineFiberSubfamily r j).family.toBodyFamily.density
          (dilatedTubeCarrier A ((U.coarse r).tube j)) := by
  let container :=
    dilatedTubeCarrier A ((U.coarse r).tube j)
  have hfull_contained :
      (U.containedFineSubfamily r j).family.toBodyFamily.containedMass
          container =
        (U.containedFineSubfamily r j).family.toBodyFamily.mass :=
    BodyFamily.containedMass_eq_mass_of_all_contained _ _ fun i =>
      U.containedFineSubfamily_all_contained r j i
  have hselected_contained :
      (U.fineFiberSubfamily r j).family.toBodyFamily.containedMass
          container =
        (U.fineFiberSubfamily r j).family.toBodyFamily.mass :=
    BodyFamily.containedMass_eq_mass_of_all_contained _ _ fun i =>
      U.fineFiberSubfamily_all_contained r j i
  dsimp only [BodyFamily.density]
  rw [hfull_contained, hselected_contained]
  have hmass := U.containedFineMass_le_of_parentCount_le
    hA hdelta hF_ball r j M hparent
  calc
    (U.containedFineSubfamily r j).family.toBodyFamily.mass /
        volume container
        ≤ (M * U.assignedUniformity *
            (U.fineFiberSubfamily r j).family.toBodyFamily.mass) /
          volume container := by
      gcongr
    _ = M * U.assignedUniformity *
        ((U.fineFiberSubfamily r j).family.toBodyFamily.mass /
          volume container) := by
      simp [div_eq_mul_inv]
      ring

end DilatedDiscreteUniformTubeStructure

end Kakeya.Streamlined
