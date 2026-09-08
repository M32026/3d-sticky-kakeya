import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.TranslateTubeGeometry
import MyLeanRepo.Kakeya.Streamlined.Estimates

/-!
# Translation of legacy strict uniform structures

Pure tube translation geometry lives in `TranslateTubeGeometry`.  This module
retains only the historical strict `TubeCover` and `UniformTubeStructure`
transport.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Streamlined.RandomTranslation

/-- Translate a TubeCover by a fixed vector. -/
def translateTubeCover {δ ρ : ℝ} {F : TubeFamily δ} {G : TubeFamily ρ}
    (P : TubeCover F G) (v : Point3) :
    TubeCover (translateTubeFamily F v) (translateTubeFamily G v) where
  parent := P.parent
  parent_surjective := P.parent_surjective
  nested := fun i => by
    have h : (F.tube i).carrier ⊆ (G.tube (P.parent i)).carrier := P.nested i
    have h_fine : (translateTubeFamily F v).tube i = translateTube (F.tube i) v := by rfl
    have h_coarse : (translateTubeFamily G v).tube (P.parent i) =
        translateTube (G.tube (P.parent i)) v := by rfl
    rw [h_fine, h_coarse]
    rw [translateTube_carrier (F.tube i) v, translateTube_carrier (G.tube (P.parent i)) v]
    exact Set.image_mono h

/-- Translation changes carriers but not the underlying parent function. -/
lemma translateTubeCover_toFactoring_parent
    {δ ρ : ℝ} {F : TubeFamily δ} {G : TubeFamily ρ}
    (P : TubeCover F G) (v : Point3) (i : Fin F.card) :
    (translateTubeCover P v).toFactoring.parent i =
      P.toFactoring.parent i :=
  rfl

/-- Translation preserves every canonical factoring fiber count. -/
lemma translateTubeCover_fiberCount
    {δ ρ : ℝ} {F : TubeFamily δ} {G : TubeFamily ρ}
    (P : TubeCover F G) (v : Point3) (j : Fin G.card) :
    (translateTubeCover P v).toFactoring.fiberCount j =
      P.toFactoring.fiberCount j := by
  unfold Factoring.fiberCount Factoring.fiberIndices
  change
    ((Finset.univ.filter fun i : Fin F.card =>
      P.parent i = j).card : ENNReal) =
      ((Finset.univ.filter fun i : Fin F.card =>
        P.parent i = j).card : ENNReal)
  rfl

/-- Translation preserves the chosen-parent factoring counts exactly. -/
lemma translateTubeCover_fibersAreCUniform
    {δ ρ : ℝ} {F : TubeFamily δ} {G : TubeFamily ρ}
    (P : TubeCover F G) (v : Point3) {C : ENNReal}
    (hP : P.toFactoring.FibersAreCUniform C) :
    (translateTubeCover P v).toFactoring.FibersAreCUniform C := by
  refine ⟨hP.1, ?_⟩
  intro first second
  rw [translateTubeCover_fiberCount,
    translateTubeCover_fiberCount]
  exact hP.2 first second

namespace AssignedUniformTubeStructure

variable {δ : ℝ} {F : TubeFamily δ}
variable (U : AssignedUniformTubeStructure F) (v : Point3)

/-- Translate an assigned uniform tube structure by a fixed vector. -/
def translate :
    AssignedUniformTubeStructure (translateTubeFamily F v) where
  coarse := fun rho => translateTubeFamily (U.coarse rho) v
  cover := fun rho => translateTubeCover (U.cover rho) v
  assignedUniformity := U.assignedUniformity
  one_le_assignedUniformity := U.one_le_assignedUniformity
  assignedUniformity_ne_top := U.assignedUniformity_ne_top
  assignedUniform := fun rho =>
    translateTubeCover_fibersAreCUniform
      (U.cover rho) v (U.assignedUniform rho)
  coarse_distinct := fun rho =>
    translateFamily_essentiallyDistinct (U.coarse_distinct rho)

end AssignedUniformTubeStructure

end Kakeya.Streamlined.RandomTranslation
