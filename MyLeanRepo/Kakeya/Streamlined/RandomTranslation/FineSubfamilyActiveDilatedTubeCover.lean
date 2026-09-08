import MyLeanRepo.Kakeya.Streamlined.DilatedTubeCover.FullContainmentFibers
import MyLeanRepo.Kakeya.Streamlined.TubeRefinement

/-!
# Restrict a dilated tube cover to active parents

An arbitrary fine subfamily need not hit every coarse parent.  This module
keeps exactly the image of the auxiliary parent map and restricts a genuine
`DilatedTubeCover` to those active parents.

The construction records assigned-parent bookkeeping only.  It does not
claim that the restricted assigned fibers are complete geometric full fibers.
-/

noncomputable section

namespace Kakeya.Streamlined.RandomTranslation

open Kakeya.Streamlined

/-- Active-parent restriction of one genuine dilated cover. -/
structure FineSubfamilyActiveDilatedTubeCover
    {delta rho A : ℝ}
    {fine : TubeFamily delta}
    {coarse : TubeFamily rho}
    (P : DilatedTubeCover A fine coarse)
    (S : TubeSubfamily fine) where
  R : TubeSubfamily coarse
  Q : DilatedTubeCover A S.family R.family
  R_image :
    Finset.image R.embedding Finset.univ =
      Finset.image
        (fun index : Fin S.family.card =>
          P.parent (S.embedding index))
        Finset.univ
  Q_parent :
    ∀ index,
      R.embedding (Q.parent index) =
        P.parent (S.embedding index)
  Q_fiberCount :
    ∀ parent,
      Q.toFactoring.fiberCount parent =
        ((Finset.univ.filter
          fun index : Fin S.family.card =>
            P.parent (S.embedding index) =
              R.embedding parent).card : ENNReal)

/-- Canonical active-parent restriction of one genuine dilated cover. -/
def fineSubfamilyActiveDilatedTubeCover
    {delta rho A : ℝ}
    {fine : TubeFamily delta}
    {coarse : TubeFamily rho}
    (P : DilatedTubeCover A fine coarse)
    (S : TubeSubfamily fine) :
    FineSubfamilyActiveDilatedTubeCover P S := by
  classical
  let activeParents : Finset (Fin coarse.card) :=
    Finset.image
      (fun index : Fin S.family.card =>
        P.parent (S.embedding index))
      Finset.univ
  let R : TubeSubfamily coarse :=
    TubeSubfamily.fromFinset coarse activeParents
  have hRImage :
      Finset.image R.embedding Finset.univ =
        activeParents :=
    Finset.image_orderEmbOfFin_univ activeParents rfl
  let indexInR
      (parent : Fin coarse.card)
      (hparent : parent ∈ activeParents) :
      Fin R.family.card :=
    Classical.choose <|
      Finset.mem_image.mp <| by
        rw [hRImage]
        exact hparent
  have hindexInR :
      ∀ (parent : Fin coarse.card)
        (hparent : parent ∈ activeParents),
        R.embedding (indexInR parent hparent) = parent := by
    intro parent hparent
    exact
      (Classical.choose_spec <|
        Finset.mem_image.mp <| by
          rw [hRImage]
          exact hparent).2
  have hactive :
      ∀ index : Fin S.family.card,
        P.parent (S.embedding index) ∈ activeParents := by
    intro index
    exact Finset.mem_image.mpr
      ⟨index, Finset.mem_univ index, rfl⟩
  let parent (index : Fin S.family.card) : Fin R.family.card :=
    indexInR
      (P.parent (S.embedding index))
      (hactive index)
  have hparent :
      ∀ index,
        R.embedding (parent index) =
          P.parent (S.embedding index) := by
    intro index
    exact hindexInR _ (hactive index)
  have hsurjective : Function.Surjective parent := by
    intro target
    have htarget :
        R.embedding target ∈ activeParents := by
      have hmem :
          R.embedding target ∈
            Finset.image R.embedding Finset.univ :=
        Finset.mem_image.mpr
          ⟨target, Finset.mem_univ target, rfl⟩
      rwa [hRImage] at hmem
    rcases Finset.mem_image.mp htarget with
      ⟨index, _hindex, htargetParent⟩
    refine ⟨index, ?_⟩
    apply R.embedding.injective
    rw [hparent index]
    exact htargetParent
  let Q : DilatedTubeCover A S.family R.family :=
    { parent := parent
      parent_surjective := hsurjective
      nested := fun index => by
        rw [S.tube_eq index, R.tube_eq (parent index), hparent index]
        exact P.nested (S.embedding index) }
  have hfiber :
      ∀ target,
        Q.toFactoring.fiberCount target =
          ((Finset.univ.filter
            fun index : Fin S.family.card =>
              P.parent (S.embedding index) =
                R.embedding target).card : ENNReal) := by
    intro target
    have hfilter :
        (Finset.univ.filter
          fun index : Fin S.family.card =>
            Q.parent index = target) =
        (Finset.univ.filter
          fun index : Fin S.family.card =>
            P.parent (S.embedding index) =
              R.embedding target) := by
      ext index
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hindex
        have himage :=
          congrArg R.embedding hindex
        rw [hparent index] at himage
        exact himage
      · intro hindex
        apply R.embedding.injective
        rw [hparent index]
        exact hindex
    change
      ((Finset.univ.filter fun index : Fin S.family.card =>
        Q.parent index = target).card : ENNReal) =
        ((Finset.univ.filter fun index : Fin S.family.card =>
          P.parent (S.embedding index) =
            R.embedding target).card : ENNReal)
    rw [hfilter]
  exact
    { R := R
      Q := Q
      R_image := hRImage
      Q_parent := hparent
      Q_fiberCount := hfiber }

end Kakeya.Streamlined.RandomTranslation

end
