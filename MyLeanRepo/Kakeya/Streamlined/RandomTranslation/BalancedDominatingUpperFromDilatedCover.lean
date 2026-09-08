import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.BalancedDominatingUpperDilatedCover
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.DilatedTubeCarrierComposition

/-!
# Balanced dominating upper covers from an already dilated lower cover

The lower cover may already use a fixed homothetic dilation `A`.  After
coaxially enlarging its parents to the target radius, maximal
essential-distinct representatives merge whole old fibers.  The fine family
is not selected again.

Composing the original `A`-dilated containment with the universal `2000`
representative containment gives the fixed output dilation

`2000 * (2 * A - 1)`.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

open MeasureTheory
open Kakeya.Streamlined.GeometricLemmas
open Kakeya.Streamlined.RandomTranslation.WithShading
open Kakeya.Streamlined.WithShading

namespace Kakeya.Streamlined.RandomTranslation

/-- Output dilation after whole-fiber representative merging. -/
def dominatingUpperFromDilatedCoverDilation (A : ℝ) : ℝ :=
  2000 * (2 * A - 1)

/-- Increasing the tube radius preserves every nonnegative homothetic
dilation of its carrier. -/
lemma dilatedTubeCarrier_subset_withRadius
    {sigma rho A : ℝ}
    (hA : 0 ≤ A)
    (hsigma_rho : sigma ≤ rho)
    (T : Kakeya.DeltaTube sigma) :
    dilatedTubeCarrier A T ⊆
      dilatedTubeCarrier A (withRadius rho T) := by
  change
    AffineMap.homothety (tubeMidpoint T) A '' T.carrier ⊆
      AffineMap.homothety
        (tubeMidpoint (withRadius rho T)) A ''
          (withRadius rho T).carrier
  rw [withRadius_midpoint]
  exact Set.image_mono (carrier_subset_withRadius hsigma_rho T)

/-- A balanced dilated lower cover produces an essentially-distinct upper
cover without changing the fine family. -/
structure BalancedDominatingUpperFromDilatedCoverPackage
    {delta sigma rho A : ℝ}
    {fine : TubeFamily delta} {lower : TubeFamily sigma}
    (P : DilatedTubeCover A fine lower)
    (C : ENNReal) (D : ℕ) where
  upper : TubeFamily rho
  cover :
    DilatedTubeCover
      (dominatingUpperFromDilatedCoverDilation A)
      fine upper
  upperEssentiallyDistinct : upper.IsEssentiallyDistinct
  assignedUniform :
    cover.toFactoring.FibersAreCUniform
      (((D + 1 : ℕ) : ENNReal) * C)
  lowerParent : Fin lower.card → Fin upper.card
  cover_parent :
    ∀ index, cover.parent index = lowerParent (P.parent index)
  factoringFiberIndices_lower :
    ∀ upperIndex, ∃ lowerIndex,
      P.toFactoring.fiberIndices lowerIndex ⊆
        cover.toFactoring.fiberIndices upperIndex
  factoringFiberCount_lower :
    ∀ upperIndex, ∃ lowerIndex,
      P.toFactoring.fiberCount lowerIndex ≤
        cover.toFactoring.fiberCount upperIndex

/-- Merge whole fibers of an already dilated cover into maximal ED
representatives at a larger radius. -/
theorem balanced_dominating_upper_from_dilated_cover
    {delta sigma rho A : ℝ}
    {fine : TubeFamily delta} {lower : TubeFamily sigma}
    (P : DilatedTubeCover A fine lower)
    (C : ENNReal) (D : ℕ)
    (hA : 1 ≤ A)
    (hfine : fine.Nonempty)
    (hrho : 0 < rho)
    (hsigma_rho : sigma ≤ rho)
    (hrho_one : rho ≤ 1)
    (huniform : P.toFactoring.FibersAreCUniform C)
    (hdegree :
      ∀ parent : Fin lower.card,
        ((Finset.univ : Finset (Fin lower.card)).filter
          fun other =>
            other ≠ parent ∧
              ¬((sameAxisEnlargedFamily
                (rho := rho) lower).tube parent).EssentiallyDistinct
                ((sameAxisEnlargedFamily
                  (rho := rho) lower).tube other)).card ≤ D) :
    Nonempty
      (BalancedDominatingUpperFromDilatedCoverPackage
        (rho := rho) P C D) := by
  classical
  let candidates : TubeFamily rho :=
    sameAxisEnlargedFamily (rho := rho) lower
  rcases exists_maximal_essentially_distinct_subfamily candidates with
    ⟨indices, hindices_ed, hmaximal⟩
  let upper : TubeSubfamily candidates :=
    TubeSubfamily.fromFinset candidates indices

  let representative : Fin candidates.card → Fin candidates.card :=
    fun parent =>
      if hparent : parent ∈ indices then parent
      else Classical.choose (hmaximal parent hparent)
  have hrepresentative_mem :
      ∀ parent, representative parent ∈ indices := by
    intro parent
    by_cases hparent : parent ∈ indices
    · simp [representative, hparent]
    · simpa [representative, hparent] using
        (Classical.choose_spec (hmaximal parent hparent)).1
  have hrepresentative_eq :
      ∀ parent, parent ∈ indices →
        representative parent = parent := by
    intro parent hparent
    simp [representative, hparent]
  have hrepresentative_conflict :
      ∀ parent, parent ∉ indices →
        ¬(candidates.tube parent).EssentiallyDistinct
          (candidates.tube (representative parent)) := by
    intro parent hparent
    simpa [representative, hparent] using
      (Classical.choose_spec (hmaximal parent hparent)).2

  have hupper_image :
      Finset.image upper.embedding Finset.univ = indices :=
    Finset.image_orderEmbOfFin_univ indices rfl
  have hpreimage :
      ∀ parent : Fin candidates.card, parent ∈ indices →
        ∃ localIndex : Fin upper.family.card,
          upper.embedding localIndex = parent := by
    intro parent hparent
    have hmem :
        parent ∈ Finset.image upper.embedding Finset.univ := by
      rw [hupper_image]
      exact hparent
    rcases Finset.mem_image.mp hmem with
      ⟨localIndex, _hlocal, hlocal⟩
    exact ⟨localIndex, hlocal⟩
  let toUpper
      (parent : Fin candidates.card)
      (hparent : parent ∈ indices) :
      Fin upper.family.card :=
    Classical.choose (hpreimage parent hparent)
  have htoUpper :
      ∀ parent hparent,
        upper.embedding (toUpper parent hparent) = parent := by
    intro parent hparent
    exact Classical.choose_spec (hpreimage parent hparent)

  let lowerParent (parent : Fin lower.card) :
      Fin upper.family.card :=
    toUpper
      (representative parent)
      (hrepresentative_mem parent)
  let parentMap (index : Fin fine.card) :
      Fin upper.family.card :=
    lowerParent (P.parent index)
  have hparentMap :
      ∀ index,
        upper.embedding (parentMap index) =
          representative (P.parent index) := by
    intro index
    exact htoUpper
      (representative (P.parent index))
      (hrepresentative_mem (P.parent index))

  have hconflict_containment :
      ∀ first second : Fin candidates.card,
        ¬(candidates.tube first).EssentiallyDistinct
          (candidates.tube second) →
        (candidates.tube first).carrier ⊆
          dilatedTubeCarrier 2000
            (candidates.tube second) := by
    intro first second hconflict
    have hfirstVolume :
        (candidates.tube first).volume =
          Kakeya.deltaTubeVolume rho :=
      tube_volume_eq_deltaTubeVolume (candidates.tube first)
    have hsecondVolume :
        (candidates.tube second).volume =
          Kakeya.deltaTubeVolume rho :=
      tube_volume_eq_deltaTubeVolume (candidates.tube second)
    have hoverlap :
        volume
            ((candidates.tube first).carrier ∩
              (candidates.tube second).carrier) >
          (candidates.tube first).volume /
            ENNReal.ofReal 2 := by
      change
        ¬ volume
            ((candidates.tube first).carrier ∩
              (candidates.tube second).carrier) ≤
          (2 : ENNReal)⁻¹ *
            max (candidates.tube first).volume
              (candidates.tube second).volume at hconflict
      have hgt := lt_of_not_ge hconflict
      rw [hfirstVolume, hsecondVolume, max_self] at hgt
      rw [hfirstVolume]
      simpa [div_eq_mul_inv, mul_comm] using hgt
    have hcontain :=
      strong_containment_via_translation
        hrho hrho_one (K := 2) (by norm_num) hoverlap
    norm_num at hcontain ⊢
    exact hcontain

  have hnested :
      ∀ index,
        (fine.tube index).carrier ⊆
          dilatedTubeCarrier
            (dominatingUpperFromDilatedCoverDilation A)
            (upper.family.tube (parentMap index)) := by
    intro index
    have hfine_lower :
        (fine.tube index).carrier ⊆
          dilatedTubeCarrier A
            (lower.tube (P.parent index)) :=
      P.nested index
    have hlower_candidate :
        dilatedTubeCarrier A
            (lower.tube (P.parent index)) ⊆
          dilatedTubeCarrier A
            (candidates.tube (P.parent index)) := by
      simpa [candidates, sameAxisEnlargedFamily_tube] using
        dilatedTubeCarrier_subset_withRadius
          (zero_le_one.trans hA) hsigma_rho
          (lower.tube (P.parent index))
    have hcandidates :
        (candidates.tube (P.parent index)).carrier ⊆
          dilatedTubeCarrier 2000
            (candidates.tube
              (representative (P.parent index))) := by
      by_cases hparent : P.parent index ∈ indices
      · rw [hrepresentative_eq (P.parent index) hparent]
        exact self_dilated_containment 2000
          (by norm_num) (candidates.tube (P.parent index))
      · exact hconflict_containment
          (P.parent index)
          (representative (P.parent index))
          (hrepresentative_conflict (P.parent index) hparent)
    have hcomposed :
        dilatedTubeCarrier A
            (candidates.tube (P.parent index)) ⊆
          dilatedTubeCarrier
            (dominatingUpperFromDilatedCoverDilation A)
            (candidates.tube
              (representative (P.parent index))) := by
      exact
        dilatedTubeCarrier_comp_subset
          hrho.le
          (by norm_num : (1 : ℝ) ≤ 2000)
          hA
          (candidates.tube (P.parent index))
          (candidates.tube
            (representative (P.parent index)))
          hcandidates
    rw [upper.tube_eq (parentMap index), hparentMap index]
    exact hfine_lower.trans
      (hlower_candidate.trans hcomposed)

  have hsurjective : Function.Surjective parentMap := by
    intro localIndex
    let ambient : Fin candidates.card :=
      upper.embedding localIndex
    have hambient : ambient ∈ indices := by
      have h :
          ambient ∈ Finset.image upper.embedding Finset.univ :=
        Finset.mem_image.mpr
          ⟨localIndex, Finset.mem_univ localIndex, rfl⟩
      rwa [hupper_image] at h
    rcases P.parent_surjective ambient with
      ⟨fineIndex, hfineIndex⟩
    refine ⟨fineIndex, ?_⟩
    apply upper.embedding.injective
    rw [hparentMap fineIndex, hfineIndex,
      hrepresentative_eq ambient hambient]

  let Q :
      DilatedTubeCover
        (dominatingUpperFromDilatedCoverDilation A)
        fine upper.family :=
    { parent := parentMap
      parent_surjective := hsurjective
      nested := hnested }

  have hupper_ed : upper.family.IsEssentiallyDistinct := by
    intro first second hne
    have hfirst :
        upper.embedding first ∈ indices :=
      Finset.orderEmbOfFin_mem indices rfl first
    have hsecond :
        upper.embedding second ∈ indices :=
      Finset.orderEmbOfFin_mem indices rfl second
    have hembedding :
        upper.embedding first ≠ upper.embedding second :=
      fun h => hne (upper.embedding.injective h)
    rw [upper.tube_eq first, upper.tube_eq second]
    exact hindices_ed
      (upper.embedding first) hfirst
      (upper.embedding second) hsecond hembedding

  let oldParents (localIndex : Fin upper.family.card) :
      Finset (Fin lower.card) :=
    Finset.univ.filter fun parent =>
      representative parent = upper.embedding localIndex
  have holdParents_subset :
      ∀ localIndex,
        oldParents localIndex ⊆
          insert (upper.embedding localIndex)
            ((Finset.univ : Finset (Fin lower.card)).filter
              fun other =>
                other ≠ upper.embedding localIndex ∧
                  ¬(candidates.tube
                    (upper.embedding localIndex)).EssentiallyDistinct
                    (candidates.tube other)) := by
    intro localIndex parent hparent
    have hrepresent :
        representative parent = upper.embedding localIndex :=
      (Finset.mem_filter.mp hparent).2
    by_cases heq : parent = upper.embedding localIndex
    · exact Finset.mem_insert.mpr (Or.inl heq)
    · have hparent_not_selected : parent ∉ indices := by
        intro hselected
        have hid := hrepresentative_eq parent hselected
        exact heq (hid.symm.trans hrepresent)
      have hconflict :=
        hrepresentative_conflict parent hparent_not_selected
      rw [hrepresent] at hconflict
      have hsymm :
          ¬(candidates.tube
            (upper.embedding localIndex)).EssentiallyDistinct
            (candidates.tube parent) := by
        simpa [Kakeya.DeltaTube.EssentiallyDistinct,
          Set.inter_comm, max_comm] using hconflict
      exact Finset.mem_insert.mpr
        (Or.inr (Finset.mem_filter.mpr
          ⟨Finset.mem_univ parent, heq, hsymm⟩))
  have holdParents_card :
      ∀ localIndex,
        (oldParents localIndex).card ≤ D + 1 := by
    intro localIndex
    calc
      (oldParents localIndex).card ≤
          (insert (upper.embedding localIndex)
            ((Finset.univ : Finset (Fin lower.card)).filter
              fun other =>
                other ≠ upper.embedding localIndex ∧
                  ¬(candidates.tube
                    (upper.embedding localIndex)).EssentiallyDistinct
                    (candidates.tube other))).card :=
        Finset.card_le_card (holdParents_subset localIndex)
      _ ≤
          ((Finset.univ : Finset (Fin lower.card)).filter
            fun other =>
              other ≠ upper.embedding localIndex ∧
                ¬(candidates.tube
                  (upper.embedding localIndex)).EssentiallyDistinct
                  (candidates.tube other)).card + 1 :=
        Finset.card_insert_le _ _
      _ ≤ D + 1 :=
        Nat.add_le_add_right
          (hdegree (upper.embedding localIndex)) 1

  have hQfiber :
      ∀ localIndex,
        Q.toFactoring.fiberCount localIndex =
          ∑ parent ∈ oldParents localIndex,
            P.toFactoring.fiberCount parent := by
    intro localIndex
    let newFiber : Finset (Fin fine.card) :=
      Finset.univ.filter fun index =>
        Q.parent index = localIndex
    have hnewFiber :
        newFiber =
          Finset.univ.filter fun index =>
            P.parent index ∈ oldParents localIndex := by
      ext index
      simp only [newFiber, Finset.mem_filter, Finset.mem_univ,
        true_and, oldParents]
      constructor
      · intro h
        have hembedding := congrArg upper.embedding h
        rw [hparentMap index] at hembedding
        exact hembedding
      · intro h
        apply upper.embedding.injective
        rw [hparentMap index]
        exact h
    have hsumNat :
        ∑ parent ∈ oldParents localIndex,
            (Finset.univ.filter fun index : Fin fine.card =>
              P.parent index = parent).card =
          (Finset.univ.filter fun index : Fin fine.card =>
            P.parent index ∈ oldParents localIndex).card := by
      simpa using
        (Finset.sum_card_fiberwise_eq_card_filter
          (s := (Finset.univ : Finset (Fin fine.card)))
          (t := oldParents localIndex)
          (g := P.parent))
    change
      (newFiber.card : ENNReal) =
        ∑ parent ∈ oldParents localIndex,
          ((Finset.univ.filter fun index : Fin fine.card =>
            P.parent index = parent).card : ENNReal)
    rw [hnewFiber]
    exact_mod_cast hsumNat.symm

  have holdSelf :
      ∀ localIndex,
        upper.embedding localIndex ∈ oldParents localIndex := by
    intro localIndex
    have hselected :
        upper.embedding localIndex ∈ indices :=
      Finset.orderEmbOfFin_mem indices rfl localIndex
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,
        hrepresentative_eq
          (upper.embedding localIndex) hselected⟩

  have huniformQ :
      Q.toFactoring.FibersAreCUniform
        (((D + 1 : ℕ) : ENNReal) * C) := by
    constructor
    · have hD : (1 : ENNReal) ≤ (D + 1 : ℕ) := by
        exact_mod_cast Nat.succ_pos D
      calc
        (1 : ENNReal) = 1 * 1 := by simp
        _ ≤ ((D + 1 : ℕ) : ENNReal) * C :=
          mul_le_mul' hD huniform.1
    · intro first second
      rw [hQfiber first, hQfiber second]
      calc
        (∑ parent ∈ oldParents first,
            P.toFactoring.fiberCount parent) ≤
          ∑ _parent ∈ oldParents first,
            C * P.toFactoring.fiberCount (upper.embedding second) := by
          apply Finset.sum_le_sum
          intro parent _
          exact huniform.2 parent (upper.embedding second)
        _ =
          ((oldParents first).card : ENNReal) *
            (C * P.toFactoring.fiberCount (upper.embedding second)) := by
          simp [Finset.sum_const, nsmul_eq_mul]
        _ ≤
          ((D + 1 : ℕ) : ENNReal) *
            (C * P.toFactoring.fiberCount (upper.embedding second)) := by
          gcongr
          exact_mod_cast holdParents_card first
        _ =
          (((D + 1 : ℕ) : ENNReal) * C) *
            P.toFactoring.fiberCount (upper.embedding second) := by
          ring
        _ ≤
          (((D + 1 : ℕ) : ENNReal) * C) *
            (∑ parent ∈ oldParents second,
              P.toFactoring.fiberCount parent) := by
          gcongr
          exact Finset.single_le_sum
            (fun _ _ => by positivity) (holdSelf second)

  exact ⟨{
    upper := upper.family
    cover := Q
    upperEssentiallyDistinct := hupper_ed
    assignedUniform := huniformQ
    lowerParent := lowerParent
    cover_parent := fun _ => rfl
    factoringFiberIndices_lower := by
      intro localIndex
      refine ⟨upper.embedding localIndex, ?_⟩
      intro fineIndex hfineIndex
      have hparent :
          P.parent fineIndex = upper.embedding localIndex :=
        (Finset.mem_filter.mp hfineIndex).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ fineIndex, ?_⟩
      change parentMap fineIndex = localIndex
      apply upper.embedding.injective
      rw [hparentMap fineIndex, hparent,
        hrepresentative_eq (upper.embedding localIndex)
          (Finset.orderEmbOfFin_mem indices rfl localIndex)]
    factoringFiberCount_lower := by
      intro localIndex
      refine ⟨upper.embedding localIndex, ?_⟩
      rw [hQfiber localIndex]
      exact Finset.single_le_sum
        (fun _ _ => by positivity) (holdSelf localIndex)
  }⟩

end Kakeya.Streamlined.RandomTranslation

end
