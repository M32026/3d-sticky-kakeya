import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12BodyReindex

/-!
# Actual BodyFamily CWA through a uniform cover

The coarse quotient branch is not one-to-one: several fine bodies may be
assigned to one coarse body.  This module is the actual-body analogue of the
historical cropped-tube uniform-cover transfer.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

/--
Transfer normalized Convex-Wolff counting from a fine actual BodyFamily to a
surjective, uniformly sized coarse cover.
-/
theorem wz2PaperBodyConvexWolffBound_of_uniform_cover
    {fine coarse : Kakeya.Streamlined.BodyFamily}
    (parent : Fin fine.card → Fin coarse.card)
    (parent_surjective : Function.Surjective parent)
    (carrier_contained :
      ∀ source,
        (fine.body source).carrier ⊆
          (coarse.body (parent source)).carrier)
    (K C : ENNReal)
    (fiber_uniform :
      ∀ first second,
        ((Finset.univ.filter fun source =>
          parent source = first).card : ENNReal) ≤
          K *
            ((Finset.univ.filter fun source =>
              parent source = second).card : ENNReal))
    (hfine : WZ2PaperBodyConvexWolffBound fine C) :
    WZ2PaperBodyConvexWolffBound coarse (K * C) := by
  intro convexSet hconvex
  let coarseContained := coarse.containedIndices convexSet
  let fineContained := fine.containedIndices convexSet
  have hparentContained :
      ∀ source, parent source ∈ coarseContained →
        source ∈ fineContained := by
    intro source hparent
    exact
      (Kakeya.Streamlined.BodyFamily.mem_containedIndices_iff).mpr
        ((carrier_contained source).trans
          ((Kakeya.Streamlined.BodyFamily.mem_containedIndices_iff).mp
            hparent))
  by_cases hcoarseEmpty : coarse.card = 0
  · have hcontainedZero : coarse.containedCount convexSet = 0 := by
      unfold Kakeya.Streamlined.BodyFamily.containedCount
      have hindicesEmpty : coarse.containedIndices convexSet = ∅ := by
        ext index
        exfalso
        exact Fin.elim0 (hcoarseEmpty ▸ index)
      rw [hindicesEmpty]
      simp
    rw [hcontainedZero]
    exact bot_le
  · let fiber : Fin coarse.card → Finset (Fin fine.card) :=
      fun coarseIndex =>
        Finset.univ.filter fun source =>
          parent source = coarseIndex
    letI : Nonempty (Fin coarse.card) :=
      ⟨⟨0, Nat.pos_of_ne_zero hcoarseEmpty⟩⟩
    obtain ⟨reference, _href, hreferenceMin⟩ :=
      Finset.exists_min_image
        (Finset.univ : Finset (Fin coarse.card))
        (fun coarseIndex => (fiber coarseIndex).card)
        Finset.univ_nonempty
    let referenceFiber := fiber reference
    have hreferenceNonempty : referenceFiber.Nonempty := by
      rcases parent_surjective reference with ⟨source, hsource⟩
      exact
        ⟨source, Finset.mem_filter.mpr
          ⟨Finset.mem_univ source, hsource⟩⟩
    have hreferencePos :
        0 < (referenceFiber.card : ENNReal) := by
      exact_mod_cast Finset.card_pos.mpr hreferenceNonempty
    have hreferenceTop :
        (referenceFiber.card : ENNReal) ≠ ⊤ := by simp
    have hcoarseToFineNat :
        coarseContained.card * referenceFiber.card ≤
          fineContained.card := by
      let selectedFine :=
        Finset.univ.filter fun source =>
          parent source ∈ coarseContained
      have hselectedSubset : selectedFine ⊆ fineContained := by
        intro source hsource
        exact hparentContained source
          (Finset.mem_filter.mp hsource).2
      have hsum :
          ∑ coarseIndex ∈ coarseContained,
              (fiber coarseIndex).card =
            selectedFine.card := by
        simpa only [fiber, selectedFine] using
          Finset.sum_card_fiberwise_eq_card_filter
            (Finset.univ : Finset (Fin fine.card))
            coarseContained parent
      calc
        coarseContained.card * referenceFiber.card =
            ∑ _coarseIndex ∈ coarseContained,
              referenceFiber.card := by
          simp [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ coarseIndex ∈ coarseContained,
              (fiber coarseIndex).card := by
          exact Finset.sum_le_sum fun coarseIndex hcoarse =>
            hreferenceMin coarseIndex (Finset.mem_univ coarseIndex)
        _ = selectedFine.card := hsum
        _ ≤ fineContained.card :=
          Finset.card_le_card hselectedSubset
    have hcoarseToFine :
        (coarseContained.card : ENNReal) *
            (referenceFiber.card : ENNReal) ≤
          (fineContained.card : ENNReal) := by
      exact_mod_cast hcoarseToFineNat
    have hfineBound :
        (fineContained.card : ENNReal) ≤
          C * volume convexSet * fine.enncard := by
      simpa [fineContained,
        Kakeya.Streamlined.BodyFamily.containedCount] using
          hfine convexSet hconvex
    have htotalFibers :
        fine.enncard ≤
          K * coarse.enncard *
            (referenceFiber.card : ENNReal) := by
      let allCoarse : Finset (Fin coarse.card) := Finset.univ
      have hsum :
          ∑ coarseIndex ∈ allCoarse,
              (fiber coarseIndex).card =
            fine.card := by
        simpa only [fiber] using
          (Finset.sum_card_fiberwise_eq_card_filter
            (Finset.univ : Finset (Fin fine.card))
            allCoarse parent).trans (by simp [allCoarse])
      have hsumUpper :
          ∑ coarseIndex ∈ allCoarse,
              ((fiber coarseIndex).card : ENNReal) ≤
            ∑ _coarseIndex ∈ allCoarse,
              K * (referenceFiber.card : ENNReal) := by
        exact Finset.sum_le_sum fun coarseIndex _ => by
          simpa [fiber, referenceFiber] using
            fiber_uniform coarseIndex reference
      rw [show fine.enncard =
          ∑ coarseIndex ∈ allCoarse,
            ((fiber coarseIndex).card : ENNReal) by
        change (fine.card : ENNReal) =
          ∑ coarseIndex ∈ allCoarse,
            ((fiber coarseIndex).card : ENNReal)
        exact_mod_cast hsum.symm]
      calc
        ∑ coarseIndex ∈ allCoarse,
            ((fiber coarseIndex).card : ENNReal) ≤
          ∑ _coarseIndex ∈ allCoarse,
            K * (referenceFiber.card : ENNReal) :=
          hsumUpper
        _ =
            K * coarse.enncard *
              (referenceFiber.card : ENNReal) := by
          simp [allCoarse, Finset.sum_const, nsmul_eq_mul,
            Kakeya.Streamlined.BodyFamily.enncard]
          ring
    have hwithReference :
        (coarseContained.card : ENNReal) *
            (referenceFiber.card : ENNReal) ≤
          ((K * C) * volume convexSet * coarse.enncard) *
            (referenceFiber.card : ENNReal) := by
      calc
        (coarseContained.card : ENNReal) *
              (referenceFiber.card : ENNReal) ≤
            (fineContained.card : ENNReal) :=
          hcoarseToFine
        _ ≤ C * volume convexSet * fine.enncard :=
          hfineBound
        _ ≤ C * volume convexSet *
            (K * coarse.enncard *
              (referenceFiber.card : ENNReal)) := by
          gcongr
        _ =
            ((K * C) * volume convexSet * coarse.enncard) *
              (referenceFiber.card : ENNReal) := by
          ring
    have hcoarseBound :
        (coarseContained.card : ENNReal) ≤
          (K * C) * volume convexSet * coarse.enncard :=
      (ENNReal.mul_le_mul_iff_left
        hreferencePos.ne' hreferenceTop).mp hwithReference
    simpa [coarseContained,
      Kakeya.Streamlined.BodyFamily.containedCount] using
        hcoarseBound

end Kakeya.Assouad

end
