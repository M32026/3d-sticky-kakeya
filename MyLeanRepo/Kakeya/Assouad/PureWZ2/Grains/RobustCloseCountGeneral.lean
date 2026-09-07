import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.RobustCloseCountPhase1
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.RobustCloseCountPhase2
import MyLeanRepo.Kakeya.Assouad.WZ1.CrossPerturbation
import MyLeanRepo.Kakeya.Assouad.WZ1.RobustCloseCountFromBalanced

/-!
# Generalized robust close count for arbitrary threshold

Adapts `pureWz2_robust_close_count` from threshold `L` to an arbitrary
threshold `kappa`. The coarse threshold becomes `kappa + L` (from the
cross perturbation bound `wz1Cross_projective_upper` with alignment error L/2).
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set Finset

attribute [local instance] Classical.propDecidable

/-- Generalized robust close direction count for PureWZ2 at arbitrary threshold.

Given a cover with direction alignment and a fiber-capped restricted shading,
the fine close direction count at threshold `kappa` is bounded by
coarse close count (at threshold `kappa + L`) × fiber cap.
-/
lemma pureWz2_robust_close_count_general
    {delta' L : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta'}
    {coarse : Kakeya.Streamlined.TubeFamily L}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading restricted : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (hsub : PaperIsSubshading restricted fineShading)
    -- Direction alignment from Phase 1
    (halign : ∀ i : Fin fine.card,
      ∃ (s : ℝ), (s = 1 ∨ s = -1) ∧
        ‖(coarse.tube (selectParent cover i)).direction -
            s • (fine.tube i).direction‖ ≤ L / 2)
    -- Point compatibility
    (hpoint : ∀ i parent,
      WZ1PaperTubeCovers (fine.tube i) (coarse.tube parent) →
      ∀ p, p ∈ fineShading.carrier i → p ∈ coarseShading.carrier parent)
    -- Threshold
    (kappa : ℝ)
    -- Fiber cap on restricted shading
    (fiberCap : ENNReal)
    (hfiber : ∀ (parent : Fin coarse.card) (p : Point3),
      (fiberPointMultiplicity cover restricted parent p : ENNReal) ≤ fiberCap)
    -- Coarse close direction count bound at threshold kappa + L
    (coarseCount : ENNReal)
    (hcoarse : ∀ (p : Point3), p ∈ coarseShading.union →
      ∀ (j : Fin coarse.card), p ∈ coarseShading.carrier j →
        (paperCloseDirectionCount coarseShading p j (kappa + L) : ENNReal) ≤ coarseCount)
    -- Parameters
    (hL_pos : 0 < L)
    (hkappa_pos : 0 < kappa)
    (p : Point3)
    (i : Fin fine.card)
    (hp : p ∈ restricted.carrier i) :
    (paperCloseDirectionCount restricted p i kappa : ENNReal) ≤ coarseCount * fiberCap := by
  let parentI := selectParent cover i
  let closeFine : Finset (Fin fine.card) :=
    Finset.univ.filter fun j =>
      p ∈ restricted.carrier j ∧
        ‖wz1Cross (fine.tube i).direction (fine.tube j).direction‖ < kappa
  let parentSet : Finset (Fin coarse.card) :=
    closeFine.image (selectParent cover)
  -- Point p is in coarse carrier of parentI
  have hcoarsePoint : p ∈ coarseShading.carrier parentI := by
    have hcovers : WZ1PaperTubeCovers (fine.tube i) (coarse.tube parentI) :=
      selectedParent_covers cover i
    have hfinePoint : p ∈ fineShading.carrier i := hsub i hp
    exact hpoint i parentI hcovers p hfinePoint
  -- Each parent in parentSet is close in cross product to parentI
  have hparentClose : ∀ q ∈ parentSet,
      ‖wz1Cross (coarse.tube parentI).direction (coarse.tube q).direction‖ < kappa + L := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨j, hj, rfl⟩
    rcases Finset.mem_filter.mp hj with ⟨_, hjp, hjcross⟩
    rcases halign i with ⟨si, hsi, hali⟩
    rcases halign j with ⟨sj, hsj, halj⟩
    have hali' : ‖(coarse.tube parentI).direction - si • (fine.tube i).direction‖ ≤ 4 * (L / 8) := by
      have h : L / 2 = 4 * (L / 8) := by ring
      rw [h] at hali
      exact hali
    have halj' : ‖(coarse.tube (selectParent cover j)).direction - sj • (fine.tube j).direction‖ ≤ 4 * (L / 8) := by
      have h : L / 2 = 4 * (L / 8) := by ring
      rw [h] at halj
      exact halj
    have h := wz1Cross_projective_upper
      (fine.tube i).direction (fine.tube j).direction
      (coarse.tube parentI).direction
      (coarse.tube (selectParent cover j)).direction
      (fine.tube i).direction_unit (fine.tube j).direction_unit
      (coarse.tube parentI).direction_unit
      si sj hsi hsj hali' halj' hjcross
    have hfinal : ‖wz1Cross (coarse.tube parentI).direction (coarse.tube (selectParent cover j)).direction‖ < kappa + L := by
      have h8 : kappa + 8 * (L / 8) = kappa + L := by ring
      rw [h8] at h
      exact h
    exact hfinal
  -- Each parent in parentSet contains p
  have hparentPoint : ∀ q ∈ parentSet, p ∈ coarseShading.carrier q := by
    intro q hq
    rcases Finset.mem_image.mp hq with ⟨j, hj, rfl⟩
    rcases Finset.mem_filter.mp hj with ⟨_, hjp, _⟩
    have hcovers : WZ1PaperTubeCovers (fine.tube j) (coarse.tube (selectParent cover j)) :=
      selectedParent_covers cover j
    have hfinePoint : p ∈ fineShading.carrier j := hsub j hjp
    exact hpoint j (selectParent cover j) hcovers p hfinePoint
  -- parentSet is subset of coarse close set at threshold kappa + L
  let coarseClose : Finset (Fin coarse.card) :=
    Finset.univ.filter fun q =>
      p ∈ coarseShading.carrier q ∧
        ‖wz1Cross (coarse.tube parentI).direction (coarse.tube q).direction‖ < kappa + L
  have hparentSubset : parentSet ⊆ coarseClose := by
    intro q hq
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hparentPoint q hq, hparentClose q hq⟩
  -- Bound parentSet.card by coarseCount
  have hcoarseCard : (coarseClose.card : ENNReal) ≤ coarseCount := by
    have hpunion : p ∈ coarseShading.union := ⟨parentI, hcoarsePoint⟩
    exact hcoarse p hpunion parentI hcoarsePoint
  have h1 : parentSet.card ≤ coarseClose.card := Finset.card_le_card hparentSubset
  have h2 : (parentSet.card : ENNReal) ≤ (coarseClose.card : ENNReal) := by exact_mod_cast h1
  have hparentCard : (parentSet.card : ENNReal) ≤ coarseCount := le_trans h2 hcoarseCard
  -- Each fiber contribution ≤ fiberCap
  have hfiberBound : ∀ q ∈ parentSet,
      ((closeFine.filter fun j => selectParent cover j = q).card : ENNReal) ≤ fiberCap := by
    intro q _
    have hsub2 :
        (closeFine.filter fun j => selectParent cover j = q) ⊆
        (Finset.univ.filter fun j => selectParent cover j = q ∧ p ∈ restricted.carrier j) := by
      intro j hj
      rcases Finset.mem_filter.mp hj with ⟨hclose, hparent⟩
      rcases Finset.mem_filter.mp hclose with ⟨_, hjp, _⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hparent, hjp⟩⟩
    have hcard : ((closeFine.filter fun j => selectParent cover j = q).card : ENNReal) ≤
        (fiberPointMultiplicity cover restricted q p : ENNReal) := by
      exact_mod_cast Finset.card_le_card hsub2
    exact hcard.trans (hfiber q p)
  -- Sum over parents
  have hmaps : Set.MapsTo (selectParent cover)
      (closeFine : Set (Fin fine.card))
      (parentSet : Set (Fin coarse.card)) := by
    intro j hj
    exact Finset.mem_image.mpr ⟨j, hj, rfl⟩
  have hcloseSum : (closeFine.card : ENNReal) =
      ∑ q ∈ parentSet, ((closeFine.filter fun j => selectParent cover j = q).card : ENNReal) := by
    have hnat := Finset.card_eq_sum_card_fiberwise hmaps
    rw [hnat]
    <;> norm_cast
  have hcloseFine_eq : paperCloseDirectionCount restricted p i kappa = closeFine.card := by
    rfl
  rw [hcloseFine_eq, hcloseSum]
  calc
    (∑ q ∈ parentSet, ((closeFine.filter fun j => selectParent cover j = q).card : ENNReal))
      ≤ ∑ q ∈ parentSet, fiberCap := by
        apply Finset.sum_le_sum
        intro q hq
        exact hfiberBound q hq
    _ = (parentSet.card : ENNReal) * fiberCap := by
      rw [Finset.sum_const, mul_comm] <;> ring
    _ ≤ coarseCount * fiberCap := by
      gcongr

end Kakeya.Assouad.PureWZ2

end
