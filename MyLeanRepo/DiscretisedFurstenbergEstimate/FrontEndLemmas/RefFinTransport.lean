module

/-
  Ref_fin transport helper for FrontEndComposition.

  Packages swap-aware transport of S-set, separation, card, and Ncover lower
  from Pbar to Ref_fin in a single lemma, saving ~30 lines of split_ifs.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CoordinatePartition
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.B1ToA1Skeleton
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DirecretisedFurstenbergEstimate.FrontEndLemmas.B1Assembly

open DirecretisedFurstenbergEstimate
open CoordinatePartition
open DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral

attribute [local instance] Classical.propDecidable

/-- Swap-aware transport of all Pbar properties to Ref_fin.

    `Ref_fin` is `Pbar.image swapCoords` when `swapped`, else `Pbar`.
    Returns S-set, separation, card equality, and Ncover lower bound. -/
lemma transport_Ref_fin
    {δ_n u C_Pbar C : ℝ}
    (Pbar : Finset EuclideanPlane)
    (swapped : Bool)
    (hPbar_sset : IsDeltaSSet δ_n u C_Pbar (Pbar : Set EuclideanPlane))
    (hPbar_sep : Set.Pairwise (Pbar : Set EuclideanPlane) (fun p q => δ_n ≤ dist p q))
    (hPbar_ncover_lower : Metric.externalCoveringNumber δ_n.toNNReal (Pbar : Set EuclideanPlane) ≥
        ENNReal.ofReal ((1 / 10000 : ℝ) * C⁻¹ * Real.rpow δ_n (-u))) :
    let Ref_fin : Finset EuclideanPlane :=
      if swapped then Pbar.image swapCoords else Pbar
    IsDeltaSSet δ_n u C_Pbar (Ref_fin : Set EuclideanPlane) ∧
    Set.Pairwise (Ref_fin : Set EuclideanPlane) (fun p q => δ_n ≤ dist p q) ∧
    Ref_fin.card = Pbar.card ∧
    Metric.externalCoveringNumber δ_n.toNNReal (Ref_fin : Set EuclideanPlane) ≥
      ENNReal.ofReal ((1 / 10000 : ℝ) * C⁻¹ * Real.rpow δ_n (-u)) := by
  let Ref_fin : Finset EuclideanPlane :=
    if swapped then Pbar.image swapCoords else Pbar
  have h_card : Ref_fin.card = Pbar.card := by
    unfold Ref_fin
    split_ifs with h
    · exact Finset.card_image_of_injective _ swapCoords_invol.injective
    · rfl
  have h_sset : IsDeltaSSet δ_n u C_Pbar (Ref_fin : Set EuclideanPlane) := by
    unfold Ref_fin
    split_ifs with h
    · have h_img : (↑(Pbar.image swapCoords) : Set EuclideanPlane) =
          swapCoords '' (↑Pbar : Set EuclideanPlane) := by simp
      rw [h_img]
      exact IsDeltaSSet.swapCoords_image hPbar_sset
    · exact hPbar_sset
  have h_sep : Set.Pairwise (Ref_fin : Set EuclideanPlane) (fun p q => δ_n ≤ dist p q) := by
    unfold Ref_fin
    split_ifs with h
    · intro p hp q hq hne
      rcases Finset.mem_image.mp hp with ⟨p', hp', rfl⟩
      rcases Finset.mem_image.mp hq with ⟨q', hq', rfl⟩
      have hne' : p' ≠ q' := by
        intro h; rw [h] at hne; exact hne rfl
      have h : δ_n ≤ dist p' q' := hPbar_sep hp' hq' hne'
      have h_iso : dist (swapCoords p') (swapCoords q') = dist p' q' :=
        swapCoords_isometry.dist_eq p' q'
      rw [h_iso]; exact h
    · exact hPbar_sep
  have h_ncover : Metric.externalCoveringNumber δ_n.toNNReal (Ref_fin : Set EuclideanPlane) ≥
      ENNReal.ofReal ((1 / 10000 : ℝ) * C⁻¹ * Real.rpow δ_n (-u)) := by
    unfold Ref_fin
    split_ifs with h
    · have h_eq : Metric.externalCoveringNumber δ_n.toNNReal
          ((Pbar.image swapCoords : Set EuclideanPlane)) =
          Metric.externalCoveringNumber δ_n.toNNReal (Pbar : Set EuclideanPlane) := by
        simpa using externalCoveringNumber_image_of_involutive_isometry
          swapCoords_isometry swapCoords_invol δ_n.toNNReal (Pbar : Set EuclideanPlane)
      rw [h_eq]; exact hPbar_ncover_lower
    · exact hPbar_ncover_lower
  exact ⟨h_sset, h_sep, h_card, h_ncover⟩

end DirecretisedFurstenbergEstimate.FrontEndLemmas.B1Assembly

end
