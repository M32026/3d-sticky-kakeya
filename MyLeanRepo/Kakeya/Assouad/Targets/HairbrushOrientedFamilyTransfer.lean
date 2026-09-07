import MyLeanRepo.Kakeya.Assouad.Subunit.HairbrushSelfContainedLeaves
import MyLeanRepo.Kakeya.Assouad.Hairbrush.RawBTransferLemmas

/-!
# Structural transfer through tube orientation

Carrier-preserving orientation transports nonemptiness, cardinality,
essential distinctness, and the Katz--Tao convex Wolff bound to the oriented
image of an arbitrary supplied subfamily.
-/

open MeasureTheory Metric Set Finset Real
open scoped Classical

namespace Kakeya.Assouad

theorem hairbrush_oriented_family_transfer :
    HairbrushOrientedFamilyTransferStatement := by
  intro δ katzTaoConstant hδ hδ1 F source h_ed h_sub h_nonempty hKT stem
  set oriented : Kakeya.TubeFamily δ := source.image (orientTube stem) with horiented
  have h_inj : Set.InjOn (orientTube stem) source :=
    orientTube_injOn hδ hδ1 h_ed h_sub stem
  have h_nonempty' : oriented.Nonempty := by
    rcases h_nonempty with ⟨U, hU⟩
    refine ⟨orientTube stem U, ?_⟩
    exact Finset.mem_image.mpr ⟨U, hU, rfl⟩
  have h_card : oriented.card = source.card :=
    Finset.card_image_of_injOn h_inj
  have h_enncard : oriented.enncard = source.enncard := by
    simp [Kakeya.TubeFamily.enncard, h_card]
  have h_ed' : oriented.IsEssentiallyDistinct := by
    intro U' hU' V' hV' hne
    rcases Finset.mem_image.mp hU' with ⟨U, hU, rfl⟩
    rcases Finset.mem_image.mp hV' with ⟨V, hV, rfl⟩
    have h_U_ne_V : U ≠ V := by
      intro h
      have h_contra : orientTube stem U = orientTube stem V := by rw [h]
      exact hne h_contra
    have h_ed_uv : U.EssentiallyDistinct V :=
      h_ed (h_sub hU) (h_sub hV) h_U_ne_V
    have hcarU : (orientTube stem U).carrier = U.carrier := orientTube_carrier stem U
    have hcarV : (orientTube stem V).carrier = V.carrier := orientTube_carrier stem V
    have hvolU : (orientTube stem U).volume = U.volume := orientTube_volume stem U
    have hvolV : (orientTube stem V).volume = V.volume := orientTube_volume stem V
    have h_inter : volume ((orientTube stem U).carrier ∩ (orientTube stem V).carrier) =
        volume (U.carrier ∩ V.carrier) := by
      rw [hcarU, hcarV]
    have h_max : max (orientTube stem U).volume (orientTube stem V).volume =
        max U.volume V.volume := by
      rw [hvolU, hvolV]
    dsimp only [Kakeya.DeltaTube.EssentiallyDistinct] at h_ed_uv ⊢
    rw [h_inter, h_max]
    exact h_ed_uv
  have hKT_source : Kakeya.KatzTaoConvexWolffBound source katzTaoConstant :=
    rawB_KT_subset hKT h_sub
  have hKT' : Kakeya.KatzTaoConvexWolffBound oriented katzTaoConstant := by
    intro W hW
    have h_S_eq : (oriented.filter fun U' => U'.carrier ⊆ W) =
        (source.filter fun U => U.carrier ⊆ W).image (orientTube stem) := by
      ext U'
      simp only [Finset.mem_filter, Finset.mem_image, horiented]
      constructor
      · rintro ⟨⟨U, hU, rfl⟩, h2⟩
        have h3 : U.carrier ⊆ W := by
          have h4 : (orientTube stem U).carrier = U.carrier := orientTube_carrier stem U
          rw [←h4] <;> exact h2
        exact ⟨U, ⟨hU, h3⟩, rfl⟩
      · rintro ⟨U, ⟨hU, h2⟩, rfl⟩
        have h3 : (orientTube stem U).carrier ⊆ W := by
          have h4 : (orientTube stem U).carrier = U.carrier := orientTube_carrier stem U
          rw [h4] <;> exact h2
        exact ⟨⟨U, hU, rfl⟩, h3⟩
    have h_Ssource_sub : (source.filter fun U => U.carrier ⊆ W) ⊆ source := by
      intro U hU
      exact (Finset.mem_filter.mp hU).1
    have h_card_eq : (oriented.filter fun U' => U'.carrier ⊆ W).card =
        (source.filter fun U => U.carrier ⊆ W).card := by
      rw [h_S_eq]
      exact Finset.card_image_of_injOn (h_inj.mono h_Ssource_sub)
    have h_main : oriented.containedCount W = source.containedCount W := by
      dsimp only [Kakeya.TubeFamily.containedCount]
      exact_mod_cast h_card_eq
    rw [h_main]
    exact hKT_source W hW
  dsimp only [HairbrushOrientedFamilyTransferStatement] at *
  <;> simp only [horiented] at *
  <;> exact ⟨h_nonempty', h_enncard, h_ed', hKT'⟩

end Kakeya.Assouad
