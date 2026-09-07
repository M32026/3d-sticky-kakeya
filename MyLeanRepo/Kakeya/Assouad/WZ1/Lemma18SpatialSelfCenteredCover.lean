import MyLeanRepo.Kakeya.Assouad.WZ1.GridCovering

/-!
# Self-centered spatial cover for WZ1 Lemma 18

The fine-to-coarse pullback enlarges one `sqrt rho` ball to
`sqrt rho + 4*rho`.  Under `4*rho ≤ sqrt rho`, this lies in a ball of radius
`2*sqrt rho`.

Local interval estimates must be centered at actual retained shaded points.
This module covers any subset of a radius-`2R` ball by at most `8^3 = 512`
balls of radius `R`, centered at points of the subset itself.
-/

noncomputable section

open Metric Set

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/--
A subset of `B(center, 2R)` is covered by at most 512 radius-`R` balls whose
centers belong to the subset.
-/
lemma point3_subset_self_centered_sqrt_cover
    {source : Set Point3} {center : Point3} {radius : ℝ}
    (hradius : 0 < radius)
    (hsource : source ⊆ closedBall center (2 * radius)) :
    ∃ selected : Finset Point3,
      (selected : Set Point3) ⊆ source ∧
      selected.card ≤ 512 ∧
      source ⊆
        ⋃ selectedCenter ∈ selected,
          closedBall selectedCenter radius := by
  have hsqrtThree : Real.sqrt 3 ≤ 2 := by
    have hsqrtNonneg : 0 ≤ Real.sqrt 3 :=
      Real.sqrt_nonneg 3
    have hsquare : (Real.sqrt 3) ^ 2 = 3 :=
      Real.sq_sqrt (by norm_num)
    nlinarith
  have hdiameter :
      Real.sqrt 3 * (2 * (2 * radius) / 8) ≤ radius := by
    have hradiusNonneg : 0 ≤ radius := hradius.le
    calc
      Real.sqrt 3 * (2 * (2 * radius) / 8) =
          (Real.sqrt 3 / 2) * radius := by ring
      _ ≤ 1 * radius := by
        apply mul_le_mul_of_nonneg_right
        · linarith
        · exact hradiusNonneg
      _ = radius := by ring
  rcases
      grid_covering_cover
        center (2 * radius) radius
        (by positivity) 8 (by norm_num)
        hradius hdiameter with
    ⟨gridCell, hgridMeasurable, hgridCover,
      hgridDiameter⟩
  let occupied : Finset (Fin 3 → Fin 8) :=
    Finset.univ.filter fun index =>
      (source ∩ gridCell index).Nonempty
  let representative :
      (Fin 3 → Fin 8) → Point3 := fun index =>
    if hindex : index ∈ occupied then
      Classical.choose ((Finset.mem_filter.mp hindex).2)
    else 0
  let selected : Finset Point3 :=
    occupied.image representative
  have hrepresentative :
      ∀ index, index ∈ occupied →
        representative index ∈ source ∩ gridCell index := by
    intro index hindex
    dsimp only [representative]
    rw [dif_pos hindex]
    exact
      Classical.choose_spec
        ((Finset.mem_filter.mp hindex).2)
  have hselectedSource :
      (selected : Set Point3) ⊆ source := by
    intro point hpoint
    rcases Finset.mem_image.mp hpoint with
      ⟨index, hindex, rfl⟩
    exact (hrepresentative index hindex).1
  have hselectedCard :
      selected.card ≤ 512 := by
    calc
      selected.card ≤ occupied.card :=
        Finset.card_image_le
      _ ≤ (Finset.univ :
          Finset (Fin 3 → Fin 8)).card :=
        Finset.card_filter_le _ _
      _ = 512 := by
        simp [Fintype.card_pi, Fintype.card_fin]
  refine
    ⟨selected, hselectedSource, hselectedCard, ?_⟩
  intro point hpoint
  rcases hgridCover point (hsource hpoint) with
    ⟨index, hpointGrid⟩
  have hindexOccupied :
      index ∈ occupied := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ index,
        ⟨point, hpoint, hpointGrid⟩⟩
  have hrepresentativeGrid :=
    (hrepresentative index hindexOccupied).2
  have hdistance :
      dist point (representative index) ≤ radius :=
    hgridDiameter index point (representative index)
      hpointGrid hrepresentativeGrid
  have hrepresentativeSelected :
      representative index ∈ selected :=
    Finset.mem_image.mpr
      ⟨index, hindexOccupied, rfl⟩
  exact Set.mem_iUnion₂.mpr
    ⟨representative index, hrepresentativeSelected,
      Metric.mem_closedBall.mpr hdistance⟩

end Kakeya.Assouad
