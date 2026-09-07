import MyLeanRepo.Kakeya.Assouad.PureWZ2.ParentLevelWholeFiberSelection
import MyLeanRepo.Kakeya.Assouad.TubeVolumeScaling

/-!
# Aggregate density on one complete actual fiber

A literal Definition 2.12 cover partitions both indexed cardinality and shaded
mass by its complete strict fibers.  Therefore aggregate source density is
attained on at least one complete fiber.  This is the source-local frontend for
normalization that avoids any global spatial-cell count.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/--
Select one actual parent whose complete strict fiber has at least the ambient
average shaded mass per source tube.
-/
theorem pureWZ2_exists_completeFiber_density_parent
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPurePartitioningCover fine coarse)
    (rhoNonnegative : 0 ≤ rho)
    (fineNonempty : fine.Nonempty)
    (shading : Kakeya.Streamlined.TubeShading fine)
    (density : ENNReal)
    (sourceDense :
      density * fine.toBodyFamily.mass ≤ shading.mass) :
    ∃ parent : Fin coarse.card,
      density *
          ((wz2PaperPureFullFiberSubfamily
            fine coarse parent).family.toBodyFamily.mass) ≤
        ((wz2PaperPureFullFiberSubfamily
          fine coarse parent).restrictShading
          shading).mass := by
  let source : Fin fine.card := ⟨0, fineNonempty⟩
  let occupied := cover.parent source
  letI : Nonempty (Fin coarse.card) := ⟨occupied⟩
  have fiberMass :
      ∀ parent : Fin coarse.card,
        (wz2PaperPureFullFiberSubfamily
          fine coarse parent).family.toBodyFamily.mass =
          wz2PaperOrdinaryFullFiberCount fine coarse parent *
            Kakeya.deltaTubeVolume delta := by
    intro parent
    rw [tubeFamily_mass_eq_nominal]
    change
      ((wz2PaperOrdinaryFullFiberIndices
        fine coarse parent).card : ENNReal) *
          Kakeya.deltaTubeVolume delta =
        wz2PaperOrdinaryFullFiberCount fine coarse parent *
          Kakeya.deltaTubeVolume delta
    rfl
  have countSum :
      (∑ parent : Fin coarse.card,
          wz2PaperOrdinaryFullFiberCount fine coarse parent) =
        fine.enncard := by
    have fiberEq :
        ∀ parent : Fin coarse.card,
          wz2PaperOrdinaryFullFiberIndices fine coarse parent =
            Finset.univ.filter fun source =>
              cover.parent source = parent := by
      intro parent
      ext source
      rw [cover.mem_fullFiber_iff_parent_eq rhoNonnegative]
      simp
    change
      (∑ parent : Fin coarse.card,
        ((wz2PaperOrdinaryFullFiberIndices
          fine coarse parent).card : ENNReal)) =
        (fine.card : ENNReal)
    simp_rw [fiberEq]
    rw [← Nat.cast_sum]
    exact_mod_cast
      ((Finset.sum_card_fiberwise_eq_card_filter
        (Finset.univ : Finset (Fin fine.card))
        (Finset.univ : Finset (Fin coarse.card))
        cover.parent).trans (by simp))
  have familyMassSum :
      (∑ parent : Fin coarse.card,
          (wz2PaperPureFullFiberSubfamily
            fine coarse parent).family.toBodyFamily.mass) =
        fine.toBodyFamily.mass := by
    simp_rw [fiberMass]
    rw [← Finset.sum_mul, countSum]
    rw [tubeFamily_mass_eq_nominal]
    rfl
  have shadingMassSum :
      (∑ parent : Fin coarse.card,
          ((wz2PaperPureFullFiberSubfamily
            fine coarse parent).restrictShading shading).mass) =
        shading.mass := by
    have fiberMassEq :
        ∀ parent : Fin coarse.card,
          ((wz2PaperPureFullFiberSubfamily
            fine coarse parent).restrictShading shading).mass =
            ∑ source ∈
              wz2PaperOrdinaryFullFiberIndices fine coarse parent,
                volume (shading.carrier source) := by
      intro parent
      let fiber :=
        wz2PaperOrdinaryFullFiberIndices fine coarse parent
      let equivalence : Fin fiber.card ≃ fiber :=
        fiber.orderIsoOfFin rfl |>.toEquiv
      change
        (∑ index : Fin fiber.card,
          volume
            (shading.carrier
              (fiber.orderEmbOfFin rfl index))) =
          ∑ source ∈ fiber, volume (shading.carrier source)
      calc
        (∑ index : Fin fiber.card,
            volume
              (shading.carrier
                (fiber.orderEmbOfFin rfl index))) =
            ∑ source : fiber,
              volume (shading.carrier source.1) := by
          exact
            Fintype.sum_equiv equivalence
              (fun index : Fin fiber.card =>
                volume
                  (shading.carrier
                    (fiber.orderEmbOfFin rfl index)))
              (fun source : fiber =>
                volume (shading.carrier source.1))
              (fun _ => rfl)
        _ =
            ∑ source ∈ fiber,
              volume (shading.carrier source) :=
          Finset.sum_coe_sort fiber
            (fun source => volume (shading.carrier source))
    simp_rw [fiberMassEq]
    have fiberEq :
        ∀ parent : Fin coarse.card,
          wz2PaperOrdinaryFullFiberIndices fine coarse parent =
            Finset.univ.filter fun source =>
              cover.parent source = parent := by
      intro parent
      ext source
      rw [cover.mem_fullFiber_iff_parent_eq rhoNonnegative]
      simp
    simp_rw [fiberEq]
    exact
      Finset.sum_fiberwise_of_maps_to
        (s := Finset.univ)
        (t := Finset.univ)
        (g := cover.parent)
        (fun _ _ => Finset.mem_univ _)
        (fun source => volume (shading.carrier source))
  by_contra noParent
  push Not at noParent
  have pointwise :
      ∀ parent : Fin coarse.card,
        ((wz2PaperPureFullFiberSubfamily
          fine coarse parent).restrictShading shading).mass <
            density *
              (wz2PaperPureFullFiberSubfamily
                fine coarse parent).family.toBodyFamily.mass := by
    intro parent
    exact noParent parent
  have strictSum :
      (∑ parent : Fin coarse.card,
          ((wz2PaperPureFullFiberSubfamily
            fine coarse parent).restrictShading shading).mass) <
        ∑ parent : Fin coarse.card,
          density *
            (wz2PaperPureFullFiberSubfamily
              fine coarse parent).family.toBodyFamily.mass :=
    ENNReal.sum_lt_sum_of_nonempty
      (Finset.univ_nonempty :
        (Finset.univ : Finset (Fin coarse.card)).Nonempty)
      (fun parent _ => pointwise parent)
  rw [shadingMassSum, ← Finset.mul_sum, familyMassSum] at strictSum
  exact (not_lt_of_ge sourceDense) strictSum

end Kakeya.Assouad

end
