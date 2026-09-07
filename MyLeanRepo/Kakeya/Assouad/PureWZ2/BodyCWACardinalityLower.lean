import MyLeanRepo.Kakeya.Assouad.PureWZ2.CenteredFullFiberCWA
import MyLeanRepo.Kakeya.Assouad.TubeVolumeScaling

/-!
# Cardinality lower bound from public body Convex-Wolff counting

Applying the count bound to the carrier of one member of a nonempty
equal-radius family gives the sharp elementary lower bound
`C⁻¹ * deltaTubeVolume delta⁻¹ ≤ family.enncard`.
-/

noncomputable section

namespace Kakeya.Assouad

/-- One member of a nonempty body-CWA tube family forces a cardinality
lower bound. -/
theorem pure_wz2_body_cwa_cardinality_lower
    {delta : ℝ}
    (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1)
    {family : Kakeya.Streamlined.TubeFamily delta}
    (hfamilyNonempty : family.Nonempty)
    {C : ENNReal}
    (hCzero : C ≠ 0)
    (hCtop : C ≠ ⊤)
    (hCWA :
      WZ2PaperBodyConvexWolffBound
        family.toBodyFamily C) :
    C⁻¹ * (Kakeya.deltaTubeVolume delta)⁻¹ ≤
      family.enncard := by
  let index : Fin family.card := ⟨0, hfamilyNonempty⟩
  let carrier := (family.tube index).carrier
  have hconvex : Convex ℝ carrier :=
    wz2_paper_ordinary_tube_carrier_convex _
  have hmember :
      index ∈ family.toBodyFamily.containedIndices carrier := by
    exact
      Kakeya.Streamlined.BodyFamily.mem_containedIndices_iff.mpr
        (Set.Subset.rfl)
  have hcount :
      (1 : ENNReal) ≤
        family.toBodyFamily.containedCount carrier := by
    change
      (1 : ENNReal) ≤
        ((family.toBodyFamily.containedIndices carrier).card :
          ENNReal)
    exact_mod_cast
      (Finset.one_le_card.mpr ⟨index, hmember⟩)
  have hvolume :
      MeasureTheory.volume carrier =
        Kakeya.deltaTubeVolume delta := by
    exact tube_volume_scaling.1 delta (family.tube index)
  have hmain :
      (1 : ENNReal) ≤
        C * Kakeya.deltaTubeVolume delta *
          family.enncard := by
    exact hcount.trans (by
      simpa [carrier, hvolume,
        Kakeya.Streamlined.BodyFamily.enncard,
        Kakeya.Streamlined.TubeFamily.enncard,
        Kakeya.Streamlined.TubeFamily.toBodyFamily] using
        hCWA carrier hconvex)
  have htubeZero :
      Kakeya.deltaTubeVolume delta ≠ 0 :=
    (tube_volume_scaling.2.1 delta
      hdelta hdeltaOne).1.ne'
  have htubeTop :
      Kakeya.deltaTubeVolume delta ≠ ⊤ :=
    (tube_volume_scaling.2.1 delta
      hdelta hdeltaOne).2
  let coefficient :=
    C * Kakeya.deltaTubeVolume delta
  have hcoefficientZero : coefficient ≠ 0 :=
    mul_ne_zero hCzero htubeZero
  have hcoefficientTop : coefficient ≠ ⊤ :=
    ENNReal.mul_ne_top hCtop htubeTop
  have hinverse :
      coefficient⁻¹ =
        C⁻¹ * (Kakeya.deltaTubeVolume delta)⁻¹ := by
    exact
      ENNReal.mul_inv
        (Or.inl hCzero) (Or.inl hCtop)
  have hmul :
      coefficient⁻¹ ≤ family.enncard := by
    have hscaled :=
      mul_le_mul_left' hmain coefficient⁻¹
    rw [show
      coefficient⁻¹ *
          (C * Kakeya.deltaTubeVolume delta *
            family.enncard) =
        (coefficient⁻¹ * coefficient) *
          family.enncard by
            simp [coefficient]
            ring] at hscaled
    rw [ENNReal.inv_mul_cancel
      hcoefficientZero hcoefficientTop, one_mul] at hscaled
    simpa using hscaled
  rw [hinverse] at hmul
  exact hmul

end Kakeya.Assouad

end
