import MyLeanRepo.Kakeya.Streamlined.TubeRefinement
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.DeterministicHelpers

/-!
# ENNReal tube-normalized shading weight

For an equal-radius tube family, normalize each shaded piece by the common
single-tube volume.  The weight lies in `[0,1]`, its total is exactly
`Y.mass / deltaTubeVolume`, and selection inequalities convert back to
literal restricted shading-mass inequalities without any finiteness
assumption on the selection loss.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Streamlined

/-- Shaded fraction of one indexed tube. -/
def tubeNormalizedShadingWeight
    {delta : ℝ} {F : TubeFamily delta}
    (Y : TubeShading F) (i : Fin F.card) : ENNReal :=
  volume (Y.carrier i) / Kakeya.deltaTubeVolume delta

lemma tubeNormalizedShadingWeight_le_one
    {delta : ℝ} (hdelta : 0 < delta)
    {F : TubeFamily delta} (Y : TubeShading F)
    (i : Fin F.card) :
    tubeNormalizedShadingWeight Y i ≤ 1 := by
  have hVzero :
      Kakeya.deltaTubeVolume delta ≠ 0 :=
    (RandomTranslation.deltaTubeVolume_pos hdelta).ne'
  have hVtop :
      Kakeya.deltaTubeVolume delta ≠ ⊤ :=
    RandomTranslation.deltaTubeVolume_ne_top
  apply
    (ENNReal.div_le_iff_le_mul
      (Or.inl hVzero) (Or.inl hVtop)).2
  calc
    volume (Y.carrier i) ≤
        volume ((F.tube i).carrier) :=
      measure_mono (Y.subset_body i)
    _ = Kakeya.deltaTubeVolume delta :=
      RandomTranslation.tube_volume_eq_deltaTubeVolume
        (F.tube i)
    _ = 1 * Kakeya.deltaTubeVolume delta := by simp

lemma sum_tubeNormalizedShadingWeight
    {delta : ℝ} (hdelta : 0 < delta)
    {F : TubeFamily delta} (Y : TubeShading F) :
    (∑ i : Fin F.card, tubeNormalizedShadingWeight Y i) =
      Y.mass / Kakeya.deltaTubeVolume delta := by
  change
    (∑ i : Fin F.card,
      volume (Y.carrier i) /
        Kakeya.deltaTubeVolume delta) =
      (∑ i : Fin F.card, volume (Y.carrier i)) /
        Kakeya.deltaTubeVolume delta
  calc
    (∑ i : Fin F.card,
        volume (Y.carrier i) /
          Kakeya.deltaTubeVolume delta) =
        ∑ i : Fin F.card,
          volume (Y.carrier i) *
            (Kakeya.deltaTubeVolume delta)⁻¹ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [div_eq_mul_inv]
    _ =
        (∑ i : Fin F.card, volume (Y.carrier i)) *
          (Kakeya.deltaTubeVolume delta)⁻¹ :=
      (Finset.sum_mul _ _ _).symm
    _ =
        (∑ i : Fin F.card, volume (Y.carrier i)) /
          Kakeya.deltaTubeVolume delta := by
      rw [div_eq_mul_inv]

lemma selected_tubeNormalizedShadingWeight
    {delta : ℝ} (hdelta : 0 < delta)
    {F : TubeFamily delta} (Y : TubeShading F)
    (S : TubeSubfamily F) :
    (∑ i : Fin S.family.card,
        tubeNormalizedShadingWeight Y (S.embedding i)) =
      (S.restrictShading Y).mass /
        Kakeya.deltaTubeVolume delta := by
  change
    (∑ i : Fin S.family.card,
      volume (Y.carrier (S.embedding i)) /
        Kakeya.deltaTubeVolume delta) =
      (∑ i : Fin S.family.card,
        volume (Y.carrier (S.embedding i))) /
          Kakeya.deltaTubeVolume delta
  calc
    (∑ i : Fin S.family.card,
        volume (Y.carrier (S.embedding i)) /
          Kakeya.deltaTubeVolume delta) =
        ∑ i : Fin S.family.card,
          volume (Y.carrier (S.embedding i)) *
            (Kakeya.deltaTubeVolume delta)⁻¹ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [div_eq_mul_inv]
    _ =
        (∑ i : Fin S.family.card,
          volume (Y.carrier (S.embedding i))) *
            (Kakeya.deltaTubeVolume delta)⁻¹ :=
      (Finset.sum_mul _ _ _).symm
    _ =
        (∑ i : Fin S.family.card,
          volume (Y.carrier (S.embedding i))) /
            Kakeya.deltaTubeVolume delta := by
      rw [div_eq_mul_inv]

/-- Reindex a selected ambient weight sum through the selected tube
subfamily. -/
lemma sum_selected_tubeNormalizedShadingWeight
    {delta : ℝ} {F : TubeFamily delta}
    (Y : TubeShading F)
    (selected : Finset (Fin F.card))
    (S : TubeSubfamily F)
    (himage :
      Finset.image S.embedding Finset.univ = selected) :
    (∑ i ∈ selected, tubeNormalizedShadingWeight Y i) =
      ∑ i : Fin S.family.card,
        tubeNormalizedShadingWeight Y (S.embedding i) := by
  rw [← himage]
  exact Finset.sum_image
    (fun i _ j _ h => S.embedding.inj' h)

/--
A normalized-weight retention inequality is exactly a restricted
shading-mass retention inequality after cancelling the common tube volume.
-/
lemma shadingMass_le_of_normalizedWeight
    {delta : ℝ} (hdelta : 0 < delta)
    {F : TubeFamily delta} (Y : TubeShading F)
    (S : TubeSubfamily F) (L : ENNReal)
    (hweight :
      (∑ i : Fin F.card,
          tubeNormalizedShadingWeight Y i) ≤
        L *
          ∑ i : Fin S.family.card,
            tubeNormalizedShadingWeight Y (S.embedding i)) :
    Y.mass ≤ L * (S.restrictShading Y).mass := by
  let V := Kakeya.deltaTubeVolume delta
  have hVzero : V ≠ 0 :=
    (RandomTranslation.deltaTubeVolume_pos hdelta).ne'
  have hVtop : V ≠ ⊤ :=
    RandomTranslation.deltaTubeVolume_ne_top
  rw [sum_tubeNormalizedShadingWeight hdelta Y,
    selected_tubeNormalizedShadingWeight hdelta Y S] at hweight
  have hmul :
      Y.mass / V * V ≤
        (L * ((S.restrictShading Y).mass / V)) * V := by
    gcongr
  rw [ENNReal.div_mul_cancel hVzero hVtop] at hmul
  calc
    Y.mass ≤
        (L * ((S.restrictShading Y).mass / V)) * V :=
      hmul
    _ = L * (((S.restrictShading Y).mass / V) * V) := by
      ring
    _ = L * (S.restrictShading Y).mass := by
      rw [ENNReal.div_mul_cancel hVzero hVtop]

end Kakeya.Streamlined

end
