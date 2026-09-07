import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.SelectedScaleStatements

/-!
WZ2 Section 7: convert weighted shaded-mass retention into indexed
cardinality retention for the same selected tube subfamily.

Proof route:
1. From `TubeVolumeScalingStatement`, all radius-`rho` tubes have the same
   positive finite volume `V = deltaTubeVolume rho`.
2. Both the ambient family `F` and the selected subfamily `S` have nominal
   mass equal to `enncard * V`.
3. Each shaded carrier is contained in its tube, so the selected shading mass
   is at most the selected family mass.
4. Chain the density hypothesis `lambda * F.mass ≤ Y.mass` with the mass
   retention `Y.mass ≤ L * selectedShading.mass` to get
   `lambda * F.mass ≤ L * S.mass`.
5. Substitute the nominal mass formulas and cancel `V` (positive, finite)
   to obtain `lambda * F.enncard ≤ L * S.enncard`.
6. Multiply by `L⁻¹` and use `L⁻¹ * L = 1` (valid since `L ≠ 0, ⊤`) to
   conclude `(L⁻¹ * lambda) * F.enncard ≤ S.enncard`.
-/

namespace Kakeya.Assouad

theorem selected_tube_cardinality_retention_from_mass :
    SelectedTubeCardinalityRetentionFromMassStatement := by
  intro hTV rho hrho hrho1 F Y selected lambda L hdense hmass hL0 hLtop
  let V := Kakeya.deltaTubeVolume rho
  have hV_eq : ∀ (T : Kakeya.DeltaTube rho), T.volume = V := hTV.1 rho
  have hV_pos : 0 < V := (hTV.2.1 rho hrho hrho1).1
  have hV_ne_zero : V ≠ 0 := hV_pos.ne'
  have hV_ne_top : V ≠ ⊤ := (hTV.2.1 rho hrho hrho1).2

  let S := selectedTubeFamily F selected
  let Z := selectedTubeShading Y selected

  have hF_mass : F.toBodyFamily.mass = F.enncard * V := by
    have h : ∀ i : Fin F.card, (F.toBodyFamily.body i).volume = V := by
      intro i
      exact hV_eq (F.tube i)
    calc
      F.toBodyFamily.mass
        = ∑ i : Fin F.card, (F.toBodyFamily.body i).volume := by rfl
      _ = ∑ i : Fin F.card, V := by
        apply Finset.sum_congr rfl
        intro i _
        exact h i
      _ = F.enncard * V := by
        simp [Finset.sum_const]
        rfl

  have hS_mass : S.toBodyFamily.mass = S.enncard * V := by
    have h : ∀ i : Fin S.card, (S.toBodyFamily.body i).volume = V := by
      intro i
      exact hV_eq (S.tube i)
    calc
      S.toBodyFamily.mass
        = ∑ i : Fin S.card, (S.toBodyFamily.body i).volume := by rfl
      _ = ∑ i : Fin S.card, V := by
        apply Finset.sum_congr rfl
        intro i _
        exact h i
      _ = S.enncard * V := by
        simp [Finset.sum_const]
        rfl

  have hZ_mass_le : Z.mass ≤ S.toBodyFamily.mass := by
    rw [selectedTubeShading_mass Y selected, selectedTubeFamily_mass F selected]
    apply Finset.sum_le_sum
    intro i _
    exact MeasureTheory.measure_mono (Y.subset_body i)

  have h3 : lambda * F.toBodyFamily.mass ≤ L * S.toBodyFamily.mass := by
    calc
      lambda * F.toBodyFamily.mass ≤ Y.mass := hdense
      _ ≤ L * Z.mass := hmass
      _ ≤ L * S.toBodyFamily.mass := by gcongr

  rw [hF_mass, hS_mass] at h3

  have h4 : (lambda * F.enncard) * V ≤ (L * S.enncard) * V := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using h3
  have h5 : lambda * F.enncard ≤ L * S.enncard := by
    rw [ENNReal.mul_le_mul_iff_left hV_ne_zero hV_ne_top] at h4
    exact h4

  have h6 : L⁻¹ * (lambda * F.enncard) ≤ L⁻¹ * (L * S.enncard) := by gcongr
  have h7 : L⁻¹ * (L * S.enncard) = S.enncard :=
    ENNReal.inv_mul_cancel_left hL0 hLtop
  rw [h7] at h6
  simpa [mul_assoc] using h6

end Kakeya.Assouad
