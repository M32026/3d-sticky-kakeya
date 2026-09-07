import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedSelectedFineVolumeInputs

/-!
# Selected-layer fine volume inside one ambient bin
-/

open MeasureTheory

namespace Kakeya.Cinematic

theorem ambient_restricted_selected_fine_volume_of_layer_mass
    {ι : Type*} [DecidableEq ι]
    {family : Set C2Function} {E : Set (ℝ × ℝ)}
    {K delta diameter epsilon eta tRep DeltaRep C_R₀ : ℝ}
    (data : DyadicFineAssignmentData
      family E K delta diameter epsilon eta tRep DeltaRep C_R₀)
    (center : C2Function)
    (selected : Finset ι)
    (piece : ι → Set (ℝ × ℝ))
    (massFactor : ℕ)
    (Lambda : ENNReal)
    (hmass :
      volume (ambientRestrictedSet data center) ≤
        (massFactor : ENNReal) *
          ∑ i ∈ selected, volume (piece i))
    (hlayer : ∀ i ∈ selected,
      volume (piece i) < 2 * Lambda) :
    volume (ambientRestrictedSet data center) ≤
      ((2 * massFactor * selected.card : ℕ) : ENNReal) * Lambda := by
  have hsum :
      ∑ i ∈ selected, volume (piece i) ≤
        (selected.card : ENNReal) * (2 * Lambda) := by
    calc
      ∑ i ∈ selected, volume (piece i) ≤
          selected.card • (2 * Lambda) :=
        Finset.sum_le_card_nsmul selected
          (fun i => volume (piece i)) (2 * Lambda)
          (fun i hi => (hlayer i hi).le)
      _ = (selected.card : ENNReal) * (2 * Lambda) := by
        simp [nsmul_eq_mul]
  calc
    volume (ambientRestrictedSet data center) ≤
        (massFactor : ENNReal) *
          ∑ i ∈ selected, volume (piece i) :=
      hmass
    _ ≤
        (massFactor : ENNReal) *
          ((selected.card : ENNReal) * (2 * Lambda)) := by
      gcongr
    _ = ((2 * massFactor * selected.card : ℕ) : ENNReal) * Lambda := by
      norm_num
      ring

theorem ambient_restricted_selected_fine_volume_of_layer
    {family : Set C2Function} {E : Set (ℝ × ℝ)}
    {K delta diameter epsilon eta tRep DeltaRep C_R₀ : ℝ}
    (data : DyadicFineAssignmentData
      family E K delta diameter epsilon eta tRep DeltaRep C_R₀)
    (center : C2Function)
    (hE : MeasurableSet E)
    {C_R C_count C_shading C_volume : ℝ}
    (fineSetup : AmbientRestrictedFSVSetupData
      data center hE C_R C_count C_shading C_volume)
    (coarseSetup : AmbientRestrictedCoarseSetupData
      data center hE fineSetup)
    {massExponent : ℝ}
    (refinement : AmbientRestrictedLargeBinRefinementData
      data center hE fineSetup coarseSetup massExponent) :
    volume (ambientRestrictedSet data center) ≤
      ((2 * refinement.massFactor * refinement.selected.card : ℕ) :
          ENNReal) *
        ((2 : ENNReal) ^ refinement.layer.val * refinement.cutoff) := by
  exact
    ambient_restricted_selected_fine_volume_of_layer_mass
      data center refinement.selected refinement.piece
      refinement.massFactor
      ((2 : ENNReal) ^ refinement.layer.val * refinement.cutoff)
      refinement.selected_mass
      (fun i hi => by
        simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using
          (refinement.selected_layer i hi).2)

theorem ambient_restricted_selected_fine_volume_of_layer_toReal
    {family : Set C2Function} {E : Set (ℝ × ℝ)}
    {K delta diameter epsilon eta tRep DeltaRep C_R₀ : ℝ}
    (data : DyadicFineAssignmentData
      family E K delta diameter epsilon eta tRep DeltaRep C_R₀)
    (center : C2Function)
    (hE : MeasurableSet E)
    {C_R C_count C_shading C_volume : ℝ}
    (fineSetup : AmbientRestrictedFSVSetupData
      data center hE C_R C_count C_shading C_volume)
    (coarseSetup : AmbientRestrictedCoarseSetupData
      data center hE fineSetup)
    {massExponent : ℝ}
    (refinement : AmbientRestrictedLargeBinRefinementData
      data center hE fineSetup coarseSetup massExponent) :
    volume (ambientRestrictedSet data center) ≤
      (refinement.selected.card : ENNReal) *
        ENNReal.ofReal
          (((2 * refinement.massFactor : ℕ) : ℝ) *
            (((2 : ENNReal) ^ refinement.layer.val *
              refinement.cutoff).toReal)) := by
  let Lambda : ENNReal :=
    (2 : ENNReal) ^ refinement.layer.val * refinement.cutoff
  have hLambda_ne_top : Lambda ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) refinement.cutoff_ne_top
  have hvolume :=
    ambient_restricted_selected_fine_volume_of_layer
      data center hE fineSetup coarseSetup refinement
  calc
    volume (ambientRestrictedSet data center) ≤
        ((2 * refinement.massFactor * refinement.selected.card : ℕ) :
          ENNReal) * Lambda :=
      hvolume
    _ = (refinement.selected.card : ENNReal) *
        ENNReal.ofReal
          (((2 * refinement.massFactor : ℕ) : ℝ) *
            Lambda.toReal) := by
      rw [ENNReal.ofReal_mul (by positivity)]
      rw [ENNReal.ofReal_toReal hLambda_ne_top]
      norm_num
      ring

theorem ambient_restricted_selected_layer_mass_le_fine_area
    {family : Set C2Function} {E : Set (ℝ × ℝ)}
    {K delta diameter epsilon eta tRep DeltaRep C_R₀ : ℝ}
    (data : DyadicFineAssignmentData
      family E K delta diameter epsilon eta tRep DeltaRep C_R₀)
    (center : C2Function)
    (hE : MeasurableSet E)
    {C_R C_count C_shading C_volume : ℝ}
    (fineSetup : AmbientRestrictedFSVSetupData
      data center hE C_R C_count C_shading C_volume)
    (coarseSetup : AmbientRestrictedCoarseSetupData
      data center hE fineSetup)
    {massExponent : ℝ}
    (refinement : AmbientRestrictedLargeBinRefinementData
      data center hE fineSetup coarseSetup massExponent)
    (hC_shading_nonneg : 0 ≤ C_shading)
    (hdelta_nonneg : 0 ≤ delta) :
    (((2 : ENNReal) ^ refinement.layer.val *
        refinement.cutoff).toReal) ≤
      2 * (C_shading * delta) *
        Real.sqrt
          ((C_shading * delta) /
            (C_R * tRep * DeltaRep / delta)) := by
  rcases refinement.selected_nonempty with ⟨i, hi⟩
  let Lambda : ENNReal :=
    (2 : ENNReal) ^ refinement.layer.val * refinement.cutoff
  let area : ℝ :=
    2 * (C_shading * delta) *
      Real.sqrt
        ((C_shading * delta) /
          (C_R * tRep * DeltaRep / delta))
  have hLambda_ne_top : Lambda ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by simp) refinement.cutoff_ne_top
  have harea_nonneg : 0 ≤ area := by
    dsimp only [area]
    positivity
  have hbound : Lambda ≤ ENNReal.ofReal area := by
    calc
      Lambda ≤ volume (refinement.piece i) :=
        (refinement.selected_layer i hi).1
      _ ≤ ENNReal.ofReal
          (2 * (C_shading * delta) *
            (fineSetup.enlarged i).interval.length) :=
        refinement.piece_volume i
      _ = ENNReal.ofReal area := by
        rw [(fineSetup.enlarged i).interval_length]
  have hreal :
      Lambda.toReal ≤ (ENNReal.ofReal area).toReal :=
    (ENNReal.toReal_le_toReal hLambda_ne_top ENNReal.ofReal_ne_top).2 hbound
  simpa [Lambda, area, ENNReal.toReal_ofReal harea_nonneg] using hreal

theorem ambient_restricted_selected_fine_volume_of_mass
    {family : Set C2Function} {E : Set (ℝ × ℝ)}
    {K delta diameter epsilon eta tRep DeltaRep C_R₀ : ℝ}
    (data : DyadicFineAssignmentData
      family E K delta diameter epsilon eta tRep DeltaRep C_R₀)
    (center : C2Function)
    (hE : MeasurableSet E)
    {C_R C_count C_shading C_volume : ℝ}
    (fineSetup : AmbientRestrictedFSVSetupData
      data center hE C_R C_count C_shading C_volume)
    (selected : Finset (Fin fineSetup.fine.card))
    (piece : Fin fineSetup.fine.card → Set (ℝ × ℝ))
    (massFactor : ℕ)
    (hmass :
      volume (ambientRestrictedSet data center) ≤
        (massFactor : ENNReal) *
          ∑ i ∈ selected, volume (piece i))
    (hpiece : ∀ i ∈ selected,
      volume (piece i) ≤
        ENNReal.ofReal
          (2 * (C_shading * delta) *
            (fineSetup.enlarged i).interval.length))
    (hC_shading_nonneg : 0 ≤ C_shading)
    (hdelta_nonneg : 0 ≤ delta) :
    volume (ambientRestrictedSet data center) ≤
      (selected.card : ENNReal) *
        ENNReal.ofReal
          ((massFactor : ℝ) *
            (2 * (C_shading * delta) *
              Real.sqrt
                ((C_shading * delta) /
                  (C_R * tRep * DeltaRep / delta)))) := by
  set a : ENNReal := (massFactor : ENNReal) with ha_def
  set b : ENNReal := (selected.card : ENNReal) with hb_def
  set C : ENNReal := ENNReal.ofReal
      (2 * (C_shading * delta) *
        Real.sqrt
          ((C_shading * delta) /
            (C_R * tRep * DeltaRep / delta))) with hC_def
  have hpiece' : ∀ i ∈ selected, volume (piece i) ≤ C := by
    intro i hi
    have h := hpiece i hi
    have hlength :
        (fineSetup.enlarged i).interval.length =
          Real.sqrt
            ((C_shading * delta) /
              (C_R * tRep * DeltaRep / delta)) :=
      (fineSetup.enlarged i).interval_length
    rw [hlength] at h
    exact h
  have hsum :
      ∑ i ∈ selected, C = b * C := by
    rw [Finset.sum_const, hb_def]
    ring
  have hsum_bound :
      ∑ i ∈ selected, volume (piece i) ≤ b * C := by
    calc
      ∑ i ∈ selected, volume (piece i) ≤
          ∑ i ∈ selected, C :=
        Finset.sum_le_sum hpiece'
      _ = b * C := hsum
  have hmassFactor : 0 ≤ (massFactor : ℝ) := by positivity
  have haC :
      a * C =
        ENNReal.ofReal
          ((massFactor : ℝ) *
            (2 * (C_shading * delta) *
              Real.sqrt
                ((C_shading * delta) /
                  (C_R * tRep * DeltaRep / delta)))) := by
    have ha :
        a = ENNReal.ofReal (massFactor : ℝ) := by
      rw [ha_def]
      norm_cast
    rw [ha, hC_def, ENNReal.ofReal_mul hmassFactor]
  calc
    volume (ambientRestrictedSet data center) ≤
        a * ∑ i ∈ selected, volume (piece i) :=
      hmass
    _ ≤ a * (b * C) := (mul_le_mul_right hsum_bound) a
    _ = b * (a * C) := mul_left_comm a b C
    _ = b * ENNReal.ofReal
          ((massFactor : ℝ) *
            (2 * (C_shading * delta) *
              Real.sqrt
                ((C_shading * delta) /
                  (C_R * tRep * DeltaRep / delta)))) := by
      rw [haC]

theorem ambient_restricted_selected_fine_volume :
    AmbientRestrictedSelectedFineVolumeStatement := by
  intro family E K delta diameter epsilon eta tRep DeltaRep C_R₀
    data center hE C_R C_count C_shading C_volume
    fineSetup coarseSetup massExponent refinement hC_shading_nonneg hdelta_nonneg
  exact
    ambient_restricted_selected_fine_volume_of_mass
      data center hE fineSetup refinement.selected refinement.piece
      refinement.massFactor
      refinement.selected_mass
      (fun i _ => refinement.piece_volume i)
      hC_shading_nonneg hdelta_nonneg

end Kakeya.Cinematic
