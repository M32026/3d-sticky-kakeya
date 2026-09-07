import MyLeanRepo.Kakeya.Cinematic.Section5.ParentFiberCardinalityRegularizationInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.PolynomialDyadicPieceRangeInputs

/-!
# Polynomially controlled dyadic piece refinement

This module composes the quantitative polynomial range with the validated
finite dyadic pigeonhole.  It keeps the logarithmic layer count and the
selected mass layer in one caller-facing result.
-/

namespace Kakeya.Cinematic

lemma dyadic_selected_mass_le_card_mul
    {N L : ℕ} (weight : Fin N → ENNReal)
    (selected : Finset (Fin N)) (Lambda total : ENNReal)
    (hweight : ∀ i ∈ selected, weight i < 2 * Lambda)
    (htotal :
      total ≤
        ((2 * L : ℕ) : ENNReal) *
          ∑ i ∈ selected, weight i) :
    total ≤
      ((4 * L * selected.card : ℕ) : ENNReal) * Lambda := by
  have hsum :
      (∑ i ∈ selected, weight i) ≤
        (selected.card : ENNReal) * (2 * Lambda) := by
    calc
      (∑ i ∈ selected, weight i)
          ≤ selected.card • (2 * Lambda) :=
        Finset.sum_le_card_nsmul selected weight (2 * Lambda)
          (fun i hi => (hweight i hi).le)
      _ = (selected.card : ENNReal) * (2 * Lambda) := by
        simp [nsmul_eq_mul]
  calc
    total ≤
        ((2 * L : ℕ) : ENNReal) *
          ∑ i ∈ selected, weight i := htotal
    _ ≤ ((2 * L : ℕ) : ENNReal) *
          ((selected.card : ENNReal) * (2 * Lambda)) := by
      gcongr
    _ = ((4 * L * selected.card : ℕ) : ENNReal) * Lambda := by
      norm_num
      ring

lemma dyadic_selected_mass_le_coarse_mul
    {N L M : ℕ} (weight : Fin N → ENNReal)
    (selected : Finset (Fin N)) (Lambda total bound : ENNReal)
    (hweight : ∀ i ∈ selected, weight i < 2 * Lambda)
    (htotal :
      total ≤
        ((2 * L : ℕ) : ENNReal) *
          ∑ i ∈ selected, weight i)
    (hselected :
      (selected.card : ENNReal) * Lambda ≤
        (M : ENNReal) * bound) :
    total ≤ ((4 * L * M : ℕ) : ENNReal) * bound := by
  have hcard :=
    dyadic_selected_mass_le_card_mul
      weight selected Lambda total hweight htotal
  calc
    total ≤
        ((4 * L * selected.card : ℕ) : ENNReal) * Lambda :=
      hcard
    _ = ((4 * L : ℕ) : ENNReal) *
          ((selected.card : ENNReal) * Lambda) := by
      norm_num
      ring
    _ ≤ ((4 * L : ℕ) : ENNReal) *
          ((M : ENNReal) * bound) := by
      gcongr
    _ = ((4 * L * M : ℕ) : ENNReal) * bound := by
      norm_num
      ring

lemma dyadic_selected_mass_le_parent_regularized_mul
    {N M L loss : ℕ}
    (weight : Fin N → ENNReal) (selected : Finset (Fin N))
    (parent : Fin N → Fin M) (selectedParents : Finset (Fin M))
    (Lambda total bound : ENNReal)
    (hlayerUpper : ∀ i ∈ selected, weight i < 2 * Lambda)
    (hmass :
      total ≤
        ((2 * L : ℕ) : ENNReal) *
          ∑ i ∈ selected, weight i)
    (hcard :
      selected.card ≤
        loss *
          (rectanglesOverParents
            selected parent selectedParents).card)
    (hpartition :
      (rectanglesOverParents
        selected parent selectedParents).card =
          ∑ coarse ∈ selectedParents,
            (parentFiber selected parent coarse).card)
    (hparent : ∀ coarse ∈ selectedParents,
      ((parentFiber selected parent coarse).card : ENNReal) *
        Lambda ≤ bound) :
    total ≤
      ((4 * L * loss * selectedParents.card : ℕ) : ENNReal) *
        bound := by
  let retained :=
    rectanglesOverParents selected parent selectedParents
  have hretainedMass :
      (retained.card : ENNReal) * Lambda ≤
        (selectedParents.card : ENNReal) * bound := by
    have hpartitionENN :
        (retained.card : ENNReal) =
          ∑ coarse ∈ selectedParents,
            ((parentFiber selected parent coarse).card : ENNReal) := by
      exact_mod_cast hpartition
    rw [hpartitionENN, Finset.sum_mul]
    calc
      ∑ coarse ∈ selectedParents,
          ((parentFiber selected parent coarse).card : ENNReal) *
            Lambda ≤
          ∑ _coarse ∈ selectedParents, bound := by
        apply Finset.sum_le_sum
        intro coarse hcoarse
        exact hparent coarse hcoarse
      _ = (selectedParents.card : ENNReal) * bound := by
        simp [Finset.sum_const]
  have hselectedMass :
      (selected.card : ENNReal) * Lambda ≤
        (((loss * selectedParents.card : ℕ) : ENNReal)) * bound := by
    have hcardENN :
        (selected.card : ENNReal) ≤
          (loss : ENNReal) * (retained.card : ENNReal) := by
      exact_mod_cast hcard
    calc
      (selected.card : ENNReal) * Lambda ≤
          ((loss : ENNReal) * (retained.card : ENNReal)) * Lambda :=
        mul_le_mul_of_nonneg_right hcardENN bot_le
      _ = (loss : ENNReal) *
          ((retained.card : ENNReal) * Lambda) := by
        ring
      _ ≤ (loss : ENNReal) *
          ((selectedParents.card : ENNReal) * bound) :=
        mul_le_mul_of_nonneg_left hretainedMass bot_le
      _ = (((loss * selectedParents.card : ℕ) : ENNReal)) *
          bound := by
        norm_num
        ring
  simpa [Nat.mul_assoc] using
    (dyadic_selected_mass_le_coarse_mul
      weight selected Lambda total bound hlayerUpper hmass
        hselectedMass)

lemma polynomial_dyadic_piece_refinement
    (hRange : PolynomialDyadicPieceRangeStatement)
    (hRefine : DyadicPieceVolumeRefinementStatement)
    {delta countExponent massExponent : ℝ}
    {N : ℕ} (weight : Fin N → ENNReal)
    {total lower upper : ENNReal}
    (hdelta : 0 < delta)
    (hdelta_half : delta ≤ 1 / 2)
    (hcountExponent : 0 ≤ countExponent)
    (hmassExponent : 0 ≤ massExponent)
    (hN : 0 < N)
    (hN_count : (N : ℝ) ≤ Real.rpow delta (-countExponent))
    (htotal_lower :
      ENNReal.ofReal (Real.rpow delta massExponent) < total)
    (hcutoff : 2 * ((N : ENNReal) * lower) = total)
    (hupper : upper ≤ 1)
    (htotal : ∑ i, weight i = total)
    (hlower : 0 < lower)
    (hweight : ∀ i, weight i ≤ upper)
    (hhalf :
      total ≤
        2 * ∑ i ∈ (Finset.univ.filter fun i => lower ≤ weight i),
          weight i) :
    ∃ L : ℕ,
      0 < L ∧
      (L : ℝ) ≤
        (countExponent + massExponent + 2) *
          (Real.logb 2 (1 / delta) + 1) ∧
      ∃ (j : Fin L) (selected : Finset (Fin N)),
        selected.Nonempty ∧
        (∀ i ∈ selected,
          (2 : ENNReal) ^ j.val * lower ≤ weight i ∧
          weight i <
            (2 : ENNReal) ^ (j.val + 1) * lower) ∧
        (∑ i, weight i) ≤
          ((2 * L : ℕ) : ENNReal) *
            ∑ i ∈ selected, weight i := by
  rcases hRange hdelta hdelta_half hcountExponent hmassExponent hN
      hN_count htotal_lower hcutoff hupper with
    ⟨L, hL, hrange, hL_bound⟩
  have htotal_pos : 0 < total :=
    lt_of_le_of_lt
      (by positivity :
        (0 : ENNReal) ≤
          ENNReal.ofReal (Real.rpow delta massExponent))
      htotal_lower
  have hsum_pos : 0 < ∑ i, weight i := by
    rw [htotal]
    exact htotal_pos
  have hhalf_sum :
      (∑ i, weight i) ≤
        2 * ∑ i ∈ (Finset.univ.filter fun i => lower ≤ weight i),
          weight i := by
    rw [htotal]
    exact hhalf
  rcases hRefine weight lower upper hL hlower hrange hweight hsum_pos
      hhalf_sum with
    ⟨j, selected, hselected, hlayer, hmass⟩
  exact ⟨L, hL, hL_bound, j, selected, hselected, hlayer, hmass⟩

/--
Apply the polynomial dyadic refinement directly from the canonical cutoff.
The cutoff identity and exact total-mass decomposition automatically imply
that pieces above the cutoff retain at least half of the total mass.
-/
lemma polynomial_dyadic_piece_refinement_from_cutoff
    (hRange : PolynomialDyadicPieceRangeStatement)
    (hRefine : DyadicPieceVolumeRefinementStatement)
    {delta countExponent massExponent : ℝ}
    {N : ℕ} (weight : Fin N → ENNReal)
    {total lower upper : ENNReal}
    (hdelta : 0 < delta)
    (hdelta_half : delta ≤ 1 / 2)
    (hcountExponent : 0 ≤ countExponent)
    (hmassExponent : 0 ≤ massExponent)
    (hN : 0 < N)
    (hN_count : (N : ℝ) ≤ Real.rpow delta (-countExponent))
    (htotal_lower :
      ENNReal.ofReal (Real.rpow delta massExponent) < total)
    (hcutoff : 2 * ((N : ENNReal) * lower) = total)
    (hupper : upper ≤ 1)
    (htotal : ∑ i, weight i = total)
    (hlower : 0 < lower)
    (hlower_ne_top : lower ≠ ⊤)
    (hweight : ∀ i, weight i ≤ upper) :
    ∃ L : ℕ,
      0 < L ∧
      (L : ℝ) ≤
        (countExponent + massExponent + 2) *
          (Real.logb 2 (1 / delta) + 1) ∧
      ∃ (j : Fin L) (selected : Finset (Fin N)),
        selected.Nonempty ∧
        (∀ i ∈ selected,
          (2 : ENNReal) ^ j.val * lower ≤ weight i ∧
          weight i <
            (2 : ENNReal) ^ (j.val + 1) * lower) ∧
        (∑ i, weight i) ≤
          ((2 * L : ℕ) : ENNReal) *
            ∑ i ∈ selected, weight i := by
  have hcutoff_le :
      2 * ((N : ENNReal) * lower) ≤ ∑ i, weight i := by
    rw [hcutoff, htotal]
  have hhalf :
      (∑ i, weight i) ≤
        2 * ∑ i ∈
          (Finset.univ.filter fun i => lower ≤ weight i),
          weight i :=
    sum_le_two_mul_sum_filter_of_cutoff
      weight lower hlower_ne_top hcutoff_le
  have hhalf_total :
      total ≤
        2 * ∑ i ∈
          (Finset.univ.filter fun i => lower ≤ weight i),
          weight i := by
    rw [← htotal]
    exact hhalf
  exact polynomial_dyadic_piece_refinement
    hRange hRefine weight hdelta hdelta_half hcountExponent
    hmassExponent hN hN_count htotal_lower hcutoff hupper htotal
    hlower hweight hhalf_total

end Kakeya.Cinematic
