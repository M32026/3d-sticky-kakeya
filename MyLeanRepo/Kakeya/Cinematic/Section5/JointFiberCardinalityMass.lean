import MyLeanRepo.Kakeya.Cinematic.Section5.PolynomialDyadicPieceRefinement

/-!
# Retained mass after joint fiber-cardinality regularization

Inside one selected piece-volume layer, all weights differ by at most a
factor of two.  Therefore a cardinality sub-selection retaining a
`1 / loss` fraction of the indices retains mass up to the explicit additional
factor `2 * loss`.
-/

namespace Kakeya.Cinematic

lemma dyadic_selected_mass_le_joint_regularized_sum
    {N L loss : ℕ}
    (weight : Fin N → ENNReal)
    (selected retained : Finset (Fin N))
    (Lambda total : ENNReal)
    (hselectedUpper : ∀ i ∈ selected, weight i < 2 * Lambda)
    (hretainedLower : ∀ i ∈ retained, Lambda ≤ weight i)
    (hmass :
      total ≤
        ((2 * L : ℕ) : ENNReal) *
          ∑ i ∈ selected, weight i)
    (hcard :
      selected.card ≤ loss * retained.card) :
    total ≤
      ((4 * L * loss : ℕ) : ENNReal) *
        ∑ i ∈ retained, weight i := by
  have hselectedSum :
      (∑ i ∈ selected, weight i) ≤
        (selected.card : ENNReal) * (2 * Lambda) := by
    calc
      (∑ i ∈ selected, weight i) ≤
          selected.card • (2 * Lambda) :=
        Finset.sum_le_card_nsmul selected weight (2 * Lambda)
          (fun i hi => (hselectedUpper i hi).le)
      _ = (selected.card : ENNReal) * (2 * Lambda) := by
        simp [nsmul_eq_mul]
  have hretainedSum :
      (retained.card : ENNReal) * Lambda ≤
        ∑ i ∈ retained, weight i := by
    calc
      (retained.card : ENNReal) * Lambda =
          ∑ _i ∈ retained, Lambda := by
        simp [Finset.sum_const]
      _ ≤ ∑ i ∈ retained, weight i :=
        Finset.sum_le_sum fun i hi => hretainedLower i hi
  have hcardENN :
      (selected.card : ENNReal) ≤
        (loss : ENNReal) * retained.card := by
    exact_mod_cast hcard
  calc
    total ≤
        ((2 * L : ℕ) : ENNReal) *
          ∑ i ∈ selected, weight i :=
      hmass
    _ ≤
        ((2 * L : ℕ) : ENNReal) *
          ((selected.card : ENNReal) * (2 * Lambda)) := by
      gcongr
    _ ≤
        ((2 * L : ℕ) : ENNReal) *
          (((loss : ENNReal) * retained.card) * (2 * Lambda)) := by
      gcongr
    _ =
        ((4 * L * loss : ℕ) : ENNReal) *
          ((retained.card : ENNReal) * Lambda) := by
      norm_num
      ring
    _ ≤
        ((4 * L * loss : ℕ) : ENNReal) *
          ∑ i ∈ retained, weight i := by
      gcongr

end Kakeya.Cinematic
