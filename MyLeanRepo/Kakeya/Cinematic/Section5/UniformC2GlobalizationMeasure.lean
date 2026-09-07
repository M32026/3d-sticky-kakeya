import MyLeanRepo.Kakeya.Cinematic.Section5.UniformC2GlobalizationInputs

/-!
# Finite-cover measure bookkeeping for uniform globalization

This module isolates the measure subadditivity used after splitting a level
set into two endpoint stubs and finitely many centered interval pieces.
-/

noncomputable section

open MeasureTheory Set

namespace Kakeya.Cinematic

theorem volume_le_card_add_two_mul_of_cover
    {ι : Type*} [Fintype ι]
    {E left right : Set (ℝ × ℝ)}
    {pieces : ι → Set (ℝ × ℝ)} {B : ENNReal}
    (hcover : E ⊆ left ∪ right ∪ ⋃ i, pieces i)
    (hleft : volume left ≤ B)
    (hright : volume right ≤ B)
    (hpieces : ∀ i, volume (pieces i) ≤ B) :
    volume E ≤ (Fintype.card ι + 2 : ℕ) * B := by
  have hmono :
      volume E ≤ volume (left ∪ right ∪ ⋃ i, pieces i) :=
    measure_mono hcover
  have hunion :
      volume (left ∪ right ∪ ⋃ i, pieces i) ≤
        volume left + volume right + volume (⋃ i, pieces i) :=
    calc
      volume (left ∪ right ∪ ⋃ i, pieces i) ≤
          volume (left ∪ right) + volume (⋃ i, pieces i) :=
        MeasureTheory.measure_union_le _ _
      _ ≤ (volume left + volume right) + volume (⋃ i, pieces i) :=
        add_le_add (MeasureTheory.measure_union_le _ _) le_rfl
  have hfinite :
      volume (⋃ i, pieces i) ≤ ∑ i, volume (pieces i) :=
    MeasureTheory.measure_iUnion_fintype_le volume pieces
  have hsum : ∑ i, volume (pieces i) ≤ (Fintype.card ι : ENNReal) * B := by
    calc
      ∑ i, volume (pieces i) ≤ ∑ _i : ι, B :=
        Finset.sum_le_sum fun i _ => hpieces i
      _ = (Fintype.card ι : ENNReal) * B := by simp
  have hfinite_sum :
      volume (⋃ i, pieces i) ≤ (Fintype.card ι : ENNReal) * B :=
    hfinite.trans hsum
  calc
    volume E ≤ volume (left ∪ right ∪ ⋃ i, pieces i) := hmono
    _ ≤ volume left + volume right + volume (⋃ i, pieces i) := hunion
    _ ≤ B + B + ((Fintype.card ι : ENNReal) * B) := by
      exact add_le_add (add_le_add hleft hright) hfinite_sum
    _ = (Fintype.card ι + 2 : ℕ) * B := by
      push_cast
      ring

end Kakeya.Cinematic
