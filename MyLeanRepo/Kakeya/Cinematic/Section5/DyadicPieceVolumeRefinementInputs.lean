import MyLeanRepo.Kakeya.Cinematic.Section5.FineCarrierMeasurableAssignmentInputs

/-!
# Dyadic refinement of assigned piece volumes

After measurable disjointification, every selected fine rectangle carries one
nonnegative `ENNReal` piece volume.  Once tiny pieces retain at least half of
the total mass and all remaining weights lie in a finite dyadic range, one
dyadic layer retains a `1 / (2L)` fraction of the total weight.
-/

namespace Kakeya.Cinematic

lemma exists_positive_finite_half_mass_cutoff
    {N : ℕ} (hN : 0 < N)
    {total : ENNReal} (htotal_pos : 0 < total)
    (htotal_ne_top : total ≠ ⊤) :
    ∃ lower : ENNReal,
      0 < lower ∧
      lower ≠ ⊤ ∧
      2 * ((N : ENNReal) * lower) = total := by
  let denominator : ENNReal := ((2 * N : ℕ) : ENNReal)
  have hdenominator_pos : 0 < denominator := by
    simp [denominator, hN]
  have hdenominator_ne_zero : denominator ≠ 0 :=
    hdenominator_pos.ne'
  have hdenominator_ne_top : denominator ≠ ⊤ := by
    exact ENNReal.natCast_ne_top (2 * N)
  let lower : ENNReal := total / denominator
  have hlower_pos : 0 < lower := by
    exact ENNReal.div_pos htotal_pos.ne' hdenominator_ne_top
  have hlower_ne_top : lower ≠ ⊤ := by
    exact ENNReal.div_ne_top htotal_ne_top hdenominator_ne_zero
  have hfactor :
      2 * ((N : ENNReal) * lower) = denominator * lower := by
    simp [denominator]
    ring
  have hcancel : denominator * lower = total := by
    dsimp only [lower]
    exact ENNReal.mul_div_cancel hdenominator_ne_zero hdenominator_ne_top
  exact ⟨lower, hlower_pos, hlower_ne_top, hfactor.trans hcancel⟩

lemma sum_le_two_mul_sum_filter_of_cutoff
    {N : ℕ} (weight : Fin N → ENNReal) (lower : ENNReal)
    (hlower_ne_top : lower ≠ ⊤)
    (hcutoff :
      2 * ((N : ENNReal) * lower) ≤ ∑ i, weight i) :
    (∑ i, weight i) ≤
      2 * ∑ i ∈ (Finset.univ.filter fun i => lower ≤ weight i),
        weight i := by
  classical
  let retained : Finset (Fin N) :=
    Finset.univ.filter fun i => lower ≤ weight i
  let tiny : Finset (Fin N) :=
    Finset.univ.filter fun i => ¬ lower ≤ weight i
  have hpartition :
      (∑ i ∈ retained, weight i) + (∑ i ∈ tiny, weight i) =
        ∑ i, weight i := by
    simpa [retained, tiny] using
      Finset.sum_filter_add_sum_filter_not
        (Finset.univ : Finset (Fin N))
        (fun i => lower ≤ weight i) weight
  have htiny_each : ∀ i ∈ tiny, weight i ≤ lower := by
    intro i hi
    have hnot : ¬ lower ≤ weight i := by
      simpa [tiny] using hi
    exact le_of_lt (lt_of_not_ge hnot)
  have htiny_card : (tiny.card : ENNReal) ≤ N := by
    have hcard : tiny.card ≤ N := by
      simpa using tiny.card_le_univ
    exact_mod_cast hcard
  have htiny :
      (∑ i ∈ tiny, weight i) ≤ (N : ENNReal) * lower := by
    calc
      (∑ i ∈ tiny, weight i) ≤ tiny.card • lower :=
        Finset.sum_le_card_nsmul tiny weight lower htiny_each
      _ = (tiny.card : ENNReal) * lower := by
        simp [nsmul_eq_mul]
      _ ≤ (N : ENNReal) * lower := by
        gcongr
  have htiny_ne_top : (∑ i ∈ tiny, weight i) ≠ ⊤ := by
    exact ne_top_of_le_ne_top
      (ENNReal.mul_ne_top (by simp) hlower_ne_top) htiny
  have htwice_tiny :
      2 * (∑ i ∈ tiny, weight i) ≤ ∑ i, weight i := by
    calc
      2 * (∑ i ∈ tiny, weight i) ≤ 2 * ((N : ENNReal) * lower) := by
        gcongr
      _ ≤ ∑ i, weight i := hcutoff
  have htiny_retained :
      (∑ i ∈ tiny, weight i) ≤ ∑ i ∈ retained, weight i := by
    apply
      (ENNReal.add_le_add_iff_right htiny_ne_top).mp
    calc
      (∑ i ∈ tiny, weight i) + (∑ i ∈ tiny, weight i) =
          2 * (∑ i ∈ tiny, weight i) := by ring
      _ ≤ ∑ i, weight i := htwice_tiny
      _ = (∑ i ∈ retained, weight i) +
          (∑ i ∈ tiny, weight i) := hpartition.symm
  calc
    (∑ i, weight i) =
        (∑ i ∈ retained, weight i) +
          (∑ i ∈ tiny, weight i) := hpartition.symm
    _ ≤ (∑ i ∈ retained, weight i) +
          (∑ i ∈ retained, weight i) := by
      gcongr
    _ = 2 * ∑ i ∈ retained, weight i := by ring
    _ = 2 * ∑ i ∈
          (Finset.univ.filter fun i => lower ≤ weight i),
          weight i := by rfl

def DyadicPieceVolumeRefinementStatement : Prop :=
  ∀ {N L : ℕ} (weight : Fin N → ENNReal)
    (lower upper : ENNReal),
    0 < L →
    0 < lower →
    upper < (2 : ENNReal) ^ L * lower →
    (∀ i, weight i ≤ upper) →
    0 < ∑ i, weight i →
    (∑ i, weight i) ≤
      2 * ∑ i ∈ (Finset.univ.filter fun i => lower ≤ weight i),
        weight i →
    ∃ (j : Fin L) (selected : Finset (Fin N)),
      selected.Nonempty ∧
      (∀ i ∈ selected,
        (2 : ENNReal) ^ j.val * lower ≤ weight i ∧
        weight i <
          (2 : ENNReal) ^ (j.val + 1) * lower) ∧
      (∑ i, weight i) ≤
        ((2 * L : ℕ) : ENNReal) *
          ∑ i ∈ selected, weight i

end Kakeya.Cinematic
