import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23BaseCyclePigeonholeStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23SnappedFourCycleAbundanceStatements

/-!
# Base-key image bound in WZ1 Lemma 23

The first-cube Step 4 key consists of one occupied height and one global
scalar bin at that height.  Hence its image on any subfamily of actual
snapped four-cycles has cardinality at most
`#occupiedHeights * globalBinBound`.
-/

namespace Kakeya.Assouad

theorem wz1_lemma23_base_key_image_bound
    (rho : ℝ) (f g : ℝ → ℝ)
    (cells : Finset (ℤ × ℤ × ℤ))
    (globalBinBound : ℕ)
    (hglobalBins :
      ∀ z ∈ wz1Lemma23SnappedHeights cells,
        (wz1Lemma23SnappedGlobalBinsAt
          rho f cells z).card ≤ globalBinBound) :
    ((wz1Lemma23SnappedFourCycles rho f g cells).image
        (wz1Lemma23BaseCycleKey rho f)).card ≤
      (wz1Lemma23SnappedHeights cells).card *
        globalBinBound := by
  let heights := wz1Lemma23SnappedHeights cells
  let globalBinsAt :=
    fun z : ℤ => wz1Lemma23SnappedGlobalBinsAt rho f cells z
  let keyUniverse :=
    heights.biUnion
      (fun z : ℤ => ({z} : Finset ℤ) ×ˢ globalBinsAt z)
  have hsubset :
      (wz1Lemma23SnappedFourCycles rho f g cells).image
          (wz1Lemma23BaseCycleKey rho f) ⊆
        keyUniverse := by
    intro key hkey
    rcases Finset.mem_image.mp hkey with
      ⟨cycle, hcycle, rfl⟩
    have hfirst :
        cycle.1 ∈ cells := by
      have h_all :
          (cycle.1 ∈ cells ∧
            cycle.2.1 ∈ cells ∧
            cycle.2.2.1 ∈ cells ∧
            cycle.2.2.2 ∈ cells) ∧
          wz1Lemma23SameSnappedLocalGrain rho g
              cycle.1 cycle.2.1 ∧
          wz1Lemma23SameSnappedLocalGrain rho g
              cycle.2.2.2 cycle.2.2.1 ∧
          wz1Lemma23SnappedHeight cycle.1 =
              wz1Lemma23SnappedHeight cycle.2.2.2 ∧
          wz1Lemma23SnappedHeight cycle.2.1 =
              wz1Lemma23SnappedHeight cycle.2.2.1 ∧
          wz1Lemma23SnappedGlobalBin rho f cycle.2.1 =
              wz1Lemma23SnappedGlobalBin rho f cycle.2.2.1 := by
        simpa [wz1Lemma23SnappedFourCycles,
          wz1Lemma23FourCycles] using hcycle
      exact h_all.1.1
    have hheight :
        wz1Lemma23SnappedHeight cycle.1 ∈ heights :=
      Finset.mem_image.mpr ⟨cycle.1, hfirst, rfl⟩
    have hglobal :
        wz1Lemma23SnappedGlobalBin rho f cycle.1 ∈
          globalBinsAt
            (wz1Lemma23SnappedHeight cycle.1) := by
      exact Finset.mem_image.mpr
        ⟨cycle.1,
          Finset.mem_filter.mpr ⟨hfirst, rfl⟩,
          rfl⟩
    have hmem :
        (wz1Lemma23SnappedHeight cycle.1,
            wz1Lemma23SnappedGlobalBin rho f cycle.1) ∈
          keyUniverse :=
      Finset.mem_biUnion.mpr
        ⟨wz1Lemma23SnappedHeight cycle.1, hheight,
          Finset.mem_product.mpr ⟨by simp, hglobal⟩⟩
    simpa [wz1Lemma23BaseCycleKey] using hmem
  calc
    ((wz1Lemma23SnappedFourCycles rho f g cells).image
        (wz1Lemma23BaseCycleKey rho f)).card
        ≤ keyUniverse.card :=
      Finset.card_le_card hsubset
    _ ≤ ∑ z ∈ heights,
        ((({z} : Finset ℤ) ×ˢ globalBinsAt z).card) :=
      Finset.card_biUnion_le
    _ = ∑ z ∈ heights, (globalBinsAt z).card := by
      apply Finset.sum_congr rfl
      intro z _
      simp
    _ ≤ ∑ _z ∈ heights, globalBinBound :=
      Finset.sum_le_sum hglobalBins
    _ = heights.card * globalBinBound := by simp

end Kakeya.Assouad
