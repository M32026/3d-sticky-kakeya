import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23FourCycleCounting
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23SnappedFourCycleAbundanceStatements

/-!
# Actual snapped four-cycle abundance in WZ1 Lemma 23

Bound the two concrete key images and apply finite Cauchy--Schwarz twice.
The second collision count is identified with the already-closed generic
four-cycle theorem.
-/

namespace Kakeya.Assouad

open Finset

/-- The snapped local-key image has at most one local-bin fiber per y-layer. -/
theorem wz1_lemma23_snapped_local_key_image_bound
    (rho : ℝ) (g : ℝ → ℝ)
    (cells : Finset (ℤ × ℤ × ℤ))
    (localBinBound : ℕ)
    (hlocalBins : ∀ y ∈ wz1Lemma23SnappedYLayers cells,
      (wz1Lemma23SnappedLocalBinsAt
        rho g cells y).card ≤ localBinBound) :
    (cells.image (wz1Lemma23SnappedLocalKey rho g)).card ≤
      (wz1Lemma23SnappedYLayers cells).card *
        localBinBound := by
  let localKey := wz1Lemma23SnappedLocalKey rho g
  let yLayers := wz1Lemma23SnappedYLayers cells
  let localBinsAt :=
    fun y : ℤ => wz1Lemma23SnappedLocalBinsAt rho g cells y
  let localKeyUniverse :=
    yLayers.biUnion
      (fun y : ℤ => ({y} : Finset ℤ) ×ˢ localBinsAt y)
  have hsubset :
      cells.image localKey ⊆ localKeyUniverse := by
    intro key hkey
    rcases Finset.mem_image.mp hkey with ⟨index, hindex, rfl⟩
    have hy : index.2.1 ∈ yLayers :=
      Finset.mem_image.mpr ⟨index, hindex, rfl⟩
    have hbin :
        (localKey index).2 ∈ localBinsAt index.2.1 := by
      exact Finset.mem_image.mpr
        ⟨index, Finset.mem_filter.mpr ⟨hindex, rfl⟩, rfl⟩
    exact Finset.mem_biUnion.mpr
      ⟨index.2.1, hy,
        Finset.mem_product.mpr
          ⟨by simp [localKey, wz1Lemma23SnappedLocalKey],
            hbin⟩⟩
  calc
    (cells.image localKey).card
        ≤ localKeyUniverse.card :=
      Finset.card_le_card hsubset
    _ ≤ ∑ y ∈ yLayers,
        ((({y} : Finset ℤ) ×ˢ localBinsAt y).card) :=
      Finset.card_biUnion_le
    _ = ∑ y ∈ yLayers, (localBinsAt y).card := by
      apply Finset.sum_congr rfl
      intro y _
      simp
    _ ≤ ∑ _y ∈ yLayers, localBinBound :=
      Finset.sum_le_sum hlocalBins
    _ = yLayers.card * localBinBound := by simp

section

attribute [local instance] Classical.dec

/--
The pair-signature image is bounded by two occupied heights and one global
bin on the second endpoint.
-/
theorem wz1_lemma23_snapped_signature_image_bound
    (rho : ℝ) (f g : ℝ → ℝ)
    (cells : Finset (ℤ × ℤ × ℤ))
    (globalBinBound : ℕ)
    (hglobalBins : ∀ z ∈ wz1Lemma23SnappedHeights cells,
      (wz1Lemma23SnappedGlobalBinsAt
        rho f cells z).card ≤ globalBinBound) :
    ((wz1Lemma23LocalPairs cells
        (wz1Lemma23SameSnappedLocalGrain rho g)).image
      (wz1Lemma23PairSignature wz1Lemma23SnappedHeight
        (wz1Lemma23SnappedGlobalBin rho f))).card ≤
      (wz1Lemma23SnappedHeights cells).card ^ 2 *
        globalBinBound := by
  let height := wz1Lemma23SnappedHeight
  let globalBin := wz1Lemma23SnappedGlobalBin rho f
  let sameLocal := wz1Lemma23SameSnappedLocalGrain rho g
  let heights := wz1Lemma23SnappedHeights cells
  let localPairs := wz1Lemma23LocalPairs cells sameLocal
  let signature := wz1Lemma23PairSignature height globalBin
  let globalBinsAt :=
    fun z : ℤ => wz1Lemma23SnappedGlobalBinsAt rho f cells z
  let globalPairs :=
    heights.biUnion
      (fun z : ℤ => ({z} : Finset ℤ) ×ˢ globalBinsAt z)
  let signatureUniverse := heights ×ˢ globalPairs
  have hsubset :
      localPairs.image signature ⊆ signatureUniverse := by
    intro value hvalue
    rcases Finset.mem_image.mp hvalue with
      ⟨pair, hpair, rfl⟩
    have hmem :
        (pair.1 ∈ cells ∧ pair.2 ∈ cells) ∧
          sameLocal pair.1 pair.2 := by
      simpa [localPairs, wz1Lemma23LocalPairs,
        Finset.mem_filter, Finset.mem_product] using hpair
    have hz1 : height pair.1 ∈ heights :=
      Finset.mem_image.mpr ⟨pair.1, hmem.1.1, rfl⟩
    have hz2 : height pair.2 ∈ heights :=
      Finset.mem_image.mpr ⟨pair.2, hmem.1.2, rfl⟩
    have hglobal :
        globalBin pair.2 ∈ globalBinsAt (height pair.2) := by
      exact Finset.mem_image.mpr
        ⟨pair.2,
          Finset.mem_filter.mpr ⟨hmem.1.2, rfl⟩,
          rfl⟩
    have hpair_global :
        (height pair.2, globalBin pair.2) ∈ globalPairs :=
      Finset.mem_biUnion.mpr
        ⟨height pair.2, hz2,
          Finset.mem_product.mpr ⟨by simp, hglobal⟩⟩
    exact Finset.mem_product.mpr ⟨hz1, hpair_global⟩
  have hglobalPairs :
      globalPairs.card ≤ heights.card * globalBinBound := by
    calc
      globalPairs.card
          ≤ ∑ z ∈ heights,
              ((({z} : Finset ℤ) ×ˢ globalBinsAt z).card) :=
        Finset.card_biUnion_le
      _ = ∑ z ∈ heights, (globalBinsAt z).card := by
        apply Finset.sum_congr rfl
        intro z _
        simp
      _ ≤ ∑ _z ∈ heights, globalBinBound :=
        Finset.sum_le_sum hglobalBins
      _ = heights.card * globalBinBound := by simp
  calc
    (localPairs.image signature).card
        ≤ signatureUniverse.card :=
      Finset.card_le_card hsubset
    _ = heights.card * globalPairs.card := by
      rw [Finset.card_product]
    _ ≤ heights.card *
        (heights.card * globalBinBound) := by
      gcongr
    _ = heights.card ^ 2 * globalBinBound := by ring

end

private lemma finite_fiber_cauchy_schwarz
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (set : Finset α) (map : α → β) :
    set.card ^ 2 ≤
      (set.image map).card *
        ((set.product set).filter
          (fun pair : α × α =>
            map pair.1 = map pair.2)).card := by
  let image := set.image map
  let fiber : β → Finset α :=
    fun value => set.filter fun element => map element = value
  let collisions :=
    (set.product set).filter
      (fun pair : α × α => map pair.1 = map pair.2)
  have h_fiber_sum :
      set.card = ∑ value ∈ image, (fiber value).card :=
    Finset.card_eq_sum_card_image map set
  have h_disjoint :
      (image : Set β).PairwiseDisjoint
        (fun value => fiber value ×ˢ fiber value) := by
    intro first _ second _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro pair hfirst hsecond
    have h1 :
        map pair.1 = first :=
      (Finset.mem_filter.mp
        (Finset.mem_product.mp hfirst).1).2
    have h2 :
        map pair.1 = second :=
      (Finset.mem_filter.mp
        (Finset.mem_product.mp hsecond).1).2
    exact hne (h1.symm.trans h2)
  have h_collisions_eq :
      collisions =
        image.biUnion
          (fun value => fiber value ×ˢ fiber value) := by
    ext pair
    simp [collisions, fiber, Finset.mem_biUnion,
      Finset.mem_product, Finset.mem_filter]
    aesop
  have h_collisions_card :
      collisions.card =
        ∑ value ∈ image, (fiber value).card ^ 2 := by
    rw [h_collisions_eq, Finset.card_biUnion h_disjoint]
    apply Finset.sum_congr rfl
    intro value _
    rw [Finset.card_product, sq]
  have h_cauchy_schwarz :
      (set.card : ℤ) ^ 2 ≤
        (image.card : ℤ) *
          ∑ value ∈ image,
            ((fiber value).card : ℤ) ^ 2 := by
    have h :=
      sq_sum_le_card_mul_sum_sq
      (s := image)
      (f := fun value : β => ((fiber value).card : ℤ))
    have hsum :
        (∑ value ∈ image, ((fiber value).card : ℤ)) =
          (set.card : ℤ) := by
      rw [← Nat.cast_sum, h_fiber_sum]
    rw [hsum] at h
    exact h
  have h_main :
      (set.card : ℤ) ^ 2 ≤
        (image.card : ℤ) * (collisions.card : ℤ) := by
    rw [h_collisions_card] at *
    simpa [Nat.cast_sum, Nat.cast_pow] using h_cauchy_schwarz
  exact_mod_cast h_main

theorem wz1_lemma23_snapped_four_cycle_abundance :
    WZ1Lemma23SnappedFourCycleAbundanceStatement := by
  intro rho f g cells localBinBound globalBinBound
    hlocalBins hglobalBins
  classical
  let localKey := wz1Lemma23SnappedLocalKey rho g
  let height := wz1Lemma23SnappedHeight
  let globalBin := wz1Lemma23SnappedGlobalBin rho f
  let sameLocal := wz1Lemma23SameSnappedLocalGrain rho g
  let yLayers := wz1Lemma23SnappedYLayers cells
  let heights := wz1Lemma23SnappedHeights cells
  let localPairs := wz1Lemma23LocalPairs cells sameLocal
  let signature :=
    wz1Lemma23PairSignature height globalBin
  let fourCycles :=
    wz1Lemma23SnappedFourCycles rho f g cells
  have hlocalKey :
      (cells.image localKey).card ≤
        yLayers.card * localBinBound :=
    wz1_lemma23_snapped_local_key_image_bound
      rho g cells localBinBound hlocalBins
  let localCollisions :=
    (cells.product cells).filter
      (fun pair : (ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ) =>
        localKey pair.1 = localKey pair.2)
  have h_sameLocal_iff :
      ∀ a b : ℤ × ℤ × ℤ,
        localKey a = localKey b ↔ sameLocal a b := by
    intro a b
    dsimp only [localKey, sameLocal,
      wz1Lemma23SameSnappedLocalGrain]
    rfl
  have hlocalCollisions :
      localCollisions = localPairs := by
    ext pair
    have hiff :
        localKey pair.1 = localKey pair.2 ↔
          sameLocal pair.1 pair.2 :=
      h_sameLocal_iff pair.1 pair.2
    simp [localCollisions, localPairs,
      wz1Lemma23LocalPairs, Finset.mem_filter,
      Finset.mem_product, hiff]
  have hfirst :
      cells.card ^ 2 ≤
        (yLayers.card * localBinBound) *
          localPairs.card := by
    calc
      cells.card ^ 2
          ≤ (cells.image localKey).card *
              localCollisions.card :=
        finite_fiber_cauchy_schwarz cells localKey
      _ = (cells.image localKey).card *
          localPairs.card := by rw [hlocalCollisions]
      _ ≤ (yLayers.card * localBinBound) *
          localPairs.card := by gcongr
  have hsignature :
      (localPairs.image signature).card ≤
        heights.card ^ 2 * globalBinBound :=
    by
      simpa [localPairs, signature, heights,
        sameLocal, height, globalBin] using
        (wz1_lemma23_snapped_signature_image_bound
          rho f g cells globalBinBound hglobalBins)
  have h_fourCycles_eq :
      fourCycles =
        wz1Lemma23FourCycles cells sameLocal
          height globalBin := by
    simp [fourCycles, wz1Lemma23SnappedFourCycles]
    rfl
  have hcycles :
      localPairs.card ^ 2 ≤
        (heights.card ^ 2 * globalBinBound) *
          fourCycles.card := by
    have hmain :=
      wz1_lemma23_four_cycle_counting
        (Cube := ℤ × ℤ × ℤ)
        (Height := ℤ) (GlobalBin := ℤ)
        cells sameLocal height globalBin
        (heights.card ^ 2 * globalBinBound)
        hsignature
    rw [h_fourCycles_eq] at *
    exact hmain
  let localKeyBound := yLayers.card * localBinBound
  let signatureBound := heights.card ^ 2 * globalBinBound
  calc
    cells.card ^ 4 = (cells.card ^ 2) ^ 2 := by ring
    _ ≤ (localKeyBound * localPairs.card) ^ 2 := by
      gcongr
    _ = localKeyBound ^ 2 * localPairs.card ^ 2 := by ring
    _ ≤ localKeyBound ^ 2 *
        (signatureBound * fourCycles.card) := by
      gcongr
    _ = localKeyBound ^ 2 * signatureBound *
        fourCycles.card := by ring

end Kakeya.Assouad
