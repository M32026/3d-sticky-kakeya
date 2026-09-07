import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma23BaseCyclePigeonholeStatements

/-!
# Base-cycle key pigeonhole in WZ1 Lemma 23

Choose a largest fiber of the first-cube `(height, global-bin)` key.
-/

namespace Kakeya.Assouad

theorem wz1_lemma23_base_cycle_pigeonhole :
    WZ1Lemma23BaseCyclePigeonholeStatement := by
  dsimp only [WZ1Lemma23BaseCyclePigeonholeStatement]
  intro rho f g cells keyBound
  exact aux rho f g cells keyBound
where
  aux (rho : ℝ) (f g : ℝ → ℝ)
      (cells : Finset (ℤ × ℤ × ℤ)) (keyBound : ℕ)
      (h : ((wz1Lemma23SnappedFourCycles rho f g cells).image
              (wz1Lemma23BaseCycleKey rho f)).card ≤ keyBound) :
      ∃ baseHeightIndex baseGlobalBin : ℤ,
        keyBound * (wz1Lemma23SnappedBaseCycles rho f g cells
          baseHeightIndex baseGlobalBin).card ≥
          (wz1Lemma23SnappedFourCycles rho f g cells).card := by
    set cycles := wz1Lemma23SnappedFourCycles rho f g cells with hcycles
    set key := wz1Lemma23BaseCycleKey rho f with hkey
    set keys := cycles.image key with hkeys
    have h_keys : keys.card ≤ keyBound := h
    by_cases h_empty : cycles = ∅
    · rw [h_empty]
      refine ⟨0, 0, ?_⟩
      simp [wz1Lemma23SnappedBaseCycles]
    · have h_cycles_nonempty : cycles.Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr h_empty
      have h_keys_nonempty : keys.Nonempty := by
        exact Finset.image_nonempty.mpr h_cycles_nonempty
      have h_keyBound_pos : 0 < keyBound := by
        by_contra h'
        have h0 : keyBound = 0 := by omega
        rw [h0] at h_keys
        have hcard : keys.card = 0 := by omega
        have hempty : keys = ∅ := Finset.card_eq_zero.mp hcard
        exact Finset.Nonempty.ne_empty h_keys_nonempty hempty
      obtain ⟨k, hk, h_max⟩ :=
        Finset.exists_max_image keys
          (fun k : ℤ × ℤ =>
            (cycles.filter fun x => key x = k).card)
          h_keys_nonempty
      have h_sum :
          cycles.card =
            ∑ j ∈ keys,
              (cycles.filter fun x => key x = j).card := by
        exact Finset.card_eq_sum_card_image key cycles
      have h_ineq :
          cycles.card ≤
            keys.card *
              (cycles.filter fun x => key x = k).card := by
        rw [h_sum]
        calc
          ∑ j ∈ keys,
              (cycles.filter fun x => key x = j).card
              ≤ ∑ _j ∈ keys,
                  (cycles.filter fun x => key x = k).card :=
            Finset.sum_le_sum h_max
          _ = keys.card *
              (cycles.filter fun x => key x = k).card := by
            simp
      have h_key_eq : ∀ x, key x = k ↔
          wz1Lemma23SnappedHeight x.1 = k.1 ∧
          wz1Lemma23SnappedGlobalBin rho f x.1 = k.2 := by
        intro x
        have h_key_def :
            key x =
              (wz1Lemma23SnappedHeight x.1,
                wz1Lemma23SnappedGlobalBin rho f x.1) := by
          simp [key, wz1Lemma23BaseCycleKey]
        constructor
        · intro hkey
          have h1 : (key x).1 = k.1 := by rw [hkey]
          have h2 : (key x).2 = k.2 := by rw [hkey]
          rw [h_key_def] at h1 h2
          exact ⟨h1, h2⟩
        · rintro ⟨h1, h2⟩
          rw [h_key_def]
          exact Prod.ext h1 h2
      have h_fiber :
          wz1Lemma23SnappedBaseCycles rho f g cells k.1 k.2 =
            cycles.filter fun x => key x = k := by
        ext x
        simp only [wz1Lemma23SnappedBaseCycles, Finset.mem_filter]
        rw [h_key_eq x]
      refine ⟨k.1, k.2, ?_⟩
      rw [h_fiber]
      calc
        cycles.card ≤
            keys.card *
              (cycles.filter fun x => key x = k).card :=
          h_ineq
        _ ≤ keyBound *
              (cycles.filter fun x => key x = k).card := by
          gcongr

end Kakeya.Assouad
