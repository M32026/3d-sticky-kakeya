import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic

open scoped Pointwise

/-!
# 1D Brunn–Minkowski Inequality

The one-dimensional Brunn–Minkowski inequality: for nonempty measurable
sets `A, B ⊆ ℝ`, `volume(A + B) ≥ volume A + volume B`.

## Proof

1. **Compact sets**: If `K, L` are compact and nonempty, let `m = sInf L`
   and `M = sSup K`. Then `K + {m}` and `{M} + L` are subsets of `K + L`,
   separated by `M + m`. Their intersection is at most `{M + m}`, measure zero.
   Hence `volume(K + L) ≥ volume(K) + volume(L)`.

2. **Measurable sets**: By inner regularity, approximate from inside by
   compact sets. Add a singleton to guarantee nonempty approximants.

## Whiteprint

This module is a sub-node of `brunn_minkowski`.
-/

namespace Geometry

open MeasureTheory ENNReal Metric Set

/-- Volume is invariant under translation. -/
private lemma volume_translate (c : ℝ) {s : Set ℝ} (hs : MeasurableSet s) :
    volume ((fun x : ℝ => x + c) '' s) = volume s := by
  let g : ℝ → ℝ := fun x => -c + x
  have hmp : MeasurePreserving g volume volume := measurePreserving_add_left volume (-c)
  have h_eq : g ⁻¹' s = (fun x : ℝ => x + c) '' s := by
    ext y
    simp only [g, mem_preimage, mem_image]
    constructor
    · intro hy
      refine ⟨-c + y, hy, ?_⟩
      <;> ring
    · rintro ⟨k, hk, rfl⟩
      simpa using hk
  rw [←h_eq]
  exact hmp.measure_preimage hs.nullMeasurableSet

/-! ### Compact case -/

/-- **1D Brunn–Minkowski for compact sets.** -/
lemma brunnMinkowski_oneDim_compact {K L : Set ℝ}
    (hK : IsCompact K) (hL : IsCompact L)
    (hKne : K.Nonempty) (hLne : L.Nonempty) :
    volume (K + L) ≥ volume K + volume L := by
  let M : ℝ := sSup K
  let m : ℝ := sInf L
  have hM_in : M ∈ K := hK.sSup_mem hKne
  have hm_in : m ∈ L := hL.sInf_mem hLne
  have hK_above : BddAbove K := hK.bddAbove
  have hL_below : BddBelow L := hL.bddBelow
  have hM_max : ∀ x ∈ K, x ≤ M := fun x hx => le_csSup hK_above hx
  have hm_min : ∀ y ∈ L, m ≤ y := fun y hy => csInf_le hL_below hy

  let S1 : Set ℝ := (fun k : ℝ => k + m) '' K
  let S2 : Set ℝ := (fun l : ℝ => l + M) '' L

  have hS1_sub : S1 ⊆ K + L := by
    intro z hz
    rcases hz with ⟨k, hk, rfl⟩
    exact ⟨k, hk, m, hm_in, rfl⟩

  have hS2_sub : S2 ⊆ K + L := by
    intro z hz
    rcases hz with ⟨l, hl, rfl⟩
    exact ⟨M, hM_in, l, hl, by simp [add_comm]⟩

  have h_inter : S1 ∩ S2 ⊆ {M + m} := by
    intro z hz
    have h1 : z ≤ M + m := by
      rcases hz.1 with ⟨k, hk, rfl⟩; linarith [hM_max k hk]
    have h2 : M + m ≤ z := by
      rcases hz.2 with ⟨l, hl, rfl⟩; linarith [hm_min l hl]
    have h3 : z = M + m := by linarith
    exact h3

  have hS1_meas : MeasurableSet S1 :=
    (hK.image (continuous_id.add continuous_const)).measurableSet
  have hS2_meas : MeasurableSet S2 :=
    (hL.image (continuous_id.add continuous_const)).measurableSet

  have h_vol_inter : volume (S1 ∩ S2) = 0 := by
    have h : volume (S1 ∩ S2) ≤ volume ({M + m} : Set ℝ) := measure_mono h_inter
    simpa using h

  have h_eq : volume (S1 ∪ S2) + volume (S1 ∩ S2) = volume S1 + volume S2 :=
    measure_union_add_inter S1 hS2_meas
  have h_vol_union : volume (S1 ∪ S2) = volume S1 + volume S2 := by
    rw [h_vol_inter] at h_eq
    simpa using h_eq

  have h_vol_S1 : volume S1 = volume K := volume_translate m hK.measurableSet
  have h_vol_S2 : volume S2 = volume L := volume_translate M hL.measurableSet

  have h_main : volume (K + L) ≥ volume (S1 ∪ S2) :=
    measure_mono (union_subset hS1_sub hS2_sub)

  rw [h_vol_union, h_vol_S1, h_vol_S2] at h_main
  exact h_main

/-! ### Extension to measurable sets -/

/-- If A has measure zero and is nonempty, BM follows from translation. -/
private lemma bm_zero_left {A B : Set ℝ} (hAne : A.Nonempty)
    (hB : MeasurableSet B) (hvol : volume A = 0) :
    volume (A + B) ≥ volume A + volume B := by
  rcases hAne with ⟨a, ha⟩
  let S : Set ℝ := (fun l : ℝ => l + a) '' B
  have hS_sub : S ⊆ A + B := by
    intro z hz
    rcases hz with ⟨l, hl, rfl⟩
    exact ⟨a, ha, l, hl, by simp [add_comm]⟩
  have h_vol_S : volume S = volume B := volume_translate a hB
  have h : volume (A + B) ≥ volume S := measure_mono hS_sub
  rw [h_vol_S] at h
  rw [hvol] <;> simpa using h

/-- **1D Brunn–Minkowski inequality.** For nonempty measurable sets
`A, B ⊆ ℝ`, `volume(A + B) ≥ volume A + volume B`. -/
theorem brunnMinkowski_oneDim (A B : Set ℝ)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAne : A.Nonempty) (hBne : B.Nonempty) :
    volume (A + B) ≥ volume A + volume B := by
  -- Zero measure cases
  by_cases hA0 : volume A = 0
  · exact bm_zero_left hAne hB hA0
  by_cases hB0 : volume B = 0
  · -- Symmetric: B has measure zero
    rcases hBne with ⟨b, hb⟩
    let S : Set ℝ := (fun k : ℝ => k + b) '' A
    have hS_sub : S ⊆ A + B := by
      intro z hz
      rcases hz with ⟨k, hk, rfl⟩
      exact ⟨k, hk, b, hb, rfl⟩
    have h_vol_S : volume S = volume A := volume_translate b hA
    have h : volume (A + B) ≥ volume S := measure_mono hS_sub
    rw [h_vol_S] at h
    rw [hB0] <;> simpa using h

  -- Infinite measure cases
  by_cases hAinf : volume A = ⊤
  · rcases hBne with ⟨b, hb⟩
    let S : Set ℝ := (fun k : ℝ => k + b) '' A
    have hS_sub : S ⊆ A + B := by
      intro z hz
      rcases hz with ⟨k, hk, rfl⟩
      exact ⟨k, hk, b, hb, rfl⟩
    have h_vol_S : volume S = volume A := volume_translate b hA
    have h : volume (A + B) ≥ volume S := measure_mono hS_sub
    rw [h_vol_S, hAinf] at h
    have h' : volume (A + B) = ⊤ := top_le_iff.mp h
    rw [h', hAinf] <;> simp
  by_cases hBinf : volume B = ⊤
  · rcases hAne with ⟨a, ha⟩
    let S : Set ℝ := (fun l : ℝ => l + a) '' B
    have hS_sub : S ⊆ A + B := by
      intro z hz
      rcases hz with ⟨l, hl, rfl⟩
      exact ⟨a, ha, l, hl, by simp [add_comm]⟩
    have h_vol_S : volume S = volume B := volume_translate a hB
    have h : volume (A + B) ≥ volume S := measure_mono hS_sub
    rw [h_vol_S, hBinf] at h
    have h' : volume (A + B) = ⊤ := top_le_iff.mp h
    rw [h', hBinf] <;> simp

  -- Both positive and finite
  have hApos : 0 < volume A := Ne.bot_lt hA0
  have hBpos : 0 < volume B := Ne.bot_lt hB0
  have hAfin : volume A ≠ ⊤ := hAinf
  have hBfin : volume B ≠ ⊤ := hBinf

  rcases hAne with ⟨a, ha⟩
  rcases hBne with ⟨b, hb⟩

  have h_forall_eps : ∀ (ε : ENNReal), ε ≠ 0 →
      volume A + volume B < volume (A + B) + 2 * ε := by
    intro ε hε
    have h_app_A : ∃ K, K ⊆ A ∧ IsCompact K ∧ volume A < volume K + ε :=
      hA.exists_isCompact_lt_add hAfin hε
    have h_app_B : ∃ L, L ⊆ B ∧ IsCompact L ∧ volume B < volume L + ε :=
      hB.exists_isCompact_lt_add hBfin hε
    rcases h_app_A with ⟨K, hK_sub, hK_cmp, hKA_lt⟩
    rcases h_app_B with ⟨L, hL_sub, hL_cmp, hLB_lt⟩

    let K' := K ∪ {a}
    let L' := L ∪ {b}
    have hK'_sub : K' ⊆ A := by
      intro x hx
      simp only [K', mem_union, mem_singleton_iff] at hx
      rcases hx with (hx | rfl) <;> tauto
    have hL'_sub : L' ⊆ B := by
      intro x hx
      simp only [L', mem_union, mem_singleton_iff] at hx
      rcases hx with (hx | rfl) <;> tauto
    have hK'_cmp : IsCompact K' := hK_cmp.union isCompact_singleton
    have hL'_cmp : IsCompact L' := hL_cmp.union isCompact_singleton
    have hK'_ne : K'.Nonempty := ⟨a, by simp [K']⟩
    have hL'_ne : L'.Nonempty := ⟨b, by simp [L']⟩
    have hK_vol : volume K ≤ volume K' := by
      have h : K ⊆ K' := by simp [K']
      exact measure_mono h
    have hL_vol : volume L ≤ volume L' := by
      have h : L ⊆ L' := by simp [L']
      exact measure_mono h
    have hKA_lt' : volume A < volume K' + ε := by
      calc volume A < volume K + ε := hKA_lt
           _ ≤ volume K' + ε := by gcongr
    have hLB_lt' : volume B < volume L' + ε := by
      calc volume B < volume L + ε := hLB_lt
           _ ≤ volume L' + ε := by gcongr

    have h_sum_sub : K' + L' ⊆ A + B := image2_subset hK'_sub hL'_sub
    have h_bm : volume (K' + L') ≥ volume K' + volume L' :=
      brunnMinkowski_oneDim_compact hK'_cmp hL'_cmp hK'_ne hL'_ne
    have h1 : volume (A + B) ≥ volume K' + volume L' :=
      le_trans h_bm (measure_mono h_sum_sub)

    calc volume A + volume B
      < (volume K' + ε) + (volume L' + ε) := by gcongr <;> linarith
    _ = volume K' + volume L' + 2 * ε := by ring
    _ ≤ volume (A + B) + 2 * ε := by gcongr

  by_cases h_top : volume (A + B) = ⊤
  · rw [h_top] <;> simp
  · have h_contra : volume A + volume B ≤ volume (A + B) := by
      by_contra h
      have h_lt : volume (A + B) < volume A + volume B := lt_of_not_ge h
      have h_exists : ∃ (r : NNReal), 0 < r ∧
          volume (A + B) + (r : ENNReal) < volume A + volume B :=
        ENNReal.lt_iff_exists_add_pos_lt.mp h_lt
      rcases h_exists with ⟨r, hr_pos, hr_lt⟩
      let ε : ENNReal := (r / 2 : NNReal)
      have hε_ne : ε ≠ 0 := by
        simp [ε, hr_pos.ne'] <;> omega
      have h2ε : 2 * ε = (r : ENNReal) := by
        simp [ε, two_mul] <;> norm_cast <;> ring
      have h_contra2 : volume (A + B) + 2 * ε < volume A + volume B := by
        rw [h2ε]; exact hr_lt
      have h3 := h_forall_eps ε hε_ne
      exact False.elim (not_le.mpr h_contra2 h3.le)
    exact h_contra

end Geometry
