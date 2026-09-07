import MyLeanRepo.Kakeya.Assouad.WZ1.Statements

/-!
# WZ1 finite-scale Lipschitz assembly

Closed proof of WZ1 Lemma 15: assemble the finite list of one-scale plane-map
estimates into a global Lipschitz estimate.
-/

namespace Kakeya.Assouad

theorem wz1_finite_scale_lipschitz :
    WZ1FiniteScaleLipschitzStatement := by
  intro N hN s hs hsl E V hunit hconst honeScale
  set C : NNReal := Real.toNNReal (2 / s) with hC
  have hpos : 0 < 2 / s := by positivity
  have hnonneg : 0 ≤ 2 / s := by positivity
  have hcoe : (C : ℝ) = 2 / s := by
    simp [hC, Real.coe_toNNReal, hnonneg]
    <;> linarith
  have hmain : ∀ p ∈ E, ∀ q ∈ E, dist (V p) (V q) ≤ (C : ℝ) * dist p q := by
    intro p hp q hq
    set d := dist p q with hd
    have hgoal : dist (V p) (V q) ≤ (2 / s) * d := by
      by_cases h1 : d ≤ s ^ N
      · -- Case 1: d ≤ s^N, constancy gives V p = V q
        have heq : V p = V q := hconst p hp q hq h1
        rw [heq]
        simp [hd] <;> positivity
      · -- d > s^N
        have h1' : s ^ N < d := by linarith
        by_cases h2 : d ≤ s
        · -- Case 2: s^N < d ≤ s, find largest k < N with d ≤ s^k
          have hN2 : 2 ≤ N := by
            by_contra h
            have hlt : N < 2 := by linarith
            have hN1 : N = 1 := by omega
            rw [hN1] at h1' <;> linarith
          let S : Finset ℕ := Finset.filter (fun k => d ≤ s ^ k) (Finset.range N)
          have hS1 : 1 ∈ Finset.range N := by
            simp only [Finset.mem_range] <;> linarith
          have hS2 : d ≤ s ^ 1 := by simpa [pow_one] using h2
          have h1in : 1 ∈ S := by
            rw [Finset.mem_filter] <;> exact ⟨hS1, hS2⟩
          have hSnonempty : S.Nonempty := ⟨1, h1in⟩
          let k := S.max' hSnonempty
          have hkin : k ∈ S := Finset.max'_mem S hSnonempty
          have hkin' : k ∈ Finset.range N ∧ d ≤ s ^ k := by
            rwa [Finset.mem_filter] at hkin
          have hk_lt_N : k < N := Finset.mem_range.mp hkin'.1
          have hdk : d ≤ s ^ k := hkin'.2
          have hk_ge1 : 1 ≤ k := Finset.le_max' S 1 h1in
          have hdk1 : s ^ (k + 1) < d := by
            by_cases h : k + 1 < N
            · have hnot : k + 1 ∉ S := by
                intro hmem
                have hle : k + 1 ≤ k := Finset.le_max' S (k + 1) hmem
                linarith
              have hr : k + 1 ∈ Finset.range N := by
                simp only [Finset.mem_range] <;> linarith
              have hiff : (k + 1 ∈ S) ↔ d ≤ s ^ (k + 1) := by
                constructor
                · intro hmem
                  exact (Finset.mem_filter.mp hmem).2
                · intro hle
                  exact Finset.mem_filter.mpr ⟨hr, hle⟩
              have h' : ¬(d ≤ s ^ (k + 1)) := mt hiff.mpr hnot
              exact lt_of_not_ge h'
            · have hkN : k + 1 = N := by omega
              rw [hkN] <;> exact h1'
          have hsk : s ^ k < d / s := by
            have h : s ^ (k + 1) = s * s ^ k := by
              rw [pow_succ] <;> ring
            rw [h] at hdk1
            calc s ^ k
              = (s * s ^ k) / s := by field_simp [hs.ne'] <;> ring
            _ < d / s := by gcongr
          have hbound : dist (V p) (V q) ≤ 2 * s ^ k :=
            honeScale k hk_ge1 hk_lt_N p hp q hq hdk
          calc dist (V p) (V q)
            ≤ 2 * s ^ k := hbound
          _ ≤ 2 * (d / s) := by gcongr
          _ = (2 / s) * d := by ring
        · -- Case 3: d > s, unit norms give dist ≤ 2 < (2/s)*d
          have h2' : s < d := by linarith
          have h3 : dist (V p) (V q) ≤ ‖V p‖ + ‖V q‖ := by
            calc dist (V p) (V q)
              = ‖V p - V q‖ := by rw [dist_eq_norm]
            _ ≤ ‖V p‖ + ‖V q‖ := norm_sub_le (V p) (V q)
          have h4 : ‖V p‖ = 1 := hunit p hp
          have h5 : ‖V q‖ = 1 := hunit q hq
          have h6 : dist (V p) (V q) ≤ 2 := by
            calc dist (V p) (V q)
              ≤ ‖V p‖ + ‖V q‖ := h3
            _ = 1 + 1 := by rw [h4, h5]
            _ = 2 := by norm_num
          have h7 : (2 : ℝ) < (2 / s) * d := by
            have h8 : (2 / s) * s = 2 := by
              field_simp [hs.ne'] <;> ring
            nlinarith
          linarith
    rw [hcoe]
    exact hgoal
  have hfinal : ∀ (x : Point3), x ∈ E → ∀ (y : Point3), y ∈ E →
      edist (V x) (V y) ≤ (C : ENNReal) * edist x y := by
    intro x hx y hy
    have hdist : dist (V x) (V y) ≤ (C : ℝ) * dist x y := hmain x hx y hy
    have h1 : edist (V x) (V y) = ENNReal.ofReal (dist (V x) (V y)) :=
      edist_dist (V x) (V y)
    have h2 : edist x y = ENNReal.ofReal (dist x y) := edist_dist x y
    rw [h1, h2]
    have h3 : ENNReal.ofReal (dist (V x) (V y)) ≤ ENNReal.ofReal ((C : ℝ) * dist x y) :=
      ENNReal.ofReal_le_ofReal hdist
    have hCnonneg : 0 ≤ (C : ℝ) := by positivity
    have h41 : ENNReal.ofReal ((C : ℝ) * dist x y) =
        ENNReal.ofReal (C : ℝ) * ENNReal.ofReal (dist x y) :=
      ENNReal.ofReal_mul hCnonneg
    have h42 : ENNReal.ofReal (C : ℝ) = (C : ENNReal) := by
      simp
    rw [h41, h42] at h3
    exact h3
  simpa [LipschitzOnWith] using hfinal

end Kakeya.Assouad
