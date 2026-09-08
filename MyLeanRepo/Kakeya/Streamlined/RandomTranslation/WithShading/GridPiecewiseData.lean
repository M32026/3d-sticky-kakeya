import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.WithShading.AllScalePiecewiseCover
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.DownwardEDMonotonicity

/-!
# Construct PiecewiseScaleData from a finite grid

Given a finite grid `σ_0 < σ_1 < ... < σ_N` covering `[δ, 1]`, with
K-strong ED coarse subfamilies and uniform covers at each grid scale,
construct `PiecewiseScaleData` for every admissible scale ρ.

For each ρ, find the bracket `σ_i ≤ ρ ≤ σ_{i+1}` and use the data at index i.
The downward-monotonicity K condition is inherited from a global bound at the
worst-case ratio `σ_{i+1}/σ_i`.

## Main results

- `GridScaleData`: per-grid input bundle.
- `build_piecewise_data`: produce `∀ ρ, PiecewiseScaleData`.
-/

noncomputable section

attribute [local instance] Classical.propDecidable

open MeasureTheory Finset Kakeya.Streamlined
open Kakeya.Streamlined.GeometricLemmas
open Kakeya.Streamlined.RandomTranslation.WithShading

namespace Kakeya.Streamlined.RandomTranslation.WithShading

/-- The volume-ratio constant `C_vol(A) = ((π + 8/3 π A) / 2) * A^2`. -/
def cVol (A : ℝ) : ℝ :=
  ((Real.pi + 8 / 3 * Real.pi * A) / 2) * A ^ 2

/-- `cVol` is strictly increasing on positive reals. -/
lemma cVol_strict_mono {A B : ℝ} (hA_pos : 0 < A) (h : A < B) :
    cVol A < cVol B := by
  dsimp only [cVol]
  have h1 : 0 < Real.pi + 8 / 3 * Real.pi * A := by positivity
  have h2 : Real.pi + 8 / 3 * Real.pi * A < Real.pi + 8 / 3 * Real.pi * B := by
    gcongr
  have h3 : A ^ 2 < B ^ 2 := by nlinarith
  have h4 : 0 < (Real.pi + 8 / 3 * Real.pi * A) / 2 := by positivity
  nlinarith [Real.pi_pos]

/-- Finite grid data for constructing piecewise scale data.

The grid has `N + 1` points `σ 0 < σ 1 < ... < σ N` with `σ 0 = δ`
and `σ N = 1`. For each index `i : Fin N`, we have a coarse subfamily
`R i` at scale `σ i` that is K-strong ED at `σ (i+1)`, plus a uniform
cover from `G` to `R i`.
-/
structure GridScaleData
    {δ : ℝ} (G : TubeFamily δ) (uniformity : ENNReal) (N : ℕ) where
  σ : Fin (N + 1) → AdmissibleScale δ
  hσ_mono : ∀ (i : Fin N), (σ (Fin.castSucc i)).1 < (σ (Fin.succ i)).1
  hσ_first : (σ 0).1 = δ
  hσ_last : (σ (Fin.last N)).1 = 1
  K : ENNReal
  hK_global : ∀ (i : Fin N),
    2 * ENNReal.ofReal (cVol ((σ (Fin.succ i)).1 / (σ (Fin.castSucc i)).1)) ≤ K
  R : ∀ (i : Fin N), TubeFamily (σ (Fin.castSucc i)).1
  R_strong_ed : ∀ (i : Fin N),
    ∀ j ∈ (Finset.univ : Finset (Fin (R i).card)),
      ∀ k ∈ (Finset.univ : Finset (Fin (R i).card)),
        j ≠ k →
          IsKStrongEssentiallyDistinct
            ((sameAxisEnlargedFamily (rho := (σ (Fin.succ i)).1) (R i)).tube j)
            ((sameAxisEnlargedFamily (rho := (σ (Fin.succ i)).1) (R i)).tube k)
            (Kakeya.deltaTubeVolume (σ (Fin.succ i)).1) K
  P : ∀ (i : Fin N), TubeCover G (R i)
  P_uniform :
    ∀ (i : Fin N),
      (P i).toFactoring.FibersAreCUniform uniformity
  C_K : ℝ
  hC_K_pos : 0 < C_K
  D : ∀ (i : Fin N), ℕ
  hD_eq : ∀ (i : Fin N),
    D i = Nat.ceil (C_K * ((σ (Fin.succ i)).1 / (σ (Fin.castSucc i)).1) ^ 4)

/-- Construct `PiecewiseScaleData` for every admissible scale from grid data.

For each ρ ∈ [δ,1], finds a bracketing grid interval [σ_i, σ_{i+1}] via
`Finset.max'`, then transfers the global K bound downward using monotonicity
of `cVol`. -/
def build_piecewise_data
    {δ : ℝ} (hδ : 0 < δ)
    {G : TubeFamily δ} {uniformity : ENNReal}
    {N : ℕ} (hN : 0 < N)
    (grid : GridScaleData G uniformity N) :
    ∀ (ρ : AdmissibleScale δ), PiecewiseScaleData G uniformity ρ := by
  intro ρ
  have hρ_in : δ ≤ ρ.1 ∧ ρ.1 ≤ 1 := ρ.2
  -- Find bracketing index i : Fin N such that σ(castSucc i) ≤ ρ ≤ σ(succ i)
  have h_exists : ∃ (i : Fin N),
      (grid.σ (Fin.castSucc i)).1 ≤ ρ.1 ∧
      ρ.1 ≤ (grid.σ (Fin.succ i)).1 := by
    let S : Finset (Fin (N + 1)) :=
      Finset.univ.filter fun k => (grid.σ k).1 ≤ ρ.1
    have h0_in : (0 : Fin (N + 1)) ∈ S := by
      have h : (grid.σ (0 : Fin (N + 1))).1 ≤ ρ.1 := by
        rw [grid.hσ_first]
        exact hρ_in.1
      simpa [S, Finset.mem_filter] using h
    have hS_nonempty : S.Nonempty := ⟨0, h0_in⟩
    let k_max : Fin (N + 1) := Finset.max' S hS_nonempty
    have hk_max_in : k_max ∈ S := Finset.max'_mem S hS_nonempty
    have hk_max_le : (grid.σ k_max).1 ≤ ρ.1 :=
      (Finset.mem_filter.mp hk_max_in).2
    by_cases h_case : k_max = Fin.last N
    · -- k_max = N, so ρ = 1; use i = N-1
      have hρ_eq_one : ρ.1 = 1 := by
        have h1 : (grid.σ (Fin.last N)).1 ≤ ρ.1 := by
          rw [h_case] at hk_max_le <;> exact hk_max_le
        have h2 : (grid.σ (Fin.last N)).1 = 1 := grid.hσ_last
        linarith [hρ_in.2]
      let i : Fin N := ⟨N - 1, by omega⟩
      have hsucc_eq : Fin.succ i = (Fin.last N) := by
        apply Fin.ext <;> simp [i, Fin.val_succ] <;> omega
      refine ⟨i, ?_⟩
      have h3 : (grid.σ (Fin.castSucc i)).1 ≤ ρ.1 := by
        have h4 : (grid.σ (Fin.castSucc i)).1 ≤
            (grid.σ (Fin.succ i)).1 :=
          (grid.hσ_mono i).le
        have h5 : (grid.σ (Fin.succ i)).1 = 1 := by
          rw [hsucc_eq] <;> exact grid.hσ_last
        rw [h5] at h4
        rw [hρ_eq_one] <;> exact h4
      have h6 : ρ.1 ≤ (grid.σ (Fin.succ i)).1 := by
        have h7 : (grid.σ (Fin.succ i)).1 = 1 := by
          rw [hsucc_eq] <;> exact grid.hσ_last
        rw [h7, hρ_eq_one]
      exact ⟨h3, h6⟩
    · -- k_max < N; use i = k_max cast to Fin N
      have hk_max_lt_N : k_max.val < N := by
        by_contra h
        have h' : k_max.val = N := by omega
        have h'' : k_max = Fin.last N := by
          apply Fin.ext
          rw [h'] <;> simp
        exact h_case h''
      let i : Fin N := ⟨k_max.val, hk_max_lt_N⟩
      let k_succ : Fin (N + 1) := ⟨k_max.val + 1, by omega⟩
      have hcast : Fin.castSucc i = k_max := by
        apply Fin.ext <;> simp [i]
      have hsucc : Fin.succ i = k_succ := by
        apply Fin.ext <;> simp [i, k_succ, Fin.val_succ] <;> omega
      have h1 : (grid.σ (Fin.castSucc i)).1 ≤ ρ.1 := by
        rw [hcast] <;> exact hk_max_le
      have hk_succ_in_univ : k_succ ∈ (Finset.univ : Finset (Fin (N + 1))) := by simp
      have h3 : k_succ ∉ S := by
        intro h4
        have h5 : k_max ≤ k_succ :=
          Fin.le_iff_val_le_val.mpr (Nat.le_succ k_max.val)
        have h6 : k_succ ≤ k_max := Finset.le_max' S k_succ h4
        have h7 : k_max = k_succ := le_antisymm h5 h6
        have h8 : k_max.val = k_succ.val := by rw [h7]
        simp [k_succ] at h8 <;> omega
      have h4 : ¬((grid.σ k_succ).1 ≤ ρ.1) := by
        simpa [S, Finset.mem_filter, hk_succ_in_univ] using h3
      have h5 : ρ.1 ≤ (grid.σ k_succ).1 := by linarith
      have h6 : ρ.1 ≤ (grid.σ (Fin.succ i)).1 := by
        rw [hsucc] <;> exact h5
      exact ⟨i, h1, h6⟩
  let i : Fin N := Classical.choose h_exists
  have h_bracket : (grid.σ (Fin.castSucc i)).1 ≤ ρ.1 ∧
      ρ.1 ≤ (grid.σ (Fin.succ i)).1 :=
    Classical.choose_spec h_exists
  have hσ_le_ρ := h_bracket.1
  have hρ_le_upper := h_bracket.2
  let σ_i := grid.σ (Fin.castSucc i)
  let σ_succ := grid.σ (Fin.succ i)
  have hσ_i_pos : 0 < σ_i.1 := by
    have h : δ ≤ σ_i.1 := σ_i.2.1
    exact lt_of_lt_of_le hδ h
  have hσ_succ_pos : 0 < σ_succ.1 := by
    have h : δ ≤ σ_succ.1 := σ_succ.2.1
    exact lt_of_lt_of_le hδ h
  have hρ_pos : 0 < ρ.1 := by linarith [ρ.2.1]
  -- Prove hK_downward for this specific ρ:
  -- since ρ ≥ σ_i, we have σ_succ/ρ ≤ σ_succ/σ_i,
  -- and cVol is increasing, so global K bound applies.
  have h_ratio_le : σ_succ.1 / ρ.1 ≤ σ_succ.1 / σ_i.1 := by
    gcongr
  have h_cVol_le : cVol (σ_succ.1 / ρ.1) ≤ cVol (σ_succ.1 / σ_i.1) := by
    by_cases h_strict : σ_succ.1 / ρ.1 < σ_succ.1 / σ_i.1
    · exact (cVol_strict_mono (by positivity) h_strict).le
    · have h_eq : σ_succ.1 / ρ.1 = σ_succ.1 / σ_i.1 := by linarith
      rw [h_eq]
  have hK_downward :
      2 * ENNReal.ofReal (cVol (σ_succ.1 / ρ.1)) ≤ grid.K := by
    have h_main : 2 * ENNReal.ofReal (cVol (σ_succ.1 / ρ.1)) ≤
        2 * ENNReal.ofReal (cVol (σ_succ.1 / σ_i.1)) := by
      gcongr
    exact h_main.trans (grid.hK_global i)
  exact {
    σ := σ_i
    σ_upper := σ_succ
    hσ_le_ρ := hσ_le_ρ
    hρ_le_upper := hρ_le_upper
    K := grid.K
    hK_downward := hK_downward
    C_K := grid.C_K
    hC_K_pos := grid.hC_K_pos
    D := grid.D i
    hD_eq := grid.hD_eq i
    R := grid.R i
    R_upper_strong_ed := grid.R_strong_ed i
    P := grid.P i
    P_uniform := grid.P_uniform i
  }

end Kakeya.Streamlined.RandomTranslation.WithShading

end
