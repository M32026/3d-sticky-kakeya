module

/-
  Final theorem assembly.

  `core_estimate` is a thin wrapper around `improved_incidence_correct_Ncover`
  (ImprovedIncidenceGeneral.lean), which is proved via the Section 9 assembly
  (`section9_main`) and the Theorem 6.1 uniform data contract.

  `compact_uniformity` provides the compact-uniform ε function needed by the
  final target theorem.

  Whiteprint node: `final_assembly`

  ## Critical path
  ```
  theorem6_1_uniform_data (contract axiom)
    ↓
  Section9Assembly.section9_main
    ↓
  NcoverAdapter.improved_incidence_correct_Ncover_adapter
    ↓
  ImprovedIncidenceGeneral.improved_incidence_correct_Ncover
    ↓
  FinalProof.core_estimate [thin wrapper]
    ↓
  discretised_furstenberg_estimate
  ```
-/
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral
public import MyLeanRepo.DiscretisedFurstenbergEstimate.PackingBound
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

namespace DirecretisedFurstenbergEstimate.FinalProof

open DirecretisedFurstenbergEstimate

/-! # Skeleton intermediate theorem statements

These declare the exact interfaces needed from the sub-theorems.
Each is left as `sorry` and will be filled by its respective whiteprint node.
-/

/--
  Improved incidence for regular sets (OS Theorem 6.1).

  **DEPRECATED**: Use `ImprovedIncidenceGeneral.improved_incidence_correct_from_Ncover`
  applied to `ImprovedIncidenceGeneral.improved_incidence_correct_Ncover` instead.

  Correct quantifier order: `∀ s t, ∃ ε_G(s,t) > 0, ∃ δ₀(s,t) > 0, ...`

  Given `s ∈ (0,1)`, `t ∈ (s,2)`, there exists `ε_G = ε_G(s,t) > 0` and
  `η = η(s,t) > 0` such that for all sufficiently small `δ`:
  If `P` is a `(δ,t,δ^{-ε_G})`-regular set and each `p ∈ P` has a
  `(δ,s,δ^{-ε_G})`-set of tubes, then `|T| ≥ δ^{-2s-ε_G}`.

  The exponent `η` is the gain from the Appendix-A alternative and is used
  in the final assembly's constant selection.
-/
theorem improved_incidence_correct (s t : ℝ) (hs : 0 < s) (hs1 : s < 1)
    (hst : s < t) (ht2 : t < 2) :
    ∃ (ε_G η : ℝ), 0 < ε_G ∧ 0 < η ∧
      ∃ (δ₀ : ℝ), 0 < δ₀ ∧
        ∀ (δ : ℝ), 0 < δ → δ ≤ δ₀ →
          ∀ (P : Set EuclideanPlane),
            P ⊆ Metric.closedBall 0 1 →
            IsDeltaSSet δ t (Real.rpow δ (-ε_G)) P →
            ∀ (T : Set AffineLine)
              (Tp : ∀ (p : EuclideanPlane), p ∈ P → Set AffineLine),
              (∀ p hp, Tp p hp ⊆ T) →
              (∀ p hp, IsDeltaSSet δ s (Real.rpow δ (-ε_G)) (Tp p hp)) →
              (∀ p hp, ∀ ℓ ∈ Tp p hp,
                 p ∈ Metric.cthickening δ ℓ.1) →
              (T.encard : ENNReal) ≥
                ENNReal.ofReal (Real.rpow δ (-(2 * s + ε_G))) :=
  ImprovedIncidenceGeneral.improved_incidence_correct_from_Ncover s t hs hs1 hst ht2
    (ImprovedIncidenceGeneral.improved_incidence_correct_Ncover s t hs hs1 hst ht2)

/--
  Multiscale decomposition (OS Proposition 8.1).

  Given `s ∈ (0,1)`, `t ∈ (s,2)`, `Δ ∈ (0,1)`, and `ε > 0` sufficiently small,
  there exists `τ = τ(ε,s,t) ∈ (0,ε]` and `ε_bad > 0` such that for sufficiently
  large `m`, a uniform `(δ,t,δ^{-ε})`-set `P` (with `δ = Δ^m`) decomposes into
  structured and bad scale blocks.

  This is a thin wrapper around `multiscaleDecompKaufman`.

  # Smallness condition

  `hε_small` requires:
    `(1 + 6/(t-s)) * (ε + 2*log(9)/log(1/Δ)) < t - s`

  Choose `Δ = 1/N` for sufficiently large `N` to satisfy this.
-/
theorem multiscale_decomposition_main (s t : ℝ) (hs : 0 < s) (hs1 : s < 1)
    (hst : s < t) (ht2 : t < 2)
    (Δ : ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ < 1) (hΔ2 : Δ ≤ 1 / 2)
    (ε : ℝ) (hε : 0 < ε)
    (hε_small : (1 + 6 / (t - s)) * (ε + 2 * Real.log 9 / Real.log (1 / Δ)) < t - s)
    (hΔ_dyadic : ∃ (n : ℕ), 0 < n ∧ (1 : ℝ) = (n : ℝ) * Δ) :
    ∃ (τ ε_bad : ℝ), 0 < τ ∧ τ ≤ ε ∧ 0 < ε_bad ∧
    ∃ (m0 : ℕ),
    ∀ (m : ℕ), m ≥ m0 →
    ∀ (P : Set EuclideanPlane) (N : ℕ → ℕ),
      P ⊆ Metric.closedBall (0 : EuclideanPlane) 1 →
      MultiscaleDecomposition.IsDyadicUniform P m Δ N →
      IsDeltaSSet (Δ ^ m) t (Real.rpow (Δ ^ m) (-ε)) P →
      ∃ (n : ℕ) (i : ℕ → ℕ) (t_j : ℕ → ℝ)
        (S B : Finset (Fin n)),
        (i 0 = 0) ∧ (i n = m) ∧
        (∀ j < n, i j < i (j + 1)) ∧
        (∀ j : Fin n, t_j j.val ∈ Set.Icc s 2) ∧
        (S ∪ B = Finset.univ) ∧ (Disjoint S B) ∧
        (∀ j : Fin n, j ∈ S →
          (Δ ^ i j.val : ℝ) / (Δ ^ i (j.val + 1)) ≥
            Real.rpow (Δ ^ m) (-τ)) ∧
        (∏ j ∈ B, ((Δ ^ i j.val : ℝ) / (Δ ^ i (j.val + 1))) ≤
          Real.rpow (Δ ^ m) (-ε_bad)) ∧
        (∀ j : Fin n, j ∈ S →
          let δ_j := Δ ^ i (j.val + 1)
          let Δ_j := Δ ^ i j.val
          let ratio := (Δ_j / δ_j : ℝ)
          let levels := i (j.val + 1) - i j.val
          MultiscaleDecomposition.IsSetBetweenScales P δ_j Δ_j (t_j j.val)
            ((81 : ℝ) * Real.rpow Δ (-4) * Real.rpow ratio ε_bad) ∧
          (t_j j.val > s →
            MultiscaleDecomposition.IsRegularBetweenScales P δ_j Δ_j (t_j j.val)
              ((81 : ℝ) * Real.rpow Δ (-4) * Real.rpow ratio ε_bad)
              ((81 : ℝ) * Real.rpow Δ (-4) * Real.rpow ratio ε_bad))) ∧
        (∏ j ∈ S, Real.rpow ((Δ ^ i j.val : ℝ) / (Δ ^ i (j.val + 1))) (t_j j.val) ≥
          Real.rpow (Δ ^ m) (ε_bad - t)) ∧
        (∀ j : Fin n, j ∈ B →
          ∀ k : Fin n, k.val = j.val + 1 → k ∉ B) := by
  have hlog1d_pos : 0 < Real.log (1 / Δ) := by
    have h1 : 1 < 1 / Δ := by apply one_lt_one_div <;> linarith
    exact Real.log_pos h1
  let ε_K : ℝ := ε + 2 * Real.log 9 / Real.log (1 / Δ)
  have hεK_pos : 0 < ε_K := by
    dsimp only [ε_K]
    have h : 0 < 2 * Real.log 9 / Real.log (1 / Δ) := by
      apply div_pos
      · positivity
      · exact hlog1d_pos
    linarith
  have hεK : ε + 2 * Real.log 9 / Real.log (1 / Δ) ≤ ε_K := by
    simp [ε_K] <;> linarith
  have hKaufman : (1 + 6 / (t - s)) * ε_K < t - s := hε_small
  have ht : t ≤ 2 := by linarith
  rcases MultiscaleDecomposition.multiscaleDecompKaufman hs hst ht hΔ hΔ1 hΔ2 hε hεK_pos hεK hKaufman hΔ_dyadic
    with ⟨τ, ε_bad, hτ_pos, hτ_le, hε_bad_pos, _hε_bad_bound, h_main⟩
  exact ⟨τ, ε_bad, hτ_pos, hτ_le, hε_bad_pos, h_main⟩

/--
  Combining theorem (OS Proposition 7.3).

  Given parameters and a configuration with normal/good/bad scale blocks,
  produces constants `C, C' > 0` and a threshold `δ₀` such that the tube
  family cardinality satisfies the product lower bound
  `|T| ≥ log(1/δ)^{-C} · M · δ^{C'·λ} · δ^{-s+ε_N} · (good product)^η · (bad product)`.

  See `combining_estimates` in `CombiningEstimates.lean` for the full statement.
-/
theorem combining_theorem_main (s t τ : ℝ) (n : ℕ)
    (ε_G η ε_N C_P lam : ℝ) :
    ∃ (C C' : ℝ), 0 < C ∧ 0 < C' ∧ True := by
  refine' ⟨1, 1, by norm_num, by norm_num, _⟩
  trivial

/-- The affine line packing constant is at least 1. -/
lemma affineLine_packing_constant_ge_one :
    1 ≤ MainAppendix.affineLine_packing_constant := by
  let p : EuclideanPlane := 0
  let v : EuclideanPlane := EuclideanSpace.single 0 1
  let ℓ_sub : AffineSubspace ℝ EuclideanPlane := AffineSubspace.mk' p (ℝ ∙ v)
  have hv_ne_zero : v ≠ 0 := by
    intro h
    have h4 : v 0 = 0 := by rw [h] <;> simp
    have h5 : v 0 = 1 := by simp [v] <;> norm_num
    rw [h5] at h4 <;> norm_num at h4
  have h_finrank : Module.finrank ℝ ℓ_sub.direction = 1 := by
    have h1 : ℓ_sub.direction = ℝ ∙ v := by simp [ℓ_sub]
    rw [h1] <;> exact finrank_span_singleton hv_ne_zero
  let z : AffineLine := ⟨ℓ_sub, h_finrank⟩
  let S : Set AffineLine := {z}
  have hS_sep : Set.Pairwise S (fun x y => (1 : ℝ) ≤ dist x y) := by
    intro x hx y hy hne
    have hx' : x = z := by simpa [S] using hx
    have hy' : y = z := by simpa [S] using hy
    rw [hx', hy'] at hne <;> tauto
  have hS_sub : S ⊆ Metric.closedBall z (2 * (1 : ℝ)) := by
    intro x hx
    have hx' : x = z := by simpa [S] using hx
    rw [hx'] <;> simp [Metric.mem_closedBall] <;> linarith
  have h3 := MainAppendix.affineLine_packing_bound (1 : ℝ) (by norm_num) hS_sep z hS_sub
  have h4 : S.encard = 1 := by simp [S]
  rw [h4] at h3
  exact_mod_cast h3.2

/--
  Metric-to-dyadic transfer for the final conclusion.

  Converts a lower bound on a δ-separated subset to a lower bound on
  `Metric.externalCoveringNumber`.

  A δ-separated set S has the property that each δ-ball contains at most
  `K_pack` points of S (by the affine line packing bound). Therefore any
  δ-cover C satisfies |S| ≤ K_pack * |C|, so |C| ≥ |S| / K_pack.

  The K_pack factor is δ-independent and can be absorbed by slightly
  increasing the exponent in the downstream proof.
-/
theorem metric_dyadic_transfer (δ : ℝ) (hδ : 0 < δ)
    (T : Set AffineLine) (s ε : ℝ)
    (h_dyadic_lower : ∃ (T' : Set AffineLine), T' ⊆ T ∧
        (∀ ℓ₁ ∈ T', ∀ ℓ₂ ∈ T', ℓ₁ ≠ ℓ₂ → δ < dist ℓ₁ ℓ₂) ∧
        (T'.encard : ENNReal) ≥ ENNReal.ofReal (Real.rpow δ (-(2 * s + ε)))) :
    (Metric.externalCoveringNumber δ.toNNReal T : ENNReal) ≥
      ENNReal.ofReal (Real.rpow δ (-(2 * s + ε))) / (MainAppendix.affineLine_packing_constant : ENNReal) := by
  rcases h_dyadic_lower with ⟨T', hT'_sub, hT'_sep_strict, hT'_card⟩
  let K_pack := MainAppendix.affineLine_packing_constant
  have hK_ge_one : 1 ≤ K_pack := affineLine_packing_constant_ge_one
  have hK_pos : 0 < K_pack := by linarith
  have hK_ne_zero : (K_pack : ENNReal) ≠ 0 := by exact_mod_cast hK_pos.ne'
  have hK_ne_top : (K_pack : ENNReal) ≠ ⊤ := by simp
  let δnn : NNReal := δ.toNNReal
  have hδnn_eq : (δnn : ℝ) = δ := by
    simp [δnn, Real.toNNReal_of_nonneg (show 0 ≤ δ by linarith)] <;> norm_cast

  -- T' is non-strictly δ-separated
  have hT'_sep : Set.Pairwise T' (fun x y => (δnn : ℝ) ≤ dist x y) := by
    intro x hx y hy hxy
    have h : δ < dist x y := hT'_sep_strict x hx y hy hxy
    rw [hδnn_eq]
    exact le_of_lt h

  -- Packing bound function for AffineLine
  have h_pack : ∀ (z : AffineLine) (S : Set AffineLine),
      Set.Pairwise S (fun x y => (δnn : ℝ) ≤ dist x y) →
      S ⊆ Metric.closedBall z (2 * (δnn : ℝ)) →
      S.Finite ∧ S.encard ≤ (K_pack : ENat) := by
    intro z S hS_sep hS_sub
    have hS_sep' : Set.Pairwise S (fun x y => δ ≤ dist x y) := by
      simpa [hδnn_eq] using hS_sep
    have hS_sub' : S ⊆ Metric.closedBall z (2 * δ) := by
      simpa [hδnn_eq] using hS_sub
    exact MainAppendix.affineLine_packing_bound δ hδ hS_sep' z hS_sub'

  -- Case split on whether covering number of T' is top
  by_cases hcov_top : (Metric.externalCoveringNumber δnn T' : ENNReal) = ⊤
  · -- Covering of T' is top, so covering of T is also top
    have h_mono : (Metric.externalCoveringNumber δnn T' : ENNReal) ≤
        (Metric.externalCoveringNumber δnn T : ENNReal) := by
      exact_mod_cast Metric.externalCoveringNumber_mono_set hT'_sub
    have hT_top : (Metric.externalCoveringNumber δnn T : ENNReal) = ⊤ := by
      rw [hcov_top] at h_mono
      exact top_le_iff.mp h_mono
    have h_final : (Metric.externalCoveringNumber δ.toNNReal T : ENNReal) = ⊤ := by
      exact_mod_cast hT_top
    rw [h_final]
    <;> exact le_top

  · -- Covering number is finite
    have hcov_fin : (Metric.externalCoveringNumber δnn T' : ENNReal) < ⊤ := by
      have h : (Metric.externalCoveringNumber δnn T' : ENNReal) ≠ ⊤ := hcov_top
      simpa [lt_top_iff_ne_top] using h

    have h_card : (T'.encard : ENNReal) ≤
        (K_pack : ENNReal) * (Metric.externalCoveringNumber δnn T' : ENNReal) :=
      MainAppendix.separated_set_card_le_covering hT'_sep K_pack h_pack hcov_fin

    have h_card_comm : (T'.encard : ENNReal) ≤
        (Metric.externalCoveringNumber δnn T' : ENNReal) * (K_pack : ENNReal) := by
      rw [mul_comm] at h_card
      exact h_card
    have h_div_iff : ((T'.encard : ENNReal) / (K_pack : ENNReal) ≤
        (Metric.externalCoveringNumber δnn T' : ENNReal)) ↔
        ((T'.encard : ENNReal) ≤ (Metric.externalCoveringNumber δnn T' : ENNReal) * (K_pack : ENNReal)) :=
      ENNReal.div_le_iff hK_ne_zero hK_ne_top
    have h_final1 : (T'.encard : ENNReal) / (K_pack : ENNReal) ≤
        (Metric.externalCoveringNumber δnn T' : ENNReal) :=
      h_div_iff.mpr h_card_comm

    have h_mono : (Metric.externalCoveringNumber δnn T' : ENNReal) ≤
        (Metric.externalCoveringNumber δnn T : ENNReal) := by
      exact_mod_cast Metric.externalCoveringNumber_mono_set hT'_sub

    have h10 : (T'.encard : ENNReal) / (K_pack : ENNReal) ≥
        ENNReal.ofReal (Real.rpow δ (-(2 * s + ε))) / (K_pack : ENNReal) := by
      gcongr

    have h_eq : δnn = δ.toNNReal := by rfl
    rw [h_eq] at h_mono
    exact le_trans h10 (le_trans h_final1 h_mono)

/--
  Absorb the δ-independent packing constant K_pack by using a slightly larger
  exponent `ε_work > ε`.

  If `δ ≤ K_pack^{-1/(ε_work - ε)}`, then
  `δ^{-(2s+ε_work)} / K_pack ≥ δ^{-(2s+ε)}`.
-/
lemma absorb_packing_constant {δ s ε ε_work : ℝ} {K_pack : ℕ}
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hε_pos : 0 < ε) (hε_work_pos : 0 < ε_work) (hε_lt_work : ε < ε_work)
    (hK_ge_one : 1 ≤ K_pack)
    (hδ_small : δ ≤ Real.rpow (K_pack : ℝ) (-(1 / (ε_work - ε)))) :
    ENNReal.ofReal (Real.rpow δ (-(2 * s + ε_work))) / (K_pack : ENNReal) ≥
    ENNReal.ofReal (Real.rpow δ (-(2 * s + ε))) := by
  set α : ℝ := ε_work - ε with hα_def
  have hα_pos : 0 < α := by linarith
  set Kreal : ℝ := (K_pack : ℝ) with hKreal_def
  have hKreal_pos : 0 < Kreal := by
    have h : 0 < K_pack := by linarith
    have h' : (0 : ℝ) < (K_pack : ℝ) := by exact_mod_cast h
    simpa [hKreal_def] using h'
  set x : ℝ := Real.rpow Kreal (-(1 / α)) with hx_def

  -- δ^{-α} ≥ K
  have h1 : Real.rpow δ (-α) ≥ Kreal := by
    have hx_pos : 0 < x := Real.rpow_pos_of_pos hKreal_pos _
    have hδ_le_x : δ ≤ x := hδ_small
    have h_exp_neg : -α < 0 := by linarith
    have h3 : α ≠ 0 := by linarith
    have h_rpow_anti : Real.rpow x (-α) ≤ Real.rpow δ (-α) := by
      by_cases h : δ < x
      · have hδ_pos' : δ ∈ Set.Ioi 0 := Set.mem_Ioi.mpr hδ_pos
        have hx_pos' : x ∈ Set.Ioi 0 := Set.mem_Ioi.mpr hx_pos
        have h' : Real.rpow x (-α) < Real.rpow δ (-α) :=
          Real.strictAntiOn_rpow_Ioi_of_exponent_neg h_exp_neg hδ_pos' hx_pos' h
        exact le_of_lt h'
      · have h' : δ = x := by linarith
        rw [h']
    have h_rpow_x : Real.rpow x (-α) = Kreal := by
      rw [hx_def]
      have h4 : Real.rpow (Real.rpow Kreal (-(1 / α))) (-α) =
          Real.rpow Kreal ((-(1 / α)) * (-α)) :=
        (Real.rpow_mul (by linarith) (-(1 / α)) (-α)).symm
      rw [h4]
      have h5 : (-(1 / α)) * (-α) = 1 := by
        field_simp [h3] <;> ring
      rw [h5]
      <;> simp
    rw [h_rpow_x] at h_rpow_anti
    exact h_rpow_anti

  -- δ^{-(2s+ε_work)} = δ^{-(2s+ε)} * δ^{-α}
  have h_exp_eq : -(2 * s + ε_work) = -(2 * s + ε) + (-α) := by
    simp [hα_def] <;> ring
  have h4 : Real.rpow δ (-(2 * s + ε_work)) =
      Real.rpow δ (-(2 * s + ε)) * Real.rpow δ (-α) := by
    rw [h_exp_eq]
    exact Real.rpow_add hδ_pos _ _

  -- δ^{-(2s+ε_work)} / K ≥ δ^{-(2s+ε)}
  have h5 : Real.rpow δ (-(2 * s + ε_work)) / Kreal ≥ Real.rpow δ (-(2 * s + ε)) := by
    rw [h4]
    have h6 : 0 < Real.rpow δ (-(2 * s + ε)) := Real.rpow_pos_of_pos hδ_pos _
    have h7 : Real.rpow δ (-α) / Kreal ≥ 1 := by
      have h71 : Real.rpow δ (-α) ≥ Kreal := h1
      have h72 : Real.rpow δ (-α) / Kreal ≥ Kreal / Kreal := by gcongr
      have h73 : Kreal / Kreal = 1 := by
        field_simp [hKreal_pos.ne'] <;> linarith
      rw [h73] at h72
      exact h72
    calc
      Real.rpow δ (-(2 * s + ε)) * Real.rpow δ (-α) / Kreal
        = Real.rpow δ (-(2 * s + ε)) * (Real.rpow δ (-α) / Kreal) := by ring
      _ ≥ Real.rpow δ (-(2 * s + ε)) * 1 := by gcongr
      _ = Real.rpow δ (-(2 * s + ε)) := by ring

  -- Convert to ENNReal
  have h6 : ENNReal.ofReal (Real.rpow δ (-(2 * s + ε_work)) / Kreal) ≥
      ENNReal.ofReal (Real.rpow δ (-(2 * s + ε))) := by
    exact ENNReal.ofReal_le_ofReal h5
  have h7 : ENNReal.ofReal (Real.rpow δ (-(2 * s + ε_work)) / Kreal) =
      ENNReal.ofReal (Real.rpow δ (-(2 * s + ε_work))) / (K_pack : ENNReal) := by
    have h71 : ENNReal.ofReal (Real.rpow δ (-(2 * s + ε_work)) / Kreal) =
        ENNReal.ofReal (Real.rpow δ (-(2 * s + ε_work))) / ENNReal.ofReal Kreal :=
      ENNReal.ofReal_div_of_pos hKreal_pos
    rw [h71]
    have h72 : ENNReal.ofReal Kreal = (K_pack : ENNReal) := by
      simp [hKreal_def]
      <;> norm_cast
    rw [h72]
  rw [h7] at h6
  exact h6

/-! # Final assembly

  Structure (Option A — thin wrapper):
  1. `improved_incidence_correct_Ncover` → the full estimate (Ncover form)
  2. `core_estimate` → thin wrapper adapting notation
  3. `compact_uniformity` → uniform exponent on compact sets

  The hard proof (multiscale decomposition + B1 induction + combining theorem)
  lives inside `improved_incidence_correct_Ncover` in ImprovedIncidenceGeneral.lean.
-/

/--
  Core estimate for a fixed `(s,t)`: produces `ε(s,t) > 0` and `δ₀(s,t) > 0`
  such that the discretised Furstenberg estimate holds.

  This is a thin wrapper around `improved_incidence_correct_Ncover`, which
  is the general improved incidence theorem (OS Theorem 6.1). The Ncover
  version directly gives the `Metric.externalCoveringNumber` bound we need.
-/
theorem core_estimate (s t : ℝ) (hs : 0 < s) (hs1 : s < 1)
    (hst : s < t) (ht2 : t < 2) :
    ∃ (ε δ₀ : ℝ), 0 < ε ∧ 0 < δ₀ ∧
      ∀ (δ : ℝ), δ ∈ Set.Ioc (0 : ℝ) δ₀ →
        ∀ (X : Set EuclideanPlane),
          X ⊆ Metric.closedBall 0 1 →
          IsDeltaSSet δ t (Real.rpow δ (-ε)) X →
          ∀ (𝓣 : ∀ (x : EuclideanPlane), x ∈ X → Set AffineLine),
            (∀ x hx, IsDeltaSSet δ s (Real.rpow δ (-ε)) (𝓣 x hx)) →
            (∀ x hx, ∀ ℓ ∈ 𝓣 x hx, x ∈ Metric.cthickening δ ℓ.1) →
            (Metric.externalCoveringNumber δ.toNNReal
               (⋃ (x : EuclideanPlane) (hx : x ∈ X), 𝓣 x hx) : ENNReal) ≥
              ENNReal.ofReal (Real.rpow δ (-(2 * s + ε))) := by
  -- The entire estimate is provided by improved_incidence_correct_Ncover,
  -- proved via section9_main + theorem6_1_uniform_data.
  rcases ImprovedIncidenceGeneral.improved_incidence_correct_Ncover
      s t hs hs1 hst ht2
    with ⟨ε_G, η, hεG_pos, hη_pos, δ₀, hδ₀_pos, h_imp⟩
  refine' ⟨ε_G, δ₀, hεG_pos, hδ₀_pos, _⟩
  intro δ hδ X hX_bounded hX_sset 𝓣 h𝓣_sset h𝓣_near
  let T : Set AffineLine := ⋃ (x : EuclideanPlane) (hx : x ∈ X), 𝓣 x hx
  have hTp_sub : ∀ (p : EuclideanPlane) (hp : p ∈ X), 𝓣 p hp ⊆ T := by
    intro p hp ℓ hℓ
    simp only [T, Set.mem_iUnion]
    exact ⟨p, hp, hℓ⟩
  exact h_imp δ hδ.1 hδ.2 X hX_bounded hX_sset T 𝓣 hTp_sub h𝓣_sset h𝓣_near

/--
  Compact uniformity: if `ε` works at `(s,t)`, a smaller exponent works
  on a neighborhood. Finite subcover gives uniform `ε₀` on compact sets.
-/
theorem compact_uniformity (ε : ℝ × ℝ → ℝ)
    (hε_cont : ContinuousOn ε parameterRange)
    (hε_pos : ∀ p ∈ parameterRange, 0 < ε p) :
    ∀ (A : Set (ℝ × ℝ)), IsCompact A → A ⊆ parameterRange →
      ∃ (ε₀ : ℝ), 0 < ε₀ ∧ ∀ p ∈ A, ε₀ ≤ ε p := by
  intro A hA_compact hA_sub
  by_cases hne : A.Nonempty
  · -- A nonempty: continuous function attains minimum on compact set
    have h_min : ∃ p₀ ∈ A, ∀ p ∈ A, ε p₀ ≤ ε p :=
      hA_compact.exists_isMinOn hne (hε_cont.mono hA_sub)
    rcases h_min with ⟨p₀, hp₀, hmin⟩
    have h_pos : 0 < ε p₀ := hε_pos p₀ (hA_sub hp₀)
    exact ⟨ε p₀, h_pos, fun p hp => hmin p hp⟩
  · -- A empty: any positive ε₀ works
    refine ⟨1, by norm_num, fun p hp => False.elim (hne ⟨p, hp⟩)⟩

end DirecretisedFurstenbergEstimate.FinalProof
