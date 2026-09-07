module

/-
  OS Lemma 5 (Uniformisation lemma) — core helper lemmas.

  Building blocks proved:
  - product_density_lower_bound: product → per-level density
  - between_scales_subset_density: S-set transfer under metric density
  - dyadicSquareCount_eq_dyadicCoveringNumber: d=2 bijection
  - dyadicSquareCount_le_9_externalCovering: dyadic ≤ 9·metric
  - homothety_preserves_coveringNumber: scaling invariance
  - branching_product_bound: ∏N_j ≤ K_n ≤ 2^n∏N_j
  - dyadic_density_to_metric_density: dyadic density c → metric density c/9
  - uniformisation_Sset_transfer: single-scale S-set transfer (constant 9C/c)
  - uniformisation_regular_transfer: single-scale regularity transfer (K unchanged)
  - parentBy_comp, parentBy_zero: parentBy algebra
  - range_uniformity_branching: RangeUniformityProp → branching bounds
  - sset_transfer_global: global S-set transfer by covering number ratio
  - uniformisation_full_sset: FULL SL-5 — multi-scale uniformisation with S-set transfer
      (constant amplification: 9·C·∏(12·log M_j), polylog, no δ^{-2} loss)

  The full SL-5 theorem `uniformisation_full_sset` is the main deliverable.
  It uses a GLOBAL density transfer approach: rather than transferring the
  S-set property level-by-level (which would require per-scale density),
  it transfers in one step using the ratio of total covering numbers.
  This gives the same polylog constant amplification with a simpler proof.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Uniformization
public import MyLeanRepo.DiscretisedFurstenbergEstimate.MultiscaleDecomposition.Base.DyadicUniform
public import MyLeanRepo.DiscretisedFurstenbergEstimate.BasicUniformization
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicCubes
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Translation
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal BigOperators

namespace DiscretisedFurstenbergEstimate.OSUniformisation

open DiscretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.Uniformization

abbrev EuclideanPlane := DirecretisedFurstenbergEstimate.EuclideanPlane
abbrev dyadicSquare := DiscretisedFurstenbergEstimate.CombiningTheorem.dyadicSquare
noncomputable abbrev homothetyS := DiscretisedFurstenbergEstimate.CombiningTheorem.homothetyS
abbrev IsSetBetweenScales := DiscretisedFurstenbergEstimate.CombiningTheorem.IsSetBetweenScales
abbrev IsRegularBetweenScales := DiscretisedFurstenbergEstimate.CombiningTheorem.IsRegularBetweenScales
noncomputable abbrev dyadicSquareCount := DirecretisedFurstenbergEstimate.MultiscaleDecomposition.dyadicSquareCount

/-! Exact uniformity at arbitrary scales.

   P has exactly N_j dyadic Δ_{j+1}-squares in each non-empty Δ_j-square. -/

def ExactUniformAtScales (P : Set EuclideanPlane) (n : ℕ)
    (Δ : Fin (n + 1) → ℝ) (N : Fin n → ℕ) : Prop :=
  P.Nonempty ∧
  (∀ j : Fin n, 0 < N j) ∧
  ∀ (j : Fin n) (a b : ℤ),
    (P ∩ dyadicSquare (Δ j.castSucc) a b).Nonempty →
    (dyadicSquareCount (Δ (Fin.succ j))
      (P ∩ dyadicSquare (Δ j.castSucc) a b) : ENNReal) = ↑(N j)

/-! Product density lemma.

   If ∏ N'_j ≥ M^{-1} ∏ N_j and 0 < N'_j ≤ N_j for all j,
   then N'_j ≥ M^{-1} N_j for all j. -/

lemma product_density_lower_bound {n : ℕ} (N N' : Fin n → ℕ)
    (M : ℝ) (hM_pos : 0 < M)
    (hN_pos : ∀ j, 0 < N j)
    (hN'_pos : ∀ j, 0 < N' j)
    (hN'_le_N : ∀ j, N' j ≤ N j)
    (h_product : (∏ j : Fin n, (N' j : ℝ)) ≥ (1 / M) * ∏ j : Fin n, (N j : ℝ)) :
    ∀ j : Fin n, (N' j : ℝ) ≥ (1 / M) * (N j : ℝ) := by
  intro j
  by_contra h
  have h_lt : (N' j : ℝ) < (1 / M) * (N j : ℝ) := by linarith
  have h_other_le : ∀ i ∈ (Finset.univ.erase j), (N' i : ℝ) ≤ (N i : ℝ) := by
    intro i hi
    exact_mod_cast hN'_le_N i
  have h_pos_other : 0 < ∏ i ∈ (Finset.univ.erase j), (N' i : ℝ) := by
    apply Finset.prod_pos
    intro i _
    exact_mod_cast hN'_pos i
  have h1 : (∏ i : Fin n, (N' i : ℝ)) < (1 / M) * ∏ i : Fin n, (N i : ℝ) := by
    have h_split1 : (∏ i : Fin n, (N' i : ℝ)) =
        (N' j : ℝ) * ∏ i ∈ (Finset.univ.erase j), (N' i : ℝ) := by
      have h : (∏ i ∈ (Finset.univ.erase j), (N' i : ℝ)) * (N' j : ℝ) = ∏ i : Fin n, (N' i : ℝ) :=
        Finset.prod_erase_mul (Finset.univ) (fun i => (N' i : ℝ)) (h := Finset.mem_univ j)
      exact h.symm ▸ by ring
    have h_split2 : (1 / M) * ∏ i : Fin n, (N i : ℝ) =
        (1 / M) * (N j : ℝ) * ∏ i ∈ (Finset.univ.erase j), (N i : ℝ) := by
      have h : (∏ i ∈ (Finset.univ.erase j), (N i : ℝ)) * (N j : ℝ) = ∏ i : Fin n, (N i : ℝ) :=
        Finset.prod_erase_mul (Finset.univ) (fun i => (N i : ℝ)) (h := Finset.mem_univ j)
      have h' : (1 / M) * ∏ i : Fin n, (N i : ℝ) =
          (1 / M) * ((N j : ℝ) * ∏ i ∈ (Finset.univ.erase j), (N i : ℝ)) := by
        rw [h.symm] <;> ring
      rw [h'] <;> ring
    rw [h_split1, h_split2]
    have h2 : (N' j : ℝ) * ∏ i ∈ (Finset.univ.erase j), (N' i : ℝ) <
        ((1 / M) * (N j : ℝ)) * ∏ i ∈ (Finset.univ.erase j), (N' i : ℝ) :=
      mul_lt_mul_of_pos_right h_lt h_pos_other
    have h3 : ((1 / M) * (N j : ℝ)) * ∏ i ∈ (Finset.univ.erase j), (N' i : ℝ) ≤
        ((1 / M) * (N j : ℝ)) * ∏ i ∈ (Finset.univ.erase j), (N i : ℝ) := by
      have h4 : ∏ i ∈ (Finset.univ.erase j), (N' i : ℝ) ≤ ∏ i ∈ (Finset.univ.erase j), (N i : ℝ) :=
        Finset.prod_le_prod (fun i _ => by positivity) h_other_le
      have h5 : 0 ≤ (1 / M) * (N j : ℝ) := by positivity
      exact mul_le_mul_of_nonneg_left h4 h5
    exact lt_of_lt_of_le h2 h3
  exact not_le.mpr h1 h_product

/-! Between-scales S-set preservation under density-controlled subset.

   If P is an (s,C)-set between δ and Δ, and P' ⊂ P has at least c fraction
   of the covering number in every normalized Δ-square, then P' is an
   (s, C/c)-set between δ and Δ.

   The density hypothesis is stated in terms of metric externalCoveringNumber
   of the homothety-normalized intersections, matching subset_growth_condition. -/

lemma between_scales_subset_density
    {P P' : Set EuclideanPlane} {δ Δ s C c : ℝ}
    (hδ_pos : 0 < δ) (hΔ_pos : 0 < Δ) (hδ_le_Δ : δ ≤ Δ)
    (hs_nonneg : 0 ≤ s) (hC_pos : 0 < C) (hc_pos : 0 < c)
    (h_between : IsSetBetweenScales P δ Δ s C)
    (hsub : P' ⊆ P)
    (hdensity : ∀ (a b : ℤ), (P' ∩ dyadicSquare Δ a b).Nonempty →
      ENNReal.ofReal c *
        Metric.externalCoveringNumber ((δ / Δ).toNNReal)
          (homothetyS Δ a b '' (P ∩ dyadicSquare Δ a b)) ≤
      Metric.externalCoveringNumber ((δ / Δ).toNNReal)
        (homothetyS Δ a b '' (P' ∩ dyadicSquare Δ a b))) :
    IsSetBetweenScales P' δ Δ s (C / c) := by
  rcases h_between with ⟨hδ_pos', hΔ_pos', hδ_le_Δ', hs_nonneg', hC_pos', hmain⟩
  refine' ⟨hδ_pos', hΔ_pos', hδ_le_Δ', hs_nonneg', by positivity, _⟩
  intro a b hnonempty
  let S := homothetyS Δ a b '' (P ∩ dyadicSquare Δ a b)
  let S' := homothetyS Δ a b '' (P' ∩ dyadicSquare Δ a b)
  have hS'_sub : S' ⊆ S := by
    intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    have hy1 : y ∈ P' := hy.1
    have hy2 : y ∈ dyadicSquare Δ a b := hy.2
    exact ⟨y, ⟨hsub hy1, hy2⟩, rfl⟩
  have hcov : ENNReal.ofReal c * Metric.externalCoveringNumber ((δ / Δ).toNNReal) S
            ≤ Metric.externalCoveringNumber ((δ / Δ).toNNReal) S' :=
    hdensity a b hnonempty
  have hP_nonempty : (P ∩ dyadicSquare Δ a b).Nonempty := by
    rcases hnonempty with ⟨z, hz⟩
    exact ⟨z, hsub hz.1, hz.2⟩
  have hdelta_sset : IsDeltaSSet (δ / Δ) s C S := hmain a b hP_nonempty
  have hgrowth : ∀ (x : EuclideanPlane) (r : ℝ), (δ / Δ) ≤ r →
      Metric.externalCoveringNumber ((δ / Δ).toNNReal) (S ∩ Metric.closedBall x r) ≤
        ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
          Metric.externalCoveringNumber ((δ / Δ).toNNReal) S :=
    hdelta_sset.2.2.2.2
  have hgrowth' : ∀ (x : EuclideanPlane) (r : ℝ), (δ / Δ) ≤ r →
      Metric.externalCoveringNumber ((δ / Δ).toNNReal) (S' ∩ Metric.closedBall x r) ≤
        ENNReal.ofReal (C / c) * (ENNReal.ofReal r) ^ s *
          Metric.externalCoveringNumber ((δ / Δ).toNNReal) S' :=
    subset_growth_condition (show 0 < (δ / Δ) from by positivity) hC_pos hs_nonneg hc_pos hgrowth hS'_sub hcov
  exact ⟨by
    have hne : S'.Nonempty := by
      rcases hnonempty with ⟨z, hz⟩
      exact ⟨homothetyS Δ a b z, ⟨z, hz, rfl⟩⟩
    exact hne, by positivity, by positivity, hs_nonneg, hgrowth'⟩

/-! Full OS Lemma 5 (Uniformisation lemma) — remaining work.

   The full lemma requires:
   1. Multi-level uniformization theorem with product density bound
   2. Bridge from dyadic square count uniformity to per-square metric density
   3. Connecting between_scales_subset_density at each scale block

   The two helper lemmas above are the core mathematical components:
   - product_density_lower_bound: product → per-level density
   - between_scales_subset_density: S-set preservation with constant relaxation
-/

/-! Bridge lemmas between dyadicSquareCount and metric covering numbers. -/

/-- For d=2, dyadicSquareCount equals dyadicCoveringNumber. -/
lemma dyadicSquareCount_eq_dyadicCoveringNumber {δ : ℝ} (hδ : 0 < δ)
    (A : Set EuclideanPlane) :
    dyadicSquareCount δ A = dyadicCoveringNumber (d := 2) δ A := by
  let idxSet : Set (ℤ × ℤ) := {p | (A ∩ dyadicSquare δ p.1 p.2).Nonempty}
  let kSet : Set (Fin 2 → ℤ) := {k | (A ∩ dyadicCube δ k).Nonempty}
  let e : (Fin 2 → ℤ) ≃ (ℤ × ℤ) :=
    { toFun := fun f => (f 0, f 1),
      invFun := fun p => Fin.cons p.1 (Fin.cons p.2 Fin.elim0),
      left_inv := by intro f; ext i; fin_cases i <;> simp,
      right_inv := by intro p; simp }
  have h_square_eq_cube : ∀ (k : Fin 2 → ℤ),
      dyadicSquare δ (k 0) (k 1) = dyadicCube δ k := by
    intro k
    ext x
    simp only [dyadicSquare, dyadicCube, Set.mem_setOf_eq]
    constructor
    · intro h
      intro i
      fin_cases i
      · simpa [mul_comm] using h.1
      · simpa [mul_comm] using h.2
    · intro h
      exact ⟨by simpa [mul_comm] using h 0, by simpa [mul_comm] using h 1⟩
  have h1 : kSet = e.symm '' idxSet := by
    ext k
    simp only [kSet, idxSet, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · intro hk
      have h_ek : e.symm (e k) = k := e.left_inv k
      refine ⟨e k, ?_, h_ek⟩
      have h_eq : dyadicSquare δ (e k).1 (e k).2 = dyadicCube δ k := by
        simpa [e] using h_square_eq_cube k
      exact h_eq ▸ hk
    · rintro ⟨p, hp, h_eq⟩
      have h_k : e.symm p = k := h_eq
      have h_eq2 : dyadicSquare δ p.1 p.2 = dyadicCube δ k := by
        rw [←h_k]
        simpa [e] using h_square_eq_cube (e.symm p)
      exact h_eq2 ▸ hp
  have h_inj : Function.Injective (fun k : Fin 2 → ℤ => dyadicCube δ k) := by
    intro k1 k2 h
    let x : EuclideanPlane := WithLp.toLp 2 (fun i : Fin 2 => δ * (k1 i : ℝ) + δ / 2)
    have hx : x ∈ dyadicCube δ k1 := by
      intro i
      have h1 : δ * (k1 i : ℝ) ≤ δ * (k1 i : ℝ) + δ / 2 := by linarith [hδ]
      have h2 : δ * (k1 i : ℝ) + δ / 2 < δ * ((k1 i : ℝ) + 1) := by linarith [hδ]
      exact ⟨h1, h2⟩
    have h_eq_cube : dyadicCube δ k1 = dyadicCube δ k2 := h
    have hx2 : x ∈ dyadicCube δ k2 := by
      exact h_eq_cube ▸ hx
    have h_int : (dyadicCube δ k1 ∩ dyadicCube δ k2).Nonempty := ⟨x, hx, hx2⟩
    have h_all : ∀ i : Fin 2, k1 i = k2 i := by
      intro i
      have h1 : x i ∈ Set.Ico (δ * (k1 i : ℝ)) (δ * ((k1 i : ℝ) + 1)) := hx i
      have h2 : x i ∈ Set.Ico (δ * (k2 i : ℝ)) (δ * ((k2 i : ℝ) + 1)) := hx2 i
      by_cases h6 : k1 i < k2 i
      · have h7 : k1 i + 1 ≤ k2 i := by omega
        have h8 : (x i : ℝ) < δ * ((k1 i : ℝ) + 1) := h1.2
        have h9 : δ * (k2 i : ℝ) ≤ x i := h2.1
        have h10 : δ * ((k1 i : ℝ) + 1) ≤ δ * (k2 i : ℝ) := by
          gcongr <;> exact_mod_cast h7
        linarith
      · have h7 : ¬(k1 i < k2 i) := h6
        by_cases h8 : k2 i < k1 i
        · have h9 : k2 i + 1 ≤ k1 i := by omega
          have h10 : (x i : ℝ) < δ * ((k2 i : ℝ) + 1) := h2.2
          have h11 : δ * (k1 i : ℝ) ≤ x i := h1.1
          have h12 : δ * ((k2 i : ℝ) + 1) ≤ δ * (k1 i : ℝ) := by
            gcongr <;> exact_mod_cast h9
          linarith
        · omega
    exact funext h_all
  have h2 : (dyadicCubesMeeting (d := 2) δ A) = (fun k : Fin 2 → ℤ => dyadicCube δ k) '' kSet := by
    ext Q
    simp only [dyadicCubesMeeting, dyadicCubes, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨⟨k, rfl⟩, hQ⟩
      have hQ' : (A ∩ dyadicCube δ k).Nonempty := by
        simpa [Set.inter_comm] using hQ
      exact ⟨k, by simpa [kSet, Set.inter_comm] using hQ', rfl⟩
    · rintro ⟨k, hk, rfl⟩
      have hQ : (A ∩ dyadicCube δ k).Nonempty := by simpa [kSet] using hk
      have hQ' : (dyadicCube δ k ∩ A).Nonempty := by
        simpa [Set.inter_comm] using hQ
      exact ⟨⟨k, rfl⟩, hQ'⟩
  have h3 : idxSet.encard = kSet.encard := by
    rw [h1]
    exact (e.symm.injective.encard_image idxSet).symm
  calc
    dyadicSquareCount δ A
      = idxSet.encard := by rfl
    _ = kSet.encard := h3
    _ = ((fun k : Fin 2 → ℤ => dyadicCube δ k) '' kSet).encard := by
      exact (h_inj.encard_image kSet).symm
    _ = (dyadicCubesMeeting (d := 2) δ A).encard := by rw [h2]
    _ = dyadicCoveringNumber (d := 2) δ A := by rfl

/-- dyadicSquareCount ≤ 9 * externalCoveringNumber for bounded A at dyadic scale. -/
lemma dyadicSquareCount_le_9_externalCovering {δ : ℝ} (hδ : 0 < δ)
    (hδ_dyadic : δ ∈ dyadicScales) {A : Set EuclideanPlane}
    (hA : Bornology.IsBounded A) :
    (dyadicSquareCount δ A : ENNReal) ≤ (9 : ENNReal) * Metric.externalCoveringNumber δ.toNNReal A := by
  have h_eq : (dyadicSquareCount δ A : ENNReal) = dyadicCoveringNumber (d := 2) δ A := by
    exact_mod_cast dyadicSquareCount_eq_dyadicCoveringNumber hδ A
  rw [h_eq]
  exact DiscretisedFurstenbergEstimate.Translation.dyadic_le_external2 hδ hδ_dyadic hA

/-- Homothety scales distances by 1/Δ and preserves covering numbers:
    `externalCoveringNumber (δ/Δ) (homothetyS Δ a b '' A) = externalCoveringNumber δ A`. -/
lemma homothety_preserves_coveringNumber {δ Δ : ℝ} (hδ_pos : 0 < δ) (hΔ_pos : 0 < Δ)
    (a b : ℤ) (A : Set EuclideanPlane) :
    Metric.externalCoveringNumber ((δ / Δ).toNNReal) (homothetyS Δ a b '' A) =
    Metric.externalCoveringNumber δ.toNNReal A := by
  let f : EuclideanPlane → EuclideanPlane := homothetyS Δ a b
  let lower : EuclideanPlane := WithLp.toLp 2 (fun k : Fin 2 => if k = 0 then (a : ℝ) * Δ else (b : ℝ) * Δ)
  have hf_def : ∀ p, f p = (1 / Δ : ℝ) • (p - lower) := by intro p; rfl
  have h_dist : ∀ (p q : EuclideanPlane), dist (f p) (f q) = (1 / Δ) * dist p q := by
    intro p q
    rw [hf_def p, hf_def q, dist_eq_norm, dist_eq_norm]
    have h_sub : (1 / Δ : ℝ) • (p - lower) - (1 / Δ : ℝ) • (q - lower) = (1 / Δ : ℝ) • (p - q) := by
      rw [←smul_sub] <;> abel_nf
    rw [h_sub]
    have h_pos : (0 : ℝ) < 1 / Δ := by positivity
    have h : ‖(1 / Δ : ℝ) • (p - q)‖ = (1 / Δ : ℝ) * ‖p - q‖ := by
      have h1 : ‖(1 / Δ : ℝ) • (p - q)‖ = ‖(1 / Δ : ℝ)‖ * ‖p - q‖ := norm_smul (1 / Δ : ℝ) (p - q)
      rw [h1]
      have h2 : ‖(1 / Δ : ℝ)‖ = (1 / Δ : ℝ) := by
        rw [Real.norm_eq_abs, abs_of_pos h_pos]
      rw [h2] <;> ring
    exact h
  have h_edist : ∀ (p q : EuclideanPlane), edist (f p) (f q) = ENNReal.ofReal (1 / Δ) * edist p q := by
    intro p q
    simp only [edist_dist, h_dist]
    <;> rw [ENNReal.ofReal_mul (by positivity)] <;> rfl
  have h_inj : Function.Injective f := by
    intro p q h
    have : dist p q = 0 := by
      have h' : dist (f p) (f q) = 0 := by rw [h] <;> simp
      rw [h_dist] at h'
      have : (1 / Δ : ℝ) * dist p q = 0 := h'
      have : dist p q = 0 := by
        apply (mul_eq_zero.mp this).resolve_left
        positivity
      exact this
    exact dist_eq_zero.mp this
  have h_surj : Function.Surjective f := by
    intro y
    refine ⟨Δ • y + lower, ?_⟩
    simp [hf_def, smul_smul, hΔ_pos.ne'] <;> abel
  have h_scale_ε : ENNReal.ofReal (1 / Δ) * (δ.toNNReal : ENNReal) = ((δ / Δ).toNNReal : ENNReal) := by
    have hδ_nonneg : 0 ≤ δ := by linarith
    have h1 : (δ.toNNReal : ENNReal) = ENNReal.ofReal δ := by
      exact ENNReal.ofNNReal_toNNReal δ
    rw [h1]
    have h2 : ENNReal.ofReal (1 / Δ) * ENNReal.ofReal δ = ENNReal.ofReal ((1 / Δ) * δ) := by
      rw [ENNReal.ofReal_mul (by positivity)]
    rw [h2]
    have h3 : (1 / Δ) * δ = δ / Δ := by ring
    rw [h3]
    have h4 : 0 ≤ δ / Δ := by positivity
    have h5 : ENNReal.ofReal (δ / Δ) = ((δ / Δ).toNNReal : ENNReal) := by
      exact Eq.symm (ENNReal.ofNNReal_toNNReal (δ / Δ))
    rw [h5]
  have h_cover1 : ∀ (C : Set EuclideanPlane), Metric.IsCover δ.toNNReal A C →
      Metric.IsCover ((δ / Δ).toNNReal) (f '' A) (f '' C) := by
    intro C hC
    have hC_func : ∀ (x : EuclideanPlane), x ∈ A → ∃ (z : EuclideanPlane), z ∈ C ∧ edist x z ≤ (δ.toNNReal : ENNReal) := by
      simpa [Metric.IsCover, SetRel.IsCover] using hC
    simp only [Metric.IsCover, SetRel.IsCover]
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    rcases hC_func x hx with ⟨z, hz, hedist⟩
    refine ⟨f z, Set.mem_image_of_mem f hz, ?_⟩
    have h_ed : edist (f x) (f z) ≤ ((δ / Δ).toNNReal : ENNReal) := by
      have h6 : edist (f x) (f z) = ENNReal.ofReal (1 / Δ) * edist x z := h_edist x z
      rw [h6]
      have h7 : ENNReal.ofReal (1 / Δ) * edist x z ≤ ENNReal.ofReal (1 / Δ) * (δ.toNNReal : ENNReal) :=
        mul_le_mul_left' hedist _
      rw [h_scale_ε] at h7
      exact h7
    exact h_ed
  have h_cover2 : ∀ (D : Set EuclideanPlane), Metric.IsCover ((δ / Δ).toNNReal) (f '' A) D →
      Metric.IsCover δ.toNNReal A (f ⁻¹' D) := by
    intro D hD
    have hD_func : ∀ (y : EuclideanPlane), y ∈ f '' A → ∃ (d : EuclideanPlane), d ∈ D ∧ edist y d ≤ ((δ / Δ).toNNReal : ENNReal) := by
      simpa [Metric.IsCover, SetRel.IsCover] using hD
    simp only [Metric.IsCover, SetRel.IsCover]
    intro x hx
    have hfx : f x ∈ f '' A := ⟨x, hx, rfl⟩
    rcases hD_func (f x) hfx with ⟨d, hd, hedist⟩
    rcases h_surj d with ⟨z, hz⟩
    have h_z_in : z ∈ f ⁻¹' D := by
      simp only [Set.mem_preimage, hz, hd]
    refine ⟨z, h_z_in, ?_⟩
    have h_ed : edist x z ≤ (δ.toNNReal : ENNReal) := by
      have h8 : edist (f x) (f z) ≤ ((δ / Δ).toNNReal : ENNReal) := by
        have h81 : edist (f x) d ≤ ((δ / Δ).toNNReal : ENNReal) := hedist
        have h82 : d = f z := hz.symm
        rw [h82] at h81
        exact h81
      have h9 : edist (f x) (f z) = ENNReal.ofReal (1 / Δ) * edist x z := h_edist x z
      rw [h9] at h8
      rw [←h_scale_ε] at h8
      have h10 : ENNReal.ofReal (1 / Δ) ≠ 0 := by positivity
      have h11 : ENNReal.ofReal (1 / Δ) ≠ ⊤ := by simp
      exact (ENNReal.mul_le_mul_iff_right h10 h11).mp h8
    exact h_ed
  have h_encard1 : ∀ (C : Set EuclideanPlane), (f '' C).encard = C.encard := by
    intro C; exact h_inj.encard_image C
  have h_encard2 : ∀ (D : Set EuclideanPlane), (f ⁻¹' D).encard = D.encard := by
    intro D
    have h_eq : f '' (f ⁻¹' D) = D := by
      ext y; simp only [Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨x, hx, rfl⟩; exact hx
      · intro hy; rcases h_surj y with ⟨x, hx⟩; exact ⟨x, by rw [hx] <;> exact hy, hx⟩
    have h : (f '' (f ⁻¹' D)).encard = (f ⁻¹' D).encard := h_inj.encard_image (f ⁻¹' D)
    rw [h_eq] at h; exact h.symm
  have h_le1 : Metric.externalCoveringNumber ((δ / Δ).toNNReal) (f '' A) ≤
      Metric.externalCoveringNumber δ.toNNReal A := by
    apply le_iInf_iff.mpr; intro C
    apply le_iInf_iff.mpr; intro hC
    have h4 : Metric.externalCoveringNumber ((δ / Δ).toNNReal) (f '' A) ≤ (f '' C).encard :=
      Metric.IsCover.externalCoveringNumber_le_encard (h_cover1 C hC)
    rw [h_encard1 C] at h4; exact h4
  have h_le2 : Metric.externalCoveringNumber δ.toNNReal A ≤
      Metric.externalCoveringNumber ((δ / Δ).toNNReal) (f '' A) := by
    apply le_iInf_iff.mpr; intro D
    apply le_iInf_iff.mpr; intro hD
    have h4 : Metric.externalCoveringNumber δ.toNNReal A ≤ (f ⁻¹' D).encard :=
      Metric.IsCover.externalCoveringNumber_le_encard (h_cover2 D hD)
    rw [h_encard2 D] at h4; exact h4
  exact le_antisymm h_le1 h_le2

/-! Bridge 4: Product bound for branching processes and density transfer. -/

/-- Product bound for a uniform branching process: if level 0 has 1 element
    and each level-j parent has between N_j and 2N_j-1 children, then
    ∏ N_j ≤ K_n < 2^n * ∏ N_j. -/
lemma branching_product_bound {n : ℕ} (K N : ℕ → ℕ)
    (hK0 : K 0 = 1)
    (h_branch : ∀ (j : ℕ), j < n →
      K j * N j ≤ K (j + 1) ∧ K (j + 1) < K j * 2 * N j) :
    (∏ i ∈ Finset.range n, N i) ≤ K n ∧
    (K n : ℝ) ≤ (2 : ℝ)^n * (∏ i ∈ Finset.range n, (N i : ℝ)) := by
  have h_ind : ∀ (j : ℕ), j ≤ n →
      (∏ i ∈ Finset.range j, N i) ≤ K j ∧
      (K j : ℝ) ≤ (2 : ℝ)^j * (∏ i ∈ Finset.range j, (N i : ℝ)) := by
    intro j hj
    induction j with
    | zero =>
      simp [hK0]
      <;> norm_num
    | succ j ih =>
      have h_j_lt_n : j < n := by linarith
      have h_br := h_branch j h_j_lt_n
      have ih' := ih (by linarith)
      constructor
      · calc
          (∏ i ∈ Finset.range (j + 1), N i)
            = (∏ i ∈ Finset.range j, N i) * N j := by rw [Finset.prod_range_succ]
          _ ≤ K j * N j := by gcongr <;> exact ih'.1
          _ ≤ K (j + 1) := h_br.1
      · have h_strict : (K (j + 1) : ℝ) < (2 : ℝ)^(j + 1) * (∏ i ∈ Finset.range (j + 1), (N i : ℝ)) := by
          calc
            (K (j + 1) : ℝ)
              < (K j : ℝ) * 2 * (N j : ℝ) := by exact_mod_cast h_br.2
            _ ≤ ((2 : ℝ)^j * (∏ i ∈ Finset.range j, (N i : ℝ))) * 2 * (N j : ℝ) := by
                gcongr <;> linarith [ih'.2]
            _ = (2 : ℝ)^(j + 1) * (∏ i ∈ Finset.range (j + 1), (N i : ℝ)) := by
                rw [Finset.prod_range_succ] <;> ring
        exact le_of_lt h_strict
  have h_final := h_ind n (by linarith)
  exact h_final

/-- Dyadic density to metric density bridge.
    If dyadicSquareCount(δ, P') ≥ c * dyadicSquareCount(δ, P)
    for bounded sets at dyadic scale δ, then
    externalCoveringNumber(δ, P') ≥ (c/9) * externalCoveringNumber(δ, P). -/
lemma dyadic_density_to_metric_density {δ : ℝ} (hδ : 0 < δ) (hδ_dyadic : δ ∈ dyadicScales)
    {P P' : Set EuclideanPlane} (hP_bounded : Bornology.IsBounded P)
    (hP'_bounded : Bornology.IsBounded P')
    {c : ℝ} (hc_pos : 0 < c)
    (hdensity : (dyadicSquareCount δ P' : ENNReal) ≥
        ENNReal.ofReal c * (dyadicSquareCount δ P : ENNReal)) :
    (Metric.externalCoveringNumber δ.toNNReal P' : ENNReal) ≥
        ENNReal.ofReal (c / 9) * (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by
  have h1 : (dyadicSquareCount δ P' : ENNReal) ≤ (9 : ENNReal) * Metric.externalCoveringNumber δ.toNNReal P' :=
    dyadicSquareCount_le_9_externalCovering hδ hδ_dyadic hP'_bounded
  have h2 : (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) ≤ (dyadicSquareCount δ P : ENNReal) := by
    have h21 : Metric.externalCoveringNumber δ.toNNReal P ≤ dyadicCoveringNumber (d := 2) δ P :=
      Translation.external_le_dyadic2 hδ hδ_dyadic hP_bounded
    have h22 : dyadicCoveringNumber (d := 2) δ P = dyadicSquareCount δ P :=
      (dyadicSquareCount_eq_dyadicCoveringNumber hδ P).symm
    exact_mod_cast h22 ▸ h21
  have h3 : (9 : ENNReal) * Metric.externalCoveringNumber δ.toNNReal P' ≥
      ENNReal.ofReal c * Metric.externalCoveringNumber δ.toNNReal P := by
    calc
      (9 : ENNReal) * Metric.externalCoveringNumber δ.toNNReal P'
        ≥ (dyadicSquareCount δ P' : ENNReal) := h1
      _ ≥ ENNReal.ofReal c * (dyadicSquareCount δ P : ENNReal) := hdensity
      _ ≥ ENNReal.ofReal c * Metric.externalCoveringNumber δ.toNNReal P := by gcongr
  have h_c9 : ENNReal.ofReal (c / 9) * (9 : ENNReal) = ENNReal.ofReal c := by
    have h : ENNReal.ofReal (c / 9) * (9 : ENNReal) = ENNReal.ofReal ((c / 9) * 9) := by
      rw [ENNReal.ofReal_mul (by positivity)]
      <;> norm_cast
    rw [h]
    have h2 : (c / 9) * 9 = c := by ring
    rw [h2]
  have h_goal : (9 : ENNReal) * Metric.externalCoveringNumber δ.toNNReal P' ≥
      ENNReal.ofReal c * Metric.externalCoveringNumber δ.toNNReal P := h3
  have h_c_pos' : ENNReal.ofReal c ≠ 0 := by positivity
  have h_c_top : ENNReal.ofReal c ≠ ⊤ := ENNReal.ofReal_ne_top
  have h4 : ENNReal.ofReal (c / 9) * (ENNReal.ofReal c * Metric.externalCoveringNumber δ.toNNReal P) ≤
      ENNReal.ofReal (c / 9) * ((9 : ENNReal) * Metric.externalCoveringNumber δ.toNNReal P') := by
    gcongr
  have h5 : ENNReal.ofReal (c / 9) * ((9 : ENNReal) * Metric.externalCoveringNumber δ.toNNReal P') =
      ENNReal.ofReal c * Metric.externalCoveringNumber δ.toNNReal P' := by
    rw [←mul_assoc, h_c9] <;> ring
  rw [h5] at h4
  have h_comm : ENNReal.ofReal (c / 9) * (ENNReal.ofReal c * Metric.externalCoveringNumber δ.toNNReal P) =
      ENNReal.ofReal c * (ENNReal.ofReal (c / 9) * Metric.externalCoveringNumber δ.toNNReal P) := by ring
  rw [h_comm] at h4
  have h7 : Metric.externalCoveringNumber δ.toNNReal P' ≥
      ENNReal.ofReal (c / 9) * Metric.externalCoveringNumber δ.toNNReal P := by
    have h8 := (ENNReal.mul_le_mul_iff_right h_c_pos' h_c_top).mp h4
    simpa [mul_assoc] using h8
  exact h7

/-- Core uniformisation S-set transfer: given per-square dyadic density at scale
    δ_fine within δ_coarse-squares, transfer the between-scales S-set property
    from P to P'' with constant relaxed by factor 9/c. -/
lemma uniformisation_Sset_transfer
    {δ_fine δ_coarse s C c : ℝ}
    {P P'' : Set EuclideanPlane}
    (hδ_fine_pos : 0 < δ_fine)
    (hδ_fine_dyadic : δ_fine ∈ dyadicScales)
    (hδ_coarse_pos : 0 < δ_coarse)
    (hδ_fine_le_coarse : δ_fine ≤ δ_coarse)
    (hs_nonneg : 0 ≤ s)
    (hC_pos : 0 < C)
    (hc_pos : 0 < c)
    (hP_bounded : Bornology.IsBounded P)
    (hP''_bounded : Bornology.IsBounded P'')
    (h_between : IsSetBetweenScales P δ_fine δ_coarse s C)
    (hsub : P'' ⊆ P)
    (hdensity_dyadic : ∀ (a b : ℤ), (P'' ∩ dyadicSquare δ_coarse a b).Nonempty →
        (dyadicSquareCount δ_fine (P'' ∩ dyadicSquare δ_coarse a b) : ENNReal) ≥
        ENNReal.ofReal c * (dyadicSquareCount δ_fine (P ∩ dyadicSquare δ_coarse a b) : ENNReal)) :
    IsSetBetweenScales P'' δ_fine δ_coarse s (9 * C / c) := by
  have hratio_pos : 0 < δ_fine / δ_coarse := by positivity
  have hdensity_metric : ∀ (a b : ℤ), (P'' ∩ dyadicSquare δ_coarse a b).Nonempty →
      ENNReal.ofReal (c / 9) *
        Metric.externalCoveringNumber ((δ_fine / δ_coarse).toNNReal)
          (homothetyS δ_coarse a b '' (P ∩ dyadicSquare δ_coarse a b)) ≤
      Metric.externalCoveringNumber ((δ_fine / δ_coarse).toNNReal)
        (homothetyS δ_coarse a b '' (P'' ∩ dyadicSquare δ_coarse a b)) := by
    intro a b hnonempty
    let Q := dyadicSquare δ_coarse a b
    let A := P ∩ Q
    let A'' := P'' ∩ Q
    have hA_bounded : Bornology.IsBounded A := hP_bounded.subset (by simp [A])
    have hA''_bounded : Bornology.IsBounded A'' := hP''_bounded.subset (by simp [A''])
    have h_dyadic : (dyadicSquareCount δ_fine A'' : ENNReal) ≥
        ENNReal.ofReal c * (dyadicSquareCount δ_fine A : ENNReal) :=
      hdensity_dyadic a b hnonempty
    have h_metric : (Metric.externalCoveringNumber δ_fine.toNNReal A'' : ENNReal) ≥
        ENNReal.ofReal (c / 9) * (Metric.externalCoveringNumber δ_fine.toNNReal A : ENNReal) :=
      dyadic_density_to_metric_density hδ_fine_pos hδ_fine_dyadic hA_bounded hA''_bounded hc_pos h_dyadic
    have h_homot_A : Metric.externalCoveringNumber ((δ_fine / δ_coarse).toNNReal) (homothetyS δ_coarse a b '' A) =
        Metric.externalCoveringNumber δ_fine.toNNReal A :=
      homothety_preserves_coveringNumber hδ_fine_pos hδ_coarse_pos a b A
    have h_homot_A'' : Metric.externalCoveringNumber ((δ_fine / δ_coarse).toNNReal) (homothetyS δ_coarse a b '' A'') =
        Metric.externalCoveringNumber δ_fine.toNNReal A'' :=
      homothety_preserves_coveringNumber hδ_fine_pos hδ_coarse_pos a b A''
    rw [h_homot_A, h_homot_A'']
    exact h_metric
  have h_result : IsSetBetweenScales P'' δ_fine δ_coarse s (C / (c / 9)) :=
    between_scales_subset_density hδ_fine_pos hδ_coarse_pos hδ_fine_le_coarse
      hs_nonneg hC_pos (by positivity) h_between hsub hdensity_metric
  have h_const : C / (c / 9) = 9 * C / c := by
    field_simp [hc_pos.ne'] <;> ring
  rw [h_const] at h_result
  exact h_result

/-- Regularity transfer under density-controlled subset.

    If P is (s,C,K)-regular between δ and Δ, and P'' ⊆ P has per-square
    dyadic density c, then P'' is (s, 9C/c, K)-regular between δ and Δ.
    The half-scale bound transfers by monotonicity (S' ⊆ S), so K is unchanged. -/
lemma uniformisation_regular_transfer
    {δ_fine δ_coarse s C K c : ℝ}
    {P P'' : Set EuclideanPlane}
    (hδ_fine_pos : 0 < δ_fine)
    (hδ_fine_dyadic : δ_fine ∈ dyadicScales)
    (hδ_coarse_pos : 0 < δ_coarse)
    (hδ_fine_le_coarse : δ_fine ≤ δ_coarse)
    (hs_nonneg : 0 ≤ s)
    (hC_pos : 0 < C)
    (hK_pos : 0 < K)
    (hc_pos : 0 < c)
    (hP_bounded : Bornology.IsBounded P)
    (hP''_bounded : Bornology.IsBounded P'')
    (h_regular : IsRegularBetweenScales P δ_fine δ_coarse s C K)
    (hsub : P'' ⊆ P)
    (hdensity_dyadic : ∀ (a b : ℤ), (P'' ∩ dyadicSquare δ_coarse a b).Nonempty →
        (dyadicSquareCount δ_fine (P'' ∩ dyadicSquare δ_coarse a b) : ENNReal) ≥
        ENNReal.ofReal c * (dyadicSquareCount δ_fine (P ∩ dyadicSquare δ_coarse a b) : ENNReal)) :
    IsRegularBetweenScales P'' δ_fine δ_coarse s (9 * C / c) K := by
  have h_between : IsSetBetweenScales P'' δ_fine δ_coarse s (9 * C / c) :=
    uniformisation_Sset_transfer hδ_fine_pos hδ_fine_dyadic hδ_coarse_pos hδ_fine_le_coarse
      hs_nonneg hC_pos hc_pos hP_bounded hP''_bounded h_regular.1 hsub hdensity_dyadic
  have h_halfscale : ∀ (a b : ℤ), (P'' ∩ dyadicSquare δ_coarse a b).Nonempty →
      (Metric.externalCoveringNumber (Real.sqrt (δ_fine / δ_coarse)).toNNReal
         (homothetyS δ_coarse a b '' (P'' ∩ dyadicSquare δ_coarse a b)) : ENNReal) ≤
      ENNReal.ofReal (K * Real.rpow (δ_fine / δ_coarse) (-s / 2)) := by
    intro a b hnonempty
    have hP_nonempty : (P ∩ dyadicSquare δ_coarse a b).Nonempty := by
      rcases hnonempty with ⟨z, hz⟩
      exact ⟨z, hsub hz.1, hz.2⟩
    have hS'_sub : (homothetyS δ_coarse a b '' (P'' ∩ dyadicSquare δ_coarse a b)) ⊆
        (homothetyS δ_coarse a b '' (P ∩ dyadicSquare δ_coarse a b)) := by
      intro x hx
      rcases hx with ⟨y, hy, rfl⟩
      have hy1 : y ∈ P'' := hy.1
      have hy2 : y ∈ dyadicSquare δ_coarse a b := hy.2
      exact ⟨y, ⟨hsub hy1, hy2⟩, rfl⟩
    have h_bound : (Metric.externalCoveringNumber (Real.sqrt (δ_fine / δ_coarse)).toNNReal
         (homothetyS δ_coarse a b '' (P ∩ dyadicSquare δ_coarse a b)) : ENNReal) ≤
        ENNReal.ofReal (K * Real.rpow (δ_fine / δ_coarse) (-s / 2)) :=
      h_regular.2.2 a b hP_nonempty
    have h_mono : (Metric.externalCoveringNumber (Real.sqrt (δ_fine / δ_coarse)).toNNReal
         (homothetyS δ_coarse a b '' (P'' ∩ dyadicSquare δ_coarse a b)) : ENNReal) ≤
       (Metric.externalCoveringNumber (Real.sqrt (δ_fine / δ_coarse)).toNNReal
         (homothetyS δ_coarse a b '' (P ∩ dyadicSquare δ_coarse a b)) : ENNReal) := by
      exact_mod_cast Metric.externalCoveringNumber_mono_set hS'_sub
    exact le_trans h_mono h_bound
  exact ⟨h_between, hK_pos, h_halfscale⟩

/-- parentBy composition. -/
lemma parentBy_comp (m1 m2 : ℕ) (x : ℤ × ℤ) :
    BasicUniformization.parentBy m1 (BasicUniformization.parentBy m2 x) =
    BasicUniformization.parentBy (m1 + m2) x := by
  apply Prod.ext
  · have h_pos1 : (0 : ℤ) < (2 ^ m1 : ℤ) := by positivity
    have h_pos2 : (0 : ℤ) < (2 ^ m2 : ℤ) := by positivity
    have h : (x.1 / (2 ^ m2 : ℤ)) / (2 ^ m1 : ℤ) = x.1 / ((2 ^ m2 : ℤ) * (2 ^ m1 : ℤ)) :=
      BasicUniformization.int_ediv_ediv x.1 h_pos2 h_pos1
    simpa [BasicUniformization.parentBy, pow_add, mul_comm] using h
  · have h_pos1 : (0 : ℤ) < (2 ^ m1 : ℤ) := by positivity
    have h_pos2 : (0 : ℤ) < (2 ^ m2 : ℤ) := by positivity
    have h : (x.2 / (2 ^ m2 : ℤ)) / (2 ^ m1 : ℤ) = x.2 / ((2 ^ m2 : ℤ) * (2 ^ m1 : ℤ)) :=
      BasicUniformization.int_ediv_ediv x.2 h_pos2 h_pos1
    simpa [BasicUniformization.parentBy, pow_add, mul_comm] using h

/-- parentBy 0 is the identity. -/
lemma parentBy_zero (x : ℤ × ℤ) :
    BasicUniformization.parentBy 0 x = x := by
  simp [BasicUniformization.parentBy]

/-- Connect RangeUniformityProp to branching process bounds.
    Given range uniformity, monotone exponents, and unit-grid containment,
    produce level counts K satisfying K₀=1, Kₙ=|S|, and
    Kⱼ·Nⱼ ≤ Kⱼ₊₁ < Kⱼ·2Nⱼ. -/
lemma range_uniformity_branching {n : ℕ} {a : Fin (n + 1) → ℕ}
    {S : Finset (ℤ × ℤ)} {N : Fin n → ℕ}
    (h_range : BasicUniformization.RangeUniformityProp n a S N)
    (h_a0 : a 0 = 0)
    (h_a_mono : ∀ (i : Fin n), a i.castSucc ≤ a (Fin.succ i))
    (h_a_last : ∀ (i : Fin (n + 1)), a i ≤ a (Fin.last n))
    (h_unit : ∀ idx ∈ S, 0 ≤ idx.1 ∧ 0 ≤ idx.2 ∧
      idx.1 < (2 : ℤ)^(a (Fin.last n)) ∧ idx.2 < (2 : ℤ)^(a (Fin.last n))) :
    ∃ (K : ℕ → ℕ), K 0 = 1 ∧ K n = S.card ∧
      ∀ (j : ℕ) (hj : j < n),
        K j * N ⟨j, hj⟩ ≤ K (j + 1) ∧
        K (j + 1) < K j * 2 * N ⟨j, hj⟩ := by
  let K : ℕ → ℕ := fun j =>
    if h : j ≤ n then
      have h' : j < n + 1 := by omega
      (S.image (BasicUniformization.parentBy (a (Fin.last n) - a ⟨j, h'⟩))).card
    else 0
  have hK0 : K 0 = 1 := by
    have h' : 0 < n + 1 := by omega
    have h_img : S.image (BasicUniformization.parentBy (a (Fin.last n))) = {(0, 0)} := by
      ext p
      simp only [Finset.mem_image, Finset.mem_singleton]
      constructor
      · rintro ⟨i, hi, h_eq⟩
        have h3 : 0 ≤ i.1 := (h_unit i hi).1
        have h4 : 0 ≤ i.2 := (h_unit i hi).2.1
        have h5 : i.1 < (2 : ℤ)^(a (Fin.last n)) := (h_unit i hi).2.2.1
        have h6 : i.2 < (2 : ℤ)^(a (Fin.last n)) := (h_unit i hi).2.2.2
        have h7 : BasicUniformization.parentBy (a (Fin.last n)) i = (0, 0) := by
          simp [BasicUniformization.parentBy, Int.ediv_eq_zero_of_lt, h3, h4, h5, h6] <;> omega
        rw [h7] at h_eq
        exact h_eq.symm
      · intro h_eq
        rcases h_range.1 with ⟨idx, hidx⟩
        have h1 : 0 ≤ idx.1 := (h_unit idx hidx).1
        have h2 : 0 ≤ idx.2 := (h_unit idx hidx).2.1
        have h3 : idx.1 < (2 : ℤ)^(a (Fin.last n)) := (h_unit idx hidx).2.2.1
        have h4 : idx.2 < (2 : ℤ)^(a (Fin.last n)) := (h_unit idx hidx).2.2.2
        have h5 : BasicUniformization.parentBy (a (Fin.last n)) idx = (0, 0) := by
          simp [BasicUniformization.parentBy, Int.ediv_eq_zero_of_lt, h1, h2, h3, h4] <;> omega
        refine ⟨idx, hidx, ?_⟩
        rw [h5] <;> exact h_eq.symm
    simp [K, h_a0, h_img]
  have hKn : K n = S.card := by
    have h' : n < n + 1 := by omega
    have h_diff : a (Fin.last n) - a ⟨n, h'⟩ = 0 := by
      simp [Fin.last] <;> omega
    have h_img : S.image (BasicUniformization.parentBy (a (Fin.last n) - a ⟨n, h'⟩)) = S := by
      rw [h_diff]
      ext x
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨y, hy, h_eq⟩
        have h_id : BasicUniformization.parentBy 0 y = y := parentBy_zero y
        rw [h_id] at h_eq
        exact h_eq ▸ hy
      · intro hx
        exact ⟨x, hx, parentBy_zero x⟩
    simp [K, h', h_img]
  have h_main : ∀ (j : ℕ) (hj : j < n),
      K j * N ⟨j, hj⟩ ≤ K (j + 1) ∧
      K (j + 1) < K j * 2 * N ⟨j, hj⟩ := by
    intro j hj
    have h_j_le : j ≤ n := by linarith
    have h_j_lt : j < n + 1 := by omega
    have h_j1_le : j + 1 ≤ n := by linarith
    have h_j1_lt : j + 1 < n + 1 := by omega
    set m_fine : ℕ := a (Fin.last n) - a (Fin.succ ⟨j, hj⟩) with hm_fine_def
    set m_coarse : ℕ := a (Fin.last n) - a ⟨j, h_j_lt⟩ with hm_coarse_def
    set m_step : ℕ := a (Fin.succ ⟨j, hj⟩) - a ⟨j, h_j_lt⟩ with hm_step_def
    set fine : Finset (ℤ × ℤ) := S.image (BasicUniformization.parentBy m_fine) with hfine_def
    set coarse : Finset (ℤ × ℤ) := S.image (BasicUniformization.parentBy m_coarse) with hcoarse_def
    set f : (ℤ × ℤ) → (ℤ × ℤ) := BasicUniformization.parentBy m_step with hf_def
    have h_mono1 : a ⟨j, h_j_lt⟩ ≤ a (Fin.succ ⟨j, hj⟩) := h_a_mono ⟨j, hj⟩
    have h_mono2 : a (Fin.succ ⟨j, hj⟩) ≤ a (Fin.last n) := h_a_last (Fin.succ ⟨j, hj⟩)
    have h_add : m_fine + m_step = m_coarse := by
      simp only [hm_fine_def, hm_coarse_def, hm_step_def]
      have h1 : a ⟨j, h_j_lt⟩ ≤ a (Fin.succ ⟨j, hj⟩) := h_mono1
      have h2 : a (Fin.succ ⟨j, hj⟩) ≤ a (Fin.last n) := h_mono2
      omega
    have h_image : fine.image f = coarse := by
      ext g
      simp only [hfine_def, hcoarse_def, Finset.mem_image]
      constructor
      · rintro ⟨h, ⟨idx, hidx, rfl⟩, rfl⟩
        refine ⟨idx, hidx, ?_⟩
        have h_comp : f (BasicUniformization.parentBy m_fine idx) = BasicUniformization.parentBy m_coarse idx := by
          rw [hf_def]
          have h : BasicUniformization.parentBy m_step (BasicUniformization.parentBy m_fine idx) =
                     BasicUniformization.parentBy (m_step + m_fine) idx := parentBy_comp m_step m_fine idx
          rw [h, show m_step + m_fine = m_coarse by omega]
        exact h_comp.symm
      · rintro ⟨idx, hidx, rfl⟩
        let h := BasicUniformization.parentBy m_fine idx
        refine ⟨h, ⟨idx, hidx, rfl⟩, ?_⟩
        have h_comp : f h = BasicUniformization.parentBy m_coarse idx := by
          rw [hf_def]
          have h : BasicUniformization.parentBy m_step (BasicUniformization.parentBy m_fine idx) =
                     BasicUniformization.parentBy (m_step + m_fine) idx := parentBy_comp m_step m_fine idx
          rw [h, show m_step + m_fine = m_coarse by omega]
        exact h_comp
    have h_sum : fine.card = ∑ g ∈ coarse, (fine.filter (fun h => f h = g)).card := by
      rw [Finset.card_eq_sum_card_image f fine, h_image]
    have h_fiber : ∀ g ∈ coarse,
        N ⟨j, hj⟩ ≤ (fine.filter (fun h => f h = g)).card ∧
        (fine.filter (fun h => f h = g)).card < 2 * N ⟨j, hj⟩ := by
      intro g hg
      have h_nonempty : (fine.filter (fun h => f h = g)).Nonempty := by
        rcases Finset.mem_image.mp hg with ⟨idx, hidx, h_eq⟩
        let h := BasicUniformization.parentBy m_fine idx
        have h_h_in : h ∈ fine := Finset.mem_image.mpr ⟨idx, hidx, rfl⟩
        have h_fh : f h = g := by
          rw [hf_def]
          have h_comp : BasicUniformization.parentBy m_step (BasicUniformization.parentBy m_fine idx) =
                         BasicUniformization.parentBy m_coarse idx := by
            have h := parentBy_comp m_step m_fine idx
            rw [h, show m_step + m_fine = m_coarse by omega]
          rw [h_comp, h_eq]
        exact ⟨h, Finset.mem_filter.mpr ⟨h_h_in, h_fh⟩⟩
      have h_pos : 0 < (fine.filter (fun h => f h = g)).card :=
        Finset.Nonempty.card_pos h_nonempty
      have h_range_j := h_range.2.2 ⟨j, hj⟩ g
      have h_f_eq : f = BasicUniformization.parentBy m_step := by
        funext y; rw [hf_def]
      have h_count_eq : (fine.filter (fun h => f h = g)).card =
          (fine.filter (fun idx => BasicUniformization.parentBy m_step idx = g)).card := by
        rw [h_f_eq]
      rw [h_count_eq]
      have h_ne_zero : (fine.filter (fun idx => BasicUniformization.parentBy m_step idx = g)).card ≠ 0 := by
        rw [←h_count_eq]
        exact Nat.ne_of_gt h_pos
      have h := h_range_j.resolve_left h_ne_zero
      exact h
    have h_lower : K j * N ⟨j, hj⟩ ≤ K (j + 1) := by
      have hKj : K j = coarse.card := by
        simp [K, h_j_le, hcoarse_def] <;> rfl
      have hKj1 : K (j + 1) = fine.card := by
        simp [K, h_j1_le, hfine_def] <;> rfl
      rw [hKj, hKj1, h_sum]
      have h : ∑ g ∈ coarse, (fine.filter (fun h => f h = g)).card ≥
          ∑ g ∈ coarse, N ⟨j, hj⟩ := by
        apply Finset.sum_le_sum
        intro g hg
        exact (h_fiber g hg).1
      have h2 : ∑ g ∈ coarse, N ⟨j, hj⟩ = coarse.card * N ⟨j, hj⟩ := by
        rw [Finset.sum_const] <;> ring
      rw [h2] at h
      exact h
    have h_upper : K (j + 1) < K j * 2 * N ⟨j, hj⟩ := by
      have hKj : K j = coarse.card := by
        simp [K, h_j_le, hcoarse_def] <;> rfl
      have hKj1 : K (j + 1) = fine.card := by
        simp [K, h_j1_le, hfine_def] <;> rfl
      rw [hKj, hKj1, h_sum]
      have h_coarse_nonempty : coarse.Nonempty := by
        rcases h_range.1 with ⟨idx, hidx⟩
        exact ⟨BasicUniformization.parentBy m_coarse idx, Finset.mem_image.mpr ⟨idx, hidx, rfl⟩⟩
      have h : ∑ g ∈ coarse, (fine.filter (fun h => f h = g)).card <
          ∑ g ∈ coarse, 2 * N ⟨j, hj⟩ := by
        apply Finset.sum_lt_sum_of_nonempty h_coarse_nonempty
        intro g hg
        exact (h_fiber g hg).2
      have h2 : ∑ g ∈ coarse, 2 * N ⟨j, hj⟩ = coarse.card * (2 * N ⟨j, hj⟩) := by
        rw [Finset.sum_const] <;> ring
      rw [h2] at h
      have h3 : coarse.card * (2 * N ⟨j, hj⟩) = coarse.card * 2 * N ⟨j, hj⟩ := by ring
      rw [h3] at h
      exact h
    exact ⟨h_lower, h_upper⟩
  exact ⟨K, hK0, hKn, h_main⟩

/-! ### Global S-set transfer by covering number ratio -/

/-- Transfer the S-set property from `P` to a subset `P'` using a global ratio
    of external covering numbers. If `externalCover(P) ≤ K · externalCover(P')`,
    then `P'` is a `(δ, s, C·K)`-set.

    This is the key lemma that allows multi-scale uniformisation: the total
    density loss from the uniformisation product becomes a multiplicative
    constant in the S-set bound. -/
lemma sset_transfer_global {X : Type*} [PseudoMetricSpace X] {δ s C K : ℝ}
    {P P' : Set X}
    (hδ_pos : 0 < δ) (hC_pos : 0 < C) (hK_pos : 0 < K)
    (hP_sset : IsDeltaSSet δ s C P)
    (hsub : P' ⊆ P)
    (h_ratio : (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) ≤
               ENNReal.ofReal K * (Metric.externalCoveringNumber δ.toNNReal P' : ENNReal)) :
    IsDeltaSSet δ s (C * K) P' := by
  have hP_nonempty : P.Nonempty := hP_sset.1
  have hs_nonneg : 0 ≤ s := hP_sset.2.2.2.1
  have hP'_nonempty : P'.Nonempty := by
    by_contra h
    have h_empty : P' = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    have h_cover0 : (Metric.externalCoveringNumber δ.toNNReal P' : ENNReal) = 0 := by
      rw [h_empty]
      simp
    rw [h_cover0] at h_ratio
    have h9 : (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) ≤ 0 := by
      simpa [mul_zero] using h_ratio
    have h10 : (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) = 0 := by
      simpa using h9
    have h11 : Metric.externalCoveringNumber δ.toNNReal P = 0 := by
      exact_mod_cast h10
    have h12 : P = ∅ := (Metric.externalCoveringNumber_eq_zero).mp h11
    exact hP_nonempty.ne_empty h12
  refine ⟨hP'_nonempty, hδ_pos, mul_pos hC_pos hK_pos, hs_nonneg, ?_⟩
  intro x r hr
  have h1 : (Metric.externalCoveringNumber δ.toNNReal (P' ∩ Metric.closedBall x r) : ENNReal) ≤
      (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) : ENNReal) := by
    exact_mod_cast Metric.externalCoveringNumber_mono_set (Set.inter_subset_inter_left _ hsub)
  have h2 : (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) : ENNReal) ≤
      ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
        (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := hP_sset.2.2.2.2 x r hr
  have h3 : ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
        (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) ≤
      ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
        (ENNReal.ofReal K * (Metric.externalCoveringNumber δ.toNNReal P' : ENNReal)) := by
    gcongr
  have h4 : ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
        (ENNReal.ofReal K * (Metric.externalCoveringNumber δ.toNNReal P' : ENNReal)) =
      ENNReal.ofReal (C * K) * (ENNReal.ofReal r) ^ s *
        (Metric.externalCoveringNumber δ.toNNReal P' : ENNReal) := by
    have h5 : ENNReal.ofReal C * ENNReal.ofReal K = ENNReal.ofReal (C * K) := by
      rw [← ENNReal.ofReal_mul hC_pos.le]
    calc
      ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
          (ENNReal.ofReal K * (Metric.externalCoveringNumber δ.toNNReal P'))
        = (ENNReal.ofReal C * ENNReal.ofReal K) * (ENNReal.ofReal r) ^ s *
            (Metric.externalCoveringNumber δ.toNNReal P') := by ring
      _ = ENNReal.ofReal (C * K) * (ENNReal.ofReal r) ^ s *
            (Metric.externalCoveringNumber δ.toNNReal P') := by rw [h5]
  calc
    (Metric.externalCoveringNumber δ.toNNReal (P' ∩ Metric.closedBall x r) : ENNReal)
      ≤ (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) : ENNReal) := h1
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
          (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := h2
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
          (ENNReal.ofReal K * (Metric.externalCoveringNumber δ.toNNReal P' : ENNReal)) := h3
    _ = ENNReal.ofReal (C * K) * (ENNReal.ofReal r) ^ s *
          (Metric.externalCoveringNumber δ.toNNReal P' : ENNReal) := h4

/-! ### Multi-level uniformisation with S-set transfer (full SL-5) -/

/-- Given a dyadic-scale set `P = setFromIndices δ S` that is a `(δ, s, C)`-set,
    and a strictly increasing sequence of dyadic exponents `a`, produce a subset
    `P' = setFromIndices δ S'` that:
    1. Has `RangeUniformityProp` at all intermediate scales
    2. Is still a `(δ, s, C')`-set with `C' = 9 · C · ∏ (12 · log(M_j))`

    The constant amplification is polylogarithmic in the scale ratios, with no
    polynomial-in-δ loss. This is the core of OS Lemma 5 (Uniformisation lemma). -/
theorem uniformisation_full_sset
    (nδ : ℕ) (n : ℕ) (a : Fin (n + 1) → ℕ)
    (ha_strict : ∀ j : Fin n, a j.castSucc < a (Fin.succ j))
    (S : Finset (ℤ × ℤ)) (hS_nonempty : S.Nonempty)
    (s C : ℝ) (hC_pos : 0 < C) (hs_nonneg : 0 ≤ s)
    (P : Set EuclideanPlane)
    (hP_eq : P = BasicUniformization.setFromIndices (dyadicDelta nδ) S)
    (hP_bounded : Bornology.IsBounded P)
    (hP_sset : IsDeltaSSet (dyadicDelta nδ) s C P) :
    ∃ (S' : Finset (ℤ × ℤ)) (N : Fin n → ℕ),
      S' ⊆ S ∧
      BasicUniformization.RangeUniformityProp n a S' N ∧
      IsDeltaSSet (dyadicDelta nδ) s
        (9 * C * ∏ j : Fin n, (12 * Real.log ((BasicUniformization.childrenPerParent
          (a (Fin.succ j) - a j.castSucc) : ℝ))))
        (BasicUniformization.setFromIndices (dyadicDelta nδ) S') := by
  let δ := dyadicDelta nδ
  have hδ_pos : 0 < δ := DyadicCubes.dyadicDelta_pos nδ
  rcases BasicUniformization.multi_level_indices n a ha_strict S hS_nonempty with
    ⟨S', N, hS'_sub, h_unif, h_density⟩
  let D : ℝ := ∏ j : Fin n, (12 * Real.log ((BasicUniformization.childrenPerParent
      (a (Fin.succ j) - a j.castSucc) : ℝ)))
  have hD_pos : 0 < D := by
    apply Finset.prod_pos
    intro j _
    have hm_pos : 0 < a (Fin.succ j) - a j.castSucc := Nat.sub_pos_of_lt (ha_strict j)
    have h1 : 1 < (BasicUniformization.childrenPerParent (a (Fin.succ j) - a j.castSucc) : ℝ) := by
      exact_mod_cast BasicUniformization.childrenPerParent_gt_one hm_pos
    have h2 : 0 < Real.log ((BasicUniformization.childrenPerParent (a (Fin.succ j) - a j.castSucc) : ℝ)) :=
      Real.log_pos h1
    linarith
  have h_density' : (S.card : ℝ) ≤ D * (S'.card : ℝ) := by
    have h : (S'.card : ℝ) * D ≥ (S.card : ℝ) := by simpa [D] using h_density
    have h_comm : (S'.card : ℝ) * D = D * (S'.card : ℝ) := by ring
    rw [h_comm] at h
    exact h
  let P' := BasicUniformization.setFromIndices δ S'
  have hP'_bounded : Bornology.IsBounded P' :=
    BasicUniformization.setFromIndices_isBounded nδ S'
  have hP'_sub : P' ⊆ P := by
    rw [hP_eq]
    exact BasicUniformization.setFromIndices_subset hS'_sub
  have hS'_nonempty : S'.Nonempty := h_unif.1
  have h_count_P : DyadicCubes.dyadicCoveringNumber nδ P hP_bounded = S.card := by
    have hP_bounded' : Bornology.IsBounded (BasicUniformization.setFromIndices δ S) :=
      BasicUniformization.setFromIndices_isBounded nδ S
    have h : DyadicCubes.dyadicCoveringNumber nδ (BasicUniformization.setFromIndices δ S) hP_bounded' = S.card :=
      BasicUniformization.count_eq_card nδ S hS_nonempty
    simpa [hP_eq] using h
  have h_count_P' : DyadicCubes.dyadicCoveringNumber nδ P' hP'_bounded = S'.card :=
    BasicUniformization.count_eq_card nδ S' hS'_nonempty
  have h_ext_le_dyadic_P : (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) ≤
      ↑(DyadicCubes.dyadicCoveringNumber nδ P hP_bounded) := by
    exact_mod_cast DyadicCubes.dyadicCoveringNumber_le_external nδ hP_bounded
  have h_dyadic_le_ext_P' : (↑(DyadicCubes.dyadicCoveringNumber nδ P' hP'_bounded) : ENNReal) ≤
      (9 : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal P' : ENNReal) := by
    have h := DyadicCubes.externalCoveringNumber_le_dyadic nδ hP'_bounded
    exact_mod_cast h
  have h_card_ratio : (↑S.card : ENNReal) ≤ ENNReal.ofReal D * (↑S'.card : ENNReal) := by
    have h_real : (S.card : ℝ) ≤ D * (S'.card : ℝ) := h_density'
    have h3 : (↑S.card : ENNReal) ≤ ENNReal.ofReal ((S.card : ℝ)) := by exact_mod_cast le_refl _
    have h4 : ENNReal.ofReal ((S.card : ℝ)) ≤ ENNReal.ofReal (D * (S'.card : ℝ)) := by
      exact ENNReal.ofReal_le_ofReal h_real
    have h5 : ENNReal.ofReal (D * (S'.card : ℝ)) = ENNReal.ofReal D * (↑S'.card : ENNReal) := by
      simp [mul_comm]
      <;> ring
    rw [h5] at h4
    exact le_trans h3 h4
  have h_ratio : (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) ≤
      ENNReal.ofReal (9 * D) * (Metric.externalCoveringNumber δ.toNNReal P' : ENNReal) := by
    calc
      (Metric.externalCoveringNumber δ.toNNReal P : ENNReal)
        ≤ ↑(DyadicCubes.dyadicCoveringNumber nδ P hP_bounded) := h_ext_le_dyadic_P
      _ = ↑S.card := by rw [h_count_P]
      _ ≤ ENNReal.ofReal D * ↑S'.card := h_card_ratio
      _ = ENNReal.ofReal D * ↑(DyadicCubes.dyadicCoveringNumber nδ P' hP'_bounded) := by
          rw [h_count_P']
      _ ≤ ENNReal.ofReal D * ((9 : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal P' : ENNReal)) := by
          gcongr
      _ = ENNReal.ofReal (9 * D) * (Metric.externalCoveringNumber δ.toNNReal P' : ENNReal) := by
          have h6 : ENNReal.ofReal D * ((9 : ENNReal) * (Metric.externalCoveringNumber δ.toNNReal P')) =
              (9 : ENNReal) * ENNReal.ofReal D * (Metric.externalCoveringNumber δ.toNNReal P') := by ring
          rw [h6]
          have h71 : (9 : ENNReal) = ENNReal.ofReal (9 : ℝ) := by norm_cast
          rw [h71]
          have h72 : ENNReal.ofReal (9 : ℝ) * ENNReal.ofReal D = ENNReal.ofReal (9 * D) := by
            rw [← ENNReal.ofReal_mul (by positivity)]
            <;> norm_cast
          rw [h72] <;> ring
  let C' := 9 * C * D
  have hC'_pos : 0 < C' := by positivity
  have h_main : IsDeltaSSet δ s C' P' := by
    have h9 : C * (9 * D) = C' := by ring
    have h_tmp : IsDeltaSSet δ s (C * (9 * D)) P' :=
      sset_transfer_global (δ := δ) (s := s) (C := C) (K := 9 * D)
        hδ_pos hC_pos (by positivity) hP_sset hP'_sub h_ratio
    rw [h9] at h_tmp
    exact h_tmp
  exact ⟨S', N, hS'_sub, h_unif, h_main⟩

/-! ### Balance argument (OS Lemma 5) -/

/-- If S'' ⊆ S and both are range-uniform with factors N'' and N,
    then N'' j ≤ 2 * N j at every level. -/
lemma uniform_subset_branching_bound
    {n : ℕ} {a : Fin (n + 1) → ℕ}
    {S S'' : Finset (ℤ × ℤ)} {N N'' : Fin n → ℕ}
    (hS''_sub : S'' ⊆ S)
    (h_unif_S : BasicUniformization.RangeUniformityProp n a S N)
    (h_unif_S'' : BasicUniformization.RangeUniformityProp n a S'' N'') :
    ∀ (j : Fin n), N'' j ≤ 2 * N j := by
  intro j
  let m_fine := a (Fin.last n) - a (Fin.succ j)
  let m_coarse := a (Fin.succ j) - a j.castSucc
  let fineS := S.image (BasicUniformization.parentBy m_fine)
  let fineS'' := S''.image (BasicUniformization.parentBy m_fine)
  have hfine_sub : fineS'' ⊆ fineS := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
    exact Finset.mem_image.mpr ⟨y, hS''_sub hy, rfl⟩
  have h_main : ∃ (g : ℤ × ℤ), g ∈ fineS''.image (BasicUniformization.parentBy m_coarse) := by
    have h : (fineS''.image (BasicUniformization.parentBy m_coarse)).Nonempty :=
      (h_unif_S''.1.image _).image _
    exact h
  rcases h_main with ⟨g, hg⟩
  have h_idx : ∃ (idx : ℤ × ℤ), idx ∈ fineS'' ∧ BasicUniformization.parentBy m_coarse idx = g := by
    simpa [Finset.mem_image] using hg
  rcases h_idx with ⟨idx, hidx_fine, h_eq_g⟩
  have h_count_sub : (fineS''.filter (fun x => BasicUniformization.parentBy m_coarse x = g)).card ≤
      (fineS.filter (fun x => BasicUniformization.parentBy m_coarse x = g)).card := by
    apply Finset.card_le_card
    intro x hx
    have h1 : x ∈ fineS'' := (Finset.mem_filter.mp hx).1
    have h2 : x ∈ fineS := hfine_sub h1
    have h3 : BasicUniformization.parentBy m_coarse x = g := (Finset.mem_filter.mp hx).2
    exact Finset.mem_filter.mpr ⟨h2, h3⟩
  have h_countS''_pos : 0 < (fineS''.filter (fun x => BasicUniformization.parentBy m_coarse x = g)).card := by
    have h1 : idx ∈ fineS'' := hidx_fine
    have h2 : BasicUniformization.parentBy m_coarse idx = g := h_eq_g
    exact Finset.card_pos.mpr ⟨idx, Finset.mem_filter.mpr ⟨h1, h2⟩⟩
  have h_rangeS'' : N'' j ≤ (fineS''.filter (fun x => BasicUniformization.parentBy m_coarse x = g)).card ∧
      (fineS''.filter (fun x => BasicUniformization.parentBy m_coarse x = g)).card < 2 * N'' j := by
    have h := h_unif_S''.2.2 j g
    cases h with
    | inl h0 => exfalso; exact h_countS''_pos.ne' h0
    | inr h_range => exact h_range
  have h_countS_pos : 0 < (fineS.filter (fun x => BasicUniformization.parentBy m_coarse x = g)).card := by
    have h1 : idx ∈ fineS := hfine_sub hidx_fine
    have h2 : BasicUniformization.parentBy m_coarse idx = g := h_eq_g
    exact Finset.card_pos.mpr ⟨idx, Finset.mem_filter.mpr ⟨h1, h2⟩⟩
  have h_rangeS : N j ≤ (fineS.filter (fun x => BasicUniformization.parentBy m_coarse x = g)).card ∧
      (fineS.filter (fun x => BasicUniformization.parentBy m_coarse x = g)).card < 2 * N j := by
    have h := h_unif_S.2.2 j g
    cases h with
    | inl h0 => exfalso; exact h_countS_pos.ne' h0
    | inr h_range => exact h_range
  have h1 : N'' j ≤ (fineS''.filter (fun x => BasicUniformization.parentBy m_coarse x = g)).card := h_rangeS''.1
  have h2 : (fineS''.filter (fun x => BasicUniformization.parentBy m_coarse x = g)).card ≤
      (fineS.filter (fun x => BasicUniformization.parentBy m_coarse x = g)).card := h_count_sub
  have h3 : (fineS.filter (fun x => BasicUniformization.parentBy m_coarse x = g)).card < 2 * N j := h_rangeS.2
  omega

/-- Core balance argument (OS Lemma 5): if S'' ⊆ S are both range-uniform
    and S'' has global density ≥ 1/M, then at every level j,
    N''_j ≥ N_j / (M · 4^n).

    The product density bound combined with bounded branching ratios
    implies per-level density. -/
lemma per_level_density
    {n : ℕ} {a : Fin (n + 1) → ℕ}
    {S S'' : Finset (ℤ × ℤ)} {N N'' : Fin n → ℕ}
    (hS''_sub : S'' ⊆ S)
    (h_unif_S : BasicUniformization.RangeUniformityProp n a S N)
    (h_unif_S'' : BasicUniformization.RangeUniformityProp n a S'' N'')
    (h_a0 : a 0 = 0)
    (h_a_mono : ∀ (i : Fin n), a i.castSucc ≤ a (Fin.succ i))
    (h_a_last : ∀ (i : Fin (n + 1)), a i ≤ a (Fin.last n))
    (h_unit_S : ∀ idx ∈ S, 0 ≤ idx.1 ∧ 0 ≤ idx.2 ∧
      idx.1 < (2 : ℤ)^(a (Fin.last n)) ∧ idx.2 < (2 : ℤ)^(a (Fin.last n)))
    (h_unit_S'' : ∀ idx ∈ S'', 0 ≤ idx.1 ∧ 0 ≤ idx.2 ∧
      idx.1 < (2 : ℤ)^(a (Fin.last n)) ∧ idx.2 < (2 : ℤ)^(a (Fin.last n)))
    (M : ℝ) (hM_pos : 0 < M)
    (h_density : (S''.card : ℝ) ≥ (S.card : ℝ) / M) :
    ∀ (j : Fin n), (N'' j : ℝ) ≥ (N j : ℝ) / (M * (4 : ℝ)^n) := by
  by_cases hn : n = 0
  · subst hn
    intro j
    exfalso
    exact Fin.elim0 j
  have hn_pos : 0 < n := by omega
  have h_branch_bound : ∀ (j : Fin n), N'' j ≤ 2 * N j :=
    uniform_subset_branching_bound hS''_sub h_unif_S h_unif_S''
  let N' : ℕ → ℕ := fun i => if h : i < n then N ⟨i, h⟩ else 0
  let N''': ℕ → ℕ := fun i => if h : i < n then N'' ⟨i, h⟩ else 0
  rcases range_uniformity_branching h_unif_S h_a0 h_a_mono h_a_last h_unit_S with
    ⟨K, hK0, hKn, hK_branch⟩
  rcases range_uniformity_branching h_unif_S'' h_a0 h_a_mono h_a_last h_unit_S'' with
    ⟨K'', hK''0, hK''n, hK''_branch⟩
  have hK_branch' : ∀ (j : ℕ), j < n →
      K j * N' j ≤ K (j + 1) ∧ K (j + 1) < K j * 2 * N' j := by
    intro j hj
    have h_eq : N' j = N ⟨j, hj⟩ := by simp [N', hj]
    rw [h_eq]
    exact hK_branch j hj
  have hK''_branch' : ∀ (j : ℕ), j < n →
      K'' j * N''' j ≤ K'' (j + 1) ∧ K'' (j + 1) < K'' j * 2 * N''' j := by
    intro j hj
    have h_eq : N''' j = N'' ⟨j, hj⟩ := by simp [N''', hj]
    rw [h_eq]
    exact hK''_branch j hj
  have h_prod_S := branching_product_bound K N' hK0 hK_branch'
  have h_prod_S'' := branching_product_bound K'' N''' hK''0 hK''_branch'
  have h_eq_prod_S : (∏ i ∈ Finset.range n, (N' i : ℝ)) = (∏ j : Fin n, (N j : ℝ)) := by
    let g : ℕ → ℝ := fun i => if h : i < n then (N ⟨i, h⟩ : ℝ) else 0
    have h1 : ∏ i ∈ Finset.range n, (N' i : ℝ) = ∏ i ∈ Finset.range n, g i := by
      apply Finset.prod_congr rfl
      intro i hi
      have hlt : i < n := Finset.mem_range.mp hi
      simp [N', g, hlt]
    rw [h1]
    have h2 : ∏ i ∈ Finset.range n, g i = ∏ j : Fin n, g j := Eq.symm (Fin.prod_univ_eq_prod_range g n)
    rw [h2]
    apply Finset.prod_congr rfl
    intro j _
    simp [g, j.is_lt]
  have h_eq_prod_S'' : (∏ i ∈ Finset.range n, (N''' i : ℝ)) = (∏ j : Fin n, (N'' j : ℝ)) := by
    let g : ℕ → ℝ := fun i => if h : i < n then (N'' ⟨i, h⟩ : ℝ) else 0
    have h1 : ∏ i ∈ Finset.range n, (N''' i : ℝ) = ∏ i ∈ Finset.range n, g i := by
      apply Finset.prod_congr rfl
      intro i hi
      have hlt : i < n := Finset.mem_range.mp hi
      simp [N''', g, hlt]
    rw [h1]
    have h2 : ∏ i ∈ Finset.range n, g i = ∏ j : Fin n, g j := Eq.symm (Fin.prod_univ_eq_prod_range g n)
    rw [h2]
    apply Finset.prod_congr rfl
    intro j _
    simp [g, j.is_lt]
  have h_S_card : (K n : ℝ) = (S.card : ℝ) := by exact_mod_cast hKn
  have h_S''_card : (K'' n : ℝ) = (S''.card : ℝ) := by exact_mod_cast hK''n
  have h_lower_prod : (∏ j : Fin n, (N'' j : ℝ)) ≥
      (∏ j : Fin n, (N j : ℝ)) / (M * (2 : ℝ)^n) := by
    have h2 : (∏ j : Fin n, (N'' j : ℝ)) ≥ (S''.card : ℝ) / (2 : ℝ)^n := by
      rw [←h_eq_prod_S'']
      have h3 : (K'' n : ℝ) ≤ (2 : ℝ)^n * (∏ i ∈ Finset.range n, (N''' i : ℝ)) := h_prod_S''.2
      rw [h_S''_card] at h3
      have hpos : (0 : ℝ) < (2 : ℝ)^n := by positivity
      calc (S''.card : ℝ) / (2 : ℝ)^n
        ≤ ((2 : ℝ)^n * (∏ i ∈ Finset.range n, (N''' i : ℝ))) / (2 : ℝ)^n := by gcongr
      _ = (∏ i ∈ Finset.range n, (N''' i : ℝ)) := by
        field_simp [hpos.ne'] <;> ring
    have h6 : (∏ j : Fin n, (N j : ℝ)) ≤ (S.card : ℝ) := by
      rw [←h_eq_prod_S]
      have h7 : (∏ i ∈ Finset.range n, (N' i : ℝ)) ≤ (K n : ℝ) := by exact_mod_cast h_prod_S.1
      rw [h_S_card] at h7
      exact h7
    calc
      (∏ j : Fin n, (N'' j : ℝ))
        ≥ (S''.card : ℝ) / (2 : ℝ)^n := h2
      _ ≥ ((S.card : ℝ) / M) / (2 : ℝ)^n := by gcongr
      _ = (S.card : ℝ) / (M * (2 : ℝ)^n) := by ring
      _ ≥ (∏ j : Fin n, (N j : ℝ)) / (M * (2 : ℝ)^n) := by gcongr
  intro j
  have hN_pos : ∀ (i : Fin n), 0 < (N i : ℝ) := by
    intro i; have h := h_unif_S.2.1 i; exact_mod_cast h
  have hN''_pos : ∀ (i : Fin n), 0 < (N'' i : ℝ) := by
    intro i; have h := h_unif_S''.2.1 i; exact_mod_cast h
  have h_branch_real : ∀ (i : Fin n), (N'' i : ℝ) ≤ 2 * (N i : ℝ) := by
    intro i; exact_mod_cast h_branch_bound i
  let P_other := (Finset.univ.erase j)
  have h_card_other : P_other.card = n - 1 := by
    simp [P_other, Finset.card_erase_of_mem (Finset.mem_univ j)] <;> omega
  have h_other_prod : (∏ i ∈ P_other, (N'' i : ℝ)) ≤
      (2 : ℝ)^(n - 1) * ∏ i ∈ P_other, (N i : ℝ) := by
    have h1 : ∏ i ∈ P_other, (N'' i : ℝ) ≤ ∏ i ∈ P_other, (2 * (N i : ℝ)) := by
      apply Finset.prod_le_prod
      · intro i _; exact_mod_cast Nat.zero_le (N'' i)
      · intro i _; exact h_branch_real i
    have h2 : ∏ i ∈ P_other, (2 * (N i : ℝ)) = (2 : ℝ)^(n - 1) * ∏ i ∈ P_other, (N i : ℝ) := by
      have h4 : ∏ i ∈ P_other, (2 * (N i : ℝ)) = (∏ i ∈ P_other, (2 : ℝ)) * ∏ i ∈ P_other, (N i : ℝ) := by
        rw [Finset.prod_mul_distrib]
      rw [h4]
      have h5 : (∏ i ∈ P_other, (2 : ℝ)) = (2 : ℝ)^P_other.card := by simp
      rw [h5, h_card_other] <;> ring
    rw [h2] at h1
    exact h1
  have h_other_pos : 0 < ∏ i ∈ P_other, (N i : ℝ) := by
    apply Finset.prod_pos; intro i _; exact hN_pos i
  have h_other''_pos : 0 < ∏ i ∈ P_other, (N'' i : ℝ) := by
    apply Finset.prod_pos; intro i _; exact hN''_pos i
  have h_prod_eq : (∏ i : Fin n, (N'' i : ℝ)) =
      (N'' j : ℝ) * ∏ i ∈ P_other, (N'' i : ℝ) := by
    have h_univ : (Finset.univ : Finset (Fin n)) = insert j P_other := by
      ext x; simp [P_other, Classical.em]
    rw [h_univ]
    rw [Finset.prod_insert (by simp [P_other])]
    <;> rfl
  have h_prod_eq_S : (∏ i : Fin n, (N i : ℝ)) =
      (N j : ℝ) * ∏ i ∈ P_other, (N i : ℝ) := by
    have h_univ : (Finset.univ : Finset (Fin n)) = insert j P_other := by
      ext x; simp [P_other, Classical.em]
    rw [h_univ]
    rw [Finset.prod_insert (by simp [P_other])]
    <;> rfl
  rw [h_prod_eq, h_prod_eq_S] at h_lower_prod
  have h11 : (N'' j : ℝ) * ∏ i ∈ P_other, (N'' i : ℝ) ≥
      ((N j : ℝ) * ∏ i ∈ P_other, (N i : ℝ)) / (M * (2 : ℝ)^n) := h_lower_prod
  have h12 : (N'' j : ℝ) ≥
      ((N j : ℝ) * ∏ i ∈ P_other, (N i : ℝ)) / (M * (2 : ℝ)^n) / (∏ i ∈ P_other, (N'' i : ℝ)) := by
    have h : (N'' j : ℝ) * ∏ i ∈ P_other, (N'' i : ℝ) ≥
        ((N j : ℝ) * ∏ i ∈ P_other, (N i : ℝ)) / (M * (2 : ℝ)^n) := h11
    have h_div_eq : (N'' j : ℝ) =
        ((N'' j : ℝ) * ∏ i ∈ P_other, (N'' i : ℝ)) / (∏ i ∈ P_other, (N'' i : ℝ)) := by
      field_simp [h_other''_pos.ne']
      <;> ring
    have h' : (N'' j : ℝ) ≥ (((N j : ℝ) * ∏ i ∈ P_other, (N i : ℝ)) / (M * (2 : ℝ)^n)) / (∏ i ∈ P_other, (N'' i : ℝ)) := by
      rw [h_div_eq]
      gcongr
    exact h'
  have h_pow_bound : (2 : ℝ)^n * (2 : ℝ)^(n - 1) ≤ (4 : ℝ)^n := by
    have h9 : n ≥ 1 := by omega
    have h10 : (2 : ℝ)^n * (2 : ℝ)^(n - 1) = (2 : ℝ)^(2 * n - 1) := by
      have h11 : n + (n - 1) = 2 * n - 1 := by omega
      rw [← pow_add] <;> rw [h11]
    rw [h10]
    have h12 : (4 : ℝ)^n = (2 : ℝ)^(2 * n) := by
      have h13 : (4 : ℝ) = (2 : ℝ)^2 := by norm_num
      rw [h13, pow_mul] <;> ring
    rw [h12]
    gcongr <;> norm_num <;> omega
  have h13 : (((N j : ℝ) * ∏ i ∈ P_other, (N i : ℝ)) / (M * (2 : ℝ)^n)) / (∏ i ∈ P_other, (N'' i : ℝ)) ≥
      (N j : ℝ) / (M * (4 : ℝ)^n) := by
    have h_ratio : (∏ i ∈ P_other, (N i : ℝ)) / (∏ i ∈ P_other, (N'' i : ℝ)) ≥ 1 / (2 : ℝ)^(n - 1) := by
      have h4 : (∏ i ∈ P_other, (N'' i : ℝ)) ≤ (2 : ℝ)^(n - 1) * (∏ i ∈ P_other, (N i : ℝ)) := h_other_prod
      have h5 : (∏ i ∈ P_other, (N i : ℝ)) / (∏ i ∈ P_other, (N'' i : ℝ)) ≥
          (∏ i ∈ P_other, (N i : ℝ)) / ((2 : ℝ)^(n - 1) * (∏ i ∈ P_other, (N i : ℝ))) := by
        gcongr
      have h6 : (∏ i ∈ P_other, (N i : ℝ)) / ((2 : ℝ)^(n - 1) * (∏ i ∈ P_other, (N i : ℝ))) = 1 / (2 : ℝ)^(n - 1) := by
        field_simp [h_other_pos.ne'] <;> ring
      rw [h6] at h5
      exact h5
    calc
      (((N j : ℝ) * ∏ i ∈ P_other, (N i : ℝ)) / (M * (2 : ℝ)^n)) / (∏ i ∈ P_other, (N'' i : ℝ))
        = (N j : ℝ) / (M * (2 : ℝ)^n) * ((∏ i ∈ P_other, (N i : ℝ)) / (∏ i ∈ P_other, (N'' i : ℝ))) := by ring
      _ ≥ (N j : ℝ) / (M * (2 : ℝ)^n) * (1 / (2 : ℝ)^(n - 1)) := by gcongr
      _ = (N j : ℝ) / (M * ((2 : ℝ)^n * (2 : ℝ)^(n - 1))) := by ring
      _ ≥ (N j : ℝ) / (M * (4 : ℝ)^n) := by
        have h7 : 0 ≤ (N j : ℝ) := by positivity
        exact div_le_div_of_nonneg_left h7 (by positivity) (mul_le_mul_of_nonneg_left h_pow_bound (by positivity))
  exact ge_trans h12 h13

/-- Step 2: Single-level density from per-level branching bound.

For any coarse parent g at level j, if S'' has children below g, then
the ratio of children counts is ≥ 1/(2·M·4^n).

This uses range uniformity: count_S < 2N_j and count_S'' ≥ N''_j ≥ N_j/(M·4^n). -/
lemma single_level_density
    {n : ℕ} {a : Fin (n + 1) → ℕ}
    {S S'' : Finset (ℤ × ℤ)} {N N'' : Fin n → ℕ}
    (h_unif_S : BasicUniformization.RangeUniformityProp n a S N)
    (h_unif_S'' : BasicUniformization.RangeUniformityProp n a S'' N'')
    (M : ℝ) (hM_pos : 0 < M)
    (h_per_level : ∀ (j : Fin n), (N'' j : ℝ) ≥ (N j : ℝ) / (M * (4 : ℝ)^n))
    (j : Fin n) (g : ℤ × ℤ)
    (hS''_sub : S'' ⊆ S)
    (hS''_nonzero :
      let k := a (Fin.last n)
      let m_fine := k - a (Fin.succ j)
      let m_coarse := a (Fin.succ j) - a j.castSucc
      let fineSquares := S''.image (BasicUniformization.parentBy m_fine)
      (fineSquares.filter (fun idx => BasicUniformization.parentBy m_coarse idx = g)).card ≠ 0) :
    (let k := a (Fin.last n)
     let m_fine := k - a (Fin.succ j)
     let m_coarse := a (Fin.succ j) - a j.castSucc
     let fineSquares_S := S.image (BasicUniformization.parentBy m_fine)
     let fineSquares_S'' := S''.image (BasicUniformization.parentBy m_fine)
     let count_S := (fineSquares_S.filter (fun idx => BasicUniformization.parentBy m_coarse idx = g)).card
     let count_S'' := (fineSquares_S''.filter (fun idx => BasicUniformization.parentBy m_coarse idx = g)).card
     (count_S'' : ℝ) ≥ (1 / (2 * M * (4 : ℝ)^n)) * (count_S : ℝ)) := by
  let k := a (Fin.last n)
  let m_fine := k - a (Fin.succ j)
  let m_coarse := a (Fin.succ j) - a j.castSucc
  let fineSquares_S := S.image (BasicUniformization.parentBy m_fine)
  let fineSquares_S'' := S''.image (BasicUniformization.parentBy m_fine)
  let count_S := (fineSquares_S.filter (fun idx => BasicUniformization.parentBy m_coarse idx = g)).card
  let count_S'' := (fineSquares_S''.filter (fun idx => BasicUniformization.parentBy m_coarse idx = g)).card
  have hS''_range : N'' j ≤ count_S'' ∧ count_S'' < 2 * N'' j := by
    have h := h_unif_S''.2.2 j g
    exact h.resolve_left hS''_nonzero
  have hS_range : count_S = 0 ∨ (N j ≤ count_S ∧ count_S < 2 * N j) := h_unif_S.2.2 j g
  have hN_pos : 0 < N j := h_unif_S.2.1 j
  have h_fine_sub : fineSquares_S'' ⊆ fineSquares_S := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
    exact Finset.mem_image.mpr ⟨y, hS''_sub hy, rfl⟩
  have h_filter_sub : (fineSquares_S''.filter (fun idx => BasicUniformization.parentBy m_coarse idx = g)) ⊆
      (fineSquares_S.filter (fun idx => BasicUniformization.parentBy m_coarse idx = g)) :=
    Finset.filter_subset_filter _ h_fine_sub
  have h_count_sub : count_S'' ≤ count_S := Finset.card_le_card h_filter_sub
  have h_count_S_pos : 0 < count_S := by
    cases hS_range with
    | inl h =>
      exfalso
      have h2 : count_S'' = 0 := by omega
      exact hS''_nonzero h2
    | inr h => exact Nat.pos_of_ne_zero (by omega)
  have hS_upper : (count_S : ℝ) < 2 * (N j : ℝ) := by
    cases hS_range with
    | inl h => exfalso; exact h_count_S_pos.ne' h
    | inr h => exact_mod_cast h.2
  have hS''_lower : (count_S'' : ℝ) ≥ (N'' j : ℝ) := by exact_mod_cast hS''_range.1
  have h_main : (N'' j : ℝ) ≥ (N j : ℝ) / (M * (4 : ℝ)^n) := h_per_level j
  have h_c_pos : 0 < 2 * M * (4 : ℝ)^n := by positivity
  dsimp only
  calc (count_S'' : ℝ)
    ≥ (N'' j : ℝ) := hS''_lower
  _ ≥ (N j : ℝ) / (M * (4 : ℝ)^n) := h_main
  _ ≥ (1 / (2 * M * (4 : ℝ)^n)) * (count_S : ℝ) := by
    have h2 : (count_S : ℝ) < 2 * (N j : ℝ) := hS_upper
    have h3 : (1 / (2 * M * (4 : ℝ)^n)) * (count_S : ℝ) < (N j : ℝ) / (M * (4 : ℝ)^n) := by
      calc (1 / (2 * M * (4 : ℝ)^n)) * (count_S : ℝ)
        < (1 / (2 * M * (4 : ℝ)^n)) * (2 * (N j : ℝ)) := by gcongr
      _ = (N j : ℝ) / (M * (4 : ℝ)^n) := by
        field_simp [h_c_pos.ne'] <;> ring
    exact h3.le

/-- Step 3: Full between-scales S-set transfer for one level.

Given a coarse set P with between-scales S-set property at scales (δ_fine, δ_coarse),
and a uniform subset P'' with single-level density c = 1/(2·M·4^n), transfer the
between-scales property to P'' with constant amplified by 9·2·M·4^n.

This is the lemma dune can use for h_normal in the induction. -/
lemma between_scales_transfer_one_level
    {δ_fine δ_coarse s C M : ℝ} {n : ℕ}
    {P P'' : Set EuclideanPlane}
    (hδ_fine_pos : 0 < δ_fine)
    (hδ_fine_dyadic : δ_fine ∈ dyadicScales)
    (hδ_coarse_pos : 0 < δ_coarse)
    (hδ_fine_le_coarse : δ_fine ≤ δ_coarse)
    (hs_nonneg : 0 ≤ s)
    (hC_pos : 0 < C)
    (hM_pos : 0 < M)
    (hn_pos : 0 < n)
    (hP_bounded : Bornology.IsBounded P)
    (hP''_bounded : Bornology.IsBounded P'')
    (h_between : IsSetBetweenScales P δ_fine δ_coarse s C)
    (hsub : P'' ⊆ P)
    (hdensity_dyadic : ∀ (a b : ℤ), (P'' ∩ dyadicSquare δ_coarse a b).Nonempty →
        (dyadicSquareCount δ_fine (P'' ∩ dyadicSquare δ_coarse a b) : ENNReal) ≥
        ENNReal.ofReal (1 / (2 * M * (4 : ℝ)^n)) *
          (dyadicSquareCount δ_fine (P ∩ dyadicSquare δ_coarse a b) : ENNReal)) :
    IsSetBetweenScales P'' δ_fine δ_coarse s (9 * C * 2 * M * (4 : ℝ)^n) := by
  let c := 1 / (2 * M * (4 : ℝ)^n)
  have hc_pos : 0 < c := by positivity
  have h_main : IsSetBetweenScales P'' δ_fine δ_coarse s (9 * C / c) :=
    uniformisation_Sset_transfer hδ_fine_pos hδ_fine_dyadic hδ_coarse_pos hδ_fine_le_coarse
      hs_nonneg hC_pos hc_pos hP_bounded hP''_bounded h_between hsub hdensity_dyadic
  have h_const : 9 * C / c = 9 * C * 2 * M * (4 : ℝ)^n := by
    dsimp only [c]
    have hpos : (0 : ℝ) < 2 * M * (4 : ℝ)^n := by positivity
    field_simp [hpos.ne'] <;> ring
  rw [h_const] at h_main
  exact h_main

end DiscretisedFurstenbergEstimate.OSUniformisation
