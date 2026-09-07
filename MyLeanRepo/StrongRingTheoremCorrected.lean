module

/-
# Strong Ring Theorem — Corrected Proof Skeleton

Proof structure for `strong_ring_theorem` (Proposition 4.1 / `thm.ringstrong`
in Corso-Shmerkin-Wang, Section 4, lines 577-644).

## Critical corrections from deprecated skeleton

1. **All-scale Frostman required**: `IsAllScaleFrostman κ C μ`, NOT
   `IsDirectionFrostman δ κ C μ`. δ-scale Frostman is insufficient for the
   Expansion Theorem (atomic counterexample).
2. **Step 3-5 conclusion**: `δ^{-1+εm}`, NOT `δ^{εm}`.
3. **Step 6-8 gain**: `(1-s)/(24k)` where `k=mN`, NOT a free parameter.
4. **Steps 9-11 exponent**: `cN/(2N+1) - (1-s)/(24k(2N+1))`, NOT `c'/2`.
5. **Step 12 final exponent**: `c = (1-s)/(400·k·(2N+1))`.
6. **ε depends on both κ and s**, not just s.

## 6-step proof outline

1. **Normalize** μ away from 0 → all-scale `(κ,2)`-measure on `[2^{-1/κ},1]`
2. **Expansion Theorem** → `X = N·K^(N)-N·K^(N)` has positive Lebesgue measure
3. **Marstrand m-dim** → `x_1,...,x_m ∈ X` with `Nδ(x_1A+...+x_mA) ≳ δ^{-1+εm}`
4. **Multi-set PR** → extract `y ∈ K^(N)` with `|t^{-1}A - yA| ≳ δ^{-(1-s)/(24k)}|t^{-1}A|`
5. **Iterated Ruzsa triangle** → some `w ∈ {1}∪K` with gain
   `δ^{cN/(2N+1) - (1-s)/(24k(2N+1))}`
6. **Convert to sumset** → final gain `δ^{-c}` with `c = (1-s)/(400k(2N+1))`

## Dependencies

- `MyLeanRepo.ProjectionBasic` — `Nreal`, `IsRealDeltaSet`, `dyadicScales`
- `MyLeanRepo.AllScaleFrostman` — `IsAllScaleFrostman`
- `MyLeanRepo.DiscretizedPluennecke` — Ruzsa triangle
- `MyLeanRepo.RuzsaTriangle` — Ruzsa triangle
- `MyLeanRepo.OSW.RuzsaCorollaries` — sum-to-diff corollary
- `MyLeanRepo.PRCorollaries` — bridge corollaries

## Whiteprint node

`WeakTwoEnds/StrongRing/CorrectedSkeleton`
-/

public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.AllScaleFrostman
public import MyLeanRepo.DiscretizedPluennecke
public import MyLeanRepo.RuzsaTriangle
public import MyLeanRepo.OSW.RuzsaCorollaries
public import MyLeanRepo.StrongRingSteps9_12
public import MyLeanRepo.StrongRingNormalize
public import MyLeanRepo.StrongRingStep6
public import MyLeanRepo.ExpansionTheoremRecursive
public import MyLeanRepo.UniformExpansionLemma
public import MyLeanRepo.Step3_5_MarstrandMDim
public import MyLeanRepo.ProductMeasureBridge
public import MyLeanRepo.OSWPrelude

@[expose] public section


open MeasureTheory ENNReal Set Classical BigOperators

namespace WeakTwoEndsSumProduct

noncomputable section

/-! ## Boundedness helpers -/

lemma bounded_productSetN {A : Set ℝ} {N : ℕ}
    (hA : Bornology.IsBounded A) :
    Bornology.IsBounded (productSetN A N) := by
  have h1 : ∃ (C : ℝ), 0 ≤ C ∧ ∀ x ∈ A, |x| ≤ C := by
    have h2 : ∃ (C : ℝ), ∀ x ∈ A, ‖x‖ ≤ C := isBounded_iff_forall_norm_le.mp hA
    rcases h2 with ⟨C, hC⟩
    refine ⟨max C 0, by positivity, fun x hx => ?_⟩
    have h3 : ‖x‖ ≤ C := hC x hx
    have h4 : |x| ≤ C := by simpa [Real.norm_eq_abs] using h3
    exact h4.trans (le_max_left C 0)
  rcases h1 with ⟨C, hC_nonneg, hC⟩
  have h_main : ∀ x ∈ productSetN A N, |x| ≤ C ^ N := by
    intro x hx
    rcases hx with ⟨f, hf, rfl⟩
    have h1 : ∀ i : Fin N, |f i| ≤ C := fun i => hC (f i) (hf i)
    have h2 : |∏ i : Fin N, f i| = ∏ i : Fin N, |f i| := by
      simpa [Finset.abs_prod] using rfl
    rw [h2]
    have h3 : ∏ i : Fin N, |f i| ≤ ∏ i : Fin N, C := by
      apply Finset.prod_le_prod
      · intro i _; positivity
      · intro i _; exact h1 i
    simpa using h3
  have h4 : productSetN A N ⊆ Set.Icc (-(C ^ N)) (C ^ N) := by
    intro x hx
    have h5 : |x| ≤ C ^ N := h_main x hx
    exact abs_le.mp h5
  have h5 : Bornology.IsBounded (Set.Icc (-(C ^ N)) (C ^ N)) := Metric.isBounded_Icc _ _
  exact h5.subset h4

lemma bounded_sumSetN {A : Set ℝ} {N : ℕ}
    (hA : Bornology.IsBounded A) :
    Bornology.IsBounded (sumSetN A N) := by
  induction N with
  | zero =>
    simp [sumSetN] <;> exact Metric.isBounded_Icc _ _
  | succ N ih =>
    have h : sumSetN A (N + 1) = Set.image2 (· + ·) A (sumSetN A N) := by
      simp [sumSetN]
    rw [h]
    exact hA.add ih

lemma bounded_expansionSet {K : Set ℝ} {N : ℕ}
    (hK : Bornology.IsBounded K) :
    Bornology.IsBounded (expansionSet K N) := by
  have h1 : Bornology.IsBounded (productSetN K N) := bounded_productSetN hK
  have h2 : Bornology.IsBounded (sumSetN (productSetN K N) N) := bounded_sumSetN h1
  exact h2.sub h2

lemma compact_productSetN {K : Set ℝ} {N : ℕ} (hK : IsCompact K) :
    IsCompact (productSetN K N) := by
  let F : Set (Fin N → ℝ) := Set.univ.pi (fun _ => K)
  have hF_compact : IsCompact F := by exact isCompact_univ_pi fun i => hK
  have h_eq : productSetN K N = Set.image (fun f : Fin N → ℝ => ∏ i : Fin N, f i) F := by
    ext x
    simp only [productSetN, F, Set.mem_univ_pi, Set.mem_image]
    <;> aesop
  rw [h_eq]
  exact hF_compact.image (by fun_prop)

lemma compact_sumSetN {A : Set ℝ} {N : ℕ} (hA : IsCompact A) :
    IsCompact (sumSetN A N) := by
  induction N with
  | zero =>
    simpa [sumSetN] using isCompact_singleton
  | succ N ih =>
    have h_prod : IsCompact (A ×ˢ sumSetN A N) := hA.prod ih
    have h_eq : Set.image2 (· + ·) A (sumSetN A N) =
        (fun p : ℝ × ℝ => p.1 + p.2) '' (A ×ˢ sumSetN A N) := by
      ext z
      simp only [Set.mem_image2, Set.mem_image, Set.mem_prod]
      constructor
      · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩
      · rintro ⟨p, ⟨ha, hb⟩, rfl⟩; exact ⟨p.1, ha, p.2, hb, rfl⟩
    have h : IsCompact (Set.image2 (· + ·) A (sumSetN A N)) := by
      rw [h_eq]; exact h_prod.image (continuous_fst.add continuous_snd)
    simpa [sumSetN] using h

lemma compact_expansionSet {K : Set ℝ} {N : ℕ} (hK : IsCompact K) :
    IsCompact (expansionSet K N) := by
  have h1 : IsCompact (productSetN K N) := compact_productSetN hK
  have h2 : IsCompact (sumSetN (productSetN K N) N) := compact_sumSetN h1
  let S := sumSetN (productSetN K N) N
  have h_prod : IsCompact (S ×ˢ S) := h2.prod h2
  have h_eq : Set.image2 (· - ·) S S =
      (fun p : ℝ × ℝ => p.1 - p.2) '' (S ×ˢ S) := by
    ext z
    simp only [Set.mem_image2, Set.mem_image, Set.mem_prod]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩
    · rintro ⟨p, ⟨ha, hb⟩, rfl⟩; exact ⟨p.1, ha, p.2, hb, rfl⟩
  have h_main : IsCompact (Set.image2 (· - ·) S S) := by
    rw [h_eq]; exact h_prod.image (continuous_fst.sub continuous_snd)
  exact h_main

/-- If `K ⊆ [0,1]`, then `expansionSet K N ⊆ [-N, N]`. -/
lemma expansionSet_subset_Icc {K : Set ℝ} {N : ℕ} (hK : K ⊆ Set.Icc 0 1) :
    expansionSet K N ⊆ Set.Icc (-(N : ℝ)) (N : ℝ) := by
  have h1 : productSetN K N ⊆ Set.Icc 0 1 := by
    intro x hx
    rcases hx with ⟨f, hf, rfl⟩
    have h2 : ∀ i, 0 ≤ f i := fun i => (hK (hf i)).1
    have h3 : ∀ i, f i ≤ 1 := fun i => (hK (hf i)).2
    have h4 : 0 ≤ ∏ i : Fin N, f i := Finset.prod_nonneg fun i _ => h2 i
    have h5 : ∏ i : Fin N, f i ≤ 1 := by
      have h6 : ∀ i ∈ Finset.univ, f i ≤ 1 := fun i _ => h3 i
      have h7 : ∏ i : Fin N, f i ≤ ∏ i : Fin N, (1 : ℝ) := Finset.prod_le_prod (fun i _ => h2 i) h6
      simpa using h7
    exact ⟨h4, h5⟩
  have h2 : ∀ n : ℕ, sumSetN (productSetN K N) n ⊆ Set.Icc 0 (n : ℝ) := by
    intro n
    induction n with
    | zero =>
      simp [sumSetN] <;> norm_num
    | succ n ih =>
      intro z hz
      simp only [sumSetN] at hz
      rcases hz with ⟨a, ha, b, hb, rfl⟩
      have ha' : a ∈ Set.Icc 0 1 := h1 ha
      have hb' : b ∈ Set.Icc 0 (n : ℝ) := ih hb
      have ha1 : 0 ≤ a := ha'.1
      have ha2 : a ≤ 1 := ha'.2
      have hb1 : 0 ≤ b := hb'.1
      have hb2 : b ≤ (n : ℝ) := hb'.2
      have h_sum1 : 0 ≤ a + b := by linarith
      have h_sum2 : a + b ≤ ((n + 1 : ℕ) : ℝ) := by
        simp [Nat.cast_add] at * <;> linarith
      exact ⟨h_sum1, h_sum2⟩
  let S := sumSetN (productSetN K N) N
  have hS : S ⊆ Set.Icc 0 (N : ℝ) := h2 N
  intro z hz
  rcases hz with ⟨a, ha, b, hb, rfl⟩
  have ha' : a ∈ Set.Icc 0 (N : ℝ) := hS ha
  have hb' : b ∈ Set.Icc 0 (N : ℝ) := hS hb
  have ha1 : 0 ≤ a := ha'.1
  have ha2 : a ≤ (N : ℝ) := ha'.2
  have hb1 : 0 ≤ b := hb'.1
  have hb2 : b ≤ (N : ℝ) := hb'.2
  exact ⟨by linarith, by linarith⟩

/-! ## Step 1: Normalize μ away from 0 (paper line 587)

    Imported from `MyLeanRepo.StrongRingNormalize.step1_normalize_allscale`. -/
/-! ## Step 2: Expansion Theorem (paper line 591, Theorem 1) -/

/-- Helper: `productSetN` equals `ExpansionLemma.productSet`. -/
lemma productSetN_eq {A : Set ℝ} {n : ℕ} :
    productSetN A n = ExpansionLemma.productSet A n := by
  ext x
  simp [productSetN, ExpansionLemma.productSet]
  <;> rfl

/-- Helper: `sumSetN` equals `ExpansionLemma.iteratedSumset`. -/
lemma sumSetN_eq {A : Set ℝ} {n : ℕ} :
    sumSetN A n = ExpansionLemma.iteratedSumset A n := by
  induction n with
  | zero => simp [sumSetN, ExpansionLemma.iteratedSumset]
  | succ n ih =>
    simp [sumSetN, ExpansionLemma.iteratedSumset, ih] <;> rfl

/-- Helper: `expansionSet K N` equals `ExpansionLemma.iteratedDifference`. -/
lemma expansionSet_eq {K : Set ℝ} {N : ℕ} :
    expansionSet K N = ExpansionLemma.iteratedDifference (ExpansionLemma.productSet K N) N := by
  have h1 : productSetN K N = ExpansionLemma.productSet K N := productSetN_eq
  have h2 : sumSetN (productSetN K N) N = ExpansionLemma.iteratedSumset (ExpansionLemma.productSet K N) N := by
    rw [h1]
    exact sumSetN_eq
  simp only [expansionSet, ExpansionLemma.iteratedDifference, h2]

lemma step2_expansion_allscale
    {κ C : ℝ} (hκ_pos : 0 < κ) (hκ_lt_one : κ < 1) (hC_pos : 0 < C)
    {μ : Measure ℝ} (hμ : IsAllScaleFrostman κ C μ)
    {K : Set ℝ} (hK : K = μ.support)
    (hK_bdd : Bornology.IsBounded K)
    (hK_nonempty : K.Nonempty) :
    ∃ (N : ℕ), 0 < N ∧
      0 < MeasureTheory.volume (expansionSet K N) := by
  have h_exists_n : ∃ (n : ℕ), 1 < (n : ℝ) * κ := by
    have h : ∃ (n : ℕ), (1 : ℝ) / κ < (n : ℝ) := exists_nat_gt (1 / κ)
    rcases h with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hκ_pos' : 0 < κ := hκ_pos
    calc (n : ℝ) * κ > (1 / κ) * κ := by gcongr
      _ = 1 := by field_simp [hκ_pos'.ne']
  rcases h_exists_n with ⟨n, hnκ⟩
  have hn_pos : 0 < n := by
    by_contra h
    have h0 : n = 0 := by omega
    rw [h0] at hnκ
    norm_num at hnκ
  -- Bound K by some R > 0
  have h_exists_R : ∃ (R : ℝ), 0 < R ∧ K ⊆ Set.Icc (-R) R := by
    have h1 : ∃ (r : ℝ), K ⊆ Metric.ball (0 : ℝ) r :=
      (Metric.isBounded_iff_subset_ball (0 : ℝ)).mp hK_bdd
    rcases h1 with ⟨r, hK_ball⟩
    let R : ℝ := max r 1
    have hr_pos : 0 < R := by positivity
    have hK_ball' : K ⊆ Metric.ball (0 : ℝ) R := by
      intro x hx
      have h2 : x ∈ Metric.ball (0 : ℝ) r := hK_ball hx
      have h3 : dist x 0 < r := h2
      have h4 : r ≤ R := le_max_left r 1
      exact Metric.ball_subset_ball h4 h2
    refine ⟨R, hr_pos, ?_⟩
    intro x hx
    have h2 : x ∈ Metric.ball (0 : ℝ) R := hK_ball' hx
    have h3 : |x| < R := by simpa [Metric.mem_ball, dist_zero_right] using h2
    have h4 : -R ≤ x := by linarith [abs_lt.mp h3]
    have h5 : x ≤ R := by linarith [abs_lt.mp h3]
    exact ⟨h4, h5⟩
  rcases h_exists_R with ⟨R, hR_pos, hK_subset_R⟩
  let C' : ℝ := max C R
  have hC'_pos : 0 < C' := by positivity
  have hC_le_C' : C ≤ C' := le_max_left C R
  have hμ' : IsAllScaleFrostman κ C' μ := hμ.mono hC_le_C'
  have hK_subset_C' : K ⊆ Set.Icc (-C') C' := by
    have hR_le_C' : R ≤ C' := le_max_right C R
    intro x hx
    have h3 : x ∈ Set.Icc (-R) R := hK_subset_R hx
    have h4 : -R ≤ x := h3.1
    have h5 : x ≤ R := h3.2
    have h6 : -C' ≤ -R := by gcongr
    have h7 : -C' ≤ x := le_trans h6 h4
    have h8 : x ≤ C' := le_trans h5 hR_le_C'
    exact ⟨h7, h8⟩
  let h_factory : BoundedExpansionFactory :=
    fun m hm d_max lam_min hd_max_pos hlam_min_pos =>
      ExpansionLemma.expansion_lemma_uniform (n := m) hm (hd_max_pos := hd_max_pos) (hlam_min_pos := hlam_min_pos)
  rcases expansion_theorem_recursive_flat
      hκ_pos hκ_lt_one hC'_pos hn_pos hnκ h_factory
    with ⟨N, c_X, hN_pos, hcX_pos, h_main⟩
  have h_vol : ENNReal.ofReal c_X ≤ MeasureTheory.volume (expansionSet K N) := by
    rw [expansionSet_eq, hK]
    have hμ_supp : μ.support ⊆ Set.Icc (-C') C' := by
      intro x hx
      have h2 : x ∈ K := hK.symm ▸ hx
      exact hK_subset_C' h2
    exact h_main μ hμ' hμ_supp
  have h_pos : 0 < MeasureTheory.volume (expansionSet K N) :=
    lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hcX_pos) h_vol
  exact ⟨N, hN_pos, h_pos⟩

/-- **Step 2 (uniform N version)**: Expansion Theorem with N depending only on κ.

    There exists `N : ℕ` and `c_X > 0` (both depending only on κ) such that for EVERY
    all-scale `(κ, 2^(κ+1))`-Frostman measure μ supported on [0,1], the expansion set
    `N·K^(N) - N·K^(N)` has Lebesgue measure at least `c_X`.

    The constant is fixed at `2^(κ+1)` because the Strong Ring input has
    `1 ≤ C₀ ≤ 2^κ`, and after restriction away from zero the constant becomes
    `2*C₀ ≤ 2^(κ+1)`. Frostman monotonicity then upgrades to `2^(κ+1)`.

    This uniform version is needed so that c (which depends on N) can be chosen
    before the specific measure μ is known. -/
lemma step2_expansion_uniform_N
    {κ : ℝ} (hκ_pos : 0 < κ) (hκ_lt_one : κ < 1)
    (C_val : ℝ) (hC_pos : 0 < C_val) (hC_val_ge_one : 1 ≤ C_val) :
    ∃ (N : ℕ) (c_X : ℝ), 0 < N ∧ 0 < c_X ∧
      ∀ (μ : Measure ℝ),
        IsAllScaleFrostman κ C_val μ →
        μ.support ⊆ Set.Icc 0 1 →
        μ Set.univ = 1 →
        ENNReal.ofReal c_X ≤ MeasureTheory.volume (expansionSet μ.support N) := by
  have h_exists_n : ∃ (n : ℕ), 1 < (n : ℝ) * κ := by
    have h : ∃ (n : ℕ), (1 : ℝ) / κ < (n : ℝ) := exists_nat_gt (1 / κ)
    rcases h with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hκ_pos' : 0 < κ := hκ_pos
    calc (n : ℝ) * κ > (1 / κ) * κ := by gcongr
      _ = 1 := by field_simp [hκ_pos'.ne']
  rcases h_exists_n with ⟨n, hnκ⟩
  have hn_pos : 0 < n := by
    by_contra h
    have h0 : n = 0 := by omega
    rw [h0] at hnκ
    norm_num at hnκ
  let h_factory : WeakTwoEndsSumProduct.BoundedExpansionFactory :=
    fun m hm d_max lam_min hd_max_pos hlam_min_pos =>
      ExpansionLemma.expansion_lemma_uniform (n := m) hm (hd_max_pos := hd_max_pos) (hlam_min_pos := hlam_min_pos)
  rcases WeakTwoEndsSumProduct.expansion_theorem_recursive_flat
      hκ_pos hκ_lt_one hC_pos hn_pos hnκ h_factory
    with ⟨N, c_X, hN_pos, hcX_pos, h_main⟩
  refine ⟨N, c_X, hN_pos, hcX_pos, ?_⟩
  intro μ hμ hμ_supp hμ_univ
  have hμ_supp' : μ.support ⊆ Set.Icc (-C_val) C_val := by
    intro x hx
    have h3 : x ∈ Set.Icc (0 : ℝ) 1 := hμ_supp hx
    have h4 : (0 : ℝ) ≤ x := h3.1
    have h5 : x ≤ (1 : ℝ) := h3.2
    have h6 : -C_val ≤ x := by
      have h7 : -C_val ≤ 0 := by linarith [hC_val_ge_one]
      linarith
    have h8 : x ≤ C_val := by linarith [hC_val_ge_one]
    exact ⟨h6, h8⟩
  rw [expansionSet_eq]
  exact h_main μ hμ hμ_supp'

/-! ## Steps 3–5: Energy + Direction Selection + Marstrand (paper lines 594–601) -/

/-! ## Steps 6–8: Unpack + Multi-set Plünnecke-Ruzsa (paper lines 602–613)

    Provided by `MyLeanRepo.StrongRingStep6.step6_8_full_difference`.
    The ε_tloss parameter absorbs the cubic sum-to-difference loss. -/

/-! ## Steps 9–11: Iterated Ruzsa Triangle (paper lines 617–636)

    Provided by `MyLeanRepo.StrongRingSteps9_12.step9_11_triangle_correct`.
    Accepts `ε_abs` for constant absorption; output exponent is `β + ε_abs`. -/

/-! ## Step 12: Convert to Sumset (paper lines 637–644)

    Provided by `MyLeanRepo.StrongRingSteps9_12.step12_diff_to_sum_correct`.
    Generalized with `β_in` parameter; also see `step12_diff_to_sum_normalized`
    for the normalization-translation wrapper. -/

/-! ## Phase wrappers (decompose main theorem assembly to avoid timeout) -/

/-- Phase 1: Step 1 only. Normalize μ to constant 2, supported away from 0. -/
lemma phase1_normalize
    {κ C₀ : ℝ} (hκ_pos : 0 < κ) (hC₀_pos : 0 < C₀) (hC_le : C₀ ≤ 2 ^ κ)
    {μ : Measure ℝ} (hμ : IsAllScaleFrostman κ C₀ μ)
    (hμ_supp : μ.support ⊆ Set.Icc 0 1)
    (hμ_univ : μ Set.univ = 1) :
    ∃ (μ' : Measure ℝ),
      IsAllScaleFrostman κ (2 * C₀) μ' ∧
      μ'.support ⊆ Set.Icc ((2 : ℝ) ^ (-(1/κ))) 1 ∧
      μ'.support ⊆ μ.support ∧
      μ' Set.univ = 1 := by
  rcases step1_normalize_allscale hκ_pos hC₀_pos hC_le hμ hμ_supp hμ_univ
    with ⟨μ', hμ'_frost, hμ'_supp, hμ'_univ, hμ'_sub⟩
  exact ⟨μ', hμ'_frost, hμ'_supp, hμ'_sub, hμ'_univ⟩

/-- Double normalization: scale μ'.support by b = sSup(μ'.support) so that
    1 ∈ ν.support. Returns b, ν, and all properties needed for the Strong Ring. -/
lemma scale_support_to_contain_one
    {κ C : ℝ} (hκ_pos : 0 < κ) (hC_pos : 0 < C)
    {μ' : Measure ℝ} (hμ'_frost : IsAllScaleFrostman κ C μ')
    (hμ'_supp : μ'.support ⊆ Set.Icc ((2:ℝ)^(-(1/κ))) 1)
    (hμ'_univ : μ' Set.univ = 1) :
    ∃ (b : ℝ) (ν : Measure ℝ),
      0 < b ∧ b ≤ 1 ∧ (2:ℝ)^(-(1/κ)) ≤ b ∧
      b ∈ μ'.support ∧ (∀ x ∈ μ'.support, x ≤ b) ∧
      IsAllScaleFrostman κ C ν ∧
      ν.support = scaleSet b⁻¹ μ'.support ∧
      1 ∈ ν.support ∧
      ν.support ⊆ Set.Icc ((2:ℝ)^(-(1/κ))) 1 ∧
      ν Set.univ = 1 := by
  let a : ℝ := (2 : ℝ)^(-(1/κ))
  have ha_pos : 0 < a := by positivity
  have hμ'_ne_zero : μ' ≠ 0 := by
    intro h; rw [h] at hμ'_univ <;> simp at hμ'_univ <;> norm_num at hμ'_univ
  have hK'_nonempty : μ'.support.Nonempty := Measure.nonempty_support_iff.mpr hμ'_ne_zero
  have h_bdd_above : BddAbove μ'.support := by use 1; intro x hx; exact (hμ'_supp hx).2
  have h_bdd_below : BddBelow μ'.support := by use a; intro x hx; exact (hμ'_supp hx).1
  have hK'_closed : IsClosed μ'.support := Measure.isClosed_support
  let b : ℝ := sSup μ'.support
  have hb_in_supp : b ∈ μ'.support := hK'_closed.csSup_mem hK'_nonempty h_bdd_above
  have hb_ge_a : a ≤ b := by
    rcases hK'_nonempty with ⟨x, hx⟩
    have h2 : a ≤ x := (hμ'_supp hx).1
    have h3 : x ≤ b := le_csSup h_bdd_above hx
    linarith
  have hb_pos : 0 < b := by linarith [ha_pos]
  have hb_le_one : b ≤ 1 := by
    have h1 : ∀ x ∈ μ'.support, x ≤ 1 := fun x hx => (hμ'_supp hx).2
    exact csSup_le hK'_nonempty h1
  have hb_max : ∀ x ∈ μ'.support, x ≤ b := fun x hx => le_csSup h_bdd_above hx
  let f : ℝ → ℝ := fun x => x / b
  have hf_cont : Continuous f := by fun_prop
  have hf_meas : Measurable f := hf_cont.measurable
  let ν : Measure ℝ := Measure.map f μ'
  have hν_univ : ν Set.univ = 1 := by
    rw [Measure.map_apply hf_meas MeasurableSet.univ] <;> simp [hμ'_univ]
  have h_preimage_eq : ∀ (y r : ℝ),
      f ⁻¹' (Set.Icc (y - r) (y + r)) = Set.Icc (b * y - b * r) (b * y + b * r) := by
    intro y r
    ext z
    simp only [Set.mem_preimage, Set.mem_Icc, f]
    constructor
    · rintro ⟨h1, h2⟩
      constructor
      · calc b * y - b * r = b * (y - r) := by ring
        _ ≤ b * (z / b) := by gcongr
        _ = z := by field_simp [hb_pos.ne'] <;> ring
      · calc z = b * (z / b) := by field_simp [hb_pos.ne'] <;> ring
        _ ≤ b * (y + r) := by gcongr
        _ = b * y + b * r := by ring
    · rintro ⟨h1, h2⟩
      constructor
      · calc y - r = (b * y - b * r) / b := by field_simp [hb_pos.ne'] <;> ring
        _ ≤ z / b := by gcongr
      · calc z / b ≤ (b * y + b * r) / b := by gcongr
        _ = y + r := by field_simp [hb_pos.ne'] <;> ring
  have h_frost' := hμ'_frost.2.2.2
  have hν_frost : IsAllScaleFrostman κ C ν := by
    refine' ⟨hν_univ, hκ_pos, hC_pos, _⟩
    intro y r hr
    have h1 : ν (Set.Icc (y - r) (y + r)) = μ' (Set.Icc (b * y - b * r) (b * y + b * r)) := by
      rw [Measure.map_apply hf_meas measurableSet_Icc, h_preimage_eq y r]
    rw [h1]
    have h3 : 0 < b * r := mul_pos hb_pos hr
    have h4 := h_frost' (b * y) (b * r) h3
    have h5 : C * (b * r) ^ κ ≤ C * r ^ κ := by
      have h7 : b * r ≤ r := by nlinarith
      have h6 : (b * r) ^ κ ≤ r ^ κ := by gcongr
      gcongr
    calc μ' (Set.Icc (b * y - b * r) (b * y + b * r))
      ≤ ENNReal.ofReal (C * (b * r) ^ κ) := h4
    _ ≤ ENNReal.ofReal (C * r ^ κ) := by gcongr
  have h_image_supp : f '' μ'.support ⊆ ν.support := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have h_main : ∀ (U : Set ℝ), U ∈ nhds (f x) → 0 < ν U := by
      intro U hU_nhds
      rcases mem_nhds_iff.mp hU_nhds with ⟨V, hV_sub, hV_open, hxV⟩
      have h_preimage_open : IsOpen (f ⁻¹' V) := hf_cont.isOpen_preimage V hV_open
      have h_x_in_preimage : x ∈ f ⁻¹' V := by simpa [f] using hxV
      have h_preimage_nhds : (f ⁻¹' V) ∈ nhds x := h_preimage_open.mem_nhds h_x_in_preimage
      have h_pos : 0 < μ' (f ⁻¹' V) := by
        have h_iff : x ∈ μ'.support ↔ ∀ (W : Set ℝ), W ∈ nhds x → 0 < μ' W := Measure.mem_support_iff_forall x
        exact (h_iff.mp hx) (f ⁻¹' V) h_preimage_nhds
      have h_eq : ν V = μ' (f ⁻¹' V) := by rw [Measure.map_apply hf_meas hV_open.measurableSet]
      have h_pos_V : 0 < ν V := by rw [h_eq] <;> exact h_pos
      have h_mono : ν V ≤ ν U := measure_mono hV_sub
      exact lt_of_lt_of_le h_pos_V h_mono
    have h_iff : f x ∈ ν.support ↔ ∀ (U : Set ℝ), U ∈ nhds (f x) → 0 < ν U := Measure.mem_support_iff_forall (f x)
    exact h_iff.mpr h_main
  have h_supp_subset_image : ν.support ⊆ f '' μ'.support := by
    let Kimg : Set ℝ := f '' μ'.support
    have hK_compact : IsCompact μ'.support :=
      Metric.isCompact_of_isClosed_isBounded hK'_closed
        (Metric.isBounded_Icc a 1 |>.subset hμ'_supp)
    have hK_closed : IsClosed Kimg := (hK_compact.image hf_cont).isClosed
    have h2 : μ'.support ⊆ f ⁻¹' Kimg := by intro x hx; exact ⟨x, hx, rfl⟩
    have h3 : ν Kimgᶜ = 0 := by
      rw [Measure.map_apply hf_meas (hK_closed.isOpen_compl.measurableSet)]
      have h4 : f ⁻¹' Kimgᶜ ⊆ μ'.supportᶜ := by
        intro z hz; intro h_contra; have h5 : f z ∈ Kimg := h2 h_contra; exact hz h5
      exact measure_mono_null h4 Measure.measure_compl_support
    intro y hy
    by_contra h
    have h5 : Kimgᶜ ∈ nhds y := hK_closed.isOpen_compl.mem_nhds h
    have h_iff : y ∈ ν.support ↔ ∀ (U : Set ℝ), U ∈ nhds y → 0 < ν U := Measure.mem_support_iff_forall y
    have h7 := (h_iff.mp hy) Kimgᶜ h5
    rw [h3] at h7 <;> simp at h7
  have hν_supp_eq : ν.support = f '' μ'.support := Set.Subset.antisymm h_supp_subset_image h_image_supp
  have hν_supp_scale : ν.support = scaleSet b⁻¹ μ'.support := by
    rw [hν_supp_eq]
    ext z
    simp only [scaleSet, Set.mem_image, f]
    <;> constructor <;> rintro ⟨x, hx, rfl⟩ <;> exact ⟨x, hx, by ring⟩
  have h1_in_supp : 1 ∈ ν.support := by
    have h2 : f b ∈ f '' μ'.support := ⟨b, hb_in_supp, rfl⟩
    have h3 : f b = 1 := by simp [f, hb_pos.ne'] <;> field_simp
    rw [h3] at h2
    rw [hν_supp_eq]
    exact h2
  have hν_supp_Icc : ν.support ⊆ Set.Icc a 1 := by
    intro y hy
    have h_y_in_image : y ∈ f '' μ'.support := by rw [←hν_supp_eq] <;> exact hy
    rcases h_y_in_image with ⟨x, hx, rfl⟩
    have h_x_Icc : x ∈ Set.Icc a 1 := hμ'_supp hx
    have h_ax : a ≤ x := h_x_Icc.1
    have h_xb : x ≤ b := le_csSup h_bdd_above hx
    have h_fx_ge_a : a ≤ f x := by
      simp only [f]
      have h_pos : 0 < b := hb_pos
      have h1 : a / b ≤ x / b := by
        exact div_le_div_of_nonneg_right h_ax (by linarith)
      have h2 : a ≤ a / b := by
        have h3 : b ≤ 1 := hb_le_one
        have h4 : 0 < a := ha_pos
        have h5 : a / 1 ≤ a / b := by gcongr
        have h6 : a / 1 = a := by ring
        rw [h6] at h5
        exact h5
      linarith
    have h_fx_le_one : f x ≤ 1 := by
      simp only [f]
      have h1 : x / b ≤ 1 := by
        have h2 : x ≤ b := h_xb
        exact (div_le_one hb_pos).mpr h2
      exact h1
    exact ⟨h_fx_ge_a, h_fx_le_one⟩
  exact ⟨b, ν, hb_pos, hb_le_one, hb_ge_a, hb_in_supp, hb_max, hν_frost, hν_supp_scale, h1_in_supp, hν_supp_Icc, hν_univ⟩

/-- Phase 2: Steps 3–8. Marstrand + multi-set PR extraction.

    Uses two-parameter ε interface:
    - `ε_A`: public δ-set exponent (hypothesis on A)
    - `ε_geom`: weighted-sum exponent (Step 3-5 output and Step 6 input)
    Requires `ε_geom = 2*ε_A` and a threshold converting the fixed-factor
    geometric bound to a δ-power at exponent `ε_geom`. -/
lemma phase2_marstrand_pr
    {κ ε_A ε_geom s : ℝ} {m N : ℕ} {δ t : ℝ} {A K : Set ℝ}
    (hκ_pos : 0 < κ) (hε_A_pos : 0 < ε_A) (hε_geom_pos : 0 < ε_geom)
    (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hδ_pos : 0 < δ) (ht_pos : 0 < t)
    (hm : 1 < (m : ℝ) * κ)
    (hA_delta : IsRealDeltaSet δ κ (δ ^ (-ε_A)) A)
    (hA_measure : MeasureTheory.volume A ≤ ENNReal.ofReal (δ ^ (1 - s)))
    {c_X : ℝ} (hcX_pos : 0 < c_X)
    (hX_lower : ENNReal.ofReal c_X ≤ MeasureTheory.volume (expansionSet K N))
    (hX_bdd : Bornology.IsBounded (expansionSet K N))
    (hX_compact : IsCompact (expansionSet K N))
    (c_step C_energy : ℝ) (hc_step_pos : 0 < c_step) (hC_energy_pos : 0 < C_energy)
    (M_X : ℝ) (hM_X_pos : 0 < M_X)
    (h_geo : ∀ {X : Set ℝ} {A : Set ℝ} {δ B : ℝ}
      (ν : Measure (EuclideanSpace ℝ (Fin m)))
      [IsProbabilityMeasure ν],
      IsCompact X →
      ENNReal.ofReal c_X ≤ MeasureTheory.volume X →
      X ⊆ Set.Icc (-M_X) M_X →
      A ⊆ Set.Icc 1 2 →
      (hδ_pos : 0 < δ) → (hB_pos : 0 < B) →
      ν.support ⊆ {x | ∀ i, x i ∈ A} →
      IsCompact ν.support →
      robust_projection_main.rieszEnergy (α := 1) (hδ := hδ_pos) ν ≤ ENNReal.ofReal B →
      ∃ (x : Fin m → ℝ), (∀ i, x i ∈ X) ∧
        ENNReal.ofReal (c_step / (B * δ)) ≤ Nreal δ (ExpansionLemma.scaledSumset x A))
    (h_bridge : ∀ (δ ε : ℝ) (A : Set ℝ),
      (hδ_pos : 0 < δ) → (hδ_le_one : δ ≤ 1) → (hε_nonneg : 0 ≤ ε) →
      (hA_sub : A ⊆ Set.Icc 1 2) →
      (hA_delta : IsRealDeltaSet δ κ (δ ^ (-ε)) A) →
      ∃ (ν : Measure (EuclideanSpace ℝ (Fin m)))
        (_ : IsProbabilityMeasure ν),
        ν.support ⊆ {x | ∀ i, x i ∈ A} ∧
        IsCompact ν.support ∧
        robust_projection_main.rieszEnergy (α := 1) (hδ := hδ_pos) ν ≤
          ENNReal.ofReal (C_energy * δ ^ (-ε * (m : ℝ))))
    (hX_sub : expansionSet K N ⊆ Set.Icc (-M_X) M_X)
    (hA_sub2 : A ⊆ Set.Icc 1 2)
    (hδ_le_one : δ ≤ 1)
    (h_ε_geom_m : ε_geom * (m : ℝ) < (1 - s) / 2)
    (h_ε_geom : ε_geom = 2 * ε_A)
    (h_threshold : δ ^ (ε_A * (m : ℝ)) ≤ c_step / C_energy)
    (h_t_lower4 : δ ^ ((1 - s) / 4) ≤ t)
    (ht_le_one : t ≤ 1)
    (hA_size : Nreal δ A ≤ ENNReal.ofReal (δ ^ (-s)))
    (hK_bounds : K ⊆ Set.Icc ((2 : ℝ) ^ (-(1/κ))) 1)
    (ε_tloss : ℝ) (hε_tloss_pos : 0 < ε_tloss)
    (γ : ℝ) (hγ_pos : 0 < γ)
    (hγ_eq : γ = (1 - s) / 2 - ε_geom * (m : ℝ) - 3 * (m : ℝ) * (N : ℝ) * ε_tloss)
    (hδ_poly : δ ^ γ ≤ (step6_full_C m N κ)⁻¹)
    (h_tloss : t ^ (2 / 3 : ℝ) ≥ δ ^ ε_tloss)
    (h_cubic_absorb : δ ^ (3 * ε_tloss) ≤
        1 / (486 * ((2 : ℝ)^((N : ℝ)/κ) + 3)))
    (δ₀ : ℝ) (hδ_small : δ ≤ δ₀) (hδ₀_le_one : δ₀ ≤ 1)
    (hK_bdd : Bornology.IsBounded K) (hA_bdd : Bornology.IsBounded A) :
    ∃ (y : ℝ), y ∈ productSetN K N ∧
      ENNReal.ofReal (δ ^ (-(1 - s) / (24 * ((m : ℝ) * (N : ℝ))) + ε_tloss)) *
        Nreal δ (scaleSet t⁻¹ A) ≤
      Nreal δ (Set.image2 (· - ·) (scaleSet t⁻¹ A) (scaleSet y A)) := by
  have h_pos_m : 0 < (m : ℝ) := by
    have h : 1 < (m : ℝ) * κ := hm
    nlinarith [hκ_pos]
  have h_εAm : ε_A * (m : ℝ) < (1 - s) / 2 := by
    have h1 : ε_A < ε_geom := by
      rw [h_ε_geom] <;> linarith
    have h2 : ε_A * (m : ℝ) < ε_geom * (m : ℝ) :=
      mul_lt_mul_of_pos_right h1 h_pos_m
    exact lt_trans h2 h_ε_geom_m
  have h_step3 : ∃ (x : Fin m → ℝ), (∀ i, x i ∈ expansionSet K N) ∧
      ENNReal.ofReal (δ ^ (-1 + ε_geom * (m : ℝ))) ≤
        Nreal δ (weightedSumset x A) := by
    -- Construct ν via product-measure bridge
    rcases h_bridge δ ε_A A hδ_pos hδ_le_one (by linarith) hA_sub2 hA_delta
      with ⟨ν, _, hν_supp, hν_supp_compact, h_energy⟩
    let B : ℝ := C_energy * δ ^ (-ε_A * (m : ℝ))
    have hB_pos : 0 < B := by positivity
    -- Apply proved Step3-5 geometric theorem
    rcases h_geo ν hX_compact hX_lower hX_sub hA_sub2 hδ_pos hB_pos hν_supp hν_supp_compact h_energy
      with ⟨x_coeffs, hx_in_X, h_bound⟩
    -- Arithmetic: c_step/(B·δ) = (c_step/C_energy)·δ^(-1+ε_A·m)
    have h_eq1 : c_step / (B * δ) = (c_step / C_energy) * δ ^ (-1 + ε_A * (m : ℝ)) := by
      dsimp only [B]
      have hδ_nonneg : 0 ≤ δ := by linarith
      have h1 : δ ^ (-ε_A * (m : ℝ)) * δ = δ ^ (1 - ε_A * (m : ℝ)) := by
        have h_rpow : δ ^ (-ε_A * (m : ℝ)) * δ ^ (1 : ℝ) =
            δ ^ (-ε_A * (m : ℝ) + 1) :=
          Eq.symm (Real.rpow_add hδ_pos (-ε_A * (m : ℝ)) (1 : ℝ))
        have hδ1 : δ ^ (1 : ℝ) = δ := by simp
        have h_sum : -ε_A * (m : ℝ) + 1 = 1 - ε_A * (m : ℝ) := by ring
        rw [hδ1] at h_rpow
        rw [h_sum] at h_rpow
        exact h_rpow
      have h2 : c_step / (C_energy * δ ^ (-ε_A * (m : ℝ)) * δ) =
          (c_step / C_energy) * (δ ^ (1 - ε_A * (m : ℝ)))⁻¹ := by
        have h_assoc : C_energy * δ ^ (-ε_A * (m : ℝ)) * δ = C_energy * (δ ^ (-ε_A * (m : ℝ)) * δ) := by ring
        rw [h_assoc, h1]
        field_simp [hC_energy_pos.ne'] <;> ring
      rw [h2]
      have h3 : (δ ^ (1 - ε_A * (m : ℝ)))⁻¹ = δ ^ (-1 + ε_A * (m : ℝ)) := by
        have h4 : (δ ^ (1 - ε_A * (m : ℝ)))⁻¹ = δ ^ (-(1 - ε_A * (m : ℝ))) :=
          Eq.symm (Real.rpow_neg hδ_nonneg (1 - ε_A * (m : ℝ)))
        rw [h4]
        congr 1 <;> ring
      rw [h3] <;> ring
    -- Threshold conversion: δ^(ε_A·m) ≤ c_step/C_energy gives δ^(-1+ε_geom·m) ≤ (c_step/C_energy)·δ^(-1+ε_A·m)
    have h_arith : δ ^ (-1 + ε_geom * (m : ℝ)) ≤ c_step / (B * δ) := by
      rw [h_eq1]
      have h9 : δ ^ (-1 + ε_geom * (m : ℝ)) =
          δ ^ (ε_A * (m : ℝ)) * δ ^ (-1 + ε_A * (m : ℝ)) := by
        have h_exp2 : -1 + ε_geom * (m : ℝ) = ε_A * (m : ℝ) + (-1 + ε_A * (m : ℝ)) := by
          rw [h_ε_geom] <;> ring
        rw [h_exp2]
        rw [Real.rpow_add (by linarith)] <;> ring
      rw [h9]
      have h10 : 0 ≤ δ ^ (-1 + ε_A * (m : ℝ)) := by positivity
      exact mul_le_mul_of_nonneg_right h_threshold h10
    have h11 : ENNReal.ofReal (δ ^ (-1 + ε_geom * (m : ℝ))) ≤ ENNReal.ofReal (c_step / (B * δ)) :=
      ENNReal.ofReal_le_ofReal h_arith
    have h12 : weightedSumset x_coeffs A = ExpansionLemma.scaledSumset x_coeffs A := by
      rfl
    have h_final : ENNReal.ofReal (δ ^ (-1 + ε_geom * (m : ℝ))) ≤
        Nreal δ (weightedSumset x_coeffs A) := by
      rw [h12]
      exact le_trans h11 h_bound
    exact ⟨x_coeffs, hx_in_X, h_final⟩
  rcases h_step3 with ⟨x_coeffs, hx_in_X, h_sumset_large⟩
  have h_result := step6_8_full_difference (A := A) (K := K) (N0 := N) (m := m)
    (hκ_pos := hκ_pos) (hs_pos := hs_pos) (hs_lt_one := hs_lt_one)
    (hδ_pos := hδ_pos) (ht_pos := ht_pos) (ht_le_one := ht_le_one) (hε_pos := hε_geom_pos)
    (x := x_coeffs) (hx_in_X := hx_in_X)
    (h_sumset_large := h_sumset_large)
    (h_εm := h_ε_geom_m) (h_t_lower := h_t_lower4)
    (hA_size := hA_size) (hK_bounds := hK_bounds)
    (ε_tloss := ε_tloss) (hε_tloss_pos := hε_tloss_pos)
    (γ := γ) (hγ_pos := hγ_pos) (hγ_eq := hγ_eq)
    (hδ_poly := hδ_poly)
    (h_tloss := h_tloss) (h_cubic_absorb := h_cubic_absorb)
    (δ₀ := δ₀) (hδ_small := hδ_small) (hδ₀_le_one := hδ₀_le_one)
    (hK_bdd := hK_bdd) (hA_bdd := hA_bdd)
  rcases h_result with ⟨y, hy, h_exp⟩
  refine ⟨y, hy, ?_⟩
  have h_assoc : (24 * (m : ℝ) * (N : ℝ)) = (24 * ((m : ℝ) * (N : ℝ))) := by ring
  rw [h_assoc] at h_exp
  exact h_exp

-- [REMOVED] phase3_triangle_sum lemma was unused and caused whnf timeouts due to complex type.
-- The main theorem calls step9_11_triangle_correct and step12_diff_to_sum_normalized directly.

/-- Helper: in a 9-level nested min, the 6th component (index 5) is an upper bound. -/
lemma nested_min_le_elem5 {a b c d e f g h i j : ℝ} :
    min a (min b (min c (min d (min e (min f (min g (min h (min i j)))))))) ≤ f := by
  apply le_trans (min_le_right _ _)
  apply le_trans (min_le_right _ _)
  apply le_trans (min_le_right _ _)
  apply le_trans (min_le_right _ _)
  apply le_trans (min_le_right _ _)
  exact min_le_left _ _

/-- Helper: in a 9-level nested min, the 7th component (index 6) is an upper bound. -/
lemma nested_min_le_elem7 {a b c d e f g h i j : ℝ} :
    min a (min b (min c (min d (min e (min f (min g (min h (min i j)))))))) ≤ g := by
  apply le_trans (min_le_right _ _)
  apply le_trans (min_le_right _ _)
  apply le_trans (min_le_right _ _)
  apply le_trans (min_le_right _ _)
  apply le_trans (min_le_right _ _)
  apply le_trans (min_le_right _ _)
  exact min_le_left _ _

/-- Helper: in a 10-level nested min, the last component is an upper bound. -/
lemma nested_min_le_last10 {a b c d e f g h i j k : ℝ} :
    min a (min b (min c (min d (min e (min f (min g (min h (min i (min j k))))))))) ≤ k := by
  apply le_trans (min_le_right _ _)
  apply le_trans (min_le_right _ _)
  apply le_trans (min_le_right _ _)
  apply le_trans (min_le_right _ _)
  apply le_trans (min_le_right _ _)
  apply le_trans (min_le_right _ _)
  apply le_trans (min_le_right _ _)
  apply le_trans (min_le_right _ _)
  apply le_trans (min_le_right _ _)
  exact min_le_right _ _

/-- Generic absorption: if `δ ≤ threshold` and `threshold = C^(1/e)` with `e > 0`,
    then `δ^e ≤ C`. -/
lemma rpow_absorption {δ threshold C e : ℝ}
    (hδ_pos : 0 < δ) (hC_nonneg : 0 ≤ C) (he_pos : 0 < e)
    (hδ_le : δ ≤ threshold) (hthreshold : threshold = C ^ (1 / e)) :
    δ ^ e ≤ C := by
  have h1 : 0 ≤ threshold := by
    rw [hthreshold]
    positivity
  have h2 : δ ^ e ≤ threshold ^ e := Real.rpow_le_rpow hδ_pos.le hδ_le he_pos.le
  have h3 : threshold ^ e = C := by
    rw [hthreshold]
    have h4 : (C ^ (1 / e)) ^ e = C ^ ((1 / e) * e) :=
      (Real.rpow_mul hC_nonneg (1 / e) e).symm
    rw [h4]
    have h5 : (1 / e) * e = 1 := by field_simp [he_pos.ne'] <;> ring
    rw [h5, Real.rpow_one]
  rw [h3] at h2
  exact h2

/-- Absorption lemma for δ₀_abs12: δ ≤ δ₀ implies δ^exp12 ≤ C_abs12.
    Extracted to avoid timeout in the huge main-theorem context. -/
lemma abs12_absorption {δ δ₀ δ₀_abs12 C_abs12 exp12 : ℝ}
    (hδ_pos : 0 < δ) (hδle : δ ≤ δ₀)
    (hδ₀_le_abs12 : δ₀ ≤ δ₀_abs12)
    (hexp12_pos : 0 < exp12)
    (hC_nonneg : 0 ≤ C_abs12)
    (hthreshold : δ₀_abs12 = C_abs12 ^ (1 / exp12)) :
    δ ^ exp12 ≤ C_abs12 := by
  have h3 : δ ≤ δ₀_abs12 := le_trans hδle hδ₀_le_abs12
  have h4 : 0 ≤ δ := hδ_pos.le
  have h5 : 0 ≤ δ₀_abs12 := by
    rw [hthreshold] <;> positivity
  have h6 : δ ^ exp12 ≤ δ₀_abs12 ^ exp12 := Real.rpow_le_rpow h4 h3 hexp12_pos.le
  have h7 : δ₀_abs12 ^ exp12 = C_abs12 := by
    rw [hthreshold]
    have h8 : (C_abs12 ^ (1 / exp12)) ^ exp12 = C_abs12 ^ ((1 / exp12) * exp12) :=
      (Real.rpow_mul hC_nonneg (1 / exp12) exp12).symm
    rw [h8]
    have h9 : (1 / exp12) * exp12 = 1 := by
      field_simp [hexp12_pos.ne'] <;> ring
    rw [h9, Real.rpow_one]
  rw [h7] at h6
  exact h6

/-- Helper: match the ENNReal constant `2 * (ceil(2^(1/κ)) + 2)` with `ofReal (2 * C_κ_real)`. -/
lemma two_Cκ_match (κ : ℝ) (hκ_pos : 0 < κ) :
    (2 * ((Nat.ceil ((2 : ℝ)^(1/κ)) + 2 : ENNReal))) =
    ENNReal.ofReal (2 * ((Nat.ceil ((2 : ℝ)^(1/κ)) + 2 : ℝ))) := by
  have h_nat : ∀ (n : ℕ), ENNReal.ofReal ((n : ℝ)) = (n : ENNReal) := by
    intro n; simp
  set n : ℕ := Nat.ceil ((2 : ℝ)^(1/κ)) + 2 with hn
  have h1 : ENNReal.ofReal ((n : ℝ)) = (n : ENNReal) := h_nat n
  have h2 : ENNReal.ofReal (2 * (n : ℝ)) = 2 * ENNReal.ofReal ((n : ℝ)) := by
    have hpos : 0 ≤ (2 : ℝ) := by norm_num
    rw [ofReal_mul hpos] <;> simp
  have h3 : ENNReal.ofReal (2 * (n : ℝ)) = 2 * (n : ENNReal) := by
    rw [h2, h1]
  have h_goal1 : (2 * ((Nat.ceil ((2 : ℝ)^(1/κ)) + 2 : ENNReal))) = 2 * (n : ENNReal) := by
    congr <;> simp [hn] <;> norm_cast
  have h_goal2 : ENNReal.ofReal (2 * (n : ℝ)) = ENNReal.ofReal (2 * ((Nat.ceil ((2 : ℝ)^(1/κ)) + 2 : ℝ))) := by
    congr <;> simp [hn] <;> norm_cast
  rw [h_goal1]
  exact h3.symm.trans h_goal2

/-- Helper: prove `0 < γ` and `β_in + 4*c' < 0` for the Strong Ring Theorem
    parameter choices. Extracted to reduce proof size. -/
lemma strong_ring_gamma_beta
    (s : ℝ) (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (m N : ℕ) (hN_pos : 0 < N)
    (k c ε : ℝ) (hc_pos : 0 < c)
    (hε : ε = (1 - s) / (4 * (m : ℝ)))
    (hc : c = (1 - s) / (400 * k * (2 * (N : ℝ) + 1)))
    (hk : k = (m : ℝ) * (N : ℝ)) :
    let ε_norm : ℝ := c / 100
    let ε_abs : ℝ := c / 100
    let c' : ℝ := c + ε_norm
    let ε_tloss : ℝ := 2 * c' / 3
    let γ : ℝ := (1 - s) / 2 - ε * (m : ℝ) - 3 * (m : ℝ) * (N : ℝ) * ε_tloss
    let α_in : ℝ := (-(1 - s) / (24 * k)) + ε_tloss
    let β_in : ℝ := c' * (N : ℝ) / (2 * (N : ℝ) + 1) + α_in / (2 * (N : ℝ) + 1) + ε_abs
    0 < γ ∧ β_in + 4 * c' < 0 := by
  dsimp only
  have hm_pos : 0 < m := by
    by_contra h
    have h0 : m = 0 := by omega
    have hk0 : k = 0 := by
      rw [hk, h0] <;> ring
    have hc0 : c = 0 := by
      rw [hc, hk0] <;> ring
    rw [hc0] at hc_pos
    <;> linarith
  set ε_norm : ℝ := c / 100 with hε_norm_def
  set ε_abs : ℝ := c / 100 with hε_abs_def
  set c' : ℝ := c + ε_norm with hc'_def
  set ε_tloss : ℝ := 2 * c' / 3 with hε_tloss_def
  set γ : ℝ := (1 - s) / 2 - ε * (m : ℝ) - 3 * (m : ℝ) * (N : ℝ) * ε_tloss with hγ_def
  set α_in : ℝ := (-(1 - s) / (24 * k)) + ε_tloss with hα_in_def
  set β_in : ℝ := c' * (N : ℝ) / (2 * (N : ℝ) + 1) + α_in / (2 * (N : ℝ) + 1) + ε_abs with hβ_in_def
  have h1_pos : 0 < 1 - s := by linarith
  have hk_pos : 0 < k := by
    rw [hk]
    have h1 : 0 < (m : ℝ) := by exact_mod_cast hm_pos
    have h2 : 0 < (N : ℝ) := by exact_mod_cast hN_pos
    positivity
  have hN3 : 2 * (N : ℝ) + 1 ≥ 3 := by
    have h16 : 1 ≤ (N : ℝ) := by exact_mod_cast hN_pos
    linarith
  -- Proof of 0 < γ
  have h_εm_exact : ε * (m : ℝ) = (1 - s) / 4 := by
    rw [hε]
    have h_pos : 0 < (m : ℝ) := by positivity
    field_simp [h_pos.ne'] <;> ring
  have h_cubic : 3 * (m : ℝ) * (N : ℝ) * ε_tloss = 2 * k * c' := by
    rw [hε_tloss_def, hc'_def, hk] <;> ring
  have h_c'_eq : c' = (101 / 100 : ℝ) * c := by
    rw [hc'_def, hε_norm_def] <;> ring
  have h_main : 2 * k * c' < (1 - s) / 4 := by
    rw [h_c'_eq, hc]
    have h_pos1 : 0 < k := hk_pos
    have h_pos2 : 0 < 2 * (N : ℝ) + 1 := by linarith
    have h_eq : 2 * k * ((101 / 100 : ℝ) * ((1 - s) / (400 * k * (2 * (N : ℝ) + 1)))) =
        (1 - s) * (202 : ℝ) / (40000 * (2 * (N : ℝ) + 1)) := by
      field_simp [h_pos1.ne', h_pos2.ne'] <;> ring
    rw [h_eq]
    have h : (1 - s) * (202 : ℝ) / (40000 * (2 * (N : ℝ) + 1)) < (1 - s) / 4 := by
      have h9 : 0 < 1 - s := h1_pos
      have h10 : 40000 * (2 * (N : ℝ) + 1) ≥ 120000 := by linarith
      have h11 : (202 : ℝ) / (40000 * (2 * (N : ℝ) + 1)) < 1 / 4 := by
        have h12 : (202 : ℝ) / (40000 * (2 * (N : ℝ) + 1)) ≤ (202 : ℝ) / 120000 := by gcongr
        have h13 : (202 : ℝ) / 120000 < (1 : ℝ) / 4 := by norm_num
        linarith
      have h14 : (1 - s) * (202 : ℝ) / (40000 * (2 * (N : ℝ) + 1)) =
          (1 - s) * ((202 : ℝ) / (40000 * (2 * (N : ℝ) + 1))) := by ring
      have h15 : (1 - s) / 4 = (1 - s) * (1 / 4 : ℝ) := by ring
      rw [h14, h15]
      exact mul_lt_mul_of_pos_left h11 h9
    exact h
  have hγ_pos : 0 < γ := by
    rw [hγ_def, h_εm_exact, h_cubic]
    have h9 : (1 - s) / 2 - (1 - s) / 4 = (1 - s) / 4 := by ring
    rw [h9]
    exact sub_pos.mpr h_main
  -- Proof of β_in + 4 * c' < 0
  have h_bracket :
      (101 / 100 : ℝ) * c * ((N : ℝ) / (2 * (N : ℝ) + 1)) +
      (((101 / 100 : ℝ) * c) * (2 / 3 : ℝ)) / (2 * (N : ℝ) + 1) +
      c / 100 + 4 * ((101 / 100 : ℝ) * c) ≤ (2857 / 500 : ℝ) * c := by
    have h5 : 0 ≤ c := by linarith
    have h6 : (101 / 100 : ℝ) * c * ((N : ℝ) / (2 * (N : ℝ) + 1)) ≤ (101 / 100 : ℝ) * c := by
      have h61 : (N : ℝ) / (2 * (N : ℝ) + 1) ≤ 1 := by
        have h62 : (N : ℝ) ≤ 2 * (N : ℝ) + 1 := by linarith
        exact (div_le_one (by linarith)).mpr h62
      have h_pos : 0 ≤ (101 / 100 : ℝ) * c := mul_nonneg (by norm_num) h5
      calc (101 / 100 : ℝ) * c * ((N : ℝ) / (2 * (N : ℝ) + 1))
        ≤ (101 / 100 : ℝ) * c * 1 := by gcongr <;> linarith
      _ = (101 / 100 : ℝ) * c := by ring
    have h7 : (((101 / 100 : ℝ) * c) * (2 / 3 : ℝ)) / (2 * (N : ℝ) + 1) ≤
        ((101 / 100 : ℝ) * c) * (2 / 3 : ℝ) * (1 / 3 : ℝ) := by
      have h71 : 1 / (2 * (N : ℝ) + 1) ≤ 1 / 3 := by
        apply one_div_le_one_div_of_le <;> linarith
      have h : (((101 / 100 : ℝ) * c) * (2 / 3 : ℝ)) / (2 * (N : ℝ) + 1) =
          ((101 / 100 : ℝ) * c) * (2 / 3 : ℝ) * (1 / (2 * (N : ℝ) + 1)) := by ring
      rw [h]; gcongr <;> linarith
    have h8 : ((101 / 100 : ℝ) * c) * (2 / 3 : ℝ) * (1 / 3 : ℝ) = (202 / 900 : ℝ) * c := by ring
    nlinarith
  have h_main2 : (2857 / 500 : ℝ) * c < (1 - s) / (24 * k * (2 * (N : ℝ) + 1)) := by
    rw [hc]
    have h7 : 0 < (1 - s) / (k * (2 * (N : ℝ) + 1)) := by positivity
    have h8 : (2857 : ℝ) / 200000 < (1 : ℝ) / 24 := by norm_num
    have h9 : (2857 / 500 : ℝ) * ((1 - s) / (400 * k * (2 * (N : ℝ) + 1))) =
        ((1 - s) / (k * (2 * (N : ℝ) + 1))) * ((2857 : ℝ) / 200000) := by
      field_simp <;> ring
    rw [h9]
    have h10 : ((1 - s) / (k * (2 * (N : ℝ) + 1))) * ((2857 : ℝ) / 200000) <
        ((1 - s) / (k * (2 * (N : ℝ) + 1))) * ((1 : ℝ) / 24) := by
      exact mul_lt_mul_of_pos_left h8 h7
    have h11 : ((1 - s) / (k * (2 * (N : ℝ) + 1))) * ((1 : ℝ) / 24) =
        (1 - s) / (24 * k * (2 * (N : ℝ) + 1)) := by field_simp <;> ring
    rw [h11] at h10; exact h10
  have h_expand : β_in + 4 * c' =
      (101 / 100 : ℝ) * c * ((N : ℝ) / (2 * (N : ℝ) + 1)) +
      (((101 / 100 : ℝ) * c) * (2 / 3 : ℝ)) / (2 * (N : ℝ) + 1) +
      (-(1 - s) / (24 * k)) / (2 * (N : ℝ) + 1) + c / 100 + 4 * ((101 / 100 : ℝ) * c) := by
    rw [hβ_in_def, hα_in_def, hc'_def, hε_norm_def, hε_abs_def, hε_tloss_def] <;> ring
  have h_div : (-(1 - s) / (24 * k)) / (2 * (N : ℝ) + 1) =
      - (1 - s) / (24 * k * (2 * (N : ℝ) + 1)) := by
    field_simp <;> ring
  have hβ_neg : β_in + 4 * c' < 0 := by
    rw [h_expand, h_div]
    have h_total : (2857 / 500 : ℝ) * c + (-(1 - s) / (24 * k * (2 * (N : ℝ) + 1))) < 0 := by
      have h9 : (2857 / 500 : ℝ) * c < (1 - s) / (24 * k * (2 * (N : ℝ) + 1)) := h_main2
      have h10 : (-(1 - s) / (24 * k * (2 * (N : ℝ) + 1))) = -((1 - s) / (24 * k * (2 * (N : ℝ) + 1))) := by
        field_simp <;> ring
      rw [h10]; exact sub_lt_zero.mpr h9
    calc (101 / 100 : ℝ) * c * ((N : ℝ) / (2 * (N : ℝ) + 1)) +
        (((101 / 100 : ℝ) * c) * (2 / 3 : ℝ)) / (2 * (N : ℝ) + 1) +
        (-(1 - s) / (24 * k * (2 * (N : ℝ) + 1))) + c / 100 + 4 * ((101 / 100 : ℝ) * c)
      = ((101 / 100 : ℝ) * c * ((N : ℝ) / (2 * (N : ℝ) + 1)) +
            (((101 / 100 : ℝ) * c) * (2 / 3 : ℝ)) / (2 * (N : ℝ) + 1) +
            c / 100 + 4 * ((101 / 100 : ℝ) * c)) +
          (-(1 - s) / (24 * k * (2 * (N : ℝ) + 1))) := by ring
    _ ≤ (2857 / 500 : ℝ) * c + (-(1 - s) / (24 * k * (2 * (N : ℝ) + 1))) := by gcongr
    _ < 0 := h_total
  exact ⟨hγ_pos, hβ_neg⟩

/-! ## Main theorem: Strong Ring Theorem (Proposition 4.1) -/

/-- **Strong Ring Theorem** (Proposition 4.1, paper lines 577–584), **t≤1 variant**.

    Given an all-scale `(κ,C₀)`-Frostman measure μ supported on `[0,1]`, with
    `1 ≤ C₀ ≤ 2^κ`, and a `(δ,κ,δ^{-ε})`-set A with `volume A ≤ δ^{1-s}` that is
    δ-discretized (`volume A = δ · Nδ(A)`), there exists `x ∈ supp μ` such that
    `|t^{-1}A + xA|_δ > δ^{-c} · |t^{-1}A|_δ` for `δ^c ≤ t ≤ 1`.

    The exponents are:
    - `m` = least integer with `m·κ > 1`
    - `N` = uniform Expansion Theorem constant (depends only on κ)
    - `k = m·N`
    - `c = (1-s)/(400·k·(2N+1))`
    - `ε` chosen so `ε·m < (1-s)/2`

    **t≤1 restriction**: This variant assumes `t ≤ 1`. In the Ring Theorem
    reduction, set `t = r₀` where `r₀` is the maximal-density interval length;
    since `δ ≤ r₀ ≤ 1`, the hypothesis is satisfied. The full paper proposition
    without `t≤1` can be recovered by scaling with `min(1,t)`, but is not needed
    for the target proof.

    Generalized from C₀=1 to arbitrary `1 ≤ C₀ ≤ 2^κ`; exponents c,ε are
    independent of C₀, only δ₀ depends on C₀.

    Requires δ-discretization of A to bridge Lebesgue measure and covering
    numbers in step 6–8. -/

lemma strong_ring_theorem_corrected
    (s κ : ℝ) (hs_pos : 0 < s) (hs_lt_one : s < 1)
    (hκ_pos : 0 < κ) (hκ_le_s : κ ≤ s) :
    ∃ (c ε : ℝ), 0 < c ∧ 0 < ε ∧
      ∀ (C₀ : ℝ), 0 < C₀ → C₀ ≤ 2 ^ κ →
        ∃ (δ₀ : ℝ), 0 < δ₀ ∧
          ∀ {δ : ℝ}, δ ∈ dyadicScales → 0 < δ → δ ≤ δ₀ →
            ∀ (A : Set ℝ) (μ : Measure ℝ) (t : ℝ),
              A ⊆ Set.Icc 1 2 →
              IsRealDeltaSet δ κ (δ ^ (-ε)) A →
              MeasureTheory.volume A ≤ ENNReal.ofReal (δ ^ (1 - s)) →
              Nreal δ A ≤ ENNReal.ofReal (δ ^ (-s)) →
              IsAllScaleFrostman κ C₀ μ →
              μ.support ⊆ Set.Icc 0 1 →
              δ ^ c ≤ t →
              t ≤ 1 →
              ∃ x ∈ μ.support,
                ENNReal.ofReal (δ ^ (-c)) * Nreal δ (scaleSet t⁻¹ A) ≤
                  Nreal δ (Set.image2 (fun a b => a + x * b)
                    (scaleSet t⁻¹ A) A) := by
  -- Choose m = least integer with m*κ > 1
  have h_exists_m : ∃ (n : ℕ), 1 < (n : ℝ) * κ := by
    have harch : ∃ (n : ℕ), 1 / κ < (n : ℝ) := exists_nat_gt (1 / κ)
    rcases harch with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hκ_pos' : 0 < κ := hκ_pos
    calc (n : ℝ) * κ > (1 / κ) * κ := by gcongr
      _ = 1 := by field_simp [hκ_pos'.ne']
  let m : ℕ := Nat.find h_exists_m
  have hm : 1 < (m : ℝ) * κ := Nat.find_spec h_exists_m
  have hm_pos : 0 < (m : ℝ) := by
    have h : 1 < (m : ℝ) * κ := hm
    nlinarith
  -- Choose ε_A (public δ-set exponent) and ε_geom (internal weighted-sum exponent)
  let ε_A : ℝ := (1 - s) / (8 * (m : ℝ))
  let ε_geom : ℝ := (1 - s) / (4 * (m : ℝ))
  have hε_A_pos : 0 < ε_A := by
    have h1 : 0 < 1 - s := by linarith
    exact div_pos h1 (by positivity)
  have hε_geom_pos : 0 < ε_geom := by
    have h1 : 0 < 1 - s := by linarith
    exact div_pos h1 (by positivity)
  have h_ε_geom : ε_geom = 2 * ε_A := by
    dsimp only [ε_geom, ε_A]
    <;> ring
  have h_ε_geom_m : ε_geom * (m : ℝ) < (1 - s) / 2 := by
    dsimp only [ε_geom]
    have h1 : 0 < (m : ℝ) := hm_pos
    field_simp [h1.ne'] <;> linarith
  have hκ_lt_one : κ < 1 := by linarith [hκ_le_s, hs_lt_one]
  -- Choose N from uniform Expansion Theorem with C_val = 2^(κ+1).
  -- This constant is independent of C₀ and ≥ 1. Later, the normalized measure
  -- (with Frostman constant 2*C₀) is upgraded to 2^(κ+1) before applying hN_uniform.
  let C_val : ℝ := (2 : ℝ)^(κ+1)
  have hC_val_pos : 0 < C_val := by positivity
  have hC_val_ge_one : 1 ≤ C_val := by
    have h1 : (0 : ℝ) ≤ κ+1 := by linarith
    have h2 : (2 : ℝ)^(0 : ℝ) ≤ (2 : ℝ)^(κ+1) := Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
    simpa using h2
  rcases step2_expansion_uniform_N hκ_pos hκ_lt_one C_val hC_val_pos hC_val_ge_one
    with ⟨N, c_X, hN_pos, hcX_pos, hN_uniform⟩
  -- Define k and c from N
  let k : ℝ := (m : ℝ) * (N : ℝ)
  let c : ℝ := (1 - s) / (400 * k * (2 * (N : ℝ) + 1))
  have hc_pos : 0 < c := by
    have h1 : 0 < 1 - s := by linarith
    have h2 : 0 < k := by positivity
    positivity
  have h_final_c : c = (1 - s) / (400 * k * (2 * (N : ℝ) + 1)) := by rfl
  -- Normalization parameters (defined early for γ proof)
  let ε_norm : ℝ := c / 100
  let ε_abs : ℝ := c / 100
  let c' : ℝ := c + ε_norm
  have hε_norm_pos : 0 < ε_norm := by positivity
  have hε_abs_pos : 0 < ε_abs := by positivity
  have hc'_pos : 0 < c' := by positivity
  -- Define ε_tloss for step6 cubic absorption (must be 2*c'/3 to match t' ≥ δ^c')
  let ε_tloss : ℝ := 2 * c' / 3
  have hε_tloss_pos : 0 < ε_tloss := by positivity
  -- Define γ for step6 polynomial threshold (includes ε_tloss loss)
  let γ : ℝ := (1 - s) / 2 - ε_geom * (m : ℝ) - 3 * (m : ℝ) * (N : ℝ) * ε_tloss
  have h_gamma_beta := strong_ring_gamma_beta s hs_pos hs_lt_one m N hN_pos k c ε_geom hc_pos
    (by rfl) (by rfl) (by rfl)
  rcases h_gamma_beta with ⟨hγ_pos, hβ_in_neg⟩
  have hγ_eq : γ = (1 - s) / 2 - ε_geom * (m : ℝ) - 3 * (m : ℝ) * (N : ℝ) * ε_tloss := by rfl
  let α_in : ℝ := (-(1 - s) / (24 * k)) + ε_tloss
  let β_in : ℝ := c' * (N : ℝ) / (2 * (N : ℝ) + 1) +
      α_in / (2 * (N : ℝ) + 1) + ε_abs
  refine' ⟨c, ε_A, hc_pos, hε_A_pos, _⟩
  intro C₀ hC₀_pos hC₀_le
  -- c_X and hN_uniform are already defined above (depend only on κ through C_val = 2^(κ+1))
  -- Step-specific δ thresholds (to be refined when step proofs are filled in).
  -- δ₀ is the minimum of all required bounds.
  let δ₀_PR : ℝ := 1
  let δ₀_triangle : ℝ := 1
  let δ₀_sum : ℝ := 1
  let C6 : ℝ := step6_full_C m N κ
  have hC6_pos : 0 < C6 := by
    dsimp only [C6, step6_full_C]
    have hm_nat_pos : 0 < m := by exact_mod_cast (show 0 < (m : ℝ) from by linarith)
    have h1 : 0 < 2 * m * N := by positivity
    have h2 : 0 < (2 : ℝ) ^ ((N : ℝ) / κ) + 2 := by positivity
    have h3 : 0 < 486 * ((2 * m * N : ℕ) : ℝ) * ((2 : ℝ) ^ ((N : ℝ) / κ) + 2) := by positivity
    have h4 : 0 < (486 * ((2 * m * N : ℕ) : ℝ) * ((2 : ℝ) ^ ((N : ℝ) / κ) + 2)) ^ (2 * m * N) := by
      exact pow_pos h3 _
    exact mul_pos (by exact_mod_cast h1) h4
  let δ₀_poly : ℝ := C6⁻¹ ^ (1 / γ)
  -- Thresholds for steps9-12 constant absorption
  let C_abs9 : ℝ := (46656 : ℝ)^ (-(N : ℝ)/(2 * (N : ℝ) + 1)) *
      (2 : ℝ)^ (-(N : ℝ) * ((N : ℝ) - 1) / (2 * κ * (2 * (N : ℝ) + 1)))
  let δ₀_abs9 : ℝ := C_abs9 ^ (1 / ε_abs)
  let exp12 : ℝ := -(β_in + 4 * c')
  have hexp12_pos : 0 < exp12 := by
    dsimp only [exp12]
    exact neg_pos.mpr hβ_in_neg
  let C_abs12 : ℝ := (2 : ℝ)^(-(1/κ)) / 729
  let δ₀_abs12 : ℝ := C_abs12 ^ (1 / exp12)
  let C_norm : ℝ := (2 : ℝ)^(-(1/κ))
  let δ₀_norm : ℝ := C_norm ^ (1 / ε_norm)
  let C_κ_real : ℝ := (Nat.ceil ((2 : ℝ)^(1/κ)) + 2 : ℝ)
  let C_abs2Cκ : ℝ := (2 * C_κ_real)⁻¹
  let δ₀_abs2Cκ : ℝ := C_abs2Cκ ^ (1 / ε_norm)
  -- Threshold for step6 cubic absorption: δ^(3*ε_tloss) ≤ 1/(486*(2^(N/κ)+3))
  let C_cubic : ℝ := 1 / (486 * ((2 : ℝ)^((N : ℝ)/κ) + 3))
  let δ₀_cubic : ℝ := C_cubic ^ (1 / (3 * ε_tloss))
  -- Geometric threshold: δ^(ε_A*m) ≤ c_step / C_energy
  -- Obtain actual c_step from Step3-5 theorem and C_energy from product-measure bridge
  have hκ_lt_one : κ < 1 := by linarith [hκ_le_s, hs_lt_one]
  have hm_ge2 : 2 ≤ m := by
    by_contra h
    have h_lt2 : m < 2 := by omega
    have h_m01 : m = 0 ∨ m = 1 := by omega
    rcases h_m01 with (h_m0 | h_m1)
    · have h6 : (m : ℝ) = 0 := by exact_mod_cast h_m0
      rw [h6] at hm
      norm_num at hm
    · have h6 : (m : ℝ) = 1 := by exact_mod_cast h_m1
      rw [h6] at hm
      have h7 : 1 < κ := by simpa using hm
      linarith [hκ_lt_one]
  let M_X : ℝ := (N : ℝ)
  have hM_X_pos : 0 < M_X := by
    dsimp only [M_X]
    exact_mod_cast hN_pos
  rcases step3_5_marstrand_mdim (hm := hm_ge2) (c_X := c_X) (M_X := M_X) hcX_pos hM_X_pos with
    ⟨c_step, hc_step_pos, h_geo⟩
  rcases product_measure_bridge_uniform hκ_pos (by linarith) hm with
    ⟨C_energy, hC_energy_pos, h_bridge⟩
  let δ₀_geom : ℝ := (c_step / C_energy) ^ (1 / (ε_A * (m : ℝ)))
  let δ₀ : ℝ := min (1 / 2) (min δ₀_PR (min δ₀_triangle (min δ₀_sum
      (min δ₀_poly (min δ₀_abs9 (min δ₀_abs12 (min δ₀_norm (min δ₀_abs2Cκ (min δ₀_cubic δ₀_geom)))))))))
  have hδ₀_pos : 0 < δ₀ := by positivity
  have hδ₀_le_one : δ₀ ≤ 1 := by
    have h : δ₀ ≤ 1 / 2 := by
      exact min_le_left _ _
    linarith
  refine' ⟨δ₀, hδ₀_pos, _⟩
  intro δ hδ hδ_pos hδle
  intro A μ t hA_sub hA_delta hA_measure hA_size hμ hμ_supp ht_lower ht_le_one
  have hμ_univ : μ Set.univ = 1 := hμ.1
  have hA_bdd : Bornology.IsBounded A :=
    (Metric.isBounded_Icc (1 : ℝ) 2).subset hA_sub
  -- Phase 1: normalize μ to constant 2*C₀, supported away from 0
  rcases phase1_normalize hκ_pos hC₀_pos hC₀_le hμ hμ_supp hμ_univ with
    ⟨μ', hμ'_frost, hμ'_supp, hμ'_sub, hμ'_univ⟩
  let K' := μ'.support
  have hK'_bdd : Bornology.IsBounded K' :=
    (Metric.isBounded_Icc (0 : ℝ) 1).subset hμ_supp |>.subset hμ'_sub
  -- Bounds for phase 2
  have ht_pos : 0 < t := by
    have h1 : 0 < δ ^ c := by positivity
    linarith
  have hδ_le_one : δ ≤ 1 := by
    calc δ ≤ δ₀ := hδle
         _ ≤ 1 / 2 := min_le_left _ _
         _ ≤ 1 := by norm_num
  -- hA_size is given directly as a hypothesis
  -- hδ_poly: choose δ₀ small enough for step6 polynomial bound
  have hδ_poly : δ ^ γ ≤ C6⁻¹ := by
    have h1 : δ ≤ δ₀ := hδle
    have h2 : δ₀ ≤ δ₀_poly := by
      exact le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _)
          (le_trans (min_le_right _ _)
            (le_trans (min_le_right _ _)
              (min_le_left _ _))))
    have h3 : δ ≤ δ₀_poly := le_trans h1 h2
    have h4 : 0 ≤ δ := by linarith
    have h5 : δ ^ γ ≤ δ₀_poly ^ γ := by
      gcongr <;> linarith
    have h6 : δ₀_poly ^ γ = C6⁻¹ := by
      dsimp only [δ₀_poly]
      have h7 : 0 ≤ C6⁻¹ := by positivity
      rw [← Real.rpow_mul h7]
      have h8 : (1 / γ) * γ = 1 := by
        exact one_div_mul_cancel hγ_pos.ne'
      rw [h8, Real.rpow_one]
    rw [h6] at h5
    exact h5
  -- Phase 3: triangle + sum (double normalization + normalized wrapper)
  -- K' is compact (closed support + bounded)
  have hK'_compact : IsCompact K' := by
    have h1 : IsClosed K' := Measure.isClosed_support
    exact Metric.isCompact_of_isClosed_isBounded h1 hK'_bdd
  -- Double normalization: scale K' by b = sSup K' so 1 ∈ K''
  rcases scale_support_to_contain_one hκ_pos (by positivity) hμ'_frost hμ'_supp hμ'_univ
    with ⟨b, ν, hb_pos, hb_le_one, hb_ge_a, hb_in_K', hb_max, hν_frost, hν_supp_eq, h1_in_K'', hν_supp_Icc, hν_univ⟩
  let K'' := ν.support
  have hK''_eq : K'' = scaleSet b⁻¹ K' := hν_supp_eq
  have hK''_bounds : K'' ⊆ Set.Icc ((2:ℝ)^(-(1/κ))) 1 := hν_supp_Icc
  have hK''_bdd : Bornology.IsBounded K'' :=
    (Metric.isBounded_Icc ((2:ℝ)^(-(1/κ))) 1).subset hK''_bounds
  have hK''_compact : IsCompact K'' := by
    rw [hK''_eq]
    exact hK'_compact.image (continuous_const.mul continuous_id)
  have hK''_nonempty : K''.Nonempty := ⟨1, h1_in_K''⟩
  -- Re-run expansion on K''
  have h_a_nonneg'' : 0 ≤ (2 : ℝ)^(-(1/κ)) := by positivity
  have hK''_supp01 : K'' ⊆ Set.Icc (0 : ℝ) 1 :=
    hK''_bounds.trans (Set.Icc_subset_Icc h_a_nonneg'' (by norm_num))
  -- Frostman monotonicity: 2*C₀ ≤ 2^(κ+1) since C₀ ≤ 2^κ
  have h2C0_le_Cbar : (2 : ℝ) * C₀ ≤ (2 : ℝ)^(κ+1) := by
    have h1 : C₀ ≤ (2 : ℝ)^κ := hC₀_le
    have h2 : (2 : ℝ) * C₀ ≤ (2 : ℝ) * (2 : ℝ)^κ := by gcongr
    have h3 : (2 : ℝ) * (2 : ℝ)^κ = (2 : ℝ)^(κ+1) := by
      have h4 : (2 : ℝ)^(κ+1) = (2 : ℝ)^κ * (2 : ℝ)^(1 : ℝ) :=
        Real.rpow_add (by norm_num) κ (1 : ℝ)
      have h5 : (2 : ℝ)^(1 : ℝ) = (2 : ℝ) := by simp
      rw [h4, h5] <;> ring
    linarith
  have hν_frost_Cbar : IsAllScaleFrostman κ ((2 : ℝ)^(κ+1)) ν :=
    hν_frost.mono h2C0_le_Cbar
  have hX_lower' : ENNReal.ofReal c_X ≤ MeasureTheory.volume (expansionSet K'' N) :=
    hN_uniform ν hν_frost_Cbar hK''_supp01 hν_univ
  have hX_bdd' : Bornology.IsBounded (expansionSet K'' N) := bounded_expansionSet hK''_bdd
  have hX_compact' : IsCompact (expansionSet K'' N) := compact_expansionSet hK''_compact
  -- t' = b * t
  let t' : ℝ := b * t
  have ht'_pos : 0 < t' := mul_pos hb_pos ht_pos
  have ht'_le_one : t' ≤ 1 := by
    calc t' = b * t := by rfl
      _ ≤ 1 * 1 := by gcongr <;> linarith
      _ = 1 := by ring
  -- δ^{ε_norm} ≤ C_abs2Cκ ≤ C_norm ≤ b
  have hδ_abs2Cκ : δ ^ ε_norm ≤ C_abs2Cκ := by
    have h1 : δ ≤ δ₀ := hδle
    have h2 : δ₀ ≤ δ₀_abs2Cκ := by
      refine' le_trans (min_le_right _ _) _
      refine' le_trans (min_le_right _ _) _
      refine' le_trans (min_le_right _ _) _
      refine' le_trans (min_le_right _ _) _
      refine' le_trans (min_le_right _ _) _
      refine' le_trans (min_le_right _ _) _
      refine' le_trans (min_le_right _ _) _
      refine' le_trans (min_le_right _ _) _
      exact min_le_left _ _
    have h3 : δ ≤ δ₀_abs2Cκ := le_trans h1 h2
    have h4 : 0 ≤ δ := by linarith
    have h5 : δ ^ ε_norm ≤ δ₀_abs2Cκ ^ ε_norm := by gcongr <;> linarith
    have h6 : δ₀_abs2Cκ ^ ε_norm = C_abs2Cκ := by
      dsimp only [δ₀_abs2Cκ]
      have h7 : 0 ≤ C_abs2Cκ := by positivity
      rw [← Real.rpow_mul h7]
      have h8 : (1 / ε_norm) * ε_norm = 1 := by field_simp [hε_norm_pos.ne'] <;> ring
      rw [h8, Real.rpow_one]
    rw [h6] at h5; exact h5
  have hC_abs2Cκ_le_norm : C_abs2Cκ ≤ C_norm := by
    have h1 : 0 < C_κ_real := by positivity
    have h2 : (2 : ℝ)^(1/κ) ≤ C_κ_real := by
      dsimp only [C_κ_real]
      have h3 : (2 : ℝ)^(1/κ) ≤ Nat.ceil ((2 : ℝ)^(1/κ)) := Nat.le_ceil _
      linarith
    have h3 : (2 : ℝ)^(1/κ) ≤ 2 * C_κ_real := by linarith
    have h4 : 0 < 2 * C_κ_real := by positivity
    have h4' : 0 < (2 : ℝ)^(1/κ) := by positivity
    have h5 : (2 * C_κ_real)⁻¹ ≤ ((2 : ℝ)^(1/κ))⁻¹ := by
      gcongr
      <;> linarith
    have h6 : ((2 : ℝ)^(1/κ))⁻¹ = (2 : ℝ)^(-(1/κ)) := by
      rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ (2 : ℝ)) (1 / κ)]
    have h_abs : C_abs2Cκ = (2 * C_κ_real)⁻¹ := by rfl
    have h_norm : C_norm = (2 : ℝ)^(-(1/κ)) := by rfl
    rw [h_abs, h_norm]
    rw [h6] at h5
    exact h5
  have hδ_norm_b : δ ^ ε_norm ≤ b :=
    le_trans (le_trans hδ_abs2Cκ hC_abs2Cκ_le_norm) hb_ge_a
  -- h_t_lower' : δ^{c'} ≤ t'
  have h_t_lower' : δ ^ c' ≤ t' := by
    have h1 : δ ^ c' = δ ^ c * δ ^ ε_norm := by
      have h2 : c' = c + ε_norm := by rfl
      rw [h2, ← Real.rpow_add hδ_pos] <;> ring
    rw [h1]
    calc δ ^ c * δ ^ ε_norm ≤ δ ^ c * b := by gcongr
      _ = b * (δ ^ c) := by rw [mul_comm]
      _ ≤ b * t := by gcongr
      _ = t' := by rfl
  -- h_c'_le : c' ≤ (1 - s) / 4
  have h_c'_le : c' ≤ (1 - s) / 4 := by
    have hε : ε_norm = c / 100 := by rfl
    have hc' : c' = c + ε_norm := by rfl
    have h1 : c' = (101 / 100 : ℝ) * c := by
      rw [hc', hε] <;> ring
    have hm_ne_zero : m ≠ 0 := by
      intro h0
      rw [h0] at hm_pos
      norm_num at hm_pos
    have hm1 : 1 ≤ (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm_ne_zero
    have hN1 : 1 ≤ (N : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr hN_pos)
    have h_k_ge1 : k ≥ 1 := by
      dsimp only [k]
      have h2 : (m : ℝ) ≥ 1 := hm1
      have h3 : (N : ℝ) ≥ 1 := hN1
      have h4 : (m : ℝ) * (N : ℝ) ≥ 1 := by
        have h5 : (m : ℝ) ≥ 1 := hm1
        have h6 : (N : ℝ) ≥ 1 := hN1
        have h7 : (m : ℝ) * (N : ℝ) ≥ 1 * 1 := mul_le_mul h5 h6 (by linarith) (by linarith)
        calc (m : ℝ) * (N : ℝ) ≥ 1 * 1 := h7
          _ = 1 := by ring
      exact h4
    have h2N1 : 2 * (N : ℝ) + 1 ≥ 3 := by linarith
    have h_denom : 400 * k * (2 * (N : ℝ) + 1) ≥ 1200 := by
      have h4 : k ≥ 1 := h_k_ge1
      have h5 : 2 * (N : ℝ) + 1 ≥ 3 := h2N1
      have h6 : k * (2 * (N : ℝ) + 1) ≥ 3 := by
        have h61 : k * (2 * (N : ℝ) + 1) ≥ 1 * (2 * (N : ℝ) + 1) := by
          exact mul_le_mul_of_nonneg_right h4 (by linarith)
        have h62 : 1 * (2 * (N : ℝ) + 1) ≥ 3 := by linarith
        linarith
      have h7 : 400 * (k * (2 * (N : ℝ) + 1)) ≥ 400 * 3 := by
        gcongr <;> linarith
      have h8 : 400 * (k * (2 * (N : ℝ) + 1)) = 400 * k * (2 * (N : ℝ) + 1) := by ring
      rw [← h8]
      linarith
    have h_c_le : c ≤ (1 - s) / 1200 := by
      dsimp only [c]
      exact div_le_div_of_nonneg_left (by linarith) (by positivity) h_denom
    have h9 : 0 ≤ 1 - s := by linarith
    have h10 : (101 / 100 : ℝ) * c ≤ (1 - s) / 4 := by
      have h11 : (101 / 100 : ℝ) * c ≤ (101 / 100 : ℝ) * ((1 - s) / 1200) := mul_le_mul_of_nonneg_left h_c_le (by norm_num)
      have h12 : (101 / 100 : ℝ) * ((1 - s) / 1200) = (1 - s) * ((101 : ℝ) / 120000) := by ring
      have h13 : (101 : ℝ) / 120000 ≤ 1 / 4 := by norm_num
      have h14 : (1 - s) * ((101 : ℝ) / 120000) ≤ (1 - s) * (1 / 4 : ℝ) := mul_le_mul_of_nonneg_left h13 h9
      have h15 : (1 - s) * (1 / 4 : ℝ) = (1 - s) / 4 := by ring
      calc (101 / 100 : ℝ) * c
        ≤ (101 / 100 : ℝ) * ((1 - s) / 1200) := h11
      _ = (1 - s) * ((101 : ℝ) / 120000) := h12
      _ ≤ (1 - s) * (1 / 4 : ℝ) := h14
      _ = (1 - s) / 4 := h15
    rw [h1]
    exact h10
  have h_t_lower4' : δ ^ ((1 - s) / 4) ≤ t' := by
    have h4 : δ ^ ((1 - s) / 4) ≤ δ ^ c' :=
      Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_le_one h_c'_le
    exact le_trans h4 h_t_lower'
  -- h_tloss: t'^(2/3) ≥ δ^ε_tloss (since ε_tloss = 2c'/3 and t' ≥ δ^c')
  have h_tloss : t' ^ (2 / 3 : ℝ) ≥ δ ^ ε_tloss := by
    have h1 : t' ^ (2 / 3 : ℝ) ≥ (δ ^ c') ^ (2 / 3 : ℝ) := by gcongr
    have h2 : (δ ^ c') ^ (2 / 3 : ℝ) = δ ^ (c' * (2 / 3 : ℝ)) := by
      rw [← Real.rpow_mul (by linarith)] <;> ring
    rw [h2] at h1
    have h3 : c' * (2 / 3 : ℝ) = ε_tloss := by
      dsimp only [ε_tloss] <;> ring
    rw [h3] at h1
    exact h1
  -- h_cubic_absorb: δ^(3*ε_tloss) ≤ C_cubic
  have h_cubic_absorb : δ ^ (3 * ε_tloss) ≤ C_cubic := by
    have h2 : δ₀ ≤ δ₀_cubic := by
      exact (min_le_right _ _).trans <|
        (min_le_right _ _).trans <|
        (min_le_right _ _).trans <|
        (min_le_right _ _).trans <|
        (min_le_right _ _).trans <|
        (min_le_right _ _).trans <|
        (min_le_right _ _).trans <|
        (min_le_right _ _).trans <|
        (min_le_right _ _).trans <|
        min_le_left _ _
    have hC_cubic_nonneg : 0 ≤ C_cubic := by
      dsimp only [C_cubic]; positivity
    have hthreshold : δ₀_cubic = C_cubic ^ (1 / (3 * ε_tloss)) := by
      dsimp only [δ₀_cubic] <;> rfl
    exact rpow_absorption hδ_pos hC_cubic_nonneg (by positivity) (le_trans hδle h2) hthreshold
  -- Re-run phase2 on K'' with t'
  have h_threshold : δ ^ (ε_A * (m : ℝ)) ≤ c_step / C_energy := by
    have h1 : 0 < ε_A * (m : ℝ) := by positivity
    have h2 : δ ≤ δ₀_geom := by
      have hδ₀_le : δ ≤ δ₀ := hδle
      have h₀_le_geom : δ₀ ≤ δ₀_geom := nested_min_le_last10
      exact le_trans hδ₀_le h₀_le_geom
    have h3 : δ ^ (ε_A * (m : ℝ)) ≤ (c_step / C_energy) := by
      have h4 : 0 ≤ c_step / C_energy := by positivity
      have h5 : 0 ≤ ε_A * (m : ℝ) := by positivity
      have h6 : δ ^ (ε_A * (m : ℝ)) ≤ (δ₀_geom) ^ (ε_A * (m : ℝ)) := by
        gcongr
        <;> linarith [hδ_pos]
      have h7 : (δ₀_geom) ^ (ε_A * (m : ℝ)) = c_step / C_energy := by
        dsimp only [δ₀_geom]
        have h_pos : 0 ≤ c_step / C_energy := by positivity
        rw [← Real.rpow_mul h_pos]
        have h_mul : (1 / (ε_A * (m : ℝ))) * (ε_A * (m : ℝ)) = 1 := by
          field_simp [h1.ne'] <;> ring
        rw [h_mul, Real.rpow_one]
      rw [h7] at h6
      exact h6
    exact h3
  rcases phase2_marstrand_pr (hκ_pos := hκ_pos) (hε_A_pos := hε_A_pos)
      (hε_geom_pos := hε_geom_pos)
      (hs_pos := hs_pos) (hs_lt_one := hs_lt_one) (hδ_pos := hδ_pos)
      (ht_pos := ht'_pos) (hm := hm) (hA_delta := hA_delta)
      (hA_measure := hA_measure) (hcX_pos := hcX_pos) (hX_lower := hX_lower') (hX_bdd := hX_bdd')
      (hX_compact := hX_compact')
      (c_step := c_step) (C_energy := C_energy)
      (hc_step_pos := hc_step_pos) (hC_energy_pos := hC_energy_pos)
      (M_X := M_X) (hM_X_pos := hM_X_pos)
      (h_geo := h_geo) (h_bridge := h_bridge)
      (hX_sub := expansionSet_subset_Icc hK''_supp01)
      (hA_sub2 := hA_sub) (hδ_le_one := by linarith [hδle, hδ₀_le_one])
      (h_ε_geom_m := h_ε_geom_m) (h_ε_geom := h_ε_geom) (h_threshold := h_threshold)
      (h_t_lower4 := h_t_lower4') (ht_le_one := ht'_le_one)
      (hA_size := hA_size) (hK_bounds := hK''_bounds)
      (ε_tloss := ε_tloss) (hε_tloss_pos := hε_tloss_pos)
      (γ := γ) (hγ_pos := hγ_pos) (hγ_eq := hγ_eq)
      (hδ_poly := hδ_poly)
      (h_tloss := h_tloss) (h_cubic_absorb := h_cubic_absorb)
      (δ₀ := δ₀) (hδ_small := hδle) (hδ₀_le_one := hδ₀_le_one)
      (hK_bdd := hK''_bdd) (hA_bdd := hA_bdd) with
    ⟨y, hy_in_KN, h_y_expansion⟩
  have hA_nonempty : A.Nonempty := by
    have h1 : IsRealDeltaSet δ κ (δ ^ (-ε_A)) A := hA_delta
    have h2 : (realLineCopy A).Nonempty := h1.2.1
    rcases h2 with ⟨p, hp⟩
    have h3 : p 0 ∈ A := by simpa [realLineCopy] using hp
    exact ⟨p 0, h3⟩
  have hK'_nonempty : K'.Nonempty := by
    by_contra h
    have h_empty : K' = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    have h_compl : μ' K'ᶜ = 0 := Measure.measure_compl_support
    rw [h_empty] at h_compl; simp at h_compl
    have h_univ : μ' Set.univ = 0 := by simpa using h_compl
    have hμ'_univ : μ' Set.univ = 1 := hμ'_frost.1
    rw [hμ'_univ] at h_univ; norm_num at h_univ
  -- Step 9-11 absorption
  have hδ_abs9 : δ ^ ε_abs ≤ C_abs9 := by
    have h2 : δ₀ ≤ δ₀_abs9 := by
      exact (min_le_right _ _).trans <|
        (min_le_right _ _).trans <|
        (min_le_right _ _).trans <|
        (min_le_right _ _).trans <|
        (min_le_right _ _).trans <|
        min_le_left _ _
    exact rpow_absorption hδ_pos (by positivity) hε_abs_pos (le_trans hδle h2)
      (by dsimp only [δ₀_abs9] <;> rfl)
  -- Convert h_y_expansion to explicit α_in for type matching with step9_11
  have hk_eq : k = (m : ℝ) * (N : ℝ) := by rfl
  have hα_in_eq : α_in = (-(1 - s) / (24 * ((m : ℝ) * (N : ℝ))) + ε_tloss) := by
    have h1 : α_in = (-(1 - s) / (24 * k)) + ε_tloss := by rfl
    rw [h1, hk_eq]
    <;> ring
  have h_y_expansion' : ENNReal.ofReal (δ ^ α_in) * Nreal δ (scaleSet (t')⁻¹ A) ≤
      Nreal δ (Set.image2 (· - ·) (scaleSet (t')⁻¹ A) (scaleSet y A)) := by
    have h9 : δ ^ α_in = δ ^ ((-(1 - s) / (24 * ((m : ℝ) * (N : ℝ))) + ε_tloss)) := by
      rw [hα_in_eq]
    rw [h9]
    exact h_y_expansion
  -- Step 9-11 on K'' with t'
  have h_step9_11 : ∃ (w : ℝ), (w = 1 ∨ w ∈ K'') ∧
      ENNReal.ofReal (δ ^ (c' * (N : ℝ) / (2 * (N : ℝ) + 1) +
        α_in / (2 * (N : ℝ) + 1) + ε_abs)) *
      Nreal δ (scaleSet (t')⁻¹ A) ≤
      Nreal δ (Set.image2 (· - ·) (scaleSet (t')⁻¹ A) (scaleSet w A)) :=
    step9_11_triangle_correct (A := A) (K := K'') (N0 := N) hN_pos
      (hδ_pos := hδ_pos) (ht_pos := ht'_pos) (ht_le_one := ht'_le_one)
      (hc_pos := hc'_pos) (hκ_pos := hκ_pos) (hε_abs_pos := hε_abs_pos)
      (α_in := α_in)
      (hy := hy_in_KN) (h_y_expansion := h_y_expansion')
      (hK_bounds := hK''_bounds) (h_t_lower := h_t_lower')
      (hδ_small := hδle) (hδ₀_le_one := hδ₀_le_one)
      (hδ_absorb := hδ_abs9)
      (hK_bdd := hK''_bdd) (hA_bdd := hA_bdd)
      (hA_nonempty := hA_nonempty) (hK_nonempty := hK''_nonempty)
  rcases h_step9_11 with ⟨w, hw_cases, h_expansion⟩
  have hw_cases' : w = 1 ∨ w ∈ scaleSet b⁻¹ K' := by
    rcases hw_cases with (h | h)
    · left; exact h
    · right; rw [hK''_eq] at h; exact h
  -- Step 12 absorption
  have hδ_abs12 : δ ^ exp12 ≤ C_abs12 := by
    have h2 : δ₀ ≤ δ₀_abs12 := by
      exact (min_le_right _ _).trans <|
        (min_le_right _ _).trans <|
        (min_le_right _ _).trans <|
        (min_le_right _ _).trans <|
        (min_le_right _ _).trans <|
        (min_le_right _ _).trans <|
        min_le_left _ _
    have hC12_nonneg : 0 ≤ C_abs12 := by
      dsimp only [C_abs12]; positivity
    have hthreshold : δ₀_abs12 = C_abs12 ^ (1 / exp12) := by
      dsimp only [δ₀_abs12] <;> rfl
    exact rpow_absorption hδ_pos hC12_nonneg hexp12_pos (le_trans hδle h2) hthreshold
  have hδ_abs12' : δ ^ (-(β_in + 4 * c')) ≤ (2 : ℝ)^(-(1/κ)) / 729 := by
    have h_eq1 : exp12 = -(β_in + 4 * c') := by rfl
    have h_eq2 : C_abs12 = (2 : ℝ)^(-(1/κ)) / 729 := by rfl
    rw [h_eq1, h_eq2] at hδ_abs12
    exact hδ_abs12
  -- Step 12 normalized wrapper
  rcases step12_diff_to_sum_normalized
      (A := A) (K := K') (δ := δ) (δ₀ := δ₀) (t := t) (c := c') (κ := κ) (β_in := β_in)
      (hδ_pos := hδ_pos) (ht_pos := ht_pos) (ht_le_one := ht_le_one)
      (hc_pos := hc'_pos) (hκ_pos := hκ_pos)
      (b := b) (hb_pos := hb_pos) (hb_le_one := hb_le_one) (hb_ge_a := hb_ge_a)
      (hb_in_K := hb_in_K') (hb_max := hb_max)
      (w := w) (hw_cases := hw_cases')
      (hβ_in_neg := hβ_in_neg)
      (h_expansion := h_expansion)
      (hK_bounds := hμ'_supp)
      (h_t_lower := h_t_lower')
      (hδ_small := hδle) (hδ₀_le_one := hδ₀_le_one)
      (hδ_absorb := hδ_abs12')
      (hK_bdd := hK'_bdd) (hA_bdd := hA_bdd)
      (hK_nonempty := hK'_nonempty) (hA_nonempty := hA_nonempty)
    with ⟨x, hx_in_K', h_result⟩
  -- Absorb 2*C_κ constant
  have hε_norm_lt_c' : ε_norm < c' := by
    have h_eq : c' = c + ε_norm := by rfl
    rw [h_eq]
    exact lt_add_of_pos_left ε_norm hc_pos
  have h2Cκ_pos : 0 < (2 * C_κ_real) := by positivity
  have h_final : ENNReal.ofReal (δ ^ (-c)) * Nreal δ (scaleSet t⁻¹ A) ≤
      Nreal δ (Set.image2 (fun a b => a + x * b) (scaleSet t⁻¹ A) A) := by
    have hCκ_def : C_κ_real = ((Nat.ceil ((2 : ℝ)^(1/κ)) + 2 : ℝ)) := by rfl
    have h_match : (2 * ((Nat.ceil ((2 : ℝ)^(1/κ)) + 2 : ENNReal))) =
        ENNReal.ofReal (2 * C_κ_real) := by
      rw [hCκ_def]
      exact two_Cκ_match κ hκ_pos
    rw [h_match] at h_result
    have h_abs := ennreal_absorb_constant
      (hδ_pos := hδ_pos) (hc_pos := hc'_pos) (hε_pos := hε_norm_pos)
      (hε_lt_c := hε_norm_lt_c') (hC_pos := h2Cκ_pos)
      (hδ_absorb := hδ_abs2Cκ) (h := h_result)
    have h9 : c' - ε_norm = c := by
      dsimp only [c', ε_norm]; ring
    rw [h9] at h_abs
    exact h_abs
  have hx_in_original : x ∈ μ.support := hμ'_sub hx_in_K'
  exact ⟨x, hx_in_original, h_final⟩

end
