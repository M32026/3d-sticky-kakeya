module

/-
  Induction Steps 1 and 7 for InductionOnScalesRewrite.

  Step 1: Coarse rounding map on DyadicTube n — nearest-multiple rounding
    to scale m, with distance ≤ scale m, separation, and packing bound.
  Step 7: Multiplicative inequality chaining.

  Whiteprint node: induction_on_scales / InductionSteps
  Dependencies: DyadicTubes, CommonTubeEnergyExtraction
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.DiscretisedFurstenbergEstimate.QuantitativeThickTubeCover
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DirecretisedFurstenbergEstimate.InductionOnScales

open DiscretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate

attribute [local instance] Classical.propDecidable

/-!
  # Step 1: Coarse rounding map for DyadicTube n

  Rounds tube indices (a,b) to nearest multiple of refinementFactor n m = 2^(n-m).
  This gives a "coarse grid" tube at scale m, represented as a DyadicTube n.
-/

/-- The refinement factor between scales n and m: 2^(n-m). -/
def refinementFactor (n m : ℕ) : ℕ := 2 ^ (n - m)

lemma refinementFactor_pos (n m : ℕ) : 0 < refinementFactor n m := by
  dsimp only [refinementFactor]
  exact pow_pos (by norm_num) _

lemma dyadicDelta_mul_refinement (n m : ℕ) (hnm : m ≤ n) :
    dyadicDelta n * (refinementFactor n m : ℝ) = dyadicDelta m := by
  dsimp only [refinementFactor, dyadicDelta]
  have h : (n - m) + m = n := Nat.sub_add_cancel hnm
  rw [←h]
  simp [pow_add]
  <;> ring

/-- Round an integer to the nearest multiple of k (k > 0).
    Error ≤ k/2. -/
def roundToMultiple (k : ℕ) (i : ℤ) : ℤ :=
  (i + (k : ℤ) / 2) / (k : ℤ) * (k : ℤ)

lemma roundToMultiple_is_multiple (k : ℕ) (i : ℤ) :
    (k : ℤ) ∣ roundToMultiple k i := by
  let q : ℤ := (i + (k : ℤ) / 2) / (k : ℤ)
  have h : roundToMultiple k i = q * (k : ℤ) := by rfl
  refine' ⟨q, _⟩
  rw [h] <;> ring

/-- If d > 0 divides x ≠ 0, then |x| ≥ d. -/
lemma abs_ge_of_dvd {d x : ℤ} (hd_pos : 0 < d) (hdvd : d ∣ x) (hx_ne : x ≠ 0) :
    (d : ℝ) ≤ |(x : ℝ)| := by
  rcases hdvd with ⟨k, hk⟩
  have hk_ne : k ≠ 0 := by
    intro h
    rw [h] at hk
    simp at hk <;> tauto
  have h2 : (x : ℝ) = (d : ℝ) * (k : ℝ) := by exact_mod_cast hk
  have h1 : |(x : ℝ)| = (d : ℝ) * |(k : ℝ)| := by
    rw [h2]
    have h3 : |(d : ℝ) * (k : ℝ)| = |(d : ℝ)| * |(k : ℝ)| := abs_mul _ _
    rw [h3]
    have h4 : |(d : ℝ)| = (d : ℝ) := abs_of_pos (by exact_mod_cast hd_pos)
    rw [h4] <;> ring
  rw [h1]
  have h3 : (1 : ℝ) ≤ |(k : ℝ)| := by
    have h4 : (1 : ℤ) ≤ |k| := Int.one_le_abs hk_ne
    exact_mod_cast h4
  have h5 : (0 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd_pos.le
  nlinarith

lemma roundToMultiple_bound (k : ℕ) (hk_pos : 0 < k) (i : ℤ) :
    |(i - roundToMultiple k i : ℤ)| ≤ (k : ℝ) / 2 := by
  set k' : ℤ := ↑k with hk'
  set half : ℤ := k' / 2 with hhalf
  set q : ℤ := (i + half) / k' with hq
  set r : ℤ := (i + half) % k' with hr
  have hk'_pos : 0 < k' := by simpa [hk'] using hk_pos
  have h_raw : (i + half) / k' * k' + (i + half) % k' = i + half := by exact Int.ediv_mul_add_emod (i + half) k'
  have h_div : q * k' + r = i + half := by
    have hq' : q = (i + half) / k' := by rfl
    have hr' : r = (i + half) % k' := by rfl
    rw [hq', hr']
    exact h_raw
  have h_r_nonneg : 0 ≤ r := Int.emod_nonneg _ hk'_pos.ne'
  have h_r_lt : r < k' := Int.emod_lt_of_pos _ hk'_pos
  have h_k'_nonneg : 0 ≤ k' := by omega
  have h2_nonneg : (0 : ℤ) ≤ 2 := by norm_num
  have h_half_nonneg : 0 ≤ half := Int.ediv_nonneg h_k'_nonneg h2_nonneg
  have h_half_lt_k : half < k' := by omega
  have h2half_le_k : 2 * half ≤ k' := by omega
  have h_k_le_2half_add1 : k' ≤ 2 * half + 1 := by omega
  have h_main : i - q * k' = r - half := by linarith
  have h_goal : (i - roundToMultiple k i : ℤ) = r - half := by
    have h9 : roundToMultiple k i = q * k' := by rfl
    rw [h9]; exact h_main
  rw [h_goal]
  have h_lower : -(k' : ℝ) / 2 ≤ (r - half : ℝ) := by
    have h_r0 : (0 : ℝ) ≤ (r : ℝ) := by exact_mod_cast h_r_nonneg
    have h_half_upper : (half : ℝ) ≤ (k' : ℝ) / 2 := by
      have h : 2 * (half : ℝ) ≤ (k' : ℝ) := by exact_mod_cast h2half_le_k
      linarith
    linarith
  have h_upper : (r - half : ℝ) ≤ (k' : ℝ) / 2 := by
    have h_r_upper : (r : ℝ) ≤ (k' : ℝ) - 1 := by
      have h : r ≤ k' - 1 := by omega
      exact_mod_cast h
    have h_half_lower : ((k' : ℝ) - 1) / 2 ≤ (half : ℝ) := by
      have h : (k' : ℝ) ≤ 2 * (half : ℝ) + 1 := by exact_mod_cast h_k_le_2half_add1
      linarith
    linarith
  have h_abs : |(r - half : ℝ)| ≤ (k' : ℝ) / 2 := by
    rw [abs_le]
    constructor <;> linarith
  have h_cast : (↑|r - half| : ℝ) = |(r - half : ℝ)| := by
    simp
  rw [h_cast]
  have h_k'_eq_k : (k' : ℝ) = (k : ℝ) := by simp [hk']
  rw [h_k'_eq_k] at h_abs
  exact h_abs

lemma roundToMultiple_idempotent (k : ℕ) (hk_pos : 0 < k) (i : ℤ) :
    roundToMultiple k (roundToMultiple k i) = roundToMultiple k i := by
  set k' : ℤ := ↑k with hk'
  set half : ℤ := k' / 2 with hhalf
  set q : ℤ := (i + half) / k' with hq
  have hk'_pos : 0 < k' := by simpa [hk'] using hk_pos
  have h_k'_nonneg : 0 ≤ k' := by omega
  have h2_nonneg : (0 : ℤ) ≤ 2 := by norm_num
  have h_half_nonneg : 0 ≤ half := Int.ediv_nonneg h_k'_nonneg h2_nonneg
  have h_half_lt : half < k' := by omega
  have h1 : roundToMultiple k i = q * k' := by rfl
  rw [h1]
  have h_half_range1 : 0 ≤ half := by omega
  have h_half_range2 : half < k' := by omega
  have h_mod : (q * k' + half) % k' = half := by
    set x : ℤ := q * k' + half with hx
    have h_div_alg : x / k' * k' + x % k' = x := by exact Int.ediv_mul_add_emod x k'
    have h4 : 0 ≤ x % k' := Int.emod_nonneg _ hk'_pos.ne'
    have h5 : x % k' < k' := Int.emod_lt_of_pos _ hk'_pos
    have h6 : k' ∣ (x - x % k') := by
      use x / k'
      linarith [h_div_alg]
    have h7 : k' ∣ (x - half) := by
      use q
      <;> simp [hx] <;> ring
    have h8 : k' ∣ (x % k' - half) := by
      have h9 : k' ∣ (x - half) - (x - x % k') := dvd_sub h7 h6
      have h10 : (x - half) - (x - x % k') = x % k' - half := by ring
      rw [h10] at h9
      exact h9
    rcases h8 with ⟨j, hj⟩
    have h_eq : x % k' = half + j * k' := by linarith
    have h_j_zero : j = 0 := by
      by_cases h_j_pos : 0 < j
      · have h_ge : x % k' ≥ k' := by
          have h_j1 : j ≥ 1 := by linarith
          nlinarith
        linarith
      · by_cases h_j_neg : j < 0
        · have h_lt : x % k' < 0 := by
            have h_j1 : j ≤ -1 := by linarith
            nlinarith
          linarith
        · linarith
    rw [h_eq, h_j_zero] <;> ring
  have h_eq : (q * k' + half) / k' * k' + (q * k' + half) % k' = q * k' + half := by exact Int.ediv_mul_add_emod (q * k' + half) k'
  rw [h_mod] at h_eq
  have h_result : (q * k' + half) / k' * k' = q * k' := by linarith
  have hk'_ne : k' ≠ 0 := by omega
  have h2 : (q * k' + half) / k' = q := by
    apply (mul_right_inj' hk'_ne).mp
    linarith
  have h5 : roundToMultiple k (q * k') = ((q * k' + half) / k') * k' := by rfl
  rw [h5, h2] <;> ring

/-- Coarse rounding of a dyadic tube to scale m.
    Rounds a and b to nearest multiple of refinementFactor n m. -/
def coarseRound (n m : ℕ) (hnm : m ≤ n) (T : DyadicTube n) : DyadicTube n :=
  let rf := refinementFactor n m
  ⟨roundToMultiple rf T.a, roundToMultiple rf T.b⟩

/-- Distance between a tube and its coarse rounding is ≤ scale m. -/
lemma coarseRound_dist (n m : ℕ) (hnm : m ≤ n) (T : DyadicTube n) :
    dist T (coarseRound n m hnm T) ≤ dyadicDelta m := by
  let rf := refinementFactor n m
  have hrf_pos : 0 < rf := refinementFactor_pos n m
  let T' := coarseRound n m hnm T
  have ha : |(T.a : ℝ) - (T'.a : ℝ)| ≤ (rf : ℝ) / 2 := by
    exact_mod_cast roundToMultiple_bound rf hrf_pos T.a
  have hb : |(T.b : ℝ) - (T'.b : ℝ)| ≤ (rf : ℝ) / 2 := by
    exact_mod_cast roundToMultiple_bound rf hrf_pos T.b
  have h_dist_eq : dist T T' =
      dyadicDelta n * ((|(T.a - T'.a : ℤ)| : ℝ) + (|(T.b - T'.b : ℤ)| : ℝ)) := by
    exact DyadicTube.dist_eq T T'
  rw [h_dist_eq]
  have h5 : dyadicDelta n * (rf : ℝ) = dyadicDelta m :=
    dyadicDelta_mul_refinement n m hnm
  have h6 : ((|(T.a - T'.a : ℤ)| : ℝ) + (|(T.b - T'.b : ℤ)| : ℝ)) ≤ (rf : ℝ) := by
    have h7 : (|(T.a - T'.a : ℤ)| : ℝ) ≤ (rf : ℝ) / 2 := by exact_mod_cast ha
    have h8 : (|(T.b - T'.b : ℤ)| : ℝ) ≤ (rf : ℝ) / 2 := by exact_mod_cast hb
    linarith
  have h9 : 0 ≤ dyadicDelta n := (dyadicDelta_pos n).le
  have h10 : dyadicDelta n * (((|(T.a - T'.a : ℤ)| : ℝ) + (|(T.b - T'.b : ℤ)| : ℝ))) ≤
      dyadicDelta n * (rf : ℝ) := by
    gcongr
  rw [h5] at h10
  exact h10

/-- Equality of DyadicTubes from field equalities. -/
lemma DyadicTube.eq_iff {n : ℕ} {T₁ T₂ : DyadicTube n} :
    T₁ = T₂ ↔ T₁.a = T₂.a ∧ T₁.b = T₂.b := by
  constructor
  · intro h
    rw [h]
    <;> exact ⟨rfl, rfl⟩
  · rintro ⟨ha, hb⟩
    cases T₁ <;> cases T₂ <;> simp_all

/-- Coarse rounding is idempotent. -/
lemma coarseRound_idempotent (n m : ℕ) (hnm : m ≤ n) (T : DyadicTube n) :
    coarseRound n m hnm (coarseRound n m hnm T) = coarseRound n m hnm T := by
  let rf := refinementFactor n m
  have hrf_pos : 0 < rf := refinementFactor_pos n m
  let T' := coarseRound n m hnm T
  have hT'a : T'.a = roundToMultiple rf T.a := by rfl
  have hT'b : T'.b = roundToMultiple rf T.b := by rfl
  have ha : roundToMultiple rf T'.a = T'.a := by
    rw [hT'a]
    exact roundToMultiple_idempotent rf hrf_pos T.a
  have hb : roundToMultiple rf T'.b = T'.b := by
    rw [hT'b]
    exact roundToMultiple_idempotent rf hrf_pos T.b
  have h1 : (coarseRound n m hnm T').a = T'.a := ha
  have h2 : (coarseRound n m hnm T').b = T'.b := hb
  exact (DyadicTube.eq_iff.mpr ⟨h1, h2⟩)

/-- Distinct coarse roundings are separated by scale m. -/
lemma coarseRound_separated (n m : ℕ) (hnm : m ≤ n)
    {T₁ T₂ : DyadicTube n}
    (h : coarseRound n m hnm T₁ ≠ coarseRound n m hnm T₂) :
    dyadicDelta m ≤ dist (coarseRound n m hnm T₁) (coarseRound n m hnm T₂) := by
  let rf := refinementFactor n m
  let U₁ := coarseRound n m hnm T₁
  let U₂ := coarseRound n m hnm T₂
  have h_mult_a1 : (rf : ℤ) ∣ U₁.a := roundToMultiple_is_multiple rf T₁.a
  have h_mult_b1 : (rf : ℤ) ∣ U₁.b := roundToMultiple_is_multiple rf T₁.b
  have h_mult_a2 : (rf : ℤ) ∣ U₂.a := roundToMultiple_is_multiple rf T₂.a
  have h_mult_b2 : (rf : ℤ) ∣ U₂.b := roundToMultiple_is_multiple rf T₂.b
  have hne : U₁.a ≠ U₂.a ∨ U₁.b ≠ U₂.b := by
    by_contra! h2
    have h3 : U₁.a = U₂.a := h2.1
    have h4 : U₁.b = U₂.b := h2.2
    have h5 : U₁ = U₂ := DyadicTube.eq_iff.mpr ⟨h3, h4⟩
    exact h h5
  have h_sum_ge : (rf : ℝ) ≤ (|(U₁.a - U₂.a : ℤ)| : ℝ) + (|(U₁.b - U₂.b : ℤ)| : ℝ) := by
    rcases hne with (hne | hne)
    · -- U₁.a ≠ U₂.a
      have hdiff : U₁.a - U₂.a ≠ 0 := by omega
      have hdiv : (rf : ℤ) ∣ (U₁.a - U₂.a) := dvd_sub h_mult_a1 h_mult_a2
      have hrf_pos' : 0 < (rf : ℤ) := by exact_mod_cast refinementFactor_pos n m
      have h_abs_ge : (rf : ℝ) ≤ (|(U₁.a - U₂.a : ℤ)| : ℝ) :=
        abs_ge_of_dvd hrf_pos' hdiv hdiff
      have h_abs_b_nonneg : (0 : ℝ) ≤ (|(U₁.b - U₂.b : ℤ)| : ℝ) := by exact_mod_cast abs_nonneg _
      linarith
    · -- U₁.b ≠ U₂.b
      have hdiff : U₁.b - U₂.b ≠ 0 := by omega
      have hdiv : (rf : ℤ) ∣ (U₁.b - U₂.b) := dvd_sub h_mult_b1 h_mult_b2
      have hrf_pos' : 0 < (rf : ℤ) := by exact_mod_cast refinementFactor_pos n m
      have h_abs_ge : (rf : ℝ) ≤ (|(U₁.b - U₂.b : ℤ)| : ℝ) :=
        abs_ge_of_dvd hrf_pos' hdiv hdiff
      have h_abs_a_nonneg : (0 : ℝ) ≤ (|(U₁.a - U₂.a : ℤ)| : ℝ) := by exact_mod_cast abs_nonneg _
      linarith
  have h_dist_eq : dist U₁ U₂ =
      dyadicDelta n * ((|(U₁.a - U₂.a : ℤ)| : ℝ) + (|(U₁.b - U₂.b : ℤ)| : ℝ)) := by
    exact DyadicTube.dist_eq U₁ U₂
  rw [h_dist_eq]
  have h5 : dyadicDelta n * (rf : ℝ) = dyadicDelta m :=
    dyadicDelta_mul_refinement n m hnm
  have h9 : 0 ≤ dyadicDelta n := (dyadicDelta_pos n).le
  have h10 : dyadicDelta n * (rf : ℝ) ≤
      dyadicDelta n * ((|(U₁.a - U₂.a : ℤ)| : ℝ) + (|(U₁.b - U₂.b : ℤ)| : ℝ)) := by
    gcongr
    <;> linarith
  rw [h5] at h10
  exact h10

/-- The coarse range of a finite set of tubes. -/
def coarseRange (n m : ℕ) (hnm : m ≤ n) (U : Finset (DyadicTube n)) :
    Finset (DyadicTube n) :=
  U.image (coarseRound n m hnm)

/-- Every coarse rounding lands in the coarse range. -/
lemma coarseRange_mem (n m : ℕ) (hnm : m ≤ n) (U : Finset (DyadicTube n))
    {T : DyadicTube n} (hT : T ∈ U) :
    coarseRound n m hnm T ∈ coarseRange n m hnm U := by
  exact Finset.mem_image.mpr ⟨T, hT, rfl⟩

/-- The coarse range is separated at scale m. -/
lemma coarseRange_separated (n m : ℕ) (hnm : m ≤ n) (U : Finset (DyadicTube n)) :
    SeparatedAt (dyadicDelta m) (coarseRange n m hnm U : Set (DyadicTube n)) := by
  dsimp only [SeparatedAt]
  intro T₁ hT₁ T₂ hT₂ hne
  rcases Finset.mem_image.mp hT₁ with ⟨S₁, hS₁, rfl⟩
  rcases Finset.mem_image.mp hT₂ with ⟨S₂, hS₂, rfl⟩
  exact coarseRound_separated n m hnm hne

/-- Helper: if d > 0, x ≥ 0, and x * d ≤ N, then x ≤ N / d. -/
lemma Int.le_ediv_of_mul_le' {d N x : ℤ} (hd_pos : 0 < d) (hx_nonneg : 0 ≤ x)
    (h : x * d ≤ N) : x ≤ N / d := by
  by_contra h2
  have h3 : N / d + 1 ≤ x := by linarith
  have h4 : (N / d + 1) * d ≤ N := by
    calc (N / d + 1) * d ≤ x * d := by gcongr
      _ ≤ N := h
  have h5 : N < (N / d + 1) * d := by
    have h6 : N = (N / d) * d + N % d := by exact Eq.symm (Int.ediv_mul_add_emod N d)
    have h7 : 0 ≤ N % d := Int.emod_nonneg N hd_pos.ne'
    have h8 : N % d < d := Int.emod_lt_of_pos N hd_pos
    linarith
  linarith

/-- Cardinality bound for the coarse range.

    If all tubes in `U` satisfy `|T.a| ≤ A` and `|T.b| ≤ B`, then
    `coarseRange.card ≤ (2*A/rf + 3) * (2*B/rf + 3)` where `rf = refinementFactor n m`.

    This follows because coarse indices are multiples of `rf` in a bounded box. -/
lemma coarseRange_card_bound {n m : ℕ} (hnm : m ≤ n) {U : Finset (DyadicTube n)}
    {A B : ℕ} (hA : ∀ T ∈ U, |T.a| ≤ (A : ℤ)) (hB : ∀ T ∈ U, |T.b| ≤ (B : ℤ)) :
    (coarseRange n m hnm U).card ≤
      (2 * (A / refinementFactor n m) + 3) * (2 * (B / refinementFactor n m) + 3) := by
  let rf := refinementFactor n m
  have hrf_pos : 0 < rf := refinementFactor_pos n m
  have hrf_pos' : 0 < (rf : ℤ) := by exact_mod_cast hrf_pos
  let kMaxA : ℕ := (A + rf) / rf
  let kMaxB : ℕ := (B + rf) / rf
  let indicesA : Finset ℤ := Finset.Icc (-(kMaxA : ℤ)) (kMaxA : ℤ)
  let indicesB : Finset ℤ := Finset.Icc (-(kMaxB : ℤ)) (kMaxB : ℤ)
  let g : ℤ × ℤ → DyadicTube n := fun p => ⟨p.1 * (rf : ℤ), p.2 * (rf : ℤ)⟩
  let possibleTubes : Finset (DyadicTube n) := (indicesA ×ˢ indicesB).image g
  have h_kMaxA_eq : kMaxA = A / rf + 1 := by
    dsimp only [kMaxA]
    have h : (A + rf) / rf = A / rf + 1 := by
      have h' : (A + rf * 1) / rf = A / rf + 1 := by exact Nat.add_mul_div_left A 1 hrf_pos
      simpa using h'
    exact h
  have h_kMaxB_eq : kMaxB = B / rf + 1 := by
    dsimp only [kMaxB]
    have h : (B + rf) / rf = B / rf + 1 := by
      have h' : (B + rf * 1) / rf = B / rf + 1 := by exact Nat.add_mul_div_left B 1 hrf_pos
      simpa using h'
    exact h
  have h_subset : coarseRange n m hnm U ⊆ possibleTubes := by
    intro T' hT'
    rcases Finset.mem_image.mp hT' with ⟨T, hT, rfl⟩
    let U1 := coarseRound n m hnm T
    have h_mult_a : (rf : ℤ) ∣ U1.a := roundToMultiple_is_multiple rf T.a
    have h_mult_b : (rf : ℤ) ∣ U1.b := roundToMultiple_is_multiple rf T.b
    rcases h_mult_a with ⟨ka, hka⟩
    rcases h_mult_b with ⟨kb, hkb⟩
    have hU1a : U1.a = ka * (rf : ℤ) := by linarith
    have hU1b : U1.b = kb * (rf : ℤ) := by linarith
    have h_bound_a1 : |(U1.a : ℝ)| ≤ (A : ℝ) + (rf : ℝ) := by
      have h11 : |(U1.a - T.a : ℤ)| ≤ (rf : ℝ) / 2 := by
        have h12 := roundToMultiple_bound rf hrf_pos T.a
        have h13 : |(U1.a - T.a : ℤ)| = |(T.a - U1.a : ℤ)| := by
          rw [show U1.a - T.a = -(T.a - U1.a) from by ring, abs_neg]
        rw [h13]; exact h12
      have h1 : |(U1.a : ℝ) - (T.a : ℝ)| ≤ (rf : ℝ) / 2 := by exact_mod_cast h11
      have h2 : |(U1.a : ℝ)| ≤ |(T.a : ℝ)| + |(U1.a : ℝ) - (T.a : ℝ)| := by
        have h21 : (U1.a : ℝ) = (T.a : ℝ) + ((U1.a : ℝ) - (T.a : ℝ)) := by ring
        have h22 : |(U1.a : ℝ)| = |(T.a : ℝ) + ((U1.a : ℝ) - (T.a : ℝ))| := by
          exact congr_arg (fun x : ℝ => |x|) h21
        rw [h22]
        exact abs_add_le (T.a : ℝ) ((U1.a : ℝ) - (T.a : ℝ))
      have h3 : |(T.a : ℝ)| ≤ (A : ℝ) := by exact_mod_cast hA T hT
      linarith
    have h_bound_b1 : |(U1.b : ℝ)| ≤ (B : ℝ) + (rf : ℝ) := by
      have h11 : |(U1.b - T.b : ℤ)| ≤ (rf : ℝ) / 2 := by
        have h12 := roundToMultiple_bound rf hrf_pos T.b
        have h13 : |(U1.b - T.b : ℤ)| = |(T.b - U1.b : ℤ)| := by
          rw [show U1.b - T.b = -(T.b - U1.b) from by ring, abs_neg]
        rw [h13]; exact h12
      have h1 : |(U1.b : ℝ) - (T.b : ℝ)| ≤ (rf : ℝ) / 2 := by exact_mod_cast h11
      have h2 : |(U1.b : ℝ)| ≤ |(T.b : ℝ)| + |(U1.b : ℝ) - (T.b : ℝ)| := by
        have h21 : (U1.b : ℝ) = (T.b : ℝ) + ((U1.b : ℝ) - (T.b : ℝ)) := by ring
        have h22 : |(U1.b : ℝ)| = |(T.b : ℝ) + ((U1.b : ℝ) - (T.b : ℝ))| := by
          exact congr_arg (fun x : ℝ => |x|) h21
        rw [h22]
        exact abs_add_le (T.b : ℝ) ((U1.b : ℝ) - (T.b : ℝ))
      have h3 : |(T.b : ℝ)| ≤ (B : ℝ) := by exact_mod_cast hB T hT
      linarith
    have h4a : |U1.a| ≤ (A : ℤ) + (rf : ℤ) := by exact_mod_cast h_bound_a1
    have h5a : |U1.a| = |ka| * (rf : ℤ) := by
      rw [hU1a]
      have h6 : |ka * (rf : ℤ)| = |ka| * |(rf : ℤ)| := abs_mul _ _
      rw [h6]
      have h7 : |(rf : ℤ)| = (rf : ℤ) := abs_of_pos hrf_pos'
      rw [h7]
    have h_ka_nonneg : 0 ≤ |ka| := abs_nonneg ka
    have h_ka_mul : |ka| * (rf : ℤ) ≤ (A : ℤ) + (rf : ℤ) := by
      rw [←h5a]; exact h4a
    have h_ka_bound : |ka| ≤ ((A : ℤ) + (rf : ℤ)) / (rf : ℤ) :=
      Int.le_ediv_of_mul_le' hrf_pos' h_ka_nonneg h_ka_mul
    have h4b : |U1.b| ≤ (B : ℤ) + (rf : ℤ) := by exact_mod_cast h_bound_b1
    have h5b : |U1.b| = |kb| * (rf : ℤ) := by
      rw [hU1b]
      have h6 : |kb * (rf : ℤ)| = |kb| * |(rf : ℤ)| := abs_mul _ _
      rw [h6]
      have h7 : |(rf : ℤ)| = (rf : ℤ) := abs_of_pos hrf_pos'
      rw [h7]
    have h_kb_nonneg : 0 ≤ |kb| := abs_nonneg kb
    have h_kb_mul : |kb| * (rf : ℤ) ≤ (B : ℤ) + (rf : ℤ) := by
      rw [←h5b]; exact h4b
    have h_kb_bound : |kb| ≤ ((B : ℤ) + (rf : ℤ)) / (rf : ℤ) :=
      Int.le_ediv_of_mul_le' hrf_pos' h_kb_nonneg h_kb_mul
    have h_ka_bound2 : |ka| ≤ (kMaxA : ℤ) := by
      simpa [kMaxA] using h_ka_bound
    have h_kb_bound2 : |kb| ≤ (kMaxB : ℤ) := by
      simpa [kMaxB] using h_kb_bound
    have h_ka_in : ka ∈ indicesA := by
      simp only [indicesA, Finset.mem_Icc]
      exact abs_le.mp h_ka_bound2
    have h_kb_in : kb ∈ indicesB := by
      simp only [indicesB, Finset.mem_Icc]
      exact abs_le.mp h_kb_bound2
    have h_main : U1 = g (ka, kb) := by
      exact DyadicTube.eq_iff.mpr ⟨hU1a, hU1b⟩
    have h_goal : coarseRound n m hnm T ∈ possibleTubes := by
      have h_eq : coarseRound n m hnm T = U1 := by rfl
      rw [h_eq, h_main]
      exact Finset.mem_image.mpr ⟨(ka, kb), Finset.mem_product.mpr ⟨h_ka_in, h_kb_in⟩, rfl⟩
    exact h_goal
  have h_card : possibleTubes.card ≤ indicesA.card * indicesB.card := by
    calc
      possibleTubes.card
        ≤ (indicesA ×ˢ indicesB).card := Finset.card_image_le
      _ = indicesA.card * indicesB.card := by simp
  calc
    (coarseRange n m hnm U).card
      ≤ possibleTubes.card := Finset.card_le_card h_subset
    _ ≤ indicesA.card * indicesB.card := h_card
    _ = (2 * kMaxA + 1) * (2 * kMaxB + 1) := by
      have hca : indicesA.card = 2 * kMaxA + 1 := by
        simp [indicesA] <;> norm_cast <;> omega
      have hcb : indicesB.card = 2 * kMaxB + 1 := by
        simp [indicesB] <;> norm_cast <;> omega
      rw [hca, hcb] <;> ring
    _ = (2 * (A / rf) + 3) * (2 * (B / rf) + 3) := by
      rw [h_kMaxA_eq, h_kMaxB_eq] <;> ring

/-!
  # Step 7: Multiplicative inequality chaining

  Given counting bounds from Steps 4-6, chain them to prove the final
  multiplicative inequality (v) of induction_core.

  This is a generic transitivity lemma. The exact instantiation will be
  filled in once Steps 2-6 are complete.
-/

/-- Generic multiplicative chaining: if
    `coarse_total * fine_total ≤ K * n_total` and
    `M ≤ M_Δ * M_Q`,
    then `n_total * M_Δ * M_Q ≥ (1/K) * coarse_total * fine_total * M`. -/
lemma multiplicative_chain (K M M_Δ M_Q : ℕ)
    (hK_pos : 0 < K)
    (n_total coarse_total fine_total : ℕ)
    (h1 : (coarse_total : ℝ) * (fine_total : ℝ) ≤ (K : ℝ) * (n_total : ℝ))
    (hM : (M : ℝ) ≤ (M_Δ : ℝ) * (M_Q : ℝ)) :
    (n_total : ℝ) * (M_Δ : ℝ) * (M_Q : ℝ) ≥
      (1 / (K : ℝ)) * (coarse_total : ℝ) * (fine_total : ℝ) * (M : ℝ) := by
  have hK_pos' : 0 < (K : ℝ) := by exact_mod_cast hK_pos
  calc
    (1 / (K : ℝ)) * (coarse_total : ℝ) * (fine_total : ℝ) * (M : ℝ)
      = (1 / (K : ℝ)) * ((coarse_total : ℝ) * (fine_total : ℝ)) * (M : ℝ) := by ring
    _ ≤ (1 / (K : ℝ)) * ((K : ℝ) * (n_total : ℝ)) * (M : ℝ) := by
        gcongr
        <;> linarith
    _ = (n_total : ℝ) * (M : ℝ) := by
        field_simp [hK_pos'.ne'] <;> ring
    _ ≤ (n_total : ℝ) * ((M_Δ : ℝ) * (M_Q : ℝ)) := by
        gcongr
        <;> linarith
    _ = (n_total : ℝ) * (M_Δ : ℝ) * (M_Q : ℝ) := by ring

end DirecretisedFurstenbergEstimate.InductionOnScales
