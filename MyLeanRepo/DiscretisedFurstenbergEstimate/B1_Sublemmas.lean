module

/-
  B1 sub-lemmas for the source-faithful induction on scales (OS Proposition 5.1).

  Contains:
  1. Packet thinning: one representative per slope packet
  2. RatioEstimate helper: double-counting inequality
  3. Tube closeness and coarse rounding lemmas
  4. L1 packing bound for DyadicTube
  5. IsFiniteDeltaSSet ↔ IsDeltaSSet conversion bridge
  6. Pigeonhole lemmas: exists_good_square, dyadic_pigeonhole_sizes
  7. Tube retention from QTTC K_val bound
  8. Polylog absorption: K_val ≤ (n-m+1)^100
  9. C₂ constant absorption
  10. IsFiniteDeltaSSet.subset monotonicity
  11. uniformize_cardinalities: dyadic band uniformization + trimming

  Whiteprint node: induction_on_scales
  Dependencies: InductionCounting, InductionConfigurations, DyadicTubes, InductionSteps
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.BallGrowth
public import MyLeanRepo.DiscretisedFurstenbergEstimate.InductionCounting
public import MyLeanRepo.DiscretisedFurstenbergEstimate.InductionConfigurations
public import MyLeanRepo.DiscretisedFurstenbergEstimate.InductionSteps
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

-- InductionSteps uses "Direcretised" typo namespace
open DirecretisedFurstenbergEstimate.InductionOnScales

namespace DiscretisedFurstenbergEstimate.InductionOnScales

open DiscretisedFurstenbergEstimate
-- Do NOT open InductionConfigurations to avoid refinementFactor ambiguity with InductionSteps
-- Explicitly qualify squareContained and containingSquare from InductionConfigurations
open DiscretisedFurstenbergEstimate.InductionOnScales.Counting

/-! ============================================================================
   0. Local definitions
   ============================================================================ -/

/-- Slope packet index: T.a / 2^m. Packets have width δ/Δ = 2^{-(n-m)}. -/
def slopePacketIdx {n m : ℕ} (hnm : m ≤ n) (T : DyadicTube n) : ℤ :=
  T.a / (2 ^ m)

/-! ============================================================================
   1. Packet thinning: one representative per slope packet
   ============================================================================ -/

/-- Given a finset of fine tubes, partition by slope packet index and
    select one representative tube per packet at scale n-m.

    The representative has intercept 0 for simplicity; the actual intercept
    should be chosen based on the fine config construction in the main proof.
-/
lemma packet_thinning
    {n m : ℕ} (hnm : m ≤ n)
    (T_fine : Finset (DyadicTube n)) :
    ∃ (reps : Finset (DyadicTube (n - m)))
      (repOf : DyadicTube n → DyadicTube (n - m)),
      (∀ T ∈ T_fine, (repOf T).a = slopePacketIdx hnm T) ∧
      (∀ T1 ∈ T_fine, ∀ T2 ∈ T_fine,
        slopePacketIdx hnm T1 = slopePacketIdx hnm T2 → repOf T1 = repOf T2) ∧
      (∀ T ∈ T_fine, repOf T ∈ reps) := by
  let idxSet : Finset ℤ := T_fine.image (slopePacketIdx hnm)
  let repOf (T : DyadicTube n) : DyadicTube (n - m) :=
    ⟨slopePacketIdx hnm T, 0⟩
  let reps : Finset (DyadicTube (n - m)) :=
    idxSet.image (fun idx => ⟨idx, 0⟩)
  refine' ⟨reps, repOf, _⟩
  constructor
  · intro T hT; rfl
  constructor
  · intro T1 _ T2 _ h_eq
    simp [repOf, h_eq]
  · intro T hT
    let idx := slopePacketIdx hnm T
    have hidx : idx ∈ idxSet := Finset.mem_image.mpr ⟨T, hT, rfl⟩
    have h_idx_eq : idx = slopePacketIdx hnm T := by rfl
    have h_goal : repOf T ∈ reps := by
      apply Finset.mem_image.mpr
      exact ⟨idx, hidx, by simp [repOf, h_idx_eq]⟩
    exact h_goal

/-- Distinct packet representatives have slopes separated by at least δ/Δ.
    This is the slope-cell separation property needed for the fine config. -/
lemma packet_reps_slope_separated
    {n m : ℕ} (hnm : m ≤ n)
    (reps : Finset (DyadicTube (n - m)))
    (h_inj : ∀ r1 ∈ reps, ∀ r2 ∈ reps, r1 ≠ r2 → r1.a ≠ r2.a) :
    ∀ r1 ∈ reps, ∀ r2 ∈ reps, r1 ≠ r2 →
      |r1.slope - r2.slope| ≥ dyadicDelta (n - m) := by
  intro r1 hr1 r2 hr2 hne
  have ha : r1.a ≠ r2.a := h_inj r1 hr1 r2 hr2 hne
  have h1 : |(r1.a : ℝ) - (r2.a : ℝ)| ≥ 1 := by
    have h1' : r1.a - r2.a ≠ 0 := by
      intro h
      have h5 : r1.a = r2.a := by linarith
      exact ha h5
    have h2 : |r1.a - r2.a| ≥ 1 := by
      exact Int.one_le_abs h1'
    exact_mod_cast h2
  have hpos : 0 < dyadicDelta (n - m) := dyadicDelta_pos (n - m)
  have h2 : r1.slope - r2.slope = ((r1.a : ℝ) - (r2.a : ℝ)) * dyadicDelta (n - m) := by
    simp [DyadicTube.slope] <;> ring
  rw [h2]
  have h3 : |((r1.a : ℝ) - (r2.a : ℝ)) * dyadicDelta (n - m)| =
      |(r1.a : ℝ) - (r2.a : ℝ)| * dyadicDelta (n - m) := by
    rw [abs_mul, abs_of_pos hpos]
  rw [h3]
  have h4 : 0 ≤ dyadicDelta (n - m) := hpos.le
  nlinarith

/-! ============================================================================
   2. RatioEstimate helper via double counting
   ============================================================================ -/

/-- Multiplicative ratio estimate from packet decomposition.

    Given children partition and disjoint packets contained in selected children,
    concludes:
    |T₀| * M_Δ * M_Q ≥ (1/L) * |coarseT₀| * |fineT₀| * M
-/
lemma ratio_estimate_from_packets
    {n m : ℕ} (hnm : m ≤ n)
    {s C₁ : ℝ} {M M_Δ M_Q N_Δ : ℕ}
    (config : CombiningTheorem.NiceConfiguration n s C₁ M)
    (coarseT₀ : Finset (DyadicTube m))
    (selectedCoarse : Finset (DyadicTube m))
    (fineT₀ : Finset (DyadicTube (n - m)))
    (L : ℝ)
    (hL : 2 ≤ L)
    (hMpos : 0 < M)
    (hMΔpos : 0 < M_Δ)
    (hMQpos : 0 < M_Q)
    (children : DyadicTube m → Finset (DyadicTube n))
    (h_children_sub : ∀ T ∈ coarseT₀, children T ⊆ config.T₀)
    (h_disj : ∀ T1 ∈ coarseT₀, ∀ T2 ∈ coarseT₀, T1 ≠ T2 → Disjoint (children T1) (children T2))
    (h_N_lower : ∀ T ∈ coarseT₀, (children T).card ≥ N_Δ)
    (h_N_upper : ∀ T ∈ selectedCoarse, (children T).card ≤ 2 * N_Δ)
    (h_selected_sub : selectedCoarse ⊆ coarseT₀)
    (h_selected_card : selectedCoarse.card = M_Δ)
    (packet : DyadicTube (n - m) → Finset (DyadicTube n))
    (h_packet_size : ∀ ξ ∈ fineT₀, ((packet ξ).card : ℝ) ≥ 2 * (M : ℝ) / (L * (M_Q : ℝ)))
    (h_packet_disj : ∀ ξ1 ∈ fineT₀, ∀ ξ2 ∈ fineT₀, ξ1 ≠ ξ2 → Disjoint (packet ξ1) (packet ξ2))
    (h_packets_in_children : (fineT₀.biUnion packet) ⊆ (selectedCoarse.biUnion children))
    (h_fineT_card : fineT₀.card = M_Q) :
    (↑(config.T₀.card) : ENNReal) * (↑M_Δ : ENNReal) * (↑M_Q : ENNReal) ≥
      ENNReal.ofReal (1 / L) * (↑(coarseT₀.card) : ENNReal) *
      (↑(fineT₀.card) : ENNReal) * (↑M : ENNReal) := by
  let m_packet : ℝ := 2 * (M : ℝ) / (L * (M_Q : ℝ))
  have hm_nonneg : 0 ≤ m_packet := by positivity
  have h_main : (config.T₀.card : ℝ) * (M_Δ : ℝ) ≥
      (coarseT₀.card : ℝ) * (fineT₀.card : ℝ) * m_packet / 2 :=
    induction_lower_bound_real config.T₀ coarseT₀ children N_Δ M_Δ selectedCoarse fineT₀ packet m_packet
      hMΔpos hm_nonneg h_children_sub h_disj h_N_lower h_N_upper h_selected_sub h_selected_card
      h_packet_size h_packet_disj h_packets_in_children
  have hL_pos : 0 < L := by linarith
  have hMQ_ne_zero : (M_Q : ℝ) ≠ 0 := by positivity
  have h_real : (config.T₀.card : ℝ) * (M_Δ : ℝ) ≥
      (1 / L) * (coarseT₀.card : ℝ) * (M : ℝ) := by
    calc (config.T₀.card : ℝ) * (M_Δ : ℝ)
      ≥ (coarseT₀.card : ℝ) * (fineT₀.card : ℝ) * m_packet / 2 := h_main
    _ = (coarseT₀.card : ℝ) * (fineT₀.card : ℝ) *
          (2 * (M : ℝ) / (L * (M_Q : ℝ))) / 2 := by rfl
    _ = (coarseT₀.card : ℝ) * (M_Q : ℝ) *
          (2 * (M : ℝ) / (L * (M_Q : ℝ))) / 2 := by
      have h_eq : (fineT₀.card : ℝ) = (M_Q : ℝ) := by exact_mod_cast h_fineT_card
      rw [h_eq]
    _ = (1 / L) * (coarseT₀.card : ℝ) * (M : ℝ) := by
      field_simp [hL_pos.ne', hMQ_ne_zero] <;> ring
  have h1' : (config.T₀.card : ℝ) * (M_Δ : ℝ) * (M_Q : ℝ) ≥
      (1 / L) * (coarseT₀.card : ℝ) * (M : ℝ) * (M_Q : ℝ) := by
    have hMQ_nonneg : (M_Q : ℝ) ≥ 0 := by positivity
    gcongr
  have h2 : (↑(config.T₀.card) : ENNReal) * (↑M_Δ : ENNReal) * (↑M_Q : ENNReal) ≥
      ENNReal.ofReal ((1 / L) * (coarseT₀.card : ℝ) * (M : ℝ) * (M_Q : ℝ)) := by
    exact_mod_cast h1'
  have h_nonneg1 : 0 ≤ (1 / L) := by positivity
  have h_nonneg2 : 0 ≤ (coarseT₀.card : ℝ) := by positivity
  have h_nonneg3 : 0 ≤ (M : ℝ) := by linarith
  have h_nonneg4 : 0 ≤ (M_Q : ℝ) := by positivity
  have h_prod : (1 / L) * (coarseT₀.card : ℝ) * (M : ℝ) * (M_Q : ℝ) =
      (1 / L) * ((coarseT₀.card : ℝ) * (M_Q : ℝ) * (M : ℝ)) := by ring
  rw [h_prod] at h2
  have h3 : ENNReal.ofReal ((1 / L) * ((coarseT₀.card : ℝ) * (M_Q : ℝ) * (M : ℝ))) =
      ENNReal.ofReal (1 / L) * ((↑(coarseT₀.card) : ENNReal) * (↑M_Q : ENNReal) * (↑M : ENNReal)) := by
    rw [ENNReal.ofReal_mul h_nonneg1, ENNReal.ofReal_mul (mul_nonneg h_nonneg2 h_nonneg4),
      ENNReal.ofReal_mul h_nonneg2] <;> simp <;> ring
  rw [h3] at h2
  have h4 : ENNReal.ofReal (1 / L) * ((↑(coarseT₀.card) : ENNReal) * (↑M_Q : ENNReal) * (↑M : ENNReal)) =
      ENNReal.ofReal (1 / L) * (↑(coarseT₀.card) : ENNReal) * (↑M_Q : ENNReal) * (↑M : ENNReal) := by
    ring
  rw [h4] at h2
  have h5 : (↑(fineT₀.card) : ENNReal) = (↑M_Q : ENNReal) := by exact_mod_cast h_fineT_card
  rw [h5]
  exact h2

/-! ============================================================================
   3. Tube closeness and coarse rounding lemmas
   ============================================================================ -/

/-- Fine tube is within Δ of its coarse rounding in parameter space. -/
lemma fine_tube_close_to_coarse
    {n m : ℕ} (hnm : m ≤ n) (T : DyadicTube n) :
    DyadicTube.dist T (coarseRound n m hnm T) ≤ dyadicDelta m :=
  coarseRound_dist n m hnm T

/-- The coarse rounding has indices divisible by refinementFactor. -/
lemma coarse_rounding_divisible
    {n m : ℕ} (hnm : m ≤ n) (T : DyadicTube n) :
    (refinementFactor n m : ℤ) ∣ (coarseRound n m hnm T).a ∧
    (refinementFactor n m : ℤ) ∣ (coarseRound n m hnm T).b := by
  let rf := refinementFactor n m
  exact ⟨roundToMultiple_is_multiple rf T.a, roundToMultiple_is_multiple rf T.b⟩

/-- Convert a coarse-rounded DyadicTube n to a DyadicTube m. -/
def coarseRoundToM {n m : ℕ} (hnm : m ≤ n) (T : DyadicTube n)
    (h : (refinementFactor n m : ℤ) ∣ T.a ∧ (refinementFactor n m : ℤ) ∣ T.b) :
    DyadicTube m :=
  ⟨T.a / (refinementFactor n m : ℤ), T.b / (refinementFactor n m : ℤ)⟩

/-- The converted tube has the same slope and intercept as the original. -/
lemma coarseRoundToM_eq
    {n m : ℕ} (hnm : m ≤ n) (T : DyadicTube n)
    (h : (refinementFactor n m : ℤ) ∣ T.a ∧ (refinementFactor n m : ℤ) ∣ T.b) :
    (coarseRoundToM hnm T h).slope = T.slope ∧
    (coarseRoundToM hnm T h).intercept = T.intercept := by
  let rf : ℕ := refinementFactor n m
  have hrf_pos : 0 < rf := by
    dsimp only [rf, refinementFactor] <;> positivity
  have hdiv_a : (rf : ℤ) ∣ T.a := h.1
  have hdiv_b : (rf : ℤ) ∣ T.b := h.2
  let qa : ℤ := T.a / (rf : ℤ)
  let qb : ℤ := T.b / (rf : ℤ)
  have hqa_def : qa = T.a / (rf : ℤ) := by rfl
  have hqb_def : qb = T.b / (rf : ℤ) := by rfl
  have hrf_eq : (rf : ℝ) = (refinementFactor n m : ℝ) := by rfl
  have ha_int : T.a = qa * (rf : ℤ) := by
    exact (Int.ediv_mul_cancel_of_dvd hdiv_a).symm
  have hb_int : T.b = qb * (rf : ℤ) := by
    exact (Int.ediv_mul_cancel_of_dvd hdiv_b).symm
  have ha_real : (T.a : ℝ) = (qa : ℝ) * (rf : ℝ) := by exact_mod_cast ha_int
  have hb_real : (T.b : ℝ) = (qb : ℝ) * (rf : ℝ) := by exact_mod_cast hb_int
  have h_mul : dyadicDelta n * (rf : ℝ) = dyadicDelta m :=
    dyadicDelta_mul_refinement n m hnm
  have h_slope : (coarseRoundToM hnm T h).slope = T.slope := by
    have hU_a : (coarseRoundToM hnm T h).a = qa := by
      simp [coarseRoundToM, qa, hrf_eq] <;> omega
    have h1 : (coarseRoundToM hnm T h).slope =
        ((coarseRoundToM hnm T h).a : ℝ) * dyadicDelta m := by
      simp [DyadicTube.slope]
    rw [h1, hU_a]
    have h2 : (qa : ℝ) * dyadicDelta m = (qa : ℝ) * (dyadicDelta n * (rf : ℝ)) := by
      rw [h_mul]
    rw [h2]
    have h3 : (qa : ℝ) * (dyadicDelta n * (rf : ℝ)) = (qa : ℝ) * (rf : ℝ) * dyadicDelta n := by ring
    rw [h3]
    have h4 : (qa : ℝ) * (rf : ℝ) = (T.a : ℝ) := Eq.symm ha_real
    rw [h4]
    <;> simp [DyadicTube.slope] <;> ring
  have h_intercept : (coarseRoundToM hnm T h).intercept = T.intercept := by
    have hU_b : (coarseRoundToM hnm T h).b = qb := by
      simp [coarseRoundToM, qb, hrf_eq] <;> omega
    have h1 : (coarseRoundToM hnm T h).intercept =
        ((coarseRoundToM hnm T h).b : ℝ) * dyadicDelta m := by
      simp [DyadicTube.intercept]
    rw [h1, hU_b]
    have h2 : (qb : ℝ) * dyadicDelta m = (qb : ℝ) * (dyadicDelta n * (rf : ℝ)) := by
      rw [h_mul]
    rw [h2]
    have h3 : (qb : ℝ) * (dyadicDelta n * (rf : ℝ)) = (qb : ℝ) * (rf : ℝ) * dyadicDelta n := by ring
    rw [h3]
    have h4 : (qb : ℝ) * (rf : ℝ) = (T.b : ℝ) := Eq.symm hb_real
    rw [h4]
    <;> simp [DyadicTube.intercept] <;> ring
  exact ⟨h_slope, h_intercept⟩

/-- A coarse-rounded tube's strip is contained in its converted-to-m strip,
    because both have the same center line and the m-scale strip is wider. -/
lemma coarse_rounded_strip_containment
    {n m : ℕ} (hnm : m ≤ n) (T : DyadicTube n)
    (h : (refinementFactor n m : ℤ) ∣ T.a ∧ (refinementFactor n m : ℤ) ∣ T.b) :
    T.toSet ⊆ (coarseRoundToM hnm T h).toSet := by
  have h_eq : (coarseRoundToM hnm T h).slope = T.slope :=
    (coarseRoundToM_eq hnm T h).1
  have h_eq2 : (coarseRoundToM hnm T h).intercept = T.intercept :=
    (coarseRoundToM_eq hnm T h).2
  have hδ_le : dyadicDelta n ≤ dyadicDelta m := by
    have h1 : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnm
    have h2 : (2 : ℝ)^(-(n : ℝ)) ≤ (2 : ℝ)^(-(m : ℝ)) := by gcongr <;> linarith
    simpa [dyadicDelta] using h2
  intro p hp
  have h4 : |p 1 - T.slope * p 0 - T.intercept| ≤ dyadicDelta n := hp
  have h5 : |p 1 - (coarseRoundToM hnm T h).slope * p 0 -
      (coarseRoundToM hnm T h).intercept| ≤ dyadicDelta m := by
    rw [h_eq, h_eq2]
    exact le_trans h4 hδ_le
  exact h5

/-! ============================================================================
   4. Parameter-space closeness containment

   FULL UnionContainment with infinite toSet is FALSE: strips with different
   slopes diverge as x → ∞. The correct statement is parameter-space closeness,
   which is what QTTC actually provides and downstream arguments need.
   ============================================================================ -/

/-- Parameter-space closeness: every fine tube is within Δ of some coarse tube. -/
def ParameterClosenessContainment {n m : ℕ} (hnm : m ≤ n)
    (P : Finset (DyadicSquare n))
    (T_fine : (p : DyadicSquare n) → p ∈ P → Finset (DyadicTube n))
    (Q : DyadicSquare m)
    (T_coarse : Finset (DyadicTube m)) : Prop :=
  ∀ (p : DyadicSquare n) (hp : p ∈ P) (hsc : InductionConfigurations.squareContained hnm p Q)
    (t : DyadicTube n) (ht : t ∈ T_fine p hp),
    ∃ (U : DyadicTube m), U ∈ T_coarse ∧
      |t.slope - U.slope| + |t.intercept - U.intercept| ≤ dyadicDelta m

/-- If the coarse family contains the converted coarse rounding of every fine
    tube, then ParameterClosenessContainment holds. -/
lemma parameter_closeness_from_rounding
    {n m : ℕ} (hnm : m ≤ n)
    (P : Finset (DyadicSquare n))
    (T_fine : (p : DyadicSquare n) → p ∈ P → Finset (DyadicTube n))
    (Q : DyadicSquare m)
    (T_coarse : Finset (DyadicTube m))
    (h : ∀ (p : DyadicSquare n) (hp : p ∈ P) (t : DyadicTube n)
      (ht : t ∈ T_fine p hp),
      let T' := coarseRound n m hnm t
      let h_mult := coarse_rounding_divisible hnm t
      coarseRoundToM hnm T' h_mult ∈ T_coarse) :
    ParameterClosenessContainment hnm P T_fine Q T_coarse := by
  intro p hp hsc t ht
  let T' := coarseRound n m hnm t
  let h_mult := coarse_rounding_divisible hnm t
  let U := coarseRoundToM hnm T' h_mult
  have hU_in : U ∈ T_coarse := h p hp t ht
  have h_slope_eq : U.slope = T'.slope := (coarseRoundToM_eq hnm T' h_mult).1
  have h_intercept_eq : U.intercept = T'.intercept :=
    (coarseRoundToM_eq hnm T' h_mult).2
  have h_close : |t.slope - U.slope| + |t.intercept - U.intercept| ≤ dyadicDelta m := by
    rw [h_slope_eq, h_intercept_eq]
    exact coarseRound_dist n m hnm t
  exact ⟨U, hU_in, h_close⟩

/-- Parameter closeness using containingSquare instead of squareContained. -/
def ParameterClosenessByContaining {n m : ℕ} (hnm : m ≤ n)
    (P : Finset (DyadicSquare n))
    (T_fine : (p : DyadicSquare n) → p ∈ P → Finset (DyadicTube n))
    (Q : DyadicSquare m)
    (T_coarse : Finset (DyadicTube m)) : Prop :=
  ∀ (p : DyadicSquare n) (hp : p ∈ P) (h_eq : InductionConfigurations.containingSquare hnm p = Q)
    (t : DyadicTube n) (ht : t ∈ T_fine p hp),
    ∃ (U : DyadicTube m), U ∈ T_coarse ∧
      DyadicTube.dist t (coarseRound n m hnm t) ≤ dyadicDelta m

/-- containingSquare p = Q implies squareContained p Q. -/
lemma containingSquare_imp_squareContained {n m : ℕ} (hnm : m ≤ n)
    (p : DyadicSquare n) (Q : DyadicSquare m)
    (h : InductionConfigurations.containingSquare hnm p = Q) : InductionConfigurations.squareContained hnm p Q := by
  let k : ℕ := InductionConfigurations.refinementFactor n m
  have hk_pos : 0 < k := by
    dsimp only [k, InductionConfigurations.refinementFactor] <;> positivity
  let k' : ℤ := ↑k
  have hk'_pos : 0 < k' := Nat.cast_pos.mpr hk_pos
  have hk'_ne : k' ≠ 0 := ne_of_gt hk'_pos
  let Q' := InductionConfigurations.containingSquare hnm p
  have hQ'i : Q'.i = p.i / k' := by rfl
  have hQ'j : Q'.j = p.j / k' := by rfl
  have h1 : (Q'.i : ℤ) * k' ≤ p.i := by
    rw [hQ'i]
    exact Int.ediv_mul_le p.i hk'_ne
  have h2 : p.i < (Q'.i + 1) * k' := by
    rw [hQ'i]
    have h21 : p.i % k' < k' := Int.emod_lt_of_pos p.i hk'_pos
    have h22 : p.i = (p.i / k') * k' + p.i % k' := by
      simp [Int.emod_def] <;> ring
    linarith
  have h3 : (Q'.j : ℤ) * k' ≤ p.j := by
    rw [hQ'j]
    exact Int.ediv_mul_le p.j hk'_ne
  have h4 : p.j < (Q'.j + 1) * k' := by
    rw [hQ'j]
    have h41 : p.j % k' < k' := Int.emod_lt_of_pos p.j hk'_pos
    have h42 : p.j = (p.j / k') * k' + p.j % k' := by
      simp [Int.emod_def] <;> ring
    linarith
  have h1' : InductionConfigurations.squareContained hnm p Q' :=
    ⟨h1, h2, h3, h4⟩
  have hQ' : Q' = Q := h
  rw [hQ'] at h1'
  exact h1'

/-- Parameter closeness from rounding, using containingSquare and DyadicTube.dist. -/
lemma parameter_closeness_qttc_style
    {n m : ℕ} (hnm : m ≤ n)
    (P : Finset (DyadicSquare n))
    (T_fine : (p : DyadicSquare n) → p ∈ P → Finset (DyadicTube n))
    (Q : DyadicSquare m)
    (T_coarse : Finset (DyadicTube m))
    (h : ∀ (p : DyadicSquare n) (hp : p ∈ P) (t : DyadicTube n)
      (ht : t ∈ T_fine p hp),
      let T' := coarseRound n m hnm t
      let h_mult := coarse_rounding_divisible hnm t
      coarseRoundToM hnm T' h_mult ∈ T_coarse) :
    ParameterClosenessByContaining hnm P T_fine Q T_coarse := by
  intro p hp h_eq t ht
  let T' := coarseRound n m hnm t
  let h_mult := coarse_rounding_divisible hnm t
  let U := coarseRoundToM hnm T' h_mult
  have hU_in : U ∈ T_coarse := h p hp t ht
  have h_close : DyadicTube.dist t T' ≤ dyadicDelta m := coarseRound_dist n m hnm t
  exact ⟨U, hU_in, h_close⟩

/-- Direct connection: QTTC output C' contains coarseRound(t) for every selected
    fine tube t. Converting to scale m and using the closeness lemma gives
    parameter closeness for the global coarse family.

    For per-square coarse families, the main B1 proof must ensure that the
    coarse rounding of each tube through p is assigned to containingSquare(p). -/
lemma qttc_coarse_in_family
    {n m : ℕ} (hnm : m ≤ n)
    (P : Finset (DyadicSquare n))
    (T_fine : (p : DyadicSquare n) → p ∈ P → Finset (DyadicTube n))
    (C' : Finset (DyadicTube n))
    (hC'_eq : ∀ (p : DyadicSquare n) (hp : p ∈ P),
      (T_fine p hp).image (coarseRound n m hnm) ⊆ C') :
    ∀ (p : DyadicSquare n) (hp : p ∈ P) (t : DyadicTube n)
      (ht : t ∈ T_fine p hp),
      coarseRound n m hnm t ∈ C' := by
  intro p hp t ht
  have h1 : coarseRound n m hnm t ∈ (T_fine p hp).image (coarseRound n m hnm) :=
    Finset.mem_image.mpr ⟨t, ht, rfl⟩
  exact hC'_eq p hp h1

/- NOTE: The statement "coarseRound(t) intersects containingSquare(p)" is NOT
    always true for arbitrary p near the boundary of Q. The vertical shift can
    be up to Δ+δ, which can push the strip outside Q's y-range.

    Correct approach for B1: assign each coarse tube to a Q based on which
    coarse square it actually intersects, or use the parameter closeness
    (ParameterClosenessContainment) instead of geometric intersection for
    incidence counting. The NiceConfiguration.h_intersect can be satisfied
    by selecting only those coarse tubes that do intersect Q. -/

/-! ### L1 packing bound for DyadicTube parameter space

    The L1 metric on (slope, intercept) is isometric to L∞ on (u,v) where
    u = slope + intercept, v = slope - intercept, via
    |a| + |b| = max(|a+b|, |a-b|).
    Therefore an L1 δ-ball is an L∞ δ-ball after transform, and the
    3×3 thirds partition gives a packing bound of 9. -/

variable {n : ℕ}

/-- Algebraic identity: |a| + |b| = max(|a+b|, |a-b|). -/
lemma abs_add_abs_eq_max (a b : ℝ) : |a| + |b| = max (|a + b|) (|a - b|) := by
  rcases le_total 0 a with (ha | ha) <;> rcases le_total 0 b with (hb | hb)
  · -- a ≥ 0, b ≥ 0
    have h_ab : |a| + |b| = a + b := by
      rw [abs_of_nonneg ha, abs_of_nonneg hb] <;> ring
    have h_sum : |a + b| = a + b := by rw [abs_of_nonneg (by linarith)]
    have h_diff : |a - b| ≤ a + b := by
      have h : |a - b| ≤ |a| + |b| := by exact real_abs_sub a b
      rw [h_ab] at h; exact h
    rw [h_ab, h_sum, max_eq_left h_diff]
  · -- a ≥ 0, b ≤ 0
    have h_ab : |a| + |b| = a - b := by
      rw [abs_of_nonneg ha, abs_of_nonpos hb] <;> ring
    have h_diff : |a - b| = a - b := by
      have h : 0 ≤ a - b := by linarith
      rw [abs_of_nonneg h] <;> ring
    have h_sum : |a + b| ≤ a - b := by
      have h : |a + b| ≤ |a| + |b| := by exact real_abs_add a b
      rw [h_ab] at h; exact h
    rw [h_ab, h_diff, max_eq_right h_sum]
  · -- a ≤ 0, b ≥ 0
    have h_ab : |a| + |b| = -a + b := by
      rw [abs_of_nonpos ha, abs_of_nonneg hb] <;> ring
    have h_diff : |a - b| = -a + b := by
      have h : a - b ≤ 0 := by linarith
      rw [abs_of_nonpos h] <;> ring
    have h_sum : |a + b| ≤ -a + b := by
      have h : |a + b| ≤ |a| + |b| := by exact real_abs_add a b
      rw [h_ab] at h; exact h
    rw [h_ab, h_diff, max_eq_right h_sum]
  · -- a ≤ 0, b ≤ 0
    have h_ab : |a| + |b| = -a - b := by
      rw [abs_of_nonpos ha, abs_of_nonpos hb] <;> ring
    have h_sum : |a + b| = -a - b := by
      have h : a + b ≤ 0 := by linarith
      rw [abs_of_nonpos h] <;> ring
    have h_diff : |a - b| ≤ -a - b := by
      have h : |a - b| ≤ |a| + |b| := by exact real_abs_sub a b
      rw [h_ab] at h; exact h
    rw [h_ab, h_sum, max_eq_left h_diff]

/-- Transform DyadicTube L1 coordinates to L∞ coordinates. -/
def dyadicTubeToLinf (T : DyadicTube n) : ℝ × ℝ :=
  (T.slope + T.intercept, T.slope - T.intercept)

/-- L1 distance equals L∞ distance after the dyadicTubeToLinf transform. -/
lemma dyadicTube_dist_linf (T U : DyadicTube n) :
    dist T U = dist (dyadicTubeToLinf T) (dyadicTubeToLinf U) := by
  have h1 : dist T U = |T.slope - U.slope| + |T.intercept - U.intercept| := by rfl
  have h2 : dist (dyadicTubeToLinf T) (dyadicTubeToLinf U) =
      max (|(T.slope + T.intercept) - (U.slope + U.intercept)|)
          (|(T.slope - T.intercept) - (U.slope - U.intercept)|) := by
    simp [dyadicTubeToLinf, dist_eq_norm] <;> rfl
  rw [h1, h2]
  have h3 := abs_add_abs_eq_max (T.slope - U.slope) (T.intercept - U.intercept)
  ring_nf at h3 ⊢ <;> exact h3

/-- dyadicTubeToLinf is injective. -/
lemma dyadicTubeToLinf_injective {n : ℕ} :
    Function.Injective (dyadicTubeToLinf (n := n)) := by
  intro T U h
  have h1 : T.slope + T.intercept = U.slope + U.intercept :=
    congr_arg Prod.fst h
  have h2 : T.slope - T.intercept = U.slope - U.intercept :=
    congr_arg Prod.snd h
  have hs : T.slope = U.slope := by linarith
  have hi : T.intercept = U.intercept := by linarith
  have ha : (T.a : ℝ) = (U.a : ℝ) := by
    have hδ : (dyadicDelta n : ℝ) ≠ 0 := (dyadicDelta_pos n).ne'
    have h_eq : (T.a : ℝ) * dyadicDelta n = (U.a : ℝ) * dyadicDelta n := by
      simpa [DyadicTube.slope] using hs
    have h_eq2 : dyadicDelta n * (T.a : ℝ) = dyadicDelta n * (U.a : ℝ) := by
      have h : (T.a : ℝ) * dyadicDelta n = (U.a : ℝ) * dyadicDelta n := h_eq
      ring_nf at h ⊢; exact h
    exact (mul_right_inj' hδ).mp h_eq2
  have hb : (T.b : ℝ) = (U.b : ℝ) := by
    have hδ : (dyadicDelta n : ℝ) ≠ 0 := (dyadicDelta_pos n).ne'
    have h_eq : (T.b : ℝ) * dyadicDelta n = (U.b : ℝ) * dyadicDelta n := by
      simpa [DyadicTube.intercept] using hi
    have h_eq2 : dyadicDelta n * (T.b : ℝ) = dyadicDelta n * (U.b : ℝ) := by
      have h : (T.b : ℝ) * dyadicDelta n = (U.b : ℝ) * dyadicDelta n := h_eq
      ring_nf at h ⊢; exact h
    exact (mul_right_inj' hδ).mp h_eq2
  have ha' : T.a = U.a := by exact_mod_cast ha
  have hb' : T.b = U.b := by exact_mod_cast hb
  cases T
  cases U
  simp_all

/-- At most 9 δ-separated DyadicTubes in a δ-ball (L1 metric).

    Proof: map to L∞ via dyadicTubeToLinf and apply the 3×3 thirds partition. -/
lemma max_points_in_delta_ball_DyadicTube {n : ℕ} {δ : ℝ} (hδ_pos : 0 < δ)
    (S : Finset (DyadicTube n)) (hsep : SeparatedAt δ (S : Set (DyadicTube n)))
    (x : DyadicTube n) :
    (S.filter (fun y => dist y x ≤ δ)).card ≤ 9 := by
  let f : DyadicTube n → ℝ × ℝ := dyadicTubeToLinf
  let S' := S.image f
  have h_inj : Set.InjOn f (S : Set (DyadicTube n)) :=
    fun _ _ y _ h => dyadicTubeToLinf_injective h
  have hsep' : SeparatedAt δ (S' : Set (ℝ × ℝ)) := by
    intro a ha b hb hne
    rcases Finset.mem_image.mp ha with ⟨y, hy, rfl⟩
    rcases Finset.mem_image.mp hb with ⟨z, hz, h_eq⟩
    have h_yne_z : y ≠ z := by
      intro h
      have h' : f y = f z := by rw [h]
      have h'' : f y = b := Eq.trans h' h_eq
      exact hne h''
    have h : δ ≤ dist y z := hsep hy hz h_yne_z
    have h' : δ ≤ dist (f y) (f z) := by
      rw [←dyadicTube_dist_linf y z]; exact h
    rw [h_eq] at h'
    exact h'
  have h_filter_img : (S.filter (fun y => dist y x ≤ δ)).image f =
      S'.filter (fun y => dist y (f x) ≤ δ) := by
    ext z
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨y, ⟨hy, hdist⟩, rfl⟩
      exact ⟨Finset.mem_image.mpr ⟨y, hy, rfl⟩, by
        rw [←dyadicTube_dist_linf y x]; exact hdist⟩
    · rintro ⟨h_in, hdist⟩
      rcases Finset.mem_image.mp h_in with ⟨y, hy, rfl⟩
      have hdist' : dist y x ≤ δ := by
        have h_eq : dist (f y) (f x) = dist y x := (dyadicTube_dist_linf y x).symm
        rw [h_eq] at hdist
        exact hdist
      exact ⟨y, ⟨hy, hdist'⟩, rfl⟩
  have h_card : ((S.filter (fun y => dist y x ≤ δ)).image f).card =
      (S.filter (fun y => dist y x ≤ δ)).card :=
    Finset.card_image_of_injOn (h_inj.mono (fun x hx => (Finset.mem_filter.mp hx).1))
  rw [←h_card, h_filter_img]
  exact DirecretisedFurstenbergEstimate.SSetBridges.max_points_in_delta_ball
    hδ_pos S' hsep' (f x)

/-- Convert IsFiniteDeltaSSet to IsDeltaSSet for DyadicTube (L1 parameter metric).

    Constant: 9 * C, from the 9-point L1 packing bound.
    Mirrors IsFiniteDeltaSSet_to_delta_sset_R2. -/
lemma IsFiniteDeltaSSet_to_delta_sset_DyadicTube {n : ℕ}
    {δ s C : ℝ} {S : Finset (DyadicTube n)}
    (h : IsFiniteDeltaSSet δ s C S) :
    IsDeltaSSet δ s (9 * C) (S : Set (DyadicTube n)) := by
  rcases h with ⟨hS_nonempty, hδ_pos, hC_ge1, hs_nonneg, hS_sep, h_growth⟩
  have hC_pos : 0 < C := by linarith
  let εnn : NNReal := δ.toNNReal
  have hεnn_coe : (εnn : ℝ) = δ := by
    simp [εnn, Real.toNNReal_of_nonneg hδ_pos.le]
  have h_pack_cover : (S.card : ENNReal) ≤
      (9 : ENNReal) * Metric.externalCoveringNumber εnn (S : Set (DyadicTube n)) :=
    DirecretisedFurstenbergEstimate.SSetBridges.packing_cover_generic
      (hδ_pos := hδ_pos) (hsep := hS_sep) (hK_pos := by norm_num)
      (max_points_in_delta_ball_DyadicTube hδ_pos S hS_sep)
  refine' ⟨hS_nonempty, hδ_pos, by positivity, hs_nonneg, _⟩
  intro x r hr
  let S' : Finset (DyadicTube n) := S.filter (fun y => dist y x ≤ r)
  have hS'_eq : (S' : Set (DyadicTube n)) =
      (S : Set (DyadicTube n)) ∩ Metric.closedBall x r := by
    ext y; simp [S', Metric.mem_closedBall]
  have h1 : (Metric.externalCoveringNumber εnn (S' : Set (DyadicTube n)) : ENNReal) ≤
      (S'.card : ENNReal) := by
    exact_mod_cast Metric.externalCoveringNumber_le_encard_self (S' : Set (DyadicTube n))
  have h2 : (S'.card : ℝ) ≤ C * r ^ s * (S.card : ℝ) := h_growth x r hr
  have h_nonneg_C : 0 ≤ C := by linarith
  have h_nonneg_r : 0 ≤ r := by linarith
  have h_nonneg_s : 0 ≤ s := hs_nonneg
  have h3 : (Metric.externalCoveringNumber εnn (S' : Set (DyadicTube n)) : ENNReal) ≤
      ENNReal.ofReal (C * r ^ s * (S.card : ℝ)) := by
    calc (Metric.externalCoveringNumber εnn (S' : Set (DyadicTube n)) : ENNReal)
      ≤ (S'.card : ENNReal) := h1
    _ = ENNReal.ofReal ((S'.card : ℝ)) := by simp
    _ ≤ ENNReal.ofReal (C * r ^ s * (S.card : ℝ)) := by
      exact ENNReal.ofReal_le_ofReal h2
  have h4 : (S.card : ENNReal) ≤
      (9 : ENNReal) * Metric.externalCoveringNumber εnn (S : Set (DyadicTube n)) :=
    h_pack_cover
  have h5 : Metric.externalCoveringNumber εnn (S : Set (DyadicTube n)) ≠ ⊤ := by
    have h6 : (S : Set (DyadicTube n)).encard ≠ ⊤ := by simp
    have h71 : Metric.externalCoveringNumber εnn (S : Set (DyadicTube n)) ≤
        (S : Set (DyadicTube n)).encard :=
      Metric.externalCoveringNumber_le_encard_self (S : Set (DyadicTube n))
    exact ne_top_of_le_ne_top h6 h71
  have h_rpow : (ENNReal.ofReal r) ^ s = ENNReal.ofReal (r ^ s) := by
    rw [ENNReal.ofReal_rpow_of_nonneg h_nonneg_r h_nonneg_s]
  have h9 : ENNReal.ofReal (C * r ^ s * (S.card : ℝ)) ≤
      ENNReal.ofReal (9 * C) * ENNReal.ofReal (r ^ s) *
        Metric.externalCoveringNumber εnn (S : Set (DyadicTube n)) := by
    have h10 : ENNReal.ofReal (C * r ^ s * (S.card : ℝ)) =
        ENNReal.ofReal (C * r ^ s) * (S.card : ENNReal) := by
      rw [ENNReal.ofReal_mul (show 0 ≤ C * r ^ s by positivity)] <;> simp
    rw [h10]
    have h11 : ENNReal.ofReal (C * r ^ s) * (S.card : ENNReal) ≤
        ENNReal.ofReal (C * r ^ s) * ((9 : ENNReal) *
          Metric.externalCoveringNumber εnn (S : Set (DyadicTube n))) := by gcongr
    have h12 : ENNReal.ofReal (C * r ^ s) = ENNReal.ofReal C * ENNReal.ofReal (r ^ s) := by
      rw [ENNReal.ofReal_mul h_nonneg_C]
    have h13 : ENNReal.ofReal (C * r ^ s) * ((9 : ENNReal) *
        Metric.externalCoveringNumber εnn (S : Set (DyadicTube n))) =
        ENNReal.ofReal (9 * C) * ENNReal.ofReal (r ^ s) *
          Metric.externalCoveringNumber εnn (S : Set (DyadicTube n)) := by
      rw [h12]
      have h14 : ENNReal.ofReal (9 * C) = (9 : ENNReal) * ENNReal.ofReal C := by
        have h15 : ENNReal.ofReal (9 * C) = ENNReal.ofReal 9 * ENNReal.ofReal C := by
          rw [ENNReal.ofReal_mul (show 0 ≤ (9 : ℝ) by norm_num)]
        have h16 : ENNReal.ofReal 9 = (9 : ENNReal) := by norm_cast
        rw [h15, h16] <;> ring
      rw [h14] <;> simp [mul_assoc, mul_comm, mul_left_comm] <;> ring
    rw [h13] at h11; exact h11
  have h_main : (Metric.externalCoveringNumber εnn (S' : Set (DyadicTube n)) : ENNReal) ≤
      ENNReal.ofReal (9 * C) * (ENNReal.ofReal r) ^ s *
        Metric.externalCoveringNumber εnn (S : Set (DyadicTube n)) := by
    rw [h_rpow]; exact le_trans h3 h9
  have h_final : Metric.externalCoveringNumber δ.toNNReal
      ((S : Set (DyadicTube n)) ∩ Metric.closedBall x r) ≤
      ENNReal.ofReal (9 * C) * (ENNReal.ofReal r) ^ s *
        Metric.externalCoveringNumber δ.toNNReal (S : Set (DyadicTube n)) := by
    have h_eq1 : εnn = δ.toNNReal := by simp [εnn]
    rw [h_eq1] at h_main
    rw [hS'_eq] at h_main
    exact h_main
  exact h_final

/-! ### Pigeonhole lemma for intersection-filtered coarse families -/

/-- Given a global family C' and a set of squares Qset, with total intersection
    incidences bounded below by H, there exists a square Q ∈ Qset such that
    the filtered family {c ∈ C' | intersects c Q} has size ≥ H / |Qset|.

    This is the basic averaging pigeonhole. For the B1 9-neighbor argument,
    the total incidences H should be divided by 9 first (each coarse tube
    contributes to at most 9 relevant coarse squares in the 3×3 neighborhood). -/
lemma pigeonhole_exists_good_square
    {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (C' : Finset X) (Qset : Finset Y)
    (intersects : X → Y → Prop) [∀ x y, Decidable (intersects x y)]
    (H : ℕ) (hQset_nonempty : Qset.Nonempty)
    (hH : H ≤ ∑ Q ∈ Qset, (C'.filter (fun c => intersects c Q)).card) :
    ∃ Q ∈ Qset, ((C'.filter (fun c => intersects c Q)).card : ℝ) ≥
      (H : ℝ) / (Qset.card : ℝ) := by
  let f : Y → ℝ := fun Q => (C'.filter (fun c => intersects c Q)).card
  let g : Y → ℝ := fun _ => (H : ℝ) / (Qset.card : ℝ)
  by_contra h
  push Not at h
  have h_pos : (0 : ℝ) < (Qset.card : ℝ) := by exact_mod_cast hQset_nonempty.card_pos
  have h_strict : ∀ Q ∈ Qset, f Q < g Q := by
    intro Q hQ
    exact h Q hQ
  have h_diff_pos : ∀ Q ∈ Qset, 0 < g Q - f Q := by
    intro Q hQ
    linarith [h_strict Q hQ]
  have h_sum_diff : 0 < ∑ Q ∈ Qset, (g Q - f Q) :=
    Finset.sum_pos h_diff_pos hQset_nonempty
  have h_eq : ∑ Q ∈ Qset, (g Q - f Q) = (∑ Q ∈ Qset, g Q) - ∑ Q ∈ Qset, f Q := by
    rw [Finset.sum_sub_distrib]
  rw [h_eq] at h_sum_diff
  have h_sum_g : ∑ Q ∈ Qset, g Q = (H : ℝ) := by
    simp [g, Finset.sum_const, h_pos.ne'] <;> field_simp [h_pos.ne'] <;> ring
  rw [h_sum_g] at h_sum_diff
  have h_sum_eq : (∑ Q ∈ Qset, f Q) = ↑(∑ Q ∈ Qset, (C'.filter (fun c => intersects c Q)).card) := by
    have h1 : (∑ Q ∈ Qset, f Q) = ∑ Q ∈ Qset, ↑((C'.filter (fun c => intersects c Q)).card) := by
      apply Finset.sum_congr rfl
      intro Q _
      simp [f] <;> norm_cast
    rw [h1, Nat.cast_sum]
  have h' : (H : ℝ) ≤ (∑ Q ∈ Qset, f Q) := by
    rw [h_sum_eq]
    exact_mod_cast hH
  linarith

/-- Dyadic pigeonhole: given positive integers `f Q ≤ 2^K` for `Q ∈ Qset`,
there exists `k ≤ K` such that the dyadic band `[2^k, 2^{k+1})` contains at least
`|Qset| / (K+1)` elements (real-valued lower bound). -/
lemma dyadic_pigeonhole_sizes
    {Y : Type*} [DecidableEq Y]
    (Qset : Finset Y) (f : Y → ℕ)
    (K : ℕ) (hK : ∀ Q ∈ Qset, f Q ≤ 2^K)
    (h_pos : ∀ Q ∈ Qset, 0 < f Q) :
    ∃ (k : ℕ), k ≤ K ∧
      ((Qset.filter (fun Q => 2^k ≤ f Q ∧ f Q < 2^(k + 1))).card : ℝ) ≥
        (Qset.card : ℝ) / (K + 1 : ℝ) := by
  let S : ℕ → Finset Y := fun k =>
    Qset.filter (fun Q => 2^k ≤ f Q ∧ f Q < 2^(k + 1))
  have h1 : ∀ Q ∈ Qset, ∃ k : ℕ, k ≤ K ∧ 2^k ≤ f Q ∧ f Q < 2^(k + 1) := by
    intro Q hQ
    have h_fpos : 0 < f Q := h_pos Q hQ
    have h_fK : f Q ≤ 2^K := hK Q hQ
    have hP : ∃ n : ℕ, f Q < 2^(n + 1) := by
      refine ⟨K, ?_⟩
      have h : 2^K < 2^(K + 1) := by
        apply Nat.pow_lt_pow_right <;> norm_num
      omega
    let k := Nat.find hP
    have hk_upper : f Q < 2^(k + 1) := Nat.find_spec hP
    have hk_le : k ≤ K := Nat.find_min' hP (by
      have h : f Q < 2^(K + 1) := by
        have h' : 2^K < 2^(K + 1) := by apply Nat.pow_lt_pow_right <;> norm_num
        omega
      exact h)
    have hk_lower : 2^k ≤ f Q := by
      by_cases h_k0 : k = 0
      · rw [h_k0]; norm_num at *; omega
      · have h_kpos : 0 < k := Nat.pos_of_ne_zero h_k0
        have h_prev : k - 1 < k := by omega
        have h_not : ¬(f Q < 2^((k - 1) + 1)) := Nat.find_min hP h_prev
        have h_eq : (k - 1) + 1 = k := by omega
        rw [h_eq] at h_not; omega
    exact ⟨k, hk_le, hk_lower, hk_upper⟩
  have h_cover : Qset ⊆ Finset.biUnion (Finset.range (K + 1)) S := by
    intro Q hQ
    rcases h1 Q hQ with ⟨k, hk_le, hk_lower, hk_upper⟩
    have hk_in : k ∈ Finset.range (K + 1) := by
      simp only [Finset.mem_range]; omega
    have hQ_in_S : Q ∈ S k := by
      simp only [S, Finset.mem_filter] <;> exact ⟨hQ, ⟨hk_lower, hk_upper⟩⟩
    exact Finset.mem_biUnion.mpr ⟨k, hk_in, hQ_in_S⟩
  have h_nat : Qset.card ≤ ∑ k ∈ Finset.range (K + 1), (S k).card := by
    have h : Qset.card ≤ (Finset.biUnion (Finset.range (K + 1)) S).card :=
      Finset.card_le_card h_cover
    have h2 : (Finset.biUnion (Finset.range (K + 1)) S).card ≤ ∑ k ∈ Finset.range (K + 1), (S k).card :=
      Finset.card_biUnion_le
    exact le_trans h h2
  have h_card : (Qset.card : ℝ) ≤ ∑ k ∈ Finset.range (K + 1), ((S k).card : ℝ) := by
    exact_mod_cast h_nat
  by_contra h
  push Not at h
  have h_all : ∀ k ∈ Finset.range (K + 1), ((S k).card : ℝ) < (Qset.card : ℝ) / (K + 1 : ℝ) := by
    intro k hk
    have h_k_le : k ≤ K := by
      simp only [Finset.mem_range] at hk; omega
    exact h k h_k_le
  have h_nonempty : (Finset.range (K + 1)).Nonempty := by
    simp <;> omega
  have h_sum_lt : ∑ k ∈ Finset.range (K + 1), ((S k).card : ℝ) <
      ∑ k ∈ Finset.range (K + 1), ((Qset.card : ℝ) / (K + 1 : ℝ)) := by
    exact Finset.sum_lt_sum_of_nonempty h_nonempty h_all
  have h_rhs : ∑ k ∈ Finset.range (K + 1), ((Qset.card : ℝ) / (K + 1 : ℝ)) = (Qset.card : ℝ) := by
    simp [Finset.sum_const, Finset.card_range]
    <;> field_simp <;> ring
  rw [h_rhs] at h_sum_lt
  linarith

/-- Tube retention: from QTTC bound `M ≤ K_val * |S|` and `K_val ≤ K`,
    derive `|S| ≥ M / Nat.ceil K`. -/
lemma tube_retention_from_Kval
    {α : Type*} {M : ℕ} {K_val K : ℝ} (hK_one : 1 ≤ K)
    (hK_val_le : K_val ≤ K)
    {S : Finset α} (h : (M : ℝ) ≤ K_val * (S.card : ℝ)) :
    S.card ≥ M / Nat.ceil K := by
  have hK_pos : 0 < K := by linarith
  have h1 : (M : ℝ) ≤ K * (S.card : ℝ) := by
    calc (M : ℝ) ≤ K_val * (S.card : ℝ) := h
      _ ≤ K * (S.card : ℝ) := by gcongr <;> linarith
  have h_ceil_pos : 0 < Nat.ceil K := Nat.ceil_pos.mpr hK_pos
  have h2 : (M : ℝ) ≤ (Nat.ceil K : ℝ) * (S.card : ℝ) := by
    calc (M : ℝ) ≤ K * (S.card : ℝ) := h1
      _ ≤ (Nat.ceil K : ℝ) * (S.card : ℝ) := by
        gcongr
        <;> exact Nat.le_ceil K
  have h3 : (M : ℝ) / (Nat.ceil K : ℝ) ≤ (S.card : ℝ) := by
    have h4 : 0 < (Nat.ceil K : ℝ) := by exact_mod_cast h_ceil_pos
    calc (M : ℝ) / (Nat.ceil K : ℝ)
      ≤ ((Nat.ceil K : ℝ) * (S.card : ℝ)) / (Nat.ceil K : ℝ) := by gcongr
      _ = (S.card : ℝ) := by field_simp [h4.ne'] <;> ring
  have h5 : ((M / Nat.ceil K : ℕ) : ℝ) ≤ (M : ℝ) / (Nat.ceil K : ℝ) := by
    exact Nat.cast_div_le
  have h6 : ((M / Nat.ceil K : ℕ) : ℝ) ≤ (S.card : ℝ) := le_trans h5 h3
  exact_mod_cast h6

/-- Polylog absorption using explicit K_val formula.
    `K_val = 2^21 * (log_2(|coarseRange|) + 4)^6` is bounded by `(n-m+1)^100`
    when `2m ≤ n` and `m ≥ 1`. This equals `inductionLossGap (n - m)`. -/
lemma polylog_absorption_explicit
    {n m : ℕ} (hnm : m ≤ n) (h_ratio : 2 * m ≤ n) (hm_pos : 1 ≤ m)
    (T₀ : Finset (DyadicTube n))
    (h_bound : ∀ T ∈ T₀, |T.a| ≤ (2^(n+1) : ℤ) ∧ |T.b| ≤ (2^(n+2) : ℤ))
    (K_val : ℝ)
    (hK_val_eq : K_val = (2^21 : ℝ) * ((Nat.log 2 (coarseRange n m hnm T₀).card + 4 : ℕ) : ℝ)^6) :
    K_val ≤ ((n - m + 1 : ℝ)^100) := by
  have hA : ∀ T ∈ T₀, |T.a| ≤ ((2^(n+1) : ℕ) : ℤ) := by
    intro T hT; exact (h_bound T hT).1
  have hB : ∀ T ∈ T₀, |T.b| ≤ ((2^(n+2) : ℕ) : ℤ) := by
    intro T hT; exact (h_bound T hT).2
  have h_card_bound : (coarseRange n m hnm T₀).card ≤
      (2 * ((2^(n+1) : ℕ) / refinementFactor n m) + 3) *
      (2 * ((2^(n+2) : ℕ) / refinementFactor n m) + 3) :=
    coarseRange_card_bound hnm hA hB
  have h_rf : refinementFactor n m = 2^(n - m) := by
    simp [refinementFactor, hnm] <;> omega
  have h_div1 : (2^(n+1) : ℕ) / refinementFactor n m = 2^(m + 1) := by
    rw [h_rf]
    have h_eq : 2^(n + 1) = 2^(n - m) * 2^(m + 1) := by
      have h : n - m + (m + 1) = n + 1 := by omega
      have h' : 2^(n - m) * 2^(m + 1) = 2^(n - m + (m + 1)) := by
        rw [← Nat.pow_add] <;> rfl
      rw [h'] <;> rw [h]
    rw [h_eq, Nat.mul_div_cancel_left] <;> positivity
  have h_div2 : (2^(n+2) : ℕ) / refinementFactor n m = 2^(m + 2) := by
    rw [h_rf]
    have h_eq : 2^(n + 2) = 2^(n - m) * 2^(m + 2) := by
      have h : n - m + (m + 2) = n + 2 := by omega
      have h' : 2^(n - m) * 2^(m + 2) = 2^(n - m + (m + 2)) := by
        rw [← Nat.pow_add] <;> rfl
      rw [h'] <;> rw [h]
    rw [h_eq, Nat.mul_div_cancel_left] <;> positivity
  rw [h_div1, h_div2] at h_card_bound
  have h3_le_pow2 : ∀ k : ℕ, k ≥ 3 → 3 ≤ 2^k := by
    intro k hk
    have h_exists : ∃ j : ℕ, k = 3 + j := by
      refine ⟨k - 3, ?_⟩
      omega
    rcases h_exists with ⟨j, rfl⟩
    have h : 2^(3 + j) ≥ 8 := by
      have h' : 2^(3 + j) = 8 * 2^j := by
        rw [pow_add] <;> ring
      rw [h']
      have h'' : 2^j ≥ 1 := by
        apply Nat.one_le_pow
        <;> norm_num
      nlinarith
    linarith
  have h_log_bound : Nat.log 2 (coarseRange n m hnm T₀).card ≤ 2 * m + 7 := by
    have h9 : (coarseRange n m hnm T₀).card ≤ (2 * 2^(m + 1) + 3) * (2 * 2^(m + 2) + 3) := h_card_bound
    have h10 : (2 * 2^(m + 1) + 3) * (2 * 2^(m + 2) + 3) ≤ 2^(2 * m + 7) := by
      have h11 : 2 * 2^(m + 1) + 3 ≤ 2^(m + 3) := by
        have h12 : 2 * 2^(m + 1) = 2^(m + 2) := by ring
        rw [h12]
        have h13 : 3 ≤ 2^(m + 2) := h3_le_pow2 (m + 2) (by omega)
        have h14 : 2^(m + 3) = 2^(m + 2) + 2^(m + 2) := by
          have h15 : 2^(m + 3) = 2 * 2^(m + 2) := by ring
          rw [h15] <;> ring
        rw [h14]
        <;> linarith
      have h12 : 2 * 2^(m + 2) + 3 ≤ 2^(m + 4) := by
        have h13 : 2 * 2^(m + 2) = 2^(m + 3) := by ring
        rw [h13]
        have h14 : 3 ≤ 2^(m + 3) := h3_le_pow2 (m + 3) (by omega)
        have h15 : 2^(m + 4) = 2^(m + 3) + 2^(m + 3) := by
          have h16 : 2^(m + 4) = 2 * 2^(m + 3) := by ring
          rw [h16] <;> ring
        rw [h15] <;> linarith
      calc (2 * 2^(m + 1) + 3) * (2 * 2^(m + 2) + 3)
        ≤ 2^(m + 3) * 2^(m + 4) := by gcongr
      _ = 2^(2 * m + 7) := by
        have h : 2^(m + 3) * 2^(m + 4) = 2^((m + 3) + (m + 4)) := by
          rw [← Nat.pow_add] <;> rfl
        rw [h] <;> ring
    have h11 : (coarseRange n m hnm T₀).card ≤ 2^(2 * m + 7) := le_trans h9 h10
    have h12 : Nat.log 2 (coarseRange n m hnm T₀).card ≤ Nat.log 2 (2^(2 * m + 7)) :=
      Nat.log_mono_right h11
    have h13 : Nat.log 2 (2^(2 * m + 7)) = 2 * m + 7 := by
      rw [Nat.log_pow] <;> simp
    rw [h13] at h12
    exact h12
  have h14 : (Nat.log 2 (coarseRange n m hnm T₀).card + 4 : ℕ) ≤ 2 * m + 11 := by omega
  rw [hK_val_eq]
  have h15 : (2^21 : ℝ) * (((Nat.log 2 (coarseRange n m hnm T₀).card + 4 : ℕ) : ℝ)^6) ≤
      (2^21 : ℝ) * ((2 * m + 11 : ℝ)^6) := by
    gcongr <;> norm_cast <;> omega
  have h17_nat : n - m + 1 ≥ m + 1 := by omega
  have h17 : (n - m + 1 : ℝ) ≥ (m + 1 : ℝ) := by exact_mod_cast h17_nat
  have h19 : (2 * m + 11 : ℝ) ≤ 11 * (m + 1 : ℝ) := by
    have h20 : (m : ℝ) ≥ 1 := by exact_mod_cast hm_pos
    linarith
  have h21 : (2 * m + 11 : ℝ)^6 ≤ (11 : ℝ)^6 * ((m + 1 : ℝ)^6) := by
    calc (2 * m + 11 : ℝ)^6
      ≤ (11 * (m + 1 : ℝ))^6 := by gcongr
    _ = (11 : ℝ)^6 * ((m + 1 : ℝ)^6) := by ring
  have h22 : (2^21 : ℝ) * (11 : ℝ)^6 < (2 : ℝ)^94 := by
    have h23 : (11 : ℝ)^6 < (2 : ℝ)^21 := by norm_num
    have h24 : (2^21 : ℝ) * (11 : ℝ)^6 < (2^21 : ℝ) * (2^21 : ℝ) := by gcongr
    have h25 : (2^21 : ℝ) * (2^21 : ℝ) = (2 : ℝ)^42 := by ring
    rw [h25] at h24
    linarith
  have h26 : (m + 1 : ℝ) ≥ 2 := by
    have h27 : (m : ℝ) ≥ 1 := by exact_mod_cast hm_pos
    linarith
  have h28 : (2 : ℝ)^94 ≤ ((m + 1 : ℝ)^94) := by
    gcongr <;> linarith
  have h16 : (2^21 : ℝ) * ((2 * m + 11 : ℝ)^6) ≤ ((n - m + 1 : ℝ)^100) := by
    calc (2^21 : ℝ) * ((2 * m + 11 : ℝ)^6)
      ≤ (2^21 : ℝ) * ((11 : ℝ)^6 * ((m + 1 : ℝ)^6)) := by gcongr
    _ = ((2^21 : ℝ) * (11 : ℝ)^6) * ((m + 1 : ℝ)^6) := by ring
    _ ≤ (2 : ℝ)^94 * ((m + 1 : ℝ)^6) := by gcongr
    _ ≤ ((m + 1 : ℝ)^94) * ((m + 1 : ℝ)^6) := by gcongr
    _ = ((m + 1 : ℝ)^100) := by ring
    _ ≤ ((n - m + 1 : ℝ)^100) := by gcongr <;> exact h17
  exact le_trans h15 h16

/-- Logarithmic bound on the cardinality of `coarseRange`.
    `Nat.log 2 (coarseRange n m hnm T₀).card ≤ 2 * m + 7` when tubes have bounded coefficients. -/
lemma coarse_range_log_bound
    {n m : ℕ} (hnm : m ≤ n) (hm_pos : 1 ≤ m)
    (T₀ : Finset (DyadicTube n))
    (h_bound : ∀ T ∈ T₀, |T.a| ≤ (2^(n+1) : ℤ) ∧ |T.b| ≤ (2^(n+2) : ℤ)) :
    Nat.log 2 (coarseRange n m hnm T₀).card ≤ 2 * m + 7 := by
  have hA : ∀ T ∈ T₀, |T.a| ≤ ((2^(n+1) : ℕ) : ℤ) := by
    intro T hT; exact (h_bound T hT).1
  have hB : ∀ T ∈ T₀, |T.b| ≤ ((2^(n+2) : ℕ) : ℤ) := by
    intro T hT; exact (h_bound T hT).2
  have h_card_bound : (coarseRange n m hnm T₀).card ≤
      (2 * ((2^(n+1) : ℕ) / refinementFactor n m) + 3) *
      (2 * ((2^(n+2) : ℕ) / refinementFactor n m) + 3) :=
    coarseRange_card_bound hnm hA hB
  have h_rf : refinementFactor n m = 2^(n - m) := by
    simp [refinementFactor, hnm] <;> omega
  have h_div1 : (2^(n+1) : ℕ) / refinementFactor n m = 2^(m + 1) := by
    rw [h_rf]
    have h_eq : 2^(n + 1) = 2^(n - m) * 2^(m + 1) := by
      have h : n - m + (m + 1) = n + 1 := by omega
      have h' : 2^(n - m) * 2^(m + 1) = 2^(n - m + (m + 1)) := by rw [← Nat.pow_add] <;> rfl
      rw [h'] <;> rw [h]
    rw [h_eq, Nat.mul_div_cancel_left] <;> positivity
  have h_div2 : (2^(n+2) : ℕ) / refinementFactor n m = 2^(m + 2) := by
    rw [h_rf]
    have h_eq : 2^(n + 2) = 2^(n - m) * 2^(m + 2) := by
      have h : n - m + (m + 2) = n + 2 := by omega
      have h' : 2^(n - m) * 2^(m + 2) = 2^(n - m + (m + 2)) := by rw [← Nat.pow_add] <;> rfl
      rw [h'] <;> rw [h]
    rw [h_eq, Nat.mul_div_cancel_left] <;> positivity
  rw [h_div1, h_div2] at h_card_bound
  have h3_le_pow2 : ∀ k : ℕ, k ≥ 3 → 3 ≤ 2^k := by
    intro k hk
    have h_exists : ∃ j : ℕ, k = 3 + j := by refine ⟨k - 3, ?_⟩; omega
    rcases h_exists with ⟨j, rfl⟩
    have h : 2^(3 + j) ≥ 8 := by
      have h' : 2^(3 + j) = 8 * 2^j := by rw [pow_add] <;> ring
      rw [h']
      have h'' : 2^j ≥ 1 := by apply Nat.one_le_pow <;> norm_num
      nlinarith
    linarith
  have h9 : (coarseRange n m hnm T₀).card ≤ (2 * 2^(m + 1) + 3) * (2 * 2^(m + 2) + 3) := h_card_bound
  have h10 : (2 * 2^(m + 1) + 3) * (2 * 2^(m + 2) + 3) ≤ 2^(2 * m + 7) := by
    have h11 : 2 * 2^(m + 1) + 3 ≤ 2^(m + 3) := by
      have h12 : 2 * 2^(m + 1) = 2^(m + 2) := by ring
      rw [h12]
      have h13 : 3 ≤ 2^(m + 2) := h3_le_pow2 (m + 2) (by omega)
      have h14 : 2^(m + 3) = 2^(m + 2) + 2^(m + 2) := by
        have h15 : 2^(m + 3) = 2 * 2^(m + 2) := by ring
        rw [h15] <;> ring
      rw [h14] <;> linarith
    have h12 : 2 * 2^(m + 2) + 3 ≤ 2^(m + 4) := by
      have h13 : 2 * 2^(m + 2) = 2^(m + 3) := by ring
      rw [h13]
      have h14 : 3 ≤ 2^(m + 3) := h3_le_pow2 (m + 3) (by omega)
      have h15 : 2^(m + 4) = 2^(m + 3) + 2^(m + 3) := by
        have h16 : 2^(m + 4) = 2 * 2^(m + 3) := by ring
        rw [h16] <;> ring
      rw [h15] <;> linarith
    calc (2 * 2^(m + 1) + 3) * (2 * 2^(m + 2) + 3)
      ≤ 2^(m + 3) * 2^(m + 4) := by gcongr
    _ = 2^(2 * m + 7) := by
      have h : 2^(m + 3) * 2^(m + 4) = 2^((m + 3) + (m + 4)) := by rw [← Nat.pow_add] <;> rfl
      rw [h] <;> ring
  have h11 : (coarseRange n m hnm T₀).card ≤ 2^(2 * m + 7) := le_trans h9 h10
  have h12 : Nat.log 2 (coarseRange n m hnm T₀).card ≤ Nat.log 2 (2^(2 * m + 7)) := Nat.log_mono_right h11
  have h13 : Nat.log 2 (2^(2 * m + 7)) = 2 * m + 7 := by rw [Nat.log_pow] <;> simp
  rw [h13] at h12; exact h12

/-- Absorption of C₂ constant into polylog loss.
    C₂ = 1024 * 2^(s+2) * max(1, 25*C₁) * (log_2(|coarseRange|)+4)^2
    is bounded by C₁ * (n-m+1)^100 when 2m ≤ n, m ≥ 1, s ≤ 1, C₁ ≥ 1. -/
lemma C2_absorption
    {n m : ℕ} (hnm : m ≤ n) (h_ratio : 2 * m ≤ n) (hm_pos : 1 ≤ m)
    (T₀ : Finset (DyadicTube n))
    (h_bound : ∀ T ∈ T₀, |T.a| ≤ (2^(n+1) : ℤ) ∧ |T.b| ≤ (2^(n+2) : ℤ))
    (s C₁ : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) (hC1 : 1 ≤ C₁)
    (C₂ : ℝ)
    (hC2_eq : C₂ = 1024 * Real.rpow 2 (s + 2) * (max 1 (25 * C₁)) *
        ((Nat.log 2 (coarseRange n m hnm T₀).card + 4 : ℕ) : ℝ)^2) :
    C₂ ≤ C₁ * ((n - m + 1 : ℝ)^100) := by
  have hA : ∀ T ∈ T₀, |T.a| ≤ ((2^(n+1) : ℕ) : ℤ) := by
    intro T hT; exact (h_bound T hT).1
  have hB : ∀ T ∈ T₀, |T.b| ≤ ((2^(n+2) : ℕ) : ℤ) := by
    intro T hT; exact (h_bound T hT).2
  have h_card_bound : (coarseRange n m hnm T₀).card ≤
      (2 * ((2^(n+1) : ℕ) / refinementFactor n m) + 3) *
      (2 * ((2^(n+2) : ℕ) / refinementFactor n m) + 3) :=
    coarseRange_card_bound hnm hA hB
  have h_rf : refinementFactor n m = 2^(n - m) := by
    simp [refinementFactor, hnm] <;> omega
  have h_div1 : (2^(n+1) : ℕ) / refinementFactor n m = 2^(m + 1) := by
    rw [h_rf]
    have h_eq : 2^(n + 1) = 2^(n - m) * 2^(m + 1) := by
      have h : n - m + (m + 1) = n + 1 := by omega
      have h' : 2^(n - m) * 2^(m + 1) = 2^(n - m + (m + 1)) := by rw [← Nat.pow_add] <;> rfl
      rw [h'] <;> rw [h]
    rw [h_eq, Nat.mul_div_cancel_left] <;> positivity
  have h_div2 : (2^(n+2) : ℕ) / refinementFactor n m = 2^(m + 2) := by
    rw [h_rf]
    have h_eq : 2^(n + 2) = 2^(n - m) * 2^(m + 2) := by
      have h : n - m + (m + 2) = n + 2 := by omega
      have h' : 2^(n - m) * 2^(m + 2) = 2^(n - m + (m + 2)) := by rw [← Nat.pow_add] <;> rfl
      rw [h'] <;> rw [h]
    rw [h_eq, Nat.mul_div_cancel_left] <;> positivity
  rw [h_div1, h_div2] at h_card_bound
  have h3_le_pow2 : ∀ k : ℕ, k ≥ 3 → 3 ≤ 2^k := by
    intro k hk
    have h_exists : ∃ j : ℕ, k = 3 + j := by refine ⟨k - 3, ?_⟩; omega
    rcases h_exists with ⟨j, rfl⟩
    have h : 2^(3 + j) ≥ 8 := by
      have h' : 2^(3 + j) = 8 * 2^j := by rw [pow_add] <;> ring
      rw [h']
      have h'' : 2^j ≥ 1 := by apply Nat.one_le_pow <;> norm_num
      nlinarith
    linarith
  have h_log_bound : Nat.log 2 (coarseRange n m hnm T₀).card ≤ 2 * m + 7 := by
    have h9 : (coarseRange n m hnm T₀).card ≤ (2 * 2^(m + 1) + 3) * (2 * 2^(m + 2) + 3) := h_card_bound
    have h10 : (2 * 2^(m + 1) + 3) * (2 * 2^(m + 2) + 3) ≤ 2^(2 * m + 7) := by
      have h11 : 2 * 2^(m + 1) + 3 ≤ 2^(m + 3) := by
        have h12 : 2 * 2^(m + 1) = 2^(m + 2) := by ring
        rw [h12]
        have h13 : 3 ≤ 2^(m + 2) := h3_le_pow2 (m + 2) (by omega)
        have h14 : 2^(m + 3) = 2^(m + 2) + 2^(m + 2) := by
          have h15 : 2^(m + 3) = 2 * 2^(m + 2) := by ring
          rw [h15] <;> ring
        rw [h14] <;> linarith
      have h12 : 2 * 2^(m + 2) + 3 ≤ 2^(m + 4) := by
        have h13 : 2 * 2^(m + 2) = 2^(m + 3) := by ring
        rw [h13]
        have h14 : 3 ≤ 2^(m + 3) := h3_le_pow2 (m + 3) (by omega)
        have h15 : 2^(m + 4) = 2^(m + 3) + 2^(m + 3) := by
          have h16 : 2^(m + 4) = 2 * 2^(m + 3) := by ring
          rw [h16] <;> ring
        rw [h15] <;> linarith
      calc (2 * 2^(m + 1) + 3) * (2 * 2^(m + 2) + 3)
        ≤ 2^(m + 3) * 2^(m + 4) := by gcongr
      _ = 2^(2 * m + 7) := by
        have h : 2^(m + 3) * 2^(m + 4) = 2^((m + 3) + (m + 4)) := by rw [← Nat.pow_add] <;> rfl
        rw [h] <;> ring
    have h11 : (coarseRange n m hnm T₀).card ≤ 2^(2 * m + 7) := le_trans h9 h10
    have h12 : Nat.log 2 (coarseRange n m hnm T₀).card ≤ Nat.log 2 (2^(2 * m + 7)) := Nat.log_mono_right h11
    have h13 : Nat.log 2 (2^(2 * m + 7)) = 2 * m + 7 := by rw [Nat.log_pow] <;> simp
    rw [h13] at h12; exact h12
  have h14 : (Nat.log 2 (coarseRange n m hnm T₀).card + 4 : ℕ) ≤ 2 * m + 11 := by omega
  have h17_nat : n - m + 1 ≥ m + 1 := by omega
  have h17 : (n - m + 1 : ℝ) ≥ (m + 1 : ℝ) := by exact_mod_cast h17_nat
  have h_s_pow : Real.rpow 2 (s + 2) ≤ 8 := by
    have h1 : s + 2 ≤ 3 := by linarith
    have h2 : Real.rpow 2 (s + 2) ≤ Real.rpow 2 3 := Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
    norm_num at h2 ⊢; exact h2
  have h_max : max 1 (25 * C₁) = 25 * C₁ := by
    have h : 25 * C₁ ≥ 1 := by linarith
    rw [max_eq_right] <;> linarith
  rw [hC2_eq, h_max]
  have h15 : ((Nat.log 2 (coarseRange n m hnm T₀).card + 4 : ℕ) : ℝ)^2 ≤ ((2 * m + 11 : ℝ)^2) := by
    gcongr <;> norm_cast <;> omega
  have h16 : (1024 : ℝ) * 8 * 25 * ((2 * m + 11 : ℝ)^2) ≤ ((n - m + 1 : ℝ)^100) := by
    have h19 : (2 * m + 11 : ℝ) ≤ 11 * (m + 1 : ℝ) := by
      have h20 : (m : ℝ) ≥ 1 := by exact_mod_cast hm_pos
      linarith
    have h21 : ((2 * m + 11 : ℝ)^2) ≤ (11 : ℝ)^2 * ((m + 1 : ℝ)^2) := by
      calc ((2 * m + 11 : ℝ)^2)
        ≤ (11 * (m + 1 : ℝ))^2 := by gcongr
      _ = (11 : ℝ)^2 * ((m + 1 : ℝ)^2) := by ring
    have h22 : (1024 : ℝ) * 8 * 25 * (11 : ℝ)^2 < (2 : ℝ)^25 := by norm_num
    have h26 : (m + 1 : ℝ) ≥ 2 := by
      have h27 : (m : ℝ) ≥ 1 := by exact_mod_cast hm_pos
      linarith
    have h28 : (2 : ℝ)^25 ≤ ((m + 1 : ℝ)^98) := by
      have h29 : (2 : ℝ)^98 ≤ ((m + 1 : ℝ)^98) := by gcongr <;> linarith
      have h30 : (2 : ℝ)^25 ≤ (2 : ℝ)^98 := by
        gcongr <;> norm_num
      linarith
    calc (1024 : ℝ) * 8 * 25 * ((2 * m + 11 : ℝ)^2)
      ≤ (1024 : ℝ) * 8 * 25 * ((11 : ℝ)^2 * ((m + 1 : ℝ)^2)) := by gcongr
    _ = ((1024 : ℝ) * 8 * 25 * (11 : ℝ)^2) * ((m + 1 : ℝ)^2) := by ring
    _ ≤ (2 : ℝ)^25 * ((m + 1 : ℝ)^2) := by gcongr
    _ ≤ ((m + 1 : ℝ)^98) * ((m + 1 : ℝ)^2) := by gcongr
    _ = ((m + 1 : ℝ)^100) := by ring
    _ ≤ ((n - m + 1 : ℝ)^100) := by gcongr <;> exact h17
  calc (1024 : ℝ) * Real.rpow 2 (s + 2) * (25 * C₁) * (((Nat.log 2 (coarseRange n m hnm T₀).card + 4 : ℕ) : ℝ)^2)
    ≤ (1024 : ℝ) * 8 * (25 * C₁) * (((Nat.log 2 (coarseRange n m hnm T₀).card + 4 : ℕ) : ℝ)^2) := by gcongr
  _ = C₁ * ((1024 : ℝ) * 8 * 25 * (((Nat.log 2 (coarseRange n m hnm T₀).card + 4 : ℕ) : ℝ)^2)) := by ring
  _ ≤ C₁ * ((1024 : ℝ) * 8 * 25 * ((2 * m + 11 : ℝ)^2)) := by gcongr
  _ ≤ C₁ * ((n - m + 1 : ℝ)^100) := by gcongr

/-- Subset monotonicity for `IsFiniteDeltaSSet`.
    If `Q ⊆ P` and `P` is a finite `(δ,s,C)`-set, then `Q` is a finite
    `(δ, s, C * |P|/|Q|)`-set. The constant blows up by the cardinality ratio. -/
lemma IsFiniteDeltaSSet.subset
    {X : Type*} [PseudoMetricSpace X] {δ s C : ℝ} {P Q : Finset X}
    (h : IsFiniteDeltaSSet δ s C P) (hQ : Q ⊆ P) (hQ_nonempty : Q.Nonempty) :
    IsFiniteDeltaSSet δ s (C * (P.card : ℝ) / (Q.card : ℝ)) Q := by
  have hQcard_pos : (Q.card : ℝ) > 0 := by exact_mod_cast Finset.Nonempty.card_pos hQ_nonempty
  have h1 : Q.Nonempty := hQ_nonempty
  have h2 : 0 < δ := h.2.1
  have h3 : 1 ≤ C := h.2.2.1
  have h4 : 0 ≤ s := h.2.2.2.1
  have h5 : SeparatedAt δ (Q : Set X) := by
    intro x hx y hy hne
    have hxP : x ∈ (P : Set X) := hQ hx
    have hyP : y ∈ (P : Set X) := hQ hy
    exact h.2.2.2.2.1 hxP hyP hne
  have h6 : ∀ (x : X) (r : ℝ), δ ≤ r →
      ((Q.filter fun y => dist y x ≤ r).card : ℝ) ≤
        (C * (P.card : ℝ) / (Q.card : ℝ)) * r ^ s * (Q.card : ℝ) := by
    intro x r hr
    have h7 : (Q.filter fun y => dist y x ≤ r) ⊆ (P.filter fun y => dist y x ≤ r) := by
      intro y hy
      simp only [Finset.mem_filter] at hy ⊢
      exact ⟨hQ hy.1, hy.2⟩
    have h8 : ((Q.filter fun y => dist y x ≤ r).card : ℝ) ≤
        ((P.filter fun y => dist y x ≤ r).card : ℝ) := by
      exact_mod_cast Finset.card_le_card h7
    have h9 : ((P.filter fun y => dist y x ≤ r).card : ℝ) ≤ C * r ^ s * (P.card : ℝ) :=
      h.2.2.2.2.2 x r hr
    calc ((Q.filter fun y => dist y x ≤ r).card : ℝ)
      ≤ ((P.filter fun y => dist y x ≤ r).card : ℝ) := h8
    _ ≤ C * r ^ s * (P.card : ℝ) := h9
    _ = (C * (P.card : ℝ) / (Q.card : ℝ)) * r ^ s * (Q.card : ℝ) := by
      field_simp [hQcard_pos.ne'] <;> ring
  have h13 : (Q.card : ℝ) ≤ (P.card : ℝ) := by exact_mod_cast Finset.card_le_card hQ
  have h14 : (P.card : ℝ) / (Q.card : ℝ) ≥ 1 := by
    have h15 : 0 < (Q.card : ℝ) := hQcard_pos
    have h16 : (P.card : ℝ) ≥ (Q.card : ℝ) := h13
    have h17 : (P.card : ℝ) / (Q.card : ℝ) ≥ (Q.card : ℝ) / (Q.card : ℝ) := by gcongr
    have h18 : (Q.card : ℝ) / (Q.card : ℝ) = 1 := by
      field_simp [h15.ne'] <;> ring
    rw [h18] at h17
    exact h17
  have h12 : 1 ≤ C * (P.card : ℝ) / (Q.card : ℝ) := by
    have h16 : 0 < C := by linarith
    have h17 : C * ((P.card : ℝ) / (Q.card : ℝ)) ≥ 1 := by
      have h18 : C ≥ 1 := h3
      have h19 : (P.card : ℝ) / (Q.card : ℝ) ≥ 1 := h14
      calc C * ((P.card : ℝ) / (Q.card : ℝ))
        ≥ 1 * ((P.card : ℝ) / (Q.card : ℝ)) := by gcongr
      _ ≥ 1 := by linarith
    have h20 : C * (P.card : ℝ) / (Q.card : ℝ) = C * ((P.card : ℝ) / (Q.card : ℝ)) := by ring
    rw [h20]
    exact h17
  exact ⟨h1, h2, h12, h4, h5, h6⟩

/-- Uniformize cardinalities of a family of finite sets via dyadic pigeonholing.

    Given `C : Y → Finset α` with `0 < |C Q| ≤ 2^K` for `Q ∈ Qset`,
    find `k ≤ K`, `Qgood ⊆ Qset`, and `M_Δ = 2^k` such that:
    - `|Qgood| ≥ |Qset| / (K+1)`
    - For all `Q ∈ Qgood`: `M_Δ ≤ |C Q| < 2 * M_Δ`
    - There exist trimmed subsets `C_trim Q ⊆ C Q` with `|C_trim Q| = M_Δ`.

    This is the standard OS uniformization step for per-square tube families. -/
lemma uniformize_cardinalities {Y α : Type*} [DecidableEq Y] [DecidableEq α]
    (Qset : Finset Y) (C : Y → Finset α) (K : ℕ)
    (hK : ∀ Q ∈ Qset, (C Q).card ≤ 2^K)
    (h_nonempty : ∀ Q ∈ Qset, (C Q).Nonempty) :
    ∃ (k : ℕ) (Qgood : Finset Y) (M_Δ : ℕ) (C_trim : Y → Finset α),
      k ≤ K ∧
      M_Δ = 2^k ∧
      Qgood ⊆ Qset ∧
      (Qgood.card : ℝ) ≥ (Qset.card : ℝ) / (K + 1 : ℝ) ∧
      ∀ Q ∈ Qgood,
        (C_trim Q) ⊆ (C Q) ∧
        (C_trim Q).card = M_Δ ∧
        M_Δ ≤ (C Q).card ∧
        (C Q).card < 2 * M_Δ := by
  let f : Y → ℕ := fun Q => (C Q).card
  have hK' : ∀ Q ∈ Qset, f Q ≤ 2^K := by
    intro Q hQ
    simpa [f] using hK Q hQ
  have h_pos : ∀ Q ∈ Qset, 0 < f Q := by
    intro Q hQ
    have hne : (C Q).Nonempty := h_nonempty Q hQ
    simpa [f, Finset.Nonempty] using Finset.Nonempty.card_pos hne
  rcases dyadic_pigeonhole_sizes Qset f K hK' h_pos with ⟨k, hk_le, hcard⟩
  let Qgood : Finset Y := Qset.filter (fun Q => 2^k ≤ f Q ∧ f Q < 2^(k + 1))
  have hQgood_sub : Qgood ⊆ Qset := Finset.filter_subset _ _
  have hQgood_card : (Qgood.card : ℝ) ≥ (Qset.card : ℝ) / (K + 1 : ℝ) := hcard
  let M_Δ : ℕ := 2^k
  have hMΔ_pos : 0 < M_Δ := by positivity
  have h_bounds : ∀ Q ∈ Qgood, M_Δ ≤ (C Q).card ∧ (C Q).card < 2 * M_Δ := by
    intro Q hQ
    have h1 : 2^k ≤ f Q ∧ f Q < 2^(k + 1) := (Finset.mem_filter.mp hQ).2
    have h2 : M_Δ ≤ (C Q).card := by
      simpa [M_Δ, f] using h1.1
    have h3 : (C Q).card < 2 * M_Δ := by
      have h4 : f Q < 2^(k + 1) := h1.2
      have h5 : 2^(k + 1) = 2 * M_Δ := by
        simp [M_Δ, pow_succ] <;> ring
      rw [h5] at h4
      simpa [f] using h4
    exact ⟨h2, h3⟩
  choose C_trim htrim_sub htrim_card using fun (Q : Y) (hQ : Q ∈ Qgood) =>
    Finset.exists_subset_card_eq (h_bounds Q hQ).1
  refine' ⟨k, Qgood, M_Δ, fun Q => if hQ : Q ∈ Qgood then C_trim Q hQ else ∅,
    hk_le, rfl, hQgood_sub, hQgood_card, _⟩
  intro Q hQ
  have h4 : C_trim Q hQ ⊆ C Q := htrim_sub Q hQ
  have h5 : (C_trim Q hQ).card = M_Δ := htrim_card Q hQ
  have h6 : (fun Q => if hQ : Q ∈ Qgood then C_trim Q hQ else ∅) Q = C_trim Q hQ := by
    simp [hQ]
  rw [h6]
  exact ⟨h4, h5, (h_bounds Q hQ).1, (h_bounds Q hQ).2⟩

/-- Weighted dyadic pigeonhole: find a size band containing at least
    1/(K+1) of the total weight. -/
lemma weighted_dyadic_pigeonhole_sizes
    {Y : Type*} [DecidableEq Y]
    (Qset : Finset Y) (f : Y → ℕ) (w : Y → ℝ)
    (K : ℕ) (hK : ∀ Q ∈ Qset, f Q ≤ 2^K)
    (h_pos : ∀ Q ∈ Qset, 0 < f Q)
    (hw_nonneg : ∀ Q ∈ Qset, 0 ≤ w Q) :
    ∃ (k : ℕ), k ≤ K ∧
      let band := Qset.filter (fun Q => 2^k ≤ f Q ∧ f Q < 2^(k + 1))
      (∑ Q ∈ band, w Q) ≥ (∑ Q ∈ Qset, w Q) / (K + 1 : ℝ) := by
  let S : ℕ → Finset Y := fun k =>
    Qset.filter (fun Q => 2^k ≤ f Q ∧ f Q < 2^(k + 1))
  have h1 : ∀ Q ∈ Qset, ∃ k : ℕ, k ≤ K ∧ 2^k ≤ f Q ∧ f Q < 2^(k + 1) := by
    intro Q hQ
    have h_fpos : 0 < f Q := h_pos Q hQ
    have h_fK : f Q ≤ 2^K := hK Q hQ
    have hP : ∃ n : ℕ, f Q < 2^(n + 1) := by
      refine ⟨K, ?_⟩
      have h : 2^K < 2^(K + 1) := by
        apply Nat.pow_lt_pow_right <;> norm_num
      omega
    let k := Nat.find hP
    have hk_upper : f Q < 2^(k + 1) := Nat.find_spec hP
    have hk_le : k ≤ K := Nat.find_min' hP (by
      have h : f Q < 2^(K + 1) := by
        have h' : 2^K < 2^(K + 1) := by apply Nat.pow_lt_pow_right <;> norm_num
        omega
      exact h)
    have hk_lower : 2^k ≤ f Q := by
      by_cases h_k0 : k = 0
      · rw [h_k0]; norm_num at *; omega
      · have h_kpos : 0 < k := Nat.pos_of_ne_zero h_k0
        have h_prev : k - 1 < k := by omega
        have h_not : ¬(f Q < 2^((k - 1) + 1)) := Nat.find_min hP h_prev
        have h_eq : (k - 1) + 1 = k := by omega
        rw [h_eq] at h_not; omega
    exact ⟨k, hk_le, hk_lower, hk_upper⟩
  have h_cover : Qset ⊆ Finset.biUnion (Finset.range (K + 1)) S := by
    intro Q hQ
    rcases h1 Q hQ with ⟨k, hk_le, hk_lower, hk_upper⟩
    have hk_in : k ∈ Finset.range (K + 1) := by
      simp only [Finset.mem_range]; omega
    have hQ_in_S : Q ∈ S k := by
      simp only [S, Finset.mem_filter] <;> exact ⟨hQ, ⟨hk_lower, hk_upper⟩⟩
    exact Finset.mem_biUnion.mpr ⟨k, hk_in, hQ_in_S⟩
  have h_sub2 : Finset.biUnion (Finset.range (K + 1)) S ⊆ Qset := by
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨k, _, hxk⟩
    exact (Finset.mem_filter.mp hxk).1
  have h_eq : Finset.biUnion (Finset.range (K + 1)) S = Qset := by
    apply Finset.Subset.antisymm h_sub2 h_cover
  have h_disj : ∀ k1 ∈ Finset.range (K + 1), ∀ k2 ∈ Finset.range (K + 1),
      k1 ≠ k2 → Disjoint (S k1) (S k2) := by
    intro k1 _ k2 _ hne
    simp only [S, Finset.disjoint_left, Finset.mem_filter]
    intro Q h1 h2
    have h3 : 2^k1 ≤ f Q := h1.2.1
    have h4 : f Q < 2^(k1 + 1) := h1.2.2
    have h5 : 2^k2 ≤ f Q := h2.2.1
    have h6 : f Q < 2^(k2 + 1) := h2.2.2
    by_cases h : k1 < k2
    · have h7 : k1 + 1 ≤ k2 := by omega
      have h12 : (2 : ℕ)^(k1 + 1) ≤ (2 : ℕ)^k2 := by gcongr <;> norm_num
      linarith
    · have h' : k2 < k1 := by omega
      have h7 : k2 + 1 ≤ k1 := by omega
      have h12 : (2 : ℕ)^(k2 + 1) ≤ (2 : ℕ)^k1 := by gcongr <;> norm_num
      linarith
  have h2 : (∑ Q ∈ Finset.biUnion (Finset.range (K + 1)) S, w Q) =
      ∑ k ∈ Finset.range (K + 1), (∑ Q ∈ S k, w Q) := by
    rw [Finset.sum_biUnion h_disj]
  have h3 : (∑ Q ∈ Qset, w Q) = ∑ Q ∈ Finset.biUnion (Finset.range (K + 1)) S, w Q := by
    rw [h_eq]
  by_contra h
  push Not at h
  have h_all : ∀ k ∈ Finset.range (K + 1), (∑ Q ∈ S k, w Q) < (∑ Q ∈ Qset, w Q) / (K + 1 : ℝ) := by
    intro k hk
    have h_k_le : k ≤ K := by
      simp only [Finset.mem_range] at hk; omega
    have h_goal : ¬((∑ Q ∈ S k, w Q) ≥ (∑ Q ∈ Qset, w Q) / (K + 1 : ℝ)) := by
      simpa [S] using h k h_k_le
    exact lt_of_not_ge h_goal
  have h_sum2 : ∑ k ∈ Finset.range (K + 1), (∑ Q ∈ S k, w Q) <
      (K + 1 : ℝ) * ((∑ Q ∈ Qset, w Q) / (K + 1 : ℝ)) := by
    have h4 : ∑ k ∈ Finset.range (K + 1), (∑ Q ∈ S k, w Q) <
        ∑ k ∈ Finset.range (K + 1), ((∑ Q ∈ Qset, w Q) / (K + 1 : ℝ)) := by
      apply Finset.sum_lt_sum_of_nonempty
      · exact ⟨0, by simp⟩
      · intro k hk; exact h_all k hk
    have h5 : ∑ k ∈ Finset.range (K + 1), ((∑ Q ∈ Qset, w Q) / (K + 1 : ℝ)) =
        (K + 1 : ℝ) * ((∑ Q ∈ Qset, w Q) / (K + 1 : ℝ)) := by
      simp [Finset.sum_const, Finset.card_range] <;> ring
    rw [h5] at h4
    exact h4
  have h6 : (K + 1 : ℝ) * ((∑ Q ∈ Qset, w Q) / (K + 1 : ℝ)) = (∑ Q ∈ Qset, w Q) := by
    field_simp <;> ring
  rw [h6] at h_sum2
  have h7 : (∑ Q ∈ Qset, w Q) = ∑ k ∈ Finset.range (K + 1), (∑ Q ∈ S k, w Q) := by
    rw [h3, h2]
  rw [h7] at h_sum2
  linarith

/-- Weighted uniformization: select a dyadic band with ≥ 1/(K+1) weight retention,
    trim families to uniform size M_Δ = 2^k. -/
lemma weighted_uniformize_cardinalities
    {Y α : Type*} [DecidableEq Y] [DecidableEq α]
    (Qset : Finset Y) (C : Y → Finset α) (w : Y → ℝ) (K : ℕ)
    (hK : ∀ Q ∈ Qset, (C Q).card ≤ 2^K)
    (h_nonempty : ∀ Q ∈ Qset, (C Q).Nonempty)
    (hw_nonneg : ∀ Q ∈ Qset, 0 ≤ w Q) :
    ∃ (k : ℕ) (Qgood : Finset Y) (M_Δ : ℕ) (C_trim : Y → Finset α),
      k ≤ K ∧
      M_Δ = 2^k ∧
      Qgood ⊆ Qset ∧
      (∑ Q ∈ Qgood, w Q) ≥ (∑ Q ∈ Qset, w Q) / (K + 1 : ℝ) ∧
      ∀ Q ∈ Qgood,
        (C_trim Q) ⊆ (C Q) ∧
        (C_trim Q).card = M_Δ ∧
        M_Δ ≤ (C Q).card ∧
        (C Q).card < 2 * M_Δ := by
  let f : Y → ℕ := fun Q => (C Q).card
  have hK' : ∀ Q ∈ Qset, f Q ≤ 2^K := by
    intro Q hQ
    simpa [f] using hK Q hQ
  have h_pos : ∀ Q ∈ Qset, 0 < f Q := by
    intro Q hQ
    have hne : (C Q).Nonempty := h_nonempty Q hQ
    simpa [f, Finset.Nonempty] using Finset.Nonempty.card_pos hne
  rcases weighted_dyadic_pigeonhole_sizes Qset f w K hK' h_pos hw_nonneg with ⟨k, hk_le, hcard⟩
  let Qgood : Finset Y := Qset.filter (fun Q => 2^k ≤ f Q ∧ f Q < 2^(k + 1))
  have hQgood_sub : Qgood ⊆ Qset := Finset.filter_subset _ _
  have hQgood_weight : (∑ Q ∈ Qgood, w Q) ≥ (∑ Q ∈ Qset, w Q) / (K + 1 : ℝ) := hcard
  let M_Δ : ℕ := 2^k
  have hMΔ_pos : 0 < M_Δ := by positivity
  have h_bounds : ∀ Q ∈ Qgood, M_Δ ≤ (C Q).card ∧ (C Q).card < 2 * M_Δ := by
    intro Q hQ
    have h1 : 2^k ≤ f Q ∧ f Q < 2^(k + 1) := (Finset.mem_filter.mp hQ).2
    have h2 : M_Δ ≤ (C Q).card := by
      simpa [M_Δ, f] using h1.1
    have h3 : (C Q).card < 2 * M_Δ := by
      have h4 : f Q < 2^(k + 1) := h1.2
      have h5 : 2^(k + 1) = 2 * M_Δ := by
        simp [M_Δ, pow_succ] <;> ring
      rw [h5] at h4
      simpa [f] using h4
    exact ⟨h2, h3⟩
  choose C_trim htrim_sub htrim_card using fun (Q : Y) (hQ : Q ∈ Qgood) =>
    Finset.exists_subset_card_eq (h_bounds Q hQ).1
  refine' ⟨k, Qgood, M_Δ, fun Q => if hQ : Q ∈ Qgood then C_trim Q hQ else ∅,
    hk_le, rfl, hQgood_sub, hQgood_weight, _⟩
  intro Q hQ
  have h4 : C_trim Q hQ ⊆ C Q := htrim_sub Q hQ
  have h5 : (C_trim Q hQ).card = M_Δ := htrim_card Q hQ
  have h6 : (fun Q => if hQ : Q ∈ Qgood then C_trim Q hQ else ∅) Q = C_trim Q hQ := by
    simp [hQ]
  rw [h6]
  exact ⟨h4, h5, (h_bounds Q hQ).1, (h_bounds Q hQ).2⟩

/-- Polynomial bound on K_val: K_val ≤ 2^21 * (2m+11)^6.
    Extracted from polylog_absorption_explicit for use in retention estimates. -/
lemma k_val_polynomial_bound {n m : ℕ} (hnm : m ≤ n) (hm_pos : 1 ≤ m)
    (T₀ : Finset (DyadicTube n))
    (h_bound : ∀ T ∈ T₀, |T.a| ≤ (2^(n+1) : ℤ) ∧ |T.b| ≤ (2^(n+2) : ℤ))
    (K_val : ℝ)
    (hK_val_eq : K_val = (2^21 : ℝ) * ((Nat.log 2 (coarseRange n m hnm T₀).card + 4 : ℕ) : ℝ)^6) :
    K_val ≤ (2^21 : ℝ) * (2 * m + 11 : ℝ)^6 := by
  have hA : ∀ T ∈ T₀, |T.a| ≤ ((2^(n+1) : ℕ) : ℤ) := by
    intro T hT; exact (h_bound T hT).1
  have hB : ∀ T ∈ T₀, |T.b| ≤ ((2^(n+2) : ℕ) : ℤ) := by
    intro T hT; exact (h_bound T hT).2
  have h_card_bound : (coarseRange n m hnm T₀).card ≤
      (2 * ((2^(n+1) : ℕ) / refinementFactor n m) + 3) *
      (2 * ((2^(n+2) : ℕ) / refinementFactor n m) + 3) :=
    coarseRange_card_bound hnm hA hB
  have h_rf : refinementFactor n m = 2^(n - m) := by
    simp [refinementFactor, hnm] <;> omega
  have h_div1 : (2^(n+1) : ℕ) / refinementFactor n m = 2^(m + 1) := by
    rw [h_rf]
    have h_eq : 2^(n + 1) = 2^(n - m) * 2^(m + 1) := by
      have h : n - m + (m + 1) = n + 1 := by omega
      rw [← Nat.pow_add, h]
    rw [h_eq, Nat.mul_div_cancel_left] <;> positivity
  have h_div2 : (2^(n+2) : ℕ) / refinementFactor n m = 2^(m + 2) := by
    rw [h_rf]
    have h_eq : 2^(n + 2) = 2^(n - m) * 2^(m + 2) := by
      have h : n - m + (m + 2) = n + 2 := by omega
      rw [← Nat.pow_add, h]
    rw [h_eq, Nat.mul_div_cancel_left] <;> positivity
  rw [h_div1, h_div2] at h_card_bound
  have h3_le_pow2 : ∀ k : ℕ, k ≥ 3 → 3 ≤ 2^k := by
    intro k hk
    induction' hk with k hk ih
    · norm_num
    · simp [pow_succ] at * <;> omega
  have h_log_bound : Nat.log 2 (coarseRange n m hnm T₀).card ≤ 2 * m + 7 := by
    have h9 : (coarseRange n m hnm T₀).card ≤ (2 * 2^(m + 1) + 3) * (2 * 2^(m + 2) + 3) := h_card_bound
    have h10 : (2 * 2^(m + 1) + 3) * (2 * 2^(m + 2) + 3) ≤ 2^(2 * m + 7) := by
      have h11 : 2 * 2^(m + 1) + 3 ≤ 2^(m + 3) := by
        have h12 : 2 * 2^(m + 1) = 2^(m + 2) := by ring
        rw [h12]
        have h13 : 3 ≤ 2^(m + 2) := h3_le_pow2 (m + 2) (by omega)
        have h14 : 2^(m + 3) = 2^(m + 2) + 2^(m + 2) := by
          have h15 : 2^(m + 3) = 2 * 2^(m + 2) := by ring
          rw [h15] <;> ring
        rw [h14] <;> linarith
      have h12 : 2 * 2^(m + 2) + 3 ≤ 2^(m + 4) := by
        have h13 : 2 * 2^(m + 2) = 2^(m + 3) := by ring
        rw [h13]
        have h14 : 3 ≤ 2^(m + 3) := h3_le_pow2 (m + 3) (by omega)
        have h15 : 2^(m + 4) = 2^(m + 3) + 2^(m + 3) := by
          have h16 : 2^(m + 4) = 2 * 2^(m + 3) := by ring
          rw [h16] <;> ring
        rw [h15] <;> linarith
      calc (2 * 2^(m + 1) + 3) * (2 * 2^(m + 2) + 3)
        ≤ 2^(m + 3) * 2^(m + 4) := by gcongr
      _ = 2^(2 * m + 7) := by
        rw [← Nat.pow_add] <;> ring
    have h11 : (coarseRange n m hnm T₀).card ≤ 2^(2 * m + 7) := le_trans h9 h10
    have h12 : Nat.log 2 (coarseRange n m hnm T₀).card ≤ Nat.log 2 (2^(2 * m + 7)) :=
      Nat.log_mono_right h11
    have h13 : Nat.log 2 (2^(2 * m + 7)) = 2 * m + 7 := by
      rw [Nat.log_pow] <;> simp
    rw [h13] at h12
    exact h12
  have h14 : ((Nat.log 2 (coarseRange n m hnm T₀).card + 4 : ℕ) : ℝ) ≤ (2 * m + 11 : ℝ) := by
    exact_mod_cast (by linarith)
  rw [hK_val_eq]
  have h15 : (2^21 : ℝ) * ((Nat.log 2 (coarseRange n m hnm T₀).card + 4 : ℕ) : ℝ)^6 ≤
      (2^21 : ℝ) * (2 * m + 11 : ℝ)^6 := by
    gcongr
    <;> linarith
  exact h15

/-- Helper: for all m ≥ 1, `2^22 * (2m+11)^7 ≤ (m+1)^100`. -/
lemma polynomial_majorization (m : ℕ) (hm : 1 ≤ m) :
    (2^22 : ℝ) * (2 * (m : ℝ) + 11)^7 ≤ ((m : ℝ) + 1)^100 := by
  by_cases h : m ≤ 3
  · interval_cases m <;> norm_num
  · have h4 : m ≥ 4 := by omega
    have h4' : (m : ℝ) ≥ 4 := by exact_mod_cast h4
    have hsq : 2 * (m : ℝ) + 11 ≤ ((m : ℝ) + 1)^2 := by
      nlinarith [sq_nonneg ((m : ℝ) - 4)]
    have h7 : (2 * (m : ℝ) + 11)^7 ≤ (((m : ℝ) + 1)^2)^7 := by
      gcongr <;> linarith
    have h7' : (((m : ℝ) + 1)^2)^7 = ((m : ℝ) + 1)^14 := by ring
    have h8 : (2^22 : ℝ) ≤ ((m : ℝ) + 1)^86 := by
      have h9 : (m : ℝ) + 1 ≥ 2 := by linarith
      have h10 : ((m : ℝ) + 1)^86 ≥ (2 : ℝ)^86 := by gcongr
      have h11 : (2 : ℝ)^86 ≥ (2^22 : ℝ) := by
        have h12 : (86 : ℕ) ≥ 22 := by norm_num
        have h13 : (2 : ℝ)^86 ≥ (2 : ℝ)^22 := by
          have h14 : (2 : ℝ)^86 = (2 : ℝ)^22 * (2 : ℝ)^64 := by
            rw [← pow_add] <;> norm_num
          rw [h14]
          have h15 : (2 : ℝ)^64 ≥ 1 := by norm_num
          nlinarith
        simpa using h13
      linarith
    calc (2^22 : ℝ) * (2 * (m : ℝ) + 11)^7
      ≤ (2^22 : ℝ) * (((m : ℝ) + 1)^2)^7 := by gcongr
    _ = (2^22 : ℝ) * ((m : ℝ) + 1)^14 := by rw [h7']
    _ ≤ ((m : ℝ) + 1)^86 * ((m : ℝ) + 1)^14 := by gcongr
    _ = ((m : ℝ) + 1)^100 := by ring

/-- Retention absorption: after uniformization, the total loss
    `2 * K_val * (K_bound + 1)` is absorbed by the induction gap `(n-m+1)^100`.

    Given `2m ≤ n`, `K_val ≈ m^6`, and `K_bound ≈ 2m`, the RHS is degree 7
    in m while the LHS is degree 100 in `n-m ≥ m`. -/
lemma retention_absorption {n m : ℕ} (hnm : m ≤ n) (h_ratio : 2 * m ≤ n)
    (hm_pos : 1 ≤ m)
    (T₀ : Finset (DyadicTube n))
    (h_bound : ∀ T ∈ T₀, |T.a| ≤ (2^(n+1) : ℤ) ∧ |T.b| ≤ (2^(n+2) : ℤ))
    (K_val : ℝ)
    (hK_val_eq : K_val = (2^21 : ℝ) * ((Nat.log 2 (coarseRange n m hnm T₀).card + 4 : ℕ) : ℝ)^6)
    (K_bound : ℕ) (hK_bound : K_bound ≤ 2 * m + 10) :
    2 * K_val * ((K_bound : ℝ) + 1) ≤ ((n - m + 1 : ℝ)^100) := by
  have hK_val_le : K_val ≤ (2^21 : ℝ) * ((2 * m + 11 : ℝ)^6) :=
    k_val_polynomial_bound hnm hm_pos T₀ h_bound K_val hK_val_eq
  have hKb : (K_bound : ℝ) + 1 ≤ (2 * m + 11 : ℝ) := by
    have h1 : (K_bound : ℝ) ≤ (2 * m + 10 : ℝ) := by exact_mod_cast hK_bound
    linarith
  have h_main : 2 * K_val * ((K_bound : ℝ) + 1) ≤
      (2^22 : ℝ) * (2 * m + 11 : ℝ)^7 := by
    calc 2 * K_val * ((K_bound : ℝ) + 1)
      ≤ 2 * ((2^21 : ℝ) * (2 * m + 11 : ℝ)^6) * ((K_bound : ℝ) + 1) := by gcongr
    _ ≤ 2 * ((2^21 : ℝ) * (2 * m + 11 : ℝ)^6) * (2 * m + 11 : ℝ) := by gcongr
    _ = (2^22 : ℝ) * (2 * m + 11 : ℝ)^7 := by ring
  have h1 : n - m + 1 ≥ m + 1 := by omega
  have h2 : ((n - m + 1 : ℝ)^100) ≥ ((m + 1 : ℝ)^100) := by
    have h21 : (n - m + 1 : ℝ) ≥ (m + 1 : ℝ) := by exact_mod_cast h1
    gcongr
  have h3 : (2^22 : ℝ) * (2 * m + 11 : ℝ)^7 ≤ ((m + 1 : ℝ)^100) :=
    polynomial_majorization m hm_pos
  calc 2 * K_val * ((K_bound : ℝ) + 1)
    ≤ (2^22 : ℝ) * (2 * m + 11 : ℝ)^7 := h_main
  _ ≤ ((m + 1 : ℝ)^100) := h3
  _ ≤ ((n - m + 1 : ℝ)^100) := h2

/-- Bound: `4 * K_val ≤ (n-m+1)^100`. -/
lemma four_kval_absorption
    {n m : ℕ} (hnm : m ≤ n) (h_ratio : 2 * m ≤ n) (hm_pos : 1 ≤ m)
    (T₀ : Finset (DyadicTube n))
    (h_bound : ∀ T ∈ T₀, |T.a| ≤ (2^(n+1) : ℤ) ∧ |T.b| ≤ (2^(n+2) : ℤ))
    (K_val : ℝ)
    (hK_val_eq : K_val = (2^21 : ℝ) * ((Nat.log 2 (coarseRange n m hnm T₀).card + 4 : ℕ) : ℝ)^6) :
    4 * K_val ≤ ((n - m + 1 : ℝ)^100) := by
  have hK_val_le : K_val ≤ (2^21 : ℝ) * ((2 * m + 11 : ℝ)^6) :=
    k_val_polynomial_bound hnm hm_pos T₀ h_bound K_val hK_val_eq
  have h1 : 4 * K_val ≤ (2^22 : ℝ) * ((2 * m + 11 : ℝ)^7) := by
    have h2 : (2 : ℝ) ≤ (2 * m + 11 : ℝ) := by linarith
    calc 4 * K_val
      ≤ 4 * ((2^21 : ℝ) * (2 * m + 11 : ℝ)^6) := by gcongr
    _ = (2^23 : ℝ) * (2 * m + 11 : ℝ)^6 := by ring
    _ = (2^22 : ℝ) * (2 * (2 * m + 11 : ℝ)^6) := by ring
    _ ≤ (2^22 : ℝ) * ((2 * m + 11 : ℝ) * (2 * m + 11 : ℝ)^6) := by gcongr
    _ = (2^22 : ℝ) * (2 * m + 11 : ℝ)^7 := by ring
  have h3 : (2^22 : ℝ) * (2 * m + 11 : ℝ)^7 ≤ ((m : ℝ) + 1)^100 :=
    polynomial_majorization m hm_pos
  have h4 : n - m + 1 ≥ m + 1 := by omega
  have h5 : ((n - m + 1 : ℝ)^100) ≥ ((m + 1 : ℝ)^100) := by
    have h51 : (n - m + 1 : ℝ) ≥ (m + 1 : ℝ) := by exact_mod_cast h4
    gcongr
  calc 4 * K_val
    ≤ (2^22 : ℝ) * (2 * m + 11 : ℝ)^7 := h1
  _ ≤ ((m + 1 : ℝ)^100) := h3
  _ ≤ ((n - m + 1 : ℝ)^100) := h5

/-- Construct polylog absorption factor K = A_final * (1 + log(1/δ_n))^A_final
    large enough to simultaneously absorb:
    - C₂ constant blowup (10*C₂ ≤ C₁*K)
    - K_val loss (2*K_val ≤ K)
    - induction gap (K ≥ (n-m+1)^100)
    - old-scale polylog (A * (1+log(1/δ_m))^A ≤ K)

    Returns A_final, K, and all required bounds. -/
lemma choose_polylog_factor
    {n m : ℕ} (hnm : m ≤ n) (h_ratio : 2 * m ≤ n) (hm_pos : 1 ≤ m)
    (A C₁ C₂ K_val : ℝ) (hA_one : 1 ≤ A) (hC₁pos : 0 < C₁)
    (hC₂_ge1 : 1 ≤ C₂) (hK_val_ge1 : 1 ≤ K_val)
    (hK_val_le_old : K_val ≤ A * Real.rpow (1 + Real.log (1 / dyadicDelta m)) A)
    (T₀ : Finset (DyadicTube n))
    (h_bound : ∀ T ∈ T₀, |T.a| ≤ (2^(n+1) : ℤ) ∧ |T.b| ≤ (2^(n+2) : ℤ))
    (hK_val_exact : K_val = (2^21 : ℝ) * ((Nat.log 2 (coarseRange n m hnm T₀).card + 4 : ℕ) : ℝ)^6) :
    ∃ (A_final K : ℝ),
      1 ≤ A_final ∧
      A ≤ A_final ∧
      K = A_final * Real.rpow (1 + Real.log (1 / dyadicDelta n)) A_final ∧
      1 ≤ K ∧
      A * Real.rpow (1 + Real.log (1 / dyadicDelta m)) A ≤ K ∧
      K_val ≤ K ∧
      2 * K_val ≤ K ∧
      K ≥ (n - m + 1 : ℝ)^100 ∧
      10 * C₂ ≤ C₁ * K := by
  have h_n_pos : 1 ≤ n := by linarith
  let b : ℝ := 1 + Real.log (1 / dyadicDelta n)
  have hb_gt_one : 1 < b := by
    have hδ_lt_one : dyadicDelta n < 1 := by
      have h1 : dyadicDelta n = 1 / (2 : ℝ)^n := by simp [dyadicDelta] <;> ring
      rw [h1]
      have h2 : (2 : ℝ)^n ≥ 2 := by
        have h3 : (2 : ℝ)^n ≥ (2 : ℝ)^1 := by gcongr <;> norm_num
        linarith
      have h4 : 0 < (2 : ℝ)^n := by positivity
      have h5 : 1 / (2 : ℝ)^n < 1 := by
        apply (div_lt_one h4).mpr; linarith
      exact h5
    have h_log_pos : 0 < Real.log (1 / dyadicDelta n) := by
      have h6 : 1 < 1 / dyadicDelta n := by
        have h7 : 0 < dyadicDelta n := dyadicDelta_pos n
        exact one_lt_one_div h7 hδ_lt_one
      exact Real.log_pos h6
    dsimp only [b]; linarith
  let X : ℝ := max (max (10 * C₂ / C₁) (2 * K_val)) ((n - m + 1 : ℝ)^100)
  have hX_pos : 0 < X := by positivity
  have h_bernoulli : ∀ (k : ℕ), b ^ k ≥ 1 + (k : ℝ) * (b - 1) := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
      calc b ^ (k + 1)
        = b * b ^ k := by ring
      _ ≥ b * (1 + (k : ℝ) * (b - 1)) := by gcongr
      _ ≥ 1 + ((k + 1 : ℕ) : ℝ) * (b - 1) := by
        have h10 : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by simp
        rw [h10]
        have h11 : 0 ≤ (k : ℝ) := by positivity
        have h12 : 0 < b - 1 := by linarith
        have h13 : 0 ≤ (b - 1) * ((k : ℝ) * (b - 1)) := by positivity
        have h14 : b * (1 + (k : ℝ) * (b - 1)) - (1 + ((k : ℝ) + 1) * (b - 1)) = (b - 1) * ((k : ℝ) * (b - 1)) := by ring
        linarith
  have h_exists : ∃ (k : ℕ), 1 + (k : ℝ) * (b - 1) ≥ X := by
    have hb_sub : 0 < b - 1 := by linarith
    obtain ⟨k, hk⟩ := exists_nat_ge ((X - 1) / (b - 1))
    refine ⟨k, ?_⟩
    have h : (k : ℝ) ≥ (X - 1) / (b - 1) := by exact_mod_cast hk
    have h_goal : 1 + (k : ℝ) * (b - 1) ≥ X := by
      have h9 : (k : ℝ) * (b - 1) ≥ X - 1 := by
        calc (k : ℝ) * (b - 1)
          ≥ ((X - 1) / (b - 1)) * (b - 1) := by gcongr
        _ = X - 1 := by field_simp [hb_sub.ne'] <;> ring
      linarith
    exact h_goal
  rcases h_exists with ⟨k, hk⟩
  have hbk : b ^ k ≥ X := by linarith [h_bernoulli k]
  let A_final : ℝ := max A (k : ℝ)
  have hA_final_ge_A : A ≤ A_final := le_max_left _ _
  have hA_final_ge_k : (k : ℝ) ≤ A_final := le_max_right _ _
  have hA_final_one : 1 ≤ A_final := by linarith [hA_one]
  have h_b_pow : b ^ A_final ≥ X := by
    have h1 : b ^ A_final ≥ b ^ (k : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) hA_final_ge_k
    have h2 : b ^ (k : ℝ) = b ^ k := by norm_cast
    rw [h2] at h1; linarith
  let K : ℝ := A_final * b ^ A_final
  have hK1 : 1 ≤ K := by
    have h4 : 1 ≤ b ^ A_final := by apply Real.one_le_rpow (by linarith) (by linarith)
    have h5 : 0 < A_final := by linarith
    have h6 : 1 ≤ A_final * b ^ A_final := by
      calc 1 = 1 * 1 := by ring
      _ ≤ A_final * b ^ A_final := by exact mul_le_mul hA_final_one h4 (by positivity) (by linarith)
    exact h6
  have hδn_le_δm : dyadicDelta n ≤ dyadicDelta m := by
    have h1 : (2 : ℝ)^m ≤ (2 : ℝ)^n := by
      have h1p : (1 : ℝ) ≤ (2 : ℝ) := by norm_num
      gcongr
      <;> linarith
    have h2 : dyadicDelta n = 1 / (2 : ℝ)^n := by simp [dyadicDelta] <;> rfl
    have h3 : dyadicDelta m = 1 / (2 : ℝ)^m := by simp [dyadicDelta] <;> rfl
    rw [h2, h3]
    gcongr
  have hδm_pos : 0 < dyadicDelta m := dyadicDelta_pos m
  have hδn_pos : 0 < dyadicDelta n := dyadicDelta_pos n
  have h_bm_le_b : 1 + Real.log (1 / dyadicDelta m) ≤ b := by
    dsimp only [b]
    have h11 : 1 / dyadicDelta m ≤ 1 / dyadicDelta n := by
      apply one_div_le_one_div_of_le; exact hδn_pos; exact hδn_le_δm
    have h12 : Real.log (1 / dyadicDelta m) ≤ Real.log (1 / dyadicDelta n) :=
      Real.log_le_log (by positivity) h11
    linarith
  have h_bm_nonneg : 0 ≤ 1 + Real.log (1 / dyadicDelta m) := by
    have h4 : dyadicDelta m ≤ 1 := by
      have h5 : (2 : ℝ)^m ≥ 1 := by
        have h51 : 0 ≤ m := by positivity
        have h52 : (2 : ℝ)^m ≥ (2 : ℝ)^0 := by
          gcongr <;> linarith
        simpa using h52
      have h7 : dyadicDelta m = 1 / (2 : ℝ)^m := by simp [dyadicDelta] <;> ring
      rw [h7]
      have h8 : 0 < (2 : ℝ)^m := by positivity
      exact (div_le_one h8).mpr h5
    have h9 : 0 < dyadicDelta m := hδm_pos
    have h10 : 1 ≤ 1 / dyadicDelta m := by exact (one_le_div h9).mpr h4
    have h11 : 0 ≤ Real.log (1 / dyadicDelta m) := Real.log_nonneg h10
    linarith
  have hK_ge_m : A * Real.rpow (1 + Real.log (1 / dyadicDelta m)) A ≤ K := by
    have h6 : Real.rpow (1 + Real.log (1 / dyadicDelta m)) A ≤ b ^ A_final := by
      calc Real.rpow (1 + Real.log (1 / dyadicDelta m)) A
        ≤ b ^ A := Real.rpow_le_rpow h_bm_nonneg h_bm_le_b (by linarith)
      _ ≤ b ^ A_final := Real.rpow_le_rpow_of_exponent_le (by linarith [hb_gt_one]) hA_final_ge_A
    have hA_le : A ≤ A_final := le_max_left _ _
    have h_rpow_nonneg : 0 ≤ Real.rpow (1 + Real.log (1 / dyadicDelta m)) A := Real.rpow_nonneg (by linarith) A
    have h7 : A * Real.rpow (1 + Real.log (1 / dyadicDelta m)) A ≤ A_final * b ^ A_final := by
      have h_step1 : A * Real.rpow (1 + Real.log (1 / dyadicDelta m)) A ≤
          A_final * Real.rpow (1 + Real.log (1 / dyadicDelta m)) A :=
        mul_le_mul_of_nonneg_right hA_le h_rpow_nonneg
      have hA_final_pos : 0 ≤ A_final := by linarith [hA_final_one]
      have h_step2 : A_final * Real.rpow (1 + Real.log (1 / dyadicDelta m)) A ≤ A_final * b ^ A_final :=
        mul_le_mul_of_nonneg_left h6 hA_final_pos
      exact le_trans h_step1 h_step2
    exact h7
  have hK_val_le_K' : K_val ≤ K := by
    calc K_val
      ≤ A * Real.rpow (1 + Real.log (1 / dyadicDelta m)) A := hK_val_le_old
    _ ≤ K := hK_ge_m
  have hK_ge_2Kval : 2 * K_val ≤ K := by
    have hX1a : 2 * K_val ≤ max (10 * C₂ / C₁) (2 * K_val) := le_max_right _ _
    have hX1b : max (10 * C₂ / C₁) (2 * K_val) ≤ X := le_max_left _ _
    have hX1 : 2 * K_val ≤ X := le_trans hX1a hX1b
    have hX2 : X ≤ K := by
      have h_pos_b : 0 < b ^ A_final := by positivity
      have h_ge : A_final * b ^ A_final ≥ 1 * b ^ A_final :=
        mul_le_mul_of_nonneg_right hA_final_one h_pos_b.le
      calc A_final * b ^ A_final
        ≥ 1 * b ^ A_final := h_ge
      _ = b ^ A_final := by ring
      _ ≥ X := h_b_pow
    exact le_trans hX1 hX2
  have hK_ge_poly : K ≥ (n - m + 1 : ℝ)^100 := by
    have hX1 : ((n - m + 1 : ℝ)^100) ≤ X := by exact le_max_right _ _
    have hX2 : X ≤ K := by
      have h_pos_b : 0 < b ^ A_final := by positivity
      have h_ge : A_final * b ^ A_final ≥ 1 * b ^ A_final :=
        mul_le_mul_of_nonneg_right hA_final_one h_pos_b.le
      calc A_final * b ^ A_final
        ≥ 1 * b ^ A_final := h_ge
      _ = b ^ A_final := by ring
      _ ≥ X := h_b_pow
    exact le_trans hX1 hX2
  have hC2_le : 10 * C₂ ≤ C₁ * K := by
    have h6 : A_final * b ^ A_final ≥ X := by
      have h_pos_b : 0 < b ^ A_final := by positivity
      have h_ge : A_final * b ^ A_final ≥ 1 * b ^ A_final :=
        mul_le_mul_of_nonneg_right hA_final_one h_pos_b.le
      calc A_final * b ^ A_final
        ≥ 1 * b ^ A_final := h_ge
      _ = b ^ A_final := by ring
      _ ≥ X := h_b_pow
    have h7 : C₁ * (A_final * b ^ A_final) ≥ C₁ * X := by gcongr
    have h8 : C₁ * X ≥ 10 * C₂ := by
      have h91 : (10 * C₂ / C₁) ≤ max (10 * C₂ / C₁) (2 * K_val) := le_max_left _ _
      have h92 : max (10 * C₂ / C₁) (2 * K_val) ≤ X := le_max_left _ _
      have h9 : X ≥ 10 * C₂ / C₁ := le_trans h91 h92
      have h10 : C₁ * X ≥ C₁ * (10 * C₂ / C₁) := by gcongr
      have h11 : C₁ * (10 * C₂ / C₁) = 10 * C₂ := by
        field_simp [hC₁pos.ne'] <;> ring
      rw [h11] at h10; exact h10
    have h12 : C₁ * K = C₁ * (A_final * b ^ A_final) := by rfl
    rw [h12]
    exact le_trans h8 h7
  exact ⟨A_final, K, hA_final_one, hA_final_ge_A, rfl, hK1, hK_ge_m, hK_val_le_K', hK_ge_2Kval, hK_ge_poly, hC2_le⟩

/-- Polylogarithmic loss factor depending on scale gap d = n - m.
    (d+1)^100 absorbs all losses from pigeonholing and rescaling. -/
def inductionLossGap (d : ℕ) : ℝ := (d + 1 : ℝ)^100

lemma inductionLossGap_pos (d : ℕ) : 0 < inductionLossGap d := by
  have h : (0 : ℝ) < (d + 1 : ℝ) := by positivity
  exact pow_pos h 100

lemma inductionLossGap_one_le (d : ℕ) : 1 ≤ inductionLossGap d := by
  have h1 : (1 : ℝ) ≤ (d + 1 : ℝ) := by linarith
  have h2 : (1 : ℝ) ≤ (d + 1 : ℝ)^100 := by
    calc (1 : ℝ) = 1^100 := by norm_num
      _ ≤ (d + 1 : ℝ)^100 := by gcongr
  exact h2

/-- Polylog absorption: QTTC loss K_val is bounded by induction loss K.
    Requires scale gap hypothesis (e.g., 2m ≤ n) to ensure K dominates. -/
lemma polylog_absorption
    {n m : ℕ} (hnm : m ≤ n) (h_ratio : 2 * m ≤ n) (hm_pos : 1 ≤ m)
    (T₀ : Finset (DyadicTube n))
    (h_bound : ∀ T ∈ T₀, |T.a| ≤ (2^(n+1) : ℤ) ∧ |T.b| ≤ (2^(n+2) : ℤ))
    (K_val : ℝ)
    (hK_val_eq : K_val = (2^21 : ℝ) * ((Nat.log 2 (coarseRange n m hnm T₀).card + 4 : ℕ) : ℝ)^6) :
    K_val ≤ inductionLossGap (n - m) := by
  have h_main : K_val ≤ (n - m + 1 : ℝ)^100 :=
    polylog_absorption_explicit hnm h_ratio hm_pos T₀ h_bound K_val hK_val_eq
  have h_cast : (n - m + 1 : ℝ) = ↑(n - m) + 1 := by
    have h1 : (n - m + 1 : ℝ) = (n : ℝ) - (m : ℝ) + 1 := by rfl
    rw [h1]
    have h2 : (n : ℝ) - (m : ℝ) = ↑(n - m) := by
      rw [Nat.cast_sub hnm] <;> ring
    rw [h2] <;> ring
  have h_gap : inductionLossGap (n - m) = (n - m + 1 : ℝ)^100 := by
    unfold inductionLossGap
    rw [h_cast]
    <;> rfl
  rw [h_gap]
  exact h_main

/-- Combined polylog absorption for B1 restructuring.
    Absorbs (16/3) * K_val^2 * (2m+8) into inductionLossGap(n-m).
    Used when point threshold and dyadic uniformization are combined. -/
lemma combined_polylog_absorption
    {n m : ℕ} (hnm : m ≤ n) (h_ratio : 2 * m ≤ n) (hm_pos : 1 ≤ m)
    (T₀ : Finset (DyadicTube n))
    (h_bound : ∀ T ∈ T₀, |T.a| ≤ (2^(n+1) : ℤ) ∧ |T.b| ≤ (2^(n+2) : ℤ))
    (K_val : ℝ)
    (hK_val_eq : K_val = (2^21 : ℝ) * ((Nat.log 2 (coarseRange n m hnm T₀).card + 4 : ℕ) : ℝ)^6) :
    (16 / 3 : ℝ) * K_val^2 * (2 * (m : ℝ) + 8) ≤ inductionLossGap (n - m) := by
  have h1 : K_val ≤ (2^21 : ℝ) * (2 * (m : ℝ) + 11)^6 :=
    k_val_polynomial_bound hnm hm_pos T₀ h_bound K_val hK_val_eq
  have hm1 : (m : ℝ) ≥ 1 := by exact_mod_cast hm_pos
  have h2 : (2 * (m : ℝ) + 11) ≤ (13 / 2 : ℝ) * ((m : ℝ) + 1) := by linarith
  have h3 : (2 * (m : ℝ) + 8) ≤ 5 * ((m : ℝ) + 1) := by linarith
  have hKval_nonneg : 0 ≤ K_val := by
    rw [hK_val_eq] <;> positivity
  have h41 : K_val^2 ≤ ((2^21 : ℝ) * (2 * (m : ℝ) + 11)^6)^2 := by
    have h : K_val ≤ (2^21 : ℝ) * (2 * (m : ℝ) + 11)^6 := h1
    have hpos : 0 ≤ (2^21 : ℝ) * (2 * (m : ℝ) + 11)^6 := by positivity
    nlinarith
  have h42 : (2 * (m : ℝ) + 8) ≤ 5 * ((m : ℝ) + 1) := h3
  have h4 : (16 / 3 : ℝ) * K_val^2 * (2 * (m : ℝ) + 8) ≤
      (80 / 3 : ℝ) * (2 : ℝ)^30 * (13 : ℝ)^12 * ((m : ℝ) + 1)^13 := by
    have h43 : (16 / 3 : ℝ) * K_val^2 * (2 * (m : ℝ) + 8) ≤
        (16 / 3 : ℝ) * ((2^21 : ℝ) * (2 * (m : ℝ) + 11)^6)^2 * (5 * ((m : ℝ) + 1)) := by
      gcongr <;> linarith
    have h44 : (16 / 3 : ℝ) * ((2^21 : ℝ) * (2 * (m : ℝ) + 11)^6)^2 * (5 * ((m : ℝ) + 1)) =
        (16 / 3 : ℝ) * (2 : ℝ)^42 * (2 * (m : ℝ) + 11)^12 * (5 * ((m : ℝ) + 1)) := by ring
    have h45 : (2 * (m : ℝ) + 11)^12 ≤ (((13 / 2 : ℝ) * ((m : ℝ) + 1))^12) := by
      gcongr <;> linarith
    calc (16 / 3 : ℝ) * K_val^2 * (2 * (m : ℝ) + 8)
      ≤ (16 / 3 : ℝ) * ((2^21 : ℝ) * (2 * (m : ℝ) + 11)^6)^2 * (5 * ((m : ℝ) + 1)) := h43
    _ = (16 / 3 : ℝ) * (2 : ℝ)^42 * (2 * (m : ℝ) + 11)^12 * (5 * ((m : ℝ) + 1)) := h44
    _ ≤ (16 / 3 : ℝ) * (2 : ℝ)^42 * (((13 / 2 : ℝ) * ((m : ℝ) + 1))^12) * (5 * ((m : ℝ) + 1)) := by gcongr
    _ = (80 / 3 : ℝ) * (2 : ℝ)^30 * (13 : ℝ)^12 * ((m : ℝ) + 1)^13 := by ring
  have h5 : (80 / 3 : ℝ) * (13 : ℝ)^12 ≤ (2 : ℝ)^57 := by norm_num
  have h6 : (80 / 3 : ℝ) * (2 : ℝ)^30 * (13 : ℝ)^12 ≤ (2 : ℝ)^87 := by
    calc (80 / 3 : ℝ) * (2 : ℝ)^30 * (13 : ℝ)^12
      = (2 : ℝ)^30 * ((80 / 3 : ℝ) * (13 : ℝ)^12) := by ring
    _ ≤ (2 : ℝ)^30 * (2 : ℝ)^57 := by gcongr
    _ = (2 : ℝ)^87 := by ring
  have h7 : ((m : ℝ) + 1) ≥ 2 := by linarith
  have h8 : (2 : ℝ)^87 ≤ (((m : ℝ) + 1)^87) := by
    gcongr <;> linarith
  have h9 : (80 / 3 : ℝ) * (2 : ℝ)^30 * (13 : ℝ)^12 * ((m : ℝ) + 1)^13 ≤ ((m : ℝ) + 1)^100 := by
    calc (80 / 3 : ℝ) * (2 : ℝ)^30 * (13 : ℝ)^12 * ((m : ℝ) + 1)^13
      ≤ (2 : ℝ)^87 * ((m : ℝ) + 1)^13 := by gcongr
    _ ≤ (((m : ℝ) + 1)^87) * ((m : ℝ) + 1)^13 := by gcongr
    _ = ((m : ℝ) + 1)^100 := by ring
  have h10 : ((n : ℝ) - (m : ℝ) + 1) ≥ ((m : ℝ) + 1) := by
    have h11 : (n : ℝ) ≥ 2 * (m : ℝ) := by exact_mod_cast h_ratio
    linarith
  have h11 : (16 / 3 : ℝ) * K_val^2 * (2 * (m : ℝ) + 8) ≤ (((n : ℝ) - (m : ℝ) + 1)^100) := by
    calc (16 / 3 : ℝ) * K_val^2 * (2 * (m : ℝ) + 8)
      ≤ (80 / 3 : ℝ) * (2 : ℝ)^30 * (13 : ℝ)^12 * ((m : ℝ) + 1)^13 := h4
    _ ≤ ((m : ℝ) + 1)^100 := h9
    _ ≤ (((n : ℝ) - (m : ℝ) + 1)^100) := by gcongr <;> linarith
  have h_cast2 : (n - m + 1 : ℝ) = ↑(n - m) + 1 := by
    have h1 : (n - m + 1 : ℝ) = (n : ℝ) - (m : ℝ) + 1 := by rfl
    rw [h1]
    have h2 : (n : ℝ) - (m : ℝ) = ↑(n - m) := by
      rw [Nat.cast_sub hnm] <;> ring
    rw [h2] <;> ring
  have h_gap2 : inductionLossGap (n - m) = (n - m + 1 : ℝ)^100 := by
    unfold inductionLossGap
    rw [h_cast2] <;> rfl
  rw [h_gap2]
  simpa [h_cast2] using h11

/-- Wrapper for C2_absorption using inductionLossGap. -/
lemma C2_absorption_gap
    {n m : ℕ} (hnm : m ≤ n) (h_ratio : 2 * m ≤ n) (hm_pos : 1 ≤ m)
    (T₀ : Finset (DyadicTube n))
    (h_bound : ∀ T ∈ T₀, |T.a| ≤ (2^(n+1) : ℤ) ∧ |T.b| ≤ (2^(n+2) : ℤ))
    (s C₁ : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) (hC1 : 1 ≤ C₁)
    (C₂ : ℝ)
    (hC2_eq : C₂ = 1024 * Real.rpow 2 (s + 2) * (max 1 (25 * C₁)) *
        ((Nat.log 2 (coarseRange n m hnm T₀).card + 4 : ℕ) : ℝ)^2) :
    C₂ ≤ C₁ * inductionLossGap (n - m) := by
  have h_main : C₂ ≤ C₁ * (n - m + 1 : ℝ)^100 :=
    C2_absorption hnm h_ratio hm_pos T₀ h_bound s C₁ hs hs1 hC1 C₂ hC2_eq
  have h_cast : (n - m + 1 : ℝ) = ↑(n - m) + 1 := by
    have h1 : (n - m + 1 : ℝ) = (n : ℝ) - (m : ℝ) + 1 := by rfl
    rw [h1]
    have h2 : (n : ℝ) - (m : ℝ) = ↑(n - m) := by
      rw [Nat.cast_sub hnm] <;> ring
    rw [h2] <;> ring
  have h_gap : inductionLossGap (n - m) = (n - m + 1 : ℝ)^100 := by
    unfold inductionLossGap
    rw [h_cast] <;> rfl
  rw [h_gap]
  exact h_main

/-- squareContained p Q iff containingSquare p = Q. -/
lemma squareContained_iff_containingSquare
    {n m : ℕ} (hnm : m ≤ n) (p : DyadicSquare n) (Q : DyadicSquare m) :
    InductionConfigurations.squareContained hnm p Q ↔
    InductionConfigurations.containingSquare hnm p = Q := by
  let k : ℕ := InductionConfigurations.refinementFactor n m
  have hk_pos : 0 < k := by
    have h : k = 2^(n-m) := by rfl
    rw [h]
    exact pow_pos (by norm_num) (n-m)
  have h_iff1 : InductionConfigurations.squareContained hnm p Q ↔
      (p.i / (k : ℤ) = Q.i ∧ p.j / (k : ℤ) = Q.j) := by
    simp [InductionConfigurations.squareContained, InductionConfigurations.int_ediv_iff, hk_pos]
    <;> aesop
  have h_iff2 : InductionConfigurations.containingSquare hnm p = Q ↔
      (p.i / (k : ℤ) = Q.i ∧ p.j / (k : ℤ) = Q.j) := by
    simp only [InductionConfigurations.containingSquare]
    constructor
    · intro h
      exact ⟨congr_arg (fun x : DyadicSquare m => x.i) h,
               congr_arg (fun x : DyadicSquare m => x.j) h⟩
    · rintro ⟨hi, hj⟩
      have h : (⟨p.i / (k : ℤ), p.j / (k : ℤ)⟩ : DyadicSquare m) = Q := by
        congr
      exact h
  rw [h_iff1, h_iff2]

/-- Card of filter by image predicate equals sum of fiber cards. -/
lemma card_filter_by_image {α β : Type*} [DecidableEq β]
    (S : Finset α) (f : α → β) (Q : Finset β) :
    (S.filter (fun x => f x ∈ Q)).card =
      ∑ y ∈ Q, (S.filter (fun x => f x = y)).card := by
  have h_disj : ∀ y ∈ Q, ∀ z ∈ Q, y ≠ z →
      Disjoint (S.filter (fun x => f x = y)) (S.filter (fun x => f x = z)) := by
    intro y _ z _ hyz
    simp only [Finset.disjoint_left, Finset.mem_filter]
    intro x hx1 hx2
    have h1 : f x = y := hx1.2
    have h2 : f x = z := hx2.2
    rw [h1] at h2
    exact hyz h2
  have h_union : S.filter (fun x => f x ∈ Q) =
      Q.biUnion (fun y => S.filter (fun x => f x = y)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_biUnion]
    constructor
    · rintro ⟨hx, hfx⟩
      exact ⟨f x, hfx, ⟨hx, rfl⟩⟩
    · rintro ⟨y, hy, ⟨hx, rfl⟩⟩
      exact ⟨hx, hy⟩
  rw [h_union, Finset.card_biUnion h_disj]

/-- Bound: 2 * K_val ≤ inductionLossGap (n - m). -/
lemma two_k_val_le_K
    {n m : ℕ} (hnm : m ≤ n) (h_ratio : 2 * m ≤ n) (hm_pos : 1 ≤ m)
    (T₀ : Finset (DyadicTube n))
    (h_bound : ∀ T ∈ T₀, |T.a| ≤ (2^(n+1) : ℤ) ∧ |T.b| ≤ (2^(n+2) : ℤ))
    (K_val : ℝ)
    (hK_val_exact : K_val = (2^21 : ℝ) * ((Nat.log 2 (coarseRange n m hnm T₀).card + 4 : ℕ) : ℝ)^6) :
    2 * K_val ≤ inductionLossGap (n - m) := by
  have h1 : K_val ≤ (2^21 : ℝ) * (2 * (m : ℝ) + 11)^6 :=
    k_val_polynomial_bound hnm hm_pos T₀ h_bound K_val hK_val_exact
  have h2 : (2 * (m : ℝ) + 11) ≥ 1 := by linarith
  have h3 : (2 * (m : ℝ) + 11)^6 ≤ (2 * (m : ℝ) + 11)^7 := by
    gcongr <;> linarith
  have h4 : 2 * K_val ≤ (2^22 : ℝ) * (2 * (m : ℝ) + 11)^7 := by
    calc 2 * K_val
      ≤ 2 * ((2^21 : ℝ) * (2 * (m : ℝ) + 11)^6) := by gcongr
    _ = (2^22 : ℝ) * (2 * (m : ℝ) + 11)^6 := by ring
    _ ≤ (2^22 : ℝ) * (2 * (m : ℝ) + 11)^7 := by gcongr
  have h5 : (2^22 : ℝ) * (2 * (m : ℝ) + 11)^7 ≤ ((m : ℝ) + 1)^100 :=
    polynomial_majorization m hm_pos
  have h61 : (n - m + 1 : ℕ) ≥ m + 1 := by omega
  have h72 : ((n - m + 1 : ℝ)) ≥ ((m + 1 : ℝ)) := by exact_mod_cast h61
  have h7 : ((n - m + 1 : ℝ)^100) ≥ ((m : ℝ) + 1)^100 := by gcongr
  have h_cast : (↑(n - m) : ℝ) = ↑n - ↑m := by exact Nat.cast_sub hnm
  have h8 : inductionLossGap (n - m) = (↑n - ↑m + 1 : ℝ)^100 := by
    unfold inductionLossGap
    <;> rw [h_cast] <;> ring
  rw [h8]
  exact le_trans h4 (le_trans h5 h7)

/-- Per-Q thinning: from global retention to uniform per-coarse-square retention.

  Given P' ⊆ P₀ with |P₀| ≤ Kv * |P'|, and 2*Kv ≤ K,
  there exists P_new ⊆ P' such that:
  - |P_new| ≥ |P₀| / K
  - For every Q in P_new.image(containingSquare),
    |P_new ∩ Q| ≥ |P₀ ∩ Q| / K
-/
lemma per_Q_thinning
    {n m : ℕ} (hnm : m ≤ n)
    (K Kv : ℝ) (hK_one : 1 ≤ K) (hKv_pos : 0 < Kv)
    (h2K : 2 * Kv ≤ K)
    (P₀ P' : Finset (DyadicSquare n))
    (hP'_sub : P' ⊆ P₀)
    (hP'_loss : (P₀.card : ℝ) ≤ Kv * (P'.card : ℝ)) :
    ∃ (P_new : Finset (DyadicSquare n)),
      P_new ⊆ P' ∧
      (P_new.card : ℝ) ≥ (P₀.card : ℝ) / K ∧
      (∀ Q ∈ P_new.image (InductionConfigurations.containingSquare hnm),
        ((P_new.filter (fun p => InductionConfigurations.squareContained hnm p Q)).card : ℝ) ≥
        ((P₀.filter (fun p => InductionConfigurations.squareContained hnm p Q)).card : ℝ) / K) := by
  let f := InductionConfigurations.containingSquare hnm
  let R := fun (p : DyadicSquare n) (Q : DyadicSquare m) =>
    InductionConfigurations.squareContained hnm p Q
  have hR_iff : ∀ (p : DyadicSquare n) (Q : DyadicSquare m), R p Q ↔ f p = Q :=
    fun p Q => squareContained_iff_containingSquare hnm p Q

  let Qgood := (P'.image f).filter (fun Q =>
    ((P'.filter (fun p => R p Q)).card : ℝ) ≥ ((P₀.filter (fun p => R p Q)).card : ℝ) / K)
  let P_new := P'.filter (fun p => f p ∈ Qgood)

  have h1 : P_new ⊆ P' := Finset.filter_subset _ _

  have h_filter_R : ∀ (S : Finset (DyadicSquare n)) (Q : DyadicSquare m),
      S.filter (fun p => R p Q) = S.filter (fun p => f p = Q) := by
    intro S Q
    ext p
    simp only [Finset.mem_filter]
    <;> rw [hR_iff p Q]

  have h_image : P_new.image f = Qgood := by
    ext Q
    constructor
    · intro h
      rcases Finset.mem_image.mp h with ⟨p, hp_new, rfl⟩
      exact (Finset.mem_filter.mp hp_new).2
    · intro hQ
      have hQ' := Finset.mem_filter.mp hQ
      rcases Finset.mem_image.mp hQ'.1 with ⟨p, hp', rfl⟩
      have hP_new : p ∈ P_new := Finset.mem_filter.mpr ⟨hp', hQ⟩
      exact Finset.mem_image.mpr ⟨p, hP_new, rfl⟩

  have h_per_Q : ∀ Q ∈ Qgood,
      ((P_new.filter (fun p => R p Q)).card : ℝ) ≥
      ((P₀.filter (fun p => R p Q)).card : ℝ) / K := by
    intro Q hQ
    have hQ' := Finset.mem_filter.mp hQ
    have hQ_cond : ((P'.filter (fun p => R p Q)).card : ℝ) ≥
        ((P₀.filter (fun p => R p Q)).card : ℝ) / K := hQ'.2
    have h_eq : P_new.filter (fun p => R p Q) = P'.filter (fun p => R p Q) := by
      ext p
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hp_new, hR⟩
        have hp' : p ∈ P' := (Finset.mem_filter.mp hp_new).1
        exact ⟨hp', hR⟩
      · rintro ⟨hp', hR⟩
        have hfp : f p = Q := (hR_iff p Q).mp hR
        have hQgood : f p ∈ Qgood := by rw [hfp]; exact hQ
        have hp_new : p ∈ P_new := Finset.mem_filter.mpr ⟨hp', hQgood⟩
        exact ⟨hp_new, hR⟩
    rw [h_eq]
    exact hQ_cond

  let Q_bad := (P'.image f) \ Qgood
  let P_bad := P'.filter (fun p => f p ∈ Q_bad)

  have h_partition : P' = P_new ∪ P_bad := by
    ext p
    have hp'_iff : p ∈ P' ↔ p ∈ P_new ∪ P_bad := by
      constructor
      · intro hp'
        by_cases h : f p ∈ Qgood
        · have hP_new : p ∈ P_new := Finset.mem_filter.mpr ⟨hp', h⟩
          exact Finset.mem_union_left P_bad hP_new
        · have hbad : f p ∈ Q_bad := by
            exact Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr ⟨p, hp', rfl⟩, h⟩
          have hP_bad : p ∈ P_bad := Finset.mem_filter.mpr ⟨hp', hbad⟩
          exact Finset.mem_union_right P_new hP_bad
      · intro h
        have h_or : p ∈ P_new ∨ p ∈ P_bad := by
          simpa [Finset.mem_union] using h
        cases h_or with
        | inl hP_new => exact (Finset.mem_filter.mp hP_new).1
        | inr hP_bad => exact (Finset.mem_filter.mp hP_bad).1
    simpa using hp'_iff

  have h_disj : Disjoint P_new P_bad := by
    rw [Finset.disjoint_left]
    intro p h1 h2
    have h3 : f p ∈ Qgood := (Finset.mem_filter.mp h1).2
    have h4 : f p ∈ Q_bad := (Finset.mem_filter.mp h2).2
    have h5 : f p ∉ Qgood := (Finset.mem_sdiff.mp h4).2
    exact h5 h3

  have h_card_union : (P_new ∪ P_bad).card = P_new.card + P_bad.card :=
    Finset.card_union_of_disjoint h_disj

  have h_card_P' : P'.card = P_new.card + P_bad.card := by
    rw [h_partition]
    exact h_card_union

  have h_card_bad : P_bad.card = ∑ Q ∈ Q_bad, (P'.filter (fun p => R p Q)).card := by
    have h : P_bad = P'.filter (fun x => f x ∈ Q_bad) := rfl
    rw [h, card_filter_by_image P' f Q_bad]
    apply Finset.sum_congr rfl
    intro Q _
    rw [h_filter_R P' Q]

  have h_bad_le : ∀ Q ∈ Q_bad,
      ((P'.filter (fun p => R p Q)).card : ℝ) ≤ ((P₀.filter (fun p => R p Q)).card : ℝ) / K := by
    intro Q hQ
    have hQ_in_img : Q ∈ P'.image f := (Finset.mem_sdiff.mp hQ).1
    have hQ_not_good : Q ∉ Qgood := (Finset.mem_sdiff.mp hQ).2
    have h : ¬(((P'.filter (fun p => R p Q)).card : ℝ) ≥ ((P₀.filter (fun p => R p Q)).card : ℝ) / K) := by
      simpa [Qgood, Finset.mem_filter, hQ_in_img] using hQ_not_good
    exact le_of_lt (lt_of_not_ge h)

  have h_sum_bad : (∑ Q ∈ Q_bad, ((P'.filter (fun p => R p Q)).card : ℝ)) ≤
      (∑ Q ∈ Q_bad, ((P₀.filter (fun p => R p Q)).card : ℝ)) / K := by
    have h : ∑ Q ∈ Q_bad, ((P'.filter (fun p => R p Q)).card : ℝ) ≤
        ∑ Q ∈ Q_bad, (((P₀.filter (fun p => R p Q)).card : ℝ) / K) := by
      apply Finset.sum_le_sum
      intro Q hQ
      exact h_bad_le Q hQ
    have h2 : ∑ Q ∈ Q_bad, (((P₀.filter (fun p => R p Q)).card : ℝ) / K) =
        (∑ Q ∈ Q_bad, ((P₀.filter (fun p => R p Q)).card : ℝ)) / K := by
      rw [Finset.sum_div]
    rw [h2] at h
    exact h

  have hQ_bad_sub : Q_bad ⊆ P₀.image f := by
    intro Q hQ
    have hQ_in_img : Q ∈ P'.image f := (Finset.mem_sdiff.mp hQ).1
    rcases Finset.mem_image.mp hQ_in_img with ⟨p, hp', rfl⟩
    have hp0 : p ∈ P₀ := hP'_sub hp'
    exact Finset.mem_image.mpr ⟨p, hp0, rfl⟩

  have h_sum_all : ∑ Q ∈ P₀.image f, (P₀.filter (fun p => R p Q)).card = P₀.card := by
    have h : P₀.filter (fun x => f x ∈ P₀.image f) = P₀ := by
      ext p
      simp only [Finset.mem_filter]
      constructor
      · intro h; exact h.1
      · intro hp
        exact ⟨hp, Finset.mem_image.mpr ⟨p, hp, rfl⟩⟩
    have h2 : (P₀.filter (fun x => f x ∈ P₀.image f)).card = ∑ Q ∈ P₀.image f, (P₀.filter (fun p => f p = Q)).card :=
      card_filter_by_image P₀ f (P₀.image f)
    have h3 : ∑ Q ∈ P₀.image f, (P₀.filter (fun p => R p Q)).card = ∑ Q ∈ P₀.image f, (P₀.filter (fun p => f p = Q)).card := by
      apply Finset.sum_congr rfl
      intro Q _
      rw [h_filter_R P₀ Q]
    rw [h3]
    rw [←h2, h]

  have h_sum_P0 : (∑ Q ∈ Q_bad, ((P₀.filter (fun p => R p Q)).card : ℝ)) ≤ (P₀.card : ℝ) := by
    have h3 : (∑ Q ∈ Q_bad, ((P₀.filter (fun p => R p Q)).card : ℝ)) ≤
        (∑ Q ∈ P₀.image f, ((P₀.filter (fun p => R p Q)).card : ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hQ_bad_sub
      intro Q _ _
      exact_mod_cast Nat.zero_le _
    have h4 : (∑ Q ∈ P₀.image f, ((P₀.filter (fun p => R p Q)).card : ℝ)) = (P₀.card : ℝ) := by
      have h5 : ∑ Q ∈ P₀.image f, (P₀.filter (fun p => R p Q)).card = P₀.card := h_sum_all
      exact_mod_cast h5
    rw [h4] at h3
    exact h3

  have h_P_bad_bound : (P_bad.card : ℝ) ≤ (P₀.card : ℝ) / K := by
    calc (P_bad.card : ℝ)
      = ∑ Q ∈ Q_bad, ((P'.filter (fun p => R p Q)).card : ℝ) := by exact_mod_cast h_card_bad
    _ ≤ (∑ Q ∈ Q_bad, ((P₀.filter (fun p => R p Q)).card : ℝ)) / K := h_sum_bad
    _ ≤ (P₀.card : ℝ) / K := by
      apply div_le_div_of_nonneg_right h_sum_P0
      positivity

  have h9 : (P'.card : ℝ) ≥ (P₀.card : ℝ) / Kv := by
    have h10 : (P₀.card : ℝ) ≤ Kv * (P'.card : ℝ) := hP'_loss
    have h11 : 0 < Kv := hKv_pos
    have h12 : (P₀.card : ℝ) / Kv ≤ (Kv * (P'.card : ℝ)) / Kv := by gcongr
    have h13 : (Kv * (P'.card : ℝ)) / Kv = (P'.card : ℝ) := by
      have h14 : Kv ≠ 0 := h11.ne'
      have h15 : Kv * (P'.card : ℝ) = (P'.card : ℝ) * Kv := by ring
      rw [h15]
      exact mul_div_cancel_right₀ (P'.card : ℝ) h14
    rw [h13] at h12
    exact h12

  have h_inv_ineq : 1 / Kv - 1 / K ≥ 1 / K := by
    have h13 : 0 < Kv := hKv_pos
    have h14 : 0 < K := by linarith
    have h15 : 2 * Kv ≤ K := h2K
    have h16 : 1 / K ≤ 1 / (2 * Kv) := by
      apply one_div_le_one_div_of_le
      <;> linarith
    have h17 : 1 / Kv - 1 / K ≥ 1 / Kv - 1 / (2 * Kv) := by linarith
    have h18 : 1 / Kv - 1 / (2 * Kv) = 1 / (2 * Kv) := by
      have h19 : 1 / Kv = 2 / (2 * Kv) := by
        rw [div_eq_mul_inv, div_eq_mul_inv] <;> ring
      rw [h19] <;> ring
    have h20 : 1 / (2 * Kv) ≥ 1 / K := by
      apply one_div_le_one_div_of_le
      <;> linarith
    linarith

  have h_card_sum : (P_new.card : ℝ) + (P_bad.card : ℝ) = (P'.card : ℝ) := by
    have h : P'.card = P_new.card + P_bad.card := h_card_P'
    have h' : (P'.card : ℝ) = (P_new.card : ℝ) + (P_bad.card : ℝ) := by exact_mod_cast h
    exact h'.symm

  have hP_new_card : (P_new.card : ℝ) ≥ (P₀.card : ℝ) / K := by
    have h12 : (P_new.card : ℝ) ≥ (P'.card : ℝ) - (P_bad.card : ℝ) := by
      linarith [h_card_sum]
    have h13 : (P'.card : ℝ) - (P_bad.card : ℝ) ≥
        (P₀.card : ℝ) / Kv - (P₀.card : ℝ) / K := by
      linarith [h9, h_P_bad_bound]
    have h14 : (P₀.card : ℝ) / Kv - (P₀.card : ℝ) / K ≥ (P₀.card : ℝ) / K := by
      have h15 : 0 ≤ (P₀.card : ℝ) := by exact_mod_cast Nat.zero_le _
      have h16 : (P₀.card : ℝ) / Kv - (P₀.card : ℝ) / K =
          (P₀.card : ℝ) * (1 / Kv - 1 / K) := by
        have h17 : (P₀.card : ℝ) / Kv = (P₀.card : ℝ) * (1 / Kv) := by
          rw [div_eq_mul_inv] <;> ring
        have h18 : (P₀.card : ℝ) / K = (P₀.card : ℝ) * (1 / K) := by
          rw [div_eq_mul_inv] <;> ring
        rw [h17, h18] <;> ring
      rw [h16]
      have h19 : (P₀.card : ℝ) * (1 / Kv - 1 / K) ≥ (P₀.card : ℝ) * (1 / K) := by
        exact mul_le_mul_of_nonneg_left h_inv_ineq h15
      have h20 : (P₀.card : ℝ) * (1 / K) = (P₀.card : ℝ) / K := by
        rw [div_eq_mul_inv] <;> ring
      rw [h20] at h19
      exact h19
    linarith

  refine' ⟨P_new, h1, hP_new_card, _⟩
  rw [h_image]
  exact h_per_Q

end DiscretisedFurstenbergEstimate.InductionOnScales
