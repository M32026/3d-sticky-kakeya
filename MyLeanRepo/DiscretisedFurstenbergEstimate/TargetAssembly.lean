module

/-
  Target theorem assembly (conditional on core_estimate).

  Constructs the function ε : ℝ × ℝ → ℝ required by the target theorem
  using a compact exhaustion of parameterRange and the compact uniformity
  result from CompactUniformity.lean.

  Whiteprint node: final_assembly / target_wiring
  Dependencies: compact_uniformity
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CompactUniformity
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

attribute [local instance] Classical.propDecidable

namespace DirecretisedFurstenbergEstimate.FinalProof

open DirecretisedFurstenbergEstimate

/-- The n-th compact set in the exhaustion of parameterRange. -/
def compactExhaustion (n : ℕ) : Set (ℝ × ℝ) :=
  {p | distToBoundary p ≥ 1 / (n + 1 : ℝ)}

lemma compactExhaustion_compact (n : ℕ) : IsCompact (compactExhaustion n) := by
  have h1 : IsClosed (compactExhaustion n) :=
    IsClosed.preimage distToBoundary_continuous isClosed_Ici
  have h2 : compactExhaustion n ⊆ Set.Icc (0 : ℝ) 2 ×ˢ Set.Icc (0 : ℝ) 2 := by
    intro p hp
    have h4 : distToBoundary p ≥ 1 / (n + 1 : ℝ) := hp
    have h_pos : 0 ≤ distToBoundary p := by
      have h5 : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
      linarith
    have h5 : 0 ≤ p.1 := by
      have h6 : distToBoundary p ≤ p.1 := distToBoundary_le_s (p := p)
      linarith
    have h6 : p.1 ≤ 2 := by
      have h7 : distToBoundary p ≤ 1 - p.1 := distToBoundary_le_1ms (p := p)
      linarith
    have h8 : 0 ≤ p.2 := by
      have h9 : distToBoundary p ≤ p.2 - p.1 := distToBoundary_le_ts (p := p)
      linarith [h_pos, h5]
    have h10 : p.2 ≤ 2 := by
      have h11 : distToBoundary p ≤ 2 - p.2 := distToBoundary_le_2t (p := p)
      linarith
    exact ⟨⟨h5, h6⟩, ⟨h8, h10⟩⟩
  have h3 : IsCompact (Set.Icc (0 : ℝ) 2 ×ˢ Set.Icc (0 : ℝ) 2) :=
    isCompact_Icc.prod isCompact_Icc
  exact IsCompact.of_isClosed_subset h3 h1 h2

lemma compactExhaustion_subset (n : ℕ) : compactExhaustion n ⊆ parameterRange := by
  intro p hp
  have h4 : distToBoundary p ≥ 1 / (n + 1 : ℝ) := hp
  have hpos : 0 < distToBoundary p := by
    have h5 : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
    linarith
  have h6 : 0 < p.1 := by
    have h7 : distToBoundary p ≤ p.1 := distToBoundary_le_s (p := p)
    linarith
  have h7 : p.1 < 1 := by
    have h8 : distToBoundary p ≤ 1 - p.1 := distToBoundary_le_1ms (p := p)
    linarith
  have h9 : p.1 < p.2 := by
    have h10 : distToBoundary p ≤ p.2 - p.1 := distToBoundary_le_ts (p := p)
    linarith
  have h10 : p.2 < 2 := by
    have h11 : distToBoundary p ≤ 2 - p.2 := distToBoundary_le_2t (p := p)
    linarith
  exact ⟨⟨h6, h7⟩, ⟨h9, h10⟩⟩

/-- For every p in parameterRange, there exists n with p ∈ compactExhaustion n. -/
lemma exists_in_compactExhaustion {p : ℝ × ℝ} (hp : p ∈ parameterRange) :
    ∃ (n : ℕ), p ∈ compactExhaustion n := by
  have h_d_pos : 0 < distToBoundary p := distToBoundary_pos hp
  have h : ∃ (n : ℕ), 1 / (n + 1 : ℝ) ≤ distToBoundary p := by
    obtain ⟨n, hn⟩ := exists_nat_ge (1 / distToBoundary p)
    refine ⟨n, ?_⟩
    have h2 : (n + 1 : ℝ) ≥ 1 / distToBoundary p := by linarith
    have h3 : 0 < (n + 1 : ℝ) := by positivity
    have h4 : 1 / (n + 1 : ℝ) ≤ distToBoundary p := by
      calc 1 / (n + 1 : ℝ)
        ≤ 1 / (1 / distToBoundary p) := by gcongr
      _ = distToBoundary p := by
        field_simp [h_d_pos.ne'] <;> ring
    exact h4
  rcases h with ⟨n, hn⟩
  exact ⟨n, hn⟩

/-- The type of the core estimate hypothesis. -/
abbrev CoreEstimateHypothesis : Prop :=
  ∀ (s t : ℝ), (s, t) ∈ parameterRange →
    ∃ (ε δ₀ : ℝ), 0 < ε ∧ 0 < δ₀ ∧ CoreEstimateHolds s t ε

/-- Choose ε_n working uniformly on compactExhaustion n. -/
def epsilonOnCompact (h_core : CoreEstimateHypothesis) (n : ℕ) : ℝ :=
  Classical.choose (compact_uniformity_from_core h_core
    (compactExhaustion_compact n) (compactExhaustion_subset n))

lemma epsilonOnCompact_pos {h_core : CoreEstimateHypothesis} {n : ℕ} :
    0 < epsilonOnCompact h_core n :=
  (Classical.choose_spec (compact_uniformity_from_core h_core
    (compactExhaustion_compact n) (compactExhaustion_subset n))).1

lemma epsilonOnCompact_holds {h_core : CoreEstimateHypothesis} {n : ℕ} :
    ∀ (p : ℝ × ℝ), p ∈ compactExhaustion n →
      CoreEstimateHolds p.1 p.2 (epsilonOnCompact h_core n) :=
  (Classical.choose_spec (compact_uniformity_from_core h_core
    (compactExhaustion_compact n) (compactExhaustion_subset n))).2

/-- Decreasing sequence: ε'_n = min(ε_0, ..., ε_n). -/
def epsilonMin (h_core : CoreEstimateHypothesis) (n : ℕ) : ℝ :=
  Finset.min' (Finset.image (epsilonOnCompact h_core) (Finset.range (n + 1)))
    (by simp)

lemma epsilonMin_pos {h_core : CoreEstimateHypothesis} {n : ℕ} :
    0 < epsilonMin h_core n := by
  have h1 : epsilonMin h_core n ∈ Finset.image (epsilonOnCompact h_core) (Finset.range (n + 1)) :=
    Finset.min'_mem _ _
  rcases Finset.mem_image.mp h1 with ⟨k, _hk, h_eq⟩
  rw [← h_eq]
  exact epsilonOnCompact_pos

lemma epsilonMin_le_epsilonOnCompact {h_core : CoreEstimateHypothesis} {n : ℕ} :
    epsilonMin h_core n ≤ epsilonOnCompact h_core n := by
  have h1 : epsilonOnCompact h_core n ∈ Finset.image (epsilonOnCompact h_core) (Finset.range (n + 1)) :=
    Finset.mem_image.mpr ⟨n, Finset.mem_range.mpr (by omega), rfl⟩
  exact Finset.min'_le _ _ h1

lemma epsilonMin_decreasing {h_core : CoreEstimateHypothesis} {n : ℕ} :
    epsilonMin h_core (n + 1) ≤ epsilonMin h_core n := by
  have h1 : epsilonMin h_core n ∈ Finset.image (epsilonOnCompact h_core) (Finset.range (n + 2)) := by
    have h2 : epsilonMin h_core n ∈ Finset.image (epsilonOnCompact h_core) (Finset.range (n + 1)) :=
      Finset.min'_mem _ _
    rcases Finset.mem_image.mp h2 with ⟨k, hk, h_eq⟩
    have h3 : k ∈ Finset.range (n + 2) := by
      simp only [Finset.mem_range] at hk ⊢ <;> omega
    rw [← h_eq]
    exact Finset.mem_image.mpr ⟨k, h3, rfl⟩
  exact Finset.min'_le _ _ h1

lemma epsilonMin_antitone {h_core : CoreEstimateHypothesis} {m n : ℕ} (h : m ≤ n) :
    epsilonMin h_core n ≤ epsilonMin h_core m := by
  induction' h with n h ih
  · rfl
  · exact le_trans epsilonMin_decreasing ih

/-- The smallest n such that p ∈ compactExhaustion n. -/
def minExhaustionIndex (p : ℝ × ℝ) (hp : p ∈ parameterRange) : ℕ :=
  Nat.find (exists_in_compactExhaustion hp)

lemma minExhaustionIndex_spec {p : ℝ × ℝ} (hp : p ∈ parameterRange) :
    p ∈ compactExhaustion (minExhaustionIndex p hp) := by
  exact Nat.find_spec (exists_in_compactExhaustion hp)

/-- The function ε(p) required by the target theorem. -/
def targetEpsilon (h_core : CoreEstimateHypothesis) (p : ℝ × ℝ) : ℝ :=
  if h : p ∈ parameterRange then
    epsilonMin h_core (minExhaustionIndex p h)
  else
    1

lemma targetEpsilon_pos {h_core : CoreEstimateHypothesis} {p : ℝ × ℝ}
    (hp : p ∈ parameterRange) : 0 < targetEpsilon h_core p := by
  have h_eq : targetEpsilon h_core p = epsilonMin h_core (minExhaustionIndex p hp) := by
    simp [targetEpsilon, hp]
  rw [h_eq]
  exact epsilonMin_pos

lemma targetEpsilon_holds {h_core : CoreEstimateHypothesis} {p : ℝ × ℝ}
    (hp : p ∈ parameterRange) :
    CoreEstimateHolds p.1 p.2 (targetEpsilon h_core p) := by
  have h_eq : targetEpsilon h_core p = epsilonMin h_core (minExhaustionIndex p hp) := by
    simp [targetEpsilon, hp]
  rw [h_eq]
  let n := minExhaustionIndex p hp
  have h1 : p ∈ compactExhaustion n := minExhaustionIndex_spec hp
  have h2 : CoreEstimateHolds p.1 p.2 (epsilonOnCompact h_core n) :=
    epsilonOnCompact_holds p h1
  have h3 : epsilonMin h_core n ≤ epsilonOnCompact h_core n :=
    epsilonMin_le_epsilonOnCompact
  have h4 : 0 < epsilonMin h_core n := epsilonMin_pos
  exact core_estimate_weaken_ε h4 h3 h2

lemma targetEpsilon_compact_uniformity {h_core : CoreEstimateHypothesis} :
    ∀ (A : Set (ℝ × ℝ)), IsCompact A → A ⊆ parameterRange →
      ∃ (ε₀ : ℝ), 0 < ε₀ ∧ ∀ p ∈ A, ε₀ ≤ targetEpsilon h_core p := by
  intro A hA_compact hA_sub
  by_cases hA_empty : A = ∅
  · refine ⟨1, by norm_num, fun p hp => by rw [hA_empty] at hp <;> simp at hp⟩
  · have hA_nonempty : A.Nonempty :=
      Set.nonempty_iff_ne_empty.mpr hA_empty
    have h_contOn : ContinuousOn distToBoundary A :=
      distToBoundary_continuous.continuousOn
    have h_min : ∃ p₀ ∈ A, ∀ p ∈ A, distToBoundary p₀ ≤ distToBoundary p :=
      hA_compact.exists_isMinOn hA_nonempty h_contOn
    rcases h_min with ⟨p₀, hp₀, hmin⟩
    have h_d_pos : 0 < distToBoundary p₀ := distToBoundary_pos (hA_sub hp₀)
    have h_exists : ∃ (N : ℕ), 1 / (N + 1 : ℝ) ≤ distToBoundary p₀ := by
      obtain ⟨N, hN⟩ := exists_nat_ge (1 / distToBoundary p₀)
      refine ⟨N, ?_⟩
      have h2 : (N + 1 : ℝ) ≥ 1 / distToBoundary p₀ := by linarith
      have h3 : 0 < (N + 1 : ℝ) := by positivity
      calc 1 / (N + 1 : ℝ)
        ≤ 1 / (1 / distToBoundary p₀) := by gcongr
      _ = distToBoundary p₀ := by field_simp [h_d_pos.ne'] <;> ring
    rcases h_exists with ⟨N, hN⟩
    have h_all_in : ∀ p ∈ A, p ∈ compactExhaustion N := by
      intro p hp
      have h4 : distToBoundary p₀ ≤ distToBoundary p := hmin p hp
      have h5 : 1 / (N + 1 : ℝ) ≤ distToBoundary p := by linarith
      exact h5
    let ε₀ := epsilonMin h_core N
    have hε₀_pos : 0 < ε₀ := epsilonMin_pos
    refine ⟨ε₀, hε₀_pos, ?_⟩
    intro p hp
    have h6 : p ∈ parameterRange := hA_sub hp
    have h_eq : targetEpsilon h_core p = epsilonMin h_core (minExhaustionIndex p h6) := by
      simp [targetEpsilon, h6]
    rw [h_eq]
    let n := minExhaustionIndex p h6
    have h7 : p ∈ compactExhaustion n := minExhaustionIndex_spec h6
    have h8 : p ∈ compactExhaustion N := h_all_in p hp
    have h9 : n ≤ N := by
      by_contra h10
      have h11 : N < n := by omega
      have h12 := Nat.find_min (exists_in_compactExhaustion h6) h11
      exact h12 h8
    have h10 : epsilonMin h_core N ≤ epsilonMin h_core n :=
      epsilonMin_antitone h9
    exact h10

/-- The target theorem, conditional on the core estimate being available. -/
theorem target_theorem_of_core_estimate (h_core : CoreEstimateHypothesis) :
    ∃ ε : ℝ × ℝ → ℝ,
      (∀ p ∈ parameterRange, 0 < ε p) ∧
        (∀ A : Set (ℝ × ℝ), IsCompact A →
          A ⊆ parameterRange →
            ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ p ∈ A, ε₀ ≤ ε p) ∧
          ∀ s t : ℝ,
            (s, t) ∈ parameterRange →
              ∃ δ₀ : ℝ, 0 < δ₀ ∧
                ∀ δ : ℝ, δ ∈ Set.Ioc (0 : ℝ) δ₀ →
                  ∀ X : Set EuclideanPlane,
                    X ⊆ Metric.closedBall 0 1 →
                      IsDeltaSSet δ t (Real.rpow δ (-(ε (s, t)))) X →
                        ∀ 𝓣 : ∀ (x : EuclideanPlane), x ∈ X → Set AffineLine,
                          (∀ x hx,
                            IsDeltaSSet δ s
                              (Real.rpow δ (-(ε (s, t)))) (𝓣 x hx)) →
                            (∀ x hx, ∀ ℓ ∈ 𝓣 x hx,
                              x ∈ Metric.cthickening δ ℓ.1) →
                              ENNReal.ofReal (Real.rpow δ (-(2 * s + ε (s, t)))) ≤
                                (Metric.externalCoveringNumber δ.toNNReal
                                  (⋃ (x : EuclideanPlane) (hx : x ∈ X), 𝓣 x hx) : ENNReal) := by
  refine ⟨targetEpsilon h_core, ?_, ?_, ?_⟩
  · intro p hp
    exact targetEpsilon_pos hp
  · exact targetEpsilon_compact_uniformity
  · intro s t hp
    have h_holds : CoreEstimateHolds s t (targetEpsilon h_core (s, t)) :=
      targetEpsilon_holds hp
    rcases h_holds with ⟨_, δ₀, hδ₀_pos, h_main⟩
    refine ⟨δ₀, hδ₀_pos, ?_⟩
    exact h_main

end DirecretisedFurstenbergEstimate.FinalProof
