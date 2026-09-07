module

/-
  Early endpoint adapter for the u=2 boundary.

  Instead of a late u_eff = 2-ε branch, we select the running exponent BEFORE
  constructing DeltasSet/Nice/B1/A2/A4:

    rho_endpoint = min(εA / 200, (2 - t) / 4)
    u_run    = if u_orig < 2 then u_orig else 2 - 2 * rho_endpoint
    εA_run   = if u_orig < 2 then εA     else εA + rho_endpoint

  Key identity: u_run / 2 + εA_run = u_orig / 2 + εA
  This lets the public sqrt-covering bound transfer unchanged.

  Properties: t ≤ u_run < 2, u_run ≤ u_orig.
-/
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.RegularIncidence.Definitions

@[expose] public section

namespace DirecretisedFurstenbergEstimate.FrontEndLemmas.EndpointAdapter

open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.RegularIncidence

/-- Construct rho_endpoint, u_run, εA_run from the original parameters. -/
noncomputable def endpointAdapter (u_orig εA t : ℝ) : ℝ × ℝ × ℝ :=
  let rho_endpoint := min (εA / 200) ((2 - t) / 4)
  let u_run := if u_orig < 2 then u_orig else 2 - 2 * rho_endpoint
  let εA_run := if u_orig < 2 then εA else εA + rho_endpoint
  (rho_endpoint, u_run, εA_run)

/-- Prove t ≤ u_run < 2, u_run ≤ u_orig, and the exponent identity.

    Here u_run and εA_run are the second and third components of endpointAdapter. -/
lemma endpointAdapter_spec
    {u_orig εA t : ℝ}
    (hεA_pos : 0 < εA)
    (ht_pos : 0 < t)
    (ht_lt_two : t < 2)
    (hu_t : t ≤ u_orig)
    (hu_two : u_orig ≤ 2) :
    t ≤ (endpointAdapter u_orig εA t).2.1 ∧
    (endpointAdapter u_orig εA t).2.1 < 2 ∧
    (endpointAdapter u_orig εA t).2.1 ≤ u_orig ∧
    (endpointAdapter u_orig εA t).2.1 / 2 + (endpointAdapter u_orig εA t).2.2 =
      u_orig / 2 + εA := by
  by_cases h : u_orig < 2
  · simp [endpointAdapter, h] <;> linarith
  · have h_eq : u_orig = 2 := by linarith
    have h' : ¬u_orig < 2 := by linarith
    let rho_endpoint := min (εA / 200) ((2 - t) / 4)
    have h_u_run_ge_t : t ≤ 2 - 2 * rho_endpoint := by linarith [min_le_right (εA / 200) ((2 - t) / 4)]
    have h_u_run_lt_two : (2 - 2 * rho_endpoint) < 2 := by
      have hpos : 0 < rho_endpoint := by
        apply lt_min <;> linarith
      linarith
    have hpos : 0 < rho_endpoint := by apply lt_min <;> linarith
    have h_u_run_le_orig : (2 - 2 * rho_endpoint) ≤ u_orig := by
      rw [h_eq]
      linarith
    have h_identity : (2 - 2 * rho_endpoint) / 2 + (εA + rho_endpoint) = u_orig / 2 + εA := by
      rw [h_eq] <;> ring
    have h_goal : t ≤ (2 - 2 * rho_endpoint) ∧
        (2 - 2 * rho_endpoint) < 2 ∧
        (2 - 2 * rho_endpoint) ≤ u_orig ∧
        (2 - 2 * rho_endpoint) / 2 + (εA + rho_endpoint) = u_orig / 2 + εA :=
      ⟨h_u_run_ge_t, h_u_run_lt_two, h_u_run_le_orig, h_identity⟩
    have h_simp : (endpointAdapter u_orig εA t) = (rho_endpoint, 2 - 2 * rho_endpoint, εA + rho_endpoint) := by
      simp [endpointAdapter, h'] <;> rfl
    rw [h_simp]
    exact h_goal

/-- Weaken an S-set from exponent u_orig to u_run ≤ u_orig.

    Direct proof avoiding import conflicts with existing weaken_exponent lemmas.
    Requires 0 ≤ u_run, u_run ≤ u_orig, and C ≥ 1. -/
lemma weakenSSetEndpoint
    {X : Type*} [PseudoMetricSpace X]
    {δ u_orig u_run C : ℝ} {P : Set X}
    (h : IsDeltaSSet δ u_orig C P)
    (hu_run_nonneg : 0 ≤ u_run)
    (hle : u_run ≤ u_orig)
    (hC_one : 1 ≤ C) :
    IsDeltaSSet δ u_run C P := by
  rcases h with ⟨hne, hδ_pos, hC_pos, hs, hmain⟩
  refine' ⟨hne, hδ_pos, hC_pos, hu_run_nonneg, _⟩
  intro x r hr
  by_cases h_r_le_one : r ≤ 1
  · -- r ≤ 1: r^u_orig ≤ r^u_run since u_run ≤ u_orig
    have h_ofReal_le_one : ENNReal.ofReal r ≤ 1 :=
      ENNReal.ofReal_le_one.mpr h_r_le_one
    have h1 : (ENNReal.ofReal r) ^ u_orig ≤ (ENNReal.ofReal r) ^ u_run :=
      ENNReal.rpow_le_rpow_of_exponent_ge h_ofReal_le_one hle
    have h_main' := hmain x r hr
    calc (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) : ENNReal)
        ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ u_orig *
            (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := h_main'
      _ ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ u_run *
            (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by
          gcongr <;> exact h1
  · -- r > 1: covering ≤ Ncover(P), and C * r^u_run ≥ 1
    have h_r_gt_one : 1 < r := by linarith
    have h_sub : P ∩ Metric.closedBall x r ⊆ P := by simp
    have h2 : (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) : ENNReal) ≤
        (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by
      exact_mod_cast Metric.externalCoveringNumber_mono_set h_sub
    have h4 : (1 : ℝ) ≤ r ^ u_run := by
      have h5 : (1 : ℝ) ≤ r := by linarith
      exact Real.one_le_rpow h5 hu_run_nonneg
    have h7 : (1 : ENNReal) ≤ ENNReal.ofReal C := by
      simpa using ENNReal.ofReal_le_ofReal hC_one
    have h8 : (1 : ENNReal) ≤ (ENNReal.ofReal r) ^ u_run := by
      by_cases h_u : 0 < u_run
      · have h9 : (1 : ENNReal) ≤ ENNReal.ofReal r := by
          simpa [ENNReal.ofReal_le_ofReal] using show (1 : ℝ) ≤ r by linarith
        exact ENNReal.one_le_rpow h9 h_u
      · have h_u0 : u_run = 0 := by linarith
        rw [h_u0, ENNReal.rpow_zero] <;> norm_num
    have h10 : (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) ≤
        ENNReal.ofReal C * (ENNReal.ofReal r) ^ u_run *
          (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by
      have h11 : (1 : ENNReal) ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ u_run :=
        one_le_mul h7 h8
      have h12 : (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) ≤
          (ENNReal.ofReal C * (ENNReal.ofReal r) ^ u_run) *
            (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by
        exact le_mul_of_one_le_left' h11
      simpa [mul_assoc] using h12
    exact h2.trans h10

/-- Weaken the constant of an S-set: if C ≤ C', a (δ,s,C)-set is a (δ,s,C')-set. -/
lemma weakenSSetConst
    {X : Type*} [PseudoMetricSpace X]
    {δ s C C' : ℝ} {P : Set X}
    (h : IsDeltaSSet δ s C P)
    (hC : C ≤ C') :
    IsDeltaSSet δ s C' P := by
  rcases h with ⟨hne, hδ_pos, hC_pos, hs, hmain⟩
  have hC'_pos : 0 < C' := by linarith
  refine' ⟨hne, hδ_pos, hC'_pos, hs, _⟩
  intro x r hr
  have h4 := hmain x r hr
  have h5 : ENNReal.ofReal C ≤ ENNReal.ofReal C' := ENNReal.ofReal_le_ofReal hC
  calc (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) : ENNReal)
      ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
          (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := h4
    _ ≤ ENNReal.ofReal C' * (ENNReal.ofReal r) ^ s *
          (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by
        gcongr

/-- Transfer the sqrt-covering bound using the exponent identity.

    Since u_run/2 + εA_run = u_orig/2 + εA, the bound is literally identical. -/
lemma transferSqrtCoverEndpoint
    {δ u_orig u_run εA εA_run : ℝ}
    (hδ_pos : 0 < δ)
    (h_identity : u_run / 2 + εA_run = u_orig / 2 + εA)
    {P : Set EuclideanPlane}
    (h : RegularIncidence.Ncover (Real.sqrt δ) P ≤
           ENNReal.ofReal (Real.rpow δ (-(u_orig / 2 + εA)))) :
    RegularIncidence.Ncover (Real.sqrt δ) P ≤
      ENNReal.ofReal (Real.rpow δ (-(u_run / 2 + εA_run))) := by
  have h1 : -(u_run / 2 + εA_run) = -(u_orig / 2 + εA) := by linarith
  rw [h1]
  exact h

/-- Bound on εA_run: since ρ_endpoint ≤ εA/200, we have
    εA_run ≤ εA + εA/200 = εA * 201/200.

    When εA = ε/50, this gives εA_run ≤ 201*ε/10000. -/
lemma endpointAdapter_epsilonA_run_bound
    {u_orig εA t : ℝ}
    (hεA_pos : 0 < εA) :
    (endpointAdapter u_orig εA t).2.2 ≤ εA * 201 / 200 := by
  by_cases h : u_orig < 2
  · -- u_orig < 2: εA_run = εA
    have h_simp : (endpointAdapter u_orig εA t).2.2 = εA := by
      simp [endpointAdapter, h] <;> ring
    rw [h_simp]
    have h : εA ≤ εA * 201 / 200 := by
      have hpos : 0 < εA := hεA_pos
      nlinarith
    exact h
  · -- u_orig ≥ 2: εA_run = εA + ρ_endpoint, ρ_endpoint ≤ εA/200
    have h' : ¬u_orig < 2 := by linarith
    let rho_endpoint := min (εA / 200) ((2 - t) / 4)
    have h_rho_le : rho_endpoint ≤ εA / 200 := min_le_left _ _
    have h_simp : (endpointAdapter u_orig εA t).2.2 = εA + rho_endpoint := by
      simp [endpointAdapter, h'] <;> ring
    rw [h_simp]
    have h : εA + rho_endpoint ≤ εA * 201 / 200 := by
      calc εA + rho_endpoint
        ≤ εA + εA / 200 := by linarith [h_rho_le]
      _ = εA * 201 / 200 := by ring
    exact h

/-- Combined endpoint S-set weakening for the common case where
    C = δ^{-εA} and we want constant δ^{-εA_run}.

    Since εA_run ≥ εA and δ < 1, δ^{-εA_run} ≥ δ^{-εA} ≥ 1,
    so both exponent and constant weaken correctly. -/
lemma weakenSSetEndpointWithConst
    {X : Type*} [PseudoMetricSpace X]
    {δ u_orig u_run εA εA_run : ℝ} {P : Set X}
    (hδ_pos : 0 < δ) (hδ_lt_one : δ < 1)
    (hεA_pos : 0 < εA) (hεA_run_ge : εA ≤ εA_run)
    (h : IsDeltaSSet δ u_orig (Real.rpow δ (-εA)) P)
    (hu_run_nonneg : 0 ≤ u_run)
    (hle : u_run ≤ u_orig) :
    IsDeltaSSet δ u_run (Real.rpow δ (-εA_run)) P := by
  have hC_one : (1 : ℝ) ≤ Real.rpow δ (-εA) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ_pos hδ_lt_one.le (by linarith)
  have hC_le : Real.rpow δ (-εA) ≤ Real.rpow δ (-εA_run) := by
    have h1 : -εA_run ≤ -εA := by linarith
    exact Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_lt_one.le h1
  have h' : IsDeltaSSet δ u_run (Real.rpow δ (-εA)) P :=
    weakenSSetEndpoint h hu_run_nonneg hle hC_one
  exact weakenSSetConst h' hC_le

end DirecretisedFurstenbergEstimate.FrontEndLemmas.EndpointAdapter
