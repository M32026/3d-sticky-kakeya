module

/-
  Coarse Regular Incidence Bridge

  Bridges from CTNiceConfiguration to the improved incidence bound
  |T₀| ≥ δ^{-(2s+ε)} using UniformRegularIncidenceEstimate (Theorem 6.1).

  ## Provided declarations

  1. `regular_incidence_apply_card` — apply UniformRegularIncidenceEstimate
     (unpacked) to arbitrary point/tube data, get finset cardinality bound.
  2. `regular_incidence_apply_card'` — convenience wrapper taking the
     packed estimate and a threshold-checking function.
  3. `coarse_config_regular_incidence` — thin wrapper around (1) that
     targets `coarseConfig.T₀.card`. The caller constructs the point set,
     tube family, and incidence data from the coarse config.

  ## Geometric recipe for callers

  To construct inputs from a `CTNiceConfiguration m s CΔ MΔ`:

  ### Point set
  Let `P := shift coarseConfig.pointSet` where `shift` translates by
  (-1/2,-1/2), so `P ⊆ [-1/2,1/2)² ⊆ Metric.closedBall 0 1`.

  ### Carrier
  Use a wide strip: `carrier T := {p | |p 1 - T.slope*p 0 - T.intercept| ≤ 3δ}`
  (also translated). For any point p in a δ-square q whose δ-strip intersects
  tube T, vertical distance to T's line is ≤ 3δ, so p ∈ carrier T, hence
  `dist(p, carrier T) = 0 ≤ δ`.

  ### Tube family
  For each translated point p', find the coarse square q containing p'+v,
  and set `tubeFamily p' := config.tubeFamily q`.

  ### S-set and regularity
  Tube S-set follows from `config.h_delta_s_set` (weaken constant).
  Square-root regularity of the point set must be supplied from good-scale
  between-scales regularity, transferred to the translated set.

  Whiteprint: combining_theorem_genuine / coarse_regular_incidence_bridge
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.RegularIncidence.Definitions
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DirecretisedFurstenbergEstimate.RegularIncidence

open DirecretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.CombiningTheorem

/-! ========================================================================
   Apply UniformRegularIncidenceEstimate → finset cardinality bound
   ======================================================================== -/

/-- Apply a UniformRegularIncidenceEstimate (unpacked) to get a cardinality
    bound on a finset containing the union of tube families. -/
lemma regular_incidence_apply_card
    {Line : Type*} [PseudoMetricSpace Line] [InStandardChart Line]
    {s t u εReg η δ δR : ℝ}
    (carrier : Line → Set EuclideanPlane)
    (hεReg_pos : 0 < εReg) (hη_pos : 0 < η)
    (hδR_pos : 0 < δR) (hδR_one : δR ≤ 1)
    (h_est_body : ∀ (u : ℝ), t ≤ u → u ≤ 2 →
      ∀ {δ : ℝ}, 0 < δ → δ ≤ δR →
      ∀ (P : Set EuclideanPlane),
        P ⊆ Metric.closedBall 0 1 →
        IsSquareRootRegular δ u
          (Real.rpow δ (-εReg)) (Real.rpow δ (-εReg)) P →
      ∀ (tubeFamily : (p : EuclideanPlane) → p ∈ P → Set Line),
        (∀ p hp, IsDeltaSSet δ s (Real.rpow δ (-εReg)) (tubeFamily p hp)) →
        (∀ p hp T, T ∈ tubeFamily p hp →
          p ∈ Metric.cthickening δ (carrier T)) →
        (∀ p hp T, T ∈ tubeFamily p hp →
          InStandardChart.inChart T) →
      ENNReal.ofReal (Real.rpow δ (-(2 * s + η))) ≤
        Ncover δ (⋃ p, ⋃ hp : p ∈ P, tubeFamily p hp))
    (hu_t : t ≤ u) (hu_two : u ≤ 2)
    (hδ_pos : 0 < δ) (hδ_le_R : δ ≤ δR)
    (P : Set EuclideanPlane)
    (hP_ball : P ⊆ Metric.closedBall 0 1)
    (hP_regular : IsSquareRootRegular δ u
        (Real.rpow δ (-εReg)) (Real.rpow δ (-εReg)) P)
    (tubeFamily : (p : EuclideanPlane) → p ∈ P → Set Line)
    (h_tube_sset : ∀ p hp,
        IsDeltaSSet δ s (Real.rpow δ (-εReg)) (tubeFamily p hp))
    (h_incidence : ∀ p hp T, T ∈ tubeFamily p hp →
        p ∈ Metric.cthickening δ (carrier T))
    (hChart : ∀ p hp T, T ∈ tubeFamily p hp →
        InStandardChart.inChart T)
    (T_finset : Finset Line)
    (h_union_sub : (⋃ p, ⋃ hp : p ∈ P, tubeFamily p hp) ⊆ (T_finset : Set Line)) :
    (T_finset.card : ENNReal) ≥
        ENNReal.ofReal (Real.rpow δ (-(2 * s + η))) := by
  have h_main : ENNReal.ofReal (Real.rpow δ (-(2 * s + η))) ≤
      Ncover δ (⋃ p, ⋃ hp : p ∈ P, tubeFamily p hp) :=
    h_est_body u hu_t hu_two hδ_pos hδ_le_R P hP_ball hP_regular
      tubeFamily h_tube_sset h_incidence hChart
  have h3 : Ncover δ (⋃ p, ⋃ hp : p ∈ P, tubeFamily p hp) ≤
      Ncover δ (T_finset : Set Line) := by
    exact_mod_cast Metric.externalCoveringNumber_mono_set h_union_sub
  have h4 : ENNReal.ofReal (Real.rpow δ (-(2 * s + η))) ≤
      Ncover δ (T_finset : Set Line) :=
    le_trans h_main h3
  have h5 : Ncover δ (T_finset : Set Line) ≤ ((T_finset : Set Line).encard : ENNReal) := by
    exact_mod_cast Metric.externalCoveringNumber_le_encard_self
      (ε := δ.toNNReal) (T_finset : Set Line)
  have h6 : ((T_finset : Set Line).encard : ENNReal) = (T_finset.card : ENNReal) := by
    simp
  rw [h6] at h5
  exact le_trans h4 h5

/-- Convenience wrapper: unpack a UniformRegularIncidenceEstimate and apply.
    The caller must provide `hδ_le_R` to check δ against the estimate's
    internally-chosen threshold δR. -/
lemma regular_incidence_apply_card'
    {Line : Type*} [PseudoMetricSpace Line] [InStandardChart Line]
    {s t u εReg η δ : ℝ}
    (carrier : Line → Set EuclideanPlane)
    (h_est : UniformRegularIncidenceEstimate carrier s t εReg η)
    (hδ_le_R : ∀ (δR : ℝ), 0 < δR → δR ≤ 1 → δ ≤ δR)
    (hu_t : t ≤ u) (hu_two : u ≤ 2)
    (hδ_pos : 0 < δ)
    (P : Set EuclideanPlane)
    (hP_ball : P ⊆ Metric.closedBall 0 1)
    (hP_regular : IsSquareRootRegular δ u
        (Real.rpow δ (-εReg)) (Real.rpow δ (-εReg)) P)
    (tubeFamily : (p : EuclideanPlane) → p ∈ P → Set Line)
    (h_tube_sset : ∀ p hp,
        IsDeltaSSet δ s (Real.rpow δ (-εReg)) (tubeFamily p hp))
    (h_incidence : ∀ p hp T, T ∈ tubeFamily p hp →
        p ∈ Metric.cthickening δ (carrier T))
    (hChart : ∀ p hp T, T ∈ tubeFamily p hp →
        InStandardChart.inChart T)
    (T_finset : Finset Line)
    (h_union_sub : (⋃ p, ⋃ hp : p ∈ P, tubeFamily p hp) ⊆ (T_finset : Set Line)) :
    (T_finset.card : ENNReal) ≥
        ENNReal.ofReal (Real.rpow δ (-(2 * s + η))) := by
  rcases h_est with ⟨hεReg_pos, hη_pos, δR, hδR_pos, hδR_one, h_est_body⟩
  have hδ_le_R' : δ ≤ δR := hδ_le_R δR hδR_pos hδR_one
  exact regular_incidence_apply_card carrier hεReg_pos hη_pos hδR_pos hδR_one
    h_est_body hu_t hu_two hδ_pos hδ_le_R' P hP_ball hP_regular
    tubeFamily h_tube_sset h_incidence hChart T_finset h_union_sub

/-! ========================================================================
   Thin wrapper targeting coarseConfig.T₀.card

   The caller constructs all geometric data (P, tubeFamily, incidence,
   regularity) from the coarse configuration. This lemma just wires
   everything together and outputs the T₀ cardinality bound.
   ======================================================================== -/

/-- Thin wrapper: apply regular incidence estimate to a coarse configuration.

    The caller supplies all point/tube data constructed from coarseConfig.
    This lemma simply verifies the union ⊆ T₀ and calls
    `regular_incidence_apply_card`. -/
lemma coarse_config_regular_incidence
    {m : ℕ} {s t u εReg η CΔ : ℝ} {MΔ : ℕ}
    (coarseConfig : CTNiceConfiguration m s CΔ MΔ)
    (carrier : DyadicTube m → Set EuclideanPlane)
    {δ δR : ℝ}
    (hεReg_pos : 0 < εReg) (hη_pos : 0 < η)
    (hδR_pos : 0 < δR) (hδR_one : δR ≤ 1)
    (h_est_body : ∀ (u : ℝ), t ≤ u → u ≤ 2 →
      ∀ {δ : ℝ}, 0 < δ → δ ≤ δR →
      ∀ (P : Set EuclideanPlane),
        P ⊆ Metric.closedBall 0 1 →
        IsSquareRootRegular δ u
          (Real.rpow δ (-εReg)) (Real.rpow δ (-εReg)) P →
      ∀ (tubeFamily : (p : EuclideanPlane) → p ∈ P → Set (DyadicTube m)),
        (∀ p hp, IsDeltaSSet δ s (Real.rpow δ (-εReg)) (tubeFamily p hp)) →
        (∀ p hp T, T ∈ tubeFamily p hp →
          p ∈ Metric.cthickening δ (carrier T)) →
        (∀ p hp T, T ∈ tubeFamily p hp →
          InStandardChart.inChart T) →
      ENNReal.ofReal (Real.rpow δ (-(2 * s + η))) ≤
        Ncover δ (⋃ p, ⋃ hp : p ∈ P, tubeFamily p hp))
    (hu_t : t ≤ u) (hu_two : u ≤ 2)
    (hδ_pos : 0 < δ) (hδ_le_R : δ ≤ δR)
    (P : Set EuclideanPlane)
    (hP_ball : P ⊆ Metric.closedBall 0 1)
    (hP_regular : IsSquareRootRegular δ u
        (Real.rpow δ (-εReg)) (Real.rpow δ (-εReg)) P)
    (tubeFamily : (p : EuclideanPlane) → p ∈ P → Set (DyadicTube m))
    (h_tube_sset : ∀ p hp,
        IsDeltaSSet δ s (Real.rpow δ (-εReg)) (tubeFamily p hp))
    (h_incidence : ∀ p hp T, T ∈ tubeFamily p hp →
        p ∈ Metric.cthickening δ (carrier T))
    (hChart : ∀ p hp T, T ∈ tubeFamily p hp →
        InStandardChart.inChart T)
    (h_union_sub : (⋃ p, ⋃ hp : p ∈ P, tubeFamily p hp) ⊆
        (coarseConfig.T₀ : Set (DyadicTube m))) :
    (coarseConfig.T₀.card : ENNReal) ≥
        ENNReal.ofReal (Real.rpow δ (-(2 * s + η))) :=
  regular_incidence_apply_card carrier hεReg_pos hη_pos hδR_pos hδR_one
    h_est_body hu_t hu_two hδ_pos hδ_le_R P hP_ball hP_regular
    tubeFamily h_tube_sset h_incidence hChart coarseConfig.T₀ h_union_sub

/-- Specialized version: estimate body already fixed at a specific δ.
    Avoids the δR threshold indirection when the caller knows the estimate
    is valid at the target scale. -/
lemma regular_incidence_apply_card_at_delta
    {Line : Type*} [PseudoMetricSpace Line] [InStandardChart Line]
    {s t u εReg η δ : ℝ}
    (carrier : Line → Set EuclideanPlane)
    (hεReg_pos : 0 < εReg) (hη_pos : 0 < η)
    (h_est_body : ∀ (u : ℝ), t ≤ u → u ≤ 2 →
      ∀ (P : Set EuclideanPlane),
        P ⊆ Metric.closedBall 0 1 →
        IsSquareRootRegular δ u
          (Real.rpow δ (-εReg)) (Real.rpow δ (-εReg)) P →
      ∀ (tubeFamily : (p : EuclideanPlane) → p ∈ P → Set Line),
        (∀ p hp, IsDeltaSSet δ s (Real.rpow δ (-εReg)) (tubeFamily p hp)) →
        (∀ p hp T, T ∈ tubeFamily p hp →
          p ∈ Metric.cthickening δ (carrier T)) →
        (∀ p hp T, T ∈ tubeFamily p hp →
          InStandardChart.inChart T) →
      ENNReal.ofReal (Real.rpow δ (-(2 * s + η))) ≤
        Ncover δ (⋃ p, ⋃ hp : p ∈ P, tubeFamily p hp))
    (hu_t : t ≤ u) (hu_two : u ≤ 2)
    (hδ_pos : 0 < δ)
    (P : Set EuclideanPlane)
    (hP_ball : P ⊆ Metric.closedBall 0 1)
    (hP_regular : IsSquareRootRegular δ u
        (Real.rpow δ (-εReg)) (Real.rpow δ (-εReg)) P)
    (tubeFamily : (p : EuclideanPlane) → p ∈ P → Set Line)
    (h_tube_sset : ∀ p hp,
        IsDeltaSSet δ s (Real.rpow δ (-εReg)) (tubeFamily p hp))
    (h_incidence : ∀ p hp T, T ∈ tubeFamily p hp →
        p ∈ Metric.cthickening δ (carrier T))
    (hChart : ∀ p hp T, T ∈ tubeFamily p hp →
        InStandardChart.inChart T)
    (T_finset : Finset Line)
    (h_union_sub : (⋃ p, ⋃ hp : p ∈ P, tubeFamily p hp) ⊆ (T_finset : Set Line)) :
    (T_finset.card : ENNReal) ≥
        ENNReal.ofReal (Real.rpow δ (-(2 * s + η))) := by
  have h_main : ENNReal.ofReal (Real.rpow δ (-(2 * s + η))) ≤
      Ncover δ (⋃ p, ⋃ hp : p ∈ P, tubeFamily p hp) :=
    h_est_body u hu_t hu_two P hP_ball hP_regular
      tubeFamily h_tube_sset h_incidence hChart
  have h3 : Ncover δ (⋃ p, ⋃ hp : p ∈ P, tubeFamily p hp) ≤
      Ncover δ (T_finset : Set Line) := by
    exact_mod_cast Metric.externalCoveringNumber_mono_set h_union_sub
  have h4 : ENNReal.ofReal (Real.rpow δ (-(2 * s + η))) ≤
      Ncover δ (T_finset : Set Line) :=
    le_trans h_main h3
  have h5 : Ncover δ (T_finset : Set Line) ≤ ((T_finset : Set Line).encard : ENNReal) := by
    exact_mod_cast Metric.externalCoveringNumber_le_encard_self
      (ε := δ.toNNReal) (T_finset : Set Line)
  have h6 : ((T_finset : Set Line).encard : ENNReal) = (T_finset.card : ENNReal) := by
    simp
  rw [h6] at h5
  exact le_trans h4 h5

/-- Specialized thin wrapper targeting coarseConfig.T₀.card at a fixed δ. -/
lemma coarse_config_regular_incidence_at_delta
    {m : ℕ} {s t u εReg η CΔ : ℝ} {MΔ : ℕ}
    (coarseConfig : CTNiceConfiguration m s CΔ MΔ)
    (carrier : DyadicTube m → Set EuclideanPlane)
    {δ : ℝ}
    (hεReg_pos : 0 < εReg) (hη_pos : 0 < η)
    (h_est_body : ∀ (u : ℝ), t ≤ u → u ≤ 2 →
      ∀ (P : Set EuclideanPlane),
        P ⊆ Metric.closedBall 0 1 →
        IsSquareRootRegular δ u
          (Real.rpow δ (-εReg)) (Real.rpow δ (-εReg)) P →
      ∀ (tubeFamily : (p : EuclideanPlane) → p ∈ P → Set (DyadicTube m)),
        (∀ p hp, IsDeltaSSet δ s (Real.rpow δ (-εReg)) (tubeFamily p hp)) →
        (∀ p hp T, T ∈ tubeFamily p hp →
          p ∈ Metric.cthickening δ (carrier T)) →
        (∀ p hp T, T ∈ tubeFamily p hp →
          InStandardChart.inChart T) →
      ENNReal.ofReal (Real.rpow δ (-(2 * s + η))) ≤
        Ncover δ (⋃ p, ⋃ hp : p ∈ P, tubeFamily p hp))
    (hu_t : t ≤ u) (hu_two : u ≤ 2)
    (hδ_pos : 0 < δ)
    (P : Set EuclideanPlane)
    (hP_ball : P ⊆ Metric.closedBall 0 1)
    (hP_regular : IsSquareRootRegular δ u
        (Real.rpow δ (-εReg)) (Real.rpow δ (-εReg)) P)
    (tubeFamily : (p : EuclideanPlane) → p ∈ P → Set (DyadicTube m))
    (h_tube_sset : ∀ p hp,
        IsDeltaSSet δ s (Real.rpow δ (-εReg)) (tubeFamily p hp))
    (h_incidence : ∀ p hp T, T ∈ tubeFamily p hp →
        p ∈ Metric.cthickening δ (carrier T))
    (hChart : ∀ p hp T, T ∈ tubeFamily p hp →
        InStandardChart.inChart T)
    (h_union_sub : (⋃ p, ⋃ hp : p ∈ P, tubeFamily p hp) ⊆
        (coarseConfig.T₀ : Set (DyadicTube m))) :
    (coarseConfig.T₀.card : ENNReal) ≥
        ENNReal.ofReal (Real.rpow δ (-(2 * s + η))) :=
  regular_incidence_apply_card_at_delta carrier hεReg_pos hη_pos
    h_est_body hu_t hu_two hδ_pos P hP_ball hP_regular
    tubeFamily h_tube_sset h_incidence hChart coarseConfig.T₀ h_union_sub

end DirecretisedFurstenbergEstimate.RegularIncidence
