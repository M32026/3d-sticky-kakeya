/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourcePaidReachableDescent
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceChosenTowerRealization
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceClosure

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

universe u

/-- All scale-independent choices of this conditional closure. The actual positive gain
and the paid absolute Sticky accuracy are separate obligations of the terminal producer. -/
structure SourcePaidDescentParameters (beta c : Real) where
  M : Nat
  K : Nat
  h : Real
  eta0 : Real
  q : Real
  a0 : Real
  eta : Real
  stickyAccuracy : Real
  stickyPayment : Real
  gain : Real
  levels_ge_two : 2 <= M
  loss_power_pos : 1 <= K
  potential_step_pos : 0 < h
  input_ceiling_pos : 0 < eta0
  entrance_payment_pos : 0 < q
  descent_payment_pos : 0 < a0
  descent_payment_le : a0 <= eta0
  entrance_fullness_budget : 4 * q <= eta0
  gain_budget : 3 * q + a0 < c
  dichotomy_exponent_pos : 0 < eta
  dichotomy_exponent_le_one : eta <= 1
  dichotomy_exponent_le_entrance : eta <= q
  sticky_accuracy_pos : 0 < stickyAccuracy
  sticky_payment_nonneg : 0 <= stickyPayment
  sticky_margin : stickyAccuracy + stickyPayment <= beta / 2 - c
  actual_gain_margin : 5 * c <= gain

/-- Source S:6136-6146 fixes this exact log-base-two loss before the input scale. -/
noncomputable def SourcePaidDescentParameters.loss {beta c : Real}
    (P : SourcePaidDescentParameters beta c) (d : NNReal) : ENNReal :=
  sourceFixedPreparationLoss P.K d

/-- The three entrance powers and the final descent power fit below c. -/
theorem source_exists_paid_descent_scalar_budget {eta0 c : Real}
    (heta : 0 < eta0) (hc : 0 < c) :
    ∃ q a0 : Real, 0 < q /\ 0 < a0 /\ a0 <= eta0 /\
      4 * q <= eta0 /\ 3 * q + a0 < c := by
  let x : Real := min eta0 c / 8
  have hx : 0 < x := by dsimp [x]; positivity
  have he : x <= eta0 / 8 := by dsimp [x]; gcongr; exact min_le_left _ _
  have hc' : x <= c / 8 := by dsimp [x]; gcongr; exact min_le_right _ _
  exact ⟨x, x, hx, hx, by linarith, by linarith, by linarith⟩

/-- A single eventual threshold pays every restart AND the final terminal trial. -/
theorem source_eventually_paid_descent_loss {beta c : Real}
    (P : SourcePaidDescentParameters beta c) :
    ∀ᶠ d : NNReal in 𝓝[>] 0,
      0 < d /\ d < 1 /\ 1 <= P.loss d /\ P.loss d ≠ ⊤ /\
      P.loss d ^ (sourceAssignedPotentialCeiling P.M P.h + 1) <=
        (d : ENNReal) ^ (-P.a0) := by
  have hbound := Kakeya.VeryNotSticky.eventually_ofReal_polylog_pow_le_rpow_neg
    (A := 2) (B := 1) (by norm_num) (by norm_num)
    (P.K * (sourceAssignedPotentialCeiling P.M P.h + 1)) P.descent_payment_pos
  filter_upwards [hbound, Ioo_mem_nhdsGT (show (0 : NNReal) < 1 by norm_num)]
    with d hbound hd
  have hd0 : (0 : Real) < d := by exact_mod_cast hd.1
  have hd1 : (d : Real) <= 1 := by exact_mod_cast hd.2.le
  have hlog : 0 <= Real.logb 2 (1 / (d : Real)) :=
    Real.logb_nonneg (by norm_num) (by rw [one_le_div hd0]; exact hd1)
  have hbase : (1 : Real) <= 2 + Real.logb 2 (1 / (d : Real)) := by linarith
  refine ⟨hd.1, hd.2, ?_, ENNReal.ofReal_ne_top, ?_⟩
  · change 1 <= ENNReal.ofReal _
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (one_le_pow₀ hbase)
  · change ENNReal.ofReal _ ^ _ <= _
    rw [← ENNReal.ofReal_pow (pow_nonneg (by linarith :
      (0 : Real) <= 2 + Real.logb 2 (1 / (d : Real))) P.K), ← pow_mul]
    simpa only [one_mul, one_div] using hbound

/-- The remaining positive margins absorb the FIXED factor two in d=delta/2. -/
theorem source_eventually_half_scale_terminal_payment {beta c : Real}
    (P : SourcePaidDescentParameters beta c) (hc : 0 < c) :
    ∀ᶠ delta : NNReal in 𝓝[>] 0,
      0 < delta /\ delta < 1 /\
      (((delta / 2 : NNReal) : ENNReal) ^
          (-(P.stickyAccuracy + P.stickyPayment) - 3 * P.q - P.a0) <=
        (delta : ENNReal) ^ (-(beta / 2))) /\
      (((delta / 2 : NNReal) : ENNReal) ^ (P.gain - 3 * P.q - P.a0) <=
        (delta : ENNReal) ^ (4 * c)) := by
  let p : Real := -(P.stickyAccuracy + P.stickyPayment) - 3 * P.q - P.a0
  let g : Real := P.gain - 3 * P.q - P.a0
  have hp : -(beta / 2) < p := by
    dsimp [p]
    linarith [P.sticky_margin, P.gain_budget]
  have hg : 4 * c < g := by
    dsimp [g]
    linarith [P.actual_gain_margin, P.gain_budget]
  have hfinite (e : Real) : (((1 / 2 : NNReal) : ENNReal)) ^ e ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_ne_zero (by norm_num) ENNReal.coe_ne_top
  have hsticky := Kakeya.VeryNotSticky.eventually_ennreal_mul_rpow_le_rpow (hfinite p) hp
  have hgain := Kakeya.VeryNotSticky.eventually_ennreal_mul_rpow_le_rpow (hfinite g) hg
  filter_upwards [hsticky, hgain,
    Ioo_mem_nhdsGT (show (0 : NNReal) < 1 by norm_num)] with delta hs hg hd
  have hscale (e : Real) : (((delta / 2 : NNReal) : ENNReal)) ^ e =
      (((1 / 2 : NNReal) : ENNReal)) ^ e * (delta : ENNReal) ^ e := by
    rw [show delta / 2 = (1 / 2 : NNReal) * delta by ring, ENNReal.coe_mul,
      ENNReal.mul_rpow_of_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top]
  exact ⟨hd.1, hd.2, (hscale p).trans_le hs, (hscale g).trans_le hg⟩

/-- An actual entrance and one fixed Q, with the trial law left explicitly open.
Only definitions are used from the construction modules. -/
structure SourceFixedQDescentRun {beta c : Real} (P : SourcePaidDescentParameters beta c)
    {iota : Type u} {delta : NNReal} (S : Finset iota)
    (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))) where
  canonicalFamily : Finset iota
  initialFamily : Finset iota
  normalized : iota -> ShadedTube (delta / 2) (EuclideanSpace Real (Fin 3))
  normalizationMap : iota -> iota
  normalization : SourceCanonicalNormalization S canonicalFamily Z normalized normalizationMap P.q
  initial_subset : initialFamily <= canonicalFamily
  tower : SourceThreadedTower initialFamily (fun i => (normalized i).toTube)
    P.M sourceThreadConstant
  geometry : SourceTowerGeometry tower sourceBottomED sourceLevelED
  neighbour_sharing : SourceTowerNeighbourSharing tower
  tower_mass_retention : (∑ i ∈ canonicalFamily, volume (normalized i).shade) <=
    sourceTowerSelectionLoss P.M canonicalFamily.card *
      ∑ i ∈ initialFamily, volume (normalized i).shade
  entrance_cost : sourceCentringCost delta P.q *
    sourceTowerSelectionLoss P.M canonicalFamily.card <=
      ((delta / 2 : NNReal) : ENNReal) ^ (-(3 * P.q))
  initial : SourcePaidState initialFamily (fun i => (normalized i).toTube) normalized
  initial_family_identity : initial.family = initialFamily
  initial_shading_identity : initial.shaded = normalized
  entrance_multiplicity : ShadedBody.multiplicity S (fun i => (Z i).toShadedBody) <=
    ((delta / 2 : NNReal) : ENNReal) ^ (-(3 * P.q)) * initial.multiplicity
  original_cardinality : initialFamily.card <= S.card
  original_density : Kakeya.maxDensity initialFamily
    (fun i => (normalized i).toConvexSpaceBody) <=
      ((delta / 2 : NNReal) : ENNReal) ^ (-P.eta0)
  initial_fullness : ((delta / 2 : NNReal) : ENNReal) ^ P.eta0 <= initial.fullness
  initial_cardinality_bound : (initialFamily.card : Real) <=
    ((delta / 2 : NNReal) : Real) ^ (-5 : Real)
  actual_reachable_trial : SourceReachablePaidTrialLaw tower P.h P.eta0
    (P.stickyAccuracy + P.stickyPayment) P.gain beta (P.loss (delta / 2)) initial

/-- All families in the unchanged Dichotomy domain; Q is an output after the runtime input.
This is an explicit producer obligation, not a theorem supplied by the current package. -/
def SourceFixedQDescentProducer {beta c : Real} (P : SourcePaidDescentParameters beta c) : Prop :=
  ∀ᶠ delta : NNReal in 𝓝[>] 0,
    ∀ {iota : Type u} (S : Finset iota)
      (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))),
      (∀ i ∈ S, (Z i).carrier <= Metric.closedBall 0 1) ->
      IsKatzTao S (fun i => (Z i).toConvexSpaceBody) ((delta : ENNReal) ^ (-P.eta)) ->
      ShadedBody.fullness S (fun i => (Z i).toShadedBody) >= delta ^ P.eta ->
      (delta : Real)⁻¹ <= (S.card : Real) ->
      Nonempty (SourceFixedQDescentRun P S Z)

/-- Payment after the actual trace, still at d=delta/2 and before the fixed factor two. -/
theorem source_fixedQ_run_half_scale_bound {beta c : Real}
    (P : SourcePaidDescentParameters beta c) (hbeta : 0 <= beta)
    {iota : Type u} {delta : NNReal} {S : Finset iota}
    {Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))}
    (run : SourceFixedQDescentRun P S Z)
    (hd0 : 0 < delta / 2) (hd1 : delta / 2 < 1)
    (hloss : 1 <= P.loss (delta / 2)) (hlossFinite : P.loss (delta / 2) ≠ ⊤)
    (hpay : P.loss (delta / 2) ^ (sourceAssignedPotentialCeiling P.M P.h + 1) <=
      ((delta / 2 : NNReal) : ENNReal) ^ (-P.a0)) :
    (ShadedBody.multiplicity S (fun i => (Z i).toShadedBody) <=
      ((delta / 2 : NNReal) : ENNReal) ^
        (-(P.stickyAccuracy + P.stickyPayment) - 3 * P.q - P.a0)) \/
    (ShadedBody.multiplicity S (fun i => (Z i).toShadedBody) <=
      ((delta / 2 : NNReal) : ENNReal) ^ (P.gain - 3 * P.q - P.a0) *
        (S.card : ENNReal) ^ beta) := by
  obtain ⟨trace, _, _, _, hbound⟩ := source_paid_descent_bound run.tower run.initial
    P.potential_step_pos hd0 hd1 hloss hlossFinite P.input_ceiling_pos P.descent_payment_pos
    P.descent_payment_le hbeta run.initial_cardinality_bound run.initial_fullness hpay
    run.actual_reachable_trial
  have hdne : (((delta / 2 : NNReal) : ENNReal)) ≠ 0 := by exact_mod_cast hd0.ne'
  have hdtop : (((delta / 2 : NNReal) : ENNReal)) ≠ ⊤ := ENNReal.coe_ne_top
  rcases hbound with hsticky | hgain
  · left
    calc ShadedBody.multiplicity S (fun i => (Z i).toShadedBody) <=
          (((delta / 2 : NNReal) : ENNReal)) ^ (-(3 * P.q)) * run.initial.multiplicity :=
        run.entrance_multiplicity
      _ <= (((delta / 2 : NNReal) : ENNReal)) ^ (-(3 * P.q)) *
          (((delta / 2 : NNReal) : ENNReal)) ^
            (-(P.stickyAccuracy + P.stickyPayment) - P.a0) :=
        mul_le_mul_right hsticky _
      _ = _ := by rw [← ENNReal.rpow_add _ _ hdne hdtop]; congr 1; ring
  · right
    have hcard : (run.initial.family.card : ENNReal) ^ beta <= (S.card : ENNReal) ^ beta := by
      apply ENNReal.rpow_le_rpow _ hbeta
      rw [run.initial_family_identity]
      exact_mod_cast run.original_cardinality
    calc ShadedBody.multiplicity S (fun i => (Z i).toShadedBody) <=
          (((delta / 2 : NNReal) : ENNReal)) ^ (-(3 * P.q)) * run.initial.multiplicity :=
        run.entrance_multiplicity
      _ <= (((delta / 2 : NNReal) : ENNReal)) ^ (-(3 * P.q)) *
          ((((delta / 2 : NNReal) : ENNReal)) ^ (P.gain - P.a0) *
            (run.initial.family.card : ENNReal) ^ beta) := mul_le_mul_right hgain _
      _ <= (((delta / 2 : NNReal) : ENNReal)) ^ (-(3 * P.q)) *
          ((((delta / 2 : NNReal) : ENNReal)) ^ (P.gain - P.a0) *
            (S.card : ENNReal) ^ beta) := by gcongr
      _ = _ := by rw [← mul_assoc, ← ENNReal.rpow_add _ _ hdne hdtop]; congr 2; ring

end Kakeya.ML2Core

namespace Kakeya.ML2Assembly

universe u

open Kakeya.ML2Core

/-- The actual chosen-Q producer is sufficient for the exact mass-form Dichotomy. -/
theorem source_dichotomy_of_fixedQ_descent {beta c : Real}
    (P : SourcePaidDescentParameters beta c) (hbeta : 0 <= beta) (hc : 0 < c)
    (hproducer : SourceFixedQDescentProducer.{u} P) :
    Dichotomy.{u} beta (beta / 2) (4 * c) P.eta := by
  have hhalf : Tendsto (fun delta : NNReal => delta / 2) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa only [id_eq, zero_div] using
        ((continuous_id.tendsto (0 : NNReal)).div_const (2 : NNReal)).mono_left
          (nhdsWithin_le_nhds (s := Set.Ioi (0 : NNReal)))
    · filter_upwards [self_mem_nhdsWithin] with delta hd
      change 0 < delta / 2
      exact div_pos hd (by norm_num)
  have hloss := hhalf.eventually (source_eventually_paid_descent_loss P)
  filter_upwards [hproducer, hloss, source_eventually_half_scale_terminal_payment P hc]
    with delta hproducer hloss hpayment
  intro iota S Z hball hKT hfull hcard
  obtain ⟨run⟩ := hproducer S Z hball hKT hfull hcard
  rcases source_fixedQ_run_half_scale_bound P hbeta run hloss.1 hloss.2.1 hloss.2.2.1
    hloss.2.2.2.1 hloss.2.2.2.2 with hsticky | hgain
  · exact Or.inl ((ShadedBody.multiplicity_le_iff S (fun i => (Z i).toShadedBody)).mp
      (hsticky.trans hpayment.2.2.1))
  · exact Or.inr ((ShadedBody.multiplicity_le_iff S (fun i => (Z i).toShadedBody)).mp
      (hgain.trans (mul_le_mul_left hpayment.2.2.2 _)))

/-- The quantifiers choose every descent parameter before every runtime scale and family. -/
def SourcePointwiseFixedQProducers : Prop :=
  ∀ beta : Real, 0 < beta -> beta <= 1 ->
    KatzTaoEstimate.{u} (EuclideanSpace Real (Fin 3)) beta ->
    FrostmanEstimate.{u} (EuclideanSpace Real (Fin 3)) beta ->
    ∃ c : Real, 0 < c /\ 2 * c <= beta /\
      ∃ P : SourcePaidDescentParameters beta c, SourceFixedQDescentProducer.{u} P

/-- Conditional closure only: hproducers includes the actual normalization, Q and trial laws. -/
theorem source_pointwiseCore_of_fixedQ_producers
    (hproducers : SourcePointwiseFixedQProducers.{u}) : PointwiseCore.{u} := by
  intro beta hbeta hbeta1 hKT hF
  obtain ⟨c, hc, hcbeta, P, hP⟩ := hproducers beta hbeta hbeta1 hKT hF
  exact ⟨c, hc, hcbeta, P.eta, P.dichotomy_exponent_pos, P.dichotomy_exponent_le_one,
    source_dichotomy_of_fixedQ_descent P hbeta.le hc hP⟩

/-- The existing free-cap endpoint needs no universal ambient-U TrialSupplier premise. -/
theorem source_mainLemma2Statement_of_fixedQ_producers
    (hproducers : SourcePointwiseFixedQProducers.{u}) : VNSUniform.MainLemma2Statement.{u} := by
  exact mainLemma2Statement_of_pointwiseCore_free
    (source_pointwiseCore_of_fixedQ_producers hproducers)

end Kakeya.ML2Assembly
