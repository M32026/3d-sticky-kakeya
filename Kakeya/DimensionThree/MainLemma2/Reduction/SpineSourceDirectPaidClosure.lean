/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceDirectWindowTrial

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube
open scoped NNReal ENNReal Classical

namespace Kakeya.ML2Core

universe u

section Trace

variable {iota : Type u} {delta : NNReal} {S : Finset iota}
  {T : iota -> Tube delta (EuclideanSpace Real (Fin 3))} {M C : Nat}
  {Y : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))}

/-- The direct D trace changes only the step certificate, preserving the
existing paid states and terminal estimates. Every actual successor pays
mass and strictly lowers the same original-Q integer potential. -/
structure SourceDirectPaidTrace (Q : SourceThreadedTower S T M C)
    (h : Real) (loss : ENNReal) (initial : SourcePaidState S T Y) where
  length : Nat
  state : Fin (length + 1) -> SourcePaidState S T Y
  start : state 0 = initial
  step : forall j : Fin length,
    SourceDirectPaidStep Q h loss (state j.castSucc) (state j.succ)

def SourceDirectPaidTrace.last {Q : SourceThreadedTower S T M C} {h : Real}
    {loss : ENNReal} {initial : SourcePaidState S T Y}
    (trace : SourceDirectPaidTrace Q h loss initial) : SourcePaidState S T Y :=
  trace.state (Fin.last trace.length)

/-- Finite descent from the literal D inequality. The actual trace and
every state's fullness/mass ledger are outputs. The final trial is charged
at k+1, using the same previously fixed sourceAssignedPotentialCeiling. -/
theorem source_direct_paid_descent_bound
    (Q : SourceThreadedTower S T M C) (initial : SourcePaidState S T Y)
    {h eta0 a0 alpha gamma beta : Real} {loss : ENNReal}
    (hh : 0 < h) (hd0 : 0 < delta) (hd1 : delta < 1)
    (hloss : 1 <= loss) (hlossFinite : loss ≠ ⊤)
    (heta : 0 < eta0) (ha : 0 < a0) (haeta : a0 <= eta0) (hbeta : 0 <= beta)
    (hcard : (S.card : Real) <= (delta : Real) ^ (-5 : Real))
    (hfull : (delta : ENNReal) ^ eta0 <= initial.fullness)
    (hpay : loss ^ (sourceAssignedPotentialCeiling M h + 1) <= (delta : ENNReal) ^ (-a0))
    (htrial : SourceDirectPaidTrialLaw Y Q h eta0 alpha gamma beta loss) :
    exists trace : SourceDirectPaidTrace Q h loss initial,
      trace.length <= sourceAssignedPotentialCeiling M h /\
      SourcePaidTerminal loss alpha gamma beta trace.last /\
      (forall j : Fin (trace.length + 1),
        (trace.state j).family <= initial.family /\
        (forall i, i ∈ (trace.state j).family ->
          ((trace.state j).shaded i).shade <= (initial.shaded i).shade) /\
        initial.mass <= loss ^ j.val * (trace.state j).mass /\
        initial.multiplicity <= loss ^ j.val * (trace.state j).multiplicity /\
        initial.fullness <= loss ^ j.val * (trace.state j).fullness /\
        (delta : ENNReal) ^ (2 * eta0) <= (trace.state j).fullness /\
        j.val + Q.assignedPotential h (trace.state j).family <=
          Q.assignedPotential h initial.family) /\
      loss ^ (trace.length + 1) <= loss ^ (sourceAssignedPotentialCeiling M h + 1) /\
      (initial.multiplicity <= (delta : ENNReal) ^ (-alpha - a0) \/
        initial.multiplicity <= (delta : ENNReal) ^ (gamma - a0) *
          (initial.family.card : ENNReal) ^ beta) := by
  classical
  have hret {x y : SourcePaidState S T Y} (step : SourceDirectPaidStep Q h loss x y) :
      x.multiplicity <= loss * y.multiplicity /\ x.fullness <= loss * y.fullness := by
    have hUnion : y.shadeUnion <= x.shadeUnion := by
      exact Set.iUnion₂_subset fun i hi =>
        Set.subset_iUnion₂_of_subset i (step.subset hi) (step.shade_subset i hi)
    have hcar : (∑ i ∈ y.family, volume (y.shaded i).carrier) <=
        ∑ i ∈ x.family, volume (x.shaded i).carrier := by
      have heq : forall i, (y.shaded i).carrier = (x.shaded i).carrier := by
        intro i
        rw [y.same_tubes, x.same_tubes]
      simp_rw [heq]
      exact Finset.sum_le_sum_of_subset step.subset
    constructor
    · change ShadedBody.multiplicity _ _ <= loss * ShadedBody.multiplicity _ _
      rw [ShadedBody.multiplicity_eq_div, ShadedBody.multiplicity_eq_div, ← mul_div_assoc]
      exact ENNReal.div_le_div step.weighted_mass (measure_mono hUnion)
    · change x.mass / _ <= loss * (y.mass / _)
      rw [← mul_div_assoc]
      exact ENNReal.div_le_div step.weighted_mass hcar
  have hledger (trace : SourceDirectPaidTrace Q h loss initial)
      (j : Fin (trace.length + 1)) :
      (trace.state j).family <= initial.family /\
      (forall i, i ∈ (trace.state j).family ->
        ((trace.state j).shaded i).shade <= (initial.shaded i).shade) /\
      initial.mass <= loss ^ j.val * (trace.state j).mass /\
      initial.multiplicity <= loss ^ j.val * (trace.state j).multiplicity /\
      initial.fullness <= loss ^ j.val * (trace.state j).fullness /\
      j.val + Q.assignedPotential h (trace.state j).family <=
        Q.assignedPotential h initial.family := by
    induction j using Fin.induction with
    | zero =>
        simp only [trace.start, Fin.val_zero, zero_add, pow_zero, one_mul]
        exact ⟨le_rfl, fun _ _ => le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩
    | succ j ih =>
        obtain ⟨hs, hz, hm, hmu, hf, hp⟩ := ih
        have step := trace.step j
        obtain ⟨hmu', hf'⟩ := hret step
        refine ⟨step.subset.trans hs,
          fun i hi => (step.shade_subset i hi).trans (hz i (step.subset hi)),
          ?_, ?_, ?_, ?_⟩
        · calc initial.mass <= loss ^ j.val * (trace.state j.castSucc).mass := hm
            _ <= loss ^ j.val * (loss * (trace.state j.succ).mass) :=
              mul_le_mul_right step.weighted_mass _
            _ = loss ^ j.succ.val * (trace.state j.succ).mass := by
              rw [Fin.val_succ, pow_succ, mul_assoc]
        · calc initial.multiplicity <= loss ^ j.val *
                (trace.state j.castSucc).multiplicity := hmu
            _ <= loss ^ j.val * (loss * (trace.state j.succ).multiplicity) :=
              mul_le_mul_right hmu' _
            _ = loss ^ j.succ.val * (trace.state j.succ).multiplicity := by
              rw [Fin.val_succ, pow_succ, mul_assoc]
        · calc initial.fullness <= loss ^ j.val * (trace.state j.castSucc).fullness := hf
            _ <= loss ^ j.val * (loss * (trace.state j.succ).fullness) :=
              mul_le_mul_right hf' _
            _ = loss ^ j.succ.val * (trace.state j.succ).fullness := by
              rw [Fin.val_succ, pow_succ, mul_assoc]
        · have hp' := step.potential_drop
          change j.val + 1 + _ <= _
          simp only [Fin.val_castSucc] at hp
          omega
  have hP := source_assignedPotential_le_fixed_ceiling Q initial.subset hd0 hd1 hh hcard
  have hdne : (delta : ENNReal) ≠ 0 := by exact_mod_cast hd0.ne'
  have hdtop : (delta : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hfullness (trace : SourceDirectPaidTrace Q h loss initial)
      (j : Fin (trace.length + 1)) :
      (delta : ENNReal) ^ (2 * eta0) <= (trace.state j).fullness := by
    obtain ⟨_, _, _, _, hf, hp⟩ := hledger trace j
    have hj : j.val <= sourceAssignedPotentialCeiling M h + 1 := by omega
    have hlpow : loss ^ j.val <= (delta : ENNReal) ^ (-a0) :=
      (pow_le_pow_right₀ hloss hj).trans hpay
    have hpaid : (delta : ENNReal) ^ eta0 <=
        (delta : ENNReal) ^ (-a0) * (trace.state j).fullness :=
      hfull.trans (hf.trans (mul_le_mul_left hlpow _))
    have hmargin : (delta : ENNReal) ^ (2 * eta0) <=
        (delta : ENNReal) ^ (eta0 + a0) :=
      ENNReal.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hd1.le) (by linarith)
    apply hmargin.trans
    have hm := mul_le_mul_right hpaid ((delta : ENNReal) ^ a0)
    rw [← ENNReal.rpow_add _ _ hdne hdtop, ← mul_assoc,
      ← ENNReal.rpow_add _ _ hdne hdtop, add_neg_cancel, ENNReal.rpow_zero, one_mul] at hm
    simpa [add_comm] using hm
  have hex : forall n : Nat, forall trace : SourceDirectPaidTrace Q h loss initial,
      Q.assignedPotential h trace.last.family = n ->
      exists final : SourceDirectPaidTrace Q h loss initial,
        final.length <= Q.assignedPotential h initial.family /\
        SourcePaidTerminal loss alpha gamma beta final.last := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro trace hn
        have ledger := hledger trace (Fin.last trace.length)
        have full := hfullness trace (Fin.last trace.length)
        rcases htrial trace.last full with hterminal | ⟨y, hstep⟩
        · refine ⟨trace, ?_, hterminal⟩
          have hp := ledger.2.2.2.2.2
          simp only [Fin.val_last] at hp
          omega
        · let next : SourceDirectPaidTrace Q h loss initial := {
            length := trace.length + 1
            state := Fin.snoc trace.state y
            start := by simpa using trace.start
            step := by
              intro j
              induction j using Fin.lastCases with
              | last => simpa [SourceDirectPaidTrace.last] using hstep
              | cast j => simpa [← Fin.castSucc_succ] using trace.step j }
          have hlast : next.last = y := by simp [next, SourceDirectPaidTrace.last]
          have hdrop := hstep.potential_drop
          have hlt : Q.assignedPotential h next.last.family < n := by
            rw [hlast]
            omega
          exact ih _ hlt next rfl
  let start : SourceDirectPaidTrace Q h loss initial := {
    length := 0
    state := fun _ => initial
    start := rfl
    step := Fin.elim0 }
  obtain ⟨trace, hk, hterminal⟩ := hex _ start rfl
  have hlength := hk.trans hP
  have hloss' : loss ^ (trace.length + 1) <=
      loss ^ (sourceAssignedPotentialCeiling M h + 1) :=
    pow_le_pow_right₀ hloss (by omega)
  refine ⟨trace, hlength, hterminal, ?_, hloss', ?_⟩
  · intro j
    obtain ⟨hs, hz, hm, hmu, hf, hp⟩ := hledger trace j
    exact ⟨hs, hz, hm, hmu, hf, hfullness trace j, hp⟩
  · obtain ⟨hsub, _, _, hmu, _, _⟩ := hledger trace (Fin.last trace.length)
    change initial.multiplicity <= loss ^ trace.length * trace.last.multiplicity at hmu
    have hpaid := hloss'.trans hpay
    rcases hterminal with hsticky | hgain
    · left
      calc initial.multiplicity <= loss ^ trace.length * trace.last.multiplicity := hmu
        _ <= loss ^ trace.length * (loss * (delta : ENNReal) ^ (-alpha)) :=
          mul_le_mul_right hsticky _
        _ = loss ^ (trace.length + 1) * (delta : ENNReal) ^ (-alpha) := by
          rw [pow_succ, mul_assoc]
        _ <= (delta : ENNReal) ^ (-a0) * (delta : ENNReal) ^ (-alpha) :=
          mul_le_mul_left hpaid _
        _ = (delta : ENNReal) ^ (-alpha - a0) := by
          rw [← ENNReal.rpow_add _ _ hdne hdtop]
          congr 1
          ring
    · right
      have hc : (trace.last.family.card : ENNReal) ^ beta <=
          (initial.family.card : ENNReal) ^ beta :=
        ENNReal.rpow_le_rpow (by exact_mod_cast Finset.card_le_card hsub) hbeta
      calc initial.multiplicity <= loss ^ trace.length * trace.last.multiplicity := hmu
        _ <= loss ^ trace.length *
            (loss * (delta : ENNReal) ^ gamma * (trace.last.family.card : ENNReal) ^ beta) :=
          mul_le_mul_right hgain _
        _ <= loss ^ trace.length *
            (loss * (delta : ENNReal) ^ gamma * (initial.family.card : ENNReal) ^ beta) := by
          gcongr
        _ = loss ^ (trace.length + 1) * (delta : ENNReal) ^ gamma *
            (initial.family.card : ENNReal) ^ beta := by rw [pow_succ]; ac_rfl
        _ <= (delta : ENNReal) ^ (-a0) * (delta : ENNReal) ^ gamma *
            (initial.family.card : ENNReal) ^ beta := by gcongr
        _ = (delta : ENNReal) ^ (gamma - a0) * (initial.family.card : ENNReal) ^ beta := by
          rw [← ENNReal.rpow_add _ _ hdne hdtop]
          congr 2
          ring

end Trace

/-- The actual once-centred entrance and direct trial law on one chosen Q.
The existing SourceFixedQDescentRun has a stronger coordinate-step law;
its protected data is unchanged and is not implicitly reconstructed here. -/
structure SourceDirectFixedQRun {beta c : Real} (P : SourcePaidDescentParameters beta c)
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
  actual_trial : SourceDirectPaidTrialLaw normalized tower P.h P.eta0
    (P.stickyAccuracy + P.stickyPayment) P.gain beta (P.loss (delta / 2))

/-- Produce the actual canonical family, full entrance and chosen fixed Q
from the unchanged Dichotomy domain, using the supplied direct trial law. -/
theorem source_exists_direct_fixedQ_run {beta c : Real}
    (P : SourcePaidDescentParameters beta c)
    (htrial : ∀ᶠ d : NNReal in 𝓝[>] 0,
      forall {iota : Type u} (S : Finset iota)
        (T : iota -> Tube d (EuclideanSpace Real (Fin 3)))
        (Q : SourceThreadedTower S T P.M sourceThreadConstant)
        (Y : iota -> ShadedTube d (EuclideanSpace Real (Fin 3))),
      SourceFixedTowerInput Q sourceBottomED sourceLevelED P.eta0 ->
      SourceDirectPaidTrialLaw Y Q P.h P.eta0
        (P.stickyAccuracy + P.stickyPayment) P.gain beta (P.loss d)) :
    ∀ᶠ delta : NNReal in 𝓝[>] 0,
      forall {iota : Type u} (S : Finset iota)
        (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))),
      (forall i, i ∈ S -> (Z i).carrier <= Metric.closedBall 0 1) ->
      IsKatzTao S (fun i => (Z i).toConvexSpaceBody) ((delta : ENNReal) ^ (-P.eta)) ->
      delta ^ P.eta <= ShadedBody.fullness S (fun i => (Z i).toShadedBody) ->
      (delta : Real)⁻¹ <= (S.card : Real) ->
      Nonempty (SourceDirectFixedQRun P S Z) := by
  classical
  obtain ⟨dt, hdt, hdt1, htower⟩ := source_exists_onceCentred_fixedTower P.M
    P.levels_ge_two P.entrance_payment_pos P.entrance_fullness_budget
  obtain ⟨dn, C3, hdn, _, _, hnested⟩ :=
    source_exists_unselected_nested_fixedTower P.M P.levels_ge_two
  have hhalf : Tendsto (fun delta : NNReal => delta / 2) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa only [id_eq, zero_div] using
        ((continuous_id.tendsto (0 : NNReal)).div_const (2 : NNReal)).mono_left
          (nhdsWithin_le_nhds (s := Set.Ioi (0 : NNReal)))
    · filter_upwards [self_mem_nhdsWithin] with delta hd
      change 0 < delta / 2
      exact div_pos hd (by norm_num)
  have hC := Kakeya.VeryNotSticky.eventually_ennreal_le_rpow_neg
    (K := (Kakeya.Tube.card_le_of_densityIn_le.C 3 : ENNReal)) ENNReal.coe_ne_top
    (by norm_num : (0 : Real) < 1)
  filter_upwards [Ioo_mem_nhdsGT hdt, hhalf.eventually (Ioo_mem_nhdsGT hdn),
    hhalf.eventually htrial, hC] with delta hd hn htrial hC
  intro iota S Z hball hKT hfull hcard
  have hd1 : delta <= 1 := (hd.2.le.trans hdt1).trans (by
    norm_num [div_le_iff₀ (show (0 : NNReal) < 200 by norm_num)])
  have hd1e : (delta : ENNReal) <= 1 := by exact_mod_cast hd1
  have hSne : S.Nonempty := by
    apply Finset.card_pos.mp
    have hdreal : (0 : Real) < delta := by exact_mod_cast hd.1
    have hpos : (0 : Real) < S.card := (inv_pos.mpr hdreal).trans_le hcard
    exact_mod_cast hpos
  have hmax : Kakeya.maxDensity S (fun i => (Z i).toConvexSpaceBody) <=
      (delta : ENNReal) ^ (-P.q) :=
    hKT.trans (ENNReal.rpow_le_rpow_of_exponent_ge hd1e
      (by linarith [P.dichotomy_exponent_le_entrance]))
  have hfull' : (delta : ENNReal) ^ P.q <=
      ShadedBody.fullness' S (fun i => (Z i).toShadedBody) := by
    have he := (ENNReal.coe_le_coe.mpr hfull)
    rw [ENNReal.coe_rpow_of_nonneg _ P.dichotomy_exponent_pos.le,
      ShadedBody.coe_fullness] at he
    exact (ENNReal.rpow_le_rpow_of_exponent_ge hd1e
      P.dichotomy_exponent_le_entrance).trans he
  obtain ⟨I, R, Y, pi, Qold, hnorm, hRI, hRne, _, hmass, hcost, hmult, hRc, hdens, hRf⟩ :=
    htower delta hd.1 hd.2 S Z hSne hball hmax hfull'
  obtain ⟨Q, hgeom, hneighbours, _⟩ := hnested (delta / 2) hn.1 hn.2 R
    (fun i => (Y i).toTube) hRne (hnorm.body_injective.mono hRI)
    (fun i hi => hnorm.centred i (hRI hi)) (fun i hi => hnorm.ball i (hRI hi))
    (hnorm.ed.subset hRI)
  have hmasspos : 0 < ∑ i ∈ R, volume (Y i).shade := by
    apply pos_iff_ne_zero.mpr
    intro hz
    have hfzero : ShadedBody.fullness' R (fun i => (Y i).toShadedBody) = 0 := by
      simp only [ShadedBody.fullness', hz, ENNReal.zero_div]
    exact (ENNReal.rpow_pos (by exact_mod_cast hn.1) ENNReal.coe_ne_top).ne'
      (le_antisymm (hfzero ▸ hRf) zero_le)
  let initial : SourcePaidState R (fun i => (Y i).toTube) Y := {
    family := R
    shaded := Y
    subset := le_rfl
    nonempty := hRne
    same_tubes := fun _ => rfl
    shade_subset := fun _ _ => le_rfl
    mass_pos := hmasspos }
  have hcardS := ML2Assembly.card_le_rpow_neg_four hd.1 hd1 hC S Z hball
    P.dichotomy_exponent_le_one hKT
  have hcardR : (R.card : Real) <= ((delta / 2 : NNReal) : Real) ^ (-5 : Real) := by
    have hhalfR : ((delta / 2 : NNReal) : Real) <= (delta : Real) := by
      simp only [NNReal.coe_div, NNReal.coe_ofNat]
      linarith [show (0 : Real) <= delta from delta.coe_nonneg]
    have hdreal : (0 : Real) < delta := by exact_mod_cast hd.1
    have hhreal : (0 : Real) < (delta / 2 : NNReal) := by exact_mod_cast hn.1
    calc (R.card : Real) <= (S.card : Real) := by exact_mod_cast hRc
      _ <= (delta : Real) ^ (-4 : Real) := hcardS
      _ <= (delta : Real) ^ (-5 : Real) :=
        Real.rpow_le_rpow_of_exponent_ge hdreal (by exact_mod_cast hd1) (by norm_num)
      _ <= ((delta / 2 : NNReal) : Real) ^ (-5 : Real) :=
        Real.rpow_le_rpow_of_nonpos hhreal hhalfR (by norm_num)
  have hinput : SourceFixedTowerInput Q sourceBottomED sourceLevelED P.eta0 := by
    refine ⟨hgeom, hneighbours, ?_⟩
    rw [← ENNReal.ofReal_rpow_of_pos (by exact_mod_cast hn.1 :
      (0 : Real) < (delta / 2 : NNReal)), ENNReal.ofReal_coe_nnreal]
    exact hdens
  exact ⟨{
    canonicalFamily := I
    initialFamily := R
    normalized := Y
    normalizationMap := pi
    normalization := hnorm
    initial_subset := hRI
    tower := Q
    geometry := hgeom
    neighbour_sharing := hneighbours
    tower_mass_retention := hmass
    entrance_cost := hcost
    initial := initial
    initial_family_identity := rfl
    initial_shading_identity := rfl
    entrance_multiplicity := hmult
    original_cardinality := hRc
    original_density := hdens
    initial_fullness := hRf
    initial_cardinality_bound := hcardR
    actual_trial := htrial R (fun i => (Y i).toTube) Q Y hinput }⟩

end Kakeya.ML2Core

namespace Kakeya.ML2Assembly

open Kakeya.ML2Core

universe u

/-- The direct trace uses the existing scalar budgets and half-scale payment
to reach precisely the old mass-form Dichotomy, without changing its domain. -/
theorem source_direct_dichotomy_of_fixedQ_runs {beta c : Real}
    (P : SourcePaidDescentParameters beta c) (hbeta : 0 <= beta) (hc : 0 < c)
    (hruns : ∀ᶠ delta : NNReal in 𝓝[>] 0,
      forall {iota : Type u} (S : Finset iota)
        (Z : iota -> ShadedTube delta (EuclideanSpace Real (Fin 3))),
      (forall i, i ∈ S -> (Z i).carrier <= Metric.closedBall 0 1) ->
      IsKatzTao S (fun i => (Z i).toConvexSpaceBody) ((delta : ENNReal) ^ (-P.eta)) ->
      delta ^ P.eta <= ShadedBody.fullness S (fun i => (Z i).toShadedBody) ->
      (delta : Real)⁻¹ <= (S.card : Real) ->
      Nonempty (SourceDirectFixedQRun P S Z)) :
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
  filter_upwards [hruns, hloss, source_eventually_half_scale_terminal_payment P hc]
    with delta hruns hloss hpayment
  intro iota S Z hball hKT hfull hcard
  obtain ⟨run⟩ := hruns S Z hball hKT hfull hcard
  obtain ⟨trace, _, _, _, _, hbound⟩ := source_direct_paid_descent_bound run.tower run.initial
    P.potential_step_pos hloss.1 hloss.2.1 hloss.2.2.1 hloss.2.2.2.1
    P.input_ceiling_pos P.descent_payment_pos P.descent_payment_le hbeta
    run.initial_cardinality_bound run.initial_fullness hloss.2.2.2.2 run.actual_trial
  have hdne : (((delta / 2 : NNReal) : ENNReal)) ≠ 0 := by exact_mod_cast hloss.1.ne'
  have hdtop : (((delta / 2 : NNReal) : ENNReal)) ≠ ⊤ := ENNReal.coe_ne_top
  rcases hbound with hsticky | hgain
  · left
    apply (ShadedBody.multiplicity_le_iff S (fun i => (Z i).toShadedBody)).mp
    calc ShadedBody.multiplicity S (fun i => (Z i).toShadedBody) <=
          (((delta / 2 : NNReal) : ENNReal)) ^ (-(3 * P.q)) * run.initial.multiplicity :=
        run.entrance_multiplicity
      _ <= (((delta / 2 : NNReal) : ENNReal)) ^ (-(3 * P.q)) *
          (((delta / 2 : NNReal) : ENNReal)) ^
            (-(P.stickyAccuracy + P.stickyPayment) - P.a0) :=
        mul_le_mul_right hsticky _
      _ = (((delta / 2 : NNReal) : ENNReal)) ^
          (-(P.stickyAccuracy + P.stickyPayment) - 3 * P.q - P.a0) := by
        rw [← ENNReal.rpow_add _ _ hdne hdtop]
        congr 1
        ring
      _ <= (delta : ENNReal) ^ (-(beta / 2)) := hpayment.2.2.1
  · right
    apply (ShadedBody.multiplicity_le_iff S (fun i => (Z i).toShadedBody)).mp
    have hcard' : (run.initial.family.card : ENNReal) ^ beta <= (S.card : ENNReal) ^ beta := by
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
      _ = (((delta / 2 : NNReal) : ENNReal)) ^ (P.gain - 3 * P.q - P.a0) *
            (S.card : ENNReal) ^ beta := by
        rw [← mul_assoc, ← ENNReal.rpow_add _ _ hdne hdtop]
        congr 2
        ring
      _ <= (delta : ENNReal) ^ (4 * c) * (S.card : ENNReal) ^ beta :=
        mul_le_mul_left hpayment.2.2.2 _

end Kakeya.ML2Assembly
