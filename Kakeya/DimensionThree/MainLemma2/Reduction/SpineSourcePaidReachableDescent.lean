/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceAssignedProfile
public import Mathlib.Logic.Relation

@[expose] public section

open MeasureTheory Metric Topology Filter ConvexSpaceBody ShadedBody Tube ShadedTube
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

universe u

/-- The fixed number of assigned level pairs, with the source height bound five. -/
noncomputable def sourceAssignedPotentialCeiling (M : Nat) (h : Real) : Nat :=
  (M * (M + 1) / 2) * Nat.ceil (5 / h)

section FixedTower

variable {iota : Type u} {d : NNReal} {ambient : Finset iota}
  {T : iota -> Tube d (EuclideanSpace Real (Fin 3))} {M C : Nat}

/-- Cardinality of the actual assigned images bounds every finite density profile. -/
theorem source_assignedProfile_le_retained_card
    (Q : SourceThreadedTower ambient T M C) (R : Finset iota) (a b : Nat) :
    Q.assignedProfile R a b <= (R.card : ENNReal) := by
  classical
  refine Finset.sup_le fun j _ => ?_
  refine (Kakeya.maxDensity_le_card _ _).trans ?_
  exact_mod_cast (Finset.card_image_le.trans (Finset.card_filter_le R _))

/-- The source logarithm is finite and lies in [0,5] after the actual leaf-card bound. -/
theorem source_assignedProfileExp_le_five
    (Q : SourceThreadedTower ambient T M C) {R : Finset iota}
    (hR : R <= ambient) (hd0 : 0 < d) (hd1 : d < 1)
    (hcard : (ambient.card : Real) <= (d : Real) ^ (-5 : Real)) (a b : Nat) :
    0 <= Q.assignedProfileExp R a b /\ Q.assignedProfileExp R a b <= 5 := by
  have hfinite := source_assignedProfile_ne_top Q R a b
  have hnn := profileExp_nonneg hd0 hd1 (Q.assignedProfile R a b)
  have hle : (Q.assignedProfile R a b).toReal <= (1 / (d : Real)) ^ (5 : Real) := by
    calc (Q.assignedProfile R a b).toReal <= (R.card : Real) := by
          simpa using ENNReal.toReal_mono (ENNReal.natCast_ne_top R.card)
            (source_assignedProfile_le_retained_card Q R a b)
      _ <= (ambient.card : Real) := by exact_mod_cast Finset.card_le_card hR
      _ <= (d : Real) ^ (-5 : Real) := hcard
      _ = (1 / (d : Real)) ^ (5 : Real) := by
          rw [one_div, Real.inv_rpow (by positivity), Real.rpow_neg (by positivity)]
  have hbound := profileExp_le_of_toReal_le hd0 hd1 hfinite (by norm_num : (0 : Real) <= 5) hle
  simpa only [profileExp_of_ne_top hfinite, SourceThreadedTower.assignedProfileExp] using
    And.intro hnn hbound

/-- Source S:5782-5789,6120-6136: the ceiling depends on M,h, not the scale. -/
theorem source_assignedPotential_le_fixed_ceiling
    (Q : SourceThreadedTower ambient T M C) {R : Finset iota}
    (hR : R <= ambient) (hd0 : 0 < d) (hd1 : d < 1) {h : Real} (hh : 0 < h)
    (hcard : (ambient.card : Real) <= (d : Real) ^ (-5 : Real)) :
    Q.assignedPotential h R <= sourceAssignedPotentialCeiling M h := by
  classical
  unfold SourceThreadedTower.assignedPotential
  calc _ <= ∑ _p ∈ (Finset.range (M + 1) ×ˢ Finset.range (M + 1)).filter
          (fun p => p.1 < p.2), Nat.ceil (5 / h) := by
        refine Finset.sum_le_sum fun p _ => Nat.ceil_le_ceil ?_
        exact div_le_div_of_nonneg_right
          (source_assignedProfileExp_le_five Q hR hd0 hd1 hcard p.1 p.2).2 hh.le
    _ = sourceAssignedPotentialCeiling M h := by
        rw [Finset.sum_const, smul_eq_mul, card_pairs_lt, sourceAssignedPotentialCeiling]

/-- A state retains actual tube identities and shades inside the fixed initial shading. -/
structure SourcePaidState (ambient : Finset iota)
    (T : iota -> Tube d (EuclideanSpace Real (Fin 3)))
    (Y : iota -> ShadedTube d (EuclideanSpace Real (Fin 3))) where
  family : Finset iota
  shaded : iota -> ShadedTube d (EuclideanSpace Real (Fin 3))
  subset : family <= ambient
  nonempty : family.Nonempty
  same_tubes : ∀ i, (shaded i).toTube = T i
  shade_subset : ∀ i ∈ family, (shaded i).shade <= (Y i).shade
  mass_pos : 0 < ∑ i ∈ family, volume (shaded i).shade

variable {Y : iota -> ShadedTube d (EuclideanSpace Real (Fin 3))}

noncomputable def SourcePaidState.mass (x : SourcePaidState ambient T Y) : ENNReal :=
  ∑ i ∈ x.family, volume (x.shaded i).shade

noncomputable def SourcePaidState.fullness (x : SourcePaidState ambient T Y) : ENNReal :=
  ShadedBody.fullness' x.family (fun i => (x.shaded i).toShadedBody)

noncomputable def SourcePaidState.multiplicity (x : SourcePaidState ambient T Y) : ENNReal :=
  ShadedBody.multiplicity x.family (fun i => (x.shaded i).toShadedBody)

def SourcePaidState.shadeUnion (x : SourcePaidState ambient T Y) :
    Set (EuclideanSpace Real (Fin 3)) :=
  ⋃ i ∈ x.family, (x.shaded i).shade

open scoped Classical in
/-- One recorded cut keeps whole CURRENT assigned fibres at its named source level.
It makes no claim that arbitrary cuts preserve earlier statistical regularity. -/
def SourceWholeFibreCut (Q : SourceThreadedTower ambient T M C)
    (S R : Finset iota) : Prop :=
  ∃ k : Nat, k <= M /\ ∃ selected : Finset iota,
    selected <= Q.assignedFootprint S k /\
    R = S.filter (fun i => Q.place k i ∈ selected)

/-- A paid drop carries the actual selected family, shade restriction and weighted mass.
The coordinate drop is on Q itself. Multiplicity/fullness retention are derived below. -/
structure SourcePaidStep (Q : SourceThreadedTower ambient T M C)
    (h : Real) (loss : ENNReal) (x y : SourcePaidState ambient T Y) : Prop where
  subset : y.family <= x.family
  whole_fibre_selections : Relation.ReflTransGen (SourceWholeFibreCut Q) x.family y.family
  shade_subset : ∀ i ∈ y.family, (y.shaded i).shade <= (x.shaded i).shade
  weighted_mass : x.mass <= loss * y.mass
  coordinate_drop : ∃ a b : Nat, a < b /\ b <= M /\
    Q.assignedProfileExp y.family a b + 2 * h <= Q.assignedProfileExp x.family a b

/-- These rows follow from the actual mass and restrictions; multiplicity alone is insufficient. -/
theorem source_paidStep_retention
    (Q : SourceThreadedTower ambient T M C) {h : Real} {loss : ENNReal}
    {x y : SourcePaidState ambient T Y} (hstep : SourcePaidStep Q h loss x y) :
    x.multiplicity <= loss * y.multiplicity /\
    x.fullness <= loss * y.fullness /\
    y.family.card <= x.family.card /\ y.shadeUnion <= x.shadeUnion := by
  have hUnion : y.shadeUnion <= x.shadeUnion := by
    exact Set.iUnion₂_subset fun i hi => Set.subset_iUnion₂_of_subset i (hstep.subset hi)
      (hstep.shade_subset i hi)
  have hcar : (∑ i ∈ y.family, volume (y.shaded i).carrier) <=
      ∑ i ∈ x.family, volume (x.shaded i).carrier := by
    have heq : ∀ i, (y.shaded i).carrier = (x.shaded i).carrier := by
      intro i
      rw [y.same_tubes, x.same_tubes]
    simp_rw [heq]
    exact Finset.sum_le_sum_of_subset hstep.subset
  refine ⟨?_, ?_, Finset.card_le_card hstep.subset, hUnion⟩
  · change ShadedBody.multiplicity _ _ <= loss * ShadedBody.multiplicity _ _
    rw [ShadedBody.multiplicity_eq_div, ShadedBody.multiplicity_eq_div, ← mul_div_assoc]
    exact ENNReal.div_le_div hstep.weighted_mass (measure_mono hUnion)
  · change x.mass / _ <= loss * (y.mass / _)
    rw [← mul_div_assoc]
    exact ENNReal.div_le_div hstep.weighted_mass hcar

/-- The actual nontruncated two-h coordinate drop gives one strict natural descent. -/
theorem source_paidStep_potential_drop
    (Q : SourceThreadedTower ambient T M C) {h : Real} {loss : ENNReal}
    {x y : SourcePaidState ambient T Y} (hh : 0 < h) (hd0 : 0 < d) (hd1 : d < 1)
    (hstep : SourcePaidStep Q h loss x y) :
    Q.assignedPotential h y.family + 1 <= Q.assignedPotential h x.family := by
  obtain ⟨a, b, hab, hb, hdrop⟩ := hstep.coordinate_drop
  exact source_assignedPotential_drop Q hstep.subset hh hd0 hd1 hab hb hdrop

/-- A finite sequence with an actual paid step at every successor and its starting identity. -/
structure SourcePaidTrace (Q : SourceThreadedTower ambient T M C)
    (h : Real) (loss : ENNReal) (initial : SourcePaidState ambient T Y) where
  length : Nat
  state : Fin (length + 1) -> SourcePaidState ambient T Y
  start : state 0 = initial
  step : ∀ j : Fin length, SourcePaidStep Q h loss (state j.castSucc) (state j.succ)

def SourcePaidTrace.last {Q : SourceThreadedTower ambient T M C} {h : Real}
    {loss : ENNReal} {initial : SourcePaidState ambient T Y}
    (trace : SourcePaidTrace Q h loss initial) : SourcePaidState ambient T Y :=
  trace.state (Fin.last trace.length)

/-- Reachability is generated only by the paid source relation, with zero steps allowed. -/
def SourcePaidReachable (Q : SourceThreadedTower ambient T M C) (h : Real)
    (loss : ENNReal) (initial x : SourcePaidState ambient T Y) : Prop :=
  Relation.ReflTransGen (SourcePaidStep Q h loss) initial x

/-- A concrete trace gives reachability and the complete cumulative mass ledger at EVERY state. -/
theorem source_paidTrace_cumulative_ledger
    (Q : SourceThreadedTower ambient T M C) {h : Real} {loss : ENNReal}
    {initial : SourcePaidState ambient T Y} (trace : SourcePaidTrace Q h loss initial)
    (hh : 0 < h) (hd0 : 0 < d) (hd1 : d < 1) (hloss : 1 <= loss) :
    ∀ j : Fin (trace.length + 1),
      SourcePaidReachable Q h loss initial (trace.state j) /\
      (trace.state j).family <= initial.family /\
      (∀ i ∈ (trace.state j).family,
        ((trace.state j).shaded i).shade <= (initial.shaded i).shade) /\
      j.val + Q.assignedPotential h (trace.state j).family <=
        Q.assignedPotential h initial.family /\
      initial.mass <= loss ^ j.val * (trace.state j).mass /\
      initial.multiplicity <= loss ^ j.val * (trace.state j).multiplicity /\
      initial.fullness <= loss ^ j.val * (trace.state j).fullness /\
      (trace.state j).family.card <= initial.family.card /\
      (trace.state j).shadeUnion <= initial.shadeUnion := by
  intro j
  induction j using Fin.induction with
  | zero =>
      simp only [trace.start, Fin.val_zero, zero_add, pow_zero, one_mul]
      exact ⟨Relation.ReflTransGen.refl, le_rfl, fun _ _ => le_rfl, le_rfl,
        le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩
  | succ j ih =>
      obtain ⟨hr, hs, hz, hp, hm, hmu, hf, hc, hu⟩ := ih
      have step := trace.step j
      obtain ⟨hmu', hf', hc', hu'⟩ := source_paidStep_retention Q step
      have hp' := source_paidStep_potential_drop Q hh hd0 hd1 step
      refine ⟨hr.tail step, step.subset.trans hs,
        fun i hi => (step.shade_subset i hi).trans (hz i (step.subset hi)),
        ?_, ?_, ?_, ?_, hc'.trans hc, hu'.trans hu⟩
      · change j.val + 1 + _ <= _
        simp only [Fin.val_castSucc] at hp
        omega
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

/-- The fullness ladder is derived from a real trace and one fixed total-loss budget. -/
theorem source_paidTrace_fullness_ladder
    (Q : SourceThreadedTower ambient T M C) {h eta0 a0 : Real} {loss : ENNReal}
    {initial : SourcePaidState ambient T Y} (trace : SourcePaidTrace Q h loss initial)
    (hh : 0 < h) (hd0 : 0 < d) (hd1 : d < 1) (hloss : 1 <= loss)
    (hlossFinite : loss ≠ ⊤) (heta : 0 < eta0) (ha : 0 < a0) (haeta : a0 <= eta0)
    (hcard : (ambient.card : Real) <= (d : Real) ^ (-5 : Real))
    (hfull : (d : ENNReal) ^ eta0 <= initial.fullness)
    (hpay : loss ^ (sourceAssignedPotentialCeiling M h + 1) <= (d : ENNReal) ^ (-a0)) :
    ∀ j : Fin (trace.length + 1),
      (d : ENNReal) ^ eta0 <=
        loss ^ (sourceAssignedPotentialCeiling M h -
          Q.assignedPotential h (trace.state j).family) * (trace.state j).fullness /\
      (d : ENNReal) ^ (2 * eta0) <= (trace.state j).fullness := by
  intro j
  obtain ⟨_, _, _, hp, _, _, hf, _, _⟩ :=
    source_paidTrace_cumulative_ledger Q trace hh hd0 hd1 hloss j
  have hP := source_assignedPotential_le_fixed_ceiling Q initial.subset hd0 hd1 hh hcard
  have hj : j.val <= sourceAssignedPotentialCeiling M h -
      Q.assignedPotential h (trace.state j).family := by omega
  have hj' : j.val <= sourceAssignedPotentialCeiling M h + 1 := by omega
  have hlpow : loss ^ j.val <= (d : ENNReal) ^ (-a0) :=
    (pow_le_pow_right₀ hloss hj').trans hpay
  refine ⟨hfull.trans (hf.trans (mul_le_mul_left (pow_le_pow_right₀ hloss hj) _)), ?_⟩
  have hpaid : (d : ENNReal) ^ eta0 <=
      (d : ENNReal) ^ (-a0) * (trace.state j).fullness :=
    hfull.trans (hf.trans (mul_le_mul_left hlpow _))
  have hdne : (d : ENNReal) ≠ 0 := by exact_mod_cast hd0.ne'
  have hdtop : (d : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hmargin : (d : ENNReal) ^ (2 * eta0) <= (d : ENNReal) ^ (eta0 + a0) :=
    ENNReal.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hd1.le) (by linarith)
  apply hmargin.trans
  have hm := mul_le_mul_right hpaid ((d : ENNReal) ^ a0)
  rw [← ENNReal.rpow_add _ _ hdne hdtop, ← mul_assoc,
    ← ENNReal.rpow_add _ _ hdne hdtop, add_neg_cancel, ENNReal.rpow_zero, one_mul] at hm
  simpa [add_comm] using hm

/-- Actual terminal estimates, including ONE terminal loss. alpha is absolute Sticky accuracy;
gamma is the actual surviving positive analytic gain, never the positive-defect source bound. -/
def SourcePaidTerminal (loss : ENNReal) (alpha gamma beta : Real)
    (x : SourcePaidState ambient T Y) : Prop :=
  x.multiplicity <= loss * (d : ENNReal) ^ (-alpha) \/
    x.multiplicity <= loss * (d : ENNReal) ^ gamma * (x.family.card : ENNReal) ^ beta

/-- Explicit OPEN input of the conditional consumer: produce a real exit or paid child
for each state reached from this initial pair, once its fullness permits a trial. -/
def SourceReachablePaidTrialLaw (Q : SourceThreadedTower ambient T M C)
    (h eta0 alpha gamma beta : Real) (loss : ENNReal)
    (initial : SourcePaidState ambient T Y) : Prop :=
  ∀ x : SourcePaidState ambient T Y,
    SourcePaidReachable Q h loss initial x ->
    (d : ENNReal) ^ (2 * eta0) <= x.fullness ->
    SourcePaidTerminal loss alpha gamma beta x \/
      ∃ y : SourcePaidState ambient T Y, SourcePaidStep Q h loss x y

/-- Finite descent constructs the trace from the actual initial pair and a faithful step law.
It does not construct the geometric/analytic trial law supplied as htrial. -/
theorem source_exists_paid_terminal_trace
    (Q : SourceThreadedTower ambient T M C) (initial : SourcePaidState ambient T Y)
    {h eta0 a0 alpha gamma beta : Real} {loss : ENNReal}
    (hh : 0 < h) (hd0 : 0 < d) (hd1 : d < 1) (hloss : 1 <= loss)
    (hlossFinite : loss ≠ ⊤) (heta : 0 < eta0) (ha : 0 < a0) (haeta : a0 <= eta0)
    (hcard : (ambient.card : Real) <= (d : Real) ^ (-5 : Real))
    (hfull : (d : ENNReal) ^ eta0 <= initial.fullness)
    (hpay : loss ^ (sourceAssignedPotentialCeiling M h + 1) <= (d : ENNReal) ^ (-a0))
    (htrial : SourceReachablePaidTrialLaw Q h eta0 alpha gamma beta loss initial) :
    ∃ trace : SourcePaidTrace Q h loss initial,
      trace.length <= Q.assignedPotential h initial.family /\
      Q.assignedPotential h initial.family <= sourceAssignedPotentialCeiling M h /\
      SourcePaidTerminal loss alpha gamma beta trace.last := by
  classical
  have hP := source_assignedPotential_le_fixed_ceiling Q initial.subset hd0 hd1 hh hcard
  have hex : ∀ n : Nat, ∀ trace : SourcePaidTrace Q h loss initial,
      Q.assignedPotential h trace.last.family = n ->
      ∃ final : SourcePaidTrace Q h loss initial,
        final.length <= Q.assignedPotential h initial.family /\
        SourcePaidTerminal loss alpha gamma beta final.last := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro trace hn
        have ledger := source_paidTrace_cumulative_ledger Q trace hh hd0 hd1 hloss
          (Fin.last trace.length)
        have full := (source_paidTrace_fullness_ladder Q trace hh hd0 hd1 hloss
          hlossFinite heta ha haeta hcard hfull hpay (Fin.last trace.length)).2
        rcases htrial trace.last ledger.1 full with hterminal | ⟨y, hstep⟩
        · refine ⟨trace, ?_, hterminal⟩
          have hp := ledger.2.2.2.1
          simp only [Fin.val_last] at hp
          omega
        · let next : SourcePaidTrace Q h loss initial := {
            length := trace.length + 1
            state := Fin.snoc trace.state y
            start := by simpa using trace.start
            step := by
              intro j
              induction j using Fin.lastCases with
              | last => simpa [SourcePaidTrace.last] using hstep
              | cast j =>
                  simpa [← Fin.castSucc_succ] using trace.step j }
          have hlast : next.last = y := by simp [next, SourcePaidTrace.last]
          have hdrop := source_paidStep_potential_drop Q hh hd0 hd1 hstep
          have hlt : Q.assignedPotential h next.last.family < n := by
            rw [hlast]
            omega
          exact ih _ hlt next rfl
  let start : SourcePaidTrace Q h loss initial := {
    length := 0
    state := fun _ => initial
    start := rfl
    step := Fin.elim0 }
  obtain ⟨trace, hlength, hterminal⟩ := hex _ start rfl
  exact ⟨trace, hlength, hP, hterminal⟩

/-- The last trial is paid at k+1; all state/cardinality changes are those of the actual trace. -/
theorem source_paid_terminal_trace_bound
    (Q : SourceThreadedTower ambient T M C) {initial : SourcePaidState ambient T Y}
    {h alpha gamma beta : Real} {loss : ENNReal}
    (trace : SourcePaidTrace Q h loss initial)
    (hh : 0 < h) (hd0 : 0 < d) (hd1 : d < 1) (hloss : 1 <= loss)
    (hbeta : 0 <= beta) (hterminal : SourcePaidTerminal loss alpha gamma beta trace.last) :
    initial.multiplicity <= loss ^ (trace.length + 1) * (d : ENNReal) ^ (-alpha) \/
      initial.multiplicity <= loss ^ (trace.length + 1) * (d : ENNReal) ^ gamma *
        (initial.family.card : ENNReal) ^ beta := by
  obtain ⟨_, _, _, _, _, hmu, _, hcard, _⟩ :=
    source_paidTrace_cumulative_ledger Q trace hh hd0 hd1 hloss (Fin.last trace.length)
  change initial.multiplicity <= loss ^ trace.length * trace.last.multiplicity at hmu
  rcases hterminal with hterminal | hterminal
  · left
    calc initial.multiplicity <= loss ^ trace.length * trace.last.multiplicity := hmu
      _ <= loss ^ trace.length * (loss * (d : ENNReal) ^ (-alpha)) :=
        mul_le_mul_right hterminal _
      _ = loss ^ (trace.length + 1) * (d : ENNReal) ^ (-alpha) := by
        rw [pow_succ, mul_assoc]
  · right
    have hcard' : (trace.last.family.card : ENNReal) ^ beta <=
        (initial.family.card : ENNReal) ^ beta :=
      ENNReal.rpow_le_rpow (by exact_mod_cast hcard) hbeta
    calc initial.multiplicity <= loss ^ trace.length * trace.last.multiplicity := hmu
      _ <= loss ^ trace.length *
          (loss * (d : ENNReal) ^ gamma * (trace.last.family.card : ENNReal) ^ beta) :=
        mul_le_mul_right hterminal _
      _ <= loss ^ trace.length *
          (loss * (d : ENNReal) ^ gamma * (initial.family.card : ENNReal) ^ beta) := by
        gcongr
      _ = loss ^ (trace.length + 1) * (d : ENNReal) ^ gamma *
          (initial.family.card : ENNReal) ^ beta := by rw [pow_succ]; ac_rfl

/-- This conditional descent packages the actual trace and the fully accumulated endpoint. -/
theorem source_paid_descent_bound
    (Q : SourceThreadedTower ambient T M C) (initial : SourcePaidState ambient T Y)
    {h eta0 a0 alpha gamma beta : Real} {loss : ENNReal}
    (hh : 0 < h) (hd0 : 0 < d) (hd1 : d < 1) (hloss : 1 <= loss)
    (hlossFinite : loss ≠ ⊤) (heta : 0 < eta0) (ha : 0 < a0) (haeta : a0 <= eta0)
    (hbeta : 0 <= beta)
    (hcard : (ambient.card : Real) <= (d : Real) ^ (-5 : Real))
    (hfull : (d : ENNReal) ^ eta0 <= initial.fullness)
    (hpay : loss ^ (sourceAssignedPotentialCeiling M h + 1) <= (d : ENNReal) ^ (-a0))
    (htrial : SourceReachablePaidTrialLaw Q h eta0 alpha gamma beta loss initial) :
    ∃ trace : SourcePaidTrace Q h loss initial,
      trace.length <= sourceAssignedPotentialCeiling M h /\
      SourcePaidTerminal loss alpha gamma beta trace.last /\
      loss ^ (trace.length + 1) <= loss ^ (sourceAssignedPotentialCeiling M h + 1) /\
      (initial.multiplicity <= (d : ENNReal) ^ (-alpha - a0) \/
        initial.multiplicity <= (d : ENNReal) ^ (gamma - a0) *
          (initial.family.card : ENNReal) ^ beta) := by
  obtain ⟨trace, hk, hP, hterminal⟩ := source_exists_paid_terminal_trace Q initial hh hd0
    hd1 hloss hlossFinite heta ha haeta hcard hfull hpay htrial
  have hlength := hk.trans hP
  have hloss' : loss ^ (trace.length + 1) <=
      loss ^ (sourceAssignedPotentialCeiling M h + 1) :=
    pow_le_pow_right₀ hloss (by omega)
  refine ⟨trace, hlength, hterminal, hloss', ?_⟩
  have hpaid := hloss'.trans hpay
  have hdne : (d : ENNReal) ≠ 0 := by exact_mod_cast hd0.ne'
  have hdtop : (d : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  rcases source_paid_terminal_trace_bound Q trace hh hd0 hd1 hloss hbeta hterminal
    with hsticky | hgain
  · left
    calc initial.multiplicity <= loss ^ (trace.length + 1) * (d : ENNReal) ^ (-alpha) :=
          hsticky
      _ <= (d : ENNReal) ^ (-a0) * (d : ENNReal) ^ (-alpha) :=
          mul_le_mul_left hpaid _
      _ = (d : ENNReal) ^ (-alpha - a0) := by
          rw [← ENNReal.rpow_add _ _ hdne hdtop]
          congr 1
          ring
  · right
    calc initial.multiplicity <= loss ^ (trace.length + 1) * (d : ENNReal) ^ gamma *
            (initial.family.card : ENNReal) ^ beta := hgain
      _ <= (d : ENNReal) ^ (-a0) * (d : ENNReal) ^ gamma *
            (initial.family.card : ENNReal) ^ beta := by gcongr
      _ = (d : ENNReal) ^ (gamma - a0) * (initial.family.card : ENNReal) ^ beta := by
          rw [← ENNReal.rpow_add _ _ hdne hdtop]
          congr 2
          ring

end FixedTower

end Kakeya.ML2Core
