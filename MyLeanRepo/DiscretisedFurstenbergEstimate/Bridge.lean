module

/-
  Bridge_Full_Filled.lean

  Full bridge between main repo B1 induction and standalone induction theorem.
  All sorrys filled using identity conversions and transfer parameters.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.DiscretisedFurstenbergEstimate.InductionConfigurations
public import MyLeanRepo.InductionOnScales.Definitions
public import MyLeanRepo.InductionOnScales.InductionStep
public import MyLeanRepo.InductionOnScales.SSet
public import MyLeanRepo.InductionOnScales.UniformSSet
public import MyLeanRepo.DiscretisedFurstenbergEstimate.BridgeGeometric
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FormatConversionLemmas
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

namespace DiscretisedFurstenbergEstimate.Bridge

open DirecretisedFurstenbergEstimate.FormatConversion.M2

-- Shorthands
abbrev MainSquare (n : ℕ) := DiscretisedFurstenbergEstimate.DyadicSquare n
abbrev MainTube (n : ℕ) := DiscretisedFurstenbergEstimate.DyadicTube n
abbrev MainConfig (n : ℕ) (s C : ℝ) (M : ℕ) :=
  DiscretisedFurstenbergEstimate.CombiningTheorem.NiceConfiguration n s C M
abbrev StandSquare (n : ℕ) := _root_.DyadicSquare n
abbrev StandTube (n : ℕ) := _root_.DyadicTube n
abbrev StandConfig (n : ℕ) (s C : ℝ) (M : ℕ) := _root_.NiceConfiguration n s C M

-- Identity conversions
def squareToStand {n} (p : MainSquare n) : StandSquare n := ⟨p.i, p.j⟩
def squareToMain {n} (p : StandSquare n) : MainSquare n := ⟨p.i, p.j⟩
def tubeToStand {n} (T : MainTube n) : StandTube n := ⟨T.a, T.b⟩
def tubeToMain {n} (T : StandTube n) : MainTube n := ⟨T.a, T.b⟩
/-- Shifted conversion: standalone cell C(a,b) maps to main strip S(a,b+1),
    which is the correct geometric containment for reverse incidence. -/
def tubeToMainShifted {n} (T : StandTube n) : MainTube n := ⟨T.a, T.b + 1⟩

lemma squareToStand_inj {n} : Function.Injective (@squareToStand n) := by
  intro p q h; have h1 := congr_arg (fun x : StandSquare n => x.i) h
  have h2 := congr_arg (fun x : StandSquare n => x.j) h
  cases p; cases q; simp [squareToStand] at h1 h2 ⊢ <;> aesop
lemma squareToMain_inj {n} : Function.Injective (@squareToMain n) := by
  intro p q h; have h1 := congr_arg (fun x : MainSquare n => x.i) h
  have h2 := congr_arg (fun x : MainSquare n => x.j) h
  cases p; cases q; simp [squareToMain] at h1 h2 ⊢ <;> aesop
lemma tubeToStand_inj {n} : Function.Injective (@tubeToStand n) := by
  intro T U h; have h1 := congr_arg (fun x : StandTube n => x.a) h
  have h2 := congr_arg (fun x : StandTube n => x.b) h
  cases T; cases U; simp [tubeToStand] at h1 h2 ⊢ <;> aesop
lemma tubeToMain_inj {n} : Function.Injective (@tubeToMain n) := by
  intro T U h; have h1 := congr_arg (fun x : MainTube n => x.a) h
  have h2 := congr_arg (fun x : MainTube n => x.b) h
  cases T; cases U; simp [tubeToMain] at h1 h2 ⊢ <;> aesop
lemma tubeToMainShifted_inj {n} : Function.Injective (@tubeToMainShifted n) := by
  intro T U h; have h1 := congr_arg (fun x : MainTube n => x.a) h
  have h2 := congr_arg (fun x : MainTube n => x.b) h
  cases T; cases U; simp [tubeToMainShifted] at h1 h2 ⊢ <;> aesop

/-- If a standalone dyadic tube is in the allowed parameter strip at scale m,
    then its shifted main-tube image has slope bounded by 1 in absolute value.
    The strip gives -(2^m) ≤ U.a < 2^m, and slope = U.a / 2^m, so -1 ≤ slope < 1. -/
lemma stand_strip_implies_main_slope_bound {m : ℕ} {U : StandTube m}
    (h_strip : U.IsInAllowedParameterStrip) :
    |(tubeToMainShifted U).slope| ≤ 1 := by
  have h1 : -((2 ^ m : ℕ) : ℤ) ≤ U.a := h_strip.1
  have h2 : U.a < ((2 ^ m : ℕ) : ℤ) := h_strip.2
  set two_pow : ℝ := (2 : ℝ) ^ m with htwo_pow_def
  have h_pos : (0 : ℝ) < two_pow := by positivity
  have h_cast : ((2 ^ m : ℕ) : ℝ) = two_pow := by
    simp [htwo_pow_def] <;> norm_cast
  have h1' : (-1 : ℝ) ≤ (U.a : ℝ) * (1 / two_pow) := by
    have h3 : (U.a : ℝ) ≥ -two_pow := by
      have h4 : (U.a : ℝ) ≥ -((2 ^ m : ℕ) : ℝ) := by exact_mod_cast h1
      rw [h_cast] at h4; exact h4
    have h5 : (U.a : ℝ) * (1 / two_pow) ≥ -two_pow * (1 / two_pow) := by gcongr
    have h6 : -two_pow * (1 / two_pow) = -1 := by
      field_simp [h_pos.ne'] <;> ring
    linarith
  have h2' : (U.a : ℝ) * (1 / two_pow) < 1 := by
    have h3 : (U.a : ℝ) < two_pow := by
      have h4 : (U.a : ℝ) < ((2 ^ m : ℕ) : ℝ) := by exact_mod_cast h2
      rw [h_cast] at h4; exact h4
    have h5 : (U.a : ℝ) * (1 / two_pow) < two_pow * (1 / two_pow) := by gcongr
    have h6 : two_pow * (1 / two_pow) = 1 := by
      field_simp [h_pos.ne'] <;> ring
    linarith
  have h_slope_eq : (tubeToMainShifted U).slope = (U.a : ℝ) * (1 / two_pow) := by
    simp [tubeToMainShifted, DyadicTube.slope, dyadicDelta, htwo_pow_def] <;> ring
  rw [h_slope_eq]
  rw [abs_le]
  constructor <;> linarith

lemma standToMainRoundtrip {n} (p : StandSquare n) :
    squareToStand (squareToMain p) = p := by
  cases p; simp [squareToStand, squareToMain] <;> rfl
lemma mainToStandRoundtrip {n} (p : MainSquare n) :
    squareToMain (squareToStand p) = p := by
  cases p; simp [squareToStand, squareToMain] <;> rfl
lemma standToMainTubeRoundtrip {n} (T : StandTube n) :
    tubeToStand (tubeToMain T) = T := by
  cases T; simp [tubeToStand, tubeToMain] <;> rfl
lemma mainToStandTubeRoundtrip {n} (T : MainTube n) :
    tubeToMain (tubeToStand T) = T := by
  cases T; simp [tubeToStand, tubeToMain] <;> rfl

/-- Reverse incidence: standalone exact cell C(a,b) intersects square Q (in unit square)
    implies main centered strip S(a,b+1) intersects the corresponding main square.
    Geometric reason: for (x,y) in C(a,b) ∩ [0,1)×[0,1), the deviation from the
    center line of S(a,b+1) is ds*x + di - δ ∈ (-δ, δ), where ds,di ∈ [0,δ). -/
lemma shifted_incidence {n : ℕ} (T : StandTube n) (Q : StandSquare n)
    (hQ_bounded : Q.toSet ⊆ _root_.unitSquare)
    (h_inc : (T.toSet ∩ Q.toSet).Nonempty) :
    ((tubeToMainShifted T).toSet ∩ (squareToMain Q).toSet).Nonempty := by
  rcases h_inc with ⟨p, hpT, hpQ⟩
  have hp_unit : p ∈ _root_.unitSquare := hQ_bounded hpQ
  have hx0 : 0 ≤ p.1 := hp_unit.1.1
  have hx1 : p.1 < 1 := hp_unit.1.2
  set δ : ℝ := _root_.dyadicDelta n with hδ_def
  have hδ_pos : 0 < δ := _root_.dyadicDelta_pos n
  have hδ_eq : δ = DiscretisedFurstenbergEstimate.dyadicDelta n := by
    simp [hδ_def, _root_.dyadicDelta, DiscretisedFurstenbergEstimate.dyadicDelta,
      Real.rpow_neg] <;> field_simp <;> norm_cast
  rcases hpT with ⟨slope, hs, intercept, hi, heq⟩
  have hs1 : (T.a : ℝ) * δ ≤ slope := hs.1
  have hs2 : slope < ((T.a + 1 : ℝ) * δ) := hs.2
  have hi1 : (T.b : ℝ) * δ ≤ intercept := hi.1
  have hi2 : intercept < ((T.b + 1 : ℝ) * δ) := hi.2
  let q : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then p.1 else p.2)
  have hq0 : q 0 = p.1 := by simp [q]
  have hq1 : q 1 = p.2 := by simp [q]
  have hq_square : q ∈ (squareToMain Q).toSet := by
    simp only [squareToMain, DiscretisedFurstenbergEstimate.DyadicSquare.toSet]
    have h_i1 : (Q.i : ℝ) * DiscretisedFurstenbergEstimate.dyadicDelta n ≤ q 0 := by
      rw [hq0, ←hδ_eq]; exact hpQ.1.1
    have h_i2 : q 0 < ((Q.i + 1 : ℝ) * DiscretisedFurstenbergEstimate.dyadicDelta n) := by
      rw [hq0, ←hδ_eq]; exact hpQ.1.2
    have h_j1 : (Q.j : ℝ) * DiscretisedFurstenbergEstimate.dyadicDelta n ≤ q 1 := by
      rw [hq1, ←hδ_eq]; exact hpQ.2.1
    have h_j2 : q 1 < ((Q.j + 1 : ℝ) * DiscretisedFurstenbergEstimate.dyadicDelta n) := by
      rw [hq1, ←hδ_eq]; exact hpQ.2.2
    exact ⟨h_i1, h_i2, h_j1, h_j2⟩
  set ds : ℝ := slope - (T.a : ℝ) * δ with hds
  set di : ℝ := intercept - (T.b : ℝ) * δ with hdi
  have hds0 : 0 ≤ ds := by linarith
  have hds1 : ds < δ := by linarith
  have hdi0 : 0 ≤ di := by linarith
  have hdi1 : di < δ := by linarith
  have hq_strip : q ∈ (tubeToMainShifted T).toSet := by
    simp only [tubeToMainShifted, DiscretisedFurstenbergEstimate.DyadicTube.toSet,
      DiscretisedFurstenbergEstimate.DyadicTube.slope,
      DiscretisedFurstenbergEstimate.DyadicTube.intercept]
    have h_goal : |q 1 - (T.a : ℝ) * DiscretisedFurstenbergEstimate.dyadicDelta n * q 0 -
        ((T.b + 1 : ℝ) * DiscretisedFurstenbergEstimate.dyadicDelta n)| ≤
        DiscretisedFurstenbergEstimate.dyadicDelta n := by
      rw [hq0, hq1, ←hδ_eq]
      have h_coerce : ((T.b + 1 : ℤ) : ℝ) = (T.b : ℝ) + 1 := by simp
      simp only [h_coerce] at *
      have h_eq2 : p.2 - (T.a : ℝ) * δ * p.1 - ((T.b : ℝ) + 1) * δ = ds * p.1 + di - δ := by
        simp [hds, hdi, heq] <;> ring
      rw [h_eq2]
      have h5 : 0 ≤ ds * p.1 := by positivity
      have h6 : ds * p.1 < δ := by nlinarith
      have h7 : -δ ≤ ds * p.1 + di - δ := by linarith
      have h8 : ds * p.1 + di - δ < δ := by linarith
      rw [abs_le] <;> constructor <;> linarith
    simpa [tubeToMainShifted, DiscretisedFurstenbergEstimate.DyadicTube.toSet,
      DiscretisedFurstenbergEstimate.DyadicTube.slope,
      DiscretisedFurstenbergEstimate.DyadicTube.intercept] using h_goal
  exact ⟨q, hq_strip, hq_square⟩

/-- Floor division by positive natural equals integer division for non-negative ints. -/
lemma floor_div_eq_int_div (a : ℤ) (ha : 0 ≤ a) (k : ℕ) (hk : 0 < k) :
    ⌊(a : ℝ) / (k : ℝ)⌋ = a / (k : ℤ) := by
  let q : ℤ := a / (k : ℤ)
  let r : ℤ := a % (k : ℤ)
  have hk' : (k : ℤ) > 0 := by exact_mod_cast hk
  have hdiv : a = q * (k : ℤ) + r := by
    have h : (a / (k : ℤ)) * (k : ℤ) + a % (k : ℤ) = a := by
      exact Int.ediv_mul_add_emod a ↑k
    linarith
  have hrem_nonneg : 0 ≤ r := Int.emod_nonneg a hk'.ne'
  have hrem_lt : r < (k : ℤ) := Int.emod_lt_of_pos a hk'
  have hpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hdiv' : (a : ℝ) = (q : ℝ) * (k : ℝ) + (r : ℝ) := by
    exact_mod_cast hdiv
  rw [Int.floor_eq_iff]
  constructor
  · have h : (q : ℝ) * (k : ℝ) ≤ (a : ℝ) := by
      rw [hdiv']
      have h_r_nonneg : 0 ≤ (r : ℝ) := by exact_mod_cast hrem_nonneg
      linarith
    calc (q : ℝ)
      = ((q : ℝ) * (k : ℝ)) / (k : ℝ) := by field_simp [hpos.ne'] <;> ring
    _ ≤ (a : ℝ) / (k : ℝ) := by gcongr
  · have h : (a : ℝ) < ((q : ℝ) + 1) * (k : ℝ) := by
      rw [hdiv']
      have h_r_lt : (r : ℝ) < (k : ℝ) := by exact_mod_cast hrem_lt
      linarith
    calc (a : ℝ) / (k : ℝ)
      < (((q : ℝ) + 1) * (k : ℝ)) / (k : ℝ) := by gcongr
    _ = (q : ℝ) + 1 := by field_simp [hpos.ne'] <;> ring

theorem inductionOnScalesBridge
    {n m : ℕ} (hnm : m ≤ n)
    (s : ℝ) (hs : 0 ≤ s) (hs_one : s ≤ 1)
    (C₁ : ℝ) (hC₁ : 1 ≤ C₁)
    (M : ℕ) (hM : 0 < M)
    (config : MainConfig n s C₁ M)
    (hP_nonempty : config.P₀.Nonempty)
    (h_squares_unit : ∀ p ∈ config.P₀,
      0 ≤ p.i ∧ p.i < (2 ^ n : ℤ) ∧ 0 ≤ p.j ∧ p.j < (2 ^ n : ℤ))
    (h_tubes_strip : ∀ T ∈ config.T₀,
      -(2 ^ n : ℤ) ≤ T.a ∧ T.a < (2 ^ n : ℤ))
    (h_tubes_bounded : config.T₀.card ≤ 12 * 16^n)
    (sset_transfer : ∀ (F : Finset (MainTube n)),
      IsDeltaSSet (DiscretisedFurstenbergEstimate.dyadicDelta n) s C₁ (F : Set (MainTube n)) →
      ∃ C', C' ≤ C₁ * 10 ∧ 1 ≤ C' ∧
        _root_.IsFiniteTubeSSet s C' (F.image tubeToStand))
    (incidence_transfer : ∀ (p : MainSquare n) (hp : p ∈ config.P₀)
      (T : MainTube n) (hT : T ∈ config.tubeFamily p hp),
      ((tubeToStand T).toSet ∩ (squareToStand p).toSet).Nonempty)
    (sset_transfer_rev : ∀ (k : ℕ) (C : ℝ), 1 ≤ C →
      ∀ (F : Finset (StandTube k)),
        _root_.IsFiniteTubeSSet s C F →
        IsDeltaSSet (DiscretisedFurstenbergEstimate.dyadicDelta k) s (5 * C)
          (F.image tubeToMainShifted : Set (MainTube k))) :
    ∃ (K : ℝ), 1 ≤ K ∧
      ∃ (P : Finset (MainSquare n))
      (hP_sub : P ⊆ config.P₀)
      (tubeFamily : (p : MainSquare n) → p ∈ P → Finset (MainTube n))
      (CΔ : ℝ) (MΔ : ℕ) (hMΔ : 0 < MΔ)
      (coarseConfig : MainConfig m s CΔ MΔ)
      (CQ : MainSquare m → ℝ)
      (MQ : MainSquare m → ℕ)
      (hMQ : ∀ Q ∈ coarseConfig.P₀, 0 < MQ Q)
      (fineConfig : (Q : MainSquare m) → Q ∈ coarseConfig.P₀ →
        MainConfig (n - m) s (CQ Q) (MQ Q))
      (fineConfig_B1 : (Q : MainSquare m) → (hQ : Q ∈ coarseConfig.P₀) →
        B1BridgeHypotheses (n - m) (fineConfig Q hQ)),
      P.Nonempty ∧
      coarseConfig.P₀ = P.image (InductionConfigurations.containingSquare hnm) ∧
      (∀ p hp, tubeFamily p hp ⊆ config.tubeFamily p (hP_sub hp) ∧
        (M : ℝ) ≤ K * ((tubeFamily p hp).card : ℝ)) ∧
      CΔ ≤ K * C₁ ∧
      (∀ Q ∈ coarseConfig.P₀, CQ Q ≤ K * C₁) ∧
      (∀ (Q : MainSquare m) (hQ : Q ∈ coarseConfig.P₀),
        K * (config.T₀.card : ℝ) * MΔ * MQ Q ≥
          (coarseConfig.T₀.card : ℝ) * ((fineConfig Q hQ).T₀.card : ℝ) * M) := by
  let C_stand := C₁ * 10
  have hC_stand_one : 1 ≤ C_stand := by linarith

  -- Helper: standalone point from image → main point in config.P₀
  have h_main_of_stand : ∀ (p : StandSquare n),
      p ∈ config.P₀.image squareToStand → squareToMain p ∈ config.P₀ := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨q, hq, h_eq⟩
    have h_eq2 : squareToMain p = q := by
      have h : squareToMain (squareToStand q) = q := mainToStandRoundtrip q
      simpa [h_eq] using h
    rw [h_eq2]
    exact hq

  -- Helper: p ∈ S.image squareToMain → squareToStand p ∈ S
  have h_mem_conv : ∀ {k : ℕ} {S : Finset (StandSquare k)} {p : MainSquare k},
      p ∈ S.image squareToMain → squareToStand p ∈ S := by
    intro k S p hp
    rcases Finset.mem_image.mp hp with ⟨q, hq, h_eq⟩
    have h_eq2 : squareToStand p = q := by
      have h : squareToStand (squareToMain q) = q := standToMainRoundtrip q
      simpa [h_eq] using h
    rw [h_eq2]
    exact hq

  -- Helper: index bounds → p.toSet ⊆ unitSquare
  have h_bounded_of_indices : ∀ (p : StandSquare n),
      0 ≤ p.i → p.i < (2 ^ n : ℤ) → 0 ≤ p.j → p.j < (2 ^ n : ℤ) →
      p.toSet ⊆ _root_.unitSquare := by
    intro p hi1 hi2 hj1 hj2 x hx
    set δ' := _root_.dyadicDelta n with hδ'_def
    have hδ'_pos : 0 < δ' := _root_.dyadicDelta_pos n
    have hδ'_one : ((2 ^ n : ℝ)) * δ' = 1 := by
      simp [hδ'_def, _root_.dyadicDelta, Real.rpow_neg, Real.rpow_natCast] <;> field_simp <;> ring
    have h_i_add1 : (p.i + 1 : ℤ) ≤ (2 ^ n : ℤ) := by linarith
    have h_j_add1 : (p.j + 1 : ℤ) ≤ (2 ^ n : ℤ) := by linarith
    constructor
    · constructor
      · have h_nonneg : 0 ≤ (p.i : ℝ) := by exact_mod_cast hi1
        have hδ'_nonneg : 0 ≤ δ' := by linarith
        have h : 0 ≤ (p.i : ℝ) * δ' := mul_nonneg h_nonneg hδ'_nonneg
        linarith [hx.1.1]
      · have h' : ((p.i + 1 : ℝ) * δ') ≤ ((2 ^ n : ℝ) * δ') := by
          gcongr <;> exact_mod_cast h_i_add1
        linarith [hδ'_one, hx.1.2]
    · constructor
      · have h_nonneg : 0 ≤ (p.j : ℝ) := by exact_mod_cast hj1
        have hδ'_nonneg : 0 ≤ δ' := by linarith
        have h : 0 ≤ (p.j : ℝ) * δ' := mul_nonneg h_nonneg hδ'_nonneg
        linarith [hx.2.1]
      · have h' : ((p.j + 1 : ℝ) * δ') ≤ ((2 ^ n : ℝ) * δ') := by
          gcongr <;> exact_mod_cast h_j_add1
        linarith [hδ'_one, hx.2.2]

  -- ==========================================================================
  -- Step 1: Construct standalone NiceConfiguration
  -- ==========================================================================
  let sconfig : StandConfig n s C_stand M :=
    { points := config.P₀.image squareToStand
      tubes := config.T₀.image tubeToStand
      tubeFamily := fun p hp =>
        let p_main := squareToMain p
        have hpm : p_main ∈ config.P₀ := h_main_of_stand p hp
        (config.tubeFamily p_main hpm).image tubeToStand
      h_subset := by
        intro p hp T hT
        rcases Finset.mem_image.mp hT with ⟨T_main, hT_main, rfl⟩
        let p_main := squareToMain p
        have hpm : p_main ∈ config.P₀ := h_main_of_stand p hp
        have h1 : T_main ∈ config.T₀ := config.h_subset p_main hpm hT_main
        exact Finset.mem_image.mpr ⟨T_main, h1, rfl⟩
      h_size := by
        intro p hp
        let p_main := squareToMain p
        have hpm : p_main ∈ config.P₀ := h_main_of_stand p hp
        have h_card : ((config.tubeFamily p_main hpm).image tubeToStand).card =
            (config.tubeFamily p_main hpm).card :=
          Finset.card_image_of_injective _ tubeToStand_inj
        rw [h_card, config.h_size p_main hpm]
      h_sset := by
        intro p hp
        let p_main := squareToMain p
        have hpm : p_main ∈ config.P₀ := h_main_of_stand p hp
        let F_main := config.tubeFamily p_main hpm
        have h_main_sset := config.h_delta_s_set p_main hpm
        rcases sset_transfer F_main h_main_sset with ⟨C', hC'_le, hC'_one, h_sset'⟩
        have h_final : _root_.IsFiniteTubeSSet s C_stand (F_main.image tubeToStand) :=
          _root_.InductionOnScales.IsFiniteTubeSSet.monotone_const hC'_le h_sset'
        exact h_final
      h_incidence := by
        intro p hp T hT
        rcases Finset.mem_image.mp hT with ⟨T_main, hT_main, rfl⟩
        let p_main := squareToMain p
        have hpm : p_main ∈ config.P₀ := h_main_of_stand p hp
        exact incidence_transfer p_main hpm T_main hT_main
      h_bounded := by
        intro p hp
        rcases Finset.mem_image.mp hp with ⟨p_main, hpm, h_eq⟩
        have h_bounds := h_squares_unit p_main hpm
        have h_p_eq : p = squareToStand p_main := h_eq.symm
        subst h_p_eq
        exact h_bounded_of_indices (squareToStand p_main) h_bounds.1 h_bounds.2.1 h_bounds.2.2.1 h_bounds.2.2.2
      h_tube_parameters := by
        intro T hT
        rcases Finset.mem_image.mp hT with ⟨T_main, hT_main, rfl⟩
        have h := h_tubes_strip T_main hT_main
        simpa [tubeToStand, _root_.DyadicTube.IsInAllowedParameterStrip] using h }

  have h_sconfig_nonempty : sconfig.points.Nonempty :=
    Finset.Nonempty.image hP_nonempty squareToStand

  have h_tubes_bounded_stand : sconfig.tubes.card ≤ 36 * 16^n := by
    have h1 : sconfig.tubes.card = config.T₀.card := by
      rw [Finset.card_image_of_injective _ tubeToStand_inj]
    rw [h1]
    have h2 : config.T₀.card ≤ 12 * 16^n := h_tubes_bounded
    have h3 : (12 * 16^n : ℕ) ≤ 36 * 16^n := by
      gcongr <;> norm_num
    exact le_trans h2 h3

  -- ==========================================================================
  -- Step 2: Call standalone induction theorem
  -- ==========================================================================
  rcases _root_.InductionOnScales.induction_step_v3 hnm s hs hs_one C_stand hC_stand_one M hM
      sconfig h_sconfig_nonempty h_tubes_bounded_stand with
    ⟨K, hK_one, _hK_bound, _max_size, _hK_eq,
      P_stand, hP_sub_stand, tubeFamily_stand,
      CΔ, MΔ, hMΔ, coarseConfig_stand, CQ_stand, MQ_stand, hMQ_stand, fineConfig_stand,
      hP_nonempty', h_coarse_points, _h_coarse_card, _h_per_Q_ret,
      h_family_data, h_CΔ_le, _h_CΔ_ge, h_CQ_bounds, _h_containment,
      _h_fine_points, _h_fine_slope, h_cardinality, hfine_tubes_eq⟩

  -- ==========================================================================
  -- Step 3: Scale K by 50 (10 for C_stand enlargement, 5 for reverse S-set transfer)
  -- ==========================================================================
  let K' := K * 50
  have hK'_one : 1 ≤ K' := by
    have h1 : 1 ≤ K := hK_one
    nlinarith
  have hK_le_K' : K ≤ K' := by
    dsimp only [K']
    have h1 : 0 ≤ K := by linarith
    nlinarith

  -- ==========================================================================
  -- Step 4: Convert output back
  -- ==========================================================================
  let P_main : Finset (MainSquare n) := P_stand.image squareToMain

  have hP_stand_conv : ∀ (p : MainSquare n), p ∈ P_main → squareToStand p ∈ P_stand :=
    fun p hp => h_mem_conv hp

  have hP_sub_main : P_main ⊆ config.P₀ := by
    intro p hp
    have h1 : squareToStand p ∈ P_stand := hP_stand_conv p hp
    have h2 : squareToStand p ∈ sconfig.points := hP_sub_stand h1
    rcases Finset.mem_image.mp h2 with ⟨q, hq, h_eq⟩
    have h_q_eq_p : q = p := squareToStand_inj h_eq
    exact h_q_eq_p ▸ hq

  let tubeFamily_main : (p : MainSquare n) → p ∈ P_main → Finset (MainTube n) :=
    fun p hp => (tubeFamily_stand (squareToStand p) (hP_stand_conv p hp)).image tubeToMain

  -- Coarse membership conversion
  have h_coarse_mem_conv : ∀ (Q : MainSquare m),
      Q ∈ coarseConfig_stand.points.image squareToMain →
      squareToStand Q ∈ coarseConfig_stand.points :=
    fun Q hQ => h_mem_conv hQ

  -- containingSquare commutes with identity conversions (for non-negative indices)
  have h_refinement_eq : ∀ (p : MainSquare n), p ∈ P_main →
      squareToMain (_root_.containingSquare hnm (squareToStand p)) =
      InductionConfigurations.containingSquare hnm p := by
    intro p hp
    have h_bounds_p := h_squares_unit p (hP_sub_main hp)
    have hpi_nonneg : 0 ≤ p.i := h_bounds_p.1
    have hpj_nonneg : 0 ≤ p.j := h_bounds_p.2.2.1
    have hk_pos : 0 < 2 ^ (n - m) := by positivity
    have hpi_eq : (squareToStand p).i = p.i := by rfl
    have hpj_eq : (squareToStand p).j = p.j := by rfl
    have h1 : (_root_.containingSquare hnm (squareToStand p)).i =
        (InductionConfigurations.containingSquare hnm p).i := by
      dsimp only [_root_.containingSquare, InductionConfigurations.containingSquare,
        _root_.coarseParentIndex, InductionConfigurations.refinementFactor,
        _root_.coarseRefinementFactor, squareToStand]
      rw [floor_div_eq_int_div p.i hpi_nonneg (2 ^ (n - m)) hk_pos]
      <;> rfl
    have h2 : (_root_.containingSquare hnm (squareToStand p)).j =
        (InductionConfigurations.containingSquare hnm p).j := by
      dsimp only [_root_.containingSquare, InductionConfigurations.containingSquare,
        _root_.coarseParentIndex, InductionConfigurations.refinementFactor,
        _root_.coarseRefinementFactor, squareToStand]
      rw [floor_div_eq_int_div p.j hpj_nonneg (2 ^ (n - m)) hk_pos]
      <;> rfl
    have h_inj : Function.Injective (fun x : MainSquare m => (x.i, x.j)) := by
      intro x y h
      have h' : x.i = y.i ∧ x.j = y.j := by
        simpa [Prod.ext_iff] using h
      have hi : x.i = y.i := h'.1
      have hj : x.j = y.j := h'.2
      cases x; cases y; simp_all
    have h_main : squareToMain (_root_.containingSquare hnm (squareToStand p)) =
        InductionConfigurations.containingSquare hnm p := by
      apply_fun (fun x : MainSquare m => (x.i, x.j)) using h_inj
      <;> simp [h1, h2] <;> tauto
    exact h_main

  let CΔ_main := 5 * CΔ
  let coarseConfig_main : MainConfig m s CΔ_main MΔ :=
    { P₀ := coarseConfig_stand.points.image squareToMain
      T₀ := coarseConfig_stand.tubes.image tubeToMainShifted
      tubeFamily := fun Q hQ =>
        let Q_stand := squareToStand Q
        have hQ_stand : Q_stand ∈ coarseConfig_stand.points := h_coarse_mem_conv Q hQ
        (coarseConfig_stand.tubeFamily Q_stand hQ_stand).image tubeToMainShifted
      h_subset := by
        intro Q hQ T hT
        rcases Finset.mem_image.mp hT with ⟨T_stand, hT_stand, rfl⟩
        let Q_stand := squareToStand Q
        have hQ_stand : Q_stand ∈ coarseConfig_stand.points := h_coarse_mem_conv Q hQ
        have h1 : T_stand ∈ coarseConfig_stand.tubes :=
          coarseConfig_stand.h_subset Q_stand hQ_stand hT_stand
        exact Finset.mem_image.mpr ⟨T_stand, h1, rfl⟩
      h_size := by
        intro Q hQ
        rw [Finset.card_image_of_injective _ tubeToMainShifted_inj]
        exact coarseConfig_stand.h_size (squareToStand Q) (h_coarse_mem_conv Q hQ)
      h_delta_s_set := by
        intro Q hQ
        let Q_stand := squareToStand Q
        have hQ_stand : Q_stand ∈ coarseConfig_stand.points := h_coarse_mem_conv Q hQ
        let F_stand := coarseConfig_stand.tubeFamily Q_stand hQ_stand
        have h_sset_stand : _root_.IsFiniteTubeSSet s CΔ F_stand :=
          coarseConfig_stand.h_sset Q_stand hQ_stand
        have hCΔ_one : 1 ≤ CΔ := h_sset_stand.2.1
        exact sset_transfer_rev m CΔ hCΔ_one F_stand h_sset_stand
      h_intersect := by
        intro Q hQ T hT
        rcases Finset.mem_image.mp hT with ⟨T_stand, hT_stand, rfl⟩
        let Q_stand := squareToStand Q
        have hQ_stand : Q_stand ∈ coarseConfig_stand.points := h_coarse_mem_conv Q hQ
        have h_inc_stand : (T_stand.toSet ∩ Q_stand.toSet).Nonempty :=
          coarseConfig_stand.h_incidence Q_stand hQ_stand T_stand hT_stand
        have hQ_bounded : Q_stand.toSet ⊆ _root_.unitSquare :=
          coarseConfig_stand.h_bounded Q_stand hQ_stand
        exact shifted_incidence T_stand Q_stand hQ_bounded h_inc_stand
      h_tube_parameters := Set.Finite.isBounded (Finset.finite_toSet (coarseConfig_stand.tubes.image tubeToMainShifted))
      h_bounded := by
        rw [Bornology.isBounded_biUnion (Finset.finite_toSet (coarseConfig_stand.points.image squareToMain))]
        intro Q _
        exact DyadicSquare.toSet_isBounded Q }

  let CQ_stand_val : MainSquare m → ℝ := fun Q => CQ_stand (squareToStand Q)
  let CQ_main : MainSquare m → ℝ := fun Q => 5 * CQ_stand_val Q
  let MQ_main : MainSquare m → ℕ := fun Q => MQ_stand (squareToStand Q)

  have hMQ_main : ∀ Q ∈ coarseConfig_main.P₀, 0 < MQ_main Q := by
    intro Q hQ
    let Q_stand := squareToStand Q
    have hQ_stand : Q_stand ∈ coarseConfig_stand.points := h_coarse_mem_conv Q hQ
    exact hMQ_stand Q_stand hQ_stand

  let fineConfig_main : (Q : MainSquare m) → Q ∈ coarseConfig_main.P₀ →
      MainConfig (n - m) s (CQ_main Q) (MQ_main Q) := by
    intro Q hQ
    let Q_stand := squareToStand Q
    have hQ_stand : Q_stand ∈ coarseConfig_stand.points := h_coarse_mem_conv Q hQ
    let fc_stand := fineConfig_stand Q_stand hQ_stand
    exact
      { P₀ := fc_stand.points.image squareToMain
        T₀ := fc_stand.tubes.image tubeToMainShifted
        tubeFamily := fun p hp =>
          let p_stand := squareToStand p
          have hp_stand : p_stand ∈ fc_stand.points := h_mem_conv hp
          (fc_stand.tubeFamily p_stand hp_stand).image tubeToMainShifted
        h_subset := by
          intro p hp T hT
          rcases Finset.mem_image.mp hT with ⟨T_stand, hT_stand, rfl⟩
          let p_stand := squareToStand p
          have hp_stand : p_stand ∈ fc_stand.points := h_mem_conv hp
          have h1 : T_stand ∈ fc_stand.tubes := fc_stand.h_subset p_stand hp_stand hT_stand
          exact Finset.mem_image.mpr ⟨T_stand, h1, rfl⟩
        h_size := by
          intro p hp
          rw [Finset.card_image_of_injective _ tubeToMainShifted_inj]
          exact fc_stand.h_size (squareToStand p) (h_mem_conv hp)
        h_delta_s_set := by
          intro p hp
          let p_stand := squareToStand p
          have hp_stand : p_stand ∈ fc_stand.points := h_mem_conv hp
          let F_stand := fc_stand.tubeFamily p_stand hp_stand
          have h_sset_stand : _root_.IsFiniteTubeSSet s (CQ_stand_val Q) F_stand :=
            fc_stand.h_sset p_stand hp_stand
          have hC_one : 1 ≤ CQ_stand_val Q := h_sset_stand.2.1
          exact sset_transfer_rev (n - m) (CQ_stand_val Q) hC_one F_stand h_sset_stand
        h_intersect := by
          intro p hp T hT
          rcases Finset.mem_image.mp hT with ⟨T_stand, hT_stand, rfl⟩
          let p_stand := squareToStand p
          have hp_stand : p_stand ∈ fc_stand.points := h_mem_conv hp
          have h_inc_stand : (T_stand.toSet ∩ p_stand.toSet).Nonempty :=
            fc_stand.h_incidence p_stand hp_stand T_stand hT_stand
          have hp_bounded : p_stand.toSet ⊆ _root_.unitSquare :=
            fc_stand.h_bounded p_stand hp_stand
          exact shifted_incidence T_stand p_stand hp_bounded h_inc_stand
        h_tube_parameters := Set.Finite.isBounded (Finset.finite_toSet (fc_stand.tubes.image tubeToMainShifted))
        h_bounded := by
          rw [Bornology.isBounded_biUnion (Finset.finite_toSet (fc_stand.points.image squareToMain))]
          intro p _
          exact DyadicSquare.toSet_isBounded p }

  -- B1BridgeHypotheses for fine config
  let fineConfig_B1_main : ∀ (Q : MainSquare m) (hQ : Q ∈ coarseConfig_main.P₀),
      B1BridgeHypotheses (n - m) (fineConfig_main Q hQ) := by
    intro Q hQ
    let Q_stand := squareToStand Q
    have hQ_stand : Q_stand ∈ coarseConfig_stand.points := h_coarse_mem_conv Q hQ
    let fc_stand := fineConfig_stand Q_stand hQ_stand
    let fc_main := fineConfig_main Q hQ
    have h_tubes_eq : fc_stand.tubes = fc_stand.points.biUnion (fun q =>
        if hq : q ∈ fc_stand.points then fc_stand.tubeFamily q hq else ∅) :=
      hfine_tubes_eq Q_stand hQ_stand
    have h_squares_unit : ∀ (p : MainSquare (n - m)), p ∈ fc_main.P₀ →
        0 ≤ p.i ∧ p.i < (2 ^ (n - m) : ℤ) ∧ 0 ≤ p.j ∧ p.j < (2 ^ (n - m) : ℤ) := by
      intro p hp
      rcases Finset.mem_image.mp hp with ⟨p_stand, hp_stand, rfl⟩
      have h_bounded : p_stand.toSet ⊆ _root_.unitSquare := fc_stand.h_bounded p_stand hp_stand
      exact InductionOnScales.CoarsePhaseHelpers.dyadic_square_in_unitSquare_bounds p_stand h_bounded
    have h_tubes_strip : ∀ (T : MainTube (n - m)), T ∈ fc_main.T₀ →
        -(2 ^ (n - m) : ℤ) ≤ T.a ∧ T.a < (2 ^ (n - m) : ℤ) := by
      intro T hT
      rcases Finset.mem_image.mp hT with ⟨T_stand, hT_stand, rfl⟩
      exact fc_stand.h_tube_parameters T_stand hT_stand
    have h_tubes_bounded : fc_main.T₀.card ≤ 12 * 16 ^ (n - m) := by
      have h_card_eq : fc_main.T₀.card = fc_stand.tubes.card := by
        rw [Finset.card_image_of_injective _ tubeToMainShifted_inj]
      rw [h_card_eq]
      by_cases h_empty : fc_stand.points = ∅
      · -- If points empty, tubes empty
        have h_tubes_empty : fc_stand.tubes = ∅ := by
          rw [h_tubes_eq]
          simp [h_empty]
        rw [h_tubes_empty] <;> positivity
      · -- Points nonempty
        have h_points_nonempty : fc_stand.points.Nonempty :=
          Finset.nonempty_iff_ne_empty.mpr h_empty
        rcases h_points_nonempty with ⟨p0, hp0⟩
        let f : StandSquare (n - m) → Finset (StandTube (n - m)) := fun q =>
          if hq : q ∈ fc_stand.points then fc_stand.tubeFamily q hq else ∅
        have h_union2 : fc_stand.tubes = fc_stand.points.biUnion f := h_tubes_eq
        rw [h_union2]
        have h1 : (fc_stand.points.biUnion f).card ≤ ∑ q ∈ fc_stand.points, (f q).card :=
          Finset.card_biUnion_le
        have h2 : ∀ q ∈ fc_stand.points, (f q).card = MQ_stand Q_stand := by
          intro q hq
          simp [f, hq, fc_stand.h_size q hq]
        have h_sum : ∑ q ∈ fc_stand.points, (f q).card = fc_stand.points.card * MQ_stand Q_stand := by
          rw [Finset.sum_congr rfl h2]
          simp [Finset.sum_const] <;> ring
        have h3 : (fc_stand.points.biUnion f).card ≤ fc_stand.points.card * MQ_stand Q_stand := by
          rw [h_sum] at h1; exact h1
        have h4 : (fc_stand.points.card : ℝ) ≤ (4 : ℝ)^(n - m) := by
          have h5 := InductionOnScales.point_count_bound fc_stand
          have h6 : (1 : ℝ) / (_root_.dyadicDelta (n - m))^2 = (4 : ℝ)^(n - m) :=
            InductionOnScales.one_over_dyadicDelta_sq (n - m)
          rw [h6] at h5; exact h5
        have h7 : (MQ_stand Q_stand : ℝ) ≤ 12 * (4 : ℝ)^(n - m) := by
          have h8 : (MQ_stand Q_stand : ℝ) ≤ 12 / (_root_.dyadicDelta (n - m))^2 :=
            InductionOnScales.tube_count_bound fc_stand p0 hp0
          have h9 : 12 / (_root_.dyadicDelta (n - m))^2 = 12 * (4 : ℝ)^(n - m) := by
            have h10 : (1 : ℝ) / (_root_.dyadicDelta (n - m))^2 = (4 : ℝ)^(n - m) :=
              InductionOnScales.one_over_dyadicDelta_sq (n - m)
            calc
              12 / (_root_.dyadicDelta (n - m))^2
                = 12 * ((1 : ℝ) / (_root_.dyadicDelta (n - m))^2) := by ring
              _ = 12 * (4 : ℝ)^(n - m) := by rw [h10]
          rw [h9] at h8
          exact h8
        have h10 : ((fc_stand.points.biUnion f).card : ℝ) ≤ 12 * (16 : ℝ)^(n - m) := by
          calc
            ((fc_stand.points.biUnion f).card : ℝ)
              ≤ (fc_stand.points.card : ℝ) * (MQ_stand Q_stand : ℝ) := by exact_mod_cast h3
            _ ≤ (4 : ℝ)^(n - m) * (12 * (4 : ℝ)^(n - m)) := by
              exact mul_le_mul h4 h7 (by positivity) (by positivity)
            _ = 12 * (16 : ℝ)^(n - m) := by
              have h11 : (4 : ℝ)^(n - m) * (12 * (4 : ℝ)^(n - m)) = 12 * (16 : ℝ)^(n - m) := by
                have h12 : (4 : ℝ)^(n - m) * (4 : ℝ)^(n - m) = (16 : ℝ)^(n - m) := by
                  rw [← mul_pow] <;> norm_num
                calc
                  (4 : ℝ)^(n - m) * (12 * (4 : ℝ)^(n - m))
                    = 12 * ((4 : ℝ)^(n - m) * (4 : ℝ)^(n - m)) := by ring
                  _ = 12 * (16 : ℝ)^(n - m) := by rw [h12]
              exact h11
        exact_mod_cast h10
    exact ⟨h_squares_unit, h_tubes_strip, h_tubes_bounded⟩

  -- ==========================================================================
  -- Step 5: Prove conclusions
  -- ==========================================================================
  refine' ⟨K', hK'_one, P_main, hP_sub_main, tubeFamily_main, CΔ_main, MΔ, hMΔ,
    coarseConfig_main, CQ_main, MQ_main, hMQ_main, fineConfig_main, fineConfig_B1_main, _⟩

  constructor
  · -- P.Nonempty
    exact Finset.Nonempty.image hP_nonempty' squareToMain

  constructor
  · -- coarseConfig.P₀ = P.image containingSquare
    ext Q
    simp only [coarseConfig_main, P_main, Finset.mem_image]
    constructor
    · rintro ⟨Q_stand, hQ_stand, rfl⟩
      have h1 : Q_stand ∈ coarseConfig_stand.points := hQ_stand
      rw [h_coarse_points] at h1
      rcases Finset.mem_image.mp h1 with ⟨p_stand, hp_stand, h_eq⟩
      let p_main := squareToMain p_stand
      have hp_main : p_main ∈ P_main := Finset.mem_image.mpr ⟨p_stand, hp_stand, rfl⟩
      have hp_main' : ∃ (a : StandSquare n), a ∈ P_stand ∧ squareToMain a = p_main :=
        ⟨p_stand, hp_stand, rfl⟩
      refine ⟨p_main, hp_main', ?_⟩
      have h3 : squareToMain Q_stand = InductionConfigurations.containingSquare hnm p_main := by
        rw [←h_eq]
        exact h_refinement_eq p_main hp_main
      exact h3.symm
    · rintro ⟨p, ⟨p_stand, hp_stand, rfl⟩, rfl⟩
      let p_main := squareToMain p_stand
      have hp_main : p_main ∈ P_main := Finset.mem_image.mpr ⟨p_stand, hp_stand, rfl⟩
      have h1 : _root_.containingSquare hnm p_stand ∈ coarseConfig_stand.points := by
        rw [h_coarse_points]
        exact Finset.mem_image.mpr ⟨p_stand, hp_stand, rfl⟩
      have h2 : squareToMain (_root_.containingSquare hnm p_stand) =
          InductionConfigurations.containingSquare hnm p_main :=
        h_refinement_eq p_main hp_main
      exact ⟨_root_.containingSquare hnm p_stand, h1, h2⟩

  constructor
  · -- tubeFamily subset and size bound
    intro p hp
    constructor
    · -- Subset
      intro T hT
      rcases Finset.mem_image.mp hT with ⟨T_stand, hT_stand, h_eq⟩
      let p_stand := squareToStand p
      have hp_stand : p_stand ∈ P_stand := hP_stand_conv p hp
      have h1 : T_stand ∈ tubeFamily_stand p_stand hp_stand := hT_stand
      have h2 : T_stand ∈ sconfig.tubeFamily p_stand (hP_sub_stand hp_stand) :=
        (h_family_data p_stand hp_stand).1 h1
      rcases Finset.mem_image.mp h2 with ⟨T_main, hT_main, h_eq2⟩
      have h4 : tubeToMain T_stand = T_main := by
        have h5 : tubeToMain T_stand = tubeToMain (tubeToStand T_main) := by rw [h_eq2]
        rw [h5]
        exact mainToStandTubeRoundtrip T_main
      have h_goal : T ∈ config.tubeFamily p (hP_sub_main hp) := by
        have hT_eq : T = tubeToMain T_stand := h_eq.symm
        rw [hT_eq, h4]
        exact hT_main
      exact h_goal
    · -- Size bound
      have h1 : (M : ℝ) ≤ K * ((tubeFamily_stand (squareToStand p) (hP_stand_conv p hp)).card : ℝ) :=
        (h_family_data (squareToStand p) (hP_stand_conv p hp)).2.1
      have h2 : ((tubeFamily_main p hp).card : ℝ) =
          ((tubeFamily_stand (squareToStand p) (hP_stand_conv p hp)).card : ℝ) := by
        dsimp only [tubeFamily_main]
        rw [Finset.card_image_of_injective _ tubeToMain_inj]
      rw [h2]
      have h3 : 0 ≤ ((tubeFamily_stand (squareToStand p) (hP_stand_conv p hp)).card : ℝ) := by positivity
      nlinarith [hK_le_K']

  constructor
  · -- CΔ_main ≤ K' * C₁
    have h1 : CΔ ≤ K * C_stand := h_CΔ_le
    dsimp only [CΔ_main, C_stand, K'] at h1 ⊢
    linarith

  constructor
  · -- ∀ Q ∈ coarseConfig.P₀, CQ Q ≤ K' * C₁
    intro Q hQ
    let Q_stand := squareToStand Q
    have hQ_stand : Q_stand ∈ coarseConfig_stand.points := h_coarse_mem_conv Q hQ
    have h1 : CQ_stand Q_stand ≤ K * C_stand := (h_CQ_bounds Q_stand hQ_stand).1
    dsimp only [C_stand, K', CQ_main, CQ_stand_val] at h1 ⊢
    linarith

  · -- Cardinality inequality
    intro Q hQ
    let Q_stand := squareToStand Q
    have hQ_stand : Q_stand ∈ coarseConfig_stand.points := h_coarse_mem_conv Q hQ
    have h_card : K * (sconfig.tubes.card : ℝ) * MΔ * MQ_stand Q_stand ≥
        (coarseConfig_stand.tubes.card : ℝ) *
        ((fineConfig_stand Q_stand hQ_stand).tubes.card : ℝ) * M :=
      h_cardinality Q_stand hQ_stand
    have h2 : sconfig.tubes.card = config.T₀.card := by
      rw [Finset.card_image_of_injective _ tubeToStand_inj]
    have h3 : (coarseConfig_main.T₀.card : ℝ) = (coarseConfig_stand.tubes.card : ℝ) := by
      dsimp only [coarseConfig_main]
      rw [Finset.card_image_of_injective _ tubeToMainShifted_inj]
      <;> rfl
    have h4 : ((fineConfig_main Q hQ).T₀.card : ℝ) =
        ((fineConfig_stand Q_stand hQ_stand).tubes.card : ℝ) := by
      dsimp only [fineConfig_main]
      rw [Finset.card_image_of_injective _ tubeToMainShifted_inj]
      <;> rfl
    have h5 : MQ_main Q = MQ_stand Q_stand := by rfl
    have h_main_ineq : K * (config.T₀.card : ℝ) * MΔ * (MQ_main Q) ≥
        (coarseConfig_main.T₀.card : ℝ) * ((fineConfig_main Q hQ).T₀.card : ℝ) * M := by
      simpa [h2, h3, h4, h5] using h_card
    have h6 : 0 ≤ (config.T₀.card : ℝ) * (MΔ : ℝ) * (MQ_main Q : ℝ) := by positivity
    have h7 : K * (config.T₀.card : ℝ) * (MΔ : ℝ) * (MQ_main Q : ℝ) ≤
        K' * (config.T₀.card : ℝ) * (MΔ : ℝ) * (MQ_main Q : ℝ) := by
      have h_pos : 0 ≤ (config.T₀.card : ℝ) * (MΔ : ℝ) * (MQ_main Q : ℝ) := h6
      have h : K * ((config.T₀.card : ℝ) * (MΔ : ℝ) * (MQ_main Q : ℝ)) ≤
          K' * ((config.T₀.card : ℝ) * (MΔ : ℝ) * (MQ_main Q : ℝ)) :=
        mul_le_mul_of_nonneg_right hK_le_K' h_pos
      have h_eq1 : K * (config.T₀.card : ℝ) * (MΔ : ℝ) * (MQ_main Q : ℝ) =
          K * ((config.T₀.card : ℝ) * (MΔ : ℝ) * (MQ_main Q : ℝ)) := by ring
      have h_eq2 : K' * (config.T₀.card : ℝ) * (MΔ : ℝ) * (MQ_main Q : ℝ) =
          K' * ((config.T₀.card : ℝ) * (MΔ : ℝ) * (MQ_main Q : ℝ)) := by ring
      rw [h_eq1, h_eq2]
      exact h
    exact le_trans h_main_ineq h7

/-! ============================================================================
   Expanded bridge: eliminates false incidence_transfer via 3-cell expansion

   Each main centered strip S(a,b) is expanded to 3 standalone exact cells
   C(a,b-1), C(a,b), C(a,b+1). At least one intersects the square.
   Filter by incidence, thin to M_min = ceil(M/3), scale K by 2700.
   ============================================================================ -/

open DiscretisedFurstenbergEstimate.Bridge.Geometric

/-- Given main tube T intersecting main square p, there exists C ∈ coveringCells
    that intersects squareToStand p. Geometric proof via strip_to_cells_cover. -/
lemma forward_incidence_repair
    {n : ℕ} (T : MainTube n) (p : MainSquare n)
    (hQ_bounded : (squareToStand p).toSet ⊆ _root_.unitSquare)
    (h_inc : (T.toSet ∩ p.toSet).Nonempty) :
    ∃ (C : StandTube n), C ∈ coveringCells n T.a T.b ∧
      (C.toSet ∩ (squareToStand p).toSet).Nonempty := by
  rcases h_inc with ⟨x, hxT, hxp⟩
  let q : ℝ × ℝ := Geometric.fromEuclidean x
  have hδ_eq : DiscretisedFurstenbergEstimate.dyadicDelta n = _root_.dyadicDelta n := by
    simp [DiscretisedFurstenbergEstimate.dyadicDelta, _root_.dyadicDelta, Real.rpow_neg]
    <;> field_simp <;> norm_cast
  have hq_square : q ∈ (squareToStand p).toSet := by
    have h1 : q.1 = x 0 := by rfl
    have h2 : q.2 = x 1 := by rfl
    simp only [squareToStand, _root_.DyadicSquare.toSet, Set.mem_prod, Set.mem_Ico]
    constructor
    · constructor
      · rw [h1, ←hδ_eq] <;> exact hxp.1
      · have h : x 0 < (↑p.i + 1) * DiscretisedFurstenbergEstimate.dyadicDelta n := hxp.2.1
        rw [h1, ←hδ_eq] <;> exact h
    · constructor
      · rw [h2, ←hδ_eq] <;> exact hxp.2.2.1
      · have h : x 1 < (↑p.j + 1) * DiscretisedFurstenbergEstimate.dyadicDelta n := hxp.2.2.2
        rw [h2, ←hδ_eq] <;> exact h
  have hq_strip : mainStrip n T.a T.b q := by
    rw [←mainStrip_iff_mainTube] <;> exact hxT
  exact mainStrip_intersection_gives_cell hQ_bounded ⟨q, hq_square, hq_strip⟩

/-- At most 3 main tubes T satisfy C ∈ coveringCells n T.a T.b. -/
lemma preimage_candidates_le_3 {n : ℕ} (C : StandTube n)
    (F : Finset (MainTube n)) :
    (F.filter (fun T => C ∈ coveringCells n T.a T.b)).card ≤ 3 := by
  let candidates : Finset (MainTube n) :=
    {⟨C.a, C.b - 1⟩, ⟨C.a, C.b⟩, ⟨C.a, C.b + 1⟩}
  have h1 : (F.filter (fun T => C ∈ coveringCells n T.a T.b)) ⊆ candidates := by
    intro T hT
    have h2 : C ∈ coveringCells n T.a T.b := (Finset.mem_filter.mp hT).2
    have h3 : C = (⟨T.a, T.b - 1⟩ : StandTube n) ∨
        C = (⟨T.a, T.b⟩ : StandTube n) ∨
        C = (⟨T.a, T.b + 1⟩ : StandTube n) := by
      simpa [coveringCells] using h2
    rcases h3 with (h3 | h3 | h3)
    · -- C = ⟨T.a, T.b-1⟩, so T = ⟨C.a, C.b+1⟩
      have h4 : T.a = C.a := by
        have h5 : (⟨T.a, T.b - 1⟩ : StandTube n).a = C.a := by rw [h3]
        simpa using h5
      have h6 : (T.b - 1 : ℤ) = C.b := by
        have h7 : (⟨T.a, T.b - 1⟩ : StandTube n).b = C.b := by rw [h3]
        simpa using h7
      have hb : T.b = C.b + 1 := by
        have h : T.b - 1 = C.b := h6
        omega
      rcases T with ⟨ta, tb⟩
      have ha : ta = C.a := by simpa using h4
      have hb' : tb = C.b + 1 := by simpa using hb
      simp [candidates, ha, hb']
    · -- C = ⟨T.a, T.b⟩, so T = ⟨C.a, C.b⟩
      have h4 : T.a = C.a := by
        have h5 : (⟨T.a, T.b⟩ : StandTube n).a = C.a := by rw [h3]
        simpa using h5
      have hb : T.b = C.b := by
        have h6 : (⟨T.a, T.b⟩ : StandTube n).b = C.b := by rw [h3]
        simpa using h6
      rcases T with ⟨ta, tb⟩
      have ha : ta = C.a := by simpa using h4
      have hb' : tb = C.b := by simpa using hb
      simp [candidates, ha, hb']
    · -- C = ⟨T.a, T.b+1⟩, so T = ⟨C.a, C.b-1⟩
      have h4 : T.a = C.a := by
        have h5 : (⟨T.a, T.b + 1⟩ : StandTube n).a = C.a := by rw [h3]
        simpa using h5
      have h6 : (T.b + 1 : ℤ) = C.b := by
        have h7 : (⟨T.a, T.b + 1⟩ : StandTube n).b = C.b := by rw [h3]
        simpa using h7
      have hb : T.b = C.b - 1 := by
        have h : T.b + 1 = C.b := h6
        omega
      rcases T with ⟨ta, tb⟩
      have ha : ta = C.a := by simpa using h4
      have hb' : tb = C.b - 1 := by simpa using hb
      simp [candidates, ha, hb']
  have h2 : candidates.card = 3 := by
    have h_ne1 : (⟨C.a, C.b - 1⟩ : MainTube n) ≠ (⟨C.a, C.b⟩ : MainTube n) := by
      intro h; have h4 := congr_arg (fun x : MainTube n => x.b) h; simp at h4 <;> linarith
    have h_ne2 : (⟨C.a, C.b - 1⟩ : MainTube n) ≠ (⟨C.a, C.b + 1⟩ : MainTube n) := by
      intro h; have h4 := congr_arg (fun x : MainTube n => x.b) h; simp at h4 <;> linarith
    have h_ne3 : (⟨C.a, C.b⟩ : MainTube n) ≠ (⟨C.a, C.b + 1⟩ : MainTube n) := by
      intro h; have h4 := congr_arg (fun x : MainTube n => x.b) h; simp at h4 <;> linarith
    simp [candidates, h_ne1, h_ne2, h_ne3] <;> rfl
  calc (F.filter (fun T => C ∈ coveringCells n T.a T.b)).card
    ≤ candidates.card := Finset.card_le_card h1
  _ = 3 := h2

/-- Filtered expanded family has size ≥ M/3 via double counting. -/
lemma expanded_filtered_size_lower
    {n : ℕ} {M : ℕ} (p : MainSquare n)
    (F : Finset (MainTube n)) (hF_card : F.card = M)
    (hQ_bounded : (squareToStand p).toSet ⊆ _root_.unitSquare)
    (h_inc : ∀ T ∈ F, (T.toSet ∩ p.toSet).Nonempty) :
    let E := F.biUnion (fun T => coveringCells n T.a T.b)
    let G := E.filter (fun C => (C.toSet ∩ (squareToStand p).toSet).Nonempty)
    (G.card : ℝ) ≥ (M : ℝ) / 3 := by
  let E := F.biUnion (fun T => coveringCells n T.a T.b)
  let G : Finset (StandTube n) :=
    E.filter (fun C => (C.toSet ∩ (squareToStand p).toSet).Nonempty)
  have h_choose : ∀ (T : MainTube n), T ∈ F →
      ∃ (C : StandTube n), C ∈ coveringCells n T.a T.b ∧
        (C.toSet ∩ (squareToStand p).toSet).Nonempty :=
    fun T hT => forward_incidence_repair T p hQ_bounded (h_inc T hT)
  choose g hg1 hg2 using h_choose
  let g' : MainTube n → StandTube n := fun T =>
    if h : T ∈ F then g T h else ⟨0, 0⟩
  have hg'_eq : ∀ (T : MainTube n) (hT : T ∈ F), g' T = g T hT := by
    intro T hT
    simp [g', hT]
  have hg_in_G : ∀ T ∈ F, g' T ∈ G := by
    intro T hT
    have h_eq : g' T = g T hT := hg'_eq T hT
    rw [h_eq]
    have h1 : g T hT ∈ E := Finset.mem_biUnion.mpr ⟨T, hT, hg1 T hT⟩
    exact Finset.mem_filter.mpr ⟨h1, hg2 T hT⟩
  let I : Finset (StandTube n) := Finset.image g' F
  have hI_sub_G : I ⊆ G := by
    intro C hC
    rcases Finset.mem_image.mp hC with ⟨T, hT, rfl⟩
    exact hg_in_G T hT
  have h_fiber_le_3 : ∀ C ∈ I,
      (F.filter (fun T => g' T = C)).card ≤
      (F.filter (fun T => C ∈ coveringCells n T.a T.b)).card := by
    intro C _
    apply Finset.card_le_card
    intro T hT
    have h3 : g' T = C := (Finset.mem_filter.mp hT).2
    have h4 : C ∈ coveringCells n T.a T.b := by
      have hT' : T ∈ F := (Finset.mem_filter.mp hT).1
      have h5 : g' T = g T hT' := hg'_eq T hT'
      have h6 : g T hT' = C := by rw [←h5, h3]
      exact h6 ▸ hg1 T hT'
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hT).1, h4⟩
  have h_mapsTo : Set.MapsTo g' (↑F : Set (MainTube n)) (↑I : Set (StandTube n)) := by
    intro x hx
    exact Finset.mem_image_of_mem g' hx
  have h_partition : F.card = ∑ C ∈ I, (F.filter (fun T => g' T = C)).card := by
    exact Finset.card_eq_sum_card_fiberwise h_mapsTo
  have h_sum : (F.card : ℝ) ≤ 3 * (I.card : ℝ) := by
    rw [h_partition]
    have h : ∑ C ∈ I, (F.filter (fun T => g' T = C)).card ≤
        ∑ C ∈ I, (F.filter (fun T => C ∈ coveringCells n T.a T.b)).card :=
      Finset.sum_le_sum (fun C hC => h_fiber_le_3 C hC)
    have h2 : ∑ C ∈ I, (F.filter (fun T => C ∈ coveringCells n T.a T.b)).card ≤
        3 * I.card := by
      calc ∑ C ∈ I, (F.filter (fun T => C ∈ coveringCells n T.a T.b)).card
        ≤ ∑ C ∈ I, 3 := Finset.sum_le_sum (fun C _ => preimage_candidates_le_3 C F)
      _ = 3 * I.card := by simp [Finset.sum_const] <;> ring
    exact_mod_cast le_trans h h2
  have hI_le_G : I.card ≤ G.card := Finset.card_le_card hI_sub_G
  have h_final : (M : ℝ) ≤ 3 * (G.card : ℝ) := by
    calc (M : ℝ)
      = (F.card : ℝ) := by exact_mod_cast hF_card.symm
    _ ≤ 3 * (I.card : ℝ) := h_sum
    _ ≤ 3 * (G.card : ℝ) := by gcongr
  linarith

/-! ### Helper lemmas for inductionOnScalesBridge_expanded

These lemmas break the large bridge proof into independently type-checkable pieces.
-/

/-- General fiber-counting bound: if `f : S → T` has fibers of size ≤ 3,
    then `|S| ≤ 3 * |T|`. -/
lemma dyadicSquare_eq {n : ℕ} {p q : DyadicSquare n} (hi : p.i = q.i) (hj : p.j = q.j) : p = q := by
  cases p with | mk pi pj =>
  cases q with | mk qi qj =>
  have hi' : pi = qi := by simpa using hi
  have hj' : pj = qj := by simpa using hj
  rw [hi', hj']

/-- `squareToMain` commutes with `squareHomothety` across the two namespaces. -/
lemma homothety_comm {n m : ℕ} (hnm : m ≤ n)
    (Q : MainSquare m) (p_stand : StandSquare n) :
    squareToMain (_root_.squareHomothety hnm (squareToStand Q) p_stand) =
      InductionConfigurations.squareHomothety hnm Q (squareToMain p_stand) := by
  have h_i : (squareToMain (_root_.squareHomothety hnm (squareToStand Q) p_stand)).i =
      (InductionConfigurations.squareHomothety hnm Q (squareToMain p_stand)).i := by
    dsimp [squareToMain, squareToStand, _root_.squareHomothety,
      InductionConfigurations.squareHomothety, _root_.coarseRefinementFactor,
      InductionConfigurations.refinementFactor]
    <;> rfl
  have h_j : (squareToMain (_root_.squareHomothety hnm (squareToStand Q) p_stand)).j =
      (InductionConfigurations.squareHomothety hnm Q (squareToMain p_stand)).j := by
    dsimp [squareToMain, squareToStand, _root_.squareHomothety,
      InductionConfigurations.squareHomothety, _root_.coarseRefinementFactor,
      InductionConfigurations.refinementFactor]
    <;> rfl
  exact dyadicSquare_eq h_i h_j

/-- `squareContained` commutes with `squareToStand`/`squareToMain`. -/
lemma squareContained_comm {n m : ℕ} (hnm : m ≤ n)
    (Q : MainSquare m) (p : MainSquare n) :
    _root_.squareContained hnm (squareToStand p) (squareToStand Q) ↔
      InductionConfigurations.squareContained hnm p Q := by
  simp [_root_.squareContained, InductionConfigurations.squareContained,
    _root_.coarseRefinementFactor, InductionConfigurations.refinementFactor,
    squareToStand]
  <;> rfl

lemma expanded_bridge_fiber_bound {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (f : α → β) (T : Finset β)
    (h_mapsTo : ∀ x ∈ S, f x ∈ T)
    (h_fiber_le : ∀ y ∈ T, (S.filter (fun x => f x = y)).card ≤ 3) :
    (S.card : ℝ) ≤ 3 * (T.card : ℝ) := by
  have h_partition : S.card = ∑ y ∈ T, (S.filter (fun x => f x = y)).card :=
    Finset.card_eq_sum_card_fiberwise (by intro x hx; exact h_mapsTo x hx)
  have h_sum : ∑ y ∈ T, (S.filter (fun x => f x = y)).card ≤ ∑ y ∈ T, (3 : ℕ) := by
    apply Finset.sum_le_sum
    intro y hy
    exact h_fiber_le y hy
  have h_sum3 : ∑ y ∈ T, (3 : ℕ) = 3 * T.card := by
    rw [Finset.sum_const] <;> ring
  have h : S.card ≤ 3 * T.card := by
    calc S.card
      = ∑ y ∈ T, (S.filter (fun x => f x = y)).card := h_partition
    _ ≤ ∑ y ∈ T, (3 : ℕ) := h_sum
    _ = 3 * T.card := h_sum3
  exact_mod_cast h

/-- Cardinality inequality transfer: standalone → main.
    Given standalone cardinality and the 3x expansion factors, derive the main inequality. -/
lemma expanded_bridge_cardinality
    (K K' C₁ MΔ : ℝ) (M M_min : ℕ)
    (sconfig_tubes_card config_T0_card : ℕ)
    (coarse_stand_tubes_card fine_stand_tubes_card : ℕ)
    (coarse_main_T0_card fine_main_T0_card : ℕ)
    (MQ_stand_val MQ_main_val : ℝ)
    (hK' : K' = K * 2700) (hK_nonneg : 0 ≤ K)
    (hM_le : M ≤ 3 * M_min)
    (h_sconfig_le : sconfig_tubes_card ≤ 3 * config_T0_card)
    (h_coarse_eq : (coarse_main_T0_card : ℝ) = (coarse_stand_tubes_card : ℝ))
    (h_fine_eq : (fine_main_T0_card : ℝ) = (fine_stand_tubes_card : ℝ))
    (h_MQ_eq : (MQ_main_val : ℝ) = (MQ_stand_val : ℝ))
    (hMΔ_nonneg : 0 ≤ MΔ) (hMQ_nonneg : 0 ≤ MQ_main_val)
    (h_card : K * (sconfig_tubes_card : ℝ) * MΔ * MQ_stand_val ≥
        (coarse_stand_tubes_card : ℝ) * (fine_stand_tubes_card : ℝ) * (M_min : ℝ)) :
    K' * (config_T0_card : ℝ) * MΔ * MQ_main_val ≥
      (coarse_main_T0_card : ℝ) * (fine_main_T0_card : ℝ) * (M : ℝ) := by
  set a : ℝ := (coarse_stand_tubes_card : ℝ) with ha
  set b : ℝ := (fine_stand_tubes_card : ℝ) with hb
  set c : ℝ := (sconfig_tubes_card : ℝ) with hc
  set d : ℝ := (config_T0_card : ℝ) with hd
  have ha_nonneg : 0 ≤ a := by positivity
  have hb_nonneg : 0 ≤ b := by positivity
  have hc_nonneg : 0 ≤ c := by positivity
  have hd_nonneg : 0 ≤ d := by positivity
  have h1 : (M : ℝ) ≤ 3 * (M_min : ℝ) := by exact_mod_cast hM_le
  have h2 : c ≤ 3 * d := by
    have h2' : (sconfig_tubes_card : ℝ) ≤ 3 * (config_T0_card : ℝ) := by exact_mod_cast h_sconfig_le
    simpa [hc, hd] using h2'
  have h_main : a * b * (M : ℝ) ≤ 9 * K * d * MΔ * MQ_main_val := by
    have h3 : a * b * (M : ℝ) ≤ a * b * (3 * (M_min : ℝ)) := by
      exact mul_le_mul_of_nonneg_left h1 (mul_nonneg ha_nonneg hb_nonneg)
    have h4 : a * b * (3 * (M_min : ℝ)) = 3 * (a * b * (M_min : ℝ)) := by ring
    have h5 : a * b * (M_min : ℝ) ≤ K * c * MΔ * MQ_stand_val := by
      simpa [ha, hb, hc] using h_card
    have h6 : 3 * (a * b * (M_min : ℝ)) ≤ 3 * (K * c * MΔ * MQ_stand_val) := by
      exact mul_le_mul_of_nonneg_left h5 (by norm_num)
    have h7 : K * c * MΔ * MQ_stand_val ≤ K * (3 * d) * MΔ * MQ_main_val := by
      have h71 : K * c * MΔ * MQ_stand_val = K * c * MΔ * MQ_main_val := by rw [h_MQ_eq]
      rw [h71]
      have h_step1 : K * c ≤ K * (3 * d) := mul_le_mul_of_nonneg_left h2 hK_nonneg
      have h_step2 : (K * c) * MΔ ≤ (K * (3 * d)) * MΔ :=
        mul_le_mul_of_nonneg_right h_step1 hMΔ_nonneg
      have h_step3 : ((K * c) * MΔ) * MQ_main_val ≤ ((K * (3 * d)) * MΔ) * MQ_main_val :=
        mul_le_mul_of_nonneg_right h_step2 hMQ_nonneg
      simpa [mul_assoc] using h_step3
    calc a * b * (M : ℝ)
      ≤ a * b * (3 * (M_min : ℝ)) := h3
    _ = 3 * (a * b * (M_min : ℝ)) := h4
    _ ≤ 3 * (K * c * MΔ * MQ_stand_val) := h6
    _ ≤ 3 * (K * (3 * d) * MΔ * MQ_main_val) := by gcongr
    _ = 9 * K * d * MΔ * MQ_main_val := by ring
  have h_final : 9 * K * d * MΔ * MQ_main_val ≤ K' * d * MΔ * MQ_main_val := by
    rw [hK']
    have h12 : 0 ≤ K := hK_nonneg
    have h13 : 0 ≤ d := hd_nonneg
    have h14 : 0 ≤ MΔ := hMΔ_nonneg
    have h15 : 0 ≤ MQ_main_val := hMQ_nonneg
    have h16 : 9 * K * d * MΔ * MQ_main_val ≤ (K * 2700) * d * MΔ * MQ_main_val := by
      have h17 : 9 * K = K * 9 := by ring
      have h18 : K * 9 ≤ K * 2700 := by
        have h19 : (9 : ℝ) ≤ 2700 := by norm_num
        exact mul_le_mul_of_nonneg_left h19 h12
      have h20 : 9 * K ≤ K * 2700 := by
        rw [h17]
        exact h18
      gcongr
      <;> linarith
    exact h16
  have h_goal : (coarse_main_T0_card : ℝ) * (fine_main_T0_card : ℝ) * (M : ℝ) =
      a * b * (M : ℝ) := by
    rw [h_coarse_eq, h_fine_eq] <;> simp [ha, hb]
  rw [h_goal]
  exact le_trans h_main h_final

/-! Expanded bridge theorem: eliminates false incidence_transfer via 3-cell expansion.
    M_min = ceil(M/3), output retention uses reverse mapping to original tubes. -/
set_option maxHeartbeats 2000000 in
theorem inductionOnScalesBridge_expanded
    {n m : ℕ} (hnm : m ≤ n)
    (s : ℝ) (hs : 0 ≤ s) (hs_one : s ≤ 1)
    (C₁ : ℝ) (hC₁ : 1 ≤ C₁)
    (M : ℕ) (hM : 0 < M)
    (config : MainConfig n s C₁ M)
    (hP_nonempty : config.P₀.Nonempty)
    (h_squares_unit : ∀ p ∈ config.P₀,
      0 ≤ p.i ∧ p.i < (2 ^ n : ℤ) ∧ 0 ≤ p.j ∧ p.j < (2 ^ n : ℤ))
    (h_tubes_strip : ∀ T ∈ config.T₀,
      -(2 ^ n : ℤ) ≤ T.a ∧ T.a < (2 ^ n : ℤ))
    (h_tubes_bounded : config.T₀.card ≤ 12 * 16^n)
    (sset_transfer_expanded : ∀ (F : Finset (MainTube n)),
      IsDeltaSSet (DiscretisedFurstenbergEstimate.dyadicDelta n) s C₁ (F : Set (MainTube n)) →
      ∃ C', C' ≤ C₁ * 60 ∧ 1 ≤ C' ∧
        _root_.IsFiniteTubeSSet s C' (F.biUnion (fun T => coveringCells n T.a T.b)))
    (h_expanded_bounded :
      (config.P₀.biUnion (fun p =>
        if hp : p ∈ config.P₀ then
          (config.tubeFamily p hp).biUnion (fun T => coveringCells n T.a T.b)
        else ∅)).card ≤ 36 * 16^n)
    (sset_transfer_rev : ∀ (k : ℕ) (C : ℝ), 1 ≤ C →
      ∀ (F : Finset (StandTube k)),
        _root_.IsFiniteTubeSSet s C F →
        IsDeltaSSet (DiscretisedFurstenbergEstimate.dyadicDelta k) s (5 * C)
          (F.image tubeToMainShifted : Set (MainTube k))) :
    ∃ (K : ℝ), 1 ≤ K ∧
      K ≤ 2700 * 3145728 * (4 * (n : ℝ) + 7)^7 ∧
      ∃ (P : Finset (MainSquare n))
      (hP_sub : P ⊆ config.P₀)
      (tubeFamily : (p : MainSquare n) → p ∈ P → Finset (MainTube n))
      (CΔ : ℝ) (MΔ : ℕ) (hMΔ : 0 < MΔ)
      (coarseConfig : MainConfig m s CΔ MΔ)
      (CQ : MainSquare m → ℝ)
      (MQ : MainSquare m → ℕ)
      (hMQ : ∀ Q ∈ coarseConfig.P₀, 0 < MQ Q)
      (fineConfig : (Q : MainSquare m) → Q ∈ coarseConfig.P₀ →
        MainConfig (n - m) s (CQ Q) (MQ Q))
      (fineConfig_B1 : (Q : MainSquare m) → (hQ : Q ∈ coarseConfig.P₀) →
        B1BridgeHypotheses (n - m) (fineConfig Q hQ)),
      P.Nonempty ∧
      coarseConfig.P₀ = P.image (InductionConfigurations.containingSquare hnm) ∧
      ((config.P₀.image (InductionConfigurations.containingSquare hnm)).card : ℝ) ≤
        K * (coarseConfig.P₀.card : ℝ) ∧
      (∀ Q ∈ coarseConfig.P₀,
        ((config.P₀.filter fun p =>
          InductionConfigurations.squareContained hnm p Q).card : ℝ) ≤
        K * ((P.filter fun p =>
          InductionConfigurations.squareContained hnm p Q).card : ℝ)) ∧
      (∀ p hp, tubeFamily p hp ⊆ config.tubeFamily p (hP_sub hp) ∧
        (M : ℝ) ≤ K * ((tubeFamily p hp).card : ℝ)) ∧
      CΔ ≤ K * C₁ ∧ C₁ ≤ K * CΔ ∧
      (∀ Q ∈ coarseConfig.P₀, CQ Q ≤ K * C₁ ∧ C₁ ≤ K * CQ Q) ∧
      (∀ p hp, ∀ T ∈ tubeFamily p hp,
        (T.toSet ∩ p.toSet).Nonempty) ∧
      (∀ p hp T, T ∈ tubeFamily p hp →
        ∃ (hQ : InductionConfigurations.containingSquare hnm p ∈ coarseConfig.P₀)
          (U_stand : StandTube m) (C : StandTube n),
          C ∈ coveringCells n T.a T.b ∧
          tubeToMainShifted U_stand ∈
            coarseConfig.tubeFamily (InductionConfigurations.containingSquare hnm p) hQ ∧
          C.toSet ⊆ U_stand.toSet) ∧
      (∀ Q, ∀ hQ : Q ∈ coarseConfig.P₀,
        (fineConfig Q hQ).P₀ =
          (P.filter fun p => InductionConfigurations.squareContained hnm p Q).image
            (InductionConfigurations.squareHomothety hnm Q)) ∧
      (∀ Q, ∀ hQ : Q ∈ coarseConfig.P₀,
        ∀ p, ∀ hp : p ∈ P,
          InductionConfigurations.squareContained hnm p Q →
          ∃ (hq : InductionConfigurations.squareHomothety hnm Q p ∈ (fineConfig Q hQ).P₀),
            ((fineConfig Q hQ).tubeFamily
                (InductionConfigurations.squareHomothety hnm Q p) hq).image (fun U => U.a) =
              (tubeFamily p hp).image
                (fun T => localSlopeCellIndex m T.a)) ∧
      (∀ (Q : MainSquare m) (hQ : Q ∈ coarseConfig.P₀),
        K * (config.T₀.card : ℝ) * MΔ * MQ Q ≥
          (coarseConfig.T₀.card : ℝ) * ((fineConfig Q hQ).T₀.card : ℝ) * M) ∧
      (∀ T ∈ coarseConfig.T₀, |T.slope| ≤ 1) := by
  -- ========================================================================
  -- Step 1: M_min = ceil(M/3)
  -- ========================================================================
  let M_min : ℕ := (M + 2) / 3
  have hM_min_pos : 0 < M_min := by omega
  have hM_le : M ≤ 3 * M_min := by omega
  have hM_min_le : (M_min : ℝ) ≥ (M : ℝ) / 3 := by
    have h : 3 * M_min ≥ M := by omega
    have h' : (3 : ℝ) * (M_min : ℝ) ≥ (M : ℝ) := by exact_mod_cast h
    linarith

  -- Helper: index bounds → p.toSet ⊆ unitSquare
  have h_bounded_of_indices : ∀ (p : StandSquare n),
      0 ≤ p.i → p.i < (2 ^ n : ℤ) → 0 ≤ p.j → p.j < (2 ^ n : ℤ) →
      p.toSet ⊆ _root_.unitSquare := by
    intro p hi1 hi2 hj1 hj2 x hx
    set δ' := _root_.dyadicDelta n with hδ'_def
    have hδ'_pos : 0 < δ' := _root_.dyadicDelta_pos n
    have hδ'_one : ((2 ^ n : ℝ)) * δ' = 1 := by
      simp [hδ'_def, _root_.dyadicDelta, Real.rpow_neg, Real.rpow_natCast] <;> field_simp <;> ring
    have h_i_add1 : (p.i + 1 : ℤ) ≤ (2 ^ n : ℤ) := by linarith
    have h_j_add1 : (p.j + 1 : ℤ) ≤ (2 ^ n : ℤ) := by linarith
    constructor
    · constructor
      · have h_nonneg : 0 ≤ (p.i : ℝ) := by exact_mod_cast hi1
        have hδ'_nonneg : 0 ≤ δ' := by linarith
        have h : 0 ≤ (p.i : ℝ) * δ' := mul_nonneg h_nonneg hδ'_nonneg
        linarith [hx.1.1]
      · have h' : ((p.i + 1 : ℝ) * δ') ≤ ((2 ^ n : ℝ) * δ') := by
          gcongr <;> exact_mod_cast h_i_add1
        linarith [hδ'_one, hx.1.2]
    · constructor
      · have h_nonneg : 0 ≤ (p.j : ℝ) := by exact_mod_cast hj1
        have hδ'_nonneg : 0 ≤ δ' := by linarith
        have h : 0 ≤ (p.j : ℝ) * δ' := mul_nonneg h_nonneg hδ'_nonneg
        linarith [hx.2.1]
      · have h' : ((p.j + 1 : ℝ) * δ') ≤ ((2 ^ n : ℝ) * δ') := by
          gcongr <;> exact_mod_cast h_j_add1
        linarith [hδ'_one, hx.2.2]

  -- Helper: p ∈ S.image squareToMain → squareToStand p ∈ S
  have h_mem_conv : ∀ {k : ℕ} {S : Finset (StandSquare k)} {p : MainSquare k},
      p ∈ S.image squareToMain → squareToStand p ∈ S := by
    intro k S p hp
    rcases Finset.mem_image.mp hp with ⟨q, hq, h_eq⟩
    have h_eq2 : squareToStand p = q := by
      have h : squareToStand (squareToMain q) = q := standToMainRoundtrip q
      simpa [h_eq] using h
    rw [h_eq2] <;> exact hq

  -- ========================================================================
  -- Step 2: Per-point expansion, filtering, and thinning
  -- ========================================================================
  let allExpanded : Finset (StandTube n) :=
    config.P₀.biUnion (fun p =>
      if hp : p ∈ config.P₀ then
        (config.tubeFamily p hp).biUnion (fun T => coveringCells n T.a T.b)
      else ∅)

  have h_allExpanded_bounded : allExpanded.card ≤ 36 * 16^n := h_expanded_bounded

  let expandFilter (p : MainSquare n) (hp : p ∈ config.P₀) : Finset (StandTube n) :=
    let F_p := config.tubeFamily p hp
    let E_p := F_p.biUnion (fun T => coveringCells n T.a T.b)
    E_p.filter (fun C => (C.toSet ∩ (squareToStand p).toSet).Nonempty)

  have hQ_bounded_all : ∀ p ∈ config.P₀, (squareToStand p).toSet ⊆ _root_.unitSquare := by
    intro p hp
    have h_bounds := h_squares_unit p hp
    exact h_bounded_of_indices (squareToStand p) h_bounds.1 h_bounds.2.1 h_bounds.2.2.1 h_bounds.2.2.2

  have hG_size : ∀ (p : MainSquare n) (hp : p ∈ config.P₀),
      M_min ≤ (expandFilter p hp).card := by
    intro p hp
    have h1 : ((expandFilter p hp).card : ℝ) ≥ (M : ℝ) / 3 :=
      expanded_filtered_size_lower p (config.tubeFamily p hp)
        (config.h_size p hp) (hQ_bounded_all p hp)
        (fun T hT => config.h_intersect p hp T hT)
    by_contra h
    have h3 : (expandFilter p hp).card ≤ M_min - 1 := by omega
    have h4 : ((expandFilter p hp).card : ℝ) ≤ ((M_min - 1 : ℕ) : ℝ) := by exact_mod_cast h3
    have h5 : 3 * (M_min - 1) < M := by
      simp [M_min] <;> omega
    have h6 : ((M_min - 1 : ℕ) : ℝ) < (M : ℝ) / 3 := by
      have h7 : (3 : ℝ) * ((M_min - 1 : ℕ) : ℝ) < (M : ℝ) := by exact_mod_cast h5
      linarith
    linarith

  let H (p : MainSquare n) (hp : p ∈ config.P₀) : Finset (StandTube n) :=
    Classical.choose (Finset.exists_subset_card_eq (hG_size p hp))

  have hH_spec : ∀ (p : MainSquare n) (hp : p ∈ config.P₀),
      H p hp ⊆ expandFilter p hp ∧ (H p hp).card = M_min := by
    intro p hp
    exact Classical.choose_spec (Finset.exists_subset_card_eq (hG_size p hp))

  have hH_sub_E : ∀ p hp, H p hp ⊆ allExpanded := by
    intro p hp
    have h1 : H p hp ⊆ expandFilter p hp := (hH_spec p hp).1
    have h2 : expandFilter p hp ⊆ allExpanded := by
      intro C hC
      have h3 : C ∈ (config.tubeFamily p hp).biUnion (fun T => coveringCells n T.a T.b) :=
        (Finset.mem_filter.mp hC).1
      have h4 : C ∈ allExpanded := by
        apply Finset.mem_biUnion.mpr
        exact ⟨p, hp, by simpa [hp] using h3⟩
      exact h4
    exact Finset.Subset.trans h1 h2

  have hH_incidence : ∀ p hp C, C ∈ H p hp →
      (C.toSet ∩ (squareToStand p).toSet).Nonempty := by
    intro p hp C hC
    have h1 : C ∈ expandFilter p hp := (hH_spec p hp).1 hC
    exact (Finset.mem_filter.mp h1).2

  -- S-set for H_p: E_p is SSet(≤60C₁), H_p ⊆ E_p, |E_p| ≤ 9|H_p|
  let C_stand : ℝ := 540 * C₁
  have hC_stand_one : 1 ≤ C_stand := by
    have h1 : 1 ≤ C₁ := hC₁
    nlinarith

  have hH_sset : ∀ p hp, _root_.IsFiniteTubeSSet s C_stand (H p hp) := by
    intro p hp
    let F_p := config.tubeFamily p hp
    let E_p := F_p.biUnion (fun T => coveringCells n T.a T.b)
    have h_main_sset : IsDeltaSSet (DiscretisedFurstenbergEstimate.dyadicDelta n) s C₁ (F_p : Set (MainTube n)) :=
      config.h_delta_s_set p hp
    rcases sset_transfer_expanded F_p h_main_sset with ⟨C', hC'_le, hC'_one, h_E_sset⟩
    have hE_size : (E_p.card : ℝ) ≤ 9 * ((H p hp).card : ℝ) := by
      have h1 : E_p.card ≤ 3 * F_p.card := by
        calc E_p.card
          ≤ ∑ T ∈ F_p, (coveringCells n T.a T.b).card := Finset.card_biUnion_le
        _ = ∑ T ∈ F_p, 3 := by simp [coveringCells_card]
        _ = 3 * F_p.card := by simp [Finset.sum_const] <;> ring
      have h2 : (H p hp).card = M_min := (hH_spec p hp).2
      have h3 : F_p.card = M := config.h_size p hp
      have h4 : E_p.card ≤ 3 * M := by
        rw [h3] at h1; exact h1
      have h5 : 3 * M ≤ 9 * M_min := by
        have h6 : M ≤ 3 * M_min := hM_le
        omega
      have h7 : E_p.card ≤ 9 * M_min := by omega
      rw [h2]
      exact_mod_cast h7
    have h4 : H p hp ⊆ E_p := by
      have h5 : H p hp ⊆ expandFilter p hp := (hH_spec p hp).1
      have h6 : expandFilter p hp ⊆ E_p := Finset.filter_subset _ _
      exact Finset.Subset.trans h5 h6
    have h5 : _root_.IsFiniteTubeSSet s (9 * C') (H p hp) :=
      _root_.InductionOnScales.sset_monotone_card h4 h_E_sset hE_size (by norm_num)
    have h6 : 9 * C' ≤ C_stand := by
      dsimp only [C_stand]
      have h7 : C' ≤ C₁ * 60 := hC'_le
      nlinarith
    exact _root_.InductionOnScales.IsFiniteTubeSSet.monotone_const h6 h5

  -- ========================================================================
  -- Step 3: Construct standalone NiceConfiguration
  -- ========================================================================
  have h_main_of_stand : ∀ (p : StandSquare n),
      p ∈ config.P₀.image squareToStand → squareToMain p ∈ config.P₀ := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨q, hq, h_eq⟩
    have h_eq2 : squareToMain p = q := by
      have h : squareToMain (squareToStand q) = q := mainToStandRoundtrip q
      simpa [h_eq] using h
    rw [h_eq2] <;> exact hq

  let sconfig : StandConfig n s C_stand M_min :=
    { points := config.P₀.image squareToStand
      tubes := allExpanded
      tubeFamily := fun p hp =>
        let p_main := squareToMain p
        have hpm : p_main ∈ config.P₀ := h_main_of_stand p hp
        H p_main hpm
      h_subset := by
        intro p hp
        exact hH_sub_E (squareToMain p) (h_main_of_stand p hp)
      h_size := by
        intro p hp
        exact (hH_spec (squareToMain p) (h_main_of_stand p hp)).2
      h_sset := by
        intro p hp
        exact hH_sset (squareToMain p) (h_main_of_stand p hp)
      h_incidence := by
        intro p hp T hT
        exact hH_incidence (squareToMain p) (h_main_of_stand p hp) T hT
      h_bounded := by
        intro p hp
        rcases Finset.mem_image.mp hp with ⟨p_main, hpm, h_eq⟩
        have h_p_eq : p = squareToStand p_main := h_eq.symm
        subst h_p_eq
        exact hQ_bounded_all p_main hpm
      h_tube_parameters := by
        intro T hT
        rcases Finset.mem_biUnion.mp hT with ⟨p, hp, hT2⟩
        have hT3 : T ∈ (config.tubeFamily p hp).biUnion (fun T => coveringCells n T.a T.b) := by
          simpa [hp] using hT2
        rcases Finset.mem_biUnion.mp hT3 with ⟨T_main, hT_main, hT4⟩
        have h5 : T ∈ coveringCells n T_main.a T_main.b := hT4
        have h6 : T.a = T_main.a := by
          have h7 : T = (⟨T_main.a, T_main.b - 1⟩ : StandTube n) ∨
              T = (⟨T_main.a, T_main.b⟩ : StandTube n) ∨
              T = (⟨T_main.a, T_main.b + 1⟩ : StandTube n) := by
            simpa [coveringCells] using h5
          rcases h7 with (h7 | h7 | h7) <;> simp [h7]
        have h_goal : T.IsInAllowedParameterStrip := by
          have hT_in_T0 : T_main ∈ config.T₀ := config.h_subset p hp hT_main
          simpa [DyadicTube.IsInAllowedParameterStrip, h6] using h_tubes_strip T_main hT_in_T0
        exact h_goal }

  have h_sconfig_nonempty : sconfig.points.Nonempty :=
    Finset.Nonempty.image hP_nonempty squareToStand

  -- ========================================================================
  -- Step 4: Call standalone induction theorem
  -- ========================================================================
  rcases _root_.InductionOnScales.induction_step_v3 hnm s hs hs_one C_stand hC_stand_one
      M_min hM_min_pos sconfig h_sconfig_nonempty h_allExpanded_bounded with
    ⟨K, hK_one, hK_bound, _max_size, _hK_eq,
      P_stand, hP_sub_stand, tubeFamily_stand,
      CΔ, MΔ, hMΔ, coarseConfig_stand, CQ_stand, MQ_stand, hMQ_stand, fineConfig_stand,
      hP_nonempty', h_coarse_points, h_coarse_card, h_per_Q_ret,
      h_family_data, h_CΔ_le, h_CΔ_ge, h_CQ_bounds, h_containment,
      h_fine_points, h_fine_slope, h_cardinality, hfine_tubes_eq⟩

  -- ========================================================================
  -- Step 5: Scale K by 2700 (= 540 for C_stand × 5 for reverse transfer)
  -- ========================================================================
  let K' := K * 2700
  have hK'_one : 1 ≤ K' := by
    have h1 : 1 ≤ K := hK_one
    nlinarith
  have hK_le_K' : K ≤ K' := by
    dsimp only [K']
    have h1 : 0 ≤ K := by linarith
    nlinarith

  have hK'_bound : K' ≤ 2700 * 3145728 * (4 * (n : ℝ) + 7)^7 := by
    dsimp only [K']
    have h : K ≤ 3145728 * (4 * (n : ℝ) + 7)^7 := hK_bound
    calc
      K * 2700
        ≤ (3145728 * (4 * (n : ℝ) + 7)^7) * 2700 := by gcongr
      _ = 2700 * 3145728 * (4 * (n : ℝ) + 7)^7 := by ring

  -- ========================================================================
  -- Step 6: Convert outputs back to main repo
  -- ========================================================================
  let P_main : Finset (MainSquare n) := P_stand.image squareToMain

  have hP_stand_conv : ∀ (p : MainSquare n), p ∈ P_main → squareToStand p ∈ P_stand :=
    fun p hp => h_mem_conv hp

  have hP_sub_main : P_main ⊆ config.P₀ := by
    intro p hp
    have h1 : squareToStand p ∈ P_stand := hP_stand_conv p hp
    have h2 : squareToStand p ∈ sconfig.points := hP_sub_stand h1
    rcases Finset.mem_image.mp h2 with ⟨q, hq, h_eq⟩
    have h_q_eq_p : q = p := squareToStand_inj h_eq
    exact h_q_eq_p ▸ hq

  -- Reverse map: each output standalone cell came from some original main tube
  let reverseMap (p : MainSquare n) (hp : p ∈ P_main) (C : StandTube n) : MainTube n :=
    if hC : C ∈ tubeFamily_stand (squareToStand p) (hP_stand_conv p hp) then
      Classical.choose (show ∃ (T : MainTube n), T ∈ config.tubeFamily p (hP_sub_main hp) ∧
        C ∈ coveringCells n T.a T.b from by
        have h5 : C ∈ H p (hP_sub_main hp) :=
          (h_family_data (squareToStand p) (hP_stand_conv p hp)).1 hC
        have h6 : C ∈ expandFilter p (hP_sub_main hp) := (hH_spec p (hP_sub_main hp)).1 h5
        have h7 : C ∈ (config.tubeFamily p (hP_sub_main hp)).biUnion (fun T => coveringCells n T.a T.b) :=
          (Finset.mem_filter.mp h6).1
        rcases Finset.mem_biUnion.mp h7 with ⟨T, hT, hC'⟩
        exact ⟨T, hT, hC'⟩)
    else ⟨0, 0⟩

  let tubeFamily_main : (p : MainSquare n) → p ∈ P_main → Finset (MainTube n) :=
    fun p hp => (tubeFamily_stand (squareToStand p) (hP_stand_conv p hp)).image (reverseMap p hp)

  have h_reverseMap_spec : ∀ (p : MainSquare n) (hp : p ∈ P_main) (C : StandTube n),
      C ∈ tubeFamily_stand (squareToStand p) (hP_stand_conv p hp) →
        reverseMap p hp C ∈ config.tubeFamily p (hP_sub_main hp) ∧
        C ∈ coveringCells n (reverseMap p hp C).a (reverseMap p hp C).b := by
    intro p hp C hC
    have h_exists : ∃ (T : MainTube n), T ∈ config.tubeFamily p (hP_sub_main hp) ∧
        C ∈ coveringCells n T.a T.b := by
      have h5 : C ∈ H p (hP_sub_main hp) :=
        (h_family_data (squareToStand p) (hP_stand_conv p hp)).1 hC
      have h6 : C ∈ expandFilter p (hP_sub_main hp) := (hH_spec p (hP_sub_main hp)).1 h5
      have h7 : C ∈ (config.tubeFamily p (hP_sub_main hp)).biUnion (fun T => coveringCells n T.a T.b) :=
        (Finset.mem_filter.mp h6).1
      rcases Finset.mem_biUnion.mp h7 with ⟨T, hT, hC'⟩
      exact ⟨T, hT, hC'⟩
    have h_def : reverseMap p hp C = Classical.choose h_exists := by
      simp only [reverseMap]
      rw [dif_pos hC]
    rw [h_def]
    exact Classical.choose_spec h_exists

  -- Coarse membership conversion
  have h_coarse_mem_conv : ∀ (Q : MainSquare m),
      Q ∈ coarseConfig_stand.points.image squareToMain →
      squareToStand Q ∈ coarseConfig_stand.points :=
    fun Q hQ => h_mem_conv hQ

  -- containingSquare commutes with identity conversions
  have h_refinement_eq : ∀ (p : MainSquare n), p ∈ P_main →
      squareToMain (_root_.containingSquare hnm (squareToStand p)) =
      InductionConfigurations.containingSquare hnm p := by
    intro p hp
    have h_bounds_p := h_squares_unit p (hP_sub_main hp)
    have hpi_nonneg : 0 ≤ p.i := h_bounds_p.1
    have hpj_nonneg : 0 ≤ p.j := h_bounds_p.2.2.1
    have hk_pos : 0 < 2 ^ (n - m) := by positivity
    have h1 : (_root_.containingSquare hnm (squareToStand p)).i =
        (InductionConfigurations.containingSquare hnm p).i := by
      dsimp only [_root_.containingSquare, InductionConfigurations.containingSquare,
        _root_.coarseParentIndex, InductionConfigurations.refinementFactor,
        _root_.coarseRefinementFactor, squareToStand]
      rw [floor_div_eq_int_div p.i hpi_nonneg (2 ^ (n - m)) hk_pos] <;> rfl
    have h2 : (_root_.containingSquare hnm (squareToStand p)).j =
        (InductionConfigurations.containingSquare hnm p).j := by
      dsimp only [_root_.containingSquare, InductionConfigurations.containingSquare,
        _root_.coarseParentIndex, InductionConfigurations.refinementFactor,
        _root_.coarseRefinementFactor, squareToStand]
      rw [floor_div_eq_int_div p.j hpj_nonneg (2 ^ (n - m)) hk_pos] <;> rfl
    have h_inj : Function.Injective (fun x : MainSquare m => (x.i, x.j)) := by
      intro x y h
      have h' : x.i = y.i ∧ x.j = y.j := by simpa [Prod.ext_iff] using h
      cases x; cases y; simp_all
    apply_fun (fun x : MainSquare m => (x.i, x.j)) using h_inj
    <;> simp [h1, h2] <;> tauto

  let CΔ_main := 5 * CΔ
  let coarseConfig_main : MainConfig m s CΔ_main MΔ :=
    { P₀ := coarseConfig_stand.points.image squareToMain
      T₀ := coarseConfig_stand.tubes.image tubeToMainShifted
      tubeFamily := fun Q hQ =>
        let Q_stand := squareToStand Q
        have hQ_stand : Q_stand ∈ coarseConfig_stand.points := h_coarse_mem_conv Q hQ
        (coarseConfig_stand.tubeFamily Q_stand hQ_stand).image tubeToMainShifted
      h_subset := by
        intro Q hQ T hT
        rcases Finset.mem_image.mp hT with ⟨T_stand, hT_stand, rfl⟩
        let Q_stand := squareToStand Q
        have hQ_stand : Q_stand ∈ coarseConfig_stand.points := h_coarse_mem_conv Q hQ
        have h1 : T_stand ∈ coarseConfig_stand.tubes :=
          coarseConfig_stand.h_subset Q_stand hQ_stand hT_stand
        exact Finset.mem_image.mpr ⟨T_stand, h1, rfl⟩
      h_size := by
        intro Q hQ
        rw [Finset.card_image_of_injective _ tubeToMainShifted_inj]
        exact coarseConfig_stand.h_size (squareToStand Q) (h_coarse_mem_conv Q hQ)
      h_delta_s_set := by
        intro Q hQ
        let Q_stand := squareToStand Q
        have hQ_stand : Q_stand ∈ coarseConfig_stand.points := h_coarse_mem_conv Q hQ
        let F_stand := coarseConfig_stand.tubeFamily Q_stand hQ_stand
        have h_sset_stand : _root_.IsFiniteTubeSSet s CΔ F_stand :=
          coarseConfig_stand.h_sset Q_stand hQ_stand
        have hCΔ_one : 1 ≤ CΔ := h_sset_stand.2.1
        exact sset_transfer_rev m CΔ hCΔ_one F_stand h_sset_stand
      h_intersect := by
        intro Q hQ T hT
        rcases Finset.mem_image.mp hT with ⟨T_stand, hT_stand, rfl⟩
        let Q_stand := squareToStand Q
        have hQ_stand : Q_stand ∈ coarseConfig_stand.points := h_coarse_mem_conv Q hQ
        have h_inc_stand : (T_stand.toSet ∩ Q_stand.toSet).Nonempty :=
          coarseConfig_stand.h_incidence Q_stand hQ_stand T_stand hT_stand
        have hQ_bounded : Q_stand.toSet ⊆ _root_.unitSquare :=
          coarseConfig_stand.h_bounded Q_stand hQ_stand
        exact shifted_incidence T_stand Q_stand hQ_bounded h_inc_stand
      h_tube_parameters := Set.Finite.isBounded (Finset.finite_toSet (coarseConfig_stand.tubes.image tubeToMainShifted))
      h_bounded := by
        rw [Bornology.isBounded_biUnion (Finset.finite_toSet (coarseConfig_stand.points.image squareToMain))]
        intro Q _
        exact DyadicSquare.toSet_isBounded Q }

  let CQ_stand_val : MainSquare m → ℝ := fun Q => CQ_stand (squareToStand Q)
  let CQ_main : MainSquare m → ℝ := fun Q => 5 * CQ_stand_val Q
  let MQ_main : MainSquare m → ℕ := fun Q => MQ_stand (squareToStand Q)

  have hMQ_main : ∀ Q ∈ coarseConfig_main.P₀, 0 < MQ_main Q := by
    intro Q hQ
    let Q_stand := squareToStand Q
    have hQ_stand : Q_stand ∈ coarseConfig_stand.points := h_coarse_mem_conv Q hQ
    exact hMQ_stand Q_stand hQ_stand

  let fineConfig_main : (Q : MainSquare m) → Q ∈ coarseConfig_main.P₀ →
      MainConfig (n - m) s (CQ_main Q) (MQ_main Q) := by
    intro Q hQ
    let Q_stand := squareToStand Q
    have hQ_stand : Q_stand ∈ coarseConfig_stand.points := h_coarse_mem_conv Q hQ
    let fc_stand := fineConfig_stand Q_stand hQ_stand
    exact
      { P₀ := fc_stand.points.image squareToMain
        T₀ := fc_stand.tubes.image tubeToMainShifted
        tubeFamily := fun p hp =>
          let p_stand := squareToStand p
          have hp_stand : p_stand ∈ fc_stand.points := h_mem_conv hp
          (fc_stand.tubeFamily p_stand hp_stand).image tubeToMainShifted
        h_subset := by
          intro p hp T hT
          rcases Finset.mem_image.mp hT with ⟨T_stand, hT_stand, rfl⟩
          let p_stand := squareToStand p
          have hp_stand : p_stand ∈ fc_stand.points := h_mem_conv hp
          have h1 : T_stand ∈ fc_stand.tubes := fc_stand.h_subset p_stand hp_stand hT_stand
          exact Finset.mem_image.mpr ⟨T_stand, h1, rfl⟩
        h_size := by
          intro p hp
          rw [Finset.card_image_of_injective _ tubeToMainShifted_inj]
          exact fc_stand.h_size (squareToStand p) (h_mem_conv hp)
        h_delta_s_set := by
          intro p hp
          let p_stand := squareToStand p
          have hp_stand : p_stand ∈ fc_stand.points := h_mem_conv hp
          let F_stand := fc_stand.tubeFamily p_stand hp_stand
          have h_sset_stand : _root_.IsFiniteTubeSSet s (CQ_stand_val Q) F_stand :=
            fc_stand.h_sset p_stand hp_stand
          have hC_one : 1 ≤ CQ_stand_val Q := h_sset_stand.2.1
          exact sset_transfer_rev (n - m) (CQ_stand_val Q) hC_one F_stand h_sset_stand
        h_intersect := by
          intro p hp T hT
          rcases Finset.mem_image.mp hT with ⟨T_stand, hT_stand, rfl⟩
          let p_stand := squareToStand p
          have hp_stand : p_stand ∈ fc_stand.points := h_mem_conv hp
          have h_inc_stand : (T_stand.toSet ∩ p_stand.toSet).Nonempty :=
            fc_stand.h_incidence p_stand hp_stand T_stand hT_stand
          have hp_bounded : p_stand.toSet ⊆ _root_.unitSquare :=
            fc_stand.h_bounded p_stand hp_stand
          exact shifted_incidence T_stand p_stand hp_bounded h_inc_stand
        h_tube_parameters := Set.Finite.isBounded (Finset.finite_toSet (fc_stand.tubes.image tubeToMainShifted))
        h_bounded := by
          rw [Bornology.isBounded_biUnion (Finset.finite_toSet (fc_stand.points.image squareToMain))]
          intro p _
          exact DyadicSquare.toSet_isBounded p }

  -- B1BridgeHypotheses for fine config (second bridge)
  let fineConfig_B1_main : ∀ (Q : MainSquare m) (hQ : Q ∈ coarseConfig_main.P₀),
      B1BridgeHypotheses (n - m) (fineConfig_main Q hQ) := by
    intro Q hQ
    let Q_stand := squareToStand Q
    have hQ_stand : Q_stand ∈ coarseConfig_stand.points := h_coarse_mem_conv Q hQ
    let fc_stand := fineConfig_stand Q_stand hQ_stand
    let fc_main := fineConfig_main Q hQ
    have h_tubes_eq : fc_stand.tubes = fc_stand.points.biUnion (fun q =>
        if hq : q ∈ fc_stand.points then fc_stand.tubeFamily q hq else ∅) :=
      hfine_tubes_eq Q_stand hQ_stand
    have h_squares_unit : ∀ (p : MainSquare (n - m)), p ∈ fc_main.P₀ →
        0 ≤ p.i ∧ p.i < (2 ^ (n - m) : ℤ) ∧ 0 ≤ p.j ∧ p.j < (2 ^ (n - m) : ℤ) := by
      intro p hp
      rcases Finset.mem_image.mp hp with ⟨p_stand, hp_stand, rfl⟩
      have h_bounded : p_stand.toSet ⊆ _root_.unitSquare := fc_stand.h_bounded p_stand hp_stand
      exact InductionOnScales.CoarsePhaseHelpers.dyadic_square_in_unitSquare_bounds p_stand h_bounded
    have h_tubes_strip : ∀ (T : MainTube (n - m)), T ∈ fc_main.T₀ →
        -(2 ^ (n - m) : ℤ) ≤ T.a ∧ T.a < (2 ^ (n - m) : ℤ) := by
      intro T hT
      rcases Finset.mem_image.mp hT with ⟨T_stand, hT_stand, rfl⟩
      exact fc_stand.h_tube_parameters T_stand hT_stand
    have h_tubes_bounded : fc_main.T₀.card ≤ 12 * 16 ^ (n - m) := by
      have h_card_eq : fc_main.T₀.card = fc_stand.tubes.card := by
        rw [Finset.card_image_of_injective _ tubeToMainShifted_inj]
      rw [h_card_eq]
      by_cases h_empty : fc_stand.points = ∅
      · -- If points empty, tubes empty
        have h_tubes_empty : fc_stand.tubes = ∅ := by
          rw [h_tubes_eq]
          simp [h_empty]
        rw [h_tubes_empty] <;> positivity
      · -- Points nonempty
        have h_points_nonempty : fc_stand.points.Nonempty :=
          Finset.nonempty_iff_ne_empty.mpr h_empty
        rcases h_points_nonempty with ⟨p0, hp0⟩
        let f : StandSquare (n - m) → Finset (StandTube (n - m)) := fun q =>
          if hq : q ∈ fc_stand.points then fc_stand.tubeFamily q hq else ∅
        have h_union2 : fc_stand.tubes = fc_stand.points.biUnion f := h_tubes_eq
        rw [h_union2]
        have h1 : (fc_stand.points.biUnion f).card ≤ ∑ q ∈ fc_stand.points, (f q).card :=
          Finset.card_biUnion_le
        have h2 : ∀ q ∈ fc_stand.points, (f q).card = MQ_stand Q_stand := by
          intro q hq
          simp [f, hq, fc_stand.h_size q hq]
        have h_sum : ∑ q ∈ fc_stand.points, (f q).card = fc_stand.points.card * MQ_stand Q_stand := by
          rw [Finset.sum_congr rfl h2]
          simp [Finset.sum_const] <;> ring
        have h3 : (fc_stand.points.biUnion f).card ≤ fc_stand.points.card * MQ_stand Q_stand := by
          rw [h_sum] at h1; exact h1
        have h4 : (fc_stand.points.card : ℝ) ≤ (4 : ℝ)^(n - m) := by
          have h5 := InductionOnScales.point_count_bound fc_stand
          have h6 : (1 : ℝ) / (_root_.dyadicDelta (n - m))^2 = (4 : ℝ)^(n - m) :=
            InductionOnScales.one_over_dyadicDelta_sq (n - m)
          rw [h6] at h5; exact h5
        have h7 : (MQ_stand Q_stand : ℝ) ≤ 12 * (4 : ℝ)^(n - m) := by
          have h8 : (MQ_stand Q_stand : ℝ) ≤ 12 / (_root_.dyadicDelta (n - m))^2 :=
            InductionOnScales.tube_count_bound fc_stand p0 hp0
          have h9 : 12 / (_root_.dyadicDelta (n - m))^2 = 12 * (4 : ℝ)^(n - m) := by
            have h10 : (1 : ℝ) / (_root_.dyadicDelta (n - m))^2 = (4 : ℝ)^(n - m) :=
              InductionOnScales.one_over_dyadicDelta_sq (n - m)
            calc
              12 / (_root_.dyadicDelta (n - m))^2
                = 12 * ((1 : ℝ) / (_root_.dyadicDelta (n - m))^2) := by ring
              _ = 12 * (4 : ℝ)^(n - m) := by rw [h10]
          rw [h9] at h8
          exact h8
        have h10 : ((fc_stand.points.biUnion f).card : ℝ) ≤ 12 * (16 : ℝ)^(n - m) := by
          calc
            ((fc_stand.points.biUnion f).card : ℝ)
              ≤ (fc_stand.points.card : ℝ) * (MQ_stand Q_stand : ℝ) := by exact_mod_cast h3
            _ ≤ (4 : ℝ)^(n - m) * (12 * (4 : ℝ)^(n - m)) := by
              exact mul_le_mul h4 h7 (by positivity) (by positivity)
            _ = 12 * (16 : ℝ)^(n - m) := by
              have h11 : (4 : ℝ)^(n - m) * (12 * (4 : ℝ)^(n - m)) = 12 * (16 : ℝ)^(n - m) := by
                have h12 : (4 : ℝ)^(n - m) * (4 : ℝ)^(n - m) = (16 : ℝ)^(n - m) := by
                  rw [← mul_pow] <;> norm_num
                calc
                  (4 : ℝ)^(n - m) * (12 * (4 : ℝ)^(n - m))
                    = 12 * ((4 : ℝ)^(n - m) * (4 : ℝ)^(n - m)) := by ring
                  _ = 12 * (16 : ℝ)^(n - m) := by rw [h12]
              exact h11
        exact_mod_cast h10
    exact ⟨h_squares_unit, h_tubes_strip, h_tubes_bounded⟩

  -- ========================================================================
  -- Step 7: Prove conclusions
  -- ========================================================================
  refine' ⟨K', hK'_one, hK'_bound, P_main, hP_sub_main, tubeFamily_main, CΔ_main, MΔ, hMΔ,
    coarseConfig_main, CQ_main, MQ_main, hMQ_main, fineConfig_main, fineConfig_B1_main, _⟩

  constructor
  · -- P.Nonempty
    exact Finset.Nonempty.image hP_nonempty' squareToMain

  constructor
  · -- coarseConfig.P₀ = P.image containingSquare
    ext Q
    simp only [coarseConfig_main, P_main, Finset.mem_image]
    constructor
    · rintro ⟨Q_stand, hQ_stand, rfl⟩
      have h1 : Q_stand ∈ coarseConfig_stand.points := hQ_stand
      rw [h_coarse_points] at h1
      rcases Finset.mem_image.mp h1 with ⟨p_stand, hp_stand, h_eq⟩
      let p_main := squareToMain p_stand
      have hp_main : p_main ∈ P_main := Finset.mem_image.mpr ⟨p_stand, hp_stand, rfl⟩
      refine ⟨p_main, ⟨p_stand, hp_stand, rfl⟩, ?_⟩
      have h3 : squareToMain Q_stand = InductionConfigurations.containingSquare hnm p_main := by
        rw [←h_eq]
        exact h_refinement_eq p_main hp_main
      exact h3.symm
    · rintro ⟨p, ⟨p_stand, hp_stand, rfl⟩, rfl⟩
      let p_main := squareToMain p_stand
      have hp_main : p_main ∈ P_main := Finset.mem_image.mpr ⟨p_stand, hp_stand, rfl⟩
      have h1 : _root_.containingSquare hnm p_stand ∈ coarseConfig_stand.points := by
        rw [h_coarse_points]
        exact Finset.mem_image.mpr ⟨p_stand, hp_stand, rfl⟩
      have h2 : squareToMain (_root_.containingSquare hnm p_stand) =
          InductionConfigurations.containingSquare hnm p_main :=
        h_refinement_eq p_main hp_main
      exact ⟨_root_.containingSquare hnm p_stand, h1, h2⟩

  constructor
  · -- Global point retention
    have h_comm : ∀ (p : MainSquare n), p ∈ config.P₀ →
        squareToMain (_root_.containingSquare hnm (squareToStand p)) =
        InductionConfigurations.containingSquare hnm p := by
      intro p hp
      have h_bounds_p := h_squares_unit p hp
      have hpi_nonneg : 0 ≤ p.i := h_bounds_p.1
      have hpj_nonneg : 0 ≤ p.j := h_bounds_p.2.2.1
      have hk_pos : 0 < 2 ^ (n - m) := by positivity
      have h1 : (_root_.containingSquare hnm (squareToStand p)).i =
          (InductionConfigurations.containingSquare hnm p).i := by
        dsimp only [_root_.containingSquare, InductionConfigurations.containingSquare,
          _root_.coarseParentIndex, InductionConfigurations.refinementFactor,
          _root_.coarseRefinementFactor, squareToStand]
        rw [floor_div_eq_int_div p.i hpi_nonneg (2 ^ (n - m)) hk_pos] <;> rfl
      have h2 : (_root_.containingSquare hnm (squareToStand p)).j =
          (InductionConfigurations.containingSquare hnm p).j := by
        dsimp only [_root_.containingSquare, InductionConfigurations.containingSquare,
          _root_.coarseParentIndex, InductionConfigurations.refinementFactor,
          _root_.coarseRefinementFactor, squareToStand]
        rw [floor_div_eq_int_div p.j hpj_nonneg (2 ^ (n - m)) hk_pos] <;> rfl
      have h_main_eq : squareToMain (_root_.containingSquare hnm (squareToStand p)) =
          InductionConfigurations.containingSquare hnm p :=
        dyadicSquare_eq h1 h2
      exact h_main_eq
    have h_set_eq : (sconfig.points.image (_root_.containingSquare hnm)).image squareToMain =
        config.P₀.image (InductionConfigurations.containingSquare hnm) := by
      ext Q
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨Q_stand, ⟨p_stand, hp_stand, rfl⟩, rfl⟩
        rcases Finset.mem_image.mp hp_stand with ⟨p_main, hp_main, h_eq⟩
        have h_eq2 : p_stand = squareToStand p_main := h_eq.symm
        exact ⟨p_main, hp_main, by
          have h_goal : InductionConfigurations.containingSquare hnm p_main = squareToMain (_root_.containingSquare hnm p_stand) := by
            rw [h_eq2]
            exact (h_comm p_main hp_main).symm
          exact h_goal⟩
      · rintro ⟨p_main, hp_main, rfl⟩
        let p_stand := squareToStand p_main
        have hp_stand : p_stand ∈ sconfig.points := Finset.mem_image.mpr ⟨p_main, hp_main, rfl⟩
        refine ⟨_root_.containingSquare hnm p_stand, ⟨p_stand, hp_stand, rfl⟩, h_comm p_main hp_main⟩
    have h_card1 : ((sconfig.points.image (_root_.containingSquare hnm)).image squareToMain).card =
        (sconfig.points.image (_root_.containingSquare hnm)).card := by
      rw [Finset.card_image_of_injective _ squareToMain_inj]
    have h_eq1 : (sconfig.points.image (_root_.containingSquare hnm)).card =
        (config.P₀.image (InductionConfigurations.containingSquare hnm)).card := by
      rw [←h_card1, h_set_eq]
    have h1 : ((sconfig.points.image (_root_.containingSquare hnm)).card : ℝ) ≤
        K * (coarseConfig_stand.points.card : ℝ) := h_coarse_card
    have h2 : (coarseConfig_main.P₀.card : ℝ) = (coarseConfig_stand.points.card : ℝ) := by
      dsimp only [coarseConfig_main]
      rw [Finset.card_image_of_injective _ squareToMain_inj] <;> rfl
    have h3 : ((config.P₀.image (InductionConfigurations.containingSquare hnm)).card : ℝ) =
        ((sconfig.points.image (_root_.containingSquare hnm)).card : ℝ) := by
      exact_mod_cast h_eq1.symm
    have h_pos : 0 ≤ (coarseConfig_stand.points.card : ℝ) := by
      exact_mod_cast Nat.zero_le _
    have hK_le : K ≤ K' := hK_le_K'
    have h4 : K * (coarseConfig_stand.points.card : ℝ) ≤ K' * (coarseConfig_stand.points.card : ℝ) :=
      mul_le_mul_of_nonneg_right hK_le h_pos
    rw [h2, h3]
    exact le_trans h1 h4

  constructor
  · -- Per-Q point retention
    intro Q hQ
    let Q_stand := squareToStand Q
    have hQ_stand : Q_stand ∈ coarseConfig_stand.points := h_coarse_mem_conv Q hQ
    have h_filter_eq : (sconfig.points.filter fun p_stand =>
          _root_.squareContained hnm p_stand Q_stand) =
        (config.P₀.filter fun p =>
          InductionConfigurations.squareContained hnm p Q).image squareToStand := by
      ext p_stand
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨hp_stand, h_contain⟩
        rcases Finset.mem_image.mp hp_stand with ⟨p_main, hp_main, rfl⟩
        have h_contain_main : InductionConfigurations.squareContained hnm p_main Q :=
          (squareContained_comm hnm Q p_main).mp h_contain
        exact ⟨p_main, ⟨hp_main, h_contain_main⟩, rfl⟩
      · rintro ⟨p_main, ⟨hp_main, h_contain_main⟩, rfl⟩
        have hp_stand : squareToStand p_main ∈ sconfig.points :=
          Finset.mem_image.mpr ⟨p_main, hp_main, rfl⟩
        have h_contain_stand : _root_.squareContained hnm (squareToStand p_main) Q_stand :=
          (squareContained_comm hnm Q p_main).mpr h_contain_main
        exact ⟨hp_stand, h_contain_stand⟩
    have h_card_eq : ((sconfig.points.filter fun p_stand =>
          _root_.squareContained hnm p_stand Q_stand).card : ℝ) =
        ((config.P₀.filter fun p =>
          InductionConfigurations.squareContained hnm p Q).card : ℝ) := by
      rw [h_filter_eq]
      rw [Finset.card_image_of_injective _ squareToStand_inj]
      <;> rfl
    have h_comm2 (p : StandSquare n) (hp : p ∈ P_stand) :
        _root_.squareContained hnm p Q_stand ↔
          InductionConfigurations.squareContained hnm (squareToMain p) Q := by
      have h_roundtrip : squareToStand (squareToMain p) = p := standToMainRoundtrip p
      have h_main_in : squareToMain p ∈ config.P₀ := h_main_of_stand p (hP_sub_stand hp)
      have h := squareContained_comm hnm Q (squareToMain p)
      rw [h_roundtrip] at h
      exact h
    have h_P_filter_eq : (P_stand.filter fun p_stand =>
          _root_.squareContained hnm p_stand Q_stand) =
        (P_main.filter fun p =>
          InductionConfigurations.squareContained hnm p Q).image squareToStand := by
      ext p_stand
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨hp_stand, h_contain⟩
        let p_main := squareToMain p_stand
        have hp_main : p_main ∈ P_main := Finset.mem_image.mpr ⟨p_stand, hp_stand, rfl⟩
        have h_contain_main : InductionConfigurations.squareContained hnm p_main Q :=
          (h_comm2 p_stand hp_stand).mp h_contain
        exact ⟨p_main, ⟨hp_main, h_contain_main⟩, rfl⟩
      · rintro ⟨p_main, ⟨hp_main, h_contain_main⟩, rfl⟩
        have hp_stand : squareToStand p_main ∈ P_stand := hP_stand_conv p_main hp_main
        have h_contain_stand : _root_.squareContained hnm (squareToStand p_main) Q_stand :=
          (squareContained_comm hnm Q p_main).mpr h_contain_main
        exact ⟨hp_stand, h_contain_stand⟩
    have h_P_card_eq : ((P_stand.filter fun p_stand =>
          _root_.squareContained hnm p_stand Q_stand).card : ℝ) =
        ((P_main.filter fun p =>
          InductionConfigurations.squareContained hnm p Q).card : ℝ) := by
      rw [h_P_filter_eq]
      rw [Finset.card_image_of_injective _ squareToStand_inj]
      <;> rfl
    have h1 : ((sconfig.points.filter fun p_stand =>
          _root_.squareContained hnm p_stand Q_stand).card : ℝ) ≤
        K * ((P_stand.filter fun p =>
          _root_.squareContained hnm p Q_stand).card : ℝ) := h_per_Q_ret Q_stand hQ_stand
    rw [h_card_eq, h_P_card_eq] at h1
    have hK_le : K ≤ K' := hK_le_K'
    have h_pos : 0 ≤ ((P_main.filter fun p =>
          InductionConfigurations.squareContained hnm p Q).card : ℝ) := by positivity
    have h2 : K * ((P_main.filter fun p =>
          InductionConfigurations.squareContained hnm p Q).card : ℝ) ≤
        K' * ((P_main.filter fun p =>
          InductionConfigurations.squareContained hnm p Q).card : ℝ) :=
      mul_le_mul_of_nonneg_right hK_le h_pos
    exact le_trans h1 h2

  constructor
  · -- tubeFamily subset and size bound
    intro p hp
    constructor
    · -- Subset
      intro T hT
      rcases Finset.mem_image.mp hT with ⟨C, hC, rfl⟩
      exact (h_reverseMap_spec p hp C hC).1
    · -- Size bound: M ≤ K' * |tubeFamily_main|
      let S := tubeFamily_stand (squareToStand p) (hP_stand_conv p hp)
      let f := reverseMap p hp
      let T_main := tubeFamily_main p hp
      have h1 : (M_min : ℝ) ≤ K * (S.card : ℝ) :=
        (h_family_data (squareToStand p) (hP_stand_conv p hp)).2.1
      have h_fiber_le_3 : ∀ T ∈ T_main,
          (S.filter (fun C => f C = T)).card ≤ 3 := by
        intro T _
        have h_sub : S.filter (fun C => f C = T) ⊆ coveringCells n T.a T.b := by
          intro C hC
          have h7 : f C = T := (Finset.mem_filter.mp hC).2
          have h8 : C ∈ coveringCells n (f C).a (f C).b :=
            (h_reverseMap_spec p hp C (Finset.mem_filter.mp hC).1).2
          rw [h7] at h8
          exact h8
        have h_card : (S.filter (fun C => f C = T)).card ≤ (coveringCells n T.a T.b).card :=
          Finset.card_le_card h_sub
        have h3 : (coveringCells n T.a T.b).card = 3 := coveringCells_card n T.a T.b
        rw [h3] at h_card
        exact h_card
      have h_mapsTo : ∀ x ∈ S, f x ∈ T_main := by
        intro x hx
        exact Finset.mem_image_of_mem f hx
      have h5 : (S.card : ℝ) ≤ 3 * (T_main.card : ℝ) :=
        expanded_bridge_fiber_bound S f T_main h_mapsTo h_fiber_le_3
      have h6 : (M : ℝ) ≤ 3 * (M_min : ℝ) := by exact_mod_cast hM_le
      have h7 : (M : ℝ) ≤ 9 * K * ((T_main.card : ℝ)) := by
        calc (M : ℝ)
          ≤ 3 * (M_min : ℝ) := h6
        _ ≤ 3 * (K * (S.card : ℝ)) := by
          exact mul_le_mul_of_nonneg_left h1 (by norm_num)
        _ = 3 * K * (S.card : ℝ) := by ring
        _ ≤ 3 * K * (3 * (T_main.card : ℝ)) := by
          exact mul_le_mul_of_nonneg_left h5 (by positivity)
        _ = 9 * K * (T_main.card : ℝ) := by ring
      have h8 : 9 * K ≤ K' := by
        dsimp only [K']
        have h9 : 0 ≤ K := by linarith
        nlinarith
      have h10 : 0 ≤ (T_main.card : ℝ) := by exact_mod_cast Nat.zero_le _
      have h11 : 9 * K * (T_main.card : ℝ) ≤ K' * (T_main.card : ℝ) := by
        exact mul_le_mul_of_nonneg_right h8 h10
      exact le_trans h7 h11

  constructor
  · -- CΔ_main ≤ K' * C₁
    have h1 : CΔ ≤ K * C_stand := h_CΔ_le
    dsimp only [CΔ_main, C_stand, K'] at h1 ⊢
    nlinarith

  constructor
  · -- C₁ ≤ K' * CΔ_main
    have h1 : C_stand ≤ K * CΔ := h_CΔ_ge
    dsimp only [C_stand, CΔ_main, K'] at h1 ⊢
    nlinarith

  constructor
  · -- ∀ Q, CQ Q ≤ K' * C₁ ∧ C₁ ≤ K' * CQ Q
    intro Q hQ
    let Q_stand := squareToStand Q
    have hQ_stand : Q_stand ∈ coarseConfig_stand.points := h_coarse_mem_conv Q hQ
    have h1 : CQ_stand Q_stand ≤ K * C_stand := (h_CQ_bounds Q_stand hQ_stand).1
    have h2 : C_stand ≤ K * CQ_stand Q_stand := (h_CQ_bounds Q_stand hQ_stand).2
    constructor
    · dsimp only [CQ_main, CQ_stand_val, C_stand, K'] at h1 ⊢ <;> nlinarith
    · dsimp only [CQ_main, CQ_stand_val, C_stand, K'] at h2 ⊢ <;> nlinarith

  constructor
  · -- Incidence
    intro p hp T hT
    rcases Finset.mem_image.mp hT with ⟨C, hC, rfl⟩
    let T_main := reverseMap p hp C
    have hT_in : T_main ∈ config.tubeFamily p (hP_sub_main hp) :=
      (h_reverseMap_spec p hp C hC).1
    exact config.h_intersect p (hP_sub_main hp) T_main hT_in

  constructor
  · -- Geometric containment (standalone-cell formulation)
    intro p hp T hT
    rcases Finset.mem_image.mp hT with ⟨C, hC, rfl⟩
    let p_stand := squareToStand p
    have hp_stand : p_stand ∈ P_stand := hP_stand_conv p hp
    rcases h_containment p_stand hp_stand C hC with ⟨hQ_stand, U_stand, hU_in, h_contain⟩
    let Q_stand0 := _root_.containingSquare hnm p_stand
    have hQ0_stand : Q_stand0 ∈ coarseConfig_stand.points := hQ_stand
    have hQ_eq : squareToMain Q_stand0 = InductionConfigurations.containingSquare hnm p :=
      h_refinement_eq p hp
    have hQ_main : InductionConfigurations.containingSquare hnm p ∈ coarseConfig_main.P₀ := by
      have h2 : squareToMain Q_stand0 ∈ coarseConfig_main.P₀ :=
        Finset.mem_image.mpr ⟨Q_stand0, hQ0_stand, rfl⟩
      convert h2 using 1
      exact hQ_eq.symm
    have h_stand_eq : squareToStand (InductionConfigurations.containingSquare hnm p) = Q_stand0 := by
      have h1 : squareToStand (squareToMain Q_stand0) = Q_stand0 := standToMainRoundtrip Q_stand0
      have h2 : squareToStand (squareToMain Q_stand0) = squareToStand (InductionConfigurations.containingSquare hnm p) := by
        rw [hQ_eq]
      exact h2.symm.trans h1
    have hQ_stand' : squareToStand (InductionConfigurations.containingSquare hnm p) ∈ coarseConfig_stand.points := by
      rw [h_stand_eq]
      exact hQ0_stand
    have h_tmp : tubeToMainShifted U_stand ∈
        coarseConfig_main.tubeFamily (InductionConfigurations.containingSquare hnm p) hQ_main := by
      dsimp only [coarseConfig_main]
      have h_family_eq : coarseConfig_stand.tubeFamily
          (squareToStand (InductionConfigurations.containingSquare hnm p)) hQ_stand' =
          coarseConfig_stand.tubeFamily Q_stand0 hQ0_stand := by
        congr
        <;> exact h_stand_eq
      rw [h_family_eq]
      exact Finset.mem_image.mpr ⟨U_stand, hU_in, rfl⟩
    have hC_in_covering : C ∈ coveringCells n (reverseMap p hp C).a (reverseMap p hp C).b :=
      (h_reverseMap_spec p hp C hC).2
    exact ⟨hQ_main, U_stand, C, hC_in_covering, h_tmp, h_contain⟩

  constructor
  · -- Fine config points equality
    intro Q hQ
    let Q_stand := squareToStand Q
    have hQ_stand : Q_stand ∈ coarseConfig_stand.points := h_coarse_mem_conv Q hQ
    have h1 : (fineConfig_stand Q_stand hQ_stand).points =
        (P_stand.filter fun p => _root_.squareContained hnm p Q_stand).image
          (_root_.squareHomothety hnm Q_stand) := h_fine_points Q_stand hQ_stand
    have h_P_filter_image : (P_stand.filter fun p_stand =>
          _root_.squareContained hnm p_stand Q_stand).image squareToMain =
        (P_main.filter fun p =>
          InductionConfigurations.squareContained hnm p Q) := by
      ext p_main
      simp only [Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨p_stand, ⟨hp_stand, h_contain⟩, rfl⟩
        have hp_main : squareToMain p_stand ∈ P_main :=
          Finset.mem_image.mpr ⟨p_stand, hp_stand, rfl⟩
        have h_main_in : squareToMain p_stand ∈ config.P₀ :=
          h_main_of_stand p_stand (hP_sub_stand hp_stand)
        have h_contain_main : InductionConfigurations.squareContained hnm (squareToMain p_stand) Q := by
          have h_roundtrip : squareToStand (squareToMain p_stand) = p_stand :=
            standToMainRoundtrip p_stand
          have h := squareContained_comm hnm Q (squareToMain p_stand)
          rw [h_roundtrip] at h
          exact h.mp h_contain
        exact ⟨hp_main, h_contain_main⟩
      · rintro ⟨hp_main, h_contain_main⟩
        have hp_stand : squareToStand p_main ∈ P_stand := hP_stand_conv p_main hp_main
        have h_contain_stand : _root_.squareContained hnm (squareToStand p_main) Q_stand :=
          (squareContained_comm hnm Q p_main).mpr h_contain_main
        exact ⟨squareToStand p_main, ⟨hp_stand, h_contain_stand⟩,
          mainToStandRoundtrip p_main⟩
    have h_goal : ((fineConfig_stand Q_stand hQ_stand).points.image squareToMain) =
        (P_main.filter fun p =>
          InductionConfigurations.squareContained hnm p Q).image
            (InductionConfigurations.squareHomothety hnm Q) := by
      rw [h1]
      have h2 : ((P_stand.filter fun p_stand =>
              _root_.squareContained hnm p_stand Q_stand).image
                (_root_.squareHomothety hnm Q_stand)).image squareToMain =
          (P_stand.filter fun p_stand =>
              _root_.squareContained hnm p_stand Q_stand).image
                (squareToMain ∘ _root_.squareHomothety hnm Q_stand) := by
        rw [Finset.image_image]
        <;> rfl
      rw [h2]
      have h3 : (squareToMain ∘ _root_.squareHomothety hnm Q_stand) =
          (InductionConfigurations.squareHomothety hnm Q ∘ squareToMain) := by
        funext p_stand
        exact homothety_comm hnm Q p_stand
      rw [h3]
      rw [←Finset.image_image]
      rw [h_P_filter_image]
    simpa [fineConfig_main] using h_goal

  constructor
  · -- Slope-cell identity
    intro Q hQ p hp hsc
    let Q_stand := squareToStand Q
    have hQ_stand : Q_stand ∈ coarseConfig_stand.points := h_coarse_mem_conv Q hQ
    let p_stand := squareToStand p
    have hp_stand : p_stand ∈ P_stand := hP_stand_conv p hp
    have h_main_in : p ∈ config.P₀ := hP_sub_main hp
    have hsc_stand : _root_.squareContained hnm p_stand Q_stand :=
      (squareContained_comm hnm Q p).mpr hsc
    rcases h_fine_slope Q_stand hQ_stand p_stand hp_stand hsc_stand with ⟨hq, h_eq⟩
    let p'_stand := _root_.squareHomothety hnm Q_stand p_stand
    let p'_main := InductionConfigurations.squareHomothety hnm Q p
    have h_p'_eq : squareToMain p'_stand = p'_main := homothety_comm hnm Q p_stand
    have hq' : p'_main ∈ (fineConfig_main Q hQ).P₀ := by
      dsimp only [fineConfig_main]
      exact Finset.mem_image.mpr ⟨p'_stand, hq, h_p'_eq⟩
    have h_tube_a_eq : ∀ (U : StandTube (n - m)),
        (tubeToMainShifted U).a = U.a := by
      intro U; rfl
    have h_reverse_a_eq : ∀ (C : StandTube n), C ∈ tubeFamily_stand p_stand hp_stand →
        (reverseMap p hp C).a = C.a := by
      intro C hC
      have h9 : C ∈ coveringCells n (reverseMap p hp C).a (reverseMap p hp C).b :=
        (h_reverseMap_spec p hp C hC).2
      have h10 : C.a = (reverseMap p hp C).a := by
        have h_general : ∀ (a b : ℤ), C ∈ coveringCells n a b → C.a = a := by
          intro a b h
          have h11 : C = (⟨a, b - 1⟩ : StandTube n) ∨
              C = (⟨a, b⟩ : StandTube n) ∨
              C = (⟨a, b + 1⟩ : StandTube n) := by
            simpa [coveringCells] using h
          rcases h11 with (h11 | h11 | h11)
          · simp [h11]
          · simp [h11]
          · simp [h11]
        exact h_general (reverseMap p hp C).a (reverseMap p hp C).b h9
      exact h10.symm
    have h_main_eq2 : ((fineConfig_main Q hQ).tubeFamily p'_main hq').image (fun U : MainTube (n - m) => U.a) =
        ((fineConfig_stand Q_stand hQ_stand).tubeFamily p'_stand hq).image (fun U : StandTube (n - m) => U.a) := by
      let standFamily := (fineConfig_stand Q_stand hQ_stand).tubeFamily p'_stand hq
      have h14 : ((fineConfig_main Q hQ).tubeFamily p'_main hq') = standFamily.image tubeToMainShifted := by
        dsimp only [fineConfig_main] <;> rfl
      rw [h14]
      have h15 : (standFamily.image tubeToMainShifted).image (fun U : MainTube (n - m) => U.a) =
          standFamily.image (fun U : StandTube (n - m) => U.a) := by
        have h16 : (standFamily.image tubeToMainShifted).image (fun U : MainTube (n - m) => U.a) =
            standFamily.image ((fun U : MainTube (n - m) => U.a) ∘ tubeToMainShifted) := by
          rw [Finset.image_image]
        rw [h16]
        apply Finset.image_congr
        intro U _
        exact h_tube_a_eq U
      exact h15
    have h_main_tube_eq : (tubeFamily_main p hp).image (fun T : MainTube n => localSlopeCellIndex m T.a) =
        (tubeFamily_stand p_stand hp_stand).image (fun C : StandTube n => localSlopeCellIndex m C.a) := by
      dsimp only [tubeFamily_main]
      rw [Finset.image_image]
      apply Finset.image_congr
      intro C hC
      have h_eq2 : (reverseMap p hp C).a = C.a := h_reverse_a_eq C hC
      have h_goal : localSlopeCellIndex m ((reverseMap p hp C).a) = localSlopeCellIndex m C.a := by
        rw [h_eq2]
      have h_comp : ((fun T : MainTube n => localSlopeCellIndex m T.a) ∘ reverseMap p hp) C =
          localSlopeCellIndex m ((reverseMap p hp C).a) := by
        rfl
      rw [h_comp]
      exact h_goal
    refine' ⟨hq', _⟩
    rw [h_main_eq2, h_main_tube_eq]
    exact h_eq

  constructor
  · -- Cardinality inequality
    intro Q hQ
    let Q_stand := squareToStand Q
    have hQ_stand : Q_stand ∈ coarseConfig_stand.points := h_coarse_mem_conv Q hQ
    have h_card : K * (sconfig.tubes.card : ℝ) * MΔ * MQ_stand Q_stand ≥
        (coarseConfig_stand.tubes.card : ℝ) *
          ((fineConfig_stand Q_stand hQ_stand).tubes.card : ℝ) * M_min :=
      h_cardinality Q_stand hQ_stand
    have h2 : sconfig.tubes.card ≤ 3 * config.T₀.card := by
      have h_sub : sconfig.tubes ⊆ config.T₀.biUnion (fun T => coveringCells n T.a T.b) := by
        intro C hC
        rcases Finset.mem_biUnion.mp hC with ⟨p, hp, hC2⟩
        have hC2' : C ∈ (config.tubeFamily p hp).biUnion (fun T => coveringCells n T.a T.b) := by
          simpa [hp] using hC2
        rcases Finset.mem_biUnion.mp hC2' with ⟨T, hT, hC3⟩
        have hT_in_T0 : T ∈ config.T₀ := config.h_subset p hp hT
        exact Finset.mem_biUnion.mpr ⟨T, hT_in_T0, hC3⟩
      calc sconfig.tubes.card
        ≤ (config.T₀.biUnion (fun T => coveringCells n T.a T.b)).card := Finset.card_le_card h_sub
        _ ≤ ∑ T ∈ config.T₀, (coveringCells n T.a T.b).card := Finset.card_biUnion_le
        _ = ∑ T ∈ config.T₀, 3 := by simp [coveringCells_card]
        _ = 3 * config.T₀.card := by simp [Finset.sum_const] <;> ring
    have h3 : (coarseConfig_main.T₀.card : ℝ) = (coarseConfig_stand.tubes.card : ℝ) := by
      dsimp only [coarseConfig_main]
      rw [Finset.card_image_of_injective _ tubeToMainShifted_inj] <;> rfl
    have h4 : ((fineConfig_main Q hQ).T₀.card : ℝ) =
        ((fineConfig_stand Q_stand hQ_stand).tubes.card : ℝ) := by
      dsimp only [fineConfig_main]
      rw [Finset.card_image_of_injective _ tubeToMainShifted_inj] <;> rfl
    have h5 : (MQ_main Q : ℝ) = (MQ_stand Q_stand : ℝ) := by
      simp [MQ_main] <;> rfl
    have hK_nonneg : 0 ≤ K := by linarith
    have hMΔ_nonneg' : (0 : ℝ) ≤ (MΔ : ℝ) := by positivity
    have hMQ_nonneg : 0 ≤ (MQ_main Q : ℝ) := by positivity
    exact expanded_bridge_cardinality K K' C₁ (MΔ : ℝ) M M_min
      sconfig.tubes.card config.T₀.card
      coarseConfig_stand.tubes.card (fineConfig_stand Q_stand hQ_stand).tubes.card
      coarseConfig_main.T₀.card (fineConfig_main Q hQ).T₀.card
      (MQ_stand Q_stand) (MQ_main Q)
      rfl hK_nonneg hM_le h2 h3 h4 h5 hMΔ_nonneg' hMQ_nonneg h_card

  · -- Slope bound for all coarse tubes
    intro T hT
    rcases Finset.mem_image.mp hT with ⟨U_stand, hU_stand, rfl⟩
    have h_strip : U_stand.IsInAllowedParameterStrip :=
      coarseConfig_stand.h_tube_parameters U_stand hU_stand
    exact stand_strip_implies_main_slope_bound h_strip

end DiscretisedFurstenbergEstimate.Bridge
