module

/-
  Bridge_Wrapper.lean

  Concrete wrapper around inductionOnScalesBridge using lagoon's S-set transfer lemmas.

  Transfer constants:
  - Forward IsDeltaSSet → IsFiniteTubeSSet: factor 10*C
      (5 from packing bound, 2 from L1→L∞ metric equivalence)
  - Reverse IsFiniteTubeSSet → IsDeltaSSet: factor 5*C
      (5 from packing bound; L∞→L1 Frostman is free since L1 ball ⊆ L∞ ball)
  - Forward incidence is taken as a hypothesis (geometrically requires
    additional assumptions beyond generic NiceConfiguration).

  Whiteprint node: B1_induction_on_scales / bridge_wrapper
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Bridge
public import MyLeanRepo.DiscretisedFurstenbergEstimate.BridgeGeometric
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Bridge_SSetTransfer
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FormatConversionLemmas
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

namespace DiscretisedFurstenbergEstimate.Bridge

open DiscretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.InductionOnScales
open DirecretisedFurstenbergEstimate.FormatConversion.M2

/-! ============================================================================
   Type-transfer helpers between main DyadicTube and standalone DyadicTube

   Both types are structurally identical (a, b : ℤ), and tubeToStand /
   tubeToMain / tubeToMainShifted preserve all relevant distances.
   ============================================================================ -/

/-- Helper: dyadicDelta equality across namespaces. -/
lemma delta_eq {n : ℕ} : (dyadicDelta n : ℝ) = _root_.dyadicDelta n := by
  simp [dyadicDelta, _root_.dyadicDelta] <;> rfl

/-- Helper: distance equality across tubeToStand. -/
lemma dist_eq_across_stand {n : ℕ} (T U : MainTube n) :
    tubeParamDistLinf T U = _root_.tubeParamDist (tubeToStand T) (tubeToStand U) := by
  unfold tubeParamDistLinf _root_.tubeParamDist tubeToStand
    DyadicTube.slope DyadicTube.intercept
    _root_.DyadicTube.slope _root_.DyadicTube.intercept
  have hδ : (dyadicDelta n : ℝ) = _root_.dyadicDelta n := delta_eq
  have h1 : |(T.a : ℝ) * dyadicDelta n - (U.a : ℝ) * dyadicDelta n| =
      |(T.a : ℝ) * _root_.dyadicDelta n - (U.a : ℝ) * _root_.dyadicDelta n| := by
    exact congr_arg (fun x : ℝ => |(T.a : ℝ) * x - (U.a : ℝ) * x|) hδ
  have h2 : |(T.b : ℝ) * dyadicDelta n - (U.b : ℝ) * dyadicDelta n| =
      |(T.b : ℝ) * _root_.dyadicDelta n - (U.b : ℝ) * _root_.dyadicDelta n| := by
    exact congr_arg (fun x : ℝ => |(T.b : ℝ) * x - (U.b : ℝ) * x|) hδ
  rw [h1, h2]

/-- Helper: distance equality across tubeToMainShifted (shift cancels). -/
lemma dist_eq_across_shifted {n : ℕ} (T U : StandTube n) :
    tubeParamDistLinf (tubeToMainShifted T) (tubeToMainShifted U) =
    _root_.tubeParamDist T U := by
  unfold tubeParamDistLinf _root_.tubeParamDist tubeToMainShifted
    DyadicTube.slope DyadicTube.intercept
    _root_.DyadicTube.slope _root_.DyadicTube.intercept
  have hδ : (dyadicDelta n : ℝ) = _root_.dyadicDelta n := delta_eq
  have h1 : |(T.a : ℝ) * dyadicDelta n - (U.a : ℝ) * dyadicDelta n| =
      |(T.a : ℝ) * _root_.dyadicDelta n - (U.a : ℝ) * _root_.dyadicDelta n| := by
    exact congr_arg (fun x : ℝ => |(T.a : ℝ) * x - (U.a : ℝ) * x|) hδ
  have h2 : |((T.b + 1 : ℤ) : ℝ) * dyadicDelta n - ((U.b + 1 : ℤ) : ℝ) * dyadicDelta n| =
      |(T.b : ℝ) * _root_.dyadicDelta n - (U.b : ℝ) * _root_.dyadicDelta n| := by
    have h_eq : ((T.b + 1 : ℤ) : ℝ) * dyadicDelta n - ((U.b + 1 : ℤ) : ℝ) * dyadicDelta n =
        (T.b : ℝ) * _root_.dyadicDelta n - (U.b : ℝ) * _root_.dyadicDelta n := by
      rw [hδ]
      simp [Int.cast_add, Int.cast_one] <;> ring
    rw [h_eq]
  rw [h1, h2]

/-- Transfer local IsFiniteTubeSSet across tubeToStand bijection. -/
lemma transfer_isFiniteTubeSSet_to_stand
    {n : ℕ} {s C : ℝ} {F : Finset (MainTube n)}
    (h : InductionOnScales.IsFiniteTubeSSet s C F) :
    _root_.IsFiniteTubeSSet s C (F.image tubeToStand) := by
  have h_inj : Function.Injective tubeToStand := tubeToStand_inj (n := n)
  have h_image_nonempty : (F.image tubeToStand).Nonempty :=
    Finset.Nonempty.image h.1 tubeToStand
  have h_sep : ∀ (T : StandTube n), T ∈ F.image tubeToStand →
      ∀ (U : StandTube n), U ∈ F.image tubeToStand → T ≠ U →
        _root_.dyadicDelta n ≤ _root_.tubeParamDist T U := by
    intro T hT U hU hne
    rcases Finset.mem_image.mp hT with ⟨T_main, hT_main, rfl⟩
    rcases Finset.mem_image.mp hU with ⟨U_main, hU_main, h_eq⟩
    have h_main_ne : T_main ≠ U_main := by
      intro h; apply hne; simpa [h] using h_eq
    have h1 : dyadicDelta n ≤ tubeParamDistLinf T_main U_main :=
      h.2.2.2.1 T_main hT_main U_main hU_main h_main_ne
    have h2 : _root_.dyadicDelta n ≤ _root_.tubeParamDist (tubeToStand T_main) (tubeToStand U_main) := by
      calc _root_.dyadicDelta n
        = dyadicDelta n := delta_eq.symm
      _ ≤ tubeParamDistLinf T_main U_main := h1
      _ = _root_.tubeParamDist (tubeToStand T_main) (tubeToStand U_main) :=
        dist_eq_across_stand T_main U_main
    rw [h_eq] at h2
    exact h2
  have h_frost : ∀ (center : StandTube n) (r : ℝ), _root_.dyadicDelta n ≤ r →
      (((F.image tubeToStand).filter fun T => _root_.tubeParamDist T center ≤ r).card : ℝ) ≤
        C * Real.rpow r s * ((F.image tubeToStand).card : ℝ) := by
    intro center r hr
    let center_main : MainTube n := tubeToMain center
    have h_center_eq : tubeToStand center_main = center := standToMainTubeRoundtrip center
    have hr_main : dyadicDelta n ≤ r := by rw [delta_eq]; exact hr
    have h_eq_filter : (F.image tubeToStand).filter (fun T => _root_.tubeParamDist T center ≤ r) =
        (F.filter fun T => tubeParamDistLinf T center_main ≤ r).image tubeToStand := by
      apply Finset.ext; intro x
      constructor
      · intro hx
        have h_x_in : x ∈ F.image tubeToStand := (Finset.mem_filter.mp hx).1
        have h_cond : _root_.tubeParamDist x center ≤ r := (Finset.mem_filter.mp hx).2
        rcases Finset.mem_image.mp h_x_in with ⟨x_main, hx_main, rfl⟩
        have h_cond2 : tubeParamDistLinf x_main center_main ≤ r := by
          have h : _root_.tubeParamDist (tubeToStand x_main) center ≤ r := h_cond
          rw [←h_center_eq] at h
          rw [←dist_eq_across_stand x_main center_main] at h
          exact h
        exact Finset.mem_image.mpr ⟨x_main, Finset.mem_filter.mpr ⟨hx_main, h_cond2⟩, rfl⟩
      · intro hx
        rcases Finset.mem_image.mp hx with ⟨x_main, hx_main, rfl⟩
        have h_cond : tubeParamDistLinf x_main center_main ≤ r := (Finset.mem_filter.mp hx_main).2
        have h_x_in : x_main ∈ F := (Finset.mem_filter.mp hx_main).1
        have h_cond2 : _root_.tubeParamDist (tubeToStand x_main) center ≤ r := by
          have h : tubeParamDistLinf x_main center_main ≤ r := h_cond
          rw [dist_eq_across_stand x_main center_main] at h
          rw [h_center_eq] at h
          exact h
        exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨x_main, h_x_in, rfl⟩, h_cond2⟩
    rw [h_eq_filter]
    have h_card : ((F.filter fun T => tubeParamDistLinf T center_main ≤ r).image tubeToStand).card =
        (F.filter fun T => tubeParamDistLinf T center_main ≤ r).card :=
      Finset.card_image_of_injective _ h_inj
    rw [h_card]
    have h_card_F : (F.image tubeToStand).card = F.card :=
      Finset.card_image_of_injective _ h_inj
    rw [h_card_F]
    exact h.2.2.2.2 center_main r hr_main
  refine' ⟨h_image_nonempty, h.2.1, h.2.2.1, h_sep, h_frost⟩

/-- Transfer standalone IsFiniteTubeSSet across tubeToMainShifted bijection
    to local IsFiniteTubeSSet on main tubes. The shift preserves distances. -/
lemma transfer_isFiniteTubeSSet_from_stand_shifted
    {n : ℕ} {s C : ℝ} {F : Finset (StandTube n)}
    (h : _root_.IsFiniteTubeSSet s C F) :
    InductionOnScales.IsFiniteTubeSSet s C (F.image tubeToMainShifted) := by
  have h_inj2 : Function.Injective tubeToMainShifted := tubeToMainShifted_inj (n := n)
  have h_image_nonempty : (F.image tubeToMainShifted).Nonempty :=
    Finset.Nonempty.image h.1 tubeToMainShifted
  have h_sep : ∀ (T : MainTube n), T ∈ F.image tubeToMainShifted →
      ∀ (U : MainTube n), U ∈ F.image tubeToMainShifted → T ≠ U →
        dyadicDelta n ≤ tubeParamDistLinf T U := by
    intro T hT U hU hne
    rcases Finset.mem_image.mp hT with ⟨T_stand, hT_stand, rfl⟩
    rcases Finset.mem_image.mp hU with ⟨U_stand, hU_stand, h_eq⟩
    have h_stand_ne : T_stand ≠ U_stand := by
      intro h; apply hne; simpa [h] using h_eq
    have h1 : _root_.dyadicDelta n ≤ _root_.tubeParamDist T_stand U_stand :=
      h.2.2.2.1 T_stand hT_stand U_stand hU_stand h_stand_ne
    have h2 : dyadicDelta n ≤ tubeParamDistLinf (tubeToMainShifted T_stand) (tubeToMainShifted U_stand) := by
      calc dyadicDelta n
        = _root_.dyadicDelta n := delta_eq
      _ ≤ _root_.tubeParamDist T_stand U_stand := h1
      _ = tubeParamDistLinf (tubeToMainShifted T_stand) (tubeToMainShifted U_stand) :=
        (dist_eq_across_shifted T_stand U_stand).symm
    rw [h_eq] at h2
    exact h2
  have h_frost : ∀ (center : MainTube n) (r : ℝ), dyadicDelta n ≤ r →
      (((F.image tubeToMainShifted).filter fun T => tubeParamDistLinf T center ≤ r).card : ℝ) ≤
        C * Real.rpow r s * ((F.image tubeToMainShifted).card : ℝ) := by
    intro center r hr
    let center_stand : StandTube n := ⟨center.a, center.b - 1⟩
    have h_center_eq : tubeToMainShifted center_stand = center := by
      cases center; simp [tubeToMainShifted, center_stand] <;> omega
    have hr_stand : _root_.dyadicDelta n ≤ r := by rw [←delta_eq]; exact hr
    have h_eq_filter : (F.image tubeToMainShifted).filter
        (fun T => tubeParamDistLinf T center ≤ r) =
        (F.filter fun T => _root_.tubeParamDist T center_stand ≤ r).image tubeToMainShifted := by
      apply Finset.ext; intro x
      constructor
      · intro hx
        have h_x_in : x ∈ F.image tubeToMainShifted := (Finset.mem_filter.mp hx).1
        have h_cond : tubeParamDistLinf x center ≤ r := (Finset.mem_filter.mp hx).2
        rcases Finset.mem_image.mp h_x_in with ⟨x_stand, hx_stand, rfl⟩
        have h_cond2 : _root_.tubeParamDist x_stand center_stand ≤ r := by
          have h : tubeParamDistLinf (tubeToMainShifted x_stand) center ≤ r := h_cond
          rw [←h_center_eq] at h
          rw [dist_eq_across_shifted x_stand center_stand] at h
          exact h
        exact Finset.mem_image.mpr ⟨x_stand, Finset.mem_filter.mpr ⟨hx_stand, h_cond2⟩, rfl⟩
      · intro hx
        rcases Finset.mem_image.mp hx with ⟨x_stand, hx_main, rfl⟩
        have h_cond : _root_.tubeParamDist x_stand center_stand ≤ r := (Finset.mem_filter.mp hx_main).2
        have h_x_in : x_stand ∈ F := (Finset.mem_filter.mp hx_main).1
        have h_cond2 : tubeParamDistLinf (tubeToMainShifted x_stand) center ≤ r := by
          have h : _root_.tubeParamDist x_stand center_stand ≤ r := h_cond
          rw [←dist_eq_across_shifted x_stand center_stand] at h
          rw [h_center_eq] at h
          exact h
        exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨x_stand, h_x_in, rfl⟩, h_cond2⟩
    rw [h_eq_filter]
    have h_card : ((F.filter fun T => _root_.tubeParamDist T center_stand ≤ r).image tubeToMainShifted).card =
        (F.filter fun T => _root_.tubeParamDist T center_stand ≤ r).card :=
      Finset.card_image_of_injective _ h_inj2
    rw [h_card]
    have h_card_F : (F.image tubeToMainShifted).card = F.card :=
      Finset.card_image_of_injective _ h_inj2
    rw [h_card_F]
    exact h.2.2.2.2 center_stand r hr_stand
  refine' ⟨h_image_nonempty, h.2.1, h.2.2.1, h_sep, h_frost⟩

/-- Transfer standalone IsFiniteTubeSSet across tubeToMain bijection
    to local IsFiniteTubeSSet on main tubes. No shift — exact roundtrip.
    Used for per-point retained tube families that were originally main tubes. -/
lemma transfer_isFiniteTubeSSet_from_stand
    {n : ℕ} {s C : ℝ} {F : Finset (StandTube n)}
    (h : _root_.IsFiniteTubeSSet s C F) :
    InductionOnScales.IsFiniteTubeSSet s C (F.image tubeToMain) := by
  have h_inj : Function.Injective tubeToMain := tubeToMain_inj (n := n)
  have h_image_nonempty : (F.image tubeToMain).Nonempty :=
    Finset.Nonempty.image h.1 tubeToMain
  have h_dist_eq : ∀ (T U : StandTube n),
      tubeParamDistLinf (tubeToMain T) (tubeToMain U) = _root_.tubeParamDist T U := by
    intro T U
    unfold tubeParamDistLinf _root_.tubeParamDist tubeToMain
      DyadicTube.slope DyadicTube.intercept
      _root_.DyadicTube.slope _root_.DyadicTube.intercept
    have hδ : (dyadicDelta n : ℝ) = _root_.dyadicDelta n := delta_eq
    rw [hδ] <;> rfl
  have h_sep : ∀ (T : MainTube n), T ∈ F.image tubeToMain →
      ∀ (U : MainTube n), U ∈ F.image tubeToMain → T ≠ U →
        dyadicDelta n ≤ tubeParamDistLinf T U := by
    intro T hT U hU hne
    rcases Finset.mem_image.mp hT with ⟨Ts, hTs, rfl⟩
    rcases Finset.mem_image.mp hU with ⟨Us, hUs, h_eq⟩
    have hne' : Ts ≠ Us := by intro h; apply hne; simpa [h] using h_eq
    have h1 := h.2.2.2.1 Ts hTs Us hUs hne'
    have h2 : dyadicDelta n ≤ tubeParamDistLinf (tubeToMain Ts) (tubeToMain Us) := by
      rw [h_dist_eq Ts Us]; rw [delta_eq]; exact h1
    rw [h_eq] at h2; exact h2
  have h_frost : ∀ (center : MainTube n) (r : ℝ), dyadicDelta n ≤ r →
      (((F.image tubeToMain).filter fun T => tubeParamDistLinf T center ≤ r).card : ℝ) ≤
        C * Real.rpow r s * ((F.image tubeToMain).card : ℝ) := by
    intro center r hr
    let cs := tubeToStand center
    have hce : tubeToMain cs = center := mainToStandTubeRoundtrip center
    have hrs : _root_.dyadicDelta n ≤ r := by rw [←delta_eq]; exact hr
    have h_eq_filter : (F.image tubeToMain).filter (fun T => tubeParamDistLinf T center ≤ r) =
        (F.filter fun T => _root_.tubeParamDist T cs ≤ r).image tubeToMain := by
      apply Finset.ext; intro x
      constructor
      · intro hx
        have hxi : x ∈ F.image tubeToMain := (Finset.mem_filter.mp hx).1
        have hcond : tubeParamDistLinf x center ≤ r := (Finset.mem_filter.mp hx).2
        rcases Finset.mem_image.mp hxi with ⟨xs, hxs, rfl⟩
        have hcond2 : _root_.tubeParamDist xs cs ≤ r := by
          have h : tubeParamDistLinf (tubeToMain xs) (tubeToMain cs) ≤ r := by
            rw [hce]; exact hcond
          rw [h_dist_eq xs cs] at h; exact h
        exact Finset.mem_image.mpr ⟨xs, Finset.mem_filter.mpr ⟨hxs, hcond2⟩, rfl⟩
      · intro hx
        rcases Finset.mem_image.mp hx with ⟨xs, hxs', rfl⟩
        have hcond : _root_.tubeParamDist xs cs ≤ r := (Finset.mem_filter.mp hxs').2
        have hxi : xs ∈ F := (Finset.mem_filter.mp hxs').1
        have hcond2 : tubeParamDistLinf (tubeToMain xs) center ≤ r := by
          have h : tubeParamDistLinf (tubeToMain xs) (tubeToMain cs) ≤ r := by
            rw [h_dist_eq xs cs]; exact hcond
          rw [hce] at h; exact h
        exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨xs, hxi, rfl⟩, hcond2⟩
    rw [h_eq_filter]
    have h1 : ((F.filter fun T => _root_.tubeParamDist T cs ≤ r).image tubeToMain).card =
        (F.filter fun T => _root_.tubeParamDist T cs ≤ r).card :=
      Finset.card_image_of_injective _ h_inj
    have h2 : (F.image tubeToMain).card = F.card := Finset.card_image_of_injective _ h_inj
    rw [h1, h2]
    exact h.2.2.2.2 cs r hrs
  refine' ⟨h_image_nonempty, h.2.1, h.2.2.1, h_sep, h_frost⟩

/-! ============================================================================
   Concrete S-set transfer parameters for inductionOnScalesBridge
   ============================================================================ -/

/-- Forward S-set transfer: main IsDeltaSSet → standalone IsFiniteTubeSSet
    with constant 10*C₁. -/
lemma sset_transfer_concrete
    {n : ℕ} {s C₁ : ℝ} (hs : 0 ≤ s) (hs_one : s ≤ 1) (hC₁ : 1 ≤ C₁)
    (F : Finset (MainTube n))
    (h : IsDeltaSSet (dyadicDelta n) s C₁ (F : Set (MainTube n))) :
    ∃ (C' : ℝ), C' ≤ C₁ * 10 ∧ 1 ≤ C' ∧
      _root_.IsFiniteTubeSSet s C' (F.image tubeToStand) := by
  have h1 : InductionOnScales.DiscreteFrostmanL1 s (5 * C₁) F :=
    isDeltaSSet_to_discreteFrostmanL1 h
  have h2 : InductionOnScales.IsFiniteTubeSSet s (max 1 (2 * (5 * C₁))) F :=
    discreteFrostmanL1_to_isFiniteTubeSSet hs_one hs h1
  have h3 : max 1 (2 * (5 * C₁)) = 10 * C₁ := by
    have h4 : 1 ≤ 10 * C₁ := by linarith
    rw [max_eq_right] <;> linarith
  rw [h3] at h2
  have h4 : _root_.IsFiniteTubeSSet s (10 * C₁) (F.image tubeToStand) :=
    transfer_isFiniteTubeSSet_to_stand h2
  exact ⟨10 * C₁, by linarith, by linarith, h4⟩

/-- Reverse S-set transfer: standalone IsFiniteTubeSSet → main IsDeltaSSet
    on shifted tubes, with constant 5*C. -/
lemma sset_transfer_rev_concrete
    {k : ℕ} {s C : ℝ} (hs : 0 ≤ s) (hC_one : 1 ≤ C)
    (F : Finset (StandTube k))
    (h : _root_.IsFiniteTubeSSet s C F) :
    IsDeltaSSet (dyadicDelta k) s (5 * C)
      (F.image tubeToMainShifted : Set (MainTube k)) := by
  have h1 : InductionOnScales.IsFiniteTubeSSet s C (F.image tubeToMainShifted) :=
    transfer_isFiniteTubeSSet_from_stand_shifted h
  exact isFiniteTubeSSet_to_isDeltaSSet hs hC_one h1

open DiscretisedFurstenbergEstimate.Bridge.Geometric

/-- Double counting identity: sum of set sizes equals sum of fiber sizes. -/
lemma double_counting {α β : Type*} [DecidableEq β] (s : Finset α) (t : α → Finset β) :
    ∑ i ∈ s, (t i).card = ∑ j ∈ s.biUnion t, (s.filter (fun i => j ∈ t i)).card := by
  let pairs : Finset (α × β) := s.biUnion (fun i => (t i).image (Prod.mk i))
  have h_disj : Set.PairwiseDisjoint (↑s) (fun i : α => (t i).image (Prod.mk i)) := by
    intro i _ j _ hne
    simp [Finset.disjoint_left, hne] <;> tauto
  have h1 : pairs.card = ∑ i ∈ s, ((t i).image (Prod.mk i)).card :=
    Finset.card_biUnion h_disj
  have h1' : ∀ i ∈ s, ((t i).image (Prod.mk i)).card = (t i).card := by
    intro i _
    apply Finset.card_image_of_injective
    intro j1 j2 h
    injection h
  have h_card1 : pairs.card = ∑ i ∈ s, (t i).card := by
    rw [h1, Finset.sum_congr rfl h1']
  have h_image : pairs.image Prod.snd = s.biUnion t := by
    ext j
    simp [pairs, Finset.mem_biUnion] <;> aesop
  have h_mapsTo : Set.MapsTo Prod.snd (↑pairs : Set (α × β)) (↑(s.biUnion t) : Set β) := by
    intro x hx
    have h_in : x.2 ∈ s.biUnion t := by
      rw [←h_image]
      exact Finset.mem_image_of_mem Prod.snd hx
    exact h_in
  have h_card2 : pairs.card = ∑ j ∈ s.biUnion t, (pairs.filter (fun p => p.2 = j)).card :=
    Finset.card_eq_sum_card_fiberwise h_mapsTo
  have h_fiber : ∀ j ∈ s.biUnion t, (pairs.filter (fun p : α × β => p.2 = j)).card =
      (s.filter (fun i => j ∈ t i)).card := by
    intro j _
    let fiber_pairs := pairs.filter (fun p : α × β => p.2 = j)
    let fiber_s := s.filter (fun i => j ∈ t i)
    have h_inj : Set.InjOn (fun (p : α × β) => p.1) fiber_pairs := by
      intro p1 hp1 p2 hp2 h
      have h_eq : p1.1 = p2.1 := h
      have h_p12 : p1.2 = p2.2 := by
        have h1 : p1.2 = j := (Finset.mem_filter.mp hp1).2
        have h2 : p2.2 = j := (Finset.mem_filter.mp hp2).2
        exact h1.trans h2.symm
      exact Prod.ext h_eq h_p12
    have h_image : fiber_pairs.image (fun (p : α × β) => p.1) = fiber_s := by
      ext i
      simp only [fiber_pairs, fiber_s, Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨p, hp, rfl⟩
        have h5 : p ∈ pairs := hp.1
        have h_p2 : p.2 = j := hp.2
        rcases Finset.mem_biUnion.mp h5 with ⟨k, hk, hpk⟩
        simp only [Finset.mem_image] at hpk
        rcases hpk with ⟨l, hl, hpl⟩
        have h_p_eq : p = (k, l) := hpl.symm
        have h_p1 : p.1 = k := by
          exact congr_arg Prod.fst h_p_eq
        have h_j_in : j ∈ t k := by
          have h : p.2 = l := by
            exact congr_arg Prod.snd h_p_eq
          have h_l_in : l ∈ t k := hl
          rw [h] at h_p2
          rw [h_p2] at h_l_in
          exact h_l_in
        exact ⟨by simpa [h_p1] using hk, by simpa [h_p1] using h_j_in⟩
      · intro hi
        have h_j_in : j ∈ t i := hi.2
        have h_p_in : (i, j) ∈ pairs := by
          apply Finset.mem_biUnion.mpr
          exact ⟨i, hi.1, Finset.mem_image_of_mem _ h_j_in⟩
        have h_filter : (i, j) ∈ fiber_pairs := by
          exact Finset.mem_filter.mpr ⟨h_p_in, by simp⟩
        have h_and : (i, j) ∈ pairs ∧ (i, j).2 = j := Finset.mem_filter.mp h_filter
        exact ⟨(i, j), h_and, rfl⟩
    have h_card : fiber_pairs.card = (fiber_pairs.image (fun (p : α × β) => p.1)).card :=
      (Finset.card_image_of_injOn h_inj).symm
    rw [h_card, h_image]
  rw [←h_card1, h_card2]
  apply Finset.sum_congr rfl
  intro j hj
  exact h_fiber j hj
lemma coveringCells_dist_bound {n : ℕ} (T : MainTube n) (C : StandTube n)
    (h : C ∈ coveringCells n T.a T.b) :
    _root_.tubeParamDist (tubeToStand T) C ≤ _root_.dyadicDelta n := by
  have hδ_pos : 0 < _root_.dyadicDelta n := _root_.dyadicDelta_pos n
  have hδ_nonneg : 0 ≤ _root_.dyadicDelta n := le_of_lt hδ_pos
  have h4 : C = (⟨T.a, T.b - 1⟩ : StandTube n) ∨
      C = (⟨T.a, T.b⟩ : StandTube n) ∨
      C = (⟨T.a, T.b + 1⟩ : StandTube n) := by
    simpa [coveringCells] using h
  rcases h4 with (h4 | h4 | h4)
  · rw [h4]
    have h_simp : _root_.tubeParamDist (tubeToStand T) (⟨T.a, T.b - 1⟩ : StandTube n) =
        |_root_.dyadicDelta n| := by
      simp [_root_.tubeParamDist, _root_.DyadicTube.slope, _root_.DyadicTube.intercept, tubeToStand]
      <;> ring_nf <;> norm_num
    rw [h_simp]
    have h_abs : |_root_.dyadicDelta n| = _root_.dyadicDelta n := abs_of_pos hδ_pos
    rw [h_abs]
  · rw [h4]
    simp [_root_.tubeParamDist, _root_.DyadicTube.slope, _root_.DyadicTube.intercept, tubeToStand, hδ_nonneg]
    <;> norm_num <;> linarith
  · rw [h4]
    have h_simp : _root_.tubeParamDist (tubeToStand T) (⟨T.a, T.b + 1⟩ : StandTube n) =
        |_root_.dyadicDelta n| := by
      simp [_root_.tubeParamDist, _root_.DyadicTube.slope, _root_.DyadicTube.intercept, tubeToStand]
      <;> ring_nf <;> norm_num
    rw [h_simp]
    have h_abs : |_root_.dyadicDelta n| = _root_.dyadicDelta n := abs_of_pos hδ_pos
    rw [h_abs]

/-- Triangle inequality for tubeParamDist (L∞ distance). -/
lemma tubeParamDist_triangle {n : ℕ} (A B C : StandTube n) :
    _root_.tubeParamDist A C ≤ _root_.tubeParamDist A B + _root_.tubeParamDist B C := by
  let d (X Y : StandTube n) := _root_.tubeParamDist X Y
  have h1 : |A.slope - C.slope| ≤ d A B + d B C := by
    have h_tri : |A.slope - C.slope| ≤ |A.slope - B.slope| + |B.slope - C.slope| := by
      exact abs_sub_le A.slope B.slope C.slope
    have h1a : |A.slope - B.slope| ≤ d A B := by
      have h_def : d A B = max (|A.slope - B.slope|) (|A.intercept - B.intercept|) := by rfl
      rw [h_def]
      exact le_max_left (|A.slope - B.slope|) (|A.intercept - B.intercept|)
    have h1b : |B.slope - C.slope| ≤ d B C := by
      have h_def : d B C = max (|B.slope - C.slope|) (|B.intercept - C.intercept|) := by rfl
      rw [h_def]
      exact le_max_left (|B.slope - C.slope|) (|B.intercept - C.intercept|)
    linarith
  have h2 : |A.intercept - C.intercept| ≤ d A B + d B C := by
    have h_tri : |A.intercept - C.intercept| ≤ |A.intercept - B.intercept| + |B.intercept - C.intercept| := by
      exact abs_sub_le A.intercept B.intercept C.intercept
    have h2a : |A.intercept - B.intercept| ≤ d A B := by
      have h_def : d A B = max (|A.slope - B.slope|) (|A.intercept - B.intercept|) := by rfl
      rw [h_def]
      exact le_max_right (|A.slope - B.slope|) (|A.intercept - B.intercept|)
    have h2b : |B.intercept - C.intercept| ≤ d B C := by
      have h_def : d B C = max (|B.slope - C.slope|) (|B.intercept - C.intercept|) := by rfl
      rw [h_def]
      exact le_max_right (|B.slope - C.slope|) (|B.intercept - C.intercept|)
    linarith
  exact max_le h1 h2

/-- Forward S-set transfer for expanded family: main IsDeltaSSet C₁ →
    standalone IsFiniteTubeSSet (60*C₁) on the 3-cell expansion.

    Proof sketch:
    - Each main tube expands to 3 standalone cells
    - Each cell comes from at most 3 main tubes
    - L∞ cell distance ≤ r implies L1 tube distance ≤ 4r
    - Frostman: |cells in ball| ≤ 3 * (5*C₁) * (4r)^s * |F| ≤ 60*C₁ * r^s * |E|
    - Uses |F| ≤ |E| from the 3-to-3 correspondence
-/
lemma sset_transfer_expanded_concrete
    {n : ℕ} {s C₁ : ℝ} (hs : 0 ≤ s) (hs_one : s ≤ 1) (hC₁ : 1 ≤ C₁)
    (F : Finset (MainTube n))
    (h : IsDeltaSSet (dyadicDelta n) s C₁ (F : Set (MainTube n))) :
    ∃ (C' : ℝ), C' ≤ C₁ * 60 ∧ 1 ≤ C' ∧
      _root_.IsFiniteTubeSSet s C' (F.biUnion (fun T => coveringCells n T.a T.b)) := by
  let E := F.biUnion (fun T : MainTube n => coveringCells n T.a T.b)
  have hF_nonempty : F.Nonempty := h.1
  have hE_nonempty : E.Nonempty := by
    exact hF_nonempty.biUnion (fun T _ => by
      simp [coveringCells] <;> decide)
  have h_frost1 : DiscreteFrostmanL1 s (5 * C₁) F :=
    isDeltaSSet_to_discreteFrostmanL1 h
  -- |F| ≤ |E| via double counting: 3|F| = total incidences ≤ 3|E|
  have hF_le_E : (F.card : ℝ) ≤ (E.card : ℝ) := by
    have h_sum1 : ∑ T ∈ F, (coveringCells n T.a T.b).card = 3 * F.card := by
      have h2 : ∀ T ∈ F, (coveringCells n T.a T.b).card = 3 :=
        fun T _ => coveringCells_card n T.a T.b
      rw [Finset.sum_congr rfl h2, Finset.sum_const, mul_comm] <;> ring
    have h_sum2 : ∑ T ∈ F, (coveringCells n T.a T.b).card =
        ∑ C ∈ E, (F.filter (fun T => C ∈ coveringCells n T.a T.b)).card :=
      double_counting F (fun T : MainTube n => coveringCells n T.a T.b)
    have h_sum3 : ∑ C ∈ E, (F.filter (fun T => C ∈ coveringCells n T.a T.b)).card ≤ 3 * E.card := by
      calc ∑ C ∈ E, (F.filter (fun T => C ∈ coveringCells n T.a T.b)).card
        ≤ ∑ C ∈ E, 3 := Finset.sum_le_sum (fun C _ => preimage_candidates_le_3 C F)
      _ = 3 * E.card := by simp [Finset.sum_const] <;> ring
    have h6 : 3 * F.card ≤ 3 * E.card := by
      rw [←h_sum1, h_sum2] <;> exact h_sum3
    have h7 : F.card ≤ E.card := by nlinarith
    exact_mod_cast h7
  -- Separation: distinct standalone cells are δ-separated in L∞
  have hδ_pos' : 0 < _root_.dyadicDelta n := _root_.dyadicDelta_pos n
  have h_sep : ∀ (C : StandTube n), C ∈ E → ∀ (D : StandTube n), D ∈ E → C ≠ D →
      _root_.dyadicDelta n ≤ _root_.tubeParamDist C D := by
    intro C _ D _ hne
    have h1 : C.a ≠ D.a ∨ C.b ≠ D.b := by
      by_contra h
      push Not at h
      have h_eq : C = D := by
        cases C; cases D; simp_all
      exact hne h_eq
    rcases h1 with (h1 | h1)
    · have h2 : (1 : ℝ) ≤ |(C.a : ℝ) - (D.a : ℝ)| := by exact_mod_cast (abs_sub_pos.mpr h1)
      have h_slope_diff : |_root_.DyadicTube.slope C - _root_.DyadicTube.slope D| =
          |(C.a : ℝ) - (D.a : ℝ)| * _root_.dyadicDelta n := by
        have h_eq : _root_.DyadicTube.slope C - _root_.DyadicTube.slope D =
            ((C.a : ℝ) - (D.a : ℝ)) * _root_.dyadicDelta n := by
          simp [_root_.DyadicTube.slope] <;> ring
        rw [h_eq]
        have h_abs : |((C.a : ℝ) - (D.a : ℝ)) * _root_.dyadicDelta n| =
            |(C.a : ℝ) - (D.a : ℝ)| * |_root_.dyadicDelta n| := by rw [abs_mul]
        rw [h_abs]
        have hδ_abs : |_root_.dyadicDelta n| = _root_.dyadicDelta n := by
          rw [abs_of_pos hδ_pos']
        rw [hδ_abs] <;> rfl
      have h3 : _root_.dyadicDelta n ≤ |_root_.DyadicTube.slope C - _root_.DyadicTube.slope D| := by
        rw [h_slope_diff]
        have h4 : _root_.dyadicDelta n ≤ |(C.a : ℝ) - (D.a : ℝ)| * _root_.dyadicDelta n := by
          nlinarith [hδ_pos']
        exact h4
      have h5 : |_root_.DyadicTube.slope C - _root_.DyadicTube.slope D| ≤ _root_.tubeParamDist C D := by
        exact le_max_left _ _
      linarith
    · have h2 : (1 : ℝ) ≤ |(C.b : ℝ) - (D.b : ℝ)| := by exact_mod_cast (abs_sub_pos.mpr h1)
      have h_int_diff : |_root_.DyadicTube.intercept C - _root_.DyadicTube.intercept D| =
          |(C.b : ℝ) - (D.b : ℝ)| * _root_.dyadicDelta n := by
        have h_eq : _root_.DyadicTube.intercept C - _root_.DyadicTube.intercept D =
            ((C.b : ℝ) - (D.b : ℝ)) * _root_.dyadicDelta n := by
          simp [_root_.DyadicTube.intercept] <;> ring
        rw [h_eq]
        have h_abs : |((C.b : ℝ) - (D.b : ℝ)) * _root_.dyadicDelta n| =
            |(C.b : ℝ) - (D.b : ℝ)| * |_root_.dyadicDelta n| := by rw [abs_mul]
        rw [h_abs]
        have hδ_abs : |_root_.dyadicDelta n| = _root_.dyadicDelta n := by
          rw [abs_of_pos hδ_pos']
        rw [hδ_abs] <;> rfl
      have h3 : _root_.dyadicDelta n ≤ |_root_.DyadicTube.intercept C - _root_.DyadicTube.intercept D| := by
        rw [h_int_diff]
        have h4 : _root_.dyadicDelta n ≤ |(C.b : ℝ) - (D.b : ℝ)| * _root_.dyadicDelta n := by
          nlinarith [hδ_pos']
        exact h4
      have h5 : |_root_.DyadicTube.intercept C - _root_.DyadicTube.intercept D| ≤ _root_.tubeParamDist C D := by
        exact le_max_right _ _
      linarith
  -- Frostman condition for E
  have h_frost_E : ∀ (center : StandTube n) (r : ℝ), _root_.dyadicDelta n ≤ r →
      ((E.filter fun C => _root_.tubeParamDist C center ≤ r).card : ℝ) ≤
        (60 * C₁) * Real.rpow r s * (E.card : ℝ) := by
    intro center r hr
    let T0 : MainTube n := tubeToMain center
    let S := E.filter fun C => _root_.tubeParamDist C center ≤ r
    let F' := F.filter fun T : MainTube n => T.dist T0 ≤ 4 * r
    have h1 : S ⊆ F'.biUnion (fun T : MainTube n => coveringCells n T.a T.b) := by
      intro C hC
      have hC_in_E : C ∈ E := (Finset.mem_filter.mp hC).1
      have hC_dist : _root_.tubeParamDist C center ≤ r := (Finset.mem_filter.mp hC).2
      rcases Finset.mem_biUnion.mp hC_in_E with ⟨T, hT, hCT⟩
      have h3 : _root_.tubeParamDist (tubeToStand T) C ≤ _root_.dyadicDelta n :=
        coveringCells_dist_bound T C hCT
      have h2 : _root_.tubeParamDist (tubeToStand T) center ≤ 2 * r := by
        calc _root_.tubeParamDist (tubeToStand T) center
          ≤ _root_.tubeParamDist (tubeToStand T) C + _root_.tubeParamDist C center :=
            tubeParamDist_triangle (tubeToStand T) C center
        _ ≤ _root_.dyadicDelta n + r := by gcongr
        _ ≤ 2 * r := by
          have hδ : _root_.dyadicDelta n ≤ r := hr
          linarith
      have h4 : T.dist T0 ≤ 4 * r := by
        have h5 : T.dist T0 ≤ 2 * _root_.tubeParamDist (tubeToStand T) center := by
          have hδ : (dyadicDelta n : ℝ) = _root_.dyadicDelta n := delta_eq
          have h_dist_eq : T.dist T0 = (dyadicDelta n) * ((|(T.a - T0.a : ℤ)| : ℝ) + (|(T.b - T0.b : ℤ)| : ℝ)) :=
            DyadicTube.dist_eq T T0
          have h_tp : _root_.tubeParamDist (tubeToStand T) center =
              _root_.dyadicDelta n * max (|(T.a - center.a : ℤ)| : ℝ) (|(T.b - center.b : ℤ)| : ℝ) := by
            let δ := _root_.dyadicDelta n
            have hδ_pos : 0 < δ := _root_.dyadicDelta_pos n
            have hδ_nonneg : 0 ≤ δ := le_of_lt hδ_pos
            have h_slope : (tubeToStand T).slope - center.slope = δ * ((T.a : ℝ) - (center.a : ℝ)) := by
              simp [tubeToStand, _root_.DyadicTube.slope] <;> ring
            have h_intercept : (tubeToStand T).intercept - center.intercept = δ * ((T.b : ℝ) - (center.b : ℝ)) := by
              simp [tubeToStand, _root_.DyadicTube.intercept] <;> ring
            have h_cast1 : |((T.a : ℝ) - (center.a : ℝ))| = (|(T.a - center.a : ℤ)| : ℝ) := by
              have h_eq : ((T.a : ℝ) - (center.a : ℝ)) = ↑(T.a - center.a) := by
                simp <;> norm_cast
              rw [h_eq]
            have h_cast2 : |((T.b : ℝ) - (center.b : ℝ))| = (|(T.b - center.b : ℤ)| : ℝ) := by
              have h_eq : ((T.b : ℝ) - (center.b : ℝ)) = ↑(T.b - center.b) := by
                simp <;> norm_cast
              rw [h_eq]
            have h_abs1 : |(tubeToStand T).slope - center.slope| = δ * (|(T.a - center.a : ℤ)| : ℝ) := by
              rw [h_slope, abs_mul, abs_of_pos hδ_pos, h_cast1]
            have h_abs2 : |(tubeToStand T).intercept - center.intercept| = δ * (|(T.b - center.b : ℤ)| : ℝ) := by
              rw [h_intercept, abs_mul, abs_of_pos hδ_pos, h_cast2]
            have h_def : _root_.tubeParamDist (tubeToStand T) center =
                max |(tubeToStand T).slope - center.slope| |(tubeToStand T).intercept - center.intercept| := by rfl
            rw [h_def, h_abs1, h_abs2, mul_max_of_nonneg _ _ hδ_nonneg]
          have hT0a : T0.a = center.a := by simp [T0, tubeToMain]
          have hT0b : T0.b = center.b := by simp [T0, tubeToMain]
          rw [h_dist_eq, h_tp, hδ, hT0a, hT0b]
          set a : ℝ := (|(T.a - center.a : ℤ)| : ℝ) with ha
          set b : ℝ := (|(T.b - center.b : ℤ)| : ℝ) with hb
          have h_sum : a + b ≤ 2 * max a b := by
            cases' le_total a b with h h <;> simp [h, max_def] <;> linarith
          have hδ_pos : 0 ≤ _root_.dyadicDelta n := by positivity
          nlinarith
        linarith [h2, h5]
      have hT_in_F' : T ∈ F' := Finset.mem_filter.mpr ⟨hT, h4⟩
      exact Finset.mem_biUnion.mpr ⟨T, hT_in_F', hCT⟩
    have h_card_S : (S.card : ℝ) ≤ 3 * (F'.card : ℝ) := by
      have h_biUnion_card : (F'.biUnion (fun T : MainTube n => coveringCells n T.a T.b)).card ≤
          ∑ T ∈ F', (coveringCells n T.a T.b).card := Finset.card_biUnion_le
      have h_sum3 : ∑ T ∈ F', (coveringCells n T.a T.b).card = 3 * F'.card := by
        have h2 : ∀ T ∈ F', (coveringCells n T.a T.b).card = 3 :=
          fun T _ => coveringCells_card n T.a T.b
        rw [Finset.sum_congr rfl h2, Finset.sum_const, mul_comm] <;> ring
      have h_sum3' : (∑ T ∈ F', (coveringCells n T.a T.b).card : ℝ) = (3 * F'.card : ℝ) := by
        exact_mod_cast h_sum3
      have h1' : (S.card : ℝ) ≤ ((F'.biUnion (fun T : MainTube n => coveringCells n T.a T.b)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card h1
      have h2' : ((F'.biUnion (fun T : MainTube n => coveringCells n T.a T.b)).card : ℝ) ≤
          (∑ T ∈ F', (coveringCells n T.a T.b).card : ℝ) := by
        exact_mod_cast h_biUnion_card
      calc (S.card : ℝ)
        ≤ ((F'.biUnion (fun T : MainTube n => coveringCells n T.a T.b)).card : ℝ) := h1'
      _ ≤ (∑ T ∈ F', (coveringCells n T.a T.b).card : ℝ) := h2'
      _ = (3 * F'.card : ℝ) := h_sum3'
    have h_frost_F' : (F'.card : ℝ) ≤ (5 * C₁) * Real.rpow (4 * r) s * (F.card : ℝ) :=
      h_frost1.2.2.2 T0 (4 * r) (by
        have hδ : (dyadicDelta n : ℝ) = _root_.dyadicDelta n := delta_eq
        have h_goal : dyadicDelta n ≤ 4 * r := by
          rw [hδ]
          linarith [hr]
        exact h_goal)
    have h_main : (S.card : ℝ) ≤ (60 * C₁) * Real.rpow r s * (E.card : ℝ) := by
      have hC₁_nonneg : 0 ≤ C₁ := by linarith
      have hr_nonneg : 0 ≤ r := by linarith [_root_.dyadicDelta_pos n, hr]
      have h_rpow4r_nonneg : 0 ≤ Real.rpow (4 * r) s := Real.rpow_nonneg (by linarith) s
      have h_rpow : Real.rpow (4 * r) s = Real.rpow 4 s * Real.rpow r s :=
        Real.mul_rpow (by norm_num) hr_nonneg
      have h6 : Real.rpow 4 s ≤ 4 := by
        have h61 : Real.rpow 4 s ≤ Real.rpow 4 (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        have h62 : Real.rpow 4 (1 : ℝ) = 4 := by norm_num
        rw [h62] at h61
        exact h61
      calc (S.card : ℝ)
        ≤ 3 * (F'.card : ℝ) := h_card_S
      _ ≤ 3 * ((5 * C₁) * Real.rpow (4 * r) s * (F.card : ℝ)) := by gcongr
      _ = 15 * C₁ * Real.rpow (4 * r) s * (F.card : ℝ) := by ring
      _ ≤ 15 * C₁ * Real.rpow (4 * r) s * (E.card : ℝ) := by
        have h_pos : 0 ≤ 15 * C₁ * Real.rpow (4 * r) s := by
          exact mul_nonneg (mul_nonneg (by norm_num) hC₁_nonneg) h_rpow4r_nonneg
        nlinarith [hF_le_E]
      _ = 15 * C₁ * (Real.rpow 4 s * Real.rpow r s) * (E.card : ℝ) := by
        rw [show Real.rpow (4 * r) s = Real.rpow 4 s * Real.rpow r s from h_rpow] <;> ring
      _ = (15 * Real.rpow 4 s * C₁) * Real.rpow r s * (E.card : ℝ) := by ring
      _ ≤ (60 * C₁) * Real.rpow r s * (E.card : ℝ) := by
        have h8 : 0 ≤ Real.rpow r s := Real.rpow_nonneg hr_nonneg s
        have h9 : 0 ≤ (E.card : ℝ) := by positivity
        have h10 : 0 ≤ C₁ * Real.rpow r s * (E.card : ℝ) := by positivity
        have h11 : 15 * Real.rpow 4 s ≤ 60 := by linarith [h6]
        have h12 : (15 * Real.rpow 4 s) * (C₁ * Real.rpow r s * (E.card : ℝ)) ≤
            60 * (C₁ * Real.rpow r s * (E.card : ℝ)) :=
          mul_le_mul_of_nonneg_right h11 h10
        ring_nf at h12 ⊢
        exact h12
    exact h_main
  have h_sset_E : _root_.IsFiniteTubeSSet s (60 * C₁) E :=
    ⟨hE_nonempty, by linarith, hs, h_sep, h_frost_E⟩
  exact ⟨60 * C₁, by linarith, by linarith, h_sset_E⟩

/-! ============================================================================
   Wrapper theorem
   ============================================================================ -/

/-- Concrete wrapper around inductionOnScalesBridge using lagoon's transfer lemmas.

    The forward incidence transfer is taken as a hypothesis because it requires
    additional geometric assumptions: a generic strip-square intersection does
    not imply a cell-square intersection (counterexample within unit square).

    Transfer constants:
    - Forward S-set: 10*C₁
    - Reverse S-set: 5*C
    - Total K scaling: 50
-/
theorem inductionOnScalesBridge_concrete
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
    (incidence_transfer : ∀ (p : MainSquare n) (hp : p ∈ config.P₀)
      (T : MainTube n) (hT : T ∈ config.tubeFamily p hp),
      ((tubeToStand T).toSet ∩ (squareToStand p).toSet).Nonempty) :
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
          (coarseConfig.T₀.card : ℝ) * ((fineConfig Q hQ).T₀.card : ℝ) * M) :=
  inductionOnScalesBridge hnm s hs hs_one C₁ hC₁ M hM config hP_nonempty
    h_squares_unit h_tubes_strip h_tubes_bounded
    (sset_transfer_concrete hs hs_one hC₁)
    incidence_transfer
    (fun k C hC_one F h => sset_transfer_rev_concrete (hs := hs) hC_one F h)

end DiscretisedFurstenbergEstimate.Bridge
