module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceConstructionArrayW97

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody
open scoped ENNReal NNReal

namespace Kakeya.ml1Boot.TrialRestartW94

noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

universe uE uI

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

open RevisedLiteralProfileInterfaceFormalizerW87

def quotientGridIndexW97 (M a b l : Nat) : Nat := a * M + (b - a) * l

/-- Exactly the restriction identities returned by the approved A6 constructor. -/
structure VisibleExtendedRestrictionW97
    {iota : Type uI} [DecidableEq iota] {delta : NNReal}
    {A : Finset iota} {Y : iota -> ShadedTube delta E} {M : Nat} {Ccan : NNReal}
    (U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan)
    (Uext : CanonicalProfileNetW87 A (fun i => (Y i).toTube) (M * M) Ccan) : Prop where
  index : ∀ k, k <= M -> U.cover.indexSet k = Uext.cover.indexSet (k * M)
  assign : ∀ k, k <= M -> U.cover.assign k = Uext.cover.assign (k * M)
  radius : ∀ k, k <= M -> Tube.gridScale delta M k = Tube.gridScale delta (M * M) (k * M)
  tube : ∀ k, k <= M -> ∀ R, HEq (U.cover.tube k R) (Uext.cover.tube (k * M) R)

/-- C1: every quotient scale was already present before the block was chosen. -/
theorem quotient_grid_index_w97 (M a b : Nat) (hM : 1 <= M)
    (hab : a < b) (hb : b <= M) (delta : NNReal) (hd : 0 < delta) (hd1 : delta < 1) :
    quotientGridIndexW97 M a b 0 = a * M ∧
    quotientGridIndexW97 M a b M = b * M ∧
    (∀ l, l <= M -> a * M <= quotientGridIndexW97 M a b l ∧
      quotientGridIndexW97 M a b l <= b * M ∧ quotientGridIndexW97 M a b l <= M * M) ∧
    (∀ l k, l < k -> k <= M -> quotientGridIndexW97 M a b l < quotientGridIndexW97 M a b k) ∧
    (∀ l, l <= M ->
      Tube.gridScale delta (M * M) (quotientGridIndexW97 M a b l) =
        Tube.gridScale delta M a *
          (Tube.gridScale delta M b / Tube.gridScale delta M a) ^ ((l : Real) / M)) := by
  have hend : a * M + (b - a) * M = b * M := by
    rw [← Nat.add_mul, Nat.add_sub_of_le hab.le]
  refine ⟨by simp [quotientGridIndexW97], hend, ?_, ?_, ?_⟩
  · intro l hl
    have hbound : a * M + (b - a) * l <= b * M := by
      calc
        _ <= a * M + (b - a) * M := Nat.add_le_add_left (Nat.mul_le_mul_left _ hl) _
        _ = _ := hend
    exact ⟨Nat.le_add_right _ _, hbound, hbound.trans (Nat.mul_le_mul_right M hb)⟩
  · intro l k hlk hk
    exact Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_left hlk (Nat.sub_pos_of_lt hab)) _
  · intro l hl
    have hMr : (M : Real) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
    unfold Tube.gridScale quotientGridIndexW97
    rw [← NNReal.rpow_sub hd.ne', ← NNReal.rpow_mul, ← NNReal.rpow_add hd.ne']
    congr 1
    push_cast
    rw [Nat.cast_sub hab.le]
    field_simp
    <;> ring

/-- C2: quotient parents partition the full old level-b family, including inactive shades. -/
theorem extended_middle_fibres_w97
    {iota : Type uI} [DecidableEq iota] {delta : NNReal}
    {A : Finset iota} {Y : iota -> ShadedTube delta E} {M : Nat} {Ccan Ctw Ccell : NNReal}
    (U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan)
    (Uext : CanonicalProfileNetW87 A (fun i => (Y i).toTube) (M * M) Ccan)
    (restriction : VisibleExtendedRestrictionW97 U Uext)
    (reg : SourceRegularizedWorkingTowerW95 Uext Ctw Ccell)
    (hM : 1 <= M) (a b : Nat) (hab : a < b) (hb : b <= M)
    (R : iota) (hR : R ∈ U.cover.indexSet a) :
    let F := actualDescendantsW95 A U.cover.assign a b R
    let parent := fun l => Kakeya.ML2Reduction.coarseNode Uext.cover.toChain
      (quotientGridIndexW97 M a b l) (b * M)
    F.Nonempty ∧ F = actualDescendantsW95 A Uext.cover.assign (a * M) (b * M) R ∧
    (∀ l, l <= M -> F.image (parent l) =
      actualDescendantsW95 A Uext.cover.assign (a * M) (quotientGridIndexW97 M a b l) R) ∧
    (∀ l, l <= M -> ∀ S ∈ F.image (parent l),
      completeFibreW94 F (parent l) S =
        actualDescendantsW95 A Uext.cover.assign (quotientGridIndexW97 M a b l) (b * M) S) ∧
    (∀ l, l <= M -> ∀ S ∈ F.image (parent l),
      frostmanConstIn (completeFibreW94 F (parent l) S)
        (fun Q => (U.cover.tube b Q).toConvexSpaceBody)
        (Uext.cover.tube (quotientGridIndexW97 M a b l) S).toConvexSpaceBody =
      actualRelativeFrostmanW95 A Uext.cover.assign Uext.cover.tube
        (quotientGridIndexW97 M a b l) (b * M) S) ∧
    (∀ l, l < M -> ∀ S ∈ F.image (parent l),
      reg.countBand (quotientGridIndexW97 M a b l) (b * M) <=
        ((completeFibreW94 F (parent l) S).card : NNReal) ∧
      ((completeFibreW94 F (parent l) S).card : NNReal) <
        2 * reg.countBand (quotientGridIndexW97 M a b l) (b * M)) ∧
    (∀ Q ∈ F, parent M Q = Q ∧ completeFibreW94 F (parent M) Q = {Q}) := by
  let c := quotientGridIndexW97 M a b
  let F := actualDescendantsW95 A U.cover.assign a b R
  let parent := fun l => Kakeya.ML2Reduction.coarseNode Uext.cover.toChain (c l) (b * M)
  have ha : a <= M := hab.le.trans hb
  have hend : c M = b * M := by
    dsimp only [c, quotientGridIndexW97]
    rw [← Nat.add_mul, Nat.add_sub_of_le hab.le]
  have hbound : ∀ l, l <= M -> a * M <= c l ∧ c l <= b * M ∧ c l <= M * M := by
    intro l hl
    have hupper : c l <= b * M := by
      rw [← hend]
      exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hl) _
    exact ⟨Nat.le_add_right _ _, hupper, hupper.trans (Nat.mul_le_mul_right M hb)⟩
  have hstrict : ∀ l, l < M -> c l < b * M := by
    intro l hl
    rw [← hend]
    exact Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_left hl (Nat.sub_pos_of_lt hab)) _
  have hF : F = actualDescendantsW95 A Uext.cover.assign (a * M) (b * M) R := by
    dsimp only [F, actualDescendantsW95]
    rw [restriction.assign a ha, restriction.assign b hb]
  have hRext : R ∈ Uext.cover.indexSet (a * M) := restriction.index a ha ▸ hR
  have hRimage : R ∈ A.image (Uext.cover.assign (a * M)) := by
    rw [reg.surjective (a * M) (Nat.mul_le_mul_right M ha)]
    exact hRext
  have hFnonempty : F.Nonempty := by
    obtain ⟨i, hi, hiR⟩ := Finset.mem_image.mp hRimage
    rw [hF]
    exact ⟨Uext.cover.assign (b * M) i,
      Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hiR⟩, rfl⟩⟩
  have hparent : ∀ l, l <= M -> ∀ i ∈ A,
      parent l (Uext.cover.assign (b * M) i) = Uext.cover.assign (c l) i := by
    intro l hl i hi
    have hclass : (Tube.coverClass A (Uext.cover.toChain.assign (b * M))
        (Uext.cover.assign (b * M) i)).Nonempty := by
      exact ⟨i, by simp only [Tube.coverClass, Finset.mem_filter]; exact ⟨hi, rfl⟩⟩
    change Kakeya.ML2Reduction.coarseNode Uext.cover.toChain (c l) (b * M)
      (Uext.cover.assign (b * M) i) = _
    rw [Kakeya.ML2Reduction.coarseNode, dif_pos hclass]
    have hmem := hclass.choose_spec
    simp only [Tube.coverClass, Finset.mem_filter] at hmem
    exact Uext.cover.assign_eq_of_le (hbound l hl).2.1
      (Nat.mul_le_mul_right M hb) hmem.1 hi hmem.2
  have himage : ∀ l, l <= M -> F.image (parent l) =
      actualDescendantsW95 A Uext.cover.assign (a * M) (c l) R := by
    intro l hl
    ext S
    constructor
    · intro hS
      obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hS
      rw [hF] at hQ
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hQ
      obtain ⟨hiA, hiR⟩ := Finset.mem_filter.mp hi
      rw [hparent l hl i hiA]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hiA, hiR⟩, rfl⟩
    · intro hS
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hS
      obtain ⟨hiA, hiR⟩ := Finset.mem_filter.mp hi
      refine Finset.mem_image.mpr ⟨Uext.cover.assign (b * M) i, ?_, hparent l hl i hiA⟩
      rw [hF]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hiA, hiR⟩, rfl⟩
  have hfibre : ∀ l, l <= M -> ∀ S ∈ F.image (parent l),
      completeFibreW94 F (parent l) S =
        actualDescendantsW95 A Uext.cover.assign (c l) (b * M) S := by
    intro l hl S hS
    rw [himage l hl] at hS
    obtain ⟨i0, hi0, hi0S⟩ := Finset.mem_image.mp hS
    obtain ⟨hi0A, hi0R⟩ := Finset.mem_filter.mp hi0
    ext Q
    constructor
    · intro hQ
      obtain ⟨hQ, hQS⟩ := Finset.mem_filter.mp hQ
      rw [hF] at hQ
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hQ
      have hiA := (Finset.mem_filter.mp hi).1
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr
        ⟨hiA, (hparent l hl i hiA).symm.trans hQS⟩, rfl⟩
    · intro hQ
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hQ
      obtain ⟨hiA, hiS⟩ := Finset.mem_filter.mp hi
      have hiR : Uext.cover.assign (a * M) i = R :=
        (Uext.cover.assign_eq_of_le (hbound l hl).1 (hbound l hl).2.2 hiA hi0A
          (hiS.trans hi0S.symm)).trans hi0R
      refine Finset.mem_filter.mpr ⟨?_, (hparent l hl i hiA).trans hiS⟩
      rw [hF]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hiA, hiR⟩, rfl⟩
  refine ⟨hFnonempty, hF, himage, hfibre, ?_, ?_, ?_⟩
  · intro l hl S hS
    rw [hfibre l hl S hS]
    unfold actualRelativeFrostmanW95
    apply frostmanConstIn_congr
    intro Q hQ
    have hbody : ∀ {r s : NNReal} (T : Tube r E) (V : Tube s E),
        r = s -> HEq T V -> T.toConvexSpaceBody = V.toConvexSpaceBody := by
      intro r s T V hrs hTV
      subst s
      exact congrArg Tube.toConvexSpaceBody (eq_of_heq hTV)
    exact hbody _ _ (restriction.radius b hb) (restriction.tube b hb Q)
  · intro l hl S hS
    rw [hfibre l hl.le S hS]
    have hSmem : S ∈ Uext.cover.indexSet (c l) := by
      rw [himage l hl.le] at hS
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hS
      exact Uext.cover.assign_mem (c l) (hbound l hl.le).2.2 i (Finset.mem_filter.mp hi).1
    exact ⟨reg.count_lower (c l) (b * M) (hstrict l hl) (Nat.mul_le_mul_right M hb) S hSmem,
      reg.count_upper (c l) (b * M) (hstrict l hl) (Nat.mul_le_mul_right M hb) S hSmem⟩
  · have hbottom : ∀ Q ∈ F, parent M Q = Q := by
      intro Q hQ
      rw [hF] at hQ
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hQ
      rw [hparent M le_rfl i (Finset.mem_filter.mp hi).1, hend]
    intro Q hQ
    refine ⟨hbottom Q hQ, ?_⟩
    ext S
    simp only [completeFibreW94, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hS, hSQ⟩
      exact (hbottom S hS).symm.trans hSQ
    · intro hSQ
      subst S
      exact ⟨hQ, hbottom Q hQ⟩

/-- C3: interpolate the actual lower witness; the delta^(2/M) payment is visible. -/
theorem extended_trial_window_cf_lower_w97 (hdim : Module.finrank Real E = 3) :
    ∃ Cinterp : NNReal, 1 <= Cinterp ∧
      ∀ {p : Params} {beta gammaZero xiMin : Real} {xi : Fin (p.N + 1) -> Real}
        {M : Nat}, SourcePassNumericsW95 p beta gammaZero xi xiMin M ->
      ∀ {delta : NNReal}, 0 < delta -> delta < 1 ->
        4 * Tube.gridScale delta (M * M) 1 <= 1 ->
      ∀ {iota : Type uI} [DecidableEq iota]
        {A : Finset iota} {Y : iota -> ShadedTube delta E} {Ccan Ctw Ccell BF : NNReal}
        (U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan)
        (Uext : CanonicalProfileNetW87 A (fun i => (Y i).toTube) (M * M) Ccan),
        A.Nonempty -> (∀ i ∈ A, (Y i).carrier ⊆ Metric.closedBall 0 1) ->
        VisibleExtendedRestrictionW97 U Uext ->
        SourceRegularizedWorkingTowerW95 U Ctw Ccell ->
        SourceRegularizedWorkingTowerW95 Uext Ctw Ccell ->
      ∀ block : ActualSourceDividingBlockW95 U p BF,
        let d := Tube.gridScale delta M block.b.val / Tube.gridScale delta M block.a.val
        ∀ l, l <= M ->
          (d : ENNReal) ^ (1 - 3 * p.ε / 2) <= (Tube.gridScale d M l : ENNReal) ->
          (Tube.gridScale d M l : ENNReal) <= (d : ENNReal) ^ (3 * p.ε / 2) ->
          ∀ S ∈ Uext.cover.indexSet (quotientGridIndexW97 M block.a.val block.b.val l),
            (Cinterp : ENNReal)⁻¹ * (delta : ENNReal) ^ ((2 : Real) / M) *
              ((Tube.gridScale d M l : ENNReal) / (d : ENNReal)) ^ p.η (block.label.val + 1) <=
            actualRelativeFrostmanW95 A Uext.cover.assign Uext.cover.tube
              (quotientGridIndexW97 M block.a.val block.b.val l) (block.b.val * M) S := by
  obtain ⟨Ctwo, hCtwo, htwo⟩ := actual_relative_cf_composition_w97 (E := E)
  obtain ⟨Cvol, hCvol, hvol⟩ := actual_relative_cf_crude_and_prefix_w97 hdim
  let Cinterp : NNReal := 8 * Ctwo ^ (2 : Nat) * Cvol
  have hCinterp : 1 <= Cinterp := by
    dsimp only [Cinterp]
    have hsq : 1 <= Ctwo ^ (2 : Nat) := one_le_pow₀ hCtwo
    nlinarith only [hCvol, hsq]
  refine ⟨Cinterp, hCinterp, ?_⟩
  intro p beta gammaZero xiMin xi M hp delta hd hd1 hgrid iota inst A Y Ccan Ctw Ccell BF
    U Uext hA hball restriction reg regext block
  let a := block.a.val
  let b := block.b.val
  let d := Tube.gridScale delta M b / Tube.gridScale delta M a
  dsimp only
  intro l hl hlow hupp S hS
  let c := quotientGridIndexW97 M a b l
  let j := c / M
  have ha : a < b := block.a_lt_b
  have hb : b <= M := by exact Nat.le_of_lt_succ block.b.isLt
  have hM : 0 < M := hp.M_pos
  have hMr : (0 : Real) < M := by exact_mod_cast hM
  have hdpos : 0 < d := div_pos (Tube.gridScale_pos hd _ _) (Tube.gridScale_pos hd _ _)
  have hdlt : d < 1 := by
    apply (div_lt_one (Tube.gridScale_pos hd _ _)).mpr
    exact Tube.gridScale_lt_gridScale hd hd1 hM ha
  have hanti : ∀ {x : NNReal}, 0 < x -> x < 1 -> ∀ u v : Real,
      x ^ u <= x ^ v ↔ v <= u := by
    intro x hx hx1 u v
    have heq := Real.rpow_le_rpow_left_iff_of_base_lt_one
      (show (0 : Real) < x by exact_mod_cast hx) (show (x : Real) < 1 by exact_mod_cast hx1)
      (y := u) (z := v)
    exact_mod_cast heq
  have hlow' : d ^ (1 - 3 * p.ε / 2) <= d ^ ((l : Real) / M) := by
    rw [← ENNReal.coe_rpow_of_ne_zero hdpos.ne'] at hlow
    exact ENNReal.coe_le_coe.mp hlow
  have hupp' : d ^ ((l : Real) / M) <= d ^ (3 * p.ε / 2) := by
    rw [← ENNReal.coe_rpow_of_ne_zero hdpos.ne'] at hupp
    exact ENNReal.coe_le_coe.mp hupp
  have hlower := (hanti hdpos hdlt _ _).mp hupp'
  have hupper := (hanti hdpos hdlt _ _).mp hlow'
  have hdPow : d = delta ^ (((b : Real) - a) / M) := by
    dsimp only [d]
    rw [Tube.gridScale_div_gridScale hd]
    congr 1
    ring
  have hlong : p.ε <= ((b : Real) - a) / M := by
    apply (hanti hd hd1 _ _).mp
    rw [← hdPow]
    exact block.block_long
  have hba : (0 : Real) < (b : Real) - a := sub_pos.mpr (by exact_mod_cast ha)
  have hsmall : (1 : Real) / M <= p.ε ^ 2 / 2 := by
    have hz0 : p.η 0 <= p.ε / 5 := (hp.zeta_mono 0 p.N (Nat.zero_le _) le_rfl).trans hp.zeta_top
    have hz01 : p.η 0 <= 1 := by linarith only [hz0, hp.epsilon_small]
    have hmul := mul_le_mul_of_nonneg_left hz01 (sq_nonneg p.ε)
    nlinarith only [hp.M_profile, hmul, sq_nonneg p.ε]
  have hunit : 2 <= p.ε * ((b : Real) - a) := by
    have h1 := (le_div_iff₀ hMr).mp hlong
    have h2 := (div_le_iff₀ hMr).mp hsmall
    have h3 := mul_le_mul_of_nonneg_left h1 hp.epsilon_pos.le
    nlinarith only [h2, h3]
  have hcReal : (c : Real) = (a : Real) * M + ((b : Real) - a) * l := by
    dsimp only [c, quotientGridIndexW97]
    push_cast
    rw [Nat.cast_sub ha.le]
  have hjlow : (j : Real) * M <= c := by exact_mod_cast Nat.div_mul_le_self c M
  have hjupper : (c : Real) < ((j : Real) + 1) * M := by
    have hh : c < (j + 1) * M := by simpa only [Nat.mul_comm] using Nat.lt_mul_div_succ c hM
    exact_mod_cast hh
  have hjwindow : p.ε * ((b : Real) - a) <= (b : Real) - j ∧
      (b : Real) - j <= (1 - p.ε) * ((b : Real) - a) := by
    have hl1 := (le_div_iff₀ hMr).mp hlower
    have hl2 := (div_le_iff₀ hMr).mp hupper
    have hc1 := mul_le_mul_of_nonneg_left hl1 hba.le
    have hc2 := mul_le_mul_of_nonneg_left hl2 hba.le
    have hgapM := mul_le_mul_of_nonneg_right hunit hMr.le
    constructor
    · apply (mul_le_mul_iff_left₀ hMr).mp
      nlinarith only [hcReal, hjlow, hc2, hgapM]
    · apply (mul_le_mul_iff_left₀ hMr).mp
      nlinarith only [hcReal, hjupper, hc1, hgapM]
  have haj : a < j := by
    have hprod : 0 < p.ε * ((b : Real) - a) := mul_pos hp.epsilon_pos hba
    have hreal : (a : Real) < j := by nlinarith only [hjwindow.2, hprod]
    exact_mod_cast hreal
  have hjb : j < b := by
    have hprod : 0 < p.ε * ((b : Real) - a) := mul_pos hp.epsilon_pos hba
    have hreal : (j : Real) < b := by linarith only [hjwindow.1, hprod]
    exact_mod_cast hreal
  have hsourceWindow : (d : ENNReal) ^ (1 - p.ε) <=
        (Tube.gridScale delta M b : ENNReal) / Tube.gridScale delta M j ∧
      (Tube.gridScale delta M b : ENNReal) / Tube.gridScale delta M j <= (d : ENNReal) ^ p.ε := by
    have hr : Tube.gridScale delta M b / Tube.gridScale delta M j =
        delta ^ (((b : Real) - j) / M) := by
      rw [Tube.gridScale_div_gridScale hd]
      congr 1
      ring
    have hpow : ∀ t : Real, d ^ t = delta ^ ((((b : Real) - a) / M) * t) := by
      intro t
      rw [hdPow, ← NNReal.rpow_mul]
    have hleft : d ^ (1 - p.ε) <= Tube.gridScale delta M b / Tube.gridScale delta M j := by
      rw [hpow, hr]
      apply (hanti hd hd1 _ _).mpr
      calc
        _ <= ((1 - p.ε) * ((b : Real) - a)) / M := div_le_div_of_nonneg_right hjwindow.2 hMr.le
        _ = _ := by ring
    have hright : Tube.gridScale delta M b / Tube.gridScale delta M j <= d ^ p.ε := by
      rw [hpow, hr]
      apply (hanti hd hd1 _ _).mpr
      calc
        _ = (p.ε * ((b : Real) - a)) / M := by ring
        _ <= _ := div_le_div_of_nonneg_right hjwindow.1 hMr.le
    exact ⟨by
      simpa only [ENNReal.coe_rpow_of_ne_zero hdpos.ne',
        ENNReal.coe_div (Tube.gridScale_pos hd M j).ne'] using ENNReal.coe_le_coe.mpr hleft,
      by simpa only [ENNReal.coe_rpow_of_ne_zero hdpos.ne',
        ENNReal.coe_div (Tube.gridScale_pos hd M j).ne'] using ENNReal.coe_le_coe.mpr hright⟩
  have hsourceWindow' := hsourceWindow
  dsimp only [d] at hsourceWindow'
  rw [ENNReal.coe_div (Tube.gridScale_pos hd M a).ne'] at hsourceWindow'
  have hcB : c < b * M := by
    have hh : c < (j + 1) * M := by simpa only [Nat.mul_comm] using Nat.lt_mul_div_succ c hM
    exact hh.trans_le (Nat.mul_le_mul_right M (Nat.succ_le_of_lt hjb))
  have hjC : j * M <= c := Nat.div_mul_le_self c M
  have hjM : j <= M := hjb.le.trans hb
  have hbMM : b * M <= M * M := Nat.mul_le_mul_right M hb
  have hbody : ∀ {r s : NNReal} (T : Tube r E) (V : Tube s E), r = s ->
      HEq T V -> T.toConvexSpaceBody = V.toConvexSpaceBody := by
    intro r s T V hrs hTV
    subst s
    exact congrArg Tube.toConvexSpaceBody (eq_of_heq hTV)
  have hvisible : ∀ k, k <= M -> ∀ R,
      actualRelativeFrostmanW95 A U.cover.assign U.cover.tube k b R =
        actualRelativeFrostmanW95 A Uext.cover.assign Uext.cover.tube (k * M) (b * M) R := by
    intro k hk R
    unfold actualRelativeFrostmanW95 actualDescendantsW95
    rw [restriction.assign k hk, restriction.assign b hb,
      hbody _ _ (restriction.radius k hk) (restriction.tube k hk R)]
    apply frostmanConstIn_congr
    intro Q hQ
    exact hbody _ _ (restriction.radius b hb) (restriction.tube b hb Q)
  have hquotient : Tube.gridScale delta (M * M) c =
      Tube.gridScale delta M a * Tube.gridScale d M l :=
    (quotient_grid_index_w97 M a b hp.M_pos ha hb delta hd hd1).2.2.2.2 l hl
  have hratio : (Tube.gridScale d M l : ENNReal) / (d : ENNReal) =
      (Tube.gridScale delta (M * M) c : ENNReal) / Tube.gridScale delta M b := by
    have heq : Tube.gridScale d M l / d =
        Tube.gridScale delta (M * M) c / Tube.gridScale delta M b := by
      rw [hquotient]
      dsimp only [d]
      field_simp
    simpa only [ENNReal.coe_div hdpos.ne',
      ENNReal.coe_div (Tube.gridScale_pos hd M b).ne'] using congrArg (fun x : NNReal => (x : ENNReal)) heq
  have hradJC : Tube.gridScale delta (M * M) c <= Tube.gridScale delta M j := by
    rw [restriction.radius j hjM]
    exact Tube.gridScale_antitone hd hd1.le _ hjC
  have hz : 0 < p.η (block.label.val + 1) := hp.zeta_pos _ (Nat.succ_le_of_lt block.label_active)
  have hpowJC : ((Tube.gridScale d M l : ENNReal) / (d : ENNReal)) ^ p.η (block.label.val + 1) <=
      ((Tube.gridScale delta M j : ENNReal) / Tube.gridScale delta M b) ^ p.η (block.label.val + 1) := by
    rw [hratio]
    apply ENNReal.rpow_le_rpow _ hz.le
    exact ENNReal.div_le_div_right (ENNReal.coe_le_coe.mpr hradJC) _
  let P : ENNReal := ((Tube.gridScale d M l : ENNReal) / (d : ENNReal)) ^ p.η (block.label.val + 1)
  let X : ENNReal := actualRelativeFrostmanW95 A Uext.cover.assign Uext.cover.tube c (b * M) S
  have hpowFin : (delta : ENNReal) ^ (-(2 : Real) / M) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_ne_zero (ENNReal.coe_pos.mpr hd).ne' ENNReal.coe_ne_top
  have hlarge : (1 : ENNReal) <= (delta : ENNReal) ^ (-(2 : Real) / M) := by
    simpa only [ENNReal.rpow_zero] using ENNReal.rpow_le_rpow_of_exponent_ge
      (show (delta : ENNReal) <= 1 by exact_mod_cast hd1.le)
      (show -(2 : Real) / M <= 0 from div_nonpos_of_nonpos_of_nonneg (by norm_num) hMr.le)
  have hbound : P <= (Cinterp : ENNReal) * (delta : ENNReal) ^ (-(2 : Real) / M) * X := by
    by_cases hsame : j * M = c
    · have hSvis : S ∈ U.cover.indexSet j := by
        rw [restriction.index j hjM, hsame]
        exact hS
      have hsource := block.intermediate_lower j haj hjb hsourceWindow'.1 hsourceWindow'.2 S hSvis
      change (1 / 2 : ENNReal) * ((Tube.gridScale delta M j : ENNReal) /
        Tube.gridScale delta M b) ^ p.η (block.label.val + 1) <
          actualRelativeFrostmanW95 A U.cover.assign U.cover.tube j b S at hsource
      have hhalf : (1 / 2 : ENNReal) * P < X := by
        apply lt_of_le_of_lt (mul_le_mul_left' hpowJC _) _
        simpa only [hvisible j hjM S, hsame, X] using hsource
      have hdouble : P <= 2 * X := by
        have h := ENNReal.mul_lt_mul_right (a := (2 : ENNReal)) (by norm_num) (by finiteness) hhalf
        rw [← mul_assoc, one_div, ENNReal.mul_inv_cancel (by norm_num : (2 : ENNReal) ≠ 0)
          (by finiteness), one_mul] at h
        exact h.le
      have hcoef : (2 : ENNReal) <= (Cinterp : ENNReal) := by
        have hh : (2 : NNReal) <= Cinterp := by
          dsimp only [Cinterp]
          have hsq : 1 <= Ctwo ^ (2 : Nat) := one_le_pow₀ hCtwo
          nlinarith only [hCvol, hsq]
        exact_mod_cast hh
      exact hdouble.trans (mul_le_mul_right' (hcoef.trans
        (le_mul_of_one_le_right bot_le hlarge)) X)
    · have hjClt : j * M < c := lt_of_le_of_ne hjC hsame
      have hgridRatio : Tube.gridScale delta (M * M) (b * M) /
          Tube.gridScale delta (M * M) c <= Tube.gridScale delta (M * M) 1 := by
        rw [Tube.gridScale_div_gridScale hd]
        unfold Tube.gridScale
        apply (hanti hd hd1 _ _).mpr
        have hcast : (c : Real) + 1 <= (b * M : Nat) := by exact_mod_cast hcB
        have hmm : (0 : Real) < (M * M : Nat) := by exact_mod_cast Nat.mul_pos hM hM
        rw [← neg_div]
        apply (div_le_div_iff_of_pos_right hmm).mpr
        norm_num only [Nat.cast_one]
        linarith only [hcast]
      have hgap : 4 * Tube.gridScale delta (M * M) (b * M) <=
          Tube.gridScale delta (M * M) c := by
        have hmul := mul_le_mul_of_nonneg_left hgridRatio (show (0 : NNReal) <= 4 by norm_num)
        have hpay := hmul.trans hgrid
        rw [← mul_div_assoc] at hpay
        exact (div_le_one (Tube.gridScale_pos hd _ _)).mp hpay
      have hcrudeRatio : Tube.gridScale delta (M * M) (j * M) /
          Tube.gridScale delta (M * M) c <= delta ^ (-(1 : Real) / M) := by
        rw [Tube.gridScale_div_gridScale hd]
        apply (hanti hd hd1 _ _).mpr
        push_cast
        rw [← neg_div]
        apply (le_div_iff₀ (mul_pos hMr hMr)).mpr
        calc
          _ = -(M : Real) := by field_simp
          _ <= _ := by nlinarith only [hjupper]
      have hcrudePow : ((Tube.gridScale delta (M * M) (j * M) : ENNReal) /
          Tube.gridScale delta (M * M) c) ^ (2 : Nat) <= (delta : ENNReal) ^ (-(2 : Real) / M) := by
        have hpow := pow_le_pow_left₀ bot_le hcrudeRatio 2
        have hid : (delta ^ (-(1 : Real) / M)) ^ (2 : Nat) = delta ^ (-(2 : Real) / M) := by
          rw [← NNReal.rpow_natCast, ← NNReal.rpow_mul]
          congr 1
          ring
        rw [hid] at hpow
        simpa only [ENNReal.coe_pow, ENNReal.coe_div (Tube.gridScale_pos hd (M * M) c).ne',
          ENNReal.coe_rpow_of_ne_zero hd.ne'] using ENNReal.coe_le_coe.mpr hpow
      have hcrude : actualRelativeCFArrayW97 Uext (j * M) c <=
          (Cvol : ENNReal) * (delta : ENNReal) ^ (-(2 : Real) / M) := by
        apply Finset.sup_le
        intro Q hQ
        exact ((hvol hd hd1.le Uext hA regext).1 (j * M) c hjClt (hcB.le.trans hbMM) Q hQ).trans
          (mul_le_mul_left' hcrudePow _)
      have htarget : actualRelativeCFArrayW97 Uext c (b * M) <= 2 * X := by
        apply Finset.sup_le
        intro Q hQ
        exact (regext.frostman_upper c (b * M) hcB hbMM Q hQ).le.trans
          (mul_le_mul_left' (regext.frostman_lower c (b * M) hcB hbMM S hS) 2)
      let i := hA.choose
      have hi := hA.choose_spec
      let R := U.cover.assign j i
      have hR : R ∈ U.cover.indexSet j := U.cover.assign_mem j hjM i hi
      have hsource := block.intermediate_lower j haj hjb hsourceWindow'.1 hsourceWindow'.2 R hR
      have hRext : R ∈ Uext.cover.indexSet (j * M) := restriction.index j hjM ▸ hR
      have hcomposition := (htwo hd hd1.le Uext hA regext hball (j * M) c (b * M)
        hjClt hcB hbMM hgap).1 R hRext
      have hhalf : (1 / 2 : ENNReal) * P <
          4 * (Ctwo : ENNReal) ^ (2 : Nat) * Cvol * (delta : ENNReal) ^ (-(2 : Real) / M) * X := by
        calc
          _ <= (1 / 2 : ENNReal) * ((Tube.gridScale delta M j : ENNReal) /
              Tube.gridScale delta M b) ^ p.η (block.label.val + 1) := mul_le_mul_left' hpowJC _
          _ < actualRelativeFrostmanW95 A U.cover.assign U.cover.tube j b R := hsource
          _ = _ := hvisible j hjM R
          _ <= _ := hcomposition
          _ <= 2 * (Ctwo : ENNReal) ^ (2 : Nat) *
              ((Cvol : ENNReal) * (delta : ENNReal) ^ (-(2 : Real) / M)) * (2 * X) := by
            gcongr
          _ = _ := by ring
      have h := ENNReal.mul_lt_mul_right (a := (2 : ENNReal)) (by norm_num) (by finiteness) hhalf
      rw [← mul_assoc, one_div, ENNReal.mul_inv_cancel (by norm_num : (2 : ENNReal) ≠ 0)
        (by finiteness), one_mul] at h
      apply h.le.trans_eq
      dsimp only [Cinterp]
      push_cast
      ring
  have hcoeffFin : (Cinterp : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hcoeffPos : (Cinterp : ENNReal) ≠ 0 := (ENNReal.coe_pos.mpr (zero_lt_one.trans_le hCinterp)).ne'
  have hdE : (delta : ENNReal) ≠ 0 := (ENNReal.coe_pos.mpr hd).ne'
  have hfinal := mul_le_mul_left' hbound ((Cinterp : ENNReal)⁻¹ * (delta : ENNReal) ^ ((2 : Real) / M))
  have hcancel : (Cinterp : ENNReal)⁻¹ * (delta : ENNReal) ^ ((2 : Real) / M) *
      ((Cinterp : ENNReal) * (delta : ENNReal) ^ (-(2 : Real) / M) * X) = X := by
    calc
      _ = ((Cinterp : ENNReal)⁻¹ * Cinterp) *
          ((delta : ENNReal) ^ ((2 : Real) / M) * (delta : ENNReal) ^ (-(2 : Real) / M)) * X := by ring
      _ = X := by
        rw [ENNReal.inv_mul_cancel hcoeffPos hcoeffFin,
          ← ENNReal.rpow_add _ _ hdE ENNReal.coe_ne_top]
        rw [show (2 : Real) / M + -(2 : Real) / M = 0 by ring]
        simp only [ENNReal.rpow_zero, one_mul]
  rw [hcancel] at hfinal
  exact hfinal

/-- Fixed constants and the interpolation loss are paid by the half-exponent margin. -/
theorem exists_quotient_half_eta_payment_w97
    {p : Params} {beta gammaZero xiMin : Real} {xi : Fin (p.N + 1) -> Real}
    {M : Nat} (hp : SourcePassNumericsW95 p beta gammaZero xi xiMin M)
    (C : NNReal) (hC : 1 <= C) :
    ∃ delta0 : NNReal, 0 < delta0 ∧ delta0 < 1 ∧
      ∀ {delta d r : NNReal}, 0 < delta -> delta < delta0 ->
        delta <= d -> d <= delta ^ p.ε ->
        (d : ENNReal) ^ (1 - 3 * p.ε / 2) <= (r : ENNReal) ->
        (r : ENNReal) <= (d : ENNReal) ^ (3 * p.ε / 2) ->
        ∀ m : Fin (p.N + 1), m.val < p.N ->
          (1 / 2 : ENNReal) * ((r : ENNReal) / (d : ENNReal)) ^ (p.η (m.val + 1) / 2) <
            (C : ENNReal)⁻¹ * (delta : ENNReal) ^ ((2 : Real) / M) *
              ((r : ENNReal) / (d : ENNReal)) ^ p.η (m.val + 1) ∧
          (C : ENNReal) * (d : ENNReal) ^ (-p.η m.val) <=
            (d : ENNReal) ^ (-xi m / 160) := by
  let e := p.ε ^ 2 * p.η 0 / 2
  let eCF := p.ε * xiMin / 800
  have hz0 : 0 < p.η 0 := hp.zeta_pos 0 (Nat.zero_le _)
  have he : 0 < e := div_pos (mul_pos (sq_pos_of_pos hp.epsilon_pos) hz0) (by norm_num)
  have heCF : 0 < eCF := div_pos (mul_pos hp.epsilon_pos hp.xiMin_pos) (by norm_num)
  have hcut : ∀ᶠ delta : NNReal in nhdsWithin 0 (Set.Ioi 0),
      delta < 1 ∧ (C : ENNReal) <= (delta : ENNReal) ^ (-e) ∧
        (C : ENNReal) <= (delta : ENNReal) ^ (-eCF) := by
    filter_upwards [eventually_le_nhdsGT (c := (1 / 2 : NNReal)) (by norm_num),
      eventually_finite_const_le_rpow_neg (c := (C : ENNReal)) ENNReal.coe_ne_top he,
      eventually_finite_const_le_rpow_neg (c := (C : ENNReal)) ENNReal.coe_ne_top heCF]
      with delta hd1 hpay hpayCF
    exact ⟨hd1.trans_lt (by norm_num), hpay, hpayCF⟩
  obtain ⟨cutoff, hcutoff, hcutoffAt⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hcut
  let delta0 : NNReal := min cutoff (1 / 2)
  refine ⟨delta0, lt_min hcutoff (by norm_num), (min_le_right _ _).trans_lt (by norm_num), ?_⟩
  intro delta d r hd hd0 hdd hdup hrlow hrup m hm
  obtain ⟨hd1, hpayE, hpayCFE⟩ := hcutoffAt ⟨hd, hd0.trans_le (min_le_left _ _)⟩
  have hdpos : 0 < d := hd.trans_le hdd
  have hdsmall : d < 1 := by
    apply hdup.trans_lt
    simpa only [NNReal.one_rpow] using NNReal.rpow_lt_rpow hd1 hp.epsilon_pos
  have hrlo : d ^ (1 - 3 * p.ε / 2) <= r := by
    rw [← ENNReal.coe_rpow_of_ne_zero hdpos.ne'] at hrlow
    exact ENNReal.coe_le_coe.mp hrlow
  have hrpos : 0 < r := (NNReal.rpow_pos hdpos).trans_le hrlo
  have hratio : 0 < r / d := div_pos hrpos hdpos
  have hpay : C <= delta ^ (-e) := by
    rw [← ENNReal.coe_rpow_of_ne_zero hd.ne'] at hpayE
    exact ENNReal.coe_le_coe.mp hpayE
  have hpayCF : C <= delta ^ (-eCF) := by
    rw [← ENNReal.coe_rpow_of_ne_zero hd.ne'] at hpayCFE
    exact ENNReal.coe_le_coe.mp hpayCFE
  have hz : 0 < p.η (m.val + 1) := hp.zeta_pos _ (by omega)
  have hzmono : p.η 0 <= p.η (m.val + 1) := hp.zeta_mono _ _ (Nat.zero_le _) (by omega)
  have hmargin : (2 : Real) / M - 3 * p.ε ^ 2 * p.η (m.val + 1) / 4 <= -e := by
    have hmono := mul_le_mul_of_nonneg_left hzmono (sq_nonneg p.ε)
    dsimp only [e]
    rw [show (2 : Real) / M = 2 * (1 / M) by ring]
    nlinarith only [hp.M_profile, hmono, mul_pos (sq_pos_of_pos hp.epsilon_pos) hz0]
  have hratioLow : d ^ (-3 * p.ε / 2) <= r / d := by
    calc
      _ = d ^ (1 - 3 * p.ε / 2) / d := by
        rw [← NNReal.rpow_sub_one hdpos.ne']
        congr 1
        ring
      _ <= _ := div_le_div_of_nonneg_right hrlo hdpos.le
  have hhalfLow : delta ^ (-3 * p.ε ^ 2 * p.η (m.val + 1) / 4) <=
      (r / d) ^ (p.η (m.val + 1) / 2) := by
    calc
      _ = (delta ^ p.ε) ^ (-3 * p.ε * p.η (m.val + 1) / 4) := by
        rw [← NNReal.rpow_mul]
        congr 1
        ring
      _ <= d ^ (-3 * p.ε * p.η (m.val + 1) / 4) :=
        NNReal.rpow_le_rpow_of_nonpos hdpos hdup (by nlinarith only [mul_pos hp.epsilon_pos hz])
      _ = (d ^ (-3 * p.ε / 2)) ^ (p.η (m.val + 1) / 2) := by
        rw [← NNReal.rpow_mul]
        congr 1
        ring
      _ <= _ := NNReal.rpow_le_rpow hratioLow (half_pos hz).le
  have hpaidHalf : C <= delta ^ ((2 : Real) / M) * (r / d) ^ (p.η (m.val + 1) / 2) := by
    calc
      C <= delta ^ (-e) := hpay
      _ <= delta ^ ((2 : Real) / M - 3 * p.ε ^ 2 * p.η (m.val + 1) / 4) :=
        NNReal.rpow_le_rpow_of_exponent_ge hd hd1.le hmargin
      _ = delta ^ ((2 : Real) / M) * delta ^ (-3 * p.ε ^ 2 * p.η (m.val + 1) / 4) := by
        rw [sub_eq_add_neg, NNReal.rpow_add hd.ne']
        congr 2
        ring
      _ <= _ := mul_le_mul_of_nonneg_left hhalfLow bot_le
  have hCpos : 0 < C := (by norm_num : (0 : NNReal) < 1).trans_le hC
  have hfirst : (1 / 2 : NNReal) * (r / d) ^ (p.η (m.val + 1) / 2) <
      C⁻¹ * delta ^ ((2 : Real) / M) * (r / d) ^ p.η (m.val + 1) := by
    have hx := NNReal.rpow_pos hratio (p := p.η (m.val + 1) / 2)
    have hxpow : (r / d) ^ p.η (m.val + 1) =
        (r / d) ^ (p.η (m.val + 1) / 2) * (r / d) ^ (p.η (m.val + 1) / 2) := by
      rw [← NNReal.rpow_add hratio.ne']
      congr 1
      ring
    have hunit : (1 : NNReal) <= C⁻¹ * delta ^ ((2 : Real) / M) *
        (r / d) ^ (p.η (m.val + 1) / 2) := by
      calc
        1 = C⁻¹ * C := (inv_mul_cancel₀ hCpos.ne').symm
        _ <= C⁻¹ * (delta ^ ((2 : Real) / M) * (r / d) ^ (p.η (m.val + 1) / 2)) :=
          mul_le_mul_of_nonneg_left hpaidHalf bot_le
        _ = _ := by ring
    calc
      _ < (1 : NNReal) * (r / d) ^ (p.η (m.val + 1) / 2) :=
        mul_lt_mul_of_pos_right (by norm_num) hx
      _ <= (C⁻¹ * delta ^ ((2 : Real) / M) * (r / d) ^ (p.η (m.val + 1) / 2)) *
          (r / d) ^ (p.η (m.val + 1) / 2) := mul_le_mul_of_nonneg_right hunit bot_le
      _ = _ := by rw [hxpow]; ring
  have hCFconst : C <= d ^ (-(xi m / 160 - p.η m.val)) := by
    have hgap : xiMin / 800 <= xi m / 160 - p.η m.val := by
      linarith only [hp.rung_xi m hm, hp.xiMin_lower m hm]
    calc
      C <= delta ^ (-eCF) := hpayCF
      _ = (delta ^ p.ε) ^ (-xiMin / 800) := by
        rw [← NNReal.rpow_mul]
        congr 1
        dsimp only [eCF]
        ring
      _ <= d ^ (-xiMin / 800) := NNReal.rpow_le_rpow_of_nonpos hdpos hdup (by linarith only [hp.xiMin_pos])
      _ <= _ := NNReal.rpow_le_rpow_of_exponent_ge hdpos hdsmall.le (by linarith only [hgap])
  have hsecond : C * d ^ (-p.η m.val) <= d ^ (-xi m / 160) := by
    calc
      _ <= d ^ (-(xi m / 160 - p.η m.val)) * d ^ (-p.η m.val) :=
        mul_le_mul_of_nonneg_right hCFconst bot_le
      _ = _ := by
        rw [← NNReal.rpow_add hdpos.ne']
        congr 1
        ring
  constructor
  · simpa only [ENNReal.coe_mul, ENNReal.coe_div hdpos.ne', ENNReal.coe_div (by norm_num : (2 : NNReal) ≠ 0),
      ENNReal.coe_one, ENNReal.coe_ofNat, ENNReal.coe_inv hCpos.ne',
      ENNReal.coe_rpow_of_ne_zero hd.ne', ENNReal.coe_rpow_of_ne_zero hratio.ne']
      using (ENNReal.coe_lt_coe.mpr hfirst)
  · simpa only [ENNReal.coe_mul, ENNReal.coe_rpow_of_ne_zero hdpos.ne'] using
      (ENNReal.coe_le_coe.mpr hsecond)

/-- The auxiliary schedule is distinct from the immutable full-eta schedule. -/
structure AuxiliaryHalfEtaThresholdsW97 (p : Params)
    (xi : Fin (p.N + 1) -> Real) (gamma : Real) (Ctw Ccell : NNReal) (M : Nat) where
  inner : Fin (p.N + 1) -> Real
  cutoff : Fin (p.N + 1) -> NNReal
  Ktr : Fin (p.N + 1) -> Nat
  inner_pos : ∀ m, 0 < inner m
  cutoff_pos : ∀ m, 0 < cutoff m
  cutoff_lt_one : ∀ m, cutoff m < 1
  Ktr_pos : ∀ m, 1 <= Ktr m
  actual_trial : ∀ m, m.val < p.N ->
    detailedTrialAtThresholdW94.{uE, uI} (E := E) gamma p.ε (xi m) (p.η (m.val + 1) / 2)
      Ctw Ccell M (inner m) (cutoff m) (Ktr m)

/-- C5 invokes the named generic P1 dependency at half eta; neither schedule is supplied. -/
theorem exists_auxiliary_half_eta_trial_thresholds_w97
    (hdim : Module.finrank Real E = 3)
    {p : Params} {beta gammaZero xiMin : Real} {xi : Fin (p.N + 1) -> Real}
    {M : Nat} (hp : SourcePassNumericsW95 p beta gammaZero xi xiMin M)
    (gamma : Real) (hgammaZero : gammaZero <= gamma) (hgamma : gamma <= 1)
    (Ctw Ccell : NNReal) (hCtw : 1 <= Ctw) (hCcell : 1 <= Ccell)
    (hKT : KatzTaoEstimate.{uI} E beta) (hKF : FrostmanEstimate.{uI} E gamma) :
    ∃ (full : LabelledDetailedTrialThresholdsW94.{uE, uI} (E := E) p xi gamma Ctw Ccell M)
      (aux : AuxiliaryHalfEtaThresholdsW97.{uE, uI} (E := E) p xi gamma Ctw Ccell M)
      (eFull : Real) (delta0 : NNReal) (Kmax : Nat),
      0 < eFull ∧ 0 < delta0 ∧ delta0 < 1 ∧ 1 <= Kmax ∧
      (∀ m : Fin (p.N + 1), m.val < p.N ->
        eFull < p.ε * min (full.inner m) (aux.inner m) / 10 ∧
        delta0 ^ p.ε <= min (full.cutoff m) (aux.cutoff m) ∧
        full.Ktr m <= Kmax ∧ aux.Ktr m <= Kmax) := by
  have hbetagamma : beta < gamma := hp.gammaZero_gt.trans_le hgammaZero
  have hgap : 3 * p.ε / 2 <= (gamma - beta) / 1000 := by
    linarith only [hp.gap, hgammaZero]
  have heps32 : 32 * p.ε <= 1 := by
    linarith only [hp.gap, hp.gammaZero_le, hp.beta_pos]
  have heps1 : p.ε <= 1 := hp.epsilon_small.le.trans (by norm_num)
  have hMpos : (0 : Real) < M := by exact_mod_cast hp.M_pos
  have hdenom : 0 < p.ε ^ 2 * beta := mul_pos (sq_pos_of_pos hp.epsilon_pos) hp.beta_pos
  have hnext : ∀ m : Fin (p.N + 1), m.val < p.N ->
      4000 * xi m / (p.ε ^ 2 * beta) <= p.η (m.val + 1) / 2 := by
    intro m hm
    apply (div_le_iff₀ hdenom).mpr
    nlinarith only [hp.xi_next m hm]
  have hMmin : ∀ m : Fin (p.N + 1), m.val < p.N ->
      (1 : Real) / M <= min (xi m) p.ε / 100 := by
    intro m hm
    have hxiMin1 : xiMin <= 1 := by
      obtain ⟨k, hk, hkMin⟩ := hp.xiMin_attained
      have hbeta1 : beta <= 1 := hp.gammaZero_gt.le.trans hp.gammaZero_le
      have heps3 : p.ε ^ 3 <= 1 := pow_le_one₀ hp.epsilon_pos.le heps1
      have hprod : p.ε ^ 3 * beta <= 1 := mul_le_one₀ heps3 hp.beta_pos.le hbeta1
      rw [← hkMin]
      nlinarith only [hp.xi_beta k hk, hprod]
    have hleft : p.ε * xiMin / 200 <= xi m / 100 := by
      have hprod : p.ε * xiMin <= xiMin := mul_le_of_le_one_left hp.xiMin_pos.le heps1
      linarith only [hprod, hp.xiMin_lower m hm, hp.xi_pos m hm]
    have hright : p.ε * xiMin / 200 <= p.ε / 100 := by
      have hprod : p.ε * xiMin <= p.ε := mul_le_of_le_one_right hp.epsilon_pos.le hxiMin1
      linarith only [hprod, hp.epsilon_pos]
    rw [← min_div_div_right (by norm_num : (0 : Real) <= 100)]
    exact le_min (hp.M_xi.trans hleft) (hp.M_xi.trans hright)
  have hMhalf : ∀ m : Fin (p.N + 1), m.val < p.N ->
      (160000 : Real) / (p.ε * (p.η (m.val + 1) / 2)) <= M := by
    intro m hm
    have hz : 0 < p.η (m.val + 1) := hp.zeta_pos _ (by omega)
    have hzero : p.η 0 <= p.ε * p.η (m.val + 1) / 100 :=
      (hp.zeta_mono 0 m.val (Nat.zero_le _) (by omega)).trans (hp.rung_next m.val hm)
    have hmul := mul_le_mul_of_nonneg_left hzero hp.epsilon_pos.le
    have hmargin := mul_le_mul_of_nonneg_right heps32 (mul_nonneg hp.epsilon_pos.le hz.le)
    have hsmall : (1 : Real) / M <= p.ε * p.η (m.val + 1) / 320000 := by
      nlinarith only [hp.M_zeta, hmul, hmargin]
    apply (div_le_iff₀ (mul_pos hp.epsilon_pos (half_pos hz))).mpr
    have hsmall' := (div_le_iff₀ hMpos).mp hsmall
    nlinarith only [hsmall']
  obtain ⟨full⟩ := exists_labelled_detailed_trial_thresholds_w94 hdim p beta gamma xi
    hp.beta_pos hbetagamma hgamma hp.epsilon_pos hp.epsilon_small hgap
    (fun m hm => ⟨hp.xi_pos m hm, hp.xi_beta m hm⟩)
    (fun m hm => (hnext m hm).trans (by linarith only [hp.zeta_pos (m.val + 1) (by omega)]))
    Ctw Ccell hCtw hCcell M hp.M_pos hMmin
    (fun m hm => by
      have hz : 0 < p.η (m.val + 1) := hp.zeta_pos _ (by omega)
      apply le_trans _ (hMhalf m hm)
      exact div_le_div_of_nonneg_left (by norm_num)
        (mul_pos hp.epsilon_pos (half_pos hz)) (by nlinarith only [mul_pos hp.epsilon_pos hz]))
    hKT hKF
  have hlabel : ∀ m : Fin (p.N + 1), ∃ (inner : Real) (cutoff : NNReal) (Ktr : Nat),
      0 < inner ∧ 0 < cutoff ∧ cutoff < 1 ∧ 1 <= Ktr ∧
      (m.val < p.N -> detailedTrialAtThresholdW94.{uE, uI} (E := E)
        gamma p.ε (xi m) (p.η (m.val + 1) / 2) Ctw Ccell M inner cutoff Ktr) := by
    intro m
    by_cases hm : m.val < p.N
    · obtain ⟨inner, cutoff, Ktr, hinner, hcutoff, hcutoff1, hKtr, htrial⟩ :=
        exists_literal_detailed_trial_threshold_w94 hdim beta gamma p.ε (xi m)
          (p.η (m.val + 1) / 2) hp.beta_pos hbetagamma hgamma hp.epsilon_pos
          hp.epsilon_small hgap (hp.xi_pos m hm) (hp.xi_beta m hm) (hnext m hm)
          Ctw Ccell hCtw hCcell M hp.M_pos (hMmin m hm) (hMhalf m hm) hKT hKF
      exact ⟨inner, cutoff, Ktr, hinner, hcutoff, hcutoff1, hKtr, fun _ => htrial⟩
    · exact ⟨1, 1 / 2, 1, by norm_num, by norm_num, by norm_num, le_rfl,
        fun hm' => (hm hm').elim⟩
  choose inner cutoff Ktr hinner hcutoff hcutoff1 hKtr htrial using hlabel
  let aux : AuxiliaryHalfEtaThresholdsW97.{uE, uI} (E := E) p xi gamma Ctw Ccell M :=
    { inner := inner, cutoff := cutoff, Ktr := Ktr, inner_pos := hinner,
      cutoff_pos := hcutoff, cutoff_lt_one := hcutoff1, Ktr_pos := hKtr,
      actual_trial := htrial }
  let e : Fin (p.N + 1) -> Real := fun m => p.ε * min (full.inner m) (aux.inner m) / 20
  obtain ⟨mE, hmE, hminE⟩ := Finset.exists_min_image Finset.univ e Finset.univ_nonempty
  let cut : Fin (p.N + 1) -> NNReal := fun m => min (full.cutoff m) (aux.cutoff m)
  obtain ⟨mD, hmD, hminD⟩ := Finset.exists_min_image Finset.univ cut Finset.univ_nonempty
  let degrees : Fin (p.N + 1) -> Nat := fun m => max (full.Ktr m) (aux.Ktr m)
  obtain ⟨mK, hmK, hmaxK⟩ := Finset.exists_max_image Finset.univ degrees Finset.univ_nonempty
  let delta0 : NNReal := min (1 / 2) (cut mD ^ p.ε⁻¹)
  have hcut : 0 < cut mD := lt_min (full.cutoff_pos mD) (aux.cutoff_pos mD)
  have he : ∀ m, 0 < e m := fun m =>
    div_pos (mul_pos hp.epsilon_pos (lt_min (full.inner_pos m) (aux.inner_pos m))) (by norm_num)
  refine ⟨full, aux, e mE, delta0, degrees mK, he mE, ?_, ?_, ?_, ?_⟩
  · exact lt_min (by norm_num) (NNReal.rpow_pos hcut)
  · exact (min_le_left _ _).trans_lt (by norm_num)
  · exact (full.Ktr_pos mK).trans (le_max_left _ _)
  · intro m hm
    refine ⟨?_, ?_, (le_max_left _ _).trans (hmaxK m (Finset.mem_univ m)),
      (le_max_right _ _).trans (hmaxK m (Finset.mem_univ m))⟩
    · have hmpos := he m
      have hmle := hminE m (Finset.mem_univ m)
      dsimp only [e] at hmpos hmle ⊢
      linarith only [hmpos, hmle]
    · apply le_trans _ (hminD m (Finset.mem_univ m))
      exact (NNReal.le_rpow_inv_iff hp.epsilon_pos).mp (min_le_right _ _)

end

end Kakeya.ml1Boot.TrialRestartW94
