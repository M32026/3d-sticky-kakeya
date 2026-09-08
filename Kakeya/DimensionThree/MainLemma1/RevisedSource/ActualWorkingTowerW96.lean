module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceConstructionDefinitionsW97
public import Kakeya.DimensionThree.MainLemma1.Factoring
public import Kakeya.DimensionThree.MainLemma2.CanonicalCentredCover
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.RawTreeClosenessW96

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody
open scoped ENNReal NNReal

namespace Kakeya.ml1Boot.TrialRestartW94

noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

universe uE uI

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]

open RevisedLiteralProfileInterfaceFormalizerW87









/-- P2 primitive: construct a heaviest realized count/relative-CF bin and
retain whole actual parent fibres. No bin labels or universal encoder are
supplied. Every retained complete fibre keeps its actual old observables. -/
theorem exists_actual_count_relative_frostman_band_w95
    {iota : Type uI} [DecidableEq iota] {delta : NNReal}
    (F : Finset iota) (Y : iota -> ShadedTube delta E)
    (assign : Nat -> iota -> iota) {rho : Nat -> NNReal}
    (tube : (l : Nat) -> iota -> Tube (rho l) E)
    (k l : Nat) (H : ENNReal) (hH : 1 <= H) (hH_finite : H < ⊤)
    (hcount_pos : ∀ R ∈ F.image (assign k),
      1 <= (actualDescendantsW95 F assign k l R).card)
    (hcount_upper : ∀ R ∈ F.image (assign k),
      ((actualDescendantsW95 F assign k l R).card : ENNReal) <= H)
    (hfrostman_lower : ∀ R ∈ F.image (assign k),
      1 <= actualRelativeFrostmanW95 F assign tube k l R)
    (hfrostman_upper : ∀ R ∈ F.image (assign k),
      actualRelativeFrostmanW95 F assign tube k l R <= H)
    (hmass_pos : 0 < ∑ i ∈ F, volume (Y i).shade)
    (hmass_finite : (∑ i ∈ F, volume (Y i).shade) < ⊤) :
    ∃ (a b : Nat) (A kept : Finset iota),
      a < dyadicRangeLengthW95 H ∧ b < dyadicRangeLengthW95 H ∧
      kept = actualBandParentsW95 F assign tube k l a b ∧
      A = F.filter (fun i => assign k i ∈ kept) ∧
      kept.Nonempty ∧ A.Nonempty ∧ A ⊆ F ∧ A.image (assign k) = kept ∧
      (∀ R ∈ kept, completeFibreW94 A (assign k) R = completeFibreW94 F (assign k) R) ∧
      (∀ R ∈ kept, actualDescendantsW95 A assign k l R =
        actualDescendantsW95 F assign k l R) ∧
      (∀ R ∈ kept, actualRelativeFrostmanW95 A assign tube k l R =
        actualRelativeFrostmanW95 F assign tube k l R) ∧
      (((dyadicRangeLengthW95 H : Nat) : ENNReal) ^ (2 : Nat))⁻¹ *
          (∑ i ∈ F, volume (Y i).shade) <=
        ∑ i ∈ A, volume (Y i).shade := by
  let N := dyadicRangeLengthW95 H
  have hN : 0 < N := by dsimp [N, dyadicRangeLengthW95]; omega
  have hbin : ∀ x : ENNReal, 1 ≤ x → x ≤ H →
      ∃ a : Fin N, (2 : ENNReal) ^ a.val ≤ x ∧ x < (2 : ENNReal) ^ (a.val + 1) := by
    intro x hx1 hxH
    have hxTop : x ≠ ⊤ := (hxH.trans_lt hH_finite).ne
    have hxR1 : 1 ≤ x.toReal := by
      simpa using (ENNReal.toReal_le_toReal (by norm_num) hxTop).mpr hx1
    have hxR0 : 0 < x.toReal := lt_of_lt_of_le (by norm_num) hxR1
    have hxRH : x.toReal ≤ H.toReal :=
      ENNReal.toReal_mono hH_finite.ne hxH
    let a := Nat.floor (Real.logb 2 x.toReal)
    have haN : a < N := by
      have hlog := Real.logb_le_logb_of_le (by norm_num : (1 : Real) < 2) hxR0 hxRH
      have hfloor := Nat.floor_mono hlog
      simpa only [a, N, dyadicRangeLengthW95, Real.logb] using Nat.lt_succ_of_le hfloor
    have hlo : (2 : Real) ^ a ≤ x.toReal := by
      rw [← Real.rpow_natCast]
      exact (Real.le_logb_iff_rpow_le (by norm_num) hxR0).mp
        (Nat.floor_le (Real.logb_nonneg (by norm_num) hxR1))
    have hhi : x.toReal < (2 : Real) ^ (a + 1) := by
      rw [← Real.rpow_natCast]
      apply (Real.logb_lt_iff_lt_rpow (by norm_num) hxR0).mp
      simpa only [Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one (Real.logb 2 x.toReal)
    refine ⟨⟨a, haN⟩, ?_, ?_⟩
    · apply (ENNReal.toReal_le_toReal (by finiteness) hxTop).mp
      simpa using hlo
    · apply (ENNReal.toReal_lt_toReal hxTop (by finiteness)).mp
      simpa using hhi
  let Obs (R : iota) (v : Fin N × Fin N) : Prop :=
    (2 : ENNReal) ^ v.1.val ≤ (actualDescendantsW95 F assign k l R).card ∧
    ((actualDescendantsW95 F assign k l R).card : ENNReal) < (2 : ENNReal) ^ (v.1.val + 1) ∧
    (2 : ENNReal) ^ v.2.val ≤ actualRelativeFrostmanW95 F assign tube k l R ∧
    actualRelativeFrostmanW95 F assign tube k l R < (2 : ENNReal) ^ (v.2.val + 1)
  have hlabels : ∀ R : iota, ∃ v : Fin N × Fin N, R ∈ F.image (assign k) → Obs R v := by
    intro R
    by_cases hR : R ∈ F.image (assign k)
    · obtain ⟨a, ha₀, ha₁⟩ := hbin ((actualDescendantsW95 F assign k l R).card : ENNReal)
        (by exact_mod_cast hcount_pos R hR) (hcount_upper R hR)
      obtain ⟨b, hb₀, hb₁⟩ := hbin (actualRelativeFrostmanW95 F assign tube k l R)
        (hfrostman_lower R hR) (hfrostman_upper R hR)
      exact ⟨(a, b), fun _ => ⟨ha₀, ha₁, hb₀, hb₁⟩⟩
    · exact ⟨(⟨0, hN⟩, ⟨0, hN⟩), fun h => False.elim (hR h)⟩
  choose label hlabel using hlabels
  letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  obtain ⟨v, hv⟩ := exists_heaviestFiber_ennreal_w87 F
    (fun i => volume (Y i).shade) (fun i => label (assign k i)) hmass_pos
  let kept := actualBandParentsW95 F assign tube k l v.1.val v.2.val
  let A := F.filter (fun i => assign k i ∈ kept)
  have hkeptSub : kept ⊆ F.image (assign k) := Finset.filter_subset _ _
  have hclassSub : F.filter (fun i => label (assign k i) = v) ⊆ A := by
    intro i hi
    obtain ⟨hiF, hiLabel⟩ := Finset.mem_filter.mp hi
    have hiParent : assign k i ∈ F.image (assign k) := Finset.mem_image.mpr ⟨i, hiF, rfl⟩
    have hObs := hlabel (assign k i) hiParent
    rw [hiLabel] at hObs
    exact Finset.mem_filter.mpr ⟨hiF, Finset.mem_filter.mpr ⟨hiParent, hObs⟩⟩
  have hsumClass : (∑ i ∈ F.filter (fun i => label (assign k i) = v), volume (Y i).shade)
      ≤ ∑ i ∈ A, volume (Y i).shade :=
    Finset.sum_le_sum_of_subset hclassSub
  have hmassUpper : (∑ i ∈ F, volume (Y i).shade) ≤
      (N : ENNReal) ^ 2 * ∑ i ∈ A, volume (Y i).shade := by
    have hv' : (∑ i ∈ F, volume (Y i).shade) ≤ (N : ENNReal) ^ 2 *
        ∑ i ∈ F.filter (fun i => label (assign k i) = v), volume (Y i).shade := by
      simpa only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, pow_two] using hv
    exact hv'.trans (mul_le_mul_left' hsumClass _)
  have hmass : ((N : ENNReal) ^ 2)⁻¹ * (∑ i ∈ F, volume (Y i).shade) ≤
      ∑ i ∈ A, volume (Y i).shade := by
    apply (ENNReal.inv_mul_le_iff (pow_ne_zero _ (Nat.cast_ne_zero.mpr hN.ne'))
      (by finiteness)).mpr
    exact hmassUpper
  have hAnonempty : A.Nonempty := by
    by_contra hA
    have hAempty : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    have hzero : (∑ i ∈ F, volume (Y i).shade) ≤ 0 := by
      simpa only [hAempty, Finset.sum_empty, mul_zero] using hmassUpper
    exact (not_le_of_gt hmass_pos) hzero
  have hAsub : A ⊆ F := Finset.filter_subset _ _
  have himage : A.image (assign k) = kept := by
    ext R
    constructor
    · intro hR
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hR
      exact (Finset.mem_filter.mp hi).2
    · intro hR
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hkeptSub hR)
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hR⟩, rfl⟩
  have hkeptNonempty : kept.Nonempty := himage ▸ hAnonempty.image (assign k)
  have hfibre : ∀ R ∈ kept,
      completeFibreW94 A (assign k) R = completeFibreW94 F (assign k) R := by
    intro R hR
    ext i
    simp only [completeFibreW94, A, Finset.mem_filter]
    exact ⟨fun hi => ⟨hi.1.1, hi.2⟩,
      fun hi => ⟨⟨hi.1, hi.2 ▸ hR⟩, hi.2⟩⟩
  have hdesc : ∀ R ∈ kept,
      actualDescendantsW95 A assign k l R = actualDescendantsW95 F assign k l R := by
    intro R hR
    simp only [actualDescendantsW95, hfibre R hR]
  refine ⟨v.1.val, v.2.val, A, kept, v.1.isLt, v.2.isLt, rfl, rfl,
    hkeptNonempty, hAnonempty, hAsub, himage, hfibre, hdesc, ?_, hmass⟩
  intro R hR
  simp only [actualRelativeFrostmanW95, hdesc R hR]





/-- P2 actual construction: the output supplies a new working tower and
regularity of the final family, from a raw centred line-ED family. It can
also initialize the fixed canonical net once, before any restart. -/
theorem exists_actual_source_regularized_working_tower_w95
    (hdim : Module.finrank Real E = 3) (M : Nat) (hM : 1 <= M)
    (Cbase : NNReal) (hCbase : 1 <= Cbase) :
    ∃ (Ccan Ctw Ccell Ctower : NNReal) (Ktower : Nat) (delta0 : NNReal),
      1 <= Ccan ∧ 1 <= Ctw ∧ 1 <= Ccell ∧ 1 <= Ctower ∧ 1 <= Ktower ∧
      0 < delta0 ∧ delta0 < 1 ∧
      ∀ {delta : NNReal}, 0 < delta -> delta < delta0 ->
        ∀ {iota : Type uI} [DecidableEq iota]
          (F : Finset iota) (Y : iota -> ShadedTube delta E),
          (∀ i ∈ F, (Y i).carrier ⊆ Metric.closedBall 0 1) ->
          (∀ i ∈ F, centredTubeW94 (Y i).toTube) ->
          lineEssentiallyDistinctW94 F (fun i => (Y i).toTube) Cbase ->
          (0 < ∑ i ∈ F, volume (Y i).shade) ->
          ∃ (A : Finset iota)
            (U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan),
            A.Nonempty ∧ A ⊆ F ∧
            towerPreparationRetainedW95 delta Ctower Ktower *
                (∑ i ∈ F, volume (Y i).shade) <=
              (∑ i ∈ A, volume (Y i).shade) ∧
            Nonempty (SourceRegularizedWorkingTowerW95 U Ctw Ccell) := by
  have hfibre_filter {delta : NNReal} {iota : Type uI} [DecidableEq iota]
      (S B : Finset iota) (T : iota -> Tube delta E)
      (G : Tube.GridCoverSystem S T M) (hBS : B ⊆ S)
      (h k : Nat) (hhk : h <= k) (hkM : k <= M) (kept : Finset iota) :
      ∀ R ∈ (B.filter (fun i => G.assign h i ∈ kept)).image (G.assign k),
        completeFibreW94 (B.filter (fun i => G.assign h i ∈ kept)) (G.assign k) R =
          completeFibreW94 B (G.assign k) R := by
    intro R hR
    obtain ⟨i, hi, hiR⟩ := Finset.mem_image.mp hR
    obtain ⟨hiB, hikept⟩ := Finset.mem_filter.mp hi
    ext j
    simp only [completeFibreW94, Finset.mem_filter]
    constructor
    · intro hj
      exact ⟨hj.1.1, hj.2⟩
    · rintro ⟨hjB, hjR⟩
      have heq : G.assign h j = G.assign h i :=
        G.assign_eq_of_le hhk hkM (hBS hjB) (hBS hiB) (hjR.trans hiR.symm)
      exact ⟨⟨hjB, heq ▸ hikept⟩, hjR⟩
  have hmass_finite {delta : NNReal} {iota : Type uI}
      (F : Finset iota) (Y : iota -> ShadedTube delta E) :
      (∑ i ∈ F, volume (Y i).shade) < ⊤ := by
    apply ENNReal.sum_lt_top.mpr
    intro i hi
    exact (measure_mono (Y i).shade_subset).trans_lt (Y i).toTube.isCompact.measure_lt_top
  have hstage {delta : NNReal} {iota : Type uI} [DecidableEq iota]
      (S : Finset iota) (Y : iota -> ShadedTube delta E)
      (G : Tube.GridCoverSystem S (fun i => (Y i).toTube) M)
      (H : ENNReal) (hH : 1 <= H) (hHt : H < ⊤)
      (hrange : ∀ B ⊆ S, ∀ k l, k < l -> l <= M -> ∀ R ∈ B.image (G.assign k),
        1 <= (actualDescendantsW95 B G.assign k l R).card ∧
        ((actualDescendantsW95 B G.assign k l R).card : ENNReal) <= H ∧
        1 <= actualRelativeFrostmanW95 B G.assign G.tube k l R ∧
        actualRelativeFrostmanW95 B G.assign G.tube k l R <= H)
      (B : Finset iota) (hBS : B ⊆ S) (hmass : 0 < ∑ i ∈ B, volume (Y i).shade)
      (k : Nat) (hkM : k < M) :
      ∃ (A : Finset iota) (a b : Nat -> Nat),
        A ⊆ B ∧ (0 < ∑ i ∈ A, volume (Y i).shade) ∧
        (∑ i ∈ B, volume (Y i).shade) <=
          (dyadicRangeLengthW95 H : ENNReal) ^ (2 * M) * ∑ i ∈ A, volume (Y i).shade ∧
        (∀ q, k <= q -> q <= M -> ∀ R ∈ A.image (G.assign q),
          completeFibreW94 A (G.assign q) R = completeFibreW94 B (G.assign q) R) ∧
        (∀ l, k < l -> l <= M -> ∀ R ∈ A.image (G.assign k),
          (2 : ENNReal) ^ a l <= (actualDescendantsW95 A G.assign k l R).card ∧
          ((actualDescendantsW95 A G.assign k l R).card : ENNReal) < 2 ^ (a l + 1) ∧
          (2 : ENNReal) ^ b l <= actualRelativeFrostmanW95 A G.assign G.tube k l R ∧
          actualRelativeFrostmanW95 A G.assign G.tube k l R < 2 ^ (b l + 1)) := by
    let L : ENNReal := dyadicRangeLengthW95 H
    have hLone : 1 <= L := by
      dsimp [L, dyadicRangeLengthW95]
      exact_mod_cast (show 1 <= Nat.floor (Real.log H.toReal / Real.log 2) + 1 by omega)
    have hLzero : L ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hLone)
    have hLtop : L ≠ ⊤ := by simp [L]
    have hsteps : ∀ n, n <= M ->
        ∃ (A : Finset iota) (a b : Nat -> Nat),
          A ⊆ B ∧ (0 < ∑ i ∈ A, volume (Y i).shade) ∧
          (∑ i ∈ B, volume (Y i).shade) <= L ^ (2 * n) * ∑ i ∈ A, volume (Y i).shade ∧
          (∀ q, k <= q -> q <= M -> ∀ R ∈ A.image (G.assign q),
            completeFibreW94 A (G.assign q) R = completeFibreW94 B (G.assign q) R) ∧
          (∀ l, k < l -> l <= n -> ∀ R ∈ A.image (G.assign k),
            (2 : ENNReal) ^ a l <= (actualDescendantsW95 A G.assign k l R).card ∧
            ((actualDescendantsW95 A G.assign k l R).card : ENNReal) < 2 ^ (a l + 1) ∧
            (2 : ENNReal) ^ b l <= actualRelativeFrostmanW95 A G.assign G.tube k l R ∧
            actualRelativeFrostmanW95 A G.assign G.tube k l R < 2 ^ (b l + 1)) := by
      intro n
      induction n with
      | zero =>
          intro hn
          refine ⟨B, fun _ => 0, fun _ => 0, Finset.Subset.refl _, hmass, ?_, ?_, ?_⟩
          · simp
          · intro q hq hqM R hR
            rfl
          · intro l hkl hl
            omega
      | succ n ih =>
          intro hnM
          obtain ⟨A, a, b, hAB, hAmass, hpay, hfibres, hbands⟩ := ih (by omega)
          by_cases hkn : k < n + 1
          · have hAS : A ⊆ S := hAB.trans hBS
            have hr := hrange A hAS k (n + 1) hkn hnM
            obtain ⟨aNew, bNew, A', kept, haNew, hbNew, hkept, hA', hkeptne,
                hA'ne, hA'A, himage, hfibre, hdesc, hCF, hpaid⟩ :=
              exists_actual_count_relative_frostman_band_w95 A Y G.assign G.tube
                k (n + 1) H hH hHt (fun R hR => (hr R hR).1)
                (fun R hR => (hr R hR).2.1) (fun R hR => (hr R hR).2.2.1)
                (fun R hR => (hr R hR).2.2.2) hAmass (hmass_finite A Y)
            have hmassStep : (∑ i ∈ A, volume (Y i).shade) <=
                L ^ 2 * ∑ i ∈ A', volume (Y i).shade :=
              (ENNReal.inv_mul_le_iff (pow_ne_zero _ hLzero) (by finiteness)).mp hpaid
            have hA'pos : 0 < ∑ i ∈ A', volume (Y i).shade := by
              by_contra hnpos
              have hz : (∑ i ∈ A', volume (Y i).shade) = 0 := le_antisymm (not_lt.mp hnpos) bot_le
              rw [hz, mul_zero] at hmassStep
              exact (not_le_of_gt hAmass) hmassStep
            have hkeep : ∀ q, k <= q -> q <= M -> ∀ R ∈ A'.image (G.assign q),
                completeFibreW94 A' (G.assign q) R = completeFibreW94 A (G.assign q) R := by
              intro q hkq hqM R hR
              rw [hA'] at hR ⊢
              exact hfibre_filter S A (fun i => (Y i).toTube) G hAS k q hkq hqM kept R hR
            refine ⟨A', (fun l => if l = n + 1 then aNew else a l),
              (fun l => if l = n + 1 then bNew else b l), hA'A.trans hAB, hA'pos, ?_, ?_, ?_⟩
            · calc
                (∑ i ∈ B, volume (Y i).shade) <= L ^ (2 * n) *
                    (L ^ 2 * ∑ i ∈ A', volume (Y i).shade) :=
                  hpay.trans (mul_le_mul_left' hmassStep _)
                _ = L ^ (2 * (n + 1)) * ∑ i ∈ A', volume (Y i).shade := by
                  rw [← mul_assoc, ← pow_add]
                  congr 2
            · intro q hkq hqM R hR
              exact (hkeep q hkq hqM R hR).trans
                (hfibres q hkq hqM R (Finset.image_subset_image hA'A hR))
            · intro l hkl hl R hR
              have hRA : R ∈ A.image (G.assign k) := Finset.image_subset_image hA'A hR
              have hFibreEq := hkeep k le_rfl hkM.le R hR
              have hDEq : actualDescendantsW95 A' G.assign k l R =
                  actualDescendantsW95 A G.assign k l R := by
                simp only [actualDescendantsW95, hFibreEq]
              have hFEq : actualRelativeFrostmanW95 A' G.assign G.tube k l R =
                  actualRelativeFrostmanW95 A G.assign G.tube k l R := by
                simp only [actualRelativeFrostmanW95, hDEq]
              by_cases hln : l = n + 1
              · subst l
                have hRkept : R ∈ kept := himage ▸ hR
                have hbnd := (Finset.mem_filter.mp (hkept ▸ hRkept)).2
                simpa only [ite_true, hDEq, hFEq] using hbnd
              · have hbnd := hbands l hkl (by omega) R hRA
                simpa only [if_neg hln, hDEq, hFEq] using hbnd
          · refine ⟨A, a, b, hAB, hAmass, ?_, hfibres, ?_⟩
            · exact hpay.trans (mul_le_mul_right'
                (pow_le_pow_right₀ hLone (by omega : 2 * n <= 2 * (n + 1))) _)
            · intro l hkl hl
              exact hbands l hkl (by omega)
    exact hsteps M le_rfl
  have hregularize {delta : NNReal} {iota : Type uI} [DecidableEq iota]
      (S : Finset iota) (Y : iota -> ShadedTube delta E)
      (G : Tube.GridCoverSystem S (fun i => (Y i).toTube) M)
      (H : ENNReal) (hH : 1 <= H) (hHt : H < ⊤)
      (hrange : ∀ B ⊆ S, ∀ k l, k < l -> l <= M -> ∀ R ∈ B.image (G.assign k),
        1 <= (actualDescendantsW95 B G.assign k l R).card ∧
        ((actualDescendantsW95 B G.assign k l R).card : ENNReal) <= H ∧
        1 <= actualRelativeFrostmanW95 B G.assign G.tube k l R ∧
        actualRelativeFrostmanW95 B G.assign G.tube k l R <= H)
      (hmass : 0 < ∑ i ∈ S, volume (Y i).shade) :
      ∃ (A : Finset iota) (a b : Nat -> Nat -> Nat),
        A ⊆ S ∧ (0 < ∑ i ∈ A, volume (Y i).shade) ∧
        (∑ i ∈ S, volume (Y i).shade) <=
          (dyadicRangeLengthW95 H : ENNReal) ^ (2 * M * M) * ∑ i ∈ A, volume (Y i).shade ∧
        (∀ k l, k < l -> l <= M -> ∀ R ∈ A.image (G.assign k),
          (2 : ENNReal) ^ a k l <= (actualDescendantsW95 A G.assign k l R).card ∧
          ((actualDescendantsW95 A G.assign k l R).card : ENNReal) < 2 ^ (a k l + 1) ∧
          (2 : ENNReal) ^ b k l <= actualRelativeFrostmanW95 A G.assign G.tube k l R ∧
          actualRelativeFrostmanW95 A G.assign G.tube k l R < 2 ^ (b k l + 1)) := by
    let L : ENNReal := dyadicRangeLengthW95 H
    have hsteps : ∀ r, r <= M ->
        ∃ (A : Finset iota) (a b : Nat -> Nat -> Nat),
          A ⊆ S ∧ (0 < ∑ i ∈ A, volume (Y i).shade) ∧
          (∑ i ∈ S, volume (Y i).shade) <=
            L ^ (2 * M * r) * ∑ i ∈ A, volume (Y i).shade ∧
          (∀ k l, M - r <= k -> k < l -> l <= M -> ∀ R ∈ A.image (G.assign k),
            (2 : ENNReal) ^ a k l <= (actualDescendantsW95 A G.assign k l R).card ∧
            ((actualDescendantsW95 A G.assign k l R).card : ENNReal) < 2 ^ (a k l + 1) ∧
            (2 : ENNReal) ^ b k l <= actualRelativeFrostmanW95 A G.assign G.tube k l R ∧
            actualRelativeFrostmanW95 A G.assign G.tube k l R < 2 ^ (b k l + 1)) := by
      intro r
      induction r with
      | zero =>
          intro hr
          refine ⟨S, fun _ _ => 0, fun _ _ => 0, Finset.Subset.refl _, hmass, ?_, ?_⟩
          · simp
          · intro k l hk hkl hl
            omega
      | succ r ih =>
          intro hrM
          obtain ⟨A, a, b, hAS, hApos, hpaid, hbands⟩ := ih (by omega)
          let k := M - (r + 1)
          have hkM : k < M := by dsimp [k]; omega
          obtain ⟨A', aNew, bNew, hA'A, hA'pos, hstepPay, hkeep, hnew⟩ :=
            hstage S Y G H hH hHt hrange A hAS hApos k hkM
          refine ⟨A', (fun q l => if q = k then aNew l else a q l),
            (fun q l => if q = k then bNew l else b q l), hA'A.trans hAS, hA'pos, ?_, ?_⟩
          · calc
              (∑ i ∈ S, volume (Y i).shade) <=
                  L ^ (2 * M * r) * (L ^ (2 * M) * ∑ i ∈ A', volume (Y i).shade) :=
                hpaid.trans (mul_le_mul_left' hstepPay _)
              _ = L ^ (2 * M * (r + 1)) * ∑ i ∈ A', volume (Y i).shade := by
                rw [← mul_assoc, ← pow_add]
                congr 2 <;> ring
          · intro q l hq hql hl R hR
            by_cases hqk : q = k
            · subst q
              simpa only [ite_true] using hnew l hql hl R hR
            · have hkq : k <= q := hq
              have hqM : q <= M := by omega
              have hqold : M - r <= q := by dsimp [k] at hqk; omega
              have hRold : R ∈ A.image (G.assign q) := Finset.image_subset_image hA'A hR
              have hFibreEq := hkeep q hkq hqM R hR
              have hDEq : actualDescendantsW95 A' G.assign q l R =
                  actualDescendantsW95 A G.assign q l R := by
                simp only [actualDescendantsW95, hFibreEq]
              have hFEq : actualRelativeFrostmanW95 A' G.assign G.tube q l R =
                  actualRelativeFrostmanW95 A G.assign G.tube q l R := by
                simp only [actualRelativeFrostmanW95, hDEq]
              simpa only [if_neg hqk, hDEq, hFEq] using hbands q l hqold hql hl R hRold
    obtain ⟨A, a, b, hAS, hApos, hpaid, hbands⟩ := hsteps M le_rfl
    exact ⟨A, a, b, hAS, hApos, hpaid, fun k l hkl hl =>
      hbands k l (by omega) hkl hl⟩
  have hfrostman_equal_volume {iota : Type uI} (D : Finset iota)
      (V : iota -> ConvexSpaceBody E) (P : ConvexSpaceBody E) (v : ENNReal)
      (hD : D.Nonempty) (hvol : ∀ i ∈ D, volume (V i).carrier = v)
      (hv0 : v ≠ 0) (hvt : v ≠ ⊤)
      (hP0 : volume P.carrier ≠ 0) (hPt : volume P.carrier ≠ ⊤)
      (hle : ∀ i ∈ D, V i <= P) :
      1 <= frostmanConstIn D V P ∧ frostmanConstIn D V P <= volume P.carrier / v := by
    have hdensity : Kakeya.densityIn D V P = (D.card : ENNReal) * v / volume P.carrier := by
      rw [Kakeya.densityIn_of_all_le hle]
      congr 1
      calc
        (∑ i ∈ D, volume (V i).carrier) = ∑ i ∈ D, v := Finset.sum_congr rfl hvol
        _ = (D.card : ENNReal) * v := by rw [Finset.sum_const, nsmul_eq_mul]
    have hdensity_pos : 0 < Kakeya.densityIn D V P := by
      rw [hdensity]
      exact ENNReal.div_pos (mul_ne_zero (by exact_mod_cast hD.card_ne_zero) hv0) hPt
    refine ⟨(isFrostmanIn_frostmanConstIn D V P).one_le hdensity_pos, ?_⟩
    apply frostmanConstIn_le
    intro Q hQP
    have hcancel : volume P.carrier / v * Kakeya.densityIn D V P = (D.card : ENNReal) := by
      rw [hdensity, div_eq_mul_inv, div_eq_mul_inv]
      calc
        volume P.carrier * v⁻¹ * ((D.card : ENNReal) * v * (volume P.carrier)⁻¹) =
            (D.card : ENNReal) * (v * v⁻¹) * (volume P.carrier * (volume P.carrier)⁻¹) := by ring
        _ = (D.card : ENNReal) := by
          rw [ENNReal.mul_inv_cancel hv0 hvt, ENNReal.mul_inv_cancel hP0 hPt]
          simp
    rw [hcancel]
    exact Kakeya.densityIn_le_card D V Q
  have hown_line {delta : NNReal} (T : Tube delta E) :
      liesInFiveDeltaLineTubeW94 T T.x T.direction := by
    intro x hx
    rw [T.carrier_eq] at hx
    obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.mp hx
    rw [segment_eq_image'] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    refine ⟨t, (Metric.mem_closedBall.mp hxz).trans ?_⟩
    have hd := delta.coe_nonneg
    change (delta : Real) <= 5 * (delta : Real)
    linarith
  have hweighted_injective {delta : NNReal} (hdelta : 0 < delta)
      {iota : Type uI} [DecidableEq iota]
      (F : Finset iota) (Y : iota -> ShadedTube delta E)
      (hline : lineEssentiallyDistinctW94 F (fun i => (Y i).toTube) Cbase)
      (hmass : 0 < ∑ i ∈ F, volume (Y i).shade) :
      ∃ G ⊆ F, G.Nonempty ∧
        Set.InjOn (fun i => (Y i).carrier) (G : Set iota) ∧
        (0 < ∑ i ∈ G, volume (Y i).shade) ∧
        (∑ i ∈ F, volume (Y i).shade) <=
          bandLoss F.card * (2 * (Cbase : ENNReal)) * ∑ i ∈ G, volume (Y i).shade := by
    obtain ⟨B, hBF, lam, hlam, hB, hband, hpaid, hfull⟩ := exists_massBand hdelta F Y hmass
    letI : Nonempty iota := ⟨hB.choose⟩
    let rep : iota -> iota := Tube.carrierRep B (fun i => (Y i).toTube)
    let G : Finset iota := B.image rep
    have hGB : G ⊆ B := Tube.carrierRep_image_subset
    have hG : G.Nonempty := hB.image rep
    have hpair : ∀ j ∈ G, ∀ i ∈ B.filter (fun i => rep i = j),
        (Y i).carrier = (Y j).carrier := by
      intro j hj i hi
      obtain ⟨hiB, hirep⟩ := Finset.mem_filter.mp hi
      have heq := Tube.carrierRep_carrier (T := fun i => (Y i).toTube) hiB
      change (Y (rep i)).carrier = (Y i).carrier at heq
      rw [hirep] at heq
      exact heq.symm
    have hcard : ∀ j ∈ G, ((B.filter (fun i => rep i = j)).card : ENNReal) <= Cbase := by
      intro j hj
      have hsubset : B.filter (fun i => rep i = j) ⊆
          F.filter (fun i => liesInFiveDeltaLineTubeW94 (Y i).toTube (Y j).x (Y j).direction) := by
        intro i hi
        refine Finset.mem_filter.mpr ⟨hBF (Finset.mem_filter.mp hi).1, ?_⟩
        intro x hx
        have hc := hpair j hj i hi
        exact hown_line (Y j).toTube x (hc ▸ hx)
      have hcap := hline (Y j).x (Y j).direction (Y j).toTube.norm_direction
      have hcardNN : ((B.filter (fun i => rep i = j)).card : NNReal) <= Cbase := by
        calc
          ((B.filter (fun i => rep i = j)).card : NNReal) <=
              ((F.filter (fun i => liesInFiveDeltaLineTubeW94 (Y i).toTube
                (Y j).x (Y j).direction)).card : NNReal) := by
            exact_mod_cast Finset.card_le_card hsubset
          _ <= Cbase := hcap
      exact_mod_cast hcardNN
    have hfibreMass : ∀ j ∈ G,
        (∑ i ∈ B.filter (fun i => rep i = j), volume (Y i).shade) <=
          (2 * (Cbase : ENNReal)) * volume (Y j).shade := by
      intro j hj
      have hterm : ∀ i ∈ B.filter (fun i => rep i = j),
          volume (Y i).shade <= 2 * volume (Y j).shade := by
        intro i hi
        have hiB := (Finset.mem_filter.mp hi).1
        calc
          volume (Y i).shade <= 2 * (lam : ENNReal) * volume (Y i).carrier := (hband i hiB).2
          _ = 2 * ((lam : ENNReal) * volume (Y j).carrier) := by rw [hpair j hj i hi, mul_assoc]
          _ <= 2 * volume (Y j).shade := mul_le_mul_left' (hband j (hGB hj)).1 _
      calc
        (∑ i ∈ B.filter (fun i => rep i = j), volume (Y i).shade) <=
            ∑ i ∈ B.filter (fun i => rep i = j), 2 * volume (Y j).shade :=
          Finset.sum_le_sum hterm
        _ = ((B.filter (fun i => rep i = j)).card : ENNReal) * (2 * volume (Y j).shade) := by
          rw [Finset.sum_const, nsmul_eq_mul]
        _ <= (Cbase : ENNReal) * (2 * volume (Y j).shade) := mul_le_mul_right' (hcard j hj) _
        _ = (2 * (Cbase : ENNReal)) * volume (Y j).shade := by ring
    have hmassBG : (∑ i ∈ B, volume (Y i).shade) <=
        (2 * (Cbase : ENNReal)) * ∑ i ∈ G, volume (Y i).shade := by
      calc
        (∑ i ∈ B, volume (Y i).shade) =
            ∑ j ∈ G, ∑ i ∈ B.filter (fun i => rep i = j), volume (Y i).shade :=
          (Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image.mpr ⟨i, hi, rfl⟩)
            (fun i => volume (Y i).shade)).symm
        _ <= ∑ j ∈ G, (2 * (Cbase : ENNReal)) * volume (Y j).shade := Finset.sum_le_sum hfibreMass
        _ = (2 * (Cbase : ENNReal)) * ∑ j ∈ G, volume (Y j).shade := (Finset.mul_sum _ _ _).symm
    have hmassFG : (∑ i ∈ F, volume (Y i).shade) <=
        bandLoss F.card * (2 * (Cbase : ENNReal)) * ∑ i ∈ G, volume (Y i).shade := by
      simpa only [mul_assoc] using hpaid.trans (mul_le_mul_left' hmassBG (bandLoss F.card))
    have hGpos : 0 < ∑ i ∈ G, volume (Y i).shade := by
      by_contra hnot
      have hz : (∑ i ∈ G, volume (Y i).shade) = 0 := le_antisymm (not_lt.mp hnot) bot_le
      rw [hz, mul_zero] at hmassFG
      exact (not_le_of_gt hmass) hmassFG
    exact ⟨G, hGB.trans hBF, hG, Tube.carrierRep_injOn_image, hGpos, hmassFG⟩
  have hinput_card {delta : NNReal} (hdelta : 0 < delta) (hdelta1 : delta <= 1)
      {iota : Type uI} [DecidableEq iota]
      (F : Finset iota) (T : iota -> Tube delta E)
      (hball : ∀ i ∈ F, (T i).carrier ⊆ Metric.closedBall (0 : E) 1)
      (hline : lineEssentiallyDistinctW94 F T Cbase) :
      (F.card : Real) <= (5 : Real) ^ (6 : Nat) * (Cbase : Real) *
        (delta : Real) ^ (-(6 : Real)) := by
    have hd : (0 : Real) < delta := by exact_mod_cast hdelta
    have hd1 : (delta : Real) <= 1 := by exact_mod_cast hdelta1
    obtain ⟨P, hPF, hsep, hcover⟩ := exists_maximal_separated_finset F
      (fun i j => ‖(T i).midpoint - (T j).midpoint‖ + ‖(T i).direction - (T j).direction‖)
      (ε := (delta : Real)) (fun i => by simpa using hd)
      (fun i j => by rw [norm_sub_rev (T i).midpoint, norm_sub_rev (T i).direction])
    let assign : iota -> iota := fun i => if hi : i ∈ F then (hcover i hi).choose else i
    have hass : ∀ i ∈ F, assign i ∈ P ∧
        ‖(T i).midpoint - (T (assign i)).midpoint‖ +
          ‖(T i).direction - (T (assign i)).direction‖ < (delta : Real) := by
      intro i hi
      simpa only [assign, dif_pos hi] using (hcover i hi).choose_spec
    have hcluster : ∀ i ∈ F,
        liesInFiveDeltaLineTubeW94 (T i) (T (assign i)).midpoint (T (assign i)).direction := by
      intro i hi x hx
      obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.mp ((T i).carrier_eq ▸ hx)
      rw [segment_eq_image'] at hz
      obtain ⟨theta, htheta, hthetaZ⟩ := hz
      let t : Real := theta - 1 / 2
      have ht : |t| <= 1 / 2 := by
        rw [abs_le]
        dsimp [t]
        constructor <;> linarith [htheta.1, htheta.2]
      have hzt : z = (T i).midpoint + t • (T i).direction := by
        rw [← hthetaZ]
        dsimp [t, Tube.midpoint, Tube.direction]
        module
      let j := assign i
      have hzclose : dist z ((T j).midpoint + t • (T j).direction) <= (delta : Real) := by
        rw [hzt, dist_eq_norm]
        have heq : (T i).midpoint + t • (T i).direction -
            ((T j).midpoint + t • (T j).direction) =
            ((T i).midpoint - (T j).midpoint) + t • ((T i).direction - (T j).direction) := by module
        rw [heq]
        calc
          _ <= ‖(T i).midpoint - (T j).midpoint‖ +
              |t| * ‖(T i).direction - (T j).direction‖ := by
            simpa only [norm_smul, Real.norm_eq_abs] using norm_add_le
              ((T i).midpoint - (T j).midpoint) (t • ((T i).direction - (T j).direction))
          _ <= (delta : Real) := by
            have hdist := (hass i hi).2
            change ‖(T i).midpoint - (T j).midpoint‖ +
              ‖(T i).direction - (T j).direction‖ < (delta : Real) at hdist
            nlinarith [norm_nonneg ((T i).direction - (T j).direction)]
      refine ⟨t, ?_⟩
      have htri := dist_triangle x z ((T j).midpoint + t • (T j).direction)
      have hxz' := Metric.mem_closedBall.mp hxz
      change dist x ((T j).midpoint + t • (T j).direction) <= 5 * (delta : Real)
      linarith
    have hfibrecard : ∀ j ∈ P, ((F.filter (fun i => assign i = j)).card : Real) <= Cbase := by
      intro j hj
      have hsub : F.filter (fun i => assign i = j) ⊆
          F.filter (fun i => liesInFiveDeltaLineTubeW94 (T i) (T j).midpoint (T j).direction) := by
        intro i hi
        obtain ⟨hiF, hij⟩ := Finset.mem_filter.mp hi
        exact Finset.mem_filter.mpr ⟨hiF, hij ▸ hcluster i hiF⟩
      have hcap := hline (T j).midpoint (T j).direction (T j).norm_direction
      have hcapR : ((F.filter (fun i => liesInFiveDeltaLineTubeW94
          (T i) (T j).midpoint (T j).direction)).card : Real) <= Cbase := by exact_mod_cast hcap
      exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans hcapR
    have hcardFP : (F.card : Real) <= (P.card : Real) * Cbase := by
      calc
        (F.card : Real) = ∑ j ∈ P, ((F.filter (fun i => assign i = j)).card : Real) := by
          simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using
            (Finset.sum_fiberwise_of_maps_to (fun i hi => (hass i hi).1) (fun _ => (1 : Real))).symm
        _ <= ∑ j ∈ P, (Cbase : Real) := Finset.sum_le_sum hfibrecard
        _ = (P.card : Real) * Cbase := by rw [Finset.sum_const, nsmul_eq_mul]
    have hcardP : (P.card : Real) <= ((5 : Real) / delta) ^ (6 : Nat) := by
      have hpack := Tube.card_le_of_L1_separated_in_box P
        (fun i => (T i).midpoint) (fun i => (T i).direction) (0 : E) (0 : E)
        (R := (1 : Real)) hd hsep
        (fun i hi => by simpa using Tube.norm_midpoint_le_of_subset_ball hdelta (T i) (hball i (hPF hi)))
        (fun i hi => by simpa using (T i).norm_direction.le)
      rw [hdim] at hpack
      have hratio : ((1 : Real) + (delta : Real) / 4) / ((delta : Real) / 4) <= 5 / (delta : Real) := by
        apply (div_le_div_iff₀ (by positivity) hd).mpr
        nlinarith
      exact hpack.trans (pow_le_pow_left₀ (by positivity) hratio 6)
    calc
      (F.card : Real) <= ((5 : Real) / delta) ^ (6 : Nat) * Cbase :=
        hcardFP.trans (mul_le_mul_of_nonneg_right hcardP Cbase.coe_nonneg)
      _ = (5 : Real) ^ (6 : Nat) * (Cbase : Real) * (delta : Real) ^ (-(6 : Real)) := by
        rw [div_pow, Real.rpow_neg hd.le]
        norm_num only [Real.rpow_ofNat]
        ring
  have hsmall_node_ball {rho : NNReal} (W : Tube rho E)
      (hrho : (rho : Real) <= 1 / 16)
      (hmid : ‖W.midpoint‖ <= 1 + (rho : Real) / 16) :
      W.carrier ⊆ Metric.closedBall (0 : E) 2 := by
    intro x hx
    obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.mp (W.carrier_eq ▸ hx)
    obtain ⟨t, ht, hzt⟩ := W.exists_param_of_mem_segment hz
    have hzNorm : ‖z‖ <= 1 + (rho : Real) / 16 + 1 / 2 := by
      rw [hzt]
      have htri := norm_add_le W.midpoint (t • W.direction)
      have hs : ‖t • W.direction‖ = |t| := by
        rw [norm_smul, Real.norm_eq_abs, W.norm_direction, mul_one]
      rw [hs] at htri
      linarith
    have htri := dist_triangle x z 0
    rw [dist_zero_right, dist_zero_right] at htri
    have hxz' := Metric.mem_closedBall.mp hxz
    rw [Metric.mem_closedBall, dist_zero_right]
    linarith
  have hroot_ball {delta : NNReal} (T : Tube delta E)
      (hball : T.carrier ⊆ Metric.closedBall (0 : E) 1) :
      (T.rescale 1).carrier ⊆ Metric.closedBall (0 : E) 2 := by
    intro x hx
    obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.mp ((T.rescale 1).carrier_eq ▸ hx)
    have hzT : z ∈ T.carrier := by
      rw [T.carrier_eq]
      exact Set.mem_iUnion₂.mpr ⟨z, hz, Metric.mem_closedBall_self delta.coe_nonneg⟩
    have hzNorm := Metric.mem_closedBall.mp (hball hzT)
    have hxz' := Metric.mem_closedBall.mp hxz
    have htri := dist_triangle x z 0
    rw [Metric.mem_closedBall]
    exact htri.trans (by norm_num only [NNReal.coe_one] at hxz'; linarith)
  have hnode_newroot {delta rho : NNReal} (W : Tube rho E) (T : Tube delta E)
      (hrho : (rho : Real) <= 1 / 16)
      (hmid : ‖W.midpoint - T.midpoint‖ <= 1 / 8 + (rho : Real) / 16)
      (hdir : ‖W.direction - T.direction‖ <= 1 / 4 + (rho : Real) / 8) :
      W.toConvexSpaceBody <= (T.rescale 1).toConvexSpaceBody := by
    apply _root_.Tube.le_of_params_close W (T.rescale 1) hmid hdir
    change 1 / 8 + (rho : Real) / 16 + (1 / 4 + (rho : Real) / 8) / 2 +
      (rho : Real) <= 1
    linarith
  have hlocalize {delta : NNReal} (hdelta : 0 < delta) (hdelta1 : delta < 1)
      (hsmall : delta <= (16 : NNReal) ^ (-(M : Real)))
      {iota : Type uI} [DecidableEq iota]
      (F : Finset iota) (Y : iota -> ShadedTube delta E)
      (hinj : Set.InjOn (fun i => (Y i).carrier) (F : Set iota))
      (hball : ∀ i ∈ F, (Y i).carrier ⊆ Metric.closedBall (0 : E) 1)
      (hmass : 0 < ∑ i ∈ F, volume (Y i).shade) :
      ∃ (S : Finset iota) (G : Tube.GridCoverSystem S (fun i => (Y i).toTube) M),
        S ⊆ F ∧ (0 < ∑ i ∈ S, volume (Y i).shade) ∧
        (∑ i ∈ F, volume (Y i).shade) <=
          ((641 : ENNReal) ^ (6 : Nat) * 4 ^ (6 : Nat)) * ∑ i ∈ S, volume (Y i).shade ∧
        (∀ k, k <= M -> S.image (G.assign k) = G.indexSet k) ∧
        (∀ i ∈ S, G.assign M i = i) ∧
        (∀ i ∈ S, (G.tube M i).toConvexSpaceBody = (Y i).toConvexSpaceBody) ∧
        (∀ k, k <= M -> Set.InjOn (G.tube k) (G.indexSet k : Set iota)) ∧
        (∀ k, k <= M -> ∀ V : Tube (Tube.gridScale delta M k) E,
          ((G.indexSet k).filter (fun R => ∃ i ∈ S,
            (Y i).toConvexSpaceBody <= (G.tube k R).toConvexSpaceBody ∧
            (Y i).toConvexSpaceBody <= V.toConvexSpaceBody)).card <=
              Tube.overlapConstBOTight (Module.finrank Real E)) ∧
        (∀ k, k <= M -> ∀ R ∈ G.indexSet k,
          (G.tube k R).carrier ⊆ Metric.closedBall (0 : E) 2) := by
    have hMpos : 0 < M := by omega
    have hF : F.Nonempty := by
      by_contra h
      simpa [Finset.not_nonempty_iff_eq_empty.mp h] using hmass
    have hrho1 : (Tube.gridScale delta M 1 : Real) <= 1 / 16 := by
      have hgap := Tube.sixteen_mul_gridScale_succ_le hdelta hsmall (k := 0) hMpos
      rw [Tube.gridScale_zero] at hgap
      have hgapR : 16 * (Tube.gridScale delta M 1 : Real) <= 1 := by exact_mod_cast hgap
      linarith
    have hgap : (delta : Real) ^ ((1 : Real) / (M : Real)) <= 1 / 2 := by
      have h := hrho1
      simp only [Tube.gridScale, NNReal.coe_rpow, Nat.cast_one] at h
      linarith
    obtain ⟨parent, assign, oldRoot, W, hamem, habottom, hanested, hcover,
        hbottom, hbottomCarrier, hWinj, hoverlap, hrescale, hparentCard, hcross,
        hmid, hdir⟩ := exists_actual_raw_tree_close_w96 hdelta hdelta1 F
      (fun i => (Y i).toTube) hinj M hMpos hgap (fun i hi => hball i hi) hF
    let Label := {R // R ∈ parent 0}
    obtain ⟨i0, hi0⟩ := hF
    letI : Nonempty Label := ⟨⟨assign 0 i0, hamem 0 (by omega) hi0⟩⟩
    let label : iota -> Label := fun i => if hi : i ∈ F then
      ⟨assign 0 i, hamem 0 (by omega) hi⟩ else ⟨assign 0 i0, hamem 0 (by omega) hi0⟩
    obtain ⟨R0, hpaidLabel⟩ := exists_heaviestFiber_ennreal_w87 F
      (fun i => volume (Y i).shade) label hmass
    let S := F.filter (fun i => assign 0 i = R0.val)
    have hSF : S ⊆ F := Finset.filter_subset _ _
    have hclass : F.filter (fun i => label i = R0) = S := by
      apply Finset.filter_congr
      intro i hi
      simp only [label, dif_pos hi]
      constructor
      · intro h
        exact congrArg (fun x : Label => x.val) h
      · intro h
        apply Subtype.ext
        exact h
    have hmassS : (∑ i ∈ F, volume (Y i).shade) <=
        ((parent 0).card : ENNReal) * ∑ i ∈ S, volume (Y i).shade := by
      simpa only [Label, Fintype.card_coe, hclass] using hpaidLabel
    have hSpos : 0 < ∑ i ∈ S, volume (Y i).shade := by
      by_contra hnot
      have hz : (∑ i ∈ S, volume (Y i).shade) = 0 := le_antisymm (not_lt.mp hnot) bot_le
      rw [hz, mul_zero] at hmassS
      exact (not_le_of_gt hmass) hmassS
    have hS : S.Nonempty := by
      by_contra h
      simpa [Finset.not_nonempty_iff_eq_empty.mp h] using hSpos
    obtain ⟨j0, hj0⟩ := hS
    have hparentZero : ((parent 0).card : ENNReal) <=
        (641 : ENNReal) ^ (6 : Nat) * 4 ^ (6 : Nat) := by
      have h := hparentCard 0 hMpos
      norm_num only [Nat.cast_zero, zero_div, NNReal.rpow_zero, NNReal.coe_one,
        div_one, hdim, Nat.mul_one, Nat.reduceMul] at h
      exact_mod_cast h
    have hSsame : ∀ i ∈ S, assign 0 i = assign 0 j0 := by
      intro i hi
      exact (Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj0).2.symm
    have hfirst_root : ∀ i ∈ S,
        (W 1 (assign 1 i)).toConvexSpaceBody <= ((Y j0).toTube.rescale 1).toConvexSpaceBody := by
      intro i hi
      have hiF := hSF hi
      have hjF := hSF hj0
      have hmidI := hmid 0 (by omega) hiF
      have hmidJ := hmid 0 (by omega) hjF
      have hdirI := hdir 0 (by omega) hiF
      have hdirJ := hdir 0 (by omega) hjF
      simp only [Nat.cast_zero, zero_div, NNReal.rpow_zero, NNReal.coe_one] at hmidI hmidJ hdirI hdirJ
      rw [hSsame i hi] at hmidI hdirI
      have hmidIJ : ‖(Y i).toTube.midpoint - (Y j0).toTube.midpoint‖ <= 1 / 8 := by
        have htri := norm_sub_le_norm_sub_add_norm_sub (Y i).toTube.midpoint
          (W 0 (assign 0 j0)).midpoint (Y j0).toTube.midpoint
        rw [norm_sub_rev (W 0 (assign 0 j0)).midpoint] at htri
        linarith
      have hdirIJ : ‖(Y i).toTube.direction - (Y j0).toTube.direction‖ <= 1 / 4 := by
        have htri := norm_sub_le_norm_sub_add_norm_sub (Y i).toTube.direction
          (W 0 (assign 0 j0)).direction (Y j0).toTube.direction
        rw [norm_sub_rev (W 0 (assign 0 j0)).direction] at htri
        linarith
      have hmid1 := hmid 1 hM hiF
      have hdir1 := hdir 1 hM hiF
      apply hnode_newroot (W 1 (assign 1 i)) (Y j0).toTube hrho1
      · have htri := norm_sub_le_norm_sub_add_norm_sub (W 1 (assign 1 i)).midpoint
          (Y i).toTube.midpoint (Y j0).toTube.midpoint
        rw [norm_sub_rev (W 1 (assign 1 i)).midpoint (Y i).toTube.midpoint] at htri
        linarith
      · have htri := norm_sub_le_norm_sub_add_norm_sub (W 1 (assign 1 i)).direction
          (Y i).toTube.direction (Y j0).toTube.direction
        rw [norm_sub_rev (W 1 (assign 1 i)).direction (Y i).toTube.direction] at htri
        linarith
    let newAssign : Nat -> iota -> iota := fun k i => if k = 0 then j0 else assign k i
    let newTube : (k : Nat) -> iota -> Tube (Tube.gridScale delta M k) E :=
      fun k R => if k = 0 then (Y j0).toTube.rescale (Tube.gridScale delta M k) else W k R
    have hnewzero : ∀ R, (newTube 0 R).toConvexSpaceBody =
        ((Y j0).toTube.rescale 1).toConvexSpaceBody := by
      intro R
      simpa only [newTube, if_pos rfl] using congrArg
        (fun r : NNReal => ((Y j0).toTube.rescale r).toConvexSpaceBody)
        (Tube.gridScale_zero delta M)
    let G : Tube.GridCoverSystem S (fun i => (Y i).toTube) M := {
      indexSet := fun k => S.image (newAssign k)
      assign := newAssign
      tube := newTube
      assign_mem := fun k hk i hi => Finset.mem_image.mpr ⟨i, hi, rfl⟩
      le_tube_assign := by
        intro k hk i hi
        by_cases hk0 : k = 0
        · subst k
          rw [hnewzero]
          exact (hcover 1 hM (hSF hi)).trans (hfirst_root i hi)
        · simpa only [newTube, newAssign, if_neg hk0] using hcover k hk (hSF hi)
      nested := by
        intro k hk i hi j hj hij
        by_cases hk0 : k = 0
        · simp only [newAssign, if_pos hk0]
        · simp only [newAssign, if_neg (show k + 1 ≠ 0 by omega)] at hij
          simpa only [newAssign, if_neg hk0] using hanested k (by omega) (hSF hi) (hSF hj) hij
      tube_nested := by
        intro k hk i hi
        by_cases hk0 : k = 0
        · subst k
          rw [hnewzero]
          simpa only [newTube, newAssign, Nat.zero_add, if_neg (by omega : 1 ≠ 0)] using hfirst_root i hi
        · simpa only [newTube, newAssign, if_neg hk0, if_neg (show k + 1 ≠ 0 by omega)] using
            hcross k (by omega) (hSF hi)
    }
    refine ⟨S, G, hSF, hSpos, hmassS.trans (mul_le_mul_right' hparentZero _),
      (fun k hk => rfl), ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi
      simpa only [G, newAssign, if_neg hMpos.ne'] using habottom (hSF hi)
    · intro i hi
      simpa only [G, newTube, if_neg hMpos.ne'] using hbottom (hSF hi)
    · intro k hk a ha b hb hab
      change a ∈ S.image (newAssign k) at ha
      change b ∈ S.image (newAssign k) at hb
      by_cases hk0 : k = 0
      · obtain ⟨i, hi, hir⟩ := Finset.mem_image.mp ha
        obtain ⟨j, hj, hjr⟩ := Finset.mem_image.mp hb
        simp only [newAssign, if_pos hk0] at hir hjr
        exact hir.symm.trans hjr
      · have hmem : ∀ R ∈ S.image (newAssign k), R ∈ parent k := by
          intro R hR
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hR
          simpa only [newAssign, if_neg hk0] using hamem k hk (hSF hi)
        apply hWinj k hk (hmem a ha) (hmem b hb)
        simpa only [G, newTube, if_neg hk0, Tube.gridScale] using hab
    · intro k hk V
      by_cases hk0 : k = 0
      · have hcard : (G.indexSet k).card <= 1 := by
          change (S.image (newAssign k)).card <= 1
          simp only [newAssign, if_pos hk0]
          rw [Finset.image_const (show S.Nonempty from ⟨j0, hj0⟩), Finset.card_singleton]
        exact (Finset.card_filter_le _ _).trans
          (hcard.trans (by norm_num [Tube.overlapConstBOTight, hdim]))
      · apply (Finset.card_le_card ?_).trans (hoverlap k hk V)
        intro R hR
        obtain ⟨hRmem, i, hi, hiW, hiV⟩ := Finset.mem_filter.mp hR
        obtain ⟨j, hj, hjR⟩ := Finset.mem_image.mp hRmem
        have hRparent : R ∈ parent k := by
          rw [← hjR]
          simpa only [newAssign, if_neg hk0] using hamem k hk (hSF hj)
        refine Finset.mem_filter.mpr ⟨hRparent, i, hSF hi, ?_, hiV⟩
        simpa only [G, newTube, if_neg hk0] using hiW
    · intro k hk R hR
      by_cases hk0 : k = 0
      · subst k
        have hbody := hnewzero R
        change (newTube 0 R).carrier ⊆ _
        rw [show (newTube 0 R).carrier = ((Y j0).toTube.rescale 1).carrier from congrArg ConvexSpaceBody.carrier hbody]
        exact hroot_ball (Y j0).toTube (hball j0 (hSF hj0))
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hR
        change (newTube k (newAssign k i)).carrier ⊆ _
        simp only [newTube, newAssign, if_neg hk0]
        have hrho : (Tube.gridScale delta M k : Real) <= 1 / 16 := by
          calc
            (Tube.gridScale delta M k : Real) <= (Tube.gridScale delta M 1 : Real) := by
              exact_mod_cast Tube.gridScale_antitone hdelta hdelta1.le M (by omega : 1 <= k)
            _ <= 1 / 16 := hrho1
        apply hsmall_node_ball (W k (assign k i)) hrho
        have hmidk := hmid k hk (hSF hi)
        have hmidnorm := Tube.norm_midpoint_le_of_subset_ball hdelta (Y i).toTube (hball i (hSF hi))
        have htri := norm_sub_le_norm_sub_add_norm_sub (W k (assign k i)).midpoint (Y i).toTube.midpoint 0
        rw [sub_zero, sub_zero,
          norm_sub_rev (W k (assign k i)).midpoint (Y i).toTube.midpoint] at htri
        linarith
  have hgrid_nested {delta : NNReal} {iota : Type uI} [DecidableEq iota]
      (S : Finset iota) (Y : iota -> ShadedTube delta E)
      (G : Tube.GridCoverSystem S (fun i => (Y i).toTube) M)
      (k l : Nat) (hkl : k <= l) (hl : l <= M) (i : iota) (hi : i ∈ S) :
      (G.tube l (G.assign l i)).toConvexSpaceBody <=
        (G.tube k (G.assign k i)).toConvexSpaceBody := by
    revert hl
    induction l, hkl using Nat.le_induction with
    | base => exact fun _ => le_rfl
    | succ l hkl ih =>
        intro hl
        exact (G.tube_nested l hl i hi).trans (ih (by omega))
  have hrange_tubes {delta : NNReal} (hdelta : 0 < delta) (hdelta1 : delta <= 1)
      {iota : Type uI} [DecidableEq iota]
      (S : Finset iota) (Y : iota -> ShadedTube delta E)
      (G : Tube.GridCoverSystem S (fun i => (Y i).toTube) M)
      (B : Finset iota) (hBS : B ⊆ S) (k l : Nat) (hkl : k < l) (hl : l <= M)
      (R : iota) (hR : R ∈ B.image (G.assign k)) :
      1 <= (actualDescendantsW95 B G.assign k l R).card ∧
      (actualDescendantsW95 B G.assign k l R).card <= S.card ∧
      1 <= actualRelativeFrostmanW95 B G.assign G.tube k l R ∧
      actualRelativeFrostmanW95 B G.assign G.tube k l R <=
        ((Tube.volume_le.C 3 : ENNReal) / (Tube.le_volume.c 3 : ENNReal)) *
          ((delta : ENNReal) ^ (2 : Nat))⁻¹ := by
    let D := actualDescendantsW95 B G.assign k l R
    obtain ⟨i0, hi0, hi0R⟩ := Finset.mem_image.mp hR
    have hD : D.Nonempty := by
      exact ⟨G.assign l i0, Finset.mem_image.mpr
        ⟨i0, Finset.mem_filter.mpr ⟨hi0, hi0R⟩, rfl⟩⟩
    have hDcard : D.card <= S.card :=
      Finset.card_image_le.trans ((Finset.card_filter_le _ _).trans (Finset.card_le_card hBS))
    have hcontained : ∀ Q ∈ D,
        (G.tube l Q).toConvexSpaceBody <= (G.tube k R).toConvexSpaceBody := by
      intro Q hQ
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hQ
      obtain ⟨hiB, hiR⟩ := Finset.mem_filter.mp hi
      have h := hgrid_nested S Y G k l hkl.le hl i (hBS hiB)
      rwa [hiR] at h
    obtain ⟨Q0, hQ0⟩ := hD
    let v := volume (G.tube l Q0).carrier
    have hvol : ∀ Q ∈ D, volume (G.tube l Q).carrier = v := by
      intro Q hQ
      exact Tube.volume_carrier_eq_volume_carrier (G.tube l Q) (G.tube l Q0)
    have hvl := Tube.volume_pos_and_lt_top (Tube.gridScale_pos hdelta M l)
      (Tube.gridScale_le_one hdelta1 M l) (G.tube l Q0)
    have hvk := Tube.volume_pos_and_lt_top (Tube.gridScale_pos hdelta M k)
      (Tube.gridScale_le_one hdelta1 M k) (G.tube k R)
    obtain ⟨hCFone, hCFvol⟩ := hfrostman_equal_volume D
      (fun Q => (G.tube l Q).toConvexSpaceBody) (G.tube k R).toConvexSpaceBody v
      ⟨Q0, hQ0⟩ hvol hvl.1.ne' hvl.2.ne hvk.1.ne' hvk.2.ne hcontained
    refine ⟨Finset.card_pos.mpr ⟨Q0, hQ0⟩, hDcard, hCFone, ?_⟩
    have hparentVolume : volume (G.tube k R).carrier <= (Tube.volume_le.C 3 : ENNReal) := by
      have hvolk := Tube.volume_le (Tube.gridScale_le_one hdelta1 M k) (G.tube k R)
      have hscale : ((Tube.gridScale delta M k : NNReal) : ENNReal) <= 1 := by
        exact_mod_cast Tube.gridScale_le_one hdelta1 M k
      have hpow : (((Tube.gridScale delta M k : NNReal) : ENNReal) ^ (2 : Nat)) <= 1 :=
        pow_le_one₀ bot_le hscale
      have hk : volume (G.tube k R).carrier <= (Tube.volume_le.C 3 : ENNReal) *
          (((Tube.gridScale delta M k : NNReal) : ENNReal) ^ (2 : Nat)) := by
        simpa only [hdim, Nat.reduceSub] using hvolk
      exact hk.trans (by simpa only [mul_one] using mul_le_mul_left' hpow (Tube.volume_le.C 3 : ENNReal))
    have hchildVolume : (Tube.le_volume.c 3 : ENNReal) * ((delta : ENNReal) ^ (2 : Nat)) <= v := by
      have hdeltascale : delta <= Tube.gridScale delta M l := by
        simpa only [Tube.gridScale_self delta (by omega : 0 < M)] using
          Tube.gridScale_antitone hdelta hdelta1 M hl
      have hscaleE : (delta : ENNReal) <= ((Tube.gridScale delta M l : NNReal) : ENNReal) := by
        exact_mod_cast hdeltascale
      have hvolmin := Tube.le_volume (G.tube l Q0)
      have hmin : (Tube.le_volume.c 3 : ENNReal) *
          (((Tube.gridScale delta M l : NNReal) : ENNReal) ^ (2 : Nat)) <= v := by
        simpa only [hdim, Nat.reduceSub] using hvolmin
      exact (mul_le_mul_left' (pow_le_pow_left' hscaleE 2) _).trans hmin
    have hc0 : (Tube.le_volume.c 3 : ENNReal) ≠ 0 :=
      (ENNReal.coe_pos.mpr (Tube.le_volume.c_pos 3)).ne'
    calc
      actualRelativeFrostmanW95 B G.assign G.tube k l R <= volume (G.tube k R).carrier / v := hCFvol
      _ <= (Tube.volume_le.C 3 : ENNReal) /
          ((Tube.le_volume.c 3 : ENNReal) * (delta : ENNReal) ^ (2 : Nat)) :=
        ENNReal.div_le_div hparentVolume hchildVolume
      _ = ((Tube.volume_le.C 3 : ENNReal) / (Tube.le_volume.c 3 : ENNReal)) *
          ((delta : ENNReal) ^ (2 : Nat))⁻¹ := by
        simp only [div_eq_mul_inv, ENNReal.mul_inv (Or.inl hc0) (Or.inl ENNReal.coe_ne_top), mul_assoc]
  let Ccan := Tube.uniformConst 3
  let Ctw : NNReal := max Cbase (Nat.ceil ((Ccan : Real) * Tube.activeLineConstant 3 1))
  have hCtwo : 2 <= Ccan := le_max_left _ _
  have hCone : 1 <= Ccan := (by norm_num : (1 : NNReal) <= 2).trans hCtwo
  have hbundle {delta : NNReal} (hdelta : 0 < delta) (hdelta1 : delta <= 1)
      (hdelta16 : delta <= (16 : NNReal) ^ (-(M : Real)))
      {iota : Type uI} [DecidableEq iota]
      (S A : Finset iota) (Y : iota -> ShadedTube delta E)
      (G : Tube.GridCoverSystem S (fun i => (Y i).toTube) M)
      (hAS : A ⊆ S)
      (hsurj : ∀ k, k <= M -> S.image (G.assign k) = G.indexSet k)
      (hbottom : ∀ i ∈ S, G.assign M i = i)
      (htubeBottom : ∀ i ∈ S, (G.tube M i).toConvexSpaceBody = (Y i).toConvexSpaceBody)
      (hinj : ∀ k, k <= M -> Set.InjOn (G.tube k) (G.indexSet k : Set iota))
      (hnice : ∀ k, k <= M -> ∀ V : Tube (Tube.gridScale delta M k) E,
        ((G.indexSet k).filter (fun R => ∃ i ∈ S,
          (Y i).toConvexSpaceBody <= (G.tube k R).toConvexSpaceBody ∧
          (Y i).toConvexSpaceBody <= V.toConvexSpaceBody)).card <= Tube.overlapConstBOTight 3)
      (hball : ∀ k, k <= M -> ∀ R ∈ G.indexSet k, (G.tube k R).carrier ⊆ Metric.closedBall 0 2)
      (hbottomBall : ∀ i ∈ A, (Y i).carrier ⊆ Metric.closedBall 0 1)
      (hcen : ∀ i ∈ A, centredTubeW94 (Y i).toTube)
      (hline : lineEssentiallyDistinctW94 A (fun i => (Y i).toTube) Cbase)
      (a b : Nat -> Nat -> Nat)
      (hbands : ∀ k l, k < l -> l <= M -> ∀ R ∈ A.image (G.assign k),
        (2 : ENNReal) ^ a k l <= (actualDescendantsW95 A G.assign k l R).card ∧
        ((actualDescendantsW95 A G.assign k l R).card : ENNReal) < 2 ^ (a k l + 1) ∧
        (2 : ENNReal) ^ b k l <= actualRelativeFrostmanW95 A G.assign G.tube k l R ∧
        actualRelativeFrostmanW95 A G.assign G.tube k l R < 2 ^ (b k l + 1)) :
      ∃ U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan,
        Nonempty (SourceRegularizedWorkingTowerW95 U Ctw (Ccan ^ 3)) := by
    let GA : Tube.GridCoverSystem A (fun i => (Y i).toTube) M := {
      indexSet := fun k => A.image (G.assign k)
      assign := G.assign
      tube := G.tube
      assign_mem := fun k hk i hi => Finset.mem_image.mpr ⟨i, hi, rfl⟩
      le_tube_assign := fun k hk i hi => G.le_tube_assign k hk i (hAS hi)
      nested := fun k hk i hi j hj hij => G.nested k hk i (hAS hi) j (hAS hj) hij
      tube_nested := fun k hk i hi => G.tube_nested k hk i (hAS hi)
    }
    have hmem : ∀ k, k <= M -> GA.indexSet k ⊆ G.indexSet k := by
      intro k hk
      rw [← hsurj k hk]
      exact Finset.image_subset_image hAS
    have hniceA : ∀ k, k <= M -> ∀ V : Tube (Tube.gridScale delta M k) E,
        ((GA.indexSet k).filter (fun R => ∃ i ∈ A,
          (Y i).toConvexSpaceBody <= (GA.tube k R).toConvexSpaceBody ∧
          (Y i).toConvexSpaceBody <= V.toConvexSpaceBody)).card <= Tube.overlapConstBOTight 3 := by
      intro k hk V
      apply (Finset.card_le_card ?_).trans (hnice k hk V)
      intro R hR
      obtain ⟨hR, i, hi, hiR, hiV⟩ := Finset.mem_filter.mp hR
      exact Finset.mem_filter.mpr ⟨hmem k hk hR, i, hAS hi, hiR, hiV⟩
    have hbottomIndex : GA.indexSet M = A := by
      change A.image (G.assign M) = A
      calc
        A.image (G.assign M) = A.image id := Finset.image_congr (fun i hi => hbottom i (hAS hi))
        _ = A := Finset.image_id
    have hfibreCover : ∀ k R, completeFibreW94 A (G.assign k) R = Tube.coverClass A (G.assign k) R := by
      intro k R
      ext i
      simp only [completeFibreW94, Tube.coverClass, Finset.mem_filter]
    have hbottomClass : ∀ R ∈ GA.indexSet M, Tube.coverClass A (GA.assign M) R = {R} := by
      intro R hR
      have hRA : R ∈ A := hbottomIndex ▸ hR
      ext i
      simp only [Tube.coverClass, Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hi, hir⟩
        exact (hbottom i (hAS hi)).symm.trans hir
      · intro hir
        subst i
        exact ⟨hRA, hbottom R (hAS hRA)⟩
    have hdescBottom : ∀ k R,
        actualDescendantsW95 A G.assign k M R = Tube.coverClass A (G.assign k) R := by
      intro k R
      have hclsSub : Tube.coverClass A (G.assign k) R ⊆ A := by
        letI : DecidablePred (fun i => G.assign k i = R) := fun _ => Classical.propDecidable _
        exact Finset.filter_subset _ _
      unfold actualDescendantsW95
      rw [hfibreCover]
      calc
        (Tube.coverClass A (G.assign k) R).image (G.assign M) =
            (Tube.coverClass A (G.assign k) R).image id := by
          apply Finset.image_congr
          intro i hi
          exact hbottom i (hAS (hclsSub hi))
        _ = _ := Finset.image_id
    let U : CanonicalProfileNetW87 A (fun i => (Y i).toTube) M Ccan := {
      cover := GA
      branchingN := fun k => if k < M then (2 : NNReal) ^ a k M else 1
      tube_injOn := fun k hk => (hinj k hk).mono (hmem k hk)
      boundedOverlap := by
        intro k hk V
        have hb : (((GA.indexSet k).filter (fun R => ∃ i ∈ A,
            (Y i).toConvexSpaceBody <= (GA.tube k R).toConvexSpaceBody ∧
            (Y i).toConvexSpaceBody <= V.toConvexSpaceBody)).card : NNReal) <=
            (Tube.overlapConstBOTight 3 : NNReal) := by exact_mod_cast hniceA k hk V
        exact hb.trans (le_max_right _ _)
      card_class_le := by
        intro k hk R hR
        by_cases hkM : k < M
        · have hb := (hbands k M hkM le_rfl R hR).2.1
          rw [hdescBottom] at hb
          have hb' : ((Tube.coverClass A (G.assign k) R).card : NNReal) <
              2 * (2 : NNReal) ^ a k M := by
            exact_mod_cast (show ((Tube.coverClass A (G.assign k) R).card : ENNReal) <
              2 * (2 : ENNReal) ^ a k M by simpa only [pow_succ, mul_comm] using hb)
          simpa only [if_pos hkM] using hb'.le.trans (mul_le_mul_right' hCtwo _)
        · have hkeq : k = M := by omega
          subst k
          simp only [hbottomClass R hR, Finset.card_singleton, Nat.cast_one, lt_self_iff_false,
            if_false, mul_one]
          exact hCone
      le_card_class := by
        intro k hk R hR
        by_cases hkM : k < M
        · have hb := (hbands k M hkM le_rfl R hR).1
          rw [hdescBottom] at hb
          have hb' : (2 : NNReal) ^ a k M <= (Tube.coverClass A (G.assign k) R).card := by
            exact_mod_cast hb
          simpa only [if_pos hkM, one_mul] using
            hb'.trans (show ((Tube.coverClass A (G.assign k) R).card : NNReal) <=
              Ccan * ((Tube.coverClass A (G.assign k) R).card : NNReal) by
                simpa only [one_mul] using mul_le_mul_right' hCone ((Tube.coverClass A (G.assign k) R).card : NNReal))
        · have hkeq : k = M := by omega
          subst k
          simp only [hbottomClass R hR, Finset.card_singleton, Nat.cast_one, lt_self_iff_false,
            if_false, mul_one]
          exact hCone
    }
    have hparentLine : ∀ k, k <= M ->
        lineEssentiallyDistinctW94 (U.cover.indexSet k) (U.cover.tube k) Ctw := by
      intro k hk o v hv
      by_cases hkM : k = M
      · subst k
        have hfilter : (U.cover.indexSet M).filter (fun R => liesInFiveDeltaLineTubeW94
            (U.cover.tube M R) o v) = A.filter (fun R => liesInFiveDeltaLineTubeW94 (Y R).toTube o v) := by
          change (GA.indexSet M).filter _ = _
          rw [hbottomIndex]
          apply Finset.filter_congr
          intro R hR
          unfold liesInFiveDeltaLineTubeW94
          have hb := congrArg ConvexSpaceBody.carrier (htubeBottom R (hAS hR))
          change (G.tube M R).carrier = (Y R).carrier at hb
          simp only [U, GA, hb, Tube.gridScale_self delta (by omega : 0 < M)]
        rw [hfilter]
        exact (hline o v hv).trans (le_max_left _ _)
      · have hklt : k < M := by omega
        have h4 : 4 * (delta : Real) <= Tube.gridScale delta M k := by
          have h16 := Tube.sixteen_mul_gridScale_le hdelta hdelta1 hdelta16 hklt le_rfl
          rw [Tube.gridScale_self delta (by omega : 0 < M)] at h16
          have h16r : 16 * (delta : Real) <= Tube.gridScale delta M k := by exact_mod_cast h16
          linarith [delta.2]
        have hcentred : ∀ i ∈ A, (Y i).toTube.IsCentred := by
          intro i hi
          have hc := hcen i hi
          simpa only [centredTubeW94, Tube.IsCentred, Tube.center, midpoint_eq_smul_add,
            Tube.midpoint, invOf_eq_inv, one_div] using hc
        have hlineNat := Tube.isLineEssDistinct_activeIndexSet_of_centred hdelta U hcentred
          (by norm_num : (0 : Real) <= 1)
          (fun i hi => Tube.norm_midpoint_le_of_subset_ball hdelta (Y i).toTube (hbottomBall i hi)) hk h4 o v hv
        have hactive : U.cover.activeIndexSet k = U.cover.indexSet k := by
          ext R
          rw [U.cover.mem_activeIndexSet]
          exact ⟨And.left, fun hR => ⟨hR, Finset.mem_image.mp hR⟩⟩
        rw [hactive] at hlineNat
        have hsub : (U.cover.indexSet k).filter (fun R => liesInFiveDeltaLineTubeW94 (U.cover.tube k R) o v) ⊆
            (U.cover.indexSet k).filter (fun R => (U.cover.tube k R).carrier ⊆
              VeryNotSticky.lineNbhd o v (5 * ((Tube.gridScale delta M k : NNReal) : Real))) := by
          intro R hR
          obtain ⟨hR, hRline⟩ := Finset.mem_filter.mp hR
          refine Finset.mem_filter.mpr ⟨hR, ?_⟩
          intro x hx
          obtain ⟨t, ht⟩ := hRline x hx
          exact VeryNotSticky.mem_lineNbhd_of_dist_le t ht
        have hcount := (Finset.card_le_card hsub).trans hlineNat
        have hcountNN : (((U.cover.indexSet k).filter
            (fun R => liesInFiveDeltaLineTubeW94 (U.cover.tube k R) o v)).card : NNReal) <=
            (Nat.ceil ((Ccan : Real) * Tube.activeLineConstant 3 1) : NNReal) := by
          simpa only [hdim] using (show _ <= (Nat.ceil ((Ccan : Real) *
            Tube.activeLineConstant (Module.finrank Real E) 1) : NNReal) by exact_mod_cast hcount)
        exact hcountNN.trans (le_max_right _ _)
    refine ⟨U, ⟨{
      surjective := fun k hk => rfl
      bottom_index := hbottomIndex
      bottom_assign := fun i hi => hbottom i (hAS hi)
      bottom_tube := fun i hi => htubeBottom i (hAS hi)
      nice := by simpa only [Tube.UniformTubeSet.Nice, hdim] using hniceA
      parent_ball := fun k hk R hR => hball k hk R (hmem k hk hR)
      parent_line_ed := hparentLine
      geometric_count := by
        intro k hk R hR
        calc
          ((exactTubeCellW87 A (fun i => (Y i).toTube) (U.cover.tube k R)).card : NNReal) <=
              Ccan ^ 2 * U.branchingN k := U.card_familyIn_le hk R
          _ <= Ccan ^ 2 * (Ccan * ((Tube.coverClass A (U.cover.assign k) R).card : NNReal)) :=
            mul_le_mul_left' (U.le_card_class k hk R hR) _
          _ = Ccan ^ 3 * ((completeFibreW94 A (U.cover.assign k) R).card : NNReal) := by
            change Ccan ^ 2 * (Ccan * ((Tube.coverClass A (G.assign k) R).card : NNReal)) =
              Ccan ^ 3 * ((completeFibreW94 A (G.assign k) R).card : NNReal)
            rw [hfibreCover]
            ring
      countBand := fun k l => (2 : NNReal) ^ a k l
      countBand_pos := fun k l hkl hl => pow_pos (by norm_num) _
      count_lower := by
        intro k l hkl hl R hR
        exact_mod_cast (hbands k l hkl hl R hR).1
      count_upper := by
        intro k l hkl hl R hR
        have h := (hbands k l hkl hl R hR).2.1
        exact_mod_cast (show ((actualDescendantsW95 A G.assign k l R).card : ENNReal) <
          2 * (2 : ENNReal) ^ a k l by simpa only [pow_succ, mul_comm] using h)
      frostmanBand := fun k l => (2 : ENNReal) ^ b k l
      frostmanBand_pos := fun k l hkl hl => by positivity
      frostmanBand_finite := fun k l hkl hl => by finiteness
      frostman_lower := fun k l hkl hl R hR => (hbands k l hkl hl R hR).2.2.1
      frostman_upper := by
        intro k l hkl hl R hR
        simpa only [pow_succ, mul_comm] using (hbands k l hkl hl R hR).2.2.2
    }⟩⟩
  let N0 : NNReal := 5 ^ (6 : Nat) * Cbase
  let Hc : NNReal := Tube.volume_le.C 3 / Tube.le_volume.c 3
  let Ccut : NNReal := max 1 (max N0 Hc)
  let Q : Nat := 2 * M * M
  let Croot : NNReal := 641 ^ (6 : Nat) * 4 ^ (6 : Nat)
  let Ctower : NNReal := max 1 (72 * (2 * Cbase) * Croot * 7 ^ Q)
  let delta0 : NNReal := min (1 / 2) (min ((16 : NNReal) ^ (-(M : Real))) Ccut⁻¹)
  have hcut1 : 1 <= Ccut := le_max_left _ _
  have hcutpos : 0 < Ccut := zero_lt_one.trans_le hcut1
  have hdelta0pos : 0 < delta0 := by
    dsimp [delta0]
    exact lt_min (by norm_num) (lt_min (by positivity) (inv_pos.mpr hcutpos))
  have hdelta0half : delta0 <= 1 / 2 := min_le_left _ _
  have hdelta01 : delta0 < 1 := hdelta0half.trans_lt (by norm_num)
  refine ⟨Ccan, Ctw, Ccan ^ 3, Ctower, Q + 1, delta0,
    hCone, hCbase.trans (le_max_left _ _), one_le_pow₀ hCone,
    le_max_left _ _, by omega, hdelta0pos, hdelta01, ?_⟩
  intro delta hdelta hsmall iota inst F Y hball hcen hline hmass
  have hd0 : 0 < (delta : Real) := hdelta
  have hd1 : delta < 1 := hsmall.trans hdelta01
  have hd1r : (delta : Real) <= 1 := hd1.le
  have hdhalf : delta <= 1 / 2 := hsmall.le.trans hdelta0half
  have hd16 : delta <= (16 : NNReal) ^ (-(M : Real)) :=
    hsmall.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hdcut : delta <= Ccut⁻¹ :=
    hsmall.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hcoeff : (Ccut : Real) <= (delta : Real)⁻¹ := by
    have hc0 : 0 < (Ccut : Real) := hcutpos
    have hd : (delta : Real) <= 1 / (Ccut : Real) := by
      simpa only [one_div] using (show (delta : Real) <= (Ccut : Real)⁻¹ by exact_mod_cast hdcut)
    have hprod := (le_div_iff₀ hc0).mp hd
    rw [← one_div, le_div_iff₀ hd0]
    nlinarith
  have hN0 : (N0 : Real) <= (delta : Real) ^ (-(1 : Real)) := by
    have hN : N0 <= Ccut := (le_max_left _ _).trans (le_max_right _ _)
    simpa only [Real.rpow_neg_one] using (show (N0 : Real) <= (delta : Real)⁻¹ from
      (show (N0 : Real) <= Ccut by exact_mod_cast hN).trans hcoeff)
  have hHc : (Hc : Real) <= (delta : Real) ^ (-(1 : Real)) := by
    have hH : Hc <= Ccut := (le_max_right _ _).trans (le_max_right _ _)
    simpa only [Real.rpow_neg_one] using (show (Hc : Real) <= (delta : Real)⁻¹ from
      (show (Hc : Real) <= Ccut by exact_mod_cast hH).trans hcoeff)
  have hcard7 : (F.card : Real) <= (delta : Real) ^ (-(7 : Real)) := by
    calc
      (F.card : Real) <= (N0 : Real) * (delta : Real) ^ (-(6 : Real)) :=
        hinput_card hdelta hd1.le F (fun i => (Y i).toTube) hball hline
      _ <= (delta : Real) ^ (-(1 : Real)) * (delta : Real) ^ (-(6 : Real)) :=
        mul_le_mul_of_nonneg_right hN0 (Real.rpow_nonneg delta.2 _)
      _ = (delta : Real) ^ (-(7 : Real)) := by rw [← Real.rpow_add hd0]; norm_num
  have hCFreal : (Hc : Real) * ((delta : Real) ^ (2 : Nat))⁻¹ <=
      (delta : Real) ^ (-(7 : Real)) := by
    calc
      (Hc : Real) * ((delta : Real) ^ (2 : Nat))⁻¹ =
          (Hc : Real) * (delta : Real) ^ (-(2 : Real)) := by
        exact congrArg (fun x : Real => (Hc : Real) * x)
          (by simpa only [Real.rpow_two] using (Real.rpow_neg hd0.le 2).symm)
      _ <= (delta : Real) ^ (-(1 : Real)) * (delta : Real) ^ (-(2 : Real)) :=
        mul_le_mul_of_nonneg_right hHc (Real.rpow_nonneg delta.2 _)
      _ = (delta : Real) ^ (-(3 : Real)) := by rw [← Real.rpow_add hd0]; norm_num
      _ <= (delta : Real) ^ (-(7 : Real)) :=
        Real.rpow_le_rpow_of_exponent_ge hd0 hd1r (by norm_num)
  let H : ENNReal := ENNReal.ofReal ((delta : Real) ^ (-(7 : Real)))
  have hHreal : 1 <= (delta : Real) ^ (-(7 : Real)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hd0 hd1r (by norm_num)
  have hHone : 1 <= H := by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hHreal
  have hHt : H < ⊤ := ENNReal.ofReal_lt_top
  have hcardH : (F.card : ENNReal) <= H := by
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hcard7
  have hc0 : Tube.le_volume.c 3 ≠ 0 := (Tube.le_volume.c_pos 3).ne'
  have hdE0 : (delta : ENNReal) ≠ 0 := (ENNReal.coe_pos.mpr hdelta).ne'
  have hCFH : ((Tube.volume_le.C 3 : ENNReal) / (Tube.le_volume.c 3 : ENNReal)) *
      ((delta : ENNReal) ^ (2 : Nat))⁻¹ <= H := by
    rw [← ENNReal.coe_div hc0]
    change (Hc : ENNReal) * ((delta : ENNReal) ^ (2 : Nat))⁻¹ <= H
    apply (ENNReal.toReal_le_toReal (by simp [ENNReal.mul_ne_top, hdE0]) hHt.ne).mp
    simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_inv,
      ENNReal.toReal_pow, H, ENNReal.toReal_ofReal (zero_le_one.trans hHreal)] using hCFreal
  obtain ⟨I, hIF, hI, hIinj, hImass, hpayI⟩ := hweighted_injective hdelta F Y hline hmass
  obtain ⟨S, G, hSI, hSmass, hpayS, hsurj, hbottom, htubeBottom, hinj, hnice, hparentBall⟩ :=
    hlocalize hdelta hd1 hd16 I Y hIinj (fun i hi => hball i (hIF hi)) hImass
  have hSF : S ⊆ F := hSI.trans hIF
  have hrange : ∀ B ⊆ S, ∀ k l, k < l -> l <= M -> ∀ R ∈ B.image (G.assign k),
      1 <= (actualDescendantsW95 B G.assign k l R).card ∧
      ((actualDescendantsW95 B G.assign k l R).card : ENNReal) <= H ∧
      1 <= actualRelativeFrostmanW95 B G.assign G.tube k l R ∧
      actualRelativeFrostmanW95 B G.assign G.tube k l R <= H := by
    intro B hBS k l hkl hl R hR
    obtain ⟨hcount1, hcountS, hCF1, hCFmax⟩ := hrange_tubes hdelta hd1.le S Y G B hBS k l hkl hl R hR
    refine ⟨hcount1, ?_, hCF1, hCFmax.trans hCFH⟩
    exact (show ((actualDescendantsW95 B G.assign k l R).card : ENNReal) <= F.card by
      exact_mod_cast hcountS.trans (Finset.card_le_card hSF)).trans hcardH
  obtain ⟨A, a, b, hAS, hAmass, hpayA, hbands⟩ := hregularize S Y G H hHone hHt hrange hSmass
  have hAF : A ⊆ F := hAS.trans hSF
  have hAline : lineEssentiallyDistinctW94 A (fun i => (Y i).toTube) Cbase := by
    intro o v hv
    exact (show ((A.filter (fun i => liesInFiveDeltaLineTubeW94 (Y i).toTube o v)).card : NNReal) <=
      (F.filter (fun i => liesInFiveDeltaLineTubeW94 (Y i).toTube o v)).card by
        exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ hAF)).trans (hline o v hv)
  obtain ⟨U, hU⟩ := hbundle hdelta hd1.le hd16 S A Y G hAS hsurj hbottom htubeBottom hinj
    (by simpa only [hdim] using hnice) hparentBall
    (fun i hi => hball i (hAF hi)) (fun i hi => hcen i (hAF hi)) hAline a b hbands
  have hAnonempty : A.Nonempty := by
    by_contra h
    simpa only [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty, lt_self_iff_false] using hAmass
  refine ⟨A, U, hAnonempty, hAF, ?_, hU⟩
  let t : Real := Real.log (1 / (delta : Real)) / Real.log 2
  let L : Real := 2 + t
  have ht0 : 0 <= t := by
    apply div_nonneg (Real.log_nonneg ?_) (Real.log_nonneg (by norm_num))
    exact (le_div_iff₀ hd0).mpr (by simpa only [one_mul] using hd1r)
  have hLpos : 0 < L := by dsimp [L]; linarith
  have hlogH : Real.log H.toReal / Real.log 2 = 7 * t := by
    rw [show H.toReal = (delta : Real) ^ (-(7 : Real)) from ENNReal.toReal_ofReal (zero_le_one.trans hHreal),
      Real.log_rpow hd0]
    dsimp [t]
    rw [Real.log_div one_ne_zero hd0.ne', Real.log_one]
    ring
  have hlenReal : (dyadicRangeLengthW95 H : Real) <= 7 * L := by
    have hfloor := Nat.floor_le (show 0 <= Real.log H.toReal / Real.log 2 by rw [hlogH]; positivity)
    dsimp only [dyadicRangeLengthW95]
    push_cast
    rw [hlogH] at hfloor
    rw [hlogH]
    dsimp [L]
    linarith
  have hlen : (dyadicRangeLengthW95 H : ENNReal) <= 7 * ENNReal.ofReal L := by
    have h := ENNReal.ofReal_le_ofReal hlenReal
    simpa only [ENNReal.ofReal_natCast, ENNReal.ofReal_mul (by norm_num : (0 : Real) <= 7),
      ENNReal.ofReal_ofNat] using h
  have hband : bandLoss F.card <= 72 * ENNReal.ofReal L := by
    apply (bandLoss_le_ofReal_logb hdelta hdhalf hcard7).trans
    have h : 72 * Real.logb 2 (1 / (delta : Real)) <= 72 * L := by
      dsimp [L, t]
      rw [Real.logb]
      linarith
    simpa only [ENNReal.ofReal_mul (by norm_num : (0 : Real) <= 72), ENNReal.ofReal_ofNat] using
      ENNReal.ofReal_le_ofReal h
  have hCpay : (72 : ENNReal) * (2 * (Cbase : ENNReal)) * (Croot : ENNReal) * 7 ^ Q <= Ctower := by
    exact_mod_cast (show (72 : NNReal) * (2 * Cbase) * Croot * 7 ^ Q <= Ctower from le_max_right _ _)
  have hcoeffpay : bandLoss F.card * (2 * (Cbase : ENNReal)) * (Croot : ENNReal) *
      (dyadicRangeLengthW95 H : ENNReal) ^ Q <=
        (Ctower : ENNReal) * ENNReal.ofReal (L ^ (Q + 1)) := by
    calc
      bandLoss F.card * (2 * (Cbase : ENNReal)) * (Croot : ENNReal) *
          (dyadicRangeLengthW95 H : ENNReal) ^ Q <=
          (72 * ENNReal.ofReal L) * (2 * (Cbase : ENNReal)) * (Croot : ENNReal) *
            (7 * ENNReal.ofReal L) ^ Q := by gcongr
      _ = ((72 : ENNReal) * (2 * (Cbase : ENNReal)) * (Croot : ENNReal) * 7 ^ Q) *
          (ENNReal.ofReal L) ^ (Q + 1) := by rw [mul_pow, pow_succ]; ring
      _ <= (Ctower : ENNReal) * (ENNReal.ofReal L) ^ (Q + 1) := mul_le_mul_right' hCpay _
      _ = (Ctower : ENNReal) * ENNReal.ofReal (L ^ (Q + 1)) := by rw [ENNReal.ofReal_pow hLpos.le]
  have hpaid : (∑ i ∈ F, volume (Y i).shade) <=
      ((Ctower : ENNReal) * ENNReal.ofReal (L ^ (Q + 1))) * ∑ i ∈ A, volume (Y i).shade := by
    calc
      (∑ i ∈ F, volume (Y i).shade) <=
          (bandLoss F.card * (2 * (Cbase : ENNReal))) *
            ((Croot : ENNReal) * ((dyadicRangeLengthW95 H : ENNReal) ^ Q * ∑ i ∈ A, volume (Y i).shade)) :=
        hpayI.trans (mul_le_mul_left' (hpayS.trans (mul_le_mul_left' hpayA _)) _)
      _ = (bandLoss F.card * (2 * (Cbase : ENNReal)) * (Croot : ENNReal) *
          (dyadicRangeLengthW95 H : ENNReal) ^ Q) * ∑ i ∈ A, volume (Y i).shade := by ring
      _ <= _ := mul_le_mul_right' hcoeffpay _
  have hCtower0 : (Ctower : ENNReal) ≠ 0 := by
    exact (ENNReal.coe_pos.mpr (zero_lt_one.trans_le (le_max_left _ _))).ne'
  have hdenom0 : (Ctower : ENNReal) * ENNReal.ofReal (L ^ (Q + 1)) ≠ 0 := by
    exact mul_ne_zero hCtower0 (ENNReal.ofReal_pos.mpr (pow_pos hLpos _)).ne'
  exact (ENNReal.inv_mul_le_iff hdenom0 (by finiteness)).mpr hpaid

end

end Kakeya.ml1Boot.TrialRestartW94
