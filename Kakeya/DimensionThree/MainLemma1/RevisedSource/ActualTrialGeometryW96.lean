module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.TrialGeometryEntryW96
public import Kakeya.DimensionThree.MainLemma1.Rescaling.Pigeonhole
public import Kakeya.DimensionThree.MainLemma1.Factoring

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody
open scoped ENNReal NNReal

namespace Kakeya.ml1Boot.TrialRestartW94

open RevisedLiteralProfileInterfaceFormalizerW87

noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

universe uE uI uP uQ

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]

/-- Literal detailed-source carrier lemma, with the actual attached unit core. -/
theorem exists_centred_attached_carrier_w96
    (hdim : Module.finrank Real E = 3)
    {iota : Type uI} [DecidableEq iota] {d a b : NNReal}
    (hd : 0 < d) (hdb : d <= b) (hb : b <= 1 / 16)
    (q : Finset iota) (T : iota -> Tube d E) (hq : q.Nonempty)
    (hcentred : ∀ i ∈ q, (T i).IsCentred)
    (hball : ∀ i ∈ q, (T i).carrier ⊆ Metric.closedBall 0 1)
    (o u : E) (hu : ‖u‖ = 1) (rhoc : Real) (hrhoc : rhoc < 3 * (b : Real) / 8)
    (henvelope : (q.convexHull_biUnion (fun i => (T i).toConvexSpaceBody)).carrier ⊆
      VeryNotSticky.lineNbhd o u rhoc)
    (hvolume : (2 : ENNReal)⁻¹ ^ (9 : Nat) * (a : ENNReal) * (b : ENNReal) <=
      volume (q.convexHull_biUnion (fun i => (T i).toConvexSpaceBody)).carrier) :
    ∃ i0 ∈ q, ((T i0).rescale (16 * b)).IsCentred ∧
      ((T i0).rescale (16 * b)).x = (T i0).x ∧
      ((T i0).rescale (16 * b)).y = (T i0).y ∧
      q.convexHull_biUnion (fun i => (T i).toConvexSpaceBody) <=
        ((T i0).rescale (16 * b)).toConvexSpaceBody ∧
      volume ((T i0).rescale (16 * b)).carrier <=
        (2 : ENNReal) ^ (12 : Nat) * (b : ENNReal) ^ (2 : Nat) := by
  classical
  obtain ⟨i0, hi0⟩ := hq
  have hcover : ∀ (R0 : Real), 0 <= R0 ->
      (q.convexHull_biUnion (fun i => (T i).toConvexSpaceBody)).carrier ⊆
        VeryNotSticky.lineNbhd o u R0 ->
      ∀ (r : NNReal), 26 * R0 + (d : Real) <= (r : Real) ->
        q.convexHull_biUnion (fun i => (T i).toConvexSpaceBody) <=
          ((T i0).rescale r).toConvexSpaceBody := by
    intro R0 hR0 henv r hscale
    have hcore : ∀ i ∈ q, ∀ z ∈ segment Real (T i).x (T i).y,
        Tube.lineDist o u z <= R0 := by
      intro i hi z hz
      apply (Tube.mem_cthickening_line_iff hu hR0).mp
      rw [← VeryNotSticky.lineNbhd_eq_cthickening_range]
      exact henv (Finset.le_convexHull_biUnion _ hi ((T i).mem_carrier_of_mem_segment hz))
    have hparams : ∀ i ∈ q, ∃ sign : Real, (sign = 1 ∨ sign = -1) ∧
        ‖(T i).direction - sign • u‖ <= 4 * R0 ∧
        ‖(T i).midpoint - Tube.lineFoot o u‖ <= 5 * R0 := by
      intro i hi
      obtain ⟨sign, hsign, hdir⟩ := Tube.exists_sign_norm_direction_sub_le (T i) hu
        (hcore i hi _ (left_mem_segment _ _ _)) (hcore i hi _ (right_mem_segment _ _ _))
      have hmidmem : (T i).midpoint ∈ segment Real (T i).x (T i).y := by
        simpa using (T i).midpoint_add_smul_mem_segment (t := 0) (by norm_num)
      have hmid : ‖(T i).midpoint‖ <= 1 := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using
          hball i hi ((T i).mem_carrier_of_mem_segment hmidmem)
      refine ⟨sign, hsign, hdir, ?_⟩
      have hmidline := hcore i hi _ hmidmem
      have hm := Tube.norm_midpoint_sub_lineFoot_le_of_isCentred (T i) (hcentred i hi)
        hu hmidline hsign hdir
      nlinarith
    obtain ⟨s0, hs0, hd0, hm0⟩ := hparams i0 hi0
    apply (Finset.Nonempty.convexHull_biUnion_le_iff ⟨i0, hi0⟩ _ _).mpr
    intro i hi z hz
    obtain ⟨si, hsi, hdi, hmi⟩ := hparams i hi
    have hsiAbs : |si| = 1 := by rcases hsi with rfl | rfl <;> norm_num
    have hs0Abs : |s0| = 1 := by rcases hs0 with rfl | rfl <;> norm_num
    have hs0sq : s0 * s0 = 1 := by rcases hs0 with rfl | rfl <;> norm_num
    have hsigAbs : |si * s0| = 1 := by rw [abs_mul, hsiAbs, hs0Abs, one_mul]
    have hmiddist : ‖(T i).midpoint - (T i0).midpoint‖ <= 10 * R0 := by
      calc
        _ <= ‖(T i).midpoint - Tube.lineFoot o u‖ +
            ‖(T i0).midpoint - Tube.lineFoot o u‖ := by
          simpa only [norm_sub_rev (Tube.lineFoot o u) (T i0).midpoint] using
            norm_sub_le_norm_sub_add_norm_sub (T i).midpoint (Tube.lineFoot o u) (T i0).midpoint
        _ <= _ := by linarith
    have hdirdist : ‖(T i).direction - (si * s0) • (T i0).direction‖ <= 8 * R0 := by
      have hid : (T i).direction - (si * s0) • (T i0).direction =
          ((T i).direction - si • u) - (si * s0) • ((T i0).direction - s0 • u) := by
        rcases hs0 with rfl | rfl <;> simp <;> module
      rw [hid]
      calc
        _ <= ‖(T i).direction - si • u‖ + ‖(si * s0) • ((T i0).direction - s0 • u)‖ :=
          norm_sub_le _ _
        _ <= _ := by rw [norm_smul, Real.norm_eq_abs, hsigAbs, one_mul]; linarith
    change z ∈ (T i).carrier at hz
    change z ∈ ((T i0).rescale r).carrier
    rw [(T i).carrier_eq] at hz
    obtain ⟨x, hx, hzx⟩ := Set.mem_iUnion₂.mp hz
    obtain ⟨t, ht, rfl⟩ := (T i).exists_param_of_mem_segment hx
    let y := (T i0).midpoint + (t * (si * s0)) • (T i0).direction
    have hy : y ∈ segment Real (T i0).x (T i0).y := by
      apply (T i0).midpoint_add_smul_mem_segment
      rw [abs_mul, hsigAbs, mul_one]
      exact ht
    have hxy : dist ((T i).midpoint + t • (T i).direction) y <= 14 * R0 := by
      rw [dist_eq_norm]
      have hid : (T i).midpoint + t • (T i).direction - y =
          ((T i).midpoint - (T i0).midpoint) +
            t • ((T i).direction - (si * s0) • (T i0).direction) := by dsimp [y]; module
      rw [hid]
      calc
        _ <= ‖(T i).midpoint - (T i0).midpoint‖ +
            ‖t • ((T i).direction - (si * s0) • (T i0).direction)‖ := norm_add_le _ _
        _ <= _ := by
          rw [norm_smul, Real.norm_eq_abs]
          nlinarith [norm_nonneg ((T i).direction - (si * s0) • (T i0).direction)]
    rw [((T i0).rescale r).carrier_eq]
    apply Set.mem_iUnion₂.mpr ⟨y, hy, ?_⟩
    apply Metric.mem_closedBall.mpr
    exact (dist_triangle z ((T i).midpoint + t • (T i).direction) y).trans
      ((add_le_add (Metric.mem_closedBall.mp hzx) hxy).trans (by linarith))
  have hb0 : (0 : Real) < b := by exact_mod_cast hd.trans_le hdb
  have henv : (q.convexHull_biUnion (fun i => (T i).toConvexSpaceBody)).carrier ⊆
      VeryNotSticky.lineNbhd o u (3 * (b : Real) / 8) :=
    henvelope.trans (Metric.cthickening_mono hrhoc.le _)
  refine ⟨i0, hi0, hcentred i0 hi0, rfl, rfl, hcover _ (by positivity) henv _ ?_, ?_⟩
  · have hdbR : (d : Real) <= b := by exact_mod_cast hdb
    push_cast
    linarith
  · have hsmall : 16 * b <= (1 : NNReal) := by nlinarith
    have hv := Tube.volume_le hsmall ((T i0).rescale (16 * b))
    rw [hdim] at hv
    norm_num [Tube.volume_le.C, mul_pow, ← mul_assoc] at hv ⊢
    exact hv

def trialComparableCarrierScaleW96 (Cw : NNReal) : NNReal := 52 * Cw + 1

/-- Internal comparable-body version. Its radius is not the source's literal 16b. -/
theorem exists_comparable_centred_attached_carrier_w96
    (hdim : Module.finrank Real E = 3)
    {iota : Type uI} [DecidableEq iota] {d a b : NNReal}
    (hd : 0 < d) (hda : d <= a) (hab : a <= b)
    (Cw : NNReal) (hCw : 1 <= Cw)
    (hsmall : trialComparableCarrierScaleW96 Cw * b <= 1)
    (q : Finset iota) (T : iota -> Tube d E) (hq : q.Nonempty)
    (hcentred : ∀ i ∈ q, (T i).IsCentred)
    (hball : ∀ i ∈ q, (T i).carrier ⊆ Metric.closedBall 0 1)
    (hdims : IsPlankOfDimensions Cw a b
      (q.convexHull_biUnion (fun i => (T i).toConvexSpaceBody))) :
    ∃ o u : E, ‖u‖ = 1 ∧
      (q.convexHull_biUnion (fun i => (T i).toConvexSpaceBody)).carrier ⊆
        VeryNotSticky.lineNbhd o u (2 * (Cw : Real) * (b : Real)) ∧
      ∃ i0 ∈ q,
        ((T i0).rescale (trialComparableCarrierScaleW96 Cw * b)).IsCentred ∧
        ((T i0).rescale (trialComparableCarrierScaleW96 Cw * b)).x = (T i0).x ∧
        ((T i0).rescale (trialComparableCarrierScaleW96 Cw * b)).y = (T i0).y ∧
        q.convexHull_biUnion (fun i => (T i).toConvexSpaceBody) <=
          ((T i0).rescale (trialComparableCarrierScaleW96 Cw * b)).toConvexSpaceBody ∧
        volume ((T i0).rescale (trialComparableCarrierScaleW96 Cw * b)).carrier <=
          (Tube.volume_le.C 3 : ENNReal) *
            ((trialComparableCarrierScaleW96 Cw : ENNReal) * (b : ENNReal)) ^ (2 : Nat) := by
  classical
  obtain ⟨i0, hi0⟩ := hq
  let W := q.convexHull_biUnion (fun i => (T i).toConvexSpaceBody)
  let Pr := outerPrism hdim W.isCompact W.nonempty
  let o := Pr.center
  let u := Pr.basis 0
  have hu : ‖u‖ = 1 := Pr.basis.orthonormal.norm_eq_one 0
  have hwidth : ∀ k : Fin 3, k = 1 ∨ k = 2 ->
      (Pr.thicknesses k : Real) <= (Cw : Real) * b := by
    intro k hk
    have he : Metric.ethickness Real W.carrier k <= (Cw : ENNReal) * b := by
      rcases hk with rfl | rfl
      · exact hdims.2.1.2
      · exact hdims.2.2.2.trans (mul_le_mul' le_rfl (by exact_mod_cast hab))
    have hre := ENNReal.toReal_mono (by finiteness) he
    rw [Metric.ethickness_thickness' (s := W.carrier) W.isCompact.isBounded] at hre
    simp only [ENNReal.toReal_mul, ENNReal.coe_toReal,
      ENNReal.toReal_ofReal (Metric.thickness_nonneg _ _)] at hre
    rw [show Pr = outerPrism hdim W.isCompact W.nonempty from rfl, outerPrism.thicknesses_eq]
    change Metric.thickness Real W.carrier k <= _
    exact hre
  have henv : W.carrier ⊆ VeryNotSticky.lineNbhd o u (2 * (Cw : Real) * (b : Real)) := by
    intro z hz
    have hzPr := outerPrism.self_subset hdim W.isCompact W.nonempty hz
    have hdist := dist_prism_transverse_le (n := 2) Pr hzPr
    have hsum : (∑ k ∈ Finset.univ.erase (0 : Fin 3), (Pr.thicknesses k : Real)) =
        (Pr.thicknesses 1 : Real) + Pr.thicknesses 2 := by
      rw [Finset.sum_erase_eq_sub (Finset.mem_univ (0 : Fin 3)), Fin.sum_univ_three]
      abel
    rw [hsum] at hdist
    apply VeryNotSticky.mem_lineNbhd_of_dist_le (Pr.basis.repr (z -ᵥ Pr.center) 0)
    have hw1 := hwidth 1 (Or.inl rfl)
    have hw2 := hwidth 2 (Or.inr rfl)
    change dist z (Pr.center + _ • Pr.basis 0) <= _
    simp only [vadd_eq_add, add_comm] at hdist
    linarith
  have hcover : ∀ (R0 : Real), 0 <= R0 ->
      (q.convexHull_biUnion (fun i => (T i).toConvexSpaceBody)).carrier ⊆
        VeryNotSticky.lineNbhd o u R0 ->
      ∀ (r : NNReal), 26 * R0 + (d : Real) <= (r : Real) ->
        q.convexHull_biUnion (fun i => (T i).toConvexSpaceBody) <=
          ((T i0).rescale r).toConvexSpaceBody := by
    intro R0 hR0 henv r hscale
    have hcore : ∀ i ∈ q, ∀ z ∈ segment Real (T i).x (T i).y,
        Tube.lineDist o u z <= R0 := by
      intro i hi z hz
      apply (Tube.mem_cthickening_line_iff hu hR0).mp
      rw [← VeryNotSticky.lineNbhd_eq_cthickening_range]
      exact henv (Finset.le_convexHull_biUnion _ hi ((T i).mem_carrier_of_mem_segment hz))
    have hparams : ∀ i ∈ q, ∃ sign : Real, (sign = 1 ∨ sign = -1) ∧
        ‖(T i).direction - sign • u‖ <= 4 * R0 ∧
        ‖(T i).midpoint - Tube.lineFoot o u‖ <= 5 * R0 := by
      intro i hi
      obtain ⟨sign, hsign, hdir⟩ := Tube.exists_sign_norm_direction_sub_le (T i) hu
        (hcore i hi _ (left_mem_segment _ _ _)) (hcore i hi _ (right_mem_segment _ _ _))
      have hmidmem : (T i).midpoint ∈ segment Real (T i).x (T i).y := by
        simpa using (T i).midpoint_add_smul_mem_segment (t := 0) (by norm_num)
      have hmid : ‖(T i).midpoint‖ <= 1 := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using
          hball i hi ((T i).mem_carrier_of_mem_segment hmidmem)
      refine ⟨sign, hsign, hdir, ?_⟩
      have hmidline := hcore i hi _ hmidmem
      have hm := Tube.norm_midpoint_sub_lineFoot_le_of_isCentred (T i) (hcentred i hi)
        hu hmidline hsign hdir
      nlinarith
    obtain ⟨s0, hs0, hd0, hm0⟩ := hparams i0 hi0
    apply (Finset.Nonempty.convexHull_biUnion_le_iff ⟨i0, hi0⟩ _ _).mpr
    intro i hi z hz
    obtain ⟨si, hsi, hdi, hmi⟩ := hparams i hi
    have hsiAbs : |si| = 1 := by rcases hsi with rfl | rfl <;> norm_num
    have hs0Abs : |s0| = 1 := by rcases hs0 with rfl | rfl <;> norm_num
    have hs0sq : s0 * s0 = 1 := by rcases hs0 with rfl | rfl <;> norm_num
    have hsigAbs : |si * s0| = 1 := by rw [abs_mul, hsiAbs, hs0Abs, one_mul]
    have hmiddist : ‖(T i).midpoint - (T i0).midpoint‖ <= 10 * R0 := by
      calc
        _ <= ‖(T i).midpoint - Tube.lineFoot o u‖ +
            ‖(T i0).midpoint - Tube.lineFoot o u‖ := by
          simpa only [norm_sub_rev (Tube.lineFoot o u) (T i0).midpoint] using
            norm_sub_le_norm_sub_add_norm_sub (T i).midpoint (Tube.lineFoot o u) (T i0).midpoint
        _ <= _ := by linarith
    have hdirdist : ‖(T i).direction - (si * s0) • (T i0).direction‖ <= 8 * R0 := by
      have hid : (T i).direction - (si * s0) • (T i0).direction =
          ((T i).direction - si • u) - (si * s0) • ((T i0).direction - s0 • u) := by
        rcases hs0 with rfl | rfl <;> simp <;> module
      rw [hid]
      calc
        _ <= ‖(T i).direction - si • u‖ + ‖(si * s0) • ((T i0).direction - s0 • u)‖ :=
          norm_sub_le _ _
        _ <= _ := by rw [norm_smul, Real.norm_eq_abs, hsigAbs, one_mul]; linarith
    change z ∈ (T i).carrier at hz
    change z ∈ ((T i0).rescale r).carrier
    rw [(T i).carrier_eq] at hz
    obtain ⟨x, hx, hzx⟩ := Set.mem_iUnion₂.mp hz
    obtain ⟨t, ht, rfl⟩ := (T i).exists_param_of_mem_segment hx
    let y := (T i0).midpoint + (t * (si * s0)) • (T i0).direction
    have hy : y ∈ segment Real (T i0).x (T i0).y := by
      apply (T i0).midpoint_add_smul_mem_segment
      rw [abs_mul, hsigAbs, mul_one]
      exact ht
    have hxy : dist ((T i).midpoint + t • (T i).direction) y <= 14 * R0 := by
      rw [dist_eq_norm]
      have hid : (T i).midpoint + t • (T i).direction - y =
          ((T i).midpoint - (T i0).midpoint) +
            t • ((T i).direction - (si * s0) • (T i0).direction) := by dsimp [y]; module
      rw [hid]
      calc
        _ <= ‖(T i).midpoint - (T i0).midpoint‖ +
            ‖t • ((T i).direction - (si * s0) • (T i0).direction)‖ := norm_add_le _ _
        _ <= _ := by
          rw [norm_smul, Real.norm_eq_abs]
          nlinarith [norm_nonneg ((T i).direction - (si * s0) • (T i0).direction)]
    rw [((T i0).rescale r).carrier_eq]
    apply Set.mem_iUnion₂.mpr ⟨y, hy, ?_⟩
    apply Metric.mem_closedBall.mpr
    exact (dist_triangle z ((T i).midpoint + t • (T i).direction) y).trans
      ((add_le_add (Metric.mem_closedBall.mp hzx) hxy).trans (by linarith))
  refine ⟨o, u, hu, henv, i0, hi0, hcentred i0 hi0, rfl, rfl, ?_, ?_⟩
  · apply hcover (2 * (Cw : Real) * b) (by positivity) henv
    have hdb : (d : Real) <= b := by exact_mod_cast hda.trans hab
    dsimp [trialComparableCarrierScaleW96]
    push_cast
    nlinarith
  · have hv := Tube.volume_le hsmall
      ((T i0).rescale (trialComparableCarrierScaleW96 Cw * b))
    simpa only [hdim, show 3 - 1 = 2 from rfl, ENNReal.coe_mul] using hv

/-- Dedupe actual envelopes and merge every labelled preimage, with no fine loss. -/
theorem exists_deduplicated_envelopes_and_merged_fibres_w96
    {iota : Type uI} {beta : Type uQ} [DecidableEq iota] [DecidableEq beta]
    {r : NNReal} (Q : Finset beta) (W : beta -> ConvexSpaceBody E)
    (B : beta -> Tube r E) (Avol : ENNReal) (hAvol : Avol < ⊤)
    (hcontain : ∀ q ∈ Q, W q <= (B q).toConvexSpaceBody)
    (hvolume : ∀ q ∈ Q, volume (B q).carrier <= Avol * volume (W q).carrier)
    (F : Finset iota) (Y : iota -> ShadedBody E) (label : iota -> beta)
    (hlabel : F.image label ⊆ Q) :
    ∃ (J : Finset beta) (rep : beta -> beta), J ⊆ Q ∧ Q.image rep = J ∧
      (∀ q ∈ Q, rep q ∈ J) ∧
      (∀ q ∈ Q, (B (rep q)).toConvexSpaceBody = (B q).toConvexSpaceBody) ∧
      Set.InjOn (fun q => (B q).toConvexSpaceBody) (J : Set beta) ∧
      maxDensity J (fun q => (B q).toConvexSpaceBody) <= Avol * maxDensity Q W ∧
      (∀ j ∈ J, completeFibreW94 F (rep ∘ label) j =
        (Q.filter (fun q => rep q = j)).biUnion (completeFibreW94 F label)) ∧
      (∑ j ∈ J, ∑ i ∈ completeFibreW94 F (rep ∘ label) j, volume (Y i).shade) =
        ∑ i ∈ F, volume (Y i).shade := by
  classical
  let f : beta -> ConvexSpaceBody E := fun q => (B q).toConvexSpaceBody
  have exists_rep : ∀ q ∈ Q, ∃ j ∈ Q, f j = f q := fun q hq => ⟨q, hq, rfl⟩
  let rep : beta -> beta := fun q => if hq : q ∈ Q then (exists_rep q hq).choose else q
  let J := Q.image rep
  have hrepQ : ∀ q ∈ Q, rep q ∈ Q := by
    intro q hq
    simpa only [rep, dif_pos hq] using (exists_rep q hq).choose_spec.1
  have hrepB : ∀ q ∈ Q, f (rep q) = f q := by
    intro q hq
    simpa only [rep, dif_pos hq] using (exists_rep q hq).choose_spec.2
  have hrepeq : ∀ q ∈ Q, ∀ q' ∈ Q, f q = f q' -> rep q = rep q' := by
    intro q hq q' hq' heq
    dsimp only [rep]
    simp only [dif_pos hq, dif_pos hq', heq.symm]
  have hJQ : J ⊆ Q := by
    rintro j hj
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hj
    exact hrepQ q hq
  have hrepJ : ∀ q ∈ Q, rep q ∈ J := fun q hq => Finset.mem_image_of_mem rep hq
  have hJinj : Set.InjOn f (J : Set beta) := by
    intro j hj j' hj' heq
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp hj'
    exact hrepeq q hq q' hq' ((hrepB q hq).symm.trans (heq.trans (hrepB q' hq')))
  refine ⟨J, rep, hJQ, rfl, hrepJ, hrepB, hJinj, ?_, ?_, ?_⟩
  · apply (maxDensity_le_iff J f _).mpr
    intro K
    have hfilter : (J.filter fun q => f q <= K) ⊆ (Q.filter fun q => W q <= K) := by
      intro q hq
      obtain ⟨hqJ, hqK⟩ := Finset.mem_filter.mp hq
      exact Finset.mem_filter.mpr ⟨hJQ hqJ, (hcontain q (hJQ hqJ)).trans hqK⟩
    calc
      densityIn J f K <= (Avol * ∑ q ∈ Q.filter (fun q => W q <= K), volume (W q).carrier) /
          volume K.carrier := by
        apply ENNReal.div_le_div_right
        calc
          _ <= ∑ q ∈ J.filter (fun q => f q <= K), Avol * volume (W q).carrier :=
            Finset.sum_le_sum fun q hq => hvolume q (hJQ (Finset.mem_filter.mp hq).1)
          _ = Avol * ∑ q ∈ J.filter (fun q => f q <= K), volume (W q).carrier :=
            (Finset.mul_sum _ _ _).symm
          _ <= _ := mul_le_mul' le_rfl (Finset.sum_le_sum_of_subset hfilter)
      _ = Avol * densityIn Q W K := by rw [div_eq_mul_inv, mul_assoc]; rfl
      _ <= _ := mul_le_mul' le_rfl (le_maxDensity Q W K)
  · intro j hj
    ext i
    constructor
    · intro hi
      obtain ⟨hiF, hij⟩ := Finset.mem_filter.mp hi
      refine Finset.mem_biUnion.mpr ⟨label i, ?_, Finset.mem_filter.mpr ⟨hiF, rfl⟩⟩
      exact Finset.mem_filter.mpr ⟨hlabel (Finset.mem_image_of_mem label hiF), hij⟩
    · intro hi
      obtain ⟨q, hq, hiq⟩ := Finset.mem_biUnion.mp hi
      obtain ⟨hiF, hlabeli⟩ := Finset.mem_filter.mp hiq
      exact Finset.mem_filter.mpr ⟨hiF, by simpa only [Function.comp_apply, hlabeli]
        using (Finset.mem_filter.mp hq).2⟩
  · exact Finset.sum_fiberwise_of_maps_to
      (fun i hi => hrepJ (label i) (hlabel (Finset.mem_image_of_mem label hi))) _

def trialBlockParentCountW96 (Ctw kB : NNReal) : Nat :=
  Nat.ceil (Ctw : Real) * lineAmplificationBoundW95 3 2 (16 * (1 + (kB : Real)))

/-- One actual shade-heavy subblock per full block; the SAME subblock is card-heavy. -/
theorem exists_actual_working_parent_subblocks_w96
    (hdim : Module.finrank Real E = 3)
    {iota : Type uI} {pi : Type uP} [DecidableEq iota] [DecidableEq pi]
    {d a b s : NNReal} (hd : 0 < d) (hda : d <= a) (hab : a <= b)
    (hbs : b <= s) (hs : s <= 1)
    (kB Ctw : NNReal) (hkB : 1 <= kB) (hCtw : 1 <= Ctw)
    (F : Finset iota) (Y : iota -> ShadedTube d E)
    (Q : Finset (Finset iota)) (hQ : Q.Nonempty)
    (hqnonempty : ∀ q ∈ Q, q.Nonempty) (hqsub : ∀ q ∈ Q, q ⊆ F)
    (hqdisjoint : (Q : Set (Finset iota)).Pairwise Disjoint)
    (B : Finset iota -> Tube (kB * b) E)
    (hqcarrier : ∀ q ∈ Q, ∀ i ∈ q, (Y i).toConvexSpaceBody <= (B q).toConvexSpaceBody)
    (J : Finset pi) (P : pi -> Tube s E) (assign : iota -> pi)
    (hassign : F.image assign ⊆ J)
    (hassigned : ∀ i ∈ F, (Y i).toConvexSpaceBody <= (P (assign i)).toConvexSpaceBody)
    (hfine_ball : ∀ i ∈ F, (Y i).carrier ⊆ Metric.closedBall 0 1)
    (hparent_ball : ∀ j ∈ J, (P j).carrier ⊆ Metric.closedBall 0 2)
    (hline : lineEssentiallyDistinctW94 J P Ctw)
    (v h D0 CV : ENNReal) (hv : 0 < v) (hvfinite : v < ⊤)
    (hh : 0 < h) (hhfinite : h < ⊤) (hD0 : 0 < D0) (hD0finite : D0 < ⊤)
    (hCV : 0 < CV) (hCVfinite : CV < ⊤)
    (hvol : ∀ i ∈ F, volume (Y i).carrier = v)
    (hfull : ∀ q ∈ Q, h * ((q.card : ENNReal) * v) <= ∑ i ∈ q, volume (Y i).shade)
    (hblockmass : ∀ q ∈ Q, D0 * (a : ENNReal) * (b : ENNReal) / (2 * CV) <=
      (q.card : ENNReal) * v) :
    let M := trialBlockParentCountW96 Ctw kB
    ∃ (chosen : Finset iota -> pi) (qPlus : Finset iota -> Finset iota)
      (G : Finset iota),
      (∀ q ∈ Q, chosen q ∈ q.image assign) ∧
      (∀ q ∈ Q, qPlus q = completeFibreW94 q assign (chosen q)) ∧
      (∀ q ∈ Q, (qPlus q).Nonempty ∧ qPlus q ⊆ q) ∧
      (∀ q ∈ Q, (q.image assign).card <= M) ∧
      (∀ q ∈ Q, (∑ i ∈ q, volume (Y i).shade) <=
        (M : ENNReal) * ∑ i ∈ qPlus q, volume (Y i).shade) ∧
      (∀ q ∈ Q, h / (M : ENNReal) * ((q.card : ENNReal) * v) <=
        ((qPlus q).card : ENNReal) * v) ∧
      (∀ q ∈ Q, h * D0 * (a : ENNReal) * (b : ENNReal) / (2 * (M : ENNReal) * CV) <=
        ∑ i ∈ qPlus q, volume (Y i).carrier) ∧
      G = Q.biUnion qPlus ∧ G.Nonempty ∧ G ⊆ F ∧
      (∑ i ∈ Q.biUnion id, volume (Y i).shade) <=
        (M : ENNReal) * ∑ i ∈ G, volume (Y i).shade ∧
      (∀ j ∈ G.image assign, completeFibreW94 G assign j ⊆
        exactTubeCellW87 F (fun i => (Y i).toTube) (P j)) ∧
      (∀ j ∈ G.image assign, ∃ q ∈ Q, chosen q = j ∧
        qPlus q ⊆ completeFibreW94 G assign j) := by
  classical
  let M := trialBlockParentCountW96 Ctw kB
  have hds : d <= s := hda.trans (hab.trans hbs)
  have hdkb : d <= kB * b := (hda.trans hab).trans (by nlinarith)
  have hs0 : (0 : Real) < s := by exact_mod_cast hd.trans_le hds
  have hcount : ∀ q ∈ Q, (q.image assign).card <= M := by
    intro q hq
    let A := Nat.ceil (Ctw : Real)
    let K : Real := 16 * (1 + (kB : Real))
    have hK : 1 <= K := by
      dsimp [K]
      have hk : (1 : Real) <= kB := by exact_mod_cast hkB
      linarith
    have hlineA : VeryNotSticky.IsLineEssDistinct A J P := by
      intro o u hu
      exact ((pointwise_lineED_iff_library_floor_w95 J P Ctw).mp hline o u hu).trans
        (Nat.floor_le_ceil (Ctw : Real))
    have hcenters : ∀ j ∈ J, ‖(P j).center‖ <= (2 : Real) := by
      intro j hj
      simpa only [Metric.mem_closedBall, dist_zero_right] using hparent_ball j hj
        ((P j).mem_carrier_of_mem_segment (midpoint_mem_segment (𝕜 := Real) (P j).x (P j).y))
    have hlineBig := lineED_five_implies_lineEDAt_w95 (hd.trans_le hds) hs
      J P A hlineA 2 K (by norm_num) hK hcenters
    rw [hdim] at hlineBig
    have hsub : q.image assign ⊆ J.filter (fun j => (P j).carrier ⊆
        VeryNotSticky.lineNbhd (B q).center (B q).direction (K * (s : Real))) := by
      intro j hj
      obtain ⟨i, hiq, rfl⟩ := Finset.mem_image.mp hj
      have hiF := hqsub q hq hiq
      refine Finset.mem_filter.mpr ⟨hassign (Finset.mem_image_of_mem assign hiF), ?_⟩
      have hTcenter : ‖(Y i).toTube.center‖ <= 1 := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using hfine_ball i hiF
          ((Y i).toTube.mem_carrier_of_mem_segment
            (midpoint_mem_segment (𝕜 := Real) (Y i).toTube.x (Y i).toTube.y))
      have hcontain := carrier_in_line_neighborhood_of_common_fine_tube_w96 hd hds hdkb
        (Y i).toTube (P (assign i)) (B q) (hassigned i hiF) (hqcarrier q hq i hiq)
        hTcenter (hcenters (assign i) (hassign (Finset.mem_image_of_mem assign hiF)))
      apply hcontain.trans (Metric.cthickening_mono ?_ _)
      have hbsR : (b : Real) <= s := by exact_mod_cast hbs
      dsimp [K]
      push_cast
      nlinarith [mul_le_mul_of_nonneg_left hbsR kB.coe_nonneg]
    have hcard := (Finset.card_le_card hsub).trans (hlineBig (B q).center (B q).direction
      (B q).norm_direction)
    simpa only [M, trialBlockParentCountW96, A, K, mul_comm] using hcard
  obtain ⟨q0, hq0⟩ := hQ
  obtain ⟨i0, hi0⟩ := hqnonempty q0 hq0
  have hchoice : ∀ q : Finset iota, ∃ j : pi, q ∈ Q -> j ∈ q.image assign ∧
      ∀ j' ∈ q.image assign,
        (∑ i ∈ completeFibreW94 q assign j', volume (Y i).shade) <=
          ∑ i ∈ completeFibreW94 q assign j, volume (Y i).shade := by
    intro q
    by_cases hq : q ∈ Q
    · obtain ⟨j, hj, hmax⟩ := (q.image assign).exists_max_image
        (fun j => ∑ i ∈ completeFibreW94 q assign j, volume (Y i).shade)
        ((hqnonempty q hq).image assign)
      exact ⟨j, fun _ => ⟨hj, hmax⟩⟩
    · exact ⟨assign i0, fun h => (hq h).elim⟩
  choose chosen hchosen using hchoice
  let qPlus := fun q => completeFibreW94 q assign (chosen q)
  let G := Q.biUnion qPlus
  have hplus : ∀ q ∈ Q, (qPlus q).Nonempty ∧ qPlus q ⊆ q := by
    intro q hq
    obtain ⟨i, hi, hij⟩ := Finset.mem_image.mp (hchosen q hq).1
    exact ⟨⟨i, Finset.mem_filter.mpr ⟨hi, hij⟩⟩, Finset.filter_subset _ _⟩
  have hMpos : 0 < M := ((hqnonempty q0 hq0).image assign).card_pos.trans_le (hcount q0 hq0)
  have hME : (0 : ENNReal) < M := by exact_mod_cast hMpos
  have hpaid : ∀ q ∈ Q, (∑ i ∈ q, volume (Y i).shade) <=
      (M : ENNReal) * ∑ i ∈ qPlus q, volume (Y i).shade := by
    intro q hq
    calc
      _ = ∑ j ∈ q.image assign, ∑ i ∈ completeFibreW94 q assign j, volume (Y i).shade :=
        (Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem assign hi) _).symm
      _ <= ∑ _j ∈ q.image assign, ∑ i ∈ qPlus q, volume (Y i).shade :=
        Finset.sum_le_sum fun j hj => (hchosen q hq).2 j hj
      _ = ((q.image assign).card : ENNReal) * ∑ i ∈ qPlus q, volume (Y i).shade := by simp
      _ <= _ := mul_le_mul' (by exact_mod_cast hcount q hq) le_rfl
  have hsumvol : ∀ q ∈ Q, ∑ i ∈ qPlus q, volume (Y i).carrier =
      ((qPlus q).card : ENNReal) * v := by
    intro q hq
    calc
      _ = ∑ _i ∈ qPlus q, v := Finset.sum_congr rfl fun i hi =>
        hvol i (hqsub q hq ((hplus q hq).2 hi))
      _ = _ := by simp
  have hcard : ∀ q ∈ Q, h / (M : ENNReal) * ((q.card : ENNReal) * v) <=
      ((qPlus q).card : ENNReal) * v := by
    intro q hq
    have hle : h * ((q.card : ENNReal) * v) <= (M : ENNReal) *
        (((qPlus q).card : ENNReal) * v) := by
      apply (hfull q hq).trans ((hpaid q hq).trans _)
      rw [← hsumvol q hq]
      exact mul_le_mul' le_rfl (Finset.sum_le_sum fun i _ => measure_mono (Y i).shade_subset)
    calc
      _ = (h * ((q.card : ENNReal) * v)) / (M : ENNReal) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        ring
      _ <= _ := (ENNReal.div_le_iff hME.ne' (by simp)).mpr (by simpa only [mul_comm] using hle)
  have hblock : ∀ q ∈ Q, h * D0 * (a : ENNReal) * (b : ENNReal) /
      (2 * (M : ENNReal) * CV) <= ∑ i ∈ qPlus q, volume (Y i).carrier := by
    intro q hq
    rw [hsumvol q hq]
    apply le_trans _ (hcard q hq)
    have hle := mul_le_mul' (le_refl (h / (M : ENNReal))) (hblockmass q hq)
    convert hle using 1
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
    simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_ofNat,
      ENNReal.toReal_natCast, ENNReal.coe_toReal]
    field_simp
  have hGsub : G ⊆ F := by
    intro i hi
    obtain ⟨q, hq, hiq⟩ := Finset.mem_biUnion.mp hi
    exact hqsub q hq ((hplus q hq).2 hiq)
  have hG : G.Nonempty := by
    obtain ⟨i, hi⟩ := (hplus q0 hq0).1
    exact ⟨i, Finset.mem_biUnion.mpr ⟨q0, hq0, hi⟩⟩
  have hdisjoint : (Q : Set (Finset iota)).Pairwise (fun q q' => Disjoint (qPlus q) (qPlus q')) := by
    intro q hq q' hq' hne
    exact (hqdisjoint hq hq' hne).mono (hplus q hq).2 (hplus q' hq').2
  refine ⟨chosen, qPlus, G, fun q hq => (hchosen q hq).1, fun _ _ => rfl,
    hplus, hcount, hpaid, hcard, hblock, rfl, hG, hGsub, ?_, ?_, ?_⟩
  · change (∑ i ∈ Q.biUnion (fun q => q), volume (Y i).shade) <=
      (M : ENNReal) * ∑ i ∈ Q.biUnion qPlus, volume (Y i).shade
    rw [Finset.sum_biUnion hqdisjoint, Finset.sum_biUnion hdisjoint, Finset.mul_sum]
    exact Finset.sum_le_sum hpaid
  · intro j hj i hi
    obtain ⟨hiG, hij⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨hGsub hiG, hij ▸ hassigned i (hGsub hiG)⟩
  · intro j hj
    obtain ⟨i, hiG, rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨q, hq, hiq⟩ := Finset.mem_biUnion.mp hiG
    have hij : assign i = chosen q := (Finset.mem_filter.mp hiq).2
    refine ⟨q, hq, hij.symm, ?_⟩
    intro i' hi'
    exact Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨q, hq, hi'⟩,
      ((Finset.mem_filter.mp hi').2).trans hij.symm⟩

def trialCompleteCellConstantW96 (Ctw kB : NNReal) (CV Cvol : ENNReal) : ENNReal :=
  4 * (trialNearbyParentCountW96 Ctw : ENNReal) *
    (trialBlockParentCountW96 Ctw kB : ENNReal) * CV * Cvol

/-- Complete NEW geometric cells use G1 reference cells and actual G5 mass witnesses. -/
theorem complete_refined_cell_frostman_bound_w96
    (hdim : Module.finrank Real E = 3)
    {iota : Type uI} {pi : Type uP} [DecidableEq iota] [DecidableEq pi]
    {d a b rho s : NNReal} (hd : 0 < d) (hda : d <= a) (hab : a <= b)
    (hbrho : b <= rho) (hrho : rho <= 1) (hbs : b <= s)
    (F G : Finset iota) (T : iota -> Tube d E) (hGF : G ⊆ F)
    (J : Finset pi) (P : pi -> Tube rho E) (U : pi -> Finset iota)
    (hUsub : ∀ S ∈ J, U S ⊆ F)
    (hUparent : ∀ S ∈ J, ∀ i ∈ U S, (T i).toConvexSpaceBody <= (P S).toConvexSpaceBody)
    (hcover : G ⊆ J.biUnion U)
    (hfine_ball : ∀ i ∈ F, (T i).carrier ⊆ Metric.closedBall 0 1)
    (hparent_ball : ∀ S ∈ J, (P S).carrier ⊆ Metric.closedBall 0 2)
    (Ctw kB : NNReal) (hCtw : 1 <= Ctw) (hkB : 1 <= kB)
    (hline : lineEssentiallyDistinctW94 J P Ctw)
    (D0 h CV Cvol : ENNReal)
    (hD0 : 0 < D0) (hD0finite : D0 < ⊤) (hh : 0 < h) (hhfinite : h < ⊤)
    (hCV : 0 < CV) (hCVfinite : CV < ⊤) (hCvol : 0 < Cvol) (hCvolfinite : Cvol < ⊤)
    (hreference : ∀ S ∈ J, maxDensity (U S) (fun i => (T i).toConvexSpaceBody) <= 2 * D0)
    (R : Tube s E) (qPlus : Finset iota) (hqPlus : qPlus.Nonempty)
    (hsubblock : qPlus ⊆ exactTubeCellW87 G T R)
    (hsubmass : h * D0 * (a : ENNReal) * (b : ENNReal) /
      (2 * (trialBlockParentCountW96 Ctw kB : ENNReal) * CV) <=
        ∑ i ∈ qPlus, volume (T i).carrier)
    (hRvolume : volume R.carrier <= Cvol * (s : ENNReal) ^ (2 : Nat)) :
    let A := exactTubeCellW87 G T R
    A.Nonempty ∧ 0 < ∑ i ∈ A, volume (T i).carrier ∧
      (∑ i ∈ A, volume (T i).carrier) < ⊤ ∧
      maxDensity A (fun i => (T i).toConvexSpaceBody) <=
        2 * (trialNearbyParentCountW96 Ctw : ENNReal) *
          ENNReal.ofReal ((max 1 ((s : Real) / (rho : Real))) ^ (6 : Nat)) * D0 ∧
      frostmanConstIn A (fun i => (T i).toConvexSpaceBody) R.toConvexSpaceBody <=
        trialCompleteCellConstantW96 Ctw kB CV Cvol * h⁻¹ *
          ENNReal.ofReal ((max 1 ((s : Real) / (rho : Real))) ^ (6 : Nat)) *
          ((s : ENNReal) / (b : ENNReal)) ^ (2 : Nat) * ((b : ENNReal) / (a : ENNReal)) := by
  classical
  let A := exactTubeCellW87 G T R
  let N := trialNearbyParentCountW96 Ctw
  let M := trialBlockParentCountW96 Ctw kB
  let X := ENNReal.ofReal ((max 1 ((s : Real) / (rho : Real))) ^ (6 : Nat))
  let lower := h * D0 * (a : ENNReal) * (b : ENNReal) / (2 * (M : ENNReal) * CV)
  have ha : 0 < a := hd.trans_le hda
  have hb : 0 < b := ha.trans_le hab
  have hs : 0 < s := hb.trans_le hbs
  have hd1 : d <= 1 := hda.trans (hab.trans (hbrho.trans hrho))
  have hA : A.Nonempty := hqPlus.mono hsubblock
  have hAsub : A ⊆ F := (exactTubeCell_subset_w87 G T R).trans hGF
  have hcontained : ∀ i ∈ A, (T i).toConvexSpaceBody <= R.toConvexSpaceBody :=
    fun i hi => (Finset.mem_filter.mp hi).2
  have hApos : 0 < ∑ i ∈ A, volume (T i).carrier := by
    obtain ⟨i, hi⟩ := hA
    exact (Tube.volume_pos_and_lt_top hd hd1 (T i)).1.trans_le
      (Finset.single_le_sum (f := fun i => volume (T i).carrier) (fun _ _ => zero_le) hi)
  have hAfin : (∑ i ∈ A, volume (T i).carrier) < ⊤ :=
    ENNReal.sum_lt_top.mpr fun i _ => (T i).toConvexSpaceBody.isCompact.measure_lt_top
  have hmass : lower <= ∑ i ∈ A, volume (T i).carrier :=
    hsubmass.trans (Finset.sum_le_sum_of_subset hsubblock)
  have haE : (0 : ENNReal) < a := by exact_mod_cast ha
  have hbE : (0 : ENNReal) < b := by exact_mod_cast hb
  have hsE : (0 : ENNReal) < s := by exact_mod_cast hs
  have hnumpos : 0 < h * D0 * (a : ENNReal) * (b : ENNReal) := by positivity
  have hlowerpos : 0 < lower := ENNReal.div_pos hnumpos.ne' (by
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) (by simp)) hCVfinite.ne)
  have hlowerfin : lower < ⊤ := hmass.trans_lt hAfin
  have hM : (M : ENNReal) ≠ 0 := by
    intro hM
    have htop : lower = ⊤ := ENNReal.div_eq_top.mpr (Or.inl ⟨hnumpos.ne', by simp [hM]⟩)
    exact hlowerfin.ne htop
  let meeting := commonFineMeetingParentsW96 F T J P R
  have hcoverA : A ⊆ meeting.biUnion U := by
    intro i hi
    obtain ⟨S, hS, hiU⟩ := Finset.mem_biUnion.mp
      (hcover (exactTubeCell_subset_w87 G T R hi))
    exact Finset.mem_biUnion.mpr ⟨S, Finset.mem_filter.mpr
      ⟨hS, i, hAsub hi, hUparent S hS i hiU, hcontained i hi⟩, hiU⟩
  have hcount : (meeting.card : ENNReal) <= (N : ENNReal) * X := by
    have hc := card_assigned_parents_meeting_exact_cell_w96 hdim hd
      (hda.trans (hab.trans hbrho)) (hda.trans (hab.trans hbs)) hrho
      F T J P R Ctw hCtw hfine_ball hparent_ball hline
    have hcE := ENNReal.ofReal_le_ofReal hc
    simpa only [ENNReal.ofReal_natCast, ENNReal.ofReal_mul (Nat.cast_nonneg _)] using hcE
  have hmax : maxDensity A (fun i => (T i).toConvexSpaceBody) <= 2 * (N : ENNReal) * X * D0 := by
    calc
      _ <= ∑ S ∈ meeting, maxDensity (U S) (fun i => (T i).toConvexSpaceBody) :=
        maxDensity_le_sum_of_subset_biUnion _ hcoverA
      _ <= ∑ _S ∈ meeting, 2 * D0 :=
        Finset.sum_le_sum fun S hS => hreference S (Finset.mem_filter.mp hS).1
      _ = (meeting.card : ENNReal) * (2 * D0) := by simp
      _ <= ((N : ENNReal) * X) * (2 * D0) := mul_le_mul' hcount le_rfl
      _ = _ := by ring
  refine ⟨hA, hApos, hAfin, hmax, ?_⟩
  have hRfin : volume R.carrier < ⊤ := R.toConvexSpaceBody.isCompact.measure_lt_top
  have hdensity : 0 < densityIn A (fun i => (T i).toConvexSpaceBody) R.toConvexSpaceBody := by
    rw [densityIn_of_all_le hcontained]
    exact ENNReal.div_pos hApos.ne' hRfin.ne
  have hdenom : lower / (Cvol * (s : ENNReal) ^ (2 : Nat)) <=
      densityIn A (fun i => (T i).toConvexSpaceBody) R.toConvexSpaceBody := by
    rw [densityIn_of_all_le hcontained]
    exact ENNReal.div_le_div hmass hRvolume
  rw [frostmanConstIn_eq_frostmanConstant, frostmanConstant_eq_maxDensity_div hdensity hcontained]
  apply (ENNReal.div_le_div hmax hdenom).trans
  let rhs := trialCompleteCellConstantW96 Ctw kB CV Cvol * h⁻¹ * X *
    ((s : ENNReal) / (b : ENNReal)) ^ (2 : Nat) * ((b : ENNReal) / (a : ENNReal))
  have hCVspos : 0 < Cvol * (s : ENNReal) ^ (2 : Nat) := by positivity
  have hCVsfin : Cvol * (s : ENNReal) ^ (2 : Nat) ≠ ⊤ := by finiteness
  have hdenpos : 0 < lower / (Cvol * (s : ENNReal) ^ (2 : Nat)) :=
    ENNReal.div_pos hlowerpos.ne' hCVsfin
  have hleftfin : 2 * (N : ENNReal) * X * D0 /
      (lower / (Cvol * (s : ENNReal) ^ (2 : Nat))) ≠ ⊤ := by
    apply ENNReal.div_ne_top _ hdenpos.ne'
    dsimp [X]
    finiteness
  have hrhsfin : rhs ≠ ⊤ := by
    dsimp [rhs, trialCompleteCellConstantW96, X]
    finiteness
  apply le_of_eq
  apply (ENNReal.toReal_eq_toReal_iff' hleftfin hrhsfin).mp
  have hhreal : h.toReal ≠ 0 := (ENNReal.toReal_pos hh.ne' hhfinite.ne).ne'
  have hDreal : D0.toReal ≠ 0 := (ENNReal.toReal_pos hD0.ne' hD0finite.ne).ne'
  have hCVreal : CV.toReal ≠ 0 := (ENNReal.toReal_pos hCV.ne' hCVfinite.ne).ne'
  have hCvolreal : Cvol.toReal ≠ 0 := (ENNReal.toReal_pos hCvol.ne' hCvolfinite.ne).ne'
  have hMreal : (M : Real) ≠ 0 := by exact_mod_cast hM
  dsimp [rhs, lower, N, M, trialCompleteCellConstantW96]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow,
    ENNReal.toReal_inv, ENNReal.toReal_ofNat, ENNReal.toReal_natCast, ENNReal.coe_toReal]
  dsimp [M] at hMreal
  field_simp
  <;> ring

/-- The six parent parameters and two volume powers account for exactly 16/L. -/
theorem complete_cell_scale_payment_w96
    {d a b rho s : Real} (hd : 0 < d) (hdone : d <= 1)
    (ha : 0 < a) (hab : a <= b) (hbrho : b <= rho) (hbs : b <= s)
    (L : Nat) (hL : 0 < L) (etaP kappa : Real) (hetaP : 0 <= etaP)
    (hadjacent : s / b <= d ^ (-2 / (L : Real)))
    (heccentric : b / a <= d ^ (-kappa)) :
    (max 1 (s / rho)) ^ (6 : Nat) <= d ^ (-12 / (L : Real)) ∧
      (s / b) ^ (2 : Nat) <= d ^ (-4 / (L : Real)) ∧
      (d ^ etaP)⁻¹ * (max 1 (s / rho)) ^ (6 : Nat) * (s / b) ^ (2 : Nat) * (b / a) <=
        d ^ (-etaP - 16 / (L : Real) - kappa) ∧
      d ^ (-etaP - 16 / (L : Real) - kappa) <=
        d ^ (-2 * etaP - 16 / (L : Real) - kappa) := by
  have hb : 0 < b := ha.trans_le hab
  have hrho : 0 < rho := hb.trans_le hbrho
  have hs : 0 < s := hb.trans_le hbs
  have hLr : (0 : Real) < L := by exact_mod_cast hL
  have hratio : max 1 (s / rho) <= d ^ (-2 / (L : Real)) := by
    apply max_le
    · calc
        1 <= s / b := (le_div_iff₀ hb).mpr (by simpa using hbs)
        _ <= _ := hadjacent
    · exact (div_le_div_of_nonneg_left hs.le hb hbrho).trans hadjacent
  have h6 : (max 1 (s / rho)) ^ (6 : Nat) <= d ^ (-12 / (L : Real)) := by
    calc
      _ <= (d ^ (-2 / (L : Real))) ^ (6 : Nat) := by
        gcongr
      _ = _ := by rw [← Real.rpow_natCast, ← Real.rpow_mul hd.le]; congr 1; ring
  have h2 : (s / b) ^ (2 : Nat) <= d ^ (-4 / (L : Real)) := by
    calc
      _ <= (d ^ (-2 / (L : Real))) ^ (2 : Nat) := by gcongr
      _ = _ := by rw [← Real.rpow_natCast, ← Real.rpow_mul hd.le]; congr 1; ring
  refine ⟨h6, h2, ?_, Real.rpow_le_rpow_of_exponent_ge hd hdone (by linarith)⟩
  calc
    _ <= (d ^ etaP)⁻¹ * d ^ (-12 / (L : Real)) * d ^ (-4 / (L : Real)) *
        d ^ (-kappa) := by gcongr
    _ = _ := by
      rw [← Real.rpow_neg hd.le, ← Real.rpow_add hd, ← Real.rpow_add hd,
        ← Real.rpow_add hd]
      congr 1
      ring

/-- G7 reads old CF on original F and returns both bounds on the same actual G. -/
theorem actual_old_cell_gap_gives_assigned_and_exact_drop_w96
    (hdim : Module.finrank Real E = 3)
    {iota : Type uI} {pi : Type uP} [DecidableEq iota] [DecidableEq pi]
    {d s : NNReal} (hd : 0 < d) (hds : d <= s) (hs : s <= 1)
    (F G : Finset iota) (T : iota -> Tube d E) (hGF : G ⊆ F)
    (J : Finset pi) (P : pi -> Tube s E) (assign : iota -> pi)
    (hassign : G.image assign = J)
    (hassigned : ∀ i ∈ G, (T i).toConvexSpaceBody <= (P (assign i)).toConvexSpaceBody)
    (hfine_ball : ∀ i ∈ F, (T i).carrier ⊆ Metric.closedBall 0 1)
    (hparent_ball : ∀ j ∈ J, (P j).carrier ⊆ Metric.closedBall 0 2)
    (Ctw : NNReal) (hCtw : 1 <= Ctw) (hline : lineEssentiallyDistinctW94 J P Ctw)
    (epsilon zetaPlus : Real) (Lambda u : ENNReal)
    (hLambda : 0 < Lambda) (hLambdafinite : Lambda < ⊤) (hufinite : u < ⊤)
    (hold : ∀ j ∈ J, Lambda <= frostmanConstIn (exactTubeCellW87 F T (P j))
      (fun i => (T i).toConvexSpaceBody) (P j).toConvexSpaceBody)
    (hnew : ∀ j ∈ J, frostmanConstIn (exactTubeCellW87 G T (P j))
      (fun i => (T i).toConvexSpaceBody) (P j).toConvexSpaceBody <= u)
    (hpayment : u / Lambda <= ENNReal.ofReal ((d : Real) ^ (epsilon * zetaPlus / 4)))
    (hcoverpayment : (trialNearbyParentCountW96 Ctw : ENNReal) *
      ENNReal.ofReal ((d : Real) ^ (epsilon * zetaPlus / 4)) <=
        ENNReal.ofReal ((d : Real) ^ (epsilon * zetaPlus / 8))) :
    (∀ j ∈ J, maxDensity (completeFibreW94 G assign j) (fun i => (T i).toConvexSpaceBody) <=
      ENNReal.ofReal ((d : Real) ^ (epsilon * zetaPlus / 4)) * allExactTubeNsW87 F T s) ∧
      allExactTubeNsW87 G T s <=
        ENNReal.ofReal ((d : Real) ^ (epsilon * zetaPlus / 8)) * allExactTubeNsW87 F T s := by
  classical
  have hpartsub : ∀ j ∈ J, completeFibreW94 G assign j ⊆ exactTubeCellW87 G T (P j) := by
    intro j hj i hi
    obtain ⟨hiG, hij⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_filter.mpr ⟨hiG, hij ▸ hassigned i hiG⟩
  have hcellne : ∀ j ∈ J, (exactTubeCellW87 G T (P j)).Nonempty := by
    intro j hj
    rw [← hassign] at hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, hassigned i hi⟩⟩
  have hlocal : ∀ j ∈ J, maxDensity (completeFibreW94 G assign j)
      (fun i => (T i).toConvexSpaceBody) <=
        ENNReal.ofReal ((d : Real) ^ (epsilon * zetaPlus / 4)) * allExactTubeNsW87 F T s := by
    intro j hj
    have hsub := exactTubeCell_mono_family_w87 hGF T (P j)
    have hOld := (hcellne j hj).mono hsub
    have hvol := Tube.volume_pos_and_lt_top (hd.trans_le hds) hs (P j)
    have hdrop := maxDensity_drop_of_complete_cell_frostman_gap_w94
      (exactTubeCellW87 F T (P j)) (exactTubeCellW87 G T (P j))
      (fun i => (T i).toConvexSpaceBody) (P j).toConvexSpaceBody Lambda u hOld hsub
      (fun i hi => (Finset.mem_filter.mp hi).2) hvol.1 hvol.2 hLambda hLambdafinite
      hufinite (hold j hj) (hnew j hj)
    exact (maxDensity_mono _ (hpartsub j hj)).trans
      (hdrop.trans (mul_le_mul' hpayment
        (maxDensity_exactTubeCell_le_allExactTubeNs_w87 (P j) hOld)))
  refine ⟨hlocal, ?_⟩
  have hcover : G ⊆ J.biUnion (completeFibreW94 G assign) := by
    intro i hi
    exact Finset.mem_biUnion.mpr ⟨assign i, hassign ▸ Finset.mem_image_of_mem assign hi,
      Finset.mem_filter.mpr ⟨hi, rfl⟩⟩
  have hmeeting : ∀ R : Tube s E,
      (((J.filter fun j => (completeFibreW94 G assign j ∩ exactTubeCellW87 G T R).Nonempty).card : Nat) : ENNReal)
        <= (trialNearbyParentCountW96 Ctw : ENNReal) := by
    intro R
    have hsub : (J.filter fun j =>
        (completeFibreW94 G assign j ∩ exactTubeCellW87 G T R).Nonempty) ⊆
        commonFineMeetingParentsW96 F T J P R := by
      intro j hj
      obtain ⟨hjJ, i, hi⟩ := Finset.mem_filter.mp hj
      obtain ⟨hiPart, hiR⟩ := Finset.mem_inter.mp hi
      obtain ⟨hiG, hij⟩ := Finset.mem_filter.mp hiPart
      exact Finset.mem_filter.mpr ⟨hjJ, i, hGF hiG,
        hij ▸ hassigned i hiG, (Finset.mem_filter.mp hiR).2⟩
    have hcount := card_assigned_parents_meeting_exact_cell_w96 hdim hd hds hds hs
      F T J P R Ctw hCtw hfine_ball hparent_ball hline
    have hs0 : (s : Real) ≠ 0 := by exact_mod_cast (hd.trans_le hds).ne'
    simp only [div_self hs0, max_self, one_pow, mul_one] at hcount
    have hcountNat : (commonFineMeetingParentsW96 F T J P R).card <= trialNearbyParentCountW96 Ctw :=
      by exact_mod_cast hcount
    exact_mod_cast (Finset.card_le_card hsub).trans hcountNat
  exact (allExactTubeNs_le_of_assignedCover_w87 J (completeFibreW94 G assign)
    (ENNReal.ofReal ((d : Real) ^ (epsilon * zetaPlus / 4)))
    (trialNearbyParentCountW96 Ctw : ENNReal) hcover hlocal hmeeting).trans
      (mul_le_mul' hcoverpayment le_rfl)

end

end Kakeya.ml1Boot.TrialRestartW94
