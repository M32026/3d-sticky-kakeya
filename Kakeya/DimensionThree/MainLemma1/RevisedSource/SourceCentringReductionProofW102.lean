module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.SourceConstructionDefinitionsW97
public import Kakeya.DimensionThree.MainLemma1.RevisedSource.CentringDensityW102

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody
open scoped ENNReal NNReal

namespace Kakeya.ml1Boot.TrialRestartW94

noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2000000

universe uE uI

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

open RevisedLiteralProfileInterfaceFormalizerW87

/-- Revised detailed GWZ 3117-3119 uses this operation before fixing U0.
The exact source construction is the rho=1 specialization of 4799-4825:
L(x)=x/8, J=1/512, and output radius delta/2. The output labels are
representatives of the original finite family, not original tube bodies.
This is a separate obligation from the source-centred prepared pass. -/
theorem exists_source_centring_reduction_w101
    (hdim : Module.finrank Real E = 3) :
    ∃ A0 F0 : NNReal, A0 = 2 * (223 : NNReal) ^ (6 : Nat) ∧
      F0 = (5000 : NNReal) ^ (6 : Nat) ∧
      ∀ {delta : NNReal}, 0 < delta -> delta <= 1 / 200 ->
      ∀ {iota : Type uI} [DecidableEq iota]
        (F : Finset iota) (Y : iota -> ShadedTube delta E)
        (Cline : NNReal), 1 <= Cline -> F.Nonempty ->
        (∀ i ∈ F, (Y i).carrier ⊆ Metric.closedBall 0 1) ->
        lineEssentiallyDistinctW94 F (fun i => (Y i).toTube) Cline ->
        ∃ (G : Finset iota) (parent : iota -> iota)
          (Z : iota -> ShadedTube (delta / 2) E),
          G.Nonempty ∧ G ⊆ F ∧ F.image parent = G ∧
          (∀ j ∈ G, (Z j).carrier ⊆ Metric.closedBall 0 (3 / 4 : Real)) ∧
          (∀ j ∈ G, centredTubeW94 (Z j).toTube) ∧
          lineEssentiallyDistinctW94 G (fun j => (Z j).toTube) A0 ∧
          (∀ i ∈ F, (fun x : E => (1 / 8 : Real) • x) '' (Y i).carrier ⊆
            (Z (parent i)).carrier) ∧
          (∀ j ∈ G, ((completeFibreW94 F parent j).card : NNReal) <= F0 * Cline) ∧
          (∀ i ∈ F, volume (Z (parent i)).carrier <=
            (384 : ENNReal) * (1 / 512 : ENNReal) * volume (Y i).carrier) ∧
          (∀ j ∈ G, (Z j).shade =
            ⋃ i ∈ completeFibreW94 F parent j,
              (fun x : E => (1 / 8 : Real) • x) '' (Y i).shade) ∧
          (⋃ j ∈ G, (Z j).shade) =
            (fun x : E => (1 / 8 : Real) • x) '' (⋃ i ∈ F, (Y i).shade) ∧
          volume (⋃ j ∈ G, (Z j).shade) =
            (1 / 512 : ENNReal) * volume (⋃ i ∈ F, (Y i).shade) ∧
          (F.card : ENNReal) / ((F0 : ENNReal) * (Cline : ENNReal)) <=
            (G.card : ENNReal) ∧ G.card <= F.card ∧
          ShadedBody.multiplicity G (fun j => (Z j).toShadedBody) <=
            ShadedBody.multiplicity F (fun i => (Y i).toShadedBody) ∧
          ShadedBody.multiplicity F (fun i => (Y i).toShadedBody) <=
            (F0 : ENNReal) * (Cline : ENNReal) *
              ShadedBody.multiplicity G (fun j => (Z j).toShadedBody) ∧
          fullness' F (fun i => (Y i).toShadedBody) /
              (384 * (F0 : ENNReal) * (Cline : ENNReal)) <=
            fullness' G (fun j => (Z j).toShadedBody) ∧
          maxDensity G (fun j => (Z j).toConvexSpaceBody) <=
            384 * maxDensity F (fun i => (Y i).toConvexSpaceBody) ∧
          (1 / 512 : ENNReal) /
              ((F0 : ENNReal) * (Cline : ENNReal)) *
                (∑ i ∈ F, volume (Y i).shade) <=
            ∑ j ∈ G, volume (Z j).shade := by
  classical
  let F0 : NNReal := (5000 : NNReal) ^ (6 : Nat)
  have hF0 : 1 <= F0 := by norm_num [F0]
  refine ⟨2 * (223 : NNReal) ^ (6 : Nat), F0, rfl, rfl, ?_⟩
  intro delta hd hdsmall iota _ F Y Cline hCline hF hball hline
  obtain ⟨G, parent, W, hG, hGF, himage, hfix, hballW, hcen, hlineW, hcov, hcard⟩ :=
    exists_source_centred_representatives_w102 hdim hd hdsmall F
      (fun i => (Y i).toTube) Cline hF hball hline
  let Z : iota -> ShadedTube (delta / 2) E :=
    sourceCentringShadingW102 F Y parent W hcov
  let J : ENNReal := 1 / 512
  let B : ENNReal := (F0 : ENNReal) * (Cline : ENNReal)
  have hJ0 : J ≠ 0 := by norm_num [J]
  have hJtop : J ≠ ⊤ := by norm_num [J]
  have hC0 : Cline ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hCline)
  have hB0 : B ≠ 0 := by simp [B, F0, hC0]
  have hBtop : B ≠ ⊤ := ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top
  have hmap : ∀ i ∈ F, parent i ∈ G := by
    intro i hi
    rw [← himage]
    exact Finset.mem_image_of_mem _ hi
  have hcard' : ∀ j ∈ G,
      ((completeFibreW94 F parent j).card : NNReal) <= F0 * Cline := by
    intro j hj
    exact (hcard j hj).trans (le_mul_of_one_le_left (by positivity) hF0)
  have hcardB : ∀ j ∈ G,
      ((completeFibreW94 F parent j).card : ENNReal) <= B := by
    intro j hj
    change ((completeFibreW94 F parent j).card : ENNReal) <=
      (F0 : ENNReal) * (Cline : ENNReal)
    exact_mod_cast hcard' j hj
  have hvol : ∀ i ∈ F, volume (Z (parent i)).carrier <=
      384 * J * volume (Y i).carrier := by
    intro i hi
    exact half_radius_carrier_volume_w102 hdim hdsmall (Y i).toTube (W (parent i))
  have hshade : ∀ j ∈ G, (Z j).shade =
      ⋃ i ∈ completeFibreW94 F parent j,
        (fun x : E => (1 / 8 : Real) • x) '' (Y i).shade := fun _ _ => rfl
  have hunion : (⋃ j ∈ G, (Z j).shade) =
      (fun x : E => (1 / 8 : Real) • x) '' (⋃ i ∈ F, (Y i).shade) :=
    source_centring_shaded_union_w102 F G Y parent W hcov hmap
  have hunionVol : volume (⋃ j ∈ G, (Z j).shade) =
      J * volume (⋃ i ∈ F, (Y i).shade) := by
    rw [hunion, volume_source_centring_image_w102 hdim]
  have himageSum : (∑ i ∈ F,
      volume ((fun x : E => (1 / 8 : Real) • x) '' (Y i).shade)) =
      J * ∑ i ∈ F, volume (Y i).shade := by
    simp_rw [volume_source_centring_image_w102 hdim]
    exact (Finset.mul_sum _ _ _).symm
  have hmass := fibre_union_measure_bounds_w102 F G parent
    (fun i => (fun x : E => (1 / 8 : Real) • x) '' (Y i).shade) B hmap hcardB
  change (∑ j ∈ G, volume (Z j).shade) <= _ ∧
    _ <= B * ∑ j ∈ G, volume (Z j).shade at hmass
  rw [himageSum] at hmass
  have hcardTotal : (F.card : ENNReal) <= B * (G.card : ENNReal) := by
    calc
      _ = ∑ j ∈ G, ((completeFibreW94 F parent j).card : ENNReal) := by
        simpa only [completeFibreW94, Finset.sum_const, nsmul_eq_mul, mul_one] using
          (Finset.sum_fiberwise_of_maps_to hmap (fun _ => (1 : ENNReal))).symm
      _ <= ∑ j ∈ G, B := Finset.sum_le_sum hcardB
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hmultUpper : ShadedBody.multiplicity G (fun j => (Z j).toShadedBody) <=
      ShadedBody.multiplicity F (fun i => (Y i).toShadedBody) := by
    unfold ShadedBody.multiplicity
    change (∑ j ∈ G, volume (Z j).shade) / volume (⋃ j ∈ G, (Z j).shade) <= _
    rw [hunionVol]
    exact (ENNReal.div_le_div_right hmass.1 _).trans_eq
      (ENNReal.mul_div_mul_left _ _ hJ0 hJtop)
  have hmultLower : ShadedBody.multiplicity F (fun i => (Y i).toShadedBody) <=
      B * ShadedBody.multiplicity G (fun j => (Z j).toShadedBody) := by
    unfold ShadedBody.multiplicity
    change _ <= B * ((∑ j ∈ G, volume (Z j).shade) / volume (⋃ j ∈ G, (Z j).shade))
    rw [hunionVol]
    calc
      _ = (J * ∑ i ∈ F, volume (Y i).shade) /
          (J * volume (⋃ i ∈ F, (Y i).shade)) :=
        (ENNReal.mul_div_mul_left _ _ hJ0 hJtop).symm
      _ <= (B * ∑ j ∈ G, volume (Z j).shade) /
          (J * volume (⋃ i ∈ F, (Y i).shade)) := ENNReal.div_le_div_right hmass.2 _
      _ = _ := mul_div_assoc _ _ _
  have hcarSum : (∑ j ∈ G, volume (Z j).carrier) <=
      (384 * J) * ∑ i ∈ F, volume (Y i).carrier := by
    calc
      _ <= ∑ j ∈ G, (384 * J) * volume (Y j).carrier := by
        apply Finset.sum_le_sum
        intro j hj
        simpa only [hfix j hj] using hvol j (hGF hj)
      _ = (384 * J) * ∑ j ∈ G, volume (Y j).carrier := (Finset.mul_sum _ _ _).symm
      _ <= _ := mul_le_mul' le_rfl (Finset.sum_le_sum_of_subset hGF)
  have hfull : fullness' F (fun i => (Y i).toShadedBody) /
      (384 * (F0 : ENNReal) * (Cline : ENNReal)) <=
      fullness' G (fun j => (Z j).toShadedBody) := by
    have hden0 : (384 * (F0 : ENNReal) * (Cline : ENNReal)) ≠ 0 := by
      simpa only [mul_assoc] using mul_ne_zero (by norm_num : (384 : ENNReal) ≠ 0) hB0
    have hdenTop : (384 * (F0 : ENNReal) * (Cline : ENNReal)) ≠ ⊤ := by
      exact ENNReal.mul_ne_top
        (ENNReal.mul_ne_top (by norm_num) ENNReal.coe_ne_top) ENNReal.coe_ne_top
    have hCYtop : (∑ i ∈ F, volume (Y i).carrier) ≠ ⊤ :=
      ENNReal.sum_ne_top.mpr fun i hi => (Y i).toConvexSpaceBody.isCompact.measure_ne_top
    have hmassY : (∑ i ∈ F, volume (Y i).shade) =
        fullness' F (fun i => (Y i).toShadedBody) * ∑ i ∈ F, volume (Y i).carrier := by
      simpa only [ShadedBody.coe_fullness] using
        ShadedBody.sum_volumeReal_shade_eq_fullness_mul F (fun i => (Y i).toShadedBody)
    have hmassZ : (∑ j ∈ G, volume (Z j).shade) =
        fullness' G (fun j => (Z j).toShadedBody) * ∑ j ∈ G, volume (Z j).carrier := by
      simpa only [ShadedBody.coe_fullness] using
        ShadedBody.sum_volumeReal_shade_eq_fullness_mul G (fun j => (Z j).toShadedBody)
    by_cases hCY0 : (∑ i ∈ F, volume (Y i).carrier) = 0
    · have hSY0 : (∑ i ∈ F, volume (Y i).shade) = 0 := by rw [hmassY, hCY0, mul_zero]
      simp only [fullness', hSY0, ENNReal.zero_div]
      exact zero_le
    · apply (ENNReal.div_le_iff hden0 hdenTop).mpr
      have hscaled :
          (J * ∑ i ∈ F, volume (Y i).carrier) * fullness' F (fun i => (Y i).toShadedBody) <=
          (J * ∑ i ∈ F, volume (Y i).carrier) *
            (384 * B * fullness' G (fun j => (Z j).toShadedBody)) := by
        calc
          _ = J * ∑ i ∈ F, volume (Y i).shade := by rw [hmassY]; ring
          _ <= B * ∑ j ∈ G, volume (Z j).shade := hmass.2
          _ = B * (fullness' G (fun j => (Z j).toShadedBody) *
              ∑ j ∈ G, volume (Z j).carrier) := by rw [hmassZ]
          _ <= B * (fullness' G (fun j => (Z j).toShadedBody) *
              ((384 * J) * ∑ i ∈ F, volume (Y i).carrier)) :=
            mul_le_mul' le_rfl (mul_le_mul' le_rfl hcarSum)
          _ = _ := by ring
      have h := (ENNReal.mul_le_mul_iff_right (mul_ne_zero hJ0 hCY0)
        (ENNReal.mul_ne_top hJtop hCYtop)).mp hscaled
      simpa only [B, mul_assoc, mul_comm, mul_left_comm] using h
  refine ⟨G, parent, Z, hG, hGF, himage, hballW, hcen, hlineW, hcov, hcard',
    hvol, hshade, hunion, hunionVol, ?_, Finset.card_le_card hGF, hmultUpper,
    hmultLower, hfull, ?_, ?_⟩
  · exact (ENNReal.div_le_iff hB0 hBtop).mpr (by simpa only [mul_comm] using hcardTotal)
  · apply source_centring_maxDensity_w102 hdim hdsmall F G
      (fun i => (Y i).toTube) W hGF
    intro j hj
    simpa only [hfix j hj] using hcov j (hGF hj)
  · have h : (J * ∑ i ∈ F, volume (Y i).shade) / B <=
        ∑ j ∈ G, volume (Z j).shade := (ENNReal.div_le_iff hB0 hBtop).mpr
      (by simpa only [mul_comm] using hmass.2)
    simpa only [B, J, div_eq_mul_inv, one_mul, mul_assoc, mul_comm, mul_left_comm] using h

end

end Kakeya.ml1Boot.TrialRestartW94
