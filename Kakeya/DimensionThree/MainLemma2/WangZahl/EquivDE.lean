/-
Wang--Zahl Proposition 1.6 (`equivDE`), the hard direction `D => E`, reduced to
its two source ingredients.

Source: `blueprint/src/WZ2/250224e_K3.tex`, Section `cEIffcDSec`.

The source proof of Proposition `equivDE` is exactly two steps:

  * the **base estimate** `E(sigma, 2)`, which the source disposes of in one
    line ("since a `delta`-tube has volume `~ delta^2`, we always have that
    `cE(sigma,2)` is true"), and

  * the **uniform weak reverse step**, Lemma `weakerPropEquivDE`: for all
    `omega, t > 0` there is a single `alpha > 0` that works for *every*
    `omega' >= omega + t`.

Everything between them -- the iteration down from `2`, the endpoint
bookkeeping, and the closure in `omega` -- is
`assertionD_implies_assertionE_of_uniform_reverse_step` in
`WangZahl/WZReverseBootstrap.lean`.

This file proves the base estimate `assertionE_two` unconditionally, and
records the weak reverse step as the single remaining obligation.
-/
module

public import Kakeya.DimensionThree.MainLemma2.WangZahl.SigmaCalculus
public import Kakeya.DimensionThree.MainLemma2.WangZahl.WZReverseBootstrap
public import Kakeya.DimensionThree.CardBound
public import Kakeya.DimensionThree.MainLemma2.WangZahl.Rescaling
public import Kakeya.DimensionThree.MainLemma2.WangZahl.TubeTrichotomy

@[expose] public section

open MeasureTheory

namespace Kakeya.WangZahl

noncomputable section

universe u

/-! ### The exponent-two base estimate `E(sigma, 2)` -/


lemma delta_le_one_of_tube_subset_unitBall {δ : NNReal} (T : Tube δ Space3)
    (h : T.carrier ⊆ Metric.closedBall (0 : Space3) 1) : δ ≤ 1 := by
  have hsub : Metric.closedBall T.x (δ : ℝ) ⊆ Metric.closedBall (0 : Space3) 1 :=
    (T.closedBall_subset_carrier_of_mem_segment (left_mem_segment ℝ T.x T.y)).trans h
  have hvol := measure_mono (μ := (volume : Measure Space3)) hsub
  rw [Measure.addHaar_closedBall (volume : Measure Space3) T.x δ.coe_nonneg] at hvol
  have hb : volume (Metric.ball (0:Space3) 1) = volume (Metric.closedBall (0:Space3) 1) := by
    simp [EuclideanSpace.volume_ball, EuclideanSpace.volume_closedBall]
  rw [hb] at hvol
  have hB0 := volume_unitBall_ne_zero
  have hBtop := volume_unitBall_ne_top
  have hvol' : ENNReal.ofReal ((δ : ℝ) ^ Module.finrank ℝ Space3) *
      volume (Metric.closedBall (0:Space3) 1) ≤ 1 * volume (Metric.closedBall (0:Space3) 1) := by
    rwa [one_mul]
  have h1 : ENNReal.ofReal ((δ : ℝ) ^ Module.finrank ℝ Space3) ≤ 1 :=
    (ENNReal.mul_le_mul_iff_left hB0 hBtop).mp hvol'
  have hrank : Module.finrank ℝ Space3 = 3 := by simp [Space3]
  rw [hrank] at h1
  have h2 : ((δ : ℝ)) ^ 3 ≤ 1 := (ENNReal.ofReal_le_one).mp h1
  by_contra hc
  have hgt : (1:ℝ) < (δ : ℝ) := by exact_mod_cast lt_of_not_ge hc
  nlinarith [h2, hgt, sq_nonneg ((δ:ℝ) - 1), sq_nonneg ((δ:ℝ))]

def stdHyperplane : Hyperplane3 where
  carrier := AffineSubspace.mk' (0 : Space3) ((ℝ ∙ (EuclideanSpace.single 2 (1:ℝ)))ᗮ)
  nonempty_carrier := ⟨0, AffineSubspace.self_mem_mk' _ _⟩
  finrank_direction := by
    rw [AffineSubspace.direction_mk']
    have hv : (EuclideanSpace.single 2 (1:ℝ) : Space3) ≠ 0 := by
      simp [EuclideanSpace.single]
    have h1 : Module.finrank ℝ (ℝ ∙ (EuclideanSpace.single 2 (1:ℝ) : Space3)) = 1 :=
      finrank_span_singleton hv
    have h2 := Submodule.finrank_add_finrank_orthogonal
      (K := (ℝ ∙ (EuclideanSpace.single 2 (1:ℝ) : Space3)))
    have h3 : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
    rw [h1, h3] at h2
    linarith

def unitBallSlab : SlabTestSet where
  plane := stdHyperplane
  thickness := 2

lemma unitBallSlab_carrier :
    unitBallSlab.carrier = Metric.closedBall (0 : Space3) 1 := by
  rw [SlabTestSet.carrier]
  apply Set.inter_eq_self_of_subset_left
  intro x hx
  have h0 : (0:Space3) ∈ (stdHyperplane.carrier : Set Space3) :=
    AffineSubspace.self_mem_mk' _ _
  have hx1 : dist x 0 ≤ 1 := by simpa using hx
  refine Metric.mem_cthickening_of_dist_le x 0 _ _ h0 ?_
  have h2 : ((unitBallSlab.thickness : NNReal) : ℝ) = 2 := by norm_num [unitBallSlab]
  rw [h2]
  simp only [dist_zero_right] at hx1 ⊢
  linarith

lemma inv_volume_unitBall_le_frostmanSlabWolffConstant {δ : NNReal} {ι : Type u}
    (s : Finset ι) (T : ι → ShadedTube δ Space3) (hs : s.Nonempty)
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : Space3) 1) :
    (volume (Metric.closedBall (0 : Space3) 1))⁻¹ ≤ frostmanSlabWolffConstant s T := by
  have hB0 := volume_unitBall_ne_zero
  have hBtop := volume_unitBall_ne_top
  rw [frostmanSlabWolffConstant]
  refine le_sInf ?_
  rintro C ⟨hC0, hC⟩
  have hfilter : (@Finset.filter ι (fun i => (T i).carrier ⊆ unitBallSlab.carrier)
      (Classical.decPred _) s) = s :=
    @Finset.filter_true_of_mem ι (fun i => (T i).carrier ⊆ unitBallSlab.carrier)
      (Classical.decPred _) s (fun i hi => by
        rw [unitBallSlab_carrier]; exact hball i hi)
  have h := hC unitBallSlab
  rw [hfilter, unitBallSlab_carrier] at h
  have hA0 : ((s.card : ENNReal)) ≠ 0 := by
    simpa using Finset.card_ne_zero_of_mem hs.choose_spec
  have hAtop : ((s.card : ENNReal)) ≠ ⊤ := by simp
  have h' : (1 : ENNReal) * (s.card : ENNReal) ≤
      (C * volume (Metric.closedBall (0 : Space3) 1)) * (s.card : ENNReal) := by
    rw [one_mul]; exact h
  have h1 : (1 : ENNReal) ≤ C * volume (Metric.closedBall (0 : Space3) 1) :=
    (ENNReal.mul_le_mul_iff_left hA0 hAtop).mp h'
  calc (volume (Metric.closedBall (0 : Space3) 1))⁻¹
      = 1 * (volume (Metric.closedBall (0 : Space3) 1))⁻¹ := (one_mul _).symm
    _ ≤ (C * volume (Metric.closedBall (0 : Space3) 1)) *
          (volume (Metric.closedBall (0 : Space3) 1))⁻¹ := by gcongr
    _ = C := by
        rw [mul_assoc, ENNReal.mul_inv_cancel hB0 hBtop, mul_one]

lemma tubeVolume_mul_le_volume_iUnionShade {δ : NNReal} {ι : Type u}
    (s : Finset ι) (T : ι → ShadedTube δ Space3) (hs : s.Nonempty) {c : NNReal}
    (hdense : IsDense s T c) :
    (c : ENNReal) * tubeVolume δ ≤
      volume (ShadedBody.iUnionShade s fun i => (T i).toShadedBody) := by
  set U : ENNReal := volume (ShadedBody.iUnionShade s fun i => (T i).toShadedBody) with hU
  have hA0 : ((s.card : ENNReal)) ≠ 0 := by
    simpa using Finset.card_ne_zero_of_mem hs.choose_spec
  have hAtop : ((s.card : ENNReal)) ≠ ⊤ := by simp
  have hshade : ∀ i ∈ s, volume (T i).shade ≤ U := by
    intro i hi
    refine measure_mono ?_
    exact Set.subset_biUnion_of_mem (u := fun j => (T j).toShadedBody.shade) hi
  have hsum : ∑ i ∈ s, volume (T i).shade ≤ (s.card : ENNReal) * U := by
    calc ∑ i ∈ s, volume (T i).shade ≤ ∑ _i ∈ s, U := Finset.sum_le_sum hshade
      _ = (s.card : ENNReal) * U := by rw [Finset.sum_const, nsmul_eq_mul]
  have hcarrier : ∑ i ∈ s, volume (T i).carrier = (s.card : ENNReal) * tubeVolume δ := by
    rw [Finset.sum_congr rfl (fun i _ => volume_carrier_eq_tubeVolume T i),
      Finset.sum_const, nsmul_eq_mul]
  have h1 : (c : ENNReal) * ((s.card : ENNReal) * tubeVolume δ) ≤ (s.card : ENNReal) * U := by
    rw [← hcarrier]
    exact le_trans hdense hsum
  have h2 : ((c : ENNReal) * tubeVolume δ) * (s.card : ENNReal) ≤ U * (s.card : ENNReal) := by
    calc ((c : ENNReal) * tubeVolume δ) * (s.card : ENNReal)
        = (c : ENNReal) * ((s.card : ENNReal) * tubeVolume δ) := by ring
      _ ≤ (s.card : ENNReal) * U := h1
      _ = U * (s.card : ENNReal) := by ring
  exact (ENNReal.mul_le_mul_iff_left hA0 hAtop).mp h2

lemma mul4_rpow {a b c d : ENNReal} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (z : ℝ) : (a * b * c * d) ^ z = a ^ z * b ^ z * c ^ z * d ^ z := by
  rw [ENNReal.mul_rpow_of_ne_zero (mul_ne_zero (mul_ne_zero ha hb) hc) hd,
    ENNReal.mul_rpow_of_ne_zero (mul_ne_zero ha hb) hc,
    ENNReal.mul_rpow_of_ne_zero ha hb]

lemma mul3_rpow {a b c : ENNReal} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (z : ℝ) : (a * b * c) ^ z = a ^ z * b ^ z * c ^ z := by
  rw [ENNReal.mul_rpow_of_ne_zero (mul_ne_zero ha hb) hc,
    ENNReal.mul_rpow_of_ne_zero ha hb]

lemma inv_rpow_eq {a : ENNReal} (z : ℝ) : (a⁻¹) ^ z = a ^ (-z) := by
  rw [ENNReal.inv_rpow, ← ENNReal.rpow_neg]

lemma efactor_le {m ell A V B : ENNReal} {σ : ℝ}
    (hσ0 : 0 ≤ σ) (hσ23 : σ ≤ 2 / 3)
    (hm0 : m ≠ 0) (hmtop : m ≠ ⊤)
    (hA0 : A ≠ 0) (hAtop : A ≠ ⊤)
    (hV0 : V ≠ 0) (hVtop : V ≠ ⊤)
    (hB0 : B ≠ 0) (hBtop : B ≠ ⊤)
    (hAV : A * V ≤ m * B) (hell : B⁻¹ ≤ ell) :
    m ^ (-1 : ℝ) * A * V * (m ^ (-3 / 2 : ℝ) * ell * A * V ^ (1 / 2 : ℝ)) ^ (-σ)
      ≤ B ^ (1 - σ / 2) * (A ^ (σ / 2) * V ^ σ) := by
  have hm32 : m ^ (-3 / 2 : ℝ) ≠ 0 := by
    simp [ENNReal.rpow_eq_zero_iff, hm0, hmtop]
  have hBinv0 : (B⁻¹ : ENNReal) ≠ 0 := ENNReal.inv_ne_zero.mpr hBtop
  have hVhalf0 : V ^ (1 / 2 : ℝ) ≠ 0 := by
    simp [ENNReal.rpow_eq_zero_iff, hV0, hVtop]
  have hstep1 : (m ^ (-3 / 2 : ℝ) * ell * A * V ^ (1 / 2 : ℝ)) ^ (-σ)
      ≤ (m ^ (-3 / 2 : ℝ) * B⁻¹ * A * V ^ (1 / 2 : ℝ)) ^ (-σ) := by
    refine rpow_le_rpow_of_nonpos ?_ (by linarith)
    gcongr
  have hexp : (m ^ (-3 / 2 : ℝ) * B⁻¹ * A * V ^ (1 / 2 : ℝ)) ^ (-σ)
      = m ^ (3 * σ / 2) * B ^ σ * A ^ (-σ) * V ^ (-σ / 2) := by
    rw [mul4_rpow hm32 hBinv0 hA0 hVhalf0]
    congr 1
    · congr 1
      · congr 1
        · rw [← ENNReal.rpow_mul]; ring_nf
        · rw [inv_rpow_eq]; ring_nf
    · rw [← ENNReal.rpow_mul]; ring_nf
  have hmul : ∀ {x : ENNReal}, x ≠ 0 → x ≠ ⊤ → ∀ y z : ℝ,
      x ^ y * x ^ z = x ^ (y + z) := by
    intro x hx0 hxtop y z
    rw [← ENNReal.rpow_add _ _ hx0 hxtop]
  have hone : ∀ {x : ENNReal}, x = x ^ (1 : ℝ) := by
    intro x; rw [ENNReal.rpow_one]
  have hle : A * V * B⁻¹ ≤ m := by
    calc A * V * B⁻¹ ≤ (m * B) * B⁻¹ := by gcongr
      _ = m := by rw [mul_assoc, ENNReal.mul_inv_cancel hB0 hBtop, mul_one]
  have hmle : m ^ (3 * σ / 2 - 1) ≤ (A * V * B⁻¹) ^ (3 * σ / 2 - 1) :=
    rpow_le_rpow_of_nonpos hle (by linarith)
  have hexp2 : (A * V * B⁻¹) ^ (3 * σ / 2 - 1)
      = A ^ (3 * σ / 2 - 1) * V ^ (3 * σ / 2 - 1) * B ^ (1 - 3 * σ / 2) := by
    rw [mul3_rpow hA0 hV0 hBinv0, inv_rpow_eq]
    congr 2
    ring
  calc m ^ (-1 : ℝ) * A * V * (m ^ (-3 / 2 : ℝ) * ell * A * V ^ (1 / 2 : ℝ)) ^ (-σ)
      ≤ m ^ (-1 : ℝ) * A * V * (m ^ (-3 / 2 : ℝ) * B⁻¹ * A * V ^ (1 / 2 : ℝ)) ^ (-σ) := by
        gcongr
    _ = m ^ (-1 : ℝ) * A * V * (m ^ (3 * σ / 2) * B ^ σ * A ^ (-σ) * V ^ (-σ / 2)) := by
        rw [hexp]
    _ = (m ^ (-1 : ℝ) * m ^ (3 * σ / 2)) * (A ^ (1 : ℝ) * A ^ (-σ)) *
          (V ^ (1 : ℝ) * V ^ (-σ / 2)) * B ^ σ := by
        rw [← hone, ← hone]; ring
    _ = m ^ ((-1 : ℝ) + 3 * σ / 2) * A ^ ((1 : ℝ) + -σ) * V ^ ((1 : ℝ) + -σ / 2) * B ^ σ := by
        rw [hmul hm0 hmtop, hmul hA0 hAtop, hmul hV0 hVtop]
    _ = m ^ (3 * σ / 2 - 1) * A ^ (1 - σ) * V ^ (1 - σ / 2) * B ^ σ := by
        rw [show (-1 : ℝ) + 3 * σ / 2 = 3 * σ / 2 - 1 from by ring,
          show (1 : ℝ) + -σ = 1 - σ from by ring,
          show (1 : ℝ) + -σ / 2 = 1 - σ / 2 from by ring]
    _ ≤ (A ^ (3 * σ / 2 - 1) * V ^ (3 * σ / 2 - 1) * B ^ (1 - 3 * σ / 2)) *
          A ^ (1 - σ) * V ^ (1 - σ / 2) * B ^ σ := by
        rw [← hexp2]; gcongr
    _ = (A ^ (3 * σ / 2 - 1) * A ^ (1 - σ)) * (V ^ (3 * σ / 2 - 1) * V ^ (1 - σ / 2)) *
          (B ^ (1 - 3 * σ / 2) * B ^ σ) := by ring
    _ = A ^ (3 * σ / 2 - 1 + (1 - σ)) * V ^ (3 * σ / 2 - 1 + (1 - σ / 2)) *
          B ^ (1 - 3 * σ / 2 + σ) := by
        rw [hmul hA0 hAtop, hmul hV0 hVtop, hmul hB0 hBtop]
    _ = A ^ (σ / 2) * V ^ σ * B ^ (1 - σ / 2) := by
        rw [show 3 * σ / 2 - 1 + (1 - σ) = σ / 2 from by ring,
          show 3 * σ / 2 - 1 + (1 - σ / 2) = σ from by ring,
          show 1 - 3 * σ / 2 + σ = 1 - σ / 2 from by ring]
    _ = B ^ (1 - σ / 2) * (A ^ (σ / 2) * V ^ σ) := by ring

/-- The volume lower bound `c * delta ^ 2 <= |T|` in rpow form. -/
lemma tubeVolume_lower {δ : NNReal} :
    ((Tube.le_volume.c 3 : NNReal) : ENNReal) * (δ : ENNReal) ^ (2 : ℝ) ≤ tubeVolume δ := by
  have hlow : ((Tube.le_volume.c 3 : NNReal) : ENNReal) * (δ : ENNReal) ^ (3 - 1 : ℕ) ≤
      tubeVolume δ := by
    simpa [tubeVolume] using Tube.le_volume (modelTube δ)
  have : (δ : ENNReal) ^ (3 - 1 : ℕ) = (δ : ENNReal) ^ (2 : ℝ) := by
    rw [show (3 - 1 : ℕ) = 2 from rfl, ← ENNReal.rpow_natCast (δ : ENNReal) 2]
    norm_num
  rwa [this] at hlow

theorem assertionE_two {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ23 : σ ≤ 2 / 3) : AssertionE.{u} σ 2 := by
  intro ε hε
  set B : ENNReal := volume (Metric.closedBall (0 : Space3) 1) with hBdef
  have hB0 : B ≠ 0 := volume_unitBall_ne_zero
  have hBtop : B ≠ ⊤ := volume_unitBall_ne_top
  set Cb : ENNReal := ((Kakeya.ml1Boot.cardBound.C : NNReal) : ENNReal) with hCbdef
  have hCb0 : Cb ≠ 0 := by
    simp only [hCbdef, ne_eq, ENNReal.coe_eq_zero]
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one Kakeya.ml1Boot.cardBound.one_le_C)
  have hCbtop : Cb ≠ ⊤ := ENNReal.coe_ne_top
  set cV : ENNReal := ((Tube.le_volume.c 3 : NNReal) : ENNReal) with hcVdef
  have hcV0 : cV ≠ 0 := by
    simp only [hcVdef, ne_eq, ENNReal.coe_eq_zero]
    exact (Tube.le_volume.c_pos 3).ne'
  have hcVtop : cV ≠ ⊤ := ENNReal.coe_ne_top
  set K : ENNReal := B ^ (1 - σ / 2) * Cb ^ (σ / 2) * cV ^ (σ - 1) with hKdef
  have hK0 : K ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_ <;>
      simp [ENNReal.rpow_eq_zero_iff, hB0, hBtop, hCb0, hCbtop, hcV0, hcVtop]
  have hKtop : K ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top ?_ ?_) ?_ <;>
      simp [ENNReal.rpow_eq_top_iff, hB0, hBtop, hCb0, hCbtop, hcV0, hcVtop]
  set M : NNReal := max 1 K.toNNReal with hMdef
  have hM1 : (1 : NNReal) ≤ M := le_max_left _ _
  have hM0 : M ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hM1)
  have hKM : K ≤ (M : ENNReal) := by
    have h1 : (K.toNNReal : ENNReal) = K := ENNReal.coe_toNNReal hKtop
    rw [← h1]
    exact_mod_cast le_max_right (1 : NNReal) K.toNNReal
  refine ⟨M⁻¹, ε, by positivity, hε, ?_⟩
  intro δ hδ ι s T hfamily hdense m ell
  by_cases hs : s.Nonempty
  · -- the tubes live in the unit ball, so `δ ≤ 1`
    obtain ⟨i0, hi0⟩ := hs
    have hs : s.Nonempty := ⟨i0, hi0⟩
    have hδ1 : δ ≤ 1 :=
      delta_le_one_of_tube_subset_unitBall (T i0).toTube (hfamily.1 i0 hi0)
    have hδ0E : (δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hδ.ne'
    have hδtopE : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
    have hδ1E : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
    set A : ENNReal := (s.card : ENNReal) with hAdef
    set V : ENNReal := tubeVolume δ with hVdef
    have hA0 : A ≠ 0 := by
      simpa [hAdef] using Finset.card_ne_zero_of_mem hi0
    have hAtop : A ≠ ⊤ := by simp [hAdef]
    have hVpos := tubeVolume_pos_and_ne_top hδ
    have hV0 : V ≠ 0 := hVpos.1.ne'
    have hVtop : V ≠ ⊤ := hVpos.2
    have hm1 : 1 ≤ m := one_le_katzTaoConvexWolffConstant_of_nonempty hδ s T hs
    have hm0 : m ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hm1)
    by_cases hmtop : m = ⊤
    · have hzero : m ^ (-1 : ℝ) = 0 := by
        rw [hmtop]; exact ENNReal.top_rpow_of_neg (by norm_num)
      simp [hzero]
    · have hAV : A * V ≤ m * B := card_mul_tubeVolume_le hδ s T hfamily.1 le_rfl
      have hell : B⁻¹ ≤ ell :=
        inv_volume_unitBall_le_frostmanSlabWolffConstant s T hs hfamily.1
      have hcore := efactor_le hσ0 hσ23 hm0 hmtop hA0 hAtop hV0 hVtop hB0 hBtop hAV hell
      -- the union lower bound
      have hdense' : ((δ ^ ε : NNReal) : ENNReal) = (δ : ENNReal) ^ ε :=
        ENNReal.coe_rpow_of_ne_zero hδ.ne' ε
      have hU : (δ : ENNReal) ^ ε * V ≤
          volume (ShadedBody.iUnionShade s fun i => (T i).toShadedBody) := by
        have h := tubeVolume_mul_le_volume_iUnionShade s T hs hdense
        rwa [show (⟨(δ : ℝ) ^ ε, Real.rpow_nonneg δ.coe_nonneg ε⟩ : NNReal) = δ ^ ε from rfl,
          hdense'] at h
      -- cardinality bound
      have hrank : Module.finrank ℝ Space3 = 3 := by simp [Space3]
      have hcard : A ≤ Cb * (δ : ENNReal) ^ (-4 : ℝ) :=
        Kakeya.ml1Boot.card_le hrank hδ hδ1 s (fun i => (T i).toTube) hfamily.1 hfamily.2
      have hApow : A ^ (σ / 2) ≤ Cb ^ (σ / 2) * (δ : ENNReal) ^ (-2 * σ) := by
        have h1 : A ^ (σ / 2) ≤ (Cb * (δ : ENNReal) ^ (-4 : ℝ)) ^ (σ / 2) :=
          ENNReal.rpow_le_rpow hcard (by linarith)
        refine h1.trans (le_of_eq ?_)
        rw [ENNReal.mul_rpow_of_ne_zero hCb0 (by simp [ENNReal.rpow_eq_zero_iff, hδ0E, hδtopE]),
          ← ENNReal.rpow_mul]
        congr 2
        ring
      have hVpow : V ^ σ ≤ cV ^ (σ - 1) * (δ : ENNReal) ^ (2 * σ - 2) * V := by
        have h1 : V ^ (σ - 1) ≤ (cV * (δ : ENNReal) ^ (2 : ℝ)) ^ (σ - 1) :=
          rpow_le_rpow_of_nonpos tubeVolume_lower (by linarith)
        have h2 : (cV * (δ : ENNReal) ^ (2 : ℝ)) ^ (σ - 1)
            = cV ^ (σ - 1) * (δ : ENNReal) ^ (2 * σ - 2) := by
          rw [ENNReal.mul_rpow_of_ne_zero hcV0 (by simp [hδ0E]), ← ENNReal.rpow_mul]
          congr 2
          ring
        have h3 : V ^ σ = V ^ (σ - 1) * V := by
          conv_lhs => rw [show σ = (σ - 1) + 1 from by ring]
          rw [ENNReal.rpow_add _ _ hV0 hVtop, ENNReal.rpow_one]
        rw [h3, ← h2]
        gcongr
      -- assemble
      have hdelta : (δ : ENNReal) ^ (2 + ε) * ((δ : ENNReal) ^ (-2 * σ) *
          (δ : ENNReal) ^ (2 * σ - 2)) = (δ : ENNReal) ^ ε := by
        rw [← ENNReal.rpow_add _ _ hδ0E hδtopE, ← ENNReal.rpow_add _ _ hδ0E hδtopE]
        congr 1
        ring
      have hkappa : ((M⁻¹ : NNReal) : ENNReal) * K ≤ 1 := by
        have hMcoe : ((M⁻¹ : NNReal) : ENNReal) = ((M : ENNReal))⁻¹ := by
          rw [ENNReal.coe_inv hM0]
        rw [hMcoe]
        calc ((M : ENNReal))⁻¹ * K ≤ ((M : ENNReal))⁻¹ * (M : ENNReal) := by gcongr
          _ = 1 := ENNReal.inv_mul_cancel (by exact_mod_cast hM0) ENNReal.coe_ne_top
      calc ((M⁻¹ : NNReal) : ENNReal) * (δ : ENNReal) ^ (2 + ε) * m ^ (-1 : ℝ) * A * V *
              (m ^ (-3 / 2 : ℝ) * ell * A * V ^ (1 / 2 : ℝ)) ^ (-σ)
          = (((M⁻¹ : NNReal) : ENNReal) * (δ : ENNReal) ^ (2 + ε)) *
              (m ^ (-1 : ℝ) * A * V *
                (m ^ (-3 / 2 : ℝ) * ell * A * V ^ (1 / 2 : ℝ)) ^ (-σ)) := by ring
        _ ≤ (((M⁻¹ : NNReal) : ENNReal) * (δ : ENNReal) ^ (2 + ε)) *
              (B ^ (1 - σ / 2) * (A ^ (σ / 2) * V ^ σ)) := by gcongr
        _ ≤ (((M⁻¹ : NNReal) : ENNReal) * (δ : ENNReal) ^ (2 + ε)) *
              (B ^ (1 - σ / 2) * ((Cb ^ (σ / 2) * (δ : ENNReal) ^ (-2 * σ)) *
                (cV ^ (σ - 1) * (δ : ENNReal) ^ (2 * σ - 2) * V))) := by gcongr
        _ = (((M⁻¹ : NNReal) : ENNReal) * K) *
              ((δ : ENNReal) ^ (2 + ε) * ((δ : ENNReal) ^ (-2 * σ) *
                (δ : ENNReal) ^ (2 * σ - 2))) * V := by rw [hKdef]; ring
        _ = (((M⁻¹ : NNReal) : ENNReal) * K) * ((δ : ENNReal) ^ ε) * V := by rw [hdelta]
        _ ≤ 1 * ((δ : ENNReal) ^ ε) * V := by gcongr
        _ = (δ : ENNReal) ^ ε * V := by rw [one_mul]
        _ ≤ _ := hU
  · have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    subst hs0
    simp [iUnionShade_empty]


/-! ### The Frostman *Convex* Wolff constant `CFC`

The project carries `katzTaoConvexWolffConstant` (`CKT`) and
`frostmanSlabWolffConstant` (`FS`) but not the third constant of Wang--Zahl
Remark `remarksFollowingConvexWolffDefn`(A)
(`blueprint/src/WZ2/250224e_K3.tex:952`), namely `CFC`, the *Frostman* Wolff
constant taken with respect to the convex test sets rather than the slabs.
`CFC` is the constant in which the source states its factoring trichotomy
(Proposition `tubeTricotProp`, :2284) and its "Frostman Convex Wolff Axioms at
every scale" (Definition `convexAtEveryScaleFromAssouadPaper`, :2257), so
without it neither is statable here.  It is supplied below. -/

/-  `frostmanConvexWolffConstant` (`CFC`) and
`frostmanSlabWolffConstant_le_frostmanConvexWolffConstant` now live in
`WangZahl/Rescaling.lean`, alongside the Wolff constants of a general convex
family and the rescaling map `phi_W` they are applied to; they are re-exported
through the import above. -/


/-! ### The tempered assertion `TE(sigma, omega)` -/

/-- Wang--Zahl Definition `TCEDefn` (`blueprint/src/WZ2/250224e_K3.tex:1550`),
Assertion `TE(sigma, omega)`.

It differs from `AssertionE` in exactly two places, both visible below:

* it *adds* the hypothesis `FS(T) <= delta^{-eta}` on the family (the source's
  "`ell` has size about 1" regime), and
* its currency drops the factor `ell`: the bracket raised to `-sigma` is
  `m^{-3/2} (#T) |T|^{1/2}` rather than `m^{-3/2} ell (#T) |T|^{1/2}`.

Source text: "For all `eps > 0`, there exists `kappa, eta > 0` such that the
following holds for all `delta > 0`.  Let `(T,Y)_delta` be `delta^eta` dense,
and suppose `FS(T) <= delta^{-eta}`.  Then
`|U Y(T)| >= kappa delta^{omega+eps} m^{-1} (#T)|T| (m^{-3/2}(#T)|T|^{1/2})^{-sigma}`,
where `m = CKT(T)`." -/
def AssertionTE (σ ω : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∃ κ : NNReal, ∃ η : ℝ, 0 < κ ∧ 0 < η ∧
    ∀ (δ : NNReal), 0 < δ →
      ∀ {ι : Type u} (s : Finset ι) (T : ι → ShadedTube δ Space3),
        IsTubeShadingFamily s T →
        IsDense s T ⟨(δ : ℝ) ^ η, Real.rpow_nonneg δ.coe_nonneg η⟩ →
        frostmanSlabWolffConstant s T ≤ (δ : ENNReal) ^ (-η) →
        let m := katzTaoConvexWolffConstant s T
        (κ : ENNReal) * (δ : ENNReal) ^ (ω + ε) * m ^ (-1 : ℝ) *
              (s.card : ENNReal) * tubeVolume δ *
              ((m ^ (-3 / 2 : ℝ) * (s.card : ENNReal) *
                (tubeVolume δ) ^ (1 / 2 : ℝ)) ^ (-σ)) ≤
          volume (ShadedBody.iUnionShade s fun i => (T i).toShadedBody)

/-- Increasing the loss exponent weakens Assertion `TE`, exactly as it weakens
Assertion `E` (`assertionE_mono_omega`). -/
theorem assertionTE_mono_omega {σ ω ω' : ℝ} (hω : ω ≤ ω') :
    AssertionTE.{u} σ ω → AssertionTE.{u} σ ω' := by
  intro hTE ε hε
  obtain ⟨κ, η, hκ, hη, hall⟩ := hTE (ε + (ω' - ω)) (by linarith)
  refine ⟨κ, η, hκ, hη, ?_⟩
  intro δ hδ ι s T hfamily hdense hell
  simpa only [show ω + (ε + (ω' - ω)) = ω' + ε by ring]
    using hall δ hδ s T hfamily hdense hell

/-- `E(sigma, omega) => TE(sigma, omega)`, the direction the source calls
trivial (Remark `discussionOfDRemark`, Situation 1, at
`blueprint/src/WZ2/250224e_K3.tex:1811`: "we have
`F(sigma,omega) => E(sigma,omega) => TE(sigma,omega)`").

Mechanically: the tempered currency `m^{-3/2}(#T)|T|^{1/2}` is the currency of
`E` divided by `ell`, and the added hypothesis `ell <= delta^{-eta}` bounds
that ratio, so the `-sigma` power costs only a factor `delta^{eta sigma}`,
absorbed into the accuracy parameter by taking `eta <= eps/(2(1+sigma))`.

Together with the unconditional `assertionE_two` this is the non-vacuity
certificate for `AssertionTE`: see `assertionTE_two`. -/
theorem assertionTE_of_assertionE {σ ω : ℝ} (hσ0 : 0 ≤ σ) :
    AssertionE.{u} σ ω → AssertionTE.{u} σ ω := by
  intro hE ε hε
  obtain ⟨κ, ηE, hκ, hηE, hall⟩ := hE (ε / 2) (by linarith)
  have hpos : (0 : ℝ) < ε / (2 * (1 + σ)) := by positivity
  refine ⟨κ, min ηE (ε / (2 * (1 + σ))), hκ, lt_min hηE hpos, ?_⟩
  set η : ℝ := min ηE (ε / (2 * (1 + σ))) with hηdef
  have hηE' : η ≤ ηE := min_le_left _ _
  have hηsmall : η ≤ ε / (2 * (1 + σ)) := min_le_right _ _
  have hη0 : 0 < η := lt_min hηE hpos
  have hησ : η * σ ≤ ε / 2 := by
    have h1 : η * (1 + σ) ≤ ε / (2 * (1 + σ)) * (1 + σ) :=
      mul_le_mul_of_nonneg_right hηsmall (by linarith : (0:ℝ) ≤ 1 + σ)
    have h2 : ε / (2 * (1 + σ)) * (1 + σ) = ε / 2 := by
      field_simp
    nlinarith [hη0.le, hσ0]
  intro δ hδ ι s T hfamily hdense hell m
  by_cases hs : s.Nonempty
  · obtain ⟨i0, hi0⟩ := hs
    have hs : s.Nonempty := ⟨i0, hi0⟩
    have hδ1 : δ ≤ 1 :=
      delta_le_one_of_tube_subset_unitBall (T i0).toTube (hfamily.1 i0 hi0)
    have hδ1E : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
    have hδ0E : (δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hδ.ne'
    have hδtopE : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
    have hnn : (⟨(δ : ℝ) ^ ηE, Real.rpow_nonneg δ.coe_nonneg ηE⟩ : NNReal) ≤
        ⟨(δ : ℝ) ^ η, Real.rpow_nonneg δ.coe_nonneg η⟩ :=
      NNReal.coe_le_coe.mp (Real.rpow_le_rpow_of_exponent_ge (by exact_mod_cast hδ)
        (by exact_mod_cast hδ1) hηE')
    have hdenseE : IsDense s T ⟨(δ : ℝ) ^ ηE, Real.rpow_nonneg δ.coe_nonneg ηE⟩ := by
      refine le_trans ?_ hdense
      gcongr
      exact hnn
    set ell : ENNReal := frostmanSlabWolffConstant s T with helldef
    set A : ENNReal := (s.card : ENNReal) with hAdef
    set V : ENNReal := tubeVolume δ with hVdef
    have hbound : (κ : ENNReal) * (δ : ENNReal) ^ (ω + ε / 2) * m ^ (-1 : ℝ) * A * V *
        ((m ^ (-3 / 2 : ℝ) * ell * A * V ^ (1 / 2 : ℝ)) ^ (-σ)) ≤
        volume (ShadedBody.iUnionShade s fun i => (T i).toShadedBody) :=
      hall δ hδ s T hfamily hdenseE
    have hA0 : A ≠ 0 := by simpa [hAdef] using Finset.card_ne_zero_of_mem hi0
    have hVpos := tubeVolume_pos_and_ne_top hδ
    have hV0 : V ≠ 0 := hVpos.1.ne'
    have hm1 : 1 ≤ m := one_le_katzTaoConvexWolffConstant_of_nonempty hδ s T hs
    have hm0 : m ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hm1)
    by_cases hmtop : m = ⊤
    · have hzero : m ^ (-1 : ℝ) = 0 := by
        rw [hmtop]; exact ENNReal.top_rpow_of_neg (by norm_num)
      simp [hzero]
    · have hm32 : m ^ (-3 / 2 : ℝ) ≠ 0 := by
        simp [ENNReal.rpow_eq_zero_iff, hm0, hmtop]
      have hVhalf0 : V ^ (1 / 2 : ℝ) ≠ 0 := by
        simp [ENNReal.rpow_eq_zero_iff, hV0]
      have hP0 : m ^ (-3 / 2 : ℝ) * A * V ^ (1 / 2 : ℝ) ≠ 0 :=
        mul_ne_zero (mul_ne_zero hm32 hA0) hVhalf0
      have hdinv0 : ((δ : ENNReal) ^ (-η)) ≠ 0 := by
        simp [ENNReal.rpow_eq_zero_iff, hδ0E, hδtopE]
      have hQP : m ^ (-3 / 2 : ℝ) * ell * A * V ^ (1 / 2 : ℝ) ≤
          (δ : ENNReal) ^ (-η) * (m ^ (-3 / 2 : ℝ) * A * V ^ (1 / 2 : ℝ)) := by
        calc m ^ (-3 / 2 : ℝ) * ell * A * V ^ (1 / 2 : ℝ)
            = ell * (m ^ (-3 / 2 : ℝ) * A * V ^ (1 / 2 : ℝ)) := by ring
          _ ≤ (δ : ENNReal) ^ (-η) * (m ^ (-3 / 2 : ℝ) * A * V ^ (1 / 2 : ℝ)) := by
              gcongr
      have hstep1 : ((δ : ENNReal) ^ (-η) * (m ^ (-3 / 2 : ℝ) * A * V ^ (1 / 2 : ℝ))) ^ (-σ) ≤
          (m ^ (-3 / 2 : ℝ) * ell * A * V ^ (1 / 2 : ℝ)) ^ (-σ) :=
        rpow_le_rpow_of_nonpos hQP (by linarith)
      have hsplit : ((δ : ENNReal) ^ (-η) * (m ^ (-3 / 2 : ℝ) * A * V ^ (1 / 2 : ℝ))) ^ (-σ)
          = (δ : ENNReal) ^ (η * σ) * (m ^ (-3 / 2 : ℝ) * A * V ^ (1 / 2 : ℝ)) ^ (-σ) := by
        rw [ENNReal.mul_rpow_of_ne_zero hdinv0 hP0, ← ENNReal.rpow_mul]
        congr 2
        ring
      have hδexp : (δ : ENNReal) ^ (ω + ε) ≤ (δ : ENNReal) ^ (ω + ε / 2 + η * σ) :=
        ENNReal.rpow_le_rpow_of_exponent_ge hδ1E (by linarith)
      calc (κ : ENNReal) * (δ : ENNReal) ^ (ω + ε) * m ^ (-1 : ℝ) * A * V *
              ((m ^ (-3 / 2 : ℝ) * A * V ^ (1 / 2 : ℝ)) ^ (-σ))
          ≤ (κ : ENNReal) * (δ : ENNReal) ^ (ω + ε / 2 + η * σ) * m ^ (-1 : ℝ) * A * V *
              ((m ^ (-3 / 2 : ℝ) * A * V ^ (1 / 2 : ℝ)) ^ (-σ)) := by gcongr
        _ = (κ : ENNReal) * (δ : ENNReal) ^ (ω + ε / 2) * m ^ (-1 : ℝ) * A * V *
              ((δ : ENNReal) ^ (η * σ) *
                (m ^ (-3 / 2 : ℝ) * A * V ^ (1 / 2 : ℝ)) ^ (-σ)) := by
              rw [ENNReal.rpow_add _ _ hδ0E hδtopE]; ring
        _ = (κ : ENNReal) * (δ : ENNReal) ^ (ω + ε / 2) * m ^ (-1 : ℝ) * A * V *
              (((δ : ENNReal) ^ (-η) *
                (m ^ (-3 / 2 : ℝ) * A * V ^ (1 / 2 : ℝ))) ^ (-σ)) := by rw [hsplit]
        _ ≤ (κ : ENNReal) * (δ : ENNReal) ^ (ω + ε / 2) * m ^ (-1 : ℝ) * A * V *
              ((m ^ (-3 / 2 : ℝ) * ell * A * V ^ (1 / 2 : ℝ)) ^ (-σ)) := by gcongr
        _ ≤ _ := hbound
  · have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    subst hs0
    simp [iUnionShade_empty]

/-- The tempered base estimate at exponent two.  With
`assertionTE_of_assertionE` this certifies that `AssertionTE` is satisfiable,
so no statement below is closed through an inconsistent hypothesis bundle. -/
theorem assertionTE_two {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ23 : σ ≤ 2 / 3) : AssertionTE.{u} σ 2 :=
  assertionTE_of_assertionE hσ0 (assertionE_two.{u} hσ0 hσ23)


/-! ### The uniform weak reverse step -/









end

end Kakeya.WangZahl
