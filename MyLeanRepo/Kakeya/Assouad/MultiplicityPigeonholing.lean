import MyLeanRepo.Kakeya.Assouad.MultiplicityRefinement
import MyLeanRepo.Kakeya.Assouad.Definitions

/-!
# Multiplicity pigeonholing and projection pullback infrastructure

Provides:
1. Dyadic pigeonholing of point multiplicity: find a band [2^k, 2^{k+1})
   capturing a 1/(log₂ N + 1) fraction of the shaded mass.
2. Dyadic band subshading and density absorption of the logarithmic loss.
3. Projection pullback shading: restrict a shading to the preimage of a
   measurable subset of its twisted projection.
4. Mass-ratio lemma for full restrictions with bounded multiplicity.
-/

noncomputable section

open MeasureTheory Set Finset

namespace Kakeya.Assouad

-- ============================================================================
-- Helper: every positive natural lies in a dyadic band
-- ============================================================================

/-- Every positive `m < 2^(K+1)` lies in some dyadic band `[2^k, 2^(k+1))` with `k ≤ K`. -/
lemma exists_dyadic_interval (m : ℕ) (hm_pos : 0 < m) (K : ℕ)
    (h : m < (2 : ℕ)^(K+1)) :
    ∃ k : ℕ, k ≤ K ∧ (2 : ℕ)^k ≤ m ∧ m < (2 : ℕ)^(k+1) := by
  induction K with
  | zero =>
    have h1 : m < 2 := by simpa [pow_one] using h
    have h2 : m = 1 := by omega
    refine ⟨0, by omega, ?_, ?_⟩ <;> omega
  | succ K ih =>
    by_cases h2 : m < (2 : ℕ)^(K+1)
    · rcases ih h2 with ⟨k, hk, h3, h4⟩
      refine ⟨k, by omega, h3, h4⟩
    · have h3 : (2 : ℕ)^(K+1) ≤ m := by omega
      refine ⟨K+1, by omega, h3, ?_⟩
      simpa [pow_succ] using h

-- ============================================================================
-- Section 1: Dyadic multiplicity pigeonholing
-- ============================================================================

/-- The set where point multiplicity lies in the half-open dyadic band `[2^k, 2^{k+1})`. -/
def dyadicMultiplicityBand
    {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    (Y : Kakeya.Streamlined.TubeShading F) (k : ℕ) : Set Point3 :=
  {p | ((2 : ℕ)^k : ENNReal) ≤ (Y.pointMultiplicity p : ENNReal) ∧
       (Y.pointMultiplicity p : ENNReal) < ((2 : ℕ)^(k+1) : ENNReal)}

lemma measurableSet_dyadicMultiplicityBand
    {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    (Y : Kakeya.Streamlined.TubeShading F) (k : ℕ) :
    MeasurableSet (dyadicMultiplicityBand Y k) := by
  let allowed : Set ℕ :=
    {n | ((2 : ℕ)^k : ENNReal) ≤ (n : ENNReal) ∧
         (n : ENNReal) < ((2 : ℕ)^(k+1) : ENNReal)}
  change MeasurableSet (Y.pointMultiplicity ⁻¹' allowed)
  exact MeasurableSet.preimage MeasurableSet.of_discrete
    (measurable_pointMultiplicity Y)

/-- Shaded mass carried by points whose multiplicity lies in a dyadic band. -/
def dyadicBandMass
    {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    (Y : Kakeya.Streamlined.TubeShading F) (k : ℕ) : ENNReal :=
  ∑ i : Fin F.toBodyFamily.card,
    MeasureTheory.volume (Y.carrier i ∩ dyadicMultiplicityBand Y k)

/-- Distinct dyadic bands are disjoint. -/
lemma dyadicBands_disjoint
    {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    (Y : Kakeya.Streamlined.TubeShading F) {k l : ℕ} (h : k ≠ l) :
    Disjoint (dyadicMultiplicityBand Y k) (dyadicMultiplicityBand Y l) := by
  have h_main : ∀ {a b : ℕ}, a < b →
      Disjoint (dyadicMultiplicityBand Y a) (dyadicMultiplicityBand Y b) := by
    intro a b hab
    have h3 : (2 : ℕ)^(a+1) ≤ (2 : ℕ)^b := by
      have h4 : a + 1 ≤ b := by omega
      gcongr <;> norm_num
    simp only [Set.disjoint_left, dyadicMultiplicityBand]
    intro p hpa
    have h4 : (Y.pointMultiplicity p : ENNReal) < ((2 : ℕ)^(a+1) : ENNReal) := hpa.2
    intro hpb
    have h5 : ((2 : ℕ)^b : ENNReal) ≤ (Y.pointMultiplicity p : ENNReal) := hpb.1
    have h6 : ((2 : ℕ)^(a+1) : ENNReal) ≤ ((2 : ℕ)^b : ENNReal) := by exact_mod_cast h3
    have h_contra : (Y.pointMultiplicity p : ENNReal) < (Y.pointMultiplicity p : ENNReal) := by
      calc
        (Y.pointMultiplicity p : ENNReal) < ((2 : ℕ)^(a+1) : ENNReal) := h4
        _ ≤ ((2 : ℕ)^b : ENNReal) := h6
        _ ≤ (Y.pointMultiplicity p : ENNReal) := h5
    exact lt_irrefl _ h_contra
  by_cases hkl : k < l
  · exact h_main hkl
  · by_cases hlk : l < k
    · exact (h_main hlk).symm
    · have h_eq : k = l := by omega
      exfalso; exact h h_eq

/-- For `K` with `F.card < 2^(K+1)`, the bands `k=0,…,K` cover `Y.union`. -/
lemma dyadicBands_cover
    {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    (Y : Kakeya.Streamlined.TubeShading F) {K : ℕ}
    (hK : F.card < (2 : ℕ)^(K+1)) :
    Y.union ⊆ ⋃ k ∈ Finset.range (K+1), dyadicMultiplicityBand Y k := by
  intro p hp
  have hmult_pos : 0 < Y.pointMultiplicity p := by
    rcases hp with ⟨i, hi⟩
    classical
    let f : Fin F.toBodyFamily.card → ℕ := fun j => if p ∈ Y.carrier j then 1 else 0
    have h1 : Y.pointMultiplicity p = ∑ j ∈ (Finset.univ : Finset (Fin F.toBodyFamily.card)), f j := by
      rw [Kakeya.Streamlined.Shading.pointMultiplicity, Finset.card_filter]
      <;> rfl
    rw [h1]
    have h2 : f i = 1 := by simp [f, hi]
    have h3 : f i ≤ ∑ j ∈ (Finset.univ : Finset (Fin F.toBodyFamily.card)), f j :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (f j)) (Finset.mem_univ i)
    rw [h2] at h3
    omega
  have hmult_le : Y.pointMultiplicity p ≤ F.card := by
    classical
    have h1 : Y.pointMultiplicity p =
        ∑ j ∈ (Finset.univ : Finset (Fin F.toBodyFamily.card)),
          if p ∈ Y.carrier j then (1 : ℕ) else 0 := by
      rw [Kakeya.Streamlined.Shading.pointMultiplicity, Finset.card_filter]
    rw [h1]
    have h2 : ∑ j ∈ (Finset.univ : Finset (Fin F.toBodyFamily.card)),
          (if p ∈ Y.carrier j then (1 : ℕ) else 0) ≤
        ∑ j ∈ (Finset.univ : Finset (Fin F.toBodyFamily.card)), (1 : ℕ) := by
      apply Finset.sum_le_sum
      intro j _
      split_ifs <;> omega
    have h3 : ∑ j ∈ (Finset.univ : Finset (Fin F.toBodyFamily.card)), (1 : ℕ) = F.toBodyFamily.card := by
      simp
    rw [h3] at h2
    exact h2
  rcases exists_dyadic_interval (Y.pointMultiplicity p) hmult_pos K
      (by omega) with ⟨k, hk_le, h1, h2⟩
  have h5 : k ∈ Finset.range (K+1) := by
    simp only [Finset.mem_range] <;> omega
  have h1' : ((2 : ℕ)^k : ENNReal) ≤ (Y.pointMultiplicity p : ENNReal) := by
    exact_mod_cast h1
  have h2' : (Y.pointMultiplicity p : ENNReal) < ((2 : ℕ)^(k+1) : ENNReal) := by
    exact_mod_cast h2
  have h6 : p ∈ dyadicMultiplicityBand Y k := ⟨h1', h2'⟩
  exact Set.mem_iUnion₂.mpr ⟨k, h5, h6⟩

/-- Sum of band masses over `k=0,…,K` equals total shaded mass. -/
lemma sum_dyadicBandMass
    {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    (Y : Kakeya.Streamlined.TubeShading F) {K : ℕ}
    (hK : F.card < (2 : ℕ)^(K+1)) :
    ∑ k ∈ Finset.range (K+1), dyadicBandMass Y k = Y.mass := by
  have h_disj : ∀ (i : Fin F.toBodyFamily.card),
      Set.PairwiseDisjoint (Finset.range (K+1) : Set ℕ)
        (fun k => Y.carrier i ∩ dyadicMultiplicityBand Y k) := by
    intro i k _ l _ hne
    exact (dyadicBands_disjoint Y hne).mono
      (Set.inter_subset_right) (Set.inter_subset_right)
  have h_meas : ∀ (i : Fin F.toBodyFamily.card) (k : ℕ),
      MeasurableSet (Y.carrier i ∩ dyadicMultiplicityBand Y k) := by
    intro i k
    exact (Y.measurable_carrier i).inter
      (measurableSet_dyadicMultiplicityBand Y k)
  have h_cover : ∀ (i : Fin F.toBodyFamily.card),
      Y.carrier i ⊆ ⋃ k ∈ Finset.range (K+1),
        (Y.carrier i ∩ dyadicMultiplicityBand Y k) := by
    intro i p hp
    have hp' : p ∈ Y.union := ⟨i, hp⟩
    have hcov : p ∈ (⋃ k ∈ Finset.range (K+1), dyadicMultiplicityBand Y k) :=
      dyadicBands_cover Y hK hp'
    have hcov' : ∃ (k : ℕ) (h : k ∈ Finset.range (K+1)), p ∈ dyadicMultiplicityBand Y k :=
      Set.mem_iUnion₂.mp hcov
    rcases hcov' with ⟨k, hkr, hband⟩
    exact Set.mem_iUnion₂.mpr ⟨k, hkr, ⟨hp, hband⟩⟩
  have h_eq : ∀ (i : Fin F.toBodyFamily.card),
      MeasureTheory.volume (Y.carrier i) =
        ∑ k ∈ Finset.range (K+1),
          MeasureTheory.volume (Y.carrier i ∩ dyadicMultiplicityBand Y k) := by
    intro i
    have h_union : Y.carrier i =
        ⋃ k ∈ Finset.range (K+1),
          (Y.carrier i ∩ dyadicMultiplicityBand Y k) := by
      apply Set.Subset.antisymm
      · exact h_cover i
      · intro p hp
        have hp' : ∃ (k : ℕ) (h : k ∈ Finset.range (K+1)), p ∈ (Y.carrier i ∩ dyadicMultiplicityBand Y k) :=
          Set.mem_iUnion₂.mp hp
        rcases hp' with ⟨k, hkr, hpk⟩
        exact hpk.1
    have h_main_eq : MeasureTheory.volume (⋃ k ∈ Finset.range (K+1), (Y.carrier i ∩ dyadicMultiplicityBand Y k)) =
        ∑ k ∈ Finset.range (K+1), MeasureTheory.volume (Y.carrier i ∩ dyadicMultiplicityBand Y k) :=
      MeasureTheory.measure_biUnion_finset (h_disj i) (fun k _ => h_meas i k)
    have h1 : MeasureTheory.volume (Y.carrier i) =
        MeasureTheory.volume (⋃ k ∈ Finset.range (K+1), (Y.carrier i ∩ dyadicMultiplicityBand Y k)) :=
      congr_arg MeasureTheory.volume h_union
    exact Eq.trans h1 h_main_eq
  calc
    ∑ k ∈ Finset.range (K+1), dyadicBandMass Y k
      = ∑ k ∈ Finset.range (K+1), ∑ i : Fin F.toBodyFamily.card,
          MeasureTheory.volume (Y.carrier i ∩ dyadicMultiplicityBand Y k) := by
        apply Finset.sum_congr rfl
        intro k _
        rfl
    _ = ∑ i : Fin F.toBodyFamily.card, ∑ k ∈ Finset.range (K+1),
          MeasureTheory.volume (Y.carrier i ∩ dyadicMultiplicityBand Y k) := by
        rw [Finset.sum_comm]
    _ = ∑ i : Fin F.toBodyFamily.card, MeasureTheory.volume (Y.carrier i) := by
        apply Finset.sum_congr rfl
        intro i _
        exact (h_eq i).symm
    _ = Y.mass := rfl

/--
**Dyadic multiplicity pigeonholing.**

There exists a dyadic band `[2^k, 2^{k+1})` whose shaded mass is at least
`Y.mass / (log₂ F.card + 1)`.
-/
lemma dyadic_multiplicity_pigeonhole
    {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    (Y : Kakeya.Streamlined.TubeShading F)
    (hN_pos : 0 < F.card) :
    ∃ (k K : ℕ), (2 : ℕ)^K ≤ F.card ∧ F.card < (2 : ℕ)^(K+1) ∧
      ((K + 1 : ℕ) : ENNReal) * dyadicBandMass Y k ≥ Y.mass := by
  set N : ℕ := F.card with hN
  have hN_pos' : 0 < N := by simpa [hN] using hN_pos
  set K : ℕ := Nat.log 2 N with hK
  have hK_lt : N < (2 : ℕ)^(K+1) :=
    Nat.lt_pow_succ_log_self (by norm_num) N
  have h_sum : ∑ k ∈ Finset.range (K+1), dyadicBandMass Y k = Y.mass :=
    sum_dyadicBandMass Y (by simpa [hN] using hK_lt)
  have h_nonempty : (Finset.range (K+1)).Nonempty := by
    simp <;> omega
  have h_max : ∃ k ∈ Finset.range (K+1),
      ∀ l ∈ Finset.range (K+1), dyadicBandMass Y l ≤ dyadicBandMass Y k :=
    Finset.exists_max_image (Finset.range (K+1))
      (fun k => dyadicBandMass Y k) h_nonempty
  rcases h_max with ⟨k, hk, hmax⟩
  have h_le : ∑ l ∈ Finset.range (K+1), dyadicBandMass Y l ≤
      (Finset.range (K+1)).card * dyadicBandMass Y k := by
    calc
      ∑ l ∈ Finset.range (K+1), dyadicBandMass Y l
        ≤ ∑ l ∈ Finset.range (K+1), dyadicBandMass Y k := by
          apply Finset.sum_le_sum
          intro l hl
          exact hmax l hl
      _ = (Finset.range (K+1)).card * dyadicBandMass Y k := by
          simp [Finset.sum_const] <;> ring
  have h_card : (Finset.range (K+1)).card = K + 1 := by simp
  rw [h_card] at h_le
  rw [h_sum] at h_le
  have hkle : k ≤ K := by
    have h : k ∈ Finset.range (K+1) := hk
    simp only [Finset.mem_range] at h <;> omega
  have h_final : ((K + 1 : ℕ) : ENNReal) * dyadicBandMass Y k ≥ Y.mass := by
    simpa [hK] using h_le
  have hK_le : (2 : ℕ)^K ≤ N := Nat.pow_log_le_self 2 (show N ≠ 0 from by omega)
  exact ⟨k, K, by simpa [hN] using hK_le, by simpa [hN] using hK_lt, h_final⟩

-- ============================================================================
-- Section 2: Dyadic band subshading and density absorption
-- ============================================================================

/-- Restrict a shading to its dyadic multiplicity band `[2^k, 2^{k+1})`. -/
def dyadicBandSubshading
    {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    (Y : Kakeya.Streamlined.TubeShading F) (k : ℕ) :
    Kakeya.Streamlined.TubeShading F where
  carrier i := Y.carrier i ∩ dyadicMultiplicityBand Y k
  measurable_carrier i :=
    (Y.measurable_carrier i).inter (measurableSet_dyadicMultiplicityBand Y k)
  subset_body i :=
    Set.inter_subset_left.trans (Y.subset_body i)

lemma dyadicBandSubshading_isSubshading
    {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    (Y : Kakeya.Streamlined.TubeShading F) (k : ℕ) :
    IsSubshading (dyadicBandSubshading Y k) Y := by
  intro i
  exact Set.inter_subset_left

lemma dyadicBandSubshading_mass
    {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    (Y : Kakeya.Streamlined.TubeShading F) (k : ℕ) :
    (dyadicBandSubshading Y k).mass = dyadicBandMass Y k := by
  rfl

/--
Absorb the logarithmic pigeonholing loss into a weaker density exponent.

Given `Y` is `δ^η`-dense and band mass ≥ `Y.mass / (log F.card + 1)`,
if `log F.card + 1 ≤ δ^{-(η'-η)}` (with `η' > η`), then the band mass
is at least `δ^{η'} · F.mass`.
-/
lemma band_mass_density_absorption
    {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    (Y : Kakeya.Streamlined.TubeShading F)
    (eta eta' : ℝ) (hδ : 0 < δ)
    (heta : 0 < eta) (heta' : eta < eta')
    (hY_dense : Y.IsLambdaDense (Kakeya.realRpowENN δ eta))
    (bandMass L : ENNReal)
    (hband : L * bandMass ≥ Y.mass)
    (hlog : L ≤ Kakeya.realRpowENN δ (eta - eta')) :
    bandMass ≥ Kakeya.realRpowENN δ eta' * F.toBodyFamily.mass := by
  have hL_top : L ≠ ⊤ := by
    have hfin : Kakeya.realRpowENN δ (eta - eta') ≠ ⊤ := by
      simp [Kakeya.realRpowENN, ENNReal.ofReal_ne_top]
    exact ne_top_of_le_ne_top hfin hlog
  have h1 : bandMass ≥ Y.mass * L⁻¹ := by
    have h2 : L * bandMass ≥ Y.mass := hband
    by_cases hL0 : L = 0
    · have hY0 : Y.mass = 0 := by simpa [hL0] using h2
      rw [hY0, hL0] <;> simp
    · calc
        bandMass = L⁻¹ * (L * bandMass) := by
          exact Eq.symm (ENNReal.inv_mul_cancel_left hL0 hL_top)
        _ ≥ L⁻¹ * Y.mass := by gcongr
        _ = Y.mass * L⁻¹ := by rw [mul_comm]
  have h4 : Y.mass ≥ Kakeya.realRpowENN δ eta * F.toBodyFamily.mass := hY_dense
  have h5 : L⁻¹ ≥ (Kakeya.realRpowENN δ (eta - eta'))⁻¹ := by gcongr
  let a : ENNReal := Kakeya.realRpowENN δ (eta' - eta)
  have ha0 : a ≠ 0 := by
    have hpos : 0 < Real.rpow δ (eta' - eta) := Real.rpow_pos_of_pos hδ (eta' - eta)
    have h : ¬(Real.rpow δ (eta' - eta) ≤ 0) := by linarith
    simpa [a, Kakeya.realRpowENN, ENNReal.ofReal_eq_zero] using h
  have ha_top : a ≠ ⊤ := by
    simp [a, Kakeya.realRpowENN, ENNReal.ofReal_ne_top]
  have hneg : Real.rpow δ (eta - eta') = (Real.rpow δ (eta' - eta))⁻¹ := by
    have hsum : Real.rpow δ ((eta - eta') + (eta' - eta)) =
        Real.rpow δ (eta - eta') * Real.rpow δ (eta' - eta) :=
      Real.rpow_add (by linarith) (eta - eta') (eta' - eta)
    have hzero : (eta - eta') + (eta' - eta) = 0 := by ring
    have h5 : Real.rpow δ ((eta - eta') + (eta' - eta)) = 1 := by
      rw [hzero]
      <;> simp
    have hprod : Real.rpow δ (eta - eta') * Real.rpow δ (eta' - eta) = 1 := by
      rw [← hsum, h5]
    exact eq_inv_of_mul_eq_one_left hprod
  have h_eq1 : Kakeya.realRpowENN δ (eta - eta') = a⁻¹ := by
    simp only [Kakeya.realRpowENN, a]
    rw [hneg]
    have h_pos : 0 < Real.rpow δ (eta' - eta) := Real.rpow_pos_of_pos hδ (eta' - eta)
    have h_ofReal_inv : ENNReal.ofReal ((Real.rpow δ (eta' - eta))⁻¹) =
        (ENNReal.ofReal (Real.rpow δ (eta' - eta)))⁻¹ :=
      ENNReal.ofReal_inv_of_pos h_pos
    exact h_ofReal_inv
  have h6 : (Kakeya.realRpowENN δ (eta - eta'))⁻¹ = a := by
    rw [h_eq1]
    have h_div : a⁻¹ = 1 / a := by simp [div_eq_mul_inv]
    rw [h_div]
    have h : (1 / a)⁻¹ = a / 1 :=
      ENNReal.inv_div (Or.inr (by simp)) (Or.inr (by simp))
    rw [h]
    <;> simp
  have h7 : Kakeya.realRpowENN δ eta * a =
              Kakeya.realRpowENN δ eta' := by
    simp only [Kakeya.realRpowENN, a]
    have h1 : Real.rpow δ (eta + (eta' - eta)) =
        Real.rpow δ eta * Real.rpow δ (eta' - eta) :=
      Real.rpow_add (by linarith) eta (eta' - eta)
    have ha : 0 ≤ Real.rpow δ eta := Real.rpow_nonneg (by linarith) eta
    have hb : 0 ≤ Real.rpow δ (eta' - eta) := Real.rpow_nonneg (by linarith) (eta' - eta)
    have h9 : eta + (eta' - eta) = eta' := by ring
    rw [h9] at h1
    rw [h1, ← ENNReal.ofReal_mul ha] <;> rfl
  calc
    bandMass
      ≥ Y.mass * L⁻¹ := h1
    _ ≥ (Kakeya.realRpowENN δ eta * F.toBodyFamily.mass) * L⁻¹ := by gcongr
    _ ≥ (Kakeya.realRpowENN δ eta * F.toBodyFamily.mass) * a := by
        rw [h6] at h5 <;> gcongr
    _ = Kakeya.realRpowENN δ eta * a * F.toBodyFamily.mass := by
        have h : (Kakeya.realRpowENN δ eta * F.toBodyFamily.mass) * a =
            Kakeya.realRpowENN δ eta * a * F.toBodyFamily.mass := by
          rw [mul_assoc, mul_comm (F.toBodyFamily.mass) a, ← mul_assoc]
        exact h
    _ = Kakeya.realRpowENN δ eta' * F.toBodyFamily.mass := by
        rw [h7]

-- ============================================================================
-- Section 3: Projection pullback shading
-- ============================================================================

/--
Restrict every shaded carrier to the preimage of a measurable subset `X`
of the twisted projection.
-/
def projectionPullbackShading
    {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    (Y : Kakeya.Streamlined.TubeShading F)
    (f : SlopeFunction)
    (X : Set Point2)
    (hX : MeasurableSet X) :
    Kakeya.Streamlined.TubeShading F where
  carrier i := Y.carrier i ∩ twistedProjection f ⁻¹' X
  measurable_carrier i :=
    (Y.measurable_carrier i).inter
      (hX.preimage (continuous_twistedProjection f).measurable)
  subset_body i :=
    Set.inter_subset_left.trans (Y.subset_body i)

/-- The pullback shading is a subshading of the original. -/
lemma projectionPullback_isSubshading
    {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    (Y : Kakeya.Streamlined.TubeShading F)
    (f : SlopeFunction) (X : Set Point2) (hX : MeasurableSet X) :
    IsSubshading (projectionPullbackShading Y f X hX) Y := by
  intro i
  exact Set.inter_subset_left

/-- The twisted image of the pullback shading is contained in `X`. -/
lemma projectionPullback_twistedUnion_subset
    {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    (Y : Kakeya.Streamlined.TubeShading F)
    (f : SlopeFunction) (X : Set Point2) (hX : MeasurableSet X) :
    twistedUnion (projectionPullbackShading Y f X hX) f ⊆ X := by
  intro q hq
  rcases hq with ⟨p, hp, rfl⟩
  rcases hp with ⟨i, hpi⟩
  exact hpi.2

/--
At every point in the preimage, the pullback shading retains ALL original
carriers, so its point multiplicity equals the original.
-/
lemma projectionPullback_fullRestriction
    {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    (Y : Kakeya.Streamlined.TubeShading F)
    (f : SlopeFunction) (X : Set Point2) (hX : MeasurableSet X)
    (p : Point3) (hp : p ∈ twistedProjection f ⁻¹' X) :
    (projectionPullbackShading Y f X hX).pointMultiplicity p =
      Y.pointMultiplicity p := by
  classical
  simp only [Kakeya.Streamlined.Shading.pointMultiplicity]
  congr 1
  apply Finset.filter_congr
  intro i _
  simp [projectionPullbackShading, hp]
  <;> tauto

-- ============================================================================
-- Section 4: Mass-ratio lemma for full restrictions
-- ============================================================================

/--
**Mass-ratio lemma for full restrictions.**

Let `Y` have pointwise multiplicity in `[λ, 2λ]` on its union.  Let `Z` be
a full restriction to a measurable set `S` (`Z.carrier i = Y.carrier i ∩ S`).
If `volume(Y.union ∩ S) ≥ c · volume(Y.union)`, then
`2 · Z.mass ≥ c · Y.mass`.
-/
lemma fullRestriction_mass_ratio
    {δ : ℝ} {F : Kakeya.Streamlined.TubeFamily δ}
    (Y : Kakeya.Streamlined.TubeShading F)
    (Z : Kakeya.Streamlined.TubeShading F)
    (S : Set Point3) (hS : MeasurableSet S)
    (hZ : ∀ i, Z.carrier i = Y.carrier i ∩ S)
    (lambda c : ENNReal)
    (hlower : ∀ p ∈ Y.union, lambda ≤ (Y.pointMultiplicity p : ENNReal))
    (hupper : ∀ p ∈ Y.union, (Y.pointMultiplicity p : ENNReal) ≤ 2 * lambda)
    (hvol : MeasureTheory.volume (Y.union ∩ S) ≥
              c * MeasureTheory.volume Y.union) :
    2 * Z.mass ≥ c * Y.mass := by
  let m : Point3 → ENNReal := fun p => (Y.pointMultiplicity p : ENNReal)
  have h_union_meas : MeasurableSet Y.union :=
    measurableSet_shading_union Y
  have h_m_zero : ∀ p, p ∉ Y.union → m p = 0 := by
    intro p hp
    classical
    have h1 : Y.pointMultiplicity p = 0 := by
      simp only [Kakeya.Streamlined.Shading.pointMultiplicity]
      have h_forall : ∀ (i : Fin F.toBodyFamily.card), p ∉ Y.carrier i := by
        intro i hi
        exact hp ⟨i, hi⟩
      have h_filter_empty : (Finset.univ.filter fun i : Fin F.toBodyFamily.card => p ∈ Y.carrier i) = ∅ := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        <;> simp_all
      rw [h_filter_empty]
      <;> simp
    simpa [m] using congr_arg (fun x : ℕ => (x : ENNReal)) h1
  have hZ_mass : Z.mass = ∫⁻ p in S, m p := by
    have h_sum : Z.mass = ∑ i : Fin F.toBodyFamily.card,
        MeasureTheory.volume (Z.carrier i) := rfl
    rw [h_sum]
    have h_eq : ∑ i : Fin F.toBodyFamily.card, MeasureTheory.volume (Z.carrier i) =
        ∑ i : Fin F.toBodyFamily.card, MeasureTheory.volume (Y.carrier i ∩ S) := by
      apply Finset.sum_congr rfl
      intro i _
      have hzi : Z.carrier i = Y.carrier i ∩ S := hZ i
      rw [hzi]
    rw [h_eq]
    exact sum_volume_inter_eq_setLIntegral_pointMultiplicity Y hS
  have h1 : Z.mass ≥ lambda * MeasureTheory.volume (Y.union ∩ S) := by
    rw [hZ_mass]
    have h_disj : Disjoint (Y.union ∩ S) (S \ Y.union) := by
      rw [Set.disjoint_left]
      intro p h1 h2
      exact h2.2 h1.1
    have h_union2 : (Y.union ∩ S) ∪ (S \ Y.union) = S := by
      ext x; simp [Set.mem_diff] <;> tauto
    have h_meas1 : MeasurableSet (Y.union ∩ S) := h_union_meas.inter hS
    have h_meas2 : MeasurableSet (S \ Y.union) := hS.diff h_union_meas
    have h_zero : ∫⁻ p in (S \ Y.union), m p = 0 := by
      apply MeasureTheory.setLIntegral_eq_zero h_meas2
      intro p hp
      exact h_m_zero p hp.2
    have h_ind_eq : ∀ p ∈ S, m p = Set.indicator (Y.union ∩ S) m p := by
      intro p hp
      by_cases h2 : p ∈ Y.union
      · have h3 : p ∈ Y.union ∩ S := ⟨h2, hp⟩
        simp [Set.indicator, h3]
      · have h4 : m p = 0 := h_m_zero p h2
        simp [Set.indicator, h2, h4]
    have h_main1 : ∫⁻ p in S, m p = ∫⁻ p in S, Set.indicator (Y.union ∩ S) m p := by
      apply le_antisymm
      · apply MeasureTheory.setLIntegral_mono' hS
        intro p hp
        exact (h_ind_eq p hp).le
      · apply MeasureTheory.setLIntegral_mono' hS
        intro p hp
        exact (h_ind_eq p hp).symm.le
    have h_ind_supp : Set.indicator (Y.union ∩ S) m = Set.indicator S (Set.indicator (Y.union ∩ S) m) := by
      funext p
      by_cases h : p ∈ S <;> simp [Set.indicator, h] <;> tauto
    have h_main2 : ∫⁻ p in S, Set.indicator (Y.union ∩ S) m p = ∫⁻ p in (Y.union ∩ S), m p := by
      have h1 : ∫⁻ p in S, Set.indicator (Y.union ∩ S) m p =
          ∫⁻ p, Set.indicator S (Set.indicator (Y.union ∩ S) m) p :=
        (MeasureTheory.lintegral_indicator hS _).symm
      rw [h1]
      have h2 : Set.indicator S (Set.indicator (Y.union ∩ S) m) = Set.indicator (Y.union ∩ S) m := h_ind_supp.symm
      rw [h2]
      exact MeasureTheory.lintegral_indicator (h_union_meas.inter hS) m
    have h_main : ∫⁻ p in S, m p = ∫⁻ p in (Y.union ∩ S), m p := by
      rw [h_main1, h_main2]
    rw [h_main]
    have h_above : ∫⁻ p in (Y.union ∩ S), m p ≥
        ∫⁻ _p in (Y.union ∩ S), lambda := by
      apply MeasureTheory.setLIntegral_mono' (h_union_meas.inter hS)
      intro p hp
      exact hlower p hp.1
    rw [MeasureTheory.setLIntegral_const] at h_above
    exact h_above
  have h2 : Y.mass ≤ 2 * lambda * MeasureTheory.volume Y.union := by
    have hY_mass : Y.mass = ∫⁻ p, m p :=
      (lintegral_pointMultiplicity Y).symm
    rw [hY_mass]
    have h_eq2 : m = Set.indicator Y.union m := by
      funext p
      by_cases h : p ∈ Y.union
      · simp [Set.indicator, h]
      · have hz : m p = 0 := h_m_zero p h
        simp [Set.indicator, h, hz]
    rw [h_eq2]
    rw [MeasureTheory.lintegral_indicator h_union_meas]
    have h_above : ∫⁻ p in Y.union, m p ≤ ∫⁻ _p in Y.union, (2 * lambda) := by
      apply MeasureTheory.setLIntegral_mono' h_union_meas
      intro p hp
      exact hupper p hp
    rw [MeasureTheory.setLIntegral_const] at h_above
    exact h_above
  calc
    2 * Z.mass
      ≥ 2 * (lambda * MeasureTheory.volume (Y.union ∩ S)) := by gcongr
    _ = 2 * lambda * MeasureTheory.volume (Y.union ∩ S) := by ring
    _ ≥ 2 * lambda * (c * MeasureTheory.volume Y.union) := by gcongr
    _ = c * (2 * lambda * MeasureTheory.volume Y.union) := by ring
    _ ≥ c * Y.mass := by gcongr

end Kakeya.Assouad
