import MyLeanRepo.Kakeya.Hairbrush.Basic
import Mathlib.Data.Finset.Card
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Wolff Hairbrush: Pigeonhole Lemma (Lemma 3.2)

Structure: find smallest N with Case I. If N ≤ L, done. Otherwise,
Case I(N-1) fails, and the hard angle-band pigeonhole gives Case II.

## Remaining sorrys

1. `caseIIFromFailure` — core combinatorial lemma:
   From >M/2 tubes with highMass(N) ≥ λ/2·V, derive Case II at some dyadic σ.
   Proof sketch: pointwise angle-band covering → measure subadditivity →
   per-tube pigeonhole → tube pigeonhole. See orchestrator notes for details.

2. `numBands_bound` — real inequality: 2·numBands(δ) ≤ 6·log(π/δ)+6.

3. Minor ENNReal facts in main theorem.
-/

noncomputable section

namespace Kakeya.Hairbrush

open MeasureTheory Set Finset

attribute [local instance] Classical.propDecidable

def tubeMultiplicity {δ : ℝ} (F : Kakeya.TubeFamily δ) (x : Point3) : ℕ :=
  (F.filter fun T => x ∈ T.carrier).card

def lowMass {δ : ℝ} (F : Kakeya.TubeFamily δ) (Y : Kakeya.Shading F)
    (N : ℕ) (T : Kakeya.DeltaTube δ) : ENNReal :=
  MeasureTheory.volume (Y.carrier T ∩ {x | tubeMultiplicity F x ≤ N})

def angleBandMass {δ : ℝ} (F : Kakeya.TubeFamily δ) (Y : Kakeya.Shading F)
    (T : Kakeya.DeltaTube δ) (N : ℕ) (σ : ℝ) : ENNReal :=
  MeasureTheory.volume <|
    Y.carrier T ∩ {x |
      ((F.filter fun U =>
        U ≠ T ∧ x ∈ U.carrier ∧ σ ≤ angleBetween T U ∧ angleBetween T U ≤ 2 * σ)).card ≥ N}

def CaseI {δ : ℝ} (F : Kakeya.TubeFamily δ) (Y : Kakeya.Shading F)
    (lambda : ENNReal) (N : ℕ) : Prop :=
  2 * (F.filter fun T =>
    (lambda / 2) * T.volume ≤ lowMass F Y N T).card ≥ F.card

/-- The filtered family of tubes satisfying the Case II mass condition. -/
def caseIIFilter {δ : ℝ} (F : Kakeya.TubeFamily δ) (Y : Kakeya.Shading F)
    (lambda : ENNReal) (N : ℕ) (σ L : ℝ) : Finset (Kakeya.DeltaTube δ) :=
  F.filter fun T =>
    (lambda / ENNReal.ofReal L) * T.volume ≤ angleBandMass F Y T (Nat.ceil (N / L)) σ

/-- Case II: there is an angle σ such that many tubes have large angle-band mass. -/
structure CaseII {δ : ℝ} (F : Kakeya.TubeFamily δ) (Y : Kakeya.Shading F)
    (lambda : ENNReal) (N : ℕ) (σ L : ℝ) : Prop where
  hL_pos : 0 < L
  hL_one : 1 ≤ L
  h_card : Nat.ceil L * (caseIIFilter F Y lambda N σ L).card ≥ F.card

def numBands (δ : ℝ) : ℕ := Nat.ceil (Real.log (Real.pi / δ) / Real.log 2) + 1

lemma lowMass_mono {δ : ℝ} (F : Kakeya.TubeFamily δ) (Y : Kakeya.Shading F)
    (T : Kakeya.DeltaTube δ) {N M : ℕ} (h : N ≤ M) :
    lowMass F Y N T ≤ lowMass F Y M T := by
  apply MeasureTheory.measure_mono
  intro x hx
  exact ⟨hx.1, hx.2.trans h⟩

lemma lowMass_max {δ : ℝ} (F : Kakeya.TubeFamily δ) (Y : Kakeya.Shading F)
    (T : Kakeya.DeltaTube δ) (hT : T ∈ F) :
    lowMass F Y F.card T = MeasureTheory.volume (Y.carrier T) := by
  have h1 : {x : Point3 | tubeMultiplicity F x ≤ F.card} = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have h2 : tubeMultiplicity F x ≤ F.card := by
      apply Finset.card_le_card; exact Finset.filter_subset _ _
    exact h2
  rw [lowMass, h1] <;> simp

/-- ENNReal pigeonhole: if sum ≥ c, some element ≥ c / |s|. -/
lemma ennreal_sum_pigeonhole {α : Type*} [DecidableEq α] {s : Finset α}
    {f : α → ENNReal} {c : ENNReal} (hc : c ≠ ⊤)
    (h : ∑ i ∈ s, f i ≥ c) (hs : s.Nonempty) :
    ∃ i ∈ s, f i ≥ c / (s.card : ENNReal) := by
  set d : ENNReal := c / (s.card : ENNReal) with hd_def
  have hcard_pos : 0 < s.card := hs.card_pos
  have hd_top : d ≠ ⊤ := ENNReal.div_ne_top hc (by simpa using hcard_pos.ne')
  by_cases h2 : (∃ i ∈ s, f i ≥ d)
  · exact h2
  · have h3 : ∀ i ∈ s, f i < d := by
      intro i hi
      have h4 : ¬(f i ≥ d) := by intro h5; exact h2 ⟨i, hi, h5⟩
      exact lt_of_not_ge h4
    have h4 : ∀ i ∈ s, f i ≠ ⊤ := by
      intro i hi; exact ne_top_of_lt (h3 i hi)
    have hsum_top : (∑ i ∈ s, f i) ≠ ⊤ := by
      intro htop
      have h5 : ∃ i ∈ s, f i = ⊤ := by
        rw [ENNReal.sum_eq_top] at htop; exact htop
      rcases h5 with ⟨i, hi, hfi⟩
      exact h4 i hi hfi
    have h5 : ∀ i ∈ s, (f i).toReal < d.toReal := by
      intro i hi
      exact (ENNReal.toReal_lt_toReal (h4 i hi) hd_top).mpr (h3 i hi)
    have hsum_real : (∑ i ∈ s, f i).toReal = ∑ i ∈ s, (f i).toReal :=
      ENNReal.toReal_sum h4
    have h_d_real : d.toReal = c.toReal / (s.card : ℝ) := by
      simp [hd_def, ENNReal.toReal_div] <;> ring
    have h6 : (∑ i ∈ s, f i).toReal < c.toReal := by
      rw [hsum_real]
      have h7 : ∑ i ∈ s, (f i).toReal < ∑ i ∈ s, d.toReal :=
        Finset.sum_lt_sum_of_nonempty hs h5
      have h9 : ∑ i ∈ s, d.toReal = (s.card : ℝ) * d.toReal := by
        simp [Finset.sum_const] <;> ring
      have h10 : (s.card : ℝ) * d.toReal = c.toReal := by
        rw [h_d_real] <;> field_simp <;> ring
      rw [h9, h10] at h7
      exact h7
    have h11 : (∑ i ∈ s, f i) < c :=
      (ENNReal.toReal_lt_toReal hsum_top hc).mp h6
    exact False.elim (not_le.mpr h11 h)

/-- If a + b ≥ c and b < c/2 (all finite), then a ≥ c/2. -/
lemma ennreal_half_lower {a b c : ENNReal} (hc : c ≠ ⊤)
    (ha : a ≠ ⊤) (hb : b ≠ ⊤)
    (h_sum : a + b ≥ c) (h_b_lt : b < c / 2) : a ≥ c / 2 := by
  by_contra h
  have h' : a < c / 2 := lt_of_not_ge h
  have h4 : c / 2 ≠ ⊤ := ENNReal.div_ne_top hc (by norm_num)
  have h5 : a.toReal < (c / 2).toReal :=
    (ENNReal.toReal_lt_toReal ha h4).mpr h'
  have h6 : b.toReal < (c / 2).toReal :=
    (ENNReal.toReal_lt_toReal hb h4).mpr h_b_lt
  have h7 : (a + b).toReal = a.toReal + b.toReal := ENNReal.toReal_add ha hb
  have h9 : (c / 2).toReal = c.toReal / 2 := by
    simp [ENNReal.toReal_div] <;> ring
  have h8 : (a + b).toReal < c.toReal := by
    rw [h7]
    rw [h9] at h5 h6
    linarith
  have h10 : a + b < c :=
    (ENNReal.toReal_lt_toReal (ENNReal.add_ne_top.mpr ⟨ha, hb⟩) hc).mp h8
  exact False.elim (not_le.mpr h10 h_sum)

/-- Natural number pigeonhole: if sum ≥ n, some f i satisfies s.card * f i ≥ n. -/
lemma nat_sum_pigeonhole {α : Type*} [DecidableEq α] {s : Finset α}
    {f : α → ℕ} {n : ℕ} (hn_pos : 0 < n)
    (h : ∑ i ∈ s, f i ≥ n) (hs : s.Nonempty) :
    ∃ i ∈ s, s.card * f i ≥ n := by
  have hpos : 0 < s.card := hs.card_pos
  by_contra h2
  have h3 : ∀ i ∈ s, s.card * f i < n := by
    intro i hi
    have h4 : ¬(s.card * f i ≥ n) := by intro h5; exact h2 ⟨i, hi, h5⟩
    exact lt_of_not_ge h4
  have h4 : ∀ i ∈ s, (f i : ℝ) < (n : ℝ) / (s.card : ℝ) := by
    intro i hi
    have h5 : (s.card : ℝ) * (f i : ℝ) < (n : ℝ) := by exact_mod_cast h3 i hi
    have hne : (s.card : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
    have h6 : (f i : ℝ) < (n : ℝ) / (s.card : ℝ) := by
      calc (f i : ℝ)
        = ((s.card : ℝ) * (f i : ℝ)) / (s.card : ℝ) := by field_simp [hne] <;> ring
      _ < (n : ℝ) / (s.card : ℝ) := by gcongr
    exact h6
  have h7 : ∑ i ∈ s, (f i : ℝ) < (n : ℝ) := by
    have h8 : ∑ i ∈ s, (f i : ℝ) < ∑ i ∈ s, ((n : ℝ) / (s.card : ℝ)) :=
      Finset.sum_lt_sum_of_nonempty hs h4
    have h9 : ∑ i ∈ s, ((n : ℝ) / (s.card : ℝ)) = (n : ℝ) := by
      simp [Finset.sum_const, hpos.ne'] <;> field_simp <;> ring
    rw [h9] at h8
    exact h8
  have h10 : (n : ℝ) ≤ ∑ i ∈ s, (f i : ℝ) := by exact_mod_cast h
  linarith

/-- Angle band covering: any θ ∈ [δ, π] lies in some dyadic band [2^k*δ, 2^(k+1)*δ]. -/
lemma angle_band_cover (δ : ℝ) (hδ : 0 < δ) (K : ℕ)
    (hK : Real.pi / δ ≤ (2 : ℝ)^K) {θ : ℝ} (hθ1 : δ ≤ θ) (hθ2 : θ ≤ Real.pi) :
    ∃ k : ℕ, k < K + 1 ∧ (2 : ℝ)^k * δ ≤ θ ∧ θ ≤ 2 * ((2 : ℝ)^k * δ) := by
  let x : ℝ := θ / δ
  have hx1 : 1 ≤ x := by
    dsimp only [x]
    rw [one_le_div hδ] <;> linarith
  have hx2 : x ≤ (2 : ℝ)^K := by
    dsimp only [x]
    have h : θ / δ ≤ Real.pi / δ := by gcongr
    exact h.trans hK
  let S : Finset ℕ := Finset.filter (fun k : ℕ => (2 : ℝ)^k ≤ x) (Finset.range (K + 1))
  have h0_in_S : 0 ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_range] <;> norm_num <;> linarith
  have hS_nonempty : S.Nonempty := ⟨0, h0_in_S⟩
  let k := S.max' hS_nonempty
  have hk_in_S : k ∈ S := Finset.max'_mem S hS_nonempty
  have hk_lt : k < K + 1 := Finset.mem_range.mp (Finset.mem_filter.mp hk_in_S).1
  have h_pow1 : (2 : ℝ)^k ≤ x := (Finset.mem_filter.mp hk_in_S).2
  have h_pow2 : x < (2 : ℝ)^(k + 1) := by
    by_cases h_kK : k = K
    · rw [h_kK]
      have h2 : (2 : ℝ)^K < (2 : ℝ)^(K + 1) := by
        gcongr <;> norm_num
      linarith [hx2]
    · have h_k_lt_K : k < K := by omega
      by_contra h
      have h' : (2 : ℝ)^(k + 1) ≤ x := by linarith
      have h_k1_in_range : k + 1 ∈ Finset.range (K + 1) := by
        simp only [Finset.mem_range] <;> omega
      have h_k1_in_S : k + 1 ∈ S := by
        simp only [S, Finset.mem_filter] <;> exact ⟨h_k1_in_range, h'⟩
      have h_le : k + 1 ≤ k := Finset.le_max' S (k + 1) h_k1_in_S
      omega
  refine ⟨k, hk_lt, ?_⟩
  have h9 : (2 : ℝ)^k * δ ≤ θ := by
    have h10 : (2 : ℝ)^k * δ ≤ x * δ := by gcongr
    have h11 : x * δ = θ := by
      dsimp only [x]
      field_simp [hδ.ne'] <;> ring
    rw [h11] at h10
    exact h10
  have h10 : θ ≤ 2 * ((2 : ℝ)^k * δ) := by
    have h11 : θ = x * δ := by
      dsimp only [x]
      field_simp [hδ.ne'] <;> ring
    rw [h11]
    have h12 : x * δ < (2 : ℝ)^(k + 1) * δ := by gcongr
    have h13 : (2 : ℝ)^(k + 1) * δ = 2 * ((2 : ℝ)^k * δ) := by ring
    rw [h13] at h12
    exact le_of_lt h12
  exact ⟨h9, h10⟩

/-- angleBandMass is antitone in the multiplicity threshold. -/
lemma angleBandMass_mono {δ : ℝ} (F : Kakeya.TubeFamily δ) (Y : Kakeya.Shading F)
    (T : Kakeya.DeltaTube δ) {N M : ℕ} (h : N ≤ M) (σ : ℝ) :
    angleBandMass F Y T M σ ≤ angleBandMass F Y T N σ := by
  apply MeasureTheory.measure_mono
  intro x hx
  exact ⟨hx.1, h.trans hx.2⟩

/-- tubeMultiplicity is a measurable function (finite sum of indicators). -/
lemma measurable_tubeMultiplicity {δ : ℝ} (F : Kakeya.TubeFamily δ) :
    Measurable (tubeMultiplicity F) := by
  have h1 : tubeMultiplicity F = fun x =>
      ∑ T ∈ F, if x ∈ T.carrier then (1 : ℕ) else 0 := by
    funext x
    have h2 : ∑ T ∈ F, (if x ∈ T.carrier then (1 : ℕ) else 0) =
        (F.filter (fun T => x ∈ T.carrier)).card := by
      rw [Finset.sum_ite]
      <;> simp
    simpa [tubeMultiplicity] using h2.symm
  rw [h1]
  apply Finset.measurable_sum
  intro T _
  have hms : MeasurableSet T.carrier := by
    unfold DeltaTube.carrier
    exact Metric.isClosed_cthickening.measurableSet
  exact Measurable.ite hms measurable_const measurable_const

/-- Threshold inequality: ⌈(N-1)/B⌉ ≥ ⌈N/(2B)⌉ for N ≥ 2, B ≥ 1. -/
lemma threshold_ineq (N B : ℕ) (hN : N ≥ 2) (hB : 0 < B) :
    Nat.ceil ((N - 1 : ℝ) / (B : ℝ)) ≥ Nat.ceil ((N : ℝ) / (2 * (B : ℝ))) := by
  have h1 : (N - 1 : ℝ) / (B : ℝ) ≥ (N : ℝ) / (2 * (B : ℝ)) := by
    have h2 : (N - 1 : ℝ) ≥ (N : ℝ) / 2 := by
      have h3 : (N : ℝ) ≥ 2 := by exact_mod_cast hN
      linarith
    have h4 : (N - 1 : ℝ) / (B : ℝ) ≥ ((N : ℝ) / 2) / (B : ℝ) := by gcongr
    have h5 : ((N : ℝ) / 2) / (B : ℝ) = (N : ℝ) / (2 * (B : ℝ)) := by ring
    linarith
  exact Nat.ceil_mono h1

/-- Assemble CaseII from the fact that all tubes satisfy the mass condition. -/
lemma assembleCaseII {δ : ℝ} {F : TubeFamily δ} {Y : Shading F} {lambda : ENNReal} {N : ℕ} {σ L : ℝ}
    (hL_pos : 0 < L) (hL_one : 1 ≤ L)
    (h_filter : caseIIFilter F Y lambda N σ L = F) :
    CaseII F Y lambda N σ L := by
  have h_ceil_pos : 1 ≤ Nat.ceil L := Nat.ceil_pos.mpr hL_pos
  have h : Nat.ceil L * F.card ≥ F.card := by
    have h2 : 1 ≤ Nat.ceil L := h_ceil_pos
    have h3 : Nat.ceil L * F.card ≥ 1 * F.card := by gcongr
    simpa using h3
  have h4 : Nat.ceil L * (caseIIFilter F Y lambda N σ L).card ≥ F.card := by
    rw [h_filter]
    exact h
  exact ⟨hL_pos, hL_one, h4⟩

/-- Assemble CaseII from a cardinality inequality on the filtered family. -/
lemma assembleCaseIIOfCard {δ : ℝ} {F : TubeFamily δ} {Y : Shading F} {lambda : ENNReal} {N : ℕ} {σ L : ℝ}
    (hL_pos : 0 < L) (hL_one : 1 ≤ L)
    (h_card : Nat.ceil L * (caseIIFilter F Y lambda N σ L).card ≥ F.card) :
    CaseII F Y lambda N σ L := by
  exact ⟨hL_pos, hL_one, h_card⟩

/-- In the trivial case (threshold=0 or massThreshold*V=0), CaseII holds for any σ. -/
lemma trivialCaseII {δ : ℝ} {F : TubeFamily δ} {Y : Shading F} {lambda : ENNReal} {N : ℕ} {σ L : ℝ}
    (hL_pos : 0 < L) (hL_one : 1 ≤ L)
    (V : ENNReal) (hUniformVolume : ∀ T ∈ F, T.volume = V)
    (hPerTube : ∀ T ∈ F, lambda * V ≤ MeasureTheory.volume (Y.carrier T))
    (h_mass_le_lambda : (lambda / ENNReal.ofReal L) ≤ lambda)
    (h_triv : Nat.ceil (N / L) = 0 ∨ (lambda / ENNReal.ofReal L) * V = 0) :
    CaseII F Y lambda N σ L := by
  have h_filter : caseIIFilter F Y lambda N σ L = F := by
    dsimp only [caseIIFilter]
    apply Finset.filter_true_of_mem
    intro T hTinF
    have h_vol : T.volume = V := hUniformVolume T hTinF
    cases h_triv with
    | inl h_thresh0 =>
      have h_set : {x : Point3 | ((F.filter fun U => U ≠ T ∧ x ∈ U.carrier ∧ σ ≤ angleBetween T U ∧ angleBetween T U ≤ 2 * σ)).card ≥ 0} = Set.univ := by
        apply Set.eq_univ_of_forall
        intro x
        exact Nat.zero_le _
      have h_vol2 : angleBandMass F Y T 0 σ = MeasureTheory.volume (Y.carrier T) := by
        rw [angleBandMass, h_set] <;> simp
      have h_goal : (lambda / ENNReal.ofReal L) * T.volume ≤ angleBandMass F Y T (Nat.ceil (N / L)) σ := by
        rw [h_vol, h_thresh0, h_vol2]
        have h6 : (lambda / ENNReal.ofReal L) * V ≤ lambda * V := by
          exact mul_le_mul_right' h_mass_le_lambda V
        exact h6.trans (hPerTube T hTinF)
      exact h_goal
    | inr h_mass0 =>
      have h7 : (lambda / ENNReal.ofReal L) * T.volume = 0 := by
        rw [h_vol, h_mass0]
      rw [h7] <;> simp
  exact assembleCaseII hL_pos hL_one h_filter

/-- If K = ceil(x), K > 0, and x ≥ 0, then K-1 < x. -/
lemma ceil_sub_one_lt (x : ℝ) (K : ℕ) (hK : K = Nat.ceil x) (hK_pos : 0 < K) (hx_nonneg : 0 ≤ x) :
    ((K - 1 : ℕ) : ℝ) < x := by
  have h1 : (Nat.ceil x : ℝ) < x + 1 := Nat.ceil_lt_add_one hx_nonneg
  have h2 : ((K - 1 : ℕ) : ℝ) = (K : ℝ) - 1 := by
    simp [Nat.cast_sub hK_pos] <;> norm_num
  have h3 : (K : ℝ) = (Nat.ceil x : ℝ) := by exact_mod_cast hK
  rw [h2, h3]
  linarith

/-- Prove σ b ≤ π from the angle band structure and non-trivial mass condition. -/
lemma sigmaBound {δ : ℝ} {F : TubeFamily δ} {Y : Shading F} {V : ENNReal}
    (hδ : 0 < δ) (hδ_le_pi : δ ≤ Real.pi)
    (B K : ℕ) (hK_eq : K = B - 1)
    (hK_ceil : K = Nat.ceil (Real.log (Real.pi / δ) / Real.log 2))
    (b : ℕ) (hb_in : b ∈ Finset.range B)
    (σ : ℕ → ℝ) (hσ_def : ∀ k, σ k = (2 : ℝ)^k * δ)
    (threshold : ℕ) (massThreshold : ENNReal)
    (hsome : ∃ (T : DeltaTube δ), T ∈ F ∧ massThreshold * V ≤ angleBandMass F Y T threshold (σ b))
    (h_not_mass : massThreshold * V ≠ 0)
    (h_thresh_pos : 0 < threshold) :
    σ b ≤ Real.pi := by
  by_cases h_b_lt_K : b < K
  · -- b < K implies σ b < π
    have hK_pos : 0 < K := by omega
    set x : ℝ := Real.log (Real.pi / δ) / Real.log 2 with hx_def
    have hx_nonneg : 0 ≤ x := by
      have h1 : 0 ≤ Real.log (Real.pi / δ) := by
        apply Real.log_nonneg
        have h2 : 1 ≤ Real.pi / δ := by
          exact (one_le_div hδ).mpr hδ_le_pi
        exact h2
      have h3 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      exact div_nonneg h1 (by linarith)
    have h_K1_lt_x : ((K - 1 : ℕ) : ℝ) < x :=
      ceil_sub_one_lt x K hK_ceil hK_pos hx_nonneg
    have h_b_le_K1 : b ≤ K - 1 := by omega
    have h_pow_b_le : (2 : ℝ)^b ≤ (2 : ℝ)^(K - 1) := by gcongr <;> norm_num
    have h_pow_K1_lt : (2 : ℝ)^(K - 1) < (2 : ℝ)^x := by
      have h_cast : (2 : ℝ)^((K - 1 : ℕ) : ℝ) = (2 : ℝ)^(K - 1) := by
        rw [Real.rpow_natCast]
      have h_goal : (2 : ℝ)^((K - 1 : ℕ) : ℝ) < (2 : ℝ)^x :=
        Real.rpow_lt_rpow_of_exponent_lt (show (1 : ℝ) < (2 : ℝ) from by norm_num) h_K1_lt_x
      rw [h_cast] at h_goal
      exact h_goal
    have h_eq2 : (2 : ℝ)^x = Real.pi / δ := by
      have h_pos : 0 < Real.pi / δ := by positivity
      have h : (2 : ℝ)^x = Real.exp (x * Real.log 2) := by
        rw [Real.rpow_def_of_pos (by norm_num)] <;> ring
      rw [h]
      have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have h2 : x * Real.log 2 = Real.log (Real.pi / δ) := by
        simp only [hx_def]
        <;> field_simp [hlog2_pos.ne'] <;> ring
      rw [h2, Real.exp_log h_pos]
    have hσb_lt_pi : σ b < Real.pi := by
      rw [hσ_def b]
      calc (2 : ℝ)^b * δ
        ≤ (2 : ℝ)^(K - 1) * δ := by gcongr
      _ < (2 : ℝ)^x * δ := by gcongr
      _ = (Real.pi / δ) * δ := by rw [h_eq2]
      _ = Real.pi := by field_simp [hδ.ne'] <;> ring
    exact hσb_lt_pi.le
  · -- b = K
    have h_b_eq_K : b = K := by
      have h_b_lt_B : b < B := Finset.mem_range.mp hb_in
      omega
    by_cases hσK_le : σ K ≤ Real.pi
    · rw [h_b_eq_K]; exact hσK_le
    · -- σ K > π leads to contradiction with positive mass
      have hσK_gt : σ K > Real.pi := by linarith
      rcases hsome with ⟨T, hTinF, h_cond⟩
      let F_K := F.filter (fun U => U ≠ T ∧ σ K ≤ angleBetween T U ∧ angleBetween T U ≤ 2 * σ K)
      have h_FK_empty : F_K = ∅ := by
        have h : F_K.Nonempty → False := by
          intro hne
          rcases hne with ⟨U, hU⟩
          have h_angle : σ K ≤ angleBetween T U := (Finset.mem_filter.mp hU).2.2.1
          have h_angle_le : angleBetween T U ≤ Real.pi := Real.arccos_le_pi _
          linarith
        by_contra hne
        exact h (Finset.nonempty_iff_ne_empty.mpr hne)
      have h_mult_zero : ∀ x, tubeMultiplicity F_K x = 0 := by
        intro x
        rw [h_FK_empty] <;> simp [tubeMultiplicity]
      have h_set_empty : {x : Point3 | tubeMultiplicity F_K x ≥ threshold} = ∅ := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        have h5 : tubeMultiplicity F_K x = 0 := h_mult_zero x
        rw [h5] <;> omega
      have h_mass_zero : angleBandMass F Y T threshold (σ K) = 0 := by
        have h_set2 : {x : Point3 | ((F.filter fun U => U ≠ T ∧ x ∈ U.carrier ∧ σ K ≤ angleBetween T U ∧ angleBetween T U ≤ 2 * σ K)).card ≥ threshold} = ∅ := by
          ext x
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          have h_eq : ((F.filter fun U => U ≠ T ∧ x ∈ U.carrier ∧ σ K ≤ angleBetween T U ∧ angleBetween T U ≤ 2 * σ K)).card = tubeMultiplicity F_K x := by
            have h_filter_eq : (F.filter fun U => U ≠ T ∧ x ∈ U.carrier ∧ σ K ≤ angleBetween T U ∧ angleBetween T U ≤ 2 * σ K) = F_K.filter (fun U => x ∈ U.carrier) := by
              ext U
              simp [F_K] <;> tauto
            rw [h_filter_eq] <;> rfl
          rw [h_eq]
          have h5 : tubeMultiplicity F_K x = 0 := h_mult_zero x
          rw [h5] <;> omega
        have h_unfold : angleBandMass F Y T threshold (σ K) = MeasureTheory.volume (Y.carrier T ∩ {x : Point3 | ((F.filter fun U => U ≠ T ∧ x ∈ U.carrier ∧ σ K ≤ angleBetween T U ∧ angleBetween T U ≤ 2 * σ K)).card ≥ threshold}) := by
          simp [angleBandMass] <;> rfl
        rw [h_unfold, h_set2] <;> simp
      have h_cond2 : massThreshold * V ≤ angleBandMass F Y T threshold (σ b) := h_cond
      rw [h_b_eq_K] at h_cond2
      rw [h_mass_zero] at h_cond2
      have h_cont : massThreshold * V ≤ 0 := h_cond2
      have h_eq : massThreshold * V = 0 := by simpa using h_cont
      exact False.elim (h_not_mass h_eq)

/-- Finish the non-trivial case: construct hsome, prove σ bound, and assemble CaseII. -/
lemma finishNonTrivialCase {δ : ℝ} {F : TubeFamily δ} {Y : Shading F} {lambda : ENNReal} {N : ℕ} {V : ENNReal}
    (hδ : 0 < δ) (hδ_le_pi : δ ≤ Real.pi)
    (hUniformVolume : ∀ T ∈ F, T.volume = V)
    (B K : ℕ) (hK_eq : K = B - 1)
    (hK_ceil : K = Nat.ceil (Real.log (Real.pi / δ) / Real.log 2))
    (L : ℝ) (hL_pos : 0 < L) (hL_one : 1 ≤ L)
    (b : ℕ) (hb_in : b ∈ Finset.range B)
    (σ : ℕ → ℝ) (hσ_def : ∀ k, σ k = (2 : ℝ)^k * δ)
    (threshold : ℕ) (hthreshold_def : threshold = Nat.ceil (N / L))
    (massThreshold : ENNReal) (hmass_def : massThreshold = lambda / ENNReal.ofReal L)
    (G : Finset (DeltaTube δ)) (hG_sub_F : G ⊆ F)
    (k' : DeltaTube δ → ℕ)
    (hk_cond : ∀ T ∈ G, massThreshold * V ≤ angleBandMass F Y T threshold (σ (k' T)))
    (counts : ℕ → ℕ) (hcounts_eq : ∀ c, counts c = (G.filter (fun T => k' T = c)).card)
    (h_final : Nat.ceil L * counts b ≥ F.card)
    (hF_pos : 0 < F.card)
    (h8 : Nat.ceil L * (F.filter fun T => massThreshold * V ≤ angleBandMass F Y T threshold (σ b)).card ≥ F.card)
    (h_not_mass : massThreshold * V ≠ 0)
    (h_thresh_pos : 0 < threshold)
    : ∃ (σ' : ℝ), δ ≤ σ' ∧ σ' ≤ Real.pi ∧ CaseII F Y lambda N σ' L := by
  have h_ceil_pos : 0 < Nat.ceil L := Nat.ceil_pos.mpr hL_pos
  have h_pos : Nat.ceil L * counts b ≥ F.card := h_final
  have h_mul_pos : 0 < Nat.ceil L * counts b := Nat.lt_of_lt_of_le hF_pos h_pos
  have hcount_pos : 0 < counts b := by
    by_cases h : counts b = 0
    · rw [h] at h_mul_pos
      simp at h_mul_pos <;> omega
    · exact Nat.pos_of_ne_zero h
  have hfiber_card : 0 < (G.filter (fun T => k' T = b)).card := by
    rw [←hcounts_eq b]
    exact hcount_pos
  have hfiber_nonempty : (G.filter (fun T => k' T = b)).Nonempty := by
    exact Finset.card_pos.mp hfiber_card
  rcases hfiber_nonempty with ⟨T, hTinFiber⟩
  have hTinG : T ∈ G := (Finset.mem_filter.mp hTinFiber).1
  have hTinF : T ∈ F := hG_sub_F hTinG
  have h_k'_eq_b : k' T = b := (Finset.mem_filter.mp hTinFiber).2
  have hsome : ∃ (T : DeltaTube δ), T ∈ F ∧ massThreshold * V ≤ angleBandMass F Y T threshold (σ b) := by
    refine ⟨T, hTinF, ?_⟩
    have h_cond := hk_cond T hTinG
    rw [h_k'_eq_b] at h_cond
    exact h_cond
  have hσ2 : σ b ≤ Real.pi :=
    sigmaBound hδ hδ_le_pi B K hK_eq hK_ceil b hb_in σ hσ_def threshold massThreshold hsome h_not_mass h_thresh_pos
  have h_filter_eq : (F.filter fun T => massThreshold * V ≤ angleBandMass F Y T threshold (σ b)) =
      caseIIFilter F Y lambda N (σ b) L := by
    dsimp only [caseIIFilter]
    apply Finset.filter_congr
    intro T hTinF
    have h_vol : T.volume = V := hUniformVolume T hTinF
    have h1 : massThreshold * V = (lambda / ENNReal.ofReal L) * T.volume := by
      rw [hmass_def, h_vol] <;> rfl
    have h2 : threshold = Nat.ceil (N / L) := hthreshold_def
    rw [h1, h2]
  have h8' : Nat.ceil L * (caseIIFilter F Y lambda N (σ b) L).card ≥ F.card := by
    rw [←h_filter_eq]
    exact h8
  have hσ1 : δ ≤ σ b := by
    rw [hσ_def b]
    have h1 : (1 : ℝ) ≤ (2 : ℝ)^b := by
      have h2 : (1 : ℝ) ≤ (2 : ℝ) := by norm_num
      have h3 : (1 : ℝ)^b ≤ (2 : ℝ)^b := by gcongr
      simpa using h3
    have h2 : 0 ≤ δ := by linarith
    have h3 : δ ≤ (2 : ℝ)^b * δ := by
      calc δ = 1 * δ := by ring
        _ ≤ (2 : ℝ)^b * δ := by gcongr
    exact h3
  exact ⟨σ b, hσ1, hσ2, assembleCaseIIOfCard hL_pos hL_one h8'⟩

/-- Core implementation of caseIIFromFailure with L as an opaque parameter. -/
lemma caseIIFromFailureCore {δ : ℝ} (hδ : 0 < δ)
    (F : Kakeya.TubeFamily δ) (Y : Kakeya.Shading F)
    (lambda : ENNReal) (hlam_top : lambda ≠ ⊤)
    (N : ℕ) (hNge2 : N ≥ 2)
    (V : ENNReal) (hV_top : V ≠ ⊤)
    (hUniformVolume : ∀ T ∈ F, T.volume = V)
    (hPerTube : ∀ T ∈ F, lambda * V ≤ MeasureTheory.volume (Y.carrier T))
    (hAngleSep : ∀ T ∈ F, ∀ U ∈ F, T ≠ U → T.carrier ∩ U.carrier ≠ ∅ →
      δ ≤ angleBetween T U)
    (hCaseIFails : ¬CaseI F Y lambda (N - 1))
    (B : ℕ) (hB_pos : 0 < B)
    (K : ℕ) (hK_eq : K = B - 1)
    (hK_ceil : K = Nat.ceil (Real.log (Real.pi / δ) / Real.log 2))
    (hK_pow : Real.pi / δ ≤ (2 : ℝ)^K)
    (L : ℝ) (hL_pos : 0 < L) (hL_one : 1 ≤ L) (hL_def : L = 2 * (B : ℝ))
    (hthresh_le : Nat.ceil (N / L) ≤ Nat.ceil ((N - 1 : ℝ) / (B : ℝ))) :
    ∃ (σ : ℝ), δ ≤ σ ∧ σ ≤ Real.pi ∧ CaseII F Y lambda N σ L := by
  set σ : ℕ → ℝ := fun k => (2 : ℝ)^k * δ with hσ_def
  set threshold : ℕ := Nat.ceil (N / L) with hthreshold_def
  set massThreshold : ENNReal := lambda / ENNReal.ofReal L with hmass_def
  have hL_pos : 0 < L := by positivity
  have hL_one : 1 ≤ L := by
    have h : (B : ℝ) ≥ 1 := by exact_mod_cast hB_pos
    linarith
  have hthresh_le : threshold ≤ Nat.ceil ((N - 1 : ℝ) / (B : ℝ)) := by
    have h_threshold_eq : threshold = Nat.ceil ((N : ℝ) / (2 * (B : ℝ))) := by
      rw [hthreshold_def, hL_def] <;> rfl
    rw [h_threshold_eq]
    exact threshold_ineq N B hNge2 hB_pos
  let G := F.filter (fun T => ¬((lambda / 2) * V ≤ lowMass F Y (N - 1) T))
  let H := F.filter (fun T => (lambda / 2) * V ≤ lowMass F Y (N - 1) T)
  have h_disj : Disjoint G H := by
    simp [G, H, Finset.disjoint_left] <;> tauto
  have h_union : G ∪ H = F := by
    ext T
    simp only [G, H, Finset.mem_union, Finset.mem_filter]
    <;> by_cases h : (lambda / 2) * V ≤ lowMass F Y (N - 1) T <;> simp [h] <;> tauto
  have hG_card : 2 * G.card > F.card := by
    have h1 : G.card + H.card = F.card := by
      rw [← Finset.card_union_of_disjoint h_disj, h_union]
    have h_filter_eq : (F.filter fun T => (lambda / 2) * T.volume ≤ lowMass F Y (N - 1) T) = H := by
      apply Finset.ext
      intro T
      by_cases hT : T ∈ F
      · have hvol : T.volume = V := hUniformVolume T hT
        simp [H, Finset.mem_filter, hT, hvol]
      · simp [H, Finset.mem_filter, hT]
    have hCaseI_iff : CaseI F Y lambda (N - 1) ↔ 2 * H.card ≥ F.card := by
      simp [CaseI, h_filter_eq] <;> rfl
    have h2 : ¬(2 * H.card ≥ F.card) := by
      exact mt hCaseI_iff.mpr hCaseIFails
    have h3 : 2 * H.card < F.card := by
      exact Nat.lt_of_not_le h2
    omega
  have hlamV_top : lambda * V ≠ ⊤ := ENNReal.mul_ne_top hlam_top hV_top
  have h_half_lamV_top : (lambda / 2) * V ≠ ⊤ := by
    have h : (lambda / 2) * V ≤ lambda * V := by
      have h5 : (lambda / 2) ≤ lambda := by
        calc lambda / 2
          ≤ lambda / 1 := by gcongr <;> norm_num
        _ = lambda := by simp
      gcongr
    exact ne_top_of_le_ne_top hlamV_top h
  have h_main1 : ∀ (T : Kakeya.DeltaTube δ), T ∈ G →
      ∃ k ∈ Finset.range B, massThreshold * V ≤ angleBandMass F Y T threshold (σ k) := by
    intro T hT
    have hTinF : T ∈ F := (Finset.mem_filter.mp hT).1
    have hT_vol : T.volume = V := hUniformVolume T hTinF
    have hY_vol : MeasureTheory.volume (Y.carrier T) ≥ lambda * V := hPerTube T hTinF
    have hY_top : MeasureTheory.volume (Y.carrier T) ≠ ⊤ := by
      have h_sub : Y.carrier T ⊆ T.carrier := Y.subset_tube hTinF
      have h : MeasureTheory.volume (Y.carrier T) ≤ T.volume := MeasureTheory.measure_mono h_sub
      have h' : T.volume = V := hT_vol
      rw [h'] at h
      exact ne_top_of_le_ne_top hV_top h
    have h_low_lt : lowMass F Y (N - 1) T < (lambda / 2) * V := by
      have h' : ¬((lambda / 2) * V ≤ lowMass F Y (N - 1) T) := (Finset.mem_filter.mp hT).2
      exact lt_of_not_ge h'
    have h_low_top : lowMass F Y (N - 1) T ≠ ⊤ := ne_top_of_lt h_low_lt
    let lowSet := Y.carrier T ∩ {x | tubeMultiplicity F x ≤ N - 1}
    let highSet := Y.carrier T ∩ {x | tubeMultiplicity F x > N - 1}
    have h_low_eq : MeasureTheory.volume lowSet = lowMass F Y (N - 1) T := by rfl
    have hmf : Measurable (tubeMultiplicity F) := measurable_tubeMultiplicity F
    have h_meas_set1 : MeasurableSet (Set.Iic (N - 1) : Set ℕ) := by simp
    have h_meas_set2 : MeasurableSet (Set.Ioi (N - 1) : Set ℕ) := by simp
    have h_imag1 : MeasurableSet (tubeMultiplicity F ⁻¹' Set.Iic (N - 1)) := by
      exact MeasurableSet.preimage h_meas_set1 hmf
    have h_imag2 : MeasurableSet (tubeMultiplicity F ⁻¹' Set.Ioi (N - 1)) := by
      exact MeasurableSet.preimage h_meas_set2 hmf
    have h_meas_low : MeasurableSet lowSet :=
      (Y.measurable_carrier hTinF).inter h_imag1
    have h_meas_high : MeasurableSet highSet :=
      (Y.measurable_carrier hTinF).inter h_imag2
    have h_disj' : Disjoint lowSet highSet := by
      rw [Set.disjoint_left]
      intro x hx1 hx2
      have h_le : tubeMultiplicity F x ≤ N - 1 := hx1.2
      have h_gt : tubeMultiplicity F x > N - 1 := hx2.2
      exact not_le.mpr h_gt h_le
    have h_union' : lowSet ∪ highSet = Y.carrier T := by
      ext x
      simp only [lowSet, highSet, Set.mem_union, Set.mem_inter_iff]
      <;> constructor
      · rintro (h | h) <;> exact h.1
      · intro hx
        by_cases h : tubeMultiplicity F x ≤ N - 1
        · exact Or.inl ⟨hx, h⟩
        · exact Or.inr ⟨hx, by simpa using h⟩
    have h_add : MeasureTheory.volume (Y.carrier T) =
        MeasureTheory.volume lowSet + MeasureTheory.volume highSet := by
      rw [← h_union']
      exact measure_union h_disj' h_meas_high
    have h_high_top : MeasureTheory.volume highSet ≠ ⊤ := by
      have h : highSet ⊆ Y.carrier T := by intro x hx; exact hx.1
      have h' : MeasureTheory.volume highSet ≤ MeasureTheory.volume (Y.carrier T) :=
        MeasureTheory.measure_mono h
      exact ne_top_of_le_ne_top hY_top h'
    have h_sum_ge : MeasureTheory.volume highSet + MeasureTheory.volume lowSet ≥ lambda * V := by
      have h_comm : MeasureTheory.volume highSet + MeasureTheory.volume lowSet =
          MeasureTheory.volume lowSet + MeasureTheory.volume highSet := by apply add_comm
      rw [h_comm, ← h_add]
      exact hY_vol
    have h_b_lt : MeasureTheory.volume lowSet < (lambda / 2) * V := by
      rw [h_low_eq]
      exact h_low_lt
    have h_b_top : MeasureTheory.volume lowSet ≠ ⊤ := by
      rw [h_low_eq] <;> exact h_low_top
    have h_c_div2 : (lambda * V) / 2 = (lambda / 2) * V := by
      simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
    have h_b_lt2 : MeasureTheory.volume lowSet < (lambda * V) / 2 := by
      rw [h_c_div2]
      exact h_b_lt
    have h_high_vol : MeasureTheory.volume highSet ≥ (lambda / 2) * V := by
      have h_goal : MeasureTheory.volume highSet ≥ (lambda * V) / 2 :=
        ennreal_half_lower hlamV_top h_high_top h_b_top h_sum_ge h_b_lt2
      have h_final : (lambda * V) / 2 = (lambda / 2) * V := h_c_div2
      rw [h_final] at h_goal
      exact h_goal
    let F_k := fun k : ℕ => F.filter (fun U => U ≠ T ∧ σ k ≤ angleBetween T U ∧ angleBetween T U ≤ 2 * σ k)
    let bandSet := fun k : ℕ => Y.carrier T ∩ {x | tubeMultiplicity (F_k k) x ≥ threshold}
    have h_bandSet_eq : ∀ k, bandSet k = Y.carrier T ∩ {x | ((F.filter fun U =>
        U ≠ T ∧ x ∈ U.carrier ∧ σ k ≤ angleBetween T U ∧ angleBetween T U ≤ 2 * σ k)).card ≥ threshold} := by
      intro k
      apply Set.ext
      intro x
      have h_eq : tubeMultiplicity (F_k k) x = ((F.filter fun U =>
          U ≠ T ∧ x ∈ U.carrier ∧ σ k ≤ angleBetween T U ∧ angleBetween T U ≤ 2 * σ k)).card := by
        have h_filter_eq : (F_k k).filter (fun U => x ∈ U.carrier) =
            F.filter (fun U => U ≠ T ∧ x ∈ U.carrier ∧ σ k ≤ angleBetween T U ∧ angleBetween T U ≤ 2 * σ k) := by
          ext U
          simp [F_k, Finset.mem_filter] <;> tauto
        exact congr_arg Finset.card h_filter_eq
      simp [bandSet, h_eq]
    have h_pointwise : highSet ⊆ ⋃ k ∈ Finset.range B, bandSet k := by
      intro x hx
      have hxY : x ∈ Y.carrier T := hx.1
      have hxT : x ∈ T.carrier := Y.subset_tube hTinF hxY
      have h_mult : tubeMultiplicity F x ≥ N := by
        have h : tubeMultiplicity F x > N - 1 := hx.2
        omega
      let S_all := F.filter (fun U => x ∈ U.carrier)
      have hS_all_card : S_all.card ≥ N := h_mult
      have hT_in_Sall : T ∈ S_all := by
        simp only [S_all, Finset.mem_filter] <;> exact ⟨hTinF, hxT⟩
      let S_other := S_all.erase T
      have hS_other_card : S_other.card ≥ N - 1 := by
        rw [Finset.card_erase_of_mem hT_in_Sall] <;> omega
      have h_cover : S_other ⊆ Finset.biUnion (Finset.range B) (fun k =>
          S_other.filter (fun U => σ k ≤ angleBetween T U ∧ angleBetween T U ≤ 2 * σ k)) := by
        intro U hU
        have h_erase : U ≠ T ∧ U ∈ S_all := Finset.mem_erase.mp hU
        have hU_ne_T : U ≠ T := h_erase.1
        have hUinSall : U ∈ S_all := h_erase.2
        have hUinF : U ∈ F := (Finset.mem_filter.mp hUinSall).1
        have hxU : x ∈ U.carrier := (Finset.mem_filter.mp hUinSall).2
        have h_inter : T.carrier ∩ U.carrier ≠ ∅ := by
          have h_nonempty : Set.Nonempty (T.carrier ∩ U.carrier) := ⟨x, hxT, hxU⟩
          exact Set.nonempty_iff_ne_empty.mp h_nonempty
        have h_angle1 : δ ≤ angleBetween T U := hAngleSep T hTinF U hUinF (Ne.symm hU_ne_T) h_inter
        have h_angle2 : angleBetween T U ≤ Real.pi := Real.arccos_le_pi _
        rcases angle_band_cover δ hδ K hK_pow h_angle1 h_angle2 with ⟨k, hk_lt, hband1, hband2⟩
        have hk_in : k ∈ Finset.range B := by
          have h_k_le_K : k ≤ K := by linarith
          have h_k_lt_B : k < B := by
            rw [hK_eq] at h_k_le_K
            omega
          simp only [Finset.mem_range] <;> exact h_k_lt_B
        have h_in_filter : U ∈ S_other.filter (fun U => σ k ≤ angleBetween T U ∧ angleBetween T U ≤ 2 * σ k) := by
          simp only [Finset.mem_filter] <;> exact ⟨hU, ⟨hband1, hband2⟩⟩
        exact Finset.mem_biUnion.mpr ⟨k, hk_in, h_in_filter⟩
      have h_sum : S_other.card ≤ ∑ k ∈ Finset.range B,
          (S_other.filter (fun U => σ k ≤ angleBetween T U ∧ angleBetween T U ≤ 2 * σ k)).card := by
        calc S_other.card
          ≤ (Finset.biUnion (Finset.range B) (fun k => S_other.filter (fun U => σ k ≤ angleBetween T U ∧ angleBetween T U ≤ 2 * σ k))).card :=
            Finset.card_le_card h_cover
        _ ≤ ∑ k ∈ Finset.range B, (S_other.filter (fun U => σ k ≤ angleBetween T U ∧ angleBetween T U ≤ 2 * σ k)).card :=
            Finset.card_biUnion_le
      have h_sum' : ∑ k ∈ Finset.range B, (S_other.filter (fun U => σ k ≤ angleBetween T U ∧ angleBetween T U ≤ 2 * σ k)).card ≥ N - 1 := by
        calc _
          ≥ S_other.card := h_sum
        _ ≥ N - 1 := hS_other_card
      rcases nat_sum_pigeonhole (show 0 < N - 1 from by omega) h_sum' (Finset.nonempty_range_iff.mpr hB_pos.ne') with ⟨k, hk_in, hk_ge⟩
      let C_k := S_other.filter (fun U => σ k ≤ angleBetween T U ∧ angleBetween T U ≤ 2 * σ k)
      have h9 : (B : ℝ) * (C_k.card : ℝ) ≥ (N - 1 : ℝ) := by
        have h_card : (Finset.range B).card = B := by simp
        have h_nat : (Finset.range B).card * C_k.card ≥ N - 1 := hk_ge
        have h_real1 : ((Finset.range B).card : ℝ) * (C_k.card : ℝ) ≥ ((N - 1 : ℕ) : ℝ) := by
          have h_le : ((N - 1 : ℕ) : ℝ) ≤ (((Finset.range B).card * C_k.card : ℕ) : ℝ) := Nat.cast_le.mpr h_nat
          have h_mul : (((Finset.range B).card * C_k.card : ℕ) : ℝ) = ((Finset.range B).card : ℝ) * (C_k.card : ℝ) := by
            exact Nat.cast_mul (Finset.range B).card C_k.card
          rw [h_mul] at h_le
          exact h_le
        have h_real2 : (B : ℝ) * (C_k.card : ℝ) ≥ ((N - 1 : ℕ) : ℝ) := by
          rw [h_card] at h_real1
          exact h_real1
        have h_final : (B : ℝ) * (C_k.card : ℝ) ≥ (N - 1 : ℝ) := by
          have h_eq : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
            rw [Nat.cast_sub (by omega)] <;> norm_num
          rw [h_eq] at h_real2
          exact h_real2
        exact h_final
      have hBreal_pos : (B : ℝ) > 0 := by exact_mod_cast hB_pos
      have h10 : (C_k.card : ℝ) ≥ (N - 1 : ℝ) / (B : ℝ) := by
        calc (C_k.card : ℝ)
          = ((B : ℝ) * (C_k.card : ℝ)) / (B : ℝ) := by field_simp [hBreal_pos.ne'] <;> ring
        _ ≥ (N - 1 : ℝ) / (B : ℝ) := by gcongr
      have hcount_ge : C_k.card ≥ Nat.ceil ((N - 1 : ℝ) / (B : ℝ)) :=
        Nat.ceil_le.mpr h10
      have h11 : C_k.card ≥ threshold := hthresh_le.trans hcount_ge
      have h13 : C_k ⊆ (F_k k).filter (fun U => x ∈ U.carrier) := by
        intro U hU
        have hUinSother : U ∈ S_other := (Finset.mem_filter.mp hU).1
        have hUinF : U ∈ F := by
          simp only [S_other, Finset.mem_erase] at hUinSother
          exact (Finset.mem_filter.mp hUinSother.2).1
        have hU_ne_T : U ≠ T := by
          simp only [S_other, Finset.mem_erase] at hUinSother <;> tauto
        have h_angle : σ k ≤ angleBetween T U ∧ angleBetween T U ≤ 2 * σ k := (Finset.mem_filter.mp hU).2
        have hxU : x ∈ U.carrier := by
          simp only [S_other, Finset.mem_erase] at hUinSother
          exact (Finset.mem_filter.mp hUinSother.2).2
        have h_in_Fk : U ∈ F_k k := by
          simp only [F_k, Finset.mem_filter] <;> exact ⟨hUinF, ⟨hU_ne_T, h_angle⟩⟩
        simp only [Finset.mem_filter] <;> exact ⟨h_in_Fk, hxU⟩
      have h14 : tubeMultiplicity (F_k k) x ≥ threshold := by
        have h15 : C_k.card ≤ tubeMultiplicity (F_k k) x := Finset.card_le_card h13
        exact h11.trans h15
      have h16 : x ∈ bandSet k := ⟨hxY, h14⟩
      simpa only [Set.mem_iUnion] using ⟨k, hk_in, h16⟩
    have h_meas_band : ∀ k ∈ Finset.range B, MeasurableSet (bandSet k) := by
      intro k _
      have h : MeasurableSet {x | tubeMultiplicity (F_k k) x ≥ threshold} := by
        have hmf2 : Measurable (tubeMultiplicity (F_k k)) := measurable_tubeMultiplicity (F_k k)
        have h_set : MeasurableSet (Set.Ici threshold : Set ℕ) := by simp
        exact MeasurableSet.preimage h_set hmf2
      exact (Y.measurable_carrier hTinF).inter h
    have h_sub : MeasureTheory.volume highSet ≤
        ∑ k ∈ Finset.range B, angleBandMass F Y T threshold (σ k) := by
      have h_mea : MeasureTheory.volume (⋃ k ∈ Finset.range B, bandSet k) ≤
          ∑ k ∈ Finset.range B, MeasureTheory.volume (bandSet k) := by
        have h_all_meas : ∀ k ∈ Finset.range B, MeasurableSet (bandSet k) := h_meas_band
        exact measure_biUnion_finset_le (Finset.range B) bandSet
      calc MeasureTheory.volume highSet
        ≤ MeasureTheory.volume (⋃ k ∈ Finset.range B, bandSet k) :=
          MeasureTheory.measure_mono h_pointwise
      _ ≤ ∑ k ∈ Finset.range B, MeasureTheory.volume (bandSet k) := h_mea
      _ = ∑ k ∈ Finset.range B, angleBandMass F Y T threshold (σ k) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [h_bandSet_eq k] <;> rfl
    have h_sum_ge2 : ∑ k ∈ Finset.range B, angleBandMass F Y T threshold (σ k) ≥ (lambda / 2) * V :=
      h_high_vol.trans h_sub
    rcases ennreal_sum_pigeonhole h_half_lamV_top h_sum_ge2 (Finset.nonempty_range_iff.mpr hB_pos.ne') with ⟨k, hk_in, hk_ge⟩
    have h_mass_eq : massThreshold * V = ((lambda / 2) * V) / (B : ENNReal) := by
      have hB_ne_zero : (B : ENNReal) ≠ 0 := by exact_mod_cast hB_pos.ne'
      have h2_ne_zero : (2 : ENNReal) ≠ 0 := by norm_num
      have hL_eq : ENNReal.ofReal L = 2 * (B : ENNReal) := by
        rw [hL_def, ENNReal.ofReal_mul] <;> norm_cast
      have h_eq1 : (lambda / (2 * (B : ENNReal))) * V = ((lambda / 2) * V) / (B : ENNReal) := by
        have hB_ne_zero' : (B : ENNReal) ≠ 0 := by exact_mod_cast hB_pos.ne'
        have h_inv : (2 * (B : ENNReal))⁻¹ = (2 : ENNReal)⁻¹ * (B : ENNReal)⁻¹ := by
          rw [ENNReal.mul_inv] <;> simp [hB_ne_zero']
        simp only [div_eq_mul_inv]
        rw [h_inv]
        <;> simp [mul_assoc, mul_comm, mul_left_comm]
      calc massThreshold * V
        = (lambda / ENNReal.ofReal L) * V := by rw [hmass_def]
      _ = (lambda / (2 * (B : ENNReal))) * V := by rw [hL_eq]
      _ = ((lambda / 2) * V) / (B : ENNReal) := h_eq1
    have hk_ge2 : massThreshold * V ≤ angleBandMass F Y T threshold (σ k) := by
      rw [h_mass_eq]
      have h_card : (Finset.range B).card = B := by simp
      simpa [h_card] using hk_ge
    exact ⟨k, hk_in, hk_ge2⟩
  choose k hk_in hk_cond using h_main1
  let k' (T : DeltaTube δ) : ℕ := if hT : T ∈ G then k T hT else 0
  have hk'_eq : ∀ (T : DeltaTube δ) (hT : T ∈ G), k' T = k T hT := by
    intro T hT
    simp [k', hT]
  let counts : ℕ → ℕ := fun b => (G.filter (fun T => k' T = b)).card
  have h_disj_fibers : ∀ b1 b2, b1 ≠ b2 →
      Disjoint (G.filter (fun T => k' T = b1)) (G.filter (fun T => k' T = b2)) := by
    intro b1 b2 hne
    simp only [Finset.disjoint_left, Finset.mem_filter]
    intro T hT1 hT2
    have h1 : k' T = b1 := hT1.2
    have h2 : k' T = b2 := hT2.2
    have h3 : b1 = b2 := h1.symm.trans h2
    exact hne h3
  have h_union_fibers : (Finset.biUnion (Finset.range B) (fun b => G.filter (fun T => k' T = b))) = G := by
    ext T
    simp only [Finset.mem_biUnion, Finset.mem_filter]
    constructor
    · rintro ⟨b, _, hT, _⟩; exact hT
    · intro hT
      have hkb : k' T ∈ Finset.range B := by
        rw [hk'_eq T hT]
        exact hk_in T hT
      exact ⟨k' T, hkb, hT, rfl⟩
  have h_sum_counts : ∑ b ∈ Finset.range B, counts b = G.card := by
    have h_disj' : (↑(Finset.range B) : Set ℕ).PairwiseDisjoint (fun b => G.filter (fun T => k' T = b)) := by
      intro b1 _ b2 _ hne
      exact h_disj_fibers b1 b2 hne
    have h5 : (Finset.biUnion (Finset.range B) (fun b => G.filter (fun T => k' T = b))).card =
        ∑ b ∈ Finset.range B, (G.filter (fun T => k' T = b)).card :=
      Finset.card_biUnion h_disj'
    rw [h_union_fibers] at h5
    simpa [counts] using h5.symm
  have hG_pos : 0 < G.card := by omega
  have h_sum2 : ∑ b ∈ Finset.range B, counts b ≥ G.card := by
    rw [h_sum_counts]
  rcases nat_sum_pigeonhole hG_pos h_sum2 (Finset.nonempty_range_iff.mpr hB_pos.ne') with ⟨b, hb_in, hb_ge⟩
  have hcount_real : (B : ℝ) * (counts b : ℝ) ≥ (G.card : ℝ) := by
    have h_nat : (Finset.range B).card * counts b ≥ G.card := hb_ge
    have h_real1 : ((Finset.range B).card : ℝ) * (counts b : ℝ) ≥ (G.card : ℝ) := by
      have h_le : (G.card : ℝ) ≤ (((Finset.range B).card * counts b : ℕ) : ℝ) := Nat.cast_le.mpr h_nat
      have h_mul : (((Finset.range B).card * counts b : ℕ) : ℝ) =
          ((Finset.range B).card : ℝ) * (counts b : ℝ) := by
        exact Nat.cast_mul (Finset.range B).card (counts b)
      rw [h_mul] at h_le
      exact h_le
    have h_card : (Finset.range B).card = B := by simp
    rw [h_card] at h_real1
    exact h_real1
  have hL_count : L * (counts b : ℝ) > (F.card : ℝ) := by
    have h1 : L = 2 * (B : ℝ) := hL_def
    rw [h1]
    have h2 : 2 * ((B : ℝ) * (counts b : ℝ)) ≥ 2 * (G.card : ℝ) :=
      mul_le_mul_of_nonneg_left hcount_real (by norm_num)
    have h2' : 2 * (B : ℝ) * (counts b : ℝ) = 2 * ((B : ℝ) * (counts b : ℝ)) := by ring
    have h3 : 2 * (G.card : ℝ) > (F.card : ℝ) := by exact_mod_cast hG_card
    linarith
  have h_final : Nat.ceil L * counts b ≥ F.card := by
    have h4 : (Nat.ceil L : ℝ) ≥ L := Nat.le_ceil L
    have h5 : (Nat.ceil L : ℝ) * (counts b : ℝ) ≥ L * (counts b : ℝ) := by gcongr
    have h6 : (Nat.ceil L : ℝ) * (counts b : ℝ) > (F.card : ℝ) := by linarith
    have h7 : (Nat.ceil L * counts b : ℝ) > (F.card : ℝ) := by simpa using h6
    have h8 : Nat.ceil L * counts b > F.card := by exact_mod_cast h7
    omega
  have h7 : counts b ≤ (F.filter fun T => massThreshold * V ≤ angleBandMass F Y T threshold (σ b)).card := by
    apply Finset.card_le_card
    intro T hT
    have hTinG : T ∈ G := (Finset.mem_filter.mp hT).1
    have h_eq : k' T = b := (Finset.mem_filter.mp hT).2
    have hTinF : T ∈ F := (Finset.mem_filter.mp hTinG).1
    have h_cond : massThreshold * V ≤ angleBandMass F Y T threshold (σ (k T hTinG)) := hk_cond T hTinG
    have h_k_eq : k' T = k T hTinG := hk'_eq T hTinG
    rw [h_k_eq] at h_eq
    rw [h_eq] at h_cond
    simp only [Finset.mem_filter] <;> exact ⟨hTinF, h_cond⟩
  have h8 : Nat.ceil L * (F.filter fun T => massThreshold * V ≤ angleBandMass F Y T threshold (σ b)).card ≥ F.card := by
    calc Nat.ceil L * (F.filter fun T => massThreshold * V ≤ angleBandMass F Y T threshold (σ b)).card
      ≥ Nat.ceil L * counts b := by gcongr
    _ ≥ F.card := h_final
  -- Prove δ ≤ π: if all multiplicities ≤ 1 then CaseI holds, so hCaseIFails gives two intersecting tubes
  have hδ_le_pi : δ ≤ Real.pi := by
    by_cases h : ∃ x, tubeMultiplicity F x ≥ 2
    · rcases h with ⟨x, hx⟩
      let S := F.filter (fun T => x ∈ T.carrier)
      have hS_card : S.card ≥ 2 := hx
      have h1 : 1 < S.card := by omega
      have hS2 := Finset.one_lt_card.mp h1
      rcases hS2 with ⟨T, hTinS, U, hUinS, hne⟩
      have hTinF : T ∈ F := (Finset.mem_filter.mp hTinS).1
      have hUinF : U ∈ F := (Finset.mem_filter.mp hUinS).1
      have hxT : x ∈ T.carrier := (Finset.mem_filter.mp hTinS).2
      have hxU : x ∈ U.carrier := (Finset.mem_filter.mp hUinS).2
      have h_inter : Set.Nonempty (T.carrier ∩ U.carrier) := ⟨x, hxT, hxU⟩
      have h_inter' : T.carrier ∩ U.carrier ≠ ∅ := Set.nonempty_iff_ne_empty.mp h_inter
      have h1 : δ ≤ angleBetween T U := hAngleSep T hTinF U hUinF hne h_inter'
      have h2 : angleBetween T U ≤ Real.pi := Real.arccos_le_pi _
      linarith
    · have h' : ∀ x, tubeMultiplicity F x ≤ 1 := by
        simpa [not_exists] using h
      have hH_eq_F : H = F := by
        apply Finset.filter_true_of_mem
        intro T hTinF
        have h_set : {x : Point3 | tubeMultiplicity F x ≤ N - 1} = Set.univ := by
          apply Set.eq_univ_of_forall
          intro x
          have h3 : tubeMultiplicity F x ≤ 1 := h' x
          have h4 : tubeMultiplicity F x ≤ N - 1 := by omega
          exact h4
        have h_low_eq : lowMass F Y (N - 1) T = MeasureTheory.volume (Y.carrier T) := by
          rw [lowMass, h_set]
          <;> simp
        rw [h_low_eq]
        have h5 : lambda / 2 * V ≤ lambda * V := by
          have h6 : lambda / 2 ≤ lambda := by
            have h7 : (1 / 2 : ENNReal) ≤ 1 := by norm_num
            have h8 : lambda * (1 / 2 : ENNReal) ≤ lambda := by
              calc lambda * (1 / 2 : ENNReal)
                ≤ lambda * 1 := by gcongr
              _ = lambda := by simp
            simpa [div_eq_mul_inv] using h8
          have h9 : lambda / 2 * V ≤ lambda * V := by
            gcongr
          exact h9
        exact h5.trans (hPerTube T hTinF)
      have hH_eq_filter : H = F.filter (fun T => (lambda / 2) * T.volume ≤ lowMass F Y (N - 1) T) := by
        apply Finset.filter_congr
        intro T hTinF
        have h_vol : T.volume = V := hUniformVolume T hTinF
        rw [h_vol]
        <;> rfl
      have h_filter_eq_F : (F.filter (fun T => (lambda / 2) * T.volume ≤ lowMass F Y (N - 1) T)) = F := by
        calc (F.filter (fun T => (lambda / 2) * T.volume ≤ lowMass F Y (N - 1) T))
          = H := hH_eq_filter.symm
        _ = F := hH_eq_F
      have h8 : 2 * (F.filter (fun T => (lambda / 2) * T.volume ≤ lowMass F Y (N - 1) T)).card ≥ F.card := by
        rw [h_filter_eq_F]
        have h9 : 0 ≤ F.card := by positivity
        nlinarith
      have hCaseI : CaseI F Y lambda (N - 1) := by
        simpa [CaseI] using h8
      exact False.elim (hCaseIFails hCaseI)
  have hσ1 : δ ≤ σ b := by
    rw [hσ_def]
    have h9 : (2 : ℝ)^b ≥ 1 := by
      have h91 : (1 : ℝ) ≤ (2 : ℝ) := by norm_num
      have h92 : (1 : ℝ)^b ≤ (2 : ℝ)^b := by
        have h : ∀ n : ℕ, (1 : ℝ)^n ≤ (2 : ℝ)^n := by
          intro n
          induction n with
          | zero => norm_num
          | succ n ih =>
            simp [pow_succ] at * <;> nlinarith
        exact h b
      have h93 : (1 : ℝ)^b = 1 := by simp
      rw [h93] at h92
      exact h92
    nlinarith
  -- Helper: massThreshold ≤ lambda (since L ≥ 2)
  have h_mass_le_lambda : massThreshold ≤ lambda := by
    have hB_ge1 : B ≥ 1 := by omega
    have hL_ge2 : L ≥ 2 := by
      rw [hL_def]
      <;> norm_cast <;> omega
    have h1 : (2 : ENNReal) ≤ ENNReal.ofReal L := by
      have h11 : (2 : ℝ) ≤ L := by exact_mod_cast hL_ge2
      have h12 : (2 : ENNReal) = ENNReal.ofReal 2 := by norm_cast
      rw [h12]
      exact ENNReal.ofReal_le_ofReal h11
    have h2 : lambda / ENNReal.ofReal L ≤ lambda / 2 := by gcongr
    have h3 : lambda / 2 ≤ lambda := by
      have h_div_def : lambda / (2 : ENNReal) = lambda * (2 : ENNReal)⁻¹ := by rfl
      rw [h_div_def]
      have h_inv_le : (2 : ENNReal)⁻¹ ≤ 1 := by norm_num
      calc lambda * (2 : ENNReal)⁻¹
        ≤ lambda * 1 := mul_le_mul_left' h_inv_le lambda
      _ = lambda := by simp
    rw [hmass_def]
    exact h2.trans h3
  -- Main case split
  by_cases h_triv : threshold = 0 ∨ massThreshold * V = 0
  · -- Trivial case: directly use trivialCaseII
    have h_triv' : Nat.ceil (N / L) = 0 ∨ (lambda / ENNReal.ofReal L) * V = 0 := by
      cases h_triv with
      | inl h =>
        have h' : Nat.ceil (N / L) = 0 := by
          rw [hthreshold_def] at h; exact h
        exact Or.inl h'
      | inr h =>
        have h' : (lambda / ENNReal.ofReal L) * V = 0 := by
          have h1 : massThreshold * V = 0 := h
          have h2 : (lambda / ENNReal.ofReal L) * V = massThreshold * V := by rw [hmass_def]
          rw [h2]; exact h1
        exact Or.inr h'
    refine ⟨δ, by linarith, hδ_le_pi, trivialCaseII hL_pos hL_one V hUniformVolume hPerTube h_mass_le_lambda h_triv'⟩
  · -- Non-trivial case: threshold > 0 and massThreshold * V > 0
    have h_not_thresh : threshold ≠ 0 := by
      intro h; exact h_triv (Or.inl h)
    have h_not_mass : massThreshold * V ≠ 0 := by
      intro h; exact h_triv (Or.inr h)
    have h_thresh_pos : 0 < threshold := Nat.pos_of_ne_zero h_not_thresh
    have hF_pos : 0 < F.card := by
      by_contra h2
      have h3 : F.card = 0 := by omega
      have h4 : G.card = 0 := by
        have h5 : G ⊆ F := Finset.filter_subset _ _
        have h6 : G.card ≤ F.card := Finset.card_le_card h5
        rw [h3] at h6; omega
      rw [h4] at hG_card
      omega
    have hk_cond' : ∀ T ∈ G, massThreshold * V ≤ angleBandMass F Y T threshold (σ (k' T)) := by
      intro T hTinG
      have h_eq : k' T = k T hTinG := hk'_eq T hTinG
      have h_cond := hk_cond T hTinG
      rw [h_eq]
      exact h_cond
    have hcounts_eq : ∀ c, counts c = (G.filter (fun T => k' T = c)).card := by
      intro c; rfl
    have hσ_def' : ∀ k, σ k = (2 : ℝ)^k * δ := by
      intro k; rw [hσ_def] <;> rfl
    exact finishNonTrivialCase hδ hδ_le_pi hUniformVolume B K hK_eq hK_ceil L hL_pos hL_one b hb_in σ hσ_def' threshold hthreshold_def massThreshold hmass_def G (Finset.filter_subset _ _) k' hk_cond' counts hcounts_eq h_final hF_pos h8 h_not_mass h_thresh_pos

/-- Core hard lemma: from Case I(N-1) failing, derive Case II at N. -/
lemma caseIIFromFailure {δ : ℝ} (hδ : 0 < δ)
    (F : Kakeya.TubeFamily δ) (Y : Kakeya.Shading F)
    (lambda : ENNReal) (hlam_top : lambda ≠ ⊤)
    (N : ℕ) (hNge2 : N ≥ 2)
    (V : ENNReal) (hV_top : V ≠ ⊤)
    (hUniformVolume : ∀ T ∈ F, T.volume = V)
    (hPerTube : ∀ T ∈ F, lambda * V ≤ MeasureTheory.volume (Y.carrier T))
    (hAngleSep : ∀ T ∈ F, ∀ U ∈ F, T ≠ U → T.carrier ∩ U.carrier ≠ ∅ →
      δ ≤ angleBetween T U)
    (hCaseIFails : ¬CaseI F Y lambda (N - 1)) :
    ∃ (σ : ℝ), δ ≤ σ ∧ σ ≤ Real.pi ∧
      CaseII F Y lambda N σ (2 * (numBands δ : ℝ)) := by
  let B : ℕ := numBands δ
  have hB_pos : 0 < B := by
    dsimp only [B, numBands] <;> apply Nat.succ_pos
  let K : ℕ := B - 1
  have hK_eq : K = Nat.ceil (Real.log (Real.pi / δ) / Real.log 2) := by
    simp [K, B, numBands] <;> omega
  have hK_pow : Real.pi / δ ≤ (2 : ℝ)^K := by
    let y := Real.log (Real.pi / δ) / Real.log 2
    have h1 : y ≤ (K : ℝ) := by
      rw [show (K : ℝ) = (Nat.ceil y : ℝ) from by exact_mod_cast hK_eq]
      exact Nat.le_ceil y
    have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have h3 : Real.log (Real.pi / δ) ≤ (K : ℝ) * Real.log 2 := by
      have h4 : Real.log (Real.pi / δ) = y * Real.log 2 := by
        dsimp only [y]
        field_simp [hlog2_pos.ne'] <;> ring
      rw [h4]
      gcongr
    have h4 : 0 < Real.pi / δ := by positivity
    have h5 : Real.log (Real.pi / δ) ≤ Real.log ((2 : ℝ)^K) := by
      have h6 : Real.log ((2 : ℝ)^K) = (K : ℝ) * Real.log 2 := by
        simp [Real.log_pow] <;> ring
      rw [h6]; exact h3
    exact (Real.log_le_log_iff h4 (by positivity)).mp h5
  let L : ℝ := 2 * (B : ℝ)
  have hL_pos : 0 < L := by positivity
  have hL_one : 1 ≤ L := by
    have h : (B : ℝ) ≥ 1 := by exact_mod_cast hB_pos
    linarith
  have hL_def : L = 2 * (B : ℝ) := by rfl
  have hthresh_le : Nat.ceil (N / L) ≤ Nat.ceil ((N - 1 : ℝ) / (B : ℝ)) :=
    threshold_ineq N B hNge2 hB_pos
  have h_main := caseIIFromFailureCore hδ F Y lambda hlam_top N hNge2 V hV_top
    hUniformVolume hPerTube hAngleSep hCaseIFails B hB_pos K (by rfl) hK_eq hK_pow L hL_pos hL_one hL_def hthresh_le
  rcases h_main with ⟨σ, hσ1, hσ2, hCaseII⟩
  exact ⟨σ, hσ1, hσ2, hCaseII⟩

lemma numBands_bound (δ : ℝ) (hδ : 0 < δ) (hδone : δ ≤ 1) :
    2 * (numBands δ : ℝ) ≤ 6 * Real.log (Real.pi / δ) + 6 := by
  have hlog2_gt : Real.log 2 ≥ 1 / 3 := by
    have h : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    linarith
  have h1 : 0 ≤ Real.log (Real.pi / δ) := by
    apply Real.log_nonneg
    have h2 : 1 ≤ Real.pi / δ := by
      rw [one_le_div hδ]
      have h4 : (1 : ℝ) < Real.pi := by
        have h5 : (3 : ℝ) < Real.pi := Real.pi_gt_three
        linarith
      linarith
    exact h2
  set x : ℝ := Real.log (Real.pi / δ) / Real.log 2 with hx
  have h_ceil_le : Nat.ceil x ≤ Nat.floor x + 1 := Nat.ceil_le_floor_add_one x
  have h3 : (Nat.ceil x : ℝ) ≤ x + 1 := by
    have hx_nonneg : 0 ≤ x := by positivity
    have h41 : (Nat.ceil x : ℝ) ≤ ((Nat.floor x + 1 : ℕ) : ℝ) := Nat.cast_le.mpr h_ceil_le
    have h42 : ((Nat.floor x + 1 : ℕ) : ℝ) = (Nat.floor x : ℝ) + 1 := by
      simp [Nat.cast_add]
    rw [h42] at h41
    have h5 : (Nat.floor x : ℝ) ≤ x := Nat.floor_le hx_nonneg
    linarith
  have h4 : x ≤ 3 * Real.log (Real.pi / δ) := by
    rw [hx]
    have h5 : Real.log 2 ≥ 1 / 3 := hlog2_gt
    calc Real.log (Real.pi / δ) / Real.log 2
      ≤ Real.log (Real.pi / δ) / (1 / 3) := by gcongr
    _ = 3 * Real.log (Real.pi / δ) := by ring
  have h7 : (numBands δ : ℝ) = (Nat.ceil x : ℝ) + 1 := by
    simp [numBands, hx] <;> norm_cast
  rw [h7]
  have h6 : 2 * ((Nat.ceil x : ℝ) + 1) ≤ 2 * (x + 2) := by
    have h7 : (Nat.ceil x : ℝ) + 1 ≤ x + 2 := by linarith
    gcongr
  calc 2 * ((Nat.ceil x : ℝ) + 1)
    ≤ 2 * (x + 2) := h6
  _ = 2 * x + 4 := by ring
  _ ≤ 2 * (3 * Real.log (Real.pi / δ)) + 4 := by gcongr
  _ = 6 * Real.log (Real.pi / δ) + 4 := by ring
  _ ≤ 6 * Real.log (Real.pi / δ) + 6 := by linarith

theorem pigeonhole {δ : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1)
    (F : Kakeya.TubeFamily δ) (Y : Kakeya.Shading F)
    (lambda : ENNReal) (hlam : lambda ≠ 0) (hlam_top : lambda ≠ ⊤)
    (hPerTube : ∀ T ∈ F, lambda * T.volume ≤ MeasureTheory.volume (Y.carrier T))
    (hAngleSep : ∀ T ∈ F, ∀ U ∈ F, T ≠ U → T.carrier ∩ U.carrier ≠ ∅ →
      δ ≤ angleBetween T U)
    (hUniformVolume : ∀ T ∈ F, T.volume = Kakeya.deltaTubeVolume δ) :
    ∃ (N : ℕ) (L : ℝ), 0 < L ∧ 1 ≤ L ∧
      L ≤ 6 * Real.log (Real.pi / δ) + 6 ∧
      CaseI F Y lambda N ∧
      (N ≤ L ∨ ∃ σ : ℝ, δ ≤ σ ∧ σ ≤ Real.pi ∧ CaseII F Y lambda N σ L) := by
  let M := F.card
  let V := Kakeya.deltaTubeVolume δ
  let K := numBands δ
  let L : ℝ := 2 * (K : ℝ)
  have hK1 : 1 ≤ K := by
    simp [K, numBands] <;> omega
  have hL_pos : 0 < L := by
    have h : (K : ℝ) ≥ 1 := by exact_mod_cast hK1
    linarith
  have hL_one : 1 ≤ L := by
    have h : (K : ℝ) ≥ 1 := by exact_mod_cast hK1
    linarith
  have hL_bound : L ≤ 6 * Real.log (Real.pi / δ) + 6 := by
    have h : L = 2 * (K : ℝ) := by rfl
    rw [h]
    exact numBands_bound δ hδ hδone
  by_cases hM0 : M = 0
  · refine' ⟨0, L, hL_pos, hL_one, hL_bound, _⟩
    have h : CaseI F Y lambda 0 := by
      simp [CaseI, hM0] <;> omega
    have h0 : (0 : ℝ) ≤ L := le_of_lt hL_pos
    have h02 : (0 : ℕ) ≤ L := by exact_mod_cast h0
    exact ⟨h, Or.inl h02⟩
  · have hMpos : 0 < M := Nat.pos_of_ne_zero hM0
    have h_fM : CaseI F Y lambda M := by
      simp [CaseI]
      have h1 : ∀ T ∈ F, (lambda / 2) * T.volume ≤ lowMass F Y M T := by
        intro T hT
        have h2 : lowMass F Y M T = MeasureTheory.volume (Y.carrier T) := lowMass_max F Y T hT
        rw [h2]
        have h3 : lambda * T.volume ≤ MeasureTheory.volume (Y.carrier T) := hPerTube T hT
        have h4 : (lambda / 2) * T.volume ≤ lambda * T.volume := by
          have h5 : (lambda / 2) ≤ lambda := by
            have h6 : lambda / 2 = lambda * (1 / 2 : ENNReal) := by
              simp [div_eq_mul_inv] <;> ring
            rw [h6]
            have h7 : (1 / 2 : ENNReal) ≤ 1 := by norm_num
            have h8 : lambda * (1 / 2 : ENNReal) ≤ lambda * (1 : ENNReal) := by
              exact mul_le_mul_of_nonneg_left h7 (by simp)
            simpa using h8
          gcongr
        exact h4.trans h3
      have h2 : F.filter (fun T => (lambda / 2) * T.volume ≤ lowMass F Y M T) = F := by
        apply Finset.filter_true_of_mem; exact h1
      rw [h2] <;> omega
    have h_exists : ∃ N, CaseI F Y lambda N := ⟨M, h_fM⟩
    let N := Nat.find h_exists
    have hN_caseI : CaseI F Y lambda N := Nat.find_spec h_exists
    by_cases h_small : (N : ℝ) ≤ L
    · exact ⟨N, L, hL_pos, hL_one, hL_bound, hN_caseI, Or.inl h_small⟩
    · have hN_gt_L : (N : ℝ) > L := by linarith
      have hNge2 : N ≥ 2 := by
        have h1 : L ≥ 1 := hL_one
        by_contra h
        have h2 : N ≤ 1 := by omega
        have h3 : (N : ℝ) ≤ 1 := by exact_mod_cast h2
        linarith
      have h_pred_fails : ¬CaseI F Y lambda (N - 1) :=
        Nat.find_min h_exists (by omega)
      have hV_top : V ≠ ⊤ := by
        simp only [V, Kakeya.deltaTubeVolume]
        let e0 : Point3 := EuclideanSpace.single (0 : Fin 3) 1
        let seg := Kakeya.unitSegment (0 : Point3) e0
        have h1 : seg ⊆ Metric.closedBall (0 : Point3) 1 := by
          intro x hx
          rcases hx with ⟨t, ht, rfl⟩
          have h2 : dist (0 + t • e0) (0 : Point3) ≤ 1 := by
            have h3 : dist (0 + t • e0) (0 : Point3) = ‖t • e0‖ := by simp [dist_eq_norm]
            rw [h3]
            have h4 : ‖t • e0‖ = |t| * ‖e0‖ := by
              have h41 : ‖t • e0‖ = ‖t‖ * ‖e0‖ := by rw [norm_smul]
              have h42 : ‖t‖ = |t| := by simp
              rw [h41, h42]
            rw [h4]
            have h5 : ‖e0‖ = 1 := by
              simp [e0, EuclideanSpace.norm_eq] <;> norm_num
            rw [h5]
            have h6 : |t| ≤ 1 := by
              rw [abs_le] <;> constructor <;> linarith [ht.1, ht.2]
            linarith
          exact h2
        have hseg_bdd : Bornology.IsBounded seg :=
          (Metric.isBounded_iff_subset_closedBall (0 : Point3)).mpr ⟨1, h1⟩
        have hcthick_bdd : Bornology.IsBounded (Metric.cthickening δ seg) := by
          have h : Bornology.IsBounded seg := hseg_bdd
          exact Bornology.IsBounded.cthickening (h := h)
        rcases (Metric.isBounded_iff_subset_closedBall (0 : Point3)).mp hcthick_bdd with ⟨r, hsub⟩
        have hball : MeasureTheory.volume (Metric.closedBall (0 : Point3) r) < ⊤ :=
          MeasureTheory.measure_closedBall_lt_top
        exact (MeasureTheory.measure_lt_top_mono hsub hball).ne
      have hPerTube' : ∀ T ∈ F, lambda * V ≤ MeasureTheory.volume (Y.carrier T) := by
        intro T hT
        have h1 : lambda * T.volume ≤ MeasureTheory.volume (Y.carrier T) := hPerTube T hT
        have h2 : T.volume = V := hUniformVolume T hT
        rw [h2] at h1
        exact h1
      have h_main : ∃ (σ : ℝ), δ ≤ σ ∧ σ ≤ Real.pi ∧
          CaseII F Y lambda N σ (2 * (numBands δ : ℝ)) :=
        caseIIFromFailure hδ F Y lambda hlam_top N hNge2 V hV_top
          hUniformVolume hPerTube' hAngleSep h_pred_fails
      rcases h_main with ⟨σ, hσ1, hσ2, hCaseII⟩
      exact ⟨N, L, hL_pos, hL_one, hL_bound, hN_caseI, Or.inr ⟨σ, hσ1, hσ2, hCaseII⟩⟩

end Kakeya.Hairbrush
