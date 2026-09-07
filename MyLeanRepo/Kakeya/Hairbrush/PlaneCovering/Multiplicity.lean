import MyLeanRepo.Kakeya.Hairbrush.PlaneCovering.Basic
import MyLeanRepo.Kakeya.AssertionD
import MyLeanRepo.Kakeya.Hairbrush.Helpers
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

noncomputable section

open MeasureTheory Metric Set Finset Real
open scoped Classical

namespace Kakeya.Assouad

variable {δ : ℝ}

/-- Helper: if each `k ∈ active` has `n k ∈ {-2,-1,0,1,2}` and each fiber has size ≤ C,
then `active.card ≤ 5 * C`. -/
lemma multiplicity_final_bound {K : ℕ} {active : Finset (Fin K)} {n : Fin K → ℤ} {C : ℕ}
    (h4 : ∀ k ∈ active, n k ∈ ({-2, -1, 0, 1, 2} : Finset ℤ))
    (h_count : ∀ n_val ∈ ({-2, -1, 0, 1, 2} : Finset ℤ),
      (active.filter (fun k => n k = n_val)).card ≤ C) :
    active.card ≤ 5 * C := by
  let S : Finset ℤ := {-2, -1, 0, 1, 2}
  have h_eq : ∑ n_val ∈ S, (active.filter (fun k => n k = n_val)).card = active.card := by
    have h1 : ∑ n_val ∈ S, (active.filter (fun k => n k = n_val)).card =
        (active.filter (fun k => n k ∈ S)).card :=
      Finset.sum_card_fiberwise_eq_card_filter active S n
    rw [h1]
    have h2 : active.filter (fun k => n k ∈ S) = active := by
      ext k; simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hk, _⟩; exact hk
      · intro hk; exact ⟨hk, h4 k hk⟩
    rw [h2]
  have h_sum : ∑ n_val ∈ S, (active.filter (fun k => n k = n_val)).card ≤ 5 * C := by
    have h_each : ∀ n_val ∈ S, (active.filter (fun k => n k = n_val)).card ≤ C := h_count
    have h_card5 : S.card = 5 := by decide
    calc ∑ n_val ∈ S, _ ≤ ∑ n_val ∈ S, C := Finset.sum_le_sum h_each
      _ = S.card * C := by rw [Finset.sum_const] <;> ring
      _ = 5 * C := by rw [h_card5] <;> ring
  rw [h_eq] at h_sum
  exact h_sum

/-- Bound: `arcsin ε ≤ (π/2) * ε` for `0 ≤ ε ≤ 1`. -/
lemma arcsin_le_pi_div_two_mul {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    Real.arcsin ε ≤ (Real.pi / 2) * ε := by
  have h_t1 : 0 ≤ Real.arcsin ε := Real.arcsin_nonneg.mpr hε0
  have h_t2 : Real.arcsin ε ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two ε
  have h : (2 / Real.pi) * Real.arcsin ε ≤ Real.sin (Real.arcsin ε) :=
    Real.mul_le_sin h_t1 h_t2
  have h_sin : Real.sin (Real.arcsin ε) = ε := Real.sin_arcsin (by linarith) hε1
  rw [h_sin] at h
  have h' : (Real.pi / 2) * ((2 / Real.pi) * Real.arcsin ε) ≤ (Real.pi / 2) * ε :=
    mul_le_mul_of_nonneg_left h (by positivity)
  have h1 : (Real.pi / 2) * (2 / Real.pi) = 1 := by
    field_simp [Real.pi_ne_zero] <;> norm_num
  have h2 : (Real.pi / 2) * ((2 / Real.pi) * Real.arcsin ε) =
      ((Real.pi / 2) * (2 / Real.pi)) * Real.arcsin ε :=
    Eq.symm (mul_assoc (Real.pi / 2) (2 / Real.pi) (Real.arcsin ε))
  have h'' : (Real.pi / 2) * ((2 / Real.pi) * Real.arcsin ε) = Real.arcsin ε := by
    rw [h2, h1] <;> simp
  rw [h''] at h'
  exact h'

/-- A natural-number index whose real cast lies in an interval has controlled
cardinality. The extra `3` is harmless in the plane-covering application and
keeps both signs of the lower endpoint uniform. -/
lemma card_fin_interval_le_ceil_add_three
    {K : ℕ} (s : Finset (Fin K)) (a b : ℝ)
    (h_int : ∀ k ∈ s, a < (k : ℝ) ∧ (k : ℝ) ≤ b) :
    s.card ≤ Nat.ceil (b - a + 3) := by
  let s_nat : Finset ℕ := s.image (fun k : Fin K => (k : ℕ))
  have h_card : s.card = s_nat.card := by
    rw [Finset.card_image_of_injOn]
    intro x _ y _ h
    exact Fin.ext h
  by_cases h_empty : s_nat = ∅
  · rw [h_card, h_empty]
    simp
  · have h_nonempty : s_nat.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr h_empty
    rcases h_nonempty with ⟨m, hm⟩
    rcases Finset.mem_image.mp hm with ⟨k0, hk0, rfl⟩
    have h_ab : a < b := by
      exact (h_int k0 hk0).1.trans_le (h_int k0 hk0).2
    have h_b_nonneg : 0 ≤ b := by
      exact (Nat.cast_nonneg k0).trans (h_int k0 hk0).2
    by_cases ha : 0 ≤ a
    · have h_sub :
          s_nat ⊆
            Finset.Ico (Nat.floor a + 1) (Nat.ceil b + 1) := by
        intro m hm
        rcases Finset.mem_image.mp hm with ⟨k, hk, rfl⟩
        have hk_int := h_int k hk
        have h_floor_le : (Nat.floor a : ℝ) ≤ a :=
          Nat.floor_le ha
        have h_lo : Nat.floor a + 1 ≤ (k : ℕ) := by
          have : (Nat.floor a : ℝ) < (k : ℝ) :=
            h_floor_le.trans_lt hk_int.1
          exact Nat.succ_le_iff.mpr (Nat.cast_lt.mp this)
        have h_hi : (k : ℕ) < Nat.ceil b + 1 := by
          have : (k : ℝ) ≤ (Nat.ceil b : ℝ) :=
            hk_int.2.trans (Nat.le_ceil b)
          exact Nat.lt_succ_iff.mpr (Nat.cast_le.mp this)
        exact Finset.mem_Ico.mpr ⟨h_lo, h_hi⟩
      have h_card_sub :
          s_nat.card ≤
            (Finset.Ico (Nat.floor a + 1)
              (Nat.ceil b + 1)).card :=
        Finset.card_le_card h_sub
      rw [Nat.card_Ico] at h_card_sub
      have h_floor_ceil : Nat.floor a ≤ Nat.ceil b := by
        have hcast :
            (Nat.floor a : ℝ) ≤ (Nat.ceil b : ℝ) :=
          (Nat.floor_le ha).trans
            ((le_of_lt h_ab).trans (Nat.le_ceil b))
        exact_mod_cast hcast
      have h_diff :
          (Nat.ceil b + 1) - (Nat.floor a + 1) =
            Nat.ceil b - Nat.floor a := by
        omega
      rw [h_diff] at h_card_sub
      have h_diff_bound :
          Nat.ceil b - Nat.floor a ≤
            Nat.ceil (b - a) + 2 := by
        have hceil : (Nat.ceil b : ℝ) < b + 1 :=
          Nat.ceil_lt_add_one h_b_nonneg
        have hfloor : a - 1 < (Nat.floor a : ℝ) := by
          linarith [Nat.lt_floor_add_one a]
        have hround :
            (Nat.ceil b : ℝ) - Nat.floor a < b - a + 2 := by
          linarith
        have htarget :
            b - a + 2 ≤ (Nat.ceil (b - a) : ℝ) + 2 := by
          gcongr
          exact Nat.le_ceil (b - a)
        have hreal :
            ((Nat.ceil b - Nat.floor a : ℕ) : ℝ) <
              ((Nat.ceil (b - a) + 2 : ℕ) : ℝ) := by
          rw [Nat.cast_sub h_floor_ceil]
          norm_num only [Nat.cast_add, Nat.cast_ofNat]
          linarith
        have hnat :
            Nat.ceil b - Nat.floor a <
              Nat.ceil (b - a) + 2 := by
          exact_mod_cast hreal
        exact hnat.le
      have hceil_add :
          Nat.ceil (b - a) + 2 ≤ Nat.ceil (b - a + 3) := by
        have h_nonneg : 0 ≤ b - a := sub_nonneg.mpr (le_of_lt h_ab)
        have hceil_eq :
            Nat.ceil (b - a + 3) = Nat.ceil (b - a) + 3 := by
          convert Nat.ceil_add_natCast h_nonneg 3 using 1 <;> norm_num
        rw [hceil_eq]
        omega
      rw [h_card]
      exact h_card_sub.trans (h_diff_bound.trans hceil_add)
    · have h_a_neg : a < 0 := lt_of_not_ge ha
      have h_sub :
          s_nat ⊆ Finset.range (Nat.ceil b + 1) := by
        intro m hm
        rcases Finset.mem_image.mp hm with ⟨k, hk, rfl⟩
        have hle : (k : ℝ) ≤ (Nat.ceil b : ℝ) :=
          (h_int k hk).2.trans (Nat.le_ceil b)
        exact Finset.mem_range.mpr
          (Nat.lt_succ_iff.mpr (Nat.cast_le.mp hle))
      have h_card_sub :
          s_nat.card ≤ (Finset.range (Nat.ceil b + 1)).card :=
        Finset.card_le_card h_sub
      rw [Finset.card_range] at h_card_sub
      have hceil :
          Nat.ceil b + 1 ≤ Nat.ceil (b - a) + 2 := by
        have : Nat.ceil b ≤ Nat.ceil (b - a) := by
          apply Nat.ceil_mono
          linarith
        omega
      have hceil_add :
          Nat.ceil (b - a) + 2 ≤ Nat.ceil (b - a + 3) := by
        have h_nonneg : 0 ≤ b - a := sub_nonneg.mpr (le_of_lt h_ab)
        have hceil_eq :
            Nat.ceil (b - a + 3) = Nat.ceil (b - a) + 3 := by
          convert Nat.ceil_add_natCast h_nonneg 3 using 1 <;> norm_num
        rw [hceil_eq]
        omega
      rw [h_card]
      exact h_card_sub.trans (hceil.trans hceil_add)

/-- Convert angular and bin inequalities into an interval for the bin index. -/
lemma plane_covering_index_interval
    {w φ φx ρ q : ℝ} {k : ℕ}
    (hw : 0 < w)
    (hbin1 : (k : ℝ) * w ≤ φ)
    (hbin2 : φ < ((k : ℝ) + 1) * w)
    (hnear : |φx - φ - q| ≤ ρ) :
    (φx - q - ρ) / w - 1 < (k : ℝ) ∧
      (k : ℝ) ≤ (φx - q + ρ) / w := by
  have hbounds := abs_le.mp hnear
  have hlo : φx - q - ρ ≤ φ := by
    linarith
  have hhi : φ ≤ φx - q + ρ := by
    linarith
  constructor
  · have hdiv :
        (φx - q - ρ) / w < (k : ℝ) + 1 :=
      (div_lt_iff₀ hw).2 (hlo.trans_lt hbin2)
    linarith
  · exact (le_div_iff₀ hw).2 (hbin1.trans hhi)

/-- The numerical estimate closing the plane-covering multiplicity bound. -/
lemma plane_covering_numeric_ceiling_bound
    {δ σ r : ℝ} (hδ : 0 < δ) (hσ : 0 < σ) (hr : 0 < r)
    (hrange : 3 * δ ≤ r) :
    (5 * Nat.ceil
        (2 * Real.arcsin (3 * δ / r) / (δ / σ) + 4) : ℝ) ≤
      100 * (σ / r + 1) := by
  have hε0 : 0 ≤ 3 * δ / r := by positivity
  have hε1 : 3 * δ / r ≤ 1 := (div_le_one hr).mpr hrange
  have harc :
      Real.arcsin (3 * δ / r) ≤
        (Real.pi / 2) * (3 * δ / r) :=
    arcsin_le_pi_div_two_mul hε0 hε1
  have hterm_nonneg :
      0 ≤ 2 * Real.arcsin (3 * δ / r) / (δ / σ) + 4 := by
    have harc_nonneg :
        0 ≤ Real.arcsin (3 * δ / r) :=
      Real.arcsin_nonneg.mpr hε0
    positivity
  have hceil :
      (Nat.ceil
          (2 * Real.arcsin (3 * δ / r) / (δ / σ) + 4) : ℝ) <
        2 * Real.arcsin (3 * δ / r) / (δ / σ) + 5 := by
    have h :=
      Nat.ceil_lt_add_one hterm_nonneg
    linarith
  have hscaled :
      (5 * Nat.ceil
          (2 * Real.arcsin (3 * δ / r) / (δ / σ) + 4) : ℝ) <
        5 *
          (2 * Real.arcsin (3 * δ / r) / (δ / σ) + 5) := by
    exact_mod_cast mul_lt_mul_of_pos_left hceil (by norm_num : (0 : ℝ) < 5)
  have harc_scaled :
      2 * Real.arcsin (3 * δ / r) / (δ / σ) ≤
        3 * Real.pi * (σ / r) := by
    have hmul :
        2 * Real.arcsin (3 * δ / r) ≤
          2 * ((Real.pi / 2) * (3 * δ / r)) := by
      gcongr
    have hdiv :
        2 * Real.arcsin (3 * δ / r) / (δ / σ) ≤
          (2 * ((Real.pi / 2) * (3 * δ / r))) / (δ / σ) := by
      exact div_le_div_of_nonneg_right hmul (by positivity)
    have heq :
        (2 * ((Real.pi / 2) * (3 * δ / r))) / (δ / σ) =
          3 * Real.pi * (σ / r) := by
      field_simp [hδ.ne', hσ.ne', hr.ne']
    rwa [heq] at hdiv
  have hmiddle :
      5 *
          (2 * Real.arcsin (3 * δ / r) / (δ / σ) + 5) ≤
        5 * (3 * Real.pi * (σ / r) + 5) := by
    gcongr
  have hlast :
      5 * (3 * Real.pi * (σ / r) + 5) ≤
        100 * (σ / r + 1) := by
    have hpi : Real.pi < 4 := Real.pi_lt_four
    have hratio : 0 < σ / r := by positivity
    nlinarith
  exact le_trans hscaled.le (hmiddle.trans hlast)

/-- Fixed-point angular estimate used in the multiplicity argument. -/
lemma plane_covering_active_sine_bound
    {δ r : ℝ} (hδ : 0 < δ) (hr : 0 < r)
    (T U : Kakeya.DeltaTube δ)
    (e1 e2 : Point3)
    (he1 : ‖e1‖ = 1) (he2 : ‖e2‖ = 1)
    (hT1 : inner ℝ T.direction e1 = 0)
    (hT2 : inner ℝ T.direction e2 = 0)
    (h12 : inner ℝ e1 e2 = 0)
    (A : Point3 ≃ₗᵢ[ℝ] Point3)
    (hA0 : ∀ z, (A z) 0 = inner ℝ z T.direction)
    (hA1 : ∀ z, (A z) 1 = inner ℝ z e1)
    (hA2 : ∀ z, (A z) 2 = inner ℝ z e2)
    (hperpPos :
      0 < ‖perpProj T.direction U.direction‖)
    (hcoords :
      inner ℝ U.direction e1 ≠ 0 ∨
        inner ℝ U.direction e2 ≠ 0)
    (hinter : (T.carrier ∩ U.carrier).Nonempty)
    (x : Point3) (hxU : x ∈ U.carrier)
    (hxcoords :
      inner ℝ (perpProj T.direction (x - T.base)) e1 ≠ 0 ∨
        inner ℝ (perpProj T.direction (x - T.base)) e2 ≠ 0)
    (hxperp :
      r ≤ ‖perpProj T.direction (x - T.base)‖) :
    |Real.sin
      (angleOfCoords
          (inner ℝ (perpProj T.direction (x - T.base)) e1)
          (inner ℝ (perpProj T.direction (x - T.base)) e2) -
        angleOfCoords
          (inner ℝ U.direction e1)
          (inner ℝ U.direction e2))| ≤
      3 * δ / r := by
  let x_perp := perpProj T.direction (x - T.base)
  have hxpos : 0 < ‖x_perp‖ := by
    dsimp only [x_perp]
    linarith
  have hxcoords' :
      inner ℝ x_perp e1 ≠ 0 ∨
        inner ℝ x_perp e2 ≠ 0 := by
    simpa [x_perp] using hxcoords
  let phiX :=
    angleOfCoords (inner ℝ x_perp e1) (inner ℝ x_perp e2)
  let c : ℝ := inner ℝ T.direction U.direction
  let pU : Point3 := U.direction - c • T.direction
  have hpUeq : pU = perpProj T.direction U.direction := by
    dsimp only [pU, perpProj, c]
    rw [real_inner_comm U.direction T.direction]
  have hdet :
      |det2 e1 e2 pU x_perp| ≤ 3 * δ * ‖pU‖ := by
    have h :=
      angular_det_bound hδ T U e1 e2 he1 he2
        hT1 hT2 h12 hinter x hxU
    simpa [hpUeq] using h
  let x1 : ℝ := inner ℝ pU e1
  let y1 : ℝ := inner ℝ pU e2
  have hx1 : x1 = inner ℝ U.direction e1 := by
    dsimp only [x1, pU]
    rw [inner_sub_left, inner_smul_left, hT1]
    ring
  have hy1 : y1 = inner ℝ U.direction e2 := by
    dsimp only [y1, pU]
    rw [inner_sub_left, inner_smul_left, hT2]
    ring
  let phiU :=
    angleOfCoords (inner ℝ U.direction e1)
      (inner ℝ U.direction e2)
  have hspecU :=
    angleOfCoords_spec
      (inner ℝ U.direction e1)
      (inner ℝ U.direction e2) hcoords
  have hpUpos : 0 < ‖pU‖ := by
    rw [hpUeq]
    exact hperpPos
  have hpT : inner ℝ pU T.direction = 0 := by
    dsimp only [pU]
    rw [inner_sub_left, inner_smul_left]
    have hcomm :
        inner ℝ U.direction T.direction = c :=
      (real_inner_comm U.direction T.direction).symm
    have hTT : inner ℝ T.direction T.direction = 1 := by
      rw [real_inner_self_eq_norm_sq, T.direction_unit]
      norm_num
    rw [hcomm, hTT]
    simp [starRingEnd]
  have hxy1 : x1 ^ 2 + y1 ^ 2 = ‖pU‖ ^ 2 := by
    have hnormA : ‖pU‖ ^ 2 = ‖A pU‖ ^ 2 := by
      rw [A.norm_map]
    have hsum :
        ‖A pU‖ ^ 2 =
          (A pU 0)^2 + (A pU 1)^2 + (A pU 2)^2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp [Fin.sum_univ_succ]
      ring
    rw [hnormA, hsum, hA0, hpT, hA1, hA2]
    simp [x1, y1]
  have hr1 : Real.sqrt (x1 ^ 2 + y1 ^ 2) = ‖pU‖ := by
    rw [hxy1, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (norm_nonneg pU)]
  have hx1polar : x1 = ‖pU‖ * Real.cos phiU := by
    have hcos := hspecU.2.2.1
    change Real.cos phiU =
      inner ℝ U.direction e1 /
        Real.sqrt
          (inner ℝ U.direction e1 ^ 2 +
            inner ℝ U.direction e2 ^ 2) at hcos
    rw [← hx1, ← hy1] at hcos
    rw [hr1] at hcos
    rw [hcos]
    field_simp [hpUpos.ne']
  have hy1polar : y1 = ‖pU‖ * Real.sin phiU := by
    have hsin := hspecU.2.2.2
    change Real.sin phiU =
      inner ℝ U.direction e2 /
        Real.sqrt
          (inner ℝ U.direction e1 ^ 2 +
            inner ℝ U.direction e2 ^ 2) at hsin
    rw [← hx1, ← hy1] at hsin
    rw [hr1] at hsin
    rw [hsin]
    field_simp [hpUpos.ne']
  let x2 : ℝ := inner ℝ x_perp e1
  let y2 : ℝ := inner ℝ x_perp e2
  have hxperpT : inner ℝ x_perp T.direction = 0 := by
    dsimp only [x_perp, perpProj]
    rw [inner_sub_left, inner_smul_left]
    have hTT : inner ℝ T.direction T.direction = 1 := by
      rw [real_inner_self_eq_norm_sq, T.direction_unit]
      norm_num
    rw [hTT]
    simp [starRingEnd]
  have hxy2 : x2 ^ 2 + y2 ^ 2 = ‖x_perp‖ ^ 2 := by
    have hnormA : ‖x_perp‖ ^ 2 = ‖A x_perp‖ ^ 2 := by
      rw [A.norm_map]
    have hsum :
        ‖A x_perp‖ ^ 2 =
          (A x_perp 0)^2 + (A x_perp 1)^2 +
            (A x_perp 2)^2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp [Fin.sum_univ_succ]
      ring
    rw [hnormA, hsum, hA0, hxperpT, hA1, hA2]
    simp [x2, y2]
  have hspecX :=
    angleOfCoords_spec (inner ℝ x_perp e1)
      (inner ℝ x_perp e2) hxcoords'
  have hr2 : Real.sqrt (x2 ^ 2 + y2 ^ 2) = ‖x_perp‖ := by
    rw [hxy2, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (norm_nonneg x_perp)]
  have hx2polar : x2 = ‖x_perp‖ * Real.cos phiX := by
    have hcos := hspecX.2.2.1
    change Real.cos phiX = x2 / Real.sqrt (x2^2 + y2^2) at hcos
    rw [hr2] at hcos
    rw [hcos]
    field_simp [hxpos.ne']
  have hy2polar : y2 = ‖x_perp‖ * Real.sin phiX := by
    have hsin := hspecX.2.2.2
    change Real.sin phiX = y2 / Real.sqrt (x2^2 + y2^2) at hsin
    rw [hr2] at hsin
    rw [hsin]
    field_simp [hxpos.ne']
  have hformula :
      det2 e1 e2 pU x_perp =
        ‖pU‖ * ‖x_perp‖ * Real.sin (phiX - phiU) := by
    simp only [det2]
    change x1 * y2 - y1 * x2 =
      ‖pU‖ * ‖x_perp‖ * Real.sin (phiX - phiU)
    rw [hx1polar, hy1polar, hx2polar, hy2polar,
      Real.sin_sub]
    ring
  rw [hformula] at hdet
  have habs :
      |‖pU‖ * ‖x_perp‖ * Real.sin (phiX - phiU)| =
        ‖pU‖ * ‖x_perp‖ *
          |Real.sin (phiX - phiU)| := by
    rw [abs_mul, abs_mul,
      abs_of_nonneg (norm_nonneg pU),
      abs_of_nonneg (norm_nonneg x_perp)]
  rw [habs] at hdet
  have hcancel :
      ‖x_perp‖ * |Real.sin (phiX - phiU)| ≤ 3 * δ := by
    nlinarith [hpUpos]
  have hmul :
      r * |Real.sin (phiX - phiU)| ≤
        ‖x_perp‖ * |Real.sin (phiX - phiU)| := by
    gcongr
  have hnum :
      r * |Real.sin (phiX - phiU)| ≤ 3 * δ :=
    hmul.trans hcancel
  calc
    |Real.sin (phiX - phiU)| =
        (r * |Real.sin (phiX - phiU)|) / r := by
          field_simp [hr.ne']
    _ ≤ (3 * δ) / r := by
      exact div_le_div_of_nonneg_right hnum hr.le

/--
Plane covering with multiplicity bound (property 4).
-/
lemma plane_covering_with_multiplicity
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {σ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (T : Kakeya.DeltaTube δ) (F_σ : Kakeya.TubeFamily δ)
    (hFσ_angle : ∀ U ∈ F_σ, σ ≤ angleBetween T U ∧ angleBetween T U ≤ 2 * σ)
    (hFσ_inter : ∀ U ∈ F_σ, (T.carrier ∩ U.carrier).Nonempty)
    (r : ℝ) (hr : 0 < r) :
    ∃ (K : ℕ) (bins : Fin K → Kakeya.TubeFamily δ),
      (∀ k, bins k ⊆ F_σ) ∧
      (∀ U ∈ F_σ, ∃ k, U ∈ bins k) ∧
      (∀ k, ∃ (n : Point3), ‖n‖ = 1 ∧ ∀ U ∈ bins k, |inner ℝ U.direction n| ≤ 2 * δ) ∧
      (∀ (x : Point3), ‖perpProj T.direction (x - T.base)‖ ≥ r →
        (Finset.filter (fun k : Fin K => ∃ U ∈ bins k, x ∈ U.carrier) Finset.univ).card ≤
          ENNReal.ofReal (100 * (σ / r + 1))) := by
  -- Build ONB via Householder reflection
  let e0_std : Point3 := EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
  let e1_std : Point3 := EuclideanSpace.single (1 : Fin 3) (1 : ℝ)
  let e2_std : Point3 := EuclideanSpace.single (2 : Fin 3) (1 : ℝ)
  let A : Point3 ≃ₗᵢ[ℝ] Point3 := Submodule.reflection (ℝ ∙ (T.direction - e0_std))ᗮ
  have hA : A T.direction = e0_std := Submodule.reflection_sub (by rw [T.direction_unit]; simp [e0_std])
  let e1 : Point3 := A.symm e1_std
  let e2 : Point3 := A.symm e2_std
  have hA_e1 : A e1 = e1_std := by simp [e1]
  have hA_e2 : A e2 = e2_std := by simp [e2]
  have he1 : ‖e1‖ = 1 := by
    have h : ‖e1‖ = ‖e1_std‖ := A.symm.norm_map e1_std
    rw [h] <;> simp [e1_std]
  have he2 : ‖e2‖ = 1 := by
    have h : ‖e2‖ = ‖e2_std‖ := A.symm.norm_map e2_std
    rw [h] <;> simp [e2_std]
  have hT1 : inner ℝ T.direction e1 = 0 := by
    have h : inner ℝ T.direction e1 = inner ℝ (A T.direction) (A e1) := (A.inner_map_map T.direction e1).symm
    rw [h, hA, hA_e1]
    have h_zero : inner ℝ e0_std e1_std = 0 := by
      have h2 : inner ℝ e0_std e1_std = (1 : ℝ) * e0_std 1 := EuclideanSpace.inner_single_right 1 (1 : ℝ) e0_std
      rw [h2]
      have h3 : e0_std 1 = 0 := by simp [e0_std, PiLp.single_apply] <;> decide
      rw [h3] <;> ring
    exact h_zero
  have hT2 : inner ℝ T.direction e2 = 0 := by
    have h : inner ℝ T.direction e2 = inner ℝ (A T.direction) (A e2) := (A.inner_map_map T.direction e2).symm
    rw [h, hA, hA_e2]
    have h_zero : inner ℝ e0_std e2_std = 0 := by
      have h2 : inner ℝ e0_std e2_std = (1 : ℝ) * e0_std 2 := EuclideanSpace.inner_single_right 2 (1 : ℝ) e0_std
      rw [h2]
      have h3 : e0_std 2 = 0 := by simp [e0_std, PiLp.single_apply] <;> decide
      rw [h3] <;> ring
    exact h_zero
  have h12 : inner ℝ e1 e2 = 0 := by
    have h : inner ℝ e1 e2 = inner ℝ (A e1) (A e2) := (A.inner_map_map e1 e2).symm
    rw [h, hA_e1, hA_e2]
    have h_zero : inner ℝ e1_std e2_std = 0 := by
      have h2 : inner ℝ e1_std e2_std = (1 : ℝ) * e1_std 2 := EuclideanSpace.inner_single_right 2 (1 : ℝ) e1_std
      rw [h2]
      have h3 : e1_std 2 = 0 := by simp [e1_std, PiLp.single_apply] <;> decide
      rw [h3] <;> ring
    exact h_zero
  have hA0 : ∀ z, (A z) 0 = inner ℝ z T.direction := by
    intro z
    have h : (A z) 0 = inner ℝ (A z) e0_std := by
      have h2 : inner ℝ (A z) e0_std = (1 : ℝ) * (A z) 0 := EuclideanSpace.inner_single_right 0 (1 : ℝ) (A z)
      rw [h2] <;> ring
    rw [h]
    have h3 : inner ℝ (A z) e0_std = inner ℝ z (A.symm e0_std) := by
      have h4 := A.inner_map_map z (A.symm e0_std)
      have h5 : A (A.symm e0_std) = e0_std := A.apply_symm_apply e0_std
      rw [h5] at h4; exact h4
    rw [h3]
    have h6 : A.symm e0_std = T.direction := by
      have h7 : A (A.symm e0_std) = A T.direction := by rw [A.apply_symm_apply, hA]
      exact A.injective h7
    rw [h6]
  have hA1 : ∀ z, (A z) 1 = inner ℝ z e1 := by
    intro z
    have h : (A z) 1 = inner ℝ (A z) e1_std := by
      have h2 : inner ℝ (A z) e1_std = (1 : ℝ) * (A z) 1 := EuclideanSpace.inner_single_right 1 (1 : ℝ) (A z)
      rw [h2] <;> ring
    rw [h]
    have h3 : inner ℝ (A z) e1_std = inner ℝ z (A.symm e1_std) := by
      have h4 := A.inner_map_map z (A.symm e1_std)
      have h5 : A (A.symm e1_std) = e1_std := A.apply_symm_apply e1_std
      rw [h5] at h4; exact h4
    rw [h3] <;> rfl
  have hA2 : ∀ z, (A z) 2 = inner ℝ z e2 := by
    intro z
    have h : (A z) 2 = inner ℝ (A z) e2_std := by
      have h2 : inner ℝ (A z) e2_std = (1 : ℝ) * (A z) 2 := EuclideanSpace.inner_single_right 2 (1 : ℝ) (A z)
      rw [h2] <;> ring
    rw [h]
    have h3 : inner ℝ (A z) e2_std = inner ℝ z (A.symm e2_std) := by
      have h4 := A.inner_map_map z (A.symm e2_std)
      have h5 : A (A.symm e2_std) = e2_std := A.apply_symm_apply e2_std
      rw [h5] at h4; exact h4
    rw [h3] <;> rfl
  let w : ℝ := δ / σ
  have hw_pos : 0 < w := by positivity
  let K : ℕ := Nat.ceil (2 * Real.pi / w)
  have hK_pos : 0 < K := by apply Nat.ceil_pos.mpr; positivity
  let angle_for (U : Kakeya.DeltaTube δ) := angleOfCoords (inner ℝ U.direction e1) (inner ℝ U.direction e2)
  let bins : Fin K → Kakeya.TubeFamily δ := fun k =>
    Finset.filter (fun U => (k : ℝ) * w ≤ angle_for U ∧ angle_for U < (k + 1 : ℝ) * w) F_σ

  have h_sub : ∀ k, bins k ⊆ F_σ := fun k => Finset.filter_subset _ _

  -- Helper: p_U = perpProj T.direction U.direction has positive norm when angle ∈ (0, π)
  have hpU_pos : ∀ U ∈ F_σ, 0 < ‖perpProj T.direction U.direction‖ := by
    intro U hU
    let c : ℝ := inner ℝ T.direction U.direction
    let p_U : Point3 := U.direction - c • T.direction
    have h_eq : p_U = perpProj T.direction U.direction := by
      dsimp only [p_U, perpProj, c]
      have h_comm : inner ℝ U.direction T.direction = inner ℝ T.direction U.direction :=
        (real_inner_comm U.direction T.direction).symm
      rw [h_comm]
    have hθ_pos : 0 < angleBetween T U := by
      have h : σ ≤ angleBetween T U := (hFσ_angle U hU).1
      linarith [hσ]
    have hθ_lt : angleBetween T U < Real.pi := by
      have h : angleBetween T U ≤ 2 * σ := (hFσ_angle U hU).2
      have h2 : (2 : ℝ) < Real.pi := by linarith [Real.pi_gt_three]
      linarith
    have h_bound1 : -1 ≤ c := by
      have h : |inner ℝ T.direction U.direction| ≤ ‖T.direction‖ * ‖U.direction‖ :=
        abs_real_inner_le_norm T.direction U.direction
      rw [T.direction_unit, U.direction_unit] at h
      have h' : |c| ≤ 1 := by simpa [c] using h
      exact (abs_le.mp h').1
    have h_bound2 : c ≤ 1 := by
      have h : |inner ℝ T.direction U.direction| ≤ ‖T.direction‖ * ‖U.direction‖ :=
        abs_real_inner_le_norm T.direction U.direction
      rw [T.direction_unit, U.direction_unit] at h
      have h' : |c| ≤ 1 := by simpa [c] using h
      exact (abs_le.mp h').2
    have hcosθ : Real.cos (angleBetween T U) = c := by
      have h_eq : angleBetween T U = Real.arccos c := by rfl
      rw [h_eq]
      exact Real.cos_arccos h_bound1 h_bound2
    have hpU_norm2 : ‖p_U‖ ^ 2 = Real.sin (angleBetween T U) ^ 2 := by
      have h_norm : ‖p_U‖ ^ 2 = ‖U.direction‖ ^ 2 - 2 * inner ℝ U.direction (c • T.direction) + ‖c • T.direction‖ ^ 2 :=
        norm_sub_sq_real U.direction (c • T.direction)
      have h_inner1 : inner ℝ U.direction (c • T.direction) = c^2 := by
        rw [inner_smul_right]
        have h_comm : inner ℝ U.direction T.direction = inner ℝ T.direction U.direction :=
          (real_inner_comm U.direction T.direction).symm
        rw [h_comm] <;> ring
      have h_norm2 : ‖c • T.direction‖ ^ 2 = c^2 := by
        simp [norm_smul, T.direction_unit] <;> ring
      have h_main : ‖p_U‖ ^ 2 = 1 - c^2 := by
        rw [h_norm, h_inner1, h_norm2, U.direction_unit] <;> ring
      have h_sin2 : 1 - c^2 = Real.sin (angleBetween T U) ^ 2 := by
        have h4 : Real.sin (angleBetween T U) ^ 2 + Real.cos (angleBetween T U) ^ 2 = 1 :=
          Real.sin_sq_add_cos_sq (angleBetween T U)
        rw [hcosθ] at h4 <;> linarith
      rw [h_main, h_sin2]
    have h_sin_pos : 0 < Real.sin (angleBetween T U) :=
      Real.sin_pos_of_pos_of_lt_pi hθ_pos hθ_lt
    have h_pos : 0 < ‖p_U‖ := by
      have h_pos2 : 0 < ‖p_U‖ ^ 2 := by
        rw [hpU_norm2]; exact sq_pos_of_pos h_sin_pos
      have h_ne : ‖p_U‖ ≠ 0 := sq_pos_iff.mp h_pos2
      have h_nonneg : 0 ≤ ‖p_U‖ := by positivity
      exact h_nonneg.lt_of_ne h_ne.symm
    rw [←h_eq]
    exact h_pos

  -- Coordinates of U.direction in (e1,e2) cannot both be zero
  have h_coords_nonzero : ∀ U ∈ F_σ, inner ℝ U.direction e1 ≠ 0 ∨ inner ℝ U.direction e2 ≠ 0 := by
    intro U hU
    by_contra h; push Not at h
    let c : ℝ := inner ℝ T.direction U.direction
    let p_U : Point3 := U.direction - c • T.direction
    have h_pe1 : inner ℝ p_U e1 = 0 := by
      dsimp only [p_U]
      rw [inner_sub_left, inner_smul_left, hT1, h.1] <;> ring
    have h_pe2 : inner ℝ p_U e2 = 0 := by
      dsimp only [p_U]
      rw [inner_sub_left, inner_smul_left, hT2, h.2] <;> ring
    have h_pT : inner ℝ p_U T.direction = 0 := by
      dsimp only [p_U]
      have h1 : inner ℝ (U.direction - c • T.direction) T.direction =
          inner ℝ U.direction T.direction - inner ℝ (c • T.direction) T.direction :=
        inner_sub_left U.direction (c • T.direction) T.direction
      rw [h1]
      have h2 : inner ℝ (c • T.direction) T.direction = c * inner ℝ T.direction T.direction := by
        exact inner_smul_left T.direction T.direction (r := c)
      rw [h2]
      have h_comm : inner ℝ U.direction T.direction = c := by
        exact (real_inner_comm U.direction T.direction).symm
      rw [h_comm]
      have hTt : inner ℝ T.direction T.direction = 1 := by
        have h : inner ℝ T.direction T.direction = ‖T.direction‖ ^ 2 := by
          rw [real_inner_self_eq_norm_sq]
        rw [h, T.direction_unit] <;> norm_num
      rw [hTt] <;> ring
    have h_ApU0 : (A p_U) 0 = 0 := by rw [hA0, h_pT]
    have h_ApU1 : (A p_U) 1 = 0 := by rw [hA1, h_pe1]
    have h_ApU2 : (A p_U) 2 = 0 := by rw [hA2, h_pe2]
    have h_ApU_eq_zero : A p_U = 0 := by
      ext i
      fin_cases i <;> tauto
    have h_pU_eq_zero : p_U = 0 := by
      have h : A p_U = A (0 : Point3) := by rw [h_ApU_eq_zero] <;> simp
      exact A.injective h
    have hpos := hpU_pos U hU
    have h_eq2 : p_U = perpProj T.direction U.direction := by
      dsimp only [p_U, perpProj, c]
      have h_comm : inner ℝ U.direction T.direction = inner ℝ T.direction U.direction :=
        (real_inner_comm U.direction T.direction).symm
      rw [h_comm]
    have hpos2 : 0 < ‖p_U‖ := h_eq2 ▸ hpos
    rw [h_pU_eq_zero] at hpos2
    simp at hpos2 <;> linarith

  have h_cover : ∀ U ∈ F_σ, ∃ (k : Fin K), U ∈ bins k := by
    intro U hU
    let φ := angle_for U
    have hspec := angleOfCoords_spec (inner ℝ U.direction e1) (inner ℝ U.direction e2) (h_coords_nonzero U hU)
    have hφ_nonneg : 0 ≤ φ := hspec.1
    have hφ_lt_2pi : φ < 2 * Real.pi := hspec.2.1
    let k : ℕ := Nat.floor (φ / w)
    have hk1 : (k : ℝ) ≤ φ / w := Nat.floor_le (by positivity)
    have hk2 : φ / w < (k : ℝ) + 1 := Nat.lt_floor_add_one (φ / w)
    have hk3 : (k : ℝ) * w ≤ φ := by
      calc
        (k : ℝ) * w ≤ (φ / w) * w := by gcongr
        _ = φ := by field_simp [hw_pos.ne'] <;> ring
    have hk4 : φ < ((k : ℝ) + 1) * w := by
      calc
        φ = (φ / w) * w := by field_simp [hw_pos.ne'] <;> ring
        _ < ((k : ℝ) + 1) * w := by gcongr
    have hkK : k < K := by
      have h : φ / w < (K : ℝ) := by
        calc
          φ / w < (2 * Real.pi) / w := by gcongr
          _ ≤ (K : ℝ) := Nat.le_ceil _
      have h6 : (k : ℝ) < (K : ℝ) := by linarith [hk1]
      exact_mod_cast h6
    let k' : Fin K := ⟨k, hkK⟩
    refine' ⟨k', _⟩
    simp only [bins, Finset.mem_filter]; exact ⟨hU, hk3, hk4⟩

  have h_plane : ∀ k, ∃ (n : Point3), ‖n‖ = 1 ∧ ∀ U ∈ bins k, |inner ℝ U.direction n| ≤ 2 * δ := by
    intro k
    let α : ℝ := (k : ℝ) * w
    let n : Point3 := -Real.sin α • e1 + Real.cos α • e2
    let n_std : Point3 := -Real.sin α • e1_std + Real.cos α • e2_std
    have h_n_def : n = A.symm n_std := by
      simp [n, n_std, e1, e2] <;> abel
    have hn : ‖n‖ = 1 := by
      rw [h_n_def]
      have h : ‖A.symm n_std‖ = ‖n_std‖ := A.symm.norm_map n_std
      rw [h]
      have h2 : ‖n_std‖ ^ 2 = ∑ i : Fin 3, (n_std i)^2 := EuclideanSpace.real_norm_sq_eq n_std
      have h3 : n_std 0 = 0 := by simp [n_std, e1_std, e2_std, PiLp.single_apply]
      have h4 : n_std 1 = -Real.sin α := by simp [n_std, e1_std, e2_std, PiLp.single_apply]
      have h5 : n_std 2 = Real.cos α := by simp [n_std, e1_std, e2_std, PiLp.single_apply]
      have h6 : ‖n_std‖ ^ 2 = 1 := by
        have h_sum : ∑ i : Fin 3, (n_std i)^2 = (n_std 0)^2 + (n_std 1)^2 + (n_std 2)^2 := by
          simp [Fin.sum_univ_succ] <;> ring
        rw [h2, h_sum, h3, h4, h5]
        have h7 : (0 : ℝ)^2 + (-Real.sin α)^2 + (Real.cos α)^2 = 1 := by
          have h8 := Real.sin_sq_add_cos_sq α
          nlinarith
        exact h7
      have h9 : 0 ≤ ‖n_std‖ := by positivity
      nlinarith
    refine ⟨n, hn, ?_⟩
    intro U hU
    have hU_Fσ : U ∈ F_σ := h_sub k hU
    have h_angle_U : σ ≤ angleBetween T U ∧ angleBetween T U ≤ 2 * σ := hFσ_angle U hU_Fσ
    let θ : ℝ := angleBetween T U
    have hθ1 : σ ≤ θ := h_angle_U.1
    have hθ2 : θ ≤ 2 * σ := h_angle_U.2
    have hθ_pos : 0 < θ := by linarith [hσ]
    have hθ_lt_pi : θ < Real.pi := by
      have h : (2 : ℝ) < Real.pi := by linarith [Real.pi_gt_three]
      linarith
    let x : ℝ := inner ℝ U.direction e1
    let y : ℝ := inner ℝ U.direction e2
    let φ := angle_for U
    have hbin : (k : ℝ) * w ≤ φ ∧ φ < (k + 1 : ℝ) * w := by
      simp only [bins, Finset.mem_filter] at hU
      exact hU.2
    let Δφ : ℝ := φ - α
    have hΔφ_nonneg : 0 ≤ Δφ := by linarith
    have hΔφ_lt : Δφ < w := by linarith
    let c : ℝ := inner ℝ T.direction U.direction
    let p_U : Point3 := U.direction - c • T.direction
    have h_bound1 : -1 ≤ c := by
      have h : |inner ℝ T.direction U.direction| ≤ ‖T.direction‖ * ‖U.direction‖ :=
        abs_real_inner_le_norm T.direction U.direction
      rw [T.direction_unit, U.direction_unit] at h
      have h' : |c| ≤ 1 := by simpa [c] using h
      exact (abs_le.mp h').1
    have h_bound2 : c ≤ 1 := by
      have h : |inner ℝ T.direction U.direction| ≤ ‖T.direction‖ * ‖U.direction‖ :=
        abs_real_inner_le_norm T.direction U.direction
      rw [T.direction_unit, U.direction_unit] at h
      have h' : |c| ≤ 1 := by simpa [c] using h
      exact (abs_le.mp h').2
    have hcosθ : Real.cos θ = c := by
      have h_eq : θ = Real.arccos c := by rfl
      rw [h_eq]
      exact Real.cos_arccos h_bound1 h_bound2
    have hpU_norm2 : ‖p_U‖ ^ 2 = Real.sin θ ^ 2 := by
      have h_norm : ‖p_U‖ ^ 2 = ‖U.direction‖ ^ 2 - 2 * inner ℝ U.direction (c • T.direction) + ‖c • T.direction‖ ^ 2 :=
        norm_sub_sq_real U.direction (c • T.direction)
      have h_inner1 : inner ℝ U.direction (c • T.direction) = c^2 := by
        rw [inner_smul_right]
        have h_comm : inner ℝ U.direction T.direction = inner ℝ T.direction U.direction :=
          (real_inner_comm U.direction T.direction).symm
        rw [h_comm] <;> ring
      have h_norm2 : ‖c • T.direction‖ ^ 2 = c^2 := by
        simp [norm_smul, T.direction_unit] <;> ring
      have h_main : ‖p_U‖ ^ 2 = 1 - c^2 := by
        rw [h_norm, h_inner1, h_norm2, U.direction_unit] <;> ring
      have h_sin2 : 1 - c^2 = Real.sin θ ^ 2 := by
        have h4 : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
        have h5 : Real.cos θ = c := hcosθ
        rw [h5] at h4 <;> linarith
      rw [h_main, h_sin2]
    have hpU_pos' : 0 < ‖p_U‖ := by
      have h_sin_pos : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ_pos hθ_lt_pi
      have h_pos2 : 0 < ‖p_U‖ ^ 2 := by
        rw [hpU_norm2]; exact sq_pos_of_pos h_sin_pos
      have h_ne : ‖p_U‖ ≠ 0 := sq_pos_iff.mp h_pos2
      have h_nonneg : 0 ≤ ‖p_U‖ := by positivity
      exact h_nonneg.lt_of_ne h_ne.symm
    have hpU_norm : ‖p_U‖ = Real.sin θ := by
      have h1 : 0 ≤ ‖p_U‖ := by positivity
      have h2 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_mem_Icc ⟨by linarith, by linarith [Real.pi_pos]⟩
      exact (sq_eq_sq₀ h1 h2).mp hpU_norm2
    have hpU_le_2σ : ‖p_U‖ ≤ 2 * σ := by
      rw [hpU_norm]
      have h : Real.sin θ ≤ θ := Real.sin_le (by linarith)
      linarith
    have hx_eq : inner ℝ p_U e1 = x := by
      dsimp only [p_U]
      rw [inner_sub_left, inner_smul_left, hT1] <;> ring
    have hy_eq : inner ℝ p_U e2 = y := by
      dsimp only [p_U]
      rw [inner_sub_left, inner_smul_left, hT2] <;> ring
    have h_pT : inner ℝ p_U T.direction = 0 := by
      dsimp only [p_U]
      have h1 : inner ℝ (U.direction - c • T.direction) T.direction =
          inner ℝ U.direction T.direction - inner ℝ (c • T.direction) T.direction :=
        inner_sub_left U.direction (c • T.direction) T.direction
      rw [h1]
      have h2 : inner ℝ (c • T.direction) T.direction = c * inner ℝ T.direction T.direction := by
        exact inner_smul_left T.direction T.direction (r := c)
      rw [h2]
      have h_comm : inner ℝ U.direction T.direction = c := by
        exact (real_inner_comm U.direction T.direction).symm
      rw [h_comm]
      have hTt : inner ℝ T.direction T.direction = 1 := by
        have h : inner ℝ T.direction T.direction = ‖T.direction‖ ^ 2 := by
          rw [real_inner_self_eq_norm_sq]
        rw [h, T.direction_unit] <;> norm_num
      rw [hTt] <;> ring
    have hxy_sum : x ^ 2 + y ^ 2 = ‖p_U‖ ^ 2 := by
      have h_norm2 : ‖p_U‖ ^ 2 = ‖A p_U‖ ^ 2 := by exact A.norm_map p_U ▸ rfl
      have h_ApU0 : (A p_U) 0 = 0 := by rw [hA0, h_pT]
      have h_ApU1 : (A p_U) 1 = x := by rw [hA1, hx_eq]
      have h_ApU2 : (A p_U) 2 = y := by rw [hA2, hy_eq]
      have h_sum : ‖A p_U‖ ^ 2 = (A p_U 0)^2 + (A p_U 1)^2 + (A p_U 2)^2 := by
        have h : ‖A p_U‖ ^ 2 = ∑ i : Fin 3, ((A p_U) i)^2 := EuclideanSpace.real_norm_sq_eq (A p_U)
        rw [h]
        simp [Fin.sum_univ_succ] <;> ring
      rw [h_norm2, h_sum, h_ApU0, h_ApU1, h_ApU2] <;> ring
    have h_ne_zero : x ≠ 0 ∨ y ≠ 0 := h_coords_nonzero U hU_Fσ
    have hspec := angleOfCoords_spec x y h_ne_zero
    have hcos_φ : Real.cos φ = x / Real.sqrt (x^2 + y^2) := hspec.2.2.1
    have hsin_φ : Real.sin φ = y / Real.sqrt (x^2 + y^2) := hspec.2.2.2
    have h_r_eq : Real.sqrt (x^2 + y^2) = ‖p_U‖ := by
      have h : x^2 + y^2 = ‖p_U‖^2 := hxy_sum
      rw [h]
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
    have h_x_cos : x = ‖p_U‖ * Real.cos φ := by
      have h : ‖p_U‖ * Real.cos φ = ‖p_U‖ * (x / Real.sqrt (x^2 + y^2)) := by rw [hcos_φ]
      rw [h, h_r_eq]
      field_simp [hpU_pos'.ne'] <;> ring
    have h_y_sin : y = ‖p_U‖ * Real.sin φ := by
      have h : ‖p_U‖ * Real.sin φ = ‖p_U‖ * (y / Real.sqrt (x^2 + y^2)) := by rw [hsin_φ]
      rw [h, h_r_eq]
      field_simp [hpU_pos'.ne'] <;> ring
    have h_inner_pU_n : inner ℝ p_U n = ‖p_U‖ * Real.sin Δφ := by
      have h1 : inner ℝ p_U n = -Real.sin α * inner ℝ p_U e1 + Real.cos α * inner ℝ p_U e2 := by
        have h_expand : n = -Real.sin α • e1 + Real.cos α • e2 := by rfl
        rw [h_expand]
        rw [inner_add_right, inner_smul_right, inner_smul_right] <;> ring
      rw [h1, hx_eq, hy_eq]
      rw [h_x_cos, h_y_sin]
      have h2 : -Real.sin α * (‖p_U‖ * Real.cos φ) + Real.cos α * (‖p_U‖ * Real.sin φ) =
          ‖p_U‖ * Real.sin (φ - α) := by
        rw [Real.sin_sub] <;> ring
      exact h2
    have h_n_perp_T : inner ℝ T.direction n = 0 := by
      have h_expand : n = -Real.sin α • e1 + Real.cos α • e2 := by rfl
      rw [h_expand]
      rw [inner_add_right, inner_smul_right, inner_smul_right, hT1, hT2] <;> ring
    have h_inner_Un : inner ℝ U.direction n = inner ℝ p_U n := by
      have h3 : U.direction = p_U + c • T.direction := by simp [p_U] <;> abel
      rw [h3]
      have h4 : inner ℝ (c • T.direction) n = 0 := by
        rw [inner_smul_left, h_n_perp_T] <;> ring
      rw [inner_add_left, h4] <;> ring
    rw [h_inner_Un, h_inner_pU_n]
    have h_abs : |‖p_U‖ * Real.sin Δφ| = ‖p_U‖ * |Real.sin Δφ| := by
      rw [abs_mul] <;> rw [abs_of_nonneg (by positivity)]
    rw [h_abs]
    have h_sin_abs : |Real.sin Δφ| ≤ Δφ := by
      have h : |Real.sin Δφ| ≤ |Δφ| := Real.abs_sin_le_abs
      have h2 : |Δφ| = Δφ := abs_of_nonneg hΔφ_nonneg
      rw [h2] at h; exact h
    have h_pos1 : 0 ≤ ‖p_U‖ := by positivity
    have h_dφ : Δφ ≤ w := le_of_lt hΔφ_lt
    have h_mul : ‖p_U‖ * Δφ ≤ (2 * σ) * w :=
      mul_le_mul hpU_le_2σ h_dφ (by linarith) (by linarith)
    have h_final : ‖p_U‖ * |Real.sin Δφ| ≤ 2 * δ := by
      have h1 : ‖p_U‖ * |Real.sin Δφ| ≤ ‖p_U‖ * Δφ := mul_le_mul_of_nonneg_left h_sin_abs h_pos1
      have h2 : ‖p_U‖ * Δφ ≤ (2 * σ) * w := h_mul
      have h3 : (2 * σ) * w = 2 * δ := by
        dsimp only [w]; field_simp [hσ.ne'] <;> ring
      rw [h3] at h2
      exact le_trans h1 h2
    exact h_final

  -- Property 4: Multiplicity bound
  have h_mult : ∀ (x : Point3), ‖perpProj T.direction (x - T.base)‖ ≥ r →
      (Finset.filter (fun k : Fin K => ∃ U ∈ bins k, x ∈ U.carrier) Finset.univ).card ≤
        ENNReal.ofReal (100 * (σ / r + 1)) := by
    intro x hx_perp
    set x_perp := perpProj T.direction (x - T.base) with hxperp_def
    have h_xpos : 0 < ‖x_perp‖ := by linarith [hr]
    let active : Finset (Fin K) := Finset.filter (fun k => ∃ U ∈ bins k, x ∈ U.carrier) Finset.univ

    by_cases h_small : r < 3 * δ
    · -- Trivial bound by K
      have h1 : (K : ℝ) ≤ 2 * Real.pi / w + 1 := by
        have h2 : (K : ℝ) < 2 * Real.pi / w + 1 := by
          have hK : K = Nat.ceil (2 * Real.pi / w) := by rfl
          rw [hK]
          set y := 2 * Real.pi / w with hy_def
          have hy_pos : 0 < y := by positivity
          set n := Nat.ceil y with hn_def
          have h_n_pos : 0 < n := Nat.ceil_pos.mpr hy_pos
          have h1 : ¬(y ≤ ↑(n - 1)) := by
            intro h
            have h2 : n ≤ n - 1 := Nat.ceil_le.mpr h
            omega
          have h3 : (↑(n - 1) : ℝ) < y := by linarith
          have h4 : (↑(n - 1) : ℝ) = (n : ℝ) - 1 := by
            simp [h_n_pos] <;> omega
          rw [h4] at h3
          linarith
        linarith
      have hpi : 2 * Real.pi ≤ 100 / 3 := by have h : Real.pi < 4 := Real.pi_lt_four; linarith
      have h5 : σ / r ≥ σ / (3 * δ) := by gcongr <;> linarith
      have h6 : 2 * Real.pi * σ / δ + 1 ≤ 100 * (σ / (3 * δ) + 1) := by
        have h9 : 2 * Real.pi * σ / δ ≤ (100 / 3 : ℝ) * σ / δ := by gcongr
        have h10 : (100 / 3 : ℝ) * σ / δ = 100 * (σ / (3 * δ)) := by ring
        rw [h10] at h9
        linarith
      have h7 : 2 * Real.pi / w + 1 = 2 * Real.pi * σ / δ + 1 := by dsimp only [w]; field_simp [hδ.ne'] <;> ring
      have h4 : (K : ℝ) ≤ 100 * (σ / r + 1) := by
        calc (K : ℝ)
          ≤ 2 * Real.pi / w + 1 := h1
        _ = 2 * Real.pi * σ / δ + 1 := h7
        _ ≤ 100 * (σ / (3 * δ) + 1) := h6
        _ ≤ 100 * (σ / r + 1) := by gcongr
      have hK : (K : ENNReal) ≤ ENNReal.ofReal (100 * (σ / r + 1)) := by
        have h_eq : (K : ENNReal) = ENNReal.ofReal (K : ℝ) := by simp
        rw [h_eq]
        have h_pos : 0 ≤ 100 * (σ / r + 1) := by positivity
        exact ENNReal.ofReal_le_ofReal h4
      have h_card : (active.card : ENNReal) ≤ (K : ENNReal) := by
        have h : active.card ≤ K := by
          have h' : active.card ≤ Fintype.card (Fin K) := Finset.card_le_univ _
          have h'' : Fintype.card (Fin K) = K := by simp
          rw [h''] at h'
          exact h'
        exact_mod_cast h
      exact le_trans h_card hK

    · -- Main case: r ≥ 3δ
      have h_rge : r ≥ 3 * δ := by linarith
      let ε : ℝ := 3 * δ / r
      have hε0 : 0 ≤ ε := by positivity
      have hε1 : ε ≤ 1 := by
        dsimp only [ε]
        have h : 3 * δ ≤ r := by linarith
        exact (div_le_one hr).mpr h

      -- x_perp has nonzero coordinates in (e1,e2) plane
      have h_xnz : inner ℝ x_perp e1 ≠ 0 ∨ inner ℝ x_perp e2 ≠ 0 := by
        by_contra h
        have h' : inner ℝ x_perp e1 = 0 ∧ inner ℝ x_perp e2 = 0 := by simpa [not_or] using h
        rcases h' with ⟨h1, h2⟩
        have h_pT : inner ℝ x_perp T.direction = 0 := by
          have h_eq : x_perp = (x - T.base) - inner ℝ (x - T.base) T.direction • T.direction := by rfl
          rw [h_eq]
          have h3 : inner ℝ ((x - T.base) - inner ℝ (x - T.base) T.direction • T.direction) T.direction = 0 := by
            have h4 : inner ℝ ((x - T.base) - inner ℝ (x - T.base) T.direction • T.direction) T.direction =
                inner ℝ (x - T.base) T.direction - inner ℝ (inner ℝ (x - T.base) T.direction • T.direction) T.direction :=
              inner_sub_left (x - T.base) (inner ℝ (x - T.base) T.direction • T.direction) T.direction
            rw [h4]
            have h5 : inner ℝ (inner ℝ (x - T.base) T.direction • T.direction) T.direction =
                inner ℝ (x - T.base) T.direction * inner ℝ T.direction T.direction := inner_smul_left T.direction T.direction (r := inner ℝ (x - T.base) T.direction)
            rw [h5]
            have h6 : inner ℝ T.direction T.direction = 1 := by
              have h7 : inner ℝ T.direction T.direction = ‖T.direction‖ ^ 2 := by
                rw [real_inner_self_eq_norm_sq]
              rw [h7, T.direction_unit] <;> norm_num
            rw [h6] <;> ring
          exact h3
        have hAz : A x_perp = 0 := by
          have h0 : (A x_perp) 0 = 0 := by rw [hA0, h_pT]
          have h1' : (A x_perp) 1 = 0 := by rw [hA1, h1]
          have h2' : (A x_perp) 2 = 0 := by rw [hA2, h2]
          ext i; fin_cases i <;> tauto
        have hAz' : A x_perp = A (0 : Point3) := by rw [hAz] <;> simp
        have hz : x_perp = 0 := A.injective hAz'
        rw [hz] at h_xpos; simp at h_xpos <;> linarith
      let φ_x := angleOfCoords (inner ℝ x_perp e1) (inner ℝ x_perp e2)
      have hφx := angleOfCoords_spec (inner ℝ x_perp e1) (inner ℝ x_perp e2) h_xnz

      have h1 : ∀ k ∈ active, ∃ (U : Kakeya.DeltaTube δ), U ∈ bins k ∧ x ∈ U.carrier := by
        intro k hk; simp only [active, Finset.mem_filter] at hk; exact hk.2
      let U : Fin K → Kakeya.DeltaTube δ := fun k =>
        if hk : k ∈ active then Classical.choose (h1 k hk) else T
      have hU : ∀ k (hk : k ∈ active), (U k ∈ bins k ∧ x ∈ (U k).carrier) := by
        intro k hk
        have h_eq : U k = Classical.choose (h1 k hk) := by
          simp [U, hk]
        rw [h_eq]
        exact Classical.choose_spec (h1 k hk)
      have hU_in : ∀ k (hk : k ∈ active), U k ∈ bins k := fun k hk => (hU k hk).1
      have hU_x : ∀ k (hk : k ∈ active), x ∈ (U k).carrier := fun k hk => (hU k hk).2

      -- Key angular bound: |sin(φ_x - φ_U)| ≤ ε
      have h2 : ∀ k ∈ active, |Real.sin (φ_x - angle_for (U k))| ≤ ε := by
        intro k hk
        have h_inter : (T.carrier ∩ (U k).carrier).Nonempty := hFσ_inter (U k) ((h_sub k) (hU_in k hk))
        simpa [φ_x, angle_for, ε] using
          plane_covering_active_sine_bound
            hδ hr T (U k) e1 e2 he1 he2 hT1 hT2
            h12 A hA0 hA1 hA2
            (hpU_pos (U k) ((h_sub k) (hU_in k hk)))
            (h_coords_nonzero (U k)
              ((h_sub k) (hU_in k hk)))
            h_inter x (hU_x k hk) h_xnz hx_perp

      have h3 : ∀ k ∈ active, ∃ (n : ℤ), |φ_x - angle_for (U k) - (n : ℝ) * Real.pi| ≤ Real.arcsin ε := by
        intro k hk; exact sin_close_to_int_mul_pi hε0 hε1 (h2 k hk)
      let n : Fin K → ℤ := fun k =>
        if hk : k ∈ active then Classical.choose (h3 k hk) else 0
      have hn : ∀ k (hk : k ∈ active), |φ_x - angle_for (U k) - (n k : ℝ) * Real.pi| ≤ Real.arcsin ε := by
        intro k hk
        have h_eq : n k = Classical.choose (h3 k hk) := by simp [n, hk]
        rw [h_eq]
        exact Classical.choose_spec (h3 k hk)

      -- Bound n ∈ {-2,-1,0,1,2}
      have h4 : ∀ k ∈ active, n k ∈ ({-2, -1, 0, 1, 2} : Finset ℤ) := by
        intro k hk
        have hφU_nonneg : 0 ≤ angle_for (U k) := (angleOfCoords_spec (inner ℝ (U k).direction e1) (inner ℝ (U k).direction e2) (h_coords_nonzero (U k) ((h_sub k) (hU_in k hk)))).1
        have hφU_lt : angle_for (U k) < 2 * Real.pi := (angleOfCoords_spec (inner ℝ (U k).direction e1) (inner ℝ (U k).direction e2) (h_coords_nonzero (U k) ((h_sub k) (hU_in k hk)))).2.1
        have h_abs : |φ_x - angle_for (U k) - (n k : ℝ) * Real.pi| ≤ Real.arcsin ε := hn k hk
        have h_abs_up : φ_x - angle_for (U k) - (n k : ℝ) * Real.pi ≤ Real.arcsin ε := (abs_le.mp h_abs).2
        have h_abs_lo : -Real.arcsin ε ≤ φ_x - angle_for (U k) - (n k : ℝ) * Real.pi := (abs_le.mp h_abs).1
        have h_arcsin : Real.arcsin ε ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two ε
        have hpi_pos : 0 < Real.pi := Real.pi_pos
        have h5 : -5 / 2 < (n k : ℝ) := by
          have h7 : φ_x - angle_for (U k) > -2 * Real.pi := by linarith [hφx.1, hφU_lt]
          have h8 : (n k : ℝ) * Real.pi ≥ φ_x - angle_for (U k) - Real.arcsin ε := by linarith
          by_contra h9
          have h10 : (n k : ℝ) ≤ -5 / 2 := by linarith
          have h11 : (n k : ℝ) * Real.pi ≤ (-5 / 2 : ℝ) * Real.pi := by
            gcongr <;> linarith [hpi_pos]
          linarith
        have h6 : (n k : ℝ) < 5 / 2 := by
          have h7 : φ_x - angle_for (U k) < 2 * Real.pi := by linarith [hφx.2.1, hφU_nonneg]
          have h8 : (n k : ℝ) * Real.pi ≤ φ_x - angle_for (U k) + Real.arcsin ε := by linarith
          by_contra h9
          have h10 : (n k : ℝ) ≥ 5 / 2 := by linarith
          have h11 : (n k : ℝ) * Real.pi ≥ (5 / 2 : ℝ) * Real.pi := by
            gcongr <;> linarith [hpi_pos]
          linarith
        have h7 : n k ∈ ({-2, -1, 0, 1, 2} : Finset ℤ) := by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          have h5' : -3 < n k := by
            have h : (-3 : ℝ) < (n k : ℝ) := by linarith
            exact_mod_cast h
          have h6' : n k < 3 := by
            have h : (n k : ℝ) < (3 : ℝ) := by linarith
            exact_mod_cast h
          omega
        exact h7

      -- Count bins per n value
      have h_count : ∀ (n_val : ℤ), n_val ∈ ({-2, -1, 0, 1, 2} : Finset ℤ) →
          (active.filter (fun k => n k = n_val)).card ≤ Nat.ceil (2 * Real.arcsin ε / w + 4) := by
        intro n_val _
        let a : ℝ :=
          (φ_x - (n_val : ℝ) * Real.pi - Real.arcsin ε) / w - 1
        let b : ℝ :=
          (φ_x - (n_val : ℝ) * Real.pi + Real.arcsin ε) / w
        have h_int :
            ∀ k ∈ active.filter (fun k => n k = n_val),
              a < (k : ℝ) ∧ (k : ℝ) ≤ b := by
          intro k hk
          have hk' : k ∈ active := (Finset.mem_filter.mp hk).1
          have h_nk : n k = n_val := (Finset.mem_filter.mp hk).2
          have h_bin :=
            (Finset.mem_filter.mp (hU_in k hk')).2
          have h_near :
              |φ_x - angle_for (U k) -
                  (n_val : ℝ) * Real.pi| ≤
                Real.arcsin ε := by
            simpa [h_nk] using hn k hk'
          exact plane_covering_index_interval hw_pos
            h_bin.1 h_bin.2 h_near
        have hcard :=
          card_fin_interval_le_ceil_add_three
            (active.filter (fun k => n k = n_val)) a b h_int
        have hab :
            b - a + 3 = 2 * Real.arcsin ε / w + 4 := by
          dsimp only [a, b]
          ring
        rwa [hab] at hcard
        /-
        intro n_val _
        let a : ℝ := (φ_x - (n_val : ℝ) * Real.pi - Real.arcsin ε) / w - 1
        let b : ℝ := (φ_x - (n_val : ℝ) * Real.pi + Real.arcsin ε) / w
        have h_int : ∀ k ∈ active.filter (fun k => n k = n_val), a < (k : ℝ) ∧ (k : ℝ) ≤ b := by
          intro k hk
          have hk' : k ∈ active := (Finset.mem_filter.mp hk).1
          have h_nk : n k = n_val := (Finset.mem_filter.mp hk).2
          have hU_mem : U k ∈ bins k := hU_in k hk'
          have h_bin : (k : ℝ) * w ≤ angle_for (U k) ∧ angle_for (U k) < ((k : ℝ) + 1) * w :=
            (Finset.mem_filter.mp hU_mem).2
          have h_bin1 : (k : ℝ) * w ≤ angle_for (U k) := h_bin.1
          have h_bin2 : angle_for (U k) < ((k : ℝ) + 1) * w := h_bin.2
          have h_near : |φ_x - angle_for (U k) - (n_val : ℝ) * Real.pi| ≤ Real.arcsin ε := by
            have h_tmp := hn k hk'
            rw [h_nk] at h_tmp
            exact h_tmp
          have h_lo : angle_for (U k) ≥ φ_x - (n_val : ℝ) * Real.pi - Real.arcsin ε := by
            have h := abs_le.mp h_near
            linarith
          have h_hi : angle_for (U k) ≤ φ_x - (n_val : ℝ) * Real.pi + Real.arcsin ε := by
            have h := abs_le.mp h_near
            linarith
          constructor
          · have h : ((k : ℝ) + 1) * w > φ_x - (n_val : ℝ) * Real.pi - Real.arcsin ε := by linarith
            have h' : (k : ℝ) > (φ_x - (n_val : ℝ) * Real.pi - Real.arcsin ε) / w - 1 := by
              calc (k : ℝ) = ((k : ℝ) + 1) * w / w - 1 := by field_simp [hw_pos.ne'] <;> ring
                _ > _ := by gcongr
            exact h'
          · have h : (k : ℝ) * w ≤ φ_x - (n_val : ℝ) * Real.pi + Real.arcsin ε := by linarith
            have h' : (k : ℝ) ≤ (φ_x - (n_val : ℝ) * Real.pi + Real.arcsin ε) / w := by
              calc (k : ℝ) = ((k : ℝ) * w) / w := by field_simp [hw_pos.ne'] <;> ring
                _ ≤ _ := by gcongr
            exact h'
        let s_nat : Finset ℕ := (active.filter (fun k => n k = n_val)).image (fun k : Fin K => (k : ℕ))
        have h_card1 : (active.filter (fun k => n k = n_val)).card = s_nat.card := by
          rw [Finset.card_image_of_injOn]
          · intro x _ y _ h; exact Fin.ext h
        by_cases h_empty : s_nat = ∅
        · rw [h_card1, h_empty]; simp
        · have h_nonempty : s_nat.Nonempty := Finset.nonempty_iff_ne_empty.mpr h_empty
          rcases h_nonempty with ⟨m, hm⟩
          rcases Finset.mem_image.mp hm with ⟨k0, hk0, rfl⟩
          have h_ab : a < b := by
            have h1 : a < (k0 : ℝ) := (h_int k0 hk0).1
            have h2 : (k0 : ℝ) ≤ b := (h_int k0 hk0).2
            linarith
          have h_b_nonneg : 0 ≤ b := by
            have h2 : (k0 : ℝ) ≤ b := (h_int k0 hk0).2
            have h_k_nonneg : 0 ≤ (k0 : ℝ) := by positivity
            linarith
          by_cases ha : 0 ≤ a
          · -- Case a ≥ 0: use Ico with floor(a) as lower bound
            have h_floor_le : (Nat.floor a : ℝ) ≤ a := Nat.floor_le ha
            have h_sub_nat : s_nat ⊆ Finset.Ico (Nat.floor a + 1) (Nat.ceil b + 1) := by
              intro m hm
              rcases Finset.mem_image.mp hm with ⟨k, hk, rfl⟩
              have h1 : a < (k : ℝ) := (h_int k hk).1
              have h2 : (k : ℝ) ≤ b := (h_int k hk).2
              have h_lo : Nat.floor a + 1 ≤ (k : ℕ) := by
                have h4 : (Nat.floor a : ℝ) < (k : ℝ) := by linarith
                have h5 : Nat.floor a < (k : ℕ) := by exact_mod_cast h4
                omega
              have h_hi : (k : ℕ) < Nat.ceil b + 1 := by
                have h4 : (k : ℝ) ≤ (Nat.ceil b : ℝ) := by
                  have h5 : b ≤ (Nat.ceil b : ℝ) := Nat.le_ceil b
                  linarith
                have h4' : (k : ℕ) ≤ Nat.ceil b := Nat.cast_le.mp h4
                omega
              exact Finset.mem_Ico.mpr ⟨h_lo, h_hi⟩
            have h_card2 : s_nat.card ≤ (Finset.Ico (Nat.floor a + 1) (Nat.ceil b + 1)).card := Finset.card_le_card h_sub_nat
            have h_card_Ico : (Finset.Ico (Nat.floor a + 1) (Nat.ceil b + 1)).card = (Nat.ceil b + 1) - (Nat.floor a + 1) := by
              rw [Nat.card_Ico]
            rw [h_card_Ico] at h_card2
            have h3 : (Nat.ceil b + 1) - (Nat.floor a + 1) = Nat.ceil b - Nat.floor a := by omega
            rw [h3] at h_card2
            have h4 : Nat.ceil b - Nat.floor a ≤ Nat.ceil (b - a) + 2 := by
              have h5 : (Nat.ceil b : ℝ) < b + 1 := Nat.ceil_lt_add_one h_b_nonneg
              have h6 : a - 1 < (Nat.floor a : ℝ) := by
                have h7 : a < (Nat.floor a : ℝ) + 1 := Nat.lt_floor_add_one a
                linarith
              have h9 : Nat.floor a ≤ Nat.ceil b := by
                have h10 : (Nat.floor a : ℝ) ≤ a := Nat.floor_le ha
                have h11 : b ≤ (Nat.ceil b : ℝ) := Nat.le_ceil b
                have h12 : (Nat.floor a : ℝ) < (Nat.ceil b : ℝ) := by linarith [h_ab, h10, h11]
                have h13 : (Nat.floor a : ℝ) ≤ (Nat.ceil b : ℝ) := le_of_lt h12
                exact Nat.cast_le.mp h13
              have h10 : ((Nat.ceil b - Nat.floor a : ℕ) : ℝ) = (Nat.ceil b : ℝ) - (Nat.floor a : ℝ) := by
                rw [Nat.cast_sub h9] <;> rfl
              have h11 : ((Nat.ceil b - Nat.floor a : ℕ) : ℝ) < b - a + 2 := by
                rw [h10]; linarith
              have h12 : b - a + 2 ≤ (Nat.ceil (b - a) + 2 : ℝ) := by
                have h13 : b - a ≤ (Nat.ceil (b - a) : ℝ) := Nat.le_ceil (b - a)
                exact add_le_add h13 (by norm_num)
              have h14 : ((Nat.ceil b - Nat.floor a : ℕ) : ℝ) < (Nat.ceil (b - a) : ℝ) + 2 := by linarith
              have h15 : ((Nat.ceil b - Nat.floor a : ℕ) : ℝ) ≤ ↑(Nat.ceil (b - a) + 2) := by
                have h16 : (Nat.ceil (b - a) : ℝ) + 2 = ↑(Nat.ceil (b - a) + 2) := by
                  rw [Nat.cast_add] <;> norm_num
                rw [h16] at h14
                exact le_of_lt h14
              exact Nat.cast_le.mp h15
            have h9 : b - a = 2 * Real.arcsin ε / w + 1 := by dsimp only [a, b]; ring
            have h10 : Nat.ceil (b - a) + 2 ≤ Nat.ceil (2 * Real.arcsin ε / w + 4) := by
              have h_nonneg : 0 ≤ b - a := sub_nonneg.mpr (le_of_lt h_ab)
              have h_eq1 : 2 * Real.arcsin ε / w + 4 = (b - a) + 3 := by
                rw [h9] <;> ring
              rw [h_eq1]
              have h_ceil_add : Nat.ceil ((b - a) + 3) = Nat.ceil (b - a) + 3 :=
                Nat.ceil_add_natCast h_nonneg 3
              rw [h_ceil_add]
              <;> omega
            rw [h_card1]
            exact le_trans (le_trans h_card2 h4) h10
          · -- Case a < 0: use range, b - a > b implies ceil(b-a) ≥ ceil(b)
            have h_a_neg : a < 0 := lt_of_not_ge ha
            have h_sub_nat : s_nat ⊆ Finset.range (Nat.ceil b + 1) := by
              intro m hm
              rcases Finset.mem_image.mp hm with ⟨k, hk, rfl⟩
              have h2 : (k : ℝ) ≤ b := (h_int k hk).2
              have h4 : (k : ℝ) ≤ (Nat.ceil b : ℝ) := by
                have h5 : b ≤ (Nat.ceil b : ℝ) := Nat.le_ceil b
                linarith
              have h4' : (k : ℕ) ≤ Nat.ceil b := Nat.cast_le.mp h4
              have h5' : (k : ℕ) < Nat.ceil b + 1 := by omega
              exact Finset.mem_range.mpr h5'
            have h_card2 : s_nat.card ≤ (Finset.range (Nat.ceil b + 1)).card := Finset.card_le_card h_sub_nat
            have h_card_range : (Finset.range (Nat.ceil b + 1)).card = Nat.ceil b + 1 := by
              rw [Finset.card_range]
            rw [h_card_range] at h_card2
            have h2 : a ≤ 0 := le_of_lt h_a_neg
            have h3 : 0 ≤ -a := neg_nonneg.mpr h2
            have h1 : b ≤ b + (-a) := le_add_of_nonneg_right h3
            have h4 : b + (-a) = b - a := by ring
            have h5 : b ≤ b - a := by rw [h4] at h1; exact h1
            have h_ceil : Nat.ceil b ≤ Nat.ceil (b - a) := Nat.ceil_mono h5
            have h6 : Nat.ceil b + 1 ≤ Nat.ceil (b - a) + 2 := by omega
            have h9 : b - a = 2 * Real.arcsin ε / w + 1 := by
              simp only [a, b] <;> ring
            have h10 : Nat.ceil (b - a) + 2 ≤ Nat.ceil (2 * Real.arcsin ε / w + 4) := by
              have h_nonneg : 0 ≤ b - a := sub_nonneg.mpr (le_of_lt h_ab)
              have h_eq1 : 2 * Real.arcsin ε / w + 4 = (b - a) + 3 := by
                rw [h9] <;> ring
              rw [h_eq1]
              have h_ceil_add : Nat.ceil ((b - a) + 3) = Nat.ceil (b - a) + 3 :=
                Nat.ceil_add_natCast h_nonneg 3
              rw [h_ceil_add]
              <;> omega
            rw [h_card1]
            exact le_trans (le_trans h_card2 h6) h10
        -/

      have h_final : active.card ≤ 5 * Nat.ceil (2 * Real.arcsin ε / w + 4) :=
        multiplicity_final_bound (h4 := h4) (h_count := h_count)
      have h_main :
          (5 * Nat.ceil (2 * Real.arcsin ε / w + 4) : ℝ) ≤
            100 * (σ / r + 1) := by
        simpa [ε, w] using
          plane_covering_numeric_ceiling_bound hδ hσ hr h_rge
      have h_final' : (active.card : ℝ) ≤ (5 * Nat.ceil (2 * Real.arcsin ε / w + 4) : ℝ) := by
        exact_mod_cast h_final
      have h_combined : (active.card : ℝ) ≤ 100 * (σ / r + 1) := le_trans h_final' h_main
      have h_pos : 0 ≤ 100 * (σ / r + 1) := by positivity
      have h_card_ofReal : (active.card : ENNReal) = ENNReal.ofReal (active.card : ℝ) := by
        simp
      rw [h_card_ofReal]
      exact ENNReal.ofReal_le_ofReal h_combined

  exact ⟨K, bins, h_sub, h_cover, h_plane, h_mult⟩

end Kakeya.Assouad
