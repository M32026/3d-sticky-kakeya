module

/-
# Spherical Integral Bound for Arbitrary-Dimensional Marstrand

For d ≥ 2, ε, r > 0, and any unit vector v ∈ ℝ^d:
`∫_{S^{d-1}} max(0, 2ε - r|θ·v|) dσ ≤ C_d · ε² / max(r, ε)`
where `C_d = 4dπ`.

Proof: volume ratio V_{d-1} ≤ (d/π)V_d, belt bound, integral case split.
-/

public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.BeltMeasure
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open MeasureTheory ENNReal Set Classical

namespace WeakTwoEndsSumProduct

/-- The unit sphere in `EuclideanSpace ℝ (Fin d)`, as a subtype. -/
abbrev UnitSphere (d : ℕ) : Type _ :=
  {x : EuclideanSpace ℝ (Fin d) // x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1}

/-- Volume of the d-dimensional unit ball (as ENNReal). -/
noncomputable def unitBallVolume (d : ℕ) : ENNReal :=
  volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)

/-- Construct a Nontrivial instance for EuclideanSpace when d > 0. -/
lemma euclideanSpace_nontrivial {d : ℕ} (hd : 0 < d) :
    Nontrivial (EuclideanSpace ℝ (Fin d)) := by
  let z : Fin d := ⟨0, by omega⟩
  let f1 : EuclideanSpace ℝ (Fin d) := EuclideanSpace.single z (1 : ℝ)
  have h_ne : (0 : EuclideanSpace ℝ (Fin d)) ≠ f1 := by
    intro h
    have h9 : (0 : EuclideanSpace ℝ (Fin d)) z = f1 z := by rw [h]
    simp [f1] at h9
  exact ⟨0, f1, h_ne⟩

/-- Recurrence: `V_d = (2π/d) · V_{d-2}` for `d > 2`. -/
lemma unitBallVolume_recurrence {d : ℕ} (hd : 2 < d) :
    unitBallVolume d = ENNReal.ofReal (2 * Real.pi / (d : ℝ)) * unitBallVolume (d - 2) := by
  have h_d_pos : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (by linarith)
  letI nontriv_d : Nontrivial (EuclideanSpace ℝ (Fin d)) := euclideanSpace_nontrivial (by omega)
  have h_d2_pos : 0 < d - 2 := by omega
  letI nontriv_d2 : Nontrivial (EuclideanSpace ℝ (Fin (d - 2))) :=
    euclideanSpace_nontrivial h_d2_pos
  have h1 : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := by simp
  have h2 : Module.finrank ℝ (EuclideanSpace ℝ (Fin (d - 2))) = d - 2 := by simp
  have h_gamma : Real.Gamma ((d : ℝ) / 2 + 1) = ((d : ℝ) / 2) * Real.Gamma ((d : ℝ) / 2) := by
    rw [Real.Gamma_add_one] <;> linarith
  have h3 : (d : ℝ) / 2 = (((d - 2 : ℕ) : ℝ) / 2 + 1) := by
    have h31 : ((d - 2 : ℕ) : ℝ) = (d : ℝ) - 2 := by
      have h : 2 ≤ d := by omega
      rw [Nat.cast_sub h] <;> norm_num
    rw [h31] <;> ring
  have h4 : Real.Gamma ((d : ℝ) / 2) = Real.Gamma (((d - 2 : ℕ) : ℝ) / 2 + 1) := by
    rw [show (d : ℝ) / 2 = (((d - 2 : ℕ) : ℝ) / 2 + 1) from h3]
  have h5 : (Real.sqrt Real.pi) ^ d = Real.pi * (Real.sqrt Real.pi) ^ (d - 2) := by
    have h_pos : 0 < d - 2 := by omega
    have h_eq : (d - 2) + 2 = d := by omega
    have h : (Real.sqrt Real.pi) ^ d = (Real.sqrt Real.pi) ^ (d - 2) * (Real.sqrt Real.pi) ^ 2 := by
      rw [← pow_add, h_eq]
    rw [h]
    have h8 : (Real.sqrt Real.pi) ^ 2 = Real.pi := by
      rw [Real.sq_sqrt] <;> positivity
    rw [h8] <;> ring
  have h_main : (Real.sqrt Real.pi) ^ d / Real.Gamma ((d : ℝ) / 2 + 1) =
      (2 * Real.pi / (d : ℝ)) * ((Real.sqrt Real.pi) ^ (d - 2) /
        Real.Gamma (((d - 2 : ℕ) : ℝ) / 2 + 1)) := by
    rw [h_gamma, h4, h5]
    field_simp [h_d_pos.ne'] <;> ring
  have h_vol1 : unitBallVolume d =
      ENNReal.ofReal ((Real.sqrt Real.pi) ^ d / Real.Gamma ((d : ℝ) / 2 + 1)) := by
    have h_ball : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) =
        ENNReal.ofReal ((Real.sqrt Real.pi) ^ d / Real.Gamma ((d : ℝ) / 2 + 1)) := by
      rw [InnerProductSpace.volume_ball (0 : EuclideanSpace ℝ (Fin d)) 1, h1] <;> simp
    exact h_ball
  have h_vol2 : unitBallVolume (d - 2) =
      ENNReal.ofReal ((Real.sqrt Real.pi) ^ (d - 2) /
        Real.Gamma (((d - 2 : ℕ) : ℝ) / 2 + 1)) := by
    have h_ball : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (d - 2))) 1) =
        ENNReal.ofReal ((Real.sqrt Real.pi) ^ (d - 2) /
          Real.Gamma (((d - 2 : ℕ) : ℝ) / 2 + 1)) := by
      rw [InnerProductSpace.volume_ball (0 : EuclideanSpace ℝ (Fin (d - 2))) 1, h2] <;> simp
    exact h_ball
  rw [h_vol1, h_vol2, h_main]
  rw [ENNReal.ofReal_mul] <;> positivity

/-- `V_n ≤ 2 · V_{n-1}` for `n ≥ 2`, from the strip volume bound with `t=1`. -/
lemma unitBallVolume_strip_bound {n : ℕ} (hn : 2 ≤ n) :
    unitBallVolume n ≤ 2 * unitBallVolume (n - 1) := by
  let z : Fin n := ⟨0, by omega⟩
  let v : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single z (1 : ℝ)
  have hv : ‖v‖ = 1 := by
    rw [EuclideanSpace.norm_single z (1 : ℝ)] <;> norm_num
  let Kperp : Submodule ℝ (EuclideanSpace ℝ (Fin n)) := (Submodule.span ℝ {v})ᗮ
  have hv_ne_zero : v ≠ 0 := by
    intro h
    have h9 : (0 : EuclideanSpace ℝ (Fin n)) z = v z := by rw [h]
    simp [v] at h9
  have hK : Module.finrank ℝ (Submodule.span ℝ {v}) = 1 :=
    finrank_span_singleton hv_ne_zero
  have h_sum_raw := Submodule.finrank_add_finrank_orthogonal (Submodule.span ℝ {v})
  have h_d : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by simp
  have h_sum2 : (1 : ℕ) + Module.finrank ℝ Kperp = n := by
    simpa [hK, h_d] using h_sum_raw
  have hKperp_finrank : Module.finrank ℝ Kperp = n - 1 := by omega
  have h_pos : 0 < Module.finrank ℝ Kperp := by omega
  have h_rank_eq : Module.rank ℝ Kperp = ↑(Module.finrank ℝ Kperp) := by exact Eq.symm (Submodule.finrank_eq_rank ℝ (EuclideanSpace ℝ (Fin n)) Kperp)
  have h_rank_pos : 0 < Module.rank ℝ Kperp := by
    rw [h_rank_eq] <;> exact_mod_cast h_pos
  letI : Nontrivial Kperp := rank_pos_iff_nontrivial.mp h_rank_pos
  have hKperp_vol : volume (Metric.ball (0 : Kperp) 1) = unitBallVolume (n - 1) := by
    have h_ball : volume (Metric.ball (0 : Kperp) 1) =
        ENNReal.ofReal ((Real.sqrt Real.pi) ^ (Module.finrank ℝ Kperp) /
          Real.Gamma ((Module.finrank ℝ Kperp : ℝ) / 2 + 1)) := by
      rw [InnerProductSpace.volume_ball (0 : Kperp) 1] <;> simp
    have h_n1_pos : 0 < n - 1 := by omega
    letI nontriv_n1 : Nontrivial (EuclideanSpace ℝ (Fin (n - 1))) :=
      euclideanSpace_nontrivial h_n1_pos
    have h_ball2 : unitBallVolume (n - 1) =
        ENNReal.ofReal ((Real.sqrt Real.pi) ^ (n - 1) /
          Real.Gamma (((n - 1 : ℕ) : ℝ) / 2 + 1)) := by
      rw [unitBallVolume, InnerProductSpace.volume_ball (0 : EuclideanSpace ℝ (Fin (n - 1))) 1]
      <;> simp
    rw [h_ball, h_ball2, hKperp_finrank] <;> rfl
  have h_main := strip_volume_bound (show 1 ≤ n from by omega) (show (0 : ℝ) ≤ 1 by norm_num) v hv
  have h_eq : {x : EuclideanSpace ℝ (Fin n) | |inner ℝ x v| < (1 : ℝ) ∧ ‖x‖ < 1} =
      Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    ext x
    simp only [Set.mem_setOf_eq, Metric.mem_ball, dist_zero_right]
    constructor
    · rintro ⟨h1, h2⟩; exact h2
    · intro h
      have h1 : |inner ℝ x v| ≤ ‖x‖ * ‖v‖ := abs_real_inner_le_norm x v
      have h1' : |inner ℝ x v| ≤ ‖x‖ := by
        calc |inner ℝ x v| ≤ ‖x‖ * ‖v‖ := h1
          _ = ‖x‖ * 1 := by rw [hv]
          _ = ‖x‖ := by ring
      have h2 : |inner ℝ x v| < 1 := by linarith
      exact ⟨h2, h⟩
  rw [h_eq] at h_main
  rw [hKperp_vol] at h_main
  have h_main2 : unitBallVolume n ≤ (2 : ENNReal) * unitBallVolume (n - 1) := by
    simpa [unitBallVolume, mul_comm] using h_main
  exact h_main2

/-- Direct computation: `V_1 = 2`. -/
lemma unitBallVolume_one : unitBallVolume 1 = 2 := by
  letI nontriv : Nontrivial (EuclideanSpace ℝ (Fin 1)) :=
    euclideanSpace_nontrivial (by norm_num)
  have h_gamma32 : Real.Gamma (3 / 2) = Real.sqrt Real.pi / 2 := by
    have h1 : Real.Gamma (3 / 2) = (1 / 2 : ℝ) * Real.Gamma (1 / 2) := by
      have h_eq : (3 / 2 : ℝ) = (1 / 2 : ℝ) + 1 := by norm_num
      have h_pos : (1 / 2 : ℝ) ≠ 0 := by norm_num
      rw [h_eq, Real.Gamma_add_one h_pos] <;> ring
    rw [h1, Real.Gamma_one_half_eq] <;> ring
  have h_ball : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 1)) 1) =
      ENNReal.ofReal ((Real.sqrt Real.pi) ^ 1 / Real.Gamma ((1 : ℝ) / 2 + 1)) := by
    rw [InnerProductSpace.volume_ball (0 : EuclideanSpace ℝ (Fin 1)) 1] <;> simp
  have h6 : (1 : ℝ) / 2 + 1 = 3 / 2 := by norm_num
  have h_eq : (Real.sqrt Real.pi) ^ 1 / Real.Gamma ((1 : ℝ) / 2 + 1) = 2 := by
    rw [h6, h_gamma32]
    have h_pos : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
    field_simp [h_pos.ne'] <;> ring
  rw [unitBallVolume, h_ball, h_eq]
  <;> norm_cast

/-- Direct computation: `V_2 = π`. -/
lemma unitBallVolume_two : unitBallVolume 2 = ENNReal.ofReal Real.pi := by
  letI nontriv : Nontrivial (EuclideanSpace ℝ (Fin 2)) :=
    euclideanSpace_nontrivial (by norm_num)
  have h_gamma2 : Real.Gamma 2 = 1 := by
    have h : Real.Gamma 2 = (1 : ℝ) * Real.Gamma 1 := by
      have h_eq2 : (2 : ℝ) = (1 : ℝ) + 1 := by norm_num
      have h_pos : (1 : ℝ) ≠ 0 := by norm_num
      rw [h_eq2, Real.Gamma_add_one h_pos] <;> ring
    rw [h, Real.Gamma_one] <;> ring
  have h_ball : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1) =
      ENNReal.ofReal ((Real.sqrt Real.pi) ^ 2 / Real.Gamma ((2 : ℝ) / 2 + 1)) := by
    rw [InnerProductSpace.volume_ball (0 : EuclideanSpace ℝ (Fin 2)) 1] <;> simp
  have h6 : (2 : ℝ) / 2 + 1 = 2 := by norm_num
  have h_eq : (Real.sqrt Real.pi) ^ 2 / Real.Gamma ((2 : ℝ) / 2 + 1) = Real.pi := by
    rw [h6, h_gamma2]
    have h8 : (Real.sqrt Real.pi) ^ 2 = Real.pi := Real.sq_sqrt (by positivity)
    rw [h8] <;> ring
  rw [unitBallVolume, h_ball, h_eq] <;> rfl

/-- Ratio bound: `V_{d-1} ≤ (d/π) · V_d` for `d ≥ 2`. -/
lemma unitBallVolume_ratio {d : ℕ} (hd : 2 ≤ d) :
    unitBallVolume (d - 1) ≤ ENNReal.ofReal ((d : ℝ) / Real.pi) * unitBallVolume d := by
  by_cases h_d2 : d = 2
  · -- d = 2: direct computation
    subst h_d2
    have h_goal : unitBallVolume 1 ≤ ENNReal.ofReal ((2 : ℝ) / Real.pi) * unitBallVolume 2 := by
      rw [unitBallVolume_one, unitBallVolume_two]
      have h : ENNReal.ofReal ((2 : ℝ) / Real.pi) * ENNReal.ofReal Real.pi = (2 : ENNReal) := by
        have h9 : ENNReal.ofReal ((2 : ℝ) / Real.pi) * ENNReal.ofReal Real.pi =
            ENNReal.ofReal (((2 : ℝ) / Real.pi) * Real.pi) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
        rw [h9]
        have h10 : ((2 : ℝ) / Real.pi) * Real.pi = 2 := by
          field_simp [Real.pi_ne_zero] <;> ring
        rw [h10] <;> norm_cast
      rw [h] <;> simp
    exact h_goal
  · -- d > 2
    have h_d_gt_2 : 2 < d := by omega
    have h_rec : unitBallVolume d =
        ENNReal.ofReal (2 * Real.pi / (d : ℝ)) * unitBallVolume (d - 2) :=
      unitBallVolume_recurrence h_d_gt_2
    have h_strip : unitBallVolume (d - 1) ≤ 2 * unitBallVolume (d - 2) :=
      unitBallVolume_strip_bound (show 2 ≤ d - 1 by omega)
    have h_d_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (show 0 < d from by linarith)
    have h_mul : ENNReal.ofReal (2 * Real.pi / (d : ℝ)) *
        ENNReal.ofReal ((d : ℝ) / (2 * Real.pi)) = 1 := by
      have h_eq : (2 * Real.pi / (d : ℝ)) * ((d : ℝ) / (2 * Real.pi)) = 1 := by
        field_simp [h_d_pos.ne', Real.pi_ne_zero] <;> ring
      rw [← ENNReal.ofReal_mul (by positivity), h_eq] <;> simp
    have h_inv : unitBallVolume (d - 2) =
        ENNReal.ofReal ((d : ℝ) / (2 * Real.pi)) * unitBallVolume d := by
      calc
        unitBallVolume (d - 2)
          = 1 * unitBallVolume (d - 2) := by ring
        _ = (ENNReal.ofReal ((d : ℝ) / (2 * Real.pi)) *
              ENNReal.ofReal (2 * Real.pi / (d : ℝ))) * unitBallVolume (d - 2) := by
            have h_mul' : ENNReal.ofReal ((d : ℝ) / (2 * Real.pi)) *
                ENNReal.ofReal (2 * Real.pi / (d : ℝ)) = 1 := by
              rw [mul_comm, h_mul]
            rw [h_mul'] <;> ring
        _ = ENNReal.ofReal ((d : ℝ) / (2 * Real.pi)) *
              (ENNReal.ofReal (2 * Real.pi / (d : ℝ)) * unitBallVolume (d - 2)) := by ring
        _ = ENNReal.ofReal ((d : ℝ) / (2 * Real.pi)) * unitBallVolume d := by rw [← h_rec]
    calc
      unitBallVolume (d - 1)
        ≤ 2 * unitBallVolume (d - 2) := h_strip
      _ = ENNReal.ofReal (2 : ℝ) * unitBallVolume (d - 2) := by norm_cast
      _ = ENNReal.ofReal (2 : ℝ) *
            (ENNReal.ofReal ((d : ℝ) / (2 * Real.pi)) * unitBallVolume d) := by rw [h_inv]
      _ = (ENNReal.ofReal (2 : ℝ) * ENNReal.ofReal ((d : ℝ) / (2 * Real.pi))) * unitBallVolume d := by ring
      _ = ENNReal.ofReal ((d : ℝ) / Real.pi) * unitBallVolume d := by
        have h_eq : (2 : ℝ) * ((d : ℝ) / (2 * Real.pi)) = (d : ℝ) / Real.pi := by
          field_simp [Real.pi_ne_zero, h_d_pos.ne'] <;> ring
        have h : ENNReal.ofReal (2 : ℝ) * ENNReal.ofReal ((d : ℝ) / (2 * Real.pi)) =
            ENNReal.ofReal ((d : ℝ) / Real.pi) := by
          rw [← ENNReal.ofReal_mul (by positivity), h_eq]
        rw [h]

/-- Helper: volume of ball minus a null singleton equals volume of ball. -/
lemma ball_diff_null {d : ℕ} (hd : 0 < d) :
    volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1 \ {0}) = unitBallVolume d := by
  letI : Nontrivial (EuclideanSpace ℝ (Fin d)) := euclideanSpace_nontrivial hd
  have h_noatoms : NoAtoms (volume : Measure (EuclideanSpace ℝ (Fin d))) :=
    Measure.IsAddHaarMeasure.noAtoms volume
  have h_zero : volume ({0} : Set (EuclideanSpace ℝ (Fin d))) = 0 :=
    measure_singleton (0 : EuclideanSpace ℝ (Fin d))
  have h_inter : volume ((Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) ∩ ({0} : Set (EuclideanSpace ℝ (Fin d)))) = 0 := by
    have h_eq : (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) ∩ ({0} : Set (EuclideanSpace ℝ (Fin d))) = ({0} : Set (EuclideanSpace ℝ (Fin d))) := by
      ext x; simp [Metric.mem_ball] <;> tauto
    rw [h_eq, h_zero]
  have h_sub : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1 \ {0}) =
      volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) :=
    measure_sdiff_null' h_inter
  rw [h_sub] <;> rfl

/-- Helper: σ = d * V_d for the spherical surface measure. -/
lemma sigma_eq {d : ℕ} (hd : 2 ≤ d) :
    volume.toSphere (Set.univ : Set (UnitSphere d)) =
    (↑d : ENNReal) * unitBallVolume d := by
  letI nontriv_d : Nontrivial (EuclideanSpace ℝ (Fin d)) :=
    euclideanSpace_nontrivial (by omega)
  have h_finrank : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := by simp
  have h := MeasureTheory.Measure.toSphere_apply_univ (E := EuclideanSpace ℝ (Fin d)) (μ := volume)
  rw [h, h_finrank] <;> norm_cast

/-- Helper: σ is positive and finite. -/
lemma sigma_pos_and_lt_top {d : ℕ} (hd : 2 ≤ d)
    (hσ : volume.toSphere (Set.univ : Set (UnitSphere d)) = (↑d : ENNReal) * unitBallVolume d) :
    0 < volume.toSphere (Set.univ : Set (UnitSphere d)) ∧
    volume.toSphere (Set.univ : Set (UnitSphere d)) < ⊤ := by
  letI nontriv_d : Nontrivial (EuclideanSpace ℝ (Fin d)) :=
    euclideanSpace_nontrivial (by omega)
  have h1 : (0 : ENNReal) < (↑d : ENNReal) := by
    exact_mod_cast (show 0 < d from by linarith)
  have h2 : (0 : ENNReal) < unitBallVolume d := by
    have h_ball_pos : (0 : ENNReal) < volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) :=
      Metric.measure_ball_pos volume (0 : EuclideanSpace ℝ (Fin d)) (by norm_num)
    exact h_ball_pos
  have h3 : unitBallVolume d < ⊤ := by
    rw [unitBallVolume]
    exact measure_ball_lt_top
  constructor
  · rw [hσ]; exact ENNReal.mul_pos (ne_of_gt h1) (ne_of_gt h2)
  · rw [hσ]; exact ENNReal.mul_lt_top (by simp) h3

/-- Normalized belt measure bound:
`ν({θ ∈ S^{d-1} : |θ·v| < t}) ≤ 2td/π` for `d ≥ 2`, `t ≥ 0`. -/
lemma normalized_belt_bound {d : ℕ} (hd : 2 ≤ d) {t : ℝ} (ht : 0 ≤ t)
    (v : EuclideanSpace ℝ (Fin d)) (hv : ‖v‖ = 1) :
    let σ : ENNReal := volume.toSphere (Set.univ : Set (UnitSphere d))
    (σ⁻¹ • volume.toSphere) {θ : UnitSphere d | |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) v| < t} ≤
    ENNReal.ofReal (2 * t * (d : ℝ) / Real.pi) := by
  dsimp only
  let Sph := UnitSphere d
  let σ : ENNReal := volume.toSphere (Set.univ : Set Sph)
  let ν : Measure Sph := σ⁻¹ • volume.toSphere
  let A : Set Sph := {θ | |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) v| < t}
  let Kperp : Submodule ℝ (EuclideanSpace ℝ (Fin d)) := (Submodule.span ℝ {v})ᗮ

  have hσ : σ = (↑d : ENNReal) * unitBallVolume d := sigma_eq hd
  have hσ_both := sigma_pos_and_lt_top hd hσ
  have hσ_pos : 0 < σ := hσ_both.1
  have hσ_lt_top : σ < ⊤ := hσ_both.2

  have hv_ne_zero : v ≠ 0 := by
    intro h
    rw [h] at hv
    simp at hv <;> linarith
  have hK : Module.finrank ℝ (Submodule.span ℝ {v}) = 1 :=
    finrank_span_singleton hv_ne_zero
  have h_sum_raw := Submodule.finrank_add_finrank_orthogonal (Submodule.span ℝ {v})
  have h_d : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := by simp
  have h_sum2 : (1 : ℕ) + Module.finrank ℝ Kperp = d := by
    simpa [hK, h_d] using h_sum_raw
  have hKperp_finrank : Module.finrank ℝ Kperp = d - 1 := by omega
  have h_pos : 0 < Module.finrank ℝ Kperp := by omega
  have h_rank_eq : Module.rank ℝ Kperp = ↑(Module.finrank ℝ Kperp) := by exact Eq.symm (Submodule.finrank_eq_rank ℝ (EuclideanSpace ℝ (Fin d)) Kperp)
  have h_rank_pos : 0 < Module.rank ℝ Kperp := by
    rw [h_rank_eq] <;> exact_mod_cast h_pos
  letI : Nontrivial Kperp := rank_pos_iff_nontrivial.mp h_rank_pos

  have hKperp_vol : volume (Metric.ball (0 : Kperp) 1) = unitBallVolume (d - 1) := by
    have h_ball : volume (Metric.ball (0 : Kperp) 1) =
        ENNReal.ofReal ((Real.sqrt Real.pi) ^ (Module.finrank ℝ Kperp) /
          Real.Gamma ((Module.finrank ℝ Kperp : ℝ) / 2 + 1)) := by
      rw [InnerProductSpace.volume_ball (0 : Kperp) 1] <;> simp
    have h_d1_pos : 0 < d - 1 := by omega
    letI nontriv_d1 : Nontrivial (EuclideanSpace ℝ (Fin (d - 1))) :=
      euclideanSpace_nontrivial h_d1_pos
    have h_ball2 : unitBallVolume (d - 1) =
        ENNReal.ofReal ((Real.sqrt Real.pi) ^ (d - 1) /
          Real.Gamma (((d - 1 : ℕ) : ℝ) / 2 + 1)) := by
      rw [unitBallVolume, InnerProductSpace.volume_ball (0 : EuclideanSpace ℝ (Fin (d - 1))) 1]
      <;> simp
    rw [h_ball, h_ball2, hKperp_finrank] <;> rfl

  have h_belt_raw := belt_spherical_measure_bound (show 1 ≤ d from by omega) ht v hv
  have h_belt : volume.toSphere A ≤
      (↑d : ENNReal) * ENNReal.ofReal (2 * t) * unitBallVolume (d - 1) := by
    have h9 : volume.toSphere A ≤ (↑d : ENNReal) * ENNReal.ofReal (2 * t) * volume (Metric.ball (0 : Kperp) 1) := by
      exact_mod_cast h_belt_raw
    rw [hKperp_vol] at h9
    exact h9

  have h_ratio : unitBallVolume (d - 1) ≤
      ENNReal.ofReal ((d : ℝ) / Real.pi) * unitBallVolume d :=
    unitBallVolume_ratio hd

  have hν_A : ν A = σ⁻¹ * volume.toSphere A := by
    change (σ⁻¹ • volume.toSphere) A = σ⁻¹ * volume.toSphere A
    rw [Measure.coe_smul] <;> rfl

  rw [hν_A]

  have h9 : ENNReal.ofReal (2 * t) * ENNReal.ofReal ((d : ℝ) / Real.pi) =
      ENNReal.ofReal (2 * t * (d : ℝ) / Real.pi) := by
    rw [← ENNReal.ofReal_mul (by positivity)] <;> ring_nf

  have h_rearrange : (↑d : ENNReal) * ENNReal.ofReal (2 * t) *
        (ENNReal.ofReal ((d : ℝ) / Real.pi) * unitBallVolume d) =
      ENNReal.ofReal (2 * t * (d : ℝ) / Real.pi) * σ := by
    rw [hσ]
    have h10 : (↑d : ENNReal) * ENNReal.ofReal (2 * t) *
          (ENNReal.ofReal ((d : ℝ) / Real.pi) * unitBallVolume d) =
        (ENNReal.ofReal (2 * t) * ENNReal.ofReal ((d : ℝ) / Real.pi)) *
          ((↑d : ENNReal) * unitBallVolume d) := by
      simp [mul_assoc, mul_comm, mul_left_comm] <;> ring
    rw [h10, h9] <;> ring

  calc
    σ⁻¹ * volume.toSphere A
      ≤ σ⁻¹ * ((↑d : ENNReal) * ENNReal.ofReal (2 * t) * unitBallVolume (d - 1)) := by gcongr
    _ ≤ σ⁻¹ * ((↑d : ENNReal) * ENNReal.ofReal (2 * t) *
          (ENNReal.ofReal ((d : ℝ) / Real.pi) * unitBallVolume d)) := by gcongr
    _ = σ⁻¹ * (ENNReal.ofReal (2 * t * (d : ℝ) / Real.pi) * σ) := by rw [h_rearrange]
    _ = ENNReal.ofReal (2 * t * (d : ℝ) / Real.pi) * (σ⁻¹ * σ) := by ring
    _ = ENNReal.ofReal (2 * t * (d : ℝ) / Real.pi) := by
        rw [ENNReal.inv_mul_cancel hσ_pos.ne' hσ_lt_top.ne] <;> ring

/-- **Spherical dot-product integral bound** (arbitrary dimension, normalized). -/
lemma sphere_dot_integral_bound {d : ℕ} (hd : 2 ≤ d)
    {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r)
    (v : EuclideanSpace ℝ (Fin d)) (hv : ‖v‖ = 1) :
    let σ : ENNReal := volume.toSphere (Set.univ : Set (UnitSphere d))
    ∫⁻ (θ : UnitSphere d),
      ENNReal.ofReal (max 0 (2 * ε - r * |∑ i : Fin d, (θ : EuclideanSpace ℝ (Fin d)) i * v i|))
      ∂(σ⁻¹ • volume.toSphere)
    ≤ ENNReal.ofReal (4 * (d : ℝ) * Real.pi * ε^2 / max r ε) := by
  dsimp only
  let Sph := UnitSphere d
  let σ : ENNReal := volume.toSphere (Set.univ : Set Sph)
  let ν : Measure Sph := σ⁻¹ • volume.toSphere

  have h_inner_sum : ∀ (x y : EuclideanSpace ℝ (Fin d)),
      inner ℝ x y = ∑ i : Fin d, x i * y i := by
    intro x y
    have h1 : inner ℝ x y = ∑ i : Fin d, y i * x i := by
      rw [EuclideanSpace.inner_eq_star_dotProduct x y] <;> simp [dotProduct] <;> rfl
    rw [h1]
    apply Finset.sum_congr rfl
    intro i _; ring

  let f : Sph → ENNReal := fun θ =>
    ENNReal.ofReal (max 0 (2 * ε - r * |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) v|))

  have h_main_integrand : ∫⁻ (θ : Sph),
      ENNReal.ofReal (max 0 (2 * ε - r * |∑ i : Fin d, (θ : EuclideanSpace ℝ (Fin d)) i * v i|)) ∂ν =
      ∫⁻ (θ : Sph), f θ ∂ν := by
    congr with θ
    rw [← h_inner_sum (θ : EuclideanSpace ℝ (Fin d)) v]

  rw [h_main_integrand]

  have hσ : σ = (↑d : ENNReal) * unitBallVolume d := sigma_eq hd
  have hσ_both := sigma_pos_and_lt_top hd hσ
  have hσ_pos : 0 < σ := hσ_both.1
  have hσ_lt_top : σ < ⊤ := hσ_both.2

  have hν_univ : ν Set.univ = 1 := by
    simp [ν]
    <;> rw [ENNReal.inv_mul_cancel hσ_pos.ne' hσ_lt_top.ne] <;> ring

  by_cases h_case : r ≥ 2 * ε
  · -- Case 1: r ≥ 2ε
    set t : ℝ := 2 * ε / r with ht_def
    have ht_pos : 0 < t := by positivity
    have ht_le_one : t ≤ 1 := by
      rw [div_le_one hr] <;> linarith

    let A : Set Sph := {θ | |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) v| < t}

    have h_outside : ∀ θ ∉ A, f θ = 0 := by
      intro θ hθ
      have h1 : ¬|inner ℝ (θ : EuclideanSpace ℝ (Fin d)) v| < t := by simpa [A] using hθ
      have h3 : t ≤ |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) v| := by exact Std.not_lt.mp hθ
      have h_rt : r * t = 2 * ε := by
        rw [ht_def]
        field_simp [hr.ne'] <;> ring
      have h2 : r * |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) v| ≥ 2 * ε := by
        calc r * |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) v|
          ≥ r * t := by gcongr
        _ = 2 * ε := h_rt
      have h4 : 2 * ε - r * |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) v| ≤ 0 := by linarith
      have h5 : max 0 (2 * ε - r * |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) v|) = 0 := by
        rw [max_eq_left h4] <;> linarith
      have h6 : f θ = 0 := by
        simp only [f, h5]
        <;> simp
      exact h6

    have h_inside : ∀ θ ∈ A, f θ ≤ ENNReal.ofReal (2 * ε) := by
      intro θ _
      have h5 : max 0 (2 * ε - r * |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) v|) ≤ 2 * ε := by
        have h6 : 0 ≤ 2 * ε := by linarith
        have h7 : 2 * ε - r * |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) v| ≤ 2 * ε := by
          have h8 : 0 ≤ r * |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) v| := by
            exact mul_nonneg (by linarith) (abs_nonneg _)
          linarith
        exact max_le h6 h7
      exact ENNReal.ofReal_le_ofReal h5

    have h_pointwise : ∀ θ, f θ ≤
        Set.indicator A (fun _ => ENNReal.ofReal (2 * ε)) θ := by
      intro θ
      by_cases hθ : θ ∈ A
      · simpa [hθ, Set.indicator] using h_inside θ hθ
      · have h0 : f θ = 0 := h_outside θ hθ
        simpa [hθ, Set.indicator, h0] using by positivity

    have h_int : ∫⁻ θ, f θ ∂ν ≤ ENNReal.ofReal (2 * ε) * ν A := by
      calc
        ∫⁻ θ, f θ ∂ν
          ≤ ∫⁻ θ, Set.indicator A (fun _ => ENNReal.ofReal (2 * ε)) θ ∂ν :=
            lintegral_mono h_pointwise
        _ = ENNReal.ofReal (2 * ε) * ν A := by
          have h_cont : Continuous (fun (θ : Sph) => |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) v|) := by fun_prop
          have h_ind : MeasurableSet A :=
            isOpen_Iio.measurableSet.preimage h_cont.measurable
          rw [lintegral_indicator h_ind]
          <;> simp [lintegral_const] <;> ring

    have h_belt := normalized_belt_bound hd (by linarith) v hv
    have h1 : ν A ≤ ENNReal.ofReal (2 * t * (d : ℝ) / Real.pi) := h_belt

    have h2 : ENNReal.ofReal (2 * ε) * ν A ≤
        ENNReal.ofReal (2 * ε) * ENNReal.ofReal (2 * t * (d : ℝ) / Real.pi) := by gcongr

    have h3 : ENNReal.ofReal (2 * ε) * ENNReal.ofReal (2 * t * (d : ℝ) / Real.pi) =
        ENNReal.ofReal (2 * ε * (2 * t * (d : ℝ) / Real.pi)) := by
      rw [← ENNReal.ofReal_mul (by positivity)] <;> ring

    have h4 : max r ε = r := by
      rw [max_eq_left] <;> linarith

    have h5 : 2 * ε * (2 * t * (d : ℝ) / Real.pi) ≤
        4 * (d : ℝ) * Real.pi * ε^2 / r := by
      have hpi2 : (2 : ℝ) ≤ Real.pi ^ 2 := by
        have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
        nlinarith [Real.pi_pos]
      have h6 : (8 : ℝ) / Real.pi ≤ 4 * Real.pi := by
        have h : (8 : ℝ) ≤ 4 * Real.pi ^ 2 := by
          have hpi2 : (2 : ℝ) ≤ Real.pi ^ 2 := by
            have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
            nlinarith [Real.pi_pos]
          nlinarith [Real.pi_pos]
        have h' : (8 : ℝ) / Real.pi ≤ (4 * Real.pi ^ 2) / Real.pi := by gcongr
        have h'' : (4 * Real.pi ^ 2) / Real.pi = 4 * Real.pi := by
          field_simp [Real.pi_ne_zero] <;> ring
        rw [h''] at h'
        exact h'
      have h_pos2 : 0 < ε * ε * (d : ℝ) / r := by positivity
      calc
        2 * ε * (2 * t * (d : ℝ) / Real.pi)
          = 8 * ε^2 * (d : ℝ) / (r * Real.pi) := by
            simp only [ht_def]
            <;> field_simp [hr.ne', Real.pi_ne_zero] <;> ring
        _ = (8 / Real.pi) * (ε^2 * (d : ℝ) / r) := by ring
        _ ≤ (4 * Real.pi) * (ε^2 * (d : ℝ) / r) := by gcongr
        _ = 4 * (d : ℝ) * Real.pi * ε^2 / r := by ring

    have h_final : ENNReal.ofReal (2 * ε) * ν A ≤
        ENNReal.ofReal (4 * (d : ℝ) * Real.pi * ε^2 / r) := by
      calc
        ENNReal.ofReal (2 * ε) * ν A
          ≤ ENNReal.ofReal (2 * ε * (2 * t * (d : ℝ) / Real.pi)) := by
            rw [h3] at h2; exact h2
        _ ≤ ENNReal.ofReal (4 * (d : ℝ) * Real.pi * ε^2 / r) :=
            ENNReal.ofReal_le_ofReal h5

    rw [h4]
    exact le_trans h_int h_final

  · -- Case 2: r < 2ε
    have h_case' : r < 2 * ε := by linarith

    have h_all : ∀ θ, f θ ≤ ENNReal.ofReal (2 * ε) := by
      intro θ
      have h5 : max 0 (2 * ε - r * |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) v|) ≤ 2 * ε := by
        have h6 : 0 ≤ 2 * ε := by linarith
        have h7 : 2 * ε - r * |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) v| ≤ 2 * ε := by
          have h8 : 0 ≤ r * |inner ℝ (θ : EuclideanSpace ℝ (Fin d)) v| := by
            exact mul_nonneg (by linarith) (abs_nonneg _)
          linarith
        exact max_le h6 h7
      exact ENNReal.ofReal_le_ofReal h5

    have h_int : ∫⁻ θ, f θ ∂ν ≤ ENNReal.ofReal (2 * ε) := by
      calc
        ∫⁻ θ, f θ ∂ν ≤ ∫⁻ (_ : Sph), ENNReal.ofReal (2 * ε) ∂ν := lintegral_mono h_all
        _ = ENNReal.ofReal (2 * ε) * ν Set.univ := by
          rw [lintegral_const] <;> ring
        _ = ENNReal.ofReal (2 * ε) := by rw [hν_univ] <;> ring

    have h_max_lt : max r ε < 2 * ε := by
      have h1 : r < 2 * ε := h_case'
      have h2 : ε < 2 * ε := by linarith
      exact max_lt_iff.mpr ⟨h1, h2⟩

    have h12 : (d : ℝ) * Real.pi ≥ 2 := by
      have h121 : (d : ℝ) ≥ 2 := by exact_mod_cast hd
      have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
      have h122 : Real.pi ≥ 1 := by linarith
      nlinarith [Real.pi_pos]

    have h9 : ε^2 / max r ε > ε / 2 := by
      have h10 : max r ε < 2 * ε := h_max_lt
      calc
        ε^2 / max r ε > ε^2 / (2 * ε) := by gcongr
        _ = ε / 2 := by field_simp [hε.ne'] <;> ring

    have h_pos : 0 < 4 * (d : ℝ) * Real.pi := by positivity
    have h11 : 4 * (d : ℝ) * Real.pi * (ε^2 / max r ε) > 2 * ε := by
      have h : 4 * (d : ℝ) * Real.pi * (ε^2 / max r ε) >
          4 * (d : ℝ) * Real.pi * (ε / 2) := mul_lt_mul_of_pos_left h9 h_pos
      have h' : 4 * (d : ℝ) * Real.pi * (ε / 2) = 2 * (d : ℝ) * Real.pi * ε := by ring
      rw [h'] at h
      have h'' : 2 * (d : ℝ) * Real.pi * ε ≥ 2 * ε := by
        have h13 : (d : ℝ) * Real.pi ≥ 2 := h12
        have h14 : 2 * (d : ℝ) * Real.pi * ε ≥ 2 * (2 : ℝ) * ε := by
          have h15 : 0 ≤ ε := by linarith
          nlinarith [h12, Real.pi_pos]
        linarith
      linarith

    have h_eq : 4 * (d : ℝ) * Real.pi * ε^2 / max r ε =
        4 * (d : ℝ) * Real.pi * (ε^2 / max r ε) := by ring
    have h_ineq : 2 * ε ≤ 4 * (d : ℝ) * Real.pi * ε^2 / max r ε := by
      rw [h_eq]
      linarith

    exact le_trans h_int (ENNReal.ofReal_le_ofReal h_ineq)

/-- Explicit spherical constant used by the arbitrary-dimensional Marstrand theorem. -/
def marstrandSphereConstant (d : ℕ) : ℝ := 4 * (d : ℝ) * Real.pi

/-- **Spherical geometric bound** for the normalized uniform spherical measure. -/
lemma spherical_geometric_bound {d : ℕ} (hd : 2 ≤ d)
    {r ε : ℝ} (hr_pos : 0 < r) (hε_pos : 0 < ε)
    (v : EuclideanSpace ℝ (Fin d)) (hv : ‖v‖ = 1) :
    let σ : ENNReal := volume.toSphere (Set.univ : Set (UnitSphere d))
    ∫⁻ (θ : UnitSphere d),
      ENNReal.ofReal (max 0 (2 * ε - r * |∑ i : Fin d, (θ : EuclideanSpace ℝ (Fin d)) i * v i|))
      ∂(σ⁻¹ • volume.toSphere)
    ≤ ENNReal.ofReal (marstrandSphereConstant d * ε^2 / max r ε) := by
  dsimp only [marstrandSphereConstant]
  exact sphere_dot_integral_bound hd hε_pos hr_pos v hv

end WeakTwoEndsSumProduct
